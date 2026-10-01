-- Prove2me | solution 1 for syracuse_descends_range_2297435_2299435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:56.520989+00:00
-- url     : https://prove2.me/submissions/3201c332-8f8f-4bdf-85f4-9343a1cec479

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

theorem B6542309 : Blo 2297435 6542309 := bbase (se 4 (by rfl) ⟨613341, by rfl⟩ : syracuseStep 6542309 = 1226683) (by norm_num)
theorem B4361539 : Blo 2297435 4361539 := bstep (se 1 (by rfl) ⟨3271154, by rfl⟩ : syracuseStep 4361539 = 6542309) B6542309
theorem B5815385 : Blo 2297435 5815385 := bstep (se 2 (by rfl) ⟨2180769, by rfl⟩ : syracuseStep 5815385 = 4361539) B4361539
theorem B3876923 : Blo 2297435 3876923 := bstep (se 1 (by rfl) ⟨2907692, by rfl⟩ : syracuseStep 3876923 = 5815385) B5815385
theorem B2584615 : Blo 2297435 2584615 := bstep (se 1 (by rfl) ⟨1938461, by rfl⟩ : syracuseStep 2584615 = 3876923) B3876923
theorem B3446153 : Blo 2297435 3446153 := bstep (se 2 (by rfl) ⟨1292307, by rfl⟩ : syracuseStep 3446153 = 2584615) B2584615
theorem B2297435 : Blo 2297435 2297435 := bstep (se 1 (by rfl) ⟨1723076, by rfl⟩ : syracuseStep 2297435 = 3446153) B3446153
theorem B11630789 : Blo 2297435 11630789 := bbase (se 4 (by rfl) ⟨1090386, by rfl⟩ : syracuseStep 11630789 = 2180773) (by norm_num)
theorem B7753859 : Blo 2297435 7753859 := bstep (se 1 (by rfl) ⟨5815394, by rfl⟩ : syracuseStep 7753859 = 11630789) B11630789
theorem B5169239 : Blo 2297435 5169239 := bstep (se 1 (by rfl) ⟨3876929, by rfl⟩ : syracuseStep 5169239 = 7753859) B7753859
theorem B3446159 : Blo 2297435 3446159 := bstep (se 1 (by rfl) ⟨2584619, by rfl⟩ : syracuseStep 3446159 = 5169239) B5169239
theorem B2297439 : Blo 2297435 2297439 := bstep (se 1 (by rfl) ⟨1723079, by rfl⟩ : syracuseStep 2297439 = 3446159) B3446159
theorem B3446165 : Blo 2297435 3446165 := bbase (se 6 (by rfl) ⟨80769, by rfl⟩ : syracuseStep 3446165 = 161539) (by norm_num)
theorem B2297443 : Blo 2297435 2297443 := bstep (se 1 (by rfl) ⟨1723082, by rfl⟩ : syracuseStep 2297443 = 3446165) B3446165
theorem B4906757 : Blo 2297435 4906757 := bbase (se 4 (by rfl) ⟨460008, by rfl⟩ : syracuseStep 4906757 = 920017) (by norm_num)
theorem B13084685 : Blo 2297435 13084685 := bstep (se 3 (by rfl) ⟨2453378, by rfl⟩ : syracuseStep 13084685 = 4906757) B4906757
theorem B8723123 : Blo 2297435 8723123 := bstep (se 1 (by rfl) ⟨6542342, by rfl⟩ : syracuseStep 8723123 = 13084685) B13084685
theorem B5815415 : Blo 2297435 5815415 := bstep (se 1 (by rfl) ⟨4361561, by rfl⟩ : syracuseStep 5815415 = 8723123) B8723123
theorem B3876943 : Blo 2297435 3876943 := bstep (se 1 (by rfl) ⟨2907707, by rfl⟩ : syracuseStep 3876943 = 5815415) B5815415
theorem B5169257 : Blo 2297435 5169257 := bstep (se 2 (by rfl) ⟨1938471, by rfl⟩ : syracuseStep 5169257 = 3876943) B3876943
theorem B3446171 : Blo 2297435 3446171 := bstep (se 1 (by rfl) ⟨2584628, by rfl⟩ : syracuseStep 3446171 = 5169257) B5169257
theorem B2297447 : Blo 2297435 2297447 := bstep (se 1 (by rfl) ⟨1723085, by rfl⟩ : syracuseStep 2297447 = 3446171) B3446171
theorem B2584633 : Blo 2297435 2584633 := bbase (se 2 (by rfl) ⟨969237, by rfl⟩ : syracuseStep 2584633 = 1938475) (by norm_num)
theorem B3446177 : Blo 2297435 3446177 := bstep (se 2 (by rfl) ⟨1292316, by rfl⟩ : syracuseStep 3446177 = 2584633) B2584633
theorem B2297451 : Blo 2297435 2297451 := bstep (se 1 (by rfl) ⟨1723088, by rfl⟩ : syracuseStep 2297451 = 3446177) B3446177
theorem B2760061 : Blo 2297435 2760061 := bbase (se 3 (by rfl) ⟨517511, by rfl⟩ : syracuseStep 2760061 = 1035023) (by norm_num)
theorem B3680081 : Blo 2297435 3680081 := bstep (se 2 (by rfl) ⟨1380030, by rfl⟩ : syracuseStep 3680081 = 2760061) B2760061
theorem B2453387 : Blo 2297435 2453387 := bstep (se 1 (by rfl) ⟨1840040, by rfl⟩ : syracuseStep 2453387 = 3680081) B3680081
theorem B6542365 : Blo 2297435 6542365 := bstep (se 3 (by rfl) ⟨1226693, by rfl⟩ : syracuseStep 6542365 = 2453387) B2453387
theorem B8723153 : Blo 2297435 8723153 := bstep (se 2 (by rfl) ⟨3271182, by rfl⟩ : syracuseStep 8723153 = 6542365) B6542365
theorem B5815435 : Blo 2297435 5815435 := bstep (se 1 (by rfl) ⟨4361576, by rfl⟩ : syracuseStep 5815435 = 8723153) B8723153
theorem B7753913 : Blo 2297435 7753913 := bstep (se 2 (by rfl) ⟨2907717, by rfl⟩ : syracuseStep 7753913 = 5815435) B5815435
theorem B5169275 : Blo 2297435 5169275 := bstep (se 1 (by rfl) ⟨3876956, by rfl⟩ : syracuseStep 5169275 = 7753913) B7753913
theorem B3446183 : Blo 2297435 3446183 := bstep (se 1 (by rfl) ⟨2584637, by rfl⟩ : syracuseStep 3446183 = 5169275) B5169275
theorem B2297455 : Blo 2297435 2297455 := bstep (se 1 (by rfl) ⟨1723091, by rfl⟩ : syracuseStep 2297455 = 3446183) B3446183
theorem B3446189 : Blo 2297435 3446189 := bbase (se 3 (by rfl) ⟨646160, by rfl⟩ : syracuseStep 3446189 = 1292321) (by norm_num)
theorem B2297459 : Blo 2297435 2297459 := bstep (se 1 (by rfl) ⟨1723094, by rfl⟩ : syracuseStep 2297459 = 3446189) B3446189
theorem B5169293 : Blo 2297435 5169293 := bbase (se 3 (by rfl) ⟨969242, by rfl⟩ : syracuseStep 5169293 = 1938485) (by norm_num)
theorem B3446195 : Blo 2297435 3446195 := bstep (se 1 (by rfl) ⟨2584646, by rfl⟩ : syracuseStep 3446195 = 5169293) B5169293
theorem B2297463 : Blo 2297435 2297463 := bstep (se 1 (by rfl) ⟨1723097, by rfl⟩ : syracuseStep 2297463 = 3446195) B3446195
theorem B2907733 : Blo 2297435 2907733 := bbase (se 8 (by rfl) ⟨17037, by rfl⟩ : syracuseStep 2907733 = 34075) (by norm_num)
theorem B3876977 : Blo 2297435 3876977 := bstep (se 2 (by rfl) ⟨1453866, by rfl⟩ : syracuseStep 3876977 = 2907733) B2907733
theorem B2584651 : Blo 2297435 2584651 := bstep (se 1 (by rfl) ⟨1938488, by rfl⟩ : syracuseStep 2584651 = 3876977) B3876977
theorem B3446201 : Blo 2297435 3446201 := bstep (se 2 (by rfl) ⟨1292325, by rfl⟩ : syracuseStep 3446201 = 2584651) B2584651
theorem B2297467 : Blo 2297435 2297467 := bstep (se 1 (by rfl) ⟨1723100, by rfl⟩ : syracuseStep 2297467 = 3446201) B3446201
theorem B8842229 : Blo 2297435 8842229 := bbase (se 5 (by rfl) ⟨414479, by rfl⟩ : syracuseStep 8842229 = 828959) (by norm_num)
theorem B5894819 : Blo 2297435 5894819 := bstep (se 1 (by rfl) ⟨4421114, by rfl⟩ : syracuseStep 5894819 = 8842229) B8842229
theorem B3929879 : Blo 2297435 3929879 := bstep (se 1 (by rfl) ⟨2947409, by rfl⟩ : syracuseStep 3929879 = 5894819) B5894819
theorem B10479677 : Blo 2297435 10479677 := bstep (se 3 (by rfl) ⟨1964939, by rfl⟩ : syracuseStep 10479677 = 3929879) B3929879
theorem B27945805 : Blo 2297435 27945805 := bstep (se 3 (by rfl) ⟨5239838, by rfl⟩ : syracuseStep 27945805 = 10479677) B10479677
theorem B37261073 : Blo 2297435 37261073 := bstep (se 2 (by rfl) ⟨13972902, by rfl⟩ : syracuseStep 37261073 = 27945805) B27945805
theorem B99362861 : Blo 2297435 99362861 := bstep (se 3 (by rfl) ⟨18630536, by rfl⟩ : syracuseStep 99362861 = 37261073) B37261073
theorem B66241907 : Blo 2297435 66241907 := bstep (se 1 (by rfl) ⟨49681430, by rfl⟩ : syracuseStep 66241907 = 99362861) B99362861
theorem B44161271 : Blo 2297435 44161271 := bstep (se 1 (by rfl) ⟨33120953, by rfl⟩ : syracuseStep 44161271 = 66241907) B66241907
theorem B29440847 : Blo 2297435 29440847 := bstep (se 1 (by rfl) ⟨22080635, by rfl⟩ : syracuseStep 29440847 = 44161271) B44161271
theorem B19627231 : Blo 2297435 19627231 := bstep (se 1 (by rfl) ⟨14720423, by rfl⟩ : syracuseStep 19627231 = 29440847) B29440847
theorem B26169641 : Blo 2297435 26169641 := bstep (se 2 (by rfl) ⟨9813615, by rfl⟩ : syracuseStep 26169641 = 19627231) B19627231
theorem B17446427 : Blo 2297435 17446427 := bstep (se 1 (by rfl) ⟨13084820, by rfl⟩ : syracuseStep 17446427 = 26169641) B26169641
theorem B11630951 : Blo 2297435 11630951 := bstep (se 1 (by rfl) ⟨8723213, by rfl⟩ : syracuseStep 11630951 = 17446427) B17446427
theorem B7753967 : Blo 2297435 7753967 := bstep (se 1 (by rfl) ⟨5815475, by rfl⟩ : syracuseStep 7753967 = 11630951) B11630951
theorem B5169311 : Blo 2297435 5169311 := bstep (se 1 (by rfl) ⟨3876983, by rfl⟩ : syracuseStep 5169311 = 7753967) B7753967
theorem B3446207 : Blo 2297435 3446207 := bstep (se 1 (by rfl) ⟨2584655, by rfl⟩ : syracuseStep 3446207 = 5169311) B5169311
theorem B2297471 : Blo 2297435 2297471 := bstep (se 1 (by rfl) ⟨1723103, by rfl⟩ : syracuseStep 2297471 = 3446207) B3446207
theorem B3446213 : Blo 2297435 3446213 := bbase (se 4 (by rfl) ⟨323082, by rfl⟩ : syracuseStep 3446213 = 646165) (by norm_num)
theorem B2297475 : Blo 2297435 2297475 := bstep (se 1 (by rfl) ⟨1723106, by rfl⟩ : syracuseStep 2297475 = 3446213) B3446213
theorem B3876997 : Blo 2297435 3876997 := bbase (se 4 (by rfl) ⟨363468, by rfl⟩ : syracuseStep 3876997 = 726937) (by norm_num)
theorem B5169329 : Blo 2297435 5169329 := bstep (se 2 (by rfl) ⟨1938498, by rfl⟩ : syracuseStep 5169329 = 3876997) B3876997
theorem B3446219 : Blo 2297435 3446219 := bstep (se 1 (by rfl) ⟨2584664, by rfl⟩ : syracuseStep 3446219 = 5169329) B5169329
theorem B2297479 : Blo 2297435 2297479 := bstep (se 1 (by rfl) ⟨1723109, by rfl⟩ : syracuseStep 2297479 = 3446219) B3446219
theorem B2584669 : Blo 2297435 2584669 := bbase (se 3 (by rfl) ⟨484625, by rfl⟩ : syracuseStep 2584669 = 969251) (by norm_num)
theorem B3446225 : Blo 2297435 3446225 := bstep (se 2 (by rfl) ⟨1292334, by rfl⟩ : syracuseStep 3446225 = 2584669) B2584669
theorem B2297483 : Blo 2297435 2297483 := bstep (se 1 (by rfl) ⟨1723112, by rfl⟩ : syracuseStep 2297483 = 3446225) B3446225
theorem B7754021 : Blo 2297435 7754021 := bbase (se 4 (by rfl) ⟨726939, by rfl⟩ : syracuseStep 7754021 = 1453879) (by norm_num)
theorem B5169347 : Blo 2297435 5169347 := bstep (se 1 (by rfl) ⟨3877010, by rfl⟩ : syracuseStep 5169347 = 7754021) B7754021
theorem B3446231 : Blo 2297435 3446231 := bstep (se 1 (by rfl) ⟨2584673, by rfl⟩ : syracuseStep 3446231 = 5169347) B5169347
theorem B2297487 : Blo 2297435 2297487 := bstep (se 1 (by rfl) ⟨1723115, by rfl⟩ : syracuseStep 2297487 = 3446231) B3446231
theorem B3446237 : Blo 2297435 3446237 := bbase (se 3 (by rfl) ⟨646169, by rfl⟩ : syracuseStep 3446237 = 1292339) (by norm_num)
theorem B2297491 : Blo 2297435 2297491 := bstep (se 1 (by rfl) ⟨1723118, by rfl⟩ : syracuseStep 2297491 = 3446237) B3446237
theorem B5169365 : Blo 2297435 5169365 := bbase (se 7 (by rfl) ⟨60578, by rfl⟩ : syracuseStep 5169365 = 121157) (by norm_num)
theorem B3446243 : Blo 2297435 3446243 := bstep (se 1 (by rfl) ⟨2584682, by rfl⟩ : syracuseStep 3446243 = 5169365) B5169365
theorem B2297495 : Blo 2297435 2297495 := bstep (se 1 (by rfl) ⟨1723121, by rfl⟩ : syracuseStep 2297495 = 3446243) B3446243
theorem B13973077 : Blo 2297435 13973077 := bbase (se 8 (by rfl) ⟨81873, by rfl⟩ : syracuseStep 13973077 = 163747) (by norm_num)
theorem B18630769 : Blo 2297435 18630769 := bstep (se 2 (by rfl) ⟨6986538, by rfl⟩ : syracuseStep 18630769 = 13973077) B13973077
theorem B24841025 : Blo 2297435 24841025 := bstep (se 2 (by rfl) ⟨9315384, by rfl⟩ : syracuseStep 24841025 = 18630769) B18630769
theorem B16560683 : Blo 2297435 16560683 := bstep (se 1 (by rfl) ⟨12420512, by rfl⟩ : syracuseStep 16560683 = 24841025) B24841025
theorem B11040455 : Blo 2297435 11040455 := bstep (se 1 (by rfl) ⟨8280341, by rfl⟩ : syracuseStep 11040455 = 16560683) B16560683
theorem B7360303 : Blo 2297435 7360303 := bstep (se 1 (by rfl) ⟨5520227, by rfl⟩ : syracuseStep 7360303 = 11040455) B11040455
theorem B9813737 : Blo 2297435 9813737 := bstep (se 2 (by rfl) ⟨3680151, by rfl⟩ : syracuseStep 9813737 = 7360303) B7360303
theorem B6542491 : Blo 2297435 6542491 := bstep (se 1 (by rfl) ⟨4906868, by rfl⟩ : syracuseStep 6542491 = 9813737) B9813737
theorem B8723321 : Blo 2297435 8723321 := bstep (se 2 (by rfl) ⟨3271245, by rfl⟩ : syracuseStep 8723321 = 6542491) B6542491
theorem B5815547 : Blo 2297435 5815547 := bstep (se 1 (by rfl) ⟨4361660, by rfl⟩ : syracuseStep 5815547 = 8723321) B8723321
theorem B3877031 : Blo 2297435 3877031 := bstep (se 1 (by rfl) ⟨2907773, by rfl⟩ : syracuseStep 3877031 = 5815547) B5815547
theorem B2584687 : Blo 2297435 2584687 := bstep (se 1 (by rfl) ⟨1938515, by rfl⟩ : syracuseStep 2584687 = 3877031) B3877031
theorem B3446249 : Blo 2297435 3446249 := bstep (se 2 (by rfl) ⟨1292343, by rfl⟩ : syracuseStep 3446249 = 2584687) B2584687
theorem B2297499 : Blo 2297435 2297499 := bstep (se 1 (by rfl) ⟨1723124, by rfl⟩ : syracuseStep 2297499 = 3446249) B3446249
theorem B14720629 : Blo 2297435 14720629 := bbase (se 5 (by rfl) ⟨690029, by rfl⟩ : syracuseStep 14720629 = 1380059) (by norm_num)
theorem B19627505 : Blo 2297435 19627505 := bstep (se 2 (by rfl) ⟨7360314, by rfl⟩ : syracuseStep 19627505 = 14720629) B14720629
theorem B13085003 : Blo 2297435 13085003 := bstep (se 1 (by rfl) ⟨9813752, by rfl⟩ : syracuseStep 13085003 = 19627505) B19627505
theorem B8723335 : Blo 2297435 8723335 := bstep (se 1 (by rfl) ⟨6542501, by rfl⟩ : syracuseStep 8723335 = 13085003) B13085003
theorem B11631113 : Blo 2297435 11631113 := bstep (se 2 (by rfl) ⟨4361667, by rfl⟩ : syracuseStep 11631113 = 8723335) B8723335
theorem B7754075 : Blo 2297435 7754075 := bstep (se 1 (by rfl) ⟨5815556, by rfl⟩ : syracuseStep 7754075 = 11631113) B11631113
theorem B5169383 : Blo 2297435 5169383 := bstep (se 1 (by rfl) ⟨3877037, by rfl⟩ : syracuseStep 5169383 = 7754075) B7754075
theorem B3446255 : Blo 2297435 3446255 := bstep (se 1 (by rfl) ⟨2584691, by rfl⟩ : syracuseStep 3446255 = 5169383) B5169383
theorem B2297503 : Blo 2297435 2297503 := bstep (se 1 (by rfl) ⟨1723127, by rfl⟩ : syracuseStep 2297503 = 3446255) B3446255
theorem B3446261 : Blo 2297435 3446261 := bbase (se 5 (by rfl) ⟨161543, by rfl⟩ : syracuseStep 3446261 = 323087) (by norm_num)
theorem B2297507 : Blo 2297435 2297507 := bstep (se 1 (by rfl) ⟨1723130, by rfl⟩ : syracuseStep 2297507 = 3446261) B3446261
theorem B19895381 : Blo 2297435 19895381 := bbase (se 8 (by rfl) ⟨116574, by rfl⟩ : syracuseStep 19895381 = 233149) (by norm_num)
theorem B13263587 : Blo 2297435 13263587 := bstep (se 1 (by rfl) ⟨9947690, by rfl⟩ : syracuseStep 13263587 = 19895381) B19895381
theorem B8842391 : Blo 2297435 8842391 := bstep (se 1 (by rfl) ⟨6631793, by rfl⟩ : syracuseStep 8842391 = 13263587) B13263587
theorem B5894927 : Blo 2297435 5894927 := bstep (se 1 (by rfl) ⟨4421195, by rfl⟩ : syracuseStep 5894927 = 8842391) B8842391
theorem B3929951 : Blo 2297435 3929951 := bstep (se 1 (by rfl) ⟨2947463, by rfl⟩ : syracuseStep 3929951 = 5894927) B5894927
theorem B2619967 : Blo 2297435 2619967 := bstep (se 1 (by rfl) ⟨1964975, by rfl⟩ : syracuseStep 2619967 = 3929951) B3929951
theorem B3493289 : Blo 2297435 3493289 := bstep (se 2 (by rfl) ⟨1309983, by rfl⟩ : syracuseStep 3493289 = 2619967) B2619967
theorem B2328859 : Blo 2297435 2328859 := bstep (se 1 (by rfl) ⟨1746644, by rfl⟩ : syracuseStep 2328859 = 3493289) B3493289
theorem B3105145 : Blo 2297435 3105145 := bstep (se 2 (by rfl) ⟨1164429, by rfl⟩ : syracuseStep 3105145 = 2328859) B2328859
theorem B4140193 : Blo 2297435 4140193 := bstep (se 2 (by rfl) ⟨1552572, by rfl⟩ : syracuseStep 4140193 = 3105145) B3105145
theorem B5520257 : Blo 2297435 5520257 := bstep (se 2 (by rfl) ⟨2070096, by rfl⟩ : syracuseStep 5520257 = 4140193) B4140193
theorem B3680171 : Blo 2297435 3680171 := bstep (se 1 (by rfl) ⟨2760128, by rfl⟩ : syracuseStep 3680171 = 5520257) B5520257
theorem B2453447 : Blo 2297435 2453447 := bstep (se 1 (by rfl) ⟨1840085, by rfl⟩ : syracuseStep 2453447 = 3680171) B3680171
theorem B6542525 : Blo 2297435 6542525 := bstep (se 3 (by rfl) ⟨1226723, by rfl⟩ : syracuseStep 6542525 = 2453447) B2453447
theorem B4361683 : Blo 2297435 4361683 := bstep (se 1 (by rfl) ⟨3271262, by rfl⟩ : syracuseStep 4361683 = 6542525) B6542525
theorem B5815577 : Blo 2297435 5815577 := bstep (se 2 (by rfl) ⟨2180841, by rfl⟩ : syracuseStep 5815577 = 4361683) B4361683
theorem B3877051 : Blo 2297435 3877051 := bstep (se 1 (by rfl) ⟨2907788, by rfl⟩ : syracuseStep 3877051 = 5815577) B5815577
theorem B5169401 : Blo 2297435 5169401 := bstep (se 2 (by rfl) ⟨1938525, by rfl⟩ : syracuseStep 5169401 = 3877051) B3877051
theorem B3446267 : Blo 2297435 3446267 := bstep (se 1 (by rfl) ⟨2584700, by rfl⟩ : syracuseStep 3446267 = 5169401) B5169401
theorem B2297511 : Blo 2297435 2297511 := bstep (se 1 (by rfl) ⟨1723133, by rfl⟩ : syracuseStep 2297511 = 3446267) B3446267
theorem B2584705 : Blo 2297435 2584705 := bbase (se 2 (by rfl) ⟨969264, by rfl⟩ : syracuseStep 2584705 = 1938529) (by norm_num)
theorem B3446273 : Blo 2297435 3446273 := bstep (se 2 (by rfl) ⟨1292352, by rfl⟩ : syracuseStep 3446273 = 2584705) B2584705
theorem B2297515 : Blo 2297435 2297515 := bstep (se 1 (by rfl) ⟨1723136, by rfl⟩ : syracuseStep 2297515 = 3446273) B3446273
theorem B5815597 : Blo 2297435 5815597 := bbase (se 3 (by rfl) ⟨1090424, by rfl⟩ : syracuseStep 5815597 = 2180849) (by norm_num)
theorem B7754129 : Blo 2297435 7754129 := bstep (se 2 (by rfl) ⟨2907798, by rfl⟩ : syracuseStep 7754129 = 5815597) B5815597
theorem B5169419 : Blo 2297435 5169419 := bstep (se 1 (by rfl) ⟨3877064, by rfl⟩ : syracuseStep 5169419 = 7754129) B7754129
theorem B3446279 : Blo 2297435 3446279 := bstep (se 1 (by rfl) ⟨2584709, by rfl⟩ : syracuseStep 3446279 = 5169419) B5169419
theorem B2297519 : Blo 2297435 2297519 := bstep (se 1 (by rfl) ⟨1723139, by rfl⟩ : syracuseStep 2297519 = 3446279) B3446279
theorem B3446285 : Blo 2297435 3446285 := bbase (se 3 (by rfl) ⟨646178, by rfl⟩ : syracuseStep 3446285 = 1292357) (by norm_num)
theorem B2297523 : Blo 2297435 2297523 := bstep (se 1 (by rfl) ⟨1723142, by rfl⟩ : syracuseStep 2297523 = 3446285) B3446285
theorem B5169437 : Blo 2297435 5169437 := bbase (se 3 (by rfl) ⟨969269, by rfl⟩ : syracuseStep 5169437 = 1938539) (by norm_num)
theorem B3446291 : Blo 2297435 3446291 := bstep (se 1 (by rfl) ⟨2584718, by rfl⟩ : syracuseStep 3446291 = 5169437) B5169437
theorem B2297527 : Blo 2297435 2297527 := bstep (se 1 (by rfl) ⟨1723145, by rfl⟩ : syracuseStep 2297527 = 3446291) B3446291
theorem B3877085 : Blo 2297435 3877085 := bbase (se 3 (by rfl) ⟨726953, by rfl⟩ : syracuseStep 3877085 = 1453907) (by norm_num)
theorem B2584723 : Blo 2297435 2584723 := bstep (se 1 (by rfl) ⟨1938542, by rfl⟩ : syracuseStep 2584723 = 3877085) B3877085
theorem B3446297 : Blo 2297435 3446297 := bstep (se 2 (by rfl) ⟨1292361, by rfl⟩ : syracuseStep 3446297 = 2584723) B2584723
theorem B2297531 : Blo 2297435 2297531 := bstep (se 1 (by rfl) ⟨1723148, by rfl⟩ : syracuseStep 2297531 = 3446297) B3446297
theorem B4657765 : Blo 2297435 4657765 := bbase (se 4 (by rfl) ⟨436665, by rfl⟩ : syracuseStep 4657765 = 873331) (by norm_num)
theorem B6210353 : Blo 2297435 6210353 := bstep (se 2 (by rfl) ⟨2328882, by rfl⟩ : syracuseStep 6210353 = 4657765) B4657765
theorem B4140235 : Blo 2297435 4140235 := bstep (se 1 (by rfl) ⟨3105176, by rfl⟩ : syracuseStep 4140235 = 6210353) B6210353
theorem B5520313 : Blo 2297435 5520313 := bstep (se 2 (by rfl) ⟨2070117, by rfl⟩ : syracuseStep 5520313 = 4140235) B4140235
theorem B7360417 : Blo 2297435 7360417 := bstep (se 2 (by rfl) ⟨2760156, by rfl⟩ : syracuseStep 7360417 = 5520313) B5520313
theorem B9813889 : Blo 2297435 9813889 := bstep (se 2 (by rfl) ⟨3680208, by rfl⟩ : syracuseStep 9813889 = 7360417) B7360417
theorem B13085185 : Blo 2297435 13085185 := bstep (se 2 (by rfl) ⟨4906944, by rfl⟩ : syracuseStep 13085185 = 9813889) B9813889
theorem B17446913 : Blo 2297435 17446913 := bstep (se 2 (by rfl) ⟨6542592, by rfl⟩ : syracuseStep 17446913 = 13085185) B13085185
theorem B11631275 : Blo 2297435 11631275 := bstep (se 1 (by rfl) ⟨8723456, by rfl⟩ : syracuseStep 11631275 = 17446913) B17446913
theorem B7754183 : Blo 2297435 7754183 := bstep (se 1 (by rfl) ⟨5815637, by rfl⟩ : syracuseStep 7754183 = 11631275) B11631275
theorem B5169455 : Blo 2297435 5169455 := bstep (se 1 (by rfl) ⟨3877091, by rfl⟩ : syracuseStep 5169455 = 7754183) B7754183
theorem B3446303 : Blo 2297435 3446303 := bstep (se 1 (by rfl) ⟨2584727, by rfl⟩ : syracuseStep 3446303 = 5169455) B5169455
theorem B2297535 : Blo 2297435 2297535 := bstep (se 1 (by rfl) ⟨1723151, by rfl⟩ : syracuseStep 2297535 = 3446303) B3446303
theorem B3446309 : Blo 2297435 3446309 := bbase (se 4 (by rfl) ⟨323091, by rfl⟩ : syracuseStep 3446309 = 646183) (by norm_num)
theorem B2297539 : Blo 2297435 2297539 := bstep (se 1 (by rfl) ⟨1723154, by rfl⟩ : syracuseStep 2297539 = 3446309) B3446309
theorem B2907829 : Blo 2297435 2907829 := bbase (se 5 (by rfl) ⟨136304, by rfl⟩ : syracuseStep 2907829 = 272609) (by norm_num)
theorem B3877105 : Blo 2297435 3877105 := bstep (se 2 (by rfl) ⟨1453914, by rfl⟩ : syracuseStep 3877105 = 2907829) B2907829
theorem B5169473 : Blo 2297435 5169473 := bstep (se 2 (by rfl) ⟨1938552, by rfl⟩ : syracuseStep 5169473 = 3877105) B3877105
theorem B3446315 : Blo 2297435 3446315 := bstep (se 1 (by rfl) ⟨2584736, by rfl⟩ : syracuseStep 3446315 = 5169473) B5169473
theorem B2297543 : Blo 2297435 2297543 := bstep (se 1 (by rfl) ⟨1723157, by rfl⟩ : syracuseStep 2297543 = 3446315) B3446315
theorem B2584741 : Blo 2297435 2584741 := bbase (se 4 (by rfl) ⟨242319, by rfl⟩ : syracuseStep 2584741 = 484639) (by norm_num)
theorem B3446321 : Blo 2297435 3446321 := bstep (se 2 (by rfl) ⟨1292370, by rfl⟩ : syracuseStep 3446321 = 2584741) B2584741
theorem B2297547 : Blo 2297435 2297547 := bstep (se 1 (by rfl) ⟨1723160, by rfl⟩ : syracuseStep 2297547 = 3446321) B3446321
theorem B2947513 : Blo 2297435 2947513 := bbase (se 2 (by rfl) ⟨1105317, by rfl⟩ : syracuseStep 2947513 = 2210635) (by norm_num)
theorem B3930017 : Blo 2297435 3930017 := bstep (se 2 (by rfl) ⟨1473756, by rfl⟩ : syracuseStep 3930017 = 2947513) B2947513
theorem B10480045 : Blo 2297435 10480045 := bstep (se 3 (by rfl) ⟨1965008, by rfl⟩ : syracuseStep 10480045 = 3930017) B3930017
theorem B13973393 : Blo 2297435 13973393 := bstep (se 2 (by rfl) ⟨5240022, by rfl⟩ : syracuseStep 13973393 = 10480045) B10480045
theorem B9315595 : Blo 2297435 9315595 := bstep (se 1 (by rfl) ⟨6986696, by rfl⟩ : syracuseStep 9315595 = 13973393) B13973393
theorem B12420793 : Blo 2297435 12420793 := bstep (se 2 (by rfl) ⟨4657797, by rfl⟩ : syracuseStep 12420793 = 9315595) B9315595
theorem B16561057 : Blo 2297435 16561057 := bstep (se 2 (by rfl) ⟨6210396, by rfl⟩ : syracuseStep 16561057 = 12420793) B12420793
theorem B22081409 : Blo 2297435 22081409 := bstep (se 2 (by rfl) ⟨8280528, by rfl⟩ : syracuseStep 22081409 = 16561057) B16561057
theorem B14720939 : Blo 2297435 14720939 := bstep (se 1 (by rfl) ⟨11040704, by rfl⟩ : syracuseStep 14720939 = 22081409) B22081409
theorem B9813959 : Blo 2297435 9813959 := bstep (se 1 (by rfl) ⟨7360469, by rfl⟩ : syracuseStep 9813959 = 14720939) B14720939
theorem B6542639 : Blo 2297435 6542639 := bstep (se 1 (by rfl) ⟨4906979, by rfl⟩ : syracuseStep 6542639 = 9813959) B9813959
theorem B4361759 : Blo 2297435 4361759 := bstep (se 1 (by rfl) ⟨3271319, by rfl⟩ : syracuseStep 4361759 = 6542639) B6542639
theorem B2907839 : Blo 2297435 2907839 := bstep (se 1 (by rfl) ⟨2180879, by rfl⟩ : syracuseStep 2907839 = 4361759) B4361759
theorem B7754237 : Blo 2297435 7754237 := bstep (se 3 (by rfl) ⟨1453919, by rfl⟩ : syracuseStep 7754237 = 2907839) B2907839
theorem B5169491 : Blo 2297435 5169491 := bstep (se 1 (by rfl) ⟨3877118, by rfl⟩ : syracuseStep 5169491 = 7754237) B7754237
theorem B3446327 : Blo 2297435 3446327 := bstep (se 1 (by rfl) ⟨2584745, by rfl⟩ : syracuseStep 3446327 = 5169491) B5169491
theorem B2297551 : Blo 2297435 2297551 := bstep (se 1 (by rfl) ⟨1723163, by rfl⟩ : syracuseStep 2297551 = 3446327) B3446327
theorem B3446333 : Blo 2297435 3446333 := bbase (se 3 (by rfl) ⟨646187, by rfl⟩ : syracuseStep 3446333 = 1292375) (by norm_num)
theorem B2297555 : Blo 2297435 2297555 := bstep (se 1 (by rfl) ⟨1723166, by rfl⟩ : syracuseStep 2297555 = 3446333) B3446333
theorem B5169509 : Blo 2297435 5169509 := bbase (se 4 (by rfl) ⟨484641, by rfl⟩ : syracuseStep 5169509 = 969283) (by norm_num)
theorem B3446339 : Blo 2297435 3446339 := bstep (se 1 (by rfl) ⟨2584754, by rfl⟩ : syracuseStep 3446339 = 5169509) B5169509
theorem B2297559 : Blo 2297435 2297559 := bstep (se 1 (by rfl) ⟨1723169, by rfl⟩ : syracuseStep 2297559 = 3446339) B3446339
theorem B5815709 : Blo 2297435 5815709 := bbase (se 3 (by rfl) ⟨1090445, by rfl⟩ : syracuseStep 5815709 = 2180891) (by norm_num)
theorem B3877139 : Blo 2297435 3877139 := bstep (se 1 (by rfl) ⟨2907854, by rfl⟩ : syracuseStep 3877139 = 5815709) B5815709
theorem B2584759 : Blo 2297435 2584759 := bstep (se 1 (by rfl) ⟨1938569, by rfl⟩ : syracuseStep 2584759 = 3877139) B3877139
theorem B3446345 : Blo 2297435 3446345 := bstep (se 2 (by rfl) ⟨1292379, by rfl⟩ : syracuseStep 3446345 = 2584759) B2584759
theorem B2297563 : Blo 2297435 2297563 := bstep (se 1 (by rfl) ⟨1723172, by rfl⟩ : syracuseStep 2297563 = 3446345) B3446345
theorem B4361789 : Blo 2297435 4361789 := bbase (se 3 (by rfl) ⟨817835, by rfl⟩ : syracuseStep 4361789 = 1635671) (by norm_num)
theorem B11631437 : Blo 2297435 11631437 := bstep (se 3 (by rfl) ⟨2180894, by rfl⟩ : syracuseStep 11631437 = 4361789) B4361789
theorem B7754291 : Blo 2297435 7754291 := bstep (se 1 (by rfl) ⟨5815718, by rfl⟩ : syracuseStep 7754291 = 11631437) B11631437
theorem B5169527 : Blo 2297435 5169527 := bstep (se 1 (by rfl) ⟨3877145, by rfl⟩ : syracuseStep 5169527 = 7754291) B7754291
theorem B3446351 : Blo 2297435 3446351 := bstep (se 1 (by rfl) ⟨2584763, by rfl⟩ : syracuseStep 3446351 = 5169527) B5169527
theorem B2297567 : Blo 2297435 2297567 := bstep (se 1 (by rfl) ⟨1723175, by rfl⟩ : syracuseStep 2297567 = 3446351) B3446351
theorem B3446357 : Blo 2297435 3446357 := bbase (se 8 (by rfl) ⟨20193, by rfl⟩ : syracuseStep 3446357 = 40387) (by norm_num)
theorem B2297571 : Blo 2297435 2297571 := bstep (se 1 (by rfl) ⟨1723178, by rfl⟩ : syracuseStep 2297571 = 3446357) B3446357
theorem B2760205 : Blo 2297435 2760205 := bbase (se 3 (by rfl) ⟨517538, by rfl⟩ : syracuseStep 2760205 = 1035077) (by norm_num)
theorem B3680273 : Blo 2297435 3680273 := bstep (se 2 (by rfl) ⟨1380102, by rfl⟩ : syracuseStep 3680273 = 2760205) B2760205
theorem B9814061 : Blo 2297435 9814061 := bstep (se 3 (by rfl) ⟨1840136, by rfl⟩ : syracuseStep 9814061 = 3680273) B3680273
theorem B6542707 : Blo 2297435 6542707 := bstep (se 1 (by rfl) ⟨4907030, by rfl⟩ : syracuseStep 6542707 = 9814061) B9814061
theorem B8723609 : Blo 2297435 8723609 := bstep (se 2 (by rfl) ⟨3271353, by rfl⟩ : syracuseStep 8723609 = 6542707) B6542707
theorem B5815739 : Blo 2297435 5815739 := bstep (se 1 (by rfl) ⟨4361804, by rfl⟩ : syracuseStep 5815739 = 8723609) B8723609
theorem B3877159 : Blo 2297435 3877159 := bstep (se 1 (by rfl) ⟨2907869, by rfl⟩ : syracuseStep 3877159 = 5815739) B5815739
theorem B5169545 : Blo 2297435 5169545 := bstep (se 2 (by rfl) ⟨1938579, by rfl⟩ : syracuseStep 5169545 = 3877159) B3877159
theorem B3446363 : Blo 2297435 3446363 := bstep (se 1 (by rfl) ⟨2584772, by rfl⟩ : syracuseStep 3446363 = 5169545) B5169545
theorem B2297575 : Blo 2297435 2297575 := bstep (se 1 (by rfl) ⟨1723181, by rfl⟩ : syracuseStep 2297575 = 3446363) B3446363
theorem B2584777 : Blo 2297435 2584777 := bbase (se 2 (by rfl) ⟨969291, by rfl⟩ : syracuseStep 2584777 = 1938583) (by norm_num)
theorem B3446369 : Blo 2297435 3446369 := bstep (se 2 (by rfl) ⟨1292388, by rfl⟩ : syracuseStep 3446369 = 2584777) B2584777
theorem B2297579 : Blo 2297435 2297579 := bstep (se 1 (by rfl) ⟨1723184, by rfl⟩ : syracuseStep 2297579 = 3446369) B3446369
theorem B3493397 : Blo 2297435 3493397 := bbase (se 6 (by rfl) ⟨81876, by rfl⟩ : syracuseStep 3493397 = 163753) (by norm_num)
theorem B2328931 : Blo 2297435 2328931 := bstep (se 1 (by rfl) ⟨1746698, by rfl⟩ : syracuseStep 2328931 = 3493397) B3493397
theorem B12420965 : Blo 2297435 12420965 := bstep (se 4 (by rfl) ⟨1164465, by rfl⟩ : syracuseStep 12420965 = 2328931) B2328931
theorem B8280643 : Blo 2297435 8280643 := bstep (se 1 (by rfl) ⟨6210482, by rfl⟩ : syracuseStep 8280643 = 12420965) B12420965
theorem B11040857 : Blo 2297435 11040857 := bstep (se 2 (by rfl) ⟨4140321, by rfl⟩ : syracuseStep 11040857 = 8280643) B8280643
theorem B7360571 : Blo 2297435 7360571 := bstep (se 1 (by rfl) ⟨5520428, by rfl⟩ : syracuseStep 7360571 = 11040857) B11040857
theorem B19628189 : Blo 2297435 19628189 := bstep (se 3 (by rfl) ⟨3680285, by rfl⟩ : syracuseStep 19628189 = 7360571) B7360571
theorem B13085459 : Blo 2297435 13085459 := bstep (se 1 (by rfl) ⟨9814094, by rfl⟩ : syracuseStep 13085459 = 19628189) B19628189
theorem B8723639 : Blo 2297435 8723639 := bstep (se 1 (by rfl) ⟨6542729, by rfl⟩ : syracuseStep 8723639 = 13085459) B13085459
theorem B5815759 : Blo 2297435 5815759 := bstep (se 1 (by rfl) ⟨4361819, by rfl⟩ : syracuseStep 5815759 = 8723639) B8723639
theorem B7754345 : Blo 2297435 7754345 := bstep (se 2 (by rfl) ⟨2907879, by rfl⟩ : syracuseStep 7754345 = 5815759) B5815759
theorem B5169563 : Blo 2297435 5169563 := bstep (se 1 (by rfl) ⟨3877172, by rfl⟩ : syracuseStep 5169563 = 7754345) B7754345
theorem B3446375 : Blo 2297435 3446375 := bstep (se 1 (by rfl) ⟨2584781, by rfl⟩ : syracuseStep 3446375 = 5169563) B5169563
theorem B2297583 : Blo 2297435 2297583 := bstep (se 1 (by rfl) ⟨1723187, by rfl⟩ : syracuseStep 2297583 = 3446375) B3446375
theorem B3446381 : Blo 2297435 3446381 := bbase (se 3 (by rfl) ⟨646196, by rfl⟩ : syracuseStep 3446381 = 1292393) (by norm_num)
theorem B2297587 : Blo 2297435 2297587 := bstep (se 1 (by rfl) ⟨1723190, by rfl⟩ : syracuseStep 2297587 = 3446381) B3446381
theorem B5169581 : Blo 2297435 5169581 := bbase (se 3 (by rfl) ⟨969296, by rfl⟩ : syracuseStep 5169581 = 1938593) (by norm_num)
theorem B3446387 : Blo 2297435 3446387 := bstep (se 1 (by rfl) ⟨2584790, by rfl⟩ : syracuseStep 3446387 = 5169581) B5169581
theorem B2297591 : Blo 2297435 2297591 := bstep (se 1 (by rfl) ⟨1723193, by rfl⟩ : syracuseStep 2297591 = 3446387) B3446387
theorem B2453537 : Blo 2297435 2453537 := bbase (se 2 (by rfl) ⟨920076, by rfl⟩ : syracuseStep 2453537 = 1840153) (by norm_num)
theorem B6542765 : Blo 2297435 6542765 := bstep (se 3 (by rfl) ⟨1226768, by rfl⟩ : syracuseStep 6542765 = 2453537) B2453537
theorem B4361843 : Blo 2297435 4361843 := bstep (se 1 (by rfl) ⟨3271382, by rfl⟩ : syracuseStep 4361843 = 6542765) B6542765
theorem B2907895 : Blo 2297435 2907895 := bstep (se 1 (by rfl) ⟨2180921, by rfl⟩ : syracuseStep 2907895 = 4361843) B4361843
theorem B3877193 : Blo 2297435 3877193 := bstep (se 2 (by rfl) ⟨1453947, by rfl⟩ : syracuseStep 3877193 = 2907895) B2907895
theorem B2584795 : Blo 2297435 2584795 := bstep (se 1 (by rfl) ⟨1938596, by rfl⟩ : syracuseStep 2584795 = 3877193) B3877193
theorem B3446393 : Blo 2297435 3446393 := bstep (se 2 (by rfl) ⟨1292397, by rfl⟩ : syracuseStep 3446393 = 2584795) B2584795
theorem B2297595 : Blo 2297435 2297595 := bstep (se 1 (by rfl) ⟨1723196, by rfl⟩ : syracuseStep 2297595 = 3446393) B3446393
theorem B10480261 : Blo 2297435 10480261 := bbase (se 4 (by rfl) ⟨982524, by rfl⟩ : syracuseStep 10480261 = 1965049) (by norm_num)
theorem B13973681 : Blo 2297435 13973681 := bstep (se 2 (by rfl) ⟨5240130, by rfl⟩ : syracuseStep 13973681 = 10480261) B10480261
theorem B37263149 : Blo 2297435 37263149 := bstep (se 3 (by rfl) ⟨6986840, by rfl⟩ : syracuseStep 37263149 = 13973681) B13973681
theorem B24842099 : Blo 2297435 24842099 := bstep (se 1 (by rfl) ⟨18631574, by rfl⟩ : syracuseStep 24842099 = 37263149) B37263149
theorem B66245597 : Blo 2297435 66245597 := bstep (se 3 (by rfl) ⟨12421049, by rfl⟩ : syracuseStep 66245597 = 24842099) B24842099
theorem B44163731 : Blo 2297435 44163731 := bstep (se 1 (by rfl) ⟨33122798, by rfl⟩ : syracuseStep 44163731 = 66245597) B66245597
theorem B29442487 : Blo 2297435 29442487 := bstep (se 1 (by rfl) ⟨22081865, by rfl⟩ : syracuseStep 29442487 = 44163731) B44163731
theorem B39256649 : Blo 2297435 39256649 := bstep (se 2 (by rfl) ⟨14721243, by rfl⟩ : syracuseStep 39256649 = 29442487) B29442487
theorem B26171099 : Blo 2297435 26171099 := bstep (se 1 (by rfl) ⟨19628324, by rfl⟩ : syracuseStep 26171099 = 39256649) B39256649
theorem B17447399 : Blo 2297435 17447399 := bstep (se 1 (by rfl) ⟨13085549, by rfl⟩ : syracuseStep 17447399 = 26171099) B26171099
theorem B11631599 : Blo 2297435 11631599 := bstep (se 1 (by rfl) ⟨8723699, by rfl⟩ : syracuseStep 11631599 = 17447399) B17447399
theorem B7754399 : Blo 2297435 7754399 := bstep (se 1 (by rfl) ⟨5815799, by rfl⟩ : syracuseStep 7754399 = 11631599) B11631599
theorem B5169599 : Blo 2297435 5169599 := bstep (se 1 (by rfl) ⟨3877199, by rfl⟩ : syracuseStep 5169599 = 7754399) B7754399
theorem B3446399 : Blo 2297435 3446399 := bstep (se 1 (by rfl) ⟨2584799, by rfl⟩ : syracuseStep 3446399 = 5169599) B5169599
theorem B2297599 : Blo 2297435 2297599 := bstep (se 1 (by rfl) ⟨1723199, by rfl⟩ : syracuseStep 2297599 = 3446399) B3446399
theorem B3446405 : Blo 2297435 3446405 := bbase (se 4 (by rfl) ⟨323100, by rfl⟩ : syracuseStep 3446405 = 646201) (by norm_num)
theorem B2297603 : Blo 2297435 2297603 := bstep (se 1 (by rfl) ⟨1723202, by rfl⟩ : syracuseStep 2297603 = 3446405) B3446405
theorem B3877213 : Blo 2297435 3877213 := bbase (se 3 (by rfl) ⟨726977, by rfl⟩ : syracuseStep 3877213 = 1453955) (by norm_num)
theorem B5169617 : Blo 2297435 5169617 := bstep (se 2 (by rfl) ⟨1938606, by rfl⟩ : syracuseStep 5169617 = 3877213) B3877213
theorem B3446411 : Blo 2297435 3446411 := bstep (se 1 (by rfl) ⟨2584808, by rfl⟩ : syracuseStep 3446411 = 5169617) B5169617
theorem B2297607 : Blo 2297435 2297607 := bstep (se 1 (by rfl) ⟨1723205, by rfl⟩ : syracuseStep 2297607 = 3446411) B3446411
theorem B2584813 : Blo 2297435 2584813 := bbase (se 3 (by rfl) ⟨484652, by rfl⟩ : syracuseStep 2584813 = 969305) (by norm_num)
theorem B3446417 : Blo 2297435 3446417 := bstep (se 2 (by rfl) ⟨1292406, by rfl⟩ : syracuseStep 3446417 = 2584813) B2584813
theorem B2297611 : Blo 2297435 2297611 := bstep (se 1 (by rfl) ⟨1723208, by rfl⟩ : syracuseStep 2297611 = 3446417) B3446417
theorem B7754453 : Blo 2297435 7754453 := bbase (se 7 (by rfl) ⟨90872, by rfl⟩ : syracuseStep 7754453 = 181745) (by norm_num)
theorem B5169635 : Blo 2297435 5169635 := bstep (se 1 (by rfl) ⟨3877226, by rfl⟩ : syracuseStep 5169635 = 7754453) B7754453
theorem B3446423 : Blo 2297435 3446423 := bstep (se 1 (by rfl) ⟨2584817, by rfl⟩ : syracuseStep 3446423 = 5169635) B5169635
theorem B2297615 : Blo 2297435 2297615 := bstep (se 1 (by rfl) ⟨1723211, by rfl⟩ : syracuseStep 2297615 = 3446423) B3446423
theorem B3446429 : Blo 2297435 3446429 := bbase (se 3 (by rfl) ⟨646205, by rfl⟩ : syracuseStep 3446429 = 1292411) (by norm_num)
theorem B2297619 : Blo 2297435 2297619 := bstep (se 1 (by rfl) ⟨1723214, by rfl⟩ : syracuseStep 2297619 = 3446429) B3446429
theorem B5169653 : Blo 2297435 5169653 := bbase (se 5 (by rfl) ⟨242327, by rfl⟩ : syracuseStep 5169653 = 484655) (by norm_num)
theorem B3446435 : Blo 2297435 3446435 := bstep (se 1 (by rfl) ⟨2584826, by rfl⟩ : syracuseStep 3446435 = 5169653) B5169653
theorem B2297623 : Blo 2297435 2297623 := bstep (se 1 (by rfl) ⟨1723217, by rfl⟩ : syracuseStep 2297623 = 3446435) B3446435
theorem B3105301 : Blo 2297435 3105301 := bbase (se 6 (by rfl) ⟨72780, by rfl⟩ : syracuseStep 3105301 = 145561) (by norm_num)
theorem B4140401 : Blo 2297435 4140401 := bstep (se 2 (by rfl) ⟨1552650, by rfl⟩ : syracuseStep 4140401 = 3105301) B3105301
theorem B44164277 : Blo 2297435 44164277 := bstep (se 5 (by rfl) ⟨2070200, by rfl⟩ : syracuseStep 44164277 = 4140401) B4140401
theorem B29442851 : Blo 2297435 29442851 := bstep (se 1 (by rfl) ⟨22082138, by rfl⟩ : syracuseStep 29442851 = 44164277) B44164277
theorem B19628567 : Blo 2297435 19628567 := bstep (se 1 (by rfl) ⟨14721425, by rfl⟩ : syracuseStep 19628567 = 29442851) B29442851
theorem B13085711 : Blo 2297435 13085711 := bstep (se 1 (by rfl) ⟨9814283, by rfl⟩ : syracuseStep 13085711 = 19628567) B19628567
theorem B8723807 : Blo 2297435 8723807 := bstep (se 1 (by rfl) ⟨6542855, by rfl⟩ : syracuseStep 8723807 = 13085711) B13085711
theorem B5815871 : Blo 2297435 5815871 := bstep (se 1 (by rfl) ⟨4361903, by rfl⟩ : syracuseStep 5815871 = 8723807) B8723807
theorem B3877247 : Blo 2297435 3877247 := bstep (se 1 (by rfl) ⟨2907935, by rfl⟩ : syracuseStep 3877247 = 5815871) B5815871
theorem B2584831 : Blo 2297435 2584831 := bstep (se 1 (by rfl) ⟨1938623, by rfl⟩ : syracuseStep 2584831 = 3877247) B3877247
theorem B3446441 : Blo 2297435 3446441 := bstep (se 2 (by rfl) ⟨1292415, by rfl⟩ : syracuseStep 3446441 = 2584831) B2584831
theorem B2297627 : Blo 2297435 2297627 := bstep (se 1 (by rfl) ⟨1723220, by rfl⟩ : syracuseStep 2297627 = 3446441) B3446441
theorem B3316069 : Blo 2297435 3316069 := bbase (se 4 (by rfl) ⟨310881, by rfl⟩ : syracuseStep 3316069 = 621763) (by norm_num)
theorem B17685701 : Blo 2297435 17685701 := bstep (se 4 (by rfl) ⟨1658034, by rfl⟩ : syracuseStep 17685701 = 3316069) B3316069
theorem B11790467 : Blo 2297435 11790467 := bstep (se 1 (by rfl) ⟨8842850, by rfl⟩ : syracuseStep 11790467 = 17685701) B17685701
theorem B7860311 : Blo 2297435 7860311 := bstep (se 1 (by rfl) ⟨5895233, by rfl⟩ : syracuseStep 7860311 = 11790467) B11790467
theorem B5240207 : Blo 2297435 5240207 := bstep (se 1 (by rfl) ⟨3930155, by rfl⟩ : syracuseStep 5240207 = 7860311) B7860311
theorem B3493471 : Blo 2297435 3493471 := bstep (se 1 (by rfl) ⟨2620103, by rfl⟩ : syracuseStep 3493471 = 5240207) B5240207
theorem B4657961 : Blo 2297435 4657961 := bstep (se 2 (by rfl) ⟨1746735, by rfl⟩ : syracuseStep 4657961 = 3493471) B3493471
theorem B3105307 : Blo 2297435 3105307 := bstep (se 1 (by rfl) ⟨2328980, by rfl⟩ : syracuseStep 3105307 = 4657961) B4657961
theorem B4140409 : Blo 2297435 4140409 := bstep (se 2 (by rfl) ⟨1552653, by rfl⟩ : syracuseStep 4140409 = 3105307) B3105307
theorem B5520545 : Blo 2297435 5520545 := bstep (se 2 (by rfl) ⟨2070204, by rfl⟩ : syracuseStep 5520545 = 4140409) B4140409
theorem B3680363 : Blo 2297435 3680363 := bstep (se 1 (by rfl) ⟨2760272, by rfl⟩ : syracuseStep 3680363 = 5520545) B5520545
theorem B2453575 : Blo 2297435 2453575 := bstep (se 1 (by rfl) ⟨1840181, by rfl⟩ : syracuseStep 2453575 = 3680363) B3680363
theorem B3271433 : Blo 2297435 3271433 := bstep (se 2 (by rfl) ⟨1226787, by rfl⟩ : syracuseStep 3271433 = 2453575) B2453575
theorem B8723821 : Blo 2297435 8723821 := bstep (se 3 (by rfl) ⟨1635716, by rfl⟩ : syracuseStep 8723821 = 3271433) B3271433
theorem B11631761 : Blo 2297435 11631761 := bstep (se 2 (by rfl) ⟨4361910, by rfl⟩ : syracuseStep 11631761 = 8723821) B8723821
theorem B7754507 : Blo 2297435 7754507 := bstep (se 1 (by rfl) ⟨5815880, by rfl⟩ : syracuseStep 7754507 = 11631761) B11631761
theorem B5169671 : Blo 2297435 5169671 := bstep (se 1 (by rfl) ⟨3877253, by rfl⟩ : syracuseStep 5169671 = 7754507) B7754507
theorem B3446447 : Blo 2297435 3446447 := bstep (se 1 (by rfl) ⟨2584835, by rfl⟩ : syracuseStep 3446447 = 5169671) B5169671
theorem B2297631 : Blo 2297435 2297631 := bstep (se 1 (by rfl) ⟨1723223, by rfl⟩ : syracuseStep 2297631 = 3446447) B3446447
theorem B3446453 : Blo 2297435 3446453 := bbase (se 5 (by rfl) ⟨161552, by rfl⟩ : syracuseStep 3446453 = 323105) (by norm_num)
theorem B2297635 : Blo 2297435 2297635 := bstep (se 1 (by rfl) ⟨1723226, by rfl⟩ : syracuseStep 2297635 = 3446453) B3446453
theorem B5815901 : Blo 2297435 5815901 := bbase (se 3 (by rfl) ⟨1090481, by rfl⟩ : syracuseStep 5815901 = 2180963) (by norm_num)
theorem B3877267 : Blo 2297435 3877267 := bstep (se 1 (by rfl) ⟨2907950, by rfl⟩ : syracuseStep 3877267 = 5815901) B5815901
theorem B5169689 : Blo 2297435 5169689 := bstep (se 2 (by rfl) ⟨1938633, by rfl⟩ : syracuseStep 5169689 = 3877267) B3877267
theorem B3446459 : Blo 2297435 3446459 := bstep (se 1 (by rfl) ⟨2584844, by rfl⟩ : syracuseStep 3446459 = 5169689) B5169689
theorem B2297639 : Blo 2297435 2297639 := bstep (se 1 (by rfl) ⟨1723229, by rfl⟩ : syracuseStep 2297639 = 3446459) B3446459
theorem B2584849 : Blo 2297435 2584849 := bbase (se 2 (by rfl) ⟨969318, by rfl⟩ : syracuseStep 2584849 = 1938637) (by norm_num)
theorem B3446465 : Blo 2297435 3446465 := bstep (se 2 (by rfl) ⟨1292424, by rfl⟩ : syracuseStep 3446465 = 2584849) B2584849
theorem B2297643 : Blo 2297435 2297643 := bstep (se 1 (by rfl) ⟨1723232, by rfl⟩ : syracuseStep 2297643 = 3446465) B3446465
theorem B4361941 : Blo 2297435 4361941 := bbase (se 7 (by rfl) ⟨51116, by rfl⟩ : syracuseStep 4361941 = 102233) (by norm_num)
theorem B5815921 : Blo 2297435 5815921 := bstep (se 2 (by rfl) ⟨2180970, by rfl⟩ : syracuseStep 5815921 = 4361941) B4361941
theorem B7754561 : Blo 2297435 7754561 := bstep (se 2 (by rfl) ⟨2907960, by rfl⟩ : syracuseStep 7754561 = 5815921) B5815921
theorem B5169707 : Blo 2297435 5169707 := bstep (se 1 (by rfl) ⟨3877280, by rfl⟩ : syracuseStep 5169707 = 7754561) B7754561
theorem B3446471 : Blo 2297435 3446471 := bstep (se 1 (by rfl) ⟨2584853, by rfl⟩ : syracuseStep 3446471 = 5169707) B5169707
theorem B2297647 : Blo 2297435 2297647 := bstep (se 1 (by rfl) ⟨1723235, by rfl⟩ : syracuseStep 2297647 = 3446471) B3446471
theorem B3446477 : Blo 2297435 3446477 := bbase (se 3 (by rfl) ⟨646214, by rfl⟩ : syracuseStep 3446477 = 1292429) (by norm_num)
theorem B2297651 : Blo 2297435 2297651 := bstep (se 1 (by rfl) ⟨1723238, by rfl⟩ : syracuseStep 2297651 = 3446477) B3446477
theorem B5169725 : Blo 2297435 5169725 := bbase (se 3 (by rfl) ⟨969323, by rfl⟩ : syracuseStep 5169725 = 1938647) (by norm_num)
theorem B3446483 : Blo 2297435 3446483 := bstep (se 1 (by rfl) ⟨2584862, by rfl⟩ : syracuseStep 3446483 = 5169725) B5169725
theorem B2297655 : Blo 2297435 2297655 := bstep (se 1 (by rfl) ⟨1723241, by rfl⟩ : syracuseStep 2297655 = 3446483) B3446483
theorem B3877301 : Blo 2297435 3877301 := bbase (se 5 (by rfl) ⟨181748, by rfl⟩ : syracuseStep 3877301 = 363497) (by norm_num)
theorem B2584867 : Blo 2297435 2584867 := bstep (se 1 (by rfl) ⟨1938650, by rfl⟩ : syracuseStep 2584867 = 3877301) B3877301
theorem B3446489 : Blo 2297435 3446489 := bstep (se 2 (by rfl) ⟨1292433, by rfl⟩ : syracuseStep 3446489 = 2584867) B2584867
theorem B2297659 : Blo 2297435 2297659 := bstep (se 1 (by rfl) ⟨1723244, by rfl⟩ : syracuseStep 2297659 = 3446489) B3446489
theorem B2453609 : Blo 2297435 2453609 := bbase (se 2 (by rfl) ⟨920103, by rfl⟩ : syracuseStep 2453609 = 1840207) (by norm_num)
theorem B6542957 : Blo 2297435 6542957 := bstep (se 3 (by rfl) ⟨1226804, by rfl⟩ : syracuseStep 6542957 = 2453609) B2453609
theorem B17447885 : Blo 2297435 17447885 := bstep (se 3 (by rfl) ⟨3271478, by rfl⟩ : syracuseStep 17447885 = 6542957) B6542957
theorem B11631923 : Blo 2297435 11631923 := bstep (se 1 (by rfl) ⟨8723942, by rfl⟩ : syracuseStep 11631923 = 17447885) B17447885
theorem B7754615 : Blo 2297435 7754615 := bstep (se 1 (by rfl) ⟨5815961, by rfl⟩ : syracuseStep 7754615 = 11631923) B11631923
theorem B5169743 : Blo 2297435 5169743 := bstep (se 1 (by rfl) ⟨3877307, by rfl⟩ : syracuseStep 5169743 = 7754615) B7754615
theorem B3446495 : Blo 2297435 3446495 := bstep (se 1 (by rfl) ⟨2584871, by rfl⟩ : syracuseStep 3446495 = 5169743) B5169743
theorem B2297663 : Blo 2297435 2297663 := bstep (se 1 (by rfl) ⟨1723247, by rfl⟩ : syracuseStep 2297663 = 3446495) B3446495
theorem B3446501 : Blo 2297435 3446501 := bbase (se 4 (by rfl) ⟨323109, by rfl⟩ : syracuseStep 3446501 = 646219) (by norm_num)
theorem B2297667 : Blo 2297435 2297667 := bstep (se 1 (by rfl) ⟨1723250, by rfl⟩ : syracuseStep 2297667 = 3446501) B3446501
theorem B6542981 : Blo 2297435 6542981 := bbase (se 4 (by rfl) ⟨613404, by rfl⟩ : syracuseStep 6542981 = 1226809) (by norm_num)
theorem B4361987 : Blo 2297435 4361987 := bstep (se 1 (by rfl) ⟨3271490, by rfl⟩ : syracuseStep 4361987 = 6542981) B6542981
theorem B2907991 : Blo 2297435 2907991 := bstep (se 1 (by rfl) ⟨2180993, by rfl⟩ : syracuseStep 2907991 = 4361987) B4361987
theorem B3877321 : Blo 2297435 3877321 := bstep (se 2 (by rfl) ⟨1453995, by rfl⟩ : syracuseStep 3877321 = 2907991) B2907991
theorem B5169761 : Blo 2297435 5169761 := bstep (se 2 (by rfl) ⟨1938660, by rfl⟩ : syracuseStep 5169761 = 3877321) B3877321
theorem B3446507 : Blo 2297435 3446507 := bstep (se 1 (by rfl) ⟨2584880, by rfl⟩ : syracuseStep 3446507 = 5169761) B5169761
theorem B2297671 : Blo 2297435 2297671 := bstep (se 1 (by rfl) ⟨1723253, by rfl⟩ : syracuseStep 2297671 = 3446507) B3446507
theorem B2584885 : Blo 2297435 2584885 := bbase (se 5 (by rfl) ⟨121166, by rfl⟩ : syracuseStep 2584885 = 242333) (by norm_num)
theorem B3446513 : Blo 2297435 3446513 := bstep (se 2 (by rfl) ⟨1292442, by rfl⟩ : syracuseStep 3446513 = 2584885) B2584885
theorem B2297675 : Blo 2297435 2297675 := bstep (se 1 (by rfl) ⟨1723256, by rfl⟩ : syracuseStep 2297675 = 3446513) B3446513
theorem B2908001 : Blo 2297435 2908001 := bbase (se 2 (by rfl) ⟨1090500, by rfl⟩ : syracuseStep 2908001 = 2181001) (by norm_num)
theorem B7754669 : Blo 2297435 7754669 := bstep (se 3 (by rfl) ⟨1454000, by rfl⟩ : syracuseStep 7754669 = 2908001) B2908001
theorem B5169779 : Blo 2297435 5169779 := bstep (se 1 (by rfl) ⟨3877334, by rfl⟩ : syracuseStep 5169779 = 7754669) B7754669
theorem B3446519 : Blo 2297435 3446519 := bstep (se 1 (by rfl) ⟨2584889, by rfl⟩ : syracuseStep 3446519 = 5169779) B5169779
theorem B2297679 : Blo 2297435 2297679 := bstep (se 1 (by rfl) ⟨1723259, by rfl⟩ : syracuseStep 2297679 = 3446519) B3446519
theorem B3446525 : Blo 2297435 3446525 := bbase (se 3 (by rfl) ⟨646223, by rfl⟩ : syracuseStep 3446525 = 1292447) (by norm_num)
theorem B2297683 : Blo 2297435 2297683 := bstep (se 1 (by rfl) ⟨1723262, by rfl⟩ : syracuseStep 2297683 = 3446525) B3446525
theorem B5169797 : Blo 2297435 5169797 := bbase (se 4 (by rfl) ⟨484668, by rfl⟩ : syracuseStep 5169797 = 969337) (by norm_num)
theorem B3446531 : Blo 2297435 3446531 := bstep (se 1 (by rfl) ⟨2584898, by rfl⟩ : syracuseStep 3446531 = 5169797) B5169797
theorem B2297687 : Blo 2297435 2297687 := bstep (se 1 (by rfl) ⟨1723265, by rfl⟩ : syracuseStep 2297687 = 3446531) B3446531
theorem B16562069 : Blo 2297435 16562069 := bbase (se 6 (by rfl) ⟨388173, by rfl⟩ : syracuseStep 16562069 = 776347) (by norm_num)
theorem B11041379 : Blo 2297435 11041379 := bstep (se 1 (by rfl) ⟨8281034, by rfl⟩ : syracuseStep 11041379 = 16562069) B16562069
theorem B7360919 : Blo 2297435 7360919 := bstep (se 1 (by rfl) ⟨5520689, by rfl⟩ : syracuseStep 7360919 = 11041379) B11041379
theorem B4907279 : Blo 2297435 4907279 := bstep (se 1 (by rfl) ⟨3680459, by rfl⟩ : syracuseStep 4907279 = 7360919) B7360919
theorem B3271519 : Blo 2297435 3271519 := bstep (se 1 (by rfl) ⟨2453639, by rfl⟩ : syracuseStep 3271519 = 4907279) B4907279
theorem B4362025 : Blo 2297435 4362025 := bstep (se 2 (by rfl) ⟨1635759, by rfl⟩ : syracuseStep 4362025 = 3271519) B3271519
theorem B5816033 : Blo 2297435 5816033 := bstep (se 2 (by rfl) ⟨2181012, by rfl⟩ : syracuseStep 5816033 = 4362025) B4362025
theorem B3877355 : Blo 2297435 3877355 := bstep (se 1 (by rfl) ⟨2908016, by rfl⟩ : syracuseStep 3877355 = 5816033) B5816033
theorem B2584903 : Blo 2297435 2584903 := bstep (se 1 (by rfl) ⟨1938677, by rfl⟩ : syracuseStep 2584903 = 3877355) B3877355
theorem B3446537 : Blo 2297435 3446537 := bstep (se 2 (by rfl) ⟨1292451, by rfl⟩ : syracuseStep 3446537 = 2584903) B2584903
theorem B2297691 : Blo 2297435 2297691 := bstep (se 1 (by rfl) ⟨1723268, by rfl⟩ : syracuseStep 2297691 = 3446537) B3446537
theorem B11632085 : Blo 2297435 11632085 := bbase (se 7 (by rfl) ⟨136313, by rfl⟩ : syracuseStep 11632085 = 272627) (by norm_num)
theorem B7754723 : Blo 2297435 7754723 := bstep (se 1 (by rfl) ⟨5816042, by rfl⟩ : syracuseStep 7754723 = 11632085) B11632085
theorem B5169815 : Blo 2297435 5169815 := bstep (se 1 (by rfl) ⟨3877361, by rfl⟩ : syracuseStep 5169815 = 7754723) B7754723
theorem B3446543 : Blo 2297435 3446543 := bstep (se 1 (by rfl) ⟨2584907, by rfl⟩ : syracuseStep 3446543 = 5169815) B5169815
theorem B2297695 : Blo 2297435 2297695 := bstep (se 1 (by rfl) ⟨1723271, by rfl⟩ : syracuseStep 2297695 = 3446543) B3446543
theorem B3446549 : Blo 2297435 3446549 := bbase (se 6 (by rfl) ⟨80778, by rfl⟩ : syracuseStep 3446549 = 161557) (by norm_num)
theorem B2297699 : Blo 2297435 2297699 := bstep (se 1 (by rfl) ⟨1723274, by rfl⟩ : syracuseStep 2297699 = 3446549) B3446549
theorem B6632341 : Blo 2297435 6632341 := bbase (se 6 (by rfl) ⟨155445, by rfl⟩ : syracuseStep 6632341 = 310891) (by norm_num)
theorem B35372485 : Blo 2297435 35372485 := bstep (se 4 (by rfl) ⟨3316170, by rfl⟩ : syracuseStep 35372485 = 6632341) B6632341
theorem B47163313 : Blo 2297435 47163313 := bstep (se 2 (by rfl) ⟨17686242, by rfl⟩ : syracuseStep 47163313 = 35372485) B35372485
theorem B251537669 : Blo 2297435 251537669 := bstep (se 4 (by rfl) ⟨23581656, by rfl⟩ : syracuseStep 251537669 = 47163313) B47163313
theorem B167691779 : Blo 2297435 167691779 := bstep (se 1 (by rfl) ⟨125768834, by rfl⟩ : syracuseStep 167691779 = 251537669) B251537669
theorem B111794519 : Blo 2297435 111794519 := bstep (se 1 (by rfl) ⟨83845889, by rfl⟩ : syracuseStep 111794519 = 167691779) B167691779
theorem B74529679 : Blo 2297435 74529679 := bstep (se 1 (by rfl) ⟨55897259, by rfl⟩ : syracuseStep 74529679 = 111794519) B111794519
theorem B99372905 : Blo 2297435 99372905 := bstep (se 2 (by rfl) ⟨37264839, by rfl⟩ : syracuseStep 99372905 = 74529679) B74529679
theorem B66248603 : Blo 2297435 66248603 := bstep (se 1 (by rfl) ⟨49686452, by rfl⟩ : syracuseStep 66248603 = 99372905) B99372905
theorem B44165735 : Blo 2297435 44165735 := bstep (se 1 (by rfl) ⟨33124301, by rfl⟩ : syracuseStep 44165735 = 66248603) B66248603
theorem B29443823 : Blo 2297435 29443823 := bstep (se 1 (by rfl) ⟨22082867, by rfl⟩ : syracuseStep 29443823 = 44165735) B44165735
theorem B19629215 : Blo 2297435 19629215 := bstep (se 1 (by rfl) ⟨14721911, by rfl⟩ : syracuseStep 19629215 = 29443823) B29443823
theorem B13086143 : Blo 2297435 13086143 := bstep (se 1 (by rfl) ⟨9814607, by rfl⟩ : syracuseStep 13086143 = 19629215) B19629215
theorem B8724095 : Blo 2297435 8724095 := bstep (se 1 (by rfl) ⟨6543071, by rfl⟩ : syracuseStep 8724095 = 13086143) B13086143
theorem B5816063 : Blo 2297435 5816063 := bstep (se 1 (by rfl) ⟨4362047, by rfl⟩ : syracuseStep 5816063 = 8724095) B8724095
theorem B3877375 : Blo 2297435 3877375 := bstep (se 1 (by rfl) ⟨2908031, by rfl⟩ : syracuseStep 3877375 = 5816063) B5816063
theorem B5169833 : Blo 2297435 5169833 := bstep (se 2 (by rfl) ⟨1938687, by rfl⟩ : syracuseStep 5169833 = 3877375) B3877375
theorem B3446555 : Blo 2297435 3446555 := bstep (se 1 (by rfl) ⟨2584916, by rfl⟩ : syracuseStep 3446555 = 5169833) B5169833
theorem B2297703 : Blo 2297435 2297703 := bstep (se 1 (by rfl) ⟨1723277, by rfl⟩ : syracuseStep 2297703 = 3446555) B3446555
theorem B2584921 : Blo 2297435 2584921 := bbase (se 2 (by rfl) ⟨969345, by rfl⟩ : syracuseStep 2584921 = 1938691) (by norm_num)
theorem B3446561 : Blo 2297435 3446561 := bstep (se 2 (by rfl) ⟨1292460, by rfl⟩ : syracuseStep 3446561 = 2584921) B2584921
theorem B2297707 : Blo 2297435 2297707 := bstep (se 1 (by rfl) ⟨1723280, by rfl⟩ : syracuseStep 2297707 = 3446561) B3446561
theorem B5240389 : Blo 2297435 5240389 := bbase (se 4 (by rfl) ⟨491286, by rfl⟩ : syracuseStep 5240389 = 982573) (by norm_num)
theorem B6987185 : Blo 2297435 6987185 := bstep (se 2 (by rfl) ⟨2620194, by rfl⟩ : syracuseStep 6987185 = 5240389) B5240389
theorem B4658123 : Blo 2297435 4658123 := bstep (se 1 (by rfl) ⟨3493592, by rfl⟩ : syracuseStep 4658123 = 6987185) B6987185
theorem B3105415 : Blo 2297435 3105415 := bstep (se 1 (by rfl) ⟨2329061, by rfl⟩ : syracuseStep 3105415 = 4658123) B4658123
theorem B4140553 : Blo 2297435 4140553 := bstep (se 2 (by rfl) ⟨1552707, by rfl⟩ : syracuseStep 4140553 = 3105415) B3105415
theorem B5520737 : Blo 2297435 5520737 := bstep (se 2 (by rfl) ⟨2070276, by rfl⟩ : syracuseStep 5520737 = 4140553) B4140553
theorem B3680491 : Blo 2297435 3680491 := bstep (se 1 (by rfl) ⟨2760368, by rfl⟩ : syracuseStep 3680491 = 5520737) B5520737
theorem B4907321 : Blo 2297435 4907321 := bstep (se 2 (by rfl) ⟨1840245, by rfl⟩ : syracuseStep 4907321 = 3680491) B3680491
theorem B3271547 : Blo 2297435 3271547 := bstep (se 1 (by rfl) ⟨2453660, by rfl⟩ : syracuseStep 3271547 = 4907321) B4907321
theorem B8724125 : Blo 2297435 8724125 := bstep (se 3 (by rfl) ⟨1635773, by rfl⟩ : syracuseStep 8724125 = 3271547) B3271547
theorem B5816083 : Blo 2297435 5816083 := bstep (se 1 (by rfl) ⟨4362062, by rfl⟩ : syracuseStep 5816083 = 8724125) B8724125
theorem B7754777 : Blo 2297435 7754777 := bstep (se 2 (by rfl) ⟨2908041, by rfl⟩ : syracuseStep 7754777 = 5816083) B5816083
theorem B5169851 : Blo 2297435 5169851 := bstep (se 1 (by rfl) ⟨3877388, by rfl⟩ : syracuseStep 5169851 = 7754777) B7754777
theorem B3446567 : Blo 2297435 3446567 := bstep (se 1 (by rfl) ⟨2584925, by rfl⟩ : syracuseStep 3446567 = 5169851) B5169851
theorem B2297711 : Blo 2297435 2297711 := bstep (se 1 (by rfl) ⟨1723283, by rfl⟩ : syracuseStep 2297711 = 3446567) B3446567
theorem B3446573 : Blo 2297435 3446573 := bbase (se 3 (by rfl) ⟨646232, by rfl⟩ : syracuseStep 3446573 = 1292465) (by norm_num)
theorem B2297715 : Blo 2297435 2297715 := bstep (se 1 (by rfl) ⟨1723286, by rfl⟩ : syracuseStep 2297715 = 3446573) B3446573
theorem B5169869 : Blo 2297435 5169869 := bbase (se 3 (by rfl) ⟨969350, by rfl⟩ : syracuseStep 5169869 = 1938701) (by norm_num)
theorem B3446579 : Blo 2297435 3446579 := bstep (se 1 (by rfl) ⟨2584934, by rfl⟩ : syracuseStep 3446579 = 5169869) B5169869
theorem B2297719 : Blo 2297435 2297719 := bstep (se 1 (by rfl) ⟨1723289, by rfl⟩ : syracuseStep 2297719 = 3446579) B3446579
theorem B2908057 : Blo 2297435 2908057 := bbase (se 2 (by rfl) ⟨1090521, by rfl⟩ : syracuseStep 2908057 = 2181043) (by norm_num)
theorem B3877409 : Blo 2297435 3877409 := bstep (se 2 (by rfl) ⟨1454028, by rfl⟩ : syracuseStep 3877409 = 2908057) B2908057
theorem B2584939 : Blo 2297435 2584939 := bstep (se 1 (by rfl) ⟨1938704, by rfl⟩ : syracuseStep 2584939 = 3877409) B3877409
theorem B3446585 : Blo 2297435 3446585 := bstep (se 2 (by rfl) ⟨1292469, by rfl⟩ : syracuseStep 3446585 = 2584939) B2584939
theorem B2297723 : Blo 2297435 2297723 := bstep (se 1 (by rfl) ⟨1723292, by rfl⟩ : syracuseStep 2297723 = 3446585) B3446585
theorem B9814709 : Blo 2297435 9814709 := bbase (se 5 (by rfl) ⟨460064, by rfl⟩ : syracuseStep 9814709 = 920129) (by norm_num)
theorem B26172557 : Blo 2297435 26172557 := bstep (se 3 (by rfl) ⟨4907354, by rfl⟩ : syracuseStep 26172557 = 9814709) B9814709
theorem B17448371 : Blo 2297435 17448371 := bstep (se 1 (by rfl) ⟨13086278, by rfl⟩ : syracuseStep 17448371 = 26172557) B26172557
theorem B11632247 : Blo 2297435 11632247 := bstep (se 1 (by rfl) ⟨8724185, by rfl⟩ : syracuseStep 11632247 = 17448371) B17448371
theorem B7754831 : Blo 2297435 7754831 := bstep (se 1 (by rfl) ⟨5816123, by rfl⟩ : syracuseStep 7754831 = 11632247) B11632247
theorem B5169887 : Blo 2297435 5169887 := bstep (se 1 (by rfl) ⟨3877415, by rfl⟩ : syracuseStep 5169887 = 7754831) B7754831
theorem B3446591 : Blo 2297435 3446591 := bstep (se 1 (by rfl) ⟨2584943, by rfl⟩ : syracuseStep 3446591 = 5169887) B5169887
theorem B2297727 : Blo 2297435 2297727 := bstep (se 1 (by rfl) ⟨1723295, by rfl⟩ : syracuseStep 2297727 = 3446591) B3446591
theorem B3446597 : Blo 2297435 3446597 := bbase (se 4 (by rfl) ⟨323118, by rfl⟩ : syracuseStep 3446597 = 646237) (by norm_num)
theorem B2297731 : Blo 2297435 2297731 := bstep (se 1 (by rfl) ⟨1723298, by rfl⟩ : syracuseStep 2297731 = 3446597) B3446597
theorem B3877429 : Blo 2297435 3877429 := bbase (se 5 (by rfl) ⟨181754, by rfl⟩ : syracuseStep 3877429 = 363509) (by norm_num)
theorem B5169905 : Blo 2297435 5169905 := bstep (se 2 (by rfl) ⟨1938714, by rfl⟩ : syracuseStep 5169905 = 3877429) B3877429
theorem B3446603 : Blo 2297435 3446603 := bstep (se 1 (by rfl) ⟨2584952, by rfl⟩ : syracuseStep 3446603 = 5169905) B5169905
theorem B2297735 : Blo 2297435 2297735 := bstep (se 1 (by rfl) ⟨1723301, by rfl⟩ : syracuseStep 2297735 = 3446603) B3446603
theorem B2584957 : Blo 2297435 2584957 := bbase (se 3 (by rfl) ⟨484679, by rfl⟩ : syracuseStep 2584957 = 969359) (by norm_num)
theorem B3446609 : Blo 2297435 3446609 := bstep (se 2 (by rfl) ⟨1292478, by rfl⟩ : syracuseStep 3446609 = 2584957) B2584957
theorem B2297739 : Blo 2297435 2297739 := bstep (se 1 (by rfl) ⟨1723304, by rfl⟩ : syracuseStep 2297739 = 3446609) B3446609
theorem B7754885 : Blo 2297435 7754885 := bbase (se 4 (by rfl) ⟨727020, by rfl⟩ : syracuseStep 7754885 = 1454041) (by norm_num)
theorem B5169923 : Blo 2297435 5169923 := bstep (se 1 (by rfl) ⟨3877442, by rfl⟩ : syracuseStep 5169923 = 7754885) B7754885
theorem B3446615 : Blo 2297435 3446615 := bstep (se 1 (by rfl) ⟨2584961, by rfl⟩ : syracuseStep 3446615 = 5169923) B5169923
theorem B2297743 : Blo 2297435 2297743 := bstep (se 1 (by rfl) ⟨1723307, by rfl⟩ : syracuseStep 2297743 = 3446615) B3446615
theorem B3446621 : Blo 2297435 3446621 := bbase (se 3 (by rfl) ⟨646241, by rfl⟩ : syracuseStep 3446621 = 1292483) (by norm_num)
theorem B2297747 : Blo 2297435 2297747 := bstep (se 1 (by rfl) ⟨1723310, by rfl⟩ : syracuseStep 2297747 = 3446621) B3446621
theorem B5169941 : Blo 2297435 5169941 := bbase (se 6 (by rfl) ⟨121170, by rfl⟩ : syracuseStep 5169941 = 242341) (by norm_num)
theorem B3446627 : Blo 2297435 3446627 := bstep (se 1 (by rfl) ⟨2584970, by rfl⟩ : syracuseStep 3446627 = 5169941) B5169941
theorem B2297751 : Blo 2297435 2297751 := bstep (se 1 (by rfl) ⟨1723313, by rfl⟩ : syracuseStep 2297751 = 3446627) B3446627
theorem B8724293 : Blo 2297435 8724293 := bbase (se 4 (by rfl) ⟨817902, by rfl⟩ : syracuseStep 8724293 = 1635805) (by norm_num)
theorem B5816195 : Blo 2297435 5816195 := bstep (se 1 (by rfl) ⟨4362146, by rfl⟩ : syracuseStep 5816195 = 8724293) B8724293
theorem B3877463 : Blo 2297435 3877463 := bstep (se 1 (by rfl) ⟨2908097, by rfl⟩ : syracuseStep 3877463 = 5816195) B5816195
theorem B2584975 : Blo 2297435 2584975 := bstep (se 1 (by rfl) ⟨1938731, by rfl⟩ : syracuseStep 2584975 = 3877463) B3877463
theorem B3446633 : Blo 2297435 3446633 := bstep (se 2 (by rfl) ⟨1292487, by rfl⟩ : syracuseStep 3446633 = 2584975) B2584975
theorem B2297755 : Blo 2297435 2297755 := bstep (se 1 (by rfl) ⟨1723316, by rfl⟩ : syracuseStep 2297755 = 3446633) B3446633
theorem B4421669 : Blo 2297435 4421669 := bbase (se 4 (by rfl) ⟨414531, by rfl⟩ : syracuseStep 4421669 = 829063) (by norm_num)
theorem B11791117 : Blo 2297435 11791117 := bstep (se 3 (by rfl) ⟨2210834, by rfl⟩ : syracuseStep 11791117 = 4421669) B4421669
theorem B15721489 : Blo 2297435 15721489 := bstep (se 2 (by rfl) ⟨5895558, by rfl⟩ : syracuseStep 15721489 = 11791117) B11791117
theorem B20961985 : Blo 2297435 20961985 := bstep (se 2 (by rfl) ⟨7860744, by rfl⟩ : syracuseStep 20961985 = 15721489) B15721489
theorem B27949313 : Blo 2297435 27949313 := bstep (se 2 (by rfl) ⟨10480992, by rfl⟩ : syracuseStep 27949313 = 20961985) B20961985
theorem B18632875 : Blo 2297435 18632875 := bstep (se 1 (by rfl) ⟨13974656, by rfl⟩ : syracuseStep 18632875 = 27949313) B27949313
theorem B24843833 : Blo 2297435 24843833 := bstep (se 2 (by rfl) ⟨9316437, by rfl⟩ : syracuseStep 24843833 = 18632875) B18632875
theorem B16562555 : Blo 2297435 16562555 := bstep (se 1 (by rfl) ⟨12421916, by rfl⟩ : syracuseStep 16562555 = 24843833) B24843833
theorem B11041703 : Blo 2297435 11041703 := bstep (se 1 (by rfl) ⟨8281277, by rfl⟩ : syracuseStep 11041703 = 16562555) B16562555
theorem B7361135 : Blo 2297435 7361135 := bstep (se 1 (by rfl) ⟨5520851, by rfl⟩ : syracuseStep 7361135 = 11041703) B11041703
theorem B4907423 : Blo 2297435 4907423 := bstep (se 1 (by rfl) ⟨3680567, by rfl⟩ : syracuseStep 4907423 = 7361135) B7361135
theorem B13086461 : Blo 2297435 13086461 := bstep (se 3 (by rfl) ⟨2453711, by rfl⟩ : syracuseStep 13086461 = 4907423) B4907423
theorem B8724307 : Blo 2297435 8724307 := bstep (se 1 (by rfl) ⟨6543230, by rfl⟩ : syracuseStep 8724307 = 13086461) B13086461
theorem B11632409 : Blo 2297435 11632409 := bstep (se 2 (by rfl) ⟨4362153, by rfl⟩ : syracuseStep 11632409 = 8724307) B8724307
theorem B7754939 : Blo 2297435 7754939 := bstep (se 1 (by rfl) ⟨5816204, by rfl⟩ : syracuseStep 7754939 = 11632409) B11632409
theorem B5169959 : Blo 2297435 5169959 := bstep (se 1 (by rfl) ⟨3877469, by rfl⟩ : syracuseStep 5169959 = 7754939) B7754939
theorem B3446639 : Blo 2297435 3446639 := bstep (se 1 (by rfl) ⟨2584979, by rfl⟩ : syracuseStep 3446639 = 5169959) B5169959
theorem B2297759 : Blo 2297435 2297759 := bstep (se 1 (by rfl) ⟨1723319, by rfl⟩ : syracuseStep 2297759 = 3446639) B3446639
theorem B3446645 : Blo 2297435 3446645 := bbase (se 5 (by rfl) ⟨161561, by rfl⟩ : syracuseStep 3446645 = 323123) (by norm_num)
theorem B2297763 : Blo 2297435 2297763 := bstep (se 1 (by rfl) ⟨1723322, by rfl⟩ : syracuseStep 2297763 = 3446645) B3446645
theorem B3680581 : Blo 2297435 3680581 := bbase (se 4 (by rfl) ⟨345054, by rfl⟩ : syracuseStep 3680581 = 690109) (by norm_num)
theorem B4907441 : Blo 2297435 4907441 := bstep (se 2 (by rfl) ⟨1840290, by rfl⟩ : syracuseStep 4907441 = 3680581) B3680581
theorem B3271627 : Blo 2297435 3271627 := bstep (se 1 (by rfl) ⟨2453720, by rfl⟩ : syracuseStep 3271627 = 4907441) B4907441
theorem B4362169 : Blo 2297435 4362169 := bstep (se 2 (by rfl) ⟨1635813, by rfl⟩ : syracuseStep 4362169 = 3271627) B3271627
theorem B5816225 : Blo 2297435 5816225 := bstep (se 2 (by rfl) ⟨2181084, by rfl⟩ : syracuseStep 5816225 = 4362169) B4362169
theorem B3877483 : Blo 2297435 3877483 := bstep (se 1 (by rfl) ⟨2908112, by rfl⟩ : syracuseStep 3877483 = 5816225) B5816225
theorem B5169977 : Blo 2297435 5169977 := bstep (se 2 (by rfl) ⟨1938741, by rfl⟩ : syracuseStep 5169977 = 3877483) B3877483
theorem B3446651 : Blo 2297435 3446651 := bstep (se 1 (by rfl) ⟨2584988, by rfl⟩ : syracuseStep 3446651 = 5169977) B5169977
theorem B2297767 : Blo 2297435 2297767 := bstep (se 1 (by rfl) ⟨1723325, by rfl⟩ : syracuseStep 2297767 = 3446651) B3446651
theorem B2584993 : Blo 2297435 2584993 := bbase (se 2 (by rfl) ⟨969372, by rfl⟩ : syracuseStep 2584993 = 1938745) (by norm_num)
theorem B3446657 : Blo 2297435 3446657 := bstep (se 2 (by rfl) ⟨1292496, by rfl⟩ : syracuseStep 3446657 = 2584993) B2584993
theorem B2297771 : Blo 2297435 2297771 := bstep (se 1 (by rfl) ⟨1723328, by rfl⟩ : syracuseStep 2297771 = 3446657) B3446657
theorem B5816245 : Blo 2297435 5816245 := bbase (se 5 (by rfl) ⟨272636, by rfl⟩ : syracuseStep 5816245 = 545273) (by norm_num)
theorem B7754993 : Blo 2297435 7754993 := bstep (se 2 (by rfl) ⟨2908122, by rfl⟩ : syracuseStep 7754993 = 5816245) B5816245
theorem B5169995 : Blo 2297435 5169995 := bstep (se 1 (by rfl) ⟨3877496, by rfl⟩ : syracuseStep 5169995 = 7754993) B7754993
theorem B3446663 : Blo 2297435 3446663 := bstep (se 1 (by rfl) ⟨2584997, by rfl⟩ : syracuseStep 3446663 = 5169995) B5169995
theorem B2297775 : Blo 2297435 2297775 := bstep (se 1 (by rfl) ⟨1723331, by rfl⟩ : syracuseStep 2297775 = 3446663) B3446663
theorem B3446669 : Blo 2297435 3446669 := bbase (se 3 (by rfl) ⟨646250, by rfl⟩ : syracuseStep 3446669 = 1292501) (by norm_num)
theorem B2297779 : Blo 2297435 2297779 := bstep (se 1 (by rfl) ⟨1723334, by rfl⟩ : syracuseStep 2297779 = 3446669) B3446669
theorem B5170013 : Blo 2297435 5170013 := bbase (se 3 (by rfl) ⟨969377, by rfl⟩ : syracuseStep 5170013 = 1938755) (by norm_num)
theorem B3446675 : Blo 2297435 3446675 := bstep (se 1 (by rfl) ⟨2585006, by rfl⟩ : syracuseStep 3446675 = 5170013) B5170013
theorem B2297783 : Blo 2297435 2297783 := bstep (se 1 (by rfl) ⟨1723337, by rfl⟩ : syracuseStep 2297783 = 3446675) B3446675
theorem B3877517 : Blo 2297435 3877517 := bbase (se 3 (by rfl) ⟨727034, by rfl⟩ : syracuseStep 3877517 = 1454069) (by norm_num)
theorem B2585011 : Blo 2297435 2585011 := bstep (se 1 (by rfl) ⟨1938758, by rfl⟩ : syracuseStep 2585011 = 3877517) B3877517
theorem B3446681 : Blo 2297435 3446681 := bstep (se 2 (by rfl) ⟨1292505, by rfl⟩ : syracuseStep 3446681 = 2585011) B2585011
theorem B2297787 : Blo 2297435 2297787 := bstep (se 1 (by rfl) ⟨1723340, by rfl⟩ : syracuseStep 2297787 = 3446681) B3446681
theorem B7361237 : Blo 2297435 7361237 := bbase (se 7 (by rfl) ⟨86264, by rfl⟩ : syracuseStep 7361237 = 172529) (by norm_num)
theorem B19629965 : Blo 2297435 19629965 := bstep (se 3 (by rfl) ⟨3680618, by rfl⟩ : syracuseStep 19629965 = 7361237) B7361237
theorem B13086643 : Blo 2297435 13086643 := bstep (se 1 (by rfl) ⟨9814982, by rfl⟩ : syracuseStep 13086643 = 19629965) B19629965
theorem B17448857 : Blo 2297435 17448857 := bstep (se 2 (by rfl) ⟨6543321, by rfl⟩ : syracuseStep 17448857 = 13086643) B13086643
theorem B11632571 : Blo 2297435 11632571 := bstep (se 1 (by rfl) ⟨8724428, by rfl⟩ : syracuseStep 11632571 = 17448857) B17448857
theorem B7755047 : Blo 2297435 7755047 := bstep (se 1 (by rfl) ⟨5816285, by rfl⟩ : syracuseStep 7755047 = 11632571) B11632571
theorem B5170031 : Blo 2297435 5170031 := bstep (se 1 (by rfl) ⟨3877523, by rfl⟩ : syracuseStep 5170031 = 7755047) B7755047
theorem B3446687 : Blo 2297435 3446687 := bstep (se 1 (by rfl) ⟨2585015, by rfl⟩ : syracuseStep 3446687 = 5170031) B5170031
theorem B2297791 : Blo 2297435 2297791 := bstep (se 1 (by rfl) ⟨1723343, by rfl⟩ : syracuseStep 2297791 = 3446687) B3446687
theorem B3446693 : Blo 2297435 3446693 := bbase (se 4 (by rfl) ⟨323127, by rfl⟩ : syracuseStep 3446693 = 646255) (by norm_num)
theorem B2297795 : Blo 2297435 2297795 := bstep (se 1 (by rfl) ⟨1723346, by rfl⟩ : syracuseStep 2297795 = 3446693) B3446693
theorem B2908153 : Blo 2297435 2908153 := bbase (se 2 (by rfl) ⟨1090557, by rfl⟩ : syracuseStep 2908153 = 2181115) (by norm_num)
theorem B3877537 : Blo 2297435 3877537 := bstep (se 2 (by rfl) ⟨1454076, by rfl⟩ : syracuseStep 3877537 = 2908153) B2908153
theorem B5170049 : Blo 2297435 5170049 := bstep (se 2 (by rfl) ⟨1938768, by rfl⟩ : syracuseStep 5170049 = 3877537) B3877537
theorem B3446699 : Blo 2297435 3446699 := bstep (se 1 (by rfl) ⟨2585024, by rfl⟩ : syracuseStep 3446699 = 5170049) B5170049
theorem B2297799 : Blo 2297435 2297799 := bstep (se 1 (by rfl) ⟨1723349, by rfl⟩ : syracuseStep 2297799 = 3446699) B3446699
theorem B2585029 : Blo 2297435 2585029 := bbase (se 4 (by rfl) ⟨242346, by rfl⟩ : syracuseStep 2585029 = 484693) (by norm_num)
theorem B3446705 : Blo 2297435 3446705 := bstep (se 2 (by rfl) ⟨1292514, by rfl⟩ : syracuseStep 3446705 = 2585029) B2585029
theorem B2297803 : Blo 2297435 2297803 := bstep (se 1 (by rfl) ⟨1723352, by rfl⟩ : syracuseStep 2297803 = 3446705) B3446705
theorem B4362245 : Blo 2297435 4362245 := bbase (se 4 (by rfl) ⟨408960, by rfl⟩ : syracuseStep 4362245 = 817921) (by norm_num)
theorem B2908163 : Blo 2297435 2908163 := bstep (se 1 (by rfl) ⟨2181122, by rfl⟩ : syracuseStep 2908163 = 4362245) B4362245
theorem B7755101 : Blo 2297435 7755101 := bstep (se 3 (by rfl) ⟨1454081, by rfl⟩ : syracuseStep 7755101 = 2908163) B2908163
theorem B5170067 : Blo 2297435 5170067 := bstep (se 1 (by rfl) ⟨3877550, by rfl⟩ : syracuseStep 5170067 = 7755101) B7755101
theorem B3446711 : Blo 2297435 3446711 := bstep (se 1 (by rfl) ⟨2585033, by rfl⟩ : syracuseStep 3446711 = 5170067) B5170067
theorem B2297807 : Blo 2297435 2297807 := bstep (se 1 (by rfl) ⟨1723355, by rfl⟩ : syracuseStep 2297807 = 3446711) B3446711
theorem B3446717 : Blo 2297435 3446717 := bbase (se 3 (by rfl) ⟨646259, by rfl⟩ : syracuseStep 3446717 = 1292519) (by norm_num)
theorem B2297811 : Blo 2297435 2297811 := bstep (se 1 (by rfl) ⟨1723358, by rfl⟩ : syracuseStep 2297811 = 3446717) B3446717
theorem B5170085 : Blo 2297435 5170085 := bbase (se 4 (by rfl) ⟨484695, by rfl⟩ : syracuseStep 5170085 = 969391) (by norm_num)
theorem B3446723 : Blo 2297435 3446723 := bstep (se 1 (by rfl) ⟨2585042, by rfl⟩ : syracuseStep 3446723 = 5170085) B5170085
theorem B2297815 : Blo 2297435 2297815 := bstep (se 1 (by rfl) ⟨1723361, by rfl⟩ : syracuseStep 2297815 = 3446723) B3446723
theorem B5816357 : Blo 2297435 5816357 := bbase (se 4 (by rfl) ⟨545283, by rfl⟩ : syracuseStep 5816357 = 1090567) (by norm_num)
theorem B3877571 : Blo 2297435 3877571 := bstep (se 1 (by rfl) ⟨2908178, by rfl⟩ : syracuseStep 3877571 = 5816357) B5816357
theorem B2585047 : Blo 2297435 2585047 := bstep (se 1 (by rfl) ⟨1938785, by rfl⟩ : syracuseStep 2585047 = 3877571) B3877571
theorem B3446729 : Blo 2297435 3446729 := bstep (se 2 (by rfl) ⟨1292523, by rfl⟩ : syracuseStep 3446729 = 2585047) B2585047
theorem B2297819 : Blo 2297435 2297819 := bstep (se 1 (by rfl) ⟨1723364, by rfl⟩ : syracuseStep 2297819 = 3446729) B3446729
theorem B6543413 : Blo 2297435 6543413 := bbase (se 5 (by rfl) ⟨306722, by rfl⟩ : syracuseStep 6543413 = 613445) (by norm_num)
theorem B4362275 : Blo 2297435 4362275 := bstep (se 1 (by rfl) ⟨3271706, by rfl⟩ : syracuseStep 4362275 = 6543413) B6543413
theorem B11632733 : Blo 2297435 11632733 := bstep (se 3 (by rfl) ⟨2181137, by rfl⟩ : syracuseStep 11632733 = 4362275) B4362275
theorem B7755155 : Blo 2297435 7755155 := bstep (se 1 (by rfl) ⟨5816366, by rfl⟩ : syracuseStep 7755155 = 11632733) B11632733
theorem B5170103 : Blo 2297435 5170103 := bstep (se 1 (by rfl) ⟨3877577, by rfl⟩ : syracuseStep 5170103 = 7755155) B7755155
theorem B3446735 : Blo 2297435 3446735 := bstep (se 1 (by rfl) ⟨2585051, by rfl⟩ : syracuseStep 3446735 = 5170103) B5170103
theorem B2297823 : Blo 2297435 2297823 := bstep (se 1 (by rfl) ⟨1723367, by rfl⟩ : syracuseStep 2297823 = 3446735) B3446735
theorem B3446741 : Blo 2297435 3446741 := bbase (se 7 (by rfl) ⟨40391, by rfl⟩ : syracuseStep 3446741 = 80783) (by norm_num)
theorem B2297827 : Blo 2297435 2297827 := bstep (se 1 (by rfl) ⟨1723370, by rfl⟩ : syracuseStep 2297827 = 3446741) B3446741
theorem B8724581 : Blo 2297435 8724581 := bbase (se 4 (by rfl) ⟨817929, by rfl⟩ : syracuseStep 8724581 = 1635859) (by norm_num)
theorem B5816387 : Blo 2297435 5816387 := bstep (se 1 (by rfl) ⟨4362290, by rfl⟩ : syracuseStep 5816387 = 8724581) B8724581
theorem B3877591 : Blo 2297435 3877591 := bstep (se 1 (by rfl) ⟨2908193, by rfl⟩ : syracuseStep 3877591 = 5816387) B5816387
theorem B5170121 : Blo 2297435 5170121 := bstep (se 2 (by rfl) ⟨1938795, by rfl⟩ : syracuseStep 5170121 = 3877591) B3877591
theorem B3446747 : Blo 2297435 3446747 := bstep (se 1 (by rfl) ⟨2585060, by rfl⟩ : syracuseStep 3446747 = 5170121) B5170121
theorem B2297831 : Blo 2297435 2297831 := bstep (se 1 (by rfl) ⟨1723373, by rfl⟩ : syracuseStep 2297831 = 3446747) B3446747
theorem B2585065 : Blo 2297435 2585065 := bbase (se 2 (by rfl) ⟨969399, by rfl⟩ : syracuseStep 2585065 = 1938799) (by norm_num)
theorem B3446753 : Blo 2297435 3446753 := bstep (se 2 (by rfl) ⟨1292532, by rfl⟩ : syracuseStep 3446753 = 2585065) B2585065
theorem B2297835 : Blo 2297435 2297835 := bstep (se 1 (by rfl) ⟨1723376, by rfl⟩ : syracuseStep 2297835 = 3446753) B3446753
theorem B2453797 : Blo 2297435 2453797 := bbase (se 4 (by rfl) ⟨230043, by rfl⟩ : syracuseStep 2453797 = 460087) (by norm_num)
theorem B13086917 : Blo 2297435 13086917 := bstep (se 4 (by rfl) ⟨1226898, by rfl⟩ : syracuseStep 13086917 = 2453797) B2453797
theorem B8724611 : Blo 2297435 8724611 := bstep (se 1 (by rfl) ⟨6543458, by rfl⟩ : syracuseStep 8724611 = 13086917) B13086917
theorem B5816407 : Blo 2297435 5816407 := bstep (se 1 (by rfl) ⟨4362305, by rfl⟩ : syracuseStep 5816407 = 8724611) B8724611
theorem B7755209 : Blo 2297435 7755209 := bstep (se 2 (by rfl) ⟨2908203, by rfl⟩ : syracuseStep 7755209 = 5816407) B5816407
theorem B5170139 : Blo 2297435 5170139 := bstep (se 1 (by rfl) ⟨3877604, by rfl⟩ : syracuseStep 5170139 = 7755209) B7755209
theorem B3446759 : Blo 2297435 3446759 := bstep (se 1 (by rfl) ⟨2585069, by rfl⟩ : syracuseStep 3446759 = 5170139) B5170139
theorem B2297839 : Blo 2297435 2297839 := bstep (se 1 (by rfl) ⟨1723379, by rfl⟩ : syracuseStep 2297839 = 3446759) B3446759
theorem B3446765 : Blo 2297435 3446765 := bbase (se 3 (by rfl) ⟨646268, by rfl⟩ : syracuseStep 3446765 = 1292537) (by norm_num)
theorem B2297843 : Blo 2297435 2297843 := bstep (se 1 (by rfl) ⟨1723382, by rfl⟩ : syracuseStep 2297843 = 3446765) B3446765
theorem B5170157 : Blo 2297435 5170157 := bbase (se 3 (by rfl) ⟨969404, by rfl⟩ : syracuseStep 5170157 = 1938809) (by norm_num)
theorem B3446771 : Blo 2297435 3446771 := bstep (se 1 (by rfl) ⟨2585078, by rfl⟩ : syracuseStep 3446771 = 5170157) B5170157
theorem B2297847 : Blo 2297435 2297847 := bstep (se 1 (by rfl) ⟨1723385, by rfl⟩ : syracuseStep 2297847 = 3446771) B3446771
theorem B4907621 : Blo 2297435 4907621 := bbase (se 4 (by rfl) ⟨460089, by rfl⟩ : syracuseStep 4907621 = 920179) (by norm_num)
theorem B3271747 : Blo 2297435 3271747 := bstep (se 1 (by rfl) ⟨2453810, by rfl⟩ : syracuseStep 3271747 = 4907621) B4907621
theorem B4362329 : Blo 2297435 4362329 := bstep (se 2 (by rfl) ⟨1635873, by rfl⟩ : syracuseStep 4362329 = 3271747) B3271747
theorem B2908219 : Blo 2297435 2908219 := bstep (se 1 (by rfl) ⟨2181164, by rfl⟩ : syracuseStep 2908219 = 4362329) B4362329
theorem B3877625 : Blo 2297435 3877625 := bstep (se 2 (by rfl) ⟨1454109, by rfl⟩ : syracuseStep 3877625 = 2908219) B2908219
theorem B2585083 : Blo 2297435 2585083 := bstep (se 1 (by rfl) ⟨1938812, by rfl⟩ : syracuseStep 2585083 = 3877625) B3877625
theorem B3446777 : Blo 2297435 3446777 := bstep (se 2 (by rfl) ⟨1292541, by rfl⟩ : syracuseStep 3446777 = 2585083) B2585083
theorem B2297851 : Blo 2297435 2297851 := bstep (se 1 (by rfl) ⟨1723388, by rfl⟩ : syracuseStep 2297851 = 3446777) B3446777
theorem B10481429 : Blo 2297435 10481429 := bbase (se 6 (by rfl) ⟨245658, by rfl⟩ : syracuseStep 10481429 = 491317) (by norm_num)
theorem B6987619 : Blo 2297435 6987619 := bstep (se 1 (by rfl) ⟨5240714, by rfl⟩ : syracuseStep 6987619 = 10481429) B10481429
theorem B9316825 : Blo 2297435 9316825 := bstep (se 2 (by rfl) ⟨3493809, by rfl⟩ : syracuseStep 9316825 = 6987619) B6987619
theorem B198758933 : Blo 2297435 198758933 := bstep (se 6 (by rfl) ⟨4658412, by rfl⟩ : syracuseStep 198758933 = 9316825) B9316825
theorem B132505955 : Blo 2297435 132505955 := bstep (se 1 (by rfl) ⟨99379466, by rfl⟩ : syracuseStep 132505955 = 198758933) B198758933
theorem B88337303 : Blo 2297435 88337303 := bstep (se 1 (by rfl) ⟨66252977, by rfl⟩ : syracuseStep 88337303 = 132505955) B132505955
theorem B58891535 : Blo 2297435 58891535 := bstep (se 1 (by rfl) ⟨44168651, by rfl⟩ : syracuseStep 58891535 = 88337303) B88337303
theorem B39261023 : Blo 2297435 39261023 := bstep (se 1 (by rfl) ⟨29445767, by rfl⟩ : syracuseStep 39261023 = 58891535) B58891535
theorem B26174015 : Blo 2297435 26174015 := bstep (se 1 (by rfl) ⟨19630511, by rfl⟩ : syracuseStep 26174015 = 39261023) B39261023
theorem B17449343 : Blo 2297435 17449343 := bstep (se 1 (by rfl) ⟨13087007, by rfl⟩ : syracuseStep 17449343 = 26174015) B26174015
theorem B11632895 : Blo 2297435 11632895 := bstep (se 1 (by rfl) ⟨8724671, by rfl⟩ : syracuseStep 11632895 = 17449343) B17449343
theorem B7755263 : Blo 2297435 7755263 := bstep (se 1 (by rfl) ⟨5816447, by rfl⟩ : syracuseStep 7755263 = 11632895) B11632895
theorem B5170175 : Blo 2297435 5170175 := bstep (se 1 (by rfl) ⟨3877631, by rfl⟩ : syracuseStep 5170175 = 7755263) B7755263
theorem B3446783 : Blo 2297435 3446783 := bstep (se 1 (by rfl) ⟨2585087, by rfl⟩ : syracuseStep 3446783 = 5170175) B5170175
theorem B2297855 : Blo 2297435 2297855 := bstep (se 1 (by rfl) ⟨1723391, by rfl⟩ : syracuseStep 2297855 = 3446783) B3446783
theorem B3446789 : Blo 2297435 3446789 := bbase (se 4 (by rfl) ⟨323136, by rfl⟩ : syracuseStep 3446789 = 646273) (by norm_num)
theorem B2297859 : Blo 2297435 2297859 := bstep (se 1 (by rfl) ⟨1723394, by rfl⟩ : syracuseStep 2297859 = 3446789) B3446789
theorem B3877645 : Blo 2297435 3877645 := bbase (se 3 (by rfl) ⟨727058, by rfl⟩ : syracuseStep 3877645 = 1454117) (by norm_num)
theorem B5170193 : Blo 2297435 5170193 := bstep (se 2 (by rfl) ⟨1938822, by rfl⟩ : syracuseStep 5170193 = 3877645) B3877645
theorem B3446795 : Blo 2297435 3446795 := bstep (se 1 (by rfl) ⟨2585096, by rfl⟩ : syracuseStep 3446795 = 5170193) B5170193
theorem B2297863 : Blo 2297435 2297863 := bstep (se 1 (by rfl) ⟨1723397, by rfl⟩ : syracuseStep 2297863 = 3446795) B3446795
theorem B2585101 : Blo 2297435 2585101 := bbase (se 3 (by rfl) ⟨484706, by rfl⟩ : syracuseStep 2585101 = 969413) (by norm_num)
theorem B3446801 : Blo 2297435 3446801 := bstep (se 2 (by rfl) ⟨1292550, by rfl⟩ : syracuseStep 3446801 = 2585101) B2585101
theorem B2297867 : Blo 2297435 2297867 := bstep (se 1 (by rfl) ⟨1723400, by rfl⟩ : syracuseStep 2297867 = 3446801) B3446801
theorem B7755317 : Blo 2297435 7755317 := bbase (se 5 (by rfl) ⟨363530, by rfl⟩ : syracuseStep 7755317 = 727061) (by norm_num)
theorem B5170211 : Blo 2297435 5170211 := bstep (se 1 (by rfl) ⟨3877658, by rfl⟩ : syracuseStep 5170211 = 7755317) B7755317
theorem B3446807 : Blo 2297435 3446807 := bstep (se 1 (by rfl) ⟨2585105, by rfl⟩ : syracuseStep 3446807 = 5170211) B5170211
theorem B2297871 : Blo 2297435 2297871 := bstep (se 1 (by rfl) ⟨1723403, by rfl⟩ : syracuseStep 2297871 = 3446807) B3446807
theorem B3446813 : Blo 2297435 3446813 := bbase (se 3 (by rfl) ⟨646277, by rfl⟩ : syracuseStep 3446813 = 1292555) (by norm_num)
theorem B2297875 : Blo 2297435 2297875 := bstep (se 1 (by rfl) ⟨1723406, by rfl⟩ : syracuseStep 2297875 = 3446813) B3446813
theorem B5170229 : Blo 2297435 5170229 := bbase (se 5 (by rfl) ⟨242354, by rfl⟩ : syracuseStep 5170229 = 484709) (by norm_num)
theorem B3446819 : Blo 2297435 3446819 := bstep (se 1 (by rfl) ⟨2585114, by rfl⟩ : syracuseStep 3446819 = 5170229) B5170229
theorem B2297879 : Blo 2297435 2297879 := bstep (se 1 (by rfl) ⟨1723409, by rfl⟩ : syracuseStep 2297879 = 3446819) B3446819
theorem B4421909 : Blo 2297435 4421909 := bbase (se 6 (by rfl) ⟨103638, by rfl⟩ : syracuseStep 4421909 = 207277) (by norm_num)
theorem B11791757 : Blo 2297435 11791757 := bstep (se 3 (by rfl) ⟨2210954, by rfl⟩ : syracuseStep 11791757 = 4421909) B4421909
theorem B31444685 : Blo 2297435 31444685 := bstep (se 3 (by rfl) ⟨5895878, by rfl⟩ : syracuseStep 31444685 = 11791757) B11791757
theorem B20963123 : Blo 2297435 20963123 := bstep (se 1 (by rfl) ⟨15722342, by rfl⟩ : syracuseStep 20963123 = 31444685) B31444685
theorem B13975415 : Blo 2297435 13975415 := bstep (se 1 (by rfl) ⟨10481561, by rfl⟩ : syracuseStep 13975415 = 20963123) B20963123
theorem B9316943 : Blo 2297435 9316943 := bstep (se 1 (by rfl) ⟨6987707, by rfl⟩ : syracuseStep 9316943 = 13975415) B13975415
theorem B6211295 : Blo 2297435 6211295 := bstep (se 1 (by rfl) ⟨4658471, by rfl⟩ : syracuseStep 6211295 = 9316943) B9316943
theorem B4140863 : Blo 2297435 4140863 := bstep (se 1 (by rfl) ⟨3105647, by rfl⟩ : syracuseStep 4140863 = 6211295) B6211295
theorem B2760575 : Blo 2297435 2760575 := bstep (se 1 (by rfl) ⟨2070431, by rfl⟩ : syracuseStep 2760575 = 4140863) B4140863
theorem B7361533 : Blo 2297435 7361533 := bstep (se 3 (by rfl) ⟨1380287, by rfl⟩ : syracuseStep 7361533 = 2760575) B2760575
theorem B9815377 : Blo 2297435 9815377 := bstep (se 2 (by rfl) ⟨3680766, by rfl⟩ : syracuseStep 9815377 = 7361533) B7361533
theorem B13087169 : Blo 2297435 13087169 := bstep (se 2 (by rfl) ⟨4907688, by rfl⟩ : syracuseStep 13087169 = 9815377) B9815377
theorem B8724779 : Blo 2297435 8724779 := bstep (se 1 (by rfl) ⟨6543584, by rfl⟩ : syracuseStep 8724779 = 13087169) B13087169
theorem B5816519 : Blo 2297435 5816519 := bstep (se 1 (by rfl) ⟨4362389, by rfl⟩ : syracuseStep 5816519 = 8724779) B8724779
theorem B3877679 : Blo 2297435 3877679 := bstep (se 1 (by rfl) ⟨2908259, by rfl⟩ : syracuseStep 3877679 = 5816519) B5816519
theorem B2585119 : Blo 2297435 2585119 := bstep (se 1 (by rfl) ⟨1938839, by rfl⟩ : syracuseStep 2585119 = 3877679) B3877679
theorem B3446825 : Blo 2297435 3446825 := bstep (se 2 (by rfl) ⟨1292559, by rfl⟩ : syracuseStep 3446825 = 2585119) B2585119
theorem B2297883 : Blo 2297435 2297883 := bstep (se 1 (by rfl) ⟨1723412, by rfl⟩ : syracuseStep 2297883 = 3446825) B3446825
theorem B5240789 : Blo 2297435 5240789 := bbase (se 7 (by rfl) ⟨61415, by rfl⟩ : syracuseStep 5240789 = 122831) (by norm_num)
theorem B3493859 : Blo 2297435 3493859 := bstep (se 1 (by rfl) ⟨2620394, by rfl⟩ : syracuseStep 3493859 = 5240789) B5240789
theorem B9316957 : Blo 2297435 9316957 := bstep (se 3 (by rfl) ⟨1746929, by rfl⟩ : syracuseStep 9316957 = 3493859) B3493859
theorem B12422609 : Blo 2297435 12422609 := bstep (se 2 (by rfl) ⟨4658478, by rfl⟩ : syracuseStep 12422609 = 9316957) B9316957
theorem B8281739 : Blo 2297435 8281739 := bstep (se 1 (by rfl) ⟨6211304, by rfl⟩ : syracuseStep 8281739 = 12422609) B12422609
theorem B5521159 : Blo 2297435 5521159 := bstep (se 1 (by rfl) ⟨4140869, by rfl⟩ : syracuseStep 5521159 = 8281739) B8281739
theorem B7361545 : Blo 2297435 7361545 := bstep (se 2 (by rfl) ⟨2760579, by rfl⟩ : syracuseStep 7361545 = 5521159) B5521159
theorem B9815393 : Blo 2297435 9815393 := bstep (se 2 (by rfl) ⟨3680772, by rfl⟩ : syracuseStep 9815393 = 7361545) B7361545
theorem B6543595 : Blo 2297435 6543595 := bstep (se 1 (by rfl) ⟨4907696, by rfl⟩ : syracuseStep 6543595 = 9815393) B9815393
theorem B8724793 : Blo 2297435 8724793 := bstep (se 2 (by rfl) ⟨3271797, by rfl⟩ : syracuseStep 8724793 = 6543595) B6543595
theorem B11633057 : Blo 2297435 11633057 := bstep (se 2 (by rfl) ⟨4362396, by rfl⟩ : syracuseStep 11633057 = 8724793) B8724793
theorem B7755371 : Blo 2297435 7755371 := bstep (se 1 (by rfl) ⟨5816528, by rfl⟩ : syracuseStep 7755371 = 11633057) B11633057
theorem B5170247 : Blo 2297435 5170247 := bstep (se 1 (by rfl) ⟨3877685, by rfl⟩ : syracuseStep 5170247 = 7755371) B7755371
theorem B3446831 : Blo 2297435 3446831 := bstep (se 1 (by rfl) ⟨2585123, by rfl⟩ : syracuseStep 3446831 = 5170247) B5170247
theorem B2297887 : Blo 2297435 2297887 := bstep (se 1 (by rfl) ⟨1723415, by rfl⟩ : syracuseStep 2297887 = 3446831) B3446831
theorem B3446837 : Blo 2297435 3446837 := bbase (se 5 (by rfl) ⟨161570, by rfl⟩ : syracuseStep 3446837 = 323141) (by norm_num)
theorem B2297891 : Blo 2297435 2297891 := bstep (se 1 (by rfl) ⟨1723418, by rfl⟩ : syracuseStep 2297891 = 3446837) B3446837
theorem B5816549 : Blo 2297435 5816549 := bbase (se 4 (by rfl) ⟨545301, by rfl⟩ : syracuseStep 5816549 = 1090603) (by norm_num)
theorem B3877699 : Blo 2297435 3877699 := bstep (se 1 (by rfl) ⟨2908274, by rfl⟩ : syracuseStep 3877699 = 5816549) B5816549
theorem B5170265 : Blo 2297435 5170265 := bstep (se 2 (by rfl) ⟨1938849, by rfl⟩ : syracuseStep 5170265 = 3877699) B3877699
theorem B3446843 : Blo 2297435 3446843 := bstep (se 1 (by rfl) ⟨2585132, by rfl⟩ : syracuseStep 3446843 = 5170265) B5170265
theorem B2297895 : Blo 2297435 2297895 := bstep (se 1 (by rfl) ⟨1723421, by rfl⟩ : syracuseStep 2297895 = 3446843) B3446843
theorem B2585137 : Blo 2297435 2585137 := bbase (se 2 (by rfl) ⟨969426, by rfl⟩ : syracuseStep 2585137 = 1938853) (by norm_num)
theorem B3446849 : Blo 2297435 3446849 := bstep (se 2 (by rfl) ⟨1292568, by rfl⟩ : syracuseStep 3446849 = 2585137) B2585137
theorem B2297899 : Blo 2297435 2297899 := bstep (se 1 (by rfl) ⟨1723424, by rfl⟩ : syracuseStep 2297899 = 3446849) B3446849
theorem B6211349 : Blo 2297435 6211349 := bbase (se 6 (by rfl) ⟨145578, by rfl⟩ : syracuseStep 6211349 = 291157) (by norm_num)
theorem B4140899 : Blo 2297435 4140899 := bstep (se 1 (by rfl) ⟨3105674, by rfl⟩ : syracuseStep 4140899 = 6211349) B6211349
theorem B2760599 : Blo 2297435 2760599 := bstep (se 1 (by rfl) ⟨2070449, by rfl⟩ : syracuseStep 2760599 = 4140899) B4140899
theorem B7361597 : Blo 2297435 7361597 := bstep (se 3 (by rfl) ⟨1380299, by rfl⟩ : syracuseStep 7361597 = 2760599) B2760599
theorem B4907731 : Blo 2297435 4907731 := bstep (se 1 (by rfl) ⟨3680798, by rfl⟩ : syracuseStep 4907731 = 7361597) B7361597
theorem B6543641 : Blo 2297435 6543641 := bstep (se 2 (by rfl) ⟨2453865, by rfl⟩ : syracuseStep 6543641 = 4907731) B4907731
theorem B4362427 : Blo 2297435 4362427 := bstep (se 1 (by rfl) ⟨3271820, by rfl⟩ : syracuseStep 4362427 = 6543641) B6543641
theorem B5816569 : Blo 2297435 5816569 := bstep (se 2 (by rfl) ⟨2181213, by rfl⟩ : syracuseStep 5816569 = 4362427) B4362427
theorem B7755425 : Blo 2297435 7755425 := bstep (se 2 (by rfl) ⟨2908284, by rfl⟩ : syracuseStep 7755425 = 5816569) B5816569
theorem B5170283 : Blo 2297435 5170283 := bstep (se 1 (by rfl) ⟨3877712, by rfl⟩ : syracuseStep 5170283 = 7755425) B7755425
theorem B3446855 : Blo 2297435 3446855 := bstep (se 1 (by rfl) ⟨2585141, by rfl⟩ : syracuseStep 3446855 = 5170283) B5170283
theorem B2297903 : Blo 2297435 2297903 := bstep (se 1 (by rfl) ⟨1723427, by rfl⟩ : syracuseStep 2297903 = 3446855) B3446855
theorem B3446861 : Blo 2297435 3446861 := bbase (se 3 (by rfl) ⟨646286, by rfl⟩ : syracuseStep 3446861 = 1292573) (by norm_num)
theorem B2297907 : Blo 2297435 2297907 := bstep (se 1 (by rfl) ⟨1723430, by rfl⟩ : syracuseStep 2297907 = 3446861) B3446861
theorem B5170301 : Blo 2297435 5170301 := bbase (se 3 (by rfl) ⟨969431, by rfl⟩ : syracuseStep 5170301 = 1938863) (by norm_num)
theorem B3446867 : Blo 2297435 3446867 := bstep (se 1 (by rfl) ⟨2585150, by rfl⟩ : syracuseStep 3446867 = 5170301) B5170301
theorem B2297911 : Blo 2297435 2297911 := bstep (se 1 (by rfl) ⟨1723433, by rfl⟩ : syracuseStep 2297911 = 3446867) B3446867
theorem B3877733 : Blo 2297435 3877733 := bbase (se 4 (by rfl) ⟨363537, by rfl⟩ : syracuseStep 3877733 = 727075) (by norm_num)
theorem B2585155 : Blo 2297435 2585155 := bstep (se 1 (by rfl) ⟨1938866, by rfl⟩ : syracuseStep 2585155 = 3877733) B3877733
theorem B3446873 : Blo 2297435 3446873 := bstep (se 2 (by rfl) ⟨1292577, by rfl⟩ : syracuseStep 3446873 = 2585155) B2585155
theorem B2297915 : Blo 2297435 2297915 := bstep (se 1 (by rfl) ⟨1723436, by rfl⟩ : syracuseStep 2297915 = 3446873) B3446873
theorem B4907765 : Blo 2297435 4907765 := bbase (se 5 (by rfl) ⟨230051, by rfl⟩ : syracuseStep 4907765 = 460103) (by norm_num)
theorem B3271843 : Blo 2297435 3271843 := bstep (se 1 (by rfl) ⟨2453882, by rfl⟩ : syracuseStep 3271843 = 4907765) B4907765
theorem B17449829 : Blo 2297435 17449829 := bstep (se 4 (by rfl) ⟨1635921, by rfl⟩ : syracuseStep 17449829 = 3271843) B3271843
theorem B11633219 : Blo 2297435 11633219 := bstep (se 1 (by rfl) ⟨8724914, by rfl⟩ : syracuseStep 11633219 = 17449829) B17449829
theorem B7755479 : Blo 2297435 7755479 := bstep (se 1 (by rfl) ⟨5816609, by rfl⟩ : syracuseStep 7755479 = 11633219) B11633219
theorem B5170319 : Blo 2297435 5170319 := bstep (se 1 (by rfl) ⟨3877739, by rfl⟩ : syracuseStep 5170319 = 7755479) B7755479
theorem B3446879 : Blo 2297435 3446879 := bstep (se 1 (by rfl) ⟨2585159, by rfl⟩ : syracuseStep 3446879 = 5170319) B5170319
theorem B2297919 : Blo 2297435 2297919 := bstep (se 1 (by rfl) ⟨1723439, by rfl⟩ : syracuseStep 2297919 = 3446879) B3446879
theorem B3446885 : Blo 2297435 3446885 := bbase (se 4 (by rfl) ⟨323145, by rfl⟩ : syracuseStep 3446885 = 646291) (by norm_num)
theorem B2297923 : Blo 2297435 2297923 := bstep (se 1 (by rfl) ⟨1723442, by rfl⟩ : syracuseStep 2297923 = 3446885) B3446885
theorem B2620441 : Blo 2297435 2620441 := bbase (se 2 (by rfl) ⟨982665, by rfl⟩ : syracuseStep 2620441 = 1965331) (by norm_num)
theorem B3493921 : Blo 2297435 3493921 := bstep (se 2 (by rfl) ⟨1310220, by rfl⟩ : syracuseStep 3493921 = 2620441) B2620441
theorem B4658561 : Blo 2297435 4658561 := bstep (se 2 (by rfl) ⟨1746960, by rfl⟩ : syracuseStep 4658561 = 3493921) B3493921
theorem B3105707 : Blo 2297435 3105707 := bstep (se 1 (by rfl) ⟨2329280, by rfl⟩ : syracuseStep 3105707 = 4658561) B4658561
theorem B8281885 : Blo 2297435 8281885 := bstep (se 3 (by rfl) ⟨1552853, by rfl⟩ : syracuseStep 8281885 = 3105707) B3105707
theorem B11042513 : Blo 2297435 11042513 := bstep (se 2 (by rfl) ⟨4140942, by rfl⟩ : syracuseStep 11042513 = 8281885) B8281885
theorem B7361675 : Blo 2297435 7361675 := bstep (se 1 (by rfl) ⟨5521256, by rfl⟩ : syracuseStep 7361675 = 11042513) B11042513
theorem B4907783 : Blo 2297435 4907783 := bstep (se 1 (by rfl) ⟨3680837, by rfl⟩ : syracuseStep 4907783 = 7361675) B7361675
theorem B3271855 : Blo 2297435 3271855 := bstep (se 1 (by rfl) ⟨2453891, by rfl⟩ : syracuseStep 3271855 = 4907783) B4907783
theorem B4362473 : Blo 2297435 4362473 := bstep (se 2 (by rfl) ⟨1635927, by rfl⟩ : syracuseStep 4362473 = 3271855) B3271855
theorem B2908315 : Blo 2297435 2908315 := bstep (se 1 (by rfl) ⟨2181236, by rfl⟩ : syracuseStep 2908315 = 4362473) B4362473
theorem B3877753 : Blo 2297435 3877753 := bstep (se 2 (by rfl) ⟨1454157, by rfl⟩ : syracuseStep 3877753 = 2908315) B2908315
theorem B5170337 : Blo 2297435 5170337 := bstep (se 2 (by rfl) ⟨1938876, by rfl⟩ : syracuseStep 5170337 = 3877753) B3877753
theorem B3446891 : Blo 2297435 3446891 := bstep (se 1 (by rfl) ⟨2585168, by rfl⟩ : syracuseStep 3446891 = 5170337) B5170337
theorem B2297927 : Blo 2297435 2297927 := bstep (se 1 (by rfl) ⟨1723445, by rfl⟩ : syracuseStep 2297927 = 3446891) B3446891
theorem B2585173 : Blo 2297435 2585173 := bbase (se 8 (by rfl) ⟨15147, by rfl⟩ : syracuseStep 2585173 = 30295) (by norm_num)
theorem B3446897 : Blo 2297435 3446897 := bstep (se 2 (by rfl) ⟨1292586, by rfl⟩ : syracuseStep 3446897 = 2585173) B2585173
theorem B2297931 : Blo 2297435 2297931 := bstep (se 1 (by rfl) ⟨1723448, by rfl⟩ : syracuseStep 2297931 = 3446897) B3446897
theorem B2908325 : Blo 2297435 2908325 := bbase (se 4 (by rfl) ⟨272655, by rfl⟩ : syracuseStep 2908325 = 545311) (by norm_num)
theorem B7755533 : Blo 2297435 7755533 := bstep (se 3 (by rfl) ⟨1454162, by rfl⟩ : syracuseStep 7755533 = 2908325) B2908325
theorem B5170355 : Blo 2297435 5170355 := bstep (se 1 (by rfl) ⟨3877766, by rfl⟩ : syracuseStep 5170355 = 7755533) B7755533
theorem B3446903 : Blo 2297435 3446903 := bstep (se 1 (by rfl) ⟨2585177, by rfl⟩ : syracuseStep 3446903 = 5170355) B5170355
theorem B2297935 : Blo 2297435 2297935 := bstep (se 1 (by rfl) ⟨1723451, by rfl⟩ : syracuseStep 2297935 = 3446903) B3446903
theorem B3446909 : Blo 2297435 3446909 := bbase (se 3 (by rfl) ⟨646295, by rfl⟩ : syracuseStep 3446909 = 1292591) (by norm_num)
theorem B2297939 : Blo 2297435 2297939 := bstep (se 1 (by rfl) ⟨1723454, by rfl⟩ : syracuseStep 2297939 = 3446909) B3446909
theorem B5170373 : Blo 2297435 5170373 := bbase (se 4 (by rfl) ⟨484722, by rfl⟩ : syracuseStep 5170373 = 969445) (by norm_num)
theorem B3446915 : Blo 2297435 3446915 := bstep (se 1 (by rfl) ⟨2585186, by rfl⟩ : syracuseStep 3446915 = 5170373) B5170373
theorem B2297943 : Blo 2297435 2297943 := bstep (se 1 (by rfl) ⟨1723457, by rfl⟩ : syracuseStep 2297943 = 3446915) B3446915
theorem B14723477 : Blo 2297435 14723477 := bbase (se 6 (by rfl) ⟨345081, by rfl⟩ : syracuseStep 14723477 = 690163) (by norm_num)
theorem B9815651 : Blo 2297435 9815651 := bstep (se 1 (by rfl) ⟨7361738, by rfl⟩ : syracuseStep 9815651 = 14723477) B14723477
theorem B6543767 : Blo 2297435 6543767 := bstep (se 1 (by rfl) ⟨4907825, by rfl⟩ : syracuseStep 6543767 = 9815651) B9815651
theorem B4362511 : Blo 2297435 4362511 := bstep (se 1 (by rfl) ⟨3271883, by rfl⟩ : syracuseStep 4362511 = 6543767) B6543767
theorem B5816681 : Blo 2297435 5816681 := bstep (se 2 (by rfl) ⟨2181255, by rfl⟩ : syracuseStep 5816681 = 4362511) B4362511
theorem B3877787 : Blo 2297435 3877787 := bstep (se 1 (by rfl) ⟨2908340, by rfl⟩ : syracuseStep 3877787 = 5816681) B5816681
theorem B2585191 : Blo 2297435 2585191 := bstep (se 1 (by rfl) ⟨1938893, by rfl⟩ : syracuseStep 2585191 = 3877787) B3877787
theorem B3446921 : Blo 2297435 3446921 := bstep (se 2 (by rfl) ⟨1292595, by rfl⟩ : syracuseStep 3446921 = 2585191) B2585191
theorem B2297947 : Blo 2297435 2297947 := bstep (se 1 (by rfl) ⟨1723460, by rfl⟩ : syracuseStep 2297947 = 3446921) B3446921
theorem B11633381 : Blo 2297435 11633381 := bbase (se 4 (by rfl) ⟨1090629, by rfl⟩ : syracuseStep 11633381 = 2181259) (by norm_num)
theorem B7755587 : Blo 2297435 7755587 := bstep (se 1 (by rfl) ⟨5816690, by rfl⟩ : syracuseStep 7755587 = 11633381) B11633381
theorem B5170391 : Blo 2297435 5170391 := bstep (se 1 (by rfl) ⟨3877793, by rfl⟩ : syracuseStep 5170391 = 7755587) B7755587
theorem B3446927 : Blo 2297435 3446927 := bstep (se 1 (by rfl) ⟨2585195, by rfl⟩ : syracuseStep 3446927 = 5170391) B5170391
theorem B2297951 : Blo 2297435 2297951 := bstep (se 1 (by rfl) ⟨1723463, by rfl⟩ : syracuseStep 2297951 = 3446927) B3446927
theorem B3446933 : Blo 2297435 3446933 := bbase (se 6 (by rfl) ⟨80787, by rfl⟩ : syracuseStep 3446933 = 161575) (by norm_num)
theorem B2297955 : Blo 2297435 2297955 := bstep (se 1 (by rfl) ⟨1723466, by rfl⟩ : syracuseStep 2297955 = 3446933) B3446933
theorem B9815701 : Blo 2297435 9815701 := bbase (se 6 (by rfl) ⟨230055, by rfl⟩ : syracuseStep 9815701 = 460111) (by norm_num)
theorem B13087601 : Blo 2297435 13087601 := bstep (se 2 (by rfl) ⟨4907850, by rfl⟩ : syracuseStep 13087601 = 9815701) B9815701
theorem B8725067 : Blo 2297435 8725067 := bstep (se 1 (by rfl) ⟨6543800, by rfl⟩ : syracuseStep 8725067 = 13087601) B13087601
theorem B5816711 : Blo 2297435 5816711 := bstep (se 1 (by rfl) ⟨4362533, by rfl⟩ : syracuseStep 5816711 = 8725067) B8725067
theorem B3877807 : Blo 2297435 3877807 := bstep (se 1 (by rfl) ⟨2908355, by rfl⟩ : syracuseStep 3877807 = 5816711) B5816711
theorem B5170409 : Blo 2297435 5170409 := bstep (se 2 (by rfl) ⟨1938903, by rfl⟩ : syracuseStep 5170409 = 3877807) B3877807
theorem B3446939 : Blo 2297435 3446939 := bstep (se 1 (by rfl) ⟨2585204, by rfl⟩ : syracuseStep 3446939 = 5170409) B5170409
theorem B2297959 : Blo 2297435 2297959 := bstep (se 1 (by rfl) ⟨1723469, by rfl⟩ : syracuseStep 2297959 = 3446939) B3446939
theorem B2585209 : Blo 2297435 2585209 := bbase (se 2 (by rfl) ⟨969453, by rfl⟩ : syracuseStep 2585209 = 1938907) (by norm_num)
theorem B3446945 : Blo 2297435 3446945 := bstep (se 2 (by rfl) ⟨1292604, by rfl⟩ : syracuseStep 3446945 = 2585209) B2585209
theorem B2297963 : Blo 2297435 2297963 := bstep (se 1 (by rfl) ⟨1723472, by rfl⟩ : syracuseStep 2297963 = 3446945) B3446945
theorem B5896093 : Blo 2297435 5896093 := bbase (se 3 (by rfl) ⟨1105517, by rfl⟩ : syracuseStep 5896093 = 2211035) (by norm_num)
theorem B7861457 : Blo 2297435 7861457 := bstep (se 2 (by rfl) ⟨2948046, by rfl⟩ : syracuseStep 7861457 = 5896093) B5896093
theorem B5240971 : Blo 2297435 5240971 := bstep (se 1 (by rfl) ⟨3930728, by rfl⟩ : syracuseStep 5240971 = 7861457) B7861457
theorem B6987961 : Blo 2297435 6987961 := bstep (se 2 (by rfl) ⟨2620485, by rfl⟩ : syracuseStep 6987961 = 5240971) B5240971
theorem B9317281 : Blo 2297435 9317281 := bstep (se 2 (by rfl) ⟨3493980, by rfl⟩ : syracuseStep 9317281 = 6987961) B6987961
theorem B12423041 : Blo 2297435 12423041 := bstep (se 2 (by rfl) ⟨4658640, by rfl⟩ : syracuseStep 12423041 = 9317281) B9317281
theorem B8282027 : Blo 2297435 8282027 := bstep (se 1 (by rfl) ⟨6211520, by rfl⟩ : syracuseStep 8282027 = 12423041) B12423041
theorem B22085405 : Blo 2297435 22085405 := bstep (se 3 (by rfl) ⟨4141013, by rfl⟩ : syracuseStep 22085405 = 8282027) B8282027
theorem B14723603 : Blo 2297435 14723603 := bstep (se 1 (by rfl) ⟨11042702, by rfl⟩ : syracuseStep 14723603 = 22085405) B22085405
theorem B9815735 : Blo 2297435 9815735 := bstep (se 1 (by rfl) ⟨7361801, by rfl⟩ : syracuseStep 9815735 = 14723603) B14723603
theorem B6543823 : Blo 2297435 6543823 := bstep (se 1 (by rfl) ⟨4907867, by rfl⟩ : syracuseStep 6543823 = 9815735) B9815735
theorem B8725097 : Blo 2297435 8725097 := bstep (se 2 (by rfl) ⟨3271911, by rfl⟩ : syracuseStep 8725097 = 6543823) B6543823
theorem B5816731 : Blo 2297435 5816731 := bstep (se 1 (by rfl) ⟨4362548, by rfl⟩ : syracuseStep 5816731 = 8725097) B8725097
theorem B7755641 : Blo 2297435 7755641 := bstep (se 2 (by rfl) ⟨2908365, by rfl⟩ : syracuseStep 7755641 = 5816731) B5816731
theorem B5170427 : Blo 2297435 5170427 := bstep (se 1 (by rfl) ⟨3877820, by rfl⟩ : syracuseStep 5170427 = 7755641) B7755641
theorem B3446951 : Blo 2297435 3446951 := bstep (se 1 (by rfl) ⟨2585213, by rfl⟩ : syracuseStep 3446951 = 5170427) B5170427
theorem B2297967 : Blo 2297435 2297967 := bstep (se 1 (by rfl) ⟨1723475, by rfl⟩ : syracuseStep 2297967 = 3446951) B3446951
theorem B3446957 : Blo 2297435 3446957 := bbase (se 3 (by rfl) ⟨646304, by rfl⟩ : syracuseStep 3446957 = 1292609) (by norm_num)
theorem B2297971 : Blo 2297435 2297971 := bstep (se 1 (by rfl) ⟨1723478, by rfl⟩ : syracuseStep 2297971 = 3446957) B3446957
theorem B5170445 : Blo 2297435 5170445 := bbase (se 3 (by rfl) ⟨969458, by rfl⟩ : syracuseStep 5170445 = 1938917) (by norm_num)
theorem B3446963 : Blo 2297435 3446963 := bstep (se 1 (by rfl) ⟨2585222, by rfl⟩ : syracuseStep 3446963 = 5170445) B5170445
theorem B2297975 : Blo 2297435 2297975 := bstep (se 1 (by rfl) ⟨1723481, by rfl⟩ : syracuseStep 2297975 = 3446963) B3446963
theorem B2908381 : Blo 2297435 2908381 := bbase (se 3 (by rfl) ⟨545321, by rfl⟩ : syracuseStep 2908381 = 1090643) (by norm_num)
theorem B3877841 : Blo 2297435 3877841 := bstep (se 2 (by rfl) ⟨1454190, by rfl⟩ : syracuseStep 3877841 = 2908381) B2908381
theorem B2585227 : Blo 2297435 2585227 := bstep (se 1 (by rfl) ⟨1938920, by rfl⟩ : syracuseStep 2585227 = 3877841) B3877841
theorem B3446969 : Blo 2297435 3446969 := bstep (se 2 (by rfl) ⟨1292613, by rfl⟩ : syracuseStep 3446969 = 2585227) B2585227
theorem B2297979 : Blo 2297435 2297979 := bstep (se 1 (by rfl) ⟨1723484, by rfl⟩ : syracuseStep 2297979 = 3446969) B3446969
theorem B19631605 : Blo 2297435 19631605 := bbase (se 5 (by rfl) ⟨920231, by rfl⟩ : syracuseStep 19631605 = 1840463) (by norm_num)
theorem B26175473 : Blo 2297435 26175473 := bstep (se 2 (by rfl) ⟨9815802, by rfl⟩ : syracuseStep 26175473 = 19631605) B19631605
theorem B17450315 : Blo 2297435 17450315 := bstep (se 1 (by rfl) ⟨13087736, by rfl⟩ : syracuseStep 17450315 = 26175473) B26175473
theorem B11633543 : Blo 2297435 11633543 := bstep (se 1 (by rfl) ⟨8725157, by rfl⟩ : syracuseStep 11633543 = 17450315) B17450315
theorem B7755695 : Blo 2297435 7755695 := bstep (se 1 (by rfl) ⟨5816771, by rfl⟩ : syracuseStep 7755695 = 11633543) B11633543
theorem B5170463 : Blo 2297435 5170463 := bstep (se 1 (by rfl) ⟨3877847, by rfl⟩ : syracuseStep 5170463 = 7755695) B7755695
theorem B3446975 : Blo 2297435 3446975 := bstep (se 1 (by rfl) ⟨2585231, by rfl⟩ : syracuseStep 3446975 = 5170463) B5170463
theorem B2297983 : Blo 2297435 2297983 := bstep (se 1 (by rfl) ⟨1723487, by rfl⟩ : syracuseStep 2297983 = 3446975) B3446975
theorem B3446981 : Blo 2297435 3446981 := bbase (se 4 (by rfl) ⟨323154, by rfl⟩ : syracuseStep 3446981 = 646309) (by norm_num)
theorem B2297987 : Blo 2297435 2297987 := bstep (se 1 (by rfl) ⟨1723490, by rfl⟩ : syracuseStep 2297987 = 3446981) B3446981
theorem B3877861 : Blo 2297435 3877861 := bbase (se 4 (by rfl) ⟨363549, by rfl⟩ : syracuseStep 3877861 = 727099) (by norm_num)
theorem B5170481 : Blo 2297435 5170481 := bstep (se 2 (by rfl) ⟨1938930, by rfl⟩ : syracuseStep 5170481 = 3877861) B3877861
theorem B3446987 : Blo 2297435 3446987 := bstep (se 1 (by rfl) ⟨2585240, by rfl⟩ : syracuseStep 3446987 = 5170481) B5170481
theorem B2297991 : Blo 2297435 2297991 := bstep (se 1 (by rfl) ⟨1723493, by rfl⟩ : syracuseStep 2297991 = 3446987) B3446987
theorem B2585245 : Blo 2297435 2585245 := bbase (se 3 (by rfl) ⟨484733, by rfl⟩ : syracuseStep 2585245 = 969467) (by norm_num)
theorem B3446993 : Blo 2297435 3446993 := bstep (se 2 (by rfl) ⟨1292622, by rfl⟩ : syracuseStep 3446993 = 2585245) B2585245
theorem B2297995 : Blo 2297435 2297995 := bstep (se 1 (by rfl) ⟨1723496, by rfl⟩ : syracuseStep 2297995 = 3446993) B3446993
theorem B7755749 : Blo 2297435 7755749 := bbase (se 4 (by rfl) ⟨727101, by rfl⟩ : syracuseStep 7755749 = 1454203) (by norm_num)
theorem B5170499 : Blo 2297435 5170499 := bstep (se 1 (by rfl) ⟨3877874, by rfl⟩ : syracuseStep 5170499 = 7755749) B7755749
theorem B3446999 : Blo 2297435 3446999 := bstep (se 1 (by rfl) ⟨2585249, by rfl⟩ : syracuseStep 3446999 = 5170499) B5170499
theorem B2297999 : Blo 2297435 2297999 := bstep (se 1 (by rfl) ⟨1723499, by rfl⟩ : syracuseStep 2297999 = 3446999) B3446999
theorem B3447005 : Blo 2297435 3447005 := bbase (se 3 (by rfl) ⟨646313, by rfl⟩ : syracuseStep 3447005 = 1292627) (by norm_num)
theorem B2298003 : Blo 2297435 2298003 := bstep (se 1 (by rfl) ⟨1723502, by rfl⟩ : syracuseStep 2298003 = 3447005) B3447005
theorem B5170517 : Blo 2297435 5170517 := bbase (se 12 (by rfl) ⟨1893, by rfl⟩ : syracuseStep 5170517 = 3787) (by norm_num)
theorem B3447011 : Blo 2297435 3447011 := bstep (se 1 (by rfl) ⟨2585258, by rfl⟩ : syracuseStep 3447011 = 5170517) B5170517
theorem B2298007 : Blo 2297435 2298007 := bstep (se 1 (by rfl) ⟨1723505, by rfl⟩ : syracuseStep 2298007 = 3447011) B3447011
theorem B2453981 : Blo 2297435 2453981 := bbase (se 3 (by rfl) ⟨460121, by rfl⟩ : syracuseStep 2453981 = 920243) (by norm_num)
theorem B6543949 : Blo 2297435 6543949 := bstep (se 3 (by rfl) ⟨1226990, by rfl⟩ : syracuseStep 6543949 = 2453981) B2453981
theorem B8725265 : Blo 2297435 8725265 := bstep (se 2 (by rfl) ⟨3271974, by rfl⟩ : syracuseStep 8725265 = 6543949) B6543949
theorem B5816843 : Blo 2297435 5816843 := bstep (se 1 (by rfl) ⟨4362632, by rfl⟩ : syracuseStep 5816843 = 8725265) B8725265
theorem B3877895 : Blo 2297435 3877895 := bstep (se 1 (by rfl) ⟨2908421, by rfl⟩ : syracuseStep 3877895 = 5816843) B5816843
theorem B2585263 : Blo 2297435 2585263 := bstep (se 1 (by rfl) ⟨1938947, by rfl⟩ : syracuseStep 2585263 = 3877895) B3877895
theorem B3447017 : Blo 2297435 3447017 := bstep (se 2 (by rfl) ⟨1292631, by rfl⟩ : syracuseStep 3447017 = 2585263) B2585263
theorem B2298011 : Blo 2297435 2298011 := bstep (se 1 (by rfl) ⟨1723508, by rfl⟩ : syracuseStep 2298011 = 3447017) B3447017
theorem B3494053 : Blo 2297435 3494053 := bbase (se 4 (by rfl) ⟨327567, by rfl⟩ : syracuseStep 3494053 = 655135) (by norm_num)
theorem B18634949 : Blo 2297435 18634949 := bstep (se 4 (by rfl) ⟨1747026, by rfl⟩ : syracuseStep 18634949 = 3494053) B3494053
theorem B12423299 : Blo 2297435 12423299 := bstep (se 1 (by rfl) ⟨9317474, by rfl⟩ : syracuseStep 12423299 = 18634949) B18634949
theorem B33128797 : Blo 2297435 33128797 := bstep (se 3 (by rfl) ⟨6211649, by rfl⟩ : syracuseStep 33128797 = 12423299) B12423299
theorem B44171729 : Blo 2297435 44171729 := bstep (se 2 (by rfl) ⟨16564398, by rfl⟩ : syracuseStep 44171729 = 33128797) B33128797
theorem B29447819 : Blo 2297435 29447819 := bstep (se 1 (by rfl) ⟨22085864, by rfl⟩ : syracuseStep 29447819 = 44171729) B44171729
theorem B19631879 : Blo 2297435 19631879 := bstep (se 1 (by rfl) ⟨14723909, by rfl⟩ : syracuseStep 19631879 = 29447819) B29447819
theorem B13087919 : Blo 2297435 13087919 := bstep (se 1 (by rfl) ⟨9815939, by rfl⟩ : syracuseStep 13087919 = 19631879) B19631879
theorem B8725279 : Blo 2297435 8725279 := bstep (se 1 (by rfl) ⟨6543959, by rfl⟩ : syracuseStep 8725279 = 13087919) B13087919
theorem B11633705 : Blo 2297435 11633705 := bstep (se 2 (by rfl) ⟨4362639, by rfl⟩ : syracuseStep 11633705 = 8725279) B8725279
theorem B7755803 : Blo 2297435 7755803 := bstep (se 1 (by rfl) ⟨5816852, by rfl⟩ : syracuseStep 7755803 = 11633705) B11633705
theorem B5170535 : Blo 2297435 5170535 := bstep (se 1 (by rfl) ⟨3877901, by rfl⟩ : syracuseStep 5170535 = 7755803) B7755803
theorem B3447023 : Blo 2297435 3447023 := bstep (se 1 (by rfl) ⟨2585267, by rfl⟩ : syracuseStep 3447023 = 5170535) B5170535
theorem B2298015 : Blo 2297435 2298015 := bstep (se 1 (by rfl) ⟨1723511, by rfl⟩ : syracuseStep 2298015 = 3447023) B3447023
theorem B3447029 : Blo 2297435 3447029 := bbase (se 5 (by rfl) ⟨161579, by rfl⟩ : syracuseStep 3447029 = 323159) (by norm_num)
theorem B2298019 : Blo 2297435 2298019 := bstep (se 1 (by rfl) ⟨1723514, by rfl⟩ : syracuseStep 2298019 = 3447029) B3447029
theorem B3731213 : Blo 2297435 3731213 := bbase (se 3 (by rfl) ⟨699602, by rfl⟩ : syracuseStep 3731213 = 1399205) (by norm_num)
theorem B2487475 : Blo 2297435 2487475 := bstep (se 1 (by rfl) ⟨1865606, by rfl⟩ : syracuseStep 2487475 = 3731213) B3731213
theorem B3316633 : Blo 2297435 3316633 := bstep (se 2 (by rfl) ⟨1243737, by rfl⟩ : syracuseStep 3316633 = 2487475) B2487475
theorem B17688709 : Blo 2297435 17688709 := bstep (se 4 (by rfl) ⟨1658316, by rfl⟩ : syracuseStep 17688709 = 3316633) B3316633
theorem B23584945 : Blo 2297435 23584945 := bstep (se 2 (by rfl) ⟨8844354, by rfl⟩ : syracuseStep 23584945 = 17688709) B17688709
theorem B31446593 : Blo 2297435 31446593 := bstep (se 2 (by rfl) ⟨11792472, by rfl⟩ : syracuseStep 31446593 = 23584945) B23584945
theorem B20964395 : Blo 2297435 20964395 := bstep (se 1 (by rfl) ⟨15723296, by rfl⟩ : syracuseStep 20964395 = 31446593) B31446593
theorem B13976263 : Blo 2297435 13976263 := bstep (se 1 (by rfl) ⟨10482197, by rfl⟩ : syracuseStep 13976263 = 20964395) B20964395
theorem B18635017 : Blo 2297435 18635017 := bstep (se 2 (by rfl) ⟨6988131, by rfl⟩ : syracuseStep 18635017 = 13976263) B13976263
theorem B24846689 : Blo 2297435 24846689 := bstep (se 2 (by rfl) ⟨9317508, by rfl⟩ : syracuseStep 24846689 = 18635017) B18635017
theorem B16564459 : Blo 2297435 16564459 := bstep (se 1 (by rfl) ⟨12423344, by rfl⟩ : syracuseStep 16564459 = 24846689) B24846689
theorem B22085945 : Blo 2297435 22085945 := bstep (se 2 (by rfl) ⟨8282229, by rfl⟩ : syracuseStep 22085945 = 16564459) B16564459
theorem B14723963 : Blo 2297435 14723963 := bstep (se 1 (by rfl) ⟨11042972, by rfl⟩ : syracuseStep 14723963 = 22085945) B22085945
theorem B9815975 : Blo 2297435 9815975 := bstep (se 1 (by rfl) ⟨7361981, by rfl⟩ : syracuseStep 9815975 = 14723963) B14723963
theorem B6543983 : Blo 2297435 6543983 := bstep (se 1 (by rfl) ⟨4907987, by rfl⟩ : syracuseStep 6543983 = 9815975) B9815975
theorem B4362655 : Blo 2297435 4362655 := bstep (se 1 (by rfl) ⟨3271991, by rfl⟩ : syracuseStep 4362655 = 6543983) B6543983
theorem B5816873 : Blo 2297435 5816873 := bstep (se 2 (by rfl) ⟨2181327, by rfl⟩ : syracuseStep 5816873 = 4362655) B4362655
theorem B3877915 : Blo 2297435 3877915 := bstep (se 1 (by rfl) ⟨2908436, by rfl⟩ : syracuseStep 3877915 = 5816873) B5816873
theorem B5170553 : Blo 2297435 5170553 := bstep (se 2 (by rfl) ⟨1938957, by rfl⟩ : syracuseStep 5170553 = 3877915) B3877915
theorem B3447035 : Blo 2297435 3447035 := bstep (se 1 (by rfl) ⟨2585276, by rfl⟩ : syracuseStep 3447035 = 5170553) B5170553
theorem B2298023 : Blo 2297435 2298023 := bstep (se 1 (by rfl) ⟨1723517, by rfl⟩ : syracuseStep 2298023 = 3447035) B3447035
theorem B2585281 : Blo 2297435 2585281 := bbase (se 2 (by rfl) ⟨969480, by rfl⟩ : syracuseStep 2585281 = 1938961) (by norm_num)
theorem B3447041 : Blo 2297435 3447041 := bstep (se 2 (by rfl) ⟨1292640, by rfl⟩ : syracuseStep 3447041 = 2585281) B2585281
theorem B2298027 : Blo 2297435 2298027 := bstep (se 1 (by rfl) ⟨1723520, by rfl⟩ : syracuseStep 2298027 = 3447041) B3447041
theorem B5816893 : Blo 2297435 5816893 := bbase (se 3 (by rfl) ⟨1090667, by rfl⟩ : syracuseStep 5816893 = 2181335) (by norm_num)
theorem B7755857 : Blo 2297435 7755857 := bstep (se 2 (by rfl) ⟨2908446, by rfl⟩ : syracuseStep 7755857 = 5816893) B5816893
theorem B5170571 : Blo 2297435 5170571 := bstep (se 1 (by rfl) ⟨3877928, by rfl⟩ : syracuseStep 5170571 = 7755857) B7755857
theorem B3447047 : Blo 2297435 3447047 := bstep (se 1 (by rfl) ⟨2585285, by rfl⟩ : syracuseStep 3447047 = 5170571) B5170571
theorem B2298031 : Blo 2297435 2298031 := bstep (se 1 (by rfl) ⟨1723523, by rfl⟩ : syracuseStep 2298031 = 3447047) B3447047
theorem B3447053 : Blo 2297435 3447053 := bbase (se 3 (by rfl) ⟨646322, by rfl⟩ : syracuseStep 3447053 = 1292645) (by norm_num)
theorem B2298035 : Blo 2297435 2298035 := bstep (se 1 (by rfl) ⟨1723526, by rfl⟩ : syracuseStep 2298035 = 3447053) B3447053
theorem B5170589 : Blo 2297435 5170589 := bbase (se 3 (by rfl) ⟨969485, by rfl⟩ : syracuseStep 5170589 = 1938971) (by norm_num)
theorem B3447059 : Blo 2297435 3447059 := bstep (se 1 (by rfl) ⟨2585294, by rfl⟩ : syracuseStep 3447059 = 5170589) B5170589
theorem B2298039 : Blo 2297435 2298039 := bstep (se 1 (by rfl) ⟨1723529, by rfl⟩ : syracuseStep 2298039 = 3447059) B3447059
theorem B3877949 : Blo 2297435 3877949 := bbase (se 3 (by rfl) ⟨727115, by rfl⟩ : syracuseStep 3877949 = 1454231) (by norm_num)
theorem B2585299 : Blo 2297435 2585299 := bstep (se 1 (by rfl) ⟨1938974, by rfl⟩ : syracuseStep 2585299 = 3877949) B3877949
theorem B3447065 : Blo 2297435 3447065 := bstep (se 2 (by rfl) ⟨1292649, by rfl⟩ : syracuseStep 3447065 = 2585299) B2585299
theorem B2298043 : Blo 2297435 2298043 := bstep (se 1 (by rfl) ⟨1723532, by rfl⟩ : syracuseStep 2298043 = 3447065) B3447065
theorem B3681029 : Blo 2297435 3681029 := bbase (se 4 (by rfl) ⟨345096, by rfl⟩ : syracuseStep 3681029 = 690193) (by norm_num)
theorem B2454019 : Blo 2297435 2454019 := bstep (se 1 (by rfl) ⟨1840514, by rfl⟩ : syracuseStep 2454019 = 3681029) B3681029
theorem B13088101 : Blo 2297435 13088101 := bstep (se 4 (by rfl) ⟨1227009, by rfl⟩ : syracuseStep 13088101 = 2454019) B2454019
theorem B17450801 : Blo 2297435 17450801 := bstep (se 2 (by rfl) ⟨6544050, by rfl⟩ : syracuseStep 17450801 = 13088101) B13088101
theorem B11633867 : Blo 2297435 11633867 := bstep (se 1 (by rfl) ⟨8725400, by rfl⟩ : syracuseStep 11633867 = 17450801) B17450801
theorem B7755911 : Blo 2297435 7755911 := bstep (se 1 (by rfl) ⟨5816933, by rfl⟩ : syracuseStep 7755911 = 11633867) B11633867
theorem B5170607 : Blo 2297435 5170607 := bstep (se 1 (by rfl) ⟨3877955, by rfl⟩ : syracuseStep 5170607 = 7755911) B7755911
theorem B3447071 : Blo 2297435 3447071 := bstep (se 1 (by rfl) ⟨2585303, by rfl⟩ : syracuseStep 3447071 = 5170607) B5170607
theorem B2298047 : Blo 2297435 2298047 := bstep (se 1 (by rfl) ⟨1723535, by rfl⟩ : syracuseStep 2298047 = 3447071) B3447071
theorem B3447077 : Blo 2297435 3447077 := bbase (se 4 (by rfl) ⟨323163, by rfl⟩ : syracuseStep 3447077 = 646327) (by norm_num)
theorem B2298051 : Blo 2297435 2298051 := bstep (se 1 (by rfl) ⟨1723538, by rfl⟩ : syracuseStep 2298051 = 3447077) B3447077
theorem B2908477 : Blo 2297435 2908477 := bbase (se 3 (by rfl) ⟨545339, by rfl⟩ : syracuseStep 2908477 = 1090679) (by norm_num)
theorem B3877969 : Blo 2297435 3877969 := bstep (se 2 (by rfl) ⟨1454238, by rfl⟩ : syracuseStep 3877969 = 2908477) B2908477
theorem B5170625 : Blo 2297435 5170625 := bstep (se 2 (by rfl) ⟨1938984, by rfl⟩ : syracuseStep 5170625 = 3877969) B3877969
theorem B3447083 : Blo 2297435 3447083 := bstep (se 1 (by rfl) ⟨2585312, by rfl⟩ : syracuseStep 3447083 = 5170625) B5170625
theorem B2298055 : Blo 2297435 2298055 := bstep (se 1 (by rfl) ⟨1723541, by rfl⟩ : syracuseStep 2298055 = 3447083) B3447083
theorem B2585317 : Blo 2297435 2585317 := bbase (se 4 (by rfl) ⟨242373, by rfl⟩ : syracuseStep 2585317 = 484747) (by norm_num)
theorem B3447089 : Blo 2297435 3447089 := bstep (se 2 (by rfl) ⟨1292658, by rfl⟩ : syracuseStep 3447089 = 2585317) B2585317
theorem B2298059 : Blo 2297435 2298059 := bstep (se 1 (by rfl) ⟨1723544, by rfl⟩ : syracuseStep 2298059 = 3447089) B3447089
theorem B4786829 : Blo 2297435 4786829 := bbase (se 3 (by rfl) ⟨897530, by rfl⟩ : syracuseStep 4786829 = 1795061) (by norm_num)
theorem B204238037 : Blo 2297435 204238037 := bstep (se 7 (by rfl) ⟨2393414, by rfl⟩ : syracuseStep 204238037 = 4786829) B4786829
theorem B136158691 : Blo 2297435 136158691 := bstep (se 1 (by rfl) ⟨102119018, by rfl⟩ : syracuseStep 136158691 = 204238037) B204238037
theorem B181544921 : Blo 2297435 181544921 := bstep (se 2 (by rfl) ⟨68079345, by rfl⟩ : syracuseStep 181544921 = 136158691) B136158691
theorem B121029947 : Blo 2297435 121029947 := bstep (se 1 (by rfl) ⟨90772460, by rfl⟩ : syracuseStep 121029947 = 181544921) B181544921
theorem B80686631 : Blo 2297435 80686631 := bstep (se 1 (by rfl) ⟨60514973, by rfl⟩ : syracuseStep 80686631 = 121029947) B121029947
theorem B53791087 : Blo 2297435 53791087 := bstep (se 1 (by rfl) ⟨40343315, by rfl⟩ : syracuseStep 53791087 = 80686631) B80686631
theorem B71721449 : Blo 2297435 71721449 := bstep (se 2 (by rfl) ⟨26895543, by rfl⟩ : syracuseStep 71721449 = 53791087) B53791087
theorem B47814299 : Blo 2297435 47814299 := bstep (se 1 (by rfl) ⟨35860724, by rfl⟩ : syracuseStep 47814299 = 71721449) B71721449
theorem B31876199 : Blo 2297435 31876199 := bstep (se 1 (by rfl) ⟨23907149, by rfl⟩ : syracuseStep 31876199 = 47814299) B47814299
theorem B21250799 : Blo 2297435 21250799 := bstep (se 1 (by rfl) ⟨15938099, by rfl⟩ : syracuseStep 21250799 = 31876199) B31876199
theorem B14167199 : Blo 2297435 14167199 := bstep (se 1 (by rfl) ⟨10625399, by rfl⟩ : syracuseStep 14167199 = 21250799) B21250799
theorem B9444799 : Blo 2297435 9444799 := bstep (se 1 (by rfl) ⟨7083599, by rfl⟩ : syracuseStep 9444799 = 14167199) B14167199
theorem B12593065 : Blo 2297435 12593065 := bstep (se 2 (by rfl) ⟨4722399, by rfl⟩ : syracuseStep 12593065 = 9444799) B9444799
theorem B16790753 : Blo 2297435 16790753 := bstep (se 2 (by rfl) ⟨6296532, by rfl⟩ : syracuseStep 16790753 = 12593065) B12593065
theorem B44775341 : Blo 2297435 44775341 := bstep (se 3 (by rfl) ⟨8395376, by rfl⟩ : syracuseStep 44775341 = 16790753) B16790753
theorem B29850227 : Blo 2297435 29850227 := bstep (se 1 (by rfl) ⟨22387670, by rfl⟩ : syracuseStep 29850227 = 44775341) B44775341
theorem B19900151 : Blo 2297435 19900151 := bstep (se 1 (by rfl) ⟨14925113, by rfl⟩ : syracuseStep 19900151 = 29850227) B29850227
theorem B13266767 : Blo 2297435 13266767 := bstep (se 1 (by rfl) ⟨9950075, by rfl⟩ : syracuseStep 13266767 = 19900151) B19900151
theorem B8844511 : Blo 2297435 8844511 := bstep (se 1 (by rfl) ⟨6633383, by rfl⟩ : syracuseStep 8844511 = 13266767) B13266767
theorem B11792681 : Blo 2297435 11792681 := bstep (se 2 (by rfl) ⟨4422255, by rfl⟩ : syracuseStep 11792681 = 8844511) B8844511
theorem B7861787 : Blo 2297435 7861787 := bstep (se 1 (by rfl) ⟨5896340, by rfl⟩ : syracuseStep 7861787 = 11792681) B11792681
theorem B5241191 : Blo 2297435 5241191 := bstep (se 1 (by rfl) ⟨3930893, by rfl⟩ : syracuseStep 5241191 = 7861787) B7861787
theorem B13976509 : Blo 2297435 13976509 := bstep (se 3 (by rfl) ⟨2620595, by rfl⟩ : syracuseStep 13976509 = 5241191) B5241191
theorem B18635345 : Blo 2297435 18635345 := bstep (se 2 (by rfl) ⟨6988254, by rfl⟩ : syracuseStep 18635345 = 13976509) B13976509
theorem B12423563 : Blo 2297435 12423563 := bstep (se 1 (by rfl) ⟨9317672, by rfl⟩ : syracuseStep 12423563 = 18635345) B18635345
theorem B8282375 : Blo 2297435 8282375 := bstep (se 1 (by rfl) ⟨6211781, by rfl⟩ : syracuseStep 8282375 = 12423563) B12423563
theorem B5521583 : Blo 2297435 5521583 := bstep (se 1 (by rfl) ⟨4141187, by rfl⟩ : syracuseStep 5521583 = 8282375) B8282375
theorem B3681055 : Blo 2297435 3681055 := bstep (se 1 (by rfl) ⟨2760791, by rfl⟩ : syracuseStep 3681055 = 5521583) B5521583
theorem B4908073 : Blo 2297435 4908073 := bstep (se 2 (by rfl) ⟨1840527, by rfl⟩ : syracuseStep 4908073 = 3681055) B3681055
theorem B6544097 : Blo 2297435 6544097 := bstep (se 2 (by rfl) ⟨2454036, by rfl⟩ : syracuseStep 6544097 = 4908073) B4908073
theorem B4362731 : Blo 2297435 4362731 := bstep (se 1 (by rfl) ⟨3272048, by rfl⟩ : syracuseStep 4362731 = 6544097) B6544097
theorem B2908487 : Blo 2297435 2908487 := bstep (se 1 (by rfl) ⟨2181365, by rfl⟩ : syracuseStep 2908487 = 4362731) B4362731
theorem B7755965 : Blo 2297435 7755965 := bstep (se 3 (by rfl) ⟨1454243, by rfl⟩ : syracuseStep 7755965 = 2908487) B2908487
theorem B5170643 : Blo 2297435 5170643 := bstep (se 1 (by rfl) ⟨3877982, by rfl⟩ : syracuseStep 5170643 = 7755965) B7755965
theorem B3447095 : Blo 2297435 3447095 := bstep (se 1 (by rfl) ⟨2585321, by rfl⟩ : syracuseStep 3447095 = 5170643) B5170643
theorem B2298063 : Blo 2297435 2298063 := bstep (se 1 (by rfl) ⟨1723547, by rfl⟩ : syracuseStep 2298063 = 3447095) B3447095
theorem B3447101 : Blo 2297435 3447101 := bbase (se 3 (by rfl) ⟨646331, by rfl⟩ : syracuseStep 3447101 = 1292663) (by norm_num)
theorem B2298067 : Blo 2297435 2298067 := bstep (se 1 (by rfl) ⟨1723550, by rfl⟩ : syracuseStep 2298067 = 3447101) B3447101
theorem B5170661 : Blo 2297435 5170661 := bbase (se 4 (by rfl) ⟨484749, by rfl⟩ : syracuseStep 5170661 = 969499) (by norm_num)
theorem B3447107 : Blo 2297435 3447107 := bstep (se 1 (by rfl) ⟨2585330, by rfl⟩ : syracuseStep 3447107 = 5170661) B5170661
theorem B2298071 : Blo 2297435 2298071 := bstep (se 1 (by rfl) ⟨1723553, by rfl⟩ : syracuseStep 2298071 = 3447107) B3447107
theorem B5817005 : Blo 2297435 5817005 := bbase (se 3 (by rfl) ⟨1090688, by rfl⟩ : syracuseStep 5817005 = 2181377) (by norm_num)
theorem B3878003 : Blo 2297435 3878003 := bstep (se 1 (by rfl) ⟨2908502, by rfl⟩ : syracuseStep 3878003 = 5817005) B5817005
theorem B2585335 : Blo 2297435 2585335 := bstep (se 1 (by rfl) ⟨1939001, by rfl⟩ : syracuseStep 2585335 = 3878003) B3878003
theorem B3447113 : Blo 2297435 3447113 := bstep (se 2 (by rfl) ⟨1292667, by rfl⟩ : syracuseStep 3447113 = 2585335) B2585335
theorem B2298075 : Blo 2297435 2298075 := bstep (se 1 (by rfl) ⟨1723556, by rfl⟩ : syracuseStep 2298075 = 3447113) B3447113
theorem B5521621 : Blo 2297435 5521621 := bbase (se 7 (by rfl) ⟨64706, by rfl⟩ : syracuseStep 5521621 = 129413) (by norm_num)
theorem B7362161 : Blo 2297435 7362161 := bstep (se 2 (by rfl) ⟨2760810, by rfl⟩ : syracuseStep 7362161 = 5521621) B5521621
theorem B4908107 : Blo 2297435 4908107 := bstep (se 1 (by rfl) ⟨3681080, by rfl⟩ : syracuseStep 4908107 = 7362161) B7362161
theorem B3272071 : Blo 2297435 3272071 := bstep (se 1 (by rfl) ⟨2454053, by rfl⟩ : syracuseStep 3272071 = 4908107) B4908107
theorem B4362761 : Blo 2297435 4362761 := bstep (se 2 (by rfl) ⟨1636035, by rfl⟩ : syracuseStep 4362761 = 3272071) B3272071
theorem B11634029 : Blo 2297435 11634029 := bstep (se 3 (by rfl) ⟨2181380, by rfl⟩ : syracuseStep 11634029 = 4362761) B4362761
theorem B7756019 : Blo 2297435 7756019 := bstep (se 1 (by rfl) ⟨5817014, by rfl⟩ : syracuseStep 7756019 = 11634029) B11634029
theorem B5170679 : Blo 2297435 5170679 := bstep (se 1 (by rfl) ⟨3878009, by rfl⟩ : syracuseStep 5170679 = 7756019) B7756019
theorem B3447119 : Blo 2297435 3447119 := bstep (se 1 (by rfl) ⟨2585339, by rfl⟩ : syracuseStep 3447119 = 5170679) B5170679
theorem B2298079 : Blo 2297435 2298079 := bstep (se 1 (by rfl) ⟨1723559, by rfl⟩ : syracuseStep 2298079 = 3447119) B3447119
theorem B3447125 : Blo 2297435 3447125 := bbase (se 10 (by rfl) ⟨5049, by rfl⟩ : syracuseStep 3447125 = 10099) (by norm_num)
theorem B2298083 : Blo 2297435 2298083 := bstep (se 1 (by rfl) ⟨1723562, by rfl⟩ : syracuseStep 2298083 = 3447125) B3447125
theorem B6544165 : Blo 2297435 6544165 := bbase (se 4 (by rfl) ⟨613515, by rfl⟩ : syracuseStep 6544165 = 1227031) (by norm_num)
theorem B8725553 : Blo 2297435 8725553 := bstep (se 2 (by rfl) ⟨3272082, by rfl⟩ : syracuseStep 8725553 = 6544165) B6544165
theorem B5817035 : Blo 2297435 5817035 := bstep (se 1 (by rfl) ⟨4362776, by rfl⟩ : syracuseStep 5817035 = 8725553) B8725553
theorem B3878023 : Blo 2297435 3878023 := bstep (se 1 (by rfl) ⟨2908517, by rfl⟩ : syracuseStep 3878023 = 5817035) B5817035
theorem B5170697 : Blo 2297435 5170697 := bstep (se 2 (by rfl) ⟨1939011, by rfl⟩ : syracuseStep 5170697 = 3878023) B3878023
theorem B3447131 : Blo 2297435 3447131 := bstep (se 1 (by rfl) ⟨2585348, by rfl⟩ : syracuseStep 3447131 = 5170697) B5170697
theorem B2298087 : Blo 2297435 2298087 := bstep (se 1 (by rfl) ⟨1723565, by rfl⟩ : syracuseStep 2298087 = 3447131) B3447131
theorem B2585353 : Blo 2297435 2585353 := bbase (se 2 (by rfl) ⟨969507, by rfl⟩ : syracuseStep 2585353 = 1939015) (by norm_num)
theorem B3447137 : Blo 2297435 3447137 := bstep (se 2 (by rfl) ⟨1292676, by rfl⟩ : syracuseStep 3447137 = 2585353) B2585353
theorem B2298091 : Blo 2297435 2298091 := bstep (se 1 (by rfl) ⟨1723568, by rfl⟩ : syracuseStep 2298091 = 3447137) B3447137
theorem B11043317 : Blo 2297435 11043317 := bbase (se 5 (by rfl) ⟨517655, by rfl⟩ : syracuseStep 11043317 = 1035311) (by norm_num)
theorem B29448845 : Blo 2297435 29448845 := bstep (se 3 (by rfl) ⟨5521658, by rfl⟩ : syracuseStep 29448845 = 11043317) B11043317
theorem B19632563 : Blo 2297435 19632563 := bstep (se 1 (by rfl) ⟨14724422, by rfl⟩ : syracuseStep 19632563 = 29448845) B29448845
theorem B13088375 : Blo 2297435 13088375 := bstep (se 1 (by rfl) ⟨9816281, by rfl⟩ : syracuseStep 13088375 = 19632563) B19632563
theorem B8725583 : Blo 2297435 8725583 := bstep (se 1 (by rfl) ⟨6544187, by rfl⟩ : syracuseStep 8725583 = 13088375) B13088375
theorem B5817055 : Blo 2297435 5817055 := bstep (se 1 (by rfl) ⟨4362791, by rfl⟩ : syracuseStep 5817055 = 8725583) B8725583
theorem B7756073 : Blo 2297435 7756073 := bstep (se 2 (by rfl) ⟨2908527, by rfl⟩ : syracuseStep 7756073 = 5817055) B5817055
theorem B5170715 : Blo 2297435 5170715 := bstep (se 1 (by rfl) ⟨3878036, by rfl⟩ : syracuseStep 5170715 = 7756073) B7756073
theorem B3447143 : Blo 2297435 3447143 := bstep (se 1 (by rfl) ⟨2585357, by rfl⟩ : syracuseStep 3447143 = 5170715) B5170715
theorem B2298095 : Blo 2297435 2298095 := bstep (se 1 (by rfl) ⟨1723571, by rfl⟩ : syracuseStep 2298095 = 3447143) B3447143
theorem B3447149 : Blo 2297435 3447149 := bbase (se 3 (by rfl) ⟨646340, by rfl⟩ : syracuseStep 3447149 = 1292681) (by norm_num)
theorem B2298099 : Blo 2297435 2298099 := bstep (se 1 (by rfl) ⟨1723574, by rfl⟩ : syracuseStep 2298099 = 3447149) B3447149
theorem B5170733 : Blo 2297435 5170733 := bbase (se 3 (by rfl) ⟨969512, by rfl⟩ : syracuseStep 5170733 = 1939025) (by norm_num)
theorem B3447155 : Blo 2297435 3447155 := bstep (se 1 (by rfl) ⟨2585366, by rfl⟩ : syracuseStep 3447155 = 5170733) B5170733
theorem B2298103 : Blo 2297435 2298103 := bstep (se 1 (by rfl) ⟨1723577, by rfl⟩ : syracuseStep 2298103 = 3447155) B3447155
theorem B33130133 : Blo 2297435 33130133 := bbase (se 6 (by rfl) ⟨776487, by rfl⟩ : syracuseStep 33130133 = 1552975) (by norm_num)
theorem B22086755 : Blo 2297435 22086755 := bstep (se 1 (by rfl) ⟨16565066, by rfl⟩ : syracuseStep 22086755 = 33130133) B33130133
theorem B14724503 : Blo 2297435 14724503 := bstep (se 1 (by rfl) ⟨11043377, by rfl⟩ : syracuseStep 14724503 = 22086755) B22086755
theorem B9816335 : Blo 2297435 9816335 := bstep (se 1 (by rfl) ⟨7362251, by rfl⟩ : syracuseStep 9816335 = 14724503) B14724503
theorem B6544223 : Blo 2297435 6544223 := bstep (se 1 (by rfl) ⟨4908167, by rfl⟩ : syracuseStep 6544223 = 9816335) B9816335
theorem B4362815 : Blo 2297435 4362815 := bstep (se 1 (by rfl) ⟨3272111, by rfl⟩ : syracuseStep 4362815 = 6544223) B6544223
theorem B2908543 : Blo 2297435 2908543 := bstep (se 1 (by rfl) ⟨2181407, by rfl⟩ : syracuseStep 2908543 = 4362815) B4362815
theorem B3878057 : Blo 2297435 3878057 := bstep (se 2 (by rfl) ⟨1454271, by rfl⟩ : syracuseStep 3878057 = 2908543) B2908543
theorem B2585371 : Blo 2297435 2585371 := bstep (se 1 (by rfl) ⟨1939028, by rfl⟩ : syracuseStep 2585371 = 3878057) B3878057
theorem B3447161 : Blo 2297435 3447161 := bstep (se 2 (by rfl) ⟨1292685, by rfl⟩ : syracuseStep 3447161 = 2585371) B2585371
theorem B2298107 : Blo 2297435 2298107 := bstep (se 1 (by rfl) ⟨1723580, by rfl⟩ : syracuseStep 2298107 = 3447161) B3447161
theorem B4658933 : Blo 2297435 4658933 := bbase (se 5 (by rfl) ⟨218387, by rfl⟩ : syracuseStep 4658933 = 436775) (by norm_num)
theorem B3105955 : Blo 2297435 3105955 := bstep (se 1 (by rfl) ⟨2329466, by rfl⟩ : syracuseStep 3105955 = 4658933) B4658933
theorem B4141273 : Blo 2297435 4141273 := bstep (se 2 (by rfl) ⟨1552977, by rfl⟩ : syracuseStep 4141273 = 3105955) B3105955
theorem B5521697 : Blo 2297435 5521697 := bstep (se 2 (by rfl) ⟨2070636, by rfl⟩ : syracuseStep 5521697 = 4141273) B4141273
theorem B3681131 : Blo 2297435 3681131 := bstep (se 1 (by rfl) ⟨2760848, by rfl⟩ : syracuseStep 3681131 = 5521697) B5521697
theorem B39265397 : Blo 2297435 39265397 := bstep (se 5 (by rfl) ⟨1840565, by rfl⟩ : syracuseStep 39265397 = 3681131) B3681131
theorem B26176931 : Blo 2297435 26176931 := bstep (se 1 (by rfl) ⟨19632698, by rfl⟩ : syracuseStep 26176931 = 39265397) B39265397
theorem B17451287 : Blo 2297435 17451287 := bstep (se 1 (by rfl) ⟨13088465, by rfl⟩ : syracuseStep 17451287 = 26176931) B26176931
theorem B11634191 : Blo 2297435 11634191 := bstep (se 1 (by rfl) ⟨8725643, by rfl⟩ : syracuseStep 11634191 = 17451287) B17451287
theorem B7756127 : Blo 2297435 7756127 := bstep (se 1 (by rfl) ⟨5817095, by rfl⟩ : syracuseStep 7756127 = 11634191) B11634191
theorem B5170751 : Blo 2297435 5170751 := bstep (se 1 (by rfl) ⟨3878063, by rfl⟩ : syracuseStep 5170751 = 7756127) B7756127
theorem B3447167 : Blo 2297435 3447167 := bstep (se 1 (by rfl) ⟨2585375, by rfl⟩ : syracuseStep 3447167 = 5170751) B5170751
theorem B2298111 : Blo 2297435 2298111 := bstep (se 1 (by rfl) ⟨1723583, by rfl⟩ : syracuseStep 2298111 = 3447167) B3447167
theorem B3447173 : Blo 2297435 3447173 := bbase (se 4 (by rfl) ⟨323172, by rfl⟩ : syracuseStep 3447173 = 646345) (by norm_num)
theorem B2298115 : Blo 2297435 2298115 := bstep (se 1 (by rfl) ⟨1723586, by rfl⟩ : syracuseStep 2298115 = 3447173) B3447173
theorem B3878077 : Blo 2297435 3878077 := bbase (se 3 (by rfl) ⟨727139, by rfl⟩ : syracuseStep 3878077 = 1454279) (by norm_num)
theorem B5170769 : Blo 2297435 5170769 := bstep (se 2 (by rfl) ⟨1939038, by rfl⟩ : syracuseStep 5170769 = 3878077) B3878077
theorem B3447179 : Blo 2297435 3447179 := bstep (se 1 (by rfl) ⟨2585384, by rfl⟩ : syracuseStep 3447179 = 5170769) B5170769
theorem B2298119 : Blo 2297435 2298119 := bstep (se 1 (by rfl) ⟨1723589, by rfl⟩ : syracuseStep 2298119 = 3447179) B3447179
theorem B2585389 : Blo 2297435 2585389 := bbase (se 3 (by rfl) ⟨484760, by rfl⟩ : syracuseStep 2585389 = 969521) (by norm_num)
theorem B3447185 : Blo 2297435 3447185 := bstep (se 2 (by rfl) ⟨1292694, by rfl⟩ : syracuseStep 3447185 = 2585389) B2585389
theorem B2298123 : Blo 2297435 2298123 := bstep (se 1 (by rfl) ⟨1723592, by rfl⟩ : syracuseStep 2298123 = 3447185) B3447185
theorem B7756181 : Blo 2297435 7756181 := bbase (se 6 (by rfl) ⟨181785, by rfl⟩ : syracuseStep 7756181 = 363571) (by norm_num)
theorem B5170787 : Blo 2297435 5170787 := bstep (se 1 (by rfl) ⟨3878090, by rfl⟩ : syracuseStep 5170787 = 7756181) B7756181
theorem B3447191 : Blo 2297435 3447191 := bstep (se 1 (by rfl) ⟨2585393, by rfl⟩ : syracuseStep 3447191 = 5170787) B5170787
theorem B2298127 : Blo 2297435 2298127 := bstep (se 1 (by rfl) ⟨1723595, by rfl⟩ : syracuseStep 2298127 = 3447191) B3447191
theorem B3447197 : Blo 2297435 3447197 := bbase (se 3 (by rfl) ⟨646349, by rfl⟩ : syracuseStep 3447197 = 1292699) (by norm_num)
theorem B2298131 : Blo 2297435 2298131 := bstep (se 1 (by rfl) ⟨1723598, by rfl⟩ : syracuseStep 2298131 = 3447197) B3447197
theorem B5170805 : Blo 2297435 5170805 := bbase (se 5 (by rfl) ⟨242381, by rfl⟩ : syracuseStep 5170805 = 484763) (by norm_num)
theorem B3447203 : Blo 2297435 3447203 := bstep (se 1 (by rfl) ⟨2585402, by rfl⟩ : syracuseStep 3447203 = 5170805) B5170805
theorem B2298135 : Blo 2297435 2298135 := bstep (se 1 (by rfl) ⟨1723601, by rfl⟩ : syracuseStep 2298135 = 3447203) B3447203
theorem B5521765 : Blo 2297435 5521765 := bbase (se 4 (by rfl) ⟨517665, by rfl⟩ : syracuseStep 5521765 = 1035331) (by norm_num)
theorem B7362353 : Blo 2297435 7362353 := bstep (se 2 (by rfl) ⟨2760882, by rfl⟩ : syracuseStep 7362353 = 5521765) B5521765
theorem B19632941 : Blo 2297435 19632941 := bstep (se 3 (by rfl) ⟨3681176, by rfl⟩ : syracuseStep 19632941 = 7362353) B7362353
theorem B13088627 : Blo 2297435 13088627 := bstep (se 1 (by rfl) ⟨9816470, by rfl⟩ : syracuseStep 13088627 = 19632941) B19632941
theorem B8725751 : Blo 2297435 8725751 := bstep (se 1 (by rfl) ⟨6544313, by rfl⟩ : syracuseStep 8725751 = 13088627) B13088627
theorem B5817167 : Blo 2297435 5817167 := bstep (se 1 (by rfl) ⟨4362875, by rfl⟩ : syracuseStep 5817167 = 8725751) B8725751
theorem B3878111 : Blo 2297435 3878111 := bstep (se 1 (by rfl) ⟨2908583, by rfl⟩ : syracuseStep 3878111 = 5817167) B5817167
theorem B2585407 : Blo 2297435 2585407 := bstep (se 1 (by rfl) ⟨1939055, by rfl⟩ : syracuseStep 2585407 = 3878111) B3878111
theorem B3447209 : Blo 2297435 3447209 := bstep (se 2 (by rfl) ⟨1292703, by rfl⟩ : syracuseStep 3447209 = 2585407) B2585407
theorem B2298139 : Blo 2297435 2298139 := bstep (se 1 (by rfl) ⟨1723604, by rfl⟩ : syracuseStep 2298139 = 3447209) B3447209
theorem B8725765 : Blo 2297435 8725765 := bbase (se 4 (by rfl) ⟨818040, by rfl⟩ : syracuseStep 8725765 = 1636081) (by norm_num)
theorem B11634353 : Blo 2297435 11634353 := bstep (se 2 (by rfl) ⟨4362882, by rfl⟩ : syracuseStep 11634353 = 8725765) B8725765
theorem B7756235 : Blo 2297435 7756235 := bstep (se 1 (by rfl) ⟨5817176, by rfl⟩ : syracuseStep 7756235 = 11634353) B11634353
theorem B5170823 : Blo 2297435 5170823 := bstep (se 1 (by rfl) ⟨3878117, by rfl⟩ : syracuseStep 5170823 = 7756235) B7756235
theorem B3447215 : Blo 2297435 3447215 := bstep (se 1 (by rfl) ⟨2585411, by rfl⟩ : syracuseStep 3447215 = 5170823) B5170823
theorem B2298143 : Blo 2297435 2298143 := bstep (se 1 (by rfl) ⟨1723607, by rfl⟩ : syracuseStep 2298143 = 3447215) B3447215
theorem B3447221 : Blo 2297435 3447221 := bbase (se 5 (by rfl) ⟨161588, by rfl⟩ : syracuseStep 3447221 = 323177) (by norm_num)
theorem B2298147 : Blo 2297435 2298147 := bstep (se 1 (by rfl) ⟨1723610, by rfl⟩ : syracuseStep 2298147 = 3447221) B3447221
theorem B5817197 : Blo 2297435 5817197 := bbase (se 3 (by rfl) ⟨1090724, by rfl⟩ : syracuseStep 5817197 = 2181449) (by norm_num)
theorem B3878131 : Blo 2297435 3878131 := bstep (se 1 (by rfl) ⟨2908598, by rfl⟩ : syracuseStep 3878131 = 5817197) B5817197
theorem B5170841 : Blo 2297435 5170841 := bstep (se 2 (by rfl) ⟨1939065, by rfl⟩ : syracuseStep 5170841 = 3878131) B3878131
theorem B3447227 : Blo 2297435 3447227 := bstep (se 1 (by rfl) ⟨2585420, by rfl⟩ : syracuseStep 3447227 = 5170841) B5170841
theorem B2298151 : Blo 2297435 2298151 := bstep (se 1 (by rfl) ⟨1723613, by rfl⟩ : syracuseStep 2298151 = 3447227) B3447227
theorem B2585425 : Blo 2297435 2585425 := bbase (se 2 (by rfl) ⟨969534, by rfl⟩ : syracuseStep 2585425 = 1939069) (by norm_num)
theorem B3447233 : Blo 2297435 3447233 := bstep (se 2 (by rfl) ⟨1292712, by rfl⟩ : syracuseStep 3447233 = 2585425) B2585425
theorem B2298155 : Blo 2297435 2298155 := bstep (se 1 (by rfl) ⟨1723616, by rfl⟩ : syracuseStep 2298155 = 3447233) B3447233
theorem B3106021 : Blo 2297435 3106021 := bbase (se 4 (by rfl) ⟨291189, by rfl⟩ : syracuseStep 3106021 = 582379) (by norm_num)
theorem B4141361 : Blo 2297435 4141361 := bstep (se 2 (by rfl) ⟨1553010, by rfl⟩ : syracuseStep 4141361 = 3106021) B3106021
theorem B2760907 : Blo 2297435 2760907 := bstep (se 1 (by rfl) ⟨2070680, by rfl⟩ : syracuseStep 2760907 = 4141361) B4141361
theorem B3681209 : Blo 2297435 3681209 := bstep (se 2 (by rfl) ⟨1380453, by rfl⟩ : syracuseStep 3681209 = 2760907) B2760907
theorem B2454139 : Blo 2297435 2454139 := bstep (se 1 (by rfl) ⟨1840604, by rfl⟩ : syracuseStep 2454139 = 3681209) B3681209
theorem B3272185 : Blo 2297435 3272185 := bstep (se 2 (by rfl) ⟨1227069, by rfl⟩ : syracuseStep 3272185 = 2454139) B2454139
theorem B4362913 : Blo 2297435 4362913 := bstep (se 2 (by rfl) ⟨1636092, by rfl⟩ : syracuseStep 4362913 = 3272185) B3272185
theorem B5817217 : Blo 2297435 5817217 := bstep (se 2 (by rfl) ⟨2181456, by rfl⟩ : syracuseStep 5817217 = 4362913) B4362913
theorem B7756289 : Blo 2297435 7756289 := bstep (se 2 (by rfl) ⟨2908608, by rfl⟩ : syracuseStep 7756289 = 5817217) B5817217
theorem B5170859 : Blo 2297435 5170859 := bstep (se 1 (by rfl) ⟨3878144, by rfl⟩ : syracuseStep 5170859 = 7756289) B7756289
theorem B3447239 : Blo 2297435 3447239 := bstep (se 1 (by rfl) ⟨2585429, by rfl⟩ : syracuseStep 3447239 = 5170859) B5170859
theorem B2298159 : Blo 2297435 2298159 := bstep (se 1 (by rfl) ⟨1723619, by rfl⟩ : syracuseStep 2298159 = 3447239) B3447239
theorem B3447245 : Blo 2297435 3447245 := bbase (se 3 (by rfl) ⟨646358, by rfl⟩ : syracuseStep 3447245 = 1292717) (by norm_num)
theorem B2298163 : Blo 2297435 2298163 := bstep (se 1 (by rfl) ⟨1723622, by rfl⟩ : syracuseStep 2298163 = 3447245) B3447245
theorem B5170877 : Blo 2297435 5170877 := bbase (se 3 (by rfl) ⟨969539, by rfl⟩ : syracuseStep 5170877 = 1939079) (by norm_num)
theorem B3447251 : Blo 2297435 3447251 := bstep (se 1 (by rfl) ⟨2585438, by rfl⟩ : syracuseStep 3447251 = 5170877) B5170877
theorem B2298167 : Blo 2297435 2298167 := bstep (se 1 (by rfl) ⟨1723625, by rfl⟩ : syracuseStep 2298167 = 3447251) B3447251
theorem B3878165 : Blo 2297435 3878165 := bbase (se 6 (by rfl) ⟨90894, by rfl⟩ : syracuseStep 3878165 = 181789) (by norm_num)
theorem B2585443 : Blo 2297435 2585443 := bstep (se 1 (by rfl) ⟨1939082, by rfl⟩ : syracuseStep 2585443 = 3878165) B3878165
theorem B3447257 : Blo 2297435 3447257 := bstep (se 2 (by rfl) ⟨1292721, by rfl⟩ : syracuseStep 3447257 = 2585443) B2585443
theorem B2298171 : Blo 2297435 2298171 := bstep (se 1 (by rfl) ⟨1723628, by rfl⟩ : syracuseStep 2298171 = 3447257) B3447257
theorem B17689877 : Blo 2297435 17689877 := bbase (se 6 (by rfl) ⟨414606, by rfl⟩ : syracuseStep 17689877 = 829213) (by norm_num)
theorem B11793251 : Blo 2297435 11793251 := bstep (se 1 (by rfl) ⟨8844938, by rfl⟩ : syracuseStep 11793251 = 17689877) B17689877
theorem B7862167 : Blo 2297435 7862167 := bstep (se 1 (by rfl) ⟨5896625, by rfl⟩ : syracuseStep 7862167 = 11793251) B11793251
theorem B41931557 : Blo 2297435 41931557 := bstep (se 4 (by rfl) ⟨3931083, by rfl⟩ : syracuseStep 41931557 = 7862167) B7862167
theorem B27954371 : Blo 2297435 27954371 := bstep (se 1 (by rfl) ⟨20965778, by rfl⟩ : syracuseStep 27954371 = 41931557) B41931557
theorem B18636247 : Blo 2297435 18636247 := bstep (se 1 (by rfl) ⟨13977185, by rfl⟩ : syracuseStep 18636247 = 27954371) B27954371
theorem B24848329 : Blo 2297435 24848329 := bstep (se 2 (by rfl) ⟨9318123, by rfl⟩ : syracuseStep 24848329 = 18636247) B18636247
theorem B33131105 : Blo 2297435 33131105 := bstep (se 2 (by rfl) ⟨12424164, by rfl⟩ : syracuseStep 33131105 = 24848329) B24848329
theorem B22087403 : Blo 2297435 22087403 := bstep (se 1 (by rfl) ⟨16565552, by rfl⟩ : syracuseStep 22087403 = 33131105) B33131105
theorem B14724935 : Blo 2297435 14724935 := bstep (se 1 (by rfl) ⟨11043701, by rfl⟩ : syracuseStep 14724935 = 22087403) B22087403
theorem B9816623 : Blo 2297435 9816623 := bstep (se 1 (by rfl) ⟨7362467, by rfl⟩ : syracuseStep 9816623 = 14724935) B14724935
theorem B6544415 : Blo 2297435 6544415 := bstep (se 1 (by rfl) ⟨4908311, by rfl⟩ : syracuseStep 6544415 = 9816623) B9816623
theorem B17451773 : Blo 2297435 17451773 := bstep (se 3 (by rfl) ⟨3272207, by rfl⟩ : syracuseStep 17451773 = 6544415) B6544415
theorem B11634515 : Blo 2297435 11634515 := bstep (se 1 (by rfl) ⟨8725886, by rfl⟩ : syracuseStep 11634515 = 17451773) B17451773
theorem B7756343 : Blo 2297435 7756343 := bstep (se 1 (by rfl) ⟨5817257, by rfl⟩ : syracuseStep 7756343 = 11634515) B11634515
theorem B5170895 : Blo 2297435 5170895 := bstep (se 1 (by rfl) ⟨3878171, by rfl⟩ : syracuseStep 5170895 = 7756343) B7756343
theorem B3447263 : Blo 2297435 3447263 := bstep (se 1 (by rfl) ⟨2585447, by rfl⟩ : syracuseStep 3447263 = 5170895) B5170895
theorem B2298175 : Blo 2297435 2298175 := bstep (se 1 (by rfl) ⟨1723631, by rfl⟩ : syracuseStep 2298175 = 3447263) B3447263
theorem B3447269 : Blo 2297435 3447269 := bbase (se 4 (by rfl) ⟨323181, by rfl⟩ : syracuseStep 3447269 = 646363) (by norm_num)
theorem B2298179 : Blo 2297435 2298179 := bstep (se 1 (by rfl) ⟨1723634, by rfl⟩ : syracuseStep 2298179 = 3447269) B3447269
theorem B7862197 : Blo 2297435 7862197 := bbase (se 5 (by rfl) ⟨368540, by rfl⟩ : syracuseStep 7862197 = 737081) (by norm_num)
theorem B10482929 : Blo 2297435 10482929 := bstep (se 2 (by rfl) ⟨3931098, by rfl⟩ : syracuseStep 10482929 = 7862197) B7862197
theorem B6988619 : Blo 2297435 6988619 := bstep (se 1 (by rfl) ⟨5241464, by rfl⟩ : syracuseStep 6988619 = 10482929) B10482929
theorem B18636317 : Blo 2297435 18636317 := bstep (se 3 (by rfl) ⟨3494309, by rfl⟩ : syracuseStep 18636317 = 6988619) B6988619
theorem B12424211 : Blo 2297435 12424211 := bstep (se 1 (by rfl) ⟨9318158, by rfl⟩ : syracuseStep 12424211 = 18636317) B18636317
theorem B8282807 : Blo 2297435 8282807 := bstep (se 1 (by rfl) ⟨6212105, by rfl⟩ : syracuseStep 8282807 = 12424211) B12424211
theorem B5521871 : Blo 2297435 5521871 := bstep (se 1 (by rfl) ⟨4141403, by rfl⟩ : syracuseStep 5521871 = 8282807) B8282807
theorem B14724989 : Blo 2297435 14724989 := bstep (se 3 (by rfl) ⟨2760935, by rfl⟩ : syracuseStep 14724989 = 5521871) B5521871
theorem B9816659 : Blo 2297435 9816659 := bstep (se 1 (by rfl) ⟨7362494, by rfl⟩ : syracuseStep 9816659 = 14724989) B14724989
theorem B6544439 : Blo 2297435 6544439 := bstep (se 1 (by rfl) ⟨4908329, by rfl⟩ : syracuseStep 6544439 = 9816659) B9816659
theorem B4362959 : Blo 2297435 4362959 := bstep (se 1 (by rfl) ⟨3272219, by rfl⟩ : syracuseStep 4362959 = 6544439) B6544439
theorem B2908639 : Blo 2297435 2908639 := bstep (se 1 (by rfl) ⟨2181479, by rfl⟩ : syracuseStep 2908639 = 4362959) B4362959
theorem B3878185 : Blo 2297435 3878185 := bstep (se 2 (by rfl) ⟨1454319, by rfl⟩ : syracuseStep 3878185 = 2908639) B2908639
theorem B5170913 : Blo 2297435 5170913 := bstep (se 2 (by rfl) ⟨1939092, by rfl⟩ : syracuseStep 5170913 = 3878185) B3878185
theorem B3447275 : Blo 2297435 3447275 := bstep (se 1 (by rfl) ⟨2585456, by rfl⟩ : syracuseStep 3447275 = 5170913) B5170913
theorem B2298183 : Blo 2297435 2298183 := bstep (se 1 (by rfl) ⟨1723637, by rfl⟩ : syracuseStep 2298183 = 3447275) B3447275
theorem B2585461 : Blo 2297435 2585461 := bbase (se 5 (by rfl) ⟨121193, by rfl⟩ : syracuseStep 2585461 = 242387) (by norm_num)
theorem B3447281 : Blo 2297435 3447281 := bstep (se 2 (by rfl) ⟨1292730, by rfl⟩ : syracuseStep 3447281 = 2585461) B2585461
theorem B2298187 : Blo 2297435 2298187 := bstep (se 1 (by rfl) ⟨1723640, by rfl⟩ : syracuseStep 2298187 = 3447281) B3447281
theorem B2908649 : Blo 2297435 2908649 := bbase (se 2 (by rfl) ⟨1090743, by rfl⟩ : syracuseStep 2908649 = 2181487) (by norm_num)
theorem B7756397 : Blo 2297435 7756397 := bstep (se 3 (by rfl) ⟨1454324, by rfl⟩ : syracuseStep 7756397 = 2908649) B2908649
theorem B5170931 : Blo 2297435 5170931 := bstep (se 1 (by rfl) ⟨3878198, by rfl⟩ : syracuseStep 5170931 = 7756397) B7756397
theorem B3447287 : Blo 2297435 3447287 := bstep (se 1 (by rfl) ⟨2585465, by rfl⟩ : syracuseStep 3447287 = 5170931) B5170931
theorem B2298191 : Blo 2297435 2298191 := bstep (se 1 (by rfl) ⟨1723643, by rfl⟩ : syracuseStep 2298191 = 3447287) B3447287
theorem B3447293 : Blo 2297435 3447293 := bbase (se 3 (by rfl) ⟨646367, by rfl⟩ : syracuseStep 3447293 = 1292735) (by norm_num)
theorem B2298195 : Blo 2297435 2298195 := bstep (se 1 (by rfl) ⟨1723646, by rfl⟩ : syracuseStep 2298195 = 3447293) B3447293
theorem B5170949 : Blo 2297435 5170949 := bbase (se 4 (by rfl) ⟨484776, by rfl⟩ : syracuseStep 5170949 = 969553) (by norm_num)
theorem B3447299 : Blo 2297435 3447299 := bstep (se 1 (by rfl) ⟨2585474, by rfl⟩ : syracuseStep 3447299 = 5170949) B5170949
theorem B2298199 : Blo 2297435 2298199 := bstep (se 1 (by rfl) ⟨1723649, by rfl⟩ : syracuseStep 2298199 = 3447299) B3447299
theorem B4362997 : Blo 2297435 4362997 := bbase (se 5 (by rfl) ⟨204515, by rfl⟩ : syracuseStep 4362997 = 409031) (by norm_num)
theorem B5817329 : Blo 2297435 5817329 := bstep (se 2 (by rfl) ⟨2181498, by rfl⟩ : syracuseStep 5817329 = 4362997) B4362997
theorem B3878219 : Blo 2297435 3878219 := bstep (se 1 (by rfl) ⟨2908664, by rfl⟩ : syracuseStep 3878219 = 5817329) B5817329
theorem B2585479 : Blo 2297435 2585479 := bstep (se 1 (by rfl) ⟨1939109, by rfl⟩ : syracuseStep 2585479 = 3878219) B3878219
theorem B3447305 : Blo 2297435 3447305 := bstep (se 2 (by rfl) ⟨1292739, by rfl⟩ : syracuseStep 3447305 = 2585479) B2585479
theorem B2298203 : Blo 2297435 2298203 := bstep (se 1 (by rfl) ⟨1723652, by rfl⟩ : syracuseStep 2298203 = 3447305) B3447305
theorem B11634677 : Blo 2297435 11634677 := bbase (se 5 (by rfl) ⟨545375, by rfl⟩ : syracuseStep 11634677 = 1090751) (by norm_num)
theorem B7756451 : Blo 2297435 7756451 := bstep (se 1 (by rfl) ⟨5817338, by rfl⟩ : syracuseStep 7756451 = 11634677) B11634677
theorem B5170967 : Blo 2297435 5170967 := bstep (se 1 (by rfl) ⟨3878225, by rfl⟩ : syracuseStep 5170967 = 7756451) B7756451
theorem B3447311 : Blo 2297435 3447311 := bstep (se 1 (by rfl) ⟨2585483, by rfl⟩ : syracuseStep 3447311 = 5170967) B5170967
theorem B2298207 : Blo 2297435 2298207 := bstep (se 1 (by rfl) ⟨1723655, by rfl⟩ : syracuseStep 2298207 = 3447311) B3447311
theorem B3447317 : Blo 2297435 3447317 := bbase (se 6 (by rfl) ⟨80796, by rfl⟩ : syracuseStep 3447317 = 161593) (by norm_num)
theorem B2298211 : Blo 2297435 2298211 := bstep (se 1 (by rfl) ⟨1723658, by rfl⟩ : syracuseStep 2298211 = 3447317) B3447317
theorem B19633589 : Blo 2297435 19633589 := bbase (se 5 (by rfl) ⟨920324, by rfl⟩ : syracuseStep 19633589 = 1840649) (by norm_num)
theorem B13089059 : Blo 2297435 13089059 := bstep (se 1 (by rfl) ⟨9816794, by rfl⟩ : syracuseStep 13089059 = 19633589) B19633589
theorem B8726039 : Blo 2297435 8726039 := bstep (se 1 (by rfl) ⟨6544529, by rfl⟩ : syracuseStep 8726039 = 13089059) B13089059
theorem B5817359 : Blo 2297435 5817359 := bstep (se 1 (by rfl) ⟨4363019, by rfl⟩ : syracuseStep 5817359 = 8726039) B8726039
theorem B3878239 : Blo 2297435 3878239 := bstep (se 1 (by rfl) ⟨2908679, by rfl⟩ : syracuseStep 3878239 = 5817359) B5817359
theorem B5170985 : Blo 2297435 5170985 := bstep (se 2 (by rfl) ⟨1939119, by rfl⟩ : syracuseStep 5170985 = 3878239) B3878239
theorem B3447323 : Blo 2297435 3447323 := bstep (se 1 (by rfl) ⟨2585492, by rfl⟩ : syracuseStep 3447323 = 5170985) B5170985
theorem B2298215 : Blo 2297435 2298215 := bstep (se 1 (by rfl) ⟨1723661, by rfl⟩ : syracuseStep 2298215 = 3447323) B3447323
theorem B2585497 : Blo 2297435 2585497 := bbase (se 2 (by rfl) ⟨969561, by rfl⟩ : syracuseStep 2585497 = 1939123) (by norm_num)
theorem B3447329 : Blo 2297435 3447329 := bstep (se 2 (by rfl) ⟨1292748, by rfl⟩ : syracuseStep 3447329 = 2585497) B2585497
theorem B2298219 : Blo 2297435 2298219 := bstep (se 1 (by rfl) ⟨1723664, by rfl⟩ : syracuseStep 2298219 = 3447329) B3447329
theorem B8726069 : Blo 2297435 8726069 := bbase (se 5 (by rfl) ⟨409034, by rfl⟩ : syracuseStep 8726069 = 818069) (by norm_num)
theorem B5817379 : Blo 2297435 5817379 := bstep (se 1 (by rfl) ⟨4363034, by rfl⟩ : syracuseStep 5817379 = 8726069) B8726069
theorem B7756505 : Blo 2297435 7756505 := bstep (se 2 (by rfl) ⟨2908689, by rfl⟩ : syracuseStep 7756505 = 5817379) B5817379
theorem B5171003 : Blo 2297435 5171003 := bstep (se 1 (by rfl) ⟨3878252, by rfl⟩ : syracuseStep 5171003 = 7756505) B7756505
theorem B3447335 : Blo 2297435 3447335 := bstep (se 1 (by rfl) ⟨2585501, by rfl⟩ : syracuseStep 3447335 = 5171003) B5171003
theorem B2298223 : Blo 2297435 2298223 := bstep (se 1 (by rfl) ⟨1723667, by rfl⟩ : syracuseStep 2298223 = 3447335) B3447335
theorem B3447341 : Blo 2297435 3447341 := bbase (se 3 (by rfl) ⟨646376, by rfl⟩ : syracuseStep 3447341 = 1292753) (by norm_num)
theorem B2298227 : Blo 2297435 2298227 := bstep (se 1 (by rfl) ⟨1723670, by rfl⟩ : syracuseStep 2298227 = 3447341) B3447341
theorem B5171021 : Blo 2297435 5171021 := bbase (se 3 (by rfl) ⟨969566, by rfl⟩ : syracuseStep 5171021 = 1939133) (by norm_num)
theorem B3447347 : Blo 2297435 3447347 := bstep (se 1 (by rfl) ⟨2585510, by rfl⟩ : syracuseStep 3447347 = 5171021) B5171021
theorem B2298231 : Blo 2297435 2298231 := bstep (se 1 (by rfl) ⟨1723673, by rfl⟩ : syracuseStep 2298231 = 3447347) B3447347
theorem B2908705 : Blo 2297435 2908705 := bbase (se 2 (by rfl) ⟨1090764, by rfl⟩ : syracuseStep 2908705 = 2181529) (by norm_num)
theorem B3878273 : Blo 2297435 3878273 := bstep (se 2 (by rfl) ⟨1454352, by rfl⟩ : syracuseStep 3878273 = 2908705) B2908705
theorem B2585515 : Blo 2297435 2585515 := bstep (se 1 (by rfl) ⟨1939136, by rfl⟩ : syracuseStep 2585515 = 3878273) B3878273
theorem B3447353 : Blo 2297435 3447353 := bstep (se 2 (by rfl) ⟨1292757, by rfl⟩ : syracuseStep 3447353 = 2585515) B2585515
theorem B2298235 : Blo 2297435 2298235 := bstep (se 1 (by rfl) ⟨1723676, by rfl⟩ : syracuseStep 2298235 = 3447353) B3447353
theorem B26178389 : Blo 2297435 26178389 := bbase (se 9 (by rfl) ⟨76694, by rfl⟩ : syracuseStep 26178389 = 153389) (by norm_num)
theorem B17452259 : Blo 2297435 17452259 := bstep (se 1 (by rfl) ⟨13089194, by rfl⟩ : syracuseStep 17452259 = 26178389) B26178389
theorem B11634839 : Blo 2297435 11634839 := bstep (se 1 (by rfl) ⟨8726129, by rfl⟩ : syracuseStep 11634839 = 17452259) B17452259
theorem B7756559 : Blo 2297435 7756559 := bstep (se 1 (by rfl) ⟨5817419, by rfl⟩ : syracuseStep 7756559 = 11634839) B11634839
theorem B5171039 : Blo 2297435 5171039 := bstep (se 1 (by rfl) ⟨3878279, by rfl⟩ : syracuseStep 5171039 = 7756559) B7756559
theorem B3447359 : Blo 2297435 3447359 := bstep (se 1 (by rfl) ⟨2585519, by rfl⟩ : syracuseStep 3447359 = 5171039) B5171039
theorem B2298239 : Blo 2297435 2298239 := bstep (se 1 (by rfl) ⟨1723679, by rfl⟩ : syracuseStep 2298239 = 3447359) B3447359
theorem B3447365 : Blo 2297435 3447365 := bbase (se 4 (by rfl) ⟨323190, by rfl⟩ : syracuseStep 3447365 = 646381) (by norm_num)
theorem B2298243 : Blo 2297435 2298243 := bstep (se 1 (by rfl) ⟨1723682, by rfl⟩ : syracuseStep 2298243 = 3447365) B3447365
theorem B3878293 : Blo 2297435 3878293 := bbase (se 6 (by rfl) ⟨90897, by rfl⟩ : syracuseStep 3878293 = 181795) (by norm_num)
theorem B5171057 : Blo 2297435 5171057 := bstep (se 2 (by rfl) ⟨1939146, by rfl⟩ : syracuseStep 5171057 = 3878293) B3878293
theorem B3447371 : Blo 2297435 3447371 := bstep (se 1 (by rfl) ⟨2585528, by rfl⟩ : syracuseStep 3447371 = 5171057) B5171057
theorem B2298247 : Blo 2297435 2298247 := bstep (se 1 (by rfl) ⟨1723685, by rfl⟩ : syracuseStep 2298247 = 3447371) B3447371
theorem B2585533 : Blo 2297435 2585533 := bbase (se 3 (by rfl) ⟨484787, by rfl⟩ : syracuseStep 2585533 = 969575) (by norm_num)
theorem B3447377 : Blo 2297435 3447377 := bstep (se 2 (by rfl) ⟨1292766, by rfl⟩ : syracuseStep 3447377 = 2585533) B2585533
theorem B2298251 : Blo 2297435 2298251 := bstep (se 1 (by rfl) ⟨1723688, by rfl⟩ : syracuseStep 2298251 = 3447377) B3447377
theorem B7756613 : Blo 2297435 7756613 := bbase (se 4 (by rfl) ⟨727182, by rfl⟩ : syracuseStep 7756613 = 1454365) (by norm_num)
theorem B5171075 : Blo 2297435 5171075 := bstep (se 1 (by rfl) ⟨3878306, by rfl⟩ : syracuseStep 5171075 = 7756613) B7756613
theorem B3447383 : Blo 2297435 3447383 := bstep (se 1 (by rfl) ⟨2585537, by rfl⟩ : syracuseStep 3447383 = 5171075) B5171075
theorem B2298255 : Blo 2297435 2298255 := bstep (se 1 (by rfl) ⟨1723691, by rfl⟩ : syracuseStep 2298255 = 3447383) B3447383
theorem B3447389 : Blo 2297435 3447389 := bbase (se 3 (by rfl) ⟨646385, by rfl⟩ : syracuseStep 3447389 = 1292771) (by norm_num)
theorem B2298259 : Blo 2297435 2298259 := bstep (se 1 (by rfl) ⟨1723694, by rfl⟩ : syracuseStep 2298259 = 3447389) B3447389
theorem B5171093 : Blo 2297435 5171093 := bbase (se 6 (by rfl) ⟨121197, by rfl⟩ : syracuseStep 5171093 = 242395) (by norm_num)
theorem B3447395 : Blo 2297435 3447395 := bstep (se 1 (by rfl) ⟨2585546, by rfl⟩ : syracuseStep 3447395 = 5171093) B5171093
theorem B2298263 : Blo 2297435 2298263 := bstep (se 1 (by rfl) ⟨1723697, by rfl⟩ : syracuseStep 2298263 = 3447395) B3447395
theorem B4908509 : Blo 2297435 4908509 := bbase (se 3 (by rfl) ⟨920345, by rfl⟩ : syracuseStep 4908509 = 1840691) (by norm_num)
theorem B3272339 : Blo 2297435 3272339 := bstep (se 1 (by rfl) ⟨2454254, by rfl⟩ : syracuseStep 3272339 = 4908509) B4908509
theorem B8726237 : Blo 2297435 8726237 := bstep (se 3 (by rfl) ⟨1636169, by rfl⟩ : syracuseStep 8726237 = 3272339) B3272339
theorem B5817491 : Blo 2297435 5817491 := bstep (se 1 (by rfl) ⟨4363118, by rfl⟩ : syracuseStep 5817491 = 8726237) B8726237
theorem B3878327 : Blo 2297435 3878327 := bstep (se 1 (by rfl) ⟨2908745, by rfl⟩ : syracuseStep 3878327 = 5817491) B5817491
theorem B2585551 : Blo 2297435 2585551 := bstep (se 1 (by rfl) ⟨1939163, by rfl⟩ : syracuseStep 2585551 = 3878327) B3878327
theorem B3447401 : Blo 2297435 3447401 := bstep (se 2 (by rfl) ⟨1292775, by rfl⟩ : syracuseStep 3447401 = 2585551) B2585551
theorem B2298267 : Blo 2297435 2298267 := bstep (se 1 (by rfl) ⟨1723700, by rfl⟩ : syracuseStep 2298267 = 3447401) B3447401
theorem B2948437 : Blo 2297435 2948437 := bbase (se 11 (by rfl) ⟨2159, by rfl⟩ : syracuseStep 2948437 = 4319) (by norm_num)
theorem B3931249 : Blo 2297435 3931249 := bstep (se 2 (by rfl) ⟨1474218, by rfl⟩ : syracuseStep 3931249 = 2948437) B2948437
theorem B5241665 : Blo 2297435 5241665 := bstep (se 2 (by rfl) ⟨1965624, by rfl⟩ : syracuseStep 5241665 = 3931249) B3931249
theorem B3494443 : Blo 2297435 3494443 := bstep (se 1 (by rfl) ⟨2620832, by rfl⟩ : syracuseStep 3494443 = 5241665) B5241665
theorem B4659257 : Blo 2297435 4659257 := bstep (se 2 (by rfl) ⟨1747221, by rfl⟩ : syracuseStep 4659257 = 3494443) B3494443
theorem B3106171 : Blo 2297435 3106171 := bstep (se 1 (by rfl) ⟨2329628, by rfl⟩ : syracuseStep 3106171 = 4659257) B4659257
theorem B16566245 : Blo 2297435 16566245 := bstep (se 4 (by rfl) ⟨1553085, by rfl⟩ : syracuseStep 16566245 = 3106171) B3106171
theorem B11044163 : Blo 2297435 11044163 := bstep (se 1 (by rfl) ⟨8283122, by rfl⟩ : syracuseStep 11044163 = 16566245) B16566245
theorem B7362775 : Blo 2297435 7362775 := bstep (se 1 (by rfl) ⟨5522081, by rfl⟩ : syracuseStep 7362775 = 11044163) B11044163
theorem B9817033 : Blo 2297435 9817033 := bstep (se 2 (by rfl) ⟨3681387, by rfl⟩ : syracuseStep 9817033 = 7362775) B7362775
theorem B13089377 : Blo 2297435 13089377 := bstep (se 2 (by rfl) ⟨4908516, by rfl⟩ : syracuseStep 13089377 = 9817033) B9817033
theorem B8726251 : Blo 2297435 8726251 := bstep (se 1 (by rfl) ⟨6544688, by rfl⟩ : syracuseStep 8726251 = 13089377) B13089377
theorem B11635001 : Blo 2297435 11635001 := bstep (se 2 (by rfl) ⟨4363125, by rfl⟩ : syracuseStep 11635001 = 8726251) B8726251
theorem B7756667 : Blo 2297435 7756667 := bstep (se 1 (by rfl) ⟨5817500, by rfl⟩ : syracuseStep 7756667 = 11635001) B11635001
theorem B5171111 : Blo 2297435 5171111 := bstep (se 1 (by rfl) ⟨3878333, by rfl⟩ : syracuseStep 5171111 = 7756667) B7756667
theorem B3447407 : Blo 2297435 3447407 := bstep (se 1 (by rfl) ⟨2585555, by rfl⟩ : syracuseStep 3447407 = 5171111) B5171111
theorem B2298271 : Blo 2297435 2298271 := bstep (se 1 (by rfl) ⟨1723703, by rfl⟩ : syracuseStep 2298271 = 3447407) B3447407
theorem B3447413 : Blo 2297435 3447413 := bbase (se 5 (by rfl) ⟨161597, by rfl⟩ : syracuseStep 3447413 = 323195) (by norm_num)
theorem B2298275 : Blo 2297435 2298275 := bstep (se 1 (by rfl) ⟨1723706, by rfl⟩ : syracuseStep 2298275 = 3447413) B3447413
theorem B4363141 : Blo 2297435 4363141 := bbase (se 4 (by rfl) ⟨409044, by rfl⟩ : syracuseStep 4363141 = 818089) (by norm_num)
theorem B5817521 : Blo 2297435 5817521 := bstep (se 2 (by rfl) ⟨2181570, by rfl⟩ : syracuseStep 5817521 = 4363141) B4363141
theorem B3878347 : Blo 2297435 3878347 := bstep (se 1 (by rfl) ⟨2908760, by rfl⟩ : syracuseStep 3878347 = 5817521) B5817521
theorem B5171129 : Blo 2297435 5171129 := bstep (se 2 (by rfl) ⟨1939173, by rfl⟩ : syracuseStep 5171129 = 3878347) B3878347
theorem B3447419 : Blo 2297435 3447419 := bstep (se 1 (by rfl) ⟨2585564, by rfl⟩ : syracuseStep 3447419 = 5171129) B5171129
theorem B2298279 : Blo 2297435 2298279 := bstep (se 1 (by rfl) ⟨1723709, by rfl⟩ : syracuseStep 2298279 = 3447419) B3447419
theorem B2585569 : Blo 2297435 2585569 := bbase (se 2 (by rfl) ⟨969588, by rfl⟩ : syracuseStep 2585569 = 1939177) (by norm_num)
theorem B3447425 : Blo 2297435 3447425 := bstep (se 2 (by rfl) ⟨1292784, by rfl⟩ : syracuseStep 3447425 = 2585569) B2585569
theorem B2298283 : Blo 2297435 2298283 := bstep (se 1 (by rfl) ⟨1723712, by rfl⟩ : syracuseStep 2298283 = 3447425) B3447425
theorem B5817541 : Blo 2297435 5817541 := bbase (se 4 (by rfl) ⟨545394, by rfl⟩ : syracuseStep 5817541 = 1090789) (by norm_num)
theorem B7756721 : Blo 2297435 7756721 := bstep (se 2 (by rfl) ⟨2908770, by rfl⟩ : syracuseStep 7756721 = 5817541) B5817541
theorem B5171147 : Blo 2297435 5171147 := bstep (se 1 (by rfl) ⟨3878360, by rfl⟩ : syracuseStep 5171147 = 7756721) B7756721
theorem B3447431 : Blo 2297435 3447431 := bstep (se 1 (by rfl) ⟨2585573, by rfl⟩ : syracuseStep 3447431 = 5171147) B5171147
theorem B2298287 : Blo 2297435 2298287 := bstep (se 1 (by rfl) ⟨1723715, by rfl⟩ : syracuseStep 2298287 = 3447431) B3447431
theorem B3447437 : Blo 2297435 3447437 := bbase (se 3 (by rfl) ⟨646394, by rfl⟩ : syracuseStep 3447437 = 1292789) (by norm_num)
theorem B2298291 : Blo 2297435 2298291 := bstep (se 1 (by rfl) ⟨1723718, by rfl⟩ : syracuseStep 2298291 = 3447437) B3447437
theorem B5171165 : Blo 2297435 5171165 := bbase (se 3 (by rfl) ⟨969593, by rfl⟩ : syracuseStep 5171165 = 1939187) (by norm_num)
theorem B3447443 : Blo 2297435 3447443 := bstep (se 1 (by rfl) ⟨2585582, by rfl⟩ : syracuseStep 3447443 = 5171165) B5171165
theorem B2298295 : Blo 2297435 2298295 := bstep (se 1 (by rfl) ⟨1723721, by rfl⟩ : syracuseStep 2298295 = 3447443) B3447443
theorem B3878381 : Blo 2297435 3878381 := bbase (se 3 (by rfl) ⟨727196, by rfl⟩ : syracuseStep 3878381 = 1454393) (by norm_num)
theorem B2585587 : Blo 2297435 2585587 := bstep (se 1 (by rfl) ⟨1939190, by rfl⟩ : syracuseStep 2585587 = 3878381) B3878381
theorem B3447449 : Blo 2297435 3447449 := bstep (se 2 (by rfl) ⟨1292793, by rfl⟩ : syracuseStep 3447449 = 2585587) B2585587
theorem B2298299 : Blo 2297435 2298299 := bstep (se 1 (by rfl) ⟨1723724, by rfl⟩ : syracuseStep 2298299 = 3447449) B3447449
theorem B2329661 : Blo 2297435 2329661 := bbase (se 3 (by rfl) ⟨436811, by rfl⟩ : syracuseStep 2329661 = 873623) (by norm_num)
theorem B6212429 : Blo 2297435 6212429 := bstep (se 3 (by rfl) ⟨1164830, by rfl⟩ : syracuseStep 6212429 = 2329661) B2329661
theorem B4141619 : Blo 2297435 4141619 := bstep (se 1 (by rfl) ⟨3106214, by rfl⟩ : syracuseStep 4141619 = 6212429) B6212429
theorem B2761079 : Blo 2297435 2761079 := bstep (se 1 (by rfl) ⟨2070809, by rfl⟩ : syracuseStep 2761079 = 4141619) B4141619
theorem B29451509 : Blo 2297435 29451509 := bstep (se 5 (by rfl) ⟨1380539, by rfl⟩ : syracuseStep 29451509 = 2761079) B2761079
theorem B19634339 : Blo 2297435 19634339 := bstep (se 1 (by rfl) ⟨14725754, by rfl⟩ : syracuseStep 19634339 = 29451509) B29451509
theorem B13089559 : Blo 2297435 13089559 := bstep (se 1 (by rfl) ⟨9817169, by rfl⟩ : syracuseStep 13089559 = 19634339) B19634339
theorem B17452745 : Blo 2297435 17452745 := bstep (se 2 (by rfl) ⟨6544779, by rfl⟩ : syracuseStep 17452745 = 13089559) B13089559
theorem B11635163 : Blo 2297435 11635163 := bstep (se 1 (by rfl) ⟨8726372, by rfl⟩ : syracuseStep 11635163 = 17452745) B17452745
theorem B7756775 : Blo 2297435 7756775 := bstep (se 1 (by rfl) ⟨5817581, by rfl⟩ : syracuseStep 7756775 = 11635163) B11635163
theorem B5171183 : Blo 2297435 5171183 := bstep (se 1 (by rfl) ⟨3878387, by rfl⟩ : syracuseStep 5171183 = 7756775) B7756775
theorem B3447455 : Blo 2297435 3447455 := bstep (se 1 (by rfl) ⟨2585591, by rfl⟩ : syracuseStep 3447455 = 5171183) B5171183
theorem B2298303 : Blo 2297435 2298303 := bstep (se 1 (by rfl) ⟨1723727, by rfl⟩ : syracuseStep 2298303 = 3447455) B3447455
theorem B3447461 : Blo 2297435 3447461 := bbase (se 4 (by rfl) ⟨323199, by rfl⟩ : syracuseStep 3447461 = 646399) (by norm_num)
theorem B2298307 : Blo 2297435 2298307 := bstep (se 1 (by rfl) ⟨1723730, by rfl⟩ : syracuseStep 2298307 = 3447461) B3447461
theorem B2908801 : Blo 2297435 2908801 := bbase (se 2 (by rfl) ⟨1090800, by rfl⟩ : syracuseStep 2908801 = 2181601) (by norm_num)
theorem B3878401 : Blo 2297435 3878401 := bstep (se 2 (by rfl) ⟨1454400, by rfl⟩ : syracuseStep 3878401 = 2908801) B2908801
theorem B5171201 : Blo 2297435 5171201 := bstep (se 2 (by rfl) ⟨1939200, by rfl⟩ : syracuseStep 5171201 = 3878401) B3878401
theorem B3447467 : Blo 2297435 3447467 := bstep (se 1 (by rfl) ⟨2585600, by rfl⟩ : syracuseStep 3447467 = 5171201) B5171201
theorem B2298311 : Blo 2297435 2298311 := bstep (se 1 (by rfl) ⟨1723733, by rfl⟩ : syracuseStep 2298311 = 3447467) B3447467
theorem B2585605 : Blo 2297435 2585605 := bbase (se 4 (by rfl) ⟨242400, by rfl⟩ : syracuseStep 2585605 = 484801) (by norm_num)
theorem B3447473 : Blo 2297435 3447473 := bstep (se 2 (by rfl) ⟨1292802, by rfl⟩ : syracuseStep 3447473 = 2585605) B2585605
theorem B2298315 : Blo 2297435 2298315 := bstep (se 1 (by rfl) ⟨1723736, by rfl⟩ : syracuseStep 2298315 = 3447473) B3447473
theorem B3272413 : Blo 2297435 3272413 := bbase (se 3 (by rfl) ⟨613577, by rfl⟩ : syracuseStep 3272413 = 1227155) (by norm_num)
theorem B4363217 : Blo 2297435 4363217 := bstep (se 2 (by rfl) ⟨1636206, by rfl⟩ : syracuseStep 4363217 = 3272413) B3272413
theorem B2908811 : Blo 2297435 2908811 := bstep (se 1 (by rfl) ⟨2181608, by rfl⟩ : syracuseStep 2908811 = 4363217) B4363217
theorem B7756829 : Blo 2297435 7756829 := bstep (se 3 (by rfl) ⟨1454405, by rfl⟩ : syracuseStep 7756829 = 2908811) B2908811
theorem B5171219 : Blo 2297435 5171219 := bstep (se 1 (by rfl) ⟨3878414, by rfl⟩ : syracuseStep 5171219 = 7756829) B7756829
theorem B3447479 : Blo 2297435 3447479 := bstep (se 1 (by rfl) ⟨2585609, by rfl⟩ : syracuseStep 3447479 = 5171219) B5171219
theorem B2298319 : Blo 2297435 2298319 := bstep (se 1 (by rfl) ⟨1723739, by rfl⟩ : syracuseStep 2298319 = 3447479) B3447479
theorem B3447485 : Blo 2297435 3447485 := bbase (se 3 (by rfl) ⟨646403, by rfl⟩ : syracuseStep 3447485 = 1292807) (by norm_num)
theorem B2298323 : Blo 2297435 2298323 := bstep (se 1 (by rfl) ⟨1723742, by rfl⟩ : syracuseStep 2298323 = 3447485) B3447485
theorem B5171237 : Blo 2297435 5171237 := bbase (se 4 (by rfl) ⟨484803, by rfl⟩ : syracuseStep 5171237 = 969607) (by norm_num)
theorem B3447491 : Blo 2297435 3447491 := bstep (se 1 (by rfl) ⟨2585618, by rfl⟩ : syracuseStep 3447491 = 5171237) B5171237
theorem B2298327 : Blo 2297435 2298327 := bstep (se 1 (by rfl) ⟨1723745, by rfl⟩ : syracuseStep 2298327 = 3447491) B3447491
theorem B5817653 : Blo 2297435 5817653 := bbase (se 5 (by rfl) ⟨272702, by rfl⟩ : syracuseStep 5817653 = 545405) (by norm_num)
theorem B3878435 : Blo 2297435 3878435 := bstep (se 1 (by rfl) ⟨2908826, by rfl⟩ : syracuseStep 3878435 = 5817653) B5817653
theorem B2585623 : Blo 2297435 2585623 := bstep (se 1 (by rfl) ⟨1939217, by rfl⟩ : syracuseStep 2585623 = 3878435) B3878435
theorem B3447497 : Blo 2297435 3447497 := bstep (se 2 (by rfl) ⟨1292811, by rfl⟩ : syracuseStep 3447497 = 2585623) B2585623
theorem B2298331 : Blo 2297435 2298331 := bstep (se 1 (by rfl) ⟨1723748, by rfl⟩ : syracuseStep 2298331 = 3447497) B3447497
theorem B9318773 : Blo 2297435 9318773 := bbase (se 5 (by rfl) ⟨436817, by rfl⟩ : syracuseStep 9318773 = 873635) (by norm_num)
theorem B24850061 : Blo 2297435 24850061 := bstep (se 3 (by rfl) ⟨4659386, by rfl⟩ : syracuseStep 24850061 = 9318773) B9318773
theorem B16566707 : Blo 2297435 16566707 := bstep (se 1 (by rfl) ⟨12425030, by rfl⟩ : syracuseStep 16566707 = 24850061) B24850061
theorem B11044471 : Blo 2297435 11044471 := bstep (se 1 (by rfl) ⟨8283353, by rfl⟩ : syracuseStep 11044471 = 16566707) B16566707
theorem B14725961 : Blo 2297435 14725961 := bstep (se 2 (by rfl) ⟨5522235, by rfl⟩ : syracuseStep 14725961 = 11044471) B11044471
theorem B9817307 : Blo 2297435 9817307 := bstep (se 1 (by rfl) ⟨7362980, by rfl⟩ : syracuseStep 9817307 = 14725961) B14725961
theorem B6544871 : Blo 2297435 6544871 := bstep (se 1 (by rfl) ⟨4908653, by rfl⟩ : syracuseStep 6544871 = 9817307) B9817307
theorem B4363247 : Blo 2297435 4363247 := bstep (se 1 (by rfl) ⟨3272435, by rfl⟩ : syracuseStep 4363247 = 6544871) B6544871
theorem B11635325 : Blo 2297435 11635325 := bstep (se 3 (by rfl) ⟨2181623, by rfl⟩ : syracuseStep 11635325 = 4363247) B4363247
theorem B7756883 : Blo 2297435 7756883 := bstep (se 1 (by rfl) ⟨5817662, by rfl⟩ : syracuseStep 7756883 = 11635325) B11635325
theorem B5171255 : Blo 2297435 5171255 := bstep (se 1 (by rfl) ⟨3878441, by rfl⟩ : syracuseStep 5171255 = 7756883) B7756883
theorem B3447503 : Blo 2297435 3447503 := bstep (se 1 (by rfl) ⟨2585627, by rfl⟩ : syracuseStep 3447503 = 5171255) B5171255
theorem B2298335 : Blo 2297435 2298335 := bstep (se 1 (by rfl) ⟨1723751, by rfl⟩ : syracuseStep 2298335 = 3447503) B3447503
theorem B3447509 : Blo 2297435 3447509 := bbase (se 7 (by rfl) ⟨40400, by rfl⟩ : syracuseStep 3447509 = 80801) (by norm_num)
theorem B2298339 : Blo 2297435 2298339 := bstep (se 1 (by rfl) ⟨1723754, by rfl⟩ : syracuseStep 2298339 = 3447509) B3447509
theorem B18891893 : Blo 2297435 18891893 := bbase (se 5 (by rfl) ⟨885557, by rfl⟩ : syracuseStep 18891893 = 1771115) (by norm_num)
theorem B50378381 : Blo 2297435 50378381 := bstep (se 3 (by rfl) ⟨9445946, by rfl⟩ : syracuseStep 50378381 = 18891893) B18891893
theorem B33585587 : Blo 2297435 33585587 := bstep (se 1 (by rfl) ⟨25189190, by rfl⟩ : syracuseStep 33585587 = 50378381) B50378381
theorem B22390391 : Blo 2297435 22390391 := bstep (se 1 (by rfl) ⟨16792793, by rfl⟩ : syracuseStep 22390391 = 33585587) B33585587
theorem B59707709 : Blo 2297435 59707709 := bstep (se 3 (by rfl) ⟨11195195, by rfl⟩ : syracuseStep 59707709 = 22390391) B22390391
theorem B39805139 : Blo 2297435 39805139 := bstep (se 1 (by rfl) ⟨29853854, by rfl⟩ : syracuseStep 39805139 = 59707709) B59707709
theorem B106147037 : Blo 2297435 106147037 := bstep (se 3 (by rfl) ⟨19902569, by rfl⟩ : syracuseStep 106147037 = 39805139) B39805139
theorem B70764691 : Blo 2297435 70764691 := bstep (se 1 (by rfl) ⟨53073518, by rfl⟩ : syracuseStep 70764691 = 106147037) B106147037
theorem B94352921 : Blo 2297435 94352921 := bstep (se 2 (by rfl) ⟨35382345, by rfl⟩ : syracuseStep 94352921 = 70764691) B70764691
theorem B62901947 : Blo 2297435 62901947 := bstep (se 1 (by rfl) ⟨47176460, by rfl⟩ : syracuseStep 62901947 = 94352921) B94352921
theorem B41934631 : Blo 2297435 41934631 := bstep (se 1 (by rfl) ⟨31450973, by rfl⟩ : syracuseStep 41934631 = 62901947) B62901947
theorem B55912841 : Blo 2297435 55912841 := bstep (se 2 (by rfl) ⟨20967315, by rfl⟩ : syracuseStep 55912841 = 41934631) B41934631
theorem B37275227 : Blo 2297435 37275227 := bstep (se 1 (by rfl) ⟨27956420, by rfl⟩ : syracuseStep 37275227 = 55912841) B55912841
theorem B24850151 : Blo 2297435 24850151 := bstep (se 1 (by rfl) ⟨18637613, by rfl⟩ : syracuseStep 24850151 = 37275227) B37275227
theorem B16566767 : Blo 2297435 16566767 := bstep (se 1 (by rfl) ⟨12425075, by rfl⟩ : syracuseStep 16566767 = 24850151) B24850151
theorem B11044511 : Blo 2297435 11044511 := bstep (se 1 (by rfl) ⟨8283383, by rfl⟩ : syracuseStep 11044511 = 16566767) B16566767
theorem B7363007 : Blo 2297435 7363007 := bstep (se 1 (by rfl) ⟨5522255, by rfl⟩ : syracuseStep 7363007 = 11044511) B11044511
theorem B4908671 : Blo 2297435 4908671 := bstep (se 1 (by rfl) ⟨3681503, by rfl⟩ : syracuseStep 4908671 = 7363007) B7363007
theorem B3272447 : Blo 2297435 3272447 := bstep (se 1 (by rfl) ⟨2454335, by rfl⟩ : syracuseStep 3272447 = 4908671) B4908671
theorem B8726525 : Blo 2297435 8726525 := bstep (se 3 (by rfl) ⟨1636223, by rfl⟩ : syracuseStep 8726525 = 3272447) B3272447
theorem B5817683 : Blo 2297435 5817683 := bstep (se 1 (by rfl) ⟨4363262, by rfl⟩ : syracuseStep 5817683 = 8726525) B8726525
theorem B3878455 : Blo 2297435 3878455 := bstep (se 1 (by rfl) ⟨2908841, by rfl⟩ : syracuseStep 3878455 = 5817683) B5817683
theorem B5171273 : Blo 2297435 5171273 := bstep (se 2 (by rfl) ⟨1939227, by rfl⟩ : syracuseStep 5171273 = 3878455) B3878455
theorem B3447515 : Blo 2297435 3447515 := bstep (se 1 (by rfl) ⟨2585636, by rfl⟩ : syracuseStep 3447515 = 5171273) B5171273
theorem B2298343 : Blo 2297435 2298343 := bstep (se 1 (by rfl) ⟨1723757, by rfl⟩ : syracuseStep 2298343 = 3447515) B3447515
theorem B2585641 : Blo 2297435 2585641 := bbase (se 2 (by rfl) ⟨969615, by rfl⟩ : syracuseStep 2585641 = 1939231) (by norm_num)
theorem B3447521 : Blo 2297435 3447521 := bstep (se 2 (by rfl) ⟨1292820, by rfl⟩ : syracuseStep 3447521 = 2585641) B2585641
theorem B2298347 : Blo 2297435 2298347 := bstep (se 1 (by rfl) ⟨1723760, by rfl⟩ : syracuseStep 2298347 = 3447521) B3447521
theorem B37275349 : Blo 2297435 37275349 := bbase (se 7 (by rfl) ⟨436820, by rfl⟩ : syracuseStep 37275349 = 873641) (by norm_num)
theorem B49700465 : Blo 2297435 49700465 := bstep (se 2 (by rfl) ⟨18637674, by rfl⟩ : syracuseStep 49700465 = 37275349) B37275349
theorem B33133643 : Blo 2297435 33133643 := bstep (se 1 (by rfl) ⟨24850232, by rfl⟩ : syracuseStep 33133643 = 49700465) B49700465
theorem B22089095 : Blo 2297435 22089095 := bstep (se 1 (by rfl) ⟨16566821, by rfl⟩ : syracuseStep 22089095 = 33133643) B33133643
theorem B14726063 : Blo 2297435 14726063 := bstep (se 1 (by rfl) ⟨11044547, by rfl⟩ : syracuseStep 14726063 = 22089095) B22089095
theorem B9817375 : Blo 2297435 9817375 := bstep (se 1 (by rfl) ⟨7363031, by rfl⟩ : syracuseStep 9817375 = 14726063) B14726063
theorem B13089833 : Blo 2297435 13089833 := bstep (se 2 (by rfl) ⟨4908687, by rfl⟩ : syracuseStep 13089833 = 9817375) B9817375
theorem B8726555 : Blo 2297435 8726555 := bstep (se 1 (by rfl) ⟨6544916, by rfl⟩ : syracuseStep 8726555 = 13089833) B13089833
theorem B5817703 : Blo 2297435 5817703 := bstep (se 1 (by rfl) ⟨4363277, by rfl⟩ : syracuseStep 5817703 = 8726555) B8726555
theorem B7756937 : Blo 2297435 7756937 := bstep (se 2 (by rfl) ⟨2908851, by rfl⟩ : syracuseStep 7756937 = 5817703) B5817703
theorem B5171291 : Blo 2297435 5171291 := bstep (se 1 (by rfl) ⟨3878468, by rfl⟩ : syracuseStep 5171291 = 7756937) B7756937
theorem B3447527 : Blo 2297435 3447527 := bstep (se 1 (by rfl) ⟨2585645, by rfl⟩ : syracuseStep 3447527 = 5171291) B5171291
theorem B2298351 : Blo 2297435 2298351 := bstep (se 1 (by rfl) ⟨1723763, by rfl⟩ : syracuseStep 2298351 = 3447527) B3447527
theorem B3447533 : Blo 2297435 3447533 := bbase (se 3 (by rfl) ⟨646412, by rfl⟩ : syracuseStep 3447533 = 1292825) (by norm_num)
theorem B2298355 : Blo 2297435 2298355 := bstep (se 1 (by rfl) ⟨1723766, by rfl⟩ : syracuseStep 2298355 = 3447533) B3447533
theorem B5171309 : Blo 2297435 5171309 := bbase (se 3 (by rfl) ⟨969620, by rfl⟩ : syracuseStep 5171309 = 1939241) (by norm_num)
theorem B3447539 : Blo 2297435 3447539 := bstep (se 1 (by rfl) ⟨2585654, by rfl⟩ : syracuseStep 3447539 = 5171309) B5171309
theorem B2298359 : Blo 2297435 2298359 := bstep (se 1 (by rfl) ⟨1723769, by rfl⟩ : syracuseStep 2298359 = 3447539) B3447539
theorem B4363301 : Blo 2297435 4363301 := bbase (se 4 (by rfl) ⟨409059, by rfl⟩ : syracuseStep 4363301 = 818119) (by norm_num)
theorem B2908867 : Blo 2297435 2908867 := bstep (se 1 (by rfl) ⟨2181650, by rfl⟩ : syracuseStep 2908867 = 4363301) B4363301
theorem B3878489 : Blo 2297435 3878489 := bstep (se 2 (by rfl) ⟨1454433, by rfl⟩ : syracuseStep 3878489 = 2908867) B2908867
theorem B2585659 : Blo 2297435 2585659 := bstep (se 1 (by rfl) ⟨1939244, by rfl⟩ : syracuseStep 2585659 = 3878489) B3878489
theorem B3447545 : Blo 2297435 3447545 := bstep (se 2 (by rfl) ⟨1292829, by rfl⟩ : syracuseStep 3447545 = 2585659) B2585659
theorem B2298363 : Blo 2297435 2298363 := bstep (se 1 (by rfl) ⟨1723772, by rfl⟩ : syracuseStep 2298363 = 3447545) B3447545
theorem B37275605 : Blo 2297435 37275605 := bbase (se 7 (by rfl) ⟨436823, by rfl⟩ : syracuseStep 37275605 = 873647) (by norm_num)
theorem B24850403 : Blo 2297435 24850403 := bstep (se 1 (by rfl) ⟨18637802, by rfl⟩ : syracuseStep 24850403 = 37275605) B37275605
theorem B16566935 : Blo 2297435 16566935 := bstep (se 1 (by rfl) ⟨12425201, by rfl⟩ : syracuseStep 16566935 = 24850403) B24850403
theorem B44178493 : Blo 2297435 44178493 := bstep (se 3 (by rfl) ⟨8283467, by rfl⟩ : syracuseStep 44178493 = 16566935) B16566935
theorem B58904657 : Blo 2297435 58904657 := bstep (se 2 (by rfl) ⟨22089246, by rfl⟩ : syracuseStep 58904657 = 44178493) B44178493
theorem B39269771 : Blo 2297435 39269771 := bstep (se 1 (by rfl) ⟨29452328, by rfl⟩ : syracuseStep 39269771 = 58904657) B58904657
theorem B26179847 : Blo 2297435 26179847 := bstep (se 1 (by rfl) ⟨19634885, by rfl⟩ : syracuseStep 26179847 = 39269771) B39269771
theorem B17453231 : Blo 2297435 17453231 := bstep (se 1 (by rfl) ⟨13089923, by rfl⟩ : syracuseStep 17453231 = 26179847) B26179847
theorem B11635487 : Blo 2297435 11635487 := bstep (se 1 (by rfl) ⟨8726615, by rfl⟩ : syracuseStep 11635487 = 17453231) B17453231
theorem B7756991 : Blo 2297435 7756991 := bstep (se 1 (by rfl) ⟨5817743, by rfl⟩ : syracuseStep 7756991 = 11635487) B11635487
theorem B5171327 : Blo 2297435 5171327 := bstep (se 1 (by rfl) ⟨3878495, by rfl⟩ : syracuseStep 5171327 = 7756991) B7756991
theorem B3447551 : Blo 2297435 3447551 := bstep (se 1 (by rfl) ⟨2585663, by rfl⟩ : syracuseStep 3447551 = 5171327) B5171327
theorem B2298367 : Blo 2297435 2298367 := bstep (se 1 (by rfl) ⟨1723775, by rfl⟩ : syracuseStep 2298367 = 3447551) B3447551
theorem B3447557 : Blo 2297435 3447557 := bbase (se 4 (by rfl) ⟨323208, by rfl⟩ : syracuseStep 3447557 = 646417) (by norm_num)
theorem B2298371 : Blo 2297435 2298371 := bstep (se 1 (by rfl) ⟨1723778, by rfl⟩ : syracuseStep 2298371 = 3447557) B3447557
theorem B3878509 : Blo 2297435 3878509 := bbase (se 3 (by rfl) ⟨727220, by rfl⟩ : syracuseStep 3878509 = 1454441) (by norm_num)
theorem B5171345 : Blo 2297435 5171345 := bstep (se 2 (by rfl) ⟨1939254, by rfl⟩ : syracuseStep 5171345 = 3878509) B3878509
theorem B3447563 : Blo 2297435 3447563 := bstep (se 1 (by rfl) ⟨2585672, by rfl⟩ : syracuseStep 3447563 = 5171345) B5171345
theorem B2298375 : Blo 2297435 2298375 := bstep (se 1 (by rfl) ⟨1723781, by rfl⟩ : syracuseStep 2298375 = 3447563) B3447563
theorem B2585677 : Blo 2297435 2585677 := bbase (se 3 (by rfl) ⟨484814, by rfl⟩ : syracuseStep 2585677 = 969629) (by norm_num)
theorem B3447569 : Blo 2297435 3447569 := bstep (se 2 (by rfl) ⟨1292838, by rfl⟩ : syracuseStep 3447569 = 2585677) B2585677
theorem B2298379 : Blo 2297435 2298379 := bstep (se 1 (by rfl) ⟨1723784, by rfl⟩ : syracuseStep 2298379 = 3447569) B3447569
theorem B7757045 : Blo 2297435 7757045 := bbase (se 5 (by rfl) ⟨363611, by rfl⟩ : syracuseStep 7757045 = 727223) (by norm_num)
theorem B5171363 : Blo 2297435 5171363 := bstep (se 1 (by rfl) ⟨3878522, by rfl⟩ : syracuseStep 5171363 = 7757045) B7757045
theorem B3447575 : Blo 2297435 3447575 := bstep (se 1 (by rfl) ⟨2585681, by rfl⟩ : syracuseStep 3447575 = 5171363) B5171363
theorem B2298383 : Blo 2297435 2298383 := bstep (se 1 (by rfl) ⟨1723787, by rfl⟩ : syracuseStep 2298383 = 3447575) B3447575
theorem B3447581 : Blo 2297435 3447581 := bbase (se 3 (by rfl) ⟨646421, by rfl⟩ : syracuseStep 3447581 = 1292843) (by norm_num)
theorem B2298387 : Blo 2297435 2298387 := bstep (se 1 (by rfl) ⟨1723790, by rfl⟩ : syracuseStep 2298387 = 3447581) B3447581
theorem B5171381 : Blo 2297435 5171381 := bbase (se 5 (by rfl) ⟨242408, by rfl⟩ : syracuseStep 5171381 = 484817) (by norm_num)
theorem B3447587 : Blo 2297435 3447587 := bstep (se 1 (by rfl) ⟨2585690, by rfl⟩ : syracuseStep 3447587 = 5171381) B5171381
theorem B2298391 : Blo 2297435 2298391 := bstep (se 1 (by rfl) ⟨1723793, by rfl⟩ : syracuseStep 2298391 = 3447587) B3447587
theorem B5522381 : Blo 2297435 5522381 := bbase (se 3 (by rfl) ⟨1035446, by rfl⟩ : syracuseStep 5522381 = 2070893) (by norm_num)
theorem B3681587 : Blo 2297435 3681587 := bstep (se 1 (by rfl) ⟨2761190, by rfl⟩ : syracuseStep 3681587 = 5522381) B5522381
theorem B2454391 : Blo 2297435 2454391 := bstep (se 1 (by rfl) ⟨1840793, by rfl⟩ : syracuseStep 2454391 = 3681587) B3681587
theorem B13090085 : Blo 2297435 13090085 := bstep (se 4 (by rfl) ⟨1227195, by rfl⟩ : syracuseStep 13090085 = 2454391) B2454391
theorem B8726723 : Blo 2297435 8726723 := bstep (se 1 (by rfl) ⟨6545042, by rfl⟩ : syracuseStep 8726723 = 13090085) B13090085
theorem B5817815 : Blo 2297435 5817815 := bstep (se 1 (by rfl) ⟨4363361, by rfl⟩ : syracuseStep 5817815 = 8726723) B8726723
theorem B3878543 : Blo 2297435 3878543 := bstep (se 1 (by rfl) ⟨2908907, by rfl⟩ : syracuseStep 3878543 = 5817815) B5817815
theorem B2585695 : Blo 2297435 2585695 := bstep (se 1 (by rfl) ⟨1939271, by rfl⟩ : syracuseStep 2585695 = 3878543) B3878543
theorem B3447593 : Blo 2297435 3447593 := bstep (se 2 (by rfl) ⟨1292847, by rfl⟩ : syracuseStep 3447593 = 2585695) B2585695
theorem B2298395 : Blo 2297435 2298395 := bstep (se 1 (by rfl) ⟨1723796, by rfl⟩ : syracuseStep 2298395 = 3447593) B3447593
theorem B2393765 : Blo 2297435 2393765 := bbase (se 4 (by rfl) ⟨224415, by rfl⟩ : syracuseStep 2393765 = 448831) (by norm_num)
theorem B102133973 : Blo 2297435 102133973 := bstep (se 7 (by rfl) ⟨1196882, by rfl⟩ : syracuseStep 102133973 = 2393765) B2393765
theorem B272357261 : Blo 2297435 272357261 := bstep (se 3 (by rfl) ⟨51066986, by rfl⟩ : syracuseStep 272357261 = 102133973) B102133973
theorem B181571507 : Blo 2297435 181571507 := bstep (se 1 (by rfl) ⟨136178630, by rfl⟩ : syracuseStep 181571507 = 272357261) B272357261
theorem B121047671 : Blo 2297435 121047671 := bstep (se 1 (by rfl) ⟨90785753, by rfl⟩ : syracuseStep 121047671 = 181571507) B181571507
theorem B80698447 : Blo 2297435 80698447 := bstep (se 1 (by rfl) ⟨60523835, by rfl⟩ : syracuseStep 80698447 = 121047671) B121047671
theorem B107597929 : Blo 2297435 107597929 := bstep (se 2 (by rfl) ⟨40349223, by rfl⟩ : syracuseStep 107597929 = 80698447) B80698447
theorem B143463905 : Blo 2297435 143463905 := bstep (se 2 (by rfl) ⟨53798964, by rfl⟩ : syracuseStep 143463905 = 107597929) B107597929
theorem B95642603 : Blo 2297435 95642603 := bstep (se 1 (by rfl) ⟨71731952, by rfl⟩ : syracuseStep 95642603 = 143463905) B143463905
theorem B63761735 : Blo 2297435 63761735 := bstep (se 1 (by rfl) ⟨47821301, by rfl⟩ : syracuseStep 63761735 = 95642603) B95642603
theorem B42507823 : Blo 2297435 42507823 := bstep (se 1 (by rfl) ⟨31880867, by rfl⟩ : syracuseStep 42507823 = 63761735) B63761735
theorem B56677097 : Blo 2297435 56677097 := bstep (se 2 (by rfl) ⟨21253911, by rfl⟩ : syracuseStep 56677097 = 42507823) B42507823
theorem B37784731 : Blo 2297435 37784731 := bstep (se 1 (by rfl) ⟨28338548, by rfl⟩ : syracuseStep 37784731 = 56677097) B56677097
theorem B50379641 : Blo 2297435 50379641 := bstep (se 2 (by rfl) ⟨18892365, by rfl⟩ : syracuseStep 50379641 = 37784731) B37784731
theorem B33586427 : Blo 2297435 33586427 := bstep (se 1 (by rfl) ⟨25189820, by rfl⟩ : syracuseStep 33586427 = 50379641) B50379641
theorem B22390951 : Blo 2297435 22390951 := bstep (se 1 (by rfl) ⟨16793213, by rfl⟩ : syracuseStep 22390951 = 33586427) B33586427
theorem B29854601 : Blo 2297435 29854601 := bstep (se 2 (by rfl) ⟨11195475, by rfl⟩ : syracuseStep 29854601 = 22390951) B22390951
theorem B19903067 : Blo 2297435 19903067 := bstep (se 1 (by rfl) ⟨14927300, by rfl⟩ : syracuseStep 19903067 = 29854601) B29854601
theorem B13268711 : Blo 2297435 13268711 := bstep (se 1 (by rfl) ⟨9951533, by rfl⟩ : syracuseStep 13268711 = 19903067) B19903067
theorem B8845807 : Blo 2297435 8845807 := bstep (se 1 (by rfl) ⟨6634355, by rfl⟩ : syracuseStep 8845807 = 13268711) B13268711
theorem B11794409 : Blo 2297435 11794409 := bstep (se 2 (by rfl) ⟨4422903, by rfl⟩ : syracuseStep 11794409 = 8845807) B8845807
theorem B7862939 : Blo 2297435 7862939 := bstep (se 1 (by rfl) ⟨5897204, by rfl⟩ : syracuseStep 7862939 = 11794409) B11794409
theorem B5241959 : Blo 2297435 5241959 := bstep (se 1 (by rfl) ⟨3931469, by rfl⟩ : syracuseStep 5241959 = 7862939) B7862939
theorem B3494639 : Blo 2297435 3494639 := bstep (se 1 (by rfl) ⟨2620979, by rfl⟩ : syracuseStep 3494639 = 5241959) B5241959
theorem B2329759 : Blo 2297435 2329759 := bstep (se 1 (by rfl) ⟨1747319, by rfl⟩ : syracuseStep 2329759 = 3494639) B3494639
theorem B3106345 : Blo 2297435 3106345 := bstep (se 2 (by rfl) ⟨1164879, by rfl⟩ : syracuseStep 3106345 = 2329759) B2329759
theorem B4141793 : Blo 2297435 4141793 := bstep (se 2 (by rfl) ⟨1553172, by rfl⟩ : syracuseStep 4141793 = 3106345) B3106345
theorem B2761195 : Blo 2297435 2761195 := bstep (se 1 (by rfl) ⟨2070896, by rfl⟩ : syracuseStep 2761195 = 4141793) B4141793
theorem B3681593 : Blo 2297435 3681593 := bstep (se 2 (by rfl) ⟨1380597, by rfl⟩ : syracuseStep 3681593 = 2761195) B2761195
theorem B2454395 : Blo 2297435 2454395 := bstep (se 1 (by rfl) ⟨1840796, by rfl⟩ : syracuseStep 2454395 = 3681593) B3681593
theorem B6545053 : Blo 2297435 6545053 := bstep (se 3 (by rfl) ⟨1227197, by rfl⟩ : syracuseStep 6545053 = 2454395) B2454395
theorem B8726737 : Blo 2297435 8726737 := bstep (se 2 (by rfl) ⟨3272526, by rfl⟩ : syracuseStep 8726737 = 6545053) B6545053
theorem B11635649 : Blo 2297435 11635649 := bstep (se 2 (by rfl) ⟨4363368, by rfl⟩ : syracuseStep 11635649 = 8726737) B8726737
theorem B7757099 : Blo 2297435 7757099 := bstep (se 1 (by rfl) ⟨5817824, by rfl⟩ : syracuseStep 7757099 = 11635649) B11635649
theorem B5171399 : Blo 2297435 5171399 := bstep (se 1 (by rfl) ⟨3878549, by rfl⟩ : syracuseStep 5171399 = 7757099) B7757099
theorem B3447599 : Blo 2297435 3447599 := bstep (se 1 (by rfl) ⟨2585699, by rfl⟩ : syracuseStep 3447599 = 5171399) B5171399
theorem B2298399 : Blo 2297435 2298399 := bstep (se 1 (by rfl) ⟨1723799, by rfl⟩ : syracuseStep 2298399 = 3447599) B3447599
theorem B3447605 : Blo 2297435 3447605 := bbase (se 5 (by rfl) ⟨161606, by rfl⟩ : syracuseStep 3447605 = 323213) (by norm_num)
theorem B2298403 : Blo 2297435 2298403 := bstep (se 1 (by rfl) ⟨1723802, by rfl⟩ : syracuseStep 2298403 = 3447605) B3447605
theorem B5817845 : Blo 2297435 5817845 := bbase (se 5 (by rfl) ⟨272711, by rfl⟩ : syracuseStep 5817845 = 545423) (by norm_num)
theorem B3878563 : Blo 2297435 3878563 := bstep (se 1 (by rfl) ⟨2908922, by rfl⟩ : syracuseStep 3878563 = 5817845) B5817845
theorem B5171417 : Blo 2297435 5171417 := bstep (se 2 (by rfl) ⟨1939281, by rfl⟩ : syracuseStep 5171417 = 3878563) B3878563
theorem B3447611 : Blo 2297435 3447611 := bstep (se 1 (by rfl) ⟨2585708, by rfl⟩ : syracuseStep 3447611 = 5171417) B5171417
theorem B2298407 : Blo 2297435 2298407 := bstep (se 1 (by rfl) ⟨1723805, by rfl⟩ : syracuseStep 2298407 = 3447611) B3447611
theorem B2585713 : Blo 2297435 2585713 := bbase (se 2 (by rfl) ⟨969642, by rfl⟩ : syracuseStep 2585713 = 1939285) (by norm_num)
theorem B3447617 : Blo 2297435 3447617 := bstep (se 2 (by rfl) ⟨1292856, by rfl⟩ : syracuseStep 3447617 = 2585713) B2585713
theorem B2298411 : Blo 2297435 2298411 := bstep (se 1 (by rfl) ⟨1723808, by rfl⟩ : syracuseStep 2298411 = 3447617) B3447617
theorem B7363237 : Blo 2297435 7363237 := bbase (se 4 (by rfl) ⟨690303, by rfl⟩ : syracuseStep 7363237 = 1380607) (by norm_num)
theorem B9817649 : Blo 2297435 9817649 := bstep (se 2 (by rfl) ⟨3681618, by rfl⟩ : syracuseStep 9817649 = 7363237) B7363237
theorem B6545099 : Blo 2297435 6545099 := bstep (se 1 (by rfl) ⟨4908824, by rfl⟩ : syracuseStep 6545099 = 9817649) B9817649
theorem B4363399 : Blo 2297435 4363399 := bstep (se 1 (by rfl) ⟨3272549, by rfl⟩ : syracuseStep 4363399 = 6545099) B6545099
theorem B5817865 : Blo 2297435 5817865 := bstep (se 2 (by rfl) ⟨2181699, by rfl⟩ : syracuseStep 5817865 = 4363399) B4363399
theorem B7757153 : Blo 2297435 7757153 := bstep (se 2 (by rfl) ⟨2908932, by rfl⟩ : syracuseStep 7757153 = 5817865) B5817865
theorem B5171435 : Blo 2297435 5171435 := bstep (se 1 (by rfl) ⟨3878576, by rfl⟩ : syracuseStep 5171435 = 7757153) B7757153
theorem B3447623 : Blo 2297435 3447623 := bstep (se 1 (by rfl) ⟨2585717, by rfl⟩ : syracuseStep 3447623 = 5171435) B5171435
theorem B2298415 : Blo 2297435 2298415 := bstep (se 1 (by rfl) ⟨1723811, by rfl⟩ : syracuseStep 2298415 = 3447623) B3447623
theorem B3447629 : Blo 2297435 3447629 := bbase (se 3 (by rfl) ⟨646430, by rfl⟩ : syracuseStep 3447629 = 1292861) (by norm_num)
theorem B2298419 : Blo 2297435 2298419 := bstep (se 1 (by rfl) ⟨1723814, by rfl⟩ : syracuseStep 2298419 = 3447629) B3447629
theorem B5171453 : Blo 2297435 5171453 := bbase (se 3 (by rfl) ⟨969647, by rfl⟩ : syracuseStep 5171453 = 1939295) (by norm_num)
theorem B3447635 : Blo 2297435 3447635 := bstep (se 1 (by rfl) ⟨2585726, by rfl⟩ : syracuseStep 3447635 = 5171453) B5171453
theorem B2298423 : Blo 2297435 2298423 := bstep (se 1 (by rfl) ⟨1723817, by rfl⟩ : syracuseStep 2298423 = 3447635) B3447635
theorem B3878597 : Blo 2297435 3878597 := bbase (se 4 (by rfl) ⟨363618, by rfl⟩ : syracuseStep 3878597 = 727237) (by norm_num)
theorem B2585731 : Blo 2297435 2585731 := bstep (se 1 (by rfl) ⟨1939298, by rfl⟩ : syracuseStep 2585731 = 3878597) B3878597
theorem B3447641 : Blo 2297435 3447641 := bstep (se 2 (by rfl) ⟨1292865, by rfl⟩ : syracuseStep 3447641 = 2585731) B2585731
theorem B2298427 : Blo 2297435 2298427 := bstep (se 1 (by rfl) ⟨1723820, by rfl⟩ : syracuseStep 2298427 = 3447641) B3447641
theorem B17453717 : Blo 2297435 17453717 := bbase (se 6 (by rfl) ⟨409071, by rfl⟩ : syracuseStep 17453717 = 818143) (by norm_num)
theorem B11635811 : Blo 2297435 11635811 := bstep (se 1 (by rfl) ⟨8726858, by rfl⟩ : syracuseStep 11635811 = 17453717) B17453717
theorem B7757207 : Blo 2297435 7757207 := bstep (se 1 (by rfl) ⟨5817905, by rfl⟩ : syracuseStep 7757207 = 11635811) B11635811
theorem B5171471 : Blo 2297435 5171471 := bstep (se 1 (by rfl) ⟨3878603, by rfl⟩ : syracuseStep 5171471 = 7757207) B7757207
theorem B3447647 : Blo 2297435 3447647 := bstep (se 1 (by rfl) ⟨2585735, by rfl⟩ : syracuseStep 3447647 = 5171471) B5171471
theorem B2298431 : Blo 2297435 2298431 := bstep (se 1 (by rfl) ⟨1723823, by rfl⟩ : syracuseStep 2298431 = 3447647) B3447647
theorem B3447653 : Blo 2297435 3447653 := bbase (se 4 (by rfl) ⟨323217, by rfl⟩ : syracuseStep 3447653 = 646435) (by norm_num)
theorem B2298435 : Blo 2297435 2298435 := bstep (se 1 (by rfl) ⟨1723826, by rfl⟩ : syracuseStep 2298435 = 3447653) B3447653
theorem B4363445 : Blo 2297435 4363445 := bbase (se 5 (by rfl) ⟨204536, by rfl⟩ : syracuseStep 4363445 = 409073) (by norm_num)
theorem B2908963 : Blo 2297435 2908963 := bstep (se 1 (by rfl) ⟨2181722, by rfl⟩ : syracuseStep 2908963 = 4363445) B4363445
theorem B3878617 : Blo 2297435 3878617 := bstep (se 2 (by rfl) ⟨1454481, by rfl⟩ : syracuseStep 3878617 = 2908963) B2908963
theorem B5171489 : Blo 2297435 5171489 := bstep (se 2 (by rfl) ⟨1939308, by rfl⟩ : syracuseStep 5171489 = 3878617) B3878617
theorem B3447659 : Blo 2297435 3447659 := bstep (se 1 (by rfl) ⟨2585744, by rfl⟩ : syracuseStep 3447659 = 5171489) B5171489
theorem B2298439 : Blo 2297435 2298439 := bstep (se 1 (by rfl) ⟨1723829, by rfl⟩ : syracuseStep 2298439 = 3447659) B3447659
theorem B2585749 : Blo 2297435 2585749 := bbase (se 6 (by rfl) ⟨60603, by rfl⟩ : syracuseStep 2585749 = 121207) (by norm_num)
theorem B3447665 : Blo 2297435 3447665 := bstep (se 2 (by rfl) ⟨1292874, by rfl⟩ : syracuseStep 3447665 = 2585749) B2585749
theorem B2298443 : Blo 2297435 2298443 := bstep (se 1 (by rfl) ⟨1723832, by rfl⟩ : syracuseStep 2298443 = 3447665) B3447665
theorem B2908973 : Blo 2297435 2908973 := bbase (se 3 (by rfl) ⟨545432, by rfl⟩ : syracuseStep 2908973 = 1090865) (by norm_num)
theorem B7757261 : Blo 2297435 7757261 := bstep (se 3 (by rfl) ⟨1454486, by rfl⟩ : syracuseStep 7757261 = 2908973) B2908973
theorem B5171507 : Blo 2297435 5171507 := bstep (se 1 (by rfl) ⟨3878630, by rfl⟩ : syracuseStep 5171507 = 7757261) B7757261
theorem B3447671 : Blo 2297435 3447671 := bstep (se 1 (by rfl) ⟨2585753, by rfl⟩ : syracuseStep 3447671 = 5171507) B5171507
theorem B2298447 : Blo 2297435 2298447 := bstep (se 1 (by rfl) ⟨1723835, by rfl⟩ : syracuseStep 2298447 = 3447671) B3447671
theorem B3447677 : Blo 2297435 3447677 := bbase (se 3 (by rfl) ⟨646439, by rfl⟩ : syracuseStep 3447677 = 1292879) (by norm_num)
theorem B2298451 : Blo 2297435 2298451 := bstep (se 1 (by rfl) ⟨1723838, by rfl⟩ : syracuseStep 2298451 = 3447677) B3447677
theorem B5171525 : Blo 2297435 5171525 := bbase (se 4 (by rfl) ⟨484830, by rfl⟩ : syracuseStep 5171525 = 969661) (by norm_num)
theorem B3447683 : Blo 2297435 3447683 := bstep (se 1 (by rfl) ⟨2585762, by rfl⟩ : syracuseStep 3447683 = 5171525) B5171525
theorem B2298455 : Blo 2297435 2298455 := bstep (se 1 (by rfl) ⟨1723841, by rfl⟩ : syracuseStep 2298455 = 3447683) B3447683
theorem B4141901 : Blo 2297435 4141901 := bbase (se 3 (by rfl) ⟨776606, by rfl⟩ : syracuseStep 4141901 = 1553213) (by norm_num)
theorem B11045069 : Blo 2297435 11045069 := bstep (se 3 (by rfl) ⟨2070950, by rfl⟩ : syracuseStep 11045069 = 4141901) B4141901
theorem B7363379 : Blo 2297435 7363379 := bstep (se 1 (by rfl) ⟨5522534, by rfl⟩ : syracuseStep 7363379 = 11045069) B11045069
theorem B4908919 : Blo 2297435 4908919 := bstep (se 1 (by rfl) ⟨3681689, by rfl⟩ : syracuseStep 4908919 = 7363379) B7363379
theorem B6545225 : Blo 2297435 6545225 := bstep (se 2 (by rfl) ⟨2454459, by rfl⟩ : syracuseStep 6545225 = 4908919) B4908919
theorem B4363483 : Blo 2297435 4363483 := bstep (se 1 (by rfl) ⟨3272612, by rfl⟩ : syracuseStep 4363483 = 6545225) B6545225
theorem B5817977 : Blo 2297435 5817977 := bstep (se 2 (by rfl) ⟨2181741, by rfl⟩ : syracuseStep 5817977 = 4363483) B4363483
theorem B3878651 : Blo 2297435 3878651 := bstep (se 1 (by rfl) ⟨2908988, by rfl⟩ : syracuseStep 3878651 = 5817977) B5817977
theorem B2585767 : Blo 2297435 2585767 := bstep (se 1 (by rfl) ⟨1939325, by rfl⟩ : syracuseStep 2585767 = 3878651) B3878651
theorem B3447689 : Blo 2297435 3447689 := bstep (se 2 (by rfl) ⟨1292883, by rfl⟩ : syracuseStep 3447689 = 2585767) B2585767
theorem B2298459 : Blo 2297435 2298459 := bstep (se 1 (by rfl) ⟨1723844, by rfl⟩ : syracuseStep 2298459 = 3447689) B3447689
theorem B11635973 : Blo 2297435 11635973 := bbase (se 4 (by rfl) ⟨1090872, by rfl⟩ : syracuseStep 11635973 = 2181745) (by norm_num)
theorem B7757315 : Blo 2297435 7757315 := bstep (se 1 (by rfl) ⟨5817986, by rfl⟩ : syracuseStep 7757315 = 11635973) B11635973
theorem B5171543 : Blo 2297435 5171543 := bstep (se 1 (by rfl) ⟨3878657, by rfl⟩ : syracuseStep 5171543 = 7757315) B7757315
theorem B3447695 : Blo 2297435 3447695 := bstep (se 1 (by rfl) ⟨2585771, by rfl⟩ : syracuseStep 3447695 = 5171543) B5171543
theorem B2298463 : Blo 2297435 2298463 := bstep (se 1 (by rfl) ⟨1723847, by rfl⟩ : syracuseStep 2298463 = 3447695) B3447695
theorem B3447701 : Blo 2297435 3447701 := bbase (se 6 (by rfl) ⟨80805, by rfl⟩ : syracuseStep 3447701 = 161611) (by norm_num)
theorem B2298467 : Blo 2297435 2298467 := bstep (se 1 (by rfl) ⟨1723850, by rfl⟩ : syracuseStep 2298467 = 3447701) B3447701
theorem B13090517 : Blo 2297435 13090517 := bbase (se 7 (by rfl) ⟨153404, by rfl⟩ : syracuseStep 13090517 = 306809) (by norm_num)
theorem B8727011 : Blo 2297435 8727011 := bstep (se 1 (by rfl) ⟨6545258, by rfl⟩ : syracuseStep 8727011 = 13090517) B13090517
theorem B5818007 : Blo 2297435 5818007 := bstep (se 1 (by rfl) ⟨4363505, by rfl⟩ : syracuseStep 5818007 = 8727011) B8727011
theorem B3878671 : Blo 2297435 3878671 := bstep (se 1 (by rfl) ⟨2909003, by rfl⟩ : syracuseStep 3878671 = 5818007) B5818007
theorem B5171561 : Blo 2297435 5171561 := bstep (se 2 (by rfl) ⟨1939335, by rfl⟩ : syracuseStep 5171561 = 3878671) B3878671
theorem B3447707 : Blo 2297435 3447707 := bstep (se 1 (by rfl) ⟨2585780, by rfl⟩ : syracuseStep 3447707 = 5171561) B5171561
theorem B2298471 : Blo 2297435 2298471 := bstep (se 1 (by rfl) ⟨1723853, by rfl⟩ : syracuseStep 2298471 = 3447707) B3447707
theorem B2585785 : Blo 2297435 2585785 := bbase (se 2 (by rfl) ⟨969669, by rfl⟩ : syracuseStep 2585785 = 1939339) (by norm_num)
theorem B3447713 : Blo 2297435 3447713 := bstep (se 2 (by rfl) ⟨1292892, by rfl⟩ : syracuseStep 3447713 = 2585785) B2585785
theorem B2298475 : Blo 2297435 2298475 := bstep (se 1 (by rfl) ⟨1723856, by rfl⟩ : syracuseStep 2298475 = 3447713) B3447713
theorem B3106453 : Blo 2297435 3106453 := bbase (se 6 (by rfl) ⟨72807, by rfl⟩ : syracuseStep 3106453 = 145615) (by norm_num)
theorem B4141937 : Blo 2297435 4141937 := bstep (se 2 (by rfl) ⟨1553226, by rfl⟩ : syracuseStep 4141937 = 3106453) B3106453
theorem B2761291 : Blo 2297435 2761291 := bstep (se 1 (by rfl) ⟨2070968, by rfl⟩ : syracuseStep 2761291 = 4141937) B4141937
theorem B3681721 : Blo 2297435 3681721 := bstep (se 2 (by rfl) ⟨1380645, by rfl⟩ : syracuseStep 3681721 = 2761291) B2761291
theorem B4908961 : Blo 2297435 4908961 := bstep (se 2 (by rfl) ⟨1840860, by rfl⟩ : syracuseStep 4908961 = 3681721) B3681721
theorem B6545281 : Blo 2297435 6545281 := bstep (se 2 (by rfl) ⟨2454480, by rfl⟩ : syracuseStep 6545281 = 4908961) B4908961
theorem B8727041 : Blo 2297435 8727041 := bstep (se 2 (by rfl) ⟨3272640, by rfl⟩ : syracuseStep 8727041 = 6545281) B6545281
theorem B5818027 : Blo 2297435 5818027 := bstep (se 1 (by rfl) ⟨4363520, by rfl⟩ : syracuseStep 5818027 = 8727041) B8727041
theorem B7757369 : Blo 2297435 7757369 := bstep (se 2 (by rfl) ⟨2909013, by rfl⟩ : syracuseStep 7757369 = 5818027) B5818027
theorem B5171579 : Blo 2297435 5171579 := bstep (se 1 (by rfl) ⟨3878684, by rfl⟩ : syracuseStep 5171579 = 7757369) B7757369
theorem B3447719 : Blo 2297435 3447719 := bstep (se 1 (by rfl) ⟨2585789, by rfl⟩ : syracuseStep 3447719 = 5171579) B5171579
theorem B2298479 : Blo 2297435 2298479 := bstep (se 1 (by rfl) ⟨1723859, by rfl⟩ : syracuseStep 2298479 = 3447719) B3447719
theorem B3447725 : Blo 2297435 3447725 := bbase (se 3 (by rfl) ⟨646448, by rfl⟩ : syracuseStep 3447725 = 1292897) (by norm_num)
theorem B2298483 : Blo 2297435 2298483 := bstep (se 1 (by rfl) ⟨1723862, by rfl⟩ : syracuseStep 2298483 = 3447725) B3447725
theorem B5171597 : Blo 2297435 5171597 := bbase (se 3 (by rfl) ⟨969674, by rfl⟩ : syracuseStep 5171597 = 1939349) (by norm_num)
theorem B3447731 : Blo 2297435 3447731 := bstep (se 1 (by rfl) ⟨2585798, by rfl⟩ : syracuseStep 3447731 = 5171597) B5171597
theorem B2298487 : Blo 2297435 2298487 := bstep (se 1 (by rfl) ⟨1723865, by rfl⟩ : syracuseStep 2298487 = 3447731) B3447731
theorem B2909029 : Blo 2297435 2909029 := bbase (se 4 (by rfl) ⟨272721, by rfl⟩ : syracuseStep 2909029 = 545443) (by norm_num)
theorem B3878705 : Blo 2297435 3878705 := bstep (se 2 (by rfl) ⟨1454514, by rfl⟩ : syracuseStep 3878705 = 2909029) B2909029
theorem B2585803 : Blo 2297435 2585803 := bstep (se 1 (by rfl) ⟨1939352, by rfl⟩ : syracuseStep 2585803 = 3878705) B3878705
theorem B3447737 : Blo 2297435 3447737 := bstep (se 2 (by rfl) ⟨1292901, by rfl⟩ : syracuseStep 3447737 = 2585803) B2585803
theorem B2298491 : Blo 2297435 2298491 := bstep (se 1 (by rfl) ⟨1723868, by rfl⟩ : syracuseStep 2298491 = 3447737) B3447737
theorem B2656849 : Blo 2297435 2656849 := bbase (se 2 (by rfl) ⟨996318, by rfl⟩ : syracuseStep 2656849 = 1992637) (by norm_num)
theorem B3542465 : Blo 2297435 3542465 := bstep (se 2 (by rfl) ⟨1328424, by rfl⟩ : syracuseStep 3542465 = 2656849) B2656849
theorem B2361643 : Blo 2297435 2361643 := bstep (se 1 (by rfl) ⟨1771232, by rfl⟩ : syracuseStep 2361643 = 3542465) B3542465
theorem B12595429 : Blo 2297435 12595429 := bstep (se 4 (by rfl) ⟨1180821, by rfl⟩ : syracuseStep 12595429 = 2361643) B2361643
theorem B16793905 : Blo 2297435 16793905 := bstep (se 2 (by rfl) ⟨6297714, by rfl⟩ : syracuseStep 16793905 = 12595429) B12595429
theorem B22391873 : Blo 2297435 22391873 := bstep (se 2 (by rfl) ⟨8396952, by rfl⟩ : syracuseStep 22391873 = 16793905) B16793905
theorem B14927915 : Blo 2297435 14927915 := bstep (se 1 (by rfl) ⟨11195936, by rfl⟩ : syracuseStep 14927915 = 22391873) B22391873
theorem B39807773 : Blo 2297435 39807773 := bstep (se 3 (by rfl) ⟨7463957, by rfl⟩ : syracuseStep 39807773 = 14927915) B14927915
theorem B26538515 : Blo 2297435 26538515 := bstep (se 1 (by rfl) ⟨19903886, by rfl⟩ : syracuseStep 26538515 = 39807773) B39807773
theorem B17692343 : Blo 2297435 17692343 := bstep (se 1 (by rfl) ⟨13269257, by rfl⟩ : syracuseStep 17692343 = 26538515) B26538515
theorem B11794895 : Blo 2297435 11794895 := bstep (se 1 (by rfl) ⟨8846171, by rfl⟩ : syracuseStep 11794895 = 17692343) B17692343
theorem B7863263 : Blo 2297435 7863263 := bstep (se 1 (by rfl) ⟨5897447, by rfl⟩ : syracuseStep 7863263 = 11794895) B11794895
theorem B5242175 : Blo 2297435 5242175 := bstep (se 1 (by rfl) ⟨3931631, by rfl⟩ : syracuseStep 5242175 = 7863263) B7863263
theorem B3494783 : Blo 2297435 3494783 := bstep (se 1 (by rfl) ⟨2621087, by rfl⟩ : syracuseStep 3494783 = 5242175) B5242175
theorem B9319421 : Blo 2297435 9319421 := bstep (se 3 (by rfl) ⟨1747391, by rfl⟩ : syracuseStep 9319421 = 3494783) B3494783
theorem B6212947 : Blo 2297435 6212947 := bstep (se 1 (by rfl) ⟨4659710, by rfl⟩ : syracuseStep 6212947 = 9319421) B9319421
theorem B8283929 : Blo 2297435 8283929 := bstep (se 2 (by rfl) ⟨3106473, by rfl⟩ : syracuseStep 8283929 = 6212947) B6212947
theorem B22090477 : Blo 2297435 22090477 := bstep (se 3 (by rfl) ⟨4141964, by rfl⟩ : syracuseStep 22090477 = 8283929) B8283929
theorem B29453969 : Blo 2297435 29453969 := bstep (se 2 (by rfl) ⟨11045238, by rfl⟩ : syracuseStep 29453969 = 22090477) B22090477
theorem B19635979 : Blo 2297435 19635979 := bstep (se 1 (by rfl) ⟨14726984, by rfl⟩ : syracuseStep 19635979 = 29453969) B29453969
theorem B26181305 : Blo 2297435 26181305 := bstep (se 2 (by rfl) ⟨9817989, by rfl⟩ : syracuseStep 26181305 = 19635979) B19635979
theorem B17454203 : Blo 2297435 17454203 := bstep (se 1 (by rfl) ⟨13090652, by rfl⟩ : syracuseStep 17454203 = 26181305) B26181305
theorem B11636135 : Blo 2297435 11636135 := bstep (se 1 (by rfl) ⟨8727101, by rfl⟩ : syracuseStep 11636135 = 17454203) B17454203
theorem B7757423 : Blo 2297435 7757423 := bstep (se 1 (by rfl) ⟨5818067, by rfl⟩ : syracuseStep 7757423 = 11636135) B11636135
theorem B5171615 : Blo 2297435 5171615 := bstep (se 1 (by rfl) ⟨3878711, by rfl⟩ : syracuseStep 5171615 = 7757423) B7757423
theorem B3447743 : Blo 2297435 3447743 := bstep (se 1 (by rfl) ⟨2585807, by rfl⟩ : syracuseStep 3447743 = 5171615) B5171615
theorem B2298495 : Blo 2297435 2298495 := bstep (se 1 (by rfl) ⟨1723871, by rfl⟩ : syracuseStep 2298495 = 3447743) B3447743
theorem B3447749 : Blo 2297435 3447749 := bbase (se 4 (by rfl) ⟨323226, by rfl⟩ : syracuseStep 3447749 = 646453) (by norm_num)
theorem B2298499 : Blo 2297435 2298499 := bstep (se 1 (by rfl) ⟨1723874, by rfl⟩ : syracuseStep 2298499 = 3447749) B3447749
theorem B3878725 : Blo 2297435 3878725 := bbase (se 4 (by rfl) ⟨363630, by rfl⟩ : syracuseStep 3878725 = 727261) (by norm_num)
theorem B5171633 : Blo 2297435 5171633 := bstep (se 2 (by rfl) ⟨1939362, by rfl⟩ : syracuseStep 5171633 = 3878725) B3878725
theorem B3447755 : Blo 2297435 3447755 := bstep (se 1 (by rfl) ⟨2585816, by rfl⟩ : syracuseStep 3447755 = 5171633) B5171633
theorem B2298503 : Blo 2297435 2298503 := bstep (se 1 (by rfl) ⟨1723877, by rfl⟩ : syracuseStep 2298503 = 3447755) B3447755
theorem B2585821 : Blo 2297435 2585821 := bbase (se 3 (by rfl) ⟨484841, by rfl⟩ : syracuseStep 2585821 = 969683) (by norm_num)
theorem B3447761 : Blo 2297435 3447761 := bstep (se 2 (by rfl) ⟨1292910, by rfl⟩ : syracuseStep 3447761 = 2585821) B2585821
theorem B2298507 : Blo 2297435 2298507 := bstep (se 1 (by rfl) ⟨1723880, by rfl⟩ : syracuseStep 2298507 = 3447761) B3447761
theorem B7757477 : Blo 2297435 7757477 := bbase (se 4 (by rfl) ⟨727263, by rfl⟩ : syracuseStep 7757477 = 1454527) (by norm_num)
theorem B5171651 : Blo 2297435 5171651 := bstep (se 1 (by rfl) ⟨3878738, by rfl⟩ : syracuseStep 5171651 = 7757477) B7757477
theorem B3447767 : Blo 2297435 3447767 := bstep (se 1 (by rfl) ⟨2585825, by rfl⟩ : syracuseStep 3447767 = 5171651) B5171651
theorem B2298511 : Blo 2297435 2298511 := bstep (se 1 (by rfl) ⟨1723883, by rfl⟩ : syracuseStep 2298511 = 3447767) B3447767
theorem B3447773 : Blo 2297435 3447773 := bbase (se 3 (by rfl) ⟨646457, by rfl⟩ : syracuseStep 3447773 = 1292915) (by norm_num)
theorem B2298515 : Blo 2297435 2298515 := bstep (se 1 (by rfl) ⟨1723886, by rfl⟩ : syracuseStep 2298515 = 3447773) B3447773
theorem B5171669 : Blo 2297435 5171669 := bbase (se 7 (by rfl) ⟨60605, by rfl⟩ : syracuseStep 5171669 = 121211) (by norm_num)
theorem B3447779 : Blo 2297435 3447779 := bstep (se 1 (by rfl) ⟨2585834, by rfl⟩ : syracuseStep 3447779 = 5171669) B5171669
theorem B2298519 : Blo 2297435 2298519 := bstep (se 1 (by rfl) ⟨1723889, by rfl⟩ : syracuseStep 2298519 = 3447779) B3447779
theorem B5977981 : Blo 2297435 5977981 := bbase (se 3 (by rfl) ⟨1120871, by rfl⟩ : syracuseStep 5977981 = 2241743) (by norm_num)
theorem B31882565 : Blo 2297435 31882565 := bstep (se 4 (by rfl) ⟨2988990, by rfl⟩ : syracuseStep 31882565 = 5977981) B5977981
theorem B21255043 : Blo 2297435 21255043 := bstep (se 1 (by rfl) ⟨15941282, by rfl⟩ : syracuseStep 21255043 = 31882565) B31882565
theorem B28340057 : Blo 2297435 28340057 := bstep (se 2 (by rfl) ⟨10627521, by rfl⟩ : syracuseStep 28340057 = 21255043) B21255043
theorem B18893371 : Blo 2297435 18893371 := bstep (se 1 (by rfl) ⟨14170028, by rfl⟩ : syracuseStep 18893371 = 28340057) B28340057
theorem B25191161 : Blo 2297435 25191161 := bstep (se 2 (by rfl) ⟨9446685, by rfl⟩ : syracuseStep 25191161 = 18893371) B18893371
theorem B16794107 : Blo 2297435 16794107 := bstep (se 1 (by rfl) ⟨12595580, by rfl⟩ : syracuseStep 16794107 = 25191161) B25191161
theorem B11196071 : Blo 2297435 11196071 := bstep (se 1 (by rfl) ⟨8397053, by rfl⟩ : syracuseStep 11196071 = 16794107) B16794107
theorem B477699029 : Blo 2297435 477699029 := bstep (se 7 (by rfl) ⟨5598035, by rfl⟩ : syracuseStep 477699029 = 11196071) B11196071
theorem B318466019 : Blo 2297435 318466019 := bstep (se 1 (by rfl) ⟨238849514, by rfl⟩ : syracuseStep 318466019 = 477699029) B477699029
theorem B849242717 : Blo 2297435 849242717 := bstep (se 3 (by rfl) ⟨159233009, by rfl⟩ : syracuseStep 849242717 = 318466019) B318466019
theorem B566161811 : Blo 2297435 566161811 := bstep (se 1 (by rfl) ⟨424621358, by rfl⟩ : syracuseStep 566161811 = 849242717) B849242717
theorem B377441207 : Blo 2297435 377441207 := bstep (se 1 (by rfl) ⟨283080905, by rfl⟩ : syracuseStep 377441207 = 566161811) B566161811
theorem B251627471 : Blo 2297435 251627471 := bstep (se 1 (by rfl) ⟨188720603, by rfl⟩ : syracuseStep 251627471 = 377441207) B377441207
theorem B167751647 : Blo 2297435 167751647 := bstep (se 1 (by rfl) ⟨125813735, by rfl⟩ : syracuseStep 167751647 = 251627471) B251627471
theorem B111834431 : Blo 2297435 111834431 := bstep (se 1 (by rfl) ⟨83875823, by rfl⟩ : syracuseStep 111834431 = 167751647) B167751647
theorem B74556287 : Blo 2297435 74556287 := bstep (se 1 (by rfl) ⟨55917215, by rfl⟩ : syracuseStep 74556287 = 111834431) B111834431
theorem B49704191 : Blo 2297435 49704191 := bstep (se 1 (by rfl) ⟨37278143, by rfl⟩ : syracuseStep 49704191 = 74556287) B74556287
theorem B33136127 : Blo 2297435 33136127 := bstep (se 1 (by rfl) ⟨24852095, by rfl⟩ : syracuseStep 33136127 = 49704191) B49704191
theorem B22090751 : Blo 2297435 22090751 := bstep (se 1 (by rfl) ⟨16568063, by rfl⟩ : syracuseStep 22090751 = 33136127) B33136127
theorem B14727167 : Blo 2297435 14727167 := bstep (se 1 (by rfl) ⟨11045375, by rfl⟩ : syracuseStep 14727167 = 22090751) B22090751
theorem B9818111 : Blo 2297435 9818111 := bstep (se 1 (by rfl) ⟨7363583, by rfl⟩ : syracuseStep 9818111 = 14727167) B14727167
theorem B6545407 : Blo 2297435 6545407 := bstep (se 1 (by rfl) ⟨4909055, by rfl⟩ : syracuseStep 6545407 = 9818111) B9818111
theorem B8727209 : Blo 2297435 8727209 := bstep (se 2 (by rfl) ⟨3272703, by rfl⟩ : syracuseStep 8727209 = 6545407) B6545407
theorem B5818139 : Blo 2297435 5818139 := bstep (se 1 (by rfl) ⟨4363604, by rfl⟩ : syracuseStep 5818139 = 8727209) B8727209
theorem B3878759 : Blo 2297435 3878759 := bstep (se 1 (by rfl) ⟨2909069, by rfl⟩ : syracuseStep 3878759 = 5818139) B5818139
theorem B2585839 : Blo 2297435 2585839 := bstep (se 1 (by rfl) ⟨1939379, by rfl⟩ : syracuseStep 2585839 = 3878759) B3878759
theorem B3447785 : Blo 2297435 3447785 := bstep (se 2 (by rfl) ⟨1292919, by rfl⟩ : syracuseStep 3447785 = 2585839) B2585839
theorem B2298523 : Blo 2297435 2298523 := bstep (se 1 (by rfl) ⟨1723892, by rfl⟩ : syracuseStep 2298523 = 3447785) B3447785
theorem B3106517 : Blo 2297435 3106517 := bbase (se 7 (by rfl) ⟨36404, by rfl⟩ : syracuseStep 3106517 = 72809) (by norm_num)
theorem B8284045 : Blo 2297435 8284045 := bstep (se 3 (by rfl) ⟨1553258, by rfl⟩ : syracuseStep 8284045 = 3106517) B3106517
theorem B11045393 : Blo 2297435 11045393 := bstep (se 2 (by rfl) ⟨4142022, by rfl⟩ : syracuseStep 11045393 = 8284045) B8284045
theorem B7363595 : Blo 2297435 7363595 := bstep (se 1 (by rfl) ⟨5522696, by rfl⟩ : syracuseStep 7363595 = 11045393) B11045393
theorem B19636253 : Blo 2297435 19636253 := bstep (se 3 (by rfl) ⟨3681797, by rfl⟩ : syracuseStep 19636253 = 7363595) B7363595
theorem B13090835 : Blo 2297435 13090835 := bstep (se 1 (by rfl) ⟨9818126, by rfl⟩ : syracuseStep 13090835 = 19636253) B19636253
theorem B8727223 : Blo 2297435 8727223 := bstep (se 1 (by rfl) ⟨6545417, by rfl⟩ : syracuseStep 8727223 = 13090835) B13090835
theorem B11636297 : Blo 2297435 11636297 := bstep (se 2 (by rfl) ⟨4363611, by rfl⟩ : syracuseStep 11636297 = 8727223) B8727223
theorem B7757531 : Blo 2297435 7757531 := bstep (se 1 (by rfl) ⟨5818148, by rfl⟩ : syracuseStep 7757531 = 11636297) B11636297
theorem B5171687 : Blo 2297435 5171687 := bstep (se 1 (by rfl) ⟨3878765, by rfl⟩ : syracuseStep 5171687 = 7757531) B7757531
theorem B3447791 : Blo 2297435 3447791 := bstep (se 1 (by rfl) ⟨2585843, by rfl⟩ : syracuseStep 3447791 = 5171687) B5171687
theorem B2298527 : Blo 2297435 2298527 := bstep (se 1 (by rfl) ⟨1723895, by rfl⟩ : syracuseStep 2298527 = 3447791) B3447791
theorem B3447797 : Blo 2297435 3447797 := bbase (se 5 (by rfl) ⟨161615, by rfl⟩ : syracuseStep 3447797 = 323231) (by norm_num)
theorem B2298531 : Blo 2297435 2298531 := bstep (se 1 (by rfl) ⟨1723898, by rfl⟩ : syracuseStep 2298531 = 3447797) B3447797
theorem B5522717 : Blo 2297435 5522717 := bbase (se 3 (by rfl) ⟨1035509, by rfl⟩ : syracuseStep 5522717 = 2071019) (by norm_num)
theorem B3681811 : Blo 2297435 3681811 := bstep (se 1 (by rfl) ⟨2761358, by rfl⟩ : syracuseStep 3681811 = 5522717) B5522717
theorem B4909081 : Blo 2297435 4909081 := bstep (se 2 (by rfl) ⟨1840905, by rfl⟩ : syracuseStep 4909081 = 3681811) B3681811
theorem B6545441 : Blo 2297435 6545441 := bstep (se 2 (by rfl) ⟨2454540, by rfl⟩ : syracuseStep 6545441 = 4909081) B4909081
theorem B4363627 : Blo 2297435 4363627 := bstep (se 1 (by rfl) ⟨3272720, by rfl⟩ : syracuseStep 4363627 = 6545441) B6545441
theorem B5818169 : Blo 2297435 5818169 := bstep (se 2 (by rfl) ⟨2181813, by rfl⟩ : syracuseStep 5818169 = 4363627) B4363627
theorem B3878779 : Blo 2297435 3878779 := bstep (se 1 (by rfl) ⟨2909084, by rfl⟩ : syracuseStep 3878779 = 5818169) B5818169
theorem B5171705 : Blo 2297435 5171705 := bstep (se 2 (by rfl) ⟨1939389, by rfl⟩ : syracuseStep 5171705 = 3878779) B3878779
theorem B3447803 : Blo 2297435 3447803 := bstep (se 1 (by rfl) ⟨2585852, by rfl⟩ : syracuseStep 3447803 = 5171705) B5171705
theorem B2298535 : Blo 2297435 2298535 := bstep (se 1 (by rfl) ⟨1723901, by rfl⟩ : syracuseStep 2298535 = 3447803) B3447803
theorem B2585857 : Blo 2297435 2585857 := bbase (se 2 (by rfl) ⟨969696, by rfl⟩ : syracuseStep 2585857 = 1939393) (by norm_num)
theorem B3447809 : Blo 2297435 3447809 := bstep (se 2 (by rfl) ⟨1292928, by rfl⟩ : syracuseStep 3447809 = 2585857) B2585857
theorem B2298539 : Blo 2297435 2298539 := bstep (se 1 (by rfl) ⟨1723904, by rfl⟩ : syracuseStep 2298539 = 3447809) B3447809
theorem B5818189 : Blo 2297435 5818189 := bbase (se 3 (by rfl) ⟨1090910, by rfl⟩ : syracuseStep 5818189 = 2181821) (by norm_num)
theorem B7757585 : Blo 2297435 7757585 := bstep (se 2 (by rfl) ⟨2909094, by rfl⟩ : syracuseStep 7757585 = 5818189) B5818189
theorem B5171723 : Blo 2297435 5171723 := bstep (se 1 (by rfl) ⟨3878792, by rfl⟩ : syracuseStep 5171723 = 7757585) B7757585
theorem B3447815 : Blo 2297435 3447815 := bstep (se 1 (by rfl) ⟨2585861, by rfl⟩ : syracuseStep 3447815 = 5171723) B5171723
theorem B2298543 : Blo 2297435 2298543 := bstep (se 1 (by rfl) ⟨1723907, by rfl⟩ : syracuseStep 2298543 = 3447815) B3447815
theorem B3447821 : Blo 2297435 3447821 := bbase (se 3 (by rfl) ⟨646466, by rfl⟩ : syracuseStep 3447821 = 1292933) (by norm_num)
theorem B2298547 : Blo 2297435 2298547 := bstep (se 1 (by rfl) ⟨1723910, by rfl⟩ : syracuseStep 2298547 = 3447821) B3447821
theorem B5171741 : Blo 2297435 5171741 := bbase (se 3 (by rfl) ⟨969701, by rfl⟩ : syracuseStep 5171741 = 1939403) (by norm_num)
theorem B3447827 : Blo 2297435 3447827 := bstep (se 1 (by rfl) ⟨2585870, by rfl⟩ : syracuseStep 3447827 = 5171741) B5171741
theorem B2298551 : Blo 2297435 2298551 := bstep (se 1 (by rfl) ⟨1723913, by rfl⟩ : syracuseStep 2298551 = 3447827) B3447827
theorem B3878813 : Blo 2297435 3878813 := bbase (se 3 (by rfl) ⟨727277, by rfl⟩ : syracuseStep 3878813 = 1454555) (by norm_num)
theorem B2585875 : Blo 2297435 2585875 := bstep (se 1 (by rfl) ⟨1939406, by rfl⟩ : syracuseStep 2585875 = 3878813) B3878813
theorem B3447833 : Blo 2297435 3447833 := bstep (se 2 (by rfl) ⟨1292937, by rfl⟩ : syracuseStep 3447833 = 2585875) B2585875
theorem B2298555 : Blo 2297435 2298555 := bstep (se 1 (by rfl) ⟨1723916, by rfl⟩ : syracuseStep 2298555 = 3447833) B3447833
theorem B22091093 : Blo 2297435 22091093 := bbase (se 14 (by rfl) ⟨2022, by rfl⟩ : syracuseStep 22091093 = 4045) (by norm_num)
theorem B14727395 : Blo 2297435 14727395 := bstep (se 1 (by rfl) ⟨11045546, by rfl⟩ : syracuseStep 14727395 = 22091093) B22091093
theorem B9818263 : Blo 2297435 9818263 := bstep (se 1 (by rfl) ⟨7363697, by rfl⟩ : syracuseStep 9818263 = 14727395) B14727395
theorem B13091017 : Blo 2297435 13091017 := bstep (se 2 (by rfl) ⟨4909131, by rfl⟩ : syracuseStep 13091017 = 9818263) B9818263
theorem B17454689 : Blo 2297435 17454689 := bstep (se 2 (by rfl) ⟨6545508, by rfl⟩ : syracuseStep 17454689 = 13091017) B13091017
theorem B11636459 : Blo 2297435 11636459 := bstep (se 1 (by rfl) ⟨8727344, by rfl⟩ : syracuseStep 11636459 = 17454689) B17454689
theorem B7757639 : Blo 2297435 7757639 := bstep (se 1 (by rfl) ⟨5818229, by rfl⟩ : syracuseStep 7757639 = 11636459) B11636459
theorem B5171759 : Blo 2297435 5171759 := bstep (se 1 (by rfl) ⟨3878819, by rfl⟩ : syracuseStep 5171759 = 7757639) B7757639
theorem B3447839 : Blo 2297435 3447839 := bstep (se 1 (by rfl) ⟨2585879, by rfl⟩ : syracuseStep 3447839 = 5171759) B5171759
theorem B2298559 : Blo 2297435 2298559 := bstep (se 1 (by rfl) ⟨1723919, by rfl⟩ : syracuseStep 2298559 = 3447839) B3447839
theorem B3447845 : Blo 2297435 3447845 := bbase (se 4 (by rfl) ⟨323235, by rfl⟩ : syracuseStep 3447845 = 646471) (by norm_num)
theorem B2298563 : Blo 2297435 2298563 := bstep (se 1 (by rfl) ⟨1723922, by rfl⟩ : syracuseStep 2298563 = 3447845) B3447845
theorem B2909125 : Blo 2297435 2909125 := bbase (se 4 (by rfl) ⟨272730, by rfl⟩ : syracuseStep 2909125 = 545461) (by norm_num)
theorem B3878833 : Blo 2297435 3878833 := bstep (se 2 (by rfl) ⟨1454562, by rfl⟩ : syracuseStep 3878833 = 2909125) B2909125
theorem B5171777 : Blo 2297435 5171777 := bstep (se 2 (by rfl) ⟨1939416, by rfl⟩ : syracuseStep 5171777 = 3878833) B3878833
theorem B3447851 : Blo 2297435 3447851 := bstep (se 1 (by rfl) ⟨2585888, by rfl⟩ : syracuseStep 3447851 = 5171777) B5171777
theorem B2298567 : Blo 2297435 2298567 := bstep (se 1 (by rfl) ⟨1723925, by rfl⟩ : syracuseStep 2298567 = 3447851) B3447851
theorem B2585893 : Blo 2297435 2585893 := bbase (se 4 (by rfl) ⟨242427, by rfl⟩ : syracuseStep 2585893 = 484855) (by norm_num)
theorem B3447857 : Blo 2297435 3447857 := bstep (se 2 (by rfl) ⟨1292946, by rfl⟩ : syracuseStep 3447857 = 2585893) B2585893
theorem B2298571 : Blo 2297435 2298571 := bstep (se 1 (by rfl) ⟨1723928, by rfl⟩ : syracuseStep 2298571 = 3447857) B3447857
theorem B5522813 : Blo 2297435 5522813 := bbase (se 3 (by rfl) ⟨1035527, by rfl⟩ : syracuseStep 5522813 = 2071055) (by norm_num)
theorem B3681875 : Blo 2297435 3681875 := bstep (se 1 (by rfl) ⟨2761406, by rfl⟩ : syracuseStep 3681875 = 5522813) B5522813
theorem B9818333 : Blo 2297435 9818333 := bstep (se 3 (by rfl) ⟨1840937, by rfl⟩ : syracuseStep 9818333 = 3681875) B3681875
theorem B6545555 : Blo 2297435 6545555 := bstep (se 1 (by rfl) ⟨4909166, by rfl⟩ : syracuseStep 6545555 = 9818333) B9818333
theorem B4363703 : Blo 2297435 4363703 := bstep (se 1 (by rfl) ⟨3272777, by rfl⟩ : syracuseStep 4363703 = 6545555) B6545555
theorem B2909135 : Blo 2297435 2909135 := bstep (se 1 (by rfl) ⟨2181851, by rfl⟩ : syracuseStep 2909135 = 4363703) B4363703
theorem B7757693 : Blo 2297435 7757693 := bstep (se 3 (by rfl) ⟨1454567, by rfl⟩ : syracuseStep 7757693 = 2909135) B2909135
theorem B5171795 : Blo 2297435 5171795 := bstep (se 1 (by rfl) ⟨3878846, by rfl⟩ : syracuseStep 5171795 = 7757693) B7757693
theorem B3447863 : Blo 2297435 3447863 := bstep (se 1 (by rfl) ⟨2585897, by rfl⟩ : syracuseStep 3447863 = 5171795) B5171795
theorem B2298575 : Blo 2297435 2298575 := bstep (se 1 (by rfl) ⟨1723931, by rfl⟩ : syracuseStep 2298575 = 3447863) B3447863
theorem B3447869 : Blo 2297435 3447869 := bbase (se 3 (by rfl) ⟨646475, by rfl⟩ : syracuseStep 3447869 = 1292951) (by norm_num)
theorem B2298579 : Blo 2297435 2298579 := bstep (se 1 (by rfl) ⟨1723934, by rfl⟩ : syracuseStep 2298579 = 3447869) B3447869
theorem B5171813 : Blo 2297435 5171813 := bbase (se 4 (by rfl) ⟨484857, by rfl⟩ : syracuseStep 5171813 = 969715) (by norm_num)
theorem B3447875 : Blo 2297435 3447875 := bstep (se 1 (by rfl) ⟨2585906, by rfl⟩ : syracuseStep 3447875 = 5171813) B5171813
theorem B2298583 : Blo 2297435 2298583 := bstep (se 1 (by rfl) ⟨1723937, by rfl⟩ : syracuseStep 2298583 = 3447875) B3447875
theorem B5818301 : Blo 2297435 5818301 := bbase (se 3 (by rfl) ⟨1090931, by rfl⟩ : syracuseStep 5818301 = 2181863) (by norm_num)
theorem B3878867 : Blo 2297435 3878867 := bstep (se 1 (by rfl) ⟨2909150, by rfl⟩ : syracuseStep 3878867 = 5818301) B5818301
theorem B2585911 : Blo 2297435 2585911 := bstep (se 1 (by rfl) ⟨1939433, by rfl⟩ : syracuseStep 2585911 = 3878867) B3878867
theorem B3447881 : Blo 2297435 3447881 := bstep (se 2 (by rfl) ⟨1292955, by rfl⟩ : syracuseStep 3447881 = 2585911) B2585911
theorem B2298587 : Blo 2297435 2298587 := bstep (se 1 (by rfl) ⟨1723940, by rfl⟩ : syracuseStep 2298587 = 3447881) B3447881
theorem B4363733 : Blo 2297435 4363733 := bbase (se 7 (by rfl) ⟨51137, by rfl⟩ : syracuseStep 4363733 = 102275) (by norm_num)
theorem B11636621 : Blo 2297435 11636621 := bstep (se 3 (by rfl) ⟨2181866, by rfl⟩ : syracuseStep 11636621 = 4363733) B4363733
theorem B7757747 : Blo 2297435 7757747 := bstep (se 1 (by rfl) ⟨5818310, by rfl⟩ : syracuseStep 7757747 = 11636621) B11636621
theorem B5171831 : Blo 2297435 5171831 := bstep (se 1 (by rfl) ⟨3878873, by rfl⟩ : syracuseStep 5171831 = 7757747) B7757747
theorem B3447887 : Blo 2297435 3447887 := bstep (se 1 (by rfl) ⟨2585915, by rfl⟩ : syracuseStep 3447887 = 5171831) B5171831
theorem B2298591 : Blo 2297435 2298591 := bstep (se 1 (by rfl) ⟨1723943, by rfl⟩ : syracuseStep 2298591 = 3447887) B3447887
theorem B3447893 : Blo 2297435 3447893 := bbase (se 8 (by rfl) ⟨20202, by rfl⟩ : syracuseStep 3447893 = 40405) (by norm_num)
theorem B2298595 : Blo 2297435 2298595 := bstep (se 1 (by rfl) ⟨1723946, by rfl⟩ : syracuseStep 2298595 = 3447893) B3447893
theorem B5897717 : Blo 2297435 5897717 := bbase (se 5 (by rfl) ⟨276455, by rfl⟩ : syracuseStep 5897717 = 552911) (by norm_num)
theorem B3931811 : Blo 2297435 3931811 := bstep (se 1 (by rfl) ⟨2948858, by rfl⟩ : syracuseStep 3931811 = 5897717) B5897717
theorem B2621207 : Blo 2297435 2621207 := bstep (se 1 (by rfl) ⟨1965905, by rfl⟩ : syracuseStep 2621207 = 3931811) B3931811
theorem B6989885 : Blo 2297435 6989885 := bstep (se 3 (by rfl) ⟨1310603, by rfl⟩ : syracuseStep 6989885 = 2621207) B2621207
theorem B4659923 : Blo 2297435 4659923 := bstep (se 1 (by rfl) ⟨3494942, by rfl⟩ : syracuseStep 4659923 = 6989885) B6989885
theorem B3106615 : Blo 2297435 3106615 := bstep (se 1 (by rfl) ⟨2329961, by rfl⟩ : syracuseStep 3106615 = 4659923) B4659923
theorem B4142153 : Blo 2297435 4142153 := bstep (se 2 (by rfl) ⟨1553307, by rfl⟩ : syracuseStep 4142153 = 3106615) B3106615
theorem B2761435 : Blo 2297435 2761435 := bstep (se 1 (by rfl) ⟨2071076, by rfl⟩ : syracuseStep 2761435 = 4142153) B4142153
theorem B14727653 : Blo 2297435 14727653 := bstep (se 4 (by rfl) ⟨1380717, by rfl⟩ : syracuseStep 14727653 = 2761435) B2761435
theorem B9818435 : Blo 2297435 9818435 := bstep (se 1 (by rfl) ⟨7363826, by rfl⟩ : syracuseStep 9818435 = 14727653) B14727653
theorem B6545623 : Blo 2297435 6545623 := bstep (se 1 (by rfl) ⟨4909217, by rfl⟩ : syracuseStep 6545623 = 9818435) B9818435
theorem B8727497 : Blo 2297435 8727497 := bstep (se 2 (by rfl) ⟨3272811, by rfl⟩ : syracuseStep 8727497 = 6545623) B6545623
theorem B5818331 : Blo 2297435 5818331 := bstep (se 1 (by rfl) ⟨4363748, by rfl⟩ : syracuseStep 5818331 = 8727497) B8727497
theorem B3878887 : Blo 2297435 3878887 := bstep (se 1 (by rfl) ⟨2909165, by rfl⟩ : syracuseStep 3878887 = 5818331) B5818331
theorem B5171849 : Blo 2297435 5171849 := bstep (se 2 (by rfl) ⟨1939443, by rfl⟩ : syracuseStep 5171849 = 3878887) B3878887
theorem B3447899 : Blo 2297435 3447899 := bstep (se 1 (by rfl) ⟨2585924, by rfl⟩ : syracuseStep 3447899 = 5171849) B5171849
theorem B2298599 : Blo 2297435 2298599 := bstep (se 1 (by rfl) ⟨1723949, by rfl⟩ : syracuseStep 2298599 = 3447899) B3447899
theorem B2585929 : Blo 2297435 2585929 := bbase (se 2 (by rfl) ⟨969723, by rfl⟩ : syracuseStep 2585929 = 1939447) (by norm_num)
theorem B3447905 : Blo 2297435 3447905 := bstep (se 2 (by rfl) ⟨1292964, by rfl⟩ : syracuseStep 3447905 = 2585929) B2585929
theorem B2298603 : Blo 2297435 2298603 := bstep (se 1 (by rfl) ⟨1723952, by rfl⟩ : syracuseStep 2298603 = 3447905) B3447905
theorem B2329969 : Blo 2297435 2329969 := bbase (se 2 (by rfl) ⟨873738, by rfl⟩ : syracuseStep 2329969 = 1747477) (by norm_num)
theorem B3106625 : Blo 2297435 3106625 := bstep (se 2 (by rfl) ⟨1164984, by rfl⟩ : syracuseStep 3106625 = 2329969) B2329969
theorem B33137333 : Blo 2297435 33137333 := bstep (se 5 (by rfl) ⟨1553312, by rfl⟩ : syracuseStep 33137333 = 3106625) B3106625
theorem B22091555 : Blo 2297435 22091555 := bstep (se 1 (by rfl) ⟨16568666, by rfl⟩ : syracuseStep 22091555 = 33137333) B33137333
theorem B14727703 : Blo 2297435 14727703 := bstep (se 1 (by rfl) ⟨11045777, by rfl⟩ : syracuseStep 14727703 = 22091555) B22091555
theorem B19636937 : Blo 2297435 19636937 := bstep (se 2 (by rfl) ⟨7363851, by rfl⟩ : syracuseStep 19636937 = 14727703) B14727703
theorem B13091291 : Blo 2297435 13091291 := bstep (se 1 (by rfl) ⟨9818468, by rfl⟩ : syracuseStep 13091291 = 19636937) B19636937
theorem B8727527 : Blo 2297435 8727527 := bstep (se 1 (by rfl) ⟨6545645, by rfl⟩ : syracuseStep 8727527 = 13091291) B13091291
theorem B5818351 : Blo 2297435 5818351 := bstep (se 1 (by rfl) ⟨4363763, by rfl⟩ : syracuseStep 5818351 = 8727527) B8727527
theorem B7757801 : Blo 2297435 7757801 := bstep (se 2 (by rfl) ⟨2909175, by rfl⟩ : syracuseStep 7757801 = 5818351) B5818351
theorem B5171867 : Blo 2297435 5171867 := bstep (se 1 (by rfl) ⟨3878900, by rfl⟩ : syracuseStep 5171867 = 7757801) B7757801
theorem B3447911 : Blo 2297435 3447911 := bstep (se 1 (by rfl) ⟨2585933, by rfl⟩ : syracuseStep 3447911 = 5171867) B5171867
theorem B2298607 : Blo 2297435 2298607 := bstep (se 1 (by rfl) ⟨1723955, by rfl⟩ : syracuseStep 2298607 = 3447911) B3447911
theorem B3447917 : Blo 2297435 3447917 := bbase (se 3 (by rfl) ⟨646484, by rfl⟩ : syracuseStep 3447917 = 1292969) (by norm_num)
theorem B2298611 : Blo 2297435 2298611 := bstep (se 1 (by rfl) ⟨1723958, by rfl⟩ : syracuseStep 2298611 = 3447917) B3447917
theorem B5171885 : Blo 2297435 5171885 := bbase (se 3 (by rfl) ⟨969728, by rfl⟩ : syracuseStep 5171885 = 1939457) (by norm_num)
theorem B3447923 : Blo 2297435 3447923 := bstep (se 1 (by rfl) ⟨2585942, by rfl⟩ : syracuseStep 3447923 = 5171885) B5171885
theorem B2298615 : Blo 2297435 2298615 := bstep (se 1 (by rfl) ⟨1723961, by rfl⟩ : syracuseStep 2298615 = 3447923) B3447923
theorem B4909261 : Blo 2297435 4909261 := bbase (se 3 (by rfl) ⟨920486, by rfl⟩ : syracuseStep 4909261 = 1840973) (by norm_num)
theorem B6545681 : Blo 2297435 6545681 := bstep (se 2 (by rfl) ⟨2454630, by rfl⟩ : syracuseStep 6545681 = 4909261) B4909261
theorem B4363787 : Blo 2297435 4363787 := bstep (se 1 (by rfl) ⟨3272840, by rfl⟩ : syracuseStep 4363787 = 6545681) B6545681
theorem B2909191 : Blo 2297435 2909191 := bstep (se 1 (by rfl) ⟨2181893, by rfl⟩ : syracuseStep 2909191 = 4363787) B4363787
theorem B3878921 : Blo 2297435 3878921 := bstep (se 2 (by rfl) ⟨1454595, by rfl⟩ : syracuseStep 3878921 = 2909191) B2909191
theorem B2585947 : Blo 2297435 2585947 := bstep (se 1 (by rfl) ⟨1939460, by rfl⟩ : syracuseStep 2585947 = 3878921) B3878921
theorem B3447929 : Blo 2297435 3447929 := bstep (se 2 (by rfl) ⟨1292973, by rfl⟩ : syracuseStep 3447929 = 2585947) B2585947
theorem B2298619 : Blo 2297435 2298619 := bstep (se 1 (by rfl) ⟨1723964, by rfl⟩ : syracuseStep 2298619 = 3447929) B3447929
theorem B2621233 : Blo 2297435 2621233 := bbase (se 2 (by rfl) ⟨982962, by rfl⟩ : syracuseStep 2621233 = 1965925) (by norm_num)
theorem B13979909 : Blo 2297435 13979909 := bstep (se 4 (by rfl) ⟨1310616, by rfl⟩ : syracuseStep 13979909 = 2621233) B2621233
theorem B37279757 : Blo 2297435 37279757 := bstep (se 3 (by rfl) ⟨6989954, by rfl⟩ : syracuseStep 37279757 = 13979909) B13979909
theorem B24853171 : Blo 2297435 24853171 := bstep (se 1 (by rfl) ⟨18639878, by rfl⟩ : syracuseStep 24853171 = 37279757) B37279757
theorem B33137561 : Blo 2297435 33137561 := bstep (se 2 (by rfl) ⟨12426585, by rfl⟩ : syracuseStep 33137561 = 24853171) B24853171
theorem B22091707 : Blo 2297435 22091707 := bstep (se 1 (by rfl) ⟨16568780, by rfl⟩ : syracuseStep 22091707 = 33137561) B33137561
theorem B29455609 : Blo 2297435 29455609 := bstep (se 2 (by rfl) ⟨11045853, by rfl⟩ : syracuseStep 29455609 = 22091707) B22091707
theorem B39274145 : Blo 2297435 39274145 := bstep (se 2 (by rfl) ⟨14727804, by rfl⟩ : syracuseStep 39274145 = 29455609) B29455609
theorem B26182763 : Blo 2297435 26182763 := bstep (se 1 (by rfl) ⟨19637072, by rfl⟩ : syracuseStep 26182763 = 39274145) B39274145
theorem B17455175 : Blo 2297435 17455175 := bstep (se 1 (by rfl) ⟨13091381, by rfl⟩ : syracuseStep 17455175 = 26182763) B26182763
theorem B11636783 : Blo 2297435 11636783 := bstep (se 1 (by rfl) ⟨8727587, by rfl⟩ : syracuseStep 11636783 = 17455175) B17455175
theorem B7757855 : Blo 2297435 7757855 := bstep (se 1 (by rfl) ⟨5818391, by rfl⟩ : syracuseStep 7757855 = 11636783) B11636783
theorem B5171903 : Blo 2297435 5171903 := bstep (se 1 (by rfl) ⟨3878927, by rfl⟩ : syracuseStep 5171903 = 7757855) B7757855
theorem B3447935 : Blo 2297435 3447935 := bstep (se 1 (by rfl) ⟨2585951, by rfl⟩ : syracuseStep 3447935 = 5171903) B5171903
theorem B2298623 : Blo 2297435 2298623 := bstep (se 1 (by rfl) ⟨1723967, by rfl⟩ : syracuseStep 2298623 = 3447935) B3447935
theorem B3447941 : Blo 2297435 3447941 := bbase (se 4 (by rfl) ⟨323244, by rfl⟩ : syracuseStep 3447941 = 646489) (by norm_num)
theorem B2298627 : Blo 2297435 2298627 := bstep (se 1 (by rfl) ⟨1723970, by rfl⟩ : syracuseStep 2298627 = 3447941) B3447941
theorem B3878941 : Blo 2297435 3878941 := bbase (se 3 (by rfl) ⟨727301, by rfl⟩ : syracuseStep 3878941 = 1454603) (by norm_num)
theorem B5171921 : Blo 2297435 5171921 := bstep (se 2 (by rfl) ⟨1939470, by rfl⟩ : syracuseStep 5171921 = 3878941) B3878941
theorem B3447947 : Blo 2297435 3447947 := bstep (se 1 (by rfl) ⟨2585960, by rfl⟩ : syracuseStep 3447947 = 5171921) B5171921
theorem B2298631 : Blo 2297435 2298631 := bstep (se 1 (by rfl) ⟨1723973, by rfl⟩ : syracuseStep 2298631 = 3447947) B3447947
theorem B2585965 : Blo 2297435 2585965 := bbase (se 3 (by rfl) ⟨484868, by rfl⟩ : syracuseStep 2585965 = 969737) (by norm_num)
theorem B3447953 : Blo 2297435 3447953 := bstep (se 2 (by rfl) ⟨1292982, by rfl⟩ : syracuseStep 3447953 = 2585965) B2585965
theorem B2298635 : Blo 2297435 2298635 := bstep (se 1 (by rfl) ⟨1723976, by rfl⟩ : syracuseStep 2298635 = 3447953) B3447953
theorem B7757909 : Blo 2297435 7757909 := bbase (se 8 (by rfl) ⟨45456, by rfl⟩ : syracuseStep 7757909 = 90913) (by norm_num)
theorem B5171939 : Blo 2297435 5171939 := bstep (se 1 (by rfl) ⟨3878954, by rfl⟩ : syracuseStep 5171939 = 7757909) B7757909
theorem B3447959 : Blo 2297435 3447959 := bstep (se 1 (by rfl) ⟨2585969, by rfl⟩ : syracuseStep 3447959 = 5171939) B5171939
theorem B2298639 : Blo 2297435 2298639 := bstep (se 1 (by rfl) ⟨1723979, by rfl⟩ : syracuseStep 2298639 = 3447959) B3447959
theorem B3447965 : Blo 2297435 3447965 := bbase (se 3 (by rfl) ⟨646493, by rfl⟩ : syracuseStep 3447965 = 1292987) (by norm_num)
theorem B2298643 : Blo 2297435 2298643 := bstep (se 1 (by rfl) ⟨1723982, by rfl⟩ : syracuseStep 2298643 = 3447965) B3447965
theorem B5171957 : Blo 2297435 5171957 := bbase (se 5 (by rfl) ⟨242435, by rfl⟩ : syracuseStep 5171957 = 484871) (by norm_num)
theorem B3447971 : Blo 2297435 3447971 := bstep (se 1 (by rfl) ⟨2585978, by rfl⟩ : syracuseStep 3447971 = 5171957) B5171957
theorem B2298647 : Blo 2297435 2298647 := bstep (se 1 (by rfl) ⟨1723985, by rfl⟩ : syracuseStep 2298647 = 3447971) B3447971
theorem B3106685 : Blo 2297435 3106685 := bbase (se 3 (by rfl) ⟨582503, by rfl⟩ : syracuseStep 3106685 = 1165007) (by norm_num)
theorem B8284493 : Blo 2297435 8284493 := bstep (se 3 (by rfl) ⟨1553342, by rfl⟩ : syracuseStep 8284493 = 3106685) B3106685
theorem B5522995 : Blo 2297435 5522995 := bstep (se 1 (by rfl) ⟨4142246, by rfl⟩ : syracuseStep 5522995 = 8284493) B8284493
theorem B29455973 : Blo 2297435 29455973 := bstep (se 4 (by rfl) ⟨2761497, by rfl⟩ : syracuseStep 29455973 = 5522995) B5522995
theorem B19637315 : Blo 2297435 19637315 := bstep (se 1 (by rfl) ⟨14727986, by rfl⟩ : syracuseStep 19637315 = 29455973) B29455973
theorem B13091543 : Blo 2297435 13091543 := bstep (se 1 (by rfl) ⟨9818657, by rfl⟩ : syracuseStep 13091543 = 19637315) B19637315
theorem B8727695 : Blo 2297435 8727695 := bstep (se 1 (by rfl) ⟨6545771, by rfl⟩ : syracuseStep 8727695 = 13091543) B13091543
theorem B5818463 : Blo 2297435 5818463 := bstep (se 1 (by rfl) ⟨4363847, by rfl⟩ : syracuseStep 5818463 = 8727695) B8727695
theorem B3878975 : Blo 2297435 3878975 := bstep (se 1 (by rfl) ⟨2909231, by rfl⟩ : syracuseStep 3878975 = 5818463) B5818463
theorem B2585983 : Blo 2297435 2585983 := bstep (se 1 (by rfl) ⟨1939487, by rfl⟩ : syracuseStep 2585983 = 3878975) B3878975
theorem B3447977 : Blo 2297435 3447977 := bstep (se 2 (by rfl) ⟨1292991, by rfl⟩ : syracuseStep 3447977 = 2585983) B2585983
theorem B2298651 : Blo 2297435 2298651 := bstep (se 1 (by rfl) ⟨1723988, by rfl⟩ : syracuseStep 2298651 = 3447977) B3447977
theorem B5523005 : Blo 2297435 5523005 := bbase (se 3 (by rfl) ⟨1035563, by rfl⟩ : syracuseStep 5523005 = 2071127) (by norm_num)
theorem B3682003 : Blo 2297435 3682003 := bstep (se 1 (by rfl) ⟨2761502, by rfl⟩ : syracuseStep 3682003 = 5523005) B5523005
theorem B4909337 : Blo 2297435 4909337 := bstep (se 2 (by rfl) ⟨1841001, by rfl⟩ : syracuseStep 4909337 = 3682003) B3682003
theorem B3272891 : Blo 2297435 3272891 := bstep (se 1 (by rfl) ⟨2454668, by rfl⟩ : syracuseStep 3272891 = 4909337) B4909337
theorem B8727709 : Blo 2297435 8727709 := bstep (se 3 (by rfl) ⟨1636445, by rfl⟩ : syracuseStep 8727709 = 3272891) B3272891
theorem B11636945 : Blo 2297435 11636945 := bstep (se 2 (by rfl) ⟨4363854, by rfl⟩ : syracuseStep 11636945 = 8727709) B8727709
theorem B7757963 : Blo 2297435 7757963 := bstep (se 1 (by rfl) ⟨5818472, by rfl⟩ : syracuseStep 7757963 = 11636945) B11636945
theorem B5171975 : Blo 2297435 5171975 := bstep (se 1 (by rfl) ⟨3878981, by rfl⟩ : syracuseStep 5171975 = 7757963) B7757963
theorem B3447983 : Blo 2297435 3447983 := bstep (se 1 (by rfl) ⟨2585987, by rfl⟩ : syracuseStep 3447983 = 5171975) B5171975
theorem B2298655 : Blo 2297435 2298655 := bstep (se 1 (by rfl) ⟨1723991, by rfl⟩ : syracuseStep 2298655 = 3447983) B3447983
theorem B3447989 : Blo 2297435 3447989 := bbase (se 5 (by rfl) ⟨161624, by rfl⟩ : syracuseStep 3447989 = 323249) (by norm_num)
theorem B2298659 : Blo 2297435 2298659 := bstep (se 1 (by rfl) ⟨1723994, by rfl⟩ : syracuseStep 2298659 = 3447989) B3447989
theorem B5818493 : Blo 2297435 5818493 := bbase (se 3 (by rfl) ⟨1090967, by rfl⟩ : syracuseStep 5818493 = 2181935) (by norm_num)
theorem B3878995 : Blo 2297435 3878995 := bstep (se 1 (by rfl) ⟨2909246, by rfl⟩ : syracuseStep 3878995 = 5818493) B5818493
theorem B5171993 : Blo 2297435 5171993 := bstep (se 2 (by rfl) ⟨1939497, by rfl⟩ : syracuseStep 5171993 = 3878995) B3878995
theorem B3447995 : Blo 2297435 3447995 := bstep (se 1 (by rfl) ⟨2585996, by rfl⟩ : syracuseStep 3447995 = 5171993) B5171993
theorem B2298663 : Blo 2297435 2298663 := bstep (se 1 (by rfl) ⟨1723997, by rfl⟩ : syracuseStep 2298663 = 3447995) B3447995
theorem B2586001 : Blo 2297435 2586001 := bbase (se 2 (by rfl) ⟨969750, by rfl⟩ : syracuseStep 2586001 = 1939501) (by norm_num)
theorem B3448001 : Blo 2297435 3448001 := bstep (se 2 (by rfl) ⟨1293000, by rfl⟩ : syracuseStep 3448001 = 2586001) B2586001
theorem B2298667 : Blo 2297435 2298667 := bstep (se 1 (by rfl) ⟨1724000, by rfl⟩ : syracuseStep 2298667 = 3448001) B3448001
theorem B4363885 : Blo 2297435 4363885 := bbase (se 3 (by rfl) ⟨818228, by rfl⟩ : syracuseStep 4363885 = 1636457) (by norm_num)
theorem B5818513 : Blo 2297435 5818513 := bstep (se 2 (by rfl) ⟨2181942, by rfl⟩ : syracuseStep 5818513 = 4363885) B4363885
theorem B7758017 : Blo 2297435 7758017 := bstep (se 2 (by rfl) ⟨2909256, by rfl⟩ : syracuseStep 7758017 = 5818513) B5818513
theorem B5172011 : Blo 2297435 5172011 := bstep (se 1 (by rfl) ⟨3879008, by rfl⟩ : syracuseStep 5172011 = 7758017) B7758017
theorem B3448007 : Blo 2297435 3448007 := bstep (se 1 (by rfl) ⟨2586005, by rfl⟩ : syracuseStep 3448007 = 5172011) B5172011
theorem B2298671 : Blo 2297435 2298671 := bstep (se 1 (by rfl) ⟨1724003, by rfl⟩ : syracuseStep 2298671 = 3448007) B3448007
theorem B3448013 : Blo 2297435 3448013 := bbase (se 3 (by rfl) ⟨646502, by rfl⟩ : syracuseStep 3448013 = 1293005) (by norm_num)
theorem B2298675 : Blo 2297435 2298675 := bstep (se 1 (by rfl) ⟨1724006, by rfl⟩ : syracuseStep 2298675 = 3448013) B3448013
theorem B5172029 : Blo 2297435 5172029 := bbase (se 3 (by rfl) ⟨969755, by rfl⟩ : syracuseStep 5172029 = 1939511) (by norm_num)
theorem B3448019 : Blo 2297435 3448019 := bstep (se 1 (by rfl) ⟨2586014, by rfl⟩ : syracuseStep 3448019 = 5172029) B5172029
theorem B2298679 : Blo 2297435 2298679 := bstep (se 1 (by rfl) ⟨1724009, by rfl⟩ : syracuseStep 2298679 = 3448019) B3448019
theorem B3879029 : Blo 2297435 3879029 := bbase (se 5 (by rfl) ⟨181829, by rfl⟩ : syracuseStep 3879029 = 363659) (by norm_num)
theorem B2586019 : Blo 2297435 2586019 := bstep (se 1 (by rfl) ⟨1939514, by rfl⟩ : syracuseStep 2586019 = 3879029) B3879029
theorem B3448025 : Blo 2297435 3448025 := bstep (se 2 (by rfl) ⟨1293009, by rfl⟩ : syracuseStep 3448025 = 2586019) B2586019
theorem B2298683 : Blo 2297435 2298683 := bstep (se 1 (by rfl) ⟨1724012, by rfl⟩ : syracuseStep 2298683 = 3448025) B3448025
theorem B4909405 : Blo 2297435 4909405 := bbase (se 3 (by rfl) ⟨920513, by rfl⟩ : syracuseStep 4909405 = 1841027) (by norm_num)
theorem B6545873 : Blo 2297435 6545873 := bstep (se 2 (by rfl) ⟨2454702, by rfl⟩ : syracuseStep 6545873 = 4909405) B4909405
theorem B17455661 : Blo 2297435 17455661 := bstep (se 3 (by rfl) ⟨3272936, by rfl⟩ : syracuseStep 17455661 = 6545873) B6545873
theorem B11637107 : Blo 2297435 11637107 := bstep (se 1 (by rfl) ⟨8727830, by rfl⟩ : syracuseStep 11637107 = 17455661) B17455661
theorem B7758071 : Blo 2297435 7758071 := bstep (se 1 (by rfl) ⟨5818553, by rfl⟩ : syracuseStep 7758071 = 11637107) B11637107
theorem B5172047 : Blo 2297435 5172047 := bstep (se 1 (by rfl) ⟨3879035, by rfl⟩ : syracuseStep 5172047 = 7758071) B7758071
theorem B3448031 : Blo 2297435 3448031 := bstep (se 1 (by rfl) ⟨2586023, by rfl⟩ : syracuseStep 3448031 = 5172047) B5172047
theorem B2298687 : Blo 2297435 2298687 := bstep (se 1 (by rfl) ⟨1724015, by rfl⟩ : syracuseStep 2298687 = 3448031) B3448031
theorem B3448037 : Blo 2297435 3448037 := bbase (se 4 (by rfl) ⟨323253, by rfl⟩ : syracuseStep 3448037 = 646507) (by norm_num)
theorem B2298691 : Blo 2297435 2298691 := bstep (se 1 (by rfl) ⟨1724018, by rfl⟩ : syracuseStep 2298691 = 3448037) B3448037
theorem B18640469 : Blo 2297435 18640469 := bbase (se 8 (by rfl) ⟨109221, by rfl⟩ : syracuseStep 18640469 = 218443) (by norm_num)
theorem B12426979 : Blo 2297435 12426979 := bstep (se 1 (by rfl) ⟨9320234, by rfl⟩ : syracuseStep 12426979 = 18640469) B18640469
theorem B16569305 : Blo 2297435 16569305 := bstep (se 2 (by rfl) ⟨6213489, by rfl⟩ : syracuseStep 16569305 = 12426979) B12426979
theorem B11046203 : Blo 2297435 11046203 := bstep (se 1 (by rfl) ⟨8284652, by rfl⟩ : syracuseStep 11046203 = 16569305) B16569305
theorem B7364135 : Blo 2297435 7364135 := bstep (se 1 (by rfl) ⟨5523101, by rfl⟩ : syracuseStep 7364135 = 11046203) B11046203
theorem B4909423 : Blo 2297435 4909423 := bstep (se 1 (by rfl) ⟨3682067, by rfl⟩ : syracuseStep 4909423 = 7364135) B7364135
theorem B6545897 : Blo 2297435 6545897 := bstep (se 2 (by rfl) ⟨2454711, by rfl⟩ : syracuseStep 6545897 = 4909423) B4909423
theorem B4363931 : Blo 2297435 4363931 := bstep (se 1 (by rfl) ⟨3272948, by rfl⟩ : syracuseStep 4363931 = 6545897) B6545897
theorem B2909287 : Blo 2297435 2909287 := bstep (se 1 (by rfl) ⟨2181965, by rfl⟩ : syracuseStep 2909287 = 4363931) B4363931
theorem B3879049 : Blo 2297435 3879049 := bstep (se 2 (by rfl) ⟨1454643, by rfl⟩ : syracuseStep 3879049 = 2909287) B2909287
theorem B5172065 : Blo 2297435 5172065 := bstep (se 2 (by rfl) ⟨1939524, by rfl⟩ : syracuseStep 5172065 = 3879049) B3879049
theorem B3448043 : Blo 2297435 3448043 := bstep (se 1 (by rfl) ⟨2586032, by rfl⟩ : syracuseStep 3448043 = 5172065) B5172065
theorem B2298695 : Blo 2297435 2298695 := bstep (se 1 (by rfl) ⟨1724021, by rfl⟩ : syracuseStep 2298695 = 3448043) B3448043
theorem B2586037 : Blo 2297435 2586037 := bbase (se 5 (by rfl) ⟨121220, by rfl⟩ : syracuseStep 2586037 = 242441) (by norm_num)
theorem B3448049 : Blo 2297435 3448049 := bstep (se 2 (by rfl) ⟨1293018, by rfl⟩ : syracuseStep 3448049 = 2586037) B2586037
theorem B2298699 : Blo 2297435 2298699 := bstep (se 1 (by rfl) ⟨1724024, by rfl⟩ : syracuseStep 2298699 = 3448049) B3448049
theorem B2909297 : Blo 2297435 2909297 := bbase (se 2 (by rfl) ⟨1090986, by rfl⟩ : syracuseStep 2909297 = 2181973) (by norm_num)
theorem B7758125 : Blo 2297435 7758125 := bstep (se 3 (by rfl) ⟨1454648, by rfl⟩ : syracuseStep 7758125 = 2909297) B2909297
theorem B5172083 : Blo 2297435 5172083 := bstep (se 1 (by rfl) ⟨3879062, by rfl⟩ : syracuseStep 5172083 = 7758125) B7758125
theorem B3448055 : Blo 2297435 3448055 := bstep (se 1 (by rfl) ⟨2586041, by rfl⟩ : syracuseStep 3448055 = 5172083) B5172083
theorem B2298703 : Blo 2297435 2298703 := bstep (se 1 (by rfl) ⟨1724027, by rfl⟩ : syracuseStep 2298703 = 3448055) B3448055
theorem B3448061 : Blo 2297435 3448061 := bbase (se 3 (by rfl) ⟨646511, by rfl⟩ : syracuseStep 3448061 = 1293023) (by norm_num)
theorem B2298707 : Blo 2297435 2298707 := bstep (se 1 (by rfl) ⟨1724030, by rfl⟩ : syracuseStep 2298707 = 3448061) B3448061
theorem B5172101 : Blo 2297435 5172101 := bbase (se 4 (by rfl) ⟨484884, by rfl⟩ : syracuseStep 5172101 = 969769) (by norm_num)
theorem B3448067 : Blo 2297435 3448067 := bstep (se 1 (by rfl) ⟨2586050, by rfl⟩ : syracuseStep 3448067 = 5172101) B5172101
theorem B2298711 : Blo 2297435 2298711 := bstep (se 1 (by rfl) ⟨1724033, by rfl⟩ : syracuseStep 2298711 = 3448067) B3448067
theorem B2454733 : Blo 2297435 2454733 := bbase (se 3 (by rfl) ⟨460262, by rfl⟩ : syracuseStep 2454733 = 920525) (by norm_num)
theorem B3272977 : Blo 2297435 3272977 := bstep (se 2 (by rfl) ⟨1227366, by rfl⟩ : syracuseStep 3272977 = 2454733) B2454733
theorem B4363969 : Blo 2297435 4363969 := bstep (se 2 (by rfl) ⟨1636488, by rfl⟩ : syracuseStep 4363969 = 3272977) B3272977
theorem B5818625 : Blo 2297435 5818625 := bstep (se 2 (by rfl) ⟨2181984, by rfl⟩ : syracuseStep 5818625 = 4363969) B4363969
theorem B3879083 : Blo 2297435 3879083 := bstep (se 1 (by rfl) ⟨2909312, by rfl⟩ : syracuseStep 3879083 = 5818625) B5818625
theorem B2586055 : Blo 2297435 2586055 := bstep (se 1 (by rfl) ⟨1939541, by rfl⟩ : syracuseStep 2586055 = 3879083) B3879083
theorem B3448073 : Blo 2297435 3448073 := bstep (se 2 (by rfl) ⟨1293027, by rfl⟩ : syracuseStep 3448073 = 2586055) B2586055
theorem B2298715 : Blo 2297435 2298715 := bstep (se 1 (by rfl) ⟨1724036, by rfl⟩ : syracuseStep 2298715 = 3448073) B3448073
theorem B11637269 : Blo 2297435 11637269 := bbase (se 6 (by rfl) ⟨272748, by rfl⟩ : syracuseStep 11637269 = 545497) (by norm_num)
theorem B7758179 : Blo 2297435 7758179 := bstep (se 1 (by rfl) ⟨5818634, by rfl⟩ : syracuseStep 7758179 = 11637269) B11637269
theorem B5172119 : Blo 2297435 5172119 := bstep (se 1 (by rfl) ⟨3879089, by rfl⟩ : syracuseStep 5172119 = 7758179) B7758179
theorem B3448079 : Blo 2297435 3448079 := bstep (se 1 (by rfl) ⟨2586059, by rfl⟩ : syracuseStep 3448079 = 5172119) B5172119
theorem B2298719 : Blo 2297435 2298719 := bstep (se 1 (by rfl) ⟨1724039, by rfl⟩ : syracuseStep 2298719 = 3448079) B3448079
theorem B3448085 : Blo 2297435 3448085 := bbase (se 6 (by rfl) ⟨80814, by rfl⟩ : syracuseStep 3448085 = 161629) (by norm_num)
theorem B2298723 : Blo 2297435 2298723 := bstep (se 1 (by rfl) ⟨1724042, by rfl⟩ : syracuseStep 2298723 = 3448085) B3448085
theorem B9952949 : Blo 2297435 9952949 := bbase (se 5 (by rfl) ⟨466544, by rfl⟩ : syracuseStep 9952949 = 933089) (by norm_num)
theorem B6635299 : Blo 2297435 6635299 := bstep (se 1 (by rfl) ⟨4976474, by rfl⟩ : syracuseStep 6635299 = 9952949) B9952949
theorem B8847065 : Blo 2297435 8847065 := bstep (se 2 (by rfl) ⟨3317649, by rfl⟩ : syracuseStep 8847065 = 6635299) B6635299
theorem B5898043 : Blo 2297435 5898043 := bstep (se 1 (by rfl) ⟨4423532, by rfl⟩ : syracuseStep 5898043 = 8847065) B8847065
theorem B7864057 : Blo 2297435 7864057 := bstep (se 2 (by rfl) ⟨2949021, by rfl⟩ : syracuseStep 7864057 = 5898043) B5898043
theorem B10485409 : Blo 2297435 10485409 := bstep (se 2 (by rfl) ⟨3932028, by rfl⟩ : syracuseStep 10485409 = 7864057) B7864057
theorem B13980545 : Blo 2297435 13980545 := bstep (se 2 (by rfl) ⟨5242704, by rfl⟩ : syracuseStep 13980545 = 10485409) B10485409
theorem B9320363 : Blo 2297435 9320363 := bstep (se 1 (by rfl) ⟨6990272, by rfl⟩ : syracuseStep 9320363 = 13980545) B13980545
theorem B6213575 : Blo 2297435 6213575 := bstep (se 1 (by rfl) ⟨4660181, by rfl⟩ : syracuseStep 6213575 = 9320363) B9320363
theorem B4142383 : Blo 2297435 4142383 := bstep (se 1 (by rfl) ⟨3106787, by rfl⟩ : syracuseStep 4142383 = 6213575) B6213575
theorem B22092709 : Blo 2297435 22092709 := bstep (se 4 (by rfl) ⟨2071191, by rfl⟩ : syracuseStep 22092709 = 4142383) B4142383
theorem B29456945 : Blo 2297435 29456945 := bstep (se 2 (by rfl) ⟨11046354, by rfl⟩ : syracuseStep 29456945 = 22092709) B22092709
theorem B19637963 : Blo 2297435 19637963 := bstep (se 1 (by rfl) ⟨14728472, by rfl⟩ : syracuseStep 19637963 = 29456945) B29456945
theorem B13091975 : Blo 2297435 13091975 := bstep (se 1 (by rfl) ⟨9818981, by rfl⟩ : syracuseStep 13091975 = 19637963) B19637963
theorem B8727983 : Blo 2297435 8727983 := bstep (se 1 (by rfl) ⟨6545987, by rfl⟩ : syracuseStep 8727983 = 13091975) B13091975
theorem B5818655 : Blo 2297435 5818655 := bstep (se 1 (by rfl) ⟨4363991, by rfl⟩ : syracuseStep 5818655 = 8727983) B8727983
theorem B3879103 : Blo 2297435 3879103 := bstep (se 1 (by rfl) ⟨2909327, by rfl⟩ : syracuseStep 3879103 = 5818655) B5818655
theorem B5172137 : Blo 2297435 5172137 := bstep (se 2 (by rfl) ⟨1939551, by rfl⟩ : syracuseStep 5172137 = 3879103) B3879103
theorem B3448091 : Blo 2297435 3448091 := bstep (se 1 (by rfl) ⟨2586068, by rfl⟩ : syracuseStep 3448091 = 5172137) B5172137
theorem B2298727 : Blo 2297435 2298727 := bstep (se 1 (by rfl) ⟨1724045, by rfl⟩ : syracuseStep 2298727 = 3448091) B3448091
theorem B2586073 : Blo 2297435 2586073 := bbase (se 2 (by rfl) ⟨969777, by rfl⟩ : syracuseStep 2586073 = 1939555) (by norm_num)
theorem B3448097 : Blo 2297435 3448097 := bstep (se 2 (by rfl) ⟨1293036, by rfl⟩ : syracuseStep 3448097 = 2586073) B2586073
theorem B2298731 : Blo 2297435 2298731 := bstep (se 1 (by rfl) ⟨1724048, by rfl⟩ : syracuseStep 2298731 = 3448097) B3448097
theorem B3273005 : Blo 2297435 3273005 := bbase (se 3 (by rfl) ⟨613688, by rfl⟩ : syracuseStep 3273005 = 1227377) (by norm_num)
theorem B8728013 : Blo 2297435 8728013 := bstep (se 3 (by rfl) ⟨1636502, by rfl⟩ : syracuseStep 8728013 = 3273005) B3273005
theorem B5818675 : Blo 2297435 5818675 := bstep (se 1 (by rfl) ⟨4364006, by rfl⟩ : syracuseStep 5818675 = 8728013) B8728013
theorem B7758233 : Blo 2297435 7758233 := bstep (se 2 (by rfl) ⟨2909337, by rfl⟩ : syracuseStep 7758233 = 5818675) B5818675
theorem B5172155 : Blo 2297435 5172155 := bstep (se 1 (by rfl) ⟨3879116, by rfl⟩ : syracuseStep 5172155 = 7758233) B7758233
theorem B3448103 : Blo 2297435 3448103 := bstep (se 1 (by rfl) ⟨2586077, by rfl⟩ : syracuseStep 3448103 = 5172155) B5172155
theorem B2298735 : Blo 2297435 2298735 := bstep (se 1 (by rfl) ⟨1724051, by rfl⟩ : syracuseStep 2298735 = 3448103) B3448103
theorem B3448109 : Blo 2297435 3448109 := bbase (se 3 (by rfl) ⟨646520, by rfl⟩ : syracuseStep 3448109 = 1293041) (by norm_num)
theorem B2298739 : Blo 2297435 2298739 := bstep (se 1 (by rfl) ⟨1724054, by rfl⟩ : syracuseStep 2298739 = 3448109) B3448109
theorem B5172173 : Blo 2297435 5172173 := bbase (se 3 (by rfl) ⟨969782, by rfl⟩ : syracuseStep 5172173 = 1939565) (by norm_num)
theorem B3448115 : Blo 2297435 3448115 := bstep (se 1 (by rfl) ⟨2586086, by rfl⟩ : syracuseStep 3448115 = 5172173) B5172173
theorem B2298743 : Blo 2297435 2298743 := bstep (se 1 (by rfl) ⟨1724057, by rfl⟩ : syracuseStep 2298743 = 3448115) B3448115
theorem B2909353 : Blo 2297435 2909353 := bbase (se 2 (by rfl) ⟨1091007, by rfl⟩ : syracuseStep 2909353 = 2182015) (by norm_num)
theorem B3879137 : Blo 2297435 3879137 := bstep (se 2 (by rfl) ⟨1454676, by rfl⟩ : syracuseStep 3879137 = 2909353) B2909353
theorem B2586091 : Blo 2297435 2586091 := bstep (se 1 (by rfl) ⟨1939568, by rfl⟩ : syracuseStep 2586091 = 3879137) B3879137
theorem B3448121 : Blo 2297435 3448121 := bstep (se 2 (by rfl) ⟨1293045, by rfl⟩ : syracuseStep 3448121 = 2586091) B2586091
theorem B2298747 : Blo 2297435 2298747 := bstep (se 1 (by rfl) ⟨1724060, by rfl⟩ : syracuseStep 2298747 = 3448121) B3448121
theorem B11046469 : Blo 2297435 11046469 := bbase (se 4 (by rfl) ⟨1035606, by rfl⟩ : syracuseStep 11046469 = 2071213) (by norm_num)
theorem B14728625 : Blo 2297435 14728625 := bstep (se 2 (by rfl) ⟨5523234, by rfl⟩ : syracuseStep 14728625 = 11046469) B11046469
theorem B9819083 : Blo 2297435 9819083 := bstep (se 1 (by rfl) ⟨7364312, by rfl⟩ : syracuseStep 9819083 = 14728625) B14728625
theorem B26184221 : Blo 2297435 26184221 := bstep (se 3 (by rfl) ⟨4909541, by rfl⟩ : syracuseStep 26184221 = 9819083) B9819083
theorem B17456147 : Blo 2297435 17456147 := bstep (se 1 (by rfl) ⟨13092110, by rfl⟩ : syracuseStep 17456147 = 26184221) B26184221
theorem B11637431 : Blo 2297435 11637431 := bstep (se 1 (by rfl) ⟨8728073, by rfl⟩ : syracuseStep 11637431 = 17456147) B17456147
theorem B7758287 : Blo 2297435 7758287 := bstep (se 1 (by rfl) ⟨5818715, by rfl⟩ : syracuseStep 7758287 = 11637431) B11637431
theorem B5172191 : Blo 2297435 5172191 := bstep (se 1 (by rfl) ⟨3879143, by rfl⟩ : syracuseStep 5172191 = 7758287) B7758287
theorem B3448127 : Blo 2297435 3448127 := bstep (se 1 (by rfl) ⟨2586095, by rfl⟩ : syracuseStep 3448127 = 5172191) B5172191
theorem B2298751 : Blo 2297435 2298751 := bstep (se 1 (by rfl) ⟨1724063, by rfl⟩ : syracuseStep 2298751 = 3448127) B3448127
theorem B3448133 : Blo 2297435 3448133 := bbase (se 4 (by rfl) ⟨323262, by rfl⟩ : syracuseStep 3448133 = 646525) (by norm_num)
theorem B2298755 : Blo 2297435 2298755 := bstep (se 1 (by rfl) ⟨1724066, by rfl⟩ : syracuseStep 2298755 = 3448133) B3448133
theorem B3879157 : Blo 2297435 3879157 := bbase (se 5 (by rfl) ⟨181835, by rfl⟩ : syracuseStep 3879157 = 363671) (by norm_num)
theorem B5172209 : Blo 2297435 5172209 := bstep (se 2 (by rfl) ⟨1939578, by rfl⟩ : syracuseStep 5172209 = 3879157) B3879157
theorem B3448139 : Blo 2297435 3448139 := bstep (se 1 (by rfl) ⟨2586104, by rfl⟩ : syracuseStep 3448139 = 5172209) B5172209
theorem B2298759 : Blo 2297435 2298759 := bstep (se 1 (by rfl) ⟨1724069, by rfl⟩ : syracuseStep 2298759 = 3448139) B3448139
theorem B2586109 : Blo 2297435 2586109 := bbase (se 3 (by rfl) ⟨484895, by rfl⟩ : syracuseStep 2586109 = 969791) (by norm_num)
theorem B3448145 : Blo 2297435 3448145 := bstep (se 2 (by rfl) ⟨1293054, by rfl⟩ : syracuseStep 3448145 = 2586109) B2586109
theorem B2298763 : Blo 2297435 2298763 := bstep (se 1 (by rfl) ⟨1724072, by rfl⟩ : syracuseStep 2298763 = 3448145) B3448145
theorem B7758341 : Blo 2297435 7758341 := bbase (se 4 (by rfl) ⟨727344, by rfl⟩ : syracuseStep 7758341 = 1454689) (by norm_num)
theorem B5172227 : Blo 2297435 5172227 := bstep (se 1 (by rfl) ⟨3879170, by rfl⟩ : syracuseStep 5172227 = 7758341) B7758341
theorem B3448151 : Blo 2297435 3448151 := bstep (se 1 (by rfl) ⟨2586113, by rfl⟩ : syracuseStep 3448151 = 5172227) B5172227
theorem B2298767 : Blo 2297435 2298767 := bstep (se 1 (by rfl) ⟨1724075, by rfl⟩ : syracuseStep 2298767 = 3448151) B3448151
theorem B3448157 : Blo 2297435 3448157 := bbase (se 3 (by rfl) ⟨646529, by rfl⟩ : syracuseStep 3448157 = 1293059) (by norm_num)
theorem B2298771 : Blo 2297435 2298771 := bstep (se 1 (by rfl) ⟨1724078, by rfl⟩ : syracuseStep 2298771 = 3448157) B3448157
theorem B5172245 : Blo 2297435 5172245 := bbase (se 6 (by rfl) ⟨121224, by rfl⟩ : syracuseStep 5172245 = 242449) (by norm_num)
theorem B3448163 : Blo 2297435 3448163 := bstep (se 1 (by rfl) ⟨2586122, by rfl⟩ : syracuseStep 3448163 = 5172245) B5172245
theorem B2298775 : Blo 2297435 2298775 := bstep (se 1 (by rfl) ⟨1724081, by rfl⟩ : syracuseStep 2298775 = 3448163) B3448163
theorem B8728181 : Blo 2297435 8728181 := bbase (se 5 (by rfl) ⟨409133, by rfl⟩ : syracuseStep 8728181 = 818267) (by norm_num)
theorem B5818787 : Blo 2297435 5818787 := bstep (se 1 (by rfl) ⟨4364090, by rfl⟩ : syracuseStep 5818787 = 8728181) B8728181
theorem B3879191 : Blo 2297435 3879191 := bstep (se 1 (by rfl) ⟨2909393, by rfl⟩ : syracuseStep 3879191 = 5818787) B5818787
theorem B2586127 : Blo 2297435 2586127 := bstep (se 1 (by rfl) ⟨1939595, by rfl⟩ : syracuseStep 2586127 = 3879191) B3879191
theorem B3448169 : Blo 2297435 3448169 := bstep (se 2 (by rfl) ⟨1293063, by rfl⟩ : syracuseStep 3448169 = 2586127) B2586127
theorem B2298779 : Blo 2297435 2298779 := bstep (se 1 (by rfl) ⟨1724084, by rfl⟩ : syracuseStep 2298779 = 3448169) B3448169
theorem B2454805 : Blo 2297435 2454805 := bbase (se 6 (by rfl) ⟨57534, by rfl⟩ : syracuseStep 2454805 = 115069) (by norm_num)
theorem B13092293 : Blo 2297435 13092293 := bstep (se 4 (by rfl) ⟨1227402, by rfl⟩ : syracuseStep 13092293 = 2454805) B2454805
theorem B8728195 : Blo 2297435 8728195 := bstep (se 1 (by rfl) ⟨6546146, by rfl⟩ : syracuseStep 8728195 = 13092293) B13092293
theorem B11637593 : Blo 2297435 11637593 := bstep (se 2 (by rfl) ⟨4364097, by rfl⟩ : syracuseStep 11637593 = 8728195) B8728195
theorem B7758395 : Blo 2297435 7758395 := bstep (se 1 (by rfl) ⟨5818796, by rfl⟩ : syracuseStep 7758395 = 11637593) B11637593
theorem B5172263 : Blo 2297435 5172263 := bstep (se 1 (by rfl) ⟨3879197, by rfl⟩ : syracuseStep 5172263 = 7758395) B7758395
theorem B3448175 : Blo 2297435 3448175 := bstep (se 1 (by rfl) ⟨2586131, by rfl⟩ : syracuseStep 3448175 = 5172263) B5172263
theorem B2298783 : Blo 2297435 2298783 := bstep (se 1 (by rfl) ⟨1724087, by rfl⟩ : syracuseStep 2298783 = 3448175) B3448175
theorem B3448181 : Blo 2297435 3448181 := bbase (se 5 (by rfl) ⟨161633, by rfl⟩ : syracuseStep 3448181 = 323267) (by norm_num)
theorem B2298787 : Blo 2297435 2298787 := bstep (se 1 (by rfl) ⟨1724090, by rfl⟩ : syracuseStep 2298787 = 3448181) B3448181
theorem B3273085 : Blo 2297435 3273085 := bbase (se 3 (by rfl) ⟨613703, by rfl⟩ : syracuseStep 3273085 = 1227407) (by norm_num)
theorem B4364113 : Blo 2297435 4364113 := bstep (se 2 (by rfl) ⟨1636542, by rfl⟩ : syracuseStep 4364113 = 3273085) B3273085
theorem B5818817 : Blo 2297435 5818817 := bstep (se 2 (by rfl) ⟨2182056, by rfl⟩ : syracuseStep 5818817 = 4364113) B4364113
theorem B3879211 : Blo 2297435 3879211 := bstep (se 1 (by rfl) ⟨2909408, by rfl⟩ : syracuseStep 3879211 = 5818817) B5818817
theorem B5172281 : Blo 2297435 5172281 := bstep (se 2 (by rfl) ⟨1939605, by rfl⟩ : syracuseStep 5172281 = 3879211) B3879211
theorem B3448187 : Blo 2297435 3448187 := bstep (se 1 (by rfl) ⟨2586140, by rfl⟩ : syracuseStep 3448187 = 5172281) B5172281
theorem B2298791 : Blo 2297435 2298791 := bstep (se 1 (by rfl) ⟨1724093, by rfl⟩ : syracuseStep 2298791 = 3448187) B3448187
theorem B2586145 : Blo 2297435 2586145 := bbase (se 2 (by rfl) ⟨969804, by rfl⟩ : syracuseStep 2586145 = 1939609) (by norm_num)
theorem B3448193 : Blo 2297435 3448193 := bstep (se 2 (by rfl) ⟨1293072, by rfl⟩ : syracuseStep 3448193 = 2586145) B2586145
theorem B2298795 : Blo 2297435 2298795 := bstep (se 1 (by rfl) ⟨1724096, by rfl⟩ : syracuseStep 2298795 = 3448193) B3448193
theorem B5818837 : Blo 2297435 5818837 := bbase (se 7 (by rfl) ⟨68189, by rfl⟩ : syracuseStep 5818837 = 136379) (by norm_num)
theorem B7758449 : Blo 2297435 7758449 := bstep (se 2 (by rfl) ⟨2909418, by rfl⟩ : syracuseStep 7758449 = 5818837) B5818837
theorem B5172299 : Blo 2297435 5172299 := bstep (se 1 (by rfl) ⟨3879224, by rfl⟩ : syracuseStep 5172299 = 7758449) B7758449
theorem B3448199 : Blo 2297435 3448199 := bstep (se 1 (by rfl) ⟨2586149, by rfl⟩ : syracuseStep 3448199 = 5172299) B5172299
theorem B2298799 : Blo 2297435 2298799 := bstep (se 1 (by rfl) ⟨1724099, by rfl⟩ : syracuseStep 2298799 = 3448199) B3448199
theorem B3448205 : Blo 2297435 3448205 := bbase (se 3 (by rfl) ⟨646538, by rfl⟩ : syracuseStep 3448205 = 1293077) (by norm_num)
theorem B2298803 : Blo 2297435 2298803 := bstep (se 1 (by rfl) ⟨1724102, by rfl⟩ : syracuseStep 2298803 = 3448205) B3448205
theorem B5172317 : Blo 2297435 5172317 := bbase (se 3 (by rfl) ⟨969809, by rfl⟩ : syracuseStep 5172317 = 1939619) (by norm_num)
theorem B3448211 : Blo 2297435 3448211 := bstep (se 1 (by rfl) ⟨2586158, by rfl⟩ : syracuseStep 3448211 = 5172317) B5172317
theorem B2298807 : Blo 2297435 2298807 := bstep (se 1 (by rfl) ⟨1724105, by rfl⟩ : syracuseStep 2298807 = 3448211) B3448211
theorem B3879245 : Blo 2297435 3879245 := bbase (se 3 (by rfl) ⟨727358, by rfl⟩ : syracuseStep 3879245 = 1454717) (by norm_num)
theorem B2586163 : Blo 2297435 2586163 := bstep (se 1 (by rfl) ⟨1939622, by rfl⟩ : syracuseStep 2586163 = 3879245) B3879245
theorem B3448217 : Blo 2297435 3448217 := bstep (se 2 (by rfl) ⟨1293081, by rfl⟩ : syracuseStep 3448217 = 2586163) B2586163
theorem B2298811 : Blo 2297435 2298811 := bstep (se 1 (by rfl) ⟨1724108, by rfl⟩ : syracuseStep 2298811 = 3448217) B3448217
theorem B16570165 : Blo 2297435 16570165 := bbase (se 5 (by rfl) ⟨776726, by rfl⟩ : syracuseStep 16570165 = 1553453) (by norm_num)
theorem B22093553 : Blo 2297435 22093553 := bstep (se 2 (by rfl) ⟨8285082, by rfl⟩ : syracuseStep 22093553 = 16570165) B16570165
theorem B14729035 : Blo 2297435 14729035 := bstep (se 1 (by rfl) ⟨11046776, by rfl⟩ : syracuseStep 14729035 = 22093553) B22093553
theorem B19638713 : Blo 2297435 19638713 := bstep (se 2 (by rfl) ⟨7364517, by rfl⟩ : syracuseStep 19638713 = 14729035) B14729035
theorem B13092475 : Blo 2297435 13092475 := bstep (se 1 (by rfl) ⟨9819356, by rfl⟩ : syracuseStep 13092475 = 19638713) B19638713
theorem B17456633 : Blo 2297435 17456633 := bstep (se 2 (by rfl) ⟨6546237, by rfl⟩ : syracuseStep 17456633 = 13092475) B13092475
theorem B11637755 : Blo 2297435 11637755 := bstep (se 1 (by rfl) ⟨8728316, by rfl⟩ : syracuseStep 11637755 = 17456633) B17456633
theorem B7758503 : Blo 2297435 7758503 := bstep (se 1 (by rfl) ⟨5818877, by rfl⟩ : syracuseStep 7758503 = 11637755) B11637755
theorem B5172335 : Blo 2297435 5172335 := bstep (se 1 (by rfl) ⟨3879251, by rfl⟩ : syracuseStep 5172335 = 7758503) B7758503
theorem B3448223 : Blo 2297435 3448223 := bstep (se 1 (by rfl) ⟨2586167, by rfl⟩ : syracuseStep 3448223 = 5172335) B5172335
theorem B2298815 : Blo 2297435 2298815 := bstep (se 1 (by rfl) ⟨1724111, by rfl⟩ : syracuseStep 2298815 = 3448223) B3448223
theorem B3448229 : Blo 2297435 3448229 := bbase (se 4 (by rfl) ⟨323271, by rfl⟩ : syracuseStep 3448229 = 646543) (by norm_num)
theorem B2298819 : Blo 2297435 2298819 := bstep (se 1 (by rfl) ⟨1724114, by rfl⟩ : syracuseStep 2298819 = 3448229) B3448229
theorem B2909449 : Blo 2297435 2909449 := bbase (se 2 (by rfl) ⟨1091043, by rfl⟩ : syracuseStep 2909449 = 2182087) (by norm_num)
theorem B3879265 : Blo 2297435 3879265 := bstep (se 2 (by rfl) ⟨1454724, by rfl⟩ : syracuseStep 3879265 = 2909449) B2909449
theorem B5172353 : Blo 2297435 5172353 := bstep (se 2 (by rfl) ⟨1939632, by rfl⟩ : syracuseStep 5172353 = 3879265) B3879265
theorem B3448235 : Blo 2297435 3448235 := bstep (se 1 (by rfl) ⟨2586176, by rfl⟩ : syracuseStep 3448235 = 5172353) B5172353
theorem B2298823 : Blo 2297435 2298823 := bstep (se 1 (by rfl) ⟨1724117, by rfl⟩ : syracuseStep 2298823 = 3448235) B3448235
theorem B2586181 : Blo 2297435 2586181 := bbase (se 4 (by rfl) ⟨242454, by rfl⟩ : syracuseStep 2586181 = 484909) (by norm_num)
theorem B3448241 : Blo 2297435 3448241 := bstep (se 2 (by rfl) ⟨1293090, by rfl⟩ : syracuseStep 3448241 = 2586181) B2586181
theorem B2298827 : Blo 2297435 2298827 := bstep (se 1 (by rfl) ⟨1724120, by rfl⟩ : syracuseStep 2298827 = 3448241) B3448241
theorem B4364189 : Blo 2297435 4364189 := bbase (se 3 (by rfl) ⟨818285, by rfl⟩ : syracuseStep 4364189 = 1636571) (by norm_num)
theorem B2909459 : Blo 2297435 2909459 := bstep (se 1 (by rfl) ⟨2182094, by rfl⟩ : syracuseStep 2909459 = 4364189) B4364189
theorem B7758557 : Blo 2297435 7758557 := bstep (se 3 (by rfl) ⟨1454729, by rfl⟩ : syracuseStep 7758557 = 2909459) B2909459
theorem B5172371 : Blo 2297435 5172371 := bstep (se 1 (by rfl) ⟨3879278, by rfl⟩ : syracuseStep 5172371 = 7758557) B7758557
theorem B3448247 : Blo 2297435 3448247 := bstep (se 1 (by rfl) ⟨2586185, by rfl⟩ : syracuseStep 3448247 = 5172371) B5172371
theorem B2298831 : Blo 2297435 2298831 := bstep (se 1 (by rfl) ⟨1724123, by rfl⟩ : syracuseStep 2298831 = 3448247) B3448247
theorem B3448253 : Blo 2297435 3448253 := bbase (se 3 (by rfl) ⟨646547, by rfl⟩ : syracuseStep 3448253 = 1293095) (by norm_num)
theorem B2298835 : Blo 2297435 2298835 := bstep (se 1 (by rfl) ⟨1724126, by rfl⟩ : syracuseStep 2298835 = 3448253) B3448253
theorem B5172389 : Blo 2297435 5172389 := bbase (se 4 (by rfl) ⟨484911, by rfl⟩ : syracuseStep 5172389 = 969823) (by norm_num)
theorem B3448259 : Blo 2297435 3448259 := bstep (se 1 (by rfl) ⟨2586194, by rfl⟩ : syracuseStep 3448259 = 5172389) B5172389
theorem B2298839 : Blo 2297435 2298839 := bstep (se 1 (by rfl) ⟨1724129, by rfl⟩ : syracuseStep 2298839 = 3448259) B3448259
theorem B5818949 : Blo 2297435 5818949 := bbase (se 4 (by rfl) ⟨545526, by rfl⟩ : syracuseStep 5818949 = 1091053) (by norm_num)
theorem B3879299 : Blo 2297435 3879299 := bstep (se 1 (by rfl) ⟨2909474, by rfl⟩ : syracuseStep 3879299 = 5818949) B5818949
theorem B2586199 : Blo 2297435 2586199 := bstep (se 1 (by rfl) ⟨1939649, by rfl⟩ : syracuseStep 2586199 = 3879299) B3879299
theorem B3448265 : Blo 2297435 3448265 := bstep (se 2 (by rfl) ⟨1293099, by rfl⟩ : syracuseStep 3448265 = 2586199) B2586199
theorem B2298843 : Blo 2297435 2298843 := bstep (se 1 (by rfl) ⟨1724132, by rfl⟩ : syracuseStep 2298843 = 3448265) B3448265
theorem B2761733 : Blo 2297435 2761733 := bbase (se 4 (by rfl) ⟨258912, by rfl⟩ : syracuseStep 2761733 = 517825) (by norm_num)
theorem B7364621 : Blo 2297435 7364621 := bstep (se 3 (by rfl) ⟨1380866, by rfl⟩ : syracuseStep 7364621 = 2761733) B2761733
theorem B4909747 : Blo 2297435 4909747 := bstep (se 1 (by rfl) ⟨3682310, by rfl⟩ : syracuseStep 4909747 = 7364621) B7364621
theorem B6546329 : Blo 2297435 6546329 := bstep (se 2 (by rfl) ⟨2454873, by rfl⟩ : syracuseStep 6546329 = 4909747) B4909747
theorem B4364219 : Blo 2297435 4364219 := bstep (se 1 (by rfl) ⟨3273164, by rfl⟩ : syracuseStep 4364219 = 6546329) B6546329
theorem B11637917 : Blo 2297435 11637917 := bstep (se 3 (by rfl) ⟨2182109, by rfl⟩ : syracuseStep 11637917 = 4364219) B4364219
theorem B7758611 : Blo 2297435 7758611 := bstep (se 1 (by rfl) ⟨5818958, by rfl⟩ : syracuseStep 7758611 = 11637917) B11637917
theorem B5172407 : Blo 2297435 5172407 := bstep (se 1 (by rfl) ⟨3879305, by rfl⟩ : syracuseStep 5172407 = 7758611) B7758611
theorem B3448271 : Blo 2297435 3448271 := bstep (se 1 (by rfl) ⟨2586203, by rfl⟩ : syracuseStep 3448271 = 5172407) B5172407
theorem B2298847 : Blo 2297435 2298847 := bstep (se 1 (by rfl) ⟨1724135, by rfl⟩ : syracuseStep 2298847 = 3448271) B3448271
theorem B3448277 : Blo 2297435 3448277 := bbase (se 7 (by rfl) ⟨40409, by rfl⟩ : syracuseStep 3448277 = 80819) (by norm_num)
theorem B2298851 : Blo 2297435 2298851 := bstep (se 1 (by rfl) ⟨1724138, by rfl⟩ : syracuseStep 2298851 = 3448277) B3448277
theorem B8728469 : Blo 2297435 8728469 := bbase (se 6 (by rfl) ⟨204573, by rfl⟩ : syracuseStep 8728469 = 409147) (by norm_num)
theorem B5818979 : Blo 2297435 5818979 := bstep (se 1 (by rfl) ⟨4364234, by rfl⟩ : syracuseStep 5818979 = 8728469) B8728469
theorem B3879319 : Blo 2297435 3879319 := bstep (se 1 (by rfl) ⟨2909489, by rfl⟩ : syracuseStep 3879319 = 5818979) B5818979
theorem B5172425 : Blo 2297435 5172425 := bstep (se 2 (by rfl) ⟨1939659, by rfl⟩ : syracuseStep 5172425 = 3879319) B3879319
theorem B3448283 : Blo 2297435 3448283 := bstep (se 1 (by rfl) ⟨2586212, by rfl⟩ : syracuseStep 3448283 = 5172425) B5172425
theorem B2298855 : Blo 2297435 2298855 := bstep (se 1 (by rfl) ⟨1724141, by rfl⟩ : syracuseStep 2298855 = 3448283) B3448283
theorem B2586217 : Blo 2297435 2586217 := bbase (se 2 (by rfl) ⟨969831, by rfl⟩ : syracuseStep 2586217 = 1939663) (by norm_num)
theorem B3448289 : Blo 2297435 3448289 := bstep (se 2 (by rfl) ⟨1293108, by rfl⟩ : syracuseStep 3448289 = 2586217) B2586217
theorem B2298859 : Blo 2297435 2298859 := bstep (se 1 (by rfl) ⟨1724144, by rfl⟩ : syracuseStep 2298859 = 3448289) B3448289
theorem B4909781 : Blo 2297435 4909781 := bbase (se 7 (by rfl) ⟨57536, by rfl⟩ : syracuseStep 4909781 = 115073) (by norm_num)
theorem B13092749 : Blo 2297435 13092749 := bstep (se 3 (by rfl) ⟨2454890, by rfl⟩ : syracuseStep 13092749 = 4909781) B4909781
theorem B8728499 : Blo 2297435 8728499 := bstep (se 1 (by rfl) ⟨6546374, by rfl⟩ : syracuseStep 8728499 = 13092749) B13092749
theorem B5818999 : Blo 2297435 5818999 := bstep (se 1 (by rfl) ⟨4364249, by rfl⟩ : syracuseStep 5818999 = 8728499) B8728499
theorem B7758665 : Blo 2297435 7758665 := bstep (se 2 (by rfl) ⟨2909499, by rfl⟩ : syracuseStep 7758665 = 5818999) B5818999
theorem B5172443 : Blo 2297435 5172443 := bstep (se 1 (by rfl) ⟨3879332, by rfl⟩ : syracuseStep 5172443 = 7758665) B7758665
theorem B3448295 : Blo 2297435 3448295 := bstep (se 1 (by rfl) ⟨2586221, by rfl⟩ : syracuseStep 3448295 = 5172443) B5172443
theorem B2298863 : Blo 2297435 2298863 := bstep (se 1 (by rfl) ⟨1724147, by rfl⟩ : syracuseStep 2298863 = 3448295) B3448295
theorem B3448301 : Blo 2297435 3448301 := bbase (se 3 (by rfl) ⟨646556, by rfl⟩ : syracuseStep 3448301 = 1293113) (by norm_num)
theorem B2298867 : Blo 2297435 2298867 := bstep (se 1 (by rfl) ⟨1724150, by rfl⟩ : syracuseStep 2298867 = 3448301) B3448301
theorem B5172461 : Blo 2297435 5172461 := bbase (se 3 (by rfl) ⟨969836, by rfl⟩ : syracuseStep 5172461 = 1939673) (by norm_num)
theorem B3448307 : Blo 2297435 3448307 := bstep (se 1 (by rfl) ⟨2586230, by rfl⟩ : syracuseStep 3448307 = 5172461) B5172461
theorem B2298871 : Blo 2297435 2298871 := bstep (se 1 (by rfl) ⟨1724153, by rfl⟩ : syracuseStep 2298871 = 3448307) B3448307
theorem B3273205 : Blo 2297435 3273205 := bbase (se 5 (by rfl) ⟨153431, by rfl⟩ : syracuseStep 3273205 = 306863) (by norm_num)
theorem B4364273 : Blo 2297435 4364273 := bstep (se 2 (by rfl) ⟨1636602, by rfl⟩ : syracuseStep 4364273 = 3273205) B3273205
theorem B2909515 : Blo 2297435 2909515 := bstep (se 1 (by rfl) ⟨2182136, by rfl⟩ : syracuseStep 2909515 = 4364273) B4364273
theorem B3879353 : Blo 2297435 3879353 := bstep (se 2 (by rfl) ⟨1454757, by rfl⟩ : syracuseStep 3879353 = 2909515) B2909515
theorem B2586235 : Blo 2297435 2586235 := bstep (se 1 (by rfl) ⟨1939676, by rfl⟩ : syracuseStep 2586235 = 3879353) B3879353
theorem B3448313 : Blo 2297435 3448313 := bstep (se 2 (by rfl) ⟨1293117, by rfl⟩ : syracuseStep 3448313 = 2586235) B2586235
theorem B2298875 : Blo 2297435 2298875 := bstep (se 1 (by rfl) ⟨1724156, by rfl⟩ : syracuseStep 2298875 = 3448313) B3448313
theorem B2621525 : Blo 2297435 2621525 := bbase (se 8 (by rfl) ⟨15360, by rfl⟩ : syracuseStep 2621525 = 30721) (by norm_num)
theorem B6990733 : Blo 2297435 6990733 := bstep (se 3 (by rfl) ⟨1310762, by rfl⟩ : syracuseStep 6990733 = 2621525) B2621525
theorem B9320977 : Blo 2297435 9320977 := bstep (se 2 (by rfl) ⟨3495366, by rfl⟩ : syracuseStep 9320977 = 6990733) B6990733
theorem B49711877 : Blo 2297435 49711877 := bstep (se 4 (by rfl) ⟨4660488, by rfl⟩ : syracuseStep 49711877 = 9320977) B9320977
theorem B33141251 : Blo 2297435 33141251 := bstep (se 1 (by rfl) ⟨24855938, by rfl⟩ : syracuseStep 33141251 = 49711877) B49711877
theorem B88376669 : Blo 2297435 88376669 := bstep (se 3 (by rfl) ⟨16570625, by rfl⟩ : syracuseStep 88376669 = 33141251) B33141251
theorem B58917779 : Blo 2297435 58917779 := bstep (se 1 (by rfl) ⟨44188334, by rfl⟩ : syracuseStep 58917779 = 88376669) B88376669
theorem B39278519 : Blo 2297435 39278519 := bstep (se 1 (by rfl) ⟨29458889, by rfl⟩ : syracuseStep 39278519 = 58917779) B58917779
theorem B26185679 : Blo 2297435 26185679 := bstep (se 1 (by rfl) ⟨19639259, by rfl⟩ : syracuseStep 26185679 = 39278519) B39278519
theorem B17457119 : Blo 2297435 17457119 := bstep (se 1 (by rfl) ⟨13092839, by rfl⟩ : syracuseStep 17457119 = 26185679) B26185679
theorem B11638079 : Blo 2297435 11638079 := bstep (se 1 (by rfl) ⟨8728559, by rfl⟩ : syracuseStep 11638079 = 17457119) B17457119
theorem B7758719 : Blo 2297435 7758719 := bstep (se 1 (by rfl) ⟨5819039, by rfl⟩ : syracuseStep 7758719 = 11638079) B11638079
theorem B5172479 : Blo 2297435 5172479 := bstep (se 1 (by rfl) ⟨3879359, by rfl⟩ : syracuseStep 5172479 = 7758719) B7758719
theorem B3448319 : Blo 2297435 3448319 := bstep (se 1 (by rfl) ⟨2586239, by rfl⟩ : syracuseStep 3448319 = 5172479) B5172479
theorem B2298879 : Blo 2297435 2298879 := bstep (se 1 (by rfl) ⟨1724159, by rfl⟩ : syracuseStep 2298879 = 3448319) B3448319
theorem B3448325 : Blo 2297435 3448325 := bbase (se 4 (by rfl) ⟨323280, by rfl⟩ : syracuseStep 3448325 = 646561) (by norm_num)
theorem B2298883 : Blo 2297435 2298883 := bstep (se 1 (by rfl) ⟨1724162, by rfl⟩ : syracuseStep 2298883 = 3448325) B3448325
theorem B3879373 : Blo 2297435 3879373 := bbase (se 3 (by rfl) ⟨727382, by rfl⟩ : syracuseStep 3879373 = 1454765) (by norm_num)
theorem B5172497 : Blo 2297435 5172497 := bstep (se 2 (by rfl) ⟨1939686, by rfl⟩ : syracuseStep 5172497 = 3879373) B3879373
theorem B3448331 : Blo 2297435 3448331 := bstep (se 1 (by rfl) ⟨2586248, by rfl⟩ : syracuseStep 3448331 = 5172497) B5172497
theorem B2298887 : Blo 2297435 2298887 := bstep (se 1 (by rfl) ⟨1724165, by rfl⟩ : syracuseStep 2298887 = 3448331) B3448331
theorem B2586253 : Blo 2297435 2586253 := bbase (se 3 (by rfl) ⟨484922, by rfl⟩ : syracuseStep 2586253 = 969845) (by norm_num)
theorem B3448337 : Blo 2297435 3448337 := bstep (se 2 (by rfl) ⟨1293126, by rfl⟩ : syracuseStep 3448337 = 2586253) B2586253
theorem B2298891 : Blo 2297435 2298891 := bstep (se 1 (by rfl) ⟨1724168, by rfl⟩ : syracuseStep 2298891 = 3448337) B3448337
theorem B7758773 : Blo 2297435 7758773 := bbase (se 5 (by rfl) ⟨363692, by rfl⟩ : syracuseStep 7758773 = 727385) (by norm_num)
theorem B5172515 : Blo 2297435 5172515 := bstep (se 1 (by rfl) ⟨3879386, by rfl⟩ : syracuseStep 5172515 = 7758773) B7758773
theorem B3448343 : Blo 2297435 3448343 := bstep (se 1 (by rfl) ⟨2586257, by rfl⟩ : syracuseStep 3448343 = 5172515) B5172515
theorem B2298895 : Blo 2297435 2298895 := bstep (se 1 (by rfl) ⟨1724171, by rfl⟩ : syracuseStep 2298895 = 3448343) B3448343
theorem B3448349 : Blo 2297435 3448349 := bbase (se 3 (by rfl) ⟨646565, by rfl⟩ : syracuseStep 3448349 = 1293131) (by norm_num)
theorem B2298899 : Blo 2297435 2298899 := bstep (se 1 (by rfl) ⟨1724174, by rfl⟩ : syracuseStep 2298899 = 3448349) B3448349
theorem B5172533 : Blo 2297435 5172533 := bbase (se 5 (by rfl) ⟨242462, by rfl⟩ : syracuseStep 5172533 = 484925) (by norm_num)
theorem B3448355 : Blo 2297435 3448355 := bstep (se 1 (by rfl) ⟨2586266, by rfl⟩ : syracuseStep 3448355 = 5172533) B5172533
theorem B2298903 : Blo 2297435 2298903 := bstep (se 1 (by rfl) ⟨1724177, by rfl⟩ : syracuseStep 2298903 = 3448355) B3448355
theorem B5978981 : Blo 2297435 5978981 := bbase (se 4 (by rfl) ⟨560529, by rfl⟩ : syracuseStep 5978981 = 1121059) (by norm_num)
theorem B15943949 : Blo 2297435 15943949 := bstep (se 3 (by rfl) ⟨2989490, by rfl⟩ : syracuseStep 15943949 = 5978981) B5978981
theorem B10629299 : Blo 2297435 10629299 := bstep (se 1 (by rfl) ⟨7971974, by rfl⟩ : syracuseStep 10629299 = 15943949) B15943949
theorem B7086199 : Blo 2297435 7086199 := bstep (se 1 (by rfl) ⟨5314649, by rfl⟩ : syracuseStep 7086199 = 10629299) B10629299
theorem B9448265 : Blo 2297435 9448265 := bstep (se 2 (by rfl) ⟨3543099, by rfl⟩ : syracuseStep 9448265 = 7086199) B7086199
theorem B25195373 : Blo 2297435 25195373 := bstep (se 3 (by rfl) ⟨4724132, by rfl⟩ : syracuseStep 25195373 = 9448265) B9448265
theorem B16796915 : Blo 2297435 16796915 := bstep (se 1 (by rfl) ⟨12597686, by rfl⟩ : syracuseStep 16796915 = 25195373) B25195373
theorem B11197943 : Blo 2297435 11197943 := bstep (se 1 (by rfl) ⟨8398457, by rfl⟩ : syracuseStep 11197943 = 16796915) B16796915
theorem B7465295 : Blo 2297435 7465295 := bstep (se 1 (by rfl) ⟨5598971, by rfl⟩ : syracuseStep 7465295 = 11197943) B11197943
theorem B19907453 : Blo 2297435 19907453 := bstep (se 3 (by rfl) ⟨3732647, by rfl⟩ : syracuseStep 19907453 = 7465295) B7465295
theorem B13271635 : Blo 2297435 13271635 := bstep (se 1 (by rfl) ⟨9953726, by rfl⟩ : syracuseStep 13271635 = 19907453) B19907453
theorem B17695513 : Blo 2297435 17695513 := bstep (se 2 (by rfl) ⟨6635817, by rfl⟩ : syracuseStep 17695513 = 13271635) B13271635
theorem B23594017 : Blo 2297435 23594017 := bstep (se 2 (by rfl) ⟨8847756, by rfl⟩ : syracuseStep 23594017 = 17695513) B17695513
theorem B31458689 : Blo 2297435 31458689 := bstep (se 2 (by rfl) ⟨11797008, by rfl⟩ : syracuseStep 31458689 = 23594017) B23594017
theorem B20972459 : Blo 2297435 20972459 := bstep (se 1 (by rfl) ⟨15729344, by rfl⟩ : syracuseStep 20972459 = 31458689) B31458689
theorem B55926557 : Blo 2297435 55926557 := bstep (se 3 (by rfl) ⟨10486229, by rfl⟩ : syracuseStep 55926557 = 20972459) B20972459
theorem B37284371 : Blo 2297435 37284371 := bstep (se 1 (by rfl) ⟨27963278, by rfl⟩ : syracuseStep 37284371 = 55926557) B55926557
theorem B24856247 : Blo 2297435 24856247 := bstep (se 1 (by rfl) ⟨18642185, by rfl⟩ : syracuseStep 24856247 = 37284371) B37284371
theorem B16570831 : Blo 2297435 16570831 := bstep (se 1 (by rfl) ⟨12428123, by rfl⟩ : syracuseStep 16570831 = 24856247) B24856247
theorem B22094441 : Blo 2297435 22094441 := bstep (se 2 (by rfl) ⟨8285415, by rfl⟩ : syracuseStep 22094441 = 16570831) B16570831
theorem B14729627 : Blo 2297435 14729627 := bstep (se 1 (by rfl) ⟨11047220, by rfl⟩ : syracuseStep 14729627 = 22094441) B22094441
theorem B9819751 : Blo 2297435 9819751 := bstep (se 1 (by rfl) ⟨7364813, by rfl⟩ : syracuseStep 9819751 = 14729627) B14729627
theorem B13093001 : Blo 2297435 13093001 := bstep (se 2 (by rfl) ⟨4909875, by rfl⟩ : syracuseStep 13093001 = 9819751) B9819751
theorem B8728667 : Blo 2297435 8728667 := bstep (se 1 (by rfl) ⟨6546500, by rfl⟩ : syracuseStep 8728667 = 13093001) B13093001
theorem B5819111 : Blo 2297435 5819111 := bstep (se 1 (by rfl) ⟨4364333, by rfl⟩ : syracuseStep 5819111 = 8728667) B8728667
theorem B3879407 : Blo 2297435 3879407 := bstep (se 1 (by rfl) ⟨2909555, by rfl⟩ : syracuseStep 3879407 = 5819111) B5819111
theorem B2586271 : Blo 2297435 2586271 := bstep (se 1 (by rfl) ⟨1939703, by rfl⟩ : syracuseStep 2586271 = 3879407) B3879407
theorem B3448361 : Blo 2297435 3448361 := bstep (se 2 (by rfl) ⟨1293135, by rfl⟩ : syracuseStep 3448361 = 2586271) B2586271
theorem B2298907 : Blo 2297435 2298907 := bstep (se 1 (by rfl) ⟨1724180, by rfl⟩ : syracuseStep 2298907 = 3448361) B3448361
theorem B8285429 : Blo 2297435 8285429 := bbase (se 5 (by rfl) ⟨388379, by rfl⟩ : syracuseStep 8285429 = 776759) (by norm_num)
theorem B22094477 : Blo 2297435 22094477 := bstep (se 3 (by rfl) ⟨4142714, by rfl⟩ : syracuseStep 22094477 = 8285429) B8285429
theorem B14729651 : Blo 2297435 14729651 := bstep (se 1 (by rfl) ⟨11047238, by rfl⟩ : syracuseStep 14729651 = 22094477) B22094477
theorem B9819767 : Blo 2297435 9819767 := bstep (se 1 (by rfl) ⟨7364825, by rfl⟩ : syracuseStep 9819767 = 14729651) B14729651
theorem B6546511 : Blo 2297435 6546511 := bstep (se 1 (by rfl) ⟨4909883, by rfl⟩ : syracuseStep 6546511 = 9819767) B9819767
theorem B8728681 : Blo 2297435 8728681 := bstep (se 2 (by rfl) ⟨3273255, by rfl⟩ : syracuseStep 8728681 = 6546511) B6546511
theorem B11638241 : Blo 2297435 11638241 := bstep (se 2 (by rfl) ⟨4364340, by rfl⟩ : syracuseStep 11638241 = 8728681) B8728681
theorem B7758827 : Blo 2297435 7758827 := bstep (se 1 (by rfl) ⟨5819120, by rfl⟩ : syracuseStep 7758827 = 11638241) B11638241
theorem B5172551 : Blo 2297435 5172551 := bstep (se 1 (by rfl) ⟨3879413, by rfl⟩ : syracuseStep 5172551 = 7758827) B7758827
theorem B3448367 : Blo 2297435 3448367 := bstep (se 1 (by rfl) ⟨2586275, by rfl⟩ : syracuseStep 3448367 = 5172551) B5172551
theorem B2298911 : Blo 2297435 2298911 := bstep (se 1 (by rfl) ⟨1724183, by rfl⟩ : syracuseStep 2298911 = 3448367) B3448367
theorem B3448373 : Blo 2297435 3448373 := bbase (se 5 (by rfl) ⟨161642, by rfl⟩ : syracuseStep 3448373 = 323285) (by norm_num)
theorem B2298915 : Blo 2297435 2298915 := bstep (se 1 (by rfl) ⟨1724186, by rfl⟩ : syracuseStep 2298915 = 3448373) B3448373
theorem B5819141 : Blo 2297435 5819141 := bbase (se 4 (by rfl) ⟨545544, by rfl⟩ : syracuseStep 5819141 = 1091089) (by norm_num)
theorem B3879427 : Blo 2297435 3879427 := bstep (se 1 (by rfl) ⟨2909570, by rfl⟩ : syracuseStep 3879427 = 5819141) B5819141
theorem B5172569 : Blo 2297435 5172569 := bstep (se 2 (by rfl) ⟨1939713, by rfl⟩ : syracuseStep 5172569 = 3879427) B3879427
theorem B3448379 : Blo 2297435 3448379 := bstep (se 1 (by rfl) ⟨2586284, by rfl⟩ : syracuseStep 3448379 = 5172569) B5172569
theorem B2298919 : Blo 2297435 2298919 := bstep (se 1 (by rfl) ⟨1724189, by rfl⟩ : syracuseStep 2298919 = 3448379) B3448379
theorem B2586289 : Blo 2297435 2586289 := bbase (se 2 (by rfl) ⟨969858, by rfl⟩ : syracuseStep 2586289 = 1939717) (by norm_num)
theorem B3448385 : Blo 2297435 3448385 := bstep (se 2 (by rfl) ⟨1293144, by rfl⟩ : syracuseStep 3448385 = 2586289) B2586289
theorem B2298923 : Blo 2297435 2298923 := bstep (se 1 (by rfl) ⟨1724192, by rfl⟩ : syracuseStep 2298923 = 3448385) B3448385
theorem B6214117 : Blo 2297435 6214117 := bbase (se 4 (by rfl) ⟨582573, by rfl⟩ : syracuseStep 6214117 = 1165147) (by norm_num)
theorem B8285489 : Blo 2297435 8285489 := bstep (se 2 (by rfl) ⟨3107058, by rfl⟩ : syracuseStep 8285489 = 6214117) B6214117
theorem B5523659 : Blo 2297435 5523659 := bstep (se 1 (by rfl) ⟨4142744, by rfl⟩ : syracuseStep 5523659 = 8285489) B8285489
theorem B3682439 : Blo 2297435 3682439 := bstep (se 1 (by rfl) ⟨2761829, by rfl⟩ : syracuseStep 3682439 = 5523659) B5523659
theorem B2454959 : Blo 2297435 2454959 := bstep (se 1 (by rfl) ⟨1841219, by rfl⟩ : syracuseStep 2454959 = 3682439) B3682439
theorem B6546557 : Blo 2297435 6546557 := bstep (se 3 (by rfl) ⟨1227479, by rfl⟩ : syracuseStep 6546557 = 2454959) B2454959
theorem B4364371 : Blo 2297435 4364371 := bstep (se 1 (by rfl) ⟨3273278, by rfl⟩ : syracuseStep 4364371 = 6546557) B6546557
theorem B5819161 : Blo 2297435 5819161 := bstep (se 2 (by rfl) ⟨2182185, by rfl⟩ : syracuseStep 5819161 = 4364371) B4364371
theorem B7758881 : Blo 2297435 7758881 := bstep (se 2 (by rfl) ⟨2909580, by rfl⟩ : syracuseStep 7758881 = 5819161) B5819161
theorem B5172587 : Blo 2297435 5172587 := bstep (se 1 (by rfl) ⟨3879440, by rfl⟩ : syracuseStep 5172587 = 7758881) B7758881
theorem B3448391 : Blo 2297435 3448391 := bstep (se 1 (by rfl) ⟨2586293, by rfl⟩ : syracuseStep 3448391 = 5172587) B5172587
theorem B2298927 : Blo 2297435 2298927 := bstep (se 1 (by rfl) ⟨1724195, by rfl⟩ : syracuseStep 2298927 = 3448391) B3448391
theorem B3448397 : Blo 2297435 3448397 := bbase (se 3 (by rfl) ⟨646574, by rfl⟩ : syracuseStep 3448397 = 1293149) (by norm_num)
theorem B2298931 : Blo 2297435 2298931 := bstep (se 1 (by rfl) ⟨1724198, by rfl⟩ : syracuseStep 2298931 = 3448397) B3448397
theorem B5172605 : Blo 2297435 5172605 := bbase (se 3 (by rfl) ⟨969863, by rfl⟩ : syracuseStep 5172605 = 1939727) (by norm_num)
theorem B3448403 : Blo 2297435 3448403 := bstep (se 1 (by rfl) ⟨2586302, by rfl⟩ : syracuseStep 3448403 = 5172605) B5172605
theorem B2298935 : Blo 2297435 2298935 := bstep (se 1 (by rfl) ⟨1724201, by rfl⟩ : syracuseStep 2298935 = 3448403) B3448403
theorem B3879461 : Blo 2297435 3879461 := bbase (se 4 (by rfl) ⟨363699, by rfl⟩ : syracuseStep 3879461 = 727399) (by norm_num)
theorem B2586307 : Blo 2297435 2586307 := bstep (se 1 (by rfl) ⟨1939730, by rfl⟩ : syracuseStep 2586307 = 3879461) B3879461
theorem B3448409 : Blo 2297435 3448409 := bstep (se 2 (by rfl) ⟨1293153, by rfl⟩ : syracuseStep 3448409 = 2586307) B2586307
theorem B2298939 : Blo 2297435 2298939 := bstep (se 1 (by rfl) ⟨1724204, by rfl⟩ : syracuseStep 2298939 = 3448409) B3448409
theorem B3273301 : Blo 2297435 3273301 := bbase (se 8 (by rfl) ⟨19179, by rfl⟩ : syracuseStep 3273301 = 38359) (by norm_num)
theorem B17457605 : Blo 2297435 17457605 := bstep (se 4 (by rfl) ⟨1636650, by rfl⟩ : syracuseStep 17457605 = 3273301) B3273301
theorem B11638403 : Blo 2297435 11638403 := bstep (se 1 (by rfl) ⟨8728802, by rfl⟩ : syracuseStep 11638403 = 17457605) B17457605
theorem B7758935 : Blo 2297435 7758935 := bstep (se 1 (by rfl) ⟨5819201, by rfl⟩ : syracuseStep 7758935 = 11638403) B11638403
theorem B5172623 : Blo 2297435 5172623 := bstep (se 1 (by rfl) ⟨3879467, by rfl⟩ : syracuseStep 5172623 = 7758935) B7758935
theorem B3448415 : Blo 2297435 3448415 := bstep (se 1 (by rfl) ⟨2586311, by rfl⟩ : syracuseStep 3448415 = 5172623) B5172623
theorem B2298943 : Blo 2297435 2298943 := bstep (se 1 (by rfl) ⟨1724207, by rfl⟩ : syracuseStep 2298943 = 3448415) B3448415
theorem B3448421 : Blo 2297435 3448421 := bbase (se 4 (by rfl) ⟨323289, by rfl⟩ : syracuseStep 3448421 = 646579) (by norm_num)
theorem B2298947 : Blo 2297435 2298947 := bstep (se 1 (by rfl) ⟨1724210, by rfl⟩ : syracuseStep 2298947 = 3448421) B3448421
theorem B2454985 : Blo 2297435 2454985 := bbase (se 2 (by rfl) ⟨920619, by rfl⟩ : syracuseStep 2454985 = 1841239) (by norm_num)
theorem B3273313 : Blo 2297435 3273313 := bstep (se 2 (by rfl) ⟨1227492, by rfl⟩ : syracuseStep 3273313 = 2454985) B2454985
theorem B4364417 : Blo 2297435 4364417 := bstep (se 2 (by rfl) ⟨1636656, by rfl⟩ : syracuseStep 4364417 = 3273313) B3273313
theorem B2909611 : Blo 2297435 2909611 := bstep (se 1 (by rfl) ⟨2182208, by rfl⟩ : syracuseStep 2909611 = 4364417) B4364417
theorem B3879481 : Blo 2297435 3879481 := bstep (se 2 (by rfl) ⟨1454805, by rfl⟩ : syracuseStep 3879481 = 2909611) B2909611
theorem B5172641 : Blo 2297435 5172641 := bstep (se 2 (by rfl) ⟨1939740, by rfl⟩ : syracuseStep 5172641 = 3879481) B3879481
theorem B3448427 : Blo 2297435 3448427 := bstep (se 1 (by rfl) ⟨2586320, by rfl⟩ : syracuseStep 3448427 = 5172641) B5172641
theorem B2298951 : Blo 2297435 2298951 := bstep (se 1 (by rfl) ⟨1724213, by rfl⟩ : syracuseStep 2298951 = 3448427) B3448427
theorem B2586325 : Blo 2297435 2586325 := bbase (se 7 (by rfl) ⟨30308, by rfl⟩ : syracuseStep 2586325 = 60617) (by norm_num)
theorem B3448433 : Blo 2297435 3448433 := bstep (se 2 (by rfl) ⟨1293162, by rfl⟩ : syracuseStep 3448433 = 2586325) B2586325
theorem B2298955 : Blo 2297435 2298955 := bstep (se 1 (by rfl) ⟨1724216, by rfl⟩ : syracuseStep 2298955 = 3448433) B3448433
theorem B2909621 : Blo 2297435 2909621 := bbase (se 5 (by rfl) ⟨136388, by rfl⟩ : syracuseStep 2909621 = 272777) (by norm_num)
theorem B7758989 : Blo 2297435 7758989 := bstep (se 3 (by rfl) ⟨1454810, by rfl⟩ : syracuseStep 7758989 = 2909621) B2909621
theorem B5172659 : Blo 2297435 5172659 := bstep (se 1 (by rfl) ⟨3879494, by rfl⟩ : syracuseStep 5172659 = 7758989) B7758989
theorem B3448439 : Blo 2297435 3448439 := bstep (se 1 (by rfl) ⟨2586329, by rfl⟩ : syracuseStep 3448439 = 5172659) B5172659
theorem B2298959 : Blo 2297435 2298959 := bstep (se 1 (by rfl) ⟨1724219, by rfl⟩ : syracuseStep 2298959 = 3448439) B3448439
theorem B3448445 : Blo 2297435 3448445 := bbase (se 3 (by rfl) ⟨646583, by rfl⟩ : syracuseStep 3448445 = 1293167) (by norm_num)
theorem B2298963 : Blo 2297435 2298963 := bstep (se 1 (by rfl) ⟨1724222, by rfl⟩ : syracuseStep 2298963 = 3448445) B3448445
theorem B5172677 : Blo 2297435 5172677 := bbase (se 4 (by rfl) ⟨484938, by rfl⟩ : syracuseStep 5172677 = 969877) (by norm_num)
theorem B3448451 : Blo 2297435 3448451 := bstep (se 1 (by rfl) ⟨2586338, by rfl⟩ : syracuseStep 3448451 = 5172677) B5172677
theorem B2298967 : Blo 2297435 2298967 := bstep (se 1 (by rfl) ⟨1724225, by rfl⟩ : syracuseStep 2298967 = 3448451) B3448451
theorem B5979149 : Blo 2297435 5979149 := bbase (se 3 (by rfl) ⟨1121090, by rfl⟩ : syracuseStep 5979149 = 2242181) (by norm_num)
theorem B3986099 : Blo 2297435 3986099 := bstep (se 1 (by rfl) ⟨2989574, by rfl⟩ : syracuseStep 3986099 = 5979149) B5979149
theorem B2657399 : Blo 2297435 2657399 := bstep (se 1 (by rfl) ⟨1993049, by rfl⟩ : syracuseStep 2657399 = 3986099) B3986099
theorem B28345589 : Blo 2297435 28345589 := bstep (se 5 (by rfl) ⟨1328699, by rfl⟩ : syracuseStep 28345589 = 2657399) B2657399
theorem B18897059 : Blo 2297435 18897059 := bstep (se 1 (by rfl) ⟨14172794, by rfl⟩ : syracuseStep 18897059 = 28345589) B28345589
theorem B12598039 : Blo 2297435 12598039 := bstep (se 1 (by rfl) ⟨9448529, by rfl⟩ : syracuseStep 12598039 = 18897059) B18897059
theorem B16797385 : Blo 2297435 16797385 := bstep (se 2 (by rfl) ⟨6299019, by rfl⟩ : syracuseStep 16797385 = 12598039) B12598039
theorem B22396513 : Blo 2297435 22396513 := bstep (se 2 (by rfl) ⟨8398692, by rfl⟩ : syracuseStep 22396513 = 16797385) B16797385
theorem B29862017 : Blo 2297435 29862017 := bstep (se 2 (by rfl) ⟨11198256, by rfl⟩ : syracuseStep 29862017 = 22396513) B22396513
theorem B19908011 : Blo 2297435 19908011 := bstep (se 1 (by rfl) ⟨14931008, by rfl⟩ : syracuseStep 19908011 = 29862017) B29862017
theorem B13272007 : Blo 2297435 13272007 := bstep (se 1 (by rfl) ⟨9954005, by rfl⟩ : syracuseStep 13272007 = 19908011) B19908011
theorem B17696009 : Blo 2297435 17696009 := bstep (se 2 (by rfl) ⟨6636003, by rfl⟩ : syracuseStep 17696009 = 13272007) B13272007
theorem B11797339 : Blo 2297435 11797339 := bstep (se 1 (by rfl) ⟨8848004, by rfl⟩ : syracuseStep 11797339 = 17696009) B17696009
theorem B15729785 : Blo 2297435 15729785 := bstep (se 2 (by rfl) ⟨5898669, by rfl⟩ : syracuseStep 15729785 = 11797339) B11797339
theorem B10486523 : Blo 2297435 10486523 := bstep (se 1 (by rfl) ⟨7864892, by rfl⟩ : syracuseStep 10486523 = 15729785) B15729785
theorem B27964061 : Blo 2297435 27964061 := bstep (se 3 (by rfl) ⟨5243261, by rfl⟩ : syracuseStep 27964061 = 10486523) B10486523
theorem B18642707 : Blo 2297435 18642707 := bstep (se 1 (by rfl) ⟨13982030, by rfl⟩ : syracuseStep 18642707 = 27964061) B27964061
theorem B12428471 : Blo 2297435 12428471 := bstep (se 1 (by rfl) ⟨9321353, by rfl⟩ : syracuseStep 12428471 = 18642707) B18642707
theorem B8285647 : Blo 2297435 8285647 := bstep (se 1 (by rfl) ⟨6214235, by rfl⟩ : syracuseStep 8285647 = 12428471) B12428471
theorem B11047529 : Blo 2297435 11047529 := bstep (se 2 (by rfl) ⟨4142823, by rfl⟩ : syracuseStep 11047529 = 8285647) B8285647
theorem B7365019 : Blo 2297435 7365019 := bstep (se 1 (by rfl) ⟨5523764, by rfl⟩ : syracuseStep 7365019 = 11047529) B11047529
theorem B9820025 : Blo 2297435 9820025 := bstep (se 2 (by rfl) ⟨3682509, by rfl⟩ : syracuseStep 9820025 = 7365019) B7365019
theorem B6546683 : Blo 2297435 6546683 := bstep (se 1 (by rfl) ⟨4910012, by rfl⟩ : syracuseStep 6546683 = 9820025) B9820025
theorem B4364455 : Blo 2297435 4364455 := bstep (se 1 (by rfl) ⟨3273341, by rfl⟩ : syracuseStep 4364455 = 6546683) B6546683
theorem B5819273 : Blo 2297435 5819273 := bstep (se 2 (by rfl) ⟨2182227, by rfl⟩ : syracuseStep 5819273 = 4364455) B4364455
theorem B3879515 : Blo 2297435 3879515 := bstep (se 1 (by rfl) ⟨2909636, by rfl⟩ : syracuseStep 3879515 = 5819273) B5819273
theorem B2586343 : Blo 2297435 2586343 := bstep (se 1 (by rfl) ⟨1939757, by rfl⟩ : syracuseStep 2586343 = 3879515) B3879515
theorem B3448457 : Blo 2297435 3448457 := bstep (se 2 (by rfl) ⟨1293171, by rfl⟩ : syracuseStep 3448457 = 2586343) B2586343
theorem B2298971 : Blo 2297435 2298971 := bstep (se 1 (by rfl) ⟨1724228, by rfl⟩ : syracuseStep 2298971 = 3448457) B3448457
theorem B11638565 : Blo 2297435 11638565 := bbase (se 4 (by rfl) ⟨1091115, by rfl⟩ : syracuseStep 11638565 = 2182231) (by norm_num)
theorem B7759043 : Blo 2297435 7759043 := bstep (se 1 (by rfl) ⟨5819282, by rfl⟩ : syracuseStep 7759043 = 11638565) B11638565
theorem B5172695 : Blo 2297435 5172695 := bstep (se 1 (by rfl) ⟨3879521, by rfl⟩ : syracuseStep 5172695 = 7759043) B7759043
theorem B3448463 : Blo 2297435 3448463 := bstep (se 1 (by rfl) ⟨2586347, by rfl⟩ : syracuseStep 3448463 = 5172695) B5172695
theorem B2298975 : Blo 2297435 2298975 := bstep (se 1 (by rfl) ⟨1724231, by rfl⟩ : syracuseStep 2298975 = 3448463) B3448463
theorem B3448469 : Blo 2297435 3448469 := bbase (se 6 (by rfl) ⟨80823, by rfl⟩ : syracuseStep 3448469 = 161647) (by norm_num)
theorem B2298979 : Blo 2297435 2298979 := bstep (se 1 (by rfl) ⟨1724234, by rfl⟩ : syracuseStep 2298979 = 3448469) B3448469
theorem B7864933 : Blo 2297435 7864933 := bbase (se 4 (by rfl) ⟨737337, by rfl⟩ : syracuseStep 7864933 = 1474675) (by norm_num)
theorem B10486577 : Blo 2297435 10486577 := bstep (se 2 (by rfl) ⟨3932466, by rfl⟩ : syracuseStep 10486577 = 7864933) B7864933
theorem B6991051 : Blo 2297435 6991051 := bstep (se 1 (by rfl) ⟨5243288, by rfl⟩ : syracuseStep 6991051 = 10486577) B10486577
theorem B9321401 : Blo 2297435 9321401 := bstep (se 2 (by rfl) ⟨3495525, by rfl⟩ : syracuseStep 9321401 = 6991051) B6991051
theorem B6214267 : Blo 2297435 6214267 := bstep (se 1 (by rfl) ⟨4660700, by rfl⟩ : syracuseStep 6214267 = 9321401) B9321401
theorem B8285689 : Blo 2297435 8285689 := bstep (se 2 (by rfl) ⟨3107133, by rfl⟩ : syracuseStep 8285689 = 6214267) B6214267
theorem B11047585 : Blo 2297435 11047585 := bstep (se 2 (by rfl) ⟨4142844, by rfl⟩ : syracuseStep 11047585 = 8285689) B8285689
theorem B14730113 : Blo 2297435 14730113 := bstep (se 2 (by rfl) ⟨5523792, by rfl⟩ : syracuseStep 14730113 = 11047585) B11047585
theorem B9820075 : Blo 2297435 9820075 := bstep (se 1 (by rfl) ⟨7365056, by rfl⟩ : syracuseStep 9820075 = 14730113) B14730113
theorem B13093433 : Blo 2297435 13093433 := bstep (se 2 (by rfl) ⟨4910037, by rfl⟩ : syracuseStep 13093433 = 9820075) B9820075
theorem B8728955 : Blo 2297435 8728955 := bstep (se 1 (by rfl) ⟨6546716, by rfl⟩ : syracuseStep 8728955 = 13093433) B13093433
theorem B5819303 : Blo 2297435 5819303 := bstep (se 1 (by rfl) ⟨4364477, by rfl⟩ : syracuseStep 5819303 = 8728955) B8728955
theorem B3879535 : Blo 2297435 3879535 := bstep (se 1 (by rfl) ⟨2909651, by rfl⟩ : syracuseStep 3879535 = 5819303) B5819303
theorem B5172713 : Blo 2297435 5172713 := bstep (se 2 (by rfl) ⟨1939767, by rfl⟩ : syracuseStep 5172713 = 3879535) B3879535
theorem B3448475 : Blo 2297435 3448475 := bstep (se 1 (by rfl) ⟨2586356, by rfl⟩ : syracuseStep 3448475 = 5172713) B5172713
theorem B2298983 : Blo 2297435 2298983 := bstep (se 1 (by rfl) ⟨1724237, by rfl⟩ : syracuseStep 2298983 = 3448475) B3448475
theorem B2586361 : Blo 2297435 2586361 := bbase (se 2 (by rfl) ⟨969885, by rfl⟩ : syracuseStep 2586361 = 1939771) (by norm_num)
theorem B3448481 : Blo 2297435 3448481 := bstep (se 2 (by rfl) ⟨1293180, by rfl⟩ : syracuseStep 3448481 = 2586361) B2586361
theorem B2298987 : Blo 2297435 2298987 := bstep (se 1 (by rfl) ⟨1724240, by rfl⟩ : syracuseStep 2298987 = 3448481) B3448481
theorem B3682541 : Blo 2297435 3682541 := bbase (se 3 (by rfl) ⟨690476, by rfl⟩ : syracuseStep 3682541 = 1380953) (by norm_num)
theorem B9820109 : Blo 2297435 9820109 := bstep (se 3 (by rfl) ⟨1841270, by rfl⟩ : syracuseStep 9820109 = 3682541) B3682541
theorem B6546739 : Blo 2297435 6546739 := bstep (se 1 (by rfl) ⟨4910054, by rfl⟩ : syracuseStep 6546739 = 9820109) B9820109
theorem B8728985 : Blo 2297435 8728985 := bstep (se 2 (by rfl) ⟨3273369, by rfl⟩ : syracuseStep 8728985 = 6546739) B6546739
theorem B5819323 : Blo 2297435 5819323 := bstep (se 1 (by rfl) ⟨4364492, by rfl⟩ : syracuseStep 5819323 = 8728985) B8728985
theorem B7759097 : Blo 2297435 7759097 := bstep (se 2 (by rfl) ⟨2909661, by rfl⟩ : syracuseStep 7759097 = 5819323) B5819323
theorem B5172731 : Blo 2297435 5172731 := bstep (se 1 (by rfl) ⟨3879548, by rfl⟩ : syracuseStep 5172731 = 7759097) B7759097
theorem B3448487 : Blo 2297435 3448487 := bstep (se 1 (by rfl) ⟨2586365, by rfl⟩ : syracuseStep 3448487 = 5172731) B5172731
theorem B2298991 : Blo 2297435 2298991 := bstep (se 1 (by rfl) ⟨1724243, by rfl⟩ : syracuseStep 2298991 = 3448487) B3448487
theorem B3448493 : Blo 2297435 3448493 := bbase (se 3 (by rfl) ⟨646592, by rfl⟩ : syracuseStep 3448493 = 1293185) (by norm_num)
theorem B2298995 : Blo 2297435 2298995 := bstep (se 1 (by rfl) ⟨1724246, by rfl⟩ : syracuseStep 2298995 = 3448493) B3448493
theorem B5172749 : Blo 2297435 5172749 := bbase (se 3 (by rfl) ⟨969890, by rfl⟩ : syracuseStep 5172749 = 1939781) (by norm_num)
theorem B3448499 : Blo 2297435 3448499 := bstep (se 1 (by rfl) ⟨2586374, by rfl⟩ : syracuseStep 3448499 = 5172749) B5172749
theorem B2298999 : Blo 2297435 2298999 := bstep (se 1 (by rfl) ⟨1724249, by rfl⟩ : syracuseStep 2298999 = 3448499) B3448499
theorem B2909677 : Blo 2297435 2909677 := bbase (se 3 (by rfl) ⟨545564, by rfl⟩ : syracuseStep 2909677 = 1091129) (by norm_num)
theorem B3879569 : Blo 2297435 3879569 := bstep (se 2 (by rfl) ⟨1454838, by rfl⟩ : syracuseStep 3879569 = 2909677) B2909677
theorem B2586379 : Blo 2297435 2586379 := bstep (se 1 (by rfl) ⟨1939784, by rfl⟩ : syracuseStep 2586379 = 3879569) B3879569
theorem B3448505 : Blo 2297435 3448505 := bstep (se 2 (by rfl) ⟨1293189, by rfl⟩ : syracuseStep 3448505 = 2586379) B2586379
theorem B2299003 : Blo 2297435 2299003 := bstep (se 1 (by rfl) ⟨1724252, by rfl⟩ : syracuseStep 2299003 = 3448505) B3448505
theorem B7465621 : Blo 2297435 7465621 := bbase (se 6 (by rfl) ⟨174975, by rfl⟩ : syracuseStep 7465621 = 349951) (by norm_num)
theorem B9954161 : Blo 2297435 9954161 := bstep (se 2 (by rfl) ⟨3732810, by rfl⟩ : syracuseStep 9954161 = 7465621) B7465621
theorem B6636107 : Blo 2297435 6636107 := bstep (se 1 (by rfl) ⟨4977080, by rfl⟩ : syracuseStep 6636107 = 9954161) B9954161
theorem B4424071 : Blo 2297435 4424071 := bstep (se 1 (by rfl) ⟨3318053, by rfl⟩ : syracuseStep 4424071 = 6636107) B6636107
theorem B5898761 : Blo 2297435 5898761 := bstep (se 2 (by rfl) ⟨2212035, by rfl⟩ : syracuseStep 5898761 = 4424071) B4424071
theorem B3932507 : Blo 2297435 3932507 := bstep (se 1 (by rfl) ⟨2949380, by rfl⟩ : syracuseStep 3932507 = 5898761) B5898761
theorem B10486685 : Blo 2297435 10486685 := bstep (se 3 (by rfl) ⟨1966253, by rfl⟩ : syracuseStep 10486685 = 3932507) B3932507
theorem B6991123 : Blo 2297435 6991123 := bstep (se 1 (by rfl) ⟨5243342, by rfl⟩ : syracuseStep 6991123 = 10486685) B10486685
theorem B9321497 : Blo 2297435 9321497 := bstep (se 2 (by rfl) ⟨3495561, by rfl⟩ : syracuseStep 9321497 = 6991123) B6991123
theorem B6214331 : Blo 2297435 6214331 := bstep (se 1 (by rfl) ⟨4660748, by rfl⟩ : syracuseStep 6214331 = 9321497) B9321497
theorem B16571549 : Blo 2297435 16571549 := bstep (se 3 (by rfl) ⟨3107165, by rfl⟩ : syracuseStep 16571549 = 6214331) B6214331
theorem B11047699 : Blo 2297435 11047699 := bstep (se 1 (by rfl) ⟨8285774, by rfl⟩ : syracuseStep 11047699 = 16571549) B16571549
theorem B14730265 : Blo 2297435 14730265 := bstep (se 2 (by rfl) ⟨5523849, by rfl⟩ : syracuseStep 14730265 = 11047699) B11047699
theorem B19640353 : Blo 2297435 19640353 := bstep (se 2 (by rfl) ⟨7365132, by rfl⟩ : syracuseStep 19640353 = 14730265) B14730265
theorem B26187137 : Blo 2297435 26187137 := bstep (se 2 (by rfl) ⟨9820176, by rfl⟩ : syracuseStep 26187137 = 19640353) B19640353
theorem B17458091 : Blo 2297435 17458091 := bstep (se 1 (by rfl) ⟨13093568, by rfl⟩ : syracuseStep 17458091 = 26187137) B26187137
theorem B11638727 : Blo 2297435 11638727 := bstep (se 1 (by rfl) ⟨8729045, by rfl⟩ : syracuseStep 11638727 = 17458091) B17458091
theorem B7759151 : Blo 2297435 7759151 := bstep (se 1 (by rfl) ⟨5819363, by rfl⟩ : syracuseStep 7759151 = 11638727) B11638727
theorem B5172767 : Blo 2297435 5172767 := bstep (se 1 (by rfl) ⟨3879575, by rfl⟩ : syracuseStep 5172767 = 7759151) B7759151
theorem B3448511 : Blo 2297435 3448511 := bstep (se 1 (by rfl) ⟨2586383, by rfl⟩ : syracuseStep 3448511 = 5172767) B5172767
theorem B2299007 : Blo 2297435 2299007 := bstep (se 1 (by rfl) ⟨1724255, by rfl⟩ : syracuseStep 2299007 = 3448511) B3448511
theorem B3448517 : Blo 2297435 3448517 := bbase (se 4 (by rfl) ⟨323298, by rfl⟩ : syracuseStep 3448517 = 646597) (by norm_num)
theorem B2299011 : Blo 2297435 2299011 := bstep (se 1 (by rfl) ⟨1724258, by rfl⟩ : syracuseStep 2299011 = 3448517) B3448517
theorem B3879589 : Blo 2297435 3879589 := bbase (se 4 (by rfl) ⟨363711, by rfl⟩ : syracuseStep 3879589 = 727423) (by norm_num)
theorem B5172785 : Blo 2297435 5172785 := bstep (se 2 (by rfl) ⟨1939794, by rfl⟩ : syracuseStep 5172785 = 3879589) B3879589
theorem B3448523 : Blo 2297435 3448523 := bstep (se 1 (by rfl) ⟨2586392, by rfl⟩ : syracuseStep 3448523 = 5172785) B5172785
theorem B2299015 : Blo 2297435 2299015 := bstep (se 1 (by rfl) ⟨1724261, by rfl⟩ : syracuseStep 2299015 = 3448523) B3448523
theorem B2586397 : Blo 2297435 2586397 := bbase (se 3 (by rfl) ⟨484949, by rfl⟩ : syracuseStep 2586397 = 969899) (by norm_num)
theorem B3448529 : Blo 2297435 3448529 := bstep (se 2 (by rfl) ⟨1293198, by rfl⟩ : syracuseStep 3448529 = 2586397) B2586397
theorem B2299019 : Blo 2297435 2299019 := bstep (se 1 (by rfl) ⟨1724264, by rfl⟩ : syracuseStep 2299019 = 3448529) B3448529
theorem B7759205 : Blo 2297435 7759205 := bbase (se 4 (by rfl) ⟨727425, by rfl⟩ : syracuseStep 7759205 = 1454851) (by norm_num)
theorem B5172803 : Blo 2297435 5172803 := bstep (se 1 (by rfl) ⟨3879602, by rfl⟩ : syracuseStep 5172803 = 7759205) B7759205
theorem B3448535 : Blo 2297435 3448535 := bstep (se 1 (by rfl) ⟨2586401, by rfl⟩ : syracuseStep 3448535 = 5172803) B5172803
theorem B2299023 : Blo 2297435 2299023 := bstep (se 1 (by rfl) ⟨1724267, by rfl⟩ : syracuseStep 2299023 = 3448535) B3448535
theorem B3448541 : Blo 2297435 3448541 := bbase (se 3 (by rfl) ⟨646601, by rfl⟩ : syracuseStep 3448541 = 1293203) (by norm_num)
theorem B2299027 : Blo 2297435 2299027 := bstep (se 1 (by rfl) ⟨1724270, by rfl⟩ : syracuseStep 2299027 = 3448541) B3448541
theorem B5172821 : Blo 2297435 5172821 := bbase (se 8 (by rfl) ⟨30309, by rfl⟩ : syracuseStep 5172821 = 60619) (by norm_num)
theorem B3448547 : Blo 2297435 3448547 := bstep (se 1 (by rfl) ⟨2586410, by rfl⟩ : syracuseStep 3448547 = 5172821) B5172821
theorem B2299031 : Blo 2297435 2299031 := bstep (se 1 (by rfl) ⟨1724273, by rfl⟩ : syracuseStep 2299031 = 3448547) B3448547
theorem B4910149 : Blo 2297435 4910149 := bbase (se 4 (by rfl) ⟨460326, by rfl⟩ : syracuseStep 4910149 = 920653) (by norm_num)
theorem B6546865 : Blo 2297435 6546865 := bstep (se 2 (by rfl) ⟨2455074, by rfl⟩ : syracuseStep 6546865 = 4910149) B4910149
theorem B8729153 : Blo 2297435 8729153 := bstep (se 2 (by rfl) ⟨3273432, by rfl⟩ : syracuseStep 8729153 = 6546865) B6546865
theorem B5819435 : Blo 2297435 5819435 := bstep (se 1 (by rfl) ⟨4364576, by rfl⟩ : syracuseStep 5819435 = 8729153) B8729153
theorem B3879623 : Blo 2297435 3879623 := bstep (se 1 (by rfl) ⟨2909717, by rfl⟩ : syracuseStep 3879623 = 5819435) B5819435
theorem B2586415 : Blo 2297435 2586415 := bstep (se 1 (by rfl) ⟨1939811, by rfl⟩ : syracuseStep 2586415 = 3879623) B3879623
theorem B3448553 : Blo 2297435 3448553 := bstep (se 2 (by rfl) ⟨1293207, by rfl⟩ : syracuseStep 3448553 = 2586415) B2586415
theorem B2299035 : Blo 2297435 2299035 := bstep (se 1 (by rfl) ⟨1724276, by rfl⟩ : syracuseStep 2299035 = 3448553) B3448553
theorem B5898845 : Blo 2297435 5898845 := bbase (se 3 (by rfl) ⟨1106033, by rfl⟩ : syracuseStep 5898845 = 2212067) (by norm_num)
theorem B3932563 : Blo 2297435 3932563 := bstep (se 1 (by rfl) ⟨2949422, by rfl⟩ : syracuseStep 3932563 = 5898845) B5898845
theorem B5243417 : Blo 2297435 5243417 := bstep (se 2 (by rfl) ⟨1966281, by rfl⟩ : syracuseStep 5243417 = 3932563) B3932563
theorem B3495611 : Blo 2297435 3495611 := bstep (se 1 (by rfl) ⟨2621708, by rfl⟩ : syracuseStep 3495611 = 5243417) B5243417
theorem B2330407 : Blo 2297435 2330407 := bstep (se 1 (by rfl) ⟨1747805, by rfl⟩ : syracuseStep 2330407 = 3495611) B3495611
theorem B3107209 : Blo 2297435 3107209 := bstep (se 2 (by rfl) ⟨1165203, by rfl⟩ : syracuseStep 3107209 = 2330407) B2330407
theorem B4142945 : Blo 2297435 4142945 := bstep (se 2 (by rfl) ⟨1553604, by rfl⟩ : syracuseStep 4142945 = 3107209) B3107209
theorem B11047853 : Blo 2297435 11047853 := bstep (se 3 (by rfl) ⟨2071472, by rfl⟩ : syracuseStep 11047853 = 4142945) B4142945
theorem B29460941 : Blo 2297435 29460941 := bstep (se 3 (by rfl) ⟨5523926, by rfl⟩ : syracuseStep 29460941 = 11047853) B11047853
theorem B19640627 : Blo 2297435 19640627 := bstep (se 1 (by rfl) ⟨14730470, by rfl⟩ : syracuseStep 19640627 = 29460941) B29460941
theorem B13093751 : Blo 2297435 13093751 := bstep (se 1 (by rfl) ⟨9820313, by rfl⟩ : syracuseStep 13093751 = 19640627) B19640627
theorem B8729167 : Blo 2297435 8729167 := bstep (se 1 (by rfl) ⟨6546875, by rfl⟩ : syracuseStep 8729167 = 13093751) B13093751
theorem B11638889 : Blo 2297435 11638889 := bstep (se 2 (by rfl) ⟨4364583, by rfl⟩ : syracuseStep 11638889 = 8729167) B8729167
theorem B7759259 : Blo 2297435 7759259 := bstep (se 1 (by rfl) ⟨5819444, by rfl⟩ : syracuseStep 7759259 = 11638889) B11638889
theorem B5172839 : Blo 2297435 5172839 := bstep (se 1 (by rfl) ⟨3879629, by rfl⟩ : syracuseStep 5172839 = 7759259) B7759259
theorem B3448559 : Blo 2297435 3448559 := bstep (se 1 (by rfl) ⟨2586419, by rfl⟩ : syracuseStep 3448559 = 5172839) B5172839
theorem B2299039 : Blo 2297435 2299039 := bstep (se 1 (by rfl) ⟨1724279, by rfl⟩ : syracuseStep 2299039 = 3448559) B3448559
theorem B3448565 : Blo 2297435 3448565 := bbase (se 5 (by rfl) ⟨161651, by rfl⟩ : syracuseStep 3448565 = 323303) (by norm_num)
theorem B2299043 : Blo 2297435 2299043 := bstep (se 1 (by rfl) ⟨1724282, by rfl⟩ : syracuseStep 2299043 = 3448565) B3448565
theorem B4424149 : Blo 2297435 4424149 := bbase (se 7 (by rfl) ⟨51845, by rfl⟩ : syracuseStep 4424149 = 103691) (by norm_num)
theorem B23595461 : Blo 2297435 23595461 := bstep (se 4 (by rfl) ⟨2212074, by rfl⟩ : syracuseStep 23595461 = 4424149) B4424149
theorem B15730307 : Blo 2297435 15730307 := bstep (se 1 (by rfl) ⟨11797730, by rfl⟩ : syracuseStep 15730307 = 23595461) B23595461
theorem B10486871 : Blo 2297435 10486871 := bstep (se 1 (by rfl) ⟨7865153, by rfl⟩ : syracuseStep 10486871 = 15730307) B15730307
theorem B6991247 : Blo 2297435 6991247 := bstep (se 1 (by rfl) ⟨5243435, by rfl⟩ : syracuseStep 6991247 = 10486871) B10486871
theorem B4660831 : Blo 2297435 4660831 := bstep (se 1 (by rfl) ⟨3495623, by rfl⟩ : syracuseStep 4660831 = 6991247) B6991247
theorem B6214441 : Blo 2297435 6214441 := bstep (se 2 (by rfl) ⟨2330415, by rfl⟩ : syracuseStep 6214441 = 4660831) B4660831
theorem B8285921 : Blo 2297435 8285921 := bstep (se 2 (by rfl) ⟨3107220, by rfl⟩ : syracuseStep 8285921 = 6214441) B6214441
theorem B5523947 : Blo 2297435 5523947 := bstep (se 1 (by rfl) ⟨4142960, by rfl⟩ : syracuseStep 5523947 = 8285921) B8285921
theorem B3682631 : Blo 2297435 3682631 := bstep (se 1 (by rfl) ⟨2761973, by rfl⟩ : syracuseStep 3682631 = 5523947) B5523947
theorem B9820349 : Blo 2297435 9820349 := bstep (se 3 (by rfl) ⟨1841315, by rfl⟩ : syracuseStep 9820349 = 3682631) B3682631
theorem B6546899 : Blo 2297435 6546899 := bstep (se 1 (by rfl) ⟨4910174, by rfl⟩ : syracuseStep 6546899 = 9820349) B9820349
theorem B4364599 : Blo 2297435 4364599 := bstep (se 1 (by rfl) ⟨3273449, by rfl⟩ : syracuseStep 4364599 = 6546899) B6546899
theorem B5819465 : Blo 2297435 5819465 := bstep (se 2 (by rfl) ⟨2182299, by rfl⟩ : syracuseStep 5819465 = 4364599) B4364599
theorem B3879643 : Blo 2297435 3879643 := bstep (se 1 (by rfl) ⟨2909732, by rfl⟩ : syracuseStep 3879643 = 5819465) B5819465
theorem B5172857 : Blo 2297435 5172857 := bstep (se 2 (by rfl) ⟨1939821, by rfl⟩ : syracuseStep 5172857 = 3879643) B3879643
theorem B3448571 : Blo 2297435 3448571 := bstep (se 1 (by rfl) ⟨2586428, by rfl⟩ : syracuseStep 3448571 = 5172857) B5172857
theorem B2299047 : Blo 2297435 2299047 := bstep (se 1 (by rfl) ⟨1724285, by rfl⟩ : syracuseStep 2299047 = 3448571) B3448571
theorem B2586433 : Blo 2297435 2586433 := bbase (se 2 (by rfl) ⟨969912, by rfl⟩ : syracuseStep 2586433 = 1939825) (by norm_num)
theorem B3448577 : Blo 2297435 3448577 := bstep (se 2 (by rfl) ⟨1293216, by rfl⟩ : syracuseStep 3448577 = 2586433) B2586433
theorem B2299051 : Blo 2297435 2299051 := bstep (se 1 (by rfl) ⟨1724288, by rfl⟩ : syracuseStep 2299051 = 3448577) B3448577
theorem B5819485 : Blo 2297435 5819485 := bbase (se 3 (by rfl) ⟨1091153, by rfl⟩ : syracuseStep 5819485 = 2182307) (by norm_num)
theorem B7759313 : Blo 2297435 7759313 := bstep (se 2 (by rfl) ⟨2909742, by rfl⟩ : syracuseStep 7759313 = 5819485) B5819485
theorem B5172875 : Blo 2297435 5172875 := bstep (se 1 (by rfl) ⟨3879656, by rfl⟩ : syracuseStep 5172875 = 7759313) B7759313
theorem B3448583 : Blo 2297435 3448583 := bstep (se 1 (by rfl) ⟨2586437, by rfl⟩ : syracuseStep 3448583 = 5172875) B5172875
theorem B2299055 : Blo 2297435 2299055 := bstep (se 1 (by rfl) ⟨1724291, by rfl⟩ : syracuseStep 2299055 = 3448583) B3448583
theorem B3448589 : Blo 2297435 3448589 := bbase (se 3 (by rfl) ⟨646610, by rfl⟩ : syracuseStep 3448589 = 1293221) (by norm_num)
theorem B2299059 : Blo 2297435 2299059 := bstep (se 1 (by rfl) ⟨1724294, by rfl⟩ : syracuseStep 2299059 = 3448589) B3448589
theorem B5172893 : Blo 2297435 5172893 := bbase (se 3 (by rfl) ⟨969917, by rfl⟩ : syracuseStep 5172893 = 1939835) (by norm_num)
theorem B3448595 : Blo 2297435 3448595 := bstep (se 1 (by rfl) ⟨2586446, by rfl⟩ : syracuseStep 3448595 = 5172893) B5172893
theorem B2299063 : Blo 2297435 2299063 := bstep (se 1 (by rfl) ⟨1724297, by rfl⟩ : syracuseStep 2299063 = 3448595) B3448595
theorem B3879677 : Blo 2297435 3879677 := bbase (se 3 (by rfl) ⟨727439, by rfl⟩ : syracuseStep 3879677 = 1454879) (by norm_num)
theorem B2586451 : Blo 2297435 2586451 := bstep (se 1 (by rfl) ⟨1939838, by rfl⟩ : syracuseStep 2586451 = 3879677) B3879677
theorem B3448601 : Blo 2297435 3448601 := bstep (se 2 (by rfl) ⟨1293225, by rfl⟩ : syracuseStep 3448601 = 2586451) B2586451
theorem B2299067 : Blo 2297435 2299067 := bstep (se 1 (by rfl) ⟨1724300, by rfl⟩ : syracuseStep 2299067 = 3448601) B3448601
theorem B3682669 : Blo 2297435 3682669 := bbase (se 3 (by rfl) ⟨690500, by rfl⟩ : syracuseStep 3682669 = 1381001) (by norm_num)
theorem B4910225 : Blo 2297435 4910225 := bstep (se 2 (by rfl) ⟨1841334, by rfl⟩ : syracuseStep 4910225 = 3682669) B3682669
theorem B13093933 : Blo 2297435 13093933 := bstep (se 3 (by rfl) ⟨2455112, by rfl⟩ : syracuseStep 13093933 = 4910225) B4910225
theorem B17458577 : Blo 2297435 17458577 := bstep (se 2 (by rfl) ⟨6546966, by rfl⟩ : syracuseStep 17458577 = 13093933) B13093933
theorem B11639051 : Blo 2297435 11639051 := bstep (se 1 (by rfl) ⟨8729288, by rfl⟩ : syracuseStep 11639051 = 17458577) B17458577
theorem B7759367 : Blo 2297435 7759367 := bstep (se 1 (by rfl) ⟨5819525, by rfl⟩ : syracuseStep 7759367 = 11639051) B11639051
theorem B5172911 : Blo 2297435 5172911 := bstep (se 1 (by rfl) ⟨3879683, by rfl⟩ : syracuseStep 5172911 = 7759367) B7759367
theorem B3448607 : Blo 2297435 3448607 := bstep (se 1 (by rfl) ⟨2586455, by rfl⟩ : syracuseStep 3448607 = 5172911) B5172911
theorem B2299071 : Blo 2297435 2299071 := bstep (se 1 (by rfl) ⟨1724303, by rfl⟩ : syracuseStep 2299071 = 3448607) B3448607
theorem B3448613 : Blo 2297435 3448613 := bbase (se 4 (by rfl) ⟨323307, by rfl⟩ : syracuseStep 3448613 = 646615) (by norm_num)
theorem B2299075 : Blo 2297435 2299075 := bstep (se 1 (by rfl) ⟨1724306, by rfl⟩ : syracuseStep 2299075 = 3448613) B3448613
theorem B2909773 : Blo 2297435 2909773 := bbase (se 3 (by rfl) ⟨545582, by rfl⟩ : syracuseStep 2909773 = 1091165) (by norm_num)
theorem B3879697 : Blo 2297435 3879697 := bstep (se 2 (by rfl) ⟨1454886, by rfl⟩ : syracuseStep 3879697 = 2909773) B2909773
theorem B5172929 : Blo 2297435 5172929 := bstep (se 2 (by rfl) ⟨1939848, by rfl⟩ : syracuseStep 5172929 = 3879697) B3879697
theorem B3448619 : Blo 2297435 3448619 := bstep (se 1 (by rfl) ⟨2586464, by rfl⟩ : syracuseStep 3448619 = 5172929) B5172929
theorem B2299079 : Blo 2297435 2299079 := bstep (se 1 (by rfl) ⟨1724309, by rfl⟩ : syracuseStep 2299079 = 3448619) B3448619
theorem B2586469 : Blo 2297435 2586469 := bbase (se 4 (by rfl) ⟨242481, by rfl⟩ : syracuseStep 2586469 = 484963) (by norm_num)
theorem B3448625 : Blo 2297435 3448625 := bstep (se 2 (by rfl) ⟨1293234, by rfl⟩ : syracuseStep 3448625 = 2586469) B2586469
theorem B2299083 : Blo 2297435 2299083 := bstep (se 1 (by rfl) ⟨1724312, by rfl⟩ : syracuseStep 2299083 = 3448625) B3448625
theorem B6547013 : Blo 2297435 6547013 := bbase (se 4 (by rfl) ⟨613782, by rfl⟩ : syracuseStep 6547013 = 1227565) (by norm_num)
theorem B4364675 : Blo 2297435 4364675 := bstep (se 1 (by rfl) ⟨3273506, by rfl⟩ : syracuseStep 4364675 = 6547013) B6547013
theorem B2909783 : Blo 2297435 2909783 := bstep (se 1 (by rfl) ⟨2182337, by rfl⟩ : syracuseStep 2909783 = 4364675) B4364675
theorem B7759421 : Blo 2297435 7759421 := bstep (se 3 (by rfl) ⟨1454891, by rfl⟩ : syracuseStep 7759421 = 2909783) B2909783
theorem B5172947 : Blo 2297435 5172947 := bstep (se 1 (by rfl) ⟨3879710, by rfl⟩ : syracuseStep 5172947 = 7759421) B7759421
theorem B3448631 : Blo 2297435 3448631 := bstep (se 1 (by rfl) ⟨2586473, by rfl⟩ : syracuseStep 3448631 = 5172947) B5172947
theorem B2299087 : Blo 2297435 2299087 := bstep (se 1 (by rfl) ⟨1724315, by rfl⟩ : syracuseStep 2299087 = 3448631) B3448631
theorem B3448637 : Blo 2297435 3448637 := bbase (se 3 (by rfl) ⟨646619, by rfl⟩ : syracuseStep 3448637 = 1293239) (by norm_num)
theorem B2299091 : Blo 2297435 2299091 := bstep (se 1 (by rfl) ⟨1724318, by rfl⟩ : syracuseStep 2299091 = 3448637) B3448637
theorem B5172965 : Blo 2297435 5172965 := bbase (se 4 (by rfl) ⟨484965, by rfl⟩ : syracuseStep 5172965 = 969931) (by norm_num)
theorem B3448643 : Blo 2297435 3448643 := bstep (se 1 (by rfl) ⟨2586482, by rfl⟩ : syracuseStep 3448643 = 5172965) B5172965
theorem B2299095 : Blo 2297435 2299095 := bstep (se 1 (by rfl) ⟨1724321, by rfl⟩ : syracuseStep 2299095 = 3448643) B3448643
theorem B5819597 : Blo 2297435 5819597 := bbase (se 3 (by rfl) ⟨1091174, by rfl⟩ : syracuseStep 5819597 = 2182349) (by norm_num)
theorem B3879731 : Blo 2297435 3879731 := bstep (se 1 (by rfl) ⟨2909798, by rfl⟩ : syracuseStep 3879731 = 5819597) B5819597
theorem B2586487 : Blo 2297435 2586487 := bstep (se 1 (by rfl) ⟨1939865, by rfl⟩ : syracuseStep 2586487 = 3879731) B3879731
theorem B3448649 : Blo 2297435 3448649 := bstep (se 2 (by rfl) ⟨1293243, by rfl⟩ : syracuseStep 3448649 = 2586487) B2586487
theorem B2299099 : Blo 2297435 2299099 := bstep (se 1 (by rfl) ⟨1724324, by rfl⟩ : syracuseStep 2299099 = 3448649) B3448649
theorem B2762041 : Blo 2297435 2762041 := bbase (se 2 (by rfl) ⟨1035765, by rfl⟩ : syracuseStep 2762041 = 2071531) (by norm_num)
theorem B3682721 : Blo 2297435 3682721 := bstep (se 2 (by rfl) ⟨1381020, by rfl⟩ : syracuseStep 3682721 = 2762041) B2762041
theorem B2455147 : Blo 2297435 2455147 := bstep (se 1 (by rfl) ⟨1841360, by rfl⟩ : syracuseStep 2455147 = 3682721) B3682721
theorem B3273529 : Blo 2297435 3273529 := bstep (se 2 (by rfl) ⟨1227573, by rfl⟩ : syracuseStep 3273529 = 2455147) B2455147
theorem B4364705 : Blo 2297435 4364705 := bstep (se 2 (by rfl) ⟨1636764, by rfl⟩ : syracuseStep 4364705 = 3273529) B3273529
theorem B11639213 : Blo 2297435 11639213 := bstep (se 3 (by rfl) ⟨2182352, by rfl⟩ : syracuseStep 11639213 = 4364705) B4364705
theorem B7759475 : Blo 2297435 7759475 := bstep (se 1 (by rfl) ⟨5819606, by rfl⟩ : syracuseStep 7759475 = 11639213) B11639213
theorem B5172983 : Blo 2297435 5172983 := bstep (se 1 (by rfl) ⟨3879737, by rfl⟩ : syracuseStep 5172983 = 7759475) B7759475
theorem B3448655 : Blo 2297435 3448655 := bstep (se 1 (by rfl) ⟨2586491, by rfl⟩ : syracuseStep 3448655 = 5172983) B5172983
theorem B2299103 : Blo 2297435 2299103 := bstep (se 1 (by rfl) ⟨1724327, by rfl⟩ : syracuseStep 2299103 = 3448655) B3448655
theorem B3448661 : Blo 2297435 3448661 := bbase (se 9 (by rfl) ⟨10103, by rfl⟩ : syracuseStep 3448661 = 20207) (by norm_num)
theorem B2299107 : Blo 2297435 2299107 := bstep (se 1 (by rfl) ⟨1724330, by rfl⟩ : syracuseStep 2299107 = 3448661) B3448661
theorem B3986341 : Blo 2297435 3986341 := bbase (se 4 (by rfl) ⟨373719, by rfl⟩ : syracuseStep 3986341 = 747439) (by norm_num)
theorem B21260485 : Blo 2297435 21260485 := bstep (se 4 (by rfl) ⟨1993170, by rfl⟩ : syracuseStep 21260485 = 3986341) B3986341
theorem B113389253 : Blo 2297435 113389253 := bstep (se 4 (by rfl) ⟨10630242, by rfl⟩ : syracuseStep 113389253 = 21260485) B21260485
theorem B75592835 : Blo 2297435 75592835 := bstep (se 1 (by rfl) ⟨56694626, by rfl⟩ : syracuseStep 75592835 = 113389253) B113389253
theorem B50395223 : Blo 2297435 50395223 := bstep (se 1 (by rfl) ⟨37796417, by rfl⟩ : syracuseStep 50395223 = 75592835) B75592835
theorem B33596815 : Blo 2297435 33596815 := bstep (se 1 (by rfl) ⟨25197611, by rfl⟩ : syracuseStep 33596815 = 50395223) B50395223
theorem B44795753 : Blo 2297435 44795753 := bstep (se 2 (by rfl) ⟨16798407, by rfl⟩ : syracuseStep 44795753 = 33596815) B33596815
theorem B29863835 : Blo 2297435 29863835 := bstep (se 1 (by rfl) ⟨22397876, by rfl⟩ : syracuseStep 29863835 = 44795753) B44795753
theorem B19909223 : Blo 2297435 19909223 := bstep (se 1 (by rfl) ⟨14931917, by rfl⟩ : syracuseStep 19909223 = 29863835) B29863835
theorem B13272815 : Blo 2297435 13272815 := bstep (se 1 (by rfl) ⟨9954611, by rfl⟩ : syracuseStep 13272815 = 19909223) B19909223
theorem B8848543 : Blo 2297435 8848543 := bstep (se 1 (by rfl) ⟨6636407, by rfl⟩ : syracuseStep 8848543 = 13272815) B13272815
theorem B11798057 : Blo 2297435 11798057 := bstep (se 2 (by rfl) ⟨4424271, by rfl⟩ : syracuseStep 11798057 = 8848543) B8848543
theorem B7865371 : Blo 2297435 7865371 := bstep (se 1 (by rfl) ⟨5899028, by rfl⟩ : syracuseStep 7865371 = 11798057) B11798057
theorem B10487161 : Blo 2297435 10487161 := bstep (se 2 (by rfl) ⟨3932685, by rfl⟩ : syracuseStep 10487161 = 7865371) B7865371
theorem B13982881 : Blo 2297435 13982881 := bstep (se 2 (by rfl) ⟨5243580, by rfl⟩ : syracuseStep 13982881 = 10487161) B10487161
theorem B18643841 : Blo 2297435 18643841 := bstep (se 2 (by rfl) ⟨6991440, by rfl⟩ : syracuseStep 18643841 = 13982881) B13982881
theorem B12429227 : Blo 2297435 12429227 := bstep (se 1 (by rfl) ⟨9321920, by rfl⟩ : syracuseStep 12429227 = 18643841) B18643841
theorem B8286151 : Blo 2297435 8286151 := bstep (se 1 (by rfl) ⟨6214613, by rfl⟩ : syracuseStep 8286151 = 12429227) B12429227
theorem B11048201 : Blo 2297435 11048201 := bstep (se 2 (by rfl) ⟨4143075, by rfl⟩ : syracuseStep 11048201 = 8286151) B8286151
theorem B7365467 : Blo 2297435 7365467 := bstep (se 1 (by rfl) ⟨5524100, by rfl⟩ : syracuseStep 7365467 = 11048201) B11048201
theorem B4910311 : Blo 2297435 4910311 := bstep (se 1 (by rfl) ⟨3682733, by rfl⟩ : syracuseStep 4910311 = 7365467) B7365467
theorem B6547081 : Blo 2297435 6547081 := bstep (se 2 (by rfl) ⟨2455155, by rfl⟩ : syracuseStep 6547081 = 4910311) B4910311
theorem B8729441 : Blo 2297435 8729441 := bstep (se 2 (by rfl) ⟨3273540, by rfl⟩ : syracuseStep 8729441 = 6547081) B6547081
theorem B5819627 : Blo 2297435 5819627 := bstep (se 1 (by rfl) ⟨4364720, by rfl⟩ : syracuseStep 5819627 = 8729441) B8729441
theorem B3879751 : Blo 2297435 3879751 := bstep (se 1 (by rfl) ⟨2909813, by rfl⟩ : syracuseStep 3879751 = 5819627) B5819627
theorem B5173001 : Blo 2297435 5173001 := bstep (se 2 (by rfl) ⟨1939875, by rfl⟩ : syracuseStep 5173001 = 3879751) B3879751
theorem B3448667 : Blo 2297435 3448667 := bstep (se 1 (by rfl) ⟨2586500, by rfl⟩ : syracuseStep 3448667 = 5173001) B5173001
theorem B2299111 : Blo 2297435 2299111 := bstep (se 1 (by rfl) ⟨1724333, by rfl⟩ : syracuseStep 2299111 = 3448667) B3448667
theorem B2586505 : Blo 2297435 2586505 := bbase (se 2 (by rfl) ⟨969939, by rfl⟩ : syracuseStep 2586505 = 1939879) (by norm_num)
theorem B3448673 : Blo 2297435 3448673 := bstep (se 2 (by rfl) ⟨1293252, by rfl⟩ : syracuseStep 3448673 = 2586505) B2586505
theorem B2299115 : Blo 2297435 2299115 := bstep (se 1 (by rfl) ⟨1724336, by rfl⟩ : syracuseStep 2299115 = 3448673) B3448673
theorem B11351765 : Blo 2297435 11351765 := bbase (se 7 (by rfl) ⟨133028, by rfl⟩ : syracuseStep 11351765 = 266057) (by norm_num)
theorem B30271373 : Blo 2297435 30271373 := bstep (se 3 (by rfl) ⟨5675882, by rfl⟩ : syracuseStep 30271373 = 11351765) B11351765
theorem B20180915 : Blo 2297435 20180915 := bstep (se 1 (by rfl) ⟨15135686, by rfl⟩ : syracuseStep 20180915 = 30271373) B30271373
theorem B13453943 : Blo 2297435 13453943 := bstep (se 1 (by rfl) ⟨10090457, by rfl⟩ : syracuseStep 13453943 = 20180915) B20180915
theorem B35877181 : Blo 2297435 35877181 := bstep (se 3 (by rfl) ⟨6726971, by rfl⟩ : syracuseStep 35877181 = 13453943) B13453943
theorem B47836241 : Blo 2297435 47836241 := bstep (se 2 (by rfl) ⟨17938590, by rfl⟩ : syracuseStep 47836241 = 35877181) B35877181
theorem B31890827 : Blo 2297435 31890827 := bstep (se 1 (by rfl) ⟨23918120, by rfl⟩ : syracuseStep 31890827 = 47836241) B47836241
theorem B21260551 : Blo 2297435 21260551 := bstep (se 1 (by rfl) ⟨15945413, by rfl⟩ : syracuseStep 21260551 = 31890827) B31890827
theorem B28347401 : Blo 2297435 28347401 := bstep (se 2 (by rfl) ⟨10630275, by rfl⟩ : syracuseStep 28347401 = 21260551) B21260551
theorem B18898267 : Blo 2297435 18898267 := bstep (se 1 (by rfl) ⟨14173700, by rfl⟩ : syracuseStep 18898267 = 28347401) B28347401
theorem B25197689 : Blo 2297435 25197689 := bstep (se 2 (by rfl) ⟨9449133, by rfl⟩ : syracuseStep 25197689 = 18898267) B18898267
theorem B67193837 : Blo 2297435 67193837 := bstep (se 3 (by rfl) ⟨12598844, by rfl⟩ : syracuseStep 67193837 = 25197689) B25197689
theorem B44795891 : Blo 2297435 44795891 := bstep (se 1 (by rfl) ⟨33596918, by rfl⟩ : syracuseStep 44795891 = 67193837) B67193837
theorem B29863927 : Blo 2297435 29863927 := bstep (se 1 (by rfl) ⟨22397945, by rfl⟩ : syracuseStep 29863927 = 44795891) B44795891
theorem B39818569 : Blo 2297435 39818569 := bstep (se 2 (by rfl) ⟨14931963, by rfl⟩ : syracuseStep 39818569 = 29863927) B29863927
theorem B53091425 : Blo 2297435 53091425 := bstep (se 2 (by rfl) ⟨19909284, by rfl⟩ : syracuseStep 53091425 = 39818569) B39818569
theorem B35394283 : Blo 2297435 35394283 := bstep (se 1 (by rfl) ⟨26545712, by rfl⟩ : syracuseStep 35394283 = 53091425) B53091425
theorem B47192377 : Blo 2297435 47192377 := bstep (se 2 (by rfl) ⟨17697141, by rfl⟩ : syracuseStep 47192377 = 35394283) B35394283
theorem B62923169 : Blo 2297435 62923169 := bstep (se 2 (by rfl) ⟨23596188, by rfl⟩ : syracuseStep 62923169 = 47192377) B47192377
theorem B41948779 : Blo 2297435 41948779 := bstep (se 1 (by rfl) ⟨31461584, by rfl⟩ : syracuseStep 41948779 = 62923169) B62923169
theorem B55931705 : Blo 2297435 55931705 := bstep (se 2 (by rfl) ⟨20974389, by rfl⟩ : syracuseStep 55931705 = 41948779) B41948779
theorem B37287803 : Blo 2297435 37287803 := bstep (se 1 (by rfl) ⟨27965852, by rfl⟩ : syracuseStep 37287803 = 55931705) B55931705
theorem B99434141 : Blo 2297435 99434141 := bstep (se 3 (by rfl) ⟨18643901, by rfl⟩ : syracuseStep 99434141 = 37287803) B37287803
theorem B66289427 : Blo 2297435 66289427 := bstep (se 1 (by rfl) ⟨49717070, by rfl⟩ : syracuseStep 66289427 = 99434141) B99434141
theorem B44192951 : Blo 2297435 44192951 := bstep (se 1 (by rfl) ⟨33144713, by rfl⟩ : syracuseStep 44192951 = 66289427) B66289427
theorem B29461967 : Blo 2297435 29461967 := bstep (se 1 (by rfl) ⟨22096475, by rfl⟩ : syracuseStep 29461967 = 44192951) B44192951
theorem B19641311 : Blo 2297435 19641311 := bstep (se 1 (by rfl) ⟨14730983, by rfl⟩ : syracuseStep 19641311 = 29461967) B29461967
theorem B13094207 : Blo 2297435 13094207 := bstep (se 1 (by rfl) ⟨9820655, by rfl⟩ : syracuseStep 13094207 = 19641311) B19641311
theorem B8729471 : Blo 2297435 8729471 := bstep (se 1 (by rfl) ⟨6547103, by rfl⟩ : syracuseStep 8729471 = 13094207) B13094207
theorem B5819647 : Blo 2297435 5819647 := bstep (se 1 (by rfl) ⟨4364735, by rfl⟩ : syracuseStep 5819647 = 8729471) B8729471
theorem B7759529 : Blo 2297435 7759529 := bstep (se 2 (by rfl) ⟨2909823, by rfl⟩ : syracuseStep 7759529 = 5819647) B5819647
theorem B5173019 : Blo 2297435 5173019 := bstep (se 1 (by rfl) ⟨3879764, by rfl⟩ : syracuseStep 5173019 = 7759529) B7759529
theorem B3448679 : Blo 2297435 3448679 := bstep (se 1 (by rfl) ⟨2586509, by rfl⟩ : syracuseStep 3448679 = 5173019) B5173019
theorem B2299119 : Blo 2297435 2299119 := bstep (se 1 (by rfl) ⟨1724339, by rfl⟩ : syracuseStep 2299119 = 3448679) B3448679
theorem B3448685 : Blo 2297435 3448685 := bbase (se 3 (by rfl) ⟨646628, by rfl⟩ : syracuseStep 3448685 = 1293257) (by norm_num)
theorem B2299123 : Blo 2297435 2299123 := bstep (se 1 (by rfl) ⟨1724342, by rfl⟩ : syracuseStep 2299123 = 3448685) B3448685
theorem B5173037 : Blo 2297435 5173037 := bbase (se 3 (by rfl) ⟨969944, by rfl⟩ : syracuseStep 5173037 = 1939889) (by norm_num)
theorem B3448691 : Blo 2297435 3448691 := bstep (se 1 (by rfl) ⟨2586518, by rfl⟩ : syracuseStep 3448691 = 5173037) B5173037
theorem B2299127 : Blo 2297435 2299127 := bstep (se 1 (by rfl) ⟨1724345, by rfl⟩ : syracuseStep 2299127 = 3448691) B3448691
theorem B9820709 : Blo 2297435 9820709 := bbase (se 4 (by rfl) ⟨920691, by rfl⟩ : syracuseStep 9820709 = 1841383) (by norm_num)
theorem B6547139 : Blo 2297435 6547139 := bstep (se 1 (by rfl) ⟨4910354, by rfl⟩ : syracuseStep 6547139 = 9820709) B9820709
theorem B4364759 : Blo 2297435 4364759 := bstep (se 1 (by rfl) ⟨3273569, by rfl⟩ : syracuseStep 4364759 = 6547139) B6547139
theorem B2909839 : Blo 2297435 2909839 := bstep (se 1 (by rfl) ⟨2182379, by rfl⟩ : syracuseStep 2909839 = 4364759) B4364759
theorem B3879785 : Blo 2297435 3879785 := bstep (se 2 (by rfl) ⟨1454919, by rfl⟩ : syracuseStep 3879785 = 2909839) B2909839
theorem B2586523 : Blo 2297435 2586523 := bstep (se 1 (by rfl) ⟨1939892, by rfl⟩ : syracuseStep 2586523 = 3879785) B3879785
theorem B3448697 : Blo 2297435 3448697 := bstep (se 2 (by rfl) ⟨1293261, by rfl⟩ : syracuseStep 3448697 = 2586523) B2586523
theorem B2299131 : Blo 2297435 2299131 := bstep (se 1 (by rfl) ⟨1724348, by rfl⟩ : syracuseStep 2299131 = 3448697) B3448697
theorem B5524157 : Blo 2297435 5524157 := bbase (se 3 (by rfl) ⟨1035779, by rfl⟩ : syracuseStep 5524157 = 2071559) (by norm_num)
theorem B14731085 : Blo 2297435 14731085 := bstep (se 3 (by rfl) ⟨2762078, by rfl⟩ : syracuseStep 14731085 = 5524157) B5524157
theorem B39282893 : Blo 2297435 39282893 := bstep (se 3 (by rfl) ⟨7365542, by rfl⟩ : syracuseStep 39282893 = 14731085) B14731085
theorem B26188595 : Blo 2297435 26188595 := bstep (se 1 (by rfl) ⟨19641446, by rfl⟩ : syracuseStep 26188595 = 39282893) B39282893
theorem B17459063 : Blo 2297435 17459063 := bstep (se 1 (by rfl) ⟨13094297, by rfl⟩ : syracuseStep 17459063 = 26188595) B26188595
theorem B11639375 : Blo 2297435 11639375 := bstep (se 1 (by rfl) ⟨8729531, by rfl⟩ : syracuseStep 11639375 = 17459063) B17459063
theorem B7759583 : Blo 2297435 7759583 := bstep (se 1 (by rfl) ⟨5819687, by rfl⟩ : syracuseStep 7759583 = 11639375) B11639375
theorem B5173055 : Blo 2297435 5173055 := bstep (se 1 (by rfl) ⟨3879791, by rfl⟩ : syracuseStep 5173055 = 7759583) B7759583
theorem B3448703 : Blo 2297435 3448703 := bstep (se 1 (by rfl) ⟨2586527, by rfl⟩ : syracuseStep 3448703 = 5173055) B5173055
theorem B2299135 : Blo 2297435 2299135 := bstep (se 1 (by rfl) ⟨1724351, by rfl⟩ : syracuseStep 2299135 = 3448703) B3448703
theorem B3448709 : Blo 2297435 3448709 := bbase (se 4 (by rfl) ⟨323316, by rfl⟩ : syracuseStep 3448709 = 646633) (by norm_num)
theorem B2299139 : Blo 2297435 2299139 := bstep (se 1 (by rfl) ⟨1724354, by rfl⟩ : syracuseStep 2299139 = 3448709) B3448709
theorem B3879805 : Blo 2297435 3879805 := bbase (se 3 (by rfl) ⟨727463, by rfl⟩ : syracuseStep 3879805 = 1454927) (by norm_num)
theorem B5173073 : Blo 2297435 5173073 := bstep (se 2 (by rfl) ⟨1939902, by rfl⟩ : syracuseStep 5173073 = 3879805) B3879805
theorem B3448715 : Blo 2297435 3448715 := bstep (se 1 (by rfl) ⟨2586536, by rfl⟩ : syracuseStep 3448715 = 5173073) B5173073
theorem B2299143 : Blo 2297435 2299143 := bstep (se 1 (by rfl) ⟨1724357, by rfl⟩ : syracuseStep 2299143 = 3448715) B3448715
theorem B2586541 : Blo 2297435 2586541 := bbase (se 3 (by rfl) ⟨484976, by rfl⟩ : syracuseStep 2586541 = 969953) (by norm_num)
theorem B3448721 : Blo 2297435 3448721 := bstep (se 2 (by rfl) ⟨1293270, by rfl⟩ : syracuseStep 3448721 = 2586541) B2586541
theorem B2299147 : Blo 2297435 2299147 := bstep (se 1 (by rfl) ⟨1724360, by rfl⟩ : syracuseStep 2299147 = 3448721) B3448721
theorem B7759637 : Blo 2297435 7759637 := bbase (se 6 (by rfl) ⟨181866, by rfl⟩ : syracuseStep 7759637 = 363733) (by norm_num)
theorem B5173091 : Blo 2297435 5173091 := bstep (se 1 (by rfl) ⟨3879818, by rfl⟩ : syracuseStep 5173091 = 7759637) B7759637
theorem B3448727 : Blo 2297435 3448727 := bstep (se 1 (by rfl) ⟨2586545, by rfl⟩ : syracuseStep 3448727 = 5173091) B5173091
theorem B2299151 : Blo 2297435 2299151 := bstep (se 1 (by rfl) ⟨1724363, by rfl⟩ : syracuseStep 2299151 = 3448727) B3448727
theorem B3448733 : Blo 2297435 3448733 := bbase (se 3 (by rfl) ⟨646637, by rfl⟩ : syracuseStep 3448733 = 1293275) (by norm_num)
theorem B2299155 : Blo 2297435 2299155 := bstep (se 1 (by rfl) ⟨1724366, by rfl⟩ : syracuseStep 2299155 = 3448733) B3448733
theorem B5173109 : Blo 2297435 5173109 := bbase (se 5 (by rfl) ⟨242489, by rfl⟩ : syracuseStep 5173109 = 484979) (by norm_num)
theorem B3448739 : Blo 2297435 3448739 := bstep (se 1 (by rfl) ⟨2586554, by rfl⟩ : syracuseStep 3448739 = 5173109) B5173109
theorem B2299159 : Blo 2297435 2299159 := bstep (se 1 (by rfl) ⟨1724369, by rfl⟩ : syracuseStep 2299159 = 3448739) B3448739
theorem B2330533 : Blo 2297435 2330533 := bbase (se 4 (by rfl) ⟨218487, by rfl⟩ : syracuseStep 2330533 = 436975) (by norm_num)
theorem B3107377 : Blo 2297435 3107377 := bstep (se 2 (by rfl) ⟨1165266, by rfl⟩ : syracuseStep 3107377 = 2330533) B2330533
theorem B4143169 : Blo 2297435 4143169 := bstep (se 2 (by rfl) ⟨1553688, by rfl⟩ : syracuseStep 4143169 = 3107377) B3107377
theorem B22096901 : Blo 2297435 22096901 := bstep (se 4 (by rfl) ⟨2071584, by rfl⟩ : syracuseStep 22096901 = 4143169) B4143169
theorem B14731267 : Blo 2297435 14731267 := bstep (se 1 (by rfl) ⟨11048450, by rfl⟩ : syracuseStep 14731267 = 22096901) B22096901
theorem B19641689 : Blo 2297435 19641689 := bstep (se 2 (by rfl) ⟨7365633, by rfl⟩ : syracuseStep 19641689 = 14731267) B14731267
theorem B13094459 : Blo 2297435 13094459 := bstep (se 1 (by rfl) ⟨9820844, by rfl⟩ : syracuseStep 13094459 = 19641689) B19641689
theorem B8729639 : Blo 2297435 8729639 := bstep (se 1 (by rfl) ⟨6547229, by rfl⟩ : syracuseStep 8729639 = 13094459) B13094459
theorem B5819759 : Blo 2297435 5819759 := bstep (se 1 (by rfl) ⟨4364819, by rfl⟩ : syracuseStep 5819759 = 8729639) B8729639
theorem B3879839 : Blo 2297435 3879839 := bstep (se 1 (by rfl) ⟨2909879, by rfl⟩ : syracuseStep 3879839 = 5819759) B5819759
theorem B2586559 : Blo 2297435 2586559 := bstep (se 1 (by rfl) ⟨1939919, by rfl⟩ : syracuseStep 2586559 = 3879839) B3879839
theorem B3448745 : Blo 2297435 3448745 := bstep (se 2 (by rfl) ⟨1293279, by rfl⟩ : syracuseStep 3448745 = 2586559) B2586559
theorem B2299163 : Blo 2297435 2299163 := bstep (se 1 (by rfl) ⟨1724372, by rfl⟩ : syracuseStep 2299163 = 3448745) B3448745
theorem B8729653 : Blo 2297435 8729653 := bbase (se 5 (by rfl) ⟨409202, by rfl⟩ : syracuseStep 8729653 = 818405) (by norm_num)
theorem B11639537 : Blo 2297435 11639537 := bstep (se 2 (by rfl) ⟨4364826, by rfl⟩ : syracuseStep 11639537 = 8729653) B8729653
theorem B7759691 : Blo 2297435 7759691 := bstep (se 1 (by rfl) ⟨5819768, by rfl⟩ : syracuseStep 7759691 = 11639537) B11639537
theorem B5173127 : Blo 2297435 5173127 := bstep (se 1 (by rfl) ⟨3879845, by rfl⟩ : syracuseStep 5173127 = 7759691) B7759691
theorem B3448751 : Blo 2297435 3448751 := bstep (se 1 (by rfl) ⟨2586563, by rfl⟩ : syracuseStep 3448751 = 5173127) B5173127
theorem B2299167 : Blo 2297435 2299167 := bstep (se 1 (by rfl) ⟨1724375, by rfl⟩ : syracuseStep 2299167 = 3448751) B3448751
theorem B3448757 : Blo 2297435 3448757 := bbase (se 5 (by rfl) ⟨161660, by rfl⟩ : syracuseStep 3448757 = 323321) (by norm_num)
theorem B2299171 : Blo 2297435 2299171 := bstep (se 1 (by rfl) ⟨1724378, by rfl⟩ : syracuseStep 2299171 = 3448757) B3448757
theorem B5819789 : Blo 2297435 5819789 := bbase (se 3 (by rfl) ⟨1091210, by rfl⟩ : syracuseStep 5819789 = 2182421) (by norm_num)
theorem B3879859 : Blo 2297435 3879859 := bstep (se 1 (by rfl) ⟨2909894, by rfl⟩ : syracuseStep 3879859 = 5819789) B5819789
theorem B5173145 : Blo 2297435 5173145 := bstep (se 2 (by rfl) ⟨1939929, by rfl⟩ : syracuseStep 5173145 = 3879859) B3879859
theorem B3448763 : Blo 2297435 3448763 := bstep (se 1 (by rfl) ⟨2586572, by rfl⟩ : syracuseStep 3448763 = 5173145) B5173145
theorem B2299175 : Blo 2297435 2299175 := bstep (se 1 (by rfl) ⟨1724381, by rfl⟩ : syracuseStep 2299175 = 3448763) B3448763
theorem B2586577 : Blo 2297435 2586577 := bbase (se 2 (by rfl) ⟨969966, by rfl⟩ : syracuseStep 2586577 = 1939933) (by norm_num)
theorem B3448769 : Blo 2297435 3448769 := bstep (se 2 (by rfl) ⟨1293288, by rfl⟩ : syracuseStep 3448769 = 2586577) B2586577
theorem B2299179 : Blo 2297435 2299179 := bstep (se 1 (by rfl) ⟨1724384, by rfl⟩ : syracuseStep 2299179 = 3448769) B3448769
theorem B2762137 : Blo 2297435 2762137 := bbase (se 2 (by rfl) ⟨1035801, by rfl⟩ : syracuseStep 2762137 = 2071603) (by norm_num)
theorem B3682849 : Blo 2297435 3682849 := bstep (se 2 (by rfl) ⟨1381068, by rfl⟩ : syracuseStep 3682849 = 2762137) B2762137
theorem B4910465 : Blo 2297435 4910465 := bstep (se 2 (by rfl) ⟨1841424, by rfl⟩ : syracuseStep 4910465 = 3682849) B3682849
theorem B3273643 : Blo 2297435 3273643 := bstep (se 1 (by rfl) ⟨2455232, by rfl⟩ : syracuseStep 3273643 = 4910465) B4910465
theorem B4364857 : Blo 2297435 4364857 := bstep (se 2 (by rfl) ⟨1636821, by rfl⟩ : syracuseStep 4364857 = 3273643) B3273643
theorem B5819809 : Blo 2297435 5819809 := bstep (se 2 (by rfl) ⟨2182428, by rfl⟩ : syracuseStep 5819809 = 4364857) B4364857
theorem B7759745 : Blo 2297435 7759745 := bstep (se 2 (by rfl) ⟨2909904, by rfl⟩ : syracuseStep 7759745 = 5819809) B5819809
theorem B5173163 : Blo 2297435 5173163 := bstep (se 1 (by rfl) ⟨3879872, by rfl⟩ : syracuseStep 5173163 = 7759745) B7759745
theorem B3448775 : Blo 2297435 3448775 := bstep (se 1 (by rfl) ⟨2586581, by rfl⟩ : syracuseStep 3448775 = 5173163) B5173163
theorem B2299183 : Blo 2297435 2299183 := bstep (se 1 (by rfl) ⟨1724387, by rfl⟩ : syracuseStep 2299183 = 3448775) B3448775
theorem B3448781 : Blo 2297435 3448781 := bbase (se 3 (by rfl) ⟨646646, by rfl⟩ : syracuseStep 3448781 = 1293293) (by norm_num)
theorem B2299187 : Blo 2297435 2299187 := bstep (se 1 (by rfl) ⟨1724390, by rfl⟩ : syracuseStep 2299187 = 3448781) B3448781
theorem B5173181 : Blo 2297435 5173181 := bbase (se 3 (by rfl) ⟨969971, by rfl⟩ : syracuseStep 5173181 = 1939943) (by norm_num)
theorem B3448787 : Blo 2297435 3448787 := bstep (se 1 (by rfl) ⟨2586590, by rfl⟩ : syracuseStep 3448787 = 5173181) B5173181
theorem B2299191 : Blo 2297435 2299191 := bstep (se 1 (by rfl) ⟨1724393, by rfl⟩ : syracuseStep 2299191 = 3448787) B3448787
theorem B3879893 : Blo 2297435 3879893 := bbase (se 7 (by rfl) ⟨45467, by rfl⟩ : syracuseStep 3879893 = 90935) (by norm_num)
theorem B2586595 : Blo 2297435 2586595 := bstep (se 1 (by rfl) ⟨1939946, by rfl⟩ : syracuseStep 2586595 = 3879893) B3879893
theorem B3448793 : Blo 2297435 3448793 := bstep (se 2 (by rfl) ⟨1293297, by rfl⟩ : syracuseStep 3448793 = 2586595) B2586595
theorem B2299195 : Blo 2297435 2299195 := bstep (se 1 (by rfl) ⟨1724396, by rfl⟩ : syracuseStep 2299195 = 3448793) B3448793
theorem B9820997 : Blo 2297435 9820997 := bbase (se 4 (by rfl) ⟨920718, by rfl⟩ : syracuseStep 9820997 = 1841437) (by norm_num)
theorem B6547331 : Blo 2297435 6547331 := bstep (se 1 (by rfl) ⟨4910498, by rfl⟩ : syracuseStep 6547331 = 9820997) B9820997
theorem B17459549 : Blo 2297435 17459549 := bstep (se 3 (by rfl) ⟨3273665, by rfl⟩ : syracuseStep 17459549 = 6547331) B6547331
theorem B11639699 : Blo 2297435 11639699 := bstep (se 1 (by rfl) ⟨8729774, by rfl⟩ : syracuseStep 11639699 = 17459549) B17459549
theorem B7759799 : Blo 2297435 7759799 := bstep (se 1 (by rfl) ⟨5819849, by rfl⟩ : syracuseStep 7759799 = 11639699) B11639699
theorem B5173199 : Blo 2297435 5173199 := bstep (se 1 (by rfl) ⟨3879899, by rfl⟩ : syracuseStep 5173199 = 7759799) B7759799
theorem B3448799 : Blo 2297435 3448799 := bstep (se 1 (by rfl) ⟨2586599, by rfl⟩ : syracuseStep 3448799 = 5173199) B5173199
theorem B2299199 : Blo 2297435 2299199 := bstep (se 1 (by rfl) ⟨1724399, by rfl⟩ : syracuseStep 2299199 = 3448799) B3448799
theorem B3448805 : Blo 2297435 3448805 := bbase (se 4 (by rfl) ⟨323325, by rfl⟩ : syracuseStep 3448805 = 646651) (by norm_num)
theorem B2299203 : Blo 2297435 2299203 := bstep (se 1 (by rfl) ⟨1724402, by rfl⟩ : syracuseStep 2299203 = 3448805) B3448805
theorem B6991733 : Blo 2297435 6991733 := bbase (se 5 (by rfl) ⟨327737, by rfl⟩ : syracuseStep 6991733 = 655475) (by norm_num)
theorem B4661155 : Blo 2297435 4661155 := bstep (se 1 (by rfl) ⟨3495866, by rfl⟩ : syracuseStep 4661155 = 6991733) B6991733
theorem B24859493 : Blo 2297435 24859493 := bstep (se 4 (by rfl) ⟨2330577, by rfl⟩ : syracuseStep 24859493 = 4661155) B4661155
theorem B16572995 : Blo 2297435 16572995 := bstep (se 1 (by rfl) ⟨12429746, by rfl⟩ : syracuseStep 16572995 = 24859493) B24859493
theorem B11048663 : Blo 2297435 11048663 := bstep (se 1 (by rfl) ⟨8286497, by rfl⟩ : syracuseStep 11048663 = 16572995) B16572995
theorem B7365775 : Blo 2297435 7365775 := bstep (se 1 (by rfl) ⟨5524331, by rfl⟩ : syracuseStep 7365775 = 11048663) B11048663
theorem B9821033 : Blo 2297435 9821033 := bstep (se 2 (by rfl) ⟨3682887, by rfl⟩ : syracuseStep 9821033 = 7365775) B7365775
theorem B6547355 : Blo 2297435 6547355 := bstep (se 1 (by rfl) ⟨4910516, by rfl⟩ : syracuseStep 6547355 = 9821033) B9821033
theorem B4364903 : Blo 2297435 4364903 := bstep (se 1 (by rfl) ⟨3273677, by rfl⟩ : syracuseStep 4364903 = 6547355) B6547355
theorem B2909935 : Blo 2297435 2909935 := bstep (se 1 (by rfl) ⟨2182451, by rfl⟩ : syracuseStep 2909935 = 4364903) B4364903
theorem B3879913 : Blo 2297435 3879913 := bstep (se 2 (by rfl) ⟨1454967, by rfl⟩ : syracuseStep 3879913 = 2909935) B2909935
theorem B5173217 : Blo 2297435 5173217 := bstep (se 2 (by rfl) ⟨1939956, by rfl⟩ : syracuseStep 5173217 = 3879913) B3879913
theorem B3448811 : Blo 2297435 3448811 := bstep (se 1 (by rfl) ⟨2586608, by rfl⟩ : syracuseStep 3448811 = 5173217) B5173217
theorem B2299207 : Blo 2297435 2299207 := bstep (se 1 (by rfl) ⟨1724405, by rfl⟩ : syracuseStep 2299207 = 3448811) B3448811
theorem B2586613 : Blo 2297435 2586613 := bbase (se 5 (by rfl) ⟨121247, by rfl⟩ : syracuseStep 2586613 = 242495) (by norm_num)
theorem B3448817 : Blo 2297435 3448817 := bstep (se 2 (by rfl) ⟨1293306, by rfl⟩ : syracuseStep 3448817 = 2586613) B2586613
theorem B2299211 : Blo 2297435 2299211 := bstep (se 1 (by rfl) ⟨1724408, by rfl⟩ : syracuseStep 2299211 = 3448817) B3448817
theorem B2909945 : Blo 2297435 2909945 := bbase (se 2 (by rfl) ⟨1091229, by rfl⟩ : syracuseStep 2909945 = 2182459) (by norm_num)
theorem B7759853 : Blo 2297435 7759853 := bstep (se 3 (by rfl) ⟨1454972, by rfl⟩ : syracuseStep 7759853 = 2909945) B2909945
theorem B5173235 : Blo 2297435 5173235 := bstep (se 1 (by rfl) ⟨3879926, by rfl⟩ : syracuseStep 5173235 = 7759853) B7759853
theorem B3448823 : Blo 2297435 3448823 := bstep (se 1 (by rfl) ⟨2586617, by rfl⟩ : syracuseStep 3448823 = 5173235) B5173235
theorem B2299215 : Blo 2297435 2299215 := bstep (se 1 (by rfl) ⟨1724411, by rfl⟩ : syracuseStep 2299215 = 3448823) B3448823
theorem B3448829 : Blo 2297435 3448829 := bbase (se 3 (by rfl) ⟨646655, by rfl⟩ : syracuseStep 3448829 = 1293311) (by norm_num)
theorem B2299219 : Blo 2297435 2299219 := bstep (se 1 (by rfl) ⟨1724414, by rfl⟩ : syracuseStep 2299219 = 3448829) B3448829
theorem B5173253 : Blo 2297435 5173253 := bbase (se 4 (by rfl) ⟨484992, by rfl⟩ : syracuseStep 5173253 = 969985) (by norm_num)
theorem B3448835 : Blo 2297435 3448835 := bstep (se 1 (by rfl) ⟨2586626, by rfl⟩ : syracuseStep 3448835 = 5173253) B5173253
theorem B2299223 : Blo 2297435 2299223 := bstep (se 1 (by rfl) ⟨1724417, by rfl⟩ : syracuseStep 2299223 = 3448835) B3448835
theorem B4364941 : Blo 2297435 4364941 := bbase (se 3 (by rfl) ⟨818426, by rfl⟩ : syracuseStep 4364941 = 1636853) (by norm_num)
theorem B5819921 : Blo 2297435 5819921 := bstep (se 2 (by rfl) ⟨2182470, by rfl⟩ : syracuseStep 5819921 = 4364941) B4364941
theorem B3879947 : Blo 2297435 3879947 := bstep (se 1 (by rfl) ⟨2909960, by rfl⟩ : syracuseStep 3879947 = 5819921) B5819921
theorem B2586631 : Blo 2297435 2586631 := bstep (se 1 (by rfl) ⟨1939973, by rfl⟩ : syracuseStep 2586631 = 3879947) B3879947
theorem B3448841 : Blo 2297435 3448841 := bstep (se 2 (by rfl) ⟨1293315, by rfl⟩ : syracuseStep 3448841 = 2586631) B2586631
theorem B2299227 : Blo 2297435 2299227 := bstep (se 1 (by rfl) ⟨1724420, by rfl⟩ : syracuseStep 2299227 = 3448841) B3448841
theorem B11639861 : Blo 2297435 11639861 := bbase (se 5 (by rfl) ⟨545618, by rfl⟩ : syracuseStep 11639861 = 1091237) (by norm_num)
theorem B7759907 : Blo 2297435 7759907 := bstep (se 1 (by rfl) ⟨5819930, by rfl⟩ : syracuseStep 7759907 = 11639861) B11639861
theorem B5173271 : Blo 2297435 5173271 := bstep (se 1 (by rfl) ⟨3879953, by rfl⟩ : syracuseStep 5173271 = 7759907) B7759907
theorem B3448847 : Blo 2297435 3448847 := bstep (se 1 (by rfl) ⟨2586635, by rfl⟩ : syracuseStep 3448847 = 5173271) B5173271
theorem B2299231 : Blo 2297435 2299231 := bstep (se 1 (by rfl) ⟨1724423, by rfl⟩ : syracuseStep 2299231 = 3448847) B3448847
theorem B3448853 : Blo 2297435 3448853 := bbase (se 6 (by rfl) ⟨80832, by rfl⟩ : syracuseStep 3448853 = 161665) (by norm_num)
theorem B2299235 : Blo 2297435 2299235 := bstep (se 1 (by rfl) ⟨1724426, by rfl⟩ : syracuseStep 2299235 = 3448853) B3448853
theorem B8399669 : Blo 2297435 8399669 := bbase (se 5 (by rfl) ⟨393734, by rfl⟩ : syracuseStep 8399669 = 787469) (by norm_num)
theorem B89596469 : Blo 2297435 89596469 := bstep (se 5 (by rfl) ⟨4199834, by rfl⟩ : syracuseStep 89596469 = 8399669) B8399669
theorem B59730979 : Blo 2297435 59730979 := bstep (se 1 (by rfl) ⟨44798234, by rfl⟩ : syracuseStep 59730979 = 89596469) B89596469
theorem B79641305 : Blo 2297435 79641305 := bstep (se 2 (by rfl) ⟨29865489, by rfl⟩ : syracuseStep 79641305 = 59730979) B59730979
theorem B53094203 : Blo 2297435 53094203 := bstep (se 1 (by rfl) ⟨39820652, by rfl⟩ : syracuseStep 53094203 = 79641305) B79641305
theorem B35396135 : Blo 2297435 35396135 := bstep (se 1 (by rfl) ⟨26547101, by rfl⟩ : syracuseStep 35396135 = 53094203) B53094203
theorem B23597423 : Blo 2297435 23597423 := bstep (se 1 (by rfl) ⟨17698067, by rfl⟩ : syracuseStep 23597423 = 35396135) B35396135
theorem B15731615 : Blo 2297435 15731615 := bstep (se 1 (by rfl) ⟨11798711, by rfl⟩ : syracuseStep 15731615 = 23597423) B23597423
theorem B41950973 : Blo 2297435 41950973 := bstep (se 3 (by rfl) ⟨7865807, by rfl⟩ : syracuseStep 41950973 = 15731615) B15731615
theorem B27967315 : Blo 2297435 27967315 := bstep (se 1 (by rfl) ⟨20975486, by rfl⟩ : syracuseStep 27967315 = 41950973) B41950973
theorem B37289753 : Blo 2297435 37289753 := bstep (se 2 (by rfl) ⟨13983657, by rfl⟩ : syracuseStep 37289753 = 27967315) B27967315
theorem B24859835 : Blo 2297435 24859835 := bstep (se 1 (by rfl) ⟨18644876, by rfl⟩ : syracuseStep 24859835 = 37289753) B37289753
theorem B16573223 : Blo 2297435 16573223 := bstep (se 1 (by rfl) ⟨12429917, by rfl⟩ : syracuseStep 16573223 = 24859835) B24859835
theorem B11048815 : Blo 2297435 11048815 := bstep (se 1 (by rfl) ⟨8286611, by rfl⟩ : syracuseStep 11048815 = 16573223) B16573223
theorem B14731753 : Blo 2297435 14731753 := bstep (se 2 (by rfl) ⟨5524407, by rfl⟩ : syracuseStep 14731753 = 11048815) B11048815
theorem B19642337 : Blo 2297435 19642337 := bstep (se 2 (by rfl) ⟨7365876, by rfl⟩ : syracuseStep 19642337 = 14731753) B14731753
theorem B13094891 : Blo 2297435 13094891 := bstep (se 1 (by rfl) ⟨9821168, by rfl⟩ : syracuseStep 13094891 = 19642337) B19642337
theorem B8729927 : Blo 2297435 8729927 := bstep (se 1 (by rfl) ⟨6547445, by rfl⟩ : syracuseStep 8729927 = 13094891) B13094891
theorem B5819951 : Blo 2297435 5819951 := bstep (se 1 (by rfl) ⟨4364963, by rfl⟩ : syracuseStep 5819951 = 8729927) B8729927
theorem B3879967 : Blo 2297435 3879967 := bstep (se 1 (by rfl) ⟨2909975, by rfl⟩ : syracuseStep 3879967 = 5819951) B5819951
theorem B5173289 : Blo 2297435 5173289 := bstep (se 2 (by rfl) ⟨1939983, by rfl⟩ : syracuseStep 5173289 = 3879967) B3879967
theorem B3448859 : Blo 2297435 3448859 := bstep (se 1 (by rfl) ⟨2586644, by rfl⟩ : syracuseStep 3448859 = 5173289) B5173289
theorem B2299239 : Blo 2297435 2299239 := bstep (se 1 (by rfl) ⟨1724429, by rfl⟩ : syracuseStep 2299239 = 3448859) B3448859
theorem B2586649 : Blo 2297435 2586649 := bbase (se 2 (by rfl) ⟨969993, by rfl⟩ : syracuseStep 2586649 = 1939987) (by norm_num)
theorem B3448865 : Blo 2297435 3448865 := bstep (se 2 (by rfl) ⟨1293324, by rfl⟩ : syracuseStep 3448865 = 2586649) B2586649
theorem B2299243 : Blo 2297435 2299243 := bstep (se 1 (by rfl) ⟨1724432, by rfl⟩ : syracuseStep 2299243 = 3448865) B3448865
theorem B8729957 : Blo 2297435 8729957 := bbase (se 4 (by rfl) ⟨818433, by rfl⟩ : syracuseStep 8729957 = 1636867) (by norm_num)
theorem B5819971 : Blo 2297435 5819971 := bstep (se 1 (by rfl) ⟨4364978, by rfl⟩ : syracuseStep 5819971 = 8729957) B8729957
theorem B7759961 : Blo 2297435 7759961 := bstep (se 2 (by rfl) ⟨2909985, by rfl⟩ : syracuseStep 7759961 = 5819971) B5819971
theorem B5173307 : Blo 2297435 5173307 := bstep (se 1 (by rfl) ⟨3879980, by rfl⟩ : syracuseStep 5173307 = 7759961) B7759961
theorem B3448871 : Blo 2297435 3448871 := bstep (se 1 (by rfl) ⟨2586653, by rfl⟩ : syracuseStep 3448871 = 5173307) B5173307
theorem B2299247 : Blo 2297435 2299247 := bstep (se 1 (by rfl) ⟨1724435, by rfl⟩ : syracuseStep 2299247 = 3448871) B3448871
theorem B3448877 : Blo 2297435 3448877 := bbase (se 3 (by rfl) ⟨646664, by rfl⟩ : syracuseStep 3448877 = 1293329) (by norm_num)
theorem B2299251 : Blo 2297435 2299251 := bstep (se 1 (by rfl) ⟨1724438, by rfl⟩ : syracuseStep 2299251 = 3448877) B3448877
theorem B5173325 : Blo 2297435 5173325 := bbase (se 3 (by rfl) ⟨969998, by rfl⟩ : syracuseStep 5173325 = 1939997) (by norm_num)
theorem B3448883 : Blo 2297435 3448883 := bstep (se 1 (by rfl) ⟨2586662, by rfl⟩ : syracuseStep 3448883 = 5173325) B5173325
theorem B2299255 : Blo 2297435 2299255 := bstep (se 1 (by rfl) ⟨1724441, by rfl⟩ : syracuseStep 2299255 = 3448883) B3448883
theorem B2910001 : Blo 2297435 2910001 := bbase (se 2 (by rfl) ⟨1091250, by rfl⟩ : syracuseStep 2910001 = 2182501) (by norm_num)
theorem B3880001 : Blo 2297435 3880001 := bstep (se 2 (by rfl) ⟨1455000, by rfl⟩ : syracuseStep 3880001 = 2910001) B2910001
theorem B2586667 : Blo 2297435 2586667 := bstep (se 1 (by rfl) ⟨1940000, by rfl⟩ : syracuseStep 2586667 = 3880001) B3880001
theorem B3448889 : Blo 2297435 3448889 := bstep (se 2 (by rfl) ⟨1293333, by rfl⟩ : syracuseStep 3448889 = 2586667) B2586667
theorem B2299259 : Blo 2297435 2299259 := bstep (se 1 (by rfl) ⟨1724444, by rfl⟩ : syracuseStep 2299259 = 3448889) B3448889
theorem B4143349 : Blo 2297435 4143349 := bbase (se 5 (by rfl) ⟨194219, by rfl⟩ : syracuseStep 4143349 = 388439) (by norm_num)
theorem B5524465 : Blo 2297435 5524465 := bstep (se 2 (by rfl) ⟨2071674, by rfl⟩ : syracuseStep 5524465 = 4143349) B4143349
theorem B7365953 : Blo 2297435 7365953 := bstep (se 2 (by rfl) ⟨2762232, by rfl⟩ : syracuseStep 7365953 = 5524465) B5524465
theorem B4910635 : Blo 2297435 4910635 := bstep (se 1 (by rfl) ⟨3682976, by rfl⟩ : syracuseStep 4910635 = 7365953) B7365953
theorem B26190053 : Blo 2297435 26190053 := bstep (se 4 (by rfl) ⟨2455317, by rfl⟩ : syracuseStep 26190053 = 4910635) B4910635
theorem B17460035 : Blo 2297435 17460035 := bstep (se 1 (by rfl) ⟨13095026, by rfl⟩ : syracuseStep 17460035 = 26190053) B26190053
theorem B11640023 : Blo 2297435 11640023 := bstep (se 1 (by rfl) ⟨8730017, by rfl⟩ : syracuseStep 11640023 = 17460035) B17460035
theorem B7760015 : Blo 2297435 7760015 := bstep (se 1 (by rfl) ⟨5820011, by rfl⟩ : syracuseStep 7760015 = 11640023) B11640023
theorem B5173343 : Blo 2297435 5173343 := bstep (se 1 (by rfl) ⟨3880007, by rfl⟩ : syracuseStep 5173343 = 7760015) B7760015
theorem B3448895 : Blo 2297435 3448895 := bstep (se 1 (by rfl) ⟨2586671, by rfl⟩ : syracuseStep 3448895 = 5173343) B5173343
theorem B2299263 : Blo 2297435 2299263 := bstep (se 1 (by rfl) ⟨1724447, by rfl⟩ : syracuseStep 2299263 = 3448895) B3448895
theorem B3448901 : Blo 2297435 3448901 := bbase (se 4 (by rfl) ⟨323334, by rfl⟩ : syracuseStep 3448901 = 646669) (by norm_num)
theorem B2299267 : Blo 2297435 2299267 := bstep (se 1 (by rfl) ⟨1724450, by rfl⟩ : syracuseStep 2299267 = 3448901) B3448901
theorem B3880021 : Blo 2297435 3880021 := bbase (se 8 (by rfl) ⟨22734, by rfl⟩ : syracuseStep 3880021 = 45469) (by norm_num)
theorem B5173361 : Blo 2297435 5173361 := bstep (se 2 (by rfl) ⟨1940010, by rfl⟩ : syracuseStep 5173361 = 3880021) B3880021
theorem B3448907 : Blo 2297435 3448907 := bstep (se 1 (by rfl) ⟨2586680, by rfl⟩ : syracuseStep 3448907 = 5173361) B5173361
theorem B2299271 : Blo 2297435 2299271 := bstep (se 1 (by rfl) ⟨1724453, by rfl⟩ : syracuseStep 2299271 = 3448907) B3448907
theorem B2586685 : Blo 2297435 2586685 := bbase (se 3 (by rfl) ⟨485003, by rfl⟩ : syracuseStep 2586685 = 970007) (by norm_num)
theorem B3448913 : Blo 2297435 3448913 := bstep (se 2 (by rfl) ⟨1293342, by rfl⟩ : syracuseStep 3448913 = 2586685) B2586685
theorem B2299275 : Blo 2297435 2299275 := bstep (se 1 (by rfl) ⟨1724456, by rfl⟩ : syracuseStep 2299275 = 3448913) B3448913
theorem B7760069 : Blo 2297435 7760069 := bbase (se 4 (by rfl) ⟨727506, by rfl⟩ : syracuseStep 7760069 = 1455013) (by norm_num)
theorem B5173379 : Blo 2297435 5173379 := bstep (se 1 (by rfl) ⟨3880034, by rfl⟩ : syracuseStep 5173379 = 7760069) B7760069
theorem B3448919 : Blo 2297435 3448919 := bstep (se 1 (by rfl) ⟨2586689, by rfl⟩ : syracuseStep 3448919 = 5173379) B5173379
theorem B2299279 : Blo 2297435 2299279 := bstep (se 1 (by rfl) ⟨1724459, by rfl⟩ : syracuseStep 2299279 = 3448919) B3448919
theorem B3448925 : Blo 2297435 3448925 := bbase (se 3 (by rfl) ⟨646673, by rfl⟩ : syracuseStep 3448925 = 1293347) (by norm_num)
theorem B2299283 : Blo 2297435 2299283 := bstep (se 1 (by rfl) ⟨1724462, by rfl⟩ : syracuseStep 2299283 = 3448925) B3448925
theorem B5173397 : Blo 2297435 5173397 := bbase (se 6 (by rfl) ⟨121251, by rfl⟩ : syracuseStep 5173397 = 242503) (by norm_num)
theorem B3448931 : Blo 2297435 3448931 := bstep (se 1 (by rfl) ⟨2586698, by rfl⟩ : syracuseStep 3448931 = 5173397) B5173397
theorem B2299287 : Blo 2297435 2299287 := bstep (se 1 (by rfl) ⟨1724465, by rfl⟩ : syracuseStep 2299287 = 3448931) B3448931
theorem B3273797 : Blo 2297435 3273797 := bbase (se 4 (by rfl) ⟨306918, by rfl⟩ : syracuseStep 3273797 = 613837) (by norm_num)
theorem B8730125 : Blo 2297435 8730125 := bstep (se 3 (by rfl) ⟨1636898, by rfl⟩ : syracuseStep 8730125 = 3273797) B3273797
theorem B5820083 : Blo 2297435 5820083 := bstep (se 1 (by rfl) ⟨4365062, by rfl⟩ : syracuseStep 5820083 = 8730125) B8730125
theorem B3880055 : Blo 2297435 3880055 := bstep (se 1 (by rfl) ⟨2910041, by rfl⟩ : syracuseStep 3880055 = 5820083) B5820083
theorem B2586703 : Blo 2297435 2586703 := bstep (se 1 (by rfl) ⟨1940027, by rfl⟩ : syracuseStep 2586703 = 3880055) B3880055
theorem B3448937 : Blo 2297435 3448937 := bstep (se 2 (by rfl) ⟨1293351, by rfl⟩ : syracuseStep 3448937 = 2586703) B2586703
theorem B2299291 : Blo 2297435 2299291 := bstep (se 1 (by rfl) ⟨1724468, by rfl⟩ : syracuseStep 2299291 = 3448937) B3448937
theorem B2362465 : Blo 2297435 2362465 := bbase (se 2 (by rfl) ⟨885924, by rfl⟩ : syracuseStep 2362465 = 1771849) (by norm_num)
theorem B12599813 : Blo 2297435 12599813 := bstep (se 4 (by rfl) ⟨1181232, by rfl⟩ : syracuseStep 12599813 = 2362465) B2362465
theorem B8399875 : Blo 2297435 8399875 := bstep (se 1 (by rfl) ⟨6299906, by rfl⟩ : syracuseStep 8399875 = 12599813) B12599813
theorem B11199833 : Blo 2297435 11199833 := bstep (se 2 (by rfl) ⟨4199937, by rfl⟩ : syracuseStep 11199833 = 8399875) B8399875
theorem B7466555 : Blo 2297435 7466555 := bstep (se 1 (by rfl) ⟨5599916, by rfl⟩ : syracuseStep 7466555 = 11199833) B11199833
theorem B4977703 : Blo 2297435 4977703 := bstep (se 1 (by rfl) ⟨3733277, by rfl⟩ : syracuseStep 4977703 = 7466555) B7466555
theorem B26547749 : Blo 2297435 26547749 := bstep (se 4 (by rfl) ⟨2488851, by rfl⟩ : syracuseStep 26547749 = 4977703) B4977703
theorem B17698499 : Blo 2297435 17698499 := bstep (se 1 (by rfl) ⟨13273874, by rfl⟩ : syracuseStep 17698499 = 26547749) B26547749
theorem B11798999 : Blo 2297435 11798999 := bstep (se 1 (by rfl) ⟨8849249, by rfl⟩ : syracuseStep 11798999 = 17698499) B17698499
theorem B7865999 : Blo 2297435 7865999 := bstep (se 1 (by rfl) ⟨5899499, by rfl⟩ : syracuseStep 7865999 = 11798999) B11798999
theorem B5243999 : Blo 2297435 5243999 := bstep (se 1 (by rfl) ⟨3932999, by rfl⟩ : syracuseStep 5243999 = 7865999) B7865999
theorem B13983997 : Blo 2297435 13983997 := bstep (se 3 (by rfl) ⟨2621999, by rfl⟩ : syracuseStep 13983997 = 5243999) B5243999
theorem B18645329 : Blo 2297435 18645329 := bstep (se 2 (by rfl) ⟨6991998, by rfl⟩ : syracuseStep 18645329 = 13983997) B13983997
theorem B49720877 : Blo 2297435 49720877 := bstep (se 3 (by rfl) ⟨9322664, by rfl⟩ : syracuseStep 49720877 = 18645329) B18645329
theorem B33147251 : Blo 2297435 33147251 := bstep (se 1 (by rfl) ⟨24860438, by rfl⟩ : syracuseStep 33147251 = 49720877) B49720877
theorem B22098167 : Blo 2297435 22098167 := bstep (se 1 (by rfl) ⟨16573625, by rfl⟩ : syracuseStep 22098167 = 33147251) B33147251
theorem B14732111 : Blo 2297435 14732111 := bstep (se 1 (by rfl) ⟨11049083, by rfl⟩ : syracuseStep 14732111 = 22098167) B22098167
theorem B9821407 : Blo 2297435 9821407 := bstep (se 1 (by rfl) ⟨7366055, by rfl⟩ : syracuseStep 9821407 = 14732111) B14732111
theorem B13095209 : Blo 2297435 13095209 := bstep (se 2 (by rfl) ⟨4910703, by rfl⟩ : syracuseStep 13095209 = 9821407) B9821407
theorem B8730139 : Blo 2297435 8730139 := bstep (se 1 (by rfl) ⟨6547604, by rfl⟩ : syracuseStep 8730139 = 13095209) B13095209
theorem B11640185 : Blo 2297435 11640185 := bstep (se 2 (by rfl) ⟨4365069, by rfl⟩ : syracuseStep 11640185 = 8730139) B8730139
theorem B7760123 : Blo 2297435 7760123 := bstep (se 1 (by rfl) ⟨5820092, by rfl⟩ : syracuseStep 7760123 = 11640185) B11640185
theorem B5173415 : Blo 2297435 5173415 := bstep (se 1 (by rfl) ⟨3880061, by rfl⟩ : syracuseStep 5173415 = 7760123) B7760123
theorem B3448943 : Blo 2297435 3448943 := bstep (se 1 (by rfl) ⟨2586707, by rfl⟩ : syracuseStep 3448943 = 5173415) B5173415
theorem B2299295 : Blo 2297435 2299295 := bstep (se 1 (by rfl) ⟨1724471, by rfl⟩ : syracuseStep 2299295 = 3448943) B3448943
theorem B3448949 : Blo 2297435 3448949 := bbase (se 5 (by rfl) ⟨161669, by rfl⟩ : syracuseStep 3448949 = 323339) (by norm_num)
theorem B2299299 : Blo 2297435 2299299 := bstep (se 1 (by rfl) ⟨1724474, by rfl⟩ : syracuseStep 2299299 = 3448949) B3448949
theorem B4365085 : Blo 2297435 4365085 := bbase (se 3 (by rfl) ⟨818453, by rfl⟩ : syracuseStep 4365085 = 1636907) (by norm_num)
theorem B5820113 : Blo 2297435 5820113 := bstep (se 2 (by rfl) ⟨2182542, by rfl⟩ : syracuseStep 5820113 = 4365085) B4365085
theorem B3880075 : Blo 2297435 3880075 := bstep (se 1 (by rfl) ⟨2910056, by rfl⟩ : syracuseStep 3880075 = 5820113) B5820113
theorem B5173433 : Blo 2297435 5173433 := bstep (se 2 (by rfl) ⟨1940037, by rfl⟩ : syracuseStep 5173433 = 3880075) B3880075
theorem B3448955 : Blo 2297435 3448955 := bstep (se 1 (by rfl) ⟨2586716, by rfl⟩ : syracuseStep 3448955 = 5173433) B5173433
theorem B2299303 : Blo 2297435 2299303 := bstep (se 1 (by rfl) ⟨1724477, by rfl⟩ : syracuseStep 2299303 = 3448955) B3448955
theorem B2586721 : Blo 2297435 2586721 := bbase (se 2 (by rfl) ⟨970020, by rfl⟩ : syracuseStep 2586721 = 1940041) (by norm_num)
theorem B3448961 : Blo 2297435 3448961 := bstep (se 2 (by rfl) ⟨1293360, by rfl⟩ : syracuseStep 3448961 = 2586721) B2586721
theorem B2299307 : Blo 2297435 2299307 := bstep (se 1 (by rfl) ⟨1724480, by rfl⟩ : syracuseStep 2299307 = 3448961) B3448961
theorem B5820133 : Blo 2297435 5820133 := bbase (se 4 (by rfl) ⟨545637, by rfl⟩ : syracuseStep 5820133 = 1091275) (by norm_num)
theorem B7760177 : Blo 2297435 7760177 := bstep (se 2 (by rfl) ⟨2910066, by rfl⟩ : syracuseStep 7760177 = 5820133) B5820133
theorem B5173451 : Blo 2297435 5173451 := bstep (se 1 (by rfl) ⟨3880088, by rfl⟩ : syracuseStep 5173451 = 7760177) B7760177
theorem B3448967 : Blo 2297435 3448967 := bstep (se 1 (by rfl) ⟨2586725, by rfl⟩ : syracuseStep 3448967 = 5173451) B5173451
theorem B2299311 : Blo 2297435 2299311 := bstep (se 1 (by rfl) ⟨1724483, by rfl⟩ : syracuseStep 2299311 = 3448967) B3448967
theorem B3448973 : Blo 2297435 3448973 := bbase (se 3 (by rfl) ⟨646682, by rfl⟩ : syracuseStep 3448973 = 1293365) (by norm_num)
theorem B2299315 : Blo 2297435 2299315 := bstep (se 1 (by rfl) ⟨1724486, by rfl⟩ : syracuseStep 2299315 = 3448973) B3448973
theorem B5173469 : Blo 2297435 5173469 := bbase (se 3 (by rfl) ⟨970025, by rfl⟩ : syracuseStep 5173469 = 1940051) (by norm_num)
theorem B3448979 : Blo 2297435 3448979 := bstep (se 1 (by rfl) ⟨2586734, by rfl⟩ : syracuseStep 3448979 = 5173469) B5173469
theorem B2299319 : Blo 2297435 2299319 := bstep (se 1 (by rfl) ⟨1724489, by rfl⟩ : syracuseStep 2299319 = 3448979) B3448979
theorem B3880109 : Blo 2297435 3880109 := bbase (se 3 (by rfl) ⟨727520, by rfl⟩ : syracuseStep 3880109 = 1455041) (by norm_num)
theorem B2586739 : Blo 2297435 2586739 := bstep (se 1 (by rfl) ⟨1940054, by rfl⟩ : syracuseStep 2586739 = 3880109) B3880109
theorem B3448985 : Blo 2297435 3448985 := bstep (se 2 (by rfl) ⟨1293369, by rfl⟩ : syracuseStep 3448985 = 2586739) B2586739
theorem B2299323 : Blo 2297435 2299323 := bstep (se 1 (by rfl) ⟨1724492, by rfl⟩ : syracuseStep 2299323 = 3448985) B3448985
theorem B8399989 : Blo 2297435 8399989 := bbase (se 5 (by rfl) ⟨393749, by rfl⟩ : syracuseStep 8399989 = 787499) (by norm_num)
theorem B44799941 : Blo 2297435 44799941 := bstep (se 4 (by rfl) ⟨4199994, by rfl⟩ : syracuseStep 44799941 = 8399989) B8399989
theorem B29866627 : Blo 2297435 29866627 := bstep (se 1 (by rfl) ⟨22399970, by rfl⟩ : syracuseStep 29866627 = 44799941) B44799941
theorem B159288677 : Blo 2297435 159288677 := bstep (se 4 (by rfl) ⟨14933313, by rfl⟩ : syracuseStep 159288677 = 29866627) B29866627
theorem B106192451 : Blo 2297435 106192451 := bstep (se 1 (by rfl) ⟨79644338, by rfl⟩ : syracuseStep 106192451 = 159288677) B159288677
theorem B70794967 : Blo 2297435 70794967 := bstep (se 1 (by rfl) ⟨53096225, by rfl⟩ : syracuseStep 70794967 = 106192451) B106192451
theorem B94393289 : Blo 2297435 94393289 := bstep (se 2 (by rfl) ⟨35397483, by rfl⟩ : syracuseStep 94393289 = 70794967) B70794967
theorem B62928859 : Blo 2297435 62928859 := bstep (se 1 (by rfl) ⟨47196644, by rfl⟩ : syracuseStep 62928859 = 94393289) B94393289
theorem B83905145 : Blo 2297435 83905145 := bstep (se 2 (by rfl) ⟨31464429, by rfl⟩ : syracuseStep 83905145 = 62928859) B62928859
theorem B55936763 : Blo 2297435 55936763 := bstep (se 1 (by rfl) ⟨41952572, by rfl⟩ : syracuseStep 55936763 = 83905145) B83905145
theorem B37291175 : Blo 2297435 37291175 := bstep (se 1 (by rfl) ⟨27968381, by rfl⟩ : syracuseStep 37291175 = 55936763) B55936763
theorem B24860783 : Blo 2297435 24860783 := bstep (se 1 (by rfl) ⟨18645587, by rfl⟩ : syracuseStep 24860783 = 37291175) B37291175
theorem B66295421 : Blo 2297435 66295421 := bstep (se 3 (by rfl) ⟨12430391, by rfl⟩ : syracuseStep 66295421 = 24860783) B24860783
theorem B44196947 : Blo 2297435 44196947 := bstep (se 1 (by rfl) ⟨33147710, by rfl⟩ : syracuseStep 44196947 = 66295421) B66295421
theorem B29464631 : Blo 2297435 29464631 := bstep (se 1 (by rfl) ⟨22098473, by rfl⟩ : syracuseStep 29464631 = 44196947) B44196947
theorem B19643087 : Blo 2297435 19643087 := bstep (se 1 (by rfl) ⟨14732315, by rfl⟩ : syracuseStep 19643087 = 29464631) B29464631
theorem B13095391 : Blo 2297435 13095391 := bstep (se 1 (by rfl) ⟨9821543, by rfl⟩ : syracuseStep 13095391 = 19643087) B19643087
theorem B17460521 : Blo 2297435 17460521 := bstep (se 2 (by rfl) ⟨6547695, by rfl⟩ : syracuseStep 17460521 = 13095391) B13095391
theorem B11640347 : Blo 2297435 11640347 := bstep (se 1 (by rfl) ⟨8730260, by rfl⟩ : syracuseStep 11640347 = 17460521) B17460521
theorem B7760231 : Blo 2297435 7760231 := bstep (se 1 (by rfl) ⟨5820173, by rfl⟩ : syracuseStep 7760231 = 11640347) B11640347
theorem B5173487 : Blo 2297435 5173487 := bstep (se 1 (by rfl) ⟨3880115, by rfl⟩ : syracuseStep 5173487 = 7760231) B7760231
theorem B3448991 : Blo 2297435 3448991 := bstep (se 1 (by rfl) ⟨2586743, by rfl⟩ : syracuseStep 3448991 = 5173487) B5173487
theorem B2299327 : Blo 2297435 2299327 := bstep (se 1 (by rfl) ⟨1724495, by rfl⟩ : syracuseStep 2299327 = 3448991) B3448991
theorem B3448997 : Blo 2297435 3448997 := bbase (se 4 (by rfl) ⟨323343, by rfl⟩ : syracuseStep 3448997 = 646687) (by norm_num)
theorem B2299331 : Blo 2297435 2299331 := bstep (se 1 (by rfl) ⟨1724498, by rfl⟩ : syracuseStep 2299331 = 3448997) B3448997
theorem B2910097 : Blo 2297435 2910097 := bbase (se 2 (by rfl) ⟨1091286, by rfl⟩ : syracuseStep 2910097 = 2182573) (by norm_num)
theorem B3880129 : Blo 2297435 3880129 := bstep (se 2 (by rfl) ⟨1455048, by rfl⟩ : syracuseStep 3880129 = 2910097) B2910097
theorem B5173505 : Blo 2297435 5173505 := bstep (se 2 (by rfl) ⟨1940064, by rfl⟩ : syracuseStep 5173505 = 3880129) B3880129
theorem B3449003 : Blo 2297435 3449003 := bstep (se 1 (by rfl) ⟨2586752, by rfl⟩ : syracuseStep 3449003 = 5173505) B5173505
theorem B2299335 : Blo 2297435 2299335 := bstep (se 1 (by rfl) ⟨1724501, by rfl⟩ : syracuseStep 2299335 = 3449003) B3449003
theorem B2586757 : Blo 2297435 2586757 := bbase (se 4 (by rfl) ⟨242508, by rfl⟩ : syracuseStep 2586757 = 485017) (by norm_num)
theorem B3449009 : Blo 2297435 3449009 := bstep (se 2 (by rfl) ⟨1293378, by rfl⟩ : syracuseStep 3449009 = 2586757) B2586757
theorem B2299339 : Blo 2297435 2299339 := bstep (se 1 (by rfl) ⟨1724504, by rfl⟩ : syracuseStep 2299339 = 3449009) B3449009
theorem B11049317 : Blo 2297435 11049317 := bbase (se 4 (by rfl) ⟨1035873, by rfl⟩ : syracuseStep 11049317 = 2071747) (by norm_num)
theorem B7366211 : Blo 2297435 7366211 := bstep (se 1 (by rfl) ⟨5524658, by rfl⟩ : syracuseStep 7366211 = 11049317) B11049317
theorem B4910807 : Blo 2297435 4910807 := bstep (se 1 (by rfl) ⟨3683105, by rfl⟩ : syracuseStep 4910807 = 7366211) B7366211
theorem B3273871 : Blo 2297435 3273871 := bstep (se 1 (by rfl) ⟨2455403, by rfl⟩ : syracuseStep 3273871 = 4910807) B4910807
theorem B4365161 : Blo 2297435 4365161 := bstep (se 2 (by rfl) ⟨1636935, by rfl⟩ : syracuseStep 4365161 = 3273871) B3273871
theorem B2910107 : Blo 2297435 2910107 := bstep (se 1 (by rfl) ⟨2182580, by rfl⟩ : syracuseStep 2910107 = 4365161) B4365161
theorem B7760285 : Blo 2297435 7760285 := bstep (se 3 (by rfl) ⟨1455053, by rfl⟩ : syracuseStep 7760285 = 2910107) B2910107
theorem B5173523 : Blo 2297435 5173523 := bstep (se 1 (by rfl) ⟨3880142, by rfl⟩ : syracuseStep 5173523 = 7760285) B7760285
theorem B3449015 : Blo 2297435 3449015 := bstep (se 1 (by rfl) ⟨2586761, by rfl⟩ : syracuseStep 3449015 = 5173523) B5173523
theorem B2299343 : Blo 2297435 2299343 := bstep (se 1 (by rfl) ⟨1724507, by rfl⟩ : syracuseStep 2299343 = 3449015) B3449015
theorem B3449021 : Blo 2297435 3449021 := bbase (se 3 (by rfl) ⟨646691, by rfl⟩ : syracuseStep 3449021 = 1293383) (by norm_num)
theorem B2299347 : Blo 2297435 2299347 := bstep (se 1 (by rfl) ⟨1724510, by rfl⟩ : syracuseStep 2299347 = 3449021) B3449021
theorem B5173541 : Blo 2297435 5173541 := bbase (se 4 (by rfl) ⟨485019, by rfl⟩ : syracuseStep 5173541 = 970039) (by norm_num)
theorem B3449027 : Blo 2297435 3449027 := bstep (se 1 (by rfl) ⟨2586770, by rfl⟩ : syracuseStep 3449027 = 5173541) B5173541
theorem B2299351 : Blo 2297435 2299351 := bstep (se 1 (by rfl) ⟨1724513, by rfl⟩ : syracuseStep 2299351 = 3449027) B3449027
theorem B5820245 : Blo 2297435 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B3880163 : Blo 2297435 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B2586775 : Blo 2297435 2586775 := bstep (se 1 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 2586775 = 3880163) B3880163
theorem B3449033 : Blo 2297435 3449033 := bstep (se 2 (by rfl) ⟨1293387, by rfl⟩ : syracuseStep 3449033 = 2586775) B2586775
theorem B2299355 : Blo 2297435 2299355 := bstep (se 1 (by rfl) ⟨1724516, by rfl⟩ : syracuseStep 2299355 = 3449033) B3449033
theorem B7366261 : Blo 2297435 7366261 := bbase (se 5 (by rfl) ⟨345293, by rfl⟩ : syracuseStep 7366261 = 690587) (by norm_num)
theorem B9821681 : Blo 2297435 9821681 := bstep (se 2 (by rfl) ⟨3683130, by rfl⟩ : syracuseStep 9821681 = 7366261) B7366261
theorem B6547787 : Blo 2297435 6547787 := bstep (se 1 (by rfl) ⟨4910840, by rfl⟩ : syracuseStep 6547787 = 9821681) B9821681
theorem B4365191 : Blo 2297435 4365191 := bstep (se 1 (by rfl) ⟨3273893, by rfl⟩ : syracuseStep 4365191 = 6547787) B6547787
theorem B11640509 : Blo 2297435 11640509 := bstep (se 3 (by rfl) ⟨2182595, by rfl⟩ : syracuseStep 11640509 = 4365191) B4365191
theorem B7760339 : Blo 2297435 7760339 := bstep (se 1 (by rfl) ⟨5820254, by rfl⟩ : syracuseStep 7760339 = 11640509) B11640509
theorem B5173559 : Blo 2297435 5173559 := bstep (se 1 (by rfl) ⟨3880169, by rfl⟩ : syracuseStep 5173559 = 7760339) B7760339
theorem B3449039 : Blo 2297435 3449039 := bstep (se 1 (by rfl) ⟨2586779, by rfl⟩ : syracuseStep 3449039 = 5173559) B5173559
theorem B2299359 : Blo 2297435 2299359 := bstep (se 1 (by rfl) ⟨1724519, by rfl⟩ : syracuseStep 2299359 = 3449039) B3449039
theorem B3449045 : Blo 2297435 3449045 := bbase (se 7 (by rfl) ⟨40418, by rfl⟩ : syracuseStep 3449045 = 80837) (by norm_num)
theorem B2299363 : Blo 2297435 2299363 := bstep (se 1 (by rfl) ⟨1724522, by rfl⟩ : syracuseStep 2299363 = 3449045) B3449045
theorem B2455429 : Blo 2297435 2455429 := bbase (se 4 (by rfl) ⟨230196, by rfl⟩ : syracuseStep 2455429 = 460393) (by norm_num)
theorem B3273905 : Blo 2297435 3273905 := bstep (se 2 (by rfl) ⟨1227714, by rfl⟩ : syracuseStep 3273905 = 2455429) B2455429
theorem B8730413 : Blo 2297435 8730413 := bstep (se 3 (by rfl) ⟨1636952, by rfl⟩ : syracuseStep 8730413 = 3273905) B3273905
theorem B5820275 : Blo 2297435 5820275 := bstep (se 1 (by rfl) ⟨4365206, by rfl⟩ : syracuseStep 5820275 = 8730413) B8730413
theorem B3880183 : Blo 2297435 3880183 := bstep (se 1 (by rfl) ⟨2910137, by rfl⟩ : syracuseStep 3880183 = 5820275) B5820275
theorem B5173577 : Blo 2297435 5173577 := bstep (se 2 (by rfl) ⟨1940091, by rfl⟩ : syracuseStep 5173577 = 3880183) B3880183
theorem B3449051 : Blo 2297435 3449051 := bstep (se 1 (by rfl) ⟨2586788, by rfl⟩ : syracuseStep 3449051 = 5173577) B5173577
theorem B2299367 : Blo 2297435 2299367 := bstep (se 1 (by rfl) ⟨1724525, by rfl⟩ : syracuseStep 2299367 = 3449051) B3449051
theorem B2586793 : Blo 2297435 2586793 := bbase (se 2 (by rfl) ⟨970047, by rfl⟩ : syracuseStep 2586793 = 1940095) (by norm_num)
theorem B3449057 : Blo 2297435 3449057 := bstep (se 2 (by rfl) ⟨1293396, by rfl⟩ : syracuseStep 3449057 = 2586793) B2586793
theorem B2299371 : Blo 2297435 2299371 := bstep (se 1 (by rfl) ⟨1724528, by rfl⟩ : syracuseStep 2299371 = 3449057) B3449057
theorem B9821749 : Blo 2297435 9821749 := bbase (se 5 (by rfl) ⟨460394, by rfl⟩ : syracuseStep 9821749 = 920789) (by norm_num)
theorem B13095665 : Blo 2297435 13095665 := bstep (se 2 (by rfl) ⟨4910874, by rfl⟩ : syracuseStep 13095665 = 9821749) B9821749
theorem B8730443 : Blo 2297435 8730443 := bstep (se 1 (by rfl) ⟨6547832, by rfl⟩ : syracuseStep 8730443 = 13095665) B13095665
theorem B5820295 : Blo 2297435 5820295 := bstep (se 1 (by rfl) ⟨4365221, by rfl⟩ : syracuseStep 5820295 = 8730443) B8730443
theorem B7760393 : Blo 2297435 7760393 := bstep (se 2 (by rfl) ⟨2910147, by rfl⟩ : syracuseStep 7760393 = 5820295) B5820295
theorem B5173595 : Blo 2297435 5173595 := bstep (se 1 (by rfl) ⟨3880196, by rfl⟩ : syracuseStep 5173595 = 7760393) B7760393
theorem B3449063 : Blo 2297435 3449063 := bstep (se 1 (by rfl) ⟨2586797, by rfl⟩ : syracuseStep 3449063 = 5173595) B5173595
theorem B2299375 : Blo 2297435 2299375 := bstep (se 1 (by rfl) ⟨1724531, by rfl⟩ : syracuseStep 2299375 = 3449063) B3449063
theorem B3449069 : Blo 2297435 3449069 := bbase (se 3 (by rfl) ⟨646700, by rfl⟩ : syracuseStep 3449069 = 1293401) (by norm_num)
theorem B2299379 : Blo 2297435 2299379 := bstep (se 1 (by rfl) ⟨1724534, by rfl⟩ : syracuseStep 2299379 = 3449069) B3449069
theorem B5173613 : Blo 2297435 5173613 := bbase (se 3 (by rfl) ⟨970052, by rfl⟩ : syracuseStep 5173613 = 1940105) (by norm_num)
theorem B3449075 : Blo 2297435 3449075 := bstep (se 1 (by rfl) ⟨2586806, by rfl⟩ : syracuseStep 3449075 = 5173613) B5173613
theorem B2299383 : Blo 2297435 2299383 := bstep (se 1 (by rfl) ⟨1724537, by rfl⟩ : syracuseStep 2299383 = 3449075) B3449075
theorem B4365245 : Blo 2297435 4365245 := bbase (se 3 (by rfl) ⟨818483, by rfl⟩ : syracuseStep 4365245 = 1636967) (by norm_num)
theorem B2910163 : Blo 2297435 2910163 := bstep (se 1 (by rfl) ⟨2182622, by rfl⟩ : syracuseStep 2910163 = 4365245) B4365245
theorem B3880217 : Blo 2297435 3880217 := bstep (se 2 (by rfl) ⟨1455081, by rfl⟩ : syracuseStep 3880217 = 2910163) B2910163
theorem B2586811 : Blo 2297435 2586811 := bstep (se 1 (by rfl) ⟨1940108, by rfl⟩ : syracuseStep 2586811 = 3880217) B3880217
theorem B3449081 : Blo 2297435 3449081 := bstep (se 2 (by rfl) ⟨1293405, by rfl⟩ : syracuseStep 3449081 = 2586811) B2586811
theorem B2299387 : Blo 2297435 2299387 := bstep (se 1 (by rfl) ⟨1724540, by rfl⟩ : syracuseStep 2299387 = 3449081) B3449081
theorem B58930901 : Blo 2297435 58930901 := bbase (se 7 (by rfl) ⟨690596, by rfl⟩ : syracuseStep 58930901 = 1381193) (by norm_num)
theorem B39287267 : Blo 2297435 39287267 := bstep (se 1 (by rfl) ⟨29465450, by rfl⟩ : syracuseStep 39287267 = 58930901) B58930901
theorem B26191511 : Blo 2297435 26191511 := bstep (se 1 (by rfl) ⟨19643633, by rfl⟩ : syracuseStep 26191511 = 39287267) B39287267
theorem B17461007 : Blo 2297435 17461007 := bstep (se 1 (by rfl) ⟨13095755, by rfl⟩ : syracuseStep 17461007 = 26191511) B26191511
theorem B11640671 : Blo 2297435 11640671 := bstep (se 1 (by rfl) ⟨8730503, by rfl⟩ : syracuseStep 11640671 = 17461007) B17461007
theorem B7760447 : Blo 2297435 7760447 := bstep (se 1 (by rfl) ⟨5820335, by rfl⟩ : syracuseStep 7760447 = 11640671) B11640671
theorem B5173631 : Blo 2297435 5173631 := bstep (se 1 (by rfl) ⟨3880223, by rfl⟩ : syracuseStep 5173631 = 7760447) B7760447
theorem B3449087 : Blo 2297435 3449087 := bstep (se 1 (by rfl) ⟨2586815, by rfl⟩ : syracuseStep 3449087 = 5173631) B5173631
theorem B2299391 : Blo 2297435 2299391 := bstep (se 1 (by rfl) ⟨1724543, by rfl⟩ : syracuseStep 2299391 = 3449087) B3449087
theorem B3449093 : Blo 2297435 3449093 := bbase (se 4 (by rfl) ⟨323352, by rfl⟩ : syracuseStep 3449093 = 646705) (by norm_num)
theorem B2299395 : Blo 2297435 2299395 := bstep (se 1 (by rfl) ⟨1724546, by rfl⟩ : syracuseStep 2299395 = 3449093) B3449093
theorem B3880237 : Blo 2297435 3880237 := bbase (se 3 (by rfl) ⟨727544, by rfl⟩ : syracuseStep 3880237 = 1455089) (by norm_num)
theorem B5173649 : Blo 2297435 5173649 := bstep (se 2 (by rfl) ⟨1940118, by rfl⟩ : syracuseStep 5173649 = 3880237) B3880237
theorem B3449099 : Blo 2297435 3449099 := bstep (se 1 (by rfl) ⟨2586824, by rfl⟩ : syracuseStep 3449099 = 5173649) B5173649
theorem B2299399 : Blo 2297435 2299399 := bstep (se 1 (by rfl) ⟨1724549, by rfl⟩ : syracuseStep 2299399 = 3449099) B3449099
theorem B2586829 : Blo 2297435 2586829 := bbase (se 3 (by rfl) ⟨485030, by rfl⟩ : syracuseStep 2586829 = 970061) (by norm_num)
theorem B3449105 : Blo 2297435 3449105 := bstep (se 2 (by rfl) ⟨1293414, by rfl⟩ : syracuseStep 3449105 = 2586829) B2586829
theorem B2299403 : Blo 2297435 2299403 := bstep (se 1 (by rfl) ⟨1724552, by rfl⟩ : syracuseStep 2299403 = 3449105) B3449105
theorem B7760501 : Blo 2297435 7760501 := bbase (se 5 (by rfl) ⟨363773, by rfl⟩ : syracuseStep 7760501 = 727547) (by norm_num)
theorem B5173667 : Blo 2297435 5173667 := bstep (se 1 (by rfl) ⟨3880250, by rfl⟩ : syracuseStep 5173667 = 7760501) B7760501
theorem B3449111 : Blo 2297435 3449111 := bstep (se 1 (by rfl) ⟨2586833, by rfl⟩ : syracuseStep 3449111 = 5173667) B5173667
theorem B2299407 : Blo 2297435 2299407 := bstep (se 1 (by rfl) ⟨1724555, by rfl⟩ : syracuseStep 2299407 = 3449111) B3449111
theorem B3449117 : Blo 2297435 3449117 := bbase (se 3 (by rfl) ⟨646709, by rfl⟩ : syracuseStep 3449117 = 1293419) (by norm_num)
theorem B2299411 : Blo 2297435 2299411 := bstep (se 1 (by rfl) ⟨1724558, by rfl⟩ : syracuseStep 2299411 = 3449117) B3449117
theorem B5173685 : Blo 2297435 5173685 := bbase (se 5 (by rfl) ⟨242516, by rfl⟩ : syracuseStep 5173685 = 485033) (by norm_num)
theorem B3449123 : Blo 2297435 3449123 := bstep (se 1 (by rfl) ⟨2586842, by rfl⟩ : syracuseStep 3449123 = 5173685) B5173685
theorem B2299415 : Blo 2297435 2299415 := bstep (se 1 (by rfl) ⟨1724561, by rfl⟩ : syracuseStep 2299415 = 3449123) B3449123
theorem B13984757 : Blo 2297435 13984757 := bbase (se 5 (by rfl) ⟨655535, by rfl⟩ : syracuseStep 13984757 = 1311071) (by norm_num)
theorem B9323171 : Blo 2297435 9323171 := bstep (se 1 (by rfl) ⟨6992378, by rfl⟩ : syracuseStep 9323171 = 13984757) B13984757
theorem B6215447 : Blo 2297435 6215447 := bstep (se 1 (by rfl) ⟨4661585, by rfl⟩ : syracuseStep 6215447 = 9323171) B9323171
theorem B4143631 : Blo 2297435 4143631 := bstep (se 1 (by rfl) ⟨3107723, by rfl⟩ : syracuseStep 4143631 = 6215447) B6215447
theorem B5524841 : Blo 2297435 5524841 := bstep (se 2 (by rfl) ⟨2071815, by rfl⟩ : syracuseStep 5524841 = 4143631) B4143631
theorem B3683227 : Blo 2297435 3683227 := bstep (se 1 (by rfl) ⟨2762420, by rfl⟩ : syracuseStep 3683227 = 5524841) B5524841
theorem B4910969 : Blo 2297435 4910969 := bstep (se 2 (by rfl) ⟨1841613, by rfl⟩ : syracuseStep 4910969 = 3683227) B3683227
theorem B13095917 : Blo 2297435 13095917 := bstep (se 3 (by rfl) ⟨2455484, by rfl⟩ : syracuseStep 13095917 = 4910969) B4910969
theorem B8730611 : Blo 2297435 8730611 := bstep (se 1 (by rfl) ⟨6547958, by rfl⟩ : syracuseStep 8730611 = 13095917) B13095917
theorem B5820407 : Blo 2297435 5820407 := bstep (se 1 (by rfl) ⟨4365305, by rfl⟩ : syracuseStep 5820407 = 8730611) B8730611
theorem B3880271 : Blo 2297435 3880271 := bstep (se 1 (by rfl) ⟨2910203, by rfl⟩ : syracuseStep 3880271 = 5820407) B5820407
theorem B2586847 : Blo 2297435 2586847 := bstep (se 1 (by rfl) ⟨1940135, by rfl⟩ : syracuseStep 2586847 = 3880271) B3880271
theorem B3449129 : Blo 2297435 3449129 := bstep (se 2 (by rfl) ⟨1293423, by rfl⟩ : syracuseStep 3449129 = 2586847) B2586847
theorem B2299419 : Blo 2297435 2299419 := bstep (se 1 (by rfl) ⟨1724564, by rfl⟩ : syracuseStep 2299419 = 3449129) B3449129
theorem B2762425 : Blo 2297435 2762425 := bbase (se 2 (by rfl) ⟨1035909, by rfl⟩ : syracuseStep 2762425 = 2071819) (by norm_num)
theorem B3683233 : Blo 2297435 3683233 := bstep (se 2 (by rfl) ⟨1381212, by rfl⟩ : syracuseStep 3683233 = 2762425) B2762425
theorem B4910977 : Blo 2297435 4910977 := bstep (se 2 (by rfl) ⟨1841616, by rfl⟩ : syracuseStep 4910977 = 3683233) B3683233
theorem B6547969 : Blo 2297435 6547969 := bstep (se 2 (by rfl) ⟨2455488, by rfl⟩ : syracuseStep 6547969 = 4910977) B4910977
theorem B8730625 : Blo 2297435 8730625 := bstep (se 2 (by rfl) ⟨3273984, by rfl⟩ : syracuseStep 8730625 = 6547969) B6547969
theorem B11640833 : Blo 2297435 11640833 := bstep (se 2 (by rfl) ⟨4365312, by rfl⟩ : syracuseStep 11640833 = 8730625) B8730625
theorem B7760555 : Blo 2297435 7760555 := bstep (se 1 (by rfl) ⟨5820416, by rfl⟩ : syracuseStep 7760555 = 11640833) B11640833
theorem B5173703 : Blo 2297435 5173703 := bstep (se 1 (by rfl) ⟨3880277, by rfl⟩ : syracuseStep 5173703 = 7760555) B7760555
theorem B3449135 : Blo 2297435 3449135 := bstep (se 1 (by rfl) ⟨2586851, by rfl⟩ : syracuseStep 3449135 = 5173703) B5173703
theorem B2299423 : Blo 2297435 2299423 := bstep (se 1 (by rfl) ⟨1724567, by rfl⟩ : syracuseStep 2299423 = 3449135) B3449135
theorem B3449141 : Blo 2297435 3449141 := bbase (se 5 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 3449141 = 323357) (by norm_num)
theorem B2299427 : Blo 2297435 2299427 := bstep (se 1 (by rfl) ⟨1724570, by rfl⟩ : syracuseStep 2299427 = 3449141) B3449141
theorem B5820437 : Blo 2297435 5820437 := bbase (se 6 (by rfl) ⟨136416, by rfl⟩ : syracuseStep 5820437 = 272833) (by norm_num)
theorem B3880291 : Blo 2297435 3880291 := bstep (se 1 (by rfl) ⟨2910218, by rfl⟩ : syracuseStep 3880291 = 5820437) B5820437
theorem B5173721 : Blo 2297435 5173721 := bstep (se 2 (by rfl) ⟨1940145, by rfl⟩ : syracuseStep 5173721 = 3880291) B3880291
theorem B3449147 : Blo 2297435 3449147 := bstep (se 1 (by rfl) ⟨2586860, by rfl⟩ : syracuseStep 3449147 = 5173721) B5173721
theorem B2299431 : Blo 2297435 2299431 := bstep (se 1 (by rfl) ⟨1724573, by rfl⟩ : syracuseStep 2299431 = 3449147) B3449147
theorem B2586865 : Blo 2297435 2586865 := bbase (se 2 (by rfl) ⟨970074, by rfl⟩ : syracuseStep 2586865 = 1940149) (by norm_num)
theorem B3449153 : Blo 2297435 3449153 := bstep (se 2 (by rfl) ⟨1293432, by rfl⟩ : syracuseStep 3449153 = 2586865) B2586865
theorem B2299435 : Blo 2297435 2299435 := bstep (se 1 (by rfl) ⟨1724576, by rfl⟩ : syracuseStep 2299435 = 3449153) B3449153
theorem C0 (j : ℕ) (h1 : 574358 ≤ j) (h2 : j ≤ 574858) : Blo 2297435 (4 * j + 3) := by
  interval_cases j
  · exact B2297435
  · exact B2297439
  · exact B2297443
  · exact B2297447
  · exact B2297451
  · exact B2297455
  · exact B2297459
  · exact B2297463
  · exact B2297467
  · exact B2297471
  · exact B2297475
  · exact B2297479
  · exact B2297483
  · exact B2297487
  · exact B2297491
  · exact B2297495
  · exact B2297499
  · exact B2297503
  · exact B2297507
  · exact B2297511
  · exact B2297515
  · exact B2297519
  · exact B2297523
  · exact B2297527
  · exact B2297531
  · exact B2297535
  · exact B2297539
  · exact B2297543
  · exact B2297547
  · exact B2297551
  · exact B2297555
  · exact B2297559
  · exact B2297563
  · exact B2297567
  · exact B2297571
  · exact B2297575
  · exact B2297579
  · exact B2297583
  · exact B2297587
  · exact B2297591
  · exact B2297595
  · exact B2297599
  · exact B2297603
  · exact B2297607
  · exact B2297611
  · exact B2297615
  · exact B2297619
  · exact B2297623
  · exact B2297627
  · exact B2297631
  · exact B2297635
  · exact B2297639
  · exact B2297643
  · exact B2297647
  · exact B2297651
  · exact B2297655
  · exact B2297659
  · exact B2297663
  · exact B2297667
  · exact B2297671
  · exact B2297675
  · exact B2297679
  · exact B2297683
  · exact B2297687
  · exact B2297691
  · exact B2297695
  · exact B2297699
  · exact B2297703
  · exact B2297707
  · exact B2297711
  · exact B2297715
  · exact B2297719
  · exact B2297723
  · exact B2297727
  · exact B2297731
  · exact B2297735
  · exact B2297739
  · exact B2297743
  · exact B2297747
  · exact B2297751
  · exact B2297755
  · exact B2297759
  · exact B2297763
  · exact B2297767
  · exact B2297771
  · exact B2297775
  · exact B2297779
  · exact B2297783
  · exact B2297787
  · exact B2297791
  · exact B2297795
  · exact B2297799
  · exact B2297803
  · exact B2297807
  · exact B2297811
  · exact B2297815
  · exact B2297819
  · exact B2297823
  · exact B2297827
  · exact B2297831
  · exact B2297835
  · exact B2297839
  · exact B2297843
  · exact B2297847
  · exact B2297851
  · exact B2297855
  · exact B2297859
  · exact B2297863
  · exact B2297867
  · exact B2297871
  · exact B2297875
  · exact B2297879
  · exact B2297883
  · exact B2297887
  · exact B2297891
  · exact B2297895
  · exact B2297899
  · exact B2297903
  · exact B2297907
  · exact B2297911
  · exact B2297915
  · exact B2297919
  · exact B2297923
  · exact B2297927
  · exact B2297931
  · exact B2297935
  · exact B2297939
  · exact B2297943
  · exact B2297947
  · exact B2297951
  · exact B2297955
  · exact B2297959
  · exact B2297963
  · exact B2297967
  · exact B2297971
  · exact B2297975
  · exact B2297979
  · exact B2297983
  · exact B2297987
  · exact B2297991
  · exact B2297995
  · exact B2297999
  · exact B2298003
  · exact B2298007
  · exact B2298011
  · exact B2298015
  · exact B2298019
  · exact B2298023
  · exact B2298027
  · exact B2298031
  · exact B2298035
  · exact B2298039
  · exact B2298043
  · exact B2298047
  · exact B2298051
  · exact B2298055
  · exact B2298059
  · exact B2298063
  · exact B2298067
  · exact B2298071
  · exact B2298075
  · exact B2298079
  · exact B2298083
  · exact B2298087
  · exact B2298091
  · exact B2298095
  · exact B2298099
  · exact B2298103
  · exact B2298107
  · exact B2298111
  · exact B2298115
  · exact B2298119
  · exact B2298123
  · exact B2298127
  · exact B2298131
  · exact B2298135
  · exact B2298139
  · exact B2298143
  · exact B2298147
  · exact B2298151
  · exact B2298155
  · exact B2298159
  · exact B2298163
  · exact B2298167
  · exact B2298171
  · exact B2298175
  · exact B2298179
  · exact B2298183
  · exact B2298187
  · exact B2298191
  · exact B2298195
  · exact B2298199
  · exact B2298203
  · exact B2298207
  · exact B2298211
  · exact B2298215
  · exact B2298219
  · exact B2298223
  · exact B2298227
  · exact B2298231
  · exact B2298235
  · exact B2298239
  · exact B2298243
  · exact B2298247
  · exact B2298251
  · exact B2298255
  · exact B2298259
  · exact B2298263
  · exact B2298267
  · exact B2298271
  · exact B2298275
  · exact B2298279
  · exact B2298283
  · exact B2298287
  · exact B2298291
  · exact B2298295
  · exact B2298299
  · exact B2298303
  · exact B2298307
  · exact B2298311
  · exact B2298315
  · exact B2298319
  · exact B2298323
  · exact B2298327
  · exact B2298331
  · exact B2298335
  · exact B2298339
  · exact B2298343
  · exact B2298347
  · exact B2298351
  · exact B2298355
  · exact B2298359
  · exact B2298363
  · exact B2298367
  · exact B2298371
  · exact B2298375
  · exact B2298379
  · exact B2298383
  · exact B2298387
  · exact B2298391
  · exact B2298395
  · exact B2298399
  · exact B2298403
  · exact B2298407
  · exact B2298411
  · exact B2298415
  · exact B2298419
  · exact B2298423
  · exact B2298427
  · exact B2298431
  · exact B2298435
  · exact B2298439
  · exact B2298443
  · exact B2298447
  · exact B2298451
  · exact B2298455
  · exact B2298459
  · exact B2298463
  · exact B2298467
  · exact B2298471
  · exact B2298475
  · exact B2298479
  · exact B2298483
  · exact B2298487
  · exact B2298491
  · exact B2298495
  · exact B2298499
  · exact B2298503
  · exact B2298507
  · exact B2298511
  · exact B2298515
  · exact B2298519
  · exact B2298523
  · exact B2298527
  · exact B2298531
  · exact B2298535
  · exact B2298539
  · exact B2298543
  · exact B2298547
  · exact B2298551
  · exact B2298555
  · exact B2298559
  · exact B2298563
  · exact B2298567
  · exact B2298571
  · exact B2298575
  · exact B2298579
  · exact B2298583
  · exact B2298587
  · exact B2298591
  · exact B2298595
  · exact B2298599
  · exact B2298603
  · exact B2298607
  · exact B2298611
  · exact B2298615
  · exact B2298619
  · exact B2298623
  · exact B2298627
  · exact B2298631
  · exact B2298635
  · exact B2298639
  · exact B2298643
  · exact B2298647
  · exact B2298651
  · exact B2298655
  · exact B2298659
  · exact B2298663
  · exact B2298667
  · exact B2298671
  · exact B2298675
  · exact B2298679
  · exact B2298683
  · exact B2298687
  · exact B2298691
  · exact B2298695
  · exact B2298699
  · exact B2298703
  · exact B2298707
  · exact B2298711
  · exact B2298715
  · exact B2298719
  · exact B2298723
  · exact B2298727
  · exact B2298731
  · exact B2298735
  · exact B2298739
  · exact B2298743
  · exact B2298747
  · exact B2298751
  · exact B2298755
  · exact B2298759
  · exact B2298763
  · exact B2298767
  · exact B2298771
  · exact B2298775
  · exact B2298779
  · exact B2298783
  · exact B2298787
  · exact B2298791
  · exact B2298795
  · exact B2298799
  · exact B2298803
  · exact B2298807
  · exact B2298811
  · exact B2298815
  · exact B2298819
  · exact B2298823
  · exact B2298827
  · exact B2298831
  · exact B2298835
  · exact B2298839
  · exact B2298843
  · exact B2298847
  · exact B2298851
  · exact B2298855
  · exact B2298859
  · exact B2298863
  · exact B2298867
  · exact B2298871
  · exact B2298875
  · exact B2298879
  · exact B2298883
  · exact B2298887
  · exact B2298891
  · exact B2298895
  · exact B2298899
  · exact B2298903
  · exact B2298907
  · exact B2298911
  · exact B2298915
  · exact B2298919
  · exact B2298923
  · exact B2298927
  · exact B2298931
  · exact B2298935
  · exact B2298939
  · exact B2298943
  · exact B2298947
  · exact B2298951
  · exact B2298955
  · exact B2298959
  · exact B2298963
  · exact B2298967
  · exact B2298971
  · exact B2298975
  · exact B2298979
  · exact B2298983
  · exact B2298987
  · exact B2298991
  · exact B2298995
  · exact B2298999
  · exact B2299003
  · exact B2299007
  · exact B2299011
  · exact B2299015
  · exact B2299019
  · exact B2299023
  · exact B2299027
  · exact B2299031
  · exact B2299035
  · exact B2299039
  · exact B2299043
  · exact B2299047
  · exact B2299051
  · exact B2299055
  · exact B2299059
  · exact B2299063
  · exact B2299067
  · exact B2299071
  · exact B2299075
  · exact B2299079
  · exact B2299083
  · exact B2299087
  · exact B2299091
  · exact B2299095
  · exact B2299099
  · exact B2299103
  · exact B2299107
  · exact B2299111
  · exact B2299115
  · exact B2299119
  · exact B2299123
  · exact B2299127
  · exact B2299131
  · exact B2299135
  · exact B2299139
  · exact B2299143
  · exact B2299147
  · exact B2299151
  · exact B2299155
  · exact B2299159
  · exact B2299163
  · exact B2299167
  · exact B2299171
  · exact B2299175
  · exact B2299179
  · exact B2299183
  · exact B2299187
  · exact B2299191
  · exact B2299195
  · exact B2299199
  · exact B2299203
  · exact B2299207
  · exact B2299211
  · exact B2299215
  · exact B2299219
  · exact B2299223
  · exact B2299227
  · exact B2299231
  · exact B2299235
  · exact B2299239
  · exact B2299243
  · exact B2299247
  · exact B2299251
  · exact B2299255
  · exact B2299259
  · exact B2299263
  · exact B2299267
  · exact B2299271
  · exact B2299275
  · exact B2299279
  · exact B2299283
  · exact B2299287
  · exact B2299291
  · exact B2299295
  · exact B2299299
  · exact B2299303
  · exact B2299307
  · exact B2299311
  · exact B2299315
  · exact B2299319
  · exact B2299323
  · exact B2299327
  · exact B2299331
  · exact B2299335
  · exact B2299339
  · exact B2299343
  · exact B2299347
  · exact B2299351
  · exact B2299355
  · exact B2299359
  · exact B2299363
  · exact B2299367
  · exact B2299371
  · exact B2299375
  · exact B2299379
  · exact B2299383
  · exact B2299387
  · exact B2299391
  · exact B2299395
  · exact B2299399
  · exact B2299403
  · exact B2299407
  · exact B2299411
  · exact B2299415
  · exact B2299419
  · exact B2299423
  · exact B2299427
  · exact B2299431
  · exact B2299435
theorem solution (m : ℕ) (hlo : 2297435 ≤ m) (hhi : m ≤ 2299435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 574358 ≤ j := by omega
    have hj2 : j ≤ 574858 := by omega
    have hb : Blo 2297435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
