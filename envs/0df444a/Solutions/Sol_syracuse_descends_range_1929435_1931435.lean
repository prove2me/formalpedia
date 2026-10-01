-- Prove2me | solution 1 for syracuse_descends_range_1929435_1931435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:20.166759+00:00
-- url     : https://prove2.me/submissions/cf7cfebb-1964-4dd4-8126-beda0882b8c3

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

theorem B4883885 : Blo 1929435 4883885 := bbase (se 3 (by rfl) ⟨915728, by rfl⟩ : syracuseStep 4883885 = 1831457) (by norm_num)
theorem B3255923 : Blo 1929435 3255923 := bstep (se 1 (by rfl) ⟨2441942, by rfl⟩ : syracuseStep 3255923 = 4883885) B4883885
theorem B2170615 : Blo 1929435 2170615 := bstep (se 1 (by rfl) ⟨1627961, by rfl⟩ : syracuseStep 2170615 = 3255923) B3255923
theorem B2894153 : Blo 1929435 2894153 := bstep (se 2 (by rfl) ⟨1085307, by rfl⟩ : syracuseStep 2894153 = 2170615) B2170615
theorem B1929435 : Blo 1929435 1929435 := bstep (se 1 (by rfl) ⟨1447076, by rfl⟩ : syracuseStep 1929435 = 2894153) B2894153
theorem B1955765 : Blo 1929435 1955765 := bbase (se 5 (by rfl) ⟨91676, by rfl⟩ : syracuseStep 1955765 = 183353) (by norm_num)
theorem B5215373 : Blo 1929435 5215373 := bstep (se 3 (by rfl) ⟨977882, by rfl⟩ : syracuseStep 5215373 = 1955765) B1955765
theorem B3476915 : Blo 1929435 3476915 := bstep (se 1 (by rfl) ⟨2607686, by rfl⟩ : syracuseStep 3476915 = 5215373) B5215373
theorem B2317943 : Blo 1929435 2317943 := bstep (se 1 (by rfl) ⟨1738457, by rfl⟩ : syracuseStep 2317943 = 3476915) B3476915
theorem B6181181 : Blo 1929435 6181181 := bstep (se 3 (by rfl) ⟨1158971, by rfl⟩ : syracuseStep 6181181 = 2317943) B2317943
theorem B4120787 : Blo 1929435 4120787 := bstep (se 1 (by rfl) ⟨3090590, by rfl⟩ : syracuseStep 4120787 = 6181181) B6181181
theorem B2747191 : Blo 1929435 2747191 := bstep (se 1 (by rfl) ⟨2060393, by rfl⟩ : syracuseStep 2747191 = 4120787) B4120787
theorem B3662921 : Blo 1929435 3662921 := bstep (se 2 (by rfl) ⟨1373595, by rfl⟩ : syracuseStep 3662921 = 2747191) B2747191
theorem B9767789 : Blo 1929435 9767789 := bstep (se 3 (by rfl) ⟨1831460, by rfl⟩ : syracuseStep 9767789 = 3662921) B3662921
theorem B6511859 : Blo 1929435 6511859 := bstep (se 1 (by rfl) ⟨4883894, by rfl⟩ : syracuseStep 6511859 = 9767789) B9767789
theorem B4341239 : Blo 1929435 4341239 := bstep (se 1 (by rfl) ⟨3255929, by rfl⟩ : syracuseStep 4341239 = 6511859) B6511859
theorem B2894159 : Blo 1929435 2894159 := bstep (se 1 (by rfl) ⟨2170619, by rfl⟩ : syracuseStep 2894159 = 4341239) B4341239
theorem B1929439 : Blo 1929435 1929439 := bstep (se 1 (by rfl) ⟨1447079, by rfl⟩ : syracuseStep 1929439 = 2894159) B2894159
theorem B2894165 : Blo 1929435 2894165 := bbase (se 10 (by rfl) ⟨4239, by rfl⟩ : syracuseStep 2894165 = 8479) (by norm_num)
theorem B1929443 : Blo 1929435 1929443 := bstep (se 1 (by rfl) ⟨1447082, by rfl⟩ : syracuseStep 1929443 = 2894165) B2894165
theorem B5494405 : Blo 1929435 5494405 := bbase (se 4 (by rfl) ⟨515100, by rfl⟩ : syracuseStep 5494405 = 1030201) (by norm_num)
theorem B7325873 : Blo 1929435 7325873 := bstep (se 2 (by rfl) ⟨2747202, by rfl⟩ : syracuseStep 7325873 = 5494405) B5494405
theorem B4883915 : Blo 1929435 4883915 := bstep (se 1 (by rfl) ⟨3662936, by rfl⟩ : syracuseStep 4883915 = 7325873) B7325873
theorem B3255943 : Blo 1929435 3255943 := bstep (se 1 (by rfl) ⟨2441957, by rfl⟩ : syracuseStep 3255943 = 4883915) B4883915
theorem B4341257 : Blo 1929435 4341257 := bstep (se 2 (by rfl) ⟨1627971, by rfl⟩ : syracuseStep 4341257 = 3255943) B3255943
theorem B2894171 : Blo 1929435 2894171 := bstep (se 1 (by rfl) ⟨2170628, by rfl⟩ : syracuseStep 2894171 = 4341257) B4341257
theorem B1929447 : Blo 1929435 1929447 := bstep (se 1 (by rfl) ⟨1447085, by rfl⟩ : syracuseStep 1929447 = 2894171) B2894171
theorem B2170633 : Blo 1929435 2170633 := bbase (se 2 (by rfl) ⟨813987, by rfl⟩ : syracuseStep 2170633 = 1627975) (by norm_num)
theorem B2894177 : Blo 1929435 2894177 := bstep (se 2 (by rfl) ⟨1085316, by rfl⟩ : syracuseStep 2894177 = 2170633) B2170633
theorem B1929451 : Blo 1929435 1929451 := bstep (se 1 (by rfl) ⟨1447088, by rfl⟩ : syracuseStep 1929451 = 2894177) B2894177
theorem B2200253 : Blo 1929435 2200253 := bbase (se 3 (by rfl) ⟨412547, by rfl⟩ : syracuseStep 2200253 = 825095) (by norm_num)
theorem B23469365 : Blo 1929435 23469365 := bstep (se 5 (by rfl) ⟨1100126, by rfl⟩ : syracuseStep 23469365 = 2200253) B2200253
theorem B15646243 : Blo 1929435 15646243 := bstep (se 1 (by rfl) ⟨11734682, by rfl⟩ : syracuseStep 15646243 = 23469365) B23469365
theorem B20861657 : Blo 1929435 20861657 := bstep (se 2 (by rfl) ⟨7823121, by rfl⟩ : syracuseStep 20861657 = 15646243) B15646243
theorem B13907771 : Blo 1929435 13907771 := bstep (se 1 (by rfl) ⟨10430828, by rfl⟩ : syracuseStep 13907771 = 20861657) B20861657
theorem B9271847 : Blo 1929435 9271847 := bstep (se 1 (by rfl) ⟨6953885, by rfl⟩ : syracuseStep 9271847 = 13907771) B13907771
theorem B24724925 : Blo 1929435 24724925 := bstep (se 3 (by rfl) ⟨4635923, by rfl⟩ : syracuseStep 24724925 = 9271847) B9271847
theorem B16483283 : Blo 1929435 16483283 := bstep (se 1 (by rfl) ⟨12362462, by rfl⟩ : syracuseStep 16483283 = 24724925) B24724925
theorem B10988855 : Blo 1929435 10988855 := bstep (se 1 (by rfl) ⟨8241641, by rfl⟩ : syracuseStep 10988855 = 16483283) B16483283
theorem B7325903 : Blo 1929435 7325903 := bstep (se 1 (by rfl) ⟨5494427, by rfl⟩ : syracuseStep 7325903 = 10988855) B10988855
theorem B4883935 : Blo 1929435 4883935 := bstep (se 1 (by rfl) ⟨3662951, by rfl⟩ : syracuseStep 4883935 = 7325903) B7325903
theorem B6511913 : Blo 1929435 6511913 := bstep (se 2 (by rfl) ⟨2441967, by rfl⟩ : syracuseStep 6511913 = 4883935) B4883935
theorem B4341275 : Blo 1929435 4341275 := bstep (se 1 (by rfl) ⟨3255956, by rfl⟩ : syracuseStep 4341275 = 6511913) B6511913
theorem B2894183 : Blo 1929435 2894183 := bstep (se 1 (by rfl) ⟨2170637, by rfl⟩ : syracuseStep 2894183 = 4341275) B4341275
theorem B1929455 : Blo 1929435 1929455 := bstep (se 1 (by rfl) ⟨1447091, by rfl⟩ : syracuseStep 1929455 = 2894183) B2894183
theorem B2894189 : Blo 1929435 2894189 := bbase (se 3 (by rfl) ⟨542660, by rfl⟩ : syracuseStep 2894189 = 1085321) (by norm_num)
theorem B1929459 : Blo 1929435 1929459 := bstep (se 1 (by rfl) ⟨1447094, by rfl⟩ : syracuseStep 1929459 = 2894189) B2894189
theorem B4341293 : Blo 1929435 4341293 := bbase (se 3 (by rfl) ⟨813992, by rfl⟩ : syracuseStep 4341293 = 1627985) (by norm_num)
theorem B2894195 : Blo 1929435 2894195 := bstep (se 1 (by rfl) ⟨2170646, by rfl⟩ : syracuseStep 2894195 = 4341293) B4341293
theorem B1929463 : Blo 1929435 1929463 := bstep (se 1 (by rfl) ⟨1447097, by rfl⟩ : syracuseStep 1929463 = 2894195) B2894195
theorem B2475301 : Blo 1929435 2475301 := bbase (se 4 (by rfl) ⟨232059, by rfl⟩ : syracuseStep 2475301 = 464119) (by norm_num)
theorem B3300401 : Blo 1929435 3300401 := bstep (se 2 (by rfl) ⟨1237650, by rfl⟩ : syracuseStep 3300401 = 2475301) B2475301
theorem B8801069 : Blo 1929435 8801069 := bstep (se 3 (by rfl) ⟨1650200, by rfl⟩ : syracuseStep 8801069 = 3300401) B3300401
theorem B23469517 : Blo 1929435 23469517 := bstep (se 3 (by rfl) ⟨4400534, by rfl⟩ : syracuseStep 23469517 = 8801069) B8801069
theorem B31292689 : Blo 1929435 31292689 := bstep (se 2 (by rfl) ⟨11734758, by rfl⟩ : syracuseStep 31292689 = 23469517) B23469517
theorem B41723585 : Blo 1929435 41723585 := bstep (se 2 (by rfl) ⟨15646344, by rfl⟩ : syracuseStep 41723585 = 31292689) B31292689
theorem B27815723 : Blo 1929435 27815723 := bstep (se 1 (by rfl) ⟨20861792, by rfl⟩ : syracuseStep 27815723 = 41723585) B41723585
theorem B18543815 : Blo 1929435 18543815 := bstep (se 1 (by rfl) ⟨13907861, by rfl⟩ : syracuseStep 18543815 = 27815723) B27815723
theorem B12362543 : Blo 1929435 12362543 := bstep (se 1 (by rfl) ⟨9271907, by rfl⟩ : syracuseStep 12362543 = 18543815) B18543815
theorem B8241695 : Blo 1929435 8241695 := bstep (se 1 (by rfl) ⟨6181271, by rfl⟩ : syracuseStep 8241695 = 12362543) B12362543
theorem B5494463 : Blo 1929435 5494463 := bstep (se 1 (by rfl) ⟨4120847, by rfl⟩ : syracuseStep 5494463 = 8241695) B8241695
theorem B3662975 : Blo 1929435 3662975 := bstep (se 1 (by rfl) ⟨2747231, by rfl⟩ : syracuseStep 3662975 = 5494463) B5494463
theorem B2441983 : Blo 1929435 2441983 := bstep (se 1 (by rfl) ⟨1831487, by rfl⟩ : syracuseStep 2441983 = 3662975) B3662975
theorem B3255977 : Blo 1929435 3255977 := bstep (se 2 (by rfl) ⟨1220991, by rfl⟩ : syracuseStep 3255977 = 2441983) B2441983
theorem B2170651 : Blo 1929435 2170651 := bstep (se 1 (by rfl) ⟨1627988, by rfl⟩ : syracuseStep 2170651 = 3255977) B3255977
theorem B2894201 : Blo 1929435 2894201 := bstep (se 2 (by rfl) ⟨1085325, by rfl⟩ : syracuseStep 2894201 = 2170651) B2170651
theorem B1929467 : Blo 1929435 1929467 := bstep (se 1 (by rfl) ⟨1447100, by rfl⟩ : syracuseStep 1929467 = 2894201) B2894201
theorem B2317981 : Blo 1929435 2317981 := bbase (se 3 (by rfl) ⟨434621, by rfl⟩ : syracuseStep 2317981 = 869243) (by norm_num)
theorem B3090641 : Blo 1929435 3090641 := bstep (se 2 (by rfl) ⟨1158990, by rfl⟩ : syracuseStep 3090641 = 2317981) B2317981
theorem B32966837 : Blo 1929435 32966837 := bstep (se 5 (by rfl) ⟨1545320, by rfl⟩ : syracuseStep 32966837 = 3090641) B3090641
theorem B21977891 : Blo 1929435 21977891 := bstep (se 1 (by rfl) ⟨16483418, by rfl⟩ : syracuseStep 21977891 = 32966837) B32966837
theorem B14651927 : Blo 1929435 14651927 := bstep (se 1 (by rfl) ⟨10988945, by rfl⟩ : syracuseStep 14651927 = 21977891) B21977891
theorem B9767951 : Blo 1929435 9767951 := bstep (se 1 (by rfl) ⟨7325963, by rfl⟩ : syracuseStep 9767951 = 14651927) B14651927
theorem B6511967 : Blo 1929435 6511967 := bstep (se 1 (by rfl) ⟨4883975, by rfl⟩ : syracuseStep 6511967 = 9767951) B9767951
theorem B4341311 : Blo 1929435 4341311 := bstep (se 1 (by rfl) ⟨3255983, by rfl⟩ : syracuseStep 4341311 = 6511967) B6511967
theorem B2894207 : Blo 1929435 2894207 := bstep (se 1 (by rfl) ⟨2170655, by rfl⟩ : syracuseStep 2894207 = 4341311) B4341311
theorem B1929471 : Blo 1929435 1929471 := bstep (se 1 (by rfl) ⟨1447103, by rfl⟩ : syracuseStep 1929471 = 2894207) B2894207
theorem B2894213 : Blo 1929435 2894213 := bbase (se 4 (by rfl) ⟨271332, by rfl⟩ : syracuseStep 2894213 = 542665) (by norm_num)
theorem B1929475 : Blo 1929435 1929475 := bstep (se 1 (by rfl) ⟨1447106, by rfl⟩ : syracuseStep 1929475 = 2894213) B2894213
theorem B3255997 : Blo 1929435 3255997 := bbase (se 3 (by rfl) ⟨610499, by rfl⟩ : syracuseStep 3255997 = 1220999) (by norm_num)
theorem B4341329 : Blo 1929435 4341329 := bstep (se 2 (by rfl) ⟨1627998, by rfl⟩ : syracuseStep 4341329 = 3255997) B3255997
theorem B2894219 : Blo 1929435 2894219 := bstep (se 1 (by rfl) ⟨2170664, by rfl⟩ : syracuseStep 2894219 = 4341329) B4341329
theorem B1929479 : Blo 1929435 1929479 := bstep (se 1 (by rfl) ⟨1447109, by rfl⟩ : syracuseStep 1929479 = 2894219) B2894219
theorem B2170669 : Blo 1929435 2170669 := bbase (se 3 (by rfl) ⟨407000, by rfl⟩ : syracuseStep 2170669 = 814001) (by norm_num)
theorem B2894225 : Blo 1929435 2894225 := bstep (se 2 (by rfl) ⟨1085334, by rfl⟩ : syracuseStep 2894225 = 2170669) B2170669
theorem B1929483 : Blo 1929435 1929483 := bstep (se 1 (by rfl) ⟨1447112, by rfl⟩ : syracuseStep 1929483 = 2894225) B2894225
theorem B6512021 : Blo 1929435 6512021 := bbase (se 6 (by rfl) ⟨152625, by rfl⟩ : syracuseStep 6512021 = 305251) (by norm_num)
theorem B4341347 : Blo 1929435 4341347 := bstep (se 1 (by rfl) ⟨3256010, by rfl⟩ : syracuseStep 4341347 = 6512021) B6512021
theorem B2894231 : Blo 1929435 2894231 := bstep (se 1 (by rfl) ⟨2170673, by rfl⟩ : syracuseStep 2894231 = 4341347) B4341347
theorem B1929487 : Blo 1929435 1929487 := bstep (se 1 (by rfl) ⟨1447115, by rfl⟩ : syracuseStep 1929487 = 2894231) B2894231
theorem B2894237 : Blo 1929435 2894237 := bbase (se 3 (by rfl) ⟨542669, by rfl⟩ : syracuseStep 2894237 = 1085339) (by norm_num)
theorem B1929491 : Blo 1929435 1929491 := bstep (se 1 (by rfl) ⟨1447118, by rfl⟩ : syracuseStep 1929491 = 2894237) B2894237
theorem B4341365 : Blo 1929435 4341365 := bbase (se 5 (by rfl) ⟨203501, by rfl⟩ : syracuseStep 4341365 = 407003) (by norm_num)
theorem B2894243 : Blo 1929435 2894243 := bstep (se 1 (by rfl) ⟨2170682, by rfl⟩ : syracuseStep 2894243 = 4341365) B4341365
theorem B1929495 : Blo 1929435 1929495 := bstep (se 1 (by rfl) ⟨1447121, by rfl⟩ : syracuseStep 1929495 = 2894243) B2894243
theorem B4234133 : Blo 1929435 4234133 := bbase (se 6 (by rfl) ⟨99237, by rfl⟩ : syracuseStep 4234133 = 198475) (by norm_num)
theorem B2822755 : Blo 1929435 2822755 := bstep (se 1 (by rfl) ⟨2117066, by rfl⟩ : syracuseStep 2822755 = 4234133) B4234133
theorem B3763673 : Blo 1929435 3763673 := bstep (se 2 (by rfl) ⟨1411377, by rfl⟩ : syracuseStep 3763673 = 2822755) B2822755
theorem B2509115 : Blo 1929435 2509115 := bstep (se 1 (by rfl) ⟨1881836, by rfl⟩ : syracuseStep 2509115 = 3763673) B3763673
theorem B6690973 : Blo 1929435 6690973 := bstep (se 3 (by rfl) ⟨1254557, by rfl⟩ : syracuseStep 6690973 = 2509115) B2509115
theorem B8921297 : Blo 1929435 8921297 := bstep (se 2 (by rfl) ⟨3345486, by rfl⟩ : syracuseStep 8921297 = 6690973) B6690973
theorem B23790125 : Blo 1929435 23790125 := bstep (se 3 (by rfl) ⟨4460648, by rfl⟩ : syracuseStep 23790125 = 8921297) B8921297
theorem B15860083 : Blo 1929435 15860083 := bstep (se 1 (by rfl) ⟨11895062, by rfl⟩ : syracuseStep 15860083 = 23790125) B23790125
theorem B21146777 : Blo 1929435 21146777 := bstep (se 2 (by rfl) ⟨7930041, by rfl⟩ : syracuseStep 21146777 = 15860083) B15860083
theorem B14097851 : Blo 1929435 14097851 := bstep (se 1 (by rfl) ⟨10573388, by rfl⟩ : syracuseStep 14097851 = 21146777) B21146777
theorem B9398567 : Blo 1929435 9398567 := bstep (se 1 (by rfl) ⟨7048925, by rfl⟩ : syracuseStep 9398567 = 14097851) B14097851
theorem B6265711 : Blo 1929435 6265711 := bstep (se 1 (by rfl) ⟨4699283, by rfl⟩ : syracuseStep 6265711 = 9398567) B9398567
theorem B8354281 : Blo 1929435 8354281 := bstep (se 2 (by rfl) ⟨3132855, by rfl⟩ : syracuseStep 8354281 = 6265711) B6265711
theorem B11139041 : Blo 1929435 11139041 := bstep (se 2 (by rfl) ⟨4177140, by rfl⟩ : syracuseStep 11139041 = 8354281) B8354281
theorem B7426027 : Blo 1929435 7426027 := bstep (se 1 (by rfl) ⟨5569520, by rfl⟩ : syracuseStep 7426027 = 11139041) B11139041
theorem B9901369 : Blo 1929435 9901369 := bstep (se 2 (by rfl) ⟨3713013, by rfl⟩ : syracuseStep 9901369 = 7426027) B7426027
theorem B13201825 : Blo 1929435 13201825 := bstep (se 2 (by rfl) ⟨4950684, by rfl⟩ : syracuseStep 13201825 = 9901369) B9901369
theorem B17602433 : Blo 1929435 17602433 := bstep (se 2 (by rfl) ⟨6600912, by rfl⟩ : syracuseStep 17602433 = 13201825) B13201825
theorem B11734955 : Blo 1929435 11734955 := bstep (se 1 (by rfl) ⟨8801216, by rfl⟩ : syracuseStep 11734955 = 17602433) B17602433
theorem B7823303 : Blo 1929435 7823303 := bstep (se 1 (by rfl) ⟨5867477, by rfl⟩ : syracuseStep 7823303 = 11734955) B11734955
theorem B5215535 : Blo 1929435 5215535 := bstep (se 1 (by rfl) ⟨3911651, by rfl⟩ : syracuseStep 5215535 = 7823303) B7823303
theorem B3477023 : Blo 1929435 3477023 := bstep (se 1 (by rfl) ⟨2607767, by rfl⟩ : syracuseStep 3477023 = 5215535) B5215535
theorem B2318015 : Blo 1929435 2318015 := bstep (se 1 (by rfl) ⟨1738511, by rfl⟩ : syracuseStep 2318015 = 3477023) B3477023
theorem B6181373 : Blo 1929435 6181373 := bstep (se 3 (by rfl) ⟨1159007, by rfl⟩ : syracuseStep 6181373 = 2318015) B2318015
theorem B16483661 : Blo 1929435 16483661 := bstep (se 3 (by rfl) ⟨3090686, by rfl⟩ : syracuseStep 16483661 = 6181373) B6181373
theorem B10989107 : Blo 1929435 10989107 := bstep (se 1 (by rfl) ⟨8241830, by rfl⟩ : syracuseStep 10989107 = 16483661) B16483661
theorem B7326071 : Blo 1929435 7326071 := bstep (se 1 (by rfl) ⟨5494553, by rfl⟩ : syracuseStep 7326071 = 10989107) B10989107
theorem B4884047 : Blo 1929435 4884047 := bstep (se 1 (by rfl) ⟨3663035, by rfl⟩ : syracuseStep 4884047 = 7326071) B7326071
theorem B3256031 : Blo 1929435 3256031 := bstep (se 1 (by rfl) ⟨2442023, by rfl⟩ : syracuseStep 3256031 = 4884047) B4884047
theorem B2170687 : Blo 1929435 2170687 := bstep (se 1 (by rfl) ⟨1628015, by rfl⟩ : syracuseStep 2170687 = 3256031) B3256031
theorem B2894249 : Blo 1929435 2894249 := bstep (se 2 (by rfl) ⟨1085343, by rfl⟩ : syracuseStep 2894249 = 2170687) B2170687
theorem B1929499 : Blo 1929435 1929499 := bstep (se 1 (by rfl) ⟨1447124, by rfl⟩ : syracuseStep 1929499 = 2894249) B2894249
theorem B7326085 : Blo 1929435 7326085 := bbase (se 4 (by rfl) ⟨686820, by rfl⟩ : syracuseStep 7326085 = 1373641) (by norm_num)
theorem B9768113 : Blo 1929435 9768113 := bstep (se 2 (by rfl) ⟨3663042, by rfl⟩ : syracuseStep 9768113 = 7326085) B7326085
theorem B6512075 : Blo 1929435 6512075 := bstep (se 1 (by rfl) ⟨4884056, by rfl⟩ : syracuseStep 6512075 = 9768113) B9768113
theorem B4341383 : Blo 1929435 4341383 := bstep (se 1 (by rfl) ⟨3256037, by rfl⟩ : syracuseStep 4341383 = 6512075) B6512075
theorem B2894255 : Blo 1929435 2894255 := bstep (se 1 (by rfl) ⟨2170691, by rfl⟩ : syracuseStep 2894255 = 4341383) B4341383
theorem B1929503 : Blo 1929435 1929503 := bstep (se 1 (by rfl) ⟨1447127, by rfl⟩ : syracuseStep 1929503 = 2894255) B2894255
theorem B2894261 : Blo 1929435 2894261 := bbase (se 5 (by rfl) ⟨135668, by rfl⟩ : syracuseStep 2894261 = 271337) (by norm_num)
theorem B1929507 : Blo 1929435 1929507 := bstep (se 1 (by rfl) ⟨1447130, by rfl⟩ : syracuseStep 1929507 = 2894261) B2894261
theorem B4884077 : Blo 1929435 4884077 := bbase (se 3 (by rfl) ⟨915764, by rfl⟩ : syracuseStep 4884077 = 1831529) (by norm_num)
theorem B3256051 : Blo 1929435 3256051 := bstep (se 1 (by rfl) ⟨2442038, by rfl⟩ : syracuseStep 3256051 = 4884077) B4884077
theorem B4341401 : Blo 1929435 4341401 := bstep (se 2 (by rfl) ⟨1628025, by rfl⟩ : syracuseStep 4341401 = 3256051) B3256051
theorem B2894267 : Blo 1929435 2894267 := bstep (se 1 (by rfl) ⟨2170700, by rfl⟩ : syracuseStep 2894267 = 4341401) B4341401
theorem B1929511 : Blo 1929435 1929511 := bstep (se 1 (by rfl) ⟨1447133, by rfl⟩ : syracuseStep 1929511 = 2894267) B2894267
theorem B2170705 : Blo 1929435 2170705 := bbase (se 2 (by rfl) ⟨814014, by rfl⟩ : syracuseStep 2170705 = 1628029) (by norm_num)
theorem B2894273 : Blo 1929435 2894273 := bstep (se 2 (by rfl) ⟨1085352, by rfl⟩ : syracuseStep 2894273 = 2170705) B2170705
theorem B1929515 : Blo 1929435 1929515 := bstep (se 1 (by rfl) ⟨1447136, by rfl⟩ : syracuseStep 1929515 = 2894273) B2894273
theorem B3713053 : Blo 1929435 3713053 := bbase (se 3 (by rfl) ⟨696197, by rfl⟩ : syracuseStep 3713053 = 1392395) (by norm_num)
theorem B4950737 : Blo 1929435 4950737 := bstep (se 2 (by rfl) ⟨1856526, by rfl⟩ : syracuseStep 4950737 = 3713053) B3713053
theorem B3300491 : Blo 1929435 3300491 := bstep (se 1 (by rfl) ⟨2475368, by rfl⟩ : syracuseStep 3300491 = 4950737) B4950737
theorem B2200327 : Blo 1929435 2200327 := bstep (se 1 (by rfl) ⟨1650245, by rfl⟩ : syracuseStep 2200327 = 3300491) B3300491
theorem B11735077 : Blo 1929435 11735077 := bstep (se 4 (by rfl) ⟨1100163, by rfl⟩ : syracuseStep 11735077 = 2200327) B2200327
theorem B15646769 : Blo 1929435 15646769 := bstep (se 2 (by rfl) ⟨5867538, by rfl⟩ : syracuseStep 15646769 = 11735077) B11735077
theorem B10431179 : Blo 1929435 10431179 := bstep (se 1 (by rfl) ⟨7823384, by rfl⟩ : syracuseStep 10431179 = 15646769) B15646769
theorem B6954119 : Blo 1929435 6954119 := bstep (se 1 (by rfl) ⟨5215589, by rfl⟩ : syracuseStep 6954119 = 10431179) B10431179
theorem B4636079 : Blo 1929435 4636079 := bstep (se 1 (by rfl) ⟨3477059, by rfl⟩ : syracuseStep 4636079 = 6954119) B6954119
theorem B3090719 : Blo 1929435 3090719 := bstep (se 1 (by rfl) ⟨2318039, by rfl⟩ : syracuseStep 3090719 = 4636079) B4636079
theorem B2060479 : Blo 1929435 2060479 := bstep (se 1 (by rfl) ⟨1545359, by rfl⟩ : syracuseStep 2060479 = 3090719) B3090719
theorem B2747305 : Blo 1929435 2747305 := bstep (se 2 (by rfl) ⟨1030239, by rfl⟩ : syracuseStep 2747305 = 2060479) B2060479
theorem B3663073 : Blo 1929435 3663073 := bstep (se 2 (by rfl) ⟨1373652, by rfl⟩ : syracuseStep 3663073 = 2747305) B2747305
theorem B4884097 : Blo 1929435 4884097 := bstep (se 2 (by rfl) ⟨1831536, by rfl⟩ : syracuseStep 4884097 = 3663073) B3663073
theorem B6512129 : Blo 1929435 6512129 := bstep (se 2 (by rfl) ⟨2442048, by rfl⟩ : syracuseStep 6512129 = 4884097) B4884097
theorem B4341419 : Blo 1929435 4341419 := bstep (se 1 (by rfl) ⟨3256064, by rfl⟩ : syracuseStep 4341419 = 6512129) B6512129
theorem B2894279 : Blo 1929435 2894279 := bstep (se 1 (by rfl) ⟨2170709, by rfl⟩ : syracuseStep 2894279 = 4341419) B4341419
theorem B1929519 : Blo 1929435 1929519 := bstep (se 1 (by rfl) ⟨1447139, by rfl⟩ : syracuseStep 1929519 = 2894279) B2894279
theorem B2894285 : Blo 1929435 2894285 := bbase (se 3 (by rfl) ⟨542678, by rfl⟩ : syracuseStep 2894285 = 1085357) (by norm_num)
theorem B1929523 : Blo 1929435 1929523 := bstep (se 1 (by rfl) ⟨1447142, by rfl⟩ : syracuseStep 1929523 = 2894285) B2894285
theorem B4341437 : Blo 1929435 4341437 := bbase (se 3 (by rfl) ⟨814019, by rfl⟩ : syracuseStep 4341437 = 1628039) (by norm_num)
theorem B2894291 : Blo 1929435 2894291 := bstep (se 1 (by rfl) ⟨2170718, by rfl⟩ : syracuseStep 2894291 = 4341437) B4341437
theorem B1929527 : Blo 1929435 1929527 := bstep (se 1 (by rfl) ⟨1447145, by rfl⟩ : syracuseStep 1929527 = 2894291) B2894291
theorem B3256085 : Blo 1929435 3256085 := bbase (se 6 (by rfl) ⟨76314, by rfl⟩ : syracuseStep 3256085 = 152629) (by norm_num)
theorem B2170723 : Blo 1929435 2170723 := bstep (se 1 (by rfl) ⟨1628042, by rfl⟩ : syracuseStep 2170723 = 3256085) B3256085
theorem B2894297 : Blo 1929435 2894297 := bstep (se 2 (by rfl) ⟨1085361, by rfl⟩ : syracuseStep 2894297 = 2170723) B2170723
theorem B1929531 : Blo 1929435 1929531 := bstep (se 1 (by rfl) ⟨1447148, by rfl⟩ : syracuseStep 1929531 = 2894297) B2894297
theorem B2349685 : Blo 1929435 2349685 := bbase (se 5 (by rfl) ⟨110141, by rfl⟩ : syracuseStep 2349685 = 220283) (by norm_num)
theorem B3132913 : Blo 1929435 3132913 := bstep (se 2 (by rfl) ⟨1174842, by rfl⟩ : syracuseStep 3132913 = 2349685) B2349685
theorem B4177217 : Blo 1929435 4177217 := bstep (se 2 (by rfl) ⟨1566456, by rfl⟩ : syracuseStep 4177217 = 3132913) B3132913
theorem B2784811 : Blo 1929435 2784811 := bstep (se 1 (by rfl) ⟨2088608, by rfl⟩ : syracuseStep 2784811 = 4177217) B4177217
theorem B3713081 : Blo 1929435 3713081 := bstep (se 2 (by rfl) ⟨1392405, by rfl⟩ : syracuseStep 3713081 = 2784811) B2784811
theorem B9901549 : Blo 1929435 9901549 := bstep (se 3 (by rfl) ⟨1856540, by rfl⟩ : syracuseStep 9901549 = 3713081) B3713081
theorem B13202065 : Blo 1929435 13202065 := bstep (se 2 (by rfl) ⟨4950774, by rfl⟩ : syracuseStep 13202065 = 9901549) B9901549
theorem B17602753 : Blo 1929435 17602753 := bstep (se 2 (by rfl) ⟨6601032, by rfl⟩ : syracuseStep 17602753 = 13202065) B13202065
theorem B23470337 : Blo 1929435 23470337 := bstep (se 2 (by rfl) ⟨8801376, by rfl⟩ : syracuseStep 23470337 = 17602753) B17602753
theorem B62587565 : Blo 1929435 62587565 := bstep (se 3 (by rfl) ⟨11735168, by rfl⟩ : syracuseStep 62587565 = 23470337) B23470337
theorem B41725043 : Blo 1929435 41725043 := bstep (se 1 (by rfl) ⟨31293782, by rfl⟩ : syracuseStep 41725043 = 62587565) B62587565
theorem B27816695 : Blo 1929435 27816695 := bstep (se 1 (by rfl) ⟨20862521, by rfl⟩ : syracuseStep 27816695 = 41725043) B41725043
theorem B18544463 : Blo 1929435 18544463 := bstep (se 1 (by rfl) ⟨13908347, by rfl⟩ : syracuseStep 18544463 = 27816695) B27816695
theorem B12362975 : Blo 1929435 12362975 := bstep (se 1 (by rfl) ⟨9272231, by rfl⟩ : syracuseStep 12362975 = 18544463) B18544463
theorem B8241983 : Blo 1929435 8241983 := bstep (se 1 (by rfl) ⟨6181487, by rfl⟩ : syracuseStep 8241983 = 12362975) B12362975
theorem B5494655 : Blo 1929435 5494655 := bstep (se 1 (by rfl) ⟨4120991, by rfl⟩ : syracuseStep 5494655 = 8241983) B8241983
theorem B14652413 : Blo 1929435 14652413 := bstep (se 3 (by rfl) ⟨2747327, by rfl⟩ : syracuseStep 14652413 = 5494655) B5494655
theorem B9768275 : Blo 1929435 9768275 := bstep (se 1 (by rfl) ⟨7326206, by rfl⟩ : syracuseStep 9768275 = 14652413) B14652413
theorem B6512183 : Blo 1929435 6512183 := bstep (se 1 (by rfl) ⟨4884137, by rfl⟩ : syracuseStep 6512183 = 9768275) B9768275
theorem B4341455 : Blo 1929435 4341455 := bstep (se 1 (by rfl) ⟨3256091, by rfl⟩ : syracuseStep 4341455 = 6512183) B6512183
theorem B2894303 : Blo 1929435 2894303 := bstep (se 1 (by rfl) ⟨2170727, by rfl⟩ : syracuseStep 2894303 = 4341455) B4341455
theorem B1929535 : Blo 1929435 1929535 := bstep (se 1 (by rfl) ⟨1447151, by rfl⟩ : syracuseStep 1929535 = 2894303) B2894303
theorem B2894309 : Blo 1929435 2894309 := bbase (se 4 (by rfl) ⟨271341, by rfl⟩ : syracuseStep 2894309 = 542683) (by norm_num)
theorem B1929539 : Blo 1929435 1929539 := bstep (se 1 (by rfl) ⟨1447154, by rfl⟩ : syracuseStep 1929539 = 2894309) B2894309
theorem B12363029 : Blo 1929435 12363029 := bbase (se 6 (by rfl) ⟨289758, by rfl⟩ : syracuseStep 12363029 = 579517) (by norm_num)
theorem B8242019 : Blo 1929435 8242019 := bstep (se 1 (by rfl) ⟨6181514, by rfl⟩ : syracuseStep 8242019 = 12363029) B12363029
theorem B5494679 : Blo 1929435 5494679 := bstep (se 1 (by rfl) ⟨4121009, by rfl⟩ : syracuseStep 5494679 = 8242019) B8242019
theorem B3663119 : Blo 1929435 3663119 := bstep (se 1 (by rfl) ⟨2747339, by rfl⟩ : syracuseStep 3663119 = 5494679) B5494679
theorem B2442079 : Blo 1929435 2442079 := bstep (se 1 (by rfl) ⟨1831559, by rfl⟩ : syracuseStep 2442079 = 3663119) B3663119
theorem B3256105 : Blo 1929435 3256105 := bstep (se 2 (by rfl) ⟨1221039, by rfl⟩ : syracuseStep 3256105 = 2442079) B2442079
theorem B4341473 : Blo 1929435 4341473 := bstep (se 2 (by rfl) ⟨1628052, by rfl⟩ : syracuseStep 4341473 = 3256105) B3256105
theorem B2894315 : Blo 1929435 2894315 := bstep (se 1 (by rfl) ⟨2170736, by rfl⟩ : syracuseStep 2894315 = 4341473) B4341473
theorem B1929543 : Blo 1929435 1929543 := bstep (se 1 (by rfl) ⟨1447157, by rfl⟩ : syracuseStep 1929543 = 2894315) B2894315
theorem B2170741 : Blo 1929435 2170741 := bbase (se 5 (by rfl) ⟨101753, by rfl⟩ : syracuseStep 2170741 = 203507) (by norm_num)
theorem B2894321 : Blo 1929435 2894321 := bstep (se 2 (by rfl) ⟨1085370, by rfl⟩ : syracuseStep 2894321 = 2170741) B2170741
theorem B1929547 : Blo 1929435 1929547 := bstep (se 1 (by rfl) ⟨1447160, by rfl⟩ : syracuseStep 1929547 = 2894321) B2894321
theorem B2442089 : Blo 1929435 2442089 := bbase (se 2 (by rfl) ⟨915783, by rfl⟩ : syracuseStep 2442089 = 1831567) (by norm_num)
theorem B6512237 : Blo 1929435 6512237 := bstep (se 3 (by rfl) ⟨1221044, by rfl⟩ : syracuseStep 6512237 = 2442089) B2442089
theorem B4341491 : Blo 1929435 4341491 := bstep (se 1 (by rfl) ⟨3256118, by rfl⟩ : syracuseStep 4341491 = 6512237) B6512237
theorem B2894327 : Blo 1929435 2894327 := bstep (se 1 (by rfl) ⟨2170745, by rfl⟩ : syracuseStep 2894327 = 4341491) B4341491
theorem B1929551 : Blo 1929435 1929551 := bstep (se 1 (by rfl) ⟨1447163, by rfl⟩ : syracuseStep 1929551 = 2894327) B2894327
theorem B2894333 : Blo 1929435 2894333 := bbase (se 3 (by rfl) ⟨542687, by rfl⟩ : syracuseStep 2894333 = 1085375) (by norm_num)
theorem B1929555 : Blo 1929435 1929555 := bstep (se 1 (by rfl) ⟨1447166, by rfl⟩ : syracuseStep 1929555 = 2894333) B2894333
theorem B4341509 : Blo 1929435 4341509 := bbase (se 4 (by rfl) ⟨407016, by rfl⟩ : syracuseStep 4341509 = 814033) (by norm_num)
theorem B2894339 : Blo 1929435 2894339 := bstep (se 1 (by rfl) ⟨2170754, by rfl⟩ : syracuseStep 2894339 = 4341509) B4341509
theorem B1929559 : Blo 1929435 1929559 := bstep (se 1 (by rfl) ⟨1447169, by rfl⟩ : syracuseStep 1929559 = 2894339) B2894339
theorem B3663157 : Blo 1929435 3663157 := bbase (se 5 (by rfl) ⟨171710, by rfl⟩ : syracuseStep 3663157 = 343421) (by norm_num)
theorem B4884209 : Blo 1929435 4884209 := bstep (se 2 (by rfl) ⟨1831578, by rfl⟩ : syracuseStep 4884209 = 3663157) B3663157
theorem B3256139 : Blo 1929435 3256139 := bstep (se 1 (by rfl) ⟨2442104, by rfl⟩ : syracuseStep 3256139 = 4884209) B4884209
theorem B2170759 : Blo 1929435 2170759 := bstep (se 1 (by rfl) ⟨1628069, by rfl⟩ : syracuseStep 2170759 = 3256139) B3256139
theorem B2894345 : Blo 1929435 2894345 := bstep (se 2 (by rfl) ⟨1085379, by rfl⟩ : syracuseStep 2894345 = 2170759) B2170759
theorem B1929563 : Blo 1929435 1929563 := bstep (se 1 (by rfl) ⟨1447172, by rfl⟩ : syracuseStep 1929563 = 2894345) B2894345
theorem B9768437 : Blo 1929435 9768437 := bbase (se 5 (by rfl) ⟨457895, by rfl⟩ : syracuseStep 9768437 = 915791) (by norm_num)
theorem B6512291 : Blo 1929435 6512291 := bstep (se 1 (by rfl) ⟨4884218, by rfl⟩ : syracuseStep 6512291 = 9768437) B9768437
theorem B4341527 : Blo 1929435 4341527 := bstep (se 1 (by rfl) ⟨3256145, by rfl⟩ : syracuseStep 4341527 = 6512291) B6512291
theorem B2894351 : Blo 1929435 2894351 := bstep (se 1 (by rfl) ⟨2170763, by rfl⟩ : syracuseStep 2894351 = 4341527) B4341527
theorem B1929567 : Blo 1929435 1929567 := bstep (se 1 (by rfl) ⟨1447175, by rfl⟩ : syracuseStep 1929567 = 2894351) B2894351
theorem B2894357 : Blo 1929435 2894357 := bbase (se 6 (by rfl) ⟨67836, by rfl⟩ : syracuseStep 2894357 = 135673) (by norm_num)
theorem B1929571 : Blo 1929435 1929571 := bstep (se 1 (by rfl) ⟨1447178, by rfl⟩ : syracuseStep 1929571 = 2894357) B2894357
theorem B16484309 : Blo 1929435 16484309 := bbase (se 7 (by rfl) ⟨193175, by rfl⟩ : syracuseStep 16484309 = 386351) (by norm_num)
theorem B10989539 : Blo 1929435 10989539 := bstep (se 1 (by rfl) ⟨8242154, by rfl⟩ : syracuseStep 10989539 = 16484309) B16484309
theorem B7326359 : Blo 1929435 7326359 := bstep (se 1 (by rfl) ⟨5494769, by rfl⟩ : syracuseStep 7326359 = 10989539) B10989539
theorem B4884239 : Blo 1929435 4884239 := bstep (se 1 (by rfl) ⟨3663179, by rfl⟩ : syracuseStep 4884239 = 7326359) B7326359
theorem B3256159 : Blo 1929435 3256159 := bstep (se 1 (by rfl) ⟨2442119, by rfl⟩ : syracuseStep 3256159 = 4884239) B4884239
theorem B4341545 : Blo 1929435 4341545 := bstep (se 2 (by rfl) ⟨1628079, by rfl⟩ : syracuseStep 4341545 = 3256159) B3256159
theorem B2894363 : Blo 1929435 2894363 := bstep (se 1 (by rfl) ⟨2170772, by rfl⟩ : syracuseStep 2894363 = 4341545) B4341545
theorem B1929575 : Blo 1929435 1929575 := bstep (se 1 (by rfl) ⟨1447181, by rfl⟩ : syracuseStep 1929575 = 2894363) B2894363
theorem B2170777 : Blo 1929435 2170777 := bbase (se 2 (by rfl) ⟨814041, by rfl⟩ : syracuseStep 2170777 = 1628083) (by norm_num)
theorem B2894369 : Blo 1929435 2894369 := bstep (se 2 (by rfl) ⟨1085388, by rfl⟩ : syracuseStep 2894369 = 2170777) B2170777
theorem B1929579 : Blo 1929435 1929579 := bstep (se 1 (by rfl) ⟨1447184, by rfl⟩ : syracuseStep 1929579 = 2894369) B2894369
theorem B7326389 : Blo 1929435 7326389 := bbase (se 5 (by rfl) ⟨343424, by rfl⟩ : syracuseStep 7326389 = 686849) (by norm_num)
theorem B4884259 : Blo 1929435 4884259 := bstep (se 1 (by rfl) ⟨3663194, by rfl⟩ : syracuseStep 4884259 = 7326389) B7326389
theorem B6512345 : Blo 1929435 6512345 := bstep (se 2 (by rfl) ⟨2442129, by rfl⟩ : syracuseStep 6512345 = 4884259) B4884259
theorem B4341563 : Blo 1929435 4341563 := bstep (se 1 (by rfl) ⟨3256172, by rfl⟩ : syracuseStep 4341563 = 6512345) B6512345
theorem B2894375 : Blo 1929435 2894375 := bstep (se 1 (by rfl) ⟨2170781, by rfl⟩ : syracuseStep 2894375 = 4341563) B4341563
theorem B1929583 : Blo 1929435 1929583 := bstep (se 1 (by rfl) ⟨1447187, by rfl⟩ : syracuseStep 1929583 = 2894375) B2894375
theorem B2894381 : Blo 1929435 2894381 := bbase (se 3 (by rfl) ⟨542696, by rfl⟩ : syracuseStep 2894381 = 1085393) (by norm_num)
theorem B1929587 : Blo 1929435 1929587 := bstep (se 1 (by rfl) ⟨1447190, by rfl⟩ : syracuseStep 1929587 = 2894381) B2894381
theorem B4341581 : Blo 1929435 4341581 := bbase (se 3 (by rfl) ⟨814046, by rfl⟩ : syracuseStep 4341581 = 1628093) (by norm_num)
theorem B2894387 : Blo 1929435 2894387 := bstep (se 1 (by rfl) ⟨2170790, by rfl⟩ : syracuseStep 2894387 = 4341581) B4341581
theorem B1929591 : Blo 1929435 1929591 := bstep (se 1 (by rfl) ⟨1447193, by rfl⟩ : syracuseStep 1929591 = 2894387) B2894387
theorem B2442145 : Blo 1929435 2442145 := bbase (se 2 (by rfl) ⟨915804, by rfl⟩ : syracuseStep 2442145 = 1831609) (by norm_num)
theorem B3256193 : Blo 1929435 3256193 := bstep (se 2 (by rfl) ⟨1221072, by rfl⟩ : syracuseStep 3256193 = 2442145) B2442145
theorem B2170795 : Blo 1929435 2170795 := bstep (se 1 (by rfl) ⟨1628096, by rfl⟩ : syracuseStep 2170795 = 3256193) B3256193
theorem B2894393 : Blo 1929435 2894393 := bstep (se 2 (by rfl) ⟨1085397, by rfl⟩ : syracuseStep 2894393 = 2170795) B2170795
theorem B1929595 : Blo 1929435 1929595 := bstep (se 1 (by rfl) ⟨1447196, by rfl⟩ : syracuseStep 1929595 = 2894393) B2894393
theorem B21979349 : Blo 1929435 21979349 := bbase (se 7 (by rfl) ⟨257570, by rfl⟩ : syracuseStep 21979349 = 515141) (by norm_num)
theorem B14652899 : Blo 1929435 14652899 := bstep (se 1 (by rfl) ⟨10989674, by rfl⟩ : syracuseStep 14652899 = 21979349) B21979349
theorem B9768599 : Blo 1929435 9768599 := bstep (se 1 (by rfl) ⟨7326449, by rfl⟩ : syracuseStep 9768599 = 14652899) B14652899
theorem B6512399 : Blo 1929435 6512399 := bstep (se 1 (by rfl) ⟨4884299, by rfl⟩ : syracuseStep 6512399 = 9768599) B9768599
theorem B4341599 : Blo 1929435 4341599 := bstep (se 1 (by rfl) ⟨3256199, by rfl⟩ : syracuseStep 4341599 = 6512399) B6512399
theorem B2894399 : Blo 1929435 2894399 := bstep (se 1 (by rfl) ⟨2170799, by rfl⟩ : syracuseStep 2894399 = 4341599) B4341599
theorem B1929599 : Blo 1929435 1929599 := bstep (se 1 (by rfl) ⟨1447199, by rfl⟩ : syracuseStep 1929599 = 2894399) B2894399
theorem B2894405 : Blo 1929435 2894405 := bbase (se 4 (by rfl) ⟨271350, by rfl⟩ : syracuseStep 2894405 = 542701) (by norm_num)
theorem B1929603 : Blo 1929435 1929603 := bstep (se 1 (by rfl) ⟨1447202, by rfl⟩ : syracuseStep 1929603 = 2894405) B2894405
theorem B3256213 : Blo 1929435 3256213 := bbase (se 6 (by rfl) ⟨76317, by rfl⟩ : syracuseStep 3256213 = 152635) (by norm_num)
theorem B4341617 : Blo 1929435 4341617 := bstep (se 2 (by rfl) ⟨1628106, by rfl⟩ : syracuseStep 4341617 = 3256213) B3256213
theorem B2894411 : Blo 1929435 2894411 := bstep (se 1 (by rfl) ⟨2170808, by rfl⟩ : syracuseStep 2894411 = 4341617) B4341617
theorem B1929607 : Blo 1929435 1929607 := bstep (se 1 (by rfl) ⟨1447205, by rfl⟩ : syracuseStep 1929607 = 2894411) B2894411
theorem B2170813 : Blo 1929435 2170813 := bbase (se 3 (by rfl) ⟨407027, by rfl⟩ : syracuseStep 2170813 = 814055) (by norm_num)
theorem B2894417 : Blo 1929435 2894417 := bstep (se 2 (by rfl) ⟨1085406, by rfl⟩ : syracuseStep 2894417 = 2170813) B2170813
theorem B1929611 : Blo 1929435 1929611 := bstep (se 1 (by rfl) ⟨1447208, by rfl⟩ : syracuseStep 1929611 = 2894417) B2894417
theorem B6512453 : Blo 1929435 6512453 := bbase (se 4 (by rfl) ⟨610542, by rfl⟩ : syracuseStep 6512453 = 1221085) (by norm_num)
theorem B4341635 : Blo 1929435 4341635 := bstep (se 1 (by rfl) ⟨3256226, by rfl⟩ : syracuseStep 4341635 = 6512453) B6512453
theorem B2894423 : Blo 1929435 2894423 := bstep (se 1 (by rfl) ⟨2170817, by rfl⟩ : syracuseStep 2894423 = 4341635) B4341635
theorem B1929615 : Blo 1929435 1929615 := bstep (se 1 (by rfl) ⟨1447211, by rfl⟩ : syracuseStep 1929615 = 2894423) B2894423
theorem B2894429 : Blo 1929435 2894429 := bbase (se 3 (by rfl) ⟨542705, by rfl⟩ : syracuseStep 2894429 = 1085411) (by norm_num)
theorem B1929619 : Blo 1929435 1929619 := bstep (se 1 (by rfl) ⟨1447214, by rfl⟩ : syracuseStep 1929619 = 2894429) B2894429
theorem B4341653 : Blo 1929435 4341653 := bbase (se 6 (by rfl) ⟨101757, by rfl⟩ : syracuseStep 4341653 = 203515) (by norm_num)
theorem B2894435 : Blo 1929435 2894435 := bstep (se 1 (by rfl) ⟨2170826, by rfl⟩ : syracuseStep 2894435 = 4341653) B4341653
theorem B1929623 : Blo 1929435 1929623 := bstep (se 1 (by rfl) ⟨1447217, by rfl⟩ : syracuseStep 1929623 = 2894435) B2894435
theorem B4121189 : Blo 1929435 4121189 := bbase (se 4 (by rfl) ⟨386361, by rfl⟩ : syracuseStep 4121189 = 772723) (by norm_num)
theorem B2747459 : Blo 1929435 2747459 := bstep (se 1 (by rfl) ⟨2060594, by rfl⟩ : syracuseStep 2747459 = 4121189) B4121189
theorem B7326557 : Blo 1929435 7326557 := bstep (se 3 (by rfl) ⟨1373729, by rfl⟩ : syracuseStep 7326557 = 2747459) B2747459
theorem B4884371 : Blo 1929435 4884371 := bstep (se 1 (by rfl) ⟨3663278, by rfl⟩ : syracuseStep 4884371 = 7326557) B7326557
theorem B3256247 : Blo 1929435 3256247 := bstep (se 1 (by rfl) ⟨2442185, by rfl⟩ : syracuseStep 3256247 = 4884371) B4884371
theorem B2170831 : Blo 1929435 2170831 := bstep (se 1 (by rfl) ⟨1628123, by rfl⟩ : syracuseStep 2170831 = 3256247) B3256247
theorem B2894441 : Blo 1929435 2894441 := bstep (se 2 (by rfl) ⟨1085415, by rfl⟩ : syracuseStep 2894441 = 2170831) B2170831
theorem B1929627 : Blo 1929435 1929627 := bstep (se 1 (by rfl) ⟨1447220, by rfl⟩ : syracuseStep 1929627 = 2894441) B2894441
theorem B9272693 : Blo 1929435 9272693 := bbase (se 5 (by rfl) ⟨434657, by rfl⟩ : syracuseStep 9272693 = 869315) (by norm_num)
theorem B6181795 : Blo 1929435 6181795 := bstep (se 1 (by rfl) ⟨4636346, by rfl⟩ : syracuseStep 6181795 = 9272693) B9272693
theorem B8242393 : Blo 1929435 8242393 := bstep (se 2 (by rfl) ⟨3090897, by rfl⟩ : syracuseStep 8242393 = 6181795) B6181795
theorem B10989857 : Blo 1929435 10989857 := bstep (se 2 (by rfl) ⟨4121196, by rfl⟩ : syracuseStep 10989857 = 8242393) B8242393
theorem B7326571 : Blo 1929435 7326571 := bstep (se 1 (by rfl) ⟨5494928, by rfl⟩ : syracuseStep 7326571 = 10989857) B10989857
theorem B9768761 : Blo 1929435 9768761 := bstep (se 2 (by rfl) ⟨3663285, by rfl⟩ : syracuseStep 9768761 = 7326571) B7326571
theorem B6512507 : Blo 1929435 6512507 := bstep (se 1 (by rfl) ⟨4884380, by rfl⟩ : syracuseStep 6512507 = 9768761) B9768761
theorem B4341671 : Blo 1929435 4341671 := bstep (se 1 (by rfl) ⟨3256253, by rfl⟩ : syracuseStep 4341671 = 6512507) B6512507
theorem B2894447 : Blo 1929435 2894447 := bstep (se 1 (by rfl) ⟨2170835, by rfl⟩ : syracuseStep 2894447 = 4341671) B4341671
theorem B1929631 : Blo 1929435 1929631 := bstep (se 1 (by rfl) ⟨1447223, by rfl⟩ : syracuseStep 1929631 = 2894447) B2894447
theorem B2894453 : Blo 1929435 2894453 := bbase (se 5 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 2894453 = 271355) (by norm_num)
theorem B1929635 : Blo 1929435 1929635 := bstep (se 1 (by rfl) ⟨1447226, by rfl⟩ : syracuseStep 1929635 = 2894453) B2894453
theorem B3663301 : Blo 1929435 3663301 := bbase (se 4 (by rfl) ⟨343434, by rfl⟩ : syracuseStep 3663301 = 686869) (by norm_num)
theorem B4884401 : Blo 1929435 4884401 := bstep (se 2 (by rfl) ⟨1831650, by rfl⟩ : syracuseStep 4884401 = 3663301) B3663301
theorem B3256267 : Blo 1929435 3256267 := bstep (se 1 (by rfl) ⟨2442200, by rfl⟩ : syracuseStep 3256267 = 4884401) B4884401
theorem B4341689 : Blo 1929435 4341689 := bstep (se 2 (by rfl) ⟨1628133, by rfl⟩ : syracuseStep 4341689 = 3256267) B3256267
theorem B2894459 : Blo 1929435 2894459 := bstep (se 1 (by rfl) ⟨2170844, by rfl⟩ : syracuseStep 2894459 = 4341689) B4341689
theorem B1929639 : Blo 1929435 1929639 := bstep (se 1 (by rfl) ⟨1447229, by rfl⟩ : syracuseStep 1929639 = 2894459) B2894459
theorem B2170849 : Blo 1929435 2170849 := bbase (se 2 (by rfl) ⟨814068, by rfl⟩ : syracuseStep 2170849 = 1628137) (by norm_num)
theorem B2894465 : Blo 1929435 2894465 := bstep (se 2 (by rfl) ⟨1085424, by rfl⟩ : syracuseStep 2894465 = 2170849) B2170849
theorem B1929643 : Blo 1929435 1929643 := bstep (se 1 (by rfl) ⟨1447232, by rfl⟩ : syracuseStep 1929643 = 2894465) B2894465
theorem B4884421 : Blo 1929435 4884421 := bbase (se 4 (by rfl) ⟨457914, by rfl⟩ : syracuseStep 4884421 = 915829) (by norm_num)
theorem B6512561 : Blo 1929435 6512561 := bstep (se 2 (by rfl) ⟨2442210, by rfl⟩ : syracuseStep 6512561 = 4884421) B4884421
theorem B4341707 : Blo 1929435 4341707 := bstep (se 1 (by rfl) ⟨3256280, by rfl⟩ : syracuseStep 4341707 = 6512561) B6512561
theorem B2894471 : Blo 1929435 2894471 := bstep (se 1 (by rfl) ⟨2170853, by rfl⟩ : syracuseStep 2894471 = 4341707) B4341707
theorem B1929647 : Blo 1929435 1929647 := bstep (se 1 (by rfl) ⟨1447235, by rfl⟩ : syracuseStep 1929647 = 2894471) B2894471
theorem B2894477 : Blo 1929435 2894477 := bbase (se 3 (by rfl) ⟨542714, by rfl⟩ : syracuseStep 2894477 = 1085429) (by norm_num)
theorem B1929651 : Blo 1929435 1929651 := bstep (se 1 (by rfl) ⟨1447238, by rfl⟩ : syracuseStep 1929651 = 2894477) B2894477
theorem B4341725 : Blo 1929435 4341725 := bbase (se 3 (by rfl) ⟨814073, by rfl⟩ : syracuseStep 4341725 = 1628147) (by norm_num)
theorem B2894483 : Blo 1929435 2894483 := bstep (se 1 (by rfl) ⟨2170862, by rfl⟩ : syracuseStep 2894483 = 4341725) B4341725
theorem B1929655 : Blo 1929435 1929655 := bstep (se 1 (by rfl) ⟨1447241, by rfl⟩ : syracuseStep 1929655 = 2894483) B2894483
theorem B3256301 : Blo 1929435 3256301 := bbase (se 3 (by rfl) ⟨610556, by rfl⟩ : syracuseStep 3256301 = 1221113) (by norm_num)
theorem B2170867 : Blo 1929435 2170867 := bstep (se 1 (by rfl) ⟨1628150, by rfl⟩ : syracuseStep 2170867 = 3256301) B3256301
theorem B2894489 : Blo 1929435 2894489 := bstep (se 2 (by rfl) ⟨1085433, by rfl⟩ : syracuseStep 2894489 = 2170867) B2170867
theorem B1929659 : Blo 1929435 1929659 := bstep (se 1 (by rfl) ⟨1447244, by rfl⟩ : syracuseStep 1929659 = 2894489) B2894489
theorem B4400981 : Blo 1929435 4400981 := bbase (se 9 (by rfl) ⟨12893, by rfl⟩ : syracuseStep 4400981 = 25787) (by norm_num)
theorem B2933987 : Blo 1929435 2933987 := bstep (se 1 (by rfl) ⟨2200490, by rfl⟩ : syracuseStep 2933987 = 4400981) B4400981
theorem B7823965 : Blo 1929435 7823965 := bstep (se 3 (by rfl) ⟨1466993, by rfl⟩ : syracuseStep 7823965 = 2933987) B2933987
theorem B10431953 : Blo 1929435 10431953 := bstep (se 2 (by rfl) ⟨3911982, by rfl⟩ : syracuseStep 10431953 = 7823965) B7823965
theorem B6954635 : Blo 1929435 6954635 := bstep (se 1 (by rfl) ⟨5215976, by rfl⟩ : syracuseStep 6954635 = 10431953) B10431953
theorem B4636423 : Blo 1929435 4636423 := bstep (se 1 (by rfl) ⟨3477317, by rfl⟩ : syracuseStep 4636423 = 6954635) B6954635
theorem B24727589 : Blo 1929435 24727589 := bstep (se 4 (by rfl) ⟨2318211, by rfl⟩ : syracuseStep 24727589 = 4636423) B4636423
theorem B16485059 : Blo 1929435 16485059 := bstep (se 1 (by rfl) ⟨12363794, by rfl⟩ : syracuseStep 16485059 = 24727589) B24727589
theorem B10990039 : Blo 1929435 10990039 := bstep (se 1 (by rfl) ⟨8242529, by rfl⟩ : syracuseStep 10990039 = 16485059) B16485059
theorem B14653385 : Blo 1929435 14653385 := bstep (se 2 (by rfl) ⟨5495019, by rfl⟩ : syracuseStep 14653385 = 10990039) B10990039
theorem B9768923 : Blo 1929435 9768923 := bstep (se 1 (by rfl) ⟨7326692, by rfl⟩ : syracuseStep 9768923 = 14653385) B14653385
theorem B6512615 : Blo 1929435 6512615 := bstep (se 1 (by rfl) ⟨4884461, by rfl⟩ : syracuseStep 6512615 = 9768923) B9768923
theorem B4341743 : Blo 1929435 4341743 := bstep (se 1 (by rfl) ⟨3256307, by rfl⟩ : syracuseStep 4341743 = 6512615) B6512615
theorem B2894495 : Blo 1929435 2894495 := bstep (se 1 (by rfl) ⟨2170871, by rfl⟩ : syracuseStep 2894495 = 4341743) B4341743
theorem B1929663 : Blo 1929435 1929663 := bstep (se 1 (by rfl) ⟨1447247, by rfl⟩ : syracuseStep 1929663 = 2894495) B2894495
theorem B2894501 : Blo 1929435 2894501 := bbase (se 4 (by rfl) ⟨271359, by rfl⟩ : syracuseStep 2894501 = 542719) (by norm_num)
theorem B1929667 : Blo 1929435 1929667 := bstep (se 1 (by rfl) ⟨1447250, by rfl⟩ : syracuseStep 1929667 = 2894501) B2894501
theorem B2442241 : Blo 1929435 2442241 := bbase (se 2 (by rfl) ⟨915840, by rfl⟩ : syracuseStep 2442241 = 1831681) (by norm_num)
theorem B3256321 : Blo 1929435 3256321 := bstep (se 2 (by rfl) ⟨1221120, by rfl⟩ : syracuseStep 3256321 = 2442241) B2442241
theorem B4341761 : Blo 1929435 4341761 := bstep (se 2 (by rfl) ⟨1628160, by rfl⟩ : syracuseStep 4341761 = 3256321) B3256321
theorem B2894507 : Blo 1929435 2894507 := bstep (se 1 (by rfl) ⟨2170880, by rfl⟩ : syracuseStep 2894507 = 4341761) B4341761
theorem B1929671 : Blo 1929435 1929671 := bstep (se 1 (by rfl) ⟨1447253, by rfl⟩ : syracuseStep 1929671 = 2894507) B2894507
theorem B2170885 : Blo 1929435 2170885 := bbase (se 4 (by rfl) ⟨203520, by rfl⟩ : syracuseStep 2170885 = 407041) (by norm_num)
theorem B2894513 : Blo 1929435 2894513 := bstep (se 2 (by rfl) ⟨1085442, by rfl⟩ : syracuseStep 2894513 = 2170885) B2170885
theorem B1929675 : Blo 1929435 1929675 := bstep (se 1 (by rfl) ⟨1447256, by rfl⟩ : syracuseStep 1929675 = 2894513) B2894513
theorem B2747533 : Blo 1929435 2747533 := bbase (se 3 (by rfl) ⟨515162, by rfl⟩ : syracuseStep 2747533 = 1030325) (by norm_num)
theorem B3663377 : Blo 1929435 3663377 := bstep (se 2 (by rfl) ⟨1373766, by rfl⟩ : syracuseStep 3663377 = 2747533) B2747533
theorem B2442251 : Blo 1929435 2442251 := bstep (se 1 (by rfl) ⟨1831688, by rfl⟩ : syracuseStep 2442251 = 3663377) B3663377
theorem B6512669 : Blo 1929435 6512669 := bstep (se 3 (by rfl) ⟨1221125, by rfl⟩ : syracuseStep 6512669 = 2442251) B2442251
theorem B4341779 : Blo 1929435 4341779 := bstep (se 1 (by rfl) ⟨3256334, by rfl⟩ : syracuseStep 4341779 = 6512669) B6512669
theorem B2894519 : Blo 1929435 2894519 := bstep (se 1 (by rfl) ⟨2170889, by rfl⟩ : syracuseStep 2894519 = 4341779) B4341779
theorem B1929679 : Blo 1929435 1929679 := bstep (se 1 (by rfl) ⟨1447259, by rfl⟩ : syracuseStep 1929679 = 2894519) B2894519
theorem B2894525 : Blo 1929435 2894525 := bbase (se 3 (by rfl) ⟨542723, by rfl⟩ : syracuseStep 2894525 = 1085447) (by norm_num)
theorem B1929683 : Blo 1929435 1929683 := bstep (se 1 (by rfl) ⟨1447262, by rfl⟩ : syracuseStep 1929683 = 2894525) B2894525
theorem B4341797 : Blo 1929435 4341797 := bbase (se 4 (by rfl) ⟨407043, by rfl⟩ : syracuseStep 4341797 = 814087) (by norm_num)
theorem B2894531 : Blo 1929435 2894531 := bstep (se 1 (by rfl) ⟨2170898, by rfl⟩ : syracuseStep 2894531 = 4341797) B4341797
theorem B1929687 : Blo 1929435 1929687 := bstep (se 1 (by rfl) ⟨1447265, by rfl⟩ : syracuseStep 1929687 = 2894531) B2894531
theorem B4884533 : Blo 1929435 4884533 := bbase (se 5 (by rfl) ⟨228962, by rfl⟩ : syracuseStep 4884533 = 457925) (by norm_num)
theorem B3256355 : Blo 1929435 3256355 := bstep (se 1 (by rfl) ⟨2442266, by rfl⟩ : syracuseStep 3256355 = 4884533) B4884533
theorem B2170903 : Blo 1929435 2170903 := bstep (se 1 (by rfl) ⟨1628177, by rfl⟩ : syracuseStep 2170903 = 3256355) B3256355
theorem B2894537 : Blo 1929435 2894537 := bstep (se 2 (by rfl) ⟨1085451, by rfl⟩ : syracuseStep 2894537 = 2170903) B2170903
theorem B1929691 : Blo 1929435 1929691 := bstep (se 1 (by rfl) ⟨1447268, by rfl⟩ : syracuseStep 1929691 = 2894537) B2894537
theorem B2543605 : Blo 1929435 2543605 := bbase (se 5 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 2543605 = 238463) (by norm_num)
theorem B13565893 : Blo 1929435 13565893 := bstep (se 4 (by rfl) ⟨1271802, by rfl⟩ : syracuseStep 13565893 = 2543605) B2543605
theorem B18087857 : Blo 1929435 18087857 := bstep (se 2 (by rfl) ⟨6782946, by rfl⟩ : syracuseStep 18087857 = 13565893) B13565893
theorem B12058571 : Blo 1929435 12058571 := bstep (se 1 (by rfl) ⟨9043928, by rfl⟩ : syracuseStep 12058571 = 18087857) B18087857
theorem B32156189 : Blo 1929435 32156189 := bstep (se 3 (by rfl) ⟨6029285, by rfl⟩ : syracuseStep 32156189 = 12058571) B12058571
theorem B21437459 : Blo 1929435 21437459 := bstep (se 1 (by rfl) ⟨16078094, by rfl⟩ : syracuseStep 21437459 = 32156189) B32156189
theorem B14291639 : Blo 1929435 14291639 := bstep (se 1 (by rfl) ⟨10718729, by rfl⟩ : syracuseStep 14291639 = 21437459) B21437459
theorem B9527759 : Blo 1929435 9527759 := bstep (se 1 (by rfl) ⟨7145819, by rfl⟩ : syracuseStep 9527759 = 14291639) B14291639
theorem B6351839 : Blo 1929435 6351839 := bstep (se 1 (by rfl) ⟨4763879, by rfl⟩ : syracuseStep 6351839 = 9527759) B9527759
theorem B4234559 : Blo 1929435 4234559 := bstep (se 1 (by rfl) ⟨3175919, by rfl⟩ : syracuseStep 4234559 = 6351839) B6351839
theorem B11292157 : Blo 1929435 11292157 := bstep (se 3 (by rfl) ⟨2117279, by rfl⟩ : syracuseStep 11292157 = 4234559) B4234559
theorem B15056209 : Blo 1929435 15056209 := bstep (se 2 (by rfl) ⟨5646078, by rfl⟩ : syracuseStep 15056209 = 11292157) B11292157
theorem B80299781 : Blo 1929435 80299781 := bstep (se 4 (by rfl) ⟨7528104, by rfl⟩ : syracuseStep 80299781 = 15056209) B15056209
theorem B53533187 : Blo 1929435 53533187 := bstep (se 1 (by rfl) ⟨40149890, by rfl⟩ : syracuseStep 53533187 = 80299781) B80299781
theorem B35688791 : Blo 1929435 35688791 := bstep (se 1 (by rfl) ⟨26766593, by rfl⟩ : syracuseStep 35688791 = 53533187) B53533187
theorem B23792527 : Blo 1929435 23792527 := bstep (se 1 (by rfl) ⟨17844395, by rfl⟩ : syracuseStep 23792527 = 35688791) B35688791
theorem B31723369 : Blo 1929435 31723369 := bstep (se 2 (by rfl) ⟨11896263, by rfl⟩ : syracuseStep 31723369 = 23792527) B23792527
theorem B676765205 : Blo 1929435 676765205 := bstep (se 6 (by rfl) ⟨15861684, by rfl⟩ : syracuseStep 676765205 = 31723369) B31723369
theorem B451176803 : Blo 1929435 451176803 := bstep (se 1 (by rfl) ⟨338382602, by rfl⟩ : syracuseStep 451176803 = 676765205) B676765205
theorem B300784535 : Blo 1929435 300784535 := bstep (se 1 (by rfl) ⟨225588401, by rfl⟩ : syracuseStep 300784535 = 451176803) B451176803
theorem B200523023 : Blo 1929435 200523023 := bstep (se 1 (by rfl) ⟨150392267, by rfl⟩ : syracuseStep 200523023 = 300784535) B300784535
theorem B133682015 : Blo 1929435 133682015 := bstep (se 1 (by rfl) ⟨100261511, by rfl⟩ : syracuseStep 133682015 = 200523023) B200523023
theorem B89121343 : Blo 1929435 89121343 := bstep (se 1 (by rfl) ⟨66841007, by rfl⟩ : syracuseStep 89121343 = 133682015) B133682015
theorem B118828457 : Blo 1929435 118828457 := bstep (se 2 (by rfl) ⟨44560671, by rfl⟩ : syracuseStep 118828457 = 89121343) B89121343
theorem B79218971 : Blo 1929435 79218971 := bstep (se 1 (by rfl) ⟨59414228, by rfl⟩ : syracuseStep 79218971 = 118828457) B118828457
theorem B52812647 : Blo 1929435 52812647 := bstep (se 1 (by rfl) ⟨39609485, by rfl⟩ : syracuseStep 52812647 = 79218971) B79218971
theorem B35208431 : Blo 1929435 35208431 := bstep (se 1 (by rfl) ⟨26406323, by rfl⟩ : syracuseStep 35208431 = 52812647) B52812647
theorem B23472287 : Blo 1929435 23472287 := bstep (se 1 (by rfl) ⟨17604215, by rfl⟩ : syracuseStep 23472287 = 35208431) B35208431
theorem B15648191 : Blo 1929435 15648191 := bstep (se 1 (by rfl) ⟨11736143, by rfl⟩ : syracuseStep 15648191 = 23472287) B23472287
theorem B10432127 : Blo 1929435 10432127 := bstep (se 1 (by rfl) ⟨7824095, by rfl⟩ : syracuseStep 10432127 = 15648191) B15648191
theorem B6954751 : Blo 1929435 6954751 := bstep (se 1 (by rfl) ⟨5216063, by rfl⟩ : syracuseStep 6954751 = 10432127) B10432127
theorem B9273001 : Blo 1929435 9273001 := bstep (se 2 (by rfl) ⟨3477375, by rfl⟩ : syracuseStep 9273001 = 6954751) B6954751
theorem B12364001 : Blo 1929435 12364001 := bstep (se 2 (by rfl) ⟨4636500, by rfl⟩ : syracuseStep 12364001 = 9273001) B9273001
theorem B8242667 : Blo 1929435 8242667 := bstep (se 1 (by rfl) ⟨6182000, by rfl⟩ : syracuseStep 8242667 = 12364001) B12364001
theorem B5495111 : Blo 1929435 5495111 := bstep (se 1 (by rfl) ⟨4121333, by rfl⟩ : syracuseStep 5495111 = 8242667) B8242667
theorem B3663407 : Blo 1929435 3663407 := bstep (se 1 (by rfl) ⟨2747555, by rfl⟩ : syracuseStep 3663407 = 5495111) B5495111
theorem B9769085 : Blo 1929435 9769085 := bstep (se 3 (by rfl) ⟨1831703, by rfl⟩ : syracuseStep 9769085 = 3663407) B3663407
theorem B6512723 : Blo 1929435 6512723 := bstep (se 1 (by rfl) ⟨4884542, by rfl⟩ : syracuseStep 6512723 = 9769085) B9769085
theorem B4341815 : Blo 1929435 4341815 := bstep (se 1 (by rfl) ⟨3256361, by rfl⟩ : syracuseStep 4341815 = 6512723) B6512723
theorem B2894543 : Blo 1929435 2894543 := bstep (se 1 (by rfl) ⟨2170907, by rfl⟩ : syracuseStep 2894543 = 4341815) B4341815
theorem B1929695 : Blo 1929435 1929695 := bstep (se 1 (by rfl) ⟨1447271, by rfl⟩ : syracuseStep 1929695 = 2894543) B2894543
theorem B2894549 : Blo 1929435 2894549 := bbase (se 7 (by rfl) ⟨33920, by rfl⟩ : syracuseStep 2894549 = 67841) (by norm_num)
theorem B1929699 : Blo 1929435 1929699 := bstep (se 1 (by rfl) ⟨1447274, by rfl⟩ : syracuseStep 1929699 = 2894549) B2894549
theorem B2200537 : Blo 1929435 2200537 := bbase (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) (by norm_num)
theorem B2934049 : Blo 1929435 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B3912065 : Blo 1929435 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B2608043 : Blo 1929435 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B6954781 : Blo 1929435 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B9273041 : Blo 1929435 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B6182027 : Blo 1929435 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B4121351 : Blo 1929435 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B2747567 : Blo 1929435 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B7326845 : Blo 1929435 7326845 := bstep (se 3 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 7326845 = 2747567) B2747567
theorem B4884563 : Blo 1929435 4884563 := bstep (se 1 (by rfl) ⟨3663422, by rfl⟩ : syracuseStep 4884563 = 7326845) B7326845
theorem B3256375 : Blo 1929435 3256375 := bstep (se 1 (by rfl) ⟨2442281, by rfl⟩ : syracuseStep 3256375 = 4884563) B4884563
theorem B4341833 : Blo 1929435 4341833 := bstep (se 2 (by rfl) ⟨1628187, by rfl⟩ : syracuseStep 4341833 = 3256375) B3256375
theorem B2894555 : Blo 1929435 2894555 := bstep (se 1 (by rfl) ⟨2170916, by rfl⟩ : syracuseStep 2894555 = 4341833) B4341833
theorem B1929703 : Blo 1929435 1929703 := bstep (se 1 (by rfl) ⟨1447277, by rfl⟩ : syracuseStep 1929703 = 2894555) B2894555
theorem B2170921 : Blo 1929435 2170921 := bbase (se 2 (by rfl) ⟨814095, by rfl⟩ : syracuseStep 2170921 = 1628191) (by norm_num)
theorem B2894561 : Blo 1929435 2894561 := bstep (se 2 (by rfl) ⟨1085460, by rfl⟩ : syracuseStep 2894561 = 2170921) B2170921
theorem B1929707 : Blo 1929435 1929707 := bstep (se 1 (by rfl) ⟨1447280, by rfl⟩ : syracuseStep 1929707 = 2894561) B2894561
theorem B16710389 : Blo 1929435 16710389 := bbase (se 5 (by rfl) ⟨783299, by rfl⟩ : syracuseStep 16710389 = 1566599) (by norm_num)
theorem B11140259 : Blo 1929435 11140259 := bstep (se 1 (by rfl) ⟨8355194, by rfl⟩ : syracuseStep 11140259 = 16710389) B16710389
theorem B118829429 : Blo 1929435 118829429 := bstep (se 5 (by rfl) ⟨5570129, by rfl⟩ : syracuseStep 118829429 = 11140259) B11140259
theorem B79219619 : Blo 1929435 79219619 := bstep (se 1 (by rfl) ⟨59414714, by rfl⟩ : syracuseStep 79219619 = 118829429) B118829429
theorem B52813079 : Blo 1929435 52813079 := bstep (se 1 (by rfl) ⟨39609809, by rfl⟩ : syracuseStep 52813079 = 79219619) B79219619
theorem B35208719 : Blo 1929435 35208719 := bstep (se 1 (by rfl) ⟨26406539, by rfl⟩ : syracuseStep 35208719 = 52813079) B52813079
theorem B23472479 : Blo 1929435 23472479 := bstep (se 1 (by rfl) ⟨17604359, by rfl⟩ : syracuseStep 23472479 = 35208719) B35208719
theorem B15648319 : Blo 1929435 15648319 := bstep (se 1 (by rfl) ⟨11736239, by rfl⟩ : syracuseStep 15648319 = 23472479) B23472479
theorem B20864425 : Blo 1929435 20864425 := bstep (se 2 (by rfl) ⟨7824159, by rfl⟩ : syracuseStep 20864425 = 15648319) B15648319
theorem B27819233 : Blo 1929435 27819233 := bstep (se 2 (by rfl) ⟨10432212, by rfl⟩ : syracuseStep 27819233 = 20864425) B20864425
theorem B18546155 : Blo 1929435 18546155 := bstep (se 1 (by rfl) ⟨13909616, by rfl⟩ : syracuseStep 18546155 = 27819233) B27819233
theorem B12364103 : Blo 1929435 12364103 := bstep (se 1 (by rfl) ⟨9273077, by rfl⟩ : syracuseStep 12364103 = 18546155) B18546155
theorem B8242735 : Blo 1929435 8242735 := bstep (se 1 (by rfl) ⟨6182051, by rfl⟩ : syracuseStep 8242735 = 12364103) B12364103
theorem B10990313 : Blo 1929435 10990313 := bstep (se 2 (by rfl) ⟨4121367, by rfl⟩ : syracuseStep 10990313 = 8242735) B8242735
theorem B7326875 : Blo 1929435 7326875 := bstep (se 1 (by rfl) ⟨5495156, by rfl⟩ : syracuseStep 7326875 = 10990313) B10990313
theorem B4884583 : Blo 1929435 4884583 := bstep (se 1 (by rfl) ⟨3663437, by rfl⟩ : syracuseStep 4884583 = 7326875) B7326875
theorem B6512777 : Blo 1929435 6512777 := bstep (se 2 (by rfl) ⟨2442291, by rfl⟩ : syracuseStep 6512777 = 4884583) B4884583
theorem B4341851 : Blo 1929435 4341851 := bstep (se 1 (by rfl) ⟨3256388, by rfl⟩ : syracuseStep 4341851 = 6512777) B6512777
theorem B2894567 : Blo 1929435 2894567 := bstep (se 1 (by rfl) ⟨2170925, by rfl⟩ : syracuseStep 2894567 = 4341851) B4341851
theorem B1929711 : Blo 1929435 1929711 := bstep (se 1 (by rfl) ⟨1447283, by rfl⟩ : syracuseStep 1929711 = 2894567) B2894567
theorem B2894573 : Blo 1929435 2894573 := bbase (se 3 (by rfl) ⟨542732, by rfl⟩ : syracuseStep 2894573 = 1085465) (by norm_num)
theorem B1929715 : Blo 1929435 1929715 := bstep (se 1 (by rfl) ⟨1447286, by rfl⟩ : syracuseStep 1929715 = 2894573) B2894573
theorem B4341869 : Blo 1929435 4341869 := bbase (se 3 (by rfl) ⟨814100, by rfl⟩ : syracuseStep 4341869 = 1628201) (by norm_num)
theorem B2894579 : Blo 1929435 2894579 := bstep (se 1 (by rfl) ⟨2170934, by rfl⟩ : syracuseStep 2894579 = 4341869) B4341869
theorem B1929719 : Blo 1929435 1929719 := bstep (se 1 (by rfl) ⟨1447289, by rfl⟩ : syracuseStep 1929719 = 2894579) B2894579
theorem B3663461 : Blo 1929435 3663461 := bbase (se 4 (by rfl) ⟨343449, by rfl⟩ : syracuseStep 3663461 = 686899) (by norm_num)
theorem B2442307 : Blo 1929435 2442307 := bstep (se 1 (by rfl) ⟨1831730, by rfl⟩ : syracuseStep 2442307 = 3663461) B3663461
theorem B3256409 : Blo 1929435 3256409 := bstep (se 2 (by rfl) ⟨1221153, by rfl⟩ : syracuseStep 3256409 = 2442307) B2442307
theorem B2170939 : Blo 1929435 2170939 := bstep (se 1 (by rfl) ⟨1628204, by rfl⟩ : syracuseStep 2170939 = 3256409) B3256409
theorem B2894585 : Blo 1929435 2894585 := bstep (se 2 (by rfl) ⟨1085469, by rfl⟩ : syracuseStep 2894585 = 2170939) B2170939
theorem B1929723 : Blo 1929435 1929723 := bstep (se 1 (by rfl) ⟨1447292, by rfl⟩ : syracuseStep 1929723 = 2894585) B2894585
theorem B5216149 : Blo 1929435 5216149 := bbase (se 6 (by rfl) ⟨122253, by rfl⟩ : syracuseStep 5216149 = 244507) (by norm_num)
theorem B6954865 : Blo 1929435 6954865 := bstep (se 2 (by rfl) ⟨2608074, by rfl⟩ : syracuseStep 6954865 = 5216149) B5216149
theorem B37092613 : Blo 1929435 37092613 := bstep (se 4 (by rfl) ⟨3477432, by rfl⟩ : syracuseStep 37092613 = 6954865) B6954865
theorem B49456817 : Blo 1929435 49456817 := bstep (se 2 (by rfl) ⟨18546306, by rfl⟩ : syracuseStep 49456817 = 37092613) B37092613
theorem B32971211 : Blo 1929435 32971211 := bstep (se 1 (by rfl) ⟨24728408, by rfl⟩ : syracuseStep 32971211 = 49456817) B49456817
theorem B21980807 : Blo 1929435 21980807 := bstep (se 1 (by rfl) ⟨16485605, by rfl⟩ : syracuseStep 21980807 = 32971211) B32971211
theorem B14653871 : Blo 1929435 14653871 := bstep (se 1 (by rfl) ⟨10990403, by rfl⟩ : syracuseStep 14653871 = 21980807) B21980807
theorem B9769247 : Blo 1929435 9769247 := bstep (se 1 (by rfl) ⟨7326935, by rfl⟩ : syracuseStep 9769247 = 14653871) B14653871
theorem B6512831 : Blo 1929435 6512831 := bstep (se 1 (by rfl) ⟨4884623, by rfl⟩ : syracuseStep 6512831 = 9769247) B9769247
theorem B4341887 : Blo 1929435 4341887 := bstep (se 1 (by rfl) ⟨3256415, by rfl⟩ : syracuseStep 4341887 = 6512831) B6512831
theorem B2894591 : Blo 1929435 2894591 := bstep (se 1 (by rfl) ⟨2170943, by rfl⟩ : syracuseStep 2894591 = 4341887) B4341887
theorem B1929727 : Blo 1929435 1929727 := bstep (se 1 (by rfl) ⟨1447295, by rfl⟩ : syracuseStep 1929727 = 2894591) B2894591
theorem B2894597 : Blo 1929435 2894597 := bbase (se 4 (by rfl) ⟨271368, by rfl⟩ : syracuseStep 2894597 = 542737) (by norm_num)
theorem B1929731 : Blo 1929435 1929731 := bstep (se 1 (by rfl) ⟨1447298, by rfl⟩ : syracuseStep 1929731 = 2894597) B2894597
theorem B3256429 : Blo 1929435 3256429 := bbase (se 3 (by rfl) ⟨610580, by rfl⟩ : syracuseStep 3256429 = 1221161) (by norm_num)
theorem B4341905 : Blo 1929435 4341905 := bstep (se 2 (by rfl) ⟨1628214, by rfl⟩ : syracuseStep 4341905 = 3256429) B3256429
theorem B2894603 : Blo 1929435 2894603 := bstep (se 1 (by rfl) ⟨2170952, by rfl⟩ : syracuseStep 2894603 = 4341905) B4341905
theorem B1929735 : Blo 1929435 1929735 := bstep (se 1 (by rfl) ⟨1447301, by rfl⟩ : syracuseStep 1929735 = 2894603) B2894603
theorem B2170957 : Blo 1929435 2170957 := bbase (se 3 (by rfl) ⟨407054, by rfl⟩ : syracuseStep 2170957 = 814109) (by norm_num)
theorem B2894609 : Blo 1929435 2894609 := bstep (se 2 (by rfl) ⟨1085478, by rfl⟩ : syracuseStep 2894609 = 2170957) B2170957
theorem B1929739 : Blo 1929435 1929739 := bstep (se 1 (by rfl) ⟨1447304, by rfl⟩ : syracuseStep 1929739 = 2894609) B2894609
theorem B6512885 : Blo 1929435 6512885 := bbase (se 5 (by rfl) ⟨305291, by rfl⟩ : syracuseStep 6512885 = 610583) (by norm_num)
theorem B4341923 : Blo 1929435 4341923 := bstep (se 1 (by rfl) ⟨3256442, by rfl⟩ : syracuseStep 4341923 = 6512885) B6512885
theorem B2894615 : Blo 1929435 2894615 := bstep (se 1 (by rfl) ⟨2170961, by rfl⟩ : syracuseStep 2894615 = 4341923) B4341923
theorem B1929743 : Blo 1929435 1929743 := bstep (se 1 (by rfl) ⟨1447307, by rfl⟩ : syracuseStep 1929743 = 2894615) B2894615
theorem B2894621 : Blo 1929435 2894621 := bbase (se 3 (by rfl) ⟨542741, by rfl⟩ : syracuseStep 2894621 = 1085483) (by norm_num)
theorem B1929747 : Blo 1929435 1929747 := bstep (se 1 (by rfl) ⟨1447310, by rfl⟩ : syracuseStep 1929747 = 2894621) B2894621
theorem B4341941 : Blo 1929435 4341941 := bbase (se 5 (by rfl) ⟨203528, by rfl⟩ : syracuseStep 4341941 = 407057) (by norm_num)
theorem B2894627 : Blo 1929435 2894627 := bstep (se 1 (by rfl) ⟨2170970, by rfl⟩ : syracuseStep 2894627 = 4341941) B4341941
theorem B1929751 : Blo 1929435 1929751 := bstep (se 1 (by rfl) ⟨1447313, by rfl⟩ : syracuseStep 1929751 = 2894627) B2894627
theorem B3477485 : Blo 1929435 3477485 := bbase (se 3 (by rfl) ⟨652028, by rfl⟩ : syracuseStep 3477485 = 1304057) (by norm_num)
theorem B2318323 : Blo 1929435 2318323 := bstep (se 1 (by rfl) ⟨1738742, by rfl⟩ : syracuseStep 2318323 = 3477485) B3477485
theorem B3091097 : Blo 1929435 3091097 := bstep (se 2 (by rfl) ⟨1159161, by rfl⟩ : syracuseStep 3091097 = 2318323) B2318323
theorem B2060731 : Blo 1929435 2060731 := bstep (se 1 (by rfl) ⟨1545548, by rfl⟩ : syracuseStep 2060731 = 3091097) B3091097
theorem B10990565 : Blo 1929435 10990565 := bstep (se 4 (by rfl) ⟨1030365, by rfl⟩ : syracuseStep 10990565 = 2060731) B2060731
theorem B7327043 : Blo 1929435 7327043 := bstep (se 1 (by rfl) ⟨5495282, by rfl⟩ : syracuseStep 7327043 = 10990565) B10990565
theorem B4884695 : Blo 1929435 4884695 := bstep (se 1 (by rfl) ⟨3663521, by rfl⟩ : syracuseStep 4884695 = 7327043) B7327043
theorem B3256463 : Blo 1929435 3256463 := bstep (se 1 (by rfl) ⟨2442347, by rfl⟩ : syracuseStep 3256463 = 4884695) B4884695
theorem B2170975 : Blo 1929435 2170975 := bstep (se 1 (by rfl) ⟨1628231, by rfl⟩ : syracuseStep 2170975 = 3256463) B3256463
theorem B2894633 : Blo 1929435 2894633 := bstep (se 2 (by rfl) ⟨1085487, by rfl⟩ : syracuseStep 2894633 = 2170975) B2170975
theorem B1929755 : Blo 1929435 1929755 := bstep (se 1 (by rfl) ⟨1447316, by rfl⟩ : syracuseStep 1929755 = 2894633) B2894633
theorem B2230625 : Blo 1929435 2230625 := bbase (se 2 (by rfl) ⟨836484, by rfl⟩ : syracuseStep 2230625 = 1672969) (by norm_num)
theorem B5948333 : Blo 1929435 5948333 := bstep (se 3 (by rfl) ⟨1115312, by rfl⟩ : syracuseStep 5948333 = 2230625) B2230625
theorem B3965555 : Blo 1929435 3965555 := bstep (se 1 (by rfl) ⟨2974166, by rfl⟩ : syracuseStep 3965555 = 5948333) B5948333
theorem B10574813 : Blo 1929435 10574813 := bstep (se 3 (by rfl) ⟨1982777, by rfl⟩ : syracuseStep 10574813 = 3965555) B3965555
theorem B7049875 : Blo 1929435 7049875 := bstep (se 1 (by rfl) ⟨5287406, by rfl⟩ : syracuseStep 7049875 = 10574813) B10574813
theorem B9399833 : Blo 1929435 9399833 := bstep (se 2 (by rfl) ⟨3524937, by rfl⟩ : syracuseStep 9399833 = 7049875) B7049875
theorem B6266555 : Blo 1929435 6266555 := bstep (se 1 (by rfl) ⟨4699916, by rfl⟩ : syracuseStep 6266555 = 9399833) B9399833
theorem B4177703 : Blo 1929435 4177703 := bstep (se 1 (by rfl) ⟨3133277, by rfl⟩ : syracuseStep 4177703 = 6266555) B6266555
theorem B11140541 : Blo 1929435 11140541 := bstep (se 3 (by rfl) ⟨2088851, by rfl⟩ : syracuseStep 11140541 = 4177703) B4177703
theorem B7427027 : Blo 1929435 7427027 := bstep (se 1 (by rfl) ⟨5570270, by rfl⟩ : syracuseStep 7427027 = 11140541) B11140541
theorem B4951351 : Blo 1929435 4951351 := bstep (se 1 (by rfl) ⟨3713513, by rfl⟩ : syracuseStep 4951351 = 7427027) B7427027
theorem B26407205 : Blo 1929435 26407205 := bstep (se 4 (by rfl) ⟨2475675, by rfl⟩ : syracuseStep 26407205 = 4951351) B4951351
theorem B17604803 : Blo 1929435 17604803 := bstep (se 1 (by rfl) ⟨13203602, by rfl⟩ : syracuseStep 17604803 = 26407205) B26407205
theorem B11736535 : Blo 1929435 11736535 := bstep (se 1 (by rfl) ⟨8802401, by rfl⟩ : syracuseStep 11736535 = 17604803) B17604803
theorem B15648713 : Blo 1929435 15648713 := bstep (se 2 (by rfl) ⟨5868267, by rfl⟩ : syracuseStep 15648713 = 11736535) B11736535
theorem B10432475 : Blo 1929435 10432475 := bstep (se 1 (by rfl) ⟨7824356, by rfl⟩ : syracuseStep 10432475 = 15648713) B15648713
theorem B6954983 : Blo 1929435 6954983 := bstep (se 1 (by rfl) ⟨5216237, by rfl⟩ : syracuseStep 6954983 = 10432475) B10432475
theorem B4636655 : Blo 1929435 4636655 := bstep (se 1 (by rfl) ⟨3477491, by rfl⟩ : syracuseStep 4636655 = 6954983) B6954983
theorem B3091103 : Blo 1929435 3091103 := bstep (se 1 (by rfl) ⟨2318327, by rfl⟩ : syracuseStep 3091103 = 4636655) B4636655
theorem B2060735 : Blo 1929435 2060735 := bstep (se 1 (by rfl) ⟨1545551, by rfl⟩ : syracuseStep 2060735 = 3091103) B3091103
theorem B5495293 : Blo 1929435 5495293 := bstep (se 3 (by rfl) ⟨1030367, by rfl⟩ : syracuseStep 5495293 = 2060735) B2060735
theorem B7327057 : Blo 1929435 7327057 := bstep (se 2 (by rfl) ⟨2747646, by rfl⟩ : syracuseStep 7327057 = 5495293) B5495293
theorem B9769409 : Blo 1929435 9769409 := bstep (se 2 (by rfl) ⟨3663528, by rfl⟩ : syracuseStep 9769409 = 7327057) B7327057
theorem B6512939 : Blo 1929435 6512939 := bstep (se 1 (by rfl) ⟨4884704, by rfl⟩ : syracuseStep 6512939 = 9769409) B9769409
theorem B4341959 : Blo 1929435 4341959 := bstep (se 1 (by rfl) ⟨3256469, by rfl⟩ : syracuseStep 4341959 = 6512939) B6512939
theorem B2894639 : Blo 1929435 2894639 := bstep (se 1 (by rfl) ⟨2170979, by rfl⟩ : syracuseStep 2894639 = 4341959) B4341959
theorem B1929759 : Blo 1929435 1929759 := bstep (se 1 (by rfl) ⟨1447319, by rfl⟩ : syracuseStep 1929759 = 2894639) B2894639
theorem B2894645 : Blo 1929435 2894645 := bbase (se 5 (by rfl) ⟨135686, by rfl⟩ : syracuseStep 2894645 = 271373) (by norm_num)
theorem B1929763 : Blo 1929435 1929763 := bstep (se 1 (by rfl) ⟨1447322, by rfl⟩ : syracuseStep 1929763 = 2894645) B2894645
theorem B4884725 : Blo 1929435 4884725 := bbase (se 5 (by rfl) ⟨228971, by rfl⟩ : syracuseStep 4884725 = 457943) (by norm_num)
theorem B3256483 : Blo 1929435 3256483 := bstep (se 1 (by rfl) ⟨2442362, by rfl⟩ : syracuseStep 3256483 = 4884725) B4884725
theorem B4341977 : Blo 1929435 4341977 := bstep (se 2 (by rfl) ⟨1628241, by rfl⟩ : syracuseStep 4341977 = 3256483) B3256483
theorem B2894651 : Blo 1929435 2894651 := bstep (se 1 (by rfl) ⟨2170988, by rfl⟩ : syracuseStep 2894651 = 4341977) B4341977
theorem B1929767 : Blo 1929435 1929767 := bstep (se 1 (by rfl) ⟨1447325, by rfl⟩ : syracuseStep 1929767 = 2894651) B2894651
theorem B2170993 : Blo 1929435 2170993 := bbase (se 2 (by rfl) ⟨814122, by rfl⟩ : syracuseStep 2170993 = 1628245) (by norm_num)
theorem B2894657 : Blo 1929435 2894657 := bstep (se 2 (by rfl) ⟨1085496, by rfl⟩ : syracuseStep 2894657 = 2170993) B2170993
theorem B1929771 : Blo 1929435 1929771 := bstep (se 1 (by rfl) ⟨1447328, by rfl⟩ : syracuseStep 1929771 = 2894657) B2894657
theorem B4636693 : Blo 1929435 4636693 := bbase (se 6 (by rfl) ⟨108672, by rfl⟩ : syracuseStep 4636693 = 217345) (by norm_num)
theorem B6182257 : Blo 1929435 6182257 := bstep (se 2 (by rfl) ⟨2318346, by rfl⟩ : syracuseStep 6182257 = 4636693) B4636693
theorem B8243009 : Blo 1929435 8243009 := bstep (se 2 (by rfl) ⟨3091128, by rfl⟩ : syracuseStep 8243009 = 6182257) B6182257
theorem B5495339 : Blo 1929435 5495339 := bstep (se 1 (by rfl) ⟨4121504, by rfl⟩ : syracuseStep 5495339 = 8243009) B8243009
theorem B3663559 : Blo 1929435 3663559 := bstep (se 1 (by rfl) ⟨2747669, by rfl⟩ : syracuseStep 3663559 = 5495339) B5495339
theorem B4884745 : Blo 1929435 4884745 := bstep (se 2 (by rfl) ⟨1831779, by rfl⟩ : syracuseStep 4884745 = 3663559) B3663559
theorem B6512993 : Blo 1929435 6512993 := bstep (se 2 (by rfl) ⟨2442372, by rfl⟩ : syracuseStep 6512993 = 4884745) B4884745
theorem B4341995 : Blo 1929435 4341995 := bstep (se 1 (by rfl) ⟨3256496, by rfl⟩ : syracuseStep 4341995 = 6512993) B6512993
theorem B2894663 : Blo 1929435 2894663 := bstep (se 1 (by rfl) ⟨2170997, by rfl⟩ : syracuseStep 2894663 = 4341995) B4341995
theorem B1929775 : Blo 1929435 1929775 := bstep (se 1 (by rfl) ⟨1447331, by rfl⟩ : syracuseStep 1929775 = 2894663) B2894663
theorem B2894669 : Blo 1929435 2894669 := bbase (se 3 (by rfl) ⟨542750, by rfl⟩ : syracuseStep 2894669 = 1085501) (by norm_num)
theorem B1929779 : Blo 1929435 1929779 := bstep (se 1 (by rfl) ⟨1447334, by rfl⟩ : syracuseStep 1929779 = 2894669) B2894669
theorem B4342013 : Blo 1929435 4342013 := bbase (se 3 (by rfl) ⟨814127, by rfl⟩ : syracuseStep 4342013 = 1628255) (by norm_num)
theorem B2894675 : Blo 1929435 2894675 := bstep (se 1 (by rfl) ⟨2171006, by rfl⟩ : syracuseStep 2894675 = 4342013) B4342013
theorem B1929783 : Blo 1929435 1929783 := bstep (se 1 (by rfl) ⟨1447337, by rfl⟩ : syracuseStep 1929783 = 2894675) B2894675
theorem B3256517 : Blo 1929435 3256517 := bbase (se 4 (by rfl) ⟨305298, by rfl⟩ : syracuseStep 3256517 = 610597) (by norm_num)
theorem B2171011 : Blo 1929435 2171011 := bstep (se 1 (by rfl) ⟨1628258, by rfl⟩ : syracuseStep 2171011 = 3256517) B3256517
theorem B2894681 : Blo 1929435 2894681 := bstep (se 2 (by rfl) ⟨1085505, by rfl⟩ : syracuseStep 2894681 = 2171011) B2171011
theorem B1929787 : Blo 1929435 1929787 := bstep (se 1 (by rfl) ⟨1447340, by rfl⟩ : syracuseStep 1929787 = 2894681) B2894681
theorem B14654357 : Blo 1929435 14654357 := bbase (se 6 (by rfl) ⟨343461, by rfl⟩ : syracuseStep 14654357 = 686923) (by norm_num)
theorem B9769571 : Blo 1929435 9769571 := bstep (se 1 (by rfl) ⟨7327178, by rfl⟩ : syracuseStep 9769571 = 14654357) B14654357
theorem B6513047 : Blo 1929435 6513047 := bstep (se 1 (by rfl) ⟨4884785, by rfl⟩ : syracuseStep 6513047 = 9769571) B9769571
theorem B4342031 : Blo 1929435 4342031 := bstep (se 1 (by rfl) ⟨3256523, by rfl⟩ : syracuseStep 4342031 = 6513047) B6513047
theorem B2894687 : Blo 1929435 2894687 := bstep (se 1 (by rfl) ⟨2171015, by rfl⟩ : syracuseStep 2894687 = 4342031) B4342031
theorem B1929791 : Blo 1929435 1929791 := bstep (se 1 (by rfl) ⟨1447343, by rfl⟩ : syracuseStep 1929791 = 2894687) B2894687
theorem B2894693 : Blo 1929435 2894693 := bbase (se 4 (by rfl) ⟨271377, by rfl⟩ : syracuseStep 2894693 = 542755) (by norm_num)
theorem B1929795 : Blo 1929435 1929795 := bstep (se 1 (by rfl) ⟨1447346, by rfl⟩ : syracuseStep 1929795 = 2894693) B2894693
theorem B3663605 : Blo 1929435 3663605 := bbase (se 5 (by rfl) ⟨171731, by rfl⟩ : syracuseStep 3663605 = 343463) (by norm_num)
theorem B2442403 : Blo 1929435 2442403 := bstep (se 1 (by rfl) ⟨1831802, by rfl⟩ : syracuseStep 2442403 = 3663605) B3663605
theorem B3256537 : Blo 1929435 3256537 := bstep (se 2 (by rfl) ⟨1221201, by rfl⟩ : syracuseStep 3256537 = 2442403) B2442403
theorem B4342049 : Blo 1929435 4342049 := bstep (se 2 (by rfl) ⟨1628268, by rfl⟩ : syracuseStep 4342049 = 3256537) B3256537
theorem B2894699 : Blo 1929435 2894699 := bstep (se 1 (by rfl) ⟨2171024, by rfl⟩ : syracuseStep 2894699 = 4342049) B4342049
theorem B1929799 : Blo 1929435 1929799 := bstep (se 1 (by rfl) ⟨1447349, by rfl⟩ : syracuseStep 1929799 = 2894699) B2894699
theorem B2171029 : Blo 1929435 2171029 := bbase (se 6 (by rfl) ⟨50883, by rfl⟩ : syracuseStep 2171029 = 101767) (by norm_num)
theorem B2894705 : Blo 1929435 2894705 := bstep (se 2 (by rfl) ⟨1085514, by rfl⟩ : syracuseStep 2894705 = 2171029) B2171029
theorem B1929803 : Blo 1929435 1929803 := bstep (se 1 (by rfl) ⟨1447352, by rfl⟩ : syracuseStep 1929803 = 2894705) B2894705
theorem B2442413 : Blo 1929435 2442413 := bbase (se 3 (by rfl) ⟨457952, by rfl⟩ : syracuseStep 2442413 = 915905) (by norm_num)
theorem B6513101 : Blo 1929435 6513101 := bstep (se 3 (by rfl) ⟨1221206, by rfl⟩ : syracuseStep 6513101 = 2442413) B2442413
theorem B4342067 : Blo 1929435 4342067 := bstep (se 1 (by rfl) ⟨3256550, by rfl⟩ : syracuseStep 4342067 = 6513101) B6513101
theorem B2894711 : Blo 1929435 2894711 := bstep (se 1 (by rfl) ⟨2171033, by rfl⟩ : syracuseStep 2894711 = 4342067) B4342067
theorem B1929807 : Blo 1929435 1929807 := bstep (se 1 (by rfl) ⟨1447355, by rfl⟩ : syracuseStep 1929807 = 2894711) B2894711
theorem B2894717 : Blo 1929435 2894717 := bbase (se 3 (by rfl) ⟨542759, by rfl⟩ : syracuseStep 2894717 = 1085519) (by norm_num)
theorem B1929811 : Blo 1929435 1929811 := bstep (se 1 (by rfl) ⟨1447358, by rfl⟩ : syracuseStep 1929811 = 2894717) B2894717
theorem B4342085 : Blo 1929435 4342085 := bbase (se 4 (by rfl) ⟨407070, by rfl⟩ : syracuseStep 4342085 = 814141) (by norm_num)
theorem B2894723 : Blo 1929435 2894723 := bstep (se 1 (by rfl) ⟨2171042, by rfl⟩ : syracuseStep 2894723 = 4342085) B4342085
theorem B1929815 : Blo 1929435 1929815 := bstep (se 1 (by rfl) ⟨1447361, by rfl⟩ : syracuseStep 1929815 = 2894723) B2894723
theorem B4461389 : Blo 1929435 4461389 := bbase (se 3 (by rfl) ⟨836510, by rfl⟩ : syracuseStep 4461389 = 1673021) (by norm_num)
theorem B2974259 : Blo 1929435 2974259 := bstep (se 1 (by rfl) ⟨2230694, by rfl⟩ : syracuseStep 2974259 = 4461389) B4461389
theorem B7931357 : Blo 1929435 7931357 := bstep (se 3 (by rfl) ⟨1487129, by rfl⟩ : syracuseStep 7931357 = 2974259) B2974259
theorem B5287571 : Blo 1929435 5287571 := bstep (se 1 (by rfl) ⟨3965678, by rfl⟩ : syracuseStep 5287571 = 7931357) B7931357
theorem B3525047 : Blo 1929435 3525047 := bstep (se 1 (by rfl) ⟨2643785, by rfl⟩ : syracuseStep 3525047 = 5287571) B5287571
theorem B2350031 : Blo 1929435 2350031 := bstep (se 1 (by rfl) ⟨1762523, by rfl⟩ : syracuseStep 2350031 = 3525047) B3525047
theorem B6266749 : Blo 1929435 6266749 := bstep (se 3 (by rfl) ⟨1175015, by rfl⟩ : syracuseStep 6266749 = 2350031) B2350031
theorem B8355665 : Blo 1929435 8355665 := bstep (se 2 (by rfl) ⟨3133374, by rfl⟩ : syracuseStep 8355665 = 6266749) B6266749
theorem B5570443 : Blo 1929435 5570443 := bstep (se 1 (by rfl) ⟨4177832, by rfl⟩ : syracuseStep 5570443 = 8355665) B8355665
theorem B7427257 : Blo 1929435 7427257 := bstep (se 2 (by rfl) ⟨2785221, by rfl⟩ : syracuseStep 7427257 = 5570443) B5570443
theorem B158448149 : Blo 1929435 158448149 := bstep (se 6 (by rfl) ⟨3713628, by rfl⟩ : syracuseStep 158448149 = 7427257) B7427257
theorem B105632099 : Blo 1929435 105632099 := bstep (se 1 (by rfl) ⟨79224074, by rfl⟩ : syracuseStep 105632099 = 158448149) B158448149
theorem B70421399 : Blo 1929435 70421399 := bstep (se 1 (by rfl) ⟨52816049, by rfl⟩ : syracuseStep 70421399 = 105632099) B105632099
theorem B46947599 : Blo 1929435 46947599 := bstep (se 1 (by rfl) ⟨35210699, by rfl⟩ : syracuseStep 46947599 = 70421399) B70421399
theorem B31298399 : Blo 1929435 31298399 := bstep (se 1 (by rfl) ⟨23473799, by rfl⟩ : syracuseStep 31298399 = 46947599) B46947599
theorem B20865599 : Blo 1929435 20865599 := bstep (se 1 (by rfl) ⟨15649199, by rfl⟩ : syracuseStep 20865599 = 31298399) B31298399
theorem B13910399 : Blo 1929435 13910399 := bstep (se 1 (by rfl) ⟨10432799, by rfl⟩ : syracuseStep 13910399 = 20865599) B20865599
theorem B9273599 : Blo 1929435 9273599 := bstep (se 1 (by rfl) ⟨6955199, by rfl⟩ : syracuseStep 9273599 = 13910399) B13910399
theorem B6182399 : Blo 1929435 6182399 := bstep (se 1 (by rfl) ⟨4636799, by rfl⟩ : syracuseStep 6182399 = 9273599) B9273599
theorem B4121599 : Blo 1929435 4121599 := bstep (se 1 (by rfl) ⟨3091199, by rfl⟩ : syracuseStep 4121599 = 6182399) B6182399
theorem B5495465 : Blo 1929435 5495465 := bstep (se 2 (by rfl) ⟨2060799, by rfl⟩ : syracuseStep 5495465 = 4121599) B4121599
theorem B3663643 : Blo 1929435 3663643 := bstep (se 1 (by rfl) ⟨2747732, by rfl⟩ : syracuseStep 3663643 = 5495465) B5495465
theorem B4884857 : Blo 1929435 4884857 := bstep (se 2 (by rfl) ⟨1831821, by rfl⟩ : syracuseStep 4884857 = 3663643) B3663643
theorem B3256571 : Blo 1929435 3256571 := bstep (se 1 (by rfl) ⟨2442428, by rfl⟩ : syracuseStep 3256571 = 4884857) B4884857
theorem B2171047 : Blo 1929435 2171047 := bstep (se 1 (by rfl) ⟨1628285, by rfl⟩ : syracuseStep 2171047 = 3256571) B3256571
theorem B2894729 : Blo 1929435 2894729 := bstep (se 2 (by rfl) ⟨1085523, by rfl⟩ : syracuseStep 2894729 = 2171047) B2171047
theorem B1929819 : Blo 1929435 1929819 := bstep (se 1 (by rfl) ⟨1447364, by rfl⟩ : syracuseStep 1929819 = 2894729) B2894729
theorem B9769733 : Blo 1929435 9769733 := bbase (se 4 (by rfl) ⟨915912, by rfl⟩ : syracuseStep 9769733 = 1831825) (by norm_num)
theorem B6513155 : Blo 1929435 6513155 := bstep (se 1 (by rfl) ⟨4884866, by rfl⟩ : syracuseStep 6513155 = 9769733) B9769733
theorem B4342103 : Blo 1929435 4342103 := bstep (se 1 (by rfl) ⟨3256577, by rfl⟩ : syracuseStep 4342103 = 6513155) B6513155
theorem B2894735 : Blo 1929435 2894735 := bstep (se 1 (by rfl) ⟨2171051, by rfl⟩ : syracuseStep 2894735 = 4342103) B4342103
theorem B1929823 : Blo 1929435 1929823 := bstep (se 1 (by rfl) ⟨1447367, by rfl⟩ : syracuseStep 1929823 = 2894735) B2894735
theorem B2894741 : Blo 1929435 2894741 := bbase (se 6 (by rfl) ⟨67845, by rfl⟩ : syracuseStep 2894741 = 135691) (by norm_num)
theorem B1929827 : Blo 1929435 1929827 := bstep (se 1 (by rfl) ⟨1447370, by rfl⟩ : syracuseStep 1929827 = 2894741) B2894741
theorem B10990997 : Blo 1929435 10990997 := bbase (se 6 (by rfl) ⟨257601, by rfl⟩ : syracuseStep 10990997 = 515203) (by norm_num)
theorem B7327331 : Blo 1929435 7327331 := bstep (se 1 (by rfl) ⟨5495498, by rfl⟩ : syracuseStep 7327331 = 10990997) B10990997
theorem B4884887 : Blo 1929435 4884887 := bstep (se 1 (by rfl) ⟨3663665, by rfl⟩ : syracuseStep 4884887 = 7327331) B7327331
theorem B3256591 : Blo 1929435 3256591 := bstep (se 1 (by rfl) ⟨2442443, by rfl⟩ : syracuseStep 3256591 = 4884887) B4884887
theorem B4342121 : Blo 1929435 4342121 := bstep (se 2 (by rfl) ⟨1628295, by rfl⟩ : syracuseStep 4342121 = 3256591) B3256591
theorem B2894747 : Blo 1929435 2894747 := bstep (se 1 (by rfl) ⟨2171060, by rfl⟩ : syracuseStep 2894747 = 4342121) B4342121
theorem B1929831 : Blo 1929435 1929831 := bstep (se 1 (by rfl) ⟨1447373, by rfl⟩ : syracuseStep 1929831 = 2894747) B2894747
theorem B2171065 : Blo 1929435 2171065 := bbase (se 2 (by rfl) ⟨814149, by rfl⟩ : syracuseStep 2171065 = 1628299) (by norm_num)
theorem B2894753 : Blo 1929435 2894753 := bstep (se 2 (by rfl) ⟨1085532, by rfl⟩ : syracuseStep 2894753 = 2171065) B2171065
theorem B1929835 : Blo 1929435 1929835 := bstep (se 1 (by rfl) ⟨1447376, by rfl⟩ : syracuseStep 1929835 = 2894753) B2894753
theorem B8922869 : Blo 1929435 8922869 := bbase (se 5 (by rfl) ⟨418259, by rfl⟩ : syracuseStep 8922869 = 836519) (by norm_num)
theorem B5948579 : Blo 1929435 5948579 := bstep (se 1 (by rfl) ⟨4461434, by rfl⟩ : syracuseStep 5948579 = 8922869) B8922869
theorem B15862877 : Blo 1929435 15862877 := bstep (se 3 (by rfl) ⟨2974289, by rfl⟩ : syracuseStep 15862877 = 5948579) B5948579
theorem B10575251 : Blo 1929435 10575251 := bstep (se 1 (by rfl) ⟨7931438, by rfl⟩ : syracuseStep 10575251 = 15862877) B15862877
theorem B7050167 : Blo 1929435 7050167 := bstep (se 1 (by rfl) ⟨5287625, by rfl⟩ : syracuseStep 7050167 = 10575251) B10575251
theorem B4700111 : Blo 1929435 4700111 := bstep (se 1 (by rfl) ⟨3525083, by rfl⟩ : syracuseStep 4700111 = 7050167) B7050167
theorem B12533629 : Blo 1929435 12533629 := bstep (se 3 (by rfl) ⟨2350055, by rfl⟩ : syracuseStep 12533629 = 4700111) B4700111
theorem B16711505 : Blo 1929435 16711505 := bstep (se 2 (by rfl) ⟨6266814, by rfl⟩ : syracuseStep 16711505 = 12533629) B12533629
theorem B11141003 : Blo 1929435 11141003 := bstep (se 1 (by rfl) ⟨8355752, by rfl⟩ : syracuseStep 11141003 = 16711505) B16711505
theorem B7427335 : Blo 1929435 7427335 := bstep (se 1 (by rfl) ⟨5570501, by rfl⟩ : syracuseStep 7427335 = 11141003) B11141003
theorem B9903113 : Blo 1929435 9903113 := bstep (se 2 (by rfl) ⟨3713667, by rfl⟩ : syracuseStep 9903113 = 7427335) B7427335
theorem B6602075 : Blo 1929435 6602075 := bstep (se 1 (by rfl) ⟨4951556, by rfl⟩ : syracuseStep 6602075 = 9903113) B9903113
theorem B4401383 : Blo 1929435 4401383 := bstep (se 1 (by rfl) ⟨3301037, by rfl⟩ : syracuseStep 4401383 = 6602075) B6602075
theorem B11737021 : Blo 1929435 11737021 := bstep (se 3 (by rfl) ⟨2200691, by rfl⟩ : syracuseStep 11737021 = 4401383) B4401383
theorem B15649361 : Blo 1929435 15649361 := bstep (se 2 (by rfl) ⟨5868510, by rfl⟩ : syracuseStep 15649361 = 11737021) B11737021
theorem B10432907 : Blo 1929435 10432907 := bstep (se 1 (by rfl) ⟨7824680, by rfl⟩ : syracuseStep 10432907 = 15649361) B15649361
theorem B6955271 : Blo 1929435 6955271 := bstep (se 1 (by rfl) ⟨5216453, by rfl⟩ : syracuseStep 6955271 = 10432907) B10432907
theorem B4636847 : Blo 1929435 4636847 := bstep (se 1 (by rfl) ⟨3477635, by rfl⟩ : syracuseStep 4636847 = 6955271) B6955271
theorem B3091231 : Blo 1929435 3091231 := bstep (se 1 (by rfl) ⟨2318423, by rfl⟩ : syracuseStep 3091231 = 4636847) B4636847
theorem B4121641 : Blo 1929435 4121641 := bstep (se 2 (by rfl) ⟨1545615, by rfl⟩ : syracuseStep 4121641 = 3091231) B3091231
theorem B5495521 : Blo 1929435 5495521 := bstep (se 2 (by rfl) ⟨2060820, by rfl⟩ : syracuseStep 5495521 = 4121641) B4121641
theorem B7327361 : Blo 1929435 7327361 := bstep (se 2 (by rfl) ⟨2747760, by rfl⟩ : syracuseStep 7327361 = 5495521) B5495521
theorem B4884907 : Blo 1929435 4884907 := bstep (se 1 (by rfl) ⟨3663680, by rfl⟩ : syracuseStep 4884907 = 7327361) B7327361
theorem B6513209 : Blo 1929435 6513209 := bstep (se 2 (by rfl) ⟨2442453, by rfl⟩ : syracuseStep 6513209 = 4884907) B4884907
theorem B4342139 : Blo 1929435 4342139 := bstep (se 1 (by rfl) ⟨3256604, by rfl⟩ : syracuseStep 4342139 = 6513209) B6513209
theorem B2894759 : Blo 1929435 2894759 := bstep (se 1 (by rfl) ⟨2171069, by rfl⟩ : syracuseStep 2894759 = 4342139) B4342139
theorem B1929839 : Blo 1929435 1929839 := bstep (se 1 (by rfl) ⟨1447379, by rfl⟩ : syracuseStep 1929839 = 2894759) B2894759
theorem B2894765 : Blo 1929435 2894765 := bbase (se 3 (by rfl) ⟨542768, by rfl⟩ : syracuseStep 2894765 = 1085537) (by norm_num)
theorem B1929843 : Blo 1929435 1929843 := bstep (se 1 (by rfl) ⟨1447382, by rfl⟩ : syracuseStep 1929843 = 2894765) B2894765
theorem B4342157 : Blo 1929435 4342157 := bbase (se 3 (by rfl) ⟨814154, by rfl⟩ : syracuseStep 4342157 = 1628309) (by norm_num)
theorem B2894771 : Blo 1929435 2894771 := bstep (se 1 (by rfl) ⟨2171078, by rfl⟩ : syracuseStep 2894771 = 4342157) B4342157
theorem B1929847 : Blo 1929435 1929847 := bstep (se 1 (by rfl) ⟨1447385, by rfl⟩ : syracuseStep 1929847 = 2894771) B2894771
theorem B2442469 : Blo 1929435 2442469 := bbase (se 4 (by rfl) ⟨228981, by rfl⟩ : syracuseStep 2442469 = 457963) (by norm_num)
theorem B3256625 : Blo 1929435 3256625 := bstep (se 2 (by rfl) ⟨1221234, by rfl⟩ : syracuseStep 3256625 = 2442469) B2442469
theorem B2171083 : Blo 1929435 2171083 := bstep (se 1 (by rfl) ⟨1628312, by rfl⟩ : syracuseStep 2171083 = 3256625) B3256625
theorem B2894777 : Blo 1929435 2894777 := bstep (se 2 (by rfl) ⟨1085541, by rfl⟩ : syracuseStep 2894777 = 2171083) B2171083
theorem B1929851 : Blo 1929435 1929851 := bstep (se 1 (by rfl) ⟨1447388, by rfl⟩ : syracuseStep 1929851 = 2894777) B2894777
theorem B2009929 : Blo 1929435 2009929 := bbase (se 2 (by rfl) ⟨753723, by rfl⟩ : syracuseStep 2009929 = 1507447) (by norm_num)
theorem B2679905 : Blo 1929435 2679905 := bstep (se 2 (by rfl) ⟨1004964, by rfl⟩ : syracuseStep 2679905 = 2009929) B2009929
theorem B7146413 : Blo 1929435 7146413 := bstep (se 3 (by rfl) ⟨1339952, by rfl⟩ : syracuseStep 7146413 = 2679905) B2679905
theorem B4764275 : Blo 1929435 4764275 := bstep (se 1 (by rfl) ⟨3573206, by rfl⟩ : syracuseStep 4764275 = 7146413) B7146413
theorem B3176183 : Blo 1929435 3176183 := bstep (se 1 (by rfl) ⟨2382137, by rfl⟩ : syracuseStep 3176183 = 4764275) B4764275
theorem B8469821 : Blo 1929435 8469821 := bstep (se 3 (by rfl) ⟨1588091, by rfl⟩ : syracuseStep 8469821 = 3176183) B3176183
theorem B5646547 : Blo 1929435 5646547 := bstep (se 1 (by rfl) ⟨4234910, by rfl⟩ : syracuseStep 5646547 = 8469821) B8469821
theorem B7528729 : Blo 1929435 7528729 := bstep (se 2 (by rfl) ⟨2823273, by rfl⟩ : syracuseStep 7528729 = 5646547) B5646547
theorem B10038305 : Blo 1929435 10038305 := bstep (se 2 (by rfl) ⟨3764364, by rfl⟩ : syracuseStep 10038305 = 7528729) B7528729
theorem B6692203 : Blo 1929435 6692203 := bstep (se 1 (by rfl) ⟨5019152, by rfl⟩ : syracuseStep 6692203 = 10038305) B10038305
theorem B35691749 : Blo 1929435 35691749 := bstep (se 4 (by rfl) ⟨3346101, by rfl⟩ : syracuseStep 35691749 = 6692203) B6692203
theorem B23794499 : Blo 1929435 23794499 := bstep (se 1 (by rfl) ⟨17845874, by rfl⟩ : syracuseStep 23794499 = 35691749) B35691749
theorem B63451997 : Blo 1929435 63451997 := bstep (se 3 (by rfl) ⟨11897249, by rfl⟩ : syracuseStep 63451997 = 23794499) B23794499
theorem B42301331 : Blo 1929435 42301331 := bstep (se 1 (by rfl) ⟨31725998, by rfl⟩ : syracuseStep 42301331 = 63451997) B63451997
theorem B28200887 : Blo 1929435 28200887 := bstep (se 1 (by rfl) ⟨21150665, by rfl⟩ : syracuseStep 28200887 = 42301331) B42301331
theorem B18800591 : Blo 1929435 18800591 := bstep (se 1 (by rfl) ⟨14100443, by rfl⟩ : syracuseStep 18800591 = 28200887) B28200887
theorem B50134909 : Blo 1929435 50134909 := bstep (se 3 (by rfl) ⟨9400295, by rfl⟩ : syracuseStep 50134909 = 18800591) B18800591
theorem B66846545 : Blo 1929435 66846545 := bstep (se 2 (by rfl) ⟨25067454, by rfl⟩ : syracuseStep 66846545 = 50134909) B50134909
theorem B44564363 : Blo 1929435 44564363 := bstep (se 1 (by rfl) ⟨33423272, by rfl⟩ : syracuseStep 44564363 = 66846545) B66846545
theorem B29709575 : Blo 1929435 29709575 := bstep (se 1 (by rfl) ⟨22282181, by rfl⟩ : syracuseStep 29709575 = 44564363) B44564363
theorem B19806383 : Blo 1929435 19806383 := bstep (se 1 (by rfl) ⟨14854787, by rfl⟩ : syracuseStep 19806383 = 29709575) B29709575
theorem B13204255 : Blo 1929435 13204255 := bstep (se 1 (by rfl) ⟨9903191, by rfl⟩ : syracuseStep 13204255 = 19806383) B19806383
theorem B17605673 : Blo 1929435 17605673 := bstep (se 2 (by rfl) ⟨6602127, by rfl⟩ : syracuseStep 17605673 = 13204255) B13204255
theorem B11737115 : Blo 1929435 11737115 := bstep (se 1 (by rfl) ⟨8802836, by rfl⟩ : syracuseStep 11737115 = 17605673) B17605673
theorem B7824743 : Blo 1929435 7824743 := bstep (se 1 (by rfl) ⟨5868557, by rfl⟩ : syracuseStep 7824743 = 11737115) B11737115
theorem B5216495 : Blo 1929435 5216495 := bstep (se 1 (by rfl) ⟨3912371, by rfl⟩ : syracuseStep 5216495 = 7824743) B7824743
theorem B13910653 : Blo 1929435 13910653 := bstep (se 3 (by rfl) ⟨2608247, by rfl⟩ : syracuseStep 13910653 = 5216495) B5216495
theorem B18547537 : Blo 1929435 18547537 := bstep (se 2 (by rfl) ⟨6955326, by rfl⟩ : syracuseStep 18547537 = 13910653) B13910653
theorem B24730049 : Blo 1929435 24730049 := bstep (se 2 (by rfl) ⟨9273768, by rfl⟩ : syracuseStep 24730049 = 18547537) B18547537
theorem B16486699 : Blo 1929435 16486699 := bstep (se 1 (by rfl) ⟨12365024, by rfl⟩ : syracuseStep 16486699 = 24730049) B24730049
theorem B21982265 : Blo 1929435 21982265 := bstep (se 2 (by rfl) ⟨8243349, by rfl⟩ : syracuseStep 21982265 = 16486699) B16486699
theorem B14654843 : Blo 1929435 14654843 := bstep (se 1 (by rfl) ⟨10991132, by rfl⟩ : syracuseStep 14654843 = 21982265) B21982265
theorem B9769895 : Blo 1929435 9769895 := bstep (se 1 (by rfl) ⟨7327421, by rfl⟩ : syracuseStep 9769895 = 14654843) B14654843
theorem B6513263 : Blo 1929435 6513263 := bstep (se 1 (by rfl) ⟨4884947, by rfl⟩ : syracuseStep 6513263 = 9769895) B9769895
theorem B4342175 : Blo 1929435 4342175 := bstep (se 1 (by rfl) ⟨3256631, by rfl⟩ : syracuseStep 4342175 = 6513263) B6513263
theorem B2894783 : Blo 1929435 2894783 := bstep (se 1 (by rfl) ⟨2171087, by rfl⟩ : syracuseStep 2894783 = 4342175) B4342175
theorem B1929855 : Blo 1929435 1929855 := bstep (se 1 (by rfl) ⟨1447391, by rfl⟩ : syracuseStep 1929855 = 2894783) B2894783
theorem B2894789 : Blo 1929435 2894789 := bbase (se 4 (by rfl) ⟨271386, by rfl⟩ : syracuseStep 2894789 = 542773) (by norm_num)
theorem B1929859 : Blo 1929435 1929859 := bstep (se 1 (by rfl) ⟨1447394, by rfl⟩ : syracuseStep 1929859 = 2894789) B2894789
theorem B3256645 : Blo 1929435 3256645 := bbase (se 4 (by rfl) ⟨305310, by rfl⟩ : syracuseStep 3256645 = 610621) (by norm_num)
theorem B4342193 : Blo 1929435 4342193 := bstep (se 2 (by rfl) ⟨1628322, by rfl⟩ : syracuseStep 4342193 = 3256645) B3256645
theorem B2894795 : Blo 1929435 2894795 := bstep (se 1 (by rfl) ⟨2171096, by rfl⟩ : syracuseStep 2894795 = 4342193) B4342193
theorem B1929863 : Blo 1929435 1929863 := bstep (se 1 (by rfl) ⟨1447397, by rfl⟩ : syracuseStep 1929863 = 2894795) B2894795
theorem B2171101 : Blo 1929435 2171101 := bbase (se 3 (by rfl) ⟨407081, by rfl⟩ : syracuseStep 2171101 = 814163) (by norm_num)
theorem B2894801 : Blo 1929435 2894801 := bstep (se 2 (by rfl) ⟨1085550, by rfl⟩ : syracuseStep 2894801 = 2171101) B2171101
theorem B1929867 : Blo 1929435 1929867 := bstep (se 1 (by rfl) ⟨1447400, by rfl⟩ : syracuseStep 1929867 = 2894801) B2894801
theorem B6513317 : Blo 1929435 6513317 := bbase (se 4 (by rfl) ⟨610623, by rfl⟩ : syracuseStep 6513317 = 1221247) (by norm_num)
theorem B4342211 : Blo 1929435 4342211 := bstep (se 1 (by rfl) ⟨3256658, by rfl⟩ : syracuseStep 4342211 = 6513317) B6513317
theorem B2894807 : Blo 1929435 2894807 := bstep (se 1 (by rfl) ⟨2171105, by rfl⟩ : syracuseStep 2894807 = 4342211) B4342211
theorem B1929871 : Blo 1929435 1929871 := bstep (se 1 (by rfl) ⟨1447403, by rfl⟩ : syracuseStep 1929871 = 2894807) B2894807
theorem B2894813 : Blo 1929435 2894813 := bbase (se 3 (by rfl) ⟨542777, by rfl⟩ : syracuseStep 2894813 = 1085555) (by norm_num)
theorem B1929875 : Blo 1929435 1929875 := bstep (se 1 (by rfl) ⟨1447406, by rfl⟩ : syracuseStep 1929875 = 2894813) B2894813
theorem B4342229 : Blo 1929435 4342229 := bbase (se 7 (by rfl) ⟨50885, by rfl⟩ : syracuseStep 4342229 = 101771) (by norm_num)
theorem B2894819 : Blo 1929435 2894819 := bstep (se 1 (by rfl) ⟨2171114, by rfl⟩ : syracuseStep 2894819 = 4342229) B4342229
theorem B1929879 : Blo 1929435 1929879 := bstep (se 1 (by rfl) ⟨1447409, by rfl⟩ : syracuseStep 1929879 = 2894819) B2894819
theorem B27821717 : Blo 1929435 27821717 := bbase (se 6 (by rfl) ⟨652071, by rfl⟩ : syracuseStep 27821717 = 1304143) (by norm_num)
theorem B18547811 : Blo 1929435 18547811 := bstep (se 1 (by rfl) ⟨13910858, by rfl⟩ : syracuseStep 18547811 = 27821717) B27821717
theorem B12365207 : Blo 1929435 12365207 := bstep (se 1 (by rfl) ⟨9273905, by rfl⟩ : syracuseStep 12365207 = 18547811) B18547811
theorem B8243471 : Blo 1929435 8243471 := bstep (se 1 (by rfl) ⟨6182603, by rfl⟩ : syracuseStep 8243471 = 12365207) B12365207
theorem B5495647 : Blo 1929435 5495647 := bstep (se 1 (by rfl) ⟨4121735, by rfl⟩ : syracuseStep 5495647 = 8243471) B8243471
theorem B7327529 : Blo 1929435 7327529 := bstep (se 2 (by rfl) ⟨2747823, by rfl⟩ : syracuseStep 7327529 = 5495647) B5495647
theorem B4885019 : Blo 1929435 4885019 := bstep (se 1 (by rfl) ⟨3663764, by rfl⟩ : syracuseStep 4885019 = 7327529) B7327529
theorem B3256679 : Blo 1929435 3256679 := bstep (se 1 (by rfl) ⟨2442509, by rfl⟩ : syracuseStep 3256679 = 4885019) B4885019
theorem B2171119 : Blo 1929435 2171119 := bstep (se 1 (by rfl) ⟨1628339, by rfl⟩ : syracuseStep 2171119 = 3256679) B3256679
theorem B2894825 : Blo 1929435 2894825 := bstep (se 2 (by rfl) ⟨1085559, by rfl⟩ : syracuseStep 2894825 = 2171119) B2171119
theorem B1929883 : Blo 1929435 1929883 := bstep (se 1 (by rfl) ⟨1447412, by rfl⟩ : syracuseStep 1929883 = 2894825) B2894825
theorem B3912437 : Blo 1929435 3912437 := bbase (se 5 (by rfl) ⟨183395, by rfl⟩ : syracuseStep 3912437 = 366791) (by norm_num)
theorem B2608291 : Blo 1929435 2608291 := bstep (se 1 (by rfl) ⟨1956218, by rfl⟩ : syracuseStep 2608291 = 3912437) B3912437
theorem B13910885 : Blo 1929435 13910885 := bstep (se 4 (by rfl) ⟨1304145, by rfl⟩ : syracuseStep 13910885 = 2608291) B2608291
theorem B9273923 : Blo 1929435 9273923 := bstep (se 1 (by rfl) ⟨6955442, by rfl⟩ : syracuseStep 9273923 = 13910885) B13910885
theorem B6182615 : Blo 1929435 6182615 := bstep (se 1 (by rfl) ⟨4636961, by rfl⟩ : syracuseStep 6182615 = 9273923) B9273923
theorem B16486973 : Blo 1929435 16486973 := bstep (se 3 (by rfl) ⟨3091307, by rfl⟩ : syracuseStep 16486973 = 6182615) B6182615
theorem B10991315 : Blo 1929435 10991315 := bstep (se 1 (by rfl) ⟨8243486, by rfl⟩ : syracuseStep 10991315 = 16486973) B16486973
theorem B7327543 : Blo 1929435 7327543 := bstep (se 1 (by rfl) ⟨5495657, by rfl⟩ : syracuseStep 7327543 = 10991315) B10991315
theorem B9770057 : Blo 1929435 9770057 := bstep (se 2 (by rfl) ⟨3663771, by rfl⟩ : syracuseStep 9770057 = 7327543) B7327543
theorem B6513371 : Blo 1929435 6513371 := bstep (se 1 (by rfl) ⟨4885028, by rfl⟩ : syracuseStep 6513371 = 9770057) B9770057
theorem B4342247 : Blo 1929435 4342247 := bstep (se 1 (by rfl) ⟨3256685, by rfl⟩ : syracuseStep 4342247 = 6513371) B6513371
theorem B2894831 : Blo 1929435 2894831 := bstep (se 1 (by rfl) ⟨2171123, by rfl⟩ : syracuseStep 2894831 = 4342247) B4342247
theorem B1929887 : Blo 1929435 1929887 := bstep (se 1 (by rfl) ⟨1447415, by rfl⟩ : syracuseStep 1929887 = 2894831) B2894831
theorem B2894837 : Blo 1929435 2894837 := bbase (se 5 (by rfl) ⟨135695, by rfl⟩ : syracuseStep 2894837 = 271391) (by norm_num)
theorem B1929891 : Blo 1929435 1929891 := bstep (se 1 (by rfl) ⟨1447418, by rfl⟩ : syracuseStep 1929891 = 2894837) B2894837
theorem B2785333 : Blo 1929435 2785333 := bbase (se 5 (by rfl) ⟨130562, by rfl⟩ : syracuseStep 2785333 = 261125) (by norm_num)
theorem B3713777 : Blo 1929435 3713777 := bstep (se 2 (by rfl) ⟨1392666, by rfl⟩ : syracuseStep 3713777 = 2785333) B2785333
theorem B2475851 : Blo 1929435 2475851 := bstep (se 1 (by rfl) ⟨1856888, by rfl⟩ : syracuseStep 2475851 = 3713777) B3713777
theorem B6602269 : Blo 1929435 6602269 := bstep (se 3 (by rfl) ⟨1237925, by rfl⟩ : syracuseStep 6602269 = 2475851) B2475851
theorem B8803025 : Blo 1929435 8803025 := bstep (se 2 (by rfl) ⟨3301134, by rfl⟩ : syracuseStep 8803025 = 6602269) B6602269
theorem B5868683 : Blo 1929435 5868683 := bstep (se 1 (by rfl) ⟨4401512, by rfl⟩ : syracuseStep 5868683 = 8803025) B8803025
theorem B3912455 : Blo 1929435 3912455 := bstep (se 1 (by rfl) ⟨2934341, by rfl⟩ : syracuseStep 3912455 = 5868683) B5868683
theorem B2608303 : Blo 1929435 2608303 := bstep (se 1 (by rfl) ⟨1956227, by rfl⟩ : syracuseStep 2608303 = 3912455) B3912455
theorem B3477737 : Blo 1929435 3477737 := bstep (se 2 (by rfl) ⟨1304151, by rfl⟩ : syracuseStep 3477737 = 2608303) B2608303
theorem B2318491 : Blo 1929435 2318491 := bstep (se 1 (by rfl) ⟨1738868, by rfl⟩ : syracuseStep 2318491 = 3477737) B3477737
theorem B3091321 : Blo 1929435 3091321 := bstep (se 2 (by rfl) ⟨1159245, by rfl⟩ : syracuseStep 3091321 = 2318491) B2318491
theorem B4121761 : Blo 1929435 4121761 := bstep (se 2 (by rfl) ⟨1545660, by rfl⟩ : syracuseStep 4121761 = 3091321) B3091321
theorem B5495681 : Blo 1929435 5495681 := bstep (se 2 (by rfl) ⟨2060880, by rfl⟩ : syracuseStep 5495681 = 4121761) B4121761
theorem B3663787 : Blo 1929435 3663787 := bstep (se 1 (by rfl) ⟨2747840, by rfl⟩ : syracuseStep 3663787 = 5495681) B5495681
theorem B4885049 : Blo 1929435 4885049 := bstep (se 2 (by rfl) ⟨1831893, by rfl⟩ : syracuseStep 4885049 = 3663787) B3663787
theorem B3256699 : Blo 1929435 3256699 := bstep (se 1 (by rfl) ⟨2442524, by rfl⟩ : syracuseStep 3256699 = 4885049) B4885049
theorem B4342265 : Blo 1929435 4342265 := bstep (se 2 (by rfl) ⟨1628349, by rfl⟩ : syracuseStep 4342265 = 3256699) B3256699
theorem B2894843 : Blo 1929435 2894843 := bstep (se 1 (by rfl) ⟨2171132, by rfl⟩ : syracuseStep 2894843 = 4342265) B4342265
theorem B1929895 : Blo 1929435 1929895 := bstep (se 1 (by rfl) ⟨1447421, by rfl⟩ : syracuseStep 1929895 = 2894843) B2894843
theorem B2171137 : Blo 1929435 2171137 := bbase (se 2 (by rfl) ⟨814176, by rfl⟩ : syracuseStep 2171137 = 1628353) (by norm_num)
theorem B2894849 : Blo 1929435 2894849 := bstep (se 2 (by rfl) ⟨1085568, by rfl⟩ : syracuseStep 2894849 = 2171137) B2171137
theorem B1929899 : Blo 1929435 1929899 := bstep (se 1 (by rfl) ⟨1447424, by rfl⟩ : syracuseStep 1929899 = 2894849) B2894849
theorem B4885069 : Blo 1929435 4885069 := bbase (se 3 (by rfl) ⟨915950, by rfl⟩ : syracuseStep 4885069 = 1831901) (by norm_num)
theorem B6513425 : Blo 1929435 6513425 := bstep (se 2 (by rfl) ⟨2442534, by rfl⟩ : syracuseStep 6513425 = 4885069) B4885069
theorem B4342283 : Blo 1929435 4342283 := bstep (se 1 (by rfl) ⟨3256712, by rfl⟩ : syracuseStep 4342283 = 6513425) B6513425
theorem B2894855 : Blo 1929435 2894855 := bstep (se 1 (by rfl) ⟨2171141, by rfl⟩ : syracuseStep 2894855 = 4342283) B4342283
theorem B1929903 : Blo 1929435 1929903 := bstep (se 1 (by rfl) ⟨1447427, by rfl⟩ : syracuseStep 1929903 = 2894855) B2894855
theorem B2894861 : Blo 1929435 2894861 := bbase (se 3 (by rfl) ⟨542786, by rfl⟩ : syracuseStep 2894861 = 1085573) (by norm_num)
theorem B1929907 : Blo 1929435 1929907 := bstep (se 1 (by rfl) ⟨1447430, by rfl⟩ : syracuseStep 1929907 = 2894861) B2894861
theorem B4342301 : Blo 1929435 4342301 := bbase (se 3 (by rfl) ⟨814181, by rfl⟩ : syracuseStep 4342301 = 1628363) (by norm_num)
theorem B2894867 : Blo 1929435 2894867 := bstep (se 1 (by rfl) ⟨2171150, by rfl⟩ : syracuseStep 2894867 = 4342301) B4342301
theorem B1929911 : Blo 1929435 1929911 := bstep (se 1 (by rfl) ⟨1447433, by rfl⟩ : syracuseStep 1929911 = 2894867) B2894867
theorem B3256733 : Blo 1929435 3256733 := bbase (se 3 (by rfl) ⟨610637, by rfl⟩ : syracuseStep 3256733 = 1221275) (by norm_num)
theorem B2171155 : Blo 1929435 2171155 := bstep (se 1 (by rfl) ⟨1628366, by rfl⟩ : syracuseStep 2171155 = 3256733) B3256733
theorem B2894873 : Blo 1929435 2894873 := bstep (se 2 (by rfl) ⟨1085577, by rfl⟩ : syracuseStep 2894873 = 2171155) B2171155
theorem B1929915 : Blo 1929435 1929915 := bstep (se 1 (by rfl) ⟨1447436, by rfl⟩ : syracuseStep 1929915 = 2894873) B2894873
theorem B15650005 : Blo 1929435 15650005 := bbase (se 7 (by rfl) ⟨183398, by rfl⟩ : syracuseStep 15650005 = 366797) (by norm_num)
theorem B20866673 : Blo 1929435 20866673 := bstep (se 2 (by rfl) ⟨7825002, by rfl⟩ : syracuseStep 20866673 = 15650005) B15650005
theorem B13911115 : Blo 1929435 13911115 := bstep (se 1 (by rfl) ⟨10433336, by rfl⟩ : syracuseStep 13911115 = 20866673) B20866673
theorem B18548153 : Blo 1929435 18548153 := bstep (se 2 (by rfl) ⟨6955557, by rfl⟩ : syracuseStep 18548153 = 13911115) B13911115
theorem B12365435 : Blo 1929435 12365435 := bstep (se 1 (by rfl) ⟨9274076, by rfl⟩ : syracuseStep 12365435 = 18548153) B18548153
theorem B8243623 : Blo 1929435 8243623 := bstep (se 1 (by rfl) ⟨6182717, by rfl⟩ : syracuseStep 8243623 = 12365435) B12365435
theorem B10991497 : Blo 1929435 10991497 := bstep (se 2 (by rfl) ⟨4121811, by rfl⟩ : syracuseStep 10991497 = 8243623) B8243623
theorem B14655329 : Blo 1929435 14655329 := bstep (se 2 (by rfl) ⟨5495748, by rfl⟩ : syracuseStep 14655329 = 10991497) B10991497
theorem B9770219 : Blo 1929435 9770219 := bstep (se 1 (by rfl) ⟨7327664, by rfl⟩ : syracuseStep 9770219 = 14655329) B14655329
theorem B6513479 : Blo 1929435 6513479 := bstep (se 1 (by rfl) ⟨4885109, by rfl⟩ : syracuseStep 6513479 = 9770219) B9770219
theorem B4342319 : Blo 1929435 4342319 := bstep (se 1 (by rfl) ⟨3256739, by rfl⟩ : syracuseStep 4342319 = 6513479) B6513479
theorem B2894879 : Blo 1929435 2894879 := bstep (se 1 (by rfl) ⟨2171159, by rfl⟩ : syracuseStep 2894879 = 4342319) B4342319
theorem B1929919 : Blo 1929435 1929919 := bstep (se 1 (by rfl) ⟨1447439, by rfl⟩ : syracuseStep 1929919 = 2894879) B2894879
theorem B2894885 : Blo 1929435 2894885 := bbase (se 4 (by rfl) ⟨271395, by rfl⟩ : syracuseStep 2894885 = 542791) (by norm_num)
theorem B1929923 : Blo 1929435 1929923 := bstep (se 1 (by rfl) ⟨1447442, by rfl⟩ : syracuseStep 1929923 = 2894885) B2894885
theorem B2442565 : Blo 1929435 2442565 := bbase (se 4 (by rfl) ⟨228990, by rfl⟩ : syracuseStep 2442565 = 457981) (by norm_num)
theorem B3256753 : Blo 1929435 3256753 := bstep (se 2 (by rfl) ⟨1221282, by rfl⟩ : syracuseStep 3256753 = 2442565) B2442565
theorem B4342337 : Blo 1929435 4342337 := bstep (se 2 (by rfl) ⟨1628376, by rfl⟩ : syracuseStep 4342337 = 3256753) B3256753
theorem B2894891 : Blo 1929435 2894891 := bstep (se 1 (by rfl) ⟨2171168, by rfl⟩ : syracuseStep 2894891 = 4342337) B4342337
theorem B1929927 : Blo 1929435 1929927 := bstep (se 1 (by rfl) ⟨1447445, by rfl⟩ : syracuseStep 1929927 = 2894891) B2894891
theorem B2171173 : Blo 1929435 2171173 := bbase (se 4 (by rfl) ⟨203547, by rfl⟩ : syracuseStep 2171173 = 407095) (by norm_num)
theorem B2894897 : Blo 1929435 2894897 := bstep (se 2 (by rfl) ⟨1085586, by rfl⟩ : syracuseStep 2894897 = 2171173) B2171173
theorem B1929931 : Blo 1929435 1929931 := bstep (se 1 (by rfl) ⟨1447448, by rfl⟩ : syracuseStep 1929931 = 2894897) B2894897
theorem B2608357 : Blo 1929435 2608357 := bbase (se 4 (by rfl) ⟨244533, by rfl⟩ : syracuseStep 2608357 = 489067) (by norm_num)
theorem B3477809 : Blo 1929435 3477809 := bstep (se 2 (by rfl) ⟨1304178, by rfl⟩ : syracuseStep 3477809 = 2608357) B2608357
theorem B2318539 : Blo 1929435 2318539 := bstep (se 1 (by rfl) ⟨1738904, by rfl⟩ : syracuseStep 2318539 = 3477809) B3477809
theorem B3091385 : Blo 1929435 3091385 := bstep (se 2 (by rfl) ⟨1159269, by rfl⟩ : syracuseStep 3091385 = 2318539) B2318539
theorem B8243693 : Blo 1929435 8243693 := bstep (se 3 (by rfl) ⟨1545692, by rfl⟩ : syracuseStep 8243693 = 3091385) B3091385
theorem B5495795 : Blo 1929435 5495795 := bstep (se 1 (by rfl) ⟨4121846, by rfl⟩ : syracuseStep 5495795 = 8243693) B8243693
theorem B3663863 : Blo 1929435 3663863 := bstep (se 1 (by rfl) ⟨2747897, by rfl⟩ : syracuseStep 3663863 = 5495795) B5495795
theorem B2442575 : Blo 1929435 2442575 := bstep (se 1 (by rfl) ⟨1831931, by rfl⟩ : syracuseStep 2442575 = 3663863) B3663863
theorem B6513533 : Blo 1929435 6513533 := bstep (se 3 (by rfl) ⟨1221287, by rfl⟩ : syracuseStep 6513533 = 2442575) B2442575
theorem B4342355 : Blo 1929435 4342355 := bstep (se 1 (by rfl) ⟨3256766, by rfl⟩ : syracuseStep 4342355 = 6513533) B6513533
theorem B2894903 : Blo 1929435 2894903 := bstep (se 1 (by rfl) ⟨2171177, by rfl⟩ : syracuseStep 2894903 = 4342355) B4342355
theorem B1929935 : Blo 1929435 1929935 := bstep (se 1 (by rfl) ⟨1447451, by rfl⟩ : syracuseStep 1929935 = 2894903) B2894903
theorem B2894909 : Blo 1929435 2894909 := bbase (se 3 (by rfl) ⟨542795, by rfl⟩ : syracuseStep 2894909 = 1085591) (by norm_num)
theorem B1929939 : Blo 1929435 1929939 := bstep (se 1 (by rfl) ⟨1447454, by rfl⟩ : syracuseStep 1929939 = 2894909) B2894909
theorem B4342373 : Blo 1929435 4342373 := bbase (se 4 (by rfl) ⟨407097, by rfl⟩ : syracuseStep 4342373 = 814195) (by norm_num)
theorem B2894915 : Blo 1929435 2894915 := bstep (se 1 (by rfl) ⟨2171186, by rfl⟩ : syracuseStep 2894915 = 4342373) B4342373
theorem B1929943 : Blo 1929435 1929943 := bstep (se 1 (by rfl) ⟨1447457, by rfl⟩ : syracuseStep 1929943 = 2894915) B2894915
theorem B4885181 : Blo 1929435 4885181 := bbase (se 3 (by rfl) ⟨915971, by rfl⟩ : syracuseStep 4885181 = 1831943) (by norm_num)
theorem B3256787 : Blo 1929435 3256787 := bstep (se 1 (by rfl) ⟨2442590, by rfl⟩ : syracuseStep 3256787 = 4885181) B4885181
theorem B2171191 : Blo 1929435 2171191 := bstep (se 1 (by rfl) ⟨1628393, by rfl⟩ : syracuseStep 2171191 = 3256787) B3256787
theorem B2894921 : Blo 1929435 2894921 := bstep (se 2 (by rfl) ⟨1085595, by rfl⟩ : syracuseStep 2894921 = 2171191) B2171191
theorem B1929947 : Blo 1929435 1929947 := bstep (se 1 (by rfl) ⟨1447460, by rfl⟩ : syracuseStep 1929947 = 2894921) B2894921
theorem B3663893 : Blo 1929435 3663893 := bbase (se 6 (by rfl) ⟨85872, by rfl⟩ : syracuseStep 3663893 = 171745) (by norm_num)
theorem B9770381 : Blo 1929435 9770381 := bstep (se 3 (by rfl) ⟨1831946, by rfl⟩ : syracuseStep 9770381 = 3663893) B3663893
theorem B6513587 : Blo 1929435 6513587 := bstep (se 1 (by rfl) ⟨4885190, by rfl⟩ : syracuseStep 6513587 = 9770381) B9770381
theorem B4342391 : Blo 1929435 4342391 := bstep (se 1 (by rfl) ⟨3256793, by rfl⟩ : syracuseStep 4342391 = 6513587) B6513587
theorem B2894927 : Blo 1929435 2894927 := bstep (se 1 (by rfl) ⟨2171195, by rfl⟩ : syracuseStep 2894927 = 4342391) B4342391
theorem B1929951 : Blo 1929435 1929951 := bstep (se 1 (by rfl) ⟨1447463, by rfl⟩ : syracuseStep 1929951 = 2894927) B2894927
theorem B2894933 : Blo 1929435 2894933 := bbase (se 8 (by rfl) ⟨16962, by rfl⟩ : syracuseStep 2894933 = 33925) (by norm_num)
theorem B1929955 : Blo 1929435 1929955 := bstep (se 1 (by rfl) ⟨1447466, by rfl⟩ : syracuseStep 1929955 = 2894933) B2894933
theorem B6602485 : Blo 1929435 6602485 := bbase (se 5 (by rfl) ⟨309491, by rfl⟩ : syracuseStep 6602485 = 618983) (by norm_num)
theorem B8803313 : Blo 1929435 8803313 := bstep (se 2 (by rfl) ⟨3301242, by rfl⟩ : syracuseStep 8803313 = 6602485) B6602485
theorem B5868875 : Blo 1929435 5868875 := bstep (se 1 (by rfl) ⟨4401656, by rfl⟩ : syracuseStep 5868875 = 8803313) B8803313
theorem B15650333 : Blo 1929435 15650333 := bstep (se 3 (by rfl) ⟨2934437, by rfl⟩ : syracuseStep 15650333 = 5868875) B5868875
theorem B10433555 : Blo 1929435 10433555 := bstep (se 1 (by rfl) ⟨7825166, by rfl⟩ : syracuseStep 10433555 = 15650333) B15650333
theorem B6955703 : Blo 1929435 6955703 := bstep (se 1 (by rfl) ⟨5216777, by rfl⟩ : syracuseStep 6955703 = 10433555) B10433555
theorem B4637135 : Blo 1929435 4637135 := bstep (se 1 (by rfl) ⟨3477851, by rfl⟩ : syracuseStep 4637135 = 6955703) B6955703
theorem B12365693 : Blo 1929435 12365693 := bstep (se 3 (by rfl) ⟨2318567, by rfl⟩ : syracuseStep 12365693 = 4637135) B4637135
theorem B8243795 : Blo 1929435 8243795 := bstep (se 1 (by rfl) ⟨6182846, by rfl⟩ : syracuseStep 8243795 = 12365693) B12365693
theorem B5495863 : Blo 1929435 5495863 := bstep (se 1 (by rfl) ⟨4121897, by rfl⟩ : syracuseStep 5495863 = 8243795) B8243795
theorem B7327817 : Blo 1929435 7327817 := bstep (se 2 (by rfl) ⟨2747931, by rfl⟩ : syracuseStep 7327817 = 5495863) B5495863
theorem B4885211 : Blo 1929435 4885211 := bstep (se 1 (by rfl) ⟨3663908, by rfl⟩ : syracuseStep 4885211 = 7327817) B7327817
theorem B3256807 : Blo 1929435 3256807 := bstep (se 1 (by rfl) ⟨2442605, by rfl⟩ : syracuseStep 3256807 = 4885211) B4885211
theorem B4342409 : Blo 1929435 4342409 := bstep (se 2 (by rfl) ⟨1628403, by rfl⟩ : syracuseStep 4342409 = 3256807) B3256807
theorem B2894939 : Blo 1929435 2894939 := bstep (se 1 (by rfl) ⟨2171204, by rfl⟩ : syracuseStep 2894939 = 4342409) B4342409
theorem B1929959 : Blo 1929435 1929959 := bstep (se 1 (by rfl) ⟨1447469, by rfl⟩ : syracuseStep 1929959 = 2894939) B2894939
theorem B2171209 : Blo 1929435 2171209 := bbase (se 2 (by rfl) ⟨814203, by rfl⟩ : syracuseStep 2171209 = 1628407) (by norm_num)
theorem B2894945 : Blo 1929435 2894945 := bstep (se 2 (by rfl) ⟨1085604, by rfl⟩ : syracuseStep 2894945 = 2171209) B2171209
theorem B1929963 : Blo 1929435 1929963 := bstep (se 1 (by rfl) ⟨1447472, by rfl⟩ : syracuseStep 1929963 = 2894945) B2894945
theorem B2200837 : Blo 1929435 2200837 := bbase (se 4 (by rfl) ⟨206328, by rfl⟩ : syracuseStep 2200837 = 412657) (by norm_num)
theorem B2934449 : Blo 1929435 2934449 := bstep (se 2 (by rfl) ⟨1100418, by rfl⟩ : syracuseStep 2934449 = 2200837) B2200837
theorem B31300789 : Blo 1929435 31300789 := bstep (se 5 (by rfl) ⟨1467224, by rfl⟩ : syracuseStep 31300789 = 2934449) B2934449
theorem B41734385 : Blo 1929435 41734385 := bstep (se 2 (by rfl) ⟨15650394, by rfl⟩ : syracuseStep 41734385 = 31300789) B31300789
theorem B27822923 : Blo 1929435 27822923 := bstep (se 1 (by rfl) ⟨20867192, by rfl⟩ : syracuseStep 27822923 = 41734385) B41734385
theorem B18548615 : Blo 1929435 18548615 := bstep (se 1 (by rfl) ⟨13911461, by rfl⟩ : syracuseStep 18548615 = 27822923) B27822923
theorem B12365743 : Blo 1929435 12365743 := bstep (se 1 (by rfl) ⟨9274307, by rfl⟩ : syracuseStep 12365743 = 18548615) B18548615
theorem B16487657 : Blo 1929435 16487657 := bstep (se 2 (by rfl) ⟨6182871, by rfl⟩ : syracuseStep 16487657 = 12365743) B12365743
theorem B10991771 : Blo 1929435 10991771 := bstep (se 1 (by rfl) ⟨8243828, by rfl⟩ : syracuseStep 10991771 = 16487657) B16487657
theorem B7327847 : Blo 1929435 7327847 := bstep (se 1 (by rfl) ⟨5495885, by rfl⟩ : syracuseStep 7327847 = 10991771) B10991771
theorem B4885231 : Blo 1929435 4885231 := bstep (se 1 (by rfl) ⟨3663923, by rfl⟩ : syracuseStep 4885231 = 7327847) B7327847
theorem B6513641 : Blo 1929435 6513641 := bstep (se 2 (by rfl) ⟨2442615, by rfl⟩ : syracuseStep 6513641 = 4885231) B4885231
theorem B4342427 : Blo 1929435 4342427 := bstep (se 1 (by rfl) ⟨3256820, by rfl⟩ : syracuseStep 4342427 = 6513641) B6513641
theorem B2894951 : Blo 1929435 2894951 := bstep (se 1 (by rfl) ⟨2171213, by rfl⟩ : syracuseStep 2894951 = 4342427) B4342427
theorem B1929967 : Blo 1929435 1929967 := bstep (se 1 (by rfl) ⟨1447475, by rfl⟩ : syracuseStep 1929967 = 2894951) B2894951
theorem B2894957 : Blo 1929435 2894957 := bbase (se 3 (by rfl) ⟨542804, by rfl⟩ : syracuseStep 2894957 = 1085609) (by norm_num)
theorem B1929971 : Blo 1929435 1929971 := bstep (se 1 (by rfl) ⟨1447478, by rfl⟩ : syracuseStep 1929971 = 2894957) B2894957
theorem B4342445 : Blo 1929435 4342445 := bbase (se 3 (by rfl) ⟨814208, by rfl⟩ : syracuseStep 4342445 = 1628417) (by norm_num)
theorem B2894963 : Blo 1929435 2894963 := bstep (se 1 (by rfl) ⟨2171222, by rfl⟩ : syracuseStep 2894963 = 4342445) B4342445
theorem B1929975 : Blo 1929435 1929975 := bstep (se 1 (by rfl) ⟨1447481, by rfl⟩ : syracuseStep 1929975 = 2894963) B2894963
theorem B4121941 : Blo 1929435 4121941 := bbase (se 12 (by rfl) ⟨1509, by rfl⟩ : syracuseStep 4121941 = 3019) (by norm_num)
theorem B5495921 : Blo 1929435 5495921 := bstep (se 2 (by rfl) ⟨2060970, by rfl⟩ : syracuseStep 5495921 = 4121941) B4121941
theorem B3663947 : Blo 1929435 3663947 := bstep (se 1 (by rfl) ⟨2747960, by rfl⟩ : syracuseStep 3663947 = 5495921) B5495921
theorem B2442631 : Blo 1929435 2442631 := bstep (se 1 (by rfl) ⟨1831973, by rfl⟩ : syracuseStep 2442631 = 3663947) B3663947
theorem B3256841 : Blo 1929435 3256841 := bstep (se 2 (by rfl) ⟨1221315, by rfl⟩ : syracuseStep 3256841 = 2442631) B2442631
theorem B2171227 : Blo 1929435 2171227 := bstep (se 1 (by rfl) ⟨1628420, by rfl⟩ : syracuseStep 2171227 = 3256841) B3256841
theorem B2894969 : Blo 1929435 2894969 := bstep (se 2 (by rfl) ⟨1085613, by rfl⟩ : syracuseStep 2894969 = 2171227) B2171227
theorem B1929979 : Blo 1929435 1929979 := bstep (se 1 (by rfl) ⟨1447484, by rfl⟩ : syracuseStep 1929979 = 2894969) B2894969
theorem B2089093 : Blo 1929435 2089093 := bbase (se 4 (by rfl) ⟨195852, by rfl⟩ : syracuseStep 2089093 = 391705) (by norm_num)
theorem B2785457 : Blo 1929435 2785457 := bstep (se 2 (by rfl) ⟨1044546, by rfl⟩ : syracuseStep 2785457 = 2089093) B2089093
theorem B7427885 : Blo 1929435 7427885 := bstep (se 3 (by rfl) ⟨1392728, by rfl⟩ : syracuseStep 7427885 = 2785457) B2785457
theorem B79230773 : Blo 1929435 79230773 := bstep (se 5 (by rfl) ⟨3713942, by rfl⟩ : syracuseStep 79230773 = 7427885) B7427885
theorem B52820515 : Blo 1929435 52820515 := bstep (se 1 (by rfl) ⟨39615386, by rfl⟩ : syracuseStep 52820515 = 79230773) B79230773
theorem B70427353 : Blo 1929435 70427353 := bstep (se 2 (by rfl) ⟨26410257, by rfl⟩ : syracuseStep 70427353 = 52820515) B52820515
theorem B93903137 : Blo 1929435 93903137 := bstep (se 2 (by rfl) ⟨35213676, by rfl⟩ : syracuseStep 93903137 = 70427353) B70427353
theorem B62602091 : Blo 1929435 62602091 := bstep (se 1 (by rfl) ⟨46951568, by rfl⟩ : syracuseStep 62602091 = 93903137) B93903137
theorem B41734727 : Blo 1929435 41734727 := bstep (se 1 (by rfl) ⟨31301045, by rfl⟩ : syracuseStep 41734727 = 62602091) B62602091
theorem B27823151 : Blo 1929435 27823151 := bstep (se 1 (by rfl) ⟨20867363, by rfl⟩ : syracuseStep 27823151 = 41734727) B41734727
theorem B18548767 : Blo 1929435 18548767 := bstep (se 1 (by rfl) ⟨13911575, by rfl⟩ : syracuseStep 18548767 = 27823151) B27823151
theorem B24731689 : Blo 1929435 24731689 := bstep (se 2 (by rfl) ⟨9274383, by rfl⟩ : syracuseStep 24731689 = 18548767) B18548767
theorem B32975585 : Blo 1929435 32975585 := bstep (se 2 (by rfl) ⟨12365844, by rfl⟩ : syracuseStep 32975585 = 24731689) B24731689
theorem B21983723 : Blo 1929435 21983723 := bstep (se 1 (by rfl) ⟨16487792, by rfl⟩ : syracuseStep 21983723 = 32975585) B32975585
theorem B14655815 : Blo 1929435 14655815 := bstep (se 1 (by rfl) ⟨10991861, by rfl⟩ : syracuseStep 14655815 = 21983723) B21983723
theorem B9770543 : Blo 1929435 9770543 := bstep (se 1 (by rfl) ⟨7327907, by rfl⟩ : syracuseStep 9770543 = 14655815) B14655815
theorem B6513695 : Blo 1929435 6513695 := bstep (se 1 (by rfl) ⟨4885271, by rfl⟩ : syracuseStep 6513695 = 9770543) B9770543
theorem B4342463 : Blo 1929435 4342463 := bstep (se 1 (by rfl) ⟨3256847, by rfl⟩ : syracuseStep 4342463 = 6513695) B6513695
theorem B2894975 : Blo 1929435 2894975 := bstep (se 1 (by rfl) ⟨2171231, by rfl⟩ : syracuseStep 2894975 = 4342463) B4342463
theorem B1929983 : Blo 1929435 1929983 := bstep (se 1 (by rfl) ⟨1447487, by rfl⟩ : syracuseStep 1929983 = 2894975) B2894975
theorem B2894981 : Blo 1929435 2894981 := bbase (se 4 (by rfl) ⟨271404, by rfl⟩ : syracuseStep 2894981 = 542809) (by norm_num)
theorem B1929987 : Blo 1929435 1929987 := bstep (se 1 (by rfl) ⟨1447490, by rfl⟩ : syracuseStep 1929987 = 2894981) B2894981
theorem B3256861 : Blo 1929435 3256861 := bbase (se 3 (by rfl) ⟨610661, by rfl⟩ : syracuseStep 3256861 = 1221323) (by norm_num)
theorem B4342481 : Blo 1929435 4342481 := bstep (se 2 (by rfl) ⟨1628430, by rfl⟩ : syracuseStep 4342481 = 3256861) B3256861
theorem B2894987 : Blo 1929435 2894987 := bstep (se 1 (by rfl) ⟨2171240, by rfl⟩ : syracuseStep 2894987 = 4342481) B4342481
theorem B1929991 : Blo 1929435 1929991 := bstep (se 1 (by rfl) ⟨1447493, by rfl⟩ : syracuseStep 1929991 = 2894987) B2894987
theorem B2171245 : Blo 1929435 2171245 := bbase (se 3 (by rfl) ⟨407108, by rfl⟩ : syracuseStep 2171245 = 814217) (by norm_num)
theorem B2894993 : Blo 1929435 2894993 := bstep (se 2 (by rfl) ⟨1085622, by rfl⟩ : syracuseStep 2894993 = 2171245) B2171245
theorem B1929995 : Blo 1929435 1929995 := bstep (se 1 (by rfl) ⟨1447496, by rfl⟩ : syracuseStep 1929995 = 2894993) B2894993
theorem B6513749 : Blo 1929435 6513749 := bbase (se 8 (by rfl) ⟨38166, by rfl⟩ : syracuseStep 6513749 = 76333) (by norm_num)
theorem B4342499 : Blo 1929435 4342499 := bstep (se 1 (by rfl) ⟨3256874, by rfl⟩ : syracuseStep 4342499 = 6513749) B6513749
theorem B2894999 : Blo 1929435 2894999 := bstep (se 1 (by rfl) ⟨2171249, by rfl⟩ : syracuseStep 2894999 = 4342499) B4342499
theorem B1929999 : Blo 1929435 1929999 := bstep (se 1 (by rfl) ⟨1447499, by rfl⟩ : syracuseStep 1929999 = 2894999) B2894999
theorem B2895005 : Blo 1929435 2895005 := bbase (se 3 (by rfl) ⟨542813, by rfl⟩ : syracuseStep 2895005 = 1085627) (by norm_num)
theorem B1930003 : Blo 1929435 1930003 := bstep (se 1 (by rfl) ⟨1447502, by rfl⟩ : syracuseStep 1930003 = 2895005) B2895005
theorem B4342517 : Blo 1929435 4342517 := bbase (se 5 (by rfl) ⟨203555, by rfl⟩ : syracuseStep 4342517 = 407111) (by norm_num)
theorem B2895011 : Blo 1929435 2895011 := bstep (se 1 (by rfl) ⟨2171258, by rfl⟩ : syracuseStep 2895011 = 4342517) B4342517
theorem B1930007 : Blo 1929435 1930007 := bstep (se 1 (by rfl) ⟨1447505, by rfl⟩ : syracuseStep 1930007 = 2895011) B2895011
theorem B24732053 : Blo 1929435 24732053 := bbase (se 6 (by rfl) ⟨579657, by rfl⟩ : syracuseStep 24732053 = 1159315) (by norm_num)
theorem B16488035 : Blo 1929435 16488035 := bstep (se 1 (by rfl) ⟨12366026, by rfl⟩ : syracuseStep 16488035 = 24732053) B24732053
theorem B10992023 : Blo 1929435 10992023 := bstep (se 1 (by rfl) ⟨8244017, by rfl⟩ : syracuseStep 10992023 = 16488035) B16488035
theorem B7328015 : Blo 1929435 7328015 := bstep (se 1 (by rfl) ⟨5496011, by rfl⟩ : syracuseStep 7328015 = 10992023) B10992023
theorem B4885343 : Blo 1929435 4885343 := bstep (se 1 (by rfl) ⟨3664007, by rfl⟩ : syracuseStep 4885343 = 7328015) B7328015
theorem B3256895 : Blo 1929435 3256895 := bstep (se 1 (by rfl) ⟨2442671, by rfl⟩ : syracuseStep 3256895 = 4885343) B4885343
theorem B2171263 : Blo 1929435 2171263 := bstep (se 1 (by rfl) ⟨1628447, by rfl⟩ : syracuseStep 2171263 = 3256895) B3256895
theorem B2895017 : Blo 1929435 2895017 := bstep (se 2 (by rfl) ⟨1085631, by rfl⟩ : syracuseStep 2895017 = 2171263) B2171263
theorem B1930011 : Blo 1929435 1930011 := bstep (se 1 (by rfl) ⟨1447508, by rfl⟩ : syracuseStep 1930011 = 2895017) B2895017
theorem B1956349 : Blo 1929435 1956349 := bbase (se 3 (by rfl) ⟨366815, by rfl⟩ : syracuseStep 1956349 = 733631) (by norm_num)
theorem B2608465 : Blo 1929435 2608465 := bstep (se 2 (by rfl) ⟨978174, by rfl⟩ : syracuseStep 2608465 = 1956349) B1956349
theorem B3477953 : Blo 1929435 3477953 := bstep (se 2 (by rfl) ⟨1304232, by rfl⟩ : syracuseStep 3477953 = 2608465) B2608465
theorem B2318635 : Blo 1929435 2318635 := bstep (se 1 (by rfl) ⟨1738976, by rfl⟩ : syracuseStep 2318635 = 3477953) B3477953
theorem B3091513 : Blo 1929435 3091513 := bstep (se 2 (by rfl) ⟨1159317, by rfl⟩ : syracuseStep 3091513 = 2318635) B2318635
theorem B4122017 : Blo 1929435 4122017 := bstep (se 2 (by rfl) ⟨1545756, by rfl⟩ : syracuseStep 4122017 = 3091513) B3091513
theorem B2748011 : Blo 1929435 2748011 := bstep (se 1 (by rfl) ⟨2061008, by rfl⟩ : syracuseStep 2748011 = 4122017) B4122017
theorem B7328029 : Blo 1929435 7328029 := bstep (se 3 (by rfl) ⟨1374005, by rfl⟩ : syracuseStep 7328029 = 2748011) B2748011
theorem B9770705 : Blo 1929435 9770705 := bstep (se 2 (by rfl) ⟨3664014, by rfl⟩ : syracuseStep 9770705 = 7328029) B7328029
theorem B6513803 : Blo 1929435 6513803 := bstep (se 1 (by rfl) ⟨4885352, by rfl⟩ : syracuseStep 6513803 = 9770705) B9770705
theorem B4342535 : Blo 1929435 4342535 := bstep (se 1 (by rfl) ⟨3256901, by rfl⟩ : syracuseStep 4342535 = 6513803) B6513803
theorem B2895023 : Blo 1929435 2895023 := bstep (se 1 (by rfl) ⟨2171267, by rfl⟩ : syracuseStep 2895023 = 4342535) B4342535
theorem B1930015 : Blo 1929435 1930015 := bstep (se 1 (by rfl) ⟨1447511, by rfl⟩ : syracuseStep 1930015 = 2895023) B2895023
theorem B2895029 : Blo 1929435 2895029 := bbase (se 5 (by rfl) ⟨135704, by rfl⟩ : syracuseStep 2895029 = 271409) (by norm_num)
theorem B1930019 : Blo 1929435 1930019 := bstep (se 1 (by rfl) ⟨1447514, by rfl⟩ : syracuseStep 1930019 = 2895029) B2895029
theorem B4885373 : Blo 1929435 4885373 := bbase (se 3 (by rfl) ⟨916007, by rfl⟩ : syracuseStep 4885373 = 1832015) (by norm_num)
theorem B3256915 : Blo 1929435 3256915 := bstep (se 1 (by rfl) ⟨2442686, by rfl⟩ : syracuseStep 3256915 = 4885373) B4885373
theorem B4342553 : Blo 1929435 4342553 := bstep (se 2 (by rfl) ⟨1628457, by rfl⟩ : syracuseStep 4342553 = 3256915) B3256915
theorem B2895035 : Blo 1929435 2895035 := bstep (se 1 (by rfl) ⟨2171276, by rfl⟩ : syracuseStep 2895035 = 4342553) B4342553
theorem B1930023 : Blo 1929435 1930023 := bstep (se 1 (by rfl) ⟨1447517, by rfl⟩ : syracuseStep 1930023 = 2895035) B2895035
theorem B2171281 : Blo 1929435 2171281 := bbase (se 2 (by rfl) ⟨814230, by rfl⟩ : syracuseStep 2171281 = 1628461) (by norm_num)
theorem B2895041 : Blo 1929435 2895041 := bstep (se 2 (by rfl) ⟨1085640, by rfl⟩ : syracuseStep 2895041 = 2171281) B2171281
theorem B1930027 : Blo 1929435 1930027 := bstep (se 1 (by rfl) ⟨1447520, by rfl⟩ : syracuseStep 1930027 = 2895041) B2895041
theorem B3664045 : Blo 1929435 3664045 := bbase (se 3 (by rfl) ⟨687008, by rfl⟩ : syracuseStep 3664045 = 1374017) (by norm_num)
theorem B4885393 : Blo 1929435 4885393 := bstep (se 2 (by rfl) ⟨1832022, by rfl⟩ : syracuseStep 4885393 = 3664045) B3664045
theorem B6513857 : Blo 1929435 6513857 := bstep (se 2 (by rfl) ⟨2442696, by rfl⟩ : syracuseStep 6513857 = 4885393) B4885393
theorem B4342571 : Blo 1929435 4342571 := bstep (se 1 (by rfl) ⟨3256928, by rfl⟩ : syracuseStep 4342571 = 6513857) B6513857
theorem B2895047 : Blo 1929435 2895047 := bstep (se 1 (by rfl) ⟨2171285, by rfl⟩ : syracuseStep 2895047 = 4342571) B4342571
theorem B1930031 : Blo 1929435 1930031 := bstep (se 1 (by rfl) ⟨1447523, by rfl⟩ : syracuseStep 1930031 = 2895047) B2895047
theorem B2895053 : Blo 1929435 2895053 := bbase (se 3 (by rfl) ⟨542822, by rfl⟩ : syracuseStep 2895053 = 1085645) (by norm_num)
theorem B1930035 : Blo 1929435 1930035 := bstep (se 1 (by rfl) ⟨1447526, by rfl⟩ : syracuseStep 1930035 = 2895053) B2895053
theorem B4342589 : Blo 1929435 4342589 := bbase (se 3 (by rfl) ⟨814235, by rfl⟩ : syracuseStep 4342589 = 1628471) (by norm_num)
theorem B2895059 : Blo 1929435 2895059 := bstep (se 1 (by rfl) ⟨2171294, by rfl⟩ : syracuseStep 2895059 = 4342589) B4342589
theorem B1930039 : Blo 1929435 1930039 := bstep (se 1 (by rfl) ⟨1447529, by rfl⟩ : syracuseStep 1930039 = 2895059) B2895059
theorem B3256949 : Blo 1929435 3256949 := bbase (se 5 (by rfl) ⟨152669, by rfl⟩ : syracuseStep 3256949 = 305339) (by norm_num)
theorem B2171299 : Blo 1929435 2171299 := bstep (se 1 (by rfl) ⟨1628474, by rfl⟩ : syracuseStep 2171299 = 3256949) B3256949
theorem B2895065 : Blo 1929435 2895065 := bstep (se 2 (by rfl) ⟨1085649, by rfl⟩ : syracuseStep 2895065 = 2171299) B2171299
theorem B1930043 : Blo 1929435 1930043 := bstep (se 1 (by rfl) ⟨1447532, by rfl⟩ : syracuseStep 1930043 = 2895065) B2895065
theorem B4122085 : Blo 1929435 4122085 := bbase (se 4 (by rfl) ⟨386445, by rfl⟩ : syracuseStep 4122085 = 772891) (by norm_num)
theorem B5496113 : Blo 1929435 5496113 := bstep (se 2 (by rfl) ⟨2061042, by rfl⟩ : syracuseStep 5496113 = 4122085) B4122085
theorem B14656301 : Blo 1929435 14656301 := bstep (se 3 (by rfl) ⟨2748056, by rfl⟩ : syracuseStep 14656301 = 5496113) B5496113
theorem B9770867 : Blo 1929435 9770867 := bstep (se 1 (by rfl) ⟨7328150, by rfl⟩ : syracuseStep 9770867 = 14656301) B14656301
theorem B6513911 : Blo 1929435 6513911 := bstep (se 1 (by rfl) ⟨4885433, by rfl⟩ : syracuseStep 6513911 = 9770867) B9770867
theorem B4342607 : Blo 1929435 4342607 := bstep (se 1 (by rfl) ⟨3256955, by rfl⟩ : syracuseStep 4342607 = 6513911) B6513911
theorem B2895071 : Blo 1929435 2895071 := bstep (se 1 (by rfl) ⟨2171303, by rfl⟩ : syracuseStep 2895071 = 4342607) B4342607
theorem B1930047 : Blo 1929435 1930047 := bstep (se 1 (by rfl) ⟨1447535, by rfl⟩ : syracuseStep 1930047 = 2895071) B2895071
theorem B2895077 : Blo 1929435 2895077 := bbase (se 4 (by rfl) ⟨271413, by rfl⟩ : syracuseStep 2895077 = 542827) (by norm_num)
theorem B1930051 : Blo 1929435 1930051 := bstep (se 1 (by rfl) ⟨1447538, by rfl⟩ : syracuseStep 1930051 = 2895077) B2895077
theorem B4401877 : Blo 1929435 4401877 := bbase (se 7 (by rfl) ⟨51584, by rfl⟩ : syracuseStep 4401877 = 103169) (by norm_num)
theorem B5869169 : Blo 1929435 5869169 := bstep (se 2 (by rfl) ⟨2200938, by rfl⟩ : syracuseStep 5869169 = 4401877) B4401877
theorem B3912779 : Blo 1929435 3912779 := bstep (se 1 (by rfl) ⟨2934584, by rfl⟩ : syracuseStep 3912779 = 5869169) B5869169
theorem B2608519 : Blo 1929435 2608519 := bstep (se 1 (by rfl) ⟨1956389, by rfl⟩ : syracuseStep 2608519 = 3912779) B3912779
theorem B3478025 : Blo 1929435 3478025 := bstep (se 2 (by rfl) ⟨1304259, by rfl⟩ : syracuseStep 3478025 = 2608519) B2608519
theorem B9274733 : Blo 1929435 9274733 := bstep (se 3 (by rfl) ⟨1739012, by rfl⟩ : syracuseStep 9274733 = 3478025) B3478025
theorem B6183155 : Blo 1929435 6183155 := bstep (se 1 (by rfl) ⟨4637366, by rfl⟩ : syracuseStep 6183155 = 9274733) B9274733
theorem B4122103 : Blo 1929435 4122103 := bstep (se 1 (by rfl) ⟨3091577, by rfl⟩ : syracuseStep 4122103 = 6183155) B6183155
theorem B5496137 : Blo 1929435 5496137 := bstep (se 2 (by rfl) ⟨2061051, by rfl⟩ : syracuseStep 5496137 = 4122103) B4122103
theorem B3664091 : Blo 1929435 3664091 := bstep (se 1 (by rfl) ⟨2748068, by rfl⟩ : syracuseStep 3664091 = 5496137) B5496137
theorem B2442727 : Blo 1929435 2442727 := bstep (se 1 (by rfl) ⟨1832045, by rfl⟩ : syracuseStep 2442727 = 3664091) B3664091
theorem B3256969 : Blo 1929435 3256969 := bstep (se 2 (by rfl) ⟨1221363, by rfl⟩ : syracuseStep 3256969 = 2442727) B2442727
theorem B4342625 : Blo 1929435 4342625 := bstep (se 2 (by rfl) ⟨1628484, by rfl⟩ : syracuseStep 4342625 = 3256969) B3256969
theorem B2895083 : Blo 1929435 2895083 := bstep (se 1 (by rfl) ⟨2171312, by rfl⟩ : syracuseStep 2895083 = 4342625) B4342625
theorem B1930055 : Blo 1929435 1930055 := bstep (se 1 (by rfl) ⟨1447541, by rfl⟩ : syracuseStep 1930055 = 2895083) B2895083
theorem B2171317 : Blo 1929435 2171317 := bbase (se 5 (by rfl) ⟨101780, by rfl⟩ : syracuseStep 2171317 = 203561) (by norm_num)
theorem B2895089 : Blo 1929435 2895089 := bstep (se 2 (by rfl) ⟨1085658, by rfl⟩ : syracuseStep 2895089 = 2171317) B2171317
theorem B1930059 : Blo 1929435 1930059 := bstep (se 1 (by rfl) ⟨1447544, by rfl⟩ : syracuseStep 1930059 = 2895089) B2895089
theorem B2442737 : Blo 1929435 2442737 := bbase (se 2 (by rfl) ⟨916026, by rfl⟩ : syracuseStep 2442737 = 1832053) (by norm_num)
theorem B6513965 : Blo 1929435 6513965 := bstep (se 3 (by rfl) ⟨1221368, by rfl⟩ : syracuseStep 6513965 = 2442737) B2442737
theorem B4342643 : Blo 1929435 4342643 := bstep (se 1 (by rfl) ⟨3256982, by rfl⟩ : syracuseStep 4342643 = 6513965) B6513965
theorem B2895095 : Blo 1929435 2895095 := bstep (se 1 (by rfl) ⟨2171321, by rfl⟩ : syracuseStep 2895095 = 4342643) B4342643
theorem B1930063 : Blo 1929435 1930063 := bstep (se 1 (by rfl) ⟨1447547, by rfl⟩ : syracuseStep 1930063 = 2895095) B2895095
theorem B2895101 : Blo 1929435 2895101 := bbase (se 3 (by rfl) ⟨542831, by rfl⟩ : syracuseStep 2895101 = 1085663) (by norm_num)
theorem B1930067 : Blo 1929435 1930067 := bstep (se 1 (by rfl) ⟨1447550, by rfl⟩ : syracuseStep 1930067 = 2895101) B2895101
theorem B4342661 : Blo 1929435 4342661 := bbase (se 4 (by rfl) ⟨407124, by rfl⟩ : syracuseStep 4342661 = 814249) (by norm_num)
theorem B2895107 : Blo 1929435 2895107 := bstep (se 1 (by rfl) ⟨2171330, by rfl⟩ : syracuseStep 2895107 = 4342661) B4342661
theorem B1930071 : Blo 1929435 1930071 := bstep (se 1 (by rfl) ⟨1447553, by rfl⟩ : syracuseStep 1930071 = 2895107) B2895107
theorem B2061073 : Blo 1929435 2061073 := bbase (se 2 (by rfl) ⟨772902, by rfl⟩ : syracuseStep 2061073 = 1545805) (by norm_num)
theorem B2748097 : Blo 1929435 2748097 := bstep (se 2 (by rfl) ⟨1030536, by rfl⟩ : syracuseStep 2748097 = 2061073) B2061073
theorem B3664129 : Blo 1929435 3664129 := bstep (se 2 (by rfl) ⟨1374048, by rfl⟩ : syracuseStep 3664129 = 2748097) B2748097
theorem B4885505 : Blo 1929435 4885505 := bstep (se 2 (by rfl) ⟨1832064, by rfl⟩ : syracuseStep 4885505 = 3664129) B3664129
theorem B3257003 : Blo 1929435 3257003 := bstep (se 1 (by rfl) ⟨2442752, by rfl⟩ : syracuseStep 3257003 = 4885505) B4885505
theorem B2171335 : Blo 1929435 2171335 := bstep (se 1 (by rfl) ⟨1628501, by rfl⟩ : syracuseStep 2171335 = 3257003) B3257003
theorem B2895113 : Blo 1929435 2895113 := bstep (se 2 (by rfl) ⟨1085667, by rfl⟩ : syracuseStep 2895113 = 2171335) B2171335
theorem B1930075 : Blo 1929435 1930075 := bstep (se 1 (by rfl) ⟨1447556, by rfl⟩ : syracuseStep 1930075 = 2895113) B2895113
theorem B9771029 : Blo 1929435 9771029 := bbase (se 6 (by rfl) ⟨229008, by rfl⟩ : syracuseStep 9771029 = 458017) (by norm_num)
theorem B6514019 : Blo 1929435 6514019 := bstep (se 1 (by rfl) ⟨4885514, by rfl⟩ : syracuseStep 6514019 = 9771029) B9771029
theorem B4342679 : Blo 1929435 4342679 := bstep (se 1 (by rfl) ⟨3257009, by rfl⟩ : syracuseStep 4342679 = 6514019) B6514019
theorem B2895119 : Blo 1929435 2895119 := bstep (se 1 (by rfl) ⟨2171339, by rfl⟩ : syracuseStep 2895119 = 4342679) B4342679
theorem B1930079 : Blo 1929435 1930079 := bstep (se 1 (by rfl) ⟨1447559, by rfl⟩ : syracuseStep 1930079 = 2895119) B2895119
theorem B2895125 : Blo 1929435 2895125 := bbase (se 6 (by rfl) ⟨67854, by rfl⟩ : syracuseStep 2895125 = 135709) (by norm_num)
theorem B1930083 : Blo 1929435 1930083 := bstep (se 1 (by rfl) ⟨1447562, by rfl⟩ : syracuseStep 1930083 = 2895125) B2895125
theorem B2680229 : Blo 1929435 2680229 := bbase (se 4 (by rfl) ⟨251271, by rfl⟩ : syracuseStep 2680229 = 502543) (by norm_num)
theorem B7147277 : Blo 1929435 7147277 := bstep (se 3 (by rfl) ⟨1340114, by rfl⟩ : syracuseStep 7147277 = 2680229) B2680229
theorem B4764851 : Blo 1929435 4764851 := bstep (se 1 (by rfl) ⟨3573638, by rfl⟩ : syracuseStep 4764851 = 7147277) B7147277
theorem B3176567 : Blo 1929435 3176567 := bstep (se 1 (by rfl) ⟨2382425, by rfl⟩ : syracuseStep 3176567 = 4764851) B4764851
theorem B2117711 : Blo 1929435 2117711 := bstep (se 1 (by rfl) ⟨1588283, by rfl⟩ : syracuseStep 2117711 = 3176567) B3176567
theorem B5647229 : Blo 1929435 5647229 := bstep (se 3 (by rfl) ⟨1058855, by rfl⟩ : syracuseStep 5647229 = 2117711) B2117711
theorem B3764819 : Blo 1929435 3764819 := bstep (se 1 (by rfl) ⟨2823614, by rfl⟩ : syracuseStep 3764819 = 5647229) B5647229
theorem B2509879 : Blo 1929435 2509879 := bstep (se 1 (by rfl) ⟨1882409, by rfl⟩ : syracuseStep 2509879 = 3764819) B3764819
theorem B3346505 : Blo 1929435 3346505 := bstep (se 2 (by rfl) ⟨1254939, by rfl⟩ : syracuseStep 3346505 = 2509879) B2509879
theorem B2231003 : Blo 1929435 2231003 := bstep (se 1 (by rfl) ⟨1673252, by rfl⟩ : syracuseStep 2231003 = 3346505) B3346505
theorem B5949341 : Blo 1929435 5949341 := bstep (se 3 (by rfl) ⟨1115501, by rfl⟩ : syracuseStep 5949341 = 2231003) B2231003
theorem B3966227 : Blo 1929435 3966227 := bstep (se 1 (by rfl) ⟨2974670, by rfl⟩ : syracuseStep 3966227 = 5949341) B5949341
theorem B42306421 : Blo 1929435 42306421 := bstep (se 5 (by rfl) ⟨1983113, by rfl⟩ : syracuseStep 42306421 = 3966227) B3966227
theorem B56408561 : Blo 1929435 56408561 := bstep (se 2 (by rfl) ⟨21153210, by rfl⟩ : syracuseStep 56408561 = 42306421) B42306421
theorem B37605707 : Blo 1929435 37605707 := bstep (se 1 (by rfl) ⟨28204280, by rfl⟩ : syracuseStep 37605707 = 56408561) B56408561
theorem B25070471 : Blo 1929435 25070471 := bstep (se 1 (by rfl) ⟨18802853, by rfl⟩ : syracuseStep 25070471 = 37605707) B37605707
theorem B16713647 : Blo 1929435 16713647 := bstep (se 1 (by rfl) ⟨12535235, by rfl⟩ : syracuseStep 16713647 = 25070471) B25070471
theorem B11142431 : Blo 1929435 11142431 := bstep (se 1 (by rfl) ⟨8356823, by rfl⟩ : syracuseStep 11142431 = 16713647) B16713647
theorem B7428287 : Blo 1929435 7428287 := bstep (se 1 (by rfl) ⟨5571215, by rfl⟩ : syracuseStep 7428287 = 11142431) B11142431
theorem B19808765 : Blo 1929435 19808765 := bstep (se 3 (by rfl) ⟨3714143, by rfl⟩ : syracuseStep 19808765 = 7428287) B7428287
theorem B13205843 : Blo 1929435 13205843 := bstep (se 1 (by rfl) ⟨9904382, by rfl⟩ : syracuseStep 13205843 = 19808765) B19808765
theorem B8803895 : Blo 1929435 8803895 := bstep (se 1 (by rfl) ⟨6602921, by rfl⟩ : syracuseStep 8803895 = 13205843) B13205843
theorem B23477053 : Blo 1929435 23477053 := bstep (se 3 (by rfl) ⟨4401947, by rfl⟩ : syracuseStep 23477053 = 8803895) B8803895
theorem B31302737 : Blo 1929435 31302737 := bstep (se 2 (by rfl) ⟨11738526, by rfl⟩ : syracuseStep 31302737 = 23477053) B23477053
theorem B20868491 : Blo 1929435 20868491 := bstep (se 1 (by rfl) ⟨15651368, by rfl⟩ : syracuseStep 20868491 = 31302737) B31302737
theorem B13912327 : Blo 1929435 13912327 := bstep (se 1 (by rfl) ⟨10434245, by rfl⟩ : syracuseStep 13912327 = 20868491) B20868491
theorem B18549769 : Blo 1929435 18549769 := bstep (se 2 (by rfl) ⟨6956163, by rfl⟩ : syracuseStep 18549769 = 13912327) B13912327
theorem B24733025 : Blo 1929435 24733025 := bstep (se 2 (by rfl) ⟨9274884, by rfl⟩ : syracuseStep 24733025 = 18549769) B18549769
theorem B16488683 : Blo 1929435 16488683 := bstep (se 1 (by rfl) ⟨12366512, by rfl⟩ : syracuseStep 16488683 = 24733025) B24733025
theorem B10992455 : Blo 1929435 10992455 := bstep (se 1 (by rfl) ⟨8244341, by rfl⟩ : syracuseStep 10992455 = 16488683) B16488683
theorem B7328303 : Blo 1929435 7328303 := bstep (se 1 (by rfl) ⟨5496227, by rfl⟩ : syracuseStep 7328303 = 10992455) B10992455
theorem B4885535 : Blo 1929435 4885535 := bstep (se 1 (by rfl) ⟨3664151, by rfl⟩ : syracuseStep 4885535 = 7328303) B7328303
theorem B3257023 : Blo 1929435 3257023 := bstep (se 1 (by rfl) ⟨2442767, by rfl⟩ : syracuseStep 3257023 = 4885535) B4885535
theorem B4342697 : Blo 1929435 4342697 := bstep (se 2 (by rfl) ⟨1628511, by rfl⟩ : syracuseStep 4342697 = 3257023) B3257023
theorem B2895131 : Blo 1929435 2895131 := bstep (se 1 (by rfl) ⟨2171348, by rfl⟩ : syracuseStep 2895131 = 4342697) B4342697
theorem B1930087 : Blo 1929435 1930087 := bstep (se 1 (by rfl) ⟨1447565, by rfl⟩ : syracuseStep 1930087 = 2895131) B2895131
theorem B2171353 : Blo 1929435 2171353 := bbase (se 2 (by rfl) ⟨814257, by rfl⟩ : syracuseStep 2171353 = 1628515) (by norm_num)
theorem B2895137 : Blo 1929435 2895137 := bstep (se 2 (by rfl) ⟨1085676, by rfl⟩ : syracuseStep 2895137 = 2171353) B2171353
theorem B1930091 : Blo 1929435 1930091 := bstep (se 1 (by rfl) ⟨1447568, by rfl⟩ : syracuseStep 1930091 = 2895137) B2895137
theorem B2748125 : Blo 1929435 2748125 := bbase (se 3 (by rfl) ⟨515273, by rfl⟩ : syracuseStep 2748125 = 1030547) (by norm_num)
theorem B7328333 : Blo 1929435 7328333 := bstep (se 3 (by rfl) ⟨1374062, by rfl⟩ : syracuseStep 7328333 = 2748125) B2748125
theorem B4885555 : Blo 1929435 4885555 := bstep (se 1 (by rfl) ⟨3664166, by rfl⟩ : syracuseStep 4885555 = 7328333) B7328333
theorem B6514073 : Blo 1929435 6514073 := bstep (se 2 (by rfl) ⟨2442777, by rfl⟩ : syracuseStep 6514073 = 4885555) B4885555
theorem B4342715 : Blo 1929435 4342715 := bstep (se 1 (by rfl) ⟨3257036, by rfl⟩ : syracuseStep 4342715 = 6514073) B6514073
theorem B2895143 : Blo 1929435 2895143 := bstep (se 1 (by rfl) ⟨2171357, by rfl⟩ : syracuseStep 2895143 = 4342715) B4342715
theorem B1930095 : Blo 1929435 1930095 := bstep (se 1 (by rfl) ⟨1447571, by rfl⟩ : syracuseStep 1930095 = 2895143) B2895143
theorem B2895149 : Blo 1929435 2895149 := bbase (se 3 (by rfl) ⟨542840, by rfl⟩ : syracuseStep 2895149 = 1085681) (by norm_num)
theorem B1930099 : Blo 1929435 1930099 := bstep (se 1 (by rfl) ⟨1447574, by rfl⟩ : syracuseStep 1930099 = 2895149) B2895149
theorem B4342733 : Blo 1929435 4342733 := bbase (se 3 (by rfl) ⟨814262, by rfl⟩ : syracuseStep 4342733 = 1628525) (by norm_num)
theorem B2895155 : Blo 1929435 2895155 := bstep (se 1 (by rfl) ⟨2171366, by rfl⟩ : syracuseStep 2895155 = 4342733) B4342733
theorem B1930103 : Blo 1929435 1930103 := bstep (se 1 (by rfl) ⟨1447577, by rfl⟩ : syracuseStep 1930103 = 2895155) B2895155
theorem B2442793 : Blo 1929435 2442793 := bbase (se 2 (by rfl) ⟨916047, by rfl⟩ : syracuseStep 2442793 = 1832095) (by norm_num)
theorem B3257057 : Blo 1929435 3257057 := bstep (se 2 (by rfl) ⟨1221396, by rfl⟩ : syracuseStep 3257057 = 2442793) B2442793
theorem B2171371 : Blo 1929435 2171371 := bstep (se 1 (by rfl) ⟨1628528, by rfl⟩ : syracuseStep 2171371 = 3257057) B3257057
theorem B2895161 : Blo 1929435 2895161 := bstep (se 2 (by rfl) ⟨1085685, by rfl⟩ : syracuseStep 2895161 = 2171371) B2171371
theorem B1930107 : Blo 1929435 1930107 := bstep (se 1 (by rfl) ⟨1447580, by rfl⟩ : syracuseStep 1930107 = 2895161) B2895161
theorem B7825781 : Blo 1929435 7825781 := bbase (se 5 (by rfl) ⟨366833, by rfl⟩ : syracuseStep 7825781 = 733667) (by norm_num)
theorem B20868749 : Blo 1929435 20868749 := bstep (se 3 (by rfl) ⟨3912890, by rfl⟩ : syracuseStep 20868749 = 7825781) B7825781
theorem B13912499 : Blo 1929435 13912499 := bstep (se 1 (by rfl) ⟨10434374, by rfl⟩ : syracuseStep 13912499 = 20868749) B20868749
theorem B9274999 : Blo 1929435 9274999 := bstep (se 1 (by rfl) ⟨6956249, by rfl⟩ : syracuseStep 9274999 = 13912499) B13912499
theorem B12366665 : Blo 1929435 12366665 := bstep (se 2 (by rfl) ⟨4637499, by rfl⟩ : syracuseStep 12366665 = 9274999) B9274999
theorem B8244443 : Blo 1929435 8244443 := bstep (se 1 (by rfl) ⟨6183332, by rfl⟩ : syracuseStep 8244443 = 12366665) B12366665
theorem B21985181 : Blo 1929435 21985181 := bstep (se 3 (by rfl) ⟨4122221, by rfl⟩ : syracuseStep 21985181 = 8244443) B8244443
theorem B14656787 : Blo 1929435 14656787 := bstep (se 1 (by rfl) ⟨10992590, by rfl⟩ : syracuseStep 14656787 = 21985181) B21985181
theorem B9771191 : Blo 1929435 9771191 := bstep (se 1 (by rfl) ⟨7328393, by rfl⟩ : syracuseStep 9771191 = 14656787) B14656787
theorem B6514127 : Blo 1929435 6514127 := bstep (se 1 (by rfl) ⟨4885595, by rfl⟩ : syracuseStep 6514127 = 9771191) B9771191
theorem B4342751 : Blo 1929435 4342751 := bstep (se 1 (by rfl) ⟨3257063, by rfl⟩ : syracuseStep 4342751 = 6514127) B6514127
theorem B2895167 : Blo 1929435 2895167 := bstep (se 1 (by rfl) ⟨2171375, by rfl⟩ : syracuseStep 2895167 = 4342751) B4342751
theorem B1930111 : Blo 1929435 1930111 := bstep (se 1 (by rfl) ⟨1447583, by rfl⟩ : syracuseStep 1930111 = 2895167) B2895167
theorem B2895173 : Blo 1929435 2895173 := bbase (se 4 (by rfl) ⟨271422, by rfl⟩ : syracuseStep 2895173 = 542845) (by norm_num)
theorem B1930115 : Blo 1929435 1930115 := bstep (se 1 (by rfl) ⟨1447586, by rfl⟩ : syracuseStep 1930115 = 2895173) B2895173
theorem B3257077 : Blo 1929435 3257077 := bbase (se 5 (by rfl) ⟨152675, by rfl⟩ : syracuseStep 3257077 = 305351) (by norm_num)
theorem B4342769 : Blo 1929435 4342769 := bstep (se 2 (by rfl) ⟨1628538, by rfl⟩ : syracuseStep 4342769 = 3257077) B3257077
theorem B2895179 : Blo 1929435 2895179 := bstep (se 1 (by rfl) ⟨2171384, by rfl⟩ : syracuseStep 2895179 = 4342769) B4342769
theorem B1930119 : Blo 1929435 1930119 := bstep (se 1 (by rfl) ⟨1447589, by rfl⟩ : syracuseStep 1930119 = 2895179) B2895179
theorem B2171389 : Blo 1929435 2171389 := bbase (se 3 (by rfl) ⟨407135, by rfl⟩ : syracuseStep 2171389 = 814271) (by norm_num)
theorem B2895185 : Blo 1929435 2895185 := bstep (se 2 (by rfl) ⟨1085694, by rfl⟩ : syracuseStep 2895185 = 2171389) B2171389
theorem B1930123 : Blo 1929435 1930123 := bstep (se 1 (by rfl) ⟨1447592, by rfl⟩ : syracuseStep 1930123 = 2895185) B2895185
theorem B6514181 : Blo 1929435 6514181 := bbase (se 4 (by rfl) ⟨610704, by rfl⟩ : syracuseStep 6514181 = 1221409) (by norm_num)
theorem B4342787 : Blo 1929435 4342787 := bstep (se 1 (by rfl) ⟨3257090, by rfl⟩ : syracuseStep 4342787 = 6514181) B6514181
theorem B2895191 : Blo 1929435 2895191 := bstep (se 1 (by rfl) ⟨2171393, by rfl⟩ : syracuseStep 2895191 = 4342787) B4342787
theorem B1930127 : Blo 1929435 1930127 := bstep (se 1 (by rfl) ⟨1447595, by rfl⟩ : syracuseStep 1930127 = 2895191) B2895191
theorem B2895197 : Blo 1929435 2895197 := bbase (se 3 (by rfl) ⟨542849, by rfl⟩ : syracuseStep 2895197 = 1085699) (by norm_num)
theorem B1930131 : Blo 1929435 1930131 := bstep (se 1 (by rfl) ⟨1447598, by rfl⟩ : syracuseStep 1930131 = 2895197) B2895197
theorem B4342805 : Blo 1929435 4342805 := bbase (se 6 (by rfl) ⟨101784, by rfl⟩ : syracuseStep 4342805 = 203569) (by norm_num)
theorem B2895203 : Blo 1929435 2895203 := bstep (se 1 (by rfl) ⟨2171402, by rfl⟩ : syracuseStep 2895203 = 4342805) B4342805
theorem B1930135 : Blo 1929435 1930135 := bstep (se 1 (by rfl) ⟨1447601, by rfl⟩ : syracuseStep 1930135 = 2895203) B2895203
theorem B7328501 : Blo 1929435 7328501 := bbase (se 5 (by rfl) ⟨343523, by rfl⟩ : syracuseStep 7328501 = 687047) (by norm_num)
theorem B4885667 : Blo 1929435 4885667 := bstep (se 1 (by rfl) ⟨3664250, by rfl⟩ : syracuseStep 4885667 = 7328501) B7328501
theorem B3257111 : Blo 1929435 3257111 := bstep (se 1 (by rfl) ⟨2442833, by rfl⟩ : syracuseStep 3257111 = 4885667) B4885667
theorem B2171407 : Blo 1929435 2171407 := bstep (se 1 (by rfl) ⟨1628555, by rfl⟩ : syracuseStep 2171407 = 3257111) B3257111
theorem B2895209 : Blo 1929435 2895209 := bstep (se 2 (by rfl) ⟨1085703, by rfl⟩ : syracuseStep 2895209 = 2171407) B2171407
theorem B1930139 : Blo 1929435 1930139 := bstep (se 1 (by rfl) ⟨1447604, by rfl⟩ : syracuseStep 1930139 = 2895209) B2895209
theorem B2061145 : Blo 1929435 2061145 := bbase (se 2 (by rfl) ⟨772929, by rfl⟩ : syracuseStep 2061145 = 1545859) (by norm_num)
theorem B10992773 : Blo 1929435 10992773 := bstep (se 4 (by rfl) ⟨1030572, by rfl⟩ : syracuseStep 10992773 = 2061145) B2061145
theorem B7328515 : Blo 1929435 7328515 := bstep (se 1 (by rfl) ⟨5496386, by rfl⟩ : syracuseStep 7328515 = 10992773) B10992773
theorem B9771353 : Blo 1929435 9771353 := bstep (se 2 (by rfl) ⟨3664257, by rfl⟩ : syracuseStep 9771353 = 7328515) B7328515
theorem B6514235 : Blo 1929435 6514235 := bstep (se 1 (by rfl) ⟨4885676, by rfl⟩ : syracuseStep 6514235 = 9771353) B9771353
theorem B4342823 : Blo 1929435 4342823 := bstep (se 1 (by rfl) ⟨3257117, by rfl⟩ : syracuseStep 4342823 = 6514235) B6514235
theorem B2895215 : Blo 1929435 2895215 := bstep (se 1 (by rfl) ⟨2171411, by rfl⟩ : syracuseStep 2895215 = 4342823) B4342823
theorem B1930143 : Blo 1929435 1930143 := bstep (se 1 (by rfl) ⟨1447607, by rfl⟩ : syracuseStep 1930143 = 2895215) B2895215
theorem B2895221 : Blo 1929435 2895221 := bbase (se 5 (by rfl) ⟨135713, by rfl⟩ : syracuseStep 2895221 = 271427) (by norm_num)
theorem B1930147 : Blo 1929435 1930147 := bstep (se 1 (by rfl) ⟨1447610, by rfl⟩ : syracuseStep 1930147 = 2895221) B2895221
theorem B2748205 : Blo 1929435 2748205 := bbase (se 3 (by rfl) ⟨515288, by rfl⟩ : syracuseStep 2748205 = 1030577) (by norm_num)
theorem B3664273 : Blo 1929435 3664273 := bstep (se 2 (by rfl) ⟨1374102, by rfl⟩ : syracuseStep 3664273 = 2748205) B2748205
theorem B4885697 : Blo 1929435 4885697 := bstep (se 2 (by rfl) ⟨1832136, by rfl⟩ : syracuseStep 4885697 = 3664273) B3664273
theorem B3257131 : Blo 1929435 3257131 := bstep (se 1 (by rfl) ⟨2442848, by rfl⟩ : syracuseStep 3257131 = 4885697) B4885697
theorem B4342841 : Blo 1929435 4342841 := bstep (se 2 (by rfl) ⟨1628565, by rfl⟩ : syracuseStep 4342841 = 3257131) B3257131
theorem B2895227 : Blo 1929435 2895227 := bstep (se 1 (by rfl) ⟨2171420, by rfl⟩ : syracuseStep 2895227 = 4342841) B4342841
theorem B1930151 : Blo 1929435 1930151 := bstep (se 1 (by rfl) ⟨1447613, by rfl⟩ : syracuseStep 1930151 = 2895227) B2895227
theorem B2171425 : Blo 1929435 2171425 := bbase (se 2 (by rfl) ⟨814284, by rfl⟩ : syracuseStep 2171425 = 1628569) (by norm_num)
theorem B2895233 : Blo 1929435 2895233 := bstep (se 2 (by rfl) ⟨1085712, by rfl⟩ : syracuseStep 2895233 = 2171425) B2171425
theorem B1930155 : Blo 1929435 1930155 := bstep (se 1 (by rfl) ⟨1447616, by rfl⟩ : syracuseStep 1930155 = 2895233) B2895233
theorem B4885717 : Blo 1929435 4885717 := bbase (se 7 (by rfl) ⟨57254, by rfl⟩ : syracuseStep 4885717 = 114509) (by norm_num)
theorem B6514289 : Blo 1929435 6514289 := bstep (se 2 (by rfl) ⟨2442858, by rfl⟩ : syracuseStep 6514289 = 4885717) B4885717
theorem B4342859 : Blo 1929435 4342859 := bstep (se 1 (by rfl) ⟨3257144, by rfl⟩ : syracuseStep 4342859 = 6514289) B6514289
theorem B2895239 : Blo 1929435 2895239 := bstep (se 1 (by rfl) ⟨2171429, by rfl⟩ : syracuseStep 2895239 = 4342859) B4342859
theorem B1930159 : Blo 1929435 1930159 := bstep (se 1 (by rfl) ⟨1447619, by rfl⟩ : syracuseStep 1930159 = 2895239) B2895239
theorem B2895245 : Blo 1929435 2895245 := bbase (se 3 (by rfl) ⟨542858, by rfl⟩ : syracuseStep 2895245 = 1085717) (by norm_num)
theorem B1930163 : Blo 1929435 1930163 := bstep (se 1 (by rfl) ⟨1447622, by rfl⟩ : syracuseStep 1930163 = 2895245) B2895245
theorem B4342877 : Blo 1929435 4342877 := bbase (se 3 (by rfl) ⟨814289, by rfl⟩ : syracuseStep 4342877 = 1628579) (by norm_num)
theorem B2895251 : Blo 1929435 2895251 := bstep (se 1 (by rfl) ⟨2171438, by rfl⟩ : syracuseStep 2895251 = 4342877) B4342877
theorem B1930167 : Blo 1929435 1930167 := bstep (se 1 (by rfl) ⟨1447625, by rfl⟩ : syracuseStep 1930167 = 2895251) B2895251
theorem B3257165 : Blo 1929435 3257165 := bbase (se 3 (by rfl) ⟨610718, by rfl⟩ : syracuseStep 3257165 = 1221437) (by norm_num)
theorem B2171443 : Blo 1929435 2171443 := bstep (se 1 (by rfl) ⟨1628582, by rfl⟩ : syracuseStep 2171443 = 3257165) B3257165
theorem B2895257 : Blo 1929435 2895257 := bstep (se 2 (by rfl) ⟨1085721, by rfl⟩ : syracuseStep 2895257 = 2171443) B2171443
theorem B1930171 : Blo 1929435 1930171 := bstep (se 1 (by rfl) ⟨1447628, by rfl⟩ : syracuseStep 1930171 = 2895257) B2895257
theorem B18550613 : Blo 1929435 18550613 := bbase (se 9 (by rfl) ⟨54347, by rfl⟩ : syracuseStep 18550613 = 108695) (by norm_num)
theorem B12367075 : Blo 1929435 12367075 := bstep (se 1 (by rfl) ⟨9275306, by rfl⟩ : syracuseStep 12367075 = 18550613) B18550613
theorem B16489433 : Blo 1929435 16489433 := bstep (se 2 (by rfl) ⟨6183537, by rfl⟩ : syracuseStep 16489433 = 12367075) B12367075
theorem B10992955 : Blo 1929435 10992955 := bstep (se 1 (by rfl) ⟨8244716, by rfl⟩ : syracuseStep 10992955 = 16489433) B16489433
theorem B14657273 : Blo 1929435 14657273 := bstep (se 2 (by rfl) ⟨5496477, by rfl⟩ : syracuseStep 14657273 = 10992955) B10992955
theorem B9771515 : Blo 1929435 9771515 := bstep (se 1 (by rfl) ⟨7328636, by rfl⟩ : syracuseStep 9771515 = 14657273) B14657273
theorem B6514343 : Blo 1929435 6514343 := bstep (se 1 (by rfl) ⟨4885757, by rfl⟩ : syracuseStep 6514343 = 9771515) B9771515
theorem B4342895 : Blo 1929435 4342895 := bstep (se 1 (by rfl) ⟨3257171, by rfl⟩ : syracuseStep 4342895 = 6514343) B6514343
theorem B2895263 : Blo 1929435 2895263 := bstep (se 1 (by rfl) ⟨2171447, by rfl⟩ : syracuseStep 2895263 = 4342895) B4342895
theorem B1930175 : Blo 1929435 1930175 := bstep (se 1 (by rfl) ⟨1447631, by rfl⟩ : syracuseStep 1930175 = 2895263) B2895263
theorem B2895269 : Blo 1929435 2895269 := bbase (se 4 (by rfl) ⟨271431, by rfl⟩ : syracuseStep 2895269 = 542863) (by norm_num)
theorem B1930179 : Blo 1929435 1930179 := bstep (se 1 (by rfl) ⟨1447634, by rfl⟩ : syracuseStep 1930179 = 2895269) B2895269
theorem B2442889 : Blo 1929435 2442889 := bbase (se 2 (by rfl) ⟨916083, by rfl⟩ : syracuseStep 2442889 = 1832167) (by norm_num)
theorem B3257185 : Blo 1929435 3257185 := bstep (se 2 (by rfl) ⟨1221444, by rfl⟩ : syracuseStep 3257185 = 2442889) B2442889
theorem B4342913 : Blo 1929435 4342913 := bstep (se 2 (by rfl) ⟨1628592, by rfl⟩ : syracuseStep 4342913 = 3257185) B3257185
theorem B2895275 : Blo 1929435 2895275 := bstep (se 1 (by rfl) ⟨2171456, by rfl⟩ : syracuseStep 2895275 = 4342913) B4342913
theorem B1930183 : Blo 1929435 1930183 := bstep (se 1 (by rfl) ⟨1447637, by rfl⟩ : syracuseStep 1930183 = 2895275) B2895275
theorem B2171461 : Blo 1929435 2171461 := bbase (se 4 (by rfl) ⟨203574, by rfl⟩ : syracuseStep 2171461 = 407149) (by norm_num)
theorem B2895281 : Blo 1929435 2895281 := bstep (se 2 (by rfl) ⟨1085730, by rfl⟩ : syracuseStep 2895281 = 2171461) B2171461
theorem B1930187 : Blo 1929435 1930187 := bstep (se 1 (by rfl) ⟨1447640, by rfl⟩ : syracuseStep 1930187 = 2895281) B2895281
theorem B3664349 : Blo 1929435 3664349 := bbase (se 3 (by rfl) ⟨687065, by rfl⟩ : syracuseStep 3664349 = 1374131) (by norm_num)
theorem B2442899 : Blo 1929435 2442899 := bstep (se 1 (by rfl) ⟨1832174, by rfl⟩ : syracuseStep 2442899 = 3664349) B3664349
theorem B6514397 : Blo 1929435 6514397 := bstep (se 3 (by rfl) ⟨1221449, by rfl⟩ : syracuseStep 6514397 = 2442899) B2442899
theorem B4342931 : Blo 1929435 4342931 := bstep (se 1 (by rfl) ⟨3257198, by rfl⟩ : syracuseStep 4342931 = 6514397) B6514397
theorem B2895287 : Blo 1929435 2895287 := bstep (se 1 (by rfl) ⟨2171465, by rfl⟩ : syracuseStep 2895287 = 4342931) B4342931
theorem B1930191 : Blo 1929435 1930191 := bstep (se 1 (by rfl) ⟨1447643, by rfl⟩ : syracuseStep 1930191 = 2895287) B2895287
theorem B2895293 : Blo 1929435 2895293 := bbase (se 3 (by rfl) ⟨542867, by rfl⟩ : syracuseStep 2895293 = 1085735) (by norm_num)
theorem B1930195 : Blo 1929435 1930195 := bstep (se 1 (by rfl) ⟨1447646, by rfl⟩ : syracuseStep 1930195 = 2895293) B2895293
theorem B4342949 : Blo 1929435 4342949 := bbase (se 4 (by rfl) ⟨407151, by rfl⟩ : syracuseStep 4342949 = 814303) (by norm_num)
theorem B2895299 : Blo 1929435 2895299 := bstep (se 1 (by rfl) ⟨2171474, by rfl⟩ : syracuseStep 2895299 = 4342949) B4342949
theorem B1930199 : Blo 1929435 1930199 := bstep (se 1 (by rfl) ⟨1447649, by rfl⟩ : syracuseStep 1930199 = 2895299) B2895299
theorem B4885829 : Blo 1929435 4885829 := bbase (se 4 (by rfl) ⟨458046, by rfl⟩ : syracuseStep 4885829 = 916093) (by norm_num)
theorem B3257219 : Blo 1929435 3257219 := bstep (se 1 (by rfl) ⟨2442914, by rfl⟩ : syracuseStep 3257219 = 4885829) B4885829
theorem B2171479 : Blo 1929435 2171479 := bstep (se 1 (by rfl) ⟨1628609, by rfl⟩ : syracuseStep 2171479 = 3257219) B3257219
theorem B2895305 : Blo 1929435 2895305 := bstep (se 2 (by rfl) ⟨1085739, by rfl⟩ : syracuseStep 2895305 = 2171479) B2171479
theorem B1930203 : Blo 1929435 1930203 := bstep (se 1 (by rfl) ⟨1447652, by rfl⟩ : syracuseStep 1930203 = 2895305) B2895305
theorem B6956597 : Blo 1929435 6956597 := bbase (se 5 (by rfl) ⟨326090, by rfl⟩ : syracuseStep 6956597 = 652181) (by norm_num)
theorem B4637731 : Blo 1929435 4637731 := bstep (se 1 (by rfl) ⟨3478298, by rfl⟩ : syracuseStep 4637731 = 6956597) B6956597
theorem B6183641 : Blo 1929435 6183641 := bstep (se 2 (by rfl) ⟨2318865, by rfl⟩ : syracuseStep 6183641 = 4637731) B4637731
theorem B4122427 : Blo 1929435 4122427 := bstep (se 1 (by rfl) ⟨3091820, by rfl⟩ : syracuseStep 4122427 = 6183641) B6183641
theorem B5496569 : Blo 1929435 5496569 := bstep (se 2 (by rfl) ⟨2061213, by rfl⟩ : syracuseStep 5496569 = 4122427) B4122427
theorem B3664379 : Blo 1929435 3664379 := bstep (se 1 (by rfl) ⟨2748284, by rfl⟩ : syracuseStep 3664379 = 5496569) B5496569
theorem B9771677 : Blo 1929435 9771677 := bstep (se 3 (by rfl) ⟨1832189, by rfl⟩ : syracuseStep 9771677 = 3664379) B3664379
theorem B6514451 : Blo 1929435 6514451 := bstep (se 1 (by rfl) ⟨4885838, by rfl⟩ : syracuseStep 6514451 = 9771677) B9771677
theorem B4342967 : Blo 1929435 4342967 := bstep (se 1 (by rfl) ⟨3257225, by rfl⟩ : syracuseStep 4342967 = 6514451) B6514451
theorem B2895311 : Blo 1929435 2895311 := bstep (se 1 (by rfl) ⟨2171483, by rfl⟩ : syracuseStep 2895311 = 4342967) B4342967
theorem B1930207 : Blo 1929435 1930207 := bstep (se 1 (by rfl) ⟨1447655, by rfl⟩ : syracuseStep 1930207 = 2895311) B2895311
theorem B2895317 : Blo 1929435 2895317 := bbase (se 7 (by rfl) ⟨33929, by rfl⟩ : syracuseStep 2895317 = 67859) (by norm_num)
theorem B1930211 : Blo 1929435 1930211 := bstep (se 1 (by rfl) ⟨1447658, by rfl⟩ : syracuseStep 1930211 = 2895317) B2895317
theorem B7328789 : Blo 1929435 7328789 := bbase (se 6 (by rfl) ⟨171768, by rfl⟩ : syracuseStep 7328789 = 343537) (by norm_num)
theorem B4885859 : Blo 1929435 4885859 := bstep (se 1 (by rfl) ⟨3664394, by rfl⟩ : syracuseStep 4885859 = 7328789) B7328789
theorem B3257239 : Blo 1929435 3257239 := bstep (se 1 (by rfl) ⟨2442929, by rfl⟩ : syracuseStep 3257239 = 4885859) B4885859
theorem B4342985 : Blo 1929435 4342985 := bstep (se 2 (by rfl) ⟨1628619, by rfl⟩ : syracuseStep 4342985 = 3257239) B3257239
theorem B2895323 : Blo 1929435 2895323 := bstep (se 1 (by rfl) ⟨2171492, by rfl⟩ : syracuseStep 2895323 = 4342985) B4342985
theorem B1930215 : Blo 1929435 1930215 := bstep (se 1 (by rfl) ⟨1447661, by rfl⟩ : syracuseStep 1930215 = 2895323) B2895323
theorem B2171497 : Blo 1929435 2171497 := bbase (se 2 (by rfl) ⟨814311, by rfl⟩ : syracuseStep 2171497 = 1628623) (by norm_num)
theorem B2895329 : Blo 1929435 2895329 := bstep (se 2 (by rfl) ⟨1085748, by rfl⟩ : syracuseStep 2895329 = 2171497) B2171497
theorem B1930219 : Blo 1929435 1930219 := bstep (se 1 (by rfl) ⟨1447664, by rfl⟩ : syracuseStep 1930219 = 2895329) B2895329
theorem B4122461 : Blo 1929435 4122461 := bbase (se 3 (by rfl) ⟨772961, by rfl⟩ : syracuseStep 4122461 = 1545923) (by norm_num)
theorem B10993229 : Blo 1929435 10993229 := bstep (se 3 (by rfl) ⟨2061230, by rfl⟩ : syracuseStep 10993229 = 4122461) B4122461
theorem B7328819 : Blo 1929435 7328819 := bstep (se 1 (by rfl) ⟨5496614, by rfl⟩ : syracuseStep 7328819 = 10993229) B10993229
theorem B4885879 : Blo 1929435 4885879 := bstep (se 1 (by rfl) ⟨3664409, by rfl⟩ : syracuseStep 4885879 = 7328819) B7328819
theorem B6514505 : Blo 1929435 6514505 := bstep (se 2 (by rfl) ⟨2442939, by rfl⟩ : syracuseStep 6514505 = 4885879) B4885879
theorem B4343003 : Blo 1929435 4343003 := bstep (se 1 (by rfl) ⟨3257252, by rfl⟩ : syracuseStep 4343003 = 6514505) B6514505
theorem B2895335 : Blo 1929435 2895335 := bstep (se 1 (by rfl) ⟨2171501, by rfl⟩ : syracuseStep 2895335 = 4343003) B4343003
theorem B1930223 : Blo 1929435 1930223 := bstep (se 1 (by rfl) ⟨1447667, by rfl⟩ : syracuseStep 1930223 = 2895335) B2895335
theorem B2895341 : Blo 1929435 2895341 := bbase (se 3 (by rfl) ⟨542876, by rfl⟩ : syracuseStep 2895341 = 1085753) (by norm_num)
theorem B1930227 : Blo 1929435 1930227 := bstep (se 1 (by rfl) ⟨1447670, by rfl⟩ : syracuseStep 1930227 = 2895341) B2895341
theorem B4343021 : Blo 1929435 4343021 := bbase (se 3 (by rfl) ⟨814316, by rfl⟩ : syracuseStep 4343021 = 1628633) (by norm_num)
theorem B2895347 : Blo 1929435 2895347 := bstep (se 1 (by rfl) ⟨2171510, by rfl⟩ : syracuseStep 2895347 = 4343021) B4343021
theorem B1930231 : Blo 1929435 1930231 := bstep (se 1 (by rfl) ⟨1447673, by rfl⟩ : syracuseStep 1930231 = 2895347) B2895347
theorem B2748325 : Blo 1929435 2748325 := bbase (se 4 (by rfl) ⟨257655, by rfl⟩ : syracuseStep 2748325 = 515311) (by norm_num)
theorem B3664433 : Blo 1929435 3664433 := bstep (se 2 (by rfl) ⟨1374162, by rfl⟩ : syracuseStep 3664433 = 2748325) B2748325
theorem B2442955 : Blo 1929435 2442955 := bstep (se 1 (by rfl) ⟨1832216, by rfl⟩ : syracuseStep 2442955 = 3664433) B3664433
theorem B3257273 : Blo 1929435 3257273 := bstep (se 2 (by rfl) ⟨1221477, by rfl⟩ : syracuseStep 3257273 = 2442955) B2442955
theorem B2171515 : Blo 1929435 2171515 := bstep (se 1 (by rfl) ⟨1628636, by rfl⟩ : syracuseStep 2171515 = 3257273) B3257273
theorem B2895353 : Blo 1929435 2895353 := bstep (se 2 (by rfl) ⟨1085757, by rfl⟩ : syracuseStep 2895353 = 2171515) B2171515
theorem B1930235 : Blo 1929435 1930235 := bstep (se 1 (by rfl) ⟨1447676, by rfl⟩ : syracuseStep 1930235 = 2895353) B2895353
theorem B17849429 : Blo 1929435 17849429 := bbase (se 8 (by rfl) ⟨104586, by rfl⟩ : syracuseStep 17849429 = 209173) (by norm_num)
theorem B11899619 : Blo 1929435 11899619 := bstep (se 1 (by rfl) ⟨8924714, by rfl⟩ : syracuseStep 11899619 = 17849429) B17849429
theorem B7933079 : Blo 1929435 7933079 := bstep (se 1 (by rfl) ⟨5949809, by rfl⟩ : syracuseStep 7933079 = 11899619) B11899619
theorem B5288719 : Blo 1929435 5288719 := bstep (se 1 (by rfl) ⟨3966539, by rfl⟩ : syracuseStep 5288719 = 7933079) B7933079
theorem B7051625 : Blo 1929435 7051625 := bstep (se 2 (by rfl) ⟨2644359, by rfl⟩ : syracuseStep 7051625 = 5288719) B5288719
theorem B4701083 : Blo 1929435 4701083 := bstep (se 1 (by rfl) ⟨3525812, by rfl⟩ : syracuseStep 4701083 = 7051625) B7051625
theorem B12536221 : Blo 1929435 12536221 := bstep (se 3 (by rfl) ⟨2350541, by rfl⟩ : syracuseStep 12536221 = 4701083) B4701083
theorem B16714961 : Blo 1929435 16714961 := bstep (se 2 (by rfl) ⟨6268110, by rfl⟩ : syracuseStep 16714961 = 12536221) B12536221
theorem B11143307 : Blo 1929435 11143307 := bstep (se 1 (by rfl) ⟨8357480, by rfl⟩ : syracuseStep 11143307 = 16714961) B16714961
theorem B7428871 : Blo 1929435 7428871 := bstep (se 1 (by rfl) ⟨5571653, by rfl⟩ : syracuseStep 7428871 = 11143307) B11143307
theorem B9905161 : Blo 1929435 9905161 := bstep (se 2 (by rfl) ⟨3714435, by rfl⟩ : syracuseStep 9905161 = 7428871) B7428871
theorem B13206881 : Blo 1929435 13206881 := bstep (se 2 (by rfl) ⟨4952580, by rfl⟩ : syracuseStep 13206881 = 9905161) B9905161
theorem B8804587 : Blo 1929435 8804587 := bstep (se 1 (by rfl) ⟨6603440, by rfl⟩ : syracuseStep 8804587 = 13206881) B13206881
theorem B11739449 : Blo 1929435 11739449 := bstep (se 2 (by rfl) ⟨4402293, by rfl⟩ : syracuseStep 11739449 = 8804587) B8804587
theorem B31305197 : Blo 1929435 31305197 := bstep (se 3 (by rfl) ⟨5869724, by rfl⟩ : syracuseStep 31305197 = 11739449) B11739449
theorem B20870131 : Blo 1929435 20870131 := bstep (se 1 (by rfl) ⟨15652598, by rfl⟩ : syracuseStep 20870131 = 31305197) B31305197
theorem B27826841 : Blo 1929435 27826841 := bstep (se 2 (by rfl) ⟨10435065, by rfl⟩ : syracuseStep 27826841 = 20870131) B20870131
theorem B74204909 : Blo 1929435 74204909 := bstep (se 3 (by rfl) ⟨13913420, by rfl⟩ : syracuseStep 74204909 = 27826841) B27826841
theorem B49469939 : Blo 1929435 49469939 := bstep (se 1 (by rfl) ⟨37102454, by rfl⟩ : syracuseStep 49469939 = 74204909) B74204909
theorem B32979959 : Blo 1929435 32979959 := bstep (se 1 (by rfl) ⟨24734969, by rfl⟩ : syracuseStep 32979959 = 49469939) B49469939
theorem B21986639 : Blo 1929435 21986639 := bstep (se 1 (by rfl) ⟨16489979, by rfl⟩ : syracuseStep 21986639 = 32979959) B32979959
theorem B14657759 : Blo 1929435 14657759 := bstep (se 1 (by rfl) ⟨10993319, by rfl⟩ : syracuseStep 14657759 = 21986639) B21986639
theorem B9771839 : Blo 1929435 9771839 := bstep (se 1 (by rfl) ⟨7328879, by rfl⟩ : syracuseStep 9771839 = 14657759) B14657759
theorem B6514559 : Blo 1929435 6514559 := bstep (se 1 (by rfl) ⟨4885919, by rfl⟩ : syracuseStep 6514559 = 9771839) B9771839
theorem B4343039 : Blo 1929435 4343039 := bstep (se 1 (by rfl) ⟨3257279, by rfl⟩ : syracuseStep 4343039 = 6514559) B6514559
theorem B2895359 : Blo 1929435 2895359 := bstep (se 1 (by rfl) ⟨2171519, by rfl⟩ : syracuseStep 2895359 = 4343039) B4343039
theorem B1930239 : Blo 1929435 1930239 := bstep (se 1 (by rfl) ⟨1447679, by rfl⟩ : syracuseStep 1930239 = 2895359) B2895359
theorem B2895365 : Blo 1929435 2895365 := bbase (se 4 (by rfl) ⟨271440, by rfl⟩ : syracuseStep 2895365 = 542881) (by norm_num)
theorem B1930243 : Blo 1929435 1930243 := bstep (se 1 (by rfl) ⟨1447682, by rfl⟩ : syracuseStep 1930243 = 2895365) B2895365
theorem B3257293 : Blo 1929435 3257293 := bbase (se 3 (by rfl) ⟨610742, by rfl⟩ : syracuseStep 3257293 = 1221485) (by norm_num)
theorem B4343057 : Blo 1929435 4343057 := bstep (se 2 (by rfl) ⟨1628646, by rfl⟩ : syracuseStep 4343057 = 3257293) B3257293
theorem B2895371 : Blo 1929435 2895371 := bstep (se 1 (by rfl) ⟨2171528, by rfl⟩ : syracuseStep 2895371 = 4343057) B4343057
theorem B1930247 : Blo 1929435 1930247 := bstep (se 1 (by rfl) ⟨1447685, by rfl⟩ : syracuseStep 1930247 = 2895371) B2895371
theorem B2171533 : Blo 1929435 2171533 := bbase (se 3 (by rfl) ⟨407162, by rfl⟩ : syracuseStep 2171533 = 814325) (by norm_num)
theorem B2895377 : Blo 1929435 2895377 := bstep (se 2 (by rfl) ⟨1085766, by rfl⟩ : syracuseStep 2895377 = 2171533) B2171533
theorem B1930251 : Blo 1929435 1930251 := bstep (se 1 (by rfl) ⟨1447688, by rfl⟩ : syracuseStep 1930251 = 2895377) B2895377
theorem B6514613 : Blo 1929435 6514613 := bbase (se 5 (by rfl) ⟨305372, by rfl⟩ : syracuseStep 6514613 = 610745) (by norm_num)
theorem B4343075 : Blo 1929435 4343075 := bstep (se 1 (by rfl) ⟨3257306, by rfl⟩ : syracuseStep 4343075 = 6514613) B6514613
theorem B2895383 : Blo 1929435 2895383 := bstep (se 1 (by rfl) ⟨2171537, by rfl⟩ : syracuseStep 2895383 = 4343075) B4343075
theorem B1930255 : Blo 1929435 1930255 := bstep (se 1 (by rfl) ⟨1447691, by rfl⟩ : syracuseStep 1930255 = 2895383) B2895383
theorem B2895389 : Blo 1929435 2895389 := bbase (se 3 (by rfl) ⟨542885, by rfl⟩ : syracuseStep 2895389 = 1085771) (by norm_num)
theorem B1930259 : Blo 1929435 1930259 := bstep (se 1 (by rfl) ⟨1447694, by rfl⟩ : syracuseStep 1930259 = 2895389) B2895389
theorem B4343093 : Blo 1929435 4343093 := bbase (se 5 (by rfl) ⟨203582, by rfl⟩ : syracuseStep 4343093 = 407165) (by norm_num)
theorem B2895395 : Blo 1929435 2895395 := bstep (se 1 (by rfl) ⟨2171546, by rfl⟩ : syracuseStep 2895395 = 4343093) B4343093
theorem B1930263 : Blo 1929435 1930263 := bstep (se 1 (by rfl) ⟨1447697, by rfl⟩ : syracuseStep 1930263 = 2895395) B2895395
theorem B2608805 : Blo 1929435 2608805 := bbase (se 4 (by rfl) ⟨244575, by rfl⟩ : syracuseStep 2608805 = 489151) (by norm_num)
theorem B6956813 : Blo 1929435 6956813 := bstep (se 3 (by rfl) ⟨1304402, by rfl⟩ : syracuseStep 6956813 = 2608805) B2608805
theorem B18551501 : Blo 1929435 18551501 := bstep (se 3 (by rfl) ⟨3478406, by rfl⟩ : syracuseStep 18551501 = 6956813) B6956813
theorem B12367667 : Blo 1929435 12367667 := bstep (se 1 (by rfl) ⟨9275750, by rfl⟩ : syracuseStep 12367667 = 18551501) B18551501
theorem B8245111 : Blo 1929435 8245111 := bstep (se 1 (by rfl) ⟨6183833, by rfl⟩ : syracuseStep 8245111 = 12367667) B12367667
theorem B10993481 : Blo 1929435 10993481 := bstep (se 2 (by rfl) ⟨4122555, by rfl⟩ : syracuseStep 10993481 = 8245111) B8245111
theorem B7328987 : Blo 1929435 7328987 := bstep (se 1 (by rfl) ⟨5496740, by rfl⟩ : syracuseStep 7328987 = 10993481) B10993481
theorem B4885991 : Blo 1929435 4885991 := bstep (se 1 (by rfl) ⟨3664493, by rfl⟩ : syracuseStep 4885991 = 7328987) B7328987
theorem B3257327 : Blo 1929435 3257327 := bstep (se 1 (by rfl) ⟨2442995, by rfl⟩ : syracuseStep 3257327 = 4885991) B4885991
theorem B2171551 : Blo 1929435 2171551 := bstep (se 1 (by rfl) ⟨1628663, by rfl⟩ : syracuseStep 2171551 = 3257327) B3257327
theorem B2895401 : Blo 1929435 2895401 := bstep (se 2 (by rfl) ⟨1085775, by rfl⟩ : syracuseStep 2895401 = 2171551) B2171551
theorem B1930267 : Blo 1929435 1930267 := bstep (se 1 (by rfl) ⟨1447700, by rfl⟩ : syracuseStep 1930267 = 2895401) B2895401
theorem B13913653 : Blo 1929435 13913653 := bbase (se 5 (by rfl) ⟨652202, by rfl⟩ : syracuseStep 13913653 = 1304405) (by norm_num)
theorem B18551537 : Blo 1929435 18551537 := bstep (se 2 (by rfl) ⟨6956826, by rfl⟩ : syracuseStep 18551537 = 13913653) B13913653
theorem B12367691 : Blo 1929435 12367691 := bstep (se 1 (by rfl) ⟨9275768, by rfl⟩ : syracuseStep 12367691 = 18551537) B18551537
theorem B8245127 : Blo 1929435 8245127 := bstep (se 1 (by rfl) ⟨6183845, by rfl⟩ : syracuseStep 8245127 = 12367691) B12367691
theorem B5496751 : Blo 1929435 5496751 := bstep (se 1 (by rfl) ⟨4122563, by rfl⟩ : syracuseStep 5496751 = 8245127) B8245127
theorem B7329001 : Blo 1929435 7329001 := bstep (se 2 (by rfl) ⟨2748375, by rfl⟩ : syracuseStep 7329001 = 5496751) B5496751
theorem B9772001 : Blo 1929435 9772001 := bstep (se 2 (by rfl) ⟨3664500, by rfl⟩ : syracuseStep 9772001 = 7329001) B7329001
theorem B6514667 : Blo 1929435 6514667 := bstep (se 1 (by rfl) ⟨4886000, by rfl⟩ : syracuseStep 6514667 = 9772001) B9772001
theorem B4343111 : Blo 1929435 4343111 := bstep (se 1 (by rfl) ⟨3257333, by rfl⟩ : syracuseStep 4343111 = 6514667) B6514667
theorem B2895407 : Blo 1929435 2895407 := bstep (se 1 (by rfl) ⟨2171555, by rfl⟩ : syracuseStep 2895407 = 4343111) B4343111
theorem B1930271 : Blo 1929435 1930271 := bstep (se 1 (by rfl) ⟨1447703, by rfl⟩ : syracuseStep 1930271 = 2895407) B2895407
theorem B2895413 : Blo 1929435 2895413 := bbase (se 5 (by rfl) ⟨135722, by rfl⟩ : syracuseStep 2895413 = 271445) (by norm_num)
theorem B1930275 : Blo 1929435 1930275 := bstep (se 1 (by rfl) ⟨1447706, by rfl⟩ : syracuseStep 1930275 = 2895413) B2895413
theorem B4886021 : Blo 1929435 4886021 := bbase (se 4 (by rfl) ⟨458064, by rfl⟩ : syracuseStep 4886021 = 916129) (by norm_num)
theorem B3257347 : Blo 1929435 3257347 := bstep (se 1 (by rfl) ⟨2443010, by rfl⟩ : syracuseStep 3257347 = 4886021) B4886021
theorem B4343129 : Blo 1929435 4343129 := bstep (se 2 (by rfl) ⟨1628673, by rfl⟩ : syracuseStep 4343129 = 3257347) B3257347
theorem B2895419 : Blo 1929435 2895419 := bstep (se 1 (by rfl) ⟨2171564, by rfl⟩ : syracuseStep 2895419 = 4343129) B4343129
theorem B1930279 : Blo 1929435 1930279 := bstep (se 1 (by rfl) ⟨1447709, by rfl⟩ : syracuseStep 1930279 = 2895419) B2895419
theorem B2171569 : Blo 1929435 2171569 := bbase (se 2 (by rfl) ⟨814338, by rfl⟩ : syracuseStep 2171569 = 1628677) (by norm_num)
theorem B2895425 : Blo 1929435 2895425 := bstep (se 2 (by rfl) ⟨1085784, by rfl⟩ : syracuseStep 2895425 = 2171569) B2171569
theorem B1930283 : Blo 1929435 1930283 := bstep (se 1 (by rfl) ⟨1447712, by rfl⟩ : syracuseStep 1930283 = 2895425) B2895425
theorem B3091949 : Blo 1929435 3091949 := bbase (se 3 (by rfl) ⟨579740, by rfl⟩ : syracuseStep 3091949 = 1159481) (by norm_num)
theorem B2061299 : Blo 1929435 2061299 := bstep (se 1 (by rfl) ⟨1545974, by rfl⟩ : syracuseStep 2061299 = 3091949) B3091949
theorem B5496797 : Blo 1929435 5496797 := bstep (se 3 (by rfl) ⟨1030649, by rfl⟩ : syracuseStep 5496797 = 2061299) B2061299
theorem B3664531 : Blo 1929435 3664531 := bstep (se 1 (by rfl) ⟨2748398, by rfl⟩ : syracuseStep 3664531 = 5496797) B5496797
theorem B4886041 : Blo 1929435 4886041 := bstep (se 2 (by rfl) ⟨1832265, by rfl⟩ : syracuseStep 4886041 = 3664531) B3664531
theorem B6514721 : Blo 1929435 6514721 := bstep (se 2 (by rfl) ⟨2443020, by rfl⟩ : syracuseStep 6514721 = 4886041) B4886041
theorem B4343147 : Blo 1929435 4343147 := bstep (se 1 (by rfl) ⟨3257360, by rfl⟩ : syracuseStep 4343147 = 6514721) B6514721
theorem B2895431 : Blo 1929435 2895431 := bstep (se 1 (by rfl) ⟨2171573, by rfl⟩ : syracuseStep 2895431 = 4343147) B4343147
theorem B1930287 : Blo 1929435 1930287 := bstep (se 1 (by rfl) ⟨1447715, by rfl⟩ : syracuseStep 1930287 = 2895431) B2895431
theorem B2895437 : Blo 1929435 2895437 := bbase (se 3 (by rfl) ⟨542894, by rfl⟩ : syracuseStep 2895437 = 1085789) (by norm_num)
theorem B1930291 : Blo 1929435 1930291 := bstep (se 1 (by rfl) ⟨1447718, by rfl⟩ : syracuseStep 1930291 = 2895437) B2895437
theorem B4343165 : Blo 1929435 4343165 := bbase (se 3 (by rfl) ⟨814343, by rfl⟩ : syracuseStep 4343165 = 1628687) (by norm_num)
theorem B2895443 : Blo 1929435 2895443 := bstep (se 1 (by rfl) ⟨2171582, by rfl⟩ : syracuseStep 2895443 = 4343165) B4343165
theorem B1930295 : Blo 1929435 1930295 := bstep (se 1 (by rfl) ⟨1447721, by rfl⟩ : syracuseStep 1930295 = 2895443) B2895443
theorem B3257381 : Blo 1929435 3257381 := bbase (se 4 (by rfl) ⟨305379, by rfl⟩ : syracuseStep 3257381 = 610759) (by norm_num)
theorem B2171587 : Blo 1929435 2171587 := bstep (se 1 (by rfl) ⟨1628690, by rfl⟩ : syracuseStep 2171587 = 3257381) B3257381
theorem B2895449 : Blo 1929435 2895449 := bstep (se 2 (by rfl) ⟨1085793, by rfl⟩ : syracuseStep 2895449 = 2171587) B2171587
theorem B1930299 : Blo 1929435 1930299 := bstep (se 1 (by rfl) ⟨1447724, by rfl⟩ : syracuseStep 1930299 = 2895449) B2895449
theorem B2748421 : Blo 1929435 2748421 := bbase (se 4 (by rfl) ⟨257664, by rfl⟩ : syracuseStep 2748421 = 515329) (by norm_num)
theorem B14658245 : Blo 1929435 14658245 := bstep (se 4 (by rfl) ⟨1374210, by rfl⟩ : syracuseStep 14658245 = 2748421) B2748421
theorem B9772163 : Blo 1929435 9772163 := bstep (se 1 (by rfl) ⟨7329122, by rfl⟩ : syracuseStep 9772163 = 14658245) B14658245
theorem B6514775 : Blo 1929435 6514775 := bstep (se 1 (by rfl) ⟨4886081, by rfl⟩ : syracuseStep 6514775 = 9772163) B9772163
theorem B4343183 : Blo 1929435 4343183 := bstep (se 1 (by rfl) ⟨3257387, by rfl⟩ : syracuseStep 4343183 = 6514775) B6514775
theorem B2895455 : Blo 1929435 2895455 := bstep (se 1 (by rfl) ⟨2171591, by rfl⟩ : syracuseStep 2895455 = 4343183) B4343183
theorem B1930303 : Blo 1929435 1930303 := bstep (se 1 (by rfl) ⟨1447727, by rfl⟩ : syracuseStep 1930303 = 2895455) B2895455
theorem B2895461 : Blo 1929435 2895461 := bbase (se 4 (by rfl) ⟨271449, by rfl⟩ : syracuseStep 2895461 = 542899) (by norm_num)
theorem B1930307 : Blo 1929435 1930307 := bstep (se 1 (by rfl) ⟨1447730, by rfl⟩ : syracuseStep 1930307 = 2895461) B2895461
theorem B2061325 : Blo 1929435 2061325 := bbase (se 3 (by rfl) ⟨386498, by rfl⟩ : syracuseStep 2061325 = 772997) (by norm_num)
theorem B2748433 : Blo 1929435 2748433 := bstep (se 2 (by rfl) ⟨1030662, by rfl⟩ : syracuseStep 2748433 = 2061325) B2061325
theorem B3664577 : Blo 1929435 3664577 := bstep (se 2 (by rfl) ⟨1374216, by rfl⟩ : syracuseStep 3664577 = 2748433) B2748433
theorem B2443051 : Blo 1929435 2443051 := bstep (se 1 (by rfl) ⟨1832288, by rfl⟩ : syracuseStep 2443051 = 3664577) B3664577
theorem B3257401 : Blo 1929435 3257401 := bstep (se 2 (by rfl) ⟨1221525, by rfl⟩ : syracuseStep 3257401 = 2443051) B2443051
theorem B4343201 : Blo 1929435 4343201 := bstep (se 2 (by rfl) ⟨1628700, by rfl⟩ : syracuseStep 4343201 = 3257401) B3257401
theorem B2895467 : Blo 1929435 2895467 := bstep (se 1 (by rfl) ⟨2171600, by rfl⟩ : syracuseStep 2895467 = 4343201) B4343201
theorem B1930311 : Blo 1929435 1930311 := bstep (se 1 (by rfl) ⟨1447733, by rfl⟩ : syracuseStep 1930311 = 2895467) B2895467
theorem B2171605 : Blo 1929435 2171605 := bbase (se 7 (by rfl) ⟨25448, by rfl⟩ : syracuseStep 2171605 = 50897) (by norm_num)
theorem B2895473 : Blo 1929435 2895473 := bstep (se 2 (by rfl) ⟨1085802, by rfl⟩ : syracuseStep 2895473 = 2171605) B2171605
theorem B1930315 : Blo 1929435 1930315 := bstep (se 1 (by rfl) ⟨1447736, by rfl⟩ : syracuseStep 1930315 = 2895473) B2895473
theorem B2443061 : Blo 1929435 2443061 := bbase (se 5 (by rfl) ⟨114518, by rfl⟩ : syracuseStep 2443061 = 229037) (by norm_num)
theorem B6514829 : Blo 1929435 6514829 := bstep (se 3 (by rfl) ⟨1221530, by rfl⟩ : syracuseStep 6514829 = 2443061) B2443061
theorem B4343219 : Blo 1929435 4343219 := bstep (se 1 (by rfl) ⟨3257414, by rfl⟩ : syracuseStep 4343219 = 6514829) B6514829
theorem B2895479 : Blo 1929435 2895479 := bstep (se 1 (by rfl) ⟨2171609, by rfl⟩ : syracuseStep 2895479 = 4343219) B4343219
theorem B1930319 : Blo 1929435 1930319 := bstep (se 1 (by rfl) ⟨1447739, by rfl⟩ : syracuseStep 1930319 = 2895479) B2895479
theorem B2895485 : Blo 1929435 2895485 := bbase (se 3 (by rfl) ⟨542903, by rfl⟩ : syracuseStep 2895485 = 1085807) (by norm_num)
theorem B1930323 : Blo 1929435 1930323 := bstep (se 1 (by rfl) ⟨1447742, by rfl⟩ : syracuseStep 1930323 = 2895485) B2895485
theorem B4343237 : Blo 1929435 4343237 := bbase (se 4 (by rfl) ⟨407178, by rfl⟩ : syracuseStep 4343237 = 814357) (by norm_num)
theorem B2895491 : Blo 1929435 2895491 := bstep (se 1 (by rfl) ⟨2171618, by rfl⟩ : syracuseStep 2895491 = 4343237) B4343237
theorem B1930327 : Blo 1929435 1930327 := bstep (se 1 (by rfl) ⟨1447745, by rfl⟩ : syracuseStep 1930327 = 2895491) B2895491
theorem B2261729 : Blo 1929435 2261729 := bbase (se 2 (by rfl) ⟨848148, by rfl⟩ : syracuseStep 2261729 = 1696297) (by norm_num)
theorem B6031277 : Blo 1929435 6031277 := bstep (se 3 (by rfl) ⟨1130864, by rfl⟩ : syracuseStep 6031277 = 2261729) B2261729
theorem B4020851 : Blo 1929435 4020851 := bstep (se 1 (by rfl) ⟨3015638, by rfl⟩ : syracuseStep 4020851 = 6031277) B6031277
theorem B10722269 : Blo 1929435 10722269 := bstep (se 3 (by rfl) ⟨2010425, by rfl⟩ : syracuseStep 10722269 = 4020851) B4020851
theorem B7148179 : Blo 1929435 7148179 := bstep (se 1 (by rfl) ⟨5361134, by rfl⟩ : syracuseStep 7148179 = 10722269) B10722269
theorem B9530905 : Blo 1929435 9530905 := bstep (se 2 (by rfl) ⟨3574089, by rfl⟩ : syracuseStep 9530905 = 7148179) B7148179
theorem B12707873 : Blo 1929435 12707873 := bstep (se 2 (by rfl) ⟨4765452, by rfl⟩ : syracuseStep 12707873 = 9530905) B9530905
theorem B8471915 : Blo 1929435 8471915 := bstep (se 1 (by rfl) ⟨6353936, by rfl⟩ : syracuseStep 8471915 = 12707873) B12707873
theorem B5647943 : Blo 1929435 5647943 := bstep (se 1 (by rfl) ⟨4235957, by rfl⟩ : syracuseStep 5647943 = 8471915) B8471915
theorem B3765295 : Blo 1929435 3765295 := bstep (se 1 (by rfl) ⟨2823971, by rfl⟩ : syracuseStep 3765295 = 5647943) B5647943
theorem B5020393 : Blo 1929435 5020393 := bstep (se 2 (by rfl) ⟨1882647, by rfl⟩ : syracuseStep 5020393 = 3765295) B3765295
theorem B6693857 : Blo 1929435 6693857 := bstep (se 2 (by rfl) ⟨2510196, by rfl⟩ : syracuseStep 6693857 = 5020393) B5020393
theorem B4462571 : Blo 1929435 4462571 := bstep (se 1 (by rfl) ⟨3346928, by rfl⟩ : syracuseStep 4462571 = 6693857) B6693857
theorem B11900189 : Blo 1929435 11900189 := bstep (se 3 (by rfl) ⟨2231285, by rfl⟩ : syracuseStep 11900189 = 4462571) B4462571
theorem B7933459 : Blo 1929435 7933459 := bstep (se 1 (by rfl) ⟨5950094, by rfl⟩ : syracuseStep 7933459 = 11900189) B11900189
theorem B10577945 : Blo 1929435 10577945 := bstep (se 2 (by rfl) ⟨3966729, by rfl⟩ : syracuseStep 10577945 = 7933459) B7933459
theorem B7051963 : Blo 1929435 7051963 := bstep (se 1 (by rfl) ⟨5288972, by rfl⟩ : syracuseStep 7051963 = 10577945) B10577945
theorem B9402617 : Blo 1929435 9402617 := bstep (se 2 (by rfl) ⟨3525981, by rfl⟩ : syracuseStep 9402617 = 7051963) B7051963
theorem B6268411 : Blo 1929435 6268411 := bstep (se 1 (by rfl) ⟨4701308, by rfl⟩ : syracuseStep 6268411 = 9402617) B9402617
theorem B33431525 : Blo 1929435 33431525 := bstep (se 4 (by rfl) ⟨3134205, by rfl⟩ : syracuseStep 33431525 = 6268411) B6268411
theorem B22287683 : Blo 1929435 22287683 := bstep (se 1 (by rfl) ⟨16715762, by rfl⟩ : syracuseStep 22287683 = 33431525) B33431525
theorem B59433821 : Blo 1929435 59433821 := bstep (se 3 (by rfl) ⟨11143841, by rfl⟩ : syracuseStep 59433821 = 22287683) B22287683
theorem B39622547 : Blo 1929435 39622547 := bstep (se 1 (by rfl) ⟨29716910, by rfl⟩ : syracuseStep 39622547 = 59433821) B59433821
theorem B26415031 : Blo 1929435 26415031 := bstep (se 1 (by rfl) ⟨19811273, by rfl⟩ : syracuseStep 26415031 = 39622547) B39622547
theorem B35220041 : Blo 1929435 35220041 := bstep (se 2 (by rfl) ⟨13207515, by rfl⟩ : syracuseStep 35220041 = 26415031) B26415031
theorem B23480027 : Blo 1929435 23480027 := bstep (se 1 (by rfl) ⟨17610020, by rfl⟩ : syracuseStep 23480027 = 35220041) B35220041
theorem B15653351 : Blo 1929435 15653351 := bstep (se 1 (by rfl) ⟨11740013, by rfl⟩ : syracuseStep 15653351 = 23480027) B23480027
theorem B10435567 : Blo 1929435 10435567 := bstep (se 1 (by rfl) ⟨7826675, by rfl⟩ : syracuseStep 10435567 = 15653351) B15653351
theorem B13914089 : Blo 1929435 13914089 := bstep (se 2 (by rfl) ⟨5217783, by rfl⟩ : syracuseStep 13914089 = 10435567) B10435567
theorem B9276059 : Blo 1929435 9276059 := bstep (se 1 (by rfl) ⟨6957044, by rfl⟩ : syracuseStep 9276059 = 13914089) B13914089
theorem B6184039 : Blo 1929435 6184039 := bstep (se 1 (by rfl) ⟨4638029, by rfl⟩ : syracuseStep 6184039 = 9276059) B9276059
theorem B8245385 : Blo 1929435 8245385 := bstep (se 2 (by rfl) ⟨3092019, by rfl⟩ : syracuseStep 8245385 = 6184039) B6184039
theorem B5496923 : Blo 1929435 5496923 := bstep (se 1 (by rfl) ⟨4122692, by rfl⟩ : syracuseStep 5496923 = 8245385) B8245385
theorem B3664615 : Blo 1929435 3664615 := bstep (se 1 (by rfl) ⟨2748461, by rfl⟩ : syracuseStep 3664615 = 5496923) B5496923
theorem B4886153 : Blo 1929435 4886153 := bstep (se 2 (by rfl) ⟨1832307, by rfl⟩ : syracuseStep 4886153 = 3664615) B3664615
theorem B3257435 : Blo 1929435 3257435 := bstep (se 1 (by rfl) ⟨2443076, by rfl⟩ : syracuseStep 3257435 = 4886153) B4886153
theorem B2171623 : Blo 1929435 2171623 := bstep (se 1 (by rfl) ⟨1628717, by rfl⟩ : syracuseStep 2171623 = 3257435) B3257435
theorem B2895497 : Blo 1929435 2895497 := bstep (se 2 (by rfl) ⟨1085811, by rfl⟩ : syracuseStep 2895497 = 2171623) B2171623
theorem B1930331 : Blo 1929435 1930331 := bstep (se 1 (by rfl) ⟨1447748, by rfl⟩ : syracuseStep 1930331 = 2895497) B2895497
theorem B9772325 : Blo 1929435 9772325 := bbase (se 4 (by rfl) ⟨916155, by rfl⟩ : syracuseStep 9772325 = 1832311) (by norm_num)
theorem B6514883 : Blo 1929435 6514883 := bstep (se 1 (by rfl) ⟨4886162, by rfl⟩ : syracuseStep 6514883 = 9772325) B9772325
theorem B4343255 : Blo 1929435 4343255 := bstep (se 1 (by rfl) ⟨3257441, by rfl⟩ : syracuseStep 4343255 = 6514883) B6514883
theorem B2895503 : Blo 1929435 2895503 := bstep (se 1 (by rfl) ⟨2171627, by rfl⟩ : syracuseStep 2895503 = 4343255) B4343255
theorem B1930335 : Blo 1929435 1930335 := bstep (se 1 (by rfl) ⟨1447751, by rfl⟩ : syracuseStep 1930335 = 2895503) B2895503
theorem B2895509 : Blo 1929435 2895509 := bbase (se 6 (by rfl) ⟨67863, by rfl⟩ : syracuseStep 2895509 = 135727) (by norm_num)
theorem B1930339 : Blo 1929435 1930339 := bstep (se 1 (by rfl) ⟨1447754, by rfl⟩ : syracuseStep 1930339 = 2895509) B2895509
theorem B11740085 : Blo 1929435 11740085 := bbase (se 5 (by rfl) ⟨550316, by rfl⟩ : syracuseStep 11740085 = 1100633) (by norm_num)
theorem B7826723 : Blo 1929435 7826723 := bstep (se 1 (by rfl) ⟨5870042, by rfl⟩ : syracuseStep 7826723 = 11740085) B11740085
theorem B5217815 : Blo 1929435 5217815 := bstep (se 1 (by rfl) ⟨3913361, by rfl⟩ : syracuseStep 5217815 = 7826723) B7826723
theorem B13914173 : Blo 1929435 13914173 := bstep (se 3 (by rfl) ⟨2608907, by rfl⟩ : syracuseStep 13914173 = 5217815) B5217815
theorem B9276115 : Blo 1929435 9276115 := bstep (se 1 (by rfl) ⟨6957086, by rfl⟩ : syracuseStep 9276115 = 13914173) B13914173
theorem B12368153 : Blo 1929435 12368153 := bstep (se 2 (by rfl) ⟨4638057, by rfl⟩ : syracuseStep 12368153 = 9276115) B9276115
theorem B8245435 : Blo 1929435 8245435 := bstep (se 1 (by rfl) ⟨6184076, by rfl⟩ : syracuseStep 8245435 = 12368153) B12368153
theorem B10993913 : Blo 1929435 10993913 := bstep (se 2 (by rfl) ⟨4122717, by rfl⟩ : syracuseStep 10993913 = 8245435) B8245435
theorem B7329275 : Blo 1929435 7329275 := bstep (se 1 (by rfl) ⟨5496956, by rfl⟩ : syracuseStep 7329275 = 10993913) B10993913
theorem B4886183 : Blo 1929435 4886183 := bstep (se 1 (by rfl) ⟨3664637, by rfl⟩ : syracuseStep 4886183 = 7329275) B7329275
theorem B3257455 : Blo 1929435 3257455 := bstep (se 1 (by rfl) ⟨2443091, by rfl⟩ : syracuseStep 3257455 = 4886183) B4886183
theorem B4343273 : Blo 1929435 4343273 := bstep (se 2 (by rfl) ⟨1628727, by rfl⟩ : syracuseStep 4343273 = 3257455) B3257455
theorem B2895515 : Blo 1929435 2895515 := bstep (se 1 (by rfl) ⟨2171636, by rfl⟩ : syracuseStep 2895515 = 4343273) B4343273
theorem B1930343 : Blo 1929435 1930343 := bstep (se 1 (by rfl) ⟨1447757, by rfl⟩ : syracuseStep 1930343 = 2895515) B2895515
theorem B2171641 : Blo 1929435 2171641 := bbase (se 2 (by rfl) ⟨814365, by rfl⟩ : syracuseStep 2171641 = 1628731) (by norm_num)
theorem B2895521 : Blo 1929435 2895521 := bstep (se 2 (by rfl) ⟨1085820, by rfl⟩ : syracuseStep 2895521 = 2171641) B2171641
theorem B1930347 : Blo 1929435 1930347 := bstep (se 1 (by rfl) ⟨1447760, by rfl⟩ : syracuseStep 1930347 = 2895521) B2895521
theorem B4638077 : Blo 1929435 4638077 := bbase (se 3 (by rfl) ⟨869639, by rfl⟩ : syracuseStep 4638077 = 1739279) (by norm_num)
theorem B3092051 : Blo 1929435 3092051 := bstep (se 1 (by rfl) ⟨2319038, by rfl⟩ : syracuseStep 3092051 = 4638077) B4638077
theorem B8245469 : Blo 1929435 8245469 := bstep (se 3 (by rfl) ⟨1546025, by rfl⟩ : syracuseStep 8245469 = 3092051) B3092051
theorem B5496979 : Blo 1929435 5496979 := bstep (se 1 (by rfl) ⟨4122734, by rfl⟩ : syracuseStep 5496979 = 8245469) B8245469
theorem B7329305 : Blo 1929435 7329305 := bstep (se 2 (by rfl) ⟨2748489, by rfl⟩ : syracuseStep 7329305 = 5496979) B5496979
theorem B4886203 : Blo 1929435 4886203 := bstep (se 1 (by rfl) ⟨3664652, by rfl⟩ : syracuseStep 4886203 = 7329305) B7329305
theorem B6514937 : Blo 1929435 6514937 := bstep (se 2 (by rfl) ⟨2443101, by rfl⟩ : syracuseStep 6514937 = 4886203) B4886203
theorem B4343291 : Blo 1929435 4343291 := bstep (se 1 (by rfl) ⟨3257468, by rfl⟩ : syracuseStep 4343291 = 6514937) B6514937
theorem B2895527 : Blo 1929435 2895527 := bstep (se 1 (by rfl) ⟨2171645, by rfl⟩ : syracuseStep 2895527 = 4343291) B4343291
theorem B1930351 : Blo 1929435 1930351 := bstep (se 1 (by rfl) ⟨1447763, by rfl⟩ : syracuseStep 1930351 = 2895527) B2895527
theorem B2895533 : Blo 1929435 2895533 := bbase (se 3 (by rfl) ⟨542912, by rfl⟩ : syracuseStep 2895533 = 1085825) (by norm_num)
theorem B1930355 : Blo 1929435 1930355 := bstep (se 1 (by rfl) ⟨1447766, by rfl⟩ : syracuseStep 1930355 = 2895533) B2895533
theorem B4343309 : Blo 1929435 4343309 := bbase (se 3 (by rfl) ⟨814370, by rfl⟩ : syracuseStep 4343309 = 1628741) (by norm_num)
theorem B2895539 : Blo 1929435 2895539 := bstep (se 1 (by rfl) ⟨2171654, by rfl⟩ : syracuseStep 2895539 = 4343309) B4343309
theorem B1930359 : Blo 1929435 1930359 := bstep (se 1 (by rfl) ⟨1447769, by rfl⟩ : syracuseStep 1930359 = 2895539) B2895539
theorem B2443117 : Blo 1929435 2443117 := bbase (se 3 (by rfl) ⟨458084, by rfl⟩ : syracuseStep 2443117 = 916169) (by norm_num)
theorem B3257489 : Blo 1929435 3257489 := bstep (se 2 (by rfl) ⟨1221558, by rfl⟩ : syracuseStep 3257489 = 2443117) B2443117
theorem B2171659 : Blo 1929435 2171659 := bstep (se 1 (by rfl) ⟨1628744, by rfl⟩ : syracuseStep 2171659 = 3257489) B3257489
theorem B2895545 : Blo 1929435 2895545 := bstep (se 2 (by rfl) ⟨1085829, by rfl⟩ : syracuseStep 2895545 = 2171659) B2171659
theorem B1930363 : Blo 1929435 1930363 := bstep (se 1 (by rfl) ⟨1447772, by rfl⟩ : syracuseStep 1930363 = 2895545) B2895545
theorem B9276229 : Blo 1929435 9276229 := bbase (se 4 (by rfl) ⟨869646, by rfl⟩ : syracuseStep 9276229 = 1739293) (by norm_num)
theorem B12368305 : Blo 1929435 12368305 := bstep (se 2 (by rfl) ⟨4638114, by rfl⟩ : syracuseStep 12368305 = 9276229) B9276229
theorem B16491073 : Blo 1929435 16491073 := bstep (se 2 (by rfl) ⟨6184152, by rfl⟩ : syracuseStep 16491073 = 12368305) B12368305
theorem B21988097 : Blo 1929435 21988097 := bstep (se 2 (by rfl) ⟨8245536, by rfl⟩ : syracuseStep 21988097 = 16491073) B16491073
theorem B14658731 : Blo 1929435 14658731 := bstep (se 1 (by rfl) ⟨10994048, by rfl⟩ : syracuseStep 14658731 = 21988097) B21988097
theorem B9772487 : Blo 1929435 9772487 := bstep (se 1 (by rfl) ⟨7329365, by rfl⟩ : syracuseStep 9772487 = 14658731) B14658731
theorem B6514991 : Blo 1929435 6514991 := bstep (se 1 (by rfl) ⟨4886243, by rfl⟩ : syracuseStep 6514991 = 9772487) B9772487
theorem B4343327 : Blo 1929435 4343327 := bstep (se 1 (by rfl) ⟨3257495, by rfl⟩ : syracuseStep 4343327 = 6514991) B6514991
theorem B2895551 : Blo 1929435 2895551 := bstep (se 1 (by rfl) ⟨2171663, by rfl⟩ : syracuseStep 2895551 = 4343327) B4343327
theorem B1930367 : Blo 1929435 1930367 := bstep (se 1 (by rfl) ⟨1447775, by rfl⟩ : syracuseStep 1930367 = 2895551) B2895551
theorem B2895557 : Blo 1929435 2895557 := bbase (se 4 (by rfl) ⟨271458, by rfl⟩ : syracuseStep 2895557 = 542917) (by norm_num)
theorem B1930371 : Blo 1929435 1930371 := bstep (se 1 (by rfl) ⟨1447778, by rfl⟩ : syracuseStep 1930371 = 2895557) B2895557
theorem B3257509 : Blo 1929435 3257509 := bbase (se 4 (by rfl) ⟨305391, by rfl⟩ : syracuseStep 3257509 = 610783) (by norm_num)
theorem B4343345 : Blo 1929435 4343345 := bstep (se 2 (by rfl) ⟨1628754, by rfl⟩ : syracuseStep 4343345 = 3257509) B3257509
theorem B2895563 : Blo 1929435 2895563 := bstep (se 1 (by rfl) ⟨2171672, by rfl⟩ : syracuseStep 2895563 = 4343345) B4343345
theorem B1930375 : Blo 1929435 1930375 := bstep (se 1 (by rfl) ⟨1447781, by rfl⟩ : syracuseStep 1930375 = 2895563) B2895563
theorem B2171677 : Blo 1929435 2171677 := bbase (se 3 (by rfl) ⟨407189, by rfl⟩ : syracuseStep 2171677 = 814379) (by norm_num)
theorem B2895569 : Blo 1929435 2895569 := bstep (se 2 (by rfl) ⟨1085838, by rfl⟩ : syracuseStep 2895569 = 2171677) B2171677
theorem B1930379 : Blo 1929435 1930379 := bstep (se 1 (by rfl) ⟨1447784, by rfl⟩ : syracuseStep 1930379 = 2895569) B2895569
theorem B6515045 : Blo 1929435 6515045 := bbase (se 4 (by rfl) ⟨610785, by rfl⟩ : syracuseStep 6515045 = 1221571) (by norm_num)
theorem B4343363 : Blo 1929435 4343363 := bstep (se 1 (by rfl) ⟨3257522, by rfl⟩ : syracuseStep 4343363 = 6515045) B6515045
theorem B2895575 : Blo 1929435 2895575 := bstep (se 1 (by rfl) ⟨2171681, by rfl⟩ : syracuseStep 2895575 = 4343363) B4343363
theorem B1930383 : Blo 1929435 1930383 := bstep (se 1 (by rfl) ⟨1447787, by rfl⟩ : syracuseStep 1930383 = 2895575) B2895575
theorem B2895581 : Blo 1929435 2895581 := bbase (se 3 (by rfl) ⟨542921, by rfl⟩ : syracuseStep 2895581 = 1085843) (by norm_num)
theorem B1930387 : Blo 1929435 1930387 := bstep (se 1 (by rfl) ⟨1447790, by rfl⟩ : syracuseStep 1930387 = 2895581) B2895581
theorem B4343381 : Blo 1929435 4343381 := bbase (se 8 (by rfl) ⟨25449, by rfl⟩ : syracuseStep 4343381 = 50899) (by norm_num)
theorem B2895587 : Blo 1929435 2895587 := bstep (se 1 (by rfl) ⟨2171690, by rfl⟩ : syracuseStep 2895587 = 4343381) B4343381
theorem B1930391 : Blo 1929435 1930391 := bstep (se 1 (by rfl) ⟨1447793, by rfl⟩ : syracuseStep 1930391 = 2895587) B2895587
theorem B4122829 : Blo 1929435 4122829 := bbase (se 3 (by rfl) ⟨773030, by rfl⟩ : syracuseStep 4122829 = 1546061) (by norm_num)
theorem B5497105 : Blo 1929435 5497105 := bstep (se 2 (by rfl) ⟨2061414, by rfl⟩ : syracuseStep 5497105 = 4122829) B4122829
theorem B7329473 : Blo 1929435 7329473 := bstep (se 2 (by rfl) ⟨2748552, by rfl⟩ : syracuseStep 7329473 = 5497105) B5497105
theorem B4886315 : Blo 1929435 4886315 := bstep (se 1 (by rfl) ⟨3664736, by rfl⟩ : syracuseStep 4886315 = 7329473) B7329473
theorem B3257543 : Blo 1929435 3257543 := bstep (se 1 (by rfl) ⟨2443157, by rfl⟩ : syracuseStep 3257543 = 4886315) B4886315
theorem B2171695 : Blo 1929435 2171695 := bstep (se 1 (by rfl) ⟨1628771, by rfl⟩ : syracuseStep 2171695 = 3257543) B3257543
theorem B2895593 : Blo 1929435 2895593 := bstep (se 2 (by rfl) ⟨1085847, by rfl⟩ : syracuseStep 2895593 = 2171695) B2171695
theorem B1930395 : Blo 1929435 1930395 := bstep (se 1 (by rfl) ⟨1447796, by rfl⟩ : syracuseStep 1930395 = 2895593) B2895593
theorem B5289157 : Blo 1929435 5289157 := bbase (se 4 (by rfl) ⟨495858, by rfl⟩ : syracuseStep 5289157 = 991717) (by norm_num)
theorem B28208837 : Blo 1929435 28208837 := bstep (se 4 (by rfl) ⟨2644578, by rfl⟩ : syracuseStep 28208837 = 5289157) B5289157
theorem B18805891 : Blo 1929435 18805891 := bstep (se 1 (by rfl) ⟨14104418, by rfl⟩ : syracuseStep 18805891 = 28208837) B28208837
theorem B25074521 : Blo 1929435 25074521 := bstep (se 2 (by rfl) ⟨9402945, by rfl⟩ : syracuseStep 25074521 = 18805891) B18805891
theorem B16716347 : Blo 1929435 16716347 := bstep (se 1 (by rfl) ⟨12537260, by rfl⟩ : syracuseStep 16716347 = 25074521) B25074521
theorem B11144231 : Blo 1929435 11144231 := bstep (se 1 (by rfl) ⟨8358173, by rfl⟩ : syracuseStep 11144231 = 16716347) B16716347
theorem B7429487 : Blo 1929435 7429487 := bstep (se 1 (by rfl) ⟨5572115, by rfl⟩ : syracuseStep 7429487 = 11144231) B11144231
theorem B19811965 : Blo 1929435 19811965 := bstep (se 3 (by rfl) ⟨3714743, by rfl⟩ : syracuseStep 19811965 = 7429487) B7429487
theorem B26415953 : Blo 1929435 26415953 := bstep (se 2 (by rfl) ⟨9905982, by rfl⟩ : syracuseStep 26415953 = 19811965) B19811965
theorem B17610635 : Blo 1929435 17610635 := bstep (se 1 (by rfl) ⟨13207976, by rfl⟩ : syracuseStep 17610635 = 26415953) B26415953
theorem B46961693 : Blo 1929435 46961693 := bstep (se 3 (by rfl) ⟨8805317, by rfl⟩ : syracuseStep 46961693 = 17610635) B17610635
theorem B31307795 : Blo 1929435 31307795 := bstep (se 1 (by rfl) ⟨23480846, by rfl⟩ : syracuseStep 31307795 = 46961693) B46961693
theorem B20871863 : Blo 1929435 20871863 := bstep (se 1 (by rfl) ⟨15653897, by rfl⟩ : syracuseStep 20871863 = 31307795) B31307795
theorem B13914575 : Blo 1929435 13914575 := bstep (se 1 (by rfl) ⟨10435931, by rfl⟩ : syracuseStep 13914575 = 20871863) B20871863
theorem B9276383 : Blo 1929435 9276383 := bstep (se 1 (by rfl) ⟨6957287, by rfl⟩ : syracuseStep 9276383 = 13914575) B13914575
theorem B24737021 : Blo 1929435 24737021 := bstep (se 3 (by rfl) ⟨4638191, by rfl⟩ : syracuseStep 24737021 = 9276383) B9276383
theorem B16491347 : Blo 1929435 16491347 := bstep (se 1 (by rfl) ⟨12368510, by rfl⟩ : syracuseStep 16491347 = 24737021) B24737021
theorem B10994231 : Blo 1929435 10994231 := bstep (se 1 (by rfl) ⟨8245673, by rfl⟩ : syracuseStep 10994231 = 16491347) B16491347
theorem B7329487 : Blo 1929435 7329487 := bstep (se 1 (by rfl) ⟨5497115, by rfl⟩ : syracuseStep 7329487 = 10994231) B10994231
theorem B9772649 : Blo 1929435 9772649 := bstep (se 2 (by rfl) ⟨3664743, by rfl⟩ : syracuseStep 9772649 = 7329487) B7329487
theorem B6515099 : Blo 1929435 6515099 := bstep (se 1 (by rfl) ⟨4886324, by rfl⟩ : syracuseStep 6515099 = 9772649) B9772649
theorem B4343399 : Blo 1929435 4343399 := bstep (se 1 (by rfl) ⟨3257549, by rfl⟩ : syracuseStep 4343399 = 6515099) B6515099
theorem B2895599 : Blo 1929435 2895599 := bstep (se 1 (by rfl) ⟨2171699, by rfl⟩ : syracuseStep 2895599 = 4343399) B4343399
theorem B1930399 : Blo 1929435 1930399 := bstep (se 1 (by rfl) ⟨1447799, by rfl⟩ : syracuseStep 1930399 = 2895599) B2895599
theorem B2895605 : Blo 1929435 2895605 := bbase (se 5 (by rfl) ⟨135731, by rfl⟩ : syracuseStep 2895605 = 271463) (by norm_num)
theorem B1930403 : Blo 1929435 1930403 := bstep (se 1 (by rfl) ⟨1447802, by rfl⟩ : syracuseStep 1930403 = 2895605) B2895605
theorem B3092141 : Blo 1929435 3092141 := bbase (se 3 (by rfl) ⟨579776, by rfl⟩ : syracuseStep 3092141 = 1159553) (by norm_num)
theorem B8245709 : Blo 1929435 8245709 := bstep (se 3 (by rfl) ⟨1546070, by rfl⟩ : syracuseStep 8245709 = 3092141) B3092141
theorem B5497139 : Blo 1929435 5497139 := bstep (se 1 (by rfl) ⟨4122854, by rfl⟩ : syracuseStep 5497139 = 8245709) B8245709
theorem B3664759 : Blo 1929435 3664759 := bstep (se 1 (by rfl) ⟨2748569, by rfl⟩ : syracuseStep 3664759 = 5497139) B5497139
theorem B4886345 : Blo 1929435 4886345 := bstep (se 2 (by rfl) ⟨1832379, by rfl⟩ : syracuseStep 4886345 = 3664759) B3664759
theorem B3257563 : Blo 1929435 3257563 := bstep (se 1 (by rfl) ⟨2443172, by rfl⟩ : syracuseStep 3257563 = 4886345) B4886345
theorem B4343417 : Blo 1929435 4343417 := bstep (se 2 (by rfl) ⟨1628781, by rfl⟩ : syracuseStep 4343417 = 3257563) B3257563
theorem B2895611 : Blo 1929435 2895611 := bstep (se 1 (by rfl) ⟨2171708, by rfl⟩ : syracuseStep 2895611 = 4343417) B4343417
theorem B1930407 : Blo 1929435 1930407 := bstep (se 1 (by rfl) ⟨1447805, by rfl⟩ : syracuseStep 1930407 = 2895611) B2895611
theorem B2171713 : Blo 1929435 2171713 := bbase (se 2 (by rfl) ⟨814392, by rfl⟩ : syracuseStep 2171713 = 1628785) (by norm_num)
theorem B2895617 : Blo 1929435 2895617 := bstep (se 2 (by rfl) ⟨1085856, by rfl⟩ : syracuseStep 2895617 = 2171713) B2171713
theorem B1930411 : Blo 1929435 1930411 := bstep (se 1 (by rfl) ⟨1447808, by rfl⟩ : syracuseStep 1930411 = 2895617) B2895617
theorem B4886365 : Blo 1929435 4886365 := bbase (se 3 (by rfl) ⟨916193, by rfl⟩ : syracuseStep 4886365 = 1832387) (by norm_num)
theorem B6515153 : Blo 1929435 6515153 := bstep (se 2 (by rfl) ⟨2443182, by rfl⟩ : syracuseStep 6515153 = 4886365) B4886365
theorem B4343435 : Blo 1929435 4343435 := bstep (se 1 (by rfl) ⟨3257576, by rfl⟩ : syracuseStep 4343435 = 6515153) B6515153
theorem B2895623 : Blo 1929435 2895623 := bstep (se 1 (by rfl) ⟨2171717, by rfl⟩ : syracuseStep 2895623 = 4343435) B4343435
theorem B1930415 : Blo 1929435 1930415 := bstep (se 1 (by rfl) ⟨1447811, by rfl⟩ : syracuseStep 1930415 = 2895623) B2895623
theorem B2895629 : Blo 1929435 2895629 := bbase (se 3 (by rfl) ⟨542930, by rfl⟩ : syracuseStep 2895629 = 1085861) (by norm_num)
theorem B1930419 : Blo 1929435 1930419 := bstep (se 1 (by rfl) ⟨1447814, by rfl⟩ : syracuseStep 1930419 = 2895629) B2895629
theorem B4343453 : Blo 1929435 4343453 := bbase (se 3 (by rfl) ⟨814397, by rfl⟩ : syracuseStep 4343453 = 1628795) (by norm_num)
theorem B2895635 : Blo 1929435 2895635 := bstep (se 1 (by rfl) ⟨2171726, by rfl⟩ : syracuseStep 2895635 = 4343453) B4343453
theorem B1930423 : Blo 1929435 1930423 := bstep (se 1 (by rfl) ⟨1447817, by rfl⟩ : syracuseStep 1930423 = 2895635) B2895635
theorem B3257597 : Blo 1929435 3257597 := bbase (se 3 (by rfl) ⟨610799, by rfl⟩ : syracuseStep 3257597 = 1221599) (by norm_num)
theorem B2171731 : Blo 1929435 2171731 := bstep (se 1 (by rfl) ⟨1628798, by rfl⟩ : syracuseStep 2171731 = 3257597) B3257597
theorem B2895641 : Blo 1929435 2895641 := bstep (se 2 (by rfl) ⟨1085865, by rfl⟩ : syracuseStep 2895641 = 2171731) B2171731
theorem B1930427 : Blo 1929435 1930427 := bstep (se 1 (by rfl) ⟨1447820, by rfl⟩ : syracuseStep 1930427 = 2895641) B2895641
theorem B4638269 : Blo 1929435 4638269 := bbase (se 3 (by rfl) ⟨869675, by rfl⟩ : syracuseStep 4638269 = 1739351) (by norm_num)
theorem B3092179 : Blo 1929435 3092179 := bstep (se 1 (by rfl) ⟨2319134, by rfl⟩ : syracuseStep 3092179 = 4638269) B4638269
theorem B4122905 : Blo 1929435 4122905 := bstep (se 2 (by rfl) ⟨1546089, by rfl⟩ : syracuseStep 4122905 = 3092179) B3092179
theorem B10994413 : Blo 1929435 10994413 := bstep (se 3 (by rfl) ⟨2061452, by rfl⟩ : syracuseStep 10994413 = 4122905) B4122905
theorem B14659217 : Blo 1929435 14659217 := bstep (se 2 (by rfl) ⟨5497206, by rfl⟩ : syracuseStep 14659217 = 10994413) B10994413
theorem B9772811 : Blo 1929435 9772811 := bstep (se 1 (by rfl) ⟨7329608, by rfl⟩ : syracuseStep 9772811 = 14659217) B14659217
theorem B6515207 : Blo 1929435 6515207 := bstep (se 1 (by rfl) ⟨4886405, by rfl⟩ : syracuseStep 6515207 = 9772811) B9772811
theorem B4343471 : Blo 1929435 4343471 := bstep (se 1 (by rfl) ⟨3257603, by rfl⟩ : syracuseStep 4343471 = 6515207) B6515207
theorem B2895647 : Blo 1929435 2895647 := bstep (se 1 (by rfl) ⟨2171735, by rfl⟩ : syracuseStep 2895647 = 4343471) B4343471
theorem B1930431 : Blo 1929435 1930431 := bstep (se 1 (by rfl) ⟨1447823, by rfl⟩ : syracuseStep 1930431 = 2895647) B2895647
theorem B2895653 : Blo 1929435 2895653 := bbase (se 4 (by rfl) ⟨271467, by rfl⟩ : syracuseStep 2895653 = 542935) (by norm_num)
theorem B1930435 : Blo 1929435 1930435 := bstep (se 1 (by rfl) ⟨1447826, by rfl⟩ : syracuseStep 1930435 = 2895653) B2895653
theorem B2443213 : Blo 1929435 2443213 := bbase (se 3 (by rfl) ⟨458102, by rfl⟩ : syracuseStep 2443213 = 916205) (by norm_num)
theorem B3257617 : Blo 1929435 3257617 := bstep (se 2 (by rfl) ⟨1221606, by rfl⟩ : syracuseStep 3257617 = 2443213) B2443213
theorem B4343489 : Blo 1929435 4343489 := bstep (se 2 (by rfl) ⟨1628808, by rfl⟩ : syracuseStep 4343489 = 3257617) B3257617
theorem B2895659 : Blo 1929435 2895659 := bstep (se 1 (by rfl) ⟨2171744, by rfl⟩ : syracuseStep 2895659 = 4343489) B4343489
theorem B1930439 : Blo 1929435 1930439 := bstep (se 1 (by rfl) ⟨1447829, by rfl⟩ : syracuseStep 1930439 = 2895659) B2895659
theorem B2171749 : Blo 1929435 2171749 := bbase (se 4 (by rfl) ⟨203601, by rfl⟩ : syracuseStep 2171749 = 407203) (by norm_num)
theorem B2895665 : Blo 1929435 2895665 := bstep (se 2 (by rfl) ⟨1085874, by rfl⟩ : syracuseStep 2895665 = 2171749) B2171749
theorem B1930443 : Blo 1929435 1930443 := bstep (se 1 (by rfl) ⟨1447832, by rfl⟩ : syracuseStep 1930443 = 2895665) B2895665
theorem B5497253 : Blo 1929435 5497253 := bbase (se 4 (by rfl) ⟨515367, by rfl⟩ : syracuseStep 5497253 = 1030735) (by norm_num)
theorem B3664835 : Blo 1929435 3664835 := bstep (se 1 (by rfl) ⟨2748626, by rfl⟩ : syracuseStep 3664835 = 5497253) B5497253
theorem B2443223 : Blo 1929435 2443223 := bstep (se 1 (by rfl) ⟨1832417, by rfl⟩ : syracuseStep 2443223 = 3664835) B3664835
theorem B6515261 : Blo 1929435 6515261 := bstep (se 3 (by rfl) ⟨1221611, by rfl⟩ : syracuseStep 6515261 = 2443223) B2443223
theorem B4343507 : Blo 1929435 4343507 := bstep (se 1 (by rfl) ⟨3257630, by rfl⟩ : syracuseStep 4343507 = 6515261) B6515261
theorem B2895671 : Blo 1929435 2895671 := bstep (se 1 (by rfl) ⟨2171753, by rfl⟩ : syracuseStep 2895671 = 4343507) B4343507
theorem B1930447 : Blo 1929435 1930447 := bstep (se 1 (by rfl) ⟨1447835, by rfl⟩ : syracuseStep 1930447 = 2895671) B2895671
theorem B2895677 : Blo 1929435 2895677 := bbase (se 3 (by rfl) ⟨542939, by rfl⟩ : syracuseStep 2895677 = 1085879) (by norm_num)
theorem B1930451 : Blo 1929435 1930451 := bstep (se 1 (by rfl) ⟨1447838, by rfl⟩ : syracuseStep 1930451 = 2895677) B2895677
theorem B4343525 : Blo 1929435 4343525 := bbase (se 4 (by rfl) ⟨407205, by rfl⟩ : syracuseStep 4343525 = 814411) (by norm_num)
theorem B2895683 : Blo 1929435 2895683 := bstep (se 1 (by rfl) ⟨2171762, by rfl⟩ : syracuseStep 2895683 = 4343525) B4343525
theorem B1930455 : Blo 1929435 1930455 := bstep (se 1 (by rfl) ⟨1447841, by rfl⟩ : syracuseStep 1930455 = 2895683) B2895683
theorem B4886477 : Blo 1929435 4886477 := bbase (se 3 (by rfl) ⟨916214, by rfl⟩ : syracuseStep 4886477 = 1832429) (by norm_num)
theorem B3257651 : Blo 1929435 3257651 := bstep (se 1 (by rfl) ⟨2443238, by rfl⟩ : syracuseStep 3257651 = 4886477) B4886477
theorem B2171767 : Blo 1929435 2171767 := bstep (se 1 (by rfl) ⟨1628825, by rfl⟩ : syracuseStep 2171767 = 3257651) B3257651
theorem B2895689 : Blo 1929435 2895689 := bstep (se 2 (by rfl) ⟨1085883, by rfl⟩ : syracuseStep 2895689 = 2171767) B2171767
theorem B1930459 : Blo 1929435 1930459 := bstep (se 1 (by rfl) ⟨1447844, by rfl⟩ : syracuseStep 1930459 = 2895689) B2895689
theorem B2935205 : Blo 1929435 2935205 := bbase (se 4 (by rfl) ⟨275175, by rfl⟩ : syracuseStep 2935205 = 550351) (by norm_num)
theorem B1956803 : Blo 1929435 1956803 := bstep (se 1 (by rfl) ⟨1467602, by rfl⟩ : syracuseStep 1956803 = 2935205) B2935205
theorem B5218141 : Blo 1929435 5218141 := bstep (se 3 (by rfl) ⟨978401, by rfl⟩ : syracuseStep 5218141 = 1956803) B1956803
theorem B6957521 : Blo 1929435 6957521 := bstep (se 2 (by rfl) ⟨2609070, by rfl⟩ : syracuseStep 6957521 = 5218141) B5218141
theorem B4638347 : Blo 1929435 4638347 := bstep (se 1 (by rfl) ⟨3478760, by rfl⟩ : syracuseStep 4638347 = 6957521) B6957521
theorem B3092231 : Blo 1929435 3092231 := bstep (se 1 (by rfl) ⟨2319173, by rfl⟩ : syracuseStep 3092231 = 4638347) B4638347
theorem B2061487 : Blo 1929435 2061487 := bstep (se 1 (by rfl) ⟨1546115, by rfl⟩ : syracuseStep 2061487 = 3092231) B3092231
theorem B2748649 : Blo 1929435 2748649 := bstep (se 2 (by rfl) ⟨1030743, by rfl⟩ : syracuseStep 2748649 = 2061487) B2061487
theorem B3664865 : Blo 1929435 3664865 := bstep (se 2 (by rfl) ⟨1374324, by rfl⟩ : syracuseStep 3664865 = 2748649) B2748649
theorem B9772973 : Blo 1929435 9772973 := bstep (se 3 (by rfl) ⟨1832432, by rfl⟩ : syracuseStep 9772973 = 3664865) B3664865
theorem B6515315 : Blo 1929435 6515315 := bstep (se 1 (by rfl) ⟨4886486, by rfl⟩ : syracuseStep 6515315 = 9772973) B9772973
theorem B4343543 : Blo 1929435 4343543 := bstep (se 1 (by rfl) ⟨3257657, by rfl⟩ : syracuseStep 4343543 = 6515315) B6515315
theorem B2895695 : Blo 1929435 2895695 := bstep (se 1 (by rfl) ⟨2171771, by rfl⟩ : syracuseStep 2895695 = 4343543) B4343543
theorem B1930463 : Blo 1929435 1930463 := bstep (se 1 (by rfl) ⟨1447847, by rfl⟩ : syracuseStep 1930463 = 2895695) B2895695
theorem B2895701 : Blo 1929435 2895701 := bbase (se 9 (by rfl) ⟨8483, by rfl⟩ : syracuseStep 2895701 = 16967) (by norm_num)
theorem B1930467 : Blo 1929435 1930467 := bstep (se 1 (by rfl) ⟨1447850, by rfl⟩ : syracuseStep 1930467 = 2895701) B2895701
theorem B15654485 : Blo 1929435 15654485 := bbase (se 8 (by rfl) ⟨91725, by rfl⟩ : syracuseStep 15654485 = 183451) (by norm_num)
theorem B10436323 : Blo 1929435 10436323 := bstep (se 1 (by rfl) ⟨7827242, by rfl⟩ : syracuseStep 10436323 = 15654485) B15654485
theorem B13915097 : Blo 1929435 13915097 := bstep (se 2 (by rfl) ⟨5218161, by rfl⟩ : syracuseStep 13915097 = 10436323) B10436323
theorem B9276731 : Blo 1929435 9276731 := bstep (se 1 (by rfl) ⟨6957548, by rfl⟩ : syracuseStep 9276731 = 13915097) B13915097
theorem B6184487 : Blo 1929435 6184487 := bstep (se 1 (by rfl) ⟨4638365, by rfl⟩ : syracuseStep 6184487 = 9276731) B9276731
theorem B4122991 : Blo 1929435 4122991 := bstep (se 1 (by rfl) ⟨3092243, by rfl⟩ : syracuseStep 4122991 = 6184487) B6184487
theorem B5497321 : Blo 1929435 5497321 := bstep (se 2 (by rfl) ⟨2061495, by rfl⟩ : syracuseStep 5497321 = 4122991) B4122991
theorem B7329761 : Blo 1929435 7329761 := bstep (se 2 (by rfl) ⟨2748660, by rfl⟩ : syracuseStep 7329761 = 5497321) B5497321
theorem B4886507 : Blo 1929435 4886507 := bstep (se 1 (by rfl) ⟨3664880, by rfl⟩ : syracuseStep 4886507 = 7329761) B7329761
theorem B3257671 : Blo 1929435 3257671 := bstep (se 1 (by rfl) ⟨2443253, by rfl⟩ : syracuseStep 3257671 = 4886507) B4886507
theorem B4343561 : Blo 1929435 4343561 := bstep (se 2 (by rfl) ⟨1628835, by rfl⟩ : syracuseStep 4343561 = 3257671) B3257671
theorem B2895707 : Blo 1929435 2895707 := bstep (se 1 (by rfl) ⟨2171780, by rfl⟩ : syracuseStep 2895707 = 4343561) B4343561
theorem B1930471 : Blo 1929435 1930471 := bstep (se 1 (by rfl) ⟨1447853, by rfl⟩ : syracuseStep 1930471 = 2895707) B2895707
theorem B2171785 : Blo 1929435 2171785 := bbase (se 2 (by rfl) ⟨814419, by rfl⟩ : syracuseStep 2171785 = 1628839) (by norm_num)
theorem B2895713 : Blo 1929435 2895713 := bstep (se 2 (by rfl) ⟨1085892, by rfl⟩ : syracuseStep 2895713 = 2171785) B2171785
theorem B1930475 : Blo 1929435 1930475 := bstep (se 1 (by rfl) ⟨1447856, by rfl⟩ : syracuseStep 1930475 = 2895713) B2895713
theorem B3439141 : Blo 1929435 3439141 := bbase (se 4 (by rfl) ⟨322419, by rfl⟩ : syracuseStep 3439141 = 644839) (by norm_num)
theorem B18342085 : Blo 1929435 18342085 := bstep (se 4 (by rfl) ⟨1719570, by rfl⟩ : syracuseStep 18342085 = 3439141) B3439141
theorem B24456113 : Blo 1929435 24456113 := bstep (se 2 (by rfl) ⟨9171042, by rfl⟩ : syracuseStep 24456113 = 18342085) B18342085
theorem B16304075 : Blo 1929435 16304075 := bstep (se 1 (by rfl) ⟨12228056, by rfl⟩ : syracuseStep 16304075 = 24456113) B24456113
theorem B10869383 : Blo 1929435 10869383 := bstep (se 1 (by rfl) ⟨8152037, by rfl⟩ : syracuseStep 10869383 = 16304075) B16304075
theorem B7246255 : Blo 1929435 7246255 := bstep (se 1 (by rfl) ⟨5434691, by rfl⟩ : syracuseStep 7246255 = 10869383) B10869383
theorem B9661673 : Blo 1929435 9661673 := bstep (se 2 (by rfl) ⟨3623127, by rfl⟩ : syracuseStep 9661673 = 7246255) B7246255
theorem B6441115 : Blo 1929435 6441115 := bstep (se 1 (by rfl) ⟨4830836, by rfl⟩ : syracuseStep 6441115 = 9661673) B9661673
theorem B8588153 : Blo 1929435 8588153 := bstep (se 2 (by rfl) ⟨3220557, by rfl⟩ : syracuseStep 8588153 = 6441115) B6441115
theorem B22901741 : Blo 1929435 22901741 := bstep (se 3 (by rfl) ⟨4294076, by rfl⟩ : syracuseStep 22901741 = 8588153) B8588153
theorem B15267827 : Blo 1929435 15267827 := bstep (se 1 (by rfl) ⟨11450870, by rfl⟩ : syracuseStep 15267827 = 22901741) B22901741
theorem B10178551 : Blo 1929435 10178551 := bstep (se 1 (by rfl) ⟨7633913, by rfl⟩ : syracuseStep 10178551 = 15267827) B15267827
theorem B13571401 : Blo 1929435 13571401 := bstep (se 2 (by rfl) ⟨5089275, by rfl⟩ : syracuseStep 13571401 = 10178551) B10178551
theorem B18095201 : Blo 1929435 18095201 := bstep (se 2 (by rfl) ⟨6785700, by rfl⟩ : syracuseStep 18095201 = 13571401) B13571401
theorem B12063467 : Blo 1929435 12063467 := bstep (se 1 (by rfl) ⟨9047600, by rfl⟩ : syracuseStep 12063467 = 18095201) B18095201
theorem B8042311 : Blo 1929435 8042311 := bstep (se 1 (by rfl) ⟨6031733, by rfl⟩ : syracuseStep 8042311 = 12063467) B12063467
theorem B42892325 : Blo 1929435 42892325 := bstep (se 4 (by rfl) ⟨4021155, by rfl⟩ : syracuseStep 42892325 = 8042311) B8042311
theorem B28594883 : Blo 1929435 28594883 := bstep (se 1 (by rfl) ⟨21446162, by rfl⟩ : syracuseStep 28594883 = 42892325) B42892325
theorem B76253021 : Blo 1929435 76253021 := bstep (se 3 (by rfl) ⟨14297441, by rfl⟩ : syracuseStep 76253021 = 28594883) B28594883
theorem B50835347 : Blo 1929435 50835347 := bstep (se 1 (by rfl) ⟨38126510, by rfl⟩ : syracuseStep 50835347 = 76253021) B76253021
theorem B33890231 : Blo 1929435 33890231 := bstep (se 1 (by rfl) ⟨25417673, by rfl⟩ : syracuseStep 33890231 = 50835347) B50835347
theorem B22593487 : Blo 1929435 22593487 := bstep (se 1 (by rfl) ⟨16945115, by rfl⟩ : syracuseStep 22593487 = 33890231) B33890231
theorem B30124649 : Blo 1929435 30124649 := bstep (se 2 (by rfl) ⟨11296743, by rfl⟩ : syracuseStep 30124649 = 22593487) B22593487
theorem B20083099 : Blo 1929435 20083099 := bstep (se 1 (by rfl) ⟨15062324, by rfl⟩ : syracuseStep 20083099 = 30124649) B30124649
theorem B26777465 : Blo 1929435 26777465 := bstep (se 2 (by rfl) ⟨10041549, by rfl⟩ : syracuseStep 26777465 = 20083099) B20083099
theorem B17851643 : Blo 1929435 17851643 := bstep (se 1 (by rfl) ⟨13388732, by rfl⟩ : syracuseStep 17851643 = 26777465) B26777465
theorem B11901095 : Blo 1929435 11901095 := bstep (se 1 (by rfl) ⟨8925821, by rfl⟩ : syracuseStep 11901095 = 17851643) B17851643
theorem B7934063 : Blo 1929435 7934063 := bstep (se 1 (by rfl) ⟨5950547, by rfl⟩ : syracuseStep 7934063 = 11901095) B11901095
theorem B84630005 : Blo 1929435 84630005 := bstep (se 5 (by rfl) ⟨3967031, by rfl⟩ : syracuseStep 84630005 = 7934063) B7934063
theorem B56420003 : Blo 1929435 56420003 := bstep (se 1 (by rfl) ⟨42315002, by rfl⟩ : syracuseStep 56420003 = 84630005) B84630005
theorem B37613335 : Blo 1929435 37613335 := bstep (se 1 (by rfl) ⟨28210001, by rfl⟩ : syracuseStep 37613335 = 56420003) B56420003
theorem B50151113 : Blo 1929435 50151113 := bstep (se 2 (by rfl) ⟨18806667, by rfl⟩ : syracuseStep 50151113 = 37613335) B37613335
theorem B33434075 : Blo 1929435 33434075 := bstep (se 1 (by rfl) ⟨25075556, by rfl⟩ : syracuseStep 33434075 = 50151113) B50151113
theorem B22289383 : Blo 1929435 22289383 := bstep (se 1 (by rfl) ⟨16717037, by rfl⟩ : syracuseStep 22289383 = 33434075) B33434075
theorem B118876709 : Blo 1929435 118876709 := bstep (se 4 (by rfl) ⟨11144691, by rfl⟩ : syracuseStep 118876709 = 22289383) B22289383
theorem B79251139 : Blo 1929435 79251139 := bstep (se 1 (by rfl) ⟨59438354, by rfl⟩ : syracuseStep 79251139 = 118876709) B118876709
theorem B422672741 : Blo 1929435 422672741 := bstep (se 4 (by rfl) ⟨39625569, by rfl⟩ : syracuseStep 422672741 = 79251139) B79251139
theorem B281781827 : Blo 1929435 281781827 := bstep (se 1 (by rfl) ⟨211336370, by rfl⟩ : syracuseStep 281781827 = 422672741) B422672741
theorem B187854551 : Blo 1929435 187854551 := bstep (se 1 (by rfl) ⟨140890913, by rfl⟩ : syracuseStep 187854551 = 281781827) B281781827
theorem B125236367 : Blo 1929435 125236367 := bstep (se 1 (by rfl) ⟨93927275, by rfl⟩ : syracuseStep 125236367 = 187854551) B187854551
theorem B83490911 : Blo 1929435 83490911 := bstep (se 1 (by rfl) ⟨62618183, by rfl⟩ : syracuseStep 83490911 = 125236367) B125236367
theorem B55660607 : Blo 1929435 55660607 := bstep (se 1 (by rfl) ⟨41745455, by rfl⟩ : syracuseStep 55660607 = 83490911) B83490911
theorem B37107071 : Blo 1929435 37107071 := bstep (se 1 (by rfl) ⟨27830303, by rfl⟩ : syracuseStep 37107071 = 55660607) B55660607
theorem B24738047 : Blo 1929435 24738047 := bstep (se 1 (by rfl) ⟨18553535, by rfl⟩ : syracuseStep 24738047 = 37107071) B37107071
theorem B16492031 : Blo 1929435 16492031 := bstep (se 1 (by rfl) ⟨12369023, by rfl⟩ : syracuseStep 16492031 = 24738047) B24738047
theorem B10994687 : Blo 1929435 10994687 := bstep (se 1 (by rfl) ⟨8246015, by rfl⟩ : syracuseStep 10994687 = 16492031) B16492031
theorem B7329791 : Blo 1929435 7329791 := bstep (se 1 (by rfl) ⟨5497343, by rfl⟩ : syracuseStep 7329791 = 10994687) B10994687
theorem B4886527 : Blo 1929435 4886527 := bstep (se 1 (by rfl) ⟨3664895, by rfl⟩ : syracuseStep 4886527 = 7329791) B7329791
theorem B6515369 : Blo 1929435 6515369 := bstep (se 2 (by rfl) ⟨2443263, by rfl⟩ : syracuseStep 6515369 = 4886527) B4886527
theorem B4343579 : Blo 1929435 4343579 := bstep (se 1 (by rfl) ⟨3257684, by rfl⟩ : syracuseStep 4343579 = 6515369) B6515369
theorem B2895719 : Blo 1929435 2895719 := bstep (se 1 (by rfl) ⟨2171789, by rfl⟩ : syracuseStep 2895719 = 4343579) B4343579
theorem B1930479 : Blo 1929435 1930479 := bstep (se 1 (by rfl) ⟨1447859, by rfl⟩ : syracuseStep 1930479 = 2895719) B2895719
theorem B2895725 : Blo 1929435 2895725 := bbase (se 3 (by rfl) ⟨542948, by rfl⟩ : syracuseStep 2895725 = 1085897) (by norm_num)
theorem B1930483 : Blo 1929435 1930483 := bstep (se 1 (by rfl) ⟨1447862, by rfl⟩ : syracuseStep 1930483 = 2895725) B2895725
theorem B4343597 : Blo 1929435 4343597 := bbase (se 3 (by rfl) ⟨814424, by rfl⟩ : syracuseStep 4343597 = 1628849) (by norm_num)
theorem B2895731 : Blo 1929435 2895731 := bstep (se 1 (by rfl) ⟨2171798, by rfl⟩ : syracuseStep 2895731 = 4343597) B4343597
theorem B1930487 : Blo 1929435 1930487 := bstep (se 1 (by rfl) ⟨1447865, by rfl⟩ : syracuseStep 1930487 = 2895731) B2895731
theorem B8246069 : Blo 1929435 8246069 := bbase (se 5 (by rfl) ⟨386534, by rfl⟩ : syracuseStep 8246069 = 773069) (by norm_num)
theorem B5497379 : Blo 1929435 5497379 := bstep (se 1 (by rfl) ⟨4123034, by rfl⟩ : syracuseStep 5497379 = 8246069) B8246069
theorem B3664919 : Blo 1929435 3664919 := bstep (se 1 (by rfl) ⟨2748689, by rfl⟩ : syracuseStep 3664919 = 5497379) B5497379
theorem B2443279 : Blo 1929435 2443279 := bstep (se 1 (by rfl) ⟨1832459, by rfl⟩ : syracuseStep 2443279 = 3664919) B3664919
theorem B3257705 : Blo 1929435 3257705 := bstep (se 2 (by rfl) ⟨1221639, by rfl⟩ : syracuseStep 3257705 = 2443279) B2443279
theorem B2171803 : Blo 1929435 2171803 := bstep (se 1 (by rfl) ⟨1628852, by rfl⟩ : syracuseStep 2171803 = 3257705) B3257705
theorem B2895737 : Blo 1929435 2895737 := bstep (se 2 (by rfl) ⟨1085901, by rfl⟩ : syracuseStep 2895737 = 2171803) B2171803
theorem B1930491 : Blo 1929435 1930491 := bstep (se 1 (by rfl) ⟨1447868, by rfl⟩ : syracuseStep 1930491 = 2895737) B2895737
theorem B2935253 : Blo 1929435 2935253 := bbase (se 7 (by rfl) ⟨34397, by rfl⟩ : syracuseStep 2935253 = 68795) (by norm_num)
theorem B1956835 : Blo 1929435 1956835 := bstep (se 1 (by rfl) ⟨1467626, by rfl⟩ : syracuseStep 1956835 = 2935253) B2935253
theorem B2609113 : Blo 1929435 2609113 := bstep (se 2 (by rfl) ⟨978417, by rfl⟩ : syracuseStep 2609113 = 1956835) B1956835
theorem B3478817 : Blo 1929435 3478817 := bstep (se 2 (by rfl) ⟨1304556, by rfl⟩ : syracuseStep 3478817 = 2609113) B2609113
theorem B2319211 : Blo 1929435 2319211 := bstep (se 1 (by rfl) ⟨1739408, by rfl⟩ : syracuseStep 2319211 = 3478817) B3478817
theorem B12369125 : Blo 1929435 12369125 := bstep (se 4 (by rfl) ⟨1159605, by rfl⟩ : syracuseStep 12369125 = 2319211) B2319211
theorem B32984333 : Blo 1929435 32984333 := bstep (se 3 (by rfl) ⟨6184562, by rfl⟩ : syracuseStep 32984333 = 12369125) B12369125
theorem B21989555 : Blo 1929435 21989555 := bstep (se 1 (by rfl) ⟨16492166, by rfl⟩ : syracuseStep 21989555 = 32984333) B32984333
theorem B14659703 : Blo 1929435 14659703 := bstep (se 1 (by rfl) ⟨10994777, by rfl⟩ : syracuseStep 14659703 = 21989555) B21989555
theorem B9773135 : Blo 1929435 9773135 := bstep (se 1 (by rfl) ⟨7329851, by rfl⟩ : syracuseStep 9773135 = 14659703) B14659703
theorem B6515423 : Blo 1929435 6515423 := bstep (se 1 (by rfl) ⟨4886567, by rfl⟩ : syracuseStep 6515423 = 9773135) B9773135
theorem B4343615 : Blo 1929435 4343615 := bstep (se 1 (by rfl) ⟨3257711, by rfl⟩ : syracuseStep 4343615 = 6515423) B6515423
theorem B2895743 : Blo 1929435 2895743 := bstep (se 1 (by rfl) ⟨2171807, by rfl⟩ : syracuseStep 2895743 = 4343615) B4343615
theorem B1930495 : Blo 1929435 1930495 := bstep (se 1 (by rfl) ⟨1447871, by rfl⟩ : syracuseStep 1930495 = 2895743) B2895743
theorem B2895749 : Blo 1929435 2895749 := bbase (se 4 (by rfl) ⟨271476, by rfl⟩ : syracuseStep 2895749 = 542953) (by norm_num)
theorem B1930499 : Blo 1929435 1930499 := bstep (se 1 (by rfl) ⟨1447874, by rfl⟩ : syracuseStep 1930499 = 2895749) B2895749
theorem B3257725 : Blo 1929435 3257725 := bbase (se 3 (by rfl) ⟨610823, by rfl⟩ : syracuseStep 3257725 = 1221647) (by norm_num)
theorem B4343633 : Blo 1929435 4343633 := bstep (se 2 (by rfl) ⟨1628862, by rfl⟩ : syracuseStep 4343633 = 3257725) B3257725
theorem B2895755 : Blo 1929435 2895755 := bstep (se 1 (by rfl) ⟨2171816, by rfl⟩ : syracuseStep 2895755 = 4343633) B4343633
theorem B1930503 : Blo 1929435 1930503 := bstep (se 1 (by rfl) ⟨1447877, by rfl⟩ : syracuseStep 1930503 = 2895755) B2895755
theorem B2171821 : Blo 1929435 2171821 := bbase (se 3 (by rfl) ⟨407216, by rfl⟩ : syracuseStep 2171821 = 814433) (by norm_num)
theorem B2895761 : Blo 1929435 2895761 := bstep (se 2 (by rfl) ⟨1085910, by rfl⟩ : syracuseStep 2895761 = 2171821) B2171821
theorem B1930507 : Blo 1929435 1930507 := bstep (se 1 (by rfl) ⟨1447880, by rfl⟩ : syracuseStep 1930507 = 2895761) B2895761
theorem B6515477 : Blo 1929435 6515477 := bbase (se 6 (by rfl) ⟨152706, by rfl⟩ : syracuseStep 6515477 = 305413) (by norm_num)
theorem B4343651 : Blo 1929435 4343651 := bstep (se 1 (by rfl) ⟨3257738, by rfl⟩ : syracuseStep 4343651 = 6515477) B6515477
theorem B2895767 : Blo 1929435 2895767 := bstep (se 1 (by rfl) ⟨2171825, by rfl⟩ : syracuseStep 2895767 = 4343651) B4343651
theorem B1930511 : Blo 1929435 1930511 := bstep (se 1 (by rfl) ⟨1447883, by rfl⟩ : syracuseStep 1930511 = 2895767) B2895767
theorem B2895773 : Blo 1929435 2895773 := bbase (se 3 (by rfl) ⟨542957, by rfl⟩ : syracuseStep 2895773 = 1085915) (by norm_num)
theorem B1930515 : Blo 1929435 1930515 := bstep (se 1 (by rfl) ⟨1447886, by rfl⟩ : syracuseStep 1930515 = 2895773) B2895773
theorem B4343669 : Blo 1929435 4343669 := bbase (se 5 (by rfl) ⟨203609, by rfl⟩ : syracuseStep 4343669 = 407219) (by norm_num)
theorem B2895779 : Blo 1929435 2895779 := bstep (se 1 (by rfl) ⟨2171834, by rfl⟩ : syracuseStep 2895779 = 4343669) B4343669
theorem B1930519 : Blo 1929435 1930519 := bstep (se 1 (by rfl) ⟨1447889, by rfl⟩ : syracuseStep 1930519 = 2895779) B2895779
theorem B10041781 : Blo 1929435 10041781 := bbase (se 5 (by rfl) ⟨470708, by rfl⟩ : syracuseStep 10041781 = 941417) (by norm_num)
theorem B13389041 : Blo 1929435 13389041 := bstep (se 2 (by rfl) ⟨5020890, by rfl⟩ : syracuseStep 13389041 = 10041781) B10041781
theorem B8926027 : Blo 1929435 8926027 := bstep (se 1 (by rfl) ⟨6694520, by rfl⟩ : syracuseStep 8926027 = 13389041) B13389041
theorem B47605477 : Blo 1929435 47605477 := bstep (se 4 (by rfl) ⟨4463013, by rfl⟩ : syracuseStep 47605477 = 8926027) B8926027
theorem B63473969 : Blo 1929435 63473969 := bstep (se 2 (by rfl) ⟨23802738, by rfl⟩ : syracuseStep 63473969 = 47605477) B47605477
theorem B42315979 : Blo 1929435 42315979 := bstep (se 1 (by rfl) ⟨31736984, by rfl⟩ : syracuseStep 42315979 = 63473969) B63473969
theorem B56421305 : Blo 1929435 56421305 := bstep (se 2 (by rfl) ⟨21157989, by rfl⟩ : syracuseStep 56421305 = 42315979) B42315979
theorem B37614203 : Blo 1929435 37614203 := bstep (se 1 (by rfl) ⟨28210652, by rfl⟩ : syracuseStep 37614203 = 56421305) B56421305
theorem B25076135 : Blo 1929435 25076135 := bstep (se 1 (by rfl) ⟨18807101, by rfl⟩ : syracuseStep 25076135 = 37614203) B37614203
theorem B16717423 : Blo 1929435 16717423 := bstep (se 1 (by rfl) ⟨12538067, by rfl⟩ : syracuseStep 16717423 = 25076135) B25076135
theorem B22289897 : Blo 1929435 22289897 := bstep (se 2 (by rfl) ⟨8358711, by rfl⟩ : syracuseStep 22289897 = 16717423) B16717423
theorem B14859931 : Blo 1929435 14859931 := bstep (se 1 (by rfl) ⟨11144948, by rfl⟩ : syracuseStep 14859931 = 22289897) B22289897
theorem B19813241 : Blo 1929435 19813241 := bstep (se 2 (by rfl) ⟨7429965, by rfl⟩ : syracuseStep 19813241 = 14859931) B14859931
theorem B13208827 : Blo 1929435 13208827 := bstep (se 1 (by rfl) ⟨9906620, by rfl⟩ : syracuseStep 13208827 = 19813241) B19813241
theorem B17611769 : Blo 1929435 17611769 := bstep (se 2 (by rfl) ⟨6604413, by rfl⟩ : syracuseStep 17611769 = 13208827) B13208827
theorem B46964717 : Blo 1929435 46964717 := bstep (se 3 (by rfl) ⟨8805884, by rfl⟩ : syracuseStep 46964717 = 17611769) B17611769
theorem B31309811 : Blo 1929435 31309811 := bstep (se 1 (by rfl) ⟨23482358, by rfl⟩ : syracuseStep 31309811 = 46964717) B46964717
theorem B20873207 : Blo 1929435 20873207 := bstep (se 1 (by rfl) ⟨15654905, by rfl⟩ : syracuseStep 20873207 = 31309811) B31309811
theorem B13915471 : Blo 1929435 13915471 := bstep (se 1 (by rfl) ⟨10436603, by rfl⟩ : syracuseStep 13915471 = 20873207) B20873207
theorem B18553961 : Blo 1929435 18553961 := bstep (se 2 (by rfl) ⟨6957735, by rfl⟩ : syracuseStep 18553961 = 13915471) B13915471
theorem B12369307 : Blo 1929435 12369307 := bstep (se 1 (by rfl) ⟨9276980, by rfl⟩ : syracuseStep 12369307 = 18553961) B18553961
theorem B16492409 : Blo 1929435 16492409 := bstep (se 2 (by rfl) ⟨6184653, by rfl⟩ : syracuseStep 16492409 = 12369307) B12369307
theorem B10994939 : Blo 1929435 10994939 := bstep (se 1 (by rfl) ⟨8246204, by rfl⟩ : syracuseStep 10994939 = 16492409) B16492409
theorem B7329959 : Blo 1929435 7329959 := bstep (se 1 (by rfl) ⟨5497469, by rfl⟩ : syracuseStep 7329959 = 10994939) B10994939
theorem B4886639 : Blo 1929435 4886639 := bstep (se 1 (by rfl) ⟨3664979, by rfl⟩ : syracuseStep 4886639 = 7329959) B7329959
theorem B3257759 : Blo 1929435 3257759 := bstep (se 1 (by rfl) ⟨2443319, by rfl⟩ : syracuseStep 3257759 = 4886639) B4886639
theorem B2171839 : Blo 1929435 2171839 := bstep (se 1 (by rfl) ⟨1628879, by rfl⟩ : syracuseStep 2171839 = 3257759) B3257759
theorem B2895785 : Blo 1929435 2895785 := bstep (se 2 (by rfl) ⟨1085919, by rfl⟩ : syracuseStep 2895785 = 2171839) B2171839
theorem B1930523 : Blo 1929435 1930523 := bstep (se 1 (by rfl) ⟨1447892, by rfl⟩ : syracuseStep 1930523 = 2895785) B2895785
theorem B7329973 : Blo 1929435 7329973 := bbase (se 5 (by rfl) ⟨343592, by rfl⟩ : syracuseStep 7329973 = 687185) (by norm_num)
theorem B9773297 : Blo 1929435 9773297 := bstep (se 2 (by rfl) ⟨3664986, by rfl⟩ : syracuseStep 9773297 = 7329973) B7329973
theorem B6515531 : Blo 1929435 6515531 := bstep (se 1 (by rfl) ⟨4886648, by rfl⟩ : syracuseStep 6515531 = 9773297) B9773297
theorem B4343687 : Blo 1929435 4343687 := bstep (se 1 (by rfl) ⟨3257765, by rfl⟩ : syracuseStep 4343687 = 6515531) B6515531
theorem B2895791 : Blo 1929435 2895791 := bstep (se 1 (by rfl) ⟨2171843, by rfl⟩ : syracuseStep 2895791 = 4343687) B4343687
theorem B1930527 : Blo 1929435 1930527 := bstep (se 1 (by rfl) ⟨1447895, by rfl⟩ : syracuseStep 1930527 = 2895791) B2895791
theorem B2895797 : Blo 1929435 2895797 := bbase (se 5 (by rfl) ⟨135740, by rfl⟩ : syracuseStep 2895797 = 271481) (by norm_num)
theorem B1930531 : Blo 1929435 1930531 := bstep (se 1 (by rfl) ⟨1447898, by rfl⟩ : syracuseStep 1930531 = 2895797) B2895797
theorem B4886669 : Blo 1929435 4886669 := bbase (se 3 (by rfl) ⟨916250, by rfl⟩ : syracuseStep 4886669 = 1832501) (by norm_num)
theorem B3257779 : Blo 1929435 3257779 := bstep (se 1 (by rfl) ⟨2443334, by rfl⟩ : syracuseStep 3257779 = 4886669) B4886669
theorem B4343705 : Blo 1929435 4343705 := bstep (se 2 (by rfl) ⟨1628889, by rfl⟩ : syracuseStep 4343705 = 3257779) B3257779
theorem B2895803 : Blo 1929435 2895803 := bstep (se 1 (by rfl) ⟨2171852, by rfl⟩ : syracuseStep 2895803 = 4343705) B4343705
theorem B1930535 : Blo 1929435 1930535 := bstep (se 1 (by rfl) ⟨1447901, by rfl⟩ : syracuseStep 1930535 = 2895803) B2895803
theorem B2171857 : Blo 1929435 2171857 := bbase (se 2 (by rfl) ⟨814446, by rfl⟩ : syracuseStep 2171857 = 1628893) (by norm_num)
theorem B2895809 : Blo 1929435 2895809 := bstep (se 2 (by rfl) ⟨1085928, by rfl⟩ : syracuseStep 2895809 = 2171857) B2171857
theorem B1930539 : Blo 1929435 1930539 := bstep (se 1 (by rfl) ⟨1447904, by rfl⟩ : syracuseStep 1930539 = 2895809) B2895809
theorem B5218357 : Blo 1929435 5218357 := bbase (se 5 (by rfl) ⟨244610, by rfl⟩ : syracuseStep 5218357 = 489221) (by norm_num)
theorem B6957809 : Blo 1929435 6957809 := bstep (se 2 (by rfl) ⟨2609178, by rfl⟩ : syracuseStep 6957809 = 5218357) B5218357
theorem B4638539 : Blo 1929435 4638539 := bstep (se 1 (by rfl) ⟨3478904, by rfl⟩ : syracuseStep 4638539 = 6957809) B6957809
theorem B3092359 : Blo 1929435 3092359 := bstep (se 1 (by rfl) ⟨2319269, by rfl⟩ : syracuseStep 3092359 = 4638539) B4638539
theorem B4123145 : Blo 1929435 4123145 := bstep (se 2 (by rfl) ⟨1546179, by rfl⟩ : syracuseStep 4123145 = 3092359) B3092359
theorem B2748763 : Blo 1929435 2748763 := bstep (se 1 (by rfl) ⟨2061572, by rfl⟩ : syracuseStep 2748763 = 4123145) B4123145
theorem B3665017 : Blo 1929435 3665017 := bstep (se 2 (by rfl) ⟨1374381, by rfl⟩ : syracuseStep 3665017 = 2748763) B2748763
theorem B4886689 : Blo 1929435 4886689 := bstep (se 2 (by rfl) ⟨1832508, by rfl⟩ : syracuseStep 4886689 = 3665017) B3665017
theorem B6515585 : Blo 1929435 6515585 := bstep (se 2 (by rfl) ⟨2443344, by rfl⟩ : syracuseStep 6515585 = 4886689) B4886689
theorem B4343723 : Blo 1929435 4343723 := bstep (se 1 (by rfl) ⟨3257792, by rfl⟩ : syracuseStep 4343723 = 6515585) B6515585
theorem B2895815 : Blo 1929435 2895815 := bstep (se 1 (by rfl) ⟨2171861, by rfl⟩ : syracuseStep 2895815 = 4343723) B4343723
theorem B1930543 : Blo 1929435 1930543 := bstep (se 1 (by rfl) ⟨1447907, by rfl⟩ : syracuseStep 1930543 = 2895815) B2895815
theorem B2895821 : Blo 1929435 2895821 := bbase (se 3 (by rfl) ⟨542966, by rfl⟩ : syracuseStep 2895821 = 1085933) (by norm_num)
theorem B1930547 : Blo 1929435 1930547 := bstep (se 1 (by rfl) ⟨1447910, by rfl⟩ : syracuseStep 1930547 = 2895821) B2895821
theorem B4343741 : Blo 1929435 4343741 := bbase (se 3 (by rfl) ⟨814451, by rfl⟩ : syracuseStep 4343741 = 1628903) (by norm_num)
theorem B2895827 : Blo 1929435 2895827 := bstep (se 1 (by rfl) ⟨2171870, by rfl⟩ : syracuseStep 2895827 = 4343741) B4343741
theorem B1930551 : Blo 1929435 1930551 := bstep (se 1 (by rfl) ⟨1447913, by rfl⟩ : syracuseStep 1930551 = 2895827) B2895827
theorem B3257813 : Blo 1929435 3257813 := bbase (se 7 (by rfl) ⟨38177, by rfl⟩ : syracuseStep 3257813 = 76355) (by norm_num)
theorem B2171875 : Blo 1929435 2171875 := bstep (se 1 (by rfl) ⟨1628906, by rfl⟩ : syracuseStep 2171875 = 3257813) B3257813
theorem B2895833 : Blo 1929435 2895833 := bstep (se 2 (by rfl) ⟨1085937, by rfl⟩ : syracuseStep 2895833 = 2171875) B2171875
theorem B1930555 : Blo 1929435 1930555 := bstep (se 1 (by rfl) ⟨1447916, by rfl⟩ : syracuseStep 1930555 = 2895833) B2895833
theorem B8246357 : Blo 1929435 8246357 := bbase (se 8 (by rfl) ⟨48318, by rfl⟩ : syracuseStep 8246357 = 96637) (by norm_num)
theorem B5497571 : Blo 1929435 5497571 := bstep (se 1 (by rfl) ⟨4123178, by rfl⟩ : syracuseStep 5497571 = 8246357) B8246357
theorem B14660189 : Blo 1929435 14660189 := bstep (se 3 (by rfl) ⟨2748785, by rfl⟩ : syracuseStep 14660189 = 5497571) B5497571
theorem B9773459 : Blo 1929435 9773459 := bstep (se 1 (by rfl) ⟨7330094, by rfl⟩ : syracuseStep 9773459 = 14660189) B14660189
theorem B6515639 : Blo 1929435 6515639 := bstep (se 1 (by rfl) ⟨4886729, by rfl⟩ : syracuseStep 6515639 = 9773459) B9773459
theorem B4343759 : Blo 1929435 4343759 := bstep (se 1 (by rfl) ⟨3257819, by rfl⟩ : syracuseStep 4343759 = 6515639) B6515639
theorem B2895839 : Blo 1929435 2895839 := bstep (se 1 (by rfl) ⟨2171879, by rfl⟩ : syracuseStep 2895839 = 4343759) B4343759
theorem B1930559 : Blo 1929435 1930559 := bstep (se 1 (by rfl) ⟨1447919, by rfl⟩ : syracuseStep 1930559 = 2895839) B2895839
theorem B2895845 : Blo 1929435 2895845 := bbase (se 4 (by rfl) ⟨271485, by rfl⟩ : syracuseStep 2895845 = 542971) (by norm_num)
theorem B1930563 : Blo 1929435 1930563 := bstep (se 1 (by rfl) ⟨1447922, by rfl⟩ : syracuseStep 1930563 = 2895845) B2895845
theorem B11145205 : Blo 1929435 11145205 := bbase (se 5 (by rfl) ⟨522431, by rfl⟩ : syracuseStep 11145205 = 1044863) (by norm_num)
theorem B14860273 : Blo 1929435 14860273 := bstep (se 2 (by rfl) ⟨5572602, by rfl⟩ : syracuseStep 14860273 = 11145205) B11145205
theorem B19813697 : Blo 1929435 19813697 := bstep (se 2 (by rfl) ⟨7430136, by rfl⟩ : syracuseStep 19813697 = 14860273) B14860273
theorem B13209131 : Blo 1929435 13209131 := bstep (se 1 (by rfl) ⟨9906848, by rfl⟩ : syracuseStep 13209131 = 19813697) B19813697
theorem B8806087 : Blo 1929435 8806087 := bstep (se 1 (by rfl) ⟨6604565, by rfl⟩ : syracuseStep 8806087 = 13209131) B13209131
theorem B11741449 : Blo 1929435 11741449 := bstep (se 2 (by rfl) ⟨4403043, by rfl⟩ : syracuseStep 11741449 = 8806087) B8806087
theorem B15655265 : Blo 1929435 15655265 := bstep (se 2 (by rfl) ⟨5870724, by rfl⟩ : syracuseStep 15655265 = 11741449) B11741449
theorem B10436843 : Blo 1929435 10436843 := bstep (se 1 (by rfl) ⟨7827632, by rfl⟩ : syracuseStep 10436843 = 15655265) B15655265
theorem B6957895 : Blo 1929435 6957895 := bstep (se 1 (by rfl) ⟨5218421, by rfl⟩ : syracuseStep 6957895 = 10436843) B10436843
theorem B9277193 : Blo 1929435 9277193 := bstep (se 2 (by rfl) ⟨3478947, by rfl⟩ : syracuseStep 9277193 = 6957895) B6957895
theorem B6184795 : Blo 1929435 6184795 := bstep (se 1 (by rfl) ⟨4638596, by rfl⟩ : syracuseStep 6184795 = 9277193) B9277193
theorem B8246393 : Blo 1929435 8246393 := bstep (se 2 (by rfl) ⟨3092397, by rfl⟩ : syracuseStep 8246393 = 6184795) B6184795
theorem B5497595 : Blo 1929435 5497595 := bstep (se 1 (by rfl) ⟨4123196, by rfl⟩ : syracuseStep 5497595 = 8246393) B8246393
theorem B3665063 : Blo 1929435 3665063 := bstep (se 1 (by rfl) ⟨2748797, by rfl⟩ : syracuseStep 3665063 = 5497595) B5497595
theorem B2443375 : Blo 1929435 2443375 := bstep (se 1 (by rfl) ⟨1832531, by rfl⟩ : syracuseStep 2443375 = 3665063) B3665063
theorem B3257833 : Blo 1929435 3257833 := bstep (se 2 (by rfl) ⟨1221687, by rfl⟩ : syracuseStep 3257833 = 2443375) B2443375
theorem B4343777 : Blo 1929435 4343777 := bstep (se 2 (by rfl) ⟨1628916, by rfl⟩ : syracuseStep 4343777 = 3257833) B3257833
theorem B2895851 : Blo 1929435 2895851 := bstep (se 1 (by rfl) ⟨2171888, by rfl⟩ : syracuseStep 2895851 = 4343777) B4343777
theorem B1930567 : Blo 1929435 1930567 := bstep (se 1 (by rfl) ⟨1447925, by rfl⟩ : syracuseStep 1930567 = 2895851) B2895851
theorem B2171893 : Blo 1929435 2171893 := bbase (se 5 (by rfl) ⟨101807, by rfl⟩ : syracuseStep 2171893 = 203615) (by norm_num)
theorem B2895857 : Blo 1929435 2895857 := bstep (se 2 (by rfl) ⟨1085946, by rfl⟩ : syracuseStep 2895857 = 2171893) B2171893
theorem B1930571 : Blo 1929435 1930571 := bstep (se 1 (by rfl) ⟨1447928, by rfl⟩ : syracuseStep 1930571 = 2895857) B2895857
theorem B2443385 : Blo 1929435 2443385 := bbase (se 2 (by rfl) ⟨916269, by rfl⟩ : syracuseStep 2443385 = 1832539) (by norm_num)
theorem B6515693 : Blo 1929435 6515693 := bstep (se 3 (by rfl) ⟨1221692, by rfl⟩ : syracuseStep 6515693 = 2443385) B2443385
theorem B4343795 : Blo 1929435 4343795 := bstep (se 1 (by rfl) ⟨3257846, by rfl⟩ : syracuseStep 4343795 = 6515693) B6515693
theorem B2895863 : Blo 1929435 2895863 := bstep (se 1 (by rfl) ⟨2171897, by rfl⟩ : syracuseStep 2895863 = 4343795) B4343795
theorem B1930575 : Blo 1929435 1930575 := bstep (se 1 (by rfl) ⟨1447931, by rfl⟩ : syracuseStep 1930575 = 2895863) B2895863
theorem B2895869 : Blo 1929435 2895869 := bbase (se 3 (by rfl) ⟨542975, by rfl⟩ : syracuseStep 2895869 = 1085951) (by norm_num)
theorem B1930579 : Blo 1929435 1930579 := bstep (se 1 (by rfl) ⟨1447934, by rfl⟩ : syracuseStep 1930579 = 2895869) B2895869
theorem B4343813 : Blo 1929435 4343813 := bbase (se 4 (by rfl) ⟨407232, by rfl⟩ : syracuseStep 4343813 = 814465) (by norm_num)
theorem B2895875 : Blo 1929435 2895875 := bstep (se 1 (by rfl) ⟨2171906, by rfl⟩ : syracuseStep 2895875 = 4343813) B4343813
theorem B1930583 : Blo 1929435 1930583 := bstep (se 1 (by rfl) ⟨1447937, by rfl⟩ : syracuseStep 1930583 = 2895875) B2895875
theorem B3665101 : Blo 1929435 3665101 := bbase (se 3 (by rfl) ⟨687206, by rfl⟩ : syracuseStep 3665101 = 1374413) (by norm_num)
theorem B4886801 : Blo 1929435 4886801 := bstep (se 2 (by rfl) ⟨1832550, by rfl⟩ : syracuseStep 4886801 = 3665101) B3665101
theorem B3257867 : Blo 1929435 3257867 := bstep (se 1 (by rfl) ⟨2443400, by rfl⟩ : syracuseStep 3257867 = 4886801) B4886801
theorem B2171911 : Blo 1929435 2171911 := bstep (se 1 (by rfl) ⟨1628933, by rfl⟩ : syracuseStep 2171911 = 3257867) B3257867
theorem B2895881 : Blo 1929435 2895881 := bstep (se 2 (by rfl) ⟨1085955, by rfl⟩ : syracuseStep 2895881 = 2171911) B2171911
theorem B1930587 : Blo 1929435 1930587 := bstep (se 1 (by rfl) ⟨1447940, by rfl⟩ : syracuseStep 1930587 = 2895881) B2895881
theorem B9773621 : Blo 1929435 9773621 := bbase (se 5 (by rfl) ⟨458138, by rfl⟩ : syracuseStep 9773621 = 916277) (by norm_num)
theorem B6515747 : Blo 1929435 6515747 := bstep (se 1 (by rfl) ⟨4886810, by rfl⟩ : syracuseStep 6515747 = 9773621) B9773621
theorem B4343831 : Blo 1929435 4343831 := bstep (se 1 (by rfl) ⟨3257873, by rfl⟩ : syracuseStep 4343831 = 6515747) B6515747
theorem B2895887 : Blo 1929435 2895887 := bstep (se 1 (by rfl) ⟨2171915, by rfl⟩ : syracuseStep 2895887 = 4343831) B4343831
theorem B1930591 : Blo 1929435 1930591 := bstep (se 1 (by rfl) ⟨1447943, by rfl⟩ : syracuseStep 1930591 = 2895887) B2895887
theorem B2895893 : Blo 1929435 2895893 := bbase (se 6 (by rfl) ⟨67872, by rfl⟩ : syracuseStep 2895893 = 135745) (by norm_num)
theorem B1930595 : Blo 1929435 1930595 := bstep (se 1 (by rfl) ⟨1447946, by rfl⟩ : syracuseStep 1930595 = 2895893) B2895893
theorem B5870821 : Blo 1929435 5870821 := bbase (se 4 (by rfl) ⟨550389, by rfl⟩ : syracuseStep 5870821 = 1100779) (by norm_num)
theorem B7827761 : Blo 1929435 7827761 := bstep (se 2 (by rfl) ⟨2935410, by rfl⟩ : syracuseStep 7827761 = 5870821) B5870821
theorem B5218507 : Blo 1929435 5218507 := bstep (se 1 (by rfl) ⟨3913880, by rfl⟩ : syracuseStep 5218507 = 7827761) B7827761
theorem B6958009 : Blo 1929435 6958009 := bstep (se 2 (by rfl) ⟨2609253, by rfl⟩ : syracuseStep 6958009 = 5218507) B5218507
theorem B9277345 : Blo 1929435 9277345 := bstep (se 2 (by rfl) ⟨3479004, by rfl⟩ : syracuseStep 9277345 = 6958009) B6958009
theorem B12369793 : Blo 1929435 12369793 := bstep (se 2 (by rfl) ⟨4638672, by rfl⟩ : syracuseStep 12369793 = 9277345) B9277345
theorem B16493057 : Blo 1929435 16493057 := bstep (se 2 (by rfl) ⟨6184896, by rfl⟩ : syracuseStep 16493057 = 12369793) B12369793
theorem B10995371 : Blo 1929435 10995371 := bstep (se 1 (by rfl) ⟨8246528, by rfl⟩ : syracuseStep 10995371 = 16493057) B16493057
theorem B7330247 : Blo 1929435 7330247 := bstep (se 1 (by rfl) ⟨5497685, by rfl⟩ : syracuseStep 7330247 = 10995371) B10995371
theorem B4886831 : Blo 1929435 4886831 := bstep (se 1 (by rfl) ⟨3665123, by rfl⟩ : syracuseStep 4886831 = 7330247) B7330247
theorem B3257887 : Blo 1929435 3257887 := bstep (se 1 (by rfl) ⟨2443415, by rfl⟩ : syracuseStep 3257887 = 4886831) B4886831
theorem B4343849 : Blo 1929435 4343849 := bstep (se 2 (by rfl) ⟨1628943, by rfl⟩ : syracuseStep 4343849 = 3257887) B3257887
theorem B2895899 : Blo 1929435 2895899 := bstep (se 1 (by rfl) ⟨2171924, by rfl⟩ : syracuseStep 2895899 = 4343849) B4343849
theorem B1930599 : Blo 1929435 1930599 := bstep (se 1 (by rfl) ⟨1447949, by rfl⟩ : syracuseStep 1930599 = 2895899) B2895899
theorem B2171929 : Blo 1929435 2171929 := bbase (se 2 (by rfl) ⟨814473, by rfl⟩ : syracuseStep 2171929 = 1628947) (by norm_num)
theorem B2895905 : Blo 1929435 2895905 := bstep (se 2 (by rfl) ⟨1085964, by rfl⟩ : syracuseStep 2895905 = 2171929) B2171929
theorem B1930603 : Blo 1929435 1930603 := bstep (se 1 (by rfl) ⟨1447952, by rfl⟩ : syracuseStep 1930603 = 2895905) B2895905
theorem B7330277 : Blo 1929435 7330277 := bbase (se 4 (by rfl) ⟨687213, by rfl⟩ : syracuseStep 7330277 = 1374427) (by norm_num)
theorem B4886851 : Blo 1929435 4886851 := bstep (se 1 (by rfl) ⟨3665138, by rfl⟩ : syracuseStep 4886851 = 7330277) B7330277
theorem B6515801 : Blo 1929435 6515801 := bstep (se 2 (by rfl) ⟨2443425, by rfl⟩ : syracuseStep 6515801 = 4886851) B4886851
theorem B4343867 : Blo 1929435 4343867 := bstep (se 1 (by rfl) ⟨3257900, by rfl⟩ : syracuseStep 4343867 = 6515801) B6515801
theorem B2895911 : Blo 1929435 2895911 := bstep (se 1 (by rfl) ⟨2171933, by rfl⟩ : syracuseStep 2895911 = 4343867) B4343867
theorem B1930607 : Blo 1929435 1930607 := bstep (se 1 (by rfl) ⟨1447955, by rfl⟩ : syracuseStep 1930607 = 2895911) B2895911
theorem B2895917 : Blo 1929435 2895917 := bbase (se 3 (by rfl) ⟨542984, by rfl⟩ : syracuseStep 2895917 = 1085969) (by norm_num)
theorem B1930611 : Blo 1929435 1930611 := bstep (se 1 (by rfl) ⟨1447958, by rfl⟩ : syracuseStep 1930611 = 2895917) B2895917
theorem B4343885 : Blo 1929435 4343885 := bbase (se 3 (by rfl) ⟨814478, by rfl⟩ : syracuseStep 4343885 = 1628957) (by norm_num)
theorem B2895923 : Blo 1929435 2895923 := bstep (se 1 (by rfl) ⟨2171942, by rfl⟩ : syracuseStep 2895923 = 4343885) B4343885
theorem B1930615 : Blo 1929435 1930615 := bstep (se 1 (by rfl) ⟨1447961, by rfl⟩ : syracuseStep 1930615 = 2895923) B2895923
theorem B2443441 : Blo 1929435 2443441 := bbase (se 2 (by rfl) ⟨916290, by rfl⟩ : syracuseStep 2443441 = 1832581) (by norm_num)
theorem B3257921 : Blo 1929435 3257921 := bstep (se 2 (by rfl) ⟨1221720, by rfl⟩ : syracuseStep 3257921 = 2443441) B2443441
theorem B2171947 : Blo 1929435 2171947 := bstep (se 1 (by rfl) ⟨1628960, by rfl⟩ : syracuseStep 2171947 = 3257921) B3257921
theorem B2895929 : Blo 1929435 2895929 := bstep (se 2 (by rfl) ⟨1085973, by rfl⟩ : syracuseStep 2895929 = 2171947) B2171947
theorem B1930619 : Blo 1929435 1930619 := bstep (se 1 (by rfl) ⟨1447964, by rfl⟩ : syracuseStep 1930619 = 2895929) B2895929
theorem B2319365 : Blo 1929435 2319365 := bbase (se 4 (by rfl) ⟨217440, by rfl⟩ : syracuseStep 2319365 = 434881) (by norm_num)
theorem B6184973 : Blo 1929435 6184973 := bstep (se 3 (by rfl) ⟨1159682, by rfl⟩ : syracuseStep 6184973 = 2319365) B2319365
theorem B4123315 : Blo 1929435 4123315 := bstep (se 1 (by rfl) ⟨3092486, by rfl⟩ : syracuseStep 4123315 = 6184973) B6184973
theorem B21991013 : Blo 1929435 21991013 := bstep (se 4 (by rfl) ⟨2061657, by rfl⟩ : syracuseStep 21991013 = 4123315) B4123315
theorem B14660675 : Blo 1929435 14660675 := bstep (se 1 (by rfl) ⟨10995506, by rfl⟩ : syracuseStep 14660675 = 21991013) B21991013
theorem B9773783 : Blo 1929435 9773783 := bstep (se 1 (by rfl) ⟨7330337, by rfl⟩ : syracuseStep 9773783 = 14660675) B14660675
theorem B6515855 : Blo 1929435 6515855 := bstep (se 1 (by rfl) ⟨4886891, by rfl⟩ : syracuseStep 6515855 = 9773783) B9773783
theorem B4343903 : Blo 1929435 4343903 := bstep (se 1 (by rfl) ⟨3257927, by rfl⟩ : syracuseStep 4343903 = 6515855) B6515855
theorem B2895935 : Blo 1929435 2895935 := bstep (se 1 (by rfl) ⟨2171951, by rfl⟩ : syracuseStep 2895935 = 4343903) B4343903
theorem B1930623 : Blo 1929435 1930623 := bstep (se 1 (by rfl) ⟨1447967, by rfl⟩ : syracuseStep 1930623 = 2895935) B2895935
theorem B2895941 : Blo 1929435 2895941 := bbase (se 4 (by rfl) ⟨271494, by rfl⟩ : syracuseStep 2895941 = 542989) (by norm_num)
theorem B1930627 : Blo 1929435 1930627 := bstep (se 1 (by rfl) ⟨1447970, by rfl⟩ : syracuseStep 1930627 = 2895941) B2895941
theorem B3257941 : Blo 1929435 3257941 := bbase (se 8 (by rfl) ⟨19089, by rfl⟩ : syracuseStep 3257941 = 38179) (by norm_num)
theorem B4343921 : Blo 1929435 4343921 := bstep (se 2 (by rfl) ⟨1628970, by rfl⟩ : syracuseStep 4343921 = 3257941) B3257941
theorem B2895947 : Blo 1929435 2895947 := bstep (se 1 (by rfl) ⟨2171960, by rfl⟩ : syracuseStep 2895947 = 4343921) B4343921
theorem B1930631 : Blo 1929435 1930631 := bstep (se 1 (by rfl) ⟨1447973, by rfl⟩ : syracuseStep 1930631 = 2895947) B2895947
theorem B2171965 : Blo 1929435 2171965 := bbase (se 3 (by rfl) ⟨407243, by rfl⟩ : syracuseStep 2171965 = 814487) (by norm_num)
theorem B2895953 : Blo 1929435 2895953 := bstep (se 2 (by rfl) ⟨1085982, by rfl⟩ : syracuseStep 2895953 = 2171965) B2171965
theorem B1930635 : Blo 1929435 1930635 := bstep (se 1 (by rfl) ⟨1447976, by rfl⟩ : syracuseStep 1930635 = 2895953) B2895953
theorem B6515909 : Blo 1929435 6515909 := bbase (se 4 (by rfl) ⟨610866, by rfl⟩ : syracuseStep 6515909 = 1221733) (by norm_num)
theorem B4343939 : Blo 1929435 4343939 := bstep (se 1 (by rfl) ⟨3257954, by rfl⟩ : syracuseStep 4343939 = 6515909) B6515909
theorem B2895959 : Blo 1929435 2895959 := bstep (se 1 (by rfl) ⟨2171969, by rfl⟩ : syracuseStep 2895959 = 4343939) B4343939
theorem B1930639 : Blo 1929435 1930639 := bstep (se 1 (by rfl) ⟨1447979, by rfl⟩ : syracuseStep 1930639 = 2895959) B2895959
theorem B2895965 : Blo 1929435 2895965 := bbase (se 3 (by rfl) ⟨542993, by rfl⟩ : syracuseStep 2895965 = 1085987) (by norm_num)
theorem B1930643 : Blo 1929435 1930643 := bstep (se 1 (by rfl) ⟨1447982, by rfl⟩ : syracuseStep 1930643 = 2895965) B2895965
theorem B4343957 : Blo 1929435 4343957 := bbase (se 6 (by rfl) ⟨101811, by rfl⟩ : syracuseStep 4343957 = 203623) (by norm_num)
theorem B2895971 : Blo 1929435 2895971 := bstep (se 1 (by rfl) ⟨2171978, by rfl⟩ : syracuseStep 2895971 = 4343957) B4343957
theorem B1930647 : Blo 1929435 1930647 := bstep (se 1 (by rfl) ⟨1447985, by rfl⟩ : syracuseStep 1930647 = 2895971) B2895971
theorem B2748917 : Blo 1929435 2748917 := bbase (se 5 (by rfl) ⟨128855, by rfl⟩ : syracuseStep 2748917 = 257711) (by norm_num)
theorem B7330445 : Blo 1929435 7330445 := bstep (se 3 (by rfl) ⟨1374458, by rfl⟩ : syracuseStep 7330445 = 2748917) B2748917
theorem B4886963 : Blo 1929435 4886963 := bstep (se 1 (by rfl) ⟨3665222, by rfl⟩ : syracuseStep 4886963 = 7330445) B7330445
theorem B3257975 : Blo 1929435 3257975 := bstep (se 1 (by rfl) ⟨2443481, by rfl⟩ : syracuseStep 3257975 = 4886963) B4886963
theorem B2171983 : Blo 1929435 2171983 := bstep (se 1 (by rfl) ⟨1628987, by rfl⟩ : syracuseStep 2171983 = 3257975) B3257975
theorem B2895977 : Blo 1929435 2895977 := bstep (se 2 (by rfl) ⟨1085991, by rfl⟩ : syracuseStep 2895977 = 2171983) B2171983
theorem B1930651 : Blo 1929435 1930651 := bstep (se 1 (by rfl) ⟨1447988, by rfl⟩ : syracuseStep 1930651 = 2895977) B2895977
theorem B35225941 : Blo 1929435 35225941 := bbase (se 10 (by rfl) ⟨51600, by rfl⟩ : syracuseStep 35225941 = 103201) (by norm_num)
theorem B46967921 : Blo 1929435 46967921 := bstep (se 2 (by rfl) ⟨17612970, by rfl⟩ : syracuseStep 46967921 = 35225941) B35225941
theorem B31311947 : Blo 1929435 31311947 := bstep (se 1 (by rfl) ⟨23483960, by rfl⟩ : syracuseStep 31311947 = 46967921) B46967921
theorem B20874631 : Blo 1929435 20874631 := bstep (se 1 (by rfl) ⟨15655973, by rfl⟩ : syracuseStep 20874631 = 31311947) B31311947
theorem B27832841 : Blo 1929435 27832841 := bstep (se 2 (by rfl) ⟨10437315, by rfl⟩ : syracuseStep 27832841 = 20874631) B20874631
theorem B18555227 : Blo 1929435 18555227 := bstep (se 1 (by rfl) ⟨13916420, by rfl⟩ : syracuseStep 18555227 = 27832841) B27832841
theorem B12370151 : Blo 1929435 12370151 := bstep (se 1 (by rfl) ⟨9277613, by rfl⟩ : syracuseStep 12370151 = 18555227) B18555227
theorem B8246767 : Blo 1929435 8246767 := bstep (se 1 (by rfl) ⟨6185075, by rfl⟩ : syracuseStep 8246767 = 12370151) B12370151
theorem B10995689 : Blo 1929435 10995689 := bstep (se 2 (by rfl) ⟨4123383, by rfl⟩ : syracuseStep 10995689 = 8246767) B8246767
theorem B7330459 : Blo 1929435 7330459 := bstep (se 1 (by rfl) ⟨5497844, by rfl⟩ : syracuseStep 7330459 = 10995689) B10995689
theorem B9773945 : Blo 1929435 9773945 := bstep (se 2 (by rfl) ⟨3665229, by rfl⟩ : syracuseStep 9773945 = 7330459) B7330459
theorem B6515963 : Blo 1929435 6515963 := bstep (se 1 (by rfl) ⟨4886972, by rfl⟩ : syracuseStep 6515963 = 9773945) B9773945
theorem B4343975 : Blo 1929435 4343975 := bstep (se 1 (by rfl) ⟨3257981, by rfl⟩ : syracuseStep 4343975 = 6515963) B6515963
theorem B2895983 : Blo 1929435 2895983 := bstep (se 1 (by rfl) ⟨2171987, by rfl⟩ : syracuseStep 2895983 = 4343975) B4343975
theorem B1930655 : Blo 1929435 1930655 := bstep (se 1 (by rfl) ⟨1447991, by rfl⟩ : syracuseStep 1930655 = 2895983) B2895983
theorem B2895989 : Blo 1929435 2895989 := bbase (se 5 (by rfl) ⟨135749, by rfl⟩ : syracuseStep 2895989 = 271499) (by norm_num)
theorem B1930659 : Blo 1929435 1930659 := bstep (se 1 (by rfl) ⟨1447994, by rfl⟩ : syracuseStep 1930659 = 2895989) B2895989
theorem B3665245 : Blo 1929435 3665245 := bbase (se 3 (by rfl) ⟨687233, by rfl⟩ : syracuseStep 3665245 = 1374467) (by norm_num)
theorem B4886993 : Blo 1929435 4886993 := bstep (se 2 (by rfl) ⟨1832622, by rfl⟩ : syracuseStep 4886993 = 3665245) B3665245
theorem B3257995 : Blo 1929435 3257995 := bstep (se 1 (by rfl) ⟨2443496, by rfl⟩ : syracuseStep 3257995 = 4886993) B4886993
theorem B4343993 : Blo 1929435 4343993 := bstep (se 2 (by rfl) ⟨1628997, by rfl⟩ : syracuseStep 4343993 = 3257995) B3257995
theorem B2895995 : Blo 1929435 2895995 := bstep (se 1 (by rfl) ⟨2171996, by rfl⟩ : syracuseStep 2895995 = 4343993) B4343993
theorem B1930663 : Blo 1929435 1930663 := bstep (se 1 (by rfl) ⟨1447997, by rfl⟩ : syracuseStep 1930663 = 2895995) B2895995
theorem B2172001 : Blo 1929435 2172001 := bbase (se 2 (by rfl) ⟨814500, by rfl⟩ : syracuseStep 2172001 = 1629001) (by norm_num)
theorem B2896001 : Blo 1929435 2896001 := bstep (se 2 (by rfl) ⟨1086000, by rfl⟩ : syracuseStep 2896001 = 2172001) B2172001
theorem B1930667 : Blo 1929435 1930667 := bstep (se 1 (by rfl) ⟨1448000, by rfl⟩ : syracuseStep 1930667 = 2896001) B2896001
theorem B4887013 : Blo 1929435 4887013 := bbase (se 4 (by rfl) ⟨458157, by rfl⟩ : syracuseStep 4887013 = 916315) (by norm_num)
theorem B6516017 : Blo 1929435 6516017 := bstep (se 2 (by rfl) ⟨2443506, by rfl⟩ : syracuseStep 6516017 = 4887013) B4887013
theorem B4344011 : Blo 1929435 4344011 := bstep (se 1 (by rfl) ⟨3258008, by rfl⟩ : syracuseStep 4344011 = 6516017) B6516017
theorem B2896007 : Blo 1929435 2896007 := bstep (se 1 (by rfl) ⟨2172005, by rfl⟩ : syracuseStep 2896007 = 4344011) B4344011
theorem B1930671 : Blo 1929435 1930671 := bstep (se 1 (by rfl) ⟨1448003, by rfl⟩ : syracuseStep 1930671 = 2896007) B2896007
theorem B2896013 : Blo 1929435 2896013 := bbase (se 3 (by rfl) ⟨543002, by rfl⟩ : syracuseStep 2896013 = 1086005) (by norm_num)
theorem B1930675 : Blo 1929435 1930675 := bstep (se 1 (by rfl) ⟨1448006, by rfl⟩ : syracuseStep 1930675 = 2896013) B2896013
theorem B4344029 : Blo 1929435 4344029 := bbase (se 3 (by rfl) ⟨814505, by rfl⟩ : syracuseStep 4344029 = 1629011) (by norm_num)
theorem B2896019 : Blo 1929435 2896019 := bstep (se 1 (by rfl) ⟨2172014, by rfl⟩ : syracuseStep 2896019 = 4344029) B4344029
theorem B1930679 : Blo 1929435 1930679 := bstep (se 1 (by rfl) ⟨1448009, by rfl⟩ : syracuseStep 1930679 = 2896019) B2896019
theorem B3258029 : Blo 1929435 3258029 := bbase (se 3 (by rfl) ⟨610880, by rfl⟩ : syracuseStep 3258029 = 1221761) (by norm_num)
theorem B2172019 : Blo 1929435 2172019 := bstep (se 1 (by rfl) ⟨1629014, by rfl⟩ : syracuseStep 2172019 = 3258029) B3258029
theorem B2896025 : Blo 1929435 2896025 := bstep (se 2 (by rfl) ⟨1086009, by rfl⟩ : syracuseStep 2896025 = 2172019) B2172019
theorem B1930683 : Blo 1929435 1930683 := bstep (se 1 (by rfl) ⟨1448012, by rfl⟩ : syracuseStep 1930683 = 2896025) B2896025
theorem B31739669 : Blo 1929435 31739669 := bbase (se 6 (by rfl) ⟨743898, by rfl⟩ : syracuseStep 31739669 = 1487797) (by norm_num)
theorem B21159779 : Blo 1929435 21159779 := bstep (se 1 (by rfl) ⟨15869834, by rfl⟩ : syracuseStep 21159779 = 31739669) B31739669
theorem B56426077 : Blo 1929435 56426077 := bstep (se 3 (by rfl) ⟨10579889, by rfl⟩ : syracuseStep 56426077 = 21159779) B21159779
theorem B300939077 : Blo 1929435 300939077 := bstep (se 4 (by rfl) ⟨28213038, by rfl⟩ : syracuseStep 300939077 = 56426077) B56426077
theorem B802504205 : Blo 1929435 802504205 := bstep (se 3 (by rfl) ⟨150469538, by rfl⟩ : syracuseStep 802504205 = 300939077) B300939077
theorem B535002803 : Blo 1929435 535002803 := bstep (se 1 (by rfl) ⟨401252102, by rfl⟩ : syracuseStep 535002803 = 802504205) B802504205
theorem B356668535 : Blo 1929435 356668535 := bstep (se 1 (by rfl) ⟨267501401, by rfl⟩ : syracuseStep 356668535 = 535002803) B535002803
theorem B237779023 : Blo 1929435 237779023 := bstep (se 1 (by rfl) ⟨178334267, by rfl⟩ : syracuseStep 237779023 = 356668535) B356668535
theorem B317038697 : Blo 1929435 317038697 := bstep (se 2 (by rfl) ⟨118889511, by rfl⟩ : syracuseStep 317038697 = 237779023) B237779023
theorem B211359131 : Blo 1929435 211359131 := bstep (se 1 (by rfl) ⟨158519348, by rfl⟩ : syracuseStep 211359131 = 317038697) B317038697
theorem B140906087 : Blo 1929435 140906087 := bstep (se 1 (by rfl) ⟨105679565, by rfl⟩ : syracuseStep 140906087 = 211359131) B211359131
theorem B93937391 : Blo 1929435 93937391 := bstep (se 1 (by rfl) ⟨70453043, by rfl⟩ : syracuseStep 93937391 = 140906087) B140906087
theorem B62624927 : Blo 1929435 62624927 := bstep (se 1 (by rfl) ⟨46968695, by rfl⟩ : syracuseStep 62624927 = 93937391) B93937391
theorem B41749951 : Blo 1929435 41749951 := bstep (se 1 (by rfl) ⟨31312463, by rfl⟩ : syracuseStep 41749951 = 62624927) B62624927
theorem B55666601 : Blo 1929435 55666601 := bstep (se 2 (by rfl) ⟨20874975, by rfl⟩ : syracuseStep 55666601 = 41749951) B41749951
theorem B37111067 : Blo 1929435 37111067 := bstep (se 1 (by rfl) ⟨27833300, by rfl⟩ : syracuseStep 37111067 = 55666601) B55666601
theorem B24740711 : Blo 1929435 24740711 := bstep (se 1 (by rfl) ⟨18555533, by rfl⟩ : syracuseStep 24740711 = 37111067) B37111067
theorem B16493807 : Blo 1929435 16493807 := bstep (se 1 (by rfl) ⟨12370355, by rfl⟩ : syracuseStep 16493807 = 24740711) B24740711
theorem B10995871 : Blo 1929435 10995871 := bstep (se 1 (by rfl) ⟨8246903, by rfl⟩ : syracuseStep 10995871 = 16493807) B16493807
theorem B14661161 : Blo 1929435 14661161 := bstep (se 2 (by rfl) ⟨5497935, by rfl⟩ : syracuseStep 14661161 = 10995871) B10995871
theorem B9774107 : Blo 1929435 9774107 := bstep (se 1 (by rfl) ⟨7330580, by rfl⟩ : syracuseStep 9774107 = 14661161) B14661161
theorem B6516071 : Blo 1929435 6516071 := bstep (se 1 (by rfl) ⟨4887053, by rfl⟩ : syracuseStep 6516071 = 9774107) B9774107
theorem B4344047 : Blo 1929435 4344047 := bstep (se 1 (by rfl) ⟨3258035, by rfl⟩ : syracuseStep 4344047 = 6516071) B6516071
theorem B2896031 : Blo 1929435 2896031 := bstep (se 1 (by rfl) ⟨2172023, by rfl⟩ : syracuseStep 2896031 = 4344047) B4344047
theorem B1930687 : Blo 1929435 1930687 := bstep (se 1 (by rfl) ⟨1448015, by rfl⟩ : syracuseStep 1930687 = 2896031) B2896031
theorem B2896037 : Blo 1929435 2896037 := bbase (se 4 (by rfl) ⟨271503, by rfl⟩ : syracuseStep 2896037 = 543007) (by norm_num)
theorem B1930691 : Blo 1929435 1930691 := bstep (se 1 (by rfl) ⟨1448018, by rfl⟩ : syracuseStep 1930691 = 2896037) B2896037
theorem B2443537 : Blo 1929435 2443537 := bbase (se 2 (by rfl) ⟨916326, by rfl⟩ : syracuseStep 2443537 = 1832653) (by norm_num)
theorem B3258049 : Blo 1929435 3258049 := bstep (se 2 (by rfl) ⟨1221768, by rfl⟩ : syracuseStep 3258049 = 2443537) B2443537
theorem B4344065 : Blo 1929435 4344065 := bstep (se 2 (by rfl) ⟨1629024, by rfl⟩ : syracuseStep 4344065 = 3258049) B3258049
theorem B2896043 : Blo 1929435 2896043 := bstep (se 1 (by rfl) ⟨2172032, by rfl⟩ : syracuseStep 2896043 = 4344065) B4344065
theorem B1930695 : Blo 1929435 1930695 := bstep (se 1 (by rfl) ⟨1448021, by rfl⟩ : syracuseStep 1930695 = 2896043) B2896043
theorem B2172037 : Blo 1929435 2172037 := bbase (se 4 (by rfl) ⟨203628, by rfl⟩ : syracuseStep 2172037 = 407257) (by norm_num)
theorem B2896049 : Blo 1929435 2896049 := bstep (se 2 (by rfl) ⟨1086018, by rfl⟩ : syracuseStep 2896049 = 2172037) B2172037
theorem B1930699 : Blo 1929435 1930699 := bstep (se 1 (by rfl) ⟨1448024, by rfl⟩ : syracuseStep 1930699 = 2896049) B2896049
theorem B20875157 : Blo 1929435 20875157 := bbase (se 6 (by rfl) ⟨489261, by rfl⟩ : syracuseStep 20875157 = 978523) (by norm_num)
theorem B13916771 : Blo 1929435 13916771 := bstep (se 1 (by rfl) ⟨10437578, by rfl⟩ : syracuseStep 13916771 = 20875157) B20875157
theorem B9277847 : Blo 1929435 9277847 := bstep (se 1 (by rfl) ⟨6958385, by rfl⟩ : syracuseStep 9277847 = 13916771) B13916771
theorem B6185231 : Blo 1929435 6185231 := bstep (se 1 (by rfl) ⟨4638923, by rfl⟩ : syracuseStep 6185231 = 9277847) B9277847
theorem B4123487 : Blo 1929435 4123487 := bstep (se 1 (by rfl) ⟨3092615, by rfl⟩ : syracuseStep 4123487 = 6185231) B6185231
theorem B2748991 : Blo 1929435 2748991 := bstep (se 1 (by rfl) ⟨2061743, by rfl⟩ : syracuseStep 2748991 = 4123487) B4123487
theorem B3665321 : Blo 1929435 3665321 := bstep (se 2 (by rfl) ⟨1374495, by rfl⟩ : syracuseStep 3665321 = 2748991) B2748991
theorem B2443547 : Blo 1929435 2443547 := bstep (se 1 (by rfl) ⟨1832660, by rfl⟩ : syracuseStep 2443547 = 3665321) B3665321
theorem B6516125 : Blo 1929435 6516125 := bstep (se 3 (by rfl) ⟨1221773, by rfl⟩ : syracuseStep 6516125 = 2443547) B2443547
theorem B4344083 : Blo 1929435 4344083 := bstep (se 1 (by rfl) ⟨3258062, by rfl⟩ : syracuseStep 4344083 = 6516125) B6516125
theorem B2896055 : Blo 1929435 2896055 := bstep (se 1 (by rfl) ⟨2172041, by rfl⟩ : syracuseStep 2896055 = 4344083) B4344083
theorem B1930703 : Blo 1929435 1930703 := bstep (se 1 (by rfl) ⟨1448027, by rfl⟩ : syracuseStep 1930703 = 2896055) B2896055
theorem B2896061 : Blo 1929435 2896061 := bbase (se 3 (by rfl) ⟨543011, by rfl⟩ : syracuseStep 2896061 = 1086023) (by norm_num)
theorem B1930707 : Blo 1929435 1930707 := bstep (se 1 (by rfl) ⟨1448030, by rfl⟩ : syracuseStep 1930707 = 2896061) B2896061
theorem B4344101 : Blo 1929435 4344101 := bbase (se 4 (by rfl) ⟨407259, by rfl⟩ : syracuseStep 4344101 = 814519) (by norm_num)
theorem B2896067 : Blo 1929435 2896067 := bstep (se 1 (by rfl) ⟨2172050, by rfl⟩ : syracuseStep 2896067 = 4344101) B4344101
theorem B1930711 : Blo 1929435 1930711 := bstep (se 1 (by rfl) ⟨1448033, by rfl⟩ : syracuseStep 1930711 = 2896067) B2896067
theorem B4887125 : Blo 1929435 4887125 := bbase (se 8 (by rfl) ⟨28635, by rfl⟩ : syracuseStep 4887125 = 57271) (by norm_num)
theorem B3258083 : Blo 1929435 3258083 := bstep (se 1 (by rfl) ⟨2443562, by rfl⟩ : syracuseStep 3258083 = 4887125) B4887125
theorem B2172055 : Blo 1929435 2172055 := bstep (se 1 (by rfl) ⟨1629041, by rfl⟩ : syracuseStep 2172055 = 3258083) B3258083
theorem B2896073 : Blo 1929435 2896073 := bstep (se 2 (by rfl) ⟨1086027, by rfl⟩ : syracuseStep 2896073 = 2172055) B2172055
theorem B1930715 : Blo 1929435 1930715 := bstep (se 1 (by rfl) ⟨1448036, by rfl⟩ : syracuseStep 1930715 = 2896073) B2896073
theorem B3479221 : Blo 1929435 3479221 := bbase (se 5 (by rfl) ⟨163088, by rfl⟩ : syracuseStep 3479221 = 326177) (by norm_num)
theorem B4638961 : Blo 1929435 4638961 := bstep (se 2 (by rfl) ⟨1739610, by rfl⟩ : syracuseStep 4638961 = 3479221) B3479221
theorem B6185281 : Blo 1929435 6185281 := bstep (se 2 (by rfl) ⟨2319480, by rfl⟩ : syracuseStep 6185281 = 4638961) B4638961
theorem B8247041 : Blo 1929435 8247041 := bstep (se 2 (by rfl) ⟨3092640, by rfl⟩ : syracuseStep 8247041 = 6185281) B6185281
theorem B5498027 : Blo 1929435 5498027 := bstep (se 1 (by rfl) ⟨4123520, by rfl⟩ : syracuseStep 5498027 = 8247041) B8247041
theorem B3665351 : Blo 1929435 3665351 := bstep (se 1 (by rfl) ⟨2749013, by rfl⟩ : syracuseStep 3665351 = 5498027) B5498027
theorem B9774269 : Blo 1929435 9774269 := bstep (se 3 (by rfl) ⟨1832675, by rfl⟩ : syracuseStep 9774269 = 3665351) B3665351
theorem B6516179 : Blo 1929435 6516179 := bstep (se 1 (by rfl) ⟨4887134, by rfl⟩ : syracuseStep 6516179 = 9774269) B9774269
theorem B4344119 : Blo 1929435 4344119 := bstep (se 1 (by rfl) ⟨3258089, by rfl⟩ : syracuseStep 4344119 = 6516179) B6516179
theorem B2896079 : Blo 1929435 2896079 := bstep (se 1 (by rfl) ⟨2172059, by rfl⟩ : syracuseStep 2896079 = 4344119) B4344119
theorem B1930719 : Blo 1929435 1930719 := bstep (se 1 (by rfl) ⟨1448039, by rfl⟩ : syracuseStep 1930719 = 2896079) B2896079
theorem B2896085 : Blo 1929435 2896085 := bbase (se 7 (by rfl) ⟨33938, by rfl⟩ : syracuseStep 2896085 = 67877) (by norm_num)
theorem B1930723 : Blo 1929435 1930723 := bstep (se 1 (by rfl) ⟨1448042, by rfl⟩ : syracuseStep 1930723 = 2896085) B2896085
theorem B2061769 : Blo 1929435 2061769 := bbase (se 2 (by rfl) ⟨773163, by rfl⟩ : syracuseStep 2061769 = 1546327) (by norm_num)
theorem B2749025 : Blo 1929435 2749025 := bstep (se 2 (by rfl) ⟨1030884, by rfl⟩ : syracuseStep 2749025 = 2061769) B2061769
theorem B7330733 : Blo 1929435 7330733 := bstep (se 3 (by rfl) ⟨1374512, by rfl⟩ : syracuseStep 7330733 = 2749025) B2749025
theorem B4887155 : Blo 1929435 4887155 := bstep (se 1 (by rfl) ⟨3665366, by rfl⟩ : syracuseStep 4887155 = 7330733) B7330733
theorem B3258103 : Blo 1929435 3258103 := bstep (se 1 (by rfl) ⟨2443577, by rfl⟩ : syracuseStep 3258103 = 4887155) B4887155
theorem B4344137 : Blo 1929435 4344137 := bstep (se 2 (by rfl) ⟨1629051, by rfl⟩ : syracuseStep 4344137 = 3258103) B3258103
theorem B2896091 : Blo 1929435 2896091 := bstep (se 1 (by rfl) ⟨2172068, by rfl⟩ : syracuseStep 2896091 = 4344137) B4344137
theorem B1930727 : Blo 1929435 1930727 := bstep (se 1 (by rfl) ⟨1448045, by rfl⟩ : syracuseStep 1930727 = 2896091) B2896091
theorem B2172073 : Blo 1929435 2172073 := bbase (se 2 (by rfl) ⟨814527, by rfl⟩ : syracuseStep 2172073 = 1629055) (by norm_num)
theorem B2896097 : Blo 1929435 2896097 := bstep (se 2 (by rfl) ⟨1086036, by rfl⟩ : syracuseStep 2896097 = 2172073) B2172073
theorem B1930731 : Blo 1929435 1930731 := bstep (se 1 (by rfl) ⟨1448048, by rfl⟩ : syracuseStep 1930731 = 2896097) B2896097
theorem B8247109 : Blo 1929435 8247109 := bbase (se 4 (by rfl) ⟨773166, by rfl⟩ : syracuseStep 8247109 = 1546333) (by norm_num)
theorem B10996145 : Blo 1929435 10996145 := bstep (se 2 (by rfl) ⟨4123554, by rfl⟩ : syracuseStep 10996145 = 8247109) B8247109
theorem B7330763 : Blo 1929435 7330763 := bstep (se 1 (by rfl) ⟨5498072, by rfl⟩ : syracuseStep 7330763 = 10996145) B10996145
theorem B4887175 : Blo 1929435 4887175 := bstep (se 1 (by rfl) ⟨3665381, by rfl⟩ : syracuseStep 4887175 = 7330763) B7330763
theorem B6516233 : Blo 1929435 6516233 := bstep (se 2 (by rfl) ⟨2443587, by rfl⟩ : syracuseStep 6516233 = 4887175) B4887175
theorem B4344155 : Blo 1929435 4344155 := bstep (se 1 (by rfl) ⟨3258116, by rfl⟩ : syracuseStep 4344155 = 6516233) B6516233
theorem B2896103 : Blo 1929435 2896103 := bstep (se 1 (by rfl) ⟨2172077, by rfl⟩ : syracuseStep 2896103 = 4344155) B4344155
theorem B1930735 : Blo 1929435 1930735 := bstep (se 1 (by rfl) ⟨1448051, by rfl⟩ : syracuseStep 1930735 = 2896103) B2896103
theorem B2896109 : Blo 1929435 2896109 := bbase (se 3 (by rfl) ⟨543020, by rfl⟩ : syracuseStep 2896109 = 1086041) (by norm_num)
theorem B1930739 : Blo 1929435 1930739 := bstep (se 1 (by rfl) ⟨1448054, by rfl⟩ : syracuseStep 1930739 = 2896109) B2896109
theorem B4344173 : Blo 1929435 4344173 := bbase (se 3 (by rfl) ⟨814532, by rfl⟩ : syracuseStep 4344173 = 1629065) (by norm_num)
theorem B2896115 : Blo 1929435 2896115 := bstep (se 1 (by rfl) ⟨2172086, by rfl⟩ : syracuseStep 2896115 = 4344173) B4344173
theorem B1930743 : Blo 1929435 1930743 := bstep (se 1 (by rfl) ⟨1448057, by rfl⟩ : syracuseStep 1930743 = 2896115) B2896115
theorem B3665405 : Blo 1929435 3665405 := bbase (se 3 (by rfl) ⟨687263, by rfl⟩ : syracuseStep 3665405 = 1374527) (by norm_num)
theorem B2443603 : Blo 1929435 2443603 := bstep (se 1 (by rfl) ⟨1832702, by rfl⟩ : syracuseStep 2443603 = 3665405) B3665405
theorem B3258137 : Blo 1929435 3258137 := bstep (se 2 (by rfl) ⟨1221801, by rfl⟩ : syracuseStep 3258137 = 2443603) B2443603
theorem B2172091 : Blo 1929435 2172091 := bstep (se 1 (by rfl) ⟨1629068, by rfl⟩ : syracuseStep 2172091 = 3258137) B3258137
theorem B2896121 : Blo 1929435 2896121 := bstep (se 2 (by rfl) ⟨1086045, by rfl⟩ : syracuseStep 2896121 = 2172091) B2172091
theorem B1930747 : Blo 1929435 1930747 := bstep (se 1 (by rfl) ⟨1448060, by rfl⟩ : syracuseStep 1930747 = 2896121) B2896121
theorem B4639037 : Blo 1929435 4639037 := bbase (se 3 (by rfl) ⟨869819, by rfl⟩ : syracuseStep 4639037 = 1739639) (by norm_num)
theorem B49483061 : Blo 1929435 49483061 := bstep (se 5 (by rfl) ⟨2319518, by rfl⟩ : syracuseStep 49483061 = 4639037) B4639037
theorem B32988707 : Blo 1929435 32988707 := bstep (se 1 (by rfl) ⟨24741530, by rfl⟩ : syracuseStep 32988707 = 49483061) B49483061
theorem B21992471 : Blo 1929435 21992471 := bstep (se 1 (by rfl) ⟨16494353, by rfl⟩ : syracuseStep 21992471 = 32988707) B32988707
theorem B14661647 : Blo 1929435 14661647 := bstep (se 1 (by rfl) ⟨10996235, by rfl⟩ : syracuseStep 14661647 = 21992471) B21992471
theorem B9774431 : Blo 1929435 9774431 := bstep (se 1 (by rfl) ⟨7330823, by rfl⟩ : syracuseStep 9774431 = 14661647) B14661647
theorem B6516287 : Blo 1929435 6516287 := bstep (se 1 (by rfl) ⟨4887215, by rfl⟩ : syracuseStep 6516287 = 9774431) B9774431
theorem B4344191 : Blo 1929435 4344191 := bstep (se 1 (by rfl) ⟨3258143, by rfl⟩ : syracuseStep 4344191 = 6516287) B6516287
theorem B2896127 : Blo 1929435 2896127 := bstep (se 1 (by rfl) ⟨2172095, by rfl⟩ : syracuseStep 2896127 = 4344191) B4344191
theorem B1930751 : Blo 1929435 1930751 := bstep (se 1 (by rfl) ⟨1448063, by rfl⟩ : syracuseStep 1930751 = 2896127) B2896127
theorem B2896133 : Blo 1929435 2896133 := bbase (se 4 (by rfl) ⟨271512, by rfl⟩ : syracuseStep 2896133 = 543025) (by norm_num)
theorem B1930755 : Blo 1929435 1930755 := bstep (se 1 (by rfl) ⟨1448066, by rfl⟩ : syracuseStep 1930755 = 2896133) B2896133
theorem B3258157 : Blo 1929435 3258157 := bbase (se 3 (by rfl) ⟨610904, by rfl⟩ : syracuseStep 3258157 = 1221809) (by norm_num)
theorem B4344209 : Blo 1929435 4344209 := bstep (se 2 (by rfl) ⟨1629078, by rfl⟩ : syracuseStep 4344209 = 3258157) B3258157
theorem B2896139 : Blo 1929435 2896139 := bstep (se 1 (by rfl) ⟨2172104, by rfl⟩ : syracuseStep 2896139 = 4344209) B4344209
theorem B1930759 : Blo 1929435 1930759 := bstep (se 1 (by rfl) ⟨1448069, by rfl⟩ : syracuseStep 1930759 = 2896139) B2896139
theorem B2172109 : Blo 1929435 2172109 := bbase (se 3 (by rfl) ⟨407270, by rfl⟩ : syracuseStep 2172109 = 814541) (by norm_num)
theorem B2896145 : Blo 1929435 2896145 := bstep (se 2 (by rfl) ⟨1086054, by rfl⟩ : syracuseStep 2896145 = 2172109) B2172109
theorem B1930763 : Blo 1929435 1930763 := bstep (se 1 (by rfl) ⟨1448072, by rfl⟩ : syracuseStep 1930763 = 2896145) B2896145
theorem B6516341 : Blo 1929435 6516341 := bbase (se 5 (by rfl) ⟨305453, by rfl⟩ : syracuseStep 6516341 = 610907) (by norm_num)
theorem B4344227 : Blo 1929435 4344227 := bstep (se 1 (by rfl) ⟨3258170, by rfl⟩ : syracuseStep 4344227 = 6516341) B6516341
theorem B2896151 : Blo 1929435 2896151 := bstep (se 1 (by rfl) ⟨2172113, by rfl⟩ : syracuseStep 2896151 = 4344227) B4344227
theorem B1930767 : Blo 1929435 1930767 := bstep (se 1 (by rfl) ⟨1448075, by rfl⟩ : syracuseStep 1930767 = 2896151) B2896151
theorem B2896157 : Blo 1929435 2896157 := bbase (se 3 (by rfl) ⟨543029, by rfl⟩ : syracuseStep 2896157 = 1086059) (by norm_num)
theorem B1930771 : Blo 1929435 1930771 := bstep (se 1 (by rfl) ⟨1448078, by rfl⟩ : syracuseStep 1930771 = 2896157) B2896157
theorem B4344245 : Blo 1929435 4344245 := bbase (se 5 (by rfl) ⟨203636, by rfl⟩ : syracuseStep 4344245 = 407273) (by norm_num)
theorem B2896163 : Blo 1929435 2896163 := bstep (se 1 (by rfl) ⟨2172122, by rfl⟩ : syracuseStep 2896163 = 4344245) B4344245
theorem B1930775 : Blo 1929435 1930775 := bstep (se 1 (by rfl) ⟨1448081, by rfl⟩ : syracuseStep 1930775 = 2896163) B2896163
theorem B2319553 : Blo 1929435 2319553 := bbase (se 2 (by rfl) ⟨869832, by rfl⟩ : syracuseStep 2319553 = 1739665) (by norm_num)
theorem B3092737 : Blo 1929435 3092737 := bstep (se 2 (by rfl) ⟨1159776, by rfl⟩ : syracuseStep 3092737 = 2319553) B2319553
theorem B4123649 : Blo 1929435 4123649 := bstep (se 2 (by rfl) ⟨1546368, by rfl⟩ : syracuseStep 4123649 = 3092737) B3092737
theorem B10996397 : Blo 1929435 10996397 := bstep (se 3 (by rfl) ⟨2061824, by rfl⟩ : syracuseStep 10996397 = 4123649) B4123649
theorem B7330931 : Blo 1929435 7330931 := bstep (se 1 (by rfl) ⟨5498198, by rfl⟩ : syracuseStep 7330931 = 10996397) B10996397
theorem B4887287 : Blo 1929435 4887287 := bstep (se 1 (by rfl) ⟨3665465, by rfl⟩ : syracuseStep 4887287 = 7330931) B7330931
theorem B3258191 : Blo 1929435 3258191 := bstep (se 1 (by rfl) ⟨2443643, by rfl⟩ : syracuseStep 3258191 = 4887287) B4887287
theorem B2172127 : Blo 1929435 2172127 := bstep (se 1 (by rfl) ⟨1629095, by rfl⟩ : syracuseStep 2172127 = 3258191) B3258191
theorem B2896169 : Blo 1929435 2896169 := bstep (se 2 (by rfl) ⟨1086063, by rfl⟩ : syracuseStep 2896169 = 2172127) B2172127
theorem B1930779 : Blo 1929435 1930779 := bstep (se 1 (by rfl) ⟨1448084, by rfl⟩ : syracuseStep 1930779 = 2896169) B2896169
theorem B3302653 : Blo 1929435 3302653 := bbase (se 3 (by rfl) ⟨619247, by rfl⟩ : syracuseStep 3302653 = 1238495) (by norm_num)
theorem B4403537 : Blo 1929435 4403537 := bstep (se 2 (by rfl) ⟨1651326, by rfl⟩ : syracuseStep 4403537 = 3302653) B3302653
theorem B2935691 : Blo 1929435 2935691 := bstep (se 1 (by rfl) ⟨2201768, by rfl⟩ : syracuseStep 2935691 = 4403537) B4403537
theorem B1957127 : Blo 1929435 1957127 := bstep (se 1 (by rfl) ⟨1467845, by rfl⟩ : syracuseStep 1957127 = 2935691) B2935691
theorem B5219005 : Blo 1929435 5219005 := bstep (se 3 (by rfl) ⟨978563, by rfl⟩ : syracuseStep 5219005 = 1957127) B1957127
theorem B6958673 : Blo 1929435 6958673 := bstep (se 2 (by rfl) ⟨2609502, by rfl⟩ : syracuseStep 6958673 = 5219005) B5219005
theorem B4639115 : Blo 1929435 4639115 := bstep (se 1 (by rfl) ⟨3479336, by rfl⟩ : syracuseStep 4639115 = 6958673) B6958673
theorem B3092743 : Blo 1929435 3092743 := bstep (se 1 (by rfl) ⟨2319557, by rfl⟩ : syracuseStep 3092743 = 4639115) B4639115
theorem B4123657 : Blo 1929435 4123657 := bstep (se 2 (by rfl) ⟨1546371, by rfl⟩ : syracuseStep 4123657 = 3092743) B3092743
theorem B5498209 : Blo 1929435 5498209 := bstep (se 2 (by rfl) ⟨2061828, by rfl⟩ : syracuseStep 5498209 = 4123657) B4123657
theorem B7330945 : Blo 1929435 7330945 := bstep (se 2 (by rfl) ⟨2749104, by rfl⟩ : syracuseStep 7330945 = 5498209) B5498209
theorem B9774593 : Blo 1929435 9774593 := bstep (se 2 (by rfl) ⟨3665472, by rfl⟩ : syracuseStep 9774593 = 7330945) B7330945
theorem B6516395 : Blo 1929435 6516395 := bstep (se 1 (by rfl) ⟨4887296, by rfl⟩ : syracuseStep 6516395 = 9774593) B9774593
theorem B4344263 : Blo 1929435 4344263 := bstep (se 1 (by rfl) ⟨3258197, by rfl⟩ : syracuseStep 4344263 = 6516395) B6516395
theorem B2896175 : Blo 1929435 2896175 := bstep (se 1 (by rfl) ⟨2172131, by rfl⟩ : syracuseStep 2896175 = 4344263) B4344263
theorem B1930783 : Blo 1929435 1930783 := bstep (se 1 (by rfl) ⟨1448087, by rfl⟩ : syracuseStep 1930783 = 2896175) B2896175
theorem B2896181 : Blo 1929435 2896181 := bbase (se 5 (by rfl) ⟨135758, by rfl⟩ : syracuseStep 2896181 = 271517) (by norm_num)
theorem B1930787 : Blo 1929435 1930787 := bstep (se 1 (by rfl) ⟨1448090, by rfl⟩ : syracuseStep 1930787 = 2896181) B2896181
theorem B4887317 : Blo 1929435 4887317 := bbase (se 6 (by rfl) ⟨114546, by rfl⟩ : syracuseStep 4887317 = 229093) (by norm_num)
theorem B3258211 : Blo 1929435 3258211 := bstep (se 1 (by rfl) ⟨2443658, by rfl⟩ : syracuseStep 3258211 = 4887317) B4887317
theorem B4344281 : Blo 1929435 4344281 := bstep (se 2 (by rfl) ⟨1629105, by rfl⟩ : syracuseStep 4344281 = 3258211) B3258211
theorem B2896187 : Blo 1929435 2896187 := bstep (se 1 (by rfl) ⟨2172140, by rfl⟩ : syracuseStep 2896187 = 4344281) B4344281
theorem B1930791 : Blo 1929435 1930791 := bstep (se 1 (by rfl) ⟨1448093, by rfl⟩ : syracuseStep 1930791 = 2896187) B2896187
theorem B2172145 : Blo 1929435 2172145 := bbase (se 2 (by rfl) ⟨814554, by rfl⟩ : syracuseStep 2172145 = 1629109) (by norm_num)
theorem B2896193 : Blo 1929435 2896193 := bstep (se 2 (by rfl) ⟨1086072, by rfl⟩ : syracuseStep 2896193 = 2172145) B2172145
theorem B1930795 : Blo 1929435 1930795 := bstep (se 1 (by rfl) ⟨1448096, by rfl⟩ : syracuseStep 1930795 = 2896193) B2896193
theorem B3479365 : Blo 1929435 3479365 := bbase (se 4 (by rfl) ⟨326190, by rfl⟩ : syracuseStep 3479365 = 652381) (by norm_num)
theorem B18556613 : Blo 1929435 18556613 := bstep (se 4 (by rfl) ⟨1739682, by rfl⟩ : syracuseStep 18556613 = 3479365) B3479365
theorem B12371075 : Blo 1929435 12371075 := bstep (se 1 (by rfl) ⟨9278306, by rfl⟩ : syracuseStep 12371075 = 18556613) B18556613
theorem B8247383 : Blo 1929435 8247383 := bstep (se 1 (by rfl) ⟨6185537, by rfl⟩ : syracuseStep 8247383 = 12371075) B12371075
theorem B5498255 : Blo 1929435 5498255 := bstep (se 1 (by rfl) ⟨4123691, by rfl⟩ : syracuseStep 5498255 = 8247383) B8247383
theorem B3665503 : Blo 1929435 3665503 := bstep (se 1 (by rfl) ⟨2749127, by rfl⟩ : syracuseStep 3665503 = 5498255) B5498255
theorem B4887337 : Blo 1929435 4887337 := bstep (se 2 (by rfl) ⟨1832751, by rfl⟩ : syracuseStep 4887337 = 3665503) B3665503
theorem B6516449 : Blo 1929435 6516449 := bstep (se 2 (by rfl) ⟨2443668, by rfl⟩ : syracuseStep 6516449 = 4887337) B4887337
theorem B4344299 : Blo 1929435 4344299 := bstep (se 1 (by rfl) ⟨3258224, by rfl⟩ : syracuseStep 4344299 = 6516449) B6516449
theorem B2896199 : Blo 1929435 2896199 := bstep (se 1 (by rfl) ⟨2172149, by rfl⟩ : syracuseStep 2896199 = 4344299) B4344299
theorem B1930799 : Blo 1929435 1930799 := bstep (se 1 (by rfl) ⟨1448099, by rfl⟩ : syracuseStep 1930799 = 2896199) B2896199
theorem B2896205 : Blo 1929435 2896205 := bbase (se 3 (by rfl) ⟨543038, by rfl⟩ : syracuseStep 2896205 = 1086077) (by norm_num)
theorem B1930803 : Blo 1929435 1930803 := bstep (se 1 (by rfl) ⟨1448102, by rfl⟩ : syracuseStep 1930803 = 2896205) B2896205
theorem B4344317 : Blo 1929435 4344317 := bbase (se 3 (by rfl) ⟨814559, by rfl⟩ : syracuseStep 4344317 = 1629119) (by norm_num)
theorem B2896211 : Blo 1929435 2896211 := bstep (se 1 (by rfl) ⟨2172158, by rfl⟩ : syracuseStep 2896211 = 4344317) B4344317
theorem B1930807 : Blo 1929435 1930807 := bstep (se 1 (by rfl) ⟨1448105, by rfl⟩ : syracuseStep 1930807 = 2896211) B2896211
theorem B3258245 : Blo 1929435 3258245 := bbase (se 4 (by rfl) ⟨305460, by rfl⟩ : syracuseStep 3258245 = 610921) (by norm_num)
theorem B2172163 : Blo 1929435 2172163 := bstep (se 1 (by rfl) ⟨1629122, by rfl⟩ : syracuseStep 2172163 = 3258245) B3258245
theorem B2896217 : Blo 1929435 2896217 := bstep (se 2 (by rfl) ⟨1086081, by rfl⟩ : syracuseStep 2896217 = 2172163) B2172163
theorem B1930811 : Blo 1929435 1930811 := bstep (se 1 (by rfl) ⟨1448108, by rfl⟩ : syracuseStep 1930811 = 2896217) B2896217
theorem B14662133 : Blo 1929435 14662133 := bbase (se 5 (by rfl) ⟨687287, by rfl⟩ : syracuseStep 14662133 = 1374575) (by norm_num)
theorem B9774755 : Blo 1929435 9774755 := bstep (se 1 (by rfl) ⟨7331066, by rfl⟩ : syracuseStep 9774755 = 14662133) B14662133
theorem B6516503 : Blo 1929435 6516503 := bstep (se 1 (by rfl) ⟨4887377, by rfl⟩ : syracuseStep 6516503 = 9774755) B9774755
theorem B4344335 : Blo 1929435 4344335 := bstep (se 1 (by rfl) ⟨3258251, by rfl⟩ : syracuseStep 4344335 = 6516503) B6516503
theorem B2896223 : Blo 1929435 2896223 := bstep (se 1 (by rfl) ⟨2172167, by rfl⟩ : syracuseStep 2896223 = 4344335) B4344335
theorem B1930815 : Blo 1929435 1930815 := bstep (se 1 (by rfl) ⟨1448111, by rfl⟩ : syracuseStep 1930815 = 2896223) B2896223
theorem B2896229 : Blo 1929435 2896229 := bbase (se 4 (by rfl) ⟨271521, by rfl⟩ : syracuseStep 2896229 = 543043) (by norm_num)
theorem B1930819 : Blo 1929435 1930819 := bstep (se 1 (by rfl) ⟨1448114, by rfl⟩ : syracuseStep 1930819 = 2896229) B2896229
theorem B3665549 : Blo 1929435 3665549 := bbase (se 3 (by rfl) ⟨687290, by rfl⟩ : syracuseStep 3665549 = 1374581) (by norm_num)
theorem B2443699 : Blo 1929435 2443699 := bstep (se 1 (by rfl) ⟨1832774, by rfl⟩ : syracuseStep 2443699 = 3665549) B3665549
theorem B3258265 : Blo 1929435 3258265 := bstep (se 2 (by rfl) ⟨1221849, by rfl⟩ : syracuseStep 3258265 = 2443699) B2443699
theorem B4344353 : Blo 1929435 4344353 := bstep (se 2 (by rfl) ⟨1629132, by rfl⟩ : syracuseStep 4344353 = 3258265) B3258265
theorem B2896235 : Blo 1929435 2896235 := bstep (se 1 (by rfl) ⟨2172176, by rfl⟩ : syracuseStep 2896235 = 4344353) B4344353
theorem B1930823 : Blo 1929435 1930823 := bstep (se 1 (by rfl) ⟨1448117, by rfl⟩ : syracuseStep 1930823 = 2896235) B2896235
theorem B2172181 : Blo 1929435 2172181 := bbase (se 6 (by rfl) ⟨50910, by rfl⟩ : syracuseStep 2172181 = 101821) (by norm_num)
theorem B2896241 : Blo 1929435 2896241 := bstep (se 2 (by rfl) ⟨1086090, by rfl⟩ : syracuseStep 2896241 = 2172181) B2172181
theorem B1930827 : Blo 1929435 1930827 := bstep (se 1 (by rfl) ⟨1448120, by rfl⟩ : syracuseStep 1930827 = 2896241) B2896241
theorem B2443709 : Blo 1929435 2443709 := bbase (se 3 (by rfl) ⟨458195, by rfl⟩ : syracuseStep 2443709 = 916391) (by norm_num)
theorem B6516557 : Blo 1929435 6516557 := bstep (se 3 (by rfl) ⟨1221854, by rfl⟩ : syracuseStep 6516557 = 2443709) B2443709
theorem B4344371 : Blo 1929435 4344371 := bstep (se 1 (by rfl) ⟨3258278, by rfl⟩ : syracuseStep 4344371 = 6516557) B6516557
theorem B2896247 : Blo 1929435 2896247 := bstep (se 1 (by rfl) ⟨2172185, by rfl⟩ : syracuseStep 2896247 = 4344371) B4344371
theorem B1930831 : Blo 1929435 1930831 := bstep (se 1 (by rfl) ⟨1448123, by rfl⟩ : syracuseStep 1930831 = 2896247) B2896247
theorem B2896253 : Blo 1929435 2896253 := bbase (se 3 (by rfl) ⟨543047, by rfl⟩ : syracuseStep 2896253 = 1086095) (by norm_num)
theorem B1930835 : Blo 1929435 1930835 := bstep (se 1 (by rfl) ⟨1448126, by rfl⟩ : syracuseStep 1930835 = 2896253) B2896253
theorem B4344389 : Blo 1929435 4344389 := bbase (se 4 (by rfl) ⟨407286, by rfl⟩ : syracuseStep 4344389 = 814573) (by norm_num)
theorem B2896259 : Blo 1929435 2896259 := bstep (se 1 (by rfl) ⟨2172194, by rfl⟩ : syracuseStep 2896259 = 4344389) B4344389
theorem B1930839 : Blo 1929435 1930839 := bstep (se 1 (by rfl) ⟨1448129, by rfl⟩ : syracuseStep 1930839 = 2896259) B2896259
theorem B2061893 : Blo 1929435 2061893 := bbase (se 4 (by rfl) ⟨193302, by rfl⟩ : syracuseStep 2061893 = 386605) (by norm_num)
theorem B5498381 : Blo 1929435 5498381 := bstep (se 3 (by rfl) ⟨1030946, by rfl⟩ : syracuseStep 5498381 = 2061893) B2061893
theorem B3665587 : Blo 1929435 3665587 := bstep (se 1 (by rfl) ⟨2749190, by rfl⟩ : syracuseStep 3665587 = 5498381) B5498381
theorem B4887449 : Blo 1929435 4887449 := bstep (se 2 (by rfl) ⟨1832793, by rfl⟩ : syracuseStep 4887449 = 3665587) B3665587
theorem B3258299 : Blo 1929435 3258299 := bstep (se 1 (by rfl) ⟨2443724, by rfl⟩ : syracuseStep 3258299 = 4887449) B4887449
theorem B2172199 : Blo 1929435 2172199 := bstep (se 1 (by rfl) ⟨1629149, by rfl⟩ : syracuseStep 2172199 = 3258299) B3258299
theorem B2896265 : Blo 1929435 2896265 := bstep (se 2 (by rfl) ⟨1086099, by rfl⟩ : syracuseStep 2896265 = 2172199) B2172199
theorem B1930843 : Blo 1929435 1930843 := bstep (se 1 (by rfl) ⟨1448132, by rfl⟩ : syracuseStep 1930843 = 2896265) B2896265
theorem B9774917 : Blo 1929435 9774917 := bbase (se 4 (by rfl) ⟨916398, by rfl⟩ : syracuseStep 9774917 = 1832797) (by norm_num)
theorem B6516611 : Blo 1929435 6516611 := bstep (se 1 (by rfl) ⟨4887458, by rfl⟩ : syracuseStep 6516611 = 9774917) B9774917
theorem B4344407 : Blo 1929435 4344407 := bstep (se 1 (by rfl) ⟨3258305, by rfl⟩ : syracuseStep 4344407 = 6516611) B6516611
theorem B2896271 : Blo 1929435 2896271 := bstep (se 1 (by rfl) ⟨2172203, by rfl⟩ : syracuseStep 2896271 = 4344407) B4344407
theorem B1930847 : Blo 1929435 1930847 := bstep (se 1 (by rfl) ⟨1448135, by rfl⟩ : syracuseStep 1930847 = 2896271) B2896271
theorem B2896277 : Blo 1929435 2896277 := bbase (se 6 (by rfl) ⟨67881, by rfl⟩ : syracuseStep 2896277 = 135763) (by norm_num)
theorem B1930851 : Blo 1929435 1930851 := bstep (se 1 (by rfl) ⟨1448138, by rfl⟩ : syracuseStep 1930851 = 2896277) B2896277
theorem B6185717 : Blo 1929435 6185717 := bbase (se 5 (by rfl) ⟨289955, by rfl⟩ : syracuseStep 6185717 = 579911) (by norm_num)
theorem B4123811 : Blo 1929435 4123811 := bstep (se 1 (by rfl) ⟨3092858, by rfl⟩ : syracuseStep 4123811 = 6185717) B6185717
theorem B10996829 : Blo 1929435 10996829 := bstep (se 3 (by rfl) ⟨2061905, by rfl⟩ : syracuseStep 10996829 = 4123811) B4123811
theorem B7331219 : Blo 1929435 7331219 := bstep (se 1 (by rfl) ⟨5498414, by rfl⟩ : syracuseStep 7331219 = 10996829) B10996829
theorem B4887479 : Blo 1929435 4887479 := bstep (se 1 (by rfl) ⟨3665609, by rfl⟩ : syracuseStep 4887479 = 7331219) B7331219
theorem B3258319 : Blo 1929435 3258319 := bstep (se 1 (by rfl) ⟨2443739, by rfl⟩ : syracuseStep 3258319 = 4887479) B4887479
theorem B4344425 : Blo 1929435 4344425 := bstep (se 2 (by rfl) ⟨1629159, by rfl⟩ : syracuseStep 4344425 = 3258319) B3258319
theorem B2896283 : Blo 1929435 2896283 := bstep (se 1 (by rfl) ⟨2172212, by rfl⟩ : syracuseStep 2896283 = 4344425) B4344425
theorem B1930855 : Blo 1929435 1930855 := bstep (se 1 (by rfl) ⟨1448141, by rfl⟩ : syracuseStep 1930855 = 2896283) B2896283
theorem B2172217 : Blo 1929435 2172217 := bbase (se 2 (by rfl) ⟨814581, by rfl⟩ : syracuseStep 2172217 = 1629163) (by norm_num)
theorem B2896289 : Blo 1929435 2896289 := bstep (se 2 (by rfl) ⟨1086108, by rfl⟩ : syracuseStep 2896289 = 2172217) B2172217
theorem B1930859 : Blo 1929435 1930859 := bstep (se 1 (by rfl) ⟨1448144, by rfl⟩ : syracuseStep 1930859 = 2896289) B2896289
theorem B5498437 : Blo 1929435 5498437 := bbase (se 4 (by rfl) ⟨515478, by rfl⟩ : syracuseStep 5498437 = 1030957) (by norm_num)
theorem B7331249 : Blo 1929435 7331249 := bstep (se 2 (by rfl) ⟨2749218, by rfl⟩ : syracuseStep 7331249 = 5498437) B5498437
theorem B4887499 : Blo 1929435 4887499 := bstep (se 1 (by rfl) ⟨3665624, by rfl⟩ : syracuseStep 4887499 = 7331249) B7331249
theorem B6516665 : Blo 1929435 6516665 := bstep (se 2 (by rfl) ⟨2443749, by rfl⟩ : syracuseStep 6516665 = 4887499) B4887499
theorem B4344443 : Blo 1929435 4344443 := bstep (se 1 (by rfl) ⟨3258332, by rfl⟩ : syracuseStep 4344443 = 6516665) B6516665
theorem B2896295 : Blo 1929435 2896295 := bstep (se 1 (by rfl) ⟨2172221, by rfl⟩ : syracuseStep 2896295 = 4344443) B4344443
theorem B1930863 : Blo 1929435 1930863 := bstep (se 1 (by rfl) ⟨1448147, by rfl⟩ : syracuseStep 1930863 = 2896295) B2896295
theorem B2896301 : Blo 1929435 2896301 := bbase (se 3 (by rfl) ⟨543056, by rfl⟩ : syracuseStep 2896301 = 1086113) (by norm_num)
theorem B1930867 : Blo 1929435 1930867 := bstep (se 1 (by rfl) ⟨1448150, by rfl⟩ : syracuseStep 1930867 = 2896301) B2896301
theorem B4344461 : Blo 1929435 4344461 := bbase (se 3 (by rfl) ⟨814586, by rfl⟩ : syracuseStep 4344461 = 1629173) (by norm_num)
theorem B2896307 : Blo 1929435 2896307 := bstep (se 1 (by rfl) ⟨2172230, by rfl⟩ : syracuseStep 2896307 = 4344461) B4344461
theorem B1930871 : Blo 1929435 1930871 := bstep (se 1 (by rfl) ⟨1448153, by rfl⟩ : syracuseStep 1930871 = 2896307) B2896307
theorem B2443765 : Blo 1929435 2443765 := bbase (se 5 (by rfl) ⟨114551, by rfl⟩ : syracuseStep 2443765 = 229103) (by norm_num)
theorem B3258353 : Blo 1929435 3258353 := bstep (se 2 (by rfl) ⟨1221882, by rfl⟩ : syracuseStep 3258353 = 2443765) B2443765
theorem B2172235 : Blo 1929435 2172235 := bstep (se 1 (by rfl) ⟨1629176, by rfl⟩ : syracuseStep 2172235 = 3258353) B3258353
theorem B2896313 : Blo 1929435 2896313 := bstep (se 2 (by rfl) ⟨1086117, by rfl⟩ : syracuseStep 2896313 = 2172235) B2172235
theorem B1930875 : Blo 1929435 1930875 := bstep (se 1 (by rfl) ⟨1448156, by rfl⟩ : syracuseStep 1930875 = 2896313) B2896313
theorem B17414261 : Blo 1929435 17414261 := bbase (se 5 (by rfl) ⟨816293, by rfl⟩ : syracuseStep 17414261 = 1632587) (by norm_num)
theorem B11609507 : Blo 1929435 11609507 := bstep (se 1 (by rfl) ⟨8707130, by rfl⟩ : syracuseStep 11609507 = 17414261) B17414261
theorem B7739671 : Blo 1929435 7739671 := bstep (se 1 (by rfl) ⟨5804753, by rfl⟩ : syracuseStep 7739671 = 11609507) B11609507
theorem B10319561 : Blo 1929435 10319561 := bstep (se 2 (by rfl) ⟨3869835, by rfl⟩ : syracuseStep 10319561 = 7739671) B7739671
theorem B6879707 : Blo 1929435 6879707 := bstep (se 1 (by rfl) ⟨5159780, by rfl⟩ : syracuseStep 6879707 = 10319561) B10319561
theorem B4586471 : Blo 1929435 4586471 := bstep (se 1 (by rfl) ⟨3439853, by rfl⟩ : syracuseStep 4586471 = 6879707) B6879707
theorem B3057647 : Blo 1929435 3057647 := bstep (se 1 (by rfl) ⟨2293235, by rfl⟩ : syracuseStep 3057647 = 4586471) B4586471
theorem B8153725 : Blo 1929435 8153725 := bstep (se 3 (by rfl) ⟨1528823, by rfl⟩ : syracuseStep 8153725 = 3057647) B3057647
theorem B10871633 : Blo 1929435 10871633 := bstep (se 2 (by rfl) ⟨4076862, by rfl⟩ : syracuseStep 10871633 = 8153725) B8153725
theorem B7247755 : Blo 1929435 7247755 := bstep (se 1 (by rfl) ⟨5435816, by rfl⟩ : syracuseStep 7247755 = 10871633) B10871633
theorem B9663673 : Blo 1929435 9663673 := bstep (se 2 (by rfl) ⟨3623877, by rfl⟩ : syracuseStep 9663673 = 7247755) B7247755
theorem B12884897 : Blo 1929435 12884897 := bstep (se 2 (by rfl) ⟨4831836, by rfl⟩ : syracuseStep 12884897 = 9663673) B9663673
theorem B8589931 : Blo 1929435 8589931 := bstep (se 1 (by rfl) ⟨6442448, by rfl⟩ : syracuseStep 8589931 = 12884897) B12884897
theorem B45812965 : Blo 1929435 45812965 := bstep (se 4 (by rfl) ⟨4294965, by rfl⟩ : syracuseStep 45812965 = 8589931) B8589931
theorem B61083953 : Blo 1929435 61083953 := bstep (se 2 (by rfl) ⟨22906482, by rfl⟩ : syracuseStep 61083953 = 45812965) B45812965
theorem B40722635 : Blo 1929435 40722635 := bstep (se 1 (by rfl) ⟨30541976, by rfl⟩ : syracuseStep 40722635 = 61083953) B61083953
theorem B108593693 : Blo 1929435 108593693 := bstep (se 3 (by rfl) ⟨20361317, by rfl⟩ : syracuseStep 108593693 = 40722635) B40722635
theorem B72395795 : Blo 1929435 72395795 := bstep (se 1 (by rfl) ⟨54296846, by rfl⟩ : syracuseStep 72395795 = 108593693) B108593693
theorem B48263863 : Blo 1929435 48263863 := bstep (se 1 (by rfl) ⟨36197897, by rfl⟩ : syracuseStep 48263863 = 72395795) B72395795
theorem B64351817 : Blo 1929435 64351817 := bstep (se 2 (by rfl) ⟨24131931, by rfl⟩ : syracuseStep 64351817 = 48263863) B48263863
theorem B42901211 : Blo 1929435 42901211 := bstep (se 1 (by rfl) ⟨32175908, by rfl⟩ : syracuseStep 42901211 = 64351817) B64351817
theorem B28600807 : Blo 1929435 28600807 := bstep (se 1 (by rfl) ⟨21450605, by rfl⟩ : syracuseStep 28600807 = 42901211) B42901211
theorem B2440602197 : Blo 1929435 2440602197 := bstep (se 8 (by rfl) ⟨14300403, by rfl⟩ : syracuseStep 2440602197 = 28600807) B28600807
theorem B1627068131 : Blo 1929435 1627068131 := bstep (se 1 (by rfl) ⟨1220301098, by rfl⟩ : syracuseStep 1627068131 = 2440602197) B2440602197
theorem B1084712087 : Blo 1929435 1084712087 := bstep (se 1 (by rfl) ⟨813534065, by rfl⟩ : syracuseStep 1084712087 = 1627068131) B1627068131
theorem B723141391 : Blo 1929435 723141391 := bstep (se 1 (by rfl) ⟨542356043, by rfl⟩ : syracuseStep 723141391 = 1084712087) B1084712087
theorem B964188521 : Blo 1929435 964188521 := bstep (se 2 (by rfl) ⟨361570695, by rfl⟩ : syracuseStep 964188521 = 723141391) B723141391
theorem B642792347 : Blo 1929435 642792347 := bstep (se 1 (by rfl) ⟨482094260, by rfl⟩ : syracuseStep 642792347 = 964188521) B964188521
theorem B428528231 : Blo 1929435 428528231 := bstep (se 1 (by rfl) ⟨321396173, by rfl⟩ : syracuseStep 428528231 = 642792347) B642792347
theorem B285685487 : Blo 1929435 285685487 := bstep (se 1 (by rfl) ⟨214264115, by rfl⟩ : syracuseStep 285685487 = 428528231) B428528231
theorem B190456991 : Blo 1929435 190456991 := bstep (se 1 (by rfl) ⟨142842743, by rfl⟩ : syracuseStep 190456991 = 285685487) B285685487
theorem B126971327 : Blo 1929435 126971327 := bstep (se 1 (by rfl) ⟨95228495, by rfl⟩ : syracuseStep 126971327 = 190456991) B190456991
theorem B84647551 : Blo 1929435 84647551 := bstep (se 1 (by rfl) ⟨63485663, by rfl⟩ : syracuseStep 84647551 = 126971327) B126971327
theorem B112863401 : Blo 1929435 112863401 := bstep (se 2 (by rfl) ⟨42323775, by rfl⟩ : syracuseStep 112863401 = 84647551) B84647551
theorem B75242267 : Blo 1929435 75242267 := bstep (se 1 (by rfl) ⟨56431700, by rfl⟩ : syracuseStep 75242267 = 112863401) B112863401
theorem B50161511 : Blo 1929435 50161511 := bstep (se 1 (by rfl) ⟨37621133, by rfl⟩ : syracuseStep 50161511 = 75242267) B75242267
theorem B33441007 : Blo 1929435 33441007 := bstep (se 1 (by rfl) ⟨25080755, by rfl⟩ : syracuseStep 33441007 = 50161511) B50161511
theorem B44588009 : Blo 1929435 44588009 := bstep (se 2 (by rfl) ⟨16720503, by rfl⟩ : syracuseStep 44588009 = 33441007) B33441007
theorem B29725339 : Blo 1929435 29725339 := bstep (se 1 (by rfl) ⟨22294004, by rfl⟩ : syracuseStep 29725339 = 44588009) B44588009
theorem B39633785 : Blo 1929435 39633785 := bstep (se 2 (by rfl) ⟨14862669, by rfl⟩ : syracuseStep 39633785 = 29725339) B29725339
theorem B26422523 : Blo 1929435 26422523 := bstep (se 1 (by rfl) ⟨19816892, by rfl⟩ : syracuseStep 26422523 = 39633785) B39633785
theorem B17615015 : Blo 1929435 17615015 := bstep (se 1 (by rfl) ⟨13211261, by rfl⟩ : syracuseStep 17615015 = 26422523) B26422523
theorem B11743343 : Blo 1929435 11743343 := bstep (se 1 (by rfl) ⟨8807507, by rfl⟩ : syracuseStep 11743343 = 17615015) B17615015
theorem B7828895 : Blo 1929435 7828895 := bstep (se 1 (by rfl) ⟨5871671, by rfl⟩ : syracuseStep 7828895 = 11743343) B11743343
theorem B5219263 : Blo 1929435 5219263 := bstep (se 1 (by rfl) ⟨3914447, by rfl⟩ : syracuseStep 5219263 = 7828895) B7828895
theorem B6959017 : Blo 1929435 6959017 := bstep (se 2 (by rfl) ⟨2609631, by rfl⟩ : syracuseStep 6959017 = 5219263) B5219263
theorem B37114757 : Blo 1929435 37114757 := bstep (se 4 (by rfl) ⟨3479508, by rfl⟩ : syracuseStep 37114757 = 6959017) B6959017
theorem B24743171 : Blo 1929435 24743171 := bstep (se 1 (by rfl) ⟨18557378, by rfl⟩ : syracuseStep 24743171 = 37114757) B37114757
theorem B16495447 : Blo 1929435 16495447 := bstep (se 1 (by rfl) ⟨12371585, by rfl⟩ : syracuseStep 16495447 = 24743171) B24743171
theorem B21993929 : Blo 1929435 21993929 := bstep (se 2 (by rfl) ⟨8247723, by rfl⟩ : syracuseStep 21993929 = 16495447) B16495447
theorem B14662619 : Blo 1929435 14662619 := bstep (se 1 (by rfl) ⟨10996964, by rfl⟩ : syracuseStep 14662619 = 21993929) B21993929
theorem B9775079 : Blo 1929435 9775079 := bstep (se 1 (by rfl) ⟨7331309, by rfl⟩ : syracuseStep 9775079 = 14662619) B14662619
theorem B6516719 : Blo 1929435 6516719 := bstep (se 1 (by rfl) ⟨4887539, by rfl⟩ : syracuseStep 6516719 = 9775079) B9775079
theorem B4344479 : Blo 1929435 4344479 := bstep (se 1 (by rfl) ⟨3258359, by rfl⟩ : syracuseStep 4344479 = 6516719) B6516719
theorem B2896319 : Blo 1929435 2896319 := bstep (se 1 (by rfl) ⟨2172239, by rfl⟩ : syracuseStep 2896319 = 4344479) B4344479
theorem B1930879 : Blo 1929435 1930879 := bstep (se 1 (by rfl) ⟨1448159, by rfl⟩ : syracuseStep 1930879 = 2896319) B2896319
theorem B2896325 : Blo 1929435 2896325 := bbase (se 4 (by rfl) ⟨271530, by rfl⟩ : syracuseStep 2896325 = 543061) (by norm_num)
theorem B1930883 : Blo 1929435 1930883 := bstep (se 1 (by rfl) ⟨1448162, by rfl⟩ : syracuseStep 1930883 = 2896325) B2896325
theorem B3258373 : Blo 1929435 3258373 := bbase (se 4 (by rfl) ⟨305472, by rfl⟩ : syracuseStep 3258373 = 610945) (by norm_num)
theorem B4344497 : Blo 1929435 4344497 := bstep (se 2 (by rfl) ⟨1629186, by rfl⟩ : syracuseStep 4344497 = 3258373) B3258373
theorem B2896331 : Blo 1929435 2896331 := bstep (se 1 (by rfl) ⟨2172248, by rfl⟩ : syracuseStep 2896331 = 4344497) B4344497
theorem B1930887 : Blo 1929435 1930887 := bstep (se 1 (by rfl) ⟨1448165, by rfl⟩ : syracuseStep 1930887 = 2896331) B2896331
theorem B2172253 : Blo 1929435 2172253 := bbase (se 3 (by rfl) ⟨407297, by rfl⟩ : syracuseStep 2172253 = 814595) (by norm_num)
theorem B2896337 : Blo 1929435 2896337 := bstep (se 2 (by rfl) ⟨1086126, by rfl⟩ : syracuseStep 2896337 = 2172253) B2172253
theorem B1930891 : Blo 1929435 1930891 := bstep (se 1 (by rfl) ⟨1448168, by rfl⟩ : syracuseStep 1930891 = 2896337) B2896337
theorem B6516773 : Blo 1929435 6516773 := bbase (se 4 (by rfl) ⟨610947, by rfl⟩ : syracuseStep 6516773 = 1221895) (by norm_num)
theorem B4344515 : Blo 1929435 4344515 := bstep (se 1 (by rfl) ⟨3258386, by rfl⟩ : syracuseStep 4344515 = 6516773) B6516773
theorem B2896343 : Blo 1929435 2896343 := bstep (se 1 (by rfl) ⟨2172257, by rfl⟩ : syracuseStep 2896343 = 4344515) B4344515
theorem B1930895 : Blo 1929435 1930895 := bstep (se 1 (by rfl) ⟨1448171, by rfl⟩ : syracuseStep 1930895 = 2896343) B2896343
theorem B2896349 : Blo 1929435 2896349 := bbase (se 3 (by rfl) ⟨543065, by rfl⟩ : syracuseStep 2896349 = 1086131) (by norm_num)
theorem B1930899 : Blo 1929435 1930899 := bstep (se 1 (by rfl) ⟨1448174, by rfl⟩ : syracuseStep 1930899 = 2896349) B2896349
theorem B4344533 : Blo 1929435 4344533 := bbase (se 7 (by rfl) ⟨50912, by rfl⟩ : syracuseStep 4344533 = 101825) (by norm_num)
theorem B2896355 : Blo 1929435 2896355 := bstep (se 1 (by rfl) ⟨2172266, by rfl⟩ : syracuseStep 2896355 = 4344533) B4344533
theorem B1930903 : Blo 1929435 1930903 := bstep (se 1 (by rfl) ⟨1448177, by rfl⟩ : syracuseStep 1930903 = 2896355) B2896355
theorem B8247845 : Blo 1929435 8247845 := bbase (se 4 (by rfl) ⟨773235, by rfl⟩ : syracuseStep 8247845 = 1546471) (by norm_num)
theorem B5498563 : Blo 1929435 5498563 := bstep (se 1 (by rfl) ⟨4123922, by rfl⟩ : syracuseStep 5498563 = 8247845) B8247845
theorem B7331417 : Blo 1929435 7331417 := bstep (se 2 (by rfl) ⟨2749281, by rfl⟩ : syracuseStep 7331417 = 5498563) B5498563
theorem B4887611 : Blo 1929435 4887611 := bstep (se 1 (by rfl) ⟨3665708, by rfl⟩ : syracuseStep 4887611 = 7331417) B7331417
theorem B3258407 : Blo 1929435 3258407 := bstep (se 1 (by rfl) ⟨2443805, by rfl⟩ : syracuseStep 3258407 = 4887611) B4887611
theorem B2172271 : Blo 1929435 2172271 := bstep (se 1 (by rfl) ⟨1629203, by rfl⟩ : syracuseStep 2172271 = 3258407) B3258407
theorem B2896361 : Blo 1929435 2896361 := bstep (se 2 (by rfl) ⟨1086135, by rfl⟩ : syracuseStep 2896361 = 2172271) B2172271
theorem B1930907 : Blo 1929435 1930907 := bstep (se 1 (by rfl) ⟨1448180, by rfl⟩ : syracuseStep 1930907 = 2896361) B2896361
theorem B8807653 : Blo 1929435 8807653 := bbase (se 4 (by rfl) ⟨825717, by rfl⟩ : syracuseStep 8807653 = 1651435) (by norm_num)
theorem B11743537 : Blo 1929435 11743537 := bstep (se 2 (by rfl) ⟨4403826, by rfl⟩ : syracuseStep 11743537 = 8807653) B8807653
theorem B15658049 : Blo 1929435 15658049 := bstep (se 2 (by rfl) ⟨5871768, by rfl⟩ : syracuseStep 15658049 = 11743537) B11743537
theorem B41754797 : Blo 1929435 41754797 := bstep (se 3 (by rfl) ⟨7829024, by rfl⟩ : syracuseStep 41754797 = 15658049) B15658049
theorem B27836531 : Blo 1929435 27836531 := bstep (se 1 (by rfl) ⟨20877398, by rfl⟩ : syracuseStep 27836531 = 41754797) B41754797
theorem B18557687 : Blo 1929435 18557687 := bstep (se 1 (by rfl) ⟨13918265, by rfl⟩ : syracuseStep 18557687 = 27836531) B27836531
theorem B12371791 : Blo 1929435 12371791 := bstep (se 1 (by rfl) ⟨9278843, by rfl⟩ : syracuseStep 12371791 = 18557687) B18557687
theorem B16495721 : Blo 1929435 16495721 := bstep (se 2 (by rfl) ⟨6185895, by rfl⟩ : syracuseStep 16495721 = 12371791) B12371791
theorem B10997147 : Blo 1929435 10997147 := bstep (se 1 (by rfl) ⟨8247860, by rfl⟩ : syracuseStep 10997147 = 16495721) B16495721
theorem B7331431 : Blo 1929435 7331431 := bstep (se 1 (by rfl) ⟨5498573, by rfl⟩ : syracuseStep 7331431 = 10997147) B10997147
theorem B9775241 : Blo 1929435 9775241 := bstep (se 2 (by rfl) ⟨3665715, by rfl⟩ : syracuseStep 9775241 = 7331431) B7331431
theorem B6516827 : Blo 1929435 6516827 := bstep (se 1 (by rfl) ⟨4887620, by rfl⟩ : syracuseStep 6516827 = 9775241) B9775241
theorem B4344551 : Blo 1929435 4344551 := bstep (se 1 (by rfl) ⟨3258413, by rfl⟩ : syracuseStep 4344551 = 6516827) B6516827
theorem B2896367 : Blo 1929435 2896367 := bstep (se 1 (by rfl) ⟨2172275, by rfl⟩ : syracuseStep 2896367 = 4344551) B4344551
theorem B1930911 : Blo 1929435 1930911 := bstep (se 1 (by rfl) ⟨1448183, by rfl⟩ : syracuseStep 1930911 = 2896367) B2896367
theorem B2896373 : Blo 1929435 2896373 := bbase (se 5 (by rfl) ⟨135767, by rfl⟩ : syracuseStep 2896373 = 271535) (by norm_num)
theorem B1930915 : Blo 1929435 1930915 := bstep (se 1 (by rfl) ⟨1448186, by rfl⟩ : syracuseStep 1930915 = 2896373) B2896373
theorem B5498597 : Blo 1929435 5498597 := bbase (se 4 (by rfl) ⟨515493, by rfl⟩ : syracuseStep 5498597 = 1030987) (by norm_num)
theorem B3665731 : Blo 1929435 3665731 := bstep (se 1 (by rfl) ⟨2749298, by rfl⟩ : syracuseStep 3665731 = 5498597) B5498597
theorem B4887641 : Blo 1929435 4887641 := bstep (se 2 (by rfl) ⟨1832865, by rfl⟩ : syracuseStep 4887641 = 3665731) B3665731
theorem B3258427 : Blo 1929435 3258427 := bstep (se 1 (by rfl) ⟨2443820, by rfl⟩ : syracuseStep 3258427 = 4887641) B4887641
theorem B4344569 : Blo 1929435 4344569 := bstep (se 2 (by rfl) ⟨1629213, by rfl⟩ : syracuseStep 4344569 = 3258427) B3258427
theorem B2896379 : Blo 1929435 2896379 := bstep (se 1 (by rfl) ⟨2172284, by rfl⟩ : syracuseStep 2896379 = 4344569) B4344569
theorem B1930919 : Blo 1929435 1930919 := bstep (se 1 (by rfl) ⟨1448189, by rfl⟩ : syracuseStep 1930919 = 2896379) B2896379
theorem B2172289 : Blo 1929435 2172289 := bbase (se 2 (by rfl) ⟨814608, by rfl⟩ : syracuseStep 2172289 = 1629217) (by norm_num)
theorem B2896385 : Blo 1929435 2896385 := bstep (se 2 (by rfl) ⟨1086144, by rfl⟩ : syracuseStep 2896385 = 2172289) B2172289
theorem B1930923 : Blo 1929435 1930923 := bstep (se 1 (by rfl) ⟨1448192, by rfl⟩ : syracuseStep 1930923 = 2896385) B2896385
theorem B4887661 : Blo 1929435 4887661 := bbase (se 3 (by rfl) ⟨916436, by rfl⟩ : syracuseStep 4887661 = 1832873) (by norm_num)
theorem B6516881 : Blo 1929435 6516881 := bstep (se 2 (by rfl) ⟨2443830, by rfl⟩ : syracuseStep 6516881 = 4887661) B4887661
theorem B4344587 : Blo 1929435 4344587 := bstep (se 1 (by rfl) ⟨3258440, by rfl⟩ : syracuseStep 4344587 = 6516881) B6516881
theorem B2896391 : Blo 1929435 2896391 := bstep (se 1 (by rfl) ⟨2172293, by rfl⟩ : syracuseStep 2896391 = 4344587) B4344587
theorem B1930927 : Blo 1929435 1930927 := bstep (se 1 (by rfl) ⟨1448195, by rfl⟩ : syracuseStep 1930927 = 2896391) B2896391
theorem B2896397 : Blo 1929435 2896397 := bbase (se 3 (by rfl) ⟨543074, by rfl⟩ : syracuseStep 2896397 = 1086149) (by norm_num)
theorem B1930931 : Blo 1929435 1930931 := bstep (se 1 (by rfl) ⟨1448198, by rfl⟩ : syracuseStep 1930931 = 2896397) B2896397
theorem B4344605 : Blo 1929435 4344605 := bbase (se 3 (by rfl) ⟨814613, by rfl⟩ : syracuseStep 4344605 = 1629227) (by norm_num)
theorem B2896403 : Blo 1929435 2896403 := bstep (se 1 (by rfl) ⟨2172302, by rfl⟩ : syracuseStep 2896403 = 4344605) B4344605
theorem B1930935 : Blo 1929435 1930935 := bstep (se 1 (by rfl) ⟨1448201, by rfl⟩ : syracuseStep 1930935 = 2896403) B2896403
theorem B3258461 : Blo 1929435 3258461 := bbase (se 3 (by rfl) ⟨610961, by rfl⟩ : syracuseStep 3258461 = 1221923) (by norm_num)
theorem B2172307 : Blo 1929435 2172307 := bstep (se 1 (by rfl) ⟨1629230, by rfl⟩ : syracuseStep 2172307 = 3258461) B3258461
theorem B2896409 : Blo 1929435 2896409 := bstep (se 2 (by rfl) ⟨1086153, by rfl⟩ : syracuseStep 2896409 = 2172307) B2172307
theorem B1930939 : Blo 1929435 1930939 := bstep (se 1 (by rfl) ⟨1448204, by rfl⟩ : syracuseStep 1930939 = 2896409) B2896409
theorem B1957289 : Blo 1929435 1957289 := bbase (se 2 (by rfl) ⟨733983, by rfl⟩ : syracuseStep 1957289 = 1467967) (by norm_num)
theorem B5219437 : Blo 1929435 5219437 := bstep (se 3 (by rfl) ⟨978644, by rfl⟩ : syracuseStep 5219437 = 1957289) B1957289
theorem B6959249 : Blo 1929435 6959249 := bstep (se 2 (by rfl) ⟨2609718, by rfl⟩ : syracuseStep 6959249 = 5219437) B5219437
theorem B4639499 : Blo 1929435 4639499 := bstep (se 1 (by rfl) ⟨3479624, by rfl⟩ : syracuseStep 4639499 = 6959249) B6959249
theorem B3092999 : Blo 1929435 3092999 := bstep (se 1 (by rfl) ⟨2319749, by rfl⟩ : syracuseStep 3092999 = 4639499) B4639499
theorem B8247997 : Blo 1929435 8247997 := bstep (se 3 (by rfl) ⟨1546499, by rfl⟩ : syracuseStep 8247997 = 3092999) B3092999
theorem B10997329 : Blo 1929435 10997329 := bstep (se 2 (by rfl) ⟨4123998, by rfl⟩ : syracuseStep 10997329 = 8247997) B8247997
theorem B14663105 : Blo 1929435 14663105 := bstep (se 2 (by rfl) ⟨5498664, by rfl⟩ : syracuseStep 14663105 = 10997329) B10997329
theorem B9775403 : Blo 1929435 9775403 := bstep (se 1 (by rfl) ⟨7331552, by rfl⟩ : syracuseStep 9775403 = 14663105) B14663105
theorem B6516935 : Blo 1929435 6516935 := bstep (se 1 (by rfl) ⟨4887701, by rfl⟩ : syracuseStep 6516935 = 9775403) B9775403
theorem B4344623 : Blo 1929435 4344623 := bstep (se 1 (by rfl) ⟨3258467, by rfl⟩ : syracuseStep 4344623 = 6516935) B6516935
theorem B2896415 : Blo 1929435 2896415 := bstep (se 1 (by rfl) ⟨2172311, by rfl⟩ : syracuseStep 2896415 = 4344623) B4344623
theorem B1930943 : Blo 1929435 1930943 := bstep (se 1 (by rfl) ⟨1448207, by rfl⟩ : syracuseStep 1930943 = 2896415) B2896415
theorem B2896421 : Blo 1929435 2896421 := bbase (se 4 (by rfl) ⟨271539, by rfl⟩ : syracuseStep 2896421 = 543079) (by norm_num)
theorem B1930947 : Blo 1929435 1930947 := bstep (se 1 (by rfl) ⟨1448210, by rfl⟩ : syracuseStep 1930947 = 2896421) B2896421
theorem B2443861 : Blo 1929435 2443861 := bbase (se 8 (by rfl) ⟨14319, by rfl⟩ : syracuseStep 2443861 = 28639) (by norm_num)
theorem B3258481 : Blo 1929435 3258481 := bstep (se 2 (by rfl) ⟨1221930, by rfl⟩ : syracuseStep 3258481 = 2443861) B2443861
theorem B4344641 : Blo 1929435 4344641 := bstep (se 2 (by rfl) ⟨1629240, by rfl⟩ : syracuseStep 4344641 = 3258481) B3258481
theorem B2896427 : Blo 1929435 2896427 := bstep (se 1 (by rfl) ⟨2172320, by rfl⟩ : syracuseStep 2896427 = 4344641) B4344641
theorem B1930951 : Blo 1929435 1930951 := bstep (se 1 (by rfl) ⟨1448213, by rfl⟩ : syracuseStep 1930951 = 2896427) B2896427
theorem B2172325 : Blo 1929435 2172325 := bbase (se 4 (by rfl) ⟨203655, by rfl⟩ : syracuseStep 2172325 = 407311) (by norm_num)
theorem B2896433 : Blo 1929435 2896433 := bstep (se 2 (by rfl) ⟨1086162, by rfl⟩ : syracuseStep 2896433 = 2172325) B2172325
theorem B1930955 : Blo 1929435 1930955 := bstep (se 1 (by rfl) ⟨1448216, by rfl⟩ : syracuseStep 1930955 = 2896433) B2896433
theorem B2319769 : Blo 1929435 2319769 := bbase (se 2 (by rfl) ⟨869913, by rfl⟩ : syracuseStep 2319769 = 1739827) (by norm_num)
theorem B12372101 : Blo 1929435 12372101 := bstep (se 4 (by rfl) ⟨1159884, by rfl⟩ : syracuseStep 12372101 = 2319769) B2319769
theorem B8248067 : Blo 1929435 8248067 := bstep (se 1 (by rfl) ⟨6186050, by rfl⟩ : syracuseStep 8248067 = 12372101) B12372101
theorem B5498711 : Blo 1929435 5498711 := bstep (se 1 (by rfl) ⟨4124033, by rfl⟩ : syracuseStep 5498711 = 8248067) B8248067
theorem B3665807 : Blo 1929435 3665807 := bstep (se 1 (by rfl) ⟨2749355, by rfl⟩ : syracuseStep 3665807 = 5498711) B5498711
theorem B2443871 : Blo 1929435 2443871 := bstep (se 1 (by rfl) ⟨1832903, by rfl⟩ : syracuseStep 2443871 = 3665807) B3665807
theorem B6516989 : Blo 1929435 6516989 := bstep (se 3 (by rfl) ⟨1221935, by rfl⟩ : syracuseStep 6516989 = 2443871) B2443871
theorem B4344659 : Blo 1929435 4344659 := bstep (se 1 (by rfl) ⟨3258494, by rfl⟩ : syracuseStep 4344659 = 6516989) B6516989
theorem B2896439 : Blo 1929435 2896439 := bstep (se 1 (by rfl) ⟨2172329, by rfl⟩ : syracuseStep 2896439 = 4344659) B4344659
theorem B1930959 : Blo 1929435 1930959 := bstep (se 1 (by rfl) ⟨1448219, by rfl⟩ : syracuseStep 1930959 = 2896439) B2896439
theorem B2896445 : Blo 1929435 2896445 := bbase (se 3 (by rfl) ⟨543083, by rfl⟩ : syracuseStep 2896445 = 1086167) (by norm_num)
theorem B1930963 : Blo 1929435 1930963 := bstep (se 1 (by rfl) ⟨1448222, by rfl⟩ : syracuseStep 1930963 = 2896445) B2896445
theorem B4344677 : Blo 1929435 4344677 := bbase (se 4 (by rfl) ⟨407313, by rfl⟩ : syracuseStep 4344677 = 814627) (by norm_num)
theorem B2896451 : Blo 1929435 2896451 := bstep (se 1 (by rfl) ⟨2172338, by rfl⟩ : syracuseStep 2896451 = 4344677) B4344677
theorem B1930967 : Blo 1929435 1930967 := bstep (se 1 (by rfl) ⟨1448225, by rfl⟩ : syracuseStep 1930967 = 2896451) B2896451
theorem B4887773 : Blo 1929435 4887773 := bbase (se 3 (by rfl) ⟨916457, by rfl⟩ : syracuseStep 4887773 = 1832915) (by norm_num)
theorem B3258515 : Blo 1929435 3258515 := bstep (se 1 (by rfl) ⟨2443886, by rfl⟩ : syracuseStep 3258515 = 4887773) B4887773
theorem B2172343 : Blo 1929435 2172343 := bstep (se 1 (by rfl) ⟨1629257, by rfl⟩ : syracuseStep 2172343 = 3258515) B3258515
theorem B2896457 : Blo 1929435 2896457 := bstep (se 2 (by rfl) ⟨1086171, by rfl⟩ : syracuseStep 2896457 = 2172343) B2172343
theorem B1930971 : Blo 1929435 1930971 := bstep (se 1 (by rfl) ⟨1448228, by rfl⟩ : syracuseStep 1930971 = 2896457) B2896457
theorem B3665837 : Blo 1929435 3665837 := bbase (se 3 (by rfl) ⟨687344, by rfl⟩ : syracuseStep 3665837 = 1374689) (by norm_num)
theorem B9775565 : Blo 1929435 9775565 := bstep (se 3 (by rfl) ⟨1832918, by rfl⟩ : syracuseStep 9775565 = 3665837) B3665837
theorem B6517043 : Blo 1929435 6517043 := bstep (se 1 (by rfl) ⟨4887782, by rfl⟩ : syracuseStep 6517043 = 9775565) B9775565
theorem B4344695 : Blo 1929435 4344695 := bstep (se 1 (by rfl) ⟨3258521, by rfl⟩ : syracuseStep 4344695 = 6517043) B6517043
theorem B2896463 : Blo 1929435 2896463 := bstep (se 1 (by rfl) ⟨2172347, by rfl⟩ : syracuseStep 2896463 = 4344695) B4344695
theorem B1930975 : Blo 1929435 1930975 := bstep (se 1 (by rfl) ⟨1448231, by rfl⟩ : syracuseStep 1930975 = 2896463) B2896463
theorem B2896469 : Blo 1929435 2896469 := bbase (se 8 (by rfl) ⟨16971, by rfl⟩ : syracuseStep 2896469 = 33943) (by norm_num)
theorem B1930979 : Blo 1929435 1930979 := bstep (se 1 (by rfl) ⟨1448234, by rfl⟩ : syracuseStep 1930979 = 2896469) B2896469
theorem B5871989 : Blo 1929435 5871989 := bbase (se 5 (by rfl) ⟨275249, by rfl⟩ : syracuseStep 5871989 = 550499) (by norm_num)
theorem B3914659 : Blo 1929435 3914659 := bstep (se 1 (by rfl) ⟨2935994, by rfl⟩ : syracuseStep 3914659 = 5871989) B5871989
theorem B20878181 : Blo 1929435 20878181 := bstep (se 4 (by rfl) ⟨1957329, by rfl⟩ : syracuseStep 20878181 = 3914659) B3914659
theorem B13918787 : Blo 1929435 13918787 := bstep (se 1 (by rfl) ⟨10439090, by rfl⟩ : syracuseStep 13918787 = 20878181) B20878181
theorem B9279191 : Blo 1929435 9279191 := bstep (se 1 (by rfl) ⟨6959393, by rfl⟩ : syracuseStep 9279191 = 13918787) B13918787
theorem B6186127 : Blo 1929435 6186127 := bstep (se 1 (by rfl) ⟨4639595, by rfl⟩ : syracuseStep 6186127 = 9279191) B9279191
theorem B8248169 : Blo 1929435 8248169 := bstep (se 2 (by rfl) ⟨3093063, by rfl⟩ : syracuseStep 8248169 = 6186127) B6186127
theorem B5498779 : Blo 1929435 5498779 := bstep (se 1 (by rfl) ⟨4124084, by rfl⟩ : syracuseStep 5498779 = 8248169) B8248169
theorem B7331705 : Blo 1929435 7331705 := bstep (se 2 (by rfl) ⟨2749389, by rfl⟩ : syracuseStep 7331705 = 5498779) B5498779
theorem B4887803 : Blo 1929435 4887803 := bstep (se 1 (by rfl) ⟨3665852, by rfl⟩ : syracuseStep 4887803 = 7331705) B7331705
theorem B3258535 : Blo 1929435 3258535 := bstep (se 1 (by rfl) ⟨2443901, by rfl⟩ : syracuseStep 3258535 = 4887803) B4887803
theorem B4344713 : Blo 1929435 4344713 := bstep (se 2 (by rfl) ⟨1629267, by rfl⟩ : syracuseStep 4344713 = 3258535) B3258535
theorem B2896475 : Blo 1929435 2896475 := bstep (se 1 (by rfl) ⟨2172356, by rfl⟩ : syracuseStep 2896475 = 4344713) B4344713
theorem B1930983 : Blo 1929435 1930983 := bstep (se 1 (by rfl) ⟨1448237, by rfl⟩ : syracuseStep 1930983 = 2896475) B2896475
theorem B2172361 : Blo 1929435 2172361 := bbase (se 2 (by rfl) ⟨814635, by rfl⟩ : syracuseStep 2172361 = 1629271) (by norm_num)
theorem B2896481 : Blo 1929435 2896481 := bstep (se 2 (by rfl) ⟨1086180, by rfl⟩ : syracuseStep 2896481 = 2172361) B2172361
theorem B1930987 : Blo 1929435 1930987 := bstep (se 1 (by rfl) ⟨1448240, by rfl⟩ : syracuseStep 1930987 = 2896481) B2896481
theorem B16496405 : Blo 1929435 16496405 := bbase (se 6 (by rfl) ⟨386634, by rfl⟩ : syracuseStep 16496405 = 773269) (by norm_num)
theorem B10997603 : Blo 1929435 10997603 := bstep (se 1 (by rfl) ⟨8248202, by rfl⟩ : syracuseStep 10997603 = 16496405) B16496405
theorem B7331735 : Blo 1929435 7331735 := bstep (se 1 (by rfl) ⟨5498801, by rfl⟩ : syracuseStep 7331735 = 10997603) B10997603
theorem B4887823 : Blo 1929435 4887823 := bstep (se 1 (by rfl) ⟨3665867, by rfl⟩ : syracuseStep 4887823 = 7331735) B7331735
theorem B6517097 : Blo 1929435 6517097 := bstep (se 2 (by rfl) ⟨2443911, by rfl⟩ : syracuseStep 6517097 = 4887823) B4887823
theorem B4344731 : Blo 1929435 4344731 := bstep (se 1 (by rfl) ⟨3258548, by rfl⟩ : syracuseStep 4344731 = 6517097) B6517097
theorem B2896487 : Blo 1929435 2896487 := bstep (se 1 (by rfl) ⟨2172365, by rfl⟩ : syracuseStep 2896487 = 4344731) B4344731
theorem B1930991 : Blo 1929435 1930991 := bstep (se 1 (by rfl) ⟨1448243, by rfl⟩ : syracuseStep 1930991 = 2896487) B2896487
theorem B2896493 : Blo 1929435 2896493 := bbase (se 3 (by rfl) ⟨543092, by rfl⟩ : syracuseStep 2896493 = 1086185) (by norm_num)
theorem B1930995 : Blo 1929435 1930995 := bstep (se 1 (by rfl) ⟨1448246, by rfl⟩ : syracuseStep 1930995 = 2896493) B2896493
theorem B4344749 : Blo 1929435 4344749 := bbase (se 3 (by rfl) ⟨814640, by rfl⟩ : syracuseStep 4344749 = 1629281) (by norm_num)
theorem B2896499 : Blo 1929435 2896499 := bstep (se 1 (by rfl) ⟨2172374, by rfl⟩ : syracuseStep 2896499 = 4344749) B4344749
theorem B1930999 : Blo 1929435 1930999 := bstep (se 1 (by rfl) ⟨1448249, by rfl⟩ : syracuseStep 1930999 = 2896499) B2896499
theorem B5498837 : Blo 1929435 5498837 := bbase (se 7 (by rfl) ⟨64439, by rfl⟩ : syracuseStep 5498837 = 128879) (by norm_num)
theorem B3665891 : Blo 1929435 3665891 := bstep (se 1 (by rfl) ⟨2749418, by rfl⟩ : syracuseStep 3665891 = 5498837) B5498837
theorem B2443927 : Blo 1929435 2443927 := bstep (se 1 (by rfl) ⟨1832945, by rfl⟩ : syracuseStep 2443927 = 3665891) B3665891
theorem B3258569 : Blo 1929435 3258569 := bstep (se 2 (by rfl) ⟨1221963, by rfl⟩ : syracuseStep 3258569 = 2443927) B2443927
theorem B2172379 : Blo 1929435 2172379 := bstep (se 1 (by rfl) ⟨1629284, by rfl⟩ : syracuseStep 2172379 = 3258569) B3258569
theorem B2896505 : Blo 1929435 2896505 := bstep (se 2 (by rfl) ⟨1086189, by rfl⟩ : syracuseStep 2896505 = 2172379) B2172379
theorem B1931003 : Blo 1929435 1931003 := bstep (se 1 (by rfl) ⟨1448252, by rfl⟩ : syracuseStep 1931003 = 2896505) B2896505
theorem B31317653 : Blo 1929435 31317653 := bbase (se 6 (by rfl) ⟨734007, by rfl⟩ : syracuseStep 31317653 = 1468015) (by norm_num)
theorem B20878435 : Blo 1929435 20878435 := bstep (se 1 (by rfl) ⟨15658826, by rfl⟩ : syracuseStep 20878435 = 31317653) B31317653
theorem B27837913 : Blo 1929435 27837913 := bstep (se 2 (by rfl) ⟨10439217, by rfl⟩ : syracuseStep 27837913 = 20878435) B20878435
theorem B37117217 : Blo 1929435 37117217 := bstep (se 2 (by rfl) ⟨13918956, by rfl⟩ : syracuseStep 37117217 = 27837913) B27837913
theorem B24744811 : Blo 1929435 24744811 := bstep (se 1 (by rfl) ⟨18558608, by rfl⟩ : syracuseStep 24744811 = 37117217) B37117217
theorem B32993081 : Blo 1929435 32993081 := bstep (se 2 (by rfl) ⟨12372405, by rfl⟩ : syracuseStep 32993081 = 24744811) B24744811
theorem B21995387 : Blo 1929435 21995387 := bstep (se 1 (by rfl) ⟨16496540, by rfl⟩ : syracuseStep 21995387 = 32993081) B32993081
theorem B14663591 : Blo 1929435 14663591 := bstep (se 1 (by rfl) ⟨10997693, by rfl⟩ : syracuseStep 14663591 = 21995387) B21995387
theorem B9775727 : Blo 1929435 9775727 := bstep (se 1 (by rfl) ⟨7331795, by rfl⟩ : syracuseStep 9775727 = 14663591) B14663591
theorem B6517151 : Blo 1929435 6517151 := bstep (se 1 (by rfl) ⟨4887863, by rfl⟩ : syracuseStep 6517151 = 9775727) B9775727
theorem B4344767 : Blo 1929435 4344767 := bstep (se 1 (by rfl) ⟨3258575, by rfl⟩ : syracuseStep 4344767 = 6517151) B6517151
theorem B2896511 : Blo 1929435 2896511 := bstep (se 1 (by rfl) ⟨2172383, by rfl⟩ : syracuseStep 2896511 = 4344767) B4344767
theorem B1931007 : Blo 1929435 1931007 := bstep (se 1 (by rfl) ⟨1448255, by rfl⟩ : syracuseStep 1931007 = 2896511) B2896511
theorem B2896517 : Blo 1929435 2896517 := bbase (se 4 (by rfl) ⟨271548, by rfl⟩ : syracuseStep 2896517 = 543097) (by norm_num)
theorem B1931011 : Blo 1929435 1931011 := bstep (se 1 (by rfl) ⟨1448258, by rfl⟩ : syracuseStep 1931011 = 2896517) B2896517
theorem B3258589 : Blo 1929435 3258589 := bbase (se 3 (by rfl) ⟨610985, by rfl⟩ : syracuseStep 3258589 = 1221971) (by norm_num)
theorem B4344785 : Blo 1929435 4344785 := bstep (se 2 (by rfl) ⟨1629294, by rfl⟩ : syracuseStep 4344785 = 3258589) B3258589
theorem B2896523 : Blo 1929435 2896523 := bstep (se 1 (by rfl) ⟨2172392, by rfl⟩ : syracuseStep 2896523 = 4344785) B4344785
theorem B1931015 : Blo 1929435 1931015 := bstep (se 1 (by rfl) ⟨1448261, by rfl⟩ : syracuseStep 1931015 = 2896523) B2896523
theorem B2172397 : Blo 1929435 2172397 := bbase (se 3 (by rfl) ⟨407324, by rfl⟩ : syracuseStep 2172397 = 814649) (by norm_num)
theorem B2896529 : Blo 1929435 2896529 := bstep (se 2 (by rfl) ⟨1086198, by rfl⟩ : syracuseStep 2896529 = 2172397) B2172397
theorem B1931019 : Blo 1929435 1931019 := bstep (se 1 (by rfl) ⟨1448264, by rfl⟩ : syracuseStep 1931019 = 2896529) B2896529
theorem B6517205 : Blo 1929435 6517205 := bbase (se 7 (by rfl) ⟨76373, by rfl⟩ : syracuseStep 6517205 = 152747) (by norm_num)
theorem B4344803 : Blo 1929435 4344803 := bstep (se 1 (by rfl) ⟨3258602, by rfl⟩ : syracuseStep 4344803 = 6517205) B6517205
theorem B2896535 : Blo 1929435 2896535 := bstep (se 1 (by rfl) ⟨2172401, by rfl⟩ : syracuseStep 2896535 = 4344803) B4344803
theorem B1931023 : Blo 1929435 1931023 := bstep (se 1 (by rfl) ⟨1448267, by rfl⟩ : syracuseStep 1931023 = 2896535) B2896535
theorem B2896541 : Blo 1929435 2896541 := bbase (se 3 (by rfl) ⟨543101, by rfl⟩ : syracuseStep 2896541 = 1086203) (by norm_num)
theorem B1931027 : Blo 1929435 1931027 := bstep (se 1 (by rfl) ⟨1448270, by rfl⟩ : syracuseStep 1931027 = 2896541) B2896541
theorem B4344821 : Blo 1929435 4344821 := bbase (se 5 (by rfl) ⟨203663, by rfl⟩ : syracuseStep 4344821 = 407327) (by norm_num)
theorem B2896547 : Blo 1929435 2896547 := bstep (se 1 (by rfl) ⟨2172410, by rfl⟩ : syracuseStep 2896547 = 4344821) B4344821
theorem B1931031 : Blo 1929435 1931031 := bstep (se 1 (by rfl) ⟨1448273, by rfl⟩ : syracuseStep 1931031 = 2896547) B2896547
theorem B2090233 : Blo 1929435 2090233 := bbase (se 2 (by rfl) ⟨783837, by rfl⟩ : syracuseStep 2090233 = 1567675) (by norm_num)
theorem B2786977 : Blo 1929435 2786977 := bstep (se 2 (by rfl) ⟨1045116, by rfl⟩ : syracuseStep 2786977 = 2090233) B2090233
theorem B3715969 : Blo 1929435 3715969 := bstep (se 2 (by rfl) ⟨1393488, by rfl⟩ : syracuseStep 3715969 = 2786977) B2786977
theorem B4954625 : Blo 1929435 4954625 := bstep (se 2 (by rfl) ⟨1857984, by rfl⟩ : syracuseStep 4954625 = 3715969) B3715969
theorem B3303083 : Blo 1929435 3303083 := bstep (se 1 (by rfl) ⟨2477312, by rfl⟩ : syracuseStep 3303083 = 4954625) B4954625
theorem B2202055 : Blo 1929435 2202055 := bstep (se 1 (by rfl) ⟨1651541, by rfl⟩ : syracuseStep 2202055 = 3303083) B3303083
theorem B11744293 : Blo 1929435 11744293 := bstep (se 4 (by rfl) ⟨1101027, by rfl⟩ : syracuseStep 11744293 = 2202055) B2202055
theorem B15659057 : Blo 1929435 15659057 := bstep (se 2 (by rfl) ⟨5872146, by rfl⟩ : syracuseStep 15659057 = 11744293) B11744293
theorem B10439371 : Blo 1929435 10439371 := bstep (se 1 (by rfl) ⟨7829528, by rfl⟩ : syracuseStep 10439371 = 15659057) B15659057
theorem B55676645 : Blo 1929435 55676645 := bstep (se 4 (by rfl) ⟨5219685, by rfl⟩ : syracuseStep 55676645 = 10439371) B10439371
theorem B37117763 : Blo 1929435 37117763 := bstep (se 1 (by rfl) ⟨27838322, by rfl⟩ : syracuseStep 37117763 = 55676645) B55676645
theorem B24745175 : Blo 1929435 24745175 := bstep (se 1 (by rfl) ⟨18558881, by rfl⟩ : syracuseStep 24745175 = 37117763) B37117763
theorem B16496783 : Blo 1929435 16496783 := bstep (se 1 (by rfl) ⟨12372587, by rfl⟩ : syracuseStep 16496783 = 24745175) B24745175
theorem B10997855 : Blo 1929435 10997855 := bstep (se 1 (by rfl) ⟨8248391, by rfl⟩ : syracuseStep 10997855 = 16496783) B16496783
theorem B7331903 : Blo 1929435 7331903 := bstep (se 1 (by rfl) ⟨5498927, by rfl⟩ : syracuseStep 7331903 = 10997855) B10997855
theorem B4887935 : Blo 1929435 4887935 := bstep (se 1 (by rfl) ⟨3665951, by rfl⟩ : syracuseStep 4887935 = 7331903) B7331903
theorem B3258623 : Blo 1929435 3258623 := bstep (se 1 (by rfl) ⟨2443967, by rfl⟩ : syracuseStep 3258623 = 4887935) B4887935
theorem B2172415 : Blo 1929435 2172415 := bstep (se 1 (by rfl) ⟨1629311, by rfl⟩ : syracuseStep 2172415 = 3258623) B3258623
theorem B2896553 : Blo 1929435 2896553 := bstep (se 2 (by rfl) ⟨1086207, by rfl⟩ : syracuseStep 2896553 = 2172415) B2172415
theorem B1931035 : Blo 1929435 1931035 := bstep (se 1 (by rfl) ⟨1448276, by rfl⟩ : syracuseStep 1931035 = 2896553) B2896553
theorem B2749469 : Blo 1929435 2749469 := bbase (se 3 (by rfl) ⟨515525, by rfl⟩ : syracuseStep 2749469 = 1031051) (by norm_num)
theorem B7331917 : Blo 1929435 7331917 := bstep (se 3 (by rfl) ⟨1374734, by rfl⟩ : syracuseStep 7331917 = 2749469) B2749469
theorem B9775889 : Blo 1929435 9775889 := bstep (se 2 (by rfl) ⟨3665958, by rfl⟩ : syracuseStep 9775889 = 7331917) B7331917
theorem B6517259 : Blo 1929435 6517259 := bstep (se 1 (by rfl) ⟨4887944, by rfl⟩ : syracuseStep 6517259 = 9775889) B9775889
theorem B4344839 : Blo 1929435 4344839 := bstep (se 1 (by rfl) ⟨3258629, by rfl⟩ : syracuseStep 4344839 = 6517259) B6517259
theorem B2896559 : Blo 1929435 2896559 := bstep (se 1 (by rfl) ⟨2172419, by rfl⟩ : syracuseStep 2896559 = 4344839) B4344839
theorem B1931039 : Blo 1929435 1931039 := bstep (se 1 (by rfl) ⟨1448279, by rfl⟩ : syracuseStep 1931039 = 2896559) B2896559
theorem B2896565 : Blo 1929435 2896565 := bbase (se 5 (by rfl) ⟨135776, by rfl⟩ : syracuseStep 2896565 = 271553) (by norm_num)
theorem B1931043 : Blo 1929435 1931043 := bstep (se 1 (by rfl) ⟨1448282, by rfl⟩ : syracuseStep 1931043 = 2896565) B2896565
theorem B4887965 : Blo 1929435 4887965 := bbase (se 3 (by rfl) ⟨916493, by rfl⟩ : syracuseStep 4887965 = 1832987) (by norm_num)
theorem B3258643 : Blo 1929435 3258643 := bstep (se 1 (by rfl) ⟨2443982, by rfl⟩ : syracuseStep 3258643 = 4887965) B4887965
theorem B4344857 : Blo 1929435 4344857 := bstep (se 2 (by rfl) ⟨1629321, by rfl⟩ : syracuseStep 4344857 = 3258643) B3258643
theorem B2896571 : Blo 1929435 2896571 := bstep (se 1 (by rfl) ⟨2172428, by rfl⟩ : syracuseStep 2896571 = 4344857) B4344857
theorem B1931047 : Blo 1929435 1931047 := bstep (se 1 (by rfl) ⟨1448285, by rfl⟩ : syracuseStep 1931047 = 2896571) B2896571
theorem B2172433 : Blo 1929435 2172433 := bbase (se 2 (by rfl) ⟨814662, by rfl⟩ : syracuseStep 2172433 = 1629325) (by norm_num)
theorem B2896577 : Blo 1929435 2896577 := bstep (se 2 (by rfl) ⟨1086216, by rfl⟩ : syracuseStep 2896577 = 2172433) B2172433
theorem B1931051 : Blo 1929435 1931051 := bstep (se 1 (by rfl) ⟨1448288, by rfl⟩ : syracuseStep 1931051 = 2896577) B2896577
theorem B3665989 : Blo 1929435 3665989 := bbase (se 4 (by rfl) ⟨343686, by rfl⟩ : syracuseStep 3665989 = 687373) (by norm_num)
theorem B4887985 : Blo 1929435 4887985 := bstep (se 2 (by rfl) ⟨1832994, by rfl⟩ : syracuseStep 4887985 = 3665989) B3665989
theorem B6517313 : Blo 1929435 6517313 := bstep (se 2 (by rfl) ⟨2443992, by rfl⟩ : syracuseStep 6517313 = 4887985) B4887985
theorem B4344875 : Blo 1929435 4344875 := bstep (se 1 (by rfl) ⟨3258656, by rfl⟩ : syracuseStep 4344875 = 6517313) B6517313
theorem B2896583 : Blo 1929435 2896583 := bstep (se 1 (by rfl) ⟨2172437, by rfl⟩ : syracuseStep 2896583 = 4344875) B4344875
theorem B1931055 : Blo 1929435 1931055 := bstep (se 1 (by rfl) ⟨1448291, by rfl⟩ : syracuseStep 1931055 = 2896583) B2896583
theorem B2896589 : Blo 1929435 2896589 := bbase (se 3 (by rfl) ⟨543110, by rfl⟩ : syracuseStep 2896589 = 1086221) (by norm_num)
theorem B1931059 : Blo 1929435 1931059 := bstep (se 1 (by rfl) ⟨1448294, by rfl⟩ : syracuseStep 1931059 = 2896589) B2896589
theorem B4344893 : Blo 1929435 4344893 := bbase (se 3 (by rfl) ⟨814667, by rfl⟩ : syracuseStep 4344893 = 1629335) (by norm_num)
theorem B2896595 : Blo 1929435 2896595 := bstep (se 1 (by rfl) ⟨2172446, by rfl⟩ : syracuseStep 2896595 = 4344893) B4344893
theorem B1931063 : Blo 1929435 1931063 := bstep (se 1 (by rfl) ⟨1448297, by rfl⟩ : syracuseStep 1931063 = 2896595) B2896595
theorem B3258677 : Blo 1929435 3258677 := bbase (se 5 (by rfl) ⟨152750, by rfl⟩ : syracuseStep 3258677 = 305501) (by norm_num)
theorem B2172451 : Blo 1929435 2172451 := bstep (se 1 (by rfl) ⟨1629338, by rfl⟩ : syracuseStep 2172451 = 3258677) B3258677
theorem B2896601 : Blo 1929435 2896601 := bstep (se 2 (by rfl) ⟨1086225, by rfl⟩ : syracuseStep 2896601 = 2172451) B2172451
theorem B1931067 : Blo 1929435 1931067 := bstep (se 1 (by rfl) ⟨1448300, by rfl⟩ : syracuseStep 1931067 = 2896601) B2896601
theorem B5499029 : Blo 1929435 5499029 := bbase (se 6 (by rfl) ⟨128883, by rfl⟩ : syracuseStep 5499029 = 257767) (by norm_num)
theorem B14664077 : Blo 1929435 14664077 := bstep (se 3 (by rfl) ⟨2749514, by rfl⟩ : syracuseStep 14664077 = 5499029) B5499029
theorem B9776051 : Blo 1929435 9776051 := bstep (se 1 (by rfl) ⟨7332038, by rfl⟩ : syracuseStep 9776051 = 14664077) B14664077
theorem B6517367 : Blo 1929435 6517367 := bstep (se 1 (by rfl) ⟨4888025, by rfl⟩ : syracuseStep 6517367 = 9776051) B9776051
theorem B4344911 : Blo 1929435 4344911 := bstep (se 1 (by rfl) ⟨3258683, by rfl⟩ : syracuseStep 4344911 = 6517367) B6517367
theorem B2896607 : Blo 1929435 2896607 := bstep (se 1 (by rfl) ⟨2172455, by rfl⟩ : syracuseStep 2896607 = 4344911) B4344911
theorem B1931071 : Blo 1929435 1931071 := bstep (se 1 (by rfl) ⟨1448303, by rfl⟩ : syracuseStep 1931071 = 2896607) B2896607
theorem B2896613 : Blo 1929435 2896613 := bbase (se 4 (by rfl) ⟨271557, by rfl⟩ : syracuseStep 2896613 = 543115) (by norm_num)
theorem B1931075 : Blo 1929435 1931075 := bstep (se 1 (by rfl) ⟨1448306, by rfl⟩ : syracuseStep 1931075 = 2896613) B2896613
theorem B2062145 : Blo 1929435 2062145 := bbase (se 2 (by rfl) ⟨773304, by rfl⟩ : syracuseStep 2062145 = 1546609) (by norm_num)
theorem B5499053 : Blo 1929435 5499053 := bstep (se 3 (by rfl) ⟨1031072, by rfl⟩ : syracuseStep 5499053 = 2062145) B2062145
theorem B3666035 : Blo 1929435 3666035 := bstep (se 1 (by rfl) ⟨2749526, by rfl⟩ : syracuseStep 3666035 = 5499053) B5499053
theorem B2444023 : Blo 1929435 2444023 := bstep (se 1 (by rfl) ⟨1833017, by rfl⟩ : syracuseStep 2444023 = 3666035) B3666035
theorem B3258697 : Blo 1929435 3258697 := bstep (se 2 (by rfl) ⟨1222011, by rfl⟩ : syracuseStep 3258697 = 2444023) B2444023
theorem B4344929 : Blo 1929435 4344929 := bstep (se 2 (by rfl) ⟨1629348, by rfl⟩ : syracuseStep 4344929 = 3258697) B3258697
theorem B2896619 : Blo 1929435 2896619 := bstep (se 1 (by rfl) ⟨2172464, by rfl⟩ : syracuseStep 2896619 = 4344929) B4344929
theorem B1931079 : Blo 1929435 1931079 := bstep (se 1 (by rfl) ⟨1448309, by rfl⟩ : syracuseStep 1931079 = 2896619) B2896619
theorem B2172469 : Blo 1929435 2172469 := bbase (se 5 (by rfl) ⟨101834, by rfl⟩ : syracuseStep 2172469 = 203669) (by norm_num)
theorem B2896625 : Blo 1929435 2896625 := bstep (se 2 (by rfl) ⟨1086234, by rfl⟩ : syracuseStep 2896625 = 2172469) B2172469
theorem B1931083 : Blo 1929435 1931083 := bstep (se 1 (by rfl) ⟨1448312, by rfl⟩ : syracuseStep 1931083 = 2896625) B2896625
theorem B2444033 : Blo 1929435 2444033 := bbase (se 2 (by rfl) ⟨916512, by rfl⟩ : syracuseStep 2444033 = 1833025) (by norm_num)
theorem B6517421 : Blo 1929435 6517421 := bstep (se 3 (by rfl) ⟨1222016, by rfl⟩ : syracuseStep 6517421 = 2444033) B2444033
theorem B4344947 : Blo 1929435 4344947 := bstep (se 1 (by rfl) ⟨3258710, by rfl⟩ : syracuseStep 4344947 = 6517421) B6517421
theorem B2896631 : Blo 1929435 2896631 := bstep (se 1 (by rfl) ⟨2172473, by rfl⟩ : syracuseStep 2896631 = 4344947) B4344947
theorem B1931087 : Blo 1929435 1931087 := bstep (se 1 (by rfl) ⟨1448315, by rfl⟩ : syracuseStep 1931087 = 2896631) B2896631
theorem B2896637 : Blo 1929435 2896637 := bbase (se 3 (by rfl) ⟨543119, by rfl⟩ : syracuseStep 2896637 = 1086239) (by norm_num)
theorem B1931091 : Blo 1929435 1931091 := bstep (se 1 (by rfl) ⟨1448318, by rfl⟩ : syracuseStep 1931091 = 2896637) B2896637
theorem B4344965 : Blo 1929435 4344965 := bbase (se 4 (by rfl) ⟨407340, by rfl⟩ : syracuseStep 4344965 = 814681) (by norm_num)
theorem B2896643 : Blo 1929435 2896643 := bstep (se 1 (by rfl) ⟨2172482, by rfl⟩ : syracuseStep 2896643 = 4344965) B4344965
theorem B1931095 : Blo 1929435 1931095 := bstep (se 1 (by rfl) ⟨1448321, by rfl⟩ : syracuseStep 1931095 = 2896643) B2896643
theorem B4124333 : Blo 1929435 4124333 := bbase (se 3 (by rfl) ⟨773312, by rfl⟩ : syracuseStep 4124333 = 1546625) (by norm_num)
theorem B2749555 : Blo 1929435 2749555 := bstep (se 1 (by rfl) ⟨2062166, by rfl⟩ : syracuseStep 2749555 = 4124333) B4124333
theorem B3666073 : Blo 1929435 3666073 := bstep (se 2 (by rfl) ⟨1374777, by rfl⟩ : syracuseStep 3666073 = 2749555) B2749555
theorem B4888097 : Blo 1929435 4888097 := bstep (se 2 (by rfl) ⟨1833036, by rfl⟩ : syracuseStep 4888097 = 3666073) B3666073
theorem B3258731 : Blo 1929435 3258731 := bstep (se 1 (by rfl) ⟨2444048, by rfl⟩ : syracuseStep 3258731 = 4888097) B4888097
theorem B2172487 : Blo 1929435 2172487 := bstep (se 1 (by rfl) ⟨1629365, by rfl⟩ : syracuseStep 2172487 = 3258731) B3258731
theorem B2896649 : Blo 1929435 2896649 := bstep (se 2 (by rfl) ⟨1086243, by rfl⟩ : syracuseStep 2896649 = 2172487) B2172487
theorem B1931099 : Blo 1929435 1931099 := bstep (se 1 (by rfl) ⟨1448324, by rfl⟩ : syracuseStep 1931099 = 2896649) B2896649
theorem B9776213 : Blo 1929435 9776213 := bbase (se 8 (by rfl) ⟨57282, by rfl⟩ : syracuseStep 9776213 = 114565) (by norm_num)
theorem B6517475 : Blo 1929435 6517475 := bstep (se 1 (by rfl) ⟨4888106, by rfl⟩ : syracuseStep 6517475 = 9776213) B9776213
theorem B4344983 : Blo 1929435 4344983 := bstep (se 1 (by rfl) ⟨3258737, by rfl⟩ : syracuseStep 4344983 = 6517475) B6517475
theorem B2896655 : Blo 1929435 2896655 := bstep (se 1 (by rfl) ⟨2172491, by rfl⟩ : syracuseStep 2896655 = 4344983) B4344983
theorem B1931103 : Blo 1929435 1931103 := bstep (se 1 (by rfl) ⟨1448327, by rfl⟩ : syracuseStep 1931103 = 2896655) B2896655
theorem B2896661 : Blo 1929435 2896661 := bbase (se 6 (by rfl) ⟨67890, by rfl⟩ : syracuseStep 2896661 = 135781) (by norm_num)
theorem B1931107 : Blo 1929435 1931107 := bstep (se 1 (by rfl) ⟨1448330, by rfl⟩ : syracuseStep 1931107 = 2896661) B2896661
theorem B2936189 : Blo 1929435 2936189 := bbase (se 3 (by rfl) ⟨550535, by rfl⟩ : syracuseStep 2936189 = 1101071) (by norm_num)
theorem B7829837 : Blo 1929435 7829837 := bstep (se 3 (by rfl) ⟨1468094, by rfl⟩ : syracuseStep 7829837 = 2936189) B2936189
theorem B5219891 : Blo 1929435 5219891 := bstep (se 1 (by rfl) ⟨3914918, by rfl⟩ : syracuseStep 5219891 = 7829837) B7829837
theorem B3479927 : Blo 1929435 3479927 := bstep (se 1 (by rfl) ⟨2609945, by rfl⟩ : syracuseStep 3479927 = 5219891) B5219891
theorem B37119221 : Blo 1929435 37119221 := bstep (se 5 (by rfl) ⟨1739963, by rfl⟩ : syracuseStep 37119221 = 3479927) B3479927
theorem B24746147 : Blo 1929435 24746147 := bstep (se 1 (by rfl) ⟨18559610, by rfl⟩ : syracuseStep 24746147 = 37119221) B37119221
theorem B16497431 : Blo 1929435 16497431 := bstep (se 1 (by rfl) ⟨12373073, by rfl⟩ : syracuseStep 16497431 = 24746147) B24746147
theorem B10998287 : Blo 1929435 10998287 := bstep (se 1 (by rfl) ⟨8248715, by rfl⟩ : syracuseStep 10998287 = 16497431) B16497431
theorem B7332191 : Blo 1929435 7332191 := bstep (se 1 (by rfl) ⟨5499143, by rfl⟩ : syracuseStep 7332191 = 10998287) B10998287
theorem B4888127 : Blo 1929435 4888127 := bstep (se 1 (by rfl) ⟨3666095, by rfl⟩ : syracuseStep 4888127 = 7332191) B7332191
theorem B3258751 : Blo 1929435 3258751 := bstep (se 1 (by rfl) ⟨2444063, by rfl⟩ : syracuseStep 3258751 = 4888127) B4888127
theorem B4345001 : Blo 1929435 4345001 := bstep (se 2 (by rfl) ⟨1629375, by rfl⟩ : syracuseStep 4345001 = 3258751) B3258751
theorem B2896667 : Blo 1929435 2896667 := bstep (se 1 (by rfl) ⟨2172500, by rfl⟩ : syracuseStep 2896667 = 4345001) B4345001
theorem B1931111 : Blo 1929435 1931111 := bstep (se 1 (by rfl) ⟨1448333, by rfl⟩ : syracuseStep 1931111 = 2896667) B2896667
theorem B2172505 : Blo 1929435 2172505 := bbase (se 2 (by rfl) ⟨814689, by rfl⟩ : syracuseStep 2172505 = 1629379) (by norm_num)
theorem B2896673 : Blo 1929435 2896673 := bstep (se 2 (by rfl) ⟨1086252, by rfl⟩ : syracuseStep 2896673 = 2172505) B2172505
theorem B1931115 : Blo 1929435 1931115 := bstep (se 1 (by rfl) ⟨1448336, by rfl⟩ : syracuseStep 1931115 = 2896673) B2896673
theorem B9279845 : Blo 1929435 9279845 := bbase (se 4 (by rfl) ⟨869985, by rfl⟩ : syracuseStep 9279845 = 1739971) (by norm_num)
theorem B6186563 : Blo 1929435 6186563 := bstep (se 1 (by rfl) ⟨4639922, by rfl⟩ : syracuseStep 6186563 = 9279845) B9279845
theorem B4124375 : Blo 1929435 4124375 := bstep (se 1 (by rfl) ⟨3093281, by rfl⟩ : syracuseStep 4124375 = 6186563) B6186563
theorem B2749583 : Blo 1929435 2749583 := bstep (se 1 (by rfl) ⟨2062187, by rfl⟩ : syracuseStep 2749583 = 4124375) B4124375
theorem B7332221 : Blo 1929435 7332221 := bstep (se 3 (by rfl) ⟨1374791, by rfl⟩ : syracuseStep 7332221 = 2749583) B2749583
theorem B4888147 : Blo 1929435 4888147 := bstep (se 1 (by rfl) ⟨3666110, by rfl⟩ : syracuseStep 4888147 = 7332221) B7332221
theorem B6517529 : Blo 1929435 6517529 := bstep (se 2 (by rfl) ⟨2444073, by rfl⟩ : syracuseStep 6517529 = 4888147) B4888147
theorem B4345019 : Blo 1929435 4345019 := bstep (se 1 (by rfl) ⟨3258764, by rfl⟩ : syracuseStep 4345019 = 6517529) B6517529
theorem B2896679 : Blo 1929435 2896679 := bstep (se 1 (by rfl) ⟨2172509, by rfl⟩ : syracuseStep 2896679 = 4345019) B4345019
theorem B1931119 : Blo 1929435 1931119 := bstep (se 1 (by rfl) ⟨1448339, by rfl⟩ : syracuseStep 1931119 = 2896679) B2896679
theorem B2896685 : Blo 1929435 2896685 := bbase (se 3 (by rfl) ⟨543128, by rfl⟩ : syracuseStep 2896685 = 1086257) (by norm_num)
theorem B1931123 : Blo 1929435 1931123 := bstep (se 1 (by rfl) ⟨1448342, by rfl⟩ : syracuseStep 1931123 = 2896685) B2896685
theorem B4345037 : Blo 1929435 4345037 := bbase (se 3 (by rfl) ⟨814694, by rfl⟩ : syracuseStep 4345037 = 1629389) (by norm_num)
theorem B2896691 : Blo 1929435 2896691 := bstep (se 1 (by rfl) ⟨2172518, by rfl⟩ : syracuseStep 2896691 = 4345037) B4345037
theorem B1931127 : Blo 1929435 1931127 := bstep (se 1 (by rfl) ⟨1448345, by rfl⟩ : syracuseStep 1931127 = 2896691) B2896691
theorem B2444089 : Blo 1929435 2444089 := bbase (se 2 (by rfl) ⟨916533, by rfl⟩ : syracuseStep 2444089 = 1833067) (by norm_num)
theorem B3258785 : Blo 1929435 3258785 := bstep (se 2 (by rfl) ⟨1222044, by rfl⟩ : syracuseStep 3258785 = 2444089) B2444089
theorem B2172523 : Blo 1929435 2172523 := bstep (se 1 (by rfl) ⟨1629392, by rfl⟩ : syracuseStep 2172523 = 3258785) B3258785
theorem B2896697 : Blo 1929435 2896697 := bstep (se 2 (by rfl) ⟨1086261, by rfl⟩ : syracuseStep 2896697 = 2172523) B2172523
theorem B1931131 : Blo 1929435 1931131 := bstep (se 1 (by rfl) ⟨1448348, by rfl⟩ : syracuseStep 1931131 = 2896697) B2896697
theorem B6186613 : Blo 1929435 6186613 := bbase (se 5 (by rfl) ⟨289997, by rfl⟩ : syracuseStep 6186613 = 579995) (by norm_num)
theorem B8248817 : Blo 1929435 8248817 := bstep (se 2 (by rfl) ⟨3093306, by rfl⟩ : syracuseStep 8248817 = 6186613) B6186613
theorem B21996845 : Blo 1929435 21996845 := bstep (se 3 (by rfl) ⟨4124408, by rfl⟩ : syracuseStep 21996845 = 8248817) B8248817
theorem B14664563 : Blo 1929435 14664563 := bstep (se 1 (by rfl) ⟨10998422, by rfl⟩ : syracuseStep 14664563 = 21996845) B21996845
theorem B9776375 : Blo 1929435 9776375 := bstep (se 1 (by rfl) ⟨7332281, by rfl⟩ : syracuseStep 9776375 = 14664563) B14664563
theorem B6517583 : Blo 1929435 6517583 := bstep (se 1 (by rfl) ⟨4888187, by rfl⟩ : syracuseStep 6517583 = 9776375) B9776375
theorem B4345055 : Blo 1929435 4345055 := bstep (se 1 (by rfl) ⟨3258791, by rfl⟩ : syracuseStep 4345055 = 6517583) B6517583
theorem B2896703 : Blo 1929435 2896703 := bstep (se 1 (by rfl) ⟨2172527, by rfl⟩ : syracuseStep 2896703 = 4345055) B4345055
theorem B1931135 : Blo 1929435 1931135 := bstep (se 1 (by rfl) ⟨1448351, by rfl⟩ : syracuseStep 1931135 = 2896703) B2896703
theorem B2896709 : Blo 1929435 2896709 := bbase (se 4 (by rfl) ⟨271566, by rfl⟩ : syracuseStep 2896709 = 543133) (by norm_num)
theorem B1931139 : Blo 1929435 1931139 := bstep (se 1 (by rfl) ⟨1448354, by rfl⟩ : syracuseStep 1931139 = 2896709) B2896709
theorem B3258805 : Blo 1929435 3258805 := bbase (se 5 (by rfl) ⟨152756, by rfl⟩ : syracuseStep 3258805 = 305513) (by norm_num)
theorem B4345073 : Blo 1929435 4345073 := bstep (se 2 (by rfl) ⟨1629402, by rfl⟩ : syracuseStep 4345073 = 3258805) B3258805
theorem B2896715 : Blo 1929435 2896715 := bstep (se 1 (by rfl) ⟨2172536, by rfl⟩ : syracuseStep 2896715 = 4345073) B4345073
theorem B1931143 : Blo 1929435 1931143 := bstep (se 1 (by rfl) ⟨1448357, by rfl⟩ : syracuseStep 1931143 = 2896715) B2896715
theorem B2172541 : Blo 1929435 2172541 := bbase (se 3 (by rfl) ⟨407351, by rfl⟩ : syracuseStep 2172541 = 814703) (by norm_num)
theorem B2896721 : Blo 1929435 2896721 := bstep (se 2 (by rfl) ⟨1086270, by rfl⟩ : syracuseStep 2896721 = 2172541) B2172541
theorem B1931147 : Blo 1929435 1931147 := bstep (se 1 (by rfl) ⟨1448360, by rfl⟩ : syracuseStep 1931147 = 2896721) B2896721
theorem B6517637 : Blo 1929435 6517637 := bbase (se 4 (by rfl) ⟨611028, by rfl⟩ : syracuseStep 6517637 = 1222057) (by norm_num)
theorem B4345091 : Blo 1929435 4345091 := bstep (se 1 (by rfl) ⟨3258818, by rfl⟩ : syracuseStep 4345091 = 6517637) B6517637
theorem B2896727 : Blo 1929435 2896727 := bstep (se 1 (by rfl) ⟨2172545, by rfl⟩ : syracuseStep 2896727 = 4345091) B4345091
theorem B1931151 : Blo 1929435 1931151 := bstep (se 1 (by rfl) ⟨1448363, by rfl⟩ : syracuseStep 1931151 = 2896727) B2896727
theorem B2896733 : Blo 1929435 2896733 := bbase (se 3 (by rfl) ⟨543137, by rfl⟩ : syracuseStep 2896733 = 1086275) (by norm_num)
theorem B1931155 : Blo 1929435 1931155 := bstep (se 1 (by rfl) ⟨1448366, by rfl⟩ : syracuseStep 1931155 = 2896733) B2896733
theorem B4345109 : Blo 1929435 4345109 := bbase (se 6 (by rfl) ⟨101838, by rfl⟩ : syracuseStep 4345109 = 203677) (by norm_num)
theorem B2896739 : Blo 1929435 2896739 := bstep (se 1 (by rfl) ⟨2172554, by rfl⟩ : syracuseStep 2896739 = 4345109) B4345109
theorem B1931159 : Blo 1929435 1931159 := bstep (se 1 (by rfl) ⟨1448369, by rfl⟩ : syracuseStep 1931159 = 2896739) B2896739
theorem B7332389 : Blo 1929435 7332389 := bbase (se 4 (by rfl) ⟨687411, by rfl⟩ : syracuseStep 7332389 = 1374823) (by norm_num)
theorem B4888259 : Blo 1929435 4888259 := bstep (se 1 (by rfl) ⟨3666194, by rfl⟩ : syracuseStep 4888259 = 7332389) B7332389
theorem B3258839 : Blo 1929435 3258839 := bstep (se 1 (by rfl) ⟨2444129, by rfl⟩ : syracuseStep 3258839 = 4888259) B4888259
theorem B2172559 : Blo 1929435 2172559 := bstep (se 1 (by rfl) ⟨1629419, by rfl⟩ : syracuseStep 2172559 = 3258839) B3258839
theorem B2896745 : Blo 1929435 2896745 := bstep (se 2 (by rfl) ⟨1086279, by rfl⟩ : syracuseStep 2896745 = 2172559) B2172559
theorem B1931163 : Blo 1929435 1931163 := bstep (se 1 (by rfl) ⟨1448372, by rfl⟩ : syracuseStep 1931163 = 2896745) B2896745
theorem B4124477 : Blo 1929435 4124477 := bbase (se 3 (by rfl) ⟨773339, by rfl⟩ : syracuseStep 4124477 = 1546679) (by norm_num)
theorem B10998605 : Blo 1929435 10998605 := bstep (se 3 (by rfl) ⟨2062238, by rfl⟩ : syracuseStep 10998605 = 4124477) B4124477
theorem B7332403 : Blo 1929435 7332403 := bstep (se 1 (by rfl) ⟨5499302, by rfl⟩ : syracuseStep 7332403 = 10998605) B10998605
theorem B9776537 : Blo 1929435 9776537 := bstep (se 2 (by rfl) ⟨3666201, by rfl⟩ : syracuseStep 9776537 = 7332403) B7332403
theorem B6517691 : Blo 1929435 6517691 := bstep (se 1 (by rfl) ⟨4888268, by rfl⟩ : syracuseStep 6517691 = 9776537) B9776537
theorem B4345127 : Blo 1929435 4345127 := bstep (se 1 (by rfl) ⟨3258845, by rfl⟩ : syracuseStep 4345127 = 6517691) B6517691
theorem B2896751 : Blo 1929435 2896751 := bstep (se 1 (by rfl) ⟨2172563, by rfl⟩ : syracuseStep 2896751 = 4345127) B4345127
theorem B1931167 : Blo 1929435 1931167 := bstep (se 1 (by rfl) ⟨1448375, by rfl⟩ : syracuseStep 1931167 = 2896751) B2896751
theorem B2896757 : Blo 1929435 2896757 := bbase (se 5 (by rfl) ⟨135785, by rfl⟩ : syracuseStep 2896757 = 271571) (by norm_num)
theorem B1931171 : Blo 1929435 1931171 := bstep (se 1 (by rfl) ⟨1448378, by rfl⟩ : syracuseStep 1931171 = 2896757) B2896757
theorem B3527525 : Blo 1929435 3527525 := bbase (se 4 (by rfl) ⟨330705, by rfl⟩ : syracuseStep 3527525 = 661411) (by norm_num)
theorem B2351683 : Blo 1929435 2351683 := bstep (se 1 (by rfl) ⟨1763762, by rfl⟩ : syracuseStep 2351683 = 3527525) B3527525
theorem B12542309 : Blo 1929435 12542309 := bstep (se 4 (by rfl) ⟨1175841, by rfl⟩ : syracuseStep 12542309 = 2351683) B2351683
theorem B8361539 : Blo 1929435 8361539 := bstep (se 1 (by rfl) ⟨6271154, by rfl⟩ : syracuseStep 8361539 = 12542309) B12542309
theorem B5574359 : Blo 1929435 5574359 := bstep (se 1 (by rfl) ⟨4180769, by rfl⟩ : syracuseStep 5574359 = 8361539) B8361539
theorem B14864957 : Blo 1929435 14864957 := bstep (se 3 (by rfl) ⟨2787179, by rfl⟩ : syracuseStep 14864957 = 5574359) B5574359
theorem B9909971 : Blo 1929435 9909971 := bstep (se 1 (by rfl) ⟨7432478, by rfl⟩ : syracuseStep 9909971 = 14864957) B14864957
theorem B6606647 : Blo 1929435 6606647 := bstep (se 1 (by rfl) ⟨4954985, by rfl⟩ : syracuseStep 6606647 = 9909971) B9909971
theorem B4404431 : Blo 1929435 4404431 := bstep (se 1 (by rfl) ⟨3303323, by rfl⟩ : syracuseStep 4404431 = 6606647) B6606647
theorem B2936287 : Blo 1929435 2936287 := bstep (se 1 (by rfl) ⟨2202215, by rfl⟩ : syracuseStep 2936287 = 4404431) B4404431
theorem B3915049 : Blo 1929435 3915049 := bstep (se 2 (by rfl) ⟨1468143, by rfl⟩ : syracuseStep 3915049 = 2936287) B2936287
theorem B5220065 : Blo 1929435 5220065 := bstep (se 2 (by rfl) ⟨1957524, by rfl⟩ : syracuseStep 5220065 = 3915049) B3915049
theorem B13920173 : Blo 1929435 13920173 := bstep (se 3 (by rfl) ⟨2610032, by rfl⟩ : syracuseStep 13920173 = 5220065) B5220065
theorem B9280115 : Blo 1929435 9280115 := bstep (se 1 (by rfl) ⟨6960086, by rfl⟩ : syracuseStep 9280115 = 13920173) B13920173
theorem B6186743 : Blo 1929435 6186743 := bstep (se 1 (by rfl) ⟨4640057, by rfl⟩ : syracuseStep 6186743 = 9280115) B9280115
theorem B4124495 : Blo 1929435 4124495 := bstep (se 1 (by rfl) ⟨3093371, by rfl⟩ : syracuseStep 4124495 = 6186743) B6186743
theorem B2749663 : Blo 1929435 2749663 := bstep (se 1 (by rfl) ⟨2062247, by rfl⟩ : syracuseStep 2749663 = 4124495) B4124495
theorem B3666217 : Blo 1929435 3666217 := bstep (se 2 (by rfl) ⟨1374831, by rfl⟩ : syracuseStep 3666217 = 2749663) B2749663
theorem B4888289 : Blo 1929435 4888289 := bstep (se 2 (by rfl) ⟨1833108, by rfl⟩ : syracuseStep 4888289 = 3666217) B3666217
theorem B3258859 : Blo 1929435 3258859 := bstep (se 1 (by rfl) ⟨2444144, by rfl⟩ : syracuseStep 3258859 = 4888289) B4888289
theorem B4345145 : Blo 1929435 4345145 := bstep (se 2 (by rfl) ⟨1629429, by rfl⟩ : syracuseStep 4345145 = 3258859) B3258859
theorem B2896763 : Blo 1929435 2896763 := bstep (se 1 (by rfl) ⟨2172572, by rfl⟩ : syracuseStep 2896763 = 4345145) B4345145
theorem B1931175 : Blo 1929435 1931175 := bstep (se 1 (by rfl) ⟨1448381, by rfl⟩ : syracuseStep 1931175 = 2896763) B2896763
theorem B2172577 : Blo 1929435 2172577 := bbase (se 2 (by rfl) ⟨814716, by rfl⟩ : syracuseStep 2172577 = 1629433) (by norm_num)
theorem B2896769 : Blo 1929435 2896769 := bstep (se 2 (by rfl) ⟨1086288, by rfl⟩ : syracuseStep 2896769 = 2172577) B2172577
theorem B1931179 : Blo 1929435 1931179 := bstep (se 1 (by rfl) ⟨1448384, by rfl⟩ : syracuseStep 1931179 = 2896769) B2896769
theorem B4888309 : Blo 1929435 4888309 := bbase (se 5 (by rfl) ⟨229139, by rfl⟩ : syracuseStep 4888309 = 458279) (by norm_num)
theorem B6517745 : Blo 1929435 6517745 := bstep (se 2 (by rfl) ⟨2444154, by rfl⟩ : syracuseStep 6517745 = 4888309) B4888309
theorem B4345163 : Blo 1929435 4345163 := bstep (se 1 (by rfl) ⟨3258872, by rfl⟩ : syracuseStep 4345163 = 6517745) B6517745
theorem B2896775 : Blo 1929435 2896775 := bstep (se 1 (by rfl) ⟨2172581, by rfl⟩ : syracuseStep 2896775 = 4345163) B4345163
theorem B1931183 : Blo 1929435 1931183 := bstep (se 1 (by rfl) ⟨1448387, by rfl⟩ : syracuseStep 1931183 = 2896775) B2896775
theorem B2896781 : Blo 1929435 2896781 := bbase (se 3 (by rfl) ⟨543146, by rfl⟩ : syracuseStep 2896781 = 1086293) (by norm_num)
theorem B1931187 : Blo 1929435 1931187 := bstep (se 1 (by rfl) ⟨1448390, by rfl⟩ : syracuseStep 1931187 = 2896781) B2896781
theorem B4345181 : Blo 1929435 4345181 := bbase (se 3 (by rfl) ⟨814721, by rfl⟩ : syracuseStep 4345181 = 1629443) (by norm_num)
theorem B2896787 : Blo 1929435 2896787 := bstep (se 1 (by rfl) ⟨2172590, by rfl⟩ : syracuseStep 2896787 = 4345181) B4345181
theorem B1931191 : Blo 1929435 1931191 := bstep (se 1 (by rfl) ⟨1448393, by rfl⟩ : syracuseStep 1931191 = 2896787) B2896787
theorem B3258893 : Blo 1929435 3258893 := bbase (se 3 (by rfl) ⟨611042, by rfl⟩ : syracuseStep 3258893 = 1222085) (by norm_num)
theorem B2172595 : Blo 1929435 2172595 := bstep (se 1 (by rfl) ⟨1629446, by rfl⟩ : syracuseStep 2172595 = 3258893) B3258893
theorem B2896793 : Blo 1929435 2896793 := bstep (se 2 (by rfl) ⟨1086297, by rfl⟩ : syracuseStep 2896793 = 2172595) B2172595
theorem B1931195 : Blo 1929435 1931195 := bstep (se 1 (by rfl) ⟨1448396, by rfl⟩ : syracuseStep 1931195 = 2896793) B2896793
theorem B2320057 : Blo 1929435 2320057 := bbase (se 2 (by rfl) ⟨870021, by rfl⟩ : syracuseStep 2320057 = 1740043) (by norm_num)
theorem B3093409 : Blo 1929435 3093409 := bstep (se 2 (by rfl) ⟨1160028, by rfl⟩ : syracuseStep 3093409 = 2320057) B2320057
theorem B16498181 : Blo 1929435 16498181 := bstep (se 4 (by rfl) ⟨1546704, by rfl⟩ : syracuseStep 16498181 = 3093409) B3093409
theorem B10998787 : Blo 1929435 10998787 := bstep (se 1 (by rfl) ⟨8249090, by rfl⟩ : syracuseStep 10998787 = 16498181) B16498181
theorem B14665049 : Blo 1929435 14665049 := bstep (se 2 (by rfl) ⟨5499393, by rfl⟩ : syracuseStep 14665049 = 10998787) B10998787
theorem B9776699 : Blo 1929435 9776699 := bstep (se 1 (by rfl) ⟨7332524, by rfl⟩ : syracuseStep 9776699 = 14665049) B14665049
theorem B6517799 : Blo 1929435 6517799 := bstep (se 1 (by rfl) ⟨4888349, by rfl⟩ : syracuseStep 6517799 = 9776699) B9776699
theorem B4345199 : Blo 1929435 4345199 := bstep (se 1 (by rfl) ⟨3258899, by rfl⟩ : syracuseStep 4345199 = 6517799) B6517799
theorem B2896799 : Blo 1929435 2896799 := bstep (se 1 (by rfl) ⟨2172599, by rfl⟩ : syracuseStep 2896799 = 4345199) B4345199
theorem B1931199 : Blo 1929435 1931199 := bstep (se 1 (by rfl) ⟨1448399, by rfl⟩ : syracuseStep 1931199 = 2896799) B2896799
theorem B2896805 : Blo 1929435 2896805 := bbase (se 4 (by rfl) ⟨271575, by rfl⟩ : syracuseStep 2896805 = 543151) (by norm_num)
theorem B1931203 : Blo 1929435 1931203 := bstep (se 1 (by rfl) ⟨1448402, by rfl⟩ : syracuseStep 1931203 = 2896805) B2896805
theorem B2444185 : Blo 1929435 2444185 := bbase (se 2 (by rfl) ⟨916569, by rfl⟩ : syracuseStep 2444185 = 1833139) (by norm_num)
theorem B3258913 : Blo 1929435 3258913 := bstep (se 2 (by rfl) ⟨1222092, by rfl⟩ : syracuseStep 3258913 = 2444185) B2444185
theorem B4345217 : Blo 1929435 4345217 := bstep (se 2 (by rfl) ⟨1629456, by rfl⟩ : syracuseStep 4345217 = 3258913) B3258913
theorem B2896811 : Blo 1929435 2896811 := bstep (se 1 (by rfl) ⟨2172608, by rfl⟩ : syracuseStep 2896811 = 4345217) B4345217
theorem B1931207 : Blo 1929435 1931207 := bstep (se 1 (by rfl) ⟨1448405, by rfl⟩ : syracuseStep 1931207 = 2896811) B2896811
theorem B2172613 : Blo 1929435 2172613 := bbase (se 4 (by rfl) ⟨203682, by rfl⟩ : syracuseStep 2172613 = 407365) (by norm_num)
theorem B2896817 : Blo 1929435 2896817 := bstep (se 2 (by rfl) ⟨1086306, by rfl⟩ : syracuseStep 2896817 = 2172613) B2172613
theorem B1931211 : Blo 1929435 1931211 := bstep (se 1 (by rfl) ⟨1448408, by rfl⟩ : syracuseStep 1931211 = 2896817) B2896817
theorem B3666293 : Blo 1929435 3666293 := bbase (se 5 (by rfl) ⟨171857, by rfl⟩ : syracuseStep 3666293 = 343715) (by norm_num)
theorem B2444195 : Blo 1929435 2444195 := bstep (se 1 (by rfl) ⟨1833146, by rfl⟩ : syracuseStep 2444195 = 3666293) B3666293
theorem B6517853 : Blo 1929435 6517853 := bstep (se 3 (by rfl) ⟨1222097, by rfl⟩ : syracuseStep 6517853 = 2444195) B2444195
theorem B4345235 : Blo 1929435 4345235 := bstep (se 1 (by rfl) ⟨3258926, by rfl⟩ : syracuseStep 4345235 = 6517853) B6517853
theorem B2896823 : Blo 1929435 2896823 := bstep (se 1 (by rfl) ⟨2172617, by rfl⟩ : syracuseStep 2896823 = 4345235) B4345235
theorem B1931215 : Blo 1929435 1931215 := bstep (se 1 (by rfl) ⟨1448411, by rfl⟩ : syracuseStep 1931215 = 2896823) B2896823
theorem B2896829 : Blo 1929435 2896829 := bbase (se 3 (by rfl) ⟨543155, by rfl⟩ : syracuseStep 2896829 = 1086311) (by norm_num)
theorem B1931219 : Blo 1929435 1931219 := bstep (se 1 (by rfl) ⟨1448414, by rfl⟩ : syracuseStep 1931219 = 2896829) B2896829
theorem B4345253 : Blo 1929435 4345253 := bbase (se 4 (by rfl) ⟨407367, by rfl⟩ : syracuseStep 4345253 = 814735) (by norm_num)
theorem B2896835 : Blo 1929435 2896835 := bstep (se 1 (by rfl) ⟨2172626, by rfl⟩ : syracuseStep 2896835 = 4345253) B4345253
theorem B1931223 : Blo 1929435 1931223 := bstep (se 1 (by rfl) ⟨1448417, by rfl⟩ : syracuseStep 1931223 = 2896835) B2896835
theorem B4888421 : Blo 1929435 4888421 := bbase (se 4 (by rfl) ⟨458289, by rfl⟩ : syracuseStep 4888421 = 916579) (by norm_num)
theorem B3258947 : Blo 1929435 3258947 := bstep (se 1 (by rfl) ⟨2444210, by rfl⟩ : syracuseStep 3258947 = 4888421) B4888421
theorem B2172631 : Blo 1929435 2172631 := bstep (se 1 (by rfl) ⟨1629473, by rfl⟩ : syracuseStep 2172631 = 3258947) B3258947
theorem B2896841 : Blo 1929435 2896841 := bstep (se 2 (by rfl) ⟨1086315, by rfl⟩ : syracuseStep 2896841 = 2172631) B2172631
theorem B1931227 : Blo 1929435 1931227 := bstep (se 1 (by rfl) ⟨1448420, by rfl⟩ : syracuseStep 1931227 = 2896841) B2896841
theorem B3093461 : Blo 1929435 3093461 := bbase (se 7 (by rfl) ⟨36251, by rfl⟩ : syracuseStep 3093461 = 72503) (by norm_num)
theorem B2062307 : Blo 1929435 2062307 := bstep (se 1 (by rfl) ⟨1546730, by rfl⟩ : syracuseStep 2062307 = 3093461) B3093461
theorem B5499485 : Blo 1929435 5499485 := bstep (se 3 (by rfl) ⟨1031153, by rfl⟩ : syracuseStep 5499485 = 2062307) B2062307
theorem B3666323 : Blo 1929435 3666323 := bstep (se 1 (by rfl) ⟨2749742, by rfl⟩ : syracuseStep 3666323 = 5499485) B5499485
theorem B9776861 : Blo 1929435 9776861 := bstep (se 3 (by rfl) ⟨1833161, by rfl⟩ : syracuseStep 9776861 = 3666323) B3666323
theorem B6517907 : Blo 1929435 6517907 := bstep (se 1 (by rfl) ⟨4888430, by rfl⟩ : syracuseStep 6517907 = 9776861) B9776861
theorem B4345271 : Blo 1929435 4345271 := bstep (se 1 (by rfl) ⟨3258953, by rfl⟩ : syracuseStep 4345271 = 6517907) B6517907
theorem B2896847 : Blo 1929435 2896847 := bstep (se 1 (by rfl) ⟨2172635, by rfl⟩ : syracuseStep 2896847 = 4345271) B4345271
theorem B1931231 : Blo 1929435 1931231 := bstep (se 1 (by rfl) ⟨1448423, by rfl⟩ : syracuseStep 1931231 = 2896847) B2896847
theorem B2896853 : Blo 1929435 2896853 := bbase (se 7 (by rfl) ⟨33947, by rfl⟩ : syracuseStep 2896853 = 67895) (by norm_num)
theorem B1931235 : Blo 1929435 1931235 := bstep (se 1 (by rfl) ⟨1448426, by rfl⟩ : syracuseStep 1931235 = 2896853) B2896853
theorem B7332677 : Blo 1929435 7332677 := bbase (se 4 (by rfl) ⟨687438, by rfl⟩ : syracuseStep 7332677 = 1374877) (by norm_num)
theorem B4888451 : Blo 1929435 4888451 := bstep (se 1 (by rfl) ⟨3666338, by rfl⟩ : syracuseStep 4888451 = 7332677) B7332677
theorem B3258967 : Blo 1929435 3258967 := bstep (se 1 (by rfl) ⟨2444225, by rfl⟩ : syracuseStep 3258967 = 4888451) B4888451
theorem B4345289 : Blo 1929435 4345289 := bstep (se 2 (by rfl) ⟨1629483, by rfl⟩ : syracuseStep 4345289 = 3258967) B3258967
theorem B2896859 : Blo 1929435 2896859 := bstep (se 1 (by rfl) ⟨2172644, by rfl⟩ : syracuseStep 2896859 = 4345289) B4345289
theorem B1931239 : Blo 1929435 1931239 := bstep (se 1 (by rfl) ⟨1448429, by rfl⟩ : syracuseStep 1931239 = 2896859) B2896859
theorem B2172649 : Blo 1929435 2172649 := bbase (se 2 (by rfl) ⟨814743, by rfl⟩ : syracuseStep 2172649 = 1629487) (by norm_num)
theorem B2896865 : Blo 1929435 2896865 := bstep (se 2 (by rfl) ⟨1086324, by rfl⟩ : syracuseStep 2896865 = 2172649) B2172649
theorem B1931243 : Blo 1929435 1931243 := bstep (se 1 (by rfl) ⟨1448432, by rfl⟩ : syracuseStep 1931243 = 2896865) B2896865
theorem B10999061 : Blo 1929435 10999061 := bbase (se 6 (by rfl) ⟨257790, by rfl⟩ : syracuseStep 10999061 = 515581) (by norm_num)
theorem B7332707 : Blo 1929435 7332707 := bstep (se 1 (by rfl) ⟨5499530, by rfl⟩ : syracuseStep 7332707 = 10999061) B10999061
theorem B4888471 : Blo 1929435 4888471 := bstep (se 1 (by rfl) ⟨3666353, by rfl⟩ : syracuseStep 4888471 = 7332707) B7332707
theorem B6517961 : Blo 1929435 6517961 := bstep (se 2 (by rfl) ⟨2444235, by rfl⟩ : syracuseStep 6517961 = 4888471) B4888471
theorem B4345307 : Blo 1929435 4345307 := bstep (se 1 (by rfl) ⟨3258980, by rfl⟩ : syracuseStep 4345307 = 6517961) B6517961
theorem B2896871 : Blo 1929435 2896871 := bstep (se 1 (by rfl) ⟨2172653, by rfl⟩ : syracuseStep 2896871 = 4345307) B4345307
theorem B1931247 : Blo 1929435 1931247 := bstep (se 1 (by rfl) ⟨1448435, by rfl⟩ : syracuseStep 1931247 = 2896871) B2896871
theorem B2896877 : Blo 1929435 2896877 := bbase (se 3 (by rfl) ⟨543164, by rfl⟩ : syracuseStep 2896877 = 1086329) (by norm_num)
theorem B1931251 : Blo 1929435 1931251 := bstep (se 1 (by rfl) ⟨1448438, by rfl⟩ : syracuseStep 1931251 = 2896877) B2896877
theorem B4345325 : Blo 1929435 4345325 := bbase (se 3 (by rfl) ⟨814748, by rfl⟩ : syracuseStep 4345325 = 1629497) (by norm_num)
theorem B2896883 : Blo 1929435 2896883 := bstep (se 1 (by rfl) ⟨2172662, by rfl⟩ : syracuseStep 2896883 = 4345325) B4345325
theorem B1931255 : Blo 1929435 1931255 := bstep (se 1 (by rfl) ⟨1448441, by rfl⟩ : syracuseStep 1931255 = 2896883) B2896883
theorem B6187013 : Blo 1929435 6187013 := bbase (se 4 (by rfl) ⟨580032, by rfl⟩ : syracuseStep 6187013 = 1160065) (by norm_num)
theorem B4124675 : Blo 1929435 4124675 := bstep (se 1 (by rfl) ⟨3093506, by rfl⟩ : syracuseStep 4124675 = 6187013) B6187013
theorem B2749783 : Blo 1929435 2749783 := bstep (se 1 (by rfl) ⟨2062337, by rfl⟩ : syracuseStep 2749783 = 4124675) B4124675
theorem B3666377 : Blo 1929435 3666377 := bstep (se 2 (by rfl) ⟨1374891, by rfl⟩ : syracuseStep 3666377 = 2749783) B2749783
theorem B2444251 : Blo 1929435 2444251 := bstep (se 1 (by rfl) ⟨1833188, by rfl⟩ : syracuseStep 2444251 = 3666377) B3666377
theorem B3259001 : Blo 1929435 3259001 := bstep (se 2 (by rfl) ⟨1222125, by rfl⟩ : syracuseStep 3259001 = 2444251) B2444251
theorem B2172667 : Blo 1929435 2172667 := bstep (se 1 (by rfl) ⟨1629500, by rfl⟩ : syracuseStep 2172667 = 3259001) B3259001
theorem B2896889 : Blo 1929435 2896889 := bstep (se 2 (by rfl) ⟨1086333, by rfl⟩ : syracuseStep 2896889 = 2172667) B2172667
theorem B1931259 : Blo 1929435 1931259 := bstep (se 1 (by rfl) ⟨1448444, by rfl⟩ : syracuseStep 1931259 = 2896889) B2896889
theorem B4404629 : Blo 1929435 4404629 := bbase (se 6 (by rfl) ⟨103233, by rfl⟩ : syracuseStep 4404629 = 206467) (by norm_num)
theorem B11745677 : Blo 1929435 11745677 := bstep (se 3 (by rfl) ⟨2202314, by rfl⟩ : syracuseStep 11745677 = 4404629) B4404629
theorem B7830451 : Blo 1929435 7830451 := bstep (se 1 (by rfl) ⟨5872838, by rfl⟩ : syracuseStep 7830451 = 11745677) B11745677
theorem B41762405 : Blo 1929435 41762405 := bstep (se 4 (by rfl) ⟨3915225, by rfl⟩ : syracuseStep 41762405 = 7830451) B7830451
theorem B111366413 : Blo 1929435 111366413 := bstep (se 3 (by rfl) ⟨20881202, by rfl⟩ : syracuseStep 111366413 = 41762405) B41762405
theorem B74244275 : Blo 1929435 74244275 := bstep (se 1 (by rfl) ⟨55683206, by rfl⟩ : syracuseStep 74244275 = 111366413) B111366413
theorem B49496183 : Blo 1929435 49496183 := bstep (se 1 (by rfl) ⟨37122137, by rfl⟩ : syracuseStep 49496183 = 74244275) B74244275
theorem B32997455 : Blo 1929435 32997455 := bstep (se 1 (by rfl) ⟨24748091, by rfl⟩ : syracuseStep 32997455 = 49496183) B49496183
theorem B21998303 : Blo 1929435 21998303 := bstep (se 1 (by rfl) ⟨16498727, by rfl⟩ : syracuseStep 21998303 = 32997455) B32997455
theorem B14665535 : Blo 1929435 14665535 := bstep (se 1 (by rfl) ⟨10999151, by rfl⟩ : syracuseStep 14665535 = 21998303) B21998303
theorem B9777023 : Blo 1929435 9777023 := bstep (se 1 (by rfl) ⟨7332767, by rfl⟩ : syracuseStep 9777023 = 14665535) B14665535
theorem B6518015 : Blo 1929435 6518015 := bstep (se 1 (by rfl) ⟨4888511, by rfl⟩ : syracuseStep 6518015 = 9777023) B9777023
theorem B4345343 : Blo 1929435 4345343 := bstep (se 1 (by rfl) ⟨3259007, by rfl⟩ : syracuseStep 4345343 = 6518015) B6518015
theorem B2896895 : Blo 1929435 2896895 := bstep (se 1 (by rfl) ⟨2172671, by rfl⟩ : syracuseStep 2896895 = 4345343) B4345343
theorem B1931263 : Blo 1929435 1931263 := bstep (se 1 (by rfl) ⟨1448447, by rfl⟩ : syracuseStep 1931263 = 2896895) B2896895
theorem B2896901 : Blo 1929435 2896901 := bbase (se 4 (by rfl) ⟨271584, by rfl⟩ : syracuseStep 2896901 = 543169) (by norm_num)
theorem B1931267 : Blo 1929435 1931267 := bstep (se 1 (by rfl) ⟨1448450, by rfl⟩ : syracuseStep 1931267 = 2896901) B2896901
theorem B3259021 : Blo 1929435 3259021 := bbase (se 3 (by rfl) ⟨611066, by rfl⟩ : syracuseStep 3259021 = 1222133) (by norm_num)
theorem B4345361 : Blo 1929435 4345361 := bstep (se 2 (by rfl) ⟨1629510, by rfl⟩ : syracuseStep 4345361 = 3259021) B3259021
theorem B2896907 : Blo 1929435 2896907 := bstep (se 1 (by rfl) ⟨2172680, by rfl⟩ : syracuseStep 2896907 = 4345361) B4345361
theorem B1931271 : Blo 1929435 1931271 := bstep (se 1 (by rfl) ⟨1448453, by rfl⟩ : syracuseStep 1931271 = 2896907) B2896907
theorem B2172685 : Blo 1929435 2172685 := bbase (se 3 (by rfl) ⟨407378, by rfl⟩ : syracuseStep 2172685 = 814757) (by norm_num)
theorem B2896913 : Blo 1929435 2896913 := bstep (se 2 (by rfl) ⟨1086342, by rfl⟩ : syracuseStep 2896913 = 2172685) B2172685
theorem B1931275 : Blo 1929435 1931275 := bstep (se 1 (by rfl) ⟨1448456, by rfl⟩ : syracuseStep 1931275 = 2896913) B2896913
theorem B6518069 : Blo 1929435 6518069 := bbase (se 5 (by rfl) ⟨305534, by rfl⟩ : syracuseStep 6518069 = 611069) (by norm_num)
theorem B4345379 : Blo 1929435 4345379 := bstep (se 1 (by rfl) ⟨3259034, by rfl⟩ : syracuseStep 4345379 = 6518069) B6518069
theorem B2896919 : Blo 1929435 2896919 := bstep (se 1 (by rfl) ⟨2172689, by rfl⟩ : syracuseStep 2896919 = 4345379) B4345379
theorem B1931279 : Blo 1929435 1931279 := bstep (se 1 (by rfl) ⟨1448459, by rfl⟩ : syracuseStep 1931279 = 2896919) B2896919
theorem B2896925 : Blo 1929435 2896925 := bbase (se 3 (by rfl) ⟨543173, by rfl⟩ : syracuseStep 2896925 = 1086347) (by norm_num)
theorem B1931283 : Blo 1929435 1931283 := bstep (se 1 (by rfl) ⟨1448462, by rfl⟩ : syracuseStep 1931283 = 2896925) B2896925
theorem B4345397 : Blo 1929435 4345397 := bbase (se 5 (by rfl) ⟨203690, by rfl⟩ : syracuseStep 4345397 = 407381) (by norm_num)
theorem B2896931 : Blo 1929435 2896931 := bstep (se 1 (by rfl) ⟨2172698, by rfl⟩ : syracuseStep 2896931 = 4345397) B4345397
theorem B1931287 : Blo 1929435 1931287 := bstep (se 1 (by rfl) ⟨1448465, by rfl⟩ : syracuseStep 1931287 = 2896931) B2896931
theorem B3093557 : Blo 1929435 3093557 := bbase (se 5 (by rfl) ⟨145010, by rfl⟩ : syracuseStep 3093557 = 290021) (by norm_num)
theorem B8249485 : Blo 1929435 8249485 := bstep (se 3 (by rfl) ⟨1546778, by rfl⟩ : syracuseStep 8249485 = 3093557) B3093557
theorem B10999313 : Blo 1929435 10999313 := bstep (se 2 (by rfl) ⟨4124742, by rfl⟩ : syracuseStep 10999313 = 8249485) B8249485
theorem B7332875 : Blo 1929435 7332875 := bstep (se 1 (by rfl) ⟨5499656, by rfl⟩ : syracuseStep 7332875 = 10999313) B10999313
theorem B4888583 : Blo 1929435 4888583 := bstep (se 1 (by rfl) ⟨3666437, by rfl⟩ : syracuseStep 4888583 = 7332875) B7332875
theorem B3259055 : Blo 1929435 3259055 := bstep (se 1 (by rfl) ⟨2444291, by rfl⟩ : syracuseStep 3259055 = 4888583) B4888583
theorem B2172703 : Blo 1929435 2172703 := bstep (se 1 (by rfl) ⟨1629527, by rfl⟩ : syracuseStep 2172703 = 3259055) B3259055
theorem B2896937 : Blo 1929435 2896937 := bstep (se 2 (by rfl) ⟨1086351, by rfl⟩ : syracuseStep 2896937 = 2172703) B2172703
theorem B1931291 : Blo 1929435 1931291 := bstep (se 1 (by rfl) ⟨1448468, by rfl⟩ : syracuseStep 1931291 = 2896937) B2896937
theorem B5220389 : Blo 1929435 5220389 := bbase (se 4 (by rfl) ⟨489411, by rfl⟩ : syracuseStep 5220389 = 978823) (by norm_num)
theorem B3480259 : Blo 1929435 3480259 := bstep (se 1 (by rfl) ⟨2610194, by rfl⟩ : syracuseStep 3480259 = 5220389) B5220389
theorem B4640345 : Blo 1929435 4640345 := bstep (se 2 (by rfl) ⟨1740129, by rfl⟩ : syracuseStep 4640345 = 3480259) B3480259
theorem B3093563 : Blo 1929435 3093563 := bstep (se 1 (by rfl) ⟨2320172, by rfl⟩ : syracuseStep 3093563 = 4640345) B4640345
theorem B8249501 : Blo 1929435 8249501 := bstep (se 3 (by rfl) ⟨1546781, by rfl⟩ : syracuseStep 8249501 = 3093563) B3093563
theorem B5499667 : Blo 1929435 5499667 := bstep (se 1 (by rfl) ⟨4124750, by rfl⟩ : syracuseStep 5499667 = 8249501) B8249501
theorem B7332889 : Blo 1929435 7332889 := bstep (se 2 (by rfl) ⟨2749833, by rfl⟩ : syracuseStep 7332889 = 5499667) B5499667
theorem B9777185 : Blo 1929435 9777185 := bstep (se 2 (by rfl) ⟨3666444, by rfl⟩ : syracuseStep 9777185 = 7332889) B7332889
theorem B6518123 : Blo 1929435 6518123 := bstep (se 1 (by rfl) ⟨4888592, by rfl⟩ : syracuseStep 6518123 = 9777185) B9777185
theorem B4345415 : Blo 1929435 4345415 := bstep (se 1 (by rfl) ⟨3259061, by rfl⟩ : syracuseStep 4345415 = 6518123) B6518123
theorem B2896943 : Blo 1929435 2896943 := bstep (se 1 (by rfl) ⟨2172707, by rfl⟩ : syracuseStep 2896943 = 4345415) B4345415
theorem B1931295 : Blo 1929435 1931295 := bstep (se 1 (by rfl) ⟨1448471, by rfl⟩ : syracuseStep 1931295 = 2896943) B2896943
theorem B2896949 : Blo 1929435 2896949 := bbase (se 5 (by rfl) ⟨135794, by rfl⟩ : syracuseStep 2896949 = 271589) (by norm_num)
theorem B1931299 : Blo 1929435 1931299 := bstep (se 1 (by rfl) ⟨1448474, by rfl⟩ : syracuseStep 1931299 = 2896949) B2896949
theorem B4888613 : Blo 1929435 4888613 := bbase (se 4 (by rfl) ⟨458307, by rfl⟩ : syracuseStep 4888613 = 916615) (by norm_num)
theorem B3259075 : Blo 1929435 3259075 := bstep (se 1 (by rfl) ⟨2444306, by rfl⟩ : syracuseStep 3259075 = 4888613) B4888613
theorem B4345433 : Blo 1929435 4345433 := bstep (se 2 (by rfl) ⟨1629537, by rfl⟩ : syracuseStep 4345433 = 3259075) B3259075
theorem B2896955 : Blo 1929435 2896955 := bstep (se 1 (by rfl) ⟨2172716, by rfl⟩ : syracuseStep 2896955 = 4345433) B4345433
theorem B1931303 : Blo 1929435 1931303 := bstep (se 1 (by rfl) ⟨1448477, by rfl⟩ : syracuseStep 1931303 = 2896955) B2896955
theorem B2172721 : Blo 1929435 2172721 := bbase (se 2 (by rfl) ⟨814770, by rfl⟩ : syracuseStep 2172721 = 1629541) (by norm_num)
theorem B2896961 : Blo 1929435 2896961 := bstep (se 2 (by rfl) ⟨1086360, by rfl⟩ : syracuseStep 2896961 = 2172721) B2172721
theorem B1931307 : Blo 1929435 1931307 := bstep (se 1 (by rfl) ⟨1448480, by rfl⟩ : syracuseStep 1931307 = 2896961) B2896961
theorem B3093589 : Blo 1929435 3093589 := bbase (se 8 (by rfl) ⟨18126, by rfl⟩ : syracuseStep 3093589 = 36253) (by norm_num)
theorem B4124785 : Blo 1929435 4124785 := bstep (se 2 (by rfl) ⟨1546794, by rfl⟩ : syracuseStep 4124785 = 3093589) B3093589
theorem B5499713 : Blo 1929435 5499713 := bstep (se 2 (by rfl) ⟨2062392, by rfl⟩ : syracuseStep 5499713 = 4124785) B4124785
theorem B3666475 : Blo 1929435 3666475 := bstep (se 1 (by rfl) ⟨2749856, by rfl⟩ : syracuseStep 3666475 = 5499713) B5499713
theorem B4888633 : Blo 1929435 4888633 := bstep (se 2 (by rfl) ⟨1833237, by rfl⟩ : syracuseStep 4888633 = 3666475) B3666475
theorem B6518177 : Blo 1929435 6518177 := bstep (se 2 (by rfl) ⟨2444316, by rfl⟩ : syracuseStep 6518177 = 4888633) B4888633
theorem B4345451 : Blo 1929435 4345451 := bstep (se 1 (by rfl) ⟨3259088, by rfl⟩ : syracuseStep 4345451 = 6518177) B6518177
theorem B2896967 : Blo 1929435 2896967 := bstep (se 1 (by rfl) ⟨2172725, by rfl⟩ : syracuseStep 2896967 = 4345451) B4345451
theorem B1931311 : Blo 1929435 1931311 := bstep (se 1 (by rfl) ⟨1448483, by rfl⟩ : syracuseStep 1931311 = 2896967) B2896967
theorem B2896973 : Blo 1929435 2896973 := bbase (se 3 (by rfl) ⟨543182, by rfl⟩ : syracuseStep 2896973 = 1086365) (by norm_num)
theorem B1931315 : Blo 1929435 1931315 := bstep (se 1 (by rfl) ⟨1448486, by rfl⟩ : syracuseStep 1931315 = 2896973) B2896973
theorem B4345469 : Blo 1929435 4345469 := bbase (se 3 (by rfl) ⟨814775, by rfl⟩ : syracuseStep 4345469 = 1629551) (by norm_num)
theorem B2896979 : Blo 1929435 2896979 := bstep (se 1 (by rfl) ⟨2172734, by rfl⟩ : syracuseStep 2896979 = 4345469) B4345469
theorem B1931319 : Blo 1929435 1931319 := bstep (se 1 (by rfl) ⟨1448489, by rfl⟩ : syracuseStep 1931319 = 2896979) B2896979
theorem B3259109 : Blo 1929435 3259109 := bbase (se 4 (by rfl) ⟨305541, by rfl⟩ : syracuseStep 3259109 = 611083) (by norm_num)
theorem B2172739 : Blo 1929435 2172739 := bstep (se 1 (by rfl) ⟨1629554, by rfl⟩ : syracuseStep 2172739 = 3259109) B3259109
theorem B2896985 : Blo 1929435 2896985 := bstep (se 2 (by rfl) ⟨1086369, by rfl⟩ : syracuseStep 2896985 = 2172739) B2172739
theorem B1931323 : Blo 1929435 1931323 := bstep (se 1 (by rfl) ⟨1448492, by rfl⟩ : syracuseStep 1931323 = 2896985) B2896985
theorem B3480317 : Blo 1929435 3480317 := bbase (se 3 (by rfl) ⟨652559, by rfl⟩ : syracuseStep 3480317 = 1305119) (by norm_num)
theorem B2320211 : Blo 1929435 2320211 := bstep (se 1 (by rfl) ⟨1740158, by rfl⟩ : syracuseStep 2320211 = 3480317) B3480317
theorem B6187229 : Blo 1929435 6187229 := bstep (se 3 (by rfl) ⟨1160105, by rfl⟩ : syracuseStep 6187229 = 2320211) B2320211
theorem B4124819 : Blo 1929435 4124819 := bstep (se 1 (by rfl) ⟨3093614, by rfl⟩ : syracuseStep 4124819 = 6187229) B6187229
theorem B2749879 : Blo 1929435 2749879 := bstep (se 1 (by rfl) ⟨2062409, by rfl⟩ : syracuseStep 2749879 = 4124819) B4124819
theorem B14666021 : Blo 1929435 14666021 := bstep (se 4 (by rfl) ⟨1374939, by rfl⟩ : syracuseStep 14666021 = 2749879) B2749879
theorem B9777347 : Blo 1929435 9777347 := bstep (se 1 (by rfl) ⟨7333010, by rfl⟩ : syracuseStep 9777347 = 14666021) B14666021
theorem B6518231 : Blo 1929435 6518231 := bstep (se 1 (by rfl) ⟨4888673, by rfl⟩ : syracuseStep 6518231 = 9777347) B9777347
theorem B4345487 : Blo 1929435 4345487 := bstep (se 1 (by rfl) ⟨3259115, by rfl⟩ : syracuseStep 4345487 = 6518231) B6518231
theorem B2896991 : Blo 1929435 2896991 := bstep (se 1 (by rfl) ⟨2172743, by rfl⟩ : syracuseStep 2896991 = 4345487) B4345487
theorem B1931327 : Blo 1929435 1931327 := bstep (se 1 (by rfl) ⟨1448495, by rfl⟩ : syracuseStep 1931327 = 2896991) B2896991
theorem B2896997 : Blo 1929435 2896997 := bbase (se 4 (by rfl) ⟨271593, by rfl⟩ : syracuseStep 2896997 = 543187) (by norm_num)
theorem B1931331 : Blo 1929435 1931331 := bstep (se 1 (by rfl) ⟨1448498, by rfl⟩ : syracuseStep 1931331 = 2896997) B2896997
theorem B4124837 : Blo 1929435 4124837 := bbase (se 4 (by rfl) ⟨386703, by rfl⟩ : syracuseStep 4124837 = 773407) (by norm_num)
theorem B2749891 : Blo 1929435 2749891 := bstep (se 1 (by rfl) ⟨2062418, by rfl⟩ : syracuseStep 2749891 = 4124837) B4124837
theorem B3666521 : Blo 1929435 3666521 := bstep (se 2 (by rfl) ⟨1374945, by rfl⟩ : syracuseStep 3666521 = 2749891) B2749891
theorem B2444347 : Blo 1929435 2444347 := bstep (se 1 (by rfl) ⟨1833260, by rfl⟩ : syracuseStep 2444347 = 3666521) B3666521
theorem B3259129 : Blo 1929435 3259129 := bstep (se 2 (by rfl) ⟨1222173, by rfl⟩ : syracuseStep 3259129 = 2444347) B2444347
theorem B4345505 : Blo 1929435 4345505 := bstep (se 2 (by rfl) ⟨1629564, by rfl⟩ : syracuseStep 4345505 = 3259129) B3259129
theorem B2897003 : Blo 1929435 2897003 := bstep (se 1 (by rfl) ⟨2172752, by rfl⟩ : syracuseStep 2897003 = 4345505) B4345505
theorem B1931335 : Blo 1929435 1931335 := bstep (se 1 (by rfl) ⟨1448501, by rfl⟩ : syracuseStep 1931335 = 2897003) B2897003
theorem B2172757 : Blo 1929435 2172757 := bbase (se 9 (by rfl) ⟨6365, by rfl⟩ : syracuseStep 2172757 = 12731) (by norm_num)
theorem B2897009 : Blo 1929435 2897009 := bstep (se 2 (by rfl) ⟨1086378, by rfl⟩ : syracuseStep 2897009 = 2172757) B2172757
theorem B1931339 : Blo 1929435 1931339 := bstep (se 1 (by rfl) ⟨1448504, by rfl⟩ : syracuseStep 1931339 = 2897009) B2897009
theorem B2444357 : Blo 1929435 2444357 := bbase (se 4 (by rfl) ⟨229158, by rfl⟩ : syracuseStep 2444357 = 458317) (by norm_num)
theorem B6518285 : Blo 1929435 6518285 := bstep (se 3 (by rfl) ⟨1222178, by rfl⟩ : syracuseStep 6518285 = 2444357) B2444357
theorem B4345523 : Blo 1929435 4345523 := bstep (se 1 (by rfl) ⟨3259142, by rfl⟩ : syracuseStep 4345523 = 6518285) B6518285
theorem B2897015 : Blo 1929435 2897015 := bstep (se 1 (by rfl) ⟨2172761, by rfl⟩ : syracuseStep 2897015 = 4345523) B4345523
theorem B1931343 : Blo 1929435 1931343 := bstep (se 1 (by rfl) ⟨1448507, by rfl⟩ : syracuseStep 1931343 = 2897015) B2897015
theorem B2897021 : Blo 1929435 2897021 := bbase (se 3 (by rfl) ⟨543191, by rfl⟩ : syracuseStep 2897021 = 1086383) (by norm_num)
theorem B1931347 : Blo 1929435 1931347 := bstep (se 1 (by rfl) ⟨1448510, by rfl⟩ : syracuseStep 1931347 = 2897021) B2897021
theorem B4345541 : Blo 1929435 4345541 := bbase (se 4 (by rfl) ⟨407394, by rfl⟩ : syracuseStep 4345541 = 814789) (by norm_num)
theorem B2897027 : Blo 1929435 2897027 := bstep (se 1 (by rfl) ⟨2172770, by rfl⟩ : syracuseStep 2897027 = 4345541) B4345541
theorem B1931351 : Blo 1929435 1931351 := bstep (se 1 (by rfl) ⟨1448513, by rfl⟩ : syracuseStep 1931351 = 2897027) B2897027
theorem B19821781 : Blo 1929435 19821781 := bbase (se 7 (by rfl) ⟨232286, by rfl⟩ : syracuseStep 19821781 = 464573) (by norm_num)
theorem B26429041 : Blo 1929435 26429041 := bstep (se 2 (by rfl) ⟨9910890, by rfl⟩ : syracuseStep 26429041 = 19821781) B19821781
theorem B35238721 : Blo 1929435 35238721 := bstep (se 2 (by rfl) ⟨13214520, by rfl⟩ : syracuseStep 35238721 = 26429041) B26429041
theorem B46984961 : Blo 1929435 46984961 := bstep (se 2 (by rfl) ⟨17619360, by rfl⟩ : syracuseStep 46984961 = 35238721) B35238721
theorem B31323307 : Blo 1929435 31323307 := bstep (se 1 (by rfl) ⟨23492480, by rfl⟩ : syracuseStep 31323307 = 46984961) B46984961
theorem B41764409 : Blo 1929435 41764409 := bstep (se 2 (by rfl) ⟨15661653, by rfl⟩ : syracuseStep 41764409 = 31323307) B31323307
theorem B27842939 : Blo 1929435 27842939 := bstep (se 1 (by rfl) ⟨20882204, by rfl⟩ : syracuseStep 27842939 = 41764409) B41764409
theorem B18561959 : Blo 1929435 18561959 := bstep (se 1 (by rfl) ⟨13921469, by rfl⟩ : syracuseStep 18561959 = 27842939) B27842939
theorem B12374639 : Blo 1929435 12374639 := bstep (se 1 (by rfl) ⟨9280979, by rfl⟩ : syracuseStep 12374639 = 18561959) B18561959
theorem B8249759 : Blo 1929435 8249759 := bstep (se 1 (by rfl) ⟨6187319, by rfl⟩ : syracuseStep 8249759 = 12374639) B12374639
theorem B5499839 : Blo 1929435 5499839 := bstep (se 1 (by rfl) ⟨4124879, by rfl⟩ : syracuseStep 5499839 = 8249759) B8249759
theorem B3666559 : Blo 1929435 3666559 := bstep (se 1 (by rfl) ⟨2749919, by rfl⟩ : syracuseStep 3666559 = 5499839) B5499839
theorem B4888745 : Blo 1929435 4888745 := bstep (se 2 (by rfl) ⟨1833279, by rfl⟩ : syracuseStep 4888745 = 3666559) B3666559
theorem B3259163 : Blo 1929435 3259163 := bstep (se 1 (by rfl) ⟨2444372, by rfl⟩ : syracuseStep 3259163 = 4888745) B4888745
theorem B2172775 : Blo 1929435 2172775 := bstep (se 1 (by rfl) ⟨1629581, by rfl⟩ : syracuseStep 2172775 = 3259163) B3259163
theorem B2897033 : Blo 1929435 2897033 := bstep (se 2 (by rfl) ⟨1086387, by rfl⟩ : syracuseStep 2897033 = 2172775) B2172775
theorem B1931355 : Blo 1929435 1931355 := bstep (se 1 (by rfl) ⟨1448516, by rfl⟩ : syracuseStep 1931355 = 2897033) B2897033
theorem B9777509 : Blo 1929435 9777509 := bbase (se 4 (by rfl) ⟨916641, by rfl⟩ : syracuseStep 9777509 = 1833283) (by norm_num)
theorem B6518339 : Blo 1929435 6518339 := bstep (se 1 (by rfl) ⟨4888754, by rfl⟩ : syracuseStep 6518339 = 9777509) B9777509
theorem B4345559 : Blo 1929435 4345559 := bstep (se 1 (by rfl) ⟨3259169, by rfl⟩ : syracuseStep 4345559 = 6518339) B6518339
theorem B2897039 : Blo 1929435 2897039 := bstep (se 1 (by rfl) ⟨2172779, by rfl⟩ : syracuseStep 2897039 = 4345559) B4345559
theorem B1931359 : Blo 1929435 1931359 := bstep (se 1 (by rfl) ⟨1448519, by rfl⟩ : syracuseStep 1931359 = 2897039) B2897039
theorem B2897045 : Blo 1929435 2897045 := bbase (se 6 (by rfl) ⟨67899, by rfl⟩ : syracuseStep 2897045 = 135799) (by norm_num)
theorem B1931363 : Blo 1929435 1931363 := bstep (se 1 (by rfl) ⟨1448522, by rfl⟩ : syracuseStep 1931363 = 2897045) B2897045
theorem B3480389 : Blo 1929435 3480389 := bbase (se 4 (by rfl) ⟨326286, by rfl⟩ : syracuseStep 3480389 = 652573) (by norm_num)
theorem B2320259 : Blo 1929435 2320259 := bstep (se 1 (by rfl) ⟨1740194, by rfl⟩ : syracuseStep 2320259 = 3480389) B3480389
theorem B6187357 : Blo 1929435 6187357 := bstep (se 3 (by rfl) ⟨1160129, by rfl⟩ : syracuseStep 6187357 = 2320259) B2320259
theorem B8249809 : Blo 1929435 8249809 := bstep (se 2 (by rfl) ⟨3093678, by rfl⟩ : syracuseStep 8249809 = 6187357) B6187357
theorem B10999745 : Blo 1929435 10999745 := bstep (se 2 (by rfl) ⟨4124904, by rfl⟩ : syracuseStep 10999745 = 8249809) B8249809
theorem B7333163 : Blo 1929435 7333163 := bstep (se 1 (by rfl) ⟨5499872, by rfl⟩ : syracuseStep 7333163 = 10999745) B10999745
theorem B4888775 : Blo 1929435 4888775 := bstep (se 1 (by rfl) ⟨3666581, by rfl⟩ : syracuseStep 4888775 = 7333163) B7333163
theorem B3259183 : Blo 1929435 3259183 := bstep (se 1 (by rfl) ⟨2444387, by rfl⟩ : syracuseStep 3259183 = 4888775) B4888775
theorem B4345577 : Blo 1929435 4345577 := bstep (se 2 (by rfl) ⟨1629591, by rfl⟩ : syracuseStep 4345577 = 3259183) B3259183
theorem B2897051 : Blo 1929435 2897051 := bstep (se 1 (by rfl) ⟨2172788, by rfl⟩ : syracuseStep 2897051 = 4345577) B4345577
theorem B1931367 : Blo 1929435 1931367 := bstep (se 1 (by rfl) ⟨1448525, by rfl⟩ : syracuseStep 1931367 = 2897051) B2897051
theorem B2172793 : Blo 1929435 2172793 := bbase (se 2 (by rfl) ⟨814797, by rfl⟩ : syracuseStep 2172793 = 1629595) (by norm_num)
theorem B2897057 : Blo 1929435 2897057 := bstep (se 2 (by rfl) ⟨1086396, by rfl⟩ : syracuseStep 2897057 = 2172793) B2172793
theorem B1931371 : Blo 1929435 1931371 := bstep (se 1 (by rfl) ⟨1448528, by rfl⟩ : syracuseStep 1931371 = 2897057) B2897057
theorem B9910997 : Blo 1929435 9910997 := bbase (se 7 (by rfl) ⟨116144, by rfl⟩ : syracuseStep 9910997 = 232289) (by norm_num)
theorem B6607331 : Blo 1929435 6607331 := bstep (se 1 (by rfl) ⟨4955498, by rfl⟩ : syracuseStep 6607331 = 9910997) B9910997
theorem B4404887 : Blo 1929435 4404887 := bstep (se 1 (by rfl) ⟨3303665, by rfl⟩ : syracuseStep 4404887 = 6607331) B6607331
theorem B2936591 : Blo 1929435 2936591 := bstep (se 1 (by rfl) ⟨2202443, by rfl⟩ : syracuseStep 2936591 = 4404887) B4404887
theorem B1957727 : Blo 1929435 1957727 := bstep (se 1 (by rfl) ⟨1468295, by rfl⟩ : syracuseStep 1957727 = 2936591) B2936591
theorem B5220605 : Blo 1929435 5220605 := bstep (se 3 (by rfl) ⟨978863, by rfl⟩ : syracuseStep 5220605 = 1957727) B1957727
theorem B3480403 : Blo 1929435 3480403 := bstep (se 1 (by rfl) ⟨2610302, by rfl⟩ : syracuseStep 3480403 = 5220605) B5220605
theorem B4640537 : Blo 1929435 4640537 := bstep (se 2 (by rfl) ⟨1740201, by rfl⟩ : syracuseStep 4640537 = 3480403) B3480403
theorem B12374765 : Blo 1929435 12374765 := bstep (se 3 (by rfl) ⟨2320268, by rfl⟩ : syracuseStep 12374765 = 4640537) B4640537
theorem B8249843 : Blo 1929435 8249843 := bstep (se 1 (by rfl) ⟨6187382, by rfl⟩ : syracuseStep 8249843 = 12374765) B12374765
theorem B5499895 : Blo 1929435 5499895 := bstep (se 1 (by rfl) ⟨4124921, by rfl⟩ : syracuseStep 5499895 = 8249843) B8249843
theorem B7333193 : Blo 1929435 7333193 := bstep (se 2 (by rfl) ⟨2749947, by rfl⟩ : syracuseStep 7333193 = 5499895) B5499895
theorem B4888795 : Blo 1929435 4888795 := bstep (se 1 (by rfl) ⟨3666596, by rfl⟩ : syracuseStep 4888795 = 7333193) B7333193
theorem B6518393 : Blo 1929435 6518393 := bstep (se 2 (by rfl) ⟨2444397, by rfl⟩ : syracuseStep 6518393 = 4888795) B4888795
theorem B4345595 : Blo 1929435 4345595 := bstep (se 1 (by rfl) ⟨3259196, by rfl⟩ : syracuseStep 4345595 = 6518393) B6518393
theorem B2897063 : Blo 1929435 2897063 := bstep (se 1 (by rfl) ⟨2172797, by rfl⟩ : syracuseStep 2897063 = 4345595) B4345595
theorem B1931375 : Blo 1929435 1931375 := bstep (se 1 (by rfl) ⟨1448531, by rfl⟩ : syracuseStep 1931375 = 2897063) B2897063
theorem B2897069 : Blo 1929435 2897069 := bbase (se 3 (by rfl) ⟨543200, by rfl⟩ : syracuseStep 2897069 = 1086401) (by norm_num)
theorem B1931379 : Blo 1929435 1931379 := bstep (se 1 (by rfl) ⟨1448534, by rfl⟩ : syracuseStep 1931379 = 2897069) B2897069
theorem B4345613 : Blo 1929435 4345613 := bbase (se 3 (by rfl) ⟨814802, by rfl⟩ : syracuseStep 4345613 = 1629605) (by norm_num)
theorem B2897075 : Blo 1929435 2897075 := bstep (se 1 (by rfl) ⟨2172806, by rfl⟩ : syracuseStep 2897075 = 4345613) B4345613
theorem B1931383 : Blo 1929435 1931383 := bstep (se 1 (by rfl) ⟨1448537, by rfl⟩ : syracuseStep 1931383 = 2897075) B2897075
theorem B2444413 : Blo 1929435 2444413 := bbase (se 3 (by rfl) ⟨458327, by rfl⟩ : syracuseStep 2444413 = 916655) (by norm_num)
theorem B3259217 : Blo 1929435 3259217 := bstep (se 2 (by rfl) ⟨1222206, by rfl⟩ : syracuseStep 3259217 = 2444413) B2444413
theorem B2172811 : Blo 1929435 2172811 := bstep (se 1 (by rfl) ⟨1629608, by rfl⟩ : syracuseStep 2172811 = 3259217) B3259217
theorem B2897081 : Blo 1929435 2897081 := bstep (se 2 (by rfl) ⟨1086405, by rfl⟩ : syracuseStep 2897081 = 2172811) B2172811
theorem B1931387 : Blo 1929435 1931387 := bstep (se 1 (by rfl) ⟨1448540, by rfl⟩ : syracuseStep 1931387 = 2897081) B2897081
theorem B3716653 : Blo 1929435 3716653 := bbase (se 3 (by rfl) ⟨696872, by rfl⟩ : syracuseStep 3716653 = 1393745) (by norm_num)
theorem B4955537 : Blo 1929435 4955537 := bstep (se 2 (by rfl) ⟨1858326, by rfl⟩ : syracuseStep 4955537 = 3716653) B3716653
theorem B13214765 : Blo 1929435 13214765 := bstep (se 3 (by rfl) ⟨2477768, by rfl⟩ : syracuseStep 13214765 = 4955537) B4955537
theorem B35239373 : Blo 1929435 35239373 := bstep (se 3 (by rfl) ⟨6607382, by rfl⟩ : syracuseStep 35239373 = 13214765) B13214765
theorem B23492915 : Blo 1929435 23492915 := bstep (se 1 (by rfl) ⟨17619686, by rfl⟩ : syracuseStep 23492915 = 35239373) B35239373
theorem B15661943 : Blo 1929435 15661943 := bstep (se 1 (by rfl) ⟨11746457, by rfl⟩ : syracuseStep 15661943 = 23492915) B23492915
theorem B10441295 : Blo 1929435 10441295 := bstep (se 1 (by rfl) ⟨7830971, by rfl⟩ : syracuseStep 10441295 = 15661943) B15661943
theorem B6960863 : Blo 1929435 6960863 := bstep (se 1 (by rfl) ⟨5220647, by rfl⟩ : syracuseStep 6960863 = 10441295) B10441295
theorem B4640575 : Blo 1929435 4640575 := bstep (se 1 (by rfl) ⟨3480431, by rfl⟩ : syracuseStep 4640575 = 6960863) B6960863
theorem B6187433 : Blo 1929435 6187433 := bstep (se 2 (by rfl) ⟨2320287, by rfl⟩ : syracuseStep 6187433 = 4640575) B4640575
theorem B16499821 : Blo 1929435 16499821 := bstep (se 3 (by rfl) ⟨3093716, by rfl⟩ : syracuseStep 16499821 = 6187433) B6187433
theorem B21999761 : Blo 1929435 21999761 := bstep (se 2 (by rfl) ⟨8249910, by rfl⟩ : syracuseStep 21999761 = 16499821) B16499821
theorem B14666507 : Blo 1929435 14666507 := bstep (se 1 (by rfl) ⟨10999880, by rfl⟩ : syracuseStep 14666507 = 21999761) B21999761
theorem B9777671 : Blo 1929435 9777671 := bstep (se 1 (by rfl) ⟨7333253, by rfl⟩ : syracuseStep 9777671 = 14666507) B14666507
theorem B6518447 : Blo 1929435 6518447 := bstep (se 1 (by rfl) ⟨4888835, by rfl⟩ : syracuseStep 6518447 = 9777671) B9777671
theorem B4345631 : Blo 1929435 4345631 := bstep (se 1 (by rfl) ⟨3259223, by rfl⟩ : syracuseStep 4345631 = 6518447) B6518447
theorem B2897087 : Blo 1929435 2897087 := bstep (se 1 (by rfl) ⟨2172815, by rfl⟩ : syracuseStep 2897087 = 4345631) B4345631
theorem B1931391 : Blo 1929435 1931391 := bstep (se 1 (by rfl) ⟨1448543, by rfl⟩ : syracuseStep 1931391 = 2897087) B2897087
theorem B2897093 : Blo 1929435 2897093 := bbase (se 4 (by rfl) ⟨271602, by rfl⟩ : syracuseStep 2897093 = 543205) (by norm_num)
theorem B1931395 : Blo 1929435 1931395 := bstep (se 1 (by rfl) ⟨1448546, by rfl⟩ : syracuseStep 1931395 = 2897093) B2897093
theorem B3259237 : Blo 1929435 3259237 := bbase (se 4 (by rfl) ⟨305553, by rfl⟩ : syracuseStep 3259237 = 611107) (by norm_num)
theorem B4345649 : Blo 1929435 4345649 := bstep (se 2 (by rfl) ⟨1629618, by rfl⟩ : syracuseStep 4345649 = 3259237) B3259237
theorem B2897099 : Blo 1929435 2897099 := bstep (se 1 (by rfl) ⟨2172824, by rfl⟩ : syracuseStep 2897099 = 4345649) B4345649
theorem B1931399 : Blo 1929435 1931399 := bstep (se 1 (by rfl) ⟨1448549, by rfl⟩ : syracuseStep 1931399 = 2897099) B2897099
theorem B2172829 : Blo 1929435 2172829 := bbase (se 3 (by rfl) ⟨407405, by rfl⟩ : syracuseStep 2172829 = 814811) (by norm_num)
theorem B2897105 : Blo 1929435 2897105 := bstep (se 2 (by rfl) ⟨1086414, by rfl⟩ : syracuseStep 2897105 = 2172829) B2172829
theorem B1931403 : Blo 1929435 1931403 := bstep (se 1 (by rfl) ⟨1448552, by rfl⟩ : syracuseStep 1931403 = 2897105) B2897105
theorem B6518501 : Blo 1929435 6518501 := bbase (se 4 (by rfl) ⟨611109, by rfl⟩ : syracuseStep 6518501 = 1222219) (by norm_num)
theorem B4345667 : Blo 1929435 4345667 := bstep (se 1 (by rfl) ⟨3259250, by rfl⟩ : syracuseStep 4345667 = 6518501) B6518501
theorem B2897111 : Blo 1929435 2897111 := bstep (se 1 (by rfl) ⟨2172833, by rfl⟩ : syracuseStep 2897111 = 4345667) B4345667
theorem B1931407 : Blo 1929435 1931407 := bstep (se 1 (by rfl) ⟨1448555, by rfl⟩ : syracuseStep 1931407 = 2897111) B2897111
theorem B2897117 : Blo 1929435 2897117 := bbase (se 3 (by rfl) ⟨543209, by rfl⟩ : syracuseStep 2897117 = 1086419) (by norm_num)
theorem B1931411 : Blo 1929435 1931411 := bstep (se 1 (by rfl) ⟨1448558, by rfl⟩ : syracuseStep 1931411 = 2897117) B2897117
theorem B4345685 : Blo 1929435 4345685 := bbase (se 9 (by rfl) ⟨12731, by rfl⟩ : syracuseStep 4345685 = 25463) (by norm_num)
theorem B2897123 : Blo 1929435 2897123 := bstep (se 1 (by rfl) ⟨2172842, by rfl⟩ : syracuseStep 2897123 = 4345685) B4345685
theorem B1931415 : Blo 1929435 1931415 := bstep (se 1 (by rfl) ⟨1448561, by rfl⟩ : syracuseStep 1931415 = 2897123) B2897123
theorem B5500021 : Blo 1929435 5500021 := bbase (se 5 (by rfl) ⟨257813, by rfl⟩ : syracuseStep 5500021 = 515627) (by norm_num)
theorem B7333361 : Blo 1929435 7333361 := bstep (se 2 (by rfl) ⟨2750010, by rfl⟩ : syracuseStep 7333361 = 5500021) B5500021
theorem B4888907 : Blo 1929435 4888907 := bstep (se 1 (by rfl) ⟨3666680, by rfl⟩ : syracuseStep 4888907 = 7333361) B7333361
theorem B3259271 : Blo 1929435 3259271 := bstep (se 1 (by rfl) ⟨2444453, by rfl⟩ : syracuseStep 3259271 = 4888907) B4888907
theorem B2172847 : Blo 1929435 2172847 := bstep (se 1 (by rfl) ⟨1629635, by rfl⟩ : syracuseStep 2172847 = 3259271) B3259271
theorem B2897129 : Blo 1929435 2897129 := bstep (se 2 (by rfl) ⟨1086423, by rfl⟩ : syracuseStep 2897129 = 2172847) B2172847
theorem B1931419 : Blo 1929435 1931419 := bstep (se 1 (by rfl) ⟨1448564, by rfl⟩ : syracuseStep 1931419 = 2897129) B2897129
theorem B3348821 : Blo 1929435 3348821 := bbase (se 10 (by rfl) ⟨4905, by rfl⟩ : syracuseStep 3348821 = 9811) (by norm_num)
theorem B8930189 : Blo 1929435 8930189 := bstep (se 3 (by rfl) ⟨1674410, by rfl⟩ : syracuseStep 8930189 = 3348821) B3348821
theorem B5953459 : Blo 1929435 5953459 := bstep (se 1 (by rfl) ⟨4465094, by rfl⟩ : syracuseStep 5953459 = 8930189) B8930189
theorem B7937945 : Blo 1929435 7937945 := bstep (se 2 (by rfl) ⟨2976729, by rfl⟩ : syracuseStep 7937945 = 5953459) B5953459
theorem B5291963 : Blo 1929435 5291963 := bstep (se 1 (by rfl) ⟨3968972, by rfl⟩ : syracuseStep 5291963 = 7937945) B7937945
theorem B3527975 : Blo 1929435 3527975 := bstep (se 1 (by rfl) ⟨2645981, by rfl⟩ : syracuseStep 3527975 = 5291963) B5291963
theorem B9407933 : Blo 1929435 9407933 := bstep (se 3 (by rfl) ⟨1763987, by rfl⟩ : syracuseStep 9407933 = 3527975) B3527975
theorem B6271955 : Blo 1929435 6271955 := bstep (se 1 (by rfl) ⟨4703966, by rfl⟩ : syracuseStep 6271955 = 9407933) B9407933
theorem B4181303 : Blo 1929435 4181303 := bstep (se 1 (by rfl) ⟨3135977, by rfl⟩ : syracuseStep 4181303 = 6271955) B6271955
theorem B11150141 : Blo 1929435 11150141 := bstep (se 3 (by rfl) ⟨2090651, by rfl⟩ : syracuseStep 11150141 = 4181303) B4181303
theorem B118934837 : Blo 1929435 118934837 := bstep (se 5 (by rfl) ⟨5575070, by rfl⟩ : syracuseStep 118934837 = 11150141) B11150141
theorem B79289891 : Blo 1929435 79289891 := bstep (se 1 (by rfl) ⟨59467418, by rfl⟩ : syracuseStep 79289891 = 118934837) B118934837
theorem B52859927 : Blo 1929435 52859927 := bstep (se 1 (by rfl) ⟨39644945, by rfl⟩ : syracuseStep 52859927 = 79289891) B79289891
theorem B35239951 : Blo 1929435 35239951 := bstep (se 1 (by rfl) ⟨26429963, by rfl⟩ : syracuseStep 35239951 = 52859927) B52859927
theorem B187946405 : Blo 1929435 187946405 := bstep (se 4 (by rfl) ⟨17619975, by rfl⟩ : syracuseStep 187946405 = 35239951) B35239951
theorem B125297603 : Blo 1929435 125297603 := bstep (se 1 (by rfl) ⟨93973202, by rfl⟩ : syracuseStep 125297603 = 187946405) B187946405
theorem B83531735 : Blo 1929435 83531735 := bstep (se 1 (by rfl) ⟨62648801, by rfl⟩ : syracuseStep 83531735 = 125297603) B125297603
theorem B55687823 : Blo 1929435 55687823 := bstep (se 1 (by rfl) ⟨41765867, by rfl⟩ : syracuseStep 55687823 = 83531735) B83531735
theorem B37125215 : Blo 1929435 37125215 := bstep (se 1 (by rfl) ⟨27843911, by rfl⟩ : syracuseStep 37125215 = 55687823) B55687823
theorem B24750143 : Blo 1929435 24750143 := bstep (se 1 (by rfl) ⟨18562607, by rfl⟩ : syracuseStep 24750143 = 37125215) B37125215
theorem B16500095 : Blo 1929435 16500095 := bstep (se 1 (by rfl) ⟨12375071, by rfl⟩ : syracuseStep 16500095 = 24750143) B24750143
theorem B11000063 : Blo 1929435 11000063 := bstep (se 1 (by rfl) ⟨8250047, by rfl⟩ : syracuseStep 11000063 = 16500095) B16500095
theorem B7333375 : Blo 1929435 7333375 := bstep (se 1 (by rfl) ⟨5500031, by rfl⟩ : syracuseStep 7333375 = 11000063) B11000063
theorem B9777833 : Blo 1929435 9777833 := bstep (se 2 (by rfl) ⟨3666687, by rfl⟩ : syracuseStep 9777833 = 7333375) B7333375
theorem B6518555 : Blo 1929435 6518555 := bstep (se 1 (by rfl) ⟨4888916, by rfl⟩ : syracuseStep 6518555 = 9777833) B9777833
theorem B4345703 : Blo 1929435 4345703 := bstep (se 1 (by rfl) ⟨3259277, by rfl⟩ : syracuseStep 4345703 = 6518555) B6518555
theorem B2897135 : Blo 1929435 2897135 := bstep (se 1 (by rfl) ⟨2172851, by rfl⟩ : syracuseStep 2897135 = 4345703) B4345703
theorem B1931423 : Blo 1929435 1931423 := bstep (se 1 (by rfl) ⟨1448567, by rfl⟩ : syracuseStep 1931423 = 2897135) B2897135
theorem B2897141 : Blo 1929435 2897141 := bbase (se 5 (by rfl) ⟨135803, by rfl⟩ : syracuseStep 2897141 = 271607) (by norm_num)
theorem B1931427 : Blo 1929435 1931427 := bstep (se 1 (by rfl) ⟨1448570, by rfl⟩ : syracuseStep 1931427 = 2897141) B2897141
theorem B12375125 : Blo 1929435 12375125 := bbase (se 8 (by rfl) ⟨72510, by rfl⟩ : syracuseStep 12375125 = 145021) (by norm_num)
theorem B8250083 : Blo 1929435 8250083 := bstep (se 1 (by rfl) ⟨6187562, by rfl⟩ : syracuseStep 8250083 = 12375125) B12375125
theorem B5500055 : Blo 1929435 5500055 := bstep (se 1 (by rfl) ⟨4125041, by rfl⟩ : syracuseStep 5500055 = 8250083) B8250083
theorem B3666703 : Blo 1929435 3666703 := bstep (se 1 (by rfl) ⟨2750027, by rfl⟩ : syracuseStep 3666703 = 5500055) B5500055
theorem B4888937 : Blo 1929435 4888937 := bstep (se 2 (by rfl) ⟨1833351, by rfl⟩ : syracuseStep 4888937 = 3666703) B3666703
theorem B3259291 : Blo 1929435 3259291 := bstep (se 1 (by rfl) ⟨2444468, by rfl⟩ : syracuseStep 3259291 = 4888937) B4888937
theorem B4345721 : Blo 1929435 4345721 := bstep (se 2 (by rfl) ⟨1629645, by rfl⟩ : syracuseStep 4345721 = 3259291) B3259291
theorem B2897147 : Blo 1929435 2897147 := bstep (se 1 (by rfl) ⟨2172860, by rfl⟩ : syracuseStep 2897147 = 4345721) B4345721
theorem B1931431 : Blo 1929435 1931431 := bstep (se 1 (by rfl) ⟨1448573, by rfl⟩ : syracuseStep 1931431 = 2897147) B2897147
theorem B2172865 : Blo 1929435 2172865 := bbase (se 2 (by rfl) ⟨814824, by rfl⟩ : syracuseStep 2172865 = 1629649) (by norm_num)
theorem B2897153 : Blo 1929435 2897153 := bstep (se 2 (by rfl) ⟨1086432, by rfl⟩ : syracuseStep 2897153 = 2172865) B2172865
theorem B1931435 : Blo 1929435 1931435 := bstep (se 1 (by rfl) ⟨1448576, by rfl⟩ : syracuseStep 1931435 = 2897153) B2897153
theorem C0 (j : ℕ) (h1 : 482358 ≤ j) (h2 : j ≤ 482858) : Blo 1929435 (4 * j + 3) := by
  interval_cases j
  · exact B1929435
  · exact B1929439
  · exact B1929443
  · exact B1929447
  · exact B1929451
  · exact B1929455
  · exact B1929459
  · exact B1929463
  · exact B1929467
  · exact B1929471
  · exact B1929475
  · exact B1929479
  · exact B1929483
  · exact B1929487
  · exact B1929491
  · exact B1929495
  · exact B1929499
  · exact B1929503
  · exact B1929507
  · exact B1929511
  · exact B1929515
  · exact B1929519
  · exact B1929523
  · exact B1929527
  · exact B1929531
  · exact B1929535
  · exact B1929539
  · exact B1929543
  · exact B1929547
  · exact B1929551
  · exact B1929555
  · exact B1929559
  · exact B1929563
  · exact B1929567
  · exact B1929571
  · exact B1929575
  · exact B1929579
  · exact B1929583
  · exact B1929587
  · exact B1929591
  · exact B1929595
  · exact B1929599
  · exact B1929603
  · exact B1929607
  · exact B1929611
  · exact B1929615
  · exact B1929619
  · exact B1929623
  · exact B1929627
  · exact B1929631
  · exact B1929635
  · exact B1929639
  · exact B1929643
  · exact B1929647
  · exact B1929651
  · exact B1929655
  · exact B1929659
  · exact B1929663
  · exact B1929667
  · exact B1929671
  · exact B1929675
  · exact B1929679
  · exact B1929683
  · exact B1929687
  · exact B1929691
  · exact B1929695
  · exact B1929699
  · exact B1929703
  · exact B1929707
  · exact B1929711
  · exact B1929715
  · exact B1929719
  · exact B1929723
  · exact B1929727
  · exact B1929731
  · exact B1929735
  · exact B1929739
  · exact B1929743
  · exact B1929747
  · exact B1929751
  · exact B1929755
  · exact B1929759
  · exact B1929763
  · exact B1929767
  · exact B1929771
  · exact B1929775
  · exact B1929779
  · exact B1929783
  · exact B1929787
  · exact B1929791
  · exact B1929795
  · exact B1929799
  · exact B1929803
  · exact B1929807
  · exact B1929811
  · exact B1929815
  · exact B1929819
  · exact B1929823
  · exact B1929827
  · exact B1929831
  · exact B1929835
  · exact B1929839
  · exact B1929843
  · exact B1929847
  · exact B1929851
  · exact B1929855
  · exact B1929859
  · exact B1929863
  · exact B1929867
  · exact B1929871
  · exact B1929875
  · exact B1929879
  · exact B1929883
  · exact B1929887
  · exact B1929891
  · exact B1929895
  · exact B1929899
  · exact B1929903
  · exact B1929907
  · exact B1929911
  · exact B1929915
  · exact B1929919
  · exact B1929923
  · exact B1929927
  · exact B1929931
  · exact B1929935
  · exact B1929939
  · exact B1929943
  · exact B1929947
  · exact B1929951
  · exact B1929955
  · exact B1929959
  · exact B1929963
  · exact B1929967
  · exact B1929971
  · exact B1929975
  · exact B1929979
  · exact B1929983
  · exact B1929987
  · exact B1929991
  · exact B1929995
  · exact B1929999
  · exact B1930003
  · exact B1930007
  · exact B1930011
  · exact B1930015
  · exact B1930019
  · exact B1930023
  · exact B1930027
  · exact B1930031
  · exact B1930035
  · exact B1930039
  · exact B1930043
  · exact B1930047
  · exact B1930051
  · exact B1930055
  · exact B1930059
  · exact B1930063
  · exact B1930067
  · exact B1930071
  · exact B1930075
  · exact B1930079
  · exact B1930083
  · exact B1930087
  · exact B1930091
  · exact B1930095
  · exact B1930099
  · exact B1930103
  · exact B1930107
  · exact B1930111
  · exact B1930115
  · exact B1930119
  · exact B1930123
  · exact B1930127
  · exact B1930131
  · exact B1930135
  · exact B1930139
  · exact B1930143
  · exact B1930147
  · exact B1930151
  · exact B1930155
  · exact B1930159
  · exact B1930163
  · exact B1930167
  · exact B1930171
  · exact B1930175
  · exact B1930179
  · exact B1930183
  · exact B1930187
  · exact B1930191
  · exact B1930195
  · exact B1930199
  · exact B1930203
  · exact B1930207
  · exact B1930211
  · exact B1930215
  · exact B1930219
  · exact B1930223
  · exact B1930227
  · exact B1930231
  · exact B1930235
  · exact B1930239
  · exact B1930243
  · exact B1930247
  · exact B1930251
  · exact B1930255
  · exact B1930259
  · exact B1930263
  · exact B1930267
  · exact B1930271
  · exact B1930275
  · exact B1930279
  · exact B1930283
  · exact B1930287
  · exact B1930291
  · exact B1930295
  · exact B1930299
  · exact B1930303
  · exact B1930307
  · exact B1930311
  · exact B1930315
  · exact B1930319
  · exact B1930323
  · exact B1930327
  · exact B1930331
  · exact B1930335
  · exact B1930339
  · exact B1930343
  · exact B1930347
  · exact B1930351
  · exact B1930355
  · exact B1930359
  · exact B1930363
  · exact B1930367
  · exact B1930371
  · exact B1930375
  · exact B1930379
  · exact B1930383
  · exact B1930387
  · exact B1930391
  · exact B1930395
  · exact B1930399
  · exact B1930403
  · exact B1930407
  · exact B1930411
  · exact B1930415
  · exact B1930419
  · exact B1930423
  · exact B1930427
  · exact B1930431
  · exact B1930435
  · exact B1930439
  · exact B1930443
  · exact B1930447
  · exact B1930451
  · exact B1930455
  · exact B1930459
  · exact B1930463
  · exact B1930467
  · exact B1930471
  · exact B1930475
  · exact B1930479
  · exact B1930483
  · exact B1930487
  · exact B1930491
  · exact B1930495
  · exact B1930499
  · exact B1930503
  · exact B1930507
  · exact B1930511
  · exact B1930515
  · exact B1930519
  · exact B1930523
  · exact B1930527
  · exact B1930531
  · exact B1930535
  · exact B1930539
  · exact B1930543
  · exact B1930547
  · exact B1930551
  · exact B1930555
  · exact B1930559
  · exact B1930563
  · exact B1930567
  · exact B1930571
  · exact B1930575
  · exact B1930579
  · exact B1930583
  · exact B1930587
  · exact B1930591
  · exact B1930595
  · exact B1930599
  · exact B1930603
  · exact B1930607
  · exact B1930611
  · exact B1930615
  · exact B1930619
  · exact B1930623
  · exact B1930627
  · exact B1930631
  · exact B1930635
  · exact B1930639
  · exact B1930643
  · exact B1930647
  · exact B1930651
  · exact B1930655
  · exact B1930659
  · exact B1930663
  · exact B1930667
  · exact B1930671
  · exact B1930675
  · exact B1930679
  · exact B1930683
  · exact B1930687
  · exact B1930691
  · exact B1930695
  · exact B1930699
  · exact B1930703
  · exact B1930707
  · exact B1930711
  · exact B1930715
  · exact B1930719
  · exact B1930723
  · exact B1930727
  · exact B1930731
  · exact B1930735
  · exact B1930739
  · exact B1930743
  · exact B1930747
  · exact B1930751
  · exact B1930755
  · exact B1930759
  · exact B1930763
  · exact B1930767
  · exact B1930771
  · exact B1930775
  · exact B1930779
  · exact B1930783
  · exact B1930787
  · exact B1930791
  · exact B1930795
  · exact B1930799
  · exact B1930803
  · exact B1930807
  · exact B1930811
  · exact B1930815
  · exact B1930819
  · exact B1930823
  · exact B1930827
  · exact B1930831
  · exact B1930835
  · exact B1930839
  · exact B1930843
  · exact B1930847
  · exact B1930851
  · exact B1930855
  · exact B1930859
  · exact B1930863
  · exact B1930867
  · exact B1930871
  · exact B1930875
  · exact B1930879
  · exact B1930883
  · exact B1930887
  · exact B1930891
  · exact B1930895
  · exact B1930899
  · exact B1930903
  · exact B1930907
  · exact B1930911
  · exact B1930915
  · exact B1930919
  · exact B1930923
  · exact B1930927
  · exact B1930931
  · exact B1930935
  · exact B1930939
  · exact B1930943
  · exact B1930947
  · exact B1930951
  · exact B1930955
  · exact B1930959
  · exact B1930963
  · exact B1930967
  · exact B1930971
  · exact B1930975
  · exact B1930979
  · exact B1930983
  · exact B1930987
  · exact B1930991
  · exact B1930995
  · exact B1930999
  · exact B1931003
  · exact B1931007
  · exact B1931011
  · exact B1931015
  · exact B1931019
  · exact B1931023
  · exact B1931027
  · exact B1931031
  · exact B1931035
  · exact B1931039
  · exact B1931043
  · exact B1931047
  · exact B1931051
  · exact B1931055
  · exact B1931059
  · exact B1931063
  · exact B1931067
  · exact B1931071
  · exact B1931075
  · exact B1931079
  · exact B1931083
  · exact B1931087
  · exact B1931091
  · exact B1931095
  · exact B1931099
  · exact B1931103
  · exact B1931107
  · exact B1931111
  · exact B1931115
  · exact B1931119
  · exact B1931123
  · exact B1931127
  · exact B1931131
  · exact B1931135
  · exact B1931139
  · exact B1931143
  · exact B1931147
  · exact B1931151
  · exact B1931155
  · exact B1931159
  · exact B1931163
  · exact B1931167
  · exact B1931171
  · exact B1931175
  · exact B1931179
  · exact B1931183
  · exact B1931187
  · exact B1931191
  · exact B1931195
  · exact B1931199
  · exact B1931203
  · exact B1931207
  · exact B1931211
  · exact B1931215
  · exact B1931219
  · exact B1931223
  · exact B1931227
  · exact B1931231
  · exact B1931235
  · exact B1931239
  · exact B1931243
  · exact B1931247
  · exact B1931251
  · exact B1931255
  · exact B1931259
  · exact B1931263
  · exact B1931267
  · exact B1931271
  · exact B1931275
  · exact B1931279
  · exact B1931283
  · exact B1931287
  · exact B1931291
  · exact B1931295
  · exact B1931299
  · exact B1931303
  · exact B1931307
  · exact B1931311
  · exact B1931315
  · exact B1931319
  · exact B1931323
  · exact B1931327
  · exact B1931331
  · exact B1931335
  · exact B1931339
  · exact B1931343
  · exact B1931347
  · exact B1931351
  · exact B1931355
  · exact B1931359
  · exact B1931363
  · exact B1931367
  · exact B1931371
  · exact B1931375
  · exact B1931379
  · exact B1931383
  · exact B1931387
  · exact B1931391
  · exact B1931395
  · exact B1931399
  · exact B1931403
  · exact B1931407
  · exact B1931411
  · exact B1931415
  · exact B1931419
  · exact B1931423
  · exact B1931427
  · exact B1931431
  · exact B1931435
theorem solution (m : ℕ) (hlo : 1929435 ≤ m) (hhi : m ≤ 1931435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 482358 ≤ j := by omega
    have hj2 : j ≤ 482858 := by omega
    have hb : Blo 1929435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
