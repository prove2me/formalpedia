-- Prove2me | solution 1 for syracuse_descends_range_2273435_2275435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:29.695747+00:00
-- url     : https://prove2.me/submissions/38725bf1-230e-4992-ba4e-7f90b7527fa6

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

theorem B2427737 : Blo 2273435 2427737 := bbase (se 2 (by rfl) ⟨910401, by rfl⟩ : syracuseStep 2427737 = 1820803) (by norm_num)
theorem B6473965 : Blo 2273435 6473965 := bstep (se 3 (by rfl) ⟨1213868, by rfl⟩ : syracuseStep 6473965 = 2427737) B2427737
theorem B8631953 : Blo 2273435 8631953 := bstep (se 2 (by rfl) ⟨3236982, by rfl⟩ : syracuseStep 8631953 = 6473965) B6473965
theorem B5754635 : Blo 2273435 5754635 := bstep (se 1 (by rfl) ⟨4315976, by rfl⟩ : syracuseStep 5754635 = 8631953) B8631953
theorem B3836423 : Blo 2273435 3836423 := bstep (se 1 (by rfl) ⟨2877317, by rfl⟩ : syracuseStep 3836423 = 5754635) B5754635
theorem B2557615 : Blo 2273435 2557615 := bstep (se 1 (by rfl) ⟨1918211, by rfl⟩ : syracuseStep 2557615 = 3836423) B3836423
theorem B3410153 : Blo 2273435 3410153 := bstep (se 2 (by rfl) ⟨1278807, by rfl⟩ : syracuseStep 3410153 = 2557615) B2557615
theorem B2273435 : Blo 2273435 2273435 := bstep (se 1 (by rfl) ⟨1705076, by rfl⟩ : syracuseStep 2273435 = 3410153) B3410153
theorem B53214677 : Blo 2273435 53214677 := bbase (se 7 (by rfl) ⟨623609, by rfl⟩ : syracuseStep 53214677 = 1247219) (by norm_num)
theorem B35476451 : Blo 2273435 35476451 := bstep (se 1 (by rfl) ⟨26607338, by rfl⟩ : syracuseStep 35476451 = 53214677) B53214677
theorem B23650967 : Blo 2273435 23650967 := bstep (se 1 (by rfl) ⟨17738225, by rfl⟩ : syracuseStep 23650967 = 35476451) B35476451
theorem B15767311 : Blo 2273435 15767311 := bstep (se 1 (by rfl) ⟨11825483, by rfl⟩ : syracuseStep 15767311 = 23650967) B23650967
theorem B21023081 : Blo 2273435 21023081 := bstep (se 2 (by rfl) ⟨7883655, by rfl⟩ : syracuseStep 21023081 = 15767311) B15767311
theorem B14015387 : Blo 2273435 14015387 := bstep (se 1 (by rfl) ⟨10511540, by rfl⟩ : syracuseStep 14015387 = 21023081) B21023081
theorem B37374365 : Blo 2273435 37374365 := bstep (se 3 (by rfl) ⟨7007693, by rfl⟩ : syracuseStep 37374365 = 14015387) B14015387
theorem B24916243 : Blo 2273435 24916243 := bstep (se 1 (by rfl) ⟨18687182, by rfl⟩ : syracuseStep 24916243 = 37374365) B37374365
theorem B33221657 : Blo 2273435 33221657 := bstep (se 2 (by rfl) ⟨12458121, by rfl⟩ : syracuseStep 33221657 = 24916243) B24916243
theorem B22147771 : Blo 2273435 22147771 := bstep (se 1 (by rfl) ⟨16610828, by rfl⟩ : syracuseStep 22147771 = 33221657) B33221657
theorem B29530361 : Blo 2273435 29530361 := bstep (se 2 (by rfl) ⟨11073885, by rfl⟩ : syracuseStep 29530361 = 22147771) B22147771
theorem B19686907 : Blo 2273435 19686907 := bstep (se 1 (by rfl) ⟨14765180, by rfl⟩ : syracuseStep 19686907 = 29530361) B29530361
theorem B104996837 : Blo 2273435 104996837 := bstep (se 4 (by rfl) ⟨9843453, by rfl⟩ : syracuseStep 104996837 = 19686907) B19686907
theorem B279991565 : Blo 2273435 279991565 := bstep (se 3 (by rfl) ⟨52498418, by rfl⟩ : syracuseStep 279991565 = 104996837) B104996837
theorem B186661043 : Blo 2273435 186661043 := bstep (se 1 (by rfl) ⟨139995782, by rfl⟩ : syracuseStep 186661043 = 279991565) B279991565
theorem B124440695 : Blo 2273435 124440695 := bstep (se 1 (by rfl) ⟨93330521, by rfl⟩ : syracuseStep 124440695 = 186661043) B186661043
theorem B82960463 : Blo 2273435 82960463 := bstep (se 1 (by rfl) ⟨62220347, by rfl⟩ : syracuseStep 82960463 = 124440695) B124440695
theorem B55306975 : Blo 2273435 55306975 := bstep (se 1 (by rfl) ⟨41480231, by rfl⟩ : syracuseStep 55306975 = 82960463) B82960463
theorem B73742633 : Blo 2273435 73742633 := bstep (se 2 (by rfl) ⟨27653487, by rfl⟩ : syracuseStep 73742633 = 55306975) B55306975
theorem B49161755 : Blo 2273435 49161755 := bstep (se 1 (by rfl) ⟨36871316, by rfl⟩ : syracuseStep 49161755 = 73742633) B73742633
theorem B32774503 : Blo 2273435 32774503 := bstep (se 1 (by rfl) ⟨24580877, by rfl⟩ : syracuseStep 32774503 = 49161755) B49161755
theorem B43699337 : Blo 2273435 43699337 := bstep (se 2 (by rfl) ⟨16387251, by rfl⟩ : syracuseStep 43699337 = 32774503) B32774503
theorem B29132891 : Blo 2273435 29132891 := bstep (se 1 (by rfl) ⟨21849668, by rfl⟩ : syracuseStep 29132891 = 43699337) B43699337
theorem B19421927 : Blo 2273435 19421927 := bstep (se 1 (by rfl) ⟨14566445, by rfl⟩ : syracuseStep 19421927 = 29132891) B29132891
theorem B12947951 : Blo 2273435 12947951 := bstep (se 1 (by rfl) ⟨9710963, by rfl⟩ : syracuseStep 12947951 = 19421927) B19421927
theorem B8631967 : Blo 2273435 8631967 := bstep (se 1 (by rfl) ⟨6473975, by rfl⟩ : syracuseStep 8631967 = 12947951) B12947951
theorem B11509289 : Blo 2273435 11509289 := bstep (se 2 (by rfl) ⟨4315983, by rfl⟩ : syracuseStep 11509289 = 8631967) B8631967
theorem B7672859 : Blo 2273435 7672859 := bstep (se 1 (by rfl) ⟨5754644, by rfl⟩ : syracuseStep 7672859 = 11509289) B11509289
theorem B5115239 : Blo 2273435 5115239 := bstep (se 1 (by rfl) ⟨3836429, by rfl⟩ : syracuseStep 5115239 = 7672859) B7672859
theorem B3410159 : Blo 2273435 3410159 := bstep (se 1 (by rfl) ⟨2557619, by rfl⟩ : syracuseStep 3410159 = 5115239) B5115239
theorem B2273439 : Blo 2273435 2273439 := bstep (se 1 (by rfl) ⟨1705079, by rfl⟩ : syracuseStep 2273439 = 3410159) B3410159
theorem B3410165 : Blo 2273435 3410165 := bbase (se 5 (by rfl) ⟨159851, by rfl⟩ : syracuseStep 3410165 = 319703) (by norm_num)
theorem B2273443 : Blo 2273435 2273443 := bstep (se 1 (by rfl) ⟨1705082, by rfl⟩ : syracuseStep 2273443 = 3410165) B3410165
theorem B21849749 : Blo 2273435 21849749 := bbase (se 6 (by rfl) ⟨512103, by rfl⟩ : syracuseStep 21849749 = 1024207) (by norm_num)
theorem B14566499 : Blo 2273435 14566499 := bstep (se 1 (by rfl) ⟨10924874, by rfl⟩ : syracuseStep 14566499 = 21849749) B21849749
theorem B9710999 : Blo 2273435 9710999 := bstep (se 1 (by rfl) ⟨7283249, by rfl⟩ : syracuseStep 9710999 = 14566499) B14566499
theorem B6473999 : Blo 2273435 6473999 := bstep (se 1 (by rfl) ⟨4855499, by rfl⟩ : syracuseStep 6473999 = 9710999) B9710999
theorem B4315999 : Blo 2273435 4315999 := bstep (se 1 (by rfl) ⟨3236999, by rfl⟩ : syracuseStep 4315999 = 6473999) B6473999
theorem B5754665 : Blo 2273435 5754665 := bstep (se 2 (by rfl) ⟨2157999, by rfl⟩ : syracuseStep 5754665 = 4315999) B4315999
theorem B3836443 : Blo 2273435 3836443 := bstep (se 1 (by rfl) ⟨2877332, by rfl⟩ : syracuseStep 3836443 = 5754665) B5754665
theorem B5115257 : Blo 2273435 5115257 := bstep (se 2 (by rfl) ⟨1918221, by rfl⟩ : syracuseStep 5115257 = 3836443) B3836443
theorem B3410171 : Blo 2273435 3410171 := bstep (se 1 (by rfl) ⟨2557628, by rfl⟩ : syracuseStep 3410171 = 5115257) B5115257
theorem B2273447 : Blo 2273435 2273447 := bstep (se 1 (by rfl) ⟨1705085, by rfl⟩ : syracuseStep 2273447 = 3410171) B3410171
theorem B2557633 : Blo 2273435 2557633 := bbase (se 2 (by rfl) ⟨959112, by rfl⟩ : syracuseStep 2557633 = 1918225) (by norm_num)
theorem B3410177 : Blo 2273435 3410177 := bstep (se 2 (by rfl) ⟨1278816, by rfl⟩ : syracuseStep 3410177 = 2557633) B2557633
theorem B2273451 : Blo 2273435 2273451 := bstep (se 1 (by rfl) ⟨1705088, by rfl⟩ : syracuseStep 2273451 = 3410177) B3410177
theorem B5754685 : Blo 2273435 5754685 := bbase (se 3 (by rfl) ⟨1079003, by rfl⟩ : syracuseStep 5754685 = 2158007) (by norm_num)
theorem B7672913 : Blo 2273435 7672913 := bstep (se 2 (by rfl) ⟨2877342, by rfl⟩ : syracuseStep 7672913 = 5754685) B5754685
theorem B5115275 : Blo 2273435 5115275 := bstep (se 1 (by rfl) ⟨3836456, by rfl⟩ : syracuseStep 5115275 = 7672913) B7672913
theorem B3410183 : Blo 2273435 3410183 := bstep (se 1 (by rfl) ⟨2557637, by rfl⟩ : syracuseStep 3410183 = 5115275) B5115275
theorem B2273455 : Blo 2273435 2273455 := bstep (se 1 (by rfl) ⟨1705091, by rfl⟩ : syracuseStep 2273455 = 3410183) B3410183
theorem B3410189 : Blo 2273435 3410189 := bbase (se 3 (by rfl) ⟨639410, by rfl⟩ : syracuseStep 3410189 = 1278821) (by norm_num)
theorem B2273459 : Blo 2273435 2273459 := bstep (se 1 (by rfl) ⟨1705094, by rfl⟩ : syracuseStep 2273459 = 3410189) B3410189
theorem B5115293 : Blo 2273435 5115293 := bbase (se 3 (by rfl) ⟨959117, by rfl⟩ : syracuseStep 5115293 = 1918235) (by norm_num)
theorem B3410195 : Blo 2273435 3410195 := bstep (se 1 (by rfl) ⟨2557646, by rfl⟩ : syracuseStep 3410195 = 5115293) B5115293
theorem B2273463 : Blo 2273435 2273463 := bstep (se 1 (by rfl) ⟨1705097, by rfl⟩ : syracuseStep 2273463 = 3410195) B3410195
theorem B3836477 : Blo 2273435 3836477 := bbase (se 3 (by rfl) ⟨719339, by rfl⟩ : syracuseStep 3836477 = 1438679) (by norm_num)
theorem B2557651 : Blo 2273435 2557651 := bstep (se 1 (by rfl) ⟨1918238, by rfl⟩ : syracuseStep 2557651 = 3836477) B3836477
theorem B3410201 : Blo 2273435 3410201 := bstep (se 2 (by rfl) ⟨1278825, by rfl⟩ : syracuseStep 3410201 = 2557651) B2557651
theorem B2273467 : Blo 2273435 2273467 := bstep (se 1 (by rfl) ⟨1705100, by rfl⟩ : syracuseStep 2273467 = 3410201) B3410201
theorem B10800485 : Blo 2273435 10800485 := bbase (se 4 (by rfl) ⟨1012545, by rfl⟩ : syracuseStep 10800485 = 2025091) (by norm_num)
theorem B7200323 : Blo 2273435 7200323 := bstep (se 1 (by rfl) ⟨5400242, by rfl⟩ : syracuseStep 7200323 = 10800485) B10800485
theorem B4800215 : Blo 2273435 4800215 := bstep (se 1 (by rfl) ⟨3600161, by rfl⟩ : syracuseStep 4800215 = 7200323) B7200323
theorem B3200143 : Blo 2273435 3200143 := bstep (se 1 (by rfl) ⟨2400107, by rfl⟩ : syracuseStep 3200143 = 4800215) B4800215
theorem B4266857 : Blo 2273435 4266857 := bstep (se 2 (by rfl) ⟨1600071, by rfl⟩ : syracuseStep 4266857 = 3200143) B3200143
theorem B2844571 : Blo 2273435 2844571 := bstep (se 1 (by rfl) ⟨2133428, by rfl⟩ : syracuseStep 2844571 = 4266857) B4266857
theorem B3792761 : Blo 2273435 3792761 := bstep (se 2 (by rfl) ⟨1422285, by rfl⟩ : syracuseStep 3792761 = 2844571) B2844571
theorem B2528507 : Blo 2273435 2528507 := bstep (se 1 (by rfl) ⟨1896380, by rfl⟩ : syracuseStep 2528507 = 3792761) B3792761
theorem B6742685 : Blo 2273435 6742685 := bstep (se 3 (by rfl) ⟨1264253, by rfl⟩ : syracuseStep 6742685 = 2528507) B2528507
theorem B4495123 : Blo 2273435 4495123 := bstep (se 1 (by rfl) ⟨3371342, by rfl⟩ : syracuseStep 4495123 = 6742685) B6742685
theorem B5993497 : Blo 2273435 5993497 := bstep (se 2 (by rfl) ⟨2247561, by rfl⟩ : syracuseStep 5993497 = 4495123) B4495123
theorem B31965317 : Blo 2273435 31965317 := bstep (se 4 (by rfl) ⟨2996748, by rfl⟩ : syracuseStep 31965317 = 5993497) B5993497
theorem B340963381 : Blo 2273435 340963381 := bstep (se 5 (by rfl) ⟨15982658, by rfl⟩ : syracuseStep 340963381 = 31965317) B31965317
theorem B454617841 : Blo 2273435 454617841 := bstep (se 2 (by rfl) ⟨170481690, by rfl⟩ : syracuseStep 454617841 = 340963381) B340963381
theorem B606157121 : Blo 2273435 606157121 := bstep (se 2 (by rfl) ⟨227308920, by rfl⟩ : syracuseStep 606157121 = 454617841) B454617841
theorem B404104747 : Blo 2273435 404104747 := bstep (se 1 (by rfl) ⟨303078560, by rfl⟩ : syracuseStep 404104747 = 606157121) B606157121
theorem B538806329 : Blo 2273435 538806329 := bstep (se 2 (by rfl) ⟨202052373, by rfl⟩ : syracuseStep 538806329 = 404104747) B404104747
theorem B359204219 : Blo 2273435 359204219 := bstep (se 1 (by rfl) ⟨269403164, by rfl⟩ : syracuseStep 359204219 = 538806329) B538806329
theorem B239469479 : Blo 2273435 239469479 := bstep (se 1 (by rfl) ⟨179602109, by rfl⟩ : syracuseStep 239469479 = 359204219) B359204219
theorem B159646319 : Blo 2273435 159646319 := bstep (se 1 (by rfl) ⟨119734739, by rfl⟩ : syracuseStep 159646319 = 239469479) B239469479
theorem B106430879 : Blo 2273435 106430879 := bstep (se 1 (by rfl) ⟨79823159, by rfl⟩ : syracuseStep 106430879 = 159646319) B159646319
theorem B283815677 : Blo 2273435 283815677 := bstep (se 3 (by rfl) ⟨53215439, by rfl⟩ : syracuseStep 283815677 = 106430879) B106430879
theorem B189210451 : Blo 2273435 189210451 := bstep (se 1 (by rfl) ⟨141907838, by rfl⟩ : syracuseStep 189210451 = 283815677) B283815677
theorem B252280601 : Blo 2273435 252280601 := bstep (se 2 (by rfl) ⟨94605225, by rfl⟩ : syracuseStep 252280601 = 189210451) B189210451
theorem B168187067 : Blo 2273435 168187067 := bstep (se 1 (by rfl) ⟨126140300, by rfl⟩ : syracuseStep 168187067 = 252280601) B252280601
theorem B112124711 : Blo 2273435 112124711 := bstep (se 1 (by rfl) ⟨84093533, by rfl⟩ : syracuseStep 112124711 = 168187067) B168187067
theorem B74749807 : Blo 2273435 74749807 := bstep (se 1 (by rfl) ⟨56062355, by rfl⟩ : syracuseStep 74749807 = 112124711) B112124711
theorem B99666409 : Blo 2273435 99666409 := bstep (se 2 (by rfl) ⟨37374903, by rfl⟩ : syracuseStep 99666409 = 74749807) B74749807
theorem B132888545 : Blo 2273435 132888545 := bstep (se 2 (by rfl) ⟨49833204, by rfl⟩ : syracuseStep 132888545 = 99666409) B99666409
theorem B88592363 : Blo 2273435 88592363 := bstep (se 1 (by rfl) ⟨66444272, by rfl⟩ : syracuseStep 88592363 = 132888545) B132888545
theorem B59061575 : Blo 2273435 59061575 := bstep (se 1 (by rfl) ⟨44296181, by rfl⟩ : syracuseStep 59061575 = 88592363) B88592363
theorem B39374383 : Blo 2273435 39374383 := bstep (se 1 (by rfl) ⟨29530787, by rfl⟩ : syracuseStep 39374383 = 59061575) B59061575
theorem B52499177 : Blo 2273435 52499177 := bstep (se 2 (by rfl) ⟨19687191, by rfl⟩ : syracuseStep 52499177 = 39374383) B39374383
theorem B34999451 : Blo 2273435 34999451 := bstep (se 1 (by rfl) ⟨26249588, by rfl⟩ : syracuseStep 34999451 = 52499177) B52499177
theorem B23332967 : Blo 2273435 23332967 := bstep (se 1 (by rfl) ⟨17499725, by rfl⟩ : syracuseStep 23332967 = 34999451) B34999451
theorem B15555311 : Blo 2273435 15555311 := bstep (se 1 (by rfl) ⟨11666483, by rfl⟩ : syracuseStep 15555311 = 23332967) B23332967
theorem B10370207 : Blo 2273435 10370207 := bstep (se 1 (by rfl) ⟨7777655, by rfl⟩ : syracuseStep 10370207 = 15555311) B15555311
theorem B27653885 : Blo 2273435 27653885 := bstep (se 3 (by rfl) ⟨5185103, by rfl⟩ : syracuseStep 27653885 = 10370207) B10370207
theorem B18435923 : Blo 2273435 18435923 := bstep (se 1 (by rfl) ⟨13826942, by rfl⟩ : syracuseStep 18435923 = 27653885) B27653885
theorem B12290615 : Blo 2273435 12290615 := bstep (se 1 (by rfl) ⟨9217961, by rfl⟩ : syracuseStep 12290615 = 18435923) B18435923
theorem B8193743 : Blo 2273435 8193743 := bstep (se 1 (by rfl) ⟨6145307, by rfl⟩ : syracuseStep 8193743 = 12290615) B12290615
theorem B5462495 : Blo 2273435 5462495 := bstep (se 1 (by rfl) ⟨4096871, by rfl⟩ : syracuseStep 5462495 = 8193743) B8193743
theorem B3641663 : Blo 2273435 3641663 := bstep (se 1 (by rfl) ⟨2731247, by rfl⟩ : syracuseStep 3641663 = 5462495) B5462495
theorem B2427775 : Blo 2273435 2427775 := bstep (se 1 (by rfl) ⟨1820831, by rfl⟩ : syracuseStep 2427775 = 3641663) B3641663
theorem B12948133 : Blo 2273435 12948133 := bstep (se 4 (by rfl) ⟨1213887, by rfl⟩ : syracuseStep 12948133 = 2427775) B2427775
theorem B17264177 : Blo 2273435 17264177 := bstep (se 2 (by rfl) ⟨6474066, by rfl⟩ : syracuseStep 17264177 = 12948133) B12948133
theorem B11509451 : Blo 2273435 11509451 := bstep (se 1 (by rfl) ⟨8632088, by rfl⟩ : syracuseStep 11509451 = 17264177) B17264177
theorem B7672967 : Blo 2273435 7672967 := bstep (se 1 (by rfl) ⟨5754725, by rfl⟩ : syracuseStep 7672967 = 11509451) B11509451
theorem B5115311 : Blo 2273435 5115311 := bstep (se 1 (by rfl) ⟨3836483, by rfl⟩ : syracuseStep 5115311 = 7672967) B7672967
theorem B3410207 : Blo 2273435 3410207 := bstep (se 1 (by rfl) ⟨2557655, by rfl⟩ : syracuseStep 3410207 = 5115311) B5115311
theorem B2273471 : Blo 2273435 2273471 := bstep (se 1 (by rfl) ⟨1705103, by rfl⟩ : syracuseStep 2273471 = 3410207) B3410207
theorem B3410213 : Blo 2273435 3410213 := bbase (se 4 (by rfl) ⟨319707, by rfl⟩ : syracuseStep 3410213 = 639415) (by norm_num)
theorem B2273475 : Blo 2273435 2273475 := bstep (se 1 (by rfl) ⟨1705106, by rfl⟩ : syracuseStep 2273475 = 3410213) B3410213
theorem B2877373 : Blo 2273435 2877373 := bbase (se 3 (by rfl) ⟨539507, by rfl⟩ : syracuseStep 2877373 = 1079015) (by norm_num)
theorem B3836497 : Blo 2273435 3836497 := bstep (se 2 (by rfl) ⟨1438686, by rfl⟩ : syracuseStep 3836497 = 2877373) B2877373
theorem B5115329 : Blo 2273435 5115329 := bstep (se 2 (by rfl) ⟨1918248, by rfl⟩ : syracuseStep 5115329 = 3836497) B3836497
theorem B3410219 : Blo 2273435 3410219 := bstep (se 1 (by rfl) ⟨2557664, by rfl⟩ : syracuseStep 3410219 = 5115329) B5115329
theorem B2273479 : Blo 2273435 2273479 := bstep (se 1 (by rfl) ⟨1705109, by rfl⟩ : syracuseStep 2273479 = 3410219) B3410219
theorem B2557669 : Blo 2273435 2557669 := bbase (se 4 (by rfl) ⟨239781, by rfl⟩ : syracuseStep 2557669 = 479563) (by norm_num)
theorem B3410225 : Blo 2273435 3410225 := bstep (se 2 (by rfl) ⟨1278834, by rfl⟩ : syracuseStep 3410225 = 2557669) B2557669
theorem B2273483 : Blo 2273435 2273483 := bstep (se 1 (by rfl) ⟨1705112, by rfl⟩ : syracuseStep 2273483 = 3410225) B3410225
theorem B4096901 : Blo 2273435 4096901 := bbase (se 4 (by rfl) ⟨384084, by rfl⟩ : syracuseStep 4096901 = 768169) (by norm_num)
theorem B2731267 : Blo 2273435 2731267 := bstep (se 1 (by rfl) ⟨2048450, by rfl⟩ : syracuseStep 2731267 = 4096901) B4096901
theorem B3641689 : Blo 2273435 3641689 := bstep (se 2 (by rfl) ⟨1365633, by rfl⟩ : syracuseStep 3641689 = 2731267) B2731267
theorem B4855585 : Blo 2273435 4855585 := bstep (se 2 (by rfl) ⟨1820844, by rfl⟩ : syracuseStep 4855585 = 3641689) B3641689
theorem B6474113 : Blo 2273435 6474113 := bstep (se 2 (by rfl) ⟨2427792, by rfl⟩ : syracuseStep 6474113 = 4855585) B4855585
theorem B4316075 : Blo 2273435 4316075 := bstep (se 1 (by rfl) ⟨3237056, by rfl⟩ : syracuseStep 4316075 = 6474113) B6474113
theorem B2877383 : Blo 2273435 2877383 := bstep (se 1 (by rfl) ⟨2158037, by rfl⟩ : syracuseStep 2877383 = 4316075) B4316075
theorem B7673021 : Blo 2273435 7673021 := bstep (se 3 (by rfl) ⟨1438691, by rfl⟩ : syracuseStep 7673021 = 2877383) B2877383
theorem B5115347 : Blo 2273435 5115347 := bstep (se 1 (by rfl) ⟨3836510, by rfl⟩ : syracuseStep 5115347 = 7673021) B7673021
theorem B3410231 : Blo 2273435 3410231 := bstep (se 1 (by rfl) ⟨2557673, by rfl⟩ : syracuseStep 3410231 = 5115347) B5115347
theorem B2273487 : Blo 2273435 2273487 := bstep (se 1 (by rfl) ⟨1705115, by rfl⟩ : syracuseStep 2273487 = 3410231) B3410231
theorem B3410237 : Blo 2273435 3410237 := bbase (se 3 (by rfl) ⟨639419, by rfl⟩ : syracuseStep 3410237 = 1278839) (by norm_num)
theorem B2273491 : Blo 2273435 2273491 := bstep (se 1 (by rfl) ⟨1705118, by rfl⟩ : syracuseStep 2273491 = 3410237) B3410237
theorem B5115365 : Blo 2273435 5115365 := bbase (se 4 (by rfl) ⟨479565, by rfl⟩ : syracuseStep 5115365 = 959131) (by norm_num)
theorem B3410243 : Blo 2273435 3410243 := bstep (se 1 (by rfl) ⟨2557682, by rfl⟩ : syracuseStep 3410243 = 5115365) B5115365
theorem B2273495 : Blo 2273435 2273495 := bstep (se 1 (by rfl) ⟨1705121, by rfl⟩ : syracuseStep 2273495 = 3410243) B3410243
theorem B5754797 : Blo 2273435 5754797 := bbase (se 3 (by rfl) ⟨1079024, by rfl⟩ : syracuseStep 5754797 = 2158049) (by norm_num)
theorem B3836531 : Blo 2273435 3836531 := bstep (se 1 (by rfl) ⟨2877398, by rfl⟩ : syracuseStep 3836531 = 5754797) B5754797
theorem B2557687 : Blo 2273435 2557687 := bstep (se 1 (by rfl) ⟨1918265, by rfl⟩ : syracuseStep 2557687 = 3836531) B3836531
theorem B3410249 : Blo 2273435 3410249 := bstep (se 2 (by rfl) ⟨1278843, by rfl⟩ : syracuseStep 3410249 = 2557687) B2557687
theorem B2273499 : Blo 2273435 2273499 := bstep (se 1 (by rfl) ⟨1705124, by rfl⟩ : syracuseStep 2273499 = 3410249) B3410249
theorem B7283429 : Blo 2273435 7283429 := bbase (se 4 (by rfl) ⟨682821, by rfl⟩ : syracuseStep 7283429 = 1365643) (by norm_num)
theorem B4855619 : Blo 2273435 4855619 := bstep (se 1 (by rfl) ⟨3641714, by rfl⟩ : syracuseStep 4855619 = 7283429) B7283429
theorem B3237079 : Blo 2273435 3237079 := bstep (se 1 (by rfl) ⟨2427809, by rfl⟩ : syracuseStep 3237079 = 4855619) B4855619
theorem B4316105 : Blo 2273435 4316105 := bstep (se 2 (by rfl) ⟨1618539, by rfl⟩ : syracuseStep 4316105 = 3237079) B3237079
theorem B11509613 : Blo 2273435 11509613 := bstep (se 3 (by rfl) ⟨2158052, by rfl⟩ : syracuseStep 11509613 = 4316105) B4316105
theorem B7673075 : Blo 2273435 7673075 := bstep (se 1 (by rfl) ⟨5754806, by rfl⟩ : syracuseStep 7673075 = 11509613) B11509613
theorem B5115383 : Blo 2273435 5115383 := bstep (se 1 (by rfl) ⟨3836537, by rfl⟩ : syracuseStep 5115383 = 7673075) B7673075
theorem B3410255 : Blo 2273435 3410255 := bstep (se 1 (by rfl) ⟨2557691, by rfl⟩ : syracuseStep 3410255 = 5115383) B5115383
theorem B2273503 : Blo 2273435 2273503 := bstep (se 1 (by rfl) ⟨1705127, by rfl⟩ : syracuseStep 2273503 = 3410255) B3410255
theorem B3410261 : Blo 2273435 3410261 := bbase (se 10 (by rfl) ⟨4995, by rfl⟩ : syracuseStep 3410261 = 9991) (by norm_num)
theorem B2273507 : Blo 2273435 2273507 := bstep (se 1 (by rfl) ⟨1705130, by rfl⟩ : syracuseStep 2273507 = 3410261) B3410261
theorem B6474181 : Blo 2273435 6474181 := bbase (se 4 (by rfl) ⟨606954, by rfl⟩ : syracuseStep 6474181 = 1213909) (by norm_num)
theorem B8632241 : Blo 2273435 8632241 := bstep (se 2 (by rfl) ⟨3237090, by rfl⟩ : syracuseStep 8632241 = 6474181) B6474181
theorem B5754827 : Blo 2273435 5754827 := bstep (se 1 (by rfl) ⟨4316120, by rfl⟩ : syracuseStep 5754827 = 8632241) B8632241
theorem B3836551 : Blo 2273435 3836551 := bstep (se 1 (by rfl) ⟨2877413, by rfl⟩ : syracuseStep 3836551 = 5754827) B5754827
theorem B5115401 : Blo 2273435 5115401 := bstep (se 2 (by rfl) ⟨1918275, by rfl⟩ : syracuseStep 5115401 = 3836551) B3836551
theorem B3410267 : Blo 2273435 3410267 := bstep (se 1 (by rfl) ⟨2557700, by rfl⟩ : syracuseStep 3410267 = 5115401) B5115401
theorem B2273511 : Blo 2273435 2273511 := bstep (se 1 (by rfl) ⟨1705133, by rfl⟩ : syracuseStep 2273511 = 3410267) B3410267
theorem B2557705 : Blo 2273435 2557705 := bbase (se 2 (by rfl) ⟨959139, by rfl⟩ : syracuseStep 2557705 = 1918279) (by norm_num)
theorem B3410273 : Blo 2273435 3410273 := bstep (se 2 (by rfl) ⟨1278852, by rfl⟩ : syracuseStep 3410273 = 2557705) B2557705
theorem B2273515 : Blo 2273435 2273515 := bstep (se 1 (by rfl) ⟨1705136, by rfl⟩ : syracuseStep 2273515 = 3410273) B3410273
theorem B16387829 : Blo 2273435 16387829 := bbase (se 5 (by rfl) ⟨768179, by rfl⟩ : syracuseStep 16387829 = 1536359) (by norm_num)
theorem B10925219 : Blo 2273435 10925219 := bstep (se 1 (by rfl) ⟨8193914, by rfl⟩ : syracuseStep 10925219 = 16387829) B16387829
theorem B29133917 : Blo 2273435 29133917 := bstep (se 3 (by rfl) ⟨5462609, by rfl⟩ : syracuseStep 29133917 = 10925219) B10925219
theorem B19422611 : Blo 2273435 19422611 := bstep (se 1 (by rfl) ⟨14566958, by rfl⟩ : syracuseStep 19422611 = 29133917) B29133917
theorem B12948407 : Blo 2273435 12948407 := bstep (se 1 (by rfl) ⟨9711305, by rfl⟩ : syracuseStep 12948407 = 19422611) B19422611
theorem B8632271 : Blo 2273435 8632271 := bstep (se 1 (by rfl) ⟨6474203, by rfl⟩ : syracuseStep 8632271 = 12948407) B12948407
theorem B5754847 : Blo 2273435 5754847 := bstep (se 1 (by rfl) ⟨4316135, by rfl⟩ : syracuseStep 5754847 = 8632271) B8632271
theorem B7673129 : Blo 2273435 7673129 := bstep (se 2 (by rfl) ⟨2877423, by rfl⟩ : syracuseStep 7673129 = 5754847) B5754847
theorem B5115419 : Blo 2273435 5115419 := bstep (se 1 (by rfl) ⟨3836564, by rfl⟩ : syracuseStep 5115419 = 7673129) B7673129
theorem B3410279 : Blo 2273435 3410279 := bstep (se 1 (by rfl) ⟨2557709, by rfl⟩ : syracuseStep 3410279 = 5115419) B5115419
theorem B2273519 : Blo 2273435 2273519 := bstep (se 1 (by rfl) ⟨1705139, by rfl⟩ : syracuseStep 2273519 = 3410279) B3410279
theorem B3410285 : Blo 2273435 3410285 := bbase (se 3 (by rfl) ⟨639428, by rfl⟩ : syracuseStep 3410285 = 1278857) (by norm_num)
theorem B2273523 : Blo 2273435 2273523 := bstep (se 1 (by rfl) ⟨1705142, by rfl⟩ : syracuseStep 2273523 = 3410285) B3410285
theorem B5115437 : Blo 2273435 5115437 := bbase (se 3 (by rfl) ⟨959144, by rfl⟩ : syracuseStep 5115437 = 1918289) (by norm_num)
theorem B3410291 : Blo 2273435 3410291 := bstep (se 1 (by rfl) ⟨2557718, by rfl⟩ : syracuseStep 3410291 = 5115437) B5115437
theorem B2273527 : Blo 2273435 2273527 := bstep (se 1 (by rfl) ⟨1705145, by rfl⟩ : syracuseStep 2273527 = 3410291) B3410291
theorem B224255317 : Blo 2273435 224255317 := bbase (se 11 (by rfl) ⟨164249, by rfl⟩ : syracuseStep 224255317 = 328499) (by norm_num)
theorem B299007089 : Blo 2273435 299007089 := bstep (se 2 (by rfl) ⟨112127658, by rfl⟩ : syracuseStep 299007089 = 224255317) B224255317
theorem B199338059 : Blo 2273435 199338059 := bstep (se 1 (by rfl) ⟨149503544, by rfl⟩ : syracuseStep 199338059 = 299007089) B299007089
theorem B132892039 : Blo 2273435 132892039 := bstep (se 1 (by rfl) ⟨99669029, by rfl⟩ : syracuseStep 132892039 = 199338059) B199338059
theorem B177189385 : Blo 2273435 177189385 := bstep (se 2 (by rfl) ⟨66446019, by rfl⟩ : syracuseStep 177189385 = 132892039) B132892039
theorem B236252513 : Blo 2273435 236252513 := bstep (se 2 (by rfl) ⟨88594692, by rfl⟩ : syracuseStep 236252513 = 177189385) B177189385
theorem B157501675 : Blo 2273435 157501675 := bstep (se 1 (by rfl) ⟨118126256, by rfl⟩ : syracuseStep 157501675 = 236252513) B236252513
theorem B210002233 : Blo 2273435 210002233 := bstep (se 2 (by rfl) ⟨78750837, by rfl⟩ : syracuseStep 210002233 = 157501675) B157501675
theorem B280002977 : Blo 2273435 280002977 := bstep (se 2 (by rfl) ⟨105001116, by rfl⟩ : syracuseStep 280002977 = 210002233) B210002233
theorem B186668651 : Blo 2273435 186668651 := bstep (se 1 (by rfl) ⟨140001488, by rfl⟩ : syracuseStep 186668651 = 280002977) B280002977
theorem B124445767 : Blo 2273435 124445767 := bstep (se 1 (by rfl) ⟨93334325, by rfl⟩ : syracuseStep 124445767 = 186668651) B186668651
theorem B165927689 : Blo 2273435 165927689 := bstep (se 2 (by rfl) ⟨62222883, by rfl⟩ : syracuseStep 165927689 = 124445767) B124445767
theorem B110618459 : Blo 2273435 110618459 := bstep (se 1 (by rfl) ⟨82963844, by rfl⟩ : syracuseStep 110618459 = 165927689) B165927689
theorem B73745639 : Blo 2273435 73745639 := bstep (se 1 (by rfl) ⟨55309229, by rfl⟩ : syracuseStep 73745639 = 110618459) B110618459
theorem B49163759 : Blo 2273435 49163759 := bstep (se 1 (by rfl) ⟨36872819, by rfl⟩ : syracuseStep 49163759 = 73745639) B73745639
theorem B32775839 : Blo 2273435 32775839 := bstep (se 1 (by rfl) ⟨24581879, by rfl⟩ : syracuseStep 32775839 = 49163759) B49163759
theorem B21850559 : Blo 2273435 21850559 := bstep (se 1 (by rfl) ⟨16387919, by rfl⟩ : syracuseStep 21850559 = 32775839) B32775839
theorem B14567039 : Blo 2273435 14567039 := bstep (se 1 (by rfl) ⟨10925279, by rfl⟩ : syracuseStep 14567039 = 21850559) B21850559
theorem B9711359 : Blo 2273435 9711359 := bstep (se 1 (by rfl) ⟨7283519, by rfl⟩ : syracuseStep 9711359 = 14567039) B14567039
theorem B6474239 : Blo 2273435 6474239 := bstep (se 1 (by rfl) ⟨4855679, by rfl⟩ : syracuseStep 6474239 = 9711359) B9711359
theorem B4316159 : Blo 2273435 4316159 := bstep (se 1 (by rfl) ⟨3237119, by rfl⟩ : syracuseStep 4316159 = 6474239) B6474239
theorem B2877439 : Blo 2273435 2877439 := bstep (se 1 (by rfl) ⟨2158079, by rfl⟩ : syracuseStep 2877439 = 4316159) B4316159
theorem B3836585 : Blo 2273435 3836585 := bstep (se 2 (by rfl) ⟨1438719, by rfl⟩ : syracuseStep 3836585 = 2877439) B2877439
theorem B2557723 : Blo 2273435 2557723 := bstep (se 1 (by rfl) ⟨1918292, by rfl⟩ : syracuseStep 2557723 = 3836585) B3836585
theorem B3410297 : Blo 2273435 3410297 := bstep (se 2 (by rfl) ⟨1278861, by rfl⟩ : syracuseStep 3410297 = 2557723) B2557723
theorem B2273531 : Blo 2273435 2273531 := bstep (se 1 (by rfl) ⟨1705148, by rfl⟩ : syracuseStep 2273531 = 3410297) B3410297
theorem B3641765 : Blo 2273435 3641765 := bbase (se 4 (by rfl) ⟨341415, by rfl⟩ : syracuseStep 3641765 = 682831) (by norm_num)
theorem B38845493 : Blo 2273435 38845493 := bstep (se 5 (by rfl) ⟨1820882, by rfl⟩ : syracuseStep 38845493 = 3641765) B3641765
theorem B25896995 : Blo 2273435 25896995 := bstep (se 1 (by rfl) ⟨19422746, by rfl⟩ : syracuseStep 25896995 = 38845493) B38845493
theorem B17264663 : Blo 2273435 17264663 := bstep (se 1 (by rfl) ⟨12948497, by rfl⟩ : syracuseStep 17264663 = 25896995) B25896995
theorem B11509775 : Blo 2273435 11509775 := bstep (se 1 (by rfl) ⟨8632331, by rfl⟩ : syracuseStep 11509775 = 17264663) B17264663
theorem B7673183 : Blo 2273435 7673183 := bstep (se 1 (by rfl) ⟨5754887, by rfl⟩ : syracuseStep 7673183 = 11509775) B11509775
theorem B5115455 : Blo 2273435 5115455 := bstep (se 1 (by rfl) ⟨3836591, by rfl⟩ : syracuseStep 5115455 = 7673183) B7673183
theorem B3410303 : Blo 2273435 3410303 := bstep (se 1 (by rfl) ⟨2557727, by rfl⟩ : syracuseStep 3410303 = 5115455) B5115455
theorem B2273535 : Blo 2273435 2273535 := bstep (se 1 (by rfl) ⟨1705151, by rfl⟩ : syracuseStep 2273535 = 3410303) B3410303
theorem B3410309 : Blo 2273435 3410309 := bbase (se 4 (by rfl) ⟨319716, by rfl⟩ : syracuseStep 3410309 = 639433) (by norm_num)
theorem B2273539 : Blo 2273435 2273539 := bstep (se 1 (by rfl) ⟨1705154, by rfl⟩ : syracuseStep 2273539 = 3410309) B3410309
theorem B3836605 : Blo 2273435 3836605 := bbase (se 3 (by rfl) ⟨719363, by rfl⟩ : syracuseStep 3836605 = 1438727) (by norm_num)
theorem B5115473 : Blo 2273435 5115473 := bstep (se 2 (by rfl) ⟨1918302, by rfl⟩ : syracuseStep 5115473 = 3836605) B3836605
theorem B3410315 : Blo 2273435 3410315 := bstep (se 1 (by rfl) ⟨2557736, by rfl⟩ : syracuseStep 3410315 = 5115473) B5115473
theorem B2273543 : Blo 2273435 2273543 := bstep (se 1 (by rfl) ⟨1705157, by rfl⟩ : syracuseStep 2273543 = 3410315) B3410315
theorem B2557741 : Blo 2273435 2557741 := bbase (se 3 (by rfl) ⟨479576, by rfl⟩ : syracuseStep 2557741 = 959153) (by norm_num)
theorem B3410321 : Blo 2273435 3410321 := bstep (se 2 (by rfl) ⟨1278870, by rfl⟩ : syracuseStep 3410321 = 2557741) B2557741
theorem B2273547 : Blo 2273435 2273547 := bstep (se 1 (by rfl) ⟨1705160, by rfl⟩ : syracuseStep 2273547 = 3410321) B3410321
theorem B7673237 : Blo 2273435 7673237 := bbase (se 6 (by rfl) ⟨179841, by rfl⟩ : syracuseStep 7673237 = 359683) (by norm_num)
theorem B5115491 : Blo 2273435 5115491 := bstep (se 1 (by rfl) ⟨3836618, by rfl⟩ : syracuseStep 5115491 = 7673237) B7673237
theorem B3410327 : Blo 2273435 3410327 := bstep (se 1 (by rfl) ⟨2557745, by rfl⟩ : syracuseStep 3410327 = 5115491) B5115491
theorem B2273551 : Blo 2273435 2273551 := bstep (se 1 (by rfl) ⟨1705163, by rfl⟩ : syracuseStep 2273551 = 3410327) B3410327
theorem B3410333 : Blo 2273435 3410333 := bbase (se 3 (by rfl) ⟨639437, by rfl⟩ : syracuseStep 3410333 = 1278875) (by norm_num)
theorem B2273555 : Blo 2273435 2273555 := bstep (se 1 (by rfl) ⟨1705166, by rfl⟩ : syracuseStep 2273555 = 3410333) B3410333
theorem B5115509 : Blo 2273435 5115509 := bbase (se 5 (by rfl) ⟨239789, by rfl⟩ : syracuseStep 5115509 = 479579) (by norm_num)
theorem B3410339 : Blo 2273435 3410339 := bstep (se 1 (by rfl) ⟨2557754, by rfl⟩ : syracuseStep 3410339 = 5115509) B5115509
theorem B2273559 : Blo 2273435 2273559 := bstep (se 1 (by rfl) ⟨1705169, by rfl⟩ : syracuseStep 2273559 = 3410339) B3410339
theorem B7283621 : Blo 2273435 7283621 := bbase (se 4 (by rfl) ⟨682839, by rfl⟩ : syracuseStep 7283621 = 1365679) (by norm_num)
theorem B19422989 : Blo 2273435 19422989 := bstep (se 3 (by rfl) ⟨3641810, by rfl⟩ : syracuseStep 19422989 = 7283621) B7283621
theorem B12948659 : Blo 2273435 12948659 := bstep (se 1 (by rfl) ⟨9711494, by rfl⟩ : syracuseStep 12948659 = 19422989) B19422989
theorem B8632439 : Blo 2273435 8632439 := bstep (se 1 (by rfl) ⟨6474329, by rfl⟩ : syracuseStep 8632439 = 12948659) B12948659
theorem B5754959 : Blo 2273435 5754959 := bstep (se 1 (by rfl) ⟨4316219, by rfl⟩ : syracuseStep 5754959 = 8632439) B8632439
theorem B3836639 : Blo 2273435 3836639 := bstep (se 1 (by rfl) ⟨2877479, by rfl⟩ : syracuseStep 3836639 = 5754959) B5754959
theorem B2557759 : Blo 2273435 2557759 := bstep (se 1 (by rfl) ⟨1918319, by rfl⟩ : syracuseStep 2557759 = 3836639) B3836639
theorem B3410345 : Blo 2273435 3410345 := bstep (se 2 (by rfl) ⟨1278879, by rfl⟩ : syracuseStep 3410345 = 2557759) B2557759
theorem B2273563 : Blo 2273435 2273563 := bstep (se 1 (by rfl) ⟨1705172, by rfl⟩ : syracuseStep 2273563 = 3410345) B3410345
theorem B8632453 : Blo 2273435 8632453 := bbase (se 4 (by rfl) ⟨809292, by rfl⟩ : syracuseStep 8632453 = 1618585) (by norm_num)
theorem B11509937 : Blo 2273435 11509937 := bstep (se 2 (by rfl) ⟨4316226, by rfl⟩ : syracuseStep 11509937 = 8632453) B8632453
theorem B7673291 : Blo 2273435 7673291 := bstep (se 1 (by rfl) ⟨5754968, by rfl⟩ : syracuseStep 7673291 = 11509937) B11509937
theorem B5115527 : Blo 2273435 5115527 := bstep (se 1 (by rfl) ⟨3836645, by rfl⟩ : syracuseStep 5115527 = 7673291) B7673291
theorem B3410351 : Blo 2273435 3410351 := bstep (se 1 (by rfl) ⟨2557763, by rfl⟩ : syracuseStep 3410351 = 5115527) B5115527
theorem B2273567 : Blo 2273435 2273567 := bstep (se 1 (by rfl) ⟨1705175, by rfl⟩ : syracuseStep 2273567 = 3410351) B3410351
theorem B3410357 : Blo 2273435 3410357 := bbase (se 5 (by rfl) ⟨159860, by rfl⟩ : syracuseStep 3410357 = 319721) (by norm_num)
theorem B2273571 : Blo 2273435 2273571 := bstep (se 1 (by rfl) ⟨1705178, by rfl⟩ : syracuseStep 2273571 = 3410357) B3410357
theorem B5754989 : Blo 2273435 5754989 := bbase (se 3 (by rfl) ⟨1079060, by rfl⟩ : syracuseStep 5754989 = 2158121) (by norm_num)
theorem B3836659 : Blo 2273435 3836659 := bstep (se 1 (by rfl) ⟨2877494, by rfl⟩ : syracuseStep 3836659 = 5754989) B5754989
theorem B5115545 : Blo 2273435 5115545 := bstep (se 2 (by rfl) ⟨1918329, by rfl⟩ : syracuseStep 5115545 = 3836659) B3836659
theorem B3410363 : Blo 2273435 3410363 := bstep (se 1 (by rfl) ⟨2557772, by rfl⟩ : syracuseStep 3410363 = 5115545) B5115545
theorem B2273575 : Blo 2273435 2273575 := bstep (se 1 (by rfl) ⟨1705181, by rfl⟩ : syracuseStep 2273575 = 3410363) B3410363
theorem B2557777 : Blo 2273435 2557777 := bbase (se 2 (by rfl) ⟨959166, by rfl⟩ : syracuseStep 2557777 = 1918333) (by norm_num)
theorem B3410369 : Blo 2273435 3410369 := bstep (se 2 (by rfl) ⟨1278888, by rfl⟩ : syracuseStep 3410369 = 2557777) B2557777
theorem B2273579 : Blo 2273435 2273579 := bstep (se 1 (by rfl) ⟨1705184, by rfl⟩ : syracuseStep 2273579 = 3410369) B3410369
theorem B5462765 : Blo 2273435 5462765 := bbase (se 3 (by rfl) ⟨1024268, by rfl⟩ : syracuseStep 5462765 = 2048537) (by norm_num)
theorem B3641843 : Blo 2273435 3641843 := bstep (se 1 (by rfl) ⟨2731382, by rfl⟩ : syracuseStep 3641843 = 5462765) B5462765
theorem B2427895 : Blo 2273435 2427895 := bstep (se 1 (by rfl) ⟨1820921, by rfl⟩ : syracuseStep 2427895 = 3641843) B3641843
theorem B3237193 : Blo 2273435 3237193 := bstep (se 2 (by rfl) ⟨1213947, by rfl⟩ : syracuseStep 3237193 = 2427895) B2427895
theorem B4316257 : Blo 2273435 4316257 := bstep (se 2 (by rfl) ⟨1618596, by rfl⟩ : syracuseStep 4316257 = 3237193) B3237193
theorem B5755009 : Blo 2273435 5755009 := bstep (se 2 (by rfl) ⟨2158128, by rfl⟩ : syracuseStep 5755009 = 4316257) B4316257
theorem B7673345 : Blo 2273435 7673345 := bstep (se 2 (by rfl) ⟨2877504, by rfl⟩ : syracuseStep 7673345 = 5755009) B5755009
theorem B5115563 : Blo 2273435 5115563 := bstep (se 1 (by rfl) ⟨3836672, by rfl⟩ : syracuseStep 5115563 = 7673345) B7673345
theorem B3410375 : Blo 2273435 3410375 := bstep (se 1 (by rfl) ⟨2557781, by rfl⟩ : syracuseStep 3410375 = 5115563) B5115563
theorem B2273583 : Blo 2273435 2273583 := bstep (se 1 (by rfl) ⟨1705187, by rfl⟩ : syracuseStep 2273583 = 3410375) B3410375
theorem B3410381 : Blo 2273435 3410381 := bbase (se 3 (by rfl) ⟨639446, by rfl⟩ : syracuseStep 3410381 = 1278893) (by norm_num)
theorem B2273587 : Blo 2273435 2273587 := bstep (se 1 (by rfl) ⟨1705190, by rfl⟩ : syracuseStep 2273587 = 3410381) B3410381
theorem B5115581 : Blo 2273435 5115581 := bbase (se 3 (by rfl) ⟨959171, by rfl⟩ : syracuseStep 5115581 = 1918343) (by norm_num)
theorem B3410387 : Blo 2273435 3410387 := bstep (se 1 (by rfl) ⟨2557790, by rfl⟩ : syracuseStep 3410387 = 5115581) B5115581
theorem B2273591 : Blo 2273435 2273591 := bstep (se 1 (by rfl) ⟨1705193, by rfl⟩ : syracuseStep 2273591 = 3410387) B3410387
theorem B3836693 : Blo 2273435 3836693 := bbase (se 6 (by rfl) ⟨89922, by rfl⟩ : syracuseStep 3836693 = 179845) (by norm_num)
theorem B2557795 : Blo 2273435 2557795 := bstep (se 1 (by rfl) ⟨1918346, by rfl⟩ : syracuseStep 2557795 = 3836693) B3836693
theorem B3410393 : Blo 2273435 3410393 := bstep (se 2 (by rfl) ⟨1278897, by rfl⟩ : syracuseStep 3410393 = 2557795) B2557795
theorem B2273595 : Blo 2273435 2273595 := bstep (se 1 (by rfl) ⟨1705196, by rfl⟩ : syracuseStep 2273595 = 3410393) B3410393
theorem B2461037 : Blo 2273435 2461037 := bbase (se 3 (by rfl) ⟨461444, by rfl⟩ : syracuseStep 2461037 = 922889) (by norm_num)
theorem B6562765 : Blo 2273435 6562765 := bstep (se 3 (by rfl) ⟨1230518, by rfl⟩ : syracuseStep 6562765 = 2461037) B2461037
theorem B8750353 : Blo 2273435 8750353 := bstep (se 2 (by rfl) ⟨3281382, by rfl⟩ : syracuseStep 8750353 = 6562765) B6562765
theorem B11667137 : Blo 2273435 11667137 := bstep (se 2 (by rfl) ⟨4375176, by rfl⟩ : syracuseStep 11667137 = 8750353) B8750353
theorem B31112365 : Blo 2273435 31112365 := bstep (se 3 (by rfl) ⟨5833568, by rfl⟩ : syracuseStep 31112365 = 11667137) B11667137
theorem B41483153 : Blo 2273435 41483153 := bstep (se 2 (by rfl) ⟨15556182, by rfl⟩ : syracuseStep 41483153 = 31112365) B31112365
theorem B27655435 : Blo 2273435 27655435 := bstep (se 1 (by rfl) ⟨20741576, by rfl⟩ : syracuseStep 27655435 = 41483153) B41483153
theorem B36873913 : Blo 2273435 36873913 := bstep (se 2 (by rfl) ⟨13827717, by rfl⟩ : syracuseStep 36873913 = 27655435) B27655435
theorem B49165217 : Blo 2273435 49165217 := bstep (se 2 (by rfl) ⟨18436956, by rfl⟩ : syracuseStep 49165217 = 36873913) B36873913
theorem B32776811 : Blo 2273435 32776811 := bstep (se 1 (by rfl) ⟨24582608, by rfl⟩ : syracuseStep 32776811 = 49165217) B49165217
theorem B21851207 : Blo 2273435 21851207 := bstep (se 1 (by rfl) ⟨16388405, by rfl⟩ : syracuseStep 21851207 = 32776811) B32776811
theorem B14567471 : Blo 2273435 14567471 := bstep (se 1 (by rfl) ⟨10925603, by rfl⟩ : syracuseStep 14567471 = 21851207) B21851207
theorem B9711647 : Blo 2273435 9711647 := bstep (se 1 (by rfl) ⟨7283735, by rfl⟩ : syracuseStep 9711647 = 14567471) B14567471
theorem B6474431 : Blo 2273435 6474431 := bstep (se 1 (by rfl) ⟨4855823, by rfl⟩ : syracuseStep 6474431 = 9711647) B9711647
theorem B17265149 : Blo 2273435 17265149 := bstep (se 3 (by rfl) ⟨3237215, by rfl⟩ : syracuseStep 17265149 = 6474431) B6474431
theorem B11510099 : Blo 2273435 11510099 := bstep (se 1 (by rfl) ⟨8632574, by rfl⟩ : syracuseStep 11510099 = 17265149) B17265149
theorem B7673399 : Blo 2273435 7673399 := bstep (se 1 (by rfl) ⟨5755049, by rfl⟩ : syracuseStep 7673399 = 11510099) B11510099
theorem B5115599 : Blo 2273435 5115599 := bstep (se 1 (by rfl) ⟨3836699, by rfl⟩ : syracuseStep 5115599 = 7673399) B7673399
theorem B3410399 : Blo 2273435 3410399 := bstep (se 1 (by rfl) ⟨2557799, by rfl⟩ : syracuseStep 3410399 = 5115599) B5115599
theorem B2273599 : Blo 2273435 2273599 := bstep (se 1 (by rfl) ⟨1705199, by rfl⟩ : syracuseStep 2273599 = 3410399) B3410399
theorem B3410405 : Blo 2273435 3410405 := bbase (se 4 (by rfl) ⟨319725, by rfl⟩ : syracuseStep 3410405 = 639451) (by norm_num)
theorem B2273603 : Blo 2273435 2273603 := bstep (se 1 (by rfl) ⟨1705202, by rfl⟩ : syracuseStep 2273603 = 3410405) B3410405
theorem B4097117 : Blo 2273435 4097117 := bbase (se 3 (by rfl) ⟨768209, by rfl⟩ : syracuseStep 4097117 = 1536419) (by norm_num)
theorem B2731411 : Blo 2273435 2731411 := bstep (se 1 (by rfl) ⟨2048558, by rfl⟩ : syracuseStep 2731411 = 4097117) B4097117
theorem B14567525 : Blo 2273435 14567525 := bstep (se 4 (by rfl) ⟨1365705, by rfl⟩ : syracuseStep 14567525 = 2731411) B2731411
theorem B9711683 : Blo 2273435 9711683 := bstep (se 1 (by rfl) ⟨7283762, by rfl⟩ : syracuseStep 9711683 = 14567525) B14567525
theorem B6474455 : Blo 2273435 6474455 := bstep (se 1 (by rfl) ⟨4855841, by rfl⟩ : syracuseStep 6474455 = 9711683) B9711683
theorem B4316303 : Blo 2273435 4316303 := bstep (se 1 (by rfl) ⟨3237227, by rfl⟩ : syracuseStep 4316303 = 6474455) B6474455
theorem B2877535 : Blo 2273435 2877535 := bstep (se 1 (by rfl) ⟨2158151, by rfl⟩ : syracuseStep 2877535 = 4316303) B4316303
theorem B3836713 : Blo 2273435 3836713 := bstep (se 2 (by rfl) ⟨1438767, by rfl⟩ : syracuseStep 3836713 = 2877535) B2877535
theorem B5115617 : Blo 2273435 5115617 := bstep (se 2 (by rfl) ⟨1918356, by rfl⟩ : syracuseStep 5115617 = 3836713) B3836713
theorem B3410411 : Blo 2273435 3410411 := bstep (se 1 (by rfl) ⟨2557808, by rfl⟩ : syracuseStep 3410411 = 5115617) B5115617
theorem B2273607 : Blo 2273435 2273607 := bstep (se 1 (by rfl) ⟨1705205, by rfl⟩ : syracuseStep 2273607 = 3410411) B3410411
theorem B2557813 : Blo 2273435 2557813 := bbase (se 5 (by rfl) ⟨119897, by rfl⟩ : syracuseStep 2557813 = 239795) (by norm_num)
theorem B3410417 : Blo 2273435 3410417 := bstep (se 2 (by rfl) ⟨1278906, by rfl⟩ : syracuseStep 3410417 = 2557813) B2557813
theorem B2273611 : Blo 2273435 2273611 := bstep (se 1 (by rfl) ⟨1705208, by rfl⟩ : syracuseStep 2273611 = 3410417) B3410417
theorem B2877545 : Blo 2273435 2877545 := bbase (se 2 (by rfl) ⟨1079079, by rfl⟩ : syracuseStep 2877545 = 2158159) (by norm_num)
theorem B7673453 : Blo 2273435 7673453 := bstep (se 3 (by rfl) ⟨1438772, by rfl⟩ : syracuseStep 7673453 = 2877545) B2877545
theorem B5115635 : Blo 2273435 5115635 := bstep (se 1 (by rfl) ⟨3836726, by rfl⟩ : syracuseStep 5115635 = 7673453) B7673453
theorem B3410423 : Blo 2273435 3410423 := bstep (se 1 (by rfl) ⟨2557817, by rfl⟩ : syracuseStep 3410423 = 5115635) B5115635
theorem B2273615 : Blo 2273435 2273615 := bstep (se 1 (by rfl) ⟨1705211, by rfl⟩ : syracuseStep 2273615 = 3410423) B3410423
theorem B3410429 : Blo 2273435 3410429 := bbase (se 3 (by rfl) ⟨639455, by rfl⟩ : syracuseStep 3410429 = 1278911) (by norm_num)
theorem B2273619 : Blo 2273435 2273619 := bstep (se 1 (by rfl) ⟨1705214, by rfl⟩ : syracuseStep 2273619 = 3410429) B3410429
theorem B5115653 : Blo 2273435 5115653 := bbase (se 4 (by rfl) ⟨479592, by rfl⟩ : syracuseStep 5115653 = 959185) (by norm_num)
theorem B3410435 : Blo 2273435 3410435 := bstep (se 1 (by rfl) ⟨2557826, by rfl⟩ : syracuseStep 3410435 = 5115653) B5115653
theorem B2273623 : Blo 2273435 2273623 := bstep (se 1 (by rfl) ⟨1705217, by rfl⟩ : syracuseStep 2273623 = 3410435) B3410435
theorem B4316341 : Blo 2273435 4316341 := bbase (se 5 (by rfl) ⟨202328, by rfl⟩ : syracuseStep 4316341 = 404657) (by norm_num)
theorem B5755121 : Blo 2273435 5755121 := bstep (se 2 (by rfl) ⟨2158170, by rfl⟩ : syracuseStep 5755121 = 4316341) B4316341
theorem B3836747 : Blo 2273435 3836747 := bstep (se 1 (by rfl) ⟨2877560, by rfl⟩ : syracuseStep 3836747 = 5755121) B5755121
theorem B2557831 : Blo 2273435 2557831 := bstep (se 1 (by rfl) ⟨1918373, by rfl⟩ : syracuseStep 2557831 = 3836747) B3836747
theorem B3410441 : Blo 2273435 3410441 := bstep (se 2 (by rfl) ⟨1278915, by rfl⟩ : syracuseStep 3410441 = 2557831) B2557831
theorem B2273627 : Blo 2273435 2273627 := bstep (se 1 (by rfl) ⟨1705220, by rfl⟩ : syracuseStep 2273627 = 3410441) B3410441
theorem B11510261 : Blo 2273435 11510261 := bbase (se 5 (by rfl) ⟨539543, by rfl⟩ : syracuseStep 11510261 = 1079087) (by norm_num)
theorem B7673507 : Blo 2273435 7673507 := bstep (se 1 (by rfl) ⟨5755130, by rfl⟩ : syracuseStep 7673507 = 11510261) B11510261
theorem B5115671 : Blo 2273435 5115671 := bstep (se 1 (by rfl) ⟨3836753, by rfl⟩ : syracuseStep 5115671 = 7673507) B7673507
theorem B3410447 : Blo 2273435 3410447 := bstep (se 1 (by rfl) ⟨2557835, by rfl⟩ : syracuseStep 3410447 = 5115671) B5115671
theorem B2273631 : Blo 2273435 2273631 := bstep (se 1 (by rfl) ⟨1705223, by rfl⟩ : syracuseStep 2273631 = 3410447) B3410447
theorem B3410453 : Blo 2273435 3410453 := bbase (se 6 (by rfl) ⟨79932, by rfl⟩ : syracuseStep 3410453 = 159865) (by norm_num)
theorem B2273635 : Blo 2273435 2273635 := bstep (se 1 (by rfl) ⟨1705226, by rfl⟩ : syracuseStep 2273635 = 3410453) B3410453
theorem B19423637 : Blo 2273435 19423637 := bbase (se 6 (by rfl) ⟨455241, by rfl⟩ : syracuseStep 19423637 = 910483) (by norm_num)
theorem B12949091 : Blo 2273435 12949091 := bstep (se 1 (by rfl) ⟨9711818, by rfl⟩ : syracuseStep 12949091 = 19423637) B19423637
theorem B8632727 : Blo 2273435 8632727 := bstep (se 1 (by rfl) ⟨6474545, by rfl⟩ : syracuseStep 8632727 = 12949091) B12949091
theorem B5755151 : Blo 2273435 5755151 := bstep (se 1 (by rfl) ⟨4316363, by rfl⟩ : syracuseStep 5755151 = 8632727) B8632727
theorem B3836767 : Blo 2273435 3836767 := bstep (se 1 (by rfl) ⟨2877575, by rfl⟩ : syracuseStep 3836767 = 5755151) B5755151
theorem B5115689 : Blo 2273435 5115689 := bstep (se 2 (by rfl) ⟨1918383, by rfl⟩ : syracuseStep 5115689 = 3836767) B3836767
theorem B3410459 : Blo 2273435 3410459 := bstep (se 1 (by rfl) ⟨2557844, by rfl⟩ : syracuseStep 3410459 = 5115689) B5115689
theorem B2273639 : Blo 2273435 2273639 := bstep (se 1 (by rfl) ⟨1705229, by rfl⟩ : syracuseStep 2273639 = 3410459) B3410459
theorem B2557849 : Blo 2273435 2557849 := bbase (se 2 (by rfl) ⟨959193, by rfl⟩ : syracuseStep 2557849 = 1918387) (by norm_num)
theorem B3410465 : Blo 2273435 3410465 := bstep (se 2 (by rfl) ⟨1278924, by rfl⟩ : syracuseStep 3410465 = 2557849) B2557849
theorem B2273643 : Blo 2273435 2273643 := bstep (se 1 (by rfl) ⟨1705232, by rfl⟩ : syracuseStep 2273643 = 3410465) B3410465
theorem B8632757 : Blo 2273435 8632757 := bbase (se 5 (by rfl) ⟨404660, by rfl⟩ : syracuseStep 8632757 = 809321) (by norm_num)
theorem B5755171 : Blo 2273435 5755171 := bstep (se 1 (by rfl) ⟨4316378, by rfl⟩ : syracuseStep 5755171 = 8632757) B8632757
theorem B7673561 : Blo 2273435 7673561 := bstep (se 2 (by rfl) ⟨2877585, by rfl⟩ : syracuseStep 7673561 = 5755171) B5755171
theorem B5115707 : Blo 2273435 5115707 := bstep (se 1 (by rfl) ⟨3836780, by rfl⟩ : syracuseStep 5115707 = 7673561) B7673561
theorem B3410471 : Blo 2273435 3410471 := bstep (se 1 (by rfl) ⟨2557853, by rfl⟩ : syracuseStep 3410471 = 5115707) B5115707
theorem B2273647 : Blo 2273435 2273647 := bstep (se 1 (by rfl) ⟨1705235, by rfl⟩ : syracuseStep 2273647 = 3410471) B3410471
theorem B3410477 : Blo 2273435 3410477 := bbase (se 3 (by rfl) ⟨639464, by rfl⟩ : syracuseStep 3410477 = 1278929) (by norm_num)
theorem B2273651 : Blo 2273435 2273651 := bstep (se 1 (by rfl) ⟨1705238, by rfl⟩ : syracuseStep 2273651 = 3410477) B3410477
theorem B5115725 : Blo 2273435 5115725 := bbase (se 3 (by rfl) ⟨959198, by rfl⟩ : syracuseStep 5115725 = 1918397) (by norm_num)
theorem B3410483 : Blo 2273435 3410483 := bstep (se 1 (by rfl) ⟨2557862, by rfl⟩ : syracuseStep 3410483 = 5115725) B5115725
theorem B2273655 : Blo 2273435 2273655 := bstep (se 1 (by rfl) ⟨1705241, by rfl⟩ : syracuseStep 2273655 = 3410483) B3410483
theorem B2877601 : Blo 2273435 2877601 := bbase (se 2 (by rfl) ⟨1079100, by rfl⟩ : syracuseStep 2877601 = 2158201) (by norm_num)
theorem B3836801 : Blo 2273435 3836801 := bstep (se 2 (by rfl) ⟨1438800, by rfl⟩ : syracuseStep 3836801 = 2877601) B2877601
theorem B2557867 : Blo 2273435 2557867 := bstep (se 1 (by rfl) ⟨1918400, by rfl⟩ : syracuseStep 2557867 = 3836801) B3836801
theorem B3410489 : Blo 2273435 3410489 := bstep (se 2 (by rfl) ⟨1278933, by rfl⟩ : syracuseStep 3410489 = 2557867) B2557867
theorem B2273659 : Blo 2273435 2273659 := bstep (se 1 (by rfl) ⟨1705244, by rfl⟩ : syracuseStep 2273659 = 3410489) B3410489
theorem B25898453 : Blo 2273435 25898453 := bbase (se 7 (by rfl) ⟨303497, by rfl⟩ : syracuseStep 25898453 = 606995) (by norm_num)
theorem B17265635 : Blo 2273435 17265635 := bstep (se 1 (by rfl) ⟨12949226, by rfl⟩ : syracuseStep 17265635 = 25898453) B25898453
theorem B11510423 : Blo 2273435 11510423 := bstep (se 1 (by rfl) ⟨8632817, by rfl⟩ : syracuseStep 11510423 = 17265635) B17265635
theorem B7673615 : Blo 2273435 7673615 := bstep (se 1 (by rfl) ⟨5755211, by rfl⟩ : syracuseStep 7673615 = 11510423) B11510423
theorem B5115743 : Blo 2273435 5115743 := bstep (se 1 (by rfl) ⟨3836807, by rfl⟩ : syracuseStep 5115743 = 7673615) B7673615
theorem B3410495 : Blo 2273435 3410495 := bstep (se 1 (by rfl) ⟨2557871, by rfl⟩ : syracuseStep 3410495 = 5115743) B5115743
theorem B2273663 : Blo 2273435 2273663 := bstep (se 1 (by rfl) ⟨1705247, by rfl⟩ : syracuseStep 2273663 = 3410495) B3410495
theorem B3410501 : Blo 2273435 3410501 := bbase (se 4 (by rfl) ⟨319734, by rfl⟩ : syracuseStep 3410501 = 639469) (by norm_num)
theorem B2273667 : Blo 2273435 2273667 := bstep (se 1 (by rfl) ⟨1705250, by rfl⟩ : syracuseStep 2273667 = 3410501) B3410501
theorem B3836821 : Blo 2273435 3836821 := bbase (se 6 (by rfl) ⟨89925, by rfl⟩ : syracuseStep 3836821 = 179851) (by norm_num)
theorem B5115761 : Blo 2273435 5115761 := bstep (se 2 (by rfl) ⟨1918410, by rfl⟩ : syracuseStep 5115761 = 3836821) B3836821
theorem B3410507 : Blo 2273435 3410507 := bstep (se 1 (by rfl) ⟨2557880, by rfl⟩ : syracuseStep 3410507 = 5115761) B5115761
theorem B2273671 : Blo 2273435 2273671 := bstep (se 1 (by rfl) ⟨1705253, by rfl⟩ : syracuseStep 2273671 = 3410507) B3410507
theorem B2557885 : Blo 2273435 2557885 := bbase (se 3 (by rfl) ⟨479603, by rfl⟩ : syracuseStep 2557885 = 959207) (by norm_num)
theorem B3410513 : Blo 2273435 3410513 := bstep (se 2 (by rfl) ⟨1278942, by rfl⟩ : syracuseStep 3410513 = 2557885) B2557885
theorem B2273675 : Blo 2273435 2273675 := bstep (se 1 (by rfl) ⟨1705256, by rfl⟩ : syracuseStep 2273675 = 3410513) B3410513
theorem B7673669 : Blo 2273435 7673669 := bbase (se 4 (by rfl) ⟨719406, by rfl⟩ : syracuseStep 7673669 = 1438813) (by norm_num)
theorem B5115779 : Blo 2273435 5115779 := bstep (se 1 (by rfl) ⟨3836834, by rfl⟩ : syracuseStep 5115779 = 7673669) B7673669
theorem B3410519 : Blo 2273435 3410519 := bstep (se 1 (by rfl) ⟨2557889, by rfl⟩ : syracuseStep 3410519 = 5115779) B5115779
theorem B2273679 : Blo 2273435 2273679 := bstep (se 1 (by rfl) ⟨1705259, by rfl⟩ : syracuseStep 2273679 = 3410519) B3410519
theorem B3410525 : Blo 2273435 3410525 := bbase (se 3 (by rfl) ⟨639473, by rfl⟩ : syracuseStep 3410525 = 1278947) (by norm_num)
theorem B2273683 : Blo 2273435 2273683 := bstep (se 1 (by rfl) ⟨1705262, by rfl⟩ : syracuseStep 2273683 = 3410525) B3410525
theorem B5115797 : Blo 2273435 5115797 := bbase (se 6 (by rfl) ⟨119901, by rfl⟩ : syracuseStep 5115797 = 239803) (by norm_num)
theorem B3410531 : Blo 2273435 3410531 := bstep (se 1 (by rfl) ⟨2557898, by rfl⟩ : syracuseStep 3410531 = 5115797) B5115797
theorem B2273687 : Blo 2273435 2273687 := bstep (se 1 (by rfl) ⟨1705265, by rfl⟩ : syracuseStep 2273687 = 3410531) B3410531
theorem B4856021 : Blo 2273435 4856021 := bbase (se 7 (by rfl) ⟨56906, by rfl⟩ : syracuseStep 4856021 = 113813) (by norm_num)
theorem B3237347 : Blo 2273435 3237347 := bstep (se 1 (by rfl) ⟨2428010, by rfl⟩ : syracuseStep 3237347 = 4856021) B4856021
theorem B8632925 : Blo 2273435 8632925 := bstep (se 3 (by rfl) ⟨1618673, by rfl⟩ : syracuseStep 8632925 = 3237347) B3237347
theorem B5755283 : Blo 2273435 5755283 := bstep (se 1 (by rfl) ⟨4316462, by rfl⟩ : syracuseStep 5755283 = 8632925) B8632925
theorem B3836855 : Blo 2273435 3836855 := bstep (se 1 (by rfl) ⟨2877641, by rfl⟩ : syracuseStep 3836855 = 5755283) B5755283
theorem B2557903 : Blo 2273435 2557903 := bstep (se 1 (by rfl) ⟨1918427, by rfl⟩ : syracuseStep 2557903 = 3836855) B3836855
theorem B3410537 : Blo 2273435 3410537 := bstep (se 2 (by rfl) ⟨1278951, by rfl⟩ : syracuseStep 3410537 = 2557903) B2557903
theorem B2273691 : Blo 2273435 2273691 := bstep (se 1 (by rfl) ⟨1705268, by rfl⟩ : syracuseStep 2273691 = 3410537) B3410537
theorem B8194549 : Blo 2273435 8194549 := bbase (se 5 (by rfl) ⟨384119, by rfl⟩ : syracuseStep 8194549 = 768239) (by norm_num)
theorem B10926065 : Blo 2273435 10926065 := bstep (se 2 (by rfl) ⟨4097274, by rfl⟩ : syracuseStep 10926065 = 8194549) B8194549
theorem B7284043 : Blo 2273435 7284043 := bstep (se 1 (by rfl) ⟨5463032, by rfl⟩ : syracuseStep 7284043 = 10926065) B10926065
theorem B9712057 : Blo 2273435 9712057 := bstep (se 2 (by rfl) ⟨3642021, by rfl⟩ : syracuseStep 9712057 = 7284043) B7284043
theorem B12949409 : Blo 2273435 12949409 := bstep (se 2 (by rfl) ⟨4856028, by rfl⟩ : syracuseStep 12949409 = 9712057) B9712057
theorem B8632939 : Blo 2273435 8632939 := bstep (se 1 (by rfl) ⟨6474704, by rfl⟩ : syracuseStep 8632939 = 12949409) B12949409
theorem B11510585 : Blo 2273435 11510585 := bstep (se 2 (by rfl) ⟨4316469, by rfl⟩ : syracuseStep 11510585 = 8632939) B8632939
theorem B7673723 : Blo 2273435 7673723 := bstep (se 1 (by rfl) ⟨5755292, by rfl⟩ : syracuseStep 7673723 = 11510585) B11510585
theorem B5115815 : Blo 2273435 5115815 := bstep (se 1 (by rfl) ⟨3836861, by rfl⟩ : syracuseStep 5115815 = 7673723) B7673723
theorem B3410543 : Blo 2273435 3410543 := bstep (se 1 (by rfl) ⟨2557907, by rfl⟩ : syracuseStep 3410543 = 5115815) B5115815
theorem B2273695 : Blo 2273435 2273695 := bstep (se 1 (by rfl) ⟨1705271, by rfl⟩ : syracuseStep 2273695 = 3410543) B3410543
theorem B3410549 : Blo 2273435 3410549 := bbase (se 5 (by rfl) ⟨159869, by rfl⟩ : syracuseStep 3410549 = 319739) (by norm_num)
theorem B2273699 : Blo 2273435 2273699 := bstep (se 1 (by rfl) ⟨1705274, by rfl⟩ : syracuseStep 2273699 = 3410549) B3410549
theorem B4316485 : Blo 2273435 4316485 := bbase (se 4 (by rfl) ⟨404670, by rfl⟩ : syracuseStep 4316485 = 809341) (by norm_num)
theorem B5755313 : Blo 2273435 5755313 := bstep (se 2 (by rfl) ⟨2158242, by rfl⟩ : syracuseStep 5755313 = 4316485) B4316485
theorem B3836875 : Blo 2273435 3836875 := bstep (se 1 (by rfl) ⟨2877656, by rfl⟩ : syracuseStep 3836875 = 5755313) B5755313
theorem B5115833 : Blo 2273435 5115833 := bstep (se 2 (by rfl) ⟨1918437, by rfl⟩ : syracuseStep 5115833 = 3836875) B3836875
theorem B3410555 : Blo 2273435 3410555 := bstep (se 1 (by rfl) ⟨2557916, by rfl⟩ : syracuseStep 3410555 = 5115833) B5115833
theorem B2273703 : Blo 2273435 2273703 := bstep (se 1 (by rfl) ⟨1705277, by rfl⟩ : syracuseStep 2273703 = 3410555) B3410555
theorem B2557921 : Blo 2273435 2557921 := bbase (se 2 (by rfl) ⟨959220, by rfl⟩ : syracuseStep 2557921 = 1918441) (by norm_num)
theorem B3410561 : Blo 2273435 3410561 := bstep (se 2 (by rfl) ⟨1278960, by rfl⟩ : syracuseStep 3410561 = 2557921) B2557921
theorem B2273707 : Blo 2273435 2273707 := bstep (se 1 (by rfl) ⟨1705280, by rfl⟩ : syracuseStep 2273707 = 3410561) B3410561
theorem B5755333 : Blo 2273435 5755333 := bbase (se 4 (by rfl) ⟨539562, by rfl⟩ : syracuseStep 5755333 = 1079125) (by norm_num)
theorem B7673777 : Blo 2273435 7673777 := bstep (se 2 (by rfl) ⟨2877666, by rfl⟩ : syracuseStep 7673777 = 5755333) B5755333
theorem B5115851 : Blo 2273435 5115851 := bstep (se 1 (by rfl) ⟨3836888, by rfl⟩ : syracuseStep 5115851 = 7673777) B7673777
theorem B3410567 : Blo 2273435 3410567 := bstep (se 1 (by rfl) ⟨2557925, by rfl⟩ : syracuseStep 3410567 = 5115851) B5115851
theorem B2273711 : Blo 2273435 2273711 := bstep (se 1 (by rfl) ⟨1705283, by rfl⟩ : syracuseStep 2273711 = 3410567) B3410567
theorem B3410573 : Blo 2273435 3410573 := bbase (se 3 (by rfl) ⟨639482, by rfl⟩ : syracuseStep 3410573 = 1278965) (by norm_num)
theorem B2273715 : Blo 2273435 2273715 := bstep (se 1 (by rfl) ⟨1705286, by rfl⟩ : syracuseStep 2273715 = 3410573) B3410573
theorem B5115869 : Blo 2273435 5115869 := bbase (se 3 (by rfl) ⟨959225, by rfl⟩ : syracuseStep 5115869 = 1918451) (by norm_num)
theorem B3410579 : Blo 2273435 3410579 := bstep (se 1 (by rfl) ⟨2557934, by rfl⟩ : syracuseStep 3410579 = 5115869) B5115869
theorem B2273719 : Blo 2273435 2273719 := bstep (se 1 (by rfl) ⟨1705289, by rfl⟩ : syracuseStep 2273719 = 3410579) B3410579
theorem B3836909 : Blo 2273435 3836909 := bbase (se 3 (by rfl) ⟨719420, by rfl⟩ : syracuseStep 3836909 = 1438841) (by norm_num)
theorem B2557939 : Blo 2273435 2557939 := bstep (se 1 (by rfl) ⟨1918454, by rfl⟩ : syracuseStep 2557939 = 3836909) B3836909
theorem B3410585 : Blo 2273435 3410585 := bstep (se 2 (by rfl) ⟨1278969, by rfl⟩ : syracuseStep 3410585 = 2557939) B2557939
theorem B2273723 : Blo 2273435 2273723 := bstep (se 1 (by rfl) ⟨1705292, by rfl⟩ : syracuseStep 2273723 = 3410585) B3410585
theorem B5463109 : Blo 2273435 5463109 := bbase (se 4 (by rfl) ⟨512166, by rfl⟩ : syracuseStep 5463109 = 1024333) (by norm_num)
theorem B29136581 : Blo 2273435 29136581 := bstep (se 4 (by rfl) ⟨2731554, by rfl⟩ : syracuseStep 29136581 = 5463109) B5463109
theorem B19424387 : Blo 2273435 19424387 := bstep (se 1 (by rfl) ⟨14568290, by rfl⟩ : syracuseStep 19424387 = 29136581) B29136581
theorem B12949591 : Blo 2273435 12949591 := bstep (se 1 (by rfl) ⟨9712193, by rfl⟩ : syracuseStep 12949591 = 19424387) B19424387
theorem B17266121 : Blo 2273435 17266121 := bstep (se 2 (by rfl) ⟨6474795, by rfl⟩ : syracuseStep 17266121 = 12949591) B12949591
theorem B11510747 : Blo 2273435 11510747 := bstep (se 1 (by rfl) ⟨8633060, by rfl⟩ : syracuseStep 11510747 = 17266121) B17266121
theorem B7673831 : Blo 2273435 7673831 := bstep (se 1 (by rfl) ⟨5755373, by rfl⟩ : syracuseStep 7673831 = 11510747) B11510747
theorem B5115887 : Blo 2273435 5115887 := bstep (se 1 (by rfl) ⟨3836915, by rfl⟩ : syracuseStep 5115887 = 7673831) B7673831
theorem B3410591 : Blo 2273435 3410591 := bstep (se 1 (by rfl) ⟨2557943, by rfl⟩ : syracuseStep 3410591 = 5115887) B5115887
theorem B2273727 : Blo 2273435 2273727 := bstep (se 1 (by rfl) ⟨1705295, by rfl⟩ : syracuseStep 2273727 = 3410591) B3410591
theorem B3410597 : Blo 2273435 3410597 := bbase (se 4 (by rfl) ⟨319743, by rfl⟩ : syracuseStep 3410597 = 639487) (by norm_num)
theorem B2273731 : Blo 2273435 2273731 := bstep (se 1 (by rfl) ⟨1705298, by rfl⟩ : syracuseStep 2273731 = 3410597) B3410597
theorem B2877697 : Blo 2273435 2877697 := bbase (se 2 (by rfl) ⟨1079136, by rfl⟩ : syracuseStep 2877697 = 2158273) (by norm_num)
theorem B3836929 : Blo 2273435 3836929 := bstep (se 2 (by rfl) ⟨1438848, by rfl⟩ : syracuseStep 3836929 = 2877697) B2877697
theorem B5115905 : Blo 2273435 5115905 := bstep (se 2 (by rfl) ⟨1918464, by rfl⟩ : syracuseStep 5115905 = 3836929) B3836929
theorem B3410603 : Blo 2273435 3410603 := bstep (se 1 (by rfl) ⟨2557952, by rfl⟩ : syracuseStep 3410603 = 5115905) B5115905
theorem B2273735 : Blo 2273435 2273735 := bstep (se 1 (by rfl) ⟨1705301, by rfl⟩ : syracuseStep 2273735 = 3410603) B3410603
theorem B2557957 : Blo 2273435 2557957 := bbase (se 4 (by rfl) ⟨239808, by rfl⟩ : syracuseStep 2557957 = 479617) (by norm_num)
theorem B3410609 : Blo 2273435 3410609 := bstep (se 2 (by rfl) ⟨1278978, by rfl⟩ : syracuseStep 3410609 = 2557957) B2557957
theorem B2273739 : Blo 2273435 2273739 := bstep (se 1 (by rfl) ⟨1705304, by rfl⟩ : syracuseStep 2273739 = 3410609) B3410609
theorem B3237421 : Blo 2273435 3237421 := bbase (se 3 (by rfl) ⟨607016, by rfl⟩ : syracuseStep 3237421 = 1214033) (by norm_num)
theorem B4316561 : Blo 2273435 4316561 := bstep (se 2 (by rfl) ⟨1618710, by rfl⟩ : syracuseStep 4316561 = 3237421) B3237421
theorem B2877707 : Blo 2273435 2877707 := bstep (se 1 (by rfl) ⟨2158280, by rfl⟩ : syracuseStep 2877707 = 4316561) B4316561
theorem B7673885 : Blo 2273435 7673885 := bstep (se 3 (by rfl) ⟨1438853, by rfl⟩ : syracuseStep 7673885 = 2877707) B2877707
theorem B5115923 : Blo 2273435 5115923 := bstep (se 1 (by rfl) ⟨3836942, by rfl⟩ : syracuseStep 5115923 = 7673885) B7673885
theorem B3410615 : Blo 2273435 3410615 := bstep (se 1 (by rfl) ⟨2557961, by rfl⟩ : syracuseStep 3410615 = 5115923) B5115923
theorem B2273743 : Blo 2273435 2273743 := bstep (se 1 (by rfl) ⟨1705307, by rfl⟩ : syracuseStep 2273743 = 3410615) B3410615
theorem B3410621 : Blo 2273435 3410621 := bbase (se 3 (by rfl) ⟨639491, by rfl⟩ : syracuseStep 3410621 = 1278983) (by norm_num)
theorem B2273747 : Blo 2273435 2273747 := bstep (se 1 (by rfl) ⟨1705310, by rfl⟩ : syracuseStep 2273747 = 3410621) B3410621
theorem B5115941 : Blo 2273435 5115941 := bbase (se 4 (by rfl) ⟨479619, by rfl⟩ : syracuseStep 5115941 = 959239) (by norm_num)
theorem B3410627 : Blo 2273435 3410627 := bstep (se 1 (by rfl) ⟨2557970, by rfl⟩ : syracuseStep 3410627 = 5115941) B5115941
theorem B2273751 : Blo 2273435 2273751 := bstep (se 1 (by rfl) ⟨1705313, by rfl⟩ : syracuseStep 2273751 = 3410627) B3410627
theorem B5755445 : Blo 2273435 5755445 := bbase (se 5 (by rfl) ⟨269786, by rfl⟩ : syracuseStep 5755445 = 539573) (by norm_num)
theorem B3836963 : Blo 2273435 3836963 := bstep (se 1 (by rfl) ⟨2877722, by rfl⟩ : syracuseStep 3836963 = 5755445) B5755445
theorem B2557975 : Blo 2273435 2557975 := bstep (se 1 (by rfl) ⟨1918481, by rfl⟩ : syracuseStep 2557975 = 3836963) B3836963
theorem B3410633 : Blo 2273435 3410633 := bstep (se 2 (by rfl) ⟨1278987, by rfl⟩ : syracuseStep 3410633 = 2557975) B2557975
theorem B2273755 : Blo 2273435 2273755 := bstep (se 1 (by rfl) ⟨1705316, by rfl⟩ : syracuseStep 2273755 = 3410633) B3410633
theorem B10926373 : Blo 2273435 10926373 := bbase (se 4 (by rfl) ⟨1024347, by rfl⟩ : syracuseStep 10926373 = 2048695) (by norm_num)
theorem B14568497 : Blo 2273435 14568497 := bstep (se 2 (by rfl) ⟨5463186, by rfl⟩ : syracuseStep 14568497 = 10926373) B10926373
theorem B9712331 : Blo 2273435 9712331 := bstep (se 1 (by rfl) ⟨7284248, by rfl⟩ : syracuseStep 9712331 = 14568497) B14568497
theorem B6474887 : Blo 2273435 6474887 := bstep (se 1 (by rfl) ⟨4856165, by rfl⟩ : syracuseStep 6474887 = 9712331) B9712331
theorem B4316591 : Blo 2273435 4316591 := bstep (se 1 (by rfl) ⟨3237443, by rfl⟩ : syracuseStep 4316591 = 6474887) B6474887
theorem B11510909 : Blo 2273435 11510909 := bstep (se 3 (by rfl) ⟨2158295, by rfl⟩ : syracuseStep 11510909 = 4316591) B4316591
theorem B7673939 : Blo 2273435 7673939 := bstep (se 1 (by rfl) ⟨5755454, by rfl⟩ : syracuseStep 7673939 = 11510909) B11510909
theorem B5115959 : Blo 2273435 5115959 := bstep (se 1 (by rfl) ⟨3836969, by rfl⟩ : syracuseStep 5115959 = 7673939) B7673939
theorem B3410639 : Blo 2273435 3410639 := bstep (se 1 (by rfl) ⟨2557979, by rfl⟩ : syracuseStep 3410639 = 5115959) B5115959
theorem B2273759 : Blo 2273435 2273759 := bstep (se 1 (by rfl) ⟨1705319, by rfl⟩ : syracuseStep 2273759 = 3410639) B3410639
theorem B3410645 : Blo 2273435 3410645 := bbase (se 7 (by rfl) ⟨39968, by rfl⟩ : syracuseStep 3410645 = 79937) (by norm_num)
theorem B2273763 : Blo 2273435 2273763 := bstep (se 1 (by rfl) ⟨1705322, by rfl⟩ : syracuseStep 2273763 = 3410645) B3410645
theorem B4097405 : Blo 2273435 4097405 := bbase (se 3 (by rfl) ⟨768263, by rfl⟩ : syracuseStep 4097405 = 1536527) (by norm_num)
theorem B10926413 : Blo 2273435 10926413 := bstep (se 3 (by rfl) ⟨2048702, by rfl⟩ : syracuseStep 10926413 = 4097405) B4097405
theorem B7284275 : Blo 2273435 7284275 := bstep (se 1 (by rfl) ⟨5463206, by rfl⟩ : syracuseStep 7284275 = 10926413) B10926413
theorem B4856183 : Blo 2273435 4856183 := bstep (se 1 (by rfl) ⟨3642137, by rfl⟩ : syracuseStep 4856183 = 7284275) B7284275
theorem B3237455 : Blo 2273435 3237455 := bstep (se 1 (by rfl) ⟨2428091, by rfl⟩ : syracuseStep 3237455 = 4856183) B4856183
theorem B8633213 : Blo 2273435 8633213 := bstep (se 3 (by rfl) ⟨1618727, by rfl⟩ : syracuseStep 8633213 = 3237455) B3237455
theorem B5755475 : Blo 2273435 5755475 := bstep (se 1 (by rfl) ⟨4316606, by rfl⟩ : syracuseStep 5755475 = 8633213) B8633213
theorem B3836983 : Blo 2273435 3836983 := bstep (se 1 (by rfl) ⟨2877737, by rfl⟩ : syracuseStep 3836983 = 5755475) B5755475
theorem B5115977 : Blo 2273435 5115977 := bstep (se 2 (by rfl) ⟨1918491, by rfl⟩ : syracuseStep 5115977 = 3836983) B3836983
theorem B3410651 : Blo 2273435 3410651 := bstep (se 1 (by rfl) ⟨2557988, by rfl⟩ : syracuseStep 3410651 = 5115977) B5115977
theorem B2273767 : Blo 2273435 2273767 := bstep (se 1 (by rfl) ⟨1705325, by rfl⟩ : syracuseStep 2273767 = 3410651) B3410651
theorem B2557993 : Blo 2273435 2557993 := bbase (se 2 (by rfl) ⟨959247, by rfl⟩ : syracuseStep 2557993 = 1918495) (by norm_num)
theorem B3410657 : Blo 2273435 3410657 := bstep (se 2 (by rfl) ⟨1278996, by rfl⟩ : syracuseStep 3410657 = 2557993) B2557993
theorem B2273771 : Blo 2273435 2273771 := bstep (se 1 (by rfl) ⟨1705328, by rfl⟩ : syracuseStep 2273771 = 3410657) B3410657
theorem B32779349 : Blo 2273435 32779349 := bbase (se 8 (by rfl) ⟨192066, by rfl⟩ : syracuseStep 32779349 = 384133) (by norm_num)
theorem B21852899 : Blo 2273435 21852899 := bstep (se 1 (by rfl) ⟨16389674, by rfl⟩ : syracuseStep 21852899 = 32779349) B32779349
theorem B14568599 : Blo 2273435 14568599 := bstep (se 1 (by rfl) ⟨10926449, by rfl⟩ : syracuseStep 14568599 = 21852899) B21852899
theorem B9712399 : Blo 2273435 9712399 := bstep (se 1 (by rfl) ⟨7284299, by rfl⟩ : syracuseStep 9712399 = 14568599) B14568599
theorem B12949865 : Blo 2273435 12949865 := bstep (se 2 (by rfl) ⟨4856199, by rfl⟩ : syracuseStep 12949865 = 9712399) B9712399
theorem B8633243 : Blo 2273435 8633243 := bstep (se 1 (by rfl) ⟨6474932, by rfl⟩ : syracuseStep 8633243 = 12949865) B12949865
theorem B5755495 : Blo 2273435 5755495 := bstep (se 1 (by rfl) ⟨4316621, by rfl⟩ : syracuseStep 5755495 = 8633243) B8633243
theorem B7673993 : Blo 2273435 7673993 := bstep (se 2 (by rfl) ⟨2877747, by rfl⟩ : syracuseStep 7673993 = 5755495) B5755495
theorem B5115995 : Blo 2273435 5115995 := bstep (se 1 (by rfl) ⟨3836996, by rfl⟩ : syracuseStep 5115995 = 7673993) B7673993
theorem B3410663 : Blo 2273435 3410663 := bstep (se 1 (by rfl) ⟨2557997, by rfl⟩ : syracuseStep 3410663 = 5115995) B5115995
theorem B2273775 : Blo 2273435 2273775 := bstep (se 1 (by rfl) ⟨1705331, by rfl⟩ : syracuseStep 2273775 = 3410663) B3410663
theorem B3410669 : Blo 2273435 3410669 := bbase (se 3 (by rfl) ⟨639500, by rfl⟩ : syracuseStep 3410669 = 1279001) (by norm_num)
theorem B2273779 : Blo 2273435 2273779 := bstep (se 1 (by rfl) ⟨1705334, by rfl⟩ : syracuseStep 2273779 = 3410669) B3410669
theorem B5116013 : Blo 2273435 5116013 := bbase (se 3 (by rfl) ⟨959252, by rfl⟩ : syracuseStep 5116013 = 1918505) (by norm_num)
theorem B3410675 : Blo 2273435 3410675 := bstep (se 1 (by rfl) ⟨2558006, by rfl⟩ : syracuseStep 3410675 = 5116013) B5116013
theorem B2273783 : Blo 2273435 2273783 := bstep (se 1 (by rfl) ⟨1705337, by rfl⟩ : syracuseStep 2273783 = 3410675) B3410675
theorem B4316645 : Blo 2273435 4316645 := bbase (se 4 (by rfl) ⟨404685, by rfl⟩ : syracuseStep 4316645 = 809371) (by norm_num)
theorem B2877763 : Blo 2273435 2877763 := bstep (se 1 (by rfl) ⟨2158322, by rfl⟩ : syracuseStep 2877763 = 4316645) B4316645
theorem B3837017 : Blo 2273435 3837017 := bstep (se 2 (by rfl) ⟨1438881, by rfl⟩ : syracuseStep 3837017 = 2877763) B2877763
theorem B2558011 : Blo 2273435 2558011 := bstep (se 1 (by rfl) ⟨1918508, by rfl⟩ : syracuseStep 2558011 = 3837017) B3837017
theorem B3410681 : Blo 2273435 3410681 := bstep (se 2 (by rfl) ⟨1279005, by rfl⟩ : syracuseStep 3410681 = 2558011) B2558011
theorem B2273787 : Blo 2273435 2273787 := bstep (se 1 (by rfl) ⟨1705340, by rfl⟩ : syracuseStep 2273787 = 3410681) B3410681
theorem B2336261 : Blo 2273435 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B6230029 : Blo 2273435 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B8306705 : Blo 2273435 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B5537803 : Blo 2273435 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B7383737 : Blo 2273435 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B4922491 : Blo 2273435 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B6563321 : Blo 2273435 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B4375547 : Blo 2273435 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B2917031 : Blo 2273435 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B7778749 : Blo 2273435 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B10371665 : Blo 2273435 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B6914443 : Blo 2273435 6914443 := bstep (se 1 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 6914443 = 10371665) B10371665
theorem B9219257 : Blo 2273435 9219257 := bstep (se 2 (by rfl) ⟨3457221, by rfl⟩ : syracuseStep 9219257 = 6914443) B6914443
theorem B6146171 : Blo 2273435 6146171 := bstep (se 1 (by rfl) ⟨4609628, by rfl⟩ : syracuseStep 6146171 = 9219257) B9219257
theorem B4097447 : Blo 2273435 4097447 := bstep (se 1 (by rfl) ⟨3073085, by rfl⟩ : syracuseStep 4097447 = 6146171) B6146171
theorem B43706101 : Blo 2273435 43706101 := bstep (se 5 (by rfl) ⟨2048723, by rfl⟩ : syracuseStep 43706101 = 4097447) B4097447
theorem B58274801 : Blo 2273435 58274801 := bstep (se 2 (by rfl) ⟨21853050, by rfl⟩ : syracuseStep 58274801 = 43706101) B43706101
theorem B38849867 : Blo 2273435 38849867 := bstep (se 1 (by rfl) ⟨29137400, by rfl⟩ : syracuseStep 38849867 = 58274801) B58274801
theorem B25899911 : Blo 2273435 25899911 := bstep (se 1 (by rfl) ⟨19424933, by rfl⟩ : syracuseStep 25899911 = 38849867) B38849867
theorem B17266607 : Blo 2273435 17266607 := bstep (se 1 (by rfl) ⟨12949955, by rfl⟩ : syracuseStep 17266607 = 25899911) B25899911
theorem B11511071 : Blo 2273435 11511071 := bstep (se 1 (by rfl) ⟨8633303, by rfl⟩ : syracuseStep 11511071 = 17266607) B17266607
theorem B7674047 : Blo 2273435 7674047 := bstep (se 1 (by rfl) ⟨5755535, by rfl⟩ : syracuseStep 7674047 = 11511071) B11511071
theorem B5116031 : Blo 2273435 5116031 := bstep (se 1 (by rfl) ⟨3837023, by rfl⟩ : syracuseStep 5116031 = 7674047) B7674047
theorem B3410687 : Blo 2273435 3410687 := bstep (se 1 (by rfl) ⟨2558015, by rfl⟩ : syracuseStep 3410687 = 5116031) B5116031
theorem B2273791 : Blo 2273435 2273791 := bstep (se 1 (by rfl) ⟨1705343, by rfl⟩ : syracuseStep 2273791 = 3410687) B3410687
theorem B3410693 : Blo 2273435 3410693 := bbase (se 4 (by rfl) ⟨319752, by rfl⟩ : syracuseStep 3410693 = 639505) (by norm_num)
theorem B2273795 : Blo 2273435 2273795 := bstep (se 1 (by rfl) ⟨1705346, by rfl⟩ : syracuseStep 2273795 = 3410693) B3410693
theorem B3837037 : Blo 2273435 3837037 := bbase (se 3 (by rfl) ⟨719444, by rfl⟩ : syracuseStep 3837037 = 1438889) (by norm_num)
theorem B5116049 : Blo 2273435 5116049 := bstep (se 2 (by rfl) ⟨1918518, by rfl⟩ : syracuseStep 5116049 = 3837037) B3837037
theorem B3410699 : Blo 2273435 3410699 := bstep (se 1 (by rfl) ⟨2558024, by rfl⟩ : syracuseStep 3410699 = 5116049) B5116049
theorem B2273799 : Blo 2273435 2273799 := bstep (se 1 (by rfl) ⟨1705349, by rfl⟩ : syracuseStep 2273799 = 3410699) B3410699
theorem B2558029 : Blo 2273435 2558029 := bbase (se 3 (by rfl) ⟨479630, by rfl⟩ : syracuseStep 2558029 = 959261) (by norm_num)
theorem B3410705 : Blo 2273435 3410705 := bstep (se 2 (by rfl) ⟨1279014, by rfl⟩ : syracuseStep 3410705 = 2558029) B2558029
theorem B2273803 : Blo 2273435 2273803 := bstep (se 1 (by rfl) ⟨1705352, by rfl⟩ : syracuseStep 2273803 = 3410705) B3410705
theorem B7674101 : Blo 2273435 7674101 := bbase (se 5 (by rfl) ⟨359723, by rfl⟩ : syracuseStep 7674101 = 719447) (by norm_num)
theorem B5116067 : Blo 2273435 5116067 := bstep (se 1 (by rfl) ⟨3837050, by rfl⟩ : syracuseStep 5116067 = 7674101) B7674101
theorem B3410711 : Blo 2273435 3410711 := bstep (se 1 (by rfl) ⟨2558033, by rfl⟩ : syracuseStep 3410711 = 5116067) B5116067
theorem B2273807 : Blo 2273435 2273807 := bstep (se 1 (by rfl) ⟨1705355, by rfl⟩ : syracuseStep 2273807 = 3410711) B3410711
theorem B3410717 : Blo 2273435 3410717 := bbase (se 3 (by rfl) ⟨639509, by rfl⟩ : syracuseStep 3410717 = 1279019) (by norm_num)
theorem B2273811 : Blo 2273435 2273811 := bstep (se 1 (by rfl) ⟨1705358, by rfl⟩ : syracuseStep 2273811 = 3410717) B3410717
theorem B5116085 : Blo 2273435 5116085 := bbase (se 5 (by rfl) ⟨239816, by rfl⟩ : syracuseStep 5116085 = 479633) (by norm_num)
theorem B3410723 : Blo 2273435 3410723 := bstep (se 1 (by rfl) ⟨2558042, by rfl⟩ : syracuseStep 3410723 = 5116085) B5116085
theorem B2273815 : Blo 2273435 2273815 := bstep (se 1 (by rfl) ⟨1705361, by rfl⟩ : syracuseStep 2273815 = 3410723) B3410723
theorem B3642221 : Blo 2273435 3642221 := bbase (se 3 (by rfl) ⟨682916, by rfl⟩ : syracuseStep 3642221 = 1365833) (by norm_num)
theorem B2428147 : Blo 2273435 2428147 := bstep (se 1 (by rfl) ⟨1821110, by rfl⟩ : syracuseStep 2428147 = 3642221) B3642221
theorem B12950117 : Blo 2273435 12950117 := bstep (se 4 (by rfl) ⟨1214073, by rfl⟩ : syracuseStep 12950117 = 2428147) B2428147
theorem B8633411 : Blo 2273435 8633411 := bstep (se 1 (by rfl) ⟨6475058, by rfl⟩ : syracuseStep 8633411 = 12950117) B12950117
theorem B5755607 : Blo 2273435 5755607 := bstep (se 1 (by rfl) ⟨4316705, by rfl⟩ : syracuseStep 5755607 = 8633411) B8633411
theorem B3837071 : Blo 2273435 3837071 := bstep (se 1 (by rfl) ⟨2877803, by rfl⟩ : syracuseStep 3837071 = 5755607) B5755607
theorem B2558047 : Blo 2273435 2558047 := bstep (se 1 (by rfl) ⟨1918535, by rfl⟩ : syracuseStep 2558047 = 3837071) B3837071
theorem B3410729 : Blo 2273435 3410729 := bstep (se 2 (by rfl) ⟨1279023, by rfl⟩ : syracuseStep 3410729 = 2558047) B2558047
theorem B2273819 : Blo 2273435 2273819 := bstep (se 1 (by rfl) ⟨1705364, by rfl⟩ : syracuseStep 2273819 = 3410729) B3410729
theorem B5463341 : Blo 2273435 5463341 := bbase (se 3 (by rfl) ⟨1024376, by rfl⟩ : syracuseStep 5463341 = 2048753) (by norm_num)
theorem B3642227 : Blo 2273435 3642227 := bstep (se 1 (by rfl) ⟨2731670, by rfl⟩ : syracuseStep 3642227 = 5463341) B5463341
theorem B2428151 : Blo 2273435 2428151 := bstep (se 1 (by rfl) ⟨1821113, by rfl⟩ : syracuseStep 2428151 = 3642227) B3642227
theorem B6475069 : Blo 2273435 6475069 := bstep (se 3 (by rfl) ⟨1214075, by rfl⟩ : syracuseStep 6475069 = 2428151) B2428151
theorem B8633425 : Blo 2273435 8633425 := bstep (se 2 (by rfl) ⟨3237534, by rfl⟩ : syracuseStep 8633425 = 6475069) B6475069
theorem B11511233 : Blo 2273435 11511233 := bstep (se 2 (by rfl) ⟨4316712, by rfl⟩ : syracuseStep 11511233 = 8633425) B8633425
theorem B7674155 : Blo 2273435 7674155 := bstep (se 1 (by rfl) ⟨5755616, by rfl⟩ : syracuseStep 7674155 = 11511233) B11511233
theorem B5116103 : Blo 2273435 5116103 := bstep (se 1 (by rfl) ⟨3837077, by rfl⟩ : syracuseStep 5116103 = 7674155) B7674155
theorem B3410735 : Blo 2273435 3410735 := bstep (se 1 (by rfl) ⟨2558051, by rfl⟩ : syracuseStep 3410735 = 5116103) B5116103
theorem B2273823 : Blo 2273435 2273823 := bstep (se 1 (by rfl) ⟨1705367, by rfl⟩ : syracuseStep 2273823 = 3410735) B3410735
theorem B3410741 : Blo 2273435 3410741 := bbase (se 5 (by rfl) ⟨159878, by rfl⟩ : syracuseStep 3410741 = 319757) (by norm_num)
theorem B2273827 : Blo 2273435 2273827 := bstep (se 1 (by rfl) ⟨1705370, by rfl⟩ : syracuseStep 2273827 = 3410741) B3410741
theorem B5755637 : Blo 2273435 5755637 := bbase (se 5 (by rfl) ⟨269795, by rfl⟩ : syracuseStep 5755637 = 539591) (by norm_num)
theorem B3837091 : Blo 2273435 3837091 := bstep (se 1 (by rfl) ⟨2877818, by rfl⟩ : syracuseStep 3837091 = 5755637) B5755637
theorem B5116121 : Blo 2273435 5116121 := bstep (se 2 (by rfl) ⟨1918545, by rfl⟩ : syracuseStep 5116121 = 3837091) B3837091
theorem B3410747 : Blo 2273435 3410747 := bstep (se 1 (by rfl) ⟨2558060, by rfl⟩ : syracuseStep 3410747 = 5116121) B5116121
theorem B2273831 : Blo 2273435 2273831 := bstep (se 1 (by rfl) ⟨1705373, by rfl⟩ : syracuseStep 2273831 = 3410747) B3410747
theorem B2558065 : Blo 2273435 2558065 := bbase (se 2 (by rfl) ⟨959274, by rfl⟩ : syracuseStep 2558065 = 1918549) (by norm_num)
theorem B3410753 : Blo 2273435 3410753 := bstep (se 2 (by rfl) ⟨1279032, by rfl⟩ : syracuseStep 3410753 = 2558065) B2558065
theorem B2273835 : Blo 2273435 2273835 := bstep (se 1 (by rfl) ⟨1705376, by rfl⟩ : syracuseStep 2273835 = 3410753) B3410753
theorem B7383893 : Blo 2273435 7383893 := bbase (se 9 (by rfl) ⟨21632, by rfl⟩ : syracuseStep 7383893 = 43265) (by norm_num)
theorem B19690381 : Blo 2273435 19690381 := bstep (se 3 (by rfl) ⟨3691946, by rfl⟩ : syracuseStep 19690381 = 7383893) B7383893
theorem B26253841 : Blo 2273435 26253841 := bstep (se 2 (by rfl) ⟨9845190, by rfl⟩ : syracuseStep 26253841 = 19690381) B19690381
theorem B35005121 : Blo 2273435 35005121 := bstep (se 2 (by rfl) ⟨13126920, by rfl⟩ : syracuseStep 35005121 = 26253841) B26253841
theorem B23336747 : Blo 2273435 23336747 := bstep (se 1 (by rfl) ⟨17502560, by rfl⟩ : syracuseStep 23336747 = 35005121) B35005121
theorem B15557831 : Blo 2273435 15557831 := bstep (se 1 (by rfl) ⟨11668373, by rfl⟩ : syracuseStep 15557831 = 23336747) B23336747
theorem B10371887 : Blo 2273435 10371887 := bstep (se 1 (by rfl) ⟨7778915, by rfl⟩ : syracuseStep 10371887 = 15557831) B15557831
theorem B6914591 : Blo 2273435 6914591 := bstep (se 1 (by rfl) ⟨5185943, by rfl⟩ : syracuseStep 6914591 = 10371887) B10371887
theorem B4609727 : Blo 2273435 4609727 := bstep (se 1 (by rfl) ⟨3457295, by rfl⟩ : syracuseStep 4609727 = 6914591) B6914591
theorem B3073151 : Blo 2273435 3073151 := bstep (se 1 (by rfl) ⟨2304863, by rfl⟩ : syracuseStep 3073151 = 4609727) B4609727
theorem B8195069 : Blo 2273435 8195069 := bstep (se 3 (by rfl) ⟨1536575, by rfl⟩ : syracuseStep 8195069 = 3073151) B3073151
theorem B5463379 : Blo 2273435 5463379 := bstep (se 1 (by rfl) ⟨4097534, by rfl⟩ : syracuseStep 5463379 = 8195069) B8195069
theorem B7284505 : Blo 2273435 7284505 := bstep (se 2 (by rfl) ⟨2731689, by rfl⟩ : syracuseStep 7284505 = 5463379) B5463379
theorem B9712673 : Blo 2273435 9712673 := bstep (se 2 (by rfl) ⟨3642252, by rfl⟩ : syracuseStep 9712673 = 7284505) B7284505
theorem B6475115 : Blo 2273435 6475115 := bstep (se 1 (by rfl) ⟨4856336, by rfl⟩ : syracuseStep 6475115 = 9712673) B9712673
theorem B4316743 : Blo 2273435 4316743 := bstep (se 1 (by rfl) ⟨3237557, by rfl⟩ : syracuseStep 4316743 = 6475115) B6475115
theorem B5755657 : Blo 2273435 5755657 := bstep (se 2 (by rfl) ⟨2158371, by rfl⟩ : syracuseStep 5755657 = 4316743) B4316743
theorem B7674209 : Blo 2273435 7674209 := bstep (se 2 (by rfl) ⟨2877828, by rfl⟩ : syracuseStep 7674209 = 5755657) B5755657
theorem B5116139 : Blo 2273435 5116139 := bstep (se 1 (by rfl) ⟨3837104, by rfl⟩ : syracuseStep 5116139 = 7674209) B7674209
theorem B3410759 : Blo 2273435 3410759 := bstep (se 1 (by rfl) ⟨2558069, by rfl⟩ : syracuseStep 3410759 = 5116139) B5116139
theorem B2273839 : Blo 2273435 2273839 := bstep (se 1 (by rfl) ⟨1705379, by rfl⟩ : syracuseStep 2273839 = 3410759) B3410759
theorem B3410765 : Blo 2273435 3410765 := bbase (se 3 (by rfl) ⟨639518, by rfl⟩ : syracuseStep 3410765 = 1279037) (by norm_num)
theorem B2273843 : Blo 2273435 2273843 := bstep (se 1 (by rfl) ⟨1705382, by rfl⟩ : syracuseStep 2273843 = 3410765) B3410765
theorem B5116157 : Blo 2273435 5116157 := bbase (se 3 (by rfl) ⟨959279, by rfl⟩ : syracuseStep 5116157 = 1918559) (by norm_num)
theorem B3410771 : Blo 2273435 3410771 := bstep (se 1 (by rfl) ⟨2558078, by rfl⟩ : syracuseStep 3410771 = 5116157) B5116157
theorem B2273847 : Blo 2273435 2273847 := bstep (se 1 (by rfl) ⟨1705385, by rfl⟩ : syracuseStep 2273847 = 3410771) B3410771
theorem B3837125 : Blo 2273435 3837125 := bbase (se 4 (by rfl) ⟨359730, by rfl⟩ : syracuseStep 3837125 = 719461) (by norm_num)
theorem B2558083 : Blo 2273435 2558083 := bstep (se 1 (by rfl) ⟨1918562, by rfl⟩ : syracuseStep 2558083 = 3837125) B3837125
theorem B3410777 : Blo 2273435 3410777 := bstep (se 2 (by rfl) ⟨1279041, by rfl⟩ : syracuseStep 3410777 = 2558083) B2558083
theorem B2273851 : Blo 2273435 2273851 := bstep (se 1 (by rfl) ⟨1705388, by rfl⟩ : syracuseStep 2273851 = 3410777) B3410777
theorem B17267093 : Blo 2273435 17267093 := bbase (se 6 (by rfl) ⟨404697, by rfl⟩ : syracuseStep 17267093 = 809395) (by norm_num)
theorem B11511395 : Blo 2273435 11511395 := bstep (se 1 (by rfl) ⟨8633546, by rfl⟩ : syracuseStep 11511395 = 17267093) B17267093
theorem B7674263 : Blo 2273435 7674263 := bstep (se 1 (by rfl) ⟨5755697, by rfl⟩ : syracuseStep 7674263 = 11511395) B11511395
theorem B5116175 : Blo 2273435 5116175 := bstep (se 1 (by rfl) ⟨3837131, by rfl⟩ : syracuseStep 5116175 = 7674263) B7674263
theorem B3410783 : Blo 2273435 3410783 := bstep (se 1 (by rfl) ⟨2558087, by rfl⟩ : syracuseStep 3410783 = 5116175) B5116175
theorem B2273855 : Blo 2273435 2273855 := bstep (se 1 (by rfl) ⟨1705391, by rfl⟩ : syracuseStep 2273855 = 3410783) B3410783
theorem B3410789 : Blo 2273435 3410789 := bbase (se 4 (by rfl) ⟨319761, by rfl⟩ : syracuseStep 3410789 = 639523) (by norm_num)
theorem B2273859 : Blo 2273435 2273859 := bstep (se 1 (by rfl) ⟨1705394, by rfl⟩ : syracuseStep 2273859 = 3410789) B3410789
theorem B4316789 : Blo 2273435 4316789 := bbase (se 5 (by rfl) ⟨202349, by rfl⟩ : syracuseStep 4316789 = 404699) (by norm_num)
theorem B2877859 : Blo 2273435 2877859 := bstep (se 1 (by rfl) ⟨2158394, by rfl⟩ : syracuseStep 2877859 = 4316789) B4316789
theorem B3837145 : Blo 2273435 3837145 := bstep (se 2 (by rfl) ⟨1438929, by rfl⟩ : syracuseStep 3837145 = 2877859) B2877859
theorem B5116193 : Blo 2273435 5116193 := bstep (se 2 (by rfl) ⟨1918572, by rfl⟩ : syracuseStep 5116193 = 3837145) B3837145
theorem B3410795 : Blo 2273435 3410795 := bstep (se 1 (by rfl) ⟨2558096, by rfl⟩ : syracuseStep 3410795 = 5116193) B5116193
theorem B2273863 : Blo 2273435 2273863 := bstep (se 1 (by rfl) ⟨1705397, by rfl⟩ : syracuseStep 2273863 = 3410795) B3410795
theorem B2558101 : Blo 2273435 2558101 := bbase (se 6 (by rfl) ⟨59955, by rfl⟩ : syracuseStep 2558101 = 119911) (by norm_num)
theorem B3410801 : Blo 2273435 3410801 := bstep (se 2 (by rfl) ⟨1279050, by rfl⟩ : syracuseStep 3410801 = 2558101) B2558101
theorem B2273867 : Blo 2273435 2273867 := bstep (se 1 (by rfl) ⟨1705400, by rfl⟩ : syracuseStep 2273867 = 3410801) B3410801
theorem B2877869 : Blo 2273435 2877869 := bbase (se 3 (by rfl) ⟨539600, by rfl⟩ : syracuseStep 2877869 = 1079201) (by norm_num)
theorem B7674317 : Blo 2273435 7674317 := bstep (se 3 (by rfl) ⟨1438934, by rfl⟩ : syracuseStep 7674317 = 2877869) B2877869
theorem B5116211 : Blo 2273435 5116211 := bstep (se 1 (by rfl) ⟨3837158, by rfl⟩ : syracuseStep 5116211 = 7674317) B7674317
theorem B3410807 : Blo 2273435 3410807 := bstep (se 1 (by rfl) ⟨2558105, by rfl⟩ : syracuseStep 3410807 = 5116211) B5116211
theorem B2273871 : Blo 2273435 2273871 := bstep (se 1 (by rfl) ⟨1705403, by rfl⟩ : syracuseStep 2273871 = 3410807) B3410807
theorem B3410813 : Blo 2273435 3410813 := bbase (se 3 (by rfl) ⟨639527, by rfl⟩ : syracuseStep 3410813 = 1279055) (by norm_num)
theorem B2273875 : Blo 2273435 2273875 := bstep (se 1 (by rfl) ⟨1705406, by rfl⟩ : syracuseStep 2273875 = 3410813) B3410813
theorem B5116229 : Blo 2273435 5116229 := bbase (se 4 (by rfl) ⟨479646, by rfl⟩ : syracuseStep 5116229 = 959293) (by norm_num)
theorem B3410819 : Blo 2273435 3410819 := bstep (se 1 (by rfl) ⟨2558114, by rfl⟩ : syracuseStep 3410819 = 5116229) B5116229
theorem B2273879 : Blo 2273435 2273879 := bstep (se 1 (by rfl) ⟨1705409, by rfl⟩ : syracuseStep 2273879 = 3410819) B3410819
theorem B9845381 : Blo 2273435 9845381 := bbase (se 4 (by rfl) ⟨923004, by rfl⟩ : syracuseStep 9845381 = 1846009) (by norm_num)
theorem B6563587 : Blo 2273435 6563587 := bstep (se 1 (by rfl) ⟨4922690, by rfl⟩ : syracuseStep 6563587 = 9845381) B9845381
theorem B8751449 : Blo 2273435 8751449 := bstep (se 2 (by rfl) ⟨3281793, by rfl⟩ : syracuseStep 8751449 = 6563587) B6563587
theorem B23337197 : Blo 2273435 23337197 := bstep (se 3 (by rfl) ⟨4375724, by rfl⟩ : syracuseStep 23337197 = 8751449) B8751449
theorem B15558131 : Blo 2273435 15558131 := bstep (se 1 (by rfl) ⟨11668598, by rfl⟩ : syracuseStep 15558131 = 23337197) B23337197
theorem B10372087 : Blo 2273435 10372087 := bstep (se 1 (by rfl) ⟨7779065, by rfl⟩ : syracuseStep 10372087 = 15558131) B15558131
theorem B13829449 : Blo 2273435 13829449 := bstep (se 2 (by rfl) ⟨5186043, by rfl⟩ : syracuseStep 13829449 = 10372087) B10372087
theorem B18439265 : Blo 2273435 18439265 := bstep (se 2 (by rfl) ⟨6914724, by rfl⟩ : syracuseStep 18439265 = 13829449) B13829449
theorem B12292843 : Blo 2273435 12292843 := bstep (se 1 (by rfl) ⟨9219632, by rfl⟩ : syracuseStep 12292843 = 18439265) B18439265
theorem B16390457 : Blo 2273435 16390457 := bstep (se 2 (by rfl) ⟨6146421, by rfl⟩ : syracuseStep 16390457 = 12292843) B12292843
theorem B10926971 : Blo 2273435 10926971 := bstep (se 1 (by rfl) ⟨8195228, by rfl⟩ : syracuseStep 10926971 = 16390457) B16390457
theorem B7284647 : Blo 2273435 7284647 := bstep (se 1 (by rfl) ⟨5463485, by rfl⟩ : syracuseStep 7284647 = 10926971) B10926971
theorem B4856431 : Blo 2273435 4856431 := bstep (se 1 (by rfl) ⟨3642323, by rfl⟩ : syracuseStep 4856431 = 7284647) B7284647
theorem B6475241 : Blo 2273435 6475241 := bstep (se 2 (by rfl) ⟨2428215, by rfl⟩ : syracuseStep 6475241 = 4856431) B4856431
theorem B4316827 : Blo 2273435 4316827 := bstep (se 1 (by rfl) ⟨3237620, by rfl⟩ : syracuseStep 4316827 = 6475241) B6475241
theorem B5755769 : Blo 2273435 5755769 := bstep (se 2 (by rfl) ⟨2158413, by rfl⟩ : syracuseStep 5755769 = 4316827) B4316827
theorem B3837179 : Blo 2273435 3837179 := bstep (se 1 (by rfl) ⟨2877884, by rfl⟩ : syracuseStep 3837179 = 5755769) B5755769
theorem B2558119 : Blo 2273435 2558119 := bstep (se 1 (by rfl) ⟨1918589, by rfl⟩ : syracuseStep 2558119 = 3837179) B3837179
theorem B3410825 : Blo 2273435 3410825 := bstep (se 2 (by rfl) ⟨1279059, by rfl⟩ : syracuseStep 3410825 = 2558119) B2558119
theorem B2273883 : Blo 2273435 2273883 := bstep (se 1 (by rfl) ⟨1705412, by rfl⟩ : syracuseStep 2273883 = 3410825) B3410825
theorem B11511557 : Blo 2273435 11511557 := bbase (se 4 (by rfl) ⟨1079208, by rfl⟩ : syracuseStep 11511557 = 2158417) (by norm_num)
theorem B7674371 : Blo 2273435 7674371 := bstep (se 1 (by rfl) ⟨5755778, by rfl⟩ : syracuseStep 7674371 = 11511557) B11511557
theorem B5116247 : Blo 2273435 5116247 := bstep (se 1 (by rfl) ⟨3837185, by rfl⟩ : syracuseStep 5116247 = 7674371) B7674371
theorem B3410831 : Blo 2273435 3410831 := bstep (se 1 (by rfl) ⟨2558123, by rfl⟩ : syracuseStep 3410831 = 5116247) B5116247
theorem B2273887 : Blo 2273435 2273887 := bstep (se 1 (by rfl) ⟨1705415, by rfl⟩ : syracuseStep 2273887 = 3410831) B3410831
theorem B3410837 : Blo 2273435 3410837 := bbase (se 6 (by rfl) ⟨79941, by rfl⟩ : syracuseStep 3410837 = 159883) (by norm_num)
theorem B2273891 : Blo 2273435 2273891 := bstep (se 1 (by rfl) ⟨1705418, by rfl⟩ : syracuseStep 2273891 = 3410837) B3410837
theorem B12950549 : Blo 2273435 12950549 := bbase (se 6 (by rfl) ⟨303528, by rfl⟩ : syracuseStep 12950549 = 607057) (by norm_num)
theorem B8633699 : Blo 2273435 8633699 := bstep (se 1 (by rfl) ⟨6475274, by rfl⟩ : syracuseStep 8633699 = 12950549) B12950549
theorem B5755799 : Blo 2273435 5755799 := bstep (se 1 (by rfl) ⟨4316849, by rfl⟩ : syracuseStep 5755799 = 8633699) B8633699
theorem B3837199 : Blo 2273435 3837199 := bstep (se 1 (by rfl) ⟨2877899, by rfl⟩ : syracuseStep 3837199 = 5755799) B5755799
theorem B5116265 : Blo 2273435 5116265 := bstep (se 2 (by rfl) ⟨1918599, by rfl⟩ : syracuseStep 5116265 = 3837199) B3837199
theorem B3410843 : Blo 2273435 3410843 := bstep (se 1 (by rfl) ⟨2558132, by rfl⟩ : syracuseStep 3410843 = 5116265) B5116265
theorem B2273895 : Blo 2273435 2273895 := bstep (se 1 (by rfl) ⟨1705421, by rfl⟩ : syracuseStep 2273895 = 3410843) B3410843
theorem B2558137 : Blo 2273435 2558137 := bbase (se 2 (by rfl) ⟨959301, by rfl⟩ : syracuseStep 2558137 = 1918603) (by norm_num)
theorem B3410849 : Blo 2273435 3410849 := bstep (se 2 (by rfl) ⟨1279068, by rfl⟩ : syracuseStep 3410849 = 2558137) B2558137
theorem B2273899 : Blo 2273435 2273899 := bstep (se 1 (by rfl) ⟨1705424, by rfl⟩ : syracuseStep 2273899 = 3410849) B3410849
theorem B5463533 : Blo 2273435 5463533 := bbase (se 3 (by rfl) ⟨1024412, by rfl⟩ : syracuseStep 5463533 = 2048825) (by norm_num)
theorem B3642355 : Blo 2273435 3642355 := bstep (se 1 (by rfl) ⟨2731766, by rfl⟩ : syracuseStep 3642355 = 5463533) B5463533
theorem B4856473 : Blo 2273435 4856473 := bstep (se 2 (by rfl) ⟨1821177, by rfl⟩ : syracuseStep 4856473 = 3642355) B3642355
theorem B6475297 : Blo 2273435 6475297 := bstep (se 2 (by rfl) ⟨2428236, by rfl⟩ : syracuseStep 6475297 = 4856473) B4856473
theorem B8633729 : Blo 2273435 8633729 := bstep (se 2 (by rfl) ⟨3237648, by rfl⟩ : syracuseStep 8633729 = 6475297) B6475297
theorem B5755819 : Blo 2273435 5755819 := bstep (se 1 (by rfl) ⟨4316864, by rfl⟩ : syracuseStep 5755819 = 8633729) B8633729
theorem B7674425 : Blo 2273435 7674425 := bstep (se 2 (by rfl) ⟨2877909, by rfl⟩ : syracuseStep 7674425 = 5755819) B5755819
theorem B5116283 : Blo 2273435 5116283 := bstep (se 1 (by rfl) ⟨3837212, by rfl⟩ : syracuseStep 5116283 = 7674425) B7674425
theorem B3410855 : Blo 2273435 3410855 := bstep (se 1 (by rfl) ⟨2558141, by rfl⟩ : syracuseStep 3410855 = 5116283) B5116283
theorem B2273903 : Blo 2273435 2273903 := bstep (se 1 (by rfl) ⟨1705427, by rfl⟩ : syracuseStep 2273903 = 3410855) B3410855
theorem B3410861 : Blo 2273435 3410861 := bbase (se 3 (by rfl) ⟨639536, by rfl⟩ : syracuseStep 3410861 = 1279073) (by norm_num)
theorem B2273907 : Blo 2273435 2273907 := bstep (se 1 (by rfl) ⟨1705430, by rfl⟩ : syracuseStep 2273907 = 3410861) B3410861
theorem B5116301 : Blo 2273435 5116301 := bbase (se 3 (by rfl) ⟨959306, by rfl⟩ : syracuseStep 5116301 = 1918613) (by norm_num)
theorem B3410867 : Blo 2273435 3410867 := bstep (se 1 (by rfl) ⟨2558150, by rfl⟩ : syracuseStep 3410867 = 5116301) B5116301
theorem B2273911 : Blo 2273435 2273911 := bstep (se 1 (by rfl) ⟨1705433, by rfl⟩ : syracuseStep 2273911 = 3410867) B3410867
theorem B2877925 : Blo 2273435 2877925 := bbase (se 4 (by rfl) ⟨269805, by rfl⟩ : syracuseStep 2877925 = 539611) (by norm_num)
theorem B3837233 : Blo 2273435 3837233 := bstep (se 2 (by rfl) ⟨1438962, by rfl⟩ : syracuseStep 3837233 = 2877925) B2877925
theorem B2558155 : Blo 2273435 2558155 := bstep (se 1 (by rfl) ⟨1918616, by rfl⟩ : syracuseStep 2558155 = 3837233) B3837233
theorem B3410873 : Blo 2273435 3410873 := bstep (se 2 (by rfl) ⟨1279077, by rfl⟩ : syracuseStep 3410873 = 2558155) B2558155
theorem B2273915 : Blo 2273435 2273915 := bstep (se 1 (by rfl) ⟨1705436, by rfl⟩ : syracuseStep 2273915 = 3410873) B3410873
theorem B29536597 : Blo 2273435 29536597 := bbase (se 10 (by rfl) ⟨43266, by rfl⟩ : syracuseStep 29536597 = 86533) (by norm_num)
theorem B39382129 : Blo 2273435 39382129 := bstep (se 2 (by rfl) ⟨14768298, by rfl⟩ : syracuseStep 39382129 = 29536597) B29536597
theorem B52509505 : Blo 2273435 52509505 := bstep (se 2 (by rfl) ⟨19691064, by rfl⟩ : syracuseStep 52509505 = 39382129) B39382129
theorem B70012673 : Blo 2273435 70012673 := bstep (se 2 (by rfl) ⟨26254752, by rfl⟩ : syracuseStep 70012673 = 52509505) B52509505
theorem B46675115 : Blo 2273435 46675115 := bstep (se 1 (by rfl) ⟨35006336, by rfl⟩ : syracuseStep 46675115 = 70012673) B70012673
theorem B31116743 : Blo 2273435 31116743 := bstep (se 1 (by rfl) ⟨23337557, by rfl⟩ : syracuseStep 31116743 = 46675115) B46675115
theorem B20744495 : Blo 2273435 20744495 := bstep (se 1 (by rfl) ⟨15558371, by rfl⟩ : syracuseStep 20744495 = 31116743) B31116743
theorem B13829663 : Blo 2273435 13829663 := bstep (se 1 (by rfl) ⟨10372247, by rfl⟩ : syracuseStep 13829663 = 20744495) B20744495
theorem B36879101 : Blo 2273435 36879101 := bstep (se 3 (by rfl) ⟨6914831, by rfl⟩ : syracuseStep 36879101 = 13829663) B13829663
theorem B24586067 : Blo 2273435 24586067 := bstep (se 1 (by rfl) ⟨18439550, by rfl⟩ : syracuseStep 24586067 = 36879101) B36879101
theorem B16390711 : Blo 2273435 16390711 := bstep (se 1 (by rfl) ⟨12293033, by rfl⟩ : syracuseStep 16390711 = 24586067) B24586067
theorem B21854281 : Blo 2273435 21854281 := bstep (se 2 (by rfl) ⟨8195355, by rfl⟩ : syracuseStep 21854281 = 16390711) B16390711
theorem B29139041 : Blo 2273435 29139041 := bstep (se 2 (by rfl) ⟨10927140, by rfl⟩ : syracuseStep 29139041 = 21854281) B21854281
theorem B19426027 : Blo 2273435 19426027 := bstep (se 1 (by rfl) ⟨14569520, by rfl⟩ : syracuseStep 19426027 = 29139041) B29139041
theorem B25901369 : Blo 2273435 25901369 := bstep (se 2 (by rfl) ⟨9713013, by rfl⟩ : syracuseStep 25901369 = 19426027) B19426027
theorem B17267579 : Blo 2273435 17267579 := bstep (se 1 (by rfl) ⟨12950684, by rfl⟩ : syracuseStep 17267579 = 25901369) B25901369
theorem B11511719 : Blo 2273435 11511719 := bstep (se 1 (by rfl) ⟨8633789, by rfl⟩ : syracuseStep 11511719 = 17267579) B17267579
theorem B7674479 : Blo 2273435 7674479 := bstep (se 1 (by rfl) ⟨5755859, by rfl⟩ : syracuseStep 7674479 = 11511719) B11511719
theorem B5116319 : Blo 2273435 5116319 := bstep (se 1 (by rfl) ⟨3837239, by rfl⟩ : syracuseStep 5116319 = 7674479) B7674479
theorem B3410879 : Blo 2273435 3410879 := bstep (se 1 (by rfl) ⟨2558159, by rfl⟩ : syracuseStep 3410879 = 5116319) B5116319
theorem B2273919 : Blo 2273435 2273919 := bstep (se 1 (by rfl) ⟨1705439, by rfl⟩ : syracuseStep 2273919 = 3410879) B3410879
theorem B3410885 : Blo 2273435 3410885 := bbase (se 4 (by rfl) ⟨319770, by rfl⟩ : syracuseStep 3410885 = 639541) (by norm_num)
theorem B2273923 : Blo 2273435 2273923 := bstep (se 1 (by rfl) ⟨1705442, by rfl⟩ : syracuseStep 2273923 = 3410885) B3410885
theorem B3837253 : Blo 2273435 3837253 := bbase (se 4 (by rfl) ⟨359742, by rfl⟩ : syracuseStep 3837253 = 719485) (by norm_num)
theorem B5116337 : Blo 2273435 5116337 := bstep (se 2 (by rfl) ⟨1918626, by rfl⟩ : syracuseStep 5116337 = 3837253) B3837253
theorem B3410891 : Blo 2273435 3410891 := bstep (se 1 (by rfl) ⟨2558168, by rfl⟩ : syracuseStep 3410891 = 5116337) B5116337
theorem B2273927 : Blo 2273435 2273927 := bstep (se 1 (by rfl) ⟨1705445, by rfl⟩ : syracuseStep 2273927 = 3410891) B3410891
theorem B2558173 : Blo 2273435 2558173 := bbase (se 3 (by rfl) ⟨479657, by rfl⟩ : syracuseStep 2558173 = 959315) (by norm_num)
theorem B3410897 : Blo 2273435 3410897 := bstep (se 2 (by rfl) ⟨1279086, by rfl⟩ : syracuseStep 3410897 = 2558173) B2558173
theorem B2273931 : Blo 2273435 2273931 := bstep (se 1 (by rfl) ⟨1705448, by rfl⟩ : syracuseStep 2273931 = 3410897) B3410897
theorem B7674533 : Blo 2273435 7674533 := bbase (se 4 (by rfl) ⟨719487, by rfl⟩ : syracuseStep 7674533 = 1438975) (by norm_num)
theorem B5116355 : Blo 2273435 5116355 := bstep (se 1 (by rfl) ⟨3837266, by rfl⟩ : syracuseStep 5116355 = 7674533) B7674533
theorem B3410903 : Blo 2273435 3410903 := bstep (se 1 (by rfl) ⟨2558177, by rfl⟩ : syracuseStep 3410903 = 5116355) B5116355
theorem B2273935 : Blo 2273435 2273935 := bstep (se 1 (by rfl) ⟨1705451, by rfl⟩ : syracuseStep 2273935 = 3410903) B3410903
theorem B3410909 : Blo 2273435 3410909 := bbase (se 3 (by rfl) ⟨639545, by rfl⟩ : syracuseStep 3410909 = 1279091) (by norm_num)
theorem B2273939 : Blo 2273435 2273939 := bstep (se 1 (by rfl) ⟨1705454, by rfl⟩ : syracuseStep 2273939 = 3410909) B3410909
theorem B5116373 : Blo 2273435 5116373 := bbase (se 7 (by rfl) ⟨59957, by rfl⟩ : syracuseStep 5116373 = 119915) (by norm_num)
theorem B3410915 : Blo 2273435 3410915 := bstep (se 1 (by rfl) ⟨2558186, by rfl⟩ : syracuseStep 3410915 = 5116373) B5116373
theorem B2273943 : Blo 2273435 2273943 := bstep (se 1 (by rfl) ⟨1705457, by rfl⟩ : syracuseStep 2273943 = 3410915) B3410915
theorem B4153637 : Blo 2273435 4153637 := bbase (se 4 (by rfl) ⟨389403, by rfl⟩ : syracuseStep 4153637 = 778807) (by norm_num)
theorem B11076365 : Blo 2273435 11076365 := bstep (se 3 (by rfl) ⟨2076818, by rfl⟩ : syracuseStep 11076365 = 4153637) B4153637
theorem B7384243 : Blo 2273435 7384243 := bstep (se 1 (by rfl) ⟨5538182, by rfl⟩ : syracuseStep 7384243 = 11076365) B11076365
theorem B9845657 : Blo 2273435 9845657 := bstep (se 2 (by rfl) ⟨3692121, by rfl⟩ : syracuseStep 9845657 = 7384243) B7384243
theorem B6563771 : Blo 2273435 6563771 := bstep (se 1 (by rfl) ⟨4922828, by rfl⟩ : syracuseStep 6563771 = 9845657) B9845657
theorem B4375847 : Blo 2273435 4375847 := bstep (se 1 (by rfl) ⟨3281885, by rfl⟩ : syracuseStep 4375847 = 6563771) B6563771
theorem B11668925 : Blo 2273435 11668925 := bstep (se 3 (by rfl) ⟨2187923, by rfl⟩ : syracuseStep 11668925 = 4375847) B4375847
theorem B7779283 : Blo 2273435 7779283 := bstep (se 1 (by rfl) ⟨5834462, by rfl⟩ : syracuseStep 7779283 = 11668925) B11668925
theorem B41489509 : Blo 2273435 41489509 := bstep (se 4 (by rfl) ⟨3889641, by rfl⟩ : syracuseStep 41489509 = 7779283) B7779283
theorem B55319345 : Blo 2273435 55319345 := bstep (se 2 (by rfl) ⟨20744754, by rfl⟩ : syracuseStep 55319345 = 41489509) B41489509
theorem B36879563 : Blo 2273435 36879563 := bstep (se 1 (by rfl) ⟨27659672, by rfl⟩ : syracuseStep 36879563 = 55319345) B55319345
theorem B24586375 : Blo 2273435 24586375 := bstep (se 1 (by rfl) ⟨18439781, by rfl⟩ : syracuseStep 24586375 = 36879563) B36879563
theorem B32781833 : Blo 2273435 32781833 := bstep (se 2 (by rfl) ⟨12293187, by rfl⟩ : syracuseStep 32781833 = 24586375) B24586375
theorem B21854555 : Blo 2273435 21854555 := bstep (se 1 (by rfl) ⟨16390916, by rfl⟩ : syracuseStep 21854555 = 32781833) B32781833
theorem B14569703 : Blo 2273435 14569703 := bstep (se 1 (by rfl) ⟨10927277, by rfl⟩ : syracuseStep 14569703 = 21854555) B21854555
theorem B9713135 : Blo 2273435 9713135 := bstep (se 1 (by rfl) ⟨7284851, by rfl⟩ : syracuseStep 9713135 = 14569703) B14569703
theorem B6475423 : Blo 2273435 6475423 := bstep (se 1 (by rfl) ⟨4856567, by rfl⟩ : syracuseStep 6475423 = 9713135) B9713135
theorem B8633897 : Blo 2273435 8633897 := bstep (se 2 (by rfl) ⟨3237711, by rfl⟩ : syracuseStep 8633897 = 6475423) B6475423
theorem B5755931 : Blo 2273435 5755931 := bstep (se 1 (by rfl) ⟨4316948, by rfl⟩ : syracuseStep 5755931 = 8633897) B8633897
theorem B3837287 : Blo 2273435 3837287 := bstep (se 1 (by rfl) ⟨2877965, by rfl⟩ : syracuseStep 3837287 = 5755931) B5755931
theorem B2558191 : Blo 2273435 2558191 := bstep (se 1 (by rfl) ⟨1918643, by rfl⟩ : syracuseStep 2558191 = 3837287) B3837287
theorem B3410921 : Blo 2273435 3410921 := bstep (se 2 (by rfl) ⟨1279095, by rfl⟩ : syracuseStep 3410921 = 2558191) B2558191
theorem B2273947 : Blo 2273435 2273947 := bstep (se 1 (by rfl) ⟨1705460, by rfl⟩ : syracuseStep 2273947 = 3410921) B3410921
theorem B132916565 : Blo 2273435 132916565 := bbase (se 12 (by rfl) ⟨48675, by rfl⟩ : syracuseStep 132916565 = 97351) (by norm_num)
theorem B88611043 : Blo 2273435 88611043 := bstep (se 1 (by rfl) ⟨66458282, by rfl⟩ : syracuseStep 88611043 = 132916565) B132916565
theorem B118148057 : Blo 2273435 118148057 := bstep (se 2 (by rfl) ⟨44305521, by rfl⟩ : syracuseStep 118148057 = 88611043) B88611043
theorem B78765371 : Blo 2273435 78765371 := bstep (se 1 (by rfl) ⟨59074028, by rfl⟩ : syracuseStep 78765371 = 118148057) B118148057
theorem B52510247 : Blo 2273435 52510247 := bstep (se 1 (by rfl) ⟨39382685, by rfl⟩ : syracuseStep 52510247 = 78765371) B78765371
theorem B35006831 : Blo 2273435 35006831 := bstep (se 1 (by rfl) ⟨26255123, by rfl⟩ : syracuseStep 35006831 = 52510247) B52510247
theorem B23337887 : Blo 2273435 23337887 := bstep (se 1 (by rfl) ⟨17503415, by rfl⟩ : syracuseStep 23337887 = 35006831) B35006831
theorem B62234365 : Blo 2273435 62234365 := bstep (se 3 (by rfl) ⟨11668943, by rfl⟩ : syracuseStep 62234365 = 23337887) B23337887
theorem B82979153 : Blo 2273435 82979153 := bstep (se 2 (by rfl) ⟨31117182, by rfl⟩ : syracuseStep 82979153 = 62234365) B62234365
theorem B55319435 : Blo 2273435 55319435 := bstep (se 1 (by rfl) ⟨41489576, by rfl⟩ : syracuseStep 55319435 = 82979153) B82979153
theorem B36879623 : Blo 2273435 36879623 := bstep (se 1 (by rfl) ⟨27659717, by rfl⟩ : syracuseStep 36879623 = 55319435) B55319435
theorem B24586415 : Blo 2273435 24586415 := bstep (se 1 (by rfl) ⟨18439811, by rfl⟩ : syracuseStep 24586415 = 36879623) B36879623
theorem B16390943 : Blo 2273435 16390943 := bstep (se 1 (by rfl) ⟨12293207, by rfl⟩ : syracuseStep 16390943 = 24586415) B24586415
theorem B10927295 : Blo 2273435 10927295 := bstep (se 1 (by rfl) ⟨8195471, by rfl⟩ : syracuseStep 10927295 = 16390943) B16390943
theorem B7284863 : Blo 2273435 7284863 := bstep (se 1 (by rfl) ⟨5463647, by rfl⟩ : syracuseStep 7284863 = 10927295) B10927295
theorem B19426301 : Blo 2273435 19426301 := bstep (se 3 (by rfl) ⟨3642431, by rfl⟩ : syracuseStep 19426301 = 7284863) B7284863
theorem B12950867 : Blo 2273435 12950867 := bstep (se 1 (by rfl) ⟨9713150, by rfl⟩ : syracuseStep 12950867 = 19426301) B19426301
theorem B8633911 : Blo 2273435 8633911 := bstep (se 1 (by rfl) ⟨6475433, by rfl⟩ : syracuseStep 8633911 = 12950867) B12950867
theorem B11511881 : Blo 2273435 11511881 := bstep (se 2 (by rfl) ⟨4316955, by rfl⟩ : syracuseStep 11511881 = 8633911) B8633911
theorem B7674587 : Blo 2273435 7674587 := bstep (se 1 (by rfl) ⟨5755940, by rfl⟩ : syracuseStep 7674587 = 11511881) B11511881
theorem B5116391 : Blo 2273435 5116391 := bstep (se 1 (by rfl) ⟨3837293, by rfl⟩ : syracuseStep 5116391 = 7674587) B7674587
theorem B3410927 : Blo 2273435 3410927 := bstep (se 1 (by rfl) ⟨2558195, by rfl⟩ : syracuseStep 3410927 = 5116391) B5116391
theorem B2273951 : Blo 2273435 2273951 := bstep (se 1 (by rfl) ⟨1705463, by rfl⟩ : syracuseStep 2273951 = 3410927) B3410927
theorem B3410933 : Blo 2273435 3410933 := bbase (se 5 (by rfl) ⟨159887, by rfl⟩ : syracuseStep 3410933 = 319775) (by norm_num)
theorem B2273955 : Blo 2273435 2273955 := bstep (se 1 (by rfl) ⟨1705466, by rfl⟩ : syracuseStep 2273955 = 3410933) B3410933
theorem B3642445 : Blo 2273435 3642445 := bbase (se 3 (by rfl) ⟨682958, by rfl⟩ : syracuseStep 3642445 = 1365917) (by norm_num)
theorem B4856593 : Blo 2273435 4856593 := bstep (se 2 (by rfl) ⟨1821222, by rfl⟩ : syracuseStep 4856593 = 3642445) B3642445
theorem B6475457 : Blo 2273435 6475457 := bstep (se 2 (by rfl) ⟨2428296, by rfl⟩ : syracuseStep 6475457 = 4856593) B4856593
theorem B4316971 : Blo 2273435 4316971 := bstep (se 1 (by rfl) ⟨3237728, by rfl⟩ : syracuseStep 4316971 = 6475457) B6475457
theorem B5755961 : Blo 2273435 5755961 := bstep (se 2 (by rfl) ⟨2158485, by rfl⟩ : syracuseStep 5755961 = 4316971) B4316971
theorem B3837307 : Blo 2273435 3837307 := bstep (se 1 (by rfl) ⟨2877980, by rfl⟩ : syracuseStep 3837307 = 5755961) B5755961
theorem B5116409 : Blo 2273435 5116409 := bstep (se 2 (by rfl) ⟨1918653, by rfl⟩ : syracuseStep 5116409 = 3837307) B3837307
theorem B3410939 : Blo 2273435 3410939 := bstep (se 1 (by rfl) ⟨2558204, by rfl⟩ : syracuseStep 3410939 = 5116409) B5116409
theorem B2273959 : Blo 2273435 2273959 := bstep (se 1 (by rfl) ⟨1705469, by rfl⟩ : syracuseStep 2273959 = 3410939) B3410939
theorem B2558209 : Blo 2273435 2558209 := bbase (se 2 (by rfl) ⟨959328, by rfl⟩ : syracuseStep 2558209 = 1918657) (by norm_num)
theorem B3410945 : Blo 2273435 3410945 := bstep (se 2 (by rfl) ⟨1279104, by rfl⟩ : syracuseStep 3410945 = 2558209) B2558209
theorem B2273963 : Blo 2273435 2273963 := bstep (se 1 (by rfl) ⟨1705472, by rfl⟩ : syracuseStep 2273963 = 3410945) B3410945
theorem B5755981 : Blo 2273435 5755981 := bbase (se 3 (by rfl) ⟨1079246, by rfl⟩ : syracuseStep 5755981 = 2158493) (by norm_num)
theorem B7674641 : Blo 2273435 7674641 := bstep (se 2 (by rfl) ⟨2877990, by rfl⟩ : syracuseStep 7674641 = 5755981) B5755981
theorem B5116427 : Blo 2273435 5116427 := bstep (se 1 (by rfl) ⟨3837320, by rfl⟩ : syracuseStep 5116427 = 7674641) B7674641
theorem B3410951 : Blo 2273435 3410951 := bstep (se 1 (by rfl) ⟨2558213, by rfl⟩ : syracuseStep 3410951 = 5116427) B5116427
theorem B2273967 : Blo 2273435 2273967 := bstep (se 1 (by rfl) ⟨1705475, by rfl⟩ : syracuseStep 2273967 = 3410951) B3410951
theorem B3410957 : Blo 2273435 3410957 := bbase (se 3 (by rfl) ⟨639554, by rfl⟩ : syracuseStep 3410957 = 1279109) (by norm_num)
theorem B2273971 : Blo 2273435 2273971 := bstep (se 1 (by rfl) ⟨1705478, by rfl⟩ : syracuseStep 2273971 = 3410957) B3410957
theorem B5116445 : Blo 2273435 5116445 := bbase (se 3 (by rfl) ⟨959333, by rfl⟩ : syracuseStep 5116445 = 1918667) (by norm_num)
theorem B3410963 : Blo 2273435 3410963 := bstep (se 1 (by rfl) ⟨2558222, by rfl⟩ : syracuseStep 3410963 = 5116445) B5116445
theorem B2273975 : Blo 2273435 2273975 := bstep (se 1 (by rfl) ⟨1705481, by rfl⟩ : syracuseStep 2273975 = 3410963) B3410963
theorem B3837341 : Blo 2273435 3837341 := bbase (se 3 (by rfl) ⟨719501, by rfl⟩ : syracuseStep 3837341 = 1439003) (by norm_num)
theorem B2558227 : Blo 2273435 2558227 := bstep (se 1 (by rfl) ⟨1918670, by rfl⟩ : syracuseStep 2558227 = 3837341) B3837341
theorem B3410969 : Blo 2273435 3410969 := bstep (se 2 (by rfl) ⟨1279113, by rfl⟩ : syracuseStep 3410969 = 2558227) B2558227
theorem B2273979 : Blo 2273435 2273979 := bstep (se 1 (by rfl) ⟨1705484, by rfl⟩ : syracuseStep 2273979 = 3410969) B3410969
theorem B2305009 : Blo 2273435 2305009 := bbase (se 2 (by rfl) ⟨864378, by rfl⟩ : syracuseStep 2305009 = 1728757) (by norm_num)
theorem B3073345 : Blo 2273435 3073345 := bstep (se 2 (by rfl) ⟨1152504, by rfl⟩ : syracuseStep 3073345 = 2305009) B2305009
theorem B16391173 : Blo 2273435 16391173 := bstep (se 4 (by rfl) ⟨1536672, by rfl⟩ : syracuseStep 16391173 = 3073345) B3073345
theorem B21854897 : Blo 2273435 21854897 := bstep (se 2 (by rfl) ⟨8195586, by rfl⟩ : syracuseStep 21854897 = 16391173) B16391173
theorem B14569931 : Blo 2273435 14569931 := bstep (se 1 (by rfl) ⟨10927448, by rfl⟩ : syracuseStep 14569931 = 21854897) B21854897
theorem B9713287 : Blo 2273435 9713287 := bstep (se 1 (by rfl) ⟨7284965, by rfl⟩ : syracuseStep 9713287 = 14569931) B14569931
theorem B12951049 : Blo 2273435 12951049 := bstep (se 2 (by rfl) ⟨4856643, by rfl⟩ : syracuseStep 12951049 = 9713287) B9713287
theorem B17268065 : Blo 2273435 17268065 := bstep (se 2 (by rfl) ⟨6475524, by rfl⟩ : syracuseStep 17268065 = 12951049) B12951049
theorem B11512043 : Blo 2273435 11512043 := bstep (se 1 (by rfl) ⟨8634032, by rfl⟩ : syracuseStep 11512043 = 17268065) B17268065
theorem B7674695 : Blo 2273435 7674695 := bstep (se 1 (by rfl) ⟨5756021, by rfl⟩ : syracuseStep 7674695 = 11512043) B11512043
theorem B5116463 : Blo 2273435 5116463 := bstep (se 1 (by rfl) ⟨3837347, by rfl⟩ : syracuseStep 5116463 = 7674695) B7674695
theorem B3410975 : Blo 2273435 3410975 := bstep (se 1 (by rfl) ⟨2558231, by rfl⟩ : syracuseStep 3410975 = 5116463) B5116463
theorem B2273983 : Blo 2273435 2273983 := bstep (se 1 (by rfl) ⟨1705487, by rfl⟩ : syracuseStep 2273983 = 3410975) B3410975
theorem B3410981 : Blo 2273435 3410981 := bbase (se 4 (by rfl) ⟨319779, by rfl⟩ : syracuseStep 3410981 = 639559) (by norm_num)
theorem B2273987 : Blo 2273435 2273987 := bstep (se 1 (by rfl) ⟨1705490, by rfl⟩ : syracuseStep 2273987 = 3410981) B3410981
theorem B2878021 : Blo 2273435 2878021 := bbase (se 4 (by rfl) ⟨269814, by rfl⟩ : syracuseStep 2878021 = 539629) (by norm_num)
theorem B3837361 : Blo 2273435 3837361 := bstep (se 2 (by rfl) ⟨1439010, by rfl⟩ : syracuseStep 3837361 = 2878021) B2878021
theorem B5116481 : Blo 2273435 5116481 := bstep (se 2 (by rfl) ⟨1918680, by rfl⟩ : syracuseStep 5116481 = 3837361) B3837361
theorem B3410987 : Blo 2273435 3410987 := bstep (se 1 (by rfl) ⟨2558240, by rfl⟩ : syracuseStep 3410987 = 5116481) B5116481
theorem B2273991 : Blo 2273435 2273991 := bstep (se 1 (by rfl) ⟨1705493, by rfl⟩ : syracuseStep 2273991 = 3410987) B3410987
theorem B2558245 : Blo 2273435 2558245 := bbase (se 4 (by rfl) ⟨239835, by rfl⟩ : syracuseStep 2558245 = 479671) (by norm_num)
theorem B3410993 : Blo 2273435 3410993 := bstep (se 2 (by rfl) ⟨1279122, by rfl⟩ : syracuseStep 3410993 = 2558245) B2558245
theorem B2273995 : Blo 2273435 2273995 := bstep (se 1 (by rfl) ⟨1705496, by rfl⟩ : syracuseStep 2273995 = 3410993) B3410993
theorem B3642509 : Blo 2273435 3642509 := bbase (se 3 (by rfl) ⟨682970, by rfl⟩ : syracuseStep 3642509 = 1365941) (by norm_num)
theorem B9713357 : Blo 2273435 9713357 := bstep (se 3 (by rfl) ⟨1821254, by rfl⟩ : syracuseStep 9713357 = 3642509) B3642509
theorem B6475571 : Blo 2273435 6475571 := bstep (se 1 (by rfl) ⟨4856678, by rfl⟩ : syracuseStep 6475571 = 9713357) B9713357
theorem B4317047 : Blo 2273435 4317047 := bstep (se 1 (by rfl) ⟨3237785, by rfl⟩ : syracuseStep 4317047 = 6475571) B6475571
theorem B2878031 : Blo 2273435 2878031 := bstep (se 1 (by rfl) ⟨2158523, by rfl⟩ : syracuseStep 2878031 = 4317047) B4317047
theorem B7674749 : Blo 2273435 7674749 := bstep (se 3 (by rfl) ⟨1439015, by rfl⟩ : syracuseStep 7674749 = 2878031) B2878031
theorem B5116499 : Blo 2273435 5116499 := bstep (se 1 (by rfl) ⟨3837374, by rfl⟩ : syracuseStep 5116499 = 7674749) B7674749
theorem B3410999 : Blo 2273435 3410999 := bstep (se 1 (by rfl) ⟨2558249, by rfl⟩ : syracuseStep 3410999 = 5116499) B5116499
theorem B2273999 : Blo 2273435 2273999 := bstep (se 1 (by rfl) ⟨1705499, by rfl⟩ : syracuseStep 2273999 = 3410999) B3410999
theorem B3411005 : Blo 2273435 3411005 := bbase (se 3 (by rfl) ⟨639563, by rfl⟩ : syracuseStep 3411005 = 1279127) (by norm_num)
theorem B2274003 : Blo 2273435 2274003 := bstep (se 1 (by rfl) ⟨1705502, by rfl⟩ : syracuseStep 2274003 = 3411005) B3411005
theorem B5116517 : Blo 2273435 5116517 := bbase (se 4 (by rfl) ⟨479673, by rfl⟩ : syracuseStep 5116517 = 959347) (by norm_num)
theorem B3411011 : Blo 2273435 3411011 := bstep (se 1 (by rfl) ⟨2558258, by rfl⟩ : syracuseStep 3411011 = 5116517) B5116517
theorem B2274007 : Blo 2273435 2274007 := bstep (se 1 (by rfl) ⟨1705505, by rfl⟩ : syracuseStep 2274007 = 3411011) B3411011
theorem B5756093 : Blo 2273435 5756093 := bbase (se 3 (by rfl) ⟨1079267, by rfl⟩ : syracuseStep 5756093 = 2158535) (by norm_num)
theorem B3837395 : Blo 2273435 3837395 := bstep (se 1 (by rfl) ⟨2878046, by rfl⟩ : syracuseStep 3837395 = 5756093) B5756093
theorem B2558263 : Blo 2273435 2558263 := bstep (se 1 (by rfl) ⟨1918697, by rfl⟩ : syracuseStep 2558263 = 3837395) B3837395
theorem B3411017 : Blo 2273435 3411017 := bstep (se 2 (by rfl) ⟨1279131, by rfl⟩ : syracuseStep 3411017 = 2558263) B2558263
theorem B2274011 : Blo 2273435 2274011 := bstep (se 1 (by rfl) ⟨1705508, by rfl⟩ : syracuseStep 2274011 = 3411017) B3411017
theorem B4317077 : Blo 2273435 4317077 := bbase (se 6 (by rfl) ⟨101181, by rfl⟩ : syracuseStep 4317077 = 202363) (by norm_num)
theorem B11512205 : Blo 2273435 11512205 := bstep (se 3 (by rfl) ⟨2158538, by rfl⟩ : syracuseStep 11512205 = 4317077) B4317077
theorem B7674803 : Blo 2273435 7674803 := bstep (se 1 (by rfl) ⟨5756102, by rfl⟩ : syracuseStep 7674803 = 11512205) B11512205
theorem B5116535 : Blo 2273435 5116535 := bstep (se 1 (by rfl) ⟨3837401, by rfl⟩ : syracuseStep 5116535 = 7674803) B7674803
theorem B3411023 : Blo 2273435 3411023 := bstep (se 1 (by rfl) ⟨2558267, by rfl⟩ : syracuseStep 3411023 = 5116535) B5116535
theorem B2274015 : Blo 2273435 2274015 := bstep (se 1 (by rfl) ⟨1705511, by rfl⟩ : syracuseStep 2274015 = 3411023) B3411023
theorem B3411029 : Blo 2273435 3411029 := bbase (se 8 (by rfl) ⟨19986, by rfl⟩ : syracuseStep 3411029 = 39973) (by norm_num)
theorem B2274019 : Blo 2273435 2274019 := bstep (se 1 (by rfl) ⟨1705514, by rfl⟩ : syracuseStep 2274019 = 3411029) B3411029
theorem B5463821 : Blo 2273435 5463821 := bbase (se 3 (by rfl) ⟨1024466, by rfl⟩ : syracuseStep 5463821 = 2048933) (by norm_num)
theorem B14570189 : Blo 2273435 14570189 := bstep (se 3 (by rfl) ⟨2731910, by rfl⟩ : syracuseStep 14570189 = 5463821) B5463821
theorem B9713459 : Blo 2273435 9713459 := bstep (se 1 (by rfl) ⟨7285094, by rfl⟩ : syracuseStep 9713459 = 14570189) B14570189
theorem B6475639 : Blo 2273435 6475639 := bstep (se 1 (by rfl) ⟨4856729, by rfl⟩ : syracuseStep 6475639 = 9713459) B9713459
theorem B8634185 : Blo 2273435 8634185 := bstep (se 2 (by rfl) ⟨3237819, by rfl⟩ : syracuseStep 8634185 = 6475639) B6475639
theorem B5756123 : Blo 2273435 5756123 := bstep (se 1 (by rfl) ⟨4317092, by rfl⟩ : syracuseStep 5756123 = 8634185) B8634185
theorem B3837415 : Blo 2273435 3837415 := bstep (se 1 (by rfl) ⟨2878061, by rfl⟩ : syracuseStep 3837415 = 5756123) B5756123
theorem B5116553 : Blo 2273435 5116553 := bstep (se 2 (by rfl) ⟨1918707, by rfl⟩ : syracuseStep 5116553 = 3837415) B3837415
theorem B3411035 : Blo 2273435 3411035 := bstep (se 1 (by rfl) ⟨2558276, by rfl⟩ : syracuseStep 3411035 = 5116553) B5116553
theorem B2274023 : Blo 2273435 2274023 := bstep (se 1 (by rfl) ⟨1705517, by rfl⟩ : syracuseStep 2274023 = 3411035) B3411035
theorem B2558281 : Blo 2273435 2558281 := bbase (se 2 (by rfl) ⟨959355, by rfl⟩ : syracuseStep 2558281 = 1918711) (by norm_num)
theorem B3411041 : Blo 2273435 3411041 := bstep (se 2 (by rfl) ⟨1279140, by rfl⟩ : syracuseStep 3411041 = 2558281) B2558281
theorem B2274027 : Blo 2273435 2274027 := bstep (se 1 (by rfl) ⟨1705520, by rfl⟩ : syracuseStep 2274027 = 3411041) B3411041
theorem B10116517 : Blo 2273435 10116517 := bbase (se 4 (by rfl) ⟨948423, by rfl⟩ : syracuseStep 10116517 = 1896847) (by norm_num)
theorem B13488689 : Blo 2273435 13488689 := bstep (se 2 (by rfl) ⟨5058258, by rfl⟩ : syracuseStep 13488689 = 10116517) B10116517
theorem B35969837 : Blo 2273435 35969837 := bstep (se 3 (by rfl) ⟨6744344, by rfl⟩ : syracuseStep 35969837 = 13488689) B13488689
theorem B95919565 : Blo 2273435 95919565 := bstep (se 3 (by rfl) ⟨17984918, by rfl⟩ : syracuseStep 95919565 = 35969837) B35969837
theorem B127892753 : Blo 2273435 127892753 := bstep (se 2 (by rfl) ⟨47959782, by rfl⟩ : syracuseStep 127892753 = 95919565) B95919565
theorem B85261835 : Blo 2273435 85261835 := bstep (se 1 (by rfl) ⟨63946376, by rfl⟩ : syracuseStep 85261835 = 127892753) B127892753
theorem B56841223 : Blo 2273435 56841223 := bstep (se 1 (by rfl) ⟨42630917, by rfl⟩ : syracuseStep 56841223 = 85261835) B85261835
theorem B75788297 : Blo 2273435 75788297 := bstep (se 2 (by rfl) ⟨28420611, by rfl⟩ : syracuseStep 75788297 = 56841223) B56841223
theorem B50525531 : Blo 2273435 50525531 := bstep (se 1 (by rfl) ⟨37894148, by rfl⟩ : syracuseStep 50525531 = 75788297) B75788297
theorem B33683687 : Blo 2273435 33683687 := bstep (se 1 (by rfl) ⟨25262765, by rfl⟩ : syracuseStep 33683687 = 50525531) B50525531
theorem B22455791 : Blo 2273435 22455791 := bstep (se 1 (by rfl) ⟨16841843, by rfl⟩ : syracuseStep 22455791 = 33683687) B33683687
theorem B14970527 : Blo 2273435 14970527 := bstep (se 1 (by rfl) ⟨11227895, by rfl⟩ : syracuseStep 14970527 = 22455791) B22455791
theorem B9980351 : Blo 2273435 9980351 := bstep (se 1 (by rfl) ⟨7485263, by rfl⟩ : syracuseStep 9980351 = 14970527) B14970527
theorem B6653567 : Blo 2273435 6653567 := bstep (se 1 (by rfl) ⟨4990175, by rfl⟩ : syracuseStep 6653567 = 9980351) B9980351
theorem B4435711 : Blo 2273435 4435711 := bstep (se 1 (by rfl) ⟨3326783, by rfl⟩ : syracuseStep 4435711 = 6653567) B6653567
theorem B23657125 : Blo 2273435 23657125 := bstep (se 4 (by rfl) ⟨2217855, by rfl⟩ : syracuseStep 23657125 = 4435711) B4435711
theorem B31542833 : Blo 2273435 31542833 := bstep (se 2 (by rfl) ⟨11828562, by rfl⟩ : syracuseStep 31542833 = 23657125) B23657125
theorem B21028555 : Blo 2273435 21028555 := bstep (se 1 (by rfl) ⟨15771416, by rfl⟩ : syracuseStep 21028555 = 31542833) B31542833
theorem B28038073 : Blo 2273435 28038073 := bstep (se 2 (by rfl) ⟨10514277, by rfl⟩ : syracuseStep 28038073 = 21028555) B21028555
theorem B37384097 : Blo 2273435 37384097 := bstep (se 2 (by rfl) ⟨14019036, by rfl⟩ : syracuseStep 37384097 = 28038073) B28038073
theorem B99690925 : Blo 2273435 99690925 := bstep (se 3 (by rfl) ⟨18692048, by rfl⟩ : syracuseStep 99690925 = 37384097) B37384097
theorem B132921233 : Blo 2273435 132921233 := bstep (se 2 (by rfl) ⟨49845462, by rfl⟩ : syracuseStep 132921233 = 99690925) B99690925
theorem B88614155 : Blo 2273435 88614155 := bstep (se 1 (by rfl) ⟨66460616, by rfl⟩ : syracuseStep 88614155 = 132921233) B132921233
theorem B59076103 : Blo 2273435 59076103 := bstep (se 1 (by rfl) ⟨44307077, by rfl⟩ : syracuseStep 59076103 = 88614155) B88614155
theorem B78768137 : Blo 2273435 78768137 := bstep (se 2 (by rfl) ⟨29538051, by rfl⟩ : syracuseStep 78768137 = 59076103) B59076103
theorem B210048365 : Blo 2273435 210048365 := bstep (se 3 (by rfl) ⟨39384068, by rfl⟩ : syracuseStep 210048365 = 78768137) B78768137
theorem B140032243 : Blo 2273435 140032243 := bstep (se 1 (by rfl) ⟨105024182, by rfl⟩ : syracuseStep 140032243 = 210048365) B210048365
theorem B186709657 : Blo 2273435 186709657 := bstep (se 2 (by rfl) ⟨70016121, by rfl⟩ : syracuseStep 186709657 = 140032243) B140032243
theorem B248946209 : Blo 2273435 248946209 := bstep (se 2 (by rfl) ⟨93354828, by rfl⟩ : syracuseStep 248946209 = 186709657) B186709657
theorem B165964139 : Blo 2273435 165964139 := bstep (se 1 (by rfl) ⟨124473104, by rfl⟩ : syracuseStep 165964139 = 248946209) B248946209
theorem B110642759 : Blo 2273435 110642759 := bstep (se 1 (by rfl) ⟨82982069, by rfl⟩ : syracuseStep 110642759 = 165964139) B165964139
theorem B73761839 : Blo 2273435 73761839 := bstep (se 1 (by rfl) ⟨55321379, by rfl⟩ : syracuseStep 73761839 = 110642759) B110642759
theorem B49174559 : Blo 2273435 49174559 := bstep (se 1 (by rfl) ⟨36880919, by rfl⟩ : syracuseStep 49174559 = 73761839) B73761839
theorem B32783039 : Blo 2273435 32783039 := bstep (se 1 (by rfl) ⟨24587279, by rfl⟩ : syracuseStep 32783039 = 49174559) B49174559
theorem B21855359 : Blo 2273435 21855359 := bstep (se 1 (by rfl) ⟨16391519, by rfl⟩ : syracuseStep 21855359 = 32783039) B32783039
theorem B14570239 : Blo 2273435 14570239 := bstep (se 1 (by rfl) ⟨10927679, by rfl⟩ : syracuseStep 14570239 = 21855359) B21855359
theorem B19426985 : Blo 2273435 19426985 := bstep (se 2 (by rfl) ⟨7285119, by rfl⟩ : syracuseStep 19426985 = 14570239) B14570239
theorem B12951323 : Blo 2273435 12951323 := bstep (se 1 (by rfl) ⟨9713492, by rfl⟩ : syracuseStep 12951323 = 19426985) B19426985
theorem B8634215 : Blo 2273435 8634215 := bstep (se 1 (by rfl) ⟨6475661, by rfl⟩ : syracuseStep 8634215 = 12951323) B12951323
theorem B5756143 : Blo 2273435 5756143 := bstep (se 1 (by rfl) ⟨4317107, by rfl⟩ : syracuseStep 5756143 = 8634215) B8634215
theorem B7674857 : Blo 2273435 7674857 := bstep (se 2 (by rfl) ⟨2878071, by rfl⟩ : syracuseStep 7674857 = 5756143) B5756143
theorem B5116571 : Blo 2273435 5116571 := bstep (se 1 (by rfl) ⟨3837428, by rfl⟩ : syracuseStep 5116571 = 7674857) B7674857
theorem B3411047 : Blo 2273435 3411047 := bstep (se 1 (by rfl) ⟨2558285, by rfl⟩ : syracuseStep 3411047 = 5116571) B5116571
theorem B2274031 : Blo 2273435 2274031 := bstep (se 1 (by rfl) ⟨1705523, by rfl⟩ : syracuseStep 2274031 = 3411047) B3411047
theorem B3411053 : Blo 2273435 3411053 := bbase (se 3 (by rfl) ⟨639572, by rfl⟩ : syracuseStep 3411053 = 1279145) (by norm_num)
theorem B2274035 : Blo 2273435 2274035 := bstep (se 1 (by rfl) ⟨1705526, by rfl⟩ : syracuseStep 2274035 = 3411053) B3411053
theorem B5116589 : Blo 2273435 5116589 := bbase (se 3 (by rfl) ⟨959360, by rfl⟩ : syracuseStep 5116589 = 1918721) (by norm_num)
theorem B3411059 : Blo 2273435 3411059 := bstep (se 1 (by rfl) ⟨2558294, by rfl⟩ : syracuseStep 3411059 = 5116589) B5116589
theorem B2274039 : Blo 2273435 2274039 := bstep (se 1 (by rfl) ⟨1705529, by rfl⟩ : syracuseStep 2274039 = 3411059) B3411059
theorem B4856773 : Blo 2273435 4856773 := bbase (se 4 (by rfl) ⟨455322, by rfl⟩ : syracuseStep 4856773 = 910645) (by norm_num)
theorem B6475697 : Blo 2273435 6475697 := bstep (se 2 (by rfl) ⟨2428386, by rfl⟩ : syracuseStep 6475697 = 4856773) B4856773
theorem B4317131 : Blo 2273435 4317131 := bstep (se 1 (by rfl) ⟨3237848, by rfl⟩ : syracuseStep 4317131 = 6475697) B6475697
theorem B2878087 : Blo 2273435 2878087 := bstep (se 1 (by rfl) ⟨2158565, by rfl⟩ : syracuseStep 2878087 = 4317131) B4317131
theorem B3837449 : Blo 2273435 3837449 := bstep (se 2 (by rfl) ⟨1439043, by rfl⟩ : syracuseStep 3837449 = 2878087) B2878087
theorem B2558299 : Blo 2273435 2558299 := bstep (se 1 (by rfl) ⟨1918724, by rfl⟩ : syracuseStep 2558299 = 3837449) B3837449
theorem B3411065 : Blo 2273435 3411065 := bstep (se 2 (by rfl) ⟨1279149, by rfl⟩ : syracuseStep 3411065 = 2558299) B2558299
theorem B2274043 : Blo 2273435 2274043 := bstep (se 1 (by rfl) ⟨1705532, by rfl⟩ : syracuseStep 2274043 = 3411065) B3411065
theorem B6915221 : Blo 2273435 6915221 := bbase (se 6 (by rfl) ⟨162075, by rfl⟩ : syracuseStep 6915221 = 324151) (by norm_num)
theorem B4610147 : Blo 2273435 4610147 := bstep (se 1 (by rfl) ⟨3457610, by rfl⟩ : syracuseStep 4610147 = 6915221) B6915221
theorem B49174901 : Blo 2273435 49174901 := bstep (se 5 (by rfl) ⟨2305073, by rfl⟩ : syracuseStep 49174901 = 4610147) B4610147
theorem B32783267 : Blo 2273435 32783267 := bstep (se 1 (by rfl) ⟨24587450, by rfl⟩ : syracuseStep 32783267 = 49174901) B49174901
theorem B21855511 : Blo 2273435 21855511 := bstep (se 1 (by rfl) ⟨16391633, by rfl⟩ : syracuseStep 21855511 = 32783267) B32783267
theorem B29140681 : Blo 2273435 29140681 := bstep (se 2 (by rfl) ⟨10927755, by rfl⟩ : syracuseStep 29140681 = 21855511) B21855511
theorem B38854241 : Blo 2273435 38854241 := bstep (se 2 (by rfl) ⟨14570340, by rfl⟩ : syracuseStep 38854241 = 29140681) B29140681
theorem B25902827 : Blo 2273435 25902827 := bstep (se 1 (by rfl) ⟨19427120, by rfl⟩ : syracuseStep 25902827 = 38854241) B38854241
theorem B17268551 : Blo 2273435 17268551 := bstep (se 1 (by rfl) ⟨12951413, by rfl⟩ : syracuseStep 17268551 = 25902827) B25902827
theorem B11512367 : Blo 2273435 11512367 := bstep (se 1 (by rfl) ⟨8634275, by rfl⟩ : syracuseStep 11512367 = 17268551) B17268551
theorem B7674911 : Blo 2273435 7674911 := bstep (se 1 (by rfl) ⟨5756183, by rfl⟩ : syracuseStep 7674911 = 11512367) B11512367
theorem B5116607 : Blo 2273435 5116607 := bstep (se 1 (by rfl) ⟨3837455, by rfl⟩ : syracuseStep 5116607 = 7674911) B7674911
theorem B3411071 : Blo 2273435 3411071 := bstep (se 1 (by rfl) ⟨2558303, by rfl⟩ : syracuseStep 3411071 = 5116607) B5116607
theorem B2274047 : Blo 2273435 2274047 := bstep (se 1 (by rfl) ⟨1705535, by rfl⟩ : syracuseStep 2274047 = 3411071) B3411071
theorem B3411077 : Blo 2273435 3411077 := bbase (se 4 (by rfl) ⟨319788, by rfl⟩ : syracuseStep 3411077 = 639577) (by norm_num)
theorem B2274051 : Blo 2273435 2274051 := bstep (se 1 (by rfl) ⟨1705538, by rfl⟩ : syracuseStep 2274051 = 3411077) B3411077
theorem B3837469 : Blo 2273435 3837469 := bbase (se 3 (by rfl) ⟨719525, by rfl⟩ : syracuseStep 3837469 = 1439051) (by norm_num)
theorem B5116625 : Blo 2273435 5116625 := bstep (se 2 (by rfl) ⟨1918734, by rfl⟩ : syracuseStep 5116625 = 3837469) B3837469
theorem B3411083 : Blo 2273435 3411083 := bstep (se 1 (by rfl) ⟨2558312, by rfl⟩ : syracuseStep 3411083 = 5116625) B5116625
theorem B2274055 : Blo 2273435 2274055 := bstep (se 1 (by rfl) ⟨1705541, by rfl⟩ : syracuseStep 2274055 = 3411083) B3411083
theorem B2558317 : Blo 2273435 2558317 := bbase (se 3 (by rfl) ⟨479684, by rfl⟩ : syracuseStep 2558317 = 959369) (by norm_num)
theorem B3411089 : Blo 2273435 3411089 := bstep (se 2 (by rfl) ⟨1279158, by rfl⟩ : syracuseStep 3411089 = 2558317) B2558317
theorem B2274059 : Blo 2273435 2274059 := bstep (se 1 (by rfl) ⟨1705544, by rfl⟩ : syracuseStep 2274059 = 3411089) B3411089
theorem B7674965 : Blo 2273435 7674965 := bbase (se 8 (by rfl) ⟨44970, by rfl⟩ : syracuseStep 7674965 = 89941) (by norm_num)
theorem B5116643 : Blo 2273435 5116643 := bstep (se 1 (by rfl) ⟨3837482, by rfl⟩ : syracuseStep 5116643 = 7674965) B7674965
theorem B3411095 : Blo 2273435 3411095 := bstep (se 1 (by rfl) ⟨2558321, by rfl⟩ : syracuseStep 3411095 = 5116643) B5116643
theorem B2274063 : Blo 2273435 2274063 := bstep (se 1 (by rfl) ⟨1705547, by rfl⟩ : syracuseStep 2274063 = 3411095) B3411095
theorem B3411101 : Blo 2273435 3411101 := bbase (se 3 (by rfl) ⟨639581, by rfl⟩ : syracuseStep 3411101 = 1279163) (by norm_num)
theorem B2274067 : Blo 2273435 2274067 := bstep (se 1 (by rfl) ⟨1705550, by rfl⟩ : syracuseStep 2274067 = 3411101) B3411101
theorem B5116661 : Blo 2273435 5116661 := bbase (se 5 (by rfl) ⟨239843, by rfl⟩ : syracuseStep 5116661 = 479687) (by norm_num)
theorem B3411107 : Blo 2273435 3411107 := bstep (se 1 (by rfl) ⟨2558330, by rfl⟩ : syracuseStep 3411107 = 5116661) B5116661
theorem B2274071 : Blo 2273435 2274071 := bstep (se 1 (by rfl) ⟨1705553, by rfl⟩ : syracuseStep 2274071 = 3411107) B3411107
theorem B2731973 : Blo 2273435 2731973 := bbase (se 4 (by rfl) ⟨256122, by rfl⟩ : syracuseStep 2731973 = 512245) (by norm_num)
theorem B29141045 : Blo 2273435 29141045 := bstep (se 5 (by rfl) ⟨1365986, by rfl⟩ : syracuseStep 29141045 = 2731973) B2731973
theorem B19427363 : Blo 2273435 19427363 := bstep (se 1 (by rfl) ⟨14570522, by rfl⟩ : syracuseStep 19427363 = 29141045) B29141045
theorem B12951575 : Blo 2273435 12951575 := bstep (se 1 (by rfl) ⟨9713681, by rfl⟩ : syracuseStep 12951575 = 19427363) B19427363
theorem B8634383 : Blo 2273435 8634383 := bstep (se 1 (by rfl) ⟨6475787, by rfl⟩ : syracuseStep 8634383 = 12951575) B12951575
theorem B5756255 : Blo 2273435 5756255 := bstep (se 1 (by rfl) ⟨4317191, by rfl⟩ : syracuseStep 5756255 = 8634383) B8634383
theorem B3837503 : Blo 2273435 3837503 := bstep (se 1 (by rfl) ⟨2878127, by rfl⟩ : syracuseStep 3837503 = 5756255) B5756255
theorem B2558335 : Blo 2273435 2558335 := bstep (se 1 (by rfl) ⟨1918751, by rfl⟩ : syracuseStep 2558335 = 3837503) B3837503
theorem B3411113 : Blo 2273435 3411113 := bstep (se 2 (by rfl) ⟨1279167, by rfl⟩ : syracuseStep 3411113 = 2558335) B2558335
theorem B2274075 : Blo 2273435 2274075 := bstep (se 1 (by rfl) ⟨1705556, by rfl⟩ : syracuseStep 2274075 = 3411113) B3411113
theorem B3642637 : Blo 2273435 3642637 := bbase (se 3 (by rfl) ⟨682994, by rfl⟩ : syracuseStep 3642637 = 1365989) (by norm_num)
theorem B4856849 : Blo 2273435 4856849 := bstep (se 2 (by rfl) ⟨1821318, by rfl⟩ : syracuseStep 4856849 = 3642637) B3642637
theorem B3237899 : Blo 2273435 3237899 := bstep (se 1 (by rfl) ⟨2428424, by rfl⟩ : syracuseStep 3237899 = 4856849) B4856849
theorem B8634397 : Blo 2273435 8634397 := bstep (se 3 (by rfl) ⟨1618949, by rfl⟩ : syracuseStep 8634397 = 3237899) B3237899
theorem B11512529 : Blo 2273435 11512529 := bstep (se 2 (by rfl) ⟨4317198, by rfl⟩ : syracuseStep 11512529 = 8634397) B8634397
theorem B7675019 : Blo 2273435 7675019 := bstep (se 1 (by rfl) ⟨5756264, by rfl⟩ : syracuseStep 7675019 = 11512529) B11512529
theorem B5116679 : Blo 2273435 5116679 := bstep (se 1 (by rfl) ⟨3837509, by rfl⟩ : syracuseStep 5116679 = 7675019) B7675019
theorem B3411119 : Blo 2273435 3411119 := bstep (se 1 (by rfl) ⟨2558339, by rfl⟩ : syracuseStep 3411119 = 5116679) B5116679
theorem B2274079 : Blo 2273435 2274079 := bstep (se 1 (by rfl) ⟨1705559, by rfl⟩ : syracuseStep 2274079 = 3411119) B3411119
theorem B3411125 : Blo 2273435 3411125 := bbase (se 5 (by rfl) ⟨159896, by rfl⟩ : syracuseStep 3411125 = 319793) (by norm_num)
theorem B2274083 : Blo 2273435 2274083 := bstep (se 1 (by rfl) ⟨1705562, by rfl⟩ : syracuseStep 2274083 = 3411125) B3411125
theorem B5756285 : Blo 2273435 5756285 := bbase (se 3 (by rfl) ⟨1079303, by rfl⟩ : syracuseStep 5756285 = 2158607) (by norm_num)
theorem B3837523 : Blo 2273435 3837523 := bstep (se 1 (by rfl) ⟨2878142, by rfl⟩ : syracuseStep 3837523 = 5756285) B5756285
theorem B5116697 : Blo 2273435 5116697 := bstep (se 2 (by rfl) ⟨1918761, by rfl⟩ : syracuseStep 5116697 = 3837523) B3837523
theorem B3411131 : Blo 2273435 3411131 := bstep (se 1 (by rfl) ⟨2558348, by rfl⟩ : syracuseStep 3411131 = 5116697) B5116697
theorem B2274087 : Blo 2273435 2274087 := bstep (se 1 (by rfl) ⟨1705565, by rfl⟩ : syracuseStep 2274087 = 3411131) B3411131
theorem B2558353 : Blo 2273435 2558353 := bbase (se 2 (by rfl) ⟨959382, by rfl⟩ : syracuseStep 2558353 = 1918765) (by norm_num)
theorem B3411137 : Blo 2273435 3411137 := bstep (se 2 (by rfl) ⟨1279176, by rfl⟩ : syracuseStep 3411137 = 2558353) B2558353
theorem B2274091 : Blo 2273435 2274091 := bstep (se 1 (by rfl) ⟨1705568, by rfl⟩ : syracuseStep 2274091 = 3411137) B3411137
theorem B4317229 : Blo 2273435 4317229 := bbase (se 3 (by rfl) ⟨809480, by rfl⟩ : syracuseStep 4317229 = 1618961) (by norm_num)
theorem B5756305 : Blo 2273435 5756305 := bstep (se 2 (by rfl) ⟨2158614, by rfl⟩ : syracuseStep 5756305 = 4317229) B4317229
theorem B7675073 : Blo 2273435 7675073 := bstep (se 2 (by rfl) ⟨2878152, by rfl⟩ : syracuseStep 7675073 = 5756305) B5756305
theorem B5116715 : Blo 2273435 5116715 := bstep (se 1 (by rfl) ⟨3837536, by rfl⟩ : syracuseStep 5116715 = 7675073) B7675073
theorem B3411143 : Blo 2273435 3411143 := bstep (se 1 (by rfl) ⟨2558357, by rfl⟩ : syracuseStep 3411143 = 5116715) B5116715
theorem B2274095 : Blo 2273435 2274095 := bstep (se 1 (by rfl) ⟨1705571, by rfl⟩ : syracuseStep 2274095 = 3411143) B3411143
theorem B3411149 : Blo 2273435 3411149 := bbase (se 3 (by rfl) ⟨639590, by rfl⟩ : syracuseStep 3411149 = 1279181) (by norm_num)
theorem B2274099 : Blo 2273435 2274099 := bstep (se 1 (by rfl) ⟨1705574, by rfl⟩ : syracuseStep 2274099 = 3411149) B3411149
theorem B5116733 : Blo 2273435 5116733 := bbase (se 3 (by rfl) ⟨959387, by rfl⟩ : syracuseStep 5116733 = 1918775) (by norm_num)
theorem B3411155 : Blo 2273435 3411155 := bstep (se 1 (by rfl) ⟨2558366, by rfl⟩ : syracuseStep 3411155 = 5116733) B5116733
theorem B2274103 : Blo 2273435 2274103 := bstep (se 1 (by rfl) ⟨1705577, by rfl⟩ : syracuseStep 2274103 = 3411155) B3411155
theorem B3837557 : Blo 2273435 3837557 := bbase (se 5 (by rfl) ⟨179885, by rfl⟩ : syracuseStep 3837557 = 359771) (by norm_num)
theorem B2558371 : Blo 2273435 2558371 := bstep (se 1 (by rfl) ⟨1918778, by rfl⟩ : syracuseStep 2558371 = 3837557) B3837557
theorem B3411161 : Blo 2273435 3411161 := bstep (se 2 (by rfl) ⟨1279185, by rfl⟩ : syracuseStep 3411161 = 2558371) B2558371
theorem B2274107 : Blo 2273435 2274107 := bstep (se 1 (by rfl) ⟨1705580, by rfl⟩ : syracuseStep 2274107 = 3411161) B3411161
theorem B4856917 : Blo 2273435 4856917 := bbase (se 8 (by rfl) ⟨28458, by rfl⟩ : syracuseStep 4856917 = 56917) (by norm_num)
theorem B6475889 : Blo 2273435 6475889 := bstep (se 2 (by rfl) ⟨2428458, by rfl⟩ : syracuseStep 6475889 = 4856917) B4856917
theorem B17269037 : Blo 2273435 17269037 := bstep (se 3 (by rfl) ⟨3237944, by rfl⟩ : syracuseStep 17269037 = 6475889) B6475889
theorem B11512691 : Blo 2273435 11512691 := bstep (se 1 (by rfl) ⟨8634518, by rfl⟩ : syracuseStep 11512691 = 17269037) B17269037
theorem B7675127 : Blo 2273435 7675127 := bstep (se 1 (by rfl) ⟨5756345, by rfl⟩ : syracuseStep 7675127 = 11512691) B11512691
theorem B5116751 : Blo 2273435 5116751 := bstep (se 1 (by rfl) ⟨3837563, by rfl⟩ : syracuseStep 5116751 = 7675127) B7675127
theorem B3411167 : Blo 2273435 3411167 := bstep (se 1 (by rfl) ⟨2558375, by rfl⟩ : syracuseStep 3411167 = 5116751) B5116751
theorem B2274111 : Blo 2273435 2274111 := bstep (se 1 (by rfl) ⟨1705583, by rfl⟩ : syracuseStep 2274111 = 3411167) B3411167
theorem B3411173 : Blo 2273435 3411173 := bbase (se 4 (by rfl) ⟨319797, by rfl⟩ : syracuseStep 3411173 = 639595) (by norm_num)
theorem B2274115 : Blo 2273435 2274115 := bstep (se 1 (by rfl) ⟨1705586, by rfl⟩ : syracuseStep 2274115 = 3411173) B3411173
theorem B8752357 : Blo 2273435 8752357 := bbase (se 4 (by rfl) ⟨820533, by rfl⟩ : syracuseStep 8752357 = 1641067) (by norm_num)
theorem B46679237 : Blo 2273435 46679237 := bstep (se 4 (by rfl) ⟨4376178, by rfl⟩ : syracuseStep 46679237 = 8752357) B8752357
theorem B31119491 : Blo 2273435 31119491 := bstep (se 1 (by rfl) ⟨23339618, by rfl⟩ : syracuseStep 31119491 = 46679237) B46679237
theorem B20746327 : Blo 2273435 20746327 := bstep (se 1 (by rfl) ⟨15559745, by rfl⟩ : syracuseStep 20746327 = 31119491) B31119491
theorem B27661769 : Blo 2273435 27661769 := bstep (se 2 (by rfl) ⟨10373163, by rfl⟩ : syracuseStep 27661769 = 20746327) B20746327
theorem B18441179 : Blo 2273435 18441179 := bstep (se 1 (by rfl) ⟨13830884, by rfl⟩ : syracuseStep 18441179 = 27661769) B27661769
theorem B12294119 : Blo 2273435 12294119 := bstep (se 1 (by rfl) ⟨9220589, by rfl⟩ : syracuseStep 12294119 = 18441179) B18441179
theorem B8196079 : Blo 2273435 8196079 := bstep (se 1 (by rfl) ⟨6147059, by rfl⟩ : syracuseStep 8196079 = 12294119) B12294119
theorem B10928105 : Blo 2273435 10928105 := bstep (se 2 (by rfl) ⟨4098039, by rfl⟩ : syracuseStep 10928105 = 8196079) B8196079
theorem B7285403 : Blo 2273435 7285403 := bstep (se 1 (by rfl) ⟨5464052, by rfl⟩ : syracuseStep 7285403 = 10928105) B10928105
theorem B4856935 : Blo 2273435 4856935 := bstep (se 1 (by rfl) ⟨3642701, by rfl⟩ : syracuseStep 4856935 = 7285403) B7285403
theorem B6475913 : Blo 2273435 6475913 := bstep (se 2 (by rfl) ⟨2428467, by rfl⟩ : syracuseStep 6475913 = 4856935) B4856935
theorem B4317275 : Blo 2273435 4317275 := bstep (se 1 (by rfl) ⟨3237956, by rfl⟩ : syracuseStep 4317275 = 6475913) B6475913
theorem B2878183 : Blo 2273435 2878183 := bstep (se 1 (by rfl) ⟨2158637, by rfl⟩ : syracuseStep 2878183 = 4317275) B4317275
theorem B3837577 : Blo 2273435 3837577 := bstep (se 2 (by rfl) ⟨1439091, by rfl⟩ : syracuseStep 3837577 = 2878183) B2878183
theorem B5116769 : Blo 2273435 5116769 := bstep (se 2 (by rfl) ⟨1918788, by rfl⟩ : syracuseStep 5116769 = 3837577) B3837577
theorem B3411179 : Blo 2273435 3411179 := bstep (se 1 (by rfl) ⟨2558384, by rfl⟩ : syracuseStep 3411179 = 5116769) B5116769
theorem B2274119 : Blo 2273435 2274119 := bstep (se 1 (by rfl) ⟨1705589, by rfl⟩ : syracuseStep 2274119 = 3411179) B3411179
theorem B2558389 : Blo 2273435 2558389 := bbase (se 5 (by rfl) ⟨119924, by rfl⟩ : syracuseStep 2558389 = 239849) (by norm_num)
theorem B3411185 : Blo 2273435 3411185 := bstep (se 2 (by rfl) ⟨1279194, by rfl⟩ : syracuseStep 3411185 = 2558389) B2558389
theorem B2274123 : Blo 2273435 2274123 := bstep (se 1 (by rfl) ⟨1705592, by rfl⟩ : syracuseStep 2274123 = 3411185) B3411185
theorem B2878193 : Blo 2273435 2878193 := bbase (se 2 (by rfl) ⟨1079322, by rfl⟩ : syracuseStep 2878193 = 2158645) (by norm_num)
theorem B7675181 : Blo 2273435 7675181 := bstep (se 3 (by rfl) ⟨1439096, by rfl⟩ : syracuseStep 7675181 = 2878193) B2878193
theorem B5116787 : Blo 2273435 5116787 := bstep (se 1 (by rfl) ⟨3837590, by rfl⟩ : syracuseStep 5116787 = 7675181) B7675181
theorem B3411191 : Blo 2273435 3411191 := bstep (se 1 (by rfl) ⟨2558393, by rfl⟩ : syracuseStep 3411191 = 5116787) B5116787
theorem B2274127 : Blo 2273435 2274127 := bstep (se 1 (by rfl) ⟨1705595, by rfl⟩ : syracuseStep 2274127 = 3411191) B3411191
theorem B3411197 : Blo 2273435 3411197 := bbase (se 3 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 3411197 = 1279199) (by norm_num)
theorem B2274131 : Blo 2273435 2274131 := bstep (se 1 (by rfl) ⟨1705598, by rfl⟩ : syracuseStep 2274131 = 3411197) B3411197
theorem B5116805 : Blo 2273435 5116805 := bbase (se 4 (by rfl) ⟨479700, by rfl⟩ : syracuseStep 5116805 = 959401) (by norm_num)
theorem B3411203 : Blo 2273435 3411203 := bstep (se 1 (by rfl) ⟨2558402, by rfl⟩ : syracuseStep 3411203 = 5116805) B5116805
theorem B2274135 : Blo 2273435 2274135 := bstep (se 1 (by rfl) ⟨1705601, by rfl⟩ : syracuseStep 2274135 = 3411203) B3411203
theorem B2428489 : Blo 2273435 2428489 := bbase (se 2 (by rfl) ⟨910683, by rfl⟩ : syracuseStep 2428489 = 1821367) (by norm_num)
theorem B3237985 : Blo 2273435 3237985 := bstep (se 2 (by rfl) ⟨1214244, by rfl⟩ : syracuseStep 3237985 = 2428489) B2428489
theorem B4317313 : Blo 2273435 4317313 := bstep (se 2 (by rfl) ⟨1618992, by rfl⟩ : syracuseStep 4317313 = 3237985) B3237985
theorem B5756417 : Blo 2273435 5756417 := bstep (se 2 (by rfl) ⟨2158656, by rfl⟩ : syracuseStep 5756417 = 4317313) B4317313
theorem B3837611 : Blo 2273435 3837611 := bstep (se 1 (by rfl) ⟨2878208, by rfl⟩ : syracuseStep 3837611 = 5756417) B5756417
theorem B2558407 : Blo 2273435 2558407 := bstep (se 1 (by rfl) ⟨1918805, by rfl⟩ : syracuseStep 2558407 = 3837611) B3837611
theorem B3411209 : Blo 2273435 3411209 := bstep (se 2 (by rfl) ⟨1279203, by rfl⟩ : syracuseStep 3411209 = 2558407) B2558407
theorem B2274139 : Blo 2273435 2274139 := bstep (se 1 (by rfl) ⟨1705604, by rfl⟩ : syracuseStep 2274139 = 3411209) B3411209
theorem B11512853 : Blo 2273435 11512853 := bbase (se 6 (by rfl) ⟨269832, by rfl⟩ : syracuseStep 11512853 = 539665) (by norm_num)
theorem B7675235 : Blo 2273435 7675235 := bstep (se 1 (by rfl) ⟨5756426, by rfl⟩ : syracuseStep 7675235 = 11512853) B11512853
theorem B5116823 : Blo 2273435 5116823 := bstep (se 1 (by rfl) ⟨3837617, by rfl⟩ : syracuseStep 5116823 = 7675235) B7675235
theorem B3411215 : Blo 2273435 3411215 := bstep (se 1 (by rfl) ⟨2558411, by rfl⟩ : syracuseStep 3411215 = 5116823) B5116823
theorem B2274143 : Blo 2273435 2274143 := bstep (se 1 (by rfl) ⟨1705607, by rfl⟩ : syracuseStep 2274143 = 3411215) B3411215
theorem B3411221 : Blo 2273435 3411221 := bbase (se 6 (by rfl) ⟨79950, by rfl⟩ : syracuseStep 3411221 = 159901) (by norm_num)
theorem B2274147 : Blo 2273435 2274147 := bstep (se 1 (by rfl) ⟨1705610, by rfl⟩ : syracuseStep 2274147 = 3411221) B3411221
theorem B8308021 : Blo 2273435 8308021 := bbase (se 5 (by rfl) ⟨389438, by rfl⟩ : syracuseStep 8308021 = 778877) (by norm_num)
theorem B11077361 : Blo 2273435 11077361 := bstep (se 2 (by rfl) ⟨4154010, by rfl⟩ : syracuseStep 11077361 = 8308021) B8308021
theorem B7384907 : Blo 2273435 7384907 := bstep (se 1 (by rfl) ⟨5538680, by rfl⟩ : syracuseStep 7384907 = 11077361) B11077361
theorem B4923271 : Blo 2273435 4923271 := bstep (se 1 (by rfl) ⟨3692453, by rfl⟩ : syracuseStep 4923271 = 7384907) B7384907
theorem B6564361 : Blo 2273435 6564361 := bstep (se 2 (by rfl) ⟨2461635, by rfl⟩ : syracuseStep 6564361 = 4923271) B4923271
theorem B8752481 : Blo 2273435 8752481 := bstep (se 2 (by rfl) ⟨3282180, by rfl⟩ : syracuseStep 8752481 = 6564361) B6564361
theorem B5834987 : Blo 2273435 5834987 := bstep (se 1 (by rfl) ⟨4376240, by rfl⟩ : syracuseStep 5834987 = 8752481) B8752481
theorem B3889991 : Blo 2273435 3889991 := bstep (se 1 (by rfl) ⟨2917493, by rfl⟩ : syracuseStep 3889991 = 5834987) B5834987
theorem B2593327 : Blo 2273435 2593327 := bstep (se 1 (by rfl) ⟨1944995, by rfl⟩ : syracuseStep 2593327 = 3889991) B3889991
theorem B3457769 : Blo 2273435 3457769 := bstep (se 2 (by rfl) ⟨1296663, by rfl⟩ : syracuseStep 3457769 = 2593327) B2593327
theorem B9220717 : Blo 2273435 9220717 := bstep (se 3 (by rfl) ⟨1728884, by rfl⟩ : syracuseStep 9220717 = 3457769) B3457769
theorem B12294289 : Blo 2273435 12294289 := bstep (se 2 (by rfl) ⟨4610358, by rfl⟩ : syracuseStep 12294289 = 9220717) B9220717
theorem B16392385 : Blo 2273435 16392385 := bstep (se 2 (by rfl) ⟨6147144, by rfl⟩ : syracuseStep 16392385 = 12294289) B12294289
theorem B21856513 : Blo 2273435 21856513 := bstep (se 2 (by rfl) ⟨8196192, by rfl⟩ : syracuseStep 21856513 = 16392385) B16392385
theorem B29142017 : Blo 2273435 29142017 := bstep (se 2 (by rfl) ⟨10928256, by rfl⟩ : syracuseStep 29142017 = 21856513) B21856513
theorem B19428011 : Blo 2273435 19428011 := bstep (se 1 (by rfl) ⟨14571008, by rfl⟩ : syracuseStep 19428011 = 29142017) B29142017
theorem B12952007 : Blo 2273435 12952007 := bstep (se 1 (by rfl) ⟨9714005, by rfl⟩ : syracuseStep 12952007 = 19428011) B19428011
theorem B8634671 : Blo 2273435 8634671 := bstep (se 1 (by rfl) ⟨6476003, by rfl⟩ : syracuseStep 8634671 = 12952007) B12952007
theorem B5756447 : Blo 2273435 5756447 := bstep (se 1 (by rfl) ⟨4317335, by rfl⟩ : syracuseStep 5756447 = 8634671) B8634671
theorem B3837631 : Blo 2273435 3837631 := bstep (se 1 (by rfl) ⟨2878223, by rfl⟩ : syracuseStep 3837631 = 5756447) B5756447
theorem B5116841 : Blo 2273435 5116841 := bstep (se 2 (by rfl) ⟨1918815, by rfl⟩ : syracuseStep 5116841 = 3837631) B3837631
theorem B3411227 : Blo 2273435 3411227 := bstep (se 1 (by rfl) ⟨2558420, by rfl⟩ : syracuseStep 3411227 = 5116841) B5116841
theorem B2274151 : Blo 2273435 2274151 := bstep (se 1 (by rfl) ⟨1705613, by rfl⟩ : syracuseStep 2274151 = 3411227) B3411227
theorem B2558425 : Blo 2273435 2558425 := bbase (se 2 (by rfl) ⟨959409, by rfl⟩ : syracuseStep 2558425 = 1918819) (by norm_num)
theorem B3411233 : Blo 2273435 3411233 := bstep (se 2 (by rfl) ⟨1279212, by rfl⟩ : syracuseStep 3411233 = 2558425) B2558425
theorem B2274155 : Blo 2273435 2274155 := bstep (se 1 (by rfl) ⟨1705616, by rfl⟩ : syracuseStep 2274155 = 3411233) B3411233
theorem B3238013 : Blo 2273435 3238013 := bbase (se 3 (by rfl) ⟨607127, by rfl⟩ : syracuseStep 3238013 = 1214255) (by norm_num)
theorem B8634701 : Blo 2273435 8634701 := bstep (se 3 (by rfl) ⟨1619006, by rfl⟩ : syracuseStep 8634701 = 3238013) B3238013
theorem B5756467 : Blo 2273435 5756467 := bstep (se 1 (by rfl) ⟨4317350, by rfl⟩ : syracuseStep 5756467 = 8634701) B8634701
theorem B7675289 : Blo 2273435 7675289 := bstep (se 2 (by rfl) ⟨2878233, by rfl⟩ : syracuseStep 7675289 = 5756467) B5756467
theorem B5116859 : Blo 2273435 5116859 := bstep (se 1 (by rfl) ⟨3837644, by rfl⟩ : syracuseStep 5116859 = 7675289) B7675289
theorem B3411239 : Blo 2273435 3411239 := bstep (se 1 (by rfl) ⟨2558429, by rfl⟩ : syracuseStep 3411239 = 5116859) B5116859
theorem B2274159 : Blo 2273435 2274159 := bstep (se 1 (by rfl) ⟨1705619, by rfl⟩ : syracuseStep 2274159 = 3411239) B3411239
theorem B3411245 : Blo 2273435 3411245 := bbase (se 3 (by rfl) ⟨639608, by rfl⟩ : syracuseStep 3411245 = 1279217) (by norm_num)
theorem B2274163 : Blo 2273435 2274163 := bstep (se 1 (by rfl) ⟨1705622, by rfl⟩ : syracuseStep 2274163 = 3411245) B3411245
theorem B5116877 : Blo 2273435 5116877 := bbase (se 3 (by rfl) ⟨959414, by rfl⟩ : syracuseStep 5116877 = 1918829) (by norm_num)
theorem B3411251 : Blo 2273435 3411251 := bstep (se 1 (by rfl) ⟨2558438, by rfl⟩ : syracuseStep 3411251 = 5116877) B5116877
theorem B2274167 : Blo 2273435 2274167 := bstep (se 1 (by rfl) ⟨1705625, by rfl⟩ : syracuseStep 2274167 = 3411251) B3411251
theorem B2878249 : Blo 2273435 2878249 := bbase (se 2 (by rfl) ⟨1079343, by rfl⟩ : syracuseStep 2878249 = 2158687) (by norm_num)
theorem B3837665 : Blo 2273435 3837665 := bstep (se 2 (by rfl) ⟨1439124, by rfl⟩ : syracuseStep 3837665 = 2878249) B2878249
theorem B2558443 : Blo 2273435 2558443 := bstep (se 1 (by rfl) ⟨1918832, by rfl⟩ : syracuseStep 2558443 = 3837665) B3837665
theorem B3411257 : Blo 2273435 3411257 := bstep (se 2 (by rfl) ⟨1279221, by rfl⟩ : syracuseStep 3411257 = 2558443) B2558443
theorem B2274171 : Blo 2273435 2274171 := bstep (se 1 (by rfl) ⟨1705628, by rfl⟩ : syracuseStep 2274171 = 3411257) B3411257
theorem B4154053 : Blo 2273435 4154053 := bbase (se 4 (by rfl) ⟨389442, by rfl⟩ : syracuseStep 4154053 = 778885) (by norm_num)
theorem B5538737 : Blo 2273435 5538737 := bstep (se 2 (by rfl) ⟨2077026, by rfl⟩ : syracuseStep 5538737 = 4154053) B4154053
theorem B14769965 : Blo 2273435 14769965 := bstep (se 3 (by rfl) ⟨2769368, by rfl⟩ : syracuseStep 14769965 = 5538737) B5538737
theorem B39386573 : Blo 2273435 39386573 := bstep (se 3 (by rfl) ⟨7384982, by rfl⟩ : syracuseStep 39386573 = 14769965) B14769965
theorem B26257715 : Blo 2273435 26257715 := bstep (se 1 (by rfl) ⟨19693286, by rfl⟩ : syracuseStep 26257715 = 39386573) B39386573
theorem B17505143 : Blo 2273435 17505143 := bstep (se 1 (by rfl) ⟨13128857, by rfl⟩ : syracuseStep 17505143 = 26257715) B26257715
theorem B11670095 : Blo 2273435 11670095 := bstep (se 1 (by rfl) ⟨8752571, by rfl⟩ : syracuseStep 11670095 = 17505143) B17505143
theorem B7780063 : Blo 2273435 7780063 := bstep (se 1 (by rfl) ⟨5835047, by rfl⟩ : syracuseStep 7780063 = 11670095) B11670095
theorem B10373417 : Blo 2273435 10373417 := bstep (se 2 (by rfl) ⟨3890031, by rfl⟩ : syracuseStep 10373417 = 7780063) B7780063
theorem B6915611 : Blo 2273435 6915611 := bstep (se 1 (by rfl) ⟨5186708, by rfl⟩ : syracuseStep 6915611 = 10373417) B10373417
theorem B4610407 : Blo 2273435 4610407 := bstep (se 1 (by rfl) ⟨3457805, by rfl⟩ : syracuseStep 4610407 = 6915611) B6915611
theorem B6147209 : Blo 2273435 6147209 := bstep (se 2 (by rfl) ⟨2305203, by rfl⟩ : syracuseStep 6147209 = 4610407) B4610407
theorem B16392557 : Blo 2273435 16392557 := bstep (se 3 (by rfl) ⟨3073604, by rfl⟩ : syracuseStep 16392557 = 6147209) B6147209
theorem B10928371 : Blo 2273435 10928371 := bstep (se 1 (by rfl) ⟨8196278, by rfl⟩ : syracuseStep 10928371 = 16392557) B16392557
theorem B14571161 : Blo 2273435 14571161 := bstep (se 2 (by rfl) ⟨5464185, by rfl⟩ : syracuseStep 14571161 = 10928371) B10928371
theorem B9714107 : Blo 2273435 9714107 := bstep (se 1 (by rfl) ⟨7285580, by rfl⟩ : syracuseStep 9714107 = 14571161) B14571161
theorem B25904285 : Blo 2273435 25904285 := bstep (se 3 (by rfl) ⟨4857053, by rfl⟩ : syracuseStep 25904285 = 9714107) B9714107
theorem B17269523 : Blo 2273435 17269523 := bstep (se 1 (by rfl) ⟨12952142, by rfl⟩ : syracuseStep 17269523 = 25904285) B25904285
theorem B11513015 : Blo 2273435 11513015 := bstep (se 1 (by rfl) ⟨8634761, by rfl⟩ : syracuseStep 11513015 = 17269523) B17269523
theorem B7675343 : Blo 2273435 7675343 := bstep (se 1 (by rfl) ⟨5756507, by rfl⟩ : syracuseStep 7675343 = 11513015) B11513015
theorem B5116895 : Blo 2273435 5116895 := bstep (se 1 (by rfl) ⟨3837671, by rfl⟩ : syracuseStep 5116895 = 7675343) B7675343
theorem B3411263 : Blo 2273435 3411263 := bstep (se 1 (by rfl) ⟨2558447, by rfl⟩ : syracuseStep 3411263 = 5116895) B5116895
theorem B2274175 : Blo 2273435 2274175 := bstep (se 1 (by rfl) ⟨1705631, by rfl⟩ : syracuseStep 2274175 = 3411263) B3411263
theorem B3411269 : Blo 2273435 3411269 := bbase (se 4 (by rfl) ⟨319806, by rfl⟩ : syracuseStep 3411269 = 639613) (by norm_num)
theorem B2274179 : Blo 2273435 2274179 := bstep (se 1 (by rfl) ⟨1705634, by rfl⟩ : syracuseStep 2274179 = 3411269) B3411269
theorem B3837685 : Blo 2273435 3837685 := bbase (se 5 (by rfl) ⟨179891, by rfl⟩ : syracuseStep 3837685 = 359783) (by norm_num)
theorem B5116913 : Blo 2273435 5116913 := bstep (se 2 (by rfl) ⟨1918842, by rfl⟩ : syracuseStep 5116913 = 3837685) B3837685
theorem B3411275 : Blo 2273435 3411275 := bstep (se 1 (by rfl) ⟨2558456, by rfl⟩ : syracuseStep 3411275 = 5116913) B5116913
theorem B2274183 : Blo 2273435 2274183 := bstep (se 1 (by rfl) ⟨1705637, by rfl⟩ : syracuseStep 2274183 = 3411275) B3411275
theorem B2558461 : Blo 2273435 2558461 := bbase (se 3 (by rfl) ⟨479711, by rfl⟩ : syracuseStep 2558461 = 959423) (by norm_num)
theorem B3411281 : Blo 2273435 3411281 := bstep (se 2 (by rfl) ⟨1279230, by rfl⟩ : syracuseStep 3411281 = 2558461) B2558461
theorem B2274187 : Blo 2273435 2274187 := bstep (se 1 (by rfl) ⟨1705640, by rfl⟩ : syracuseStep 2274187 = 3411281) B3411281
theorem B7675397 : Blo 2273435 7675397 := bbase (se 4 (by rfl) ⟨719568, by rfl⟩ : syracuseStep 7675397 = 1439137) (by norm_num)
theorem B5116931 : Blo 2273435 5116931 := bstep (se 1 (by rfl) ⟨3837698, by rfl⟩ : syracuseStep 5116931 = 7675397) B7675397
theorem B3411287 : Blo 2273435 3411287 := bstep (se 1 (by rfl) ⟨2558465, by rfl⟩ : syracuseStep 3411287 = 5116931) B5116931
theorem B2274191 : Blo 2273435 2274191 := bstep (se 1 (by rfl) ⟨1705643, by rfl⟩ : syracuseStep 2274191 = 3411287) B3411287
theorem B3411293 : Blo 2273435 3411293 := bbase (se 3 (by rfl) ⟨639617, by rfl⟩ : syracuseStep 3411293 = 1279235) (by norm_num)
theorem B2274195 : Blo 2273435 2274195 := bstep (se 1 (by rfl) ⟨1705646, by rfl⟩ : syracuseStep 2274195 = 3411293) B3411293
theorem B5116949 : Blo 2273435 5116949 := bbase (se 6 (by rfl) ⟨119928, by rfl⟩ : syracuseStep 5116949 = 239857) (by norm_num)
theorem B3411299 : Blo 2273435 3411299 := bstep (se 1 (by rfl) ⟨2558474, by rfl⟩ : syracuseStep 3411299 = 5116949) B5116949
theorem B2274199 : Blo 2273435 2274199 := bstep (se 1 (by rfl) ⟨1705649, by rfl⟩ : syracuseStep 2274199 = 3411299) B3411299
theorem B8634869 : Blo 2273435 8634869 := bbase (se 5 (by rfl) ⟨404759, by rfl⟩ : syracuseStep 8634869 = 809519) (by norm_num)
theorem B5756579 : Blo 2273435 5756579 := bstep (se 1 (by rfl) ⟨4317434, by rfl⟩ : syracuseStep 5756579 = 8634869) B8634869
theorem B3837719 : Blo 2273435 3837719 := bstep (se 1 (by rfl) ⟨2878289, by rfl⟩ : syracuseStep 3837719 = 5756579) B5756579
theorem B2558479 : Blo 2273435 2558479 := bstep (se 1 (by rfl) ⟨1918859, by rfl⟩ : syracuseStep 2558479 = 3837719) B3837719
theorem B3411305 : Blo 2273435 3411305 := bstep (se 2 (by rfl) ⟨1279239, by rfl⟩ : syracuseStep 3411305 = 2558479) B2558479
theorem B2274203 : Blo 2273435 2274203 := bstep (se 1 (by rfl) ⟨1705652, by rfl⟩ : syracuseStep 2274203 = 3411305) B3411305
theorem B2428561 : Blo 2273435 2428561 := bbase (se 2 (by rfl) ⟨910710, by rfl⟩ : syracuseStep 2428561 = 1821421) (by norm_num)
theorem B12952325 : Blo 2273435 12952325 := bstep (se 4 (by rfl) ⟨1214280, by rfl⟩ : syracuseStep 12952325 = 2428561) B2428561
theorem B8634883 : Blo 2273435 8634883 := bstep (se 1 (by rfl) ⟨6476162, by rfl⟩ : syracuseStep 8634883 = 12952325) B12952325
theorem B11513177 : Blo 2273435 11513177 := bstep (se 2 (by rfl) ⟨4317441, by rfl⟩ : syracuseStep 11513177 = 8634883) B8634883
theorem B7675451 : Blo 2273435 7675451 := bstep (se 1 (by rfl) ⟨5756588, by rfl⟩ : syracuseStep 7675451 = 11513177) B11513177
theorem B5116967 : Blo 2273435 5116967 := bstep (se 1 (by rfl) ⟨3837725, by rfl⟩ : syracuseStep 5116967 = 7675451) B7675451
theorem B3411311 : Blo 2273435 3411311 := bstep (se 1 (by rfl) ⟨2558483, by rfl⟩ : syracuseStep 3411311 = 5116967) B5116967
theorem B2274207 : Blo 2273435 2274207 := bstep (se 1 (by rfl) ⟨1705655, by rfl⟩ : syracuseStep 2274207 = 3411311) B3411311
theorem B3411317 : Blo 2273435 3411317 := bbase (se 5 (by rfl) ⟨159905, by rfl⟩ : syracuseStep 3411317 = 319811) (by norm_num)
theorem B2274211 : Blo 2273435 2274211 := bstep (se 1 (by rfl) ⟨1705658, by rfl⟩ : syracuseStep 2274211 = 3411317) B3411317
theorem B3238093 : Blo 2273435 3238093 := bbase (se 3 (by rfl) ⟨607142, by rfl⟩ : syracuseStep 3238093 = 1214285) (by norm_num)
theorem B4317457 : Blo 2273435 4317457 := bstep (se 2 (by rfl) ⟨1619046, by rfl⟩ : syracuseStep 4317457 = 3238093) B3238093
theorem B5756609 : Blo 2273435 5756609 := bstep (se 2 (by rfl) ⟨2158728, by rfl⟩ : syracuseStep 5756609 = 4317457) B4317457
theorem B3837739 : Blo 2273435 3837739 := bstep (se 1 (by rfl) ⟨2878304, by rfl⟩ : syracuseStep 3837739 = 5756609) B5756609
theorem B5116985 : Blo 2273435 5116985 := bstep (se 2 (by rfl) ⟨1918869, by rfl⟩ : syracuseStep 5116985 = 3837739) B3837739
theorem B3411323 : Blo 2273435 3411323 := bstep (se 1 (by rfl) ⟨2558492, by rfl⟩ : syracuseStep 3411323 = 5116985) B5116985
theorem B2274215 : Blo 2273435 2274215 := bstep (se 1 (by rfl) ⟨1705661, by rfl⟩ : syracuseStep 2274215 = 3411323) B3411323
theorem B2558497 : Blo 2273435 2558497 := bbase (se 2 (by rfl) ⟨959436, by rfl⟩ : syracuseStep 2558497 = 1918873) (by norm_num)
theorem B3411329 : Blo 2273435 3411329 := bstep (se 2 (by rfl) ⟨1279248, by rfl⟩ : syracuseStep 3411329 = 2558497) B2558497
theorem B2274219 : Blo 2273435 2274219 := bstep (se 1 (by rfl) ⟨1705664, by rfl⟩ : syracuseStep 2274219 = 3411329) B3411329
theorem B5756629 : Blo 2273435 5756629 := bbase (se 7 (by rfl) ⟨67460, by rfl⟩ : syracuseStep 5756629 = 134921) (by norm_num)
theorem B7675505 : Blo 2273435 7675505 := bstep (se 2 (by rfl) ⟨2878314, by rfl⟩ : syracuseStep 7675505 = 5756629) B5756629
theorem B5117003 : Blo 2273435 5117003 := bstep (se 1 (by rfl) ⟨3837752, by rfl⟩ : syracuseStep 5117003 = 7675505) B7675505
theorem B3411335 : Blo 2273435 3411335 := bstep (se 1 (by rfl) ⟨2558501, by rfl⟩ : syracuseStep 3411335 = 5117003) B5117003
theorem B2274223 : Blo 2273435 2274223 := bstep (se 1 (by rfl) ⟨1705667, by rfl⟩ : syracuseStep 2274223 = 3411335) B3411335
theorem B3411341 : Blo 2273435 3411341 := bbase (se 3 (by rfl) ⟨639626, by rfl⟩ : syracuseStep 3411341 = 1279253) (by norm_num)
theorem B2274227 : Blo 2273435 2274227 := bstep (se 1 (by rfl) ⟨1705670, by rfl⟩ : syracuseStep 2274227 = 3411341) B3411341
theorem B5117021 : Blo 2273435 5117021 := bbase (se 3 (by rfl) ⟨959441, by rfl⟩ : syracuseStep 5117021 = 1918883) (by norm_num)
theorem B3411347 : Blo 2273435 3411347 := bstep (se 1 (by rfl) ⟨2558510, by rfl⟩ : syracuseStep 3411347 = 5117021) B5117021
theorem B2274231 : Blo 2273435 2274231 := bstep (se 1 (by rfl) ⟨1705673, by rfl⟩ : syracuseStep 2274231 = 3411347) B3411347
theorem B3837773 : Blo 2273435 3837773 := bbase (se 3 (by rfl) ⟨719582, by rfl⟩ : syracuseStep 3837773 = 1439165) (by norm_num)
theorem B2558515 : Blo 2273435 2558515 := bstep (se 1 (by rfl) ⟨1918886, by rfl⟩ : syracuseStep 2558515 = 3837773) B3837773
theorem B3411353 : Blo 2273435 3411353 := bstep (se 2 (by rfl) ⟨1279257, by rfl⟩ : syracuseStep 3411353 = 2558515) B2558515
theorem B2274235 : Blo 2273435 2274235 := bstep (se 1 (by rfl) ⟨1705676, by rfl⟩ : syracuseStep 2274235 = 3411353) B3411353
theorem B4923461 : Blo 2273435 4923461 := bbase (se 4 (by rfl) ⟨461574, by rfl⟩ : syracuseStep 4923461 = 923149) (by norm_num)
theorem B13129229 : Blo 2273435 13129229 := bstep (se 3 (by rfl) ⟨2461730, by rfl⟩ : syracuseStep 13129229 = 4923461) B4923461
theorem B8752819 : Blo 2273435 8752819 := bstep (se 1 (by rfl) ⟨6564614, by rfl⟩ : syracuseStep 8752819 = 13129229) B13129229
theorem B11670425 : Blo 2273435 11670425 := bstep (se 2 (by rfl) ⟨4376409, by rfl⟩ : syracuseStep 11670425 = 8752819) B8752819
theorem B7780283 : Blo 2273435 7780283 := bstep (se 1 (by rfl) ⟨5835212, by rfl⟩ : syracuseStep 7780283 = 11670425) B11670425
theorem B5186855 : Blo 2273435 5186855 := bstep (se 1 (by rfl) ⟨3890141, by rfl⟩ : syracuseStep 5186855 = 7780283) B7780283
theorem B3457903 : Blo 2273435 3457903 := bstep (se 1 (by rfl) ⟨2593427, by rfl⟩ : syracuseStep 3457903 = 5186855) B5186855
theorem B4610537 : Blo 2273435 4610537 := bstep (se 2 (by rfl) ⟨1728951, by rfl⟩ : syracuseStep 4610537 = 3457903) B3457903
theorem B3073691 : Blo 2273435 3073691 := bstep (se 1 (by rfl) ⟨2305268, by rfl⟩ : syracuseStep 3073691 = 4610537) B4610537
theorem B8196509 : Blo 2273435 8196509 := bstep (se 3 (by rfl) ⟨1536845, by rfl⟩ : syracuseStep 8196509 = 3073691) B3073691
theorem B21857357 : Blo 2273435 21857357 := bstep (se 3 (by rfl) ⟨4098254, by rfl⟩ : syracuseStep 21857357 = 8196509) B8196509
theorem B14571571 : Blo 2273435 14571571 := bstep (se 1 (by rfl) ⟨10928678, by rfl⟩ : syracuseStep 14571571 = 21857357) B21857357
theorem B19428761 : Blo 2273435 19428761 := bstep (se 2 (by rfl) ⟨7285785, by rfl⟩ : syracuseStep 19428761 = 14571571) B14571571
theorem B12952507 : Blo 2273435 12952507 := bstep (se 1 (by rfl) ⟨9714380, by rfl⟩ : syracuseStep 12952507 = 19428761) B19428761
theorem B17270009 : Blo 2273435 17270009 := bstep (se 2 (by rfl) ⟨6476253, by rfl⟩ : syracuseStep 17270009 = 12952507) B12952507
theorem B11513339 : Blo 2273435 11513339 := bstep (se 1 (by rfl) ⟨8635004, by rfl⟩ : syracuseStep 11513339 = 17270009) B17270009
theorem B7675559 : Blo 2273435 7675559 := bstep (se 1 (by rfl) ⟨5756669, by rfl⟩ : syracuseStep 7675559 = 11513339) B11513339
theorem B5117039 : Blo 2273435 5117039 := bstep (se 1 (by rfl) ⟨3837779, by rfl⟩ : syracuseStep 5117039 = 7675559) B7675559
theorem B3411359 : Blo 2273435 3411359 := bstep (se 1 (by rfl) ⟨2558519, by rfl⟩ : syracuseStep 3411359 = 5117039) B5117039
theorem B2274239 : Blo 2273435 2274239 := bstep (se 1 (by rfl) ⟨1705679, by rfl⟩ : syracuseStep 2274239 = 3411359) B3411359
theorem B3411365 : Blo 2273435 3411365 := bbase (se 4 (by rfl) ⟨319815, by rfl⟩ : syracuseStep 3411365 = 639631) (by norm_num)
theorem B2274243 : Blo 2273435 2274243 := bstep (se 1 (by rfl) ⟨1705682, by rfl⟩ : syracuseStep 2274243 = 3411365) B3411365
theorem B2878345 : Blo 2273435 2878345 := bbase (se 2 (by rfl) ⟨1079379, by rfl⟩ : syracuseStep 2878345 = 2158759) (by norm_num)
theorem B3837793 : Blo 2273435 3837793 := bstep (se 2 (by rfl) ⟨1439172, by rfl⟩ : syracuseStep 3837793 = 2878345) B2878345
theorem B5117057 : Blo 2273435 5117057 := bstep (se 2 (by rfl) ⟨1918896, by rfl⟩ : syracuseStep 5117057 = 3837793) B3837793
theorem B3411371 : Blo 2273435 3411371 := bstep (se 1 (by rfl) ⟨2558528, by rfl⟩ : syracuseStep 3411371 = 5117057) B5117057
theorem B2274247 : Blo 2273435 2274247 := bstep (se 1 (by rfl) ⟨1705685, by rfl⟩ : syracuseStep 2274247 = 3411371) B3411371
theorem B2558533 : Blo 2273435 2558533 := bbase (se 4 (by rfl) ⟨239862, by rfl⟩ : syracuseStep 2558533 = 479725) (by norm_num)
theorem B3411377 : Blo 2273435 3411377 := bstep (se 2 (by rfl) ⟨1279266, by rfl⟩ : syracuseStep 3411377 = 2558533) B2558533
theorem B2274251 : Blo 2273435 2274251 := bstep (se 1 (by rfl) ⟨1705688, by rfl⟩ : syracuseStep 2274251 = 3411377) B3411377
theorem B4317533 : Blo 2273435 4317533 := bbase (se 3 (by rfl) ⟨809537, by rfl⟩ : syracuseStep 4317533 = 1619075) (by norm_num)
theorem B2878355 : Blo 2273435 2878355 := bstep (se 1 (by rfl) ⟨2158766, by rfl⟩ : syracuseStep 2878355 = 4317533) B4317533
theorem B7675613 : Blo 2273435 7675613 := bstep (se 3 (by rfl) ⟨1439177, by rfl⟩ : syracuseStep 7675613 = 2878355) B2878355
theorem B5117075 : Blo 2273435 5117075 := bstep (se 1 (by rfl) ⟨3837806, by rfl⟩ : syracuseStep 5117075 = 7675613) B7675613
theorem B3411383 : Blo 2273435 3411383 := bstep (se 1 (by rfl) ⟨2558537, by rfl⟩ : syracuseStep 3411383 = 5117075) B5117075
theorem B2274255 : Blo 2273435 2274255 := bstep (se 1 (by rfl) ⟨1705691, by rfl⟩ : syracuseStep 2274255 = 3411383) B3411383
theorem B3411389 : Blo 2273435 3411389 := bbase (se 3 (by rfl) ⟨639635, by rfl⟩ : syracuseStep 3411389 = 1279271) (by norm_num)
theorem B2274259 : Blo 2273435 2274259 := bstep (se 1 (by rfl) ⟨1705694, by rfl⟩ : syracuseStep 2274259 = 3411389) B3411389
theorem B5117093 : Blo 2273435 5117093 := bbase (se 4 (by rfl) ⟨479727, by rfl⟩ : syracuseStep 5117093 = 959455) (by norm_num)
theorem B3411395 : Blo 2273435 3411395 := bstep (se 1 (by rfl) ⟨2558546, by rfl⟩ : syracuseStep 3411395 = 5117093) B5117093
theorem B2274263 : Blo 2273435 2274263 := bstep (se 1 (by rfl) ⟨1705697, by rfl⟩ : syracuseStep 2274263 = 3411395) B3411395
theorem B5756741 : Blo 2273435 5756741 := bbase (se 4 (by rfl) ⟨539694, by rfl⟩ : syracuseStep 5756741 = 1079389) (by norm_num)
theorem B3837827 : Blo 2273435 3837827 := bstep (se 1 (by rfl) ⟨2878370, by rfl⟩ : syracuseStep 3837827 = 5756741) B5756741
theorem B2558551 : Blo 2273435 2558551 := bstep (se 1 (by rfl) ⟨1918913, by rfl⟩ : syracuseStep 2558551 = 3837827) B3837827
theorem B3411401 : Blo 2273435 3411401 := bstep (se 2 (by rfl) ⟨1279275, by rfl⟩ : syracuseStep 3411401 = 2558551) B2558551
theorem B2274267 : Blo 2273435 2274267 := bstep (se 1 (by rfl) ⟨1705700, by rfl⟩ : syracuseStep 2274267 = 3411401) B3411401
theorem B3890197 : Blo 2273435 3890197 := bbase (se 6 (by rfl) ⟨91176, by rfl⟩ : syracuseStep 3890197 = 182353) (by norm_num)
theorem B5186929 : Blo 2273435 5186929 := bstep (se 2 (by rfl) ⟨1945098, by rfl⟩ : syracuseStep 5186929 = 3890197) B3890197
theorem B6915905 : Blo 2273435 6915905 := bstep (se 2 (by rfl) ⟨2593464, by rfl⟩ : syracuseStep 6915905 = 5186929) B5186929
theorem B4610603 : Blo 2273435 4610603 := bstep (se 1 (by rfl) ⟨3457952, by rfl⟩ : syracuseStep 4610603 = 6915905) B6915905
theorem B3073735 : Blo 2273435 3073735 := bstep (se 1 (by rfl) ⟨2305301, by rfl⟩ : syracuseStep 3073735 = 4610603) B4610603
theorem B4098313 : Blo 2273435 4098313 := bstep (se 2 (by rfl) ⟨1536867, by rfl⟩ : syracuseStep 4098313 = 3073735) B3073735
theorem B5464417 : Blo 2273435 5464417 := bstep (se 2 (by rfl) ⟨2049156, by rfl⟩ : syracuseStep 5464417 = 4098313) B4098313
theorem B7285889 : Blo 2273435 7285889 := bstep (se 2 (by rfl) ⟨2732208, by rfl⟩ : syracuseStep 7285889 = 5464417) B5464417
theorem B4857259 : Blo 2273435 4857259 := bstep (se 1 (by rfl) ⟨3642944, by rfl⟩ : syracuseStep 4857259 = 7285889) B7285889
theorem B6476345 : Blo 2273435 6476345 := bstep (se 2 (by rfl) ⟨2428629, by rfl⟩ : syracuseStep 6476345 = 4857259) B4857259
theorem B4317563 : Blo 2273435 4317563 := bstep (se 1 (by rfl) ⟨3238172, by rfl⟩ : syracuseStep 4317563 = 6476345) B6476345
theorem B11513501 : Blo 2273435 11513501 := bstep (se 3 (by rfl) ⟨2158781, by rfl⟩ : syracuseStep 11513501 = 4317563) B4317563
theorem B7675667 : Blo 2273435 7675667 := bstep (se 1 (by rfl) ⟨5756750, by rfl⟩ : syracuseStep 7675667 = 11513501) B11513501
theorem B5117111 : Blo 2273435 5117111 := bstep (se 1 (by rfl) ⟨3837833, by rfl⟩ : syracuseStep 5117111 = 7675667) B7675667
theorem B3411407 : Blo 2273435 3411407 := bstep (se 1 (by rfl) ⟨2558555, by rfl⟩ : syracuseStep 3411407 = 5117111) B5117111
theorem B2274271 : Blo 2273435 2274271 := bstep (se 1 (by rfl) ⟨1705703, by rfl⟩ : syracuseStep 2274271 = 3411407) B3411407
theorem B3411413 : Blo 2273435 3411413 := bbase (se 7 (by rfl) ⟨39977, by rfl⟩ : syracuseStep 3411413 = 79955) (by norm_num)
theorem B2274275 : Blo 2273435 2274275 := bstep (se 1 (by rfl) ⟨1705706, by rfl⟩ : syracuseStep 2274275 = 3411413) B3411413
theorem B8635157 : Blo 2273435 8635157 := bbase (se 6 (by rfl) ⟨202386, by rfl⟩ : syracuseStep 8635157 = 404773) (by norm_num)
theorem B5756771 : Blo 2273435 5756771 := bstep (se 1 (by rfl) ⟨4317578, by rfl⟩ : syracuseStep 5756771 = 8635157) B8635157
theorem B3837847 : Blo 2273435 3837847 := bstep (se 1 (by rfl) ⟨2878385, by rfl⟩ : syracuseStep 3837847 = 5756771) B5756771
theorem B5117129 : Blo 2273435 5117129 := bstep (se 2 (by rfl) ⟨1918923, by rfl⟩ : syracuseStep 5117129 = 3837847) B3837847
theorem B3411419 : Blo 2273435 3411419 := bstep (se 1 (by rfl) ⟨2558564, by rfl⟩ : syracuseStep 3411419 = 5117129) B5117129
theorem B2274279 : Blo 2273435 2274279 := bstep (se 1 (by rfl) ⟨1705709, by rfl⟩ : syracuseStep 2274279 = 3411419) B3411419
theorem B2558569 : Blo 2273435 2558569 := bbase (se 2 (by rfl) ⟨959463, by rfl⟩ : syracuseStep 2558569 = 1918927) (by norm_num)
theorem B3411425 : Blo 2273435 3411425 := bstep (se 2 (by rfl) ⟨1279284, by rfl⟩ : syracuseStep 3411425 = 2558569) B2558569
theorem B2274283 : Blo 2273435 2274283 := bstep (se 1 (by rfl) ⟨1705712, by rfl⟩ : syracuseStep 2274283 = 3411425) B3411425
theorem B4857293 : Blo 2273435 4857293 := bbase (se 3 (by rfl) ⟨910742, by rfl⟩ : syracuseStep 4857293 = 1821485) (by norm_num)
theorem B12952781 : Blo 2273435 12952781 := bstep (se 3 (by rfl) ⟨2428646, by rfl⟩ : syracuseStep 12952781 = 4857293) B4857293
theorem B8635187 : Blo 2273435 8635187 := bstep (se 1 (by rfl) ⟨6476390, by rfl⟩ : syracuseStep 8635187 = 12952781) B12952781
theorem B5756791 : Blo 2273435 5756791 := bstep (se 1 (by rfl) ⟨4317593, by rfl⟩ : syracuseStep 5756791 = 8635187) B8635187
theorem B7675721 : Blo 2273435 7675721 := bstep (se 2 (by rfl) ⟨2878395, by rfl⟩ : syracuseStep 7675721 = 5756791) B5756791
theorem B5117147 : Blo 2273435 5117147 := bstep (se 1 (by rfl) ⟨3837860, by rfl⟩ : syracuseStep 5117147 = 7675721) B7675721
theorem B3411431 : Blo 2273435 3411431 := bstep (se 1 (by rfl) ⟨2558573, by rfl⟩ : syracuseStep 3411431 = 5117147) B5117147
theorem B2274287 : Blo 2273435 2274287 := bstep (se 1 (by rfl) ⟨1705715, by rfl⟩ : syracuseStep 2274287 = 3411431) B3411431
theorem B3411437 : Blo 2273435 3411437 := bbase (se 3 (by rfl) ⟨639644, by rfl⟩ : syracuseStep 3411437 = 1279289) (by norm_num)
theorem B2274291 : Blo 2273435 2274291 := bstep (se 1 (by rfl) ⟨1705718, by rfl⟩ : syracuseStep 2274291 = 3411437) B3411437
theorem B5117165 : Blo 2273435 5117165 := bbase (se 3 (by rfl) ⟨959468, by rfl⟩ : syracuseStep 5117165 = 1918937) (by norm_num)
theorem B3411443 : Blo 2273435 3411443 := bstep (se 1 (by rfl) ⟨2558582, by rfl⟩ : syracuseStep 3411443 = 5117165) B5117165
theorem B2274295 : Blo 2273435 2274295 := bstep (se 1 (by rfl) ⟨1705721, by rfl⟩ : syracuseStep 2274295 = 3411443) B3411443
theorem B3238213 : Blo 2273435 3238213 := bbase (se 4 (by rfl) ⟨303582, by rfl⟩ : syracuseStep 3238213 = 607165) (by norm_num)
theorem B4317617 : Blo 2273435 4317617 := bstep (se 2 (by rfl) ⟨1619106, by rfl⟩ : syracuseStep 4317617 = 3238213) B3238213
theorem B2878411 : Blo 2273435 2878411 := bstep (se 1 (by rfl) ⟨2158808, by rfl⟩ : syracuseStep 2878411 = 4317617) B4317617
theorem B3837881 : Blo 2273435 3837881 := bstep (se 2 (by rfl) ⟨1439205, by rfl⟩ : syracuseStep 3837881 = 2878411) B2878411
theorem B2558587 : Blo 2273435 2558587 := bstep (se 1 (by rfl) ⟨1918940, by rfl⟩ : syracuseStep 2558587 = 3837881) B3837881
theorem B3411449 : Blo 2273435 3411449 := bstep (se 2 (by rfl) ⟨1279293, by rfl⟩ : syracuseStep 3411449 = 2558587) B2558587
theorem B2274299 : Blo 2273435 2274299 := bstep (se 1 (by rfl) ⟨1705724, by rfl⟩ : syracuseStep 2274299 = 3411449) B3411449
theorem B2305333 : Blo 2273435 2305333 := bbase (se 5 (by rfl) ⟨108062, by rfl⟩ : syracuseStep 2305333 = 216125) (by norm_num)
theorem B12295109 : Blo 2273435 12295109 := bstep (se 4 (by rfl) ⟨1152666, by rfl⟩ : syracuseStep 12295109 = 2305333) B2305333
theorem B32786957 : Blo 2273435 32786957 := bstep (se 3 (by rfl) ⟨6147554, by rfl⟩ : syracuseStep 32786957 = 12295109) B12295109
theorem B87431885 : Blo 2273435 87431885 := bstep (se 3 (by rfl) ⟨16393478, by rfl⟩ : syracuseStep 87431885 = 32786957) B32786957
theorem B58287923 : Blo 2273435 58287923 := bstep (se 1 (by rfl) ⟨43715942, by rfl⟩ : syracuseStep 58287923 = 87431885) B87431885
theorem B38858615 : Blo 2273435 38858615 := bstep (se 1 (by rfl) ⟨29143961, by rfl⟩ : syracuseStep 38858615 = 58287923) B58287923
theorem B25905743 : Blo 2273435 25905743 := bstep (se 1 (by rfl) ⟨19429307, by rfl⟩ : syracuseStep 25905743 = 38858615) B38858615
theorem B17270495 : Blo 2273435 17270495 := bstep (se 1 (by rfl) ⟨12952871, by rfl⟩ : syracuseStep 17270495 = 25905743) B25905743
theorem B11513663 : Blo 2273435 11513663 := bstep (se 1 (by rfl) ⟨8635247, by rfl⟩ : syracuseStep 11513663 = 17270495) B17270495
theorem B7675775 : Blo 2273435 7675775 := bstep (se 1 (by rfl) ⟨5756831, by rfl⟩ : syracuseStep 7675775 = 11513663) B11513663
theorem B5117183 : Blo 2273435 5117183 := bstep (se 1 (by rfl) ⟨3837887, by rfl⟩ : syracuseStep 5117183 = 7675775) B7675775
theorem B3411455 : Blo 2273435 3411455 := bstep (se 1 (by rfl) ⟨2558591, by rfl⟩ : syracuseStep 3411455 = 5117183) B5117183
theorem B2274303 : Blo 2273435 2274303 := bstep (se 1 (by rfl) ⟨1705727, by rfl⟩ : syracuseStep 2274303 = 3411455) B3411455
theorem B3411461 : Blo 2273435 3411461 := bbase (se 4 (by rfl) ⟨319824, by rfl⟩ : syracuseStep 3411461 = 639649) (by norm_num)
theorem B2274307 : Blo 2273435 2274307 := bstep (se 1 (by rfl) ⟨1705730, by rfl⟩ : syracuseStep 2274307 = 3411461) B3411461
theorem B3837901 : Blo 2273435 3837901 := bbase (se 3 (by rfl) ⟨719606, by rfl⟩ : syracuseStep 3837901 = 1439213) (by norm_num)
theorem B5117201 : Blo 2273435 5117201 := bstep (se 2 (by rfl) ⟨1918950, by rfl⟩ : syracuseStep 5117201 = 3837901) B3837901
theorem B3411467 : Blo 2273435 3411467 := bstep (se 1 (by rfl) ⟨2558600, by rfl⟩ : syracuseStep 3411467 = 5117201) B5117201
theorem B2274311 : Blo 2273435 2274311 := bstep (se 1 (by rfl) ⟨1705733, by rfl⟩ : syracuseStep 2274311 = 3411467) B3411467
theorem B2558605 : Blo 2273435 2558605 := bbase (se 3 (by rfl) ⟨479738, by rfl⟩ : syracuseStep 2558605 = 959477) (by norm_num)
theorem B3411473 : Blo 2273435 3411473 := bstep (se 2 (by rfl) ⟨1279302, by rfl⟩ : syracuseStep 3411473 = 2558605) B2558605
theorem B2274315 : Blo 2273435 2274315 := bstep (se 1 (by rfl) ⟨1705736, by rfl⟩ : syracuseStep 2274315 = 3411473) B3411473
theorem B7675829 : Blo 2273435 7675829 := bbase (se 5 (by rfl) ⟨359804, by rfl⟩ : syracuseStep 7675829 = 719609) (by norm_num)
theorem B5117219 : Blo 2273435 5117219 := bstep (se 1 (by rfl) ⟨3837914, by rfl⟩ : syracuseStep 5117219 = 7675829) B7675829
theorem B3411479 : Blo 2273435 3411479 := bstep (se 1 (by rfl) ⟨2558609, by rfl⟩ : syracuseStep 3411479 = 5117219) B5117219
theorem B2274319 : Blo 2273435 2274319 := bstep (se 1 (by rfl) ⟨1705739, by rfl⟩ : syracuseStep 2274319 = 3411479) B3411479
theorem B3411485 : Blo 2273435 3411485 := bbase (se 3 (by rfl) ⟨639653, by rfl⟩ : syracuseStep 3411485 = 1279307) (by norm_num)
theorem B2274323 : Blo 2273435 2274323 := bstep (se 1 (by rfl) ⟨1705742, by rfl⟩ : syracuseStep 2274323 = 3411485) B3411485
theorem B5117237 : Blo 2273435 5117237 := bbase (se 5 (by rfl) ⟨239870, by rfl⟩ : syracuseStep 5117237 = 479741) (by norm_num)
theorem B3411491 : Blo 2273435 3411491 := bstep (se 1 (by rfl) ⟨2558618, by rfl⟩ : syracuseStep 3411491 = 5117237) B5117237
theorem B2274327 : Blo 2273435 2274327 := bstep (se 1 (by rfl) ⟨1705745, by rfl⟩ : syracuseStep 2274327 = 3411491) B3411491
theorem B4098421 : Blo 2273435 4098421 := bbase (se 5 (by rfl) ⟨192113, by rfl⟩ : syracuseStep 4098421 = 384227) (by norm_num)
theorem B21858245 : Blo 2273435 21858245 := bstep (se 4 (by rfl) ⟨2049210, by rfl⟩ : syracuseStep 21858245 = 4098421) B4098421
theorem B14572163 : Blo 2273435 14572163 := bstep (se 1 (by rfl) ⟨10929122, by rfl⟩ : syracuseStep 14572163 = 21858245) B21858245
theorem B9714775 : Blo 2273435 9714775 := bstep (se 1 (by rfl) ⟨7286081, by rfl⟩ : syracuseStep 9714775 = 14572163) B14572163
theorem B12953033 : Blo 2273435 12953033 := bstep (se 2 (by rfl) ⟨4857387, by rfl⟩ : syracuseStep 12953033 = 9714775) B9714775
theorem B8635355 : Blo 2273435 8635355 := bstep (se 1 (by rfl) ⟨6476516, by rfl⟩ : syracuseStep 8635355 = 12953033) B12953033
theorem B5756903 : Blo 2273435 5756903 := bstep (se 1 (by rfl) ⟨4317677, by rfl⟩ : syracuseStep 5756903 = 8635355) B8635355
theorem B3837935 : Blo 2273435 3837935 := bstep (se 1 (by rfl) ⟨2878451, by rfl⟩ : syracuseStep 3837935 = 5756903) B5756903
theorem B2558623 : Blo 2273435 2558623 := bstep (se 1 (by rfl) ⟨1918967, by rfl⟩ : syracuseStep 2558623 = 3837935) B3837935
theorem B3411497 : Blo 2273435 3411497 := bstep (se 2 (by rfl) ⟨1279311, by rfl⟩ : syracuseStep 3411497 = 2558623) B2558623
theorem B2274331 : Blo 2273435 2274331 := bstep (se 1 (by rfl) ⟨1705748, by rfl⟩ : syracuseStep 2274331 = 3411497) B3411497
theorem B19963381 : Blo 2273435 19963381 := bbase (se 5 (by rfl) ⟨935783, by rfl⟩ : syracuseStep 19963381 = 1871567) (by norm_num)
theorem B26617841 : Blo 2273435 26617841 := bstep (se 2 (by rfl) ⟨9981690, by rfl⟩ : syracuseStep 26617841 = 19963381) B19963381
theorem B17745227 : Blo 2273435 17745227 := bstep (se 1 (by rfl) ⟨13308920, by rfl⟩ : syracuseStep 17745227 = 26617841) B26617841
theorem B11830151 : Blo 2273435 11830151 := bstep (se 1 (by rfl) ⟨8872613, by rfl⟩ : syracuseStep 11830151 = 17745227) B17745227
theorem B7886767 : Blo 2273435 7886767 := bstep (se 1 (by rfl) ⟨5915075, by rfl⟩ : syracuseStep 7886767 = 11830151) B11830151
theorem B10515689 : Blo 2273435 10515689 := bstep (se 2 (by rfl) ⟨3943383, by rfl⟩ : syracuseStep 10515689 = 7886767) B7886767
theorem B7010459 : Blo 2273435 7010459 := bstep (se 1 (by rfl) ⟨5257844, by rfl⟩ : syracuseStep 7010459 = 10515689) B10515689
theorem B4673639 : Blo 2273435 4673639 := bstep (se 1 (by rfl) ⟨3505229, by rfl⟩ : syracuseStep 4673639 = 7010459) B7010459
theorem B3115759 : Blo 2273435 3115759 := bstep (se 1 (by rfl) ⟨2336819, by rfl⟩ : syracuseStep 3115759 = 4673639) B4673639
theorem B4154345 : Blo 2273435 4154345 := bstep (se 2 (by rfl) ⟨1557879, by rfl⟩ : syracuseStep 4154345 = 3115759) B3115759
theorem B2769563 : Blo 2273435 2769563 := bstep (se 1 (by rfl) ⟨2077172, by rfl⟩ : syracuseStep 2769563 = 4154345) B4154345
theorem B7385501 : Blo 2273435 7385501 := bstep (se 3 (by rfl) ⟨1384781, by rfl⟩ : syracuseStep 7385501 = 2769563) B2769563
theorem B4923667 : Blo 2273435 4923667 := bstep (se 1 (by rfl) ⟨3692750, by rfl⟩ : syracuseStep 4923667 = 7385501) B7385501
theorem B26259557 : Blo 2273435 26259557 := bstep (se 4 (by rfl) ⟨2461833, by rfl⟩ : syracuseStep 26259557 = 4923667) B4923667
theorem B70025485 : Blo 2273435 70025485 := bstep (se 3 (by rfl) ⟨13129778, by rfl⟩ : syracuseStep 70025485 = 26259557) B26259557
theorem B93367313 : Blo 2273435 93367313 := bstep (se 2 (by rfl) ⟨35012742, by rfl⟩ : syracuseStep 93367313 = 70025485) B70025485
theorem B62244875 : Blo 2273435 62244875 := bstep (se 1 (by rfl) ⟨46683656, by rfl⟩ : syracuseStep 62244875 = 93367313) B93367313
theorem B41496583 : Blo 2273435 41496583 := bstep (se 1 (by rfl) ⟨31122437, by rfl⟩ : syracuseStep 41496583 = 62244875) B62244875
theorem B55328777 : Blo 2273435 55328777 := bstep (se 2 (by rfl) ⟨20748291, by rfl⟩ : syracuseStep 55328777 = 41496583) B41496583
theorem B36885851 : Blo 2273435 36885851 := bstep (se 1 (by rfl) ⟨27664388, by rfl⟩ : syracuseStep 36885851 = 55328777) B55328777
theorem B24590567 : Blo 2273435 24590567 := bstep (se 1 (by rfl) ⟨18442925, by rfl⟩ : syracuseStep 24590567 = 36885851) B36885851
theorem B16393711 : Blo 2273435 16393711 := bstep (se 1 (by rfl) ⟨12295283, by rfl⟩ : syracuseStep 16393711 = 24590567) B24590567
theorem B21858281 : Blo 2273435 21858281 := bstep (se 2 (by rfl) ⟨8196855, by rfl⟩ : syracuseStep 21858281 = 16393711) B16393711
theorem B14572187 : Blo 2273435 14572187 := bstep (se 1 (by rfl) ⟨10929140, by rfl⟩ : syracuseStep 14572187 = 21858281) B21858281
theorem B9714791 : Blo 2273435 9714791 := bstep (se 1 (by rfl) ⟨7286093, by rfl⟩ : syracuseStep 9714791 = 14572187) B14572187
theorem B6476527 : Blo 2273435 6476527 := bstep (se 1 (by rfl) ⟨4857395, by rfl⟩ : syracuseStep 6476527 = 9714791) B9714791
theorem B8635369 : Blo 2273435 8635369 := bstep (se 2 (by rfl) ⟨3238263, by rfl⟩ : syracuseStep 8635369 = 6476527) B6476527
theorem B11513825 : Blo 2273435 11513825 := bstep (se 2 (by rfl) ⟨4317684, by rfl⟩ : syracuseStep 11513825 = 8635369) B8635369
theorem B7675883 : Blo 2273435 7675883 := bstep (se 1 (by rfl) ⟨5756912, by rfl⟩ : syracuseStep 7675883 = 11513825) B11513825
theorem B5117255 : Blo 2273435 5117255 := bstep (se 1 (by rfl) ⟨3837941, by rfl⟩ : syracuseStep 5117255 = 7675883) B7675883
theorem B3411503 : Blo 2273435 3411503 := bstep (se 1 (by rfl) ⟨2558627, by rfl⟩ : syracuseStep 3411503 = 5117255) B5117255
theorem B2274335 : Blo 2273435 2274335 := bstep (se 1 (by rfl) ⟨1705751, by rfl⟩ : syracuseStep 2274335 = 3411503) B3411503
theorem B3411509 : Blo 2273435 3411509 := bbase (se 5 (by rfl) ⟨159914, by rfl⟩ : syracuseStep 3411509 = 319829) (by norm_num)
theorem B2274339 : Blo 2273435 2274339 := bstep (se 1 (by rfl) ⟨1705754, by rfl⟩ : syracuseStep 2274339 = 3411509) B3411509
theorem B5756933 : Blo 2273435 5756933 := bbase (se 4 (by rfl) ⟨539712, by rfl⟩ : syracuseStep 5756933 = 1079425) (by norm_num)
theorem B3837955 : Blo 2273435 3837955 := bstep (se 1 (by rfl) ⟨2878466, by rfl⟩ : syracuseStep 3837955 = 5756933) B5756933
theorem B5117273 : Blo 2273435 5117273 := bstep (se 2 (by rfl) ⟨1918977, by rfl⟩ : syracuseStep 5117273 = 3837955) B3837955
theorem B3411515 : Blo 2273435 3411515 := bstep (se 1 (by rfl) ⟨2558636, by rfl⟩ : syracuseStep 3411515 = 5117273) B5117273
theorem B2274343 : Blo 2273435 2274343 := bstep (se 1 (by rfl) ⟨1705757, by rfl⟩ : syracuseStep 2274343 = 3411515) B3411515
theorem B2558641 : Blo 2273435 2558641 := bbase (se 2 (by rfl) ⟨959490, by rfl⟩ : syracuseStep 2558641 = 1918981) (by norm_num)
theorem B3411521 : Blo 2273435 3411521 := bstep (se 2 (by rfl) ⟨1279320, by rfl⟩ : syracuseStep 3411521 = 2558641) B2558641
theorem B2274347 : Blo 2273435 2274347 := bstep (se 1 (by rfl) ⟨1705760, by rfl⟩ : syracuseStep 2274347 = 3411521) B3411521
theorem B2732305 : Blo 2273435 2732305 := bbase (se 2 (by rfl) ⟨1024614, by rfl⟩ : syracuseStep 2732305 = 2049229) (by norm_num)
theorem B3643073 : Blo 2273435 3643073 := bstep (se 2 (by rfl) ⟨1366152, by rfl⟩ : syracuseStep 3643073 = 2732305) B2732305
theorem B2428715 : Blo 2273435 2428715 := bstep (se 1 (by rfl) ⟨1821536, by rfl⟩ : syracuseStep 2428715 = 3643073) B3643073
theorem B6476573 : Blo 2273435 6476573 := bstep (se 3 (by rfl) ⟨1214357, by rfl⟩ : syracuseStep 6476573 = 2428715) B2428715
theorem B4317715 : Blo 2273435 4317715 := bstep (se 1 (by rfl) ⟨3238286, by rfl⟩ : syracuseStep 4317715 = 6476573) B6476573
theorem B5756953 : Blo 2273435 5756953 := bstep (se 2 (by rfl) ⟨2158857, by rfl⟩ : syracuseStep 5756953 = 4317715) B4317715
theorem B7675937 : Blo 2273435 7675937 := bstep (se 2 (by rfl) ⟨2878476, by rfl⟩ : syracuseStep 7675937 = 5756953) B5756953
theorem B5117291 : Blo 2273435 5117291 := bstep (se 1 (by rfl) ⟨3837968, by rfl⟩ : syracuseStep 5117291 = 7675937) B7675937
theorem B3411527 : Blo 2273435 3411527 := bstep (se 1 (by rfl) ⟨2558645, by rfl⟩ : syracuseStep 3411527 = 5117291) B5117291
theorem B2274351 : Blo 2273435 2274351 := bstep (se 1 (by rfl) ⟨1705763, by rfl⟩ : syracuseStep 2274351 = 3411527) B3411527
theorem B3411533 : Blo 2273435 3411533 := bbase (se 3 (by rfl) ⟨639662, by rfl⟩ : syracuseStep 3411533 = 1279325) (by norm_num)
theorem B2274355 : Blo 2273435 2274355 := bstep (se 1 (by rfl) ⟨1705766, by rfl⟩ : syracuseStep 2274355 = 3411533) B3411533
theorem B5117309 : Blo 2273435 5117309 := bbase (se 3 (by rfl) ⟨959495, by rfl⟩ : syracuseStep 5117309 = 1918991) (by norm_num)
theorem B3411539 : Blo 2273435 3411539 := bstep (se 1 (by rfl) ⟨2558654, by rfl⟩ : syracuseStep 3411539 = 5117309) B5117309
theorem B2274359 : Blo 2273435 2274359 := bstep (se 1 (by rfl) ⟨1705769, by rfl⟩ : syracuseStep 2274359 = 3411539) B3411539
theorem B3837989 : Blo 2273435 3837989 := bbase (se 4 (by rfl) ⟨359811, by rfl⟩ : syracuseStep 3837989 = 719623) (by norm_num)
theorem B2558659 : Blo 2273435 2558659 := bstep (se 1 (by rfl) ⟨1918994, by rfl⟩ : syracuseStep 2558659 = 3837989) B3837989
theorem B3411545 : Blo 2273435 3411545 := bstep (se 2 (by rfl) ⟨1279329, by rfl⟩ : syracuseStep 3411545 = 2558659) B2558659
theorem B2274363 : Blo 2273435 2274363 := bstep (se 1 (by rfl) ⟨1705772, by rfl⟩ : syracuseStep 2274363 = 3411545) B3411545
theorem B3238309 : Blo 2273435 3238309 := bbase (se 4 (by rfl) ⟨303591, by rfl⟩ : syracuseStep 3238309 = 607183) (by norm_num)
theorem B17270981 : Blo 2273435 17270981 := bstep (se 4 (by rfl) ⟨1619154, by rfl⟩ : syracuseStep 17270981 = 3238309) B3238309
theorem B11513987 : Blo 2273435 11513987 := bstep (se 1 (by rfl) ⟨8635490, by rfl⟩ : syracuseStep 11513987 = 17270981) B17270981
theorem B7675991 : Blo 2273435 7675991 := bstep (se 1 (by rfl) ⟨5756993, by rfl⟩ : syracuseStep 7675991 = 11513987) B11513987
theorem B5117327 : Blo 2273435 5117327 := bstep (se 1 (by rfl) ⟨3837995, by rfl⟩ : syracuseStep 5117327 = 7675991) B7675991
theorem B3411551 : Blo 2273435 3411551 := bstep (se 1 (by rfl) ⟨2558663, by rfl⟩ : syracuseStep 3411551 = 5117327) B5117327
theorem B2274367 : Blo 2273435 2274367 := bstep (se 1 (by rfl) ⟨1705775, by rfl⟩ : syracuseStep 2274367 = 3411551) B3411551
theorem B3411557 : Blo 2273435 3411557 := bbase (se 4 (by rfl) ⟨319833, by rfl⟩ : syracuseStep 3411557 = 639667) (by norm_num)
theorem B2274371 : Blo 2273435 2274371 := bstep (se 1 (by rfl) ⟨1705778, by rfl⟩ : syracuseStep 2274371 = 3411557) B3411557
theorem B2428741 : Blo 2273435 2428741 := bbase (se 4 (by rfl) ⟨227694, by rfl⟩ : syracuseStep 2428741 = 455389) (by norm_num)
theorem B3238321 : Blo 2273435 3238321 := bstep (se 2 (by rfl) ⟨1214370, by rfl⟩ : syracuseStep 3238321 = 2428741) B2428741
theorem B4317761 : Blo 2273435 4317761 := bstep (se 2 (by rfl) ⟨1619160, by rfl⟩ : syracuseStep 4317761 = 3238321) B3238321
theorem B2878507 : Blo 2273435 2878507 := bstep (se 1 (by rfl) ⟨2158880, by rfl⟩ : syracuseStep 2878507 = 4317761) B4317761
theorem B3838009 : Blo 2273435 3838009 := bstep (se 2 (by rfl) ⟨1439253, by rfl⟩ : syracuseStep 3838009 = 2878507) B2878507
theorem B5117345 : Blo 2273435 5117345 := bstep (se 2 (by rfl) ⟨1919004, by rfl⟩ : syracuseStep 5117345 = 3838009) B3838009
theorem B3411563 : Blo 2273435 3411563 := bstep (se 1 (by rfl) ⟨2558672, by rfl⟩ : syracuseStep 3411563 = 5117345) B5117345
theorem B2274375 : Blo 2273435 2274375 := bstep (se 1 (by rfl) ⟨1705781, by rfl⟩ : syracuseStep 2274375 = 3411563) B3411563
theorem B2558677 : Blo 2273435 2558677 := bbase (se 7 (by rfl) ⟨29984, by rfl⟩ : syracuseStep 2558677 = 59969) (by norm_num)
theorem B3411569 : Blo 2273435 3411569 := bstep (se 2 (by rfl) ⟨1279338, by rfl⟩ : syracuseStep 3411569 = 2558677) B2558677
theorem B2274379 : Blo 2273435 2274379 := bstep (se 1 (by rfl) ⟨1705784, by rfl⟩ : syracuseStep 2274379 = 3411569) B3411569
theorem B2878517 : Blo 2273435 2878517 := bbase (se 5 (by rfl) ⟨134930, by rfl⟩ : syracuseStep 2878517 = 269861) (by norm_num)
theorem B7676045 : Blo 2273435 7676045 := bstep (se 3 (by rfl) ⟨1439258, by rfl⟩ : syracuseStep 7676045 = 2878517) B2878517
theorem B5117363 : Blo 2273435 5117363 := bstep (se 1 (by rfl) ⟨3838022, by rfl⟩ : syracuseStep 5117363 = 7676045) B7676045
theorem B3411575 : Blo 2273435 3411575 := bstep (se 1 (by rfl) ⟨2558681, by rfl⟩ : syracuseStep 3411575 = 5117363) B5117363
theorem B2274383 : Blo 2273435 2274383 := bstep (se 1 (by rfl) ⟨1705787, by rfl⟩ : syracuseStep 2274383 = 3411575) B3411575
theorem B3411581 : Blo 2273435 3411581 := bbase (se 3 (by rfl) ⟨639671, by rfl⟩ : syracuseStep 3411581 = 1279343) (by norm_num)
theorem B2274387 : Blo 2273435 2274387 := bstep (se 1 (by rfl) ⟨1705790, by rfl⟩ : syracuseStep 2274387 = 3411581) B3411581
theorem B5117381 : Blo 2273435 5117381 := bbase (se 4 (by rfl) ⟨479754, by rfl⟩ : syracuseStep 5117381 = 959509) (by norm_num)
theorem B3411587 : Blo 2273435 3411587 := bstep (se 1 (by rfl) ⟨2558690, by rfl⟩ : syracuseStep 3411587 = 5117381) B5117381
theorem B2274391 : Blo 2273435 2274391 := bstep (se 1 (by rfl) ⟨1705793, by rfl⟩ : syracuseStep 2274391 = 3411587) B3411587
theorem B3458141 : Blo 2273435 3458141 := bbase (se 3 (by rfl) ⟨648401, by rfl⟩ : syracuseStep 3458141 = 1296803) (by norm_num)
theorem B2305427 : Blo 2273435 2305427 := bstep (se 1 (by rfl) ⟨1729070, by rfl⟩ : syracuseStep 2305427 = 3458141) B3458141
theorem B24591221 : Blo 2273435 24591221 := bstep (se 5 (by rfl) ⟨1152713, by rfl⟩ : syracuseStep 24591221 = 2305427) B2305427
theorem B16394147 : Blo 2273435 16394147 := bstep (se 1 (by rfl) ⟨12295610, by rfl⟩ : syracuseStep 16394147 = 24591221) B24591221
theorem B10929431 : Blo 2273435 10929431 := bstep (se 1 (by rfl) ⟨8197073, by rfl⟩ : syracuseStep 10929431 = 16394147) B16394147
theorem B7286287 : Blo 2273435 7286287 := bstep (se 1 (by rfl) ⟨5464715, by rfl⟩ : syracuseStep 7286287 = 10929431) B10929431
theorem B9715049 : Blo 2273435 9715049 := bstep (se 2 (by rfl) ⟨3643143, by rfl⟩ : syracuseStep 9715049 = 7286287) B7286287
theorem B6476699 : Blo 2273435 6476699 := bstep (se 1 (by rfl) ⟨4857524, by rfl⟩ : syracuseStep 6476699 = 9715049) B9715049
theorem B4317799 : Blo 2273435 4317799 := bstep (se 1 (by rfl) ⟨3238349, by rfl⟩ : syracuseStep 4317799 = 6476699) B6476699
theorem B5757065 : Blo 2273435 5757065 := bstep (se 2 (by rfl) ⟨2158899, by rfl⟩ : syracuseStep 5757065 = 4317799) B4317799
theorem B3838043 : Blo 2273435 3838043 := bstep (se 1 (by rfl) ⟨2878532, by rfl⟩ : syracuseStep 3838043 = 5757065) B5757065
theorem B2558695 : Blo 2273435 2558695 := bstep (se 1 (by rfl) ⟨1919021, by rfl⟩ : syracuseStep 2558695 = 3838043) B3838043
theorem B3411593 : Blo 2273435 3411593 := bstep (se 2 (by rfl) ⟨1279347, by rfl⟩ : syracuseStep 3411593 = 2558695) B2558695
theorem B2274395 : Blo 2273435 2274395 := bstep (se 1 (by rfl) ⟨1705796, by rfl⟩ : syracuseStep 2274395 = 3411593) B3411593
theorem B11514149 : Blo 2273435 11514149 := bbase (se 4 (by rfl) ⟨1079451, by rfl⟩ : syracuseStep 11514149 = 2158903) (by norm_num)
theorem B7676099 : Blo 2273435 7676099 := bstep (se 1 (by rfl) ⟨5757074, by rfl⟩ : syracuseStep 7676099 = 11514149) B11514149
theorem B5117399 : Blo 2273435 5117399 := bstep (se 1 (by rfl) ⟨3838049, by rfl⟩ : syracuseStep 5117399 = 7676099) B7676099
theorem B3411599 : Blo 2273435 3411599 := bstep (se 1 (by rfl) ⟨2558699, by rfl⟩ : syracuseStep 3411599 = 5117399) B5117399
theorem B2274399 : Blo 2273435 2274399 := bstep (se 1 (by rfl) ⟨1705799, by rfl⟩ : syracuseStep 2274399 = 3411599) B3411599
theorem B3411605 : Blo 2273435 3411605 := bbase (se 6 (by rfl) ⟨79959, by rfl⟩ : syracuseStep 3411605 = 159919) (by norm_num)
theorem B2274403 : Blo 2273435 2274403 := bstep (se 1 (by rfl) ⟨1705802, by rfl⟩ : syracuseStep 2274403 = 3411605) B3411605
theorem B11671285 : Blo 2273435 11671285 := bbase (se 5 (by rfl) ⟨547091, by rfl⟩ : syracuseStep 11671285 = 1094183) (by norm_num)
theorem B15561713 : Blo 2273435 15561713 := bstep (se 2 (by rfl) ⟨5835642, by rfl⟩ : syracuseStep 15561713 = 11671285) B11671285
theorem B10374475 : Blo 2273435 10374475 := bstep (se 1 (by rfl) ⟨7780856, by rfl⟩ : syracuseStep 10374475 = 15561713) B15561713
theorem B13832633 : Blo 2273435 13832633 := bstep (se 2 (by rfl) ⟨5187237, by rfl⟩ : syracuseStep 13832633 = 10374475) B10374475
theorem B36887021 : Blo 2273435 36887021 := bstep (se 3 (by rfl) ⟨6916316, by rfl⟩ : syracuseStep 36887021 = 13832633) B13832633
theorem B24591347 : Blo 2273435 24591347 := bstep (se 1 (by rfl) ⟨18443510, by rfl⟩ : syracuseStep 24591347 = 36887021) B36887021
theorem B16394231 : Blo 2273435 16394231 := bstep (se 1 (by rfl) ⟨12295673, by rfl⟩ : syracuseStep 16394231 = 24591347) B24591347
theorem B10929487 : Blo 2273435 10929487 := bstep (se 1 (by rfl) ⟨8197115, by rfl⟩ : syracuseStep 10929487 = 16394231) B16394231
theorem B14572649 : Blo 2273435 14572649 := bstep (se 2 (by rfl) ⟨5464743, by rfl⟩ : syracuseStep 14572649 = 10929487) B10929487
theorem B9715099 : Blo 2273435 9715099 := bstep (se 1 (by rfl) ⟨7286324, by rfl⟩ : syracuseStep 9715099 = 14572649) B14572649
theorem B12953465 : Blo 2273435 12953465 := bstep (se 2 (by rfl) ⟨4857549, by rfl⟩ : syracuseStep 12953465 = 9715099) B9715099
theorem B8635643 : Blo 2273435 8635643 := bstep (se 1 (by rfl) ⟨6476732, by rfl⟩ : syracuseStep 8635643 = 12953465) B12953465
theorem B5757095 : Blo 2273435 5757095 := bstep (se 1 (by rfl) ⟨4317821, by rfl⟩ : syracuseStep 5757095 = 8635643) B8635643
theorem B3838063 : Blo 2273435 3838063 := bstep (se 1 (by rfl) ⟨2878547, by rfl⟩ : syracuseStep 3838063 = 5757095) B5757095
theorem B5117417 : Blo 2273435 5117417 := bstep (se 2 (by rfl) ⟨1919031, by rfl⟩ : syracuseStep 5117417 = 3838063) B3838063
theorem B3411611 : Blo 2273435 3411611 := bstep (se 1 (by rfl) ⟨2558708, by rfl⟩ : syracuseStep 3411611 = 5117417) B5117417
theorem B2274407 : Blo 2273435 2274407 := bstep (se 1 (by rfl) ⟨1705805, by rfl⟩ : syracuseStep 2274407 = 3411611) B3411611
theorem B2558713 : Blo 2273435 2558713 := bbase (se 2 (by rfl) ⟨959517, by rfl⟩ : syracuseStep 2558713 = 1919035) (by norm_num)
theorem B3411617 : Blo 2273435 3411617 := bstep (se 2 (by rfl) ⟨1279356, by rfl⟩ : syracuseStep 3411617 = 2558713) B2558713
theorem B2274411 : Blo 2273435 2274411 := bstep (se 1 (by rfl) ⟨1705808, by rfl⟩ : syracuseStep 2274411 = 3411617) B3411617
theorem B4376749 : Blo 2273435 4376749 := bbase (se 3 (by rfl) ⟨820640, by rfl⟩ : syracuseStep 4376749 = 1641281) (by norm_num)
theorem B5835665 : Blo 2273435 5835665 := bstep (se 2 (by rfl) ⟨2188374, by rfl⟩ : syracuseStep 5835665 = 4376749) B4376749
theorem B3890443 : Blo 2273435 3890443 := bstep (se 1 (by rfl) ⟨2917832, by rfl⟩ : syracuseStep 3890443 = 5835665) B5835665
theorem B5187257 : Blo 2273435 5187257 := bstep (se 2 (by rfl) ⟨1945221, by rfl⟩ : syracuseStep 5187257 = 3890443) B3890443
theorem B3458171 : Blo 2273435 3458171 := bstep (se 1 (by rfl) ⟨2593628, by rfl⟩ : syracuseStep 3458171 = 5187257) B5187257
theorem B9221789 : Blo 2273435 9221789 := bstep (se 3 (by rfl) ⟨1729085, by rfl⟩ : syracuseStep 9221789 = 3458171) B3458171
theorem B6147859 : Blo 2273435 6147859 := bstep (se 1 (by rfl) ⟨4610894, by rfl⟩ : syracuseStep 6147859 = 9221789) B9221789
theorem B8197145 : Blo 2273435 8197145 := bstep (se 2 (by rfl) ⟨3073929, by rfl⟩ : syracuseStep 8197145 = 6147859) B6147859
theorem B5464763 : Blo 2273435 5464763 := bstep (se 1 (by rfl) ⟨4098572, by rfl⟩ : syracuseStep 5464763 = 8197145) B8197145
theorem B3643175 : Blo 2273435 3643175 := bstep (se 1 (by rfl) ⟨2732381, by rfl⟩ : syracuseStep 3643175 = 5464763) B5464763
theorem B9715133 : Blo 2273435 9715133 := bstep (se 3 (by rfl) ⟨1821587, by rfl⟩ : syracuseStep 9715133 = 3643175) B3643175
theorem B6476755 : Blo 2273435 6476755 := bstep (se 1 (by rfl) ⟨4857566, by rfl⟩ : syracuseStep 6476755 = 9715133) B9715133
theorem B8635673 : Blo 2273435 8635673 := bstep (se 2 (by rfl) ⟨3238377, by rfl⟩ : syracuseStep 8635673 = 6476755) B6476755
theorem B5757115 : Blo 2273435 5757115 := bstep (se 1 (by rfl) ⟨4317836, by rfl⟩ : syracuseStep 5757115 = 8635673) B8635673
theorem B7676153 : Blo 2273435 7676153 := bstep (se 2 (by rfl) ⟨2878557, by rfl⟩ : syracuseStep 7676153 = 5757115) B5757115
theorem B5117435 : Blo 2273435 5117435 := bstep (se 1 (by rfl) ⟨3838076, by rfl⟩ : syracuseStep 5117435 = 7676153) B7676153
theorem B3411623 : Blo 2273435 3411623 := bstep (se 1 (by rfl) ⟨2558717, by rfl⟩ : syracuseStep 3411623 = 5117435) B5117435
theorem B2274415 : Blo 2273435 2274415 := bstep (se 1 (by rfl) ⟨1705811, by rfl⟩ : syracuseStep 2274415 = 3411623) B3411623
theorem B3411629 : Blo 2273435 3411629 := bbase (se 3 (by rfl) ⟨639680, by rfl⟩ : syracuseStep 3411629 = 1279361) (by norm_num)
theorem B2274419 : Blo 2273435 2274419 := bstep (se 1 (by rfl) ⟨1705814, by rfl⟩ : syracuseStep 2274419 = 3411629) B3411629
theorem B5117453 : Blo 2273435 5117453 := bbase (se 3 (by rfl) ⟨959522, by rfl⟩ : syracuseStep 5117453 = 1919045) (by norm_num)
theorem B3411635 : Blo 2273435 3411635 := bstep (se 1 (by rfl) ⟨2558726, by rfl⟩ : syracuseStep 3411635 = 5117453) B5117453
theorem B2274423 : Blo 2273435 2274423 := bstep (se 1 (by rfl) ⟨1705817, by rfl⟩ : syracuseStep 2274423 = 3411635) B3411635
theorem B2878573 : Blo 2273435 2878573 := bbase (se 3 (by rfl) ⟨539732, by rfl⟩ : syracuseStep 2878573 = 1079465) (by norm_num)
theorem B3838097 : Blo 2273435 3838097 := bstep (se 2 (by rfl) ⟨1439286, by rfl⟩ : syracuseStep 3838097 = 2878573) B2878573
theorem B2558731 : Blo 2273435 2558731 := bstep (se 1 (by rfl) ⟨1919048, by rfl⟩ : syracuseStep 2558731 = 3838097) B3838097
theorem B3411641 : Blo 2273435 3411641 := bstep (se 2 (by rfl) ⟨1279365, by rfl⟩ : syracuseStep 3411641 = 2558731) B2558731
theorem B2274427 : Blo 2273435 2274427 := bstep (se 1 (by rfl) ⟨1705820, by rfl⟩ : syracuseStep 2274427 = 3411641) B3411641
theorem B5187293 : Blo 2273435 5187293 := bbase (se 3 (by rfl) ⟨972617, by rfl⟩ : syracuseStep 5187293 = 1945235) (by norm_num)
theorem B3458195 : Blo 2273435 3458195 := bstep (se 1 (by rfl) ⟨2593646, by rfl⟩ : syracuseStep 3458195 = 5187293) B5187293
theorem B2305463 : Blo 2273435 2305463 := bstep (se 1 (by rfl) ⟨1729097, by rfl⟩ : syracuseStep 2305463 = 3458195) B3458195
theorem B6147901 : Blo 2273435 6147901 := bstep (se 3 (by rfl) ⟨1152731, by rfl⟩ : syracuseStep 6147901 = 2305463) B2305463
theorem B8197201 : Blo 2273435 8197201 := bstep (se 2 (by rfl) ⟨3073950, by rfl⟩ : syracuseStep 8197201 = 6147901) B6147901
theorem B10929601 : Blo 2273435 10929601 := bstep (se 2 (by rfl) ⟨4098600, by rfl⟩ : syracuseStep 10929601 = 8197201) B8197201
theorem B14572801 : Blo 2273435 14572801 := bstep (se 2 (by rfl) ⟨5464800, by rfl⟩ : syracuseStep 14572801 = 10929601) B10929601
theorem B19430401 : Blo 2273435 19430401 := bstep (se 2 (by rfl) ⟨7286400, by rfl⟩ : syracuseStep 19430401 = 14572801) B14572801
theorem B25907201 : Blo 2273435 25907201 := bstep (se 2 (by rfl) ⟨9715200, by rfl⟩ : syracuseStep 25907201 = 19430401) B19430401
theorem B17271467 : Blo 2273435 17271467 := bstep (se 1 (by rfl) ⟨12953600, by rfl⟩ : syracuseStep 17271467 = 25907201) B25907201
theorem B11514311 : Blo 2273435 11514311 := bstep (se 1 (by rfl) ⟨8635733, by rfl⟩ : syracuseStep 11514311 = 17271467) B17271467
theorem B7676207 : Blo 2273435 7676207 := bstep (se 1 (by rfl) ⟨5757155, by rfl⟩ : syracuseStep 7676207 = 11514311) B11514311
theorem B5117471 : Blo 2273435 5117471 := bstep (se 1 (by rfl) ⟨3838103, by rfl⟩ : syracuseStep 5117471 = 7676207) B7676207
theorem B3411647 : Blo 2273435 3411647 := bstep (se 1 (by rfl) ⟨2558735, by rfl⟩ : syracuseStep 3411647 = 5117471) B5117471
theorem B2274431 : Blo 2273435 2274431 := bstep (se 1 (by rfl) ⟨1705823, by rfl⟩ : syracuseStep 2274431 = 3411647) B3411647
theorem B3411653 : Blo 2273435 3411653 := bbase (se 4 (by rfl) ⟨319842, by rfl⟩ : syracuseStep 3411653 = 639685) (by norm_num)
theorem B2274435 : Blo 2273435 2274435 := bstep (se 1 (by rfl) ⟨1705826, by rfl⟩ : syracuseStep 2274435 = 3411653) B3411653
theorem B3838117 : Blo 2273435 3838117 := bbase (se 4 (by rfl) ⟨359823, by rfl⟩ : syracuseStep 3838117 = 719647) (by norm_num)
theorem B5117489 : Blo 2273435 5117489 := bstep (se 2 (by rfl) ⟨1919058, by rfl⟩ : syracuseStep 5117489 = 3838117) B3838117
theorem B3411659 : Blo 2273435 3411659 := bstep (se 1 (by rfl) ⟨2558744, by rfl⟩ : syracuseStep 3411659 = 5117489) B5117489
theorem B2274439 : Blo 2273435 2274439 := bstep (se 1 (by rfl) ⟨1705829, by rfl⟩ : syracuseStep 2274439 = 3411659) B3411659
theorem B2558749 : Blo 2273435 2558749 := bbase (se 3 (by rfl) ⟨479765, by rfl⟩ : syracuseStep 2558749 = 959531) (by norm_num)
theorem B3411665 : Blo 2273435 3411665 := bstep (se 2 (by rfl) ⟨1279374, by rfl⟩ : syracuseStep 3411665 = 2558749) B2558749
theorem B2274443 : Blo 2273435 2274443 := bstep (se 1 (by rfl) ⟨1705832, by rfl⟩ : syracuseStep 2274443 = 3411665) B3411665
theorem B7676261 : Blo 2273435 7676261 := bbase (se 4 (by rfl) ⟨719649, by rfl⟩ : syracuseStep 7676261 = 1439299) (by norm_num)
theorem B5117507 : Blo 2273435 5117507 := bstep (se 1 (by rfl) ⟨3838130, by rfl⟩ : syracuseStep 5117507 = 7676261) B7676261
theorem B3411671 : Blo 2273435 3411671 := bstep (se 1 (by rfl) ⟨2558753, by rfl⟩ : syracuseStep 3411671 = 5117507) B5117507
theorem B2274447 : Blo 2273435 2274447 := bstep (se 1 (by rfl) ⟨1705835, by rfl⟩ : syracuseStep 2274447 = 3411671) B3411671
theorem B3411677 : Blo 2273435 3411677 := bbase (se 3 (by rfl) ⟨639689, by rfl⟩ : syracuseStep 3411677 = 1279379) (by norm_num)
theorem B2274451 : Blo 2273435 2274451 := bstep (se 1 (by rfl) ⟨1705838, by rfl⟩ : syracuseStep 2274451 = 3411677) B3411677
theorem B5117525 : Blo 2273435 5117525 := bbase (se 8 (by rfl) ⟨29985, by rfl⟩ : syracuseStep 5117525 = 59971) (by norm_num)
theorem B3411683 : Blo 2273435 3411683 := bstep (se 1 (by rfl) ⟨2558762, by rfl⟩ : syracuseStep 3411683 = 5117525) B5117525
theorem B2274455 : Blo 2273435 2274455 := bstep (se 1 (by rfl) ⟨1705841, by rfl⟩ : syracuseStep 2274455 = 3411683) B3411683
theorem B4857661 : Blo 2273435 4857661 := bbase (se 3 (by rfl) ⟨910811, by rfl⟩ : syracuseStep 4857661 = 1821623) (by norm_num)
theorem B6476881 : Blo 2273435 6476881 := bstep (se 2 (by rfl) ⟨2428830, by rfl⟩ : syracuseStep 6476881 = 4857661) B4857661
theorem B8635841 : Blo 2273435 8635841 := bstep (se 2 (by rfl) ⟨3238440, by rfl⟩ : syracuseStep 8635841 = 6476881) B6476881
theorem B5757227 : Blo 2273435 5757227 := bstep (se 1 (by rfl) ⟨4317920, by rfl⟩ : syracuseStep 5757227 = 8635841) B8635841
theorem B3838151 : Blo 2273435 3838151 := bstep (se 1 (by rfl) ⟨2878613, by rfl⟩ : syracuseStep 3838151 = 5757227) B5757227
theorem B2558767 : Blo 2273435 2558767 := bstep (se 1 (by rfl) ⟨1919075, by rfl⟩ : syracuseStep 2558767 = 3838151) B3838151
theorem B3411689 : Blo 2273435 3411689 := bstep (se 2 (by rfl) ⟨1279383, by rfl⟩ : syracuseStep 3411689 = 2558767) B2558767
theorem B2274459 : Blo 2273435 2274459 := bstep (se 1 (by rfl) ⟨1705844, by rfl⟩ : syracuseStep 2274459 = 3411689) B3411689
theorem B5258141 : Blo 2273435 5258141 := bbase (se 3 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 5258141 = 1971803) (by norm_num)
theorem B3505427 : Blo 2273435 3505427 := bstep (se 1 (by rfl) ⟨2629070, by rfl⟩ : syracuseStep 3505427 = 5258141) B5258141
theorem B2336951 : Blo 2273435 2336951 := bstep (se 1 (by rfl) ⟨1752713, by rfl⟩ : syracuseStep 2336951 = 3505427) B3505427
theorem B6231869 : Blo 2273435 6231869 := bstep (se 3 (by rfl) ⟨1168475, by rfl⟩ : syracuseStep 6231869 = 2336951) B2336951
theorem B4154579 : Blo 2273435 4154579 := bstep (se 1 (by rfl) ⟨3115934, by rfl⟩ : syracuseStep 4154579 = 6231869) B6231869
theorem B2769719 : Blo 2273435 2769719 := bstep (se 1 (by rfl) ⟨2077289, by rfl⟩ : syracuseStep 2769719 = 4154579) B4154579
theorem B7385917 : Blo 2273435 7385917 := bstep (se 3 (by rfl) ⟨1384859, by rfl⟩ : syracuseStep 7385917 = 2769719) B2769719
theorem B9847889 : Blo 2273435 9847889 := bstep (se 2 (by rfl) ⟨3692958, by rfl⟩ : syracuseStep 9847889 = 7385917) B7385917
theorem B6565259 : Blo 2273435 6565259 := bstep (se 1 (by rfl) ⟨4923944, by rfl⟩ : syracuseStep 6565259 = 9847889) B9847889
theorem B17507357 : Blo 2273435 17507357 := bstep (se 3 (by rfl) ⟨3282629, by rfl⟩ : syracuseStep 17507357 = 6565259) B6565259
theorem B11671571 : Blo 2273435 11671571 := bstep (se 1 (by rfl) ⟨8753678, by rfl⟩ : syracuseStep 11671571 = 17507357) B17507357
theorem B31124189 : Blo 2273435 31124189 := bstep (se 3 (by rfl) ⟨5835785, by rfl⟩ : syracuseStep 31124189 = 11671571) B11671571
theorem B20749459 : Blo 2273435 20749459 := bstep (se 1 (by rfl) ⟨15562094, by rfl⟩ : syracuseStep 20749459 = 31124189) B31124189
theorem B27665945 : Blo 2273435 27665945 := bstep (se 2 (by rfl) ⟨10374729, by rfl⟩ : syracuseStep 27665945 = 20749459) B20749459
theorem B18443963 : Blo 2273435 18443963 := bstep (se 1 (by rfl) ⟨13832972, by rfl⟩ : syracuseStep 18443963 = 27665945) B27665945
theorem B12295975 : Blo 2273435 12295975 := bstep (se 1 (by rfl) ⟨9221981, by rfl⟩ : syracuseStep 12295975 = 18443963) B18443963
theorem B16394633 : Blo 2273435 16394633 := bstep (se 2 (by rfl) ⟨6147987, by rfl⟩ : syracuseStep 16394633 = 12295975) B12295975
theorem B10929755 : Blo 2273435 10929755 := bstep (se 1 (by rfl) ⟨8197316, by rfl⟩ : syracuseStep 10929755 = 16394633) B16394633
theorem B29146013 : Blo 2273435 29146013 := bstep (se 3 (by rfl) ⟨5464877, by rfl⟩ : syracuseStep 29146013 = 10929755) B10929755
theorem B19430675 : Blo 2273435 19430675 := bstep (se 1 (by rfl) ⟨14573006, by rfl⟩ : syracuseStep 19430675 = 29146013) B29146013
theorem B12953783 : Blo 2273435 12953783 := bstep (se 1 (by rfl) ⟨9715337, by rfl⟩ : syracuseStep 12953783 = 19430675) B19430675
theorem B8635855 : Blo 2273435 8635855 := bstep (se 1 (by rfl) ⟨6476891, by rfl⟩ : syracuseStep 8635855 = 12953783) B12953783
theorem B11514473 : Blo 2273435 11514473 := bstep (se 2 (by rfl) ⟨4317927, by rfl⟩ : syracuseStep 11514473 = 8635855) B8635855
theorem B7676315 : Blo 2273435 7676315 := bstep (se 1 (by rfl) ⟨5757236, by rfl⟩ : syracuseStep 7676315 = 11514473) B11514473
theorem B5117543 : Blo 2273435 5117543 := bstep (se 1 (by rfl) ⟨3838157, by rfl⟩ : syracuseStep 5117543 = 7676315) B7676315
theorem B3411695 : Blo 2273435 3411695 := bstep (se 1 (by rfl) ⟨2558771, by rfl⟩ : syracuseStep 3411695 = 5117543) B5117543
theorem B2274463 : Blo 2273435 2274463 := bstep (se 1 (by rfl) ⟨1705847, by rfl⟩ : syracuseStep 2274463 = 3411695) B3411695
theorem B3411701 : Blo 2273435 3411701 := bbase (se 5 (by rfl) ⟨159923, by rfl⟩ : syracuseStep 3411701 = 319847) (by norm_num)
theorem B2274467 : Blo 2273435 2274467 := bstep (se 1 (by rfl) ⟨1705850, by rfl⟩ : syracuseStep 2274467 = 3411701) B3411701
theorem B2732449 : Blo 2273435 2732449 := bbase (se 2 (by rfl) ⟨1024668, by rfl⟩ : syracuseStep 2732449 = 2049337) (by norm_num)
theorem B3643265 : Blo 2273435 3643265 := bstep (se 2 (by rfl) ⟨1366224, by rfl⟩ : syracuseStep 3643265 = 2732449) B2732449
theorem B9715373 : Blo 2273435 9715373 := bstep (se 3 (by rfl) ⟨1821632, by rfl⟩ : syracuseStep 9715373 = 3643265) B3643265
theorem B6476915 : Blo 2273435 6476915 := bstep (se 1 (by rfl) ⟨4857686, by rfl⟩ : syracuseStep 6476915 = 9715373) B9715373
theorem B4317943 : Blo 2273435 4317943 := bstep (se 1 (by rfl) ⟨3238457, by rfl⟩ : syracuseStep 4317943 = 6476915) B6476915
theorem B5757257 : Blo 2273435 5757257 := bstep (se 2 (by rfl) ⟨2158971, by rfl⟩ : syracuseStep 5757257 = 4317943) B4317943
theorem B3838171 : Blo 2273435 3838171 := bstep (se 1 (by rfl) ⟨2878628, by rfl⟩ : syracuseStep 3838171 = 5757257) B5757257
theorem B5117561 : Blo 2273435 5117561 := bstep (se 2 (by rfl) ⟨1919085, by rfl⟩ : syracuseStep 5117561 = 3838171) B3838171
theorem B3411707 : Blo 2273435 3411707 := bstep (se 1 (by rfl) ⟨2558780, by rfl⟩ : syracuseStep 3411707 = 5117561) B5117561
theorem B2274471 : Blo 2273435 2274471 := bstep (se 1 (by rfl) ⟨1705853, by rfl⟩ : syracuseStep 2274471 = 3411707) B3411707
theorem B2558785 : Blo 2273435 2558785 := bbase (se 2 (by rfl) ⟨959544, by rfl⟩ : syracuseStep 2558785 = 1919089) (by norm_num)
theorem B3411713 : Blo 2273435 3411713 := bstep (se 2 (by rfl) ⟨1279392, by rfl⟩ : syracuseStep 3411713 = 2558785) B2558785
theorem B2274475 : Blo 2273435 2274475 := bstep (se 1 (by rfl) ⟨1705856, by rfl⟩ : syracuseStep 2274475 = 3411713) B3411713
theorem B5757277 : Blo 2273435 5757277 := bbase (se 3 (by rfl) ⟨1079489, by rfl⟩ : syracuseStep 5757277 = 2158979) (by norm_num)
theorem B7676369 : Blo 2273435 7676369 := bstep (se 2 (by rfl) ⟨2878638, by rfl⟩ : syracuseStep 7676369 = 5757277) B5757277
theorem B5117579 : Blo 2273435 5117579 := bstep (se 1 (by rfl) ⟨3838184, by rfl⟩ : syracuseStep 5117579 = 7676369) B7676369
theorem B3411719 : Blo 2273435 3411719 := bstep (se 1 (by rfl) ⟨2558789, by rfl⟩ : syracuseStep 3411719 = 5117579) B5117579
theorem B2274479 : Blo 2273435 2274479 := bstep (se 1 (by rfl) ⟨1705859, by rfl⟩ : syracuseStep 2274479 = 3411719) B3411719
theorem B3411725 : Blo 2273435 3411725 := bbase (se 3 (by rfl) ⟨639698, by rfl⟩ : syracuseStep 3411725 = 1279397) (by norm_num)
theorem B2274483 : Blo 2273435 2274483 := bstep (se 1 (by rfl) ⟨1705862, by rfl⟩ : syracuseStep 2274483 = 3411725) B3411725
theorem B5117597 : Blo 2273435 5117597 := bbase (se 3 (by rfl) ⟨959549, by rfl⟩ : syracuseStep 5117597 = 1919099) (by norm_num)
theorem B3411731 : Blo 2273435 3411731 := bstep (se 1 (by rfl) ⟨2558798, by rfl⟩ : syracuseStep 3411731 = 5117597) B5117597
theorem B2274487 : Blo 2273435 2274487 := bstep (se 1 (by rfl) ⟨1705865, by rfl⟩ : syracuseStep 2274487 = 3411731) B3411731
theorem B3838205 : Blo 2273435 3838205 := bbase (se 3 (by rfl) ⟨719663, by rfl⟩ : syracuseStep 3838205 = 1439327) (by norm_num)
theorem B2558803 : Blo 2273435 2558803 := bstep (se 1 (by rfl) ⟨1919102, by rfl⟩ : syracuseStep 2558803 = 3838205) B3838205
theorem B3411737 : Blo 2273435 3411737 := bstep (se 2 (by rfl) ⟨1279401, by rfl⟩ : syracuseStep 3411737 = 2558803) B2558803
theorem B2274491 : Blo 2273435 2274491 := bstep (se 1 (by rfl) ⟨1705868, by rfl⟩ : syracuseStep 2274491 = 3411737) B3411737
theorem B3943661 : Blo 2273435 3943661 := bbase (se 3 (by rfl) ⟨739436, by rfl⟩ : syracuseStep 3943661 = 1478873) (by norm_num)
theorem B10516429 : Blo 2273435 10516429 := bstep (se 3 (by rfl) ⟨1971830, by rfl⟩ : syracuseStep 10516429 = 3943661) B3943661
theorem B14021905 : Blo 2273435 14021905 := bstep (se 2 (by rfl) ⟨5258214, by rfl⟩ : syracuseStep 14021905 = 10516429) B10516429
theorem B18695873 : Blo 2273435 18695873 := bstep (se 2 (by rfl) ⟨7010952, by rfl⟩ : syracuseStep 18695873 = 14021905) B14021905
theorem B12463915 : Blo 2273435 12463915 := bstep (se 1 (by rfl) ⟨9347936, by rfl⟩ : syracuseStep 12463915 = 18695873) B18695873
theorem B16618553 : Blo 2273435 16618553 := bstep (se 2 (by rfl) ⟨6231957, by rfl⟩ : syracuseStep 16618553 = 12463915) B12463915
theorem B11079035 : Blo 2273435 11079035 := bstep (se 1 (by rfl) ⟨8309276, by rfl⟩ : syracuseStep 11079035 = 16618553) B16618553
theorem B7386023 : Blo 2273435 7386023 := bstep (se 1 (by rfl) ⟨5539517, by rfl⟩ : syracuseStep 7386023 = 11079035) B11079035
theorem B19696061 : Blo 2273435 19696061 := bstep (se 3 (by rfl) ⟨3693011, by rfl⟩ : syracuseStep 19696061 = 7386023) B7386023
theorem B13130707 : Blo 2273435 13130707 := bstep (se 1 (by rfl) ⟨9848030, by rfl⟩ : syracuseStep 13130707 = 19696061) B19696061
theorem B17507609 : Blo 2273435 17507609 := bstep (se 2 (by rfl) ⟨6565353, by rfl⟩ : syracuseStep 17507609 = 13130707) B13130707
theorem B11671739 : Blo 2273435 11671739 := bstep (se 1 (by rfl) ⟨8753804, by rfl⟩ : syracuseStep 11671739 = 17507609) B17507609
theorem B7781159 : Blo 2273435 7781159 := bstep (se 1 (by rfl) ⟨5835869, by rfl⟩ : syracuseStep 7781159 = 11671739) B11671739
theorem B5187439 : Blo 2273435 5187439 := bstep (se 1 (by rfl) ⟨3890579, by rfl⟩ : syracuseStep 5187439 = 7781159) B7781159
theorem B6916585 : Blo 2273435 6916585 := bstep (se 2 (by rfl) ⟨2593719, by rfl⟩ : syracuseStep 6916585 = 5187439) B5187439
theorem B9222113 : Blo 2273435 9222113 := bstep (se 2 (by rfl) ⟨3458292, by rfl⟩ : syracuseStep 9222113 = 6916585) B6916585
theorem B6148075 : Blo 2273435 6148075 := bstep (se 1 (by rfl) ⟨4611056, by rfl⟩ : syracuseStep 6148075 = 9222113) B9222113
theorem B8197433 : Blo 2273435 8197433 := bstep (se 2 (by rfl) ⟨3074037, by rfl⟩ : syracuseStep 8197433 = 6148075) B6148075
theorem B5464955 : Blo 2273435 5464955 := bstep (se 1 (by rfl) ⟨4098716, by rfl⟩ : syracuseStep 5464955 = 8197433) B8197433
theorem B3643303 : Blo 2273435 3643303 := bstep (se 1 (by rfl) ⟨2732477, by rfl⟩ : syracuseStep 3643303 = 5464955) B5464955
theorem B4857737 : Blo 2273435 4857737 := bstep (se 2 (by rfl) ⟨1821651, by rfl⟩ : syracuseStep 4857737 = 3643303) B3643303
theorem B12953965 : Blo 2273435 12953965 := bstep (se 3 (by rfl) ⟨2428868, by rfl⟩ : syracuseStep 12953965 = 4857737) B4857737
theorem B17271953 : Blo 2273435 17271953 := bstep (se 2 (by rfl) ⟨6476982, by rfl⟩ : syracuseStep 17271953 = 12953965) B12953965
theorem B11514635 : Blo 2273435 11514635 := bstep (se 1 (by rfl) ⟨8635976, by rfl⟩ : syracuseStep 11514635 = 17271953) B17271953
theorem B7676423 : Blo 2273435 7676423 := bstep (se 1 (by rfl) ⟨5757317, by rfl⟩ : syracuseStep 7676423 = 11514635) B11514635
theorem B5117615 : Blo 2273435 5117615 := bstep (se 1 (by rfl) ⟨3838211, by rfl⟩ : syracuseStep 5117615 = 7676423) B7676423
theorem B3411743 : Blo 2273435 3411743 := bstep (se 1 (by rfl) ⟨2558807, by rfl⟩ : syracuseStep 3411743 = 5117615) B5117615
theorem B2274495 : Blo 2273435 2274495 := bstep (se 1 (by rfl) ⟨1705871, by rfl⟩ : syracuseStep 2274495 = 3411743) B3411743
theorem B3411749 : Blo 2273435 3411749 := bbase (se 4 (by rfl) ⟨319851, by rfl⟩ : syracuseStep 3411749 = 639703) (by norm_num)
theorem B2274499 : Blo 2273435 2274499 := bstep (se 1 (by rfl) ⟨1705874, by rfl⟩ : syracuseStep 2274499 = 3411749) B3411749
theorem B2878669 : Blo 2273435 2878669 := bbase (se 3 (by rfl) ⟨539750, by rfl⟩ : syracuseStep 2878669 = 1079501) (by norm_num)
theorem B3838225 : Blo 2273435 3838225 := bstep (se 2 (by rfl) ⟨1439334, by rfl⟩ : syracuseStep 3838225 = 2878669) B2878669
theorem B5117633 : Blo 2273435 5117633 := bstep (se 2 (by rfl) ⟨1919112, by rfl⟩ : syracuseStep 5117633 = 3838225) B3838225
theorem B3411755 : Blo 2273435 3411755 := bstep (se 1 (by rfl) ⟨2558816, by rfl⟩ : syracuseStep 3411755 = 5117633) B5117633
theorem B2274503 : Blo 2273435 2274503 := bstep (se 1 (by rfl) ⟨1705877, by rfl⟩ : syracuseStep 2274503 = 3411755) B3411755
theorem B2558821 : Blo 2273435 2558821 := bbase (se 4 (by rfl) ⟨239889, by rfl⟩ : syracuseStep 2558821 = 479779) (by norm_num)
theorem B3411761 : Blo 2273435 3411761 := bstep (se 2 (by rfl) ⟨1279410, by rfl⟩ : syracuseStep 3411761 = 2558821) B2558821
theorem B2274507 : Blo 2273435 2274507 := bstep (se 1 (by rfl) ⟨1705880, by rfl⟩ : syracuseStep 2274507 = 3411761) B3411761
theorem B6477029 : Blo 2273435 6477029 := bbase (se 4 (by rfl) ⟨607221, by rfl⟩ : syracuseStep 6477029 = 1214443) (by norm_num)
theorem B4318019 : Blo 2273435 4318019 := bstep (se 1 (by rfl) ⟨3238514, by rfl⟩ : syracuseStep 4318019 = 6477029) B6477029
theorem B2878679 : Blo 2273435 2878679 := bstep (se 1 (by rfl) ⟨2159009, by rfl⟩ : syracuseStep 2878679 = 4318019) B4318019
theorem B7676477 : Blo 2273435 7676477 := bstep (se 3 (by rfl) ⟨1439339, by rfl⟩ : syracuseStep 7676477 = 2878679) B2878679
theorem B5117651 : Blo 2273435 5117651 := bstep (se 1 (by rfl) ⟨3838238, by rfl⟩ : syracuseStep 5117651 = 7676477) B7676477
theorem B3411767 : Blo 2273435 3411767 := bstep (se 1 (by rfl) ⟨2558825, by rfl⟩ : syracuseStep 3411767 = 5117651) B5117651
theorem B2274511 : Blo 2273435 2274511 := bstep (se 1 (by rfl) ⟨1705883, by rfl⟩ : syracuseStep 2274511 = 3411767) B3411767
theorem B3411773 : Blo 2273435 3411773 := bbase (se 3 (by rfl) ⟨639707, by rfl⟩ : syracuseStep 3411773 = 1279415) (by norm_num)
theorem B2274515 : Blo 2273435 2274515 := bstep (se 1 (by rfl) ⟨1705886, by rfl⟩ : syracuseStep 2274515 = 3411773) B3411773
theorem B5117669 : Blo 2273435 5117669 := bbase (se 4 (by rfl) ⟨479781, by rfl⟩ : syracuseStep 5117669 = 959563) (by norm_num)
theorem B3411779 : Blo 2273435 3411779 := bstep (se 1 (by rfl) ⟨2558834, by rfl⟩ : syracuseStep 3411779 = 5117669) B5117669
theorem B2274519 : Blo 2273435 2274519 := bstep (se 1 (by rfl) ⟨1705889, by rfl⟩ : syracuseStep 2274519 = 3411779) B3411779
theorem B5757389 : Blo 2273435 5757389 := bbase (se 3 (by rfl) ⟨1079510, by rfl⟩ : syracuseStep 5757389 = 2159021) (by norm_num)
theorem B3838259 : Blo 2273435 3838259 := bstep (se 1 (by rfl) ⟨2878694, by rfl⟩ : syracuseStep 3838259 = 5757389) B5757389
theorem B2558839 : Blo 2273435 2558839 := bstep (se 1 (by rfl) ⟨1919129, by rfl⟩ : syracuseStep 2558839 = 3838259) B3838259
theorem B3411785 : Blo 2273435 3411785 := bstep (se 2 (by rfl) ⟨1279419, by rfl⟩ : syracuseStep 3411785 = 2558839) B2558839
theorem B2274523 : Blo 2273435 2274523 := bstep (se 1 (by rfl) ⟨1705892, by rfl⟩ : syracuseStep 2274523 = 3411785) B3411785
theorem B9222245 : Blo 2273435 9222245 := bbase (se 4 (by rfl) ⟨864585, by rfl⟩ : syracuseStep 9222245 = 1729171) (by norm_num)
theorem B6148163 : Blo 2273435 6148163 := bstep (se 1 (by rfl) ⟨4611122, by rfl⟩ : syracuseStep 6148163 = 9222245) B9222245
theorem B4098775 : Blo 2273435 4098775 := bstep (se 1 (by rfl) ⟨3074081, by rfl⟩ : syracuseStep 4098775 = 6148163) B6148163
theorem B5465033 : Blo 2273435 5465033 := bstep (se 2 (by rfl) ⟨2049387, by rfl⟩ : syracuseStep 5465033 = 4098775) B4098775
theorem B3643355 : Blo 2273435 3643355 := bstep (se 1 (by rfl) ⟨2732516, by rfl⟩ : syracuseStep 3643355 = 5465033) B5465033
theorem B2428903 : Blo 2273435 2428903 := bstep (se 1 (by rfl) ⟨1821677, by rfl⟩ : syracuseStep 2428903 = 3643355) B3643355
theorem B3238537 : Blo 2273435 3238537 := bstep (se 2 (by rfl) ⟨1214451, by rfl⟩ : syracuseStep 3238537 = 2428903) B2428903
theorem B4318049 : Blo 2273435 4318049 := bstep (se 2 (by rfl) ⟨1619268, by rfl⟩ : syracuseStep 4318049 = 3238537) B3238537
theorem B11514797 : Blo 2273435 11514797 := bstep (se 3 (by rfl) ⟨2159024, by rfl⟩ : syracuseStep 11514797 = 4318049) B4318049
theorem B7676531 : Blo 2273435 7676531 := bstep (se 1 (by rfl) ⟨5757398, by rfl⟩ : syracuseStep 7676531 = 11514797) B11514797
theorem B5117687 : Blo 2273435 5117687 := bstep (se 1 (by rfl) ⟨3838265, by rfl⟩ : syracuseStep 5117687 = 7676531) B7676531
theorem B3411791 : Blo 2273435 3411791 := bstep (se 1 (by rfl) ⟨2558843, by rfl⟩ : syracuseStep 3411791 = 5117687) B5117687
theorem B2274527 : Blo 2273435 2274527 := bstep (se 1 (by rfl) ⟨1705895, by rfl⟩ : syracuseStep 2274527 = 3411791) B3411791
theorem B3411797 : Blo 2273435 3411797 := bbase (se 9 (by rfl) ⟨9995, by rfl⟩ : syracuseStep 3411797 = 19991) (by norm_num)
theorem B2274531 : Blo 2273435 2274531 := bstep (se 1 (by rfl) ⟨1705898, by rfl⟩ : syracuseStep 2274531 = 3411797) B3411797
theorem B2593765 : Blo 2273435 2593765 := bbase (se 4 (by rfl) ⟨243165, by rfl⟩ : syracuseStep 2593765 = 486331) (by norm_num)
theorem B13833413 : Blo 2273435 13833413 := bstep (se 4 (by rfl) ⟨1296882, by rfl⟩ : syracuseStep 13833413 = 2593765) B2593765
theorem B9222275 : Blo 2273435 9222275 := bstep (se 1 (by rfl) ⟨6916706, by rfl⟩ : syracuseStep 9222275 = 13833413) B13833413
theorem B24592733 : Blo 2273435 24592733 := bstep (se 3 (by rfl) ⟨4611137, by rfl⟩ : syracuseStep 24592733 = 9222275) B9222275
theorem B16395155 : Blo 2273435 16395155 := bstep (se 1 (by rfl) ⟨12296366, by rfl⟩ : syracuseStep 16395155 = 24592733) B24592733
theorem B10930103 : Blo 2273435 10930103 := bstep (se 1 (by rfl) ⟨8197577, by rfl⟩ : syracuseStep 10930103 = 16395155) B16395155
theorem B7286735 : Blo 2273435 7286735 := bstep (se 1 (by rfl) ⟨5465051, by rfl⟩ : syracuseStep 7286735 = 10930103) B10930103
theorem B4857823 : Blo 2273435 4857823 := bstep (se 1 (by rfl) ⟨3643367, by rfl⟩ : syracuseStep 4857823 = 7286735) B7286735
theorem B6477097 : Blo 2273435 6477097 := bstep (se 2 (by rfl) ⟨2428911, by rfl⟩ : syracuseStep 6477097 = 4857823) B4857823
theorem B8636129 : Blo 2273435 8636129 := bstep (se 2 (by rfl) ⟨3238548, by rfl⟩ : syracuseStep 8636129 = 6477097) B6477097
theorem B5757419 : Blo 2273435 5757419 := bstep (se 1 (by rfl) ⟨4318064, by rfl⟩ : syracuseStep 5757419 = 8636129) B8636129
theorem B3838279 : Blo 2273435 3838279 := bstep (se 1 (by rfl) ⟨2878709, by rfl⟩ : syracuseStep 3838279 = 5757419) B5757419
theorem B5117705 : Blo 2273435 5117705 := bstep (se 2 (by rfl) ⟨1919139, by rfl⟩ : syracuseStep 5117705 = 3838279) B3838279
theorem B3411803 : Blo 2273435 3411803 := bstep (se 1 (by rfl) ⟨2558852, by rfl⟩ : syracuseStep 3411803 = 5117705) B5117705
theorem B2274535 : Blo 2273435 2274535 := bstep (se 1 (by rfl) ⟨1705901, by rfl⟩ : syracuseStep 2274535 = 3411803) B3411803
theorem B2558857 : Blo 2273435 2558857 := bbase (se 2 (by rfl) ⟨959571, by rfl⟩ : syracuseStep 2558857 = 1919143) (by norm_num)
theorem B3411809 : Blo 2273435 3411809 := bstep (se 2 (by rfl) ⟨1279428, by rfl⟩ : syracuseStep 3411809 = 2558857) B2558857
theorem B2274539 : Blo 2273435 2274539 := bstep (se 1 (by rfl) ⟨1705904, by rfl⟩ : syracuseStep 2274539 = 3411809) B3411809
theorem B4924117 : Blo 2273435 4924117 := bbase (se 7 (by rfl) ⟨57704, by rfl⟩ : syracuseStep 4924117 = 115409) (by norm_num)
theorem B26261957 : Blo 2273435 26261957 := bstep (se 4 (by rfl) ⟨2462058, by rfl⟩ : syracuseStep 26261957 = 4924117) B4924117
theorem B17507971 : Blo 2273435 17507971 := bstep (se 1 (by rfl) ⟨13130978, by rfl⟩ : syracuseStep 17507971 = 26261957) B26261957
theorem B93375845 : Blo 2273435 93375845 := bstep (se 4 (by rfl) ⟨8753985, by rfl⟩ : syracuseStep 93375845 = 17507971) B17507971
theorem B62250563 : Blo 2273435 62250563 := bstep (se 1 (by rfl) ⟨46687922, by rfl⟩ : syracuseStep 62250563 = 93375845) B93375845
theorem B166001501 : Blo 2273435 166001501 := bstep (se 3 (by rfl) ⟨31125281, by rfl⟩ : syracuseStep 166001501 = 62250563) B62250563
theorem B110667667 : Blo 2273435 110667667 := bstep (se 1 (by rfl) ⟨83000750, by rfl⟩ : syracuseStep 110667667 = 166001501) B166001501
theorem B147556889 : Blo 2273435 147556889 := bstep (se 2 (by rfl) ⟨55333833, by rfl⟩ : syracuseStep 147556889 = 110667667) B110667667
theorem B98371259 : Blo 2273435 98371259 := bstep (se 1 (by rfl) ⟨73778444, by rfl⟩ : syracuseStep 98371259 = 147556889) B147556889
theorem B65580839 : Blo 2273435 65580839 := bstep (se 1 (by rfl) ⟨49185629, by rfl⟩ : syracuseStep 65580839 = 98371259) B98371259
theorem B43720559 : Blo 2273435 43720559 := bstep (se 1 (by rfl) ⟨32790419, by rfl⟩ : syracuseStep 43720559 = 65580839) B65580839
theorem B29147039 : Blo 2273435 29147039 := bstep (se 1 (by rfl) ⟨21860279, by rfl⟩ : syracuseStep 29147039 = 43720559) B43720559
theorem B19431359 : Blo 2273435 19431359 := bstep (se 1 (by rfl) ⟨14573519, by rfl⟩ : syracuseStep 19431359 = 29147039) B29147039
theorem B12954239 : Blo 2273435 12954239 := bstep (se 1 (by rfl) ⟨9715679, by rfl⟩ : syracuseStep 12954239 = 19431359) B19431359
theorem B8636159 : Blo 2273435 8636159 := bstep (se 1 (by rfl) ⟨6477119, by rfl⟩ : syracuseStep 8636159 = 12954239) B12954239
theorem B5757439 : Blo 2273435 5757439 := bstep (se 1 (by rfl) ⟨4318079, by rfl⟩ : syracuseStep 5757439 = 8636159) B8636159
theorem B7676585 : Blo 2273435 7676585 := bstep (se 2 (by rfl) ⟨2878719, by rfl⟩ : syracuseStep 7676585 = 5757439) B5757439
theorem B5117723 : Blo 2273435 5117723 := bstep (se 1 (by rfl) ⟨3838292, by rfl⟩ : syracuseStep 5117723 = 7676585) B7676585
theorem B3411815 : Blo 2273435 3411815 := bstep (se 1 (by rfl) ⟨2558861, by rfl⟩ : syracuseStep 3411815 = 5117723) B5117723
theorem B2274543 : Blo 2273435 2274543 := bstep (se 1 (by rfl) ⟨1705907, by rfl⟩ : syracuseStep 2274543 = 3411815) B3411815
theorem B3411821 : Blo 2273435 3411821 := bbase (se 3 (by rfl) ⟨639716, by rfl⟩ : syracuseStep 3411821 = 1279433) (by norm_num)
theorem B2274547 : Blo 2273435 2274547 := bstep (se 1 (by rfl) ⟨1705910, by rfl⟩ : syracuseStep 2274547 = 3411821) B3411821
theorem B5117741 : Blo 2273435 5117741 := bbase (se 3 (by rfl) ⟨959576, by rfl⟩ : syracuseStep 5117741 = 1919153) (by norm_num)
theorem B3411827 : Blo 2273435 3411827 := bstep (se 1 (by rfl) ⟨2558870, by rfl⟩ : syracuseStep 3411827 = 5117741) B5117741
theorem B2274551 : Blo 2273435 2274551 := bstep (se 1 (by rfl) ⟨1705913, by rfl⟩ : syracuseStep 2274551 = 3411827) B3411827
theorem B9715733 : Blo 2273435 9715733 := bbase (se 6 (by rfl) ⟨227712, by rfl⟩ : syracuseStep 9715733 = 455425) (by norm_num)
theorem B6477155 : Blo 2273435 6477155 := bstep (se 1 (by rfl) ⟨4857866, by rfl⟩ : syracuseStep 6477155 = 9715733) B9715733
theorem B4318103 : Blo 2273435 4318103 := bstep (se 1 (by rfl) ⟨3238577, by rfl⟩ : syracuseStep 4318103 = 6477155) B6477155
theorem B2878735 : Blo 2273435 2878735 := bstep (se 1 (by rfl) ⟨2159051, by rfl⟩ : syracuseStep 2878735 = 4318103) B4318103
theorem B3838313 : Blo 2273435 3838313 := bstep (se 2 (by rfl) ⟨1439367, by rfl⟩ : syracuseStep 3838313 = 2878735) B2878735
theorem B2558875 : Blo 2273435 2558875 := bstep (se 1 (by rfl) ⟨1919156, by rfl⟩ : syracuseStep 2558875 = 3838313) B3838313
theorem B3411833 : Blo 2273435 3411833 := bstep (se 2 (by rfl) ⟨1279437, by rfl⟩ : syracuseStep 3411833 = 2558875) B2558875
theorem B2274555 : Blo 2273435 2274555 := bstep (se 1 (by rfl) ⟨1705916, by rfl⟩ : syracuseStep 2274555 = 3411833) B3411833
theorem B14573621 : Blo 2273435 14573621 := bbase (se 5 (by rfl) ⟨683138, by rfl⟩ : syracuseStep 14573621 = 1366277) (by norm_num)
theorem B38862989 : Blo 2273435 38862989 := bstep (se 3 (by rfl) ⟨7286810, by rfl⟩ : syracuseStep 38862989 = 14573621) B14573621
theorem B25908659 : Blo 2273435 25908659 := bstep (se 1 (by rfl) ⟨19431494, by rfl⟩ : syracuseStep 25908659 = 38862989) B38862989
theorem B17272439 : Blo 2273435 17272439 := bstep (se 1 (by rfl) ⟨12954329, by rfl⟩ : syracuseStep 17272439 = 25908659) B25908659
theorem B11514959 : Blo 2273435 11514959 := bstep (se 1 (by rfl) ⟨8636219, by rfl⟩ : syracuseStep 11514959 = 17272439) B17272439
theorem B7676639 : Blo 2273435 7676639 := bstep (se 1 (by rfl) ⟨5757479, by rfl⟩ : syracuseStep 7676639 = 11514959) B11514959
theorem B5117759 : Blo 2273435 5117759 := bstep (se 1 (by rfl) ⟨3838319, by rfl⟩ : syracuseStep 5117759 = 7676639) B7676639
theorem B3411839 : Blo 2273435 3411839 := bstep (se 1 (by rfl) ⟨2558879, by rfl⟩ : syracuseStep 3411839 = 5117759) B5117759
theorem B2274559 : Blo 2273435 2274559 := bstep (se 1 (by rfl) ⟨1705919, by rfl⟩ : syracuseStep 2274559 = 3411839) B3411839
theorem B3411845 : Blo 2273435 3411845 := bbase (se 4 (by rfl) ⟨319860, by rfl⟩ : syracuseStep 3411845 = 639721) (by norm_num)
theorem B2274563 : Blo 2273435 2274563 := bstep (se 1 (by rfl) ⟨1705922, by rfl⟩ : syracuseStep 2274563 = 3411845) B3411845
theorem B3838333 : Blo 2273435 3838333 := bbase (se 3 (by rfl) ⟨719687, by rfl⟩ : syracuseStep 3838333 = 1439375) (by norm_num)
theorem B5117777 : Blo 2273435 5117777 := bstep (se 2 (by rfl) ⟨1919166, by rfl⟩ : syracuseStep 5117777 = 3838333) B3838333
theorem B3411851 : Blo 2273435 3411851 := bstep (se 1 (by rfl) ⟨2558888, by rfl⟩ : syracuseStep 3411851 = 5117777) B5117777
theorem B2274567 : Blo 2273435 2274567 := bstep (se 1 (by rfl) ⟨1705925, by rfl⟩ : syracuseStep 2274567 = 3411851) B3411851
theorem B2558893 : Blo 2273435 2558893 := bbase (se 3 (by rfl) ⟨479792, by rfl⟩ : syracuseStep 2558893 = 959585) (by norm_num)
theorem B3411857 : Blo 2273435 3411857 := bstep (se 2 (by rfl) ⟨1279446, by rfl⟩ : syracuseStep 3411857 = 2558893) B2558893
theorem B2274571 : Blo 2273435 2274571 := bstep (se 1 (by rfl) ⟨1705928, by rfl⟩ : syracuseStep 2274571 = 3411857) B3411857
theorem B7676693 : Blo 2273435 7676693 := bbase (se 6 (by rfl) ⟨179922, by rfl⟩ : syracuseStep 7676693 = 359845) (by norm_num)
theorem B5117795 : Blo 2273435 5117795 := bstep (se 1 (by rfl) ⟨3838346, by rfl⟩ : syracuseStep 5117795 = 7676693) B7676693
theorem B3411863 : Blo 2273435 3411863 := bstep (se 1 (by rfl) ⟨2558897, by rfl⟩ : syracuseStep 3411863 = 5117795) B5117795
theorem B2274575 : Blo 2273435 2274575 := bstep (se 1 (by rfl) ⟨1705931, by rfl⟩ : syracuseStep 2274575 = 3411863) B3411863
theorem B3411869 : Blo 2273435 3411869 := bbase (se 3 (by rfl) ⟨639725, by rfl⟩ : syracuseStep 3411869 = 1279451) (by norm_num)
theorem B2274579 : Blo 2273435 2274579 := bstep (se 1 (by rfl) ⟨1705934, by rfl⟩ : syracuseStep 2274579 = 3411869) B3411869
theorem B5117813 : Blo 2273435 5117813 := bbase (se 5 (by rfl) ⟨239897, by rfl⟩ : syracuseStep 5117813 = 479795) (by norm_num)
theorem B3411875 : Blo 2273435 3411875 := bstep (se 1 (by rfl) ⟨2558906, by rfl⟩ : syracuseStep 3411875 = 5117813) B5117813
theorem B2274583 : Blo 2273435 2274583 := bstep (se 1 (by rfl) ⟨1705937, by rfl⟩ : syracuseStep 2274583 = 3411875) B3411875
theorem B5258429 : Blo 2273435 5258429 := bbase (se 3 (by rfl) ⟨985955, by rfl⟩ : syracuseStep 5258429 = 1971911) (by norm_num)
theorem B3505619 : Blo 2273435 3505619 := bstep (se 1 (by rfl) ⟨2629214, by rfl⟩ : syracuseStep 3505619 = 5258429) B5258429
theorem B9348317 : Blo 2273435 9348317 := bstep (se 3 (by rfl) ⟨1752809, by rfl⟩ : syracuseStep 9348317 = 3505619) B3505619
theorem B6232211 : Blo 2273435 6232211 := bstep (se 1 (by rfl) ⟨4674158, by rfl⟩ : syracuseStep 6232211 = 9348317) B9348317
theorem B4154807 : Blo 2273435 4154807 := bstep (se 1 (by rfl) ⟨3116105, by rfl⟩ : syracuseStep 4154807 = 6232211) B6232211
theorem B2769871 : Blo 2273435 2769871 := bstep (se 1 (by rfl) ⟨2077403, by rfl⟩ : syracuseStep 2769871 = 4154807) B4154807
theorem B3693161 : Blo 2273435 3693161 := bstep (se 2 (by rfl) ⟨1384935, by rfl⟩ : syracuseStep 3693161 = 2769871) B2769871
theorem B2462107 : Blo 2273435 2462107 := bstep (se 1 (by rfl) ⟨1846580, by rfl⟩ : syracuseStep 2462107 = 3693161) B3693161
theorem B3282809 : Blo 2273435 3282809 := bstep (se 2 (by rfl) ⟨1231053, by rfl⟩ : syracuseStep 3282809 = 2462107) B2462107
theorem B8754157 : Blo 2273435 8754157 := bstep (se 3 (by rfl) ⟨1641404, by rfl⟩ : syracuseStep 8754157 = 3282809) B3282809
theorem B11672209 : Blo 2273435 11672209 := bstep (se 2 (by rfl) ⟨4377078, by rfl⟩ : syracuseStep 11672209 = 8754157) B8754157
theorem B15562945 : Blo 2273435 15562945 := bstep (se 2 (by rfl) ⟨5836104, by rfl⟩ : syracuseStep 15562945 = 11672209) B11672209
theorem B20750593 : Blo 2273435 20750593 := bstep (se 2 (by rfl) ⟨7781472, by rfl⟩ : syracuseStep 20750593 = 15562945) B15562945
theorem B27667457 : Blo 2273435 27667457 := bstep (se 2 (by rfl) ⟨10375296, by rfl⟩ : syracuseStep 27667457 = 20750593) B20750593
theorem B18444971 : Blo 2273435 18444971 := bstep (se 1 (by rfl) ⟨13833728, by rfl⟩ : syracuseStep 18444971 = 27667457) B27667457
theorem B12296647 : Blo 2273435 12296647 := bstep (se 1 (by rfl) ⟨9222485, by rfl⟩ : syracuseStep 12296647 = 18444971) B18444971
theorem B16395529 : Blo 2273435 16395529 := bstep (se 2 (by rfl) ⟨6148323, by rfl⟩ : syracuseStep 16395529 = 12296647) B12296647
theorem B21860705 : Blo 2273435 21860705 := bstep (se 2 (by rfl) ⟨8197764, by rfl⟩ : syracuseStep 21860705 = 16395529) B16395529
theorem B14573803 : Blo 2273435 14573803 := bstep (se 1 (by rfl) ⟨10930352, by rfl⟩ : syracuseStep 14573803 = 21860705) B21860705
theorem B19431737 : Blo 2273435 19431737 := bstep (se 2 (by rfl) ⟨7286901, by rfl⟩ : syracuseStep 19431737 = 14573803) B14573803
theorem B12954491 : Blo 2273435 12954491 := bstep (se 1 (by rfl) ⟨9715868, by rfl⟩ : syracuseStep 12954491 = 19431737) B19431737
theorem B8636327 : Blo 2273435 8636327 := bstep (se 1 (by rfl) ⟨6477245, by rfl⟩ : syracuseStep 8636327 = 12954491) B12954491
theorem B5757551 : Blo 2273435 5757551 := bstep (se 1 (by rfl) ⟨4318163, by rfl⟩ : syracuseStep 5757551 = 8636327) B8636327
theorem B3838367 : Blo 2273435 3838367 := bstep (se 1 (by rfl) ⟨2878775, by rfl⟩ : syracuseStep 3838367 = 5757551) B5757551
theorem B2558911 : Blo 2273435 2558911 := bstep (se 1 (by rfl) ⟨1919183, by rfl⟩ : syracuseStep 2558911 = 3838367) B3838367
theorem B3411881 : Blo 2273435 3411881 := bstep (se 2 (by rfl) ⟨1279455, by rfl⟩ : syracuseStep 3411881 = 2558911) B2558911
theorem B2274587 : Blo 2273435 2274587 := bstep (se 1 (by rfl) ⟨1705940, by rfl⟩ : syracuseStep 2274587 = 3411881) B3411881
theorem B8636341 : Blo 2273435 8636341 := bbase (se 5 (by rfl) ⟨404828, by rfl⟩ : syracuseStep 8636341 = 809657) (by norm_num)
theorem B11515121 : Blo 2273435 11515121 := bstep (se 2 (by rfl) ⟨4318170, by rfl⟩ : syracuseStep 11515121 = 8636341) B8636341
theorem B7676747 : Blo 2273435 7676747 := bstep (se 1 (by rfl) ⟨5757560, by rfl⟩ : syracuseStep 7676747 = 11515121) B11515121
theorem B5117831 : Blo 2273435 5117831 := bstep (se 1 (by rfl) ⟨3838373, by rfl⟩ : syracuseStep 5117831 = 7676747) B7676747
theorem B3411887 : Blo 2273435 3411887 := bstep (se 1 (by rfl) ⟨2558915, by rfl⟩ : syracuseStep 3411887 = 5117831) B5117831
theorem B2274591 : Blo 2273435 2274591 := bstep (se 1 (by rfl) ⟨1705943, by rfl⟩ : syracuseStep 2274591 = 3411887) B3411887
theorem B3411893 : Blo 2273435 3411893 := bbase (se 5 (by rfl) ⟨159932, by rfl⟩ : syracuseStep 3411893 = 319865) (by norm_num)
theorem B2274595 : Blo 2273435 2274595 := bstep (se 1 (by rfl) ⟨1705946, by rfl⟩ : syracuseStep 2274595 = 3411893) B3411893
theorem B5757581 : Blo 2273435 5757581 := bbase (se 3 (by rfl) ⟨1079546, by rfl⟩ : syracuseStep 5757581 = 2159093) (by norm_num)
theorem B3838387 : Blo 2273435 3838387 := bstep (se 1 (by rfl) ⟨2878790, by rfl⟩ : syracuseStep 3838387 = 5757581) B5757581
theorem B5117849 : Blo 2273435 5117849 := bstep (se 2 (by rfl) ⟨1919193, by rfl⟩ : syracuseStep 5117849 = 3838387) B3838387
theorem B3411899 : Blo 2273435 3411899 := bstep (se 1 (by rfl) ⟨2558924, by rfl⟩ : syracuseStep 3411899 = 5117849) B5117849
theorem B2274599 : Blo 2273435 2274599 := bstep (se 1 (by rfl) ⟨1705949, by rfl⟩ : syracuseStep 2274599 = 3411899) B3411899
theorem B2558929 : Blo 2273435 2558929 := bbase (se 2 (by rfl) ⟨959598, by rfl⟩ : syracuseStep 2558929 = 1919197) (by norm_num)
theorem B3411905 : Blo 2273435 3411905 := bstep (se 2 (by rfl) ⟨1279464, by rfl⟩ : syracuseStep 3411905 = 2558929) B2558929
theorem B2274603 : Blo 2273435 2274603 := bstep (se 1 (by rfl) ⟨1705952, by rfl⟩ : syracuseStep 2274603 = 3411905) B3411905
theorem B2629237 : Blo 2273435 2629237 := bbase (se 5 (by rfl) ⟨123245, by rfl⟩ : syracuseStep 2629237 = 246491) (by norm_num)
theorem B3505649 : Blo 2273435 3505649 := bstep (se 2 (by rfl) ⟨1314618, by rfl⟩ : syracuseStep 3505649 = 2629237) B2629237
theorem B37393589 : Blo 2273435 37393589 := bstep (se 5 (by rfl) ⟨1752824, by rfl⟩ : syracuseStep 37393589 = 3505649) B3505649
theorem B24929059 : Blo 2273435 24929059 := bstep (se 1 (by rfl) ⟨18696794, by rfl⟩ : syracuseStep 24929059 = 37393589) B37393589
theorem B33238745 : Blo 2273435 33238745 := bstep (se 2 (by rfl) ⟨12464529, by rfl⟩ : syracuseStep 33238745 = 24929059) B24929059
theorem B22159163 : Blo 2273435 22159163 := bstep (se 1 (by rfl) ⟨16619372, by rfl⟩ : syracuseStep 22159163 = 33238745) B33238745
theorem B14772775 : Blo 2273435 14772775 := bstep (se 1 (by rfl) ⟨11079581, by rfl⟩ : syracuseStep 14772775 = 22159163) B22159163
theorem B19697033 : Blo 2273435 19697033 := bstep (se 2 (by rfl) ⟨7386387, by rfl⟩ : syracuseStep 19697033 = 14772775) B14772775
theorem B52525421 : Blo 2273435 52525421 := bstep (se 3 (by rfl) ⟨9848516, by rfl⟩ : syracuseStep 52525421 = 19697033) B19697033
theorem B35016947 : Blo 2273435 35016947 := bstep (se 1 (by rfl) ⟨26262710, by rfl⟩ : syracuseStep 35016947 = 52525421) B52525421
theorem B23344631 : Blo 2273435 23344631 := bstep (se 1 (by rfl) ⟨17508473, by rfl⟩ : syracuseStep 23344631 = 35016947) B35016947
theorem B15563087 : Blo 2273435 15563087 := bstep (se 1 (by rfl) ⟨11672315, by rfl⟩ : syracuseStep 15563087 = 23344631) B23344631
theorem B10375391 : Blo 2273435 10375391 := bstep (se 1 (by rfl) ⟨7781543, by rfl⟩ : syracuseStep 10375391 = 15563087) B15563087
theorem B6916927 : Blo 2273435 6916927 := bstep (se 1 (by rfl) ⟨5187695, by rfl⟩ : syracuseStep 6916927 = 10375391) B10375391
theorem B9222569 : Blo 2273435 9222569 := bstep (se 2 (by rfl) ⟨3458463, by rfl⟩ : syracuseStep 9222569 = 6916927) B6916927
theorem B6148379 : Blo 2273435 6148379 := bstep (se 1 (by rfl) ⟨4611284, by rfl⟩ : syracuseStep 6148379 = 9222569) B9222569
theorem B4098919 : Blo 2273435 4098919 := bstep (se 1 (by rfl) ⟨3074189, by rfl⟩ : syracuseStep 4098919 = 6148379) B6148379
theorem B5465225 : Blo 2273435 5465225 := bstep (se 2 (by rfl) ⟨2049459, by rfl⟩ : syracuseStep 5465225 = 4098919) B4098919
theorem B3643483 : Blo 2273435 3643483 := bstep (se 1 (by rfl) ⟨2732612, by rfl⟩ : syracuseStep 3643483 = 5465225) B5465225
theorem B4857977 : Blo 2273435 4857977 := bstep (se 2 (by rfl) ⟨1821741, by rfl⟩ : syracuseStep 4857977 = 3643483) B3643483
theorem B3238651 : Blo 2273435 3238651 := bstep (se 1 (by rfl) ⟨2428988, by rfl⟩ : syracuseStep 3238651 = 4857977) B4857977
theorem B4318201 : Blo 2273435 4318201 := bstep (se 2 (by rfl) ⟨1619325, by rfl⟩ : syracuseStep 4318201 = 3238651) B3238651
theorem B5757601 : Blo 2273435 5757601 := bstep (se 2 (by rfl) ⟨2159100, by rfl⟩ : syracuseStep 5757601 = 4318201) B4318201
theorem B7676801 : Blo 2273435 7676801 := bstep (se 2 (by rfl) ⟨2878800, by rfl⟩ : syracuseStep 7676801 = 5757601) B5757601
theorem B5117867 : Blo 2273435 5117867 := bstep (se 1 (by rfl) ⟨3838400, by rfl⟩ : syracuseStep 5117867 = 7676801) B7676801
theorem B3411911 : Blo 2273435 3411911 := bstep (se 1 (by rfl) ⟨2558933, by rfl⟩ : syracuseStep 3411911 = 5117867) B5117867
theorem B2274607 : Blo 2273435 2274607 := bstep (se 1 (by rfl) ⟨1705955, by rfl⟩ : syracuseStep 2274607 = 3411911) B3411911
theorem B3411917 : Blo 2273435 3411917 := bbase (se 3 (by rfl) ⟨639734, by rfl⟩ : syracuseStep 3411917 = 1279469) (by norm_num)
theorem B2274611 : Blo 2273435 2274611 := bstep (se 1 (by rfl) ⟨1705958, by rfl⟩ : syracuseStep 2274611 = 3411917) B3411917
theorem B5117885 : Blo 2273435 5117885 := bbase (se 3 (by rfl) ⟨959603, by rfl⟩ : syracuseStep 5117885 = 1919207) (by norm_num)
theorem B3411923 : Blo 2273435 3411923 := bstep (se 1 (by rfl) ⟨2558942, by rfl⟩ : syracuseStep 3411923 = 5117885) B5117885
theorem B2274615 : Blo 2273435 2274615 := bstep (se 1 (by rfl) ⟨1705961, by rfl⟩ : syracuseStep 2274615 = 3411923) B3411923
theorem B3838421 : Blo 2273435 3838421 := bbase (se 7 (by rfl) ⟨44981, by rfl⟩ : syracuseStep 3838421 = 89963) (by norm_num)
theorem B2558947 : Blo 2273435 2558947 := bstep (se 1 (by rfl) ⟨1919210, by rfl⟩ : syracuseStep 2558947 = 3838421) B3838421
theorem B3411929 : Blo 2273435 3411929 := bstep (se 2 (by rfl) ⟨1279473, by rfl⟩ : syracuseStep 3411929 = 2558947) B2558947
theorem B2274619 : Blo 2273435 2274619 := bstep (se 1 (by rfl) ⟨1705964, by rfl⟩ : syracuseStep 2274619 = 3411929) B3411929
theorem B9716021 : Blo 2273435 9716021 := bbase (se 5 (by rfl) ⟨455438, by rfl⟩ : syracuseStep 9716021 = 910877) (by norm_num)
theorem B6477347 : Blo 2273435 6477347 := bstep (se 1 (by rfl) ⟨4858010, by rfl⟩ : syracuseStep 6477347 = 9716021) B9716021
theorem B17272925 : Blo 2273435 17272925 := bstep (se 3 (by rfl) ⟨3238673, by rfl⟩ : syracuseStep 17272925 = 6477347) B6477347
theorem B11515283 : Blo 2273435 11515283 := bstep (se 1 (by rfl) ⟨8636462, by rfl⟩ : syracuseStep 11515283 = 17272925) B17272925
theorem B7676855 : Blo 2273435 7676855 := bstep (se 1 (by rfl) ⟨5757641, by rfl⟩ : syracuseStep 7676855 = 11515283) B11515283
theorem B5117903 : Blo 2273435 5117903 := bstep (se 1 (by rfl) ⟨3838427, by rfl⟩ : syracuseStep 5117903 = 7676855) B7676855
theorem B3411935 : Blo 2273435 3411935 := bstep (se 1 (by rfl) ⟨2558951, by rfl⟩ : syracuseStep 3411935 = 5117903) B5117903
theorem B2274623 : Blo 2273435 2274623 := bstep (se 1 (by rfl) ⟨1705967, by rfl⟩ : syracuseStep 2274623 = 3411935) B3411935
theorem B3411941 : Blo 2273435 3411941 := bbase (se 4 (by rfl) ⟨319869, by rfl⟩ : syracuseStep 3411941 = 639739) (by norm_num)
theorem B2274627 : Blo 2273435 2274627 := bstep (se 1 (by rfl) ⟨1705970, by rfl⟩ : syracuseStep 2274627 = 3411941) B3411941
theorem B10930565 : Blo 2273435 10930565 := bbase (se 4 (by rfl) ⟨1024740, by rfl⟩ : syracuseStep 10930565 = 2049481) (by norm_num)
theorem B7287043 : Blo 2273435 7287043 := bstep (se 1 (by rfl) ⟨5465282, by rfl⟩ : syracuseStep 7287043 = 10930565) B10930565
theorem B9716057 : Blo 2273435 9716057 := bstep (se 2 (by rfl) ⟨3643521, by rfl⟩ : syracuseStep 9716057 = 7287043) B7287043
theorem B6477371 : Blo 2273435 6477371 := bstep (se 1 (by rfl) ⟨4858028, by rfl⟩ : syracuseStep 6477371 = 9716057) B9716057
theorem B4318247 : Blo 2273435 4318247 := bstep (se 1 (by rfl) ⟨3238685, by rfl⟩ : syracuseStep 4318247 = 6477371) B6477371
theorem B2878831 : Blo 2273435 2878831 := bstep (se 1 (by rfl) ⟨2159123, by rfl⟩ : syracuseStep 2878831 = 4318247) B4318247
theorem B3838441 : Blo 2273435 3838441 := bstep (se 2 (by rfl) ⟨1439415, by rfl⟩ : syracuseStep 3838441 = 2878831) B2878831
theorem B5117921 : Blo 2273435 5117921 := bstep (se 2 (by rfl) ⟨1919220, by rfl⟩ : syracuseStep 5117921 = 3838441) B3838441
theorem B3411947 : Blo 2273435 3411947 := bstep (se 1 (by rfl) ⟨2558960, by rfl⟩ : syracuseStep 3411947 = 5117921) B5117921
theorem B2274631 : Blo 2273435 2274631 := bstep (se 1 (by rfl) ⟨1705973, by rfl⟩ : syracuseStep 2274631 = 3411947) B3411947
theorem B2558965 : Blo 2273435 2558965 := bbase (se 5 (by rfl) ⟨119951, by rfl⟩ : syracuseStep 2558965 = 239903) (by norm_num)
theorem B3411953 : Blo 2273435 3411953 := bstep (se 2 (by rfl) ⟨1279482, by rfl⟩ : syracuseStep 3411953 = 2558965) B2558965
theorem B2274635 : Blo 2273435 2274635 := bstep (se 1 (by rfl) ⟨1705976, by rfl⟩ : syracuseStep 2274635 = 3411953) B3411953
theorem B2878841 : Blo 2273435 2878841 := bbase (se 2 (by rfl) ⟨1079565, by rfl⟩ : syracuseStep 2878841 = 2159131) (by norm_num)
theorem B7676909 : Blo 2273435 7676909 := bstep (se 3 (by rfl) ⟨1439420, by rfl⟩ : syracuseStep 7676909 = 2878841) B2878841
theorem B5117939 : Blo 2273435 5117939 := bstep (se 1 (by rfl) ⟨3838454, by rfl⟩ : syracuseStep 5117939 = 7676909) B7676909
theorem B3411959 : Blo 2273435 3411959 := bstep (se 1 (by rfl) ⟨2558969, by rfl⟩ : syracuseStep 3411959 = 5117939) B5117939
theorem B2274639 : Blo 2273435 2274639 := bstep (se 1 (by rfl) ⟨1705979, by rfl⟩ : syracuseStep 2274639 = 3411959) B3411959
theorem B3411965 : Blo 2273435 3411965 := bbase (se 3 (by rfl) ⟨639743, by rfl⟩ : syracuseStep 3411965 = 1279487) (by norm_num)
theorem B2274643 : Blo 2273435 2274643 := bstep (se 1 (by rfl) ⟨1705982, by rfl⟩ : syracuseStep 2274643 = 3411965) B3411965
theorem B5117957 : Blo 2273435 5117957 := bbase (se 4 (by rfl) ⟨479808, by rfl⟩ : syracuseStep 5117957 = 959617) (by norm_num)
theorem B3411971 : Blo 2273435 3411971 := bstep (se 1 (by rfl) ⟨2558978, by rfl⟩ : syracuseStep 3411971 = 5117957) B5117957
theorem B2274647 : Blo 2273435 2274647 := bstep (se 1 (by rfl) ⟨1705985, by rfl⟩ : syracuseStep 2274647 = 3411971) B3411971
theorem B4318285 : Blo 2273435 4318285 := bbase (se 3 (by rfl) ⟨809678, by rfl⟩ : syracuseStep 4318285 = 1619357) (by norm_num)
theorem B5757713 : Blo 2273435 5757713 := bstep (se 2 (by rfl) ⟨2159142, by rfl⟩ : syracuseStep 5757713 = 4318285) B4318285
theorem B3838475 : Blo 2273435 3838475 := bstep (se 1 (by rfl) ⟨2878856, by rfl⟩ : syracuseStep 3838475 = 5757713) B5757713
theorem B2558983 : Blo 2273435 2558983 := bstep (se 1 (by rfl) ⟨1919237, by rfl⟩ : syracuseStep 2558983 = 3838475) B3838475
theorem B3411977 : Blo 2273435 3411977 := bstep (se 2 (by rfl) ⟨1279491, by rfl⟩ : syracuseStep 3411977 = 2558983) B2558983
theorem B2274651 : Blo 2273435 2274651 := bstep (se 1 (by rfl) ⟨1705988, by rfl⟩ : syracuseStep 2274651 = 3411977) B3411977
theorem B11515445 : Blo 2273435 11515445 := bbase (se 5 (by rfl) ⟨539786, by rfl⟩ : syracuseStep 11515445 = 1079573) (by norm_num)
theorem B7676963 : Blo 2273435 7676963 := bstep (se 1 (by rfl) ⟨5757722, by rfl⟩ : syracuseStep 7676963 = 11515445) B11515445
theorem B5117975 : Blo 2273435 5117975 := bstep (se 1 (by rfl) ⟨3838481, by rfl⟩ : syracuseStep 5117975 = 7676963) B7676963
theorem B3411983 : Blo 2273435 3411983 := bstep (se 1 (by rfl) ⟨2558987, by rfl⟩ : syracuseStep 3411983 = 5117975) B5117975
theorem B2274655 : Blo 2273435 2274655 := bstep (se 1 (by rfl) ⟨1705991, by rfl⟩ : syracuseStep 2274655 = 3411983) B3411983
theorem B3411989 : Blo 2273435 3411989 := bbase (se 6 (by rfl) ⟨79968, by rfl⟩ : syracuseStep 3411989 = 159937) (by norm_num)
theorem B2274659 : Blo 2273435 2274659 := bstep (se 1 (by rfl) ⟨1705994, by rfl⟩ : syracuseStep 2274659 = 3411989) B3411989
theorem B4611397 : Blo 2273435 4611397 := bbase (se 4 (by rfl) ⟨432318, by rfl⟩ : syracuseStep 4611397 = 864637) (by norm_num)
theorem B6148529 : Blo 2273435 6148529 := bstep (se 2 (by rfl) ⟨2305698, by rfl⟩ : syracuseStep 6148529 = 4611397) B4611397
theorem B4099019 : Blo 2273435 4099019 := bstep (se 1 (by rfl) ⟨3074264, by rfl⟩ : syracuseStep 4099019 = 6148529) B6148529
theorem B10930717 : Blo 2273435 10930717 := bstep (se 3 (by rfl) ⟨2049509, by rfl⟩ : syracuseStep 10930717 = 4099019) B4099019
theorem B14574289 : Blo 2273435 14574289 := bstep (se 2 (by rfl) ⟨5465358, by rfl⟩ : syracuseStep 14574289 = 10930717) B10930717
theorem B19432385 : Blo 2273435 19432385 := bstep (se 2 (by rfl) ⟨7287144, by rfl⟩ : syracuseStep 19432385 = 14574289) B14574289
theorem B12954923 : Blo 2273435 12954923 := bstep (se 1 (by rfl) ⟨9716192, by rfl⟩ : syracuseStep 12954923 = 19432385) B19432385
theorem B8636615 : Blo 2273435 8636615 := bstep (se 1 (by rfl) ⟨6477461, by rfl⟩ : syracuseStep 8636615 = 12954923) B12954923
theorem B5757743 : Blo 2273435 5757743 := bstep (se 1 (by rfl) ⟨4318307, by rfl⟩ : syracuseStep 5757743 = 8636615) B8636615
theorem B3838495 : Blo 2273435 3838495 := bstep (se 1 (by rfl) ⟨2878871, by rfl⟩ : syracuseStep 3838495 = 5757743) B5757743
theorem B5117993 : Blo 2273435 5117993 := bstep (se 2 (by rfl) ⟨1919247, by rfl⟩ : syracuseStep 5117993 = 3838495) B3838495
theorem B3411995 : Blo 2273435 3411995 := bstep (se 1 (by rfl) ⟨2558996, by rfl⟩ : syracuseStep 3411995 = 5117993) B5117993
theorem B2274663 : Blo 2273435 2274663 := bstep (se 1 (by rfl) ⟨1705997, by rfl⟩ : syracuseStep 2274663 = 3411995) B3411995
theorem B2559001 : Blo 2273435 2559001 := bbase (se 2 (by rfl) ⟨959625, by rfl⟩ : syracuseStep 2559001 = 1919251) (by norm_num)
theorem B3412001 : Blo 2273435 3412001 := bstep (se 2 (by rfl) ⟨1279500, by rfl⟩ : syracuseStep 3412001 = 2559001) B2559001
theorem B2274667 : Blo 2273435 2274667 := bstep (se 1 (by rfl) ⟨1706000, by rfl⟩ : syracuseStep 2274667 = 3412001) B3412001
theorem B8636645 : Blo 2273435 8636645 := bbase (se 4 (by rfl) ⟨809685, by rfl⟩ : syracuseStep 8636645 = 1619371) (by norm_num)
theorem B5757763 : Blo 2273435 5757763 := bstep (se 1 (by rfl) ⟨4318322, by rfl⟩ : syracuseStep 5757763 = 8636645) B8636645
theorem B7677017 : Blo 2273435 7677017 := bstep (se 2 (by rfl) ⟨2878881, by rfl⟩ : syracuseStep 7677017 = 5757763) B5757763
theorem B5118011 : Blo 2273435 5118011 := bstep (se 1 (by rfl) ⟨3838508, by rfl⟩ : syracuseStep 5118011 = 7677017) B7677017
theorem B3412007 : Blo 2273435 3412007 := bstep (se 1 (by rfl) ⟨2559005, by rfl⟩ : syracuseStep 3412007 = 5118011) B5118011
theorem B2274671 : Blo 2273435 2274671 := bstep (se 1 (by rfl) ⟨1706003, by rfl⟩ : syracuseStep 2274671 = 3412007) B3412007
theorem B3412013 : Blo 2273435 3412013 := bbase (se 3 (by rfl) ⟨639752, by rfl⟩ : syracuseStep 3412013 = 1279505) (by norm_num)
theorem B2274675 : Blo 2273435 2274675 := bstep (se 1 (by rfl) ⟨1706006, by rfl⟩ : syracuseStep 2274675 = 3412013) B3412013
theorem B5118029 : Blo 2273435 5118029 := bbase (se 3 (by rfl) ⟨959630, by rfl⟩ : syracuseStep 5118029 = 1919261) (by norm_num)
theorem B3412019 : Blo 2273435 3412019 := bstep (se 1 (by rfl) ⟨2559014, by rfl⟩ : syracuseStep 3412019 = 5118029) B5118029
theorem B2274679 : Blo 2273435 2274679 := bstep (se 1 (by rfl) ⟨1706009, by rfl⟩ : syracuseStep 2274679 = 3412019) B3412019
theorem B2878897 : Blo 2273435 2878897 := bbase (se 2 (by rfl) ⟨1079586, by rfl⟩ : syracuseStep 2878897 = 2159173) (by norm_num)
theorem B3838529 : Blo 2273435 3838529 := bstep (se 2 (by rfl) ⟨1439448, by rfl⟩ : syracuseStep 3838529 = 2878897) B2878897
theorem B2559019 : Blo 2273435 2559019 := bstep (se 1 (by rfl) ⟨1919264, by rfl⟩ : syracuseStep 2559019 = 3838529) B3838529
theorem B3412025 : Blo 2273435 3412025 := bstep (se 2 (by rfl) ⟨1279509, by rfl⟩ : syracuseStep 3412025 = 2559019) B2559019
theorem B2274683 : Blo 2273435 2274683 := bstep (se 1 (by rfl) ⟨1706012, by rfl⟩ : syracuseStep 2274683 = 3412025) B3412025
theorem B7287221 : Blo 2273435 7287221 := bbase (se 5 (by rfl) ⟨341588, by rfl⟩ : syracuseStep 7287221 = 683177) (by norm_num)
theorem B4858147 : Blo 2273435 4858147 := bstep (se 1 (by rfl) ⟨3643610, by rfl⟩ : syracuseStep 4858147 = 7287221) B7287221
theorem B25910117 : Blo 2273435 25910117 := bstep (se 4 (by rfl) ⟨2429073, by rfl⟩ : syracuseStep 25910117 = 4858147) B4858147
theorem B17273411 : Blo 2273435 17273411 := bstep (se 1 (by rfl) ⟨12955058, by rfl⟩ : syracuseStep 17273411 = 25910117) B25910117
theorem B11515607 : Blo 2273435 11515607 := bstep (se 1 (by rfl) ⟨8636705, by rfl⟩ : syracuseStep 11515607 = 17273411) B17273411
theorem B7677071 : Blo 2273435 7677071 := bstep (se 1 (by rfl) ⟨5757803, by rfl⟩ : syracuseStep 7677071 = 11515607) B11515607
theorem B5118047 : Blo 2273435 5118047 := bstep (se 1 (by rfl) ⟨3838535, by rfl⟩ : syracuseStep 5118047 = 7677071) B7677071
theorem B3412031 : Blo 2273435 3412031 := bstep (se 1 (by rfl) ⟨2559023, by rfl⟩ : syracuseStep 3412031 = 5118047) B5118047
theorem B2274687 : Blo 2273435 2274687 := bstep (se 1 (by rfl) ⟨1706015, by rfl⟩ : syracuseStep 2274687 = 3412031) B3412031
theorem B3412037 : Blo 2273435 3412037 := bbase (se 4 (by rfl) ⟨319878, by rfl⟩ : syracuseStep 3412037 = 639757) (by norm_num)
theorem B2274691 : Blo 2273435 2274691 := bstep (se 1 (by rfl) ⟨1706018, by rfl⟩ : syracuseStep 2274691 = 3412037) B3412037
theorem B3838549 : Blo 2273435 3838549 := bbase (se 8 (by rfl) ⟨22491, by rfl⟩ : syracuseStep 3838549 = 44983) (by norm_num)
theorem B5118065 : Blo 2273435 5118065 := bstep (se 2 (by rfl) ⟨1919274, by rfl⟩ : syracuseStep 5118065 = 3838549) B3838549
theorem B3412043 : Blo 2273435 3412043 := bstep (se 1 (by rfl) ⟨2559032, by rfl⟩ : syracuseStep 3412043 = 5118065) B5118065
theorem B2274695 : Blo 2273435 2274695 := bstep (se 1 (by rfl) ⟨1706021, by rfl⟩ : syracuseStep 2274695 = 3412043) B3412043
theorem B2559037 : Blo 2273435 2559037 := bbase (se 3 (by rfl) ⟨479819, by rfl⟩ : syracuseStep 2559037 = 959639) (by norm_num)
theorem B3412049 : Blo 2273435 3412049 := bstep (se 2 (by rfl) ⟨1279518, by rfl⟩ : syracuseStep 3412049 = 2559037) B2559037
theorem B2274699 : Blo 2273435 2274699 := bstep (se 1 (by rfl) ⟨1706024, by rfl⟩ : syracuseStep 2274699 = 3412049) B3412049
theorem B7677125 : Blo 2273435 7677125 := bbase (se 4 (by rfl) ⟨719730, by rfl⟩ : syracuseStep 7677125 = 1439461) (by norm_num)
theorem B5118083 : Blo 2273435 5118083 := bstep (se 1 (by rfl) ⟨3838562, by rfl⟩ : syracuseStep 5118083 = 7677125) B7677125
theorem B3412055 : Blo 2273435 3412055 := bstep (se 1 (by rfl) ⟨2559041, by rfl⟩ : syracuseStep 3412055 = 5118083) B5118083
theorem B2274703 : Blo 2273435 2274703 := bstep (se 1 (by rfl) ⟨1706027, by rfl⟩ : syracuseStep 2274703 = 3412055) B3412055
theorem B3412061 : Blo 2273435 3412061 := bbase (se 3 (by rfl) ⟨639761, by rfl⟩ : syracuseStep 3412061 = 1279523) (by norm_num)
theorem B2274707 : Blo 2273435 2274707 := bstep (se 1 (by rfl) ⟨1706030, by rfl⟩ : syracuseStep 2274707 = 3412061) B3412061
theorem B5118101 : Blo 2273435 5118101 := bbase (se 6 (by rfl) ⟨119955, by rfl⟩ : syracuseStep 5118101 = 239911) (by norm_num)
theorem B3412067 : Blo 2273435 3412067 := bstep (se 1 (by rfl) ⟨2559050, by rfl⟩ : syracuseStep 3412067 = 5118101) B5118101
theorem B2274711 : Blo 2273435 2274711 := bstep (se 1 (by rfl) ⟨1706033, by rfl⟩ : syracuseStep 2274711 = 3412067) B3412067
theorem B3238805 : Blo 2273435 3238805 := bbase (se 6 (by rfl) ⟨75909, by rfl⟩ : syracuseStep 3238805 = 151819) (by norm_num)
theorem B8636813 : Blo 2273435 8636813 := bstep (se 3 (by rfl) ⟨1619402, by rfl⟩ : syracuseStep 8636813 = 3238805) B3238805
theorem B5757875 : Blo 2273435 5757875 := bstep (se 1 (by rfl) ⟨4318406, by rfl⟩ : syracuseStep 5757875 = 8636813) B8636813
theorem B3838583 : Blo 2273435 3838583 := bstep (se 1 (by rfl) ⟨2878937, by rfl⟩ : syracuseStep 3838583 = 5757875) B5757875
theorem B2559055 : Blo 2273435 2559055 := bstep (se 1 (by rfl) ⟨1919291, by rfl⟩ : syracuseStep 2559055 = 3838583) B3838583
theorem B3412073 : Blo 2273435 3412073 := bstep (se 2 (by rfl) ⟨1279527, by rfl⟩ : syracuseStep 3412073 = 2559055) B2559055
theorem B2274715 : Blo 2273435 2274715 := bstep (se 1 (by rfl) ⟨1706036, by rfl⟩ : syracuseStep 2274715 = 3412073) B3412073
theorem B11672885 : Blo 2273435 11672885 := bbase (se 5 (by rfl) ⟨547166, by rfl⟩ : syracuseStep 11672885 = 1094333) (by norm_num)
theorem B7781923 : Blo 2273435 7781923 := bstep (se 1 (by rfl) ⟨5836442, by rfl⟩ : syracuseStep 7781923 = 11672885) B11672885
theorem B41503589 : Blo 2273435 41503589 := bstep (se 4 (by rfl) ⟨3890961, by rfl⟩ : syracuseStep 41503589 = 7781923) B7781923
theorem B27669059 : Blo 2273435 27669059 := bstep (se 1 (by rfl) ⟨20751794, by rfl⟩ : syracuseStep 27669059 = 41503589) B41503589
theorem B18446039 : Blo 2273435 18446039 := bstep (se 1 (by rfl) ⟨13834529, by rfl⟩ : syracuseStep 18446039 = 27669059) B27669059
theorem B12297359 : Blo 2273435 12297359 := bstep (se 1 (by rfl) ⟨9223019, by rfl⟩ : syracuseStep 12297359 = 18446039) B18446039
theorem B32792957 : Blo 2273435 32792957 := bstep (se 3 (by rfl) ⟨6148679, by rfl⟩ : syracuseStep 32792957 = 12297359) B12297359
theorem B21861971 : Blo 2273435 21861971 := bstep (se 1 (by rfl) ⟨16396478, by rfl⟩ : syracuseStep 21861971 = 32792957) B32792957
theorem B14574647 : Blo 2273435 14574647 := bstep (se 1 (by rfl) ⟨10930985, by rfl⟩ : syracuseStep 14574647 = 21861971) B21861971
theorem B9716431 : Blo 2273435 9716431 := bstep (se 1 (by rfl) ⟨7287323, by rfl⟩ : syracuseStep 9716431 = 14574647) B14574647
theorem B12955241 : Blo 2273435 12955241 := bstep (se 2 (by rfl) ⟨4858215, by rfl⟩ : syracuseStep 12955241 = 9716431) B9716431
theorem B8636827 : Blo 2273435 8636827 := bstep (se 1 (by rfl) ⟨6477620, by rfl⟩ : syracuseStep 8636827 = 12955241) B12955241
theorem B11515769 : Blo 2273435 11515769 := bstep (se 2 (by rfl) ⟨4318413, by rfl⟩ : syracuseStep 11515769 = 8636827) B8636827
theorem B7677179 : Blo 2273435 7677179 := bstep (se 1 (by rfl) ⟨5757884, by rfl⟩ : syracuseStep 7677179 = 11515769) B11515769
theorem B5118119 : Blo 2273435 5118119 := bstep (se 1 (by rfl) ⟨3838589, by rfl⟩ : syracuseStep 5118119 = 7677179) B7677179
theorem B3412079 : Blo 2273435 3412079 := bstep (se 1 (by rfl) ⟨2559059, by rfl⟩ : syracuseStep 3412079 = 5118119) B5118119
theorem B2274719 : Blo 2273435 2274719 := bstep (se 1 (by rfl) ⟨1706039, by rfl⟩ : syracuseStep 2274719 = 3412079) B3412079
theorem B3412085 : Blo 2273435 3412085 := bbase (se 5 (by rfl) ⟨159941, by rfl⟩ : syracuseStep 3412085 = 319883) (by norm_num)
theorem B2274723 : Blo 2273435 2274723 := bstep (se 1 (by rfl) ⟨1706042, by rfl⟩ : syracuseStep 2274723 = 3412085) B3412085
theorem B4318429 : Blo 2273435 4318429 := bbase (se 3 (by rfl) ⟨809705, by rfl⟩ : syracuseStep 4318429 = 1619411) (by norm_num)
theorem B5757905 : Blo 2273435 5757905 := bstep (se 2 (by rfl) ⟨2159214, by rfl⟩ : syracuseStep 5757905 = 4318429) B4318429
theorem B3838603 : Blo 2273435 3838603 := bstep (se 1 (by rfl) ⟨2878952, by rfl⟩ : syracuseStep 3838603 = 5757905) B5757905
theorem B5118137 : Blo 2273435 5118137 := bstep (se 2 (by rfl) ⟨1919301, by rfl⟩ : syracuseStep 5118137 = 3838603) B3838603
theorem B3412091 : Blo 2273435 3412091 := bstep (se 1 (by rfl) ⟨2559068, by rfl⟩ : syracuseStep 3412091 = 5118137) B5118137
theorem B2274727 : Blo 2273435 2274727 := bstep (se 1 (by rfl) ⟨1706045, by rfl⟩ : syracuseStep 2274727 = 3412091) B3412091
theorem B2559073 : Blo 2273435 2559073 := bbase (se 2 (by rfl) ⟨959652, by rfl⟩ : syracuseStep 2559073 = 1919305) (by norm_num)
theorem B3412097 : Blo 2273435 3412097 := bstep (se 2 (by rfl) ⟨1279536, by rfl⟩ : syracuseStep 3412097 = 2559073) B2559073
theorem B2274731 : Blo 2273435 2274731 := bstep (se 1 (by rfl) ⟨1706048, by rfl⟩ : syracuseStep 2274731 = 3412097) B3412097
theorem B5757925 : Blo 2273435 5757925 := bbase (se 4 (by rfl) ⟨539805, by rfl⟩ : syracuseStep 5757925 = 1079611) (by norm_num)
theorem B7677233 : Blo 2273435 7677233 := bstep (se 2 (by rfl) ⟨2878962, by rfl⟩ : syracuseStep 7677233 = 5757925) B5757925
theorem B5118155 : Blo 2273435 5118155 := bstep (se 1 (by rfl) ⟨3838616, by rfl⟩ : syracuseStep 5118155 = 7677233) B7677233
theorem B3412103 : Blo 2273435 3412103 := bstep (se 1 (by rfl) ⟨2559077, by rfl⟩ : syracuseStep 3412103 = 5118155) B5118155
theorem B2274735 : Blo 2273435 2274735 := bstep (se 1 (by rfl) ⟨1706051, by rfl⟩ : syracuseStep 2274735 = 3412103) B3412103
theorem B3412109 : Blo 2273435 3412109 := bbase (se 3 (by rfl) ⟨639770, by rfl⟩ : syracuseStep 3412109 = 1279541) (by norm_num)
theorem B2274739 : Blo 2273435 2274739 := bstep (se 1 (by rfl) ⟨1706054, by rfl⟩ : syracuseStep 2274739 = 3412109) B3412109
theorem B5118173 : Blo 2273435 5118173 := bbase (se 3 (by rfl) ⟨959657, by rfl⟩ : syracuseStep 5118173 = 1919315) (by norm_num)
theorem B3412115 : Blo 2273435 3412115 := bstep (se 1 (by rfl) ⟨2559086, by rfl⟩ : syracuseStep 3412115 = 5118173) B5118173
theorem B2274743 : Blo 2273435 2274743 := bstep (se 1 (by rfl) ⟨1706057, by rfl⟩ : syracuseStep 2274743 = 3412115) B3412115
theorem B3838637 : Blo 2273435 3838637 := bbase (se 3 (by rfl) ⟨719744, by rfl⟩ : syracuseStep 3838637 = 1439489) (by norm_num)
theorem B2559091 : Blo 2273435 2559091 := bstep (se 1 (by rfl) ⟨1919318, by rfl⟩ : syracuseStep 2559091 = 3838637) B3838637
theorem B3412121 : Blo 2273435 3412121 := bstep (se 2 (by rfl) ⟨1279545, by rfl⟩ : syracuseStep 3412121 = 2559091) B2559091
theorem B2274747 : Blo 2273435 2274747 := bstep (se 1 (by rfl) ⟨1706060, by rfl⟩ : syracuseStep 2274747 = 3412121) B3412121
theorem B20752085 : Blo 2273435 20752085 := bbase (se 7 (by rfl) ⟨243188, by rfl⟩ : syracuseStep 20752085 = 486377) (by norm_num)
theorem B13834723 : Blo 2273435 13834723 := bstep (se 1 (by rfl) ⟨10376042, by rfl⟩ : syracuseStep 13834723 = 20752085) B20752085
theorem B18446297 : Blo 2273435 18446297 := bstep (se 2 (by rfl) ⟨6917361, by rfl⟩ : syracuseStep 18446297 = 13834723) B13834723
theorem B49190125 : Blo 2273435 49190125 := bstep (se 3 (by rfl) ⟨9223148, by rfl⟩ : syracuseStep 49190125 = 18446297) B18446297
theorem B65586833 : Blo 2273435 65586833 := bstep (se 2 (by rfl) ⟨24595062, by rfl⟩ : syracuseStep 65586833 = 49190125) B49190125
theorem B43724555 : Blo 2273435 43724555 := bstep (se 1 (by rfl) ⟨32793416, by rfl⟩ : syracuseStep 43724555 = 65586833) B65586833
theorem B29149703 : Blo 2273435 29149703 := bstep (se 1 (by rfl) ⟨21862277, by rfl⟩ : syracuseStep 29149703 = 43724555) B43724555
theorem B19433135 : Blo 2273435 19433135 := bstep (se 1 (by rfl) ⟨14574851, by rfl⟩ : syracuseStep 19433135 = 29149703) B29149703
theorem B12955423 : Blo 2273435 12955423 := bstep (se 1 (by rfl) ⟨9716567, by rfl⟩ : syracuseStep 12955423 = 19433135) B19433135
theorem B17273897 : Blo 2273435 17273897 := bstep (se 2 (by rfl) ⟨6477711, by rfl⟩ : syracuseStep 17273897 = 12955423) B12955423
theorem B11515931 : Blo 2273435 11515931 := bstep (se 1 (by rfl) ⟨8636948, by rfl⟩ : syracuseStep 11515931 = 17273897) B17273897
theorem B7677287 : Blo 2273435 7677287 := bstep (se 1 (by rfl) ⟨5757965, by rfl⟩ : syracuseStep 7677287 = 11515931) B11515931
theorem B5118191 : Blo 2273435 5118191 := bstep (se 1 (by rfl) ⟨3838643, by rfl⟩ : syracuseStep 5118191 = 7677287) B7677287
theorem B3412127 : Blo 2273435 3412127 := bstep (se 1 (by rfl) ⟨2559095, by rfl⟩ : syracuseStep 3412127 = 5118191) B5118191
theorem B2274751 : Blo 2273435 2274751 := bstep (se 1 (by rfl) ⟨1706063, by rfl⟩ : syracuseStep 2274751 = 3412127) B3412127
theorem B3412133 : Blo 2273435 3412133 := bbase (se 4 (by rfl) ⟨319887, by rfl⟩ : syracuseStep 3412133 = 639775) (by norm_num)
theorem B2274755 : Blo 2273435 2274755 := bstep (se 1 (by rfl) ⟨1706066, by rfl⟩ : syracuseStep 2274755 = 3412133) B3412133
theorem B2878993 : Blo 2273435 2878993 := bbase (se 2 (by rfl) ⟨1079622, by rfl⟩ : syracuseStep 2878993 = 2159245) (by norm_num)
theorem B3838657 : Blo 2273435 3838657 := bstep (se 2 (by rfl) ⟨1439496, by rfl⟩ : syracuseStep 3838657 = 2878993) B2878993
theorem B5118209 : Blo 2273435 5118209 := bstep (se 2 (by rfl) ⟨1919328, by rfl⟩ : syracuseStep 5118209 = 3838657) B3838657
theorem B3412139 : Blo 2273435 3412139 := bstep (se 1 (by rfl) ⟨2559104, by rfl⟩ : syracuseStep 3412139 = 5118209) B5118209
theorem B2274759 : Blo 2273435 2274759 := bstep (se 1 (by rfl) ⟨1706069, by rfl⟩ : syracuseStep 2274759 = 3412139) B3412139
theorem B2559109 : Blo 2273435 2559109 := bbase (se 4 (by rfl) ⟨239916, by rfl⟩ : syracuseStep 2559109 = 479833) (by norm_num)
theorem B3412145 : Blo 2273435 3412145 := bstep (se 2 (by rfl) ⟨1279554, by rfl⟩ : syracuseStep 3412145 = 2559109) B2559109
theorem B2274763 : Blo 2273435 2274763 := bstep (se 1 (by rfl) ⟨1706072, by rfl⟩ : syracuseStep 2274763 = 3412145) B3412145
theorem B6917413 : Blo 2273435 6917413 := bbase (se 4 (by rfl) ⟨648507, by rfl⟩ : syracuseStep 6917413 = 1297015) (by norm_num)
theorem B9223217 : Blo 2273435 9223217 := bstep (se 2 (by rfl) ⟨3458706, by rfl⟩ : syracuseStep 9223217 = 6917413) B6917413
theorem B6148811 : Blo 2273435 6148811 := bstep (se 1 (by rfl) ⟨4611608, by rfl⟩ : syracuseStep 6148811 = 9223217) B9223217
theorem B16396829 : Blo 2273435 16396829 := bstep (se 3 (by rfl) ⟨3074405, by rfl⟩ : syracuseStep 16396829 = 6148811) B6148811
theorem B10931219 : Blo 2273435 10931219 := bstep (se 1 (by rfl) ⟨8198414, by rfl⟩ : syracuseStep 10931219 = 16396829) B16396829
theorem B7287479 : Blo 2273435 7287479 := bstep (se 1 (by rfl) ⟨5465609, by rfl⟩ : syracuseStep 7287479 = 10931219) B10931219
theorem B4858319 : Blo 2273435 4858319 := bstep (se 1 (by rfl) ⟨3643739, by rfl⟩ : syracuseStep 4858319 = 7287479) B7287479
theorem B3238879 : Blo 2273435 3238879 := bstep (se 1 (by rfl) ⟨2429159, by rfl⟩ : syracuseStep 3238879 = 4858319) B4858319
theorem B4318505 : Blo 2273435 4318505 := bstep (se 2 (by rfl) ⟨1619439, by rfl⟩ : syracuseStep 4318505 = 3238879) B3238879
theorem B2879003 : Blo 2273435 2879003 := bstep (se 1 (by rfl) ⟨2159252, by rfl⟩ : syracuseStep 2879003 = 4318505) B4318505
theorem B7677341 : Blo 2273435 7677341 := bstep (se 3 (by rfl) ⟨1439501, by rfl⟩ : syracuseStep 7677341 = 2879003) B2879003
theorem B5118227 : Blo 2273435 5118227 := bstep (se 1 (by rfl) ⟨3838670, by rfl⟩ : syracuseStep 5118227 = 7677341) B7677341
theorem B3412151 : Blo 2273435 3412151 := bstep (se 1 (by rfl) ⟨2559113, by rfl⟩ : syracuseStep 3412151 = 5118227) B5118227
theorem B2274767 : Blo 2273435 2274767 := bstep (se 1 (by rfl) ⟨1706075, by rfl⟩ : syracuseStep 2274767 = 3412151) B3412151
theorem B3412157 : Blo 2273435 3412157 := bbase (se 3 (by rfl) ⟨639779, by rfl⟩ : syracuseStep 3412157 = 1279559) (by norm_num)
theorem B2274771 : Blo 2273435 2274771 := bstep (se 1 (by rfl) ⟨1706078, by rfl⟩ : syracuseStep 2274771 = 3412157) B3412157
theorem B5118245 : Blo 2273435 5118245 := bbase (se 4 (by rfl) ⟨479835, by rfl⟩ : syracuseStep 5118245 = 959671) (by norm_num)
theorem B3412163 : Blo 2273435 3412163 := bstep (se 1 (by rfl) ⟨2559122, by rfl⟩ : syracuseStep 3412163 = 5118245) B5118245
theorem B2274775 : Blo 2273435 2274775 := bstep (se 1 (by rfl) ⟨1706081, by rfl⟩ : syracuseStep 2274775 = 3412163) B3412163
theorem B5758037 : Blo 2273435 5758037 := bbase (se 8 (by rfl) ⟨33738, by rfl⟩ : syracuseStep 5758037 = 67477) (by norm_num)
theorem B3838691 : Blo 2273435 3838691 := bstep (se 1 (by rfl) ⟨2879018, by rfl⟩ : syracuseStep 3838691 = 5758037) B5758037
theorem B2559127 : Blo 2273435 2559127 := bstep (se 1 (by rfl) ⟨1919345, by rfl⟩ : syracuseStep 2559127 = 3838691) B3838691
theorem B3412169 : Blo 2273435 3412169 := bstep (se 2 (by rfl) ⟨1279563, by rfl⟩ : syracuseStep 3412169 = 2559127) B2559127
theorem B2274779 : Blo 2273435 2274779 := bstep (se 1 (by rfl) ⟨1706084, by rfl⟩ : syracuseStep 2274779 = 3412169) B3412169
theorem B7995941 : Blo 2273435 7995941 := bbase (se 4 (by rfl) ⟨749619, by rfl⟩ : syracuseStep 7995941 = 1499239) (by norm_num)
theorem B5330627 : Blo 2273435 5330627 := bstep (se 1 (by rfl) ⟨3997970, by rfl⟩ : syracuseStep 5330627 = 7995941) B7995941
theorem B56860021 : Blo 2273435 56860021 := bstep (se 5 (by rfl) ⟨2665313, by rfl⟩ : syracuseStep 56860021 = 5330627) B5330627
theorem B303253445 : Blo 2273435 303253445 := bstep (se 4 (by rfl) ⟨28430010, by rfl⟩ : syracuseStep 303253445 = 56860021) B56860021
theorem B202168963 : Blo 2273435 202168963 := bstep (se 1 (by rfl) ⟨151626722, by rfl⟩ : syracuseStep 202168963 = 303253445) B303253445
theorem B269558617 : Blo 2273435 269558617 := bstep (se 2 (by rfl) ⟨101084481, by rfl⟩ : syracuseStep 269558617 = 202168963) B202168963
theorem B359411489 : Blo 2273435 359411489 := bstep (se 2 (by rfl) ⟨134779308, by rfl⟩ : syracuseStep 359411489 = 269558617) B269558617
theorem B239607659 : Blo 2273435 239607659 := bstep (se 1 (by rfl) ⟨179705744, by rfl⟩ : syracuseStep 239607659 = 359411489) B359411489
theorem B159738439 : Blo 2273435 159738439 := bstep (se 1 (by rfl) ⟨119803829, by rfl⟩ : syracuseStep 159738439 = 239607659) B239607659
theorem B212984585 : Blo 2273435 212984585 := bstep (se 2 (by rfl) ⟨79869219, by rfl⟩ : syracuseStep 212984585 = 159738439) B159738439
theorem B141989723 : Blo 2273435 141989723 := bstep (se 1 (by rfl) ⟨106492292, by rfl⟩ : syracuseStep 141989723 = 212984585) B212984585
theorem B94659815 : Blo 2273435 94659815 := bstep (se 1 (by rfl) ⟨70994861, by rfl⟩ : syracuseStep 94659815 = 141989723) B141989723
theorem B63106543 : Blo 2273435 63106543 := bstep (se 1 (by rfl) ⟨47329907, by rfl⟩ : syracuseStep 63106543 = 94659815) B94659815
theorem B336568229 : Blo 2273435 336568229 := bstep (se 4 (by rfl) ⟨31553271, by rfl⟩ : syracuseStep 336568229 = 63106543) B63106543
theorem B224378819 : Blo 2273435 224378819 := bstep (se 1 (by rfl) ⟨168284114, by rfl⟩ : syracuseStep 224378819 = 336568229) B336568229
theorem B149585879 : Blo 2273435 149585879 := bstep (se 1 (by rfl) ⟨112189409, by rfl⟩ : syracuseStep 149585879 = 224378819) B224378819
theorem B398895677 : Blo 2273435 398895677 := bstep (se 3 (by rfl) ⟨74792939, by rfl⟩ : syracuseStep 398895677 = 149585879) B149585879
theorem B265930451 : Blo 2273435 265930451 := bstep (se 1 (by rfl) ⟨199447838, by rfl⟩ : syracuseStep 265930451 = 398895677) B398895677
theorem B177286967 : Blo 2273435 177286967 := bstep (se 1 (by rfl) ⟨132965225, by rfl⟩ : syracuseStep 177286967 = 265930451) B265930451
theorem B118191311 : Blo 2273435 118191311 := bstep (se 1 (by rfl) ⟨88643483, by rfl⟩ : syracuseStep 118191311 = 177286967) B177286967
theorem B78794207 : Blo 2273435 78794207 := bstep (se 1 (by rfl) ⟨59095655, by rfl⟩ : syracuseStep 78794207 = 118191311) B118191311
theorem B52529471 : Blo 2273435 52529471 := bstep (se 1 (by rfl) ⟨39397103, by rfl⟩ : syracuseStep 52529471 = 78794207) B78794207
theorem B35019647 : Blo 2273435 35019647 := bstep (se 1 (by rfl) ⟨26264735, by rfl⟩ : syracuseStep 35019647 = 52529471) B52529471
theorem B23346431 : Blo 2273435 23346431 := bstep (se 1 (by rfl) ⟨17509823, by rfl⟩ : syracuseStep 23346431 = 35019647) B35019647
theorem B15564287 : Blo 2273435 15564287 := bstep (se 1 (by rfl) ⟨11673215, by rfl⟩ : syracuseStep 15564287 = 23346431) B23346431
theorem B10376191 : Blo 2273435 10376191 := bstep (se 1 (by rfl) ⟨7782143, by rfl⟩ : syracuseStep 10376191 = 15564287) B15564287
theorem B13834921 : Blo 2273435 13834921 := bstep (se 2 (by rfl) ⟨5188095, by rfl⟩ : syracuseStep 13834921 = 10376191) B10376191
theorem B18446561 : Blo 2273435 18446561 := bstep (se 2 (by rfl) ⟨6917460, by rfl⟩ : syracuseStep 18446561 = 13834921) B13834921
theorem B12297707 : Blo 2273435 12297707 := bstep (se 1 (by rfl) ⟨9223280, by rfl⟩ : syracuseStep 12297707 = 18446561) B18446561
theorem B8198471 : Blo 2273435 8198471 := bstep (se 1 (by rfl) ⟨6148853, by rfl⟩ : syracuseStep 8198471 = 12297707) B12297707
theorem B5465647 : Blo 2273435 5465647 := bstep (se 1 (by rfl) ⟨4099235, by rfl⟩ : syracuseStep 5465647 = 8198471) B8198471
theorem B7287529 : Blo 2273435 7287529 := bstep (se 2 (by rfl) ⟨2732823, by rfl⟩ : syracuseStep 7287529 = 5465647) B5465647
theorem B9716705 : Blo 2273435 9716705 := bstep (se 2 (by rfl) ⟨3643764, by rfl⟩ : syracuseStep 9716705 = 7287529) B7287529
theorem B6477803 : Blo 2273435 6477803 := bstep (se 1 (by rfl) ⟨4858352, by rfl⟩ : syracuseStep 6477803 = 9716705) B9716705
theorem B4318535 : Blo 2273435 4318535 := bstep (se 1 (by rfl) ⟨3238901, by rfl⟩ : syracuseStep 4318535 = 6477803) B6477803
theorem B11516093 : Blo 2273435 11516093 := bstep (se 3 (by rfl) ⟨2159267, by rfl⟩ : syracuseStep 11516093 = 4318535) B4318535
theorem B7677395 : Blo 2273435 7677395 := bstep (se 1 (by rfl) ⟨5758046, by rfl⟩ : syracuseStep 7677395 = 11516093) B11516093
theorem B5118263 : Blo 2273435 5118263 := bstep (se 1 (by rfl) ⟨3838697, by rfl⟩ : syracuseStep 5118263 = 7677395) B7677395
theorem B3412175 : Blo 2273435 3412175 := bstep (se 1 (by rfl) ⟨2559131, by rfl⟩ : syracuseStep 3412175 = 5118263) B5118263
theorem B2274783 : Blo 2273435 2274783 := bstep (se 1 (by rfl) ⟨1706087, by rfl⟩ : syracuseStep 2274783 = 3412175) B3412175
theorem B3412181 : Blo 2273435 3412181 := bbase (se 7 (by rfl) ⟨39986, by rfl⟩ : syracuseStep 3412181 = 79973) (by norm_num)
theorem B2274787 : Blo 2273435 2274787 := bstep (se 1 (by rfl) ⟨1706090, by rfl⟩ : syracuseStep 2274787 = 3412181) B3412181
theorem B2429185 : Blo 2273435 2429185 := bbase (se 2 (by rfl) ⟨910944, by rfl⟩ : syracuseStep 2429185 = 1821889) (by norm_num)
theorem B3238913 : Blo 2273435 3238913 := bstep (se 2 (by rfl) ⟨1214592, by rfl⟩ : syracuseStep 3238913 = 2429185) B2429185
theorem B8637101 : Blo 2273435 8637101 := bstep (se 3 (by rfl) ⟨1619456, by rfl⟩ : syracuseStep 8637101 = 3238913) B3238913
theorem B5758067 : Blo 2273435 5758067 := bstep (se 1 (by rfl) ⟨4318550, by rfl⟩ : syracuseStep 5758067 = 8637101) B8637101
theorem B3838711 : Blo 2273435 3838711 := bstep (se 1 (by rfl) ⟨2879033, by rfl⟩ : syracuseStep 3838711 = 5758067) B5758067
theorem B5118281 : Blo 2273435 5118281 := bstep (se 2 (by rfl) ⟨1919355, by rfl⟩ : syracuseStep 5118281 = 3838711) B3838711
theorem B3412187 : Blo 2273435 3412187 := bstep (se 1 (by rfl) ⟨2559140, by rfl⟩ : syracuseStep 3412187 = 5118281) B5118281
theorem B2274791 : Blo 2273435 2274791 := bstep (se 1 (by rfl) ⟨1706093, by rfl⟩ : syracuseStep 2274791 = 3412187) B3412187
theorem B2559145 : Blo 2273435 2559145 := bbase (se 2 (by rfl) ⟨959679, by rfl⟩ : syracuseStep 2559145 = 1919359) (by norm_num)
theorem B3412193 : Blo 2273435 3412193 := bstep (se 2 (by rfl) ⟨1279572, by rfl⟩ : syracuseStep 3412193 = 2559145) B2559145
theorem B2274795 : Blo 2273435 2274795 := bstep (se 1 (by rfl) ⟨1706096, by rfl⟩ : syracuseStep 2274795 = 3412193) B3412193
theorem B9716773 : Blo 2273435 9716773 := bbase (se 4 (by rfl) ⟨910947, by rfl⟩ : syracuseStep 9716773 = 1821895) (by norm_num)
theorem B12955697 : Blo 2273435 12955697 := bstep (se 2 (by rfl) ⟨4858386, by rfl⟩ : syracuseStep 12955697 = 9716773) B9716773
theorem B8637131 : Blo 2273435 8637131 := bstep (se 1 (by rfl) ⟨6477848, by rfl⟩ : syracuseStep 8637131 = 12955697) B12955697
theorem B5758087 : Blo 2273435 5758087 := bstep (se 1 (by rfl) ⟨4318565, by rfl⟩ : syracuseStep 5758087 = 8637131) B8637131
theorem B7677449 : Blo 2273435 7677449 := bstep (se 2 (by rfl) ⟨2879043, by rfl⟩ : syracuseStep 7677449 = 5758087) B5758087
theorem B5118299 : Blo 2273435 5118299 := bstep (se 1 (by rfl) ⟨3838724, by rfl⟩ : syracuseStep 5118299 = 7677449) B7677449
theorem B3412199 : Blo 2273435 3412199 := bstep (se 1 (by rfl) ⟨2559149, by rfl⟩ : syracuseStep 3412199 = 5118299) B5118299
theorem B2274799 : Blo 2273435 2274799 := bstep (se 1 (by rfl) ⟨1706099, by rfl⟩ : syracuseStep 2274799 = 3412199) B3412199
theorem B3412205 : Blo 2273435 3412205 := bbase (se 3 (by rfl) ⟨639788, by rfl⟩ : syracuseStep 3412205 = 1279577) (by norm_num)
theorem B2274803 : Blo 2273435 2274803 := bstep (se 1 (by rfl) ⟨1706102, by rfl⟩ : syracuseStep 2274803 = 3412205) B3412205
theorem B5118317 : Blo 2273435 5118317 := bbase (se 3 (by rfl) ⟨959684, by rfl⟩ : syracuseStep 5118317 = 1919369) (by norm_num)
theorem B3412211 : Blo 2273435 3412211 := bstep (se 1 (by rfl) ⟨2559158, by rfl⟩ : syracuseStep 3412211 = 5118317) B5118317
theorem B2274807 : Blo 2273435 2274807 := bstep (se 1 (by rfl) ⟨1706105, by rfl⟩ : syracuseStep 2274807 = 3412211) B3412211
theorem B4318589 : Blo 2273435 4318589 := bbase (se 3 (by rfl) ⟨809735, by rfl⟩ : syracuseStep 4318589 = 1619471) (by norm_num)
theorem B2879059 : Blo 2273435 2879059 := bstep (se 1 (by rfl) ⟨2159294, by rfl⟩ : syracuseStep 2879059 = 4318589) B4318589
theorem B3838745 : Blo 2273435 3838745 := bstep (se 2 (by rfl) ⟨1439529, by rfl⟩ : syracuseStep 3838745 = 2879059) B2879059
theorem B2559163 : Blo 2273435 2559163 := bstep (se 1 (by rfl) ⟨1919372, by rfl⟩ : syracuseStep 2559163 = 3838745) B3838745
theorem B3412217 : Blo 2273435 3412217 := bstep (se 2 (by rfl) ⟨1279581, by rfl⟩ : syracuseStep 3412217 = 2559163) B2559163
theorem B2274811 : Blo 2273435 2274811 := bstep (se 1 (by rfl) ⟨1706108, by rfl⟩ : syracuseStep 2274811 = 3412217) B3412217
theorem B6917557 : Blo 2273435 6917557 := bbase (se 5 (by rfl) ⟨324260, by rfl⟩ : syracuseStep 6917557 = 648521) (by norm_num)
theorem B9223409 : Blo 2273435 9223409 := bstep (se 2 (by rfl) ⟨3458778, by rfl⟩ : syracuseStep 9223409 = 6917557) B6917557
theorem B6148939 : Blo 2273435 6148939 := bstep (se 1 (by rfl) ⟨4611704, by rfl⟩ : syracuseStep 6148939 = 9223409) B9223409
theorem B8198585 : Blo 2273435 8198585 := bstep (se 2 (by rfl) ⟨3074469, by rfl⟩ : syracuseStep 8198585 = 6148939) B6148939
theorem B5465723 : Blo 2273435 5465723 := bstep (se 1 (by rfl) ⟨4099292, by rfl⟩ : syracuseStep 5465723 = 8198585) B8198585
theorem B58301045 : Blo 2273435 58301045 := bstep (se 5 (by rfl) ⟨2732861, by rfl⟩ : syracuseStep 58301045 = 5465723) B5465723
theorem B38867363 : Blo 2273435 38867363 := bstep (se 1 (by rfl) ⟨29150522, by rfl⟩ : syracuseStep 38867363 = 58301045) B58301045
theorem B25911575 : Blo 2273435 25911575 := bstep (se 1 (by rfl) ⟨19433681, by rfl⟩ : syracuseStep 25911575 = 38867363) B38867363
theorem B17274383 : Blo 2273435 17274383 := bstep (se 1 (by rfl) ⟨12955787, by rfl⟩ : syracuseStep 17274383 = 25911575) B25911575
theorem B11516255 : Blo 2273435 11516255 := bstep (se 1 (by rfl) ⟨8637191, by rfl⟩ : syracuseStep 11516255 = 17274383) B17274383
theorem B7677503 : Blo 2273435 7677503 := bstep (se 1 (by rfl) ⟨5758127, by rfl⟩ : syracuseStep 7677503 = 11516255) B11516255
theorem B5118335 : Blo 2273435 5118335 := bstep (se 1 (by rfl) ⟨3838751, by rfl⟩ : syracuseStep 5118335 = 7677503) B7677503
theorem B3412223 : Blo 2273435 3412223 := bstep (se 1 (by rfl) ⟨2559167, by rfl⟩ : syracuseStep 3412223 = 5118335) B5118335
theorem B2274815 : Blo 2273435 2274815 := bstep (se 1 (by rfl) ⟨1706111, by rfl⟩ : syracuseStep 2274815 = 3412223) B3412223
theorem B3412229 : Blo 2273435 3412229 := bbase (se 4 (by rfl) ⟨319896, by rfl⟩ : syracuseStep 3412229 = 639793) (by norm_num)
theorem B2274819 : Blo 2273435 2274819 := bstep (se 1 (by rfl) ⟨1706114, by rfl⟩ : syracuseStep 2274819 = 3412229) B3412229
theorem B3838765 : Blo 2273435 3838765 := bbase (se 3 (by rfl) ⟨719768, by rfl⟩ : syracuseStep 3838765 = 1439537) (by norm_num)
theorem B5118353 : Blo 2273435 5118353 := bstep (se 2 (by rfl) ⟨1919382, by rfl⟩ : syracuseStep 5118353 = 3838765) B3838765
theorem B3412235 : Blo 2273435 3412235 := bstep (se 1 (by rfl) ⟨2559176, by rfl⟩ : syracuseStep 3412235 = 5118353) B5118353
theorem B2274823 : Blo 2273435 2274823 := bstep (se 1 (by rfl) ⟨1706117, by rfl⟩ : syracuseStep 2274823 = 3412235) B3412235
theorem B2559181 : Blo 2273435 2559181 := bbase (se 3 (by rfl) ⟨479846, by rfl⟩ : syracuseStep 2559181 = 959693) (by norm_num)
theorem B3412241 : Blo 2273435 3412241 := bstep (se 2 (by rfl) ⟨1279590, by rfl⟩ : syracuseStep 3412241 = 2559181) B2559181
theorem B2274827 : Blo 2273435 2274827 := bstep (se 1 (by rfl) ⟨1706120, by rfl⟩ : syracuseStep 2274827 = 3412241) B3412241
theorem B7677557 : Blo 2273435 7677557 := bbase (se 5 (by rfl) ⟨359885, by rfl⟩ : syracuseStep 7677557 = 719771) (by norm_num)
theorem B5118371 : Blo 2273435 5118371 := bstep (se 1 (by rfl) ⟨3838778, by rfl⟩ : syracuseStep 5118371 = 7677557) B7677557
theorem B3412247 : Blo 2273435 3412247 := bstep (se 1 (by rfl) ⟨2559185, by rfl⟩ : syracuseStep 3412247 = 5118371) B5118371
theorem B2274831 : Blo 2273435 2274831 := bstep (se 1 (by rfl) ⟨1706123, by rfl⟩ : syracuseStep 2274831 = 3412247) B3412247
theorem B3412253 : Blo 2273435 3412253 := bbase (se 3 (by rfl) ⟨639797, by rfl⟩ : syracuseStep 3412253 = 1279595) (by norm_num)
theorem B2274835 : Blo 2273435 2274835 := bstep (se 1 (by rfl) ⟨1706126, by rfl⟩ : syracuseStep 2274835 = 3412253) B3412253
theorem B5118389 : Blo 2273435 5118389 := bbase (se 5 (by rfl) ⟨239924, by rfl⟩ : syracuseStep 5118389 = 479849) (by norm_num)
theorem B3412259 : Blo 2273435 3412259 := bstep (se 1 (by rfl) ⟨2559194, by rfl⟩ : syracuseStep 3412259 = 5118389) B5118389
theorem B2274839 : Blo 2273435 2274839 := bstep (se 1 (by rfl) ⟨1706129, by rfl⟩ : syracuseStep 2274839 = 3412259) B3412259
theorem B3643861 : Blo 2273435 3643861 := bbase (se 7 (by rfl) ⟨42701, by rfl⟩ : syracuseStep 3643861 = 85403) (by norm_num)
theorem B4858481 : Blo 2273435 4858481 := bstep (se 2 (by rfl) ⟨1821930, by rfl⟩ : syracuseStep 4858481 = 3643861) B3643861
theorem B12955949 : Blo 2273435 12955949 := bstep (se 3 (by rfl) ⟨2429240, by rfl⟩ : syracuseStep 12955949 = 4858481) B4858481
theorem B8637299 : Blo 2273435 8637299 := bstep (se 1 (by rfl) ⟨6477974, by rfl⟩ : syracuseStep 8637299 = 12955949) B12955949
theorem B5758199 : Blo 2273435 5758199 := bstep (se 1 (by rfl) ⟨4318649, by rfl⟩ : syracuseStep 5758199 = 8637299) B8637299
theorem B3838799 : Blo 2273435 3838799 := bstep (se 1 (by rfl) ⟨2879099, by rfl⟩ : syracuseStep 3838799 = 5758199) B5758199
theorem B2559199 : Blo 2273435 2559199 := bstep (se 1 (by rfl) ⟨1919399, by rfl⟩ : syracuseStep 2559199 = 3838799) B3838799
theorem B3412265 : Blo 2273435 3412265 := bstep (se 2 (by rfl) ⟨1279599, by rfl⟩ : syracuseStep 3412265 = 2559199) B2559199
theorem B2274843 : Blo 2273435 2274843 := bstep (se 1 (by rfl) ⟨1706132, by rfl⟩ : syracuseStep 2274843 = 3412265) B3412265
theorem B9223541 : Blo 2273435 9223541 := bbase (se 5 (by rfl) ⟨432353, by rfl⟩ : syracuseStep 9223541 = 864707) (by norm_num)
theorem B6149027 : Blo 2273435 6149027 := bstep (se 1 (by rfl) ⟨4611770, by rfl⟩ : syracuseStep 6149027 = 9223541) B9223541
theorem B4099351 : Blo 2273435 4099351 := bstep (se 1 (by rfl) ⟨3074513, by rfl⟩ : syracuseStep 4099351 = 6149027) B6149027
theorem B5465801 : Blo 2273435 5465801 := bstep (se 2 (by rfl) ⟨2049675, by rfl⟩ : syracuseStep 5465801 = 4099351) B4099351
theorem B3643867 : Blo 2273435 3643867 := bstep (se 1 (by rfl) ⟨2732900, by rfl⟩ : syracuseStep 3643867 = 5465801) B5465801
theorem B4858489 : Blo 2273435 4858489 := bstep (se 2 (by rfl) ⟨1821933, by rfl⟩ : syracuseStep 4858489 = 3643867) B3643867
theorem B6477985 : Blo 2273435 6477985 := bstep (se 2 (by rfl) ⟨2429244, by rfl⟩ : syracuseStep 6477985 = 4858489) B4858489
theorem B8637313 : Blo 2273435 8637313 := bstep (se 2 (by rfl) ⟨3238992, by rfl⟩ : syracuseStep 8637313 = 6477985) B6477985
theorem B11516417 : Blo 2273435 11516417 := bstep (se 2 (by rfl) ⟨4318656, by rfl⟩ : syracuseStep 11516417 = 8637313) B8637313
theorem B7677611 : Blo 2273435 7677611 := bstep (se 1 (by rfl) ⟨5758208, by rfl⟩ : syracuseStep 7677611 = 11516417) B11516417
theorem B5118407 : Blo 2273435 5118407 := bstep (se 1 (by rfl) ⟨3838805, by rfl⟩ : syracuseStep 5118407 = 7677611) B7677611
theorem B3412271 : Blo 2273435 3412271 := bstep (se 1 (by rfl) ⟨2559203, by rfl⟩ : syracuseStep 3412271 = 5118407) B5118407
theorem B2274847 : Blo 2273435 2274847 := bstep (se 1 (by rfl) ⟨1706135, by rfl⟩ : syracuseStep 2274847 = 3412271) B3412271
theorem B3412277 : Blo 2273435 3412277 := bbase (se 5 (by rfl) ⟨159950, by rfl⟩ : syracuseStep 3412277 = 319901) (by norm_num)
theorem B2274851 : Blo 2273435 2274851 := bstep (se 1 (by rfl) ⟨1706138, by rfl⟩ : syracuseStep 2274851 = 3412277) B3412277
theorem B5758229 : Blo 2273435 5758229 := bbase (se 6 (by rfl) ⟨134958, by rfl⟩ : syracuseStep 5758229 = 269917) (by norm_num)
theorem B3838819 : Blo 2273435 3838819 := bstep (se 1 (by rfl) ⟨2879114, by rfl⟩ : syracuseStep 3838819 = 5758229) B5758229
theorem B5118425 : Blo 2273435 5118425 := bstep (se 2 (by rfl) ⟨1919409, by rfl⟩ : syracuseStep 5118425 = 3838819) B3838819
theorem B3412283 : Blo 2273435 3412283 := bstep (se 1 (by rfl) ⟨2559212, by rfl⟩ : syracuseStep 3412283 = 5118425) B5118425
theorem B2274855 : Blo 2273435 2274855 := bstep (se 1 (by rfl) ⟨1706141, by rfl⟩ : syracuseStep 2274855 = 3412283) B3412283
theorem B2559217 : Blo 2273435 2559217 := bbase (se 2 (by rfl) ⟨959706, by rfl⟩ : syracuseStep 2559217 = 1919413) (by norm_num)
theorem B3412289 : Blo 2273435 3412289 := bstep (se 2 (by rfl) ⟨1279608, by rfl⟩ : syracuseStep 3412289 = 2559217) B2559217
theorem B2274859 : Blo 2273435 2274859 := bstep (se 1 (by rfl) ⟨1706144, by rfl⟩ : syracuseStep 2274859 = 3412289) B3412289
theorem B5540413 : Blo 2273435 5540413 := bbase (se 3 (by rfl) ⟨1038827, by rfl⟩ : syracuseStep 5540413 = 2077655) (by norm_num)
theorem B7387217 : Blo 2273435 7387217 := bstep (se 2 (by rfl) ⟨2770206, by rfl⟩ : syracuseStep 7387217 = 5540413) B5540413
theorem B4924811 : Blo 2273435 4924811 := bstep (se 1 (by rfl) ⟨3693608, by rfl⟩ : syracuseStep 4924811 = 7387217) B7387217
theorem B13132829 : Blo 2273435 13132829 := bstep (se 3 (by rfl) ⟨2462405, by rfl⟩ : syracuseStep 13132829 = 4924811) B4924811
theorem B8755219 : Blo 2273435 8755219 := bstep (se 1 (by rfl) ⟨6566414, by rfl⟩ : syracuseStep 8755219 = 13132829) B13132829
theorem B46694501 : Blo 2273435 46694501 := bstep (se 4 (by rfl) ⟨4377609, by rfl⟩ : syracuseStep 46694501 = 8755219) B8755219
theorem B31129667 : Blo 2273435 31129667 := bstep (se 1 (by rfl) ⟨23347250, by rfl⟩ : syracuseStep 31129667 = 46694501) B46694501
theorem B20753111 : Blo 2273435 20753111 := bstep (se 1 (by rfl) ⟨15564833, by rfl⟩ : syracuseStep 20753111 = 31129667) B31129667
theorem B13835407 : Blo 2273435 13835407 := bstep (se 1 (by rfl) ⟨10376555, by rfl⟩ : syracuseStep 13835407 = 20753111) B20753111
theorem B18447209 : Blo 2273435 18447209 := bstep (se 2 (by rfl) ⟨6917703, by rfl⟩ : syracuseStep 18447209 = 13835407) B13835407
theorem B12298139 : Blo 2273435 12298139 := bstep (se 1 (by rfl) ⟨9223604, by rfl⟩ : syracuseStep 12298139 = 18447209) B18447209
theorem B8198759 : Blo 2273435 8198759 := bstep (se 1 (by rfl) ⟨6149069, by rfl⟩ : syracuseStep 8198759 = 12298139) B12298139
theorem B21863357 : Blo 2273435 21863357 := bstep (se 3 (by rfl) ⟨4099379, by rfl⟩ : syracuseStep 21863357 = 8198759) B8198759
theorem B14575571 : Blo 2273435 14575571 := bstep (se 1 (by rfl) ⟨10931678, by rfl⟩ : syracuseStep 14575571 = 21863357) B21863357
theorem B9717047 : Blo 2273435 9717047 := bstep (se 1 (by rfl) ⟨7287785, by rfl⟩ : syracuseStep 9717047 = 14575571) B14575571
theorem B6478031 : Blo 2273435 6478031 := bstep (se 1 (by rfl) ⟨4858523, by rfl⟩ : syracuseStep 6478031 = 9717047) B9717047
theorem B4318687 : Blo 2273435 4318687 := bstep (se 1 (by rfl) ⟨3239015, by rfl⟩ : syracuseStep 4318687 = 6478031) B6478031
theorem B5758249 : Blo 2273435 5758249 := bstep (se 2 (by rfl) ⟨2159343, by rfl⟩ : syracuseStep 5758249 = 4318687) B4318687
theorem B7677665 : Blo 2273435 7677665 := bstep (se 2 (by rfl) ⟨2879124, by rfl⟩ : syracuseStep 7677665 = 5758249) B5758249
theorem B5118443 : Blo 2273435 5118443 := bstep (se 1 (by rfl) ⟨3838832, by rfl⟩ : syracuseStep 5118443 = 7677665) B7677665
theorem B3412295 : Blo 2273435 3412295 := bstep (se 1 (by rfl) ⟨2559221, by rfl⟩ : syracuseStep 3412295 = 5118443) B5118443
theorem B2274863 : Blo 2273435 2274863 := bstep (se 1 (by rfl) ⟨1706147, by rfl⟩ : syracuseStep 2274863 = 3412295) B3412295
theorem B3412301 : Blo 2273435 3412301 := bbase (se 3 (by rfl) ⟨639806, by rfl⟩ : syracuseStep 3412301 = 1279613) (by norm_num)
theorem B2274867 : Blo 2273435 2274867 := bstep (se 1 (by rfl) ⟨1706150, by rfl⟩ : syracuseStep 2274867 = 3412301) B3412301
theorem B5118461 : Blo 2273435 5118461 := bbase (se 3 (by rfl) ⟨959711, by rfl⟩ : syracuseStep 5118461 = 1919423) (by norm_num)
theorem B3412307 : Blo 2273435 3412307 := bstep (se 1 (by rfl) ⟨2559230, by rfl⟩ : syracuseStep 3412307 = 5118461) B5118461
theorem B2274871 : Blo 2273435 2274871 := bstep (se 1 (by rfl) ⟨1706153, by rfl⟩ : syracuseStep 2274871 = 3412307) B3412307
theorem B3838853 : Blo 2273435 3838853 := bbase (se 4 (by rfl) ⟨359892, by rfl⟩ : syracuseStep 3838853 = 719785) (by norm_num)
theorem B2559235 : Blo 2273435 2559235 := bstep (se 1 (by rfl) ⟨1919426, by rfl⟩ : syracuseStep 2559235 = 3838853) B3838853
theorem B3412313 : Blo 2273435 3412313 := bstep (se 2 (by rfl) ⟨1279617, by rfl⟩ : syracuseStep 3412313 = 2559235) B2559235
theorem B2274875 : Blo 2273435 2274875 := bstep (se 1 (by rfl) ⟨1706156, by rfl⟩ : syracuseStep 2274875 = 3412313) B3412313
theorem B17274869 : Blo 2273435 17274869 := bbase (se 5 (by rfl) ⟨809759, by rfl⟩ : syracuseStep 17274869 = 1619519) (by norm_num)
theorem B11516579 : Blo 2273435 11516579 := bstep (se 1 (by rfl) ⟨8637434, by rfl⟩ : syracuseStep 11516579 = 17274869) B17274869
theorem B7677719 : Blo 2273435 7677719 := bstep (se 1 (by rfl) ⟨5758289, by rfl⟩ : syracuseStep 7677719 = 11516579) B11516579
theorem B5118479 : Blo 2273435 5118479 := bstep (se 1 (by rfl) ⟨3838859, by rfl⟩ : syracuseStep 5118479 = 7677719) B7677719
theorem B3412319 : Blo 2273435 3412319 := bstep (se 1 (by rfl) ⟨2559239, by rfl⟩ : syracuseStep 3412319 = 5118479) B5118479
theorem B2274879 : Blo 2273435 2274879 := bstep (se 1 (by rfl) ⟨1706159, by rfl⟩ : syracuseStep 2274879 = 3412319) B3412319
theorem B3412325 : Blo 2273435 3412325 := bbase (se 4 (by rfl) ⟨319905, by rfl⟩ : syracuseStep 3412325 = 639811) (by norm_num)
theorem B2274883 : Blo 2273435 2274883 := bstep (se 1 (by rfl) ⟨1706162, by rfl⟩ : syracuseStep 2274883 = 3412325) B3412325
theorem B4318733 : Blo 2273435 4318733 := bbase (se 3 (by rfl) ⟨809762, by rfl⟩ : syracuseStep 4318733 = 1619525) (by norm_num)
theorem B2879155 : Blo 2273435 2879155 := bstep (se 1 (by rfl) ⟨2159366, by rfl⟩ : syracuseStep 2879155 = 4318733) B4318733
theorem B3838873 : Blo 2273435 3838873 := bstep (se 2 (by rfl) ⟨1439577, by rfl⟩ : syracuseStep 3838873 = 2879155) B2879155
theorem B5118497 : Blo 2273435 5118497 := bstep (se 2 (by rfl) ⟨1919436, by rfl⟩ : syracuseStep 5118497 = 3838873) B3838873
theorem B3412331 : Blo 2273435 3412331 := bstep (se 1 (by rfl) ⟨2559248, by rfl⟩ : syracuseStep 3412331 = 5118497) B5118497
theorem B2274887 : Blo 2273435 2274887 := bstep (se 1 (by rfl) ⟨1706165, by rfl⟩ : syracuseStep 2274887 = 3412331) B3412331
theorem B2559253 : Blo 2273435 2559253 := bbase (se 6 (by rfl) ⟨59982, by rfl⟩ : syracuseStep 2559253 = 119965) (by norm_num)
theorem B3412337 : Blo 2273435 3412337 := bstep (se 2 (by rfl) ⟨1279626, by rfl⟩ : syracuseStep 3412337 = 2559253) B2559253
theorem B2274891 : Blo 2273435 2274891 := bstep (se 1 (by rfl) ⟨1706168, by rfl⟩ : syracuseStep 2274891 = 3412337) B3412337
theorem B2879165 : Blo 2273435 2879165 := bbase (se 3 (by rfl) ⟨539843, by rfl⟩ : syracuseStep 2879165 = 1079687) (by norm_num)
theorem B7677773 : Blo 2273435 7677773 := bstep (se 3 (by rfl) ⟨1439582, by rfl⟩ : syracuseStep 7677773 = 2879165) B2879165
theorem B5118515 : Blo 2273435 5118515 := bstep (se 1 (by rfl) ⟨3838886, by rfl⟩ : syracuseStep 5118515 = 7677773) B7677773
theorem B3412343 : Blo 2273435 3412343 := bstep (se 1 (by rfl) ⟨2559257, by rfl⟩ : syracuseStep 3412343 = 5118515) B5118515
theorem B2274895 : Blo 2273435 2274895 := bstep (se 1 (by rfl) ⟨1706171, by rfl⟩ : syracuseStep 2274895 = 3412343) B3412343
theorem B3412349 : Blo 2273435 3412349 := bbase (se 3 (by rfl) ⟨639815, by rfl⟩ : syracuseStep 3412349 = 1279631) (by norm_num)
theorem B2274899 : Blo 2273435 2274899 := bstep (se 1 (by rfl) ⟨1706174, by rfl⟩ : syracuseStep 2274899 = 3412349) B3412349
theorem B5118533 : Blo 2273435 5118533 := bbase (se 4 (by rfl) ⟨479862, by rfl⟩ : syracuseStep 5118533 = 959725) (by norm_num)
theorem B3412355 : Blo 2273435 3412355 := bstep (se 1 (by rfl) ⟨2559266, by rfl⟩ : syracuseStep 3412355 = 5118533) B5118533
theorem B2274903 : Blo 2273435 2274903 := bstep (se 1 (by rfl) ⟨1706177, by rfl⟩ : syracuseStep 2274903 = 3412355) B3412355
theorem B2429309 : Blo 2273435 2429309 := bbase (se 3 (by rfl) ⟨455495, by rfl⟩ : syracuseStep 2429309 = 910991) (by norm_num)
theorem B6478157 : Blo 2273435 6478157 := bstep (se 3 (by rfl) ⟨1214654, by rfl⟩ : syracuseStep 6478157 = 2429309) B2429309
theorem B4318771 : Blo 2273435 4318771 := bstep (se 1 (by rfl) ⟨3239078, by rfl⟩ : syracuseStep 4318771 = 6478157) B6478157
theorem B5758361 : Blo 2273435 5758361 := bstep (se 2 (by rfl) ⟨2159385, by rfl⟩ : syracuseStep 5758361 = 4318771) B4318771
theorem B3838907 : Blo 2273435 3838907 := bstep (se 1 (by rfl) ⟨2879180, by rfl⟩ : syracuseStep 3838907 = 5758361) B5758361
theorem B2559271 : Blo 2273435 2559271 := bstep (se 1 (by rfl) ⟨1919453, by rfl⟩ : syracuseStep 2559271 = 3838907) B3838907
theorem B3412361 : Blo 2273435 3412361 := bstep (se 2 (by rfl) ⟨1279635, by rfl⟩ : syracuseStep 3412361 = 2559271) B2559271
theorem B2274907 : Blo 2273435 2274907 := bstep (se 1 (by rfl) ⟨1706180, by rfl⟩ : syracuseStep 2274907 = 3412361) B3412361
theorem B11516741 : Blo 2273435 11516741 := bbase (se 4 (by rfl) ⟨1079694, by rfl⟩ : syracuseStep 11516741 = 2159389) (by norm_num)
theorem B7677827 : Blo 2273435 7677827 := bstep (se 1 (by rfl) ⟨5758370, by rfl⟩ : syracuseStep 7677827 = 11516741) B11516741
theorem B5118551 : Blo 2273435 5118551 := bstep (se 1 (by rfl) ⟨3838913, by rfl⟩ : syracuseStep 5118551 = 7677827) B7677827
theorem B3412367 : Blo 2273435 3412367 := bstep (se 1 (by rfl) ⟨2559275, by rfl⟩ : syracuseStep 3412367 = 5118551) B5118551
theorem B2274911 : Blo 2273435 2274911 := bstep (se 1 (by rfl) ⟨1706183, by rfl⟩ : syracuseStep 2274911 = 3412367) B3412367
theorem B3412373 : Blo 2273435 3412373 := bbase (se 6 (by rfl) ⟨79977, by rfl⟩ : syracuseStep 3412373 = 159955) (by norm_num)
theorem B2274915 : Blo 2273435 2274915 := bstep (se 1 (by rfl) ⟨1706186, by rfl⟩ : syracuseStep 2274915 = 3412373) B3412373
theorem B4611917 : Blo 2273435 4611917 := bbase (se 3 (by rfl) ⟨864734, by rfl⟩ : syracuseStep 4611917 = 1729469) (by norm_num)
theorem B3074611 : Blo 2273435 3074611 := bstep (se 1 (by rfl) ⟨2305958, by rfl⟩ : syracuseStep 3074611 = 4611917) B4611917
theorem B4099481 : Blo 2273435 4099481 := bstep (se 2 (by rfl) ⟨1537305, by rfl⟩ : syracuseStep 4099481 = 3074611) B3074611
theorem B2732987 : Blo 2273435 2732987 := bstep (se 1 (by rfl) ⟨2049740, by rfl⟩ : syracuseStep 2732987 = 4099481) B4099481
theorem B7287965 : Blo 2273435 7287965 := bstep (se 3 (by rfl) ⟨1366493, by rfl⟩ : syracuseStep 7287965 = 2732987) B2732987
theorem B4858643 : Blo 2273435 4858643 := bstep (se 1 (by rfl) ⟨3643982, by rfl⟩ : syracuseStep 4858643 = 7287965) B7287965
theorem B12956381 : Blo 2273435 12956381 := bstep (se 3 (by rfl) ⟨2429321, by rfl⟩ : syracuseStep 12956381 = 4858643) B4858643
theorem B8637587 : Blo 2273435 8637587 := bstep (se 1 (by rfl) ⟨6478190, by rfl⟩ : syracuseStep 8637587 = 12956381) B12956381
theorem B5758391 : Blo 2273435 5758391 := bstep (se 1 (by rfl) ⟨4318793, by rfl⟩ : syracuseStep 5758391 = 8637587) B8637587
theorem B3838927 : Blo 2273435 3838927 := bstep (se 1 (by rfl) ⟨2879195, by rfl⟩ : syracuseStep 3838927 = 5758391) B5758391
theorem B5118569 : Blo 2273435 5118569 := bstep (se 2 (by rfl) ⟨1919463, by rfl⟩ : syracuseStep 5118569 = 3838927) B3838927
theorem B3412379 : Blo 2273435 3412379 := bstep (se 1 (by rfl) ⟨2559284, by rfl⟩ : syracuseStep 3412379 = 5118569) B5118569
theorem B2274919 : Blo 2273435 2274919 := bstep (se 1 (by rfl) ⟨1706189, by rfl⟩ : syracuseStep 2274919 = 3412379) B3412379
theorem B2559289 : Blo 2273435 2559289 := bbase (se 2 (by rfl) ⟨959733, by rfl⟩ : syracuseStep 2559289 = 1919467) (by norm_num)
theorem B3412385 : Blo 2273435 3412385 := bstep (se 2 (by rfl) ⟨1279644, by rfl⟩ : syracuseStep 3412385 = 2559289) B2559289
theorem B2274923 : Blo 2273435 2274923 := bstep (se 1 (by rfl) ⟨1706192, by rfl⟩ : syracuseStep 2274923 = 3412385) B3412385
theorem B6478213 : Blo 2273435 6478213 := bbase (se 4 (by rfl) ⟨607332, by rfl⟩ : syracuseStep 6478213 = 1214665) (by norm_num)
theorem B8637617 : Blo 2273435 8637617 := bstep (se 2 (by rfl) ⟨3239106, by rfl⟩ : syracuseStep 8637617 = 6478213) B6478213
theorem B5758411 : Blo 2273435 5758411 := bstep (se 1 (by rfl) ⟨4318808, by rfl⟩ : syracuseStep 5758411 = 8637617) B8637617
theorem B7677881 : Blo 2273435 7677881 := bstep (se 2 (by rfl) ⟨2879205, by rfl⟩ : syracuseStep 7677881 = 5758411) B5758411
theorem B5118587 : Blo 2273435 5118587 := bstep (se 1 (by rfl) ⟨3838940, by rfl⟩ : syracuseStep 5118587 = 7677881) B7677881
theorem B3412391 : Blo 2273435 3412391 := bstep (se 1 (by rfl) ⟨2559293, by rfl⟩ : syracuseStep 3412391 = 5118587) B5118587
theorem B2274927 : Blo 2273435 2274927 := bstep (se 1 (by rfl) ⟨1706195, by rfl⟩ : syracuseStep 2274927 = 3412391) B3412391
theorem B3412397 : Blo 2273435 3412397 := bbase (se 3 (by rfl) ⟨639824, by rfl⟩ : syracuseStep 3412397 = 1279649) (by norm_num)
theorem B2274931 : Blo 2273435 2274931 := bstep (se 1 (by rfl) ⟨1706198, by rfl⟩ : syracuseStep 2274931 = 3412397) B3412397
theorem B5118605 : Blo 2273435 5118605 := bbase (se 3 (by rfl) ⟨959738, by rfl⟩ : syracuseStep 5118605 = 1919477) (by norm_num)
theorem B3412403 : Blo 2273435 3412403 := bstep (se 1 (by rfl) ⟨2559302, by rfl⟩ : syracuseStep 3412403 = 5118605) B5118605
theorem B2274935 : Blo 2273435 2274935 := bstep (se 1 (by rfl) ⟨1706201, by rfl⟩ : syracuseStep 2274935 = 3412403) B3412403
theorem B2879221 : Blo 2273435 2879221 := bbase (se 5 (by rfl) ⟨134963, by rfl⟩ : syracuseStep 2879221 = 269927) (by norm_num)
theorem B3838961 : Blo 2273435 3838961 := bstep (se 2 (by rfl) ⟨1439610, by rfl⟩ : syracuseStep 3838961 = 2879221) B2879221
theorem B2559307 : Blo 2273435 2559307 := bstep (se 1 (by rfl) ⟨1919480, by rfl⟩ : syracuseStep 2559307 = 3838961) B3838961
theorem B3412409 : Blo 2273435 3412409 := bstep (se 2 (by rfl) ⟨1279653, by rfl⟩ : syracuseStep 3412409 = 2559307) B2559307
theorem B2274939 : Blo 2273435 2274939 := bstep (se 1 (by rfl) ⟨1706204, by rfl⟩ : syracuseStep 2274939 = 3412409) B3412409
theorem B6149285 : Blo 2273435 6149285 := bbase (se 4 (by rfl) ⟨576495, by rfl⟩ : syracuseStep 6149285 = 1152991) (by norm_num)
theorem B4099523 : Blo 2273435 4099523 := bstep (se 1 (by rfl) ⟨3074642, by rfl⟩ : syracuseStep 4099523 = 6149285) B6149285
theorem B43728245 : Blo 2273435 43728245 := bstep (se 5 (by rfl) ⟨2049761, by rfl⟩ : syracuseStep 43728245 = 4099523) B4099523
theorem B29152163 : Blo 2273435 29152163 := bstep (se 1 (by rfl) ⟨21864122, by rfl⟩ : syracuseStep 29152163 = 43728245) B43728245
theorem B19434775 : Blo 2273435 19434775 := bstep (se 1 (by rfl) ⟨14576081, by rfl⟩ : syracuseStep 19434775 = 29152163) B29152163
theorem B25913033 : Blo 2273435 25913033 := bstep (se 2 (by rfl) ⟨9717387, by rfl⟩ : syracuseStep 25913033 = 19434775) B19434775
theorem B17275355 : Blo 2273435 17275355 := bstep (se 1 (by rfl) ⟨12956516, by rfl⟩ : syracuseStep 17275355 = 25913033) B25913033
theorem B11516903 : Blo 2273435 11516903 := bstep (se 1 (by rfl) ⟨8637677, by rfl⟩ : syracuseStep 11516903 = 17275355) B17275355
theorem B7677935 : Blo 2273435 7677935 := bstep (se 1 (by rfl) ⟨5758451, by rfl⟩ : syracuseStep 7677935 = 11516903) B11516903
theorem B5118623 : Blo 2273435 5118623 := bstep (se 1 (by rfl) ⟨3838967, by rfl⟩ : syracuseStep 5118623 = 7677935) B7677935
theorem B3412415 : Blo 2273435 3412415 := bstep (se 1 (by rfl) ⟨2559311, by rfl⟩ : syracuseStep 3412415 = 5118623) B5118623
theorem B2274943 : Blo 2273435 2274943 := bstep (se 1 (by rfl) ⟨1706207, by rfl⟩ : syracuseStep 2274943 = 3412415) B3412415
theorem B3412421 : Blo 2273435 3412421 := bbase (se 4 (by rfl) ⟨319914, by rfl⟩ : syracuseStep 3412421 = 639829) (by norm_num)
theorem B2274947 : Blo 2273435 2274947 := bstep (se 1 (by rfl) ⟨1706210, by rfl⟩ : syracuseStep 2274947 = 3412421) B3412421
theorem B3838981 : Blo 2273435 3838981 := bbase (se 4 (by rfl) ⟨359904, by rfl⟩ : syracuseStep 3838981 = 719809) (by norm_num)
theorem B5118641 : Blo 2273435 5118641 := bstep (se 2 (by rfl) ⟨1919490, by rfl⟩ : syracuseStep 5118641 = 3838981) B3838981
theorem B3412427 : Blo 2273435 3412427 := bstep (se 1 (by rfl) ⟨2559320, by rfl⟩ : syracuseStep 3412427 = 5118641) B5118641
theorem B2274951 : Blo 2273435 2274951 := bstep (se 1 (by rfl) ⟨1706213, by rfl⟩ : syracuseStep 2274951 = 3412427) B3412427
theorem B2559325 : Blo 2273435 2559325 := bbase (se 3 (by rfl) ⟨479873, by rfl⟩ : syracuseStep 2559325 = 959747) (by norm_num)
theorem B3412433 : Blo 2273435 3412433 := bstep (se 2 (by rfl) ⟨1279662, by rfl⟩ : syracuseStep 3412433 = 2559325) B2559325
theorem B2274955 : Blo 2273435 2274955 := bstep (se 1 (by rfl) ⟨1706216, by rfl⟩ : syracuseStep 2274955 = 3412433) B3412433
theorem B7677989 : Blo 2273435 7677989 := bbase (se 4 (by rfl) ⟨719811, by rfl⟩ : syracuseStep 7677989 = 1439623) (by norm_num)
theorem B5118659 : Blo 2273435 5118659 := bstep (se 1 (by rfl) ⟨3838994, by rfl⟩ : syracuseStep 5118659 = 7677989) B7677989
theorem B3412439 : Blo 2273435 3412439 := bstep (se 1 (by rfl) ⟨2559329, by rfl⟩ : syracuseStep 3412439 = 5118659) B5118659
theorem B2274959 : Blo 2273435 2274959 := bstep (se 1 (by rfl) ⟨1706219, by rfl⟩ : syracuseStep 2274959 = 3412439) B3412439
theorem B3412445 : Blo 2273435 3412445 := bbase (se 3 (by rfl) ⟨639833, by rfl⟩ : syracuseStep 3412445 = 1279667) (by norm_num)
theorem B2274963 : Blo 2273435 2274963 := bstep (se 1 (by rfl) ⟨1706222, by rfl⟩ : syracuseStep 2274963 = 3412445) B3412445
theorem B5118677 : Blo 2273435 5118677 := bbase (se 7 (by rfl) ⟨59984, by rfl⟩ : syracuseStep 5118677 = 119969) (by norm_num)
theorem B3412451 : Blo 2273435 3412451 := bstep (se 1 (by rfl) ⟨2559338, by rfl⟩ : syracuseStep 3412451 = 5118677) B5118677
theorem B2274967 : Blo 2273435 2274967 := bstep (se 1 (by rfl) ⟨1706225, by rfl⟩ : syracuseStep 2274967 = 3412451) B3412451
theorem B9717509 : Blo 2273435 9717509 := bbase (se 4 (by rfl) ⟨911016, by rfl⟩ : syracuseStep 9717509 = 1822033) (by norm_num)
theorem B6478339 : Blo 2273435 6478339 := bstep (se 1 (by rfl) ⟨4858754, by rfl⟩ : syracuseStep 6478339 = 9717509) B9717509
theorem B8637785 : Blo 2273435 8637785 := bstep (se 2 (by rfl) ⟨3239169, by rfl⟩ : syracuseStep 8637785 = 6478339) B6478339
theorem B5758523 : Blo 2273435 5758523 := bstep (se 1 (by rfl) ⟨4318892, by rfl⟩ : syracuseStep 5758523 = 8637785) B8637785
theorem B3839015 : Blo 2273435 3839015 := bstep (se 1 (by rfl) ⟨2879261, by rfl⟩ : syracuseStep 3839015 = 5758523) B5758523
theorem B2559343 : Blo 2273435 2559343 := bstep (se 1 (by rfl) ⟨1919507, by rfl⟩ : syracuseStep 2559343 = 3839015) B3839015
theorem B3412457 : Blo 2273435 3412457 := bstep (se 2 (by rfl) ⟨1279671, by rfl⟩ : syracuseStep 3412457 = 2559343) B2559343
theorem B2274971 : Blo 2273435 2274971 := bstep (se 1 (by rfl) ⟨1706228, by rfl⟩ : syracuseStep 2274971 = 3412457) B3412457
theorem B14775157 : Blo 2273435 14775157 := bbase (se 5 (by rfl) ⟨692585, by rfl⟩ : syracuseStep 14775157 = 1385171) (by norm_num)
theorem B19700209 : Blo 2273435 19700209 := bstep (se 2 (by rfl) ⟨7387578, by rfl⟩ : syracuseStep 19700209 = 14775157) B14775157
theorem B26266945 : Blo 2273435 26266945 := bstep (se 2 (by rfl) ⟨9850104, by rfl⟩ : syracuseStep 26266945 = 19700209) B19700209
theorem B35022593 : Blo 2273435 35022593 := bstep (se 2 (by rfl) ⟨13133472, by rfl⟩ : syracuseStep 35022593 = 26266945) B26266945
theorem B23348395 : Blo 2273435 23348395 := bstep (se 1 (by rfl) ⟨17511296, by rfl⟩ : syracuseStep 23348395 = 35022593) B35022593
theorem B124524773 : Blo 2273435 124524773 := bstep (se 4 (by rfl) ⟨11674197, by rfl⟩ : syracuseStep 124524773 = 23348395) B23348395
theorem B83016515 : Blo 2273435 83016515 := bstep (se 1 (by rfl) ⟨62262386, by rfl⟩ : syracuseStep 83016515 = 124524773) B124524773
theorem B55344343 : Blo 2273435 55344343 := bstep (se 1 (by rfl) ⟨41508257, by rfl⟩ : syracuseStep 55344343 = 83016515) B83016515
theorem B73792457 : Blo 2273435 73792457 := bstep (se 2 (by rfl) ⟨27672171, by rfl⟩ : syracuseStep 73792457 = 55344343) B55344343
theorem B49194971 : Blo 2273435 49194971 := bstep (se 1 (by rfl) ⟨36896228, by rfl⟩ : syracuseStep 49194971 = 73792457) B73792457
theorem B32796647 : Blo 2273435 32796647 := bstep (se 1 (by rfl) ⟨24597485, by rfl⟩ : syracuseStep 32796647 = 49194971) B49194971
theorem B21864431 : Blo 2273435 21864431 := bstep (se 1 (by rfl) ⟨16398323, by rfl⟩ : syracuseStep 21864431 = 32796647) B32796647
theorem B14576287 : Blo 2273435 14576287 := bstep (se 1 (by rfl) ⟨10932215, by rfl⟩ : syracuseStep 14576287 = 21864431) B21864431
theorem B19435049 : Blo 2273435 19435049 := bstep (se 2 (by rfl) ⟨7288143, by rfl⟩ : syracuseStep 19435049 = 14576287) B14576287
theorem B12956699 : Blo 2273435 12956699 := bstep (se 1 (by rfl) ⟨9717524, by rfl⟩ : syracuseStep 12956699 = 19435049) B19435049
theorem B8637799 : Blo 2273435 8637799 := bstep (se 1 (by rfl) ⟨6478349, by rfl⟩ : syracuseStep 8637799 = 12956699) B12956699
theorem B11517065 : Blo 2273435 11517065 := bstep (se 2 (by rfl) ⟨4318899, by rfl⟩ : syracuseStep 11517065 = 8637799) B8637799
theorem B7678043 : Blo 2273435 7678043 := bstep (se 1 (by rfl) ⟨5758532, by rfl⟩ : syracuseStep 7678043 = 11517065) B11517065
theorem B5118695 : Blo 2273435 5118695 := bstep (se 1 (by rfl) ⟨3839021, by rfl⟩ : syracuseStep 5118695 = 7678043) B7678043
theorem B3412463 : Blo 2273435 3412463 := bstep (se 1 (by rfl) ⟨2559347, by rfl⟩ : syracuseStep 3412463 = 5118695) B5118695
theorem B2274975 : Blo 2273435 2274975 := bstep (se 1 (by rfl) ⟨1706231, by rfl⟩ : syracuseStep 2274975 = 3412463) B3412463
theorem B3412469 : Blo 2273435 3412469 := bbase (se 5 (by rfl) ⟨159959, by rfl⟩ : syracuseStep 3412469 = 319919) (by norm_num)
theorem B2274979 : Blo 2273435 2274979 := bstep (se 1 (by rfl) ⟨1706234, by rfl⟩ : syracuseStep 2274979 = 3412469) B3412469
theorem B6478373 : Blo 2273435 6478373 := bbase (se 4 (by rfl) ⟨607347, by rfl⟩ : syracuseStep 6478373 = 1214695) (by norm_num)
theorem B4318915 : Blo 2273435 4318915 := bstep (se 1 (by rfl) ⟨3239186, by rfl⟩ : syracuseStep 4318915 = 6478373) B6478373
theorem B5758553 : Blo 2273435 5758553 := bstep (se 2 (by rfl) ⟨2159457, by rfl⟩ : syracuseStep 5758553 = 4318915) B4318915
theorem B3839035 : Blo 2273435 3839035 := bstep (se 1 (by rfl) ⟨2879276, by rfl⟩ : syracuseStep 3839035 = 5758553) B5758553
theorem B5118713 : Blo 2273435 5118713 := bstep (se 2 (by rfl) ⟨1919517, by rfl⟩ : syracuseStep 5118713 = 3839035) B3839035
theorem B3412475 : Blo 2273435 3412475 := bstep (se 1 (by rfl) ⟨2559356, by rfl⟩ : syracuseStep 3412475 = 5118713) B5118713
theorem B2274983 : Blo 2273435 2274983 := bstep (se 1 (by rfl) ⟨1706237, by rfl⟩ : syracuseStep 2274983 = 3412475) B3412475
theorem B2559361 : Blo 2273435 2559361 := bbase (se 2 (by rfl) ⟨959760, by rfl⟩ : syracuseStep 2559361 = 1919521) (by norm_num)
theorem B3412481 : Blo 2273435 3412481 := bstep (se 2 (by rfl) ⟨1279680, by rfl⟩ : syracuseStep 3412481 = 2559361) B2559361
theorem B2274987 : Blo 2273435 2274987 := bstep (se 1 (by rfl) ⟨1706240, by rfl⟩ : syracuseStep 2274987 = 3412481) B3412481
theorem B5758573 : Blo 2273435 5758573 := bbase (se 3 (by rfl) ⟨1079732, by rfl⟩ : syracuseStep 5758573 = 2159465) (by norm_num)
theorem B7678097 : Blo 2273435 7678097 := bstep (se 2 (by rfl) ⟨2879286, by rfl⟩ : syracuseStep 7678097 = 5758573) B5758573
theorem B5118731 : Blo 2273435 5118731 := bstep (se 1 (by rfl) ⟨3839048, by rfl⟩ : syracuseStep 5118731 = 7678097) B7678097
theorem B3412487 : Blo 2273435 3412487 := bstep (se 1 (by rfl) ⟨2559365, by rfl⟩ : syracuseStep 3412487 = 5118731) B5118731
theorem B2274991 : Blo 2273435 2274991 := bstep (se 1 (by rfl) ⟨1706243, by rfl⟩ : syracuseStep 2274991 = 3412487) B3412487
theorem B3412493 : Blo 2273435 3412493 := bbase (se 3 (by rfl) ⟨639842, by rfl⟩ : syracuseStep 3412493 = 1279685) (by norm_num)
theorem B2274995 : Blo 2273435 2274995 := bstep (se 1 (by rfl) ⟨1706246, by rfl⟩ : syracuseStep 2274995 = 3412493) B3412493
theorem B5118749 : Blo 2273435 5118749 := bbase (se 3 (by rfl) ⟨959765, by rfl⟩ : syracuseStep 5118749 = 1919531) (by norm_num)
theorem B3412499 : Blo 2273435 3412499 := bstep (se 1 (by rfl) ⟨2559374, by rfl⟩ : syracuseStep 3412499 = 5118749) B5118749
theorem B2274999 : Blo 2273435 2274999 := bstep (se 1 (by rfl) ⟨1706249, by rfl⟩ : syracuseStep 2274999 = 3412499) B3412499
theorem B3839069 : Blo 2273435 3839069 := bbase (se 3 (by rfl) ⟨719825, by rfl⟩ : syracuseStep 3839069 = 1439651) (by norm_num)
theorem B2559379 : Blo 2273435 2559379 := bstep (se 1 (by rfl) ⟨1919534, by rfl⟩ : syracuseStep 2559379 = 3839069) B3839069
theorem B3412505 : Blo 2273435 3412505 := bstep (se 2 (by rfl) ⟨1279689, by rfl⟩ : syracuseStep 3412505 = 2559379) B2559379
theorem B2275003 : Blo 2273435 2275003 := bstep (se 1 (by rfl) ⟨1706252, by rfl⟩ : syracuseStep 2275003 = 3412505) B3412505
theorem B13494485 : Blo 2273435 13494485 := bbase (se 7 (by rfl) ⟨158138, by rfl⟩ : syracuseStep 13494485 = 316277) (by norm_num)
theorem B35985293 : Blo 2273435 35985293 := bstep (se 3 (by rfl) ⟨6747242, by rfl⟩ : syracuseStep 35985293 = 13494485) B13494485
theorem B23990195 : Blo 2273435 23990195 := bstep (se 1 (by rfl) ⟨17992646, by rfl⟩ : syracuseStep 23990195 = 35985293) B35985293
theorem B15993463 : Blo 2273435 15993463 := bstep (se 1 (by rfl) ⟨11995097, by rfl⟩ : syracuseStep 15993463 = 23990195) B23990195
theorem B21324617 : Blo 2273435 21324617 := bstep (se 2 (by rfl) ⟨7996731, by rfl⟩ : syracuseStep 21324617 = 15993463) B15993463
theorem B14216411 : Blo 2273435 14216411 := bstep (se 1 (by rfl) ⟨10662308, by rfl⟩ : syracuseStep 14216411 = 21324617) B21324617
theorem B37910429 : Blo 2273435 37910429 := bstep (se 3 (by rfl) ⟨7108205, by rfl⟩ : syracuseStep 37910429 = 14216411) B14216411
theorem B25273619 : Blo 2273435 25273619 := bstep (se 1 (by rfl) ⟨18955214, by rfl⟩ : syracuseStep 25273619 = 37910429) B37910429
theorem B16849079 : Blo 2273435 16849079 := bstep (se 1 (by rfl) ⟨12636809, by rfl⟩ : syracuseStep 16849079 = 25273619) B25273619
theorem B11232719 : Blo 2273435 11232719 := bstep (se 1 (by rfl) ⟨8424539, by rfl⟩ : syracuseStep 11232719 = 16849079) B16849079
theorem B7488479 : Blo 2273435 7488479 := bstep (se 1 (by rfl) ⟨5616359, by rfl⟩ : syracuseStep 7488479 = 11232719) B11232719
theorem B4992319 : Blo 2273435 4992319 := bstep (se 1 (by rfl) ⟨3744239, by rfl⟩ : syracuseStep 4992319 = 7488479) B7488479
theorem B26625701 : Blo 2273435 26625701 := bstep (se 4 (by rfl) ⟨2496159, by rfl⟩ : syracuseStep 26625701 = 4992319) B4992319
theorem B17750467 : Blo 2273435 17750467 := bstep (se 1 (by rfl) ⟨13312850, by rfl⟩ : syracuseStep 17750467 = 26625701) B26625701
theorem B94669157 : Blo 2273435 94669157 := bstep (se 4 (by rfl) ⟨8875233, by rfl⟩ : syracuseStep 94669157 = 17750467) B17750467
theorem B63112771 : Blo 2273435 63112771 := bstep (se 1 (by rfl) ⟨47334578, by rfl⟩ : syracuseStep 63112771 = 94669157) B94669157
theorem B84150361 : Blo 2273435 84150361 := bstep (se 2 (by rfl) ⟨31556385, by rfl⟩ : syracuseStep 84150361 = 63112771) B63112771
theorem B112200481 : Blo 2273435 112200481 := bstep (se 2 (by rfl) ⟨42075180, by rfl⟩ : syracuseStep 112200481 = 84150361) B84150361
theorem B149600641 : Blo 2273435 149600641 := bstep (se 2 (by rfl) ⟨56100240, by rfl⟩ : syracuseStep 149600641 = 112200481) B112200481
theorem B199467521 : Blo 2273435 199467521 := bstep (se 2 (by rfl) ⟨74800320, by rfl⟩ : syracuseStep 199467521 = 149600641) B149600641
theorem B132978347 : Blo 2273435 132978347 := bstep (se 1 (by rfl) ⟨99733760, by rfl⟩ : syracuseStep 132978347 = 199467521) B199467521
theorem B88652231 : Blo 2273435 88652231 := bstep (se 1 (by rfl) ⟨66489173, by rfl⟩ : syracuseStep 88652231 = 132978347) B132978347
theorem B59101487 : Blo 2273435 59101487 := bstep (se 1 (by rfl) ⟨44326115, by rfl⟩ : syracuseStep 59101487 = 88652231) B88652231
theorem B39400991 : Blo 2273435 39400991 := bstep (se 1 (by rfl) ⟨29550743, by rfl⟩ : syracuseStep 39400991 = 59101487) B59101487
theorem B26267327 : Blo 2273435 26267327 := bstep (se 1 (by rfl) ⟨19700495, by rfl⟩ : syracuseStep 26267327 = 39400991) B39400991
theorem B17511551 : Blo 2273435 17511551 := bstep (se 1 (by rfl) ⟨13133663, by rfl⟩ : syracuseStep 17511551 = 26267327) B26267327
theorem B11674367 : Blo 2273435 11674367 := bstep (se 1 (by rfl) ⟨8755775, by rfl⟩ : syracuseStep 11674367 = 17511551) B17511551
theorem B7782911 : Blo 2273435 7782911 := bstep (se 1 (by rfl) ⟨5837183, by rfl⟩ : syracuseStep 7782911 = 11674367) B11674367
theorem B5188607 : Blo 2273435 5188607 := bstep (se 1 (by rfl) ⟨3891455, by rfl⟩ : syracuseStep 5188607 = 7782911) B7782911
theorem B3459071 : Blo 2273435 3459071 := bstep (se 1 (by rfl) ⟨2594303, by rfl⟩ : syracuseStep 3459071 = 5188607) B5188607
theorem B9224189 : Blo 2273435 9224189 := bstep (se 3 (by rfl) ⟨1729535, by rfl⟩ : syracuseStep 9224189 = 3459071) B3459071
theorem B6149459 : Blo 2273435 6149459 := bstep (se 1 (by rfl) ⟨4612094, by rfl⟩ : syracuseStep 6149459 = 9224189) B9224189
theorem B4099639 : Blo 2273435 4099639 := bstep (se 1 (by rfl) ⟨3074729, by rfl⟩ : syracuseStep 4099639 = 6149459) B6149459
theorem B5466185 : Blo 2273435 5466185 := bstep (se 2 (by rfl) ⟨2049819, by rfl⟩ : syracuseStep 5466185 = 4099639) B4099639
theorem B3644123 : Blo 2273435 3644123 := bstep (se 1 (by rfl) ⟨2733092, by rfl⟩ : syracuseStep 3644123 = 5466185) B5466185
theorem B9717661 : Blo 2273435 9717661 := bstep (se 3 (by rfl) ⟨1822061, by rfl⟩ : syracuseStep 9717661 = 3644123) B3644123
theorem B12956881 : Blo 2273435 12956881 := bstep (se 2 (by rfl) ⟨4858830, by rfl⟩ : syracuseStep 12956881 = 9717661) B9717661
theorem B17275841 : Blo 2273435 17275841 := bstep (se 2 (by rfl) ⟨6478440, by rfl⟩ : syracuseStep 17275841 = 12956881) B12956881
theorem B11517227 : Blo 2273435 11517227 := bstep (se 1 (by rfl) ⟨8637920, by rfl⟩ : syracuseStep 11517227 = 17275841) B17275841
theorem B7678151 : Blo 2273435 7678151 := bstep (se 1 (by rfl) ⟨5758613, by rfl⟩ : syracuseStep 7678151 = 11517227) B11517227
theorem B5118767 : Blo 2273435 5118767 := bstep (se 1 (by rfl) ⟨3839075, by rfl⟩ : syracuseStep 5118767 = 7678151) B7678151
theorem B3412511 : Blo 2273435 3412511 := bstep (se 1 (by rfl) ⟨2559383, by rfl⟩ : syracuseStep 3412511 = 5118767) B5118767
theorem B2275007 : Blo 2273435 2275007 := bstep (se 1 (by rfl) ⟨1706255, by rfl⟩ : syracuseStep 2275007 = 3412511) B3412511
theorem B3412517 : Blo 2273435 3412517 := bbase (se 4 (by rfl) ⟨319923, by rfl⟩ : syracuseStep 3412517 = 639847) (by norm_num)
theorem B2275011 : Blo 2273435 2275011 := bstep (se 1 (by rfl) ⟨1706258, by rfl⟩ : syracuseStep 2275011 = 3412517) B3412517
theorem B2879317 : Blo 2273435 2879317 := bbase (se 9 (by rfl) ⟨8435, by rfl⟩ : syracuseStep 2879317 = 16871) (by norm_num)
theorem B3839089 : Blo 2273435 3839089 := bstep (se 2 (by rfl) ⟨1439658, by rfl⟩ : syracuseStep 3839089 = 2879317) B2879317
theorem B5118785 : Blo 2273435 5118785 := bstep (se 2 (by rfl) ⟨1919544, by rfl⟩ : syracuseStep 5118785 = 3839089) B3839089
theorem B3412523 : Blo 2273435 3412523 := bstep (se 1 (by rfl) ⟨2559392, by rfl⟩ : syracuseStep 3412523 = 5118785) B5118785
theorem B2275015 : Blo 2273435 2275015 := bstep (se 1 (by rfl) ⟨1706261, by rfl⟩ : syracuseStep 2275015 = 3412523) B3412523
theorem B2559397 : Blo 2273435 2559397 := bbase (se 4 (by rfl) ⟨239943, by rfl⟩ : syracuseStep 2559397 = 479887) (by norm_num)
theorem B3412529 : Blo 2273435 3412529 := bstep (se 2 (by rfl) ⟨1279698, by rfl⟩ : syracuseStep 3412529 = 2559397) B2559397
theorem B2275019 : Blo 2273435 2275019 := bstep (se 1 (by rfl) ⟨1706264, by rfl⟩ : syracuseStep 2275019 = 3412529) B3412529
theorem B14576597 : Blo 2273435 14576597 := bbase (se 7 (by rfl) ⟨170819, by rfl⟩ : syracuseStep 14576597 = 341639) (by norm_num)
theorem B9717731 : Blo 2273435 9717731 := bstep (se 1 (by rfl) ⟨7288298, by rfl⟩ : syracuseStep 9717731 = 14576597) B14576597
theorem B6478487 : Blo 2273435 6478487 := bstep (se 1 (by rfl) ⟨4858865, by rfl⟩ : syracuseStep 6478487 = 9717731) B9717731
theorem B4318991 : Blo 2273435 4318991 := bstep (se 1 (by rfl) ⟨3239243, by rfl⟩ : syracuseStep 4318991 = 6478487) B6478487
theorem B2879327 : Blo 2273435 2879327 := bstep (se 1 (by rfl) ⟨2159495, by rfl⟩ : syracuseStep 2879327 = 4318991) B4318991
theorem B7678205 : Blo 2273435 7678205 := bstep (se 3 (by rfl) ⟨1439663, by rfl⟩ : syracuseStep 7678205 = 2879327) B2879327
theorem B5118803 : Blo 2273435 5118803 := bstep (se 1 (by rfl) ⟨3839102, by rfl⟩ : syracuseStep 5118803 = 7678205) B7678205
theorem B3412535 : Blo 2273435 3412535 := bstep (se 1 (by rfl) ⟨2559401, by rfl⟩ : syracuseStep 3412535 = 5118803) B5118803
theorem B2275023 : Blo 2273435 2275023 := bstep (se 1 (by rfl) ⟨1706267, by rfl⟩ : syracuseStep 2275023 = 3412535) B3412535
theorem B3412541 : Blo 2273435 3412541 := bbase (se 3 (by rfl) ⟨639851, by rfl⟩ : syracuseStep 3412541 = 1279703) (by norm_num)
theorem B2275027 : Blo 2273435 2275027 := bstep (se 1 (by rfl) ⟨1706270, by rfl⟩ : syracuseStep 2275027 = 3412541) B3412541
theorem B5118821 : Blo 2273435 5118821 := bbase (se 4 (by rfl) ⟨479889, by rfl⟩ : syracuseStep 5118821 = 959779) (by norm_num)
theorem B3412547 : Blo 2273435 3412547 := bstep (se 1 (by rfl) ⟨2559410, by rfl⟩ : syracuseStep 3412547 = 5118821) B5118821
theorem B2275031 : Blo 2273435 2275031 := bstep (se 1 (by rfl) ⟨1706273, by rfl⟩ : syracuseStep 2275031 = 3412547) B3412547
theorem B5758685 : Blo 2273435 5758685 := bbase (se 3 (by rfl) ⟨1079753, by rfl⟩ : syracuseStep 5758685 = 2159507) (by norm_num)
theorem B3839123 : Blo 2273435 3839123 := bstep (se 1 (by rfl) ⟨2879342, by rfl⟩ : syracuseStep 3839123 = 5758685) B5758685
theorem B2559415 : Blo 2273435 2559415 := bstep (se 1 (by rfl) ⟨1919561, by rfl⟩ : syracuseStep 2559415 = 3839123) B3839123
theorem B3412553 : Blo 2273435 3412553 := bstep (se 2 (by rfl) ⟨1279707, by rfl⟩ : syracuseStep 3412553 = 2559415) B2559415
theorem B2275035 : Blo 2273435 2275035 := bstep (se 1 (by rfl) ⟨1706276, by rfl⟩ : syracuseStep 2275035 = 3412553) B3412553
theorem B4319021 : Blo 2273435 4319021 := bbase (se 3 (by rfl) ⟨809816, by rfl⟩ : syracuseStep 4319021 = 1619633) (by norm_num)
theorem B11517389 : Blo 2273435 11517389 := bstep (se 3 (by rfl) ⟨2159510, by rfl⟩ : syracuseStep 11517389 = 4319021) B4319021
theorem B7678259 : Blo 2273435 7678259 := bstep (se 1 (by rfl) ⟨5758694, by rfl⟩ : syracuseStep 7678259 = 11517389) B11517389
theorem B5118839 : Blo 2273435 5118839 := bstep (se 1 (by rfl) ⟨3839129, by rfl⟩ : syracuseStep 5118839 = 7678259) B7678259
theorem B3412559 : Blo 2273435 3412559 := bstep (se 1 (by rfl) ⟨2559419, by rfl⟩ : syracuseStep 3412559 = 5118839) B5118839
theorem B2275039 : Blo 2273435 2275039 := bstep (se 1 (by rfl) ⟨1706279, by rfl⟩ : syracuseStep 2275039 = 3412559) B3412559
theorem B3412565 : Blo 2273435 3412565 := bbase (se 8 (by rfl) ⟨19995, by rfl⟩ : syracuseStep 3412565 = 39991) (by norm_num)
theorem B2275043 : Blo 2273435 2275043 := bstep (se 1 (by rfl) ⟨1706282, by rfl⟩ : syracuseStep 2275043 = 3412565) B3412565
theorem B2530261 : Blo 2273435 2530261 := bbase (se 7 (by rfl) ⟨29651, by rfl⟩ : syracuseStep 2530261 = 59303) (by norm_num)
theorem B13494725 : Blo 2273435 13494725 := bstep (se 4 (by rfl) ⟨1265130, by rfl⟩ : syracuseStep 13494725 = 2530261) B2530261
theorem B8996483 : Blo 2273435 8996483 := bstep (se 1 (by rfl) ⟨6747362, by rfl⟩ : syracuseStep 8996483 = 13494725) B13494725
theorem B5997655 : Blo 2273435 5997655 := bstep (se 1 (by rfl) ⟨4498241, by rfl⟩ : syracuseStep 5997655 = 8996483) B8996483
theorem B7996873 : Blo 2273435 7996873 := bstep (se 2 (by rfl) ⟨2998827, by rfl⟩ : syracuseStep 7996873 = 5997655) B5997655
theorem B10662497 : Blo 2273435 10662497 := bstep (se 2 (by rfl) ⟨3998436, by rfl⟩ : syracuseStep 10662497 = 7996873) B7996873
theorem B7108331 : Blo 2273435 7108331 := bstep (se 1 (by rfl) ⟨5331248, by rfl⟩ : syracuseStep 7108331 = 10662497) B10662497
theorem B18955549 : Blo 2273435 18955549 := bstep (se 3 (by rfl) ⟨3554165, by rfl⟩ : syracuseStep 18955549 = 7108331) B7108331
theorem B25274065 : Blo 2273435 25274065 := bstep (se 2 (by rfl) ⟨9477774, by rfl⟩ : syracuseStep 25274065 = 18955549) B18955549
theorem B33698753 : Blo 2273435 33698753 := bstep (se 2 (by rfl) ⟨12637032, by rfl⟩ : syracuseStep 33698753 = 25274065) B25274065
theorem B22465835 : Blo 2273435 22465835 := bstep (se 1 (by rfl) ⟨16849376, by rfl⟩ : syracuseStep 22465835 = 33698753) B33698753
theorem B14977223 : Blo 2273435 14977223 := bstep (se 1 (by rfl) ⟨11232917, by rfl⟩ : syracuseStep 14977223 = 22465835) B22465835
theorem B9984815 : Blo 2273435 9984815 := bstep (se 1 (by rfl) ⟨7488611, by rfl⟩ : syracuseStep 9984815 = 14977223) B14977223
theorem B6656543 : Blo 2273435 6656543 := bstep (se 1 (by rfl) ⟨4992407, by rfl⟩ : syracuseStep 6656543 = 9984815) B9984815
theorem B4437695 : Blo 2273435 4437695 := bstep (se 1 (by rfl) ⟨3328271, by rfl⟩ : syracuseStep 4437695 = 6656543) B6656543
theorem B2958463 : Blo 2273435 2958463 := bstep (se 1 (by rfl) ⟨2218847, by rfl⟩ : syracuseStep 2958463 = 4437695) B4437695
theorem B15778469 : Blo 2273435 15778469 := bstep (se 4 (by rfl) ⟨1479231, by rfl⟩ : syracuseStep 15778469 = 2958463) B2958463
theorem B10518979 : Blo 2273435 10518979 := bstep (se 1 (by rfl) ⟨7889234, by rfl⟩ : syracuseStep 10518979 = 15778469) B15778469
theorem B14025305 : Blo 2273435 14025305 := bstep (se 2 (by rfl) ⟨5259489, by rfl⟩ : syracuseStep 14025305 = 10518979) B10518979
theorem B9350203 : Blo 2273435 9350203 := bstep (se 1 (by rfl) ⟨7012652, by rfl⟩ : syracuseStep 9350203 = 14025305) B14025305
theorem B12466937 : Blo 2273435 12466937 := bstep (se 2 (by rfl) ⟨4675101, by rfl⟩ : syracuseStep 12466937 = 9350203) B9350203
theorem B8311291 : Blo 2273435 8311291 := bstep (se 1 (by rfl) ⟨6233468, by rfl⟩ : syracuseStep 8311291 = 12466937) B12466937
theorem B177307541 : Blo 2273435 177307541 := bstep (se 6 (by rfl) ⟨4155645, by rfl⟩ : syracuseStep 177307541 = 8311291) B8311291
theorem B118205027 : Blo 2273435 118205027 := bstep (se 1 (by rfl) ⟨88653770, by rfl⟩ : syracuseStep 118205027 = 177307541) B177307541
theorem B78803351 : Blo 2273435 78803351 := bstep (se 1 (by rfl) ⟨59102513, by rfl⟩ : syracuseStep 78803351 = 118205027) B118205027
theorem B52535567 : Blo 2273435 52535567 := bstep (se 1 (by rfl) ⟨39401675, by rfl⟩ : syracuseStep 52535567 = 78803351) B78803351
theorem B35023711 : Blo 2273435 35023711 := bstep (se 1 (by rfl) ⟨26267783, by rfl⟩ : syracuseStep 35023711 = 52535567) B52535567
theorem B46698281 : Blo 2273435 46698281 := bstep (se 2 (by rfl) ⟨17511855, by rfl⟩ : syracuseStep 46698281 = 35023711) B35023711
theorem B31132187 : Blo 2273435 31132187 := bstep (se 1 (by rfl) ⟨23349140, by rfl⟩ : syracuseStep 31132187 = 46698281) B46698281
theorem B20754791 : Blo 2273435 20754791 := bstep (se 1 (by rfl) ⟨15566093, by rfl⟩ : syracuseStep 20754791 = 31132187) B31132187
theorem B13836527 : Blo 2273435 13836527 := bstep (se 1 (by rfl) ⟨10377395, by rfl⟩ : syracuseStep 13836527 = 20754791) B20754791
theorem B9224351 : Blo 2273435 9224351 := bstep (se 1 (by rfl) ⟨6918263, by rfl⟩ : syracuseStep 9224351 = 13836527) B13836527
theorem B6149567 : Blo 2273435 6149567 := bstep (se 1 (by rfl) ⟨4612175, by rfl⟩ : syracuseStep 6149567 = 9224351) B9224351
theorem B16398845 : Blo 2273435 16398845 := bstep (se 3 (by rfl) ⟨3074783, by rfl⟩ : syracuseStep 16398845 = 6149567) B6149567
theorem B10932563 : Blo 2273435 10932563 := bstep (se 1 (by rfl) ⟨8199422, by rfl⟩ : syracuseStep 10932563 = 16398845) B16398845
theorem B7288375 : Blo 2273435 7288375 := bstep (se 1 (by rfl) ⟨5466281, by rfl⟩ : syracuseStep 7288375 = 10932563) B10932563
theorem B9717833 : Blo 2273435 9717833 := bstep (se 2 (by rfl) ⟨3644187, by rfl⟩ : syracuseStep 9717833 = 7288375) B7288375
theorem B6478555 : Blo 2273435 6478555 := bstep (se 1 (by rfl) ⟨4858916, by rfl⟩ : syracuseStep 6478555 = 9717833) B9717833
theorem B8638073 : Blo 2273435 8638073 := bstep (se 2 (by rfl) ⟨3239277, by rfl⟩ : syracuseStep 8638073 = 6478555) B6478555
theorem B5758715 : Blo 2273435 5758715 := bstep (se 1 (by rfl) ⟨4319036, by rfl⟩ : syracuseStep 5758715 = 8638073) B8638073
theorem B3839143 : Blo 2273435 3839143 := bstep (se 1 (by rfl) ⟨2879357, by rfl⟩ : syracuseStep 3839143 = 5758715) B5758715
theorem B5118857 : Blo 2273435 5118857 := bstep (se 2 (by rfl) ⟨1919571, by rfl⟩ : syracuseStep 5118857 = 3839143) B3839143
theorem B3412571 : Blo 2273435 3412571 := bstep (se 1 (by rfl) ⟨2559428, by rfl⟩ : syracuseStep 3412571 = 5118857) B5118857
theorem B2275047 : Blo 2273435 2275047 := bstep (se 1 (by rfl) ⟨1706285, by rfl⟩ : syracuseStep 2275047 = 3412571) B3412571
theorem B2559433 : Blo 2273435 2559433 := bbase (se 2 (by rfl) ⟨959787, by rfl⟩ : syracuseStep 2559433 = 1919575) (by norm_num)
theorem B3412577 : Blo 2273435 3412577 := bstep (se 2 (by rfl) ⟨1279716, by rfl⟩ : syracuseStep 3412577 = 2559433) B2559433
theorem B2275051 : Blo 2273435 2275051 := bstep (se 1 (by rfl) ⟨1706288, by rfl⟩ : syracuseStep 2275051 = 3412577) B3412577
theorem B19435733 : Blo 2273435 19435733 := bbase (se 7 (by rfl) ⟨227762, by rfl⟩ : syracuseStep 19435733 = 455525) (by norm_num)
theorem B12957155 : Blo 2273435 12957155 := bstep (se 1 (by rfl) ⟨9717866, by rfl⟩ : syracuseStep 12957155 = 19435733) B19435733
theorem B8638103 : Blo 2273435 8638103 := bstep (se 1 (by rfl) ⟨6478577, by rfl⟩ : syracuseStep 8638103 = 12957155) B12957155
theorem B5758735 : Blo 2273435 5758735 := bstep (se 1 (by rfl) ⟨4319051, by rfl⟩ : syracuseStep 5758735 = 8638103) B8638103
theorem B7678313 : Blo 2273435 7678313 := bstep (se 2 (by rfl) ⟨2879367, by rfl⟩ : syracuseStep 7678313 = 5758735) B5758735
theorem B5118875 : Blo 2273435 5118875 := bstep (se 1 (by rfl) ⟨3839156, by rfl⟩ : syracuseStep 5118875 = 7678313) B7678313
theorem B3412583 : Blo 2273435 3412583 := bstep (se 1 (by rfl) ⟨2559437, by rfl⟩ : syracuseStep 3412583 = 5118875) B5118875
theorem B2275055 : Blo 2273435 2275055 := bstep (se 1 (by rfl) ⟨1706291, by rfl⟩ : syracuseStep 2275055 = 3412583) B3412583
theorem B3412589 : Blo 2273435 3412589 := bbase (se 3 (by rfl) ⟨639860, by rfl⟩ : syracuseStep 3412589 = 1279721) (by norm_num)
theorem B2275059 : Blo 2273435 2275059 := bstep (se 1 (by rfl) ⟨1706294, by rfl⟩ : syracuseStep 2275059 = 3412589) B3412589
theorem B5118893 : Blo 2273435 5118893 := bbase (se 3 (by rfl) ⟨959792, by rfl⟩ : syracuseStep 5118893 = 1919585) (by norm_num)
theorem B3412595 : Blo 2273435 3412595 := bstep (se 1 (by rfl) ⟨2559446, by rfl⟩ : syracuseStep 3412595 = 5118893) B5118893
theorem B2275063 : Blo 2273435 2275063 := bstep (se 1 (by rfl) ⟨1706297, by rfl⟩ : syracuseStep 2275063 = 3412595) B3412595
theorem B6478613 : Blo 2273435 6478613 := bbase (se 6 (by rfl) ⟨151842, by rfl⟩ : syracuseStep 6478613 = 303685) (by norm_num)
theorem B4319075 : Blo 2273435 4319075 := bstep (se 1 (by rfl) ⟨3239306, by rfl⟩ : syracuseStep 4319075 = 6478613) B6478613
theorem B2879383 : Blo 2273435 2879383 := bstep (se 1 (by rfl) ⟨2159537, by rfl⟩ : syracuseStep 2879383 = 4319075) B4319075
theorem B3839177 : Blo 2273435 3839177 := bstep (se 2 (by rfl) ⟨1439691, by rfl⟩ : syracuseStep 3839177 = 2879383) B2879383
theorem B2559451 : Blo 2273435 2559451 := bstep (se 1 (by rfl) ⟨1919588, by rfl⟩ : syracuseStep 2559451 = 3839177) B3839177
theorem B3412601 : Blo 2273435 3412601 := bstep (se 2 (by rfl) ⟨1279725, by rfl⟩ : syracuseStep 3412601 = 2559451) B2559451
theorem B2275067 : Blo 2273435 2275067 := bstep (se 1 (by rfl) ⟨1706300, by rfl⟩ : syracuseStep 2275067 = 3412601) B3412601
theorem B5916989 : Blo 2273435 5916989 := bbase (se 3 (by rfl) ⟨1109435, by rfl⟩ : syracuseStep 5916989 = 2218871) (by norm_num)
theorem B15778637 : Blo 2273435 15778637 := bstep (se 3 (by rfl) ⟨2958494, by rfl⟩ : syracuseStep 15778637 = 5916989) B5916989
theorem B10519091 : Blo 2273435 10519091 := bstep (se 1 (by rfl) ⟨7889318, by rfl⟩ : syracuseStep 10519091 = 15778637) B15778637
theorem B7012727 : Blo 2273435 7012727 := bstep (se 1 (by rfl) ⟨5259545, by rfl⟩ : syracuseStep 7012727 = 10519091) B10519091
theorem B4675151 : Blo 2273435 4675151 := bstep (se 1 (by rfl) ⟨3506363, by rfl⟩ : syracuseStep 4675151 = 7012727) B7012727
theorem B3116767 : Blo 2273435 3116767 := bstep (se 1 (by rfl) ⟨2337575, by rfl⟩ : syracuseStep 3116767 = 4675151) B4675151
theorem B4155689 : Blo 2273435 4155689 := bstep (se 2 (by rfl) ⟨1558383, by rfl⟩ : syracuseStep 4155689 = 3116767) B3116767
theorem B11081837 : Blo 2273435 11081837 := bstep (se 3 (by rfl) ⟨2077844, by rfl⟩ : syracuseStep 11081837 = 4155689) B4155689
theorem B7387891 : Blo 2273435 7387891 := bstep (se 1 (by rfl) ⟨5540918, by rfl⟩ : syracuseStep 7387891 = 11081837) B11081837
theorem B39402085 : Blo 2273435 39402085 := bstep (se 4 (by rfl) ⟨3693945, by rfl⟩ : syracuseStep 39402085 = 7387891) B7387891
theorem B52536113 : Blo 2273435 52536113 := bstep (se 2 (by rfl) ⟨19701042, by rfl⟩ : syracuseStep 52536113 = 39402085) B39402085
theorem B35024075 : Blo 2273435 35024075 := bstep (se 1 (by rfl) ⟨26268056, by rfl⟩ : syracuseStep 35024075 = 52536113) B52536113
theorem B23349383 : Blo 2273435 23349383 := bstep (se 1 (by rfl) ⟨17512037, by rfl⟩ : syracuseStep 23349383 = 35024075) B35024075
theorem B15566255 : Blo 2273435 15566255 := bstep (se 1 (by rfl) ⟨11674691, by rfl⟩ : syracuseStep 15566255 = 23349383) B23349383
theorem B10377503 : Blo 2273435 10377503 := bstep (se 1 (by rfl) ⟨7783127, by rfl⟩ : syracuseStep 10377503 = 15566255) B15566255
theorem B6918335 : Blo 2273435 6918335 := bstep (se 1 (by rfl) ⟨5188751, by rfl⟩ : syracuseStep 6918335 = 10377503) B10377503
theorem B4612223 : Blo 2273435 4612223 := bstep (se 1 (by rfl) ⟨3459167, by rfl⟩ : syracuseStep 4612223 = 6918335) B6918335
theorem B12299261 : Blo 2273435 12299261 := bstep (se 3 (by rfl) ⟨2306111, by rfl⟩ : syracuseStep 12299261 = 4612223) B4612223
theorem B32798029 : Blo 2273435 32798029 := bstep (se 3 (by rfl) ⟨6149630, by rfl⟩ : syracuseStep 32798029 = 12299261) B12299261
theorem B43730705 : Blo 2273435 43730705 := bstep (se 2 (by rfl) ⟨16399014, by rfl⟩ : syracuseStep 43730705 = 32798029) B32798029
theorem B29153803 : Blo 2273435 29153803 := bstep (se 1 (by rfl) ⟨21865352, by rfl⟩ : syracuseStep 29153803 = 43730705) B43730705
theorem B38871737 : Blo 2273435 38871737 := bstep (se 2 (by rfl) ⟨14576901, by rfl⟩ : syracuseStep 38871737 = 29153803) B29153803
theorem B25914491 : Blo 2273435 25914491 := bstep (se 1 (by rfl) ⟨19435868, by rfl⟩ : syracuseStep 25914491 = 38871737) B38871737
theorem B17276327 : Blo 2273435 17276327 := bstep (se 1 (by rfl) ⟨12957245, by rfl⟩ : syracuseStep 17276327 = 25914491) B25914491
theorem B11517551 : Blo 2273435 11517551 := bstep (se 1 (by rfl) ⟨8638163, by rfl⟩ : syracuseStep 11517551 = 17276327) B17276327
theorem B7678367 : Blo 2273435 7678367 := bstep (se 1 (by rfl) ⟨5758775, by rfl⟩ : syracuseStep 7678367 = 11517551) B11517551
theorem B5118911 : Blo 2273435 5118911 := bstep (se 1 (by rfl) ⟨3839183, by rfl⟩ : syracuseStep 5118911 = 7678367) B7678367
theorem B3412607 : Blo 2273435 3412607 := bstep (se 1 (by rfl) ⟨2559455, by rfl⟩ : syracuseStep 3412607 = 5118911) B5118911
theorem B2275071 : Blo 2273435 2275071 := bstep (se 1 (by rfl) ⟨1706303, by rfl⟩ : syracuseStep 2275071 = 3412607) B3412607
theorem B3412613 : Blo 2273435 3412613 := bbase (se 4 (by rfl) ⟨319932, by rfl⟩ : syracuseStep 3412613 = 639865) (by norm_num)
theorem B2275075 : Blo 2273435 2275075 := bstep (se 1 (by rfl) ⟨1706306, by rfl⟩ : syracuseStep 2275075 = 3412613) B3412613
theorem B3839197 : Blo 2273435 3839197 := bbase (se 3 (by rfl) ⟨719849, by rfl⟩ : syracuseStep 3839197 = 1439699) (by norm_num)
theorem B5118929 : Blo 2273435 5118929 := bstep (se 2 (by rfl) ⟨1919598, by rfl⟩ : syracuseStep 5118929 = 3839197) B3839197
theorem B3412619 : Blo 2273435 3412619 := bstep (se 1 (by rfl) ⟨2559464, by rfl⟩ : syracuseStep 3412619 = 5118929) B5118929
theorem B2275079 : Blo 2273435 2275079 := bstep (se 1 (by rfl) ⟨1706309, by rfl⟩ : syracuseStep 2275079 = 3412619) B3412619
theorem B2559469 : Blo 2273435 2559469 := bbase (se 3 (by rfl) ⟨479900, by rfl⟩ : syracuseStep 2559469 = 959801) (by norm_num)
theorem B3412625 : Blo 2273435 3412625 := bstep (se 2 (by rfl) ⟨1279734, by rfl⟩ : syracuseStep 3412625 = 2559469) B2559469
theorem B2275083 : Blo 2273435 2275083 := bstep (se 1 (by rfl) ⟨1706312, by rfl⟩ : syracuseStep 2275083 = 3412625) B3412625
theorem B7678421 : Blo 2273435 7678421 := bbase (se 7 (by rfl) ⟨89981, by rfl⟩ : syracuseStep 7678421 = 179963) (by norm_num)
theorem B5118947 : Blo 2273435 5118947 := bstep (se 1 (by rfl) ⟨3839210, by rfl⟩ : syracuseStep 5118947 = 7678421) B7678421
theorem B3412631 : Blo 2273435 3412631 := bstep (se 1 (by rfl) ⟨2559473, by rfl⟩ : syracuseStep 3412631 = 5118947) B5118947
theorem B2275087 : Blo 2273435 2275087 := bstep (se 1 (by rfl) ⟨1706315, by rfl⟩ : syracuseStep 2275087 = 3412631) B3412631
theorem B3412637 : Blo 2273435 3412637 := bbase (se 3 (by rfl) ⟨639869, by rfl⟩ : syracuseStep 3412637 = 1279739) (by norm_num)
theorem B2275091 : Blo 2273435 2275091 := bstep (se 1 (by rfl) ⟨1706318, by rfl⟩ : syracuseStep 2275091 = 3412637) B3412637
theorem B5118965 : Blo 2273435 5118965 := bbase (se 5 (by rfl) ⟨239951, by rfl⟩ : syracuseStep 5118965 = 479903) (by norm_num)
theorem B3412643 : Blo 2273435 3412643 := bstep (se 1 (by rfl) ⟨2559482, by rfl⟩ : syracuseStep 3412643 = 5118965) B5118965
theorem B2275095 : Blo 2273435 2275095 := bstep (se 1 (by rfl) ⟨1706321, by rfl⟩ : syracuseStep 2275095 = 3412643) B3412643
theorem B6918421 : Blo 2273435 6918421 := bbase (se 6 (by rfl) ⟨162150, by rfl⟩ : syracuseStep 6918421 = 324301) (by norm_num)
theorem B9224561 : Blo 2273435 9224561 := bstep (se 2 (by rfl) ⟨3459210, by rfl⟩ : syracuseStep 9224561 = 6918421) B6918421
theorem B24598829 : Blo 2273435 24598829 := bstep (se 3 (by rfl) ⟨4612280, by rfl⟩ : syracuseStep 24598829 = 9224561) B9224561
theorem B65596877 : Blo 2273435 65596877 := bstep (se 3 (by rfl) ⟨12299414, by rfl⟩ : syracuseStep 65596877 = 24598829) B24598829
theorem B43731251 : Blo 2273435 43731251 := bstep (se 1 (by rfl) ⟨32798438, by rfl⟩ : syracuseStep 43731251 = 65596877) B65596877
theorem B29154167 : Blo 2273435 29154167 := bstep (se 1 (by rfl) ⟨21865625, by rfl⟩ : syracuseStep 29154167 = 43731251) B43731251
theorem B19436111 : Blo 2273435 19436111 := bstep (se 1 (by rfl) ⟨14577083, by rfl⟩ : syracuseStep 19436111 = 29154167) B29154167
theorem B12957407 : Blo 2273435 12957407 := bstep (se 1 (by rfl) ⟨9718055, by rfl⟩ : syracuseStep 12957407 = 19436111) B19436111
theorem B8638271 : Blo 2273435 8638271 := bstep (se 1 (by rfl) ⟨6478703, by rfl⟩ : syracuseStep 8638271 = 12957407) B12957407
theorem B5758847 : Blo 2273435 5758847 := bstep (se 1 (by rfl) ⟨4319135, by rfl⟩ : syracuseStep 5758847 = 8638271) B8638271
theorem B3839231 : Blo 2273435 3839231 := bstep (se 1 (by rfl) ⟨2879423, by rfl⟩ : syracuseStep 3839231 = 5758847) B5758847
theorem B2559487 : Blo 2273435 2559487 := bstep (se 1 (by rfl) ⟨1919615, by rfl⟩ : syracuseStep 2559487 = 3839231) B3839231
theorem B3412649 : Blo 2273435 3412649 := bstep (se 2 (by rfl) ⟨1279743, by rfl⟩ : syracuseStep 3412649 = 2559487) B2559487
theorem B2275099 : Blo 2273435 2275099 := bstep (se 1 (by rfl) ⟨1706324, by rfl⟩ : syracuseStep 2275099 = 3412649) B3412649
theorem B3239357 : Blo 2273435 3239357 := bbase (se 3 (by rfl) ⟨607379, by rfl⟩ : syracuseStep 3239357 = 1214759) (by norm_num)
theorem B8638285 : Blo 2273435 8638285 := bstep (se 3 (by rfl) ⟨1619678, by rfl⟩ : syracuseStep 8638285 = 3239357) B3239357
theorem B11517713 : Blo 2273435 11517713 := bstep (se 2 (by rfl) ⟨4319142, by rfl⟩ : syracuseStep 11517713 = 8638285) B8638285
theorem B7678475 : Blo 2273435 7678475 := bstep (se 1 (by rfl) ⟨5758856, by rfl⟩ : syracuseStep 7678475 = 11517713) B11517713
theorem B5118983 : Blo 2273435 5118983 := bstep (se 1 (by rfl) ⟨3839237, by rfl⟩ : syracuseStep 5118983 = 7678475) B7678475
theorem B3412655 : Blo 2273435 3412655 := bstep (se 1 (by rfl) ⟨2559491, by rfl⟩ : syracuseStep 3412655 = 5118983) B5118983
theorem B2275103 : Blo 2273435 2275103 := bstep (se 1 (by rfl) ⟨1706327, by rfl⟩ : syracuseStep 2275103 = 3412655) B3412655
theorem B3412661 : Blo 2273435 3412661 := bbase (se 5 (by rfl) ⟨159968, by rfl⟩ : syracuseStep 3412661 = 319937) (by norm_num)
theorem B2275107 : Blo 2273435 2275107 := bstep (se 1 (by rfl) ⟨1706330, by rfl⟩ : syracuseStep 2275107 = 3412661) B3412661
theorem B5758877 : Blo 2273435 5758877 := bbase (se 3 (by rfl) ⟨1079789, by rfl⟩ : syracuseStep 5758877 = 2159579) (by norm_num)
theorem B3839251 : Blo 2273435 3839251 := bstep (se 1 (by rfl) ⟨2879438, by rfl⟩ : syracuseStep 3839251 = 5758877) B5758877
theorem B5119001 : Blo 2273435 5119001 := bstep (se 2 (by rfl) ⟨1919625, by rfl⟩ : syracuseStep 5119001 = 3839251) B3839251
theorem B3412667 : Blo 2273435 3412667 := bstep (se 1 (by rfl) ⟨2559500, by rfl⟩ : syracuseStep 3412667 = 5119001) B5119001
theorem B2275111 : Blo 2273435 2275111 := bstep (se 1 (by rfl) ⟨1706333, by rfl⟩ : syracuseStep 2275111 = 3412667) B3412667
theorem B2559505 : Blo 2273435 2559505 := bbase (se 2 (by rfl) ⟨959814, by rfl⟩ : syracuseStep 2559505 = 1919629) (by norm_num)
theorem B3412673 : Blo 2273435 3412673 := bstep (se 2 (by rfl) ⟨1279752, by rfl⟩ : syracuseStep 3412673 = 2559505) B2559505
theorem B2275115 : Blo 2273435 2275115 := bstep (se 1 (by rfl) ⟨1706336, by rfl⟩ : syracuseStep 2275115 = 3412673) B3412673
theorem B4319173 : Blo 2273435 4319173 := bbase (se 4 (by rfl) ⟨404922, by rfl⟩ : syracuseStep 4319173 = 809845) (by norm_num)
theorem B5758897 : Blo 2273435 5758897 := bstep (se 2 (by rfl) ⟨2159586, by rfl⟩ : syracuseStep 5758897 = 4319173) B4319173
theorem B7678529 : Blo 2273435 7678529 := bstep (se 2 (by rfl) ⟨2879448, by rfl⟩ : syracuseStep 7678529 = 5758897) B5758897
theorem B5119019 : Blo 2273435 5119019 := bstep (se 1 (by rfl) ⟨3839264, by rfl⟩ : syracuseStep 5119019 = 7678529) B7678529
theorem B3412679 : Blo 2273435 3412679 := bstep (se 1 (by rfl) ⟨2559509, by rfl⟩ : syracuseStep 3412679 = 5119019) B5119019
theorem B2275119 : Blo 2273435 2275119 := bstep (se 1 (by rfl) ⟨1706339, by rfl⟩ : syracuseStep 2275119 = 3412679) B3412679
theorem B3412685 : Blo 2273435 3412685 := bbase (se 3 (by rfl) ⟨639878, by rfl⟩ : syracuseStep 3412685 = 1279757) (by norm_num)
theorem B2275123 : Blo 2273435 2275123 := bstep (se 1 (by rfl) ⟨1706342, by rfl⟩ : syracuseStep 2275123 = 3412685) B3412685
theorem B5119037 : Blo 2273435 5119037 := bbase (se 3 (by rfl) ⟨959819, by rfl⟩ : syracuseStep 5119037 = 1919639) (by norm_num)
theorem B3412691 : Blo 2273435 3412691 := bstep (se 1 (by rfl) ⟨2559518, by rfl⟩ : syracuseStep 3412691 = 5119037) B5119037
theorem B2275127 : Blo 2273435 2275127 := bstep (se 1 (by rfl) ⟨1706345, by rfl⟩ : syracuseStep 2275127 = 3412691) B3412691
theorem B3839285 : Blo 2273435 3839285 := bbase (se 5 (by rfl) ⟨179966, by rfl⟩ : syracuseStep 3839285 = 359933) (by norm_num)
theorem B2559523 : Blo 2273435 2559523 := bstep (se 1 (by rfl) ⟨1919642, by rfl⟩ : syracuseStep 2559523 = 3839285) B3839285
theorem B3412697 : Blo 2273435 3412697 := bstep (se 2 (by rfl) ⟨1279761, by rfl⟩ : syracuseStep 3412697 = 2559523) B2559523
theorem B2275131 : Blo 2273435 2275131 := bstep (se 1 (by rfl) ⟨1706348, by rfl⟩ : syracuseStep 2275131 = 3412697) B3412697
theorem B6478805 : Blo 2273435 6478805 := bbase (se 7 (by rfl) ⟨75923, by rfl⟩ : syracuseStep 6478805 = 151847) (by norm_num)
theorem B17276813 : Blo 2273435 17276813 := bstep (se 3 (by rfl) ⟨3239402, by rfl⟩ : syracuseStep 17276813 = 6478805) B6478805
theorem B11517875 : Blo 2273435 11517875 := bstep (se 1 (by rfl) ⟨8638406, by rfl⟩ : syracuseStep 11517875 = 17276813) B17276813
theorem B7678583 : Blo 2273435 7678583 := bstep (se 1 (by rfl) ⟨5758937, by rfl⟩ : syracuseStep 7678583 = 11517875) B11517875
theorem B5119055 : Blo 2273435 5119055 := bstep (se 1 (by rfl) ⟨3839291, by rfl⟩ : syracuseStep 5119055 = 7678583) B7678583
theorem B3412703 : Blo 2273435 3412703 := bstep (se 1 (by rfl) ⟨2559527, by rfl⟩ : syracuseStep 3412703 = 5119055) B5119055
theorem B2275135 : Blo 2273435 2275135 := bstep (se 1 (by rfl) ⟨1706351, by rfl⟩ : syracuseStep 2275135 = 3412703) B3412703
theorem B3412709 : Blo 2273435 3412709 := bbase (se 4 (by rfl) ⟨319941, by rfl⟩ : syracuseStep 3412709 = 639883) (by norm_num)
theorem B2275139 : Blo 2273435 2275139 := bstep (se 1 (by rfl) ⟨1706354, by rfl⟩ : syracuseStep 2275139 = 3412709) B3412709
theorem B2429561 : Blo 2273435 2429561 := bbase (se 2 (by rfl) ⟨911085, by rfl⟩ : syracuseStep 2429561 = 1822171) (by norm_num)
theorem B6478829 : Blo 2273435 6478829 := bstep (se 3 (by rfl) ⟨1214780, by rfl⟩ : syracuseStep 6478829 = 2429561) B2429561
theorem B4319219 : Blo 2273435 4319219 := bstep (se 1 (by rfl) ⟨3239414, by rfl⟩ : syracuseStep 4319219 = 6478829) B6478829
theorem B2879479 : Blo 2273435 2879479 := bstep (se 1 (by rfl) ⟨2159609, by rfl⟩ : syracuseStep 2879479 = 4319219) B4319219
theorem B3839305 : Blo 2273435 3839305 := bstep (se 2 (by rfl) ⟨1439739, by rfl⟩ : syracuseStep 3839305 = 2879479) B2879479
theorem B5119073 : Blo 2273435 5119073 := bstep (se 2 (by rfl) ⟨1919652, by rfl⟩ : syracuseStep 5119073 = 3839305) B3839305
theorem B3412715 : Blo 2273435 3412715 := bstep (se 1 (by rfl) ⟨2559536, by rfl⟩ : syracuseStep 3412715 = 5119073) B5119073
theorem B2275143 : Blo 2273435 2275143 := bstep (se 1 (by rfl) ⟨1706357, by rfl⟩ : syracuseStep 2275143 = 3412715) B3412715
theorem B2559541 : Blo 2273435 2559541 := bbase (se 5 (by rfl) ⟨119978, by rfl⟩ : syracuseStep 2559541 = 239957) (by norm_num)
theorem B3412721 : Blo 2273435 3412721 := bstep (se 2 (by rfl) ⟨1279770, by rfl⟩ : syracuseStep 3412721 = 2559541) B2559541
theorem B2275147 : Blo 2273435 2275147 := bstep (se 1 (by rfl) ⟨1706360, by rfl⟩ : syracuseStep 2275147 = 3412721) B3412721
theorem B2879489 : Blo 2273435 2879489 := bbase (se 2 (by rfl) ⟨1079808, by rfl⟩ : syracuseStep 2879489 = 2159617) (by norm_num)
theorem B7678637 : Blo 2273435 7678637 := bstep (se 3 (by rfl) ⟨1439744, by rfl⟩ : syracuseStep 7678637 = 2879489) B2879489
theorem B5119091 : Blo 2273435 5119091 := bstep (se 1 (by rfl) ⟨3839318, by rfl⟩ : syracuseStep 5119091 = 7678637) B7678637
theorem B3412727 : Blo 2273435 3412727 := bstep (se 1 (by rfl) ⟨2559545, by rfl⟩ : syracuseStep 3412727 = 5119091) B5119091
theorem B2275151 : Blo 2273435 2275151 := bstep (se 1 (by rfl) ⟨1706363, by rfl⟩ : syracuseStep 2275151 = 3412727) B3412727
theorem B3412733 : Blo 2273435 3412733 := bbase (se 3 (by rfl) ⟨639887, by rfl⟩ : syracuseStep 3412733 = 1279775) (by norm_num)
theorem B2275155 : Blo 2273435 2275155 := bstep (se 1 (by rfl) ⟨1706366, by rfl⟩ : syracuseStep 2275155 = 3412733) B3412733
theorem B5119109 : Blo 2273435 5119109 := bbase (se 4 (by rfl) ⟨479916, by rfl⟩ : syracuseStep 5119109 = 959833) (by norm_num)
theorem B3412739 : Blo 2273435 3412739 := bstep (se 1 (by rfl) ⟨2559554, by rfl⟩ : syracuseStep 3412739 = 5119109) B5119109
theorem B2275159 : Blo 2273435 2275159 := bstep (se 1 (by rfl) ⟨1706369, by rfl⟩ : syracuseStep 2275159 = 3412739) B3412739
theorem B4859165 : Blo 2273435 4859165 := bbase (se 3 (by rfl) ⟨911093, by rfl⟩ : syracuseStep 4859165 = 1822187) (by norm_num)
theorem B3239443 : Blo 2273435 3239443 := bstep (se 1 (by rfl) ⟨2429582, by rfl⟩ : syracuseStep 3239443 = 4859165) B4859165
theorem B4319257 : Blo 2273435 4319257 := bstep (se 2 (by rfl) ⟨1619721, by rfl⟩ : syracuseStep 4319257 = 3239443) B3239443
theorem B5759009 : Blo 2273435 5759009 := bstep (se 2 (by rfl) ⟨2159628, by rfl⟩ : syracuseStep 5759009 = 4319257) B4319257
theorem B3839339 : Blo 2273435 3839339 := bstep (se 1 (by rfl) ⟨2879504, by rfl⟩ : syracuseStep 3839339 = 5759009) B5759009
theorem B2559559 : Blo 2273435 2559559 := bstep (se 1 (by rfl) ⟨1919669, by rfl⟩ : syracuseStep 2559559 = 3839339) B3839339
theorem B3412745 : Blo 2273435 3412745 := bstep (se 2 (by rfl) ⟨1279779, by rfl⟩ : syracuseStep 3412745 = 2559559) B2559559
theorem B2275163 : Blo 2273435 2275163 := bstep (se 1 (by rfl) ⟨1706372, by rfl⟩ : syracuseStep 2275163 = 3412745) B3412745
theorem B11518037 : Blo 2273435 11518037 := bbase (se 8 (by rfl) ⟨67488, by rfl⟩ : syracuseStep 11518037 = 134977) (by norm_num)
theorem B7678691 : Blo 2273435 7678691 := bstep (se 1 (by rfl) ⟨5759018, by rfl⟩ : syracuseStep 7678691 = 11518037) B11518037
theorem B5119127 : Blo 2273435 5119127 := bstep (se 1 (by rfl) ⟨3839345, by rfl⟩ : syracuseStep 5119127 = 7678691) B7678691
theorem B3412751 : Blo 2273435 3412751 := bstep (se 1 (by rfl) ⟨2559563, by rfl⟩ : syracuseStep 3412751 = 5119127) B5119127
theorem B2275167 : Blo 2273435 2275167 := bstep (se 1 (by rfl) ⟨1706375, by rfl⟩ : syracuseStep 2275167 = 3412751) B3412751
theorem B3412757 : Blo 2273435 3412757 := bbase (se 6 (by rfl) ⟨79986, by rfl⟩ : syracuseStep 3412757 = 159973) (by norm_num)
theorem B2275171 : Blo 2273435 2275171 := bstep (se 1 (by rfl) ⟨1706378, by rfl⟩ : syracuseStep 2275171 = 3412757) B3412757
theorem B9224869 : Blo 2273435 9224869 := bbase (se 4 (by rfl) ⟨864831, by rfl⟩ : syracuseStep 9224869 = 1729663) (by norm_num)
theorem B12299825 : Blo 2273435 12299825 := bstep (se 2 (by rfl) ⟨4612434, by rfl⟩ : syracuseStep 12299825 = 9224869) B9224869
theorem B8199883 : Blo 2273435 8199883 := bstep (se 1 (by rfl) ⟨6149912, by rfl⟩ : syracuseStep 8199883 = 12299825) B12299825
theorem B43732709 : Blo 2273435 43732709 := bstep (se 4 (by rfl) ⟨4099941, by rfl⟩ : syracuseStep 43732709 = 8199883) B8199883
theorem B29155139 : Blo 2273435 29155139 := bstep (se 1 (by rfl) ⟨21866354, by rfl⟩ : syracuseStep 29155139 = 43732709) B43732709
theorem B19436759 : Blo 2273435 19436759 := bstep (se 1 (by rfl) ⟨14577569, by rfl⟩ : syracuseStep 19436759 = 29155139) B29155139
theorem B12957839 : Blo 2273435 12957839 := bstep (se 1 (by rfl) ⟨9718379, by rfl⟩ : syracuseStep 12957839 = 19436759) B19436759
theorem B8638559 : Blo 2273435 8638559 := bstep (se 1 (by rfl) ⟨6478919, by rfl⟩ : syracuseStep 8638559 = 12957839) B12957839
theorem B5759039 : Blo 2273435 5759039 := bstep (se 1 (by rfl) ⟨4319279, by rfl⟩ : syracuseStep 5759039 = 8638559) B8638559
theorem B3839359 : Blo 2273435 3839359 := bstep (se 1 (by rfl) ⟨2879519, by rfl⟩ : syracuseStep 3839359 = 5759039) B5759039
theorem B5119145 : Blo 2273435 5119145 := bstep (se 2 (by rfl) ⟨1919679, by rfl⟩ : syracuseStep 5119145 = 3839359) B3839359
theorem B3412763 : Blo 2273435 3412763 := bstep (se 1 (by rfl) ⟨2559572, by rfl⟩ : syracuseStep 3412763 = 5119145) B5119145
theorem B2275175 : Blo 2273435 2275175 := bstep (se 1 (by rfl) ⟨1706381, by rfl⟩ : syracuseStep 2275175 = 3412763) B3412763
theorem B2559577 : Blo 2273435 2559577 := bbase (se 2 (by rfl) ⟨959841, by rfl⟩ : syracuseStep 2559577 = 1919683) (by norm_num)
theorem B3412769 : Blo 2273435 3412769 := bstep (se 2 (by rfl) ⟨1279788, by rfl⟩ : syracuseStep 3412769 = 2559577) B2559577
theorem B2275179 : Blo 2273435 2275179 := bstep (se 1 (by rfl) ⟨1706384, by rfl⟩ : syracuseStep 2275179 = 3412769) B3412769
theorem B11675269 : Blo 2273435 11675269 := bbase (se 4 (by rfl) ⟨1094556, by rfl⟩ : syracuseStep 11675269 = 2189113) (by norm_num)
theorem B15567025 : Blo 2273435 15567025 := bstep (se 2 (by rfl) ⟨5837634, by rfl⟩ : syracuseStep 15567025 = 11675269) B11675269
theorem B20756033 : Blo 2273435 20756033 := bstep (se 2 (by rfl) ⟨7783512, by rfl⟩ : syracuseStep 20756033 = 15567025) B15567025
theorem B13837355 : Blo 2273435 13837355 := bstep (se 1 (by rfl) ⟨10378016, by rfl⟩ : syracuseStep 13837355 = 20756033) B20756033
theorem B9224903 : Blo 2273435 9224903 := bstep (se 1 (by rfl) ⟨6918677, by rfl⟩ : syracuseStep 9224903 = 13837355) B13837355
theorem B6149935 : Blo 2273435 6149935 := bstep (se 1 (by rfl) ⟨4612451, by rfl⟩ : syracuseStep 6149935 = 9224903) B9224903
theorem B8199913 : Blo 2273435 8199913 := bstep (se 2 (by rfl) ⟨3074967, by rfl⟩ : syracuseStep 8199913 = 6149935) B6149935
theorem B10933217 : Blo 2273435 10933217 := bstep (se 2 (by rfl) ⟨4099956, by rfl⟩ : syracuseStep 10933217 = 8199913) B8199913
theorem B7288811 : Blo 2273435 7288811 := bstep (se 1 (by rfl) ⟨5466608, by rfl⟩ : syracuseStep 7288811 = 10933217) B10933217
theorem B4859207 : Blo 2273435 4859207 := bstep (se 1 (by rfl) ⟨3644405, by rfl⟩ : syracuseStep 4859207 = 7288811) B7288811
theorem B3239471 : Blo 2273435 3239471 := bstep (se 1 (by rfl) ⟨2429603, by rfl⟩ : syracuseStep 3239471 = 4859207) B4859207
theorem B8638589 : Blo 2273435 8638589 := bstep (se 3 (by rfl) ⟨1619735, by rfl⟩ : syracuseStep 8638589 = 3239471) B3239471
theorem B5759059 : Blo 2273435 5759059 := bstep (se 1 (by rfl) ⟨4319294, by rfl⟩ : syracuseStep 5759059 = 8638589) B8638589
theorem B7678745 : Blo 2273435 7678745 := bstep (se 2 (by rfl) ⟨2879529, by rfl⟩ : syracuseStep 7678745 = 5759059) B5759059
theorem B5119163 : Blo 2273435 5119163 := bstep (se 1 (by rfl) ⟨3839372, by rfl⟩ : syracuseStep 5119163 = 7678745) B7678745
theorem B3412775 : Blo 2273435 3412775 := bstep (se 1 (by rfl) ⟨2559581, by rfl⟩ : syracuseStep 3412775 = 5119163) B5119163
theorem B2275183 : Blo 2273435 2275183 := bstep (se 1 (by rfl) ⟨1706387, by rfl⟩ : syracuseStep 2275183 = 3412775) B3412775
theorem B3412781 : Blo 2273435 3412781 := bbase (se 3 (by rfl) ⟨639896, by rfl⟩ : syracuseStep 3412781 = 1279793) (by norm_num)
theorem B2275187 : Blo 2273435 2275187 := bstep (se 1 (by rfl) ⟨1706390, by rfl⟩ : syracuseStep 2275187 = 3412781) B3412781
theorem B5119181 : Blo 2273435 5119181 := bbase (se 3 (by rfl) ⟨959846, by rfl⟩ : syracuseStep 5119181 = 1919693) (by norm_num)
theorem B3412787 : Blo 2273435 3412787 := bstep (se 1 (by rfl) ⟨2559590, by rfl⟩ : syracuseStep 3412787 = 5119181) B5119181
theorem B2275191 : Blo 2273435 2275191 := bstep (se 1 (by rfl) ⟨1706393, by rfl⟩ : syracuseStep 2275191 = 3412787) B3412787
theorem B2879545 : Blo 2273435 2879545 := bbase (se 2 (by rfl) ⟨1079829, by rfl⟩ : syracuseStep 2879545 = 2159659) (by norm_num)
theorem B3839393 : Blo 2273435 3839393 := bstep (se 2 (by rfl) ⟨1439772, by rfl⟩ : syracuseStep 3839393 = 2879545) B2879545
theorem B2559595 : Blo 2273435 2559595 := bstep (se 1 (by rfl) ⟨1919696, by rfl⟩ : syracuseStep 2559595 = 3839393) B3839393
theorem B3412793 : Blo 2273435 3412793 := bstep (se 2 (by rfl) ⟨1279797, by rfl⟩ : syracuseStep 3412793 = 2559595) B2559595
theorem B2275195 : Blo 2273435 2275195 := bstep (se 1 (by rfl) ⟨1706396, by rfl⟩ : syracuseStep 2275195 = 3412793) B3412793
theorem B3074989 : Blo 2273435 3074989 := bbase (se 3 (by rfl) ⟨576560, by rfl⟩ : syracuseStep 3074989 = 1153121) (by norm_num)
theorem B4099985 : Blo 2273435 4099985 := bstep (se 2 (by rfl) ⟨1537494, by rfl⟩ : syracuseStep 4099985 = 3074989) B3074989
theorem B2733323 : Blo 2273435 2733323 := bstep (se 1 (by rfl) ⟨2049992, by rfl⟩ : syracuseStep 2733323 = 4099985) B4099985
theorem B7288861 : Blo 2273435 7288861 := bstep (se 3 (by rfl) ⟨1366661, by rfl⟩ : syracuseStep 7288861 = 2733323) B2733323
theorem B9718481 : Blo 2273435 9718481 := bstep (se 2 (by rfl) ⟨3644430, by rfl⟩ : syracuseStep 9718481 = 7288861) B7288861
theorem B25915949 : Blo 2273435 25915949 := bstep (se 3 (by rfl) ⟨4859240, by rfl⟩ : syracuseStep 25915949 = 9718481) B9718481
theorem B17277299 : Blo 2273435 17277299 := bstep (se 1 (by rfl) ⟨12957974, by rfl⟩ : syracuseStep 17277299 = 25915949) B25915949
theorem B11518199 : Blo 2273435 11518199 := bstep (se 1 (by rfl) ⟨8638649, by rfl⟩ : syracuseStep 11518199 = 17277299) B17277299
theorem B7678799 : Blo 2273435 7678799 := bstep (se 1 (by rfl) ⟨5759099, by rfl⟩ : syracuseStep 7678799 = 11518199) B11518199
theorem B5119199 : Blo 2273435 5119199 := bstep (se 1 (by rfl) ⟨3839399, by rfl⟩ : syracuseStep 5119199 = 7678799) B7678799
theorem B3412799 : Blo 2273435 3412799 := bstep (se 1 (by rfl) ⟨2559599, by rfl⟩ : syracuseStep 3412799 = 5119199) B5119199
theorem B2275199 : Blo 2273435 2275199 := bstep (se 1 (by rfl) ⟨1706399, by rfl⟩ : syracuseStep 2275199 = 3412799) B3412799
theorem B3412805 : Blo 2273435 3412805 := bbase (se 4 (by rfl) ⟨319950, by rfl⟩ : syracuseStep 3412805 = 639901) (by norm_num)
theorem B2275203 : Blo 2273435 2275203 := bstep (se 1 (by rfl) ⟨1706402, by rfl⟩ : syracuseStep 2275203 = 3412805) B3412805
theorem B3839413 : Blo 2273435 3839413 := bbase (se 5 (by rfl) ⟨179972, by rfl⟩ : syracuseStep 3839413 = 359945) (by norm_num)
theorem B5119217 : Blo 2273435 5119217 := bstep (se 2 (by rfl) ⟨1919706, by rfl⟩ : syracuseStep 5119217 = 3839413) B3839413
theorem B3412811 : Blo 2273435 3412811 := bstep (se 1 (by rfl) ⟨2559608, by rfl⟩ : syracuseStep 3412811 = 5119217) B5119217
theorem B2275207 : Blo 2273435 2275207 := bstep (se 1 (by rfl) ⟨1706405, by rfl⟩ : syracuseStep 2275207 = 3412811) B3412811
theorem B2559613 : Blo 2273435 2559613 := bbase (se 3 (by rfl) ⟨479927, by rfl⟩ : syracuseStep 2559613 = 959855) (by norm_num)
theorem B3412817 : Blo 2273435 3412817 := bstep (se 2 (by rfl) ⟨1279806, by rfl⟩ : syracuseStep 3412817 = 2559613) B2559613
theorem B2275211 : Blo 2273435 2275211 := bstep (se 1 (by rfl) ⟨1706408, by rfl⟩ : syracuseStep 2275211 = 3412817) B3412817
theorem B7678853 : Blo 2273435 7678853 := bbase (se 4 (by rfl) ⟨719892, by rfl⟩ : syracuseStep 7678853 = 1439785) (by norm_num)
theorem B5119235 : Blo 2273435 5119235 := bstep (se 1 (by rfl) ⟨3839426, by rfl⟩ : syracuseStep 5119235 = 7678853) B7678853
theorem B3412823 : Blo 2273435 3412823 := bstep (se 1 (by rfl) ⟨2559617, by rfl⟩ : syracuseStep 3412823 = 5119235) B5119235
theorem B2275215 : Blo 2273435 2275215 := bstep (se 1 (by rfl) ⟨1706411, by rfl⟩ : syracuseStep 2275215 = 3412823) B3412823
theorem B3412829 : Blo 2273435 3412829 := bbase (se 3 (by rfl) ⟨639905, by rfl⟩ : syracuseStep 3412829 = 1279811) (by norm_num)
theorem B2275219 : Blo 2273435 2275219 := bstep (se 1 (by rfl) ⟨1706414, by rfl⟩ : syracuseStep 2275219 = 3412829) B3412829
theorem B5119253 : Blo 2273435 5119253 := bbase (se 6 (by rfl) ⟨119982, by rfl⟩ : syracuseStep 5119253 = 239965) (by norm_num)
theorem B3412835 : Blo 2273435 3412835 := bstep (se 1 (by rfl) ⟨2559626, by rfl⟩ : syracuseStep 3412835 = 5119253) B5119253
theorem B2275223 : Blo 2273435 2275223 := bstep (se 1 (by rfl) ⟨1706417, by rfl⟩ : syracuseStep 2275223 = 3412835) B3412835
theorem B8638757 : Blo 2273435 8638757 := bbase (se 4 (by rfl) ⟨809883, by rfl⟩ : syracuseStep 8638757 = 1619767) (by norm_num)
theorem B5759171 : Blo 2273435 5759171 := bstep (se 1 (by rfl) ⟨4319378, by rfl⟩ : syracuseStep 5759171 = 8638757) B8638757
theorem B3839447 : Blo 2273435 3839447 := bstep (se 1 (by rfl) ⟨2879585, by rfl⟩ : syracuseStep 3839447 = 5759171) B5759171
theorem B2559631 : Blo 2273435 2559631 := bstep (se 1 (by rfl) ⟨1919723, by rfl⟩ : syracuseStep 2559631 = 3839447) B3839447
theorem B3412841 : Blo 2273435 3412841 := bstep (se 2 (by rfl) ⟨1279815, by rfl⟩ : syracuseStep 3412841 = 2559631) B2559631
theorem B2275227 : Blo 2273435 2275227 := bstep (se 1 (by rfl) ⟨1706420, by rfl⟩ : syracuseStep 2275227 = 3412841) B3412841
theorem B4859309 : Blo 2273435 4859309 := bbase (se 3 (by rfl) ⟨911120, by rfl⟩ : syracuseStep 4859309 = 1822241) (by norm_num)
theorem B12958157 : Blo 2273435 12958157 := bstep (se 3 (by rfl) ⟨2429654, by rfl⟩ : syracuseStep 12958157 = 4859309) B4859309
theorem B8638771 : Blo 2273435 8638771 := bstep (se 1 (by rfl) ⟨6479078, by rfl⟩ : syracuseStep 8638771 = 12958157) B12958157
theorem B11518361 : Blo 2273435 11518361 := bstep (se 2 (by rfl) ⟨4319385, by rfl⟩ : syracuseStep 11518361 = 8638771) B8638771
theorem B7678907 : Blo 2273435 7678907 := bstep (se 1 (by rfl) ⟨5759180, by rfl⟩ : syracuseStep 7678907 = 11518361) B11518361
theorem B5119271 : Blo 2273435 5119271 := bstep (se 1 (by rfl) ⟨3839453, by rfl⟩ : syracuseStep 5119271 = 7678907) B7678907
theorem B3412847 : Blo 2273435 3412847 := bstep (se 1 (by rfl) ⟨2559635, by rfl⟩ : syracuseStep 3412847 = 5119271) B5119271
theorem B2275231 : Blo 2273435 2275231 := bstep (se 1 (by rfl) ⟨1706423, by rfl⟩ : syracuseStep 2275231 = 3412847) B3412847
theorem B3412853 : Blo 2273435 3412853 := bbase (se 5 (by rfl) ⟨159977, by rfl⟩ : syracuseStep 3412853 = 319955) (by norm_num)
theorem B2275235 : Blo 2273435 2275235 := bstep (se 1 (by rfl) ⟨1706426, by rfl⟩ : syracuseStep 2275235 = 3412853) B3412853
theorem B12467989 : Blo 2273435 12467989 := bbase (se 6 (by rfl) ⟨292218, by rfl⟩ : syracuseStep 12467989 = 584437) (by norm_num)
theorem B16623985 : Blo 2273435 16623985 := bstep (se 2 (by rfl) ⟨6233994, by rfl⟩ : syracuseStep 16623985 = 12467989) B12467989
theorem B354645013 : Blo 2273435 354645013 := bstep (se 6 (by rfl) ⟨8311992, by rfl⟩ : syracuseStep 354645013 = 16623985) B16623985
theorem B472860017 : Blo 2273435 472860017 := bstep (se 2 (by rfl) ⟨177322506, by rfl⟩ : syracuseStep 472860017 = 354645013) B354645013
theorem B315240011 : Blo 2273435 315240011 := bstep (se 1 (by rfl) ⟨236430008, by rfl⟩ : syracuseStep 315240011 = 472860017) B472860017
theorem B210160007 : Blo 2273435 210160007 := bstep (se 1 (by rfl) ⟨157620005, by rfl⟩ : syracuseStep 210160007 = 315240011) B315240011
theorem B140106671 : Blo 2273435 140106671 := bstep (se 1 (by rfl) ⟨105080003, by rfl⟩ : syracuseStep 140106671 = 210160007) B210160007
theorem B93404447 : Blo 2273435 93404447 := bstep (se 1 (by rfl) ⟨70053335, by rfl⟩ : syracuseStep 93404447 = 140106671) B140106671
theorem B62269631 : Blo 2273435 62269631 := bstep (se 1 (by rfl) ⟨46702223, by rfl⟩ : syracuseStep 62269631 = 93404447) B93404447
theorem B41513087 : Blo 2273435 41513087 := bstep (se 1 (by rfl) ⟨31134815, by rfl⟩ : syracuseStep 41513087 = 62269631) B62269631
theorem B27675391 : Blo 2273435 27675391 := bstep (se 1 (by rfl) ⟨20756543, by rfl⟩ : syracuseStep 27675391 = 41513087) B41513087
theorem B36900521 : Blo 2273435 36900521 := bstep (se 2 (by rfl) ⟨13837695, by rfl⟩ : syracuseStep 36900521 = 27675391) B27675391
theorem B24600347 : Blo 2273435 24600347 := bstep (se 1 (by rfl) ⟨18450260, by rfl⟩ : syracuseStep 24600347 = 36900521) B36900521
theorem B16400231 : Blo 2273435 16400231 := bstep (se 1 (by rfl) ⟨12300173, by rfl⟩ : syracuseStep 16400231 = 24600347) B24600347
theorem B10933487 : Blo 2273435 10933487 := bstep (se 1 (by rfl) ⟨8200115, by rfl⟩ : syracuseStep 10933487 = 16400231) B16400231
theorem B7288991 : Blo 2273435 7288991 := bstep (se 1 (by rfl) ⟨5466743, by rfl⟩ : syracuseStep 7288991 = 10933487) B10933487
theorem B4859327 : Blo 2273435 4859327 := bstep (se 1 (by rfl) ⟨3644495, by rfl⟩ : syracuseStep 4859327 = 7288991) B7288991
theorem B3239551 : Blo 2273435 3239551 := bstep (se 1 (by rfl) ⟨2429663, by rfl⟩ : syracuseStep 3239551 = 4859327) B4859327
theorem B4319401 : Blo 2273435 4319401 := bstep (se 2 (by rfl) ⟨1619775, by rfl⟩ : syracuseStep 4319401 = 3239551) B3239551
theorem B5759201 : Blo 2273435 5759201 := bstep (se 2 (by rfl) ⟨2159700, by rfl⟩ : syracuseStep 5759201 = 4319401) B4319401
theorem B3839467 : Blo 2273435 3839467 := bstep (se 1 (by rfl) ⟨2879600, by rfl⟩ : syracuseStep 3839467 = 5759201) B5759201
theorem B5119289 : Blo 2273435 5119289 := bstep (se 2 (by rfl) ⟨1919733, by rfl⟩ : syracuseStep 5119289 = 3839467) B3839467
theorem B3412859 : Blo 2273435 3412859 := bstep (se 1 (by rfl) ⟨2559644, by rfl⟩ : syracuseStep 3412859 = 5119289) B5119289
theorem B2275239 : Blo 2273435 2275239 := bstep (se 1 (by rfl) ⟨1706429, by rfl⟩ : syracuseStep 2275239 = 3412859) B3412859
theorem B2559649 : Blo 2273435 2559649 := bbase (se 2 (by rfl) ⟨959868, by rfl⟩ : syracuseStep 2559649 = 1919737) (by norm_num)
theorem B3412865 : Blo 2273435 3412865 := bstep (se 2 (by rfl) ⟨1279824, by rfl⟩ : syracuseStep 3412865 = 2559649) B2559649
theorem B2275243 : Blo 2273435 2275243 := bstep (se 1 (by rfl) ⟨1706432, by rfl⟩ : syracuseStep 2275243 = 3412865) B3412865
theorem B5759221 : Blo 2273435 5759221 := bbase (se 5 (by rfl) ⟨269963, by rfl⟩ : syracuseStep 5759221 = 539927) (by norm_num)
theorem B7678961 : Blo 2273435 7678961 := bstep (se 2 (by rfl) ⟨2879610, by rfl⟩ : syracuseStep 7678961 = 5759221) B5759221
theorem B5119307 : Blo 2273435 5119307 := bstep (se 1 (by rfl) ⟨3839480, by rfl⟩ : syracuseStep 5119307 = 7678961) B7678961
theorem B3412871 : Blo 2273435 3412871 := bstep (se 1 (by rfl) ⟨2559653, by rfl⟩ : syracuseStep 3412871 = 5119307) B5119307
theorem B2275247 : Blo 2273435 2275247 := bstep (se 1 (by rfl) ⟨1706435, by rfl⟩ : syracuseStep 2275247 = 3412871) B3412871
theorem B3412877 : Blo 2273435 3412877 := bbase (se 3 (by rfl) ⟨639914, by rfl⟩ : syracuseStep 3412877 = 1279829) (by norm_num)
theorem B2275251 : Blo 2273435 2275251 := bstep (se 1 (by rfl) ⟨1706438, by rfl⟩ : syracuseStep 2275251 = 3412877) B3412877
theorem B5119325 : Blo 2273435 5119325 := bbase (se 3 (by rfl) ⟨959873, by rfl⟩ : syracuseStep 5119325 = 1919747) (by norm_num)
theorem B3412883 : Blo 2273435 3412883 := bstep (se 1 (by rfl) ⟨2559662, by rfl⟩ : syracuseStep 3412883 = 5119325) B5119325
theorem B2275255 : Blo 2273435 2275255 := bstep (se 1 (by rfl) ⟨1706441, by rfl⟩ : syracuseStep 2275255 = 3412883) B3412883
theorem B3839501 : Blo 2273435 3839501 := bbase (se 3 (by rfl) ⟨719906, by rfl⟩ : syracuseStep 3839501 = 1439813) (by norm_num)
theorem B2559667 : Blo 2273435 2559667 := bstep (se 1 (by rfl) ⟨1919750, by rfl⟩ : syracuseStep 2559667 = 3839501) B3839501
theorem B3412889 : Blo 2273435 3412889 := bstep (se 2 (by rfl) ⟨1279833, by rfl⟩ : syracuseStep 3412889 = 2559667) B2559667
theorem B2275259 : Blo 2273435 2275259 := bstep (se 1 (by rfl) ⟨1706444, by rfl⟩ : syracuseStep 2275259 = 3412889) B3412889
theorem B3644533 : Blo 2273435 3644533 := bbase (se 5 (by rfl) ⟨170837, by rfl⟩ : syracuseStep 3644533 = 341675) (by norm_num)
theorem B19437509 : Blo 2273435 19437509 := bstep (se 4 (by rfl) ⟨1822266, by rfl⟩ : syracuseStep 19437509 = 3644533) B3644533
theorem B12958339 : Blo 2273435 12958339 := bstep (se 1 (by rfl) ⟨9718754, by rfl⟩ : syracuseStep 12958339 = 19437509) B19437509
theorem B17277785 : Blo 2273435 17277785 := bstep (se 2 (by rfl) ⟨6479169, by rfl⟩ : syracuseStep 17277785 = 12958339) B12958339
theorem B11518523 : Blo 2273435 11518523 := bstep (se 1 (by rfl) ⟨8638892, by rfl⟩ : syracuseStep 11518523 = 17277785) B17277785
theorem B7679015 : Blo 2273435 7679015 := bstep (se 1 (by rfl) ⟨5759261, by rfl⟩ : syracuseStep 7679015 = 11518523) B11518523
theorem B5119343 : Blo 2273435 5119343 := bstep (se 1 (by rfl) ⟨3839507, by rfl⟩ : syracuseStep 5119343 = 7679015) B7679015
theorem B3412895 : Blo 2273435 3412895 := bstep (se 1 (by rfl) ⟨2559671, by rfl⟩ : syracuseStep 3412895 = 5119343) B5119343
theorem B2275263 : Blo 2273435 2275263 := bstep (se 1 (by rfl) ⟨1706447, by rfl⟩ : syracuseStep 2275263 = 3412895) B3412895
theorem B3412901 : Blo 2273435 3412901 := bbase (se 4 (by rfl) ⟨319959, by rfl⟩ : syracuseStep 3412901 = 639919) (by norm_num)
theorem B2275267 : Blo 2273435 2275267 := bstep (se 1 (by rfl) ⟨1706450, by rfl⟩ : syracuseStep 2275267 = 3412901) B3412901
theorem B2879641 : Blo 2273435 2879641 := bbase (se 2 (by rfl) ⟨1079865, by rfl⟩ : syracuseStep 2879641 = 2159731) (by norm_num)
theorem B3839521 : Blo 2273435 3839521 := bstep (se 2 (by rfl) ⟨1439820, by rfl⟩ : syracuseStep 3839521 = 2879641) B2879641
theorem B5119361 : Blo 2273435 5119361 := bstep (se 2 (by rfl) ⟨1919760, by rfl⟩ : syracuseStep 5119361 = 3839521) B3839521
theorem B3412907 : Blo 2273435 3412907 := bstep (se 1 (by rfl) ⟨2559680, by rfl⟩ : syracuseStep 3412907 = 5119361) B5119361
theorem B2275271 : Blo 2273435 2275271 := bstep (se 1 (by rfl) ⟨1706453, by rfl⟩ : syracuseStep 2275271 = 3412907) B3412907
theorem B2559685 : Blo 2273435 2559685 := bbase (se 4 (by rfl) ⟨239970, by rfl⟩ : syracuseStep 2559685 = 479941) (by norm_num)
theorem B3412913 : Blo 2273435 3412913 := bstep (se 2 (by rfl) ⟨1279842, by rfl⟩ : syracuseStep 3412913 = 2559685) B2559685
theorem B2275275 : Blo 2273435 2275275 := bstep (se 1 (by rfl) ⟨1706456, by rfl⟩ : syracuseStep 2275275 = 3412913) B3412913
theorem B4319477 : Blo 2273435 4319477 := bbase (se 5 (by rfl) ⟨202475, by rfl⟩ : syracuseStep 4319477 = 404951) (by norm_num)
theorem B2879651 : Blo 2273435 2879651 := bstep (se 1 (by rfl) ⟨2159738, by rfl⟩ : syracuseStep 2879651 = 4319477) B4319477
theorem B7679069 : Blo 2273435 7679069 := bstep (se 3 (by rfl) ⟨1439825, by rfl⟩ : syracuseStep 7679069 = 2879651) B2879651
theorem B5119379 : Blo 2273435 5119379 := bstep (se 1 (by rfl) ⟨3839534, by rfl⟩ : syracuseStep 5119379 = 7679069) B7679069
theorem B3412919 : Blo 2273435 3412919 := bstep (se 1 (by rfl) ⟨2559689, by rfl⟩ : syracuseStep 3412919 = 5119379) B5119379
theorem B2275279 : Blo 2273435 2275279 := bstep (se 1 (by rfl) ⟨1706459, by rfl⟩ : syracuseStep 2275279 = 3412919) B3412919
theorem B3412925 : Blo 2273435 3412925 := bbase (se 3 (by rfl) ⟨639923, by rfl⟩ : syracuseStep 3412925 = 1279847) (by norm_num)
theorem B2275283 : Blo 2273435 2275283 := bstep (se 1 (by rfl) ⟨1706462, by rfl⟩ : syracuseStep 2275283 = 3412925) B3412925
theorem B5119397 : Blo 2273435 5119397 := bbase (se 4 (by rfl) ⟨479943, by rfl⟩ : syracuseStep 5119397 = 959887) (by norm_num)
theorem B3412931 : Blo 2273435 3412931 := bstep (se 1 (by rfl) ⟨2559698, by rfl⟩ : syracuseStep 3412931 = 5119397) B5119397
theorem B2275287 : Blo 2273435 2275287 := bstep (se 1 (by rfl) ⟨1706465, by rfl⟩ : syracuseStep 2275287 = 3412931) B3412931
theorem B5759333 : Blo 2273435 5759333 := bbase (se 4 (by rfl) ⟨539937, by rfl⟩ : syracuseStep 5759333 = 1079875) (by norm_num)
theorem B3839555 : Blo 2273435 3839555 := bstep (se 1 (by rfl) ⟨2879666, by rfl⟩ : syracuseStep 3839555 = 5759333) B5759333
theorem B2559703 : Blo 2273435 2559703 := bstep (se 1 (by rfl) ⟨1919777, by rfl⟩ : syracuseStep 2559703 = 3839555) B3839555
theorem B3412937 : Blo 2273435 3412937 := bstep (se 2 (by rfl) ⟨1279851, by rfl⟩ : syracuseStep 3412937 = 2559703) B2559703
theorem B2275291 : Blo 2273435 2275291 := bstep (se 1 (by rfl) ⟨1706468, by rfl⟩ : syracuseStep 2275291 = 3412937) B3412937
theorem B8756885 : Blo 2273435 8756885 := bbase (se 6 (by rfl) ⟨205239, by rfl⟩ : syracuseStep 8756885 = 410479) (by norm_num)
theorem B5837923 : Blo 2273435 5837923 := bstep (se 1 (by rfl) ⟨4378442, by rfl⟩ : syracuseStep 5837923 = 8756885) B8756885
theorem B31135589 : Blo 2273435 31135589 := bstep (se 4 (by rfl) ⟨2918961, by rfl⟩ : syracuseStep 31135589 = 5837923) B5837923
theorem B20757059 : Blo 2273435 20757059 := bstep (se 1 (by rfl) ⟨15567794, by rfl⟩ : syracuseStep 20757059 = 31135589) B31135589
theorem B13838039 : Blo 2273435 13838039 := bstep (se 1 (by rfl) ⟨10378529, by rfl⟩ : syracuseStep 13838039 = 20757059) B20757059
theorem B9225359 : Blo 2273435 9225359 := bstep (se 1 (by rfl) ⟨6919019, by rfl⟩ : syracuseStep 9225359 = 13838039) B13838039
theorem B6150239 : Blo 2273435 6150239 := bstep (se 1 (by rfl) ⟨4612679, by rfl⟩ : syracuseStep 6150239 = 9225359) B9225359
theorem B4100159 : Blo 2273435 4100159 := bstep (se 1 (by rfl) ⟨3075119, by rfl⟩ : syracuseStep 4100159 = 6150239) B6150239
theorem B2733439 : Blo 2273435 2733439 := bstep (se 1 (by rfl) ⟨2050079, by rfl⟩ : syracuseStep 2733439 = 4100159) B4100159
theorem B3644585 : Blo 2273435 3644585 := bstep (se 2 (by rfl) ⟨1366719, by rfl⟩ : syracuseStep 3644585 = 2733439) B2733439
theorem B2429723 : Blo 2273435 2429723 := bstep (se 1 (by rfl) ⟨1822292, by rfl⟩ : syracuseStep 2429723 = 3644585) B3644585
theorem B6479261 : Blo 2273435 6479261 := bstep (se 3 (by rfl) ⟨1214861, by rfl⟩ : syracuseStep 6479261 = 2429723) B2429723
theorem B4319507 : Blo 2273435 4319507 := bstep (se 1 (by rfl) ⟨3239630, by rfl⟩ : syracuseStep 4319507 = 6479261) B6479261
theorem B11518685 : Blo 2273435 11518685 := bstep (se 3 (by rfl) ⟨2159753, by rfl⟩ : syracuseStep 11518685 = 4319507) B4319507
theorem B7679123 : Blo 2273435 7679123 := bstep (se 1 (by rfl) ⟨5759342, by rfl⟩ : syracuseStep 7679123 = 11518685) B11518685
theorem B5119415 : Blo 2273435 5119415 := bstep (se 1 (by rfl) ⟨3839561, by rfl⟩ : syracuseStep 5119415 = 7679123) B7679123
theorem B3412943 : Blo 2273435 3412943 := bstep (se 1 (by rfl) ⟨2559707, by rfl⟩ : syracuseStep 3412943 = 5119415) B5119415
theorem B2275295 : Blo 2273435 2275295 := bstep (se 1 (by rfl) ⟨1706471, by rfl⟩ : syracuseStep 2275295 = 3412943) B3412943
theorem B3412949 : Blo 2273435 3412949 := bbase (se 7 (by rfl) ⟨39995, by rfl⟩ : syracuseStep 3412949 = 79991) (by norm_num)
theorem B2275299 : Blo 2273435 2275299 := bstep (se 1 (by rfl) ⟨1706474, by rfl⟩ : syracuseStep 2275299 = 3412949) B3412949
theorem B8639045 : Blo 2273435 8639045 := bbase (se 4 (by rfl) ⟨809910, by rfl⟩ : syracuseStep 8639045 = 1619821) (by norm_num)
theorem B5759363 : Blo 2273435 5759363 := bstep (se 1 (by rfl) ⟨4319522, by rfl⟩ : syracuseStep 5759363 = 8639045) B8639045
theorem B3839575 : Blo 2273435 3839575 := bstep (se 1 (by rfl) ⟨2879681, by rfl⟩ : syracuseStep 3839575 = 5759363) B5759363
theorem B5119433 : Blo 2273435 5119433 := bstep (se 2 (by rfl) ⟨1919787, by rfl⟩ : syracuseStep 5119433 = 3839575) B3839575
theorem B3412955 : Blo 2273435 3412955 := bstep (se 1 (by rfl) ⟨2559716, by rfl⟩ : syracuseStep 3412955 = 5119433) B5119433
theorem B2275303 : Blo 2273435 2275303 := bstep (se 1 (by rfl) ⟨1706477, by rfl⟩ : syracuseStep 2275303 = 3412955) B3412955
theorem B2559721 : Blo 2273435 2559721 := bbase (se 2 (by rfl) ⟨959895, by rfl⟩ : syracuseStep 2559721 = 1919791) (by norm_num)
theorem B3412961 : Blo 2273435 3412961 := bstep (se 2 (by rfl) ⟨1279860, by rfl⟩ : syracuseStep 3412961 = 2559721) B2559721
theorem B2275307 : Blo 2273435 2275307 := bstep (se 1 (by rfl) ⟨1706480, by rfl⟩ : syracuseStep 2275307 = 3412961) B3412961
theorem B12958613 : Blo 2273435 12958613 := bbase (se 6 (by rfl) ⟨303717, by rfl⟩ : syracuseStep 12958613 = 607435) (by norm_num)
theorem B8639075 : Blo 2273435 8639075 := bstep (se 1 (by rfl) ⟨6479306, by rfl⟩ : syracuseStep 8639075 = 12958613) B12958613
theorem B5759383 : Blo 2273435 5759383 := bstep (se 1 (by rfl) ⟨4319537, by rfl⟩ : syracuseStep 5759383 = 8639075) B8639075
theorem B7679177 : Blo 2273435 7679177 := bstep (se 2 (by rfl) ⟨2879691, by rfl⟩ : syracuseStep 7679177 = 5759383) B5759383
theorem B5119451 : Blo 2273435 5119451 := bstep (se 1 (by rfl) ⟨3839588, by rfl⟩ : syracuseStep 5119451 = 7679177) B7679177
theorem B3412967 : Blo 2273435 3412967 := bstep (se 1 (by rfl) ⟨2559725, by rfl⟩ : syracuseStep 3412967 = 5119451) B5119451
theorem B2275311 : Blo 2273435 2275311 := bstep (se 1 (by rfl) ⟨1706483, by rfl⟩ : syracuseStep 2275311 = 3412967) B3412967
theorem B3412973 : Blo 2273435 3412973 := bbase (se 3 (by rfl) ⟨639932, by rfl⟩ : syracuseStep 3412973 = 1279865) (by norm_num)
theorem B2275315 : Blo 2273435 2275315 := bstep (se 1 (by rfl) ⟨1706486, by rfl⟩ : syracuseStep 2275315 = 3412973) B3412973
theorem B5119469 : Blo 2273435 5119469 := bbase (se 3 (by rfl) ⟨959900, by rfl⟩ : syracuseStep 5119469 = 1919801) (by norm_num)
theorem B3412979 : Blo 2273435 3412979 := bstep (se 1 (by rfl) ⟨2559734, by rfl⟩ : syracuseStep 3412979 = 5119469) B5119469
theorem B2275319 : Blo 2273435 2275319 := bstep (se 1 (by rfl) ⟨1706489, by rfl⟩ : syracuseStep 2275319 = 3412979) B3412979
theorem B2733473 : Blo 2273435 2733473 := bbase (se 2 (by rfl) ⟨1025052, by rfl⟩ : syracuseStep 2733473 = 2050105) (by norm_num)
theorem B7289261 : Blo 2273435 7289261 := bstep (se 3 (by rfl) ⟨1366736, by rfl⟩ : syracuseStep 7289261 = 2733473) B2733473
theorem B4859507 : Blo 2273435 4859507 := bstep (se 1 (by rfl) ⟨3644630, by rfl⟩ : syracuseStep 4859507 = 7289261) B7289261
theorem B3239671 : Blo 2273435 3239671 := bstep (se 1 (by rfl) ⟨2429753, by rfl⟩ : syracuseStep 3239671 = 4859507) B4859507
theorem B4319561 : Blo 2273435 4319561 := bstep (se 2 (by rfl) ⟨1619835, by rfl⟩ : syracuseStep 4319561 = 3239671) B3239671
theorem B2879707 : Blo 2273435 2879707 := bstep (se 1 (by rfl) ⟨2159780, by rfl⟩ : syracuseStep 2879707 = 4319561) B4319561
theorem B3839609 : Blo 2273435 3839609 := bstep (se 2 (by rfl) ⟨1439853, by rfl⟩ : syracuseStep 3839609 = 2879707) B2879707
theorem B2559739 : Blo 2273435 2559739 := bstep (se 1 (by rfl) ⟨1919804, by rfl⟩ : syracuseStep 2559739 = 3839609) B3839609
theorem B3412985 : Blo 2273435 3412985 := bstep (se 2 (by rfl) ⟨1279869, by rfl⟩ : syracuseStep 3412985 = 2559739) B2559739
theorem B2275323 : Blo 2273435 2275323 := bstep (se 1 (by rfl) ⟨1706492, by rfl⟩ : syracuseStep 2275323 = 3412985) B3412985
theorem B2919001 : Blo 2273435 2919001 := bbase (se 2 (by rfl) ⟨1094625, by rfl⟩ : syracuseStep 2919001 = 2189251) (by norm_num)
theorem B3892001 : Blo 2273435 3892001 := bstep (se 2 (by rfl) ⟨1459500, by rfl⟩ : syracuseStep 3892001 = 2919001) B2919001
theorem B41514677 : Blo 2273435 41514677 := bstep (se 5 (by rfl) ⟨1946000, by rfl⟩ : syracuseStep 41514677 = 3892001) B3892001
theorem B27676451 : Blo 2273435 27676451 := bstep (se 1 (by rfl) ⟨20757338, by rfl⟩ : syracuseStep 27676451 = 41514677) B41514677
theorem B73803869 : Blo 2273435 73803869 := bstep (se 3 (by rfl) ⟨13838225, by rfl⟩ : syracuseStep 73803869 = 27676451) B27676451
theorem B49202579 : Blo 2273435 49202579 := bstep (se 1 (by rfl) ⟨36901934, by rfl⟩ : syracuseStep 49202579 = 73803869) B73803869
theorem B131206877 : Blo 2273435 131206877 := bstep (se 3 (by rfl) ⟨24601289, by rfl⟩ : syracuseStep 131206877 = 49202579) B49202579
theorem B87471251 : Blo 2273435 87471251 := bstep (se 1 (by rfl) ⟨65603438, by rfl⟩ : syracuseStep 87471251 = 131206877) B131206877
theorem B58314167 : Blo 2273435 58314167 := bstep (se 1 (by rfl) ⟨43735625, by rfl⟩ : syracuseStep 58314167 = 87471251) B87471251
theorem B38876111 : Blo 2273435 38876111 := bstep (se 1 (by rfl) ⟨29157083, by rfl⟩ : syracuseStep 38876111 = 58314167) B58314167
theorem B25917407 : Blo 2273435 25917407 := bstep (se 1 (by rfl) ⟨19438055, by rfl⟩ : syracuseStep 25917407 = 38876111) B38876111
theorem B17278271 : Blo 2273435 17278271 := bstep (se 1 (by rfl) ⟨12958703, by rfl⟩ : syracuseStep 17278271 = 25917407) B25917407
theorem B11518847 : Blo 2273435 11518847 := bstep (se 1 (by rfl) ⟨8639135, by rfl⟩ : syracuseStep 11518847 = 17278271) B17278271
theorem B7679231 : Blo 2273435 7679231 := bstep (se 1 (by rfl) ⟨5759423, by rfl⟩ : syracuseStep 7679231 = 11518847) B11518847
theorem B5119487 : Blo 2273435 5119487 := bstep (se 1 (by rfl) ⟨3839615, by rfl⟩ : syracuseStep 5119487 = 7679231) B7679231
theorem B3412991 : Blo 2273435 3412991 := bstep (se 1 (by rfl) ⟨2559743, by rfl⟩ : syracuseStep 3412991 = 5119487) B5119487
theorem B2275327 : Blo 2273435 2275327 := bstep (se 1 (by rfl) ⟨1706495, by rfl⟩ : syracuseStep 2275327 = 3412991) B3412991
theorem B3412997 : Blo 2273435 3412997 := bbase (se 4 (by rfl) ⟨319968, by rfl⟩ : syracuseStep 3412997 = 639937) (by norm_num)
theorem B2275331 : Blo 2273435 2275331 := bstep (se 1 (by rfl) ⟨1706498, by rfl⟩ : syracuseStep 2275331 = 3412997) B3412997
theorem B3839629 : Blo 2273435 3839629 := bbase (se 3 (by rfl) ⟨719930, by rfl⟩ : syracuseStep 3839629 = 1439861) (by norm_num)
theorem B5119505 : Blo 2273435 5119505 := bstep (se 2 (by rfl) ⟨1919814, by rfl⟩ : syracuseStep 5119505 = 3839629) B3839629
theorem B3413003 : Blo 2273435 3413003 := bstep (se 1 (by rfl) ⟨2559752, by rfl⟩ : syracuseStep 3413003 = 5119505) B5119505
theorem B2275335 : Blo 2273435 2275335 := bstep (se 1 (by rfl) ⟨1706501, by rfl⟩ : syracuseStep 2275335 = 3413003) B3413003
theorem B2559757 : Blo 2273435 2559757 := bbase (se 3 (by rfl) ⟨479954, by rfl⟩ : syracuseStep 2559757 = 959909) (by norm_num)
theorem B3413009 : Blo 2273435 3413009 := bstep (se 2 (by rfl) ⟨1279878, by rfl⟩ : syracuseStep 3413009 = 2559757) B2559757
theorem B2275339 : Blo 2273435 2275339 := bstep (se 1 (by rfl) ⟨1706504, by rfl⟩ : syracuseStep 2275339 = 3413009) B3413009
theorem B7679285 : Blo 2273435 7679285 := bbase (se 5 (by rfl) ⟨359966, by rfl⟩ : syracuseStep 7679285 = 719933) (by norm_num)
theorem B5119523 : Blo 2273435 5119523 := bstep (se 1 (by rfl) ⟨3839642, by rfl⟩ : syracuseStep 5119523 = 7679285) B7679285
theorem B3413015 : Blo 2273435 3413015 := bstep (se 1 (by rfl) ⟨2559761, by rfl⟩ : syracuseStep 3413015 = 5119523) B5119523
theorem B2275343 : Blo 2273435 2275343 := bstep (se 1 (by rfl) ⟨1706507, by rfl⟩ : syracuseStep 2275343 = 3413015) B3413015
theorem B3413021 : Blo 2273435 3413021 := bbase (se 3 (by rfl) ⟨639941, by rfl⟩ : syracuseStep 3413021 = 1279883) (by norm_num)
theorem B2275347 : Blo 2273435 2275347 := bstep (se 1 (by rfl) ⟨1706510, by rfl⟩ : syracuseStep 2275347 = 3413021) B3413021
theorem B5119541 : Blo 2273435 5119541 := bbase (se 5 (by rfl) ⟨239978, by rfl⟩ : syracuseStep 5119541 = 479957) (by norm_num)
theorem B3413027 : Blo 2273435 3413027 := bstep (se 1 (by rfl) ⟨2559770, by rfl⟩ : syracuseStep 3413027 = 5119541) B5119541
theorem B2275351 : Blo 2273435 2275351 := bstep (se 1 (by rfl) ⟨1706513, by rfl⟩ : syracuseStep 2275351 = 3413027) B3413027
theorem B2594701 : Blo 2273435 2594701 := bbase (se 3 (by rfl) ⟨486506, by rfl⟩ : syracuseStep 2594701 = 973013) (by norm_num)
theorem B3459601 : Blo 2273435 3459601 := bstep (se 2 (by rfl) ⟨1297350, by rfl⟩ : syracuseStep 3459601 = 2594701) B2594701
theorem B4612801 : Blo 2273435 4612801 := bstep (se 2 (by rfl) ⟨1729800, by rfl⟩ : syracuseStep 4612801 = 3459601) B3459601
theorem B6150401 : Blo 2273435 6150401 := bstep (se 2 (by rfl) ⟨2306400, by rfl⟩ : syracuseStep 6150401 = 4612801) B4612801
theorem B4100267 : Blo 2273435 4100267 := bstep (se 1 (by rfl) ⟨3075200, by rfl⟩ : syracuseStep 4100267 = 6150401) B6150401
theorem B2733511 : Blo 2273435 2733511 := bstep (se 1 (by rfl) ⟨2050133, by rfl⟩ : syracuseStep 2733511 = 4100267) B4100267
theorem B3644681 : Blo 2273435 3644681 := bstep (se 2 (by rfl) ⟨1366755, by rfl⟩ : syracuseStep 3644681 = 2733511) B2733511
theorem B9719149 : Blo 2273435 9719149 := bstep (se 3 (by rfl) ⟨1822340, by rfl⟩ : syracuseStep 9719149 = 3644681) B3644681
theorem B12958865 : Blo 2273435 12958865 := bstep (se 2 (by rfl) ⟨4859574, by rfl⟩ : syracuseStep 12958865 = 9719149) B9719149
theorem B8639243 : Blo 2273435 8639243 := bstep (se 1 (by rfl) ⟨6479432, by rfl⟩ : syracuseStep 8639243 = 12958865) B12958865
theorem B5759495 : Blo 2273435 5759495 := bstep (se 1 (by rfl) ⟨4319621, by rfl⟩ : syracuseStep 5759495 = 8639243) B8639243
theorem B3839663 : Blo 2273435 3839663 := bstep (se 1 (by rfl) ⟨2879747, by rfl⟩ : syracuseStep 3839663 = 5759495) B5759495
theorem B2559775 : Blo 2273435 2559775 := bstep (se 1 (by rfl) ⟨1919831, by rfl⟩ : syracuseStep 2559775 = 3839663) B3839663
theorem B3413033 : Blo 2273435 3413033 := bstep (se 2 (by rfl) ⟨1279887, by rfl⟩ : syracuseStep 3413033 = 2559775) B2559775
theorem B2275355 : Blo 2273435 2275355 := bstep (se 1 (by rfl) ⟨1706516, by rfl⟩ : syracuseStep 2275355 = 3413033) B3413033
theorem B12300821 : Blo 2273435 12300821 := bbase (se 6 (by rfl) ⟨288300, by rfl⟩ : syracuseStep 12300821 = 576601) (by norm_num)
theorem B8200547 : Blo 2273435 8200547 := bstep (se 1 (by rfl) ⟨6150410, by rfl⟩ : syracuseStep 8200547 = 12300821) B12300821
theorem B5467031 : Blo 2273435 5467031 := bstep (se 1 (by rfl) ⟨4100273, by rfl⟩ : syracuseStep 5467031 = 8200547) B8200547
theorem B3644687 : Blo 2273435 3644687 := bstep (se 1 (by rfl) ⟨2733515, by rfl⟩ : syracuseStep 3644687 = 5467031) B5467031
theorem B9719165 : Blo 2273435 9719165 := bstep (se 3 (by rfl) ⟨1822343, by rfl⟩ : syracuseStep 9719165 = 3644687) B3644687
theorem B6479443 : Blo 2273435 6479443 := bstep (se 1 (by rfl) ⟨4859582, by rfl⟩ : syracuseStep 6479443 = 9719165) B9719165
theorem B8639257 : Blo 2273435 8639257 := bstep (se 2 (by rfl) ⟨3239721, by rfl⟩ : syracuseStep 8639257 = 6479443) B6479443
theorem B11519009 : Blo 2273435 11519009 := bstep (se 2 (by rfl) ⟨4319628, by rfl⟩ : syracuseStep 11519009 = 8639257) B8639257
theorem B7679339 : Blo 2273435 7679339 := bstep (se 1 (by rfl) ⟨5759504, by rfl⟩ : syracuseStep 7679339 = 11519009) B11519009
theorem B5119559 : Blo 2273435 5119559 := bstep (se 1 (by rfl) ⟨3839669, by rfl⟩ : syracuseStep 5119559 = 7679339) B7679339
theorem B3413039 : Blo 2273435 3413039 := bstep (se 1 (by rfl) ⟨2559779, by rfl⟩ : syracuseStep 3413039 = 5119559) B5119559
theorem B2275359 : Blo 2273435 2275359 := bstep (se 1 (by rfl) ⟨1706519, by rfl⟩ : syracuseStep 2275359 = 3413039) B3413039
theorem B3413045 : Blo 2273435 3413045 := bbase (se 5 (by rfl) ⟨159986, by rfl⟩ : syracuseStep 3413045 = 319973) (by norm_num)
theorem B2275363 : Blo 2273435 2275363 := bstep (se 1 (by rfl) ⟨1706522, by rfl⟩ : syracuseStep 2275363 = 3413045) B3413045
theorem B5759525 : Blo 2273435 5759525 := bbase (se 4 (by rfl) ⟨539955, by rfl⟩ : syracuseStep 5759525 = 1079911) (by norm_num)
theorem B3839683 : Blo 2273435 3839683 := bstep (se 1 (by rfl) ⟨2879762, by rfl⟩ : syracuseStep 3839683 = 5759525) B5759525
theorem B5119577 : Blo 2273435 5119577 := bstep (se 2 (by rfl) ⟨1919841, by rfl⟩ : syracuseStep 5119577 = 3839683) B3839683
theorem B3413051 : Blo 2273435 3413051 := bstep (se 1 (by rfl) ⟨2559788, by rfl⟩ : syracuseStep 3413051 = 5119577) B5119577
theorem B2275367 : Blo 2273435 2275367 := bstep (se 1 (by rfl) ⟨1706525, by rfl⟩ : syracuseStep 2275367 = 3413051) B3413051
theorem B2559793 : Blo 2273435 2559793 := bbase (se 2 (by rfl) ⟨959922, by rfl⟩ : syracuseStep 2559793 = 1919845) (by norm_num)
theorem B3413057 : Blo 2273435 3413057 := bstep (se 2 (by rfl) ⟨1279896, by rfl⟩ : syracuseStep 3413057 = 2559793) B2559793
theorem B2275371 : Blo 2273435 2275371 := bstep (se 1 (by rfl) ⟨1706528, by rfl⟩ : syracuseStep 2275371 = 3413057) B3413057
theorem B9351557 : Blo 2273435 9351557 := bbase (se 4 (by rfl) ⟨876708, by rfl⟩ : syracuseStep 9351557 = 1753417) (by norm_num)
theorem B6234371 : Blo 2273435 6234371 := bstep (se 1 (by rfl) ⟨4675778, by rfl⟩ : syracuseStep 6234371 = 9351557) B9351557
theorem B4156247 : Blo 2273435 4156247 := bstep (se 1 (by rfl) ⟨3117185, by rfl⟩ : syracuseStep 4156247 = 6234371) B6234371
theorem B2770831 : Blo 2273435 2770831 := bstep (se 1 (by rfl) ⟨2078123, by rfl⟩ : syracuseStep 2770831 = 4156247) B4156247
theorem B14777765 : Blo 2273435 14777765 := bstep (se 4 (by rfl) ⟨1385415, by rfl⟩ : syracuseStep 14777765 = 2770831) B2770831
theorem B9851843 : Blo 2273435 9851843 := bstep (se 1 (by rfl) ⟨7388882, by rfl⟩ : syracuseStep 9851843 = 14777765) B14777765
theorem B6567895 : Blo 2273435 6567895 := bstep (se 1 (by rfl) ⟨4925921, by rfl⟩ : syracuseStep 6567895 = 9851843) B9851843
theorem B8757193 : Blo 2273435 8757193 := bstep (se 2 (by rfl) ⟨3283947, by rfl⟩ : syracuseStep 8757193 = 6567895) B6567895
theorem B11676257 : Blo 2273435 11676257 := bstep (se 2 (by rfl) ⟨4378596, by rfl⟩ : syracuseStep 11676257 = 8757193) B8757193
theorem B7784171 : Blo 2273435 7784171 := bstep (se 1 (by rfl) ⟨5838128, by rfl⟩ : syracuseStep 7784171 = 11676257) B11676257
theorem B5189447 : Blo 2273435 5189447 := bstep (se 1 (by rfl) ⟨3892085, by rfl⟩ : syracuseStep 5189447 = 7784171) B7784171
theorem B13838525 : Blo 2273435 13838525 := bstep (se 3 (by rfl) ⟨2594723, by rfl⟩ : syracuseStep 13838525 = 5189447) B5189447
theorem B9225683 : Blo 2273435 9225683 := bstep (se 1 (by rfl) ⟨6919262, by rfl⟩ : syracuseStep 9225683 = 13838525) B13838525
theorem B6150455 : Blo 2273435 6150455 := bstep (se 1 (by rfl) ⟨4612841, by rfl⟩ : syracuseStep 6150455 = 9225683) B9225683
theorem B4100303 : Blo 2273435 4100303 := bstep (se 1 (by rfl) ⟨3075227, by rfl⟩ : syracuseStep 4100303 = 6150455) B6150455
theorem B2733535 : Blo 2273435 2733535 := bstep (se 1 (by rfl) ⟨2050151, by rfl⟩ : syracuseStep 2733535 = 4100303) B4100303
theorem B3644713 : Blo 2273435 3644713 := bstep (se 2 (by rfl) ⟨1366767, by rfl⟩ : syracuseStep 3644713 = 2733535) B2733535
theorem B4859617 : Blo 2273435 4859617 := bstep (se 2 (by rfl) ⟨1822356, by rfl⟩ : syracuseStep 4859617 = 3644713) B3644713
theorem B6479489 : Blo 2273435 6479489 := bstep (se 2 (by rfl) ⟨2429808, by rfl⟩ : syracuseStep 6479489 = 4859617) B4859617
theorem B4319659 : Blo 2273435 4319659 := bstep (se 1 (by rfl) ⟨3239744, by rfl⟩ : syracuseStep 4319659 = 6479489) B6479489
theorem B5759545 : Blo 2273435 5759545 := bstep (se 2 (by rfl) ⟨2159829, by rfl⟩ : syracuseStep 5759545 = 4319659) B4319659
theorem B7679393 : Blo 2273435 7679393 := bstep (se 2 (by rfl) ⟨2879772, by rfl⟩ : syracuseStep 7679393 = 5759545) B5759545
theorem B5119595 : Blo 2273435 5119595 := bstep (se 1 (by rfl) ⟨3839696, by rfl⟩ : syracuseStep 5119595 = 7679393) B7679393
theorem B3413063 : Blo 2273435 3413063 := bstep (se 1 (by rfl) ⟨2559797, by rfl⟩ : syracuseStep 3413063 = 5119595) B5119595
theorem B2275375 : Blo 2273435 2275375 := bstep (se 1 (by rfl) ⟨1706531, by rfl⟩ : syracuseStep 2275375 = 3413063) B3413063
theorem B3413069 : Blo 2273435 3413069 := bbase (se 3 (by rfl) ⟨639950, by rfl⟩ : syracuseStep 3413069 = 1279901) (by norm_num)
theorem B2275379 : Blo 2273435 2275379 := bstep (se 1 (by rfl) ⟨1706534, by rfl⟩ : syracuseStep 2275379 = 3413069) B3413069
theorem B5119613 : Blo 2273435 5119613 := bbase (se 3 (by rfl) ⟨959927, by rfl⟩ : syracuseStep 5119613 = 1919855) (by norm_num)
theorem B3413075 : Blo 2273435 3413075 := bstep (se 1 (by rfl) ⟨2559806, by rfl⟩ : syracuseStep 3413075 = 5119613) B5119613
theorem B2275383 : Blo 2273435 2275383 := bstep (se 1 (by rfl) ⟨1706537, by rfl⟩ : syracuseStep 2275383 = 3413075) B3413075
theorem B3839717 : Blo 2273435 3839717 := bbase (se 4 (by rfl) ⟨359973, by rfl⟩ : syracuseStep 3839717 = 719947) (by norm_num)
theorem B2559811 : Blo 2273435 2559811 := bstep (se 1 (by rfl) ⟨1919858, by rfl⟩ : syracuseStep 2559811 = 3839717) B3839717
theorem B3413081 : Blo 2273435 3413081 := bstep (se 2 (by rfl) ⟨1279905, by rfl⟩ : syracuseStep 3413081 = 2559811) B2559811
theorem B2275387 : Blo 2273435 2275387 := bstep (se 1 (by rfl) ⟨1706540, by rfl⟩ : syracuseStep 2275387 = 3413081) B3413081
theorem B7289477 : Blo 2273435 7289477 := bbase (se 4 (by rfl) ⟨683388, by rfl⟩ : syracuseStep 7289477 = 1366777) (by norm_num)
theorem B4859651 : Blo 2273435 4859651 := bstep (se 1 (by rfl) ⟨3644738, by rfl⟩ : syracuseStep 4859651 = 7289477) B7289477
theorem B3239767 : Blo 2273435 3239767 := bstep (se 1 (by rfl) ⟨2429825, by rfl⟩ : syracuseStep 3239767 = 4859651) B4859651
theorem B17278757 : Blo 2273435 17278757 := bstep (se 4 (by rfl) ⟨1619883, by rfl⟩ : syracuseStep 17278757 = 3239767) B3239767
theorem B11519171 : Blo 2273435 11519171 := bstep (se 1 (by rfl) ⟨8639378, by rfl⟩ : syracuseStep 11519171 = 17278757) B17278757
theorem B7679447 : Blo 2273435 7679447 := bstep (se 1 (by rfl) ⟨5759585, by rfl⟩ : syracuseStep 7679447 = 11519171) B11519171
theorem B5119631 : Blo 2273435 5119631 := bstep (se 1 (by rfl) ⟨3839723, by rfl⟩ : syracuseStep 5119631 = 7679447) B7679447
theorem B3413087 : Blo 2273435 3413087 := bstep (se 1 (by rfl) ⟨2559815, by rfl⟩ : syracuseStep 3413087 = 5119631) B5119631
theorem B2275391 : Blo 2273435 2275391 := bstep (se 1 (by rfl) ⟨1706543, by rfl⟩ : syracuseStep 2275391 = 3413087) B3413087
theorem B3413093 : Blo 2273435 3413093 := bbase (se 4 (by rfl) ⟨319977, by rfl⟩ : syracuseStep 3413093 = 639955) (by norm_num)
theorem B2275395 : Blo 2273435 2275395 := bstep (se 1 (by rfl) ⟨1706546, by rfl⟩ : syracuseStep 2275395 = 3413093) B3413093
theorem B4859669 : Blo 2273435 4859669 := bbase (se 6 (by rfl) ⟨113898, by rfl⟩ : syracuseStep 4859669 = 227797) (by norm_num)
theorem B3239779 : Blo 2273435 3239779 := bstep (se 1 (by rfl) ⟨2429834, by rfl⟩ : syracuseStep 3239779 = 4859669) B4859669
theorem B4319705 : Blo 2273435 4319705 := bstep (se 2 (by rfl) ⟨1619889, by rfl⟩ : syracuseStep 4319705 = 3239779) B3239779
theorem B2879803 : Blo 2273435 2879803 := bstep (se 1 (by rfl) ⟨2159852, by rfl⟩ : syracuseStep 2879803 = 4319705) B4319705
theorem B3839737 : Blo 2273435 3839737 := bstep (se 2 (by rfl) ⟨1439901, by rfl⟩ : syracuseStep 3839737 = 2879803) B2879803
theorem B5119649 : Blo 2273435 5119649 := bstep (se 2 (by rfl) ⟨1919868, by rfl⟩ : syracuseStep 5119649 = 3839737) B3839737
theorem B3413099 : Blo 2273435 3413099 := bstep (se 1 (by rfl) ⟨2559824, by rfl⟩ : syracuseStep 3413099 = 5119649) B5119649
theorem B2275399 : Blo 2273435 2275399 := bstep (se 1 (by rfl) ⟨1706549, by rfl⟩ : syracuseStep 2275399 = 3413099) B3413099
theorem B2559829 : Blo 2273435 2559829 := bbase (se 9 (by rfl) ⟨7499, by rfl⟩ : syracuseStep 2559829 = 14999) (by norm_num)
theorem B3413105 : Blo 2273435 3413105 := bstep (se 2 (by rfl) ⟨1279914, by rfl⟩ : syracuseStep 3413105 = 2559829) B2559829
theorem B2275403 : Blo 2273435 2275403 := bstep (se 1 (by rfl) ⟨1706552, by rfl⟩ : syracuseStep 2275403 = 3413105) B3413105
theorem B2879813 : Blo 2273435 2879813 := bbase (se 4 (by rfl) ⟨269982, by rfl⟩ : syracuseStep 2879813 = 539965) (by norm_num)
theorem B7679501 : Blo 2273435 7679501 := bstep (se 3 (by rfl) ⟨1439906, by rfl⟩ : syracuseStep 7679501 = 2879813) B2879813
theorem B5119667 : Blo 2273435 5119667 := bstep (se 1 (by rfl) ⟨3839750, by rfl⟩ : syracuseStep 5119667 = 7679501) B7679501
theorem B3413111 : Blo 2273435 3413111 := bstep (se 1 (by rfl) ⟨2559833, by rfl⟩ : syracuseStep 3413111 = 5119667) B5119667
theorem B2275407 : Blo 2273435 2275407 := bstep (se 1 (by rfl) ⟨1706555, by rfl⟩ : syracuseStep 2275407 = 3413111) B3413111
theorem B3413117 : Blo 2273435 3413117 := bbase (se 3 (by rfl) ⟨639959, by rfl⟩ : syracuseStep 3413117 = 1279919) (by norm_num)
theorem B2275411 : Blo 2273435 2275411 := bstep (se 1 (by rfl) ⟨1706558, by rfl⟩ : syracuseStep 2275411 = 3413117) B3413117
theorem B5119685 : Blo 2273435 5119685 := bbase (se 4 (by rfl) ⟨479970, by rfl⟩ : syracuseStep 5119685 = 959941) (by norm_num)
theorem B3413123 : Blo 2273435 3413123 := bstep (se 1 (by rfl) ⟨2559842, by rfl⟩ : syracuseStep 3413123 = 5119685) B5119685
theorem B2275415 : Blo 2273435 2275415 := bstep (se 1 (by rfl) ⟨1706561, by rfl⟩ : syracuseStep 2275415 = 3413123) B3413123
theorem B5260349 : Blo 2273435 5260349 := bbase (se 3 (by rfl) ⟨986315, by rfl⟩ : syracuseStep 5260349 = 1972631) (by norm_num)
theorem B14027597 : Blo 2273435 14027597 := bstep (se 3 (by rfl) ⟨2630174, by rfl⟩ : syracuseStep 14027597 = 5260349) B5260349
theorem B9351731 : Blo 2273435 9351731 := bstep (se 1 (by rfl) ⟨7013798, by rfl⟩ : syracuseStep 9351731 = 14027597) B14027597
theorem B6234487 : Blo 2273435 6234487 := bstep (se 1 (by rfl) ⟨4675865, by rfl⟩ : syracuseStep 6234487 = 9351731) B9351731
theorem B33250597 : Blo 2273435 33250597 := bstep (se 4 (by rfl) ⟨3117243, by rfl⟩ : syracuseStep 33250597 = 6234487) B6234487
theorem B709346069 : Blo 2273435 709346069 := bstep (se 6 (by rfl) ⟨16625298, by rfl⟩ : syracuseStep 709346069 = 33250597) B33250597
theorem B472897379 : Blo 2273435 472897379 := bstep (se 1 (by rfl) ⟨354673034, by rfl⟩ : syracuseStep 472897379 = 709346069) B709346069
theorem B315264919 : Blo 2273435 315264919 := bstep (se 1 (by rfl) ⟨236448689, by rfl⟩ : syracuseStep 315264919 = 472897379) B472897379
theorem B420353225 : Blo 2273435 420353225 := bstep (se 2 (by rfl) ⟨157632459, by rfl⟩ : syracuseStep 420353225 = 315264919) B315264919
theorem B280235483 : Blo 2273435 280235483 := bstep (se 1 (by rfl) ⟨210176612, by rfl⟩ : syracuseStep 280235483 = 420353225) B420353225
theorem B186823655 : Blo 2273435 186823655 := bstep (se 1 (by rfl) ⟨140117741, by rfl⟩ : syracuseStep 186823655 = 280235483) B280235483
theorem B124549103 : Blo 2273435 124549103 := bstep (se 1 (by rfl) ⟨93411827, by rfl⟩ : syracuseStep 124549103 = 186823655) B186823655
theorem B83032735 : Blo 2273435 83032735 := bstep (se 1 (by rfl) ⟨62274551, by rfl⟩ : syracuseStep 83032735 = 124549103) B124549103
theorem B110710313 : Blo 2273435 110710313 := bstep (se 2 (by rfl) ⟨41516367, by rfl⟩ : syracuseStep 110710313 = 83032735) B83032735
theorem B73806875 : Blo 2273435 73806875 := bstep (se 1 (by rfl) ⟨55355156, by rfl⟩ : syracuseStep 73806875 = 110710313) B110710313
theorem B49204583 : Blo 2273435 49204583 := bstep (se 1 (by rfl) ⟨36903437, by rfl⟩ : syracuseStep 49204583 = 73806875) B73806875
theorem B32803055 : Blo 2273435 32803055 := bstep (se 1 (by rfl) ⟨24602291, by rfl⟩ : syracuseStep 32803055 = 49204583) B49204583
theorem B21868703 : Blo 2273435 21868703 := bstep (se 1 (by rfl) ⟨16401527, by rfl⟩ : syracuseStep 21868703 = 32803055) B32803055
theorem B14579135 : Blo 2273435 14579135 := bstep (se 1 (by rfl) ⟨10934351, by rfl⟩ : syracuseStep 14579135 = 21868703) B21868703
theorem B9719423 : Blo 2273435 9719423 := bstep (se 1 (by rfl) ⟨7289567, by rfl⟩ : syracuseStep 9719423 = 14579135) B14579135
theorem B6479615 : Blo 2273435 6479615 := bstep (se 1 (by rfl) ⟨4859711, by rfl⟩ : syracuseStep 6479615 = 9719423) B9719423
theorem B4319743 : Blo 2273435 4319743 := bstep (se 1 (by rfl) ⟨3239807, by rfl⟩ : syracuseStep 4319743 = 6479615) B6479615
theorem B5759657 : Blo 2273435 5759657 := bstep (se 2 (by rfl) ⟨2159871, by rfl⟩ : syracuseStep 5759657 = 4319743) B4319743
theorem B3839771 : Blo 2273435 3839771 := bstep (se 1 (by rfl) ⟨2879828, by rfl⟩ : syracuseStep 3839771 = 5759657) B5759657
theorem B2559847 : Blo 2273435 2559847 := bstep (se 1 (by rfl) ⟨1919885, by rfl⟩ : syracuseStep 2559847 = 3839771) B3839771
theorem B3413129 : Blo 2273435 3413129 := bstep (se 2 (by rfl) ⟨1279923, by rfl⟩ : syracuseStep 3413129 = 2559847) B2559847
theorem B2275419 : Blo 2273435 2275419 := bstep (se 1 (by rfl) ⟨1706564, by rfl⟩ : syracuseStep 2275419 = 3413129) B3413129
theorem B11519333 : Blo 2273435 11519333 := bbase (se 4 (by rfl) ⟨1079937, by rfl⟩ : syracuseStep 11519333 = 2159875) (by norm_num)
theorem B7679555 : Blo 2273435 7679555 := bstep (se 1 (by rfl) ⟨5759666, by rfl⟩ : syracuseStep 7679555 = 11519333) B11519333
theorem B5119703 : Blo 2273435 5119703 := bstep (se 1 (by rfl) ⟨3839777, by rfl⟩ : syracuseStep 5119703 = 7679555) B7679555
theorem B3413135 : Blo 2273435 3413135 := bstep (se 1 (by rfl) ⟨2559851, by rfl⟩ : syracuseStep 3413135 = 5119703) B5119703
theorem B2275423 : Blo 2273435 2275423 := bstep (se 1 (by rfl) ⟨1706567, by rfl⟩ : syracuseStep 2275423 = 3413135) B3413135
theorem B3413141 : Blo 2273435 3413141 := bbase (se 6 (by rfl) ⟨79995, by rfl⟩ : syracuseStep 3413141 = 159991) (by norm_num)
theorem B2275427 : Blo 2273435 2275427 := bstep (se 1 (by rfl) ⟨1706570, by rfl⟩ : syracuseStep 2275427 = 3413141) B3413141
theorem B7289605 : Blo 2273435 7289605 := bbase (se 4 (by rfl) ⟨683400, by rfl⟩ : syracuseStep 7289605 = 1366801) (by norm_num)
theorem B9719473 : Blo 2273435 9719473 := bstep (se 2 (by rfl) ⟨3644802, by rfl⟩ : syracuseStep 9719473 = 7289605) B7289605
theorem B12959297 : Blo 2273435 12959297 := bstep (se 2 (by rfl) ⟨4859736, by rfl⟩ : syracuseStep 12959297 = 9719473) B9719473
theorem B8639531 : Blo 2273435 8639531 := bstep (se 1 (by rfl) ⟨6479648, by rfl⟩ : syracuseStep 8639531 = 12959297) B12959297
theorem B5759687 : Blo 2273435 5759687 := bstep (se 1 (by rfl) ⟨4319765, by rfl⟩ : syracuseStep 5759687 = 8639531) B8639531
theorem B3839791 : Blo 2273435 3839791 := bstep (se 1 (by rfl) ⟨2879843, by rfl⟩ : syracuseStep 3839791 = 5759687) B5759687
theorem B5119721 : Blo 2273435 5119721 := bstep (se 2 (by rfl) ⟨1919895, by rfl⟩ : syracuseStep 5119721 = 3839791) B3839791
theorem B3413147 : Blo 2273435 3413147 := bstep (se 1 (by rfl) ⟨2559860, by rfl⟩ : syracuseStep 3413147 = 5119721) B5119721
theorem B2275431 : Blo 2273435 2275431 := bstep (se 1 (by rfl) ⟨1706573, by rfl⟩ : syracuseStep 2275431 = 3413147) B3413147
theorem B2559865 : Blo 2273435 2559865 := bbase (se 2 (by rfl) ⟨959949, by rfl⟩ : syracuseStep 2559865 = 1919899) (by norm_num)
theorem B3413153 : Blo 2273435 3413153 := bstep (se 2 (by rfl) ⟨1279932, by rfl⟩ : syracuseStep 3413153 = 2559865) B2559865
theorem B2275435 : Blo 2273435 2275435 := bstep (se 1 (by rfl) ⟨1706576, by rfl⟩ : syracuseStep 2275435 = 3413153) B3413153
theorem C0 (j : ℕ) (h1 : 568358 ≤ j) (h2 : j ≤ 568858) : Blo 2273435 (4 * j + 3) := by
  interval_cases j
  · exact B2273435
  · exact B2273439
  · exact B2273443
  · exact B2273447
  · exact B2273451
  · exact B2273455
  · exact B2273459
  · exact B2273463
  · exact B2273467
  · exact B2273471
  · exact B2273475
  · exact B2273479
  · exact B2273483
  · exact B2273487
  · exact B2273491
  · exact B2273495
  · exact B2273499
  · exact B2273503
  · exact B2273507
  · exact B2273511
  · exact B2273515
  · exact B2273519
  · exact B2273523
  · exact B2273527
  · exact B2273531
  · exact B2273535
  · exact B2273539
  · exact B2273543
  · exact B2273547
  · exact B2273551
  · exact B2273555
  · exact B2273559
  · exact B2273563
  · exact B2273567
  · exact B2273571
  · exact B2273575
  · exact B2273579
  · exact B2273583
  · exact B2273587
  · exact B2273591
  · exact B2273595
  · exact B2273599
  · exact B2273603
  · exact B2273607
  · exact B2273611
  · exact B2273615
  · exact B2273619
  · exact B2273623
  · exact B2273627
  · exact B2273631
  · exact B2273635
  · exact B2273639
  · exact B2273643
  · exact B2273647
  · exact B2273651
  · exact B2273655
  · exact B2273659
  · exact B2273663
  · exact B2273667
  · exact B2273671
  · exact B2273675
  · exact B2273679
  · exact B2273683
  · exact B2273687
  · exact B2273691
  · exact B2273695
  · exact B2273699
  · exact B2273703
  · exact B2273707
  · exact B2273711
  · exact B2273715
  · exact B2273719
  · exact B2273723
  · exact B2273727
  · exact B2273731
  · exact B2273735
  · exact B2273739
  · exact B2273743
  · exact B2273747
  · exact B2273751
  · exact B2273755
  · exact B2273759
  · exact B2273763
  · exact B2273767
  · exact B2273771
  · exact B2273775
  · exact B2273779
  · exact B2273783
  · exact B2273787
  · exact B2273791
  · exact B2273795
  · exact B2273799
  · exact B2273803
  · exact B2273807
  · exact B2273811
  · exact B2273815
  · exact B2273819
  · exact B2273823
  · exact B2273827
  · exact B2273831
  · exact B2273835
  · exact B2273839
  · exact B2273843
  · exact B2273847
  · exact B2273851
  · exact B2273855
  · exact B2273859
  · exact B2273863
  · exact B2273867
  · exact B2273871
  · exact B2273875
  · exact B2273879
  · exact B2273883
  · exact B2273887
  · exact B2273891
  · exact B2273895
  · exact B2273899
  · exact B2273903
  · exact B2273907
  · exact B2273911
  · exact B2273915
  · exact B2273919
  · exact B2273923
  · exact B2273927
  · exact B2273931
  · exact B2273935
  · exact B2273939
  · exact B2273943
  · exact B2273947
  · exact B2273951
  · exact B2273955
  · exact B2273959
  · exact B2273963
  · exact B2273967
  · exact B2273971
  · exact B2273975
  · exact B2273979
  · exact B2273983
  · exact B2273987
  · exact B2273991
  · exact B2273995
  · exact B2273999
  · exact B2274003
  · exact B2274007
  · exact B2274011
  · exact B2274015
  · exact B2274019
  · exact B2274023
  · exact B2274027
  · exact B2274031
  · exact B2274035
  · exact B2274039
  · exact B2274043
  · exact B2274047
  · exact B2274051
  · exact B2274055
  · exact B2274059
  · exact B2274063
  · exact B2274067
  · exact B2274071
  · exact B2274075
  · exact B2274079
  · exact B2274083
  · exact B2274087
  · exact B2274091
  · exact B2274095
  · exact B2274099
  · exact B2274103
  · exact B2274107
  · exact B2274111
  · exact B2274115
  · exact B2274119
  · exact B2274123
  · exact B2274127
  · exact B2274131
  · exact B2274135
  · exact B2274139
  · exact B2274143
  · exact B2274147
  · exact B2274151
  · exact B2274155
  · exact B2274159
  · exact B2274163
  · exact B2274167
  · exact B2274171
  · exact B2274175
  · exact B2274179
  · exact B2274183
  · exact B2274187
  · exact B2274191
  · exact B2274195
  · exact B2274199
  · exact B2274203
  · exact B2274207
  · exact B2274211
  · exact B2274215
  · exact B2274219
  · exact B2274223
  · exact B2274227
  · exact B2274231
  · exact B2274235
  · exact B2274239
  · exact B2274243
  · exact B2274247
  · exact B2274251
  · exact B2274255
  · exact B2274259
  · exact B2274263
  · exact B2274267
  · exact B2274271
  · exact B2274275
  · exact B2274279
  · exact B2274283
  · exact B2274287
  · exact B2274291
  · exact B2274295
  · exact B2274299
  · exact B2274303
  · exact B2274307
  · exact B2274311
  · exact B2274315
  · exact B2274319
  · exact B2274323
  · exact B2274327
  · exact B2274331
  · exact B2274335
  · exact B2274339
  · exact B2274343
  · exact B2274347
  · exact B2274351
  · exact B2274355
  · exact B2274359
  · exact B2274363
  · exact B2274367
  · exact B2274371
  · exact B2274375
  · exact B2274379
  · exact B2274383
  · exact B2274387
  · exact B2274391
  · exact B2274395
  · exact B2274399
  · exact B2274403
  · exact B2274407
  · exact B2274411
  · exact B2274415
  · exact B2274419
  · exact B2274423
  · exact B2274427
  · exact B2274431
  · exact B2274435
  · exact B2274439
  · exact B2274443
  · exact B2274447
  · exact B2274451
  · exact B2274455
  · exact B2274459
  · exact B2274463
  · exact B2274467
  · exact B2274471
  · exact B2274475
  · exact B2274479
  · exact B2274483
  · exact B2274487
  · exact B2274491
  · exact B2274495
  · exact B2274499
  · exact B2274503
  · exact B2274507
  · exact B2274511
  · exact B2274515
  · exact B2274519
  · exact B2274523
  · exact B2274527
  · exact B2274531
  · exact B2274535
  · exact B2274539
  · exact B2274543
  · exact B2274547
  · exact B2274551
  · exact B2274555
  · exact B2274559
  · exact B2274563
  · exact B2274567
  · exact B2274571
  · exact B2274575
  · exact B2274579
  · exact B2274583
  · exact B2274587
  · exact B2274591
  · exact B2274595
  · exact B2274599
  · exact B2274603
  · exact B2274607
  · exact B2274611
  · exact B2274615
  · exact B2274619
  · exact B2274623
  · exact B2274627
  · exact B2274631
  · exact B2274635
  · exact B2274639
  · exact B2274643
  · exact B2274647
  · exact B2274651
  · exact B2274655
  · exact B2274659
  · exact B2274663
  · exact B2274667
  · exact B2274671
  · exact B2274675
  · exact B2274679
  · exact B2274683
  · exact B2274687
  · exact B2274691
  · exact B2274695
  · exact B2274699
  · exact B2274703
  · exact B2274707
  · exact B2274711
  · exact B2274715
  · exact B2274719
  · exact B2274723
  · exact B2274727
  · exact B2274731
  · exact B2274735
  · exact B2274739
  · exact B2274743
  · exact B2274747
  · exact B2274751
  · exact B2274755
  · exact B2274759
  · exact B2274763
  · exact B2274767
  · exact B2274771
  · exact B2274775
  · exact B2274779
  · exact B2274783
  · exact B2274787
  · exact B2274791
  · exact B2274795
  · exact B2274799
  · exact B2274803
  · exact B2274807
  · exact B2274811
  · exact B2274815
  · exact B2274819
  · exact B2274823
  · exact B2274827
  · exact B2274831
  · exact B2274835
  · exact B2274839
  · exact B2274843
  · exact B2274847
  · exact B2274851
  · exact B2274855
  · exact B2274859
  · exact B2274863
  · exact B2274867
  · exact B2274871
  · exact B2274875
  · exact B2274879
  · exact B2274883
  · exact B2274887
  · exact B2274891
  · exact B2274895
  · exact B2274899
  · exact B2274903
  · exact B2274907
  · exact B2274911
  · exact B2274915
  · exact B2274919
  · exact B2274923
  · exact B2274927
  · exact B2274931
  · exact B2274935
  · exact B2274939
  · exact B2274943
  · exact B2274947
  · exact B2274951
  · exact B2274955
  · exact B2274959
  · exact B2274963
  · exact B2274967
  · exact B2274971
  · exact B2274975
  · exact B2274979
  · exact B2274983
  · exact B2274987
  · exact B2274991
  · exact B2274995
  · exact B2274999
  · exact B2275003
  · exact B2275007
  · exact B2275011
  · exact B2275015
  · exact B2275019
  · exact B2275023
  · exact B2275027
  · exact B2275031
  · exact B2275035
  · exact B2275039
  · exact B2275043
  · exact B2275047
  · exact B2275051
  · exact B2275055
  · exact B2275059
  · exact B2275063
  · exact B2275067
  · exact B2275071
  · exact B2275075
  · exact B2275079
  · exact B2275083
  · exact B2275087
  · exact B2275091
  · exact B2275095
  · exact B2275099
  · exact B2275103
  · exact B2275107
  · exact B2275111
  · exact B2275115
  · exact B2275119
  · exact B2275123
  · exact B2275127
  · exact B2275131
  · exact B2275135
  · exact B2275139
  · exact B2275143
  · exact B2275147
  · exact B2275151
  · exact B2275155
  · exact B2275159
  · exact B2275163
  · exact B2275167
  · exact B2275171
  · exact B2275175
  · exact B2275179
  · exact B2275183
  · exact B2275187
  · exact B2275191
  · exact B2275195
  · exact B2275199
  · exact B2275203
  · exact B2275207
  · exact B2275211
  · exact B2275215
  · exact B2275219
  · exact B2275223
  · exact B2275227
  · exact B2275231
  · exact B2275235
  · exact B2275239
  · exact B2275243
  · exact B2275247
  · exact B2275251
  · exact B2275255
  · exact B2275259
  · exact B2275263
  · exact B2275267
  · exact B2275271
  · exact B2275275
  · exact B2275279
  · exact B2275283
  · exact B2275287
  · exact B2275291
  · exact B2275295
  · exact B2275299
  · exact B2275303
  · exact B2275307
  · exact B2275311
  · exact B2275315
  · exact B2275319
  · exact B2275323
  · exact B2275327
  · exact B2275331
  · exact B2275335
  · exact B2275339
  · exact B2275343
  · exact B2275347
  · exact B2275351
  · exact B2275355
  · exact B2275359
  · exact B2275363
  · exact B2275367
  · exact B2275371
  · exact B2275375
  · exact B2275379
  · exact B2275383
  · exact B2275387
  · exact B2275391
  · exact B2275395
  · exact B2275399
  · exact B2275403
  · exact B2275407
  · exact B2275411
  · exact B2275415
  · exact B2275419
  · exact B2275423
  · exact B2275427
  · exact B2275431
  · exact B2275435
theorem solution (m : ℕ) (hlo : 2273435 ≤ m) (hhi : m ≤ 2275435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 568358 ≤ j := by omega
    have hj2 : j ≤ 568858 := by omega
    have hb : Blo 2273435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
