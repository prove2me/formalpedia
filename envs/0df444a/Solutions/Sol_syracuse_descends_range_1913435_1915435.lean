-- Prove2me | solution 1 for syracuse_descends_range_1913435_1915435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:03.203906+00:00
-- url     : https://prove2.me/submissions/f1d4a02f-19cd-4de0-96a8-af9f0c768635

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

theorem B3879085 : Blo 1913435 3879085 := bbase (se 3 (by rfl) ⟨727328, by rfl⟩ : syracuseStep 3879085 = 1454657) (by norm_num)
theorem B5172113 : Blo 1913435 5172113 := bstep (se 2 (by rfl) ⟨1939542, by rfl⟩ : syracuseStep 5172113 = 3879085) B3879085
theorem B13792301 : Blo 1913435 13792301 := bstep (se 3 (by rfl) ⟨2586056, by rfl⟩ : syracuseStep 13792301 = 5172113) B5172113
theorem B9194867 : Blo 1913435 9194867 := bstep (se 1 (by rfl) ⟨6896150, by rfl⟩ : syracuseStep 9194867 = 13792301) B13792301
theorem B6129911 : Blo 1913435 6129911 := bstep (se 1 (by rfl) ⟨4597433, by rfl⟩ : syracuseStep 6129911 = 9194867) B9194867
theorem B4086607 : Blo 1913435 4086607 := bstep (se 1 (by rfl) ⟨3064955, by rfl⟩ : syracuseStep 4086607 = 6129911) B6129911
theorem B5448809 : Blo 1913435 5448809 := bstep (se 2 (by rfl) ⟨2043303, by rfl⟩ : syracuseStep 5448809 = 4086607) B4086607
theorem B3632539 : Blo 1913435 3632539 := bstep (se 1 (by rfl) ⟨2724404, by rfl⟩ : syracuseStep 3632539 = 5448809) B5448809
theorem B4843385 : Blo 1913435 4843385 := bstep (se 2 (by rfl) ⟨1816269, by rfl⟩ : syracuseStep 4843385 = 3632539) B3632539
theorem B3228923 : Blo 1913435 3228923 := bstep (se 1 (by rfl) ⟨2421692, by rfl⟩ : syracuseStep 3228923 = 4843385) B4843385
theorem B2152615 : Blo 1913435 2152615 := bstep (se 1 (by rfl) ⟨1614461, by rfl⟩ : syracuseStep 2152615 = 3228923) B3228923
theorem B2870153 : Blo 1913435 2870153 := bstep (se 2 (by rfl) ⟨1076307, by rfl⟩ : syracuseStep 2870153 = 2152615) B2152615
theorem B1913435 : Blo 1913435 1913435 := bstep (se 1 (by rfl) ⟨1435076, by rfl⟩ : syracuseStep 1913435 = 2870153) B2870153
theorem B9686789 : Blo 1913435 9686789 := bbase (se 4 (by rfl) ⟨908136, by rfl⟩ : syracuseStep 9686789 = 1816273) (by norm_num)
theorem B6457859 : Blo 1913435 6457859 := bstep (se 1 (by rfl) ⟨4843394, by rfl⟩ : syracuseStep 6457859 = 9686789) B9686789
theorem B4305239 : Blo 1913435 4305239 := bstep (se 1 (by rfl) ⟨3228929, by rfl⟩ : syracuseStep 4305239 = 6457859) B6457859
theorem B2870159 : Blo 1913435 2870159 := bstep (se 1 (by rfl) ⟨2152619, by rfl⟩ : syracuseStep 2870159 = 4305239) B4305239
theorem B1913439 : Blo 1913435 1913439 := bstep (se 1 (by rfl) ⟨1435079, by rfl⟩ : syracuseStep 1913439 = 2870159) B2870159
theorem B2870165 : Blo 1913435 2870165 := bbase (se 6 (by rfl) ⟨67269, by rfl⟩ : syracuseStep 2870165 = 134539) (by norm_num)
theorem B1913443 : Blo 1913435 1913443 := bstep (se 1 (by rfl) ⟨1435082, by rfl⟩ : syracuseStep 1913443 = 2870165) B2870165
theorem B10897685 : Blo 1913435 10897685 := bbase (se 6 (by rfl) ⟨255414, by rfl⟩ : syracuseStep 10897685 = 510829) (by norm_num)
theorem B7265123 : Blo 1913435 7265123 := bstep (se 1 (by rfl) ⟨5448842, by rfl⟩ : syracuseStep 7265123 = 10897685) B10897685
theorem B4843415 : Blo 1913435 4843415 := bstep (se 1 (by rfl) ⟨3632561, by rfl⟩ : syracuseStep 4843415 = 7265123) B7265123
theorem B3228943 : Blo 1913435 3228943 := bstep (se 1 (by rfl) ⟨2421707, by rfl⟩ : syracuseStep 3228943 = 4843415) B4843415
theorem B4305257 : Blo 1913435 4305257 := bstep (se 2 (by rfl) ⟨1614471, by rfl⟩ : syracuseStep 4305257 = 3228943) B3228943
theorem B2870171 : Blo 1913435 2870171 := bstep (se 1 (by rfl) ⟨2152628, by rfl⟩ : syracuseStep 2870171 = 4305257) B4305257
theorem B1913447 : Blo 1913435 1913447 := bstep (se 1 (by rfl) ⟨1435085, by rfl⟩ : syracuseStep 1913447 = 2870171) B2870171
theorem B2152633 : Blo 1913435 2152633 := bbase (se 2 (by rfl) ⟨807237, by rfl⟩ : syracuseStep 2152633 = 1614475) (by norm_num)
theorem B2870177 : Blo 1913435 2870177 := bstep (se 2 (by rfl) ⟨1076316, by rfl⟩ : syracuseStep 2870177 = 2152633) B2152633
theorem B1913451 : Blo 1913435 1913451 := bstep (se 1 (by rfl) ⟨1435088, by rfl⟩ : syracuseStep 1913451 = 2870177) B2870177
theorem B4198925 : Blo 1913435 4198925 := bbase (se 3 (by rfl) ⟨787298, by rfl⟩ : syracuseStep 4198925 = 1574597) (by norm_num)
theorem B11197133 : Blo 1913435 11197133 := bstep (se 3 (by rfl) ⟨2099462, by rfl⟩ : syracuseStep 11197133 = 4198925) B4198925
theorem B7464755 : Blo 1913435 7464755 := bstep (se 1 (by rfl) ⟨5598566, by rfl⟩ : syracuseStep 7464755 = 11197133) B11197133
theorem B19906013 : Blo 1913435 19906013 := bstep (se 3 (by rfl) ⟨3732377, by rfl⟩ : syracuseStep 19906013 = 7464755) B7464755
theorem B13270675 : Blo 1913435 13270675 := bstep (se 1 (by rfl) ⟨9953006, by rfl⟩ : syracuseStep 13270675 = 19906013) B19906013
theorem B17694233 : Blo 1913435 17694233 := bstep (se 2 (by rfl) ⟨6635337, by rfl⟩ : syracuseStep 17694233 = 13270675) B13270675
theorem B11796155 : Blo 1913435 11796155 := bstep (se 1 (by rfl) ⟨8847116, by rfl⟩ : syracuseStep 11796155 = 17694233) B17694233
theorem B7864103 : Blo 1913435 7864103 := bstep (se 1 (by rfl) ⟨5898077, by rfl⟩ : syracuseStep 7864103 = 11796155) B11796155
theorem B5242735 : Blo 1913435 5242735 := bstep (se 1 (by rfl) ⟨3932051, by rfl⟩ : syracuseStep 5242735 = 7864103) B7864103
theorem B6990313 : Blo 1913435 6990313 := bstep (se 2 (by rfl) ⟨2621367, by rfl⟩ : syracuseStep 6990313 = 5242735) B5242735
theorem B9320417 : Blo 1913435 9320417 := bstep (se 2 (by rfl) ⟨3495156, by rfl⟩ : syracuseStep 9320417 = 6990313) B6990313
theorem B6213611 : Blo 1913435 6213611 := bstep (se 1 (by rfl) ⟨4660208, by rfl⟩ : syracuseStep 6213611 = 9320417) B9320417
theorem B16569629 : Blo 1913435 16569629 := bstep (se 3 (by rfl) ⟨3106805, by rfl⟩ : syracuseStep 16569629 = 6213611) B6213611
theorem B11046419 : Blo 1913435 11046419 := bstep (se 1 (by rfl) ⟨8284814, by rfl⟩ : syracuseStep 11046419 = 16569629) B16569629
theorem B7364279 : Blo 1913435 7364279 := bstep (se 1 (by rfl) ⟨5523209, by rfl⟩ : syracuseStep 7364279 = 11046419) B11046419
theorem B4909519 : Blo 1913435 4909519 := bstep (se 1 (by rfl) ⟨3682139, by rfl⟩ : syracuseStep 4909519 = 7364279) B7364279
theorem B6546025 : Blo 1913435 6546025 := bstep (se 2 (by rfl) ⟨2454759, by rfl⟩ : syracuseStep 6546025 = 4909519) B4909519
theorem B8728033 : Blo 1913435 8728033 := bstep (se 2 (by rfl) ⟨3273012, by rfl⟩ : syracuseStep 8728033 = 6546025) B6546025
theorem B11637377 : Blo 1913435 11637377 := bstep (se 2 (by rfl) ⟨4364016, by rfl⟩ : syracuseStep 11637377 = 8728033) B8728033
theorem B7758251 : Blo 1913435 7758251 := bstep (se 1 (by rfl) ⟨5818688, by rfl⟩ : syracuseStep 7758251 = 11637377) B11637377
theorem B5172167 : Blo 1913435 5172167 := bstep (se 1 (by rfl) ⟨3879125, by rfl⟩ : syracuseStep 5172167 = 7758251) B7758251
theorem B3448111 : Blo 1913435 3448111 := bstep (se 1 (by rfl) ⟨2586083, by rfl⟩ : syracuseStep 3448111 = 5172167) B5172167
theorem B4597481 : Blo 1913435 4597481 := bstep (se 2 (by rfl) ⟨1724055, by rfl⟩ : syracuseStep 4597481 = 3448111) B3448111
theorem B3064987 : Blo 1913435 3064987 := bstep (se 1 (by rfl) ⟨2298740, by rfl⟩ : syracuseStep 3064987 = 4597481) B4597481
theorem B4086649 : Blo 1913435 4086649 := bstep (se 2 (by rfl) ⟨1532493, by rfl⟩ : syracuseStep 4086649 = 3064987) B3064987
theorem B5448865 : Blo 1913435 5448865 := bstep (se 2 (by rfl) ⟨2043324, by rfl⟩ : syracuseStep 5448865 = 4086649) B4086649
theorem B7265153 : Blo 1913435 7265153 := bstep (se 2 (by rfl) ⟨2724432, by rfl⟩ : syracuseStep 7265153 = 5448865) B5448865
theorem B4843435 : Blo 1913435 4843435 := bstep (se 1 (by rfl) ⟨3632576, by rfl⟩ : syracuseStep 4843435 = 7265153) B7265153
theorem B6457913 : Blo 1913435 6457913 := bstep (se 2 (by rfl) ⟨2421717, by rfl⟩ : syracuseStep 6457913 = 4843435) B4843435
theorem B4305275 : Blo 1913435 4305275 := bstep (se 1 (by rfl) ⟨3228956, by rfl⟩ : syracuseStep 4305275 = 6457913) B6457913
theorem B2870183 : Blo 1913435 2870183 := bstep (se 1 (by rfl) ⟨2152637, by rfl⟩ : syracuseStep 2870183 = 4305275) B4305275
theorem B1913455 : Blo 1913435 1913455 := bstep (se 1 (by rfl) ⟨1435091, by rfl⟩ : syracuseStep 1913455 = 2870183) B2870183
theorem B2870189 : Blo 1913435 2870189 := bbase (se 3 (by rfl) ⟨538160, by rfl⟩ : syracuseStep 2870189 = 1076321) (by norm_num)
theorem B1913459 : Blo 1913435 1913459 := bstep (se 1 (by rfl) ⟨1435094, by rfl⟩ : syracuseStep 1913459 = 2870189) B2870189
theorem B4305293 : Blo 1913435 4305293 := bbase (se 3 (by rfl) ⟨807242, by rfl⟩ : syracuseStep 4305293 = 1614485) (by norm_num)
theorem B2870195 : Blo 1913435 2870195 := bstep (se 1 (by rfl) ⟨2152646, by rfl⟩ : syracuseStep 2870195 = 4305293) B4305293
theorem B1913463 : Blo 1913435 1913463 := bstep (se 1 (by rfl) ⟨1435097, by rfl⟩ : syracuseStep 1913463 = 2870195) B2870195
theorem B2421733 : Blo 1913435 2421733 := bbase (se 4 (by rfl) ⟨227037, by rfl⟩ : syracuseStep 2421733 = 454075) (by norm_num)
theorem B3228977 : Blo 1913435 3228977 := bstep (se 2 (by rfl) ⟨1210866, by rfl⟩ : syracuseStep 3228977 = 2421733) B2421733
theorem B2152651 : Blo 1913435 2152651 := bstep (se 1 (by rfl) ⟨1614488, by rfl⟩ : syracuseStep 2152651 = 3228977) B3228977
theorem B2870201 : Blo 1913435 2870201 := bstep (se 2 (by rfl) ⟨1076325, by rfl⟩ : syracuseStep 2870201 = 2152651) B2152651
theorem B1913467 : Blo 1913435 1913467 := bstep (se 1 (by rfl) ⟨1435100, by rfl⟩ : syracuseStep 1913467 = 2870201) B2870201
theorem B10485557 : Blo 1913435 10485557 := bbase (se 5 (by rfl) ⟨491510, by rfl⟩ : syracuseStep 10485557 = 983021) (by norm_num)
theorem B6990371 : Blo 1913435 6990371 := bstep (se 1 (by rfl) ⟨5242778, by rfl⟩ : syracuseStep 6990371 = 10485557) B10485557
theorem B4660247 : Blo 1913435 4660247 := bstep (se 1 (by rfl) ⟨3495185, by rfl⟩ : syracuseStep 4660247 = 6990371) B6990371
theorem B3106831 : Blo 1913435 3106831 := bstep (se 1 (by rfl) ⟨2330123, by rfl⟩ : syracuseStep 3106831 = 4660247) B4660247
theorem B4142441 : Blo 1913435 4142441 := bstep (se 2 (by rfl) ⟨1553415, by rfl⟩ : syracuseStep 4142441 = 3106831) B3106831
theorem B2761627 : Blo 1913435 2761627 := bstep (se 1 (by rfl) ⟨2071220, by rfl⟩ : syracuseStep 2761627 = 4142441) B4142441
theorem B3682169 : Blo 1913435 3682169 := bstep (se 2 (by rfl) ⟨1380813, by rfl⟩ : syracuseStep 3682169 = 2761627) B2761627
theorem B2454779 : Blo 1913435 2454779 := bstep (se 1 (by rfl) ⟨1841084, by rfl⟩ : syracuseStep 2454779 = 3682169) B3682169
theorem B6546077 : Blo 1913435 6546077 := bstep (se 3 (by rfl) ⟨1227389, by rfl⟩ : syracuseStep 6546077 = 2454779) B2454779
theorem B4364051 : Blo 1913435 4364051 := bstep (se 1 (by rfl) ⟨3273038, by rfl⟩ : syracuseStep 4364051 = 6546077) B6546077
theorem B11637469 : Blo 1913435 11637469 := bstep (se 3 (by rfl) ⟨2182025, by rfl⟩ : syracuseStep 11637469 = 4364051) B4364051
theorem B15516625 : Blo 1913435 15516625 := bstep (se 2 (by rfl) ⟨5818734, by rfl⟩ : syracuseStep 15516625 = 11637469) B11637469
theorem B20688833 : Blo 1913435 20688833 := bstep (se 2 (by rfl) ⟨7758312, by rfl⟩ : syracuseStep 20688833 = 15516625) B15516625
theorem B13792555 : Blo 1913435 13792555 := bstep (se 1 (by rfl) ⟨10344416, by rfl⟩ : syracuseStep 13792555 = 20688833) B20688833
theorem B18390073 : Blo 1913435 18390073 := bstep (se 2 (by rfl) ⟨6896277, by rfl⟩ : syracuseStep 18390073 = 13792555) B13792555
theorem B24520097 : Blo 1913435 24520097 := bstep (se 2 (by rfl) ⟨9195036, by rfl⟩ : syracuseStep 24520097 = 18390073) B18390073
theorem B16346731 : Blo 1913435 16346731 := bstep (se 1 (by rfl) ⟨12260048, by rfl⟩ : syracuseStep 16346731 = 24520097) B24520097
theorem B21795641 : Blo 1913435 21795641 := bstep (se 2 (by rfl) ⟨8173365, by rfl⟩ : syracuseStep 21795641 = 16346731) B16346731
theorem B14530427 : Blo 1913435 14530427 := bstep (se 1 (by rfl) ⟨10897820, by rfl⟩ : syracuseStep 14530427 = 21795641) B21795641
theorem B9686951 : Blo 1913435 9686951 := bstep (se 1 (by rfl) ⟨7265213, by rfl⟩ : syracuseStep 9686951 = 14530427) B14530427
theorem B6457967 : Blo 1913435 6457967 := bstep (se 1 (by rfl) ⟨4843475, by rfl⟩ : syracuseStep 6457967 = 9686951) B9686951
theorem B4305311 : Blo 1913435 4305311 := bstep (se 1 (by rfl) ⟨3228983, by rfl⟩ : syracuseStep 4305311 = 6457967) B6457967
theorem B2870207 : Blo 1913435 2870207 := bstep (se 1 (by rfl) ⟨2152655, by rfl⟩ : syracuseStep 2870207 = 4305311) B4305311
theorem B1913471 : Blo 1913435 1913471 := bstep (se 1 (by rfl) ⟨1435103, by rfl⟩ : syracuseStep 1913471 = 2870207) B2870207
theorem B2870213 : Blo 1913435 2870213 := bbase (se 4 (by rfl) ⟨269082, by rfl⟩ : syracuseStep 2870213 = 538165) (by norm_num)
theorem B1913475 : Blo 1913435 1913475 := bstep (se 1 (by rfl) ⟨1435106, by rfl⟩ : syracuseStep 1913475 = 2870213) B2870213
theorem B3228997 : Blo 1913435 3228997 := bbase (se 4 (by rfl) ⟨302718, by rfl⟩ : syracuseStep 3228997 = 605437) (by norm_num)
theorem B4305329 : Blo 1913435 4305329 := bstep (se 2 (by rfl) ⟨1614498, by rfl⟩ : syracuseStep 4305329 = 3228997) B3228997
theorem B2870219 : Blo 1913435 2870219 := bstep (se 1 (by rfl) ⟨2152664, by rfl⟩ : syracuseStep 2870219 = 4305329) B4305329
theorem B1913479 : Blo 1913435 1913479 := bstep (se 1 (by rfl) ⟨1435109, by rfl⟩ : syracuseStep 1913479 = 2870219) B2870219
theorem B2152669 : Blo 1913435 2152669 := bbase (se 3 (by rfl) ⟨403625, by rfl⟩ : syracuseStep 2152669 = 807251) (by norm_num)
theorem B2870225 : Blo 1913435 2870225 := bstep (se 2 (by rfl) ⟨1076334, by rfl⟩ : syracuseStep 2870225 = 2152669) B2152669
theorem B1913483 : Blo 1913435 1913483 := bstep (se 1 (by rfl) ⟨1435112, by rfl⟩ : syracuseStep 1913483 = 2870225) B2870225
theorem B6458021 : Blo 1913435 6458021 := bbase (se 4 (by rfl) ⟨605439, by rfl⟩ : syracuseStep 6458021 = 1210879) (by norm_num)
theorem B4305347 : Blo 1913435 4305347 := bstep (se 1 (by rfl) ⟨3229010, by rfl⟩ : syracuseStep 4305347 = 6458021) B6458021
theorem B2870231 : Blo 1913435 2870231 := bstep (se 1 (by rfl) ⟨2152673, by rfl⟩ : syracuseStep 2870231 = 4305347) B4305347
theorem B1913487 : Blo 1913435 1913487 := bstep (se 1 (by rfl) ⟨1435115, by rfl⟩ : syracuseStep 1913487 = 2870231) B2870231
theorem B2870237 : Blo 1913435 2870237 := bbase (se 3 (by rfl) ⟨538169, by rfl⟩ : syracuseStep 2870237 = 1076339) (by norm_num)
theorem B1913491 : Blo 1913435 1913491 := bstep (se 1 (by rfl) ⟨1435118, by rfl⟩ : syracuseStep 1913491 = 2870237) B2870237
theorem B4305365 : Blo 1913435 4305365 := bbase (se 7 (by rfl) ⟨50453, by rfl⟩ : syracuseStep 4305365 = 100907) (by norm_num)
theorem B2870243 : Blo 1913435 2870243 := bstep (se 1 (by rfl) ⟨2152682, by rfl⟩ : syracuseStep 2870243 = 4305365) B4305365
theorem B1913495 : Blo 1913435 1913495 := bstep (se 1 (by rfl) ⟨1435121, by rfl⟩ : syracuseStep 1913495 = 2870243) B2870243
theorem B4364117 : Blo 1913435 4364117 := bbase (se 9 (by rfl) ⟨12785, by rfl⟩ : syracuseStep 4364117 = 25571) (by norm_num)
theorem B2909411 : Blo 1913435 2909411 := bstep (se 1 (by rfl) ⟨2182058, by rfl⟩ : syracuseStep 2909411 = 4364117) B4364117
theorem B1939607 : Blo 1913435 1939607 := bstep (se 1 (by rfl) ⟨1454705, by rfl⟩ : syracuseStep 1939607 = 2909411) B2909411
theorem B20689141 : Blo 1913435 20689141 := bstep (se 5 (by rfl) ⟨969803, by rfl⟩ : syracuseStep 20689141 = 1939607) B1939607
theorem B27585521 : Blo 1913435 27585521 := bstep (se 2 (by rfl) ⟨10344570, by rfl⟩ : syracuseStep 27585521 = 20689141) B20689141
theorem B18390347 : Blo 1913435 18390347 := bstep (se 1 (by rfl) ⟨13792760, by rfl⟩ : syracuseStep 18390347 = 27585521) B27585521
theorem B12260231 : Blo 1913435 12260231 := bstep (se 1 (by rfl) ⟨9195173, by rfl⟩ : syracuseStep 12260231 = 18390347) B18390347
theorem B8173487 : Blo 1913435 8173487 := bstep (se 1 (by rfl) ⟨6130115, by rfl⟩ : syracuseStep 8173487 = 12260231) B12260231
theorem B5448991 : Blo 1913435 5448991 := bstep (se 1 (by rfl) ⟨4086743, by rfl⟩ : syracuseStep 5448991 = 8173487) B8173487
theorem B7265321 : Blo 1913435 7265321 := bstep (se 2 (by rfl) ⟨2724495, by rfl⟩ : syracuseStep 7265321 = 5448991) B5448991
theorem B4843547 : Blo 1913435 4843547 := bstep (se 1 (by rfl) ⟨3632660, by rfl⟩ : syracuseStep 4843547 = 7265321) B7265321
theorem B3229031 : Blo 1913435 3229031 := bstep (se 1 (by rfl) ⟨2421773, by rfl⟩ : syracuseStep 3229031 = 4843547) B4843547
theorem B2152687 : Blo 1913435 2152687 := bstep (se 1 (by rfl) ⟨1614515, by rfl⟩ : syracuseStep 2152687 = 3229031) B3229031
theorem B2870249 : Blo 1913435 2870249 := bstep (se 2 (by rfl) ⟨1076343, by rfl⟩ : syracuseStep 2870249 = 2152687) B2152687
theorem B1913499 : Blo 1913435 1913499 := bstep (se 1 (by rfl) ⟨1435124, by rfl⟩ : syracuseStep 1913499 = 2870249) B2870249
theorem B4660325 : Blo 1913435 4660325 := bbase (se 4 (by rfl) ⟨436905, by rfl⟩ : syracuseStep 4660325 = 873811) (by norm_num)
theorem B3106883 : Blo 1913435 3106883 := bstep (se 1 (by rfl) ⟨2330162, by rfl⟩ : syracuseStep 3106883 = 4660325) B4660325
theorem B2071255 : Blo 1913435 2071255 := bstep (se 1 (by rfl) ⟨1553441, by rfl⟩ : syracuseStep 2071255 = 3106883) B3106883
theorem B2761673 : Blo 1913435 2761673 := bstep (se 2 (by rfl) ⟨1035627, by rfl⟩ : syracuseStep 2761673 = 2071255) B2071255
theorem B7364461 : Blo 1913435 7364461 := bstep (se 3 (by rfl) ⟨1380836, by rfl⟩ : syracuseStep 7364461 = 2761673) B2761673
theorem B9819281 : Blo 1913435 9819281 := bstep (se 2 (by rfl) ⟨3682230, by rfl⟩ : syracuseStep 9819281 = 7364461) B7364461
theorem B6546187 : Blo 1913435 6546187 := bstep (se 1 (by rfl) ⟨4909640, by rfl⟩ : syracuseStep 6546187 = 9819281) B9819281
theorem B8728249 : Blo 1913435 8728249 := bstep (se 2 (by rfl) ⟨3273093, by rfl⟩ : syracuseStep 8728249 = 6546187) B6546187
theorem B11637665 : Blo 1913435 11637665 := bstep (se 2 (by rfl) ⟨4364124, by rfl⟩ : syracuseStep 11637665 = 8728249) B8728249
theorem B7758443 : Blo 1913435 7758443 := bstep (se 1 (by rfl) ⟨5818832, by rfl⟩ : syracuseStep 7758443 = 11637665) B11637665
theorem B20689181 : Blo 1913435 20689181 := bstep (se 3 (by rfl) ⟨3879221, by rfl⟩ : syracuseStep 20689181 = 7758443) B7758443
theorem B13792787 : Blo 1913435 13792787 := bstep (se 1 (by rfl) ⟨10344590, by rfl⟩ : syracuseStep 13792787 = 20689181) B20689181
theorem B9195191 : Blo 1913435 9195191 := bstep (se 1 (by rfl) ⟨6896393, by rfl⟩ : syracuseStep 9195191 = 13792787) B13792787
theorem B6130127 : Blo 1913435 6130127 := bstep (se 1 (by rfl) ⟨4597595, by rfl⟩ : syracuseStep 6130127 = 9195191) B9195191
theorem B16347005 : Blo 1913435 16347005 := bstep (se 3 (by rfl) ⟨3065063, by rfl⟩ : syracuseStep 16347005 = 6130127) B6130127
theorem B10898003 : Blo 1913435 10898003 := bstep (se 1 (by rfl) ⟨8173502, by rfl⟩ : syracuseStep 10898003 = 16347005) B16347005
theorem B7265335 : Blo 1913435 7265335 := bstep (se 1 (by rfl) ⟨5449001, by rfl⟩ : syracuseStep 7265335 = 10898003) B10898003
theorem B9687113 : Blo 1913435 9687113 := bstep (se 2 (by rfl) ⟨3632667, by rfl⟩ : syracuseStep 9687113 = 7265335) B7265335
theorem B6458075 : Blo 1913435 6458075 := bstep (se 1 (by rfl) ⟨4843556, by rfl⟩ : syracuseStep 6458075 = 9687113) B9687113
theorem B4305383 : Blo 1913435 4305383 := bstep (se 1 (by rfl) ⟨3229037, by rfl⟩ : syracuseStep 4305383 = 6458075) B6458075
theorem B2870255 : Blo 1913435 2870255 := bstep (se 1 (by rfl) ⟨2152691, by rfl⟩ : syracuseStep 2870255 = 4305383) B4305383
theorem B1913503 : Blo 1913435 1913503 := bstep (se 1 (by rfl) ⟨1435127, by rfl⟩ : syracuseStep 1913503 = 2870255) B2870255
theorem B2870261 : Blo 1913435 2870261 := bbase (se 5 (by rfl) ⟨134543, by rfl⟩ : syracuseStep 2870261 = 269087) (by norm_num)
theorem B1913507 : Blo 1913435 1913507 := bstep (se 1 (by rfl) ⟨1435130, by rfl⟩ : syracuseStep 1913507 = 2870261) B2870261
theorem B3065077 : Blo 1913435 3065077 := bbase (se 5 (by rfl) ⟨143675, by rfl⟩ : syracuseStep 3065077 = 287351) (by norm_num)
theorem B4086769 : Blo 1913435 4086769 := bstep (se 2 (by rfl) ⟨1532538, by rfl⟩ : syracuseStep 4086769 = 3065077) B3065077
theorem B5449025 : Blo 1913435 5449025 := bstep (se 2 (by rfl) ⟨2043384, by rfl⟩ : syracuseStep 5449025 = 4086769) B4086769
theorem B3632683 : Blo 1913435 3632683 := bstep (se 1 (by rfl) ⟨2724512, by rfl⟩ : syracuseStep 3632683 = 5449025) B5449025
theorem B4843577 : Blo 1913435 4843577 := bstep (se 2 (by rfl) ⟨1816341, by rfl⟩ : syracuseStep 4843577 = 3632683) B3632683
theorem B3229051 : Blo 1913435 3229051 := bstep (se 1 (by rfl) ⟨2421788, by rfl⟩ : syracuseStep 3229051 = 4843577) B4843577
theorem B4305401 : Blo 1913435 4305401 := bstep (se 2 (by rfl) ⟨1614525, by rfl⟩ : syracuseStep 4305401 = 3229051) B3229051
theorem B2870267 : Blo 1913435 2870267 := bstep (se 1 (by rfl) ⟨2152700, by rfl⟩ : syracuseStep 2870267 = 4305401) B4305401
theorem B1913511 : Blo 1913435 1913511 := bstep (se 1 (by rfl) ⟨1435133, by rfl⟩ : syracuseStep 1913511 = 2870267) B2870267
theorem B2152705 : Blo 1913435 2152705 := bbase (se 2 (by rfl) ⟨807264, by rfl⟩ : syracuseStep 2152705 = 1614529) (by norm_num)
theorem B2870273 : Blo 1913435 2870273 := bstep (se 2 (by rfl) ⟨1076352, by rfl⟩ : syracuseStep 2870273 = 2152705) B2152705
theorem B1913515 : Blo 1913435 1913515 := bstep (se 1 (by rfl) ⟨1435136, by rfl⟩ : syracuseStep 1913515 = 2870273) B2870273
theorem B4843597 : Blo 1913435 4843597 := bbase (se 3 (by rfl) ⟨908174, by rfl⟩ : syracuseStep 4843597 = 1816349) (by norm_num)
theorem B6458129 : Blo 1913435 6458129 := bstep (se 2 (by rfl) ⟨2421798, by rfl⟩ : syracuseStep 6458129 = 4843597) B4843597
theorem B4305419 : Blo 1913435 4305419 := bstep (se 1 (by rfl) ⟨3229064, by rfl⟩ : syracuseStep 4305419 = 6458129) B6458129
theorem B2870279 : Blo 1913435 2870279 := bstep (se 1 (by rfl) ⟨2152709, by rfl⟩ : syracuseStep 2870279 = 4305419) B4305419
theorem B1913519 : Blo 1913435 1913519 := bstep (se 1 (by rfl) ⟨1435139, by rfl⟩ : syracuseStep 1913519 = 2870279) B2870279
theorem B2870285 : Blo 1913435 2870285 := bbase (se 3 (by rfl) ⟨538178, by rfl⟩ : syracuseStep 2870285 = 1076357) (by norm_num)
theorem B1913523 : Blo 1913435 1913523 := bstep (se 1 (by rfl) ⟨1435142, by rfl⟩ : syracuseStep 1913523 = 2870285) B2870285
theorem B4305437 : Blo 1913435 4305437 := bbase (se 3 (by rfl) ⟨807269, by rfl⟩ : syracuseStep 4305437 = 1614539) (by norm_num)
theorem B2870291 : Blo 1913435 2870291 := bstep (se 1 (by rfl) ⟨2152718, by rfl⟩ : syracuseStep 2870291 = 4305437) B4305437
theorem B1913527 : Blo 1913435 1913527 := bstep (se 1 (by rfl) ⟨1435145, by rfl⟩ : syracuseStep 1913527 = 2870291) B2870291
theorem B3229085 : Blo 1913435 3229085 := bbase (se 3 (by rfl) ⟨605453, by rfl⟩ : syracuseStep 3229085 = 1210907) (by norm_num)
theorem B2152723 : Blo 1913435 2152723 := bstep (se 1 (by rfl) ⟨1614542, by rfl⟩ : syracuseStep 2152723 = 3229085) B3229085
theorem B2870297 : Blo 1913435 2870297 := bstep (se 2 (by rfl) ⟨1076361, by rfl⟩ : syracuseStep 2870297 = 2152723) B2152723
theorem B1913531 : Blo 1913435 1913531 := bstep (se 1 (by rfl) ⟨1435148, by rfl⟩ : syracuseStep 1913531 = 2870297) B2870297
theorem B17456789 : Blo 1913435 17456789 := bbase (se 6 (by rfl) ⟨409143, by rfl⟩ : syracuseStep 17456789 = 818287) (by norm_num)
theorem B11637859 : Blo 1913435 11637859 := bstep (se 1 (by rfl) ⟨8728394, by rfl⟩ : syracuseStep 11637859 = 17456789) B17456789
theorem B15517145 : Blo 1913435 15517145 := bstep (se 2 (by rfl) ⟨5818929, by rfl⟩ : syracuseStep 15517145 = 11637859) B11637859
theorem B10344763 : Blo 1913435 10344763 := bstep (se 1 (by rfl) ⟨7758572, by rfl⟩ : syracuseStep 10344763 = 15517145) B15517145
theorem B13793017 : Blo 1913435 13793017 := bstep (se 2 (by rfl) ⟨5172381, by rfl⟩ : syracuseStep 13793017 = 10344763) B10344763
theorem B18390689 : Blo 1913435 18390689 := bstep (se 2 (by rfl) ⟨6896508, by rfl⟩ : syracuseStep 18390689 = 13793017) B13793017
theorem B12260459 : Blo 1913435 12260459 := bstep (se 1 (by rfl) ⟨9195344, by rfl⟩ : syracuseStep 12260459 = 18390689) B18390689
theorem B8173639 : Blo 1913435 8173639 := bstep (se 1 (by rfl) ⟨6130229, by rfl⟩ : syracuseStep 8173639 = 12260459) B12260459
theorem B10898185 : Blo 1913435 10898185 := bstep (se 2 (by rfl) ⟨4086819, by rfl⟩ : syracuseStep 10898185 = 8173639) B8173639
theorem B14530913 : Blo 1913435 14530913 := bstep (se 2 (by rfl) ⟨5449092, by rfl⟩ : syracuseStep 14530913 = 10898185) B10898185
theorem B9687275 : Blo 1913435 9687275 := bstep (se 1 (by rfl) ⟨7265456, by rfl⟩ : syracuseStep 9687275 = 14530913) B14530913
theorem B6458183 : Blo 1913435 6458183 := bstep (se 1 (by rfl) ⟨4843637, by rfl⟩ : syracuseStep 6458183 = 9687275) B9687275
theorem B4305455 : Blo 1913435 4305455 := bstep (se 1 (by rfl) ⟨3229091, by rfl⟩ : syracuseStep 4305455 = 6458183) B6458183
theorem B2870303 : Blo 1913435 2870303 := bstep (se 1 (by rfl) ⟨2152727, by rfl⟩ : syracuseStep 2870303 = 4305455) B4305455
theorem B1913535 : Blo 1913435 1913535 := bstep (se 1 (by rfl) ⟨1435151, by rfl⟩ : syracuseStep 1913535 = 2870303) B2870303
theorem B2870309 : Blo 1913435 2870309 := bbase (se 4 (by rfl) ⟨269091, by rfl⟩ : syracuseStep 2870309 = 538183) (by norm_num)
theorem B1913539 : Blo 1913435 1913539 := bstep (se 1 (by rfl) ⟨1435154, by rfl⟩ : syracuseStep 1913539 = 2870309) B2870309
theorem B2421829 : Blo 1913435 2421829 := bbase (se 4 (by rfl) ⟨227046, by rfl⟩ : syracuseStep 2421829 = 454093) (by norm_num)
theorem B3229105 : Blo 1913435 3229105 := bstep (se 2 (by rfl) ⟨1210914, by rfl⟩ : syracuseStep 3229105 = 2421829) B2421829
theorem B4305473 : Blo 1913435 4305473 := bstep (se 2 (by rfl) ⟨1614552, by rfl⟩ : syracuseStep 4305473 = 3229105) B3229105
theorem B2870315 : Blo 1913435 2870315 := bstep (se 1 (by rfl) ⟨2152736, by rfl⟩ : syracuseStep 2870315 = 4305473) B4305473
theorem B1913543 : Blo 1913435 1913543 := bstep (se 1 (by rfl) ⟨1435157, by rfl⟩ : syracuseStep 1913543 = 2870315) B2870315
theorem B2152741 : Blo 1913435 2152741 := bbase (se 4 (by rfl) ⟨201819, by rfl⟩ : syracuseStep 2152741 = 403639) (by norm_num)
theorem B2870321 : Blo 1913435 2870321 := bstep (se 2 (by rfl) ⟨1076370, by rfl⟩ : syracuseStep 2870321 = 2152741) B2152741
theorem B1913547 : Blo 1913435 1913547 := bstep (se 1 (by rfl) ⟨1435160, by rfl⟩ : syracuseStep 1913547 = 2870321) B2870321
theorem B3065141 : Blo 1913435 3065141 := bbase (se 5 (by rfl) ⟨143678, by rfl⟩ : syracuseStep 3065141 = 287357) (by norm_num)
theorem B8173709 : Blo 1913435 8173709 := bstep (se 3 (by rfl) ⟨1532570, by rfl⟩ : syracuseStep 8173709 = 3065141) B3065141
theorem B5449139 : Blo 1913435 5449139 := bstep (se 1 (by rfl) ⟨4086854, by rfl⟩ : syracuseStep 5449139 = 8173709) B8173709
theorem B3632759 : Blo 1913435 3632759 := bstep (se 1 (by rfl) ⟨2724569, by rfl⟩ : syracuseStep 3632759 = 5449139) B5449139
theorem B2421839 : Blo 1913435 2421839 := bstep (se 1 (by rfl) ⟨1816379, by rfl⟩ : syracuseStep 2421839 = 3632759) B3632759
theorem B6458237 : Blo 1913435 6458237 := bstep (se 3 (by rfl) ⟨1210919, by rfl⟩ : syracuseStep 6458237 = 2421839) B2421839
theorem B4305491 : Blo 1913435 4305491 := bstep (se 1 (by rfl) ⟨3229118, by rfl⟩ : syracuseStep 4305491 = 6458237) B6458237
theorem B2870327 : Blo 1913435 2870327 := bstep (se 1 (by rfl) ⟨2152745, by rfl⟩ : syracuseStep 2870327 = 4305491) B4305491
theorem B1913551 : Blo 1913435 1913551 := bstep (se 1 (by rfl) ⟨1435163, by rfl⟩ : syracuseStep 1913551 = 2870327) B2870327
theorem B2870333 : Blo 1913435 2870333 := bbase (se 3 (by rfl) ⟨538187, by rfl⟩ : syracuseStep 2870333 = 1076375) (by norm_num)
theorem B1913555 : Blo 1913435 1913555 := bstep (se 1 (by rfl) ⟨1435166, by rfl⟩ : syracuseStep 1913555 = 2870333) B2870333
theorem B4305509 : Blo 1913435 4305509 := bbase (se 4 (by rfl) ⟨403641, by rfl⟩ : syracuseStep 4305509 = 807283) (by norm_num)
theorem B2870339 : Blo 1913435 2870339 := bstep (se 1 (by rfl) ⟨2152754, by rfl⟩ : syracuseStep 2870339 = 4305509) B4305509
theorem B1913559 : Blo 1913435 1913559 := bstep (se 1 (by rfl) ⟨1435169, by rfl⟩ : syracuseStep 1913559 = 2870339) B2870339
theorem B4843709 : Blo 1913435 4843709 := bbase (se 3 (by rfl) ⟨908195, by rfl⟩ : syracuseStep 4843709 = 1816391) (by norm_num)
theorem B3229139 : Blo 1913435 3229139 := bstep (se 1 (by rfl) ⟨2421854, by rfl⟩ : syracuseStep 3229139 = 4843709) B4843709
theorem B2152759 : Blo 1913435 2152759 := bstep (se 1 (by rfl) ⟨1614569, by rfl⟩ : syracuseStep 2152759 = 3229139) B3229139
theorem B2870345 : Blo 1913435 2870345 := bstep (se 2 (by rfl) ⟨1076379, by rfl⟩ : syracuseStep 2870345 = 2152759) B2152759
theorem B1913563 : Blo 1913435 1913563 := bstep (se 1 (by rfl) ⟨1435172, by rfl⟩ : syracuseStep 1913563 = 2870345) B2870345
theorem B3632789 : Blo 1913435 3632789 := bbase (se 6 (by rfl) ⟨85143, by rfl⟩ : syracuseStep 3632789 = 170287) (by norm_num)
theorem B9687437 : Blo 1913435 9687437 := bstep (se 3 (by rfl) ⟨1816394, by rfl⟩ : syracuseStep 9687437 = 3632789) B3632789
theorem B6458291 : Blo 1913435 6458291 := bstep (se 1 (by rfl) ⟨4843718, by rfl⟩ : syracuseStep 6458291 = 9687437) B9687437
theorem B4305527 : Blo 1913435 4305527 := bstep (se 1 (by rfl) ⟨3229145, by rfl⟩ : syracuseStep 4305527 = 6458291) B6458291
theorem B2870351 : Blo 1913435 2870351 := bstep (se 1 (by rfl) ⟨2152763, by rfl⟩ : syracuseStep 2870351 = 4305527) B4305527
theorem B1913567 : Blo 1913435 1913567 := bstep (se 1 (by rfl) ⟨1435175, by rfl⟩ : syracuseStep 1913567 = 2870351) B2870351
theorem B2870357 : Blo 1913435 2870357 := bbase (se 8 (by rfl) ⟨16818, by rfl⟩ : syracuseStep 2870357 = 33637) (by norm_num)
theorem B1913571 : Blo 1913435 1913571 := bstep (se 1 (by rfl) ⟨1435178, by rfl⟩ : syracuseStep 1913571 = 2870357) B2870357
theorem B2182145 : Blo 1913435 2182145 := bbase (se 2 (by rfl) ⟨818304, by rfl⟩ : syracuseStep 2182145 = 1636609) (by norm_num)
theorem B5819053 : Blo 1913435 5819053 := bstep (se 3 (by rfl) ⟨1091072, by rfl⟩ : syracuseStep 5819053 = 2182145) B2182145
theorem B7758737 : Blo 1913435 7758737 := bstep (se 2 (by rfl) ⟨2909526, by rfl⟩ : syracuseStep 7758737 = 5819053) B5819053
theorem B5172491 : Blo 1913435 5172491 := bstep (se 1 (by rfl) ⟨3879368, by rfl⟩ : syracuseStep 5172491 = 7758737) B7758737
theorem B3448327 : Blo 1913435 3448327 := bstep (se 1 (by rfl) ⟨2586245, by rfl⟩ : syracuseStep 3448327 = 5172491) B5172491
theorem B4597769 : Blo 1913435 4597769 := bstep (se 2 (by rfl) ⟨1724163, by rfl⟩ : syracuseStep 4597769 = 3448327) B3448327
theorem B12260717 : Blo 1913435 12260717 := bstep (se 3 (by rfl) ⟨2298884, by rfl⟩ : syracuseStep 12260717 = 4597769) B4597769
theorem B8173811 : Blo 1913435 8173811 := bstep (se 1 (by rfl) ⟨6130358, by rfl⟩ : syracuseStep 8173811 = 12260717) B12260717
theorem B5449207 : Blo 1913435 5449207 := bstep (se 1 (by rfl) ⟨4086905, by rfl⟩ : syracuseStep 5449207 = 8173811) B8173811
theorem B7265609 : Blo 1913435 7265609 := bstep (se 2 (by rfl) ⟨2724603, by rfl⟩ : syracuseStep 7265609 = 5449207) B5449207
theorem B4843739 : Blo 1913435 4843739 := bstep (se 1 (by rfl) ⟨3632804, by rfl⟩ : syracuseStep 4843739 = 7265609) B7265609
theorem B3229159 : Blo 1913435 3229159 := bstep (se 1 (by rfl) ⟨2421869, by rfl⟩ : syracuseStep 3229159 = 4843739) B4843739
theorem B4305545 : Blo 1913435 4305545 := bstep (se 2 (by rfl) ⟨1614579, by rfl⟩ : syracuseStep 4305545 = 3229159) B3229159
theorem B2870363 : Blo 1913435 2870363 := bstep (se 1 (by rfl) ⟨2152772, by rfl⟩ : syracuseStep 2870363 = 4305545) B4305545
theorem B1913575 : Blo 1913435 1913575 := bstep (se 1 (by rfl) ⟨1435181, by rfl⟩ : syracuseStep 1913575 = 2870363) B2870363
theorem B2152777 : Blo 1913435 2152777 := bbase (se 2 (by rfl) ⟨807291, by rfl⟩ : syracuseStep 2152777 = 1614583) (by norm_num)
theorem B2870369 : Blo 1913435 2870369 := bstep (se 2 (by rfl) ⟨1076388, by rfl⟩ : syracuseStep 2870369 = 2152777) B2152777
theorem B1913579 : Blo 1913435 1913579 := bstep (se 1 (by rfl) ⟨1435184, by rfl⟩ : syracuseStep 1913579 = 2870369) B2870369
theorem B4545389 : Blo 1913435 4545389 := bbase (se 3 (by rfl) ⟨852260, by rfl⟩ : syracuseStep 4545389 = 1704521) (by norm_num)
theorem B3030259 : Blo 1913435 3030259 := bstep (se 1 (by rfl) ⟨2272694, by rfl⟩ : syracuseStep 3030259 = 4545389) B4545389
theorem B4040345 : Blo 1913435 4040345 := bstep (se 2 (by rfl) ⟨1515129, by rfl⟩ : syracuseStep 4040345 = 3030259) B3030259
theorem B2693563 : Blo 1913435 2693563 := bstep (se 1 (by rfl) ⟨2020172, by rfl⟩ : syracuseStep 2693563 = 4040345) B4040345
theorem B14365669 : Blo 1913435 14365669 := bstep (se 4 (by rfl) ⟨1346781, by rfl⟩ : syracuseStep 14365669 = 2693563) B2693563
theorem B19154225 : Blo 1913435 19154225 := bstep (se 2 (by rfl) ⟨7182834, by rfl⟩ : syracuseStep 19154225 = 14365669) B14365669
theorem B12769483 : Blo 1913435 12769483 := bstep (se 1 (by rfl) ⟨9577112, by rfl⟩ : syracuseStep 12769483 = 19154225) B19154225
theorem B17025977 : Blo 1913435 17025977 := bstep (se 2 (by rfl) ⟨6384741, by rfl⟩ : syracuseStep 17025977 = 12769483) B12769483
theorem B11350651 : Blo 1913435 11350651 := bstep (se 1 (by rfl) ⟨8512988, by rfl⟩ : syracuseStep 11350651 = 17025977) B17025977
theorem B15134201 : Blo 1913435 15134201 := bstep (se 2 (by rfl) ⟨5675325, by rfl⟩ : syracuseStep 15134201 = 11350651) B11350651
theorem B10089467 : Blo 1913435 10089467 := bstep (se 1 (by rfl) ⟨7567100, by rfl⟩ : syracuseStep 10089467 = 15134201) B15134201
theorem B6726311 : Blo 1913435 6726311 := bstep (se 1 (by rfl) ⟨5044733, by rfl⟩ : syracuseStep 6726311 = 10089467) B10089467
theorem B4484207 : Blo 1913435 4484207 := bstep (se 1 (by rfl) ⟨3363155, by rfl⟩ : syracuseStep 4484207 = 6726311) B6726311
theorem B11957885 : Blo 1913435 11957885 := bstep (se 3 (by rfl) ⟨2242103, by rfl⟩ : syracuseStep 11957885 = 4484207) B4484207
theorem B7971923 : Blo 1913435 7971923 := bstep (se 1 (by rfl) ⟨5978942, by rfl⟩ : syracuseStep 7971923 = 11957885) B11957885
theorem B5314615 : Blo 1913435 5314615 := bstep (se 1 (by rfl) ⟨3985961, by rfl⟩ : syracuseStep 5314615 = 7971923) B7971923
theorem B113378453 : Blo 1913435 113378453 := bstep (se 6 (by rfl) ⟨2657307, by rfl⟩ : syracuseStep 113378453 = 5314615) B5314615
theorem B75585635 : Blo 1913435 75585635 := bstep (se 1 (by rfl) ⟨56689226, by rfl⟩ : syracuseStep 75585635 = 113378453) B113378453
theorem B50390423 : Blo 1913435 50390423 := bstep (se 1 (by rfl) ⟨37792817, by rfl⟩ : syracuseStep 50390423 = 75585635) B75585635
theorem B33593615 : Blo 1913435 33593615 := bstep (se 1 (by rfl) ⟨25195211, by rfl⟩ : syracuseStep 33593615 = 50390423) B50390423
theorem B22395743 : Blo 1913435 22395743 := bstep (se 1 (by rfl) ⟨16796807, by rfl⟩ : syracuseStep 22395743 = 33593615) B33593615
theorem B14930495 : Blo 1913435 14930495 := bstep (se 1 (by rfl) ⟨11197871, by rfl⟩ : syracuseStep 14930495 = 22395743) B22395743
theorem B9953663 : Blo 1913435 9953663 := bstep (se 1 (by rfl) ⟨7465247, by rfl⟩ : syracuseStep 9953663 = 14930495) B14930495
theorem B26543101 : Blo 1913435 26543101 := bstep (se 3 (by rfl) ⟨4976831, by rfl⟩ : syracuseStep 26543101 = 9953663) B9953663
theorem B35390801 : Blo 1913435 35390801 := bstep (se 2 (by rfl) ⟨13271550, by rfl⟩ : syracuseStep 35390801 = 26543101) B26543101
theorem B94375469 : Blo 1913435 94375469 := bstep (se 3 (by rfl) ⟨17695400, by rfl⟩ : syracuseStep 94375469 = 35390801) B35390801
theorem B251667917 : Blo 1913435 251667917 := bstep (se 3 (by rfl) ⟨47187734, by rfl⟩ : syracuseStep 251667917 = 94375469) B94375469
theorem B167778611 : Blo 1913435 167778611 := bstep (se 1 (by rfl) ⟨125833958, by rfl⟩ : syracuseStep 167778611 = 251667917) B251667917
theorem B111852407 : Blo 1913435 111852407 := bstep (se 1 (by rfl) ⟨83889305, by rfl⟩ : syracuseStep 111852407 = 167778611) B167778611
theorem B74568271 : Blo 1913435 74568271 := bstep (se 1 (by rfl) ⟨55926203, by rfl⟩ : syracuseStep 74568271 = 111852407) B111852407
theorem B99424361 : Blo 1913435 99424361 := bstep (se 2 (by rfl) ⟨37284135, by rfl⟩ : syracuseStep 99424361 = 74568271) B74568271
theorem B265131629 : Blo 1913435 265131629 := bstep (se 3 (by rfl) ⟨49712180, by rfl⟩ : syracuseStep 265131629 = 99424361) B99424361
theorem B176754419 : Blo 1913435 176754419 := bstep (se 1 (by rfl) ⟨132565814, by rfl⟩ : syracuseStep 176754419 = 265131629) B265131629
theorem B117836279 : Blo 1913435 117836279 := bstep (se 1 (by rfl) ⟨88377209, by rfl⟩ : syracuseStep 117836279 = 176754419) B176754419
theorem B78557519 : Blo 1913435 78557519 := bstep (se 1 (by rfl) ⟨58918139, by rfl⟩ : syracuseStep 78557519 = 117836279) B117836279
theorem B52371679 : Blo 1913435 52371679 := bstep (se 1 (by rfl) ⟨39278759, by rfl⟩ : syracuseStep 52371679 = 78557519) B78557519
theorem B69828905 : Blo 1913435 69828905 := bstep (se 2 (by rfl) ⟨26185839, by rfl⟩ : syracuseStep 69828905 = 52371679) B52371679
theorem B46552603 : Blo 1913435 46552603 := bstep (se 1 (by rfl) ⟨34914452, by rfl⟩ : syracuseStep 46552603 = 69828905) B69828905
theorem B62070137 : Blo 1913435 62070137 := bstep (se 2 (by rfl) ⟨23276301, by rfl⟩ : syracuseStep 62070137 = 46552603) B46552603
theorem B41380091 : Blo 1913435 41380091 := bstep (se 1 (by rfl) ⟨31035068, by rfl⟩ : syracuseStep 41380091 = 62070137) B62070137
theorem B27586727 : Blo 1913435 27586727 := bstep (se 1 (by rfl) ⟨20690045, by rfl⟩ : syracuseStep 27586727 = 41380091) B41380091
theorem B18391151 : Blo 1913435 18391151 := bstep (se 1 (by rfl) ⟨13793363, by rfl⟩ : syracuseStep 18391151 = 27586727) B27586727
theorem B12260767 : Blo 1913435 12260767 := bstep (se 1 (by rfl) ⟨9195575, by rfl⟩ : syracuseStep 12260767 = 18391151) B18391151
theorem B16347689 : Blo 1913435 16347689 := bstep (se 2 (by rfl) ⟨6130383, by rfl⟩ : syracuseStep 16347689 = 12260767) B12260767
theorem B10898459 : Blo 1913435 10898459 := bstep (se 1 (by rfl) ⟨8173844, by rfl⟩ : syracuseStep 10898459 = 16347689) B16347689
theorem B7265639 : Blo 1913435 7265639 := bstep (se 1 (by rfl) ⟨5449229, by rfl⟩ : syracuseStep 7265639 = 10898459) B10898459
theorem B4843759 : Blo 1913435 4843759 := bstep (se 1 (by rfl) ⟨3632819, by rfl⟩ : syracuseStep 4843759 = 7265639) B7265639
theorem B6458345 : Blo 1913435 6458345 := bstep (se 2 (by rfl) ⟨2421879, by rfl⟩ : syracuseStep 6458345 = 4843759) B4843759
theorem B4305563 : Blo 1913435 4305563 := bstep (se 1 (by rfl) ⟨3229172, by rfl⟩ : syracuseStep 4305563 = 6458345) B6458345
theorem B2870375 : Blo 1913435 2870375 := bstep (se 1 (by rfl) ⟨2152781, by rfl⟩ : syracuseStep 2870375 = 4305563) B4305563
theorem B1913583 : Blo 1913435 1913583 := bstep (se 1 (by rfl) ⟨1435187, by rfl⟩ : syracuseStep 1913583 = 2870375) B2870375
theorem B2870381 : Blo 1913435 2870381 := bbase (se 3 (by rfl) ⟨538196, by rfl⟩ : syracuseStep 2870381 = 1076393) (by norm_num)
theorem B1913587 : Blo 1913435 1913587 := bstep (se 1 (by rfl) ⟨1435190, by rfl⟩ : syracuseStep 1913587 = 2870381) B2870381
theorem B4305581 : Blo 1913435 4305581 := bbase (se 3 (by rfl) ⟨807296, by rfl⟩ : syracuseStep 4305581 = 1614593) (by norm_num)
theorem B2870387 : Blo 1913435 2870387 := bstep (se 1 (by rfl) ⟨2152790, by rfl⟩ : syracuseStep 2870387 = 4305581) B4305581
theorem B1913591 : Blo 1913435 1913591 := bstep (se 1 (by rfl) ⟨1435193, by rfl⟩ : syracuseStep 1913591 = 2870387) B2870387
theorem B4086949 : Blo 1913435 4086949 := bbase (se 4 (by rfl) ⟨383151, by rfl⟩ : syracuseStep 4086949 = 766303) (by norm_num)
theorem B5449265 : Blo 1913435 5449265 := bstep (se 2 (by rfl) ⟨2043474, by rfl⟩ : syracuseStep 5449265 = 4086949) B4086949
theorem B3632843 : Blo 1913435 3632843 := bstep (se 1 (by rfl) ⟨2724632, by rfl⟩ : syracuseStep 3632843 = 5449265) B5449265
theorem B2421895 : Blo 1913435 2421895 := bstep (se 1 (by rfl) ⟨1816421, by rfl⟩ : syracuseStep 2421895 = 3632843) B3632843
theorem B3229193 : Blo 1913435 3229193 := bstep (se 2 (by rfl) ⟨1210947, by rfl⟩ : syracuseStep 3229193 = 2421895) B2421895
theorem B2152795 : Blo 1913435 2152795 := bstep (se 1 (by rfl) ⟨1614596, by rfl⟩ : syracuseStep 2152795 = 3229193) B3229193
theorem B2870393 : Blo 1913435 2870393 := bstep (se 2 (by rfl) ⟨1076397, by rfl⟩ : syracuseStep 2870393 = 2152795) B2152795
theorem B1913595 : Blo 1913435 1913595 := bstep (se 1 (by rfl) ⟨1435196, by rfl⟩ : syracuseStep 1913595 = 2870393) B2870393
theorem B12428149 : Blo 1913435 12428149 := bbase (se 5 (by rfl) ⟨582569, by rfl⟩ : syracuseStep 12428149 = 1165139) (by norm_num)
theorem B16570865 : Blo 1913435 16570865 := bstep (se 2 (by rfl) ⟨6214074, by rfl⟩ : syracuseStep 16570865 = 12428149) B12428149
theorem B44188973 : Blo 1913435 44188973 := bstep (se 3 (by rfl) ⟨8285432, by rfl⟩ : syracuseStep 44188973 = 16570865) B16570865
theorem B29459315 : Blo 1913435 29459315 := bstep (se 1 (by rfl) ⟨22094486, by rfl⟩ : syracuseStep 29459315 = 44188973) B44188973
theorem B19639543 : Blo 1913435 19639543 := bstep (se 1 (by rfl) ⟨14729657, by rfl⟩ : syracuseStep 19639543 = 29459315) B29459315
theorem B26186057 : Blo 1913435 26186057 := bstep (se 2 (by rfl) ⟨9819771, by rfl⟩ : syracuseStep 26186057 = 19639543) B19639543
theorem B17457371 : Blo 1913435 17457371 := bstep (se 1 (by rfl) ⟨13093028, by rfl⟩ : syracuseStep 17457371 = 26186057) B26186057
theorem B11638247 : Blo 1913435 11638247 := bstep (se 1 (by rfl) ⟨8728685, by rfl⟩ : syracuseStep 11638247 = 17457371) B17457371
theorem B31035325 : Blo 1913435 31035325 := bstep (se 3 (by rfl) ⟨5819123, by rfl⟩ : syracuseStep 31035325 = 11638247) B11638247
theorem B41380433 : Blo 1913435 41380433 := bstep (se 2 (by rfl) ⟨15517662, by rfl⟩ : syracuseStep 41380433 = 31035325) B31035325
theorem B27586955 : Blo 1913435 27586955 := bstep (se 1 (by rfl) ⟨20690216, by rfl⟩ : syracuseStep 27586955 = 41380433) B41380433
theorem B18391303 : Blo 1913435 18391303 := bstep (se 1 (by rfl) ⟨13793477, by rfl⟩ : syracuseStep 18391303 = 27586955) B27586955
theorem B24521737 : Blo 1913435 24521737 := bstep (se 2 (by rfl) ⟨9195651, by rfl⟩ : syracuseStep 24521737 = 18391303) B18391303
theorem B32695649 : Blo 1913435 32695649 := bstep (se 2 (by rfl) ⟨12260868, by rfl⟩ : syracuseStep 32695649 = 24521737) B24521737
theorem B21797099 : Blo 1913435 21797099 := bstep (se 1 (by rfl) ⟨16347824, by rfl⟩ : syracuseStep 21797099 = 32695649) B32695649
theorem B14531399 : Blo 1913435 14531399 := bstep (se 1 (by rfl) ⟨10898549, by rfl⟩ : syracuseStep 14531399 = 21797099) B21797099
theorem B9687599 : Blo 1913435 9687599 := bstep (se 1 (by rfl) ⟨7265699, by rfl⟩ : syracuseStep 9687599 = 14531399) B14531399
theorem B6458399 : Blo 1913435 6458399 := bstep (se 1 (by rfl) ⟨4843799, by rfl⟩ : syracuseStep 6458399 = 9687599) B9687599
theorem B4305599 : Blo 1913435 4305599 := bstep (se 1 (by rfl) ⟨3229199, by rfl⟩ : syracuseStep 4305599 = 6458399) B6458399
theorem B2870399 : Blo 1913435 2870399 := bstep (se 1 (by rfl) ⟨2152799, by rfl⟩ : syracuseStep 2870399 = 4305599) B4305599
theorem B1913599 : Blo 1913435 1913599 := bstep (se 1 (by rfl) ⟨1435199, by rfl⟩ : syracuseStep 1913599 = 2870399) B2870399
theorem B2870405 : Blo 1913435 2870405 := bbase (se 4 (by rfl) ⟨269100, by rfl⟩ : syracuseStep 2870405 = 538201) (by norm_num)
theorem B1913603 : Blo 1913435 1913603 := bstep (se 1 (by rfl) ⟨1435202, by rfl⟩ : syracuseStep 1913603 = 2870405) B2870405
theorem B3229213 : Blo 1913435 3229213 := bbase (se 3 (by rfl) ⟨605477, by rfl⟩ : syracuseStep 3229213 = 1210955) (by norm_num)
theorem B4305617 : Blo 1913435 4305617 := bstep (se 2 (by rfl) ⟨1614606, by rfl⟩ : syracuseStep 4305617 = 3229213) B3229213
theorem B2870411 : Blo 1913435 2870411 := bstep (se 1 (by rfl) ⟨2152808, by rfl⟩ : syracuseStep 2870411 = 4305617) B4305617
theorem B1913607 : Blo 1913435 1913607 := bstep (se 1 (by rfl) ⟨1435205, by rfl⟩ : syracuseStep 1913607 = 2870411) B2870411
theorem B2152813 : Blo 1913435 2152813 := bbase (se 3 (by rfl) ⟨403652, by rfl⟩ : syracuseStep 2152813 = 807305) (by norm_num)
theorem B2870417 : Blo 1913435 2870417 := bstep (se 2 (by rfl) ⟨1076406, by rfl⟩ : syracuseStep 2870417 = 2152813) B2152813
theorem B1913611 : Blo 1913435 1913611 := bstep (se 1 (by rfl) ⟨1435208, by rfl⟩ : syracuseStep 1913611 = 2870417) B2870417
theorem B6458453 : Blo 1913435 6458453 := bbase (se 8 (by rfl) ⟨37842, by rfl⟩ : syracuseStep 6458453 = 75685) (by norm_num)
theorem B4305635 : Blo 1913435 4305635 := bstep (se 1 (by rfl) ⟨3229226, by rfl⟩ : syracuseStep 4305635 = 6458453) B6458453
theorem B2870423 : Blo 1913435 2870423 := bstep (se 1 (by rfl) ⟨2152817, by rfl⟩ : syracuseStep 2870423 = 4305635) B4305635
theorem B1913615 : Blo 1913435 1913615 := bstep (se 1 (by rfl) ⟨1435211, by rfl⟩ : syracuseStep 1913615 = 2870423) B2870423
theorem B2870429 : Blo 1913435 2870429 := bbase (se 3 (by rfl) ⟨538205, by rfl⟩ : syracuseStep 2870429 = 1076411) (by norm_num)
theorem B1913619 : Blo 1913435 1913619 := bstep (se 1 (by rfl) ⟨1435214, by rfl⟩ : syracuseStep 1913619 = 2870429) B2870429
theorem B4305653 : Blo 1913435 4305653 := bbase (se 5 (by rfl) ⟨201827, by rfl⟩ : syracuseStep 4305653 = 403655) (by norm_num)
theorem B2870435 : Blo 1913435 2870435 := bstep (se 1 (by rfl) ⟨2152826, by rfl⟩ : syracuseStep 2870435 = 4305653) B4305653
theorem B1913623 : Blo 1913435 1913623 := bstep (se 1 (by rfl) ⟨1435217, by rfl⟩ : syracuseStep 1913623 = 2870435) B2870435
theorem B3448421 : Blo 1913435 3448421 := bbase (se 4 (by rfl) ⟨323289, by rfl⟩ : syracuseStep 3448421 = 646579) (by norm_num)
theorem B2298947 : Blo 1913435 2298947 := bstep (se 1 (by rfl) ⟨1724210, by rfl⟩ : syracuseStep 2298947 = 3448421) B3448421
theorem B24522101 : Blo 1913435 24522101 := bstep (se 5 (by rfl) ⟨1149473, by rfl⟩ : syracuseStep 24522101 = 2298947) B2298947
theorem B16348067 : Blo 1913435 16348067 := bstep (se 1 (by rfl) ⟨12261050, by rfl⟩ : syracuseStep 16348067 = 24522101) B24522101
theorem B10898711 : Blo 1913435 10898711 := bstep (se 1 (by rfl) ⟨8174033, by rfl⟩ : syracuseStep 10898711 = 16348067) B16348067
theorem B7265807 : Blo 1913435 7265807 := bstep (se 1 (by rfl) ⟨5449355, by rfl⟩ : syracuseStep 7265807 = 10898711) B10898711
theorem B4843871 : Blo 1913435 4843871 := bstep (se 1 (by rfl) ⟨3632903, by rfl⟩ : syracuseStep 4843871 = 7265807) B7265807
theorem B3229247 : Blo 1913435 3229247 := bstep (se 1 (by rfl) ⟨2421935, by rfl⟩ : syracuseStep 3229247 = 4843871) B4843871
theorem B2152831 : Blo 1913435 2152831 := bstep (se 1 (by rfl) ⟨1614623, by rfl⟩ : syracuseStep 2152831 = 3229247) B3229247
theorem B2870441 : Blo 1913435 2870441 := bstep (se 2 (by rfl) ⟨1076415, by rfl⟩ : syracuseStep 2870441 = 2152831) B2152831
theorem B1913627 : Blo 1913435 1913627 := bstep (se 1 (by rfl) ⟨1435220, by rfl⟩ : syracuseStep 1913627 = 2870441) B2870441
theorem B3065269 : Blo 1913435 3065269 := bbase (se 5 (by rfl) ⟨143684, by rfl⟩ : syracuseStep 3065269 = 287369) (by norm_num)
theorem B4087025 : Blo 1913435 4087025 := bstep (se 2 (by rfl) ⟨1532634, by rfl⟩ : syracuseStep 4087025 = 3065269) B3065269
theorem B2724683 : Blo 1913435 2724683 := bstep (se 1 (by rfl) ⟨2043512, by rfl⟩ : syracuseStep 2724683 = 4087025) B4087025
theorem B7265821 : Blo 1913435 7265821 := bstep (se 3 (by rfl) ⟨1362341, by rfl⟩ : syracuseStep 7265821 = 2724683) B2724683
theorem B9687761 : Blo 1913435 9687761 := bstep (se 2 (by rfl) ⟨3632910, by rfl⟩ : syracuseStep 9687761 = 7265821) B7265821
theorem B6458507 : Blo 1913435 6458507 := bstep (se 1 (by rfl) ⟨4843880, by rfl⟩ : syracuseStep 6458507 = 9687761) B9687761
theorem B4305671 : Blo 1913435 4305671 := bstep (se 1 (by rfl) ⟨3229253, by rfl⟩ : syracuseStep 4305671 = 6458507) B6458507
theorem B2870447 : Blo 1913435 2870447 := bstep (se 1 (by rfl) ⟨2152835, by rfl⟩ : syracuseStep 2870447 = 4305671) B4305671
theorem B1913631 : Blo 1913435 1913631 := bstep (se 1 (by rfl) ⟨1435223, by rfl⟩ : syracuseStep 1913631 = 2870447) B2870447
theorem B2870453 : Blo 1913435 2870453 := bbase (se 5 (by rfl) ⟨134552, by rfl⟩ : syracuseStep 2870453 = 269105) (by norm_num)
theorem B1913635 : Blo 1913435 1913635 := bstep (se 1 (by rfl) ⟨1435226, by rfl⟩ : syracuseStep 1913635 = 2870453) B2870453
theorem B4843901 : Blo 1913435 4843901 := bbase (se 3 (by rfl) ⟨908231, by rfl⟩ : syracuseStep 4843901 = 1816463) (by norm_num)
theorem B3229267 : Blo 1913435 3229267 := bstep (se 1 (by rfl) ⟨2421950, by rfl⟩ : syracuseStep 3229267 = 4843901) B4843901
theorem B4305689 : Blo 1913435 4305689 := bstep (se 2 (by rfl) ⟨1614633, by rfl⟩ : syracuseStep 4305689 = 3229267) B3229267
theorem B2870459 : Blo 1913435 2870459 := bstep (se 1 (by rfl) ⟨2152844, by rfl⟩ : syracuseStep 2870459 = 4305689) B4305689
theorem B1913639 : Blo 1913435 1913639 := bstep (se 1 (by rfl) ⟨1435229, by rfl⟩ : syracuseStep 1913639 = 2870459) B2870459
theorem B2152849 : Blo 1913435 2152849 := bbase (se 2 (by rfl) ⟨807318, by rfl⟩ : syracuseStep 2152849 = 1614637) (by norm_num)
theorem B2870465 : Blo 1913435 2870465 := bstep (se 2 (by rfl) ⟨1076424, by rfl⟩ : syracuseStep 2870465 = 2152849) B2152849
theorem B1913643 : Blo 1913435 1913643 := bstep (se 1 (by rfl) ⟨1435232, by rfl⟩ : syracuseStep 1913643 = 2870465) B2870465
theorem B3632941 : Blo 1913435 3632941 := bbase (se 3 (by rfl) ⟨681176, by rfl⟩ : syracuseStep 3632941 = 1362353) (by norm_num)
theorem B4843921 : Blo 1913435 4843921 := bstep (se 2 (by rfl) ⟨1816470, by rfl⟩ : syracuseStep 4843921 = 3632941) B3632941
theorem B6458561 : Blo 1913435 6458561 := bstep (se 2 (by rfl) ⟨2421960, by rfl⟩ : syracuseStep 6458561 = 4843921) B4843921
theorem B4305707 : Blo 1913435 4305707 := bstep (se 1 (by rfl) ⟨3229280, by rfl⟩ : syracuseStep 4305707 = 6458561) B6458561
theorem B2870471 : Blo 1913435 2870471 := bstep (se 1 (by rfl) ⟨2152853, by rfl⟩ : syracuseStep 2870471 = 4305707) B4305707
theorem B1913647 : Blo 1913435 1913647 := bstep (se 1 (by rfl) ⟨1435235, by rfl⟩ : syracuseStep 1913647 = 2870471) B2870471
theorem B2870477 : Blo 1913435 2870477 := bbase (se 3 (by rfl) ⟨538214, by rfl⟩ : syracuseStep 2870477 = 1076429) (by norm_num)
theorem B1913651 : Blo 1913435 1913651 := bstep (se 1 (by rfl) ⟨1435238, by rfl⟩ : syracuseStep 1913651 = 2870477) B2870477
theorem B4305725 : Blo 1913435 4305725 := bbase (se 3 (by rfl) ⟨807323, by rfl⟩ : syracuseStep 4305725 = 1614647) (by norm_num)
theorem B2870483 : Blo 1913435 2870483 := bstep (se 1 (by rfl) ⟨2152862, by rfl⟩ : syracuseStep 2870483 = 4305725) B4305725
theorem B1913655 : Blo 1913435 1913655 := bstep (se 1 (by rfl) ⟨1435241, by rfl⟩ : syracuseStep 1913655 = 2870483) B2870483
theorem B3229301 : Blo 1913435 3229301 := bbase (se 5 (by rfl) ⟨151373, by rfl⟩ : syracuseStep 3229301 = 302747) (by norm_num)
theorem B2152867 : Blo 1913435 2152867 := bstep (se 1 (by rfl) ⟨1614650, by rfl⟩ : syracuseStep 2152867 = 3229301) B3229301
theorem B2870489 : Blo 1913435 2870489 := bstep (se 2 (by rfl) ⟨1076433, by rfl⟩ : syracuseStep 2870489 = 2152867) B2152867
theorem B1913659 : Blo 1913435 1913659 := bstep (se 1 (by rfl) ⟨1435244, by rfl⟩ : syracuseStep 1913659 = 2870489) B2870489
theorem B4087093 : Blo 1913435 4087093 := bbase (se 5 (by rfl) ⟨191582, by rfl⟩ : syracuseStep 4087093 = 383165) (by norm_num)
theorem B5449457 : Blo 1913435 5449457 := bstep (se 2 (by rfl) ⟨2043546, by rfl⟩ : syracuseStep 5449457 = 4087093) B4087093
theorem B14531885 : Blo 1913435 14531885 := bstep (se 3 (by rfl) ⟨2724728, by rfl⟩ : syracuseStep 14531885 = 5449457) B5449457
theorem B9687923 : Blo 1913435 9687923 := bstep (se 1 (by rfl) ⟨7265942, by rfl⟩ : syracuseStep 9687923 = 14531885) B14531885
theorem B6458615 : Blo 1913435 6458615 := bstep (se 1 (by rfl) ⟨4843961, by rfl⟩ : syracuseStep 6458615 = 9687923) B9687923
theorem B4305743 : Blo 1913435 4305743 := bstep (se 1 (by rfl) ⟨3229307, by rfl⟩ : syracuseStep 4305743 = 6458615) B6458615
theorem B2870495 : Blo 1913435 2870495 := bstep (se 1 (by rfl) ⟨2152871, by rfl⟩ : syracuseStep 2870495 = 4305743) B4305743
theorem B1913663 : Blo 1913435 1913663 := bstep (se 1 (by rfl) ⟨1435247, by rfl⟩ : syracuseStep 1913663 = 2870495) B2870495
theorem B2870501 : Blo 1913435 2870501 := bbase (se 4 (by rfl) ⟨269109, by rfl⟩ : syracuseStep 2870501 = 538219) (by norm_num)
theorem B1913667 : Blo 1913435 1913667 := bstep (se 1 (by rfl) ⟨1435250, by rfl⟩ : syracuseStep 1913667 = 2870501) B2870501
theorem B17458037 : Blo 1913435 17458037 := bbase (se 5 (by rfl) ⟨818345, by rfl⟩ : syracuseStep 17458037 = 1636691) (by norm_num)
theorem B11638691 : Blo 1913435 11638691 := bstep (se 1 (by rfl) ⟨8729018, by rfl⟩ : syracuseStep 11638691 = 17458037) B17458037
theorem B7759127 : Blo 1913435 7759127 := bstep (se 1 (by rfl) ⟨5819345, by rfl⟩ : syracuseStep 7759127 = 11638691) B11638691
theorem B5172751 : Blo 1913435 5172751 := bstep (se 1 (by rfl) ⟨3879563, by rfl⟩ : syracuseStep 5172751 = 7759127) B7759127
theorem B6897001 : Blo 1913435 6897001 := bstep (se 2 (by rfl) ⟨2586375, by rfl⟩ : syracuseStep 6897001 = 5172751) B5172751
theorem B9196001 : Blo 1913435 9196001 := bstep (se 2 (by rfl) ⟨3448500, by rfl⟩ : syracuseStep 9196001 = 6897001) B6897001
theorem B6130667 : Blo 1913435 6130667 := bstep (se 1 (by rfl) ⟨4598000, by rfl⟩ : syracuseStep 6130667 = 9196001) B9196001
theorem B4087111 : Blo 1913435 4087111 := bstep (se 1 (by rfl) ⟨3065333, by rfl⟩ : syracuseStep 4087111 = 6130667) B6130667
theorem B5449481 : Blo 1913435 5449481 := bstep (se 2 (by rfl) ⟨2043555, by rfl⟩ : syracuseStep 5449481 = 4087111) B4087111
theorem B3632987 : Blo 1913435 3632987 := bstep (se 1 (by rfl) ⟨2724740, by rfl⟩ : syracuseStep 3632987 = 5449481) B5449481
theorem B2421991 : Blo 1913435 2421991 := bstep (se 1 (by rfl) ⟨1816493, by rfl⟩ : syracuseStep 2421991 = 3632987) B3632987
theorem B3229321 : Blo 1913435 3229321 := bstep (se 2 (by rfl) ⟨1210995, by rfl⟩ : syracuseStep 3229321 = 2421991) B2421991
theorem B4305761 : Blo 1913435 4305761 := bstep (se 2 (by rfl) ⟨1614660, by rfl⟩ : syracuseStep 4305761 = 3229321) B3229321
theorem B2870507 : Blo 1913435 2870507 := bstep (se 1 (by rfl) ⟨2152880, by rfl⟩ : syracuseStep 2870507 = 4305761) B4305761
theorem B1913671 : Blo 1913435 1913671 := bstep (se 1 (by rfl) ⟨1435253, by rfl⟩ : syracuseStep 1913671 = 2870507) B2870507
theorem B2152885 : Blo 1913435 2152885 := bbase (se 5 (by rfl) ⟨100916, by rfl⟩ : syracuseStep 2152885 = 201833) (by norm_num)
theorem B2870513 : Blo 1913435 2870513 := bstep (se 2 (by rfl) ⟨1076442, by rfl⟩ : syracuseStep 2870513 = 2152885) B2152885
theorem B1913675 : Blo 1913435 1913675 := bstep (se 1 (by rfl) ⟨1435256, by rfl⟩ : syracuseStep 1913675 = 2870513) B2870513
theorem B2422001 : Blo 1913435 2422001 := bbase (se 2 (by rfl) ⟨908250, by rfl⟩ : syracuseStep 2422001 = 1816501) (by norm_num)
theorem B6458669 : Blo 1913435 6458669 := bstep (se 3 (by rfl) ⟨1211000, by rfl⟩ : syracuseStep 6458669 = 2422001) B2422001
theorem B4305779 : Blo 1913435 4305779 := bstep (se 1 (by rfl) ⟨3229334, by rfl⟩ : syracuseStep 4305779 = 6458669) B6458669
theorem B2870519 : Blo 1913435 2870519 := bstep (se 1 (by rfl) ⟨2152889, by rfl⟩ : syracuseStep 2870519 = 4305779) B4305779
theorem B1913679 : Blo 1913435 1913679 := bstep (se 1 (by rfl) ⟨1435259, by rfl⟩ : syracuseStep 1913679 = 2870519) B2870519
theorem B2870525 : Blo 1913435 2870525 := bbase (se 3 (by rfl) ⟨538223, by rfl⟩ : syracuseStep 2870525 = 1076447) (by norm_num)
theorem B1913683 : Blo 1913435 1913683 := bstep (se 1 (by rfl) ⟨1435262, by rfl⟩ : syracuseStep 1913683 = 2870525) B2870525
theorem B4305797 : Blo 1913435 4305797 := bbase (se 4 (by rfl) ⟨403668, by rfl⟩ : syracuseStep 4305797 = 807337) (by norm_num)
theorem B2870531 : Blo 1913435 2870531 := bstep (se 1 (by rfl) ⟨2152898, by rfl⟩ : syracuseStep 2870531 = 4305797) B4305797
theorem B1913687 : Blo 1913435 1913687 := bstep (se 1 (by rfl) ⟨1435265, by rfl⟩ : syracuseStep 1913687 = 2870531) B2870531
theorem B2043577 : Blo 1913435 2043577 := bbase (se 2 (by rfl) ⟨766341, by rfl⟩ : syracuseStep 2043577 = 1532683) (by norm_num)
theorem B2724769 : Blo 1913435 2724769 := bstep (se 2 (by rfl) ⟨1021788, by rfl⟩ : syracuseStep 2724769 = 2043577) B2043577
theorem B3633025 : Blo 1913435 3633025 := bstep (se 2 (by rfl) ⟨1362384, by rfl⟩ : syracuseStep 3633025 = 2724769) B2724769
theorem B4844033 : Blo 1913435 4844033 := bstep (se 2 (by rfl) ⟨1816512, by rfl⟩ : syracuseStep 4844033 = 3633025) B3633025
theorem B3229355 : Blo 1913435 3229355 := bstep (se 1 (by rfl) ⟨2422016, by rfl⟩ : syracuseStep 3229355 = 4844033) B4844033
theorem B2152903 : Blo 1913435 2152903 := bstep (se 1 (by rfl) ⟨1614677, by rfl⟩ : syracuseStep 2152903 = 3229355) B3229355
theorem B2870537 : Blo 1913435 2870537 := bstep (se 2 (by rfl) ⟨1076451, by rfl⟩ : syracuseStep 2870537 = 2152903) B2152903
theorem B1913691 : Blo 1913435 1913691 := bstep (se 1 (by rfl) ⟨1435268, by rfl⟩ : syracuseStep 1913691 = 2870537) B2870537
theorem B9688085 : Blo 1913435 9688085 := bbase (se 6 (by rfl) ⟨227064, by rfl⟩ : syracuseStep 9688085 = 454129) (by norm_num)
theorem B6458723 : Blo 1913435 6458723 := bstep (se 1 (by rfl) ⟨4844042, by rfl⟩ : syracuseStep 6458723 = 9688085) B9688085
theorem B4305815 : Blo 1913435 4305815 := bstep (se 1 (by rfl) ⟨3229361, by rfl⟩ : syracuseStep 4305815 = 6458723) B6458723
theorem B2870543 : Blo 1913435 2870543 := bstep (se 1 (by rfl) ⟨2152907, by rfl⟩ : syracuseStep 2870543 = 4305815) B4305815
theorem B1913695 : Blo 1913435 1913695 := bstep (se 1 (by rfl) ⟨1435271, by rfl⟩ : syracuseStep 1913695 = 2870543) B2870543
theorem B2870549 : Blo 1913435 2870549 := bbase (se 6 (by rfl) ⟨67278, by rfl⟩ : syracuseStep 2870549 = 134557) (by norm_num)
theorem B1913699 : Blo 1913435 1913699 := bstep (se 1 (by rfl) ⟨1435274, by rfl⟩ : syracuseStep 1913699 = 2870549) B2870549
theorem B13794229 : Blo 1913435 13794229 := bbase (se 5 (by rfl) ⟨646604, by rfl⟩ : syracuseStep 13794229 = 1293209) (by norm_num)
theorem B18392305 : Blo 1913435 18392305 := bstep (se 2 (by rfl) ⟨6897114, by rfl⟩ : syracuseStep 18392305 = 13794229) B13794229
theorem B24523073 : Blo 1913435 24523073 := bstep (se 2 (by rfl) ⟨9196152, by rfl⟩ : syracuseStep 24523073 = 18392305) B18392305
theorem B16348715 : Blo 1913435 16348715 := bstep (se 1 (by rfl) ⟨12261536, by rfl⟩ : syracuseStep 16348715 = 24523073) B24523073
theorem B10899143 : Blo 1913435 10899143 := bstep (se 1 (by rfl) ⟨8174357, by rfl⟩ : syracuseStep 10899143 = 16348715) B16348715
theorem B7266095 : Blo 1913435 7266095 := bstep (se 1 (by rfl) ⟨5449571, by rfl⟩ : syracuseStep 7266095 = 10899143) B10899143
theorem B4844063 : Blo 1913435 4844063 := bstep (se 1 (by rfl) ⟨3633047, by rfl⟩ : syracuseStep 4844063 = 7266095) B7266095
theorem B3229375 : Blo 1913435 3229375 := bstep (se 1 (by rfl) ⟨2422031, by rfl⟩ : syracuseStep 3229375 = 4844063) B4844063
theorem B4305833 : Blo 1913435 4305833 := bstep (se 2 (by rfl) ⟨1614687, by rfl⟩ : syracuseStep 4305833 = 3229375) B3229375
theorem B2870555 : Blo 1913435 2870555 := bstep (se 1 (by rfl) ⟨2152916, by rfl⟩ : syracuseStep 2870555 = 4305833) B4305833
theorem B1913703 : Blo 1913435 1913703 := bstep (se 1 (by rfl) ⟨1435277, by rfl⟩ : syracuseStep 1913703 = 2870555) B2870555
theorem B2152921 : Blo 1913435 2152921 := bbase (se 2 (by rfl) ⟨807345, by rfl⟩ : syracuseStep 2152921 = 1614691) (by norm_num)
theorem B2870561 : Blo 1913435 2870561 := bstep (se 2 (by rfl) ⟨1076460, by rfl⟩ : syracuseStep 2870561 = 2152921) B2152921
theorem B1913707 : Blo 1913435 1913707 := bstep (se 1 (by rfl) ⟨1435280, by rfl⟩ : syracuseStep 1913707 = 2870561) B2870561
theorem B2724797 : Blo 1913435 2724797 := bbase (se 3 (by rfl) ⟨510899, by rfl⟩ : syracuseStep 2724797 = 1021799) (by norm_num)
theorem B7266125 : Blo 1913435 7266125 := bstep (se 3 (by rfl) ⟨1362398, by rfl⟩ : syracuseStep 7266125 = 2724797) B2724797
theorem B4844083 : Blo 1913435 4844083 := bstep (se 1 (by rfl) ⟨3633062, by rfl⟩ : syracuseStep 4844083 = 7266125) B7266125
theorem B6458777 : Blo 1913435 6458777 := bstep (se 2 (by rfl) ⟨2422041, by rfl⟩ : syracuseStep 6458777 = 4844083) B4844083
theorem B4305851 : Blo 1913435 4305851 := bstep (se 1 (by rfl) ⟨3229388, by rfl⟩ : syracuseStep 4305851 = 6458777) B6458777
theorem B2870567 : Blo 1913435 2870567 := bstep (se 1 (by rfl) ⟨2152925, by rfl⟩ : syracuseStep 2870567 = 4305851) B4305851
theorem B1913711 : Blo 1913435 1913711 := bstep (se 1 (by rfl) ⟨1435283, by rfl⟩ : syracuseStep 1913711 = 2870567) B2870567
theorem B2870573 : Blo 1913435 2870573 := bbase (se 3 (by rfl) ⟨538232, by rfl⟩ : syracuseStep 2870573 = 1076465) (by norm_num)
theorem B1913715 : Blo 1913435 1913715 := bstep (se 1 (by rfl) ⟨1435286, by rfl⟩ : syracuseStep 1913715 = 2870573) B2870573
theorem B4305869 : Blo 1913435 4305869 := bbase (se 3 (by rfl) ⟨807350, by rfl⟩ : syracuseStep 4305869 = 1614701) (by norm_num)
theorem B2870579 : Blo 1913435 2870579 := bstep (se 1 (by rfl) ⟨2152934, by rfl⟩ : syracuseStep 2870579 = 4305869) B4305869
theorem B1913719 : Blo 1913435 1913719 := bstep (se 1 (by rfl) ⟨1435289, by rfl⟩ : syracuseStep 1913719 = 2870579) B2870579
theorem B2422057 : Blo 1913435 2422057 := bbase (se 2 (by rfl) ⟨908271, by rfl⟩ : syracuseStep 2422057 = 1816543) (by norm_num)
theorem B3229409 : Blo 1913435 3229409 := bstep (se 2 (by rfl) ⟨1211028, by rfl⟩ : syracuseStep 3229409 = 2422057) B2422057
theorem B2152939 : Blo 1913435 2152939 := bstep (se 1 (by rfl) ⟨1614704, by rfl⟩ : syracuseStep 2152939 = 3229409) B3229409
theorem B2870585 : Blo 1913435 2870585 := bstep (se 2 (by rfl) ⟨1076469, by rfl⟩ : syracuseStep 2870585 = 2152939) B2152939
theorem B1913723 : Blo 1913435 1913723 := bstep (se 1 (by rfl) ⟨1435292, by rfl⟩ : syracuseStep 1913723 = 2870585) B2870585
theorem B8285989 : Blo 1913435 8285989 := bbase (se 4 (by rfl) ⟨776811, by rfl⟩ : syracuseStep 8285989 = 1553623) (by norm_num)
theorem B11047985 : Blo 1913435 11047985 := bstep (se 2 (by rfl) ⟨4142994, by rfl⟩ : syracuseStep 11047985 = 8285989) B8285989
theorem B7365323 : Blo 1913435 7365323 := bstep (se 1 (by rfl) ⟨5523992, by rfl⟩ : syracuseStep 7365323 = 11047985) B11047985
theorem B4910215 : Blo 1913435 4910215 := bstep (se 1 (by rfl) ⟨3682661, by rfl⟩ : syracuseStep 4910215 = 7365323) B7365323
theorem B6546953 : Blo 1913435 6546953 := bstep (se 2 (by rfl) ⟨2455107, by rfl⟩ : syracuseStep 6546953 = 4910215) B4910215
theorem B17458541 : Blo 1913435 17458541 := bstep (se 3 (by rfl) ⟨3273476, by rfl⟩ : syracuseStep 17458541 = 6546953) B6546953
theorem B11639027 : Blo 1913435 11639027 := bstep (se 1 (by rfl) ⟨8729270, by rfl⟩ : syracuseStep 11639027 = 17458541) B17458541
theorem B7759351 : Blo 1913435 7759351 := bstep (se 1 (by rfl) ⟨5819513, by rfl⟩ : syracuseStep 7759351 = 11639027) B11639027
theorem B10345801 : Blo 1913435 10345801 := bstep (se 2 (by rfl) ⟨3879675, by rfl⟩ : syracuseStep 10345801 = 7759351) B7759351
theorem B13794401 : Blo 1913435 13794401 := bstep (se 2 (by rfl) ⟨5172900, by rfl⟩ : syracuseStep 13794401 = 10345801) B10345801
theorem B9196267 : Blo 1913435 9196267 := bstep (se 1 (by rfl) ⟨6897200, by rfl⟩ : syracuseStep 9196267 = 13794401) B13794401
theorem B12261689 : Blo 1913435 12261689 := bstep (se 2 (by rfl) ⟨4598133, by rfl⟩ : syracuseStep 12261689 = 9196267) B9196267
theorem B8174459 : Blo 1913435 8174459 := bstep (se 1 (by rfl) ⟨6130844, by rfl⟩ : syracuseStep 8174459 = 12261689) B12261689
theorem B21798557 : Blo 1913435 21798557 := bstep (se 3 (by rfl) ⟨4087229, by rfl⟩ : syracuseStep 21798557 = 8174459) B8174459
theorem B14532371 : Blo 1913435 14532371 := bstep (se 1 (by rfl) ⟨10899278, by rfl⟩ : syracuseStep 14532371 = 21798557) B21798557
theorem B9688247 : Blo 1913435 9688247 := bstep (se 1 (by rfl) ⟨7266185, by rfl⟩ : syracuseStep 9688247 = 14532371) B14532371
theorem B6458831 : Blo 1913435 6458831 := bstep (se 1 (by rfl) ⟨4844123, by rfl⟩ : syracuseStep 6458831 = 9688247) B9688247
theorem B4305887 : Blo 1913435 4305887 := bstep (se 1 (by rfl) ⟨3229415, by rfl⟩ : syracuseStep 4305887 = 6458831) B6458831
theorem B2870591 : Blo 1913435 2870591 := bstep (se 1 (by rfl) ⟨2152943, by rfl⟩ : syracuseStep 2870591 = 4305887) B4305887
theorem B1913727 : Blo 1913435 1913727 := bstep (se 1 (by rfl) ⟨1435295, by rfl⟩ : syracuseStep 1913727 = 2870591) B2870591
theorem B2870597 : Blo 1913435 2870597 := bbase (se 4 (by rfl) ⟨269118, by rfl⟩ : syracuseStep 2870597 = 538237) (by norm_num)
theorem B1913731 : Blo 1913435 1913731 := bstep (se 1 (by rfl) ⟨1435298, by rfl⟩ : syracuseStep 1913731 = 2870597) B2870597
theorem B3229429 : Blo 1913435 3229429 := bbase (se 5 (by rfl) ⟨151379, by rfl⟩ : syracuseStep 3229429 = 302759) (by norm_num)
theorem B4305905 : Blo 1913435 4305905 := bstep (se 2 (by rfl) ⟨1614714, by rfl⟩ : syracuseStep 4305905 = 3229429) B3229429
theorem B2870603 : Blo 1913435 2870603 := bstep (se 1 (by rfl) ⟨2152952, by rfl⟩ : syracuseStep 2870603 = 4305905) B4305905
theorem B1913735 : Blo 1913435 1913735 := bstep (se 1 (by rfl) ⟨1435301, by rfl⟩ : syracuseStep 1913735 = 2870603) B2870603
theorem B2152957 : Blo 1913435 2152957 := bbase (se 3 (by rfl) ⟨403679, by rfl⟩ : syracuseStep 2152957 = 807359) (by norm_num)
theorem B2870609 : Blo 1913435 2870609 := bstep (se 2 (by rfl) ⟨1076478, by rfl⟩ : syracuseStep 2870609 = 2152957) B2152957
theorem B1913739 : Blo 1913435 1913739 := bstep (se 1 (by rfl) ⟨1435304, by rfl⟩ : syracuseStep 1913739 = 2870609) B2870609
theorem B6458885 : Blo 1913435 6458885 := bbase (se 4 (by rfl) ⟨605520, by rfl⟩ : syracuseStep 6458885 = 1211041) (by norm_num)
theorem B4305923 : Blo 1913435 4305923 := bstep (se 1 (by rfl) ⟨3229442, by rfl⟩ : syracuseStep 4305923 = 6458885) B6458885
theorem B2870615 : Blo 1913435 2870615 := bstep (se 1 (by rfl) ⟨2152961, by rfl⟩ : syracuseStep 2870615 = 4305923) B4305923
theorem B1913743 : Blo 1913435 1913743 := bstep (se 1 (by rfl) ⟨1435307, by rfl⟩ : syracuseStep 1913743 = 2870615) B2870615
theorem B2870621 : Blo 1913435 2870621 := bbase (se 3 (by rfl) ⟨538241, by rfl⟩ : syracuseStep 2870621 = 1076483) (by norm_num)
theorem B1913747 : Blo 1913435 1913747 := bstep (se 1 (by rfl) ⟨1435310, by rfl⟩ : syracuseStep 1913747 = 2870621) B2870621
theorem B4305941 : Blo 1913435 4305941 := bbase (se 6 (by rfl) ⟨100920, by rfl⟩ : syracuseStep 4305941 = 201841) (by norm_num)
theorem B2870627 : Blo 1913435 2870627 := bstep (se 1 (by rfl) ⟨2152970, by rfl⟩ : syracuseStep 2870627 = 4305941) B4305941
theorem B1913751 : Blo 1913435 1913751 := bstep (se 1 (by rfl) ⟨1435313, by rfl⟩ : syracuseStep 1913751 = 2870627) B2870627
theorem B7266293 : Blo 1913435 7266293 := bbase (se 5 (by rfl) ⟨340607, by rfl⟩ : syracuseStep 7266293 = 681215) (by norm_num)
theorem B4844195 : Blo 1913435 4844195 := bstep (se 1 (by rfl) ⟨3633146, by rfl⟩ : syracuseStep 4844195 = 7266293) B7266293
theorem B3229463 : Blo 1913435 3229463 := bstep (se 1 (by rfl) ⟨2422097, by rfl⟩ : syracuseStep 3229463 = 4844195) B4844195
theorem B2152975 : Blo 1913435 2152975 := bstep (se 1 (by rfl) ⟨1614731, by rfl⟩ : syracuseStep 2152975 = 3229463) B3229463
theorem B2870633 : Blo 1913435 2870633 := bstep (se 2 (by rfl) ⟨1076487, by rfl⟩ : syracuseStep 2870633 = 2152975) B2152975
theorem B1913755 : Blo 1913435 1913755 := bstep (se 1 (by rfl) ⟨1435316, by rfl⟩ : syracuseStep 1913755 = 2870633) B2870633
theorem B2043649 : Blo 1913435 2043649 := bbase (se 2 (by rfl) ⟨766368, by rfl⟩ : syracuseStep 2043649 = 1532737) (by norm_num)
theorem B10899461 : Blo 1913435 10899461 := bstep (se 4 (by rfl) ⟨1021824, by rfl⟩ : syracuseStep 10899461 = 2043649) B2043649
theorem B7266307 : Blo 1913435 7266307 := bstep (se 1 (by rfl) ⟨5449730, by rfl⟩ : syracuseStep 7266307 = 10899461) B10899461
theorem B9688409 : Blo 1913435 9688409 := bstep (se 2 (by rfl) ⟨3633153, by rfl⟩ : syracuseStep 9688409 = 7266307) B7266307
theorem B6458939 : Blo 1913435 6458939 := bstep (se 1 (by rfl) ⟨4844204, by rfl⟩ : syracuseStep 6458939 = 9688409) B9688409
theorem B4305959 : Blo 1913435 4305959 := bstep (se 1 (by rfl) ⟨3229469, by rfl⟩ : syracuseStep 4305959 = 6458939) B6458939
theorem B2870639 : Blo 1913435 2870639 := bstep (se 1 (by rfl) ⟨2152979, by rfl⟩ : syracuseStep 2870639 = 4305959) B4305959
theorem B1913759 : Blo 1913435 1913759 := bstep (se 1 (by rfl) ⟨1435319, by rfl⟩ : syracuseStep 1913759 = 2870639) B2870639
theorem B2870645 : Blo 1913435 2870645 := bbase (se 5 (by rfl) ⟨134561, by rfl⟩ : syracuseStep 2870645 = 269123) (by norm_num)
theorem B1913763 : Blo 1913435 1913763 := bstep (se 1 (by rfl) ⟨1435322, by rfl⟩ : syracuseStep 1913763 = 2870645) B2870645
theorem B2724877 : Blo 1913435 2724877 := bbase (se 3 (by rfl) ⟨510914, by rfl⟩ : syracuseStep 2724877 = 1021829) (by norm_num)
theorem B3633169 : Blo 1913435 3633169 := bstep (se 2 (by rfl) ⟨1362438, by rfl⟩ : syracuseStep 3633169 = 2724877) B2724877
theorem B4844225 : Blo 1913435 4844225 := bstep (se 2 (by rfl) ⟨1816584, by rfl⟩ : syracuseStep 4844225 = 3633169) B3633169
theorem B3229483 : Blo 1913435 3229483 := bstep (se 1 (by rfl) ⟨2422112, by rfl⟩ : syracuseStep 3229483 = 4844225) B4844225
theorem B4305977 : Blo 1913435 4305977 := bstep (se 2 (by rfl) ⟨1614741, by rfl⟩ : syracuseStep 4305977 = 3229483) B3229483
theorem B2870651 : Blo 1913435 2870651 := bstep (se 1 (by rfl) ⟨2152988, by rfl⟩ : syracuseStep 2870651 = 4305977) B4305977
theorem B1913767 : Blo 1913435 1913767 := bstep (se 1 (by rfl) ⟨1435325, by rfl⟩ : syracuseStep 1913767 = 2870651) B2870651
theorem B2152993 : Blo 1913435 2152993 := bbase (se 2 (by rfl) ⟨807372, by rfl⟩ : syracuseStep 2152993 = 1614745) (by norm_num)
theorem B2870657 : Blo 1913435 2870657 := bstep (se 2 (by rfl) ⟨1076496, by rfl⟩ : syracuseStep 2870657 = 2152993) B2152993
theorem B1913771 : Blo 1913435 1913771 := bstep (se 1 (by rfl) ⟨1435328, by rfl⟩ : syracuseStep 1913771 = 2870657) B2870657
theorem B4844245 : Blo 1913435 4844245 := bbase (se 7 (by rfl) ⟨56768, by rfl⟩ : syracuseStep 4844245 = 113537) (by norm_num)
theorem B6458993 : Blo 1913435 6458993 := bstep (se 2 (by rfl) ⟨2422122, by rfl⟩ : syracuseStep 6458993 = 4844245) B4844245
theorem B4305995 : Blo 1913435 4305995 := bstep (se 1 (by rfl) ⟨3229496, by rfl⟩ : syracuseStep 4305995 = 6458993) B6458993
theorem B2870663 : Blo 1913435 2870663 := bstep (se 1 (by rfl) ⟨2152997, by rfl⟩ : syracuseStep 2870663 = 4305995) B4305995
theorem B1913775 : Blo 1913435 1913775 := bstep (se 1 (by rfl) ⟨1435331, by rfl⟩ : syracuseStep 1913775 = 2870663) B2870663
theorem B2870669 : Blo 1913435 2870669 := bbase (se 3 (by rfl) ⟨538250, by rfl⟩ : syracuseStep 2870669 = 1076501) (by norm_num)
theorem B1913779 : Blo 1913435 1913779 := bstep (se 1 (by rfl) ⟨1435334, by rfl⟩ : syracuseStep 1913779 = 2870669) B2870669
theorem B4306013 : Blo 1913435 4306013 := bbase (se 3 (by rfl) ⟨807377, by rfl⟩ : syracuseStep 4306013 = 1614755) (by norm_num)
theorem B2870675 : Blo 1913435 2870675 := bstep (se 1 (by rfl) ⟨2153006, by rfl⟩ : syracuseStep 2870675 = 4306013) B4306013
theorem B1913783 : Blo 1913435 1913783 := bstep (se 1 (by rfl) ⟨1435337, by rfl⟩ : syracuseStep 1913783 = 2870675) B2870675
theorem B3229517 : Blo 1913435 3229517 := bbase (se 3 (by rfl) ⟨605534, by rfl⟩ : syracuseStep 3229517 = 1211069) (by norm_num)
theorem B2153011 : Blo 1913435 2153011 := bstep (se 1 (by rfl) ⟨1614758, by rfl⟩ : syracuseStep 2153011 = 3229517) B3229517
theorem B2870681 : Blo 1913435 2870681 := bstep (se 2 (by rfl) ⟨1076505, by rfl⟩ : syracuseStep 2870681 = 2153011) B2153011
theorem B1913787 : Blo 1913435 1913787 := bstep (se 1 (by rfl) ⟨1435340, by rfl⟩ : syracuseStep 1913787 = 2870681) B2870681
theorem B15519221 : Blo 1913435 15519221 := bbase (se 5 (by rfl) ⟨727463, by rfl⟩ : syracuseStep 15519221 = 1454927) (by norm_num)
theorem B10346147 : Blo 1913435 10346147 := bstep (se 1 (by rfl) ⟨7759610, by rfl⟩ : syracuseStep 10346147 = 15519221) B15519221
theorem B6897431 : Blo 1913435 6897431 := bstep (se 1 (by rfl) ⟨5173073, by rfl⟩ : syracuseStep 6897431 = 10346147) B10346147
theorem B18393149 : Blo 1913435 18393149 := bstep (se 3 (by rfl) ⟨3448715, by rfl⟩ : syracuseStep 18393149 = 6897431) B6897431
theorem B12262099 : Blo 1913435 12262099 := bstep (se 1 (by rfl) ⟨9196574, by rfl⟩ : syracuseStep 12262099 = 18393149) B18393149
theorem B16349465 : Blo 1913435 16349465 := bstep (se 2 (by rfl) ⟨6131049, by rfl⟩ : syracuseStep 16349465 = 12262099) B12262099
theorem B10899643 : Blo 1913435 10899643 := bstep (se 1 (by rfl) ⟨8174732, by rfl⟩ : syracuseStep 10899643 = 16349465) B16349465
theorem B14532857 : Blo 1913435 14532857 := bstep (se 2 (by rfl) ⟨5449821, by rfl⟩ : syracuseStep 14532857 = 10899643) B10899643
theorem B9688571 : Blo 1913435 9688571 := bstep (se 1 (by rfl) ⟨7266428, by rfl⟩ : syracuseStep 9688571 = 14532857) B14532857
theorem B6459047 : Blo 1913435 6459047 := bstep (se 1 (by rfl) ⟨4844285, by rfl⟩ : syracuseStep 6459047 = 9688571) B9688571
theorem B4306031 : Blo 1913435 4306031 := bstep (se 1 (by rfl) ⟨3229523, by rfl⟩ : syracuseStep 4306031 = 6459047) B6459047
theorem B2870687 : Blo 1913435 2870687 := bstep (se 1 (by rfl) ⟨2153015, by rfl⟩ : syracuseStep 2870687 = 4306031) B4306031
theorem B1913791 : Blo 1913435 1913791 := bstep (se 1 (by rfl) ⟨1435343, by rfl⟩ : syracuseStep 1913791 = 2870687) B2870687
theorem B2870693 : Blo 1913435 2870693 := bbase (se 4 (by rfl) ⟨269127, by rfl⟩ : syracuseStep 2870693 = 538255) (by norm_num)
theorem B1913795 : Blo 1913435 1913795 := bstep (se 1 (by rfl) ⟨1435346, by rfl⟩ : syracuseStep 1913795 = 2870693) B2870693
theorem B2422153 : Blo 1913435 2422153 := bbase (se 2 (by rfl) ⟨908307, by rfl⟩ : syracuseStep 2422153 = 1816615) (by norm_num)
theorem B3229537 : Blo 1913435 3229537 := bstep (se 2 (by rfl) ⟨1211076, by rfl⟩ : syracuseStep 3229537 = 2422153) B2422153
theorem B4306049 : Blo 1913435 4306049 := bstep (se 2 (by rfl) ⟨1614768, by rfl⟩ : syracuseStep 4306049 = 3229537) B3229537
theorem B2870699 : Blo 1913435 2870699 := bstep (se 1 (by rfl) ⟨2153024, by rfl⟩ : syracuseStep 2870699 = 4306049) B4306049
theorem B1913799 : Blo 1913435 1913799 := bstep (se 1 (by rfl) ⟨1435349, by rfl⟩ : syracuseStep 1913799 = 2870699) B2870699
theorem B2153029 : Blo 1913435 2153029 := bbase (se 4 (by rfl) ⟨201846, by rfl⟩ : syracuseStep 2153029 = 403693) (by norm_num)
theorem B2870705 : Blo 1913435 2870705 := bstep (se 2 (by rfl) ⟨1076514, by rfl⟩ : syracuseStep 2870705 = 2153029) B2153029
theorem B1913803 : Blo 1913435 1913803 := bstep (se 1 (by rfl) ⟨1435352, by rfl⟩ : syracuseStep 1913803 = 2870705) B2870705
theorem B3633245 : Blo 1913435 3633245 := bbase (se 3 (by rfl) ⟨681233, by rfl⟩ : syracuseStep 3633245 = 1362467) (by norm_num)
theorem B2422163 : Blo 1913435 2422163 := bstep (se 1 (by rfl) ⟨1816622, by rfl⟩ : syracuseStep 2422163 = 3633245) B3633245
theorem B6459101 : Blo 1913435 6459101 := bstep (se 3 (by rfl) ⟨1211081, by rfl⟩ : syracuseStep 6459101 = 2422163) B2422163
theorem B4306067 : Blo 1913435 4306067 := bstep (se 1 (by rfl) ⟨3229550, by rfl⟩ : syracuseStep 4306067 = 6459101) B6459101
theorem B2870711 : Blo 1913435 2870711 := bstep (se 1 (by rfl) ⟨2153033, by rfl⟩ : syracuseStep 2870711 = 4306067) B4306067
theorem B1913807 : Blo 1913435 1913807 := bstep (se 1 (by rfl) ⟨1435355, by rfl⟩ : syracuseStep 1913807 = 2870711) B2870711
theorem B2870717 : Blo 1913435 2870717 := bbase (se 3 (by rfl) ⟨538259, by rfl⟩ : syracuseStep 2870717 = 1076519) (by norm_num)
theorem B1913811 : Blo 1913435 1913811 := bstep (se 1 (by rfl) ⟨1435358, by rfl⟩ : syracuseStep 1913811 = 2870717) B2870717
theorem B4306085 : Blo 1913435 4306085 := bbase (se 4 (by rfl) ⟨403695, by rfl⟩ : syracuseStep 4306085 = 807391) (by norm_num)
theorem B2870723 : Blo 1913435 2870723 := bstep (se 1 (by rfl) ⟨2153042, by rfl⟩ : syracuseStep 2870723 = 4306085) B4306085
theorem B1913815 : Blo 1913435 1913815 := bstep (se 1 (by rfl) ⟨1435361, by rfl⟩ : syracuseStep 1913815 = 2870723) B2870723
theorem B4844357 : Blo 1913435 4844357 := bbase (se 4 (by rfl) ⟨454158, by rfl⟩ : syracuseStep 4844357 = 908317) (by norm_num)
theorem B3229571 : Blo 1913435 3229571 := bstep (se 1 (by rfl) ⟨2422178, by rfl⟩ : syracuseStep 3229571 = 4844357) B4844357
theorem B2153047 : Blo 1913435 2153047 := bstep (se 1 (by rfl) ⟨1614785, by rfl⟩ : syracuseStep 2153047 = 3229571) B3229571
theorem B2870729 : Blo 1913435 2870729 := bstep (se 2 (by rfl) ⟨1076523, by rfl⟩ : syracuseStep 2870729 = 2153047) B2153047
theorem B1913819 : Blo 1913435 1913819 := bstep (se 1 (by rfl) ⟨1435364, by rfl⟩ : syracuseStep 1913819 = 2870729) B2870729
theorem B4598365 : Blo 1913435 4598365 := bbase (se 3 (by rfl) ⟨862193, by rfl⟩ : syracuseStep 4598365 = 1724387) (by norm_num)
theorem B6131153 : Blo 1913435 6131153 := bstep (se 2 (by rfl) ⟨2299182, by rfl⟩ : syracuseStep 6131153 = 4598365) B4598365
theorem B4087435 : Blo 1913435 4087435 := bstep (se 1 (by rfl) ⟨3065576, by rfl⟩ : syracuseStep 4087435 = 6131153) B6131153
theorem B5449913 : Blo 1913435 5449913 := bstep (se 2 (by rfl) ⟨2043717, by rfl⟩ : syracuseStep 5449913 = 4087435) B4087435
theorem B3633275 : Blo 1913435 3633275 := bstep (se 1 (by rfl) ⟨2724956, by rfl⟩ : syracuseStep 3633275 = 5449913) B5449913
theorem B9688733 : Blo 1913435 9688733 := bstep (se 3 (by rfl) ⟨1816637, by rfl⟩ : syracuseStep 9688733 = 3633275) B3633275
theorem B6459155 : Blo 1913435 6459155 := bstep (se 1 (by rfl) ⟨4844366, by rfl⟩ : syracuseStep 6459155 = 9688733) B9688733
theorem B4306103 : Blo 1913435 4306103 := bstep (se 1 (by rfl) ⟨3229577, by rfl⟩ : syracuseStep 4306103 = 6459155) B6459155
theorem B2870735 : Blo 1913435 2870735 := bstep (se 1 (by rfl) ⟨2153051, by rfl⟩ : syracuseStep 2870735 = 4306103) B4306103
theorem B1913823 : Blo 1913435 1913823 := bstep (se 1 (by rfl) ⟨1435367, by rfl⟩ : syracuseStep 1913823 = 2870735) B2870735
theorem B2870741 : Blo 1913435 2870741 := bbase (se 7 (by rfl) ⟨33641, by rfl⟩ : syracuseStep 2870741 = 67283) (by norm_num)
theorem B1913827 : Blo 1913435 1913827 := bstep (se 1 (by rfl) ⟨1435370, by rfl⟩ : syracuseStep 1913827 = 2870741) B2870741
theorem B7266581 : Blo 1913435 7266581 := bbase (se 6 (by rfl) ⟨170310, by rfl⟩ : syracuseStep 7266581 = 340621) (by norm_num)
theorem B4844387 : Blo 1913435 4844387 := bstep (se 1 (by rfl) ⟨3633290, by rfl⟩ : syracuseStep 4844387 = 7266581) B7266581
theorem B3229591 : Blo 1913435 3229591 := bstep (se 1 (by rfl) ⟨2422193, by rfl⟩ : syracuseStep 3229591 = 4844387) B4844387
theorem B4306121 : Blo 1913435 4306121 := bstep (se 2 (by rfl) ⟨1614795, by rfl⟩ : syracuseStep 4306121 = 3229591) B3229591
theorem B2870747 : Blo 1913435 2870747 := bstep (se 1 (by rfl) ⟨2153060, by rfl⟩ : syracuseStep 2870747 = 4306121) B4306121
theorem B1913831 : Blo 1913435 1913831 := bstep (se 1 (by rfl) ⟨1435373, by rfl⟩ : syracuseStep 1913831 = 2870747) B2870747
theorem B2153065 : Blo 1913435 2153065 := bbase (se 2 (by rfl) ⟨807399, by rfl⟩ : syracuseStep 2153065 = 1614799) (by norm_num)
theorem B2870753 : Blo 1913435 2870753 := bstep (se 2 (by rfl) ⟨1076532, by rfl⟩ : syracuseStep 2870753 = 2153065) B2153065
theorem B1913835 : Blo 1913435 1913835 := bstep (se 1 (by rfl) ⟨1435376, by rfl⟩ : syracuseStep 1913835 = 2870753) B2870753
theorem B4087469 : Blo 1913435 4087469 := bbase (se 3 (by rfl) ⟨766400, by rfl⟩ : syracuseStep 4087469 = 1532801) (by norm_num)
theorem B10899917 : Blo 1913435 10899917 := bstep (se 3 (by rfl) ⟨2043734, by rfl⟩ : syracuseStep 10899917 = 4087469) B4087469
theorem B7266611 : Blo 1913435 7266611 := bstep (se 1 (by rfl) ⟨5449958, by rfl⟩ : syracuseStep 7266611 = 10899917) B10899917
theorem B4844407 : Blo 1913435 4844407 := bstep (se 1 (by rfl) ⟨3633305, by rfl⟩ : syracuseStep 4844407 = 7266611) B7266611
theorem B6459209 : Blo 1913435 6459209 := bstep (se 2 (by rfl) ⟨2422203, by rfl⟩ : syracuseStep 6459209 = 4844407) B4844407
theorem B4306139 : Blo 1913435 4306139 := bstep (se 1 (by rfl) ⟨3229604, by rfl⟩ : syracuseStep 4306139 = 6459209) B6459209
theorem B2870759 : Blo 1913435 2870759 := bstep (se 1 (by rfl) ⟨2153069, by rfl⟩ : syracuseStep 2870759 = 4306139) B4306139
theorem B1913839 : Blo 1913435 1913839 := bstep (se 1 (by rfl) ⟨1435379, by rfl⟩ : syracuseStep 1913839 = 2870759) B2870759
theorem B2870765 : Blo 1913435 2870765 := bbase (se 3 (by rfl) ⟨538268, by rfl⟩ : syracuseStep 2870765 = 1076537) (by norm_num)
theorem B1913843 : Blo 1913435 1913843 := bstep (se 1 (by rfl) ⟨1435382, by rfl⟩ : syracuseStep 1913843 = 2870765) B2870765
theorem B4306157 : Blo 1913435 4306157 := bbase (se 3 (by rfl) ⟨807404, by rfl⟩ : syracuseStep 4306157 = 1614809) (by norm_num)
theorem B2870771 : Blo 1913435 2870771 := bstep (se 1 (by rfl) ⟨2153078, by rfl⟩ : syracuseStep 2870771 = 4306157) B4306157
theorem B1913847 : Blo 1913435 1913847 := bstep (se 1 (by rfl) ⟨1435385, by rfl⟩ : syracuseStep 1913847 = 2870771) B2870771
theorem B2724997 : Blo 1913435 2724997 := bbase (se 4 (by rfl) ⟨255468, by rfl⟩ : syracuseStep 2724997 = 510937) (by norm_num)
theorem B3633329 : Blo 1913435 3633329 := bstep (se 2 (by rfl) ⟨1362498, by rfl⟩ : syracuseStep 3633329 = 2724997) B2724997
theorem B2422219 : Blo 1913435 2422219 := bstep (se 1 (by rfl) ⟨1816664, by rfl⟩ : syracuseStep 2422219 = 3633329) B3633329
theorem B3229625 : Blo 1913435 3229625 := bstep (se 2 (by rfl) ⟨1211109, by rfl⟩ : syracuseStep 3229625 = 2422219) B2422219
theorem B2153083 : Blo 1913435 2153083 := bstep (se 1 (by rfl) ⟨1614812, by rfl⟩ : syracuseStep 2153083 = 3229625) B3229625
theorem B2870777 : Blo 1913435 2870777 := bstep (se 2 (by rfl) ⟨1076541, by rfl⟩ : syracuseStep 2870777 = 2153083) B2153083
theorem B1913851 : Blo 1913435 1913851 := bstep (se 1 (by rfl) ⟨1435388, by rfl⟩ : syracuseStep 1913851 = 2870777) B2870777
theorem B55934165 : Blo 1913435 55934165 := bbase (se 7 (by rfl) ⟨655478, by rfl⟩ : syracuseStep 55934165 = 1310957) (by norm_num)
theorem B149157773 : Blo 1913435 149157773 := bstep (se 3 (by rfl) ⟨27967082, by rfl⟩ : syracuseStep 149157773 = 55934165) B55934165
theorem B99438515 : Blo 1913435 99438515 := bstep (se 1 (by rfl) ⟨74578886, by rfl⟩ : syracuseStep 99438515 = 149157773) B149157773
theorem B66292343 : Blo 1913435 66292343 := bstep (se 1 (by rfl) ⟨49719257, by rfl⟩ : syracuseStep 66292343 = 99438515) B99438515
theorem B44194895 : Blo 1913435 44194895 := bstep (se 1 (by rfl) ⟨33146171, by rfl⟩ : syracuseStep 44194895 = 66292343) B66292343
theorem B29463263 : Blo 1913435 29463263 := bstep (se 1 (by rfl) ⟨22097447, by rfl⟩ : syracuseStep 29463263 = 44194895) B44194895
theorem B19642175 : Blo 1913435 19642175 := bstep (se 1 (by rfl) ⟨14731631, by rfl⟩ : syracuseStep 19642175 = 29463263) B29463263
theorem B13094783 : Blo 1913435 13094783 := bstep (se 1 (by rfl) ⟨9821087, by rfl⟩ : syracuseStep 13094783 = 19642175) B19642175
theorem B8729855 : Blo 1913435 8729855 := bstep (se 1 (by rfl) ⟨6547391, by rfl⟩ : syracuseStep 8729855 = 13094783) B13094783
theorem B5819903 : Blo 1913435 5819903 := bstep (se 1 (by rfl) ⟨4364927, by rfl⟩ : syracuseStep 5819903 = 8729855) B8729855
theorem B3879935 : Blo 1913435 3879935 := bstep (se 1 (by rfl) ⟨2909951, by rfl⟩ : syracuseStep 3879935 = 5819903) B5819903
theorem B2586623 : Blo 1913435 2586623 := bstep (se 1 (by rfl) ⟨1939967, by rfl⟩ : syracuseStep 2586623 = 3879935) B3879935
theorem B27590645 : Blo 1913435 27590645 := bstep (se 5 (by rfl) ⟨1293311, by rfl⟩ : syracuseStep 27590645 = 2586623) B2586623
theorem B73575053 : Blo 1913435 73575053 := bstep (se 3 (by rfl) ⟨13795322, by rfl⟩ : syracuseStep 73575053 = 27590645) B27590645
theorem B49050035 : Blo 1913435 49050035 := bstep (se 1 (by rfl) ⟨36787526, by rfl⟩ : syracuseStep 49050035 = 73575053) B73575053
theorem B32700023 : Blo 1913435 32700023 := bstep (se 1 (by rfl) ⟨24525017, by rfl⟩ : syracuseStep 32700023 = 49050035) B49050035
theorem B21800015 : Blo 1913435 21800015 := bstep (se 1 (by rfl) ⟨16350011, by rfl⟩ : syracuseStep 21800015 = 32700023) B32700023
theorem B14533343 : Blo 1913435 14533343 := bstep (se 1 (by rfl) ⟨10900007, by rfl⟩ : syracuseStep 14533343 = 21800015) B21800015
theorem B9688895 : Blo 1913435 9688895 := bstep (se 1 (by rfl) ⟨7266671, by rfl⟩ : syracuseStep 9688895 = 14533343) B14533343
theorem B6459263 : Blo 1913435 6459263 := bstep (se 1 (by rfl) ⟨4844447, by rfl⟩ : syracuseStep 6459263 = 9688895) B9688895
theorem B4306175 : Blo 1913435 4306175 := bstep (se 1 (by rfl) ⟨3229631, by rfl⟩ : syracuseStep 4306175 = 6459263) B6459263
theorem B2870783 : Blo 1913435 2870783 := bstep (se 1 (by rfl) ⟨2153087, by rfl⟩ : syracuseStep 2870783 = 4306175) B4306175
theorem B1913855 : Blo 1913435 1913855 := bstep (se 1 (by rfl) ⟨1435391, by rfl⟩ : syracuseStep 1913855 = 2870783) B2870783
theorem B2870789 : Blo 1913435 2870789 := bbase (se 4 (by rfl) ⟨269136, by rfl⟩ : syracuseStep 2870789 = 538273) (by norm_num)
theorem B1913859 : Blo 1913435 1913859 := bstep (se 1 (by rfl) ⟨1435394, by rfl⟩ : syracuseStep 1913859 = 2870789) B2870789
theorem B3229645 : Blo 1913435 3229645 := bbase (se 3 (by rfl) ⟨605558, by rfl⟩ : syracuseStep 3229645 = 1211117) (by norm_num)
theorem B4306193 : Blo 1913435 4306193 := bstep (se 2 (by rfl) ⟨1614822, by rfl⟩ : syracuseStep 4306193 = 3229645) B3229645
theorem B2870795 : Blo 1913435 2870795 := bstep (se 1 (by rfl) ⟨2153096, by rfl⟩ : syracuseStep 2870795 = 4306193) B4306193
theorem B1913863 : Blo 1913435 1913863 := bstep (se 1 (by rfl) ⟨1435397, by rfl⟩ : syracuseStep 1913863 = 2870795) B2870795
theorem B2153101 : Blo 1913435 2153101 := bbase (se 3 (by rfl) ⟨403706, by rfl⟩ : syracuseStep 2153101 = 807413) (by norm_num)
theorem B2870801 : Blo 1913435 2870801 := bstep (se 2 (by rfl) ⟨1076550, by rfl⟩ : syracuseStep 2870801 = 2153101) B2153101
theorem B1913867 : Blo 1913435 1913867 := bstep (se 1 (by rfl) ⟨1435400, by rfl⟩ : syracuseStep 1913867 = 2870801) B2870801
theorem B6459317 : Blo 1913435 6459317 := bbase (se 5 (by rfl) ⟨302780, by rfl⟩ : syracuseStep 6459317 = 605561) (by norm_num)
theorem B4306211 : Blo 1913435 4306211 := bstep (se 1 (by rfl) ⟨3229658, by rfl⟩ : syracuseStep 4306211 = 6459317) B6459317
theorem B2870807 : Blo 1913435 2870807 := bstep (se 1 (by rfl) ⟨2153105, by rfl⟩ : syracuseStep 2870807 = 4306211) B4306211
theorem B1913871 : Blo 1913435 1913871 := bstep (se 1 (by rfl) ⟨1435403, by rfl⟩ : syracuseStep 1913871 = 2870807) B2870807
theorem B2870813 : Blo 1913435 2870813 := bbase (se 3 (by rfl) ⟨538277, by rfl⟩ : syracuseStep 2870813 = 1076555) (by norm_num)
theorem B1913875 : Blo 1913435 1913875 := bstep (se 1 (by rfl) ⟨1435406, by rfl⟩ : syracuseStep 1913875 = 2870813) B2870813
theorem B4306229 : Blo 1913435 4306229 := bbase (se 5 (by rfl) ⟨201854, by rfl⟩ : syracuseStep 4306229 = 403709) (by norm_num)
theorem B2870819 : Blo 1913435 2870819 := bstep (se 1 (by rfl) ⟨2153114, by rfl⟩ : syracuseStep 2870819 = 4306229) B4306229
theorem B1913879 : Blo 1913435 1913879 := bstep (se 1 (by rfl) ⟨1435409, by rfl⟩ : syracuseStep 1913879 = 2870819) B2870819
theorem B18394037 : Blo 1913435 18394037 := bbase (se 5 (by rfl) ⟨862220, by rfl⟩ : syracuseStep 18394037 = 1724441) (by norm_num)
theorem B12262691 : Blo 1913435 12262691 := bstep (se 1 (by rfl) ⟨9197018, by rfl⟩ : syracuseStep 12262691 = 18394037) B18394037
theorem B8175127 : Blo 1913435 8175127 := bstep (se 1 (by rfl) ⟨6131345, by rfl⟩ : syracuseStep 8175127 = 12262691) B12262691
theorem B10900169 : Blo 1913435 10900169 := bstep (se 2 (by rfl) ⟨4087563, by rfl⟩ : syracuseStep 10900169 = 8175127) B8175127
theorem B7266779 : Blo 1913435 7266779 := bstep (se 1 (by rfl) ⟨5450084, by rfl⟩ : syracuseStep 7266779 = 10900169) B10900169
theorem B4844519 : Blo 1913435 4844519 := bstep (se 1 (by rfl) ⟨3633389, by rfl⟩ : syracuseStep 4844519 = 7266779) B7266779
theorem B3229679 : Blo 1913435 3229679 := bstep (se 1 (by rfl) ⟨2422259, by rfl⟩ : syracuseStep 3229679 = 4844519) B4844519
theorem B2153119 : Blo 1913435 2153119 := bstep (se 1 (by rfl) ⟨1614839, by rfl⟩ : syracuseStep 2153119 = 3229679) B3229679
theorem B2870825 : Blo 1913435 2870825 := bstep (se 2 (by rfl) ⟨1076559, by rfl⟩ : syracuseStep 2870825 = 2153119) B2153119
theorem B1913883 : Blo 1913435 1913883 := bstep (se 1 (by rfl) ⟨1435412, by rfl⟩ : syracuseStep 1913883 = 2870825) B2870825
theorem B20693333 : Blo 1913435 20693333 := bbase (se 10 (by rfl) ⟨30312, by rfl⟩ : syracuseStep 20693333 = 60625) (by norm_num)
theorem B13795555 : Blo 1913435 13795555 := bstep (se 1 (by rfl) ⟨10346666, by rfl⟩ : syracuseStep 13795555 = 20693333) B20693333
theorem B18394073 : Blo 1913435 18394073 := bstep (se 2 (by rfl) ⟨6897777, by rfl⟩ : syracuseStep 18394073 = 13795555) B13795555
theorem B12262715 : Blo 1913435 12262715 := bstep (se 1 (by rfl) ⟨9197036, by rfl⟩ : syracuseStep 12262715 = 18394073) B18394073
theorem B8175143 : Blo 1913435 8175143 := bstep (se 1 (by rfl) ⟨6131357, by rfl⟩ : syracuseStep 8175143 = 12262715) B12262715
theorem B5450095 : Blo 1913435 5450095 := bstep (se 1 (by rfl) ⟨4087571, by rfl⟩ : syracuseStep 5450095 = 8175143) B8175143
theorem B7266793 : Blo 1913435 7266793 := bstep (se 2 (by rfl) ⟨2725047, by rfl⟩ : syracuseStep 7266793 = 5450095) B5450095
theorem B9689057 : Blo 1913435 9689057 := bstep (se 2 (by rfl) ⟨3633396, by rfl⟩ : syracuseStep 9689057 = 7266793) B7266793
theorem B6459371 : Blo 1913435 6459371 := bstep (se 1 (by rfl) ⟨4844528, by rfl⟩ : syracuseStep 6459371 = 9689057) B9689057
theorem B4306247 : Blo 1913435 4306247 := bstep (se 1 (by rfl) ⟨3229685, by rfl⟩ : syracuseStep 4306247 = 6459371) B6459371
theorem B2870831 : Blo 1913435 2870831 := bstep (se 1 (by rfl) ⟨2153123, by rfl⟩ : syracuseStep 2870831 = 4306247) B4306247
theorem B1913887 : Blo 1913435 1913887 := bstep (se 1 (by rfl) ⟨1435415, by rfl⟩ : syracuseStep 1913887 = 2870831) B2870831
theorem B2870837 : Blo 1913435 2870837 := bbase (se 5 (by rfl) ⟨134570, by rfl⟩ : syracuseStep 2870837 = 269141) (by norm_num)
theorem B1913891 : Blo 1913435 1913891 := bstep (se 1 (by rfl) ⟨1435418, by rfl⟩ : syracuseStep 1913891 = 2870837) B2870837
theorem B4844549 : Blo 1913435 4844549 := bbase (se 4 (by rfl) ⟨454176, by rfl⟩ : syracuseStep 4844549 = 908353) (by norm_num)
theorem B3229699 : Blo 1913435 3229699 := bstep (se 1 (by rfl) ⟨2422274, by rfl⟩ : syracuseStep 3229699 = 4844549) B4844549
theorem B4306265 : Blo 1913435 4306265 := bstep (se 2 (by rfl) ⟨1614849, by rfl⟩ : syracuseStep 4306265 = 3229699) B3229699
theorem B2870843 : Blo 1913435 2870843 := bstep (se 1 (by rfl) ⟨2153132, by rfl⟩ : syracuseStep 2870843 = 4306265) B4306265
theorem B1913895 : Blo 1913435 1913895 := bstep (se 1 (by rfl) ⟨1435421, by rfl⟩ : syracuseStep 1913895 = 2870843) B2870843
theorem B2153137 : Blo 1913435 2153137 := bbase (se 2 (by rfl) ⟨807426, by rfl⟩ : syracuseStep 2153137 = 1614853) (by norm_num)
theorem B2870849 : Blo 1913435 2870849 := bstep (se 2 (by rfl) ⟨1076568, by rfl⟩ : syracuseStep 2870849 = 2153137) B2153137
theorem B1913899 : Blo 1913435 1913899 := bstep (se 1 (by rfl) ⟨1435424, by rfl⟩ : syracuseStep 1913899 = 2870849) B2870849
theorem B7760069 : Blo 1913435 7760069 := bbase (se 4 (by rfl) ⟨727506, by rfl⟩ : syracuseStep 7760069 = 1455013) (by norm_num)
theorem B5173379 : Blo 1913435 5173379 := bstep (se 1 (by rfl) ⟨3880034, by rfl⟩ : syracuseStep 5173379 = 7760069) B7760069
theorem B3448919 : Blo 1913435 3448919 := bstep (se 1 (by rfl) ⟨2586689, by rfl⟩ : syracuseStep 3448919 = 5173379) B5173379
theorem B2299279 : Blo 1913435 2299279 := bstep (se 1 (by rfl) ⟨1724459, by rfl⟩ : syracuseStep 2299279 = 3448919) B3448919
theorem B3065705 : Blo 1913435 3065705 := bstep (se 2 (by rfl) ⟨1149639, by rfl⟩ : syracuseStep 3065705 = 2299279) B2299279
theorem B2043803 : Blo 1913435 2043803 := bstep (se 1 (by rfl) ⟨1532852, by rfl⟩ : syracuseStep 2043803 = 3065705) B3065705
theorem B5450141 : Blo 1913435 5450141 := bstep (se 3 (by rfl) ⟨1021901, by rfl⟩ : syracuseStep 5450141 = 2043803) B2043803
theorem B3633427 : Blo 1913435 3633427 := bstep (se 1 (by rfl) ⟨2725070, by rfl⟩ : syracuseStep 3633427 = 5450141) B5450141
theorem B4844569 : Blo 1913435 4844569 := bstep (se 2 (by rfl) ⟨1816713, by rfl⟩ : syracuseStep 4844569 = 3633427) B3633427
theorem B6459425 : Blo 1913435 6459425 := bstep (se 2 (by rfl) ⟨2422284, by rfl⟩ : syracuseStep 6459425 = 4844569) B4844569
theorem B4306283 : Blo 1913435 4306283 := bstep (se 1 (by rfl) ⟨3229712, by rfl⟩ : syracuseStep 4306283 = 6459425) B6459425
theorem B2870855 : Blo 1913435 2870855 := bstep (se 1 (by rfl) ⟨2153141, by rfl⟩ : syracuseStep 2870855 = 4306283) B4306283
theorem B1913903 : Blo 1913435 1913903 := bstep (se 1 (by rfl) ⟨1435427, by rfl⟩ : syracuseStep 1913903 = 2870855) B2870855
theorem B2870861 : Blo 1913435 2870861 := bbase (se 3 (by rfl) ⟨538286, by rfl⟩ : syracuseStep 2870861 = 1076573) (by norm_num)
theorem B1913907 : Blo 1913435 1913907 := bstep (se 1 (by rfl) ⟨1435430, by rfl⟩ : syracuseStep 1913907 = 2870861) B2870861
theorem B4306301 : Blo 1913435 4306301 := bbase (se 3 (by rfl) ⟨807431, by rfl⟩ : syracuseStep 4306301 = 1614863) (by norm_num)
theorem B2870867 : Blo 1913435 2870867 := bstep (se 1 (by rfl) ⟨2153150, by rfl⟩ : syracuseStep 2870867 = 4306301) B4306301
theorem B1913911 : Blo 1913435 1913911 := bstep (se 1 (by rfl) ⟨1435433, by rfl⟩ : syracuseStep 1913911 = 2870867) B2870867
theorem B3229733 : Blo 1913435 3229733 := bbase (se 4 (by rfl) ⟨302787, by rfl⟩ : syracuseStep 3229733 = 605575) (by norm_num)
theorem B2153155 : Blo 1913435 2153155 := bstep (se 1 (by rfl) ⟨1614866, by rfl⟩ : syracuseStep 2153155 = 3229733) B3229733
theorem B2870873 : Blo 1913435 2870873 := bstep (se 2 (by rfl) ⟨1076577, by rfl⟩ : syracuseStep 2870873 = 2153155) B2153155
theorem B1913915 : Blo 1913435 1913915 := bstep (se 1 (by rfl) ⟨1435436, by rfl⟩ : syracuseStep 1913915 = 2870873) B2870873
theorem B2725093 : Blo 1913435 2725093 := bbase (se 4 (by rfl) ⟨255477, by rfl⟩ : syracuseStep 2725093 = 510955) (by norm_num)
theorem B14533829 : Blo 1913435 14533829 := bstep (se 4 (by rfl) ⟨1362546, by rfl⟩ : syracuseStep 14533829 = 2725093) B2725093
theorem B9689219 : Blo 1913435 9689219 := bstep (se 1 (by rfl) ⟨7266914, by rfl⟩ : syracuseStep 9689219 = 14533829) B14533829
theorem B6459479 : Blo 1913435 6459479 := bstep (se 1 (by rfl) ⟨4844609, by rfl⟩ : syracuseStep 6459479 = 9689219) B9689219
theorem B4306319 : Blo 1913435 4306319 := bstep (se 1 (by rfl) ⟨3229739, by rfl⟩ : syracuseStep 4306319 = 6459479) B6459479
theorem B2870879 : Blo 1913435 2870879 := bstep (se 1 (by rfl) ⟨2153159, by rfl⟩ : syracuseStep 2870879 = 4306319) B4306319
theorem B1913919 : Blo 1913435 1913919 := bstep (se 1 (by rfl) ⟨1435439, by rfl⟩ : syracuseStep 1913919 = 2870879) B2870879
theorem B2870885 : Blo 1913435 2870885 := bbase (se 4 (by rfl) ⟨269145, by rfl⟩ : syracuseStep 2870885 = 538291) (by norm_num)
theorem B1913923 : Blo 1913435 1913923 := bstep (se 1 (by rfl) ⟨1435442, by rfl⟩ : syracuseStep 1913923 = 2870885) B2870885
theorem B2043829 : Blo 1913435 2043829 := bbase (se 5 (by rfl) ⟨95804, by rfl⟩ : syracuseStep 2043829 = 191609) (by norm_num)
theorem B2725105 : Blo 1913435 2725105 := bstep (se 2 (by rfl) ⟨1021914, by rfl⟩ : syracuseStep 2725105 = 2043829) B2043829
theorem B3633473 : Blo 1913435 3633473 := bstep (se 2 (by rfl) ⟨1362552, by rfl⟩ : syracuseStep 3633473 = 2725105) B2725105
theorem B2422315 : Blo 1913435 2422315 := bstep (se 1 (by rfl) ⟨1816736, by rfl⟩ : syracuseStep 2422315 = 3633473) B3633473
theorem B3229753 : Blo 1913435 3229753 := bstep (se 2 (by rfl) ⟨1211157, by rfl⟩ : syracuseStep 3229753 = 2422315) B2422315
theorem B4306337 : Blo 1913435 4306337 := bstep (se 2 (by rfl) ⟨1614876, by rfl⟩ : syracuseStep 4306337 = 3229753) B3229753
theorem B2870891 : Blo 1913435 2870891 := bstep (se 1 (by rfl) ⟨2153168, by rfl⟩ : syracuseStep 2870891 = 4306337) B4306337
theorem B1913927 : Blo 1913435 1913927 := bstep (se 1 (by rfl) ⟨1435445, by rfl⟩ : syracuseStep 1913927 = 2870891) B2870891
theorem B2153173 : Blo 1913435 2153173 := bbase (se 7 (by rfl) ⟨25232, by rfl⟩ : syracuseStep 2153173 = 50465) (by norm_num)
theorem B2870897 : Blo 1913435 2870897 := bstep (se 2 (by rfl) ⟨1076586, by rfl⟩ : syracuseStep 2870897 = 2153173) B2153173
theorem B1913931 : Blo 1913435 1913931 := bstep (se 1 (by rfl) ⟨1435448, by rfl⟩ : syracuseStep 1913931 = 2870897) B2870897
theorem B2422325 : Blo 1913435 2422325 := bbase (se 5 (by rfl) ⟨113546, by rfl⟩ : syracuseStep 2422325 = 227093) (by norm_num)
theorem B6459533 : Blo 1913435 6459533 := bstep (se 3 (by rfl) ⟨1211162, by rfl⟩ : syracuseStep 6459533 = 2422325) B2422325
theorem B4306355 : Blo 1913435 4306355 := bstep (se 1 (by rfl) ⟨3229766, by rfl⟩ : syracuseStep 4306355 = 6459533) B6459533
theorem B2870903 : Blo 1913435 2870903 := bstep (se 1 (by rfl) ⟨2153177, by rfl⟩ : syracuseStep 2870903 = 4306355) B4306355
theorem B1913935 : Blo 1913435 1913935 := bstep (se 1 (by rfl) ⟨1435451, by rfl⟩ : syracuseStep 1913935 = 2870903) B2870903
theorem B2870909 : Blo 1913435 2870909 := bbase (se 3 (by rfl) ⟨538295, by rfl⟩ : syracuseStep 2870909 = 1076591) (by norm_num)
theorem B1913939 : Blo 1913435 1913939 := bstep (se 1 (by rfl) ⟨1435454, by rfl⟩ : syracuseStep 1913939 = 2870909) B2870909
theorem B4306373 : Blo 1913435 4306373 := bbase (se 4 (by rfl) ⟨403722, by rfl⟩ : syracuseStep 4306373 = 807445) (by norm_num)
theorem B2870915 : Blo 1913435 2870915 := bstep (se 1 (by rfl) ⟨2153186, by rfl⟩ : syracuseStep 2870915 = 4306373) B4306373
theorem B1913943 : Blo 1913435 1913943 := bstep (se 1 (by rfl) ⟨1435457, by rfl⟩ : syracuseStep 1913943 = 2870915) B2870915
theorem B31040981 : Blo 1913435 31040981 := bbase (se 7 (by rfl) ⟨363761, by rfl⟩ : syracuseStep 31040981 = 727523) (by norm_num)
theorem B20693987 : Blo 1913435 20693987 := bstep (se 1 (by rfl) ⟨15520490, by rfl⟩ : syracuseStep 20693987 = 31040981) B31040981
theorem B13795991 : Blo 1913435 13795991 := bstep (se 1 (by rfl) ⟨10346993, by rfl⟩ : syracuseStep 13795991 = 20693987) B20693987
theorem B9197327 : Blo 1913435 9197327 := bstep (se 1 (by rfl) ⟨6897995, by rfl⟩ : syracuseStep 9197327 = 13795991) B13795991
theorem B6131551 : Blo 1913435 6131551 := bstep (se 1 (by rfl) ⟨4598663, by rfl⟩ : syracuseStep 6131551 = 9197327) B9197327
theorem B8175401 : Blo 1913435 8175401 := bstep (se 2 (by rfl) ⟨3065775, by rfl⟩ : syracuseStep 8175401 = 6131551) B6131551
theorem B5450267 : Blo 1913435 5450267 := bstep (se 1 (by rfl) ⟨4087700, by rfl⟩ : syracuseStep 5450267 = 8175401) B8175401
theorem B3633511 : Blo 1913435 3633511 := bstep (se 1 (by rfl) ⟨2725133, by rfl⟩ : syracuseStep 3633511 = 5450267) B5450267
theorem B4844681 : Blo 1913435 4844681 := bstep (se 2 (by rfl) ⟨1816755, by rfl⟩ : syracuseStep 4844681 = 3633511) B3633511
theorem B3229787 : Blo 1913435 3229787 := bstep (se 1 (by rfl) ⟨2422340, by rfl⟩ : syracuseStep 3229787 = 4844681) B4844681
theorem B2153191 : Blo 1913435 2153191 := bstep (se 1 (by rfl) ⟨1614893, by rfl⟩ : syracuseStep 2153191 = 3229787) B3229787
theorem B2870921 : Blo 1913435 2870921 := bstep (se 2 (by rfl) ⟨1076595, by rfl⟩ : syracuseStep 2870921 = 2153191) B2153191
theorem B1913947 : Blo 1913435 1913947 := bstep (se 1 (by rfl) ⟨1435460, by rfl⟩ : syracuseStep 1913947 = 2870921) B2870921
theorem B9689381 : Blo 1913435 9689381 := bbase (se 4 (by rfl) ⟨908379, by rfl⟩ : syracuseStep 9689381 = 1816759) (by norm_num)
theorem B6459587 : Blo 1913435 6459587 := bstep (se 1 (by rfl) ⟨4844690, by rfl⟩ : syracuseStep 6459587 = 9689381) B9689381
theorem B4306391 : Blo 1913435 4306391 := bstep (se 1 (by rfl) ⟨3229793, by rfl⟩ : syracuseStep 4306391 = 6459587) B6459587
theorem B2870927 : Blo 1913435 2870927 := bstep (se 1 (by rfl) ⟨2153195, by rfl⟩ : syracuseStep 2870927 = 4306391) B4306391
theorem B1913951 : Blo 1913435 1913951 := bstep (se 1 (by rfl) ⟨1435463, by rfl⟩ : syracuseStep 1913951 = 2870927) B2870927
theorem B2870933 : Blo 1913435 2870933 := bbase (se 6 (by rfl) ⟨67287, by rfl⟩ : syracuseStep 2870933 = 134575) (by norm_num)
theorem B1913955 : Blo 1913435 1913955 := bstep (se 1 (by rfl) ⟨1435466, by rfl⟩ : syracuseStep 1913955 = 2870933) B2870933
theorem B9821621 : Blo 1913435 9821621 := bbase (se 5 (by rfl) ⟨460388, by rfl⟩ : syracuseStep 9821621 = 920777) (by norm_num)
theorem B26190989 : Blo 1913435 26190989 := bstep (se 3 (by rfl) ⟨4910810, by rfl⟩ : syracuseStep 26190989 = 9821621) B9821621
theorem B17460659 : Blo 1913435 17460659 := bstep (se 1 (by rfl) ⟨13095494, by rfl⟩ : syracuseStep 17460659 = 26190989) B26190989
theorem B11640439 : Blo 1913435 11640439 := bstep (se 1 (by rfl) ⟨8730329, by rfl⟩ : syracuseStep 11640439 = 17460659) B17460659
theorem B15520585 : Blo 1913435 15520585 := bstep (se 2 (by rfl) ⟨5820219, by rfl⟩ : syracuseStep 15520585 = 11640439) B11640439
theorem B20694113 : Blo 1913435 20694113 := bstep (se 2 (by rfl) ⟨7760292, by rfl⟩ : syracuseStep 20694113 = 15520585) B15520585
theorem B13796075 : Blo 1913435 13796075 := bstep (se 1 (by rfl) ⟨10347056, by rfl⟩ : syracuseStep 13796075 = 20694113) B20694113
theorem B9197383 : Blo 1913435 9197383 := bstep (se 1 (by rfl) ⟨6898037, by rfl⟩ : syracuseStep 9197383 = 13796075) B13796075
theorem B12263177 : Blo 1913435 12263177 := bstep (se 2 (by rfl) ⟨4598691, by rfl⟩ : syracuseStep 12263177 = 9197383) B9197383
theorem B8175451 : Blo 1913435 8175451 := bstep (se 1 (by rfl) ⟨6131588, by rfl⟩ : syracuseStep 8175451 = 12263177) B12263177
theorem B10900601 : Blo 1913435 10900601 := bstep (se 2 (by rfl) ⟨4087725, by rfl⟩ : syracuseStep 10900601 = 8175451) B8175451
theorem B7267067 : Blo 1913435 7267067 := bstep (se 1 (by rfl) ⟨5450300, by rfl⟩ : syracuseStep 7267067 = 10900601) B10900601
theorem B4844711 : Blo 1913435 4844711 := bstep (se 1 (by rfl) ⟨3633533, by rfl⟩ : syracuseStep 4844711 = 7267067) B7267067
theorem B3229807 : Blo 1913435 3229807 := bstep (se 1 (by rfl) ⟨2422355, by rfl⟩ : syracuseStep 3229807 = 4844711) B4844711
theorem B4306409 : Blo 1913435 4306409 := bstep (se 2 (by rfl) ⟨1614903, by rfl⟩ : syracuseStep 4306409 = 3229807) B3229807
theorem B2870939 : Blo 1913435 2870939 := bstep (se 1 (by rfl) ⟨2153204, by rfl⟩ : syracuseStep 2870939 = 4306409) B4306409
theorem B1913959 : Blo 1913435 1913959 := bstep (se 1 (by rfl) ⟨1435469, by rfl⟩ : syracuseStep 1913959 = 2870939) B2870939
theorem B2153209 : Blo 1913435 2153209 := bbase (se 2 (by rfl) ⟨807453, by rfl⟩ : syracuseStep 2153209 = 1614907) (by norm_num)
theorem B2870945 : Blo 1913435 2870945 := bstep (se 2 (by rfl) ⟨1076604, by rfl⟩ : syracuseStep 2870945 = 2153209) B2153209
theorem B1913963 : Blo 1913435 1913963 := bstep (se 1 (by rfl) ⟨1435472, by rfl⟩ : syracuseStep 1913963 = 2870945) B2870945
theorem B5820245 : Blo 1913435 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B3880163 : Blo 1913435 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B10347101 : Blo 1913435 10347101 := bstep (se 3 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 10347101 = 3880163) B3880163
theorem B6898067 : Blo 1913435 6898067 := bstep (se 1 (by rfl) ⟨5173550, by rfl⟩ : syracuseStep 6898067 = 10347101) B10347101
theorem B4598711 : Blo 1913435 4598711 := bstep (se 1 (by rfl) ⟨3449033, by rfl⟩ : syracuseStep 4598711 = 6898067) B6898067
theorem B3065807 : Blo 1913435 3065807 := bstep (se 1 (by rfl) ⟨2299355, by rfl⟩ : syracuseStep 3065807 = 4598711) B4598711
theorem B8175485 : Blo 1913435 8175485 := bstep (se 3 (by rfl) ⟨1532903, by rfl⟩ : syracuseStep 8175485 = 3065807) B3065807
theorem B5450323 : Blo 1913435 5450323 := bstep (se 1 (by rfl) ⟨4087742, by rfl⟩ : syracuseStep 5450323 = 8175485) B8175485
theorem B7267097 : Blo 1913435 7267097 := bstep (se 2 (by rfl) ⟨2725161, by rfl⟩ : syracuseStep 7267097 = 5450323) B5450323
theorem B4844731 : Blo 1913435 4844731 := bstep (se 1 (by rfl) ⟨3633548, by rfl⟩ : syracuseStep 4844731 = 7267097) B7267097
theorem B6459641 : Blo 1913435 6459641 := bstep (se 2 (by rfl) ⟨2422365, by rfl⟩ : syracuseStep 6459641 = 4844731) B4844731
theorem B4306427 : Blo 1913435 4306427 := bstep (se 1 (by rfl) ⟨3229820, by rfl⟩ : syracuseStep 4306427 = 6459641) B6459641
theorem B2870951 : Blo 1913435 2870951 := bstep (se 1 (by rfl) ⟨2153213, by rfl⟩ : syracuseStep 2870951 = 4306427) B4306427
theorem B1913967 : Blo 1913435 1913967 := bstep (se 1 (by rfl) ⟨1435475, by rfl⟩ : syracuseStep 1913967 = 2870951) B2870951
theorem B2870957 : Blo 1913435 2870957 := bbase (se 3 (by rfl) ⟨538304, by rfl⟩ : syracuseStep 2870957 = 1076609) (by norm_num)
theorem B1913971 : Blo 1913435 1913971 := bstep (se 1 (by rfl) ⟨1435478, by rfl⟩ : syracuseStep 1913971 = 2870957) B2870957
theorem B4306445 : Blo 1913435 4306445 := bbase (se 3 (by rfl) ⟨807458, by rfl⟩ : syracuseStep 4306445 = 1614917) (by norm_num)
theorem B2870963 : Blo 1913435 2870963 := bstep (se 1 (by rfl) ⟨2153222, by rfl⟩ : syracuseStep 2870963 = 4306445) B4306445
theorem B1913975 : Blo 1913435 1913975 := bstep (se 1 (by rfl) ⟨1435481, by rfl⟩ : syracuseStep 1913975 = 2870963) B2870963
theorem B2422381 : Blo 1913435 2422381 := bbase (se 3 (by rfl) ⟨454196, by rfl⟩ : syracuseStep 2422381 = 908393) (by norm_num)
theorem B3229841 : Blo 1913435 3229841 := bstep (se 2 (by rfl) ⟨1211190, by rfl⟩ : syracuseStep 3229841 = 2422381) B2422381
theorem B2153227 : Blo 1913435 2153227 := bstep (se 1 (by rfl) ⟨1614920, by rfl⟩ : syracuseStep 2153227 = 3229841) B3229841
theorem B2870969 : Blo 1913435 2870969 := bstep (se 2 (by rfl) ⟨1076613, by rfl⟩ : syracuseStep 2870969 = 2153227) B2153227
theorem B1913979 : Blo 1913435 1913979 := bstep (se 1 (by rfl) ⟨1435484, by rfl⟩ : syracuseStep 1913979 = 2870969) B2870969
theorem B7760389 : Blo 1913435 7760389 := bbase (se 4 (by rfl) ⟨727536, by rfl⟩ : syracuseStep 7760389 = 1455073) (by norm_num)
theorem B10347185 : Blo 1913435 10347185 := bstep (se 2 (by rfl) ⟨3880194, by rfl⟩ : syracuseStep 10347185 = 7760389) B7760389
theorem B6898123 : Blo 1913435 6898123 := bstep (se 1 (by rfl) ⟨5173592, by rfl⟩ : syracuseStep 6898123 = 10347185) B10347185
theorem B9197497 : Blo 1913435 9197497 := bstep (se 2 (by rfl) ⟨3449061, by rfl⟩ : syracuseStep 9197497 = 6898123) B6898123
theorem B12263329 : Blo 1913435 12263329 := bstep (se 2 (by rfl) ⟨4598748, by rfl⟩ : syracuseStep 12263329 = 9197497) B9197497
theorem B16351105 : Blo 1913435 16351105 := bstep (se 2 (by rfl) ⟨6131664, by rfl⟩ : syracuseStep 16351105 = 12263329) B12263329
theorem B21801473 : Blo 1913435 21801473 := bstep (se 2 (by rfl) ⟨8175552, by rfl⟩ : syracuseStep 21801473 = 16351105) B16351105
theorem B14534315 : Blo 1913435 14534315 := bstep (se 1 (by rfl) ⟨10900736, by rfl⟩ : syracuseStep 14534315 = 21801473) B21801473
theorem B9689543 : Blo 1913435 9689543 := bstep (se 1 (by rfl) ⟨7267157, by rfl⟩ : syracuseStep 9689543 = 14534315) B14534315
theorem B6459695 : Blo 1913435 6459695 := bstep (se 1 (by rfl) ⟨4844771, by rfl⟩ : syracuseStep 6459695 = 9689543) B9689543
theorem B4306463 : Blo 1913435 4306463 := bstep (se 1 (by rfl) ⟨3229847, by rfl⟩ : syracuseStep 4306463 = 6459695) B6459695
theorem B2870975 : Blo 1913435 2870975 := bstep (se 1 (by rfl) ⟨2153231, by rfl⟩ : syracuseStep 2870975 = 4306463) B4306463
theorem B1913983 : Blo 1913435 1913983 := bstep (se 1 (by rfl) ⟨1435487, by rfl⟩ : syracuseStep 1913983 = 2870975) B2870975
theorem B2870981 : Blo 1913435 2870981 := bbase (se 4 (by rfl) ⟨269154, by rfl⟩ : syracuseStep 2870981 = 538309) (by norm_num)
theorem B1913987 : Blo 1913435 1913987 := bstep (se 1 (by rfl) ⟨1435490, by rfl⟩ : syracuseStep 1913987 = 2870981) B2870981
theorem B3229861 : Blo 1913435 3229861 := bbase (se 4 (by rfl) ⟨302799, by rfl⟩ : syracuseStep 3229861 = 605599) (by norm_num)
theorem B4306481 : Blo 1913435 4306481 := bstep (se 2 (by rfl) ⟨1614930, by rfl⟩ : syracuseStep 4306481 = 3229861) B3229861
theorem B2870987 : Blo 1913435 2870987 := bstep (se 1 (by rfl) ⟨2153240, by rfl⟩ : syracuseStep 2870987 = 4306481) B4306481
theorem B1913991 : Blo 1913435 1913991 := bstep (se 1 (by rfl) ⟨1435493, by rfl⟩ : syracuseStep 1913991 = 2870987) B2870987
theorem B2153245 : Blo 1913435 2153245 := bbase (se 3 (by rfl) ⟨403733, by rfl⟩ : syracuseStep 2153245 = 807467) (by norm_num)
theorem B2870993 : Blo 1913435 2870993 := bstep (se 2 (by rfl) ⟨1076622, by rfl⟩ : syracuseStep 2870993 = 2153245) B2153245
theorem B1913995 : Blo 1913435 1913995 := bstep (se 1 (by rfl) ⟨1435496, by rfl⟩ : syracuseStep 1913995 = 2870993) B2870993
theorem B6459749 : Blo 1913435 6459749 := bbase (se 4 (by rfl) ⟨605601, by rfl⟩ : syracuseStep 6459749 = 1211203) (by norm_num)
theorem B4306499 : Blo 1913435 4306499 := bstep (se 1 (by rfl) ⟨3229874, by rfl⟩ : syracuseStep 4306499 = 6459749) B6459749
theorem B2870999 : Blo 1913435 2870999 := bstep (se 1 (by rfl) ⟨2153249, by rfl⟩ : syracuseStep 2870999 = 4306499) B4306499
theorem B1913999 : Blo 1913435 1913999 := bstep (se 1 (by rfl) ⟨1435499, by rfl⟩ : syracuseStep 1913999 = 2870999) B2870999
theorem B2871005 : Blo 1913435 2871005 := bbase (se 3 (by rfl) ⟨538313, by rfl⟩ : syracuseStep 2871005 = 1076627) (by norm_num)
theorem B1914003 : Blo 1913435 1914003 := bstep (se 1 (by rfl) ⟨1435502, by rfl⟩ : syracuseStep 1914003 = 2871005) B2871005
theorem B4306517 : Blo 1913435 4306517 := bbase (se 8 (by rfl) ⟨25233, by rfl⟩ : syracuseStep 4306517 = 50467) (by norm_num)
theorem B2871011 : Blo 1913435 2871011 := bstep (se 1 (by rfl) ⟨2153258, by rfl⟩ : syracuseStep 2871011 = 4306517) B4306517
theorem B1914007 : Blo 1913435 1914007 := bstep (se 1 (by rfl) ⟨1435505, by rfl⟩ : syracuseStep 1914007 = 2871011) B2871011
theorem B4087837 : Blo 1913435 4087837 := bbase (se 3 (by rfl) ⟨766469, by rfl⟩ : syracuseStep 4087837 = 1532939) (by norm_num)
theorem B5450449 : Blo 1913435 5450449 := bstep (se 2 (by rfl) ⟨2043918, by rfl⟩ : syracuseStep 5450449 = 4087837) B4087837
theorem B7267265 : Blo 1913435 7267265 := bstep (se 2 (by rfl) ⟨2725224, by rfl⟩ : syracuseStep 7267265 = 5450449) B5450449
theorem B4844843 : Blo 1913435 4844843 := bstep (se 1 (by rfl) ⟨3633632, by rfl⟩ : syracuseStep 4844843 = 7267265) B7267265
theorem B3229895 : Blo 1913435 3229895 := bstep (se 1 (by rfl) ⟨2422421, by rfl⟩ : syracuseStep 3229895 = 4844843) B4844843
theorem B2153263 : Blo 1913435 2153263 := bstep (se 1 (by rfl) ⟨1614947, by rfl⟩ : syracuseStep 2153263 = 3229895) B3229895
theorem B2871017 : Blo 1913435 2871017 := bstep (se 2 (by rfl) ⟨1076631, by rfl⟩ : syracuseStep 2871017 = 2153263) B2153263
theorem B1914011 : Blo 1913435 1914011 := bstep (se 1 (by rfl) ⟨1435508, by rfl⟩ : syracuseStep 1914011 = 2871017) B2871017
theorem B2455477 : Blo 1913435 2455477 := bbase (se 5 (by rfl) ⟨115100, by rfl⟩ : syracuseStep 2455477 = 230201) (by norm_num)
theorem B13095877 : Blo 1913435 13095877 := bstep (se 4 (by rfl) ⟨1227738, by rfl⟩ : syracuseStep 13095877 = 2455477) B2455477
theorem B17461169 : Blo 1913435 17461169 := bstep (se 2 (by rfl) ⟨6547938, by rfl⟩ : syracuseStep 17461169 = 13095877) B13095877
theorem B11640779 : Blo 1913435 11640779 := bstep (se 1 (by rfl) ⟨8730584, by rfl⟩ : syracuseStep 11640779 = 17461169) B17461169
theorem B7760519 : Blo 1913435 7760519 := bstep (se 1 (by rfl) ⟨5820389, by rfl⟩ : syracuseStep 7760519 = 11640779) B11640779
theorem B5173679 : Blo 1913435 5173679 := bstep (se 1 (by rfl) ⟨3880259, by rfl⟩ : syracuseStep 5173679 = 7760519) B7760519
theorem B13796477 : Blo 1913435 13796477 := bstep (se 3 (by rfl) ⟨2586839, by rfl⟩ : syracuseStep 13796477 = 5173679) B5173679
theorem B9197651 : Blo 1913435 9197651 := bstep (se 1 (by rfl) ⟨6898238, by rfl⟩ : syracuseStep 9197651 = 13796477) B13796477
theorem B24527069 : Blo 1913435 24527069 := bstep (se 3 (by rfl) ⟨4598825, by rfl⟩ : syracuseStep 24527069 = 9197651) B9197651
theorem B16351379 : Blo 1913435 16351379 := bstep (se 1 (by rfl) ⟨12263534, by rfl⟩ : syracuseStep 16351379 = 24527069) B24527069
theorem B10900919 : Blo 1913435 10900919 := bstep (se 1 (by rfl) ⟨8175689, by rfl⟩ : syracuseStep 10900919 = 16351379) B16351379
theorem B7267279 : Blo 1913435 7267279 := bstep (se 1 (by rfl) ⟨5450459, by rfl⟩ : syracuseStep 7267279 = 10900919) B10900919
theorem B9689705 : Blo 1913435 9689705 := bstep (se 2 (by rfl) ⟨3633639, by rfl⟩ : syracuseStep 9689705 = 7267279) B7267279
theorem B6459803 : Blo 1913435 6459803 := bstep (se 1 (by rfl) ⟨4844852, by rfl⟩ : syracuseStep 6459803 = 9689705) B9689705
theorem B4306535 : Blo 1913435 4306535 := bstep (se 1 (by rfl) ⟨3229901, by rfl⟩ : syracuseStep 4306535 = 6459803) B6459803
theorem B2871023 : Blo 1913435 2871023 := bstep (se 1 (by rfl) ⟨2153267, by rfl⟩ : syracuseStep 2871023 = 4306535) B4306535
theorem B1914015 : Blo 1913435 1914015 := bstep (se 1 (by rfl) ⟨1435511, by rfl⟩ : syracuseStep 1914015 = 2871023) B2871023
theorem B2871029 : Blo 1913435 2871029 := bbase (se 5 (by rfl) ⟨134579, by rfl⟩ : syracuseStep 2871029 = 269159) (by norm_num)
theorem B1914019 : Blo 1913435 1914019 := bstep (se 1 (by rfl) ⟨1435514, by rfl⟩ : syracuseStep 1914019 = 2871029) B2871029
theorem B2330797 : Blo 1913435 2330797 := bbase (se 3 (by rfl) ⟨437024, by rfl⟩ : syracuseStep 2330797 = 874049) (by norm_num)
theorem B3107729 : Blo 1913435 3107729 := bstep (se 2 (by rfl) ⟨1165398, by rfl⟩ : syracuseStep 3107729 = 2330797) B2330797
theorem B2071819 : Blo 1913435 2071819 := bstep (se 1 (by rfl) ⟨1553864, by rfl⟩ : syracuseStep 2071819 = 3107729) B3107729
theorem B2762425 : Blo 1913435 2762425 := bstep (se 2 (by rfl) ⟨1035909, by rfl⟩ : syracuseStep 2762425 = 2071819) B2071819
theorem B3683233 : Blo 1913435 3683233 := bstep (se 2 (by rfl) ⟨1381212, by rfl⟩ : syracuseStep 3683233 = 2762425) B2762425
theorem B4910977 : Blo 1913435 4910977 := bstep (se 2 (by rfl) ⟨1841616, by rfl⟩ : syracuseStep 4910977 = 3683233) B3683233
theorem B6547969 : Blo 1913435 6547969 := bstep (se 2 (by rfl) ⟨2455488, by rfl⟩ : syracuseStep 6547969 = 4910977) B4910977
theorem B8730625 : Blo 1913435 8730625 := bstep (se 2 (by rfl) ⟨3273984, by rfl⟩ : syracuseStep 8730625 = 6547969) B6547969
theorem B11640833 : Blo 1913435 11640833 := bstep (se 2 (by rfl) ⟨4365312, by rfl⟩ : syracuseStep 11640833 = 8730625) B8730625
theorem B7760555 : Blo 1913435 7760555 := bstep (se 1 (by rfl) ⟨5820416, by rfl⟩ : syracuseStep 7760555 = 11640833) B11640833
theorem B5173703 : Blo 1913435 5173703 := bstep (se 1 (by rfl) ⟨3880277, by rfl⟩ : syracuseStep 5173703 = 7760555) B7760555
theorem B3449135 : Blo 1913435 3449135 := bstep (se 1 (by rfl) ⟨2586851, by rfl⟩ : syracuseStep 3449135 = 5173703) B5173703
theorem B2299423 : Blo 1913435 2299423 := bstep (se 1 (by rfl) ⟨1724567, by rfl⟩ : syracuseStep 2299423 = 3449135) B3449135
theorem B3065897 : Blo 1913435 3065897 := bstep (se 2 (by rfl) ⟨1149711, by rfl⟩ : syracuseStep 3065897 = 2299423) B2299423
theorem B8175725 : Blo 1913435 8175725 := bstep (se 3 (by rfl) ⟨1532948, by rfl⟩ : syracuseStep 8175725 = 3065897) B3065897
theorem B5450483 : Blo 1913435 5450483 := bstep (se 1 (by rfl) ⟨4087862, by rfl⟩ : syracuseStep 5450483 = 8175725) B8175725
theorem B3633655 : Blo 1913435 3633655 := bstep (se 1 (by rfl) ⟨2725241, by rfl⟩ : syracuseStep 3633655 = 5450483) B5450483
theorem B4844873 : Blo 1913435 4844873 := bstep (se 2 (by rfl) ⟨1816827, by rfl⟩ : syracuseStep 4844873 = 3633655) B3633655
theorem B3229915 : Blo 1913435 3229915 := bstep (se 1 (by rfl) ⟨2422436, by rfl⟩ : syracuseStep 3229915 = 4844873) B4844873
theorem B4306553 : Blo 1913435 4306553 := bstep (se 2 (by rfl) ⟨1614957, by rfl⟩ : syracuseStep 4306553 = 3229915) B3229915
theorem B2871035 : Blo 1913435 2871035 := bstep (se 1 (by rfl) ⟨2153276, by rfl⟩ : syracuseStep 2871035 = 4306553) B4306553
theorem B1914023 : Blo 1913435 1914023 := bstep (se 1 (by rfl) ⟨1435517, by rfl⟩ : syracuseStep 1914023 = 2871035) B2871035
theorem B2153281 : Blo 1913435 2153281 := bbase (se 2 (by rfl) ⟨807480, by rfl⟩ : syracuseStep 2153281 = 1614961) (by norm_num)
theorem B2871041 : Blo 1913435 2871041 := bstep (se 2 (by rfl) ⟨1076640, by rfl⟩ : syracuseStep 2871041 = 2153281) B2153281
theorem B1914027 : Blo 1913435 1914027 := bstep (se 1 (by rfl) ⟨1435520, by rfl⟩ : syracuseStep 1914027 = 2871041) B2871041
theorem B4844893 : Blo 1913435 4844893 := bbase (se 3 (by rfl) ⟨908417, by rfl⟩ : syracuseStep 4844893 = 1816835) (by norm_num)
theorem B6459857 : Blo 1913435 6459857 := bstep (se 2 (by rfl) ⟨2422446, by rfl⟩ : syracuseStep 6459857 = 4844893) B4844893
theorem B4306571 : Blo 1913435 4306571 := bstep (se 1 (by rfl) ⟨3229928, by rfl⟩ : syracuseStep 4306571 = 6459857) B6459857
theorem B2871047 : Blo 1913435 2871047 := bstep (se 1 (by rfl) ⟨2153285, by rfl⟩ : syracuseStep 2871047 = 4306571) B4306571
theorem B1914031 : Blo 1913435 1914031 := bstep (se 1 (by rfl) ⟨1435523, by rfl⟩ : syracuseStep 1914031 = 2871047) B2871047
theorem B2871053 : Blo 1913435 2871053 := bbase (se 3 (by rfl) ⟨538322, by rfl⟩ : syracuseStep 2871053 = 1076645) (by norm_num)
theorem B1914035 : Blo 1913435 1914035 := bstep (se 1 (by rfl) ⟨1435526, by rfl⟩ : syracuseStep 1914035 = 2871053) B2871053
theorem B4306589 : Blo 1913435 4306589 := bbase (se 3 (by rfl) ⟨807485, by rfl⟩ : syracuseStep 4306589 = 1614971) (by norm_num)
theorem B2871059 : Blo 1913435 2871059 := bstep (se 1 (by rfl) ⟨2153294, by rfl⟩ : syracuseStep 2871059 = 4306589) B4306589
theorem B1914039 : Blo 1913435 1914039 := bstep (se 1 (by rfl) ⟨1435529, by rfl⟩ : syracuseStep 1914039 = 2871059) B2871059
theorem B3229949 : Blo 1913435 3229949 := bbase (se 3 (by rfl) ⟨605615, by rfl⟩ : syracuseStep 3229949 = 1211231) (by norm_num)
theorem B2153299 : Blo 1913435 2153299 := bstep (se 1 (by rfl) ⟨1614974, by rfl⟩ : syracuseStep 2153299 = 3229949) B3229949
theorem B2871065 : Blo 1913435 2871065 := bstep (se 2 (by rfl) ⟨1076649, by rfl⟩ : syracuseStep 2871065 = 2153299) B2153299
theorem B1914043 : Blo 1913435 1914043 := bstep (se 1 (by rfl) ⟨1435532, by rfl⟩ : syracuseStep 1914043 = 2871065) B2871065
theorem B3880325 : Blo 1913435 3880325 := bbase (se 4 (by rfl) ⟨363780, by rfl⟩ : syracuseStep 3880325 = 727561) (by norm_num)
theorem B10347533 : Blo 1913435 10347533 := bstep (se 3 (by rfl) ⟨1940162, by rfl⟩ : syracuseStep 10347533 = 3880325) B3880325
theorem B6898355 : Blo 1913435 6898355 := bstep (se 1 (by rfl) ⟨5173766, by rfl⟩ : syracuseStep 6898355 = 10347533) B10347533
theorem B4598903 : Blo 1913435 4598903 := bstep (se 1 (by rfl) ⟨3449177, by rfl⟩ : syracuseStep 4598903 = 6898355) B6898355
theorem B3065935 : Blo 1913435 3065935 := bstep (se 1 (by rfl) ⟨2299451, by rfl⟩ : syracuseStep 3065935 = 4598903) B4598903
theorem B4087913 : Blo 1913435 4087913 := bstep (se 2 (by rfl) ⟨1532967, by rfl⟩ : syracuseStep 4087913 = 3065935) B3065935
theorem B10901101 : Blo 1913435 10901101 := bstep (se 3 (by rfl) ⟨2043956, by rfl⟩ : syracuseStep 10901101 = 4087913) B4087913
theorem B14534801 : Blo 1913435 14534801 := bstep (se 2 (by rfl) ⟨5450550, by rfl⟩ : syracuseStep 14534801 = 10901101) B10901101
theorem B9689867 : Blo 1913435 9689867 := bstep (se 1 (by rfl) ⟨7267400, by rfl⟩ : syracuseStep 9689867 = 14534801) B14534801
theorem B6459911 : Blo 1913435 6459911 := bstep (se 1 (by rfl) ⟨4844933, by rfl⟩ : syracuseStep 6459911 = 9689867) B9689867
theorem B4306607 : Blo 1913435 4306607 := bstep (se 1 (by rfl) ⟨3229955, by rfl⟩ : syracuseStep 4306607 = 6459911) B6459911
theorem B2871071 : Blo 1913435 2871071 := bstep (se 1 (by rfl) ⟨2153303, by rfl⟩ : syracuseStep 2871071 = 4306607) B4306607
theorem B1914047 : Blo 1913435 1914047 := bstep (se 1 (by rfl) ⟨1435535, by rfl⟩ : syracuseStep 1914047 = 2871071) B2871071
theorem B2871077 : Blo 1913435 2871077 := bbase (se 4 (by rfl) ⟨269163, by rfl⟩ : syracuseStep 2871077 = 538327) (by norm_num)
theorem B1914051 : Blo 1913435 1914051 := bstep (se 1 (by rfl) ⟨1435538, by rfl⟩ : syracuseStep 1914051 = 2871077) B2871077
theorem B2422477 : Blo 1913435 2422477 := bbase (se 3 (by rfl) ⟨454214, by rfl⟩ : syracuseStep 2422477 = 908429) (by norm_num)
theorem B3229969 : Blo 1913435 3229969 := bstep (se 2 (by rfl) ⟨1211238, by rfl⟩ : syracuseStep 3229969 = 2422477) B2422477
theorem B4306625 : Blo 1913435 4306625 := bstep (se 2 (by rfl) ⟨1614984, by rfl⟩ : syracuseStep 4306625 = 3229969) B3229969
theorem B2871083 : Blo 1913435 2871083 := bstep (se 1 (by rfl) ⟨2153312, by rfl⟩ : syracuseStep 2871083 = 4306625) B4306625
theorem B1914055 : Blo 1913435 1914055 := bstep (se 1 (by rfl) ⟨1435541, by rfl⟩ : syracuseStep 1914055 = 2871083) B2871083
theorem B2153317 : Blo 1913435 2153317 := bbase (se 4 (by rfl) ⟨201873, by rfl⟩ : syracuseStep 2153317 = 403747) (by norm_num)
theorem B2871089 : Blo 1913435 2871089 := bstep (se 2 (by rfl) ⟨1076658, by rfl⟩ : syracuseStep 2871089 = 2153317) B2153317
theorem B1914059 : Blo 1913435 1914059 := bstep (se 1 (by rfl) ⟨1435544, by rfl⟩ : syracuseStep 1914059 = 2871089) B2871089
theorem B5450597 : Blo 1913435 5450597 := bbase (se 4 (by rfl) ⟨510993, by rfl⟩ : syracuseStep 5450597 = 1021987) (by norm_num)
theorem B3633731 : Blo 1913435 3633731 := bstep (se 1 (by rfl) ⟨2725298, by rfl⟩ : syracuseStep 3633731 = 5450597) B5450597
theorem B2422487 : Blo 1913435 2422487 := bstep (se 1 (by rfl) ⟨1816865, by rfl⟩ : syracuseStep 2422487 = 3633731) B3633731
theorem B6459965 : Blo 1913435 6459965 := bstep (se 3 (by rfl) ⟨1211243, by rfl⟩ : syracuseStep 6459965 = 2422487) B2422487
theorem B4306643 : Blo 1913435 4306643 := bstep (se 1 (by rfl) ⟨3229982, by rfl⟩ : syracuseStep 4306643 = 6459965) B6459965
theorem B2871095 : Blo 1913435 2871095 := bstep (se 1 (by rfl) ⟨2153321, by rfl⟩ : syracuseStep 2871095 = 4306643) B4306643
theorem B1914063 : Blo 1913435 1914063 := bstep (se 1 (by rfl) ⟨1435547, by rfl⟩ : syracuseStep 1914063 = 2871095) B2871095
theorem B2871101 : Blo 1913435 2871101 := bbase (se 3 (by rfl) ⟨538331, by rfl⟩ : syracuseStep 2871101 = 1076663) (by norm_num)
theorem B1914067 : Blo 1913435 1914067 := bstep (se 1 (by rfl) ⟨1435550, by rfl⟩ : syracuseStep 1914067 = 2871101) B2871101
theorem B4306661 : Blo 1913435 4306661 := bbase (se 4 (by rfl) ⟨403749, by rfl⟩ : syracuseStep 4306661 = 807499) (by norm_num)
theorem B2871107 : Blo 1913435 2871107 := bstep (se 1 (by rfl) ⟨2153330, by rfl⟩ : syracuseStep 2871107 = 4306661) B4306661
theorem B1914071 : Blo 1913435 1914071 := bstep (se 1 (by rfl) ⟨1435553, by rfl⟩ : syracuseStep 1914071 = 2871107) B2871107
theorem B4845005 : Blo 1913435 4845005 := bbase (se 3 (by rfl) ⟨908438, by rfl⟩ : syracuseStep 4845005 = 1816877) (by norm_num)
theorem B3230003 : Blo 1913435 3230003 := bstep (se 1 (by rfl) ⟨2422502, by rfl⟩ : syracuseStep 3230003 = 4845005) B4845005
theorem B2153335 : Blo 1913435 2153335 := bstep (se 1 (by rfl) ⟨1615001, by rfl⟩ : syracuseStep 2153335 = 3230003) B3230003
theorem B2871113 : Blo 1913435 2871113 := bstep (se 2 (by rfl) ⟨1076667, by rfl⟩ : syracuseStep 2871113 = 2153335) B2153335
theorem B1914075 : Blo 1913435 1914075 := bstep (se 1 (by rfl) ⟨1435556, by rfl⟩ : syracuseStep 1914075 = 2871113) B2871113
theorem B4598981 : Blo 1913435 4598981 := bbase (se 4 (by rfl) ⟨431154, by rfl⟩ : syracuseStep 4598981 = 862309) (by norm_num)
theorem B3065987 : Blo 1913435 3065987 := bstep (se 1 (by rfl) ⟨2299490, by rfl⟩ : syracuseStep 3065987 = 4598981) B4598981
theorem B2043991 : Blo 1913435 2043991 := bstep (se 1 (by rfl) ⟨1532993, by rfl⟩ : syracuseStep 2043991 = 3065987) B3065987
theorem B2725321 : Blo 1913435 2725321 := bstep (se 2 (by rfl) ⟨1021995, by rfl⟩ : syracuseStep 2725321 = 2043991) B2043991
theorem B3633761 : Blo 1913435 3633761 := bstep (se 2 (by rfl) ⟨1362660, by rfl⟩ : syracuseStep 3633761 = 2725321) B2725321
theorem B9690029 : Blo 1913435 9690029 := bstep (se 3 (by rfl) ⟨1816880, by rfl⟩ : syracuseStep 9690029 = 3633761) B3633761
theorem B6460019 : Blo 1913435 6460019 := bstep (se 1 (by rfl) ⟨4845014, by rfl⟩ : syracuseStep 6460019 = 9690029) B9690029
theorem B4306679 : Blo 1913435 4306679 := bstep (se 1 (by rfl) ⟨3230009, by rfl⟩ : syracuseStep 4306679 = 6460019) B6460019
theorem B2871119 : Blo 1913435 2871119 := bstep (se 1 (by rfl) ⟨2153339, by rfl⟩ : syracuseStep 2871119 = 4306679) B4306679
theorem B1914079 : Blo 1913435 1914079 := bstep (se 1 (by rfl) ⟨1435559, by rfl⟩ : syracuseStep 1914079 = 2871119) B2871119
theorem B2871125 : Blo 1913435 2871125 := bbase (se 9 (by rfl) ⟨8411, by rfl⟩ : syracuseStep 2871125 = 16823) (by norm_num)
theorem B1914083 : Blo 1913435 1914083 := bstep (se 1 (by rfl) ⟨1435562, by rfl⟩ : syracuseStep 1914083 = 2871125) B2871125
theorem B3274093 : Blo 1913435 3274093 := bbase (se 3 (by rfl) ⟨613892, by rfl⟩ : syracuseStep 3274093 = 1227785) (by norm_num)
theorem B4365457 : Blo 1913435 4365457 := bstep (se 2 (by rfl) ⟨1637046, by rfl⟩ : syracuseStep 4365457 = 3274093) B3274093
theorem B23282437 : Blo 1913435 23282437 := bstep (se 4 (by rfl) ⟨2182728, by rfl⟩ : syracuseStep 23282437 = 4365457) B4365457
theorem B31043249 : Blo 1913435 31043249 := bstep (se 2 (by rfl) ⟨11641218, by rfl⟩ : syracuseStep 31043249 = 23282437) B23282437
theorem B20695499 : Blo 1913435 20695499 := bstep (se 1 (by rfl) ⟨15521624, by rfl⟩ : syracuseStep 20695499 = 31043249) B31043249
theorem B13796999 : Blo 1913435 13796999 := bstep (se 1 (by rfl) ⟨10347749, by rfl⟩ : syracuseStep 13796999 = 20695499) B20695499
theorem B9197999 : Blo 1913435 9197999 := bstep (se 1 (by rfl) ⟨6898499, by rfl⟩ : syracuseStep 9197999 = 13796999) B13796999
theorem B6131999 : Blo 1913435 6131999 := bstep (se 1 (by rfl) ⟨4598999, by rfl⟩ : syracuseStep 6131999 = 9197999) B9197999
theorem B4087999 : Blo 1913435 4087999 := bstep (se 1 (by rfl) ⟨3065999, by rfl⟩ : syracuseStep 4087999 = 6131999) B6131999
theorem B5450665 : Blo 1913435 5450665 := bstep (se 2 (by rfl) ⟨2043999, by rfl⟩ : syracuseStep 5450665 = 4087999) B4087999
theorem B7267553 : Blo 1913435 7267553 := bstep (se 2 (by rfl) ⟨2725332, by rfl⟩ : syracuseStep 7267553 = 5450665) B5450665
theorem B4845035 : Blo 1913435 4845035 := bstep (se 1 (by rfl) ⟨3633776, by rfl⟩ : syracuseStep 4845035 = 7267553) B7267553
theorem B3230023 : Blo 1913435 3230023 := bstep (se 1 (by rfl) ⟨2422517, by rfl⟩ : syracuseStep 3230023 = 4845035) B4845035
theorem B4306697 : Blo 1913435 4306697 := bstep (se 2 (by rfl) ⟨1615011, by rfl⟩ : syracuseStep 4306697 = 3230023) B3230023
theorem B2871131 : Blo 1913435 2871131 := bstep (se 1 (by rfl) ⟨2153348, by rfl⟩ : syracuseStep 2871131 = 4306697) B4306697
theorem B1914087 : Blo 1913435 1914087 := bstep (se 1 (by rfl) ⟨1435565, by rfl⟩ : syracuseStep 1914087 = 2871131) B2871131
theorem B2153353 : Blo 1913435 2153353 := bbase (se 2 (by rfl) ⟨807507, by rfl⟩ : syracuseStep 2153353 = 1615015) (by norm_num)
theorem B2871137 : Blo 1913435 2871137 := bstep (se 2 (by rfl) ⟨1076676, by rfl⟩ : syracuseStep 2871137 = 2153353) B2153353
theorem B1914091 : Blo 1913435 1914091 := bstep (se 1 (by rfl) ⟨1435568, by rfl⟩ : syracuseStep 1914091 = 2871137) B2871137
theorem B3933365 : Blo 1913435 3933365 := bbase (se 5 (by rfl) ⟨184376, by rfl⟩ : syracuseStep 3933365 = 368753) (by norm_num)
theorem B10488973 : Blo 1913435 10488973 := bstep (se 3 (by rfl) ⟨1966682, by rfl⟩ : syracuseStep 10488973 = 3933365) B3933365
theorem B13985297 : Blo 1913435 13985297 := bstep (se 2 (by rfl) ⟨5244486, by rfl⟩ : syracuseStep 13985297 = 10488973) B10488973
theorem B9323531 : Blo 1913435 9323531 := bstep (se 1 (by rfl) ⟨6992648, by rfl⟩ : syracuseStep 9323531 = 13985297) B13985297
theorem B6215687 : Blo 1913435 6215687 := bstep (se 1 (by rfl) ⟨4661765, by rfl⟩ : syracuseStep 6215687 = 9323531) B9323531
theorem B4143791 : Blo 1913435 4143791 := bstep (se 1 (by rfl) ⟨3107843, by rfl⟩ : syracuseStep 4143791 = 6215687) B6215687
theorem B2762527 : Blo 1913435 2762527 := bstep (se 1 (by rfl) ⟨2071895, by rfl⟩ : syracuseStep 2762527 = 4143791) B4143791
theorem B3683369 : Blo 1913435 3683369 := bstep (se 2 (by rfl) ⟨1381263, by rfl⟩ : syracuseStep 3683369 = 2762527) B2762527
theorem B9822317 : Blo 1913435 9822317 := bstep (se 3 (by rfl) ⟨1841684, by rfl⟩ : syracuseStep 9822317 = 3683369) B3683369
theorem B26192845 : Blo 1913435 26192845 := bstep (se 3 (by rfl) ⟨4911158, by rfl⟩ : syracuseStep 26192845 = 9822317) B9822317
theorem B34923793 : Blo 1913435 34923793 := bstep (se 2 (by rfl) ⟨13096422, by rfl⟩ : syracuseStep 34923793 = 26192845) B26192845
theorem B46565057 : Blo 1913435 46565057 := bstep (se 2 (by rfl) ⟨17461896, by rfl⟩ : syracuseStep 46565057 = 34923793) B34923793
theorem B124173485 : Blo 1913435 124173485 := bstep (se 3 (by rfl) ⟨23282528, by rfl⟩ : syracuseStep 124173485 = 46565057) B46565057
theorem B82782323 : Blo 1913435 82782323 := bstep (se 1 (by rfl) ⟨62086742, by rfl⟩ : syracuseStep 82782323 = 124173485) B124173485
theorem B55188215 : Blo 1913435 55188215 := bstep (se 1 (by rfl) ⟨41391161, by rfl⟩ : syracuseStep 55188215 = 82782323) B82782323
theorem B36792143 : Blo 1913435 36792143 := bstep (se 1 (by rfl) ⟨27594107, by rfl⟩ : syracuseStep 36792143 = 55188215) B55188215
theorem B24528095 : Blo 1913435 24528095 := bstep (se 1 (by rfl) ⟨18396071, by rfl⟩ : syracuseStep 24528095 = 36792143) B36792143
theorem B16352063 : Blo 1913435 16352063 := bstep (se 1 (by rfl) ⟨12264047, by rfl⟩ : syracuseStep 16352063 = 24528095) B24528095
theorem B10901375 : Blo 1913435 10901375 := bstep (se 1 (by rfl) ⟨8176031, by rfl⟩ : syracuseStep 10901375 = 16352063) B16352063
theorem B7267583 : Blo 1913435 7267583 := bstep (se 1 (by rfl) ⟨5450687, by rfl⟩ : syracuseStep 7267583 = 10901375) B10901375
theorem B4845055 : Blo 1913435 4845055 := bstep (se 1 (by rfl) ⟨3633791, by rfl⟩ : syracuseStep 4845055 = 7267583) B7267583
theorem B6460073 : Blo 1913435 6460073 := bstep (se 2 (by rfl) ⟨2422527, by rfl⟩ : syracuseStep 6460073 = 4845055) B4845055
theorem B4306715 : Blo 1913435 4306715 := bstep (se 1 (by rfl) ⟨3230036, by rfl⟩ : syracuseStep 4306715 = 6460073) B6460073
theorem B2871143 : Blo 1913435 2871143 := bstep (se 1 (by rfl) ⟨2153357, by rfl⟩ : syracuseStep 2871143 = 4306715) B4306715
theorem B1914095 : Blo 1913435 1914095 := bstep (se 1 (by rfl) ⟨1435571, by rfl⟩ : syracuseStep 1914095 = 2871143) B2871143
theorem B2871149 : Blo 1913435 2871149 := bbase (se 3 (by rfl) ⟨538340, by rfl⟩ : syracuseStep 2871149 = 1076681) (by norm_num)
theorem B1914099 : Blo 1913435 1914099 := bstep (se 1 (by rfl) ⟨1435574, by rfl⟩ : syracuseStep 1914099 = 2871149) B2871149
theorem B4306733 : Blo 1913435 4306733 := bbase (se 3 (by rfl) ⟨807512, by rfl⟩ : syracuseStep 4306733 = 1615025) (by norm_num)
theorem B2871155 : Blo 1913435 2871155 := bstep (se 1 (by rfl) ⟨2153366, by rfl⟩ : syracuseStep 2871155 = 4306733) B4306733
theorem B1914103 : Blo 1913435 1914103 := bstep (se 1 (by rfl) ⟨1435577, by rfl⟩ : syracuseStep 1914103 = 2871155) B2871155
theorem B8176085 : Blo 1913435 8176085 := bbase (se 7 (by rfl) ⟨95813, by rfl⟩ : syracuseStep 8176085 = 191627) (by norm_num)
theorem B5450723 : Blo 1913435 5450723 := bstep (se 1 (by rfl) ⟨4088042, by rfl⟩ : syracuseStep 5450723 = 8176085) B8176085
theorem B3633815 : Blo 1913435 3633815 := bstep (se 1 (by rfl) ⟨2725361, by rfl⟩ : syracuseStep 3633815 = 5450723) B5450723
theorem B2422543 : Blo 1913435 2422543 := bstep (se 1 (by rfl) ⟨1816907, by rfl⟩ : syracuseStep 2422543 = 3633815) B3633815
theorem B3230057 : Blo 1913435 3230057 := bstep (se 2 (by rfl) ⟨1211271, by rfl⟩ : syracuseStep 3230057 = 2422543) B2422543
theorem B2153371 : Blo 1913435 2153371 := bstep (se 1 (by rfl) ⟨1615028, by rfl⟩ : syracuseStep 2153371 = 3230057) B3230057
theorem B2871161 : Blo 1913435 2871161 := bstep (se 2 (by rfl) ⟨1076685, by rfl⟩ : syracuseStep 2871161 = 2153371) B2153371
theorem B1914107 : Blo 1913435 1914107 := bstep (se 1 (by rfl) ⟨1435580, by rfl⟩ : syracuseStep 1914107 = 2871161) B2871161
theorem B12264149 : Blo 1913435 12264149 := bbase (se 7 (by rfl) ⟨143720, by rfl⟩ : syracuseStep 12264149 = 287441) (by norm_num)
theorem B32704397 : Blo 1913435 32704397 := bstep (se 3 (by rfl) ⟨6132074, by rfl⟩ : syracuseStep 32704397 = 12264149) B12264149
theorem B21802931 : Blo 1913435 21802931 := bstep (se 1 (by rfl) ⟨16352198, by rfl⟩ : syracuseStep 21802931 = 32704397) B32704397
theorem B14535287 : Blo 1913435 14535287 := bstep (se 1 (by rfl) ⟨10901465, by rfl⟩ : syracuseStep 14535287 = 21802931) B21802931
theorem B9690191 : Blo 1913435 9690191 := bstep (se 1 (by rfl) ⟨7267643, by rfl⟩ : syracuseStep 9690191 = 14535287) B14535287
theorem B6460127 : Blo 1913435 6460127 := bstep (se 1 (by rfl) ⟨4845095, by rfl⟩ : syracuseStep 6460127 = 9690191) B9690191
theorem B4306751 : Blo 1913435 4306751 := bstep (se 1 (by rfl) ⟨3230063, by rfl⟩ : syracuseStep 4306751 = 6460127) B6460127
theorem B2871167 : Blo 1913435 2871167 := bstep (se 1 (by rfl) ⟨2153375, by rfl⟩ : syracuseStep 2871167 = 4306751) B4306751
theorem B1914111 : Blo 1913435 1914111 := bstep (se 1 (by rfl) ⟨1435583, by rfl⟩ : syracuseStep 1914111 = 2871167) B2871167
theorem B2871173 : Blo 1913435 2871173 := bbase (se 4 (by rfl) ⟨269172, by rfl⟩ : syracuseStep 2871173 = 538345) (by norm_num)
theorem B1914115 : Blo 1913435 1914115 := bstep (se 1 (by rfl) ⟨1435586, by rfl⟩ : syracuseStep 1914115 = 2871173) B2871173
theorem B3230077 : Blo 1913435 3230077 := bbase (se 3 (by rfl) ⟨605639, by rfl⟩ : syracuseStep 3230077 = 1211279) (by norm_num)
theorem B4306769 : Blo 1913435 4306769 := bstep (se 2 (by rfl) ⟨1615038, by rfl⟩ : syracuseStep 4306769 = 3230077) B3230077
theorem B2871179 : Blo 1913435 2871179 := bstep (se 1 (by rfl) ⟨2153384, by rfl⟩ : syracuseStep 2871179 = 4306769) B4306769
theorem B1914119 : Blo 1913435 1914119 := bstep (se 1 (by rfl) ⟨1435589, by rfl⟩ : syracuseStep 1914119 = 2871179) B2871179
theorem B2153389 : Blo 1913435 2153389 := bbase (se 3 (by rfl) ⟨403760, by rfl⟩ : syracuseStep 2153389 = 807521) (by norm_num)
theorem B2871185 : Blo 1913435 2871185 := bstep (se 2 (by rfl) ⟨1076694, by rfl⟩ : syracuseStep 2871185 = 2153389) B2153389
theorem B1914123 : Blo 1913435 1914123 := bstep (se 1 (by rfl) ⟨1435592, by rfl⟩ : syracuseStep 1914123 = 2871185) B2871185
theorem B6460181 : Blo 1913435 6460181 := bbase (se 6 (by rfl) ⟨151410, by rfl⟩ : syracuseStep 6460181 = 302821) (by norm_num)
theorem B4306787 : Blo 1913435 4306787 := bstep (se 1 (by rfl) ⟨3230090, by rfl⟩ : syracuseStep 4306787 = 6460181) B6460181
theorem B2871191 : Blo 1913435 2871191 := bstep (se 1 (by rfl) ⟨2153393, by rfl⟩ : syracuseStep 2871191 = 4306787) B4306787
theorem B1914127 : Blo 1913435 1914127 := bstep (se 1 (by rfl) ⟨1435595, by rfl⟩ : syracuseStep 1914127 = 2871191) B2871191
theorem B2871197 : Blo 1913435 2871197 := bbase (se 3 (by rfl) ⟨538349, by rfl⟩ : syracuseStep 2871197 = 1076699) (by norm_num)
theorem B1914131 : Blo 1913435 1914131 := bstep (se 1 (by rfl) ⟨1435598, by rfl⟩ : syracuseStep 1914131 = 2871197) B2871197
theorem B4306805 : Blo 1913435 4306805 := bbase (se 5 (by rfl) ⟨201881, by rfl⟩ : syracuseStep 4306805 = 403763) (by norm_num)
theorem B2871203 : Blo 1913435 2871203 := bstep (se 1 (by rfl) ⟨2153402, by rfl⟩ : syracuseStep 2871203 = 4306805) B4306805
theorem B1914135 : Blo 1913435 1914135 := bstep (se 1 (by rfl) ⟨1435601, by rfl⟩ : syracuseStep 1914135 = 2871203) B2871203
theorem B2990341 : Blo 1913435 2990341 := bbase (se 4 (by rfl) ⟨280344, by rfl⟩ : syracuseStep 2990341 = 560689) (by norm_num)
theorem B15948485 : Blo 1913435 15948485 := bstep (se 4 (by rfl) ⟨1495170, by rfl⟩ : syracuseStep 15948485 = 2990341) B2990341
theorem B10632323 : Blo 1913435 10632323 := bstep (se 1 (by rfl) ⟨7974242, by rfl⟩ : syracuseStep 10632323 = 15948485) B15948485
theorem B28352861 : Blo 1913435 28352861 := bstep (se 3 (by rfl) ⟨5316161, by rfl⟩ : syracuseStep 28352861 = 10632323) B10632323
theorem B18901907 : Blo 1913435 18901907 := bstep (se 1 (by rfl) ⟨14176430, by rfl⟩ : syracuseStep 18901907 = 28352861) B28352861
theorem B12601271 : Blo 1913435 12601271 := bstep (se 1 (by rfl) ⟨9450953, by rfl⟩ : syracuseStep 12601271 = 18901907) B18901907
theorem B8400847 : Blo 1913435 8400847 := bstep (se 1 (by rfl) ⟨6300635, by rfl⟩ : syracuseStep 8400847 = 12601271) B12601271
theorem B11201129 : Blo 1913435 11201129 := bstep (se 2 (by rfl) ⟨4200423, by rfl⟩ : syracuseStep 11201129 = 8400847) B8400847
theorem B7467419 : Blo 1913435 7467419 := bstep (se 1 (by rfl) ⟨5600564, by rfl⟩ : syracuseStep 7467419 = 11201129) B11201129
theorem B4978279 : Blo 1913435 4978279 := bstep (se 1 (by rfl) ⟨3733709, by rfl⟩ : syracuseStep 4978279 = 7467419) B7467419
theorem B26550821 : Blo 1913435 26550821 := bstep (se 4 (by rfl) ⟨2489139, by rfl⟩ : syracuseStep 26550821 = 4978279) B4978279
theorem B70802189 : Blo 1913435 70802189 := bstep (se 3 (by rfl) ⟨13275410, by rfl⟩ : syracuseStep 70802189 = 26550821) B26550821
theorem B47201459 : Blo 1913435 47201459 := bstep (se 1 (by rfl) ⟨35401094, by rfl⟩ : syracuseStep 47201459 = 70802189) B70802189
theorem B125870557 : Blo 1913435 125870557 := bstep (se 3 (by rfl) ⟨23600729, by rfl⟩ : syracuseStep 125870557 = 47201459) B47201459
theorem B167827409 : Blo 1913435 167827409 := bstep (se 2 (by rfl) ⟨62935278, by rfl⟩ : syracuseStep 167827409 = 125870557) B125870557
theorem B111884939 : Blo 1913435 111884939 := bstep (se 1 (by rfl) ⟨83913704, by rfl⟩ : syracuseStep 111884939 = 167827409) B167827409
theorem B74589959 : Blo 1913435 74589959 := bstep (se 1 (by rfl) ⟨55942469, by rfl⟩ : syracuseStep 74589959 = 111884939) B111884939
theorem B49726639 : Blo 1913435 49726639 := bstep (se 1 (by rfl) ⟨37294979, by rfl⟩ : syracuseStep 49726639 = 74589959) B74589959
theorem B66302185 : Blo 1913435 66302185 := bstep (se 2 (by rfl) ⟨24863319, by rfl⟩ : syracuseStep 66302185 = 49726639) B49726639
theorem B88402913 : Blo 1913435 88402913 := bstep (se 2 (by rfl) ⟨33151092, by rfl⟩ : syracuseStep 88402913 = 66302185) B66302185
theorem B58935275 : Blo 1913435 58935275 := bstep (se 1 (by rfl) ⟨44201456, by rfl⟩ : syracuseStep 58935275 = 88402913) B88402913
theorem B39290183 : Blo 1913435 39290183 := bstep (se 1 (by rfl) ⟨29467637, by rfl⟩ : syracuseStep 39290183 = 58935275) B58935275
theorem B26193455 : Blo 1913435 26193455 := bstep (se 1 (by rfl) ⟨19645091, by rfl⟩ : syracuseStep 26193455 = 39290183) B39290183
theorem B17462303 : Blo 1913435 17462303 := bstep (se 1 (by rfl) ⟨13096727, by rfl⟩ : syracuseStep 17462303 = 26193455) B26193455
theorem B11641535 : Blo 1913435 11641535 := bstep (se 1 (by rfl) ⟨8731151, by rfl⟩ : syracuseStep 11641535 = 17462303) B17462303
theorem B7761023 : Blo 1913435 7761023 := bstep (se 1 (by rfl) ⟨5820767, by rfl⟩ : syracuseStep 7761023 = 11641535) B11641535
theorem B5174015 : Blo 1913435 5174015 := bstep (se 1 (by rfl) ⟨3880511, by rfl⟩ : syracuseStep 5174015 = 7761023) B7761023
theorem B13797373 : Blo 1913435 13797373 := bstep (se 3 (by rfl) ⟨2587007, by rfl⟩ : syracuseStep 13797373 = 5174015) B5174015
theorem B18396497 : Blo 1913435 18396497 := bstep (se 2 (by rfl) ⟨6898686, by rfl⟩ : syracuseStep 18396497 = 13797373) B13797373
theorem B12264331 : Blo 1913435 12264331 := bstep (se 1 (by rfl) ⟨9198248, by rfl⟩ : syracuseStep 12264331 = 18396497) B18396497
theorem B16352441 : Blo 1913435 16352441 := bstep (se 2 (by rfl) ⟨6132165, by rfl⟩ : syracuseStep 16352441 = 12264331) B12264331
theorem B10901627 : Blo 1913435 10901627 := bstep (se 1 (by rfl) ⟨8176220, by rfl⟩ : syracuseStep 10901627 = 16352441) B16352441
theorem B7267751 : Blo 1913435 7267751 := bstep (se 1 (by rfl) ⟨5450813, by rfl⟩ : syracuseStep 7267751 = 10901627) B10901627
theorem B4845167 : Blo 1913435 4845167 := bstep (se 1 (by rfl) ⟨3633875, by rfl⟩ : syracuseStep 4845167 = 7267751) B7267751
theorem B3230111 : Blo 1913435 3230111 := bstep (se 1 (by rfl) ⟨2422583, by rfl⟩ : syracuseStep 3230111 = 4845167) B4845167
theorem B2153407 : Blo 1913435 2153407 := bstep (se 1 (by rfl) ⟨1615055, by rfl⟩ : syracuseStep 2153407 = 3230111) B3230111
theorem B2871209 : Blo 1913435 2871209 := bstep (se 2 (by rfl) ⟨1076703, by rfl⟩ : syracuseStep 2871209 = 2153407) B2153407
theorem B1914139 : Blo 1913435 1914139 := bstep (se 1 (by rfl) ⟨1435604, by rfl⟩ : syracuseStep 1914139 = 2871209) B2871209
theorem B7267765 : Blo 1913435 7267765 := bbase (se 5 (by rfl) ⟨340676, by rfl⟩ : syracuseStep 7267765 = 681353) (by norm_num)
theorem B9690353 : Blo 1913435 9690353 := bstep (se 2 (by rfl) ⟨3633882, by rfl⟩ : syracuseStep 9690353 = 7267765) B7267765
theorem B6460235 : Blo 1913435 6460235 := bstep (se 1 (by rfl) ⟨4845176, by rfl⟩ : syracuseStep 6460235 = 9690353) B9690353
theorem B4306823 : Blo 1913435 4306823 := bstep (se 1 (by rfl) ⟨3230117, by rfl⟩ : syracuseStep 4306823 = 6460235) B6460235
theorem B2871215 : Blo 1913435 2871215 := bstep (se 1 (by rfl) ⟨2153411, by rfl⟩ : syracuseStep 2871215 = 4306823) B4306823
theorem B1914143 : Blo 1913435 1914143 := bstep (se 1 (by rfl) ⟨1435607, by rfl⟩ : syracuseStep 1914143 = 2871215) B2871215
theorem B2871221 : Blo 1913435 2871221 := bbase (se 5 (by rfl) ⟨134588, by rfl⟩ : syracuseStep 2871221 = 269177) (by norm_num)
theorem B1914147 : Blo 1913435 1914147 := bstep (se 1 (by rfl) ⟨1435610, by rfl⟩ : syracuseStep 1914147 = 2871221) B2871221
theorem B4845197 : Blo 1913435 4845197 := bbase (se 3 (by rfl) ⟨908474, by rfl⟩ : syracuseStep 4845197 = 1816949) (by norm_num)
theorem B3230131 : Blo 1913435 3230131 := bstep (se 1 (by rfl) ⟨2422598, by rfl⟩ : syracuseStep 3230131 = 4845197) B4845197
theorem B4306841 : Blo 1913435 4306841 := bstep (se 2 (by rfl) ⟨1615065, by rfl⟩ : syracuseStep 4306841 = 3230131) B3230131
theorem B2871227 : Blo 1913435 2871227 := bstep (se 1 (by rfl) ⟨2153420, by rfl⟩ : syracuseStep 2871227 = 4306841) B4306841
theorem B1914151 : Blo 1913435 1914151 := bstep (se 1 (by rfl) ⟨1435613, by rfl⟩ : syracuseStep 1914151 = 2871227) B2871227
theorem B2153425 : Blo 1913435 2153425 := bbase (se 2 (by rfl) ⟨807534, by rfl⟩ : syracuseStep 2153425 = 1615069) (by norm_num)
theorem B2871233 : Blo 1913435 2871233 := bstep (se 2 (by rfl) ⟨1076712, by rfl⟩ : syracuseStep 2871233 = 2153425) B2153425
theorem B1914155 : Blo 1913435 1914155 := bstep (se 1 (by rfl) ⟨1435616, by rfl⟩ : syracuseStep 1914155 = 2871233) B2871233
theorem B4599173 : Blo 1913435 4599173 := bbase (se 4 (by rfl) ⟨431172, by rfl⟩ : syracuseStep 4599173 = 862345) (by norm_num)
theorem B3066115 : Blo 1913435 3066115 := bstep (se 1 (by rfl) ⟨2299586, by rfl⟩ : syracuseStep 3066115 = 4599173) B4599173
theorem B4088153 : Blo 1913435 4088153 := bstep (se 2 (by rfl) ⟨1533057, by rfl⟩ : syracuseStep 4088153 = 3066115) B3066115
theorem B2725435 : Blo 1913435 2725435 := bstep (se 1 (by rfl) ⟨2044076, by rfl⟩ : syracuseStep 2725435 = 4088153) B4088153
theorem B3633913 : Blo 1913435 3633913 := bstep (se 2 (by rfl) ⟨1362717, by rfl⟩ : syracuseStep 3633913 = 2725435) B2725435
theorem B4845217 : Blo 1913435 4845217 := bstep (se 2 (by rfl) ⟨1816956, by rfl⟩ : syracuseStep 4845217 = 3633913) B3633913
theorem B6460289 : Blo 1913435 6460289 := bstep (se 2 (by rfl) ⟨2422608, by rfl⟩ : syracuseStep 6460289 = 4845217) B4845217
theorem B4306859 : Blo 1913435 4306859 := bstep (se 1 (by rfl) ⟨3230144, by rfl⟩ : syracuseStep 4306859 = 6460289) B6460289
theorem B2871239 : Blo 1913435 2871239 := bstep (se 1 (by rfl) ⟨2153429, by rfl⟩ : syracuseStep 2871239 = 4306859) B4306859
theorem B1914159 : Blo 1913435 1914159 := bstep (se 1 (by rfl) ⟨1435619, by rfl⟩ : syracuseStep 1914159 = 2871239) B2871239
theorem B2871245 : Blo 1913435 2871245 := bbase (se 3 (by rfl) ⟨538358, by rfl⟩ : syracuseStep 2871245 = 1076717) (by norm_num)
theorem B1914163 : Blo 1913435 1914163 := bstep (se 1 (by rfl) ⟨1435622, by rfl⟩ : syracuseStep 1914163 = 2871245) B2871245
theorem B4306877 : Blo 1913435 4306877 := bbase (se 3 (by rfl) ⟨807539, by rfl⟩ : syracuseStep 4306877 = 1615079) (by norm_num)
theorem B2871251 : Blo 1913435 2871251 := bstep (se 1 (by rfl) ⟨2153438, by rfl⟩ : syracuseStep 2871251 = 4306877) B4306877
theorem B1914167 : Blo 1913435 1914167 := bstep (se 1 (by rfl) ⟨1435625, by rfl⟩ : syracuseStep 1914167 = 2871251) B2871251
theorem B3230165 : Blo 1913435 3230165 := bbase (se 7 (by rfl) ⟨37853, by rfl⟩ : syracuseStep 3230165 = 75707) (by norm_num)
theorem B2153443 : Blo 1913435 2153443 := bstep (se 1 (by rfl) ⟨1615082, by rfl⟩ : syracuseStep 2153443 = 3230165) B3230165
theorem B2871257 : Blo 1913435 2871257 := bstep (se 2 (by rfl) ⟨1076721, by rfl⟩ : syracuseStep 2871257 = 2153443) B2153443
theorem B1914171 : Blo 1913435 1914171 := bstep (se 1 (by rfl) ⟨1435628, by rfl⟩ : syracuseStep 1914171 = 2871257) B2871257
theorem B8176373 : Blo 1913435 8176373 := bbase (se 5 (by rfl) ⟨383267, by rfl⟩ : syracuseStep 8176373 = 766535) (by norm_num)
theorem B5450915 : Blo 1913435 5450915 := bstep (se 1 (by rfl) ⟨4088186, by rfl⟩ : syracuseStep 5450915 = 8176373) B8176373
theorem B14535773 : Blo 1913435 14535773 := bstep (se 3 (by rfl) ⟨2725457, by rfl⟩ : syracuseStep 14535773 = 5450915) B5450915
theorem B9690515 : Blo 1913435 9690515 := bstep (se 1 (by rfl) ⟨7267886, by rfl⟩ : syracuseStep 9690515 = 14535773) B14535773
theorem B6460343 : Blo 1913435 6460343 := bstep (se 1 (by rfl) ⟨4845257, by rfl⟩ : syracuseStep 6460343 = 9690515) B9690515
theorem B4306895 : Blo 1913435 4306895 := bstep (se 1 (by rfl) ⟨3230171, by rfl⟩ : syracuseStep 4306895 = 6460343) B6460343
theorem B2871263 : Blo 1913435 2871263 := bstep (se 1 (by rfl) ⟨2153447, by rfl⟩ : syracuseStep 2871263 = 4306895) B4306895
theorem B1914175 : Blo 1913435 1914175 := bstep (se 1 (by rfl) ⟨1435631, by rfl⟩ : syracuseStep 1914175 = 2871263) B2871263
theorem B2871269 : Blo 1913435 2871269 := bbase (se 4 (by rfl) ⟨269181, by rfl⟩ : syracuseStep 2871269 = 538363) (by norm_num)
theorem B1914179 : Blo 1913435 1914179 := bstep (se 1 (by rfl) ⟨1435634, by rfl⟩ : syracuseStep 1914179 = 2871269) B2871269
theorem B4365677 : Blo 1913435 4365677 := bbase (se 3 (by rfl) ⟨818564, by rfl⟩ : syracuseStep 4365677 = 1637129) (by norm_num)
theorem B11641805 : Blo 1913435 11641805 := bstep (se 3 (by rfl) ⟨2182838, by rfl⟩ : syracuseStep 11641805 = 4365677) B4365677
theorem B7761203 : Blo 1913435 7761203 := bstep (se 1 (by rfl) ⟨5820902, by rfl⟩ : syracuseStep 7761203 = 11641805) B11641805
theorem B5174135 : Blo 1913435 5174135 := bstep (se 1 (by rfl) ⟨3880601, by rfl⟩ : syracuseStep 5174135 = 7761203) B7761203
theorem B3449423 : Blo 1913435 3449423 := bstep (se 1 (by rfl) ⟨2587067, by rfl⟩ : syracuseStep 3449423 = 5174135) B5174135
theorem B9198461 : Blo 1913435 9198461 := bstep (se 3 (by rfl) ⟨1724711, by rfl⟩ : syracuseStep 9198461 = 3449423) B3449423
theorem B6132307 : Blo 1913435 6132307 := bstep (se 1 (by rfl) ⟨4599230, by rfl⟩ : syracuseStep 6132307 = 9198461) B9198461
theorem B8176409 : Blo 1913435 8176409 := bstep (se 2 (by rfl) ⟨3066153, by rfl⟩ : syracuseStep 8176409 = 6132307) B6132307
theorem B5450939 : Blo 1913435 5450939 := bstep (se 1 (by rfl) ⟨4088204, by rfl⟩ : syracuseStep 5450939 = 8176409) B8176409
theorem B3633959 : Blo 1913435 3633959 := bstep (se 1 (by rfl) ⟨2725469, by rfl⟩ : syracuseStep 3633959 = 5450939) B5450939
theorem B2422639 : Blo 1913435 2422639 := bstep (se 1 (by rfl) ⟨1816979, by rfl⟩ : syracuseStep 2422639 = 3633959) B3633959
theorem B3230185 : Blo 1913435 3230185 := bstep (se 2 (by rfl) ⟨1211319, by rfl⟩ : syracuseStep 3230185 = 2422639) B2422639
theorem B4306913 : Blo 1913435 4306913 := bstep (se 2 (by rfl) ⟨1615092, by rfl⟩ : syracuseStep 4306913 = 3230185) B3230185
theorem B2871275 : Blo 1913435 2871275 := bstep (se 1 (by rfl) ⟨2153456, by rfl⟩ : syracuseStep 2871275 = 4306913) B4306913
theorem B1914183 : Blo 1913435 1914183 := bstep (se 1 (by rfl) ⟨1435637, by rfl⟩ : syracuseStep 1914183 = 2871275) B2871275
theorem B2153461 : Blo 1913435 2153461 := bbase (se 5 (by rfl) ⟨100943, by rfl⟩ : syracuseStep 2153461 = 201887) (by norm_num)
theorem B2871281 : Blo 1913435 2871281 := bstep (se 2 (by rfl) ⟨1076730, by rfl⟩ : syracuseStep 2871281 = 2153461) B2153461
theorem B1914187 : Blo 1913435 1914187 := bstep (se 1 (by rfl) ⟨1435640, by rfl⟩ : syracuseStep 1914187 = 2871281) B2871281
theorem B2422649 : Blo 1913435 2422649 := bbase (se 2 (by rfl) ⟨908493, by rfl⟩ : syracuseStep 2422649 = 1816987) (by norm_num)
theorem B6460397 : Blo 1913435 6460397 := bstep (se 3 (by rfl) ⟨1211324, by rfl⟩ : syracuseStep 6460397 = 2422649) B2422649
theorem B4306931 : Blo 1913435 4306931 := bstep (se 1 (by rfl) ⟨3230198, by rfl⟩ : syracuseStep 4306931 = 6460397) B6460397
theorem B2871287 : Blo 1913435 2871287 := bstep (se 1 (by rfl) ⟨2153465, by rfl⟩ : syracuseStep 2871287 = 4306931) B4306931
theorem B1914191 : Blo 1913435 1914191 := bstep (se 1 (by rfl) ⟨1435643, by rfl⟩ : syracuseStep 1914191 = 2871287) B2871287
theorem B2871293 : Blo 1913435 2871293 := bbase (se 3 (by rfl) ⟨538367, by rfl⟩ : syracuseStep 2871293 = 1076735) (by norm_num)
theorem B1914195 : Blo 1913435 1914195 := bstep (se 1 (by rfl) ⟨1435646, by rfl⟩ : syracuseStep 1914195 = 2871293) B2871293
theorem B4306949 : Blo 1913435 4306949 := bbase (se 4 (by rfl) ⟨403776, by rfl⟩ : syracuseStep 4306949 = 807553) (by norm_num)
theorem B2871299 : Blo 1913435 2871299 := bstep (se 1 (by rfl) ⟨2153474, by rfl⟩ : syracuseStep 2871299 = 4306949) B4306949
theorem B1914199 : Blo 1913435 1914199 := bstep (se 1 (by rfl) ⟨1435649, by rfl⟩ : syracuseStep 1914199 = 2871299) B2871299
theorem B3633997 : Blo 1913435 3633997 := bbase (se 3 (by rfl) ⟨681374, by rfl⟩ : syracuseStep 3633997 = 1362749) (by norm_num)
theorem B4845329 : Blo 1913435 4845329 := bstep (se 2 (by rfl) ⟨1816998, by rfl⟩ : syracuseStep 4845329 = 3633997) B3633997
theorem B3230219 : Blo 1913435 3230219 := bstep (se 1 (by rfl) ⟨2422664, by rfl⟩ : syracuseStep 3230219 = 4845329) B4845329
theorem B2153479 : Blo 1913435 2153479 := bstep (se 1 (by rfl) ⟨1615109, by rfl⟩ : syracuseStep 2153479 = 3230219) B3230219
theorem B2871305 : Blo 1913435 2871305 := bstep (se 2 (by rfl) ⟨1076739, by rfl⟩ : syracuseStep 2871305 = 2153479) B2153479
theorem B1914203 : Blo 1913435 1914203 := bstep (se 1 (by rfl) ⟨1435652, by rfl⟩ : syracuseStep 1914203 = 2871305) B2871305
theorem B9690677 : Blo 1913435 9690677 := bbase (se 5 (by rfl) ⟨454250, by rfl⟩ : syracuseStep 9690677 = 908501) (by norm_num)
theorem B6460451 : Blo 1913435 6460451 := bstep (se 1 (by rfl) ⟨4845338, by rfl⟩ : syracuseStep 6460451 = 9690677) B9690677
theorem B4306967 : Blo 1913435 4306967 := bstep (se 1 (by rfl) ⟨3230225, by rfl⟩ : syracuseStep 4306967 = 6460451) B6460451
theorem B2871311 : Blo 1913435 2871311 := bstep (se 1 (by rfl) ⟨2153483, by rfl⟩ : syracuseStep 2871311 = 4306967) B4306967
theorem B1914207 : Blo 1913435 1914207 := bstep (se 1 (by rfl) ⟨1435655, by rfl⟩ : syracuseStep 1914207 = 2871311) B2871311
theorem B2871317 : Blo 1913435 2871317 := bbase (se 6 (by rfl) ⟨67296, by rfl⟩ : syracuseStep 2871317 = 134593) (by norm_num)
theorem B1914211 : Blo 1913435 1914211 := bstep (se 1 (by rfl) ⟨1435658, by rfl⟩ : syracuseStep 1914211 = 2871317) B2871317
theorem B9198613 : Blo 1913435 9198613 := bbase (se 6 (by rfl) ⟨215592, by rfl⟩ : syracuseStep 9198613 = 431185) (by norm_num)
theorem B12264817 : Blo 1913435 12264817 := bstep (se 2 (by rfl) ⟨4599306, by rfl⟩ : syracuseStep 12264817 = 9198613) B9198613
theorem B16353089 : Blo 1913435 16353089 := bstep (se 2 (by rfl) ⟨6132408, by rfl⟩ : syracuseStep 16353089 = 12264817) B12264817
theorem B10902059 : Blo 1913435 10902059 := bstep (se 1 (by rfl) ⟨8176544, by rfl⟩ : syracuseStep 10902059 = 16353089) B16353089
theorem B7268039 : Blo 1913435 7268039 := bstep (se 1 (by rfl) ⟨5451029, by rfl⟩ : syracuseStep 7268039 = 10902059) B10902059
theorem B4845359 : Blo 1913435 4845359 := bstep (se 1 (by rfl) ⟨3634019, by rfl⟩ : syracuseStep 4845359 = 7268039) B7268039
theorem B3230239 : Blo 1913435 3230239 := bstep (se 1 (by rfl) ⟨2422679, by rfl⟩ : syracuseStep 3230239 = 4845359) B4845359
theorem B4306985 : Blo 1913435 4306985 := bstep (se 2 (by rfl) ⟨1615119, by rfl⟩ : syracuseStep 4306985 = 3230239) B3230239
theorem B2871323 : Blo 1913435 2871323 := bstep (se 1 (by rfl) ⟨2153492, by rfl⟩ : syracuseStep 2871323 = 4306985) B4306985
theorem B1914215 : Blo 1913435 1914215 := bstep (se 1 (by rfl) ⟨1435661, by rfl⟩ : syracuseStep 1914215 = 2871323) B2871323
theorem B2153497 : Blo 1913435 2153497 := bbase (se 2 (by rfl) ⟨807561, by rfl⟩ : syracuseStep 2153497 = 1615123) (by norm_num)
theorem B2871329 : Blo 1913435 2871329 := bstep (se 2 (by rfl) ⟨1076748, by rfl⟩ : syracuseStep 2871329 = 2153497) B2153497
theorem B1914219 : Blo 1913435 1914219 := bstep (se 1 (by rfl) ⟨1435664, by rfl⟩ : syracuseStep 1914219 = 2871329) B2871329
theorem B7268069 : Blo 1913435 7268069 := bbase (se 4 (by rfl) ⟨681381, by rfl⟩ : syracuseStep 7268069 = 1362763) (by norm_num)
theorem B4845379 : Blo 1913435 4845379 := bstep (se 1 (by rfl) ⟨3634034, by rfl⟩ : syracuseStep 4845379 = 7268069) B7268069
theorem B6460505 : Blo 1913435 6460505 := bstep (se 2 (by rfl) ⟨2422689, by rfl⟩ : syracuseStep 6460505 = 4845379) B4845379
theorem B4307003 : Blo 1913435 4307003 := bstep (se 1 (by rfl) ⟨3230252, by rfl⟩ : syracuseStep 4307003 = 6460505) B6460505
theorem B2871335 : Blo 1913435 2871335 := bstep (se 1 (by rfl) ⟨2153501, by rfl⟩ : syracuseStep 2871335 = 4307003) B4307003
theorem B1914223 : Blo 1913435 1914223 := bstep (se 1 (by rfl) ⟨1435667, by rfl⟩ : syracuseStep 1914223 = 2871335) B2871335
theorem B2871341 : Blo 1913435 2871341 := bbase (se 3 (by rfl) ⟨538376, by rfl⟩ : syracuseStep 2871341 = 1076753) (by norm_num)
theorem B1914227 : Blo 1913435 1914227 := bstep (se 1 (by rfl) ⟨1435670, by rfl⟩ : syracuseStep 1914227 = 2871341) B2871341
theorem B4307021 : Blo 1913435 4307021 := bbase (se 3 (by rfl) ⟨807566, by rfl⟩ : syracuseStep 4307021 = 1615133) (by norm_num)
theorem B2871347 : Blo 1913435 2871347 := bstep (se 1 (by rfl) ⟨2153510, by rfl⟩ : syracuseStep 2871347 = 4307021) B4307021
theorem B1914231 : Blo 1913435 1914231 := bstep (se 1 (by rfl) ⟨1435673, by rfl⟩ : syracuseStep 1914231 = 2871347) B2871347
theorem B2422705 : Blo 1913435 2422705 := bbase (se 2 (by rfl) ⟨908514, by rfl⟩ : syracuseStep 2422705 = 1817029) (by norm_num)
theorem B3230273 : Blo 1913435 3230273 := bstep (se 2 (by rfl) ⟨1211352, by rfl⟩ : syracuseStep 3230273 = 2422705) B2422705
theorem B2153515 : Blo 1913435 2153515 := bstep (se 1 (by rfl) ⟨1615136, by rfl⟩ : syracuseStep 2153515 = 3230273) B3230273
theorem B2871353 : Blo 1913435 2871353 := bstep (se 2 (by rfl) ⟨1076757, by rfl⟩ : syracuseStep 2871353 = 2153515) B2153515
theorem B1914235 : Blo 1913435 1914235 := bstep (se 1 (by rfl) ⟨1435676, by rfl⟩ : syracuseStep 1914235 = 2871353) B2871353
theorem B6132485 : Blo 1913435 6132485 := bbase (se 4 (by rfl) ⟨574920, by rfl⟩ : syracuseStep 6132485 = 1149841) (by norm_num)
theorem B4088323 : Blo 1913435 4088323 := bstep (se 1 (by rfl) ⟨3066242, by rfl⟩ : syracuseStep 4088323 = 6132485) B6132485
theorem B21804389 : Blo 1913435 21804389 := bstep (se 4 (by rfl) ⟨2044161, by rfl⟩ : syracuseStep 21804389 = 4088323) B4088323
theorem B14536259 : Blo 1913435 14536259 := bstep (se 1 (by rfl) ⟨10902194, by rfl⟩ : syracuseStep 14536259 = 21804389) B21804389
theorem B9690839 : Blo 1913435 9690839 := bstep (se 1 (by rfl) ⟨7268129, by rfl⟩ : syracuseStep 9690839 = 14536259) B14536259
theorem B6460559 : Blo 1913435 6460559 := bstep (se 1 (by rfl) ⟨4845419, by rfl⟩ : syracuseStep 6460559 = 9690839) B9690839
theorem B4307039 : Blo 1913435 4307039 := bstep (se 1 (by rfl) ⟨3230279, by rfl⟩ : syracuseStep 4307039 = 6460559) B6460559
theorem B2871359 : Blo 1913435 2871359 := bstep (se 1 (by rfl) ⟨2153519, by rfl⟩ : syracuseStep 2871359 = 4307039) B4307039
theorem B1914239 : Blo 1913435 1914239 := bstep (se 1 (by rfl) ⟨1435679, by rfl⟩ : syracuseStep 1914239 = 2871359) B2871359
theorem B2871365 : Blo 1913435 2871365 := bbase (se 4 (by rfl) ⟨269190, by rfl⟩ : syracuseStep 2871365 = 538381) (by norm_num)
theorem B1914243 : Blo 1913435 1914243 := bstep (se 1 (by rfl) ⟨1435682, by rfl⟩ : syracuseStep 1914243 = 2871365) B2871365
theorem B3230293 : Blo 1913435 3230293 := bbase (se 8 (by rfl) ⟨18927, by rfl⟩ : syracuseStep 3230293 = 37855) (by norm_num)
theorem B4307057 : Blo 1913435 4307057 := bstep (se 2 (by rfl) ⟨1615146, by rfl⟩ : syracuseStep 4307057 = 3230293) B3230293
theorem B2871371 : Blo 1913435 2871371 := bstep (se 1 (by rfl) ⟨2153528, by rfl⟩ : syracuseStep 2871371 = 4307057) B4307057
theorem B1914247 : Blo 1913435 1914247 := bstep (se 1 (by rfl) ⟨1435685, by rfl⟩ : syracuseStep 1914247 = 2871371) B2871371
theorem B2153533 : Blo 1913435 2153533 := bbase (se 3 (by rfl) ⟨403787, by rfl⟩ : syracuseStep 2153533 = 807575) (by norm_num)
theorem B2871377 : Blo 1913435 2871377 := bstep (se 2 (by rfl) ⟨1076766, by rfl⟩ : syracuseStep 2871377 = 2153533) B2153533
theorem B1914251 : Blo 1913435 1914251 := bstep (se 1 (by rfl) ⟨1435688, by rfl⟩ : syracuseStep 1914251 = 2871377) B2871377
theorem B6460613 : Blo 1913435 6460613 := bbase (se 4 (by rfl) ⟨605682, by rfl⟩ : syracuseStep 6460613 = 1211365) (by norm_num)
theorem B4307075 : Blo 1913435 4307075 := bstep (se 1 (by rfl) ⟨3230306, by rfl⟩ : syracuseStep 4307075 = 6460613) B6460613
theorem B2871383 : Blo 1913435 2871383 := bstep (se 1 (by rfl) ⟨2153537, by rfl⟩ : syracuseStep 2871383 = 4307075) B4307075
theorem B1914255 : Blo 1913435 1914255 := bstep (se 1 (by rfl) ⟨1435691, by rfl⟩ : syracuseStep 1914255 = 2871383) B2871383
theorem B2871389 : Blo 1913435 2871389 := bbase (se 3 (by rfl) ⟨538385, by rfl⟩ : syracuseStep 2871389 = 1076771) (by norm_num)
theorem B1914259 : Blo 1913435 1914259 := bstep (se 1 (by rfl) ⟨1435694, by rfl⟩ : syracuseStep 1914259 = 2871389) B2871389
theorem B4307093 : Blo 1913435 4307093 := bbase (se 6 (by rfl) ⟨100947, by rfl⟩ : syracuseStep 4307093 = 201895) (by norm_num)
theorem B2871395 : Blo 1913435 2871395 := bstep (se 1 (by rfl) ⟨2153546, by rfl⟩ : syracuseStep 2871395 = 4307093) B4307093
theorem B1914263 : Blo 1913435 1914263 := bstep (se 1 (by rfl) ⟨1435697, by rfl⟩ : syracuseStep 1914263 = 2871395) B2871395
theorem B2725589 : Blo 1913435 2725589 := bbase (se 7 (by rfl) ⟨31940, by rfl⟩ : syracuseStep 2725589 = 63881) (by norm_num)
theorem B7268237 : Blo 1913435 7268237 := bstep (se 3 (by rfl) ⟨1362794, by rfl⟩ : syracuseStep 7268237 = 2725589) B2725589
theorem B4845491 : Blo 1913435 4845491 := bstep (se 1 (by rfl) ⟨3634118, by rfl⟩ : syracuseStep 4845491 = 7268237) B7268237
theorem B3230327 : Blo 1913435 3230327 := bstep (se 1 (by rfl) ⟨2422745, by rfl⟩ : syracuseStep 3230327 = 4845491) B4845491
theorem B2153551 : Blo 1913435 2153551 := bstep (se 1 (by rfl) ⟨1615163, by rfl⟩ : syracuseStep 2153551 = 3230327) B3230327
theorem B2871401 : Blo 1913435 2871401 := bstep (se 2 (by rfl) ⟨1076775, by rfl⟩ : syracuseStep 2871401 = 2153551) B2153551
theorem B1914267 : Blo 1913435 1914267 := bstep (se 1 (by rfl) ⟨1435700, by rfl⟩ : syracuseStep 1914267 = 2871401) B2871401
theorem B7761557 : Blo 1913435 7761557 := bbase (se 6 (by rfl) ⟨181911, by rfl⟩ : syracuseStep 7761557 = 363823) (by norm_num)
theorem B5174371 : Blo 1913435 5174371 := bstep (se 1 (by rfl) ⟨3880778, by rfl⟩ : syracuseStep 5174371 = 7761557) B7761557
theorem B27596645 : Blo 1913435 27596645 := bstep (se 4 (by rfl) ⟨2587185, by rfl⟩ : syracuseStep 27596645 = 5174371) B5174371
theorem B18397763 : Blo 1913435 18397763 := bstep (se 1 (by rfl) ⟨13798322, by rfl⟩ : syracuseStep 18397763 = 27596645) B27596645
theorem B12265175 : Blo 1913435 12265175 := bstep (se 1 (by rfl) ⟨9198881, by rfl⟩ : syracuseStep 12265175 = 18397763) B18397763
theorem B8176783 : Blo 1913435 8176783 := bstep (se 1 (by rfl) ⟨6132587, by rfl⟩ : syracuseStep 8176783 = 12265175) B12265175
theorem B10902377 : Blo 1913435 10902377 := bstep (se 2 (by rfl) ⟨4088391, by rfl⟩ : syracuseStep 10902377 = 8176783) B8176783
theorem B7268251 : Blo 1913435 7268251 := bstep (se 1 (by rfl) ⟨5451188, by rfl⟩ : syracuseStep 7268251 = 10902377) B10902377
theorem B9691001 : Blo 1913435 9691001 := bstep (se 2 (by rfl) ⟨3634125, by rfl⟩ : syracuseStep 9691001 = 7268251) B7268251
theorem B6460667 : Blo 1913435 6460667 := bstep (se 1 (by rfl) ⟨4845500, by rfl⟩ : syracuseStep 6460667 = 9691001) B9691001
theorem B4307111 : Blo 1913435 4307111 := bstep (se 1 (by rfl) ⟨3230333, by rfl⟩ : syracuseStep 4307111 = 6460667) B6460667
theorem B2871407 : Blo 1913435 2871407 := bstep (se 1 (by rfl) ⟨2153555, by rfl⟩ : syracuseStep 2871407 = 4307111) B4307111
theorem B1914271 : Blo 1913435 1914271 := bstep (se 1 (by rfl) ⟨1435703, by rfl⟩ : syracuseStep 1914271 = 2871407) B2871407
theorem B2871413 : Blo 1913435 2871413 := bbase (se 5 (by rfl) ⟨134597, by rfl⟩ : syracuseStep 2871413 = 269195) (by norm_num)
theorem B1914275 : Blo 1913435 1914275 := bstep (se 1 (by rfl) ⟨1435706, by rfl⟩ : syracuseStep 1914275 = 2871413) B2871413
theorem B3634141 : Blo 1913435 3634141 := bbase (se 3 (by rfl) ⟨681401, by rfl⟩ : syracuseStep 3634141 = 1362803) (by norm_num)
theorem B4845521 : Blo 1913435 4845521 := bstep (se 2 (by rfl) ⟨1817070, by rfl⟩ : syracuseStep 4845521 = 3634141) B3634141
theorem B3230347 : Blo 1913435 3230347 := bstep (se 1 (by rfl) ⟨2422760, by rfl⟩ : syracuseStep 3230347 = 4845521) B4845521
theorem B4307129 : Blo 1913435 4307129 := bstep (se 2 (by rfl) ⟨1615173, by rfl⟩ : syracuseStep 4307129 = 3230347) B3230347
theorem B2871419 : Blo 1913435 2871419 := bstep (se 1 (by rfl) ⟨2153564, by rfl⟩ : syracuseStep 2871419 = 4307129) B4307129
theorem B1914279 : Blo 1913435 1914279 := bstep (se 1 (by rfl) ⟨1435709, by rfl⟩ : syracuseStep 1914279 = 2871419) B2871419
theorem B2153569 : Blo 1913435 2153569 := bbase (se 2 (by rfl) ⟨807588, by rfl⟩ : syracuseStep 2153569 = 1615177) (by norm_num)
theorem B2871425 : Blo 1913435 2871425 := bstep (se 2 (by rfl) ⟨1076784, by rfl⟩ : syracuseStep 2871425 = 2153569) B2153569
theorem B1914283 : Blo 1913435 1914283 := bstep (se 1 (by rfl) ⟨1435712, by rfl⟩ : syracuseStep 1914283 = 2871425) B2871425
theorem B4845541 : Blo 1913435 4845541 := bbase (se 4 (by rfl) ⟨454269, by rfl⟩ : syracuseStep 4845541 = 908539) (by norm_num)
theorem B6460721 : Blo 1913435 6460721 := bstep (se 2 (by rfl) ⟨2422770, by rfl⟩ : syracuseStep 6460721 = 4845541) B4845541
theorem B4307147 : Blo 1913435 4307147 := bstep (se 1 (by rfl) ⟨3230360, by rfl⟩ : syracuseStep 4307147 = 6460721) B6460721
theorem B2871431 : Blo 1913435 2871431 := bstep (se 1 (by rfl) ⟨2153573, by rfl⟩ : syracuseStep 2871431 = 4307147) B4307147
theorem B1914287 : Blo 1913435 1914287 := bstep (se 1 (by rfl) ⟨1435715, by rfl⟩ : syracuseStep 1914287 = 2871431) B2871431
theorem B2871437 : Blo 1913435 2871437 := bbase (se 3 (by rfl) ⟨538394, by rfl⟩ : syracuseStep 2871437 = 1076789) (by norm_num)
theorem B1914291 : Blo 1913435 1914291 := bstep (se 1 (by rfl) ⟨1435718, by rfl⟩ : syracuseStep 1914291 = 2871437) B2871437
theorem B4307165 : Blo 1913435 4307165 := bbase (se 3 (by rfl) ⟨807593, by rfl⟩ : syracuseStep 4307165 = 1615187) (by norm_num)
theorem B2871443 : Blo 1913435 2871443 := bstep (se 1 (by rfl) ⟨2153582, by rfl⟩ : syracuseStep 2871443 = 4307165) B4307165
theorem B1914295 : Blo 1913435 1914295 := bstep (se 1 (by rfl) ⟨1435721, by rfl⟩ : syracuseStep 1914295 = 2871443) B2871443
theorem B3230381 : Blo 1913435 3230381 := bbase (se 3 (by rfl) ⟨605696, by rfl⟩ : syracuseStep 3230381 = 1211393) (by norm_num)
theorem B2153587 : Blo 1913435 2153587 := bstep (se 1 (by rfl) ⟨1615190, by rfl⟩ : syracuseStep 2153587 = 3230381) B3230381
theorem B2871449 : Blo 1913435 2871449 := bstep (se 2 (by rfl) ⟨1076793, by rfl⟩ : syracuseStep 2871449 = 2153587) B2153587
theorem B1914299 : Blo 1913435 1914299 := bstep (se 1 (by rfl) ⟨1435724, by rfl⟩ : syracuseStep 1914299 = 2871449) B2871449
theorem B13097845 : Blo 1913435 13097845 := bbase (se 5 (by rfl) ⟨613961, by rfl⟩ : syracuseStep 13097845 = 1227923) (by norm_num)
theorem B69855173 : Blo 1913435 69855173 := bstep (se 4 (by rfl) ⟨6548922, by rfl⟩ : syracuseStep 69855173 = 13097845) B13097845
theorem B46570115 : Blo 1913435 46570115 := bstep (se 1 (by rfl) ⟨34927586, by rfl⟩ : syracuseStep 46570115 = 69855173) B69855173
theorem B31046743 : Blo 1913435 31046743 := bstep (se 1 (by rfl) ⟨23285057, by rfl⟩ : syracuseStep 31046743 = 46570115) B46570115
theorem B41395657 : Blo 1913435 41395657 := bstep (se 2 (by rfl) ⟨15523371, by rfl⟩ : syracuseStep 41395657 = 31046743) B31046743
theorem B55194209 : Blo 1913435 55194209 := bstep (se 2 (by rfl) ⟨20697828, by rfl⟩ : syracuseStep 55194209 = 41395657) B41395657
theorem B36796139 : Blo 1913435 36796139 := bstep (se 1 (by rfl) ⟨27597104, by rfl⟩ : syracuseStep 36796139 = 55194209) B55194209
theorem B24530759 : Blo 1913435 24530759 := bstep (se 1 (by rfl) ⟨18398069, by rfl⟩ : syracuseStep 24530759 = 36796139) B36796139
theorem B16353839 : Blo 1913435 16353839 := bstep (se 1 (by rfl) ⟨12265379, by rfl⟩ : syracuseStep 16353839 = 24530759) B24530759
theorem B10902559 : Blo 1913435 10902559 := bstep (se 1 (by rfl) ⟨8176919, by rfl⟩ : syracuseStep 10902559 = 16353839) B16353839
theorem B14536745 : Blo 1913435 14536745 := bstep (se 2 (by rfl) ⟨5451279, by rfl⟩ : syracuseStep 14536745 = 10902559) B10902559
theorem B9691163 : Blo 1913435 9691163 := bstep (se 1 (by rfl) ⟨7268372, by rfl⟩ : syracuseStep 9691163 = 14536745) B14536745
theorem B6460775 : Blo 1913435 6460775 := bstep (se 1 (by rfl) ⟨4845581, by rfl⟩ : syracuseStep 6460775 = 9691163) B9691163
theorem B4307183 : Blo 1913435 4307183 := bstep (se 1 (by rfl) ⟨3230387, by rfl⟩ : syracuseStep 4307183 = 6460775) B6460775
theorem B2871455 : Blo 1913435 2871455 := bstep (se 1 (by rfl) ⟨2153591, by rfl⟩ : syracuseStep 2871455 = 4307183) B4307183
theorem B1914303 : Blo 1913435 1914303 := bstep (se 1 (by rfl) ⟨1435727, by rfl⟩ : syracuseStep 1914303 = 2871455) B2871455
theorem B2871461 : Blo 1913435 2871461 := bbase (se 4 (by rfl) ⟨269199, by rfl⟩ : syracuseStep 2871461 = 538399) (by norm_num)
theorem B1914307 : Blo 1913435 1914307 := bstep (se 1 (by rfl) ⟨1435730, by rfl⟩ : syracuseStep 1914307 = 2871461) B2871461
theorem B2422801 : Blo 1913435 2422801 := bbase (se 2 (by rfl) ⟨908550, by rfl⟩ : syracuseStep 2422801 = 1817101) (by norm_num)
theorem B3230401 : Blo 1913435 3230401 := bstep (se 2 (by rfl) ⟨1211400, by rfl⟩ : syracuseStep 3230401 = 2422801) B2422801
theorem B4307201 : Blo 1913435 4307201 := bstep (se 2 (by rfl) ⟨1615200, by rfl⟩ : syracuseStep 4307201 = 3230401) B3230401
theorem B2871467 : Blo 1913435 2871467 := bstep (se 1 (by rfl) ⟨2153600, by rfl⟩ : syracuseStep 2871467 = 4307201) B4307201
theorem B1914311 : Blo 1913435 1914311 := bstep (se 1 (by rfl) ⟨1435733, by rfl⟩ : syracuseStep 1914311 = 2871467) B2871467
theorem B2153605 : Blo 1913435 2153605 := bbase (se 4 (by rfl) ⟨201900, by rfl⟩ : syracuseStep 2153605 = 403801) (by norm_num)
theorem B2871473 : Blo 1913435 2871473 := bstep (se 2 (by rfl) ⟨1076802, by rfl⟩ : syracuseStep 2871473 = 2153605) B2153605
theorem B1914315 : Blo 1913435 1914315 := bstep (se 1 (by rfl) ⟨1435736, by rfl⟩ : syracuseStep 1914315 = 2871473) B2871473
theorem B3880877 : Blo 1913435 3880877 := bbase (se 3 (by rfl) ⟨727664, by rfl⟩ : syracuseStep 3880877 = 1455329) (by norm_num)
theorem B10349005 : Blo 1913435 10349005 := bstep (se 3 (by rfl) ⟨1940438, by rfl⟩ : syracuseStep 10349005 = 3880877) B3880877
theorem B13798673 : Blo 1913435 13798673 := bstep (se 2 (by rfl) ⟨5174502, by rfl⟩ : syracuseStep 13798673 = 10349005) B10349005
theorem B9199115 : Blo 1913435 9199115 := bstep (se 1 (by rfl) ⟨6899336, by rfl⟩ : syracuseStep 9199115 = 13798673) B13798673
theorem B6132743 : Blo 1913435 6132743 := bstep (se 1 (by rfl) ⟨4599557, by rfl⟩ : syracuseStep 6132743 = 9199115) B9199115
theorem B4088495 : Blo 1913435 4088495 := bstep (se 1 (by rfl) ⟨3066371, by rfl⟩ : syracuseStep 4088495 = 6132743) B6132743
theorem B2725663 : Blo 1913435 2725663 := bstep (se 1 (by rfl) ⟨2044247, by rfl⟩ : syracuseStep 2725663 = 4088495) B4088495
theorem B3634217 : Blo 1913435 3634217 := bstep (se 2 (by rfl) ⟨1362831, by rfl⟩ : syracuseStep 3634217 = 2725663) B2725663
theorem B2422811 : Blo 1913435 2422811 := bstep (se 1 (by rfl) ⟨1817108, by rfl⟩ : syracuseStep 2422811 = 3634217) B3634217
theorem B6460829 : Blo 1913435 6460829 := bstep (se 3 (by rfl) ⟨1211405, by rfl⟩ : syracuseStep 6460829 = 2422811) B2422811
theorem B4307219 : Blo 1913435 4307219 := bstep (se 1 (by rfl) ⟨3230414, by rfl⟩ : syracuseStep 4307219 = 6460829) B6460829
theorem B2871479 : Blo 1913435 2871479 := bstep (se 1 (by rfl) ⟨2153609, by rfl⟩ : syracuseStep 2871479 = 4307219) B4307219
theorem B1914319 : Blo 1913435 1914319 := bstep (se 1 (by rfl) ⟨1435739, by rfl⟩ : syracuseStep 1914319 = 2871479) B2871479
theorem B2871485 : Blo 1913435 2871485 := bbase (se 3 (by rfl) ⟨538403, by rfl⟩ : syracuseStep 2871485 = 1076807) (by norm_num)
theorem B1914323 : Blo 1913435 1914323 := bstep (se 1 (by rfl) ⟨1435742, by rfl⟩ : syracuseStep 1914323 = 2871485) B2871485
theorem B4307237 : Blo 1913435 4307237 := bbase (se 4 (by rfl) ⟨403803, by rfl⟩ : syracuseStep 4307237 = 807607) (by norm_num)
theorem B2871491 : Blo 1913435 2871491 := bstep (se 1 (by rfl) ⟨2153618, by rfl⟩ : syracuseStep 2871491 = 4307237) B4307237
theorem B1914327 : Blo 1913435 1914327 := bstep (se 1 (by rfl) ⟨1435745, by rfl⟩ : syracuseStep 1914327 = 2871491) B2871491
theorem B4845653 : Blo 1913435 4845653 := bbase (se 8 (by rfl) ⟨28392, by rfl⟩ : syracuseStep 4845653 = 56785) (by norm_num)
theorem B3230435 : Blo 1913435 3230435 := bstep (se 1 (by rfl) ⟨2422826, by rfl⟩ : syracuseStep 3230435 = 4845653) B4845653
theorem B2153623 : Blo 1913435 2153623 := bstep (se 1 (by rfl) ⟨1615217, by rfl⟩ : syracuseStep 2153623 = 3230435) B3230435
theorem B2871497 : Blo 1913435 2871497 := bstep (se 2 (by rfl) ⟨1076811, by rfl⟩ : syracuseStep 2871497 = 2153623) B2153623
theorem B1914331 : Blo 1913435 1914331 := bstep (se 1 (by rfl) ⟨1435748, by rfl⟩ : syracuseStep 1914331 = 2871497) B2871497
theorem B3880909 : Blo 1913435 3880909 := bbase (se 3 (by rfl) ⟨727670, by rfl⟩ : syracuseStep 3880909 = 1455341) (by norm_num)
theorem B5174545 : Blo 1913435 5174545 := bstep (se 2 (by rfl) ⟨1940454, by rfl⟩ : syracuseStep 5174545 = 3880909) B3880909
theorem B6899393 : Blo 1913435 6899393 := bstep (se 2 (by rfl) ⟨2587272, by rfl⟩ : syracuseStep 6899393 = 5174545) B5174545
theorem B4599595 : Blo 1913435 4599595 := bstep (se 1 (by rfl) ⟨3449696, by rfl⟩ : syracuseStep 4599595 = 6899393) B6899393
theorem B6132793 : Blo 1913435 6132793 := bstep (se 2 (by rfl) ⟨2299797, by rfl⟩ : syracuseStep 6132793 = 4599595) B4599595
theorem B8177057 : Blo 1913435 8177057 := bstep (se 2 (by rfl) ⟨3066396, by rfl⟩ : syracuseStep 8177057 = 6132793) B6132793
theorem B5451371 : Blo 1913435 5451371 := bstep (se 1 (by rfl) ⟨4088528, by rfl⟩ : syracuseStep 5451371 = 8177057) B8177057
theorem B3634247 : Blo 1913435 3634247 := bstep (se 1 (by rfl) ⟨2725685, by rfl⟩ : syracuseStep 3634247 = 5451371) B5451371
theorem B9691325 : Blo 1913435 9691325 := bstep (se 3 (by rfl) ⟨1817123, by rfl⟩ : syracuseStep 9691325 = 3634247) B3634247
theorem B6460883 : Blo 1913435 6460883 := bstep (se 1 (by rfl) ⟨4845662, by rfl⟩ : syracuseStep 6460883 = 9691325) B9691325
theorem B4307255 : Blo 1913435 4307255 := bstep (se 1 (by rfl) ⟨3230441, by rfl⟩ : syracuseStep 4307255 = 6460883) B6460883
theorem B2871503 : Blo 1913435 2871503 := bstep (se 1 (by rfl) ⟨2153627, by rfl⟩ : syracuseStep 2871503 = 4307255) B4307255
theorem B1914335 : Blo 1913435 1914335 := bstep (se 1 (by rfl) ⟨1435751, by rfl⟩ : syracuseStep 1914335 = 2871503) B2871503
theorem B2871509 : Blo 1913435 2871509 := bbase (se 7 (by rfl) ⟨33650, by rfl⟩ : syracuseStep 2871509 = 67301) (by norm_num)
theorem B1914339 : Blo 1913435 1914339 := bstep (se 1 (by rfl) ⟨1435754, by rfl⟩ : syracuseStep 1914339 = 2871509) B2871509
theorem B2044273 : Blo 1913435 2044273 := bbase (se 2 (by rfl) ⟨766602, by rfl⟩ : syracuseStep 2044273 = 1533205) (by norm_num)
theorem B2725697 : Blo 1913435 2725697 := bstep (se 2 (by rfl) ⟨1022136, by rfl⟩ : syracuseStep 2725697 = 2044273) B2044273
theorem B7268525 : Blo 1913435 7268525 := bstep (se 3 (by rfl) ⟨1362848, by rfl⟩ : syracuseStep 7268525 = 2725697) B2725697
theorem B4845683 : Blo 1913435 4845683 := bstep (se 1 (by rfl) ⟨3634262, by rfl⟩ : syracuseStep 4845683 = 7268525) B7268525
theorem B3230455 : Blo 1913435 3230455 := bstep (se 1 (by rfl) ⟨2422841, by rfl⟩ : syracuseStep 3230455 = 4845683) B4845683
theorem B4307273 : Blo 1913435 4307273 := bstep (se 2 (by rfl) ⟨1615227, by rfl⟩ : syracuseStep 4307273 = 3230455) B3230455
theorem B2871515 : Blo 1913435 2871515 := bstep (se 1 (by rfl) ⟨2153636, by rfl⟩ : syracuseStep 2871515 = 4307273) B4307273
theorem B1914343 : Blo 1913435 1914343 := bstep (se 1 (by rfl) ⟨1435757, by rfl⟩ : syracuseStep 1914343 = 2871515) B2871515
theorem B2153641 : Blo 1913435 2153641 := bbase (se 2 (by rfl) ⟨807615, by rfl⟩ : syracuseStep 2153641 = 1615231) (by norm_num)
theorem B2871521 : Blo 1913435 2871521 := bstep (se 2 (by rfl) ⟨1076820, by rfl⟩ : syracuseStep 2871521 = 2153641) B2153641
theorem B1914347 : Blo 1913435 1914347 := bstep (se 1 (by rfl) ⟨1435760, by rfl⟩ : syracuseStep 1914347 = 2871521) B2871521
theorem B8177125 : Blo 1913435 8177125 := bbase (se 4 (by rfl) ⟨766605, by rfl⟩ : syracuseStep 8177125 = 1533211) (by norm_num)
theorem B10902833 : Blo 1913435 10902833 := bstep (se 2 (by rfl) ⟨4088562, by rfl⟩ : syracuseStep 10902833 = 8177125) B8177125
theorem B7268555 : Blo 1913435 7268555 := bstep (se 1 (by rfl) ⟨5451416, by rfl⟩ : syracuseStep 7268555 = 10902833) B10902833
theorem B4845703 : Blo 1913435 4845703 := bstep (se 1 (by rfl) ⟨3634277, by rfl⟩ : syracuseStep 4845703 = 7268555) B7268555
theorem B6460937 : Blo 1913435 6460937 := bstep (se 2 (by rfl) ⟨2422851, by rfl⟩ : syracuseStep 6460937 = 4845703) B4845703
theorem B4307291 : Blo 1913435 4307291 := bstep (se 1 (by rfl) ⟨3230468, by rfl⟩ : syracuseStep 4307291 = 6460937) B6460937
theorem B2871527 : Blo 1913435 2871527 := bstep (se 1 (by rfl) ⟨2153645, by rfl⟩ : syracuseStep 2871527 = 4307291) B4307291
theorem B1914351 : Blo 1913435 1914351 := bstep (se 1 (by rfl) ⟨1435763, by rfl⟩ : syracuseStep 1914351 = 2871527) B2871527
theorem B2871533 : Blo 1913435 2871533 := bbase (se 3 (by rfl) ⟨538412, by rfl⟩ : syracuseStep 2871533 = 1076825) (by norm_num)
theorem B1914355 : Blo 1913435 1914355 := bstep (se 1 (by rfl) ⟨1435766, by rfl⟩ : syracuseStep 1914355 = 2871533) B2871533
theorem B4307309 : Blo 1913435 4307309 := bbase (se 3 (by rfl) ⟨807620, by rfl⟩ : syracuseStep 4307309 = 1615241) (by norm_num)
theorem B2871539 : Blo 1913435 2871539 := bstep (se 1 (by rfl) ⟨2153654, by rfl⟩ : syracuseStep 2871539 = 4307309) B4307309
theorem B1914359 : Blo 1913435 1914359 := bstep (se 1 (by rfl) ⟨1435769, by rfl⟩ : syracuseStep 1914359 = 2871539) B2871539
theorem B3634301 : Blo 1913435 3634301 := bbase (se 3 (by rfl) ⟨681431, by rfl⟩ : syracuseStep 3634301 = 1362863) (by norm_num)
theorem B2422867 : Blo 1913435 2422867 := bstep (se 1 (by rfl) ⟨1817150, by rfl⟩ : syracuseStep 2422867 = 3634301) B3634301
theorem B3230489 : Blo 1913435 3230489 := bstep (se 2 (by rfl) ⟨1211433, by rfl⟩ : syracuseStep 3230489 = 2422867) B2422867
theorem B2153659 : Blo 1913435 2153659 := bstep (se 1 (by rfl) ⟨1615244, by rfl⟩ : syracuseStep 2153659 = 3230489) B3230489
theorem B2871545 : Blo 1913435 2871545 := bstep (se 2 (by rfl) ⟨1076829, by rfl⟩ : syracuseStep 2871545 = 2153659) B2153659
theorem B1914363 : Blo 1913435 1914363 := bstep (se 1 (by rfl) ⟨1435772, by rfl⟩ : syracuseStep 1914363 = 2871545) B2871545
theorem B3880973 : Blo 1913435 3880973 := bbase (se 3 (by rfl) ⟨727682, by rfl⟩ : syracuseStep 3880973 = 1455365) (by norm_num)
theorem B10349261 : Blo 1913435 10349261 := bstep (se 3 (by rfl) ⟨1940486, by rfl⟩ : syracuseStep 10349261 = 3880973) B3880973
theorem B6899507 : Blo 1913435 6899507 := bstep (se 1 (by rfl) ⟨5174630, by rfl⟩ : syracuseStep 6899507 = 10349261) B10349261
theorem B4599671 : Blo 1913435 4599671 := bstep (se 1 (by rfl) ⟨3449753, by rfl⟩ : syracuseStep 4599671 = 6899507) B6899507
theorem B49063157 : Blo 1913435 49063157 := bstep (se 5 (by rfl) ⟨2299835, by rfl⟩ : syracuseStep 49063157 = 4599671) B4599671
theorem B32708771 : Blo 1913435 32708771 := bstep (se 1 (by rfl) ⟨24531578, by rfl⟩ : syracuseStep 32708771 = 49063157) B49063157
theorem B21805847 : Blo 1913435 21805847 := bstep (se 1 (by rfl) ⟨16354385, by rfl⟩ : syracuseStep 21805847 = 32708771) B32708771
theorem B14537231 : Blo 1913435 14537231 := bstep (se 1 (by rfl) ⟨10902923, by rfl⟩ : syracuseStep 14537231 = 21805847) B21805847
theorem B9691487 : Blo 1913435 9691487 := bstep (se 1 (by rfl) ⟨7268615, by rfl⟩ : syracuseStep 9691487 = 14537231) B14537231
theorem B6460991 : Blo 1913435 6460991 := bstep (se 1 (by rfl) ⟨4845743, by rfl⟩ : syracuseStep 6460991 = 9691487) B9691487
theorem B4307327 : Blo 1913435 4307327 := bstep (se 1 (by rfl) ⟨3230495, by rfl⟩ : syracuseStep 4307327 = 6460991) B6460991
theorem B2871551 : Blo 1913435 2871551 := bstep (se 1 (by rfl) ⟨2153663, by rfl⟩ : syracuseStep 2871551 = 4307327) B4307327
theorem B1914367 : Blo 1913435 1914367 := bstep (se 1 (by rfl) ⟨1435775, by rfl⟩ : syracuseStep 1914367 = 2871551) B2871551
theorem B2871557 : Blo 1913435 2871557 := bbase (se 4 (by rfl) ⟨269208, by rfl⟩ : syracuseStep 2871557 = 538417) (by norm_num)
theorem B1914371 : Blo 1913435 1914371 := bstep (se 1 (by rfl) ⟨1435778, by rfl⟩ : syracuseStep 1914371 = 2871557) B2871557
theorem B3230509 : Blo 1913435 3230509 := bbase (se 3 (by rfl) ⟨605720, by rfl⟩ : syracuseStep 3230509 = 1211441) (by norm_num)
theorem B4307345 : Blo 1913435 4307345 := bstep (se 2 (by rfl) ⟨1615254, by rfl⟩ : syracuseStep 4307345 = 3230509) B3230509
theorem B2871563 : Blo 1913435 2871563 := bstep (se 1 (by rfl) ⟨2153672, by rfl⟩ : syracuseStep 2871563 = 4307345) B4307345
theorem B1914375 : Blo 1913435 1914375 := bstep (se 1 (by rfl) ⟨1435781, by rfl⟩ : syracuseStep 1914375 = 2871563) B2871563
theorem B2153677 : Blo 1913435 2153677 := bbase (se 3 (by rfl) ⟨403814, by rfl⟩ : syracuseStep 2153677 = 807629) (by norm_num)
theorem B2871569 : Blo 1913435 2871569 := bstep (se 2 (by rfl) ⟨1076838, by rfl⟩ : syracuseStep 2871569 = 2153677) B2153677
theorem B1914379 : Blo 1913435 1914379 := bstep (se 1 (by rfl) ⟨1435784, by rfl⟩ : syracuseStep 1914379 = 2871569) B2871569
theorem B6461045 : Blo 1913435 6461045 := bbase (se 5 (by rfl) ⟨302861, by rfl⟩ : syracuseStep 6461045 = 605723) (by norm_num)
theorem B4307363 : Blo 1913435 4307363 := bstep (se 1 (by rfl) ⟨3230522, by rfl⟩ : syracuseStep 4307363 = 6461045) B6461045
theorem B2871575 : Blo 1913435 2871575 := bstep (se 1 (by rfl) ⟨2153681, by rfl⟩ : syracuseStep 2871575 = 4307363) B4307363
theorem B1914383 : Blo 1913435 1914383 := bstep (se 1 (by rfl) ⟨1435787, by rfl⟩ : syracuseStep 1914383 = 2871575) B2871575
theorem B2871581 : Blo 1913435 2871581 := bbase (se 3 (by rfl) ⟨538421, by rfl⟩ : syracuseStep 2871581 = 1076843) (by norm_num)
theorem B1914387 : Blo 1913435 1914387 := bstep (se 1 (by rfl) ⟨1435790, by rfl⟩ : syracuseStep 1914387 = 2871581) B2871581
theorem B4307381 : Blo 1913435 4307381 := bbase (se 5 (by rfl) ⟨201908, by rfl⟩ : syracuseStep 4307381 = 403817) (by norm_num)
theorem B2871587 : Blo 1913435 2871587 := bstep (se 1 (by rfl) ⟨2153690, by rfl⟩ : syracuseStep 2871587 = 4307381) B4307381
theorem B1914391 : Blo 1913435 1914391 := bstep (se 1 (by rfl) ⟨1435793, by rfl⟩ : syracuseStep 1914391 = 2871587) B2871587
theorem B3066493 : Blo 1913435 3066493 := bbase (se 3 (by rfl) ⟨574967, by rfl⟩ : syracuseStep 3066493 = 1149935) (by norm_num)
theorem B4088657 : Blo 1913435 4088657 := bstep (se 2 (by rfl) ⟨1533246, by rfl⟩ : syracuseStep 4088657 = 3066493) B3066493
theorem B10903085 : Blo 1913435 10903085 := bstep (se 3 (by rfl) ⟨2044328, by rfl⟩ : syracuseStep 10903085 = 4088657) B4088657
theorem B7268723 : Blo 1913435 7268723 := bstep (se 1 (by rfl) ⟨5451542, by rfl⟩ : syracuseStep 7268723 = 10903085) B10903085
theorem B4845815 : Blo 1913435 4845815 := bstep (se 1 (by rfl) ⟨3634361, by rfl⟩ : syracuseStep 4845815 = 7268723) B7268723
theorem B3230543 : Blo 1913435 3230543 := bstep (se 1 (by rfl) ⟨2422907, by rfl⟩ : syracuseStep 3230543 = 4845815) B4845815
theorem B2153695 : Blo 1913435 2153695 := bstep (se 1 (by rfl) ⟨1615271, by rfl⟩ : syracuseStep 2153695 = 3230543) B3230543
theorem B2871593 : Blo 1913435 2871593 := bstep (se 2 (by rfl) ⟨1076847, by rfl⟩ : syracuseStep 2871593 = 2153695) B2153695
theorem B1914395 : Blo 1913435 1914395 := bstep (se 1 (by rfl) ⟨1435796, by rfl⟩ : syracuseStep 1914395 = 2871593) B2871593
theorem B4599749 : Blo 1913435 4599749 := bbase (se 4 (by rfl) ⟨431226, by rfl⟩ : syracuseStep 4599749 = 862453) (by norm_num)
theorem B3066499 : Blo 1913435 3066499 := bstep (se 1 (by rfl) ⟨2299874, by rfl⟩ : syracuseStep 3066499 = 4599749) B4599749
theorem B4088665 : Blo 1913435 4088665 := bstep (se 2 (by rfl) ⟨1533249, by rfl⟩ : syracuseStep 4088665 = 3066499) B3066499
theorem B5451553 : Blo 1913435 5451553 := bstep (se 2 (by rfl) ⟨2044332, by rfl⟩ : syracuseStep 5451553 = 4088665) B4088665
theorem B7268737 : Blo 1913435 7268737 := bstep (se 2 (by rfl) ⟨2725776, by rfl⟩ : syracuseStep 7268737 = 5451553) B5451553
theorem B9691649 : Blo 1913435 9691649 := bstep (se 2 (by rfl) ⟨3634368, by rfl⟩ : syracuseStep 9691649 = 7268737) B7268737
theorem B6461099 : Blo 1913435 6461099 := bstep (se 1 (by rfl) ⟨4845824, by rfl⟩ : syracuseStep 6461099 = 9691649) B9691649
theorem B4307399 : Blo 1913435 4307399 := bstep (se 1 (by rfl) ⟨3230549, by rfl⟩ : syracuseStep 4307399 = 6461099) B6461099
theorem B2871599 : Blo 1913435 2871599 := bstep (se 1 (by rfl) ⟨2153699, by rfl⟩ : syracuseStep 2871599 = 4307399) B4307399
theorem B1914399 : Blo 1913435 1914399 := bstep (se 1 (by rfl) ⟨1435799, by rfl⟩ : syracuseStep 1914399 = 2871599) B2871599
theorem B2871605 : Blo 1913435 2871605 := bbase (se 5 (by rfl) ⟨134606, by rfl⟩ : syracuseStep 2871605 = 269213) (by norm_num)
theorem B1914403 : Blo 1913435 1914403 := bstep (se 1 (by rfl) ⟨1435802, by rfl⟩ : syracuseStep 1914403 = 2871605) B2871605
theorem B4845845 : Blo 1913435 4845845 := bbase (se 6 (by rfl) ⟨113574, by rfl⟩ : syracuseStep 4845845 = 227149) (by norm_num)
theorem B3230563 : Blo 1913435 3230563 := bstep (se 1 (by rfl) ⟨2422922, by rfl⟩ : syracuseStep 3230563 = 4845845) B4845845
theorem B4307417 : Blo 1913435 4307417 := bstep (se 2 (by rfl) ⟨1615281, by rfl⟩ : syracuseStep 4307417 = 3230563) B3230563
theorem B2871611 : Blo 1913435 2871611 := bstep (se 1 (by rfl) ⟨2153708, by rfl⟩ : syracuseStep 2871611 = 4307417) B4307417
theorem B1914407 : Blo 1913435 1914407 := bstep (se 1 (by rfl) ⟨1435805, by rfl⟩ : syracuseStep 1914407 = 2871611) B2871611
theorem B2153713 : Blo 1913435 2153713 := bbase (se 2 (by rfl) ⟨807642, by rfl⟩ : syracuseStep 2153713 = 1615285) (by norm_num)
theorem B2871617 : Blo 1913435 2871617 := bstep (se 2 (by rfl) ⟨1076856, by rfl⟩ : syracuseStep 2871617 = 2153713) B2153713
theorem B1914411 : Blo 1913435 1914411 := bstep (se 1 (by rfl) ⟨1435808, by rfl⟩ : syracuseStep 1914411 = 2871617) B2871617
theorem B13987637 : Blo 1913435 13987637 := bbase (se 5 (by rfl) ⟨655670, by rfl⟩ : syracuseStep 13987637 = 1311341) (by norm_num)
theorem B9325091 : Blo 1913435 9325091 := bstep (se 1 (by rfl) ⟨6993818, by rfl⟩ : syracuseStep 9325091 = 13987637) B13987637
theorem B24866909 : Blo 1913435 24866909 := bstep (se 3 (by rfl) ⟨4662545, by rfl⟩ : syracuseStep 24866909 = 9325091) B9325091
theorem B16577939 : Blo 1913435 16577939 := bstep (se 1 (by rfl) ⟨12433454, by rfl⟩ : syracuseStep 16577939 = 24866909) B24866909
theorem B11051959 : Blo 1913435 11051959 := bstep (se 1 (by rfl) ⟨8288969, by rfl⟩ : syracuseStep 11051959 = 16577939) B16577939
theorem B14735945 : Blo 1913435 14735945 := bstep (se 2 (by rfl) ⟨5525979, by rfl⟩ : syracuseStep 14735945 = 11051959) B11051959
theorem B9823963 : Blo 1913435 9823963 := bstep (se 1 (by rfl) ⟨7367972, by rfl⟩ : syracuseStep 9823963 = 14735945) B14735945
theorem B13098617 : Blo 1913435 13098617 := bstep (se 2 (by rfl) ⟨4911981, by rfl⟩ : syracuseStep 13098617 = 9823963) B9823963
theorem B8732411 : Blo 1913435 8732411 := bstep (se 1 (by rfl) ⟨6549308, by rfl⟩ : syracuseStep 8732411 = 13098617) B13098617
theorem B5821607 : Blo 1913435 5821607 := bstep (se 1 (by rfl) ⟨4366205, by rfl⟩ : syracuseStep 5821607 = 8732411) B8732411
theorem B3881071 : Blo 1913435 3881071 := bstep (se 1 (by rfl) ⟨2910803, by rfl⟩ : syracuseStep 3881071 = 5821607) B5821607
theorem B5174761 : Blo 1913435 5174761 := bstep (se 2 (by rfl) ⟨1940535, by rfl⟩ : syracuseStep 5174761 = 3881071) B3881071
theorem B6899681 : Blo 1913435 6899681 := bstep (se 2 (by rfl) ⟨2587380, by rfl⟩ : syracuseStep 6899681 = 5174761) B5174761
theorem B18399149 : Blo 1913435 18399149 := bstep (se 3 (by rfl) ⟨3449840, by rfl⟩ : syracuseStep 18399149 = 6899681) B6899681
theorem B12266099 : Blo 1913435 12266099 := bstep (se 1 (by rfl) ⟨9199574, by rfl⟩ : syracuseStep 12266099 = 18399149) B18399149
theorem B8177399 : Blo 1913435 8177399 := bstep (se 1 (by rfl) ⟨6133049, by rfl⟩ : syracuseStep 8177399 = 12266099) B12266099
theorem B5451599 : Blo 1913435 5451599 := bstep (se 1 (by rfl) ⟨4088699, by rfl⟩ : syracuseStep 5451599 = 8177399) B8177399
theorem B3634399 : Blo 1913435 3634399 := bstep (se 1 (by rfl) ⟨2725799, by rfl⟩ : syracuseStep 3634399 = 5451599) B5451599
theorem B4845865 : Blo 1913435 4845865 := bstep (se 2 (by rfl) ⟨1817199, by rfl⟩ : syracuseStep 4845865 = 3634399) B3634399
theorem B6461153 : Blo 1913435 6461153 := bstep (se 2 (by rfl) ⟨2422932, by rfl⟩ : syracuseStep 6461153 = 4845865) B4845865
theorem B4307435 : Blo 1913435 4307435 := bstep (se 1 (by rfl) ⟨3230576, by rfl⟩ : syracuseStep 4307435 = 6461153) B6461153
theorem B2871623 : Blo 1913435 2871623 := bstep (se 1 (by rfl) ⟨2153717, by rfl⟩ : syracuseStep 2871623 = 4307435) B4307435
theorem B1914415 : Blo 1913435 1914415 := bstep (se 1 (by rfl) ⟨1435811, by rfl⟩ : syracuseStep 1914415 = 2871623) B2871623
theorem B2871629 : Blo 1913435 2871629 := bbase (se 3 (by rfl) ⟨538430, by rfl⟩ : syracuseStep 2871629 = 1076861) (by norm_num)
theorem B1914419 : Blo 1913435 1914419 := bstep (se 1 (by rfl) ⟨1435814, by rfl⟩ : syracuseStep 1914419 = 2871629) B2871629
theorem B4307453 : Blo 1913435 4307453 := bbase (se 3 (by rfl) ⟨807647, by rfl⟩ : syracuseStep 4307453 = 1615295) (by norm_num)
theorem B2871635 : Blo 1913435 2871635 := bstep (se 1 (by rfl) ⟨2153726, by rfl⟩ : syracuseStep 2871635 = 4307453) B4307453
theorem B1914423 : Blo 1913435 1914423 := bstep (se 1 (by rfl) ⟨1435817, by rfl⟩ : syracuseStep 1914423 = 2871635) B2871635
theorem B3230597 : Blo 1913435 3230597 := bbase (se 4 (by rfl) ⟨302868, by rfl⟩ : syracuseStep 3230597 = 605737) (by norm_num)
theorem B2153731 : Blo 1913435 2153731 := bstep (se 1 (by rfl) ⟨1615298, by rfl⟩ : syracuseStep 2153731 = 3230597) B3230597
theorem B2871641 : Blo 1913435 2871641 := bstep (se 2 (by rfl) ⟨1076865, by rfl⟩ : syracuseStep 2871641 = 2153731) B2153731
theorem B1914427 : Blo 1913435 1914427 := bstep (se 1 (by rfl) ⟨1435820, by rfl⟩ : syracuseStep 1914427 = 2871641) B2871641
theorem B14537717 : Blo 1913435 14537717 := bbase (se 5 (by rfl) ⟨681455, by rfl⟩ : syracuseStep 14537717 = 1362911) (by norm_num)
theorem B9691811 : Blo 1913435 9691811 := bstep (se 1 (by rfl) ⟨7268858, by rfl⟩ : syracuseStep 9691811 = 14537717) B14537717
theorem B6461207 : Blo 1913435 6461207 := bstep (se 1 (by rfl) ⟨4845905, by rfl⟩ : syracuseStep 6461207 = 9691811) B9691811
theorem B4307471 : Blo 1913435 4307471 := bstep (se 1 (by rfl) ⟨3230603, by rfl⟩ : syracuseStep 4307471 = 6461207) B6461207
theorem B2871647 : Blo 1913435 2871647 := bstep (se 1 (by rfl) ⟨2153735, by rfl⟩ : syracuseStep 2871647 = 4307471) B4307471
theorem B1914431 : Blo 1913435 1914431 := bstep (se 1 (by rfl) ⟨1435823, by rfl⟩ : syracuseStep 1914431 = 2871647) B2871647
theorem B2871653 : Blo 1913435 2871653 := bbase (se 4 (by rfl) ⟨269217, by rfl⟩ : syracuseStep 2871653 = 538435) (by norm_num)
theorem B1914435 : Blo 1913435 1914435 := bstep (se 1 (by rfl) ⟨1435826, by rfl⟩ : syracuseStep 1914435 = 2871653) B2871653
theorem B3634445 : Blo 1913435 3634445 := bbase (se 3 (by rfl) ⟨681458, by rfl⟩ : syracuseStep 3634445 = 1362917) (by norm_num)
theorem B2422963 : Blo 1913435 2422963 := bstep (se 1 (by rfl) ⟨1817222, by rfl⟩ : syracuseStep 2422963 = 3634445) B3634445
theorem B3230617 : Blo 1913435 3230617 := bstep (se 2 (by rfl) ⟨1211481, by rfl⟩ : syracuseStep 3230617 = 2422963) B2422963
theorem B4307489 : Blo 1913435 4307489 := bstep (se 2 (by rfl) ⟨1615308, by rfl⟩ : syracuseStep 4307489 = 3230617) B3230617
theorem B2871659 : Blo 1913435 2871659 := bstep (se 1 (by rfl) ⟨2153744, by rfl⟩ : syracuseStep 2871659 = 4307489) B4307489
theorem B1914439 : Blo 1913435 1914439 := bstep (se 1 (by rfl) ⟨1435829, by rfl⟩ : syracuseStep 1914439 = 2871659) B2871659
theorem B2153749 : Blo 1913435 2153749 := bbase (se 6 (by rfl) ⟨50478, by rfl⟩ : syracuseStep 2153749 = 100957) (by norm_num)
theorem B2871665 : Blo 1913435 2871665 := bstep (se 2 (by rfl) ⟨1076874, by rfl⟩ : syracuseStep 2871665 = 2153749) B2153749
theorem B1914443 : Blo 1913435 1914443 := bstep (se 1 (by rfl) ⟨1435832, by rfl⟩ : syracuseStep 1914443 = 2871665) B2871665
theorem B2422973 : Blo 1913435 2422973 := bbase (se 3 (by rfl) ⟨454307, by rfl⟩ : syracuseStep 2422973 = 908615) (by norm_num)
theorem B6461261 : Blo 1913435 6461261 := bstep (se 3 (by rfl) ⟨1211486, by rfl⟩ : syracuseStep 6461261 = 2422973) B2422973
theorem B4307507 : Blo 1913435 4307507 := bstep (se 1 (by rfl) ⟨3230630, by rfl⟩ : syracuseStep 4307507 = 6461261) B6461261
theorem B2871671 : Blo 1913435 2871671 := bstep (se 1 (by rfl) ⟨2153753, by rfl⟩ : syracuseStep 2871671 = 4307507) B4307507
theorem B1914447 : Blo 1913435 1914447 := bstep (se 1 (by rfl) ⟨1435835, by rfl⟩ : syracuseStep 1914447 = 2871671) B2871671
theorem B2871677 : Blo 1913435 2871677 := bbase (se 3 (by rfl) ⟨538439, by rfl⟩ : syracuseStep 2871677 = 1076879) (by norm_num)
theorem B1914451 : Blo 1913435 1914451 := bstep (se 1 (by rfl) ⟨1435838, by rfl⟩ : syracuseStep 1914451 = 2871677) B2871677
theorem B4307525 : Blo 1913435 4307525 := bbase (se 4 (by rfl) ⟨403830, by rfl⟩ : syracuseStep 4307525 = 807661) (by norm_num)
theorem B2871683 : Blo 1913435 2871683 := bstep (se 1 (by rfl) ⟨2153762, by rfl⟩ : syracuseStep 2871683 = 4307525) B4307525
theorem B1914455 : Blo 1913435 1914455 := bstep (se 1 (by rfl) ⟨1435841, by rfl⟩ : syracuseStep 1914455 = 2871683) B2871683
theorem B2044397 : Blo 1913435 2044397 := bbase (se 3 (by rfl) ⟨383324, by rfl⟩ : syracuseStep 2044397 = 766649) (by norm_num)
theorem B5451725 : Blo 1913435 5451725 := bstep (se 3 (by rfl) ⟨1022198, by rfl⟩ : syracuseStep 5451725 = 2044397) B2044397
theorem B3634483 : Blo 1913435 3634483 := bstep (se 1 (by rfl) ⟨2725862, by rfl⟩ : syracuseStep 3634483 = 5451725) B5451725
theorem B4845977 : Blo 1913435 4845977 := bstep (se 2 (by rfl) ⟨1817241, by rfl⟩ : syracuseStep 4845977 = 3634483) B3634483
theorem B3230651 : Blo 1913435 3230651 := bstep (se 1 (by rfl) ⟨2422988, by rfl⟩ : syracuseStep 3230651 = 4845977) B4845977
theorem B2153767 : Blo 1913435 2153767 := bstep (se 1 (by rfl) ⟨1615325, by rfl⟩ : syracuseStep 2153767 = 3230651) B3230651
theorem B2871689 : Blo 1913435 2871689 := bstep (se 2 (by rfl) ⟨1076883, by rfl⟩ : syracuseStep 2871689 = 2153767) B2153767
theorem B1914459 : Blo 1913435 1914459 := bstep (se 1 (by rfl) ⟨1435844, by rfl⟩ : syracuseStep 1914459 = 2871689) B2871689
theorem B9691973 : Blo 1913435 9691973 := bbase (se 4 (by rfl) ⟨908622, by rfl⟩ : syracuseStep 9691973 = 1817245) (by norm_num)
theorem B6461315 : Blo 1913435 6461315 := bstep (se 1 (by rfl) ⟨4845986, by rfl⟩ : syracuseStep 6461315 = 9691973) B9691973
theorem B4307543 : Blo 1913435 4307543 := bstep (se 1 (by rfl) ⟨3230657, by rfl⟩ : syracuseStep 4307543 = 6461315) B6461315
theorem B2871695 : Blo 1913435 2871695 := bstep (se 1 (by rfl) ⟨2153771, by rfl⟩ : syracuseStep 2871695 = 4307543) B4307543
theorem B1914463 : Blo 1913435 1914463 := bstep (se 1 (by rfl) ⟨1435847, by rfl⟩ : syracuseStep 1914463 = 2871695) B2871695
theorem B2871701 : Blo 1913435 2871701 := bbase (se 6 (by rfl) ⟨67305, by rfl⟩ : syracuseStep 2871701 = 134611) (by norm_num)
theorem B1914467 : Blo 1913435 1914467 := bstep (se 1 (by rfl) ⟨1435850, by rfl⟩ : syracuseStep 1914467 = 2871701) B2871701
theorem B2299961 : Blo 1913435 2299961 := bbase (se 2 (by rfl) ⟨862485, by rfl⟩ : syracuseStep 2299961 = 1724971) (by norm_num)
theorem B6133229 : Blo 1913435 6133229 := bstep (se 3 (by rfl) ⟨1149980, by rfl⟩ : syracuseStep 6133229 = 2299961) B2299961
theorem B4088819 : Blo 1913435 4088819 := bstep (se 1 (by rfl) ⟨3066614, by rfl⟩ : syracuseStep 4088819 = 6133229) B6133229
theorem B10903517 : Blo 1913435 10903517 := bstep (se 3 (by rfl) ⟨2044409, by rfl⟩ : syracuseStep 10903517 = 4088819) B4088819
theorem B7269011 : Blo 1913435 7269011 := bstep (se 1 (by rfl) ⟨5451758, by rfl⟩ : syracuseStep 7269011 = 10903517) B10903517
theorem B4846007 : Blo 1913435 4846007 := bstep (se 1 (by rfl) ⟨3634505, by rfl⟩ : syracuseStep 4846007 = 7269011) B7269011
theorem B3230671 : Blo 1913435 3230671 := bstep (se 1 (by rfl) ⟨2423003, by rfl⟩ : syracuseStep 3230671 = 4846007) B4846007
theorem B4307561 : Blo 1913435 4307561 := bstep (se 2 (by rfl) ⟨1615335, by rfl⟩ : syracuseStep 4307561 = 3230671) B3230671
theorem B2871707 : Blo 1913435 2871707 := bstep (se 1 (by rfl) ⟨2153780, by rfl⟩ : syracuseStep 2871707 = 4307561) B4307561
theorem B1914471 : Blo 1913435 1914471 := bstep (se 1 (by rfl) ⟨1435853, by rfl⟩ : syracuseStep 1914471 = 2871707) B2871707
theorem B2153785 : Blo 1913435 2153785 := bbase (se 2 (by rfl) ⟨807669, by rfl⟩ : syracuseStep 2153785 = 1615339) (by norm_num)
theorem B2871713 : Blo 1913435 2871713 := bstep (se 2 (by rfl) ⟨1076892, by rfl⟩ : syracuseStep 2871713 = 2153785) B2153785
theorem B1914475 : Blo 1913435 1914475 := bstep (se 1 (by rfl) ⟨1435856, by rfl⟩ : syracuseStep 1914475 = 2871713) B2871713
theorem B5451781 : Blo 1913435 5451781 := bbase (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) (by norm_num)
theorem B7269041 : Blo 1913435 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B4846027 : Blo 1913435 4846027 := bstep (se 1 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 4846027 = 7269041) B7269041
theorem B6461369 : Blo 1913435 6461369 := bstep (se 2 (by rfl) ⟨2423013, by rfl⟩ : syracuseStep 6461369 = 4846027) B4846027
theorem B4307579 : Blo 1913435 4307579 := bstep (se 1 (by rfl) ⟨3230684, by rfl⟩ : syracuseStep 4307579 = 6461369) B6461369
theorem B2871719 : Blo 1913435 2871719 := bstep (se 1 (by rfl) ⟨2153789, by rfl⟩ : syracuseStep 2871719 = 4307579) B4307579
theorem B1914479 : Blo 1913435 1914479 := bstep (se 1 (by rfl) ⟨1435859, by rfl⟩ : syracuseStep 1914479 = 2871719) B2871719
theorem B2871725 : Blo 1913435 2871725 := bbase (se 3 (by rfl) ⟨538448, by rfl⟩ : syracuseStep 2871725 = 1076897) (by norm_num)
theorem B1914483 : Blo 1913435 1914483 := bstep (se 1 (by rfl) ⟨1435862, by rfl⟩ : syracuseStep 1914483 = 2871725) B2871725
theorem B4307597 : Blo 1913435 4307597 := bbase (se 3 (by rfl) ⟨807674, by rfl⟩ : syracuseStep 4307597 = 1615349) (by norm_num)
theorem B2871731 : Blo 1913435 2871731 := bstep (se 1 (by rfl) ⟨2153798, by rfl⟩ : syracuseStep 2871731 = 4307597) B4307597
theorem B1914487 : Blo 1913435 1914487 := bstep (se 1 (by rfl) ⟨1435865, by rfl⟩ : syracuseStep 1914487 = 2871731) B2871731
theorem B2423029 : Blo 1913435 2423029 := bbase (se 5 (by rfl) ⟨113579, by rfl⟩ : syracuseStep 2423029 = 227159) (by norm_num)
theorem B3230705 : Blo 1913435 3230705 := bstep (se 2 (by rfl) ⟨1211514, by rfl⟩ : syracuseStep 3230705 = 2423029) B2423029
theorem B2153803 : Blo 1913435 2153803 := bstep (se 1 (by rfl) ⟨1615352, by rfl⟩ : syracuseStep 2153803 = 3230705) B3230705
theorem B2871737 : Blo 1913435 2871737 := bstep (se 2 (by rfl) ⟨1076901, by rfl⟩ : syracuseStep 2871737 = 2153803) B2153803
theorem B1914491 : Blo 1913435 1914491 := bstep (se 1 (by rfl) ⟨1435868, by rfl⟩ : syracuseStep 1914491 = 2871737) B2871737
theorem B36799829 : Blo 1913435 36799829 := bbase (se 12 (by rfl) ⟨13476, by rfl⟩ : syracuseStep 36799829 = 26953) (by norm_num)
theorem B24533219 : Blo 1913435 24533219 := bstep (se 1 (by rfl) ⟨18399914, by rfl⟩ : syracuseStep 24533219 = 36799829) B36799829
theorem B16355479 : Blo 1913435 16355479 := bstep (se 1 (by rfl) ⟨12266609, by rfl⟩ : syracuseStep 16355479 = 24533219) B24533219
theorem B21807305 : Blo 1913435 21807305 := bstep (se 2 (by rfl) ⟨8177739, by rfl⟩ : syracuseStep 21807305 = 16355479) B16355479
theorem B14538203 : Blo 1913435 14538203 := bstep (se 1 (by rfl) ⟨10903652, by rfl⟩ : syracuseStep 14538203 = 21807305) B21807305
theorem B9692135 : Blo 1913435 9692135 := bstep (se 1 (by rfl) ⟨7269101, by rfl⟩ : syracuseStep 9692135 = 14538203) B14538203
theorem B6461423 : Blo 1913435 6461423 := bstep (se 1 (by rfl) ⟨4846067, by rfl⟩ : syracuseStep 6461423 = 9692135) B9692135
theorem B4307615 : Blo 1913435 4307615 := bstep (se 1 (by rfl) ⟨3230711, by rfl⟩ : syracuseStep 4307615 = 6461423) B6461423
theorem B2871743 : Blo 1913435 2871743 := bstep (se 1 (by rfl) ⟨2153807, by rfl⟩ : syracuseStep 2871743 = 4307615) B4307615
theorem B1914495 : Blo 1913435 1914495 := bstep (se 1 (by rfl) ⟨1435871, by rfl⟩ : syracuseStep 1914495 = 2871743) B2871743
theorem B2871749 : Blo 1913435 2871749 := bbase (se 4 (by rfl) ⟨269226, by rfl⟩ : syracuseStep 2871749 = 538453) (by norm_num)
theorem B1914499 : Blo 1913435 1914499 := bstep (se 1 (by rfl) ⟨1435874, by rfl⟩ : syracuseStep 1914499 = 2871749) B2871749
theorem B3230725 : Blo 1913435 3230725 := bbase (se 4 (by rfl) ⟨302880, by rfl⟩ : syracuseStep 3230725 = 605761) (by norm_num)
theorem B4307633 : Blo 1913435 4307633 := bstep (se 2 (by rfl) ⟨1615362, by rfl⟩ : syracuseStep 4307633 = 3230725) B3230725
theorem B2871755 : Blo 1913435 2871755 := bstep (se 1 (by rfl) ⟨2153816, by rfl⟩ : syracuseStep 2871755 = 4307633) B4307633
theorem B1914503 : Blo 1913435 1914503 := bstep (se 1 (by rfl) ⟨1435877, by rfl⟩ : syracuseStep 1914503 = 2871755) B2871755
theorem B2153821 : Blo 1913435 2153821 := bbase (se 3 (by rfl) ⟨403841, by rfl⟩ : syracuseStep 2153821 = 807683) (by norm_num)
theorem B2871761 : Blo 1913435 2871761 := bstep (se 2 (by rfl) ⟨1076910, by rfl⟩ : syracuseStep 2871761 = 2153821) B2153821
theorem B1914507 : Blo 1913435 1914507 := bstep (se 1 (by rfl) ⟨1435880, by rfl⟩ : syracuseStep 1914507 = 2871761) B2871761
theorem B6461477 : Blo 1913435 6461477 := bbase (se 4 (by rfl) ⟨605763, by rfl⟩ : syracuseStep 6461477 = 1211527) (by norm_num)
theorem B4307651 : Blo 1913435 4307651 := bstep (se 1 (by rfl) ⟨3230738, by rfl⟩ : syracuseStep 4307651 = 6461477) B6461477
theorem B2871767 : Blo 1913435 2871767 := bstep (se 1 (by rfl) ⟨2153825, by rfl⟩ : syracuseStep 2871767 = 4307651) B4307651
theorem B1914511 : Blo 1913435 1914511 := bstep (se 1 (by rfl) ⟨1435883, by rfl⟩ : syracuseStep 1914511 = 2871767) B2871767
theorem B2871773 : Blo 1913435 2871773 := bbase (se 3 (by rfl) ⟨538457, by rfl⟩ : syracuseStep 2871773 = 1076915) (by norm_num)
theorem B1914515 : Blo 1913435 1914515 := bstep (se 1 (by rfl) ⟨1435886, by rfl⟩ : syracuseStep 1914515 = 2871773) B2871773
theorem B4307669 : Blo 1913435 4307669 := bbase (se 7 (by rfl) ⟨50480, by rfl⟩ : syracuseStep 4307669 = 100961) (by norm_num)
theorem B2871779 : Blo 1913435 2871779 := bstep (se 1 (by rfl) ⟨2153834, by rfl⟩ : syracuseStep 2871779 = 4307669) B4307669
theorem B1914519 : Blo 1913435 1914519 := bstep (se 1 (by rfl) ⟨1435889, by rfl⟩ : syracuseStep 1914519 = 2871779) B2871779
theorem B8177861 : Blo 1913435 8177861 := bbase (se 4 (by rfl) ⟨766674, by rfl⟩ : syracuseStep 8177861 = 1533349) (by norm_num)
theorem B5451907 : Blo 1913435 5451907 := bstep (se 1 (by rfl) ⟨4088930, by rfl⟩ : syracuseStep 5451907 = 8177861) B8177861
theorem B7269209 : Blo 1913435 7269209 := bstep (se 2 (by rfl) ⟨2725953, by rfl⟩ : syracuseStep 7269209 = 5451907) B5451907
theorem B4846139 : Blo 1913435 4846139 := bstep (se 1 (by rfl) ⟨3634604, by rfl⟩ : syracuseStep 4846139 = 7269209) B7269209
theorem B3230759 : Blo 1913435 3230759 := bstep (se 1 (by rfl) ⟨2423069, by rfl⟩ : syracuseStep 3230759 = 4846139) B4846139
theorem B2153839 : Blo 1913435 2153839 := bstep (se 1 (by rfl) ⟨1615379, by rfl⟩ : syracuseStep 2153839 = 3230759) B3230759
theorem B2871785 : Blo 1913435 2871785 := bstep (se 2 (by rfl) ⟨1076919, by rfl⟩ : syracuseStep 2871785 = 2153839) B2153839
theorem B1914523 : Blo 1913435 1914523 := bstep (se 1 (by rfl) ⟨1435892, by rfl⟩ : syracuseStep 1914523 = 2871785) B2871785
theorem B16578901 : Blo 1913435 16578901 := bbase (se 10 (by rfl) ⟨24285, by rfl⟩ : syracuseStep 16578901 = 48571) (by norm_num)
theorem B88420805 : Blo 1913435 88420805 := bstep (se 4 (by rfl) ⟨8289450, by rfl⟩ : syracuseStep 88420805 = 16578901) B16578901
theorem B58947203 : Blo 1913435 58947203 := bstep (se 1 (by rfl) ⟨44210402, by rfl⟩ : syracuseStep 58947203 = 88420805) B88420805
theorem B39298135 : Blo 1913435 39298135 := bstep (se 1 (by rfl) ⟨29473601, by rfl⟩ : syracuseStep 39298135 = 58947203) B58947203
theorem B52397513 : Blo 1913435 52397513 := bstep (se 2 (by rfl) ⟨19649067, by rfl⟩ : syracuseStep 52397513 = 39298135) B39298135
theorem B34931675 : Blo 1913435 34931675 := bstep (se 1 (by rfl) ⟨26198756, by rfl⟩ : syracuseStep 34931675 = 52397513) B52397513
theorem B93151133 : Blo 1913435 93151133 := bstep (se 3 (by rfl) ⟨17465837, by rfl⟩ : syracuseStep 93151133 = 34931675) B34931675
theorem B62100755 : Blo 1913435 62100755 := bstep (se 1 (by rfl) ⟨46575566, by rfl⟩ : syracuseStep 62100755 = 93151133) B93151133
theorem B41400503 : Blo 1913435 41400503 := bstep (se 1 (by rfl) ⟨31050377, by rfl⟩ : syracuseStep 41400503 = 62100755) B62100755
theorem B27600335 : Blo 1913435 27600335 := bstep (se 1 (by rfl) ⟨20700251, by rfl⟩ : syracuseStep 27600335 = 41400503) B41400503
theorem B18400223 : Blo 1913435 18400223 := bstep (se 1 (by rfl) ⟨13800167, by rfl⟩ : syracuseStep 18400223 = 27600335) B27600335
theorem B12266815 : Blo 1913435 12266815 := bstep (se 1 (by rfl) ⟨9200111, by rfl⟩ : syracuseStep 12266815 = 18400223) B18400223
theorem B16355753 : Blo 1913435 16355753 := bstep (se 2 (by rfl) ⟨6133407, by rfl⟩ : syracuseStep 16355753 = 12266815) B12266815
theorem B10903835 : Blo 1913435 10903835 := bstep (se 1 (by rfl) ⟨8177876, by rfl⟩ : syracuseStep 10903835 = 16355753) B16355753
theorem B7269223 : Blo 1913435 7269223 := bstep (se 1 (by rfl) ⟨5451917, by rfl⟩ : syracuseStep 7269223 = 10903835) B10903835
theorem B9692297 : Blo 1913435 9692297 := bstep (se 2 (by rfl) ⟨3634611, by rfl⟩ : syracuseStep 9692297 = 7269223) B7269223
theorem B6461531 : Blo 1913435 6461531 := bstep (se 1 (by rfl) ⟨4846148, by rfl⟩ : syracuseStep 6461531 = 9692297) B9692297
theorem B4307687 : Blo 1913435 4307687 := bstep (se 1 (by rfl) ⟨3230765, by rfl⟩ : syracuseStep 4307687 = 6461531) B6461531
theorem B2871791 : Blo 1913435 2871791 := bstep (se 1 (by rfl) ⟨2153843, by rfl⟩ : syracuseStep 2871791 = 4307687) B4307687
theorem B1914527 : Blo 1913435 1914527 := bstep (se 1 (by rfl) ⟨1435895, by rfl⟩ : syracuseStep 1914527 = 2871791) B2871791
theorem B2871797 : Blo 1913435 2871797 := bbase (se 5 (by rfl) ⟨134615, by rfl⟩ : syracuseStep 2871797 = 269231) (by norm_num)
theorem B1914531 : Blo 1913435 1914531 := bstep (se 1 (by rfl) ⟨1435898, by rfl⟩ : syracuseStep 1914531 = 2871797) B2871797
theorem B5451941 : Blo 1913435 5451941 := bbase (se 4 (by rfl) ⟨511119, by rfl⟩ : syracuseStep 5451941 = 1022239) (by norm_num)
theorem B3634627 : Blo 1913435 3634627 := bstep (se 1 (by rfl) ⟨2725970, by rfl⟩ : syracuseStep 3634627 = 5451941) B5451941
theorem B4846169 : Blo 1913435 4846169 := bstep (se 2 (by rfl) ⟨1817313, by rfl⟩ : syracuseStep 4846169 = 3634627) B3634627
theorem B3230779 : Blo 1913435 3230779 := bstep (se 1 (by rfl) ⟨2423084, by rfl⟩ : syracuseStep 3230779 = 4846169) B4846169
theorem B4307705 : Blo 1913435 4307705 := bstep (se 2 (by rfl) ⟨1615389, by rfl⟩ : syracuseStep 4307705 = 3230779) B3230779
theorem B2871803 : Blo 1913435 2871803 := bstep (se 1 (by rfl) ⟨2153852, by rfl⟩ : syracuseStep 2871803 = 4307705) B4307705
theorem B1914535 : Blo 1913435 1914535 := bstep (se 1 (by rfl) ⟨1435901, by rfl⟩ : syracuseStep 1914535 = 2871803) B2871803
theorem B2153857 : Blo 1913435 2153857 := bbase (se 2 (by rfl) ⟨807696, by rfl⟩ : syracuseStep 2153857 = 1615393) (by norm_num)
theorem B2871809 : Blo 1913435 2871809 := bstep (se 2 (by rfl) ⟨1076928, by rfl⟩ : syracuseStep 2871809 = 2153857) B2153857
theorem B1914539 : Blo 1913435 1914539 := bstep (se 1 (by rfl) ⟨1435904, by rfl⟩ : syracuseStep 1914539 = 2871809) B2871809
theorem B4846189 : Blo 1913435 4846189 := bbase (se 3 (by rfl) ⟨908660, by rfl⟩ : syracuseStep 4846189 = 1817321) (by norm_num)
theorem B6461585 : Blo 1913435 6461585 := bstep (se 2 (by rfl) ⟨2423094, by rfl⟩ : syracuseStep 6461585 = 4846189) B4846189
theorem B4307723 : Blo 1913435 4307723 := bstep (se 1 (by rfl) ⟨3230792, by rfl⟩ : syracuseStep 4307723 = 6461585) B6461585
theorem B2871815 : Blo 1913435 2871815 := bstep (se 1 (by rfl) ⟨2153861, by rfl⟩ : syracuseStep 2871815 = 4307723) B4307723
theorem B1914543 : Blo 1913435 1914543 := bstep (se 1 (by rfl) ⟨1435907, by rfl⟩ : syracuseStep 1914543 = 2871815) B2871815
theorem B2871821 : Blo 1913435 2871821 := bbase (se 3 (by rfl) ⟨538466, by rfl⟩ : syracuseStep 2871821 = 1076933) (by norm_num)
theorem B1914547 : Blo 1913435 1914547 := bstep (se 1 (by rfl) ⟨1435910, by rfl⟩ : syracuseStep 1914547 = 2871821) B2871821
theorem B4307741 : Blo 1913435 4307741 := bbase (se 3 (by rfl) ⟨807701, by rfl⟩ : syracuseStep 4307741 = 1615403) (by norm_num)
theorem B2871827 : Blo 1913435 2871827 := bstep (se 1 (by rfl) ⟨2153870, by rfl⟩ : syracuseStep 2871827 = 4307741) B4307741
theorem B1914551 : Blo 1913435 1914551 := bstep (se 1 (by rfl) ⟨1435913, by rfl⟩ : syracuseStep 1914551 = 2871827) B2871827
theorem B3230813 : Blo 1913435 3230813 := bbase (se 3 (by rfl) ⟨605777, by rfl⟩ : syracuseStep 3230813 = 1211555) (by norm_num)
theorem B2153875 : Blo 1913435 2153875 := bstep (se 1 (by rfl) ⟨1615406, by rfl⟩ : syracuseStep 2153875 = 3230813) B3230813
theorem B2871833 : Blo 1913435 2871833 := bstep (se 2 (by rfl) ⟨1076937, by rfl⟩ : syracuseStep 2871833 = 2153875) B2153875
theorem B1914555 : Blo 1913435 1914555 := bstep (se 1 (by rfl) ⟨1435916, by rfl⟩ : syracuseStep 1914555 = 2871833) B2871833
theorem B4600133 : Blo 1913435 4600133 := bbase (se 4 (by rfl) ⟨431262, by rfl⟩ : syracuseStep 4600133 = 862525) (by norm_num)
theorem B3066755 : Blo 1913435 3066755 := bstep (se 1 (by rfl) ⟨2300066, by rfl⟩ : syracuseStep 3066755 = 4600133) B4600133
theorem B8178013 : Blo 1913435 8178013 := bstep (se 3 (by rfl) ⟨1533377, by rfl⟩ : syracuseStep 8178013 = 3066755) B3066755
theorem B10904017 : Blo 1913435 10904017 := bstep (se 2 (by rfl) ⟨4089006, by rfl⟩ : syracuseStep 10904017 = 8178013) B8178013
theorem B14538689 : Blo 1913435 14538689 := bstep (se 2 (by rfl) ⟨5452008, by rfl⟩ : syracuseStep 14538689 = 10904017) B10904017
theorem B9692459 : Blo 1913435 9692459 := bstep (se 1 (by rfl) ⟨7269344, by rfl⟩ : syracuseStep 9692459 = 14538689) B14538689
theorem B6461639 : Blo 1913435 6461639 := bstep (se 1 (by rfl) ⟨4846229, by rfl⟩ : syracuseStep 6461639 = 9692459) B9692459
theorem B4307759 : Blo 1913435 4307759 := bstep (se 1 (by rfl) ⟨3230819, by rfl⟩ : syracuseStep 4307759 = 6461639) B6461639
theorem B2871839 : Blo 1913435 2871839 := bstep (se 1 (by rfl) ⟨2153879, by rfl⟩ : syracuseStep 2871839 = 4307759) B4307759
theorem B1914559 : Blo 1913435 1914559 := bstep (se 1 (by rfl) ⟨1435919, by rfl⟩ : syracuseStep 1914559 = 2871839) B2871839
theorem B2871845 : Blo 1913435 2871845 := bbase (se 4 (by rfl) ⟨269235, by rfl⟩ : syracuseStep 2871845 = 538471) (by norm_num)
theorem B1914563 : Blo 1913435 1914563 := bstep (se 1 (by rfl) ⟨1435922, by rfl⟩ : syracuseStep 1914563 = 2871845) B2871845
theorem B2423125 : Blo 1913435 2423125 := bbase (se 10 (by rfl) ⟨3549, by rfl⟩ : syracuseStep 2423125 = 7099) (by norm_num)
theorem B3230833 : Blo 1913435 3230833 := bstep (se 2 (by rfl) ⟨1211562, by rfl⟩ : syracuseStep 3230833 = 2423125) B2423125
theorem B4307777 : Blo 1913435 4307777 := bstep (se 2 (by rfl) ⟨1615416, by rfl⟩ : syracuseStep 4307777 = 3230833) B3230833
theorem B2871851 : Blo 1913435 2871851 := bstep (se 1 (by rfl) ⟨2153888, by rfl⟩ : syracuseStep 2871851 = 4307777) B4307777
theorem B1914567 : Blo 1913435 1914567 := bstep (se 1 (by rfl) ⟨1435925, by rfl⟩ : syracuseStep 1914567 = 2871851) B2871851
theorem B2153893 : Blo 1913435 2153893 := bbase (se 4 (by rfl) ⟨201927, by rfl⟩ : syracuseStep 2153893 = 403855) (by norm_num)
theorem B2871857 : Blo 1913435 2871857 := bstep (se 2 (by rfl) ⟨1076946, by rfl⟩ : syracuseStep 2871857 = 2153893) B2153893
theorem B1914571 : Blo 1913435 1914571 := bstep (se 1 (by rfl) ⟨1435928, by rfl⟩ : syracuseStep 1914571 = 2871857) B2871857
theorem B12267125 : Blo 1913435 12267125 := bbase (se 5 (by rfl) ⟨575021, by rfl⟩ : syracuseStep 12267125 = 1150043) (by norm_num)
theorem B8178083 : Blo 1913435 8178083 := bstep (se 1 (by rfl) ⟨6133562, by rfl⟩ : syracuseStep 8178083 = 12267125) B12267125
theorem B5452055 : Blo 1913435 5452055 := bstep (se 1 (by rfl) ⟨4089041, by rfl⟩ : syracuseStep 5452055 = 8178083) B8178083
theorem B3634703 : Blo 1913435 3634703 := bstep (se 1 (by rfl) ⟨2726027, by rfl⟩ : syracuseStep 3634703 = 5452055) B5452055
theorem B2423135 : Blo 1913435 2423135 := bstep (se 1 (by rfl) ⟨1817351, by rfl⟩ : syracuseStep 2423135 = 3634703) B3634703
theorem B6461693 : Blo 1913435 6461693 := bstep (se 3 (by rfl) ⟨1211567, by rfl⟩ : syracuseStep 6461693 = 2423135) B2423135
theorem B4307795 : Blo 1913435 4307795 := bstep (se 1 (by rfl) ⟨3230846, by rfl⟩ : syracuseStep 4307795 = 6461693) B6461693
theorem B2871863 : Blo 1913435 2871863 := bstep (se 1 (by rfl) ⟨2153897, by rfl⟩ : syracuseStep 2871863 = 4307795) B4307795
theorem B1914575 : Blo 1913435 1914575 := bstep (se 1 (by rfl) ⟨1435931, by rfl⟩ : syracuseStep 1914575 = 2871863) B2871863
theorem B2871869 : Blo 1913435 2871869 := bbase (se 3 (by rfl) ⟨538475, by rfl⟩ : syracuseStep 2871869 = 1076951) (by norm_num)
theorem B1914579 : Blo 1913435 1914579 := bstep (se 1 (by rfl) ⟨1435934, by rfl⟩ : syracuseStep 1914579 = 2871869) B2871869
theorem B4307813 : Blo 1913435 4307813 := bbase (se 4 (by rfl) ⟨403857, by rfl⟩ : syracuseStep 4307813 = 807715) (by norm_num)
theorem B2871875 : Blo 1913435 2871875 := bstep (se 1 (by rfl) ⟨2153906, by rfl⟩ : syracuseStep 2871875 = 4307813) B4307813
theorem B1914583 : Blo 1913435 1914583 := bstep (se 1 (by rfl) ⟨1435937, by rfl⟩ : syracuseStep 1914583 = 2871875) B2871875
theorem B4846301 : Blo 1913435 4846301 := bbase (se 3 (by rfl) ⟨908681, by rfl⟩ : syracuseStep 4846301 = 1817363) (by norm_num)
theorem B3230867 : Blo 1913435 3230867 := bstep (se 1 (by rfl) ⟨2423150, by rfl⟩ : syracuseStep 3230867 = 4846301) B4846301
theorem B2153911 : Blo 1913435 2153911 := bstep (se 1 (by rfl) ⟨1615433, by rfl⟩ : syracuseStep 2153911 = 3230867) B3230867
theorem B2871881 : Blo 1913435 2871881 := bstep (se 2 (by rfl) ⟨1076955, by rfl⟩ : syracuseStep 2871881 = 2153911) B2153911
theorem B1914587 : Blo 1913435 1914587 := bstep (se 1 (by rfl) ⟨1435940, by rfl⟩ : syracuseStep 1914587 = 2871881) B2871881
theorem B3634733 : Blo 1913435 3634733 := bbase (se 3 (by rfl) ⟨681512, by rfl⟩ : syracuseStep 3634733 = 1363025) (by norm_num)
theorem B9692621 : Blo 1913435 9692621 := bstep (se 3 (by rfl) ⟨1817366, by rfl⟩ : syracuseStep 9692621 = 3634733) B3634733
theorem B6461747 : Blo 1913435 6461747 := bstep (se 1 (by rfl) ⟨4846310, by rfl⟩ : syracuseStep 6461747 = 9692621) B9692621
theorem B4307831 : Blo 1913435 4307831 := bstep (se 1 (by rfl) ⟨3230873, by rfl⟩ : syracuseStep 4307831 = 6461747) B6461747
theorem B2871887 : Blo 1913435 2871887 := bstep (se 1 (by rfl) ⟨2153915, by rfl⟩ : syracuseStep 2871887 = 4307831) B4307831
theorem B1914591 : Blo 1913435 1914591 := bstep (se 1 (by rfl) ⟨1435943, by rfl⟩ : syracuseStep 1914591 = 2871887) B2871887
theorem B2871893 : Blo 1913435 2871893 := bbase (se 8 (by rfl) ⟨16827, by rfl⟩ : syracuseStep 2871893 = 33655) (by norm_num)
theorem B1914595 : Blo 1913435 1914595 := bstep (se 1 (by rfl) ⟨1435946, by rfl⟩ : syracuseStep 1914595 = 2871893) B2871893
theorem B10350517 : Blo 1913435 10350517 := bbase (se 5 (by rfl) ⟨485180, by rfl⟩ : syracuseStep 10350517 = 970361) (by norm_num)
theorem B13800689 : Blo 1913435 13800689 := bstep (se 2 (by rfl) ⟨5175258, by rfl⟩ : syracuseStep 13800689 = 10350517) B10350517
theorem B9200459 : Blo 1913435 9200459 := bstep (se 1 (by rfl) ⟨6900344, by rfl⟩ : syracuseStep 9200459 = 13800689) B13800689
theorem B6133639 : Blo 1913435 6133639 := bstep (se 1 (by rfl) ⟨4600229, by rfl⟩ : syracuseStep 6133639 = 9200459) B9200459
theorem B8178185 : Blo 1913435 8178185 := bstep (se 2 (by rfl) ⟨3066819, by rfl⟩ : syracuseStep 8178185 = 6133639) B6133639
theorem B5452123 : Blo 1913435 5452123 := bstep (se 1 (by rfl) ⟨4089092, by rfl⟩ : syracuseStep 5452123 = 8178185) B8178185
theorem B7269497 : Blo 1913435 7269497 := bstep (se 2 (by rfl) ⟨2726061, by rfl⟩ : syracuseStep 7269497 = 5452123) B5452123
theorem B4846331 : Blo 1913435 4846331 := bstep (se 1 (by rfl) ⟨3634748, by rfl⟩ : syracuseStep 4846331 = 7269497) B7269497
theorem B3230887 : Blo 1913435 3230887 := bstep (se 1 (by rfl) ⟨2423165, by rfl⟩ : syracuseStep 3230887 = 4846331) B4846331
theorem B4307849 : Blo 1913435 4307849 := bstep (se 2 (by rfl) ⟨1615443, by rfl⟩ : syracuseStep 4307849 = 3230887) B3230887
theorem B2871899 : Blo 1913435 2871899 := bstep (se 1 (by rfl) ⟨2153924, by rfl⟩ : syracuseStep 2871899 = 4307849) B4307849
theorem B1914599 : Blo 1913435 1914599 := bstep (se 1 (by rfl) ⟨1435949, by rfl⟩ : syracuseStep 1914599 = 2871899) B2871899
theorem B2153929 : Blo 1913435 2153929 := bbase (se 2 (by rfl) ⟨807723, by rfl⟩ : syracuseStep 2153929 = 1615447) (by norm_num)
theorem B2871905 : Blo 1913435 2871905 := bstep (se 2 (by rfl) ⟨1076964, by rfl⟩ : syracuseStep 2871905 = 2153929) B2153929
theorem B1914603 : Blo 1913435 1914603 := bstep (se 1 (by rfl) ⟨1435952, by rfl⟩ : syracuseStep 1914603 = 2871905) B2871905
theorem B16356437 : Blo 1913435 16356437 := bbase (se 8 (by rfl) ⟨95838, by rfl⟩ : syracuseStep 16356437 = 191677) (by norm_num)
theorem B10904291 : Blo 1913435 10904291 := bstep (se 1 (by rfl) ⟨8178218, by rfl⟩ : syracuseStep 10904291 = 16356437) B16356437
theorem B7269527 : Blo 1913435 7269527 := bstep (se 1 (by rfl) ⟨5452145, by rfl⟩ : syracuseStep 7269527 = 10904291) B10904291
theorem B4846351 : Blo 1913435 4846351 := bstep (se 1 (by rfl) ⟨3634763, by rfl⟩ : syracuseStep 4846351 = 7269527) B7269527
theorem B6461801 : Blo 1913435 6461801 := bstep (se 2 (by rfl) ⟨2423175, by rfl⟩ : syracuseStep 6461801 = 4846351) B4846351
theorem B4307867 : Blo 1913435 4307867 := bstep (se 1 (by rfl) ⟨3230900, by rfl⟩ : syracuseStep 4307867 = 6461801) B6461801
theorem B2871911 : Blo 1913435 2871911 := bstep (se 1 (by rfl) ⟨2153933, by rfl⟩ : syracuseStep 2871911 = 4307867) B4307867
theorem B1914607 : Blo 1913435 1914607 := bstep (se 1 (by rfl) ⟨1435955, by rfl⟩ : syracuseStep 1914607 = 2871911) B2871911
theorem B2871917 : Blo 1913435 2871917 := bbase (se 3 (by rfl) ⟨538484, by rfl⟩ : syracuseStep 2871917 = 1076969) (by norm_num)
theorem B1914611 : Blo 1913435 1914611 := bstep (se 1 (by rfl) ⟨1435958, by rfl⟩ : syracuseStep 1914611 = 2871917) B2871917
theorem B4307885 : Blo 1913435 4307885 := bbase (se 3 (by rfl) ⟨807728, by rfl⟩ : syracuseStep 4307885 = 1615457) (by norm_num)
theorem B2871923 : Blo 1913435 2871923 := bstep (se 1 (by rfl) ⟨2153942, by rfl⟩ : syracuseStep 2871923 = 4307885) B4307885
theorem B1914615 : Blo 1913435 1914615 := bstep (se 1 (by rfl) ⟨1435961, by rfl⟩ : syracuseStep 1914615 = 2871923) B2871923
theorem B5452181 : Blo 1913435 5452181 := bbase (se 6 (by rfl) ⟨127785, by rfl⟩ : syracuseStep 5452181 = 255571) (by norm_num)
theorem B3634787 : Blo 1913435 3634787 := bstep (se 1 (by rfl) ⟨2726090, by rfl⟩ : syracuseStep 3634787 = 5452181) B5452181
theorem B2423191 : Blo 1913435 2423191 := bstep (se 1 (by rfl) ⟨1817393, by rfl⟩ : syracuseStep 2423191 = 3634787) B3634787
theorem B3230921 : Blo 1913435 3230921 := bstep (se 2 (by rfl) ⟨1211595, by rfl⟩ : syracuseStep 3230921 = 2423191) B2423191
theorem B2153947 : Blo 1913435 2153947 := bstep (se 1 (by rfl) ⟨1615460, by rfl⟩ : syracuseStep 2153947 = 3230921) B3230921
theorem B2871929 : Blo 1913435 2871929 := bstep (se 2 (by rfl) ⟨1076973, by rfl⟩ : syracuseStep 2871929 = 2153947) B2153947
theorem B1914619 : Blo 1913435 1914619 := bstep (se 1 (by rfl) ⟨1435964, by rfl⟩ : syracuseStep 1914619 = 2871929) B2871929
theorem B2587661 : Blo 1913435 2587661 := bbase (se 3 (by rfl) ⟨485186, by rfl⟩ : syracuseStep 2587661 = 970373) (by norm_num)
theorem B27601717 : Blo 1913435 27601717 := bstep (se 5 (by rfl) ⟨1293830, by rfl⟩ : syracuseStep 27601717 = 2587661) B2587661
theorem B36802289 : Blo 1913435 36802289 := bstep (se 2 (by rfl) ⟨13800858, by rfl⟩ : syracuseStep 36802289 = 27601717) B27601717
theorem B24534859 : Blo 1913435 24534859 := bstep (se 1 (by rfl) ⟨18401144, by rfl⟩ : syracuseStep 24534859 = 36802289) B36802289
theorem B32713145 : Blo 1913435 32713145 := bstep (se 2 (by rfl) ⟨12267429, by rfl⟩ : syracuseStep 32713145 = 24534859) B24534859
theorem B21808763 : Blo 1913435 21808763 := bstep (se 1 (by rfl) ⟨16356572, by rfl⟩ : syracuseStep 21808763 = 32713145) B32713145
theorem B14539175 : Blo 1913435 14539175 := bstep (se 1 (by rfl) ⟨10904381, by rfl⟩ : syracuseStep 14539175 = 21808763) B21808763
theorem B9692783 : Blo 1913435 9692783 := bstep (se 1 (by rfl) ⟨7269587, by rfl⟩ : syracuseStep 9692783 = 14539175) B14539175
theorem B6461855 : Blo 1913435 6461855 := bstep (se 1 (by rfl) ⟨4846391, by rfl⟩ : syracuseStep 6461855 = 9692783) B9692783
theorem B4307903 : Blo 1913435 4307903 := bstep (se 1 (by rfl) ⟨3230927, by rfl⟩ : syracuseStep 4307903 = 6461855) B6461855
theorem B2871935 : Blo 1913435 2871935 := bstep (se 1 (by rfl) ⟨2153951, by rfl⟩ : syracuseStep 2871935 = 4307903) B4307903
theorem B1914623 : Blo 1913435 1914623 := bstep (se 1 (by rfl) ⟨1435967, by rfl⟩ : syracuseStep 1914623 = 2871935) B2871935
theorem B2871941 : Blo 1913435 2871941 := bbase (se 4 (by rfl) ⟨269244, by rfl⟩ : syracuseStep 2871941 = 538489) (by norm_num)
theorem B1914627 : Blo 1913435 1914627 := bstep (se 1 (by rfl) ⟨1435970, by rfl⟩ : syracuseStep 1914627 = 2871941) B2871941
theorem B3230941 : Blo 1913435 3230941 := bbase (se 3 (by rfl) ⟨605801, by rfl⟩ : syracuseStep 3230941 = 1211603) (by norm_num)
theorem B4307921 : Blo 1913435 4307921 := bstep (se 2 (by rfl) ⟨1615470, by rfl⟩ : syracuseStep 4307921 = 3230941) B3230941
theorem B2871947 : Blo 1913435 2871947 := bstep (se 1 (by rfl) ⟨2153960, by rfl⟩ : syracuseStep 2871947 = 4307921) B4307921
theorem B1914631 : Blo 1913435 1914631 := bstep (se 1 (by rfl) ⟨1435973, by rfl⟩ : syracuseStep 1914631 = 2871947) B2871947
theorem B2153965 : Blo 1913435 2153965 := bbase (se 3 (by rfl) ⟨403868, by rfl⟩ : syracuseStep 2153965 = 807737) (by norm_num)
theorem B2871953 : Blo 1913435 2871953 := bstep (se 2 (by rfl) ⟨1076982, by rfl⟩ : syracuseStep 2871953 = 2153965) B2153965
theorem B1914635 : Blo 1913435 1914635 := bstep (se 1 (by rfl) ⟨1435976, by rfl⟩ : syracuseStep 1914635 = 2871953) B2871953
theorem B6461909 : Blo 1913435 6461909 := bbase (se 7 (by rfl) ⟨75725, by rfl⟩ : syracuseStep 6461909 = 151451) (by norm_num)
theorem B4307939 : Blo 1913435 4307939 := bstep (se 1 (by rfl) ⟨3230954, by rfl⟩ : syracuseStep 4307939 = 6461909) B6461909
theorem B2871959 : Blo 1913435 2871959 := bstep (se 1 (by rfl) ⟨2153969, by rfl⟩ : syracuseStep 2871959 = 4307939) B4307939
theorem B1914639 : Blo 1913435 1914639 := bstep (se 1 (by rfl) ⟨1435979, by rfl⟩ : syracuseStep 1914639 = 2871959) B2871959
theorem B2871965 : Blo 1913435 2871965 := bbase (se 3 (by rfl) ⟨538493, by rfl⟩ : syracuseStep 2871965 = 1076987) (by norm_num)
theorem B1914643 : Blo 1913435 1914643 := bstep (se 1 (by rfl) ⟨1435982, by rfl⟩ : syracuseStep 1914643 = 2871965) B2871965
theorem B4307957 : Blo 1913435 4307957 := bbase (se 5 (by rfl) ⟨201935, by rfl⟩ : syracuseStep 4307957 = 403871) (by norm_num)
theorem B2871971 : Blo 1913435 2871971 := bstep (se 1 (by rfl) ⟨2153978, by rfl⟩ : syracuseStep 2871971 = 4307957) B4307957
theorem B1914647 : Blo 1913435 1914647 := bstep (se 1 (by rfl) ⟨1435985, by rfl⟩ : syracuseStep 1914647 = 2871971) B2871971
theorem B31476053 : Blo 1913435 31476053 := bbase (se 10 (by rfl) ⟨46107, by rfl⟩ : syracuseStep 31476053 = 92215) (by norm_num)
theorem B20984035 : Blo 1913435 20984035 := bstep (se 1 (by rfl) ⟨15738026, by rfl⟩ : syracuseStep 20984035 = 31476053) B31476053
theorem B27978713 : Blo 1913435 27978713 := bstep (se 2 (by rfl) ⟨10492017, by rfl⟩ : syracuseStep 27978713 = 20984035) B20984035
theorem B18652475 : Blo 1913435 18652475 := bstep (se 1 (by rfl) ⟨13989356, by rfl⟩ : syracuseStep 18652475 = 27978713) B27978713
theorem B49739933 : Blo 1913435 49739933 := bstep (se 3 (by rfl) ⟨9326237, by rfl⟩ : syracuseStep 49739933 = 18652475) B18652475
theorem B33159955 : Blo 1913435 33159955 := bstep (se 1 (by rfl) ⟨24869966, by rfl⟩ : syracuseStep 33159955 = 49739933) B49739933
theorem B44213273 : Blo 1913435 44213273 := bstep (se 2 (by rfl) ⟨16579977, by rfl⟩ : syracuseStep 44213273 = 33159955) B33159955
theorem B29475515 : Blo 1913435 29475515 := bstep (se 1 (by rfl) ⟨22106636, by rfl⟩ : syracuseStep 29475515 = 44213273) B44213273
theorem B78601373 : Blo 1913435 78601373 := bstep (se 3 (by rfl) ⟨14737757, by rfl⟩ : syracuseStep 78601373 = 29475515) B29475515
theorem B52400915 : Blo 1913435 52400915 := bstep (se 1 (by rfl) ⟨39300686, by rfl⟩ : syracuseStep 52400915 = 78601373) B78601373
theorem B34933943 : Blo 1913435 34933943 := bstep (se 1 (by rfl) ⟨26200457, by rfl⟩ : syracuseStep 34933943 = 52400915) B52400915
theorem B23289295 : Blo 1913435 23289295 := bstep (se 1 (by rfl) ⟨17466971, by rfl⟩ : syracuseStep 23289295 = 34933943) B34933943
theorem B31052393 : Blo 1913435 31052393 := bstep (se 2 (by rfl) ⟨11644647, by rfl⟩ : syracuseStep 31052393 = 23289295) B23289295
theorem B20701595 : Blo 1913435 20701595 := bstep (se 1 (by rfl) ⟨15526196, by rfl⟩ : syracuseStep 20701595 = 31052393) B31052393
theorem B55204253 : Blo 1913435 55204253 := bstep (se 3 (by rfl) ⟨10350797, by rfl⟩ : syracuseStep 55204253 = 20701595) B20701595
theorem B36802835 : Blo 1913435 36802835 := bstep (se 1 (by rfl) ⟨27602126, by rfl⟩ : syracuseStep 36802835 = 55204253) B55204253
theorem B24535223 : Blo 1913435 24535223 := bstep (se 1 (by rfl) ⟨18401417, by rfl⟩ : syracuseStep 24535223 = 36802835) B36802835
theorem B16356815 : Blo 1913435 16356815 := bstep (se 1 (by rfl) ⟨12267611, by rfl⟩ : syracuseStep 16356815 = 24535223) B24535223
theorem B10904543 : Blo 1913435 10904543 := bstep (se 1 (by rfl) ⟨8178407, by rfl⟩ : syracuseStep 10904543 = 16356815) B16356815
theorem B7269695 : Blo 1913435 7269695 := bstep (se 1 (by rfl) ⟨5452271, by rfl⟩ : syracuseStep 7269695 = 10904543) B10904543
theorem B4846463 : Blo 1913435 4846463 := bstep (se 1 (by rfl) ⟨3634847, by rfl⟩ : syracuseStep 4846463 = 7269695) B7269695
theorem B3230975 : Blo 1913435 3230975 := bstep (se 1 (by rfl) ⟨2423231, by rfl⟩ : syracuseStep 3230975 = 4846463) B4846463
theorem B2153983 : Blo 1913435 2153983 := bstep (se 1 (by rfl) ⟨1615487, by rfl⟩ : syracuseStep 2153983 = 3230975) B3230975
theorem B2871977 : Blo 1913435 2871977 := bstep (se 2 (by rfl) ⟨1076991, by rfl⟩ : syracuseStep 2871977 = 2153983) B2153983
theorem B1914651 : Blo 1913435 1914651 := bstep (se 1 (by rfl) ⟨1435988, by rfl⟩ : syracuseStep 1914651 = 2871977) B2871977
theorem B2726141 : Blo 1913435 2726141 := bbase (se 3 (by rfl) ⟨511151, by rfl⟩ : syracuseStep 2726141 = 1022303) (by norm_num)
theorem B7269709 : Blo 1913435 7269709 := bstep (se 3 (by rfl) ⟨1363070, by rfl⟩ : syracuseStep 7269709 = 2726141) B2726141
theorem B9692945 : Blo 1913435 9692945 := bstep (se 2 (by rfl) ⟨3634854, by rfl⟩ : syracuseStep 9692945 = 7269709) B7269709
theorem B6461963 : Blo 1913435 6461963 := bstep (se 1 (by rfl) ⟨4846472, by rfl⟩ : syracuseStep 6461963 = 9692945) B9692945
theorem B4307975 : Blo 1913435 4307975 := bstep (se 1 (by rfl) ⟨3230981, by rfl⟩ : syracuseStep 4307975 = 6461963) B6461963
theorem B2871983 : Blo 1913435 2871983 := bstep (se 1 (by rfl) ⟨2153987, by rfl⟩ : syracuseStep 2871983 = 4307975) B4307975
theorem B1914655 : Blo 1913435 1914655 := bstep (se 1 (by rfl) ⟨1435991, by rfl⟩ : syracuseStep 1914655 = 2871983) B2871983
theorem B2871989 : Blo 1913435 2871989 := bbase (se 5 (by rfl) ⟨134624, by rfl⟩ : syracuseStep 2871989 = 269249) (by norm_num)
theorem B1914659 : Blo 1913435 1914659 := bstep (se 1 (by rfl) ⟨1435994, by rfl⟩ : syracuseStep 1914659 = 2871989) B2871989
theorem B4846493 : Blo 1913435 4846493 := bbase (se 3 (by rfl) ⟨908717, by rfl⟩ : syracuseStep 4846493 = 1817435) (by norm_num)
theorem B3230995 : Blo 1913435 3230995 := bstep (se 1 (by rfl) ⟨2423246, by rfl⟩ : syracuseStep 3230995 = 4846493) B4846493
theorem B4307993 : Blo 1913435 4307993 := bstep (se 2 (by rfl) ⟨1615497, by rfl⟩ : syracuseStep 4307993 = 3230995) B3230995
theorem B2871995 : Blo 1913435 2871995 := bstep (se 1 (by rfl) ⟨2153996, by rfl⟩ : syracuseStep 2871995 = 4307993) B4307993
theorem B1914663 : Blo 1913435 1914663 := bstep (se 1 (by rfl) ⟨1435997, by rfl⟩ : syracuseStep 1914663 = 2871995) B2871995
theorem B2154001 : Blo 1913435 2154001 := bbase (se 2 (by rfl) ⟨807750, by rfl⟩ : syracuseStep 2154001 = 1615501) (by norm_num)
theorem B2872001 : Blo 1913435 2872001 := bstep (se 2 (by rfl) ⟨1077000, by rfl⟩ : syracuseStep 2872001 = 2154001) B2154001
theorem B1914667 : Blo 1913435 1914667 := bstep (se 1 (by rfl) ⟨1436000, by rfl⟩ : syracuseStep 1914667 = 2872001) B2872001
theorem B3634885 : Blo 1913435 3634885 := bbase (se 4 (by rfl) ⟨340770, by rfl⟩ : syracuseStep 3634885 = 681541) (by norm_num)
theorem B4846513 : Blo 1913435 4846513 := bstep (se 2 (by rfl) ⟨1817442, by rfl⟩ : syracuseStep 4846513 = 3634885) B3634885
theorem B6462017 : Blo 1913435 6462017 := bstep (se 2 (by rfl) ⟨2423256, by rfl⟩ : syracuseStep 6462017 = 4846513) B4846513
theorem B4308011 : Blo 1913435 4308011 := bstep (se 1 (by rfl) ⟨3231008, by rfl⟩ : syracuseStep 4308011 = 6462017) B6462017
theorem B2872007 : Blo 1913435 2872007 := bstep (se 1 (by rfl) ⟨2154005, by rfl⟩ : syracuseStep 2872007 = 4308011) B4308011
theorem B1914671 : Blo 1913435 1914671 := bstep (se 1 (by rfl) ⟨1436003, by rfl⟩ : syracuseStep 1914671 = 2872007) B2872007
theorem B2872013 : Blo 1913435 2872013 := bbase (se 3 (by rfl) ⟨538502, by rfl⟩ : syracuseStep 2872013 = 1077005) (by norm_num)
theorem B1914675 : Blo 1913435 1914675 := bstep (se 1 (by rfl) ⟨1436006, by rfl⟩ : syracuseStep 1914675 = 2872013) B2872013
theorem B4308029 : Blo 1913435 4308029 := bbase (se 3 (by rfl) ⟨807755, by rfl⟩ : syracuseStep 4308029 = 1615511) (by norm_num)
theorem B2872019 : Blo 1913435 2872019 := bstep (se 1 (by rfl) ⟨2154014, by rfl⟩ : syracuseStep 2872019 = 4308029) B4308029
theorem B1914679 : Blo 1913435 1914679 := bstep (se 1 (by rfl) ⟨1436009, by rfl⟩ : syracuseStep 1914679 = 2872019) B2872019
theorem B3231029 : Blo 1913435 3231029 := bbase (se 5 (by rfl) ⟨151454, by rfl⟩ : syracuseStep 3231029 = 302909) (by norm_num)
theorem B2154019 : Blo 1913435 2154019 := bstep (se 1 (by rfl) ⟨1615514, by rfl⟩ : syracuseStep 2154019 = 3231029) B3231029
theorem B2872025 : Blo 1913435 2872025 := bstep (se 2 (by rfl) ⟨1077009, by rfl⟩ : syracuseStep 2872025 = 2154019) B2154019
theorem B1914683 : Blo 1913435 1914683 := bstep (se 1 (by rfl) ⟨1436012, by rfl⟩ : syracuseStep 1914683 = 2872025) B2872025
theorem B5452373 : Blo 1913435 5452373 := bbase (se 8 (by rfl) ⟨31947, by rfl⟩ : syracuseStep 5452373 = 63895) (by norm_num)
theorem B14539661 : Blo 1913435 14539661 := bstep (se 3 (by rfl) ⟨2726186, by rfl⟩ : syracuseStep 14539661 = 5452373) B5452373
theorem B9693107 : Blo 1913435 9693107 := bstep (se 1 (by rfl) ⟨7269830, by rfl⟩ : syracuseStep 9693107 = 14539661) B14539661
theorem B6462071 : Blo 1913435 6462071 := bstep (se 1 (by rfl) ⟨4846553, by rfl⟩ : syracuseStep 6462071 = 9693107) B9693107
theorem B4308047 : Blo 1913435 4308047 := bstep (se 1 (by rfl) ⟨3231035, by rfl⟩ : syracuseStep 4308047 = 6462071) B6462071
theorem B2872031 : Blo 1913435 2872031 := bstep (se 1 (by rfl) ⟨2154023, by rfl⟩ : syracuseStep 2872031 = 4308047) B4308047
theorem B1914687 : Blo 1913435 1914687 := bstep (se 1 (by rfl) ⟨1436015, by rfl⟩ : syracuseStep 1914687 = 2872031) B2872031
theorem B2872037 : Blo 1913435 2872037 := bbase (se 4 (by rfl) ⟨269253, by rfl⟩ : syracuseStep 2872037 = 538507) (by norm_num)
theorem B1914691 : Blo 1913435 1914691 := bstep (se 1 (by rfl) ⟨1436018, by rfl⟩ : syracuseStep 1914691 = 2872037) B2872037
theorem B2044649 : Blo 1913435 2044649 := bbase (se 2 (by rfl) ⟨766743, by rfl⟩ : syracuseStep 2044649 = 1533487) (by norm_num)
theorem B5452397 : Blo 1913435 5452397 := bstep (se 3 (by rfl) ⟨1022324, by rfl⟩ : syracuseStep 5452397 = 2044649) B2044649
theorem B3634931 : Blo 1913435 3634931 := bstep (se 1 (by rfl) ⟨2726198, by rfl⟩ : syracuseStep 3634931 = 5452397) B5452397
theorem B2423287 : Blo 1913435 2423287 := bstep (se 1 (by rfl) ⟨1817465, by rfl⟩ : syracuseStep 2423287 = 3634931) B3634931
theorem B3231049 : Blo 1913435 3231049 := bstep (se 2 (by rfl) ⟨1211643, by rfl⟩ : syracuseStep 3231049 = 2423287) B2423287
theorem B4308065 : Blo 1913435 4308065 := bstep (se 2 (by rfl) ⟨1615524, by rfl⟩ : syracuseStep 4308065 = 3231049) B3231049
theorem B2872043 : Blo 1913435 2872043 := bstep (se 1 (by rfl) ⟨2154032, by rfl⟩ : syracuseStep 2872043 = 4308065) B4308065
theorem B1914695 : Blo 1913435 1914695 := bstep (se 1 (by rfl) ⟨1436021, by rfl⟩ : syracuseStep 1914695 = 2872043) B2872043
theorem B2154037 : Blo 1913435 2154037 := bbase (se 5 (by rfl) ⟨100970, by rfl⟩ : syracuseStep 2154037 = 201941) (by norm_num)
theorem B2872049 : Blo 1913435 2872049 := bstep (se 2 (by rfl) ⟨1077018, by rfl⟩ : syracuseStep 2872049 = 2154037) B2154037
theorem B1914699 : Blo 1913435 1914699 := bstep (se 1 (by rfl) ⟨1436024, by rfl⟩ : syracuseStep 1914699 = 2872049) B2872049
theorem B2423297 : Blo 1913435 2423297 := bbase (se 2 (by rfl) ⟨908736, by rfl⟩ : syracuseStep 2423297 = 1817473) (by norm_num)
theorem B6462125 : Blo 1913435 6462125 := bstep (se 3 (by rfl) ⟨1211648, by rfl⟩ : syracuseStep 6462125 = 2423297) B2423297
theorem B4308083 : Blo 1913435 4308083 := bstep (se 1 (by rfl) ⟨3231062, by rfl⟩ : syracuseStep 4308083 = 6462125) B6462125
theorem B2872055 : Blo 1913435 2872055 := bstep (se 1 (by rfl) ⟨2154041, by rfl⟩ : syracuseStep 2872055 = 4308083) B4308083
theorem B1914703 : Blo 1913435 1914703 := bstep (se 1 (by rfl) ⟨1436027, by rfl⟩ : syracuseStep 1914703 = 2872055) B2872055
theorem B2872061 : Blo 1913435 2872061 := bbase (se 3 (by rfl) ⟨538511, by rfl⟩ : syracuseStep 2872061 = 1077023) (by norm_num)
theorem B1914707 : Blo 1913435 1914707 := bstep (se 1 (by rfl) ⟨1436030, by rfl⟩ : syracuseStep 1914707 = 2872061) B2872061
theorem B4308101 : Blo 1913435 4308101 := bbase (se 4 (by rfl) ⟨403884, by rfl⟩ : syracuseStep 4308101 = 807769) (by norm_num)
theorem B2872067 : Blo 1913435 2872067 := bstep (se 1 (by rfl) ⟨2154050, by rfl⟩ : syracuseStep 2872067 = 4308101) B4308101
theorem B1914711 : Blo 1913435 1914711 := bstep (se 1 (by rfl) ⟨1436033, by rfl⟩ : syracuseStep 1914711 = 2872067) B2872067
theorem B4089341 : Blo 1913435 4089341 := bbase (se 3 (by rfl) ⟨766751, by rfl⟩ : syracuseStep 4089341 = 1533503) (by norm_num)
theorem B2726227 : Blo 1913435 2726227 := bstep (se 1 (by rfl) ⟨2044670, by rfl⟩ : syracuseStep 2726227 = 4089341) B4089341
theorem B3634969 : Blo 1913435 3634969 := bstep (se 2 (by rfl) ⟨1363113, by rfl⟩ : syracuseStep 3634969 = 2726227) B2726227
theorem B4846625 : Blo 1913435 4846625 := bstep (se 2 (by rfl) ⟨1817484, by rfl⟩ : syracuseStep 4846625 = 3634969) B3634969
theorem B3231083 : Blo 1913435 3231083 := bstep (se 1 (by rfl) ⟨2423312, by rfl⟩ : syracuseStep 3231083 = 4846625) B4846625
theorem B2154055 : Blo 1913435 2154055 := bstep (se 1 (by rfl) ⟨1615541, by rfl⟩ : syracuseStep 2154055 = 3231083) B3231083
theorem B2872073 : Blo 1913435 2872073 := bstep (se 2 (by rfl) ⟨1077027, by rfl⟩ : syracuseStep 2872073 = 2154055) B2154055
theorem B1914715 : Blo 1913435 1914715 := bstep (se 1 (by rfl) ⟨1436036, by rfl⟩ : syracuseStep 1914715 = 2872073) B2872073
theorem B9693269 : Blo 1913435 9693269 := bbase (se 8 (by rfl) ⟨56796, by rfl⟩ : syracuseStep 9693269 = 113593) (by norm_num)
theorem B6462179 : Blo 1913435 6462179 := bstep (se 1 (by rfl) ⟨4846634, by rfl⟩ : syracuseStep 6462179 = 9693269) B9693269
theorem B4308119 : Blo 1913435 4308119 := bstep (se 1 (by rfl) ⟨3231089, by rfl⟩ : syracuseStep 4308119 = 6462179) B6462179
theorem B2872079 : Blo 1913435 2872079 := bstep (se 1 (by rfl) ⟨2154059, by rfl⟩ : syracuseStep 2872079 = 4308119) B4308119
theorem B1914719 : Blo 1913435 1914719 := bstep (se 1 (by rfl) ⟨1436039, by rfl⟩ : syracuseStep 1914719 = 2872079) B2872079
theorem B2872085 : Blo 1913435 2872085 := bbase (se 6 (by rfl) ⟨67314, by rfl⟩ : syracuseStep 2872085 = 134629) (by norm_num)
theorem B1914723 : Blo 1913435 1914723 := bstep (se 1 (by rfl) ⟨1436042, by rfl⟩ : syracuseStep 1914723 = 2872085) B2872085
theorem B6900805 : Blo 1913435 6900805 := bbase (se 4 (by rfl) ⟨646950, by rfl⟩ : syracuseStep 6900805 = 1293901) (by norm_num)
theorem B36804293 : Blo 1913435 36804293 := bstep (se 4 (by rfl) ⟨3450402, by rfl⟩ : syracuseStep 36804293 = 6900805) B6900805
theorem B24536195 : Blo 1913435 24536195 := bstep (se 1 (by rfl) ⟨18402146, by rfl⟩ : syracuseStep 24536195 = 36804293) B36804293
theorem B16357463 : Blo 1913435 16357463 := bstep (se 1 (by rfl) ⟨12268097, by rfl⟩ : syracuseStep 16357463 = 24536195) B24536195
theorem B10904975 : Blo 1913435 10904975 := bstep (se 1 (by rfl) ⟨8178731, by rfl⟩ : syracuseStep 10904975 = 16357463) B16357463
theorem B7269983 : Blo 1913435 7269983 := bstep (se 1 (by rfl) ⟨5452487, by rfl⟩ : syracuseStep 7269983 = 10904975) B10904975
theorem B4846655 : Blo 1913435 4846655 := bstep (se 1 (by rfl) ⟨3634991, by rfl⟩ : syracuseStep 4846655 = 7269983) B7269983
theorem B3231103 : Blo 1913435 3231103 := bstep (se 1 (by rfl) ⟨2423327, by rfl⟩ : syracuseStep 3231103 = 4846655) B4846655
theorem B4308137 : Blo 1913435 4308137 := bstep (se 2 (by rfl) ⟨1615551, by rfl⟩ : syracuseStep 4308137 = 3231103) B3231103
theorem B2872091 : Blo 1913435 2872091 := bstep (se 1 (by rfl) ⟨2154068, by rfl⟩ : syracuseStep 2872091 = 4308137) B4308137
theorem B1914727 : Blo 1913435 1914727 := bstep (se 1 (by rfl) ⟨1436045, by rfl⟩ : syracuseStep 1914727 = 2872091) B2872091
theorem B2154073 : Blo 1913435 2154073 := bbase (se 2 (by rfl) ⟨807777, by rfl⟩ : syracuseStep 2154073 = 1615555) (by norm_num)
theorem B2872097 : Blo 1913435 2872097 := bstep (se 2 (by rfl) ⟨1077036, by rfl⟩ : syracuseStep 2872097 = 2154073) B2154073
theorem B1914731 : Blo 1913435 1914731 := bstep (se 1 (by rfl) ⟨1436048, by rfl⟩ : syracuseStep 1914731 = 2872097) B2872097
theorem B10351253 : Blo 1913435 10351253 := bbase (se 6 (by rfl) ⟨242607, by rfl⟩ : syracuseStep 10351253 = 485215) (by norm_num)
theorem B6900835 : Blo 1913435 6900835 := bstep (se 1 (by rfl) ⟨5175626, by rfl⟩ : syracuseStep 6900835 = 10351253) B10351253
theorem B9201113 : Blo 1913435 9201113 := bstep (se 2 (by rfl) ⟨3450417, by rfl⟩ : syracuseStep 9201113 = 6900835) B6900835
theorem B6134075 : Blo 1913435 6134075 := bstep (se 1 (by rfl) ⟨4600556, by rfl⟩ : syracuseStep 6134075 = 9201113) B9201113
theorem B4089383 : Blo 1913435 4089383 := bstep (se 1 (by rfl) ⟨3067037, by rfl⟩ : syracuseStep 4089383 = 6134075) B6134075
theorem B2726255 : Blo 1913435 2726255 := bstep (se 1 (by rfl) ⟨2044691, by rfl⟩ : syracuseStep 2726255 = 4089383) B4089383
theorem B7270013 : Blo 1913435 7270013 := bstep (se 3 (by rfl) ⟨1363127, by rfl⟩ : syracuseStep 7270013 = 2726255) B2726255
theorem B4846675 : Blo 1913435 4846675 := bstep (se 1 (by rfl) ⟨3635006, by rfl⟩ : syracuseStep 4846675 = 7270013) B7270013
theorem B6462233 : Blo 1913435 6462233 := bstep (se 2 (by rfl) ⟨2423337, by rfl⟩ : syracuseStep 6462233 = 4846675) B4846675
theorem B4308155 : Blo 1913435 4308155 := bstep (se 1 (by rfl) ⟨3231116, by rfl⟩ : syracuseStep 4308155 = 6462233) B6462233
theorem B2872103 : Blo 1913435 2872103 := bstep (se 1 (by rfl) ⟨2154077, by rfl⟩ : syracuseStep 2872103 = 4308155) B4308155
theorem B1914735 : Blo 1913435 1914735 := bstep (se 1 (by rfl) ⟨1436051, by rfl⟩ : syracuseStep 1914735 = 2872103) B2872103
theorem B2872109 : Blo 1913435 2872109 := bbase (se 3 (by rfl) ⟨538520, by rfl⟩ : syracuseStep 2872109 = 1077041) (by norm_num)
theorem B1914739 : Blo 1913435 1914739 := bstep (se 1 (by rfl) ⟨1436054, by rfl⟩ : syracuseStep 1914739 = 2872109) B2872109
theorem B4308173 : Blo 1913435 4308173 := bbase (se 3 (by rfl) ⟨807782, by rfl⟩ : syracuseStep 4308173 = 1615565) (by norm_num)
theorem B2872115 : Blo 1913435 2872115 := bstep (se 1 (by rfl) ⟨2154086, by rfl⟩ : syracuseStep 2872115 = 4308173) B4308173
theorem B1914743 : Blo 1913435 1914743 := bstep (se 1 (by rfl) ⟨1436057, by rfl⟩ : syracuseStep 1914743 = 2872115) B2872115
theorem B2423353 : Blo 1913435 2423353 := bbase (se 2 (by rfl) ⟨908757, by rfl⟩ : syracuseStep 2423353 = 1817515) (by norm_num)
theorem B3231137 : Blo 1913435 3231137 := bstep (se 2 (by rfl) ⟨1211676, by rfl⟩ : syracuseStep 3231137 = 2423353) B2423353
theorem B2154091 : Blo 1913435 2154091 := bstep (se 1 (by rfl) ⟨1615568, by rfl⟩ : syracuseStep 2154091 = 3231137) B3231137
theorem B2872121 : Blo 1913435 2872121 := bstep (se 2 (by rfl) ⟨1077045, by rfl⟩ : syracuseStep 2872121 = 2154091) B2154091
theorem B1914747 : Blo 1913435 1914747 := bstep (se 1 (by rfl) ⟨1436060, by rfl⟩ : syracuseStep 1914747 = 2872121) B2872121
theorem B2300297 : Blo 1913435 2300297 := bbase (se 2 (by rfl) ⟨862611, by rfl⟩ : syracuseStep 2300297 = 1725223) (by norm_num)
theorem B6134125 : Blo 1913435 6134125 := bstep (se 3 (by rfl) ⟨1150148, by rfl⟩ : syracuseStep 6134125 = 2300297) B2300297
theorem B8178833 : Blo 1913435 8178833 := bstep (se 2 (by rfl) ⟨3067062, by rfl⟩ : syracuseStep 8178833 = 6134125) B6134125
theorem B21810221 : Blo 1913435 21810221 := bstep (se 3 (by rfl) ⟨4089416, by rfl⟩ : syracuseStep 21810221 = 8178833) B8178833
theorem B14540147 : Blo 1913435 14540147 := bstep (se 1 (by rfl) ⟨10905110, by rfl⟩ : syracuseStep 14540147 = 21810221) B21810221
theorem B9693431 : Blo 1913435 9693431 := bstep (se 1 (by rfl) ⟨7270073, by rfl⟩ : syracuseStep 9693431 = 14540147) B14540147
theorem B6462287 : Blo 1913435 6462287 := bstep (se 1 (by rfl) ⟨4846715, by rfl⟩ : syracuseStep 6462287 = 9693431) B9693431
theorem B4308191 : Blo 1913435 4308191 := bstep (se 1 (by rfl) ⟨3231143, by rfl⟩ : syracuseStep 4308191 = 6462287) B6462287
theorem B2872127 : Blo 1913435 2872127 := bstep (se 1 (by rfl) ⟨2154095, by rfl⟩ : syracuseStep 2872127 = 4308191) B4308191
theorem B1914751 : Blo 1913435 1914751 := bstep (se 1 (by rfl) ⟨1436063, by rfl⟩ : syracuseStep 1914751 = 2872127) B2872127
theorem B2872133 : Blo 1913435 2872133 := bbase (se 4 (by rfl) ⟨269262, by rfl⟩ : syracuseStep 2872133 = 538525) (by norm_num)
theorem B1914755 : Blo 1913435 1914755 := bstep (se 1 (by rfl) ⟨1436066, by rfl⟩ : syracuseStep 1914755 = 2872133) B2872133
theorem B3231157 : Blo 1913435 3231157 := bbase (se 5 (by rfl) ⟨151460, by rfl⟩ : syracuseStep 3231157 = 302921) (by norm_num)
theorem B4308209 : Blo 1913435 4308209 := bstep (se 2 (by rfl) ⟨1615578, by rfl⟩ : syracuseStep 4308209 = 3231157) B3231157
theorem B2872139 : Blo 1913435 2872139 := bstep (se 1 (by rfl) ⟨2154104, by rfl⟩ : syracuseStep 2872139 = 4308209) B4308209
theorem B1914759 : Blo 1913435 1914759 := bstep (se 1 (by rfl) ⟨1436069, by rfl⟩ : syracuseStep 1914759 = 2872139) B2872139
theorem B2154109 : Blo 1913435 2154109 := bbase (se 3 (by rfl) ⟨403895, by rfl⟩ : syracuseStep 2154109 = 807791) (by norm_num)
theorem B2872145 : Blo 1913435 2872145 := bstep (se 2 (by rfl) ⟨1077054, by rfl⟩ : syracuseStep 2872145 = 2154109) B2154109
theorem B1914763 : Blo 1913435 1914763 := bstep (se 1 (by rfl) ⟨1436072, by rfl⟩ : syracuseStep 1914763 = 2872145) B2872145
theorem B6462341 : Blo 1913435 6462341 := bbase (se 4 (by rfl) ⟨605844, by rfl⟩ : syracuseStep 6462341 = 1211689) (by norm_num)
theorem B4308227 : Blo 1913435 4308227 := bstep (se 1 (by rfl) ⟨3231170, by rfl⟩ : syracuseStep 4308227 = 6462341) B6462341
theorem B2872151 : Blo 1913435 2872151 := bstep (se 1 (by rfl) ⟨2154113, by rfl⟩ : syracuseStep 2872151 = 4308227) B4308227
theorem B1914767 : Blo 1913435 1914767 := bstep (se 1 (by rfl) ⟨1436075, by rfl⟩ : syracuseStep 1914767 = 2872151) B2872151
theorem B2872157 : Blo 1913435 2872157 := bbase (se 3 (by rfl) ⟨538529, by rfl⟩ : syracuseStep 2872157 = 1077059) (by norm_num)
theorem B1914771 : Blo 1913435 1914771 := bstep (se 1 (by rfl) ⟨1436078, by rfl⟩ : syracuseStep 1914771 = 2872157) B2872157
theorem B4308245 : Blo 1913435 4308245 := bbase (se 6 (by rfl) ⟨100974, by rfl⟩ : syracuseStep 4308245 = 201949) (by norm_num)
theorem B2872163 : Blo 1913435 2872163 := bstep (se 1 (by rfl) ⟨2154122, by rfl⟩ : syracuseStep 2872163 = 4308245) B4308245
theorem B1914775 : Blo 1913435 1914775 := bstep (se 1 (by rfl) ⟨1436081, by rfl⟩ : syracuseStep 1914775 = 2872163) B2872163
theorem B7270181 : Blo 1913435 7270181 := bbase (se 4 (by rfl) ⟨681579, by rfl⟩ : syracuseStep 7270181 = 1363159) (by norm_num)
theorem B4846787 : Blo 1913435 4846787 := bstep (se 1 (by rfl) ⟨3635090, by rfl⟩ : syracuseStep 4846787 = 7270181) B7270181
theorem B3231191 : Blo 1913435 3231191 := bstep (se 1 (by rfl) ⟨2423393, by rfl⟩ : syracuseStep 3231191 = 4846787) B4846787
theorem B2154127 : Blo 1913435 2154127 := bstep (se 1 (by rfl) ⟨1615595, by rfl⟩ : syracuseStep 2154127 = 3231191) B3231191
theorem B2872169 : Blo 1913435 2872169 := bstep (se 2 (by rfl) ⟨1077063, by rfl⟩ : syracuseStep 2872169 = 2154127) B2154127
theorem B1914779 : Blo 1913435 1914779 := bstep (se 1 (by rfl) ⟨1436084, by rfl⟩ : syracuseStep 1914779 = 2872169) B2872169
theorem B4089485 : Blo 1913435 4089485 := bbase (se 3 (by rfl) ⟨766778, by rfl⟩ : syracuseStep 4089485 = 1533557) (by norm_num)
theorem B10905293 : Blo 1913435 10905293 := bstep (se 3 (by rfl) ⟨2044742, by rfl⟩ : syracuseStep 10905293 = 4089485) B4089485
theorem B7270195 : Blo 1913435 7270195 := bstep (se 1 (by rfl) ⟨5452646, by rfl⟩ : syracuseStep 7270195 = 10905293) B10905293
theorem B9693593 : Blo 1913435 9693593 := bstep (se 2 (by rfl) ⟨3635097, by rfl⟩ : syracuseStep 9693593 = 7270195) B7270195
theorem B6462395 : Blo 1913435 6462395 := bstep (se 1 (by rfl) ⟨4846796, by rfl⟩ : syracuseStep 6462395 = 9693593) B9693593
theorem B4308263 : Blo 1913435 4308263 := bstep (se 1 (by rfl) ⟨3231197, by rfl⟩ : syracuseStep 4308263 = 6462395) B6462395
theorem B2872175 : Blo 1913435 2872175 := bstep (se 1 (by rfl) ⟨2154131, by rfl⟩ : syracuseStep 2872175 = 4308263) B4308263
theorem B1914783 : Blo 1913435 1914783 := bstep (se 1 (by rfl) ⟨1436087, by rfl⟩ : syracuseStep 1914783 = 2872175) B2872175
theorem B2872181 : Blo 1913435 2872181 := bbase (se 5 (by rfl) ⟨134633, by rfl⟩ : syracuseStep 2872181 = 269267) (by norm_num)
theorem B1914787 : Blo 1913435 1914787 := bstep (se 1 (by rfl) ⟨1436090, by rfl⟩ : syracuseStep 1914787 = 2872181) B2872181
theorem B8290597 : Blo 1913435 8290597 := bbase (se 4 (by rfl) ⟨777243, by rfl⟩ : syracuseStep 8290597 = 1554487) (by norm_num)
theorem B11054129 : Blo 1913435 11054129 := bstep (se 2 (by rfl) ⟨4145298, by rfl⟩ : syracuseStep 11054129 = 8290597) B8290597
theorem B29477677 : Blo 1913435 29477677 := bstep (se 3 (by rfl) ⟨5527064, by rfl⟩ : syracuseStep 29477677 = 11054129) B11054129
theorem B39303569 : Blo 1913435 39303569 := bstep (se 2 (by rfl) ⟨14738838, by rfl⟩ : syracuseStep 39303569 = 29477677) B29477677
theorem B26202379 : Blo 1913435 26202379 := bstep (se 1 (by rfl) ⟨19651784, by rfl⟩ : syracuseStep 26202379 = 39303569) B39303569
theorem B34936505 : Blo 1913435 34936505 := bstep (se 2 (by rfl) ⟨13101189, by rfl⟩ : syracuseStep 34936505 = 26202379) B26202379
theorem B23291003 : Blo 1913435 23291003 := bstep (se 1 (by rfl) ⟨17468252, by rfl⟩ : syracuseStep 23291003 = 34936505) B34936505
theorem B15527335 : Blo 1913435 15527335 := bstep (se 1 (by rfl) ⟨11645501, by rfl⟩ : syracuseStep 15527335 = 23291003) B23291003
theorem B20703113 : Blo 1913435 20703113 := bstep (se 2 (by rfl) ⟨7763667, by rfl⟩ : syracuseStep 20703113 = 15527335) B15527335
theorem B13802075 : Blo 1913435 13802075 := bstep (se 1 (by rfl) ⟨10351556, by rfl⟩ : syracuseStep 13802075 = 20703113) B20703113
theorem B9201383 : Blo 1913435 9201383 := bstep (se 1 (by rfl) ⟨6901037, by rfl⟩ : syracuseStep 9201383 = 13802075) B13802075
theorem B6134255 : Blo 1913435 6134255 := bstep (se 1 (by rfl) ⟨4600691, by rfl⟩ : syracuseStep 6134255 = 9201383) B9201383
theorem B4089503 : Blo 1913435 4089503 := bstep (se 1 (by rfl) ⟨3067127, by rfl⟩ : syracuseStep 4089503 = 6134255) B6134255
theorem B2726335 : Blo 1913435 2726335 := bstep (se 1 (by rfl) ⟨2044751, by rfl⟩ : syracuseStep 2726335 = 4089503) B4089503
theorem B3635113 : Blo 1913435 3635113 := bstep (se 2 (by rfl) ⟨1363167, by rfl⟩ : syracuseStep 3635113 = 2726335) B2726335
theorem B4846817 : Blo 1913435 4846817 := bstep (se 2 (by rfl) ⟨1817556, by rfl⟩ : syracuseStep 4846817 = 3635113) B3635113
theorem B3231211 : Blo 1913435 3231211 := bstep (se 1 (by rfl) ⟨2423408, by rfl⟩ : syracuseStep 3231211 = 4846817) B4846817
theorem B4308281 : Blo 1913435 4308281 := bstep (se 2 (by rfl) ⟨1615605, by rfl⟩ : syracuseStep 4308281 = 3231211) B3231211
theorem B2872187 : Blo 1913435 2872187 := bstep (se 1 (by rfl) ⟨2154140, by rfl⟩ : syracuseStep 2872187 = 4308281) B4308281
theorem B1914791 : Blo 1913435 1914791 := bstep (se 1 (by rfl) ⟨1436093, by rfl⟩ : syracuseStep 1914791 = 2872187) B2872187
theorem B2154145 : Blo 1913435 2154145 := bbase (se 2 (by rfl) ⟨807804, by rfl⟩ : syracuseStep 2154145 = 1615609) (by norm_num)
theorem B2872193 : Blo 1913435 2872193 := bstep (se 2 (by rfl) ⟨1077072, by rfl⟩ : syracuseStep 2872193 = 2154145) B2154145
theorem B1914795 : Blo 1913435 1914795 := bstep (se 1 (by rfl) ⟨1436096, by rfl⟩ : syracuseStep 1914795 = 2872193) B2872193
theorem B4846837 : Blo 1913435 4846837 := bbase (se 5 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 4846837 = 454391) (by norm_num)
theorem B6462449 : Blo 1913435 6462449 := bstep (se 2 (by rfl) ⟨2423418, by rfl⟩ : syracuseStep 6462449 = 4846837) B4846837
theorem B4308299 : Blo 1913435 4308299 := bstep (se 1 (by rfl) ⟨3231224, by rfl⟩ : syracuseStep 4308299 = 6462449) B6462449
theorem B2872199 : Blo 1913435 2872199 := bstep (se 1 (by rfl) ⟨2154149, by rfl⟩ : syracuseStep 2872199 = 4308299) B4308299
theorem B1914799 : Blo 1913435 1914799 := bstep (se 1 (by rfl) ⟨1436099, by rfl⟩ : syracuseStep 1914799 = 2872199) B2872199
theorem B2872205 : Blo 1913435 2872205 := bbase (se 3 (by rfl) ⟨538538, by rfl⟩ : syracuseStep 2872205 = 1077077) (by norm_num)
theorem B1914803 : Blo 1913435 1914803 := bstep (se 1 (by rfl) ⟨1436102, by rfl⟩ : syracuseStep 1914803 = 2872205) B2872205
theorem B4308317 : Blo 1913435 4308317 := bbase (se 3 (by rfl) ⟨807809, by rfl⟩ : syracuseStep 4308317 = 1615619) (by norm_num)
theorem B2872211 : Blo 1913435 2872211 := bstep (se 1 (by rfl) ⟨2154158, by rfl⟩ : syracuseStep 2872211 = 4308317) B4308317
theorem B1914807 : Blo 1913435 1914807 := bstep (se 1 (by rfl) ⟨1436105, by rfl⟩ : syracuseStep 1914807 = 2872211) B2872211
theorem B3231245 : Blo 1913435 3231245 := bbase (se 3 (by rfl) ⟨605858, by rfl⟩ : syracuseStep 3231245 = 1211717) (by norm_num)
theorem B2154163 : Blo 1913435 2154163 := bstep (se 1 (by rfl) ⟨1615622, by rfl⟩ : syracuseStep 2154163 = 3231245) B3231245
theorem B2872217 : Blo 1913435 2872217 := bstep (se 2 (by rfl) ⟨1077081, by rfl⟩ : syracuseStep 2872217 = 2154163) B2154163
theorem B1914811 : Blo 1913435 1914811 := bstep (se 1 (by rfl) ⟨1436108, by rfl⟩ : syracuseStep 1914811 = 2872217) B2872217
theorem B3067165 : Blo 1913435 3067165 := bbase (se 3 (by rfl) ⟨575093, by rfl⟩ : syracuseStep 3067165 = 1150187) (by norm_num)
theorem B16358213 : Blo 1913435 16358213 := bstep (se 4 (by rfl) ⟨1533582, by rfl⟩ : syracuseStep 16358213 = 3067165) B3067165
theorem B10905475 : Blo 1913435 10905475 := bstep (se 1 (by rfl) ⟨8179106, by rfl⟩ : syracuseStep 10905475 = 16358213) B16358213
theorem B14540633 : Blo 1913435 14540633 := bstep (se 2 (by rfl) ⟨5452737, by rfl⟩ : syracuseStep 14540633 = 10905475) B10905475
theorem B9693755 : Blo 1913435 9693755 := bstep (se 1 (by rfl) ⟨7270316, by rfl⟩ : syracuseStep 9693755 = 14540633) B14540633
theorem B6462503 : Blo 1913435 6462503 := bstep (se 1 (by rfl) ⟨4846877, by rfl⟩ : syracuseStep 6462503 = 9693755) B9693755
theorem B4308335 : Blo 1913435 4308335 := bstep (se 1 (by rfl) ⟨3231251, by rfl⟩ : syracuseStep 4308335 = 6462503) B6462503
theorem B2872223 : Blo 1913435 2872223 := bstep (se 1 (by rfl) ⟨2154167, by rfl⟩ : syracuseStep 2872223 = 4308335) B4308335
theorem B1914815 : Blo 1913435 1914815 := bstep (se 1 (by rfl) ⟨1436111, by rfl⟩ : syracuseStep 1914815 = 2872223) B2872223
theorem B2872229 : Blo 1913435 2872229 := bbase (se 4 (by rfl) ⟨269271, by rfl⟩ : syracuseStep 2872229 = 538543) (by norm_num)
theorem B1914819 : Blo 1913435 1914819 := bstep (se 1 (by rfl) ⟨1436114, by rfl⟩ : syracuseStep 1914819 = 2872229) B2872229
theorem B2423449 : Blo 1913435 2423449 := bbase (se 2 (by rfl) ⟨908793, by rfl⟩ : syracuseStep 2423449 = 1817587) (by norm_num)
theorem B3231265 : Blo 1913435 3231265 := bstep (se 2 (by rfl) ⟨1211724, by rfl⟩ : syracuseStep 3231265 = 2423449) B2423449
theorem B4308353 : Blo 1913435 4308353 := bstep (se 2 (by rfl) ⟨1615632, by rfl⟩ : syracuseStep 4308353 = 3231265) B3231265
theorem B2872235 : Blo 1913435 2872235 := bstep (se 1 (by rfl) ⟨2154176, by rfl⟩ : syracuseStep 2872235 = 4308353) B4308353
theorem B1914823 : Blo 1913435 1914823 := bstep (se 1 (by rfl) ⟨1436117, by rfl⟩ : syracuseStep 1914823 = 2872235) B2872235
theorem B2154181 : Blo 1913435 2154181 := bbase (se 4 (by rfl) ⟨201954, by rfl⟩ : syracuseStep 2154181 = 403909) (by norm_num)
theorem B2872241 : Blo 1913435 2872241 := bstep (se 2 (by rfl) ⟨1077090, by rfl⟩ : syracuseStep 2872241 = 2154181) B2154181
theorem B1914827 : Blo 1913435 1914827 := bstep (se 1 (by rfl) ⟨1436120, by rfl⟩ : syracuseStep 1914827 = 2872241) B2872241
theorem B3635189 : Blo 1913435 3635189 := bbase (se 5 (by rfl) ⟨170399, by rfl⟩ : syracuseStep 3635189 = 340799) (by norm_num)
theorem B2423459 : Blo 1913435 2423459 := bstep (se 1 (by rfl) ⟨1817594, by rfl⟩ : syracuseStep 2423459 = 3635189) B3635189
theorem B6462557 : Blo 1913435 6462557 := bstep (se 3 (by rfl) ⟨1211729, by rfl⟩ : syracuseStep 6462557 = 2423459) B2423459
theorem B4308371 : Blo 1913435 4308371 := bstep (se 1 (by rfl) ⟨3231278, by rfl⟩ : syracuseStep 4308371 = 6462557) B6462557
theorem B2872247 : Blo 1913435 2872247 := bstep (se 1 (by rfl) ⟨2154185, by rfl⟩ : syracuseStep 2872247 = 4308371) B4308371
theorem B1914831 : Blo 1913435 1914831 := bstep (se 1 (by rfl) ⟨1436123, by rfl⟩ : syracuseStep 1914831 = 2872247) B2872247
theorem B2872253 : Blo 1913435 2872253 := bbase (se 3 (by rfl) ⟨538547, by rfl⟩ : syracuseStep 2872253 = 1077095) (by norm_num)
theorem B1914835 : Blo 1913435 1914835 := bstep (se 1 (by rfl) ⟨1436126, by rfl⟩ : syracuseStep 1914835 = 2872253) B2872253
theorem B4308389 : Blo 1913435 4308389 := bbase (se 4 (by rfl) ⟨403911, by rfl⟩ : syracuseStep 4308389 = 807823) (by norm_num)
theorem B2872259 : Blo 1913435 2872259 := bstep (se 1 (by rfl) ⟨2154194, by rfl⟩ : syracuseStep 2872259 = 4308389) B4308389
theorem B1914839 : Blo 1913435 1914839 := bstep (se 1 (by rfl) ⟨1436129, by rfl⟩ : syracuseStep 1914839 = 2872259) B2872259
theorem B4846949 : Blo 1913435 4846949 := bbase (se 4 (by rfl) ⟨454401, by rfl⟩ : syracuseStep 4846949 = 908803) (by norm_num)
theorem B3231299 : Blo 1913435 3231299 := bstep (se 1 (by rfl) ⟨2423474, by rfl⟩ : syracuseStep 3231299 = 4846949) B4846949
theorem B2154199 : Blo 1913435 2154199 := bstep (se 1 (by rfl) ⟨1615649, by rfl⟩ : syracuseStep 2154199 = 3231299) B3231299
theorem B2872265 : Blo 1913435 2872265 := bstep (se 2 (by rfl) ⟨1077099, by rfl⟩ : syracuseStep 2872265 = 2154199) B2154199
theorem B1914843 : Blo 1913435 1914843 := bstep (se 1 (by rfl) ⟨1436132, by rfl⟩ : syracuseStep 1914843 = 2872265) B2872265
theorem B2300413 : Blo 1913435 2300413 := bbase (se 3 (by rfl) ⟨431327, by rfl⟩ : syracuseStep 2300413 = 862655) (by norm_num)
theorem B3067217 : Blo 1913435 3067217 := bstep (se 2 (by rfl) ⟨1150206, by rfl⟩ : syracuseStep 3067217 = 2300413) B2300413
theorem B2044811 : Blo 1913435 2044811 := bstep (se 1 (by rfl) ⟨1533608, by rfl⟩ : syracuseStep 2044811 = 3067217) B3067217
theorem B5452829 : Blo 1913435 5452829 := bstep (se 3 (by rfl) ⟨1022405, by rfl⟩ : syracuseStep 5452829 = 2044811) B2044811
theorem B3635219 : Blo 1913435 3635219 := bstep (se 1 (by rfl) ⟨2726414, by rfl⟩ : syracuseStep 3635219 = 5452829) B5452829
theorem B9693917 : Blo 1913435 9693917 := bstep (se 3 (by rfl) ⟨1817609, by rfl⟩ : syracuseStep 9693917 = 3635219) B3635219
theorem B6462611 : Blo 1913435 6462611 := bstep (se 1 (by rfl) ⟨4846958, by rfl⟩ : syracuseStep 6462611 = 9693917) B9693917
theorem B4308407 : Blo 1913435 4308407 := bstep (se 1 (by rfl) ⟨3231305, by rfl⟩ : syracuseStep 4308407 = 6462611) B6462611
theorem B2872271 : Blo 1913435 2872271 := bstep (se 1 (by rfl) ⟨2154203, by rfl⟩ : syracuseStep 2872271 = 4308407) B4308407
theorem B1914847 : Blo 1913435 1914847 := bstep (se 1 (by rfl) ⟨1436135, by rfl⟩ : syracuseStep 1914847 = 2872271) B2872271
theorem B2872277 : Blo 1913435 2872277 := bbase (se 7 (by rfl) ⟨33659, by rfl⟩ : syracuseStep 2872277 = 67319) (by norm_num)
theorem B1914851 : Blo 1913435 1914851 := bstep (se 1 (by rfl) ⟨1436138, by rfl⟩ : syracuseStep 1914851 = 2872277) B2872277
theorem B7270469 : Blo 1913435 7270469 := bbase (se 4 (by rfl) ⟨681606, by rfl⟩ : syracuseStep 7270469 = 1363213) (by norm_num)
theorem B4846979 : Blo 1913435 4846979 := bstep (se 1 (by rfl) ⟨3635234, by rfl⟩ : syracuseStep 4846979 = 7270469) B7270469
theorem B3231319 : Blo 1913435 3231319 := bstep (se 1 (by rfl) ⟨2423489, by rfl⟩ : syracuseStep 3231319 = 4846979) B4846979
theorem B4308425 : Blo 1913435 4308425 := bstep (se 2 (by rfl) ⟨1615659, by rfl⟩ : syracuseStep 4308425 = 3231319) B3231319
theorem B2872283 : Blo 1913435 2872283 := bstep (se 1 (by rfl) ⟨2154212, by rfl⟩ : syracuseStep 2872283 = 4308425) B4308425
theorem B1914855 : Blo 1913435 1914855 := bstep (se 1 (by rfl) ⟨1436141, by rfl⟩ : syracuseStep 1914855 = 2872283) B2872283
theorem B2154217 : Blo 1913435 2154217 := bbase (se 2 (by rfl) ⟨807831, by rfl⟩ : syracuseStep 2154217 = 1615663) (by norm_num)
theorem B2872289 : Blo 1913435 2872289 := bstep (se 2 (by rfl) ⟨1077108, by rfl⟩ : syracuseStep 2872289 = 2154217) B2154217
theorem B1914859 : Blo 1913435 1914859 := bstep (se 1 (by rfl) ⟨1436144, by rfl⟩ : syracuseStep 1914859 = 2872289) B2872289
theorem B10905749 : Blo 1913435 10905749 := bbase (se 6 (by rfl) ⟨255603, by rfl⟩ : syracuseStep 10905749 = 511207) (by norm_num)
theorem B7270499 : Blo 1913435 7270499 := bstep (se 1 (by rfl) ⟨5452874, by rfl⟩ : syracuseStep 7270499 = 10905749) B10905749
theorem B4846999 : Blo 1913435 4846999 := bstep (se 1 (by rfl) ⟨3635249, by rfl⟩ : syracuseStep 4846999 = 7270499) B7270499
theorem B6462665 : Blo 1913435 6462665 := bstep (se 2 (by rfl) ⟨2423499, by rfl⟩ : syracuseStep 6462665 = 4846999) B4846999
theorem B4308443 : Blo 1913435 4308443 := bstep (se 1 (by rfl) ⟨3231332, by rfl⟩ : syracuseStep 4308443 = 6462665) B6462665
theorem B2872295 : Blo 1913435 2872295 := bstep (se 1 (by rfl) ⟨2154221, by rfl⟩ : syracuseStep 2872295 = 4308443) B4308443
theorem B1914863 : Blo 1913435 1914863 := bstep (se 1 (by rfl) ⟨1436147, by rfl⟩ : syracuseStep 1914863 = 2872295) B2872295
theorem B2872301 : Blo 1913435 2872301 := bbase (se 3 (by rfl) ⟨538556, by rfl⟩ : syracuseStep 2872301 = 1077113) (by norm_num)
theorem B1914867 : Blo 1913435 1914867 := bstep (se 1 (by rfl) ⟨1436150, by rfl⟩ : syracuseStep 1914867 = 2872301) B2872301
theorem B4308461 : Blo 1913435 4308461 := bbase (se 3 (by rfl) ⟨807836, by rfl⟩ : syracuseStep 4308461 = 1615673) (by norm_num)
theorem B2872307 : Blo 1913435 2872307 := bstep (se 1 (by rfl) ⟨2154230, by rfl⟩ : syracuseStep 2872307 = 4308461) B4308461
theorem B1914871 : Blo 1913435 1914871 := bstep (se 1 (by rfl) ⟨1436153, by rfl⟩ : syracuseStep 1914871 = 2872307) B2872307
theorem B6550885 : Blo 1913435 6550885 := bbase (se 4 (by rfl) ⟨614145, by rfl⟩ : syracuseStep 6550885 = 1228291) (by norm_num)
theorem B8734513 : Blo 1913435 8734513 := bstep (se 2 (by rfl) ⟨3275442, by rfl⟩ : syracuseStep 8734513 = 6550885) B6550885
theorem B11646017 : Blo 1913435 11646017 := bstep (se 2 (by rfl) ⟨4367256, by rfl⟩ : syracuseStep 11646017 = 8734513) B8734513
theorem B7764011 : Blo 1913435 7764011 := bstep (se 1 (by rfl) ⟨5823008, by rfl⟩ : syracuseStep 7764011 = 11646017) B11646017
theorem B5176007 : Blo 1913435 5176007 := bstep (se 1 (by rfl) ⟨3882005, by rfl⟩ : syracuseStep 5176007 = 7764011) B7764011
theorem B3450671 : Blo 1913435 3450671 := bstep (se 1 (by rfl) ⟨2588003, by rfl⟩ : syracuseStep 3450671 = 5176007) B5176007
theorem B2300447 : Blo 1913435 2300447 := bstep (se 1 (by rfl) ⟨1725335, by rfl⟩ : syracuseStep 2300447 = 3450671) B3450671
theorem B6134525 : Blo 1913435 6134525 := bstep (se 3 (by rfl) ⟨1150223, by rfl⟩ : syracuseStep 6134525 = 2300447) B2300447
theorem B4089683 : Blo 1913435 4089683 := bstep (se 1 (by rfl) ⟨3067262, by rfl⟩ : syracuseStep 4089683 = 6134525) B6134525
theorem B2726455 : Blo 1913435 2726455 := bstep (se 1 (by rfl) ⟨2044841, by rfl⟩ : syracuseStep 2726455 = 4089683) B4089683
theorem B3635273 : Blo 1913435 3635273 := bstep (se 2 (by rfl) ⟨1363227, by rfl⟩ : syracuseStep 3635273 = 2726455) B2726455
theorem B2423515 : Blo 1913435 2423515 := bstep (se 1 (by rfl) ⟨1817636, by rfl⟩ : syracuseStep 2423515 = 3635273) B3635273
theorem B3231353 : Blo 1913435 3231353 := bstep (se 2 (by rfl) ⟨1211757, by rfl⟩ : syracuseStep 3231353 = 2423515) B2423515
theorem B2154235 : Blo 1913435 2154235 := bstep (se 1 (by rfl) ⟨1615676, by rfl⟩ : syracuseStep 2154235 = 3231353) B3231353
theorem B2872313 : Blo 1913435 2872313 := bstep (se 2 (by rfl) ⟨1077117, by rfl⟩ : syracuseStep 2872313 = 2154235) B2154235
theorem B1914875 : Blo 1913435 1914875 := bstep (se 1 (by rfl) ⟨1436156, by rfl⟩ : syracuseStep 1914875 = 2872313) B2872313
theorem B27982037 : Blo 1913435 27982037 := bbase (se 7 (by rfl) ⟨327914, by rfl⟩ : syracuseStep 27982037 = 655829) (by norm_num)
theorem B74618765 : Blo 1913435 74618765 := bstep (se 3 (by rfl) ⟨13991018, by rfl⟩ : syracuseStep 74618765 = 27982037) B27982037
theorem B49745843 : Blo 1913435 49745843 := bstep (se 1 (by rfl) ⟨37309382, by rfl⟩ : syracuseStep 49745843 = 74618765) B74618765
theorem B33163895 : Blo 1913435 33163895 := bstep (se 1 (by rfl) ⟨24872921, by rfl⟩ : syracuseStep 33163895 = 49745843) B49745843
theorem B22109263 : Blo 1913435 22109263 := bstep (se 1 (by rfl) ⟨16581947, by rfl⟩ : syracuseStep 22109263 = 33163895) B33163895
theorem B117916069 : Blo 1913435 117916069 := bstep (se 4 (by rfl) ⟨11054631, by rfl⟩ : syracuseStep 117916069 = 22109263) B22109263
theorem B157221425 : Blo 1913435 157221425 := bstep (se 2 (by rfl) ⟨58958034, by rfl⟩ : syracuseStep 157221425 = 117916069) B117916069
theorem B104814283 : Blo 1913435 104814283 := bstep (se 1 (by rfl) ⟨78610712, by rfl⟩ : syracuseStep 104814283 = 157221425) B157221425
theorem B139752377 : Blo 1913435 139752377 := bstep (se 2 (by rfl) ⟨52407141, by rfl⟩ : syracuseStep 139752377 = 104814283) B104814283
theorem B93168251 : Blo 1913435 93168251 := bstep (se 1 (by rfl) ⟨69876188, by rfl⟩ : syracuseStep 93168251 = 139752377) B139752377
theorem B62112167 : Blo 1913435 62112167 := bstep (se 1 (by rfl) ⟨46584125, by rfl⟩ : syracuseStep 62112167 = 93168251) B93168251
theorem B41408111 : Blo 1913435 41408111 := bstep (se 1 (by rfl) ⟨31056083, by rfl⟩ : syracuseStep 41408111 = 62112167) B62112167
theorem B110421629 : Blo 1913435 110421629 := bstep (se 3 (by rfl) ⟨20704055, by rfl⟩ : syracuseStep 110421629 = 41408111) B41408111
theorem B73614419 : Blo 1913435 73614419 := bstep (se 1 (by rfl) ⟨55210814, by rfl⟩ : syracuseStep 73614419 = 110421629) B110421629
theorem B49076279 : Blo 1913435 49076279 := bstep (se 1 (by rfl) ⟨36807209, by rfl⟩ : syracuseStep 49076279 = 73614419) B73614419
theorem B32717519 : Blo 1913435 32717519 := bstep (se 1 (by rfl) ⟨24538139, by rfl⟩ : syracuseStep 32717519 = 49076279) B49076279
theorem B21811679 : Blo 1913435 21811679 := bstep (se 1 (by rfl) ⟨16358759, by rfl⟩ : syracuseStep 21811679 = 32717519) B32717519
theorem B14541119 : Blo 1913435 14541119 := bstep (se 1 (by rfl) ⟨10905839, by rfl⟩ : syracuseStep 14541119 = 21811679) B21811679
theorem B9694079 : Blo 1913435 9694079 := bstep (se 1 (by rfl) ⟨7270559, by rfl⟩ : syracuseStep 9694079 = 14541119) B14541119
theorem B6462719 : Blo 1913435 6462719 := bstep (se 1 (by rfl) ⟨4847039, by rfl⟩ : syracuseStep 6462719 = 9694079) B9694079
theorem B4308479 : Blo 1913435 4308479 := bstep (se 1 (by rfl) ⟨3231359, by rfl⟩ : syracuseStep 4308479 = 6462719) B6462719
theorem B2872319 : Blo 1913435 2872319 := bstep (se 1 (by rfl) ⟨2154239, by rfl⟩ : syracuseStep 2872319 = 4308479) B4308479
theorem B1914879 : Blo 1913435 1914879 := bstep (se 1 (by rfl) ⟨1436159, by rfl⟩ : syracuseStep 1914879 = 2872319) B2872319
theorem B2872325 : Blo 1913435 2872325 := bbase (se 4 (by rfl) ⟨269280, by rfl⟩ : syracuseStep 2872325 = 538561) (by norm_num)
theorem B1914883 : Blo 1913435 1914883 := bstep (se 1 (by rfl) ⟨1436162, by rfl⟩ : syracuseStep 1914883 = 2872325) B2872325
theorem B3231373 : Blo 1913435 3231373 := bbase (se 3 (by rfl) ⟨605882, by rfl⟩ : syracuseStep 3231373 = 1211765) (by norm_num)
theorem B4308497 : Blo 1913435 4308497 := bstep (se 2 (by rfl) ⟨1615686, by rfl⟩ : syracuseStep 4308497 = 3231373) B3231373
theorem B2872331 : Blo 1913435 2872331 := bstep (se 1 (by rfl) ⟨2154248, by rfl⟩ : syracuseStep 2872331 = 4308497) B4308497
theorem B1914887 : Blo 1913435 1914887 := bstep (se 1 (by rfl) ⟨1436165, by rfl⟩ : syracuseStep 1914887 = 2872331) B2872331
theorem B2154253 : Blo 1913435 2154253 := bbase (se 3 (by rfl) ⟨403922, by rfl⟩ : syracuseStep 2154253 = 807845) (by norm_num)
theorem B2872337 : Blo 1913435 2872337 := bstep (se 2 (by rfl) ⟨1077126, by rfl⟩ : syracuseStep 2872337 = 2154253) B2154253
theorem B1914891 : Blo 1913435 1914891 := bstep (se 1 (by rfl) ⟨1436168, by rfl⟩ : syracuseStep 1914891 = 2872337) B2872337
theorem B6462773 : Blo 1913435 6462773 := bbase (se 5 (by rfl) ⟨302942, by rfl⟩ : syracuseStep 6462773 = 605885) (by norm_num)
theorem B4308515 : Blo 1913435 4308515 := bstep (se 1 (by rfl) ⟨3231386, by rfl⟩ : syracuseStep 4308515 = 6462773) B6462773
theorem B2872343 : Blo 1913435 2872343 := bstep (se 1 (by rfl) ⟨2154257, by rfl⟩ : syracuseStep 2872343 = 4308515) B4308515
theorem B1914895 : Blo 1913435 1914895 := bstep (se 1 (by rfl) ⟨1436171, by rfl⟩ : syracuseStep 1914895 = 2872343) B2872343
theorem B2872349 : Blo 1913435 2872349 := bbase (se 3 (by rfl) ⟨538565, by rfl⟩ : syracuseStep 2872349 = 1077131) (by norm_num)
theorem B1914899 : Blo 1913435 1914899 := bstep (se 1 (by rfl) ⟨1436174, by rfl⟩ : syracuseStep 1914899 = 2872349) B2872349
theorem B4308533 : Blo 1913435 4308533 := bbase (se 5 (by rfl) ⟨201962, by rfl⟩ : syracuseStep 4308533 = 403925) (by norm_num)
theorem B2872355 : Blo 1913435 2872355 := bstep (se 1 (by rfl) ⟨2154266, by rfl⟩ : syracuseStep 2872355 = 4308533) B4308533
theorem B1914903 : Blo 1913435 1914903 := bstep (se 1 (by rfl) ⟨1436177, by rfl⟩ : syracuseStep 1914903 = 2872355) B2872355
theorem B2300485 : Blo 1913435 2300485 := bbase (se 4 (by rfl) ⟨215670, by rfl⟩ : syracuseStep 2300485 = 431341) (by norm_num)
theorem B3067313 : Blo 1913435 3067313 := bstep (se 2 (by rfl) ⟨1150242, by rfl⟩ : syracuseStep 3067313 = 2300485) B2300485
theorem B8179501 : Blo 1913435 8179501 := bstep (se 3 (by rfl) ⟨1533656, by rfl⟩ : syracuseStep 8179501 = 3067313) B3067313
theorem B10906001 : Blo 1913435 10906001 := bstep (se 2 (by rfl) ⟨4089750, by rfl⟩ : syracuseStep 10906001 = 8179501) B8179501
theorem B7270667 : Blo 1913435 7270667 := bstep (se 1 (by rfl) ⟨5453000, by rfl⟩ : syracuseStep 7270667 = 10906001) B10906001
theorem B4847111 : Blo 1913435 4847111 := bstep (se 1 (by rfl) ⟨3635333, by rfl⟩ : syracuseStep 4847111 = 7270667) B7270667
theorem B3231407 : Blo 1913435 3231407 := bstep (se 1 (by rfl) ⟨2423555, by rfl⟩ : syracuseStep 3231407 = 4847111) B4847111
theorem B2154271 : Blo 1913435 2154271 := bstep (se 1 (by rfl) ⟨1615703, by rfl⟩ : syracuseStep 2154271 = 3231407) B3231407
theorem B2872361 : Blo 1913435 2872361 := bstep (se 2 (by rfl) ⟨1077135, by rfl⟩ : syracuseStep 2872361 = 2154271) B2154271
theorem B1914907 : Blo 1913435 1914907 := bstep (se 1 (by rfl) ⟨1436180, by rfl⟩ : syracuseStep 1914907 = 2872361) B2872361
theorem B3882077 : Blo 1913435 3882077 := bbase (se 3 (by rfl) ⟨727889, by rfl⟩ : syracuseStep 3882077 = 1455779) (by norm_num)
theorem B2588051 : Blo 1913435 2588051 := bstep (se 1 (by rfl) ⟨1941038, by rfl⟩ : syracuseStep 2588051 = 3882077) B3882077
theorem B6901469 : Blo 1913435 6901469 := bstep (se 3 (by rfl) ⟨1294025, by rfl⟩ : syracuseStep 6901469 = 2588051) B2588051
theorem B4600979 : Blo 1913435 4600979 := bstep (se 1 (by rfl) ⟨3450734, by rfl⟩ : syracuseStep 4600979 = 6901469) B6901469
theorem B3067319 : Blo 1913435 3067319 := bstep (se 1 (by rfl) ⟨2300489, by rfl⟩ : syracuseStep 3067319 = 4600979) B4600979
theorem B8179517 : Blo 1913435 8179517 := bstep (se 3 (by rfl) ⟨1533659, by rfl⟩ : syracuseStep 8179517 = 3067319) B3067319
theorem B5453011 : Blo 1913435 5453011 := bstep (se 1 (by rfl) ⟨4089758, by rfl⟩ : syracuseStep 5453011 = 8179517) B8179517
theorem B7270681 : Blo 1913435 7270681 := bstep (se 2 (by rfl) ⟨2726505, by rfl⟩ : syracuseStep 7270681 = 5453011) B5453011
theorem B9694241 : Blo 1913435 9694241 := bstep (se 2 (by rfl) ⟨3635340, by rfl⟩ : syracuseStep 9694241 = 7270681) B7270681
theorem B6462827 : Blo 1913435 6462827 := bstep (se 1 (by rfl) ⟨4847120, by rfl⟩ : syracuseStep 6462827 = 9694241) B9694241
theorem B4308551 : Blo 1913435 4308551 := bstep (se 1 (by rfl) ⟨3231413, by rfl⟩ : syracuseStep 4308551 = 6462827) B6462827
theorem B2872367 : Blo 1913435 2872367 := bstep (se 1 (by rfl) ⟨2154275, by rfl⟩ : syracuseStep 2872367 = 4308551) B4308551
theorem B1914911 : Blo 1913435 1914911 := bstep (se 1 (by rfl) ⟨1436183, by rfl⟩ : syracuseStep 1914911 = 2872367) B2872367
theorem B2872373 : Blo 1913435 2872373 := bbase (se 5 (by rfl) ⟨134642, by rfl⟩ : syracuseStep 2872373 = 269285) (by norm_num)
theorem B1914915 : Blo 1913435 1914915 := bstep (se 1 (by rfl) ⟨1436186, by rfl⟩ : syracuseStep 1914915 = 2872373) B2872373
theorem B4847141 : Blo 1913435 4847141 := bbase (se 4 (by rfl) ⟨454419, by rfl⟩ : syracuseStep 4847141 = 908839) (by norm_num)
theorem B3231427 : Blo 1913435 3231427 := bstep (se 1 (by rfl) ⟨2423570, by rfl⟩ : syracuseStep 3231427 = 4847141) B4847141
theorem B4308569 : Blo 1913435 4308569 := bstep (se 2 (by rfl) ⟨1615713, by rfl⟩ : syracuseStep 4308569 = 3231427) B3231427
theorem B2872379 : Blo 1913435 2872379 := bstep (se 1 (by rfl) ⟨2154284, by rfl⟩ : syracuseStep 2872379 = 4308569) B4308569
theorem B1914919 : Blo 1913435 1914919 := bstep (se 1 (by rfl) ⟨1436189, by rfl⟩ : syracuseStep 1914919 = 2872379) B2872379
theorem B2154289 : Blo 1913435 2154289 := bbase (se 2 (by rfl) ⟨807858, by rfl⟩ : syracuseStep 2154289 = 1615717) (by norm_num)
theorem B2872385 : Blo 1913435 2872385 := bstep (se 2 (by rfl) ⟨1077144, by rfl⟩ : syracuseStep 2872385 = 2154289) B2154289
theorem B1914923 : Blo 1913435 1914923 := bstep (se 1 (by rfl) ⟨1436192, by rfl⟩ : syracuseStep 1914923 = 2872385) B2872385
theorem B2300509 : Blo 1913435 2300509 := bbase (se 3 (by rfl) ⟨431345, by rfl⟩ : syracuseStep 2300509 = 862691) (by norm_num)
theorem B3067345 : Blo 1913435 3067345 := bstep (se 2 (by rfl) ⟨1150254, by rfl⟩ : syracuseStep 3067345 = 2300509) B2300509
theorem B4089793 : Blo 1913435 4089793 := bstep (se 2 (by rfl) ⟨1533672, by rfl⟩ : syracuseStep 4089793 = 3067345) B3067345
theorem B5453057 : Blo 1913435 5453057 := bstep (se 2 (by rfl) ⟨2044896, by rfl⟩ : syracuseStep 5453057 = 4089793) B4089793
theorem B3635371 : Blo 1913435 3635371 := bstep (se 1 (by rfl) ⟨2726528, by rfl⟩ : syracuseStep 3635371 = 5453057) B5453057
theorem B4847161 : Blo 1913435 4847161 := bstep (se 2 (by rfl) ⟨1817685, by rfl⟩ : syracuseStep 4847161 = 3635371) B3635371
theorem B6462881 : Blo 1913435 6462881 := bstep (se 2 (by rfl) ⟨2423580, by rfl⟩ : syracuseStep 6462881 = 4847161) B4847161
theorem B4308587 : Blo 1913435 4308587 := bstep (se 1 (by rfl) ⟨3231440, by rfl⟩ : syracuseStep 4308587 = 6462881) B6462881
theorem B2872391 : Blo 1913435 2872391 := bstep (se 1 (by rfl) ⟨2154293, by rfl⟩ : syracuseStep 2872391 = 4308587) B4308587
theorem B1914927 : Blo 1913435 1914927 := bstep (se 1 (by rfl) ⟨1436195, by rfl⟩ : syracuseStep 1914927 = 2872391) B2872391
theorem B2872397 : Blo 1913435 2872397 := bbase (se 3 (by rfl) ⟨538574, by rfl⟩ : syracuseStep 2872397 = 1077149) (by norm_num)
theorem B1914931 : Blo 1913435 1914931 := bstep (se 1 (by rfl) ⟨1436198, by rfl⟩ : syracuseStep 1914931 = 2872397) B2872397
theorem B4308605 : Blo 1913435 4308605 := bbase (se 3 (by rfl) ⟨807863, by rfl⟩ : syracuseStep 4308605 = 1615727) (by norm_num)
theorem B2872403 : Blo 1913435 2872403 := bstep (se 1 (by rfl) ⟨2154302, by rfl⟩ : syracuseStep 2872403 = 4308605) B4308605
theorem B1914935 : Blo 1913435 1914935 := bstep (se 1 (by rfl) ⟨1436201, by rfl⟩ : syracuseStep 1914935 = 2872403) B2872403
theorem B3231461 : Blo 1913435 3231461 := bbase (se 4 (by rfl) ⟨302949, by rfl⟩ : syracuseStep 3231461 = 605899) (by norm_num)
theorem B2154307 : Blo 1913435 2154307 := bstep (se 1 (by rfl) ⟨1615730, by rfl⟩ : syracuseStep 2154307 = 3231461) B3231461
theorem B2872409 : Blo 1913435 2872409 := bstep (se 2 (by rfl) ⟨1077153, by rfl⟩ : syracuseStep 2872409 = 2154307) B2154307
theorem B1914939 : Blo 1913435 1914939 := bstep (se 1 (by rfl) ⟨1436204, by rfl⟩ : syracuseStep 1914939 = 2872409) B2872409
theorem B6134741 : Blo 1913435 6134741 := bbase (se 7 (by rfl) ⟨71891, by rfl⟩ : syracuseStep 6134741 = 143783) (by norm_num)
theorem B4089827 : Blo 1913435 4089827 := bstep (se 1 (by rfl) ⟨3067370, by rfl⟩ : syracuseStep 4089827 = 6134741) B6134741
theorem B2726551 : Blo 1913435 2726551 := bstep (se 1 (by rfl) ⟨2044913, by rfl⟩ : syracuseStep 2726551 = 4089827) B4089827
theorem B14541605 : Blo 1913435 14541605 := bstep (se 4 (by rfl) ⟨1363275, by rfl⟩ : syracuseStep 14541605 = 2726551) B2726551
theorem B9694403 : Blo 1913435 9694403 := bstep (se 1 (by rfl) ⟨7270802, by rfl⟩ : syracuseStep 9694403 = 14541605) B14541605
theorem B6462935 : Blo 1913435 6462935 := bstep (se 1 (by rfl) ⟨4847201, by rfl⟩ : syracuseStep 6462935 = 9694403) B9694403
theorem B4308623 : Blo 1913435 4308623 := bstep (se 1 (by rfl) ⟨3231467, by rfl⟩ : syracuseStep 4308623 = 6462935) B6462935
theorem B2872415 : Blo 1913435 2872415 := bstep (se 1 (by rfl) ⟨2154311, by rfl⟩ : syracuseStep 2872415 = 4308623) B4308623
theorem B1914943 : Blo 1913435 1914943 := bstep (se 1 (by rfl) ⟨1436207, by rfl⟩ : syracuseStep 1914943 = 2872415) B2872415
theorem B2872421 : Blo 1913435 2872421 := bbase (se 4 (by rfl) ⟨269289, by rfl⟩ : syracuseStep 2872421 = 538579) (by norm_num)
theorem B1914947 : Blo 1913435 1914947 := bstep (se 1 (by rfl) ⟨1436210, by rfl⟩ : syracuseStep 1914947 = 2872421) B2872421
theorem B4089845 : Blo 1913435 4089845 := bbase (se 5 (by rfl) ⟨191711, by rfl⟩ : syracuseStep 4089845 = 383423) (by norm_num)
theorem B2726563 : Blo 1913435 2726563 := bstep (se 1 (by rfl) ⟨2044922, by rfl⟩ : syracuseStep 2726563 = 4089845) B4089845
theorem B3635417 : Blo 1913435 3635417 := bstep (se 2 (by rfl) ⟨1363281, by rfl⟩ : syracuseStep 3635417 = 2726563) B2726563
theorem B2423611 : Blo 1913435 2423611 := bstep (se 1 (by rfl) ⟨1817708, by rfl⟩ : syracuseStep 2423611 = 3635417) B3635417
theorem B3231481 : Blo 1913435 3231481 := bstep (se 2 (by rfl) ⟨1211805, by rfl⟩ : syracuseStep 3231481 = 2423611) B2423611
theorem B4308641 : Blo 1913435 4308641 := bstep (se 2 (by rfl) ⟨1615740, by rfl⟩ : syracuseStep 4308641 = 3231481) B3231481
theorem B2872427 : Blo 1913435 2872427 := bstep (se 1 (by rfl) ⟨2154320, by rfl⟩ : syracuseStep 2872427 = 4308641) B4308641
theorem B1914951 : Blo 1913435 1914951 := bstep (se 1 (by rfl) ⟨1436213, by rfl⟩ : syracuseStep 1914951 = 2872427) B2872427
theorem B2154325 : Blo 1913435 2154325 := bbase (se 9 (by rfl) ⟨6311, by rfl⟩ : syracuseStep 2154325 = 12623) (by norm_num)
theorem B2872433 : Blo 1913435 2872433 := bstep (se 2 (by rfl) ⟨1077162, by rfl⟩ : syracuseStep 2872433 = 2154325) B2154325
theorem B1914955 : Blo 1913435 1914955 := bstep (se 1 (by rfl) ⟨1436216, by rfl⟩ : syracuseStep 1914955 = 2872433) B2872433
theorem B2423621 : Blo 1913435 2423621 := bbase (se 4 (by rfl) ⟨227214, by rfl⟩ : syracuseStep 2423621 = 454429) (by norm_num)
theorem B6462989 : Blo 1913435 6462989 := bstep (se 3 (by rfl) ⟨1211810, by rfl⟩ : syracuseStep 6462989 = 2423621) B2423621
theorem B4308659 : Blo 1913435 4308659 := bstep (se 1 (by rfl) ⟨3231494, by rfl⟩ : syracuseStep 4308659 = 6462989) B6462989
theorem B2872439 : Blo 1913435 2872439 := bstep (se 1 (by rfl) ⟨2154329, by rfl⟩ : syracuseStep 2872439 = 4308659) B4308659
theorem B1914959 : Blo 1913435 1914959 := bstep (se 1 (by rfl) ⟨1436219, by rfl⟩ : syracuseStep 1914959 = 2872439) B2872439
theorem B2872445 : Blo 1913435 2872445 := bbase (se 3 (by rfl) ⟨538583, by rfl⟩ : syracuseStep 2872445 = 1077167) (by norm_num)
theorem B1914963 : Blo 1913435 1914963 := bstep (se 1 (by rfl) ⟨1436222, by rfl⟩ : syracuseStep 1914963 = 2872445) B2872445
theorem B4308677 : Blo 1913435 4308677 := bbase (se 4 (by rfl) ⟨403938, by rfl⟩ : syracuseStep 4308677 = 807877) (by norm_num)
theorem B2872451 : Blo 1913435 2872451 := bstep (se 1 (by rfl) ⟨2154338, by rfl⟩ : syracuseStep 2872451 = 4308677) B4308677
theorem B1914967 : Blo 1913435 1914967 := bstep (se 1 (by rfl) ⟨1436225, by rfl⟩ : syracuseStep 1914967 = 2872451) B2872451
theorem B3275605 : Blo 1913435 3275605 := bbase (se 9 (by rfl) ⟨9596, by rfl⟩ : syracuseStep 3275605 = 19193) (by norm_num)
theorem B17469893 : Blo 1913435 17469893 := bstep (se 4 (by rfl) ⟨1637802, by rfl⟩ : syracuseStep 17469893 = 3275605) B3275605
theorem B11646595 : Blo 1913435 11646595 := bstep (se 1 (by rfl) ⟨8734946, by rfl⟩ : syracuseStep 11646595 = 17469893) B17469893
theorem B62115173 : Blo 1913435 62115173 := bstep (se 4 (by rfl) ⟨5823297, by rfl⟩ : syracuseStep 62115173 = 11646595) B11646595
theorem B41410115 : Blo 1913435 41410115 := bstep (se 1 (by rfl) ⟨31057586, by rfl⟩ : syracuseStep 41410115 = 62115173) B62115173
theorem B27606743 : Blo 1913435 27606743 := bstep (se 1 (by rfl) ⟨20705057, by rfl⟩ : syracuseStep 27606743 = 41410115) B41410115
theorem B18404495 : Blo 1913435 18404495 := bstep (se 1 (by rfl) ⟨13803371, by rfl⟩ : syracuseStep 18404495 = 27606743) B27606743
theorem B12269663 : Blo 1913435 12269663 := bstep (se 1 (by rfl) ⟨9202247, by rfl⟩ : syracuseStep 12269663 = 18404495) B18404495
theorem B8179775 : Blo 1913435 8179775 := bstep (se 1 (by rfl) ⟨6134831, by rfl⟩ : syracuseStep 8179775 = 12269663) B12269663
theorem B5453183 : Blo 1913435 5453183 := bstep (se 1 (by rfl) ⟨4089887, by rfl⟩ : syracuseStep 5453183 = 8179775) B8179775
theorem B3635455 : Blo 1913435 3635455 := bstep (se 1 (by rfl) ⟨2726591, by rfl⟩ : syracuseStep 3635455 = 5453183) B5453183
theorem B4847273 : Blo 1913435 4847273 := bstep (se 2 (by rfl) ⟨1817727, by rfl⟩ : syracuseStep 4847273 = 3635455) B3635455
theorem B3231515 : Blo 1913435 3231515 := bstep (se 1 (by rfl) ⟨2423636, by rfl⟩ : syracuseStep 3231515 = 4847273) B4847273
theorem B2154343 : Blo 1913435 2154343 := bstep (se 1 (by rfl) ⟨1615757, by rfl⟩ : syracuseStep 2154343 = 3231515) B3231515
theorem B2872457 : Blo 1913435 2872457 := bstep (se 2 (by rfl) ⟨1077171, by rfl⟩ : syracuseStep 2872457 = 2154343) B2154343
theorem B1914971 : Blo 1913435 1914971 := bstep (se 1 (by rfl) ⟨1436228, by rfl⟩ : syracuseStep 1914971 = 2872457) B2872457
theorem B9694565 : Blo 1913435 9694565 := bbase (se 4 (by rfl) ⟨908865, by rfl⟩ : syracuseStep 9694565 = 1817731) (by norm_num)
theorem B6463043 : Blo 1913435 6463043 := bstep (se 1 (by rfl) ⟨4847282, by rfl⟩ : syracuseStep 6463043 = 9694565) B9694565
theorem B4308695 : Blo 1913435 4308695 := bstep (se 1 (by rfl) ⟨3231521, by rfl⟩ : syracuseStep 4308695 = 6463043) B6463043
theorem B2872463 : Blo 1913435 2872463 := bstep (se 1 (by rfl) ⟨2154347, by rfl⟩ : syracuseStep 2872463 = 4308695) B4308695
theorem B1914975 : Blo 1913435 1914975 := bstep (se 1 (by rfl) ⟨1436231, by rfl⟩ : syracuseStep 1914975 = 2872463) B2872463
theorem B2872469 : Blo 1913435 2872469 := bbase (se 6 (by rfl) ⟨67323, by rfl⟩ : syracuseStep 2872469 = 134647) (by norm_num)
theorem B1914979 : Blo 1913435 1914979 := bstep (se 1 (by rfl) ⟨1436234, by rfl⟩ : syracuseStep 1914979 = 2872469) B2872469
theorem B6134869 : Blo 1913435 6134869 := bbase (se 8 (by rfl) ⟨35946, by rfl⟩ : syracuseStep 6134869 = 71893) (by norm_num)
theorem B8179825 : Blo 1913435 8179825 := bstep (se 2 (by rfl) ⟨3067434, by rfl⟩ : syracuseStep 8179825 = 6134869) B6134869
theorem B10906433 : Blo 1913435 10906433 := bstep (se 2 (by rfl) ⟨4089912, by rfl⟩ : syracuseStep 10906433 = 8179825) B8179825
theorem B7270955 : Blo 1913435 7270955 := bstep (se 1 (by rfl) ⟨5453216, by rfl⟩ : syracuseStep 7270955 = 10906433) B10906433
theorem B4847303 : Blo 1913435 4847303 := bstep (se 1 (by rfl) ⟨3635477, by rfl⟩ : syracuseStep 4847303 = 7270955) B7270955
theorem B3231535 : Blo 1913435 3231535 := bstep (se 1 (by rfl) ⟨2423651, by rfl⟩ : syracuseStep 3231535 = 4847303) B4847303
theorem B4308713 : Blo 1913435 4308713 := bstep (se 2 (by rfl) ⟨1615767, by rfl⟩ : syracuseStep 4308713 = 3231535) B3231535
theorem B2872475 : Blo 1913435 2872475 := bstep (se 1 (by rfl) ⟨2154356, by rfl⟩ : syracuseStep 2872475 = 4308713) B4308713
theorem B1914983 : Blo 1913435 1914983 := bstep (se 1 (by rfl) ⟨1436237, by rfl⟩ : syracuseStep 1914983 = 2872475) B2872475
theorem B2154361 : Blo 1913435 2154361 := bbase (se 2 (by rfl) ⟨807885, by rfl⟩ : syracuseStep 2154361 = 1615771) (by norm_num)
theorem B2872481 : Blo 1913435 2872481 := bstep (se 2 (by rfl) ⟨1077180, by rfl⟩ : syracuseStep 2872481 = 2154361) B2154361
theorem B1914987 : Blo 1913435 1914987 := bstep (se 1 (by rfl) ⟨1436240, by rfl⟩ : syracuseStep 1914987 = 2872481) B2872481
theorem B14941493 : Blo 1913435 14941493 := bbase (se 5 (by rfl) ⟨700382, by rfl⟩ : syracuseStep 14941493 = 1400765) (by norm_num)
theorem B9960995 : Blo 1913435 9960995 := bstep (se 1 (by rfl) ⟨7470746, by rfl⟩ : syracuseStep 9960995 = 14941493) B14941493
theorem B6640663 : Blo 1913435 6640663 := bstep (se 1 (by rfl) ⟨4980497, by rfl⟩ : syracuseStep 6640663 = 9960995) B9960995
theorem B8854217 : Blo 1913435 8854217 := bstep (se 2 (by rfl) ⟨3320331, by rfl⟩ : syracuseStep 8854217 = 6640663) B6640663
theorem B5902811 : Blo 1913435 5902811 := bstep (se 1 (by rfl) ⟨4427108, by rfl⟩ : syracuseStep 5902811 = 8854217) B8854217
theorem B3935207 : Blo 1913435 3935207 := bstep (se 1 (by rfl) ⟨2951405, by rfl⟩ : syracuseStep 3935207 = 5902811) B5902811
theorem B2623471 : Blo 1913435 2623471 := bstep (se 1 (by rfl) ⟨1967603, by rfl⟩ : syracuseStep 2623471 = 3935207) B3935207
theorem B55967381 : Blo 1913435 55967381 := bstep (se 6 (by rfl) ⟨1311735, by rfl⟩ : syracuseStep 55967381 = 2623471) B2623471
theorem B37311587 : Blo 1913435 37311587 := bstep (se 1 (by rfl) ⟨27983690, by rfl⟩ : syracuseStep 37311587 = 55967381) B55967381
theorem B24874391 : Blo 1913435 24874391 := bstep (se 1 (by rfl) ⟨18655793, by rfl⟩ : syracuseStep 24874391 = 37311587) B37311587
theorem B66331709 : Blo 1913435 66331709 := bstep (se 3 (by rfl) ⟨12437195, by rfl⟩ : syracuseStep 66331709 = 24874391) B24874391
theorem B44221139 : Blo 1913435 44221139 := bstep (se 1 (by rfl) ⟨33165854, by rfl⟩ : syracuseStep 44221139 = 66331709) B66331709
theorem B29480759 : Blo 1913435 29480759 := bstep (se 1 (by rfl) ⟨22110569, by rfl⟩ : syracuseStep 29480759 = 44221139) B44221139
theorem B19653839 : Blo 1913435 19653839 := bstep (se 1 (by rfl) ⟨14740379, by rfl⟩ : syracuseStep 19653839 = 29480759) B29480759
theorem B13102559 : Blo 1913435 13102559 := bstep (se 1 (by rfl) ⟨9826919, by rfl⟩ : syracuseStep 13102559 = 19653839) B19653839
theorem B8735039 : Blo 1913435 8735039 := bstep (se 1 (by rfl) ⟨6551279, by rfl⟩ : syracuseStep 8735039 = 13102559) B13102559
theorem B5823359 : Blo 1913435 5823359 := bstep (se 1 (by rfl) ⟨4367519, by rfl⟩ : syracuseStep 5823359 = 8735039) B8735039
theorem B3882239 : Blo 1913435 3882239 := bstep (se 1 (by rfl) ⟨2911679, by rfl⟩ : syracuseStep 3882239 = 5823359) B5823359
theorem B2588159 : Blo 1913435 2588159 := bstep (se 1 (by rfl) ⟨1941119, by rfl⟩ : syracuseStep 2588159 = 3882239) B3882239
theorem B6901757 : Blo 1913435 6901757 := bstep (se 3 (by rfl) ⟨1294079, by rfl⟩ : syracuseStep 6901757 = 2588159) B2588159
theorem B4601171 : Blo 1913435 4601171 := bstep (se 1 (by rfl) ⟨3450878, by rfl⟩ : syracuseStep 4601171 = 6901757) B6901757
theorem B12269789 : Blo 1913435 12269789 := bstep (se 3 (by rfl) ⟨2300585, by rfl⟩ : syracuseStep 12269789 = 4601171) B4601171
theorem B8179859 : Blo 1913435 8179859 := bstep (se 1 (by rfl) ⟨6134894, by rfl⟩ : syracuseStep 8179859 = 12269789) B12269789
theorem B5453239 : Blo 1913435 5453239 := bstep (se 1 (by rfl) ⟨4089929, by rfl⟩ : syracuseStep 5453239 = 8179859) B8179859
theorem B7270985 : Blo 1913435 7270985 := bstep (se 2 (by rfl) ⟨2726619, by rfl⟩ : syracuseStep 7270985 = 5453239) B5453239
theorem B4847323 : Blo 1913435 4847323 := bstep (se 1 (by rfl) ⟨3635492, by rfl⟩ : syracuseStep 4847323 = 7270985) B7270985
theorem B6463097 : Blo 1913435 6463097 := bstep (se 2 (by rfl) ⟨2423661, by rfl⟩ : syracuseStep 6463097 = 4847323) B4847323
theorem B4308731 : Blo 1913435 4308731 := bstep (se 1 (by rfl) ⟨3231548, by rfl⟩ : syracuseStep 4308731 = 6463097) B6463097
theorem B2872487 : Blo 1913435 2872487 := bstep (se 1 (by rfl) ⟨2154365, by rfl⟩ : syracuseStep 2872487 = 4308731) B4308731
theorem B1914991 : Blo 1913435 1914991 := bstep (se 1 (by rfl) ⟨1436243, by rfl⟩ : syracuseStep 1914991 = 2872487) B2872487
theorem B2872493 : Blo 1913435 2872493 := bbase (se 3 (by rfl) ⟨538592, by rfl⟩ : syracuseStep 2872493 = 1077185) (by norm_num)
theorem B1914995 : Blo 1913435 1914995 := bstep (se 1 (by rfl) ⟨1436246, by rfl⟩ : syracuseStep 1914995 = 2872493) B2872493
theorem B4308749 : Blo 1913435 4308749 := bbase (se 3 (by rfl) ⟨807890, by rfl⟩ : syracuseStep 4308749 = 1615781) (by norm_num)
theorem B2872499 : Blo 1913435 2872499 := bstep (se 1 (by rfl) ⟨2154374, by rfl⟩ : syracuseStep 2872499 = 4308749) B4308749
theorem B1914999 : Blo 1913435 1914999 := bstep (se 1 (by rfl) ⟨1436249, by rfl⟩ : syracuseStep 1914999 = 2872499) B2872499
theorem B2423677 : Blo 1913435 2423677 := bbase (se 3 (by rfl) ⟨454439, by rfl⟩ : syracuseStep 2423677 = 908879) (by norm_num)
theorem B3231569 : Blo 1913435 3231569 := bstep (se 2 (by rfl) ⟨1211838, by rfl⟩ : syracuseStep 3231569 = 2423677) B2423677
theorem B2154379 : Blo 1913435 2154379 := bstep (se 1 (by rfl) ⟨1615784, by rfl⟩ : syracuseStep 2154379 = 3231569) B3231569
theorem B2872505 : Blo 1913435 2872505 := bstep (se 2 (by rfl) ⟨1077189, by rfl⟩ : syracuseStep 2872505 = 2154379) B2154379
theorem B1915003 : Blo 1913435 1915003 := bstep (se 1 (by rfl) ⟨1436252, by rfl⟩ : syracuseStep 1915003 = 2872505) B2872505
theorem B14740501 : Blo 1913435 14740501 := bbase (se 6 (by rfl) ⟨345480, by rfl⟩ : syracuseStep 14740501 = 690961) (by norm_num)
theorem B19654001 : Blo 1913435 19654001 := bstep (se 2 (by rfl) ⟨7370250, by rfl⟩ : syracuseStep 19654001 = 14740501) B14740501
theorem B13102667 : Blo 1913435 13102667 := bstep (se 1 (by rfl) ⟨9827000, by rfl⟩ : syracuseStep 13102667 = 19654001) B19654001
theorem B8735111 : Blo 1913435 8735111 := bstep (se 1 (by rfl) ⟨6551333, by rfl⟩ : syracuseStep 8735111 = 13102667) B13102667
theorem B5823407 : Blo 1913435 5823407 := bstep (se 1 (by rfl) ⟨4367555, by rfl⟩ : syracuseStep 5823407 = 8735111) B8735111
theorem B3882271 : Blo 1913435 3882271 := bstep (se 1 (by rfl) ⟨2911703, by rfl⟩ : syracuseStep 3882271 = 5823407) B5823407
theorem B5176361 : Blo 1913435 5176361 := bstep (se 2 (by rfl) ⟨1941135, by rfl⟩ : syracuseStep 5176361 = 3882271) B3882271
theorem B3450907 : Blo 1913435 3450907 := bstep (se 1 (by rfl) ⟨2588180, by rfl⟩ : syracuseStep 3450907 = 5176361) B5176361
theorem B4601209 : Blo 1913435 4601209 := bstep (se 2 (by rfl) ⟨1725453, by rfl⟩ : syracuseStep 4601209 = 3450907) B3450907
theorem B6134945 : Blo 1913435 6134945 := bstep (se 2 (by rfl) ⟨2300604, by rfl⟩ : syracuseStep 6134945 = 4601209) B4601209
theorem B16359853 : Blo 1913435 16359853 := bstep (se 3 (by rfl) ⟨3067472, by rfl⟩ : syracuseStep 16359853 = 6134945) B6134945
theorem B21813137 : Blo 1913435 21813137 := bstep (se 2 (by rfl) ⟨8179926, by rfl⟩ : syracuseStep 21813137 = 16359853) B16359853
theorem B14542091 : Blo 1913435 14542091 := bstep (se 1 (by rfl) ⟨10906568, by rfl⟩ : syracuseStep 14542091 = 21813137) B21813137
theorem B9694727 : Blo 1913435 9694727 := bstep (se 1 (by rfl) ⟨7271045, by rfl⟩ : syracuseStep 9694727 = 14542091) B14542091
theorem B6463151 : Blo 1913435 6463151 := bstep (se 1 (by rfl) ⟨4847363, by rfl⟩ : syracuseStep 6463151 = 9694727) B9694727
theorem B4308767 : Blo 1913435 4308767 := bstep (se 1 (by rfl) ⟨3231575, by rfl⟩ : syracuseStep 4308767 = 6463151) B6463151
theorem B2872511 : Blo 1913435 2872511 := bstep (se 1 (by rfl) ⟨2154383, by rfl⟩ : syracuseStep 2872511 = 4308767) B4308767
theorem B1915007 : Blo 1913435 1915007 := bstep (se 1 (by rfl) ⟨1436255, by rfl⟩ : syracuseStep 1915007 = 2872511) B2872511
theorem B2872517 : Blo 1913435 2872517 := bbase (se 4 (by rfl) ⟨269298, by rfl⟩ : syracuseStep 2872517 = 538597) (by norm_num)
theorem B1915011 : Blo 1913435 1915011 := bstep (se 1 (by rfl) ⟨1436258, by rfl⟩ : syracuseStep 1915011 = 2872517) B2872517
theorem B3231589 : Blo 1913435 3231589 := bbase (se 4 (by rfl) ⟨302961, by rfl⟩ : syracuseStep 3231589 = 605923) (by norm_num)
theorem B4308785 : Blo 1913435 4308785 := bstep (se 2 (by rfl) ⟨1615794, by rfl⟩ : syracuseStep 4308785 = 3231589) B3231589
theorem B2872523 : Blo 1913435 2872523 := bstep (se 1 (by rfl) ⟨2154392, by rfl⟩ : syracuseStep 2872523 = 4308785) B4308785
theorem B1915015 : Blo 1913435 1915015 := bstep (se 1 (by rfl) ⟨1436261, by rfl⟩ : syracuseStep 1915015 = 2872523) B2872523
theorem B2154397 : Blo 1913435 2154397 := bbase (se 3 (by rfl) ⟨403949, by rfl⟩ : syracuseStep 2154397 = 807899) (by norm_num)
theorem B2872529 : Blo 1913435 2872529 := bstep (se 2 (by rfl) ⟨1077198, by rfl⟩ : syracuseStep 2872529 = 2154397) B2154397
theorem B1915019 : Blo 1913435 1915019 := bstep (se 1 (by rfl) ⟨1436264, by rfl⟩ : syracuseStep 1915019 = 2872529) B2872529
theorem B6463205 : Blo 1913435 6463205 := bbase (se 4 (by rfl) ⟨605925, by rfl⟩ : syracuseStep 6463205 = 1211851) (by norm_num)
theorem B4308803 : Blo 1913435 4308803 := bstep (se 1 (by rfl) ⟨3231602, by rfl⟩ : syracuseStep 4308803 = 6463205) B6463205
theorem B2872535 : Blo 1913435 2872535 := bstep (se 1 (by rfl) ⟨2154401, by rfl⟩ : syracuseStep 2872535 = 4308803) B4308803
theorem B1915023 : Blo 1913435 1915023 := bstep (se 1 (by rfl) ⟨1436267, by rfl⟩ : syracuseStep 1915023 = 2872535) B2872535
theorem B2872541 : Blo 1913435 2872541 := bbase (se 3 (by rfl) ⟨538601, by rfl⟩ : syracuseStep 2872541 = 1077203) (by norm_num)
theorem B1915027 : Blo 1913435 1915027 := bstep (se 1 (by rfl) ⟨1436270, by rfl⟩ : syracuseStep 1915027 = 2872541) B2872541
theorem B4308821 : Blo 1913435 4308821 := bbase (se 9 (by rfl) ⟨12623, by rfl⟩ : syracuseStep 4308821 = 25247) (by norm_num)
theorem B2872547 : Blo 1913435 2872547 := bstep (se 1 (by rfl) ⟨2154410, by rfl⟩ : syracuseStep 2872547 = 4308821) B4308821
theorem B1915031 : Blo 1913435 1915031 := bstep (se 1 (by rfl) ⟨1436273, by rfl⟩ : syracuseStep 1915031 = 2872547) B2872547
theorem B5453365 : Blo 1913435 5453365 := bbase (se 5 (by rfl) ⟨255626, by rfl⟩ : syracuseStep 5453365 = 511253) (by norm_num)
theorem B7271153 : Blo 1913435 7271153 := bstep (se 2 (by rfl) ⟨2726682, by rfl⟩ : syracuseStep 7271153 = 5453365) B5453365
theorem B4847435 : Blo 1913435 4847435 := bstep (se 1 (by rfl) ⟨3635576, by rfl⟩ : syracuseStep 4847435 = 7271153) B7271153
theorem B3231623 : Blo 1913435 3231623 := bstep (se 1 (by rfl) ⟨2423717, by rfl⟩ : syracuseStep 3231623 = 4847435) B4847435
theorem B2154415 : Blo 1913435 2154415 := bstep (se 1 (by rfl) ⟨1615811, by rfl⟩ : syracuseStep 2154415 = 3231623) B3231623
theorem B2872553 : Blo 1913435 2872553 := bstep (se 2 (by rfl) ⟨1077207, by rfl⟩ : syracuseStep 2872553 = 2154415) B2154415
theorem B1915035 : Blo 1913435 1915035 := bstep (se 1 (by rfl) ⟨1436276, by rfl⟩ : syracuseStep 1915035 = 2872553) B2872553
theorem B3988997 : Blo 1913435 3988997 := bbase (se 4 (by rfl) ⟨373968, by rfl⟩ : syracuseStep 3988997 = 747937) (by norm_num)
theorem B2659331 : Blo 1913435 2659331 := bstep (se 1 (by rfl) ⟨1994498, by rfl⟩ : syracuseStep 2659331 = 3988997) B3988997
theorem B7091549 : Blo 1913435 7091549 := bstep (se 3 (by rfl) ⟨1329665, by rfl⟩ : syracuseStep 7091549 = 2659331) B2659331
theorem B4727699 : Blo 1913435 4727699 := bstep (se 1 (by rfl) ⟨3545774, by rfl⟩ : syracuseStep 4727699 = 7091549) B7091549
theorem B3151799 : Blo 1913435 3151799 := bstep (se 1 (by rfl) ⟨2363849, by rfl⟩ : syracuseStep 3151799 = 4727699) B4727699
theorem B2101199 : Blo 1913435 2101199 := bstep (se 1 (by rfl) ⟨1575899, by rfl⟩ : syracuseStep 2101199 = 3151799) B3151799
theorem B5603197 : Blo 1913435 5603197 := bstep (se 3 (by rfl) ⟨1050599, by rfl⟩ : syracuseStep 5603197 = 2101199) B2101199
theorem B7470929 : Blo 1913435 7470929 := bstep (se 2 (by rfl) ⟨2801598, by rfl⟩ : syracuseStep 7470929 = 5603197) B5603197
theorem B4980619 : Blo 1913435 4980619 := bstep (se 1 (by rfl) ⟨3735464, by rfl⟩ : syracuseStep 4980619 = 7470929) B7470929
theorem B26563301 : Blo 1913435 26563301 := bstep (se 4 (by rfl) ⟨2490309, by rfl⟩ : syracuseStep 26563301 = 4980619) B4980619
theorem B17708867 : Blo 1913435 17708867 := bstep (se 1 (by rfl) ⟨13281650, by rfl⟩ : syracuseStep 17708867 = 26563301) B26563301
theorem B11805911 : Blo 1913435 11805911 := bstep (se 1 (by rfl) ⟨8854433, by rfl⟩ : syracuseStep 11805911 = 17708867) B17708867
theorem B7870607 : Blo 1913435 7870607 := bstep (se 1 (by rfl) ⟨5902955, by rfl⟩ : syracuseStep 7870607 = 11805911) B11805911
theorem B5247071 : Blo 1913435 5247071 := bstep (se 1 (by rfl) ⟨3935303, by rfl⟩ : syracuseStep 5247071 = 7870607) B7870607
theorem B3498047 : Blo 1913435 3498047 := bstep (se 1 (by rfl) ⟨2623535, by rfl⟩ : syracuseStep 3498047 = 5247071) B5247071
theorem B149250005 : Blo 1913435 149250005 := bstep (se 7 (by rfl) ⟨1749023, by rfl⟩ : syracuseStep 149250005 = 3498047) B3498047
theorem B99500003 : Blo 1913435 99500003 := bstep (se 1 (by rfl) ⟨74625002, by rfl⟩ : syracuseStep 99500003 = 149250005) B149250005
theorem B66333335 : Blo 1913435 66333335 := bstep (se 1 (by rfl) ⟨49750001, by rfl⟩ : syracuseStep 66333335 = 99500003) B99500003
theorem B176888893 : Blo 1913435 176888893 := bstep (se 3 (by rfl) ⟨33166667, by rfl⟩ : syracuseStep 176888893 = 66333335) B66333335
theorem B235851857 : Blo 1913435 235851857 := bstep (se 2 (by rfl) ⟨88444446, by rfl⟩ : syracuseStep 235851857 = 176888893) B176888893
theorem B157234571 : Blo 1913435 157234571 := bstep (se 1 (by rfl) ⟨117925928, by rfl⟩ : syracuseStep 157234571 = 235851857) B235851857
theorem B104823047 : Blo 1913435 104823047 := bstep (se 1 (by rfl) ⟨78617285, by rfl⟩ : syracuseStep 104823047 = 157234571) B157234571
theorem B69882031 : Blo 1913435 69882031 := bstep (se 1 (by rfl) ⟨52411523, by rfl⟩ : syracuseStep 69882031 = 104823047) B104823047
theorem B93176041 : Blo 1913435 93176041 := bstep (se 2 (by rfl) ⟨34941015, by rfl⟩ : syracuseStep 93176041 = 69882031) B69882031
theorem B124234721 : Blo 1913435 124234721 := bstep (se 2 (by rfl) ⟨46588020, by rfl⟩ : syracuseStep 124234721 = 93176041) B93176041
theorem B82823147 : Blo 1913435 82823147 := bstep (se 1 (by rfl) ⟨62117360, by rfl⟩ : syracuseStep 82823147 = 124234721) B124234721
theorem B55215431 : Blo 1913435 55215431 := bstep (se 1 (by rfl) ⟨41411573, by rfl⟩ : syracuseStep 55215431 = 82823147) B82823147
theorem B36810287 : Blo 1913435 36810287 := bstep (se 1 (by rfl) ⟨27607715, by rfl⟩ : syracuseStep 36810287 = 55215431) B55215431
theorem B24540191 : Blo 1913435 24540191 := bstep (se 1 (by rfl) ⟨18405143, by rfl⟩ : syracuseStep 24540191 = 36810287) B36810287
theorem B16360127 : Blo 1913435 16360127 := bstep (se 1 (by rfl) ⟨12270095, by rfl⟩ : syracuseStep 16360127 = 24540191) B24540191
theorem B10906751 : Blo 1913435 10906751 := bstep (se 1 (by rfl) ⟨8180063, by rfl⟩ : syracuseStep 10906751 = 16360127) B16360127
theorem B7271167 : Blo 1913435 7271167 := bstep (se 1 (by rfl) ⟨5453375, by rfl⟩ : syracuseStep 7271167 = 10906751) B10906751
theorem B9694889 : Blo 1913435 9694889 := bstep (se 2 (by rfl) ⟨3635583, by rfl⟩ : syracuseStep 9694889 = 7271167) B7271167
theorem B6463259 : Blo 1913435 6463259 := bstep (se 1 (by rfl) ⟨4847444, by rfl⟩ : syracuseStep 6463259 = 9694889) B9694889
theorem B4308839 : Blo 1913435 4308839 := bstep (se 1 (by rfl) ⟨3231629, by rfl⟩ : syracuseStep 4308839 = 6463259) B6463259
theorem B2872559 : Blo 1913435 2872559 := bstep (se 1 (by rfl) ⟨2154419, by rfl⟩ : syracuseStep 2872559 = 4308839) B4308839
theorem B1915039 : Blo 1913435 1915039 := bstep (se 1 (by rfl) ⟨1436279, by rfl⟩ : syracuseStep 1915039 = 2872559) B2872559
theorem B2872565 : Blo 1913435 2872565 := bbase (se 5 (by rfl) ⟨134651, by rfl⟩ : syracuseStep 2872565 = 269303) (by norm_num)
theorem B1915043 : Blo 1913435 1915043 := bstep (se 1 (by rfl) ⟨1436282, by rfl⟩ : syracuseStep 1915043 = 2872565) B2872565
theorem B2300653 : Blo 1913435 2300653 := bbase (se 3 (by rfl) ⟨431372, by rfl⟩ : syracuseStep 2300653 = 862745) (by norm_num)
theorem B12270149 : Blo 1913435 12270149 := bstep (se 4 (by rfl) ⟨1150326, by rfl⟩ : syracuseStep 12270149 = 2300653) B2300653
theorem B8180099 : Blo 1913435 8180099 := bstep (se 1 (by rfl) ⟨6135074, by rfl⟩ : syracuseStep 8180099 = 12270149) B12270149
theorem B5453399 : Blo 1913435 5453399 := bstep (se 1 (by rfl) ⟨4090049, by rfl⟩ : syracuseStep 5453399 = 8180099) B8180099
theorem B3635599 : Blo 1913435 3635599 := bstep (se 1 (by rfl) ⟨2726699, by rfl⟩ : syracuseStep 3635599 = 5453399) B5453399
theorem B4847465 : Blo 1913435 4847465 := bstep (se 2 (by rfl) ⟨1817799, by rfl⟩ : syracuseStep 4847465 = 3635599) B3635599
theorem B3231643 : Blo 1913435 3231643 := bstep (se 1 (by rfl) ⟨2423732, by rfl⟩ : syracuseStep 3231643 = 4847465) B4847465
theorem B4308857 : Blo 1913435 4308857 := bstep (se 2 (by rfl) ⟨1615821, by rfl⟩ : syracuseStep 4308857 = 3231643) B3231643
theorem B2872571 : Blo 1913435 2872571 := bstep (se 1 (by rfl) ⟨2154428, by rfl⟩ : syracuseStep 2872571 = 4308857) B4308857
theorem B1915047 : Blo 1913435 1915047 := bstep (se 1 (by rfl) ⟨1436285, by rfl⟩ : syracuseStep 1915047 = 2872571) B2872571
theorem B2154433 : Blo 1913435 2154433 := bbase (se 2 (by rfl) ⟨807912, by rfl⟩ : syracuseStep 2154433 = 1615825) (by norm_num)
theorem B2872577 : Blo 1913435 2872577 := bstep (se 2 (by rfl) ⟨1077216, by rfl⟩ : syracuseStep 2872577 = 2154433) B2154433
theorem B1915051 : Blo 1913435 1915051 := bstep (se 1 (by rfl) ⟨1436288, by rfl⟩ : syracuseStep 1915051 = 2872577) B2872577
theorem B4847485 : Blo 1913435 4847485 := bbase (se 3 (by rfl) ⟨908903, by rfl⟩ : syracuseStep 4847485 = 1817807) (by norm_num)
theorem B6463313 : Blo 1913435 6463313 := bstep (se 2 (by rfl) ⟨2423742, by rfl⟩ : syracuseStep 6463313 = 4847485) B4847485
theorem B4308875 : Blo 1913435 4308875 := bstep (se 1 (by rfl) ⟨3231656, by rfl⟩ : syracuseStep 4308875 = 6463313) B6463313
theorem B2872583 : Blo 1913435 2872583 := bstep (se 1 (by rfl) ⟨2154437, by rfl⟩ : syracuseStep 2872583 = 4308875) B4308875
theorem B1915055 : Blo 1913435 1915055 := bstep (se 1 (by rfl) ⟨1436291, by rfl⟩ : syracuseStep 1915055 = 2872583) B2872583
theorem B2872589 : Blo 1913435 2872589 := bbase (se 3 (by rfl) ⟨538610, by rfl⟩ : syracuseStep 2872589 = 1077221) (by norm_num)
theorem B1915059 : Blo 1913435 1915059 := bstep (se 1 (by rfl) ⟨1436294, by rfl⟩ : syracuseStep 1915059 = 2872589) B2872589
theorem B4308893 : Blo 1913435 4308893 := bbase (se 3 (by rfl) ⟨807917, by rfl⟩ : syracuseStep 4308893 = 1615835) (by norm_num)
theorem B2872595 : Blo 1913435 2872595 := bstep (se 1 (by rfl) ⟨2154446, by rfl⟩ : syracuseStep 2872595 = 4308893) B4308893
theorem B1915063 : Blo 1913435 1915063 := bstep (se 1 (by rfl) ⟨1436297, by rfl⟩ : syracuseStep 1915063 = 2872595) B2872595
theorem B3231677 : Blo 1913435 3231677 := bbase (se 3 (by rfl) ⟨605939, by rfl⟩ : syracuseStep 3231677 = 1211879) (by norm_num)
theorem B2154451 : Blo 1913435 2154451 := bstep (se 1 (by rfl) ⟨1615838, by rfl⟩ : syracuseStep 2154451 = 3231677) B3231677
theorem B2872601 : Blo 1913435 2872601 := bstep (se 2 (by rfl) ⟨1077225, by rfl⟩ : syracuseStep 2872601 = 2154451) B2154451
theorem B1915067 : Blo 1913435 1915067 := bstep (se 1 (by rfl) ⟨1436300, by rfl⟩ : syracuseStep 1915067 = 2872601) B2872601
theorem B10906933 : Blo 1913435 10906933 := bbase (se 5 (by rfl) ⟨511262, by rfl⟩ : syracuseStep 10906933 = 1022525) (by norm_num)
theorem B14542577 : Blo 1913435 14542577 := bstep (se 2 (by rfl) ⟨5453466, by rfl⟩ : syracuseStep 14542577 = 10906933) B10906933
theorem B9695051 : Blo 1913435 9695051 := bstep (se 1 (by rfl) ⟨7271288, by rfl⟩ : syracuseStep 9695051 = 14542577) B14542577
theorem B6463367 : Blo 1913435 6463367 := bstep (se 1 (by rfl) ⟨4847525, by rfl⟩ : syracuseStep 6463367 = 9695051) B9695051
theorem B4308911 : Blo 1913435 4308911 := bstep (se 1 (by rfl) ⟨3231683, by rfl⟩ : syracuseStep 4308911 = 6463367) B6463367
theorem B2872607 : Blo 1913435 2872607 := bstep (se 1 (by rfl) ⟨2154455, by rfl⟩ : syracuseStep 2872607 = 4308911) B4308911
theorem B1915071 : Blo 1913435 1915071 := bstep (se 1 (by rfl) ⟨1436303, by rfl⟩ : syracuseStep 1915071 = 2872607) B2872607
theorem B2872613 : Blo 1913435 2872613 := bbase (se 4 (by rfl) ⟨269307, by rfl⟩ : syracuseStep 2872613 = 538615) (by norm_num)
theorem B1915075 : Blo 1913435 1915075 := bstep (se 1 (by rfl) ⟨1436306, by rfl⟩ : syracuseStep 1915075 = 2872613) B2872613
theorem B2423773 : Blo 1913435 2423773 := bbase (se 3 (by rfl) ⟨454457, by rfl⟩ : syracuseStep 2423773 = 908915) (by norm_num)
theorem B3231697 : Blo 1913435 3231697 := bstep (se 2 (by rfl) ⟨1211886, by rfl⟩ : syracuseStep 3231697 = 2423773) B2423773
theorem B4308929 : Blo 1913435 4308929 := bstep (se 2 (by rfl) ⟨1615848, by rfl⟩ : syracuseStep 4308929 = 3231697) B3231697
theorem B2872619 : Blo 1913435 2872619 := bstep (se 1 (by rfl) ⟨2154464, by rfl⟩ : syracuseStep 2872619 = 4308929) B4308929
theorem B1915079 : Blo 1913435 1915079 := bstep (se 1 (by rfl) ⟨1436309, by rfl⟩ : syracuseStep 1915079 = 2872619) B2872619
theorem B2154469 : Blo 1913435 2154469 := bbase (se 4 (by rfl) ⟨201981, by rfl⟩ : syracuseStep 2154469 = 403963) (by norm_num)
theorem B2872625 : Blo 1913435 2872625 := bstep (se 2 (by rfl) ⟨1077234, by rfl⟩ : syracuseStep 2872625 = 2154469) B2154469
theorem B1915083 : Blo 1913435 1915083 := bstep (se 1 (by rfl) ⟨1436312, by rfl⟩ : syracuseStep 1915083 = 2872625) B2872625
theorem B9202805 : Blo 1913435 9202805 := bbase (se 5 (by rfl) ⟨431381, by rfl⟩ : syracuseStep 9202805 = 862763) (by norm_num)
theorem B6135203 : Blo 1913435 6135203 := bstep (se 1 (by rfl) ⟨4601402, by rfl⟩ : syracuseStep 6135203 = 9202805) B9202805
theorem B4090135 : Blo 1913435 4090135 := bstep (se 1 (by rfl) ⟨3067601, by rfl⟩ : syracuseStep 4090135 = 6135203) B6135203
theorem B5453513 : Blo 1913435 5453513 := bstep (se 2 (by rfl) ⟨2045067, by rfl⟩ : syracuseStep 5453513 = 4090135) B4090135
theorem B3635675 : Blo 1913435 3635675 := bstep (se 1 (by rfl) ⟨2726756, by rfl⟩ : syracuseStep 3635675 = 5453513) B5453513
theorem B2423783 : Blo 1913435 2423783 := bstep (se 1 (by rfl) ⟨1817837, by rfl⟩ : syracuseStep 2423783 = 3635675) B3635675
theorem B6463421 : Blo 1913435 6463421 := bstep (se 3 (by rfl) ⟨1211891, by rfl⟩ : syracuseStep 6463421 = 2423783) B2423783
theorem B4308947 : Blo 1913435 4308947 := bstep (se 1 (by rfl) ⟨3231710, by rfl⟩ : syracuseStep 4308947 = 6463421) B6463421
theorem B2872631 : Blo 1913435 2872631 := bstep (se 1 (by rfl) ⟨2154473, by rfl⟩ : syracuseStep 2872631 = 4308947) B4308947
theorem B1915087 : Blo 1913435 1915087 := bstep (se 1 (by rfl) ⟨1436315, by rfl⟩ : syracuseStep 1915087 = 2872631) B2872631
theorem B2872637 : Blo 1913435 2872637 := bbase (se 3 (by rfl) ⟨538619, by rfl⟩ : syracuseStep 2872637 = 1077239) (by norm_num)
theorem B1915091 : Blo 1913435 1915091 := bstep (se 1 (by rfl) ⟨1436318, by rfl⟩ : syracuseStep 1915091 = 2872637) B2872637
theorem B4308965 : Blo 1913435 4308965 := bbase (se 4 (by rfl) ⟨403965, by rfl⟩ : syracuseStep 4308965 = 807931) (by norm_num)
theorem B2872643 : Blo 1913435 2872643 := bstep (se 1 (by rfl) ⟨2154482, by rfl⟩ : syracuseStep 2872643 = 4308965) B4308965
theorem B1915095 : Blo 1913435 1915095 := bstep (se 1 (by rfl) ⟨1436321, by rfl⟩ : syracuseStep 1915095 = 2872643) B2872643
theorem B4847597 : Blo 1913435 4847597 := bbase (se 3 (by rfl) ⟨908924, by rfl⟩ : syracuseStep 4847597 = 1817849) (by norm_num)
theorem B3231731 : Blo 1913435 3231731 := bstep (se 1 (by rfl) ⟨2423798, by rfl⟩ : syracuseStep 3231731 = 4847597) B4847597
theorem B2154487 : Blo 1913435 2154487 := bstep (se 1 (by rfl) ⟨1615865, by rfl⟩ : syracuseStep 2154487 = 3231731) B3231731
theorem B2872649 : Blo 1913435 2872649 := bstep (se 2 (by rfl) ⟨1077243, by rfl⟩ : syracuseStep 2872649 = 2154487) B2154487
theorem B1915099 : Blo 1913435 1915099 := bstep (se 1 (by rfl) ⟨1436324, by rfl⟩ : syracuseStep 1915099 = 2872649) B2872649
theorem B5823701 : Blo 1913435 5823701 := bbase (se 7 (by rfl) ⟨68246, by rfl⟩ : syracuseStep 5823701 = 136493) (by norm_num)
theorem B3882467 : Blo 1913435 3882467 := bstep (se 1 (by rfl) ⟨2911850, by rfl⟩ : syracuseStep 3882467 = 5823701) B5823701
theorem B2588311 : Blo 1913435 2588311 := bstep (se 1 (by rfl) ⟨1941233, by rfl⟩ : syracuseStep 2588311 = 3882467) B3882467
theorem B3451081 : Blo 1913435 3451081 := bstep (se 2 (by rfl) ⟨1294155, by rfl⟩ : syracuseStep 3451081 = 2588311) B2588311
theorem B4601441 : Blo 1913435 4601441 := bstep (se 2 (by rfl) ⟨1725540, by rfl⟩ : syracuseStep 4601441 = 3451081) B3451081
theorem B3067627 : Blo 1913435 3067627 := bstep (se 1 (by rfl) ⟨2300720, by rfl⟩ : syracuseStep 3067627 = 4601441) B4601441
theorem B4090169 : Blo 1913435 4090169 := bstep (se 2 (by rfl) ⟨1533813, by rfl⟩ : syracuseStep 4090169 = 3067627) B3067627
theorem B2726779 : Blo 1913435 2726779 := bstep (se 1 (by rfl) ⟨2045084, by rfl⟩ : syracuseStep 2726779 = 4090169) B4090169
theorem B3635705 : Blo 1913435 3635705 := bstep (se 2 (by rfl) ⟨1363389, by rfl⟩ : syracuseStep 3635705 = 2726779) B2726779
theorem B9695213 : Blo 1913435 9695213 := bstep (se 3 (by rfl) ⟨1817852, by rfl⟩ : syracuseStep 9695213 = 3635705) B3635705
theorem B6463475 : Blo 1913435 6463475 := bstep (se 1 (by rfl) ⟨4847606, by rfl⟩ : syracuseStep 6463475 = 9695213) B9695213
theorem B4308983 : Blo 1913435 4308983 := bstep (se 1 (by rfl) ⟨3231737, by rfl⟩ : syracuseStep 4308983 = 6463475) B6463475
theorem B2872655 : Blo 1913435 2872655 := bstep (se 1 (by rfl) ⟨2154491, by rfl⟩ : syracuseStep 2872655 = 4308983) B4308983
theorem B1915103 : Blo 1913435 1915103 := bstep (se 1 (by rfl) ⟨1436327, by rfl⟩ : syracuseStep 1915103 = 2872655) B2872655
theorem B2872661 : Blo 1913435 2872661 := bbase (se 15 (by rfl) ⟨131, by rfl⟩ : syracuseStep 2872661 = 263) (by norm_num)
theorem B1915107 : Blo 1913435 1915107 := bstep (se 1 (by rfl) ⟨1436330, by rfl⟩ : syracuseStep 1915107 = 2872661) B2872661
theorem B2045093 : Blo 1913435 2045093 := bbase (se 4 (by rfl) ⟨191727, by rfl⟩ : syracuseStep 2045093 = 383455) (by norm_num)
theorem B5453581 : Blo 1913435 5453581 := bstep (se 3 (by rfl) ⟨1022546, by rfl⟩ : syracuseStep 5453581 = 2045093) B2045093
theorem B7271441 : Blo 1913435 7271441 := bstep (se 2 (by rfl) ⟨2726790, by rfl⟩ : syracuseStep 7271441 = 5453581) B5453581
theorem B4847627 : Blo 1913435 4847627 := bstep (se 1 (by rfl) ⟨3635720, by rfl⟩ : syracuseStep 4847627 = 7271441) B7271441
theorem B3231751 : Blo 1913435 3231751 := bstep (se 1 (by rfl) ⟨2423813, by rfl⟩ : syracuseStep 3231751 = 4847627) B4847627
theorem B4309001 : Blo 1913435 4309001 := bstep (se 2 (by rfl) ⟨1615875, by rfl⟩ : syracuseStep 4309001 = 3231751) B3231751
theorem B2872667 : Blo 1913435 2872667 := bstep (se 1 (by rfl) ⟨2154500, by rfl⟩ : syracuseStep 2872667 = 4309001) B4309001
theorem B1915111 : Blo 1913435 1915111 := bstep (se 1 (by rfl) ⟨1436333, by rfl⟩ : syracuseStep 1915111 = 2872667) B2872667
theorem B2154505 : Blo 1913435 2154505 := bbase (se 2 (by rfl) ⟨807939, by rfl⟩ : syracuseStep 2154505 = 1615879) (by norm_num)
theorem B2872673 : Blo 1913435 2872673 := bstep (se 2 (by rfl) ⟨1077252, by rfl⟩ : syracuseStep 2872673 = 2154505) B2154505
theorem B1915115 : Blo 1913435 1915115 := bstep (se 1 (by rfl) ⟨1436336, by rfl⟩ : syracuseStep 1915115 = 2872673) B2872673
theorem B2183905 : Blo 1913435 2183905 := bbase (se 2 (by rfl) ⟨818964, by rfl⟩ : syracuseStep 2183905 = 1637929) (by norm_num)
theorem B11647493 : Blo 1913435 11647493 := bstep (se 4 (by rfl) ⟨1091952, by rfl⟩ : syracuseStep 11647493 = 2183905) B2183905
theorem B7764995 : Blo 1913435 7764995 := bstep (se 1 (by rfl) ⟨5823746, by rfl⟩ : syracuseStep 7764995 = 11647493) B11647493
theorem B20706653 : Blo 1913435 20706653 := bstep (se 3 (by rfl) ⟨3882497, by rfl⟩ : syracuseStep 20706653 = 7764995) B7764995
theorem B13804435 : Blo 1913435 13804435 := bstep (se 1 (by rfl) ⟨10353326, by rfl⟩ : syracuseStep 13804435 = 20706653) B20706653
theorem B18405913 : Blo 1913435 18405913 := bstep (se 2 (by rfl) ⟨6902217, by rfl⟩ : syracuseStep 18405913 = 13804435) B13804435
theorem B24541217 : Blo 1913435 24541217 := bstep (se 2 (by rfl) ⟨9202956, by rfl⟩ : syracuseStep 24541217 = 18405913) B18405913
theorem B16360811 : Blo 1913435 16360811 := bstep (se 1 (by rfl) ⟨12270608, by rfl⟩ : syracuseStep 16360811 = 24541217) B24541217
theorem B10907207 : Blo 1913435 10907207 := bstep (se 1 (by rfl) ⟨8180405, by rfl⟩ : syracuseStep 10907207 = 16360811) B16360811
theorem B7271471 : Blo 1913435 7271471 := bstep (se 1 (by rfl) ⟨5453603, by rfl⟩ : syracuseStep 7271471 = 10907207) B10907207
theorem B4847647 : Blo 1913435 4847647 := bstep (se 1 (by rfl) ⟨3635735, by rfl⟩ : syracuseStep 4847647 = 7271471) B7271471
theorem B6463529 : Blo 1913435 6463529 := bstep (se 2 (by rfl) ⟨2423823, by rfl⟩ : syracuseStep 6463529 = 4847647) B4847647
theorem B4309019 : Blo 1913435 4309019 := bstep (se 1 (by rfl) ⟨3231764, by rfl⟩ : syracuseStep 4309019 = 6463529) B6463529
theorem B2872679 : Blo 1913435 2872679 := bstep (se 1 (by rfl) ⟨2154509, by rfl⟩ : syracuseStep 2872679 = 4309019) B4309019
theorem B1915119 : Blo 1913435 1915119 := bstep (se 1 (by rfl) ⟨1436339, by rfl⟩ : syracuseStep 1915119 = 2872679) B2872679
theorem B2872685 : Blo 1913435 2872685 := bbase (se 3 (by rfl) ⟨538628, by rfl⟩ : syracuseStep 2872685 = 1077257) (by norm_num)
theorem B1915123 : Blo 1913435 1915123 := bstep (se 1 (by rfl) ⟨1436342, by rfl⟩ : syracuseStep 1915123 = 2872685) B2872685
theorem B4309037 : Blo 1913435 4309037 := bbase (se 3 (by rfl) ⟨807944, by rfl⟩ : syracuseStep 4309037 = 1615889) (by norm_num)
theorem B2872691 : Blo 1913435 2872691 := bstep (se 1 (by rfl) ⟨2154518, by rfl⟩ : syracuseStep 2872691 = 4309037) B4309037
theorem B1915127 : Blo 1913435 1915127 := bstep (se 1 (by rfl) ⟨1436345, by rfl⟩ : syracuseStep 1915127 = 2872691) B2872691
theorem B19923445 : Blo 1913435 19923445 := bbase (se 5 (by rfl) ⟨933911, by rfl⟩ : syracuseStep 19923445 = 1867823) (by norm_num)
theorem B26564593 : Blo 1913435 26564593 := bstep (se 2 (by rfl) ⟨9961722, by rfl⟩ : syracuseStep 26564593 = 19923445) B19923445
theorem B35419457 : Blo 1913435 35419457 := bstep (se 2 (by rfl) ⟨13282296, by rfl⟩ : syracuseStep 35419457 = 26564593) B26564593
theorem B23612971 : Blo 1913435 23612971 := bstep (se 1 (by rfl) ⟨17709728, by rfl⟩ : syracuseStep 23612971 = 35419457) B35419457
theorem B31483961 : Blo 1913435 31483961 := bstep (se 2 (by rfl) ⟨11806485, by rfl⟩ : syracuseStep 31483961 = 23612971) B23612971
theorem B20989307 : Blo 1913435 20989307 := bstep (se 1 (by rfl) ⟨15741980, by rfl⟩ : syracuseStep 20989307 = 31483961) B31483961
theorem B13992871 : Blo 1913435 13992871 := bstep (se 1 (by rfl) ⟨10494653, by rfl⟩ : syracuseStep 13992871 = 20989307) B20989307
theorem B18657161 : Blo 1913435 18657161 := bstep (se 2 (by rfl) ⟨6996435, by rfl⟩ : syracuseStep 18657161 = 13992871) B13992871
theorem B12438107 : Blo 1913435 12438107 := bstep (se 1 (by rfl) ⟨9328580, by rfl⟩ : syracuseStep 12438107 = 18657161) B18657161
theorem B8292071 : Blo 1913435 8292071 := bstep (se 1 (by rfl) ⟨6219053, by rfl⟩ : syracuseStep 8292071 = 12438107) B12438107
theorem B22112189 : Blo 1913435 22112189 := bstep (se 3 (by rfl) ⟨4146035, by rfl⟩ : syracuseStep 22112189 = 8292071) B8292071
theorem B14741459 : Blo 1913435 14741459 := bstep (se 1 (by rfl) ⟨11056094, by rfl⟩ : syracuseStep 14741459 = 22112189) B22112189
theorem B9827639 : Blo 1913435 9827639 := bstep (se 1 (by rfl) ⟨7370729, by rfl⟩ : syracuseStep 9827639 = 14741459) B14741459
theorem B6551759 : Blo 1913435 6551759 := bstep (se 1 (by rfl) ⟨4913819, by rfl⟩ : syracuseStep 6551759 = 9827639) B9827639
theorem B4367839 : Blo 1913435 4367839 := bstep (se 1 (by rfl) ⟨3275879, by rfl⟩ : syracuseStep 4367839 = 6551759) B6551759
theorem B5823785 : Blo 1913435 5823785 := bstep (se 2 (by rfl) ⟨2183919, by rfl⟩ : syracuseStep 5823785 = 4367839) B4367839
theorem B15530093 : Blo 1913435 15530093 := bstep (se 3 (by rfl) ⟨2911892, by rfl⟩ : syracuseStep 15530093 = 5823785) B5823785
theorem B10353395 : Blo 1913435 10353395 := bstep (se 1 (by rfl) ⟨7765046, by rfl⟩ : syracuseStep 10353395 = 15530093) B15530093
theorem B6902263 : Blo 1913435 6902263 := bstep (se 1 (by rfl) ⟨5176697, by rfl⟩ : syracuseStep 6902263 = 10353395) B10353395
theorem B9203017 : Blo 1913435 9203017 := bstep (se 2 (by rfl) ⟨3451131, by rfl⟩ : syracuseStep 9203017 = 6902263) B6902263
theorem B12270689 : Blo 1913435 12270689 := bstep (se 2 (by rfl) ⟨4601508, by rfl⟩ : syracuseStep 12270689 = 9203017) B9203017
theorem B8180459 : Blo 1913435 8180459 := bstep (se 1 (by rfl) ⟨6135344, by rfl⟩ : syracuseStep 8180459 = 12270689) B12270689
theorem B5453639 : Blo 1913435 5453639 := bstep (se 1 (by rfl) ⟨4090229, by rfl⟩ : syracuseStep 5453639 = 8180459) B8180459
theorem B3635759 : Blo 1913435 3635759 := bstep (se 1 (by rfl) ⟨2726819, by rfl⟩ : syracuseStep 3635759 = 5453639) B5453639
theorem B2423839 : Blo 1913435 2423839 := bstep (se 1 (by rfl) ⟨1817879, by rfl⟩ : syracuseStep 2423839 = 3635759) B3635759
theorem B3231785 : Blo 1913435 3231785 := bstep (se 2 (by rfl) ⟨1211919, by rfl⟩ : syracuseStep 3231785 = 2423839) B2423839
theorem B2154523 : Blo 1913435 2154523 := bstep (se 1 (by rfl) ⟨1615892, by rfl⟩ : syracuseStep 2154523 = 3231785) B3231785
theorem B2872697 : Blo 1913435 2872697 := bstep (se 2 (by rfl) ⟨1077261, by rfl⟩ : syracuseStep 2872697 = 2154523) B2154523
theorem B1915131 : Blo 1913435 1915131 := bstep (se 1 (by rfl) ⟨1436348, by rfl⟩ : syracuseStep 1915131 = 2872697) B2872697
theorem B1941265 : Blo 1913435 1941265 := bbase (se 2 (by rfl) ⟨727974, by rfl⟩ : syracuseStep 1941265 = 1455949) (by norm_num)
theorem B10353413 : Blo 1913435 10353413 := bstep (se 4 (by rfl) ⟨970632, by rfl⟩ : syracuseStep 10353413 = 1941265) B1941265
theorem B6902275 : Blo 1913435 6902275 := bstep (se 1 (by rfl) ⟨5176706, by rfl⟩ : syracuseStep 6902275 = 10353413) B10353413
theorem B9203033 : Blo 1913435 9203033 := bstep (se 2 (by rfl) ⟨3451137, by rfl⟩ : syracuseStep 9203033 = 6902275) B6902275
theorem B6135355 : Blo 1913435 6135355 := bstep (se 1 (by rfl) ⟨4601516, by rfl⟩ : syracuseStep 6135355 = 9203033) B9203033
theorem B32721893 : Blo 1913435 32721893 := bstep (se 4 (by rfl) ⟨3067677, by rfl⟩ : syracuseStep 32721893 = 6135355) B6135355
theorem B21814595 : Blo 1913435 21814595 := bstep (se 1 (by rfl) ⟨16360946, by rfl⟩ : syracuseStep 21814595 = 32721893) B32721893
theorem B14543063 : Blo 1913435 14543063 := bstep (se 1 (by rfl) ⟨10907297, by rfl⟩ : syracuseStep 14543063 = 21814595) B21814595
theorem B9695375 : Blo 1913435 9695375 := bstep (se 1 (by rfl) ⟨7271531, by rfl⟩ : syracuseStep 9695375 = 14543063) B14543063
theorem B6463583 : Blo 1913435 6463583 := bstep (se 1 (by rfl) ⟨4847687, by rfl⟩ : syracuseStep 6463583 = 9695375) B9695375
theorem B4309055 : Blo 1913435 4309055 := bstep (se 1 (by rfl) ⟨3231791, by rfl⟩ : syracuseStep 4309055 = 6463583) B6463583
theorem B2872703 : Blo 1913435 2872703 := bstep (se 1 (by rfl) ⟨2154527, by rfl⟩ : syracuseStep 2872703 = 4309055) B4309055
theorem B1915135 : Blo 1913435 1915135 := bstep (se 1 (by rfl) ⟨1436351, by rfl⟩ : syracuseStep 1915135 = 2872703) B2872703
theorem B2872709 : Blo 1913435 2872709 := bbase (se 4 (by rfl) ⟨269316, by rfl⟩ : syracuseStep 2872709 = 538633) (by norm_num)
theorem B1915139 : Blo 1913435 1915139 := bstep (se 1 (by rfl) ⟨1436354, by rfl⟩ : syracuseStep 1915139 = 2872709) B2872709
theorem B3231805 : Blo 1913435 3231805 := bbase (se 3 (by rfl) ⟨605963, by rfl⟩ : syracuseStep 3231805 = 1211927) (by norm_num)
theorem B4309073 : Blo 1913435 4309073 := bstep (se 2 (by rfl) ⟨1615902, by rfl⟩ : syracuseStep 4309073 = 3231805) B3231805
theorem B2872715 : Blo 1913435 2872715 := bstep (se 1 (by rfl) ⟨2154536, by rfl⟩ : syracuseStep 2872715 = 4309073) B4309073
theorem B1915143 : Blo 1913435 1915143 := bstep (se 1 (by rfl) ⟨1436357, by rfl⟩ : syracuseStep 1915143 = 2872715) B2872715
theorem B2154541 : Blo 1913435 2154541 := bbase (se 3 (by rfl) ⟨403976, by rfl⟩ : syracuseStep 2154541 = 807953) (by norm_num)
theorem B2872721 : Blo 1913435 2872721 := bstep (se 2 (by rfl) ⟨1077270, by rfl⟩ : syracuseStep 2872721 = 2154541) B2154541
theorem B1915147 : Blo 1913435 1915147 := bstep (se 1 (by rfl) ⟨1436360, by rfl⟩ : syracuseStep 1915147 = 2872721) B2872721
theorem B6463637 : Blo 1913435 6463637 := bbase (se 6 (by rfl) ⟨151491, by rfl⟩ : syracuseStep 6463637 = 302983) (by norm_num)
theorem B4309091 : Blo 1913435 4309091 := bstep (se 1 (by rfl) ⟨3231818, by rfl⟩ : syracuseStep 4309091 = 6463637) B6463637
theorem B2872727 : Blo 1913435 2872727 := bstep (se 1 (by rfl) ⟨2154545, by rfl⟩ : syracuseStep 2872727 = 4309091) B4309091
theorem B1915151 : Blo 1913435 1915151 := bstep (se 1 (by rfl) ⟨1436363, by rfl⟩ : syracuseStep 1915151 = 2872727) B2872727
theorem B2872733 : Blo 1913435 2872733 := bbase (se 3 (by rfl) ⟨538637, by rfl⟩ : syracuseStep 2872733 = 1077275) (by norm_num)
theorem B1915155 : Blo 1913435 1915155 := bstep (se 1 (by rfl) ⟨1436366, by rfl⟩ : syracuseStep 1915155 = 2872733) B2872733
theorem B4309109 : Blo 1913435 4309109 := bbase (se 5 (by rfl) ⟨201989, by rfl⟩ : syracuseStep 4309109 = 403979) (by norm_num)
theorem B2872739 : Blo 1913435 2872739 := bstep (se 1 (by rfl) ⟨2154554, by rfl⟩ : syracuseStep 2872739 = 4309109) B4309109
theorem B1915159 : Blo 1913435 1915159 := bstep (se 1 (by rfl) ⟨1436369, by rfl⟩ : syracuseStep 1915159 = 2872739) B2872739
theorem B3451189 : Blo 1913435 3451189 := bbase (se 5 (by rfl) ⟨161774, by rfl⟩ : syracuseStep 3451189 = 323549) (by norm_num)
theorem B4601585 : Blo 1913435 4601585 := bstep (se 2 (by rfl) ⟨1725594, by rfl⟩ : syracuseStep 4601585 = 3451189) B3451189
theorem B3067723 : Blo 1913435 3067723 := bstep (se 1 (by rfl) ⟨2300792, by rfl⟩ : syracuseStep 3067723 = 4601585) B4601585
theorem B16361189 : Blo 1913435 16361189 := bstep (se 4 (by rfl) ⟨1533861, by rfl⟩ : syracuseStep 16361189 = 3067723) B3067723
theorem B10907459 : Blo 1913435 10907459 := bstep (se 1 (by rfl) ⟨8180594, by rfl⟩ : syracuseStep 10907459 = 16361189) B16361189
theorem B7271639 : Blo 1913435 7271639 := bstep (se 1 (by rfl) ⟨5453729, by rfl⟩ : syracuseStep 7271639 = 10907459) B10907459
theorem B4847759 : Blo 1913435 4847759 := bstep (se 1 (by rfl) ⟨3635819, by rfl⟩ : syracuseStep 4847759 = 7271639) B7271639
theorem B3231839 : Blo 1913435 3231839 := bstep (se 1 (by rfl) ⟨2423879, by rfl⟩ : syracuseStep 3231839 = 4847759) B4847759
theorem B2154559 : Blo 1913435 2154559 := bstep (se 1 (by rfl) ⟨1615919, by rfl⟩ : syracuseStep 2154559 = 3231839) B3231839
theorem B2872745 : Blo 1913435 2872745 := bstep (se 2 (by rfl) ⟨1077279, by rfl⟩ : syracuseStep 2872745 = 2154559) B2154559
theorem B1915163 : Blo 1913435 1915163 := bstep (se 1 (by rfl) ⟨1436372, by rfl⟩ : syracuseStep 1915163 = 2872745) B2872745
theorem B7271653 : Blo 1913435 7271653 := bbase (se 4 (by rfl) ⟨681717, by rfl⟩ : syracuseStep 7271653 = 1363435) (by norm_num)
theorem B9695537 : Blo 1913435 9695537 := bstep (se 2 (by rfl) ⟨3635826, by rfl⟩ : syracuseStep 9695537 = 7271653) B7271653
theorem B6463691 : Blo 1913435 6463691 := bstep (se 1 (by rfl) ⟨4847768, by rfl⟩ : syracuseStep 6463691 = 9695537) B9695537
theorem B4309127 : Blo 1913435 4309127 := bstep (se 1 (by rfl) ⟨3231845, by rfl⟩ : syracuseStep 4309127 = 6463691) B6463691
theorem B2872751 : Blo 1913435 2872751 := bstep (se 1 (by rfl) ⟨2154563, by rfl⟩ : syracuseStep 2872751 = 4309127) B4309127
theorem B1915167 : Blo 1913435 1915167 := bstep (se 1 (by rfl) ⟨1436375, by rfl⟩ : syracuseStep 1915167 = 2872751) B2872751
theorem B2872757 : Blo 1913435 2872757 := bbase (se 5 (by rfl) ⟨134660, by rfl⟩ : syracuseStep 2872757 = 269321) (by norm_num)
theorem B1915171 : Blo 1913435 1915171 := bstep (se 1 (by rfl) ⟨1436378, by rfl⟩ : syracuseStep 1915171 = 2872757) B2872757
theorem B4847789 : Blo 1913435 4847789 := bbase (se 3 (by rfl) ⟨908960, by rfl⟩ : syracuseStep 4847789 = 1817921) (by norm_num)
theorem B3231859 : Blo 1913435 3231859 := bstep (se 1 (by rfl) ⟨2423894, by rfl⟩ : syracuseStep 3231859 = 4847789) B4847789
theorem B4309145 : Blo 1913435 4309145 := bstep (se 2 (by rfl) ⟨1615929, by rfl⟩ : syracuseStep 4309145 = 3231859) B3231859
theorem B2872763 : Blo 1913435 2872763 := bstep (se 1 (by rfl) ⟨2154572, by rfl⟩ : syracuseStep 2872763 = 4309145) B4309145
theorem B1915175 : Blo 1913435 1915175 := bstep (se 1 (by rfl) ⟨1436381, by rfl⟩ : syracuseStep 1915175 = 2872763) B2872763
theorem B2154577 : Blo 1913435 2154577 := bbase (se 2 (by rfl) ⟨807966, by rfl⟩ : syracuseStep 2154577 = 1615933) (by norm_num)
theorem B2872769 : Blo 1913435 2872769 := bstep (se 2 (by rfl) ⟨1077288, by rfl⟩ : syracuseStep 2872769 = 2154577) B2154577
theorem B1915179 : Blo 1913435 1915179 := bstep (se 1 (by rfl) ⟨1436384, by rfl⟩ : syracuseStep 1915179 = 2872769) B2872769
theorem B2726893 : Blo 1913435 2726893 := bbase (se 3 (by rfl) ⟨511292, by rfl⟩ : syracuseStep 2726893 = 1022585) (by norm_num)
theorem B3635857 : Blo 1913435 3635857 := bstep (se 2 (by rfl) ⟨1363446, by rfl⟩ : syracuseStep 3635857 = 2726893) B2726893
theorem B4847809 : Blo 1913435 4847809 := bstep (se 2 (by rfl) ⟨1817928, by rfl⟩ : syracuseStep 4847809 = 3635857) B3635857
theorem B6463745 : Blo 1913435 6463745 := bstep (se 2 (by rfl) ⟨2423904, by rfl⟩ : syracuseStep 6463745 = 4847809) B4847809
theorem B4309163 : Blo 1913435 4309163 := bstep (se 1 (by rfl) ⟨3231872, by rfl⟩ : syracuseStep 4309163 = 6463745) B6463745
theorem B2872775 : Blo 1913435 2872775 := bstep (se 1 (by rfl) ⟨2154581, by rfl⟩ : syracuseStep 2872775 = 4309163) B4309163
theorem B1915183 : Blo 1913435 1915183 := bstep (se 1 (by rfl) ⟨1436387, by rfl⟩ : syracuseStep 1915183 = 2872775) B2872775
theorem B2872781 : Blo 1913435 2872781 := bbase (se 3 (by rfl) ⟨538646, by rfl⟩ : syracuseStep 2872781 = 1077293) (by norm_num)
theorem B1915187 : Blo 1913435 1915187 := bstep (se 1 (by rfl) ⟨1436390, by rfl⟩ : syracuseStep 1915187 = 2872781) B2872781
theorem B4309181 : Blo 1913435 4309181 := bbase (se 3 (by rfl) ⟨807971, by rfl⟩ : syracuseStep 4309181 = 1615943) (by norm_num)
theorem B2872787 : Blo 1913435 2872787 := bstep (se 1 (by rfl) ⟨2154590, by rfl⟩ : syracuseStep 2872787 = 4309181) B4309181
theorem B1915191 : Blo 1913435 1915191 := bstep (se 1 (by rfl) ⟨1436393, by rfl⟩ : syracuseStep 1915191 = 2872787) B2872787
theorem B3231893 : Blo 1913435 3231893 := bbase (se 6 (by rfl) ⟨75747, by rfl⟩ : syracuseStep 3231893 = 151495) (by norm_num)
theorem B2154595 : Blo 1913435 2154595 := bstep (se 1 (by rfl) ⟨1615946, by rfl⟩ : syracuseStep 2154595 = 3231893) B3231893
theorem B2872793 : Blo 1913435 2872793 := bstep (se 2 (by rfl) ⟨1077297, by rfl⟩ : syracuseStep 2872793 = 2154595) B2154595
theorem B1915195 : Blo 1913435 1915195 := bstep (se 1 (by rfl) ⟨1436396, by rfl⟩ : syracuseStep 1915195 = 2872793) B2872793
theorem B3451253 : Blo 1913435 3451253 := bbase (se 5 (by rfl) ⟨161777, by rfl⟩ : syracuseStep 3451253 = 323555) (by norm_num)
theorem B9203341 : Blo 1913435 9203341 := bstep (se 3 (by rfl) ⟨1725626, by rfl⟩ : syracuseStep 9203341 = 3451253) B3451253
theorem B12271121 : Blo 1913435 12271121 := bstep (se 2 (by rfl) ⟨4601670, by rfl⟩ : syracuseStep 12271121 = 9203341) B9203341
theorem B8180747 : Blo 1913435 8180747 := bstep (se 1 (by rfl) ⟨6135560, by rfl⟩ : syracuseStep 8180747 = 12271121) B12271121
theorem B5453831 : Blo 1913435 5453831 := bstep (se 1 (by rfl) ⟨4090373, by rfl⟩ : syracuseStep 5453831 = 8180747) B8180747
theorem B14543549 : Blo 1913435 14543549 := bstep (se 3 (by rfl) ⟨2726915, by rfl⟩ : syracuseStep 14543549 = 5453831) B5453831
theorem B9695699 : Blo 1913435 9695699 := bstep (se 1 (by rfl) ⟨7271774, by rfl⟩ : syracuseStep 9695699 = 14543549) B14543549
theorem B6463799 : Blo 1913435 6463799 := bstep (se 1 (by rfl) ⟨4847849, by rfl⟩ : syracuseStep 6463799 = 9695699) B9695699
theorem B4309199 : Blo 1913435 4309199 := bstep (se 1 (by rfl) ⟨3231899, by rfl⟩ : syracuseStep 4309199 = 6463799) B6463799
theorem B2872799 : Blo 1913435 2872799 := bstep (se 1 (by rfl) ⟨2154599, by rfl⟩ : syracuseStep 2872799 = 4309199) B4309199
theorem B1915199 : Blo 1913435 1915199 := bstep (se 1 (by rfl) ⟨1436399, by rfl⟩ : syracuseStep 1915199 = 2872799) B2872799
theorem B2872805 : Blo 1913435 2872805 := bbase (se 4 (by rfl) ⟨269325, by rfl⟩ : syracuseStep 2872805 = 538651) (by norm_num)
theorem B1915203 : Blo 1913435 1915203 := bstep (se 1 (by rfl) ⟨1436402, by rfl⟩ : syracuseStep 1915203 = 2872805) B2872805
theorem B19656053 : Blo 1913435 19656053 := bbase (se 5 (by rfl) ⟨921377, by rfl⟩ : syracuseStep 19656053 = 1842755) (by norm_num)
theorem B13104035 : Blo 1913435 13104035 := bstep (se 1 (by rfl) ⟨9828026, by rfl⟩ : syracuseStep 13104035 = 19656053) B19656053
theorem B8736023 : Blo 1913435 8736023 := bstep (se 1 (by rfl) ⟨6552017, by rfl⟩ : syracuseStep 8736023 = 13104035) B13104035
theorem B23296061 : Blo 1913435 23296061 := bstep (se 3 (by rfl) ⟨4368011, by rfl⟩ : syracuseStep 23296061 = 8736023) B8736023
theorem B15530707 : Blo 1913435 15530707 := bstep (se 1 (by rfl) ⟨11648030, by rfl⟩ : syracuseStep 15530707 = 23296061) B23296061
theorem B20707609 : Blo 1913435 20707609 := bstep (se 2 (by rfl) ⟨7765353, by rfl⟩ : syracuseStep 20707609 = 15530707) B15530707
theorem B27610145 : Blo 1913435 27610145 := bstep (se 2 (by rfl) ⟨10353804, by rfl⟩ : syracuseStep 27610145 = 20707609) B20707609
theorem B18406763 : Blo 1913435 18406763 := bstep (se 1 (by rfl) ⟨13805072, by rfl⟩ : syracuseStep 18406763 = 27610145) B27610145
theorem B12271175 : Blo 1913435 12271175 := bstep (se 1 (by rfl) ⟨9203381, by rfl⟩ : syracuseStep 12271175 = 18406763) B18406763
theorem B8180783 : Blo 1913435 8180783 := bstep (se 1 (by rfl) ⟨6135587, by rfl⟩ : syracuseStep 8180783 = 12271175) B12271175
theorem B5453855 : Blo 1913435 5453855 := bstep (se 1 (by rfl) ⟨4090391, by rfl⟩ : syracuseStep 5453855 = 8180783) B8180783
theorem B3635903 : Blo 1913435 3635903 := bstep (se 1 (by rfl) ⟨2726927, by rfl⟩ : syracuseStep 3635903 = 5453855) B5453855
theorem B2423935 : Blo 1913435 2423935 := bstep (se 1 (by rfl) ⟨1817951, by rfl⟩ : syracuseStep 2423935 = 3635903) B3635903
theorem B3231913 : Blo 1913435 3231913 := bstep (se 2 (by rfl) ⟨1211967, by rfl⟩ : syracuseStep 3231913 = 2423935) B2423935
theorem B4309217 : Blo 1913435 4309217 := bstep (se 2 (by rfl) ⟨1615956, by rfl⟩ : syracuseStep 4309217 = 3231913) B3231913
theorem B2872811 : Blo 1913435 2872811 := bstep (se 1 (by rfl) ⟨2154608, by rfl⟩ : syracuseStep 2872811 = 4309217) B4309217
theorem B1915207 : Blo 1913435 1915207 := bstep (se 1 (by rfl) ⟨1436405, by rfl⟩ : syracuseStep 1915207 = 2872811) B2872811
theorem B2154613 : Blo 1913435 2154613 := bbase (se 5 (by rfl) ⟨100997, by rfl⟩ : syracuseStep 2154613 = 201995) (by norm_num)
theorem B2872817 : Blo 1913435 2872817 := bstep (se 2 (by rfl) ⟨1077306, by rfl⟩ : syracuseStep 2872817 = 2154613) B2154613
theorem B1915211 : Blo 1913435 1915211 := bstep (se 1 (by rfl) ⟨1436408, by rfl⟩ : syracuseStep 1915211 = 2872817) B2872817
theorem B2423945 : Blo 1913435 2423945 := bbase (se 2 (by rfl) ⟨908979, by rfl⟩ : syracuseStep 2423945 = 1817959) (by norm_num)
theorem B6463853 : Blo 1913435 6463853 := bstep (se 3 (by rfl) ⟨1211972, by rfl⟩ : syracuseStep 6463853 = 2423945) B2423945
theorem B4309235 : Blo 1913435 4309235 := bstep (se 1 (by rfl) ⟨3231926, by rfl⟩ : syracuseStep 4309235 = 6463853) B6463853
theorem B2872823 : Blo 1913435 2872823 := bstep (se 1 (by rfl) ⟨2154617, by rfl⟩ : syracuseStep 2872823 = 4309235) B4309235
theorem B1915215 : Blo 1913435 1915215 := bstep (se 1 (by rfl) ⟨1436411, by rfl⟩ : syracuseStep 1915215 = 2872823) B2872823
theorem B2872829 : Blo 1913435 2872829 := bbase (se 3 (by rfl) ⟨538655, by rfl⟩ : syracuseStep 2872829 = 1077311) (by norm_num)
theorem B1915219 : Blo 1913435 1915219 := bstep (se 1 (by rfl) ⟨1436414, by rfl⟩ : syracuseStep 1915219 = 2872829) B2872829
theorem B4309253 : Blo 1913435 4309253 := bbase (se 4 (by rfl) ⟨403992, by rfl⟩ : syracuseStep 4309253 = 807985) (by norm_num)
theorem B2872835 : Blo 1913435 2872835 := bstep (se 1 (by rfl) ⟨2154626, by rfl⟩ : syracuseStep 2872835 = 4309253) B4309253
theorem B1915223 : Blo 1913435 1915223 := bstep (se 1 (by rfl) ⟨1436417, by rfl⟩ : syracuseStep 1915223 = 2872835) B2872835
theorem B3635941 : Blo 1913435 3635941 := bbase (se 4 (by rfl) ⟨340869, by rfl⟩ : syracuseStep 3635941 = 681739) (by norm_num)
theorem B4847921 : Blo 1913435 4847921 := bstep (se 2 (by rfl) ⟨1817970, by rfl⟩ : syracuseStep 4847921 = 3635941) B3635941
theorem B3231947 : Blo 1913435 3231947 := bstep (se 1 (by rfl) ⟨2423960, by rfl⟩ : syracuseStep 3231947 = 4847921) B4847921
theorem B2154631 : Blo 1913435 2154631 := bstep (se 1 (by rfl) ⟨1615973, by rfl⟩ : syracuseStep 2154631 = 3231947) B3231947
theorem B2872841 : Blo 1913435 2872841 := bstep (se 2 (by rfl) ⟨1077315, by rfl⟩ : syracuseStep 2872841 = 2154631) B2154631
theorem B1915227 : Blo 1913435 1915227 := bstep (se 1 (by rfl) ⟨1436420, by rfl⟩ : syracuseStep 1915227 = 2872841) B2872841
theorem B9695861 : Blo 1913435 9695861 := bbase (se 5 (by rfl) ⟨454493, by rfl⟩ : syracuseStep 9695861 = 908987) (by norm_num)
theorem B6463907 : Blo 1913435 6463907 := bstep (se 1 (by rfl) ⟨4847930, by rfl⟩ : syracuseStep 6463907 = 9695861) B9695861
theorem B4309271 : Blo 1913435 4309271 := bstep (se 1 (by rfl) ⟨3231953, by rfl⟩ : syracuseStep 4309271 = 6463907) B6463907
theorem B2872847 : Blo 1913435 2872847 := bstep (se 1 (by rfl) ⟨2154635, by rfl⟩ : syracuseStep 2872847 = 4309271) B4309271
theorem B1915231 : Blo 1913435 1915231 := bstep (se 1 (by rfl) ⟨1436423, by rfl⟩ : syracuseStep 1915231 = 2872847) B2872847
theorem B2872853 : Blo 1913435 2872853 := bbase (se 6 (by rfl) ⟨67332, by rfl⟩ : syracuseStep 2872853 = 134665) (by norm_num)
theorem B1915235 : Blo 1913435 1915235 := bstep (se 1 (by rfl) ⟨1436426, by rfl⟩ : syracuseStep 1915235 = 2872853) B2872853
theorem B49755221 : Blo 1913435 49755221 := bbase (se 8 (by rfl) ⟨291534, by rfl⟩ : syracuseStep 49755221 = 583069) (by norm_num)
theorem B33170147 : Blo 1913435 33170147 := bstep (se 1 (by rfl) ⟨24877610, by rfl⟩ : syracuseStep 33170147 = 49755221) B49755221
theorem B22113431 : Blo 1913435 22113431 := bstep (se 1 (by rfl) ⟨16585073, by rfl⟩ : syracuseStep 22113431 = 33170147) B33170147
theorem B14742287 : Blo 1913435 14742287 := bstep (se 1 (by rfl) ⟨11056715, by rfl⟩ : syracuseStep 14742287 = 22113431) B22113431
theorem B9828191 : Blo 1913435 9828191 := bstep (se 1 (by rfl) ⟨7371143, by rfl⟩ : syracuseStep 9828191 = 14742287) B14742287
theorem B6552127 : Blo 1913435 6552127 := bstep (se 1 (by rfl) ⟨4914095, by rfl⟩ : syracuseStep 6552127 = 9828191) B9828191
theorem B8736169 : Blo 1913435 8736169 := bstep (se 2 (by rfl) ⟨3276063, by rfl⟩ : syracuseStep 8736169 = 6552127) B6552127
theorem B11648225 : Blo 1913435 11648225 := bstep (se 2 (by rfl) ⟨4368084, by rfl⟩ : syracuseStep 11648225 = 8736169) B8736169
theorem B7765483 : Blo 1913435 7765483 := bstep (se 1 (by rfl) ⟨5824112, by rfl⟩ : syracuseStep 7765483 = 11648225) B11648225
theorem B10353977 : Blo 1913435 10353977 := bstep (se 2 (by rfl) ⟨3882741, by rfl⟩ : syracuseStep 10353977 = 7765483) B7765483
theorem B6902651 : Blo 1913435 6902651 := bstep (se 1 (by rfl) ⟨5176988, by rfl⟩ : syracuseStep 6902651 = 10353977) B10353977
theorem B4601767 : Blo 1913435 4601767 := bstep (se 1 (by rfl) ⟨3451325, by rfl⟩ : syracuseStep 4601767 = 6902651) B6902651
theorem B6135689 : Blo 1913435 6135689 := bstep (se 2 (by rfl) ⟨2300883, by rfl⟩ : syracuseStep 6135689 = 4601767) B4601767
theorem B16361837 : Blo 1913435 16361837 := bstep (se 3 (by rfl) ⟨3067844, by rfl⟩ : syracuseStep 16361837 = 6135689) B6135689
theorem B10907891 : Blo 1913435 10907891 := bstep (se 1 (by rfl) ⟨8180918, by rfl⟩ : syracuseStep 10907891 = 16361837) B16361837
theorem B7271927 : Blo 1913435 7271927 := bstep (se 1 (by rfl) ⟨5453945, by rfl⟩ : syracuseStep 7271927 = 10907891) B10907891
theorem B4847951 : Blo 1913435 4847951 := bstep (se 1 (by rfl) ⟨3635963, by rfl⟩ : syracuseStep 4847951 = 7271927) B7271927
theorem B3231967 : Blo 1913435 3231967 := bstep (se 1 (by rfl) ⟨2423975, by rfl⟩ : syracuseStep 3231967 = 4847951) B4847951
theorem B4309289 : Blo 1913435 4309289 := bstep (se 2 (by rfl) ⟨1615983, by rfl⟩ : syracuseStep 4309289 = 3231967) B3231967
theorem B2872859 : Blo 1913435 2872859 := bstep (se 1 (by rfl) ⟨2154644, by rfl⟩ : syracuseStep 2872859 = 4309289) B4309289
theorem B1915239 : Blo 1913435 1915239 := bstep (se 1 (by rfl) ⟨1436429, by rfl⟩ : syracuseStep 1915239 = 2872859) B2872859
theorem B2154649 : Blo 1913435 2154649 := bbase (se 2 (by rfl) ⟨807993, by rfl⟩ : syracuseStep 2154649 = 1615987) (by norm_num)
theorem B2872865 : Blo 1913435 2872865 := bstep (se 2 (by rfl) ⟨1077324, by rfl⟩ : syracuseStep 2872865 = 2154649) B2154649
theorem B1915243 : Blo 1913435 1915243 := bstep (se 1 (by rfl) ⟨1436432, by rfl⟩ : syracuseStep 1915243 = 2872865) B2872865
theorem B7271957 : Blo 1913435 7271957 := bbase (se 6 (by rfl) ⟨170436, by rfl⟩ : syracuseStep 7271957 = 340873) (by norm_num)
theorem B4847971 : Blo 1913435 4847971 := bstep (se 1 (by rfl) ⟨3635978, by rfl⟩ : syracuseStep 4847971 = 7271957) B7271957
theorem B6463961 : Blo 1913435 6463961 := bstep (se 2 (by rfl) ⟨2423985, by rfl⟩ : syracuseStep 6463961 = 4847971) B4847971
theorem B4309307 : Blo 1913435 4309307 := bstep (se 1 (by rfl) ⟨3231980, by rfl⟩ : syracuseStep 4309307 = 6463961) B6463961
theorem B2872871 : Blo 1913435 2872871 := bstep (se 1 (by rfl) ⟨2154653, by rfl⟩ : syracuseStep 2872871 = 4309307) B4309307
theorem B1915247 : Blo 1913435 1915247 := bstep (se 1 (by rfl) ⟨1436435, by rfl⟩ : syracuseStep 1915247 = 2872871) B2872871
theorem B2872877 : Blo 1913435 2872877 := bbase (se 3 (by rfl) ⟨538664, by rfl⟩ : syracuseStep 2872877 = 1077329) (by norm_num)
theorem B1915251 : Blo 1913435 1915251 := bstep (se 1 (by rfl) ⟨1436438, by rfl⟩ : syracuseStep 1915251 = 2872877) B2872877
theorem B4309325 : Blo 1913435 4309325 := bbase (se 3 (by rfl) ⟨807998, by rfl⟩ : syracuseStep 4309325 = 1615997) (by norm_num)
theorem B2872883 : Blo 1913435 2872883 := bstep (se 1 (by rfl) ⟨2154662, by rfl⟩ : syracuseStep 2872883 = 4309325) B4309325
theorem B1915255 : Blo 1913435 1915255 := bstep (se 1 (by rfl) ⟨1436441, by rfl⟩ : syracuseStep 1915255 = 2872883) B2872883
theorem B2424001 : Blo 1913435 2424001 := bbase (se 2 (by rfl) ⟨909000, by rfl⟩ : syracuseStep 2424001 = 1818001) (by norm_num)
theorem B3232001 : Blo 1913435 3232001 := bstep (se 2 (by rfl) ⟨1212000, by rfl⟩ : syracuseStep 3232001 = 2424001) B2424001
theorem B2154667 : Blo 1913435 2154667 := bstep (se 1 (by rfl) ⟨1616000, by rfl⟩ : syracuseStep 2154667 = 3232001) B3232001
theorem B2872889 : Blo 1913435 2872889 := bstep (se 2 (by rfl) ⟨1077333, by rfl⟩ : syracuseStep 2872889 = 2154667) B2154667
theorem B1915259 : Blo 1913435 1915259 := bstep (se 1 (by rfl) ⟨1436444, by rfl⟩ : syracuseStep 1915259 = 2872889) B2872889
theorem B2073161 : Blo 1913435 2073161 := bbase (se 2 (by rfl) ⟨777435, by rfl⟩ : syracuseStep 2073161 = 1554871) (by norm_num)
theorem B5528429 : Blo 1913435 5528429 := bstep (se 3 (by rfl) ⟨1036580, by rfl⟩ : syracuseStep 5528429 = 2073161) B2073161
theorem B3685619 : Blo 1913435 3685619 := bstep (se 1 (by rfl) ⟨2764214, by rfl⟩ : syracuseStep 3685619 = 5528429) B5528429
theorem B9828317 : Blo 1913435 9828317 := bstep (se 3 (by rfl) ⟨1842809, by rfl⟩ : syracuseStep 9828317 = 3685619) B3685619
theorem B6552211 : Blo 1913435 6552211 := bstep (se 1 (by rfl) ⟨4914158, by rfl⟩ : syracuseStep 6552211 = 9828317) B9828317
theorem B8736281 : Blo 1913435 8736281 := bstep (se 2 (by rfl) ⟨3276105, by rfl⟩ : syracuseStep 8736281 = 6552211) B6552211
theorem B5824187 : Blo 1913435 5824187 := bstep (se 1 (by rfl) ⟨4368140, by rfl⟩ : syracuseStep 5824187 = 8736281) B8736281
theorem B3882791 : Blo 1913435 3882791 := bstep (se 1 (by rfl) ⟨2912093, by rfl⟩ : syracuseStep 3882791 = 5824187) B5824187
theorem B2588527 : Blo 1913435 2588527 := bstep (se 1 (by rfl) ⟨1941395, by rfl⟩ : syracuseStep 2588527 = 3882791) B3882791
theorem B3451369 : Blo 1913435 3451369 := bstep (se 2 (by rfl) ⟨1294263, by rfl⟩ : syracuseStep 3451369 = 2588527) B2588527
theorem B4601825 : Blo 1913435 4601825 := bstep (se 2 (by rfl) ⟨1725684, by rfl⟩ : syracuseStep 4601825 = 3451369) B3451369
theorem B3067883 : Blo 1913435 3067883 := bstep (se 1 (by rfl) ⟨2300912, by rfl⟩ : syracuseStep 3067883 = 4601825) B4601825
theorem B2045255 : Blo 1913435 2045255 := bstep (se 1 (by rfl) ⟨1533941, by rfl⟩ : syracuseStep 2045255 = 3067883) B3067883
theorem B21816053 : Blo 1913435 21816053 := bstep (se 5 (by rfl) ⟨1022627, by rfl⟩ : syracuseStep 21816053 = 2045255) B2045255
theorem B14544035 : Blo 1913435 14544035 := bstep (se 1 (by rfl) ⟨10908026, by rfl⟩ : syracuseStep 14544035 = 21816053) B21816053
theorem B9696023 : Blo 1913435 9696023 := bstep (se 1 (by rfl) ⟨7272017, by rfl⟩ : syracuseStep 9696023 = 14544035) B14544035
theorem B6464015 : Blo 1913435 6464015 := bstep (se 1 (by rfl) ⟨4848011, by rfl⟩ : syracuseStep 6464015 = 9696023) B9696023
theorem B4309343 : Blo 1913435 4309343 := bstep (se 1 (by rfl) ⟨3232007, by rfl⟩ : syracuseStep 4309343 = 6464015) B6464015
theorem B2872895 : Blo 1913435 2872895 := bstep (se 1 (by rfl) ⟨2154671, by rfl⟩ : syracuseStep 2872895 = 4309343) B4309343
theorem B1915263 : Blo 1913435 1915263 := bstep (se 1 (by rfl) ⟨1436447, by rfl⟩ : syracuseStep 1915263 = 2872895) B2872895
theorem B2872901 : Blo 1913435 2872901 := bbase (se 4 (by rfl) ⟨269334, by rfl⟩ : syracuseStep 2872901 = 538669) (by norm_num)
theorem B1915267 : Blo 1913435 1915267 := bstep (se 1 (by rfl) ⟨1436450, by rfl⟩ : syracuseStep 1915267 = 2872901) B2872901
theorem B3232021 : Blo 1913435 3232021 := bbase (se 6 (by rfl) ⟨75750, by rfl⟩ : syracuseStep 3232021 = 151501) (by norm_num)
theorem B4309361 : Blo 1913435 4309361 := bstep (se 2 (by rfl) ⟨1616010, by rfl⟩ : syracuseStep 4309361 = 3232021) B3232021
theorem B2872907 : Blo 1913435 2872907 := bstep (se 1 (by rfl) ⟨2154680, by rfl⟩ : syracuseStep 2872907 = 4309361) B4309361
theorem B1915271 : Blo 1913435 1915271 := bstep (se 1 (by rfl) ⟨1436453, by rfl⟩ : syracuseStep 1915271 = 2872907) B2872907
theorem B2154685 : Blo 1913435 2154685 := bbase (se 3 (by rfl) ⟨404003, by rfl⟩ : syracuseStep 2154685 = 808007) (by norm_num)
theorem B2872913 : Blo 1913435 2872913 := bstep (se 2 (by rfl) ⟨1077342, by rfl⟩ : syracuseStep 2872913 = 2154685) B2154685
theorem B1915275 : Blo 1913435 1915275 := bstep (se 1 (by rfl) ⟨1436456, by rfl⟩ : syracuseStep 1915275 = 2872913) B2872913
theorem B6464069 : Blo 1913435 6464069 := bbase (se 4 (by rfl) ⟨606006, by rfl⟩ : syracuseStep 6464069 = 1212013) (by norm_num)
theorem B4309379 : Blo 1913435 4309379 := bstep (se 1 (by rfl) ⟨3232034, by rfl⟩ : syracuseStep 4309379 = 6464069) B6464069
theorem B2872919 : Blo 1913435 2872919 := bstep (se 1 (by rfl) ⟨2154689, by rfl⟩ : syracuseStep 2872919 = 4309379) B4309379
theorem B1915279 : Blo 1913435 1915279 := bstep (se 1 (by rfl) ⟨1436459, by rfl⟩ : syracuseStep 1915279 = 2872919) B2872919
theorem B2872925 : Blo 1913435 2872925 := bbase (se 3 (by rfl) ⟨538673, by rfl⟩ : syracuseStep 2872925 = 1077347) (by norm_num)
theorem B1915283 : Blo 1913435 1915283 := bstep (se 1 (by rfl) ⟨1436462, by rfl⟩ : syracuseStep 1915283 = 2872925) B2872925
theorem B4309397 : Blo 1913435 4309397 := bbase (se 6 (by rfl) ⟨101001, by rfl⟩ : syracuseStep 4309397 = 202003) (by norm_num)
theorem B2872931 : Blo 1913435 2872931 := bstep (se 1 (by rfl) ⟨2154698, by rfl⟩ : syracuseStep 2872931 = 4309397) B4309397
theorem B1915287 : Blo 1913435 1915287 := bstep (se 1 (by rfl) ⟨1436465, by rfl⟩ : syracuseStep 1915287 = 2872931) B2872931
theorem B4601893 : Blo 1913435 4601893 := bbase (se 4 (by rfl) ⟨431427, by rfl⟩ : syracuseStep 4601893 = 862855) (by norm_num)
theorem B6135857 : Blo 1913435 6135857 := bstep (se 2 (by rfl) ⟨2300946, by rfl⟩ : syracuseStep 6135857 = 4601893) B4601893
theorem B4090571 : Blo 1913435 4090571 := bstep (se 1 (by rfl) ⟨3067928, by rfl⟩ : syracuseStep 4090571 = 6135857) B6135857
theorem B2727047 : Blo 1913435 2727047 := bstep (se 1 (by rfl) ⟨2045285, by rfl⟩ : syracuseStep 2727047 = 4090571) B4090571
theorem B7272125 : Blo 1913435 7272125 := bstep (se 3 (by rfl) ⟨1363523, by rfl⟩ : syracuseStep 7272125 = 2727047) B2727047
theorem B4848083 : Blo 1913435 4848083 := bstep (se 1 (by rfl) ⟨3636062, by rfl⟩ : syracuseStep 4848083 = 7272125) B7272125
theorem B3232055 : Blo 1913435 3232055 := bstep (se 1 (by rfl) ⟨2424041, by rfl⟩ : syracuseStep 3232055 = 4848083) B4848083
theorem B2154703 : Blo 1913435 2154703 := bstep (se 1 (by rfl) ⟨1616027, by rfl⟩ : syracuseStep 2154703 = 3232055) B3232055
theorem B2872937 : Blo 1913435 2872937 := bstep (se 2 (by rfl) ⟨1077351, by rfl⟩ : syracuseStep 2872937 = 2154703) B2154703
theorem B1915291 : Blo 1913435 1915291 := bstep (se 1 (by rfl) ⟨1436468, by rfl⟩ : syracuseStep 1915291 = 2872937) B2872937
theorem B8181157 : Blo 1913435 8181157 := bbase (se 4 (by rfl) ⟨766983, by rfl⟩ : syracuseStep 8181157 = 1533967) (by norm_num)
theorem B10908209 : Blo 1913435 10908209 := bstep (se 2 (by rfl) ⟨4090578, by rfl⟩ : syracuseStep 10908209 = 8181157) B8181157
theorem B7272139 : Blo 1913435 7272139 := bstep (se 1 (by rfl) ⟨5454104, by rfl⟩ : syracuseStep 7272139 = 10908209) B10908209
theorem B9696185 : Blo 1913435 9696185 := bstep (se 2 (by rfl) ⟨3636069, by rfl⟩ : syracuseStep 9696185 = 7272139) B7272139
theorem B6464123 : Blo 1913435 6464123 := bstep (se 1 (by rfl) ⟨4848092, by rfl⟩ : syracuseStep 6464123 = 9696185) B9696185
theorem B4309415 : Blo 1913435 4309415 := bstep (se 1 (by rfl) ⟨3232061, by rfl⟩ : syracuseStep 4309415 = 6464123) B6464123
theorem B2872943 : Blo 1913435 2872943 := bstep (se 1 (by rfl) ⟨2154707, by rfl⟩ : syracuseStep 2872943 = 4309415) B4309415
theorem B1915295 : Blo 1913435 1915295 := bstep (se 1 (by rfl) ⟨1436471, by rfl⟩ : syracuseStep 1915295 = 2872943) B2872943
theorem B2872949 : Blo 1913435 2872949 := bbase (se 5 (by rfl) ⟨134669, by rfl⟩ : syracuseStep 2872949 = 269339) (by norm_num)
theorem B1915299 : Blo 1913435 1915299 := bstep (se 1 (by rfl) ⟨1436474, by rfl⟩ : syracuseStep 1915299 = 2872949) B2872949
theorem B3636085 : Blo 1913435 3636085 := bbase (se 5 (by rfl) ⟨170441, by rfl⟩ : syracuseStep 3636085 = 340883) (by norm_num)
theorem B4848113 : Blo 1913435 4848113 := bstep (se 2 (by rfl) ⟨1818042, by rfl⟩ : syracuseStep 4848113 = 3636085) B3636085
theorem B3232075 : Blo 1913435 3232075 := bstep (se 1 (by rfl) ⟨2424056, by rfl⟩ : syracuseStep 3232075 = 4848113) B4848113
theorem B4309433 : Blo 1913435 4309433 := bstep (se 2 (by rfl) ⟨1616037, by rfl⟩ : syracuseStep 4309433 = 3232075) B3232075
theorem B2872955 : Blo 1913435 2872955 := bstep (se 1 (by rfl) ⟨2154716, by rfl⟩ : syracuseStep 2872955 = 4309433) B4309433
theorem B1915303 : Blo 1913435 1915303 := bstep (se 1 (by rfl) ⟨1436477, by rfl⟩ : syracuseStep 1915303 = 2872955) B2872955
theorem B2154721 : Blo 1913435 2154721 := bbase (se 2 (by rfl) ⟨808020, by rfl⟩ : syracuseStep 2154721 = 1616041) (by norm_num)
theorem B2872961 : Blo 1913435 2872961 := bstep (se 2 (by rfl) ⟨1077360, by rfl⟩ : syracuseStep 2872961 = 2154721) B2154721
theorem B1915307 : Blo 1913435 1915307 := bstep (se 1 (by rfl) ⟨1436480, by rfl⟩ : syracuseStep 1915307 = 2872961) B2872961
theorem B4848133 : Blo 1913435 4848133 := bbase (se 4 (by rfl) ⟨454512, by rfl⟩ : syracuseStep 4848133 = 909025) (by norm_num)
theorem B6464177 : Blo 1913435 6464177 := bstep (se 2 (by rfl) ⟨2424066, by rfl⟩ : syracuseStep 6464177 = 4848133) B4848133
theorem B4309451 : Blo 1913435 4309451 := bstep (se 1 (by rfl) ⟨3232088, by rfl⟩ : syracuseStep 4309451 = 6464177) B6464177
theorem B2872967 : Blo 1913435 2872967 := bstep (se 1 (by rfl) ⟨2154725, by rfl⟩ : syracuseStep 2872967 = 4309451) B4309451
theorem B1915311 : Blo 1913435 1915311 := bstep (se 1 (by rfl) ⟨1436483, by rfl⟩ : syracuseStep 1915311 = 2872967) B2872967
theorem B2872973 : Blo 1913435 2872973 := bbase (se 3 (by rfl) ⟨538682, by rfl⟩ : syracuseStep 2872973 = 1077365) (by norm_num)
theorem B1915315 : Blo 1913435 1915315 := bstep (se 1 (by rfl) ⟨1436486, by rfl⟩ : syracuseStep 1915315 = 2872973) B2872973
theorem B4309469 : Blo 1913435 4309469 := bbase (se 3 (by rfl) ⟨808025, by rfl⟩ : syracuseStep 4309469 = 1616051) (by norm_num)
theorem B2872979 : Blo 1913435 2872979 := bstep (se 1 (by rfl) ⟨2154734, by rfl⟩ : syracuseStep 2872979 = 4309469) B4309469
theorem B1915319 : Blo 1913435 1915319 := bstep (se 1 (by rfl) ⟨1436489, by rfl⟩ : syracuseStep 1915319 = 2872979) B2872979
theorem B3232109 : Blo 1913435 3232109 := bbase (se 3 (by rfl) ⟨606020, by rfl⟩ : syracuseStep 3232109 = 1212041) (by norm_num)
theorem B2154739 : Blo 1913435 2154739 := bstep (se 1 (by rfl) ⟨1616054, by rfl⟩ : syracuseStep 2154739 = 3232109) B3232109
theorem B2872985 : Blo 1913435 2872985 := bstep (se 2 (by rfl) ⟨1077369, by rfl⟩ : syracuseStep 2872985 = 2154739) B2154739
theorem B1915323 : Blo 1913435 1915323 := bstep (se 1 (by rfl) ⟨1436492, by rfl⟩ : syracuseStep 1915323 = 2872985) B2872985
theorem B13994293 : Blo 1913435 13994293 := bbase (se 5 (by rfl) ⟨655982, by rfl⟩ : syracuseStep 13994293 = 1311965) (by norm_num)
theorem B18659057 : Blo 1913435 18659057 := bstep (se 2 (by rfl) ⟨6997146, by rfl⟩ : syracuseStep 18659057 = 13994293) B13994293
theorem B49757485 : Blo 1913435 49757485 := bstep (se 3 (by rfl) ⟨9329528, by rfl⟩ : syracuseStep 49757485 = 18659057) B18659057
theorem B66343313 : Blo 1913435 66343313 := bstep (se 2 (by rfl) ⟨24878742, by rfl⟩ : syracuseStep 66343313 = 49757485) B49757485
theorem B44228875 : Blo 1913435 44228875 := bstep (se 1 (by rfl) ⟨33171656, by rfl⟩ : syracuseStep 44228875 = 66343313) B66343313
theorem B58971833 : Blo 1913435 58971833 := bstep (se 2 (by rfl) ⟨22114437, by rfl⟩ : syracuseStep 58971833 = 44228875) B44228875
theorem B39314555 : Blo 1913435 39314555 := bstep (se 1 (by rfl) ⟨29485916, by rfl⟩ : syracuseStep 39314555 = 58971833) B58971833
theorem B26209703 : Blo 1913435 26209703 := bstep (se 1 (by rfl) ⟨19657277, by rfl⟩ : syracuseStep 26209703 = 39314555) B39314555
theorem B69892541 : Blo 1913435 69892541 := bstep (se 3 (by rfl) ⟨13104851, by rfl⟩ : syracuseStep 69892541 = 26209703) B26209703
theorem B46595027 : Blo 1913435 46595027 := bstep (se 1 (by rfl) ⟨34946270, by rfl⟩ : syracuseStep 46595027 = 69892541) B69892541
theorem B31063351 : Blo 1913435 31063351 := bstep (se 1 (by rfl) ⟨23297513, by rfl⟩ : syracuseStep 31063351 = 46595027) B46595027
theorem B41417801 : Blo 1913435 41417801 := bstep (se 2 (by rfl) ⟨15531675, by rfl⟩ : syracuseStep 41417801 = 31063351) B31063351
theorem B27611867 : Blo 1913435 27611867 := bstep (se 1 (by rfl) ⟨20708900, by rfl⟩ : syracuseStep 27611867 = 41417801) B41417801
theorem B18407911 : Blo 1913435 18407911 := bstep (se 1 (by rfl) ⟨13805933, by rfl⟩ : syracuseStep 18407911 = 27611867) B27611867
theorem B24543881 : Blo 1913435 24543881 := bstep (se 2 (by rfl) ⟨9203955, by rfl⟩ : syracuseStep 24543881 = 18407911) B18407911
theorem B16362587 : Blo 1913435 16362587 := bstep (se 1 (by rfl) ⟨12271940, by rfl⟩ : syracuseStep 16362587 = 24543881) B24543881
theorem B10908391 : Blo 1913435 10908391 := bstep (se 1 (by rfl) ⟨8181293, by rfl⟩ : syracuseStep 10908391 = 16362587) B16362587
theorem B14544521 : Blo 1913435 14544521 := bstep (se 2 (by rfl) ⟨5454195, by rfl⟩ : syracuseStep 14544521 = 10908391) B10908391
theorem B9696347 : Blo 1913435 9696347 := bstep (se 1 (by rfl) ⟨7272260, by rfl⟩ : syracuseStep 9696347 = 14544521) B14544521
theorem B6464231 : Blo 1913435 6464231 := bstep (se 1 (by rfl) ⟨4848173, by rfl⟩ : syracuseStep 6464231 = 9696347) B9696347
theorem B4309487 : Blo 1913435 4309487 := bstep (se 1 (by rfl) ⟨3232115, by rfl⟩ : syracuseStep 4309487 = 6464231) B6464231
theorem B2872991 : Blo 1913435 2872991 := bstep (se 1 (by rfl) ⟨2154743, by rfl⟩ : syracuseStep 2872991 = 4309487) B4309487
theorem B1915327 : Blo 1913435 1915327 := bstep (se 1 (by rfl) ⟨1436495, by rfl⟩ : syracuseStep 1915327 = 2872991) B2872991
theorem B2872997 : Blo 1913435 2872997 := bbase (se 4 (by rfl) ⟨269343, by rfl⟩ : syracuseStep 2872997 = 538687) (by norm_num)
theorem B1915331 : Blo 1913435 1915331 := bstep (se 1 (by rfl) ⟨1436498, by rfl⟩ : syracuseStep 1915331 = 2872997) B2872997
theorem B2424097 : Blo 1913435 2424097 := bbase (se 2 (by rfl) ⟨909036, by rfl⟩ : syracuseStep 2424097 = 1818073) (by norm_num)
theorem B3232129 : Blo 1913435 3232129 := bstep (se 2 (by rfl) ⟨1212048, by rfl⟩ : syracuseStep 3232129 = 2424097) B2424097
theorem B4309505 : Blo 1913435 4309505 := bstep (se 2 (by rfl) ⟨1616064, by rfl⟩ : syracuseStep 4309505 = 3232129) B3232129
theorem B2873003 : Blo 1913435 2873003 := bstep (se 1 (by rfl) ⟨2154752, by rfl⟩ : syracuseStep 2873003 = 4309505) B4309505
theorem B1915335 : Blo 1913435 1915335 := bstep (se 1 (by rfl) ⟨1436501, by rfl⟩ : syracuseStep 1915335 = 2873003) B2873003
theorem B2154757 : Blo 1913435 2154757 := bbase (se 4 (by rfl) ⟨202008, by rfl⟩ : syracuseStep 2154757 = 404017) (by norm_num)
theorem B2873009 : Blo 1913435 2873009 := bstep (se 2 (by rfl) ⟨1077378, by rfl⟩ : syracuseStep 2873009 = 2154757) B2154757
theorem B1915339 : Blo 1913435 1915339 := bstep (se 1 (by rfl) ⟨1436504, by rfl⟩ : syracuseStep 1915339 = 2873009) B2873009
theorem B2045341 : Blo 1913435 2045341 := bbase (se 3 (by rfl) ⟨383501, by rfl⟩ : syracuseStep 2045341 = 767003) (by norm_num)
theorem B2727121 : Blo 1913435 2727121 := bstep (se 2 (by rfl) ⟨1022670, by rfl⟩ : syracuseStep 2727121 = 2045341) B2045341
theorem B3636161 : Blo 1913435 3636161 := bstep (se 2 (by rfl) ⟨1363560, by rfl⟩ : syracuseStep 3636161 = 2727121) B2727121
theorem B2424107 : Blo 1913435 2424107 := bstep (se 1 (by rfl) ⟨1818080, by rfl⟩ : syracuseStep 2424107 = 3636161) B3636161
theorem B6464285 : Blo 1913435 6464285 := bstep (se 3 (by rfl) ⟨1212053, by rfl⟩ : syracuseStep 6464285 = 2424107) B2424107
theorem B4309523 : Blo 1913435 4309523 := bstep (se 1 (by rfl) ⟨3232142, by rfl⟩ : syracuseStep 4309523 = 6464285) B6464285
theorem B2873015 : Blo 1913435 2873015 := bstep (se 1 (by rfl) ⟨2154761, by rfl⟩ : syracuseStep 2873015 = 4309523) B4309523
theorem B1915343 : Blo 1913435 1915343 := bstep (se 1 (by rfl) ⟨1436507, by rfl⟩ : syracuseStep 1915343 = 2873015) B2873015
theorem B2873021 : Blo 1913435 2873021 := bbase (se 3 (by rfl) ⟨538691, by rfl⟩ : syracuseStep 2873021 = 1077383) (by norm_num)
theorem B1915347 : Blo 1913435 1915347 := bstep (se 1 (by rfl) ⟨1436510, by rfl⟩ : syracuseStep 1915347 = 2873021) B2873021
theorem B4309541 : Blo 1913435 4309541 := bbase (se 4 (by rfl) ⟨404019, by rfl⟩ : syracuseStep 4309541 = 808039) (by norm_num)
theorem B2873027 : Blo 1913435 2873027 := bstep (se 1 (by rfl) ⟨2154770, by rfl⟩ : syracuseStep 2873027 = 4309541) B4309541
theorem B1915351 : Blo 1913435 1915351 := bstep (se 1 (by rfl) ⟨1436513, by rfl⟩ : syracuseStep 1915351 = 2873027) B2873027
theorem B4848245 : Blo 1913435 4848245 := bbase (se 5 (by rfl) ⟨227261, by rfl⟩ : syracuseStep 4848245 = 454523) (by norm_num)
theorem B3232163 : Blo 1913435 3232163 := bstep (se 1 (by rfl) ⟨2424122, by rfl⟩ : syracuseStep 3232163 = 4848245) B4848245
theorem B2154775 : Blo 1913435 2154775 := bstep (se 1 (by rfl) ⟨1616081, by rfl⟩ : syracuseStep 2154775 = 3232163) B3232163
theorem B2873033 : Blo 1913435 2873033 := bstep (se 2 (by rfl) ⟨1077387, by rfl⟩ : syracuseStep 2873033 = 2154775) B2154775
theorem B1915355 : Blo 1913435 1915355 := bstep (se 1 (by rfl) ⟨1436516, by rfl⟩ : syracuseStep 1915355 = 2873033) B2873033
theorem B3276269 : Blo 1913435 3276269 := bbase (se 3 (by rfl) ⟨614300, by rfl⟩ : syracuseStep 3276269 = 1228601) (by norm_num)
theorem B2184179 : Blo 1913435 2184179 := bstep (se 1 (by rfl) ⟨1638134, by rfl⟩ : syracuseStep 2184179 = 3276269) B3276269
theorem B5824477 : Blo 1913435 5824477 := bstep (se 3 (by rfl) ⟨1092089, by rfl⟩ : syracuseStep 5824477 = 2184179) B2184179
theorem B7765969 : Blo 1913435 7765969 := bstep (se 2 (by rfl) ⟨2912238, by rfl⟩ : syracuseStep 7765969 = 5824477) B5824477
theorem B10354625 : Blo 1913435 10354625 := bstep (se 2 (by rfl) ⟨3882984, by rfl⟩ : syracuseStep 10354625 = 7765969) B7765969
theorem B6903083 : Blo 1913435 6903083 := bstep (se 1 (by rfl) ⟨5177312, by rfl⟩ : syracuseStep 6903083 = 10354625) B10354625
theorem B18408221 : Blo 1913435 18408221 := bstep (se 3 (by rfl) ⟨3451541, by rfl⟩ : syracuseStep 18408221 = 6903083) B6903083
theorem B12272147 : Blo 1913435 12272147 := bstep (se 1 (by rfl) ⟨9204110, by rfl⟩ : syracuseStep 12272147 = 18408221) B18408221
theorem B8181431 : Blo 1913435 8181431 := bstep (se 1 (by rfl) ⟨6136073, by rfl⟩ : syracuseStep 8181431 = 12272147) B12272147
theorem B5454287 : Blo 1913435 5454287 := bstep (se 1 (by rfl) ⟨4090715, by rfl⟩ : syracuseStep 5454287 = 8181431) B8181431
theorem B3636191 : Blo 1913435 3636191 := bstep (se 1 (by rfl) ⟨2727143, by rfl⟩ : syracuseStep 3636191 = 5454287) B5454287
theorem B9696509 : Blo 1913435 9696509 := bstep (se 3 (by rfl) ⟨1818095, by rfl⟩ : syracuseStep 9696509 = 3636191) B3636191
theorem B6464339 : Blo 1913435 6464339 := bstep (se 1 (by rfl) ⟨4848254, by rfl⟩ : syracuseStep 6464339 = 9696509) B9696509
theorem B4309559 : Blo 1913435 4309559 := bstep (se 1 (by rfl) ⟨3232169, by rfl⟩ : syracuseStep 4309559 = 6464339) B6464339
theorem B2873039 : Blo 1913435 2873039 := bstep (se 1 (by rfl) ⟨2154779, by rfl⟩ : syracuseStep 2873039 = 4309559) B4309559
theorem B1915359 : Blo 1913435 1915359 := bstep (se 1 (by rfl) ⟨1436519, by rfl⟩ : syracuseStep 1915359 = 2873039) B2873039
theorem B2873045 : Blo 1913435 2873045 := bbase (se 7 (by rfl) ⟨33668, by rfl⟩ : syracuseStep 2873045 = 67337) (by norm_num)
theorem B1915363 : Blo 1913435 1915363 := bstep (se 1 (by rfl) ⟨1436522, by rfl⟩ : syracuseStep 1915363 = 2873045) B2873045
theorem B4090733 : Blo 1913435 4090733 := bbase (se 3 (by rfl) ⟨767012, by rfl⟩ : syracuseStep 4090733 = 1534025) (by norm_num)
theorem B2727155 : Blo 1913435 2727155 := bstep (se 1 (by rfl) ⟨2045366, by rfl⟩ : syracuseStep 2727155 = 4090733) B4090733
theorem B7272413 : Blo 1913435 7272413 := bstep (se 3 (by rfl) ⟨1363577, by rfl⟩ : syracuseStep 7272413 = 2727155) B2727155
theorem B4848275 : Blo 1913435 4848275 := bstep (se 1 (by rfl) ⟨3636206, by rfl⟩ : syracuseStep 4848275 = 7272413) B7272413
theorem B3232183 : Blo 1913435 3232183 := bstep (se 1 (by rfl) ⟨2424137, by rfl⟩ : syracuseStep 3232183 = 4848275) B4848275
theorem B4309577 : Blo 1913435 4309577 := bstep (se 2 (by rfl) ⟨1616091, by rfl⟩ : syracuseStep 4309577 = 3232183) B3232183
theorem B2873051 : Blo 1913435 2873051 := bstep (se 1 (by rfl) ⟨2154788, by rfl⟩ : syracuseStep 2873051 = 4309577) B4309577
theorem B1915367 : Blo 1913435 1915367 := bstep (se 1 (by rfl) ⟨1436525, by rfl⟩ : syracuseStep 1915367 = 2873051) B2873051
theorem B2154793 : Blo 1913435 2154793 := bbase (se 2 (by rfl) ⟨808047, by rfl⟩ : syracuseStep 2154793 = 1616095) (by norm_num)
theorem B2873057 : Blo 1913435 2873057 := bstep (se 2 (by rfl) ⟨1077396, by rfl⟩ : syracuseStep 2873057 = 2154793) B2154793
theorem B1915371 : Blo 1913435 1915371 := bstep (se 1 (by rfl) ⟨1436528, by rfl⟩ : syracuseStep 1915371 = 2873057) B2873057
theorem B2184197 : Blo 1913435 2184197 := bbase (se 4 (by rfl) ⟨204768, by rfl⟩ : syracuseStep 2184197 = 409537) (by norm_num)
theorem B23298101 : Blo 1913435 23298101 := bstep (se 5 (by rfl) ⟨1092098, by rfl⟩ : syracuseStep 23298101 = 2184197) B2184197
theorem B15532067 : Blo 1913435 15532067 := bstep (se 1 (by rfl) ⟨11649050, by rfl⟩ : syracuseStep 15532067 = 23298101) B23298101
theorem B10354711 : Blo 1913435 10354711 := bstep (se 1 (by rfl) ⟨7766033, by rfl⟩ : syracuseStep 10354711 = 15532067) B15532067
theorem B13806281 : Blo 1913435 13806281 := bstep (se 2 (by rfl) ⟨5177355, by rfl⟩ : syracuseStep 13806281 = 10354711) B10354711
theorem B9204187 : Blo 1913435 9204187 := bstep (se 1 (by rfl) ⟨6903140, by rfl⟩ : syracuseStep 9204187 = 13806281) B13806281
theorem B12272249 : Blo 1913435 12272249 := bstep (se 2 (by rfl) ⟨4602093, by rfl⟩ : syracuseStep 12272249 = 9204187) B9204187
theorem B8181499 : Blo 1913435 8181499 := bstep (se 1 (by rfl) ⟨6136124, by rfl⟩ : syracuseStep 8181499 = 12272249) B12272249
theorem B10908665 : Blo 1913435 10908665 := bstep (se 2 (by rfl) ⟨4090749, by rfl⟩ : syracuseStep 10908665 = 8181499) B8181499
theorem B7272443 : Blo 1913435 7272443 := bstep (se 1 (by rfl) ⟨5454332, by rfl⟩ : syracuseStep 7272443 = 10908665) B10908665
theorem B4848295 : Blo 1913435 4848295 := bstep (se 1 (by rfl) ⟨3636221, by rfl⟩ : syracuseStep 4848295 = 7272443) B7272443
theorem B6464393 : Blo 1913435 6464393 := bstep (se 2 (by rfl) ⟨2424147, by rfl⟩ : syracuseStep 6464393 = 4848295) B4848295
theorem B4309595 : Blo 1913435 4309595 := bstep (se 1 (by rfl) ⟨3232196, by rfl⟩ : syracuseStep 4309595 = 6464393) B6464393
theorem B2873063 : Blo 1913435 2873063 := bstep (se 1 (by rfl) ⟨2154797, by rfl⟩ : syracuseStep 2873063 = 4309595) B4309595
theorem B1915375 : Blo 1913435 1915375 := bstep (se 1 (by rfl) ⟨1436531, by rfl⟩ : syracuseStep 1915375 = 2873063) B2873063
theorem B2873069 : Blo 1913435 2873069 := bbase (se 3 (by rfl) ⟨538700, by rfl⟩ : syracuseStep 2873069 = 1077401) (by norm_num)
theorem B1915379 : Blo 1913435 1915379 := bstep (se 1 (by rfl) ⟨1436534, by rfl⟩ : syracuseStep 1915379 = 2873069) B2873069
theorem B4309613 : Blo 1913435 4309613 := bbase (se 3 (by rfl) ⟨808052, by rfl⟩ : syracuseStep 4309613 = 1616105) (by norm_num)
theorem B2873075 : Blo 1913435 2873075 := bstep (se 1 (by rfl) ⟨2154806, by rfl⟩ : syracuseStep 2873075 = 4309613) B4309613
theorem B1915383 : Blo 1913435 1915383 := bstep (se 1 (by rfl) ⟨1436537, by rfl⟩ : syracuseStep 1915383 = 2873075) B2873075
theorem B3636245 : Blo 1913435 3636245 := bbase (se 6 (by rfl) ⟨85224, by rfl⟩ : syracuseStep 3636245 = 170449) (by norm_num)
theorem B2424163 : Blo 1913435 2424163 := bstep (se 1 (by rfl) ⟨1818122, by rfl⟩ : syracuseStep 2424163 = 3636245) B3636245
theorem B3232217 : Blo 1913435 3232217 := bstep (se 2 (by rfl) ⟨1212081, by rfl⟩ : syracuseStep 3232217 = 2424163) B2424163
theorem B2154811 : Blo 1913435 2154811 := bstep (se 1 (by rfl) ⟨1616108, by rfl⟩ : syracuseStep 2154811 = 3232217) B3232217
theorem B2873081 : Blo 1913435 2873081 := bstep (se 2 (by rfl) ⟨1077405, by rfl⟩ : syracuseStep 2873081 = 2154811) B2154811
theorem B1915387 : Blo 1913435 1915387 := bstep (se 1 (by rfl) ⟨1436540, by rfl⟩ : syracuseStep 1915387 = 2873081) B2873081
theorem B2764397 : Blo 1913435 2764397 := bbase (se 3 (by rfl) ⟨518324, by rfl⟩ : syracuseStep 2764397 = 1036649) (by norm_num)
theorem B7371725 : Blo 1913435 7371725 := bstep (se 3 (by rfl) ⟨1382198, by rfl⟩ : syracuseStep 7371725 = 2764397) B2764397
theorem B19657933 : Blo 1913435 19657933 := bstep (se 3 (by rfl) ⟨3685862, by rfl⟩ : syracuseStep 19657933 = 7371725) B7371725
theorem B104842309 : Blo 1913435 104842309 := bstep (se 4 (by rfl) ⟨9828966, by rfl⟩ : syracuseStep 104842309 = 19657933) B19657933
theorem B139789745 : Blo 1913435 139789745 := bstep (se 2 (by rfl) ⟨52421154, by rfl⟩ : syracuseStep 139789745 = 104842309) B104842309
theorem B93193163 : Blo 1913435 93193163 := bstep (se 1 (by rfl) ⟨69894872, by rfl⟩ : syracuseStep 93193163 = 139789745) B139789745
theorem B62128775 : Blo 1913435 62128775 := bstep (se 1 (by rfl) ⟨46596581, by rfl⟩ : syracuseStep 62128775 = 93193163) B93193163
theorem B41419183 : Blo 1913435 41419183 := bstep (se 1 (by rfl) ⟨31064387, by rfl⟩ : syracuseStep 41419183 = 62128775) B62128775
theorem B55225577 : Blo 1913435 55225577 := bstep (se 2 (by rfl) ⟨20709591, by rfl⟩ : syracuseStep 55225577 = 41419183) B41419183
theorem B36817051 : Blo 1913435 36817051 := bstep (se 1 (by rfl) ⟨27612788, by rfl⟩ : syracuseStep 36817051 = 55225577) B55225577
theorem B49089401 : Blo 1913435 49089401 := bstep (se 2 (by rfl) ⟨18408525, by rfl⟩ : syracuseStep 49089401 = 36817051) B36817051
theorem B32726267 : Blo 1913435 32726267 := bstep (se 1 (by rfl) ⟨24544700, by rfl⟩ : syracuseStep 32726267 = 49089401) B49089401
theorem B21817511 : Blo 1913435 21817511 := bstep (se 1 (by rfl) ⟨16363133, by rfl⟩ : syracuseStep 21817511 = 32726267) B32726267
theorem B14545007 : Blo 1913435 14545007 := bstep (se 1 (by rfl) ⟨10908755, by rfl⟩ : syracuseStep 14545007 = 21817511) B21817511
theorem B9696671 : Blo 1913435 9696671 := bstep (se 1 (by rfl) ⟨7272503, by rfl⟩ : syracuseStep 9696671 = 14545007) B14545007
theorem B6464447 : Blo 1913435 6464447 := bstep (se 1 (by rfl) ⟨4848335, by rfl⟩ : syracuseStep 6464447 = 9696671) B9696671
theorem B4309631 : Blo 1913435 4309631 := bstep (se 1 (by rfl) ⟨3232223, by rfl⟩ : syracuseStep 4309631 = 6464447) B6464447
theorem B2873087 : Blo 1913435 2873087 := bstep (se 1 (by rfl) ⟨2154815, by rfl⟩ : syracuseStep 2873087 = 4309631) B4309631
theorem B1915391 : Blo 1913435 1915391 := bstep (se 1 (by rfl) ⟨1436543, by rfl⟩ : syracuseStep 1915391 = 2873087) B2873087
theorem B2873093 : Blo 1913435 2873093 := bbase (se 4 (by rfl) ⟨269352, by rfl⟩ : syracuseStep 2873093 = 538705) (by norm_num)
theorem B1915395 : Blo 1913435 1915395 := bstep (se 1 (by rfl) ⟨1436546, by rfl⟩ : syracuseStep 1915395 = 2873093) B2873093
theorem B3232237 : Blo 1913435 3232237 := bbase (se 3 (by rfl) ⟨606044, by rfl⟩ : syracuseStep 3232237 = 1212089) (by norm_num)
theorem B4309649 : Blo 1913435 4309649 := bstep (se 2 (by rfl) ⟨1616118, by rfl⟩ : syracuseStep 4309649 = 3232237) B3232237
theorem B2873099 : Blo 1913435 2873099 := bstep (se 1 (by rfl) ⟨2154824, by rfl⟩ : syracuseStep 2873099 = 4309649) B4309649
theorem B1915399 : Blo 1913435 1915399 := bstep (se 1 (by rfl) ⟨1436549, by rfl⟩ : syracuseStep 1915399 = 2873099) B2873099
theorem B2154829 : Blo 1913435 2154829 := bbase (se 3 (by rfl) ⟨404030, by rfl⟩ : syracuseStep 2154829 = 808061) (by norm_num)
theorem B2873105 : Blo 1913435 2873105 := bstep (se 2 (by rfl) ⟨1077414, by rfl⟩ : syracuseStep 2873105 = 2154829) B2154829
theorem B1915403 : Blo 1913435 1915403 := bstep (se 1 (by rfl) ⟨1436552, by rfl⟩ : syracuseStep 1915403 = 2873105) B2873105
theorem B6464501 : Blo 1913435 6464501 := bbase (se 5 (by rfl) ⟨303023, by rfl⟩ : syracuseStep 6464501 = 606047) (by norm_num)
theorem B4309667 : Blo 1913435 4309667 := bstep (se 1 (by rfl) ⟨3232250, by rfl⟩ : syracuseStep 4309667 = 6464501) B6464501
theorem B2873111 : Blo 1913435 2873111 := bstep (se 1 (by rfl) ⟨2154833, by rfl⟩ : syracuseStep 2873111 = 4309667) B4309667
theorem B1915407 : Blo 1913435 1915407 := bstep (se 1 (by rfl) ⟨1436555, by rfl⟩ : syracuseStep 1915407 = 2873111) B2873111
theorem B2873117 : Blo 1913435 2873117 := bbase (se 3 (by rfl) ⟨538709, by rfl⟩ : syracuseStep 2873117 = 1077419) (by norm_num)
theorem B1915411 : Blo 1913435 1915411 := bstep (se 1 (by rfl) ⟨1436558, by rfl⟩ : syracuseStep 1915411 = 2873117) B2873117
theorem B4309685 : Blo 1913435 4309685 := bbase (se 5 (by rfl) ⟨202016, by rfl⟩ : syracuseStep 4309685 = 404033) (by norm_num)
theorem B2873123 : Blo 1913435 2873123 := bstep (se 1 (by rfl) ⟨2154842, by rfl⟩ : syracuseStep 2873123 = 4309685) B4309685
theorem B1915415 : Blo 1913435 1915415 := bstep (se 1 (by rfl) ⟨1436561, by rfl⟩ : syracuseStep 1915415 = 2873123) B2873123
theorem B10908917 : Blo 1913435 10908917 := bbase (se 5 (by rfl) ⟨511355, by rfl⟩ : syracuseStep 10908917 = 1022711) (by norm_num)
theorem B7272611 : Blo 1913435 7272611 := bstep (se 1 (by rfl) ⟨5454458, by rfl⟩ : syracuseStep 7272611 = 10908917) B10908917
theorem B4848407 : Blo 1913435 4848407 := bstep (se 1 (by rfl) ⟨3636305, by rfl⟩ : syracuseStep 4848407 = 7272611) B7272611
theorem B3232271 : Blo 1913435 3232271 := bstep (se 1 (by rfl) ⟨2424203, by rfl⟩ : syracuseStep 3232271 = 4848407) B4848407
theorem B2154847 : Blo 1913435 2154847 := bstep (se 1 (by rfl) ⟨1616135, by rfl⟩ : syracuseStep 2154847 = 3232271) B3232271
theorem B2873129 : Blo 1913435 2873129 := bstep (se 2 (by rfl) ⟨1077423, by rfl⟩ : syracuseStep 2873129 = 2154847) B2154847
theorem B1915419 : Blo 1913435 1915419 := bstep (se 1 (by rfl) ⟨1436564, by rfl⟩ : syracuseStep 1915419 = 2873129) B2873129
theorem B5454469 : Blo 1913435 5454469 := bbase (se 4 (by rfl) ⟨511356, by rfl⟩ : syracuseStep 5454469 = 1022713) (by norm_num)
theorem B7272625 : Blo 1913435 7272625 := bstep (se 2 (by rfl) ⟨2727234, by rfl⟩ : syracuseStep 7272625 = 5454469) B5454469
theorem B9696833 : Blo 1913435 9696833 := bstep (se 2 (by rfl) ⟨3636312, by rfl⟩ : syracuseStep 9696833 = 7272625) B7272625
theorem B6464555 : Blo 1913435 6464555 := bstep (se 1 (by rfl) ⟨4848416, by rfl⟩ : syracuseStep 6464555 = 9696833) B9696833
theorem B4309703 : Blo 1913435 4309703 := bstep (se 1 (by rfl) ⟨3232277, by rfl⟩ : syracuseStep 4309703 = 6464555) B6464555
theorem B2873135 : Blo 1913435 2873135 := bstep (se 1 (by rfl) ⟨2154851, by rfl⟩ : syracuseStep 2873135 = 4309703) B4309703
theorem B1915423 : Blo 1913435 1915423 := bstep (se 1 (by rfl) ⟨1436567, by rfl⟩ : syracuseStep 1915423 = 2873135) B2873135
theorem B2873141 : Blo 1913435 2873141 := bbase (se 5 (by rfl) ⟨134678, by rfl⟩ : syracuseStep 2873141 = 269357) (by norm_num)
theorem B1915427 : Blo 1913435 1915427 := bstep (se 1 (by rfl) ⟨1436570, by rfl⟩ : syracuseStep 1915427 = 2873141) B2873141
theorem B4848437 : Blo 1913435 4848437 := bbase (se 5 (by rfl) ⟨227270, by rfl⟩ : syracuseStep 4848437 = 454541) (by norm_num)
theorem B3232291 : Blo 1913435 3232291 := bstep (se 1 (by rfl) ⟨2424218, by rfl⟩ : syracuseStep 3232291 = 4848437) B4848437
theorem B4309721 : Blo 1913435 4309721 := bstep (se 2 (by rfl) ⟨1616145, by rfl⟩ : syracuseStep 4309721 = 3232291) B3232291
theorem B2873147 : Blo 1913435 2873147 := bstep (se 1 (by rfl) ⟨2154860, by rfl⟩ : syracuseStep 2873147 = 4309721) B4309721
theorem B1915431 : Blo 1913435 1915431 := bstep (se 1 (by rfl) ⟨1436573, by rfl⟩ : syracuseStep 1915431 = 2873147) B2873147
theorem B2154865 : Blo 1913435 2154865 := bbase (se 2 (by rfl) ⟨808074, by rfl⟩ : syracuseStep 2154865 = 1616149) (by norm_num)
theorem B2873153 : Blo 1913435 2873153 := bstep (se 2 (by rfl) ⟨1077432, by rfl⟩ : syracuseStep 2873153 = 2154865) B2154865
theorem B1915435 : Blo 1913435 1915435 := bstep (se 1 (by rfl) ⟨1436576, by rfl⟩ : syracuseStep 1915435 = 2873153) B2873153
theorem C0 (j : ℕ) (h1 : 478358 ≤ j) (h2 : j ≤ 478858) : Blo 1913435 (4 * j + 3) := by
  interval_cases j
  · exact B1913435
  · exact B1913439
  · exact B1913443
  · exact B1913447
  · exact B1913451
  · exact B1913455
  · exact B1913459
  · exact B1913463
  · exact B1913467
  · exact B1913471
  · exact B1913475
  · exact B1913479
  · exact B1913483
  · exact B1913487
  · exact B1913491
  · exact B1913495
  · exact B1913499
  · exact B1913503
  · exact B1913507
  · exact B1913511
  · exact B1913515
  · exact B1913519
  · exact B1913523
  · exact B1913527
  · exact B1913531
  · exact B1913535
  · exact B1913539
  · exact B1913543
  · exact B1913547
  · exact B1913551
  · exact B1913555
  · exact B1913559
  · exact B1913563
  · exact B1913567
  · exact B1913571
  · exact B1913575
  · exact B1913579
  · exact B1913583
  · exact B1913587
  · exact B1913591
  · exact B1913595
  · exact B1913599
  · exact B1913603
  · exact B1913607
  · exact B1913611
  · exact B1913615
  · exact B1913619
  · exact B1913623
  · exact B1913627
  · exact B1913631
  · exact B1913635
  · exact B1913639
  · exact B1913643
  · exact B1913647
  · exact B1913651
  · exact B1913655
  · exact B1913659
  · exact B1913663
  · exact B1913667
  · exact B1913671
  · exact B1913675
  · exact B1913679
  · exact B1913683
  · exact B1913687
  · exact B1913691
  · exact B1913695
  · exact B1913699
  · exact B1913703
  · exact B1913707
  · exact B1913711
  · exact B1913715
  · exact B1913719
  · exact B1913723
  · exact B1913727
  · exact B1913731
  · exact B1913735
  · exact B1913739
  · exact B1913743
  · exact B1913747
  · exact B1913751
  · exact B1913755
  · exact B1913759
  · exact B1913763
  · exact B1913767
  · exact B1913771
  · exact B1913775
  · exact B1913779
  · exact B1913783
  · exact B1913787
  · exact B1913791
  · exact B1913795
  · exact B1913799
  · exact B1913803
  · exact B1913807
  · exact B1913811
  · exact B1913815
  · exact B1913819
  · exact B1913823
  · exact B1913827
  · exact B1913831
  · exact B1913835
  · exact B1913839
  · exact B1913843
  · exact B1913847
  · exact B1913851
  · exact B1913855
  · exact B1913859
  · exact B1913863
  · exact B1913867
  · exact B1913871
  · exact B1913875
  · exact B1913879
  · exact B1913883
  · exact B1913887
  · exact B1913891
  · exact B1913895
  · exact B1913899
  · exact B1913903
  · exact B1913907
  · exact B1913911
  · exact B1913915
  · exact B1913919
  · exact B1913923
  · exact B1913927
  · exact B1913931
  · exact B1913935
  · exact B1913939
  · exact B1913943
  · exact B1913947
  · exact B1913951
  · exact B1913955
  · exact B1913959
  · exact B1913963
  · exact B1913967
  · exact B1913971
  · exact B1913975
  · exact B1913979
  · exact B1913983
  · exact B1913987
  · exact B1913991
  · exact B1913995
  · exact B1913999
  · exact B1914003
  · exact B1914007
  · exact B1914011
  · exact B1914015
  · exact B1914019
  · exact B1914023
  · exact B1914027
  · exact B1914031
  · exact B1914035
  · exact B1914039
  · exact B1914043
  · exact B1914047
  · exact B1914051
  · exact B1914055
  · exact B1914059
  · exact B1914063
  · exact B1914067
  · exact B1914071
  · exact B1914075
  · exact B1914079
  · exact B1914083
  · exact B1914087
  · exact B1914091
  · exact B1914095
  · exact B1914099
  · exact B1914103
  · exact B1914107
  · exact B1914111
  · exact B1914115
  · exact B1914119
  · exact B1914123
  · exact B1914127
  · exact B1914131
  · exact B1914135
  · exact B1914139
  · exact B1914143
  · exact B1914147
  · exact B1914151
  · exact B1914155
  · exact B1914159
  · exact B1914163
  · exact B1914167
  · exact B1914171
  · exact B1914175
  · exact B1914179
  · exact B1914183
  · exact B1914187
  · exact B1914191
  · exact B1914195
  · exact B1914199
  · exact B1914203
  · exact B1914207
  · exact B1914211
  · exact B1914215
  · exact B1914219
  · exact B1914223
  · exact B1914227
  · exact B1914231
  · exact B1914235
  · exact B1914239
  · exact B1914243
  · exact B1914247
  · exact B1914251
  · exact B1914255
  · exact B1914259
  · exact B1914263
  · exact B1914267
  · exact B1914271
  · exact B1914275
  · exact B1914279
  · exact B1914283
  · exact B1914287
  · exact B1914291
  · exact B1914295
  · exact B1914299
  · exact B1914303
  · exact B1914307
  · exact B1914311
  · exact B1914315
  · exact B1914319
  · exact B1914323
  · exact B1914327
  · exact B1914331
  · exact B1914335
  · exact B1914339
  · exact B1914343
  · exact B1914347
  · exact B1914351
  · exact B1914355
  · exact B1914359
  · exact B1914363
  · exact B1914367
  · exact B1914371
  · exact B1914375
  · exact B1914379
  · exact B1914383
  · exact B1914387
  · exact B1914391
  · exact B1914395
  · exact B1914399
  · exact B1914403
  · exact B1914407
  · exact B1914411
  · exact B1914415
  · exact B1914419
  · exact B1914423
  · exact B1914427
  · exact B1914431
  · exact B1914435
  · exact B1914439
  · exact B1914443
  · exact B1914447
  · exact B1914451
  · exact B1914455
  · exact B1914459
  · exact B1914463
  · exact B1914467
  · exact B1914471
  · exact B1914475
  · exact B1914479
  · exact B1914483
  · exact B1914487
  · exact B1914491
  · exact B1914495
  · exact B1914499
  · exact B1914503
  · exact B1914507
  · exact B1914511
  · exact B1914515
  · exact B1914519
  · exact B1914523
  · exact B1914527
  · exact B1914531
  · exact B1914535
  · exact B1914539
  · exact B1914543
  · exact B1914547
  · exact B1914551
  · exact B1914555
  · exact B1914559
  · exact B1914563
  · exact B1914567
  · exact B1914571
  · exact B1914575
  · exact B1914579
  · exact B1914583
  · exact B1914587
  · exact B1914591
  · exact B1914595
  · exact B1914599
  · exact B1914603
  · exact B1914607
  · exact B1914611
  · exact B1914615
  · exact B1914619
  · exact B1914623
  · exact B1914627
  · exact B1914631
  · exact B1914635
  · exact B1914639
  · exact B1914643
  · exact B1914647
  · exact B1914651
  · exact B1914655
  · exact B1914659
  · exact B1914663
  · exact B1914667
  · exact B1914671
  · exact B1914675
  · exact B1914679
  · exact B1914683
  · exact B1914687
  · exact B1914691
  · exact B1914695
  · exact B1914699
  · exact B1914703
  · exact B1914707
  · exact B1914711
  · exact B1914715
  · exact B1914719
  · exact B1914723
  · exact B1914727
  · exact B1914731
  · exact B1914735
  · exact B1914739
  · exact B1914743
  · exact B1914747
  · exact B1914751
  · exact B1914755
  · exact B1914759
  · exact B1914763
  · exact B1914767
  · exact B1914771
  · exact B1914775
  · exact B1914779
  · exact B1914783
  · exact B1914787
  · exact B1914791
  · exact B1914795
  · exact B1914799
  · exact B1914803
  · exact B1914807
  · exact B1914811
  · exact B1914815
  · exact B1914819
  · exact B1914823
  · exact B1914827
  · exact B1914831
  · exact B1914835
  · exact B1914839
  · exact B1914843
  · exact B1914847
  · exact B1914851
  · exact B1914855
  · exact B1914859
  · exact B1914863
  · exact B1914867
  · exact B1914871
  · exact B1914875
  · exact B1914879
  · exact B1914883
  · exact B1914887
  · exact B1914891
  · exact B1914895
  · exact B1914899
  · exact B1914903
  · exact B1914907
  · exact B1914911
  · exact B1914915
  · exact B1914919
  · exact B1914923
  · exact B1914927
  · exact B1914931
  · exact B1914935
  · exact B1914939
  · exact B1914943
  · exact B1914947
  · exact B1914951
  · exact B1914955
  · exact B1914959
  · exact B1914963
  · exact B1914967
  · exact B1914971
  · exact B1914975
  · exact B1914979
  · exact B1914983
  · exact B1914987
  · exact B1914991
  · exact B1914995
  · exact B1914999
  · exact B1915003
  · exact B1915007
  · exact B1915011
  · exact B1915015
  · exact B1915019
  · exact B1915023
  · exact B1915027
  · exact B1915031
  · exact B1915035
  · exact B1915039
  · exact B1915043
  · exact B1915047
  · exact B1915051
  · exact B1915055
  · exact B1915059
  · exact B1915063
  · exact B1915067
  · exact B1915071
  · exact B1915075
  · exact B1915079
  · exact B1915083
  · exact B1915087
  · exact B1915091
  · exact B1915095
  · exact B1915099
  · exact B1915103
  · exact B1915107
  · exact B1915111
  · exact B1915115
  · exact B1915119
  · exact B1915123
  · exact B1915127
  · exact B1915131
  · exact B1915135
  · exact B1915139
  · exact B1915143
  · exact B1915147
  · exact B1915151
  · exact B1915155
  · exact B1915159
  · exact B1915163
  · exact B1915167
  · exact B1915171
  · exact B1915175
  · exact B1915179
  · exact B1915183
  · exact B1915187
  · exact B1915191
  · exact B1915195
  · exact B1915199
  · exact B1915203
  · exact B1915207
  · exact B1915211
  · exact B1915215
  · exact B1915219
  · exact B1915223
  · exact B1915227
  · exact B1915231
  · exact B1915235
  · exact B1915239
  · exact B1915243
  · exact B1915247
  · exact B1915251
  · exact B1915255
  · exact B1915259
  · exact B1915263
  · exact B1915267
  · exact B1915271
  · exact B1915275
  · exact B1915279
  · exact B1915283
  · exact B1915287
  · exact B1915291
  · exact B1915295
  · exact B1915299
  · exact B1915303
  · exact B1915307
  · exact B1915311
  · exact B1915315
  · exact B1915319
  · exact B1915323
  · exact B1915327
  · exact B1915331
  · exact B1915335
  · exact B1915339
  · exact B1915343
  · exact B1915347
  · exact B1915351
  · exact B1915355
  · exact B1915359
  · exact B1915363
  · exact B1915367
  · exact B1915371
  · exact B1915375
  · exact B1915379
  · exact B1915383
  · exact B1915387
  · exact B1915391
  · exact B1915395
  · exact B1915399
  · exact B1915403
  · exact B1915407
  · exact B1915411
  · exact B1915415
  · exact B1915419
  · exact B1915423
  · exact B1915427
  · exact B1915431
  · exact B1915435
theorem solution (m : ℕ) (hlo : 1913435 ≤ m) (hhi : m ≤ 1915435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 478358 ≤ j := by omega
    have hj2 : j ≤ 478858 := by omega
    have hb : Blo 1913435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
