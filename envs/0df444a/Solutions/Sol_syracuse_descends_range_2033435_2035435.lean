-- Prove2me | solution 1 for syracuse_descends_range_2033435_2035435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:49:08.517979+00:00
-- url     : https://prove2.me/submissions/badfb7d0-fd31-4d83-99a5-b6fdad28bbe9

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

theorem B9660149 : Blo 2033435 9660149 := bbase (se 5 (by rfl) ⟨452819, by rfl⟩ : syracuseStep 9660149 = 905639) (by norm_num)
theorem B6440099 : Blo 2033435 6440099 := bstep (se 1 (by rfl) ⟨4830074, by rfl⟩ : syracuseStep 6440099 = 9660149) B9660149
theorem B68694389 : Blo 2033435 68694389 := bstep (se 5 (by rfl) ⟨3220049, by rfl⟩ : syracuseStep 68694389 = 6440099) B6440099
theorem B45796259 : Blo 2033435 45796259 := bstep (se 1 (by rfl) ⟨34347194, by rfl⟩ : syracuseStep 45796259 = 68694389) B68694389
theorem B30530839 : Blo 2033435 30530839 := bstep (se 1 (by rfl) ⟨22898129, by rfl⟩ : syracuseStep 30530839 = 45796259) B45796259
theorem B40707785 : Blo 2033435 40707785 := bstep (se 2 (by rfl) ⟨15265419, by rfl⟩ : syracuseStep 40707785 = 30530839) B30530839
theorem B108554093 : Blo 2033435 108554093 := bstep (se 3 (by rfl) ⟨20353892, by rfl⟩ : syracuseStep 108554093 = 40707785) B40707785
theorem B72369395 : Blo 2033435 72369395 := bstep (se 1 (by rfl) ⟨54277046, by rfl⟩ : syracuseStep 72369395 = 108554093) B108554093
theorem B48246263 : Blo 2033435 48246263 := bstep (se 1 (by rfl) ⟨36184697, by rfl⟩ : syracuseStep 48246263 = 72369395) B72369395
theorem B32164175 : Blo 2033435 32164175 := bstep (se 1 (by rfl) ⟨24123131, by rfl⟩ : syracuseStep 32164175 = 48246263) B48246263
theorem B85771133 : Blo 2033435 85771133 := bstep (se 3 (by rfl) ⟨16082087, by rfl⟩ : syracuseStep 85771133 = 32164175) B32164175
theorem B57180755 : Blo 2033435 57180755 := bstep (se 1 (by rfl) ⟨42885566, by rfl⟩ : syracuseStep 57180755 = 85771133) B85771133
theorem B38120503 : Blo 2033435 38120503 := bstep (se 1 (by rfl) ⟨28590377, by rfl⟩ : syracuseStep 38120503 = 57180755) B57180755
theorem B50827337 : Blo 2033435 50827337 := bstep (se 2 (by rfl) ⟨19060251, by rfl⟩ : syracuseStep 50827337 = 38120503) B38120503
theorem B33884891 : Blo 2033435 33884891 := bstep (se 1 (by rfl) ⟨25413668, by rfl⟩ : syracuseStep 33884891 = 50827337) B50827337
theorem B22589927 : Blo 2033435 22589927 := bstep (se 1 (by rfl) ⟨16942445, by rfl⟩ : syracuseStep 22589927 = 33884891) B33884891
theorem B15059951 : Blo 2033435 15059951 := bstep (se 1 (by rfl) ⟨11294963, by rfl⟩ : syracuseStep 15059951 = 22589927) B22589927
theorem B10039967 : Blo 2033435 10039967 := bstep (se 1 (by rfl) ⟨7529975, by rfl⟩ : syracuseStep 10039967 = 15059951) B15059951
theorem B6693311 : Blo 2033435 6693311 := bstep (se 1 (by rfl) ⟨5019983, by rfl⟩ : syracuseStep 6693311 = 10039967) B10039967
theorem B17848829 : Blo 2033435 17848829 := bstep (se 3 (by rfl) ⟨3346655, by rfl⟩ : syracuseStep 17848829 = 6693311) B6693311
theorem B47596877 : Blo 2033435 47596877 := bstep (se 3 (by rfl) ⟨8924414, by rfl⟩ : syracuseStep 47596877 = 17848829) B17848829
theorem B507700021 : Blo 2033435 507700021 := bstep (se 5 (by rfl) ⟨23798438, by rfl⟩ : syracuseStep 507700021 = 47596877) B47596877
theorem B676933361 : Blo 2033435 676933361 := bstep (se 2 (by rfl) ⟨253850010, by rfl⟩ : syracuseStep 676933361 = 507700021) B507700021
theorem B451288907 : Blo 2033435 451288907 := bstep (se 1 (by rfl) ⟨338466680, by rfl⟩ : syracuseStep 451288907 = 676933361) B676933361
theorem B300859271 : Blo 2033435 300859271 := bstep (se 1 (by rfl) ⟨225644453, by rfl⟩ : syracuseStep 300859271 = 451288907) B451288907
theorem B200572847 : Blo 2033435 200572847 := bstep (se 1 (by rfl) ⟨150429635, by rfl⟩ : syracuseStep 200572847 = 300859271) B300859271
theorem B133715231 : Blo 2033435 133715231 := bstep (se 1 (by rfl) ⟨100286423, by rfl⟩ : syracuseStep 133715231 = 200572847) B200572847
theorem B89143487 : Blo 2033435 89143487 := bstep (se 1 (by rfl) ⟨66857615, by rfl⟩ : syracuseStep 89143487 = 133715231) B133715231
theorem B59428991 : Blo 2033435 59428991 := bstep (se 1 (by rfl) ⟨44571743, by rfl⟩ : syracuseStep 59428991 = 89143487) B89143487
theorem B158477309 : Blo 2033435 158477309 := bstep (se 3 (by rfl) ⟨29714495, by rfl⟩ : syracuseStep 158477309 = 59428991) B59428991
theorem B105651539 : Blo 2033435 105651539 := bstep (se 1 (by rfl) ⟨79238654, by rfl⟩ : syracuseStep 105651539 = 158477309) B158477309
theorem B70434359 : Blo 2033435 70434359 := bstep (se 1 (by rfl) ⟨52825769, by rfl⟩ : syracuseStep 70434359 = 105651539) B105651539
theorem B46956239 : Blo 2033435 46956239 := bstep (se 1 (by rfl) ⟨35217179, by rfl⟩ : syracuseStep 46956239 = 70434359) B70434359
theorem B31304159 : Blo 2033435 31304159 := bstep (se 1 (by rfl) ⟨23478119, by rfl⟩ : syracuseStep 31304159 = 46956239) B46956239
theorem B20869439 : Blo 2033435 20869439 := bstep (se 1 (by rfl) ⟨15652079, by rfl⟩ : syracuseStep 20869439 = 31304159) B31304159
theorem B222607349 : Blo 2033435 222607349 := bstep (se 5 (by rfl) ⟨10434719, by rfl⟩ : syracuseStep 222607349 = 20869439) B20869439
theorem B148404899 : Blo 2033435 148404899 := bstep (se 1 (by rfl) ⟨111303674, by rfl⟩ : syracuseStep 148404899 = 222607349) B222607349
theorem B98936599 : Blo 2033435 98936599 := bstep (se 1 (by rfl) ⟨74202449, by rfl⟩ : syracuseStep 98936599 = 148404899) B148404899
theorem B131915465 : Blo 2033435 131915465 := bstep (se 2 (by rfl) ⟨49468299, by rfl⟩ : syracuseStep 131915465 = 98936599) B98936599
theorem B87943643 : Blo 2033435 87943643 := bstep (se 1 (by rfl) ⟨65957732, by rfl⟩ : syracuseStep 87943643 = 131915465) B131915465
theorem B58629095 : Blo 2033435 58629095 := bstep (se 1 (by rfl) ⟨43971821, by rfl⟩ : syracuseStep 58629095 = 87943643) B87943643
theorem B39086063 : Blo 2033435 39086063 := bstep (se 1 (by rfl) ⟨29314547, by rfl⟩ : syracuseStep 39086063 = 58629095) B58629095
theorem B26057375 : Blo 2033435 26057375 := bstep (se 1 (by rfl) ⟨19543031, by rfl⟩ : syracuseStep 26057375 = 39086063) B39086063
theorem B17371583 : Blo 2033435 17371583 := bstep (se 1 (by rfl) ⟨13028687, by rfl⟩ : syracuseStep 17371583 = 26057375) B26057375
theorem B11581055 : Blo 2033435 11581055 := bstep (se 1 (by rfl) ⟨8685791, by rfl⟩ : syracuseStep 11581055 = 17371583) B17371583
theorem B7720703 : Blo 2033435 7720703 := bstep (se 1 (by rfl) ⟨5790527, by rfl⟩ : syracuseStep 7720703 = 11581055) B11581055
theorem B5147135 : Blo 2033435 5147135 := bstep (se 1 (by rfl) ⟨3860351, by rfl⟩ : syracuseStep 5147135 = 7720703) B7720703
theorem B3431423 : Blo 2033435 3431423 := bstep (se 1 (by rfl) ⟨2573567, by rfl⟩ : syracuseStep 3431423 = 5147135) B5147135
theorem B2287615 : Blo 2033435 2287615 := bstep (se 1 (by rfl) ⟨1715711, by rfl⟩ : syracuseStep 2287615 = 3431423) B3431423
theorem B3050153 : Blo 2033435 3050153 := bstep (se 2 (by rfl) ⟨1143807, by rfl⟩ : syracuseStep 3050153 = 2287615) B2287615
theorem B2033435 : Blo 2033435 2033435 := bstep (se 1 (by rfl) ⟨1525076, by rfl⟩ : syracuseStep 2033435 = 3050153) B3050153
theorem B2895269 : Blo 2033435 2895269 := bbase (se 4 (by rfl) ⟨271431, by rfl⟩ : syracuseStep 2895269 = 542863) (by norm_num)
theorem B7720717 : Blo 2033435 7720717 := bstep (se 3 (by rfl) ⟨1447634, by rfl⟩ : syracuseStep 7720717 = 2895269) B2895269
theorem B10294289 : Blo 2033435 10294289 := bstep (se 2 (by rfl) ⟨3860358, by rfl⟩ : syracuseStep 10294289 = 7720717) B7720717
theorem B6862859 : Blo 2033435 6862859 := bstep (se 1 (by rfl) ⟨5147144, by rfl⟩ : syracuseStep 6862859 = 10294289) B10294289
theorem B4575239 : Blo 2033435 4575239 := bstep (se 1 (by rfl) ⟨3431429, by rfl⟩ : syracuseStep 4575239 = 6862859) B6862859
theorem B3050159 : Blo 2033435 3050159 := bstep (se 1 (by rfl) ⟨2287619, by rfl⟩ : syracuseStep 3050159 = 4575239) B4575239
theorem B2033439 : Blo 2033435 2033439 := bstep (se 1 (by rfl) ⟨1525079, by rfl⟩ : syracuseStep 2033439 = 3050159) B3050159
theorem B3050165 : Blo 2033435 3050165 := bbase (se 5 (by rfl) ⟨142976, by rfl⟩ : syracuseStep 3050165 = 285953) (by norm_num)
theorem B2033443 : Blo 2033435 2033443 := bstep (se 1 (by rfl) ⟨1525082, by rfl⟩ : syracuseStep 2033443 = 3050165) B3050165
theorem B5147165 : Blo 2033435 5147165 := bbase (se 3 (by rfl) ⟨965093, by rfl⟩ : syracuseStep 5147165 = 1930187) (by norm_num)
theorem B3431443 : Blo 2033435 3431443 := bstep (se 1 (by rfl) ⟨2573582, by rfl⟩ : syracuseStep 3431443 = 5147165) B5147165
theorem B4575257 : Blo 2033435 4575257 := bstep (se 2 (by rfl) ⟨1715721, by rfl⟩ : syracuseStep 4575257 = 3431443) B3431443
theorem B3050171 : Blo 2033435 3050171 := bstep (se 1 (by rfl) ⟨2287628, by rfl⟩ : syracuseStep 3050171 = 4575257) B4575257
theorem B2033447 : Blo 2033435 2033447 := bstep (se 1 (by rfl) ⟨1525085, by rfl⟩ : syracuseStep 2033447 = 3050171) B3050171
theorem B2287633 : Blo 2033435 2287633 := bbase (se 2 (by rfl) ⟨857862, by rfl⟩ : syracuseStep 2287633 = 1715725) (by norm_num)
theorem B3050177 : Blo 2033435 3050177 := bstep (se 2 (by rfl) ⟨1143816, by rfl⟩ : syracuseStep 3050177 = 2287633) B2287633
theorem B2033451 : Blo 2033435 2033451 := bstep (se 1 (by rfl) ⟨1525088, by rfl⟩ : syracuseStep 2033451 = 3050177) B3050177
theorem B3860389 : Blo 2033435 3860389 := bbase (se 4 (by rfl) ⟨361911, by rfl⟩ : syracuseStep 3860389 = 723823) (by norm_num)
theorem B5147185 : Blo 2033435 5147185 := bstep (se 2 (by rfl) ⟨1930194, by rfl⟩ : syracuseStep 5147185 = 3860389) B3860389
theorem B6862913 : Blo 2033435 6862913 := bstep (se 2 (by rfl) ⟨2573592, by rfl⟩ : syracuseStep 6862913 = 5147185) B5147185
theorem B4575275 : Blo 2033435 4575275 := bstep (se 1 (by rfl) ⟨3431456, by rfl⟩ : syracuseStep 4575275 = 6862913) B6862913
theorem B3050183 : Blo 2033435 3050183 := bstep (se 1 (by rfl) ⟨2287637, by rfl⟩ : syracuseStep 3050183 = 4575275) B4575275
theorem B2033455 : Blo 2033435 2033455 := bstep (se 1 (by rfl) ⟨1525091, by rfl⟩ : syracuseStep 2033455 = 3050183) B3050183
theorem B3050189 : Blo 2033435 3050189 := bbase (se 3 (by rfl) ⟨571910, by rfl⟩ : syracuseStep 3050189 = 1143821) (by norm_num)
theorem B2033459 : Blo 2033435 2033459 := bstep (se 1 (by rfl) ⟨1525094, by rfl⟩ : syracuseStep 2033459 = 3050189) B3050189
theorem B4575293 : Blo 2033435 4575293 := bbase (se 3 (by rfl) ⟨857867, by rfl⟩ : syracuseStep 4575293 = 1715735) (by norm_num)
theorem B3050195 : Blo 2033435 3050195 := bstep (se 1 (by rfl) ⟨2287646, by rfl⟩ : syracuseStep 3050195 = 4575293) B4575293
theorem B2033463 : Blo 2033435 2033463 := bstep (se 1 (by rfl) ⟨1525097, by rfl⟩ : syracuseStep 2033463 = 3050195) B3050195
theorem B3431477 : Blo 2033435 3431477 := bbase (se 5 (by rfl) ⟨160850, by rfl⟩ : syracuseStep 3431477 = 321701) (by norm_num)
theorem B2287651 : Blo 2033435 2287651 := bstep (se 1 (by rfl) ⟨1715738, by rfl⟩ : syracuseStep 2287651 = 3431477) B3431477
theorem B3050201 : Blo 2033435 3050201 := bstep (se 2 (by rfl) ⟨1143825, by rfl⟩ : syracuseStep 3050201 = 2287651) B2287651
theorem B2033467 : Blo 2033435 2033467 := bstep (se 1 (by rfl) ⟨1525100, by rfl⟩ : syracuseStep 2033467 = 3050201) B3050201
theorem B5790629 : Blo 2033435 5790629 := bbase (se 4 (by rfl) ⟨542871, by rfl⟩ : syracuseStep 5790629 = 1085743) (by norm_num)
theorem B15441677 : Blo 2033435 15441677 := bstep (se 3 (by rfl) ⟨2895314, by rfl⟩ : syracuseStep 15441677 = 5790629) B5790629
theorem B10294451 : Blo 2033435 10294451 := bstep (se 1 (by rfl) ⟨7720838, by rfl⟩ : syracuseStep 10294451 = 15441677) B15441677
theorem B6862967 : Blo 2033435 6862967 := bstep (se 1 (by rfl) ⟨5147225, by rfl⟩ : syracuseStep 6862967 = 10294451) B10294451
theorem B4575311 : Blo 2033435 4575311 := bstep (se 1 (by rfl) ⟨3431483, by rfl⟩ : syracuseStep 4575311 = 6862967) B6862967
theorem B3050207 : Blo 2033435 3050207 := bstep (se 1 (by rfl) ⟨2287655, by rfl⟩ : syracuseStep 3050207 = 4575311) B4575311
theorem B2033471 : Blo 2033435 2033471 := bstep (se 1 (by rfl) ⟨1525103, by rfl⟩ : syracuseStep 2033471 = 3050207) B3050207
theorem B3050213 : Blo 2033435 3050213 := bbase (se 4 (by rfl) ⟨285957, by rfl⟩ : syracuseStep 3050213 = 571915) (by norm_num)
theorem B2033475 : Blo 2033435 2033475 := bstep (se 1 (by rfl) ⟨1525106, by rfl⟩ : syracuseStep 2033475 = 3050213) B3050213
theorem B12367349 : Blo 2033435 12367349 := bbase (se 5 (by rfl) ⟨579719, by rfl⟩ : syracuseStep 12367349 = 1159439) (by norm_num)
theorem B8244899 : Blo 2033435 8244899 := bstep (se 1 (by rfl) ⟨6183674, by rfl⟩ : syracuseStep 8244899 = 12367349) B12367349
theorem B5496599 : Blo 2033435 5496599 := bstep (se 1 (by rfl) ⟨4122449, by rfl⟩ : syracuseStep 5496599 = 8244899) B8244899
theorem B3664399 : Blo 2033435 3664399 := bstep (se 1 (by rfl) ⟨2748299, by rfl⟩ : syracuseStep 3664399 = 5496599) B5496599
theorem B4885865 : Blo 2033435 4885865 := bstep (se 2 (by rfl) ⟨1832199, by rfl⟩ : syracuseStep 4885865 = 3664399) B3664399
theorem B3257243 : Blo 2033435 3257243 := bstep (se 1 (by rfl) ⟨2442932, by rfl⟩ : syracuseStep 3257243 = 4885865) B4885865
theorem B2171495 : Blo 2033435 2171495 := bstep (se 1 (by rfl) ⟨1628621, by rfl⟩ : syracuseStep 2171495 = 3257243) B3257243
theorem B5790653 : Blo 2033435 5790653 := bstep (se 3 (by rfl) ⟨1085747, by rfl⟩ : syracuseStep 5790653 = 2171495) B2171495
theorem B3860435 : Blo 2033435 3860435 := bstep (se 1 (by rfl) ⟨2895326, by rfl⟩ : syracuseStep 3860435 = 5790653) B5790653
theorem B2573623 : Blo 2033435 2573623 := bstep (se 1 (by rfl) ⟨1930217, by rfl⟩ : syracuseStep 2573623 = 3860435) B3860435
theorem B3431497 : Blo 2033435 3431497 := bstep (se 2 (by rfl) ⟨1286811, by rfl⟩ : syracuseStep 3431497 = 2573623) B2573623
theorem B4575329 : Blo 2033435 4575329 := bstep (se 2 (by rfl) ⟨1715748, by rfl⟩ : syracuseStep 4575329 = 3431497) B3431497
theorem B3050219 : Blo 2033435 3050219 := bstep (se 1 (by rfl) ⟨2287664, by rfl⟩ : syracuseStep 3050219 = 4575329) B4575329
theorem B2033479 : Blo 2033435 2033479 := bstep (se 1 (by rfl) ⟨1525109, by rfl⟩ : syracuseStep 2033479 = 3050219) B3050219
theorem B2287669 : Blo 2033435 2287669 := bbase (se 5 (by rfl) ⟨107234, by rfl⟩ : syracuseStep 2287669 = 214469) (by norm_num)
theorem B3050225 : Blo 2033435 3050225 := bstep (se 2 (by rfl) ⟨1143834, by rfl⟩ : syracuseStep 3050225 = 2287669) B2287669
theorem B2033483 : Blo 2033435 2033483 := bstep (se 1 (by rfl) ⟨1525112, by rfl⟩ : syracuseStep 2033483 = 3050225) B3050225
theorem B2573633 : Blo 2033435 2573633 := bbase (se 2 (by rfl) ⟨965112, by rfl⟩ : syracuseStep 2573633 = 1930225) (by norm_num)
theorem B6863021 : Blo 2033435 6863021 := bstep (se 3 (by rfl) ⟨1286816, by rfl⟩ : syracuseStep 6863021 = 2573633) B2573633
theorem B4575347 : Blo 2033435 4575347 := bstep (se 1 (by rfl) ⟨3431510, by rfl⟩ : syracuseStep 4575347 = 6863021) B6863021
theorem B3050231 : Blo 2033435 3050231 := bstep (se 1 (by rfl) ⟨2287673, by rfl⟩ : syracuseStep 3050231 = 4575347) B4575347
theorem B2033487 : Blo 2033435 2033487 := bstep (se 1 (by rfl) ⟨1525115, by rfl⟩ : syracuseStep 2033487 = 3050231) B3050231
theorem B3050237 : Blo 2033435 3050237 := bbase (se 3 (by rfl) ⟨571919, by rfl⟩ : syracuseStep 3050237 = 1143839) (by norm_num)
theorem B2033491 : Blo 2033435 2033491 := bstep (se 1 (by rfl) ⟨1525118, by rfl⟩ : syracuseStep 2033491 = 3050237) B3050237
theorem B4575365 : Blo 2033435 4575365 := bbase (se 4 (by rfl) ⟨428940, by rfl⟩ : syracuseStep 4575365 = 857881) (by norm_num)
theorem B3050243 : Blo 2033435 3050243 := bstep (se 1 (by rfl) ⟨2287682, by rfl⟩ : syracuseStep 3050243 = 4575365) B4575365
theorem B2033495 : Blo 2033435 2033495 := bstep (se 1 (by rfl) ⟨1525121, by rfl⟩ : syracuseStep 2033495 = 3050243) B3050243
theorem B2061245 : Blo 2033435 2061245 := bbase (se 3 (by rfl) ⟨386483, by rfl⟩ : syracuseStep 2061245 = 772967) (by norm_num)
theorem B5496653 : Blo 2033435 5496653 := bstep (se 3 (by rfl) ⟨1030622, by rfl⟩ : syracuseStep 5496653 = 2061245) B2061245
theorem B3664435 : Blo 2033435 3664435 := bstep (se 1 (by rfl) ⟨2748326, by rfl⟩ : syracuseStep 3664435 = 5496653) B5496653
theorem B4885913 : Blo 2033435 4885913 := bstep (se 2 (by rfl) ⟨1832217, by rfl⟩ : syracuseStep 4885913 = 3664435) B3664435
theorem B3257275 : Blo 2033435 3257275 := bstep (se 1 (by rfl) ⟨2442956, by rfl⟩ : syracuseStep 3257275 = 4885913) B4885913
theorem B4343033 : Blo 2033435 4343033 := bstep (se 2 (by rfl) ⟨1628637, by rfl⟩ : syracuseStep 4343033 = 3257275) B3257275
theorem B2895355 : Blo 2033435 2895355 := bstep (se 1 (by rfl) ⟨2171516, by rfl⟩ : syracuseStep 2895355 = 4343033) B4343033
theorem B3860473 : Blo 2033435 3860473 := bstep (se 2 (by rfl) ⟨1447677, by rfl⟩ : syracuseStep 3860473 = 2895355) B2895355
theorem B5147297 : Blo 2033435 5147297 := bstep (se 2 (by rfl) ⟨1930236, by rfl⟩ : syracuseStep 5147297 = 3860473) B3860473
theorem B3431531 : Blo 2033435 3431531 := bstep (se 1 (by rfl) ⟨2573648, by rfl⟩ : syracuseStep 3431531 = 5147297) B5147297
theorem B2287687 : Blo 2033435 2287687 := bstep (se 1 (by rfl) ⟨1715765, by rfl⟩ : syracuseStep 2287687 = 3431531) B3431531
theorem B3050249 : Blo 2033435 3050249 := bstep (se 2 (by rfl) ⟨1143843, by rfl⟩ : syracuseStep 3050249 = 2287687) B2287687
theorem B2033499 : Blo 2033435 2033499 := bstep (se 1 (by rfl) ⟨1525124, by rfl⟩ : syracuseStep 2033499 = 3050249) B3050249
theorem B10294613 : Blo 2033435 10294613 := bbase (se 14 (by rfl) ⟨942, by rfl⟩ : syracuseStep 10294613 = 1885) (by norm_num)
theorem B6863075 : Blo 2033435 6863075 := bstep (se 1 (by rfl) ⟨5147306, by rfl⟩ : syracuseStep 6863075 = 10294613) B10294613
theorem B4575383 : Blo 2033435 4575383 := bstep (se 1 (by rfl) ⟨3431537, by rfl⟩ : syracuseStep 4575383 = 6863075) B6863075
theorem B3050255 : Blo 2033435 3050255 := bstep (se 1 (by rfl) ⟨2287691, by rfl⟩ : syracuseStep 3050255 = 4575383) B4575383
theorem B2033503 : Blo 2033435 2033503 := bstep (se 1 (by rfl) ⟨1525127, by rfl⟩ : syracuseStep 2033503 = 3050255) B3050255
theorem B3050261 : Blo 2033435 3050261 := bbase (se 6 (by rfl) ⟨71490, by rfl⟩ : syracuseStep 3050261 = 142981) (by norm_num)
theorem B2033507 : Blo 2033435 2033507 := bstep (se 1 (by rfl) ⟨1525130, by rfl⟩ : syracuseStep 2033507 = 3050261) B3050261
theorem B23478997 : Blo 2033435 23478997 := bbase (se 7 (by rfl) ⟨275144, by rfl⟩ : syracuseStep 23478997 = 550289) (by norm_num)
theorem B31305329 : Blo 2033435 31305329 := bstep (se 2 (by rfl) ⟨11739498, by rfl⟩ : syracuseStep 31305329 = 23478997) B23478997
theorem B20870219 : Blo 2033435 20870219 := bstep (se 1 (by rfl) ⟨15652664, by rfl⟩ : syracuseStep 20870219 = 31305329) B31305329
theorem B13913479 : Blo 2033435 13913479 := bstep (se 1 (by rfl) ⟨10435109, by rfl⟩ : syracuseStep 13913479 = 20870219) B20870219
theorem B18551305 : Blo 2033435 18551305 := bstep (se 2 (by rfl) ⟨6956739, by rfl⟩ : syracuseStep 18551305 = 13913479) B13913479
theorem B24735073 : Blo 2033435 24735073 := bstep (se 2 (by rfl) ⟨9275652, by rfl⟩ : syracuseStep 24735073 = 18551305) B18551305
theorem B32980097 : Blo 2033435 32980097 := bstep (se 2 (by rfl) ⟨12367536, by rfl⟩ : syracuseStep 32980097 = 24735073) B24735073
theorem B21986731 : Blo 2033435 21986731 := bstep (se 1 (by rfl) ⟨16490048, by rfl⟩ : syracuseStep 21986731 = 32980097) B32980097
theorem B29315641 : Blo 2033435 29315641 := bstep (se 2 (by rfl) ⟨10993365, by rfl⟩ : syracuseStep 29315641 = 21986731) B21986731
theorem B39087521 : Blo 2033435 39087521 := bstep (se 2 (by rfl) ⟨14657820, by rfl⟩ : syracuseStep 39087521 = 29315641) B29315641
theorem B26058347 : Blo 2033435 26058347 := bstep (se 1 (by rfl) ⟨19543760, by rfl⟩ : syracuseStep 26058347 = 39087521) B39087521
theorem B17372231 : Blo 2033435 17372231 := bstep (se 1 (by rfl) ⟨13029173, by rfl⟩ : syracuseStep 17372231 = 26058347) B26058347
theorem B11581487 : Blo 2033435 11581487 := bstep (se 1 (by rfl) ⟨8686115, by rfl⟩ : syracuseStep 11581487 = 17372231) B17372231
theorem B7720991 : Blo 2033435 7720991 := bstep (se 1 (by rfl) ⟨5790743, by rfl⟩ : syracuseStep 7720991 = 11581487) B11581487
theorem B5147327 : Blo 2033435 5147327 := bstep (se 1 (by rfl) ⟨3860495, by rfl⟩ : syracuseStep 5147327 = 7720991) B7720991
theorem B3431551 : Blo 2033435 3431551 := bstep (se 1 (by rfl) ⟨2573663, by rfl⟩ : syracuseStep 3431551 = 5147327) B5147327
theorem B4575401 : Blo 2033435 4575401 := bstep (se 2 (by rfl) ⟨1715775, by rfl⟩ : syracuseStep 4575401 = 3431551) B3431551
theorem B3050267 : Blo 2033435 3050267 := bstep (se 1 (by rfl) ⟨2287700, by rfl⟩ : syracuseStep 3050267 = 4575401) B4575401
theorem B2033511 : Blo 2033435 2033511 := bstep (se 1 (by rfl) ⟨1525133, by rfl⟩ : syracuseStep 2033511 = 3050267) B3050267
theorem B2287705 : Blo 2033435 2287705 := bbase (se 2 (by rfl) ⟨857889, by rfl⟩ : syracuseStep 2287705 = 1715779) (by norm_num)
theorem B3050273 : Blo 2033435 3050273 := bstep (se 2 (by rfl) ⟨1143852, by rfl⟩ : syracuseStep 3050273 = 2287705) B2287705
theorem B2033515 : Blo 2033435 2033515 := bstep (se 1 (by rfl) ⟨1525136, by rfl⟩ : syracuseStep 2033515 = 3050273) B3050273
theorem B6514613 : Blo 2033435 6514613 := bbase (se 5 (by rfl) ⟨305372, by rfl⟩ : syracuseStep 6514613 = 610745) (by norm_num)
theorem B4343075 : Blo 2033435 4343075 := bstep (se 1 (by rfl) ⟨3257306, by rfl⟩ : syracuseStep 4343075 = 6514613) B6514613
theorem B2895383 : Blo 2033435 2895383 := bstep (se 1 (by rfl) ⟨2171537, by rfl⟩ : syracuseStep 2895383 = 4343075) B4343075
theorem B7721021 : Blo 2033435 7721021 := bstep (se 3 (by rfl) ⟨1447691, by rfl⟩ : syracuseStep 7721021 = 2895383) B2895383
theorem B5147347 : Blo 2033435 5147347 := bstep (se 1 (by rfl) ⟨3860510, by rfl⟩ : syracuseStep 5147347 = 7721021) B7721021
theorem B6863129 : Blo 2033435 6863129 := bstep (se 2 (by rfl) ⟨2573673, by rfl⟩ : syracuseStep 6863129 = 5147347) B5147347
theorem B4575419 : Blo 2033435 4575419 := bstep (se 1 (by rfl) ⟨3431564, by rfl⟩ : syracuseStep 4575419 = 6863129) B6863129
theorem B3050279 : Blo 2033435 3050279 := bstep (se 1 (by rfl) ⟨2287709, by rfl⟩ : syracuseStep 3050279 = 4575419) B4575419
theorem B2033519 : Blo 2033435 2033519 := bstep (se 1 (by rfl) ⟨1525139, by rfl⟩ : syracuseStep 2033519 = 3050279) B3050279
theorem B3050285 : Blo 2033435 3050285 := bbase (se 3 (by rfl) ⟨571928, by rfl⟩ : syracuseStep 3050285 = 1143857) (by norm_num)
theorem B2033523 : Blo 2033435 2033523 := bstep (se 1 (by rfl) ⟨1525142, by rfl⟩ : syracuseStep 2033523 = 3050285) B3050285
theorem B4575437 : Blo 2033435 4575437 := bbase (se 3 (by rfl) ⟨857894, by rfl⟩ : syracuseStep 4575437 = 1715789) (by norm_num)
theorem B3050291 : Blo 2033435 3050291 := bstep (se 1 (by rfl) ⟨2287718, by rfl⟩ : syracuseStep 3050291 = 4575437) B4575437
theorem B2033527 : Blo 2033435 2033527 := bstep (se 1 (by rfl) ⟨1525145, by rfl⟩ : syracuseStep 2033527 = 3050291) B3050291
theorem B2573689 : Blo 2033435 2573689 := bbase (se 2 (by rfl) ⟨965133, by rfl⟩ : syracuseStep 2573689 = 1930267) (by norm_num)
theorem B3431585 : Blo 2033435 3431585 := bstep (se 2 (by rfl) ⟨1286844, by rfl⟩ : syracuseStep 3431585 = 2573689) B2573689
theorem B2287723 : Blo 2033435 2287723 := bstep (se 1 (by rfl) ⟨1715792, by rfl⟩ : syracuseStep 2287723 = 3431585) B3431585
theorem B3050297 : Blo 2033435 3050297 := bstep (se 2 (by rfl) ⟨1143861, by rfl⟩ : syracuseStep 3050297 = 2287723) B2287723
theorem B2033531 : Blo 2033435 2033531 := bstep (se 1 (by rfl) ⟨1525148, by rfl⟩ : syracuseStep 2033531 = 3050297) B3050297
theorem B3913213 : Blo 2033435 3913213 := bbase (se 3 (by rfl) ⟨733727, by rfl⟩ : syracuseStep 3913213 = 1467455) (by norm_num)
theorem B5217617 : Blo 2033435 5217617 := bstep (se 2 (by rfl) ⟨1956606, by rfl⟩ : syracuseStep 5217617 = 3913213) B3913213
theorem B3478411 : Blo 2033435 3478411 := bstep (se 1 (by rfl) ⟨2608808, by rfl⟩ : syracuseStep 3478411 = 5217617) B5217617
theorem B4637881 : Blo 2033435 4637881 := bstep (se 2 (by rfl) ⟨1739205, by rfl⟩ : syracuseStep 4637881 = 3478411) B3478411
theorem B24735365 : Blo 2033435 24735365 := bstep (se 4 (by rfl) ⟨2318940, by rfl⟩ : syracuseStep 24735365 = 4637881) B4637881
theorem B16490243 : Blo 2033435 16490243 := bstep (se 1 (by rfl) ⟨12367682, by rfl⟩ : syracuseStep 16490243 = 24735365) B24735365
theorem B10993495 : Blo 2033435 10993495 := bstep (se 1 (by rfl) ⟨8245121, by rfl⟩ : syracuseStep 10993495 = 16490243) B16490243
theorem B14657993 : Blo 2033435 14657993 := bstep (se 2 (by rfl) ⟨5496747, by rfl⟩ : syracuseStep 14657993 = 10993495) B10993495
theorem B9771995 : Blo 2033435 9771995 := bstep (se 1 (by rfl) ⟨7328996, by rfl⟩ : syracuseStep 9771995 = 14657993) B14657993
theorem B6514663 : Blo 2033435 6514663 := bstep (se 1 (by rfl) ⟨4885997, by rfl⟩ : syracuseStep 6514663 = 9771995) B9771995
theorem B8686217 : Blo 2033435 8686217 := bstep (se 2 (by rfl) ⟨3257331, by rfl⟩ : syracuseStep 8686217 = 6514663) B6514663
theorem B23163245 : Blo 2033435 23163245 := bstep (se 3 (by rfl) ⟨4343108, by rfl⟩ : syracuseStep 23163245 = 8686217) B8686217
theorem B15442163 : Blo 2033435 15442163 := bstep (se 1 (by rfl) ⟨11581622, by rfl⟩ : syracuseStep 15442163 = 23163245) B23163245
theorem B10294775 : Blo 2033435 10294775 := bstep (se 1 (by rfl) ⟨7721081, by rfl⟩ : syracuseStep 10294775 = 15442163) B15442163
theorem B6863183 : Blo 2033435 6863183 := bstep (se 1 (by rfl) ⟨5147387, by rfl⟩ : syracuseStep 6863183 = 10294775) B10294775
theorem B4575455 : Blo 2033435 4575455 := bstep (se 1 (by rfl) ⟨3431591, by rfl⟩ : syracuseStep 4575455 = 6863183) B6863183
theorem B3050303 : Blo 2033435 3050303 := bstep (se 1 (by rfl) ⟨2287727, by rfl⟩ : syracuseStep 3050303 = 4575455) B4575455
theorem B2033535 : Blo 2033435 2033535 := bstep (se 1 (by rfl) ⟨1525151, by rfl⟩ : syracuseStep 2033535 = 3050303) B3050303
theorem B3050309 : Blo 2033435 3050309 := bbase (se 4 (by rfl) ⟨285966, by rfl⟩ : syracuseStep 3050309 = 571933) (by norm_num)
theorem B2033539 : Blo 2033435 2033539 := bstep (se 1 (by rfl) ⟨1525154, by rfl⟩ : syracuseStep 2033539 = 3050309) B3050309
theorem B3431605 : Blo 2033435 3431605 := bbase (se 5 (by rfl) ⟨160856, by rfl⟩ : syracuseStep 3431605 = 321713) (by norm_num)
theorem B4575473 : Blo 2033435 4575473 := bstep (se 2 (by rfl) ⟨1715802, by rfl⟩ : syracuseStep 4575473 = 3431605) B3431605
theorem B3050315 : Blo 2033435 3050315 := bstep (se 1 (by rfl) ⟨2287736, by rfl⟩ : syracuseStep 3050315 = 4575473) B4575473
theorem B2033543 : Blo 2033435 2033543 := bstep (se 1 (by rfl) ⟨1525157, by rfl⟩ : syracuseStep 2033543 = 3050315) B3050315
theorem B2287741 : Blo 2033435 2287741 := bbase (se 3 (by rfl) ⟨428951, by rfl⟩ : syracuseStep 2287741 = 857903) (by norm_num)
theorem B3050321 : Blo 2033435 3050321 := bstep (se 2 (by rfl) ⟨1143870, by rfl⟩ : syracuseStep 3050321 = 2287741) B2287741
theorem B2033547 : Blo 2033435 2033547 := bstep (se 1 (by rfl) ⟨1525160, by rfl⟩ : syracuseStep 2033547 = 3050321) B3050321
theorem B6863237 : Blo 2033435 6863237 := bbase (se 4 (by rfl) ⟨643428, by rfl⟩ : syracuseStep 6863237 = 1286857) (by norm_num)
theorem B4575491 : Blo 2033435 4575491 := bstep (se 1 (by rfl) ⟨3431618, by rfl⟩ : syracuseStep 4575491 = 6863237) B6863237
theorem B3050327 : Blo 2033435 3050327 := bstep (se 1 (by rfl) ⟨2287745, by rfl⟩ : syracuseStep 3050327 = 4575491) B4575491
theorem B2033551 : Blo 2033435 2033551 := bstep (se 1 (by rfl) ⟨1525163, by rfl⟩ : syracuseStep 2033551 = 3050327) B3050327
theorem B3050333 : Blo 2033435 3050333 := bbase (se 3 (by rfl) ⟨571937, by rfl⟩ : syracuseStep 3050333 = 1143875) (by norm_num)
theorem B2033555 : Blo 2033435 2033555 := bstep (se 1 (by rfl) ⟨1525166, by rfl⟩ : syracuseStep 2033555 = 3050333) B3050333
theorem B4575509 : Blo 2033435 4575509 := bbase (se 6 (by rfl) ⟨107238, by rfl⟩ : syracuseStep 4575509 = 214477) (by norm_num)
theorem B3050339 : Blo 2033435 3050339 := bstep (se 1 (by rfl) ⟨2287754, by rfl⟩ : syracuseStep 3050339 = 4575509) B4575509
theorem B2033559 : Blo 2033435 2033559 := bstep (se 1 (by rfl) ⟨1525169, by rfl⟩ : syracuseStep 2033559 = 3050339) B3050339
theorem B7721189 : Blo 2033435 7721189 := bbase (se 4 (by rfl) ⟨723861, by rfl⟩ : syracuseStep 7721189 = 1447723) (by norm_num)
theorem B5147459 : Blo 2033435 5147459 := bstep (se 1 (by rfl) ⟨3860594, by rfl⟩ : syracuseStep 5147459 = 7721189) B7721189
theorem B3431639 : Blo 2033435 3431639 := bstep (se 1 (by rfl) ⟨2573729, by rfl⟩ : syracuseStep 3431639 = 5147459) B5147459
theorem B2287759 : Blo 2033435 2287759 := bstep (se 1 (by rfl) ⟨1715819, by rfl⟩ : syracuseStep 2287759 = 3431639) B3431639
theorem B3050345 : Blo 2033435 3050345 := bstep (se 2 (by rfl) ⟨1143879, by rfl⟩ : syracuseStep 3050345 = 2287759) B2287759
theorem B2033563 : Blo 2033435 2033563 := bstep (se 1 (by rfl) ⟨1525172, by rfl⟩ : syracuseStep 2033563 = 3050345) B3050345
theorem B8245253 : Blo 2033435 8245253 := bbase (se 4 (by rfl) ⟨772992, by rfl⟩ : syracuseStep 8245253 = 1545985) (by norm_num)
theorem B5496835 : Blo 2033435 5496835 := bstep (se 1 (by rfl) ⟨4122626, by rfl⟩ : syracuseStep 5496835 = 8245253) B8245253
theorem B7329113 : Blo 2033435 7329113 := bstep (se 2 (by rfl) ⟨2748417, by rfl⟩ : syracuseStep 7329113 = 5496835) B5496835
theorem B4886075 : Blo 2033435 4886075 := bstep (se 1 (by rfl) ⟨3664556, by rfl⟩ : syracuseStep 4886075 = 7329113) B7329113
theorem B3257383 : Blo 2033435 3257383 := bstep (se 1 (by rfl) ⟨2443037, by rfl⟩ : syracuseStep 3257383 = 4886075) B4886075
theorem B4343177 : Blo 2033435 4343177 := bstep (se 2 (by rfl) ⟨1628691, by rfl⟩ : syracuseStep 4343177 = 3257383) B3257383
theorem B11581805 : Blo 2033435 11581805 := bstep (se 3 (by rfl) ⟨2171588, by rfl⟩ : syracuseStep 11581805 = 4343177) B4343177
theorem B7721203 : Blo 2033435 7721203 := bstep (se 1 (by rfl) ⟨5790902, by rfl⟩ : syracuseStep 7721203 = 11581805) B11581805
theorem B10294937 : Blo 2033435 10294937 := bstep (se 2 (by rfl) ⟨3860601, by rfl⟩ : syracuseStep 10294937 = 7721203) B7721203
theorem B6863291 : Blo 2033435 6863291 := bstep (se 1 (by rfl) ⟨5147468, by rfl⟩ : syracuseStep 6863291 = 10294937) B10294937
theorem B4575527 : Blo 2033435 4575527 := bstep (se 1 (by rfl) ⟨3431645, by rfl⟩ : syracuseStep 4575527 = 6863291) B6863291
theorem B3050351 : Blo 2033435 3050351 := bstep (se 1 (by rfl) ⟨2287763, by rfl⟩ : syracuseStep 3050351 = 4575527) B4575527
theorem B2033567 : Blo 2033435 2033567 := bstep (se 1 (by rfl) ⟨1525175, by rfl⟩ : syracuseStep 2033567 = 3050351) B3050351
theorem B3050357 : Blo 2033435 3050357 := bbase (se 5 (by rfl) ⟨142985, by rfl⟩ : syracuseStep 3050357 = 285971) (by norm_num)
theorem B2033571 : Blo 2033435 2033571 := bstep (se 1 (by rfl) ⟨1525178, by rfl⟩ : syracuseStep 2033571 = 3050357) B3050357
theorem B2608861 : Blo 2033435 2608861 := bbase (se 3 (by rfl) ⟨489161, by rfl⟩ : syracuseStep 2608861 = 978323) (by norm_num)
theorem B3478481 : Blo 2033435 3478481 := bstep (se 2 (by rfl) ⟨1304430, by rfl⟩ : syracuseStep 3478481 = 2608861) B2608861
theorem B2318987 : Blo 2033435 2318987 := bstep (se 1 (by rfl) ⟨1739240, by rfl⟩ : syracuseStep 2318987 = 3478481) B3478481
theorem B6183965 : Blo 2033435 6183965 := bstep (se 3 (by rfl) ⟨1159493, by rfl⟩ : syracuseStep 6183965 = 2318987) B2318987
theorem B16490573 : Blo 2033435 16490573 := bstep (se 3 (by rfl) ⟨3091982, by rfl⟩ : syracuseStep 16490573 = 6183965) B6183965
theorem B10993715 : Blo 2033435 10993715 := bstep (se 1 (by rfl) ⟨8245286, by rfl⟩ : syracuseStep 10993715 = 16490573) B16490573
theorem B7329143 : Blo 2033435 7329143 := bstep (se 1 (by rfl) ⟨5496857, by rfl⟩ : syracuseStep 7329143 = 10993715) B10993715
theorem B4886095 : Blo 2033435 4886095 := bstep (se 1 (by rfl) ⟨3664571, by rfl⟩ : syracuseStep 4886095 = 7329143) B7329143
theorem B6514793 : Blo 2033435 6514793 := bstep (se 2 (by rfl) ⟨2443047, by rfl⟩ : syracuseStep 6514793 = 4886095) B4886095
theorem B4343195 : Blo 2033435 4343195 := bstep (se 1 (by rfl) ⟨3257396, by rfl⟩ : syracuseStep 4343195 = 6514793) B6514793
theorem B2895463 : Blo 2033435 2895463 := bstep (se 1 (by rfl) ⟨2171597, by rfl⟩ : syracuseStep 2895463 = 4343195) B4343195
theorem B3860617 : Blo 2033435 3860617 := bstep (se 2 (by rfl) ⟨1447731, by rfl⟩ : syracuseStep 3860617 = 2895463) B2895463
theorem B5147489 : Blo 2033435 5147489 := bstep (se 2 (by rfl) ⟨1930308, by rfl⟩ : syracuseStep 5147489 = 3860617) B3860617
theorem B3431659 : Blo 2033435 3431659 := bstep (se 1 (by rfl) ⟨2573744, by rfl⟩ : syracuseStep 3431659 = 5147489) B5147489
theorem B4575545 : Blo 2033435 4575545 := bstep (se 2 (by rfl) ⟨1715829, by rfl⟩ : syracuseStep 4575545 = 3431659) B3431659
theorem B3050363 : Blo 2033435 3050363 := bstep (se 1 (by rfl) ⟨2287772, by rfl⟩ : syracuseStep 3050363 = 4575545) B4575545
theorem B2033575 : Blo 2033435 2033575 := bstep (se 1 (by rfl) ⟨1525181, by rfl⟩ : syracuseStep 2033575 = 3050363) B3050363
theorem B2287777 : Blo 2033435 2287777 := bbase (se 2 (by rfl) ⟨857916, by rfl⟩ : syracuseStep 2287777 = 1715833) (by norm_num)
theorem B3050369 : Blo 2033435 3050369 := bstep (se 2 (by rfl) ⟨1143888, by rfl⟩ : syracuseStep 3050369 = 2287777) B2287777
theorem B2033579 : Blo 2033435 2033579 := bstep (se 1 (by rfl) ⟨1525184, by rfl⟩ : syracuseStep 2033579 = 3050369) B3050369
theorem B5147509 : Blo 2033435 5147509 := bbase (se 5 (by rfl) ⟨241289, by rfl⟩ : syracuseStep 5147509 = 482579) (by norm_num)
theorem B6863345 : Blo 2033435 6863345 := bstep (se 2 (by rfl) ⟨2573754, by rfl⟩ : syracuseStep 6863345 = 5147509) B5147509
theorem B4575563 : Blo 2033435 4575563 := bstep (se 1 (by rfl) ⟨3431672, by rfl⟩ : syracuseStep 4575563 = 6863345) B6863345
theorem B3050375 : Blo 2033435 3050375 := bstep (se 1 (by rfl) ⟨2287781, by rfl⟩ : syracuseStep 3050375 = 4575563) B4575563
theorem B2033583 : Blo 2033435 2033583 := bstep (se 1 (by rfl) ⟨1525187, by rfl⟩ : syracuseStep 2033583 = 3050375) B3050375
theorem B3050381 : Blo 2033435 3050381 := bbase (se 3 (by rfl) ⟨571946, by rfl⟩ : syracuseStep 3050381 = 1143893) (by norm_num)
theorem B2033587 : Blo 2033435 2033587 := bstep (se 1 (by rfl) ⟨1525190, by rfl⟩ : syracuseStep 2033587 = 3050381) B3050381
theorem B4575581 : Blo 2033435 4575581 := bbase (se 3 (by rfl) ⟨857921, by rfl⟩ : syracuseStep 4575581 = 1715843) (by norm_num)
theorem B3050387 : Blo 2033435 3050387 := bstep (se 1 (by rfl) ⟨2287790, by rfl⟩ : syracuseStep 3050387 = 4575581) B4575581
theorem B2033591 : Blo 2033435 2033591 := bstep (se 1 (by rfl) ⟨1525193, by rfl⟩ : syracuseStep 2033591 = 3050387) B3050387
theorem B3431693 : Blo 2033435 3431693 := bbase (se 3 (by rfl) ⟨643442, by rfl⟩ : syracuseStep 3431693 = 1286885) (by norm_num)
theorem B2287795 : Blo 2033435 2287795 := bstep (se 1 (by rfl) ⟨1715846, by rfl⟩ : syracuseStep 2287795 = 3431693) B3431693
theorem B3050393 : Blo 2033435 3050393 := bstep (se 2 (by rfl) ⟨1143897, by rfl⟩ : syracuseStep 3050393 = 2287795) B2287795
theorem B2033595 : Blo 2033435 2033595 := bstep (se 1 (by rfl) ⟨1525196, by rfl⟩ : syracuseStep 2033595 = 3050393) B3050393
theorem B17372981 : Blo 2033435 17372981 := bbase (se 5 (by rfl) ⟨814358, by rfl⟩ : syracuseStep 17372981 = 1628717) (by norm_num)
theorem B11581987 : Blo 2033435 11581987 := bstep (se 1 (by rfl) ⟨8686490, by rfl⟩ : syracuseStep 11581987 = 17372981) B17372981
theorem B15442649 : Blo 2033435 15442649 := bstep (se 2 (by rfl) ⟨5790993, by rfl⟩ : syracuseStep 15442649 = 11581987) B11581987
theorem B10295099 : Blo 2033435 10295099 := bstep (se 1 (by rfl) ⟨7721324, by rfl⟩ : syracuseStep 10295099 = 15442649) B15442649
theorem B6863399 : Blo 2033435 6863399 := bstep (se 1 (by rfl) ⟨5147549, by rfl⟩ : syracuseStep 6863399 = 10295099) B10295099
theorem B4575599 : Blo 2033435 4575599 := bstep (se 1 (by rfl) ⟨3431699, by rfl⟩ : syracuseStep 4575599 = 6863399) B6863399
theorem B3050399 : Blo 2033435 3050399 := bstep (se 1 (by rfl) ⟨2287799, by rfl⟩ : syracuseStep 3050399 = 4575599) B4575599
theorem B2033599 : Blo 2033435 2033599 := bstep (se 1 (by rfl) ⟨1525199, by rfl⟩ : syracuseStep 2033599 = 3050399) B3050399
theorem B3050405 : Blo 2033435 3050405 := bbase (se 4 (by rfl) ⟨285975, by rfl⟩ : syracuseStep 3050405 = 571951) (by norm_num)
theorem B2033603 : Blo 2033435 2033603 := bstep (se 1 (by rfl) ⟨1525202, by rfl⟩ : syracuseStep 2033603 = 3050405) B3050405
theorem B2573785 : Blo 2033435 2573785 := bbase (se 2 (by rfl) ⟨965169, by rfl⟩ : syracuseStep 2573785 = 1930339) (by norm_num)
theorem B3431713 : Blo 2033435 3431713 := bstep (se 2 (by rfl) ⟨1286892, by rfl⟩ : syracuseStep 3431713 = 2573785) B2573785
theorem B4575617 : Blo 2033435 4575617 := bstep (se 2 (by rfl) ⟨1715856, by rfl⟩ : syracuseStep 4575617 = 3431713) B3431713
theorem B3050411 : Blo 2033435 3050411 := bstep (se 1 (by rfl) ⟨2287808, by rfl⟩ : syracuseStep 3050411 = 4575617) B4575617
theorem B2033607 : Blo 2033435 2033607 := bstep (se 1 (by rfl) ⟨1525205, by rfl⟩ : syracuseStep 2033607 = 3050411) B3050411
theorem B2287813 : Blo 2033435 2287813 := bbase (se 4 (by rfl) ⟨214482, by rfl⟩ : syracuseStep 2287813 = 428965) (by norm_num)
theorem B3050417 : Blo 2033435 3050417 := bstep (se 2 (by rfl) ⟨1143906, by rfl⟩ : syracuseStep 3050417 = 2287813) B2287813
theorem B2033611 : Blo 2033435 2033611 := bstep (se 1 (by rfl) ⟨1525208, by rfl⟩ : syracuseStep 2033611 = 3050417) B3050417
theorem B3860693 : Blo 2033435 3860693 := bbase (se 7 (by rfl) ⟨45242, by rfl⟩ : syracuseStep 3860693 = 90485) (by norm_num)
theorem B2573795 : Blo 2033435 2573795 := bstep (se 1 (by rfl) ⟨1930346, by rfl⟩ : syracuseStep 2573795 = 3860693) B3860693
theorem B6863453 : Blo 2033435 6863453 := bstep (se 3 (by rfl) ⟨1286897, by rfl⟩ : syracuseStep 6863453 = 2573795) B2573795
theorem B4575635 : Blo 2033435 4575635 := bstep (se 1 (by rfl) ⟨3431726, by rfl⟩ : syracuseStep 4575635 = 6863453) B6863453
theorem B3050423 : Blo 2033435 3050423 := bstep (se 1 (by rfl) ⟨2287817, by rfl⟩ : syracuseStep 3050423 = 4575635) B4575635
theorem B2033615 : Blo 2033435 2033615 := bstep (se 1 (by rfl) ⟨1525211, by rfl⟩ : syracuseStep 2033615 = 3050423) B3050423
theorem B3050429 : Blo 2033435 3050429 := bbase (se 3 (by rfl) ⟨571955, by rfl⟩ : syracuseStep 3050429 = 1143911) (by norm_num)
theorem B2033619 : Blo 2033435 2033619 := bstep (se 1 (by rfl) ⟨1525214, by rfl⟩ : syracuseStep 2033619 = 3050429) B3050429
theorem B4575653 : Blo 2033435 4575653 := bbase (se 4 (by rfl) ⟨428967, by rfl⟩ : syracuseStep 4575653 = 857935) (by norm_num)
theorem B3050435 : Blo 2033435 3050435 := bstep (se 1 (by rfl) ⟨2287826, by rfl⟩ : syracuseStep 3050435 = 4575653) B4575653
theorem B2033623 : Blo 2033435 2033623 := bstep (se 1 (by rfl) ⟨1525217, by rfl⟩ : syracuseStep 2033623 = 3050435) B3050435
theorem B5147621 : Blo 2033435 5147621 := bbase (se 4 (by rfl) ⟨482589, by rfl⟩ : syracuseStep 5147621 = 965179) (by norm_num)
theorem B3431747 : Blo 2033435 3431747 := bstep (se 1 (by rfl) ⟨2573810, by rfl⟩ : syracuseStep 3431747 = 5147621) B5147621
theorem B2287831 : Blo 2033435 2287831 := bstep (se 1 (by rfl) ⟨1715873, by rfl⟩ : syracuseStep 2287831 = 3431747) B3431747
theorem B3050441 : Blo 2033435 3050441 := bstep (se 2 (by rfl) ⟨1143915, by rfl⟩ : syracuseStep 3050441 = 2287831) B2287831
theorem B2033627 : Blo 2033435 2033627 := bstep (se 1 (by rfl) ⟨1525220, by rfl⟩ : syracuseStep 2033627 = 3050441) B3050441
theorem B2171657 : Blo 2033435 2171657 := bbase (se 2 (by rfl) ⟨814371, by rfl⟩ : syracuseStep 2171657 = 1628743) (by norm_num)
theorem B5791085 : Blo 2033435 5791085 := bstep (se 3 (by rfl) ⟨1085828, by rfl⟩ : syracuseStep 5791085 = 2171657) B2171657
theorem B3860723 : Blo 2033435 3860723 := bstep (se 1 (by rfl) ⟨2895542, by rfl⟩ : syracuseStep 3860723 = 5791085) B5791085
theorem B10295261 : Blo 2033435 10295261 := bstep (se 3 (by rfl) ⟨1930361, by rfl⟩ : syracuseStep 10295261 = 3860723) B3860723
theorem B6863507 : Blo 2033435 6863507 := bstep (se 1 (by rfl) ⟨5147630, by rfl⟩ : syracuseStep 6863507 = 10295261) B10295261
theorem B4575671 : Blo 2033435 4575671 := bstep (se 1 (by rfl) ⟨3431753, by rfl⟩ : syracuseStep 4575671 = 6863507) B6863507
theorem B3050447 : Blo 2033435 3050447 := bstep (se 1 (by rfl) ⟨2287835, by rfl⟩ : syracuseStep 3050447 = 4575671) B4575671
theorem B2033631 : Blo 2033435 2033631 := bstep (se 1 (by rfl) ⟨1525223, by rfl⟩ : syracuseStep 2033631 = 3050447) B3050447
theorem B3050453 : Blo 2033435 3050453 := bbase (se 7 (by rfl) ⟨35747, by rfl⟩ : syracuseStep 3050453 = 71495) (by norm_num)
theorem B2033635 : Blo 2033435 2033635 := bstep (se 1 (by rfl) ⟨1525226, by rfl⟩ : syracuseStep 2033635 = 3050453) B3050453
theorem B7721477 : Blo 2033435 7721477 := bbase (se 4 (by rfl) ⟨723888, by rfl⟩ : syracuseStep 7721477 = 1447777) (by norm_num)
theorem B5147651 : Blo 2033435 5147651 := bstep (se 1 (by rfl) ⟨3860738, by rfl⟩ : syracuseStep 5147651 = 7721477) B7721477
theorem B3431767 : Blo 2033435 3431767 := bstep (se 1 (by rfl) ⟨2573825, by rfl⟩ : syracuseStep 3431767 = 5147651) B5147651
theorem B4575689 : Blo 2033435 4575689 := bstep (se 2 (by rfl) ⟨1715883, by rfl⟩ : syracuseStep 4575689 = 3431767) B3431767
theorem B3050459 : Blo 2033435 3050459 := bstep (se 1 (by rfl) ⟨2287844, by rfl⟩ : syracuseStep 3050459 = 4575689) B4575689
theorem B2033639 : Blo 2033435 2033639 := bstep (se 1 (by rfl) ⟨1525229, by rfl⟩ : syracuseStep 2033639 = 3050459) B3050459
theorem B2287849 : Blo 2033435 2287849 := bbase (se 2 (by rfl) ⟨857943, by rfl⟩ : syracuseStep 2287849 = 1715887) (by norm_num)
theorem B3050465 : Blo 2033435 3050465 := bstep (se 2 (by rfl) ⟨1143924, by rfl⟩ : syracuseStep 3050465 = 2287849) B2287849
theorem B2033643 : Blo 2033435 2033643 := bstep (se 1 (by rfl) ⟨1525232, by rfl⟩ : syracuseStep 2033643 = 3050465) B3050465
theorem B11582261 : Blo 2033435 11582261 := bbase (se 5 (by rfl) ⟨542918, by rfl⟩ : syracuseStep 11582261 = 1085837) (by norm_num)
theorem B7721507 : Blo 2033435 7721507 := bstep (se 1 (by rfl) ⟨5791130, by rfl⟩ : syracuseStep 7721507 = 11582261) B11582261
theorem B5147671 : Blo 2033435 5147671 := bstep (se 1 (by rfl) ⟨3860753, by rfl⟩ : syracuseStep 5147671 = 7721507) B7721507
theorem B6863561 : Blo 2033435 6863561 := bstep (se 2 (by rfl) ⟨2573835, by rfl⟩ : syracuseStep 6863561 = 5147671) B5147671
theorem B4575707 : Blo 2033435 4575707 := bstep (se 1 (by rfl) ⟨3431780, by rfl⟩ : syracuseStep 4575707 = 6863561) B6863561
theorem B3050471 : Blo 2033435 3050471 := bstep (se 1 (by rfl) ⟨2287853, by rfl⟩ : syracuseStep 3050471 = 4575707) B4575707
theorem B2033647 : Blo 2033435 2033647 := bstep (se 1 (by rfl) ⟨1525235, by rfl⟩ : syracuseStep 2033647 = 3050471) B3050471
theorem B3050477 : Blo 2033435 3050477 := bbase (se 3 (by rfl) ⟨571964, by rfl⟩ : syracuseStep 3050477 = 1143929) (by norm_num)
theorem B2033651 : Blo 2033435 2033651 := bstep (se 1 (by rfl) ⟨1525238, by rfl⟩ : syracuseStep 2033651 = 3050477) B3050477
theorem B4575725 : Blo 2033435 4575725 := bbase (se 3 (by rfl) ⟨857948, by rfl⟩ : syracuseStep 4575725 = 1715897) (by norm_num)
theorem B3050483 : Blo 2033435 3050483 := bstep (se 1 (by rfl) ⟨2287862, by rfl⟩ : syracuseStep 3050483 = 4575725) B4575725
theorem B2033655 : Blo 2033435 2033655 := bstep (se 1 (by rfl) ⟨1525241, by rfl⟩ : syracuseStep 2033655 = 3050483) B3050483
theorem B10435877 : Blo 2033435 10435877 := bbase (se 4 (by rfl) ⟨978363, by rfl⟩ : syracuseStep 10435877 = 1956727) (by norm_num)
theorem B6957251 : Blo 2033435 6957251 := bstep (se 1 (by rfl) ⟨5217938, by rfl⟩ : syracuseStep 6957251 = 10435877) B10435877
theorem B4638167 : Blo 2033435 4638167 := bstep (se 1 (by rfl) ⟨3478625, by rfl⟩ : syracuseStep 4638167 = 6957251) B6957251
theorem B3092111 : Blo 2033435 3092111 := bstep (se 1 (by rfl) ⟨2319083, by rfl⟩ : syracuseStep 3092111 = 4638167) B4638167
theorem B2061407 : Blo 2033435 2061407 := bstep (se 1 (by rfl) ⟨1546055, by rfl⟩ : syracuseStep 2061407 = 3092111) B3092111
theorem B5497085 : Blo 2033435 5497085 := bstep (se 3 (by rfl) ⟨1030703, by rfl⟩ : syracuseStep 5497085 = 2061407) B2061407
theorem B14658893 : Blo 2033435 14658893 := bstep (se 3 (by rfl) ⟨2748542, by rfl⟩ : syracuseStep 14658893 = 5497085) B5497085
theorem B9772595 : Blo 2033435 9772595 := bstep (se 1 (by rfl) ⟨7329446, by rfl⟩ : syracuseStep 9772595 = 14658893) B14658893
theorem B6515063 : Blo 2033435 6515063 := bstep (se 1 (by rfl) ⟨4886297, by rfl⟩ : syracuseStep 6515063 = 9772595) B9772595
theorem B4343375 : Blo 2033435 4343375 := bstep (se 1 (by rfl) ⟨3257531, by rfl⟩ : syracuseStep 4343375 = 6515063) B6515063
theorem B2895583 : Blo 2033435 2895583 := bstep (se 1 (by rfl) ⟨2171687, by rfl⟩ : syracuseStep 2895583 = 4343375) B4343375
theorem B3860777 : Blo 2033435 3860777 := bstep (se 2 (by rfl) ⟨1447791, by rfl⟩ : syracuseStep 3860777 = 2895583) B2895583
theorem B2573851 : Blo 2033435 2573851 := bstep (se 1 (by rfl) ⟨1930388, by rfl⟩ : syracuseStep 2573851 = 3860777) B3860777
theorem B3431801 : Blo 2033435 3431801 := bstep (se 2 (by rfl) ⟨1286925, by rfl⟩ : syracuseStep 3431801 = 2573851) B2573851
theorem B2287867 : Blo 2033435 2287867 := bstep (se 1 (by rfl) ⟨1715900, by rfl⟩ : syracuseStep 2287867 = 3431801) B3431801
theorem B3050489 : Blo 2033435 3050489 := bstep (se 2 (by rfl) ⟨1143933, by rfl⟩ : syracuseStep 3050489 = 2287867) B2287867
theorem B2033659 : Blo 2033435 2033659 := bstep (se 1 (by rfl) ⟨1525244, by rfl⟩ : syracuseStep 2033659 = 3050489) B3050489
theorem B13914517 : Blo 2033435 13914517 := bbase (se 6 (by rfl) ⟨326121, by rfl⟩ : syracuseStep 13914517 = 652243) (by norm_num)
theorem B18552689 : Blo 2033435 18552689 := bstep (se 2 (by rfl) ⟨6957258, by rfl⟩ : syracuseStep 18552689 = 13914517) B13914517
theorem B12368459 : Blo 2033435 12368459 := bstep (se 1 (by rfl) ⟨9276344, by rfl⟩ : syracuseStep 12368459 = 18552689) B18552689
theorem B32982557 : Blo 2033435 32982557 := bstep (se 3 (by rfl) ⟨6184229, by rfl⟩ : syracuseStep 32982557 = 12368459) B12368459
theorem B87953485 : Blo 2033435 87953485 := bstep (se 3 (by rfl) ⟨16491278, by rfl⟩ : syracuseStep 87953485 = 32982557) B32982557
theorem B117271313 : Blo 2033435 117271313 := bstep (se 2 (by rfl) ⟨43976742, by rfl⟩ : syracuseStep 117271313 = 87953485) B87953485
theorem B78180875 : Blo 2033435 78180875 := bstep (se 1 (by rfl) ⟨58635656, by rfl⟩ : syracuseStep 78180875 = 117271313) B117271313
theorem B52120583 : Blo 2033435 52120583 := bstep (se 1 (by rfl) ⟨39090437, by rfl⟩ : syracuseStep 52120583 = 78180875) B78180875
theorem B34747055 : Blo 2033435 34747055 := bstep (se 1 (by rfl) ⟨26060291, by rfl⟩ : syracuseStep 34747055 = 52120583) B52120583
theorem B23164703 : Blo 2033435 23164703 := bstep (se 1 (by rfl) ⟨17373527, by rfl⟩ : syracuseStep 23164703 = 34747055) B34747055
theorem B15443135 : Blo 2033435 15443135 := bstep (se 1 (by rfl) ⟨11582351, by rfl⟩ : syracuseStep 15443135 = 23164703) B23164703
theorem B10295423 : Blo 2033435 10295423 := bstep (se 1 (by rfl) ⟨7721567, by rfl⟩ : syracuseStep 10295423 = 15443135) B15443135
theorem B6863615 : Blo 2033435 6863615 := bstep (se 1 (by rfl) ⟨5147711, by rfl⟩ : syracuseStep 6863615 = 10295423) B10295423
theorem B4575743 : Blo 2033435 4575743 := bstep (se 1 (by rfl) ⟨3431807, by rfl⟩ : syracuseStep 4575743 = 6863615) B6863615
theorem B3050495 : Blo 2033435 3050495 := bstep (se 1 (by rfl) ⟨2287871, by rfl⟩ : syracuseStep 3050495 = 4575743) B4575743
theorem B2033663 : Blo 2033435 2033663 := bstep (se 1 (by rfl) ⟨1525247, by rfl⟩ : syracuseStep 2033663 = 3050495) B3050495
theorem B3050501 : Blo 2033435 3050501 := bbase (se 4 (by rfl) ⟨285984, by rfl⟩ : syracuseStep 3050501 = 571969) (by norm_num)
theorem B2033667 : Blo 2033435 2033667 := bstep (se 1 (by rfl) ⟨1525250, by rfl⟩ : syracuseStep 2033667 = 3050501) B3050501
theorem B3431821 : Blo 2033435 3431821 := bbase (se 3 (by rfl) ⟨643466, by rfl⟩ : syracuseStep 3431821 = 1286933) (by norm_num)
theorem B4575761 : Blo 2033435 4575761 := bstep (se 2 (by rfl) ⟨1715910, by rfl⟩ : syracuseStep 4575761 = 3431821) B3431821
theorem B3050507 : Blo 2033435 3050507 := bstep (se 1 (by rfl) ⟨2287880, by rfl⟩ : syracuseStep 3050507 = 4575761) B4575761
theorem B2033671 : Blo 2033435 2033671 := bstep (se 1 (by rfl) ⟨1525253, by rfl⟩ : syracuseStep 2033671 = 3050507) B3050507
theorem B2287885 : Blo 2033435 2287885 := bbase (se 3 (by rfl) ⟨428978, by rfl⟩ : syracuseStep 2287885 = 857957) (by norm_num)
theorem B3050513 : Blo 2033435 3050513 := bstep (se 2 (by rfl) ⟨1143942, by rfl⟩ : syracuseStep 3050513 = 2287885) B2287885
theorem B2033675 : Blo 2033435 2033675 := bstep (se 1 (by rfl) ⟨1525256, by rfl⟩ : syracuseStep 2033675 = 3050513) B3050513
theorem B6863669 : Blo 2033435 6863669 := bbase (se 5 (by rfl) ⟨321734, by rfl⟩ : syracuseStep 6863669 = 643469) (by norm_num)
theorem B4575779 : Blo 2033435 4575779 := bstep (se 1 (by rfl) ⟨3431834, by rfl⟩ : syracuseStep 4575779 = 6863669) B6863669
theorem B3050519 : Blo 2033435 3050519 := bstep (se 1 (by rfl) ⟨2287889, by rfl⟩ : syracuseStep 3050519 = 4575779) B4575779
theorem B2033679 : Blo 2033435 2033679 := bstep (se 1 (by rfl) ⟨1525259, by rfl⟩ : syracuseStep 2033679 = 3050519) B3050519
theorem B3050525 : Blo 2033435 3050525 := bbase (se 3 (by rfl) ⟨571973, by rfl⟩ : syracuseStep 3050525 = 1143947) (by norm_num)
theorem B2033683 : Blo 2033435 2033683 := bstep (se 1 (by rfl) ⟨1525262, by rfl⟩ : syracuseStep 2033683 = 3050525) B3050525
theorem B4575797 : Blo 2033435 4575797 := bbase (se 5 (by rfl) ⟨214490, by rfl⟩ : syracuseStep 4575797 = 428981) (by norm_num)
theorem B3050531 : Blo 2033435 3050531 := bstep (se 1 (by rfl) ⟨2287898, by rfl⟩ : syracuseStep 3050531 = 4575797) B4575797
theorem B2033687 : Blo 2033435 2033687 := bstep (se 1 (by rfl) ⟨1525265, by rfl⟩ : syracuseStep 2033687 = 3050531) B3050531
theorem B8686885 : Blo 2033435 8686885 := bbase (se 4 (by rfl) ⟨814395, by rfl⟩ : syracuseStep 8686885 = 1628791) (by norm_num)
theorem B11582513 : Blo 2033435 11582513 := bstep (se 2 (by rfl) ⟨4343442, by rfl⟩ : syracuseStep 11582513 = 8686885) B8686885
theorem B7721675 : Blo 2033435 7721675 := bstep (se 1 (by rfl) ⟨5791256, by rfl⟩ : syracuseStep 7721675 = 11582513) B11582513
theorem B5147783 : Blo 2033435 5147783 := bstep (se 1 (by rfl) ⟨3860837, by rfl⟩ : syracuseStep 5147783 = 7721675) B7721675
theorem B3431855 : Blo 2033435 3431855 := bstep (se 1 (by rfl) ⟨2573891, by rfl⟩ : syracuseStep 3431855 = 5147783) B5147783
theorem B2287903 : Blo 2033435 2287903 := bstep (se 1 (by rfl) ⟨1715927, by rfl⟩ : syracuseStep 2287903 = 3431855) B3431855
theorem B3050537 : Blo 2033435 3050537 := bstep (se 2 (by rfl) ⟨1143951, by rfl⟩ : syracuseStep 3050537 = 2287903) B2287903
theorem B2033691 : Blo 2033435 2033691 := bstep (se 1 (by rfl) ⟨1525268, by rfl⟩ : syracuseStep 2033691 = 3050537) B3050537
theorem B8686901 : Blo 2033435 8686901 := bbase (se 5 (by rfl) ⟨407198, by rfl⟩ : syracuseStep 8686901 = 814397) (by norm_num)
theorem B5791267 : Blo 2033435 5791267 := bstep (se 1 (by rfl) ⟨4343450, by rfl⟩ : syracuseStep 5791267 = 8686901) B8686901
theorem B7721689 : Blo 2033435 7721689 := bstep (se 2 (by rfl) ⟨2895633, by rfl⟩ : syracuseStep 7721689 = 5791267) B5791267
theorem B10295585 : Blo 2033435 10295585 := bstep (se 2 (by rfl) ⟨3860844, by rfl⟩ : syracuseStep 10295585 = 7721689) B7721689
theorem B6863723 : Blo 2033435 6863723 := bstep (se 1 (by rfl) ⟨5147792, by rfl⟩ : syracuseStep 6863723 = 10295585) B10295585
theorem B4575815 : Blo 2033435 4575815 := bstep (se 1 (by rfl) ⟨3431861, by rfl⟩ : syracuseStep 4575815 = 6863723) B6863723
theorem B3050543 : Blo 2033435 3050543 := bstep (se 1 (by rfl) ⟨2287907, by rfl⟩ : syracuseStep 3050543 = 4575815) B4575815
theorem B2033695 : Blo 2033435 2033695 := bstep (se 1 (by rfl) ⟨1525271, by rfl⟩ : syracuseStep 2033695 = 3050543) B3050543
theorem B3050549 : Blo 2033435 3050549 := bbase (se 5 (by rfl) ⟨142994, by rfl⟩ : syracuseStep 3050549 = 285989) (by norm_num)
theorem B2033699 : Blo 2033435 2033699 := bstep (se 1 (by rfl) ⟨1525274, by rfl⟩ : syracuseStep 2033699 = 3050549) B3050549
theorem B5147813 : Blo 2033435 5147813 := bbase (se 4 (by rfl) ⟨482607, by rfl⟩ : syracuseStep 5147813 = 965215) (by norm_num)
theorem B3431875 : Blo 2033435 3431875 := bstep (se 1 (by rfl) ⟨2573906, by rfl⟩ : syracuseStep 3431875 = 5147813) B5147813
theorem B4575833 : Blo 2033435 4575833 := bstep (se 2 (by rfl) ⟨1715937, by rfl⟩ : syracuseStep 4575833 = 3431875) B3431875
theorem B3050555 : Blo 2033435 3050555 := bstep (se 1 (by rfl) ⟨2287916, by rfl⟩ : syracuseStep 3050555 = 4575833) B4575833
theorem B2033703 : Blo 2033435 2033703 := bstep (se 1 (by rfl) ⟨1525277, by rfl⟩ : syracuseStep 2033703 = 3050555) B3050555
theorem B2287921 : Blo 2033435 2287921 := bbase (se 2 (by rfl) ⟨857970, by rfl⟩ : syracuseStep 2287921 = 1715941) (by norm_num)
theorem B3050561 : Blo 2033435 3050561 := bstep (se 2 (by rfl) ⟨1143960, by rfl⟩ : syracuseStep 3050561 = 2287921) B2287921
theorem B2033707 : Blo 2033435 2033707 := bstep (se 1 (by rfl) ⟨1525280, by rfl⟩ : syracuseStep 2033707 = 3050561) B3050561
theorem B4343485 : Blo 2033435 4343485 := bbase (se 3 (by rfl) ⟨814403, by rfl⟩ : syracuseStep 4343485 = 1628807) (by norm_num)
theorem B5791313 : Blo 2033435 5791313 := bstep (se 2 (by rfl) ⟨2171742, by rfl⟩ : syracuseStep 5791313 = 4343485) B4343485
theorem B3860875 : Blo 2033435 3860875 := bstep (se 1 (by rfl) ⟨2895656, by rfl⟩ : syracuseStep 3860875 = 5791313) B5791313
theorem B5147833 : Blo 2033435 5147833 := bstep (se 2 (by rfl) ⟨1930437, by rfl⟩ : syracuseStep 5147833 = 3860875) B3860875
theorem B6863777 : Blo 2033435 6863777 := bstep (se 2 (by rfl) ⟨2573916, by rfl⟩ : syracuseStep 6863777 = 5147833) B5147833
theorem B4575851 : Blo 2033435 4575851 := bstep (se 1 (by rfl) ⟨3431888, by rfl⟩ : syracuseStep 4575851 = 6863777) B6863777
theorem B3050567 : Blo 2033435 3050567 := bstep (se 1 (by rfl) ⟨2287925, by rfl⟩ : syracuseStep 3050567 = 4575851) B4575851
theorem B2033711 : Blo 2033435 2033711 := bstep (se 1 (by rfl) ⟨1525283, by rfl⟩ : syracuseStep 2033711 = 3050567) B3050567
theorem B3050573 : Blo 2033435 3050573 := bbase (se 3 (by rfl) ⟨571982, by rfl⟩ : syracuseStep 3050573 = 1143965) (by norm_num)
theorem B2033715 : Blo 2033435 2033715 := bstep (se 1 (by rfl) ⟨1525286, by rfl⟩ : syracuseStep 2033715 = 3050573) B3050573
theorem B4575869 : Blo 2033435 4575869 := bbase (se 3 (by rfl) ⟨857975, by rfl⟩ : syracuseStep 4575869 = 1715951) (by norm_num)
theorem B3050579 : Blo 2033435 3050579 := bstep (se 1 (by rfl) ⟨2287934, by rfl⟩ : syracuseStep 3050579 = 4575869) B4575869
theorem B2033719 : Blo 2033435 2033719 := bstep (se 1 (by rfl) ⟨1525289, by rfl⟩ : syracuseStep 2033719 = 3050579) B3050579
theorem B3431909 : Blo 2033435 3431909 := bbase (se 4 (by rfl) ⟨321741, by rfl⟩ : syracuseStep 3431909 = 643483) (by norm_num)
theorem B2287939 : Blo 2033435 2287939 := bstep (se 1 (by rfl) ⟨1715954, by rfl⟩ : syracuseStep 2287939 = 3431909) B3431909
theorem B3050585 : Blo 2033435 3050585 := bstep (se 2 (by rfl) ⟨1143969, by rfl⟩ : syracuseStep 3050585 = 2287939) B2287939
theorem B2033723 : Blo 2033435 2033723 := bstep (se 1 (by rfl) ⟨1525292, by rfl⟩ : syracuseStep 2033723 = 3050585) B3050585
theorem B3092213 : Blo 2033435 3092213 := bbase (se 5 (by rfl) ⟨144947, by rfl⟩ : syracuseStep 3092213 = 289895) (by norm_num)
theorem B8245901 : Blo 2033435 8245901 := bstep (se 3 (by rfl) ⟨1546106, by rfl⟩ : syracuseStep 8245901 = 3092213) B3092213
theorem B21989069 : Blo 2033435 21989069 := bstep (se 3 (by rfl) ⟨4122950, by rfl⟩ : syracuseStep 21989069 = 8245901) B8245901
theorem B14659379 : Blo 2033435 14659379 := bstep (se 1 (by rfl) ⟨10994534, by rfl⟩ : syracuseStep 14659379 = 21989069) B21989069
theorem B9772919 : Blo 2033435 9772919 := bstep (se 1 (by rfl) ⟨7329689, by rfl⟩ : syracuseStep 9772919 = 14659379) B14659379
theorem B6515279 : Blo 2033435 6515279 := bstep (se 1 (by rfl) ⟨4886459, by rfl⟩ : syracuseStep 6515279 = 9772919) B9772919
theorem B4343519 : Blo 2033435 4343519 := bstep (se 1 (by rfl) ⟨3257639, by rfl⟩ : syracuseStep 4343519 = 6515279) B6515279
theorem B2895679 : Blo 2033435 2895679 := bstep (se 1 (by rfl) ⟨2171759, by rfl⟩ : syracuseStep 2895679 = 4343519) B4343519
theorem B15443621 : Blo 2033435 15443621 := bstep (se 4 (by rfl) ⟨1447839, by rfl⟩ : syracuseStep 15443621 = 2895679) B2895679
theorem B10295747 : Blo 2033435 10295747 := bstep (se 1 (by rfl) ⟨7721810, by rfl⟩ : syracuseStep 10295747 = 15443621) B15443621
theorem B6863831 : Blo 2033435 6863831 := bstep (se 1 (by rfl) ⟨5147873, by rfl⟩ : syracuseStep 6863831 = 10295747) B10295747
theorem B4575887 : Blo 2033435 4575887 := bstep (se 1 (by rfl) ⟨3431915, by rfl⟩ : syracuseStep 4575887 = 6863831) B6863831
theorem B3050591 : Blo 2033435 3050591 := bstep (se 1 (by rfl) ⟨2287943, by rfl⟩ : syracuseStep 3050591 = 4575887) B4575887
theorem B2033727 : Blo 2033435 2033727 := bstep (se 1 (by rfl) ⟨1525295, by rfl⟩ : syracuseStep 2033727 = 3050591) B3050591
theorem B3050597 : Blo 2033435 3050597 := bbase (se 4 (by rfl) ⟨285993, by rfl⟩ : syracuseStep 3050597 = 571987) (by norm_num)
theorem B2033731 : Blo 2033435 2033731 := bstep (se 1 (by rfl) ⟨1525298, by rfl⟩ : syracuseStep 2033731 = 3050597) B3050597
theorem B3257653 : Blo 2033435 3257653 := bbase (se 5 (by rfl) ⟨152702, by rfl⟩ : syracuseStep 3257653 = 305405) (by norm_num)
theorem B4343537 : Blo 2033435 4343537 := bstep (se 2 (by rfl) ⟨1628826, by rfl⟩ : syracuseStep 4343537 = 3257653) B3257653
theorem B2895691 : Blo 2033435 2895691 := bstep (se 1 (by rfl) ⟨2171768, by rfl⟩ : syracuseStep 2895691 = 4343537) B4343537
theorem B3860921 : Blo 2033435 3860921 := bstep (se 2 (by rfl) ⟨1447845, by rfl⟩ : syracuseStep 3860921 = 2895691) B2895691
theorem B2573947 : Blo 2033435 2573947 := bstep (se 1 (by rfl) ⟨1930460, by rfl⟩ : syracuseStep 2573947 = 3860921) B3860921
theorem B3431929 : Blo 2033435 3431929 := bstep (se 2 (by rfl) ⟨1286973, by rfl⟩ : syracuseStep 3431929 = 2573947) B2573947
theorem B4575905 : Blo 2033435 4575905 := bstep (se 2 (by rfl) ⟨1715964, by rfl⟩ : syracuseStep 4575905 = 3431929) B3431929
theorem B3050603 : Blo 2033435 3050603 := bstep (se 1 (by rfl) ⟨2287952, by rfl⟩ : syracuseStep 3050603 = 4575905) B4575905
theorem B2033735 : Blo 2033435 2033735 := bstep (se 1 (by rfl) ⟨1525301, by rfl⟩ : syracuseStep 2033735 = 3050603) B3050603
theorem B2287957 : Blo 2033435 2287957 := bbase (se 10 (by rfl) ⟨3351, by rfl⟩ : syracuseStep 2287957 = 6703) (by norm_num)
theorem B3050609 : Blo 2033435 3050609 := bstep (se 2 (by rfl) ⟨1143978, by rfl⟩ : syracuseStep 3050609 = 2287957) B2287957
theorem B2033739 : Blo 2033435 2033739 := bstep (se 1 (by rfl) ⟨1525304, by rfl⟩ : syracuseStep 2033739 = 3050609) B3050609
theorem B2573957 : Blo 2033435 2573957 := bbase (se 4 (by rfl) ⟨241308, by rfl⟩ : syracuseStep 2573957 = 482617) (by norm_num)
theorem B6863885 : Blo 2033435 6863885 := bstep (se 3 (by rfl) ⟨1286978, by rfl⟩ : syracuseStep 6863885 = 2573957) B2573957
theorem B4575923 : Blo 2033435 4575923 := bstep (se 1 (by rfl) ⟨3431942, by rfl⟩ : syracuseStep 4575923 = 6863885) B6863885
theorem B3050615 : Blo 2033435 3050615 := bstep (se 1 (by rfl) ⟨2287961, by rfl⟩ : syracuseStep 3050615 = 4575923) B4575923
theorem B2033743 : Blo 2033435 2033743 := bstep (se 1 (by rfl) ⟨1525307, by rfl⟩ : syracuseStep 2033743 = 3050615) B3050615
theorem B3050621 : Blo 2033435 3050621 := bbase (se 3 (by rfl) ⟨571991, by rfl⟩ : syracuseStep 3050621 = 1143983) (by norm_num)
theorem B2033747 : Blo 2033435 2033747 := bstep (se 1 (by rfl) ⟨1525310, by rfl⟩ : syracuseStep 2033747 = 3050621) B3050621
theorem B4575941 : Blo 2033435 4575941 := bbase (se 4 (by rfl) ⟨428994, by rfl⟩ : syracuseStep 4575941 = 857989) (by norm_num)
theorem B3050627 : Blo 2033435 3050627 := bstep (se 1 (by rfl) ⟨2287970, by rfl⟩ : syracuseStep 3050627 = 4575941) B4575941
theorem B2033751 : Blo 2033435 2033751 := bstep (se 1 (by rfl) ⟨1525313, by rfl⟩ : syracuseStep 2033751 = 3050627) B3050627
theorem B3439141 : Blo 2033435 3439141 := bbase (se 4 (by rfl) ⟨322419, by rfl⟩ : syracuseStep 3439141 = 644839) (by norm_num)
theorem B18342085 : Blo 2033435 18342085 := bstep (se 4 (by rfl) ⟨1719570, by rfl⟩ : syracuseStep 18342085 = 3439141) B3439141
theorem B24456113 : Blo 2033435 24456113 := bstep (se 2 (by rfl) ⟨9171042, by rfl⟩ : syracuseStep 24456113 = 18342085) B18342085
theorem B16304075 : Blo 2033435 16304075 := bstep (se 1 (by rfl) ⟨12228056, by rfl⟩ : syracuseStep 16304075 = 24456113) B24456113
theorem B10869383 : Blo 2033435 10869383 := bstep (se 1 (by rfl) ⟨8152037, by rfl⟩ : syracuseStep 10869383 = 16304075) B16304075
theorem B7246255 : Blo 2033435 7246255 := bstep (se 1 (by rfl) ⟨5434691, by rfl⟩ : syracuseStep 7246255 = 10869383) B10869383
theorem B9661673 : Blo 2033435 9661673 := bstep (se 2 (by rfl) ⟨3623127, by rfl⟩ : syracuseStep 9661673 = 7246255) B7246255
theorem B6441115 : Blo 2033435 6441115 := bstep (se 1 (by rfl) ⟨4830836, by rfl⟩ : syracuseStep 6441115 = 9661673) B9661673
theorem B8588153 : Blo 2033435 8588153 := bstep (se 2 (by rfl) ⟨3220557, by rfl⟩ : syracuseStep 8588153 = 6441115) B6441115
theorem B22901741 : Blo 2033435 22901741 := bstep (se 3 (by rfl) ⟨4294076, by rfl⟩ : syracuseStep 22901741 = 8588153) B8588153
theorem B15267827 : Blo 2033435 15267827 := bstep (se 1 (by rfl) ⟨11450870, by rfl⟩ : syracuseStep 15267827 = 22901741) B22901741
theorem B10178551 : Blo 2033435 10178551 := bstep (se 1 (by rfl) ⟨7633913, by rfl⟩ : syracuseStep 10178551 = 15267827) B15267827
theorem B13571401 : Blo 2033435 13571401 := bstep (se 2 (by rfl) ⟨5089275, by rfl⟩ : syracuseStep 13571401 = 10178551) B10178551
theorem B18095201 : Blo 2033435 18095201 := bstep (se 2 (by rfl) ⟨6785700, by rfl⟩ : syracuseStep 18095201 = 13571401) B13571401
theorem B12063467 : Blo 2033435 12063467 := bstep (se 1 (by rfl) ⟨9047600, by rfl⟩ : syracuseStep 12063467 = 18095201) B18095201
theorem B8042311 : Blo 2033435 8042311 := bstep (se 1 (by rfl) ⟨6031733, by rfl⟩ : syracuseStep 8042311 = 12063467) B12063467
theorem B42892325 : Blo 2033435 42892325 := bstep (se 4 (by rfl) ⟨4021155, by rfl⟩ : syracuseStep 42892325 = 8042311) B8042311
theorem B28594883 : Blo 2033435 28594883 := bstep (se 1 (by rfl) ⟨21446162, by rfl⟩ : syracuseStep 28594883 = 42892325) B42892325
theorem B76253021 : Blo 2033435 76253021 := bstep (se 3 (by rfl) ⟨14297441, by rfl⟩ : syracuseStep 76253021 = 28594883) B28594883
theorem B50835347 : Blo 2033435 50835347 := bstep (se 1 (by rfl) ⟨38126510, by rfl⟩ : syracuseStep 50835347 = 76253021) B76253021
theorem B33890231 : Blo 2033435 33890231 := bstep (se 1 (by rfl) ⟨25417673, by rfl⟩ : syracuseStep 33890231 = 50835347) B50835347
theorem B22593487 : Blo 2033435 22593487 := bstep (se 1 (by rfl) ⟨16945115, by rfl⟩ : syracuseStep 22593487 = 33890231) B33890231
theorem B30124649 : Blo 2033435 30124649 := bstep (se 2 (by rfl) ⟨11296743, by rfl⟩ : syracuseStep 30124649 = 22593487) B22593487
theorem B20083099 : Blo 2033435 20083099 := bstep (se 1 (by rfl) ⟨15062324, by rfl⟩ : syracuseStep 20083099 = 30124649) B30124649
theorem B26777465 : Blo 2033435 26777465 := bstep (se 2 (by rfl) ⟨10041549, by rfl⟩ : syracuseStep 26777465 = 20083099) B20083099
theorem B17851643 : Blo 2033435 17851643 := bstep (se 1 (by rfl) ⟨13388732, by rfl⟩ : syracuseStep 17851643 = 26777465) B26777465
theorem B11901095 : Blo 2033435 11901095 := bstep (se 1 (by rfl) ⟨8925821, by rfl⟩ : syracuseStep 11901095 = 17851643) B17851643
theorem B7934063 : Blo 2033435 7934063 := bstep (se 1 (by rfl) ⟨5950547, by rfl⟩ : syracuseStep 7934063 = 11901095) B11901095
theorem B84630005 : Blo 2033435 84630005 := bstep (se 5 (by rfl) ⟨3967031, by rfl⟩ : syracuseStep 84630005 = 7934063) B7934063
theorem B56420003 : Blo 2033435 56420003 := bstep (se 1 (by rfl) ⟨42315002, by rfl⟩ : syracuseStep 56420003 = 84630005) B84630005
theorem B37613335 : Blo 2033435 37613335 := bstep (se 1 (by rfl) ⟨28210001, by rfl⟩ : syracuseStep 37613335 = 56420003) B56420003
theorem B50151113 : Blo 2033435 50151113 := bstep (se 2 (by rfl) ⟨18806667, by rfl⟩ : syracuseStep 50151113 = 37613335) B37613335
theorem B33434075 : Blo 2033435 33434075 := bstep (se 1 (by rfl) ⟨25075556, by rfl⟩ : syracuseStep 33434075 = 50151113) B50151113
theorem B22289383 : Blo 2033435 22289383 := bstep (se 1 (by rfl) ⟨16717037, by rfl⟩ : syracuseStep 22289383 = 33434075) B33434075
theorem B118876709 : Blo 2033435 118876709 := bstep (se 4 (by rfl) ⟨11144691, by rfl⟩ : syracuseStep 118876709 = 22289383) B22289383
theorem B79251139 : Blo 2033435 79251139 := bstep (se 1 (by rfl) ⟨59438354, by rfl⟩ : syracuseStep 79251139 = 118876709) B118876709
theorem B422672741 : Blo 2033435 422672741 := bstep (se 4 (by rfl) ⟨39625569, by rfl⟩ : syracuseStep 422672741 = 79251139) B79251139
theorem B281781827 : Blo 2033435 281781827 := bstep (se 1 (by rfl) ⟨211336370, by rfl⟩ : syracuseStep 281781827 = 422672741) B422672741
theorem B187854551 : Blo 2033435 187854551 := bstep (se 1 (by rfl) ⟨140890913, by rfl⟩ : syracuseStep 187854551 = 281781827) B281781827
theorem B125236367 : Blo 2033435 125236367 := bstep (se 1 (by rfl) ⟨93927275, by rfl⟩ : syracuseStep 125236367 = 187854551) B187854551
theorem B83490911 : Blo 2033435 83490911 := bstep (se 1 (by rfl) ⟨62618183, by rfl⟩ : syracuseStep 83490911 = 125236367) B125236367
theorem B55660607 : Blo 2033435 55660607 := bstep (se 1 (by rfl) ⟨41745455, by rfl⟩ : syracuseStep 55660607 = 83490911) B83490911
theorem B37107071 : Blo 2033435 37107071 := bstep (se 1 (by rfl) ⟨27830303, by rfl⟩ : syracuseStep 37107071 = 55660607) B55660607
theorem B24738047 : Blo 2033435 24738047 := bstep (se 1 (by rfl) ⟨18553535, by rfl⟩ : syracuseStep 24738047 = 37107071) B37107071
theorem B16492031 : Blo 2033435 16492031 := bstep (se 1 (by rfl) ⟨12369023, by rfl⟩ : syracuseStep 16492031 = 24738047) B24738047
theorem B10994687 : Blo 2033435 10994687 := bstep (se 1 (by rfl) ⟨8246015, by rfl⟩ : syracuseStep 10994687 = 16492031) B16492031
theorem B7329791 : Blo 2033435 7329791 := bstep (se 1 (by rfl) ⟨5497343, by rfl⟩ : syracuseStep 7329791 = 10994687) B10994687
theorem B19546109 : Blo 2033435 19546109 := bstep (se 3 (by rfl) ⟨3664895, by rfl⟩ : syracuseStep 19546109 = 7329791) B7329791
theorem B13030739 : Blo 2033435 13030739 := bstep (se 1 (by rfl) ⟨9773054, by rfl⟩ : syracuseStep 13030739 = 19546109) B19546109
theorem B8687159 : Blo 2033435 8687159 := bstep (se 1 (by rfl) ⟨6515369, by rfl⟩ : syracuseStep 8687159 = 13030739) B13030739
theorem B5791439 : Blo 2033435 5791439 := bstep (se 1 (by rfl) ⟨4343579, by rfl⟩ : syracuseStep 5791439 = 8687159) B8687159
theorem B3860959 : Blo 2033435 3860959 := bstep (se 1 (by rfl) ⟨2895719, by rfl⟩ : syracuseStep 3860959 = 5791439) B5791439
theorem B5147945 : Blo 2033435 5147945 := bstep (se 2 (by rfl) ⟨1930479, by rfl⟩ : syracuseStep 5147945 = 3860959) B3860959
theorem B3431963 : Blo 2033435 3431963 := bstep (se 1 (by rfl) ⟨2573972, by rfl⟩ : syracuseStep 3431963 = 5147945) B5147945
theorem B2287975 : Blo 2033435 2287975 := bstep (se 1 (by rfl) ⟨1715981, by rfl⟩ : syracuseStep 2287975 = 3431963) B3431963
theorem B3050633 : Blo 2033435 3050633 := bstep (se 2 (by rfl) ⟨1143987, by rfl⟩ : syracuseStep 3050633 = 2287975) B2287975
theorem B2033755 : Blo 2033435 2033755 := bstep (se 1 (by rfl) ⟨1525316, by rfl⟩ : syracuseStep 2033755 = 3050633) B3050633
theorem B10295909 : Blo 2033435 10295909 := bbase (se 4 (by rfl) ⟨965241, by rfl⟩ : syracuseStep 10295909 = 1930483) (by norm_num)
theorem B6863939 : Blo 2033435 6863939 := bstep (se 1 (by rfl) ⟨5147954, by rfl⟩ : syracuseStep 6863939 = 10295909) B10295909
theorem B4575959 : Blo 2033435 4575959 := bstep (se 1 (by rfl) ⟨3431969, by rfl⟩ : syracuseStep 4575959 = 6863939) B6863939
theorem B3050639 : Blo 2033435 3050639 := bstep (se 1 (by rfl) ⟨2287979, by rfl⟩ : syracuseStep 3050639 = 4575959) B4575959
theorem B2033759 : Blo 2033435 2033759 := bstep (se 1 (by rfl) ⟨1525319, by rfl⟩ : syracuseStep 2033759 = 3050639) B3050639
theorem B3050645 : Blo 2033435 3050645 := bbase (se 6 (by rfl) ⟨71499, by rfl⟩ : syracuseStep 3050645 = 142999) (by norm_num)
theorem B2033763 : Blo 2033435 2033763 := bstep (se 1 (by rfl) ⟨1525322, by rfl⟩ : syracuseStep 2033763 = 3050645) B3050645
theorem B2476613 : Blo 2033435 2476613 := bbase (se 4 (by rfl) ⟨232182, by rfl⟩ : syracuseStep 2476613 = 464365) (by norm_num)
theorem B6604301 : Blo 2033435 6604301 := bstep (se 3 (by rfl) ⟨1238306, by rfl⟩ : syracuseStep 6604301 = 2476613) B2476613
theorem B4402867 : Blo 2033435 4402867 := bstep (se 1 (by rfl) ⟨3302150, by rfl⟩ : syracuseStep 4402867 = 6604301) B6604301
theorem B5870489 : Blo 2033435 5870489 := bstep (se 2 (by rfl) ⟨2201433, by rfl⟩ : syracuseStep 5870489 = 4402867) B4402867
theorem B15654637 : Blo 2033435 15654637 := bstep (se 3 (by rfl) ⟨2935244, by rfl⟩ : syracuseStep 15654637 = 5870489) B5870489
theorem B20872849 : Blo 2033435 20872849 := bstep (se 2 (by rfl) ⟨7827318, by rfl⟩ : syracuseStep 20872849 = 15654637) B15654637
theorem B27830465 : Blo 2033435 27830465 := bstep (se 2 (by rfl) ⟨10436424, by rfl⟩ : syracuseStep 27830465 = 20872849) B20872849
theorem B18553643 : Blo 2033435 18553643 := bstep (se 1 (by rfl) ⟨13915232, by rfl⟩ : syracuseStep 18553643 = 27830465) B27830465
theorem B12369095 : Blo 2033435 12369095 := bstep (se 1 (by rfl) ⟨9276821, by rfl⟩ : syracuseStep 12369095 = 18553643) B18553643
theorem B8246063 : Blo 2033435 8246063 := bstep (se 1 (by rfl) ⟨6184547, by rfl⟩ : syracuseStep 8246063 = 12369095) B12369095
theorem B21989501 : Blo 2033435 21989501 := bstep (se 3 (by rfl) ⟨4123031, by rfl⟩ : syracuseStep 21989501 = 8246063) B8246063
theorem B14659667 : Blo 2033435 14659667 := bstep (se 1 (by rfl) ⟨10994750, by rfl⟩ : syracuseStep 14659667 = 21989501) B21989501
theorem B9773111 : Blo 2033435 9773111 := bstep (se 1 (by rfl) ⟨7329833, by rfl⟩ : syracuseStep 9773111 = 14659667) B14659667
theorem B6515407 : Blo 2033435 6515407 := bstep (se 1 (by rfl) ⟨4886555, by rfl⟩ : syracuseStep 6515407 = 9773111) B9773111
theorem B8687209 : Blo 2033435 8687209 := bstep (se 2 (by rfl) ⟨3257703, by rfl⟩ : syracuseStep 8687209 = 6515407) B6515407
theorem B11582945 : Blo 2033435 11582945 := bstep (se 2 (by rfl) ⟨4343604, by rfl⟩ : syracuseStep 11582945 = 8687209) B8687209
theorem B7721963 : Blo 2033435 7721963 := bstep (se 1 (by rfl) ⟨5791472, by rfl⟩ : syracuseStep 7721963 = 11582945) B11582945
theorem B5147975 : Blo 2033435 5147975 := bstep (se 1 (by rfl) ⟨3860981, by rfl⟩ : syracuseStep 5147975 = 7721963) B7721963
theorem B3431983 : Blo 2033435 3431983 := bstep (se 1 (by rfl) ⟨2573987, by rfl⟩ : syracuseStep 3431983 = 5147975) B5147975
theorem B4575977 : Blo 2033435 4575977 := bstep (se 2 (by rfl) ⟨1715991, by rfl⟩ : syracuseStep 4575977 = 3431983) B3431983
theorem B3050651 : Blo 2033435 3050651 := bstep (se 1 (by rfl) ⟨2287988, by rfl⟩ : syracuseStep 3050651 = 4575977) B4575977
theorem B2033767 : Blo 2033435 2033767 := bstep (se 1 (by rfl) ⟨1525325, by rfl⟩ : syracuseStep 2033767 = 3050651) B3050651
theorem B2287993 : Blo 2033435 2287993 := bbase (se 2 (by rfl) ⟨857997, by rfl⟩ : syracuseStep 2287993 = 1715995) (by norm_num)
theorem B3050657 : Blo 2033435 3050657 := bstep (se 2 (by rfl) ⟨1143996, by rfl⟩ : syracuseStep 3050657 = 2287993) B2287993
theorem B2033771 : Blo 2033435 2033771 := bstep (se 1 (by rfl) ⟨1525328, by rfl⟩ : syracuseStep 2033771 = 3050657) B3050657
theorem B5497397 : Blo 2033435 5497397 := bbase (se 5 (by rfl) ⟨257690, by rfl⟩ : syracuseStep 5497397 = 515381) (by norm_num)
theorem B3664931 : Blo 2033435 3664931 := bstep (se 1 (by rfl) ⟨2748698, by rfl⟩ : syracuseStep 3664931 = 5497397) B5497397
theorem B9773149 : Blo 2033435 9773149 := bstep (se 3 (by rfl) ⟨1832465, by rfl⟩ : syracuseStep 9773149 = 3664931) B3664931
theorem B13030865 : Blo 2033435 13030865 := bstep (se 2 (by rfl) ⟨4886574, by rfl⟩ : syracuseStep 13030865 = 9773149) B9773149
theorem B8687243 : Blo 2033435 8687243 := bstep (se 1 (by rfl) ⟨6515432, by rfl⟩ : syracuseStep 8687243 = 13030865) B13030865
theorem B5791495 : Blo 2033435 5791495 := bstep (se 1 (by rfl) ⟨4343621, by rfl⟩ : syracuseStep 5791495 = 8687243) B8687243
theorem B7721993 : Blo 2033435 7721993 := bstep (se 2 (by rfl) ⟨2895747, by rfl⟩ : syracuseStep 7721993 = 5791495) B5791495
theorem B5147995 : Blo 2033435 5147995 := bstep (se 1 (by rfl) ⟨3860996, by rfl⟩ : syracuseStep 5147995 = 7721993) B7721993
theorem B6863993 : Blo 2033435 6863993 := bstep (se 2 (by rfl) ⟨2573997, by rfl⟩ : syracuseStep 6863993 = 5147995) B5147995
theorem B4575995 : Blo 2033435 4575995 := bstep (se 1 (by rfl) ⟨3431996, by rfl⟩ : syracuseStep 4575995 = 6863993) B6863993
theorem B3050663 : Blo 2033435 3050663 := bstep (se 1 (by rfl) ⟨2287997, by rfl⟩ : syracuseStep 3050663 = 4575995) B4575995
theorem B2033775 : Blo 2033435 2033775 := bstep (se 1 (by rfl) ⟨1525331, by rfl⟩ : syracuseStep 2033775 = 3050663) B3050663
theorem B3050669 : Blo 2033435 3050669 := bbase (se 3 (by rfl) ⟨572000, by rfl⟩ : syracuseStep 3050669 = 1144001) (by norm_num)
theorem B2033779 : Blo 2033435 2033779 := bstep (se 1 (by rfl) ⟨1525334, by rfl⟩ : syracuseStep 2033779 = 3050669) B3050669
theorem B4576013 : Blo 2033435 4576013 := bbase (se 3 (by rfl) ⟨858002, by rfl⟩ : syracuseStep 4576013 = 1716005) (by norm_num)
theorem B3050675 : Blo 2033435 3050675 := bstep (se 1 (by rfl) ⟨2288006, by rfl⟩ : syracuseStep 3050675 = 4576013) B4576013
theorem B2033783 : Blo 2033435 2033783 := bstep (se 1 (by rfl) ⟨1525337, by rfl⟩ : syracuseStep 2033783 = 3050675) B3050675
theorem B2574013 : Blo 2033435 2574013 := bbase (se 3 (by rfl) ⟨482627, by rfl⟩ : syracuseStep 2574013 = 965255) (by norm_num)
theorem B3432017 : Blo 2033435 3432017 := bstep (se 2 (by rfl) ⟨1287006, by rfl⟩ : syracuseStep 3432017 = 2574013) B2574013
theorem B2288011 : Blo 2033435 2288011 := bstep (se 1 (by rfl) ⟨1716008, by rfl⟩ : syracuseStep 2288011 = 3432017) B3432017
theorem B3050681 : Blo 2033435 3050681 := bstep (se 2 (by rfl) ⟨1144005, by rfl⟩ : syracuseStep 3050681 = 2288011) B2288011
theorem B2033787 : Blo 2033435 2033787 := bstep (se 1 (by rfl) ⟨1525340, by rfl⟩ : syracuseStep 2033787 = 3050681) B3050681
theorem B3302189 : Blo 2033435 3302189 := bbase (se 3 (by rfl) ⟨619160, by rfl⟩ : syracuseStep 3302189 = 1238321) (by norm_num)
theorem B2201459 : Blo 2033435 2201459 := bstep (se 1 (by rfl) ⟨1651094, by rfl⟩ : syracuseStep 2201459 = 3302189) B3302189
theorem B23482229 : Blo 2033435 23482229 := bstep (se 5 (by rfl) ⟨1100729, by rfl⟩ : syracuseStep 23482229 = 2201459) B2201459
theorem B62619277 : Blo 2033435 62619277 := bstep (se 3 (by rfl) ⟨11741114, by rfl⟩ : syracuseStep 62619277 = 23482229) B23482229
theorem B83492369 : Blo 2033435 83492369 := bstep (se 2 (by rfl) ⟨31309638, by rfl⟩ : syracuseStep 83492369 = 62619277) B62619277
theorem B55661579 : Blo 2033435 55661579 := bstep (se 1 (by rfl) ⟨41746184, by rfl⟩ : syracuseStep 55661579 = 83492369) B83492369
theorem B37107719 : Blo 2033435 37107719 := bstep (se 1 (by rfl) ⟨27830789, by rfl⟩ : syracuseStep 37107719 = 55661579) B55661579
theorem B24738479 : Blo 2033435 24738479 := bstep (se 1 (by rfl) ⟨18553859, by rfl⟩ : syracuseStep 24738479 = 37107719) B37107719
theorem B16492319 : Blo 2033435 16492319 := bstep (se 1 (by rfl) ⟨12369239, by rfl⟩ : syracuseStep 16492319 = 24738479) B24738479
theorem B10994879 : Blo 2033435 10994879 := bstep (se 1 (by rfl) ⟨8246159, by rfl⟩ : syracuseStep 10994879 = 16492319) B16492319
theorem B7329919 : Blo 2033435 7329919 := bstep (se 1 (by rfl) ⟨5497439, by rfl⟩ : syracuseStep 7329919 = 10994879) B10994879
theorem B9773225 : Blo 2033435 9773225 := bstep (se 2 (by rfl) ⟨3664959, by rfl⟩ : syracuseStep 9773225 = 7329919) B7329919
theorem B6515483 : Blo 2033435 6515483 := bstep (se 1 (by rfl) ⟨4886612, by rfl⟩ : syracuseStep 6515483 = 9773225) B9773225
theorem B17374621 : Blo 2033435 17374621 := bstep (se 3 (by rfl) ⟨3257741, by rfl⟩ : syracuseStep 17374621 = 6515483) B6515483
theorem B23166161 : Blo 2033435 23166161 := bstep (se 2 (by rfl) ⟨8687310, by rfl⟩ : syracuseStep 23166161 = 17374621) B17374621
theorem B15444107 : Blo 2033435 15444107 := bstep (se 1 (by rfl) ⟨11583080, by rfl⟩ : syracuseStep 15444107 = 23166161) B23166161
theorem B10296071 : Blo 2033435 10296071 := bstep (se 1 (by rfl) ⟨7722053, by rfl⟩ : syracuseStep 10296071 = 15444107) B15444107
theorem B6864047 : Blo 2033435 6864047 := bstep (se 1 (by rfl) ⟨5148035, by rfl⟩ : syracuseStep 6864047 = 10296071) B10296071
theorem B4576031 : Blo 2033435 4576031 := bstep (se 1 (by rfl) ⟨3432023, by rfl⟩ : syracuseStep 4576031 = 6864047) B6864047
theorem B3050687 : Blo 2033435 3050687 := bstep (se 1 (by rfl) ⟨2288015, by rfl⟩ : syracuseStep 3050687 = 4576031) B4576031
theorem B2033791 : Blo 2033435 2033791 := bstep (se 1 (by rfl) ⟨1525343, by rfl⟩ : syracuseStep 2033791 = 3050687) B3050687
theorem B3050693 : Blo 2033435 3050693 := bbase (se 4 (by rfl) ⟨286002, by rfl⟩ : syracuseStep 3050693 = 572005) (by norm_num)
theorem B2033795 : Blo 2033435 2033795 := bstep (se 1 (by rfl) ⟨1525346, by rfl⟩ : syracuseStep 2033795 = 3050693) B3050693
theorem B3432037 : Blo 2033435 3432037 := bbase (se 4 (by rfl) ⟨321753, by rfl⟩ : syracuseStep 3432037 = 643507) (by norm_num)
theorem B4576049 : Blo 2033435 4576049 := bstep (se 2 (by rfl) ⟨1716018, by rfl⟩ : syracuseStep 4576049 = 3432037) B3432037
theorem B3050699 : Blo 2033435 3050699 := bstep (se 1 (by rfl) ⟨2288024, by rfl⟩ : syracuseStep 3050699 = 4576049) B4576049
theorem B2033799 : Blo 2033435 2033799 := bstep (se 1 (by rfl) ⟨1525349, by rfl⟩ : syracuseStep 2033799 = 3050699) B3050699
theorem B2288029 : Blo 2033435 2288029 := bbase (se 3 (by rfl) ⟨429005, by rfl⟩ : syracuseStep 2288029 = 858011) (by norm_num)
theorem B3050705 : Blo 2033435 3050705 := bstep (se 2 (by rfl) ⟨1144014, by rfl⟩ : syracuseStep 3050705 = 2288029) B2288029
theorem B2033803 : Blo 2033435 2033803 := bstep (se 1 (by rfl) ⟨1525352, by rfl⟩ : syracuseStep 2033803 = 3050705) B3050705
theorem B6864101 : Blo 2033435 6864101 := bbase (se 4 (by rfl) ⟨643509, by rfl⟩ : syracuseStep 6864101 = 1287019) (by norm_num)
theorem B4576067 : Blo 2033435 4576067 := bstep (se 1 (by rfl) ⟨3432050, by rfl⟩ : syracuseStep 4576067 = 6864101) B6864101
theorem B3050711 : Blo 2033435 3050711 := bstep (se 1 (by rfl) ⟨2288033, by rfl⟩ : syracuseStep 3050711 = 4576067) B4576067
theorem B2033807 : Blo 2033435 2033807 := bstep (se 1 (by rfl) ⟨1525355, by rfl⟩ : syracuseStep 2033807 = 3050711) B3050711
theorem B3050717 : Blo 2033435 3050717 := bbase (se 3 (by rfl) ⟨572009, by rfl⟩ : syracuseStep 3050717 = 1144019) (by norm_num)
theorem B2033811 : Blo 2033435 2033811 := bstep (se 1 (by rfl) ⟨1525358, by rfl⟩ : syracuseStep 2033811 = 3050717) B3050717
theorem B4576085 : Blo 2033435 4576085 := bbase (se 9 (by rfl) ⟨13406, by rfl⟩ : syracuseStep 4576085 = 26813) (by norm_num)
theorem B3050723 : Blo 2033435 3050723 := bstep (se 1 (by rfl) ⟨2288042, by rfl⟩ : syracuseStep 3050723 = 4576085) B4576085
theorem B2033815 : Blo 2033435 2033815 := bstep (se 1 (by rfl) ⟨1525361, by rfl⟩ : syracuseStep 2033815 = 3050723) B3050723
theorem B5791621 : Blo 2033435 5791621 := bbase (se 4 (by rfl) ⟨542964, by rfl⟩ : syracuseStep 5791621 = 1085929) (by norm_num)
theorem B7722161 : Blo 2033435 7722161 := bstep (se 2 (by rfl) ⟨2895810, by rfl⟩ : syracuseStep 7722161 = 5791621) B5791621
theorem B5148107 : Blo 2033435 5148107 := bstep (se 1 (by rfl) ⟨3861080, by rfl⟩ : syracuseStep 5148107 = 7722161) B7722161
theorem B3432071 : Blo 2033435 3432071 := bstep (se 1 (by rfl) ⟨2574053, by rfl⟩ : syracuseStep 3432071 = 5148107) B5148107
theorem B2288047 : Blo 2033435 2288047 := bstep (se 1 (by rfl) ⟨1716035, by rfl⟩ : syracuseStep 2288047 = 3432071) B3432071
theorem B3050729 : Blo 2033435 3050729 := bstep (se 2 (by rfl) ⟨1144023, by rfl⟩ : syracuseStep 3050729 = 2288047) B2288047
theorem B2033819 : Blo 2033435 2033819 := bstep (se 1 (by rfl) ⟨1525364, by rfl⟩ : syracuseStep 2033819 = 3050729) B3050729
theorem B2935325 : Blo 2033435 2935325 := bbase (se 3 (by rfl) ⟨550373, by rfl⟩ : syracuseStep 2935325 = 1100747) (by norm_num)
theorem B7827533 : Blo 2033435 7827533 := bstep (se 3 (by rfl) ⟨1467662, by rfl⟩ : syracuseStep 7827533 = 2935325) B2935325
theorem B5218355 : Blo 2033435 5218355 := bstep (se 1 (by rfl) ⟨3913766, by rfl⟩ : syracuseStep 5218355 = 7827533) B7827533
theorem B13915613 : Blo 2033435 13915613 := bstep (se 3 (by rfl) ⟨2609177, by rfl⟩ : syracuseStep 13915613 = 5218355) B5218355
theorem B9277075 : Blo 2033435 9277075 := bstep (se 1 (by rfl) ⟨6957806, by rfl⟩ : syracuseStep 9277075 = 13915613) B13915613
theorem B12369433 : Blo 2033435 12369433 := bstep (se 2 (by rfl) ⟨4638537, by rfl⟩ : syracuseStep 12369433 = 9277075) B9277075
theorem B16492577 : Blo 2033435 16492577 := bstep (se 2 (by rfl) ⟨6184716, by rfl⟩ : syracuseStep 16492577 = 12369433) B12369433
theorem B43980205 : Blo 2033435 43980205 := bstep (se 3 (by rfl) ⟨8246288, by rfl⟩ : syracuseStep 43980205 = 16492577) B16492577
theorem B58640273 : Blo 2033435 58640273 := bstep (se 2 (by rfl) ⟨21990102, by rfl⟩ : syracuseStep 58640273 = 43980205) B43980205
theorem B39093515 : Blo 2033435 39093515 := bstep (se 1 (by rfl) ⟨29320136, by rfl⟩ : syracuseStep 39093515 = 58640273) B58640273
theorem B26062343 : Blo 2033435 26062343 := bstep (se 1 (by rfl) ⟨19546757, by rfl⟩ : syracuseStep 26062343 = 39093515) B39093515
theorem B17374895 : Blo 2033435 17374895 := bstep (se 1 (by rfl) ⟨13031171, by rfl⟩ : syracuseStep 17374895 = 26062343) B26062343
theorem B11583263 : Blo 2033435 11583263 := bstep (se 1 (by rfl) ⟨8687447, by rfl⟩ : syracuseStep 11583263 = 17374895) B17374895
theorem B7722175 : Blo 2033435 7722175 := bstep (se 1 (by rfl) ⟨5791631, by rfl⟩ : syracuseStep 7722175 = 11583263) B11583263
theorem B10296233 : Blo 2033435 10296233 := bstep (se 2 (by rfl) ⟨3861087, by rfl⟩ : syracuseStep 10296233 = 7722175) B7722175
theorem B6864155 : Blo 2033435 6864155 := bstep (se 1 (by rfl) ⟨5148116, by rfl⟩ : syracuseStep 6864155 = 10296233) B10296233
theorem B4576103 : Blo 2033435 4576103 := bstep (se 1 (by rfl) ⟨3432077, by rfl⟩ : syracuseStep 4576103 = 6864155) B6864155
theorem B3050735 : Blo 2033435 3050735 := bstep (se 1 (by rfl) ⟨2288051, by rfl⟩ : syracuseStep 3050735 = 4576103) B4576103
theorem B2033823 : Blo 2033435 2033823 := bstep (se 1 (by rfl) ⟨1525367, by rfl⟩ : syracuseStep 2033823 = 3050735) B3050735
theorem B3050741 : Blo 2033435 3050741 := bbase (se 5 (by rfl) ⟨143003, by rfl⟩ : syracuseStep 3050741 = 286007) (by norm_num)
theorem B2033827 : Blo 2033435 2033827 := bstep (se 1 (by rfl) ⟨1525370, by rfl⟩ : syracuseStep 2033827 = 3050741) B3050741
theorem B4638557 : Blo 2033435 4638557 := bbase (se 3 (by rfl) ⟨869729, by rfl⟩ : syracuseStep 4638557 = 1739459) (by norm_num)
theorem B12369485 : Blo 2033435 12369485 := bstep (se 3 (by rfl) ⟨2319278, by rfl⟩ : syracuseStep 12369485 = 4638557) B4638557
theorem B8246323 : Blo 2033435 8246323 := bstep (se 1 (by rfl) ⟨6184742, by rfl⟩ : syracuseStep 8246323 = 12369485) B12369485
theorem B10995097 : Blo 2033435 10995097 := bstep (se 2 (by rfl) ⟨4123161, by rfl⟩ : syracuseStep 10995097 = 8246323) B8246323
theorem B14660129 : Blo 2033435 14660129 := bstep (se 2 (by rfl) ⟨5497548, by rfl⟩ : syracuseStep 14660129 = 10995097) B10995097
theorem B9773419 : Blo 2033435 9773419 := bstep (se 1 (by rfl) ⟨7330064, by rfl⟩ : syracuseStep 9773419 = 14660129) B14660129
theorem B13031225 : Blo 2033435 13031225 := bstep (se 2 (by rfl) ⟨4886709, by rfl⟩ : syracuseStep 13031225 = 9773419) B9773419
theorem B8687483 : Blo 2033435 8687483 := bstep (se 1 (by rfl) ⟨6515612, by rfl⟩ : syracuseStep 8687483 = 13031225) B13031225
theorem B5791655 : Blo 2033435 5791655 := bstep (se 1 (by rfl) ⟨4343741, by rfl⟩ : syracuseStep 5791655 = 8687483) B8687483
theorem B3861103 : Blo 2033435 3861103 := bstep (se 1 (by rfl) ⟨2895827, by rfl⟩ : syracuseStep 3861103 = 5791655) B5791655
theorem B5148137 : Blo 2033435 5148137 := bstep (se 2 (by rfl) ⟨1930551, by rfl⟩ : syracuseStep 5148137 = 3861103) B3861103
theorem B3432091 : Blo 2033435 3432091 := bstep (se 1 (by rfl) ⟨2574068, by rfl⟩ : syracuseStep 3432091 = 5148137) B5148137
theorem B4576121 : Blo 2033435 4576121 := bstep (se 2 (by rfl) ⟨1716045, by rfl⟩ : syracuseStep 4576121 = 3432091) B3432091
theorem B3050747 : Blo 2033435 3050747 := bstep (se 1 (by rfl) ⟨2288060, by rfl⟩ : syracuseStep 3050747 = 4576121) B4576121
theorem B2033831 : Blo 2033435 2033831 := bstep (se 1 (by rfl) ⟨1525373, by rfl⟩ : syracuseStep 2033831 = 3050747) B3050747
theorem B2288065 : Blo 2033435 2288065 := bbase (se 2 (by rfl) ⟨858024, by rfl⟩ : syracuseStep 2288065 = 1716049) (by norm_num)
theorem B3050753 : Blo 2033435 3050753 := bstep (se 2 (by rfl) ⟨1144032, by rfl⟩ : syracuseStep 3050753 = 2288065) B2288065
theorem B2033835 : Blo 2033435 2033835 := bstep (se 1 (by rfl) ⟨1525376, by rfl⟩ : syracuseStep 2033835 = 3050753) B3050753
theorem B5148157 : Blo 2033435 5148157 := bbase (se 3 (by rfl) ⟨965279, by rfl⟩ : syracuseStep 5148157 = 1930559) (by norm_num)
theorem B6864209 : Blo 2033435 6864209 := bstep (se 2 (by rfl) ⟨2574078, by rfl⟩ : syracuseStep 6864209 = 5148157) B5148157
theorem B4576139 : Blo 2033435 4576139 := bstep (se 1 (by rfl) ⟨3432104, by rfl⟩ : syracuseStep 4576139 = 6864209) B6864209
theorem B3050759 : Blo 2033435 3050759 := bstep (se 1 (by rfl) ⟨2288069, by rfl⟩ : syracuseStep 3050759 = 4576139) B4576139
theorem B2033839 : Blo 2033435 2033839 := bstep (se 1 (by rfl) ⟨1525379, by rfl⟩ : syracuseStep 2033839 = 3050759) B3050759
theorem B3050765 : Blo 2033435 3050765 := bbase (se 3 (by rfl) ⟨572018, by rfl⟩ : syracuseStep 3050765 = 1144037) (by norm_num)
theorem B2033843 : Blo 2033435 2033843 := bstep (se 1 (by rfl) ⟨1525382, by rfl⟩ : syracuseStep 2033843 = 3050765) B3050765
theorem B4576157 : Blo 2033435 4576157 := bbase (se 3 (by rfl) ⟨858029, by rfl⟩ : syracuseStep 4576157 = 1716059) (by norm_num)
theorem B3050771 : Blo 2033435 3050771 := bstep (se 1 (by rfl) ⟨2288078, by rfl⟩ : syracuseStep 3050771 = 4576157) B4576157
theorem B2033847 : Blo 2033435 2033847 := bstep (se 1 (by rfl) ⟨1525385, by rfl⟩ : syracuseStep 2033847 = 3050771) B3050771
theorem B3432125 : Blo 2033435 3432125 := bbase (se 3 (by rfl) ⟨643523, by rfl⟩ : syracuseStep 3432125 = 1287047) (by norm_num)
theorem B2288083 : Blo 2033435 2288083 := bstep (se 1 (by rfl) ⟨1716062, by rfl⟩ : syracuseStep 2288083 = 3432125) B3432125
theorem B3050777 : Blo 2033435 3050777 := bstep (se 2 (by rfl) ⟨1144041, by rfl⟩ : syracuseStep 3050777 = 2288083) B2288083
theorem B2033851 : Blo 2033435 2033851 := bstep (se 1 (by rfl) ⟨1525388, by rfl⟩ : syracuseStep 2033851 = 3050777) B3050777
theorem B11583445 : Blo 2033435 11583445 := bbase (se 7 (by rfl) ⟨135743, by rfl⟩ : syracuseStep 11583445 = 271487) (by norm_num)
theorem B15444593 : Blo 2033435 15444593 := bstep (se 2 (by rfl) ⟨5791722, by rfl⟩ : syracuseStep 15444593 = 11583445) B11583445
theorem B10296395 : Blo 2033435 10296395 := bstep (se 1 (by rfl) ⟨7722296, by rfl⟩ : syracuseStep 10296395 = 15444593) B15444593
theorem B6864263 : Blo 2033435 6864263 := bstep (se 1 (by rfl) ⟨5148197, by rfl⟩ : syracuseStep 6864263 = 10296395) B10296395
theorem B4576175 : Blo 2033435 4576175 := bstep (se 1 (by rfl) ⟨3432131, by rfl⟩ : syracuseStep 4576175 = 6864263) B6864263
theorem B3050783 : Blo 2033435 3050783 := bstep (se 1 (by rfl) ⟨2288087, by rfl⟩ : syracuseStep 3050783 = 4576175) B4576175
theorem B2033855 : Blo 2033435 2033855 := bstep (se 1 (by rfl) ⟨1525391, by rfl⟩ : syracuseStep 2033855 = 3050783) B3050783
theorem B3050789 : Blo 2033435 3050789 := bbase (se 4 (by rfl) ⟨286011, by rfl⟩ : syracuseStep 3050789 = 572023) (by norm_num)
theorem B2033859 : Blo 2033435 2033859 := bstep (se 1 (by rfl) ⟨1525394, by rfl⟩ : syracuseStep 2033859 = 3050789) B3050789
theorem B2574109 : Blo 2033435 2574109 := bbase (se 3 (by rfl) ⟨482645, by rfl⟩ : syracuseStep 2574109 = 965291) (by norm_num)
theorem B3432145 : Blo 2033435 3432145 := bstep (se 2 (by rfl) ⟨1287054, by rfl⟩ : syracuseStep 3432145 = 2574109) B2574109
theorem B4576193 : Blo 2033435 4576193 := bstep (se 2 (by rfl) ⟨1716072, by rfl⟩ : syracuseStep 4576193 = 3432145) B3432145
theorem B3050795 : Blo 2033435 3050795 := bstep (se 1 (by rfl) ⟨2288096, by rfl⟩ : syracuseStep 3050795 = 4576193) B4576193
theorem B2033863 : Blo 2033435 2033863 := bstep (se 1 (by rfl) ⟨1525397, by rfl⟩ : syracuseStep 2033863 = 3050795) B3050795
theorem B2288101 : Blo 2033435 2288101 := bbase (se 4 (by rfl) ⟨214509, by rfl⟩ : syracuseStep 2288101 = 429019) (by norm_num)
theorem B3050801 : Blo 2033435 3050801 := bstep (se 2 (by rfl) ⟨1144050, by rfl⟩ : syracuseStep 3050801 = 2288101) B2288101
theorem B2033867 : Blo 2033435 2033867 := bstep (se 1 (by rfl) ⟨1525400, by rfl⟩ : syracuseStep 2033867 = 3050801) B3050801
theorem B2748829 : Blo 2033435 2748829 := bbase (se 3 (by rfl) ⟨515405, by rfl⟩ : syracuseStep 2748829 = 1030811) (by norm_num)
theorem B3665105 : Blo 2033435 3665105 := bstep (se 2 (by rfl) ⟨1374414, by rfl⟩ : syracuseStep 3665105 = 2748829) B2748829
theorem B2443403 : Blo 2033435 2443403 := bstep (se 1 (by rfl) ⟨1832552, by rfl⟩ : syracuseStep 2443403 = 3665105) B3665105
theorem B6515741 : Blo 2033435 6515741 := bstep (se 3 (by rfl) ⟨1221701, by rfl⟩ : syracuseStep 6515741 = 2443403) B2443403
theorem B4343827 : Blo 2033435 4343827 := bstep (se 1 (by rfl) ⟨3257870, by rfl⟩ : syracuseStep 4343827 = 6515741) B6515741
theorem B5791769 : Blo 2033435 5791769 := bstep (se 2 (by rfl) ⟨2171913, by rfl⟩ : syracuseStep 5791769 = 4343827) B4343827
theorem B3861179 : Blo 2033435 3861179 := bstep (se 1 (by rfl) ⟨2895884, by rfl⟩ : syracuseStep 3861179 = 5791769) B5791769
theorem B2574119 : Blo 2033435 2574119 := bstep (se 1 (by rfl) ⟨1930589, by rfl⟩ : syracuseStep 2574119 = 3861179) B3861179
theorem B6864317 : Blo 2033435 6864317 := bstep (se 3 (by rfl) ⟨1287059, by rfl⟩ : syracuseStep 6864317 = 2574119) B2574119
theorem B4576211 : Blo 2033435 4576211 := bstep (se 1 (by rfl) ⟨3432158, by rfl⟩ : syracuseStep 4576211 = 6864317) B6864317
theorem B3050807 : Blo 2033435 3050807 := bstep (se 1 (by rfl) ⟨2288105, by rfl⟩ : syracuseStep 3050807 = 4576211) B4576211
theorem B2033871 : Blo 2033435 2033871 := bstep (se 1 (by rfl) ⟨1525403, by rfl⟩ : syracuseStep 2033871 = 3050807) B3050807
theorem B3050813 : Blo 2033435 3050813 := bbase (se 3 (by rfl) ⟨572027, by rfl⟩ : syracuseStep 3050813 = 1144055) (by norm_num)
theorem B2033875 : Blo 2033435 2033875 := bstep (se 1 (by rfl) ⟨1525406, by rfl⟩ : syracuseStep 2033875 = 3050813) B3050813
theorem B4576229 : Blo 2033435 4576229 := bbase (se 4 (by rfl) ⟨429021, by rfl⟩ : syracuseStep 4576229 = 858043) (by norm_num)
theorem B3050819 : Blo 2033435 3050819 := bstep (se 1 (by rfl) ⟨2288114, by rfl⟩ : syracuseStep 3050819 = 4576229) B4576229
theorem B2033879 : Blo 2033435 2033879 := bstep (se 1 (by rfl) ⟨1525409, by rfl⟩ : syracuseStep 2033879 = 3050819) B3050819
theorem B5148269 : Blo 2033435 5148269 := bbase (se 3 (by rfl) ⟨965300, by rfl⟩ : syracuseStep 5148269 = 1930601) (by norm_num)
theorem B3432179 : Blo 2033435 3432179 := bstep (se 1 (by rfl) ⟨2574134, by rfl⟩ : syracuseStep 3432179 = 5148269) B5148269
theorem B2288119 : Blo 2033435 2288119 := bstep (se 1 (by rfl) ⟨1716089, by rfl⟩ : syracuseStep 2288119 = 3432179) B3432179
theorem B3050825 : Blo 2033435 3050825 := bstep (se 2 (by rfl) ⟨1144059, by rfl⟩ : syracuseStep 3050825 = 2288119) B2288119
theorem B2033883 : Blo 2033435 2033883 := bstep (se 1 (by rfl) ⟨1525412, by rfl⟩ : syracuseStep 2033883 = 3050825) B3050825
theorem B4343861 : Blo 2033435 4343861 := bbase (se 5 (by rfl) ⟨203618, by rfl⟩ : syracuseStep 4343861 = 407237) (by norm_num)
theorem B2895907 : Blo 2033435 2895907 := bstep (se 1 (by rfl) ⟨2171930, by rfl⟩ : syracuseStep 2895907 = 4343861) B4343861
theorem B3861209 : Blo 2033435 3861209 := bstep (se 2 (by rfl) ⟨1447953, by rfl⟩ : syracuseStep 3861209 = 2895907) B2895907
theorem B10296557 : Blo 2033435 10296557 := bstep (se 3 (by rfl) ⟨1930604, by rfl⟩ : syracuseStep 10296557 = 3861209) B3861209
theorem B6864371 : Blo 2033435 6864371 := bstep (se 1 (by rfl) ⟨5148278, by rfl⟩ : syracuseStep 6864371 = 10296557) B10296557
theorem B4576247 : Blo 2033435 4576247 := bstep (se 1 (by rfl) ⟨3432185, by rfl⟩ : syracuseStep 4576247 = 6864371) B6864371
theorem B3050831 : Blo 2033435 3050831 := bstep (se 1 (by rfl) ⟨2288123, by rfl⟩ : syracuseStep 3050831 = 4576247) B4576247
theorem B2033887 : Blo 2033435 2033887 := bstep (se 1 (by rfl) ⟨1525415, by rfl⟩ : syracuseStep 2033887 = 3050831) B3050831
theorem B3050837 : Blo 2033435 3050837 := bbase (se 11 (by rfl) ⟨2234, by rfl⟩ : syracuseStep 3050837 = 4469) (by norm_num)
theorem B2033891 : Blo 2033435 2033891 := bstep (se 1 (by rfl) ⟨1525418, by rfl⟩ : syracuseStep 2033891 = 3050837) B3050837
theorem B3257909 : Blo 2033435 3257909 := bbase (se 5 (by rfl) ⟨152714, by rfl⟩ : syracuseStep 3257909 = 305429) (by norm_num)
theorem B2171939 : Blo 2033435 2171939 := bstep (se 1 (by rfl) ⟨1628954, by rfl⟩ : syracuseStep 2171939 = 3257909) B3257909
theorem B5791837 : Blo 2033435 5791837 := bstep (se 3 (by rfl) ⟨1085969, by rfl⟩ : syracuseStep 5791837 = 2171939) B2171939
theorem B7722449 : Blo 2033435 7722449 := bstep (se 2 (by rfl) ⟨2895918, by rfl⟩ : syracuseStep 7722449 = 5791837) B5791837
theorem B5148299 : Blo 2033435 5148299 := bstep (se 1 (by rfl) ⟨3861224, by rfl⟩ : syracuseStep 5148299 = 7722449) B7722449
theorem B3432199 : Blo 2033435 3432199 := bstep (se 1 (by rfl) ⟨2574149, by rfl⟩ : syracuseStep 3432199 = 5148299) B5148299
theorem B4576265 : Blo 2033435 4576265 := bstep (se 2 (by rfl) ⟨1716099, by rfl⟩ : syracuseStep 4576265 = 3432199) B3432199
theorem B3050843 : Blo 2033435 3050843 := bstep (se 1 (by rfl) ⟨2288132, by rfl⟩ : syracuseStep 3050843 = 4576265) B4576265
theorem B2033895 : Blo 2033435 2033895 := bstep (se 1 (by rfl) ⟨1525421, by rfl⟩ : syracuseStep 2033895 = 3050843) B3050843
theorem B2288137 : Blo 2033435 2288137 := bbase (se 2 (by rfl) ⟨858051, by rfl⟩ : syracuseStep 2288137 = 1716103) (by norm_num)
theorem B3050849 : Blo 2033435 3050849 := bstep (se 2 (by rfl) ⟨1144068, by rfl⟩ : syracuseStep 3050849 = 2288137) B2288137
theorem B2033899 : Blo 2033435 2033899 := bstep (se 1 (by rfl) ⟨1525424, by rfl⟩ : syracuseStep 2033899 = 3050849) B3050849
theorem B32986453 : Blo 2033435 32986453 := bbase (se 17 (by rfl) ⟨377, by rfl⟩ : syracuseStep 32986453 = 755) (by norm_num)
theorem B43981937 : Blo 2033435 43981937 := bstep (se 2 (by rfl) ⟨16493226, by rfl⟩ : syracuseStep 43981937 = 32986453) B32986453
theorem B29321291 : Blo 2033435 29321291 := bstep (se 1 (by rfl) ⟨21990968, by rfl⟩ : syracuseStep 29321291 = 43981937) B43981937
theorem B19547527 : Blo 2033435 19547527 := bstep (se 1 (by rfl) ⟨14660645, by rfl⟩ : syracuseStep 19547527 = 29321291) B29321291
theorem B26063369 : Blo 2033435 26063369 := bstep (se 2 (by rfl) ⟨9773763, by rfl⟩ : syracuseStep 26063369 = 19547527) B19547527
theorem B17375579 : Blo 2033435 17375579 := bstep (se 1 (by rfl) ⟨13031684, by rfl⟩ : syracuseStep 17375579 = 26063369) B26063369
theorem B11583719 : Blo 2033435 11583719 := bstep (se 1 (by rfl) ⟨8687789, by rfl⟩ : syracuseStep 11583719 = 17375579) B17375579
theorem B7722479 : Blo 2033435 7722479 := bstep (se 1 (by rfl) ⟨5791859, by rfl⟩ : syracuseStep 7722479 = 11583719) B11583719
theorem B5148319 : Blo 2033435 5148319 := bstep (se 1 (by rfl) ⟨3861239, by rfl⟩ : syracuseStep 5148319 = 7722479) B7722479
theorem B6864425 : Blo 2033435 6864425 := bstep (se 2 (by rfl) ⟨2574159, by rfl⟩ : syracuseStep 6864425 = 5148319) B5148319
theorem B4576283 : Blo 2033435 4576283 := bstep (se 1 (by rfl) ⟨3432212, by rfl⟩ : syracuseStep 4576283 = 6864425) B6864425
theorem B3050855 : Blo 2033435 3050855 := bstep (se 1 (by rfl) ⟨2288141, by rfl⟩ : syracuseStep 3050855 = 4576283) B4576283
theorem B2033903 : Blo 2033435 2033903 := bstep (se 1 (by rfl) ⟨1525427, by rfl⟩ : syracuseStep 2033903 = 3050855) B3050855
theorem B3050861 : Blo 2033435 3050861 := bbase (se 3 (by rfl) ⟨572036, by rfl⟩ : syracuseStep 3050861 = 1144073) (by norm_num)
theorem B2033907 : Blo 2033435 2033907 := bstep (se 1 (by rfl) ⟨1525430, by rfl⟩ : syracuseStep 2033907 = 3050861) B3050861
theorem B4576301 : Blo 2033435 4576301 := bbase (se 3 (by rfl) ⟨858056, by rfl⟩ : syracuseStep 4576301 = 1716113) (by norm_num)
theorem B3050867 : Blo 2033435 3050867 := bstep (se 1 (by rfl) ⟨2288150, by rfl⟩ : syracuseStep 3050867 = 4576301) B4576301
theorem B2033911 : Blo 2033435 2033911 := bstep (se 1 (by rfl) ⟨1525433, by rfl⟩ : syracuseStep 2033911 = 3050867) B3050867
theorem B13031765 : Blo 2033435 13031765 := bbase (se 10 (by rfl) ⟨19089, by rfl⟩ : syracuseStep 13031765 = 38179) (by norm_num)
theorem B8687843 : Blo 2033435 8687843 := bstep (se 1 (by rfl) ⟨6515882, by rfl⟩ : syracuseStep 8687843 = 13031765) B13031765
theorem B5791895 : Blo 2033435 5791895 := bstep (se 1 (by rfl) ⟨4343921, by rfl⟩ : syracuseStep 5791895 = 8687843) B8687843
theorem B3861263 : Blo 2033435 3861263 := bstep (se 1 (by rfl) ⟨2895947, by rfl⟩ : syracuseStep 3861263 = 5791895) B5791895
theorem B2574175 : Blo 2033435 2574175 := bstep (se 1 (by rfl) ⟨1930631, by rfl⟩ : syracuseStep 2574175 = 3861263) B3861263
theorem B3432233 : Blo 2033435 3432233 := bstep (se 2 (by rfl) ⟨1287087, by rfl⟩ : syracuseStep 3432233 = 2574175) B2574175
theorem B2288155 : Blo 2033435 2288155 := bstep (se 1 (by rfl) ⟨1716116, by rfl⟩ : syracuseStep 2288155 = 3432233) B3432233
theorem B3050873 : Blo 2033435 3050873 := bstep (se 2 (by rfl) ⟨1144077, by rfl⟩ : syracuseStep 3050873 = 2288155) B2288155
theorem B2033915 : Blo 2033435 2033915 := bstep (se 1 (by rfl) ⟨1525436, by rfl⟩ : syracuseStep 2033915 = 3050873) B3050873
theorem B6515893 : Blo 2033435 6515893 := bbase (se 5 (by rfl) ⟨305432, by rfl⟩ : syracuseStep 6515893 = 610865) (by norm_num)
theorem B34751429 : Blo 2033435 34751429 := bstep (se 4 (by rfl) ⟨3257946, by rfl⟩ : syracuseStep 34751429 = 6515893) B6515893
theorem B23167619 : Blo 2033435 23167619 := bstep (se 1 (by rfl) ⟨17375714, by rfl⟩ : syracuseStep 23167619 = 34751429) B34751429
theorem B15445079 : Blo 2033435 15445079 := bstep (se 1 (by rfl) ⟨11583809, by rfl⟩ : syracuseStep 15445079 = 23167619) B23167619
theorem B10296719 : Blo 2033435 10296719 := bstep (se 1 (by rfl) ⟨7722539, by rfl⟩ : syracuseStep 10296719 = 15445079) B15445079
theorem B6864479 : Blo 2033435 6864479 := bstep (se 1 (by rfl) ⟨5148359, by rfl⟩ : syracuseStep 6864479 = 10296719) B10296719
theorem B4576319 : Blo 2033435 4576319 := bstep (se 1 (by rfl) ⟨3432239, by rfl⟩ : syracuseStep 4576319 = 6864479) B6864479
theorem B3050879 : Blo 2033435 3050879 := bstep (se 1 (by rfl) ⟨2288159, by rfl⟩ : syracuseStep 3050879 = 4576319) B4576319
theorem B2033919 : Blo 2033435 2033919 := bstep (se 1 (by rfl) ⟨1525439, by rfl⟩ : syracuseStep 2033919 = 3050879) B3050879
theorem B3050885 : Blo 2033435 3050885 := bbase (se 4 (by rfl) ⟨286020, by rfl⟩ : syracuseStep 3050885 = 572041) (by norm_num)
theorem B2033923 : Blo 2033435 2033923 := bstep (se 1 (by rfl) ⟨1525442, by rfl⟩ : syracuseStep 2033923 = 3050885) B3050885
theorem B3432253 : Blo 2033435 3432253 := bbase (se 3 (by rfl) ⟨643547, by rfl⟩ : syracuseStep 3432253 = 1287095) (by norm_num)
theorem B4576337 : Blo 2033435 4576337 := bstep (se 2 (by rfl) ⟨1716126, by rfl⟩ : syracuseStep 4576337 = 3432253) B3432253
theorem B3050891 : Blo 2033435 3050891 := bstep (se 1 (by rfl) ⟨2288168, by rfl⟩ : syracuseStep 3050891 = 4576337) B4576337
theorem B2033927 : Blo 2033435 2033927 := bstep (se 1 (by rfl) ⟨1525445, by rfl⟩ : syracuseStep 2033927 = 3050891) B3050891
theorem B2288173 : Blo 2033435 2288173 := bbase (se 3 (by rfl) ⟨429032, by rfl⟩ : syracuseStep 2288173 = 858065) (by norm_num)
theorem B3050897 : Blo 2033435 3050897 := bstep (se 2 (by rfl) ⟨1144086, by rfl⟩ : syracuseStep 3050897 = 2288173) B2288173
theorem B2033931 : Blo 2033435 2033931 := bstep (se 1 (by rfl) ⟨1525448, by rfl⟩ : syracuseStep 2033931 = 3050897) B3050897
theorem B6864533 : Blo 2033435 6864533 := bbase (se 6 (by rfl) ⟨160887, by rfl⟩ : syracuseStep 6864533 = 321775) (by norm_num)
theorem B4576355 : Blo 2033435 4576355 := bstep (se 1 (by rfl) ⟨3432266, by rfl⟩ : syracuseStep 4576355 = 6864533) B6864533
theorem B3050903 : Blo 2033435 3050903 := bstep (se 1 (by rfl) ⟨2288177, by rfl⟩ : syracuseStep 3050903 = 4576355) B4576355
theorem B2033935 : Blo 2033435 2033935 := bstep (se 1 (by rfl) ⟨1525451, by rfl⟩ : syracuseStep 2033935 = 3050903) B3050903
theorem B3050909 : Blo 2033435 3050909 := bbase (se 3 (by rfl) ⟨572045, by rfl⟩ : syracuseStep 3050909 = 1144091) (by norm_num)
theorem B2033939 : Blo 2033435 2033939 := bstep (se 1 (by rfl) ⟨1525454, by rfl⟩ : syracuseStep 2033939 = 3050909) B3050909
theorem B4576373 : Blo 2033435 4576373 := bbase (se 5 (by rfl) ⟨214517, by rfl⟩ : syracuseStep 4576373 = 429035) (by norm_num)
theorem B3050915 : Blo 2033435 3050915 := bstep (se 1 (by rfl) ⟨2288186, by rfl⟩ : syracuseStep 3050915 = 4576373) B4576373
theorem B2033943 : Blo 2033435 2033943 := bstep (se 1 (by rfl) ⟨1525457, by rfl⟩ : syracuseStep 2033943 = 3050915) B3050915
theorem B17375957 : Blo 2033435 17375957 := bbase (se 7 (by rfl) ⟨203624, by rfl⟩ : syracuseStep 17375957 = 407249) (by norm_num)
theorem B11583971 : Blo 2033435 11583971 := bstep (se 1 (by rfl) ⟨8687978, by rfl⟩ : syracuseStep 11583971 = 17375957) B17375957
theorem B7722647 : Blo 2033435 7722647 := bstep (se 1 (by rfl) ⟨5791985, by rfl⟩ : syracuseStep 7722647 = 11583971) B11583971
theorem B5148431 : Blo 2033435 5148431 := bstep (se 1 (by rfl) ⟨3861323, by rfl⟩ : syracuseStep 5148431 = 7722647) B7722647
theorem B3432287 : Blo 2033435 3432287 := bstep (se 1 (by rfl) ⟨2574215, by rfl⟩ : syracuseStep 3432287 = 5148431) B5148431
theorem B2288191 : Blo 2033435 2288191 := bstep (se 1 (by rfl) ⟨1716143, by rfl⟩ : syracuseStep 2288191 = 3432287) B3432287
theorem B3050921 : Blo 2033435 3050921 := bstep (se 2 (by rfl) ⟨1144095, by rfl⟩ : syracuseStep 3050921 = 2288191) B2288191
theorem B2033947 : Blo 2033435 2033947 := bstep (se 1 (by rfl) ⟨1525460, by rfl⟩ : syracuseStep 2033947 = 3050921) B3050921
theorem B7722661 : Blo 2033435 7722661 := bbase (se 4 (by rfl) ⟨723999, by rfl⟩ : syracuseStep 7722661 = 1447999) (by norm_num)
theorem B10296881 : Blo 2033435 10296881 := bstep (se 2 (by rfl) ⟨3861330, by rfl⟩ : syracuseStep 10296881 = 7722661) B7722661
theorem B6864587 : Blo 2033435 6864587 := bstep (se 1 (by rfl) ⟨5148440, by rfl⟩ : syracuseStep 6864587 = 10296881) B10296881
theorem B4576391 : Blo 2033435 4576391 := bstep (se 1 (by rfl) ⟨3432293, by rfl⟩ : syracuseStep 4576391 = 6864587) B6864587
theorem B3050927 : Blo 2033435 3050927 := bstep (se 1 (by rfl) ⟨2288195, by rfl⟩ : syracuseStep 3050927 = 4576391) B4576391
theorem B2033951 : Blo 2033435 2033951 := bstep (se 1 (by rfl) ⟨1525463, by rfl⟩ : syracuseStep 2033951 = 3050927) B3050927
theorem B3050933 : Blo 2033435 3050933 := bbase (se 5 (by rfl) ⟨143012, by rfl⟩ : syracuseStep 3050933 = 286025) (by norm_num)
theorem B2033955 : Blo 2033435 2033955 := bstep (se 1 (by rfl) ⟨1525466, by rfl⟩ : syracuseStep 2033955 = 3050933) B3050933
theorem B5148461 : Blo 2033435 5148461 := bbase (se 3 (by rfl) ⟨965336, by rfl⟩ : syracuseStep 5148461 = 1930673) (by norm_num)
theorem B3432307 : Blo 2033435 3432307 := bstep (se 1 (by rfl) ⟨2574230, by rfl⟩ : syracuseStep 3432307 = 5148461) B5148461
theorem B4576409 : Blo 2033435 4576409 := bstep (se 2 (by rfl) ⟨1716153, by rfl⟩ : syracuseStep 4576409 = 3432307) B3432307
theorem B3050939 : Blo 2033435 3050939 := bstep (se 1 (by rfl) ⟨2288204, by rfl⟩ : syracuseStep 3050939 = 4576409) B4576409
theorem B2033959 : Blo 2033435 2033959 := bstep (se 1 (by rfl) ⟨1525469, by rfl⟩ : syracuseStep 2033959 = 3050939) B3050939
theorem B2288209 : Blo 2033435 2288209 := bbase (se 2 (by rfl) ⟨858078, by rfl⟩ : syracuseStep 2288209 = 1716157) (by norm_num)
theorem B3050945 : Blo 2033435 3050945 := bstep (se 2 (by rfl) ⟨1144104, by rfl⟩ : syracuseStep 3050945 = 2288209) B2288209
theorem B2033963 : Blo 2033435 2033963 := bstep (se 1 (by rfl) ⟨1525472, by rfl⟩ : syracuseStep 2033963 = 3050945) B3050945
theorem B2896021 : Blo 2033435 2896021 := bbase (se 6 (by rfl) ⟨67875, by rfl⟩ : syracuseStep 2896021 = 135751) (by norm_num)
theorem B3861361 : Blo 2033435 3861361 := bstep (se 2 (by rfl) ⟨1448010, by rfl⟩ : syracuseStep 3861361 = 2896021) B2896021
theorem B5148481 : Blo 2033435 5148481 := bstep (se 2 (by rfl) ⟨1930680, by rfl⟩ : syracuseStep 5148481 = 3861361) B3861361
theorem B6864641 : Blo 2033435 6864641 := bstep (se 2 (by rfl) ⟨2574240, by rfl⟩ : syracuseStep 6864641 = 5148481) B5148481
theorem B4576427 : Blo 2033435 4576427 := bstep (se 1 (by rfl) ⟨3432320, by rfl⟩ : syracuseStep 4576427 = 6864641) B6864641
theorem B3050951 : Blo 2033435 3050951 := bstep (se 1 (by rfl) ⟨2288213, by rfl⟩ : syracuseStep 3050951 = 4576427) B4576427
theorem B2033967 : Blo 2033435 2033967 := bstep (se 1 (by rfl) ⟨1525475, by rfl⟩ : syracuseStep 2033967 = 3050951) B3050951
theorem B3050957 : Blo 2033435 3050957 := bbase (se 3 (by rfl) ⟨572054, by rfl⟩ : syracuseStep 3050957 = 1144109) (by norm_num)
theorem B2033971 : Blo 2033435 2033971 := bstep (se 1 (by rfl) ⟨1525478, by rfl⟩ : syracuseStep 2033971 = 3050957) B3050957
theorem B4576445 : Blo 2033435 4576445 := bbase (se 3 (by rfl) ⟨858083, by rfl⟩ : syracuseStep 4576445 = 1716167) (by norm_num)
theorem B3050963 : Blo 2033435 3050963 := bstep (se 1 (by rfl) ⟨2288222, by rfl⟩ : syracuseStep 3050963 = 4576445) B4576445
theorem B2033975 : Blo 2033435 2033975 := bstep (se 1 (by rfl) ⟨1525481, by rfl⟩ : syracuseStep 2033975 = 3050963) B3050963
theorem B3432341 : Blo 2033435 3432341 := bbase (se 6 (by rfl) ⟨80445, by rfl⟩ : syracuseStep 3432341 = 160891) (by norm_num)
theorem B2288227 : Blo 2033435 2288227 := bstep (se 1 (by rfl) ⟨1716170, by rfl⟩ : syracuseStep 2288227 = 3432341) B3432341
theorem B3050969 : Blo 2033435 3050969 := bstep (se 2 (by rfl) ⟨1144113, by rfl⟩ : syracuseStep 3050969 = 2288227) B2288227
theorem B2033979 : Blo 2033435 2033979 := bstep (se 1 (by rfl) ⟨1525484, by rfl⟩ : syracuseStep 2033979 = 3050969) B3050969
theorem B2443537 : Blo 2033435 2443537 := bbase (se 2 (by rfl) ⟨916326, by rfl⟩ : syracuseStep 2443537 = 1832653) (by norm_num)
theorem B13032197 : Blo 2033435 13032197 := bstep (se 4 (by rfl) ⟨1221768, by rfl⟩ : syracuseStep 13032197 = 2443537) B2443537
theorem B8688131 : Blo 2033435 8688131 := bstep (se 1 (by rfl) ⟨6516098, by rfl⟩ : syracuseStep 8688131 = 13032197) B13032197
theorem B5792087 : Blo 2033435 5792087 := bstep (se 1 (by rfl) ⟨4344065, by rfl⟩ : syracuseStep 5792087 = 8688131) B8688131
theorem B15445565 : Blo 2033435 15445565 := bstep (se 3 (by rfl) ⟨2896043, by rfl⟩ : syracuseStep 15445565 = 5792087) B5792087
theorem B10297043 : Blo 2033435 10297043 := bstep (se 1 (by rfl) ⟨7722782, by rfl⟩ : syracuseStep 10297043 = 15445565) B15445565
theorem B6864695 : Blo 2033435 6864695 := bstep (se 1 (by rfl) ⟨5148521, by rfl⟩ : syracuseStep 6864695 = 10297043) B10297043
theorem B4576463 : Blo 2033435 4576463 := bstep (se 1 (by rfl) ⟨3432347, by rfl⟩ : syracuseStep 4576463 = 6864695) B6864695
theorem B3050975 : Blo 2033435 3050975 := bstep (se 1 (by rfl) ⟨2288231, by rfl⟩ : syracuseStep 3050975 = 4576463) B4576463
theorem B2033983 : Blo 2033435 2033983 := bstep (se 1 (by rfl) ⟨1525487, by rfl⟩ : syracuseStep 2033983 = 3050975) B3050975
theorem B3050981 : Blo 2033435 3050981 := bbase (se 4 (by rfl) ⟨286029, by rfl⟩ : syracuseStep 3050981 = 572059) (by norm_num)
theorem B2033987 : Blo 2033435 2033987 := bstep (se 1 (by rfl) ⟨1525490, by rfl⟩ : syracuseStep 2033987 = 3050981) B3050981
theorem B5218789 : Blo 2033435 5218789 := bbase (se 4 (by rfl) ⟨489261, by rfl⟩ : syracuseStep 5218789 = 978523) (by norm_num)
theorem B6958385 : Blo 2033435 6958385 := bstep (se 2 (by rfl) ⟨2609394, by rfl⟩ : syracuseStep 6958385 = 5218789) B5218789
theorem B4638923 : Blo 2033435 4638923 := bstep (se 1 (by rfl) ⟨3479192, by rfl⟩ : syracuseStep 4638923 = 6958385) B6958385
theorem B3092615 : Blo 2033435 3092615 := bstep (se 1 (by rfl) ⟨2319461, by rfl⟩ : syracuseStep 3092615 = 4638923) B4638923
theorem B2061743 : Blo 2033435 2061743 := bstep (se 1 (by rfl) ⟨1546307, by rfl⟩ : syracuseStep 2061743 = 3092615) B3092615
theorem B21991925 : Blo 2033435 21991925 := bstep (se 5 (by rfl) ⟨1030871, by rfl⟩ : syracuseStep 21991925 = 2061743) B2061743
theorem B14661283 : Blo 2033435 14661283 := bstep (se 1 (by rfl) ⟨10995962, by rfl⟩ : syracuseStep 14661283 = 21991925) B21991925
theorem B19548377 : Blo 2033435 19548377 := bstep (se 2 (by rfl) ⟨7330641, by rfl⟩ : syracuseStep 19548377 = 14661283) B14661283
theorem B13032251 : Blo 2033435 13032251 := bstep (se 1 (by rfl) ⟨9774188, by rfl⟩ : syracuseStep 13032251 = 19548377) B19548377
theorem B8688167 : Blo 2033435 8688167 := bstep (se 1 (by rfl) ⟨6516125, by rfl⟩ : syracuseStep 8688167 = 13032251) B13032251
theorem B5792111 : Blo 2033435 5792111 := bstep (se 1 (by rfl) ⟨4344083, by rfl⟩ : syracuseStep 5792111 = 8688167) B8688167
theorem B3861407 : Blo 2033435 3861407 := bstep (se 1 (by rfl) ⟨2896055, by rfl⟩ : syracuseStep 3861407 = 5792111) B5792111
theorem B2574271 : Blo 2033435 2574271 := bstep (se 1 (by rfl) ⟨1930703, by rfl⟩ : syracuseStep 2574271 = 3861407) B3861407
theorem B3432361 : Blo 2033435 3432361 := bstep (se 2 (by rfl) ⟨1287135, by rfl⟩ : syracuseStep 3432361 = 2574271) B2574271
theorem B4576481 : Blo 2033435 4576481 := bstep (se 2 (by rfl) ⟨1716180, by rfl⟩ : syracuseStep 4576481 = 3432361) B3432361
theorem B3050987 : Blo 2033435 3050987 := bstep (se 1 (by rfl) ⟨2288240, by rfl⟩ : syracuseStep 3050987 = 4576481) B4576481
theorem B2033991 : Blo 2033435 2033991 := bstep (se 1 (by rfl) ⟨1525493, by rfl⟩ : syracuseStep 2033991 = 3050987) B3050987
theorem B2288245 : Blo 2033435 2288245 := bbase (se 5 (by rfl) ⟨107261, by rfl⟩ : syracuseStep 2288245 = 214523) (by norm_num)
theorem B3050993 : Blo 2033435 3050993 := bstep (se 2 (by rfl) ⟨1144122, by rfl⟩ : syracuseStep 3050993 = 2288245) B2288245
theorem B2033995 : Blo 2033435 2033995 := bstep (se 1 (by rfl) ⟨1525496, by rfl⟩ : syracuseStep 2033995 = 3050993) B3050993
theorem B2574281 : Blo 2033435 2574281 := bbase (se 2 (by rfl) ⟨965355, by rfl⟩ : syracuseStep 2574281 = 1930711) (by norm_num)
theorem B6864749 : Blo 2033435 6864749 := bstep (se 3 (by rfl) ⟨1287140, by rfl⟩ : syracuseStep 6864749 = 2574281) B2574281
theorem B4576499 : Blo 2033435 4576499 := bstep (se 1 (by rfl) ⟨3432374, by rfl⟩ : syracuseStep 4576499 = 6864749) B6864749
theorem B3050999 : Blo 2033435 3050999 := bstep (se 1 (by rfl) ⟨2288249, by rfl⟩ : syracuseStep 3050999 = 4576499) B4576499
theorem B2033999 : Blo 2033435 2033999 := bstep (se 1 (by rfl) ⟨1525499, by rfl⟩ : syracuseStep 2033999 = 3050999) B3050999
theorem B3051005 : Blo 2033435 3051005 := bbase (se 3 (by rfl) ⟨572063, by rfl⟩ : syracuseStep 3051005 = 1144127) (by norm_num)
theorem B2034003 : Blo 2033435 2034003 := bstep (se 1 (by rfl) ⟨1525502, by rfl⟩ : syracuseStep 2034003 = 3051005) B3051005
theorem B4576517 : Blo 2033435 4576517 := bbase (se 4 (by rfl) ⟨429048, by rfl⟩ : syracuseStep 4576517 = 858097) (by norm_num)
theorem B3051011 : Blo 2033435 3051011 := bstep (se 1 (by rfl) ⟨2288258, by rfl⟩ : syracuseStep 3051011 = 4576517) B4576517
theorem B2034007 : Blo 2033435 2034007 := bstep (se 1 (by rfl) ⟨1525505, by rfl⟩ : syracuseStep 2034007 = 3051011) B3051011
theorem B3861445 : Blo 2033435 3861445 := bbase (se 4 (by rfl) ⟨362010, by rfl⟩ : syracuseStep 3861445 = 724021) (by norm_num)
theorem B5148593 : Blo 2033435 5148593 := bstep (se 2 (by rfl) ⟨1930722, by rfl⟩ : syracuseStep 5148593 = 3861445) B3861445
theorem B3432395 : Blo 2033435 3432395 := bstep (se 1 (by rfl) ⟨2574296, by rfl⟩ : syracuseStep 3432395 = 5148593) B5148593
theorem B2288263 : Blo 2033435 2288263 := bstep (se 1 (by rfl) ⟨1716197, by rfl⟩ : syracuseStep 2288263 = 3432395) B3432395
theorem B3051017 : Blo 2033435 3051017 := bstep (se 2 (by rfl) ⟨1144131, by rfl⟩ : syracuseStep 3051017 = 2288263) B2288263
theorem B2034011 : Blo 2033435 2034011 := bstep (se 1 (by rfl) ⟨1525508, by rfl⟩ : syracuseStep 2034011 = 3051017) B3051017
theorem B10297205 : Blo 2033435 10297205 := bbase (se 5 (by rfl) ⟨482681, by rfl⟩ : syracuseStep 10297205 = 965363) (by norm_num)
theorem B6864803 : Blo 2033435 6864803 := bstep (se 1 (by rfl) ⟨5148602, by rfl⟩ : syracuseStep 6864803 = 10297205) B10297205
theorem B4576535 : Blo 2033435 4576535 := bstep (se 1 (by rfl) ⟨3432401, by rfl⟩ : syracuseStep 4576535 = 6864803) B6864803
theorem B3051023 : Blo 2033435 3051023 := bstep (se 1 (by rfl) ⟨2288267, by rfl⟩ : syracuseStep 3051023 = 4576535) B4576535
theorem B2034015 : Blo 2033435 2034015 := bstep (se 1 (by rfl) ⟨1525511, by rfl⟩ : syracuseStep 2034015 = 3051023) B3051023
theorem B3051029 : Blo 2033435 3051029 := bbase (se 6 (by rfl) ⟨71508, by rfl⟩ : syracuseStep 3051029 = 143017) (by norm_num)
theorem B2034019 : Blo 2033435 2034019 := bstep (se 1 (by rfl) ⟨1525514, by rfl⟩ : syracuseStep 2034019 = 3051029) B3051029
theorem B9774341 : Blo 2033435 9774341 := bbase (se 4 (by rfl) ⟨916344, by rfl⟩ : syracuseStep 9774341 = 1832689) (by norm_num)
theorem B6516227 : Blo 2033435 6516227 := bstep (se 1 (by rfl) ⟨4887170, by rfl⟩ : syracuseStep 6516227 = 9774341) B9774341
theorem B17376605 : Blo 2033435 17376605 := bstep (se 3 (by rfl) ⟨3258113, by rfl⟩ : syracuseStep 17376605 = 6516227) B6516227
theorem B11584403 : Blo 2033435 11584403 := bstep (se 1 (by rfl) ⟨8688302, by rfl⟩ : syracuseStep 11584403 = 17376605) B17376605
theorem B7722935 : Blo 2033435 7722935 := bstep (se 1 (by rfl) ⟨5792201, by rfl⟩ : syracuseStep 7722935 = 11584403) B11584403
theorem B5148623 : Blo 2033435 5148623 := bstep (se 1 (by rfl) ⟨3861467, by rfl⟩ : syracuseStep 5148623 = 7722935) B7722935
theorem B3432415 : Blo 2033435 3432415 := bstep (se 1 (by rfl) ⟨2574311, by rfl⟩ : syracuseStep 3432415 = 5148623) B5148623
theorem B4576553 : Blo 2033435 4576553 := bstep (se 2 (by rfl) ⟨1716207, by rfl⟩ : syracuseStep 4576553 = 3432415) B3432415
theorem B3051035 : Blo 2033435 3051035 := bstep (se 1 (by rfl) ⟨2288276, by rfl⟩ : syracuseStep 3051035 = 4576553) B4576553
theorem B2034023 : Blo 2033435 2034023 := bstep (se 1 (by rfl) ⟨1525517, by rfl⟩ : syracuseStep 2034023 = 3051035) B3051035
theorem B2288281 : Blo 2033435 2288281 := bbase (se 2 (by rfl) ⟨858105, by rfl⟩ : syracuseStep 2288281 = 1716211) (by norm_num)
theorem B3051041 : Blo 2033435 3051041 := bstep (se 2 (by rfl) ⟨1144140, by rfl⟩ : syracuseStep 3051041 = 2288281) B2288281
theorem B2034027 : Blo 2033435 2034027 := bstep (se 1 (by rfl) ⟨1525520, by rfl⟩ : syracuseStep 2034027 = 3051041) B3051041
theorem B7722965 : Blo 2033435 7722965 := bbase (se 7 (by rfl) ⟨90503, by rfl⟩ : syracuseStep 7722965 = 181007) (by norm_num)
theorem B5148643 : Blo 2033435 5148643 := bstep (se 1 (by rfl) ⟨3861482, by rfl⟩ : syracuseStep 5148643 = 7722965) B7722965
theorem B6864857 : Blo 2033435 6864857 := bstep (se 2 (by rfl) ⟨2574321, by rfl⟩ : syracuseStep 6864857 = 5148643) B5148643
theorem B4576571 : Blo 2033435 4576571 := bstep (se 1 (by rfl) ⟨3432428, by rfl⟩ : syracuseStep 4576571 = 6864857) B6864857
theorem B3051047 : Blo 2033435 3051047 := bstep (se 1 (by rfl) ⟨2288285, by rfl⟩ : syracuseStep 3051047 = 4576571) B4576571
theorem B2034031 : Blo 2033435 2034031 := bstep (se 1 (by rfl) ⟨1525523, by rfl⟩ : syracuseStep 2034031 = 3051047) B3051047
theorem B3051053 : Blo 2033435 3051053 := bbase (se 3 (by rfl) ⟨572072, by rfl⟩ : syracuseStep 3051053 = 1144145) (by norm_num)
theorem B2034035 : Blo 2033435 2034035 := bstep (se 1 (by rfl) ⟨1525526, by rfl⟩ : syracuseStep 2034035 = 3051053) B3051053
theorem B4576589 : Blo 2033435 4576589 := bbase (se 3 (by rfl) ⟨858110, by rfl⟩ : syracuseStep 4576589 = 1716221) (by norm_num)
theorem B3051059 : Blo 2033435 3051059 := bstep (se 1 (by rfl) ⟨2288294, by rfl⟩ : syracuseStep 3051059 = 4576589) B4576589
theorem B2034039 : Blo 2033435 2034039 := bstep (se 1 (by rfl) ⟨1525529, by rfl⟩ : syracuseStep 2034039 = 3051059) B3051059
theorem B2574337 : Blo 2033435 2574337 := bbase (se 2 (by rfl) ⟨965376, by rfl⟩ : syracuseStep 2574337 = 1930753) (by norm_num)
theorem B3432449 : Blo 2033435 3432449 := bstep (se 2 (by rfl) ⟨1287168, by rfl⟩ : syracuseStep 3432449 = 2574337) B2574337
theorem B2288299 : Blo 2033435 2288299 := bstep (se 1 (by rfl) ⟨1716224, by rfl⟩ : syracuseStep 2288299 = 3432449) B3432449
theorem B3051065 : Blo 2033435 3051065 := bstep (se 2 (by rfl) ⟨1144149, by rfl⟩ : syracuseStep 3051065 = 2288299) B2288299
theorem B2034043 : Blo 2033435 2034043 := bstep (se 1 (by rfl) ⟨1525532, by rfl⟩ : syracuseStep 2034043 = 3051065) B3051065
theorem B2172101 : Blo 2033435 2172101 := bbase (se 4 (by rfl) ⟨203634, by rfl⟩ : syracuseStep 2172101 = 407269) (by norm_num)
theorem B23169077 : Blo 2033435 23169077 := bstep (se 5 (by rfl) ⟨1086050, by rfl⟩ : syracuseStep 23169077 = 2172101) B2172101
theorem B15446051 : Blo 2033435 15446051 := bstep (se 1 (by rfl) ⟨11584538, by rfl⟩ : syracuseStep 15446051 = 23169077) B23169077
theorem B10297367 : Blo 2033435 10297367 := bstep (se 1 (by rfl) ⟨7723025, by rfl⟩ : syracuseStep 10297367 = 15446051) B15446051
theorem B6864911 : Blo 2033435 6864911 := bstep (se 1 (by rfl) ⟨5148683, by rfl⟩ : syracuseStep 6864911 = 10297367) B10297367
theorem B4576607 : Blo 2033435 4576607 := bstep (se 1 (by rfl) ⟨3432455, by rfl⟩ : syracuseStep 4576607 = 6864911) B6864911
theorem B3051071 : Blo 2033435 3051071 := bstep (se 1 (by rfl) ⟨2288303, by rfl⟩ : syracuseStep 3051071 = 4576607) B4576607
theorem B2034047 : Blo 2033435 2034047 := bstep (se 1 (by rfl) ⟨1525535, by rfl⟩ : syracuseStep 2034047 = 3051071) B3051071
theorem B3051077 : Blo 2033435 3051077 := bbase (se 4 (by rfl) ⟨286038, by rfl⟩ : syracuseStep 3051077 = 572077) (by norm_num)
theorem B2034051 : Blo 2033435 2034051 := bstep (se 1 (by rfl) ⟨1525538, by rfl⟩ : syracuseStep 2034051 = 3051077) B3051077
theorem B3432469 : Blo 2033435 3432469 := bbase (se 6 (by rfl) ⟨80448, by rfl⟩ : syracuseStep 3432469 = 160897) (by norm_num)
theorem B4576625 : Blo 2033435 4576625 := bstep (se 2 (by rfl) ⟨1716234, by rfl⟩ : syracuseStep 4576625 = 3432469) B3432469
theorem B3051083 : Blo 2033435 3051083 := bstep (se 1 (by rfl) ⟨2288312, by rfl⟩ : syracuseStep 3051083 = 4576625) B4576625
theorem B2034055 : Blo 2033435 2034055 := bstep (se 1 (by rfl) ⟨1525541, by rfl⟩ : syracuseStep 2034055 = 3051083) B3051083
theorem B2288317 : Blo 2033435 2288317 := bbase (se 3 (by rfl) ⟨429059, by rfl⟩ : syracuseStep 2288317 = 858119) (by norm_num)
theorem B3051089 : Blo 2033435 3051089 := bstep (se 2 (by rfl) ⟨1144158, by rfl⟩ : syracuseStep 3051089 = 2288317) B2288317
theorem B2034059 : Blo 2033435 2034059 := bstep (se 1 (by rfl) ⟨1525544, by rfl⟩ : syracuseStep 2034059 = 3051089) B3051089
theorem B6864965 : Blo 2033435 6864965 := bbase (se 4 (by rfl) ⟨643590, by rfl⟩ : syracuseStep 6864965 = 1287181) (by norm_num)
theorem B4576643 : Blo 2033435 4576643 := bstep (se 1 (by rfl) ⟨3432482, by rfl⟩ : syracuseStep 4576643 = 6864965) B6864965
theorem B3051095 : Blo 2033435 3051095 := bstep (se 1 (by rfl) ⟨2288321, by rfl⟩ : syracuseStep 3051095 = 4576643) B4576643
theorem B2034063 : Blo 2033435 2034063 := bstep (se 1 (by rfl) ⟨1525547, by rfl⟩ : syracuseStep 2034063 = 3051095) B3051095
theorem B3051101 : Blo 2033435 3051101 := bbase (se 3 (by rfl) ⟨572081, by rfl⟩ : syracuseStep 3051101 = 1144163) (by norm_num)
theorem B2034067 : Blo 2033435 2034067 := bstep (se 1 (by rfl) ⟨1525550, by rfl⟩ : syracuseStep 2034067 = 3051101) B3051101
theorem B4576661 : Blo 2033435 4576661 := bbase (se 6 (by rfl) ⟨107265, by rfl⟩ : syracuseStep 4576661 = 214531) (by norm_num)
theorem B3051107 : Blo 2033435 3051107 := bstep (se 1 (by rfl) ⟨2288330, by rfl⟩ : syracuseStep 3051107 = 4576661) B4576661
theorem B2034071 : Blo 2033435 2034071 := bstep (se 1 (by rfl) ⟨1525553, by rfl⟩ : syracuseStep 2034071 = 3051107) B3051107
theorem B5219005 : Blo 2033435 5219005 := bbase (se 3 (by rfl) ⟨978563, by rfl⟩ : syracuseStep 5219005 = 1957127) (by norm_num)
theorem B6958673 : Blo 2033435 6958673 := bstep (se 2 (by rfl) ⟨2609502, by rfl⟩ : syracuseStep 6958673 = 5219005) B5219005
theorem B4639115 : Blo 2033435 4639115 := bstep (se 1 (by rfl) ⟨3479336, by rfl⟩ : syracuseStep 4639115 = 6958673) B6958673
theorem B3092743 : Blo 2033435 3092743 := bstep (se 1 (by rfl) ⟨2319557, by rfl⟩ : syracuseStep 3092743 = 4639115) B4639115
theorem B4123657 : Blo 2033435 4123657 := bstep (se 2 (by rfl) ⟨1546371, by rfl⟩ : syracuseStep 4123657 = 3092743) B3092743
theorem B5498209 : Blo 2033435 5498209 := bstep (se 2 (by rfl) ⟨2061828, by rfl⟩ : syracuseStep 5498209 = 4123657) B4123657
theorem B7330945 : Blo 2033435 7330945 := bstep (se 2 (by rfl) ⟨2749104, by rfl⟩ : syracuseStep 7330945 = 5498209) B5498209
theorem B9774593 : Blo 2033435 9774593 := bstep (se 2 (by rfl) ⟨3665472, by rfl⟩ : syracuseStep 9774593 = 7330945) B7330945
theorem B6516395 : Blo 2033435 6516395 := bstep (se 1 (by rfl) ⟨4887296, by rfl⟩ : syracuseStep 6516395 = 9774593) B9774593
theorem B4344263 : Blo 2033435 4344263 := bstep (se 1 (by rfl) ⟨3258197, by rfl⟩ : syracuseStep 4344263 = 6516395) B6516395
theorem B2896175 : Blo 2033435 2896175 := bstep (se 1 (by rfl) ⟨2172131, by rfl⟩ : syracuseStep 2896175 = 4344263) B4344263
theorem B7723133 : Blo 2033435 7723133 := bstep (se 3 (by rfl) ⟨1448087, by rfl⟩ : syracuseStep 7723133 = 2896175) B2896175
theorem B5148755 : Blo 2033435 5148755 := bstep (se 1 (by rfl) ⟨3861566, by rfl⟩ : syracuseStep 5148755 = 7723133) B7723133
theorem B3432503 : Blo 2033435 3432503 := bstep (se 1 (by rfl) ⟨2574377, by rfl⟩ : syracuseStep 3432503 = 5148755) B5148755
theorem B2288335 : Blo 2033435 2288335 := bstep (se 1 (by rfl) ⟨1716251, by rfl⟩ : syracuseStep 2288335 = 3432503) B3432503
theorem B3051113 : Blo 2033435 3051113 := bstep (se 2 (by rfl) ⟨1144167, by rfl⟩ : syracuseStep 3051113 = 2288335) B2288335
theorem B2034075 : Blo 2033435 2034075 := bstep (se 1 (by rfl) ⟨1525556, by rfl⟩ : syracuseStep 2034075 = 3051113) B3051113
theorem B3914261 : Blo 2033435 3914261 := bbase (se 6 (by rfl) ⟨91740, by rfl⟩ : syracuseStep 3914261 = 183481) (by norm_num)
theorem B2609507 : Blo 2033435 2609507 := bstep (se 1 (by rfl) ⟨1957130, by rfl⟩ : syracuseStep 2609507 = 3914261) B3914261
theorem B6958685 : Blo 2033435 6958685 := bstep (se 3 (by rfl) ⟨1304753, by rfl⟩ : syracuseStep 6958685 = 2609507) B2609507
theorem B4639123 : Blo 2033435 4639123 := bstep (se 1 (by rfl) ⟨3479342, by rfl⟩ : syracuseStep 4639123 = 6958685) B6958685
theorem B6185497 : Blo 2033435 6185497 := bstep (se 2 (by rfl) ⟨2319561, by rfl⟩ : syracuseStep 6185497 = 4639123) B4639123
theorem B8247329 : Blo 2033435 8247329 := bstep (se 2 (by rfl) ⟨3092748, by rfl⟩ : syracuseStep 8247329 = 6185497) B6185497
theorem B5498219 : Blo 2033435 5498219 := bstep (se 1 (by rfl) ⟨4123664, by rfl⟩ : syracuseStep 5498219 = 8247329) B8247329
theorem B3665479 : Blo 2033435 3665479 := bstep (se 1 (by rfl) ⟨2749109, by rfl⟩ : syracuseStep 3665479 = 5498219) B5498219
theorem B4887305 : Blo 2033435 4887305 := bstep (se 2 (by rfl) ⟨1832739, by rfl⟩ : syracuseStep 4887305 = 3665479) B3665479
theorem B3258203 : Blo 2033435 3258203 := bstep (se 1 (by rfl) ⟨2443652, by rfl⟩ : syracuseStep 3258203 = 4887305) B4887305
theorem B8688541 : Blo 2033435 8688541 := bstep (se 3 (by rfl) ⟨1629101, by rfl⟩ : syracuseStep 8688541 = 3258203) B3258203
theorem B11584721 : Blo 2033435 11584721 := bstep (se 2 (by rfl) ⟨4344270, by rfl⟩ : syracuseStep 11584721 = 8688541) B8688541
theorem B7723147 : Blo 2033435 7723147 := bstep (se 1 (by rfl) ⟨5792360, by rfl⟩ : syracuseStep 7723147 = 11584721) B11584721
theorem B10297529 : Blo 2033435 10297529 := bstep (se 2 (by rfl) ⟨3861573, by rfl⟩ : syracuseStep 10297529 = 7723147) B7723147
theorem B6865019 : Blo 2033435 6865019 := bstep (se 1 (by rfl) ⟨5148764, by rfl⟩ : syracuseStep 6865019 = 10297529) B10297529
theorem B4576679 : Blo 2033435 4576679 := bstep (se 1 (by rfl) ⟨3432509, by rfl⟩ : syracuseStep 4576679 = 6865019) B6865019
theorem B3051119 : Blo 2033435 3051119 := bstep (se 1 (by rfl) ⟨2288339, by rfl⟩ : syracuseStep 3051119 = 4576679) B4576679
theorem B2034079 : Blo 2033435 2034079 := bstep (se 1 (by rfl) ⟨1525559, by rfl⟩ : syracuseStep 2034079 = 3051119) B3051119
theorem B3051125 : Blo 2033435 3051125 := bbase (se 5 (by rfl) ⟨143021, by rfl⟩ : syracuseStep 3051125 = 286043) (by norm_num)
theorem B2034083 : Blo 2033435 2034083 := bstep (se 1 (by rfl) ⟨1525562, by rfl⟩ : syracuseStep 2034083 = 3051125) B3051125
theorem B3861589 : Blo 2033435 3861589 := bbase (se 8 (by rfl) ⟨22626, by rfl⟩ : syracuseStep 3861589 = 45253) (by norm_num)
theorem B5148785 : Blo 2033435 5148785 := bstep (se 2 (by rfl) ⟨1930794, by rfl⟩ : syracuseStep 5148785 = 3861589) B3861589
theorem B3432523 : Blo 2033435 3432523 := bstep (se 1 (by rfl) ⟨2574392, by rfl⟩ : syracuseStep 3432523 = 5148785) B5148785
theorem B4576697 : Blo 2033435 4576697 := bstep (se 2 (by rfl) ⟨1716261, by rfl⟩ : syracuseStep 4576697 = 3432523) B3432523
theorem B3051131 : Blo 2033435 3051131 := bstep (se 1 (by rfl) ⟨2288348, by rfl⟩ : syracuseStep 3051131 = 4576697) B4576697
theorem B2034087 : Blo 2033435 2034087 := bstep (se 1 (by rfl) ⟨1525565, by rfl⟩ : syracuseStep 2034087 = 3051131) B3051131
theorem B2288353 : Blo 2033435 2288353 := bbase (se 2 (by rfl) ⟨858132, by rfl⟩ : syracuseStep 2288353 = 1716265) (by norm_num)
theorem B3051137 : Blo 2033435 3051137 := bstep (se 2 (by rfl) ⟨1144176, by rfl⟩ : syracuseStep 3051137 = 2288353) B2288353
theorem B2034091 : Blo 2033435 2034091 := bstep (se 1 (by rfl) ⟨1525568, by rfl⟩ : syracuseStep 2034091 = 3051137) B3051137
theorem B5148805 : Blo 2033435 5148805 := bbase (se 4 (by rfl) ⟨482700, by rfl⟩ : syracuseStep 5148805 = 965401) (by norm_num)
theorem B6865073 : Blo 2033435 6865073 := bstep (se 2 (by rfl) ⟨2574402, by rfl⟩ : syracuseStep 6865073 = 5148805) B5148805
theorem B4576715 : Blo 2033435 4576715 := bstep (se 1 (by rfl) ⟨3432536, by rfl⟩ : syracuseStep 4576715 = 6865073) B6865073
theorem B3051143 : Blo 2033435 3051143 := bstep (se 1 (by rfl) ⟨2288357, by rfl⟩ : syracuseStep 3051143 = 4576715) B4576715
theorem B2034095 : Blo 2033435 2034095 := bstep (se 1 (by rfl) ⟨1525571, by rfl⟩ : syracuseStep 2034095 = 3051143) B3051143
theorem B3051149 : Blo 2033435 3051149 := bbase (se 3 (by rfl) ⟨572090, by rfl⟩ : syracuseStep 3051149 = 1144181) (by norm_num)
theorem B2034099 : Blo 2033435 2034099 := bstep (se 1 (by rfl) ⟨1525574, by rfl⟩ : syracuseStep 2034099 = 3051149) B3051149
theorem B4576733 : Blo 2033435 4576733 := bbase (se 3 (by rfl) ⟨858137, by rfl⟩ : syracuseStep 4576733 = 1716275) (by norm_num)
theorem B3051155 : Blo 2033435 3051155 := bstep (se 1 (by rfl) ⟨2288366, by rfl⟩ : syracuseStep 3051155 = 4576733) B4576733
theorem B2034103 : Blo 2033435 2034103 := bstep (se 1 (by rfl) ⟨1525577, by rfl⟩ : syracuseStep 2034103 = 3051155) B3051155
theorem B3432557 : Blo 2033435 3432557 := bbase (se 3 (by rfl) ⟨643604, by rfl⟩ : syracuseStep 3432557 = 1287209) (by norm_num)
theorem B2288371 : Blo 2033435 2288371 := bstep (se 1 (by rfl) ⟨1716278, by rfl⟩ : syracuseStep 2288371 = 3432557) B3432557
theorem B3051161 : Blo 2033435 3051161 := bstep (se 2 (by rfl) ⟨1144185, by rfl⟩ : syracuseStep 3051161 = 2288371) B2288371
theorem B2034107 : Blo 2033435 2034107 := bstep (se 1 (by rfl) ⟨1525580, by rfl⟩ : syracuseStep 2034107 = 3051161) B3051161
theorem B19549525 : Blo 2033435 19549525 := bbase (se 11 (by rfl) ⟨14318, by rfl⟩ : syracuseStep 19549525 = 28637) (by norm_num)
theorem B26066033 : Blo 2033435 26066033 := bstep (se 2 (by rfl) ⟨9774762, by rfl⟩ : syracuseStep 26066033 = 19549525) B19549525
theorem B17377355 : Blo 2033435 17377355 := bstep (se 1 (by rfl) ⟨13033016, by rfl⟩ : syracuseStep 17377355 = 26066033) B26066033
theorem B11584903 : Blo 2033435 11584903 := bstep (se 1 (by rfl) ⟨8688677, by rfl⟩ : syracuseStep 11584903 = 17377355) B17377355
theorem B15446537 : Blo 2033435 15446537 := bstep (se 2 (by rfl) ⟨5792451, by rfl⟩ : syracuseStep 15446537 = 11584903) B11584903
theorem B10297691 : Blo 2033435 10297691 := bstep (se 1 (by rfl) ⟨7723268, by rfl⟩ : syracuseStep 10297691 = 15446537) B15446537
theorem B6865127 : Blo 2033435 6865127 := bstep (se 1 (by rfl) ⟨5148845, by rfl⟩ : syracuseStep 6865127 = 10297691) B10297691
theorem B4576751 : Blo 2033435 4576751 := bstep (se 1 (by rfl) ⟨3432563, by rfl⟩ : syracuseStep 4576751 = 6865127) B6865127
theorem B3051167 : Blo 2033435 3051167 := bstep (se 1 (by rfl) ⟨2288375, by rfl⟩ : syracuseStep 3051167 = 4576751) B4576751
theorem B2034111 : Blo 2033435 2034111 := bstep (se 1 (by rfl) ⟨1525583, by rfl⟩ : syracuseStep 2034111 = 3051167) B3051167
theorem B3051173 : Blo 2033435 3051173 := bbase (se 4 (by rfl) ⟨286047, by rfl⟩ : syracuseStep 3051173 = 572095) (by norm_num)
theorem B2034115 : Blo 2033435 2034115 := bstep (se 1 (by rfl) ⟨1525586, by rfl⟩ : syracuseStep 2034115 = 3051173) B3051173
theorem B2574433 : Blo 2033435 2574433 := bbase (se 2 (by rfl) ⟨965412, by rfl⟩ : syracuseStep 2574433 = 1930825) (by norm_num)
theorem B3432577 : Blo 2033435 3432577 := bstep (se 2 (by rfl) ⟨1287216, by rfl⟩ : syracuseStep 3432577 = 2574433) B2574433
theorem B4576769 : Blo 2033435 4576769 := bstep (se 2 (by rfl) ⟨1716288, by rfl⟩ : syracuseStep 4576769 = 3432577) B3432577
theorem B3051179 : Blo 2033435 3051179 := bstep (se 1 (by rfl) ⟨2288384, by rfl⟩ : syracuseStep 3051179 = 4576769) B4576769
theorem B2034119 : Blo 2033435 2034119 := bstep (se 1 (by rfl) ⟨1525589, by rfl⟩ : syracuseStep 2034119 = 3051179) B3051179
theorem B2288389 : Blo 2033435 2288389 := bbase (se 4 (by rfl) ⟨214536, by rfl⟩ : syracuseStep 2288389 = 429073) (by norm_num)
theorem B3051185 : Blo 2033435 3051185 := bstep (se 2 (by rfl) ⟨1144194, by rfl⟩ : syracuseStep 3051185 = 2288389) B2288389
theorem B2034123 : Blo 2033435 2034123 := bstep (se 1 (by rfl) ⟨1525592, by rfl⟩ : syracuseStep 2034123 = 3051185) B3051185
theorem B7053797 : Blo 2033435 7053797 := bbase (se 4 (by rfl) ⟨661293, by rfl⟩ : syracuseStep 7053797 = 1322587) (by norm_num)
theorem B4702531 : Blo 2033435 4702531 := bstep (se 1 (by rfl) ⟨3526898, by rfl⟩ : syracuseStep 4702531 = 7053797) B7053797
theorem B6270041 : Blo 2033435 6270041 := bstep (se 2 (by rfl) ⟨2351265, by rfl⟩ : syracuseStep 6270041 = 4702531) B4702531
theorem B4180027 : Blo 2033435 4180027 := bstep (se 1 (by rfl) ⟨3135020, by rfl⟩ : syracuseStep 4180027 = 6270041) B6270041
theorem B5573369 : Blo 2033435 5573369 := bstep (se 2 (by rfl) ⟨2090013, by rfl⟩ : syracuseStep 5573369 = 4180027) B4180027
theorem B3715579 : Blo 2033435 3715579 := bstep (se 1 (by rfl) ⟨2786684, by rfl⟩ : syracuseStep 3715579 = 5573369) B5573369
theorem B4954105 : Blo 2033435 4954105 := bstep (se 2 (by rfl) ⟨1857789, by rfl⟩ : syracuseStep 4954105 = 3715579) B3715579
theorem B6605473 : Blo 2033435 6605473 := bstep (se 2 (by rfl) ⟨2477052, by rfl⟩ : syracuseStep 6605473 = 4954105) B4954105
theorem B8807297 : Blo 2033435 8807297 := bstep (se 2 (by rfl) ⟨3302736, by rfl⟩ : syracuseStep 8807297 = 6605473) B6605473
theorem B23486125 : Blo 2033435 23486125 := bstep (se 3 (by rfl) ⟨4403648, by rfl⟩ : syracuseStep 23486125 = 8807297) B8807297
theorem B31314833 : Blo 2033435 31314833 := bstep (se 2 (by rfl) ⟨11743062, by rfl⟩ : syracuseStep 31314833 = 23486125) B23486125
theorem B20876555 : Blo 2033435 20876555 := bstep (se 1 (by rfl) ⟨15657416, by rfl⟩ : syracuseStep 20876555 = 31314833) B31314833
theorem B13917703 : Blo 2033435 13917703 := bstep (se 1 (by rfl) ⟨10438277, by rfl⟩ : syracuseStep 13917703 = 20876555) B20876555
theorem B18556937 : Blo 2033435 18556937 := bstep (se 2 (by rfl) ⟨6958851, by rfl⟩ : syracuseStep 18556937 = 13917703) B13917703
theorem B12371291 : Blo 2033435 12371291 := bstep (se 1 (by rfl) ⟨9278468, by rfl⟩ : syracuseStep 12371291 = 18556937) B18556937
theorem B8247527 : Blo 2033435 8247527 := bstep (se 1 (by rfl) ⟨6185645, by rfl⟩ : syracuseStep 8247527 = 12371291) B12371291
theorem B5498351 : Blo 2033435 5498351 := bstep (se 1 (by rfl) ⟨4123763, by rfl⟩ : syracuseStep 5498351 = 8247527) B8247527
theorem B3665567 : Blo 2033435 3665567 := bstep (se 1 (by rfl) ⟨2749175, by rfl⟩ : syracuseStep 3665567 = 5498351) B5498351
theorem B2443711 : Blo 2033435 2443711 := bstep (se 1 (by rfl) ⟨1832783, by rfl⟩ : syracuseStep 2443711 = 3665567) B3665567
theorem B3258281 : Blo 2033435 3258281 := bstep (se 2 (by rfl) ⟨1221855, by rfl⟩ : syracuseStep 3258281 = 2443711) B2443711
theorem B2172187 : Blo 2033435 2172187 := bstep (se 1 (by rfl) ⟨1629140, by rfl⟩ : syracuseStep 2172187 = 3258281) B3258281
theorem B2896249 : Blo 2033435 2896249 := bstep (se 2 (by rfl) ⟨1086093, by rfl⟩ : syracuseStep 2896249 = 2172187) B2172187
theorem B3861665 : Blo 2033435 3861665 := bstep (se 2 (by rfl) ⟨1448124, by rfl⟩ : syracuseStep 3861665 = 2896249) B2896249
theorem B2574443 : Blo 2033435 2574443 := bstep (se 1 (by rfl) ⟨1930832, by rfl⟩ : syracuseStep 2574443 = 3861665) B3861665
theorem B6865181 : Blo 2033435 6865181 := bstep (se 3 (by rfl) ⟨1287221, by rfl⟩ : syracuseStep 6865181 = 2574443) B2574443
theorem B4576787 : Blo 2033435 4576787 := bstep (se 1 (by rfl) ⟨3432590, by rfl⟩ : syracuseStep 4576787 = 6865181) B6865181
theorem B3051191 : Blo 2033435 3051191 := bstep (se 1 (by rfl) ⟨2288393, by rfl⟩ : syracuseStep 3051191 = 4576787) B4576787
theorem B2034127 : Blo 2033435 2034127 := bstep (se 1 (by rfl) ⟨1525595, by rfl⟩ : syracuseStep 2034127 = 3051191) B3051191
theorem B3051197 : Blo 2033435 3051197 := bbase (se 3 (by rfl) ⟨572099, by rfl⟩ : syracuseStep 3051197 = 1144199) (by norm_num)
theorem B2034131 : Blo 2033435 2034131 := bstep (se 1 (by rfl) ⟨1525598, by rfl⟩ : syracuseStep 2034131 = 3051197) B3051197
theorem B4576805 : Blo 2033435 4576805 := bbase (se 4 (by rfl) ⟨429075, by rfl⟩ : syracuseStep 4576805 = 858151) (by norm_num)
theorem B3051203 : Blo 2033435 3051203 := bstep (se 1 (by rfl) ⟨2288402, by rfl⟩ : syracuseStep 3051203 = 4576805) B4576805
theorem B2034135 : Blo 2033435 2034135 := bstep (se 1 (by rfl) ⟨1525601, by rfl⟩ : syracuseStep 2034135 = 3051203) B3051203
theorem B5148917 : Blo 2033435 5148917 := bbase (se 5 (by rfl) ⟨241355, by rfl⟩ : syracuseStep 5148917 = 482711) (by norm_num)
theorem B3432611 : Blo 2033435 3432611 := bstep (se 1 (by rfl) ⟨2574458, by rfl⟩ : syracuseStep 3432611 = 5148917) B5148917
theorem B2288407 : Blo 2033435 2288407 := bstep (se 1 (by rfl) ⟨1716305, by rfl⟩ : syracuseStep 2288407 = 3432611) B3432611
theorem B3051209 : Blo 2033435 3051209 := bstep (se 2 (by rfl) ⟨1144203, by rfl⟩ : syracuseStep 3051209 = 2288407) B2288407
theorem B2034139 : Blo 2033435 2034139 := bstep (se 1 (by rfl) ⟨1525604, by rfl⟩ : syracuseStep 2034139 = 3051209) B3051209
theorem B12371381 : Blo 2033435 12371381 := bbase (se 5 (by rfl) ⟨579908, by rfl⟩ : syracuseStep 12371381 = 1159817) (by norm_num)
theorem B8247587 : Blo 2033435 8247587 := bstep (se 1 (by rfl) ⟨6185690, by rfl⟩ : syracuseStep 8247587 = 12371381) B12371381
theorem B21993565 : Blo 2033435 21993565 := bstep (se 3 (by rfl) ⟨4123793, by rfl⟩ : syracuseStep 21993565 = 8247587) B8247587
theorem B29324753 : Blo 2033435 29324753 := bstep (se 2 (by rfl) ⟨10996782, by rfl⟩ : syracuseStep 29324753 = 21993565) B21993565
theorem B19549835 : Blo 2033435 19549835 := bstep (se 1 (by rfl) ⟨14662376, by rfl⟩ : syracuseStep 19549835 = 29324753) B29324753
theorem B13033223 : Blo 2033435 13033223 := bstep (se 1 (by rfl) ⟨9774917, by rfl⟩ : syracuseStep 13033223 = 19549835) B19549835
theorem B8688815 : Blo 2033435 8688815 := bstep (se 1 (by rfl) ⟨6516611, by rfl⟩ : syracuseStep 8688815 = 13033223) B13033223
theorem B5792543 : Blo 2033435 5792543 := bstep (se 1 (by rfl) ⟨4344407, by rfl⟩ : syracuseStep 5792543 = 8688815) B8688815
theorem B3861695 : Blo 2033435 3861695 := bstep (se 1 (by rfl) ⟨2896271, by rfl⟩ : syracuseStep 3861695 = 5792543) B5792543
theorem B10297853 : Blo 2033435 10297853 := bstep (se 3 (by rfl) ⟨1930847, by rfl⟩ : syracuseStep 10297853 = 3861695) B3861695
theorem B6865235 : Blo 2033435 6865235 := bstep (se 1 (by rfl) ⟨5148926, by rfl⟩ : syracuseStep 6865235 = 10297853) B10297853
theorem B4576823 : Blo 2033435 4576823 := bstep (se 1 (by rfl) ⟨3432617, by rfl⟩ : syracuseStep 4576823 = 6865235) B6865235
theorem B3051215 : Blo 2033435 3051215 := bstep (se 1 (by rfl) ⟨2288411, by rfl⟩ : syracuseStep 3051215 = 4576823) B4576823
theorem B2034143 : Blo 2033435 2034143 := bstep (se 1 (by rfl) ⟨1525607, by rfl⟩ : syracuseStep 2034143 = 3051215) B3051215
theorem B3051221 : Blo 2033435 3051221 := bbase (se 7 (by rfl) ⟨35756, by rfl⟩ : syracuseStep 3051221 = 71513) (by norm_num)
theorem B2034147 : Blo 2033435 2034147 := bstep (se 1 (by rfl) ⟨1525610, by rfl⟩ : syracuseStep 2034147 = 3051221) B3051221
theorem B6185717 : Blo 2033435 6185717 := bbase (se 5 (by rfl) ⟨289955, by rfl⟩ : syracuseStep 6185717 = 579911) (by norm_num)
theorem B4123811 : Blo 2033435 4123811 := bstep (se 1 (by rfl) ⟨3092858, by rfl⟩ : syracuseStep 4123811 = 6185717) B6185717
theorem B10996829 : Blo 2033435 10996829 := bstep (se 3 (by rfl) ⟨2061905, by rfl⟩ : syracuseStep 10996829 = 4123811) B4123811
theorem B7331219 : Blo 2033435 7331219 := bstep (se 1 (by rfl) ⟨5498414, by rfl⟩ : syracuseStep 7331219 = 10996829) B10996829
theorem B4887479 : Blo 2033435 4887479 := bstep (se 1 (by rfl) ⟨3665609, by rfl⟩ : syracuseStep 4887479 = 7331219) B7331219
theorem B3258319 : Blo 2033435 3258319 := bstep (se 1 (by rfl) ⟨2443739, by rfl⟩ : syracuseStep 3258319 = 4887479) B4887479
theorem B4344425 : Blo 2033435 4344425 := bstep (se 2 (by rfl) ⟨1629159, by rfl⟩ : syracuseStep 4344425 = 3258319) B3258319
theorem B2896283 : Blo 2033435 2896283 := bstep (se 1 (by rfl) ⟨2172212, by rfl⟩ : syracuseStep 2896283 = 4344425) B4344425
theorem B7723421 : Blo 2033435 7723421 := bstep (se 3 (by rfl) ⟨1448141, by rfl⟩ : syracuseStep 7723421 = 2896283) B2896283
theorem B5148947 : Blo 2033435 5148947 := bstep (se 1 (by rfl) ⟨3861710, by rfl⟩ : syracuseStep 5148947 = 7723421) B7723421
theorem B3432631 : Blo 2033435 3432631 := bstep (se 1 (by rfl) ⟨2574473, by rfl⟩ : syracuseStep 3432631 = 5148947) B5148947
theorem B4576841 : Blo 2033435 4576841 := bstep (se 2 (by rfl) ⟨1716315, by rfl⟩ : syracuseStep 4576841 = 3432631) B3432631
theorem B3051227 : Blo 2033435 3051227 := bstep (se 1 (by rfl) ⟨2288420, by rfl⟩ : syracuseStep 3051227 = 4576841) B4576841
theorem B2034151 : Blo 2033435 2034151 := bstep (se 1 (by rfl) ⟨1525613, by rfl⟩ : syracuseStep 2034151 = 3051227) B3051227
theorem B2288425 : Blo 2033435 2288425 := bbase (se 2 (by rfl) ⟨858159, by rfl⟩ : syracuseStep 2288425 = 1716319) (by norm_num)
theorem B3051233 : Blo 2033435 3051233 := bstep (se 2 (by rfl) ⟨1144212, by rfl⟩ : syracuseStep 3051233 = 2288425) B2288425
theorem B2034155 : Blo 2033435 2034155 := bstep (se 1 (by rfl) ⟨1525616, by rfl⟩ : syracuseStep 2034155 = 3051233) B3051233
theorem B8247653 : Blo 2033435 8247653 := bbase (se 4 (by rfl) ⟨773217, by rfl⟩ : syracuseStep 8247653 = 1546435) (by norm_num)
theorem B5498435 : Blo 2033435 5498435 := bstep (se 1 (by rfl) ⟨4123826, by rfl⟩ : syracuseStep 5498435 = 8247653) B8247653
theorem B3665623 : Blo 2033435 3665623 := bstep (se 1 (by rfl) ⟨2749217, by rfl⟩ : syracuseStep 3665623 = 5498435) B5498435
theorem B4887497 : Blo 2033435 4887497 := bstep (se 2 (by rfl) ⟨1832811, by rfl⟩ : syracuseStep 4887497 = 3665623) B3665623
theorem B13033325 : Blo 2033435 13033325 := bstep (se 3 (by rfl) ⟨2443748, by rfl⟩ : syracuseStep 13033325 = 4887497) B4887497
theorem B8688883 : Blo 2033435 8688883 := bstep (se 1 (by rfl) ⟨6516662, by rfl⟩ : syracuseStep 8688883 = 13033325) B13033325
theorem B11585177 : Blo 2033435 11585177 := bstep (se 2 (by rfl) ⟨4344441, by rfl⟩ : syracuseStep 11585177 = 8688883) B8688883
theorem B7723451 : Blo 2033435 7723451 := bstep (se 1 (by rfl) ⟨5792588, by rfl⟩ : syracuseStep 7723451 = 11585177) B11585177
theorem B5148967 : Blo 2033435 5148967 := bstep (se 1 (by rfl) ⟨3861725, by rfl⟩ : syracuseStep 5148967 = 7723451) B7723451
theorem B6865289 : Blo 2033435 6865289 := bstep (se 2 (by rfl) ⟨2574483, by rfl⟩ : syracuseStep 6865289 = 5148967) B5148967
theorem B4576859 : Blo 2033435 4576859 := bstep (se 1 (by rfl) ⟨3432644, by rfl⟩ : syracuseStep 4576859 = 6865289) B6865289
theorem B3051239 : Blo 2033435 3051239 := bstep (se 1 (by rfl) ⟨2288429, by rfl⟩ : syracuseStep 3051239 = 4576859) B4576859
theorem B2034159 : Blo 2033435 2034159 := bstep (se 1 (by rfl) ⟨1525619, by rfl⟩ : syracuseStep 2034159 = 3051239) B3051239
theorem B3051245 : Blo 2033435 3051245 := bbase (se 3 (by rfl) ⟨572108, by rfl⟩ : syracuseStep 3051245 = 1144217) (by norm_num)
theorem B2034163 : Blo 2033435 2034163 := bstep (se 1 (by rfl) ⟨1525622, by rfl⟩ : syracuseStep 2034163 = 3051245) B3051245
theorem B4576877 : Blo 2033435 4576877 := bbase (se 3 (by rfl) ⟨858164, by rfl⟩ : syracuseStep 4576877 = 1716329) (by norm_num)
theorem B3051251 : Blo 2033435 3051251 := bstep (se 1 (by rfl) ⟨2288438, by rfl⟩ : syracuseStep 3051251 = 4576877) B4576877
theorem B2034167 : Blo 2033435 2034167 := bstep (se 1 (by rfl) ⟨1525625, by rfl⟩ : syracuseStep 2034167 = 3051251) B3051251
theorem B3861749 : Blo 2033435 3861749 := bbase (se 5 (by rfl) ⟨181019, by rfl⟩ : syracuseStep 3861749 = 362039) (by norm_num)
theorem B2574499 : Blo 2033435 2574499 := bstep (se 1 (by rfl) ⟨1930874, by rfl⟩ : syracuseStep 2574499 = 3861749) B3861749
theorem B3432665 : Blo 2033435 3432665 := bstep (se 2 (by rfl) ⟨1287249, by rfl⟩ : syracuseStep 3432665 = 2574499) B2574499
theorem B2288443 : Blo 2033435 2288443 := bstep (se 1 (by rfl) ⟨1716332, by rfl⟩ : syracuseStep 2288443 = 3432665) B3432665
theorem B3051257 : Blo 2033435 3051257 := bstep (se 2 (by rfl) ⟨1144221, by rfl⟩ : syracuseStep 3051257 = 2288443) B2288443
theorem B2034171 : Blo 2033435 2034171 := bstep (se 1 (by rfl) ⟨1525628, by rfl⟩ : syracuseStep 2034171 = 3051257) B3051257
theorem B12371573 : Blo 2033435 12371573 := bbase (se 5 (by rfl) ⟨579917, by rfl⟩ : syracuseStep 12371573 = 1159835) (by norm_num)
theorem B32990861 : Blo 2033435 32990861 := bstep (se 3 (by rfl) ⟨6185786, by rfl⟩ : syracuseStep 32990861 = 12371573) B12371573
theorem B87975629 : Blo 2033435 87975629 := bstep (se 3 (by rfl) ⟨16495430, by rfl⟩ : syracuseStep 87975629 = 32990861) B32990861
theorem B58650419 : Blo 2033435 58650419 := bstep (se 1 (by rfl) ⟨43987814, by rfl⟩ : syracuseStep 58650419 = 87975629) B87975629
theorem B39100279 : Blo 2033435 39100279 := bstep (se 1 (by rfl) ⟨29325209, by rfl⟩ : syracuseStep 39100279 = 58650419) B58650419
theorem B52133705 : Blo 2033435 52133705 := bstep (se 2 (by rfl) ⟨19550139, by rfl⟩ : syracuseStep 52133705 = 39100279) B39100279
theorem B34755803 : Blo 2033435 34755803 := bstep (se 1 (by rfl) ⟨26066852, by rfl⟩ : syracuseStep 34755803 = 52133705) B52133705
theorem B23170535 : Blo 2033435 23170535 := bstep (se 1 (by rfl) ⟨17377901, by rfl⟩ : syracuseStep 23170535 = 34755803) B34755803
theorem B15447023 : Blo 2033435 15447023 := bstep (se 1 (by rfl) ⟨11585267, by rfl⟩ : syracuseStep 15447023 = 23170535) B23170535
theorem B10298015 : Blo 2033435 10298015 := bstep (se 1 (by rfl) ⟨7723511, by rfl⟩ : syracuseStep 10298015 = 15447023) B15447023
theorem B6865343 : Blo 2033435 6865343 := bstep (se 1 (by rfl) ⟨5149007, by rfl⟩ : syracuseStep 6865343 = 10298015) B10298015
theorem B4576895 : Blo 2033435 4576895 := bstep (se 1 (by rfl) ⟨3432671, by rfl⟩ : syracuseStep 4576895 = 6865343) B6865343
theorem B3051263 : Blo 2033435 3051263 := bstep (se 1 (by rfl) ⟨2288447, by rfl⟩ : syracuseStep 3051263 = 4576895) B4576895
theorem B2034175 : Blo 2033435 2034175 := bstep (se 1 (by rfl) ⟨1525631, by rfl⟩ : syracuseStep 2034175 = 3051263) B3051263
theorem B3051269 : Blo 2033435 3051269 := bbase (se 4 (by rfl) ⟨286056, by rfl⟩ : syracuseStep 3051269 = 572113) (by norm_num)
theorem B2034179 : Blo 2033435 2034179 := bstep (se 1 (by rfl) ⟨1525634, by rfl⟩ : syracuseStep 2034179 = 3051269) B3051269
theorem B3432685 : Blo 2033435 3432685 := bbase (se 3 (by rfl) ⟨643628, by rfl⟩ : syracuseStep 3432685 = 1287257) (by norm_num)
theorem B4576913 : Blo 2033435 4576913 := bstep (se 2 (by rfl) ⟨1716342, by rfl⟩ : syracuseStep 4576913 = 3432685) B3432685
theorem B3051275 : Blo 2033435 3051275 := bstep (se 1 (by rfl) ⟨2288456, by rfl⟩ : syracuseStep 3051275 = 4576913) B4576913
theorem B2034183 : Blo 2033435 2034183 := bstep (se 1 (by rfl) ⟨1525637, by rfl⟩ : syracuseStep 2034183 = 3051275) B3051275
theorem B2288461 : Blo 2033435 2288461 := bbase (se 3 (by rfl) ⟨429086, by rfl⟩ : syracuseStep 2288461 = 858173) (by norm_num)
theorem B3051281 : Blo 2033435 3051281 := bstep (se 2 (by rfl) ⟨1144230, by rfl⟩ : syracuseStep 3051281 = 2288461) B2288461
theorem B2034187 : Blo 2033435 2034187 := bstep (se 1 (by rfl) ⟨1525640, by rfl⟩ : syracuseStep 2034187 = 3051281) B3051281
theorem B6865397 : Blo 2033435 6865397 := bbase (se 5 (by rfl) ⟨321815, by rfl⟩ : syracuseStep 6865397 = 643631) (by norm_num)
theorem B4576931 : Blo 2033435 4576931 := bstep (se 1 (by rfl) ⟨3432698, by rfl⟩ : syracuseStep 4576931 = 6865397) B6865397
theorem B3051287 : Blo 2033435 3051287 := bstep (se 1 (by rfl) ⟨2288465, by rfl⟩ : syracuseStep 3051287 = 4576931) B4576931
theorem B2034191 : Blo 2033435 2034191 := bstep (se 1 (by rfl) ⟨1525643, by rfl⟩ : syracuseStep 2034191 = 3051287) B3051287
theorem B3051293 : Blo 2033435 3051293 := bbase (se 3 (by rfl) ⟨572117, by rfl⟩ : syracuseStep 3051293 = 1144235) (by norm_num)
theorem B2034195 : Blo 2033435 2034195 := bstep (se 1 (by rfl) ⟨1525646, by rfl⟩ : syracuseStep 2034195 = 3051293) B3051293
theorem B4576949 : Blo 2033435 4576949 := bbase (se 5 (by rfl) ⟨214544, by rfl⟩ : syracuseStep 4576949 = 429089) (by norm_num)
theorem B3051299 : Blo 2033435 3051299 := bstep (se 1 (by rfl) ⟨2288474, by rfl⟩ : syracuseStep 3051299 = 4576949) B4576949
theorem B2034199 : Blo 2033435 2034199 := bstep (se 1 (by rfl) ⟨1525649, by rfl⟩ : syracuseStep 2034199 = 3051299) B3051299
theorem B11585429 : Blo 2033435 11585429 := bbase (se 6 (by rfl) ⟨271533, by rfl⟩ : syracuseStep 11585429 = 543067) (by norm_num)
theorem B7723619 : Blo 2033435 7723619 := bstep (se 1 (by rfl) ⟨5792714, by rfl⟩ : syracuseStep 7723619 = 11585429) B11585429
theorem B5149079 : Blo 2033435 5149079 := bstep (se 1 (by rfl) ⟨3861809, by rfl⟩ : syracuseStep 5149079 = 7723619) B7723619
theorem B3432719 : Blo 2033435 3432719 := bstep (se 1 (by rfl) ⟨2574539, by rfl⟩ : syracuseStep 3432719 = 5149079) B5149079
theorem B2288479 : Blo 2033435 2288479 := bstep (se 1 (by rfl) ⟨1716359, by rfl⟩ : syracuseStep 2288479 = 3432719) B3432719
theorem B3051305 : Blo 2033435 3051305 := bstep (se 2 (by rfl) ⟨1144239, by rfl⟩ : syracuseStep 3051305 = 2288479) B2288479
theorem B2034203 : Blo 2033435 2034203 := bstep (se 1 (by rfl) ⟨1525652, by rfl⟩ : syracuseStep 2034203 = 3051305) B3051305
theorem B5792725 : Blo 2033435 5792725 := bbase (se 7 (by rfl) ⟨67883, by rfl⟩ : syracuseStep 5792725 = 135767) (by norm_num)
theorem B7723633 : Blo 2033435 7723633 := bstep (se 2 (by rfl) ⟨2896362, by rfl⟩ : syracuseStep 7723633 = 5792725) B5792725
theorem B10298177 : Blo 2033435 10298177 := bstep (se 2 (by rfl) ⟨3861816, by rfl⟩ : syracuseStep 10298177 = 7723633) B7723633
theorem B6865451 : Blo 2033435 6865451 := bstep (se 1 (by rfl) ⟨5149088, by rfl⟩ : syracuseStep 6865451 = 10298177) B10298177
theorem B4576967 : Blo 2033435 4576967 := bstep (se 1 (by rfl) ⟨3432725, by rfl⟩ : syracuseStep 4576967 = 6865451) B6865451
theorem B3051311 : Blo 2033435 3051311 := bstep (se 1 (by rfl) ⟨2288483, by rfl⟩ : syracuseStep 3051311 = 4576967) B4576967
theorem B2034207 : Blo 2033435 2034207 := bstep (se 1 (by rfl) ⟨1525655, by rfl⟩ : syracuseStep 2034207 = 3051311) B3051311
theorem B3051317 : Blo 2033435 3051317 := bbase (se 5 (by rfl) ⟨143030, by rfl⟩ : syracuseStep 3051317 = 286061) (by norm_num)
theorem B2034211 : Blo 2033435 2034211 := bstep (se 1 (by rfl) ⟨1525658, by rfl⟩ : syracuseStep 2034211 = 3051317) B3051317
theorem B5149109 : Blo 2033435 5149109 := bbase (se 5 (by rfl) ⟨241364, by rfl⟩ : syracuseStep 5149109 = 482729) (by norm_num)
theorem B3432739 : Blo 2033435 3432739 := bstep (se 1 (by rfl) ⟨2574554, by rfl⟩ : syracuseStep 3432739 = 5149109) B5149109
theorem B4576985 : Blo 2033435 4576985 := bstep (se 2 (by rfl) ⟨1716369, by rfl⟩ : syracuseStep 4576985 = 3432739) B3432739
theorem B3051323 : Blo 2033435 3051323 := bstep (se 1 (by rfl) ⟨2288492, by rfl⟩ : syracuseStep 3051323 = 4576985) B4576985
theorem B2034215 : Blo 2033435 2034215 := bstep (se 1 (by rfl) ⟨1525661, by rfl⟩ : syracuseStep 2034215 = 3051323) B3051323
theorem B2288497 : Blo 2033435 2288497 := bbase (se 2 (by rfl) ⟨858186, by rfl⟩ : syracuseStep 2288497 = 1716373) (by norm_num)
theorem B3051329 : Blo 2033435 3051329 := bstep (se 2 (by rfl) ⟨1144248, by rfl⟩ : syracuseStep 3051329 = 2288497) B2288497
theorem B2034219 : Blo 2033435 2034219 := bstep (se 1 (by rfl) ⟨1525664, by rfl⟩ : syracuseStep 2034219 = 3051329) B3051329
theorem B8689157 : Blo 2033435 8689157 := bbase (se 4 (by rfl) ⟨814608, by rfl⟩ : syracuseStep 8689157 = 1629217) (by norm_num)
theorem B5792771 : Blo 2033435 5792771 := bstep (se 1 (by rfl) ⟨4344578, by rfl⟩ : syracuseStep 5792771 = 8689157) B8689157
theorem B3861847 : Blo 2033435 3861847 := bstep (se 1 (by rfl) ⟨2896385, by rfl⟩ : syracuseStep 3861847 = 5792771) B5792771
theorem B5149129 : Blo 2033435 5149129 := bstep (se 2 (by rfl) ⟨1930923, by rfl⟩ : syracuseStep 5149129 = 3861847) B3861847
theorem B6865505 : Blo 2033435 6865505 := bstep (se 2 (by rfl) ⟨2574564, by rfl⟩ : syracuseStep 6865505 = 5149129) B5149129
theorem B4577003 : Blo 2033435 4577003 := bstep (se 1 (by rfl) ⟨3432752, by rfl⟩ : syracuseStep 4577003 = 6865505) B6865505
theorem B3051335 : Blo 2033435 3051335 := bstep (se 1 (by rfl) ⟨2288501, by rfl⟩ : syracuseStep 3051335 = 4577003) B4577003
theorem B2034223 : Blo 2033435 2034223 := bstep (se 1 (by rfl) ⟨1525667, by rfl⟩ : syracuseStep 2034223 = 3051335) B3051335
theorem B3051341 : Blo 2033435 3051341 := bbase (se 3 (by rfl) ⟨572126, by rfl⟩ : syracuseStep 3051341 = 1144253) (by norm_num)
theorem B2034227 : Blo 2033435 2034227 := bstep (se 1 (by rfl) ⟨1525670, by rfl⟩ : syracuseStep 2034227 = 3051341) B3051341
theorem B4577021 : Blo 2033435 4577021 := bbase (se 3 (by rfl) ⟨858191, by rfl⟩ : syracuseStep 4577021 = 1716383) (by norm_num)
theorem B3051347 : Blo 2033435 3051347 := bstep (se 1 (by rfl) ⟨2288510, by rfl⟩ : syracuseStep 3051347 = 4577021) B4577021
theorem B2034231 : Blo 2033435 2034231 := bstep (se 1 (by rfl) ⟨1525673, by rfl⟩ : syracuseStep 2034231 = 3051347) B3051347
theorem B3432773 : Blo 2033435 3432773 := bbase (se 4 (by rfl) ⟨321822, by rfl⟩ : syracuseStep 3432773 = 643645) (by norm_num)
theorem B2288515 : Blo 2033435 2288515 := bstep (se 1 (by rfl) ⟨1716386, by rfl⟩ : syracuseStep 2288515 = 3432773) B3432773
theorem B3051353 : Blo 2033435 3051353 := bstep (se 2 (by rfl) ⟨1144257, by rfl⟩ : syracuseStep 3051353 = 2288515) B2288515
theorem B2034235 : Blo 2033435 2034235 := bstep (se 1 (by rfl) ⟨1525676, by rfl⟩ : syracuseStep 2034235 = 3051353) B3051353
theorem B15447509 : Blo 2033435 15447509 := bbase (se 7 (by rfl) ⟨181025, by rfl⟩ : syracuseStep 15447509 = 362051) (by norm_num)
theorem B10298339 : Blo 2033435 10298339 := bstep (se 1 (by rfl) ⟨7723754, by rfl⟩ : syracuseStep 10298339 = 15447509) B15447509
theorem B6865559 : Blo 2033435 6865559 := bstep (se 1 (by rfl) ⟨5149169, by rfl⟩ : syracuseStep 6865559 = 10298339) B10298339
theorem B4577039 : Blo 2033435 4577039 := bstep (se 1 (by rfl) ⟨3432779, by rfl⟩ : syracuseStep 4577039 = 6865559) B6865559
theorem B3051359 : Blo 2033435 3051359 := bstep (se 1 (by rfl) ⟨2288519, by rfl⟩ : syracuseStep 3051359 = 4577039) B4577039
theorem B2034239 : Blo 2033435 2034239 := bstep (se 1 (by rfl) ⟨1525679, by rfl⟩ : syracuseStep 2034239 = 3051359) B3051359
theorem B3051365 : Blo 2033435 3051365 := bbase (se 4 (by rfl) ⟨286065, by rfl⟩ : syracuseStep 3051365 = 572131) (by norm_num)
theorem B2034243 : Blo 2033435 2034243 := bstep (se 1 (by rfl) ⟨1525682, by rfl⟩ : syracuseStep 2034243 = 3051365) B3051365
theorem B3861893 : Blo 2033435 3861893 := bbase (se 4 (by rfl) ⟨362052, by rfl⟩ : syracuseStep 3861893 = 724105) (by norm_num)
theorem B2574595 : Blo 2033435 2574595 := bstep (se 1 (by rfl) ⟨1930946, by rfl⟩ : syracuseStep 2574595 = 3861893) B3861893
theorem B3432793 : Blo 2033435 3432793 := bstep (se 2 (by rfl) ⟨1287297, by rfl⟩ : syracuseStep 3432793 = 2574595) B2574595
theorem B4577057 : Blo 2033435 4577057 := bstep (se 2 (by rfl) ⟨1716396, by rfl⟩ : syracuseStep 4577057 = 3432793) B3432793
theorem B3051371 : Blo 2033435 3051371 := bstep (se 1 (by rfl) ⟨2288528, by rfl⟩ : syracuseStep 3051371 = 4577057) B4577057
theorem B2034247 : Blo 2033435 2034247 := bstep (se 1 (by rfl) ⟨1525685, by rfl⟩ : syracuseStep 2034247 = 3051371) B3051371
theorem B2288533 : Blo 2033435 2288533 := bbase (se 6 (by rfl) ⟨53637, by rfl⟩ : syracuseStep 2288533 = 107275) (by norm_num)
theorem B3051377 : Blo 2033435 3051377 := bstep (se 2 (by rfl) ⟨1144266, by rfl⟩ : syracuseStep 3051377 = 2288533) B2288533
theorem B2034251 : Blo 2033435 2034251 := bstep (se 1 (by rfl) ⟨1525688, by rfl⟩ : syracuseStep 2034251 = 3051377) B3051377
theorem B2574605 : Blo 2033435 2574605 := bbase (se 3 (by rfl) ⟨482738, by rfl⟩ : syracuseStep 2574605 = 965477) (by norm_num)
theorem B6865613 : Blo 2033435 6865613 := bstep (se 3 (by rfl) ⟨1287302, by rfl⟩ : syracuseStep 6865613 = 2574605) B2574605
theorem B4577075 : Blo 2033435 4577075 := bstep (se 1 (by rfl) ⟨3432806, by rfl⟩ : syracuseStep 4577075 = 6865613) B6865613
theorem B3051383 : Blo 2033435 3051383 := bstep (se 1 (by rfl) ⟨2288537, by rfl⟩ : syracuseStep 3051383 = 4577075) B4577075
theorem B2034255 : Blo 2033435 2034255 := bstep (se 1 (by rfl) ⟨1525691, by rfl⟩ : syracuseStep 2034255 = 3051383) B3051383
theorem B3051389 : Blo 2033435 3051389 := bbase (se 3 (by rfl) ⟨572135, by rfl⟩ : syracuseStep 3051389 = 1144271) (by norm_num)
theorem B2034259 : Blo 2033435 2034259 := bstep (se 1 (by rfl) ⟨1525694, by rfl⟩ : syracuseStep 2034259 = 3051389) B3051389
theorem B4577093 : Blo 2033435 4577093 := bbase (se 4 (by rfl) ⟨429102, by rfl⟩ : syracuseStep 4577093 = 858205) (by norm_num)
theorem B3051395 : Blo 2033435 3051395 := bstep (se 1 (by rfl) ⟨2288546, by rfl⟩ : syracuseStep 3051395 = 4577093) B4577093
theorem B2034263 : Blo 2033435 2034263 := bstep (se 1 (by rfl) ⟨1525697, by rfl⟩ : syracuseStep 2034263 = 3051395) B3051395
theorem B2609749 : Blo 2033435 2609749 := bbase (se 8 (by rfl) ⟨15291, by rfl⟩ : syracuseStep 2609749 = 30583) (by norm_num)
theorem B13918661 : Blo 2033435 13918661 := bstep (se 4 (by rfl) ⟨1304874, by rfl⟩ : syracuseStep 13918661 = 2609749) B2609749
theorem B9279107 : Blo 2033435 9279107 := bstep (se 1 (by rfl) ⟨6959330, by rfl⟩ : syracuseStep 9279107 = 13918661) B13918661
theorem B6186071 : Blo 2033435 6186071 := bstep (se 1 (by rfl) ⟨4639553, by rfl⟩ : syracuseStep 6186071 = 9279107) B9279107
theorem B4124047 : Blo 2033435 4124047 := bstep (se 1 (by rfl) ⟨3093035, by rfl⟩ : syracuseStep 4124047 = 6186071) B6186071
theorem B5498729 : Blo 2033435 5498729 := bstep (se 2 (by rfl) ⟨2062023, by rfl⟩ : syracuseStep 5498729 = 4124047) B4124047
theorem B3665819 : Blo 2033435 3665819 := bstep (se 1 (by rfl) ⟨2749364, by rfl⟩ : syracuseStep 3665819 = 5498729) B5498729
theorem B2443879 : Blo 2033435 2443879 := bstep (se 1 (by rfl) ⟨1832909, by rfl⟩ : syracuseStep 2443879 = 3665819) B3665819
theorem B3258505 : Blo 2033435 3258505 := bstep (se 2 (by rfl) ⟨1221939, by rfl⟩ : syracuseStep 3258505 = 2443879) B2443879
theorem B4344673 : Blo 2033435 4344673 := bstep (se 2 (by rfl) ⟨1629252, by rfl⟩ : syracuseStep 4344673 = 3258505) B3258505
theorem B5792897 : Blo 2033435 5792897 := bstep (se 2 (by rfl) ⟨2172336, by rfl⟩ : syracuseStep 5792897 = 4344673) B4344673
theorem B3861931 : Blo 2033435 3861931 := bstep (se 1 (by rfl) ⟨2896448, by rfl⟩ : syracuseStep 3861931 = 5792897) B5792897
theorem B5149241 : Blo 2033435 5149241 := bstep (se 2 (by rfl) ⟨1930965, by rfl⟩ : syracuseStep 5149241 = 3861931) B3861931
theorem B3432827 : Blo 2033435 3432827 := bstep (se 1 (by rfl) ⟨2574620, by rfl⟩ : syracuseStep 3432827 = 5149241) B5149241
theorem B2288551 : Blo 2033435 2288551 := bstep (se 1 (by rfl) ⟨1716413, by rfl⟩ : syracuseStep 2288551 = 3432827) B3432827
theorem B3051401 : Blo 2033435 3051401 := bstep (se 2 (by rfl) ⟨1144275, by rfl⟩ : syracuseStep 3051401 = 2288551) B2288551
theorem B2034267 : Blo 2033435 2034267 := bstep (se 1 (by rfl) ⟨1525700, by rfl⟩ : syracuseStep 2034267 = 3051401) B3051401
theorem B10298501 : Blo 2033435 10298501 := bbase (se 4 (by rfl) ⟨965484, by rfl⟩ : syracuseStep 10298501 = 1930969) (by norm_num)
theorem B6865667 : Blo 2033435 6865667 := bstep (se 1 (by rfl) ⟨5149250, by rfl⟩ : syracuseStep 6865667 = 10298501) B10298501
theorem B4577111 : Blo 2033435 4577111 := bstep (se 1 (by rfl) ⟨3432833, by rfl⟩ : syracuseStep 4577111 = 6865667) B6865667
theorem B3051407 : Blo 2033435 3051407 := bstep (se 1 (by rfl) ⟨2288555, by rfl⟩ : syracuseStep 3051407 = 4577111) B4577111
theorem B2034271 : Blo 2033435 2034271 := bstep (se 1 (by rfl) ⟨1525703, by rfl⟩ : syracuseStep 2034271 = 3051407) B3051407
theorem B3051413 : Blo 2033435 3051413 := bbase (se 6 (by rfl) ⟨71517, by rfl⟩ : syracuseStep 3051413 = 143035) (by norm_num)
theorem B2034275 : Blo 2033435 2034275 := bstep (se 1 (by rfl) ⟨1525706, by rfl⟩ : syracuseStep 2034275 = 3051413) B3051413
theorem B2172349 : Blo 2033435 2172349 := bbase (se 3 (by rfl) ⟨407315, by rfl⟩ : syracuseStep 2172349 = 814631) (by norm_num)
theorem B11585861 : Blo 2033435 11585861 := bstep (se 4 (by rfl) ⟨1086174, by rfl⟩ : syracuseStep 11585861 = 2172349) B2172349
theorem B7723907 : Blo 2033435 7723907 := bstep (se 1 (by rfl) ⟨5792930, by rfl⟩ : syracuseStep 7723907 = 11585861) B11585861
theorem B5149271 : Blo 2033435 5149271 := bstep (se 1 (by rfl) ⟨3861953, by rfl⟩ : syracuseStep 5149271 = 7723907) B7723907
theorem B3432847 : Blo 2033435 3432847 := bstep (se 1 (by rfl) ⟨2574635, by rfl⟩ : syracuseStep 3432847 = 5149271) B5149271
theorem B4577129 : Blo 2033435 4577129 := bstep (se 2 (by rfl) ⟨1716423, by rfl⟩ : syracuseStep 4577129 = 3432847) B3432847
theorem B3051419 : Blo 2033435 3051419 := bstep (se 1 (by rfl) ⟨2288564, by rfl⟩ : syracuseStep 3051419 = 4577129) B4577129
theorem B2034279 : Blo 2033435 2034279 := bstep (se 1 (by rfl) ⟨1525709, by rfl⟩ : syracuseStep 2034279 = 3051419) B3051419
theorem B2288569 : Blo 2033435 2288569 := bbase (se 2 (by rfl) ⟨858213, by rfl⟩ : syracuseStep 2288569 = 1716427) (by norm_num)
theorem B3051425 : Blo 2033435 3051425 := bstep (se 2 (by rfl) ⟨1144284, by rfl⟩ : syracuseStep 3051425 = 2288569) B2288569
theorem B2034283 : Blo 2033435 2034283 := bstep (se 1 (by rfl) ⟨1525712, by rfl⟩ : syracuseStep 2034283 = 3051425) B3051425
theorem B4887805 : Blo 2033435 4887805 := bbase (se 3 (by rfl) ⟨916463, by rfl⟩ : syracuseStep 4887805 = 1832927) (by norm_num)
theorem B6517073 : Blo 2033435 6517073 := bstep (se 2 (by rfl) ⟨2443902, by rfl⟩ : syracuseStep 6517073 = 4887805) B4887805
theorem B4344715 : Blo 2033435 4344715 := bstep (se 1 (by rfl) ⟨3258536, by rfl⟩ : syracuseStep 4344715 = 6517073) B6517073
theorem B5792953 : Blo 2033435 5792953 := bstep (se 2 (by rfl) ⟨2172357, by rfl⟩ : syracuseStep 5792953 = 4344715) B4344715
theorem B7723937 : Blo 2033435 7723937 := bstep (se 2 (by rfl) ⟨2896476, by rfl⟩ : syracuseStep 7723937 = 5792953) B5792953
theorem B5149291 : Blo 2033435 5149291 := bstep (se 1 (by rfl) ⟨3861968, by rfl⟩ : syracuseStep 5149291 = 7723937) B7723937
theorem B6865721 : Blo 2033435 6865721 := bstep (se 2 (by rfl) ⟨2574645, by rfl⟩ : syracuseStep 6865721 = 5149291) B5149291
theorem B4577147 : Blo 2033435 4577147 := bstep (se 1 (by rfl) ⟨3432860, by rfl⟩ : syracuseStep 4577147 = 6865721) B6865721
theorem B3051431 : Blo 2033435 3051431 := bstep (se 1 (by rfl) ⟨2288573, by rfl⟩ : syracuseStep 3051431 = 4577147) B4577147
theorem B2034287 : Blo 2033435 2034287 := bstep (se 1 (by rfl) ⟨1525715, by rfl⟩ : syracuseStep 2034287 = 3051431) B3051431
theorem B3051437 : Blo 2033435 3051437 := bbase (se 3 (by rfl) ⟨572144, by rfl⟩ : syracuseStep 3051437 = 1144289) (by norm_num)
theorem B2034291 : Blo 2033435 2034291 := bstep (se 1 (by rfl) ⟨1525718, by rfl⟩ : syracuseStep 2034291 = 3051437) B3051437
theorem B4577165 : Blo 2033435 4577165 := bbase (se 3 (by rfl) ⟨858218, by rfl⟩ : syracuseStep 4577165 = 1716437) (by norm_num)
theorem B3051443 : Blo 2033435 3051443 := bstep (se 1 (by rfl) ⟨2288582, by rfl⟩ : syracuseStep 3051443 = 4577165) B4577165
theorem B2034295 : Blo 2033435 2034295 := bstep (se 1 (by rfl) ⟨1525721, by rfl⟩ : syracuseStep 2034295 = 3051443) B3051443
theorem B2574661 : Blo 2033435 2574661 := bbase (se 4 (by rfl) ⟨241374, by rfl⟩ : syracuseStep 2574661 = 482749) (by norm_num)
theorem B3432881 : Blo 2033435 3432881 := bstep (se 2 (by rfl) ⟨1287330, by rfl⟩ : syracuseStep 3432881 = 2574661) B2574661
theorem B2288587 : Blo 2033435 2288587 := bstep (se 1 (by rfl) ⟨1716440, by rfl⟩ : syracuseStep 2288587 = 3432881) B3432881
theorem B3051449 : Blo 2033435 3051449 := bstep (se 2 (by rfl) ⟨1144293, by rfl⟩ : syracuseStep 3051449 = 2288587) B2288587
theorem B2034299 : Blo 2033435 2034299 := bstep (se 1 (by rfl) ⟨1525724, by rfl⟩ : syracuseStep 2034299 = 3051449) B3051449
theorem B9775685 : Blo 2033435 9775685 := bbase (se 4 (by rfl) ⟨916470, by rfl⟩ : syracuseStep 9775685 = 1832941) (by norm_num)
theorem B26068493 : Blo 2033435 26068493 := bstep (se 3 (by rfl) ⟨4887842, by rfl⟩ : syracuseStep 26068493 = 9775685) B9775685
theorem B17378995 : Blo 2033435 17378995 := bstep (se 1 (by rfl) ⟨13034246, by rfl⟩ : syracuseStep 17378995 = 26068493) B26068493
theorem B23171993 : Blo 2033435 23171993 := bstep (se 2 (by rfl) ⟨8689497, by rfl⟩ : syracuseStep 23171993 = 17378995) B17378995
theorem B15447995 : Blo 2033435 15447995 := bstep (se 1 (by rfl) ⟨11585996, by rfl⟩ : syracuseStep 15447995 = 23171993) B23171993
theorem B10298663 : Blo 2033435 10298663 := bstep (se 1 (by rfl) ⟨7723997, by rfl⟩ : syracuseStep 10298663 = 15447995) B15447995
theorem B6865775 : Blo 2033435 6865775 := bstep (se 1 (by rfl) ⟨5149331, by rfl⟩ : syracuseStep 6865775 = 10298663) B10298663
theorem B4577183 : Blo 2033435 4577183 := bstep (se 1 (by rfl) ⟨3432887, by rfl⟩ : syracuseStep 4577183 = 6865775) B6865775
theorem B3051455 : Blo 2033435 3051455 := bstep (se 1 (by rfl) ⟨2288591, by rfl⟩ : syracuseStep 3051455 = 4577183) B4577183
theorem B2034303 : Blo 2033435 2034303 := bstep (se 1 (by rfl) ⟨1525727, by rfl⟩ : syracuseStep 2034303 = 3051455) B3051455
theorem B3051461 : Blo 2033435 3051461 := bbase (se 4 (by rfl) ⟨286074, by rfl⟩ : syracuseStep 3051461 = 572149) (by norm_num)
theorem B2034307 : Blo 2033435 2034307 := bstep (se 1 (by rfl) ⟨1525730, by rfl⟩ : syracuseStep 2034307 = 3051461) B3051461
theorem B3432901 : Blo 2033435 3432901 := bbase (se 4 (by rfl) ⟨321834, by rfl⟩ : syracuseStep 3432901 = 643669) (by norm_num)
theorem B4577201 : Blo 2033435 4577201 := bstep (se 2 (by rfl) ⟨1716450, by rfl⟩ : syracuseStep 4577201 = 3432901) B3432901
theorem B3051467 : Blo 2033435 3051467 := bstep (se 1 (by rfl) ⟨2288600, by rfl⟩ : syracuseStep 3051467 = 4577201) B4577201
theorem B2034311 : Blo 2033435 2034311 := bstep (se 1 (by rfl) ⟨1525733, by rfl⟩ : syracuseStep 2034311 = 3051467) B3051467
theorem B2288605 : Blo 2033435 2288605 := bbase (se 3 (by rfl) ⟨429113, by rfl⟩ : syracuseStep 2288605 = 858227) (by norm_num)
theorem B3051473 : Blo 2033435 3051473 := bstep (se 2 (by rfl) ⟨1144302, by rfl⟩ : syracuseStep 3051473 = 2288605) B2288605
theorem B2034315 : Blo 2033435 2034315 := bstep (se 1 (by rfl) ⟨1525736, by rfl⟩ : syracuseStep 2034315 = 3051473) B3051473
theorem B6865829 : Blo 2033435 6865829 := bbase (se 4 (by rfl) ⟨643671, by rfl⟩ : syracuseStep 6865829 = 1287343) (by norm_num)
theorem B4577219 : Blo 2033435 4577219 := bstep (se 1 (by rfl) ⟨3432914, by rfl⟩ : syracuseStep 4577219 = 6865829) B6865829
theorem B3051479 : Blo 2033435 3051479 := bstep (se 1 (by rfl) ⟨2288609, by rfl⟩ : syracuseStep 3051479 = 4577219) B4577219
theorem B2034319 : Blo 2033435 2034319 := bstep (se 1 (by rfl) ⟨1525739, by rfl⟩ : syracuseStep 2034319 = 3051479) B3051479
theorem B3051485 : Blo 2033435 3051485 := bbase (se 3 (by rfl) ⟨572153, by rfl⟩ : syracuseStep 3051485 = 1144307) (by norm_num)
theorem B2034323 : Blo 2033435 2034323 := bstep (se 1 (by rfl) ⟨1525742, by rfl⟩ : syracuseStep 2034323 = 3051485) B3051485
theorem B4577237 : Blo 2033435 4577237 := bbase (se 7 (by rfl) ⟨53639, by rfl⟩ : syracuseStep 4577237 = 107279) (by norm_num)
theorem B3051491 : Blo 2033435 3051491 := bstep (se 1 (by rfl) ⟨2288618, by rfl⟩ : syracuseStep 3051491 = 4577237) B4577237
theorem B2034327 : Blo 2033435 2034327 := bstep (se 1 (by rfl) ⟨1525745, by rfl⟩ : syracuseStep 2034327 = 3051491) B3051491
theorem B10581749 : Blo 2033435 10581749 := bbase (se 5 (by rfl) ⟨496019, by rfl⟩ : syracuseStep 10581749 = 992039) (by norm_num)
theorem B7054499 : Blo 2033435 7054499 := bstep (se 1 (by rfl) ⟨5290874, by rfl⟩ : syracuseStep 7054499 = 10581749) B10581749
theorem B18811997 : Blo 2033435 18811997 := bstep (se 3 (by rfl) ⟨3527249, by rfl⟩ : syracuseStep 18811997 = 7054499) B7054499
theorem B12541331 : Blo 2033435 12541331 := bstep (se 1 (by rfl) ⟨9405998, by rfl⟩ : syracuseStep 12541331 = 18811997) B18811997
theorem B33443549 : Blo 2033435 33443549 := bstep (se 3 (by rfl) ⟨6270665, by rfl⟩ : syracuseStep 33443549 = 12541331) B12541331
theorem B22295699 : Blo 2033435 22295699 := bstep (se 1 (by rfl) ⟨16721774, by rfl⟩ : syracuseStep 22295699 = 33443549) B33443549
theorem B14863799 : Blo 2033435 14863799 := bstep (se 1 (by rfl) ⟨11147849, by rfl⟩ : syracuseStep 14863799 = 22295699) B22295699
theorem B9909199 : Blo 2033435 9909199 := bstep (se 1 (by rfl) ⟨7431899, by rfl⟩ : syracuseStep 9909199 = 14863799) B14863799
theorem B52849061 : Blo 2033435 52849061 := bstep (se 4 (by rfl) ⟨4954599, by rfl⟩ : syracuseStep 52849061 = 9909199) B9909199
theorem B35232707 : Blo 2033435 35232707 := bstep (se 1 (by rfl) ⟨26424530, by rfl⟩ : syracuseStep 35232707 = 52849061) B52849061
theorem B23488471 : Blo 2033435 23488471 := bstep (se 1 (by rfl) ⟨17616353, by rfl⟩ : syracuseStep 23488471 = 35232707) B35232707
theorem B31317961 : Blo 2033435 31317961 := bstep (se 2 (by rfl) ⟨11744235, by rfl⟩ : syracuseStep 31317961 = 23488471) B23488471
theorem B41757281 : Blo 2033435 41757281 := bstep (se 2 (by rfl) ⟨15658980, by rfl⟩ : syracuseStep 41757281 = 31317961) B31317961
theorem B27838187 : Blo 2033435 27838187 := bstep (se 1 (by rfl) ⟨20878640, by rfl⟩ : syracuseStep 27838187 = 41757281) B41757281
theorem B18558791 : Blo 2033435 18558791 := bstep (se 1 (by rfl) ⟨13919093, by rfl⟩ : syracuseStep 18558791 = 27838187) B27838187
theorem B12372527 : Blo 2033435 12372527 := bstep (se 1 (by rfl) ⟨9279395, by rfl⟩ : syracuseStep 12372527 = 18558791) B18558791
theorem B8248351 : Blo 2033435 8248351 := bstep (se 1 (by rfl) ⟨6186263, by rfl⟩ : syracuseStep 8248351 = 12372527) B12372527
theorem B10997801 : Blo 2033435 10997801 := bstep (se 2 (by rfl) ⟨4124175, by rfl⟩ : syracuseStep 10997801 = 8248351) B8248351
theorem B7331867 : Blo 2033435 7331867 := bstep (se 1 (by rfl) ⟨5498900, by rfl⟩ : syracuseStep 7331867 = 10997801) B10997801
theorem B4887911 : Blo 2033435 4887911 := bstep (se 1 (by rfl) ⟨3665933, by rfl⟩ : syracuseStep 4887911 = 7331867) B7331867
theorem B13034429 : Blo 2033435 13034429 := bstep (se 3 (by rfl) ⟨2443955, by rfl⟩ : syracuseStep 13034429 = 4887911) B4887911
theorem B8689619 : Blo 2033435 8689619 := bstep (se 1 (by rfl) ⟨6517214, by rfl⟩ : syracuseStep 8689619 = 13034429) B13034429
theorem B5793079 : Blo 2033435 5793079 := bstep (se 1 (by rfl) ⟨4344809, by rfl⟩ : syracuseStep 5793079 = 8689619) B8689619
theorem B7724105 : Blo 2033435 7724105 := bstep (se 2 (by rfl) ⟨2896539, by rfl⟩ : syracuseStep 7724105 = 5793079) B5793079
theorem B5149403 : Blo 2033435 5149403 := bstep (se 1 (by rfl) ⟨3862052, by rfl⟩ : syracuseStep 5149403 = 7724105) B7724105
theorem B3432935 : Blo 2033435 3432935 := bstep (se 1 (by rfl) ⟨2574701, by rfl⟩ : syracuseStep 3432935 = 5149403) B5149403
theorem B2288623 : Blo 2033435 2288623 := bstep (se 1 (by rfl) ⟨1716467, by rfl⟩ : syracuseStep 2288623 = 3432935) B3432935
theorem B3051497 : Blo 2033435 3051497 := bstep (se 2 (by rfl) ⟨1144311, by rfl⟩ : syracuseStep 3051497 = 2288623) B2288623
theorem B2034331 : Blo 2033435 2034331 := bstep (se 1 (by rfl) ⟨1525748, by rfl⟩ : syracuseStep 2034331 = 3051497) B3051497
theorem B3258613 : Blo 2033435 3258613 := bbase (se 5 (by rfl) ⟨152747, by rfl⟩ : syracuseStep 3258613 = 305495) (by norm_num)
theorem B17379269 : Blo 2033435 17379269 := bstep (se 4 (by rfl) ⟨1629306, by rfl⟩ : syracuseStep 17379269 = 3258613) B3258613
theorem B11586179 : Blo 2033435 11586179 := bstep (se 1 (by rfl) ⟨8689634, by rfl⟩ : syracuseStep 11586179 = 17379269) B17379269
theorem B7724119 : Blo 2033435 7724119 := bstep (se 1 (by rfl) ⟨5793089, by rfl⟩ : syracuseStep 7724119 = 11586179) B11586179
theorem B10298825 : Blo 2033435 10298825 := bstep (se 2 (by rfl) ⟨3862059, by rfl⟩ : syracuseStep 10298825 = 7724119) B7724119
theorem B6865883 : Blo 2033435 6865883 := bstep (se 1 (by rfl) ⟨5149412, by rfl⟩ : syracuseStep 6865883 = 10298825) B10298825
theorem B4577255 : Blo 2033435 4577255 := bstep (se 1 (by rfl) ⟨3432941, by rfl⟩ : syracuseStep 4577255 = 6865883) B6865883
theorem B3051503 : Blo 2033435 3051503 := bstep (se 1 (by rfl) ⟨2288627, by rfl⟩ : syracuseStep 3051503 = 4577255) B4577255
theorem B2034335 : Blo 2033435 2034335 := bstep (se 1 (by rfl) ⟨1525751, by rfl⟩ : syracuseStep 2034335 = 3051503) B3051503
theorem B3051509 : Blo 2033435 3051509 := bbase (se 5 (by rfl) ⟨143039, by rfl⟩ : syracuseStep 3051509 = 286079) (by norm_num)
theorem B2034339 : Blo 2033435 2034339 := bstep (se 1 (by rfl) ⟨1525754, by rfl⟩ : syracuseStep 2034339 = 3051509) B3051509
theorem B6517253 : Blo 2033435 6517253 := bbase (se 4 (by rfl) ⟨610992, by rfl⟩ : syracuseStep 6517253 = 1221985) (by norm_num)
theorem B4344835 : Blo 2033435 4344835 := bstep (se 1 (by rfl) ⟨3258626, by rfl⟩ : syracuseStep 4344835 = 6517253) B6517253
theorem B5793113 : Blo 2033435 5793113 := bstep (se 2 (by rfl) ⟨2172417, by rfl⟩ : syracuseStep 5793113 = 4344835) B4344835
theorem B3862075 : Blo 2033435 3862075 := bstep (se 1 (by rfl) ⟨2896556, by rfl⟩ : syracuseStep 3862075 = 5793113) B5793113
theorem B5149433 : Blo 2033435 5149433 := bstep (se 2 (by rfl) ⟨1931037, by rfl⟩ : syracuseStep 5149433 = 3862075) B3862075
theorem B3432955 : Blo 2033435 3432955 := bstep (se 1 (by rfl) ⟨2574716, by rfl⟩ : syracuseStep 3432955 = 5149433) B5149433
theorem B4577273 : Blo 2033435 4577273 := bstep (se 2 (by rfl) ⟨1716477, by rfl⟩ : syracuseStep 4577273 = 3432955) B3432955
theorem B3051515 : Blo 2033435 3051515 := bstep (se 1 (by rfl) ⟨2288636, by rfl⟩ : syracuseStep 3051515 = 4577273) B4577273
theorem B2034343 : Blo 2033435 2034343 := bstep (se 1 (by rfl) ⟨1525757, by rfl⟩ : syracuseStep 2034343 = 3051515) B3051515
theorem B2288641 : Blo 2033435 2288641 := bbase (se 2 (by rfl) ⟨858240, by rfl⟩ : syracuseStep 2288641 = 1716481) (by norm_num)
theorem B3051521 : Blo 2033435 3051521 := bstep (se 2 (by rfl) ⟨1144320, by rfl⟩ : syracuseStep 3051521 = 2288641) B2288641
theorem B2034347 : Blo 2033435 2034347 := bstep (se 1 (by rfl) ⟨1525760, by rfl⟩ : syracuseStep 2034347 = 3051521) B3051521
theorem B5149453 : Blo 2033435 5149453 := bbase (se 3 (by rfl) ⟨965522, by rfl⟩ : syracuseStep 5149453 = 1931045) (by norm_num)
theorem B6865937 : Blo 2033435 6865937 := bstep (se 2 (by rfl) ⟨2574726, by rfl⟩ : syracuseStep 6865937 = 5149453) B5149453
theorem B4577291 : Blo 2033435 4577291 := bstep (se 1 (by rfl) ⟨3432968, by rfl⟩ : syracuseStep 4577291 = 6865937) B6865937
theorem B3051527 : Blo 2033435 3051527 := bstep (se 1 (by rfl) ⟨2288645, by rfl⟩ : syracuseStep 3051527 = 4577291) B4577291
theorem B2034351 : Blo 2033435 2034351 := bstep (se 1 (by rfl) ⟨1525763, by rfl⟩ : syracuseStep 2034351 = 3051527) B3051527
theorem B3051533 : Blo 2033435 3051533 := bbase (se 3 (by rfl) ⟨572162, by rfl⟩ : syracuseStep 3051533 = 1144325) (by norm_num)
theorem B2034355 : Blo 2033435 2034355 := bstep (se 1 (by rfl) ⟨1525766, by rfl⟩ : syracuseStep 2034355 = 3051533) B3051533
theorem B4577309 : Blo 2033435 4577309 := bbase (se 3 (by rfl) ⟨858245, by rfl⟩ : syracuseStep 4577309 = 1716491) (by norm_num)
theorem B3051539 : Blo 2033435 3051539 := bstep (se 1 (by rfl) ⟨2288654, by rfl⟩ : syracuseStep 3051539 = 4577309) B4577309
theorem B2034359 : Blo 2033435 2034359 := bstep (se 1 (by rfl) ⟨1525769, by rfl⟩ : syracuseStep 2034359 = 3051539) B3051539
theorem B3432989 : Blo 2033435 3432989 := bbase (se 3 (by rfl) ⟨643685, by rfl⟩ : syracuseStep 3432989 = 1287371) (by norm_num)
theorem B2288659 : Blo 2033435 2288659 := bstep (se 1 (by rfl) ⟨1716494, by rfl⟩ : syracuseStep 2288659 = 3432989) B3432989
theorem B3051545 : Blo 2033435 3051545 := bstep (se 2 (by rfl) ⟨1144329, by rfl⟩ : syracuseStep 3051545 = 2288659) B2288659
theorem B2034363 : Blo 2033435 2034363 := bstep (se 1 (by rfl) ⟨1525772, by rfl⟩ : syracuseStep 2034363 = 3051545) B3051545
theorem B9406165 : Blo 2033435 9406165 := bbase (se 7 (by rfl) ⟨110228, by rfl⟩ : syracuseStep 9406165 = 220457) (by norm_num)
theorem B12541553 : Blo 2033435 12541553 := bstep (se 2 (by rfl) ⟨4703082, by rfl⟩ : syracuseStep 12541553 = 9406165) B9406165
theorem B8361035 : Blo 2033435 8361035 := bstep (se 1 (by rfl) ⟨6270776, by rfl⟩ : syracuseStep 8361035 = 12541553) B12541553
theorem B5574023 : Blo 2033435 5574023 := bstep (se 1 (by rfl) ⟨4180517, by rfl⟩ : syracuseStep 5574023 = 8361035) B8361035
theorem B3716015 : Blo 2033435 3716015 := bstep (se 1 (by rfl) ⟨2787011, by rfl⟩ : syracuseStep 3716015 = 5574023) B5574023
theorem B9909373 : Blo 2033435 9909373 := bstep (se 3 (by rfl) ⟨1858007, by rfl⟩ : syracuseStep 9909373 = 3716015) B3716015
theorem B13212497 : Blo 2033435 13212497 := bstep (se 2 (by rfl) ⟨4954686, by rfl⟩ : syracuseStep 13212497 = 9909373) B9909373
theorem B8808331 : Blo 2033435 8808331 := bstep (se 1 (by rfl) ⟨6606248, by rfl⟩ : syracuseStep 8808331 = 13212497) B13212497
theorem B11744441 : Blo 2033435 11744441 := bstep (se 2 (by rfl) ⟨4404165, by rfl⟩ : syracuseStep 11744441 = 8808331) B8808331
theorem B7829627 : Blo 2033435 7829627 := bstep (se 1 (by rfl) ⟨5872220, by rfl⟩ : syracuseStep 7829627 = 11744441) B11744441
theorem B20879005 : Blo 2033435 20879005 := bstep (se 3 (by rfl) ⟨3914813, by rfl⟩ : syracuseStep 20879005 = 7829627) B7829627
theorem B27838673 : Blo 2033435 27838673 := bstep (se 2 (by rfl) ⟨10439502, by rfl⟩ : syracuseStep 27838673 = 20879005) B20879005
theorem B18559115 : Blo 2033435 18559115 := bstep (se 1 (by rfl) ⟨13919336, by rfl⟩ : syracuseStep 18559115 = 27838673) B27838673
theorem B12372743 : Blo 2033435 12372743 := bstep (se 1 (by rfl) ⟨9279557, by rfl⟩ : syracuseStep 12372743 = 18559115) B18559115
theorem B8248495 : Blo 2033435 8248495 := bstep (se 1 (by rfl) ⟨6186371, by rfl⟩ : syracuseStep 8248495 = 12372743) B12372743
theorem B10997993 : Blo 2033435 10997993 := bstep (se 2 (by rfl) ⟨4124247, by rfl⟩ : syracuseStep 10997993 = 8248495) B8248495
theorem B7331995 : Blo 2033435 7331995 := bstep (se 1 (by rfl) ⟨5498996, by rfl⟩ : syracuseStep 7331995 = 10997993) B10997993
theorem B9775993 : Blo 2033435 9775993 := bstep (se 2 (by rfl) ⟨3665997, by rfl⟩ : syracuseStep 9775993 = 7331995) B7331995
theorem B13034657 : Blo 2033435 13034657 := bstep (se 2 (by rfl) ⟨4887996, by rfl⟩ : syracuseStep 13034657 = 9775993) B9775993
theorem B8689771 : Blo 2033435 8689771 := bstep (se 1 (by rfl) ⟨6517328, by rfl⟩ : syracuseStep 8689771 = 13034657) B13034657
theorem B11586361 : Blo 2033435 11586361 := bstep (se 2 (by rfl) ⟨4344885, by rfl⟩ : syracuseStep 11586361 = 8689771) B8689771
theorem B15448481 : Blo 2033435 15448481 := bstep (se 2 (by rfl) ⟨5793180, by rfl⟩ : syracuseStep 15448481 = 11586361) B11586361
theorem B10298987 : Blo 2033435 10298987 := bstep (se 1 (by rfl) ⟨7724240, by rfl⟩ : syracuseStep 10298987 = 15448481) B15448481
theorem B6865991 : Blo 2033435 6865991 := bstep (se 1 (by rfl) ⟨5149493, by rfl⟩ : syracuseStep 6865991 = 10298987) B10298987
theorem B4577327 : Blo 2033435 4577327 := bstep (se 1 (by rfl) ⟨3432995, by rfl⟩ : syracuseStep 4577327 = 6865991) B6865991
theorem B3051551 : Blo 2033435 3051551 := bstep (se 1 (by rfl) ⟨2288663, by rfl⟩ : syracuseStep 3051551 = 4577327) B4577327
theorem B2034367 : Blo 2033435 2034367 := bstep (se 1 (by rfl) ⟨1525775, by rfl⟩ : syracuseStep 2034367 = 3051551) B3051551
theorem B3051557 : Blo 2033435 3051557 := bbase (se 4 (by rfl) ⟨286083, by rfl⟩ : syracuseStep 3051557 = 572167) (by norm_num)
theorem B2034371 : Blo 2033435 2034371 := bstep (se 1 (by rfl) ⟨1525778, by rfl⟩ : syracuseStep 2034371 = 3051557) B3051557
theorem B2574757 : Blo 2033435 2574757 := bbase (se 4 (by rfl) ⟨241383, by rfl⟩ : syracuseStep 2574757 = 482767) (by norm_num)
theorem B3433009 : Blo 2033435 3433009 := bstep (se 2 (by rfl) ⟨1287378, by rfl⟩ : syracuseStep 3433009 = 2574757) B2574757
theorem B4577345 : Blo 2033435 4577345 := bstep (se 2 (by rfl) ⟨1716504, by rfl⟩ : syracuseStep 4577345 = 3433009) B3433009
theorem B3051563 : Blo 2033435 3051563 := bstep (se 1 (by rfl) ⟨2288672, by rfl⟩ : syracuseStep 3051563 = 4577345) B4577345
theorem B2034375 : Blo 2033435 2034375 := bstep (se 1 (by rfl) ⟨1525781, by rfl⟩ : syracuseStep 2034375 = 3051563) B3051563
theorem B2288677 : Blo 2033435 2288677 := bbase (se 4 (by rfl) ⟨214563, by rfl⟩ : syracuseStep 2288677 = 429127) (by norm_num)
theorem B3051569 : Blo 2033435 3051569 := bstep (se 2 (by rfl) ⟨1144338, by rfl⟩ : syracuseStep 3051569 = 2288677) B2288677
theorem B2034379 : Blo 2033435 2034379 := bstep (se 1 (by rfl) ⟨1525784, by rfl⟩ : syracuseStep 2034379 = 3051569) B3051569
theorem B6517381 : Blo 2033435 6517381 := bbase (se 4 (by rfl) ⟨611004, by rfl⟩ : syracuseStep 6517381 = 1222009) (by norm_num)
theorem B8689841 : Blo 2033435 8689841 := bstep (se 2 (by rfl) ⟨3258690, by rfl⟩ : syracuseStep 8689841 = 6517381) B6517381
theorem B5793227 : Blo 2033435 5793227 := bstep (se 1 (by rfl) ⟨4344920, by rfl⟩ : syracuseStep 5793227 = 8689841) B8689841
theorem B3862151 : Blo 2033435 3862151 := bstep (se 1 (by rfl) ⟨2896613, by rfl⟩ : syracuseStep 3862151 = 5793227) B5793227
theorem B2574767 : Blo 2033435 2574767 := bstep (se 1 (by rfl) ⟨1931075, by rfl⟩ : syracuseStep 2574767 = 3862151) B3862151
theorem B6866045 : Blo 2033435 6866045 := bstep (se 3 (by rfl) ⟨1287383, by rfl⟩ : syracuseStep 6866045 = 2574767) B2574767
theorem B4577363 : Blo 2033435 4577363 := bstep (se 1 (by rfl) ⟨3433022, by rfl⟩ : syracuseStep 4577363 = 6866045) B6866045
theorem B3051575 : Blo 2033435 3051575 := bstep (se 1 (by rfl) ⟨2288681, by rfl⟩ : syracuseStep 3051575 = 4577363) B4577363
theorem B2034383 : Blo 2033435 2034383 := bstep (se 1 (by rfl) ⟨1525787, by rfl⟩ : syracuseStep 2034383 = 3051575) B3051575
theorem B3051581 : Blo 2033435 3051581 := bbase (se 3 (by rfl) ⟨572171, by rfl⟩ : syracuseStep 3051581 = 1144343) (by norm_num)
theorem B2034387 : Blo 2033435 2034387 := bstep (se 1 (by rfl) ⟨1525790, by rfl⟩ : syracuseStep 2034387 = 3051581) B3051581
theorem B4577381 : Blo 2033435 4577381 := bbase (se 4 (by rfl) ⟨429129, by rfl⟩ : syracuseStep 4577381 = 858259) (by norm_num)
theorem B3051587 : Blo 2033435 3051587 := bstep (se 1 (by rfl) ⟨2288690, by rfl⟩ : syracuseStep 3051587 = 4577381) B4577381
theorem B2034391 : Blo 2033435 2034391 := bstep (se 1 (by rfl) ⟨1525793, by rfl⟩ : syracuseStep 2034391 = 3051587) B3051587
theorem B5149565 : Blo 2033435 5149565 := bbase (se 3 (by rfl) ⟨965543, by rfl⟩ : syracuseStep 5149565 = 1931087) (by norm_num)
theorem B3433043 : Blo 2033435 3433043 := bstep (se 1 (by rfl) ⟨2574782, by rfl⟩ : syracuseStep 3433043 = 5149565) B5149565
theorem B2288695 : Blo 2033435 2288695 := bstep (se 1 (by rfl) ⟨1716521, by rfl⟩ : syracuseStep 2288695 = 3433043) B3433043
theorem B3051593 : Blo 2033435 3051593 := bstep (se 2 (by rfl) ⟨1144347, by rfl⟩ : syracuseStep 3051593 = 2288695) B2288695
theorem B2034395 : Blo 2033435 2034395 := bstep (se 1 (by rfl) ⟨1525796, by rfl⟩ : syracuseStep 2034395 = 3051593) B3051593
theorem B3862181 : Blo 2033435 3862181 := bbase (se 4 (by rfl) ⟨362079, by rfl⟩ : syracuseStep 3862181 = 724159) (by norm_num)
theorem B10299149 : Blo 2033435 10299149 := bstep (se 3 (by rfl) ⟨1931090, by rfl⟩ : syracuseStep 10299149 = 3862181) B3862181
theorem B6866099 : Blo 2033435 6866099 := bstep (se 1 (by rfl) ⟨5149574, by rfl⟩ : syracuseStep 6866099 = 10299149) B10299149
theorem B4577399 : Blo 2033435 4577399 := bstep (se 1 (by rfl) ⟨3433049, by rfl⟩ : syracuseStep 4577399 = 6866099) B6866099
theorem B3051599 : Blo 2033435 3051599 := bstep (se 1 (by rfl) ⟨2288699, by rfl⟩ : syracuseStep 3051599 = 4577399) B4577399
theorem B2034399 : Blo 2033435 2034399 := bstep (se 1 (by rfl) ⟨1525799, by rfl⟩ : syracuseStep 2034399 = 3051599) B3051599
theorem B3051605 : Blo 2033435 3051605 := bbase (se 8 (by rfl) ⟨17880, by rfl⟩ : syracuseStep 3051605 = 35761) (by norm_num)
theorem B2034403 : Blo 2033435 2034403 := bstep (se 1 (by rfl) ⟨1525802, by rfl⟩ : syracuseStep 2034403 = 3051605) B3051605
theorem B19552373 : Blo 2033435 19552373 := bbase (se 5 (by rfl) ⟨916517, by rfl⟩ : syracuseStep 19552373 = 1833035) (by norm_num)
theorem B13034915 : Blo 2033435 13034915 := bstep (se 1 (by rfl) ⟨9776186, by rfl⟩ : syracuseStep 13034915 = 19552373) B19552373
theorem B8689943 : Blo 2033435 8689943 := bstep (se 1 (by rfl) ⟨6517457, by rfl⟩ : syracuseStep 8689943 = 13034915) B13034915
theorem B5793295 : Blo 2033435 5793295 := bstep (se 1 (by rfl) ⟨4344971, by rfl⟩ : syracuseStep 5793295 = 8689943) B8689943
theorem B7724393 : Blo 2033435 7724393 := bstep (se 2 (by rfl) ⟨2896647, by rfl⟩ : syracuseStep 7724393 = 5793295) B5793295
theorem B5149595 : Blo 2033435 5149595 := bstep (se 1 (by rfl) ⟨3862196, by rfl⟩ : syracuseStep 5149595 = 7724393) B7724393
theorem B3433063 : Blo 2033435 3433063 := bstep (se 1 (by rfl) ⟨2574797, by rfl⟩ : syracuseStep 3433063 = 5149595) B5149595
theorem B4577417 : Blo 2033435 4577417 := bstep (se 2 (by rfl) ⟨1716531, by rfl⟩ : syracuseStep 4577417 = 3433063) B3433063
theorem B3051611 : Blo 2033435 3051611 := bstep (se 1 (by rfl) ⟨2288708, by rfl⟩ : syracuseStep 3051611 = 4577417) B4577417
theorem B2034407 : Blo 2033435 2034407 := bstep (se 1 (by rfl) ⟨1525805, by rfl⟩ : syracuseStep 2034407 = 3051611) B3051611
theorem B2288713 : Blo 2033435 2288713 := bbase (se 2 (by rfl) ⟨858267, by rfl⟩ : syracuseStep 2288713 = 1716535) (by norm_num)
theorem B3051617 : Blo 2033435 3051617 := bstep (se 2 (by rfl) ⟨1144356, by rfl⟩ : syracuseStep 3051617 = 2288713) B2288713
theorem B2034411 : Blo 2033435 2034411 := bstep (se 1 (by rfl) ⟨1525808, by rfl⟩ : syracuseStep 2034411 = 3051617) B3051617
theorem B13034965 : Blo 2033435 13034965 := bbase (se 7 (by rfl) ⟨152753, by rfl⟩ : syracuseStep 13034965 = 305507) (by norm_num)
theorem B17379953 : Blo 2033435 17379953 := bstep (se 2 (by rfl) ⟨6517482, by rfl⟩ : syracuseStep 17379953 = 13034965) B13034965
theorem B11586635 : Blo 2033435 11586635 := bstep (se 1 (by rfl) ⟨8689976, by rfl⟩ : syracuseStep 11586635 = 17379953) B17379953
theorem B7724423 : Blo 2033435 7724423 := bstep (se 1 (by rfl) ⟨5793317, by rfl⟩ : syracuseStep 7724423 = 11586635) B11586635
theorem B5149615 : Blo 2033435 5149615 := bstep (se 1 (by rfl) ⟨3862211, by rfl⟩ : syracuseStep 5149615 = 7724423) B7724423
theorem B6866153 : Blo 2033435 6866153 := bstep (se 2 (by rfl) ⟨2574807, by rfl⟩ : syracuseStep 6866153 = 5149615) B5149615
theorem B4577435 : Blo 2033435 4577435 := bstep (se 1 (by rfl) ⟨3433076, by rfl⟩ : syracuseStep 4577435 = 6866153) B6866153
theorem B3051623 : Blo 2033435 3051623 := bstep (se 1 (by rfl) ⟨2288717, by rfl⟩ : syracuseStep 3051623 = 4577435) B4577435
theorem B2034415 : Blo 2033435 2034415 := bstep (se 1 (by rfl) ⟨1525811, by rfl⟩ : syracuseStep 2034415 = 3051623) B3051623
theorem B3051629 : Blo 2033435 3051629 := bbase (se 3 (by rfl) ⟨572180, by rfl⟩ : syracuseStep 3051629 = 1144361) (by norm_num)
theorem B2034419 : Blo 2033435 2034419 := bstep (se 1 (by rfl) ⟨1525814, by rfl⟩ : syracuseStep 2034419 = 3051629) B3051629
theorem B4577453 : Blo 2033435 4577453 := bbase (se 3 (by rfl) ⟨858272, by rfl⟩ : syracuseStep 4577453 = 1716545) (by norm_num)
theorem B3051635 : Blo 2033435 3051635 := bstep (se 1 (by rfl) ⟨2288726, by rfl⟩ : syracuseStep 3051635 = 4577453) B4577453
theorem B2034423 : Blo 2033435 2034423 := bstep (se 1 (by rfl) ⟨1525817, by rfl⟩ : syracuseStep 2034423 = 3051635) B3051635
theorem B5219909 : Blo 2033435 5219909 := bbase (se 4 (by rfl) ⟨489366, by rfl⟩ : syracuseStep 5219909 = 978733) (by norm_num)
theorem B3479939 : Blo 2033435 3479939 := bstep (se 1 (by rfl) ⟨2609954, by rfl⟩ : syracuseStep 3479939 = 5219909) B5219909
theorem B2319959 : Blo 2033435 2319959 := bstep (se 1 (by rfl) ⟨1739969, by rfl⟩ : syracuseStep 2319959 = 3479939) B3479939
theorem B6186557 : Blo 2033435 6186557 := bstep (se 3 (by rfl) ⟨1159979, by rfl⟩ : syracuseStep 6186557 = 2319959) B2319959
theorem B4124371 : Blo 2033435 4124371 := bstep (se 1 (by rfl) ⟨3093278, by rfl⟩ : syracuseStep 4124371 = 6186557) B6186557
theorem B5499161 : Blo 2033435 5499161 := bstep (se 2 (by rfl) ⟨2062185, by rfl⟩ : syracuseStep 5499161 = 4124371) B4124371
theorem B3666107 : Blo 2033435 3666107 := bstep (se 1 (by rfl) ⟨2749580, by rfl⟩ : syracuseStep 3666107 = 5499161) B5499161
theorem B9776285 : Blo 2033435 9776285 := bstep (se 3 (by rfl) ⟨1833053, by rfl⟩ : syracuseStep 9776285 = 3666107) B3666107
theorem B6517523 : Blo 2033435 6517523 := bstep (se 1 (by rfl) ⟨4888142, by rfl⟩ : syracuseStep 6517523 = 9776285) B9776285
theorem B4345015 : Blo 2033435 4345015 := bstep (se 1 (by rfl) ⟨3258761, by rfl⟩ : syracuseStep 4345015 = 6517523) B6517523
theorem B5793353 : Blo 2033435 5793353 := bstep (se 2 (by rfl) ⟨2172507, by rfl⟩ : syracuseStep 5793353 = 4345015) B4345015
theorem B3862235 : Blo 2033435 3862235 := bstep (se 1 (by rfl) ⟨2896676, by rfl⟩ : syracuseStep 3862235 = 5793353) B5793353
theorem B2574823 : Blo 2033435 2574823 := bstep (se 1 (by rfl) ⟨1931117, by rfl⟩ : syracuseStep 2574823 = 3862235) B3862235
theorem B3433097 : Blo 2033435 3433097 := bstep (se 2 (by rfl) ⟨1287411, by rfl⟩ : syracuseStep 3433097 = 2574823) B2574823
theorem B2288731 : Blo 2033435 2288731 := bstep (se 1 (by rfl) ⟨1716548, by rfl⟩ : syracuseStep 2288731 = 3433097) B3433097
theorem B3051641 : Blo 2033435 3051641 := bstep (se 2 (by rfl) ⟨1144365, by rfl⟩ : syracuseStep 3051641 = 2288731) B2288731
theorem B2034427 : Blo 2033435 2034427 := bstep (se 1 (by rfl) ⟨1525820, by rfl⟩ : syracuseStep 2034427 = 3051641) B3051641
theorem B2062189 : Blo 2033435 2062189 := bbase (se 3 (by rfl) ⟨386660, by rfl⟩ : syracuseStep 2062189 = 773321) (by norm_num)
theorem B2749585 : Blo 2033435 2749585 := bstep (se 2 (by rfl) ⟨1031094, by rfl⟩ : syracuseStep 2749585 = 2062189) B2062189
theorem B3666113 : Blo 2033435 3666113 := bstep (se 2 (by rfl) ⟨1374792, by rfl⟩ : syracuseStep 3666113 = 2749585) B2749585
theorem B2444075 : Blo 2033435 2444075 := bstep (se 1 (by rfl) ⟨1833056, by rfl⟩ : syracuseStep 2444075 = 3666113) B3666113
theorem B26070133 : Blo 2033435 26070133 := bstep (se 5 (by rfl) ⟨1222037, by rfl⟩ : syracuseStep 26070133 = 2444075) B2444075
theorem B34760177 : Blo 2033435 34760177 := bstep (se 2 (by rfl) ⟨13035066, by rfl⟩ : syracuseStep 34760177 = 26070133) B26070133
theorem B23173451 : Blo 2033435 23173451 := bstep (se 1 (by rfl) ⟨17380088, by rfl⟩ : syracuseStep 23173451 = 34760177) B34760177
theorem B15448967 : Blo 2033435 15448967 := bstep (se 1 (by rfl) ⟨11586725, by rfl⟩ : syracuseStep 15448967 = 23173451) B23173451
theorem B10299311 : Blo 2033435 10299311 := bstep (se 1 (by rfl) ⟨7724483, by rfl⟩ : syracuseStep 10299311 = 15448967) B15448967
theorem B6866207 : Blo 2033435 6866207 := bstep (se 1 (by rfl) ⟨5149655, by rfl⟩ : syracuseStep 6866207 = 10299311) B10299311
theorem B4577471 : Blo 2033435 4577471 := bstep (se 1 (by rfl) ⟨3433103, by rfl⟩ : syracuseStep 4577471 = 6866207) B6866207
theorem B3051647 : Blo 2033435 3051647 := bstep (se 1 (by rfl) ⟨2288735, by rfl⟩ : syracuseStep 3051647 = 4577471) B4577471
theorem B2034431 : Blo 2033435 2034431 := bstep (se 1 (by rfl) ⟨1525823, by rfl⟩ : syracuseStep 2034431 = 3051647) B3051647
theorem B3051653 : Blo 2033435 3051653 := bbase (se 4 (by rfl) ⟨286092, by rfl⟩ : syracuseStep 3051653 = 572185) (by norm_num)
theorem B2034435 : Blo 2033435 2034435 := bstep (se 1 (by rfl) ⟨1525826, by rfl⟩ : syracuseStep 2034435 = 3051653) B3051653
theorem B3433117 : Blo 2033435 3433117 := bbase (se 3 (by rfl) ⟨643709, by rfl⟩ : syracuseStep 3433117 = 1287419) (by norm_num)
theorem B4577489 : Blo 2033435 4577489 := bstep (se 2 (by rfl) ⟨1716558, by rfl⟩ : syracuseStep 4577489 = 3433117) B3433117
theorem B3051659 : Blo 2033435 3051659 := bstep (se 1 (by rfl) ⟨2288744, by rfl⟩ : syracuseStep 3051659 = 4577489) B4577489
theorem B2034439 : Blo 2033435 2034439 := bstep (se 1 (by rfl) ⟨1525829, by rfl⟩ : syracuseStep 2034439 = 3051659) B3051659
theorem B2288749 : Blo 2033435 2288749 := bbase (se 3 (by rfl) ⟨429140, by rfl⟩ : syracuseStep 2288749 = 858281) (by norm_num)
theorem B3051665 : Blo 2033435 3051665 := bstep (se 2 (by rfl) ⟨1144374, by rfl⟩ : syracuseStep 3051665 = 2288749) B2288749
theorem B2034443 : Blo 2033435 2034443 := bstep (se 1 (by rfl) ⟨1525832, by rfl⟩ : syracuseStep 2034443 = 3051665) B3051665
theorem B6866261 : Blo 2033435 6866261 := bbase (se 12 (by rfl) ⟨2514, by rfl⟩ : syracuseStep 6866261 = 5029) (by norm_num)
theorem B4577507 : Blo 2033435 4577507 := bstep (se 1 (by rfl) ⟨3433130, by rfl⟩ : syracuseStep 4577507 = 6866261) B6866261
theorem B3051671 : Blo 2033435 3051671 := bstep (se 1 (by rfl) ⟨2288753, by rfl⟩ : syracuseStep 3051671 = 4577507) B4577507
theorem B2034447 : Blo 2033435 2034447 := bstep (se 1 (by rfl) ⟨1525835, by rfl⟩ : syracuseStep 2034447 = 3051671) B3051671
theorem B3051677 : Blo 2033435 3051677 := bbase (se 3 (by rfl) ⟨572189, by rfl⟩ : syracuseStep 3051677 = 1144379) (by norm_num)
theorem B2034451 : Blo 2033435 2034451 := bstep (se 1 (by rfl) ⟨1525838, by rfl⟩ : syracuseStep 2034451 = 3051677) B3051677
theorem B4577525 : Blo 2033435 4577525 := bbase (se 5 (by rfl) ⟨214571, by rfl⟩ : syracuseStep 4577525 = 429143) (by norm_num)
theorem B3051683 : Blo 2033435 3051683 := bstep (se 1 (by rfl) ⟨2288762, by rfl⟩ : syracuseStep 3051683 = 4577525) B4577525
theorem B2034455 : Blo 2033435 2034455 := bstep (se 1 (by rfl) ⟨1525841, by rfl⟩ : syracuseStep 2034455 = 3051683) B3051683
theorem B8361413 : Blo 2033435 8361413 := bbase (se 4 (by rfl) ⟨783882, by rfl⟩ : syracuseStep 8361413 = 1567765) (by norm_num)
theorem B5574275 : Blo 2033435 5574275 := bstep (se 1 (by rfl) ⟨4180706, by rfl⟩ : syracuseStep 5574275 = 8361413) B8361413
theorem B3716183 : Blo 2033435 3716183 := bstep (se 1 (by rfl) ⟨2787137, by rfl⟩ : syracuseStep 3716183 = 5574275) B5574275
theorem B9909821 : Blo 2033435 9909821 := bstep (se 3 (by rfl) ⟨1858091, by rfl⟩ : syracuseStep 9909821 = 3716183) B3716183
theorem B26426189 : Blo 2033435 26426189 := bstep (se 3 (by rfl) ⟨4954910, by rfl⟩ : syracuseStep 26426189 = 9909821) B9909821
theorem B17617459 : Blo 2033435 17617459 := bstep (se 1 (by rfl) ⟨13213094, by rfl⟩ : syracuseStep 17617459 = 26426189) B26426189
theorem B23489945 : Blo 2033435 23489945 := bstep (se 2 (by rfl) ⟨8808729, by rfl⟩ : syracuseStep 23489945 = 17617459) B17617459
theorem B15659963 : Blo 2033435 15659963 := bstep (se 1 (by rfl) ⟨11744972, by rfl⟩ : syracuseStep 15659963 = 23489945) B23489945
theorem B10439975 : Blo 2033435 10439975 := bstep (se 1 (by rfl) ⟨7829981, by rfl⟩ : syracuseStep 10439975 = 15659963) B15659963
theorem B27839933 : Blo 2033435 27839933 := bstep (se 3 (by rfl) ⟨5219987, by rfl⟩ : syracuseStep 27839933 = 10439975) B10439975
theorem B18559955 : Blo 2033435 18559955 := bstep (se 1 (by rfl) ⟨13919966, by rfl⟩ : syracuseStep 18559955 = 27839933) B27839933
theorem B49493213 : Blo 2033435 49493213 := bstep (se 3 (by rfl) ⟨9279977, by rfl⟩ : syracuseStep 49493213 = 18559955) B18559955
theorem B32995475 : Blo 2033435 32995475 := bstep (se 1 (by rfl) ⟨24746606, by rfl⟩ : syracuseStep 32995475 = 49493213) B49493213
theorem B21996983 : Blo 2033435 21996983 := bstep (se 1 (by rfl) ⟨16497737, by rfl⟩ : syracuseStep 21996983 = 32995475) B32995475
theorem B14664655 : Blo 2033435 14664655 := bstep (se 1 (by rfl) ⟨10998491, by rfl⟩ : syracuseStep 14664655 = 21996983) B21996983
theorem B19552873 : Blo 2033435 19552873 := bstep (se 2 (by rfl) ⟨7332327, by rfl⟩ : syracuseStep 19552873 = 14664655) B14664655
theorem B26070497 : Blo 2033435 26070497 := bstep (se 2 (by rfl) ⟨9776436, by rfl⟩ : syracuseStep 26070497 = 19552873) B19552873
theorem B17380331 : Blo 2033435 17380331 := bstep (se 1 (by rfl) ⟨13035248, by rfl⟩ : syracuseStep 17380331 = 26070497) B26070497
theorem B11586887 : Blo 2033435 11586887 := bstep (se 1 (by rfl) ⟨8690165, by rfl⟩ : syracuseStep 11586887 = 17380331) B17380331
theorem B7724591 : Blo 2033435 7724591 := bstep (se 1 (by rfl) ⟨5793443, by rfl⟩ : syracuseStep 7724591 = 11586887) B11586887
theorem B5149727 : Blo 2033435 5149727 := bstep (se 1 (by rfl) ⟨3862295, by rfl⟩ : syracuseStep 5149727 = 7724591) B7724591
theorem B3433151 : Blo 2033435 3433151 := bstep (se 1 (by rfl) ⟨2574863, by rfl⟩ : syracuseStep 3433151 = 5149727) B5149727
theorem B2288767 : Blo 2033435 2288767 := bstep (se 1 (by rfl) ⟨1716575, by rfl⟩ : syracuseStep 2288767 = 3433151) B3433151
theorem B3051689 : Blo 2033435 3051689 := bstep (se 2 (by rfl) ⟨1144383, by rfl⟩ : syracuseStep 3051689 = 2288767) B2288767
theorem B2034459 : Blo 2033435 2034459 := bstep (se 1 (by rfl) ⟨1525844, by rfl⟩ : syracuseStep 2034459 = 3051689) B3051689
theorem B6517637 : Blo 2033435 6517637 := bbase (se 4 (by rfl) ⟨611028, by rfl⟩ : syracuseStep 6517637 = 1222057) (by norm_num)
theorem B4345091 : Blo 2033435 4345091 := bstep (se 1 (by rfl) ⟨3258818, by rfl⟩ : syracuseStep 4345091 = 6517637) B6517637
theorem B2896727 : Blo 2033435 2896727 := bstep (se 1 (by rfl) ⟨2172545, by rfl⟩ : syracuseStep 2896727 = 4345091) B4345091
theorem B7724605 : Blo 2033435 7724605 := bstep (se 3 (by rfl) ⟨1448363, by rfl⟩ : syracuseStep 7724605 = 2896727) B2896727
theorem B10299473 : Blo 2033435 10299473 := bstep (se 2 (by rfl) ⟨3862302, by rfl⟩ : syracuseStep 10299473 = 7724605) B7724605
theorem B6866315 : Blo 2033435 6866315 := bstep (se 1 (by rfl) ⟨5149736, by rfl⟩ : syracuseStep 6866315 = 10299473) B10299473
theorem B4577543 : Blo 2033435 4577543 := bstep (se 1 (by rfl) ⟨3433157, by rfl⟩ : syracuseStep 4577543 = 6866315) B6866315
theorem B3051695 : Blo 2033435 3051695 := bstep (se 1 (by rfl) ⟨2288771, by rfl⟩ : syracuseStep 3051695 = 4577543) B4577543
theorem B2034463 : Blo 2033435 2034463 := bstep (se 1 (by rfl) ⟨1525847, by rfl⟩ : syracuseStep 2034463 = 3051695) B3051695
theorem B3051701 : Blo 2033435 3051701 := bbase (se 5 (by rfl) ⟨143048, by rfl⟩ : syracuseStep 3051701 = 286097) (by norm_num)
theorem B2034467 : Blo 2033435 2034467 := bstep (se 1 (by rfl) ⟨1525850, by rfl⟩ : syracuseStep 2034467 = 3051701) B3051701
theorem B5149757 : Blo 2033435 5149757 := bbase (se 3 (by rfl) ⟨965579, by rfl⟩ : syracuseStep 5149757 = 1931159) (by norm_num)
theorem B3433171 : Blo 2033435 3433171 := bstep (se 1 (by rfl) ⟨2574878, by rfl⟩ : syracuseStep 3433171 = 5149757) B5149757
theorem B4577561 : Blo 2033435 4577561 := bstep (se 2 (by rfl) ⟨1716585, by rfl⟩ : syracuseStep 4577561 = 3433171) B3433171
theorem B3051707 : Blo 2033435 3051707 := bstep (se 1 (by rfl) ⟨2288780, by rfl⟩ : syracuseStep 3051707 = 4577561) B4577561
theorem B2034471 : Blo 2033435 2034471 := bstep (se 1 (by rfl) ⟨1525853, by rfl⟩ : syracuseStep 2034471 = 3051707) B3051707
theorem B2288785 : Blo 2033435 2288785 := bbase (se 2 (by rfl) ⟨858294, by rfl⟩ : syracuseStep 2288785 = 1716589) (by norm_num)
theorem B3051713 : Blo 2033435 3051713 := bstep (se 2 (by rfl) ⟨1144392, by rfl⟩ : syracuseStep 3051713 = 2288785) B2288785
theorem B2034475 : Blo 2033435 2034475 := bstep (se 1 (by rfl) ⟨1525856, by rfl⟩ : syracuseStep 2034475 = 3051713) B3051713
theorem B3862333 : Blo 2033435 3862333 := bbase (se 3 (by rfl) ⟨724187, by rfl⟩ : syracuseStep 3862333 = 1448375) (by norm_num)
theorem B5149777 : Blo 2033435 5149777 := bstep (se 2 (by rfl) ⟨1931166, by rfl⟩ : syracuseStep 5149777 = 3862333) B3862333
theorem B6866369 : Blo 2033435 6866369 := bstep (se 2 (by rfl) ⟨2574888, by rfl⟩ : syracuseStep 6866369 = 5149777) B5149777
theorem B4577579 : Blo 2033435 4577579 := bstep (se 1 (by rfl) ⟨3433184, by rfl⟩ : syracuseStep 4577579 = 6866369) B6866369
theorem B3051719 : Blo 2033435 3051719 := bstep (se 1 (by rfl) ⟨2288789, by rfl⟩ : syracuseStep 3051719 = 4577579) B4577579
theorem B2034479 : Blo 2033435 2034479 := bstep (se 1 (by rfl) ⟨1525859, by rfl⟩ : syracuseStep 2034479 = 3051719) B3051719
theorem B3051725 : Blo 2033435 3051725 := bbase (se 3 (by rfl) ⟨572198, by rfl⟩ : syracuseStep 3051725 = 1144397) (by norm_num)
theorem B2034483 : Blo 2033435 2034483 := bstep (se 1 (by rfl) ⟨1525862, by rfl⟩ : syracuseStep 2034483 = 3051725) B3051725
theorem B4577597 : Blo 2033435 4577597 := bbase (se 3 (by rfl) ⟨858299, by rfl⟩ : syracuseStep 4577597 = 1716599) (by norm_num)
theorem B3051731 : Blo 2033435 3051731 := bstep (se 1 (by rfl) ⟨2288798, by rfl⟩ : syracuseStep 3051731 = 4577597) B4577597
theorem B2034487 : Blo 2033435 2034487 := bstep (se 1 (by rfl) ⟨1525865, by rfl⟩ : syracuseStep 2034487 = 3051731) B3051731
theorem B3433205 : Blo 2033435 3433205 := bbase (se 5 (by rfl) ⟨160931, by rfl⟩ : syracuseStep 3433205 = 321863) (by norm_num)
theorem B2288803 : Blo 2033435 2288803 := bstep (se 1 (by rfl) ⟨1716602, by rfl⟩ : syracuseStep 2288803 = 3433205) B3433205
theorem B3051737 : Blo 2033435 3051737 := bstep (se 2 (by rfl) ⟨1144401, by rfl⟩ : syracuseStep 3051737 = 2288803) B2288803
theorem B2034491 : Blo 2033435 2034491 := bstep (se 1 (by rfl) ⟨1525868, by rfl⟩ : syracuseStep 2034491 = 3051737) B3051737
theorem B4180781 : Blo 2033435 4180781 := bbase (se 3 (by rfl) ⟨783896, by rfl⟩ : syracuseStep 4180781 = 1567793) (by norm_num)
theorem B11148749 : Blo 2033435 11148749 := bstep (se 3 (by rfl) ⟨2090390, by rfl⟩ : syracuseStep 11148749 = 4180781) B4180781
theorem B7432499 : Blo 2033435 7432499 := bstep (se 1 (by rfl) ⟨5574374, by rfl⟩ : syracuseStep 7432499 = 11148749) B11148749
theorem B19819997 : Blo 2033435 19819997 := bstep (se 3 (by rfl) ⟨3716249, by rfl⟩ : syracuseStep 19819997 = 7432499) B7432499
theorem B13213331 : Blo 2033435 13213331 := bstep (se 1 (by rfl) ⟨9909998, by rfl⟩ : syracuseStep 13213331 = 19819997) B19819997
theorem B8808887 : Blo 2033435 8808887 := bstep (se 1 (by rfl) ⟨6606665, by rfl⟩ : syracuseStep 8808887 = 13213331) B13213331
theorem B5872591 : Blo 2033435 5872591 := bstep (se 1 (by rfl) ⟨4404443, by rfl⟩ : syracuseStep 5872591 = 8808887) B8808887
theorem B7830121 : Blo 2033435 7830121 := bstep (se 2 (by rfl) ⟨2936295, by rfl⟩ : syracuseStep 7830121 = 5872591) B5872591
theorem B10440161 : Blo 2033435 10440161 := bstep (se 2 (by rfl) ⟨3915060, by rfl⟩ : syracuseStep 10440161 = 7830121) B7830121
theorem B6960107 : Blo 2033435 6960107 := bstep (se 1 (by rfl) ⟨5220080, by rfl⟩ : syracuseStep 6960107 = 10440161) B10440161
theorem B18560285 : Blo 2033435 18560285 := bstep (se 3 (by rfl) ⟨3480053, by rfl⟩ : syracuseStep 18560285 = 6960107) B6960107
theorem B12373523 : Blo 2033435 12373523 := bstep (se 1 (by rfl) ⟨9280142, by rfl⟩ : syracuseStep 12373523 = 18560285) B18560285
theorem B8249015 : Blo 2033435 8249015 := bstep (se 1 (by rfl) ⟨6186761, by rfl⟩ : syracuseStep 8249015 = 12373523) B12373523
theorem B5499343 : Blo 2033435 5499343 := bstep (se 1 (by rfl) ⟨4124507, by rfl⟩ : syracuseStep 5499343 = 8249015) B8249015
theorem B7332457 : Blo 2033435 7332457 := bstep (se 2 (by rfl) ⟨2749671, by rfl⟩ : syracuseStep 7332457 = 5499343) B5499343
theorem B9776609 : Blo 2033435 9776609 := bstep (se 2 (by rfl) ⟨3666228, by rfl⟩ : syracuseStep 9776609 = 7332457) B7332457
theorem B6517739 : Blo 2033435 6517739 := bstep (se 1 (by rfl) ⟨4888304, by rfl⟩ : syracuseStep 6517739 = 9776609) B9776609
theorem B4345159 : Blo 2033435 4345159 := bstep (se 1 (by rfl) ⟨3258869, by rfl⟩ : syracuseStep 4345159 = 6517739) B6517739
theorem B5793545 : Blo 2033435 5793545 := bstep (se 2 (by rfl) ⟨2172579, by rfl⟩ : syracuseStep 5793545 = 4345159) B4345159
theorem B15449453 : Blo 2033435 15449453 := bstep (se 3 (by rfl) ⟨2896772, by rfl⟩ : syracuseStep 15449453 = 5793545) B5793545
theorem B10299635 : Blo 2033435 10299635 := bstep (se 1 (by rfl) ⟨7724726, by rfl⟩ : syracuseStep 10299635 = 15449453) B15449453
theorem B6866423 : Blo 2033435 6866423 := bstep (se 1 (by rfl) ⟨5149817, by rfl⟩ : syracuseStep 6866423 = 10299635) B10299635
theorem B4577615 : Blo 2033435 4577615 := bstep (se 1 (by rfl) ⟨3433211, by rfl⟩ : syracuseStep 4577615 = 6866423) B6866423
theorem B3051743 : Blo 2033435 3051743 := bstep (se 1 (by rfl) ⟨2288807, by rfl⟩ : syracuseStep 3051743 = 4577615) B4577615
theorem B2034495 : Blo 2033435 2034495 := bstep (se 1 (by rfl) ⟨1525871, by rfl⟩ : syracuseStep 2034495 = 3051743) B3051743
theorem B3051749 : Blo 2033435 3051749 := bbase (se 4 (by rfl) ⟨286101, by rfl⟩ : syracuseStep 3051749 = 572203) (by norm_num)
theorem B2034499 : Blo 2033435 2034499 := bstep (se 1 (by rfl) ⟨1525874, by rfl⟩ : syracuseStep 2034499 = 3051749) B3051749
theorem B4888325 : Blo 2033435 4888325 := bbase (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) (by norm_num)
theorem B3258883 : Blo 2033435 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B4345177 : Blo 2033435 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B5793569 : Blo 2033435 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B3862379 : Blo 2033435 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B2574919 : Blo 2033435 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B3433225 : Blo 2033435 3433225 := bstep (se 2 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 3433225 = 2574919) B2574919
theorem B4577633 : Blo 2033435 4577633 := bstep (se 2 (by rfl) ⟨1716612, by rfl⟩ : syracuseStep 4577633 = 3433225) B3433225
theorem B3051755 : Blo 2033435 3051755 := bstep (se 1 (by rfl) ⟨2288816, by rfl⟩ : syracuseStep 3051755 = 4577633) B4577633
theorem B2034503 : Blo 2033435 2034503 := bstep (se 1 (by rfl) ⟨1525877, by rfl⟩ : syracuseStep 2034503 = 3051755) B3051755
theorem B2288821 : Blo 2033435 2288821 := bbase (se 5 (by rfl) ⟨107288, by rfl⟩ : syracuseStep 2288821 = 214577) (by norm_num)
theorem B3051761 : Blo 2033435 3051761 := bstep (se 2 (by rfl) ⟨1144410, by rfl⟩ : syracuseStep 3051761 = 2288821) B2288821
theorem B2034507 : Blo 2033435 2034507 := bstep (se 1 (by rfl) ⟨1525880, by rfl⟩ : syracuseStep 2034507 = 3051761) B3051761
theorem B2574929 : Blo 2033435 2574929 := bbase (se 2 (by rfl) ⟨965598, by rfl⟩ : syracuseStep 2574929 = 1931197) (by norm_num)
theorem B6866477 : Blo 2033435 6866477 := bstep (se 3 (by rfl) ⟨1287464, by rfl⟩ : syracuseStep 6866477 = 2574929) B2574929
theorem B4577651 : Blo 2033435 4577651 := bstep (se 1 (by rfl) ⟨3433238, by rfl⟩ : syracuseStep 4577651 = 6866477) B6866477
theorem B3051767 : Blo 2033435 3051767 := bstep (se 1 (by rfl) ⟨2288825, by rfl⟩ : syracuseStep 3051767 = 4577651) B4577651
theorem B2034511 : Blo 2033435 2034511 := bstep (se 1 (by rfl) ⟨1525883, by rfl⟩ : syracuseStep 2034511 = 3051767) B3051767
theorem B3051773 : Blo 2033435 3051773 := bbase (se 3 (by rfl) ⟨572207, by rfl⟩ : syracuseStep 3051773 = 1144415) (by norm_num)
theorem B2034515 : Blo 2033435 2034515 := bstep (se 1 (by rfl) ⟨1525886, by rfl⟩ : syracuseStep 2034515 = 3051773) B3051773
theorem B4577669 : Blo 2033435 4577669 := bbase (se 4 (by rfl) ⟨429156, by rfl⟩ : syracuseStep 4577669 = 858313) (by norm_num)
theorem B3051779 : Blo 2033435 3051779 := bstep (se 1 (by rfl) ⟨2288834, by rfl⟩ : syracuseStep 3051779 = 4577669) B4577669
theorem B2034519 : Blo 2033435 2034519 := bstep (se 1 (by rfl) ⟨1525889, by rfl⟩ : syracuseStep 2034519 = 3051779) B3051779
theorem B2896813 : Blo 2033435 2896813 := bbase (se 3 (by rfl) ⟨543152, by rfl⟩ : syracuseStep 2896813 = 1086305) (by norm_num)
theorem B3862417 : Blo 2033435 3862417 := bstep (se 2 (by rfl) ⟨1448406, by rfl⟩ : syracuseStep 3862417 = 2896813) B2896813
theorem B5149889 : Blo 2033435 5149889 := bstep (se 2 (by rfl) ⟨1931208, by rfl⟩ : syracuseStep 5149889 = 3862417) B3862417
theorem B3433259 : Blo 2033435 3433259 := bstep (se 1 (by rfl) ⟨2574944, by rfl⟩ : syracuseStep 3433259 = 5149889) B5149889
theorem B2288839 : Blo 2033435 2288839 := bstep (se 1 (by rfl) ⟨1716629, by rfl⟩ : syracuseStep 2288839 = 3433259) B3433259
theorem B3051785 : Blo 2033435 3051785 := bstep (se 2 (by rfl) ⟨1144419, by rfl⟩ : syracuseStep 3051785 = 2288839) B2288839
theorem B2034523 : Blo 2033435 2034523 := bstep (se 1 (by rfl) ⟨1525892, by rfl⟩ : syracuseStep 2034523 = 3051785) B3051785
theorem B10299797 : Blo 2033435 10299797 := bbase (se 6 (by rfl) ⟨241401, by rfl⟩ : syracuseStep 10299797 = 482803) (by norm_num)
theorem B6866531 : Blo 2033435 6866531 := bstep (se 1 (by rfl) ⟨5149898, by rfl⟩ : syracuseStep 6866531 = 10299797) B10299797
theorem B4577687 : Blo 2033435 4577687 := bstep (se 1 (by rfl) ⟨3433265, by rfl⟩ : syracuseStep 4577687 = 6866531) B6866531
theorem B3051791 : Blo 2033435 3051791 := bstep (se 1 (by rfl) ⟨2288843, by rfl⟩ : syracuseStep 3051791 = 4577687) B4577687
theorem B2034527 : Blo 2033435 2034527 := bstep (se 1 (by rfl) ⟨1525895, by rfl⟩ : syracuseStep 2034527 = 3051791) B3051791
theorem B3051797 : Blo 2033435 3051797 := bbase (se 6 (by rfl) ⟨71526, by rfl⟩ : syracuseStep 3051797 = 143053) (by norm_num)
theorem B2034531 : Blo 2033435 2034531 := bstep (se 1 (by rfl) ⟨1525898, by rfl⟩ : syracuseStep 2034531 = 3051797) B3051797
theorem B9280325 : Blo 2033435 9280325 := bbase (se 4 (by rfl) ⟨870030, by rfl⟩ : syracuseStep 9280325 = 1740061) (by norm_num)
theorem B6186883 : Blo 2033435 6186883 := bstep (se 1 (by rfl) ⟨4640162, by rfl⟩ : syracuseStep 6186883 = 9280325) B9280325
theorem B8249177 : Blo 2033435 8249177 := bstep (se 2 (by rfl) ⟨3093441, by rfl⟩ : syracuseStep 8249177 = 6186883) B6186883
theorem B5499451 : Blo 2033435 5499451 := bstep (se 1 (by rfl) ⟨4124588, by rfl⟩ : syracuseStep 5499451 = 8249177) B8249177
theorem B7332601 : Blo 2033435 7332601 := bstep (se 2 (by rfl) ⟨2749725, by rfl⟩ : syracuseStep 7332601 = 5499451) B5499451
theorem B9776801 : Blo 2033435 9776801 := bstep (se 2 (by rfl) ⟨3666300, by rfl⟩ : syracuseStep 9776801 = 7332601) B7332601
theorem B26071469 : Blo 2033435 26071469 := bstep (se 3 (by rfl) ⟨4888400, by rfl⟩ : syracuseStep 26071469 = 9776801) B9776801
theorem B17380979 : Blo 2033435 17380979 := bstep (se 1 (by rfl) ⟨13035734, by rfl⟩ : syracuseStep 17380979 = 26071469) B26071469
theorem B11587319 : Blo 2033435 11587319 := bstep (se 1 (by rfl) ⟨8690489, by rfl⟩ : syracuseStep 11587319 = 17380979) B17380979
theorem B7724879 : Blo 2033435 7724879 := bstep (se 1 (by rfl) ⟨5793659, by rfl⟩ : syracuseStep 7724879 = 11587319) B11587319
theorem B5149919 : Blo 2033435 5149919 := bstep (se 1 (by rfl) ⟨3862439, by rfl⟩ : syracuseStep 5149919 = 7724879) B7724879
theorem B3433279 : Blo 2033435 3433279 := bstep (se 1 (by rfl) ⟨2574959, by rfl⟩ : syracuseStep 3433279 = 5149919) B5149919
theorem B4577705 : Blo 2033435 4577705 := bstep (se 2 (by rfl) ⟨1716639, by rfl⟩ : syracuseStep 4577705 = 3433279) B3433279
theorem B3051803 : Blo 2033435 3051803 := bstep (se 1 (by rfl) ⟨2288852, by rfl⟩ : syracuseStep 3051803 = 4577705) B4577705
theorem B2034535 : Blo 2033435 2034535 := bstep (se 1 (by rfl) ⟨1525901, by rfl⟩ : syracuseStep 2034535 = 3051803) B3051803
theorem B2288857 : Blo 2033435 2288857 := bbase (se 2 (by rfl) ⟨858321, by rfl⟩ : syracuseStep 2288857 = 1716643) (by norm_num)
theorem B3051809 : Blo 2033435 3051809 := bstep (se 2 (by rfl) ⟨1144428, by rfl⟩ : syracuseStep 3051809 = 2288857) B2288857
theorem B2034539 : Blo 2033435 2034539 := bstep (se 1 (by rfl) ⟨1525904, by rfl⟩ : syracuseStep 2034539 = 3051809) B3051809
theorem B4888421 : Blo 2033435 4888421 := bbase (se 4 (by rfl) ⟨458289, by rfl⟩ : syracuseStep 4888421 = 916579) (by norm_num)
theorem B3258947 : Blo 2033435 3258947 := bstep (se 1 (by rfl) ⟨2444210, by rfl⟩ : syracuseStep 3258947 = 4888421) B4888421
theorem B2172631 : Blo 2033435 2172631 := bstep (se 1 (by rfl) ⟨1629473, by rfl⟩ : syracuseStep 2172631 = 3258947) B3258947
theorem B2896841 : Blo 2033435 2896841 := bstep (se 2 (by rfl) ⟨1086315, by rfl⟩ : syracuseStep 2896841 = 2172631) B2172631
theorem B7724909 : Blo 2033435 7724909 := bstep (se 3 (by rfl) ⟨1448420, by rfl⟩ : syracuseStep 7724909 = 2896841) B2896841
theorem B5149939 : Blo 2033435 5149939 := bstep (se 1 (by rfl) ⟨3862454, by rfl⟩ : syracuseStep 5149939 = 7724909) B7724909
theorem B6866585 : Blo 2033435 6866585 := bstep (se 2 (by rfl) ⟨2574969, by rfl⟩ : syracuseStep 6866585 = 5149939) B5149939
theorem B4577723 : Blo 2033435 4577723 := bstep (se 1 (by rfl) ⟨3433292, by rfl⟩ : syracuseStep 4577723 = 6866585) B6866585
theorem B3051815 : Blo 2033435 3051815 := bstep (se 1 (by rfl) ⟨2288861, by rfl⟩ : syracuseStep 3051815 = 4577723) B4577723
theorem B2034543 : Blo 2033435 2034543 := bstep (se 1 (by rfl) ⟨1525907, by rfl⟩ : syracuseStep 2034543 = 3051815) B3051815
theorem B3051821 : Blo 2033435 3051821 := bbase (se 3 (by rfl) ⟨572216, by rfl⟩ : syracuseStep 3051821 = 1144433) (by norm_num)
theorem B2034547 : Blo 2033435 2034547 := bstep (se 1 (by rfl) ⟨1525910, by rfl⟩ : syracuseStep 2034547 = 3051821) B3051821
theorem B4577741 : Blo 2033435 4577741 := bbase (se 3 (by rfl) ⟨858326, by rfl⟩ : syracuseStep 4577741 = 1716653) (by norm_num)
theorem B3051827 : Blo 2033435 3051827 := bstep (se 1 (by rfl) ⟨2288870, by rfl⟩ : syracuseStep 3051827 = 4577741) B4577741
theorem B2034551 : Blo 2033435 2034551 := bstep (se 1 (by rfl) ⟨1525913, by rfl⟩ : syracuseStep 2034551 = 3051827) B3051827
theorem B2574985 : Blo 2033435 2574985 := bbase (se 2 (by rfl) ⟨965619, by rfl⟩ : syracuseStep 2574985 = 1931239) (by norm_num)
theorem B3433313 : Blo 2033435 3433313 := bstep (se 2 (by rfl) ⟨1287492, by rfl⟩ : syracuseStep 3433313 = 2574985) B2574985
theorem B2288875 : Blo 2033435 2288875 := bstep (se 1 (by rfl) ⟨1716656, by rfl⟩ : syracuseStep 2288875 = 3433313) B3433313
theorem B3051833 : Blo 2033435 3051833 := bstep (se 2 (by rfl) ⟨1144437, by rfl⟩ : syracuseStep 3051833 = 2288875) B2288875
theorem B2034555 : Blo 2033435 2034555 := bstep (se 1 (by rfl) ⟨1525916, by rfl⟩ : syracuseStep 2034555 = 3051833) B3051833
theorem B49495637 : Blo 2033435 49495637 := bbase (se 8 (by rfl) ⟨290013, by rfl⟩ : syracuseStep 49495637 = 580027) (by norm_num)
theorem B32997091 : Blo 2033435 32997091 := bstep (se 1 (by rfl) ⟨24747818, by rfl⟩ : syracuseStep 32997091 = 49495637) B49495637
theorem B43996121 : Blo 2033435 43996121 := bstep (se 2 (by rfl) ⟨16498545, by rfl⟩ : syracuseStep 43996121 = 32997091) B32997091
theorem B29330747 : Blo 2033435 29330747 := bstep (se 1 (by rfl) ⟨21998060, by rfl⟩ : syracuseStep 29330747 = 43996121) B43996121
theorem B19553831 : Blo 2033435 19553831 := bstep (se 1 (by rfl) ⟨14665373, by rfl⟩ : syracuseStep 19553831 = 29330747) B29330747
theorem B13035887 : Blo 2033435 13035887 := bstep (se 1 (by rfl) ⟨9776915, by rfl⟩ : syracuseStep 13035887 = 19553831) B19553831
theorem B8690591 : Blo 2033435 8690591 := bstep (se 1 (by rfl) ⟨6517943, by rfl⟩ : syracuseStep 8690591 = 13035887) B13035887
theorem B23174909 : Blo 2033435 23174909 := bstep (se 3 (by rfl) ⟨4345295, by rfl⟩ : syracuseStep 23174909 = 8690591) B8690591
theorem B15449939 : Blo 2033435 15449939 := bstep (se 1 (by rfl) ⟨11587454, by rfl⟩ : syracuseStep 15449939 = 23174909) B23174909
theorem B10299959 : Blo 2033435 10299959 := bstep (se 1 (by rfl) ⟨7724969, by rfl⟩ : syracuseStep 10299959 = 15449939) B15449939
theorem B6866639 : Blo 2033435 6866639 := bstep (se 1 (by rfl) ⟨5149979, by rfl⟩ : syracuseStep 6866639 = 10299959) B10299959
theorem B4577759 : Blo 2033435 4577759 := bstep (se 1 (by rfl) ⟨3433319, by rfl⟩ : syracuseStep 4577759 = 6866639) B6866639
theorem B3051839 : Blo 2033435 3051839 := bstep (se 1 (by rfl) ⟨2288879, by rfl⟩ : syracuseStep 3051839 = 4577759) B4577759
theorem B2034559 : Blo 2033435 2034559 := bstep (se 1 (by rfl) ⟨1525919, by rfl⟩ : syracuseStep 2034559 = 3051839) B3051839
theorem B3051845 : Blo 2033435 3051845 := bbase (se 4 (by rfl) ⟨286110, by rfl⟩ : syracuseStep 3051845 = 572221) (by norm_num)
theorem B2034563 : Blo 2033435 2034563 := bstep (se 1 (by rfl) ⟨1525922, by rfl⟩ : syracuseStep 2034563 = 3051845) B3051845
theorem B3433333 : Blo 2033435 3433333 := bbase (se 5 (by rfl) ⟨160937, by rfl⟩ : syracuseStep 3433333 = 321875) (by norm_num)
theorem B4577777 : Blo 2033435 4577777 := bstep (se 2 (by rfl) ⟨1716666, by rfl⟩ : syracuseStep 4577777 = 3433333) B3433333
theorem B3051851 : Blo 2033435 3051851 := bstep (se 1 (by rfl) ⟨2288888, by rfl⟩ : syracuseStep 3051851 = 4577777) B4577777
theorem B2034567 : Blo 2033435 2034567 := bstep (se 1 (by rfl) ⟨1525925, by rfl⟩ : syracuseStep 2034567 = 3051851) B3051851
theorem B2288893 : Blo 2033435 2288893 := bbase (se 3 (by rfl) ⟨429167, by rfl⟩ : syracuseStep 2288893 = 858335) (by norm_num)
theorem B3051857 : Blo 2033435 3051857 := bstep (se 2 (by rfl) ⟨1144446, by rfl⟩ : syracuseStep 3051857 = 2288893) B2288893
theorem B2034571 : Blo 2033435 2034571 := bstep (se 1 (by rfl) ⟨1525928, by rfl⟩ : syracuseStep 2034571 = 3051857) B3051857
theorem B6866693 : Blo 2033435 6866693 := bbase (se 4 (by rfl) ⟨643752, by rfl⟩ : syracuseStep 6866693 = 1287505) (by norm_num)
theorem B4577795 : Blo 2033435 4577795 := bstep (se 1 (by rfl) ⟨3433346, by rfl⟩ : syracuseStep 4577795 = 6866693) B6866693
theorem B3051863 : Blo 2033435 3051863 := bstep (se 1 (by rfl) ⟨2288897, by rfl⟩ : syracuseStep 3051863 = 4577795) B4577795
theorem B2034575 : Blo 2033435 2034575 := bstep (se 1 (by rfl) ⟨1525931, by rfl⟩ : syracuseStep 2034575 = 3051863) B3051863
theorem B3051869 : Blo 2033435 3051869 := bbase (se 3 (by rfl) ⟨572225, by rfl⟩ : syracuseStep 3051869 = 1144451) (by norm_num)
theorem B2034579 : Blo 2033435 2034579 := bstep (se 1 (by rfl) ⟨1525934, by rfl⟩ : syracuseStep 2034579 = 3051869) B3051869
theorem B4577813 : Blo 2033435 4577813 := bbase (se 6 (by rfl) ⟨107292, by rfl⟩ : syracuseStep 4577813 = 214585) (by norm_num)
theorem B3051875 : Blo 2033435 3051875 := bstep (se 1 (by rfl) ⟨2288906, by rfl⟩ : syracuseStep 3051875 = 4577813) B4577813
theorem B2034583 : Blo 2033435 2034583 := bstep (se 1 (by rfl) ⟨1525937, by rfl⟩ : syracuseStep 2034583 = 3051875) B3051875
theorem B7725077 : Blo 2033435 7725077 := bbase (se 6 (by rfl) ⟨181056, by rfl⟩ : syracuseStep 7725077 = 362113) (by norm_num)
theorem B5150051 : Blo 2033435 5150051 := bstep (se 1 (by rfl) ⟨3862538, by rfl⟩ : syracuseStep 5150051 = 7725077) B7725077
theorem B3433367 : Blo 2033435 3433367 := bstep (se 1 (by rfl) ⟨2575025, by rfl⟩ : syracuseStep 3433367 = 5150051) B5150051
theorem B2288911 : Blo 2033435 2288911 := bstep (se 1 (by rfl) ⟨1716683, by rfl⟩ : syracuseStep 2288911 = 3433367) B3433367
theorem B3051881 : Blo 2033435 3051881 := bstep (se 2 (by rfl) ⟨1144455, by rfl⟩ : syracuseStep 3051881 = 2288911) B2288911
theorem B2034587 : Blo 2033435 2034587 := bstep (se 1 (by rfl) ⟨1525940, by rfl⟩ : syracuseStep 2034587 = 3051881) B3051881
theorem B11587637 : Blo 2033435 11587637 := bbase (se 5 (by rfl) ⟨543170, by rfl⟩ : syracuseStep 11587637 = 1086341) (by norm_num)
theorem B7725091 : Blo 2033435 7725091 := bstep (se 1 (by rfl) ⟨5793818, by rfl⟩ : syracuseStep 7725091 = 11587637) B11587637
theorem B10300121 : Blo 2033435 10300121 := bstep (se 2 (by rfl) ⟨3862545, by rfl⟩ : syracuseStep 10300121 = 7725091) B7725091
theorem B6866747 : Blo 2033435 6866747 := bstep (se 1 (by rfl) ⟨5150060, by rfl⟩ : syracuseStep 6866747 = 10300121) B10300121
theorem B4577831 : Blo 2033435 4577831 := bstep (se 1 (by rfl) ⟨3433373, by rfl⟩ : syracuseStep 4577831 = 6866747) B6866747
theorem B3051887 : Blo 2033435 3051887 := bstep (se 1 (by rfl) ⟨2288915, by rfl⟩ : syracuseStep 3051887 = 4577831) B4577831
theorem B2034591 : Blo 2033435 2034591 := bstep (se 1 (by rfl) ⟨1525943, by rfl⟩ : syracuseStep 2034591 = 3051887) B3051887
theorem B3051893 : Blo 2033435 3051893 := bbase (se 5 (by rfl) ⟨143057, by rfl⟩ : syracuseStep 3051893 = 286115) (by norm_num)
theorem B2034595 : Blo 2033435 2034595 := bstep (se 1 (by rfl) ⟨1525946, by rfl⟩ : syracuseStep 2034595 = 3051893) B3051893
theorem B3259037 : Blo 2033435 3259037 := bbase (se 3 (by rfl) ⟨611069, by rfl⟩ : syracuseStep 3259037 = 1222139) (by norm_num)
theorem B2172691 : Blo 2033435 2172691 := bstep (se 1 (by rfl) ⟨1629518, by rfl⟩ : syracuseStep 2172691 = 3259037) B3259037
theorem B2896921 : Blo 2033435 2896921 := bstep (se 2 (by rfl) ⟨1086345, by rfl⟩ : syracuseStep 2896921 = 2172691) B2172691
theorem B3862561 : Blo 2033435 3862561 := bstep (se 2 (by rfl) ⟨1448460, by rfl⟩ : syracuseStep 3862561 = 2896921) B2896921
theorem B5150081 : Blo 2033435 5150081 := bstep (se 2 (by rfl) ⟨1931280, by rfl⟩ : syracuseStep 5150081 = 3862561) B3862561
theorem B3433387 : Blo 2033435 3433387 := bstep (se 1 (by rfl) ⟨2575040, by rfl⟩ : syracuseStep 3433387 = 5150081) B5150081
theorem B4577849 : Blo 2033435 4577849 := bstep (se 2 (by rfl) ⟨1716693, by rfl⟩ : syracuseStep 4577849 = 3433387) B3433387
theorem B3051899 : Blo 2033435 3051899 := bstep (se 1 (by rfl) ⟨2288924, by rfl⟩ : syracuseStep 3051899 = 4577849) B4577849
theorem B2034599 : Blo 2033435 2034599 := bstep (se 1 (by rfl) ⟨1525949, by rfl⟩ : syracuseStep 2034599 = 3051899) B3051899
theorem B2288929 : Blo 2033435 2288929 := bbase (se 2 (by rfl) ⟨858348, by rfl⟩ : syracuseStep 2288929 = 1716697) (by norm_num)
theorem B3051905 : Blo 2033435 3051905 := bstep (se 2 (by rfl) ⟨1144464, by rfl⟩ : syracuseStep 3051905 = 2288929) B2288929
theorem B2034603 : Blo 2033435 2034603 := bstep (se 1 (by rfl) ⟨1525952, by rfl⟩ : syracuseStep 2034603 = 3051905) B3051905
theorem B5150101 : Blo 2033435 5150101 := bbase (se 6 (by rfl) ⟨120705, by rfl⟩ : syracuseStep 5150101 = 241411) (by norm_num)
theorem B6866801 : Blo 2033435 6866801 := bstep (se 2 (by rfl) ⟨2575050, by rfl⟩ : syracuseStep 6866801 = 5150101) B5150101
theorem B4577867 : Blo 2033435 4577867 := bstep (se 1 (by rfl) ⟨3433400, by rfl⟩ : syracuseStep 4577867 = 6866801) B6866801
theorem B3051911 : Blo 2033435 3051911 := bstep (se 1 (by rfl) ⟨2288933, by rfl⟩ : syracuseStep 3051911 = 4577867) B4577867
theorem B2034607 : Blo 2033435 2034607 := bstep (se 1 (by rfl) ⟨1525955, by rfl⟩ : syracuseStep 2034607 = 3051911) B3051911
theorem B3051917 : Blo 2033435 3051917 := bbase (se 3 (by rfl) ⟨572234, by rfl⟩ : syracuseStep 3051917 = 1144469) (by norm_num)
theorem B2034611 : Blo 2033435 2034611 := bstep (se 1 (by rfl) ⟨1525958, by rfl⟩ : syracuseStep 2034611 = 3051917) B3051917
theorem B4577885 : Blo 2033435 4577885 := bbase (se 3 (by rfl) ⟨858353, by rfl⟩ : syracuseStep 4577885 = 1716707) (by norm_num)
theorem B3051923 : Blo 2033435 3051923 := bstep (se 1 (by rfl) ⟨2288942, by rfl⟩ : syracuseStep 3051923 = 4577885) B4577885
theorem B2034615 : Blo 2033435 2034615 := bstep (se 1 (by rfl) ⟨1525961, by rfl⟩ : syracuseStep 2034615 = 3051923) B3051923
theorem B3433421 : Blo 2033435 3433421 := bbase (se 3 (by rfl) ⟨643766, by rfl⟩ : syracuseStep 3433421 = 1287533) (by norm_num)
theorem B2288947 : Blo 2033435 2288947 := bstep (se 1 (by rfl) ⟨1716710, by rfl⟩ : syracuseStep 2288947 = 3433421) B3433421
theorem B3051929 : Blo 2033435 3051929 := bstep (se 2 (by rfl) ⟨1144473, by rfl⟩ : syracuseStep 3051929 = 2288947) B2288947
theorem B2034619 : Blo 2033435 2034619 := bstep (se 1 (by rfl) ⟨1525964, by rfl⟩ : syracuseStep 2034619 = 3051929) B3051929
theorem B7055509 : Blo 2033435 7055509 := bbase (se 6 (by rfl) ⟨165363, by rfl⟩ : syracuseStep 7055509 = 330727) (by norm_num)
theorem B9407345 : Blo 2033435 9407345 := bstep (se 2 (by rfl) ⟨3527754, by rfl⟩ : syracuseStep 9407345 = 7055509) B7055509
theorem B100345013 : Blo 2033435 100345013 := bstep (se 5 (by rfl) ⟨4703672, by rfl⟩ : syracuseStep 100345013 = 9407345) B9407345
theorem B66896675 : Blo 2033435 66896675 := bstep (se 1 (by rfl) ⟨50172506, by rfl⟩ : syracuseStep 66896675 = 100345013) B100345013
theorem B44597783 : Blo 2033435 44597783 := bstep (se 1 (by rfl) ⟨33448337, by rfl⟩ : syracuseStep 44597783 = 66896675) B66896675
theorem B29731855 : Blo 2033435 29731855 := bstep (se 1 (by rfl) ⟨22298891, by rfl⟩ : syracuseStep 29731855 = 44597783) B44597783
theorem B39642473 : Blo 2033435 39642473 := bstep (se 2 (by rfl) ⟨14865927, by rfl⟩ : syracuseStep 39642473 = 29731855) B29731855
theorem B105713261 : Blo 2033435 105713261 := bstep (se 3 (by rfl) ⟨19821236, by rfl⟩ : syracuseStep 105713261 = 39642473) B39642473
theorem B70475507 : Blo 2033435 70475507 := bstep (se 1 (by rfl) ⟨52856630, by rfl⟩ : syracuseStep 70475507 = 105713261) B105713261
theorem B46983671 : Blo 2033435 46983671 := bstep (se 1 (by rfl) ⟨35237753, by rfl⟩ : syracuseStep 46983671 = 70475507) B70475507
theorem B31322447 : Blo 2033435 31322447 := bstep (se 1 (by rfl) ⟨23491835, by rfl⟩ : syracuseStep 31322447 = 46983671) B46983671
theorem B20881631 : Blo 2033435 20881631 := bstep (se 1 (by rfl) ⟨15661223, by rfl⟩ : syracuseStep 20881631 = 31322447) B31322447
theorem B13921087 : Blo 2033435 13921087 := bstep (se 1 (by rfl) ⟨10440815, by rfl⟩ : syracuseStep 13921087 = 20881631) B20881631
theorem B18561449 : Blo 2033435 18561449 := bstep (se 2 (by rfl) ⟨6960543, by rfl⟩ : syracuseStep 18561449 = 13921087) B13921087
theorem B12374299 : Blo 2033435 12374299 := bstep (se 1 (by rfl) ⟨9280724, by rfl⟩ : syracuseStep 12374299 = 18561449) B18561449
theorem B16499065 : Blo 2033435 16499065 := bstep (se 2 (by rfl) ⟨6187149, by rfl⟩ : syracuseStep 16499065 = 12374299) B12374299
theorem B21998753 : Blo 2033435 21998753 := bstep (se 2 (by rfl) ⟨8249532, by rfl⟩ : syracuseStep 21998753 = 16499065) B16499065
theorem B14665835 : Blo 2033435 14665835 := bstep (se 1 (by rfl) ⟨10999376, by rfl⟩ : syracuseStep 14665835 = 21998753) B21998753
theorem B9777223 : Blo 2033435 9777223 := bstep (se 1 (by rfl) ⟨7332917, by rfl⟩ : syracuseStep 9777223 = 14665835) B14665835
theorem B13036297 : Blo 2033435 13036297 := bstep (se 2 (by rfl) ⟨4888611, by rfl⟩ : syracuseStep 13036297 = 9777223) B9777223
theorem B17381729 : Blo 2033435 17381729 := bstep (se 2 (by rfl) ⟨6518148, by rfl⟩ : syracuseStep 17381729 = 13036297) B13036297
theorem B11587819 : Blo 2033435 11587819 := bstep (se 1 (by rfl) ⟨8690864, by rfl⟩ : syracuseStep 11587819 = 17381729) B17381729
theorem B15450425 : Blo 2033435 15450425 := bstep (se 2 (by rfl) ⟨5793909, by rfl⟩ : syracuseStep 15450425 = 11587819) B11587819
theorem B10300283 : Blo 2033435 10300283 := bstep (se 1 (by rfl) ⟨7725212, by rfl⟩ : syracuseStep 10300283 = 15450425) B15450425
theorem B6866855 : Blo 2033435 6866855 := bstep (se 1 (by rfl) ⟨5150141, by rfl⟩ : syracuseStep 6866855 = 10300283) B10300283
theorem B4577903 : Blo 2033435 4577903 := bstep (se 1 (by rfl) ⟨3433427, by rfl⟩ : syracuseStep 4577903 = 6866855) B6866855
theorem B3051935 : Blo 2033435 3051935 := bstep (se 1 (by rfl) ⟨2288951, by rfl⟩ : syracuseStep 3051935 = 4577903) B4577903
theorem B2034623 : Blo 2033435 2034623 := bstep (se 1 (by rfl) ⟨1525967, by rfl⟩ : syracuseStep 2034623 = 3051935) B3051935
theorem B3051941 : Blo 2033435 3051941 := bbase (se 4 (by rfl) ⟨286119, by rfl⟩ : syracuseStep 3051941 = 572239) (by norm_num)
theorem B2034627 : Blo 2033435 2034627 := bstep (se 1 (by rfl) ⟨1525970, by rfl⟩ : syracuseStep 2034627 = 3051941) B3051941
theorem B2575081 : Blo 2033435 2575081 := bbase (se 2 (by rfl) ⟨965655, by rfl⟩ : syracuseStep 2575081 = 1931311) (by norm_num)
theorem B3433441 : Blo 2033435 3433441 := bstep (se 2 (by rfl) ⟨1287540, by rfl⟩ : syracuseStep 3433441 = 2575081) B2575081
theorem B4577921 : Blo 2033435 4577921 := bstep (se 2 (by rfl) ⟨1716720, by rfl⟩ : syracuseStep 4577921 = 3433441) B3433441
theorem B3051947 : Blo 2033435 3051947 := bstep (se 1 (by rfl) ⟨2288960, by rfl⟩ : syracuseStep 3051947 = 4577921) B4577921
theorem B2034631 : Blo 2033435 2034631 := bstep (se 1 (by rfl) ⟨1525973, by rfl⟩ : syracuseStep 2034631 = 3051947) B3051947
theorem B2288965 : Blo 2033435 2288965 := bbase (se 4 (by rfl) ⟨214590, by rfl⟩ : syracuseStep 2288965 = 429181) (by norm_num)
theorem B3051953 : Blo 2033435 3051953 := bstep (se 2 (by rfl) ⟨1144482, by rfl⟩ : syracuseStep 3051953 = 2288965) B2288965
theorem B2034635 : Blo 2033435 2034635 := bstep (se 1 (by rfl) ⟨1525976, by rfl⟩ : syracuseStep 2034635 = 3051953) B3051953
theorem B3862637 : Blo 2033435 3862637 := bbase (se 3 (by rfl) ⟨724244, by rfl⟩ : syracuseStep 3862637 = 1448489) (by norm_num)
theorem B2575091 : Blo 2033435 2575091 := bstep (se 1 (by rfl) ⟨1931318, by rfl⟩ : syracuseStep 2575091 = 3862637) B3862637
theorem B6866909 : Blo 2033435 6866909 := bstep (se 3 (by rfl) ⟨1287545, by rfl⟩ : syracuseStep 6866909 = 2575091) B2575091
theorem B4577939 : Blo 2033435 4577939 := bstep (se 1 (by rfl) ⟨3433454, by rfl⟩ : syracuseStep 4577939 = 6866909) B6866909
theorem B3051959 : Blo 2033435 3051959 := bstep (se 1 (by rfl) ⟨2288969, by rfl⟩ : syracuseStep 3051959 = 4577939) B4577939
theorem B2034639 : Blo 2033435 2034639 := bstep (se 1 (by rfl) ⟨1525979, by rfl⟩ : syracuseStep 2034639 = 3051959) B3051959
theorem B3051965 : Blo 2033435 3051965 := bbase (se 3 (by rfl) ⟨572243, by rfl⟩ : syracuseStep 3051965 = 1144487) (by norm_num)
theorem B2034643 : Blo 2033435 2034643 := bstep (se 1 (by rfl) ⟨1525982, by rfl⟩ : syracuseStep 2034643 = 3051965) B3051965
theorem B4577957 : Blo 2033435 4577957 := bbase (se 4 (by rfl) ⟨429183, by rfl⟩ : syracuseStep 4577957 = 858367) (by norm_num)
theorem B3051971 : Blo 2033435 3051971 := bstep (se 1 (by rfl) ⟨2288978, by rfl⟩ : syracuseStep 3051971 = 4577957) B4577957
theorem B2034647 : Blo 2033435 2034647 := bstep (se 1 (by rfl) ⟨1525985, by rfl⟩ : syracuseStep 2034647 = 3051971) B3051971
theorem B5150213 : Blo 2033435 5150213 := bbase (se 4 (by rfl) ⟨482832, by rfl⟩ : syracuseStep 5150213 = 965665) (by norm_num)
theorem B3433475 : Blo 2033435 3433475 := bstep (se 1 (by rfl) ⟨2575106, by rfl⟩ : syracuseStep 3433475 = 5150213) B5150213
theorem B2288983 : Blo 2033435 2288983 := bstep (se 1 (by rfl) ⟨1716737, by rfl⟩ : syracuseStep 2288983 = 3433475) B3433475
theorem B3051977 : Blo 2033435 3051977 := bstep (se 2 (by rfl) ⟨1144491, by rfl⟩ : syracuseStep 3051977 = 2288983) B2288983
theorem B2034651 : Blo 2033435 2034651 := bstep (se 1 (by rfl) ⟨1525988, by rfl⟩ : syracuseStep 2034651 = 3051977) B3051977
theorem B4345501 : Blo 2033435 4345501 := bbase (se 3 (by rfl) ⟨814781, by rfl⟩ : syracuseStep 4345501 = 1629563) (by norm_num)
theorem B5794001 : Blo 2033435 5794001 := bstep (se 2 (by rfl) ⟨2172750, by rfl⟩ : syracuseStep 5794001 = 4345501) B4345501
theorem B3862667 : Blo 2033435 3862667 := bstep (se 1 (by rfl) ⟨2897000, by rfl⟩ : syracuseStep 3862667 = 5794001) B5794001
theorem B10300445 : Blo 2033435 10300445 := bstep (se 3 (by rfl) ⟨1931333, by rfl⟩ : syracuseStep 10300445 = 3862667) B3862667
theorem B6866963 : Blo 2033435 6866963 := bstep (se 1 (by rfl) ⟨5150222, by rfl⟩ : syracuseStep 6866963 = 10300445) B10300445
theorem B4577975 : Blo 2033435 4577975 := bstep (se 1 (by rfl) ⟨3433481, by rfl⟩ : syracuseStep 4577975 = 6866963) B6866963
theorem B3051983 : Blo 2033435 3051983 := bstep (se 1 (by rfl) ⟨2288987, by rfl⟩ : syracuseStep 3051983 = 4577975) B4577975
theorem B2034655 : Blo 2033435 2034655 := bstep (se 1 (by rfl) ⟨1525991, by rfl⟩ : syracuseStep 2034655 = 3051983) B3051983
theorem B3051989 : Blo 2033435 3051989 := bbase (se 7 (by rfl) ⟨35765, by rfl⟩ : syracuseStep 3051989 = 71531) (by norm_num)
theorem B2034659 : Blo 2033435 2034659 := bstep (se 1 (by rfl) ⟨1525994, by rfl⟩ : syracuseStep 2034659 = 3051989) B3051989
theorem B7725365 : Blo 2033435 7725365 := bbase (se 5 (by rfl) ⟨362126, by rfl⟩ : syracuseStep 7725365 = 724253) (by norm_num)
theorem B5150243 : Blo 2033435 5150243 := bstep (se 1 (by rfl) ⟨3862682, by rfl⟩ : syracuseStep 5150243 = 7725365) B7725365
theorem B3433495 : Blo 2033435 3433495 := bstep (se 1 (by rfl) ⟨2575121, by rfl⟩ : syracuseStep 3433495 = 5150243) B5150243
theorem B4577993 : Blo 2033435 4577993 := bstep (se 2 (by rfl) ⟨1716747, by rfl⟩ : syracuseStep 4577993 = 3433495) B3433495
theorem B3051995 : Blo 2033435 3051995 := bstep (se 1 (by rfl) ⟨2288996, by rfl⟩ : syracuseStep 3051995 = 4577993) B4577993
theorem B2034663 : Blo 2033435 2034663 := bstep (se 1 (by rfl) ⟨1525997, by rfl⟩ : syracuseStep 2034663 = 3051995) B3051995
theorem B2289001 : Blo 2033435 2289001 := bbase (se 2 (by rfl) ⟨858375, by rfl⟩ : syracuseStep 2289001 = 1716751) (by norm_num)
theorem B3052001 : Blo 2033435 3052001 := bstep (se 2 (by rfl) ⟨1144500, by rfl⟩ : syracuseStep 3052001 = 2289001) B2289001
theorem B2034667 : Blo 2033435 2034667 := bstep (se 1 (by rfl) ⟨1526000, by rfl⟩ : syracuseStep 2034667 = 3052001) B3052001
theorem B2232461 : Blo 2033435 2232461 := bbase (se 3 (by rfl) ⟨418586, by rfl⟩ : syracuseStep 2232461 = 837173) (by norm_num)
theorem B5953229 : Blo 2033435 5953229 := bstep (se 3 (by rfl) ⟨1116230, by rfl⟩ : syracuseStep 5953229 = 2232461) B2232461
theorem B3968819 : Blo 2033435 3968819 := bstep (se 1 (by rfl) ⟨2976614, by rfl⟩ : syracuseStep 3968819 = 5953229) B5953229
theorem B2645879 : Blo 2033435 2645879 := bstep (se 1 (by rfl) ⟨1984409, by rfl⟩ : syracuseStep 2645879 = 3968819) B3968819
theorem B7055677 : Blo 2033435 7055677 := bstep (se 3 (by rfl) ⟨1322939, by rfl⟩ : syracuseStep 7055677 = 2645879) B2645879
theorem B9407569 : Blo 2033435 9407569 := bstep (se 2 (by rfl) ⟨3527838, by rfl⟩ : syracuseStep 9407569 = 7055677) B7055677
theorem B12543425 : Blo 2033435 12543425 := bstep (se 2 (by rfl) ⟨4703784, by rfl⟩ : syracuseStep 12543425 = 9407569) B9407569
theorem B8362283 : Blo 2033435 8362283 := bstep (se 1 (by rfl) ⟨6271712, by rfl⟩ : syracuseStep 8362283 = 12543425) B12543425
theorem B89197685 : Blo 2033435 89197685 := bstep (se 5 (by rfl) ⟨4181141, by rfl⟩ : syracuseStep 89197685 = 8362283) B8362283
theorem B59465123 : Blo 2033435 59465123 := bstep (se 1 (by rfl) ⟨44598842, by rfl⟩ : syracuseStep 59465123 = 89197685) B89197685
theorem B39643415 : Blo 2033435 39643415 := bstep (se 1 (by rfl) ⟨29732561, by rfl⟩ : syracuseStep 39643415 = 59465123) B59465123
theorem B26428943 : Blo 2033435 26428943 := bstep (se 1 (by rfl) ⟨19821707, by rfl⟩ : syracuseStep 26428943 = 39643415) B39643415
theorem B17619295 : Blo 2033435 17619295 := bstep (se 1 (by rfl) ⟨13214471, by rfl⟩ : syracuseStep 17619295 = 26428943) B26428943
theorem B23492393 : Blo 2033435 23492393 := bstep (se 2 (by rfl) ⟨8809647, by rfl⟩ : syracuseStep 23492393 = 17619295) B17619295
theorem B15661595 : Blo 2033435 15661595 := bstep (se 1 (by rfl) ⟨11746196, by rfl⟩ : syracuseStep 15661595 = 23492393) B23492393
theorem B10441063 : Blo 2033435 10441063 := bstep (se 1 (by rfl) ⟨7830797, by rfl⟩ : syracuseStep 10441063 = 15661595) B15661595
theorem B13921417 : Blo 2033435 13921417 := bstep (se 2 (by rfl) ⟨5220531, by rfl⟩ : syracuseStep 13921417 = 10441063) B10441063
theorem B18561889 : Blo 2033435 18561889 := bstep (se 2 (by rfl) ⟨6960708, by rfl⟩ : syracuseStep 18561889 = 13921417) B13921417
theorem B24749185 : Blo 2033435 24749185 := bstep (se 2 (by rfl) ⟨9280944, by rfl⟩ : syracuseStep 24749185 = 18561889) B18561889
theorem B32998913 : Blo 2033435 32998913 := bstep (se 2 (by rfl) ⟨12374592, by rfl⟩ : syracuseStep 32998913 = 24749185) B24749185
theorem B21999275 : Blo 2033435 21999275 := bstep (se 1 (by rfl) ⟨16499456, by rfl⟩ : syracuseStep 21999275 = 32998913) B32998913
theorem B14666183 : Blo 2033435 14666183 := bstep (se 1 (by rfl) ⟨10999637, by rfl⟩ : syracuseStep 14666183 = 21999275) B21999275
theorem B9777455 : Blo 2033435 9777455 := bstep (se 1 (by rfl) ⟨7333091, by rfl⟩ : syracuseStep 9777455 = 14666183) B14666183
theorem B6518303 : Blo 2033435 6518303 := bstep (se 1 (by rfl) ⟨4888727, by rfl⟩ : syracuseStep 6518303 = 9777455) B9777455
theorem B4345535 : Blo 2033435 4345535 := bstep (se 1 (by rfl) ⟨3259151, by rfl⟩ : syracuseStep 4345535 = 6518303) B6518303
theorem B11588093 : Blo 2033435 11588093 := bstep (se 3 (by rfl) ⟨2172767, by rfl⟩ : syracuseStep 11588093 = 4345535) B4345535
theorem B7725395 : Blo 2033435 7725395 := bstep (se 1 (by rfl) ⟨5794046, by rfl⟩ : syracuseStep 7725395 = 11588093) B11588093
theorem B5150263 : Blo 2033435 5150263 := bstep (se 1 (by rfl) ⟨3862697, by rfl⟩ : syracuseStep 5150263 = 7725395) B7725395
theorem B6867017 : Blo 2033435 6867017 := bstep (se 2 (by rfl) ⟨2575131, by rfl⟩ : syracuseStep 6867017 = 5150263) B5150263
theorem B4578011 : Blo 2033435 4578011 := bstep (se 1 (by rfl) ⟨3433508, by rfl⟩ : syracuseStep 4578011 = 6867017) B6867017
theorem B3052007 : Blo 2033435 3052007 := bstep (se 1 (by rfl) ⟨2289005, by rfl⟩ : syracuseStep 3052007 = 4578011) B4578011
theorem B2034671 : Blo 2033435 2034671 := bstep (se 1 (by rfl) ⟨1526003, by rfl⟩ : syracuseStep 2034671 = 3052007) B3052007
theorem B3052013 : Blo 2033435 3052013 := bbase (se 3 (by rfl) ⟨572252, by rfl⟩ : syracuseStep 3052013 = 1144505) (by norm_num)
theorem B2034675 : Blo 2033435 2034675 := bstep (se 1 (by rfl) ⟨1526006, by rfl⟩ : syracuseStep 2034675 = 3052013) B3052013
theorem B4578029 : Blo 2033435 4578029 := bbase (se 3 (by rfl) ⟨858380, by rfl⟩ : syracuseStep 4578029 = 1716761) (by norm_num)
theorem B3052019 : Blo 2033435 3052019 := bstep (se 1 (by rfl) ⟨2289014, by rfl⟩ : syracuseStep 3052019 = 4578029) B4578029
theorem B2034679 : Blo 2033435 2034679 := bstep (se 1 (by rfl) ⟨1526009, by rfl⟩ : syracuseStep 2034679 = 3052019) B3052019
theorem B2172781 : Blo 2033435 2172781 := bbase (se 3 (by rfl) ⟨407396, by rfl⟩ : syracuseStep 2172781 = 814793) (by norm_num)
theorem B2897041 : Blo 2033435 2897041 := bstep (se 2 (by rfl) ⟨1086390, by rfl⟩ : syracuseStep 2897041 = 2172781) B2172781
theorem B3862721 : Blo 2033435 3862721 := bstep (se 2 (by rfl) ⟨1448520, by rfl⟩ : syracuseStep 3862721 = 2897041) B2897041
theorem B2575147 : Blo 2033435 2575147 := bstep (se 1 (by rfl) ⟨1931360, by rfl⟩ : syracuseStep 2575147 = 3862721) B3862721
theorem B3433529 : Blo 2033435 3433529 := bstep (se 2 (by rfl) ⟨1287573, by rfl⟩ : syracuseStep 3433529 = 2575147) B2575147
theorem B2289019 : Blo 2033435 2289019 := bstep (se 1 (by rfl) ⟨1716764, by rfl⟩ : syracuseStep 2289019 = 3433529) B3433529
theorem B3052025 : Blo 2033435 3052025 := bstep (se 2 (by rfl) ⟨1144509, by rfl⟩ : syracuseStep 3052025 = 2289019) B2289019
theorem B2034683 : Blo 2033435 2034683 := bstep (se 1 (by rfl) ⟨1526012, by rfl⟩ : syracuseStep 2034683 = 3052025) B3052025
theorem B16724693 : Blo 2033435 16724693 := bbase (se 7 (by rfl) ⟨195992, by rfl⟩ : syracuseStep 16724693 = 391985) (by norm_num)
theorem B11149795 : Blo 2033435 11149795 := bstep (se 1 (by rfl) ⟨8362346, by rfl⟩ : syracuseStep 11149795 = 16724693) B16724693
theorem B59465573 : Blo 2033435 59465573 := bstep (se 4 (by rfl) ⟨5574897, by rfl⟩ : syracuseStep 59465573 = 11149795) B11149795
theorem B39643715 : Blo 2033435 39643715 := bstep (se 1 (by rfl) ⟨29732786, by rfl⟩ : syracuseStep 39643715 = 59465573) B59465573
theorem B105716573 : Blo 2033435 105716573 := bstep (se 3 (by rfl) ⟨19821857, by rfl⟩ : syracuseStep 105716573 = 39643715) B39643715
theorem B70477715 : Blo 2033435 70477715 := bstep (se 1 (by rfl) ⟨52858286, by rfl⟩ : syracuseStep 70477715 = 105716573) B105716573
theorem B46985143 : Blo 2033435 46985143 := bstep (se 1 (by rfl) ⟨35238857, by rfl⟩ : syracuseStep 46985143 = 70477715) B70477715
theorem B62646857 : Blo 2033435 62646857 := bstep (se 2 (by rfl) ⟨23492571, by rfl⟩ : syracuseStep 62646857 = 46985143) B46985143
theorem B41764571 : Blo 2033435 41764571 := bstep (se 1 (by rfl) ⟨31323428, by rfl⟩ : syracuseStep 41764571 = 62646857) B62646857
theorem B27843047 : Blo 2033435 27843047 := bstep (se 1 (by rfl) ⟨20882285, by rfl⟩ : syracuseStep 27843047 = 41764571) B41764571
theorem B18562031 : Blo 2033435 18562031 := bstep (se 1 (by rfl) ⟨13921523, by rfl⟩ : syracuseStep 18562031 = 27843047) B27843047
theorem B12374687 : Blo 2033435 12374687 := bstep (se 1 (by rfl) ⟨9281015, by rfl⟩ : syracuseStep 12374687 = 18562031) B18562031
theorem B32999165 : Blo 2033435 32999165 := bstep (se 3 (by rfl) ⟨6187343, by rfl⟩ : syracuseStep 32999165 = 12374687) B12374687
theorem B21999443 : Blo 2033435 21999443 := bstep (se 1 (by rfl) ⟨16499582, by rfl⟩ : syracuseStep 21999443 = 32999165) B32999165
theorem B58665181 : Blo 2033435 58665181 := bstep (se 3 (by rfl) ⟨10999721, by rfl⟩ : syracuseStep 58665181 = 21999443) B21999443
theorem B78220241 : Blo 2033435 78220241 := bstep (se 2 (by rfl) ⟨29332590, by rfl⟩ : syracuseStep 78220241 = 58665181) B58665181
theorem B52146827 : Blo 2033435 52146827 := bstep (se 1 (by rfl) ⟨39110120, by rfl⟩ : syracuseStep 52146827 = 78220241) B78220241
theorem B34764551 : Blo 2033435 34764551 := bstep (se 1 (by rfl) ⟨26073413, by rfl⟩ : syracuseStep 34764551 = 52146827) B52146827
theorem B23176367 : Blo 2033435 23176367 := bstep (se 1 (by rfl) ⟨17382275, by rfl⟩ : syracuseStep 23176367 = 34764551) B34764551
theorem B15450911 : Blo 2033435 15450911 := bstep (se 1 (by rfl) ⟨11588183, by rfl⟩ : syracuseStep 15450911 = 23176367) B23176367
theorem B10300607 : Blo 2033435 10300607 := bstep (se 1 (by rfl) ⟨7725455, by rfl⟩ : syracuseStep 10300607 = 15450911) B15450911
theorem B6867071 : Blo 2033435 6867071 := bstep (se 1 (by rfl) ⟨5150303, by rfl⟩ : syracuseStep 6867071 = 10300607) B10300607
theorem B4578047 : Blo 2033435 4578047 := bstep (se 1 (by rfl) ⟨3433535, by rfl⟩ : syracuseStep 4578047 = 6867071) B6867071
theorem B3052031 : Blo 2033435 3052031 := bstep (se 1 (by rfl) ⟨2289023, by rfl⟩ : syracuseStep 3052031 = 4578047) B4578047
theorem B2034687 : Blo 2033435 2034687 := bstep (se 1 (by rfl) ⟨1526015, by rfl⟩ : syracuseStep 2034687 = 3052031) B3052031
theorem B3052037 : Blo 2033435 3052037 := bbase (se 4 (by rfl) ⟨286128, by rfl⟩ : syracuseStep 3052037 = 572257) (by norm_num)
theorem B2034691 : Blo 2033435 2034691 := bstep (se 1 (by rfl) ⟨1526018, by rfl⟩ : syracuseStep 2034691 = 3052037) B3052037
theorem B3433549 : Blo 2033435 3433549 := bbase (se 3 (by rfl) ⟨643790, by rfl⟩ : syracuseStep 3433549 = 1287581) (by norm_num)
theorem B4578065 : Blo 2033435 4578065 := bstep (se 2 (by rfl) ⟨1716774, by rfl⟩ : syracuseStep 4578065 = 3433549) B3433549
theorem B3052043 : Blo 2033435 3052043 := bstep (se 1 (by rfl) ⟨2289032, by rfl⟩ : syracuseStep 3052043 = 4578065) B4578065
theorem B2034695 : Blo 2033435 2034695 := bstep (se 1 (by rfl) ⟨1526021, by rfl⟩ : syracuseStep 2034695 = 3052043) B3052043
theorem B2289037 : Blo 2033435 2289037 := bbase (se 3 (by rfl) ⟨429194, by rfl⟩ : syracuseStep 2289037 = 858389) (by norm_num)
theorem B3052049 : Blo 2033435 3052049 := bstep (se 2 (by rfl) ⟨1144518, by rfl⟩ : syracuseStep 3052049 = 2289037) B2289037
theorem B2034699 : Blo 2033435 2034699 := bstep (se 1 (by rfl) ⟨1526024, by rfl⟩ : syracuseStep 2034699 = 3052049) B3052049
theorem B6867125 : Blo 2033435 6867125 := bbase (se 5 (by rfl) ⟨321896, by rfl⟩ : syracuseStep 6867125 = 643793) (by norm_num)
theorem B4578083 : Blo 2033435 4578083 := bstep (se 1 (by rfl) ⟨3433562, by rfl⟩ : syracuseStep 4578083 = 6867125) B6867125
theorem B3052055 : Blo 2033435 3052055 := bstep (se 1 (by rfl) ⟨2289041, by rfl⟩ : syracuseStep 3052055 = 4578083) B4578083
theorem B2034703 : Blo 2033435 2034703 := bstep (se 1 (by rfl) ⟨1526027, by rfl⟩ : syracuseStep 2034703 = 3052055) B3052055
theorem B3052061 : Blo 2033435 3052061 := bbase (se 3 (by rfl) ⟨572261, by rfl⟩ : syracuseStep 3052061 = 1144523) (by norm_num)
theorem B2034707 : Blo 2033435 2034707 := bstep (se 1 (by rfl) ⟨1526030, by rfl⟩ : syracuseStep 2034707 = 3052061) B3052061
theorem B4578101 : Blo 2033435 4578101 := bbase (se 5 (by rfl) ⟨214598, by rfl⟩ : syracuseStep 4578101 = 429197) (by norm_num)
theorem B3052067 : Blo 2033435 3052067 := bstep (se 1 (by rfl) ⟨2289050, by rfl⟩ : syracuseStep 3052067 = 4578101) B4578101
theorem B2034711 : Blo 2033435 2034711 := bstep (se 1 (by rfl) ⟨1526033, by rfl⟩ : syracuseStep 2034711 = 3052067) B3052067
theorem B2062477 : Blo 2033435 2062477 := bbase (se 3 (by rfl) ⟨386714, by rfl⟩ : syracuseStep 2062477 = 773429) (by norm_num)
theorem B2749969 : Blo 2033435 2749969 := bstep (se 2 (by rfl) ⟨1031238, by rfl⟩ : syracuseStep 2749969 = 2062477) B2062477
theorem B14666501 : Blo 2033435 14666501 := bstep (se 4 (by rfl) ⟨1374984, by rfl⟩ : syracuseStep 14666501 = 2749969) B2749969
theorem B9777667 : Blo 2033435 9777667 := bstep (se 1 (by rfl) ⟨7333250, by rfl⟩ : syracuseStep 9777667 = 14666501) B14666501
theorem B13036889 : Blo 2033435 13036889 := bstep (se 2 (by rfl) ⟨4888833, by rfl⟩ : syracuseStep 13036889 = 9777667) B9777667
theorem B8691259 : Blo 2033435 8691259 := bstep (se 1 (by rfl) ⟨6518444, by rfl⟩ : syracuseStep 8691259 = 13036889) B13036889
theorem B11588345 : Blo 2033435 11588345 := bstep (se 2 (by rfl) ⟨4345629, by rfl⟩ : syracuseStep 11588345 = 8691259) B8691259
theorem B7725563 : Blo 2033435 7725563 := bstep (se 1 (by rfl) ⟨5794172, by rfl⟩ : syracuseStep 7725563 = 11588345) B11588345
theorem B5150375 : Blo 2033435 5150375 := bstep (se 1 (by rfl) ⟨3862781, by rfl⟩ : syracuseStep 5150375 = 7725563) B7725563
theorem B3433583 : Blo 2033435 3433583 := bstep (se 1 (by rfl) ⟨2575187, by rfl⟩ : syracuseStep 3433583 = 5150375) B5150375
theorem B2289055 : Blo 2033435 2289055 := bstep (se 1 (by rfl) ⟨1716791, by rfl⟩ : syracuseStep 2289055 = 3433583) B3433583
theorem B3052073 : Blo 2033435 3052073 := bstep (se 2 (by rfl) ⟨1144527, by rfl⟩ : syracuseStep 3052073 = 2289055) B2289055
theorem B2034715 : Blo 2033435 2034715 := bstep (se 1 (by rfl) ⟨1526036, by rfl⟩ : syracuseStep 2034715 = 3052073) B3052073
theorem B9777685 : Blo 2033435 9777685 := bbase (se 6 (by rfl) ⟨229164, by rfl⟩ : syracuseStep 9777685 = 458329) (by norm_num)
theorem B13036913 : Blo 2033435 13036913 := bstep (se 2 (by rfl) ⟨4888842, by rfl⟩ : syracuseStep 13036913 = 9777685) B9777685
theorem B8691275 : Blo 2033435 8691275 := bstep (se 1 (by rfl) ⟨6518456, by rfl⟩ : syracuseStep 8691275 = 13036913) B13036913
theorem B5794183 : Blo 2033435 5794183 := bstep (se 1 (by rfl) ⟨4345637, by rfl⟩ : syracuseStep 5794183 = 8691275) B8691275
theorem B7725577 : Blo 2033435 7725577 := bstep (se 2 (by rfl) ⟨2897091, by rfl⟩ : syracuseStep 7725577 = 5794183) B5794183
theorem B10300769 : Blo 2033435 10300769 := bstep (se 2 (by rfl) ⟨3862788, by rfl⟩ : syracuseStep 10300769 = 7725577) B7725577
theorem B6867179 : Blo 2033435 6867179 := bstep (se 1 (by rfl) ⟨5150384, by rfl⟩ : syracuseStep 6867179 = 10300769) B10300769
theorem B4578119 : Blo 2033435 4578119 := bstep (se 1 (by rfl) ⟨3433589, by rfl⟩ : syracuseStep 4578119 = 6867179) B6867179
theorem B3052079 : Blo 2033435 3052079 := bstep (se 1 (by rfl) ⟨2289059, by rfl⟩ : syracuseStep 3052079 = 4578119) B4578119
theorem B2034719 : Blo 2033435 2034719 := bstep (se 1 (by rfl) ⟨1526039, by rfl⟩ : syracuseStep 2034719 = 3052079) B3052079
theorem B3052085 : Blo 2033435 3052085 := bbase (se 5 (by rfl) ⟨143066, by rfl⟩ : syracuseStep 3052085 = 286133) (by norm_num)
theorem B2034723 : Blo 2033435 2034723 := bstep (se 1 (by rfl) ⟨1526042, by rfl⟩ : syracuseStep 2034723 = 3052085) B3052085
theorem B5150405 : Blo 2033435 5150405 := bbase (se 4 (by rfl) ⟨482850, by rfl⟩ : syracuseStep 5150405 = 965701) (by norm_num)
theorem B3433603 : Blo 2033435 3433603 := bstep (se 1 (by rfl) ⟨2575202, by rfl⟩ : syracuseStep 3433603 = 5150405) B5150405
theorem B4578137 : Blo 2033435 4578137 := bstep (se 2 (by rfl) ⟨1716801, by rfl⟩ : syracuseStep 4578137 = 3433603) B3433603
theorem B3052091 : Blo 2033435 3052091 := bstep (se 1 (by rfl) ⟨2289068, by rfl⟩ : syracuseStep 3052091 = 4578137) B4578137
theorem B2034727 : Blo 2033435 2034727 := bstep (se 1 (by rfl) ⟨1526045, by rfl⟩ : syracuseStep 2034727 = 3052091) B3052091
theorem B2289073 : Blo 2033435 2289073 := bbase (se 2 (by rfl) ⟨858402, by rfl⟩ : syracuseStep 2289073 = 1716805) (by norm_num)
theorem B3052097 : Blo 2033435 3052097 := bstep (se 2 (by rfl) ⟨1144536, by rfl⟩ : syracuseStep 3052097 = 2289073) B2289073
theorem B2034731 : Blo 2033435 2034731 := bstep (se 1 (by rfl) ⟨1526048, by rfl⟩ : syracuseStep 2034731 = 3052097) B3052097
theorem B5794229 : Blo 2033435 5794229 := bbase (se 5 (by rfl) ⟨271604, by rfl⟩ : syracuseStep 5794229 = 543209) (by norm_num)
theorem B3862819 : Blo 2033435 3862819 := bstep (se 1 (by rfl) ⟨2897114, by rfl⟩ : syracuseStep 3862819 = 5794229) B5794229
theorem B5150425 : Blo 2033435 5150425 := bstep (se 2 (by rfl) ⟨1931409, by rfl⟩ : syracuseStep 5150425 = 3862819) B3862819
theorem B6867233 : Blo 2033435 6867233 := bstep (se 2 (by rfl) ⟨2575212, by rfl⟩ : syracuseStep 6867233 = 5150425) B5150425
theorem B4578155 : Blo 2033435 4578155 := bstep (se 1 (by rfl) ⟨3433616, by rfl⟩ : syracuseStep 4578155 = 6867233) B6867233
theorem B3052103 : Blo 2033435 3052103 := bstep (se 1 (by rfl) ⟨2289077, by rfl⟩ : syracuseStep 3052103 = 4578155) B4578155
theorem B2034735 : Blo 2033435 2034735 := bstep (se 1 (by rfl) ⟨1526051, by rfl⟩ : syracuseStep 2034735 = 3052103) B3052103
theorem B3052109 : Blo 2033435 3052109 := bbase (se 3 (by rfl) ⟨572270, by rfl⟩ : syracuseStep 3052109 = 1144541) (by norm_num)
theorem B2034739 : Blo 2033435 2034739 := bstep (se 1 (by rfl) ⟨1526054, by rfl⟩ : syracuseStep 2034739 = 3052109) B3052109
theorem B4578173 : Blo 2033435 4578173 := bbase (se 3 (by rfl) ⟨858407, by rfl⟩ : syracuseStep 4578173 = 1716815) (by norm_num)
theorem B3052115 : Blo 2033435 3052115 := bstep (se 1 (by rfl) ⟨2289086, by rfl⟩ : syracuseStep 3052115 = 4578173) B4578173
theorem B2034743 : Blo 2033435 2034743 := bstep (se 1 (by rfl) ⟨1526057, by rfl⟩ : syracuseStep 2034743 = 3052115) B3052115
theorem B3433637 : Blo 2033435 3433637 := bbase (se 4 (by rfl) ⟨321903, by rfl⟩ : syracuseStep 3433637 = 643807) (by norm_num)
theorem B2289091 : Blo 2033435 2289091 := bstep (se 1 (by rfl) ⟨1716818, by rfl⟩ : syracuseStep 2289091 = 3433637) B3433637
theorem B3052121 : Blo 2033435 3052121 := bstep (se 2 (by rfl) ⟨1144545, by rfl⟩ : syracuseStep 3052121 = 2289091) B2289091
theorem B2034747 : Blo 2033435 2034747 := bstep (se 1 (by rfl) ⟨1526060, by rfl⟩ : syracuseStep 2034747 = 3052121) B3052121
theorem B2172853 : Blo 2033435 2172853 := bbase (se 5 (by rfl) ⟨101852, by rfl⟩ : syracuseStep 2172853 = 203705) (by norm_num)
theorem B2897137 : Blo 2033435 2897137 := bstep (se 2 (by rfl) ⟨1086426, by rfl⟩ : syracuseStep 2897137 = 2172853) B2172853
theorem B15451397 : Blo 2033435 15451397 := bstep (se 4 (by rfl) ⟨1448568, by rfl⟩ : syracuseStep 15451397 = 2897137) B2897137
theorem B10300931 : Blo 2033435 10300931 := bstep (se 1 (by rfl) ⟨7725698, by rfl⟩ : syracuseStep 10300931 = 15451397) B15451397
theorem B6867287 : Blo 2033435 6867287 := bstep (se 1 (by rfl) ⟨5150465, by rfl⟩ : syracuseStep 6867287 = 10300931) B10300931
theorem B4578191 : Blo 2033435 4578191 := bstep (se 1 (by rfl) ⟨3433643, by rfl⟩ : syracuseStep 4578191 = 6867287) B6867287
theorem B3052127 : Blo 2033435 3052127 := bstep (se 1 (by rfl) ⟨2289095, by rfl⟩ : syracuseStep 3052127 = 4578191) B4578191
theorem B2034751 : Blo 2033435 2034751 := bstep (se 1 (by rfl) ⟨1526063, by rfl⟩ : syracuseStep 2034751 = 3052127) B3052127
theorem B3052133 : Blo 2033435 3052133 := bbase (se 4 (by rfl) ⟨286137, by rfl⟩ : syracuseStep 3052133 = 572275) (by norm_num)
theorem B2034755 : Blo 2033435 2034755 := bstep (se 1 (by rfl) ⟨1526066, by rfl⟩ : syracuseStep 2034755 = 3052133) B3052133
theorem B2897149 : Blo 2033435 2897149 := bbase (se 3 (by rfl) ⟨543215, by rfl⟩ : syracuseStep 2897149 = 1086431) (by norm_num)
theorem B3862865 : Blo 2033435 3862865 := bstep (se 2 (by rfl) ⟨1448574, by rfl⟩ : syracuseStep 3862865 = 2897149) B2897149
theorem B2575243 : Blo 2033435 2575243 := bstep (se 1 (by rfl) ⟨1931432, by rfl⟩ : syracuseStep 2575243 = 3862865) B3862865
theorem B3433657 : Blo 2033435 3433657 := bstep (se 2 (by rfl) ⟨1287621, by rfl⟩ : syracuseStep 3433657 = 2575243) B2575243
theorem B4578209 : Blo 2033435 4578209 := bstep (se 2 (by rfl) ⟨1716828, by rfl⟩ : syracuseStep 4578209 = 3433657) B3433657
theorem B3052139 : Blo 2033435 3052139 := bstep (se 1 (by rfl) ⟨2289104, by rfl⟩ : syracuseStep 3052139 = 4578209) B4578209
theorem B2034759 : Blo 2033435 2034759 := bstep (se 1 (by rfl) ⟨1526069, by rfl⟩ : syracuseStep 2034759 = 3052139) B3052139
theorem B2289109 : Blo 2033435 2289109 := bbase (se 7 (by rfl) ⟨26825, by rfl⟩ : syracuseStep 2289109 = 53651) (by norm_num)
theorem B3052145 : Blo 2033435 3052145 := bstep (se 2 (by rfl) ⟨1144554, by rfl⟩ : syracuseStep 3052145 = 2289109) B2289109
theorem B2034763 : Blo 2033435 2034763 := bstep (se 1 (by rfl) ⟨1526072, by rfl⟩ : syracuseStep 2034763 = 3052145) B3052145
theorem B2575253 : Blo 2033435 2575253 := bbase (se 6 (by rfl) ⟨60357, by rfl⟩ : syracuseStep 2575253 = 120715) (by norm_num)
theorem B6867341 : Blo 2033435 6867341 := bstep (se 3 (by rfl) ⟨1287626, by rfl⟩ : syracuseStep 6867341 = 2575253) B2575253
theorem B4578227 : Blo 2033435 4578227 := bstep (se 1 (by rfl) ⟨3433670, by rfl⟩ : syracuseStep 4578227 = 6867341) B6867341
theorem B3052151 : Blo 2033435 3052151 := bstep (se 1 (by rfl) ⟨2289113, by rfl⟩ : syracuseStep 3052151 = 4578227) B4578227
theorem B2034767 : Blo 2033435 2034767 := bstep (se 1 (by rfl) ⟨1526075, by rfl⟩ : syracuseStep 2034767 = 3052151) B3052151
theorem B3052157 : Blo 2033435 3052157 := bbase (se 3 (by rfl) ⟨572279, by rfl⟩ : syracuseStep 3052157 = 1144559) (by norm_num)
theorem B2034771 : Blo 2033435 2034771 := bstep (se 1 (by rfl) ⟨1526078, by rfl⟩ : syracuseStep 2034771 = 3052157) B3052157
theorem B4578245 : Blo 2033435 4578245 := bbase (se 4 (by rfl) ⟨429210, by rfl⟩ : syracuseStep 4578245 = 858421) (by norm_num)
theorem B3052163 : Blo 2033435 3052163 := bstep (se 1 (by rfl) ⟨2289122, by rfl⟩ : syracuseStep 3052163 = 4578245) B4578245
theorem B2034775 : Blo 2033435 2034775 := bstep (se 1 (by rfl) ⟨1526081, by rfl⟩ : syracuseStep 2034775 = 3052163) B3052163
theorem B3259325 : Blo 2033435 3259325 := bbase (se 3 (by rfl) ⟨611123, by rfl⟩ : syracuseStep 3259325 = 1222247) (by norm_num)
theorem B8691533 : Blo 2033435 8691533 := bstep (se 3 (by rfl) ⟨1629662, by rfl⟩ : syracuseStep 8691533 = 3259325) B3259325
theorem B5794355 : Blo 2033435 5794355 := bstep (se 1 (by rfl) ⟨4345766, by rfl⟩ : syracuseStep 5794355 = 8691533) B8691533
theorem B3862903 : Blo 2033435 3862903 := bstep (se 1 (by rfl) ⟨2897177, by rfl⟩ : syracuseStep 3862903 = 5794355) B5794355
theorem B5150537 : Blo 2033435 5150537 := bstep (se 2 (by rfl) ⟨1931451, by rfl⟩ : syracuseStep 5150537 = 3862903) B3862903
theorem B3433691 : Blo 2033435 3433691 := bstep (se 1 (by rfl) ⟨2575268, by rfl⟩ : syracuseStep 3433691 = 5150537) B5150537
theorem B2289127 : Blo 2033435 2289127 := bstep (se 1 (by rfl) ⟨1716845, by rfl⟩ : syracuseStep 2289127 = 3433691) B3433691
theorem B3052169 : Blo 2033435 3052169 := bstep (se 2 (by rfl) ⟨1144563, by rfl⟩ : syracuseStep 3052169 = 2289127) B2289127
theorem B2034779 : Blo 2033435 2034779 := bstep (se 1 (by rfl) ⟨1526084, by rfl⟩ : syracuseStep 2034779 = 3052169) B3052169
theorem B10301093 : Blo 2033435 10301093 := bbase (se 4 (by rfl) ⟨965727, by rfl⟩ : syracuseStep 10301093 = 1931455) (by norm_num)
theorem B6867395 : Blo 2033435 6867395 := bstep (se 1 (by rfl) ⟨5150546, by rfl⟩ : syracuseStep 6867395 = 10301093) B10301093
theorem B4578263 : Blo 2033435 4578263 := bstep (se 1 (by rfl) ⟨3433697, by rfl⟩ : syracuseStep 4578263 = 6867395) B6867395
theorem B3052175 : Blo 2033435 3052175 := bstep (se 1 (by rfl) ⟨2289131, by rfl⟩ : syracuseStep 3052175 = 4578263) B4578263
theorem B2034783 : Blo 2033435 2034783 := bstep (se 1 (by rfl) ⟨1526087, by rfl⟩ : syracuseStep 2034783 = 3052175) B3052175
theorem B3052181 : Blo 2033435 3052181 := bbase (se 6 (by rfl) ⟨71535, by rfl⟩ : syracuseStep 3052181 = 143071) (by norm_num)
theorem B2034787 : Blo 2033435 2034787 := bstep (se 1 (by rfl) ⟨1526090, by rfl⟩ : syracuseStep 2034787 = 3052181) B3052181
theorem B3767501 : Blo 2033435 3767501 := bbase (se 3 (by rfl) ⟨706406, by rfl⟩ : syracuseStep 3767501 = 1412813) (by norm_num)
theorem B2511667 : Blo 2033435 2511667 := bstep (se 1 (by rfl) ⟨1883750, by rfl⟩ : syracuseStep 2511667 = 3767501) B3767501
theorem B13395557 : Blo 2033435 13395557 := bstep (se 4 (by rfl) ⟨1255833, by rfl⟩ : syracuseStep 13395557 = 2511667) B2511667
theorem B8930371 : Blo 2033435 8930371 := bstep (se 1 (by rfl) ⟨6697778, by rfl⟩ : syracuseStep 8930371 = 13395557) B13395557
theorem B11907161 : Blo 2033435 11907161 := bstep (se 2 (by rfl) ⟨4465185, by rfl⟩ : syracuseStep 11907161 = 8930371) B8930371
theorem B7938107 : Blo 2033435 7938107 := bstep (se 1 (by rfl) ⟨5953580, by rfl⟩ : syracuseStep 7938107 = 11907161) B11907161
theorem B5292071 : Blo 2033435 5292071 := bstep (se 1 (by rfl) ⟨3969053, by rfl⟩ : syracuseStep 5292071 = 7938107) B7938107
theorem B3528047 : Blo 2033435 3528047 := bstep (se 1 (by rfl) ⟨2646035, by rfl⟩ : syracuseStep 3528047 = 5292071) B5292071
theorem B9408125 : Blo 2033435 9408125 := bstep (se 3 (by rfl) ⟨1764023, by rfl⟩ : syracuseStep 9408125 = 3528047) B3528047
theorem B6272083 : Blo 2033435 6272083 := bstep (se 1 (by rfl) ⟨4704062, by rfl⟩ : syracuseStep 6272083 = 9408125) B9408125
theorem B8362777 : Blo 2033435 8362777 := bstep (se 2 (by rfl) ⟨3136041, by rfl⟩ : syracuseStep 8362777 = 6272083) B6272083
theorem B11150369 : Blo 2033435 11150369 := bstep (se 2 (by rfl) ⟨4181388, by rfl⟩ : syracuseStep 11150369 = 8362777) B8362777
theorem B7433579 : Blo 2033435 7433579 := bstep (se 1 (by rfl) ⟨5575184, by rfl⟩ : syracuseStep 7433579 = 11150369) B11150369
theorem B19822877 : Blo 2033435 19822877 := bstep (se 3 (by rfl) ⟨3716789, by rfl⟩ : syracuseStep 19822877 = 7433579) B7433579
theorem B13215251 : Blo 2033435 13215251 := bstep (se 1 (by rfl) ⟨9911438, by rfl⟩ : syracuseStep 13215251 = 19822877) B19822877
theorem B8810167 : Blo 2033435 8810167 := bstep (se 1 (by rfl) ⟨6607625, by rfl⟩ : syracuseStep 8810167 = 13215251) B13215251
theorem B11746889 : Blo 2033435 11746889 := bstep (se 2 (by rfl) ⟨4405083, by rfl⟩ : syracuseStep 11746889 = 8810167) B8810167
theorem B7831259 : Blo 2033435 7831259 := bstep (se 1 (by rfl) ⟨5873444, by rfl⟩ : syracuseStep 7831259 = 11746889) B11746889
theorem B5220839 : Blo 2033435 5220839 := bstep (se 1 (by rfl) ⟨3915629, by rfl⟩ : syracuseStep 5220839 = 7831259) B7831259
theorem B13922237 : Blo 2033435 13922237 := bstep (se 3 (by rfl) ⟨2610419, by rfl⟩ : syracuseStep 13922237 = 5220839) B5220839
theorem B37125965 : Blo 2033435 37125965 := bstep (se 3 (by rfl) ⟨6961118, by rfl⟩ : syracuseStep 37125965 = 13922237) B13922237
theorem B99002573 : Blo 2033435 99002573 := bstep (se 3 (by rfl) ⟨18562982, by rfl⟩ : syracuseStep 99002573 = 37125965) B37125965
theorem B66001715 : Blo 2033435 66001715 := bstep (se 1 (by rfl) ⟨49501286, by rfl⟩ : syracuseStep 66001715 = 99002573) B99002573
theorem B44001143 : Blo 2033435 44001143 := bstep (se 1 (by rfl) ⟨33000857, by rfl⟩ : syracuseStep 44001143 = 66001715) B66001715
theorem B29334095 : Blo 2033435 29334095 := bstep (se 1 (by rfl) ⟨22000571, by rfl⟩ : syracuseStep 29334095 = 44001143) B44001143
theorem B19556063 : Blo 2033435 19556063 := bstep (se 1 (by rfl) ⟨14667047, by rfl⟩ : syracuseStep 19556063 = 29334095) B29334095
theorem B13037375 : Blo 2033435 13037375 := bstep (se 1 (by rfl) ⟨9778031, by rfl⟩ : syracuseStep 13037375 = 19556063) B19556063
theorem B8691583 : Blo 2033435 8691583 := bstep (se 1 (by rfl) ⟨6518687, by rfl⟩ : syracuseStep 8691583 = 13037375) B13037375
theorem B11588777 : Blo 2033435 11588777 := bstep (se 2 (by rfl) ⟨4345791, by rfl⟩ : syracuseStep 11588777 = 8691583) B8691583
theorem B7725851 : Blo 2033435 7725851 := bstep (se 1 (by rfl) ⟨5794388, by rfl⟩ : syracuseStep 7725851 = 11588777) B11588777
theorem B5150567 : Blo 2033435 5150567 := bstep (se 1 (by rfl) ⟨3862925, by rfl⟩ : syracuseStep 5150567 = 7725851) B7725851
theorem B3433711 : Blo 2033435 3433711 := bstep (se 1 (by rfl) ⟨2575283, by rfl⟩ : syracuseStep 3433711 = 5150567) B5150567
theorem B4578281 : Blo 2033435 4578281 := bstep (se 2 (by rfl) ⟨1716855, by rfl⟩ : syracuseStep 4578281 = 3433711) B3433711
theorem B3052187 : Blo 2033435 3052187 := bstep (se 1 (by rfl) ⟨2289140, by rfl⟩ : syracuseStep 3052187 = 4578281) B4578281
theorem B2034791 : Blo 2033435 2034791 := bstep (se 1 (by rfl) ⟨1526093, by rfl⟩ : syracuseStep 2034791 = 3052187) B3052187
theorem B2289145 : Blo 2033435 2289145 := bbase (se 2 (by rfl) ⟨858429, by rfl⟩ : syracuseStep 2289145 = 1716859) (by norm_num)
theorem B3052193 : Blo 2033435 3052193 := bstep (se 2 (by rfl) ⟨1144572, by rfl⟩ : syracuseStep 3052193 = 2289145) B2289145
theorem B2034795 : Blo 2033435 2034795 := bstep (se 1 (by rfl) ⟨1526096, by rfl⟩ : syracuseStep 2034795 = 3052193) B3052193
theorem B5500165 : Blo 2033435 5500165 := bbase (se 4 (by rfl) ⟨515640, by rfl⟩ : syracuseStep 5500165 = 1031281) (by norm_num)
theorem B7333553 : Blo 2033435 7333553 := bstep (se 2 (by rfl) ⟨2750082, by rfl⟩ : syracuseStep 7333553 = 5500165) B5500165
theorem B4889035 : Blo 2033435 4889035 := bstep (se 1 (by rfl) ⟨3666776, by rfl⟩ : syracuseStep 4889035 = 7333553) B7333553
theorem B6518713 : Blo 2033435 6518713 := bstep (se 2 (by rfl) ⟨2444517, by rfl⟩ : syracuseStep 6518713 = 4889035) B4889035
theorem B8691617 : Blo 2033435 8691617 := bstep (se 2 (by rfl) ⟨3259356, by rfl⟩ : syracuseStep 8691617 = 6518713) B6518713
theorem B5794411 : Blo 2033435 5794411 := bstep (se 1 (by rfl) ⟨4345808, by rfl⟩ : syracuseStep 5794411 = 8691617) B8691617
theorem B7725881 : Blo 2033435 7725881 := bstep (se 2 (by rfl) ⟨2897205, by rfl⟩ : syracuseStep 7725881 = 5794411) B5794411
theorem B5150587 : Blo 2033435 5150587 := bstep (se 1 (by rfl) ⟨3862940, by rfl⟩ : syracuseStep 5150587 = 7725881) B7725881
theorem B6867449 : Blo 2033435 6867449 := bstep (se 2 (by rfl) ⟨2575293, by rfl⟩ : syracuseStep 6867449 = 5150587) B5150587
theorem B4578299 : Blo 2033435 4578299 := bstep (se 1 (by rfl) ⟨3433724, by rfl⟩ : syracuseStep 4578299 = 6867449) B6867449
theorem B3052199 : Blo 2033435 3052199 := bstep (se 1 (by rfl) ⟨2289149, by rfl⟩ : syracuseStep 3052199 = 4578299) B4578299
theorem B2034799 : Blo 2033435 2034799 := bstep (se 1 (by rfl) ⟨1526099, by rfl⟩ : syracuseStep 2034799 = 3052199) B3052199
theorem B3052205 : Blo 2033435 3052205 := bbase (se 3 (by rfl) ⟨572288, by rfl⟩ : syracuseStep 3052205 = 1144577) (by norm_num)
theorem B2034803 : Blo 2033435 2034803 := bstep (se 1 (by rfl) ⟨1526102, by rfl⟩ : syracuseStep 2034803 = 3052205) B3052205
theorem B4578317 : Blo 2033435 4578317 := bbase (se 3 (by rfl) ⟨858434, by rfl⟩ : syracuseStep 4578317 = 1716869) (by norm_num)
theorem B3052211 : Blo 2033435 3052211 := bstep (se 1 (by rfl) ⟨2289158, by rfl⟩ : syracuseStep 3052211 = 4578317) B4578317
theorem B2034807 : Blo 2033435 2034807 := bstep (se 1 (by rfl) ⟨1526105, by rfl⟩ : syracuseStep 2034807 = 3052211) B3052211
theorem B2575309 : Blo 2033435 2575309 := bbase (se 3 (by rfl) ⟨482870, by rfl⟩ : syracuseStep 2575309 = 965741) (by norm_num)
theorem B3433745 : Blo 2033435 3433745 := bstep (se 2 (by rfl) ⟨1287654, by rfl⟩ : syracuseStep 3433745 = 2575309) B2575309
theorem B2289163 : Blo 2033435 2289163 := bstep (se 1 (by rfl) ⟨1716872, by rfl⟩ : syracuseStep 2289163 = 3433745) B3433745
theorem B3052217 : Blo 2033435 3052217 := bstep (se 2 (by rfl) ⟨1144581, by rfl⟩ : syracuseStep 3052217 = 2289163) B2289163
theorem B2034811 : Blo 2033435 2034811 := bstep (se 1 (by rfl) ⟨1526108, by rfl⟩ : syracuseStep 2034811 = 3052217) B3052217
theorem B3969101 : Blo 2033435 3969101 := bbase (se 3 (by rfl) ⟨744206, by rfl⟩ : syracuseStep 3969101 = 1488413) (by norm_num)
theorem B10584269 : Blo 2033435 10584269 := bstep (se 3 (by rfl) ⟨1984550, by rfl⟩ : syracuseStep 10584269 = 3969101) B3969101
theorem B7056179 : Blo 2033435 7056179 := bstep (se 1 (by rfl) ⟨5292134, by rfl⟩ : syracuseStep 7056179 = 10584269) B10584269
theorem B4704119 : Blo 2033435 4704119 := bstep (se 1 (by rfl) ⟨3528089, by rfl⟩ : syracuseStep 4704119 = 7056179) B7056179
theorem B3136079 : Blo 2033435 3136079 := bstep (se 1 (by rfl) ⟨2352059, by rfl⟩ : syracuseStep 3136079 = 4704119) B4704119
theorem B2090719 : Blo 2033435 2090719 := bstep (se 1 (by rfl) ⟨1568039, by rfl⟩ : syracuseStep 2090719 = 3136079) B3136079
theorem B2787625 : Blo 2033435 2787625 := bstep (se 2 (by rfl) ⟨1045359, by rfl⟩ : syracuseStep 2787625 = 2090719) B2090719
theorem B14867333 : Blo 2033435 14867333 := bstep (se 4 (by rfl) ⟨1393812, by rfl⟩ : syracuseStep 14867333 = 2787625) B2787625
theorem B9911555 : Blo 2033435 9911555 := bstep (se 1 (by rfl) ⟨7433666, by rfl⟩ : syracuseStep 9911555 = 14867333) B14867333
theorem B6607703 : Blo 2033435 6607703 := bstep (se 1 (by rfl) ⟨4955777, by rfl⟩ : syracuseStep 6607703 = 9911555) B9911555
theorem B17620541 : Blo 2033435 17620541 := bstep (se 3 (by rfl) ⟨3303851, by rfl⟩ : syracuseStep 17620541 = 6607703) B6607703
theorem B11747027 : Blo 2033435 11747027 := bstep (se 1 (by rfl) ⟨8810270, by rfl⟩ : syracuseStep 11747027 = 17620541) B17620541
theorem B7831351 : Blo 2033435 7831351 := bstep (se 1 (by rfl) ⟨5873513, by rfl⟩ : syracuseStep 7831351 = 11747027) B11747027
theorem B10441801 : Blo 2033435 10441801 := bstep (se 2 (by rfl) ⟨3915675, by rfl⟩ : syracuseStep 10441801 = 7831351) B7831351
theorem B13922401 : Blo 2033435 13922401 := bstep (se 2 (by rfl) ⟨5220900, by rfl⟩ : syracuseStep 13922401 = 10441801) B10441801
theorem B18563201 : Blo 2033435 18563201 := bstep (se 2 (by rfl) ⟨6961200, by rfl⟩ : syracuseStep 18563201 = 13922401) B13922401
theorem B12375467 : Blo 2033435 12375467 := bstep (se 1 (by rfl) ⟨9281600, by rfl⟩ : syracuseStep 12375467 = 18563201) B18563201
theorem B8250311 : Blo 2033435 8250311 := bstep (se 1 (by rfl) ⟨6187733, by rfl⟩ : syracuseStep 8250311 = 12375467) B12375467
theorem B5500207 : Blo 2033435 5500207 := bstep (se 1 (by rfl) ⟨4125155, by rfl⟩ : syracuseStep 5500207 = 8250311) B8250311
theorem B29334437 : Blo 2033435 29334437 := bstep (se 4 (by rfl) ⟨2750103, by rfl⟩ : syracuseStep 29334437 = 5500207) B5500207
theorem B19556291 : Blo 2033435 19556291 := bstep (se 1 (by rfl) ⟨14667218, by rfl⟩ : syracuseStep 19556291 = 29334437) B29334437
theorem B13037527 : Blo 2033435 13037527 := bstep (se 1 (by rfl) ⟨9778145, by rfl⟩ : syracuseStep 13037527 = 19556291) B19556291
theorem B17383369 : Blo 2033435 17383369 := bstep (se 2 (by rfl) ⟨6518763, by rfl⟩ : syracuseStep 17383369 = 13037527) B13037527
theorem B23177825 : Blo 2033435 23177825 := bstep (se 2 (by rfl) ⟨8691684, by rfl⟩ : syracuseStep 23177825 = 17383369) B17383369
theorem B15451883 : Blo 2033435 15451883 := bstep (se 1 (by rfl) ⟨11588912, by rfl⟩ : syracuseStep 15451883 = 23177825) B23177825
theorem B10301255 : Blo 2033435 10301255 := bstep (se 1 (by rfl) ⟨7725941, by rfl⟩ : syracuseStep 10301255 = 15451883) B15451883
theorem B6867503 : Blo 2033435 6867503 := bstep (se 1 (by rfl) ⟨5150627, by rfl⟩ : syracuseStep 6867503 = 10301255) B10301255
theorem B4578335 : Blo 2033435 4578335 := bstep (se 1 (by rfl) ⟨3433751, by rfl⟩ : syracuseStep 4578335 = 6867503) B6867503
theorem B3052223 : Blo 2033435 3052223 := bstep (se 1 (by rfl) ⟨2289167, by rfl⟩ : syracuseStep 3052223 = 4578335) B4578335
theorem B2034815 : Blo 2033435 2034815 := bstep (se 1 (by rfl) ⟨1526111, by rfl⟩ : syracuseStep 2034815 = 3052223) B3052223
theorem B3052229 : Blo 2033435 3052229 := bbase (se 4 (by rfl) ⟨286146, by rfl⟩ : syracuseStep 3052229 = 572293) (by norm_num)
theorem B2034819 : Blo 2033435 2034819 := bstep (se 1 (by rfl) ⟨1526114, by rfl⟩ : syracuseStep 2034819 = 3052229) B3052229
theorem B3433765 : Blo 2033435 3433765 := bbase (se 4 (by rfl) ⟨321915, by rfl⟩ : syracuseStep 3433765 = 643831) (by norm_num)
theorem B4578353 : Blo 2033435 4578353 := bstep (se 2 (by rfl) ⟨1716882, by rfl⟩ : syracuseStep 4578353 = 3433765) B3433765
theorem B3052235 : Blo 2033435 3052235 := bstep (se 1 (by rfl) ⟨2289176, by rfl⟩ : syracuseStep 3052235 = 4578353) B4578353
theorem B2034823 : Blo 2033435 2034823 := bstep (se 1 (by rfl) ⟨1526117, by rfl⟩ : syracuseStep 2034823 = 3052235) B3052235
theorem B2289181 : Blo 2033435 2289181 := bbase (se 3 (by rfl) ⟨429221, by rfl⟩ : syracuseStep 2289181 = 858443) (by norm_num)
theorem B3052241 : Blo 2033435 3052241 := bstep (se 2 (by rfl) ⟨1144590, by rfl⟩ : syracuseStep 3052241 = 2289181) B2289181
theorem B2034827 : Blo 2033435 2034827 := bstep (se 1 (by rfl) ⟨1526120, by rfl⟩ : syracuseStep 2034827 = 3052241) B3052241
theorem B6867557 : Blo 2033435 6867557 := bbase (se 4 (by rfl) ⟨643833, by rfl⟩ : syracuseStep 6867557 = 1287667) (by norm_num)
theorem B4578371 : Blo 2033435 4578371 := bstep (se 1 (by rfl) ⟨3433778, by rfl⟩ : syracuseStep 4578371 = 6867557) B6867557
theorem B3052247 : Blo 2033435 3052247 := bstep (se 1 (by rfl) ⟨2289185, by rfl⟩ : syracuseStep 3052247 = 4578371) B4578371
theorem B2034831 : Blo 2033435 2034831 := bstep (se 1 (by rfl) ⟨1526123, by rfl⟩ : syracuseStep 2034831 = 3052247) B3052247
theorem B3052253 : Blo 2033435 3052253 := bbase (se 3 (by rfl) ⟨572297, by rfl⟩ : syracuseStep 3052253 = 1144595) (by norm_num)
theorem B2034835 : Blo 2033435 2034835 := bstep (se 1 (by rfl) ⟨1526126, by rfl⟩ : syracuseStep 2034835 = 3052253) B3052253
theorem B4578389 : Blo 2033435 4578389 := bbase (se 8 (by rfl) ⟨26826, by rfl⟩ : syracuseStep 4578389 = 53653) (by norm_num)
theorem B3052259 : Blo 2033435 3052259 := bstep (se 1 (by rfl) ⟨2289194, by rfl⟩ : syracuseStep 3052259 = 4578389) B4578389
theorem B2034839 : Blo 2033435 2034839 := bstep (se 1 (by rfl) ⟨1526129, by rfl⟩ : syracuseStep 2034839 = 3052259) B3052259
theorem B8362997 : Blo 2033435 8362997 := bbase (se 5 (by rfl) ⟨392015, by rfl⟩ : syracuseStep 8362997 = 784031) (by norm_num)
theorem B5575331 : Blo 2033435 5575331 := bstep (se 1 (by rfl) ⟨4181498, by rfl⟩ : syracuseStep 5575331 = 8362997) B8362997
theorem B3716887 : Blo 2033435 3716887 := bstep (se 1 (by rfl) ⟨2787665, by rfl⟩ : syracuseStep 3716887 = 5575331) B5575331
theorem B4955849 : Blo 2033435 4955849 := bstep (se 2 (by rfl) ⟨1858443, by rfl⟩ : syracuseStep 4955849 = 3716887) B3716887
theorem B3303899 : Blo 2033435 3303899 := bstep (se 1 (by rfl) ⟨2477924, by rfl⟩ : syracuseStep 3303899 = 4955849) B4955849
theorem B2202599 : Blo 2033435 2202599 := bstep (se 1 (by rfl) ⟨1651949, by rfl⟩ : syracuseStep 2202599 = 3303899) B3303899
theorem B5873597 : Blo 2033435 5873597 := bstep (se 3 (by rfl) ⟨1101299, by rfl⟩ : syracuseStep 5873597 = 2202599) B2202599
theorem B3915731 : Blo 2033435 3915731 := bstep (se 1 (by rfl) ⟨2936798, by rfl⟩ : syracuseStep 3915731 = 5873597) B5873597
theorem B2610487 : Blo 2033435 2610487 := bstep (se 1 (by rfl) ⟨1957865, by rfl⟩ : syracuseStep 2610487 = 3915731) B3915731
theorem B13922597 : Blo 2033435 13922597 := bstep (se 4 (by rfl) ⟨1305243, by rfl⟩ : syracuseStep 13922597 = 2610487) B2610487
theorem B9281731 : Blo 2033435 9281731 := bstep (se 1 (by rfl) ⟨6961298, by rfl⟩ : syracuseStep 9281731 = 13922597) B13922597
theorem B12375641 : Blo 2033435 12375641 := bstep (se 2 (by rfl) ⟨4640865, by rfl⟩ : syracuseStep 12375641 = 9281731) B9281731
theorem B8250427 : Blo 2033435 8250427 := bstep (se 1 (by rfl) ⟨6187820, by rfl⟩ : syracuseStep 8250427 = 12375641) B12375641
theorem B11000569 : Blo 2033435 11000569 := bstep (se 2 (by rfl) ⟨4125213, by rfl⟩ : syracuseStep 11000569 = 8250427) B8250427
theorem B14667425 : Blo 2033435 14667425 := bstep (se 2 (by rfl) ⟨5500284, by rfl⟩ : syracuseStep 14667425 = 11000569) B11000569
theorem B9778283 : Blo 2033435 9778283 := bstep (se 1 (by rfl) ⟨7333712, by rfl⟩ : syracuseStep 9778283 = 14667425) B14667425
theorem B6518855 : Blo 2033435 6518855 := bstep (se 1 (by rfl) ⟨4889141, by rfl⟩ : syracuseStep 6518855 = 9778283) B9778283
theorem B4345903 : Blo 2033435 4345903 := bstep (se 1 (by rfl) ⟨3259427, by rfl⟩ : syracuseStep 4345903 = 6518855) B6518855
theorem B5794537 : Blo 2033435 5794537 := bstep (se 2 (by rfl) ⟨2172951, by rfl⟩ : syracuseStep 5794537 = 4345903) B4345903
theorem B7726049 : Blo 2033435 7726049 := bstep (se 2 (by rfl) ⟨2897268, by rfl⟩ : syracuseStep 7726049 = 5794537) B5794537
theorem B5150699 : Blo 2033435 5150699 := bstep (se 1 (by rfl) ⟨3863024, by rfl⟩ : syracuseStep 5150699 = 7726049) B7726049
theorem B3433799 : Blo 2033435 3433799 := bstep (se 1 (by rfl) ⟨2575349, by rfl⟩ : syracuseStep 3433799 = 5150699) B5150699
theorem B2289199 : Blo 2033435 2289199 := bstep (se 1 (by rfl) ⟨1716899, by rfl⟩ : syracuseStep 2289199 = 3433799) B3433799
theorem B3052265 : Blo 2033435 3052265 := bstep (se 2 (by rfl) ⟨1144599, by rfl⟩ : syracuseStep 3052265 = 2289199) B2289199
theorem B2034843 : Blo 2033435 2034843 := bstep (se 1 (by rfl) ⟨1526132, by rfl⟩ : syracuseStep 2034843 = 3052265) B3052265
theorem B4405205 : Blo 2033435 4405205 := bbase (se 7 (by rfl) ⟨51623, by rfl⟩ : syracuseStep 4405205 = 103247) (by norm_num)
theorem B11747213 : Blo 2033435 11747213 := bstep (se 3 (by rfl) ⟨2202602, by rfl⟩ : syracuseStep 11747213 = 4405205) B4405205
theorem B7831475 : Blo 2033435 7831475 := bstep (se 1 (by rfl) ⟨5873606, by rfl⟩ : syracuseStep 7831475 = 11747213) B11747213
theorem B5220983 : Blo 2033435 5220983 := bstep (se 1 (by rfl) ⟨3915737, by rfl⟩ : syracuseStep 5220983 = 7831475) B7831475
theorem B3480655 : Blo 2033435 3480655 := bstep (se 1 (by rfl) ⟨2610491, by rfl⟩ : syracuseStep 3480655 = 5220983) B5220983
theorem B4640873 : Blo 2033435 4640873 := bstep (se 2 (by rfl) ⟨1740327, by rfl⟩ : syracuseStep 4640873 = 3480655) B3480655
theorem B12375661 : Blo 2033435 12375661 := bstep (se 3 (by rfl) ⟨2320436, by rfl⟩ : syracuseStep 12375661 = 4640873) B4640873
theorem B16500881 : Blo 2033435 16500881 := bstep (se 2 (by rfl) ⟨6187830, by rfl⟩ : syracuseStep 16500881 = 12375661) B12375661
theorem B44002349 : Blo 2033435 44002349 := bstep (se 3 (by rfl) ⟨8250440, by rfl⟩ : syracuseStep 44002349 = 16500881) B16500881
theorem B29334899 : Blo 2033435 29334899 := bstep (se 1 (by rfl) ⟨22001174, by rfl⟩ : syracuseStep 29334899 = 44002349) B44002349
theorem B19556599 : Blo 2033435 19556599 := bstep (se 1 (by rfl) ⟨14667449, by rfl⟩ : syracuseStep 19556599 = 29334899) B29334899
theorem B26075465 : Blo 2033435 26075465 := bstep (se 2 (by rfl) ⟨9778299, by rfl⟩ : syracuseStep 26075465 = 19556599) B19556599
theorem B17383643 : Blo 2033435 17383643 := bstep (se 1 (by rfl) ⟨13037732, by rfl⟩ : syracuseStep 17383643 = 26075465) B26075465
theorem B11589095 : Blo 2033435 11589095 := bstep (se 1 (by rfl) ⟨8691821, by rfl⟩ : syracuseStep 11589095 = 17383643) B17383643
theorem B7726063 : Blo 2033435 7726063 := bstep (se 1 (by rfl) ⟨5794547, by rfl⟩ : syracuseStep 7726063 = 11589095) B11589095
theorem B10301417 : Blo 2033435 10301417 := bstep (se 2 (by rfl) ⟨3863031, by rfl⟩ : syracuseStep 10301417 = 7726063) B7726063
theorem B6867611 : Blo 2033435 6867611 := bstep (se 1 (by rfl) ⟨5150708, by rfl⟩ : syracuseStep 6867611 = 10301417) B10301417
theorem B4578407 : Blo 2033435 4578407 := bstep (se 1 (by rfl) ⟨3433805, by rfl⟩ : syracuseStep 4578407 = 6867611) B6867611
theorem B3052271 : Blo 2033435 3052271 := bstep (se 1 (by rfl) ⟨2289203, by rfl⟩ : syracuseStep 3052271 = 4578407) B4578407
theorem B2034847 : Blo 2033435 2034847 := bstep (se 1 (by rfl) ⟨1526135, by rfl⟩ : syracuseStep 2034847 = 3052271) B3052271
theorem B3052277 : Blo 2033435 3052277 := bbase (se 5 (by rfl) ⟨143075, by rfl⟩ : syracuseStep 3052277 = 286151) (by norm_num)
theorem B2034851 : Blo 2033435 2034851 := bstep (se 1 (by rfl) ⟨1526138, by rfl⟩ : syracuseStep 2034851 = 3052277) B3052277
theorem B2444585 : Blo 2033435 2444585 := bbase (se 2 (by rfl) ⟨916719, by rfl⟩ : syracuseStep 2444585 = 1833439) (by norm_num)
theorem B6518893 : Blo 2033435 6518893 := bstep (se 3 (by rfl) ⟨1222292, by rfl⟩ : syracuseStep 6518893 = 2444585) B2444585
theorem B8691857 : Blo 2033435 8691857 := bstep (se 2 (by rfl) ⟨3259446, by rfl⟩ : syracuseStep 8691857 = 6518893) B6518893
theorem B5794571 : Blo 2033435 5794571 := bstep (se 1 (by rfl) ⟨4345928, by rfl⟩ : syracuseStep 5794571 = 8691857) B8691857
theorem B3863047 : Blo 2033435 3863047 := bstep (se 1 (by rfl) ⟨2897285, by rfl⟩ : syracuseStep 3863047 = 5794571) B5794571
theorem B5150729 : Blo 2033435 5150729 := bstep (se 2 (by rfl) ⟨1931523, by rfl⟩ : syracuseStep 5150729 = 3863047) B3863047
theorem B3433819 : Blo 2033435 3433819 := bstep (se 1 (by rfl) ⟨2575364, by rfl⟩ : syracuseStep 3433819 = 5150729) B5150729
theorem B4578425 : Blo 2033435 4578425 := bstep (se 2 (by rfl) ⟨1716909, by rfl⟩ : syracuseStep 4578425 = 3433819) B3433819
theorem B3052283 : Blo 2033435 3052283 := bstep (se 1 (by rfl) ⟨2289212, by rfl⟩ : syracuseStep 3052283 = 4578425) B4578425
theorem B2034855 : Blo 2033435 2034855 := bstep (se 1 (by rfl) ⟨1526141, by rfl⟩ : syracuseStep 2034855 = 3052283) B3052283
theorem B2289217 : Blo 2033435 2289217 := bbase (se 2 (by rfl) ⟨858456, by rfl⟩ : syracuseStep 2289217 = 1716913) (by norm_num)
theorem B3052289 : Blo 2033435 3052289 := bstep (se 2 (by rfl) ⟨1144608, by rfl⟩ : syracuseStep 3052289 = 2289217) B2289217
theorem B2034859 : Blo 2033435 2034859 := bstep (se 1 (by rfl) ⟨1526144, by rfl⟩ : syracuseStep 2034859 = 3052289) B3052289
theorem B5150749 : Blo 2033435 5150749 := bbase (se 3 (by rfl) ⟨965765, by rfl⟩ : syracuseStep 5150749 = 1931531) (by norm_num)
theorem B6867665 : Blo 2033435 6867665 := bstep (se 2 (by rfl) ⟨2575374, by rfl⟩ : syracuseStep 6867665 = 5150749) B5150749
theorem B4578443 : Blo 2033435 4578443 := bstep (se 1 (by rfl) ⟨3433832, by rfl⟩ : syracuseStep 4578443 = 6867665) B6867665
theorem B3052295 : Blo 2033435 3052295 := bstep (se 1 (by rfl) ⟨2289221, by rfl⟩ : syracuseStep 3052295 = 4578443) B4578443
theorem B2034863 : Blo 2033435 2034863 := bstep (se 1 (by rfl) ⟨1526147, by rfl⟩ : syracuseStep 2034863 = 3052295) B3052295
theorem B3052301 : Blo 2033435 3052301 := bbase (se 3 (by rfl) ⟨572306, by rfl⟩ : syracuseStep 3052301 = 1144613) (by norm_num)
theorem B2034867 : Blo 2033435 2034867 := bstep (se 1 (by rfl) ⟨1526150, by rfl⟩ : syracuseStep 2034867 = 3052301) B3052301
theorem B4578461 : Blo 2033435 4578461 := bbase (se 3 (by rfl) ⟨858461, by rfl⟩ : syracuseStep 4578461 = 1716923) (by norm_num)
theorem B3052307 : Blo 2033435 3052307 := bstep (se 1 (by rfl) ⟨2289230, by rfl⟩ : syracuseStep 3052307 = 4578461) B4578461
theorem B2034871 : Blo 2033435 2034871 := bstep (se 1 (by rfl) ⟨1526153, by rfl⟩ : syracuseStep 2034871 = 3052307) B3052307
theorem B3433853 : Blo 2033435 3433853 := bbase (se 3 (by rfl) ⟨643847, by rfl⟩ : syracuseStep 3433853 = 1287695) (by norm_num)
theorem B2289235 : Blo 2033435 2289235 := bstep (se 1 (by rfl) ⟨1716926, by rfl⟩ : syracuseStep 2289235 = 3433853) B3433853
theorem B3052313 : Blo 2033435 3052313 := bstep (se 2 (by rfl) ⟨1144617, by rfl⟩ : syracuseStep 3052313 = 2289235) B2289235
theorem B2034875 : Blo 2033435 2034875 := bstep (se 1 (by rfl) ⟨1526156, by rfl⟩ : syracuseStep 2034875 = 3052313) B3052313
theorem B3093965 : Blo 2033435 3093965 := bbase (se 3 (by rfl) ⟨580118, by rfl⟩ : syracuseStep 3093965 = 1160237) (by norm_num)
theorem B2062643 : Blo 2033435 2062643 := bstep (se 1 (by rfl) ⟨1546982, by rfl⟩ : syracuseStep 2062643 = 3093965) B3093965
theorem B5500381 : Blo 2033435 5500381 := bstep (se 3 (by rfl) ⟨1031321, by rfl⟩ : syracuseStep 5500381 = 2062643) B2062643
theorem B7333841 : Blo 2033435 7333841 := bstep (se 2 (by rfl) ⟨2750190, by rfl⟩ : syracuseStep 7333841 = 5500381) B5500381
theorem B4889227 : Blo 2033435 4889227 := bstep (se 1 (by rfl) ⟨3666920, by rfl⟩ : syracuseStep 4889227 = 7333841) B7333841
theorem B6518969 : Blo 2033435 6518969 := bstep (se 2 (by rfl) ⟨2444613, by rfl⟩ : syracuseStep 6518969 = 4889227) B4889227
theorem B4345979 : Blo 2033435 4345979 := bstep (se 1 (by rfl) ⟨3259484, by rfl⟩ : syracuseStep 4345979 = 6518969) B6518969
theorem B11589277 : Blo 2033435 11589277 := bstep (se 3 (by rfl) ⟨2172989, by rfl⟩ : syracuseStep 11589277 = 4345979) B4345979
theorem B15452369 : Blo 2033435 15452369 := bstep (se 2 (by rfl) ⟨5794638, by rfl⟩ : syracuseStep 15452369 = 11589277) B11589277
theorem B10301579 : Blo 2033435 10301579 := bstep (se 1 (by rfl) ⟨7726184, by rfl⟩ : syracuseStep 10301579 = 15452369) B15452369
theorem B6867719 : Blo 2033435 6867719 := bstep (se 1 (by rfl) ⟨5150789, by rfl⟩ : syracuseStep 6867719 = 10301579) B10301579
theorem B4578479 : Blo 2033435 4578479 := bstep (se 1 (by rfl) ⟨3433859, by rfl⟩ : syracuseStep 4578479 = 6867719) B6867719
theorem B3052319 : Blo 2033435 3052319 := bstep (se 1 (by rfl) ⟨2289239, by rfl⟩ : syracuseStep 3052319 = 4578479) B4578479
theorem B2034879 : Blo 2033435 2034879 := bstep (se 1 (by rfl) ⟨1526159, by rfl⟩ : syracuseStep 2034879 = 3052319) B3052319
theorem B3052325 : Blo 2033435 3052325 := bbase (se 4 (by rfl) ⟨286155, by rfl⟩ : syracuseStep 3052325 = 572311) (by norm_num)
theorem B2034883 : Blo 2033435 2034883 := bstep (se 1 (by rfl) ⟨1526162, by rfl⟩ : syracuseStep 2034883 = 3052325) B3052325
theorem B2575405 : Blo 2033435 2575405 := bbase (se 3 (by rfl) ⟨482888, by rfl⟩ : syracuseStep 2575405 = 965777) (by norm_num)
theorem B3433873 : Blo 2033435 3433873 := bstep (se 2 (by rfl) ⟨1287702, by rfl⟩ : syracuseStep 3433873 = 2575405) B2575405
theorem B4578497 : Blo 2033435 4578497 := bstep (se 2 (by rfl) ⟨1716936, by rfl⟩ : syracuseStep 4578497 = 3433873) B3433873
theorem B3052331 : Blo 2033435 3052331 := bstep (se 1 (by rfl) ⟨2289248, by rfl⟩ : syracuseStep 3052331 = 4578497) B4578497
theorem B2034887 : Blo 2033435 2034887 := bstep (se 1 (by rfl) ⟨1526165, by rfl⟩ : syracuseStep 2034887 = 3052331) B3052331
theorem B2289253 : Blo 2033435 2289253 := bbase (se 4 (by rfl) ⟨214617, by rfl⟩ : syracuseStep 2289253 = 429235) (by norm_num)
theorem B3052337 : Blo 2033435 3052337 := bstep (se 2 (by rfl) ⟨1144626, by rfl⟩ : syracuseStep 3052337 = 2289253) B2289253
theorem B2034891 : Blo 2033435 2034891 := bstep (se 1 (by rfl) ⟨1526168, by rfl⟩ : syracuseStep 2034891 = 3052337) B3052337
theorem B2750213 : Blo 2033435 2750213 := bbase (se 4 (by rfl) ⟨257832, by rfl⟩ : syracuseStep 2750213 = 515665) (by norm_num)
theorem B7333901 : Blo 2033435 7333901 := bstep (se 3 (by rfl) ⟨1375106, by rfl⟩ : syracuseStep 7333901 = 2750213) B2750213
theorem B4889267 : Blo 2033435 4889267 := bstep (se 1 (by rfl) ⟨3666950, by rfl⟩ : syracuseStep 4889267 = 7333901) B7333901
theorem B3259511 : Blo 2033435 3259511 := bstep (se 1 (by rfl) ⟨2444633, by rfl⟩ : syracuseStep 3259511 = 4889267) B4889267
theorem B2173007 : Blo 2033435 2173007 := bstep (se 1 (by rfl) ⟨1629755, by rfl⟩ : syracuseStep 2173007 = 3259511) B3259511
theorem B5794685 : Blo 2033435 5794685 := bstep (se 3 (by rfl) ⟨1086503, by rfl⟩ : syracuseStep 5794685 = 2173007) B2173007
theorem B3863123 : Blo 2033435 3863123 := bstep (se 1 (by rfl) ⟨2897342, by rfl⟩ : syracuseStep 3863123 = 5794685) B5794685
theorem B2575415 : Blo 2033435 2575415 := bstep (se 1 (by rfl) ⟨1931561, by rfl⟩ : syracuseStep 2575415 = 3863123) B3863123
theorem B6867773 : Blo 2033435 6867773 := bstep (se 3 (by rfl) ⟨1287707, by rfl⟩ : syracuseStep 6867773 = 2575415) B2575415
theorem B4578515 : Blo 2033435 4578515 := bstep (se 1 (by rfl) ⟨3433886, by rfl⟩ : syracuseStep 4578515 = 6867773) B6867773
theorem B3052343 : Blo 2033435 3052343 := bstep (se 1 (by rfl) ⟨2289257, by rfl⟩ : syracuseStep 3052343 = 4578515) B4578515
theorem B2034895 : Blo 2033435 2034895 := bstep (se 1 (by rfl) ⟨1526171, by rfl⟩ : syracuseStep 2034895 = 3052343) B3052343
theorem B3052349 : Blo 2033435 3052349 := bbase (se 3 (by rfl) ⟨572315, by rfl⟩ : syracuseStep 3052349 = 1144631) (by norm_num)
theorem B2034899 : Blo 2033435 2034899 := bstep (se 1 (by rfl) ⟨1526174, by rfl⟩ : syracuseStep 2034899 = 3052349) B3052349
theorem B4578533 : Blo 2033435 4578533 := bbase (se 4 (by rfl) ⟨429237, by rfl⟩ : syracuseStep 4578533 = 858475) (by norm_num)
theorem B3052355 : Blo 2033435 3052355 := bstep (se 1 (by rfl) ⟨2289266, by rfl⟩ : syracuseStep 3052355 = 4578533) B4578533
theorem B2034903 : Blo 2033435 2034903 := bstep (se 1 (by rfl) ⟨1526177, by rfl⟩ : syracuseStep 2034903 = 3052355) B3052355
theorem B5150861 : Blo 2033435 5150861 := bbase (se 3 (by rfl) ⟨965786, by rfl⟩ : syracuseStep 5150861 = 1931573) (by norm_num)
theorem B3433907 : Blo 2033435 3433907 := bstep (se 1 (by rfl) ⟨2575430, by rfl⟩ : syracuseStep 3433907 = 5150861) B5150861
theorem B2289271 : Blo 2033435 2289271 := bstep (se 1 (by rfl) ⟨1716953, by rfl⟩ : syracuseStep 2289271 = 3433907) B3433907
theorem B3052361 : Blo 2033435 3052361 := bstep (se 2 (by rfl) ⟨1144635, by rfl⟩ : syracuseStep 3052361 = 2289271) B2289271
theorem B2034907 : Blo 2033435 2034907 := bstep (se 1 (by rfl) ⟨1526180, by rfl⟩ : syracuseStep 2034907 = 3052361) B3052361
theorem B2897365 : Blo 2033435 2897365 := bbase (se 7 (by rfl) ⟨33953, by rfl⟩ : syracuseStep 2897365 = 67907) (by norm_num)
theorem B3863153 : Blo 2033435 3863153 := bstep (se 2 (by rfl) ⟨1448682, by rfl⟩ : syracuseStep 3863153 = 2897365) B2897365
theorem B10301741 : Blo 2033435 10301741 := bstep (se 3 (by rfl) ⟨1931576, by rfl⟩ : syracuseStep 10301741 = 3863153) B3863153
theorem B6867827 : Blo 2033435 6867827 := bstep (se 1 (by rfl) ⟨5150870, by rfl⟩ : syracuseStep 6867827 = 10301741) B10301741
theorem B4578551 : Blo 2033435 4578551 := bstep (se 1 (by rfl) ⟨3433913, by rfl⟩ : syracuseStep 4578551 = 6867827) B6867827
theorem B3052367 : Blo 2033435 3052367 := bstep (se 1 (by rfl) ⟨2289275, by rfl⟩ : syracuseStep 3052367 = 4578551) B4578551
theorem B2034911 : Blo 2033435 2034911 := bstep (se 1 (by rfl) ⟨1526183, by rfl⟩ : syracuseStep 2034911 = 3052367) B3052367
theorem B3052373 : Blo 2033435 3052373 := bbase (se 9 (by rfl) ⟨8942, by rfl⟩ : syracuseStep 3052373 = 17885) (by norm_num)
theorem B2034915 : Blo 2033435 2034915 := bstep (se 1 (by rfl) ⟨1526186, by rfl⟩ : syracuseStep 2034915 = 3052373) B3052373
theorem B3259549 : Blo 2033435 3259549 := bbase (se 3 (by rfl) ⟨611165, by rfl⟩ : syracuseStep 3259549 = 1222331) (by norm_num)
theorem B4346065 : Blo 2033435 4346065 := bstep (se 2 (by rfl) ⟨1629774, by rfl⟩ : syracuseStep 4346065 = 3259549) B3259549
theorem B5794753 : Blo 2033435 5794753 := bstep (se 2 (by rfl) ⟨2173032, by rfl⟩ : syracuseStep 5794753 = 4346065) B4346065
theorem B7726337 : Blo 2033435 7726337 := bstep (se 2 (by rfl) ⟨2897376, by rfl⟩ : syracuseStep 7726337 = 5794753) B5794753
theorem B5150891 : Blo 2033435 5150891 := bstep (se 1 (by rfl) ⟨3863168, by rfl⟩ : syracuseStep 5150891 = 7726337) B7726337
theorem B3433927 : Blo 2033435 3433927 := bstep (se 1 (by rfl) ⟨2575445, by rfl⟩ : syracuseStep 3433927 = 5150891) B5150891
theorem B4578569 : Blo 2033435 4578569 := bstep (se 2 (by rfl) ⟨1716963, by rfl⟩ : syracuseStep 4578569 = 3433927) B3433927
theorem B3052379 : Blo 2033435 3052379 := bstep (se 1 (by rfl) ⟨2289284, by rfl⟩ : syracuseStep 3052379 = 4578569) B4578569
theorem B2034919 : Blo 2033435 2034919 := bstep (se 1 (by rfl) ⟨1526189, by rfl⟩ : syracuseStep 2034919 = 3052379) B3052379
theorem B2289289 : Blo 2033435 2289289 := bbase (se 2 (by rfl) ⟨858483, by rfl⟩ : syracuseStep 2289289 = 1716967) (by norm_num)
theorem B3052385 : Blo 2033435 3052385 := bstep (se 2 (by rfl) ⟨1144644, by rfl⟩ : syracuseStep 3052385 = 2289289) B2289289
theorem B2034923 : Blo 2033435 2034923 := bstep (se 1 (by rfl) ⟨1526192, by rfl⟩ : syracuseStep 2034923 = 3052385) B3052385
theorem B5221189 : Blo 2033435 5221189 := bbase (se 4 (by rfl) ⟨489486, by rfl⟩ : syracuseStep 5221189 = 978973) (by norm_num)
theorem B6961585 : Blo 2033435 6961585 := bstep (se 2 (by rfl) ⟨2610594, by rfl⟩ : syracuseStep 6961585 = 5221189) B5221189
theorem B9282113 : Blo 2033435 9282113 := bstep (se 2 (by rfl) ⟨3480792, by rfl⟩ : syracuseStep 9282113 = 6961585) B6961585
theorem B6188075 : Blo 2033435 6188075 := bstep (se 1 (by rfl) ⟨4641056, by rfl⟩ : syracuseStep 6188075 = 9282113) B9282113
theorem B4125383 : Blo 2033435 4125383 := bstep (se 1 (by rfl) ⟨3094037, by rfl⟩ : syracuseStep 4125383 = 6188075) B6188075
theorem B2750255 : Blo 2033435 2750255 := bstep (se 1 (by rfl) ⟨2062691, by rfl⟩ : syracuseStep 2750255 = 4125383) B4125383
theorem B29336053 : Blo 2033435 29336053 := bstep (se 5 (by rfl) ⟨1375127, by rfl⟩ : syracuseStep 29336053 = 2750255) B2750255
theorem B39114737 : Blo 2033435 39114737 := bstep (se 2 (by rfl) ⟨14668026, by rfl⟩ : syracuseStep 39114737 = 29336053) B29336053
theorem B26076491 : Blo 2033435 26076491 := bstep (se 1 (by rfl) ⟨19557368, by rfl⟩ : syracuseStep 26076491 = 39114737) B39114737
theorem B17384327 : Blo 2033435 17384327 := bstep (se 1 (by rfl) ⟨13038245, by rfl⟩ : syracuseStep 17384327 = 26076491) B26076491
theorem B11589551 : Blo 2033435 11589551 := bstep (se 1 (by rfl) ⟨8692163, by rfl⟩ : syracuseStep 11589551 = 17384327) B17384327
theorem B7726367 : Blo 2033435 7726367 := bstep (se 1 (by rfl) ⟨5794775, by rfl⟩ : syracuseStep 7726367 = 11589551) B11589551
theorem B5150911 : Blo 2033435 5150911 := bstep (se 1 (by rfl) ⟨3863183, by rfl⟩ : syracuseStep 5150911 = 7726367) B7726367
theorem B6867881 : Blo 2033435 6867881 := bstep (se 2 (by rfl) ⟨2575455, by rfl⟩ : syracuseStep 6867881 = 5150911) B5150911
theorem B4578587 : Blo 2033435 4578587 := bstep (se 1 (by rfl) ⟨3433940, by rfl⟩ : syracuseStep 4578587 = 6867881) B6867881
theorem B3052391 : Blo 2033435 3052391 := bstep (se 1 (by rfl) ⟨2289293, by rfl⟩ : syracuseStep 3052391 = 4578587) B4578587
theorem B2034927 : Blo 2033435 2034927 := bstep (se 1 (by rfl) ⟨1526195, by rfl⟩ : syracuseStep 2034927 = 3052391) B3052391
theorem B3052397 : Blo 2033435 3052397 := bbase (se 3 (by rfl) ⟨572324, by rfl⟩ : syracuseStep 3052397 = 1144649) (by norm_num)
theorem B2034931 : Blo 2033435 2034931 := bstep (se 1 (by rfl) ⟨1526198, by rfl⟩ : syracuseStep 2034931 = 3052397) B3052397
theorem B4578605 : Blo 2033435 4578605 := bbase (se 3 (by rfl) ⟨858488, by rfl⟩ : syracuseStep 4578605 = 1716977) (by norm_num)
theorem B3052403 : Blo 2033435 3052403 := bstep (se 1 (by rfl) ⟨2289302, by rfl⟩ : syracuseStep 3052403 = 4578605) B4578605
theorem B2034935 : Blo 2033435 2034935 := bstep (se 1 (by rfl) ⟨1526201, by rfl⟩ : syracuseStep 2034935 = 3052403) B3052403
theorem B4641085 : Blo 2033435 4641085 := bbase (se 3 (by rfl) ⟨870203, by rfl⟩ : syracuseStep 4641085 = 1740407) (by norm_num)
theorem B6188113 : Blo 2033435 6188113 := bstep (se 2 (by rfl) ⟨2320542, by rfl⟩ : syracuseStep 6188113 = 4641085) B4641085
theorem B8250817 : Blo 2033435 8250817 := bstep (se 2 (by rfl) ⟨3094056, by rfl⟩ : syracuseStep 8250817 = 6188113) B6188113
theorem B11001089 : Blo 2033435 11001089 := bstep (se 2 (by rfl) ⟨4125408, by rfl⟩ : syracuseStep 11001089 = 8250817) B8250817
theorem B7334059 : Blo 2033435 7334059 := bstep (se 1 (by rfl) ⟨5500544, by rfl⟩ : syracuseStep 7334059 = 11001089) B11001089
theorem B9778745 : Blo 2033435 9778745 := bstep (se 2 (by rfl) ⟨3667029, by rfl⟩ : syracuseStep 9778745 = 7334059) B7334059
theorem B6519163 : Blo 2033435 6519163 := bstep (se 1 (by rfl) ⟨4889372, by rfl⟩ : syracuseStep 6519163 = 9778745) B9778745
theorem B8692217 : Blo 2033435 8692217 := bstep (se 2 (by rfl) ⟨3259581, by rfl⟩ : syracuseStep 8692217 = 6519163) B6519163
theorem B5794811 : Blo 2033435 5794811 := bstep (se 1 (by rfl) ⟨4346108, by rfl⟩ : syracuseStep 5794811 = 8692217) B8692217
theorem B3863207 : Blo 2033435 3863207 := bstep (se 1 (by rfl) ⟨2897405, by rfl⟩ : syracuseStep 3863207 = 5794811) B5794811
theorem B2575471 : Blo 2033435 2575471 := bstep (se 1 (by rfl) ⟨1931603, by rfl⟩ : syracuseStep 2575471 = 3863207) B3863207
theorem B3433961 : Blo 2033435 3433961 := bstep (se 2 (by rfl) ⟨1287735, by rfl⟩ : syracuseStep 3433961 = 2575471) B2575471
theorem B2289307 : Blo 2033435 2289307 := bstep (se 1 (by rfl) ⟨1716980, by rfl⟩ : syracuseStep 2289307 = 3433961) B3433961
theorem B3052409 : Blo 2033435 3052409 := bstep (se 2 (by rfl) ⟨1144653, by rfl⟩ : syracuseStep 3052409 = 2289307) B2289307
theorem B2034939 : Blo 2033435 2034939 := bstep (se 1 (by rfl) ⟨1526204, by rfl⟩ : syracuseStep 2034939 = 3052409) B3052409
theorem B4181701 : Blo 2033435 4181701 := bbase (se 4 (by rfl) ⟨392034, by rfl⟩ : syracuseStep 4181701 = 784069) (by norm_num)
theorem B5575601 : Blo 2033435 5575601 := bstep (se 2 (by rfl) ⟨2090850, by rfl⟩ : syracuseStep 5575601 = 4181701) B4181701
theorem B14868269 : Blo 2033435 14868269 := bstep (se 3 (by rfl) ⟨2787800, by rfl⟩ : syracuseStep 14868269 = 5575601) B5575601
theorem B9912179 : Blo 2033435 9912179 := bstep (se 1 (by rfl) ⟨7434134, by rfl⟩ : syracuseStep 9912179 = 14868269) B14868269
theorem B26432477 : Blo 2033435 26432477 := bstep (se 3 (by rfl) ⟨4956089, by rfl⟩ : syracuseStep 26432477 = 9912179) B9912179
theorem B17621651 : Blo 2033435 17621651 := bstep (se 1 (by rfl) ⟨13216238, by rfl⟩ : syracuseStep 17621651 = 26432477) B26432477
theorem B11747767 : Blo 2033435 11747767 := bstep (se 1 (by rfl) ⟨8810825, by rfl⟩ : syracuseStep 11747767 = 17621651) B17621651
theorem B15663689 : Blo 2033435 15663689 := bstep (se 2 (by rfl) ⟨5873883, by rfl⟩ : syracuseStep 15663689 = 11747767) B11747767
theorem B10442459 : Blo 2033435 10442459 := bstep (se 1 (by rfl) ⟨7831844, by rfl⟩ : syracuseStep 10442459 = 15663689) B15663689
theorem B6961639 : Blo 2033435 6961639 := bstep (se 1 (by rfl) ⟨5221229, by rfl⟩ : syracuseStep 6961639 = 10442459) B10442459
theorem B9282185 : Blo 2033435 9282185 := bstep (se 2 (by rfl) ⟨3480819, by rfl⟩ : syracuseStep 9282185 = 6961639) B6961639
theorem B6188123 : Blo 2033435 6188123 := bstep (se 1 (by rfl) ⟨4641092, by rfl⟩ : syracuseStep 6188123 = 9282185) B9282185
theorem B4125415 : Blo 2033435 4125415 := bstep (se 1 (by rfl) ⟨3094061, by rfl⟩ : syracuseStep 4125415 = 6188123) B6188123
theorem B5500553 : Blo 2033435 5500553 := bstep (se 2 (by rfl) ⟨2062707, by rfl⟩ : syracuseStep 5500553 = 4125415) B4125415
theorem B14668141 : Blo 2033435 14668141 := bstep (se 3 (by rfl) ⟨2750276, by rfl⟩ : syracuseStep 14668141 = 5500553) B5500553
theorem B19557521 : Blo 2033435 19557521 := bstep (se 2 (by rfl) ⟨7334070, by rfl⟩ : syracuseStep 19557521 = 14668141) B14668141
theorem B13038347 : Blo 2033435 13038347 := bstep (se 1 (by rfl) ⟨9778760, by rfl⟩ : syracuseStep 13038347 = 19557521) B19557521
theorem B34768925 : Blo 2033435 34768925 := bstep (se 3 (by rfl) ⟨6519173, by rfl⟩ : syracuseStep 34768925 = 13038347) B13038347
theorem B23179283 : Blo 2033435 23179283 := bstep (se 1 (by rfl) ⟨17384462, by rfl⟩ : syracuseStep 23179283 = 34768925) B34768925
theorem B15452855 : Blo 2033435 15452855 := bstep (se 1 (by rfl) ⟨11589641, by rfl⟩ : syracuseStep 15452855 = 23179283) B23179283
theorem B10301903 : Blo 2033435 10301903 := bstep (se 1 (by rfl) ⟨7726427, by rfl⟩ : syracuseStep 10301903 = 15452855) B15452855
theorem B6867935 : Blo 2033435 6867935 := bstep (se 1 (by rfl) ⟨5150951, by rfl⟩ : syracuseStep 6867935 = 10301903) B10301903
theorem B4578623 : Blo 2033435 4578623 := bstep (se 1 (by rfl) ⟨3433967, by rfl⟩ : syracuseStep 4578623 = 6867935) B6867935
theorem B3052415 : Blo 2033435 3052415 := bstep (se 1 (by rfl) ⟨2289311, by rfl⟩ : syracuseStep 3052415 = 4578623) B4578623
theorem B2034943 : Blo 2033435 2034943 := bstep (se 1 (by rfl) ⟨1526207, by rfl⟩ : syracuseStep 2034943 = 3052415) B3052415
theorem B3052421 : Blo 2033435 3052421 := bbase (se 4 (by rfl) ⟨286164, by rfl⟩ : syracuseStep 3052421 = 572329) (by norm_num)
theorem B2034947 : Blo 2033435 2034947 := bstep (se 1 (by rfl) ⟨1526210, by rfl⟩ : syracuseStep 2034947 = 3052421) B3052421
theorem B3433981 : Blo 2033435 3433981 := bbase (se 3 (by rfl) ⟨643871, by rfl⟩ : syracuseStep 3433981 = 1287743) (by norm_num)
theorem B4578641 : Blo 2033435 4578641 := bstep (se 2 (by rfl) ⟨1716990, by rfl⟩ : syracuseStep 4578641 = 3433981) B3433981
theorem B3052427 : Blo 2033435 3052427 := bstep (se 1 (by rfl) ⟨2289320, by rfl⟩ : syracuseStep 3052427 = 4578641) B4578641
theorem B2034951 : Blo 2033435 2034951 := bstep (se 1 (by rfl) ⟨1526213, by rfl⟩ : syracuseStep 2034951 = 3052427) B3052427
theorem B2289325 : Blo 2033435 2289325 := bbase (se 3 (by rfl) ⟨429248, by rfl⟩ : syracuseStep 2289325 = 858497) (by norm_num)
theorem B3052433 : Blo 2033435 3052433 := bstep (se 2 (by rfl) ⟨1144662, by rfl⟩ : syracuseStep 3052433 = 2289325) B2289325
theorem B2034955 : Blo 2033435 2034955 := bstep (se 1 (by rfl) ⟨1526216, by rfl⟩ : syracuseStep 2034955 = 3052433) B3052433
theorem B6867989 : Blo 2033435 6867989 := bbase (se 6 (by rfl) ⟨160968, by rfl⟩ : syracuseStep 6867989 = 321937) (by norm_num)
theorem B4578659 : Blo 2033435 4578659 := bstep (se 1 (by rfl) ⟨3433994, by rfl⟩ : syracuseStep 4578659 = 6867989) B6867989
theorem B3052439 : Blo 2033435 3052439 := bstep (se 1 (by rfl) ⟨2289329, by rfl⟩ : syracuseStep 3052439 = 4578659) B4578659
theorem B2034959 : Blo 2033435 2034959 := bstep (se 1 (by rfl) ⟨1526219, by rfl⟩ : syracuseStep 2034959 = 3052439) B3052439
theorem B3052445 : Blo 2033435 3052445 := bbase (se 3 (by rfl) ⟨572333, by rfl⟩ : syracuseStep 3052445 = 1144667) (by norm_num)
theorem B2034963 : Blo 2033435 2034963 := bstep (se 1 (by rfl) ⟨1526222, by rfl⟩ : syracuseStep 2034963 = 3052445) B3052445
theorem B4578677 : Blo 2033435 4578677 := bbase (se 5 (by rfl) ⟨214625, by rfl⟩ : syracuseStep 4578677 = 429251) (by norm_num)
theorem B3052451 : Blo 2033435 3052451 := bstep (se 1 (by rfl) ⟨2289338, by rfl⟩ : syracuseStep 3052451 = 4578677) B4578677
theorem B2034967 : Blo 2033435 2034967 := bstep (se 1 (by rfl) ⟨1526225, by rfl⟩ : syracuseStep 2034967 = 3052451) B3052451
theorem B3480869 : Blo 2033435 3480869 := bbase (se 4 (by rfl) ⟨326331, by rfl⟩ : syracuseStep 3480869 = 652663) (by norm_num)
theorem B2320579 : Blo 2033435 2320579 := bstep (se 1 (by rfl) ⟨1740434, by rfl⟩ : syracuseStep 2320579 = 3480869) B3480869
theorem B3094105 : Blo 2033435 3094105 := bstep (se 2 (by rfl) ⟨1160289, by rfl⟩ : syracuseStep 3094105 = 2320579) B2320579
theorem B4125473 : Blo 2033435 4125473 := bstep (se 2 (by rfl) ⟨1547052, by rfl⟩ : syracuseStep 4125473 = 3094105) B3094105
theorem B2750315 : Blo 2033435 2750315 := bstep (se 1 (by rfl) ⟨2062736, by rfl⟩ : syracuseStep 2750315 = 4125473) B4125473
theorem B7334173 : Blo 2033435 7334173 := bstep (se 3 (by rfl) ⟨1375157, by rfl⟩ : syracuseStep 7334173 = 2750315) B2750315
theorem B9778897 : Blo 2033435 9778897 := bstep (se 2 (by rfl) ⟨3667086, by rfl⟩ : syracuseStep 9778897 = 7334173) B7334173
theorem B13038529 : Blo 2033435 13038529 := bstep (se 2 (by rfl) ⟨4889448, by rfl⟩ : syracuseStep 13038529 = 9778897) B9778897
theorem B17384705 : Blo 2033435 17384705 := bstep (se 2 (by rfl) ⟨6519264, by rfl⟩ : syracuseStep 17384705 = 13038529) B13038529
theorem B11589803 : Blo 2033435 11589803 := bstep (se 1 (by rfl) ⟨8692352, by rfl⟩ : syracuseStep 11589803 = 17384705) B17384705
theorem B7726535 : Blo 2033435 7726535 := bstep (se 1 (by rfl) ⟨5794901, by rfl⟩ : syracuseStep 7726535 = 11589803) B11589803
theorem B5151023 : Blo 2033435 5151023 := bstep (se 1 (by rfl) ⟨3863267, by rfl⟩ : syracuseStep 5151023 = 7726535) B7726535
theorem B3434015 : Blo 2033435 3434015 := bstep (se 1 (by rfl) ⟨2575511, by rfl⟩ : syracuseStep 3434015 = 5151023) B5151023
theorem B2289343 : Blo 2033435 2289343 := bstep (se 1 (by rfl) ⟨1717007, by rfl⟩ : syracuseStep 2289343 = 3434015) B3434015
theorem B3052457 : Blo 2033435 3052457 := bstep (se 2 (by rfl) ⟨1144671, by rfl⟩ : syracuseStep 3052457 = 2289343) B2289343
theorem B2034971 : Blo 2033435 2034971 := bstep (se 1 (by rfl) ⟨1526228, by rfl⟩ : syracuseStep 2034971 = 3052457) B3052457
theorem B7726549 : Blo 2033435 7726549 := bbase (se 7 (by rfl) ⟨90545, by rfl⟩ : syracuseStep 7726549 = 181091) (by norm_num)
theorem B10302065 : Blo 2033435 10302065 := bstep (se 2 (by rfl) ⟨3863274, by rfl⟩ : syracuseStep 10302065 = 7726549) B7726549
theorem B6868043 : Blo 2033435 6868043 := bstep (se 1 (by rfl) ⟨5151032, by rfl⟩ : syracuseStep 6868043 = 10302065) B10302065
theorem B4578695 : Blo 2033435 4578695 := bstep (se 1 (by rfl) ⟨3434021, by rfl⟩ : syracuseStep 4578695 = 6868043) B6868043
theorem B3052463 : Blo 2033435 3052463 := bstep (se 1 (by rfl) ⟨2289347, by rfl⟩ : syracuseStep 3052463 = 4578695) B4578695
theorem B2034975 : Blo 2033435 2034975 := bstep (se 1 (by rfl) ⟨1526231, by rfl⟩ : syracuseStep 2034975 = 3052463) B3052463
theorem B3052469 : Blo 2033435 3052469 := bbase (se 5 (by rfl) ⟨143084, by rfl⟩ : syracuseStep 3052469 = 286169) (by norm_num)
theorem B2034979 : Blo 2033435 2034979 := bstep (se 1 (by rfl) ⟨1526234, by rfl⟩ : syracuseStep 2034979 = 3052469) B3052469
theorem B5151053 : Blo 2033435 5151053 := bbase (se 3 (by rfl) ⟨965822, by rfl⟩ : syracuseStep 5151053 = 1931645) (by norm_num)
theorem B3434035 : Blo 2033435 3434035 := bstep (se 1 (by rfl) ⟨2575526, by rfl⟩ : syracuseStep 3434035 = 5151053) B5151053
theorem B4578713 : Blo 2033435 4578713 := bstep (se 2 (by rfl) ⟨1717017, by rfl⟩ : syracuseStep 4578713 = 3434035) B3434035
theorem B3052475 : Blo 2033435 3052475 := bstep (se 1 (by rfl) ⟨2289356, by rfl⟩ : syracuseStep 3052475 = 4578713) B4578713
theorem B2034983 : Blo 2033435 2034983 := bstep (se 1 (by rfl) ⟨1526237, by rfl⟩ : syracuseStep 2034983 = 3052475) B3052475
theorem B2289361 : Blo 2033435 2289361 := bbase (se 2 (by rfl) ⟨858510, by rfl⟩ : syracuseStep 2289361 = 1717021) (by norm_num)
theorem B3052481 : Blo 2033435 3052481 := bstep (se 2 (by rfl) ⟨1144680, by rfl⟩ : syracuseStep 3052481 = 2289361) B2289361
theorem B2034987 : Blo 2033435 2034987 := bstep (se 1 (by rfl) ⟨1526240, by rfl⟩ : syracuseStep 2034987 = 3052481) B3052481
theorem B2062757 : Blo 2033435 2062757 := bbase (se 4 (by rfl) ⟨193383, by rfl⟩ : syracuseStep 2062757 = 386767) (by norm_num)
theorem B5500685 : Blo 2033435 5500685 := bstep (se 3 (by rfl) ⟨1031378, by rfl⟩ : syracuseStep 5500685 = 2062757) B2062757
theorem B3667123 : Blo 2033435 3667123 := bstep (se 1 (by rfl) ⟨2750342, by rfl⟩ : syracuseStep 3667123 = 5500685) B5500685
theorem B4889497 : Blo 2033435 4889497 := bstep (se 2 (by rfl) ⟨1833561, by rfl⟩ : syracuseStep 4889497 = 3667123) B3667123
theorem B6519329 : Blo 2033435 6519329 := bstep (se 2 (by rfl) ⟨2444748, by rfl⟩ : syracuseStep 6519329 = 4889497) B4889497
theorem B4346219 : Blo 2033435 4346219 := bstep (se 1 (by rfl) ⟨3259664, by rfl⟩ : syracuseStep 4346219 = 6519329) B6519329
theorem B2897479 : Blo 2033435 2897479 := bstep (se 1 (by rfl) ⟨2173109, by rfl⟩ : syracuseStep 2897479 = 4346219) B4346219
theorem B3863305 : Blo 2033435 3863305 := bstep (se 2 (by rfl) ⟨1448739, by rfl⟩ : syracuseStep 3863305 = 2897479) B2897479
theorem B5151073 : Blo 2033435 5151073 := bstep (se 2 (by rfl) ⟨1931652, by rfl⟩ : syracuseStep 5151073 = 3863305) B3863305
theorem B6868097 : Blo 2033435 6868097 := bstep (se 2 (by rfl) ⟨2575536, by rfl⟩ : syracuseStep 6868097 = 5151073) B5151073
theorem B4578731 : Blo 2033435 4578731 := bstep (se 1 (by rfl) ⟨3434048, by rfl⟩ : syracuseStep 4578731 = 6868097) B6868097
theorem B3052487 : Blo 2033435 3052487 := bstep (se 1 (by rfl) ⟨2289365, by rfl⟩ : syracuseStep 3052487 = 4578731) B4578731
theorem B2034991 : Blo 2033435 2034991 := bstep (se 1 (by rfl) ⟨1526243, by rfl⟩ : syracuseStep 2034991 = 3052487) B3052487
theorem B3052493 : Blo 2033435 3052493 := bbase (se 3 (by rfl) ⟨572342, by rfl⟩ : syracuseStep 3052493 = 1144685) (by norm_num)
theorem B2034995 : Blo 2033435 2034995 := bstep (se 1 (by rfl) ⟨1526246, by rfl⟩ : syracuseStep 2034995 = 3052493) B3052493
theorem B4578749 : Blo 2033435 4578749 := bbase (se 3 (by rfl) ⟨858515, by rfl⟩ : syracuseStep 4578749 = 1717031) (by norm_num)
theorem B3052499 : Blo 2033435 3052499 := bstep (se 1 (by rfl) ⟨2289374, by rfl⟩ : syracuseStep 3052499 = 4578749) B4578749
theorem B2034999 : Blo 2033435 2034999 := bstep (se 1 (by rfl) ⟨1526249, by rfl⟩ : syracuseStep 2034999 = 3052499) B3052499
theorem B3434069 : Blo 2033435 3434069 := bbase (se 8 (by rfl) ⟨20121, by rfl⟩ : syracuseStep 3434069 = 40243) (by norm_num)
theorem B2289379 : Blo 2033435 2289379 := bstep (se 1 (by rfl) ⟨1717034, by rfl⟩ : syracuseStep 2289379 = 3434069) B3434069
theorem B3052505 : Blo 2033435 3052505 := bstep (se 2 (by rfl) ⟨1144689, by rfl⟩ : syracuseStep 3052505 = 2289379) B2289379
theorem B2035003 : Blo 2033435 2035003 := bstep (se 1 (by rfl) ⟨1526252, by rfl⟩ : syracuseStep 2035003 = 3052505) B3052505
theorem B10442789 : Blo 2033435 10442789 := bbase (se 4 (by rfl) ⟨979011, by rfl⟩ : syracuseStep 10442789 = 1958023) (by norm_num)
theorem B6961859 : Blo 2033435 6961859 := bstep (se 1 (by rfl) ⟨5221394, by rfl⟩ : syracuseStep 6961859 = 10442789) B10442789
theorem B4641239 : Blo 2033435 4641239 := bstep (se 1 (by rfl) ⟨3480929, by rfl⟩ : syracuseStep 4641239 = 6961859) B6961859
theorem B12376637 : Blo 2033435 12376637 := bstep (se 3 (by rfl) ⟨2320619, by rfl⟩ : syracuseStep 12376637 = 4641239) B4641239
theorem B8251091 : Blo 2033435 8251091 := bstep (se 1 (by rfl) ⟨6188318, by rfl⟩ : syracuseStep 8251091 = 12376637) B12376637
theorem B5500727 : Blo 2033435 5500727 := bstep (se 1 (by rfl) ⟨4125545, by rfl⟩ : syracuseStep 5500727 = 8251091) B8251091
theorem B3667151 : Blo 2033435 3667151 := bstep (se 1 (by rfl) ⟨2750363, by rfl⟩ : syracuseStep 3667151 = 5500727) B5500727
theorem B9779069 : Blo 2033435 9779069 := bstep (se 3 (by rfl) ⟨1833575, by rfl⟩ : syracuseStep 9779069 = 3667151) B3667151
theorem B6519379 : Blo 2033435 6519379 := bstep (se 1 (by rfl) ⟨4889534, by rfl⟩ : syracuseStep 6519379 = 9779069) B9779069
theorem B8692505 : Blo 2033435 8692505 := bstep (se 2 (by rfl) ⟨3259689, by rfl⟩ : syracuseStep 8692505 = 6519379) B6519379
theorem B5795003 : Blo 2033435 5795003 := bstep (se 1 (by rfl) ⟨4346252, by rfl⟩ : syracuseStep 5795003 = 8692505) B8692505
theorem B15453341 : Blo 2033435 15453341 := bstep (se 3 (by rfl) ⟨2897501, by rfl⟩ : syracuseStep 15453341 = 5795003) B5795003
theorem B10302227 : Blo 2033435 10302227 := bstep (se 1 (by rfl) ⟨7726670, by rfl⟩ : syracuseStep 10302227 = 15453341) B15453341
theorem B6868151 : Blo 2033435 6868151 := bstep (se 1 (by rfl) ⟨5151113, by rfl⟩ : syracuseStep 6868151 = 10302227) B10302227
theorem B4578767 : Blo 2033435 4578767 := bstep (se 1 (by rfl) ⟨3434075, by rfl⟩ : syracuseStep 4578767 = 6868151) B6868151
theorem B3052511 : Blo 2033435 3052511 := bstep (se 1 (by rfl) ⟨2289383, by rfl⟩ : syracuseStep 3052511 = 4578767) B4578767
theorem B2035007 : Blo 2033435 2035007 := bstep (se 1 (by rfl) ⟨1526255, by rfl⟩ : syracuseStep 2035007 = 3052511) B3052511
theorem B3052517 : Blo 2033435 3052517 := bbase (se 4 (by rfl) ⟨286173, by rfl⟩ : syracuseStep 3052517 = 572347) (by norm_num)
theorem B2035011 : Blo 2033435 2035011 := bstep (se 1 (by rfl) ⟨1526258, by rfl⟩ : syracuseStep 2035011 = 3052517) B3052517
theorem B2787901 : Blo 2033435 2787901 := bbase (se 3 (by rfl) ⟨522731, by rfl⟩ : syracuseStep 2787901 = 1045463) (by norm_num)
theorem B14868805 : Blo 2033435 14868805 := bstep (se 4 (by rfl) ⟨1393950, by rfl⟩ : syracuseStep 14868805 = 2787901) B2787901
theorem B19825073 : Blo 2033435 19825073 := bstep (se 2 (by rfl) ⟨7434402, by rfl⟩ : syracuseStep 19825073 = 14868805) B14868805
theorem B13216715 : Blo 2033435 13216715 := bstep (se 1 (by rfl) ⟨9912536, by rfl⟩ : syracuseStep 13216715 = 19825073) B19825073
theorem B8811143 : Blo 2033435 8811143 := bstep (se 1 (by rfl) ⟨6608357, by rfl⟩ : syracuseStep 8811143 = 13216715) B13216715
theorem B5874095 : Blo 2033435 5874095 := bstep (se 1 (by rfl) ⟨4405571, by rfl⟩ : syracuseStep 5874095 = 8811143) B8811143
theorem B3916063 : Blo 2033435 3916063 := bstep (se 1 (by rfl) ⟨2937047, by rfl⟩ : syracuseStep 3916063 = 5874095) B5874095
theorem B5221417 : Blo 2033435 5221417 := bstep (se 2 (by rfl) ⟨1958031, by rfl⟩ : syracuseStep 5221417 = 3916063) B3916063
theorem B6961889 : Blo 2033435 6961889 := bstep (se 2 (by rfl) ⟨2610708, by rfl⟩ : syracuseStep 6961889 = 5221417) B5221417
theorem B4641259 : Blo 2033435 4641259 := bstep (se 1 (by rfl) ⟨3480944, by rfl⟩ : syracuseStep 4641259 = 6961889) B6961889
theorem B6188345 : Blo 2033435 6188345 := bstep (se 2 (by rfl) ⟨2320629, by rfl⟩ : syracuseStep 6188345 = 4641259) B4641259
theorem B4125563 : Blo 2033435 4125563 := bstep (se 1 (by rfl) ⟨3094172, by rfl⟩ : syracuseStep 4125563 = 6188345) B6188345
theorem B2750375 : Blo 2033435 2750375 := bstep (se 1 (by rfl) ⟨2062781, by rfl⟩ : syracuseStep 2750375 = 4125563) B4125563
theorem B7334333 : Blo 2033435 7334333 := bstep (se 3 (by rfl) ⟨1375187, by rfl⟩ : syracuseStep 7334333 = 2750375) B2750375
theorem B4889555 : Blo 2033435 4889555 := bstep (se 1 (by rfl) ⟨3667166, by rfl⟩ : syracuseStep 4889555 = 7334333) B7334333
theorem B3259703 : Blo 2033435 3259703 := bstep (se 1 (by rfl) ⟨2444777, by rfl⟩ : syracuseStep 3259703 = 4889555) B4889555
theorem B8692541 : Blo 2033435 8692541 := bstep (se 3 (by rfl) ⟨1629851, by rfl⟩ : syracuseStep 8692541 = 3259703) B3259703
theorem B5795027 : Blo 2033435 5795027 := bstep (se 1 (by rfl) ⟨4346270, by rfl⟩ : syracuseStep 5795027 = 8692541) B8692541
theorem B3863351 : Blo 2033435 3863351 := bstep (se 1 (by rfl) ⟨2897513, by rfl⟩ : syracuseStep 3863351 = 5795027) B5795027
theorem B2575567 : Blo 2033435 2575567 := bstep (se 1 (by rfl) ⟨1931675, by rfl⟩ : syracuseStep 2575567 = 3863351) B3863351
theorem B3434089 : Blo 2033435 3434089 := bstep (se 2 (by rfl) ⟨1287783, by rfl⟩ : syracuseStep 3434089 = 2575567) B2575567
theorem B4578785 : Blo 2033435 4578785 := bstep (se 2 (by rfl) ⟨1717044, by rfl⟩ : syracuseStep 4578785 = 3434089) B3434089
theorem B3052523 : Blo 2033435 3052523 := bstep (se 1 (by rfl) ⟨2289392, by rfl⟩ : syracuseStep 3052523 = 4578785) B4578785
theorem B2035015 : Blo 2033435 2035015 := bstep (se 1 (by rfl) ⟨1526261, by rfl⟩ : syracuseStep 2035015 = 3052523) B3052523
theorem B2289397 : Blo 2033435 2289397 := bbase (se 5 (by rfl) ⟨107315, by rfl⟩ : syracuseStep 2289397 = 214631) (by norm_num)
theorem B3052529 : Blo 2033435 3052529 := bstep (se 2 (by rfl) ⟨1144698, by rfl⟩ : syracuseStep 3052529 = 2289397) B2289397
theorem B2035019 : Blo 2033435 2035019 := bstep (se 1 (by rfl) ⟨1526264, by rfl⟩ : syracuseStep 2035019 = 3052529) B3052529
theorem B2575577 : Blo 2033435 2575577 := bbase (se 2 (by rfl) ⟨965841, by rfl⟩ : syracuseStep 2575577 = 1931683) (by norm_num)
theorem B6868205 : Blo 2033435 6868205 := bstep (se 3 (by rfl) ⟨1287788, by rfl⟩ : syracuseStep 6868205 = 2575577) B2575577
theorem B4578803 : Blo 2033435 4578803 := bstep (se 1 (by rfl) ⟨3434102, by rfl⟩ : syracuseStep 4578803 = 6868205) B6868205
theorem B3052535 : Blo 2033435 3052535 := bstep (se 1 (by rfl) ⟨2289401, by rfl⟩ : syracuseStep 3052535 = 4578803) B4578803
theorem B2035023 : Blo 2033435 2035023 := bstep (se 1 (by rfl) ⟨1526267, by rfl⟩ : syracuseStep 2035023 = 3052535) B3052535
theorem B3052541 : Blo 2033435 3052541 := bbase (se 3 (by rfl) ⟨572351, by rfl⟩ : syracuseStep 3052541 = 1144703) (by norm_num)
theorem B2035027 : Blo 2033435 2035027 := bstep (se 1 (by rfl) ⟨1526270, by rfl⟩ : syracuseStep 2035027 = 3052541) B3052541
theorem B4578821 : Blo 2033435 4578821 := bbase (se 4 (by rfl) ⟨429264, by rfl⟩ : syracuseStep 4578821 = 858529) (by norm_num)
theorem B3052547 : Blo 2033435 3052547 := bstep (se 1 (by rfl) ⟨2289410, by rfl⟩ : syracuseStep 3052547 = 4578821) B4578821
theorem B2035031 : Blo 2033435 2035031 := bstep (se 1 (by rfl) ⟨1526273, by rfl⟩ : syracuseStep 2035031 = 3052547) B3052547
theorem B3863389 : Blo 2033435 3863389 := bbase (se 3 (by rfl) ⟨724385, by rfl⟩ : syracuseStep 3863389 = 1448771) (by norm_num)
theorem B5151185 : Blo 2033435 5151185 := bstep (se 2 (by rfl) ⟨1931694, by rfl⟩ : syracuseStep 5151185 = 3863389) B3863389
theorem B3434123 : Blo 2033435 3434123 := bstep (se 1 (by rfl) ⟨2575592, by rfl⟩ : syracuseStep 3434123 = 5151185) B5151185
theorem B2289415 : Blo 2033435 2289415 := bstep (se 1 (by rfl) ⟨1717061, by rfl⟩ : syracuseStep 2289415 = 3434123) B3434123
theorem B3052553 : Blo 2033435 3052553 := bstep (se 2 (by rfl) ⟨1144707, by rfl⟩ : syracuseStep 3052553 = 2289415) B2289415
theorem B2035035 : Blo 2033435 2035035 := bstep (se 1 (by rfl) ⟨1526276, by rfl⟩ : syracuseStep 2035035 = 3052553) B3052553
theorem B10302389 : Blo 2033435 10302389 := bbase (se 5 (by rfl) ⟨482924, by rfl⟩ : syracuseStep 10302389 = 965849) (by norm_num)
theorem B6868259 : Blo 2033435 6868259 := bstep (se 1 (by rfl) ⟨5151194, by rfl⟩ : syracuseStep 6868259 = 10302389) B10302389
theorem B4578839 : Blo 2033435 4578839 := bstep (se 1 (by rfl) ⟨3434129, by rfl⟩ : syracuseStep 4578839 = 6868259) B6868259
theorem B3052559 : Blo 2033435 3052559 := bstep (se 1 (by rfl) ⟨2289419, by rfl⟩ : syracuseStep 3052559 = 4578839) B4578839
theorem B2035039 : Blo 2033435 2035039 := bstep (se 1 (by rfl) ⟨1526279, by rfl⟩ : syracuseStep 2035039 = 3052559) B3052559
theorem B3052565 : Blo 2033435 3052565 := bbase (se 6 (by rfl) ⟨71544, by rfl⟩ : syracuseStep 3052565 = 143089) (by norm_num)
theorem B2035043 : Blo 2033435 2035043 := bstep (se 1 (by rfl) ⟨1526282, by rfl⟩ : syracuseStep 2035043 = 3052565) B3052565
theorem B13923989 : Blo 2033435 13923989 := bbase (se 6 (by rfl) ⟨326343, by rfl⟩ : syracuseStep 13923989 = 652687) (by norm_num)
theorem B9282659 : Blo 2033435 9282659 := bstep (se 1 (by rfl) ⟨6961994, by rfl⟩ : syracuseStep 9282659 = 13923989) B13923989
theorem B24753757 : Blo 2033435 24753757 := bstep (se 3 (by rfl) ⟨4641329, by rfl⟩ : syracuseStep 24753757 = 9282659) B9282659
theorem B33005009 : Blo 2033435 33005009 := bstep (se 2 (by rfl) ⟨12376878, by rfl⟩ : syracuseStep 33005009 = 24753757) B24753757
theorem B22003339 : Blo 2033435 22003339 := bstep (se 1 (by rfl) ⟨16502504, by rfl⟩ : syracuseStep 22003339 = 33005009) B33005009
theorem B29337785 : Blo 2033435 29337785 := bstep (se 2 (by rfl) ⟨11001669, by rfl⟩ : syracuseStep 29337785 = 22003339) B22003339
theorem B19558523 : Blo 2033435 19558523 := bstep (se 1 (by rfl) ⟨14668892, by rfl⟩ : syracuseStep 19558523 = 29337785) B29337785
theorem B13039015 : Blo 2033435 13039015 := bstep (se 1 (by rfl) ⟨9779261, by rfl⟩ : syracuseStep 13039015 = 19558523) B19558523
theorem B17385353 : Blo 2033435 17385353 := bstep (se 2 (by rfl) ⟨6519507, by rfl⟩ : syracuseStep 17385353 = 13039015) B13039015
theorem B11590235 : Blo 2033435 11590235 := bstep (se 1 (by rfl) ⟨8692676, by rfl⟩ : syracuseStep 11590235 = 17385353) B17385353
theorem B7726823 : Blo 2033435 7726823 := bstep (se 1 (by rfl) ⟨5795117, by rfl⟩ : syracuseStep 7726823 = 11590235) B11590235
theorem B5151215 : Blo 2033435 5151215 := bstep (se 1 (by rfl) ⟨3863411, by rfl⟩ : syracuseStep 5151215 = 7726823) B7726823
theorem B3434143 : Blo 2033435 3434143 := bstep (se 1 (by rfl) ⟨2575607, by rfl⟩ : syracuseStep 3434143 = 5151215) B5151215
theorem B4578857 : Blo 2033435 4578857 := bstep (se 2 (by rfl) ⟨1717071, by rfl⟩ : syracuseStep 4578857 = 3434143) B3434143
theorem B3052571 : Blo 2033435 3052571 := bstep (se 1 (by rfl) ⟨2289428, by rfl⟩ : syracuseStep 3052571 = 4578857) B4578857
theorem B2035047 : Blo 2033435 2035047 := bstep (se 1 (by rfl) ⟨1526285, by rfl⟩ : syracuseStep 2035047 = 3052571) B3052571
theorem B2289433 : Blo 2033435 2289433 := bbase (se 2 (by rfl) ⟨858537, by rfl⟩ : syracuseStep 2289433 = 1717075) (by norm_num)
theorem B3052577 : Blo 2033435 3052577 := bstep (se 2 (by rfl) ⟨1144716, by rfl⟩ : syracuseStep 3052577 = 2289433) B2289433
theorem B2035051 : Blo 2033435 2035051 := bstep (se 1 (by rfl) ⟨1526288, by rfl⟩ : syracuseStep 2035051 = 3052577) B3052577
theorem B7726853 : Blo 2033435 7726853 := bbase (se 4 (by rfl) ⟨724392, by rfl⟩ : syracuseStep 7726853 = 1448785) (by norm_num)
theorem B5151235 : Blo 2033435 5151235 := bstep (se 1 (by rfl) ⟨3863426, by rfl⟩ : syracuseStep 5151235 = 7726853) B7726853
theorem B6868313 : Blo 2033435 6868313 := bstep (se 2 (by rfl) ⟨2575617, by rfl⟩ : syracuseStep 6868313 = 5151235) B5151235
theorem B4578875 : Blo 2033435 4578875 := bstep (se 1 (by rfl) ⟨3434156, by rfl⟩ : syracuseStep 4578875 = 6868313) B6868313
theorem B3052583 : Blo 2033435 3052583 := bstep (se 1 (by rfl) ⟨2289437, by rfl⟩ : syracuseStep 3052583 = 4578875) B4578875
theorem B2035055 : Blo 2033435 2035055 := bstep (se 1 (by rfl) ⟨1526291, by rfl⟩ : syracuseStep 2035055 = 3052583) B3052583
theorem B3052589 : Blo 2033435 3052589 := bbase (se 3 (by rfl) ⟨572360, by rfl⟩ : syracuseStep 3052589 = 1144721) (by norm_num)
theorem B2035059 : Blo 2033435 2035059 := bstep (se 1 (by rfl) ⟨1526294, by rfl⟩ : syracuseStep 2035059 = 3052589) B3052589
theorem B4578893 : Blo 2033435 4578893 := bbase (se 3 (by rfl) ⟨858542, by rfl⟩ : syracuseStep 4578893 = 1717085) (by norm_num)
theorem B3052595 : Blo 2033435 3052595 := bstep (se 1 (by rfl) ⟨2289446, by rfl⟩ : syracuseStep 3052595 = 4578893) B4578893
theorem B2035063 : Blo 2033435 2035063 := bstep (se 1 (by rfl) ⟨1526297, by rfl⟩ : syracuseStep 2035063 = 3052595) B3052595
theorem B2575633 : Blo 2033435 2575633 := bbase (se 2 (by rfl) ⟨965862, by rfl⟩ : syracuseStep 2575633 = 1931725) (by norm_num)
theorem B3434177 : Blo 2033435 3434177 := bstep (se 2 (by rfl) ⟨1287816, by rfl⟩ : syracuseStep 3434177 = 2575633) B2575633
theorem B2289451 : Blo 2033435 2289451 := bstep (se 1 (by rfl) ⟨1717088, by rfl⟩ : syracuseStep 2289451 = 3434177) B3434177
theorem B3052601 : Blo 2033435 3052601 := bstep (se 2 (by rfl) ⟨1144725, by rfl⟩ : syracuseStep 3052601 = 2289451) B2289451
theorem B2035067 : Blo 2033435 2035067 := bstep (se 1 (by rfl) ⟨1526300, by rfl⟩ : syracuseStep 2035067 = 3052601) B3052601
theorem B4346389 : Blo 2033435 4346389 := bbase (se 6 (by rfl) ⟨101868, by rfl⟩ : syracuseStep 4346389 = 203737) (by norm_num)
theorem B23180741 : Blo 2033435 23180741 := bstep (se 4 (by rfl) ⟨2173194, by rfl⟩ : syracuseStep 23180741 = 4346389) B4346389
theorem B15453827 : Blo 2033435 15453827 := bstep (se 1 (by rfl) ⟨11590370, by rfl⟩ : syracuseStep 15453827 = 23180741) B23180741
theorem B10302551 : Blo 2033435 10302551 := bstep (se 1 (by rfl) ⟨7726913, by rfl⟩ : syracuseStep 10302551 = 15453827) B15453827
theorem B6868367 : Blo 2033435 6868367 := bstep (se 1 (by rfl) ⟨5151275, by rfl⟩ : syracuseStep 6868367 = 10302551) B10302551
theorem B4578911 : Blo 2033435 4578911 := bstep (se 1 (by rfl) ⟨3434183, by rfl⟩ : syracuseStep 4578911 = 6868367) B6868367
theorem B3052607 : Blo 2033435 3052607 := bstep (se 1 (by rfl) ⟨2289455, by rfl⟩ : syracuseStep 3052607 = 4578911) B4578911
theorem B2035071 : Blo 2033435 2035071 := bstep (se 1 (by rfl) ⟨1526303, by rfl⟩ : syracuseStep 2035071 = 3052607) B3052607
theorem B3052613 : Blo 2033435 3052613 := bbase (se 4 (by rfl) ⟨286182, by rfl⟩ : syracuseStep 3052613 = 572365) (by norm_num)
theorem B2035075 : Blo 2033435 2035075 := bstep (se 1 (by rfl) ⟨1526306, by rfl⟩ : syracuseStep 2035075 = 3052613) B3052613
theorem B3434197 : Blo 2033435 3434197 := bbase (se 7 (by rfl) ⟨40244, by rfl⟩ : syracuseStep 3434197 = 80489) (by norm_num)
theorem B4578929 : Blo 2033435 4578929 := bstep (se 2 (by rfl) ⟨1717098, by rfl⟩ : syracuseStep 4578929 = 3434197) B3434197
theorem B3052619 : Blo 2033435 3052619 := bstep (se 1 (by rfl) ⟨2289464, by rfl⟩ : syracuseStep 3052619 = 4578929) B4578929
theorem B2035079 : Blo 2033435 2035079 := bstep (se 1 (by rfl) ⟨1526309, by rfl⟩ : syracuseStep 2035079 = 3052619) B3052619
theorem B2289469 : Blo 2033435 2289469 := bbase (se 3 (by rfl) ⟨429275, by rfl⟩ : syracuseStep 2289469 = 858551) (by norm_num)
theorem B3052625 : Blo 2033435 3052625 := bstep (se 2 (by rfl) ⟨1144734, by rfl⟩ : syracuseStep 3052625 = 2289469) B2289469
theorem B2035083 : Blo 2033435 2035083 := bstep (se 1 (by rfl) ⟨1526312, by rfl⟩ : syracuseStep 2035083 = 3052625) B3052625
theorem B6868421 : Blo 2033435 6868421 := bbase (se 4 (by rfl) ⟨643914, by rfl⟩ : syracuseStep 6868421 = 1287829) (by norm_num)
theorem B4578947 : Blo 2033435 4578947 := bstep (se 1 (by rfl) ⟨3434210, by rfl⟩ : syracuseStep 4578947 = 6868421) B6868421
theorem B3052631 : Blo 2033435 3052631 := bstep (se 1 (by rfl) ⟨2289473, by rfl⟩ : syracuseStep 3052631 = 4578947) B4578947
theorem B2035087 : Blo 2033435 2035087 := bstep (se 1 (by rfl) ⟨1526315, by rfl⟩ : syracuseStep 2035087 = 3052631) B3052631
theorem B3052637 : Blo 2033435 3052637 := bbase (se 3 (by rfl) ⟨572369, by rfl⟩ : syracuseStep 3052637 = 1144739) (by norm_num)
theorem B2035091 : Blo 2033435 2035091 := bstep (se 1 (by rfl) ⟨1526318, by rfl⟩ : syracuseStep 2035091 = 3052637) B3052637
theorem B4578965 : Blo 2033435 4578965 := bbase (se 6 (by rfl) ⟨107319, by rfl⟩ : syracuseStep 4578965 = 214639) (by norm_num)
theorem B3052643 : Blo 2033435 3052643 := bstep (se 1 (by rfl) ⟨2289482, by rfl⟩ : syracuseStep 3052643 = 4578965) B4578965
theorem B2035095 : Blo 2033435 2035095 := bstep (se 1 (by rfl) ⟨1526321, by rfl⟩ : syracuseStep 2035095 = 3052643) B3052643
theorem B2173225 : Blo 2033435 2173225 := bbase (se 2 (by rfl) ⟨814959, by rfl⟩ : syracuseStep 2173225 = 1629919) (by norm_num)
theorem B2897633 : Blo 2033435 2897633 := bstep (se 2 (by rfl) ⟨1086612, by rfl⟩ : syracuseStep 2897633 = 2173225) B2173225
theorem B7727021 : Blo 2033435 7727021 := bstep (se 3 (by rfl) ⟨1448816, by rfl⟩ : syracuseStep 7727021 = 2897633) B2897633
theorem B5151347 : Blo 2033435 5151347 := bstep (se 1 (by rfl) ⟨3863510, by rfl⟩ : syracuseStep 5151347 = 7727021) B7727021
theorem B3434231 : Blo 2033435 3434231 := bstep (se 1 (by rfl) ⟨2575673, by rfl⟩ : syracuseStep 3434231 = 5151347) B5151347
theorem B2289487 : Blo 2033435 2289487 := bstep (se 1 (by rfl) ⟨1717115, by rfl⟩ : syracuseStep 2289487 = 3434231) B3434231
theorem B3052649 : Blo 2033435 3052649 := bstep (se 2 (by rfl) ⟨1144743, by rfl⟩ : syracuseStep 3052649 = 2289487) B2289487
theorem B2035099 : Blo 2033435 2035099 := bstep (se 1 (by rfl) ⟨1526324, by rfl⟩ : syracuseStep 2035099 = 3052649) B3052649
theorem B4889765 : Blo 2033435 4889765 := bbase (se 4 (by rfl) ⟨458415, by rfl⟩ : syracuseStep 4889765 = 916831) (by norm_num)
theorem B13039373 : Blo 2033435 13039373 := bstep (se 3 (by rfl) ⟨2444882, by rfl⟩ : syracuseStep 13039373 = 4889765) B4889765
theorem B8692915 : Blo 2033435 8692915 := bstep (se 1 (by rfl) ⟨6519686, by rfl⟩ : syracuseStep 8692915 = 13039373) B13039373
theorem B11590553 : Blo 2033435 11590553 := bstep (se 2 (by rfl) ⟨4346457, by rfl⟩ : syracuseStep 11590553 = 8692915) B8692915
theorem B7727035 : Blo 2033435 7727035 := bstep (se 1 (by rfl) ⟨5795276, by rfl⟩ : syracuseStep 7727035 = 11590553) B11590553
theorem B10302713 : Blo 2033435 10302713 := bstep (se 2 (by rfl) ⟨3863517, by rfl⟩ : syracuseStep 10302713 = 7727035) B7727035
theorem B6868475 : Blo 2033435 6868475 := bstep (se 1 (by rfl) ⟨5151356, by rfl⟩ : syracuseStep 6868475 = 10302713) B10302713
theorem B4578983 : Blo 2033435 4578983 := bstep (se 1 (by rfl) ⟨3434237, by rfl⟩ : syracuseStep 4578983 = 6868475) B6868475
theorem B3052655 : Blo 2033435 3052655 := bstep (se 1 (by rfl) ⟨2289491, by rfl⟩ : syracuseStep 3052655 = 4578983) B4578983
theorem B2035103 : Blo 2033435 2035103 := bstep (se 1 (by rfl) ⟨1526327, by rfl⟩ : syracuseStep 2035103 = 3052655) B3052655
theorem B3052661 : Blo 2033435 3052661 := bbase (se 5 (by rfl) ⟨143093, by rfl⟩ : syracuseStep 3052661 = 286187) (by norm_num)
theorem B2035107 : Blo 2033435 2035107 := bstep (se 1 (by rfl) ⟨1526330, by rfl⟩ : syracuseStep 2035107 = 3052661) B3052661
theorem B3863533 : Blo 2033435 3863533 := bbase (se 3 (by rfl) ⟨724412, by rfl⟩ : syracuseStep 3863533 = 1448825) (by norm_num)
theorem B5151377 : Blo 2033435 5151377 := bstep (se 2 (by rfl) ⟨1931766, by rfl⟩ : syracuseStep 5151377 = 3863533) B3863533
theorem B3434251 : Blo 2033435 3434251 := bstep (se 1 (by rfl) ⟨2575688, by rfl⟩ : syracuseStep 3434251 = 5151377) B5151377
theorem B4579001 : Blo 2033435 4579001 := bstep (se 2 (by rfl) ⟨1717125, by rfl⟩ : syracuseStep 4579001 = 3434251) B3434251
theorem B3052667 : Blo 2033435 3052667 := bstep (se 1 (by rfl) ⟨2289500, by rfl⟩ : syracuseStep 3052667 = 4579001) B4579001
theorem B2035111 : Blo 2033435 2035111 := bstep (se 1 (by rfl) ⟨1526333, by rfl⟩ : syracuseStep 2035111 = 3052667) B3052667
theorem B2289505 : Blo 2033435 2289505 := bbase (se 2 (by rfl) ⟨858564, by rfl⟩ : syracuseStep 2289505 = 1717129) (by norm_num)
theorem B3052673 : Blo 2033435 3052673 := bstep (se 2 (by rfl) ⟨1144752, by rfl⟩ : syracuseStep 3052673 = 2289505) B2289505
theorem B2035115 : Blo 2033435 2035115 := bstep (se 1 (by rfl) ⟨1526336, by rfl⟩ : syracuseStep 2035115 = 3052673) B3052673
theorem B5151397 : Blo 2033435 5151397 := bbase (se 4 (by rfl) ⟨482943, by rfl⟩ : syracuseStep 5151397 = 965887) (by norm_num)
theorem B6868529 : Blo 2033435 6868529 := bstep (se 2 (by rfl) ⟨2575698, by rfl⟩ : syracuseStep 6868529 = 5151397) B5151397
theorem B4579019 : Blo 2033435 4579019 := bstep (se 1 (by rfl) ⟨3434264, by rfl⟩ : syracuseStep 4579019 = 6868529) B6868529
theorem B3052679 : Blo 2033435 3052679 := bstep (se 1 (by rfl) ⟨2289509, by rfl⟩ : syracuseStep 3052679 = 4579019) B4579019
theorem B2035119 : Blo 2033435 2035119 := bstep (se 1 (by rfl) ⟨1526339, by rfl⟩ : syracuseStep 2035119 = 3052679) B3052679
theorem B3052685 : Blo 2033435 3052685 := bbase (se 3 (by rfl) ⟨572378, by rfl⟩ : syracuseStep 3052685 = 1144757) (by norm_num)
theorem B2035123 : Blo 2033435 2035123 := bstep (se 1 (by rfl) ⟨1526342, by rfl⟩ : syracuseStep 2035123 = 3052685) B3052685
theorem B4579037 : Blo 2033435 4579037 := bbase (se 3 (by rfl) ⟨858569, by rfl⟩ : syracuseStep 4579037 = 1717139) (by norm_num)
theorem B3052691 : Blo 2033435 3052691 := bstep (se 1 (by rfl) ⟨2289518, by rfl⟩ : syracuseStep 3052691 = 4579037) B4579037
theorem B2035127 : Blo 2033435 2035127 := bstep (se 1 (by rfl) ⟨1526345, by rfl⟩ : syracuseStep 2035127 = 3052691) B3052691
theorem B3434285 : Blo 2033435 3434285 := bbase (se 3 (by rfl) ⟨643928, by rfl⟩ : syracuseStep 3434285 = 1287857) (by norm_num)
theorem B2289523 : Blo 2033435 2289523 := bstep (se 1 (by rfl) ⟨1717142, by rfl⟩ : syracuseStep 2289523 = 3434285) B3434285
theorem B3052697 : Blo 2033435 3052697 := bstep (se 2 (by rfl) ⟨1144761, by rfl⟩ : syracuseStep 3052697 = 2289523) B2289523
theorem B2035131 : Blo 2033435 2035131 := bstep (se 1 (by rfl) ⟨1526348, by rfl⟩ : syracuseStep 2035131 = 3052697) B3052697
theorem B14669525 : Blo 2033435 14669525 := bbase (se 7 (by rfl) ⟨171908, by rfl⟩ : syracuseStep 14669525 = 343817) (by norm_num)
theorem B39118733 : Blo 2033435 39118733 := bstep (se 3 (by rfl) ⟨7334762, by rfl⟩ : syracuseStep 39118733 = 14669525) B14669525
theorem B26079155 : Blo 2033435 26079155 := bstep (se 1 (by rfl) ⟨19559366, by rfl⟩ : syracuseStep 26079155 = 39118733) B39118733
theorem B17386103 : Blo 2033435 17386103 := bstep (se 1 (by rfl) ⟨13039577, by rfl⟩ : syracuseStep 17386103 = 26079155) B26079155
theorem B11590735 : Blo 2033435 11590735 := bstep (se 1 (by rfl) ⟨8693051, by rfl⟩ : syracuseStep 11590735 = 17386103) B17386103
theorem B15454313 : Blo 2033435 15454313 := bstep (se 2 (by rfl) ⟨5795367, by rfl⟩ : syracuseStep 15454313 = 11590735) B11590735
theorem B10302875 : Blo 2033435 10302875 := bstep (se 1 (by rfl) ⟨7727156, by rfl⟩ : syracuseStep 10302875 = 15454313) B15454313
theorem B6868583 : Blo 2033435 6868583 := bstep (se 1 (by rfl) ⟨5151437, by rfl⟩ : syracuseStep 6868583 = 10302875) B10302875
theorem B4579055 : Blo 2033435 4579055 := bstep (se 1 (by rfl) ⟨3434291, by rfl⟩ : syracuseStep 4579055 = 6868583) B6868583
theorem B3052703 : Blo 2033435 3052703 := bstep (se 1 (by rfl) ⟨2289527, by rfl⟩ : syracuseStep 3052703 = 4579055) B4579055
theorem B2035135 : Blo 2033435 2035135 := bstep (se 1 (by rfl) ⟨1526351, by rfl⟩ : syracuseStep 2035135 = 3052703) B3052703
theorem B3052709 : Blo 2033435 3052709 := bbase (se 4 (by rfl) ⟨286191, by rfl⟩ : syracuseStep 3052709 = 572383) (by norm_num)
theorem B2035139 : Blo 2033435 2035139 := bstep (se 1 (by rfl) ⟨1526354, by rfl⟩ : syracuseStep 2035139 = 3052709) B3052709
theorem B2575729 : Blo 2033435 2575729 := bbase (se 2 (by rfl) ⟨965898, by rfl⟩ : syracuseStep 2575729 = 1931797) (by norm_num)
theorem B3434305 : Blo 2033435 3434305 := bstep (se 2 (by rfl) ⟨1287864, by rfl⟩ : syracuseStep 3434305 = 2575729) B2575729
theorem B4579073 : Blo 2033435 4579073 := bstep (se 2 (by rfl) ⟨1717152, by rfl⟩ : syracuseStep 4579073 = 3434305) B3434305
theorem B3052715 : Blo 2033435 3052715 := bstep (se 1 (by rfl) ⟨2289536, by rfl⟩ : syracuseStep 3052715 = 4579073) B4579073
theorem B2035143 : Blo 2033435 2035143 := bstep (se 1 (by rfl) ⟨1526357, by rfl⟩ : syracuseStep 2035143 = 3052715) B3052715
theorem B2289541 : Blo 2033435 2289541 := bbase (se 4 (by rfl) ⟨214644, by rfl⟩ : syracuseStep 2289541 = 429289) (by norm_num)
theorem B3052721 : Blo 2033435 3052721 := bstep (se 2 (by rfl) ⟨1144770, by rfl⟩ : syracuseStep 3052721 = 2289541) B2289541
theorem B2035147 : Blo 2033435 2035147 := bstep (se 1 (by rfl) ⟨1526360, by rfl⟩ : syracuseStep 2035147 = 3052721) B3052721
theorem B2444941 : Blo 2033435 2444941 := bbase (se 3 (by rfl) ⟨458426, by rfl⟩ : syracuseStep 2444941 = 916853) (by norm_num)
theorem B3259921 : Blo 2033435 3259921 := bstep (se 2 (by rfl) ⟨1222470, by rfl⟩ : syracuseStep 3259921 = 2444941) B2444941
theorem B4346561 : Blo 2033435 4346561 := bstep (se 2 (by rfl) ⟨1629960, by rfl⟩ : syracuseStep 4346561 = 3259921) B3259921
theorem B2897707 : Blo 2033435 2897707 := bstep (se 1 (by rfl) ⟨2173280, by rfl⟩ : syracuseStep 2897707 = 4346561) B4346561
theorem B3863609 : Blo 2033435 3863609 := bstep (se 2 (by rfl) ⟨1448853, by rfl⟩ : syracuseStep 3863609 = 2897707) B2897707
theorem B2575739 : Blo 2033435 2575739 := bstep (se 1 (by rfl) ⟨1931804, by rfl⟩ : syracuseStep 2575739 = 3863609) B3863609
theorem B6868637 : Blo 2033435 6868637 := bstep (se 3 (by rfl) ⟨1287869, by rfl⟩ : syracuseStep 6868637 = 2575739) B2575739
theorem B4579091 : Blo 2033435 4579091 := bstep (se 1 (by rfl) ⟨3434318, by rfl⟩ : syracuseStep 4579091 = 6868637) B6868637
theorem B3052727 : Blo 2033435 3052727 := bstep (se 1 (by rfl) ⟨2289545, by rfl⟩ : syracuseStep 3052727 = 4579091) B4579091
theorem B2035151 : Blo 2033435 2035151 := bstep (se 1 (by rfl) ⟨1526363, by rfl⟩ : syracuseStep 2035151 = 3052727) B3052727
theorem B3052733 : Blo 2033435 3052733 := bbase (se 3 (by rfl) ⟨572387, by rfl⟩ : syracuseStep 3052733 = 1144775) (by norm_num)
theorem B2035155 : Blo 2033435 2035155 := bstep (se 1 (by rfl) ⟨1526366, by rfl⟩ : syracuseStep 2035155 = 3052733) B3052733
theorem B4579109 : Blo 2033435 4579109 := bbase (se 4 (by rfl) ⟨429291, by rfl⟩ : syracuseStep 4579109 = 858583) (by norm_num)
theorem B3052739 : Blo 2033435 3052739 := bstep (se 1 (by rfl) ⟨2289554, by rfl⟩ : syracuseStep 3052739 = 4579109) B4579109
theorem B2035159 : Blo 2033435 2035159 := bstep (se 1 (by rfl) ⟨1526369, by rfl⟩ : syracuseStep 2035159 = 3052739) B3052739
theorem B5151509 : Blo 2033435 5151509 := bbase (se 6 (by rfl) ⟨120738, by rfl⟩ : syracuseStep 5151509 = 241477) (by norm_num)
theorem B3434339 : Blo 2033435 3434339 := bstep (se 1 (by rfl) ⟨2575754, by rfl⟩ : syracuseStep 3434339 = 5151509) B5151509
theorem B2289559 : Blo 2033435 2289559 := bstep (se 1 (by rfl) ⟨1717169, by rfl⟩ : syracuseStep 2289559 = 3434339) B3434339
theorem B3052745 : Blo 2033435 3052745 := bstep (se 2 (by rfl) ⟨1144779, by rfl⟩ : syracuseStep 3052745 = 2289559) B2289559
theorem B2035163 : Blo 2033435 2035163 := bstep (se 1 (by rfl) ⟨1526372, by rfl⟩ : syracuseStep 2035163 = 3052745) B3052745
theorem B8693189 : Blo 2033435 8693189 := bbase (se 4 (by rfl) ⟨814986, by rfl⟩ : syracuseStep 8693189 = 1629973) (by norm_num)
theorem B5795459 : Blo 2033435 5795459 := bstep (se 1 (by rfl) ⟨4346594, by rfl⟩ : syracuseStep 5795459 = 8693189) B8693189
theorem B3863639 : Blo 2033435 3863639 := bstep (se 1 (by rfl) ⟨2897729, by rfl⟩ : syracuseStep 3863639 = 5795459) B5795459
theorem B10303037 : Blo 2033435 10303037 := bstep (se 3 (by rfl) ⟨1931819, by rfl⟩ : syracuseStep 10303037 = 3863639) B3863639
theorem B6868691 : Blo 2033435 6868691 := bstep (se 1 (by rfl) ⟨5151518, by rfl⟩ : syracuseStep 6868691 = 10303037) B10303037
theorem B4579127 : Blo 2033435 4579127 := bstep (se 1 (by rfl) ⟨3434345, by rfl⟩ : syracuseStep 4579127 = 6868691) B6868691
theorem B3052751 : Blo 2033435 3052751 := bstep (se 1 (by rfl) ⟨2289563, by rfl⟩ : syracuseStep 3052751 = 4579127) B4579127
theorem B2035167 : Blo 2033435 2035167 := bstep (se 1 (by rfl) ⟨1526375, by rfl⟩ : syracuseStep 2035167 = 3052751) B3052751
theorem B3052757 : Blo 2033435 3052757 := bbase (se 7 (by rfl) ⟨35774, by rfl⟩ : syracuseStep 3052757 = 71549) (by norm_num)
theorem B2035171 : Blo 2033435 2035171 := bstep (se 1 (by rfl) ⟨1526378, by rfl⟩ : syracuseStep 2035171 = 3052757) B3052757
theorem B2897741 : Blo 2033435 2897741 := bbase (se 3 (by rfl) ⟨543326, by rfl⟩ : syracuseStep 2897741 = 1086653) (by norm_num)
theorem B7727309 : Blo 2033435 7727309 := bstep (se 3 (by rfl) ⟨1448870, by rfl⟩ : syracuseStep 7727309 = 2897741) B2897741
theorem B5151539 : Blo 2033435 5151539 := bstep (se 1 (by rfl) ⟨3863654, by rfl⟩ : syracuseStep 5151539 = 7727309) B7727309
theorem B3434359 : Blo 2033435 3434359 := bstep (se 1 (by rfl) ⟨2575769, by rfl⟩ : syracuseStep 3434359 = 5151539) B5151539
theorem B4579145 : Blo 2033435 4579145 := bstep (se 2 (by rfl) ⟨1717179, by rfl⟩ : syracuseStep 4579145 = 3434359) B3434359
theorem B3052763 : Blo 2033435 3052763 := bstep (se 1 (by rfl) ⟨2289572, by rfl⟩ : syracuseStep 3052763 = 4579145) B4579145
theorem B2035175 : Blo 2033435 2035175 := bstep (se 1 (by rfl) ⟨1526381, by rfl⟩ : syracuseStep 2035175 = 3052763) B3052763
theorem B2289577 : Blo 2033435 2289577 := bbase (se 2 (by rfl) ⟨858591, by rfl⟩ : syracuseStep 2289577 = 1717183) (by norm_num)
theorem B3052769 : Blo 2033435 3052769 := bstep (se 2 (by rfl) ⟨1144788, by rfl⟩ : syracuseStep 3052769 = 2289577) B2289577
theorem B2035179 : Blo 2033435 2035179 := bstep (se 1 (by rfl) ⟨1526384, by rfl⟩ : syracuseStep 2035179 = 3052769) B3052769
theorem B4956677 : Blo 2033435 4956677 := bbase (se 4 (by rfl) ⟨464688, by rfl⟩ : syracuseStep 4956677 = 929377) (by norm_num)
theorem B3304451 : Blo 2033435 3304451 := bstep (se 1 (by rfl) ⟨2478338, by rfl⟩ : syracuseStep 3304451 = 4956677) B4956677
theorem B2202967 : Blo 2033435 2202967 := bstep (se 1 (by rfl) ⟨1652225, by rfl⟩ : syracuseStep 2202967 = 3304451) B3304451
theorem B11749157 : Blo 2033435 11749157 := bstep (se 4 (by rfl) ⟨1101483, by rfl⟩ : syracuseStep 11749157 = 2202967) B2202967
theorem B7832771 : Blo 2033435 7832771 := bstep (se 1 (by rfl) ⟨5874578, by rfl⟩ : syracuseStep 7832771 = 11749157) B11749157
theorem B5221847 : Blo 2033435 5221847 := bstep (se 1 (by rfl) ⟨3916385, by rfl⟩ : syracuseStep 5221847 = 7832771) B7832771
theorem B3481231 : Blo 2033435 3481231 := bstep (se 1 (by rfl) ⟨2610923, by rfl⟩ : syracuseStep 3481231 = 5221847) B5221847
theorem B4641641 : Blo 2033435 4641641 := bstep (se 2 (by rfl) ⟨1740615, by rfl⟩ : syracuseStep 4641641 = 3481231) B3481231
theorem B3094427 : Blo 2033435 3094427 := bstep (se 1 (by rfl) ⟨2320820, by rfl⟩ : syracuseStep 3094427 = 4641641) B4641641
theorem B2062951 : Blo 2033435 2062951 := bstep (se 1 (by rfl) ⟨1547213, by rfl⟩ : syracuseStep 2062951 = 3094427) B3094427
theorem B11002405 : Blo 2033435 11002405 := bstep (se 4 (by rfl) ⟨1031475, by rfl⟩ : syracuseStep 11002405 = 2062951) B2062951
theorem B14669873 : Blo 2033435 14669873 := bstep (se 2 (by rfl) ⟨5501202, by rfl⟩ : syracuseStep 14669873 = 11002405) B11002405
theorem B9779915 : Blo 2033435 9779915 := bstep (se 1 (by rfl) ⟨7334936, by rfl⟩ : syracuseStep 9779915 = 14669873) B14669873
theorem B6519943 : Blo 2033435 6519943 := bstep (se 1 (by rfl) ⟨4889957, by rfl⟩ : syracuseStep 6519943 = 9779915) B9779915
theorem B8693257 : Blo 2033435 8693257 := bstep (se 2 (by rfl) ⟨3259971, by rfl⟩ : syracuseStep 8693257 = 6519943) B6519943
theorem B11591009 : Blo 2033435 11591009 := bstep (se 2 (by rfl) ⟨4346628, by rfl⟩ : syracuseStep 11591009 = 8693257) B8693257
theorem B7727339 : Blo 2033435 7727339 := bstep (se 1 (by rfl) ⟨5795504, by rfl⟩ : syracuseStep 7727339 = 11591009) B11591009
theorem B5151559 : Blo 2033435 5151559 := bstep (se 1 (by rfl) ⟨3863669, by rfl⟩ : syracuseStep 5151559 = 7727339) B7727339
theorem B6868745 : Blo 2033435 6868745 := bstep (se 2 (by rfl) ⟨2575779, by rfl⟩ : syracuseStep 6868745 = 5151559) B5151559
theorem B4579163 : Blo 2033435 4579163 := bstep (se 1 (by rfl) ⟨3434372, by rfl⟩ : syracuseStep 4579163 = 6868745) B6868745
theorem B3052775 : Blo 2033435 3052775 := bstep (se 1 (by rfl) ⟨2289581, by rfl⟩ : syracuseStep 3052775 = 4579163) B4579163
theorem B2035183 : Blo 2033435 2035183 := bstep (se 1 (by rfl) ⟨1526387, by rfl⟩ : syracuseStep 2035183 = 3052775) B3052775
theorem B3052781 : Blo 2033435 3052781 := bbase (se 3 (by rfl) ⟨572396, by rfl⟩ : syracuseStep 3052781 = 1144793) (by norm_num)
theorem B2035187 : Blo 2033435 2035187 := bstep (se 1 (by rfl) ⟨1526390, by rfl⟩ : syracuseStep 2035187 = 3052781) B3052781
theorem B4579181 : Blo 2033435 4579181 := bbase (se 3 (by rfl) ⟨858596, by rfl⟩ : syracuseStep 4579181 = 1717193) (by norm_num)
theorem B3052787 : Blo 2033435 3052787 := bstep (se 1 (by rfl) ⟨2289590, by rfl⟩ : syracuseStep 3052787 = 4579181) B4579181
theorem B2035191 : Blo 2033435 2035191 := bstep (se 1 (by rfl) ⟨1526393, by rfl⟩ : syracuseStep 2035191 = 3052787) B3052787
theorem B3863693 : Blo 2033435 3863693 := bbase (se 3 (by rfl) ⟨724442, by rfl⟩ : syracuseStep 3863693 = 1448885) (by norm_num)
theorem B2575795 : Blo 2033435 2575795 := bstep (se 1 (by rfl) ⟨1931846, by rfl⟩ : syracuseStep 2575795 = 3863693) B3863693
theorem B3434393 : Blo 2033435 3434393 := bstep (se 2 (by rfl) ⟨1287897, by rfl⟩ : syracuseStep 3434393 = 2575795) B2575795
theorem B2289595 : Blo 2033435 2289595 := bstep (se 1 (by rfl) ⟨1717196, by rfl⟩ : syracuseStep 2289595 = 3434393) B3434393
theorem B3052793 : Blo 2033435 3052793 := bstep (se 2 (by rfl) ⟨1144797, by rfl⟩ : syracuseStep 3052793 = 2289595) B2289595
theorem B2035195 : Blo 2033435 2035195 := bstep (se 1 (by rfl) ⟨1526396, by rfl⟩ : syracuseStep 2035195 = 3052793) B3052793
theorem B4641677 : Blo 2033435 4641677 := bbase (se 3 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 4641677 = 1740629) (by norm_num)
theorem B3094451 : Blo 2033435 3094451 := bstep (se 1 (by rfl) ⟨2320838, by rfl⟩ : syracuseStep 3094451 = 4641677) B4641677
theorem B2062967 : Blo 2033435 2062967 := bstep (se 1 (by rfl) ⟨1547225, by rfl⟩ : syracuseStep 2062967 = 3094451) B3094451
theorem B5501245 : Blo 2033435 5501245 := bstep (se 3 (by rfl) ⟨1031483, by rfl⟩ : syracuseStep 5501245 = 2062967) B2062967
theorem B7334993 : Blo 2033435 7334993 := bstep (se 2 (by rfl) ⟨2750622, by rfl⟩ : syracuseStep 7334993 = 5501245) B5501245
theorem B19559981 : Blo 2033435 19559981 := bstep (se 3 (by rfl) ⟨3667496, by rfl⟩ : syracuseStep 19559981 = 7334993) B7334993
theorem B52159949 : Blo 2033435 52159949 := bstep (se 3 (by rfl) ⟨9779990, by rfl⟩ : syracuseStep 52159949 = 19559981) B19559981
theorem B34773299 : Blo 2033435 34773299 := bstep (se 1 (by rfl) ⟨26079974, by rfl⟩ : syracuseStep 34773299 = 52159949) B52159949
theorem B23182199 : Blo 2033435 23182199 := bstep (se 1 (by rfl) ⟨17386649, by rfl⟩ : syracuseStep 23182199 = 34773299) B34773299
theorem B15454799 : Blo 2033435 15454799 := bstep (se 1 (by rfl) ⟨11591099, by rfl⟩ : syracuseStep 15454799 = 23182199) B23182199
theorem B10303199 : Blo 2033435 10303199 := bstep (se 1 (by rfl) ⟨7727399, by rfl⟩ : syracuseStep 10303199 = 15454799) B15454799
theorem B6868799 : Blo 2033435 6868799 := bstep (se 1 (by rfl) ⟨5151599, by rfl⟩ : syracuseStep 6868799 = 10303199) B10303199
theorem B4579199 : Blo 2033435 4579199 := bstep (se 1 (by rfl) ⟨3434399, by rfl⟩ : syracuseStep 4579199 = 6868799) B6868799
theorem B3052799 : Blo 2033435 3052799 := bstep (se 1 (by rfl) ⟨2289599, by rfl⟩ : syracuseStep 3052799 = 4579199) B4579199
theorem B2035199 : Blo 2033435 2035199 := bstep (se 1 (by rfl) ⟨1526399, by rfl⟩ : syracuseStep 2035199 = 3052799) B3052799
theorem B3052805 : Blo 2033435 3052805 := bbase (se 4 (by rfl) ⟨286200, by rfl⟩ : syracuseStep 3052805 = 572401) (by norm_num)
theorem B2035203 : Blo 2033435 2035203 := bstep (se 1 (by rfl) ⟨1526402, by rfl⟩ : syracuseStep 2035203 = 3052805) B3052805
theorem B3434413 : Blo 2033435 3434413 := bbase (se 3 (by rfl) ⟨643952, by rfl⟩ : syracuseStep 3434413 = 1287905) (by norm_num)
theorem B4579217 : Blo 2033435 4579217 := bstep (se 2 (by rfl) ⟨1717206, by rfl⟩ : syracuseStep 4579217 = 3434413) B3434413
theorem B3052811 : Blo 2033435 3052811 := bstep (se 1 (by rfl) ⟨2289608, by rfl⟩ : syracuseStep 3052811 = 4579217) B4579217
theorem B2035207 : Blo 2033435 2035207 := bstep (se 1 (by rfl) ⟨1526405, by rfl⟩ : syracuseStep 2035207 = 3052811) B3052811
theorem B2289613 : Blo 2033435 2289613 := bbase (se 3 (by rfl) ⟨429302, by rfl⟩ : syracuseStep 2289613 = 858605) (by norm_num)
theorem B3052817 : Blo 2033435 3052817 := bstep (se 2 (by rfl) ⟨1144806, by rfl⟩ : syracuseStep 3052817 = 2289613) B2289613
theorem B2035211 : Blo 2033435 2035211 := bstep (se 1 (by rfl) ⟨1526408, by rfl⟩ : syracuseStep 2035211 = 3052817) B3052817
theorem B6868853 : Blo 2033435 6868853 := bbase (se 5 (by rfl) ⟨321977, by rfl⟩ : syracuseStep 6868853 = 643955) (by norm_num)
theorem B4579235 : Blo 2033435 4579235 := bstep (se 1 (by rfl) ⟨3434426, by rfl⟩ : syracuseStep 4579235 = 6868853) B6868853
theorem B3052823 : Blo 2033435 3052823 := bstep (se 1 (by rfl) ⟨2289617, by rfl⟩ : syracuseStep 3052823 = 4579235) B4579235
theorem B2035215 : Blo 2033435 2035215 := bstep (se 1 (by rfl) ⟨1526411, by rfl⟩ : syracuseStep 2035215 = 3052823) B3052823
theorem B3052829 : Blo 2033435 3052829 := bbase (se 3 (by rfl) ⟨572405, by rfl⟩ : syracuseStep 3052829 = 1144811) (by norm_num)
theorem B2035219 : Blo 2033435 2035219 := bstep (se 1 (by rfl) ⟨1526414, by rfl⟩ : syracuseStep 2035219 = 3052829) B3052829
theorem B4579253 : Blo 2033435 4579253 := bbase (se 5 (by rfl) ⟨214652, by rfl⟩ : syracuseStep 4579253 = 429305) (by norm_num)
theorem B3052835 : Blo 2033435 3052835 := bstep (se 1 (by rfl) ⟨2289626, by rfl⟩ : syracuseStep 3052835 = 4579253) B4579253
theorem B2035223 : Blo 2033435 2035223 := bstep (se 1 (by rfl) ⟨1526417, by rfl⟩ : syracuseStep 2035223 = 3052835) B3052835
theorem B6520085 : Blo 2033435 6520085 := bbase (se 6 (by rfl) ⟨152814, by rfl⟩ : syracuseStep 6520085 = 305629) (by norm_num)
theorem B4346723 : Blo 2033435 4346723 := bstep (se 1 (by rfl) ⟨3260042, by rfl⟩ : syracuseStep 4346723 = 6520085) B6520085
theorem B11591261 : Blo 2033435 11591261 := bstep (se 3 (by rfl) ⟨2173361, by rfl⟩ : syracuseStep 11591261 = 4346723) B4346723
theorem B7727507 : Blo 2033435 7727507 := bstep (se 1 (by rfl) ⟨5795630, by rfl⟩ : syracuseStep 7727507 = 11591261) B11591261
theorem B5151671 : Blo 2033435 5151671 := bstep (se 1 (by rfl) ⟨3863753, by rfl⟩ : syracuseStep 5151671 = 7727507) B7727507
theorem B3434447 : Blo 2033435 3434447 := bstep (se 1 (by rfl) ⟨2575835, by rfl⟩ : syracuseStep 3434447 = 5151671) B5151671
theorem B2289631 : Blo 2033435 2289631 := bstep (se 1 (by rfl) ⟨1717223, by rfl⟩ : syracuseStep 2289631 = 3434447) B3434447
theorem B3052841 : Blo 2033435 3052841 := bstep (se 2 (by rfl) ⟨1144815, by rfl⟩ : syracuseStep 3052841 = 2289631) B2289631
theorem B2035227 : Blo 2033435 2035227 := bstep (se 1 (by rfl) ⟨1526420, by rfl⟩ : syracuseStep 2035227 = 3052841) B3052841
theorem B5501333 : Blo 2033435 5501333 := bbase (se 6 (by rfl) ⟨128937, by rfl⟩ : syracuseStep 5501333 = 257875) (by norm_num)
theorem B3667555 : Blo 2033435 3667555 := bstep (se 1 (by rfl) ⟨2750666, by rfl⟩ : syracuseStep 3667555 = 5501333) B5501333
theorem B4890073 : Blo 2033435 4890073 := bstep (se 2 (by rfl) ⟨1833777, by rfl⟩ : syracuseStep 4890073 = 3667555) B3667555
theorem B6520097 : Blo 2033435 6520097 := bstep (se 2 (by rfl) ⟨2445036, by rfl⟩ : syracuseStep 6520097 = 4890073) B4890073
theorem B4346731 : Blo 2033435 4346731 := bstep (se 1 (by rfl) ⟨3260048, by rfl⟩ : syracuseStep 4346731 = 6520097) B6520097
theorem B5795641 : Blo 2033435 5795641 := bstep (se 2 (by rfl) ⟨2173365, by rfl⟩ : syracuseStep 5795641 = 4346731) B4346731
theorem B7727521 : Blo 2033435 7727521 := bstep (se 2 (by rfl) ⟨2897820, by rfl⟩ : syracuseStep 7727521 = 5795641) B5795641
theorem B10303361 : Blo 2033435 10303361 := bstep (se 2 (by rfl) ⟨3863760, by rfl⟩ : syracuseStep 10303361 = 7727521) B7727521
theorem B6868907 : Blo 2033435 6868907 := bstep (se 1 (by rfl) ⟨5151680, by rfl⟩ : syracuseStep 6868907 = 10303361) B10303361
theorem B4579271 : Blo 2033435 4579271 := bstep (se 1 (by rfl) ⟨3434453, by rfl⟩ : syracuseStep 4579271 = 6868907) B6868907
theorem B3052847 : Blo 2033435 3052847 := bstep (se 1 (by rfl) ⟨2289635, by rfl⟩ : syracuseStep 3052847 = 4579271) B4579271
theorem B2035231 : Blo 2033435 2035231 := bstep (se 1 (by rfl) ⟨1526423, by rfl⟩ : syracuseStep 2035231 = 3052847) B3052847
theorem B3052853 : Blo 2033435 3052853 := bbase (se 5 (by rfl) ⟨143102, by rfl⟩ : syracuseStep 3052853 = 286205) (by norm_num)
theorem B2035235 : Blo 2033435 2035235 := bstep (se 1 (by rfl) ⟨1526426, by rfl⟩ : syracuseStep 2035235 = 3052853) B3052853
theorem B5151701 : Blo 2033435 5151701 := bbase (se 7 (by rfl) ⟨60371, by rfl⟩ : syracuseStep 5151701 = 120743) (by norm_num)
theorem B3434467 : Blo 2033435 3434467 := bstep (se 1 (by rfl) ⟨2575850, by rfl⟩ : syracuseStep 3434467 = 5151701) B5151701
theorem B4579289 : Blo 2033435 4579289 := bstep (se 2 (by rfl) ⟨1717233, by rfl⟩ : syracuseStep 4579289 = 3434467) B3434467
theorem B3052859 : Blo 2033435 3052859 := bstep (se 1 (by rfl) ⟨2289644, by rfl⟩ : syracuseStep 3052859 = 4579289) B4579289
theorem B2035239 : Blo 2033435 2035239 := bstep (se 1 (by rfl) ⟨1526429, by rfl⟩ : syracuseStep 2035239 = 3052859) B3052859
theorem B2289649 : Blo 2033435 2289649 := bbase (se 2 (by rfl) ⟨858618, by rfl⟩ : syracuseStep 2289649 = 1717237) (by norm_num)
theorem B3052865 : Blo 2033435 3052865 := bstep (se 2 (by rfl) ⟨1144824, by rfl⟩ : syracuseStep 3052865 = 2289649) B2289649
theorem B2035243 : Blo 2033435 2035243 := bstep (se 1 (by rfl) ⟨1526432, by rfl⟩ : syracuseStep 2035243 = 3052865) B3052865
theorem B2512229 : Blo 2033435 2512229 := bbase (se 4 (by rfl) ⟨235521, by rfl⟩ : syracuseStep 2512229 = 471043) (by norm_num)
theorem B6699277 : Blo 2033435 6699277 := bstep (se 3 (by rfl) ⟨1256114, by rfl⟩ : syracuseStep 6699277 = 2512229) B2512229
theorem B8932369 : Blo 2033435 8932369 := bstep (se 2 (by rfl) ⟨3349638, by rfl⟩ : syracuseStep 8932369 = 6699277) B6699277
theorem B11909825 : Blo 2033435 11909825 := bstep (se 2 (by rfl) ⟨4466184, by rfl⟩ : syracuseStep 11909825 = 8932369) B8932369
theorem B7939883 : Blo 2033435 7939883 := bstep (se 1 (by rfl) ⟨5954912, by rfl⟩ : syracuseStep 7939883 = 11909825) B11909825
theorem B21173021 : Blo 2033435 21173021 := bstep (se 3 (by rfl) ⟨3969941, by rfl⟩ : syracuseStep 21173021 = 7939883) B7939883
theorem B14115347 : Blo 2033435 14115347 := bstep (se 1 (by rfl) ⟨10586510, by rfl⟩ : syracuseStep 14115347 = 21173021) B21173021
theorem B9410231 : Blo 2033435 9410231 := bstep (se 1 (by rfl) ⟨7057673, by rfl⟩ : syracuseStep 9410231 = 14115347) B14115347
theorem B6273487 : Blo 2033435 6273487 := bstep (se 1 (by rfl) ⟨4705115, by rfl⟩ : syracuseStep 6273487 = 9410231) B9410231
theorem B33458597 : Blo 2033435 33458597 := bstep (se 4 (by rfl) ⟨3136743, by rfl⟩ : syracuseStep 33458597 = 6273487) B6273487
theorem B22305731 : Blo 2033435 22305731 := bstep (se 1 (by rfl) ⟨16729298, by rfl⟩ : syracuseStep 22305731 = 33458597) B33458597
theorem B237927797 : Blo 2033435 237927797 := bstep (se 5 (by rfl) ⟨11152865, by rfl⟩ : syracuseStep 237927797 = 22305731) B22305731
theorem B158618531 : Blo 2033435 158618531 := bstep (se 1 (by rfl) ⟨118963898, by rfl⟩ : syracuseStep 158618531 = 237927797) B237927797
theorem B422982749 : Blo 2033435 422982749 := bstep (se 3 (by rfl) ⟨79309265, by rfl⟩ : syracuseStep 422982749 = 158618531) B158618531
theorem B281988499 : Blo 2033435 281988499 := bstep (se 1 (by rfl) ⟨211491374, by rfl⟩ : syracuseStep 281988499 = 422982749) B422982749
theorem B375984665 : Blo 2033435 375984665 := bstep (se 2 (by rfl) ⟨140994249, by rfl⟩ : syracuseStep 375984665 = 281988499) B281988499
theorem B250656443 : Blo 2033435 250656443 := bstep (se 1 (by rfl) ⟨187992332, by rfl⟩ : syracuseStep 250656443 = 375984665) B375984665
theorem B167104295 : Blo 2033435 167104295 := bstep (se 1 (by rfl) ⟨125328221, by rfl⟩ : syracuseStep 167104295 = 250656443) B250656443
theorem B111402863 : Blo 2033435 111402863 := bstep (se 1 (by rfl) ⟨83552147, by rfl⟩ : syracuseStep 111402863 = 167104295) B167104295
theorem B74268575 : Blo 2033435 74268575 := bstep (se 1 (by rfl) ⟨55701431, by rfl⟩ : syracuseStep 74268575 = 111402863) B111402863
theorem B49512383 : Blo 2033435 49512383 := bstep (se 1 (by rfl) ⟨37134287, by rfl⟩ : syracuseStep 49512383 = 74268575) B74268575
theorem B33008255 : Blo 2033435 33008255 := bstep (se 1 (by rfl) ⟨24756191, by rfl⟩ : syracuseStep 33008255 = 49512383) B49512383
theorem B22005503 : Blo 2033435 22005503 := bstep (se 1 (by rfl) ⟨16504127, by rfl⟩ : syracuseStep 22005503 = 33008255) B33008255
theorem B14670335 : Blo 2033435 14670335 := bstep (se 1 (by rfl) ⟨11002751, by rfl⟩ : syracuseStep 14670335 = 22005503) B22005503
theorem B9780223 : Blo 2033435 9780223 := bstep (se 1 (by rfl) ⟨7335167, by rfl⟩ : syracuseStep 9780223 = 14670335) B14670335
theorem B13040297 : Blo 2033435 13040297 := bstep (se 2 (by rfl) ⟨4890111, by rfl⟩ : syracuseStep 13040297 = 9780223) B9780223
theorem B8693531 : Blo 2033435 8693531 := bstep (se 1 (by rfl) ⟨6520148, by rfl⟩ : syracuseStep 8693531 = 13040297) B13040297
theorem B5795687 : Blo 2033435 5795687 := bstep (se 1 (by rfl) ⟨4346765, by rfl⟩ : syracuseStep 5795687 = 8693531) B8693531
theorem B3863791 : Blo 2033435 3863791 := bstep (se 1 (by rfl) ⟨2897843, by rfl⟩ : syracuseStep 3863791 = 5795687) B5795687
theorem B5151721 : Blo 2033435 5151721 := bstep (se 2 (by rfl) ⟨1931895, by rfl⟩ : syracuseStep 5151721 = 3863791) B3863791
theorem B6868961 : Blo 2033435 6868961 := bstep (se 2 (by rfl) ⟨2575860, by rfl⟩ : syracuseStep 6868961 = 5151721) B5151721
theorem B4579307 : Blo 2033435 4579307 := bstep (se 1 (by rfl) ⟨3434480, by rfl⟩ : syracuseStep 4579307 = 6868961) B6868961
theorem B3052871 : Blo 2033435 3052871 := bstep (se 1 (by rfl) ⟨2289653, by rfl⟩ : syracuseStep 3052871 = 4579307) B4579307
theorem B2035247 : Blo 2033435 2035247 := bstep (se 1 (by rfl) ⟨1526435, by rfl⟩ : syracuseStep 2035247 = 3052871) B3052871
theorem B3052877 : Blo 2033435 3052877 := bbase (se 3 (by rfl) ⟨572414, by rfl⟩ : syracuseStep 3052877 = 1144829) (by norm_num)
theorem B2035251 : Blo 2033435 2035251 := bstep (se 1 (by rfl) ⟨1526438, by rfl⟩ : syracuseStep 2035251 = 3052877) B3052877
theorem B4579325 : Blo 2033435 4579325 := bbase (se 3 (by rfl) ⟨858623, by rfl⟩ : syracuseStep 4579325 = 1717247) (by norm_num)
theorem B3052883 : Blo 2033435 3052883 := bstep (se 1 (by rfl) ⟨2289662, by rfl⟩ : syracuseStep 3052883 = 4579325) B4579325
theorem B2035255 : Blo 2033435 2035255 := bstep (se 1 (by rfl) ⟨1526441, by rfl⟩ : syracuseStep 2035255 = 3052883) B3052883
theorem B3434501 : Blo 2033435 3434501 := bbase (se 4 (by rfl) ⟨321984, by rfl⟩ : syracuseStep 3434501 = 643969) (by norm_num)
theorem B2289667 : Blo 2033435 2289667 := bstep (se 1 (by rfl) ⟨1717250, by rfl⟩ : syracuseStep 2289667 = 3434501) B3434501
theorem B3052889 : Blo 2033435 3052889 := bstep (se 2 (by rfl) ⟨1144833, by rfl⟩ : syracuseStep 3052889 = 2289667) B2289667
theorem B2035259 : Blo 2033435 2035259 := bstep (se 1 (by rfl) ⟨1526444, by rfl⟩ : syracuseStep 2035259 = 3052889) B3052889
theorem B15455285 : Blo 2033435 15455285 := bbase (se 5 (by rfl) ⟨724466, by rfl⟩ : syracuseStep 15455285 = 1448933) (by norm_num)
theorem B10303523 : Blo 2033435 10303523 := bstep (se 1 (by rfl) ⟨7727642, by rfl⟩ : syracuseStep 10303523 = 15455285) B15455285
theorem B6869015 : Blo 2033435 6869015 := bstep (se 1 (by rfl) ⟨5151761, by rfl⟩ : syracuseStep 6869015 = 10303523) B10303523
theorem B4579343 : Blo 2033435 4579343 := bstep (se 1 (by rfl) ⟨3434507, by rfl⟩ : syracuseStep 4579343 = 6869015) B6869015
theorem B3052895 : Blo 2033435 3052895 := bstep (se 1 (by rfl) ⟨2289671, by rfl⟩ : syracuseStep 3052895 = 4579343) B4579343
theorem B2035263 : Blo 2033435 2035263 := bstep (se 1 (by rfl) ⟨1526447, by rfl⟩ : syracuseStep 2035263 = 3052895) B3052895
theorem B3052901 : Blo 2033435 3052901 := bbase (se 4 (by rfl) ⟨286209, by rfl⟩ : syracuseStep 3052901 = 572419) (by norm_num)
theorem B2035267 : Blo 2033435 2035267 := bstep (se 1 (by rfl) ⟨1526450, by rfl⟩ : syracuseStep 2035267 = 3052901) B3052901
theorem B3863837 : Blo 2033435 3863837 := bbase (se 3 (by rfl) ⟨724469, by rfl⟩ : syracuseStep 3863837 = 1448939) (by norm_num)
theorem B2575891 : Blo 2033435 2575891 := bstep (se 1 (by rfl) ⟨1931918, by rfl⟩ : syracuseStep 2575891 = 3863837) B3863837
theorem B3434521 : Blo 2033435 3434521 := bstep (se 2 (by rfl) ⟨1287945, by rfl⟩ : syracuseStep 3434521 = 2575891) B2575891
theorem B4579361 : Blo 2033435 4579361 := bstep (se 2 (by rfl) ⟨1717260, by rfl⟩ : syracuseStep 4579361 = 3434521) B3434521
theorem B3052907 : Blo 2033435 3052907 := bstep (se 1 (by rfl) ⟨2289680, by rfl⟩ : syracuseStep 3052907 = 4579361) B4579361
theorem B2035271 : Blo 2033435 2035271 := bstep (se 1 (by rfl) ⟨1526453, by rfl⟩ : syracuseStep 2035271 = 3052907) B3052907
theorem B2289685 : Blo 2033435 2289685 := bbase (se 6 (by rfl) ⟨53664, by rfl⟩ : syracuseStep 2289685 = 107329) (by norm_num)
theorem B3052913 : Blo 2033435 3052913 := bstep (se 2 (by rfl) ⟨1144842, by rfl⟩ : syracuseStep 3052913 = 2289685) B2289685
theorem B2035275 : Blo 2033435 2035275 := bstep (se 1 (by rfl) ⟨1526456, by rfl⟩ : syracuseStep 2035275 = 3052913) B3052913
theorem B2575901 : Blo 2033435 2575901 := bbase (se 3 (by rfl) ⟨482981, by rfl⟩ : syracuseStep 2575901 = 965963) (by norm_num)
theorem B6869069 : Blo 2033435 6869069 := bstep (se 3 (by rfl) ⟨1287950, by rfl⟩ : syracuseStep 6869069 = 2575901) B2575901
theorem B4579379 : Blo 2033435 4579379 := bstep (se 1 (by rfl) ⟨3434534, by rfl⟩ : syracuseStep 4579379 = 6869069) B6869069
theorem B3052919 : Blo 2033435 3052919 := bstep (se 1 (by rfl) ⟨2289689, by rfl⟩ : syracuseStep 3052919 = 4579379) B4579379
theorem B2035279 : Blo 2033435 2035279 := bstep (se 1 (by rfl) ⟨1526459, by rfl⟩ : syracuseStep 2035279 = 3052919) B3052919
theorem B3052925 : Blo 2033435 3052925 := bbase (se 3 (by rfl) ⟨572423, by rfl⟩ : syracuseStep 3052925 = 1144847) (by norm_num)
theorem B2035283 : Blo 2033435 2035283 := bstep (se 1 (by rfl) ⟨1526462, by rfl⟩ : syracuseStep 2035283 = 3052925) B3052925
theorem B4579397 : Blo 2033435 4579397 := bbase (se 4 (by rfl) ⟨429318, by rfl⟩ : syracuseStep 4579397 = 858637) (by norm_num)
theorem B3052931 : Blo 2033435 3052931 := bstep (se 1 (by rfl) ⟨2289698, by rfl⟩ : syracuseStep 3052931 = 4579397) B4579397
theorem B2035287 : Blo 2033435 2035287 := bstep (se 1 (by rfl) ⟨1526465, by rfl⟩ : syracuseStep 2035287 = 3052931) B3052931
theorem B5795813 : Blo 2033435 5795813 := bbase (se 4 (by rfl) ⟨543357, by rfl⟩ : syracuseStep 5795813 = 1086715) (by norm_num)
theorem B3863875 : Blo 2033435 3863875 := bstep (se 1 (by rfl) ⟨2897906, by rfl⟩ : syracuseStep 3863875 = 5795813) B5795813
theorem B5151833 : Blo 2033435 5151833 := bstep (se 2 (by rfl) ⟨1931937, by rfl⟩ : syracuseStep 5151833 = 3863875) B3863875
theorem B3434555 : Blo 2033435 3434555 := bstep (se 1 (by rfl) ⟨2575916, by rfl⟩ : syracuseStep 3434555 = 5151833) B5151833
theorem B2289703 : Blo 2033435 2289703 := bstep (se 1 (by rfl) ⟨1717277, by rfl⟩ : syracuseStep 2289703 = 3434555) B3434555
theorem B3052937 : Blo 2033435 3052937 := bstep (se 2 (by rfl) ⟨1144851, by rfl⟩ : syracuseStep 3052937 = 2289703) B2289703
theorem B2035291 : Blo 2033435 2035291 := bstep (se 1 (by rfl) ⟨1526468, by rfl⟩ : syracuseStep 2035291 = 3052937) B3052937
theorem B10303685 : Blo 2033435 10303685 := bbase (se 4 (by rfl) ⟨965970, by rfl⟩ : syracuseStep 10303685 = 1931941) (by norm_num)
theorem B6869123 : Blo 2033435 6869123 := bstep (se 1 (by rfl) ⟨5151842, by rfl⟩ : syracuseStep 6869123 = 10303685) B10303685
theorem B4579415 : Blo 2033435 4579415 := bstep (se 1 (by rfl) ⟨3434561, by rfl⟩ : syracuseStep 4579415 = 6869123) B6869123
theorem B3052943 : Blo 2033435 3052943 := bstep (se 1 (by rfl) ⟨2289707, by rfl⟩ : syracuseStep 3052943 = 4579415) B4579415
theorem B2035295 : Blo 2033435 2035295 := bstep (se 1 (by rfl) ⟨1526471, by rfl⟩ : syracuseStep 2035295 = 3052943) B3052943
theorem B3052949 : Blo 2033435 3052949 := bbase (se 6 (by rfl) ⟨71553, by rfl⟩ : syracuseStep 3052949 = 143107) (by norm_num)
theorem B2035299 : Blo 2033435 2035299 := bstep (se 1 (by rfl) ⟨1526474, by rfl⟩ : syracuseStep 2035299 = 3052949) B3052949
theorem B4346885 : Blo 2033435 4346885 := bbase (se 4 (by rfl) ⟨407520, by rfl⟩ : syracuseStep 4346885 = 815041) (by norm_num)
theorem B11591693 : Blo 2033435 11591693 := bstep (se 3 (by rfl) ⟨2173442, by rfl⟩ : syracuseStep 11591693 = 4346885) B4346885
theorem B7727795 : Blo 2033435 7727795 := bstep (se 1 (by rfl) ⟨5795846, by rfl⟩ : syracuseStep 7727795 = 11591693) B11591693
theorem B5151863 : Blo 2033435 5151863 := bstep (se 1 (by rfl) ⟨3863897, by rfl⟩ : syracuseStep 5151863 = 7727795) B7727795
theorem B3434575 : Blo 2033435 3434575 := bstep (se 1 (by rfl) ⟨2575931, by rfl⟩ : syracuseStep 3434575 = 5151863) B5151863
theorem B4579433 : Blo 2033435 4579433 := bstep (se 2 (by rfl) ⟨1717287, by rfl⟩ : syracuseStep 4579433 = 3434575) B3434575
theorem B3052955 : Blo 2033435 3052955 := bstep (se 1 (by rfl) ⟨2289716, by rfl⟩ : syracuseStep 3052955 = 4579433) B4579433
theorem B2035303 : Blo 2033435 2035303 := bstep (se 1 (by rfl) ⟨1526477, by rfl⟩ : syracuseStep 2035303 = 3052955) B3052955
theorem B2289721 : Blo 2033435 2289721 := bbase (se 2 (by rfl) ⟨858645, by rfl⟩ : syracuseStep 2289721 = 1717291) (by norm_num)
theorem B3052961 : Blo 2033435 3052961 := bstep (se 2 (by rfl) ⟨1144860, by rfl⟩ : syracuseStep 3052961 = 2289721) B2289721
theorem B2035307 : Blo 2033435 2035307 := bstep (se 1 (by rfl) ⟨1526480, by rfl⟩ : syracuseStep 2035307 = 3052961) B3052961
theorem B2445133 : Blo 2033435 2445133 := bbase (se 3 (by rfl) ⟨458462, by rfl⟩ : syracuseStep 2445133 = 916925) (by norm_num)
theorem B3260177 : Blo 2033435 3260177 := bstep (se 2 (by rfl) ⟨1222566, by rfl⟩ : syracuseStep 3260177 = 2445133) B2445133
theorem B2173451 : Blo 2033435 2173451 := bstep (se 1 (by rfl) ⟨1630088, by rfl⟩ : syracuseStep 2173451 = 3260177) B3260177
theorem B5795869 : Blo 2033435 5795869 := bstep (se 3 (by rfl) ⟨1086725, by rfl⟩ : syracuseStep 5795869 = 2173451) B2173451
theorem B7727825 : Blo 2033435 7727825 := bstep (se 2 (by rfl) ⟨2897934, by rfl⟩ : syracuseStep 7727825 = 5795869) B5795869
theorem B5151883 : Blo 2033435 5151883 := bstep (se 1 (by rfl) ⟨3863912, by rfl⟩ : syracuseStep 5151883 = 7727825) B7727825
theorem B6869177 : Blo 2033435 6869177 := bstep (se 2 (by rfl) ⟨2575941, by rfl⟩ : syracuseStep 6869177 = 5151883) B5151883
theorem B4579451 : Blo 2033435 4579451 := bstep (se 1 (by rfl) ⟨3434588, by rfl⟩ : syracuseStep 4579451 = 6869177) B6869177
theorem B3052967 : Blo 2033435 3052967 := bstep (se 1 (by rfl) ⟨2289725, by rfl⟩ : syracuseStep 3052967 = 4579451) B4579451
theorem B2035311 : Blo 2033435 2035311 := bstep (se 1 (by rfl) ⟨1526483, by rfl⟩ : syracuseStep 2035311 = 3052967) B3052967
theorem B3052973 : Blo 2033435 3052973 := bbase (se 3 (by rfl) ⟨572432, by rfl⟩ : syracuseStep 3052973 = 1144865) (by norm_num)
theorem B2035315 : Blo 2033435 2035315 := bstep (se 1 (by rfl) ⟨1526486, by rfl⟩ : syracuseStep 2035315 = 3052973) B3052973
theorem B4579469 : Blo 2033435 4579469 := bbase (se 3 (by rfl) ⟨858650, by rfl⟩ : syracuseStep 4579469 = 1717301) (by norm_num)
theorem B3052979 : Blo 2033435 3052979 := bstep (se 1 (by rfl) ⟨2289734, by rfl⟩ : syracuseStep 3052979 = 4579469) B4579469
theorem B2035319 : Blo 2033435 2035319 := bstep (se 1 (by rfl) ⟨1526489, by rfl⟩ : syracuseStep 2035319 = 3052979) B3052979
theorem B2575957 : Blo 2033435 2575957 := bbase (se 8 (by rfl) ⟨15093, by rfl⟩ : syracuseStep 2575957 = 30187) (by norm_num)
theorem B3434609 : Blo 2033435 3434609 := bstep (se 2 (by rfl) ⟨1287978, by rfl⟩ : syracuseStep 3434609 = 2575957) B2575957
theorem B2289739 : Blo 2033435 2289739 := bstep (se 1 (by rfl) ⟨1717304, by rfl⟩ : syracuseStep 2289739 = 3434609) B3434609
theorem B3052985 : Blo 2033435 3052985 := bstep (se 2 (by rfl) ⟨1144869, by rfl⟩ : syracuseStep 3052985 = 2289739) B2289739
theorem B2035323 : Blo 2033435 2035323 := bstep (se 1 (by rfl) ⟨1526492, by rfl⟩ : syracuseStep 2035323 = 3052985) B3052985
theorem B35249941 : Blo 2033435 35249941 := bbase (se 6 (by rfl) ⟨826170, by rfl⟩ : syracuseStep 35249941 = 1652341) (by norm_num)
theorem B46999921 : Blo 2033435 46999921 := bstep (se 2 (by rfl) ⟨17624970, by rfl⟩ : syracuseStep 46999921 = 35249941) B35249941
theorem B62666561 : Blo 2033435 62666561 := bstep (se 2 (by rfl) ⟨23499960, by rfl⟩ : syracuseStep 62666561 = 46999921) B46999921
theorem B41777707 : Blo 2033435 41777707 := bstep (se 1 (by rfl) ⟨31333280, by rfl⟩ : syracuseStep 41777707 = 62666561) B62666561
theorem B55703609 : Blo 2033435 55703609 := bstep (se 2 (by rfl) ⟨20888853, by rfl⟩ : syracuseStep 55703609 = 41777707) B41777707
theorem B37135739 : Blo 2033435 37135739 := bstep (se 1 (by rfl) ⟨27851804, by rfl⟩ : syracuseStep 37135739 = 55703609) B55703609
theorem B24757159 : Blo 2033435 24757159 := bstep (se 1 (by rfl) ⟨18567869, by rfl⟩ : syracuseStep 24757159 = 37135739) B37135739
theorem B33009545 : Blo 2033435 33009545 := bstep (se 2 (by rfl) ⟨12378579, by rfl⟩ : syracuseStep 33009545 = 24757159) B24757159
theorem B88025453 : Blo 2033435 88025453 := bstep (se 3 (by rfl) ⟨16504772, by rfl⟩ : syracuseStep 88025453 = 33009545) B33009545
theorem B58683635 : Blo 2033435 58683635 := bstep (se 1 (by rfl) ⟨44012726, by rfl⟩ : syracuseStep 58683635 = 88025453) B88025453
theorem B39122423 : Blo 2033435 39122423 := bstep (se 1 (by rfl) ⟨29341817, by rfl⟩ : syracuseStep 39122423 = 58683635) B58683635
theorem B26081615 : Blo 2033435 26081615 := bstep (se 1 (by rfl) ⟨19561211, by rfl⟩ : syracuseStep 26081615 = 39122423) B39122423
theorem B17387743 : Blo 2033435 17387743 := bstep (se 1 (by rfl) ⟨13040807, by rfl⟩ : syracuseStep 17387743 = 26081615) B26081615
theorem B23183657 : Blo 2033435 23183657 := bstep (se 2 (by rfl) ⟨8693871, by rfl⟩ : syracuseStep 23183657 = 17387743) B17387743
theorem B15455771 : Blo 2033435 15455771 := bstep (se 1 (by rfl) ⟨11591828, by rfl⟩ : syracuseStep 15455771 = 23183657) B23183657
theorem B10303847 : Blo 2033435 10303847 := bstep (se 1 (by rfl) ⟨7727885, by rfl⟩ : syracuseStep 10303847 = 15455771) B15455771
theorem B6869231 : Blo 2033435 6869231 := bstep (se 1 (by rfl) ⟨5151923, by rfl⟩ : syracuseStep 6869231 = 10303847) B10303847
theorem B4579487 : Blo 2033435 4579487 := bstep (se 1 (by rfl) ⟨3434615, by rfl⟩ : syracuseStep 4579487 = 6869231) B6869231
theorem B3052991 : Blo 2033435 3052991 := bstep (se 1 (by rfl) ⟨2289743, by rfl⟩ : syracuseStep 3052991 = 4579487) B4579487
theorem B2035327 : Blo 2033435 2035327 := bstep (se 1 (by rfl) ⟨1526495, by rfl⟩ : syracuseStep 2035327 = 3052991) B3052991
theorem B3052997 : Blo 2033435 3052997 := bbase (se 4 (by rfl) ⟨286218, by rfl⟩ : syracuseStep 3052997 = 572437) (by norm_num)
theorem B2035331 : Blo 2033435 2035331 := bstep (se 1 (by rfl) ⟨1526498, by rfl⟩ : syracuseStep 2035331 = 3052997) B3052997
theorem B3434629 : Blo 2033435 3434629 := bbase (se 4 (by rfl) ⟨321996, by rfl⟩ : syracuseStep 3434629 = 643993) (by norm_num)
theorem B4579505 : Blo 2033435 4579505 := bstep (se 2 (by rfl) ⟨1717314, by rfl⟩ : syracuseStep 4579505 = 3434629) B3434629
theorem B3053003 : Blo 2033435 3053003 := bstep (se 1 (by rfl) ⟨2289752, by rfl⟩ : syracuseStep 3053003 = 4579505) B4579505
theorem B2035335 : Blo 2033435 2035335 := bstep (se 1 (by rfl) ⟨1526501, by rfl⟩ : syracuseStep 2035335 = 3053003) B3053003
theorem B2289757 : Blo 2033435 2289757 := bbase (se 3 (by rfl) ⟨429329, by rfl⟩ : syracuseStep 2289757 = 858659) (by norm_num)
theorem B3053009 : Blo 2033435 3053009 := bstep (se 2 (by rfl) ⟨1144878, by rfl⟩ : syracuseStep 3053009 = 2289757) B2289757
theorem B2035339 : Blo 2033435 2035339 := bstep (se 1 (by rfl) ⟨1526504, by rfl⟩ : syracuseStep 2035339 = 3053009) B3053009
theorem B6869285 : Blo 2033435 6869285 := bbase (se 4 (by rfl) ⟨643995, by rfl⟩ : syracuseStep 6869285 = 1287991) (by norm_num)
theorem B4579523 : Blo 2033435 4579523 := bstep (se 1 (by rfl) ⟨3434642, by rfl⟩ : syracuseStep 4579523 = 6869285) B6869285
theorem B3053015 : Blo 2033435 3053015 := bstep (se 1 (by rfl) ⟨2289761, by rfl⟩ : syracuseStep 3053015 = 4579523) B4579523
theorem B2035343 : Blo 2033435 2035343 := bstep (se 1 (by rfl) ⟨1526507, by rfl⟩ : syracuseStep 2035343 = 3053015) B3053015
theorem B3053021 : Blo 2033435 3053021 := bbase (se 3 (by rfl) ⟨572441, by rfl⟩ : syracuseStep 3053021 = 1144883) (by norm_num)
theorem B2035347 : Blo 2033435 2035347 := bstep (se 1 (by rfl) ⟨1526510, by rfl⟩ : syracuseStep 2035347 = 3053021) B3053021
theorem B4579541 : Blo 2033435 4579541 := bbase (se 7 (by rfl) ⟨53666, by rfl⟩ : syracuseStep 4579541 = 107333) (by norm_num)
theorem B3053027 : Blo 2033435 3053027 := bstep (se 1 (by rfl) ⟨2289770, by rfl⟩ : syracuseStep 3053027 = 4579541) B4579541
theorem B2035351 : Blo 2033435 2035351 := bstep (se 1 (by rfl) ⟨1526513, by rfl⟩ : syracuseStep 2035351 = 3053027) B3053027
theorem B3481525 : Blo 2033435 3481525 := bbase (se 5 (by rfl) ⟨163196, by rfl⟩ : syracuseStep 3481525 = 326393) (by norm_num)
theorem B4642033 : Blo 2033435 4642033 := bstep (se 2 (by rfl) ⟨1740762, by rfl⟩ : syracuseStep 4642033 = 3481525) B3481525
theorem B6189377 : Blo 2033435 6189377 := bstep (se 2 (by rfl) ⟨2321016, by rfl⟩ : syracuseStep 6189377 = 4642033) B4642033
theorem B16505005 : Blo 2033435 16505005 := bstep (se 3 (by rfl) ⟨3094688, by rfl⟩ : syracuseStep 16505005 = 6189377) B6189377
theorem B22006673 : Blo 2033435 22006673 := bstep (se 2 (by rfl) ⟨8252502, by rfl⟩ : syracuseStep 22006673 = 16505005) B16505005
theorem B14671115 : Blo 2033435 14671115 := bstep (se 1 (by rfl) ⟨11003336, by rfl⟩ : syracuseStep 14671115 = 22006673) B22006673
theorem B9780743 : Blo 2033435 9780743 := bstep (se 1 (by rfl) ⟨7335557, by rfl⟩ : syracuseStep 9780743 = 14671115) B14671115
theorem B6520495 : Blo 2033435 6520495 := bstep (se 1 (by rfl) ⟨4890371, by rfl⟩ : syracuseStep 6520495 = 9780743) B9780743
theorem B8693993 : Blo 2033435 8693993 := bstep (se 2 (by rfl) ⟨3260247, by rfl⟩ : syracuseStep 8693993 = 6520495) B6520495
theorem B5795995 : Blo 2033435 5795995 := bstep (se 1 (by rfl) ⟨4346996, by rfl⟩ : syracuseStep 5795995 = 8693993) B8693993
theorem B7727993 : Blo 2033435 7727993 := bstep (se 2 (by rfl) ⟨2897997, by rfl⟩ : syracuseStep 7727993 = 5795995) B5795995
theorem B5151995 : Blo 2033435 5151995 := bstep (se 1 (by rfl) ⟨3863996, by rfl⟩ : syracuseStep 5151995 = 7727993) B7727993
theorem B3434663 : Blo 2033435 3434663 := bstep (se 1 (by rfl) ⟨2575997, by rfl⟩ : syracuseStep 3434663 = 5151995) B5151995
theorem B2289775 : Blo 2033435 2289775 := bstep (se 1 (by rfl) ⟨1717331, by rfl⟩ : syracuseStep 2289775 = 3434663) B3434663
theorem B3053033 : Blo 2033435 3053033 := bstep (se 2 (by rfl) ⟨1144887, by rfl⟩ : syracuseStep 3053033 = 2289775) B2289775
theorem B2035355 : Blo 2033435 2035355 := bstep (se 1 (by rfl) ⟨1526516, by rfl⟩ : syracuseStep 2035355 = 3053033) B3053033
theorem B13041013 : Blo 2033435 13041013 := bbase (se 5 (by rfl) ⟨611297, by rfl⟩ : syracuseStep 13041013 = 1222595) (by norm_num)
theorem B17388017 : Blo 2033435 17388017 := bstep (se 2 (by rfl) ⟨6520506, by rfl⟩ : syracuseStep 17388017 = 13041013) B13041013
theorem B11592011 : Blo 2033435 11592011 := bstep (se 1 (by rfl) ⟨8694008, by rfl⟩ : syracuseStep 11592011 = 17388017) B17388017
theorem B7728007 : Blo 2033435 7728007 := bstep (se 1 (by rfl) ⟨5796005, by rfl⟩ : syracuseStep 7728007 = 11592011) B11592011
theorem B10304009 : Blo 2033435 10304009 := bstep (se 2 (by rfl) ⟨3864003, by rfl⟩ : syracuseStep 10304009 = 7728007) B7728007
theorem B6869339 : Blo 2033435 6869339 := bstep (se 1 (by rfl) ⟨5152004, by rfl⟩ : syracuseStep 6869339 = 10304009) B10304009
theorem B4579559 : Blo 2033435 4579559 := bstep (se 1 (by rfl) ⟨3434669, by rfl⟩ : syracuseStep 4579559 = 6869339) B6869339
theorem B3053039 : Blo 2033435 3053039 := bstep (se 1 (by rfl) ⟨2289779, by rfl⟩ : syracuseStep 3053039 = 4579559) B4579559
theorem B2035359 : Blo 2033435 2035359 := bstep (se 1 (by rfl) ⟨1526519, by rfl⟩ : syracuseStep 2035359 = 3053039) B3053039
theorem B3053045 : Blo 2033435 3053045 := bbase (se 5 (by rfl) ⟨143111, by rfl⟩ : syracuseStep 3053045 = 286223) (by norm_num)
theorem B2035363 : Blo 2033435 2035363 := bstep (se 1 (by rfl) ⟨1526522, by rfl⟩ : syracuseStep 2035363 = 3053045) B3053045
theorem B4126277 : Blo 2033435 4126277 := bbase (se 4 (by rfl) ⟨386838, by rfl⟩ : syracuseStep 4126277 = 773677) (by norm_num)
theorem B2750851 : Blo 2033435 2750851 := bstep (se 1 (by rfl) ⟨2063138, by rfl⟩ : syracuseStep 2750851 = 4126277) B4126277
theorem B3667801 : Blo 2033435 3667801 := bstep (se 2 (by rfl) ⟨1375425, by rfl⟩ : syracuseStep 3667801 = 2750851) B2750851
theorem B4890401 : Blo 2033435 4890401 := bstep (se 2 (by rfl) ⟨1833900, by rfl⟩ : syracuseStep 4890401 = 3667801) B3667801
theorem B3260267 : Blo 2033435 3260267 := bstep (se 1 (by rfl) ⟨2445200, by rfl⟩ : syracuseStep 3260267 = 4890401) B4890401
theorem B2173511 : Blo 2033435 2173511 := bstep (se 1 (by rfl) ⟨1630133, by rfl⟩ : syracuseStep 2173511 = 3260267) B3260267
theorem B5796029 : Blo 2033435 5796029 := bstep (se 3 (by rfl) ⟨1086755, by rfl⟩ : syracuseStep 5796029 = 2173511) B2173511
theorem B3864019 : Blo 2033435 3864019 := bstep (se 1 (by rfl) ⟨2898014, by rfl⟩ : syracuseStep 3864019 = 5796029) B5796029
theorem B5152025 : Blo 2033435 5152025 := bstep (se 2 (by rfl) ⟨1932009, by rfl⟩ : syracuseStep 5152025 = 3864019) B3864019
theorem B3434683 : Blo 2033435 3434683 := bstep (se 1 (by rfl) ⟨2576012, by rfl⟩ : syracuseStep 3434683 = 5152025) B5152025
theorem B4579577 : Blo 2033435 4579577 := bstep (se 2 (by rfl) ⟨1717341, by rfl⟩ : syracuseStep 4579577 = 3434683) B3434683
theorem B3053051 : Blo 2033435 3053051 := bstep (se 1 (by rfl) ⟨2289788, by rfl⟩ : syracuseStep 3053051 = 4579577) B4579577
theorem B2035367 : Blo 2033435 2035367 := bstep (se 1 (by rfl) ⟨1526525, by rfl⟩ : syracuseStep 2035367 = 3053051) B3053051
theorem B2289793 : Blo 2033435 2289793 := bbase (se 2 (by rfl) ⟨858672, by rfl⟩ : syracuseStep 2289793 = 1717345) (by norm_num)
theorem B3053057 : Blo 2033435 3053057 := bstep (se 2 (by rfl) ⟨1144896, by rfl⟩ : syracuseStep 3053057 = 2289793) B2289793
theorem B2035371 : Blo 2033435 2035371 := bstep (se 1 (by rfl) ⟨1526528, by rfl⟩ : syracuseStep 2035371 = 3053057) B3053057
theorem B5152045 : Blo 2033435 5152045 := bbase (se 3 (by rfl) ⟨966008, by rfl⟩ : syracuseStep 5152045 = 1932017) (by norm_num)
theorem B6869393 : Blo 2033435 6869393 := bstep (se 2 (by rfl) ⟨2576022, by rfl⟩ : syracuseStep 6869393 = 5152045) B5152045
theorem B4579595 : Blo 2033435 4579595 := bstep (se 1 (by rfl) ⟨3434696, by rfl⟩ : syracuseStep 4579595 = 6869393) B6869393
theorem B3053063 : Blo 2033435 3053063 := bstep (se 1 (by rfl) ⟨2289797, by rfl⟩ : syracuseStep 3053063 = 4579595) B4579595
theorem B2035375 : Blo 2033435 2035375 := bstep (se 1 (by rfl) ⟨1526531, by rfl⟩ : syracuseStep 2035375 = 3053063) B3053063
theorem B3053069 : Blo 2033435 3053069 := bbase (se 3 (by rfl) ⟨572450, by rfl⟩ : syracuseStep 3053069 = 1144901) (by norm_num)
theorem B2035379 : Blo 2033435 2035379 := bstep (se 1 (by rfl) ⟨1526534, by rfl⟩ : syracuseStep 2035379 = 3053069) B3053069
theorem B4579613 : Blo 2033435 4579613 := bbase (se 3 (by rfl) ⟨858677, by rfl⟩ : syracuseStep 4579613 = 1717355) (by norm_num)
theorem B3053075 : Blo 2033435 3053075 := bstep (se 1 (by rfl) ⟨2289806, by rfl⟩ : syracuseStep 3053075 = 4579613) B4579613
theorem B2035383 : Blo 2033435 2035383 := bstep (se 1 (by rfl) ⟨1526537, by rfl⟩ : syracuseStep 2035383 = 3053075) B3053075
theorem B3434717 : Blo 2033435 3434717 := bbase (se 3 (by rfl) ⟨644009, by rfl⟩ : syracuseStep 3434717 = 1288019) (by norm_num)
theorem B2289811 : Blo 2033435 2289811 := bstep (se 1 (by rfl) ⟨1717358, by rfl⟩ : syracuseStep 2289811 = 3434717) B3434717
theorem B3053081 : Blo 2033435 3053081 := bstep (se 2 (by rfl) ⟨1144905, by rfl⟩ : syracuseStep 3053081 = 2289811) B2289811
theorem B2035387 : Blo 2033435 2035387 := bstep (se 1 (by rfl) ⟨1526540, by rfl⟩ : syracuseStep 2035387 = 3053081) B3053081
theorem B5501765 : Blo 2033435 5501765 := bbase (se 4 (by rfl) ⟨515790, by rfl⟩ : syracuseStep 5501765 = 1031581) (by norm_num)
theorem B3667843 : Blo 2033435 3667843 := bstep (se 1 (by rfl) ⟨2750882, by rfl⟩ : syracuseStep 3667843 = 5501765) B5501765
theorem B4890457 : Blo 2033435 4890457 := bstep (se 2 (by rfl) ⟨1833921, by rfl⟩ : syracuseStep 4890457 = 3667843) B3667843
theorem B6520609 : Blo 2033435 6520609 := bstep (se 2 (by rfl) ⟨2445228, by rfl⟩ : syracuseStep 6520609 = 4890457) B4890457
theorem B8694145 : Blo 2033435 8694145 := bstep (se 2 (by rfl) ⟨3260304, by rfl⟩ : syracuseStep 8694145 = 6520609) B6520609
theorem B11592193 : Blo 2033435 11592193 := bstep (se 2 (by rfl) ⟨4347072, by rfl⟩ : syracuseStep 11592193 = 8694145) B8694145
theorem B15456257 : Blo 2033435 15456257 := bstep (se 2 (by rfl) ⟨5796096, by rfl⟩ : syracuseStep 15456257 = 11592193) B11592193
theorem B10304171 : Blo 2033435 10304171 := bstep (se 1 (by rfl) ⟨7728128, by rfl⟩ : syracuseStep 10304171 = 15456257) B15456257
theorem B6869447 : Blo 2033435 6869447 := bstep (se 1 (by rfl) ⟨5152085, by rfl⟩ : syracuseStep 6869447 = 10304171) B10304171
theorem B4579631 : Blo 2033435 4579631 := bstep (se 1 (by rfl) ⟨3434723, by rfl⟩ : syracuseStep 4579631 = 6869447) B6869447
theorem B3053087 : Blo 2033435 3053087 := bstep (se 1 (by rfl) ⟨2289815, by rfl⟩ : syracuseStep 3053087 = 4579631) B4579631
theorem B2035391 : Blo 2033435 2035391 := bstep (se 1 (by rfl) ⟨1526543, by rfl⟩ : syracuseStep 2035391 = 3053087) B3053087
theorem B3053093 : Blo 2033435 3053093 := bbase (se 4 (by rfl) ⟨286227, by rfl⟩ : syracuseStep 3053093 = 572455) (by norm_num)
theorem B2035395 : Blo 2033435 2035395 := bstep (se 1 (by rfl) ⟨1526546, by rfl⟩ : syracuseStep 2035395 = 3053093) B3053093
theorem B2576053 : Blo 2033435 2576053 := bbase (se 5 (by rfl) ⟨120752, by rfl⟩ : syracuseStep 2576053 = 241505) (by norm_num)
theorem B3434737 : Blo 2033435 3434737 := bstep (se 2 (by rfl) ⟨1288026, by rfl⟩ : syracuseStep 3434737 = 2576053) B2576053
theorem B4579649 : Blo 2033435 4579649 := bstep (se 2 (by rfl) ⟨1717368, by rfl⟩ : syracuseStep 4579649 = 3434737) B3434737
theorem B3053099 : Blo 2033435 3053099 := bstep (se 1 (by rfl) ⟨2289824, by rfl⟩ : syracuseStep 3053099 = 4579649) B4579649
theorem B2035399 : Blo 2033435 2035399 := bstep (se 1 (by rfl) ⟨1526549, by rfl⟩ : syracuseStep 2035399 = 3053099) B3053099
theorem B2289829 : Blo 2033435 2289829 := bbase (se 4 (by rfl) ⟨214671, by rfl⟩ : syracuseStep 2289829 = 429343) (by norm_num)
theorem B3053105 : Blo 2033435 3053105 := bstep (se 2 (by rfl) ⟨1144914, by rfl⟩ : syracuseStep 3053105 = 2289829) B2289829
theorem B2035403 : Blo 2033435 2035403 := bstep (se 1 (by rfl) ⟨1526552, by rfl⟩ : syracuseStep 2035403 = 3053105) B3053105
theorem B2119861 : Blo 2033435 2119861 := bbase (se 5 (by rfl) ⟨99368, by rfl⟩ : syracuseStep 2119861 = 198737) (by norm_num)
theorem B11305925 : Blo 2033435 11305925 := bstep (se 4 (by rfl) ⟨1059930, by rfl⟩ : syracuseStep 11305925 = 2119861) B2119861
theorem B7537283 : Blo 2033435 7537283 := bstep (se 1 (by rfl) ⟨5652962, by rfl⟩ : syracuseStep 7537283 = 11305925) B11305925
theorem B5024855 : Blo 2033435 5024855 := bstep (se 1 (by rfl) ⟨3768641, by rfl⟩ : syracuseStep 5024855 = 7537283) B7537283
theorem B13399613 : Blo 2033435 13399613 := bstep (se 3 (by rfl) ⟨2512427, by rfl⟩ : syracuseStep 13399613 = 5024855) B5024855
theorem B8933075 : Blo 2033435 8933075 := bstep (se 1 (by rfl) ⟨6699806, by rfl⟩ : syracuseStep 8933075 = 13399613) B13399613
theorem B5955383 : Blo 2033435 5955383 := bstep (se 1 (by rfl) ⟨4466537, by rfl⟩ : syracuseStep 5955383 = 8933075) B8933075
theorem B15881021 : Blo 2033435 15881021 := bstep (se 3 (by rfl) ⟨2977691, by rfl⟩ : syracuseStep 15881021 = 5955383) B5955383
theorem B10587347 : Blo 2033435 10587347 := bstep (se 1 (by rfl) ⟨7940510, by rfl⟩ : syracuseStep 10587347 = 15881021) B15881021
theorem B7058231 : Blo 2033435 7058231 := bstep (se 1 (by rfl) ⟨5293673, by rfl⟩ : syracuseStep 7058231 = 10587347) B10587347
theorem B4705487 : Blo 2033435 4705487 := bstep (se 1 (by rfl) ⟨3529115, by rfl⟩ : syracuseStep 4705487 = 7058231) B7058231
theorem B3136991 : Blo 2033435 3136991 := bstep (se 1 (by rfl) ⟨2352743, by rfl⟩ : syracuseStep 3136991 = 4705487) B4705487
theorem B33461237 : Blo 2033435 33461237 := bstep (se 5 (by rfl) ⟨1568495, by rfl⟩ : syracuseStep 33461237 = 3136991) B3136991
theorem B22307491 : Blo 2033435 22307491 := bstep (se 1 (by rfl) ⟨16730618, by rfl⟩ : syracuseStep 22307491 = 33461237) B33461237
theorem B29743321 : Blo 2033435 29743321 := bstep (se 2 (by rfl) ⟨11153745, by rfl⟩ : syracuseStep 29743321 = 22307491) B22307491
theorem B39657761 : Blo 2033435 39657761 := bstep (se 2 (by rfl) ⟨14871660, by rfl⟩ : syracuseStep 39657761 = 29743321) B29743321
theorem B26438507 : Blo 2033435 26438507 := bstep (se 1 (by rfl) ⟨19828880, by rfl⟩ : syracuseStep 26438507 = 39657761) B39657761
theorem B17625671 : Blo 2033435 17625671 := bstep (se 1 (by rfl) ⟨13219253, by rfl⟩ : syracuseStep 17625671 = 26438507) B26438507
theorem B11750447 : Blo 2033435 11750447 := bstep (se 1 (by rfl) ⟨8812835, by rfl⟩ : syracuseStep 11750447 = 17625671) B17625671
theorem B31334525 : Blo 2033435 31334525 := bstep (se 3 (by rfl) ⟨5875223, by rfl⟩ : syracuseStep 31334525 = 11750447) B11750447
theorem B20889683 : Blo 2033435 20889683 := bstep (se 1 (by rfl) ⟨15667262, by rfl⟩ : syracuseStep 20889683 = 31334525) B31334525
theorem B13926455 : Blo 2033435 13926455 := bstep (se 1 (by rfl) ⟨10444841, by rfl⟩ : syracuseStep 13926455 = 20889683) B20889683
theorem B9284303 : Blo 2033435 9284303 := bstep (se 1 (by rfl) ⟨6963227, by rfl⟩ : syracuseStep 9284303 = 13926455) B13926455
theorem B6189535 : Blo 2033435 6189535 := bstep (se 1 (by rfl) ⟨4642151, by rfl⟩ : syracuseStep 6189535 = 9284303) B9284303
theorem B8252713 : Blo 2033435 8252713 := bstep (se 2 (by rfl) ⟨3094767, by rfl⟩ : syracuseStep 8252713 = 6189535) B6189535
theorem B11003617 : Blo 2033435 11003617 := bstep (se 2 (by rfl) ⟨4126356, by rfl⟩ : syracuseStep 11003617 = 8252713) B8252713
theorem B14671489 : Blo 2033435 14671489 := bstep (se 2 (by rfl) ⟨5501808, by rfl⟩ : syracuseStep 14671489 = 11003617) B11003617
theorem B19561985 : Blo 2033435 19561985 := bstep (se 2 (by rfl) ⟨7335744, by rfl⟩ : syracuseStep 19561985 = 14671489) B14671489
theorem B13041323 : Blo 2033435 13041323 := bstep (se 1 (by rfl) ⟨9780992, by rfl⟩ : syracuseStep 13041323 = 19561985) B19561985
theorem B8694215 : Blo 2033435 8694215 := bstep (se 1 (by rfl) ⟨6520661, by rfl⟩ : syracuseStep 8694215 = 13041323) B13041323
theorem B5796143 : Blo 2033435 5796143 := bstep (se 1 (by rfl) ⟨4347107, by rfl⟩ : syracuseStep 5796143 = 8694215) B8694215
theorem B3864095 : Blo 2033435 3864095 := bstep (se 1 (by rfl) ⟨2898071, by rfl⟩ : syracuseStep 3864095 = 5796143) B5796143
theorem B2576063 : Blo 2033435 2576063 := bstep (se 1 (by rfl) ⟨1932047, by rfl⟩ : syracuseStep 2576063 = 3864095) B3864095
theorem B6869501 : Blo 2033435 6869501 := bstep (se 3 (by rfl) ⟨1288031, by rfl⟩ : syracuseStep 6869501 = 2576063) B2576063
theorem B4579667 : Blo 2033435 4579667 := bstep (se 1 (by rfl) ⟨3434750, by rfl⟩ : syracuseStep 4579667 = 6869501) B6869501
theorem B3053111 : Blo 2033435 3053111 := bstep (se 1 (by rfl) ⟨2289833, by rfl⟩ : syracuseStep 3053111 = 4579667) B4579667
theorem B2035407 : Blo 2033435 2035407 := bstep (se 1 (by rfl) ⟨1526555, by rfl⟩ : syracuseStep 2035407 = 3053111) B3053111
theorem B3053117 : Blo 2033435 3053117 := bbase (se 3 (by rfl) ⟨572459, by rfl⟩ : syracuseStep 3053117 = 1144919) (by norm_num)
theorem B2035411 : Blo 2033435 2035411 := bstep (se 1 (by rfl) ⟨1526558, by rfl⟩ : syracuseStep 2035411 = 3053117) B3053117
theorem B4579685 : Blo 2033435 4579685 := bbase (se 4 (by rfl) ⟨429345, by rfl⟩ : syracuseStep 4579685 = 858691) (by norm_num)
theorem B3053123 : Blo 2033435 3053123 := bstep (se 1 (by rfl) ⟨2289842, by rfl⟩ : syracuseStep 3053123 = 4579685) B4579685
theorem B2035415 : Blo 2033435 2035415 := bstep (se 1 (by rfl) ⟨1526561, by rfl⟩ : syracuseStep 2035415 = 3053123) B3053123
theorem B5152157 : Blo 2033435 5152157 := bbase (se 3 (by rfl) ⟨966029, by rfl⟩ : syracuseStep 5152157 = 1932059) (by norm_num)
theorem B3434771 : Blo 2033435 3434771 := bstep (se 1 (by rfl) ⟨2576078, by rfl⟩ : syracuseStep 3434771 = 5152157) B5152157
theorem B2289847 : Blo 2033435 2289847 := bstep (se 1 (by rfl) ⟨1717385, by rfl⟩ : syracuseStep 2289847 = 3434771) B3434771
theorem B3053129 : Blo 2033435 3053129 := bstep (se 2 (by rfl) ⟨1144923, by rfl⟩ : syracuseStep 3053129 = 2289847) B2289847
theorem B2035419 : Blo 2033435 2035419 := bstep (se 1 (by rfl) ⟨1526564, by rfl⟩ : syracuseStep 2035419 = 3053129) B3053129
theorem B3864125 : Blo 2033435 3864125 := bbase (se 3 (by rfl) ⟨724523, by rfl⟩ : syracuseStep 3864125 = 1449047) (by norm_num)
theorem B10304333 : Blo 2033435 10304333 := bstep (se 3 (by rfl) ⟨1932062, by rfl⟩ : syracuseStep 10304333 = 3864125) B3864125
theorem B6869555 : Blo 2033435 6869555 := bstep (se 1 (by rfl) ⟨5152166, by rfl⟩ : syracuseStep 6869555 = 10304333) B10304333
theorem B4579703 : Blo 2033435 4579703 := bstep (se 1 (by rfl) ⟨3434777, by rfl⟩ : syracuseStep 4579703 = 6869555) B6869555
theorem B3053135 : Blo 2033435 3053135 := bstep (se 1 (by rfl) ⟨2289851, by rfl⟩ : syracuseStep 3053135 = 4579703) B4579703
theorem B2035423 : Blo 2033435 2035423 := bstep (se 1 (by rfl) ⟨1526567, by rfl⟩ : syracuseStep 2035423 = 3053135) B3053135
theorem B3053141 : Blo 2033435 3053141 := bbase (se 8 (by rfl) ⟨17889, by rfl⟩ : syracuseStep 3053141 = 35779) (by norm_num)
theorem B2035427 : Blo 2033435 2035427 := bstep (se 1 (by rfl) ⟨1526570, by rfl⟩ : syracuseStep 2035427 = 3053141) B3053141
theorem B2445277 : Blo 2033435 2445277 := bbase (se 3 (by rfl) ⟨458489, by rfl⟩ : syracuseStep 2445277 = 916979) (by norm_num)
theorem B3260369 : Blo 2033435 3260369 := bstep (se 2 (by rfl) ⟨1222638, by rfl⟩ : syracuseStep 3260369 = 2445277) B2445277
theorem B8694317 : Blo 2033435 8694317 := bstep (se 3 (by rfl) ⟨1630184, by rfl⟩ : syracuseStep 8694317 = 3260369) B3260369
theorem B5796211 : Blo 2033435 5796211 := bstep (se 1 (by rfl) ⟨4347158, by rfl⟩ : syracuseStep 5796211 = 8694317) B8694317
theorem B7728281 : Blo 2033435 7728281 := bstep (se 2 (by rfl) ⟨2898105, by rfl⟩ : syracuseStep 7728281 = 5796211) B5796211
theorem B5152187 : Blo 2033435 5152187 := bstep (se 1 (by rfl) ⟨3864140, by rfl⟩ : syracuseStep 5152187 = 7728281) B7728281
theorem B3434791 : Blo 2033435 3434791 := bstep (se 1 (by rfl) ⟨2576093, by rfl⟩ : syracuseStep 3434791 = 5152187) B5152187
theorem B4579721 : Blo 2033435 4579721 := bstep (se 2 (by rfl) ⟨1717395, by rfl⟩ : syracuseStep 4579721 = 3434791) B3434791
theorem B3053147 : Blo 2033435 3053147 := bstep (se 1 (by rfl) ⟨2289860, by rfl⟩ : syracuseStep 3053147 = 4579721) B4579721
theorem B2035431 : Blo 2033435 2035431 := bstep (se 1 (by rfl) ⟨1526573, by rfl⟩ : syracuseStep 2035431 = 3053147) B3053147
theorem B2289865 : Blo 2033435 2289865 := bbase (se 2 (by rfl) ⟨858699, by rfl⟩ : syracuseStep 2289865 = 1717399) (by norm_num)
theorem B3053153 : Blo 2033435 3053153 := bstep (se 2 (by rfl) ⟨1144932, by rfl⟩ : syracuseStep 3053153 = 2289865) B2289865
theorem B2035435 : Blo 2033435 2035435 := bstep (se 1 (by rfl) ⟨1526576, by rfl⟩ : syracuseStep 2035435 = 3053153) B3053153
theorem C0 (j : ℕ) (h1 : 508358 ≤ j) (h2 : j ≤ 508858) : Blo 2033435 (4 * j + 3) := by
  interval_cases j
  · exact B2033435
  · exact B2033439
  · exact B2033443
  · exact B2033447
  · exact B2033451
  · exact B2033455
  · exact B2033459
  · exact B2033463
  · exact B2033467
  · exact B2033471
  · exact B2033475
  · exact B2033479
  · exact B2033483
  · exact B2033487
  · exact B2033491
  · exact B2033495
  · exact B2033499
  · exact B2033503
  · exact B2033507
  · exact B2033511
  · exact B2033515
  · exact B2033519
  · exact B2033523
  · exact B2033527
  · exact B2033531
  · exact B2033535
  · exact B2033539
  · exact B2033543
  · exact B2033547
  · exact B2033551
  · exact B2033555
  · exact B2033559
  · exact B2033563
  · exact B2033567
  · exact B2033571
  · exact B2033575
  · exact B2033579
  · exact B2033583
  · exact B2033587
  · exact B2033591
  · exact B2033595
  · exact B2033599
  · exact B2033603
  · exact B2033607
  · exact B2033611
  · exact B2033615
  · exact B2033619
  · exact B2033623
  · exact B2033627
  · exact B2033631
  · exact B2033635
  · exact B2033639
  · exact B2033643
  · exact B2033647
  · exact B2033651
  · exact B2033655
  · exact B2033659
  · exact B2033663
  · exact B2033667
  · exact B2033671
  · exact B2033675
  · exact B2033679
  · exact B2033683
  · exact B2033687
  · exact B2033691
  · exact B2033695
  · exact B2033699
  · exact B2033703
  · exact B2033707
  · exact B2033711
  · exact B2033715
  · exact B2033719
  · exact B2033723
  · exact B2033727
  · exact B2033731
  · exact B2033735
  · exact B2033739
  · exact B2033743
  · exact B2033747
  · exact B2033751
  · exact B2033755
  · exact B2033759
  · exact B2033763
  · exact B2033767
  · exact B2033771
  · exact B2033775
  · exact B2033779
  · exact B2033783
  · exact B2033787
  · exact B2033791
  · exact B2033795
  · exact B2033799
  · exact B2033803
  · exact B2033807
  · exact B2033811
  · exact B2033815
  · exact B2033819
  · exact B2033823
  · exact B2033827
  · exact B2033831
  · exact B2033835
  · exact B2033839
  · exact B2033843
  · exact B2033847
  · exact B2033851
  · exact B2033855
  · exact B2033859
  · exact B2033863
  · exact B2033867
  · exact B2033871
  · exact B2033875
  · exact B2033879
  · exact B2033883
  · exact B2033887
  · exact B2033891
  · exact B2033895
  · exact B2033899
  · exact B2033903
  · exact B2033907
  · exact B2033911
  · exact B2033915
  · exact B2033919
  · exact B2033923
  · exact B2033927
  · exact B2033931
  · exact B2033935
  · exact B2033939
  · exact B2033943
  · exact B2033947
  · exact B2033951
  · exact B2033955
  · exact B2033959
  · exact B2033963
  · exact B2033967
  · exact B2033971
  · exact B2033975
  · exact B2033979
  · exact B2033983
  · exact B2033987
  · exact B2033991
  · exact B2033995
  · exact B2033999
  · exact B2034003
  · exact B2034007
  · exact B2034011
  · exact B2034015
  · exact B2034019
  · exact B2034023
  · exact B2034027
  · exact B2034031
  · exact B2034035
  · exact B2034039
  · exact B2034043
  · exact B2034047
  · exact B2034051
  · exact B2034055
  · exact B2034059
  · exact B2034063
  · exact B2034067
  · exact B2034071
  · exact B2034075
  · exact B2034079
  · exact B2034083
  · exact B2034087
  · exact B2034091
  · exact B2034095
  · exact B2034099
  · exact B2034103
  · exact B2034107
  · exact B2034111
  · exact B2034115
  · exact B2034119
  · exact B2034123
  · exact B2034127
  · exact B2034131
  · exact B2034135
  · exact B2034139
  · exact B2034143
  · exact B2034147
  · exact B2034151
  · exact B2034155
  · exact B2034159
  · exact B2034163
  · exact B2034167
  · exact B2034171
  · exact B2034175
  · exact B2034179
  · exact B2034183
  · exact B2034187
  · exact B2034191
  · exact B2034195
  · exact B2034199
  · exact B2034203
  · exact B2034207
  · exact B2034211
  · exact B2034215
  · exact B2034219
  · exact B2034223
  · exact B2034227
  · exact B2034231
  · exact B2034235
  · exact B2034239
  · exact B2034243
  · exact B2034247
  · exact B2034251
  · exact B2034255
  · exact B2034259
  · exact B2034263
  · exact B2034267
  · exact B2034271
  · exact B2034275
  · exact B2034279
  · exact B2034283
  · exact B2034287
  · exact B2034291
  · exact B2034295
  · exact B2034299
  · exact B2034303
  · exact B2034307
  · exact B2034311
  · exact B2034315
  · exact B2034319
  · exact B2034323
  · exact B2034327
  · exact B2034331
  · exact B2034335
  · exact B2034339
  · exact B2034343
  · exact B2034347
  · exact B2034351
  · exact B2034355
  · exact B2034359
  · exact B2034363
  · exact B2034367
  · exact B2034371
  · exact B2034375
  · exact B2034379
  · exact B2034383
  · exact B2034387
  · exact B2034391
  · exact B2034395
  · exact B2034399
  · exact B2034403
  · exact B2034407
  · exact B2034411
  · exact B2034415
  · exact B2034419
  · exact B2034423
  · exact B2034427
  · exact B2034431
  · exact B2034435
  · exact B2034439
  · exact B2034443
  · exact B2034447
  · exact B2034451
  · exact B2034455
  · exact B2034459
  · exact B2034463
  · exact B2034467
  · exact B2034471
  · exact B2034475
  · exact B2034479
  · exact B2034483
  · exact B2034487
  · exact B2034491
  · exact B2034495
  · exact B2034499
  · exact B2034503
  · exact B2034507
  · exact B2034511
  · exact B2034515
  · exact B2034519
  · exact B2034523
  · exact B2034527
  · exact B2034531
  · exact B2034535
  · exact B2034539
  · exact B2034543
  · exact B2034547
  · exact B2034551
  · exact B2034555
  · exact B2034559
  · exact B2034563
  · exact B2034567
  · exact B2034571
  · exact B2034575
  · exact B2034579
  · exact B2034583
  · exact B2034587
  · exact B2034591
  · exact B2034595
  · exact B2034599
  · exact B2034603
  · exact B2034607
  · exact B2034611
  · exact B2034615
  · exact B2034619
  · exact B2034623
  · exact B2034627
  · exact B2034631
  · exact B2034635
  · exact B2034639
  · exact B2034643
  · exact B2034647
  · exact B2034651
  · exact B2034655
  · exact B2034659
  · exact B2034663
  · exact B2034667
  · exact B2034671
  · exact B2034675
  · exact B2034679
  · exact B2034683
  · exact B2034687
  · exact B2034691
  · exact B2034695
  · exact B2034699
  · exact B2034703
  · exact B2034707
  · exact B2034711
  · exact B2034715
  · exact B2034719
  · exact B2034723
  · exact B2034727
  · exact B2034731
  · exact B2034735
  · exact B2034739
  · exact B2034743
  · exact B2034747
  · exact B2034751
  · exact B2034755
  · exact B2034759
  · exact B2034763
  · exact B2034767
  · exact B2034771
  · exact B2034775
  · exact B2034779
  · exact B2034783
  · exact B2034787
  · exact B2034791
  · exact B2034795
  · exact B2034799
  · exact B2034803
  · exact B2034807
  · exact B2034811
  · exact B2034815
  · exact B2034819
  · exact B2034823
  · exact B2034827
  · exact B2034831
  · exact B2034835
  · exact B2034839
  · exact B2034843
  · exact B2034847
  · exact B2034851
  · exact B2034855
  · exact B2034859
  · exact B2034863
  · exact B2034867
  · exact B2034871
  · exact B2034875
  · exact B2034879
  · exact B2034883
  · exact B2034887
  · exact B2034891
  · exact B2034895
  · exact B2034899
  · exact B2034903
  · exact B2034907
  · exact B2034911
  · exact B2034915
  · exact B2034919
  · exact B2034923
  · exact B2034927
  · exact B2034931
  · exact B2034935
  · exact B2034939
  · exact B2034943
  · exact B2034947
  · exact B2034951
  · exact B2034955
  · exact B2034959
  · exact B2034963
  · exact B2034967
  · exact B2034971
  · exact B2034975
  · exact B2034979
  · exact B2034983
  · exact B2034987
  · exact B2034991
  · exact B2034995
  · exact B2034999
  · exact B2035003
  · exact B2035007
  · exact B2035011
  · exact B2035015
  · exact B2035019
  · exact B2035023
  · exact B2035027
  · exact B2035031
  · exact B2035035
  · exact B2035039
  · exact B2035043
  · exact B2035047
  · exact B2035051
  · exact B2035055
  · exact B2035059
  · exact B2035063
  · exact B2035067
  · exact B2035071
  · exact B2035075
  · exact B2035079
  · exact B2035083
  · exact B2035087
  · exact B2035091
  · exact B2035095
  · exact B2035099
  · exact B2035103
  · exact B2035107
  · exact B2035111
  · exact B2035115
  · exact B2035119
  · exact B2035123
  · exact B2035127
  · exact B2035131
  · exact B2035135
  · exact B2035139
  · exact B2035143
  · exact B2035147
  · exact B2035151
  · exact B2035155
  · exact B2035159
  · exact B2035163
  · exact B2035167
  · exact B2035171
  · exact B2035175
  · exact B2035179
  · exact B2035183
  · exact B2035187
  · exact B2035191
  · exact B2035195
  · exact B2035199
  · exact B2035203
  · exact B2035207
  · exact B2035211
  · exact B2035215
  · exact B2035219
  · exact B2035223
  · exact B2035227
  · exact B2035231
  · exact B2035235
  · exact B2035239
  · exact B2035243
  · exact B2035247
  · exact B2035251
  · exact B2035255
  · exact B2035259
  · exact B2035263
  · exact B2035267
  · exact B2035271
  · exact B2035275
  · exact B2035279
  · exact B2035283
  · exact B2035287
  · exact B2035291
  · exact B2035295
  · exact B2035299
  · exact B2035303
  · exact B2035307
  · exact B2035311
  · exact B2035315
  · exact B2035319
  · exact B2035323
  · exact B2035327
  · exact B2035331
  · exact B2035335
  · exact B2035339
  · exact B2035343
  · exact B2035347
  · exact B2035351
  · exact B2035355
  · exact B2035359
  · exact B2035363
  · exact B2035367
  · exact B2035371
  · exact B2035375
  · exact B2035379
  · exact B2035383
  · exact B2035387
  · exact B2035391
  · exact B2035395
  · exact B2035399
  · exact B2035403
  · exact B2035407
  · exact B2035411
  · exact B2035415
  · exact B2035419
  · exact B2035423
  · exact B2035427
  · exact B2035431
  · exact B2035435
theorem solution (m : ℕ) (hlo : 2033435 ≤ m) (hhi : m ≤ 2035435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 508358 ≤ j := by omega
    have hj2 : j ≤ 508858 := by omega
    have hb : Blo 2033435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
