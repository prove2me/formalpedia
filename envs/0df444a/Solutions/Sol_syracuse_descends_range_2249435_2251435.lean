-- Prove2me | solution 1 for syracuse_descends_range_2249435_2251435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:06.370684+00:00
-- url     : https://prove2.me/submissions/44d0e5f8-2da8-45e5-8b4d-c652e2813003

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

theorem B5693885 : Blo 2249435 5693885 := bbase (se 3 (by rfl) ⟨1067603, by rfl⟩ : syracuseStep 5693885 = 2135207) (by norm_num)
theorem B3795923 : Blo 2249435 3795923 := bstep (se 1 (by rfl) ⟨2846942, by rfl⟩ : syracuseStep 3795923 = 5693885) B5693885
theorem B2530615 : Blo 2249435 2530615 := bstep (se 1 (by rfl) ⟨1897961, by rfl⟩ : syracuseStep 2530615 = 3795923) B3795923
theorem B3374153 : Blo 2249435 3374153 := bstep (se 2 (by rfl) ⟨1265307, by rfl⟩ : syracuseStep 3374153 = 2530615) B2530615
theorem B2249435 : Blo 2249435 2249435 := bstep (se 1 (by rfl) ⟨1687076, by rfl⟩ : syracuseStep 2249435 = 3374153) B3374153
theorem B4270421 : Blo 2249435 4270421 := bbase (se 10 (by rfl) ⟨6255, by rfl⟩ : syracuseStep 4270421 = 12511) (by norm_num)
theorem B11387789 : Blo 2249435 11387789 := bstep (se 3 (by rfl) ⟨2135210, by rfl⟩ : syracuseStep 11387789 = 4270421) B4270421
theorem B7591859 : Blo 2249435 7591859 := bstep (se 1 (by rfl) ⟨5693894, by rfl⟩ : syracuseStep 7591859 = 11387789) B11387789
theorem B5061239 : Blo 2249435 5061239 := bstep (se 1 (by rfl) ⟨3795929, by rfl⟩ : syracuseStep 5061239 = 7591859) B7591859
theorem B3374159 : Blo 2249435 3374159 := bstep (se 1 (by rfl) ⟨2530619, by rfl⟩ : syracuseStep 3374159 = 5061239) B5061239
theorem B2249439 : Blo 2249435 2249439 := bstep (se 1 (by rfl) ⟨1687079, by rfl⟩ : syracuseStep 2249439 = 3374159) B3374159
theorem B3374165 : Blo 2249435 3374165 := bbase (se 8 (by rfl) ⟨19770, by rfl⟩ : syracuseStep 3374165 = 39541) (by norm_num)
theorem B2249443 : Blo 2249435 2249443 := bstep (se 1 (by rfl) ⟨1687082, by rfl⟩ : syracuseStep 2249443 = 3374165) B3374165
theorem B14412725 : Blo 2249435 14412725 := bbase (se 5 (by rfl) ⟨675596, by rfl⟩ : syracuseStep 14412725 = 1351193) (by norm_num)
theorem B9608483 : Blo 2249435 9608483 := bstep (se 1 (by rfl) ⟨7206362, by rfl⟩ : syracuseStep 9608483 = 14412725) B14412725
theorem B6405655 : Blo 2249435 6405655 := bstep (se 1 (by rfl) ⟨4804241, by rfl⟩ : syracuseStep 6405655 = 9608483) B9608483
theorem B8540873 : Blo 2249435 8540873 := bstep (se 2 (by rfl) ⟨3202827, by rfl⟩ : syracuseStep 8540873 = 6405655) B6405655
theorem B5693915 : Blo 2249435 5693915 := bstep (se 1 (by rfl) ⟨4270436, by rfl⟩ : syracuseStep 5693915 = 8540873) B8540873
theorem B3795943 : Blo 2249435 3795943 := bstep (se 1 (by rfl) ⟨2846957, by rfl⟩ : syracuseStep 3795943 = 5693915) B5693915
theorem B5061257 : Blo 2249435 5061257 := bstep (se 2 (by rfl) ⟨1897971, by rfl⟩ : syracuseStep 5061257 = 3795943) B3795943
theorem B3374171 : Blo 2249435 3374171 := bstep (se 1 (by rfl) ⟨2530628, by rfl⟩ : syracuseStep 3374171 = 5061257) B5061257
theorem B2249447 : Blo 2249435 2249447 := bstep (se 1 (by rfl) ⟨1687085, by rfl⟩ : syracuseStep 2249447 = 3374171) B3374171
theorem B2530633 : Blo 2249435 2530633 := bbase (se 2 (by rfl) ⟨948987, by rfl⟩ : syracuseStep 2530633 = 1897975) (by norm_num)
theorem B3374177 : Blo 2249435 3374177 := bstep (se 2 (by rfl) ⟨1265316, by rfl⟩ : syracuseStep 3374177 = 2530633) B2530633
theorem B2249451 : Blo 2249435 2249451 := bstep (se 1 (by rfl) ⟨1687088, by rfl⟩ : syracuseStep 2249451 = 3374177) B3374177
theorem B5771621 : Blo 2249435 5771621 := bbase (se 4 (by rfl) ⟨541089, by rfl⟩ : syracuseStep 5771621 = 1082179) (by norm_num)
theorem B3847747 : Blo 2249435 3847747 := bstep (se 1 (by rfl) ⟨2885810, by rfl⟩ : syracuseStep 3847747 = 5771621) B5771621
theorem B5130329 : Blo 2249435 5130329 := bstep (se 2 (by rfl) ⟨1923873, by rfl⟩ : syracuseStep 5130329 = 3847747) B3847747
theorem B54723509 : Blo 2249435 54723509 := bstep (se 5 (by rfl) ⟨2565164, by rfl⟩ : syracuseStep 54723509 = 5130329) B5130329
theorem B36482339 : Blo 2249435 36482339 := bstep (se 1 (by rfl) ⟨27361754, by rfl⟩ : syracuseStep 36482339 = 54723509) B54723509
theorem B24321559 : Blo 2249435 24321559 := bstep (se 1 (by rfl) ⟨18241169, by rfl⟩ : syracuseStep 24321559 = 36482339) B36482339
theorem B32428745 : Blo 2249435 32428745 := bstep (se 2 (by rfl) ⟨12160779, by rfl⟩ : syracuseStep 32428745 = 24321559) B24321559
theorem B21619163 : Blo 2249435 21619163 := bstep (se 1 (by rfl) ⟨16214372, by rfl⟩ : syracuseStep 21619163 = 32428745) B32428745
theorem B14412775 : Blo 2249435 14412775 := bstep (se 1 (by rfl) ⟨10809581, by rfl⟩ : syracuseStep 14412775 = 21619163) B21619163
theorem B19217033 : Blo 2249435 19217033 := bstep (se 2 (by rfl) ⟨7206387, by rfl⟩ : syracuseStep 19217033 = 14412775) B14412775
theorem B12811355 : Blo 2249435 12811355 := bstep (se 1 (by rfl) ⟨9608516, by rfl⟩ : syracuseStep 12811355 = 19217033) B19217033
theorem B8540903 : Blo 2249435 8540903 := bstep (se 1 (by rfl) ⟨6405677, by rfl⟩ : syracuseStep 8540903 = 12811355) B12811355
theorem B5693935 : Blo 2249435 5693935 := bstep (se 1 (by rfl) ⟨4270451, by rfl⟩ : syracuseStep 5693935 = 8540903) B8540903
theorem B7591913 : Blo 2249435 7591913 := bstep (se 2 (by rfl) ⟨2846967, by rfl⟩ : syracuseStep 7591913 = 5693935) B5693935
theorem B5061275 : Blo 2249435 5061275 := bstep (se 1 (by rfl) ⟨3795956, by rfl⟩ : syracuseStep 5061275 = 7591913) B7591913
theorem B3374183 : Blo 2249435 3374183 := bstep (se 1 (by rfl) ⟨2530637, by rfl⟩ : syracuseStep 3374183 = 5061275) B5061275
theorem B2249455 : Blo 2249435 2249455 := bstep (se 1 (by rfl) ⟨1687091, by rfl⟩ : syracuseStep 2249455 = 3374183) B3374183
theorem B3374189 : Blo 2249435 3374189 := bbase (se 3 (by rfl) ⟨632660, by rfl⟩ : syracuseStep 3374189 = 1265321) (by norm_num)
theorem B2249459 : Blo 2249435 2249459 := bstep (se 1 (by rfl) ⟨1687094, by rfl⟩ : syracuseStep 2249459 = 3374189) B3374189
theorem B5061293 : Blo 2249435 5061293 := bbase (se 3 (by rfl) ⟨948992, by rfl⟩ : syracuseStep 5061293 = 1897985) (by norm_num)
theorem B3374195 : Blo 2249435 3374195 := bstep (se 1 (by rfl) ⟨2530646, by rfl⟩ : syracuseStep 3374195 = 5061293) B5061293
theorem B2249463 : Blo 2249435 2249463 := bstep (se 1 (by rfl) ⟨1687097, by rfl⟩ : syracuseStep 2249463 = 3374195) B3374195
theorem B4804285 : Blo 2249435 4804285 := bbase (se 3 (by rfl) ⟨900803, by rfl⟩ : syracuseStep 4804285 = 1801607) (by norm_num)
theorem B6405713 : Blo 2249435 6405713 := bstep (se 2 (by rfl) ⟨2402142, by rfl⟩ : syracuseStep 6405713 = 4804285) B4804285
theorem B4270475 : Blo 2249435 4270475 := bstep (se 1 (by rfl) ⟨3202856, by rfl⟩ : syracuseStep 4270475 = 6405713) B6405713
theorem B2846983 : Blo 2249435 2846983 := bstep (se 1 (by rfl) ⟨2135237, by rfl⟩ : syracuseStep 2846983 = 4270475) B4270475
theorem B3795977 : Blo 2249435 3795977 := bstep (se 2 (by rfl) ⟨1423491, by rfl⟩ : syracuseStep 3795977 = 2846983) B2846983
theorem B2530651 : Blo 2249435 2530651 := bstep (se 1 (by rfl) ⟨1897988, by rfl⟩ : syracuseStep 2530651 = 3795977) B3795977
theorem B3374201 : Blo 2249435 3374201 := bstep (se 2 (by rfl) ⟨1265325, by rfl⟩ : syracuseStep 3374201 = 2530651) B2530651
theorem B2249467 : Blo 2249435 2249467 := bstep (se 1 (by rfl) ⟨1687100, by rfl⟩ : syracuseStep 2249467 = 3374201) B3374201
theorem B4387805 : Blo 2249435 4387805 := bbase (se 3 (by rfl) ⟨822713, by rfl⟩ : syracuseStep 4387805 = 1645427) (by norm_num)
theorem B46803253 : Blo 2249435 46803253 := bstep (se 5 (by rfl) ⟨2193902, by rfl⟩ : syracuseStep 46803253 = 4387805) B4387805
theorem B62404337 : Blo 2249435 62404337 := bstep (se 2 (by rfl) ⟨23401626, by rfl⟩ : syracuseStep 62404337 = 46803253) B46803253
theorem B41602891 : Blo 2249435 41602891 := bstep (se 1 (by rfl) ⟨31202168, by rfl⟩ : syracuseStep 41602891 = 62404337) B62404337
theorem B55470521 : Blo 2249435 55470521 := bstep (se 2 (by rfl) ⟨20801445, by rfl⟩ : syracuseStep 55470521 = 41602891) B41602891
theorem B147921389 : Blo 2249435 147921389 := bstep (se 3 (by rfl) ⟨27735260, by rfl⟩ : syracuseStep 147921389 = 55470521) B55470521
theorem B98614259 : Blo 2249435 98614259 := bstep (se 1 (by rfl) ⟨73960694, by rfl⟩ : syracuseStep 98614259 = 147921389) B147921389
theorem B65742839 : Blo 2249435 65742839 := bstep (se 1 (by rfl) ⟨49307129, by rfl⟩ : syracuseStep 65742839 = 98614259) B98614259
theorem B43828559 : Blo 2249435 43828559 := bstep (se 1 (by rfl) ⟨32871419, by rfl⟩ : syracuseStep 43828559 = 65742839) B65742839
theorem B29219039 : Blo 2249435 29219039 := bstep (se 1 (by rfl) ⟨21914279, by rfl⟩ : syracuseStep 29219039 = 43828559) B43828559
theorem B19479359 : Blo 2249435 19479359 := bstep (se 1 (by rfl) ⟨14609519, by rfl⟩ : syracuseStep 19479359 = 29219039) B29219039
theorem B12986239 : Blo 2249435 12986239 := bstep (se 1 (by rfl) ⟨9739679, by rfl⟩ : syracuseStep 12986239 = 19479359) B19479359
theorem B17314985 : Blo 2249435 17314985 := bstep (se 2 (by rfl) ⟨6493119, by rfl⟩ : syracuseStep 17314985 = 12986239) B12986239
theorem B11543323 : Blo 2249435 11543323 := bstep (se 1 (by rfl) ⟨8657492, by rfl⟩ : syracuseStep 11543323 = 17314985) B17314985
theorem B15391097 : Blo 2249435 15391097 := bstep (se 2 (by rfl) ⟨5771661, by rfl⟩ : syracuseStep 15391097 = 11543323) B11543323
theorem B10260731 : Blo 2249435 10260731 := bstep (se 1 (by rfl) ⟨7695548, by rfl⟩ : syracuseStep 10260731 = 15391097) B15391097
theorem B6840487 : Blo 2249435 6840487 := bstep (se 1 (by rfl) ⟨5130365, by rfl⟩ : syracuseStep 6840487 = 10260731) B10260731
theorem B9120649 : Blo 2249435 9120649 := bstep (se 2 (by rfl) ⟨3420243, by rfl⟩ : syracuseStep 9120649 = 6840487) B6840487
theorem B12160865 : Blo 2249435 12160865 := bstep (se 2 (by rfl) ⟨4560324, by rfl⟩ : syracuseStep 12160865 = 9120649) B9120649
theorem B32428973 : Blo 2249435 32428973 := bstep (se 3 (by rfl) ⟨6080432, by rfl⟩ : syracuseStep 32428973 = 12160865) B12160865
theorem B21619315 : Blo 2249435 21619315 := bstep (se 1 (by rfl) ⟨16214486, by rfl⟩ : syracuseStep 21619315 = 32428973) B32428973
theorem B28825753 : Blo 2249435 28825753 := bstep (se 2 (by rfl) ⟨10809657, by rfl⟩ : syracuseStep 28825753 = 21619315) B21619315
theorem B38434337 : Blo 2249435 38434337 := bstep (se 2 (by rfl) ⟨14412876, by rfl⟩ : syracuseStep 38434337 = 28825753) B28825753
theorem B25622891 : Blo 2249435 25622891 := bstep (se 1 (by rfl) ⟨19217168, by rfl⟩ : syracuseStep 25622891 = 38434337) B38434337
theorem B17081927 : Blo 2249435 17081927 := bstep (se 1 (by rfl) ⟨12811445, by rfl⟩ : syracuseStep 17081927 = 25622891) B25622891
theorem B11387951 : Blo 2249435 11387951 := bstep (se 1 (by rfl) ⟨8540963, by rfl⟩ : syracuseStep 11387951 = 17081927) B17081927
theorem B7591967 : Blo 2249435 7591967 := bstep (se 1 (by rfl) ⟨5693975, by rfl⟩ : syracuseStep 7591967 = 11387951) B11387951
theorem B5061311 : Blo 2249435 5061311 := bstep (se 1 (by rfl) ⟨3795983, by rfl⟩ : syracuseStep 5061311 = 7591967) B7591967
theorem B3374207 : Blo 2249435 3374207 := bstep (se 1 (by rfl) ⟨2530655, by rfl⟩ : syracuseStep 3374207 = 5061311) B5061311
theorem B2249471 : Blo 2249435 2249471 := bstep (se 1 (by rfl) ⟨1687103, by rfl⟩ : syracuseStep 2249471 = 3374207) B3374207
theorem B3374213 : Blo 2249435 3374213 := bbase (se 4 (by rfl) ⟨316332, by rfl⟩ : syracuseStep 3374213 = 632665) (by norm_num)
theorem B2249475 : Blo 2249435 2249475 := bstep (se 1 (by rfl) ⟨1687106, by rfl⟩ : syracuseStep 2249475 = 3374213) B3374213
theorem B3795997 : Blo 2249435 3795997 := bbase (se 3 (by rfl) ⟨711749, by rfl⟩ : syracuseStep 3795997 = 1423499) (by norm_num)
theorem B5061329 : Blo 2249435 5061329 := bstep (se 2 (by rfl) ⟨1897998, by rfl⟩ : syracuseStep 5061329 = 3795997) B3795997
theorem B3374219 : Blo 2249435 3374219 := bstep (se 1 (by rfl) ⟨2530664, by rfl⟩ : syracuseStep 3374219 = 5061329) B5061329
theorem B2249479 : Blo 2249435 2249479 := bstep (se 1 (by rfl) ⟨1687109, by rfl⟩ : syracuseStep 2249479 = 3374219) B3374219
theorem B2530669 : Blo 2249435 2530669 := bbase (se 3 (by rfl) ⟨474500, by rfl⟩ : syracuseStep 2530669 = 949001) (by norm_num)
theorem B3374225 : Blo 2249435 3374225 := bstep (se 2 (by rfl) ⟨1265334, by rfl⟩ : syracuseStep 3374225 = 2530669) B2530669
theorem B2249483 : Blo 2249435 2249483 := bstep (se 1 (by rfl) ⟨1687112, by rfl⟩ : syracuseStep 2249483 = 3374225) B3374225
theorem B7592021 : Blo 2249435 7592021 := bbase (se 8 (by rfl) ⟨44484, by rfl⟩ : syracuseStep 7592021 = 88969) (by norm_num)
theorem B5061347 : Blo 2249435 5061347 := bstep (se 1 (by rfl) ⟨3796010, by rfl⟩ : syracuseStep 5061347 = 7592021) B7592021
theorem B3374231 : Blo 2249435 3374231 := bstep (se 1 (by rfl) ⟨2530673, by rfl⟩ : syracuseStep 3374231 = 5061347) B5061347
theorem B2249487 : Blo 2249435 2249487 := bstep (se 1 (by rfl) ⟨1687115, by rfl⟩ : syracuseStep 2249487 = 3374231) B3374231
theorem B3374237 : Blo 2249435 3374237 := bbase (se 3 (by rfl) ⟨632669, by rfl⟩ : syracuseStep 3374237 = 1265339) (by norm_num)
theorem B2249491 : Blo 2249435 2249491 := bstep (se 1 (by rfl) ⟨1687118, by rfl⟩ : syracuseStep 2249491 = 3374237) B3374237
theorem B5061365 : Blo 2249435 5061365 := bbase (se 5 (by rfl) ⟨237251, by rfl⟩ : syracuseStep 5061365 = 474503) (by norm_num)
theorem B3374243 : Blo 2249435 3374243 := bstep (se 1 (by rfl) ⟨2530682, by rfl⟩ : syracuseStep 3374243 = 5061365) B5061365
theorem B2249495 : Blo 2249435 2249495 := bstep (se 1 (by rfl) ⟨1687121, by rfl⟩ : syracuseStep 2249495 = 3374243) B3374243
theorem B116877653 : Blo 2249435 116877653 := bbase (se 10 (by rfl) ⟨171207, by rfl⟩ : syracuseStep 116877653 = 342415) (by norm_num)
theorem B77918435 : Blo 2249435 77918435 := bstep (se 1 (by rfl) ⟨58438826, by rfl⟩ : syracuseStep 77918435 = 116877653) B116877653
theorem B51945623 : Blo 2249435 51945623 := bstep (se 1 (by rfl) ⟨38959217, by rfl⟩ : syracuseStep 51945623 = 77918435) B77918435
theorem B34630415 : Blo 2249435 34630415 := bstep (se 1 (by rfl) ⟨25972811, by rfl⟩ : syracuseStep 34630415 = 51945623) B51945623
theorem B23086943 : Blo 2249435 23086943 := bstep (se 1 (by rfl) ⟨17315207, by rfl⟩ : syracuseStep 23086943 = 34630415) B34630415
theorem B15391295 : Blo 2249435 15391295 := bstep (se 1 (by rfl) ⟨11543471, by rfl⟩ : syracuseStep 15391295 = 23086943) B23086943
theorem B10260863 : Blo 2249435 10260863 := bstep (se 1 (by rfl) ⟨7695647, by rfl⟩ : syracuseStep 10260863 = 15391295) B15391295
theorem B6840575 : Blo 2249435 6840575 := bstep (se 1 (by rfl) ⟨5130431, by rfl⟩ : syracuseStep 6840575 = 10260863) B10260863
theorem B4560383 : Blo 2249435 4560383 := bstep (se 1 (by rfl) ⟨3420287, by rfl⟩ : syracuseStep 4560383 = 6840575) B6840575
theorem B3040255 : Blo 2249435 3040255 := bstep (se 1 (by rfl) ⟨2280191, by rfl⟩ : syracuseStep 3040255 = 4560383) B4560383
theorem B4053673 : Blo 2249435 4053673 := bstep (se 2 (by rfl) ⟨1520127, by rfl⟩ : syracuseStep 4053673 = 3040255) B3040255
theorem B5404897 : Blo 2249435 5404897 := bstep (se 2 (by rfl) ⟨2026836, by rfl⟩ : syracuseStep 5404897 = 4053673) B4053673
theorem B28826117 : Blo 2249435 28826117 := bstep (se 4 (by rfl) ⟨2702448, by rfl⟩ : syracuseStep 28826117 = 5404897) B5404897
theorem B19217411 : Blo 2249435 19217411 := bstep (se 1 (by rfl) ⟨14413058, by rfl⟩ : syracuseStep 19217411 = 28826117) B28826117
theorem B12811607 : Blo 2249435 12811607 := bstep (se 1 (by rfl) ⟨9608705, by rfl⟩ : syracuseStep 12811607 = 19217411) B19217411
theorem B8541071 : Blo 2249435 8541071 := bstep (se 1 (by rfl) ⟨6405803, by rfl⟩ : syracuseStep 8541071 = 12811607) B12811607
theorem B5694047 : Blo 2249435 5694047 := bstep (se 1 (by rfl) ⟨4270535, by rfl⟩ : syracuseStep 5694047 = 8541071) B8541071
theorem B3796031 : Blo 2249435 3796031 := bstep (se 1 (by rfl) ⟨2847023, by rfl⟩ : syracuseStep 3796031 = 5694047) B5694047
theorem B2530687 : Blo 2249435 2530687 := bstep (se 1 (by rfl) ⟨1898015, by rfl⟩ : syracuseStep 2530687 = 3796031) B3796031
theorem B3374249 : Blo 2249435 3374249 := bstep (se 2 (by rfl) ⟨1265343, by rfl⟩ : syracuseStep 3374249 = 2530687) B2530687
theorem B2249499 : Blo 2249435 2249499 := bstep (se 1 (by rfl) ⟨1687124, by rfl⟩ : syracuseStep 2249499 = 3374249) B3374249
theorem B2885873 : Blo 2249435 2885873 := bbase (se 2 (by rfl) ⟨1082202, by rfl⟩ : syracuseStep 2885873 = 2164405) (by norm_num)
theorem B7695661 : Blo 2249435 7695661 := bstep (se 3 (by rfl) ⟨1442936, by rfl⟩ : syracuseStep 7695661 = 2885873) B2885873
theorem B10260881 : Blo 2249435 10260881 := bstep (se 2 (by rfl) ⟨3847830, by rfl⟩ : syracuseStep 10260881 = 7695661) B7695661
theorem B6840587 : Blo 2249435 6840587 := bstep (se 1 (by rfl) ⟨5130440, by rfl⟩ : syracuseStep 6840587 = 10260881) B10260881
theorem B4560391 : Blo 2249435 4560391 := bstep (se 1 (by rfl) ⟨3420293, by rfl⟩ : syracuseStep 4560391 = 6840587) B6840587
theorem B6080521 : Blo 2249435 6080521 := bstep (se 2 (by rfl) ⟨2280195, by rfl⟩ : syracuseStep 6080521 = 4560391) B4560391
theorem B8107361 : Blo 2249435 8107361 := bstep (se 2 (by rfl) ⟨3040260, by rfl⟩ : syracuseStep 8107361 = 6080521) B6080521
theorem B5404907 : Blo 2249435 5404907 := bstep (se 1 (by rfl) ⟨4053680, by rfl⟩ : syracuseStep 5404907 = 8107361) B8107361
theorem B3603271 : Blo 2249435 3603271 := bstep (se 1 (by rfl) ⟨2702453, by rfl⟩ : syracuseStep 3603271 = 5404907) B5404907
theorem B4804361 : Blo 2249435 4804361 := bstep (se 2 (by rfl) ⟨1801635, by rfl⟩ : syracuseStep 4804361 = 3603271) B3603271
theorem B3202907 : Blo 2249435 3202907 := bstep (se 1 (by rfl) ⟨2402180, by rfl⟩ : syracuseStep 3202907 = 4804361) B4804361
theorem B8541085 : Blo 2249435 8541085 := bstep (se 3 (by rfl) ⟨1601453, by rfl⟩ : syracuseStep 8541085 = 3202907) B3202907
theorem B11388113 : Blo 2249435 11388113 := bstep (se 2 (by rfl) ⟨4270542, by rfl⟩ : syracuseStep 11388113 = 8541085) B8541085
theorem B7592075 : Blo 2249435 7592075 := bstep (se 1 (by rfl) ⟨5694056, by rfl⟩ : syracuseStep 7592075 = 11388113) B11388113
theorem B5061383 : Blo 2249435 5061383 := bstep (se 1 (by rfl) ⟨3796037, by rfl⟩ : syracuseStep 5061383 = 7592075) B7592075
theorem B3374255 : Blo 2249435 3374255 := bstep (se 1 (by rfl) ⟨2530691, by rfl⟩ : syracuseStep 3374255 = 5061383) B5061383
theorem B2249503 : Blo 2249435 2249503 := bstep (se 1 (by rfl) ⟨1687127, by rfl⟩ : syracuseStep 2249503 = 3374255) B3374255
theorem B3374261 : Blo 2249435 3374261 := bbase (se 5 (by rfl) ⟨158168, by rfl⟩ : syracuseStep 3374261 = 316337) (by norm_num)
theorem B2249507 : Blo 2249435 2249507 := bstep (se 1 (by rfl) ⟨1687130, by rfl⟩ : syracuseStep 2249507 = 3374261) B3374261
theorem B5694077 : Blo 2249435 5694077 := bbase (se 3 (by rfl) ⟨1067639, by rfl⟩ : syracuseStep 5694077 = 2135279) (by norm_num)
theorem B3796051 : Blo 2249435 3796051 := bstep (se 1 (by rfl) ⟨2847038, by rfl⟩ : syracuseStep 3796051 = 5694077) B5694077
theorem B5061401 : Blo 2249435 5061401 := bstep (se 2 (by rfl) ⟨1898025, by rfl⟩ : syracuseStep 5061401 = 3796051) B3796051
theorem B3374267 : Blo 2249435 3374267 := bstep (se 1 (by rfl) ⟨2530700, by rfl⟩ : syracuseStep 3374267 = 5061401) B5061401
theorem B2249511 : Blo 2249435 2249511 := bstep (se 1 (by rfl) ⟨1687133, by rfl⟩ : syracuseStep 2249511 = 3374267) B3374267
theorem B2530705 : Blo 2249435 2530705 := bbase (se 2 (by rfl) ⟨949014, by rfl⟩ : syracuseStep 2530705 = 1898029) (by norm_num)
theorem B3374273 : Blo 2249435 3374273 := bstep (se 2 (by rfl) ⟨1265352, by rfl⟩ : syracuseStep 3374273 = 2530705) B2530705
theorem B2249515 : Blo 2249435 2249515 := bstep (se 1 (by rfl) ⟨1687136, by rfl⟩ : syracuseStep 2249515 = 3374273) B3374273
theorem B4270573 : Blo 2249435 4270573 := bbase (se 3 (by rfl) ⟨800732, by rfl⟩ : syracuseStep 4270573 = 1601465) (by norm_num)
theorem B5694097 : Blo 2249435 5694097 := bstep (se 2 (by rfl) ⟨2135286, by rfl⟩ : syracuseStep 5694097 = 4270573) B4270573
theorem B7592129 : Blo 2249435 7592129 := bstep (se 2 (by rfl) ⟨2847048, by rfl⟩ : syracuseStep 7592129 = 5694097) B5694097
theorem B5061419 : Blo 2249435 5061419 := bstep (se 1 (by rfl) ⟨3796064, by rfl⟩ : syracuseStep 5061419 = 7592129) B7592129
theorem B3374279 : Blo 2249435 3374279 := bstep (se 1 (by rfl) ⟨2530709, by rfl⟩ : syracuseStep 3374279 = 5061419) B5061419
theorem B2249519 : Blo 2249435 2249519 := bstep (se 1 (by rfl) ⟨1687139, by rfl⟩ : syracuseStep 2249519 = 3374279) B3374279
theorem B3374285 : Blo 2249435 3374285 := bbase (se 3 (by rfl) ⟨632678, by rfl⟩ : syracuseStep 3374285 = 1265357) (by norm_num)
theorem B2249523 : Blo 2249435 2249523 := bstep (se 1 (by rfl) ⟨1687142, by rfl⟩ : syracuseStep 2249523 = 3374285) B3374285
theorem B5061437 : Blo 2249435 5061437 := bbase (se 3 (by rfl) ⟨949019, by rfl⟩ : syracuseStep 5061437 = 1898039) (by norm_num)
theorem B3374291 : Blo 2249435 3374291 := bstep (se 1 (by rfl) ⟨2530718, by rfl⟩ : syracuseStep 3374291 = 5061437) B5061437
theorem B2249527 : Blo 2249435 2249527 := bstep (se 1 (by rfl) ⟨1687145, by rfl⟩ : syracuseStep 2249527 = 3374291) B3374291
theorem B3796085 : Blo 2249435 3796085 := bbase (se 5 (by rfl) ⟨177941, by rfl⟩ : syracuseStep 3796085 = 355883) (by norm_num)
theorem B2530723 : Blo 2249435 2530723 := bstep (se 1 (by rfl) ⟨1898042, by rfl⟩ : syracuseStep 2530723 = 3796085) B3796085
theorem B3374297 : Blo 2249435 3374297 := bstep (se 2 (by rfl) ⟨1265361, by rfl⟩ : syracuseStep 3374297 = 2530723) B2530723
theorem B2249531 : Blo 2249435 2249531 := bstep (se 1 (by rfl) ⟨1687148, by rfl⟩ : syracuseStep 2249531 = 3374297) B3374297
theorem B4804429 : Blo 2249435 4804429 := bbase (se 3 (by rfl) ⟨900830, by rfl⟩ : syracuseStep 4804429 = 1801661) (by norm_num)
theorem B6405905 : Blo 2249435 6405905 := bstep (se 2 (by rfl) ⟨2402214, by rfl⟩ : syracuseStep 6405905 = 4804429) B4804429
theorem B17082413 : Blo 2249435 17082413 := bstep (se 3 (by rfl) ⟨3202952, by rfl⟩ : syracuseStep 17082413 = 6405905) B6405905
theorem B11388275 : Blo 2249435 11388275 := bstep (se 1 (by rfl) ⟨8541206, by rfl⟩ : syracuseStep 11388275 = 17082413) B17082413
theorem B7592183 : Blo 2249435 7592183 := bstep (se 1 (by rfl) ⟨5694137, by rfl⟩ : syracuseStep 7592183 = 11388275) B11388275
theorem B5061455 : Blo 2249435 5061455 := bstep (se 1 (by rfl) ⟨3796091, by rfl⟩ : syracuseStep 5061455 = 7592183) B7592183
theorem B3374303 : Blo 2249435 3374303 := bstep (se 1 (by rfl) ⟨2530727, by rfl⟩ : syracuseStep 3374303 = 5061455) B5061455
theorem B2249535 : Blo 2249435 2249535 := bstep (se 1 (by rfl) ⟨1687151, by rfl⟩ : syracuseStep 2249535 = 3374303) B3374303
theorem B3374309 : Blo 2249435 3374309 := bbase (se 4 (by rfl) ⟨316341, by rfl⟩ : syracuseStep 3374309 = 632683) (by norm_num)
theorem B2249539 : Blo 2249435 2249539 := bstep (se 1 (by rfl) ⟨1687154, by rfl⟩ : syracuseStep 2249539 = 3374309) B3374309
theorem B24322517 : Blo 2249435 24322517 := bbase (se 7 (by rfl) ⟨285029, by rfl⟩ : syracuseStep 24322517 = 570059) (by norm_num)
theorem B16215011 : Blo 2249435 16215011 := bstep (se 1 (by rfl) ⟨12161258, by rfl⟩ : syracuseStep 16215011 = 24322517) B24322517
theorem B10810007 : Blo 2249435 10810007 := bstep (se 1 (by rfl) ⟨8107505, by rfl⟩ : syracuseStep 10810007 = 16215011) B16215011
theorem B7206671 : Blo 2249435 7206671 := bstep (se 1 (by rfl) ⟨5405003, by rfl⟩ : syracuseStep 7206671 = 10810007) B10810007
theorem B4804447 : Blo 2249435 4804447 := bstep (se 1 (by rfl) ⟨3603335, by rfl⟩ : syracuseStep 4804447 = 7206671) B7206671
theorem B6405929 : Blo 2249435 6405929 := bstep (se 2 (by rfl) ⟨2402223, by rfl⟩ : syracuseStep 6405929 = 4804447) B4804447
theorem B4270619 : Blo 2249435 4270619 := bstep (se 1 (by rfl) ⟨3202964, by rfl⟩ : syracuseStep 4270619 = 6405929) B6405929
theorem B2847079 : Blo 2249435 2847079 := bstep (se 1 (by rfl) ⟨2135309, by rfl⟩ : syracuseStep 2847079 = 4270619) B4270619
theorem B3796105 : Blo 2249435 3796105 := bstep (se 2 (by rfl) ⟨1423539, by rfl⟩ : syracuseStep 3796105 = 2847079) B2847079
theorem B5061473 : Blo 2249435 5061473 := bstep (se 2 (by rfl) ⟨1898052, by rfl⟩ : syracuseStep 5061473 = 3796105) B3796105
theorem B3374315 : Blo 2249435 3374315 := bstep (se 1 (by rfl) ⟨2530736, by rfl⟩ : syracuseStep 3374315 = 5061473) B5061473
theorem B2249543 : Blo 2249435 2249543 := bstep (se 1 (by rfl) ⟨1687157, by rfl⟩ : syracuseStep 2249543 = 3374315) B3374315
theorem B2530741 : Blo 2249435 2530741 := bbase (se 5 (by rfl) ⟨118628, by rfl⟩ : syracuseStep 2530741 = 237257) (by norm_num)
theorem B3374321 : Blo 2249435 3374321 := bstep (se 2 (by rfl) ⟨1265370, by rfl⟩ : syracuseStep 3374321 = 2530741) B2530741
theorem B2249547 : Blo 2249435 2249547 := bstep (se 1 (by rfl) ⟨1687160, by rfl⟩ : syracuseStep 2249547 = 3374321) B3374321
theorem B2847089 : Blo 2249435 2847089 := bbase (se 2 (by rfl) ⟨1067658, by rfl⟩ : syracuseStep 2847089 = 2135317) (by norm_num)
theorem B7592237 : Blo 2249435 7592237 := bstep (se 3 (by rfl) ⟨1423544, by rfl⟩ : syracuseStep 7592237 = 2847089) B2847089
theorem B5061491 : Blo 2249435 5061491 := bstep (se 1 (by rfl) ⟨3796118, by rfl⟩ : syracuseStep 5061491 = 7592237) B7592237
theorem B3374327 : Blo 2249435 3374327 := bstep (se 1 (by rfl) ⟨2530745, by rfl⟩ : syracuseStep 3374327 = 5061491) B5061491
theorem B2249551 : Blo 2249435 2249551 := bstep (se 1 (by rfl) ⟨1687163, by rfl⟩ : syracuseStep 2249551 = 3374327) B3374327
theorem B3374333 : Blo 2249435 3374333 := bbase (se 3 (by rfl) ⟨632687, by rfl⟩ : syracuseStep 3374333 = 1265375) (by norm_num)
theorem B2249555 : Blo 2249435 2249555 := bstep (se 1 (by rfl) ⟨1687166, by rfl⟩ : syracuseStep 2249555 = 3374333) B3374333
theorem B5061509 : Blo 2249435 5061509 := bbase (se 4 (by rfl) ⟨474516, by rfl⟩ : syracuseStep 5061509 = 949033) (by norm_num)
theorem B3374339 : Blo 2249435 3374339 := bstep (se 1 (by rfl) ⟨2530754, by rfl⟩ : syracuseStep 3374339 = 5061509) B5061509
theorem B2249559 : Blo 2249435 2249559 := bstep (se 1 (by rfl) ⟨1687169, by rfl⟩ : syracuseStep 2249559 = 3374339) B3374339
theorem B2402245 : Blo 2249435 2402245 := bbase (se 4 (by rfl) ⟨225210, by rfl⟩ : syracuseStep 2402245 = 450421) (by norm_num)
theorem B3202993 : Blo 2249435 3202993 := bstep (se 2 (by rfl) ⟨1201122, by rfl⟩ : syracuseStep 3202993 = 2402245) B2402245
theorem B4270657 : Blo 2249435 4270657 := bstep (se 2 (by rfl) ⟨1601496, by rfl⟩ : syracuseStep 4270657 = 3202993) B3202993
theorem B5694209 : Blo 2249435 5694209 := bstep (se 2 (by rfl) ⟨2135328, by rfl⟩ : syracuseStep 5694209 = 4270657) B4270657
theorem B3796139 : Blo 2249435 3796139 := bstep (se 1 (by rfl) ⟨2847104, by rfl⟩ : syracuseStep 3796139 = 5694209) B5694209
theorem B2530759 : Blo 2249435 2530759 := bstep (se 1 (by rfl) ⟨1898069, by rfl⟩ : syracuseStep 2530759 = 3796139) B3796139
theorem B3374345 : Blo 2249435 3374345 := bstep (se 2 (by rfl) ⟨1265379, by rfl⟩ : syracuseStep 3374345 = 2530759) B2530759
theorem B2249563 : Blo 2249435 2249563 := bstep (se 1 (by rfl) ⟨1687172, by rfl⟩ : syracuseStep 2249563 = 3374345) B3374345
theorem B11388437 : Blo 2249435 11388437 := bbase (se 6 (by rfl) ⟨266916, by rfl⟩ : syracuseStep 11388437 = 533833) (by norm_num)
theorem B7592291 : Blo 2249435 7592291 := bstep (se 1 (by rfl) ⟨5694218, by rfl⟩ : syracuseStep 7592291 = 11388437) B11388437
theorem B5061527 : Blo 2249435 5061527 := bstep (se 1 (by rfl) ⟨3796145, by rfl⟩ : syracuseStep 5061527 = 7592291) B7592291
theorem B3374351 : Blo 2249435 3374351 := bstep (se 1 (by rfl) ⟨2530763, by rfl⟩ : syracuseStep 3374351 = 5061527) B5061527
theorem B2249567 : Blo 2249435 2249567 := bstep (se 1 (by rfl) ⟨1687175, by rfl⟩ : syracuseStep 2249567 = 3374351) B3374351
theorem B3374357 : Blo 2249435 3374357 := bbase (se 6 (by rfl) ⟨79086, by rfl⟩ : syracuseStep 3374357 = 158173) (by norm_num)
theorem B2249571 : Blo 2249435 2249571 := bstep (se 1 (by rfl) ⟨1687178, by rfl⟩ : syracuseStep 2249571 = 3374357) B3374357
theorem B12161429 : Blo 2249435 12161429 := bbase (se 6 (by rfl) ⟨285033, by rfl⟩ : syracuseStep 12161429 = 570067) (by norm_num)
theorem B8107619 : Blo 2249435 8107619 := bstep (se 1 (by rfl) ⟨6080714, by rfl⟩ : syracuseStep 8107619 = 12161429) B12161429
theorem B21620317 : Blo 2249435 21620317 := bstep (se 3 (by rfl) ⟨4053809, by rfl⟩ : syracuseStep 21620317 = 8107619) B8107619
theorem B28827089 : Blo 2249435 28827089 := bstep (se 2 (by rfl) ⟨10810158, by rfl⟩ : syracuseStep 28827089 = 21620317) B21620317
theorem B19218059 : Blo 2249435 19218059 := bstep (se 1 (by rfl) ⟨14413544, by rfl⟩ : syracuseStep 19218059 = 28827089) B28827089
theorem B12812039 : Blo 2249435 12812039 := bstep (se 1 (by rfl) ⟨9609029, by rfl⟩ : syracuseStep 12812039 = 19218059) B19218059
theorem B8541359 : Blo 2249435 8541359 := bstep (se 1 (by rfl) ⟨6406019, by rfl⟩ : syracuseStep 8541359 = 12812039) B12812039
theorem B5694239 : Blo 2249435 5694239 := bstep (se 1 (by rfl) ⟨4270679, by rfl⟩ : syracuseStep 5694239 = 8541359) B8541359
theorem B3796159 : Blo 2249435 3796159 := bstep (se 1 (by rfl) ⟨2847119, by rfl⟩ : syracuseStep 3796159 = 5694239) B5694239
theorem B5061545 : Blo 2249435 5061545 := bstep (se 2 (by rfl) ⟨1898079, by rfl⟩ : syracuseStep 5061545 = 3796159) B3796159
theorem B3374363 : Blo 2249435 3374363 := bstep (se 1 (by rfl) ⟨2530772, by rfl⟩ : syracuseStep 3374363 = 5061545) B5061545
theorem B2249575 : Blo 2249435 2249575 := bstep (se 1 (by rfl) ⟨1687181, by rfl⟩ : syracuseStep 2249575 = 3374363) B3374363
theorem B2530777 : Blo 2249435 2530777 := bbase (se 2 (by rfl) ⟨949041, by rfl⟩ : syracuseStep 2530777 = 1898083) (by norm_num)
theorem B3374369 : Blo 2249435 3374369 := bstep (se 2 (by rfl) ⟨1265388, by rfl⟩ : syracuseStep 3374369 = 2530777) B2530777
theorem B2249579 : Blo 2249435 2249579 := bstep (se 1 (by rfl) ⟨1687184, by rfl⟩ : syracuseStep 2249579 = 3374369) B3374369
theorem B3203021 : Blo 2249435 3203021 := bbase (se 3 (by rfl) ⟨600566, by rfl⟩ : syracuseStep 3203021 = 1201133) (by norm_num)
theorem B8541389 : Blo 2249435 8541389 := bstep (se 3 (by rfl) ⟨1601510, by rfl⟩ : syracuseStep 8541389 = 3203021) B3203021
theorem B5694259 : Blo 2249435 5694259 := bstep (se 1 (by rfl) ⟨4270694, by rfl⟩ : syracuseStep 5694259 = 8541389) B8541389
theorem B7592345 : Blo 2249435 7592345 := bstep (se 2 (by rfl) ⟨2847129, by rfl⟩ : syracuseStep 7592345 = 5694259) B5694259
theorem B5061563 : Blo 2249435 5061563 := bstep (se 1 (by rfl) ⟨3796172, by rfl⟩ : syracuseStep 5061563 = 7592345) B7592345
theorem B3374375 : Blo 2249435 3374375 := bstep (se 1 (by rfl) ⟨2530781, by rfl⟩ : syracuseStep 3374375 = 5061563) B5061563
theorem B2249583 : Blo 2249435 2249583 := bstep (se 1 (by rfl) ⟨1687187, by rfl⟩ : syracuseStep 2249583 = 3374375) B3374375
theorem B3374381 : Blo 2249435 3374381 := bbase (se 3 (by rfl) ⟨632696, by rfl⟩ : syracuseStep 3374381 = 1265393) (by norm_num)
theorem B2249587 : Blo 2249435 2249587 := bstep (se 1 (by rfl) ⟨1687190, by rfl⟩ : syracuseStep 2249587 = 3374381) B3374381
theorem B5061581 : Blo 2249435 5061581 := bbase (se 3 (by rfl) ⟨949046, by rfl⟩ : syracuseStep 5061581 = 1898093) (by norm_num)
theorem B3374387 : Blo 2249435 3374387 := bstep (se 1 (by rfl) ⟨2530790, by rfl⟩ : syracuseStep 3374387 = 5061581) B5061581
theorem B2249591 : Blo 2249435 2249591 := bstep (se 1 (by rfl) ⟨1687193, by rfl⟩ : syracuseStep 2249591 = 3374387) B3374387
theorem B2847145 : Blo 2249435 2847145 := bbase (se 2 (by rfl) ⟨1067679, by rfl⟩ : syracuseStep 2847145 = 2135359) (by norm_num)
theorem B3796193 : Blo 2249435 3796193 := bstep (se 2 (by rfl) ⟨1423572, by rfl⟩ : syracuseStep 3796193 = 2847145) B2847145
theorem B2530795 : Blo 2249435 2530795 := bstep (se 1 (by rfl) ⟨1898096, by rfl⟩ : syracuseStep 2530795 = 3796193) B3796193
theorem B3374393 : Blo 2249435 3374393 := bstep (se 2 (by rfl) ⟨1265397, by rfl⟩ : syracuseStep 3374393 = 2530795) B2530795
theorem B2249595 : Blo 2249435 2249595 := bstep (se 1 (by rfl) ⟨1687196, by rfl⟩ : syracuseStep 2249595 = 3374393) B3374393
theorem B2565329 : Blo 2249435 2565329 := bbase (se 2 (by rfl) ⟨961998, by rfl⟩ : syracuseStep 2565329 = 1923997) (by norm_num)
theorem B6840877 : Blo 2249435 6840877 := bstep (se 3 (by rfl) ⟨1282664, by rfl⟩ : syracuseStep 6840877 = 2565329) B2565329
theorem B9121169 : Blo 2249435 9121169 := bstep (se 2 (by rfl) ⟨3420438, by rfl⟩ : syracuseStep 9121169 = 6840877) B6840877
theorem B6080779 : Blo 2249435 6080779 := bstep (se 1 (by rfl) ⟨4560584, by rfl⟩ : syracuseStep 6080779 = 9121169) B9121169
theorem B8107705 : Blo 2249435 8107705 := bstep (se 2 (by rfl) ⟨3040389, by rfl⟩ : syracuseStep 8107705 = 6080779) B6080779
theorem B10810273 : Blo 2249435 10810273 := bstep (se 2 (by rfl) ⟨4053852, by rfl⟩ : syracuseStep 10810273 = 8107705) B8107705
theorem B14413697 : Blo 2249435 14413697 := bstep (se 2 (by rfl) ⟨5405136, by rfl⟩ : syracuseStep 14413697 = 10810273) B10810273
theorem B9609131 : Blo 2249435 9609131 := bstep (se 1 (by rfl) ⟨7206848, by rfl⟩ : syracuseStep 9609131 = 14413697) B14413697
theorem B25624349 : Blo 2249435 25624349 := bstep (se 3 (by rfl) ⟨4804565, by rfl⟩ : syracuseStep 25624349 = 9609131) B9609131
theorem B17082899 : Blo 2249435 17082899 := bstep (se 1 (by rfl) ⟨12812174, by rfl⟩ : syracuseStep 17082899 = 25624349) B25624349
theorem B11388599 : Blo 2249435 11388599 := bstep (se 1 (by rfl) ⟨8541449, by rfl⟩ : syracuseStep 11388599 = 17082899) B17082899
theorem B7592399 : Blo 2249435 7592399 := bstep (se 1 (by rfl) ⟨5694299, by rfl⟩ : syracuseStep 7592399 = 11388599) B11388599
theorem B5061599 : Blo 2249435 5061599 := bstep (se 1 (by rfl) ⟨3796199, by rfl⟩ : syracuseStep 5061599 = 7592399) B7592399
theorem B3374399 : Blo 2249435 3374399 := bstep (se 1 (by rfl) ⟨2530799, by rfl⟩ : syracuseStep 3374399 = 5061599) B5061599
theorem B2249599 : Blo 2249435 2249599 := bstep (se 1 (by rfl) ⟨1687199, by rfl⟩ : syracuseStep 2249599 = 3374399) B3374399
theorem B3374405 : Blo 2249435 3374405 := bbase (se 4 (by rfl) ⟨316350, by rfl⟩ : syracuseStep 3374405 = 632701) (by norm_num)
theorem B2249603 : Blo 2249435 2249603 := bstep (se 1 (by rfl) ⟨1687202, by rfl⟩ : syracuseStep 2249603 = 3374405) B3374405
theorem B3796213 : Blo 2249435 3796213 := bbase (se 5 (by rfl) ⟨177947, by rfl⟩ : syracuseStep 3796213 = 355895) (by norm_num)
theorem B5061617 : Blo 2249435 5061617 := bstep (se 2 (by rfl) ⟨1898106, by rfl⟩ : syracuseStep 5061617 = 3796213) B3796213
theorem B3374411 : Blo 2249435 3374411 := bstep (se 1 (by rfl) ⟨2530808, by rfl⟩ : syracuseStep 3374411 = 5061617) B5061617
theorem B2249607 : Blo 2249435 2249607 := bstep (se 1 (by rfl) ⟨1687205, by rfl⟩ : syracuseStep 2249607 = 3374411) B3374411
theorem B2530813 : Blo 2249435 2530813 := bbase (se 3 (by rfl) ⟨474527, by rfl⟩ : syracuseStep 2530813 = 949055) (by norm_num)
theorem B3374417 : Blo 2249435 3374417 := bstep (se 2 (by rfl) ⟨1265406, by rfl⟩ : syracuseStep 3374417 = 2530813) B2530813
theorem B2249611 : Blo 2249435 2249611 := bstep (se 1 (by rfl) ⟨1687208, by rfl⟩ : syracuseStep 2249611 = 3374417) B3374417
theorem B7592453 : Blo 2249435 7592453 := bbase (se 4 (by rfl) ⟨711792, by rfl⟩ : syracuseStep 7592453 = 1423585) (by norm_num)
theorem B5061635 : Blo 2249435 5061635 := bstep (se 1 (by rfl) ⟨3796226, by rfl⟩ : syracuseStep 5061635 = 7592453) B7592453
theorem B3374423 : Blo 2249435 3374423 := bstep (se 1 (by rfl) ⟨2530817, by rfl⟩ : syracuseStep 3374423 = 5061635) B5061635
theorem B2249615 : Blo 2249435 2249615 := bstep (se 1 (by rfl) ⟨1687211, by rfl⟩ : syracuseStep 2249615 = 3374423) B3374423
theorem B3374429 : Blo 2249435 3374429 := bbase (se 3 (by rfl) ⟨632705, by rfl⟩ : syracuseStep 3374429 = 1265411) (by norm_num)
theorem B2249619 : Blo 2249435 2249619 := bstep (se 1 (by rfl) ⟨1687214, by rfl⟩ : syracuseStep 2249619 = 3374429) B3374429
theorem B5061653 : Blo 2249435 5061653 := bbase (se 6 (by rfl) ⟨118632, by rfl⟩ : syracuseStep 5061653 = 237265) (by norm_num)
theorem B3374435 : Blo 2249435 3374435 := bstep (se 1 (by rfl) ⟨2530826, by rfl⟩ : syracuseStep 3374435 = 5061653) B5061653
theorem B2249623 : Blo 2249435 2249623 := bstep (se 1 (by rfl) ⟨1687217, by rfl⟩ : syracuseStep 2249623 = 3374435) B3374435
theorem B8541557 : Blo 2249435 8541557 := bbase (se 5 (by rfl) ⟨400385, by rfl⟩ : syracuseStep 8541557 = 800771) (by norm_num)
theorem B5694371 : Blo 2249435 5694371 := bstep (se 1 (by rfl) ⟨4270778, by rfl⟩ : syracuseStep 5694371 = 8541557) B8541557
theorem B3796247 : Blo 2249435 3796247 := bstep (se 1 (by rfl) ⟨2847185, by rfl⟩ : syracuseStep 3796247 = 5694371) B5694371
theorem B2530831 : Blo 2249435 2530831 := bstep (se 1 (by rfl) ⟨1898123, by rfl⟩ : syracuseStep 2530831 = 3796247) B3796247
theorem B3374441 : Blo 2249435 3374441 := bstep (se 2 (by rfl) ⟨1265415, by rfl⟩ : syracuseStep 3374441 = 2530831) B2530831
theorem B2249627 : Blo 2249435 2249627 := bstep (se 1 (by rfl) ⟨1687220, by rfl⟩ : syracuseStep 2249627 = 3374441) B3374441
theorem B2402317 : Blo 2249435 2402317 := bbase (se 3 (by rfl) ⟨450434, by rfl⟩ : syracuseStep 2402317 = 900869) (by norm_num)
theorem B12812357 : Blo 2249435 12812357 := bstep (se 4 (by rfl) ⟨1201158, by rfl⟩ : syracuseStep 12812357 = 2402317) B2402317
theorem B8541571 : Blo 2249435 8541571 := bstep (se 1 (by rfl) ⟨6406178, by rfl⟩ : syracuseStep 8541571 = 12812357) B12812357
theorem B11388761 : Blo 2249435 11388761 := bstep (se 2 (by rfl) ⟨4270785, by rfl⟩ : syracuseStep 11388761 = 8541571) B8541571
theorem B7592507 : Blo 2249435 7592507 := bstep (se 1 (by rfl) ⟨5694380, by rfl⟩ : syracuseStep 7592507 = 11388761) B11388761
theorem B5061671 : Blo 2249435 5061671 := bstep (se 1 (by rfl) ⟨3796253, by rfl⟩ : syracuseStep 5061671 = 7592507) B7592507
theorem B3374447 : Blo 2249435 3374447 := bstep (se 1 (by rfl) ⟨2530835, by rfl⟩ : syracuseStep 3374447 = 5061671) B5061671
theorem B2249631 : Blo 2249435 2249631 := bstep (se 1 (by rfl) ⟨1687223, by rfl⟩ : syracuseStep 2249631 = 3374447) B3374447
theorem B3374453 : Blo 2249435 3374453 := bbase (se 5 (by rfl) ⟨158177, by rfl⟩ : syracuseStep 3374453 = 316355) (by norm_num)
theorem B2249635 : Blo 2249435 2249635 := bstep (se 1 (by rfl) ⟨1687226, by rfl⟩ : syracuseStep 2249635 = 3374453) B3374453
theorem B3203101 : Blo 2249435 3203101 := bbase (se 3 (by rfl) ⟨600581, by rfl⟩ : syracuseStep 3203101 = 1201163) (by norm_num)
theorem B4270801 : Blo 2249435 4270801 := bstep (se 2 (by rfl) ⟨1601550, by rfl⟩ : syracuseStep 4270801 = 3203101) B3203101
theorem B5694401 : Blo 2249435 5694401 := bstep (se 2 (by rfl) ⟨2135400, by rfl⟩ : syracuseStep 5694401 = 4270801) B4270801
theorem B3796267 : Blo 2249435 3796267 := bstep (se 1 (by rfl) ⟨2847200, by rfl⟩ : syracuseStep 3796267 = 5694401) B5694401
theorem B5061689 : Blo 2249435 5061689 := bstep (se 2 (by rfl) ⟨1898133, by rfl⟩ : syracuseStep 5061689 = 3796267) B3796267
theorem B3374459 : Blo 2249435 3374459 := bstep (se 1 (by rfl) ⟨2530844, by rfl⟩ : syracuseStep 3374459 = 5061689) B5061689
theorem B2249639 : Blo 2249435 2249639 := bstep (se 1 (by rfl) ⟨1687229, by rfl⟩ : syracuseStep 2249639 = 3374459) B3374459
theorem B2530849 : Blo 2249435 2530849 := bbase (se 2 (by rfl) ⟨949068, by rfl⟩ : syracuseStep 2530849 = 1898137) (by norm_num)
theorem B3374465 : Blo 2249435 3374465 := bstep (se 2 (by rfl) ⟨1265424, by rfl⟩ : syracuseStep 3374465 = 2530849) B2530849
theorem B2249643 : Blo 2249435 2249643 := bstep (se 1 (by rfl) ⟨1687232, by rfl⟩ : syracuseStep 2249643 = 3374465) B3374465
theorem B5694421 : Blo 2249435 5694421 := bbase (se 7 (by rfl) ⟨66731, by rfl⟩ : syracuseStep 5694421 = 133463) (by norm_num)
theorem B7592561 : Blo 2249435 7592561 := bstep (se 2 (by rfl) ⟨2847210, by rfl⟩ : syracuseStep 7592561 = 5694421) B5694421
theorem B5061707 : Blo 2249435 5061707 := bstep (se 1 (by rfl) ⟨3796280, by rfl⟩ : syracuseStep 5061707 = 7592561) B7592561
theorem B3374471 : Blo 2249435 3374471 := bstep (se 1 (by rfl) ⟨2530853, by rfl⟩ : syracuseStep 3374471 = 5061707) B5061707
theorem B2249647 : Blo 2249435 2249647 := bstep (se 1 (by rfl) ⟨1687235, by rfl⟩ : syracuseStep 2249647 = 3374471) B3374471
theorem B3374477 : Blo 2249435 3374477 := bbase (se 3 (by rfl) ⟨632714, by rfl⟩ : syracuseStep 3374477 = 1265429) (by norm_num)
theorem B2249651 : Blo 2249435 2249651 := bstep (se 1 (by rfl) ⟨1687238, by rfl⟩ : syracuseStep 2249651 = 3374477) B3374477
theorem B5061725 : Blo 2249435 5061725 := bbase (se 3 (by rfl) ⟨949073, by rfl⟩ : syracuseStep 5061725 = 1898147) (by norm_num)
theorem B3374483 : Blo 2249435 3374483 := bstep (se 1 (by rfl) ⟨2530862, by rfl⟩ : syracuseStep 3374483 = 5061725) B5061725
theorem B2249655 : Blo 2249435 2249655 := bstep (se 1 (by rfl) ⟨1687241, by rfl⟩ : syracuseStep 2249655 = 3374483) B3374483
theorem B3796301 : Blo 2249435 3796301 := bbase (se 3 (by rfl) ⟨711806, by rfl⟩ : syracuseStep 3796301 = 1423613) (by norm_num)
theorem B2530867 : Blo 2249435 2530867 := bstep (se 1 (by rfl) ⟨1898150, by rfl⟩ : syracuseStep 2530867 = 3796301) B3796301
theorem B3374489 : Blo 2249435 3374489 := bstep (se 2 (by rfl) ⟨1265433, by rfl⟩ : syracuseStep 3374489 = 2530867) B2530867
theorem B2249659 : Blo 2249435 2249659 := bstep (se 1 (by rfl) ⟨1687244, by rfl⟩ : syracuseStep 2249659 = 3374489) B3374489
theorem B46807253 : Blo 2249435 46807253 := bbase (se 7 (by rfl) ⟨548522, by rfl⟩ : syracuseStep 46807253 = 1097045) (by norm_num)
theorem B31204835 : Blo 2249435 31204835 := bstep (se 1 (by rfl) ⟨23403626, by rfl⟩ : syracuseStep 31204835 = 46807253) B46807253
theorem B20803223 : Blo 2249435 20803223 := bstep (se 1 (by rfl) ⟨15602417, by rfl⟩ : syracuseStep 20803223 = 31204835) B31204835
theorem B13868815 : Blo 2249435 13868815 := bstep (se 1 (by rfl) ⟨10401611, by rfl⟩ : syracuseStep 13868815 = 20803223) B20803223
theorem B18491753 : Blo 2249435 18491753 := bstep (se 2 (by rfl) ⟨6934407, by rfl⟩ : syracuseStep 18491753 = 13868815) B13868815
theorem B12327835 : Blo 2249435 12327835 := bstep (se 1 (by rfl) ⟨9245876, by rfl⟩ : syracuseStep 12327835 = 18491753) B18491753
theorem B16437113 : Blo 2249435 16437113 := bstep (se 2 (by rfl) ⟨6163917, by rfl⟩ : syracuseStep 16437113 = 12327835) B12327835
theorem B10958075 : Blo 2249435 10958075 := bstep (se 1 (by rfl) ⟨8218556, by rfl⟩ : syracuseStep 10958075 = 16437113) B16437113
theorem B7305383 : Blo 2249435 7305383 := bstep (se 1 (by rfl) ⟨5479037, by rfl⟩ : syracuseStep 7305383 = 10958075) B10958075
theorem B4870255 : Blo 2249435 4870255 := bstep (se 1 (by rfl) ⟨3652691, by rfl⟩ : syracuseStep 4870255 = 7305383) B7305383
theorem B6493673 : Blo 2249435 6493673 := bstep (se 2 (by rfl) ⟨2435127, by rfl⟩ : syracuseStep 6493673 = 4870255) B4870255
theorem B17316461 : Blo 2249435 17316461 := bstep (se 3 (by rfl) ⟨3246836, by rfl⟩ : syracuseStep 17316461 = 6493673) B6493673
theorem B46177229 : Blo 2249435 46177229 := bstep (se 3 (by rfl) ⟨8658230, by rfl⟩ : syracuseStep 46177229 = 17316461) B17316461
theorem B123139277 : Blo 2249435 123139277 := bstep (se 3 (by rfl) ⟨23088614, by rfl⟩ : syracuseStep 123139277 = 46177229) B46177229
theorem B82092851 : Blo 2249435 82092851 := bstep (se 1 (by rfl) ⟨61569638, by rfl⟩ : syracuseStep 82092851 = 123139277) B123139277
theorem B54728567 : Blo 2249435 54728567 := bstep (se 1 (by rfl) ⟨41046425, by rfl⟩ : syracuseStep 54728567 = 82092851) B82092851
theorem B36485711 : Blo 2249435 36485711 := bstep (se 1 (by rfl) ⟨27364283, by rfl⟩ : syracuseStep 36485711 = 54728567) B54728567
theorem B24323807 : Blo 2249435 24323807 := bstep (se 1 (by rfl) ⟨18242855, by rfl⟩ : syracuseStep 24323807 = 36485711) B36485711
theorem B16215871 : Blo 2249435 16215871 := bstep (se 1 (by rfl) ⟨12161903, by rfl⟩ : syracuseStep 16215871 = 24323807) B24323807
theorem B21621161 : Blo 2249435 21621161 := bstep (se 2 (by rfl) ⟨8107935, by rfl⟩ : syracuseStep 21621161 = 16215871) B16215871
theorem B14414107 : Blo 2249435 14414107 := bstep (se 1 (by rfl) ⟨10810580, by rfl⟩ : syracuseStep 14414107 = 21621161) B21621161
theorem B19218809 : Blo 2249435 19218809 := bstep (se 2 (by rfl) ⟨7207053, by rfl⟩ : syracuseStep 19218809 = 14414107) B14414107
theorem B12812539 : Blo 2249435 12812539 := bstep (se 1 (by rfl) ⟨9609404, by rfl⟩ : syracuseStep 12812539 = 19218809) B19218809
theorem B17083385 : Blo 2249435 17083385 := bstep (se 2 (by rfl) ⟨6406269, by rfl⟩ : syracuseStep 17083385 = 12812539) B12812539
theorem B11388923 : Blo 2249435 11388923 := bstep (se 1 (by rfl) ⟨8541692, by rfl⟩ : syracuseStep 11388923 = 17083385) B17083385
theorem B7592615 : Blo 2249435 7592615 := bstep (se 1 (by rfl) ⟨5694461, by rfl⟩ : syracuseStep 7592615 = 11388923) B11388923
theorem B5061743 : Blo 2249435 5061743 := bstep (se 1 (by rfl) ⟨3796307, by rfl⟩ : syracuseStep 5061743 = 7592615) B7592615
theorem B3374495 : Blo 2249435 3374495 := bstep (se 1 (by rfl) ⟨2530871, by rfl⟩ : syracuseStep 3374495 = 5061743) B5061743
theorem B2249663 : Blo 2249435 2249663 := bstep (se 1 (by rfl) ⟨1687247, by rfl⟩ : syracuseStep 2249663 = 3374495) B3374495
theorem B3374501 : Blo 2249435 3374501 := bbase (se 4 (by rfl) ⟨316359, by rfl⟩ : syracuseStep 3374501 = 632719) (by norm_num)
theorem B2249667 : Blo 2249435 2249667 := bstep (se 1 (by rfl) ⟨1687250, by rfl⟩ : syracuseStep 2249667 = 3374501) B3374501
theorem B2847241 : Blo 2249435 2847241 := bbase (se 2 (by rfl) ⟨1067715, by rfl⟩ : syracuseStep 2847241 = 2135431) (by norm_num)
theorem B3796321 : Blo 2249435 3796321 := bstep (se 2 (by rfl) ⟨1423620, by rfl⟩ : syracuseStep 3796321 = 2847241) B2847241
theorem B5061761 : Blo 2249435 5061761 := bstep (se 2 (by rfl) ⟨1898160, by rfl⟩ : syracuseStep 5061761 = 3796321) B3796321
theorem B3374507 : Blo 2249435 3374507 := bstep (se 1 (by rfl) ⟨2530880, by rfl⟩ : syracuseStep 3374507 = 5061761) B5061761
theorem B2249671 : Blo 2249435 2249671 := bstep (se 1 (by rfl) ⟨1687253, by rfl⟩ : syracuseStep 2249671 = 3374507) B3374507
theorem B2530885 : Blo 2249435 2530885 := bbase (se 4 (by rfl) ⟨237270, by rfl⟩ : syracuseStep 2530885 = 474541) (by norm_num)
theorem B3374513 : Blo 2249435 3374513 := bstep (se 2 (by rfl) ⟨1265442, by rfl⟩ : syracuseStep 3374513 = 2530885) B2530885
theorem B2249675 : Blo 2249435 2249675 := bstep (se 1 (by rfl) ⟨1687256, by rfl⟩ : syracuseStep 2249675 = 3374513) B3374513
theorem B4270877 : Blo 2249435 4270877 := bbase (se 3 (by rfl) ⟨800789, by rfl⟩ : syracuseStep 4270877 = 1601579) (by norm_num)
theorem B2847251 : Blo 2249435 2847251 := bstep (se 1 (by rfl) ⟨2135438, by rfl⟩ : syracuseStep 2847251 = 4270877) B4270877
theorem B7592669 : Blo 2249435 7592669 := bstep (se 3 (by rfl) ⟨1423625, by rfl⟩ : syracuseStep 7592669 = 2847251) B2847251
theorem B5061779 : Blo 2249435 5061779 := bstep (se 1 (by rfl) ⟨3796334, by rfl⟩ : syracuseStep 5061779 = 7592669) B7592669
theorem B3374519 : Blo 2249435 3374519 := bstep (se 1 (by rfl) ⟨2530889, by rfl⟩ : syracuseStep 3374519 = 5061779) B5061779
theorem B2249679 : Blo 2249435 2249679 := bstep (se 1 (by rfl) ⟨1687259, by rfl⟩ : syracuseStep 2249679 = 3374519) B3374519
theorem B3374525 : Blo 2249435 3374525 := bbase (se 3 (by rfl) ⟨632723, by rfl⟩ : syracuseStep 3374525 = 1265447) (by norm_num)
theorem B2249683 : Blo 2249435 2249683 := bstep (se 1 (by rfl) ⟨1687262, by rfl⟩ : syracuseStep 2249683 = 3374525) B3374525
theorem B5061797 : Blo 2249435 5061797 := bbase (se 4 (by rfl) ⟨474543, by rfl⟩ : syracuseStep 5061797 = 949087) (by norm_num)
theorem B3374531 : Blo 2249435 3374531 := bstep (se 1 (by rfl) ⟨2530898, by rfl⟩ : syracuseStep 3374531 = 5061797) B5061797
theorem B2249687 : Blo 2249435 2249687 := bstep (se 1 (by rfl) ⟨1687265, by rfl⟩ : syracuseStep 2249687 = 3374531) B3374531
theorem B5694533 : Blo 2249435 5694533 := bbase (se 4 (by rfl) ⟨533862, by rfl⟩ : syracuseStep 5694533 = 1067725) (by norm_num)
theorem B3796355 : Blo 2249435 3796355 := bstep (se 1 (by rfl) ⟨2847266, by rfl⟩ : syracuseStep 3796355 = 5694533) B5694533
theorem B2530903 : Blo 2249435 2530903 := bstep (se 1 (by rfl) ⟨1898177, by rfl⟩ : syracuseStep 2530903 = 3796355) B3796355
theorem B3374537 : Blo 2249435 3374537 := bstep (se 2 (by rfl) ⟨1265451, by rfl⟩ : syracuseStep 3374537 = 2530903) B2530903
theorem B2249691 : Blo 2249435 2249691 := bstep (se 1 (by rfl) ⟨1687268, by rfl⟩ : syracuseStep 2249691 = 3374537) B3374537
theorem B7207157 : Blo 2249435 7207157 := bbase (se 5 (by rfl) ⟨337835, by rfl⟩ : syracuseStep 7207157 = 675671) (by norm_num)
theorem B4804771 : Blo 2249435 4804771 := bstep (se 1 (by rfl) ⟨3603578, by rfl⟩ : syracuseStep 4804771 = 7207157) B7207157
theorem B6406361 : Blo 2249435 6406361 := bstep (se 2 (by rfl) ⟨2402385, by rfl⟩ : syracuseStep 6406361 = 4804771) B4804771
theorem B4270907 : Blo 2249435 4270907 := bstep (se 1 (by rfl) ⟨3203180, by rfl⟩ : syracuseStep 4270907 = 6406361) B6406361
theorem B11389085 : Blo 2249435 11389085 := bstep (se 3 (by rfl) ⟨2135453, by rfl⟩ : syracuseStep 11389085 = 4270907) B4270907
theorem B7592723 : Blo 2249435 7592723 := bstep (se 1 (by rfl) ⟨5694542, by rfl⟩ : syracuseStep 7592723 = 11389085) B11389085
theorem B5061815 : Blo 2249435 5061815 := bstep (se 1 (by rfl) ⟨3796361, by rfl⟩ : syracuseStep 5061815 = 7592723) B7592723
theorem B3374543 : Blo 2249435 3374543 := bstep (se 1 (by rfl) ⟨2530907, by rfl⟩ : syracuseStep 3374543 = 5061815) B5061815
theorem B2249695 : Blo 2249435 2249695 := bstep (se 1 (by rfl) ⟨1687271, by rfl⟩ : syracuseStep 2249695 = 3374543) B3374543
theorem B3374549 : Blo 2249435 3374549 := bbase (se 7 (by rfl) ⟨39545, by rfl⟩ : syracuseStep 3374549 = 79091) (by norm_num)
theorem B2249699 : Blo 2249435 2249699 := bstep (se 1 (by rfl) ⟨1687274, by rfl⟩ : syracuseStep 2249699 = 3374549) B3374549
theorem B8541845 : Blo 2249435 8541845 := bbase (se 6 (by rfl) ⟨200199, by rfl⟩ : syracuseStep 8541845 = 400399) (by norm_num)
theorem B5694563 : Blo 2249435 5694563 := bstep (se 1 (by rfl) ⟨4270922, by rfl⟩ : syracuseStep 5694563 = 8541845) B8541845
theorem B3796375 : Blo 2249435 3796375 := bstep (se 1 (by rfl) ⟨2847281, by rfl⟩ : syracuseStep 3796375 = 5694563) B5694563
theorem B5061833 : Blo 2249435 5061833 := bstep (se 2 (by rfl) ⟨1898187, by rfl⟩ : syracuseStep 5061833 = 3796375) B3796375
theorem B3374555 : Blo 2249435 3374555 := bstep (se 1 (by rfl) ⟨2530916, by rfl⟩ : syracuseStep 3374555 = 5061833) B5061833
theorem B2249703 : Blo 2249435 2249703 := bstep (se 1 (by rfl) ⟨1687277, by rfl⟩ : syracuseStep 2249703 = 3374555) B3374555
theorem B2530921 : Blo 2249435 2530921 := bbase (se 2 (by rfl) ⟨949095, by rfl⟩ : syracuseStep 2530921 = 1898191) (by norm_num)
theorem B3374561 : Blo 2249435 3374561 := bstep (se 2 (by rfl) ⟨1265460, by rfl⟩ : syracuseStep 3374561 = 2530921) B2530921
theorem B2249707 : Blo 2249435 2249707 := bstep (se 1 (by rfl) ⟨1687280, by rfl⟩ : syracuseStep 2249707 = 3374561) B3374561
theorem B4804805 : Blo 2249435 4804805 := bbase (se 4 (by rfl) ⟨450450, by rfl⟩ : syracuseStep 4804805 = 900901) (by norm_num)
theorem B12812813 : Blo 2249435 12812813 := bstep (se 3 (by rfl) ⟨2402402, by rfl⟩ : syracuseStep 12812813 = 4804805) B4804805
theorem B8541875 : Blo 2249435 8541875 := bstep (se 1 (by rfl) ⟨6406406, by rfl⟩ : syracuseStep 8541875 = 12812813) B12812813
theorem B5694583 : Blo 2249435 5694583 := bstep (se 1 (by rfl) ⟨4270937, by rfl⟩ : syracuseStep 5694583 = 8541875) B8541875
theorem B7592777 : Blo 2249435 7592777 := bstep (se 2 (by rfl) ⟨2847291, by rfl⟩ : syracuseStep 7592777 = 5694583) B5694583
theorem B5061851 : Blo 2249435 5061851 := bstep (se 1 (by rfl) ⟨3796388, by rfl⟩ : syracuseStep 5061851 = 7592777) B7592777
theorem B3374567 : Blo 2249435 3374567 := bstep (se 1 (by rfl) ⟨2530925, by rfl⟩ : syracuseStep 3374567 = 5061851) B5061851
theorem B2249711 : Blo 2249435 2249711 := bstep (se 1 (by rfl) ⟨1687283, by rfl⟩ : syracuseStep 2249711 = 3374567) B3374567
theorem B3374573 : Blo 2249435 3374573 := bbase (se 3 (by rfl) ⟨632732, by rfl⟩ : syracuseStep 3374573 = 1265465) (by norm_num)
theorem B2249715 : Blo 2249435 2249715 := bstep (se 1 (by rfl) ⟨1687286, by rfl⟩ : syracuseStep 2249715 = 3374573) B3374573
theorem B5061869 : Blo 2249435 5061869 := bbase (se 3 (by rfl) ⟨949100, by rfl⟩ : syracuseStep 5061869 = 1898201) (by norm_num)
theorem B3374579 : Blo 2249435 3374579 := bstep (se 1 (by rfl) ⟨2530934, by rfl⟩ : syracuseStep 3374579 = 5061869) B5061869
theorem B2249719 : Blo 2249435 2249719 := bstep (se 1 (by rfl) ⟨1687289, by rfl⟩ : syracuseStep 2249719 = 3374579) B3374579
theorem B3203221 : Blo 2249435 3203221 := bbase (se 6 (by rfl) ⟨75075, by rfl⟩ : syracuseStep 3203221 = 150151) (by norm_num)
theorem B4270961 : Blo 2249435 4270961 := bstep (se 2 (by rfl) ⟨1601610, by rfl⟩ : syracuseStep 4270961 = 3203221) B3203221
theorem B2847307 : Blo 2249435 2847307 := bstep (se 1 (by rfl) ⟨2135480, by rfl⟩ : syracuseStep 2847307 = 4270961) B4270961
theorem B3796409 : Blo 2249435 3796409 := bstep (se 2 (by rfl) ⟨1423653, by rfl⟩ : syracuseStep 3796409 = 2847307) B2847307
theorem B2530939 : Blo 2249435 2530939 := bstep (se 1 (by rfl) ⟨1898204, by rfl⟩ : syracuseStep 2530939 = 3796409) B3796409
theorem B3374585 : Blo 2249435 3374585 := bstep (se 2 (by rfl) ⟨1265469, by rfl⟩ : syracuseStep 3374585 = 2530939) B2530939
theorem B2249723 : Blo 2249435 2249723 := bstep (se 1 (by rfl) ⟨1687292, by rfl⟩ : syracuseStep 2249723 = 3374585) B3374585
theorem B5130949 : Blo 2249435 5130949 := bbase (se 4 (by rfl) ⟨481026, by rfl⟩ : syracuseStep 5130949 = 962053) (by norm_num)
theorem B6841265 : Blo 2249435 6841265 := bstep (se 2 (by rfl) ⟨2565474, by rfl⟩ : syracuseStep 6841265 = 5130949) B5130949
theorem B72973493 : Blo 2249435 72973493 := bstep (se 5 (by rfl) ⟨3420632, by rfl⟩ : syracuseStep 72973493 = 6841265) B6841265
theorem B48648995 : Blo 2249435 48648995 := bstep (se 1 (by rfl) ⟨36486746, by rfl⟩ : syracuseStep 48648995 = 72973493) B72973493
theorem B32432663 : Blo 2249435 32432663 := bstep (se 1 (by rfl) ⟨24324497, by rfl⟩ : syracuseStep 32432663 = 48648995) B48648995
theorem B86487101 : Blo 2249435 86487101 := bstep (se 3 (by rfl) ⟨16216331, by rfl⟩ : syracuseStep 86487101 = 32432663) B32432663
theorem B57658067 : Blo 2249435 57658067 := bstep (se 1 (by rfl) ⟨43243550, by rfl⟩ : syracuseStep 57658067 = 86487101) B86487101
theorem B38438711 : Blo 2249435 38438711 := bstep (se 1 (by rfl) ⟨28829033, by rfl⟩ : syracuseStep 38438711 = 57658067) B57658067
theorem B25625807 : Blo 2249435 25625807 := bstep (se 1 (by rfl) ⟨19219355, by rfl⟩ : syracuseStep 25625807 = 38438711) B38438711
theorem B17083871 : Blo 2249435 17083871 := bstep (se 1 (by rfl) ⟨12812903, by rfl⟩ : syracuseStep 17083871 = 25625807) B25625807
theorem B11389247 : Blo 2249435 11389247 := bstep (se 1 (by rfl) ⟨8541935, by rfl⟩ : syracuseStep 11389247 = 17083871) B17083871
theorem B7592831 : Blo 2249435 7592831 := bstep (se 1 (by rfl) ⟨5694623, by rfl⟩ : syracuseStep 7592831 = 11389247) B11389247
theorem B5061887 : Blo 2249435 5061887 := bstep (se 1 (by rfl) ⟨3796415, by rfl⟩ : syracuseStep 5061887 = 7592831) B7592831
theorem B3374591 : Blo 2249435 3374591 := bstep (se 1 (by rfl) ⟨2530943, by rfl⟩ : syracuseStep 3374591 = 5061887) B5061887
theorem B2249727 : Blo 2249435 2249727 := bstep (se 1 (by rfl) ⟨1687295, by rfl⟩ : syracuseStep 2249727 = 3374591) B3374591
theorem B3374597 : Blo 2249435 3374597 := bbase (se 4 (by rfl) ⟨316368, by rfl⟩ : syracuseStep 3374597 = 632737) (by norm_num)
theorem B2249731 : Blo 2249435 2249731 := bstep (se 1 (by rfl) ⟨1687298, by rfl⟩ : syracuseStep 2249731 = 3374597) B3374597
theorem B3796429 : Blo 2249435 3796429 := bbase (se 3 (by rfl) ⟨711830, by rfl⟩ : syracuseStep 3796429 = 1423661) (by norm_num)
theorem B5061905 : Blo 2249435 5061905 := bstep (se 2 (by rfl) ⟨1898214, by rfl⟩ : syracuseStep 5061905 = 3796429) B3796429
theorem B3374603 : Blo 2249435 3374603 := bstep (se 1 (by rfl) ⟨2530952, by rfl⟩ : syracuseStep 3374603 = 5061905) B5061905
theorem B2249735 : Blo 2249435 2249735 := bstep (se 1 (by rfl) ⟨1687301, by rfl⟩ : syracuseStep 2249735 = 3374603) B3374603
theorem B2530957 : Blo 2249435 2530957 := bbase (se 3 (by rfl) ⟨474554, by rfl⟩ : syracuseStep 2530957 = 949109) (by norm_num)
theorem B3374609 : Blo 2249435 3374609 := bstep (se 2 (by rfl) ⟨1265478, by rfl⟩ : syracuseStep 3374609 = 2530957) B2530957
theorem B2249739 : Blo 2249435 2249739 := bstep (se 1 (by rfl) ⟨1687304, by rfl⟩ : syracuseStep 2249739 = 3374609) B3374609
theorem B7592885 : Blo 2249435 7592885 := bbase (se 5 (by rfl) ⟨355916, by rfl⟩ : syracuseStep 7592885 = 711833) (by norm_num)
theorem B5061923 : Blo 2249435 5061923 := bstep (se 1 (by rfl) ⟨3796442, by rfl⟩ : syracuseStep 5061923 = 7592885) B7592885
theorem B3374615 : Blo 2249435 3374615 := bstep (se 1 (by rfl) ⟨2530961, by rfl⟩ : syracuseStep 3374615 = 5061923) B5061923
theorem B2249743 : Blo 2249435 2249743 := bstep (se 1 (by rfl) ⟨1687307, by rfl⟩ : syracuseStep 2249743 = 3374615) B3374615
theorem B3374621 : Blo 2249435 3374621 := bbase (se 3 (by rfl) ⟨632741, by rfl⟩ : syracuseStep 3374621 = 1265483) (by norm_num)
theorem B2249747 : Blo 2249435 2249747 := bstep (se 1 (by rfl) ⟨1687310, by rfl⟩ : syracuseStep 2249747 = 3374621) B3374621
theorem B5061941 : Blo 2249435 5061941 := bbase (se 5 (by rfl) ⟨237278, by rfl⟩ : syracuseStep 5061941 = 474557) (by norm_num)
theorem B3374627 : Blo 2249435 3374627 := bstep (se 1 (by rfl) ⟨2530970, by rfl⟩ : syracuseStep 3374627 = 5061941) B5061941
theorem B2249751 : Blo 2249435 2249751 := bstep (se 1 (by rfl) ⟨1687313, by rfl⟩ : syracuseStep 2249751 = 3374627) B3374627
theorem B18243605 : Blo 2249435 18243605 := bbase (se 6 (by rfl) ⟨427584, by rfl⟩ : syracuseStep 18243605 = 855169) (by norm_num)
theorem B12162403 : Blo 2249435 12162403 := bstep (se 1 (by rfl) ⟨9121802, by rfl⟩ : syracuseStep 12162403 = 18243605) B18243605
theorem B16216537 : Blo 2249435 16216537 := bstep (se 2 (by rfl) ⟨6081201, by rfl⟩ : syracuseStep 16216537 = 12162403) B12162403
theorem B21622049 : Blo 2249435 21622049 := bstep (se 2 (by rfl) ⟨8108268, by rfl⟩ : syracuseStep 21622049 = 16216537) B16216537
theorem B14414699 : Blo 2249435 14414699 := bstep (se 1 (by rfl) ⟨10811024, by rfl⟩ : syracuseStep 14414699 = 21622049) B21622049
theorem B9609799 : Blo 2249435 9609799 := bstep (se 1 (by rfl) ⟨7207349, by rfl⟩ : syracuseStep 9609799 = 14414699) B14414699
theorem B12813065 : Blo 2249435 12813065 := bstep (se 2 (by rfl) ⟨4804899, by rfl⟩ : syracuseStep 12813065 = 9609799) B9609799
theorem B8542043 : Blo 2249435 8542043 := bstep (se 1 (by rfl) ⟨6406532, by rfl⟩ : syracuseStep 8542043 = 12813065) B12813065
theorem B5694695 : Blo 2249435 5694695 := bstep (se 1 (by rfl) ⟨4271021, by rfl⟩ : syracuseStep 5694695 = 8542043) B8542043
theorem B3796463 : Blo 2249435 3796463 := bstep (se 1 (by rfl) ⟨2847347, by rfl⟩ : syracuseStep 3796463 = 5694695) B5694695
theorem B2530975 : Blo 2249435 2530975 := bstep (se 1 (by rfl) ⟨1898231, by rfl⟩ : syracuseStep 2530975 = 3796463) B3796463
theorem B3374633 : Blo 2249435 3374633 := bstep (se 2 (by rfl) ⟨1265487, by rfl⟩ : syracuseStep 3374633 = 2530975) B2530975
theorem B2249755 : Blo 2249435 2249755 := bstep (se 1 (by rfl) ⟨1687316, by rfl⟩ : syracuseStep 2249755 = 3374633) B3374633
theorem B4054141 : Blo 2249435 4054141 := bbase (se 3 (by rfl) ⟨760151, by rfl⟩ : syracuseStep 4054141 = 1520303) (by norm_num)
theorem B21622085 : Blo 2249435 21622085 := bstep (se 4 (by rfl) ⟨2027070, by rfl⟩ : syracuseStep 21622085 = 4054141) B4054141
theorem B14414723 : Blo 2249435 14414723 := bstep (se 1 (by rfl) ⟨10811042, by rfl⟩ : syracuseStep 14414723 = 21622085) B21622085
theorem B9609815 : Blo 2249435 9609815 := bstep (se 1 (by rfl) ⟨7207361, by rfl⟩ : syracuseStep 9609815 = 14414723) B14414723
theorem B6406543 : Blo 2249435 6406543 := bstep (se 1 (by rfl) ⟨4804907, by rfl⟩ : syracuseStep 6406543 = 9609815) B9609815
theorem B8542057 : Blo 2249435 8542057 := bstep (se 2 (by rfl) ⟨3203271, by rfl⟩ : syracuseStep 8542057 = 6406543) B6406543
theorem B11389409 : Blo 2249435 11389409 := bstep (se 2 (by rfl) ⟨4271028, by rfl⟩ : syracuseStep 11389409 = 8542057) B8542057
theorem B7592939 : Blo 2249435 7592939 := bstep (se 1 (by rfl) ⟨5694704, by rfl⟩ : syracuseStep 7592939 = 11389409) B11389409
theorem B5061959 : Blo 2249435 5061959 := bstep (se 1 (by rfl) ⟨3796469, by rfl⟩ : syracuseStep 5061959 = 7592939) B7592939
theorem B3374639 : Blo 2249435 3374639 := bstep (se 1 (by rfl) ⟨2530979, by rfl⟩ : syracuseStep 3374639 = 5061959) B5061959
theorem B2249759 : Blo 2249435 2249759 := bstep (se 1 (by rfl) ⟨1687319, by rfl⟩ : syracuseStep 2249759 = 3374639) B3374639
theorem B3374645 : Blo 2249435 3374645 := bbase (se 5 (by rfl) ⟨158186, by rfl⟩ : syracuseStep 3374645 = 316373) (by norm_num)
theorem B2249763 : Blo 2249435 2249763 := bstep (se 1 (by rfl) ⟨1687322, by rfl⟩ : syracuseStep 2249763 = 3374645) B3374645
theorem B5694725 : Blo 2249435 5694725 := bbase (se 4 (by rfl) ⟨533880, by rfl⟩ : syracuseStep 5694725 = 1067761) (by norm_num)
theorem B3796483 : Blo 2249435 3796483 := bstep (se 1 (by rfl) ⟨2847362, by rfl⟩ : syracuseStep 3796483 = 5694725) B5694725
theorem B5061977 : Blo 2249435 5061977 := bstep (se 2 (by rfl) ⟨1898241, by rfl⟩ : syracuseStep 5061977 = 3796483) B3796483
theorem B3374651 : Blo 2249435 3374651 := bstep (se 1 (by rfl) ⟨2530988, by rfl⟩ : syracuseStep 3374651 = 5061977) B5061977
theorem B2249767 : Blo 2249435 2249767 := bstep (se 1 (by rfl) ⟨1687325, by rfl⟩ : syracuseStep 2249767 = 3374651) B3374651
theorem B2530993 : Blo 2249435 2530993 := bbase (se 2 (by rfl) ⟨949122, by rfl⟩ : syracuseStep 2530993 = 1898245) (by norm_num)
theorem B3374657 : Blo 2249435 3374657 := bstep (se 2 (by rfl) ⟨1265496, by rfl⟩ : syracuseStep 3374657 = 2530993) B2530993
theorem B2249771 : Blo 2249435 2249771 := bstep (se 1 (by rfl) ⟨1687328, by rfl⟩ : syracuseStep 2249771 = 3374657) B3374657
theorem B16437941 : Blo 2249435 16437941 := bbase (se 5 (by rfl) ⟨770528, by rfl⟩ : syracuseStep 16437941 = 1541057) (by norm_num)
theorem B10958627 : Blo 2249435 10958627 := bstep (se 1 (by rfl) ⟨8218970, by rfl⟩ : syracuseStep 10958627 = 16437941) B16437941
theorem B7305751 : Blo 2249435 7305751 := bstep (se 1 (by rfl) ⟨5479313, by rfl⟩ : syracuseStep 7305751 = 10958627) B10958627
theorem B9741001 : Blo 2249435 9741001 := bstep (se 2 (by rfl) ⟨3652875, by rfl⟩ : syracuseStep 9741001 = 7305751) B7305751
theorem B12988001 : Blo 2249435 12988001 := bstep (se 2 (by rfl) ⟨4870500, by rfl⟩ : syracuseStep 12988001 = 9741001) B9741001
theorem B8658667 : Blo 2249435 8658667 := bstep (se 1 (by rfl) ⟨6494000, by rfl⟩ : syracuseStep 8658667 = 12988001) B12988001
theorem B11544889 : Blo 2249435 11544889 := bstep (se 2 (by rfl) ⟨4329333, by rfl⟩ : syracuseStep 11544889 = 8658667) B8658667
theorem B15393185 : Blo 2249435 15393185 := bstep (se 2 (by rfl) ⟨5772444, by rfl⟩ : syracuseStep 15393185 = 11544889) B11544889
theorem B10262123 : Blo 2249435 10262123 := bstep (se 1 (by rfl) ⟨7696592, by rfl⟩ : syracuseStep 10262123 = 15393185) B15393185
theorem B6841415 : Blo 2249435 6841415 := bstep (se 1 (by rfl) ⟨5131061, by rfl⟩ : syracuseStep 6841415 = 10262123) B10262123
theorem B4560943 : Blo 2249435 4560943 := bstep (se 1 (by rfl) ⟨3420707, by rfl⟩ : syracuseStep 4560943 = 6841415) B6841415
theorem B6081257 : Blo 2249435 6081257 := bstep (se 2 (by rfl) ⟨2280471, by rfl⟩ : syracuseStep 6081257 = 4560943) B4560943
theorem B4054171 : Blo 2249435 4054171 := bstep (se 1 (by rfl) ⟨3040628, by rfl⟩ : syracuseStep 4054171 = 6081257) B6081257
theorem B5405561 : Blo 2249435 5405561 := bstep (se 2 (by rfl) ⟨2027085, by rfl⟩ : syracuseStep 5405561 = 4054171) B4054171
theorem B3603707 : Blo 2249435 3603707 := bstep (se 1 (by rfl) ⟨2702780, by rfl⟩ : syracuseStep 3603707 = 5405561) B5405561
theorem B2402471 : Blo 2249435 2402471 := bstep (se 1 (by rfl) ⟨1801853, by rfl⟩ : syracuseStep 2402471 = 3603707) B3603707
theorem B6406589 : Blo 2249435 6406589 := bstep (se 3 (by rfl) ⟨1201235, by rfl⟩ : syracuseStep 6406589 = 2402471) B2402471
theorem B4271059 : Blo 2249435 4271059 := bstep (se 1 (by rfl) ⟨3203294, by rfl⟩ : syracuseStep 4271059 = 6406589) B6406589
theorem B5694745 : Blo 2249435 5694745 := bstep (se 2 (by rfl) ⟨2135529, by rfl⟩ : syracuseStep 5694745 = 4271059) B4271059
theorem B7592993 : Blo 2249435 7592993 := bstep (se 2 (by rfl) ⟨2847372, by rfl⟩ : syracuseStep 7592993 = 5694745) B5694745
theorem B5061995 : Blo 2249435 5061995 := bstep (se 1 (by rfl) ⟨3796496, by rfl⟩ : syracuseStep 5061995 = 7592993) B7592993
theorem B3374663 : Blo 2249435 3374663 := bstep (se 1 (by rfl) ⟨2530997, by rfl⟩ : syracuseStep 3374663 = 5061995) B5061995
theorem B2249775 : Blo 2249435 2249775 := bstep (se 1 (by rfl) ⟨1687331, by rfl⟩ : syracuseStep 2249775 = 3374663) B3374663
theorem B3374669 : Blo 2249435 3374669 := bbase (se 3 (by rfl) ⟨632750, by rfl⟩ : syracuseStep 3374669 = 1265501) (by norm_num)
theorem B2249779 : Blo 2249435 2249779 := bstep (se 1 (by rfl) ⟨1687334, by rfl⟩ : syracuseStep 2249779 = 3374669) B3374669
theorem B5062013 : Blo 2249435 5062013 := bbase (se 3 (by rfl) ⟨949127, by rfl⟩ : syracuseStep 5062013 = 1898255) (by norm_num)
theorem B3374675 : Blo 2249435 3374675 := bstep (se 1 (by rfl) ⟨2531006, by rfl⟩ : syracuseStep 3374675 = 5062013) B5062013
theorem B2249783 : Blo 2249435 2249783 := bstep (se 1 (by rfl) ⟨1687337, by rfl⟩ : syracuseStep 2249783 = 3374675) B3374675
theorem B3796517 : Blo 2249435 3796517 := bbase (se 4 (by rfl) ⟨355923, by rfl⟩ : syracuseStep 3796517 = 711847) (by norm_num)
theorem B2531011 : Blo 2249435 2531011 := bstep (se 1 (by rfl) ⟨1898258, by rfl⟩ : syracuseStep 2531011 = 3796517) B3796517
theorem B3374681 : Blo 2249435 3374681 := bstep (se 2 (by rfl) ⟨1265505, by rfl⟩ : syracuseStep 3374681 = 2531011) B2531011
theorem B2249787 : Blo 2249435 2249787 := bstep (se 1 (by rfl) ⟨1687340, by rfl⟩ : syracuseStep 2249787 = 3374681) B3374681
theorem B3203317 : Blo 2249435 3203317 := bbase (se 5 (by rfl) ⟨150155, by rfl⟩ : syracuseStep 3203317 = 300311) (by norm_num)
theorem B17084357 : Blo 2249435 17084357 := bstep (se 4 (by rfl) ⟨1601658, by rfl⟩ : syracuseStep 17084357 = 3203317) B3203317
theorem B11389571 : Blo 2249435 11389571 := bstep (se 1 (by rfl) ⟨8542178, by rfl⟩ : syracuseStep 11389571 = 17084357) B17084357
theorem B7593047 : Blo 2249435 7593047 := bstep (se 1 (by rfl) ⟨5694785, by rfl⟩ : syracuseStep 7593047 = 11389571) B11389571
theorem B5062031 : Blo 2249435 5062031 := bstep (se 1 (by rfl) ⟨3796523, by rfl⟩ : syracuseStep 5062031 = 7593047) B7593047
theorem B3374687 : Blo 2249435 3374687 := bstep (se 1 (by rfl) ⟨2531015, by rfl⟩ : syracuseStep 3374687 = 5062031) B5062031
theorem B2249791 : Blo 2249435 2249791 := bstep (se 1 (by rfl) ⟨1687343, by rfl⟩ : syracuseStep 2249791 = 3374687) B3374687
theorem B3374693 : Blo 2249435 3374693 := bbase (se 4 (by rfl) ⟨316377, by rfl⟩ : syracuseStep 3374693 = 632755) (by norm_num)
theorem B2249795 : Blo 2249435 2249795 := bstep (se 1 (by rfl) ⟨1687346, by rfl⟩ : syracuseStep 2249795 = 3374693) B3374693
theorem B2402497 : Blo 2249435 2402497 := bbase (se 2 (by rfl) ⟨900936, by rfl⟩ : syracuseStep 2402497 = 1801873) (by norm_num)
theorem B3203329 : Blo 2249435 3203329 := bstep (se 2 (by rfl) ⟨1201248, by rfl⟩ : syracuseStep 3203329 = 2402497) B2402497
theorem B4271105 : Blo 2249435 4271105 := bstep (se 2 (by rfl) ⟨1601664, by rfl⟩ : syracuseStep 4271105 = 3203329) B3203329
theorem B2847403 : Blo 2249435 2847403 := bstep (se 1 (by rfl) ⟨2135552, by rfl⟩ : syracuseStep 2847403 = 4271105) B4271105
theorem B3796537 : Blo 2249435 3796537 := bstep (se 2 (by rfl) ⟨1423701, by rfl⟩ : syracuseStep 3796537 = 2847403) B2847403
theorem B5062049 : Blo 2249435 5062049 := bstep (se 2 (by rfl) ⟨1898268, by rfl⟩ : syracuseStep 5062049 = 3796537) B3796537
theorem B3374699 : Blo 2249435 3374699 := bstep (se 1 (by rfl) ⟨2531024, by rfl⟩ : syracuseStep 3374699 = 5062049) B5062049
theorem B2249799 : Blo 2249435 2249799 := bstep (se 1 (by rfl) ⟨1687349, by rfl⟩ : syracuseStep 2249799 = 3374699) B3374699
theorem B2531029 : Blo 2249435 2531029 := bbase (se 7 (by rfl) ⟨29660, by rfl⟩ : syracuseStep 2531029 = 59321) (by norm_num)
theorem B3374705 : Blo 2249435 3374705 := bstep (se 2 (by rfl) ⟨1265514, by rfl⟩ : syracuseStep 3374705 = 2531029) B2531029
theorem B2249803 : Blo 2249435 2249803 := bstep (se 1 (by rfl) ⟨1687352, by rfl⟩ : syracuseStep 2249803 = 3374705) B3374705
theorem B2847413 : Blo 2249435 2847413 := bbase (se 5 (by rfl) ⟨133472, by rfl⟩ : syracuseStep 2847413 = 266945) (by norm_num)
theorem B7593101 : Blo 2249435 7593101 := bstep (se 3 (by rfl) ⟨1423706, by rfl⟩ : syracuseStep 7593101 = 2847413) B2847413
theorem B5062067 : Blo 2249435 5062067 := bstep (se 1 (by rfl) ⟨3796550, by rfl⟩ : syracuseStep 5062067 = 7593101) B7593101
theorem B3374711 : Blo 2249435 3374711 := bstep (se 1 (by rfl) ⟨2531033, by rfl⟩ : syracuseStep 3374711 = 5062067) B5062067
theorem B2249807 : Blo 2249435 2249807 := bstep (se 1 (by rfl) ⟨1687355, by rfl⟩ : syracuseStep 2249807 = 3374711) B3374711
theorem B3374717 : Blo 2249435 3374717 := bbase (se 3 (by rfl) ⟨632759, by rfl⟩ : syracuseStep 3374717 = 1265519) (by norm_num)
theorem B2249811 : Blo 2249435 2249811 := bstep (se 1 (by rfl) ⟨1687358, by rfl⟩ : syracuseStep 2249811 = 3374717) B3374717
theorem B5062085 : Blo 2249435 5062085 := bbase (se 4 (by rfl) ⟨474570, by rfl⟩ : syracuseStep 5062085 = 949141) (by norm_num)
theorem B3374723 : Blo 2249435 3374723 := bstep (se 1 (by rfl) ⟨2531042, by rfl⟩ : syracuseStep 3374723 = 5062085) B5062085
theorem B2249815 : Blo 2249435 2249815 := bstep (se 1 (by rfl) ⟨1687361, by rfl⟩ : syracuseStep 2249815 = 3374723) B3374723
theorem B10811333 : Blo 2249435 10811333 := bbase (se 4 (by rfl) ⟨1013562, by rfl⟩ : syracuseStep 10811333 = 2027125) (by norm_num)
theorem B7207555 : Blo 2249435 7207555 := bstep (se 1 (by rfl) ⟨5405666, by rfl⟩ : syracuseStep 7207555 = 10811333) B10811333
theorem B9610073 : Blo 2249435 9610073 := bstep (se 2 (by rfl) ⟨3603777, by rfl⟩ : syracuseStep 9610073 = 7207555) B7207555
theorem B6406715 : Blo 2249435 6406715 := bstep (se 1 (by rfl) ⟨4805036, by rfl⟩ : syracuseStep 6406715 = 9610073) B9610073
theorem B4271143 : Blo 2249435 4271143 := bstep (se 1 (by rfl) ⟨3203357, by rfl⟩ : syracuseStep 4271143 = 6406715) B6406715
theorem B5694857 : Blo 2249435 5694857 := bstep (se 2 (by rfl) ⟨2135571, by rfl⟩ : syracuseStep 5694857 = 4271143) B4271143
theorem B3796571 : Blo 2249435 3796571 := bstep (se 1 (by rfl) ⟨2847428, by rfl⟩ : syracuseStep 3796571 = 5694857) B5694857
theorem B2531047 : Blo 2249435 2531047 := bstep (se 1 (by rfl) ⟨1898285, by rfl⟩ : syracuseStep 2531047 = 3796571) B3796571
theorem B3374729 : Blo 2249435 3374729 := bstep (se 2 (by rfl) ⟨1265523, by rfl⟩ : syracuseStep 3374729 = 2531047) B2531047
theorem B2249819 : Blo 2249435 2249819 := bstep (se 1 (by rfl) ⟨1687364, by rfl⟩ : syracuseStep 2249819 = 3374729) B3374729
theorem B11389733 : Blo 2249435 11389733 := bbase (se 4 (by rfl) ⟨1067787, by rfl⟩ : syracuseStep 11389733 = 2135575) (by norm_num)
theorem B7593155 : Blo 2249435 7593155 := bstep (se 1 (by rfl) ⟨5694866, by rfl⟩ : syracuseStep 7593155 = 11389733) B11389733
theorem B5062103 : Blo 2249435 5062103 := bstep (se 1 (by rfl) ⟨3796577, by rfl⟩ : syracuseStep 5062103 = 7593155) B7593155
theorem B3374735 : Blo 2249435 3374735 := bstep (se 1 (by rfl) ⟨2531051, by rfl⟩ : syracuseStep 3374735 = 5062103) B5062103
theorem B2249823 : Blo 2249435 2249823 := bstep (se 1 (by rfl) ⟨1687367, by rfl⟩ : syracuseStep 2249823 = 3374735) B3374735
theorem B3374741 : Blo 2249435 3374741 := bbase (se 6 (by rfl) ⟨79095, by rfl⟩ : syracuseStep 3374741 = 158191) (by norm_num)
theorem B2249827 : Blo 2249435 2249827 := bstep (se 1 (by rfl) ⟨1687370, by rfl⟩ : syracuseStep 2249827 = 3374741) B3374741
theorem B3381805 : Blo 2249435 3381805 := bbase (se 3 (by rfl) ⟨634088, by rfl⟩ : syracuseStep 3381805 = 1268177) (by norm_num)
theorem B4509073 : Blo 2249435 4509073 := bstep (se 2 (by rfl) ⟨1690902, by rfl⟩ : syracuseStep 4509073 = 3381805) B3381805
theorem B24048389 : Blo 2249435 24048389 := bstep (se 4 (by rfl) ⟨2254536, by rfl⟩ : syracuseStep 24048389 = 4509073) B4509073
theorem B16032259 : Blo 2249435 16032259 := bstep (se 1 (by rfl) ⟨12024194, by rfl⟩ : syracuseStep 16032259 = 24048389) B24048389
theorem B85505381 : Blo 2249435 85505381 := bstep (se 4 (by rfl) ⟨8016129, by rfl⟩ : syracuseStep 85505381 = 16032259) B16032259
theorem B57003587 : Blo 2249435 57003587 := bstep (se 1 (by rfl) ⟨42752690, by rfl⟩ : syracuseStep 57003587 = 85505381) B85505381
theorem B38002391 : Blo 2249435 38002391 := bstep (se 1 (by rfl) ⟨28501793, by rfl⟩ : syracuseStep 38002391 = 57003587) B57003587
theorem B25334927 : Blo 2249435 25334927 := bstep (se 1 (by rfl) ⟨19001195, by rfl⟩ : syracuseStep 25334927 = 38002391) B38002391
theorem B16889951 : Blo 2249435 16889951 := bstep (se 1 (by rfl) ⟨12667463, by rfl⟩ : syracuseStep 16889951 = 25334927) B25334927
theorem B11259967 : Blo 2249435 11259967 := bstep (se 1 (by rfl) ⟨8444975, by rfl⟩ : syracuseStep 11259967 = 16889951) B16889951
theorem B15013289 : Blo 2249435 15013289 := bstep (se 2 (by rfl) ⟨5629983, by rfl⟩ : syracuseStep 15013289 = 11259967) B11259967
theorem B40035437 : Blo 2249435 40035437 := bstep (se 3 (by rfl) ⟨7506644, by rfl⟩ : syracuseStep 40035437 = 15013289) B15013289
theorem B26690291 : Blo 2249435 26690291 := bstep (se 1 (by rfl) ⟨20017718, by rfl⟩ : syracuseStep 26690291 = 40035437) B40035437
theorem B17793527 : Blo 2249435 17793527 := bstep (se 1 (by rfl) ⟨13345145, by rfl⟩ : syracuseStep 17793527 = 26690291) B26690291
theorem B47449405 : Blo 2249435 47449405 := bstep (se 3 (by rfl) ⟨8896763, by rfl⟩ : syracuseStep 47449405 = 17793527) B17793527
theorem B63265873 : Blo 2249435 63265873 := bstep (se 2 (by rfl) ⟨23724702, by rfl⟩ : syracuseStep 63265873 = 47449405) B47449405
theorem B84354497 : Blo 2249435 84354497 := bstep (se 2 (by rfl) ⟨31632936, by rfl⟩ : syracuseStep 84354497 = 63265873) B63265873
theorem B56236331 : Blo 2249435 56236331 := bstep (se 1 (by rfl) ⟨42177248, by rfl⟩ : syracuseStep 56236331 = 84354497) B84354497
theorem B37490887 : Blo 2249435 37490887 := bstep (se 1 (by rfl) ⟨28118165, by rfl⟩ : syracuseStep 37490887 = 56236331) B56236331
theorem B49987849 : Blo 2249435 49987849 := bstep (se 2 (by rfl) ⟨18745443, by rfl⟩ : syracuseStep 49987849 = 37490887) B37490887
theorem B66650465 : Blo 2249435 66650465 := bstep (se 2 (by rfl) ⟨24993924, by rfl⟩ : syracuseStep 66650465 = 49987849) B49987849
theorem B177734573 : Blo 2249435 177734573 := bstep (se 3 (by rfl) ⟨33325232, by rfl⟩ : syracuseStep 177734573 = 66650465) B66650465
theorem B118489715 : Blo 2249435 118489715 := bstep (se 1 (by rfl) ⟨88867286, by rfl⟩ : syracuseStep 118489715 = 177734573) B177734573
theorem B78993143 : Blo 2249435 78993143 := bstep (se 1 (by rfl) ⟨59244857, by rfl⟩ : syracuseStep 78993143 = 118489715) B118489715
theorem B52662095 : Blo 2249435 52662095 := bstep (se 1 (by rfl) ⟨39496571, by rfl⟩ : syracuseStep 52662095 = 78993143) B78993143
theorem B35108063 : Blo 2249435 35108063 := bstep (se 1 (by rfl) ⟨26331047, by rfl⟩ : syracuseStep 35108063 = 52662095) B52662095
theorem B23405375 : Blo 2249435 23405375 := bstep (se 1 (by rfl) ⟨17554031, by rfl⟩ : syracuseStep 23405375 = 35108063) B35108063
theorem B62414333 : Blo 2249435 62414333 := bstep (se 3 (by rfl) ⟨11702687, by rfl⟩ : syracuseStep 62414333 = 23405375) B23405375
theorem B41609555 : Blo 2249435 41609555 := bstep (se 1 (by rfl) ⟨31207166, by rfl⟩ : syracuseStep 41609555 = 62414333) B62414333
theorem B27739703 : Blo 2249435 27739703 := bstep (se 1 (by rfl) ⟨20804777, by rfl⟩ : syracuseStep 27739703 = 41609555) B41609555
theorem B73972541 : Blo 2249435 73972541 := bstep (se 3 (by rfl) ⟨13869851, by rfl⟩ : syracuseStep 73972541 = 27739703) B27739703
theorem B197260109 : Blo 2249435 197260109 := bstep (se 3 (by rfl) ⟨36986270, by rfl⟩ : syracuseStep 197260109 = 73972541) B73972541
theorem B131506739 : Blo 2249435 131506739 := bstep (se 1 (by rfl) ⟨98630054, by rfl⟩ : syracuseStep 131506739 = 197260109) B197260109
theorem B87671159 : Blo 2249435 87671159 := bstep (se 1 (by rfl) ⟨65753369, by rfl⟩ : syracuseStep 87671159 = 131506739) B131506739
theorem B58447439 : Blo 2249435 58447439 := bstep (se 1 (by rfl) ⟨43835579, by rfl⟩ : syracuseStep 58447439 = 87671159) B87671159
theorem B38964959 : Blo 2249435 38964959 := bstep (se 1 (by rfl) ⟨29223719, by rfl⟩ : syracuseStep 38964959 = 58447439) B58447439
theorem B25976639 : Blo 2249435 25976639 := bstep (se 1 (by rfl) ⟨19482479, by rfl⟩ : syracuseStep 25976639 = 38964959) B38964959
theorem B69271037 : Blo 2249435 69271037 := bstep (se 3 (by rfl) ⟨12988319, by rfl⟩ : syracuseStep 69271037 = 25976639) B25976639
theorem B46180691 : Blo 2249435 46180691 := bstep (se 1 (by rfl) ⟨34635518, by rfl⟩ : syracuseStep 46180691 = 69271037) B69271037
theorem B30787127 : Blo 2249435 30787127 := bstep (se 1 (by rfl) ⟨23090345, by rfl⟩ : syracuseStep 30787127 = 46180691) B46180691
theorem B20524751 : Blo 2249435 20524751 := bstep (se 1 (by rfl) ⟨15393563, by rfl⟩ : syracuseStep 20524751 = 30787127) B30787127
theorem B13683167 : Blo 2249435 13683167 := bstep (se 1 (by rfl) ⟨10262375, by rfl⟩ : syracuseStep 13683167 = 20524751) B20524751
theorem B9122111 : Blo 2249435 9122111 := bstep (se 1 (by rfl) ⟨6841583, by rfl⟩ : syracuseStep 9122111 = 13683167) B13683167
theorem B6081407 : Blo 2249435 6081407 := bstep (se 1 (by rfl) ⟨4561055, by rfl⟩ : syracuseStep 6081407 = 9122111) B9122111
theorem B4054271 : Blo 2249435 4054271 := bstep (se 1 (by rfl) ⟨3040703, by rfl⟩ : syracuseStep 4054271 = 6081407) B6081407
theorem B10811389 : Blo 2249435 10811389 := bstep (se 3 (by rfl) ⟨2027135, by rfl⟩ : syracuseStep 10811389 = 4054271) B4054271
theorem B14415185 : Blo 2249435 14415185 := bstep (se 2 (by rfl) ⟨5405694, by rfl⟩ : syracuseStep 14415185 = 10811389) B10811389
theorem B9610123 : Blo 2249435 9610123 := bstep (se 1 (by rfl) ⟨7207592, by rfl⟩ : syracuseStep 9610123 = 14415185) B14415185
theorem B12813497 : Blo 2249435 12813497 := bstep (se 2 (by rfl) ⟨4805061, by rfl⟩ : syracuseStep 12813497 = 9610123) B9610123
theorem B8542331 : Blo 2249435 8542331 := bstep (se 1 (by rfl) ⟨6406748, by rfl⟩ : syracuseStep 8542331 = 12813497) B12813497
theorem B5694887 : Blo 2249435 5694887 := bstep (se 1 (by rfl) ⟨4271165, by rfl⟩ : syracuseStep 5694887 = 8542331) B8542331
theorem B3796591 : Blo 2249435 3796591 := bstep (se 1 (by rfl) ⟨2847443, by rfl⟩ : syracuseStep 3796591 = 5694887) B5694887
theorem B5062121 : Blo 2249435 5062121 := bstep (se 2 (by rfl) ⟨1898295, by rfl⟩ : syracuseStep 5062121 = 3796591) B3796591
theorem B3374747 : Blo 2249435 3374747 := bstep (se 1 (by rfl) ⟨2531060, by rfl⟩ : syracuseStep 3374747 = 5062121) B5062121
theorem B2249831 : Blo 2249435 2249831 := bstep (se 1 (by rfl) ⟨1687373, by rfl⟩ : syracuseStep 2249831 = 3374747) B3374747
theorem B2531065 : Blo 2249435 2531065 := bbase (se 2 (by rfl) ⟨949149, by rfl⟩ : syracuseStep 2531065 = 1898299) (by norm_num)
theorem B3374753 : Blo 2249435 3374753 := bstep (se 2 (by rfl) ⟨1265532, by rfl⟩ : syracuseStep 3374753 = 2531065) B2531065
theorem B2249835 : Blo 2249435 2249835 := bstep (se 1 (by rfl) ⟨1687376, by rfl⟩ : syracuseStep 2249835 = 3374753) B3374753
theorem B2702857 : Blo 2249435 2702857 := bbase (se 2 (by rfl) ⟨1013571, by rfl⟩ : syracuseStep 2702857 = 2027143) (by norm_num)
theorem B3603809 : Blo 2249435 3603809 := bstep (se 2 (by rfl) ⟨1351428, by rfl⟩ : syracuseStep 3603809 = 2702857) B2702857
theorem B9610157 : Blo 2249435 9610157 := bstep (se 3 (by rfl) ⟨1801904, by rfl⟩ : syracuseStep 9610157 = 3603809) B3603809
theorem B6406771 : Blo 2249435 6406771 := bstep (se 1 (by rfl) ⟨4805078, by rfl⟩ : syracuseStep 6406771 = 9610157) B9610157
theorem B8542361 : Blo 2249435 8542361 := bstep (se 2 (by rfl) ⟨3203385, by rfl⟩ : syracuseStep 8542361 = 6406771) B6406771
theorem B5694907 : Blo 2249435 5694907 := bstep (se 1 (by rfl) ⟨4271180, by rfl⟩ : syracuseStep 5694907 = 8542361) B8542361
theorem B7593209 : Blo 2249435 7593209 := bstep (se 2 (by rfl) ⟨2847453, by rfl⟩ : syracuseStep 7593209 = 5694907) B5694907
theorem B5062139 : Blo 2249435 5062139 := bstep (se 1 (by rfl) ⟨3796604, by rfl⟩ : syracuseStep 5062139 = 7593209) B7593209
theorem B3374759 : Blo 2249435 3374759 := bstep (se 1 (by rfl) ⟨2531069, by rfl⟩ : syracuseStep 3374759 = 5062139) B5062139
theorem B2249839 : Blo 2249435 2249839 := bstep (se 1 (by rfl) ⟨1687379, by rfl⟩ : syracuseStep 2249839 = 3374759) B3374759
theorem B3374765 : Blo 2249435 3374765 := bbase (se 3 (by rfl) ⟨632768, by rfl⟩ : syracuseStep 3374765 = 1265537) (by norm_num)
theorem B2249843 : Blo 2249435 2249843 := bstep (se 1 (by rfl) ⟨1687382, by rfl⟩ : syracuseStep 2249843 = 3374765) B3374765
theorem B5062157 : Blo 2249435 5062157 := bbase (se 3 (by rfl) ⟨949154, by rfl⟩ : syracuseStep 5062157 = 1898309) (by norm_num)
theorem B3374771 : Blo 2249435 3374771 := bstep (se 1 (by rfl) ⟨2531078, by rfl⟩ : syracuseStep 3374771 = 5062157) B5062157
theorem B2249847 : Blo 2249435 2249847 := bstep (se 1 (by rfl) ⟨1687385, by rfl⟩ : syracuseStep 2249847 = 3374771) B3374771
theorem B2847469 : Blo 2249435 2847469 := bbase (se 3 (by rfl) ⟨533900, by rfl⟩ : syracuseStep 2847469 = 1067801) (by norm_num)
theorem B3796625 : Blo 2249435 3796625 := bstep (se 2 (by rfl) ⟨1423734, by rfl⟩ : syracuseStep 3796625 = 2847469) B2847469
theorem B2531083 : Blo 2249435 2531083 := bstep (se 1 (by rfl) ⟨1898312, by rfl⟩ : syracuseStep 2531083 = 3796625) B3796625
theorem B3374777 : Blo 2249435 3374777 := bstep (se 2 (by rfl) ⟨1265541, by rfl⟩ : syracuseStep 3374777 = 2531083) B2531083
theorem B2249851 : Blo 2249435 2249851 := bstep (se 1 (by rfl) ⟨1687388, by rfl⟩ : syracuseStep 2249851 = 3374777) B3374777
theorem B4109629 : Blo 2249435 4109629 := bbase (se 3 (by rfl) ⟨770555, by rfl⟩ : syracuseStep 4109629 = 1541111) (by norm_num)
theorem B5479505 : Blo 2249435 5479505 := bstep (se 2 (by rfl) ⟨2054814, by rfl⟩ : syracuseStep 5479505 = 4109629) B4109629
theorem B3653003 : Blo 2249435 3653003 := bstep (se 1 (by rfl) ⟨2739752, by rfl⟩ : syracuseStep 3653003 = 5479505) B5479505
theorem B9741341 : Blo 2249435 9741341 := bstep (se 3 (by rfl) ⟨1826501, by rfl⟩ : syracuseStep 9741341 = 3653003) B3653003
theorem B25976909 : Blo 2249435 25976909 := bstep (se 3 (by rfl) ⟨4870670, by rfl⟩ : syracuseStep 25976909 = 9741341) B9741341
theorem B69271757 : Blo 2249435 69271757 := bstep (se 3 (by rfl) ⟨12988454, by rfl⟩ : syracuseStep 69271757 = 25976909) B25976909
theorem B46181171 : Blo 2249435 46181171 := bstep (se 1 (by rfl) ⟨34635878, by rfl⟩ : syracuseStep 46181171 = 69271757) B69271757
theorem B30787447 : Blo 2249435 30787447 := bstep (se 1 (by rfl) ⟨23090585, by rfl⟩ : syracuseStep 30787447 = 46181171) B46181171
theorem B41049929 : Blo 2249435 41049929 := bstep (se 2 (by rfl) ⟨15393723, by rfl⟩ : syracuseStep 41049929 = 30787447) B30787447
theorem B27366619 : Blo 2249435 27366619 := bstep (se 1 (by rfl) ⟨20524964, by rfl⟩ : syracuseStep 27366619 = 41049929) B41049929
theorem B36488825 : Blo 2249435 36488825 := bstep (se 2 (by rfl) ⟨13683309, by rfl⟩ : syracuseStep 36488825 = 27366619) B27366619
theorem B24325883 : Blo 2249435 24325883 := bstep (se 1 (by rfl) ⟨18244412, by rfl⟩ : syracuseStep 24325883 = 36488825) B36488825
theorem B16217255 : Blo 2249435 16217255 := bstep (se 1 (by rfl) ⟨12162941, by rfl⟩ : syracuseStep 16217255 = 24325883) B24325883
theorem B10811503 : Blo 2249435 10811503 := bstep (se 1 (by rfl) ⟨8108627, by rfl⟩ : syracuseStep 10811503 = 16217255) B16217255
theorem B14415337 : Blo 2249435 14415337 := bstep (se 2 (by rfl) ⟨5405751, by rfl⟩ : syracuseStep 14415337 = 10811503) B10811503
theorem B19220449 : Blo 2249435 19220449 := bstep (se 2 (by rfl) ⟨7207668, by rfl⟩ : syracuseStep 19220449 = 14415337) B14415337
theorem B25627265 : Blo 2249435 25627265 := bstep (se 2 (by rfl) ⟨9610224, by rfl⟩ : syracuseStep 25627265 = 19220449) B19220449
theorem B17084843 : Blo 2249435 17084843 := bstep (se 1 (by rfl) ⟨12813632, by rfl⟩ : syracuseStep 17084843 = 25627265) B25627265
theorem B11389895 : Blo 2249435 11389895 := bstep (se 1 (by rfl) ⟨8542421, by rfl⟩ : syracuseStep 11389895 = 17084843) B17084843
theorem B7593263 : Blo 2249435 7593263 := bstep (se 1 (by rfl) ⟨5694947, by rfl⟩ : syracuseStep 7593263 = 11389895) B11389895
theorem B5062175 : Blo 2249435 5062175 := bstep (se 1 (by rfl) ⟨3796631, by rfl⟩ : syracuseStep 5062175 = 7593263) B7593263
theorem B3374783 : Blo 2249435 3374783 := bstep (se 1 (by rfl) ⟨2531087, by rfl⟩ : syracuseStep 3374783 = 5062175) B5062175
theorem B2249855 : Blo 2249435 2249855 := bstep (se 1 (by rfl) ⟨1687391, by rfl⟩ : syracuseStep 2249855 = 3374783) B3374783
theorem B3374789 : Blo 2249435 3374789 := bbase (se 4 (by rfl) ⟨316386, by rfl⟩ : syracuseStep 3374789 = 632773) (by norm_num)
theorem B2249859 : Blo 2249435 2249859 := bstep (se 1 (by rfl) ⟨1687394, by rfl⟩ : syracuseStep 2249859 = 3374789) B3374789
theorem B3796645 : Blo 2249435 3796645 := bbase (se 4 (by rfl) ⟨355935, by rfl⟩ : syracuseStep 3796645 = 711871) (by norm_num)
theorem B5062193 : Blo 2249435 5062193 := bstep (se 2 (by rfl) ⟨1898322, by rfl⟩ : syracuseStep 5062193 = 3796645) B3796645
theorem B3374795 : Blo 2249435 3374795 := bstep (se 1 (by rfl) ⟨2531096, by rfl⟩ : syracuseStep 3374795 = 5062193) B5062193
theorem B2249863 : Blo 2249435 2249863 := bstep (se 1 (by rfl) ⟨1687397, by rfl⟩ : syracuseStep 2249863 = 3374795) B3374795
theorem B2531101 : Blo 2249435 2531101 := bbase (se 3 (by rfl) ⟨474581, by rfl⟩ : syracuseStep 2531101 = 949163) (by norm_num)
theorem B3374801 : Blo 2249435 3374801 := bstep (se 2 (by rfl) ⟨1265550, by rfl⟩ : syracuseStep 3374801 = 2531101) B2531101
theorem B2249867 : Blo 2249435 2249867 := bstep (se 1 (by rfl) ⟨1687400, by rfl⟩ : syracuseStep 2249867 = 3374801) B3374801
theorem B7593317 : Blo 2249435 7593317 := bbase (se 4 (by rfl) ⟨711873, by rfl⟩ : syracuseStep 7593317 = 1423747) (by norm_num)
theorem B5062211 : Blo 2249435 5062211 := bstep (se 1 (by rfl) ⟨3796658, by rfl⟩ : syracuseStep 5062211 = 7593317) B7593317
theorem B3374807 : Blo 2249435 3374807 := bstep (se 1 (by rfl) ⟨2531105, by rfl⟩ : syracuseStep 3374807 = 5062211) B5062211
theorem B2249871 : Blo 2249435 2249871 := bstep (se 1 (by rfl) ⟨1687403, by rfl⟩ : syracuseStep 2249871 = 3374807) B3374807
theorem B3374813 : Blo 2249435 3374813 := bbase (se 3 (by rfl) ⟨632777, by rfl⟩ : syracuseStep 3374813 = 1265555) (by norm_num)
theorem B2249875 : Blo 2249435 2249875 := bstep (se 1 (by rfl) ⟨1687406, by rfl⟩ : syracuseStep 2249875 = 3374813) B3374813
theorem B5062229 : Blo 2249435 5062229 := bbase (se 8 (by rfl) ⟨29661, by rfl⟩ : syracuseStep 5062229 = 59323) (by norm_num)
theorem B3374819 : Blo 2249435 3374819 := bstep (se 1 (by rfl) ⟨2531114, by rfl⟩ : syracuseStep 3374819 = 5062229) B5062229
theorem B2249879 : Blo 2249435 2249879 := bstep (se 1 (by rfl) ⟨1687409, by rfl⟩ : syracuseStep 2249879 = 3374819) B3374819
theorem B4805173 : Blo 2249435 4805173 := bbase (se 5 (by rfl) ⟨225242, by rfl⟩ : syracuseStep 4805173 = 450485) (by norm_num)
theorem B6406897 : Blo 2249435 6406897 := bstep (se 2 (by rfl) ⟨2402586, by rfl⟩ : syracuseStep 6406897 = 4805173) B4805173
theorem B8542529 : Blo 2249435 8542529 := bstep (se 2 (by rfl) ⟨3203448, by rfl⟩ : syracuseStep 8542529 = 6406897) B6406897
theorem B5695019 : Blo 2249435 5695019 := bstep (se 1 (by rfl) ⟨4271264, by rfl⟩ : syracuseStep 5695019 = 8542529) B8542529
theorem B3796679 : Blo 2249435 3796679 := bstep (se 1 (by rfl) ⟨2847509, by rfl⟩ : syracuseStep 3796679 = 5695019) B5695019
theorem B2531119 : Blo 2249435 2531119 := bstep (se 1 (by rfl) ⟨1898339, by rfl⟩ : syracuseStep 2531119 = 3796679) B3796679
theorem B3374825 : Blo 2249435 3374825 := bstep (se 2 (by rfl) ⟨1265559, by rfl⟩ : syracuseStep 3374825 = 2531119) B2531119
theorem B2249883 : Blo 2249435 2249883 := bstep (se 1 (by rfl) ⟨1687412, by rfl⟩ : syracuseStep 2249883 = 3374825) B3374825
theorem B10262629 : Blo 2249435 10262629 := bbase (se 4 (by rfl) ⟨962121, by rfl⟩ : syracuseStep 10262629 = 1924243) (by norm_num)
theorem B13683505 : Blo 2249435 13683505 := bstep (se 2 (by rfl) ⟨5131314, by rfl⟩ : syracuseStep 13683505 = 10262629) B10262629
theorem B18244673 : Blo 2249435 18244673 := bstep (se 2 (by rfl) ⟨6841752, by rfl⟩ : syracuseStep 18244673 = 13683505) B13683505
theorem B12163115 : Blo 2249435 12163115 := bstep (se 1 (by rfl) ⟨9122336, by rfl⟩ : syracuseStep 12163115 = 18244673) B18244673
theorem B8108743 : Blo 2249435 8108743 := bstep (se 1 (by rfl) ⟨6081557, by rfl⟩ : syracuseStep 8108743 = 12163115) B12163115
theorem B10811657 : Blo 2249435 10811657 := bstep (se 2 (by rfl) ⟨4054371, by rfl⟩ : syracuseStep 10811657 = 8108743) B8108743
theorem B28831085 : Blo 2249435 28831085 := bstep (se 3 (by rfl) ⟨5405828, by rfl⟩ : syracuseStep 28831085 = 10811657) B10811657
theorem B19220723 : Blo 2249435 19220723 := bstep (se 1 (by rfl) ⟨14415542, by rfl⟩ : syracuseStep 19220723 = 28831085) B28831085
theorem B12813815 : Blo 2249435 12813815 := bstep (se 1 (by rfl) ⟨9610361, by rfl⟩ : syracuseStep 12813815 = 19220723) B19220723
theorem B8542543 : Blo 2249435 8542543 := bstep (se 1 (by rfl) ⟨6406907, by rfl⟩ : syracuseStep 8542543 = 12813815) B12813815
theorem B11390057 : Blo 2249435 11390057 := bstep (se 2 (by rfl) ⟨4271271, by rfl⟩ : syracuseStep 11390057 = 8542543) B8542543
theorem B7593371 : Blo 2249435 7593371 := bstep (se 1 (by rfl) ⟨5695028, by rfl⟩ : syracuseStep 7593371 = 11390057) B11390057
theorem B5062247 : Blo 2249435 5062247 := bstep (se 1 (by rfl) ⟨3796685, by rfl⟩ : syracuseStep 5062247 = 7593371) B7593371
theorem B3374831 : Blo 2249435 3374831 := bstep (se 1 (by rfl) ⟨2531123, by rfl⟩ : syracuseStep 3374831 = 5062247) B5062247
theorem B2249887 : Blo 2249435 2249887 := bstep (se 1 (by rfl) ⟨1687415, by rfl⟩ : syracuseStep 2249887 = 3374831) B3374831
theorem B3374837 : Blo 2249435 3374837 := bbase (se 5 (by rfl) ⟨158195, by rfl⟩ : syracuseStep 3374837 = 316391) (by norm_num)
theorem B2249891 : Blo 2249435 2249891 := bstep (se 1 (by rfl) ⟨1687418, by rfl⟩ : syracuseStep 2249891 = 3374837) B3374837
theorem B2280593 : Blo 2249435 2280593 := bbase (se 2 (by rfl) ⟨855222, by rfl⟩ : syracuseStep 2280593 = 1710445) (by norm_num)
theorem B6081581 : Blo 2249435 6081581 := bstep (se 3 (by rfl) ⟨1140296, by rfl⟩ : syracuseStep 6081581 = 2280593) B2280593
theorem B4054387 : Blo 2249435 4054387 := bstep (se 1 (by rfl) ⟨3040790, by rfl⟩ : syracuseStep 4054387 = 6081581) B6081581
theorem B5405849 : Blo 2249435 5405849 := bstep (se 2 (by rfl) ⟨2027193, by rfl⟩ : syracuseStep 5405849 = 4054387) B4054387
theorem B3603899 : Blo 2249435 3603899 := bstep (se 1 (by rfl) ⟨2702924, by rfl⟩ : syracuseStep 3603899 = 5405849) B5405849
theorem B9610397 : Blo 2249435 9610397 := bstep (se 3 (by rfl) ⟨1801949, by rfl⟩ : syracuseStep 9610397 = 3603899) B3603899
theorem B6406931 : Blo 2249435 6406931 := bstep (se 1 (by rfl) ⟨4805198, by rfl⟩ : syracuseStep 6406931 = 9610397) B9610397
theorem B4271287 : Blo 2249435 4271287 := bstep (se 1 (by rfl) ⟨3203465, by rfl⟩ : syracuseStep 4271287 = 6406931) B6406931
theorem B5695049 : Blo 2249435 5695049 := bstep (se 2 (by rfl) ⟨2135643, by rfl⟩ : syracuseStep 5695049 = 4271287) B4271287
theorem B3796699 : Blo 2249435 3796699 := bstep (se 1 (by rfl) ⟨2847524, by rfl⟩ : syracuseStep 3796699 = 5695049) B5695049
theorem B5062265 : Blo 2249435 5062265 := bstep (se 2 (by rfl) ⟨1898349, by rfl⟩ : syracuseStep 5062265 = 3796699) B3796699
theorem B3374843 : Blo 2249435 3374843 := bstep (se 1 (by rfl) ⟨2531132, by rfl⟩ : syracuseStep 3374843 = 5062265) B5062265
theorem B2249895 : Blo 2249435 2249895 := bstep (se 1 (by rfl) ⟨1687421, by rfl⟩ : syracuseStep 2249895 = 3374843) B3374843
theorem B2531137 : Blo 2249435 2531137 := bbase (se 2 (by rfl) ⟨949176, by rfl⟩ : syracuseStep 2531137 = 1898353) (by norm_num)
theorem B3374849 : Blo 2249435 3374849 := bstep (se 2 (by rfl) ⟨1265568, by rfl⟩ : syracuseStep 3374849 = 2531137) B2531137
theorem B2249899 : Blo 2249435 2249899 := bstep (se 1 (by rfl) ⟨1687424, by rfl⟩ : syracuseStep 2249899 = 3374849) B3374849
theorem B5695069 : Blo 2249435 5695069 := bbase (se 3 (by rfl) ⟨1067825, by rfl⟩ : syracuseStep 5695069 = 2135651) (by norm_num)
theorem B7593425 : Blo 2249435 7593425 := bstep (se 2 (by rfl) ⟨2847534, by rfl⟩ : syracuseStep 7593425 = 5695069) B5695069
theorem B5062283 : Blo 2249435 5062283 := bstep (se 1 (by rfl) ⟨3796712, by rfl⟩ : syracuseStep 5062283 = 7593425) B7593425
theorem B3374855 : Blo 2249435 3374855 := bstep (se 1 (by rfl) ⟨2531141, by rfl⟩ : syracuseStep 3374855 = 5062283) B5062283
theorem B2249903 : Blo 2249435 2249903 := bstep (se 1 (by rfl) ⟨1687427, by rfl⟩ : syracuseStep 2249903 = 3374855) B3374855
theorem B3374861 : Blo 2249435 3374861 := bbase (se 3 (by rfl) ⟨632786, by rfl⟩ : syracuseStep 3374861 = 1265573) (by norm_num)
theorem B2249907 : Blo 2249435 2249907 := bstep (se 1 (by rfl) ⟨1687430, by rfl⟩ : syracuseStep 2249907 = 3374861) B3374861
theorem B5062301 : Blo 2249435 5062301 := bbase (se 3 (by rfl) ⟨949181, by rfl⟩ : syracuseStep 5062301 = 1898363) (by norm_num)
theorem B3374867 : Blo 2249435 3374867 := bstep (se 1 (by rfl) ⟨2531150, by rfl⟩ : syracuseStep 3374867 = 5062301) B5062301
theorem B2249911 : Blo 2249435 2249911 := bstep (se 1 (by rfl) ⟨1687433, by rfl⟩ : syracuseStep 2249911 = 3374867) B3374867
theorem B3796733 : Blo 2249435 3796733 := bbase (se 3 (by rfl) ⟨711887, by rfl⟩ : syracuseStep 3796733 = 1423775) (by norm_num)
theorem B2531155 : Blo 2249435 2531155 := bstep (se 1 (by rfl) ⟨1898366, by rfl⟩ : syracuseStep 2531155 = 3796733) B3796733
theorem B3374873 : Blo 2249435 3374873 := bstep (se 2 (by rfl) ⟨1265577, by rfl⟩ : syracuseStep 3374873 = 2531155) B2531155
theorem B2249915 : Blo 2249435 2249915 := bstep (se 1 (by rfl) ⟨1687436, by rfl⟩ : syracuseStep 2249915 = 3374873) B3374873
theorem B2702953 : Blo 2249435 2702953 := bbase (se 2 (by rfl) ⟨1013607, by rfl⟩ : syracuseStep 2702953 = 2027215) (by norm_num)
theorem B3603937 : Blo 2249435 3603937 := bstep (se 2 (by rfl) ⟨1351476, by rfl⟩ : syracuseStep 3603937 = 2702953) B2702953
theorem B4805249 : Blo 2249435 4805249 := bstep (se 2 (by rfl) ⟨1801968, by rfl⟩ : syracuseStep 4805249 = 3603937) B3603937
theorem B12813997 : Blo 2249435 12813997 := bstep (se 3 (by rfl) ⟨2402624, by rfl⟩ : syracuseStep 12813997 = 4805249) B4805249
theorem B17085329 : Blo 2249435 17085329 := bstep (se 2 (by rfl) ⟨6406998, by rfl⟩ : syracuseStep 17085329 = 12813997) B12813997
theorem B11390219 : Blo 2249435 11390219 := bstep (se 1 (by rfl) ⟨8542664, by rfl⟩ : syracuseStep 11390219 = 17085329) B17085329
theorem B7593479 : Blo 2249435 7593479 := bstep (se 1 (by rfl) ⟨5695109, by rfl⟩ : syracuseStep 7593479 = 11390219) B11390219
theorem B5062319 : Blo 2249435 5062319 := bstep (se 1 (by rfl) ⟨3796739, by rfl⟩ : syracuseStep 5062319 = 7593479) B7593479
theorem B3374879 : Blo 2249435 3374879 := bstep (se 1 (by rfl) ⟨2531159, by rfl⟩ : syracuseStep 3374879 = 5062319) B5062319
theorem B2249919 : Blo 2249435 2249919 := bstep (se 1 (by rfl) ⟨1687439, by rfl⟩ : syracuseStep 2249919 = 3374879) B3374879
theorem B3374885 : Blo 2249435 3374885 := bbase (se 4 (by rfl) ⟨316395, by rfl⟩ : syracuseStep 3374885 = 632791) (by norm_num)
theorem B2249923 : Blo 2249435 2249923 := bstep (se 1 (by rfl) ⟨1687442, by rfl⟩ : syracuseStep 2249923 = 3374885) B3374885
theorem B2847565 : Blo 2249435 2847565 := bbase (se 3 (by rfl) ⟨533918, by rfl⟩ : syracuseStep 2847565 = 1067837) (by norm_num)
theorem B3796753 : Blo 2249435 3796753 := bstep (se 2 (by rfl) ⟨1423782, by rfl⟩ : syracuseStep 3796753 = 2847565) B2847565
theorem B5062337 : Blo 2249435 5062337 := bstep (se 2 (by rfl) ⟨1898376, by rfl⟩ : syracuseStep 5062337 = 3796753) B3796753
theorem B3374891 : Blo 2249435 3374891 := bstep (se 1 (by rfl) ⟨2531168, by rfl⟩ : syracuseStep 3374891 = 5062337) B5062337
theorem B2249927 : Blo 2249435 2249927 := bstep (se 1 (by rfl) ⟨1687445, by rfl⟩ : syracuseStep 2249927 = 3374891) B3374891
theorem B2531173 : Blo 2249435 2531173 := bbase (se 4 (by rfl) ⟨237297, by rfl⟩ : syracuseStep 2531173 = 474595) (by norm_num)
theorem B3374897 : Blo 2249435 3374897 := bstep (se 2 (by rfl) ⟨1265586, by rfl⟩ : syracuseStep 3374897 = 2531173) B2531173
theorem B2249931 : Blo 2249435 2249931 := bstep (se 1 (by rfl) ⟨1687448, by rfl⟩ : syracuseStep 2249931 = 3374897) B3374897
theorem B6407045 : Blo 2249435 6407045 := bbase (se 4 (by rfl) ⟨600660, by rfl⟩ : syracuseStep 6407045 = 1201321) (by norm_num)
theorem B4271363 : Blo 2249435 4271363 := bstep (se 1 (by rfl) ⟨3203522, by rfl⟩ : syracuseStep 4271363 = 6407045) B6407045
theorem B2847575 : Blo 2249435 2847575 := bstep (se 1 (by rfl) ⟨2135681, by rfl⟩ : syracuseStep 2847575 = 4271363) B4271363
theorem B7593533 : Blo 2249435 7593533 := bstep (se 3 (by rfl) ⟨1423787, by rfl⟩ : syracuseStep 7593533 = 2847575) B2847575
theorem B5062355 : Blo 2249435 5062355 := bstep (se 1 (by rfl) ⟨3796766, by rfl⟩ : syracuseStep 5062355 = 7593533) B7593533
theorem B3374903 : Blo 2249435 3374903 := bstep (se 1 (by rfl) ⟨2531177, by rfl⟩ : syracuseStep 3374903 = 5062355) B5062355
theorem B2249935 : Blo 2249435 2249935 := bstep (se 1 (by rfl) ⟨1687451, by rfl⟩ : syracuseStep 2249935 = 3374903) B3374903
theorem B3374909 : Blo 2249435 3374909 := bbase (se 3 (by rfl) ⟨632795, by rfl⟩ : syracuseStep 3374909 = 1265591) (by norm_num)
theorem B2249939 : Blo 2249435 2249939 := bstep (se 1 (by rfl) ⟨1687454, by rfl⟩ : syracuseStep 2249939 = 3374909) B3374909
theorem B5062373 : Blo 2249435 5062373 := bbase (se 4 (by rfl) ⟨474597, by rfl⟩ : syracuseStep 5062373 = 949195) (by norm_num)
theorem B3374915 : Blo 2249435 3374915 := bstep (se 1 (by rfl) ⟨2531186, by rfl⟩ : syracuseStep 3374915 = 5062373) B5062373
theorem B2249943 : Blo 2249435 2249943 := bstep (se 1 (by rfl) ⟨1687457, by rfl⟩ : syracuseStep 2249943 = 3374915) B3374915
theorem B5695181 : Blo 2249435 5695181 := bbase (se 3 (by rfl) ⟨1067846, by rfl⟩ : syracuseStep 5695181 = 2135693) (by norm_num)
theorem B3796787 : Blo 2249435 3796787 := bstep (se 1 (by rfl) ⟨2847590, by rfl⟩ : syracuseStep 3796787 = 5695181) B5695181
theorem B2531191 : Blo 2249435 2531191 := bstep (se 1 (by rfl) ⟨1898393, by rfl⟩ : syracuseStep 2531191 = 3796787) B3796787
theorem B3374921 : Blo 2249435 3374921 := bstep (se 2 (by rfl) ⟨1265595, by rfl⟩ : syracuseStep 3374921 = 2531191) B2531191
theorem B2249947 : Blo 2249435 2249947 := bstep (se 1 (by rfl) ⟨1687460, by rfl⟩ : syracuseStep 2249947 = 3374921) B3374921
theorem B3603989 : Blo 2249435 3603989 := bbase (se 6 (by rfl) ⟨84468, by rfl⟩ : syracuseStep 3603989 = 168937) (by norm_num)
theorem B2402659 : Blo 2249435 2402659 := bstep (se 1 (by rfl) ⟨1801994, by rfl⟩ : syracuseStep 2402659 = 3603989) B3603989
theorem B3203545 : Blo 2249435 3203545 := bstep (se 2 (by rfl) ⟨1201329, by rfl⟩ : syracuseStep 3203545 = 2402659) B2402659
theorem B4271393 : Blo 2249435 4271393 := bstep (se 2 (by rfl) ⟨1601772, by rfl⟩ : syracuseStep 4271393 = 3203545) B3203545
theorem B11390381 : Blo 2249435 11390381 := bstep (se 3 (by rfl) ⟨2135696, by rfl⟩ : syracuseStep 11390381 = 4271393) B4271393
theorem B7593587 : Blo 2249435 7593587 := bstep (se 1 (by rfl) ⟨5695190, by rfl⟩ : syracuseStep 7593587 = 11390381) B11390381
theorem B5062391 : Blo 2249435 5062391 := bstep (se 1 (by rfl) ⟨3796793, by rfl⟩ : syracuseStep 5062391 = 7593587) B7593587
theorem B3374927 : Blo 2249435 3374927 := bstep (se 1 (by rfl) ⟨2531195, by rfl⟩ : syracuseStep 3374927 = 5062391) B5062391
theorem B2249951 : Blo 2249435 2249951 := bstep (se 1 (by rfl) ⟨1687463, by rfl⟩ : syracuseStep 2249951 = 3374927) B3374927
theorem B3374933 : Blo 2249435 3374933 := bbase (se 9 (by rfl) ⟨9887, by rfl⟩ : syracuseStep 3374933 = 19775) (by norm_num)
theorem B2249955 : Blo 2249435 2249955 := bstep (se 1 (by rfl) ⟨1687466, by rfl⟩ : syracuseStep 2249955 = 3374933) B3374933
theorem B10812005 : Blo 2249435 10812005 := bbase (se 4 (by rfl) ⟨1013625, by rfl⟩ : syracuseStep 10812005 = 2027251) (by norm_num)
theorem B7208003 : Blo 2249435 7208003 := bstep (se 1 (by rfl) ⟨5406002, by rfl⟩ : syracuseStep 7208003 = 10812005) B10812005
theorem B4805335 : Blo 2249435 4805335 := bstep (se 1 (by rfl) ⟨3604001, by rfl⟩ : syracuseStep 4805335 = 7208003) B7208003
theorem B6407113 : Blo 2249435 6407113 := bstep (se 2 (by rfl) ⟨2402667, by rfl⟩ : syracuseStep 6407113 = 4805335) B4805335
theorem B8542817 : Blo 2249435 8542817 := bstep (se 2 (by rfl) ⟨3203556, by rfl⟩ : syracuseStep 8542817 = 6407113) B6407113
theorem B5695211 : Blo 2249435 5695211 := bstep (se 1 (by rfl) ⟨4271408, by rfl⟩ : syracuseStep 5695211 = 8542817) B8542817
theorem B3796807 : Blo 2249435 3796807 := bstep (se 1 (by rfl) ⟨2847605, by rfl⟩ : syracuseStep 3796807 = 5695211) B5695211
theorem B5062409 : Blo 2249435 5062409 := bstep (se 2 (by rfl) ⟨1898403, by rfl⟩ : syracuseStep 5062409 = 3796807) B3796807
theorem B3374939 : Blo 2249435 3374939 := bstep (se 1 (by rfl) ⟨2531204, by rfl⟩ : syracuseStep 3374939 = 5062409) B5062409
theorem B2249959 : Blo 2249435 2249959 := bstep (se 1 (by rfl) ⟨1687469, by rfl⟩ : syracuseStep 2249959 = 3374939) B3374939
theorem B2531209 : Blo 2249435 2531209 := bbase (se 2 (by rfl) ⟨949203, by rfl⟩ : syracuseStep 2531209 = 1898407) (by norm_num)
theorem B3374945 : Blo 2249435 3374945 := bstep (se 2 (by rfl) ⟨1265604, by rfl⟩ : syracuseStep 3374945 = 2531209) B2531209
theorem B2249963 : Blo 2249435 2249963 := bstep (se 1 (by rfl) ⟨1687472, by rfl⟩ : syracuseStep 2249963 = 3374945) B3374945
theorem B4329701 : Blo 2249435 4329701 := bbase (se 4 (by rfl) ⟨405909, by rfl⟩ : syracuseStep 4329701 = 811819) (by norm_num)
theorem B2886467 : Blo 2249435 2886467 := bstep (se 1 (by rfl) ⟨2164850, by rfl⟩ : syracuseStep 2886467 = 4329701) B4329701
theorem B7697245 : Blo 2249435 7697245 := bstep (se 3 (by rfl) ⟨1443233, by rfl⟩ : syracuseStep 7697245 = 2886467) B2886467
theorem B10262993 : Blo 2249435 10262993 := bstep (se 2 (by rfl) ⟨3848622, by rfl⟩ : syracuseStep 10262993 = 7697245) B7697245
theorem B109471925 : Blo 2249435 109471925 := bstep (se 5 (by rfl) ⟨5131496, by rfl⟩ : syracuseStep 109471925 = 10262993) B10262993
theorem B72981283 : Blo 2249435 72981283 := bstep (se 1 (by rfl) ⟨54735962, by rfl⟩ : syracuseStep 72981283 = 109471925) B109471925
theorem B97308377 : Blo 2249435 97308377 := bstep (se 2 (by rfl) ⟨36490641, by rfl⟩ : syracuseStep 97308377 = 72981283) B72981283
theorem B64872251 : Blo 2249435 64872251 := bstep (se 1 (by rfl) ⟨48654188, by rfl⟩ : syracuseStep 64872251 = 97308377) B97308377
theorem B43248167 : Blo 2249435 43248167 := bstep (se 1 (by rfl) ⟨32436125, by rfl⟩ : syracuseStep 43248167 = 64872251) B64872251
theorem B28832111 : Blo 2249435 28832111 := bstep (se 1 (by rfl) ⟨21624083, by rfl⟩ : syracuseStep 28832111 = 43248167) B43248167
theorem B19221407 : Blo 2249435 19221407 := bstep (se 1 (by rfl) ⟨14416055, by rfl⟩ : syracuseStep 19221407 = 28832111) B28832111
theorem B12814271 : Blo 2249435 12814271 := bstep (se 1 (by rfl) ⟨9610703, by rfl⟩ : syracuseStep 12814271 = 19221407) B19221407
theorem B8542847 : Blo 2249435 8542847 := bstep (se 1 (by rfl) ⟨6407135, by rfl⟩ : syracuseStep 8542847 = 12814271) B12814271
theorem B5695231 : Blo 2249435 5695231 := bstep (se 1 (by rfl) ⟨4271423, by rfl⟩ : syracuseStep 5695231 = 8542847) B8542847
theorem B7593641 : Blo 2249435 7593641 := bstep (se 2 (by rfl) ⟨2847615, by rfl⟩ : syracuseStep 7593641 = 5695231) B5695231
theorem B5062427 : Blo 2249435 5062427 := bstep (se 1 (by rfl) ⟨3796820, by rfl⟩ : syracuseStep 5062427 = 7593641) B7593641
theorem B3374951 : Blo 2249435 3374951 := bstep (se 1 (by rfl) ⟨2531213, by rfl⟩ : syracuseStep 3374951 = 5062427) B5062427
theorem B2249967 : Blo 2249435 2249967 := bstep (se 1 (by rfl) ⟨1687475, by rfl⟩ : syracuseStep 2249967 = 3374951) B3374951
theorem B3374957 : Blo 2249435 3374957 := bbase (se 3 (by rfl) ⟨632804, by rfl⟩ : syracuseStep 3374957 = 1265609) (by norm_num)
theorem B2249971 : Blo 2249435 2249971 := bstep (se 1 (by rfl) ⟨1687478, by rfl⟩ : syracuseStep 2249971 = 3374957) B3374957
theorem B5062445 : Blo 2249435 5062445 := bbase (se 3 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 5062445 = 1898417) (by norm_num)
theorem B3374963 : Blo 2249435 3374963 := bstep (se 1 (by rfl) ⟨2531222, by rfl⟩ : syracuseStep 3374963 = 5062445) B5062445
theorem B2249975 : Blo 2249435 2249975 := bstep (se 1 (by rfl) ⟨1687481, by rfl⟩ : syracuseStep 2249975 = 3374963) B3374963
theorem B9610757 : Blo 2249435 9610757 := bbase (se 4 (by rfl) ⟨901008, by rfl⟩ : syracuseStep 9610757 = 1802017) (by norm_num)
theorem B6407171 : Blo 2249435 6407171 := bstep (se 1 (by rfl) ⟨4805378, by rfl⟩ : syracuseStep 6407171 = 9610757) B9610757
theorem B4271447 : Blo 2249435 4271447 := bstep (se 1 (by rfl) ⟨3203585, by rfl⟩ : syracuseStep 4271447 = 6407171) B6407171
theorem B2847631 : Blo 2249435 2847631 := bstep (se 1 (by rfl) ⟨2135723, by rfl⟩ : syracuseStep 2847631 = 4271447) B4271447
theorem B3796841 : Blo 2249435 3796841 := bstep (se 2 (by rfl) ⟨1423815, by rfl⟩ : syracuseStep 3796841 = 2847631) B2847631
theorem B2531227 : Blo 2249435 2531227 := bstep (se 1 (by rfl) ⟨1898420, by rfl⟩ : syracuseStep 2531227 = 3796841) B3796841
theorem B3374969 : Blo 2249435 3374969 := bstep (se 2 (by rfl) ⟨1265613, by rfl⟩ : syracuseStep 3374969 = 2531227) B2531227
theorem B2249979 : Blo 2249435 2249979 := bstep (se 1 (by rfl) ⟨1687484, by rfl⟩ : syracuseStep 2249979 = 3374969) B3374969
theorem B4329733 : Blo 2249435 4329733 := bbase (se 4 (by rfl) ⟨405912, by rfl⟩ : syracuseStep 4329733 = 811825) (by norm_num)
theorem B5772977 : Blo 2249435 5772977 := bstep (se 2 (by rfl) ⟨2164866, by rfl⟩ : syracuseStep 5772977 = 4329733) B4329733
theorem B3848651 : Blo 2249435 3848651 := bstep (se 1 (by rfl) ⟨2886488, by rfl⟩ : syracuseStep 3848651 = 5772977) B5772977
theorem B2565767 : Blo 2249435 2565767 := bstep (se 1 (by rfl) ⟨1924325, by rfl⟩ : syracuseStep 2565767 = 3848651) B3848651
theorem B6842045 : Blo 2249435 6842045 := bstep (se 3 (by rfl) ⟨1282883, by rfl⟩ : syracuseStep 6842045 = 2565767) B2565767
theorem B4561363 : Blo 2249435 4561363 := bstep (se 1 (by rfl) ⟨3421022, by rfl⟩ : syracuseStep 4561363 = 6842045) B6842045
theorem B6081817 : Blo 2249435 6081817 := bstep (se 2 (by rfl) ⟨2280681, by rfl⟩ : syracuseStep 6081817 = 4561363) B4561363
theorem B8109089 : Blo 2249435 8109089 := bstep (se 2 (by rfl) ⟨3040908, by rfl⟩ : syracuseStep 8109089 = 6081817) B6081817
theorem B5406059 : Blo 2249435 5406059 := bstep (se 1 (by rfl) ⟨4054544, by rfl⟩ : syracuseStep 5406059 = 8109089) B8109089
theorem B14416157 : Blo 2249435 14416157 := bstep (se 3 (by rfl) ⟨2703029, by rfl⟩ : syracuseStep 14416157 = 5406059) B5406059
theorem B38443085 : Blo 2249435 38443085 := bstep (se 3 (by rfl) ⟨7208078, by rfl⟩ : syracuseStep 38443085 = 14416157) B14416157
theorem B25628723 : Blo 2249435 25628723 := bstep (se 1 (by rfl) ⟨19221542, by rfl⟩ : syracuseStep 25628723 = 38443085) B38443085
theorem B17085815 : Blo 2249435 17085815 := bstep (se 1 (by rfl) ⟨12814361, by rfl⟩ : syracuseStep 17085815 = 25628723) B25628723
theorem B11390543 : Blo 2249435 11390543 := bstep (se 1 (by rfl) ⟨8542907, by rfl⟩ : syracuseStep 11390543 = 17085815) B17085815
theorem B7593695 : Blo 2249435 7593695 := bstep (se 1 (by rfl) ⟨5695271, by rfl⟩ : syracuseStep 7593695 = 11390543) B11390543
theorem B5062463 : Blo 2249435 5062463 := bstep (se 1 (by rfl) ⟨3796847, by rfl⟩ : syracuseStep 5062463 = 7593695) B7593695
theorem B3374975 : Blo 2249435 3374975 := bstep (se 1 (by rfl) ⟨2531231, by rfl⟩ : syracuseStep 3374975 = 5062463) B5062463
theorem B2249983 : Blo 2249435 2249983 := bstep (se 1 (by rfl) ⟨1687487, by rfl⟩ : syracuseStep 2249983 = 3374975) B3374975
theorem B3374981 : Blo 2249435 3374981 := bbase (se 4 (by rfl) ⟨316404, by rfl⟩ : syracuseStep 3374981 = 632809) (by norm_num)
theorem B2249987 : Blo 2249435 2249987 := bstep (se 1 (by rfl) ⟨1687490, by rfl⟩ : syracuseStep 2249987 = 3374981) B3374981
theorem B3796861 : Blo 2249435 3796861 := bbase (se 3 (by rfl) ⟨711911, by rfl⟩ : syracuseStep 3796861 = 1423823) (by norm_num)
theorem B5062481 : Blo 2249435 5062481 := bstep (se 2 (by rfl) ⟨1898430, by rfl⟩ : syracuseStep 5062481 = 3796861) B3796861
theorem B3374987 : Blo 2249435 3374987 := bstep (se 1 (by rfl) ⟨2531240, by rfl⟩ : syracuseStep 3374987 = 5062481) B5062481
theorem B2249991 : Blo 2249435 2249991 := bstep (se 1 (by rfl) ⟨1687493, by rfl⟩ : syracuseStep 2249991 = 3374987) B3374987
theorem B2531245 : Blo 2249435 2531245 := bbase (se 3 (by rfl) ⟨474608, by rfl⟩ : syracuseStep 2531245 = 949217) (by norm_num)
theorem B3374993 : Blo 2249435 3374993 := bstep (se 2 (by rfl) ⟨1265622, by rfl⟩ : syracuseStep 3374993 = 2531245) B2531245
theorem B2249995 : Blo 2249435 2249995 := bstep (se 1 (by rfl) ⟨1687496, by rfl⟩ : syracuseStep 2249995 = 3374993) B3374993
theorem B7593749 : Blo 2249435 7593749 := bbase (se 6 (by rfl) ⟨177978, by rfl⟩ : syracuseStep 7593749 = 355957) (by norm_num)
theorem B5062499 : Blo 2249435 5062499 := bstep (se 1 (by rfl) ⟨3796874, by rfl⟩ : syracuseStep 5062499 = 7593749) B7593749
theorem B3374999 : Blo 2249435 3374999 := bstep (se 1 (by rfl) ⟨2531249, by rfl⟩ : syracuseStep 3374999 = 5062499) B5062499
theorem B2249999 : Blo 2249435 2249999 := bstep (se 1 (by rfl) ⟨1687499, by rfl⟩ : syracuseStep 2249999 = 3374999) B3374999
theorem B3375005 : Blo 2249435 3375005 := bbase (se 3 (by rfl) ⟨632813, by rfl⟩ : syracuseStep 3375005 = 1265627) (by norm_num)
theorem B2250003 : Blo 2249435 2250003 := bstep (se 1 (by rfl) ⟨1687502, by rfl⟩ : syracuseStep 2250003 = 3375005) B3375005
theorem B5062517 : Blo 2249435 5062517 := bbase (se 5 (by rfl) ⟨237305, by rfl⟩ : syracuseStep 5062517 = 474611) (by norm_num)
theorem B3375011 : Blo 2249435 3375011 := bstep (se 1 (by rfl) ⟨2531258, by rfl⟩ : syracuseStep 3375011 = 5062517) B5062517
theorem B2250007 : Blo 2249435 2250007 := bstep (se 1 (by rfl) ⟨1687505, by rfl⟩ : syracuseStep 2250007 = 3375011) B3375011
theorem B7306517 : Blo 2249435 7306517 := bbase (se 6 (by rfl) ⟨171246, by rfl⟩ : syracuseStep 7306517 = 342493) (by norm_num)
theorem B4871011 : Blo 2249435 4871011 := bstep (se 1 (by rfl) ⟨3653258, by rfl⟩ : syracuseStep 4871011 = 7306517) B7306517
theorem B6494681 : Blo 2249435 6494681 := bstep (se 2 (by rfl) ⟨2435505, by rfl⟩ : syracuseStep 6494681 = 4871011) B4871011
theorem B4329787 : Blo 2249435 4329787 := bstep (se 1 (by rfl) ⟨3247340, by rfl⟩ : syracuseStep 4329787 = 6494681) B6494681
theorem B5773049 : Blo 2249435 5773049 := bstep (se 2 (by rfl) ⟨2164893, by rfl⟩ : syracuseStep 5773049 = 4329787) B4329787
theorem B3848699 : Blo 2249435 3848699 := bstep (se 1 (by rfl) ⟨2886524, by rfl⟩ : syracuseStep 3848699 = 5773049) B5773049
theorem B2565799 : Blo 2249435 2565799 := bstep (se 1 (by rfl) ⟨1924349, by rfl⟩ : syracuseStep 2565799 = 3848699) B3848699
theorem B13684261 : Blo 2249435 13684261 := bstep (se 4 (by rfl) ⟨1282899, by rfl⟩ : syracuseStep 13684261 = 2565799) B2565799
theorem B18245681 : Blo 2249435 18245681 := bstep (se 2 (by rfl) ⟨6842130, by rfl⟩ : syracuseStep 18245681 = 13684261) B13684261
theorem B12163787 : Blo 2249435 12163787 := bstep (se 1 (by rfl) ⟨9122840, by rfl⟩ : syracuseStep 12163787 = 18245681) B18245681
theorem B8109191 : Blo 2249435 8109191 := bstep (se 1 (by rfl) ⟨6081893, by rfl⟩ : syracuseStep 8109191 = 12163787) B12163787
theorem B21624509 : Blo 2249435 21624509 := bstep (se 3 (by rfl) ⟨4054595, by rfl⟩ : syracuseStep 21624509 = 8109191) B8109191
theorem B14416339 : Blo 2249435 14416339 := bstep (se 1 (by rfl) ⟨10812254, by rfl⟩ : syracuseStep 14416339 = 21624509) B21624509
theorem B19221785 : Blo 2249435 19221785 := bstep (se 2 (by rfl) ⟨7208169, by rfl⟩ : syracuseStep 19221785 = 14416339) B14416339
theorem B12814523 : Blo 2249435 12814523 := bstep (se 1 (by rfl) ⟨9610892, by rfl⟩ : syracuseStep 12814523 = 19221785) B19221785
theorem B8543015 : Blo 2249435 8543015 := bstep (se 1 (by rfl) ⟨6407261, by rfl⟩ : syracuseStep 8543015 = 12814523) B12814523
theorem B5695343 : Blo 2249435 5695343 := bstep (se 1 (by rfl) ⟨4271507, by rfl⟩ : syracuseStep 5695343 = 8543015) B8543015
theorem B3796895 : Blo 2249435 3796895 := bstep (se 1 (by rfl) ⟨2847671, by rfl⟩ : syracuseStep 3796895 = 5695343) B5695343
theorem B2531263 : Blo 2249435 2531263 := bstep (se 1 (by rfl) ⟨1898447, by rfl⟩ : syracuseStep 2531263 = 3796895) B3796895
theorem B3375017 : Blo 2249435 3375017 := bstep (se 2 (by rfl) ⟨1265631, by rfl⟩ : syracuseStep 3375017 = 2531263) B2531263
theorem B2250011 : Blo 2249435 2250011 := bstep (se 1 (by rfl) ⟨1687508, by rfl⟩ : syracuseStep 2250011 = 3375017) B3375017
theorem B8543029 : Blo 2249435 8543029 := bbase (se 5 (by rfl) ⟨400454, by rfl⟩ : syracuseStep 8543029 = 800909) (by norm_num)
theorem B11390705 : Blo 2249435 11390705 := bstep (se 2 (by rfl) ⟨4271514, by rfl⟩ : syracuseStep 11390705 = 8543029) B8543029
theorem B7593803 : Blo 2249435 7593803 := bstep (se 1 (by rfl) ⟨5695352, by rfl⟩ : syracuseStep 7593803 = 11390705) B11390705
theorem B5062535 : Blo 2249435 5062535 := bstep (se 1 (by rfl) ⟨3796901, by rfl⟩ : syracuseStep 5062535 = 7593803) B7593803
theorem B3375023 : Blo 2249435 3375023 := bstep (se 1 (by rfl) ⟨2531267, by rfl⟩ : syracuseStep 3375023 = 5062535) B5062535
theorem B2250015 : Blo 2249435 2250015 := bstep (se 1 (by rfl) ⟨1687511, by rfl⟩ : syracuseStep 2250015 = 3375023) B3375023
theorem B3375029 : Blo 2249435 3375029 := bbase (se 5 (by rfl) ⟨158204, by rfl⟩ : syracuseStep 3375029 = 316409) (by norm_num)
theorem B2250019 : Blo 2249435 2250019 := bstep (se 1 (by rfl) ⟨1687514, by rfl⟩ : syracuseStep 2250019 = 3375029) B3375029
theorem B5695373 : Blo 2249435 5695373 := bbase (se 3 (by rfl) ⟨1067882, by rfl⟩ : syracuseStep 5695373 = 2135765) (by norm_num)
theorem B3796915 : Blo 2249435 3796915 := bstep (se 1 (by rfl) ⟨2847686, by rfl⟩ : syracuseStep 3796915 = 5695373) B5695373
theorem B5062553 : Blo 2249435 5062553 := bstep (se 2 (by rfl) ⟨1898457, by rfl⟩ : syracuseStep 5062553 = 3796915) B3796915
theorem B3375035 : Blo 2249435 3375035 := bstep (se 1 (by rfl) ⟨2531276, by rfl⟩ : syracuseStep 3375035 = 5062553) B5062553
theorem B2250023 : Blo 2249435 2250023 := bstep (se 1 (by rfl) ⟨1687517, by rfl⟩ : syracuseStep 2250023 = 3375035) B3375035
theorem B2531281 : Blo 2249435 2531281 := bbase (se 2 (by rfl) ⟨949230, by rfl⟩ : syracuseStep 2531281 = 1898461) (by norm_num)
theorem B3375041 : Blo 2249435 3375041 := bstep (se 2 (by rfl) ⟨1265640, by rfl⟩ : syracuseStep 3375041 = 2531281) B2531281
theorem B2250027 : Blo 2249435 2250027 := bstep (se 1 (by rfl) ⟨1687520, by rfl⟩ : syracuseStep 2250027 = 3375041) B3375041
theorem B3604117 : Blo 2249435 3604117 := bbase (se 6 (by rfl) ⟨84471, by rfl⟩ : syracuseStep 3604117 = 168943) (by norm_num)
theorem B4805489 : Blo 2249435 4805489 := bstep (se 2 (by rfl) ⟨1802058, by rfl⟩ : syracuseStep 4805489 = 3604117) B3604117
theorem B3203659 : Blo 2249435 3203659 := bstep (se 1 (by rfl) ⟨2402744, by rfl⟩ : syracuseStep 3203659 = 4805489) B4805489
theorem B4271545 : Blo 2249435 4271545 := bstep (se 2 (by rfl) ⟨1601829, by rfl⟩ : syracuseStep 4271545 = 3203659) B3203659
theorem B5695393 : Blo 2249435 5695393 := bstep (se 2 (by rfl) ⟨2135772, by rfl⟩ : syracuseStep 5695393 = 4271545) B4271545
theorem B7593857 : Blo 2249435 7593857 := bstep (se 2 (by rfl) ⟨2847696, by rfl⟩ : syracuseStep 7593857 = 5695393) B5695393
theorem B5062571 : Blo 2249435 5062571 := bstep (se 1 (by rfl) ⟨3796928, by rfl⟩ : syracuseStep 5062571 = 7593857) B7593857
theorem B3375047 : Blo 2249435 3375047 := bstep (se 1 (by rfl) ⟨2531285, by rfl⟩ : syracuseStep 3375047 = 5062571) B5062571
theorem B2250031 : Blo 2249435 2250031 := bstep (se 1 (by rfl) ⟨1687523, by rfl⟩ : syracuseStep 2250031 = 3375047) B3375047
theorem B3375053 : Blo 2249435 3375053 := bbase (se 3 (by rfl) ⟨632822, by rfl⟩ : syracuseStep 3375053 = 1265645) (by norm_num)
theorem B2250035 : Blo 2249435 2250035 := bstep (se 1 (by rfl) ⟨1687526, by rfl⟩ : syracuseStep 2250035 = 3375053) B3375053
theorem B5062589 : Blo 2249435 5062589 := bbase (se 3 (by rfl) ⟨949235, by rfl⟩ : syracuseStep 5062589 = 1898471) (by norm_num)
theorem B3375059 : Blo 2249435 3375059 := bstep (se 1 (by rfl) ⟨2531294, by rfl⟩ : syracuseStep 3375059 = 5062589) B5062589
theorem B2250039 : Blo 2249435 2250039 := bstep (se 1 (by rfl) ⟨1687529, by rfl⟩ : syracuseStep 2250039 = 3375059) B3375059
theorem B3796949 : Blo 2249435 3796949 := bbase (se 7 (by rfl) ⟨44495, by rfl⟩ : syracuseStep 3796949 = 88991) (by norm_num)
theorem B2531299 : Blo 2249435 2531299 := bstep (se 1 (by rfl) ⟨1898474, by rfl⟩ : syracuseStep 2531299 = 3796949) B3796949
theorem B3375065 : Blo 2249435 3375065 := bstep (se 2 (by rfl) ⟨1265649, by rfl⟩ : syracuseStep 3375065 = 2531299) B2531299
theorem B2250043 : Blo 2249435 2250043 := bstep (se 1 (by rfl) ⟨1687532, by rfl⟩ : syracuseStep 2250043 = 3375065) B3375065
theorem B9611045 : Blo 2249435 9611045 := bbase (se 4 (by rfl) ⟨901035, by rfl⟩ : syracuseStep 9611045 = 1802071) (by norm_num)
theorem B6407363 : Blo 2249435 6407363 := bstep (se 1 (by rfl) ⟨4805522, by rfl⟩ : syracuseStep 6407363 = 9611045) B9611045
theorem B17086301 : Blo 2249435 17086301 := bstep (se 3 (by rfl) ⟨3203681, by rfl⟩ : syracuseStep 17086301 = 6407363) B6407363
theorem B11390867 : Blo 2249435 11390867 := bstep (se 1 (by rfl) ⟨8543150, by rfl⟩ : syracuseStep 11390867 = 17086301) B17086301
theorem B7593911 : Blo 2249435 7593911 := bstep (se 1 (by rfl) ⟨5695433, by rfl⟩ : syracuseStep 7593911 = 11390867) B11390867
theorem B5062607 : Blo 2249435 5062607 := bstep (se 1 (by rfl) ⟨3796955, by rfl⟩ : syracuseStep 5062607 = 7593911) B7593911
theorem B3375071 : Blo 2249435 3375071 := bstep (se 1 (by rfl) ⟨2531303, by rfl⟩ : syracuseStep 3375071 = 5062607) B5062607
theorem B2250047 : Blo 2249435 2250047 := bstep (se 1 (by rfl) ⟨1687535, by rfl⟩ : syracuseStep 2250047 = 3375071) B3375071
theorem B3375077 : Blo 2249435 3375077 := bbase (se 4 (by rfl) ⟨316413, by rfl⟩ : syracuseStep 3375077 = 632827) (by norm_num)
theorem B2250051 : Blo 2249435 2250051 := bstep (se 1 (by rfl) ⟨1687538, by rfl⟩ : syracuseStep 2250051 = 3375077) B3375077
theorem B3421133 : Blo 2249435 3421133 := bbase (se 3 (by rfl) ⟨641462, by rfl⟩ : syracuseStep 3421133 = 1282925) (by norm_num)
theorem B2280755 : Blo 2249435 2280755 := bstep (se 1 (by rfl) ⟨1710566, by rfl⟩ : syracuseStep 2280755 = 3421133) B3421133
theorem B6082013 : Blo 2249435 6082013 := bstep (se 3 (by rfl) ⟨1140377, by rfl⟩ : syracuseStep 6082013 = 2280755) B2280755
theorem B16218701 : Blo 2249435 16218701 := bstep (se 3 (by rfl) ⟨3041006, by rfl⟩ : syracuseStep 16218701 = 6082013) B6082013
theorem B10812467 : Blo 2249435 10812467 := bstep (se 1 (by rfl) ⟨8109350, by rfl⟩ : syracuseStep 10812467 = 16218701) B16218701
theorem B7208311 : Blo 2249435 7208311 := bstep (se 1 (by rfl) ⟨5406233, by rfl⟩ : syracuseStep 7208311 = 10812467) B10812467
theorem B9611081 : Blo 2249435 9611081 := bstep (se 2 (by rfl) ⟨3604155, by rfl⟩ : syracuseStep 9611081 = 7208311) B7208311
theorem B6407387 : Blo 2249435 6407387 := bstep (se 1 (by rfl) ⟨4805540, by rfl⟩ : syracuseStep 6407387 = 9611081) B9611081
theorem B4271591 : Blo 2249435 4271591 := bstep (se 1 (by rfl) ⟨3203693, by rfl⟩ : syracuseStep 4271591 = 6407387) B6407387
theorem B2847727 : Blo 2249435 2847727 := bstep (se 1 (by rfl) ⟨2135795, by rfl⟩ : syracuseStep 2847727 = 4271591) B4271591
theorem B3796969 : Blo 2249435 3796969 := bstep (se 2 (by rfl) ⟨1423863, by rfl⟩ : syracuseStep 3796969 = 2847727) B2847727
theorem B5062625 : Blo 2249435 5062625 := bstep (se 2 (by rfl) ⟨1898484, by rfl⟩ : syracuseStep 5062625 = 3796969) B3796969
theorem B3375083 : Blo 2249435 3375083 := bstep (se 1 (by rfl) ⟨2531312, by rfl⟩ : syracuseStep 3375083 = 5062625) B5062625
theorem B2250055 : Blo 2249435 2250055 := bstep (se 1 (by rfl) ⟨1687541, by rfl⟩ : syracuseStep 2250055 = 3375083) B3375083
theorem B2531317 : Blo 2249435 2531317 := bbase (se 5 (by rfl) ⟨118655, by rfl⟩ : syracuseStep 2531317 = 237311) (by norm_num)
theorem B3375089 : Blo 2249435 3375089 := bstep (se 2 (by rfl) ⟨1265658, by rfl⟩ : syracuseStep 3375089 = 2531317) B2531317
theorem B2250059 : Blo 2249435 2250059 := bstep (se 1 (by rfl) ⟨1687544, by rfl⟩ : syracuseStep 2250059 = 3375089) B3375089
theorem B2847737 : Blo 2249435 2847737 := bbase (se 2 (by rfl) ⟨1067901, by rfl⟩ : syracuseStep 2847737 = 2135803) (by norm_num)
theorem B7593965 : Blo 2249435 7593965 := bstep (se 3 (by rfl) ⟨1423868, by rfl⟩ : syracuseStep 7593965 = 2847737) B2847737
theorem B5062643 : Blo 2249435 5062643 := bstep (se 1 (by rfl) ⟨3796982, by rfl⟩ : syracuseStep 5062643 = 7593965) B7593965
theorem B3375095 : Blo 2249435 3375095 := bstep (se 1 (by rfl) ⟨2531321, by rfl⟩ : syracuseStep 3375095 = 5062643) B5062643
theorem B2250063 : Blo 2249435 2250063 := bstep (se 1 (by rfl) ⟨1687547, by rfl⟩ : syracuseStep 2250063 = 3375095) B3375095
theorem B3375101 : Blo 2249435 3375101 := bbase (se 3 (by rfl) ⟨632831, by rfl⟩ : syracuseStep 3375101 = 1265663) (by norm_num)
theorem B2250067 : Blo 2249435 2250067 := bstep (se 1 (by rfl) ⟨1687550, by rfl⟩ : syracuseStep 2250067 = 3375101) B3375101
theorem B5062661 : Blo 2249435 5062661 := bbase (se 4 (by rfl) ⟨474624, by rfl⟩ : syracuseStep 5062661 = 949249) (by norm_num)
theorem B3375107 : Blo 2249435 3375107 := bstep (se 1 (by rfl) ⟨2531330, by rfl⟩ : syracuseStep 3375107 = 5062661) B5062661
theorem B2250071 : Blo 2249435 2250071 := bstep (se 1 (by rfl) ⟨1687553, by rfl⟩ : syracuseStep 2250071 = 3375107) B3375107
theorem B4271629 : Blo 2249435 4271629 := bbase (se 3 (by rfl) ⟨800930, by rfl⟩ : syracuseStep 4271629 = 1601861) (by norm_num)
theorem B5695505 : Blo 2249435 5695505 := bstep (se 2 (by rfl) ⟨2135814, by rfl⟩ : syracuseStep 5695505 = 4271629) B4271629
theorem B3797003 : Blo 2249435 3797003 := bstep (se 1 (by rfl) ⟨2847752, by rfl⟩ : syracuseStep 3797003 = 5695505) B5695505
theorem B2531335 : Blo 2249435 2531335 := bstep (se 1 (by rfl) ⟨1898501, by rfl⟩ : syracuseStep 2531335 = 3797003) B3797003
theorem B3375113 : Blo 2249435 3375113 := bstep (se 2 (by rfl) ⟨1265667, by rfl⟩ : syracuseStep 3375113 = 2531335) B2531335
theorem B2250075 : Blo 2249435 2250075 := bstep (se 1 (by rfl) ⟨1687556, by rfl⟩ : syracuseStep 2250075 = 3375113) B3375113
theorem B11391029 : Blo 2249435 11391029 := bbase (se 5 (by rfl) ⟨533954, by rfl⟩ : syracuseStep 11391029 = 1067909) (by norm_num)
theorem B7594019 : Blo 2249435 7594019 := bstep (se 1 (by rfl) ⟨5695514, by rfl⟩ : syracuseStep 7594019 = 11391029) B11391029
theorem B5062679 : Blo 2249435 5062679 := bstep (se 1 (by rfl) ⟨3797009, by rfl⟩ : syracuseStep 5062679 = 7594019) B7594019
theorem B3375119 : Blo 2249435 3375119 := bstep (se 1 (by rfl) ⟨2531339, by rfl⟩ : syracuseStep 3375119 = 5062679) B5062679
theorem B2250079 : Blo 2249435 2250079 := bstep (se 1 (by rfl) ⟨1687559, by rfl⟩ : syracuseStep 2250079 = 3375119) B3375119
theorem B3375125 : Blo 2249435 3375125 := bbase (se 6 (by rfl) ⟨79104, by rfl⟩ : syracuseStep 3375125 = 158209) (by norm_num)
theorem B2250083 : Blo 2249435 2250083 := bstep (se 1 (by rfl) ⟨1687562, by rfl⟩ : syracuseStep 2250083 = 3375125) B3375125
theorem B3421181 : Blo 2249435 3421181 := bbase (se 3 (by rfl) ⟨641471, by rfl⟩ : syracuseStep 3421181 = 1282943) (by norm_num)
theorem B2280787 : Blo 2249435 2280787 := bstep (se 1 (by rfl) ⟨1710590, by rfl⟩ : syracuseStep 2280787 = 3421181) B3421181
theorem B12164197 : Blo 2249435 12164197 := bstep (se 4 (by rfl) ⟨1140393, by rfl⟩ : syracuseStep 12164197 = 2280787) B2280787
theorem B16218929 : Blo 2249435 16218929 := bstep (se 2 (by rfl) ⟨6082098, by rfl⟩ : syracuseStep 16218929 = 12164197) B12164197
theorem B10812619 : Blo 2249435 10812619 := bstep (se 1 (by rfl) ⟨8109464, by rfl⟩ : syracuseStep 10812619 = 16218929) B16218929
theorem B14416825 : Blo 2249435 14416825 := bstep (se 2 (by rfl) ⟨5406309, by rfl⟩ : syracuseStep 14416825 = 10812619) B10812619
theorem B19222433 : Blo 2249435 19222433 := bstep (se 2 (by rfl) ⟨7208412, by rfl⟩ : syracuseStep 19222433 = 14416825) B14416825
theorem B12814955 : Blo 2249435 12814955 := bstep (se 1 (by rfl) ⟨9611216, by rfl⟩ : syracuseStep 12814955 = 19222433) B19222433
theorem B8543303 : Blo 2249435 8543303 := bstep (se 1 (by rfl) ⟨6407477, by rfl⟩ : syracuseStep 8543303 = 12814955) B12814955
theorem B5695535 : Blo 2249435 5695535 := bstep (se 1 (by rfl) ⟨4271651, by rfl⟩ : syracuseStep 5695535 = 8543303) B8543303
theorem B3797023 : Blo 2249435 3797023 := bstep (se 1 (by rfl) ⟨2847767, by rfl⟩ : syracuseStep 3797023 = 5695535) B5695535
theorem B5062697 : Blo 2249435 5062697 := bstep (se 2 (by rfl) ⟨1898511, by rfl⟩ : syracuseStep 5062697 = 3797023) B3797023
theorem B3375131 : Blo 2249435 3375131 := bstep (se 1 (by rfl) ⟨2531348, by rfl⟩ : syracuseStep 3375131 = 5062697) B5062697
theorem B2250087 : Blo 2249435 2250087 := bstep (se 1 (by rfl) ⟨1687565, by rfl⟩ : syracuseStep 2250087 = 3375131) B3375131
theorem B2531353 : Blo 2249435 2531353 := bbase (se 2 (by rfl) ⟨949257, by rfl⟩ : syracuseStep 2531353 = 1898515) (by norm_num)
theorem B3375137 : Blo 2249435 3375137 := bstep (se 2 (by rfl) ⟨1265676, by rfl⟩ : syracuseStep 3375137 = 2531353) B2531353
theorem B2250091 : Blo 2249435 2250091 := bstep (se 1 (by rfl) ⟨1687568, by rfl⟩ : syracuseStep 2250091 = 3375137) B3375137
theorem B8543333 : Blo 2249435 8543333 := bbase (se 4 (by rfl) ⟨800937, by rfl⟩ : syracuseStep 8543333 = 1601875) (by norm_num)
theorem B5695555 : Blo 2249435 5695555 := bstep (se 1 (by rfl) ⟨4271666, by rfl⟩ : syracuseStep 5695555 = 8543333) B8543333
theorem B7594073 : Blo 2249435 7594073 := bstep (se 2 (by rfl) ⟨2847777, by rfl⟩ : syracuseStep 7594073 = 5695555) B5695555
theorem B5062715 : Blo 2249435 5062715 := bstep (se 1 (by rfl) ⟨3797036, by rfl⟩ : syracuseStep 5062715 = 7594073) B7594073
theorem B3375143 : Blo 2249435 3375143 := bstep (se 1 (by rfl) ⟨2531357, by rfl⟩ : syracuseStep 3375143 = 5062715) B5062715
theorem B2250095 : Blo 2249435 2250095 := bstep (se 1 (by rfl) ⟨1687571, by rfl⟩ : syracuseStep 2250095 = 3375143) B3375143
theorem B3375149 : Blo 2249435 3375149 := bbase (se 3 (by rfl) ⟨632840, by rfl⟩ : syracuseStep 3375149 = 1265681) (by norm_num)
theorem B2250099 : Blo 2249435 2250099 := bstep (se 1 (by rfl) ⟨1687574, by rfl⟩ : syracuseStep 2250099 = 3375149) B3375149
theorem B5062733 : Blo 2249435 5062733 := bbase (se 3 (by rfl) ⟨949262, by rfl⟩ : syracuseStep 5062733 = 1898525) (by norm_num)
theorem B3375155 : Blo 2249435 3375155 := bstep (se 1 (by rfl) ⟨2531366, by rfl⟩ : syracuseStep 3375155 = 5062733) B5062733
theorem B2250103 : Blo 2249435 2250103 := bstep (se 1 (by rfl) ⟨1687577, by rfl⟩ : syracuseStep 2250103 = 3375155) B3375155
theorem B2847793 : Blo 2249435 2847793 := bbase (se 2 (by rfl) ⟨1067922, by rfl⟩ : syracuseStep 2847793 = 2135845) (by norm_num)
theorem B3797057 : Blo 2249435 3797057 := bstep (se 2 (by rfl) ⟨1423896, by rfl⟩ : syracuseStep 3797057 = 2847793) B2847793
theorem B2531371 : Blo 2249435 2531371 := bstep (se 1 (by rfl) ⟨1898528, by rfl⟩ : syracuseStep 2531371 = 3797057) B3797057
theorem B3375161 : Blo 2249435 3375161 := bstep (se 2 (by rfl) ⟨1265685, by rfl⟩ : syracuseStep 3375161 = 2531371) B2531371
theorem B2250107 : Blo 2249435 2250107 := bstep (se 1 (by rfl) ⟨1687580, by rfl⟩ : syracuseStep 2250107 = 3375161) B3375161
theorem B3082573 : Blo 2249435 3082573 := bbase (se 3 (by rfl) ⟨577982, by rfl⟩ : syracuseStep 3082573 = 1155965) (by norm_num)
theorem B4110097 : Blo 2249435 4110097 := bstep (se 2 (by rfl) ⟨1541286, by rfl⟩ : syracuseStep 4110097 = 3082573) B3082573
theorem B5480129 : Blo 2249435 5480129 := bstep (se 2 (by rfl) ⟨2055048, by rfl⟩ : syracuseStep 5480129 = 4110097) B4110097
theorem B14613677 : Blo 2249435 14613677 := bstep (se 3 (by rfl) ⟨2740064, by rfl⟩ : syracuseStep 14613677 = 5480129) B5480129
theorem B9742451 : Blo 2249435 9742451 := bstep (se 1 (by rfl) ⟨7306838, by rfl⟩ : syracuseStep 9742451 = 14613677) B14613677
theorem B25979869 : Blo 2249435 25979869 := bstep (se 3 (by rfl) ⟨4871225, by rfl⟩ : syracuseStep 25979869 = 9742451) B9742451
theorem B34639825 : Blo 2249435 34639825 := bstep (se 2 (by rfl) ⟨12989934, by rfl⟩ : syracuseStep 34639825 = 25979869) B25979869
theorem B46186433 : Blo 2249435 46186433 := bstep (se 2 (by rfl) ⟨17319912, by rfl⟩ : syracuseStep 46186433 = 34639825) B34639825
theorem B30790955 : Blo 2249435 30790955 := bstep (se 1 (by rfl) ⟨23093216, by rfl⟩ : syracuseStep 30790955 = 46186433) B46186433
theorem B20527303 : Blo 2249435 20527303 := bstep (se 1 (by rfl) ⟨15395477, by rfl⟩ : syracuseStep 20527303 = 30790955) B30790955
theorem B27369737 : Blo 2249435 27369737 := bstep (se 2 (by rfl) ⟨10263651, by rfl⟩ : syracuseStep 27369737 = 20527303) B20527303
theorem B18246491 : Blo 2249435 18246491 := bstep (se 1 (by rfl) ⟨13684868, by rfl⟩ : syracuseStep 18246491 = 27369737) B27369737
theorem B12164327 : Blo 2249435 12164327 := bstep (se 1 (by rfl) ⟨9123245, by rfl⟩ : syracuseStep 12164327 = 18246491) B18246491
theorem B8109551 : Blo 2249435 8109551 := bstep (se 1 (by rfl) ⟨6082163, by rfl⟩ : syracuseStep 8109551 = 12164327) B12164327
theorem B5406367 : Blo 2249435 5406367 := bstep (se 1 (by rfl) ⟨4054775, by rfl⟩ : syracuseStep 5406367 = 8109551) B8109551
theorem B7208489 : Blo 2249435 7208489 := bstep (se 2 (by rfl) ⟨2703183, by rfl⟩ : syracuseStep 7208489 = 5406367) B5406367
theorem B4805659 : Blo 2249435 4805659 := bstep (se 1 (by rfl) ⟨3604244, by rfl⟩ : syracuseStep 4805659 = 7208489) B7208489
theorem B25630181 : Blo 2249435 25630181 := bstep (se 4 (by rfl) ⟨2402829, by rfl⟩ : syracuseStep 25630181 = 4805659) B4805659
theorem B17086787 : Blo 2249435 17086787 := bstep (se 1 (by rfl) ⟨12815090, by rfl⟩ : syracuseStep 17086787 = 25630181) B25630181
theorem B11391191 : Blo 2249435 11391191 := bstep (se 1 (by rfl) ⟨8543393, by rfl⟩ : syracuseStep 11391191 = 17086787) B17086787
theorem B7594127 : Blo 2249435 7594127 := bstep (se 1 (by rfl) ⟨5695595, by rfl⟩ : syracuseStep 7594127 = 11391191) B11391191
theorem B5062751 : Blo 2249435 5062751 := bstep (se 1 (by rfl) ⟨3797063, by rfl⟩ : syracuseStep 5062751 = 7594127) B7594127
theorem B3375167 : Blo 2249435 3375167 := bstep (se 1 (by rfl) ⟨2531375, by rfl⟩ : syracuseStep 3375167 = 5062751) B5062751
theorem B2250111 : Blo 2249435 2250111 := bstep (se 1 (by rfl) ⟨1687583, by rfl⟩ : syracuseStep 2250111 = 3375167) B3375167
theorem B3375173 : Blo 2249435 3375173 := bbase (se 4 (by rfl) ⟨316422, by rfl⟩ : syracuseStep 3375173 = 632845) (by norm_num)
theorem B2250115 : Blo 2249435 2250115 := bstep (se 1 (by rfl) ⟨1687586, by rfl⟩ : syracuseStep 2250115 = 3375173) B3375173
theorem B3797077 : Blo 2249435 3797077 := bbase (se 8 (by rfl) ⟨22248, by rfl⟩ : syracuseStep 3797077 = 44497) (by norm_num)
theorem B5062769 : Blo 2249435 5062769 := bstep (se 2 (by rfl) ⟨1898538, by rfl⟩ : syracuseStep 5062769 = 3797077) B3797077
theorem B3375179 : Blo 2249435 3375179 := bstep (se 1 (by rfl) ⟨2531384, by rfl⟩ : syracuseStep 3375179 = 5062769) B5062769
theorem B2250119 : Blo 2249435 2250119 := bstep (se 1 (by rfl) ⟨1687589, by rfl⟩ : syracuseStep 2250119 = 3375179) B3375179
theorem B2531389 : Blo 2249435 2531389 := bbase (se 3 (by rfl) ⟨474635, by rfl⟩ : syracuseStep 2531389 = 949271) (by norm_num)
theorem B3375185 : Blo 2249435 3375185 := bstep (se 2 (by rfl) ⟨1265694, by rfl⟩ : syracuseStep 3375185 = 2531389) B2531389
theorem B2250123 : Blo 2249435 2250123 := bstep (se 1 (by rfl) ⟨1687592, by rfl⟩ : syracuseStep 2250123 = 3375185) B3375185
theorem B7594181 : Blo 2249435 7594181 := bbase (se 4 (by rfl) ⟨711954, by rfl⟩ : syracuseStep 7594181 = 1423909) (by norm_num)
theorem B5062787 : Blo 2249435 5062787 := bstep (se 1 (by rfl) ⟨3797090, by rfl⟩ : syracuseStep 5062787 = 7594181) B7594181
theorem B3375191 : Blo 2249435 3375191 := bstep (se 1 (by rfl) ⟨2531393, by rfl⟩ : syracuseStep 3375191 = 5062787) B5062787
theorem B2250127 : Blo 2249435 2250127 := bstep (se 1 (by rfl) ⟨1687595, by rfl⟩ : syracuseStep 2250127 = 3375191) B3375191
theorem B3375197 : Blo 2249435 3375197 := bbase (se 3 (by rfl) ⟨632849, by rfl⟩ : syracuseStep 3375197 = 1265699) (by norm_num)
theorem B2250131 : Blo 2249435 2250131 := bstep (se 1 (by rfl) ⟨1687598, by rfl⟩ : syracuseStep 2250131 = 3375197) B3375197
theorem B5062805 : Blo 2249435 5062805 := bbase (se 6 (by rfl) ⟨118659, by rfl⟩ : syracuseStep 5062805 = 237319) (by norm_num)
theorem B3375203 : Blo 2249435 3375203 := bstep (se 1 (by rfl) ⟨2531402, by rfl⟩ : syracuseStep 3375203 = 5062805) B5062805
theorem B2250135 : Blo 2249435 2250135 := bstep (se 1 (by rfl) ⟨1687601, by rfl⟩ : syracuseStep 2250135 = 3375203) B3375203
theorem B3203813 : Blo 2249435 3203813 := bbase (se 4 (by rfl) ⟨300357, by rfl⟩ : syracuseStep 3203813 = 600715) (by norm_num)
theorem B8543501 : Blo 2249435 8543501 := bstep (se 3 (by rfl) ⟨1601906, by rfl⟩ : syracuseStep 8543501 = 3203813) B3203813
theorem B5695667 : Blo 2249435 5695667 := bstep (se 1 (by rfl) ⟨4271750, by rfl⟩ : syracuseStep 5695667 = 8543501) B8543501
theorem B3797111 : Blo 2249435 3797111 := bstep (se 1 (by rfl) ⟨2847833, by rfl⟩ : syracuseStep 3797111 = 5695667) B5695667
theorem B2531407 : Blo 2249435 2531407 := bstep (se 1 (by rfl) ⟨1898555, by rfl⟩ : syracuseStep 2531407 = 3797111) B3797111
theorem B3375209 : Blo 2249435 3375209 := bstep (se 2 (by rfl) ⟨1265703, by rfl⟩ : syracuseStep 3375209 = 2531407) B2531407
theorem B2250139 : Blo 2249435 2250139 := bstep (se 1 (by rfl) ⟨1687604, by rfl⟩ : syracuseStep 2250139 = 3375209) B3375209
theorem B2565949 : Blo 2249435 2565949 := bbase (se 3 (by rfl) ⟨481115, by rfl⟩ : syracuseStep 2565949 = 962231) (by norm_num)
theorem B54740245 : Blo 2249435 54740245 := bstep (se 6 (by rfl) ⟨1282974, by rfl⟩ : syracuseStep 54740245 = 2565949) B2565949
theorem B72986993 : Blo 2249435 72986993 := bstep (se 2 (by rfl) ⟨27370122, by rfl⟩ : syracuseStep 72986993 = 54740245) B54740245
theorem B48657995 : Blo 2249435 48657995 := bstep (se 1 (by rfl) ⟨36493496, by rfl⟩ : syracuseStep 48657995 = 72986993) B72986993
theorem B32438663 : Blo 2249435 32438663 := bstep (se 1 (by rfl) ⟨24328997, by rfl⟩ : syracuseStep 32438663 = 48657995) B48657995
theorem B21625775 : Blo 2249435 21625775 := bstep (se 1 (by rfl) ⟨16219331, by rfl⟩ : syracuseStep 21625775 = 32438663) B32438663
theorem B14417183 : Blo 2249435 14417183 := bstep (se 1 (by rfl) ⟨10812887, by rfl⟩ : syracuseStep 14417183 = 21625775) B21625775
theorem B9611455 : Blo 2249435 9611455 := bstep (se 1 (by rfl) ⟨7208591, by rfl⟩ : syracuseStep 9611455 = 14417183) B14417183
theorem B12815273 : Blo 2249435 12815273 := bstep (se 2 (by rfl) ⟨4805727, by rfl⟩ : syracuseStep 12815273 = 9611455) B9611455
theorem B8543515 : Blo 2249435 8543515 := bstep (se 1 (by rfl) ⟨6407636, by rfl⟩ : syracuseStep 8543515 = 12815273) B12815273
theorem B11391353 : Blo 2249435 11391353 := bstep (se 2 (by rfl) ⟨4271757, by rfl⟩ : syracuseStep 11391353 = 8543515) B8543515
theorem B7594235 : Blo 2249435 7594235 := bstep (se 1 (by rfl) ⟨5695676, by rfl⟩ : syracuseStep 7594235 = 11391353) B11391353
theorem B5062823 : Blo 2249435 5062823 := bstep (se 1 (by rfl) ⟨3797117, by rfl⟩ : syracuseStep 5062823 = 7594235) B7594235
theorem B3375215 : Blo 2249435 3375215 := bstep (se 1 (by rfl) ⟨2531411, by rfl⟩ : syracuseStep 3375215 = 5062823) B5062823
theorem B2250143 : Blo 2249435 2250143 := bstep (se 1 (by rfl) ⟨1687607, by rfl⟩ : syracuseStep 2250143 = 3375215) B3375215
theorem B3375221 : Blo 2249435 3375221 := bbase (se 5 (by rfl) ⟨158213, by rfl⟩ : syracuseStep 3375221 = 316427) (by norm_num)
theorem B2250147 : Blo 2249435 2250147 := bstep (se 1 (by rfl) ⟨1687610, by rfl⟩ : syracuseStep 2250147 = 3375221) B3375221
theorem B4271773 : Blo 2249435 4271773 := bbase (se 3 (by rfl) ⟨800957, by rfl⟩ : syracuseStep 4271773 = 1601915) (by norm_num)
theorem B5695697 : Blo 2249435 5695697 := bstep (se 2 (by rfl) ⟨2135886, by rfl⟩ : syracuseStep 5695697 = 4271773) B4271773
theorem B3797131 : Blo 2249435 3797131 := bstep (se 1 (by rfl) ⟨2847848, by rfl⟩ : syracuseStep 3797131 = 5695697) B5695697
theorem B5062841 : Blo 2249435 5062841 := bstep (se 2 (by rfl) ⟨1898565, by rfl⟩ : syracuseStep 5062841 = 3797131) B3797131
theorem B3375227 : Blo 2249435 3375227 := bstep (se 1 (by rfl) ⟨2531420, by rfl⟩ : syracuseStep 3375227 = 5062841) B5062841
theorem B2250151 : Blo 2249435 2250151 := bstep (se 1 (by rfl) ⟨1687613, by rfl⟩ : syracuseStep 2250151 = 3375227) B3375227
theorem B2531425 : Blo 2249435 2531425 := bbase (se 2 (by rfl) ⟨949284, by rfl⟩ : syracuseStep 2531425 = 1898569) (by norm_num)
theorem B3375233 : Blo 2249435 3375233 := bstep (se 2 (by rfl) ⟨1265712, by rfl⟩ : syracuseStep 3375233 = 2531425) B2531425
theorem B2250155 : Blo 2249435 2250155 := bstep (se 1 (by rfl) ⟨1687616, by rfl⟩ : syracuseStep 2250155 = 3375233) B3375233
theorem B5695717 : Blo 2249435 5695717 := bbase (se 4 (by rfl) ⟨533973, by rfl⟩ : syracuseStep 5695717 = 1067947) (by norm_num)
theorem B7594289 : Blo 2249435 7594289 := bstep (se 2 (by rfl) ⟨2847858, by rfl⟩ : syracuseStep 7594289 = 5695717) B5695717
theorem B5062859 : Blo 2249435 5062859 := bstep (se 1 (by rfl) ⟨3797144, by rfl⟩ : syracuseStep 5062859 = 7594289) B7594289
theorem B3375239 : Blo 2249435 3375239 := bstep (se 1 (by rfl) ⟨2531429, by rfl⟩ : syracuseStep 3375239 = 5062859) B5062859
theorem B2250159 : Blo 2249435 2250159 := bstep (se 1 (by rfl) ⟨1687619, by rfl⟩ : syracuseStep 2250159 = 3375239) B3375239
theorem B3375245 : Blo 2249435 3375245 := bbase (se 3 (by rfl) ⟨632858, by rfl⟩ : syracuseStep 3375245 = 1265717) (by norm_num)
theorem B2250163 : Blo 2249435 2250163 := bstep (se 1 (by rfl) ⟨1687622, by rfl⟩ : syracuseStep 2250163 = 3375245) B3375245
theorem B5062877 : Blo 2249435 5062877 := bbase (se 3 (by rfl) ⟨949289, by rfl⟩ : syracuseStep 5062877 = 1898579) (by norm_num)
theorem B3375251 : Blo 2249435 3375251 := bstep (se 1 (by rfl) ⟨2531438, by rfl⟩ : syracuseStep 3375251 = 5062877) B5062877
theorem B2250167 : Blo 2249435 2250167 := bstep (se 1 (by rfl) ⟨1687625, by rfl⟩ : syracuseStep 2250167 = 3375251) B3375251
theorem B3797165 : Blo 2249435 3797165 := bbase (se 3 (by rfl) ⟨711968, by rfl⟩ : syracuseStep 3797165 = 1423937) (by norm_num)
theorem B2531443 : Blo 2249435 2531443 := bstep (se 1 (by rfl) ⟨1898582, by rfl⟩ : syracuseStep 2531443 = 3797165) B3797165
theorem B3375257 : Blo 2249435 3375257 := bstep (se 2 (by rfl) ⟨1265721, by rfl⟩ : syracuseStep 3375257 = 2531443) B2531443
theorem B2250171 : Blo 2249435 2250171 := bstep (se 1 (by rfl) ⟨1687628, by rfl⟩ : syracuseStep 2250171 = 3375257) B3375257
theorem B16440853 : Blo 2249435 16440853 := bbase (se 6 (by rfl) ⟨385332, by rfl⟩ : syracuseStep 16440853 = 770665) (by norm_num)
theorem B21921137 : Blo 2249435 21921137 := bstep (se 2 (by rfl) ⟨8220426, by rfl⟩ : syracuseStep 21921137 = 16440853) B16440853
theorem B14614091 : Blo 2249435 14614091 := bstep (se 1 (by rfl) ⟨10960568, by rfl⟩ : syracuseStep 14614091 = 21921137) B21921137
theorem B9742727 : Blo 2249435 9742727 := bstep (se 1 (by rfl) ⟨7307045, by rfl⟩ : syracuseStep 9742727 = 14614091) B14614091
theorem B6495151 : Blo 2249435 6495151 := bstep (se 1 (by rfl) ⟨4871363, by rfl⟩ : syracuseStep 6495151 = 9742727) B9742727
theorem B8660201 : Blo 2249435 8660201 := bstep (se 2 (by rfl) ⟨3247575, by rfl⟩ : syracuseStep 8660201 = 6495151) B6495151
theorem B92375477 : Blo 2249435 92375477 := bstep (se 5 (by rfl) ⟨4330100, by rfl⟩ : syracuseStep 92375477 = 8660201) B8660201
theorem B61583651 : Blo 2249435 61583651 := bstep (se 1 (by rfl) ⟨46187738, by rfl⟩ : syracuseStep 61583651 = 92375477) B92375477
theorem B41055767 : Blo 2249435 41055767 := bstep (se 1 (by rfl) ⟨30791825, by rfl⟩ : syracuseStep 41055767 = 61583651) B61583651
theorem B27370511 : Blo 2249435 27370511 := bstep (se 1 (by rfl) ⟨20527883, by rfl⟩ : syracuseStep 27370511 = 41055767) B41055767
theorem B18247007 : Blo 2249435 18247007 := bstep (se 1 (by rfl) ⟨13685255, by rfl⟩ : syracuseStep 18247007 = 27370511) B27370511
theorem B12164671 : Blo 2249435 12164671 := bstep (se 1 (by rfl) ⟨9123503, by rfl⟩ : syracuseStep 12164671 = 18247007) B18247007
theorem B64878245 : Blo 2249435 64878245 := bstep (se 4 (by rfl) ⟨6082335, by rfl⟩ : syracuseStep 64878245 = 12164671) B12164671
theorem B43252163 : Blo 2249435 43252163 := bstep (se 1 (by rfl) ⟨32439122, by rfl⟩ : syracuseStep 43252163 = 64878245) B64878245
theorem B28834775 : Blo 2249435 28834775 := bstep (se 1 (by rfl) ⟨21626081, by rfl⟩ : syracuseStep 28834775 = 43252163) B43252163
theorem B19223183 : Blo 2249435 19223183 := bstep (se 1 (by rfl) ⟨14417387, by rfl⟩ : syracuseStep 19223183 = 28834775) B28834775
theorem B12815455 : Blo 2249435 12815455 := bstep (se 1 (by rfl) ⟨9611591, by rfl⟩ : syracuseStep 12815455 = 19223183) B19223183
theorem B17087273 : Blo 2249435 17087273 := bstep (se 2 (by rfl) ⟨6407727, by rfl⟩ : syracuseStep 17087273 = 12815455) B12815455
theorem B11391515 : Blo 2249435 11391515 := bstep (se 1 (by rfl) ⟨8543636, by rfl⟩ : syracuseStep 11391515 = 17087273) B17087273
theorem B7594343 : Blo 2249435 7594343 := bstep (se 1 (by rfl) ⟨5695757, by rfl⟩ : syracuseStep 7594343 = 11391515) B11391515
theorem B5062895 : Blo 2249435 5062895 := bstep (se 1 (by rfl) ⟨3797171, by rfl⟩ : syracuseStep 5062895 = 7594343) B7594343
theorem B3375263 : Blo 2249435 3375263 := bstep (se 1 (by rfl) ⟨2531447, by rfl⟩ : syracuseStep 3375263 = 5062895) B5062895
theorem B2250175 : Blo 2249435 2250175 := bstep (se 1 (by rfl) ⟨1687631, by rfl⟩ : syracuseStep 2250175 = 3375263) B3375263
theorem B3375269 : Blo 2249435 3375269 := bbase (se 4 (by rfl) ⟨316431, by rfl⟩ : syracuseStep 3375269 = 632863) (by norm_num)
theorem B2250179 : Blo 2249435 2250179 := bstep (se 1 (by rfl) ⟨1687634, by rfl⟩ : syracuseStep 2250179 = 3375269) B3375269
theorem B2847889 : Blo 2249435 2847889 := bbase (se 2 (by rfl) ⟨1067958, by rfl⟩ : syracuseStep 2847889 = 2135917) (by norm_num)
theorem B3797185 : Blo 2249435 3797185 := bstep (se 2 (by rfl) ⟨1423944, by rfl⟩ : syracuseStep 3797185 = 2847889) B2847889
theorem B5062913 : Blo 2249435 5062913 := bstep (se 2 (by rfl) ⟨1898592, by rfl⟩ : syracuseStep 5062913 = 3797185) B3797185
theorem B3375275 : Blo 2249435 3375275 := bstep (se 1 (by rfl) ⟨2531456, by rfl⟩ : syracuseStep 3375275 = 5062913) B5062913
theorem B2250183 : Blo 2249435 2250183 := bstep (se 1 (by rfl) ⟨1687637, by rfl⟩ : syracuseStep 2250183 = 3375275) B3375275
theorem B2531461 : Blo 2249435 2531461 := bbase (se 4 (by rfl) ⟨237324, by rfl⟩ : syracuseStep 2531461 = 474649) (by norm_num)
theorem B3375281 : Blo 2249435 3375281 := bstep (se 2 (by rfl) ⟨1265730, by rfl⟩ : syracuseStep 3375281 = 2531461) B2531461
theorem B2250187 : Blo 2249435 2250187 := bstep (se 1 (by rfl) ⟨1687640, by rfl⟩ : syracuseStep 2250187 = 3375281) B3375281
theorem B2280893 : Blo 2249435 2280893 := bbase (se 3 (by rfl) ⟨427667, by rfl⟩ : syracuseStep 2280893 = 855335) (by norm_num)
theorem B6082381 : Blo 2249435 6082381 := bstep (se 3 (by rfl) ⟨1140446, by rfl⟩ : syracuseStep 6082381 = 2280893) B2280893
theorem B8109841 : Blo 2249435 8109841 := bstep (se 2 (by rfl) ⟨3041190, by rfl⟩ : syracuseStep 8109841 = 6082381) B6082381
theorem B10813121 : Blo 2249435 10813121 := bstep (se 2 (by rfl) ⟨4054920, by rfl⟩ : syracuseStep 10813121 = 8109841) B8109841
theorem B7208747 : Blo 2249435 7208747 := bstep (se 1 (by rfl) ⟨5406560, by rfl⟩ : syracuseStep 7208747 = 10813121) B10813121
theorem B4805831 : Blo 2249435 4805831 := bstep (se 1 (by rfl) ⟨3604373, by rfl⟩ : syracuseStep 4805831 = 7208747) B7208747
theorem B3203887 : Blo 2249435 3203887 := bstep (se 1 (by rfl) ⟨2402915, by rfl⟩ : syracuseStep 3203887 = 4805831) B4805831
theorem B4271849 : Blo 2249435 4271849 := bstep (se 2 (by rfl) ⟨1601943, by rfl⟩ : syracuseStep 4271849 = 3203887) B3203887
theorem B2847899 : Blo 2249435 2847899 := bstep (se 1 (by rfl) ⟨2135924, by rfl⟩ : syracuseStep 2847899 = 4271849) B4271849
theorem B7594397 : Blo 2249435 7594397 := bstep (se 3 (by rfl) ⟨1423949, by rfl⟩ : syracuseStep 7594397 = 2847899) B2847899
theorem B5062931 : Blo 2249435 5062931 := bstep (se 1 (by rfl) ⟨3797198, by rfl⟩ : syracuseStep 5062931 = 7594397) B7594397
theorem B3375287 : Blo 2249435 3375287 := bstep (se 1 (by rfl) ⟨2531465, by rfl⟩ : syracuseStep 3375287 = 5062931) B5062931
theorem B2250191 : Blo 2249435 2250191 := bstep (se 1 (by rfl) ⟨1687643, by rfl⟩ : syracuseStep 2250191 = 3375287) B3375287
theorem B3375293 : Blo 2249435 3375293 := bbase (se 3 (by rfl) ⟨632867, by rfl⟩ : syracuseStep 3375293 = 1265735) (by norm_num)
theorem B2250195 : Blo 2249435 2250195 := bstep (se 1 (by rfl) ⟨1687646, by rfl⟩ : syracuseStep 2250195 = 3375293) B3375293
theorem B5062949 : Blo 2249435 5062949 := bbase (se 4 (by rfl) ⟨474651, by rfl⟩ : syracuseStep 5062949 = 949303) (by norm_num)
theorem B3375299 : Blo 2249435 3375299 := bstep (se 1 (by rfl) ⟨2531474, by rfl⟩ : syracuseStep 3375299 = 5062949) B5062949
theorem B2250199 : Blo 2249435 2250199 := bstep (se 1 (by rfl) ⟨1687649, by rfl⟩ : syracuseStep 2250199 = 3375299) B3375299
theorem B5695829 : Blo 2249435 5695829 := bbase (se 10 (by rfl) ⟨8343, by rfl⟩ : syracuseStep 5695829 = 16687) (by norm_num)
theorem B3797219 : Blo 2249435 3797219 := bstep (se 1 (by rfl) ⟨2847914, by rfl⟩ : syracuseStep 3797219 = 5695829) B5695829
theorem B2531479 : Blo 2249435 2531479 := bstep (se 1 (by rfl) ⟨1898609, by rfl⟩ : syracuseStep 2531479 = 3797219) B3797219
theorem B3375305 : Blo 2249435 3375305 := bstep (se 2 (by rfl) ⟨1265739, by rfl⟩ : syracuseStep 3375305 = 2531479) B2531479
theorem B2250203 : Blo 2249435 2250203 := bstep (se 1 (by rfl) ⟨1687652, by rfl⟩ : syracuseStep 2250203 = 3375305) B3375305
theorem B4054949 : Blo 2249435 4054949 := bbase (se 4 (by rfl) ⟨380151, by rfl⟩ : syracuseStep 4054949 = 760303) (by norm_num)
theorem B2703299 : Blo 2249435 2703299 := bstep (se 1 (by rfl) ⟨2027474, by rfl⟩ : syracuseStep 2703299 = 4054949) B4054949
theorem B7208797 : Blo 2249435 7208797 := bstep (se 3 (by rfl) ⟨1351649, by rfl⟩ : syracuseStep 7208797 = 2703299) B2703299
theorem B9611729 : Blo 2249435 9611729 := bstep (se 2 (by rfl) ⟨3604398, by rfl⟩ : syracuseStep 9611729 = 7208797) B7208797
theorem B6407819 : Blo 2249435 6407819 := bstep (se 1 (by rfl) ⟨4805864, by rfl⟩ : syracuseStep 6407819 = 9611729) B9611729
theorem B4271879 : Blo 2249435 4271879 := bstep (se 1 (by rfl) ⟨3203909, by rfl⟩ : syracuseStep 4271879 = 6407819) B6407819
theorem B11391677 : Blo 2249435 11391677 := bstep (se 3 (by rfl) ⟨2135939, by rfl⟩ : syracuseStep 11391677 = 4271879) B4271879
theorem B7594451 : Blo 2249435 7594451 := bstep (se 1 (by rfl) ⟨5695838, by rfl⟩ : syracuseStep 7594451 = 11391677) B11391677
theorem B5062967 : Blo 2249435 5062967 := bstep (se 1 (by rfl) ⟨3797225, by rfl⟩ : syracuseStep 5062967 = 7594451) B7594451
theorem B3375311 : Blo 2249435 3375311 := bstep (se 1 (by rfl) ⟨2531483, by rfl⟩ : syracuseStep 3375311 = 5062967) B5062967
theorem B2250207 : Blo 2249435 2250207 := bstep (se 1 (by rfl) ⟨1687655, by rfl⟩ : syracuseStep 2250207 = 3375311) B3375311
theorem B3375317 : Blo 2249435 3375317 := bbase (se 7 (by rfl) ⟨39554, by rfl⟩ : syracuseStep 3375317 = 79109) (by norm_num)
theorem B2250211 : Blo 2249435 2250211 := bstep (se 1 (by rfl) ⟨1687658, by rfl⟩ : syracuseStep 2250211 = 3375317) B3375317
theorem B2402941 : Blo 2249435 2402941 := bbase (se 3 (by rfl) ⟨450551, by rfl⟩ : syracuseStep 2402941 = 901103) (by norm_num)
theorem B3203921 : Blo 2249435 3203921 := bstep (se 2 (by rfl) ⟨1201470, by rfl⟩ : syracuseStep 3203921 = 2402941) B2402941
theorem B8543789 : Blo 2249435 8543789 := bstep (se 3 (by rfl) ⟨1601960, by rfl⟩ : syracuseStep 8543789 = 3203921) B3203921
theorem B5695859 : Blo 2249435 5695859 := bstep (se 1 (by rfl) ⟨4271894, by rfl⟩ : syracuseStep 5695859 = 8543789) B8543789
theorem B3797239 : Blo 2249435 3797239 := bstep (se 1 (by rfl) ⟨2847929, by rfl⟩ : syracuseStep 3797239 = 5695859) B5695859
theorem B5062985 : Blo 2249435 5062985 := bstep (se 2 (by rfl) ⟨1898619, by rfl⟩ : syracuseStep 5062985 = 3797239) B3797239
theorem B3375323 : Blo 2249435 3375323 := bstep (se 1 (by rfl) ⟨2531492, by rfl⟩ : syracuseStep 3375323 = 5062985) B5062985
theorem B2250215 : Blo 2249435 2250215 := bstep (se 1 (by rfl) ⟨1687661, by rfl⟩ : syracuseStep 2250215 = 3375323) B3375323
theorem B2531497 : Blo 2249435 2531497 := bbase (se 2 (by rfl) ⟨949311, by rfl⟩ : syracuseStep 2531497 = 1898623) (by norm_num)
theorem B3375329 : Blo 2249435 3375329 := bstep (se 2 (by rfl) ⟨1265748, by rfl⟩ : syracuseStep 3375329 = 2531497) B2531497
theorem B2250219 : Blo 2249435 2250219 := bstep (se 1 (by rfl) ⟨1687664, by rfl⟩ : syracuseStep 2250219 = 3375329) B3375329
theorem B9611797 : Blo 2249435 9611797 := bbase (se 6 (by rfl) ⟨225276, by rfl⟩ : syracuseStep 9611797 = 450553) (by norm_num)
theorem B12815729 : Blo 2249435 12815729 := bstep (se 2 (by rfl) ⟨4805898, by rfl⟩ : syracuseStep 12815729 = 9611797) B9611797
theorem B8543819 : Blo 2249435 8543819 := bstep (se 1 (by rfl) ⟨6407864, by rfl⟩ : syracuseStep 8543819 = 12815729) B12815729
theorem B5695879 : Blo 2249435 5695879 := bstep (se 1 (by rfl) ⟨4271909, by rfl⟩ : syracuseStep 5695879 = 8543819) B8543819
theorem B7594505 : Blo 2249435 7594505 := bstep (se 2 (by rfl) ⟨2847939, by rfl⟩ : syracuseStep 7594505 = 5695879) B5695879
theorem B5063003 : Blo 2249435 5063003 := bstep (se 1 (by rfl) ⟨3797252, by rfl⟩ : syracuseStep 5063003 = 7594505) B7594505
theorem B3375335 : Blo 2249435 3375335 := bstep (se 1 (by rfl) ⟨2531501, by rfl⟩ : syracuseStep 3375335 = 5063003) B5063003
theorem B2250223 : Blo 2249435 2250223 := bstep (se 1 (by rfl) ⟨1687667, by rfl⟩ : syracuseStep 2250223 = 3375335) B3375335
theorem B3375341 : Blo 2249435 3375341 := bbase (se 3 (by rfl) ⟨632876, by rfl⟩ : syracuseStep 3375341 = 1265753) (by norm_num)
theorem B2250227 : Blo 2249435 2250227 := bstep (se 1 (by rfl) ⟨1687670, by rfl⟩ : syracuseStep 2250227 = 3375341) B3375341
theorem B5063021 : Blo 2249435 5063021 := bbase (se 3 (by rfl) ⟨949316, by rfl⟩ : syracuseStep 5063021 = 1898633) (by norm_num)
theorem B3375347 : Blo 2249435 3375347 := bstep (se 1 (by rfl) ⟨2531510, by rfl⟩ : syracuseStep 3375347 = 5063021) B5063021
theorem B2250231 : Blo 2249435 2250231 := bstep (se 1 (by rfl) ⟨1687673, by rfl⟩ : syracuseStep 2250231 = 3375347) B3375347
theorem B4271933 : Blo 2249435 4271933 := bbase (se 3 (by rfl) ⟨800987, by rfl⟩ : syracuseStep 4271933 = 1601975) (by norm_num)
theorem B2847955 : Blo 2249435 2847955 := bstep (se 1 (by rfl) ⟨2135966, by rfl⟩ : syracuseStep 2847955 = 4271933) B4271933
theorem B3797273 : Blo 2249435 3797273 := bstep (se 2 (by rfl) ⟨1423977, by rfl⟩ : syracuseStep 3797273 = 2847955) B2847955
theorem B2531515 : Blo 2249435 2531515 := bstep (se 1 (by rfl) ⟨1898636, by rfl⟩ : syracuseStep 2531515 = 3797273) B3797273
theorem B3375353 : Blo 2249435 3375353 := bstep (se 2 (by rfl) ⟨1265757, by rfl⟩ : syracuseStep 3375353 = 2531515) B2531515
theorem B2250235 : Blo 2249435 2250235 := bstep (se 1 (by rfl) ⟨1687676, by rfl⟩ : syracuseStep 2250235 = 3375353) B3375353
theorem B2703337 : Blo 2249435 2703337 := bbase (se 2 (by rfl) ⟨1013751, by rfl⟩ : syracuseStep 2703337 = 2027503) (by norm_num)
theorem B57671189 : Blo 2249435 57671189 := bstep (se 6 (by rfl) ⟨1351668, by rfl⟩ : syracuseStep 57671189 = 2703337) B2703337
theorem B38447459 : Blo 2249435 38447459 := bstep (se 1 (by rfl) ⟨28835594, by rfl⟩ : syracuseStep 38447459 = 57671189) B57671189
theorem B25631639 : Blo 2249435 25631639 := bstep (se 1 (by rfl) ⟨19223729, by rfl⟩ : syracuseStep 25631639 = 38447459) B38447459
theorem B17087759 : Blo 2249435 17087759 := bstep (se 1 (by rfl) ⟨12815819, by rfl⟩ : syracuseStep 17087759 = 25631639) B25631639
theorem B11391839 : Blo 2249435 11391839 := bstep (se 1 (by rfl) ⟨8543879, by rfl⟩ : syracuseStep 11391839 = 17087759) B17087759
theorem B7594559 : Blo 2249435 7594559 := bstep (se 1 (by rfl) ⟨5695919, by rfl⟩ : syracuseStep 7594559 = 11391839) B11391839
theorem B5063039 : Blo 2249435 5063039 := bstep (se 1 (by rfl) ⟨3797279, by rfl⟩ : syracuseStep 5063039 = 7594559) B7594559
theorem B3375359 : Blo 2249435 3375359 := bstep (se 1 (by rfl) ⟨2531519, by rfl⟩ : syracuseStep 3375359 = 5063039) B5063039
theorem B2250239 : Blo 2249435 2250239 := bstep (se 1 (by rfl) ⟨1687679, by rfl⟩ : syracuseStep 2250239 = 3375359) B3375359
theorem B3375365 : Blo 2249435 3375365 := bbase (se 4 (by rfl) ⟨316440, by rfl⟩ : syracuseStep 3375365 = 632881) (by norm_num)
theorem B2250243 : Blo 2249435 2250243 := bstep (se 1 (by rfl) ⟨1687682, by rfl⟩ : syracuseStep 2250243 = 3375365) B3375365
theorem B3797293 : Blo 2249435 3797293 := bbase (se 3 (by rfl) ⟨711992, by rfl⟩ : syracuseStep 3797293 = 1423985) (by norm_num)
theorem B5063057 : Blo 2249435 5063057 := bstep (se 2 (by rfl) ⟨1898646, by rfl⟩ : syracuseStep 5063057 = 3797293) B3797293
theorem B3375371 : Blo 2249435 3375371 := bstep (se 1 (by rfl) ⟨2531528, by rfl⟩ : syracuseStep 3375371 = 5063057) B5063057
theorem B2250247 : Blo 2249435 2250247 := bstep (se 1 (by rfl) ⟨1687685, by rfl⟩ : syracuseStep 2250247 = 3375371) B3375371
theorem B2531533 : Blo 2249435 2531533 := bbase (se 3 (by rfl) ⟨474662, by rfl⟩ : syracuseStep 2531533 = 949325) (by norm_num)
theorem B3375377 : Blo 2249435 3375377 := bstep (se 2 (by rfl) ⟨1265766, by rfl⟩ : syracuseStep 3375377 = 2531533) B2531533
theorem B2250251 : Blo 2249435 2250251 := bstep (se 1 (by rfl) ⟨1687688, by rfl⟩ : syracuseStep 2250251 = 3375377) B3375377
theorem B7594613 : Blo 2249435 7594613 := bbase (se 5 (by rfl) ⟨355997, by rfl⟩ : syracuseStep 7594613 = 711995) (by norm_num)
theorem B5063075 : Blo 2249435 5063075 := bstep (se 1 (by rfl) ⟨3797306, by rfl⟩ : syracuseStep 5063075 = 7594613) B7594613
theorem B3375383 : Blo 2249435 3375383 := bstep (se 1 (by rfl) ⟨2531537, by rfl⟩ : syracuseStep 3375383 = 5063075) B5063075
theorem B2250255 : Blo 2249435 2250255 := bstep (se 1 (by rfl) ⟨1687691, by rfl⟩ : syracuseStep 2250255 = 3375383) B3375383
theorem B3375389 : Blo 2249435 3375389 := bbase (se 3 (by rfl) ⟨632885, by rfl⟩ : syracuseStep 3375389 = 1265771) (by norm_num)
theorem B2250259 : Blo 2249435 2250259 := bstep (se 1 (by rfl) ⟨1687694, by rfl⟩ : syracuseStep 2250259 = 3375389) B3375389
theorem B5063093 : Blo 2249435 5063093 := bbase (se 5 (by rfl) ⟨237332, by rfl⟩ : syracuseStep 5063093 = 474665) (by norm_num)
theorem B3375395 : Blo 2249435 3375395 := bstep (se 1 (by rfl) ⟨2531546, by rfl⟩ : syracuseStep 3375395 = 5063093) B5063093
theorem B2250263 : Blo 2249435 2250263 := bstep (se 1 (by rfl) ⟨1687697, by rfl⟩ : syracuseStep 2250263 = 3375395) B3375395
theorem B12165173 : Blo 2249435 12165173 := bbase (se 5 (by rfl) ⟨570242, by rfl⟩ : syracuseStep 12165173 = 1140485) (by norm_num)
theorem B8110115 : Blo 2249435 8110115 := bstep (se 1 (by rfl) ⟨6082586, by rfl⟩ : syracuseStep 8110115 = 12165173) B12165173
theorem B5406743 : Blo 2249435 5406743 := bstep (se 1 (by rfl) ⟨4055057, by rfl⟩ : syracuseStep 5406743 = 8110115) B8110115
theorem B3604495 : Blo 2249435 3604495 := bstep (se 1 (by rfl) ⟨2703371, by rfl⟩ : syracuseStep 3604495 = 5406743) B5406743
theorem B4805993 : Blo 2249435 4805993 := bstep (se 2 (by rfl) ⟨1802247, by rfl⟩ : syracuseStep 4805993 = 3604495) B3604495
theorem B12815981 : Blo 2249435 12815981 := bstep (se 3 (by rfl) ⟨2402996, by rfl⟩ : syracuseStep 12815981 = 4805993) B4805993
theorem B8543987 : Blo 2249435 8543987 := bstep (se 1 (by rfl) ⟨6407990, by rfl⟩ : syracuseStep 8543987 = 12815981) B12815981
theorem B5695991 : Blo 2249435 5695991 := bstep (se 1 (by rfl) ⟨4271993, by rfl⟩ : syracuseStep 5695991 = 8543987) B8543987
theorem B3797327 : Blo 2249435 3797327 := bstep (se 1 (by rfl) ⟨2847995, by rfl⟩ : syracuseStep 3797327 = 5695991) B5695991
theorem B2531551 : Blo 2249435 2531551 := bstep (se 1 (by rfl) ⟨1898663, by rfl⟩ : syracuseStep 2531551 = 3797327) B3797327
theorem B3375401 : Blo 2249435 3375401 := bstep (se 2 (by rfl) ⟨1265775, by rfl⟩ : syracuseStep 3375401 = 2531551) B2531551
theorem B2250267 : Blo 2249435 2250267 := bstep (se 1 (by rfl) ⟨1687700, by rfl⟩ : syracuseStep 2250267 = 3375401) B3375401
theorem B3604501 : Blo 2249435 3604501 := bbase (se 6 (by rfl) ⟨84480, by rfl⟩ : syracuseStep 3604501 = 168961) (by norm_num)
theorem B4806001 : Blo 2249435 4806001 := bstep (se 2 (by rfl) ⟨1802250, by rfl⟩ : syracuseStep 4806001 = 3604501) B3604501
theorem B6408001 : Blo 2249435 6408001 := bstep (se 2 (by rfl) ⟨2403000, by rfl⟩ : syracuseStep 6408001 = 4806001) B4806001
theorem B8544001 : Blo 2249435 8544001 := bstep (se 2 (by rfl) ⟨3204000, by rfl⟩ : syracuseStep 8544001 = 6408001) B6408001
theorem B11392001 : Blo 2249435 11392001 := bstep (se 2 (by rfl) ⟨4272000, by rfl⟩ : syracuseStep 11392001 = 8544001) B8544001
theorem B7594667 : Blo 2249435 7594667 := bstep (se 1 (by rfl) ⟨5696000, by rfl⟩ : syracuseStep 7594667 = 11392001) B11392001
theorem B5063111 : Blo 2249435 5063111 := bstep (se 1 (by rfl) ⟨3797333, by rfl⟩ : syracuseStep 5063111 = 7594667) B7594667
theorem B3375407 : Blo 2249435 3375407 := bstep (se 1 (by rfl) ⟨2531555, by rfl⟩ : syracuseStep 3375407 = 5063111) B5063111
theorem B2250271 : Blo 2249435 2250271 := bstep (se 1 (by rfl) ⟨1687703, by rfl⟩ : syracuseStep 2250271 = 3375407) B3375407
theorem B3375413 : Blo 2249435 3375413 := bbase (se 5 (by rfl) ⟨158222, by rfl⟩ : syracuseStep 3375413 = 316445) (by norm_num)
theorem B2250275 : Blo 2249435 2250275 := bstep (se 1 (by rfl) ⟨1687706, by rfl⟩ : syracuseStep 2250275 = 3375413) B3375413
theorem B5696021 : Blo 2249435 5696021 := bbase (se 6 (by rfl) ⟨133500, by rfl⟩ : syracuseStep 5696021 = 267001) (by norm_num)
theorem B3797347 : Blo 2249435 3797347 := bstep (se 1 (by rfl) ⟨2848010, by rfl⟩ : syracuseStep 3797347 = 5696021) B5696021
theorem B5063129 : Blo 2249435 5063129 := bstep (se 2 (by rfl) ⟨1898673, by rfl⟩ : syracuseStep 5063129 = 3797347) B3797347
theorem B3375419 : Blo 2249435 3375419 := bstep (se 1 (by rfl) ⟨2531564, by rfl⟩ : syracuseStep 3375419 = 5063129) B5063129
theorem B2250279 : Blo 2249435 2250279 := bstep (se 1 (by rfl) ⟨1687709, by rfl⟩ : syracuseStep 2250279 = 3375419) B3375419
theorem B2531569 : Blo 2249435 2531569 := bbase (se 2 (by rfl) ⟨949338, by rfl⟩ : syracuseStep 2531569 = 1898677) (by norm_num)
theorem B3375425 : Blo 2249435 3375425 := bstep (se 2 (by rfl) ⟨1265784, by rfl⟩ : syracuseStep 3375425 = 2531569) B2531569
theorem B2250283 : Blo 2249435 2250283 := bstep (se 1 (by rfl) ⟨1687712, by rfl⟩ : syracuseStep 2250283 = 3375425) B3375425
theorem B7698341 : Blo 2249435 7698341 := bbase (se 4 (by rfl) ⟨721719, by rfl⟩ : syracuseStep 7698341 = 1443439) (by norm_num)
theorem B20528909 : Blo 2249435 20528909 := bstep (se 3 (by rfl) ⟨3849170, by rfl⟩ : syracuseStep 20528909 = 7698341) B7698341
theorem B13685939 : Blo 2249435 13685939 := bstep (se 1 (by rfl) ⟨10264454, by rfl⟩ : syracuseStep 13685939 = 20528909) B20528909
theorem B9123959 : Blo 2249435 9123959 := bstep (se 1 (by rfl) ⟨6842969, by rfl⟩ : syracuseStep 9123959 = 13685939) B13685939
theorem B24330557 : Blo 2249435 24330557 := bstep (se 3 (by rfl) ⟨4561979, by rfl⟩ : syracuseStep 24330557 = 9123959) B9123959
theorem B16220371 : Blo 2249435 16220371 := bstep (se 1 (by rfl) ⟨12165278, by rfl⟩ : syracuseStep 16220371 = 24330557) B24330557
theorem B21627161 : Blo 2249435 21627161 := bstep (se 2 (by rfl) ⟨8110185, by rfl⟩ : syracuseStep 21627161 = 16220371) B16220371
theorem B14418107 : Blo 2249435 14418107 := bstep (se 1 (by rfl) ⟨10813580, by rfl⟩ : syracuseStep 14418107 = 21627161) B21627161
theorem B9612071 : Blo 2249435 9612071 := bstep (se 1 (by rfl) ⟨7209053, by rfl⟩ : syracuseStep 9612071 = 14418107) B14418107
theorem B6408047 : Blo 2249435 6408047 := bstep (se 1 (by rfl) ⟨4806035, by rfl⟩ : syracuseStep 6408047 = 9612071) B9612071
theorem B4272031 : Blo 2249435 4272031 := bstep (se 1 (by rfl) ⟨3204023, by rfl⟩ : syracuseStep 4272031 = 6408047) B6408047
theorem B5696041 : Blo 2249435 5696041 := bstep (se 2 (by rfl) ⟨2136015, by rfl⟩ : syracuseStep 5696041 = 4272031) B4272031
theorem B7594721 : Blo 2249435 7594721 := bstep (se 2 (by rfl) ⟨2848020, by rfl⟩ : syracuseStep 7594721 = 5696041) B5696041
theorem B5063147 : Blo 2249435 5063147 := bstep (se 1 (by rfl) ⟨3797360, by rfl⟩ : syracuseStep 5063147 = 7594721) B7594721
theorem B3375431 : Blo 2249435 3375431 := bstep (se 1 (by rfl) ⟨2531573, by rfl⟩ : syracuseStep 3375431 = 5063147) B5063147
theorem B2250287 : Blo 2249435 2250287 := bstep (se 1 (by rfl) ⟨1687715, by rfl⟩ : syracuseStep 2250287 = 3375431) B3375431
theorem B3375437 : Blo 2249435 3375437 := bbase (se 3 (by rfl) ⟨632894, by rfl⟩ : syracuseStep 3375437 = 1265789) (by norm_num)
theorem B2250291 : Blo 2249435 2250291 := bstep (se 1 (by rfl) ⟨1687718, by rfl⟩ : syracuseStep 2250291 = 3375437) B3375437
theorem B5063165 : Blo 2249435 5063165 := bbase (se 3 (by rfl) ⟨949343, by rfl⟩ : syracuseStep 5063165 = 1898687) (by norm_num)
theorem B3375443 : Blo 2249435 3375443 := bstep (se 1 (by rfl) ⟨2531582, by rfl⟩ : syracuseStep 3375443 = 5063165) B5063165
theorem B2250295 : Blo 2249435 2250295 := bstep (se 1 (by rfl) ⟨1687721, by rfl⟩ : syracuseStep 2250295 = 3375443) B3375443
theorem B3797381 : Blo 2249435 3797381 := bbase (se 4 (by rfl) ⟨356004, by rfl⟩ : syracuseStep 3797381 = 712009) (by norm_num)
theorem B2531587 : Blo 2249435 2531587 := bstep (se 1 (by rfl) ⟨1898690, by rfl⟩ : syracuseStep 2531587 = 3797381) B3797381
theorem B3375449 : Blo 2249435 3375449 := bstep (se 2 (by rfl) ⟨1265793, by rfl⟩ : syracuseStep 3375449 = 2531587) B2531587
theorem B2250299 : Blo 2249435 2250299 := bstep (se 1 (by rfl) ⟨1687724, by rfl⟩ : syracuseStep 2250299 = 3375449) B3375449
theorem B17088245 : Blo 2249435 17088245 := bbase (se 5 (by rfl) ⟨801011, by rfl⟩ : syracuseStep 17088245 = 1602023) (by norm_num)
theorem B11392163 : Blo 2249435 11392163 := bstep (se 1 (by rfl) ⟨8544122, by rfl⟩ : syracuseStep 11392163 = 17088245) B17088245
theorem B7594775 : Blo 2249435 7594775 := bstep (se 1 (by rfl) ⟨5696081, by rfl⟩ : syracuseStep 7594775 = 11392163) B11392163
theorem B5063183 : Blo 2249435 5063183 := bstep (se 1 (by rfl) ⟨3797387, by rfl⟩ : syracuseStep 5063183 = 7594775) B7594775
theorem B3375455 : Blo 2249435 3375455 := bstep (se 1 (by rfl) ⟨2531591, by rfl⟩ : syracuseStep 3375455 = 5063183) B5063183
theorem B2250303 : Blo 2249435 2250303 := bstep (se 1 (by rfl) ⟨1687727, by rfl⟩ : syracuseStep 2250303 = 3375455) B3375455
theorem B3375461 : Blo 2249435 3375461 := bbase (se 4 (by rfl) ⟨316449, by rfl⟩ : syracuseStep 3375461 = 632899) (by norm_num)
theorem B2250307 : Blo 2249435 2250307 := bstep (se 1 (by rfl) ⟨1687730, by rfl⟩ : syracuseStep 2250307 = 3375461) B3375461
theorem B4272077 : Blo 2249435 4272077 := bbase (se 3 (by rfl) ⟨801014, by rfl⟩ : syracuseStep 4272077 = 1602029) (by norm_num)
theorem B2848051 : Blo 2249435 2848051 := bstep (se 1 (by rfl) ⟨2136038, by rfl⟩ : syracuseStep 2848051 = 4272077) B4272077
theorem B3797401 : Blo 2249435 3797401 := bstep (se 2 (by rfl) ⟨1424025, by rfl⟩ : syracuseStep 3797401 = 2848051) B2848051
theorem B5063201 : Blo 2249435 5063201 := bstep (se 2 (by rfl) ⟨1898700, by rfl⟩ : syracuseStep 5063201 = 3797401) B3797401
theorem B3375467 : Blo 2249435 3375467 := bstep (se 1 (by rfl) ⟨2531600, by rfl⟩ : syracuseStep 3375467 = 5063201) B5063201
theorem B2250311 : Blo 2249435 2250311 := bstep (se 1 (by rfl) ⟨1687733, by rfl⟩ : syracuseStep 2250311 = 3375467) B3375467
theorem B2531605 : Blo 2249435 2531605 := bbase (se 6 (by rfl) ⟨59334, by rfl⟩ : syracuseStep 2531605 = 118669) (by norm_num)
theorem B3375473 : Blo 2249435 3375473 := bstep (se 2 (by rfl) ⟨1265802, by rfl⟩ : syracuseStep 3375473 = 2531605) B2531605
theorem B2250315 : Blo 2249435 2250315 := bstep (se 1 (by rfl) ⟨1687736, by rfl⟩ : syracuseStep 2250315 = 3375473) B3375473
theorem B2848061 : Blo 2249435 2848061 := bbase (se 3 (by rfl) ⟨534011, by rfl⟩ : syracuseStep 2848061 = 1068023) (by norm_num)
theorem B7594829 : Blo 2249435 7594829 := bstep (se 3 (by rfl) ⟨1424030, by rfl⟩ : syracuseStep 7594829 = 2848061) B2848061
theorem B5063219 : Blo 2249435 5063219 := bstep (se 1 (by rfl) ⟨3797414, by rfl⟩ : syracuseStep 5063219 = 7594829) B7594829
theorem B3375479 : Blo 2249435 3375479 := bstep (se 1 (by rfl) ⟨2531609, by rfl⟩ : syracuseStep 3375479 = 5063219) B5063219
theorem B2250319 : Blo 2249435 2250319 := bstep (se 1 (by rfl) ⟨1687739, by rfl⟩ : syracuseStep 2250319 = 3375479) B3375479
theorem B3375485 : Blo 2249435 3375485 := bbase (se 3 (by rfl) ⟨632903, by rfl⟩ : syracuseStep 3375485 = 1265807) (by norm_num)
theorem B2250323 : Blo 2249435 2250323 := bstep (se 1 (by rfl) ⟨1687742, by rfl⟩ : syracuseStep 2250323 = 3375485) B3375485
theorem B5063237 : Blo 2249435 5063237 := bbase (se 4 (by rfl) ⟨474678, by rfl⟩ : syracuseStep 5063237 = 949357) (by norm_num)
theorem B3375491 : Blo 2249435 3375491 := bstep (se 1 (by rfl) ⟨2531618, by rfl⟩ : syracuseStep 3375491 = 5063237) B5063237
theorem B2250327 : Blo 2249435 2250327 := bstep (se 1 (by rfl) ⟨1687745, by rfl⟩ : syracuseStep 2250327 = 3375491) B3375491
theorem B2403065 : Blo 2249435 2403065 := bbase (se 2 (by rfl) ⟨901149, by rfl⟩ : syracuseStep 2403065 = 1802299) (by norm_num)
theorem B6408173 : Blo 2249435 6408173 := bstep (se 3 (by rfl) ⟨1201532, by rfl⟩ : syracuseStep 6408173 = 2403065) B2403065
theorem B4272115 : Blo 2249435 4272115 := bstep (se 1 (by rfl) ⟨3204086, by rfl⟩ : syracuseStep 4272115 = 6408173) B6408173
theorem B5696153 : Blo 2249435 5696153 := bstep (se 2 (by rfl) ⟨2136057, by rfl⟩ : syracuseStep 5696153 = 4272115) B4272115
theorem B3797435 : Blo 2249435 3797435 := bstep (se 1 (by rfl) ⟨2848076, by rfl⟩ : syracuseStep 3797435 = 5696153) B5696153
theorem B2531623 : Blo 2249435 2531623 := bstep (se 1 (by rfl) ⟨1898717, by rfl⟩ : syracuseStep 2531623 = 3797435) B3797435
theorem B3375497 : Blo 2249435 3375497 := bstep (se 2 (by rfl) ⟨1265811, by rfl⟩ : syracuseStep 3375497 = 2531623) B2531623
theorem B2250331 : Blo 2249435 2250331 := bstep (se 1 (by rfl) ⟨1687748, by rfl⟩ : syracuseStep 2250331 = 3375497) B3375497
theorem B11392325 : Blo 2249435 11392325 := bbase (se 4 (by rfl) ⟨1068030, by rfl⟩ : syracuseStep 11392325 = 2136061) (by norm_num)
theorem B7594883 : Blo 2249435 7594883 := bstep (se 1 (by rfl) ⟨5696162, by rfl⟩ : syracuseStep 7594883 = 11392325) B11392325
theorem B5063255 : Blo 2249435 5063255 := bstep (se 1 (by rfl) ⟨3797441, by rfl⟩ : syracuseStep 5063255 = 7594883) B7594883
theorem B3375503 : Blo 2249435 3375503 := bstep (se 1 (by rfl) ⟨2531627, by rfl⟩ : syracuseStep 3375503 = 5063255) B5063255
theorem B2250335 : Blo 2249435 2250335 := bstep (se 1 (by rfl) ⟨1687751, by rfl⟩ : syracuseStep 2250335 = 3375503) B3375503
theorem B3375509 : Blo 2249435 3375509 := bbase (se 6 (by rfl) ⟨79113, by rfl⟩ : syracuseStep 3375509 = 158227) (by norm_num)
theorem B2250339 : Blo 2249435 2250339 := bstep (se 1 (by rfl) ⟨1687754, by rfl⟩ : syracuseStep 2250339 = 3375509) B3375509
theorem B5406925 : Blo 2249435 5406925 := bbase (se 3 (by rfl) ⟨1013798, by rfl⟩ : syracuseStep 5406925 = 2027597) (by norm_num)
theorem B7209233 : Blo 2249435 7209233 := bstep (se 2 (by rfl) ⟨2703462, by rfl⟩ : syracuseStep 7209233 = 5406925) B5406925
theorem B4806155 : Blo 2249435 4806155 := bstep (se 1 (by rfl) ⟨3604616, by rfl⟩ : syracuseStep 4806155 = 7209233) B7209233
theorem B12816413 : Blo 2249435 12816413 := bstep (se 3 (by rfl) ⟨2403077, by rfl⟩ : syracuseStep 12816413 = 4806155) B4806155
theorem B8544275 : Blo 2249435 8544275 := bstep (se 1 (by rfl) ⟨6408206, by rfl⟩ : syracuseStep 8544275 = 12816413) B12816413
theorem B5696183 : Blo 2249435 5696183 := bstep (se 1 (by rfl) ⟨4272137, by rfl⟩ : syracuseStep 5696183 = 8544275) B8544275
theorem B3797455 : Blo 2249435 3797455 := bstep (se 1 (by rfl) ⟨2848091, by rfl⟩ : syracuseStep 3797455 = 5696183) B5696183
theorem B5063273 : Blo 2249435 5063273 := bstep (se 2 (by rfl) ⟨1898727, by rfl⟩ : syracuseStep 5063273 = 3797455) B3797455
theorem B3375515 : Blo 2249435 3375515 := bstep (se 1 (by rfl) ⟨2531636, by rfl⟩ : syracuseStep 3375515 = 5063273) B5063273
theorem B2250343 : Blo 2249435 2250343 := bstep (se 1 (by rfl) ⟨1687757, by rfl⟩ : syracuseStep 2250343 = 3375515) B3375515
theorem B2531641 : Blo 2249435 2531641 := bbase (se 2 (by rfl) ⟨949365, by rfl⟩ : syracuseStep 2531641 = 1898731) (by norm_num)
theorem B3375521 : Blo 2249435 3375521 := bstep (se 2 (by rfl) ⟨1265820, by rfl⟩ : syracuseStep 3375521 = 2531641) B2531641
theorem B2250347 : Blo 2249435 2250347 := bstep (se 1 (by rfl) ⟨1687760, by rfl⟩ : syracuseStep 2250347 = 3375521) B3375521
theorem B6408229 : Blo 2249435 6408229 := bbase (se 4 (by rfl) ⟨600771, by rfl⟩ : syracuseStep 6408229 = 1201543) (by norm_num)
theorem B8544305 : Blo 2249435 8544305 := bstep (se 2 (by rfl) ⟨3204114, by rfl⟩ : syracuseStep 8544305 = 6408229) B6408229
theorem B5696203 : Blo 2249435 5696203 := bstep (se 1 (by rfl) ⟨4272152, by rfl⟩ : syracuseStep 5696203 = 8544305) B8544305
theorem B7594937 : Blo 2249435 7594937 := bstep (se 2 (by rfl) ⟨2848101, by rfl⟩ : syracuseStep 7594937 = 5696203) B5696203
theorem B5063291 : Blo 2249435 5063291 := bstep (se 1 (by rfl) ⟨3797468, by rfl⟩ : syracuseStep 5063291 = 7594937) B7594937
theorem B3375527 : Blo 2249435 3375527 := bstep (se 1 (by rfl) ⟨2531645, by rfl⟩ : syracuseStep 3375527 = 5063291) B5063291
theorem B2250351 : Blo 2249435 2250351 := bstep (se 1 (by rfl) ⟨1687763, by rfl⟩ : syracuseStep 2250351 = 3375527) B3375527
theorem B3375533 : Blo 2249435 3375533 := bbase (se 3 (by rfl) ⟨632912, by rfl⟩ : syracuseStep 3375533 = 1265825) (by norm_num)
theorem B2250355 : Blo 2249435 2250355 := bstep (se 1 (by rfl) ⟨1687766, by rfl⟩ : syracuseStep 2250355 = 3375533) B3375533
theorem B5063309 : Blo 2249435 5063309 := bbase (se 3 (by rfl) ⟨949370, by rfl⟩ : syracuseStep 5063309 = 1898741) (by norm_num)
theorem B3375539 : Blo 2249435 3375539 := bstep (se 1 (by rfl) ⟨2531654, by rfl⟩ : syracuseStep 3375539 = 5063309) B5063309
theorem B2250359 : Blo 2249435 2250359 := bstep (se 1 (by rfl) ⟨1687769, by rfl⟩ : syracuseStep 2250359 = 3375539) B3375539
theorem B2848117 : Blo 2249435 2848117 := bbase (se 5 (by rfl) ⟨133505, by rfl⟩ : syracuseStep 2848117 = 267011) (by norm_num)
theorem B3797489 : Blo 2249435 3797489 := bstep (se 2 (by rfl) ⟨1424058, by rfl⟩ : syracuseStep 3797489 = 2848117) B2848117
theorem B2531659 : Blo 2249435 2531659 := bstep (se 1 (by rfl) ⟨1898744, by rfl⟩ : syracuseStep 2531659 = 3797489) B3797489
theorem B3375545 : Blo 2249435 3375545 := bstep (se 2 (by rfl) ⟨1265829, by rfl⟩ : syracuseStep 3375545 = 2531659) B2531659
theorem B2250363 : Blo 2249435 2250363 := bstep (se 1 (by rfl) ⟨1687772, by rfl⟩ : syracuseStep 2250363 = 3375545) B3375545
theorem B4562141 : Blo 2249435 4562141 := bbase (se 3 (by rfl) ⟨855401, by rfl⟩ : syracuseStep 4562141 = 1710803) (by norm_num)
theorem B12165709 : Blo 2249435 12165709 := bstep (se 3 (by rfl) ⟨2281070, by rfl⟩ : syracuseStep 12165709 = 4562141) B4562141
theorem B16220945 : Blo 2249435 16220945 := bstep (se 2 (by rfl) ⟨6082854, by rfl⟩ : syracuseStep 16220945 = 12165709) B12165709
theorem B43255853 : Blo 2249435 43255853 := bstep (se 3 (by rfl) ⟨8110472, by rfl⟩ : syracuseStep 43255853 = 16220945) B16220945
theorem B28837235 : Blo 2249435 28837235 := bstep (se 1 (by rfl) ⟨21627926, by rfl⟩ : syracuseStep 28837235 = 43255853) B43255853
theorem B19224823 : Blo 2249435 19224823 := bstep (se 1 (by rfl) ⟨14418617, by rfl⟩ : syracuseStep 19224823 = 28837235) B28837235
theorem B25633097 : Blo 2249435 25633097 := bstep (se 2 (by rfl) ⟨9612411, by rfl⟩ : syracuseStep 25633097 = 19224823) B19224823
theorem B17088731 : Blo 2249435 17088731 := bstep (se 1 (by rfl) ⟨12816548, by rfl⟩ : syracuseStep 17088731 = 25633097) B25633097
theorem B11392487 : Blo 2249435 11392487 := bstep (se 1 (by rfl) ⟨8544365, by rfl⟩ : syracuseStep 11392487 = 17088731) B17088731
theorem B7594991 : Blo 2249435 7594991 := bstep (se 1 (by rfl) ⟨5696243, by rfl⟩ : syracuseStep 7594991 = 11392487) B11392487
theorem B5063327 : Blo 2249435 5063327 := bstep (se 1 (by rfl) ⟨3797495, by rfl⟩ : syracuseStep 5063327 = 7594991) B7594991
theorem B3375551 : Blo 2249435 3375551 := bstep (se 1 (by rfl) ⟨2531663, by rfl⟩ : syracuseStep 3375551 = 5063327) B5063327
theorem B2250367 : Blo 2249435 2250367 := bstep (se 1 (by rfl) ⟨1687775, by rfl⟩ : syracuseStep 2250367 = 3375551) B3375551
theorem B3375557 : Blo 2249435 3375557 := bbase (se 4 (by rfl) ⟨316458, by rfl⟩ : syracuseStep 3375557 = 632917) (by norm_num)
theorem B2250371 : Blo 2249435 2250371 := bstep (se 1 (by rfl) ⟨1687778, by rfl⟩ : syracuseStep 2250371 = 3375557) B3375557
theorem B3797509 : Blo 2249435 3797509 := bbase (se 4 (by rfl) ⟨356016, by rfl⟩ : syracuseStep 3797509 = 712033) (by norm_num)
theorem B5063345 : Blo 2249435 5063345 := bstep (se 2 (by rfl) ⟨1898754, by rfl⟩ : syracuseStep 5063345 = 3797509) B3797509
theorem B3375563 : Blo 2249435 3375563 := bstep (se 1 (by rfl) ⟨2531672, by rfl⟩ : syracuseStep 3375563 = 5063345) B5063345
theorem B2250375 : Blo 2249435 2250375 := bstep (se 1 (by rfl) ⟨1687781, by rfl⟩ : syracuseStep 2250375 = 3375563) B3375563
theorem B2531677 : Blo 2249435 2531677 := bbase (se 3 (by rfl) ⟨474689, by rfl⟩ : syracuseStep 2531677 = 949379) (by norm_num)
theorem B3375569 : Blo 2249435 3375569 := bstep (se 2 (by rfl) ⟨1265838, by rfl⟩ : syracuseStep 3375569 = 2531677) B2531677
theorem B2250379 : Blo 2249435 2250379 := bstep (se 1 (by rfl) ⟨1687784, by rfl⟩ : syracuseStep 2250379 = 3375569) B3375569
theorem B7595045 : Blo 2249435 7595045 := bbase (se 4 (by rfl) ⟨712035, by rfl⟩ : syracuseStep 7595045 = 1424071) (by norm_num)
theorem B5063363 : Blo 2249435 5063363 := bstep (se 1 (by rfl) ⟨3797522, by rfl⟩ : syracuseStep 5063363 = 7595045) B7595045
theorem B3375575 : Blo 2249435 3375575 := bstep (se 1 (by rfl) ⟨2531681, by rfl⟩ : syracuseStep 3375575 = 5063363) B5063363
theorem B2250383 : Blo 2249435 2250383 := bstep (se 1 (by rfl) ⟨1687787, by rfl⟩ : syracuseStep 2250383 = 3375575) B3375575
theorem B3375581 : Blo 2249435 3375581 := bbase (se 3 (by rfl) ⟨632921, by rfl⟩ : syracuseStep 3375581 = 1265843) (by norm_num)
theorem B2250387 : Blo 2249435 2250387 := bstep (se 1 (by rfl) ⟨1687790, by rfl⟩ : syracuseStep 2250387 = 3375581) B3375581
theorem B5063381 : Blo 2249435 5063381 := bbase (se 7 (by rfl) ⟨59336, by rfl⟩ : syracuseStep 5063381 = 118673) (by norm_num)
theorem B3375587 : Blo 2249435 3375587 := bstep (se 1 (by rfl) ⟨2531690, by rfl⟩ : syracuseStep 3375587 = 5063381) B5063381
theorem B2250391 : Blo 2249435 2250391 := bstep (se 1 (by rfl) ⟨1687793, by rfl⟩ : syracuseStep 2250391 = 3375587) B3375587
theorem B9612533 : Blo 2249435 9612533 := bbase (se 5 (by rfl) ⟨450587, by rfl⟩ : syracuseStep 9612533 = 901175) (by norm_num)
theorem B6408355 : Blo 2249435 6408355 := bstep (se 1 (by rfl) ⟨4806266, by rfl⟩ : syracuseStep 6408355 = 9612533) B9612533
theorem B8544473 : Blo 2249435 8544473 := bstep (se 2 (by rfl) ⟨3204177, by rfl⟩ : syracuseStep 8544473 = 6408355) B6408355
theorem B5696315 : Blo 2249435 5696315 := bstep (se 1 (by rfl) ⟨4272236, by rfl⟩ : syracuseStep 5696315 = 8544473) B8544473
theorem B3797543 : Blo 2249435 3797543 := bstep (se 1 (by rfl) ⟨2848157, by rfl⟩ : syracuseStep 3797543 = 5696315) B5696315
theorem B2531695 : Blo 2249435 2531695 := bstep (se 1 (by rfl) ⟨1898771, by rfl⟩ : syracuseStep 2531695 = 3797543) B3797543
theorem B3375593 : Blo 2249435 3375593 := bstep (se 2 (by rfl) ⟨1265847, by rfl⟩ : syracuseStep 3375593 = 2531695) B2531695
theorem B2250395 : Blo 2249435 2250395 := bstep (se 1 (by rfl) ⟨1687796, by rfl⟩ : syracuseStep 2250395 = 3375593) B3375593
theorem B7698725 : Blo 2249435 7698725 := bbase (se 4 (by rfl) ⟨721755, by rfl⟩ : syracuseStep 7698725 = 1443511) (by norm_num)
theorem B5132483 : Blo 2249435 5132483 := bstep (se 1 (by rfl) ⟨3849362, by rfl⟩ : syracuseStep 5132483 = 7698725) B7698725
theorem B3421655 : Blo 2249435 3421655 := bstep (se 1 (by rfl) ⟨2566241, by rfl⟩ : syracuseStep 3421655 = 5132483) B5132483
theorem B2281103 : Blo 2249435 2281103 := bstep (se 1 (by rfl) ⟨1710827, by rfl⟩ : syracuseStep 2281103 = 3421655) B3421655
theorem B24331765 : Blo 2249435 24331765 := bstep (se 5 (by rfl) ⟨1140551, by rfl⟩ : syracuseStep 24331765 = 2281103) B2281103
theorem B32442353 : Blo 2249435 32442353 := bstep (se 2 (by rfl) ⟨12165882, by rfl⟩ : syracuseStep 32442353 = 24331765) B24331765
theorem B21628235 : Blo 2249435 21628235 := bstep (se 1 (by rfl) ⟨16221176, by rfl⟩ : syracuseStep 21628235 = 32442353) B32442353
theorem B14418823 : Blo 2249435 14418823 := bstep (se 1 (by rfl) ⟨10814117, by rfl⟩ : syracuseStep 14418823 = 21628235) B21628235
theorem B19225097 : Blo 2249435 19225097 := bstep (se 2 (by rfl) ⟨7209411, by rfl⟩ : syracuseStep 19225097 = 14418823) B14418823
theorem B12816731 : Blo 2249435 12816731 := bstep (se 1 (by rfl) ⟨9612548, by rfl⟩ : syracuseStep 12816731 = 19225097) B19225097
theorem B8544487 : Blo 2249435 8544487 := bstep (se 1 (by rfl) ⟨6408365, by rfl⟩ : syracuseStep 8544487 = 12816731) B12816731
theorem B11392649 : Blo 2249435 11392649 := bstep (se 2 (by rfl) ⟨4272243, by rfl⟩ : syracuseStep 11392649 = 8544487) B8544487
theorem B7595099 : Blo 2249435 7595099 := bstep (se 1 (by rfl) ⟨5696324, by rfl⟩ : syracuseStep 7595099 = 11392649) B11392649
theorem B5063399 : Blo 2249435 5063399 := bstep (se 1 (by rfl) ⟨3797549, by rfl⟩ : syracuseStep 5063399 = 7595099) B7595099
theorem B3375599 : Blo 2249435 3375599 := bstep (se 1 (by rfl) ⟨2531699, by rfl⟩ : syracuseStep 3375599 = 5063399) B5063399
theorem B2250399 : Blo 2249435 2250399 := bstep (se 1 (by rfl) ⟨1687799, by rfl⟩ : syracuseStep 2250399 = 3375599) B3375599
theorem B3375605 : Blo 2249435 3375605 := bbase (se 5 (by rfl) ⟨158231, by rfl⟩ : syracuseStep 3375605 = 316463) (by norm_num)
theorem B2250403 : Blo 2249435 2250403 := bstep (se 1 (by rfl) ⟨1687802, by rfl⟩ : syracuseStep 2250403 = 3375605) B3375605
theorem B6408389 : Blo 2249435 6408389 := bbase (se 4 (by rfl) ⟨600786, by rfl⟩ : syracuseStep 6408389 = 1201573) (by norm_num)
theorem B4272259 : Blo 2249435 4272259 := bstep (se 1 (by rfl) ⟨3204194, by rfl⟩ : syracuseStep 4272259 = 6408389) B6408389
theorem B5696345 : Blo 2249435 5696345 := bstep (se 2 (by rfl) ⟨2136129, by rfl⟩ : syracuseStep 5696345 = 4272259) B4272259
theorem B3797563 : Blo 2249435 3797563 := bstep (se 1 (by rfl) ⟨2848172, by rfl⟩ : syracuseStep 3797563 = 5696345) B5696345
theorem B5063417 : Blo 2249435 5063417 := bstep (se 2 (by rfl) ⟨1898781, by rfl⟩ : syracuseStep 5063417 = 3797563) B3797563
theorem B3375611 : Blo 2249435 3375611 := bstep (se 1 (by rfl) ⟨2531708, by rfl⟩ : syracuseStep 3375611 = 5063417) B5063417
theorem B2250407 : Blo 2249435 2250407 := bstep (se 1 (by rfl) ⟨1687805, by rfl⟩ : syracuseStep 2250407 = 3375611) B3375611
theorem B2531713 : Blo 2249435 2531713 := bbase (se 2 (by rfl) ⟨949392, by rfl⟩ : syracuseStep 2531713 = 1898785) (by norm_num)
theorem B3375617 : Blo 2249435 3375617 := bstep (se 2 (by rfl) ⟨1265856, by rfl⟩ : syracuseStep 3375617 = 2531713) B2531713
theorem B2250411 : Blo 2249435 2250411 := bstep (se 1 (by rfl) ⟨1687808, by rfl⟩ : syracuseStep 2250411 = 3375617) B3375617
theorem B5696365 : Blo 2249435 5696365 := bbase (se 3 (by rfl) ⟨1068068, by rfl⟩ : syracuseStep 5696365 = 2136137) (by norm_num)
theorem B7595153 : Blo 2249435 7595153 := bstep (se 2 (by rfl) ⟨2848182, by rfl⟩ : syracuseStep 7595153 = 5696365) B5696365
theorem B5063435 : Blo 2249435 5063435 := bstep (se 1 (by rfl) ⟨3797576, by rfl⟩ : syracuseStep 5063435 = 7595153) B7595153
theorem B3375623 : Blo 2249435 3375623 := bstep (se 1 (by rfl) ⟨2531717, by rfl⟩ : syracuseStep 3375623 = 5063435) B5063435
theorem B2250415 : Blo 2249435 2250415 := bstep (se 1 (by rfl) ⟨1687811, by rfl⟩ : syracuseStep 2250415 = 3375623) B3375623
theorem B3375629 : Blo 2249435 3375629 := bbase (se 3 (by rfl) ⟨632930, by rfl⟩ : syracuseStep 3375629 = 1265861) (by norm_num)
theorem B2250419 : Blo 2249435 2250419 := bstep (se 1 (by rfl) ⟨1687814, by rfl⟩ : syracuseStep 2250419 = 3375629) B3375629
theorem B5063453 : Blo 2249435 5063453 := bbase (se 3 (by rfl) ⟨949397, by rfl⟩ : syracuseStep 5063453 = 1898795) (by norm_num)
theorem B3375635 : Blo 2249435 3375635 := bstep (se 1 (by rfl) ⟨2531726, by rfl⟩ : syracuseStep 3375635 = 5063453) B5063453
theorem B2250423 : Blo 2249435 2250423 := bstep (se 1 (by rfl) ⟨1687817, by rfl⟩ : syracuseStep 2250423 = 3375635) B3375635
theorem B3797597 : Blo 2249435 3797597 := bbase (se 3 (by rfl) ⟨712049, by rfl⟩ : syracuseStep 3797597 = 1424099) (by norm_num)
theorem B2531731 : Blo 2249435 2531731 := bstep (se 1 (by rfl) ⟨1898798, by rfl⟩ : syracuseStep 2531731 = 3797597) B3797597
theorem B3375641 : Blo 2249435 3375641 := bstep (se 2 (by rfl) ⟨1265865, by rfl⟩ : syracuseStep 3375641 = 2531731) B2531731
theorem B2250427 : Blo 2249435 2250427 := bstep (se 1 (by rfl) ⟨1687820, by rfl⟩ : syracuseStep 2250427 = 3375641) B3375641
theorem B3604757 : Blo 2249435 3604757 := bbase (se 6 (by rfl) ⟨84486, by rfl⟩ : syracuseStep 3604757 = 168973) (by norm_num)
theorem B9612685 : Blo 2249435 9612685 := bstep (se 3 (by rfl) ⟨1802378, by rfl⟩ : syracuseStep 9612685 = 3604757) B3604757
theorem B12816913 : Blo 2249435 12816913 := bstep (se 2 (by rfl) ⟨4806342, by rfl⟩ : syracuseStep 12816913 = 9612685) B9612685
theorem B17089217 : Blo 2249435 17089217 := bstep (se 2 (by rfl) ⟨6408456, by rfl⟩ : syracuseStep 17089217 = 12816913) B12816913
theorem B11392811 : Blo 2249435 11392811 := bstep (se 1 (by rfl) ⟨8544608, by rfl⟩ : syracuseStep 11392811 = 17089217) B17089217
theorem B7595207 : Blo 2249435 7595207 := bstep (se 1 (by rfl) ⟨5696405, by rfl⟩ : syracuseStep 7595207 = 11392811) B11392811
theorem B5063471 : Blo 2249435 5063471 := bstep (se 1 (by rfl) ⟨3797603, by rfl⟩ : syracuseStep 5063471 = 7595207) B7595207
theorem B3375647 : Blo 2249435 3375647 := bstep (se 1 (by rfl) ⟨2531735, by rfl⟩ : syracuseStep 3375647 = 5063471) B5063471
theorem B2250431 : Blo 2249435 2250431 := bstep (se 1 (by rfl) ⟨1687823, by rfl⟩ : syracuseStep 2250431 = 3375647) B3375647
theorem B3375653 : Blo 2249435 3375653 := bbase (se 4 (by rfl) ⟨316467, by rfl⟩ : syracuseStep 3375653 = 632935) (by norm_num)
theorem B2250435 : Blo 2249435 2250435 := bstep (se 1 (by rfl) ⟨1687826, by rfl⟩ : syracuseStep 2250435 = 3375653) B3375653
theorem B2848213 : Blo 2249435 2848213 := bbase (se 7 (by rfl) ⟨33377, by rfl⟩ : syracuseStep 2848213 = 66755) (by norm_num)
theorem B3797617 : Blo 2249435 3797617 := bstep (se 2 (by rfl) ⟨1424106, by rfl⟩ : syracuseStep 3797617 = 2848213) B2848213
theorem B5063489 : Blo 2249435 5063489 := bstep (se 2 (by rfl) ⟨1898808, by rfl⟩ : syracuseStep 5063489 = 3797617) B3797617
theorem B3375659 : Blo 2249435 3375659 := bstep (se 1 (by rfl) ⟨2531744, by rfl⟩ : syracuseStep 3375659 = 5063489) B5063489
theorem B2250439 : Blo 2249435 2250439 := bstep (se 1 (by rfl) ⟨1687829, by rfl⟩ : syracuseStep 2250439 = 3375659) B3375659
theorem B2531749 : Blo 2249435 2531749 := bbase (se 4 (by rfl) ⟨237351, by rfl⟩ : syracuseStep 2531749 = 474703) (by norm_num)
theorem B3375665 : Blo 2249435 3375665 := bstep (se 2 (by rfl) ⟨1265874, by rfl⟩ : syracuseStep 3375665 = 2531749) B2531749
theorem B2250443 : Blo 2249435 2250443 := bstep (se 1 (by rfl) ⟨1687832, by rfl⟩ : syracuseStep 2250443 = 3375665) B3375665
theorem B3849445 : Blo 2249435 3849445 := bbase (se 4 (by rfl) ⟨360885, by rfl⟩ : syracuseStep 3849445 = 721771) (by norm_num)
theorem B5132593 : Blo 2249435 5132593 := bstep (se 2 (by rfl) ⟨1924722, by rfl⟩ : syracuseStep 5132593 = 3849445) B3849445
theorem B6843457 : Blo 2249435 6843457 := bstep (se 2 (by rfl) ⟨2566296, by rfl⟩ : syracuseStep 6843457 = 5132593) B5132593
theorem B9124609 : Blo 2249435 9124609 := bstep (se 2 (by rfl) ⟨3421728, by rfl⟩ : syracuseStep 9124609 = 6843457) B6843457
theorem B12166145 : Blo 2249435 12166145 := bstep (se 2 (by rfl) ⟨4562304, by rfl⟩ : syracuseStep 12166145 = 9124609) B9124609
theorem B8110763 : Blo 2249435 8110763 := bstep (se 1 (by rfl) ⟨6083072, by rfl⟩ : syracuseStep 8110763 = 12166145) B12166145
theorem B5407175 : Blo 2249435 5407175 := bstep (se 1 (by rfl) ⟨4055381, by rfl⟩ : syracuseStep 5407175 = 8110763) B8110763
theorem B14419133 : Blo 2249435 14419133 := bstep (se 3 (by rfl) ⟨2703587, by rfl⟩ : syracuseStep 14419133 = 5407175) B5407175
theorem B9612755 : Blo 2249435 9612755 := bstep (se 1 (by rfl) ⟨7209566, by rfl⟩ : syracuseStep 9612755 = 14419133) B14419133
theorem B6408503 : Blo 2249435 6408503 := bstep (se 1 (by rfl) ⟨4806377, by rfl⟩ : syracuseStep 6408503 = 9612755) B9612755
theorem B4272335 : Blo 2249435 4272335 := bstep (se 1 (by rfl) ⟨3204251, by rfl⟩ : syracuseStep 4272335 = 6408503) B6408503
theorem B2848223 : Blo 2249435 2848223 := bstep (se 1 (by rfl) ⟨2136167, by rfl⟩ : syracuseStep 2848223 = 4272335) B4272335
theorem B7595261 : Blo 2249435 7595261 := bstep (se 3 (by rfl) ⟨1424111, by rfl⟩ : syracuseStep 7595261 = 2848223) B2848223
theorem B5063507 : Blo 2249435 5063507 := bstep (se 1 (by rfl) ⟨3797630, by rfl⟩ : syracuseStep 5063507 = 7595261) B7595261
theorem B3375671 : Blo 2249435 3375671 := bstep (se 1 (by rfl) ⟨2531753, by rfl⟩ : syracuseStep 3375671 = 5063507) B5063507
theorem B2250447 : Blo 2249435 2250447 := bstep (se 1 (by rfl) ⟨1687835, by rfl⟩ : syracuseStep 2250447 = 3375671) B3375671
theorem B3375677 : Blo 2249435 3375677 := bbase (se 3 (by rfl) ⟨632939, by rfl⟩ : syracuseStep 3375677 = 1265879) (by norm_num)
theorem B2250451 : Blo 2249435 2250451 := bstep (se 1 (by rfl) ⟨1687838, by rfl⟩ : syracuseStep 2250451 = 3375677) B3375677
theorem B5063525 : Blo 2249435 5063525 := bbase (se 4 (by rfl) ⟨474705, by rfl⟩ : syracuseStep 5063525 = 949411) (by norm_num)
theorem B3375683 : Blo 2249435 3375683 := bstep (se 1 (by rfl) ⟨2531762, by rfl⟩ : syracuseStep 3375683 = 5063525) B5063525
theorem B2250455 : Blo 2249435 2250455 := bstep (se 1 (by rfl) ⟨1687841, by rfl⟩ : syracuseStep 2250455 = 3375683) B3375683
theorem B5696477 : Blo 2249435 5696477 := bbase (se 3 (by rfl) ⟨1068089, by rfl⟩ : syracuseStep 5696477 = 2136179) (by norm_num)
theorem B3797651 : Blo 2249435 3797651 := bstep (se 1 (by rfl) ⟨2848238, by rfl⟩ : syracuseStep 3797651 = 5696477) B5696477
theorem B2531767 : Blo 2249435 2531767 := bstep (se 1 (by rfl) ⟨1898825, by rfl⟩ : syracuseStep 2531767 = 3797651) B3797651
theorem B3375689 : Blo 2249435 3375689 := bstep (se 2 (by rfl) ⟨1265883, by rfl⟩ : syracuseStep 3375689 = 2531767) B2531767
theorem B2250459 : Blo 2249435 2250459 := bstep (se 1 (by rfl) ⟨1687844, by rfl⟩ : syracuseStep 2250459 = 3375689) B3375689
theorem B4272365 : Blo 2249435 4272365 := bbase (se 3 (by rfl) ⟨801068, by rfl⟩ : syracuseStep 4272365 = 1602137) (by norm_num)
theorem B11392973 : Blo 2249435 11392973 := bstep (se 3 (by rfl) ⟨2136182, by rfl⟩ : syracuseStep 11392973 = 4272365) B4272365
theorem B7595315 : Blo 2249435 7595315 := bstep (se 1 (by rfl) ⟨5696486, by rfl⟩ : syracuseStep 7595315 = 11392973) B11392973
theorem B5063543 : Blo 2249435 5063543 := bstep (se 1 (by rfl) ⟨3797657, by rfl⟩ : syracuseStep 5063543 = 7595315) B7595315
theorem B3375695 : Blo 2249435 3375695 := bstep (se 1 (by rfl) ⟨2531771, by rfl⟩ : syracuseStep 3375695 = 5063543) B5063543
theorem B2250463 : Blo 2249435 2250463 := bstep (se 1 (by rfl) ⟨1687847, by rfl⟩ : syracuseStep 2250463 = 3375695) B3375695
theorem B3375701 : Blo 2249435 3375701 := bbase (se 8 (by rfl) ⟨19779, by rfl⟩ : syracuseStep 3375701 = 39559) (by norm_num)
theorem B2250467 : Blo 2249435 2250467 := bstep (se 1 (by rfl) ⟨1687850, by rfl⟩ : syracuseStep 2250467 = 3375701) B3375701
theorem B3421765 : Blo 2249435 3421765 := bbase (se 4 (by rfl) ⟨320790, by rfl⟩ : syracuseStep 3421765 = 641581) (by norm_num)
theorem B4562353 : Blo 2249435 4562353 := bstep (se 2 (by rfl) ⟨1710882, by rfl⟩ : syracuseStep 4562353 = 3421765) B3421765
theorem B6083137 : Blo 2249435 6083137 := bstep (se 2 (by rfl) ⟨2281176, by rfl⟩ : syracuseStep 6083137 = 4562353) B4562353
theorem B8110849 : Blo 2249435 8110849 := bstep (se 2 (by rfl) ⟨3041568, by rfl⟩ : syracuseStep 8110849 = 6083137) B6083137
theorem B10814465 : Blo 2249435 10814465 := bstep (se 2 (by rfl) ⟨4055424, by rfl⟩ : syracuseStep 10814465 = 8110849) B8110849
theorem B7209643 : Blo 2249435 7209643 := bstep (se 1 (by rfl) ⟨5407232, by rfl⟩ : syracuseStep 7209643 = 10814465) B10814465
theorem B9612857 : Blo 2249435 9612857 := bstep (se 2 (by rfl) ⟨3604821, by rfl⟩ : syracuseStep 9612857 = 7209643) B7209643
theorem B6408571 : Blo 2249435 6408571 := bstep (se 1 (by rfl) ⟨4806428, by rfl⟩ : syracuseStep 6408571 = 9612857) B9612857
theorem B8544761 : Blo 2249435 8544761 := bstep (se 2 (by rfl) ⟨3204285, by rfl⟩ : syracuseStep 8544761 = 6408571) B6408571
theorem B5696507 : Blo 2249435 5696507 := bstep (se 1 (by rfl) ⟨4272380, by rfl⟩ : syracuseStep 5696507 = 8544761) B8544761
theorem B3797671 : Blo 2249435 3797671 := bstep (se 1 (by rfl) ⟨2848253, by rfl⟩ : syracuseStep 3797671 = 5696507) B5696507
theorem B5063561 : Blo 2249435 5063561 := bstep (se 2 (by rfl) ⟨1898835, by rfl⟩ : syracuseStep 5063561 = 3797671) B3797671
theorem B3375707 : Blo 2249435 3375707 := bstep (se 1 (by rfl) ⟨2531780, by rfl⟩ : syracuseStep 3375707 = 5063561) B5063561
theorem B2250471 : Blo 2249435 2250471 := bstep (se 1 (by rfl) ⟨1687853, by rfl⟩ : syracuseStep 2250471 = 3375707) B3375707
theorem B2531785 : Blo 2249435 2531785 := bbase (se 2 (by rfl) ⟨949419, by rfl⟩ : syracuseStep 2531785 = 1898839) (by norm_num)
theorem B3375713 : Blo 2249435 3375713 := bstep (se 2 (by rfl) ⟨1265892, by rfl⟩ : syracuseStep 3375713 = 2531785) B2531785
theorem B2250475 : Blo 2249435 2250475 := bstep (se 1 (by rfl) ⟨1687856, by rfl⟩ : syracuseStep 2250475 = 3375713) B3375713
theorem B19225781 : Blo 2249435 19225781 := bbase (se 5 (by rfl) ⟨901208, by rfl⟩ : syracuseStep 19225781 = 1802417) (by norm_num)
theorem B12817187 : Blo 2249435 12817187 := bstep (se 1 (by rfl) ⟨9612890, by rfl⟩ : syracuseStep 12817187 = 19225781) B19225781
theorem B8544791 : Blo 2249435 8544791 := bstep (se 1 (by rfl) ⟨6408593, by rfl⟩ : syracuseStep 8544791 = 12817187) B12817187
theorem B5696527 : Blo 2249435 5696527 := bstep (se 1 (by rfl) ⟨4272395, by rfl⟩ : syracuseStep 5696527 = 8544791) B8544791
theorem B7595369 : Blo 2249435 7595369 := bstep (se 2 (by rfl) ⟨2848263, by rfl⟩ : syracuseStep 7595369 = 5696527) B5696527
theorem B5063579 : Blo 2249435 5063579 := bstep (se 1 (by rfl) ⟨3797684, by rfl⟩ : syracuseStep 5063579 = 7595369) B7595369
theorem B3375719 : Blo 2249435 3375719 := bstep (se 1 (by rfl) ⟨2531789, by rfl⟩ : syracuseStep 3375719 = 5063579) B5063579
theorem B2250479 : Blo 2249435 2250479 := bstep (se 1 (by rfl) ⟨1687859, by rfl⟩ : syracuseStep 2250479 = 3375719) B3375719
theorem B3375725 : Blo 2249435 3375725 := bbase (se 3 (by rfl) ⟨632948, by rfl⟩ : syracuseStep 3375725 = 1265897) (by norm_num)
theorem B2250483 : Blo 2249435 2250483 := bstep (se 1 (by rfl) ⟨1687862, by rfl⟩ : syracuseStep 2250483 = 3375725) B3375725
theorem B5063597 : Blo 2249435 5063597 := bbase (se 3 (by rfl) ⟨949424, by rfl⟩ : syracuseStep 5063597 = 1898849) (by norm_num)
theorem B3375731 : Blo 2249435 3375731 := bstep (se 1 (by rfl) ⟨2531798, by rfl⟩ : syracuseStep 3375731 = 5063597) B5063597
theorem B2250487 : Blo 2249435 2250487 := bstep (se 1 (by rfl) ⟨1687865, by rfl⟩ : syracuseStep 2250487 = 3375731) B3375731
theorem B6408629 : Blo 2249435 6408629 := bbase (se 5 (by rfl) ⟨300404, by rfl⟩ : syracuseStep 6408629 = 600809) (by norm_num)
theorem B4272419 : Blo 2249435 4272419 := bstep (se 1 (by rfl) ⟨3204314, by rfl⟩ : syracuseStep 4272419 = 6408629) B6408629
theorem B2848279 : Blo 2249435 2848279 := bstep (se 1 (by rfl) ⟨2136209, by rfl⟩ : syracuseStep 2848279 = 4272419) B4272419
theorem B3797705 : Blo 2249435 3797705 := bstep (se 2 (by rfl) ⟨1424139, by rfl⟩ : syracuseStep 3797705 = 2848279) B2848279
theorem B2531803 : Blo 2249435 2531803 := bstep (se 1 (by rfl) ⟨1898852, by rfl⟩ : syracuseStep 2531803 = 3797705) B3797705
theorem B3375737 : Blo 2249435 3375737 := bstep (se 2 (by rfl) ⟨1265901, by rfl⟩ : syracuseStep 3375737 = 2531803) B2531803
theorem B2250491 : Blo 2249435 2250491 := bstep (se 1 (by rfl) ⟨1687868, by rfl⟩ : syracuseStep 2250491 = 3375737) B3375737
theorem B7308085 : Blo 2249435 7308085 := bbase (se 5 (by rfl) ⟨342566, by rfl⟩ : syracuseStep 7308085 = 685133) (by norm_num)
theorem B9744113 : Blo 2249435 9744113 := bstep (se 2 (by rfl) ⟨3654042, by rfl⟩ : syracuseStep 9744113 = 7308085) B7308085
theorem B6496075 : Blo 2249435 6496075 := bstep (se 1 (by rfl) ⟨4872056, by rfl⟩ : syracuseStep 6496075 = 9744113) B9744113
theorem B8661433 : Blo 2249435 8661433 := bstep (se 2 (by rfl) ⟨3248037, by rfl⟩ : syracuseStep 8661433 = 6496075) B6496075
theorem B11548577 : Blo 2249435 11548577 := bstep (se 2 (by rfl) ⟨4330716, by rfl⟩ : syracuseStep 11548577 = 8661433) B8661433
theorem B7699051 : Blo 2249435 7699051 := bstep (se 1 (by rfl) ⟨5774288, by rfl⟩ : syracuseStep 7699051 = 11548577) B11548577
theorem B10265401 : Blo 2249435 10265401 := bstep (se 2 (by rfl) ⟨3849525, by rfl⟩ : syracuseStep 10265401 = 7699051) B7699051
theorem B13687201 : Blo 2249435 13687201 := bstep (se 2 (by rfl) ⟨5132700, by rfl⟩ : syracuseStep 13687201 = 10265401) B10265401
theorem B72998405 : Blo 2249435 72998405 := bstep (se 4 (by rfl) ⟨6843600, by rfl⟩ : syracuseStep 72998405 = 13687201) B13687201
theorem B48665603 : Blo 2249435 48665603 := bstep (se 1 (by rfl) ⟨36499202, by rfl⟩ : syracuseStep 48665603 = 72998405) B72998405
theorem B32443735 : Blo 2249435 32443735 := bstep (se 1 (by rfl) ⟨24332801, by rfl⟩ : syracuseStep 32443735 = 48665603) B48665603
theorem B43258313 : Blo 2249435 43258313 := bstep (se 2 (by rfl) ⟨16221867, by rfl⟩ : syracuseStep 43258313 = 32443735) B32443735
theorem B28838875 : Blo 2249435 28838875 := bstep (se 1 (by rfl) ⟨21629156, by rfl⟩ : syracuseStep 28838875 = 43258313) B43258313
theorem B38451833 : Blo 2249435 38451833 := bstep (se 2 (by rfl) ⟨14419437, by rfl⟩ : syracuseStep 38451833 = 28838875) B28838875
theorem B25634555 : Blo 2249435 25634555 := bstep (se 1 (by rfl) ⟨19225916, by rfl⟩ : syracuseStep 25634555 = 38451833) B38451833
theorem B17089703 : Blo 2249435 17089703 := bstep (se 1 (by rfl) ⟨12817277, by rfl⟩ : syracuseStep 17089703 = 25634555) B25634555
theorem B11393135 : Blo 2249435 11393135 := bstep (se 1 (by rfl) ⟨8544851, by rfl⟩ : syracuseStep 11393135 = 17089703) B17089703
theorem B7595423 : Blo 2249435 7595423 := bstep (se 1 (by rfl) ⟨5696567, by rfl⟩ : syracuseStep 7595423 = 11393135) B11393135
theorem B5063615 : Blo 2249435 5063615 := bstep (se 1 (by rfl) ⟨3797711, by rfl⟩ : syracuseStep 5063615 = 7595423) B7595423
theorem B3375743 : Blo 2249435 3375743 := bstep (se 1 (by rfl) ⟨2531807, by rfl⟩ : syracuseStep 3375743 = 5063615) B5063615
theorem B2250495 : Blo 2249435 2250495 := bstep (se 1 (by rfl) ⟨1687871, by rfl⟩ : syracuseStep 2250495 = 3375743) B3375743
theorem B3375749 : Blo 2249435 3375749 := bbase (se 4 (by rfl) ⟨316476, by rfl⟩ : syracuseStep 3375749 = 632953) (by norm_num)
theorem B2250499 : Blo 2249435 2250499 := bstep (se 1 (by rfl) ⟨1687874, by rfl⟩ : syracuseStep 2250499 = 3375749) B3375749
theorem B3797725 : Blo 2249435 3797725 := bbase (se 3 (by rfl) ⟨712073, by rfl⟩ : syracuseStep 3797725 = 1424147) (by norm_num)
theorem B5063633 : Blo 2249435 5063633 := bstep (se 2 (by rfl) ⟨1898862, by rfl⟩ : syracuseStep 5063633 = 3797725) B3797725
theorem B3375755 : Blo 2249435 3375755 := bstep (se 1 (by rfl) ⟨2531816, by rfl⟩ : syracuseStep 3375755 = 5063633) B5063633
theorem B2250503 : Blo 2249435 2250503 := bstep (se 1 (by rfl) ⟨1687877, by rfl⟩ : syracuseStep 2250503 = 3375755) B3375755
theorem B2531821 : Blo 2249435 2531821 := bbase (se 3 (by rfl) ⟨474716, by rfl⟩ : syracuseStep 2531821 = 949433) (by norm_num)
theorem B3375761 : Blo 2249435 3375761 := bstep (se 2 (by rfl) ⟨1265910, by rfl⟩ : syracuseStep 3375761 = 2531821) B2531821
theorem B2250507 : Blo 2249435 2250507 := bstep (se 1 (by rfl) ⟨1687880, by rfl⟩ : syracuseStep 2250507 = 3375761) B3375761
theorem B7595477 : Blo 2249435 7595477 := bbase (se 7 (by rfl) ⟨89009, by rfl⟩ : syracuseStep 7595477 = 178019) (by norm_num)
theorem B5063651 : Blo 2249435 5063651 := bstep (se 1 (by rfl) ⟨3797738, by rfl⟩ : syracuseStep 5063651 = 7595477) B7595477
theorem B3375767 : Blo 2249435 3375767 := bstep (se 1 (by rfl) ⟨2531825, by rfl⟩ : syracuseStep 3375767 = 5063651) B5063651
theorem B2250511 : Blo 2249435 2250511 := bstep (se 1 (by rfl) ⟨1687883, by rfl⟩ : syracuseStep 2250511 = 3375767) B3375767
theorem B3375773 : Blo 2249435 3375773 := bbase (se 3 (by rfl) ⟨632957, by rfl⟩ : syracuseStep 3375773 = 1265915) (by norm_num)
theorem B2250515 : Blo 2249435 2250515 := bstep (se 1 (by rfl) ⟨1687886, by rfl⟩ : syracuseStep 2250515 = 3375773) B3375773
theorem B5063669 : Blo 2249435 5063669 := bbase (se 5 (by rfl) ⟨237359, by rfl⟩ : syracuseStep 5063669 = 474719) (by norm_num)
theorem B3375779 : Blo 2249435 3375779 := bstep (se 1 (by rfl) ⟨2531834, by rfl⟩ : syracuseStep 3375779 = 5063669) B5063669
theorem B2250519 : Blo 2249435 2250519 := bstep (se 1 (by rfl) ⟨1687889, by rfl⟩ : syracuseStep 2250519 = 3375779) B3375779
theorem B6250405 : Blo 2249435 6250405 := bbase (se 4 (by rfl) ⟨585975, by rfl⟩ : syracuseStep 6250405 = 1171951) (by norm_num)
theorem B8333873 : Blo 2249435 8333873 := bstep (se 2 (by rfl) ⟨3125202, by rfl⟩ : syracuseStep 8333873 = 6250405) B6250405
theorem B5555915 : Blo 2249435 5555915 := bstep (se 1 (by rfl) ⟨4166936, by rfl⟩ : syracuseStep 5555915 = 8333873) B8333873
theorem B3703943 : Blo 2249435 3703943 := bstep (se 1 (by rfl) ⟨2777957, by rfl⟩ : syracuseStep 3703943 = 5555915) B5555915
theorem B2469295 : Blo 2249435 2469295 := bstep (se 1 (by rfl) ⟨1851971, by rfl⟩ : syracuseStep 2469295 = 3703943) B3703943
theorem B13169573 : Blo 2249435 13169573 := bstep (se 4 (by rfl) ⟨1234647, by rfl⟩ : syracuseStep 13169573 = 2469295) B2469295
theorem B8779715 : Blo 2249435 8779715 := bstep (se 1 (by rfl) ⟨6584786, by rfl⟩ : syracuseStep 8779715 = 13169573) B13169573
theorem B5853143 : Blo 2249435 5853143 := bstep (se 1 (by rfl) ⟨4389857, by rfl⟩ : syracuseStep 5853143 = 8779715) B8779715
theorem B3902095 : Blo 2249435 3902095 := bstep (se 1 (by rfl) ⟨2926571, by rfl⟩ : syracuseStep 3902095 = 5853143) B5853143
theorem B20811173 : Blo 2249435 20811173 := bstep (se 4 (by rfl) ⟨1951047, by rfl⟩ : syracuseStep 20811173 = 3902095) B3902095
theorem B55496461 : Blo 2249435 55496461 := bstep (se 3 (by rfl) ⟨10405586, by rfl⟩ : syracuseStep 55496461 = 20811173) B20811173
theorem B73995281 : Blo 2249435 73995281 := bstep (se 2 (by rfl) ⟨27748230, by rfl⟩ : syracuseStep 73995281 = 55496461) B55496461
theorem B49330187 : Blo 2249435 49330187 := bstep (se 1 (by rfl) ⟨36997640, by rfl⟩ : syracuseStep 49330187 = 73995281) B73995281
theorem B32886791 : Blo 2249435 32886791 := bstep (se 1 (by rfl) ⟨24665093, by rfl⟩ : syracuseStep 32886791 = 49330187) B49330187
theorem B21924527 : Blo 2249435 21924527 := bstep (se 1 (by rfl) ⟨16443395, by rfl⟩ : syracuseStep 21924527 = 32886791) B32886791
theorem B58465405 : Blo 2249435 58465405 := bstep (se 3 (by rfl) ⟨10962263, by rfl⟩ : syracuseStep 58465405 = 21924527) B21924527
theorem B77953873 : Blo 2249435 77953873 := bstep (se 2 (by rfl) ⟨29232702, by rfl⟩ : syracuseStep 77953873 = 58465405) B58465405
theorem B103938497 : Blo 2249435 103938497 := bstep (se 2 (by rfl) ⟨38976936, by rfl⟩ : syracuseStep 103938497 = 77953873) B77953873
theorem B69292331 : Blo 2249435 69292331 := bstep (se 1 (by rfl) ⟨51969248, by rfl⟩ : syracuseStep 69292331 = 103938497) B103938497
theorem B46194887 : Blo 2249435 46194887 := bstep (se 1 (by rfl) ⟨34646165, by rfl⟩ : syracuseStep 46194887 = 69292331) B69292331
theorem B123186365 : Blo 2249435 123186365 := bstep (se 3 (by rfl) ⟨23097443, by rfl⟩ : syracuseStep 123186365 = 46194887) B46194887
theorem B82124243 : Blo 2249435 82124243 := bstep (se 1 (by rfl) ⟨61593182, by rfl⟩ : syracuseStep 82124243 = 123186365) B123186365
theorem B54749495 : Blo 2249435 54749495 := bstep (se 1 (by rfl) ⟨41062121, by rfl⟩ : syracuseStep 54749495 = 82124243) B82124243
theorem B36499663 : Blo 2249435 36499663 := bstep (se 1 (by rfl) ⟨27374747, by rfl⟩ : syracuseStep 36499663 = 54749495) B54749495
theorem B48666217 : Blo 2249435 48666217 := bstep (se 2 (by rfl) ⟨18249831, by rfl⟩ : syracuseStep 48666217 = 36499663) B36499663
theorem B64888289 : Blo 2249435 64888289 := bstep (se 2 (by rfl) ⟨24333108, by rfl⟩ : syracuseStep 64888289 = 48666217) B48666217
theorem B43258859 : Blo 2249435 43258859 := bstep (se 1 (by rfl) ⟨32444144, by rfl⟩ : syracuseStep 43258859 = 64888289) B64888289
theorem B28839239 : Blo 2249435 28839239 := bstep (se 1 (by rfl) ⟨21629429, by rfl⟩ : syracuseStep 28839239 = 43258859) B43258859
theorem B19226159 : Blo 2249435 19226159 := bstep (se 1 (by rfl) ⟨14419619, by rfl⟩ : syracuseStep 19226159 = 28839239) B28839239
theorem B12817439 : Blo 2249435 12817439 := bstep (se 1 (by rfl) ⟨9613079, by rfl⟩ : syracuseStep 12817439 = 19226159) B19226159
theorem B8544959 : Blo 2249435 8544959 := bstep (se 1 (by rfl) ⟨6408719, by rfl⟩ : syracuseStep 8544959 = 12817439) B12817439
theorem B5696639 : Blo 2249435 5696639 := bstep (se 1 (by rfl) ⟨4272479, by rfl⟩ : syracuseStep 5696639 = 8544959) B8544959
theorem B3797759 : Blo 2249435 3797759 := bstep (se 1 (by rfl) ⟨2848319, by rfl⟩ : syracuseStep 3797759 = 5696639) B5696639
theorem B2531839 : Blo 2249435 2531839 := bstep (se 1 (by rfl) ⟨1898879, by rfl⟩ : syracuseStep 2531839 = 3797759) B3797759
theorem B3375785 : Blo 2249435 3375785 := bstep (se 2 (by rfl) ⟨1265919, by rfl⟩ : syracuseStep 3375785 = 2531839) B2531839
theorem B2250523 : Blo 2249435 2250523 := bstep (se 1 (by rfl) ⟨1687892, by rfl⟩ : syracuseStep 2250523 = 3375785) B3375785
theorem B3204365 : Blo 2249435 3204365 := bbase (se 3 (by rfl) ⟨600818, by rfl⟩ : syracuseStep 3204365 = 1201637) (by norm_num)
theorem B8544973 : Blo 2249435 8544973 := bstep (se 3 (by rfl) ⟨1602182, by rfl⟩ : syracuseStep 8544973 = 3204365) B3204365
theorem B11393297 : Blo 2249435 11393297 := bstep (se 2 (by rfl) ⟨4272486, by rfl⟩ : syracuseStep 11393297 = 8544973) B8544973
theorem B7595531 : Blo 2249435 7595531 := bstep (se 1 (by rfl) ⟨5696648, by rfl⟩ : syracuseStep 7595531 = 11393297) B11393297
theorem B5063687 : Blo 2249435 5063687 := bstep (se 1 (by rfl) ⟨3797765, by rfl⟩ : syracuseStep 5063687 = 7595531) B7595531
theorem B3375791 : Blo 2249435 3375791 := bstep (se 1 (by rfl) ⟨2531843, by rfl⟩ : syracuseStep 3375791 = 5063687) B5063687
theorem B2250527 : Blo 2249435 2250527 := bstep (se 1 (by rfl) ⟨1687895, by rfl⟩ : syracuseStep 2250527 = 3375791) B3375791
theorem B3375797 : Blo 2249435 3375797 := bbase (se 5 (by rfl) ⟨158240, by rfl⟩ : syracuseStep 3375797 = 316481) (by norm_num)
theorem B2250531 : Blo 2249435 2250531 := bstep (se 1 (by rfl) ⟨1687898, by rfl⟩ : syracuseStep 2250531 = 3375797) B3375797
theorem B5696669 : Blo 2249435 5696669 := bbase (se 3 (by rfl) ⟨1068125, by rfl⟩ : syracuseStep 5696669 = 2136251) (by norm_num)
theorem B3797779 : Blo 2249435 3797779 := bstep (se 1 (by rfl) ⟨2848334, by rfl⟩ : syracuseStep 3797779 = 5696669) B5696669
theorem B5063705 : Blo 2249435 5063705 := bstep (se 2 (by rfl) ⟨1898889, by rfl⟩ : syracuseStep 5063705 = 3797779) B3797779
theorem B3375803 : Blo 2249435 3375803 := bstep (se 1 (by rfl) ⟨2531852, by rfl⟩ : syracuseStep 3375803 = 5063705) B5063705
theorem B2250535 : Blo 2249435 2250535 := bstep (se 1 (by rfl) ⟨1687901, by rfl⟩ : syracuseStep 2250535 = 3375803) B3375803
theorem B2531857 : Blo 2249435 2531857 := bbase (se 2 (by rfl) ⟨949446, by rfl⟩ : syracuseStep 2531857 = 1898893) (by norm_num)
theorem B3375809 : Blo 2249435 3375809 := bstep (se 2 (by rfl) ⟨1265928, by rfl⟩ : syracuseStep 3375809 = 2531857) B2531857
theorem B2250539 : Blo 2249435 2250539 := bstep (se 1 (by rfl) ⟨1687904, by rfl⟩ : syracuseStep 2250539 = 3375809) B3375809
theorem B4272517 : Blo 2249435 4272517 := bbase (se 4 (by rfl) ⟨400548, by rfl⟩ : syracuseStep 4272517 = 801097) (by norm_num)
theorem B5696689 : Blo 2249435 5696689 := bstep (se 2 (by rfl) ⟨2136258, by rfl⟩ : syracuseStep 5696689 = 4272517) B4272517
theorem B7595585 : Blo 2249435 7595585 := bstep (se 2 (by rfl) ⟨2848344, by rfl⟩ : syracuseStep 7595585 = 5696689) B5696689
theorem B5063723 : Blo 2249435 5063723 := bstep (se 1 (by rfl) ⟨3797792, by rfl⟩ : syracuseStep 5063723 = 7595585) B7595585
theorem B3375815 : Blo 2249435 3375815 := bstep (se 1 (by rfl) ⟨2531861, by rfl⟩ : syracuseStep 3375815 = 5063723) B5063723
theorem B2250543 : Blo 2249435 2250543 := bstep (se 1 (by rfl) ⟨1687907, by rfl⟩ : syracuseStep 2250543 = 3375815) B3375815
theorem B3375821 : Blo 2249435 3375821 := bbase (se 3 (by rfl) ⟨632966, by rfl⟩ : syracuseStep 3375821 = 1265933) (by norm_num)
theorem B2250547 : Blo 2249435 2250547 := bstep (se 1 (by rfl) ⟨1687910, by rfl⟩ : syracuseStep 2250547 = 3375821) B3375821
theorem B5063741 : Blo 2249435 5063741 := bbase (se 3 (by rfl) ⟨949451, by rfl⟩ : syracuseStep 5063741 = 1898903) (by norm_num)
theorem B3375827 : Blo 2249435 3375827 := bstep (se 1 (by rfl) ⟨2531870, by rfl⟩ : syracuseStep 3375827 = 5063741) B5063741
theorem B2250551 : Blo 2249435 2250551 := bstep (se 1 (by rfl) ⟨1687913, by rfl⟩ : syracuseStep 2250551 = 3375827) B3375827
theorem B3797813 : Blo 2249435 3797813 := bbase (se 5 (by rfl) ⟨178022, by rfl⟩ : syracuseStep 3797813 = 356045) (by norm_num)
theorem B2531875 : Blo 2249435 2531875 := bstep (se 1 (by rfl) ⟨1898906, by rfl⟩ : syracuseStep 2531875 = 3797813) B3797813
theorem B3375833 : Blo 2249435 3375833 := bstep (se 2 (by rfl) ⟨1265937, by rfl⟩ : syracuseStep 3375833 = 2531875) B2531875
theorem B2250555 : Blo 2249435 2250555 := bstep (se 1 (by rfl) ⟨1687916, by rfl⟩ : syracuseStep 2250555 = 3375833) B3375833
theorem B6408821 : Blo 2249435 6408821 := bbase (se 5 (by rfl) ⟨300413, by rfl⟩ : syracuseStep 6408821 = 600827) (by norm_num)
theorem B17090189 : Blo 2249435 17090189 := bstep (se 3 (by rfl) ⟨3204410, by rfl⟩ : syracuseStep 17090189 = 6408821) B6408821
theorem B11393459 : Blo 2249435 11393459 := bstep (se 1 (by rfl) ⟨8545094, by rfl⟩ : syracuseStep 11393459 = 17090189) B17090189
theorem B7595639 : Blo 2249435 7595639 := bstep (se 1 (by rfl) ⟨5696729, by rfl⟩ : syracuseStep 7595639 = 11393459) B11393459
theorem B5063759 : Blo 2249435 5063759 := bstep (se 1 (by rfl) ⟨3797819, by rfl⟩ : syracuseStep 5063759 = 7595639) B7595639
theorem B3375839 : Blo 2249435 3375839 := bstep (se 1 (by rfl) ⟨2531879, by rfl⟩ : syracuseStep 3375839 = 5063759) B5063759
theorem B2250559 : Blo 2249435 2250559 := bstep (se 1 (by rfl) ⟨1687919, by rfl⟩ : syracuseStep 2250559 = 3375839) B3375839
theorem B3375845 : Blo 2249435 3375845 := bbase (se 4 (by rfl) ⟨316485, by rfl⟩ : syracuseStep 3375845 = 632971) (by norm_num)
theorem B2250563 : Blo 2249435 2250563 := bstep (se 1 (by rfl) ⟨1687922, by rfl⟩ : syracuseStep 2250563 = 3375845) B3375845
theorem B2403317 : Blo 2249435 2403317 := bbase (se 5 (by rfl) ⟨112655, by rfl⟩ : syracuseStep 2403317 = 225311) (by norm_num)
theorem B6408845 : Blo 2249435 6408845 := bstep (se 3 (by rfl) ⟨1201658, by rfl⟩ : syracuseStep 6408845 = 2403317) B2403317
theorem B4272563 : Blo 2249435 4272563 := bstep (se 1 (by rfl) ⟨3204422, by rfl⟩ : syracuseStep 4272563 = 6408845) B6408845
theorem B2848375 : Blo 2249435 2848375 := bstep (se 1 (by rfl) ⟨2136281, by rfl⟩ : syracuseStep 2848375 = 4272563) B4272563
theorem B3797833 : Blo 2249435 3797833 := bstep (se 2 (by rfl) ⟨1424187, by rfl⟩ : syracuseStep 3797833 = 2848375) B2848375
theorem B5063777 : Blo 2249435 5063777 := bstep (se 2 (by rfl) ⟨1898916, by rfl⟩ : syracuseStep 5063777 = 3797833) B3797833
theorem B3375851 : Blo 2249435 3375851 := bstep (se 1 (by rfl) ⟨2531888, by rfl⟩ : syracuseStep 3375851 = 5063777) B5063777
theorem B2250567 : Blo 2249435 2250567 := bstep (se 1 (by rfl) ⟨1687925, by rfl⟩ : syracuseStep 2250567 = 3375851) B3375851
theorem B2531893 : Blo 2249435 2531893 := bbase (se 5 (by rfl) ⟨118682, by rfl⟩ : syracuseStep 2531893 = 237365) (by norm_num)
theorem B3375857 : Blo 2249435 3375857 := bstep (se 2 (by rfl) ⟨1265946, by rfl⟩ : syracuseStep 3375857 = 2531893) B2531893
theorem B2250571 : Blo 2249435 2250571 := bstep (se 1 (by rfl) ⟨1687928, by rfl⟩ : syracuseStep 2250571 = 3375857) B3375857
theorem B2848385 : Blo 2249435 2848385 := bbase (se 2 (by rfl) ⟨1068144, by rfl⟩ : syracuseStep 2848385 = 2136289) (by norm_num)
theorem B7595693 : Blo 2249435 7595693 := bstep (se 3 (by rfl) ⟨1424192, by rfl⟩ : syracuseStep 7595693 = 2848385) B2848385
theorem B5063795 : Blo 2249435 5063795 := bstep (se 1 (by rfl) ⟨3797846, by rfl⟩ : syracuseStep 5063795 = 7595693) B7595693
theorem B3375863 : Blo 2249435 3375863 := bstep (se 1 (by rfl) ⟨2531897, by rfl⟩ : syracuseStep 3375863 = 5063795) B5063795
theorem B2250575 : Blo 2249435 2250575 := bstep (se 1 (by rfl) ⟨1687931, by rfl⟩ : syracuseStep 2250575 = 3375863) B3375863
theorem B3375869 : Blo 2249435 3375869 := bbase (se 3 (by rfl) ⟨632975, by rfl⟩ : syracuseStep 3375869 = 1265951) (by norm_num)
theorem B2250579 : Blo 2249435 2250579 := bstep (se 1 (by rfl) ⟨1687934, by rfl⟩ : syracuseStep 2250579 = 3375869) B3375869
theorem B5063813 : Blo 2249435 5063813 := bbase (se 4 (by rfl) ⟨474732, by rfl⟩ : syracuseStep 5063813 = 949465) (by norm_num)
theorem B3375875 : Blo 2249435 3375875 := bstep (se 1 (by rfl) ⟨2531906, by rfl⟩ : syracuseStep 3375875 = 5063813) B5063813
theorem B2250583 : Blo 2249435 2250583 := bstep (se 1 (by rfl) ⟨1687937, by rfl⟩ : syracuseStep 2250583 = 3375875) B3375875
theorem B4806677 : Blo 2249435 4806677 := bbase (se 6 (by rfl) ⟨112656, by rfl⟩ : syracuseStep 4806677 = 225313) (by norm_num)
theorem B3204451 : Blo 2249435 3204451 := bstep (se 1 (by rfl) ⟨2403338, by rfl⟩ : syracuseStep 3204451 = 4806677) B4806677
theorem B4272601 : Blo 2249435 4272601 := bstep (se 2 (by rfl) ⟨1602225, by rfl⟩ : syracuseStep 4272601 = 3204451) B3204451
theorem B5696801 : Blo 2249435 5696801 := bstep (se 2 (by rfl) ⟨2136300, by rfl⟩ : syracuseStep 5696801 = 4272601) B4272601
theorem B3797867 : Blo 2249435 3797867 := bstep (se 1 (by rfl) ⟨2848400, by rfl⟩ : syracuseStep 3797867 = 5696801) B5696801
theorem B2531911 : Blo 2249435 2531911 := bstep (se 1 (by rfl) ⟨1898933, by rfl⟩ : syracuseStep 2531911 = 3797867) B3797867
theorem B3375881 : Blo 2249435 3375881 := bstep (se 2 (by rfl) ⟨1265955, by rfl⟩ : syracuseStep 3375881 = 2531911) B2531911
theorem B2250587 : Blo 2249435 2250587 := bstep (se 1 (by rfl) ⟨1687940, by rfl⟩ : syracuseStep 2250587 = 3375881) B3375881
theorem B11393621 : Blo 2249435 11393621 := bbase (se 8 (by rfl) ⟨66759, by rfl⟩ : syracuseStep 11393621 = 133519) (by norm_num)
theorem B7595747 : Blo 2249435 7595747 := bstep (se 1 (by rfl) ⟨5696810, by rfl⟩ : syracuseStep 7595747 = 11393621) B11393621
theorem B5063831 : Blo 2249435 5063831 := bstep (se 1 (by rfl) ⟨3797873, by rfl⟩ : syracuseStep 5063831 = 7595747) B7595747
theorem B3375887 : Blo 2249435 3375887 := bstep (se 1 (by rfl) ⟨2531915, by rfl⟩ : syracuseStep 3375887 = 5063831) B5063831
theorem B2250591 : Blo 2249435 2250591 := bstep (se 1 (by rfl) ⟨1687943, by rfl⟩ : syracuseStep 2250591 = 3375887) B3375887
theorem B3375893 : Blo 2249435 3375893 := bbase (se 6 (by rfl) ⟨79122, by rfl⟩ : syracuseStep 3375893 = 158245) (by norm_num)
theorem B2250595 : Blo 2249435 2250595 := bstep (se 1 (by rfl) ⟨1687946, by rfl⟩ : syracuseStep 2250595 = 3375893) B3375893
theorem B18499445 : Blo 2249435 18499445 := bbase (se 5 (by rfl) ⟨867161, by rfl⟩ : syracuseStep 18499445 = 1734323) (by norm_num)
theorem B12332963 : Blo 2249435 12332963 := bstep (se 1 (by rfl) ⟨9249722, by rfl⟩ : syracuseStep 12332963 = 18499445) B18499445
theorem B32887901 : Blo 2249435 32887901 := bstep (se 3 (by rfl) ⟨6166481, by rfl⟩ : syracuseStep 32887901 = 12332963) B12332963
theorem B87701069 : Blo 2249435 87701069 := bstep (se 3 (by rfl) ⟨16443950, by rfl⟩ : syracuseStep 87701069 = 32887901) B32887901
theorem B58467379 : Blo 2249435 58467379 := bstep (se 1 (by rfl) ⟨43850534, by rfl⟩ : syracuseStep 58467379 = 87701069) B87701069
theorem B77956505 : Blo 2249435 77956505 := bstep (se 2 (by rfl) ⟨29233689, by rfl⟩ : syracuseStep 77956505 = 58467379) B58467379
theorem B51971003 : Blo 2249435 51971003 := bstep (se 1 (by rfl) ⟨38978252, by rfl⟩ : syracuseStep 51971003 = 77956505) B77956505
theorem B34647335 : Blo 2249435 34647335 := bstep (se 1 (by rfl) ⟨25985501, by rfl⟩ : syracuseStep 34647335 = 51971003) B51971003
theorem B23098223 : Blo 2249435 23098223 := bstep (se 1 (by rfl) ⟨17323667, by rfl⟩ : syracuseStep 23098223 = 34647335) B34647335
theorem B61595261 : Blo 2249435 61595261 := bstep (se 3 (by rfl) ⟨11549111, by rfl⟩ : syracuseStep 61595261 = 23098223) B23098223
theorem B41063507 : Blo 2249435 41063507 := bstep (se 1 (by rfl) ⟨30797630, by rfl⟩ : syracuseStep 41063507 = 61595261) B61595261
theorem B27375671 : Blo 2249435 27375671 := bstep (se 1 (by rfl) ⟨20531753, by rfl⟩ : syracuseStep 27375671 = 41063507) B41063507
theorem B18250447 : Blo 2249435 18250447 := bstep (se 1 (by rfl) ⟨13687835, by rfl⟩ : syracuseStep 18250447 = 27375671) B27375671
theorem B24333929 : Blo 2249435 24333929 := bstep (se 2 (by rfl) ⟨9125223, by rfl⟩ : syracuseStep 24333929 = 18250447) B18250447
theorem B16222619 : Blo 2249435 16222619 := bstep (se 1 (by rfl) ⟨12166964, by rfl⟩ : syracuseStep 16222619 = 24333929) B24333929
theorem B43260317 : Blo 2249435 43260317 := bstep (se 3 (by rfl) ⟨8111309, by rfl⟩ : syracuseStep 43260317 = 16222619) B16222619
theorem B28840211 : Blo 2249435 28840211 := bstep (se 1 (by rfl) ⟨21630158, by rfl⟩ : syracuseStep 28840211 = 43260317) B43260317
theorem B19226807 : Blo 2249435 19226807 := bstep (se 1 (by rfl) ⟨14420105, by rfl⟩ : syracuseStep 19226807 = 28840211) B28840211
theorem B12817871 : Blo 2249435 12817871 := bstep (se 1 (by rfl) ⟨9613403, by rfl⟩ : syracuseStep 12817871 = 19226807) B19226807
theorem B8545247 : Blo 2249435 8545247 := bstep (se 1 (by rfl) ⟨6408935, by rfl⟩ : syracuseStep 8545247 = 12817871) B12817871
theorem B5696831 : Blo 2249435 5696831 := bstep (se 1 (by rfl) ⟨4272623, by rfl⟩ : syracuseStep 5696831 = 8545247) B8545247
theorem B3797887 : Blo 2249435 3797887 := bstep (se 1 (by rfl) ⟨2848415, by rfl⟩ : syracuseStep 3797887 = 5696831) B5696831
theorem B5063849 : Blo 2249435 5063849 := bstep (se 2 (by rfl) ⟨1898943, by rfl⟩ : syracuseStep 5063849 = 3797887) B3797887
theorem B3375899 : Blo 2249435 3375899 := bstep (se 1 (by rfl) ⟨2531924, by rfl⟩ : syracuseStep 3375899 = 5063849) B5063849
theorem B2250599 : Blo 2249435 2250599 := bstep (se 1 (by rfl) ⟨1687949, by rfl⟩ : syracuseStep 2250599 = 3375899) B3375899
theorem B2531929 : Blo 2249435 2531929 := bbase (se 2 (by rfl) ⟨949473, by rfl⟩ : syracuseStep 2531929 = 1898947) (by norm_num)
theorem B3375905 : Blo 2249435 3375905 := bstep (se 2 (by rfl) ⟨1265964, by rfl⟩ : syracuseStep 3375905 = 2531929) B2531929
theorem B2250603 : Blo 2249435 2250603 := bstep (se 1 (by rfl) ⟨1687952, by rfl⟩ : syracuseStep 2250603 = 3375905) B3375905
theorem B17323733 : Blo 2249435 17323733 := bbase (se 7 (by rfl) ⟨203012, by rfl⟩ : syracuseStep 17323733 = 406025) (by norm_num)
theorem B11549155 : Blo 2249435 11549155 := bstep (se 1 (by rfl) ⟨8661866, by rfl⟩ : syracuseStep 11549155 = 17323733) B17323733
theorem B15398873 : Blo 2249435 15398873 := bstep (se 2 (by rfl) ⟨5774577, by rfl⟩ : syracuseStep 15398873 = 11549155) B11549155
theorem B10265915 : Blo 2249435 10265915 := bstep (se 1 (by rfl) ⟨7699436, by rfl⟩ : syracuseStep 10265915 = 15398873) B15398873
theorem B6843943 : Blo 2249435 6843943 := bstep (se 1 (by rfl) ⟨5132957, by rfl⟩ : syracuseStep 6843943 = 10265915) B10265915
theorem B36501029 : Blo 2249435 36501029 := bstep (se 4 (by rfl) ⟨3421971, by rfl⟩ : syracuseStep 36501029 = 6843943) B6843943
theorem B24334019 : Blo 2249435 24334019 := bstep (se 1 (by rfl) ⟨18250514, by rfl⟩ : syracuseStep 24334019 = 36501029) B36501029
theorem B16222679 : Blo 2249435 16222679 := bstep (se 1 (by rfl) ⟨12167009, by rfl⟩ : syracuseStep 16222679 = 24334019) B24334019
theorem B10815119 : Blo 2249435 10815119 := bstep (se 1 (by rfl) ⟨8111339, by rfl⟩ : syracuseStep 10815119 = 16222679) B16222679
theorem B7210079 : Blo 2249435 7210079 := bstep (se 1 (by rfl) ⟨5407559, by rfl⟩ : syracuseStep 7210079 = 10815119) B10815119
theorem B4806719 : Blo 2249435 4806719 := bstep (se 1 (by rfl) ⟨3605039, by rfl⟩ : syracuseStep 4806719 = 7210079) B7210079
theorem B3204479 : Blo 2249435 3204479 := bstep (se 1 (by rfl) ⟨2403359, by rfl⟩ : syracuseStep 3204479 = 4806719) B4806719
theorem B8545277 : Blo 2249435 8545277 := bstep (se 3 (by rfl) ⟨1602239, by rfl⟩ : syracuseStep 8545277 = 3204479) B3204479
theorem B5696851 : Blo 2249435 5696851 := bstep (se 1 (by rfl) ⟨4272638, by rfl⟩ : syracuseStep 5696851 = 8545277) B8545277
theorem B7595801 : Blo 2249435 7595801 := bstep (se 2 (by rfl) ⟨2848425, by rfl⟩ : syracuseStep 7595801 = 5696851) B5696851
theorem B5063867 : Blo 2249435 5063867 := bstep (se 1 (by rfl) ⟨3797900, by rfl⟩ : syracuseStep 5063867 = 7595801) B7595801
theorem B3375911 : Blo 2249435 3375911 := bstep (se 1 (by rfl) ⟨2531933, by rfl⟩ : syracuseStep 3375911 = 5063867) B5063867
theorem B2250607 : Blo 2249435 2250607 := bstep (se 1 (by rfl) ⟨1687955, by rfl⟩ : syracuseStep 2250607 = 3375911) B3375911
theorem B3375917 : Blo 2249435 3375917 := bbase (se 3 (by rfl) ⟨632984, by rfl⟩ : syracuseStep 3375917 = 1265969) (by norm_num)
theorem B2250611 : Blo 2249435 2250611 := bstep (se 1 (by rfl) ⟨1687958, by rfl⟩ : syracuseStep 2250611 = 3375917) B3375917
theorem B5063885 : Blo 2249435 5063885 := bbase (se 3 (by rfl) ⟨949478, by rfl⟩ : syracuseStep 5063885 = 1898957) (by norm_num)
theorem B3375923 : Blo 2249435 3375923 := bstep (se 1 (by rfl) ⟨2531942, by rfl⟩ : syracuseStep 3375923 = 5063885) B5063885
theorem B2250615 : Blo 2249435 2250615 := bstep (se 1 (by rfl) ⟨1687961, by rfl⟩ : syracuseStep 2250615 = 3375923) B3375923
theorem B2848441 : Blo 2249435 2848441 := bbase (se 2 (by rfl) ⟨1068165, by rfl⟩ : syracuseStep 2848441 = 2136331) (by norm_num)
theorem B3797921 : Blo 2249435 3797921 := bstep (se 2 (by rfl) ⟨1424220, by rfl⟩ : syracuseStep 3797921 = 2848441) B2848441
theorem B2531947 : Blo 2249435 2531947 := bstep (se 1 (by rfl) ⟨1898960, by rfl⟩ : syracuseStep 2531947 = 3797921) B3797921
theorem B3375929 : Blo 2249435 3375929 := bstep (se 2 (by rfl) ⟨1265973, by rfl⟩ : syracuseStep 3375929 = 2531947) B2531947
theorem B2250619 : Blo 2249435 2250619 := bstep (se 1 (by rfl) ⟨1687964, by rfl⟩ : syracuseStep 2250619 = 3375929) B3375929
theorem B5407597 : Blo 2249435 5407597 := bbase (se 3 (by rfl) ⟨1013924, by rfl⟩ : syracuseStep 5407597 = 2027849) (by norm_num)
theorem B7210129 : Blo 2249435 7210129 := bstep (se 2 (by rfl) ⟨2703798, by rfl⟩ : syracuseStep 7210129 = 5407597) B5407597
theorem B9613505 : Blo 2249435 9613505 := bstep (se 2 (by rfl) ⟨3605064, by rfl⟩ : syracuseStep 9613505 = 7210129) B7210129
theorem B25636013 : Blo 2249435 25636013 := bstep (se 3 (by rfl) ⟨4806752, by rfl⟩ : syracuseStep 25636013 = 9613505) B9613505
theorem B17090675 : Blo 2249435 17090675 := bstep (se 1 (by rfl) ⟨12818006, by rfl⟩ : syracuseStep 17090675 = 25636013) B25636013
theorem B11393783 : Blo 2249435 11393783 := bstep (se 1 (by rfl) ⟨8545337, by rfl⟩ : syracuseStep 11393783 = 17090675) B17090675
theorem B7595855 : Blo 2249435 7595855 := bstep (se 1 (by rfl) ⟨5696891, by rfl⟩ : syracuseStep 7595855 = 11393783) B11393783
theorem B5063903 : Blo 2249435 5063903 := bstep (se 1 (by rfl) ⟨3797927, by rfl⟩ : syracuseStep 5063903 = 7595855) B7595855
theorem B3375935 : Blo 2249435 3375935 := bstep (se 1 (by rfl) ⟨2531951, by rfl⟩ : syracuseStep 3375935 = 5063903) B5063903
theorem B2250623 : Blo 2249435 2250623 := bstep (se 1 (by rfl) ⟨1687967, by rfl⟩ : syracuseStep 2250623 = 3375935) B3375935
theorem B3375941 : Blo 2249435 3375941 := bbase (se 4 (by rfl) ⟨316494, by rfl⟩ : syracuseStep 3375941 = 632989) (by norm_num)
theorem B2250627 : Blo 2249435 2250627 := bstep (se 1 (by rfl) ⟨1687970, by rfl⟩ : syracuseStep 2250627 = 3375941) B3375941
theorem B3797941 : Blo 2249435 3797941 := bbase (se 5 (by rfl) ⟨178028, by rfl⟩ : syracuseStep 3797941 = 356057) (by norm_num)
theorem B5063921 : Blo 2249435 5063921 := bstep (se 2 (by rfl) ⟨1898970, by rfl⟩ : syracuseStep 5063921 = 3797941) B3797941
theorem B3375947 : Blo 2249435 3375947 := bstep (se 1 (by rfl) ⟨2531960, by rfl⟩ : syracuseStep 3375947 = 5063921) B5063921
theorem B2250631 : Blo 2249435 2250631 := bstep (se 1 (by rfl) ⟨1687973, by rfl⟩ : syracuseStep 2250631 = 3375947) B3375947
theorem B2531965 : Blo 2249435 2531965 := bbase (se 3 (by rfl) ⟨474743, by rfl⟩ : syracuseStep 2531965 = 949487) (by norm_num)
theorem B3375953 : Blo 2249435 3375953 := bstep (se 2 (by rfl) ⟨1265982, by rfl⟩ : syracuseStep 3375953 = 2531965) B2531965
theorem B2250635 : Blo 2249435 2250635 := bstep (se 1 (by rfl) ⟨1687976, by rfl⟩ : syracuseStep 2250635 = 3375953) B3375953
theorem B7595909 : Blo 2249435 7595909 := bbase (se 4 (by rfl) ⟨712116, by rfl⟩ : syracuseStep 7595909 = 1424233) (by norm_num)
theorem B5063939 : Blo 2249435 5063939 := bstep (se 1 (by rfl) ⟨3797954, by rfl⟩ : syracuseStep 5063939 = 7595909) B7595909
theorem B3375959 : Blo 2249435 3375959 := bstep (se 1 (by rfl) ⟨2531969, by rfl⟩ : syracuseStep 3375959 = 5063939) B5063939
theorem B2250639 : Blo 2249435 2250639 := bstep (se 1 (by rfl) ⟨1687979, by rfl⟩ : syracuseStep 2250639 = 3375959) B3375959
theorem B3375965 : Blo 2249435 3375965 := bbase (se 3 (by rfl) ⟨632993, by rfl⟩ : syracuseStep 3375965 = 1265987) (by norm_num)
theorem B2250643 : Blo 2249435 2250643 := bstep (se 1 (by rfl) ⟨1687982, by rfl⟩ : syracuseStep 2250643 = 3375965) B3375965
theorem B5063957 : Blo 2249435 5063957 := bbase (se 6 (by rfl) ⟨118686, by rfl⟩ : syracuseStep 5063957 = 237373) (by norm_num)
theorem B3375971 : Blo 2249435 3375971 := bstep (se 1 (by rfl) ⟨2531978, by rfl⟩ : syracuseStep 3375971 = 5063957) B5063957
theorem B2250647 : Blo 2249435 2250647 := bstep (se 1 (by rfl) ⟨1687985, by rfl⟩ : syracuseStep 2250647 = 3375971) B3375971
theorem B8545445 : Blo 2249435 8545445 := bbase (se 4 (by rfl) ⟨801135, by rfl⟩ : syracuseStep 8545445 = 1602271) (by norm_num)
theorem B5696963 : Blo 2249435 5696963 := bstep (se 1 (by rfl) ⟨4272722, by rfl⟩ : syracuseStep 5696963 = 8545445) B8545445
theorem B3797975 : Blo 2249435 3797975 := bstep (se 1 (by rfl) ⟨2848481, by rfl⟩ : syracuseStep 3797975 = 5696963) B5696963
theorem B2531983 : Blo 2249435 2531983 := bstep (se 1 (by rfl) ⟨1898987, by rfl⟩ : syracuseStep 2531983 = 3797975) B3797975
theorem B3375977 : Blo 2249435 3375977 := bstep (se 2 (by rfl) ⟨1265991, by rfl⟩ : syracuseStep 3375977 = 2531983) B2531983
theorem B2250651 : Blo 2249435 2250651 := bstep (se 1 (by rfl) ⟨1687988, by rfl⟩ : syracuseStep 2250651 = 3375977) B3375977
theorem B4806821 : Blo 2249435 4806821 := bbase (se 4 (by rfl) ⟨450639, by rfl⟩ : syracuseStep 4806821 = 901279) (by norm_num)
theorem B12818189 : Blo 2249435 12818189 := bstep (se 3 (by rfl) ⟨2403410, by rfl⟩ : syracuseStep 12818189 = 4806821) B4806821
theorem B8545459 : Blo 2249435 8545459 := bstep (se 1 (by rfl) ⟨6409094, by rfl⟩ : syracuseStep 8545459 = 12818189) B12818189
theorem B11393945 : Blo 2249435 11393945 := bstep (se 2 (by rfl) ⟨4272729, by rfl⟩ : syracuseStep 11393945 = 8545459) B8545459
theorem B7595963 : Blo 2249435 7595963 := bstep (se 1 (by rfl) ⟨5696972, by rfl⟩ : syracuseStep 7595963 = 11393945) B11393945
theorem B5063975 : Blo 2249435 5063975 := bstep (se 1 (by rfl) ⟨3797981, by rfl⟩ : syracuseStep 5063975 = 7595963) B7595963
theorem B3375983 : Blo 2249435 3375983 := bstep (se 1 (by rfl) ⟨2531987, by rfl⟩ : syracuseStep 3375983 = 5063975) B5063975
theorem B2250655 : Blo 2249435 2250655 := bstep (se 1 (by rfl) ⟨1687991, by rfl⟩ : syracuseStep 2250655 = 3375983) B3375983
theorem B3375989 : Blo 2249435 3375989 := bbase (se 5 (by rfl) ⟨158249, by rfl⟩ : syracuseStep 3375989 = 316499) (by norm_num)
theorem B2250659 : Blo 2249435 2250659 := bstep (se 1 (by rfl) ⟨1687994, by rfl⟩ : syracuseStep 2250659 = 3375989) B3375989
theorem B8662085 : Blo 2249435 8662085 := bbase (se 4 (by rfl) ⟨812070, by rfl⟩ : syracuseStep 8662085 = 1624141) (by norm_num)
theorem B5774723 : Blo 2249435 5774723 := bstep (se 1 (by rfl) ⟨4331042, by rfl⟩ : syracuseStep 5774723 = 8662085) B8662085
theorem B3849815 : Blo 2249435 3849815 := bstep (se 1 (by rfl) ⟨2887361, by rfl⟩ : syracuseStep 3849815 = 5774723) B5774723
theorem B10266173 : Blo 2249435 10266173 := bstep (se 3 (by rfl) ⟨1924907, by rfl⟩ : syracuseStep 10266173 = 3849815) B3849815
theorem B6844115 : Blo 2249435 6844115 := bstep (se 1 (by rfl) ⟨5133086, by rfl⟩ : syracuseStep 6844115 = 10266173) B10266173
theorem B4562743 : Blo 2249435 4562743 := bstep (se 1 (by rfl) ⟨3422057, by rfl⟩ : syracuseStep 4562743 = 6844115) B6844115
theorem B6083657 : Blo 2249435 6083657 := bstep (se 2 (by rfl) ⟨2281371, by rfl⟩ : syracuseStep 6083657 = 4562743) B4562743
theorem B4055771 : Blo 2249435 4055771 := bstep (se 1 (by rfl) ⟨3041828, by rfl⟩ : syracuseStep 4055771 = 6083657) B6083657
theorem B10815389 : Blo 2249435 10815389 := bstep (se 3 (by rfl) ⟨2027885, by rfl⟩ : syracuseStep 10815389 = 4055771) B4055771
theorem B7210259 : Blo 2249435 7210259 := bstep (se 1 (by rfl) ⟨5407694, by rfl⟩ : syracuseStep 7210259 = 10815389) B10815389
theorem B4806839 : Blo 2249435 4806839 := bstep (se 1 (by rfl) ⟨3605129, by rfl⟩ : syracuseStep 4806839 = 7210259) B7210259
theorem B3204559 : Blo 2249435 3204559 := bstep (se 1 (by rfl) ⟨2403419, by rfl⟩ : syracuseStep 3204559 = 4806839) B4806839
theorem B4272745 : Blo 2249435 4272745 := bstep (se 2 (by rfl) ⟨1602279, by rfl⟩ : syracuseStep 4272745 = 3204559) B3204559
theorem B5696993 : Blo 2249435 5696993 := bstep (se 2 (by rfl) ⟨2136372, by rfl⟩ : syracuseStep 5696993 = 4272745) B4272745
theorem B3797995 : Blo 2249435 3797995 := bstep (se 1 (by rfl) ⟨2848496, by rfl⟩ : syracuseStep 3797995 = 5696993) B5696993
theorem B5063993 : Blo 2249435 5063993 := bstep (se 2 (by rfl) ⟨1898997, by rfl⟩ : syracuseStep 5063993 = 3797995) B3797995
theorem B3375995 : Blo 2249435 3375995 := bstep (se 1 (by rfl) ⟨2531996, by rfl⟩ : syracuseStep 3375995 = 5063993) B5063993
theorem B2250663 : Blo 2249435 2250663 := bstep (se 1 (by rfl) ⟨1687997, by rfl⟩ : syracuseStep 2250663 = 3375995) B3375995
theorem B2532001 : Blo 2249435 2532001 := bbase (se 2 (by rfl) ⟨949500, by rfl⟩ : syracuseStep 2532001 = 1899001) (by norm_num)
theorem B3376001 : Blo 2249435 3376001 := bstep (se 2 (by rfl) ⟨1266000, by rfl⟩ : syracuseStep 3376001 = 2532001) B2532001
theorem B2250667 : Blo 2249435 2250667 := bstep (se 1 (by rfl) ⟨1688000, by rfl⟩ : syracuseStep 2250667 = 3376001) B3376001
theorem B5697013 : Blo 2249435 5697013 := bbase (se 5 (by rfl) ⟨267047, by rfl⟩ : syracuseStep 5697013 = 534095) (by norm_num)
theorem B7596017 : Blo 2249435 7596017 := bstep (se 2 (by rfl) ⟨2848506, by rfl⟩ : syracuseStep 7596017 = 5697013) B5697013
theorem B5064011 : Blo 2249435 5064011 := bstep (se 1 (by rfl) ⟨3798008, by rfl⟩ : syracuseStep 5064011 = 7596017) B7596017
theorem B3376007 : Blo 2249435 3376007 := bstep (se 1 (by rfl) ⟨2532005, by rfl⟩ : syracuseStep 3376007 = 5064011) B5064011
theorem B2250671 : Blo 2249435 2250671 := bstep (se 1 (by rfl) ⟨1688003, by rfl⟩ : syracuseStep 2250671 = 3376007) B3376007
theorem B3376013 : Blo 2249435 3376013 := bbase (se 3 (by rfl) ⟨633002, by rfl⟩ : syracuseStep 3376013 = 1266005) (by norm_num)
theorem B2250675 : Blo 2249435 2250675 := bstep (se 1 (by rfl) ⟨1688006, by rfl⟩ : syracuseStep 2250675 = 3376013) B3376013
theorem B5064029 : Blo 2249435 5064029 := bbase (se 3 (by rfl) ⟨949505, by rfl⟩ : syracuseStep 5064029 = 1899011) (by norm_num)
theorem B3376019 : Blo 2249435 3376019 := bstep (se 1 (by rfl) ⟨2532014, by rfl⟩ : syracuseStep 3376019 = 5064029) B5064029
theorem B2250679 : Blo 2249435 2250679 := bstep (se 1 (by rfl) ⟨1688009, by rfl⟩ : syracuseStep 2250679 = 3376019) B3376019
theorem B3798029 : Blo 2249435 3798029 := bbase (se 3 (by rfl) ⟨712130, by rfl⟩ : syracuseStep 3798029 = 1424261) (by norm_num)
theorem B2532019 : Blo 2249435 2532019 := bstep (se 1 (by rfl) ⟨1899014, by rfl⟩ : syracuseStep 2532019 = 3798029) B3798029
theorem B3376025 : Blo 2249435 3376025 := bstep (se 2 (by rfl) ⟨1266009, by rfl⟩ : syracuseStep 3376025 = 2532019) B2532019
theorem B2250683 : Blo 2249435 2250683 := bstep (se 1 (by rfl) ⟨1688012, by rfl⟩ : syracuseStep 2250683 = 3376025) B3376025
theorem B3422093 : Blo 2249435 3422093 := bbase (se 3 (by rfl) ⟨641642, by rfl⟩ : syracuseStep 3422093 = 1283285) (by norm_num)
theorem B9125581 : Blo 2249435 9125581 := bstep (se 3 (by rfl) ⟨1711046, by rfl⟩ : syracuseStep 9125581 = 3422093) B3422093
theorem B12167441 : Blo 2249435 12167441 := bstep (se 2 (by rfl) ⟨4562790, by rfl⟩ : syracuseStep 12167441 = 9125581) B9125581
theorem B8111627 : Blo 2249435 8111627 := bstep (se 1 (by rfl) ⟨6083720, by rfl⟩ : syracuseStep 8111627 = 12167441) B12167441
theorem B5407751 : Blo 2249435 5407751 := bstep (se 1 (by rfl) ⟨4055813, by rfl⟩ : syracuseStep 5407751 = 8111627) B8111627
theorem B3605167 : Blo 2249435 3605167 := bstep (se 1 (by rfl) ⟨2703875, by rfl⟩ : syracuseStep 3605167 = 5407751) B5407751
theorem B19227557 : Blo 2249435 19227557 := bstep (se 4 (by rfl) ⟨1802583, by rfl⟩ : syracuseStep 19227557 = 3605167) B3605167
theorem B12818371 : Blo 2249435 12818371 := bstep (se 1 (by rfl) ⟨9613778, by rfl⟩ : syracuseStep 12818371 = 19227557) B19227557
theorem B17091161 : Blo 2249435 17091161 := bstep (se 2 (by rfl) ⟨6409185, by rfl⟩ : syracuseStep 17091161 = 12818371) B12818371
theorem B11394107 : Blo 2249435 11394107 := bstep (se 1 (by rfl) ⟨8545580, by rfl⟩ : syracuseStep 11394107 = 17091161) B17091161
theorem B7596071 : Blo 2249435 7596071 := bstep (se 1 (by rfl) ⟨5697053, by rfl⟩ : syracuseStep 7596071 = 11394107) B11394107
theorem B5064047 : Blo 2249435 5064047 := bstep (se 1 (by rfl) ⟨3798035, by rfl⟩ : syracuseStep 5064047 = 7596071) B7596071
theorem B3376031 : Blo 2249435 3376031 := bstep (se 1 (by rfl) ⟨2532023, by rfl⟩ : syracuseStep 3376031 = 5064047) B5064047
theorem B2250687 : Blo 2249435 2250687 := bstep (se 1 (by rfl) ⟨1688015, by rfl⟩ : syracuseStep 2250687 = 3376031) B3376031
theorem B3376037 : Blo 2249435 3376037 := bbase (se 4 (by rfl) ⟨316503, by rfl⟩ : syracuseStep 3376037 = 633007) (by norm_num)
theorem B2250691 : Blo 2249435 2250691 := bstep (se 1 (by rfl) ⟨1688018, by rfl⟩ : syracuseStep 2250691 = 3376037) B3376037
theorem B2848537 : Blo 2249435 2848537 := bbase (se 2 (by rfl) ⟨1068201, by rfl⟩ : syracuseStep 2848537 = 2136403) (by norm_num)
theorem B3798049 : Blo 2249435 3798049 := bstep (se 2 (by rfl) ⟨1424268, by rfl⟩ : syracuseStep 3798049 = 2848537) B2848537
theorem B5064065 : Blo 2249435 5064065 := bstep (se 2 (by rfl) ⟨1899024, by rfl⟩ : syracuseStep 5064065 = 3798049) B3798049
theorem B3376043 : Blo 2249435 3376043 := bstep (se 1 (by rfl) ⟨2532032, by rfl⟩ : syracuseStep 3376043 = 5064065) B5064065
theorem B2250695 : Blo 2249435 2250695 := bstep (se 1 (by rfl) ⟨1688021, by rfl⟩ : syracuseStep 2250695 = 3376043) B3376043
theorem B2532037 : Blo 2249435 2532037 := bbase (se 4 (by rfl) ⟨237378, by rfl⟩ : syracuseStep 2532037 = 474757) (by norm_num)
theorem B3376049 : Blo 2249435 3376049 := bstep (se 2 (by rfl) ⟨1266018, by rfl⟩ : syracuseStep 3376049 = 2532037) B2532037
theorem B2250699 : Blo 2249435 2250699 := bstep (se 1 (by rfl) ⟨1688024, by rfl⟩ : syracuseStep 2250699 = 3376049) B3376049
theorem B4272821 : Blo 2249435 4272821 := bbase (se 5 (by rfl) ⟨200288, by rfl⟩ : syracuseStep 4272821 = 400577) (by norm_num)
theorem B2848547 : Blo 2249435 2848547 := bstep (se 1 (by rfl) ⟨2136410, by rfl⟩ : syracuseStep 2848547 = 4272821) B4272821
theorem B7596125 : Blo 2249435 7596125 := bstep (se 3 (by rfl) ⟨1424273, by rfl⟩ : syracuseStep 7596125 = 2848547) B2848547
theorem B5064083 : Blo 2249435 5064083 := bstep (se 1 (by rfl) ⟨3798062, by rfl⟩ : syracuseStep 5064083 = 7596125) B7596125
theorem B3376055 : Blo 2249435 3376055 := bstep (se 1 (by rfl) ⟨2532041, by rfl⟩ : syracuseStep 3376055 = 5064083) B5064083
theorem B2250703 : Blo 2249435 2250703 := bstep (se 1 (by rfl) ⟨1688027, by rfl⟩ : syracuseStep 2250703 = 3376055) B3376055
theorem B3376061 : Blo 2249435 3376061 := bbase (se 3 (by rfl) ⟨633011, by rfl⟩ : syracuseStep 3376061 = 1266023) (by norm_num)
theorem B2250707 : Blo 2249435 2250707 := bstep (se 1 (by rfl) ⟨1688030, by rfl⟩ : syracuseStep 2250707 = 3376061) B3376061
theorem B5064101 : Blo 2249435 5064101 := bbase (se 4 (by rfl) ⟨474759, by rfl⟩ : syracuseStep 5064101 = 949519) (by norm_num)
theorem B3376067 : Blo 2249435 3376067 := bstep (se 1 (by rfl) ⟨2532050, by rfl⟩ : syracuseStep 3376067 = 5064101) B5064101
theorem B2250711 : Blo 2249435 2250711 := bstep (se 1 (by rfl) ⟨1688033, by rfl⟩ : syracuseStep 2250711 = 3376067) B3376067
theorem B5697125 : Blo 2249435 5697125 := bbase (se 4 (by rfl) ⟨534105, by rfl⟩ : syracuseStep 5697125 = 1068211) (by norm_num)
theorem B3798083 : Blo 2249435 3798083 := bstep (se 1 (by rfl) ⟨2848562, by rfl⟩ : syracuseStep 3798083 = 5697125) B5697125
theorem B2532055 : Blo 2249435 2532055 := bstep (se 1 (by rfl) ⟨1899041, by rfl⟩ : syracuseStep 2532055 = 3798083) B3798083
theorem B3376073 : Blo 2249435 3376073 := bstep (se 2 (by rfl) ⟨1266027, by rfl⟩ : syracuseStep 3376073 = 2532055) B2532055
theorem B2250715 : Blo 2249435 2250715 := bstep (se 1 (by rfl) ⟨1688036, by rfl⟩ : syracuseStep 2250715 = 3376073) B3376073
theorem B5407829 : Blo 2249435 5407829 := bbase (se 8 (by rfl) ⟨31686, by rfl⟩ : syracuseStep 5407829 = 63373) (by norm_num)
theorem B3605219 : Blo 2249435 3605219 := bstep (se 1 (by rfl) ⟨2703914, by rfl⟩ : syracuseStep 3605219 = 5407829) B5407829
theorem B2403479 : Blo 2249435 2403479 := bstep (se 1 (by rfl) ⟨1802609, by rfl⟩ : syracuseStep 2403479 = 3605219) B3605219
theorem B6409277 : Blo 2249435 6409277 := bstep (se 3 (by rfl) ⟨1201739, by rfl⟩ : syracuseStep 6409277 = 2403479) B2403479
theorem B4272851 : Blo 2249435 4272851 := bstep (se 1 (by rfl) ⟨3204638, by rfl⟩ : syracuseStep 4272851 = 6409277) B6409277
theorem B11394269 : Blo 2249435 11394269 := bstep (se 3 (by rfl) ⟨2136425, by rfl⟩ : syracuseStep 11394269 = 4272851) B4272851
theorem B7596179 : Blo 2249435 7596179 := bstep (se 1 (by rfl) ⟨5697134, by rfl⟩ : syracuseStep 7596179 = 11394269) B11394269
theorem B5064119 : Blo 2249435 5064119 := bstep (se 1 (by rfl) ⟨3798089, by rfl⟩ : syracuseStep 5064119 = 7596179) B7596179
theorem B3376079 : Blo 2249435 3376079 := bstep (se 1 (by rfl) ⟨2532059, by rfl⟩ : syracuseStep 3376079 = 5064119) B5064119
theorem B2250719 : Blo 2249435 2250719 := bstep (se 1 (by rfl) ⟨1688039, by rfl⟩ : syracuseStep 2250719 = 3376079) B3376079
theorem B3376085 : Blo 2249435 3376085 := bbase (se 7 (by rfl) ⟨39563, by rfl⟩ : syracuseStep 3376085 = 79127) (by norm_num)
theorem B2250723 : Blo 2249435 2250723 := bstep (se 1 (by rfl) ⟨1688042, by rfl⟩ : syracuseStep 2250723 = 3376085) B3376085
theorem B8545733 : Blo 2249435 8545733 := bbase (se 4 (by rfl) ⟨801162, by rfl⟩ : syracuseStep 8545733 = 1602325) (by norm_num)
theorem B5697155 : Blo 2249435 5697155 := bstep (se 1 (by rfl) ⟨4272866, by rfl⟩ : syracuseStep 5697155 = 8545733) B8545733
theorem B3798103 : Blo 2249435 3798103 := bstep (se 1 (by rfl) ⟨2848577, by rfl⟩ : syracuseStep 3798103 = 5697155) B5697155
theorem B5064137 : Blo 2249435 5064137 := bstep (se 2 (by rfl) ⟨1899051, by rfl⟩ : syracuseStep 5064137 = 3798103) B3798103
theorem B3376091 : Blo 2249435 3376091 := bstep (se 1 (by rfl) ⟨2532068, by rfl⟩ : syracuseStep 3376091 = 5064137) B5064137
theorem B2250727 : Blo 2249435 2250727 := bstep (se 1 (by rfl) ⟨1688045, by rfl⟩ : syracuseStep 2250727 = 3376091) B3376091
theorem B2532073 : Blo 2249435 2532073 := bbase (se 2 (by rfl) ⟨949527, by rfl⟩ : syracuseStep 2532073 = 1899055) (by norm_num)
theorem B3376097 : Blo 2249435 3376097 := bstep (se 2 (by rfl) ⟨1266036, by rfl⟩ : syracuseStep 3376097 = 2532073) B2532073
theorem B2250731 : Blo 2249435 2250731 := bstep (se 1 (by rfl) ⟨1688048, by rfl⟩ : syracuseStep 2250731 = 3376097) B3376097
theorem B12818645 : Blo 2249435 12818645 := bbase (se 7 (by rfl) ⟨150218, by rfl⟩ : syracuseStep 12818645 = 300437) (by norm_num)
theorem B8545763 : Blo 2249435 8545763 := bstep (se 1 (by rfl) ⟨6409322, by rfl⟩ : syracuseStep 8545763 = 12818645) B12818645
theorem B5697175 : Blo 2249435 5697175 := bstep (se 1 (by rfl) ⟨4272881, by rfl⟩ : syracuseStep 5697175 = 8545763) B8545763
theorem B7596233 : Blo 2249435 7596233 := bstep (se 2 (by rfl) ⟨2848587, by rfl⟩ : syracuseStep 7596233 = 5697175) B5697175
theorem B5064155 : Blo 2249435 5064155 := bstep (se 1 (by rfl) ⟨3798116, by rfl⟩ : syracuseStep 5064155 = 7596233) B7596233
theorem B3376103 : Blo 2249435 3376103 := bstep (se 1 (by rfl) ⟨2532077, by rfl⟩ : syracuseStep 3376103 = 5064155) B5064155
theorem B2250735 : Blo 2249435 2250735 := bstep (se 1 (by rfl) ⟨1688051, by rfl⟩ : syracuseStep 2250735 = 3376103) B3376103
theorem B3376109 : Blo 2249435 3376109 := bbase (se 3 (by rfl) ⟨633020, by rfl⟩ : syracuseStep 3376109 = 1266041) (by norm_num)
theorem B2250739 : Blo 2249435 2250739 := bstep (se 1 (by rfl) ⟨1688054, by rfl⟩ : syracuseStep 2250739 = 3376109) B3376109
theorem B5064173 : Blo 2249435 5064173 := bbase (se 3 (by rfl) ⟨949532, by rfl⟩ : syracuseStep 5064173 = 1899065) (by norm_num)
theorem B3376115 : Blo 2249435 3376115 := bstep (se 1 (by rfl) ⟨2532086, by rfl⟩ : syracuseStep 3376115 = 5064173) B5064173
theorem B2250743 : Blo 2249435 2250743 := bstep (se 1 (by rfl) ⟨1688057, by rfl⟩ : syracuseStep 2250743 = 3376115) B3376115
theorem B2281457 : Blo 2249435 2281457 := bbase (se 2 (by rfl) ⟨855546, by rfl⟩ : syracuseStep 2281457 = 1711093) (by norm_num)
theorem B6083885 : Blo 2249435 6083885 := bstep (se 3 (by rfl) ⟨1140728, by rfl⟩ : syracuseStep 6083885 = 2281457) B2281457
theorem B4055923 : Blo 2249435 4055923 := bstep (se 1 (by rfl) ⟨3041942, by rfl⟩ : syracuseStep 4055923 = 6083885) B6083885
theorem B5407897 : Blo 2249435 5407897 := bstep (se 2 (by rfl) ⟨2027961, by rfl⟩ : syracuseStep 5407897 = 4055923) B4055923
theorem B7210529 : Blo 2249435 7210529 := bstep (se 2 (by rfl) ⟨2703948, by rfl⟩ : syracuseStep 7210529 = 5407897) B5407897
theorem B4807019 : Blo 2249435 4807019 := bstep (se 1 (by rfl) ⟨3605264, by rfl⟩ : syracuseStep 4807019 = 7210529) B7210529
theorem B3204679 : Blo 2249435 3204679 := bstep (se 1 (by rfl) ⟨2403509, by rfl⟩ : syracuseStep 3204679 = 4807019) B4807019
theorem B4272905 : Blo 2249435 4272905 := bstep (se 2 (by rfl) ⟨1602339, by rfl⟩ : syracuseStep 4272905 = 3204679) B3204679
theorem B2848603 : Blo 2249435 2848603 := bstep (se 1 (by rfl) ⟨2136452, by rfl⟩ : syracuseStep 2848603 = 4272905) B4272905
theorem B3798137 : Blo 2249435 3798137 := bstep (se 2 (by rfl) ⟨1424301, by rfl⟩ : syracuseStep 3798137 = 2848603) B2848603
theorem B2532091 : Blo 2249435 2532091 := bstep (se 1 (by rfl) ⟨1899068, by rfl⟩ : syracuseStep 2532091 = 3798137) B3798137
theorem B3376121 : Blo 2249435 3376121 := bstep (se 2 (by rfl) ⟨1266045, by rfl⟩ : syracuseStep 3376121 = 2532091) B2532091
theorem B2250747 : Blo 2249435 2250747 := bstep (se 1 (by rfl) ⟨1688060, by rfl⟩ : syracuseStep 2250747 = 3376121) B3376121
theorem B7308917 : Blo 2249435 7308917 := bbase (se 5 (by rfl) ⟨342605, by rfl⟩ : syracuseStep 7308917 = 685211) (by norm_num)
theorem B4872611 : Blo 2249435 4872611 := bstep (se 1 (by rfl) ⟨3654458, by rfl⟩ : syracuseStep 4872611 = 7308917) B7308917
theorem B3248407 : Blo 2249435 3248407 := bstep (se 1 (by rfl) ⟨2436305, by rfl⟩ : syracuseStep 3248407 = 4872611) B4872611
theorem B17324837 : Blo 2249435 17324837 := bstep (se 4 (by rfl) ⟨1624203, by rfl⟩ : syracuseStep 17324837 = 3248407) B3248407
theorem B11549891 : Blo 2249435 11549891 := bstep (se 1 (by rfl) ⟨8662418, by rfl⟩ : syracuseStep 11549891 = 17324837) B17324837
theorem B7699927 : Blo 2249435 7699927 := bstep (se 1 (by rfl) ⟨5774945, by rfl⟩ : syracuseStep 7699927 = 11549891) B11549891
theorem B10266569 : Blo 2249435 10266569 := bstep (se 2 (by rfl) ⟨3849963, by rfl⟩ : syracuseStep 10266569 = 7699927) B7699927
theorem B6844379 : Blo 2249435 6844379 := bstep (se 1 (by rfl) ⟨5133284, by rfl⟩ : syracuseStep 6844379 = 10266569) B10266569
theorem B18251677 : Blo 2249435 18251677 := bstep (se 3 (by rfl) ⟨3422189, by rfl⟩ : syracuseStep 18251677 = 6844379) B6844379
theorem B24335569 : Blo 2249435 24335569 := bstep (se 2 (by rfl) ⟨9125838, by rfl⟩ : syracuseStep 24335569 = 18251677) B18251677
theorem B129789701 : Blo 2249435 129789701 := bstep (se 4 (by rfl) ⟨12167784, by rfl⟩ : syracuseStep 129789701 = 24335569) B24335569
theorem B86526467 : Blo 2249435 86526467 := bstep (se 1 (by rfl) ⟨64894850, by rfl⟩ : syracuseStep 86526467 = 129789701) B129789701
theorem B57684311 : Blo 2249435 57684311 := bstep (se 1 (by rfl) ⟨43263233, by rfl⟩ : syracuseStep 57684311 = 86526467) B86526467
theorem B38456207 : Blo 2249435 38456207 := bstep (se 1 (by rfl) ⟨28842155, by rfl⟩ : syracuseStep 38456207 = 57684311) B57684311
theorem B25637471 : Blo 2249435 25637471 := bstep (se 1 (by rfl) ⟨19228103, by rfl⟩ : syracuseStep 25637471 = 38456207) B38456207
theorem B17091647 : Blo 2249435 17091647 := bstep (se 1 (by rfl) ⟨12818735, by rfl⟩ : syracuseStep 17091647 = 25637471) B25637471
theorem B11394431 : Blo 2249435 11394431 := bstep (se 1 (by rfl) ⟨8545823, by rfl⟩ : syracuseStep 11394431 = 17091647) B17091647
theorem B7596287 : Blo 2249435 7596287 := bstep (se 1 (by rfl) ⟨5697215, by rfl⟩ : syracuseStep 7596287 = 11394431) B11394431
theorem B5064191 : Blo 2249435 5064191 := bstep (se 1 (by rfl) ⟨3798143, by rfl⟩ : syracuseStep 5064191 = 7596287) B7596287
theorem B3376127 : Blo 2249435 3376127 := bstep (se 1 (by rfl) ⟨2532095, by rfl⟩ : syracuseStep 3376127 = 5064191) B5064191
theorem B2250751 : Blo 2249435 2250751 := bstep (se 1 (by rfl) ⟨1688063, by rfl⟩ : syracuseStep 2250751 = 3376127) B3376127
theorem B3376133 : Blo 2249435 3376133 := bbase (se 4 (by rfl) ⟨316512, by rfl⟩ : syracuseStep 3376133 = 633025) (by norm_num)
theorem B2250755 : Blo 2249435 2250755 := bstep (se 1 (by rfl) ⟨1688066, by rfl⟩ : syracuseStep 2250755 = 3376133) B3376133
theorem B3798157 : Blo 2249435 3798157 := bbase (se 3 (by rfl) ⟨712154, by rfl⟩ : syracuseStep 3798157 = 1424309) (by norm_num)
theorem B5064209 : Blo 2249435 5064209 := bstep (se 2 (by rfl) ⟨1899078, by rfl⟩ : syracuseStep 5064209 = 3798157) B3798157
theorem B3376139 : Blo 2249435 3376139 := bstep (se 1 (by rfl) ⟨2532104, by rfl⟩ : syracuseStep 3376139 = 5064209) B5064209
theorem B2250759 : Blo 2249435 2250759 := bstep (se 1 (by rfl) ⟨1688069, by rfl⟩ : syracuseStep 2250759 = 3376139) B3376139
theorem B2532109 : Blo 2249435 2532109 := bbase (se 3 (by rfl) ⟨474770, by rfl⟩ : syracuseStep 2532109 = 949541) (by norm_num)
theorem B3376145 : Blo 2249435 3376145 := bstep (se 2 (by rfl) ⟨1266054, by rfl⟩ : syracuseStep 3376145 = 2532109) B2532109
theorem B2250763 : Blo 2249435 2250763 := bstep (se 1 (by rfl) ⟨1688072, by rfl⟩ : syracuseStep 2250763 = 3376145) B3376145
theorem B7596341 : Blo 2249435 7596341 := bbase (se 5 (by rfl) ⟨356078, by rfl⟩ : syracuseStep 7596341 = 712157) (by norm_num)
theorem B5064227 : Blo 2249435 5064227 := bstep (se 1 (by rfl) ⟨3798170, by rfl⟩ : syracuseStep 5064227 = 7596341) B7596341
theorem B3376151 : Blo 2249435 3376151 := bstep (se 1 (by rfl) ⟨2532113, by rfl⟩ : syracuseStep 3376151 = 5064227) B5064227
theorem B2250767 : Blo 2249435 2250767 := bstep (se 1 (by rfl) ⟨1688075, by rfl⟩ : syracuseStep 2250767 = 3376151) B3376151
theorem B3376157 : Blo 2249435 3376157 := bbase (se 3 (by rfl) ⟨633029, by rfl⟩ : syracuseStep 3376157 = 1266059) (by norm_num)
theorem B2250771 : Blo 2249435 2250771 := bstep (se 1 (by rfl) ⟨1688078, by rfl⟩ : syracuseStep 2250771 = 3376157) B3376157
theorem B5064245 : Blo 2249435 5064245 := bbase (se 5 (by rfl) ⟨237386, by rfl⟩ : syracuseStep 5064245 = 474773) (by norm_num)
theorem B3376163 : Blo 2249435 3376163 := bstep (se 1 (by rfl) ⟨2532122, by rfl⟩ : syracuseStep 3376163 = 5064245) B5064245
theorem B2250775 : Blo 2249435 2250775 := bstep (se 1 (by rfl) ⟨1688081, by rfl⟩ : syracuseStep 2250775 = 3376163) B3376163
theorem B5407973 : Blo 2249435 5407973 := bbase (se 4 (by rfl) ⟨506997, by rfl⟩ : syracuseStep 5407973 = 1013995) (by norm_num)
theorem B3605315 : Blo 2249435 3605315 := bstep (se 1 (by rfl) ⟨2703986, by rfl⟩ : syracuseStep 3605315 = 5407973) B5407973
theorem B9614173 : Blo 2249435 9614173 := bstep (se 3 (by rfl) ⟨1802657, by rfl⟩ : syracuseStep 9614173 = 3605315) B3605315
theorem B12818897 : Blo 2249435 12818897 := bstep (se 2 (by rfl) ⟨4807086, by rfl⟩ : syracuseStep 12818897 = 9614173) B9614173
theorem B8545931 : Blo 2249435 8545931 := bstep (se 1 (by rfl) ⟨6409448, by rfl⟩ : syracuseStep 8545931 = 12818897) B12818897
theorem B5697287 : Blo 2249435 5697287 := bstep (se 1 (by rfl) ⟨4272965, by rfl⟩ : syracuseStep 5697287 = 8545931) B8545931
theorem B3798191 : Blo 2249435 3798191 := bstep (se 1 (by rfl) ⟨2848643, by rfl⟩ : syracuseStep 3798191 = 5697287) B5697287
theorem B2532127 : Blo 2249435 2532127 := bstep (se 1 (by rfl) ⟨1899095, by rfl⟩ : syracuseStep 2532127 = 3798191) B3798191
theorem B3376169 : Blo 2249435 3376169 := bstep (se 2 (by rfl) ⟨1266063, by rfl⟩ : syracuseStep 3376169 = 2532127) B2532127
theorem B2250779 : Blo 2249435 2250779 := bstep (se 1 (by rfl) ⟨1688084, by rfl⟩ : syracuseStep 2250779 = 3376169) B3376169
theorem B2281493 : Blo 2249435 2281493 := bbase (se 6 (by rfl) ⟨53472, by rfl⟩ : syracuseStep 2281493 = 106945) (by norm_num)
theorem B6083981 : Blo 2249435 6083981 := bstep (se 3 (by rfl) ⟨1140746, by rfl⟩ : syracuseStep 6083981 = 2281493) B2281493
theorem B4055987 : Blo 2249435 4055987 := bstep (se 1 (by rfl) ⟨3041990, by rfl⟩ : syracuseStep 4055987 = 6083981) B6083981
theorem B2703991 : Blo 2249435 2703991 := bstep (se 1 (by rfl) ⟨2027993, by rfl⟩ : syracuseStep 2703991 = 4055987) B4055987
theorem B3605321 : Blo 2249435 3605321 := bstep (se 2 (by rfl) ⟨1351995, by rfl⟩ : syracuseStep 3605321 = 2703991) B2703991
theorem B9614189 : Blo 2249435 9614189 := bstep (se 3 (by rfl) ⟨1802660, by rfl⟩ : syracuseStep 9614189 = 3605321) B3605321
theorem B6409459 : Blo 2249435 6409459 := bstep (se 1 (by rfl) ⟨4807094, by rfl⟩ : syracuseStep 6409459 = 9614189) B9614189
theorem B8545945 : Blo 2249435 8545945 := bstep (se 2 (by rfl) ⟨3204729, by rfl⟩ : syracuseStep 8545945 = 6409459) B6409459
theorem B11394593 : Blo 2249435 11394593 := bstep (se 2 (by rfl) ⟨4272972, by rfl⟩ : syracuseStep 11394593 = 8545945) B8545945
theorem B7596395 : Blo 2249435 7596395 := bstep (se 1 (by rfl) ⟨5697296, by rfl⟩ : syracuseStep 7596395 = 11394593) B11394593
theorem B5064263 : Blo 2249435 5064263 := bstep (se 1 (by rfl) ⟨3798197, by rfl⟩ : syracuseStep 5064263 = 7596395) B7596395
theorem B3376175 : Blo 2249435 3376175 := bstep (se 1 (by rfl) ⟨2532131, by rfl⟩ : syracuseStep 3376175 = 5064263) B5064263
theorem B2250783 : Blo 2249435 2250783 := bstep (se 1 (by rfl) ⟨1688087, by rfl⟩ : syracuseStep 2250783 = 3376175) B3376175
theorem B3376181 : Blo 2249435 3376181 := bbase (se 5 (by rfl) ⟨158258, by rfl⟩ : syracuseStep 3376181 = 316517) (by norm_num)
theorem B2250787 : Blo 2249435 2250787 := bstep (se 1 (by rfl) ⟨1688090, by rfl⟩ : syracuseStep 2250787 = 3376181) B3376181
theorem B5697317 : Blo 2249435 5697317 := bbase (se 4 (by rfl) ⟨534123, by rfl⟩ : syracuseStep 5697317 = 1068247) (by norm_num)
theorem B3798211 : Blo 2249435 3798211 := bstep (se 1 (by rfl) ⟨2848658, by rfl⟩ : syracuseStep 3798211 = 5697317) B5697317
theorem B5064281 : Blo 2249435 5064281 := bstep (se 2 (by rfl) ⟨1899105, by rfl⟩ : syracuseStep 5064281 = 3798211) B3798211
theorem B3376187 : Blo 2249435 3376187 := bstep (se 1 (by rfl) ⟨2532140, by rfl⟩ : syracuseStep 3376187 = 5064281) B5064281
theorem B2250791 : Blo 2249435 2250791 := bstep (se 1 (by rfl) ⟨1688093, by rfl⟩ : syracuseStep 2250791 = 3376187) B3376187
theorem B2532145 : Blo 2249435 2532145 := bbase (se 2 (by rfl) ⟨949554, by rfl⟩ : syracuseStep 2532145 = 1899109) (by norm_num)
theorem B3376193 : Blo 2249435 3376193 := bstep (se 2 (by rfl) ⟨1266072, by rfl⟩ : syracuseStep 3376193 = 2532145) B2532145
theorem B2250795 : Blo 2249435 2250795 := bstep (se 1 (by rfl) ⟨1688096, by rfl⟩ : syracuseStep 2250795 = 3376193) B3376193
theorem B5408021 : Blo 2249435 5408021 := bbase (se 6 (by rfl) ⟨126750, by rfl⟩ : syracuseStep 5408021 = 253501) (by norm_num)
theorem B3605347 : Blo 2249435 3605347 := bstep (se 1 (by rfl) ⟨2704010, by rfl⟩ : syracuseStep 3605347 = 5408021) B5408021
theorem B4807129 : Blo 2249435 4807129 := bstep (se 2 (by rfl) ⟨1802673, by rfl⟩ : syracuseStep 4807129 = 3605347) B3605347
theorem B6409505 : Blo 2249435 6409505 := bstep (se 2 (by rfl) ⟨2403564, by rfl⟩ : syracuseStep 6409505 = 4807129) B4807129
theorem B4273003 : Blo 2249435 4273003 := bstep (se 1 (by rfl) ⟨3204752, by rfl⟩ : syracuseStep 4273003 = 6409505) B6409505
theorem B5697337 : Blo 2249435 5697337 := bstep (se 2 (by rfl) ⟨2136501, by rfl⟩ : syracuseStep 5697337 = 4273003) B4273003
theorem B7596449 : Blo 2249435 7596449 := bstep (se 2 (by rfl) ⟨2848668, by rfl⟩ : syracuseStep 7596449 = 5697337) B5697337
theorem B5064299 : Blo 2249435 5064299 := bstep (se 1 (by rfl) ⟨3798224, by rfl⟩ : syracuseStep 5064299 = 7596449) B7596449
theorem B3376199 : Blo 2249435 3376199 := bstep (se 1 (by rfl) ⟨2532149, by rfl⟩ : syracuseStep 3376199 = 5064299) B5064299
theorem B2250799 : Blo 2249435 2250799 := bstep (se 1 (by rfl) ⟨1688099, by rfl⟩ : syracuseStep 2250799 = 3376199) B3376199
theorem B3376205 : Blo 2249435 3376205 := bbase (se 3 (by rfl) ⟨633038, by rfl⟩ : syracuseStep 3376205 = 1266077) (by norm_num)
theorem B2250803 : Blo 2249435 2250803 := bstep (se 1 (by rfl) ⟨1688102, by rfl⟩ : syracuseStep 2250803 = 3376205) B3376205
theorem B5064317 : Blo 2249435 5064317 := bbase (se 3 (by rfl) ⟨949559, by rfl⟩ : syracuseStep 5064317 = 1899119) (by norm_num)
theorem B3376211 : Blo 2249435 3376211 := bstep (se 1 (by rfl) ⟨2532158, by rfl⟩ : syracuseStep 3376211 = 5064317) B5064317
theorem B2250807 : Blo 2249435 2250807 := bstep (se 1 (by rfl) ⟨1688105, by rfl⟩ : syracuseStep 2250807 = 3376211) B3376211
theorem B3798245 : Blo 2249435 3798245 := bbase (se 4 (by rfl) ⟨356085, by rfl⟩ : syracuseStep 3798245 = 712171) (by norm_num)
theorem B2532163 : Blo 2249435 2532163 := bstep (se 1 (by rfl) ⟨1899122, by rfl⟩ : syracuseStep 2532163 = 3798245) B3798245
theorem B3376217 : Blo 2249435 3376217 := bstep (se 2 (by rfl) ⟨1266081, by rfl⟩ : syracuseStep 3376217 = 2532163) B2532163
theorem B2250811 : Blo 2249435 2250811 := bstep (se 1 (by rfl) ⟨1688108, by rfl⟩ : syracuseStep 2250811 = 3376217) B3376217
theorem B9126101 : Blo 2249435 9126101 := bbase (se 7 (by rfl) ⟨106946, by rfl⟩ : syracuseStep 9126101 = 213893) (by norm_num)
theorem B6084067 : Blo 2249435 6084067 := bstep (se 1 (by rfl) ⟨4563050, by rfl⟩ : syracuseStep 6084067 = 9126101) B9126101
theorem B8112089 : Blo 2249435 8112089 := bstep (se 2 (by rfl) ⟨3042033, by rfl⟩ : syracuseStep 8112089 = 6084067) B6084067
theorem B5408059 : Blo 2249435 5408059 := bstep (se 1 (by rfl) ⟨4056044, by rfl⟩ : syracuseStep 5408059 = 8112089) B8112089
theorem B7210745 : Blo 2249435 7210745 := bstep (se 2 (by rfl) ⟨2704029, by rfl⟩ : syracuseStep 7210745 = 5408059) B5408059
theorem B4807163 : Blo 2249435 4807163 := bstep (se 1 (by rfl) ⟨3605372, by rfl⟩ : syracuseStep 4807163 = 7210745) B7210745
theorem B3204775 : Blo 2249435 3204775 := bstep (se 1 (by rfl) ⟨2403581, by rfl⟩ : syracuseStep 3204775 = 4807163) B4807163
theorem B17092133 : Blo 2249435 17092133 := bstep (se 4 (by rfl) ⟨1602387, by rfl⟩ : syracuseStep 17092133 = 3204775) B3204775
theorem B11394755 : Blo 2249435 11394755 := bstep (se 1 (by rfl) ⟨8546066, by rfl⟩ : syracuseStep 11394755 = 17092133) B17092133
theorem B7596503 : Blo 2249435 7596503 := bstep (se 1 (by rfl) ⟨5697377, by rfl⟩ : syracuseStep 7596503 = 11394755) B11394755
theorem B5064335 : Blo 2249435 5064335 := bstep (se 1 (by rfl) ⟨3798251, by rfl⟩ : syracuseStep 5064335 = 7596503) B7596503
theorem B3376223 : Blo 2249435 3376223 := bstep (se 1 (by rfl) ⟨2532167, by rfl⟩ : syracuseStep 3376223 = 5064335) B5064335
theorem B2250815 : Blo 2249435 2250815 := bstep (se 1 (by rfl) ⟨1688111, by rfl⟩ : syracuseStep 2250815 = 3376223) B3376223
theorem B3376229 : Blo 2249435 3376229 := bbase (se 4 (by rfl) ⟨316521, by rfl⟩ : syracuseStep 3376229 = 633043) (by norm_num)
theorem B2250819 : Blo 2249435 2250819 := bstep (se 1 (by rfl) ⟨1688114, by rfl⟩ : syracuseStep 2250819 = 3376229) B3376229
theorem B4807181 : Blo 2249435 4807181 := bbase (se 3 (by rfl) ⟨901346, by rfl⟩ : syracuseStep 4807181 = 1802693) (by norm_num)
theorem B3204787 : Blo 2249435 3204787 := bstep (se 1 (by rfl) ⟨2403590, by rfl⟩ : syracuseStep 3204787 = 4807181) B4807181
theorem B4273049 : Blo 2249435 4273049 := bstep (se 2 (by rfl) ⟨1602393, by rfl⟩ : syracuseStep 4273049 = 3204787) B3204787
theorem B2848699 : Blo 2249435 2848699 := bstep (se 1 (by rfl) ⟨2136524, by rfl⟩ : syracuseStep 2848699 = 4273049) B4273049
theorem B3798265 : Blo 2249435 3798265 := bstep (se 2 (by rfl) ⟨1424349, by rfl⟩ : syracuseStep 3798265 = 2848699) B2848699
theorem B5064353 : Blo 2249435 5064353 := bstep (se 2 (by rfl) ⟨1899132, by rfl⟩ : syracuseStep 5064353 = 3798265) B3798265
theorem B3376235 : Blo 2249435 3376235 := bstep (se 1 (by rfl) ⟨2532176, by rfl⟩ : syracuseStep 3376235 = 5064353) B5064353
theorem B2250823 : Blo 2249435 2250823 := bstep (se 1 (by rfl) ⟨1688117, by rfl⟩ : syracuseStep 2250823 = 3376235) B3376235
theorem B2532181 : Blo 2249435 2532181 := bbase (se 9 (by rfl) ⟨7418, by rfl⟩ : syracuseStep 2532181 = 14837) (by norm_num)
theorem B3376241 : Blo 2249435 3376241 := bstep (se 2 (by rfl) ⟨1266090, by rfl⟩ : syracuseStep 3376241 = 2532181) B2532181
theorem B2250827 : Blo 2249435 2250827 := bstep (se 1 (by rfl) ⟨1688120, by rfl⟩ : syracuseStep 2250827 = 3376241) B3376241
theorem B2848709 : Blo 2249435 2848709 := bbase (se 4 (by rfl) ⟨267066, by rfl⟩ : syracuseStep 2848709 = 534133) (by norm_num)
theorem B7596557 : Blo 2249435 7596557 := bstep (se 3 (by rfl) ⟨1424354, by rfl⟩ : syracuseStep 7596557 = 2848709) B2848709
theorem B5064371 : Blo 2249435 5064371 := bstep (se 1 (by rfl) ⟨3798278, by rfl⟩ : syracuseStep 5064371 = 7596557) B7596557
theorem B3376247 : Blo 2249435 3376247 := bstep (se 1 (by rfl) ⟨2532185, by rfl⟩ : syracuseStep 3376247 = 5064371) B5064371
theorem B2250831 : Blo 2249435 2250831 := bstep (se 1 (by rfl) ⟨1688123, by rfl⟩ : syracuseStep 2250831 = 3376247) B3376247
theorem B3376253 : Blo 2249435 3376253 := bbase (se 3 (by rfl) ⟨633047, by rfl⟩ : syracuseStep 3376253 = 1266095) (by norm_num)
theorem B2250835 : Blo 2249435 2250835 := bstep (se 1 (by rfl) ⟨1688126, by rfl⟩ : syracuseStep 2250835 = 3376253) B3376253
theorem B5064389 : Blo 2249435 5064389 := bbase (se 4 (by rfl) ⟨474786, by rfl⟩ : syracuseStep 5064389 = 949573) (by norm_num)
theorem B3376259 : Blo 2249435 3376259 := bstep (se 1 (by rfl) ⟨2532194, by rfl⟩ : syracuseStep 3376259 = 5064389) B5064389
theorem B2250839 : Blo 2249435 2250839 := bstep (se 1 (by rfl) ⟨1688129, by rfl⟩ : syracuseStep 2250839 = 3376259) B3376259
theorem B38982485 : Blo 2249435 38982485 := bbase (se 9 (by rfl) ⟨114206, by rfl⟩ : syracuseStep 38982485 = 228413) (by norm_num)
theorem B25988323 : Blo 2249435 25988323 := bstep (se 1 (by rfl) ⟨19491242, by rfl⟩ : syracuseStep 25988323 = 38982485) B38982485
theorem B34651097 : Blo 2249435 34651097 := bstep (se 2 (by rfl) ⟨12994161, by rfl⟩ : syracuseStep 34651097 = 25988323) B25988323
theorem B23100731 : Blo 2249435 23100731 := bstep (se 1 (by rfl) ⟨17325548, by rfl⟩ : syracuseStep 23100731 = 34651097) B34651097
theorem B15400487 : Blo 2249435 15400487 := bstep (se 1 (by rfl) ⟨11550365, by rfl⟩ : syracuseStep 15400487 = 23100731) B23100731
theorem B41067965 : Blo 2249435 41067965 := bstep (se 3 (by rfl) ⟨7700243, by rfl⟩ : syracuseStep 41067965 = 15400487) B15400487
theorem B27378643 : Blo 2249435 27378643 := bstep (se 1 (by rfl) ⟨20533982, by rfl⟩ : syracuseStep 27378643 = 41067965) B41067965
theorem B36504857 : Blo 2249435 36504857 := bstep (se 2 (by rfl) ⟨13689321, by rfl⟩ : syracuseStep 36504857 = 27378643) B27378643
theorem B24336571 : Blo 2249435 24336571 := bstep (se 1 (by rfl) ⟨18252428, by rfl⟩ : syracuseStep 24336571 = 36504857) B36504857
theorem B32448761 : Blo 2249435 32448761 := bstep (se 2 (by rfl) ⟨12168285, by rfl⟩ : syracuseStep 32448761 = 24336571) B24336571
theorem B21632507 : Blo 2249435 21632507 := bstep (se 1 (by rfl) ⟨16224380, by rfl⟩ : syracuseStep 21632507 = 32448761) B32448761
theorem B14421671 : Blo 2249435 14421671 := bstep (se 1 (by rfl) ⟨10816253, by rfl⟩ : syracuseStep 14421671 = 21632507) B21632507
theorem B9614447 : Blo 2249435 9614447 := bstep (se 1 (by rfl) ⟨7210835, by rfl⟩ : syracuseStep 9614447 = 14421671) B14421671
theorem B6409631 : Blo 2249435 6409631 := bstep (se 1 (by rfl) ⟨4807223, by rfl⟩ : syracuseStep 6409631 = 9614447) B9614447
theorem B4273087 : Blo 2249435 4273087 := bstep (se 1 (by rfl) ⟨3204815, by rfl⟩ : syracuseStep 4273087 = 6409631) B6409631
theorem B5697449 : Blo 2249435 5697449 := bstep (se 2 (by rfl) ⟨2136543, by rfl⟩ : syracuseStep 5697449 = 4273087) B4273087
theorem B3798299 : Blo 2249435 3798299 := bstep (se 1 (by rfl) ⟨2848724, by rfl⟩ : syracuseStep 3798299 = 5697449) B5697449
theorem B2532199 : Blo 2249435 2532199 := bstep (se 1 (by rfl) ⟨1899149, by rfl⟩ : syracuseStep 2532199 = 3798299) B3798299
theorem B3376265 : Blo 2249435 3376265 := bstep (se 2 (by rfl) ⟨1266099, by rfl⟩ : syracuseStep 3376265 = 2532199) B2532199
theorem B2250843 : Blo 2249435 2250843 := bstep (se 1 (by rfl) ⟨1688132, by rfl⟩ : syracuseStep 2250843 = 3376265) B3376265
theorem B11394917 : Blo 2249435 11394917 := bbase (se 4 (by rfl) ⟨1068273, by rfl⟩ : syracuseStep 11394917 = 2136547) (by norm_num)
theorem B7596611 : Blo 2249435 7596611 := bstep (se 1 (by rfl) ⟨5697458, by rfl⟩ : syracuseStep 7596611 = 11394917) B11394917
theorem B5064407 : Blo 2249435 5064407 := bstep (se 1 (by rfl) ⟨3798305, by rfl⟩ : syracuseStep 5064407 = 7596611) B7596611
theorem B3376271 : Blo 2249435 3376271 := bstep (se 1 (by rfl) ⟨2532203, by rfl⟩ : syracuseStep 3376271 = 5064407) B5064407
theorem B2250847 : Blo 2249435 2250847 := bstep (se 1 (by rfl) ⟨1688135, by rfl⟩ : syracuseStep 2250847 = 3376271) B3376271
theorem B3376277 : Blo 2249435 3376277 := bbase (se 6 (by rfl) ⟨79131, by rfl⟩ : syracuseStep 3376277 = 158263) (by norm_num)
theorem B2250851 : Blo 2249435 2250851 := bstep (se 1 (by rfl) ⟨1688138, by rfl⟩ : syracuseStep 2250851 = 3376277) B3376277
theorem B3654629 : Blo 2249435 3654629 := bbase (se 4 (by rfl) ⟨342621, by rfl⟩ : syracuseStep 3654629 = 685243) (by norm_num)
theorem B2436419 : Blo 2249435 2436419 := bstep (se 1 (by rfl) ⟨1827314, by rfl⟩ : syracuseStep 2436419 = 3654629) B3654629
theorem B6497117 : Blo 2249435 6497117 := bstep (se 3 (by rfl) ⟨1218209, by rfl⟩ : syracuseStep 6497117 = 2436419) B2436419
theorem B4331411 : Blo 2249435 4331411 := bstep (se 1 (by rfl) ⟨3248558, by rfl⟩ : syracuseStep 4331411 = 6497117) B6497117
theorem B2887607 : Blo 2249435 2887607 := bstep (se 1 (by rfl) ⟨2165705, by rfl⟩ : syracuseStep 2887607 = 4331411) B4331411
theorem B7700285 : Blo 2249435 7700285 := bstep (se 3 (by rfl) ⟨1443803, by rfl⟩ : syracuseStep 7700285 = 2887607) B2887607
theorem B20534093 : Blo 2249435 20534093 := bstep (se 3 (by rfl) ⟨3850142, by rfl⟩ : syracuseStep 20534093 = 7700285) B7700285
theorem B13689395 : Blo 2249435 13689395 := bstep (se 1 (by rfl) ⟨10267046, by rfl⟩ : syracuseStep 13689395 = 20534093) B20534093
theorem B9126263 : Blo 2249435 9126263 := bstep (se 1 (by rfl) ⟨6844697, by rfl⟩ : syracuseStep 9126263 = 13689395) B13689395
theorem B6084175 : Blo 2249435 6084175 := bstep (se 1 (by rfl) ⟨4563131, by rfl⟩ : syracuseStep 6084175 = 9126263) B9126263
theorem B8112233 : Blo 2249435 8112233 := bstep (se 2 (by rfl) ⟨3042087, by rfl⟩ : syracuseStep 8112233 = 6084175) B6084175
theorem B5408155 : Blo 2249435 5408155 := bstep (se 1 (by rfl) ⟨4056116, by rfl⟩ : syracuseStep 5408155 = 8112233) B8112233
theorem B7210873 : Blo 2249435 7210873 := bstep (se 2 (by rfl) ⟨2704077, by rfl⟩ : syracuseStep 7210873 = 5408155) B5408155
theorem B9614497 : Blo 2249435 9614497 := bstep (se 2 (by rfl) ⟨3605436, by rfl⟩ : syracuseStep 9614497 = 7210873) B7210873
theorem B12819329 : Blo 2249435 12819329 := bstep (se 2 (by rfl) ⟨4807248, by rfl⟩ : syracuseStep 12819329 = 9614497) B9614497
theorem B8546219 : Blo 2249435 8546219 := bstep (se 1 (by rfl) ⟨6409664, by rfl⟩ : syracuseStep 8546219 = 12819329) B12819329
theorem B5697479 : Blo 2249435 5697479 := bstep (se 1 (by rfl) ⟨4273109, by rfl⟩ : syracuseStep 5697479 = 8546219) B8546219
theorem B3798319 : Blo 2249435 3798319 := bstep (se 1 (by rfl) ⟨2848739, by rfl⟩ : syracuseStep 3798319 = 5697479) B5697479
theorem B5064425 : Blo 2249435 5064425 := bstep (se 2 (by rfl) ⟨1899159, by rfl⟩ : syracuseStep 5064425 = 3798319) B3798319
theorem B3376283 : Blo 2249435 3376283 := bstep (se 1 (by rfl) ⟨2532212, by rfl⟩ : syracuseStep 3376283 = 5064425) B5064425
theorem B2250855 : Blo 2249435 2250855 := bstep (se 1 (by rfl) ⟨1688141, by rfl⟩ : syracuseStep 2250855 = 3376283) B3376283
theorem B2532217 : Blo 2249435 2532217 := bbase (se 2 (by rfl) ⟨949581, by rfl⟩ : syracuseStep 2532217 = 1899163) (by norm_num)
theorem B3376289 : Blo 2249435 3376289 := bstep (se 2 (by rfl) ⟨1266108, by rfl⟩ : syracuseStep 3376289 = 2532217) B2532217
theorem B2250859 : Blo 2249435 2250859 := bstep (se 1 (by rfl) ⟨1688144, by rfl⟩ : syracuseStep 2250859 = 3376289) B3376289
theorem B6084197 : Blo 2249435 6084197 := bbase (se 4 (by rfl) ⟨570393, by rfl⟩ : syracuseStep 6084197 = 1140787) (by norm_num)
theorem B4056131 : Blo 2249435 4056131 := bstep (se 1 (by rfl) ⟨3042098, by rfl⟩ : syracuseStep 4056131 = 6084197) B6084197
theorem B2704087 : Blo 2249435 2704087 := bstep (se 1 (by rfl) ⟨2028065, by rfl⟩ : syracuseStep 2704087 = 4056131) B4056131
theorem B14421797 : Blo 2249435 14421797 := bstep (se 4 (by rfl) ⟨1352043, by rfl⟩ : syracuseStep 14421797 = 2704087) B2704087
theorem B9614531 : Blo 2249435 9614531 := bstep (se 1 (by rfl) ⟨7210898, by rfl⟩ : syracuseStep 9614531 = 14421797) B14421797
theorem B6409687 : Blo 2249435 6409687 := bstep (se 1 (by rfl) ⟨4807265, by rfl⟩ : syracuseStep 6409687 = 9614531) B9614531
theorem B8546249 : Blo 2249435 8546249 := bstep (se 2 (by rfl) ⟨3204843, by rfl⟩ : syracuseStep 8546249 = 6409687) B6409687
theorem B5697499 : Blo 2249435 5697499 := bstep (se 1 (by rfl) ⟨4273124, by rfl⟩ : syracuseStep 5697499 = 8546249) B8546249
theorem B7596665 : Blo 2249435 7596665 := bstep (se 2 (by rfl) ⟨2848749, by rfl⟩ : syracuseStep 7596665 = 5697499) B5697499
theorem B5064443 : Blo 2249435 5064443 := bstep (se 1 (by rfl) ⟨3798332, by rfl⟩ : syracuseStep 5064443 = 7596665) B7596665
theorem B3376295 : Blo 2249435 3376295 := bstep (se 1 (by rfl) ⟨2532221, by rfl⟩ : syracuseStep 3376295 = 5064443) B5064443
theorem B2250863 : Blo 2249435 2250863 := bstep (se 1 (by rfl) ⟨1688147, by rfl⟩ : syracuseStep 2250863 = 3376295) B3376295
theorem B3376301 : Blo 2249435 3376301 := bbase (se 3 (by rfl) ⟨633056, by rfl⟩ : syracuseStep 3376301 = 1266113) (by norm_num)
theorem B2250867 : Blo 2249435 2250867 := bstep (se 1 (by rfl) ⟨1688150, by rfl⟩ : syracuseStep 2250867 = 3376301) B3376301
theorem B5064461 : Blo 2249435 5064461 := bbase (se 3 (by rfl) ⟨949586, by rfl⟩ : syracuseStep 5064461 = 1899173) (by norm_num)
theorem B3376307 : Blo 2249435 3376307 := bstep (se 1 (by rfl) ⟨2532230, by rfl⟩ : syracuseStep 3376307 = 5064461) B5064461
theorem B2250871 : Blo 2249435 2250871 := bstep (se 1 (by rfl) ⟨1688153, by rfl⟩ : syracuseStep 2250871 = 3376307) B3376307
theorem B2848765 : Blo 2249435 2848765 := bbase (se 3 (by rfl) ⟨534143, by rfl⟩ : syracuseStep 2848765 = 1068287) (by norm_num)
theorem B3798353 : Blo 2249435 3798353 := bstep (se 2 (by rfl) ⟨1424382, by rfl⟩ : syracuseStep 3798353 = 2848765) B2848765
theorem B2532235 : Blo 2249435 2532235 := bstep (se 1 (by rfl) ⟨1899176, by rfl⟩ : syracuseStep 2532235 = 3798353) B3798353
theorem B3376313 : Blo 2249435 3376313 := bstep (se 2 (by rfl) ⟨1266117, by rfl⟩ : syracuseStep 3376313 = 2532235) B2532235
theorem B2250875 : Blo 2249435 2250875 := bstep (se 1 (by rfl) ⟨1688156, by rfl⟩ : syracuseStep 2250875 = 3376313) B3376313
theorem B7210949 : Blo 2249435 7210949 := bbase (se 4 (by rfl) ⟨676026, by rfl⟩ : syracuseStep 7210949 = 1352053) (by norm_num)
theorem B19229197 : Blo 2249435 19229197 := bstep (se 3 (by rfl) ⟨3605474, by rfl⟩ : syracuseStep 19229197 = 7210949) B7210949
theorem B25638929 : Blo 2249435 25638929 := bstep (se 2 (by rfl) ⟨9614598, by rfl⟩ : syracuseStep 25638929 = 19229197) B19229197
theorem B17092619 : Blo 2249435 17092619 := bstep (se 1 (by rfl) ⟨12819464, by rfl⟩ : syracuseStep 17092619 = 25638929) B25638929
theorem B11395079 : Blo 2249435 11395079 := bstep (se 1 (by rfl) ⟨8546309, by rfl⟩ : syracuseStep 11395079 = 17092619) B17092619
theorem B7596719 : Blo 2249435 7596719 := bstep (se 1 (by rfl) ⟨5697539, by rfl⟩ : syracuseStep 7596719 = 11395079) B11395079
theorem B5064479 : Blo 2249435 5064479 := bstep (se 1 (by rfl) ⟨3798359, by rfl⟩ : syracuseStep 5064479 = 7596719) B7596719
theorem B3376319 : Blo 2249435 3376319 := bstep (se 1 (by rfl) ⟨2532239, by rfl⟩ : syracuseStep 3376319 = 5064479) B5064479
theorem B2250879 : Blo 2249435 2250879 := bstep (se 1 (by rfl) ⟨1688159, by rfl⟩ : syracuseStep 2250879 = 3376319) B3376319
theorem B3376325 : Blo 2249435 3376325 := bbase (se 4 (by rfl) ⟨316530, by rfl⟩ : syracuseStep 3376325 = 633061) (by norm_num)
theorem B2250883 : Blo 2249435 2250883 := bstep (se 1 (by rfl) ⟨1688162, by rfl⟩ : syracuseStep 2250883 = 3376325) B3376325
theorem B3798373 : Blo 2249435 3798373 := bbase (se 4 (by rfl) ⟨356097, by rfl⟩ : syracuseStep 3798373 = 712195) (by norm_num)
theorem B5064497 : Blo 2249435 5064497 := bstep (se 2 (by rfl) ⟨1899186, by rfl⟩ : syracuseStep 5064497 = 3798373) B3798373
theorem B3376331 : Blo 2249435 3376331 := bstep (se 1 (by rfl) ⟨2532248, by rfl⟩ : syracuseStep 3376331 = 5064497) B5064497
theorem B2250887 : Blo 2249435 2250887 := bstep (se 1 (by rfl) ⟨1688165, by rfl⟩ : syracuseStep 2250887 = 3376331) B3376331
theorem B2532253 : Blo 2249435 2532253 := bbase (se 3 (by rfl) ⟨474797, by rfl⟩ : syracuseStep 2532253 = 949595) (by norm_num)
theorem B3376337 : Blo 2249435 3376337 := bstep (se 2 (by rfl) ⟨1266126, by rfl⟩ : syracuseStep 3376337 = 2532253) B2532253
theorem B2250891 : Blo 2249435 2250891 := bstep (se 1 (by rfl) ⟨1688168, by rfl⟩ : syracuseStep 2250891 = 3376337) B3376337
theorem B7596773 : Blo 2249435 7596773 := bbase (se 4 (by rfl) ⟨712197, by rfl⟩ : syracuseStep 7596773 = 1424395) (by norm_num)
theorem B5064515 : Blo 2249435 5064515 := bstep (se 1 (by rfl) ⟨3798386, by rfl⟩ : syracuseStep 5064515 = 7596773) B7596773
theorem B3376343 : Blo 2249435 3376343 := bstep (se 1 (by rfl) ⟨2532257, by rfl⟩ : syracuseStep 3376343 = 5064515) B5064515
theorem B2250895 : Blo 2249435 2250895 := bstep (se 1 (by rfl) ⟨1688171, by rfl⟩ : syracuseStep 2250895 = 3376343) B3376343
theorem B3376349 : Blo 2249435 3376349 := bbase (se 3 (by rfl) ⟨633065, by rfl⟩ : syracuseStep 3376349 = 1266131) (by norm_num)
theorem B2250899 : Blo 2249435 2250899 := bstep (se 1 (by rfl) ⟨1688174, by rfl⟩ : syracuseStep 2250899 = 3376349) B3376349
theorem B5064533 : Blo 2249435 5064533 := bbase (se 9 (by rfl) ⟨14837, by rfl⟩ : syracuseStep 5064533 = 29675) (by norm_num)
theorem B3376355 : Blo 2249435 3376355 := bstep (se 1 (by rfl) ⟨2532266, by rfl⟩ : syracuseStep 3376355 = 5064533) B5064533
theorem B2250903 : Blo 2249435 2250903 := bstep (se 1 (by rfl) ⟨1688177, by rfl⟩ : syracuseStep 2250903 = 3376355) B3376355
theorem B6409813 : Blo 2249435 6409813 := bbase (se 8 (by rfl) ⟨37557, by rfl⟩ : syracuseStep 6409813 = 75115) (by norm_num)
theorem B8546417 : Blo 2249435 8546417 := bstep (se 2 (by rfl) ⟨3204906, by rfl⟩ : syracuseStep 8546417 = 6409813) B6409813
theorem B5697611 : Blo 2249435 5697611 := bstep (se 1 (by rfl) ⟨4273208, by rfl⟩ : syracuseStep 5697611 = 8546417) B8546417
theorem B3798407 : Blo 2249435 3798407 := bstep (se 1 (by rfl) ⟨2848805, by rfl⟩ : syracuseStep 3798407 = 5697611) B5697611
theorem B2532271 : Blo 2249435 2532271 := bstep (se 1 (by rfl) ⟨1899203, by rfl⟩ : syracuseStep 2532271 = 3798407) B3798407
theorem B3376361 : Blo 2249435 3376361 := bstep (se 2 (by rfl) ⟨1266135, by rfl⟩ : syracuseStep 3376361 = 2532271) B2532271
theorem B2250907 : Blo 2249435 2250907 := bstep (se 1 (by rfl) ⟨1688180, by rfl⟩ : syracuseStep 2250907 = 3376361) B3376361
theorem B9878885 : Blo 2249435 9878885 := bbase (se 4 (by rfl) ⟨926145, by rfl⟩ : syracuseStep 9878885 = 1852291) (by norm_num)
theorem B6585923 : Blo 2249435 6585923 := bstep (se 1 (by rfl) ⟨4939442, by rfl⟩ : syracuseStep 6585923 = 9878885) B9878885
theorem B4390615 : Blo 2249435 4390615 := bstep (se 1 (by rfl) ⟨3292961, by rfl⟩ : syracuseStep 4390615 = 6585923) B6585923
theorem B5854153 : Blo 2249435 5854153 := bstep (se 2 (by rfl) ⟨2195307, by rfl⟩ : syracuseStep 5854153 = 4390615) B4390615
theorem B7805537 : Blo 2249435 7805537 := bstep (se 2 (by rfl) ⟨2927076, by rfl⟩ : syracuseStep 7805537 = 5854153) B5854153
theorem B5203691 : Blo 2249435 5203691 := bstep (se 1 (by rfl) ⟨3902768, by rfl⟩ : syracuseStep 5203691 = 7805537) B7805537
theorem B3469127 : Blo 2249435 3469127 := bstep (se 1 (by rfl) ⟨2601845, by rfl⟩ : syracuseStep 3469127 = 5203691) B5203691
theorem B9251005 : Blo 2249435 9251005 := bstep (se 3 (by rfl) ⟨1734563, by rfl⟩ : syracuseStep 9251005 = 3469127) B3469127
theorem B12334673 : Blo 2249435 12334673 := bstep (se 2 (by rfl) ⟨4625502, by rfl⟩ : syracuseStep 12334673 = 9251005) B9251005
theorem B8223115 : Blo 2249435 8223115 := bstep (se 1 (by rfl) ⟨6167336, by rfl⟩ : syracuseStep 8223115 = 12334673) B12334673
theorem B10964153 : Blo 2249435 10964153 := bstep (se 2 (by rfl) ⟨4111557, by rfl⟩ : syracuseStep 10964153 = 8223115) B8223115
theorem B7309435 : Blo 2249435 7309435 := bstep (se 1 (by rfl) ⟨5482076, by rfl⟩ : syracuseStep 7309435 = 10964153) B10964153
theorem B9745913 : Blo 2249435 9745913 := bstep (se 2 (by rfl) ⟨3654717, by rfl⟩ : syracuseStep 9745913 = 7309435) B7309435
theorem B25989101 : Blo 2249435 25989101 := bstep (se 3 (by rfl) ⟨4872956, by rfl⟩ : syracuseStep 25989101 = 9745913) B9745913
theorem B17326067 : Blo 2249435 17326067 := bstep (se 1 (by rfl) ⟨12994550, by rfl⟩ : syracuseStep 17326067 = 25989101) B25989101
theorem B46202845 : Blo 2249435 46202845 := bstep (se 3 (by rfl) ⟨8663033, by rfl⟩ : syracuseStep 46202845 = 17326067) B17326067
theorem B61603793 : Blo 2249435 61603793 := bstep (se 2 (by rfl) ⟨23101422, by rfl⟩ : syracuseStep 61603793 = 46202845) B46202845
theorem B41069195 : Blo 2249435 41069195 := bstep (se 1 (by rfl) ⟨30801896, by rfl⟩ : syracuseStep 41069195 = 61603793) B61603793
theorem B27379463 : Blo 2249435 27379463 := bstep (se 1 (by rfl) ⟨20534597, by rfl⟩ : syracuseStep 27379463 = 41069195) B41069195
theorem B73011901 : Blo 2249435 73011901 := bstep (se 3 (by rfl) ⟨13689731, by rfl⟩ : syracuseStep 73011901 = 27379463) B27379463
theorem B97349201 : Blo 2249435 97349201 := bstep (se 2 (by rfl) ⟨36505950, by rfl⟩ : syracuseStep 97349201 = 73011901) B73011901
theorem B64899467 : Blo 2249435 64899467 := bstep (se 1 (by rfl) ⟨48674600, by rfl⟩ : syracuseStep 64899467 = 97349201) B97349201
theorem B43266311 : Blo 2249435 43266311 := bstep (se 1 (by rfl) ⟨32449733, by rfl⟩ : syracuseStep 43266311 = 64899467) B64899467
theorem B28844207 : Blo 2249435 28844207 := bstep (se 1 (by rfl) ⟨21633155, by rfl⟩ : syracuseStep 28844207 = 43266311) B43266311
theorem B19229471 : Blo 2249435 19229471 := bstep (se 1 (by rfl) ⟨14422103, by rfl⟩ : syracuseStep 19229471 = 28844207) B28844207
theorem B12819647 : Blo 2249435 12819647 := bstep (se 1 (by rfl) ⟨9614735, by rfl⟩ : syracuseStep 12819647 = 19229471) B19229471
theorem B8546431 : Blo 2249435 8546431 := bstep (se 1 (by rfl) ⟨6409823, by rfl⟩ : syracuseStep 8546431 = 12819647) B12819647
theorem B11395241 : Blo 2249435 11395241 := bstep (se 2 (by rfl) ⟨4273215, by rfl⟩ : syracuseStep 11395241 = 8546431) B8546431
theorem B7596827 : Blo 2249435 7596827 := bstep (se 1 (by rfl) ⟨5697620, by rfl⟩ : syracuseStep 7596827 = 11395241) B11395241
theorem B5064551 : Blo 2249435 5064551 := bstep (se 1 (by rfl) ⟨3798413, by rfl⟩ : syracuseStep 5064551 = 7596827) B7596827
theorem B3376367 : Blo 2249435 3376367 := bstep (se 1 (by rfl) ⟨2532275, by rfl⟩ : syracuseStep 3376367 = 5064551) B5064551
theorem B2250911 : Blo 2249435 2250911 := bstep (se 1 (by rfl) ⟨1688183, by rfl⟩ : syracuseStep 2250911 = 3376367) B3376367
theorem B3376373 : Blo 2249435 3376373 := bbase (se 5 (by rfl) ⟨158267, by rfl⟩ : syracuseStep 3376373 = 316535) (by norm_num)
theorem B2250915 : Blo 2249435 2250915 := bstep (se 1 (by rfl) ⟨1688186, by rfl⟩ : syracuseStep 2250915 = 3376373) B3376373
theorem B5408309 : Blo 2249435 5408309 := bbase (se 5 (by rfl) ⟨253514, by rfl⟩ : syracuseStep 5408309 = 507029) (by norm_num)
theorem B14422157 : Blo 2249435 14422157 := bstep (se 3 (by rfl) ⟨2704154, by rfl⟩ : syracuseStep 14422157 = 5408309) B5408309
theorem B9614771 : Blo 2249435 9614771 := bstep (se 1 (by rfl) ⟨7211078, by rfl⟩ : syracuseStep 9614771 = 14422157) B14422157
theorem B6409847 : Blo 2249435 6409847 := bstep (se 1 (by rfl) ⟨4807385, by rfl⟩ : syracuseStep 6409847 = 9614771) B9614771
theorem B4273231 : Blo 2249435 4273231 := bstep (se 1 (by rfl) ⟨3204923, by rfl⟩ : syracuseStep 4273231 = 6409847) B6409847
theorem B5697641 : Blo 2249435 5697641 := bstep (se 2 (by rfl) ⟨2136615, by rfl⟩ : syracuseStep 5697641 = 4273231) B4273231
theorem B3798427 : Blo 2249435 3798427 := bstep (se 1 (by rfl) ⟨2848820, by rfl⟩ : syracuseStep 3798427 = 5697641) B5697641
theorem B5064569 : Blo 2249435 5064569 := bstep (se 2 (by rfl) ⟨1899213, by rfl⟩ : syracuseStep 5064569 = 3798427) B3798427
theorem B3376379 : Blo 2249435 3376379 := bstep (se 1 (by rfl) ⟨2532284, by rfl⟩ : syracuseStep 3376379 = 5064569) B5064569
theorem B2250919 : Blo 2249435 2250919 := bstep (se 1 (by rfl) ⟨1688189, by rfl⟩ : syracuseStep 2250919 = 3376379) B3376379
theorem B2532289 : Blo 2249435 2532289 := bbase (se 2 (by rfl) ⟨949608, by rfl⟩ : syracuseStep 2532289 = 1899217) (by norm_num)
theorem B3376385 : Blo 2249435 3376385 := bstep (se 2 (by rfl) ⟨1266144, by rfl⟩ : syracuseStep 3376385 = 2532289) B2532289
theorem B2250923 : Blo 2249435 2250923 := bstep (se 1 (by rfl) ⟨1688192, by rfl⟩ : syracuseStep 2250923 = 3376385) B3376385
theorem B5697661 : Blo 2249435 5697661 := bbase (se 3 (by rfl) ⟨1068311, by rfl⟩ : syracuseStep 5697661 = 2136623) (by norm_num)
theorem B7596881 : Blo 2249435 7596881 := bstep (se 2 (by rfl) ⟨2848830, by rfl⟩ : syracuseStep 7596881 = 5697661) B5697661
theorem B5064587 : Blo 2249435 5064587 := bstep (se 1 (by rfl) ⟨3798440, by rfl⟩ : syracuseStep 5064587 = 7596881) B7596881
theorem B3376391 : Blo 2249435 3376391 := bstep (se 1 (by rfl) ⟨2532293, by rfl⟩ : syracuseStep 3376391 = 5064587) B5064587
theorem B2250927 : Blo 2249435 2250927 := bstep (se 1 (by rfl) ⟨1688195, by rfl⟩ : syracuseStep 2250927 = 3376391) B3376391
theorem B3376397 : Blo 2249435 3376397 := bbase (se 3 (by rfl) ⟨633074, by rfl⟩ : syracuseStep 3376397 = 1266149) (by norm_num)
theorem B2250931 : Blo 2249435 2250931 := bstep (se 1 (by rfl) ⟨1688198, by rfl⟩ : syracuseStep 2250931 = 3376397) B3376397
theorem B5064605 : Blo 2249435 5064605 := bbase (se 3 (by rfl) ⟨949613, by rfl⟩ : syracuseStep 5064605 = 1899227) (by norm_num)
theorem B3376403 : Blo 2249435 3376403 := bstep (se 1 (by rfl) ⟨2532302, by rfl⟩ : syracuseStep 3376403 = 5064605) B5064605
theorem B2250935 : Blo 2249435 2250935 := bstep (se 1 (by rfl) ⟨1688201, by rfl⟩ : syracuseStep 2250935 = 3376403) B3376403
theorem B3798461 : Blo 2249435 3798461 := bbase (se 3 (by rfl) ⟨712211, by rfl⟩ : syracuseStep 3798461 = 1424423) (by norm_num)
theorem B2532307 : Blo 2249435 2532307 := bstep (se 1 (by rfl) ⟨1899230, by rfl⟩ : syracuseStep 2532307 = 3798461) B3798461
theorem B3376409 : Blo 2249435 3376409 := bstep (se 2 (by rfl) ⟨1266153, by rfl⟩ : syracuseStep 3376409 = 2532307) B2532307
theorem B2250939 : Blo 2249435 2250939 := bstep (se 1 (by rfl) ⟨1688204, by rfl⟩ : syracuseStep 2250939 = 3376409) B3376409
theorem B12819829 : Blo 2249435 12819829 := bbase (se 5 (by rfl) ⟨600929, by rfl⟩ : syracuseStep 12819829 = 1201859) (by norm_num)
theorem B17093105 : Blo 2249435 17093105 := bstep (se 2 (by rfl) ⟨6409914, by rfl⟩ : syracuseStep 17093105 = 12819829) B12819829
theorem B11395403 : Blo 2249435 11395403 := bstep (se 1 (by rfl) ⟨8546552, by rfl⟩ : syracuseStep 11395403 = 17093105) B17093105
theorem B7596935 : Blo 2249435 7596935 := bstep (se 1 (by rfl) ⟨5697701, by rfl⟩ : syracuseStep 7596935 = 11395403) B11395403
theorem B5064623 : Blo 2249435 5064623 := bstep (se 1 (by rfl) ⟨3798467, by rfl⟩ : syracuseStep 5064623 = 7596935) B7596935
theorem B3376415 : Blo 2249435 3376415 := bstep (se 1 (by rfl) ⟨2532311, by rfl⟩ : syracuseStep 3376415 = 5064623) B5064623
theorem B2250943 : Blo 2249435 2250943 := bstep (se 1 (by rfl) ⟨1688207, by rfl⟩ : syracuseStep 2250943 = 3376415) B3376415
theorem B3376421 : Blo 2249435 3376421 := bbase (se 4 (by rfl) ⟨316539, by rfl⟩ : syracuseStep 3376421 = 633079) (by norm_num)
theorem B2250947 : Blo 2249435 2250947 := bstep (se 1 (by rfl) ⟨1688210, by rfl⟩ : syracuseStep 2250947 = 3376421) B3376421
theorem B2848861 : Blo 2249435 2848861 := bbase (se 3 (by rfl) ⟨534161, by rfl⟩ : syracuseStep 2848861 = 1068323) (by norm_num)
theorem B3798481 : Blo 2249435 3798481 := bstep (se 2 (by rfl) ⟨1424430, by rfl⟩ : syracuseStep 3798481 = 2848861) B2848861
theorem B5064641 : Blo 2249435 5064641 := bstep (se 2 (by rfl) ⟨1899240, by rfl⟩ : syracuseStep 5064641 = 3798481) B3798481
theorem B3376427 : Blo 2249435 3376427 := bstep (se 1 (by rfl) ⟨2532320, by rfl⟩ : syracuseStep 3376427 = 5064641) B5064641
theorem B2250951 : Blo 2249435 2250951 := bstep (se 1 (by rfl) ⟨1688213, by rfl⟩ : syracuseStep 2250951 = 3376427) B3376427
theorem B2532325 : Blo 2249435 2532325 := bbase (se 4 (by rfl) ⟨237405, by rfl⟩ : syracuseStep 2532325 = 474811) (by norm_num)
theorem B3376433 : Blo 2249435 3376433 := bstep (se 2 (by rfl) ⟨1266162, by rfl⟩ : syracuseStep 3376433 = 2532325) B2532325
theorem B2250955 : Blo 2249435 2250955 := bstep (se 1 (by rfl) ⟨1688216, by rfl⟩ : syracuseStep 2250955 = 3376433) B3376433
theorem B2887741 : Blo 2249435 2887741 := bbase (se 3 (by rfl) ⟨541451, by rfl⟩ : syracuseStep 2887741 = 1082903) (by norm_num)
theorem B3850321 : Blo 2249435 3850321 := bstep (se 2 (by rfl) ⟨1443870, by rfl⟩ : syracuseStep 3850321 = 2887741) B2887741
theorem B5133761 : Blo 2249435 5133761 := bstep (se 2 (by rfl) ⟨1925160, by rfl⟩ : syracuseStep 5133761 = 3850321) B3850321
theorem B3422507 : Blo 2249435 3422507 := bstep (se 1 (by rfl) ⟨2566880, by rfl⟩ : syracuseStep 3422507 = 5133761) B5133761
theorem B9126685 : Blo 2249435 9126685 := bstep (se 3 (by rfl) ⟨1711253, by rfl⟩ : syracuseStep 9126685 = 3422507) B3422507
theorem B12168913 : Blo 2249435 12168913 := bstep (se 2 (by rfl) ⟨4563342, by rfl⟩ : syracuseStep 12168913 = 9126685) B9126685
theorem B16225217 : Blo 2249435 16225217 := bstep (se 2 (by rfl) ⟨6084456, by rfl⟩ : syracuseStep 16225217 = 12168913) B12168913
theorem B10816811 : Blo 2249435 10816811 := bstep (se 1 (by rfl) ⟨8112608, by rfl⟩ : syracuseStep 10816811 = 16225217) B16225217
theorem B7211207 : Blo 2249435 7211207 := bstep (se 1 (by rfl) ⟨5408405, by rfl⟩ : syracuseStep 7211207 = 10816811) B10816811
theorem B4807471 : Blo 2249435 4807471 := bstep (se 1 (by rfl) ⟨3605603, by rfl⟩ : syracuseStep 4807471 = 7211207) B7211207
theorem B6409961 : Blo 2249435 6409961 := bstep (se 2 (by rfl) ⟨2403735, by rfl⟩ : syracuseStep 6409961 = 4807471) B4807471
theorem B4273307 : Blo 2249435 4273307 := bstep (se 1 (by rfl) ⟨3204980, by rfl⟩ : syracuseStep 4273307 = 6409961) B6409961
theorem B2848871 : Blo 2249435 2848871 := bstep (se 1 (by rfl) ⟨2136653, by rfl⟩ : syracuseStep 2848871 = 4273307) B4273307
theorem B7596989 : Blo 2249435 7596989 := bstep (se 3 (by rfl) ⟨1424435, by rfl⟩ : syracuseStep 7596989 = 2848871) B2848871
theorem B5064659 : Blo 2249435 5064659 := bstep (se 1 (by rfl) ⟨3798494, by rfl⟩ : syracuseStep 5064659 = 7596989) B7596989
theorem B3376439 : Blo 2249435 3376439 := bstep (se 1 (by rfl) ⟨2532329, by rfl⟩ : syracuseStep 3376439 = 5064659) B5064659
theorem B2250959 : Blo 2249435 2250959 := bstep (se 1 (by rfl) ⟨1688219, by rfl⟩ : syracuseStep 2250959 = 3376439) B3376439
theorem B3376445 : Blo 2249435 3376445 := bbase (se 3 (by rfl) ⟨633083, by rfl⟩ : syracuseStep 3376445 = 1266167) (by norm_num)
theorem B2250963 : Blo 2249435 2250963 := bstep (se 1 (by rfl) ⟨1688222, by rfl⟩ : syracuseStep 2250963 = 3376445) B3376445
theorem B5064677 : Blo 2249435 5064677 := bbase (se 4 (by rfl) ⟨474813, by rfl⟩ : syracuseStep 5064677 = 949627) (by norm_num)
theorem B3376451 : Blo 2249435 3376451 := bstep (se 1 (by rfl) ⟨2532338, by rfl⟩ : syracuseStep 3376451 = 5064677) B5064677
theorem B2250967 : Blo 2249435 2250967 := bstep (se 1 (by rfl) ⟨1688225, by rfl⟩ : syracuseStep 2250967 = 3376451) B3376451
theorem B5697773 : Blo 2249435 5697773 := bbase (se 3 (by rfl) ⟨1068332, by rfl⟩ : syracuseStep 5697773 = 2136665) (by norm_num)
theorem B3798515 : Blo 2249435 3798515 := bstep (se 1 (by rfl) ⟨2848886, by rfl⟩ : syracuseStep 3798515 = 5697773) B5697773
theorem B2532343 : Blo 2249435 2532343 := bstep (se 1 (by rfl) ⟨1899257, by rfl⟩ : syracuseStep 2532343 = 3798515) B3798515
theorem B3376457 : Blo 2249435 3376457 := bstep (se 2 (by rfl) ⟨1266171, by rfl⟩ : syracuseStep 3376457 = 2532343) B2532343
theorem B2250971 : Blo 2249435 2250971 := bstep (se 1 (by rfl) ⟨1688228, by rfl⟩ : syracuseStep 2250971 = 3376457) B3376457
theorem B3605629 : Blo 2249435 3605629 := bbase (se 3 (by rfl) ⟨676055, by rfl⟩ : syracuseStep 3605629 = 1352111) (by norm_num)
theorem B4807505 : Blo 2249435 4807505 := bstep (se 2 (by rfl) ⟨1802814, by rfl⟩ : syracuseStep 4807505 = 3605629) B3605629
theorem B3205003 : Blo 2249435 3205003 := bstep (se 1 (by rfl) ⟨2403752, by rfl⟩ : syracuseStep 3205003 = 4807505) B4807505
theorem B4273337 : Blo 2249435 4273337 := bstep (se 2 (by rfl) ⟨1602501, by rfl⟩ : syracuseStep 4273337 = 3205003) B3205003
theorem B11395565 : Blo 2249435 11395565 := bstep (se 3 (by rfl) ⟨2136668, by rfl⟩ : syracuseStep 11395565 = 4273337) B4273337
theorem B7597043 : Blo 2249435 7597043 := bstep (se 1 (by rfl) ⟨5697782, by rfl⟩ : syracuseStep 7597043 = 11395565) B11395565
theorem B5064695 : Blo 2249435 5064695 := bstep (se 1 (by rfl) ⟨3798521, by rfl⟩ : syracuseStep 5064695 = 7597043) B7597043
theorem B3376463 : Blo 2249435 3376463 := bstep (se 1 (by rfl) ⟨2532347, by rfl⟩ : syracuseStep 3376463 = 5064695) B5064695
theorem B2250975 : Blo 2249435 2250975 := bstep (se 1 (by rfl) ⟨1688231, by rfl⟩ : syracuseStep 2250975 = 3376463) B3376463
theorem B3376469 : Blo 2249435 3376469 := bbase (se 12 (by rfl) ⟨1236, by rfl⟩ : syracuseStep 3376469 = 2473) (by norm_num)
theorem B2250979 : Blo 2249435 2250979 := bstep (se 1 (by rfl) ⟨1688234, by rfl⟩ : syracuseStep 2250979 = 3376469) B3376469
theorem B2403761 : Blo 2249435 2403761 := bbase (se 2 (by rfl) ⟨901410, by rfl⟩ : syracuseStep 2403761 = 1802821) (by norm_num)
theorem B6410029 : Blo 2249435 6410029 := bstep (se 3 (by rfl) ⟨1201880, by rfl⟩ : syracuseStep 6410029 = 2403761) B2403761
theorem B8546705 : Blo 2249435 8546705 := bstep (se 2 (by rfl) ⟨3205014, by rfl⟩ : syracuseStep 8546705 = 6410029) B6410029
theorem B5697803 : Blo 2249435 5697803 := bstep (se 1 (by rfl) ⟨4273352, by rfl⟩ : syracuseStep 5697803 = 8546705) B8546705
theorem B3798535 : Blo 2249435 3798535 := bstep (se 1 (by rfl) ⟨2848901, by rfl⟩ : syracuseStep 3798535 = 5697803) B5697803
theorem B5064713 : Blo 2249435 5064713 := bstep (se 2 (by rfl) ⟨1899267, by rfl⟩ : syracuseStep 5064713 = 3798535) B3798535
theorem B3376475 : Blo 2249435 3376475 := bstep (se 1 (by rfl) ⟨2532356, by rfl⟩ : syracuseStep 3376475 = 5064713) B5064713
theorem B2250983 : Blo 2249435 2250983 := bstep (se 1 (by rfl) ⟨1688237, by rfl⟩ : syracuseStep 2250983 = 3376475) B3376475
theorem B2532361 : Blo 2249435 2532361 := bbase (se 2 (by rfl) ⟨949635, by rfl⟩ : syracuseStep 2532361 = 1899271) (by norm_num)
theorem B3376481 : Blo 2249435 3376481 := bstep (se 2 (by rfl) ⟨1266180, by rfl⟩ : syracuseStep 3376481 = 2532361) B2532361
theorem B2250987 : Blo 2249435 2250987 := bstep (se 1 (by rfl) ⟨1688240, by rfl⟩ : syracuseStep 2250987 = 3376481) B3376481
theorem B6497509 : Blo 2249435 6497509 := bbase (se 4 (by rfl) ⟨609141, by rfl⟩ : syracuseStep 6497509 = 1218283) (by norm_num)
theorem B8663345 : Blo 2249435 8663345 := bstep (se 2 (by rfl) ⟨3248754, by rfl⟩ : syracuseStep 8663345 = 6497509) B6497509
theorem B5775563 : Blo 2249435 5775563 := bstep (se 1 (by rfl) ⟨4331672, by rfl⟩ : syracuseStep 5775563 = 8663345) B8663345
theorem B15401501 : Blo 2249435 15401501 := bstep (se 3 (by rfl) ⟨2887781, by rfl⟩ : syracuseStep 15401501 = 5775563) B5775563
theorem B10267667 : Blo 2249435 10267667 := bstep (se 1 (by rfl) ⟨7700750, by rfl⟩ : syracuseStep 10267667 = 15401501) B15401501
theorem B6845111 : Blo 2249435 6845111 := bstep (se 1 (by rfl) ⟨5133833, by rfl⟩ : syracuseStep 6845111 = 10267667) B10267667
theorem B4563407 : Blo 2249435 4563407 := bstep (se 1 (by rfl) ⟨3422555, by rfl⟩ : syracuseStep 4563407 = 6845111) B6845111
theorem B3042271 : Blo 2249435 3042271 := bstep (se 1 (by rfl) ⟨2281703, by rfl⟩ : syracuseStep 3042271 = 4563407) B4563407
theorem B4056361 : Blo 2249435 4056361 := bstep (se 2 (by rfl) ⟨1521135, by rfl⟩ : syracuseStep 4056361 = 3042271) B3042271
theorem B21633925 : Blo 2249435 21633925 := bstep (se 4 (by rfl) ⟨2028180, by rfl⟩ : syracuseStep 21633925 = 4056361) B4056361
theorem B28845233 : Blo 2249435 28845233 := bstep (se 2 (by rfl) ⟨10816962, by rfl⟩ : syracuseStep 28845233 = 21633925) B21633925
theorem B19230155 : Blo 2249435 19230155 := bstep (se 1 (by rfl) ⟨14422616, by rfl⟩ : syracuseStep 19230155 = 28845233) B28845233
theorem B12820103 : Blo 2249435 12820103 := bstep (se 1 (by rfl) ⟨9615077, by rfl⟩ : syracuseStep 12820103 = 19230155) B19230155
theorem B8546735 : Blo 2249435 8546735 := bstep (se 1 (by rfl) ⟨6410051, by rfl⟩ : syracuseStep 8546735 = 12820103) B12820103
theorem B5697823 : Blo 2249435 5697823 := bstep (se 1 (by rfl) ⟨4273367, by rfl⟩ : syracuseStep 5697823 = 8546735) B8546735
theorem B7597097 : Blo 2249435 7597097 := bstep (se 2 (by rfl) ⟨2848911, by rfl⟩ : syracuseStep 7597097 = 5697823) B5697823
theorem B5064731 : Blo 2249435 5064731 := bstep (se 1 (by rfl) ⟨3798548, by rfl⟩ : syracuseStep 5064731 = 7597097) B7597097
theorem B3376487 : Blo 2249435 3376487 := bstep (se 1 (by rfl) ⟨2532365, by rfl⟩ : syracuseStep 3376487 = 5064731) B5064731
theorem B2250991 : Blo 2249435 2250991 := bstep (se 1 (by rfl) ⟨1688243, by rfl⟩ : syracuseStep 2250991 = 3376487) B3376487
theorem B3376493 : Blo 2249435 3376493 := bbase (se 3 (by rfl) ⟨633092, by rfl⟩ : syracuseStep 3376493 = 1266185) (by norm_num)
theorem B2250995 : Blo 2249435 2250995 := bstep (se 1 (by rfl) ⟨1688246, by rfl⟩ : syracuseStep 2250995 = 3376493) B3376493
theorem B5064749 : Blo 2249435 5064749 := bbase (se 3 (by rfl) ⟨949640, by rfl⟩ : syracuseStep 5064749 = 1899281) (by norm_num)
theorem B3376499 : Blo 2249435 3376499 := bstep (se 1 (by rfl) ⟨2532374, by rfl⟩ : syracuseStep 3376499 = 5064749) B5064749
theorem B2250999 : Blo 2249435 2250999 := bstep (se 1 (by rfl) ⟨1688249, by rfl⟩ : syracuseStep 2250999 = 3376499) B3376499
theorem B2408809 : Blo 2249435 2408809 := bbase (se 2 (by rfl) ⟨903303, by rfl⟩ : syracuseStep 2408809 = 1806607) (by norm_num)
theorem B3211745 : Blo 2249435 3211745 := bstep (se 2 (by rfl) ⟨1204404, by rfl⟩ : syracuseStep 3211745 = 2408809) B2408809
theorem B8564653 : Blo 2249435 8564653 := bstep (se 3 (by rfl) ⟨1605872, by rfl⟩ : syracuseStep 8564653 = 3211745) B3211745
theorem B11419537 : Blo 2249435 11419537 := bstep (se 2 (by rfl) ⟨4282326, by rfl⟩ : syracuseStep 11419537 = 8564653) B8564653
theorem B15226049 : Blo 2249435 15226049 := bstep (se 2 (by rfl) ⟨5709768, by rfl⟩ : syracuseStep 15226049 = 11419537) B11419537
theorem B10150699 : Blo 2249435 10150699 := bstep (se 1 (by rfl) ⟨7613024, by rfl⟩ : syracuseStep 10150699 = 15226049) B15226049
theorem B13534265 : Blo 2249435 13534265 := bstep (se 2 (by rfl) ⟨5075349, by rfl⟩ : syracuseStep 13534265 = 10150699) B10150699
theorem B9022843 : Blo 2249435 9022843 := bstep (se 1 (by rfl) ⟨6767132, by rfl⟩ : syracuseStep 9022843 = 13534265) B13534265
theorem B12030457 : Blo 2249435 12030457 := bstep (se 2 (by rfl) ⟨4511421, by rfl⟩ : syracuseStep 12030457 = 9022843) B9022843
theorem B16040609 : Blo 2249435 16040609 := bstep (se 2 (by rfl) ⟨6015228, by rfl⟩ : syracuseStep 16040609 = 12030457) B12030457
theorem B10693739 : Blo 2249435 10693739 := bstep (se 1 (by rfl) ⟨8020304, by rfl⟩ : syracuseStep 10693739 = 16040609) B16040609
theorem B28516637 : Blo 2249435 28516637 := bstep (se 3 (by rfl) ⟨5346869, by rfl⟩ : syracuseStep 28516637 = 10693739) B10693739
theorem B76044365 : Blo 2249435 76044365 := bstep (se 3 (by rfl) ⟨14258318, by rfl⟩ : syracuseStep 76044365 = 28516637) B28516637
theorem B50696243 : Blo 2249435 50696243 := bstep (se 1 (by rfl) ⟨38022182, by rfl⟩ : syracuseStep 50696243 = 76044365) B76044365
theorem B33797495 : Blo 2249435 33797495 := bstep (se 1 (by rfl) ⟨25348121, by rfl⟩ : syracuseStep 33797495 = 50696243) B50696243
theorem B22531663 : Blo 2249435 22531663 := bstep (se 1 (by rfl) ⟨16898747, by rfl⟩ : syracuseStep 22531663 = 33797495) B33797495
theorem B30042217 : Blo 2249435 30042217 := bstep (se 2 (by rfl) ⟨11265831, by rfl⟩ : syracuseStep 30042217 = 22531663) B22531663
theorem B40056289 : Blo 2249435 40056289 := bstep (se 2 (by rfl) ⟨15021108, by rfl⟩ : syracuseStep 40056289 = 30042217) B30042217
theorem B213633541 : Blo 2249435 213633541 := bstep (se 4 (by rfl) ⟨20028144, by rfl⟩ : syracuseStep 213633541 = 40056289) B40056289
theorem B284844721 : Blo 2249435 284844721 := bstep (se 2 (by rfl) ⟨106816770, by rfl⟩ : syracuseStep 284844721 = 213633541) B213633541
theorem B379792961 : Blo 2249435 379792961 := bstep (se 2 (by rfl) ⟨142422360, by rfl⟩ : syracuseStep 379792961 = 284844721) B284844721
theorem B253195307 : Blo 2249435 253195307 := bstep (se 1 (by rfl) ⟨189896480, by rfl⟩ : syracuseStep 253195307 = 379792961) B379792961
theorem B168796871 : Blo 2249435 168796871 := bstep (se 1 (by rfl) ⟨126597653, by rfl⟩ : syracuseStep 168796871 = 253195307) B253195307
theorem B112531247 : Blo 2249435 112531247 := bstep (se 1 (by rfl) ⟨84398435, by rfl⟩ : syracuseStep 112531247 = 168796871) B168796871
theorem B75020831 : Blo 2249435 75020831 := bstep (se 1 (by rfl) ⟨56265623, by rfl⟩ : syracuseStep 75020831 = 112531247) B112531247
theorem B50013887 : Blo 2249435 50013887 := bstep (se 1 (by rfl) ⟨37510415, by rfl⟩ : syracuseStep 50013887 = 75020831) B75020831
theorem B533481461 : Blo 2249435 533481461 := bstep (se 5 (by rfl) ⟨25006943, by rfl⟩ : syracuseStep 533481461 = 50013887) B50013887
theorem B355654307 : Blo 2249435 355654307 := bstep (se 1 (by rfl) ⟨266740730, by rfl⟩ : syracuseStep 355654307 = 533481461) B533481461
theorem B237102871 : Blo 2249435 237102871 := bstep (se 1 (by rfl) ⟨177827153, by rfl⟩ : syracuseStep 237102871 = 355654307) B355654307
theorem B316137161 : Blo 2249435 316137161 := bstep (se 2 (by rfl) ⟨118551435, by rfl⟩ : syracuseStep 316137161 = 237102871) B237102871
theorem B210758107 : Blo 2249435 210758107 := bstep (se 1 (by rfl) ⟨158068580, by rfl⟩ : syracuseStep 210758107 = 316137161) B316137161
theorem B281010809 : Blo 2249435 281010809 := bstep (se 2 (by rfl) ⟨105379053, by rfl⟩ : syracuseStep 281010809 = 210758107) B210758107
theorem B187340539 : Blo 2249435 187340539 := bstep (se 1 (by rfl) ⟨140505404, by rfl⟩ : syracuseStep 187340539 = 281010809) B281010809
theorem B249787385 : Blo 2249435 249787385 := bstep (se 2 (by rfl) ⟨93670269, by rfl⟩ : syracuseStep 249787385 = 187340539) B187340539
theorem B166524923 : Blo 2249435 166524923 := bstep (se 1 (by rfl) ⟨124893692, by rfl⟩ : syracuseStep 166524923 = 249787385) B249787385
theorem B111016615 : Blo 2249435 111016615 := bstep (se 1 (by rfl) ⟨83262461, by rfl⟩ : syracuseStep 111016615 = 166524923) B166524923
theorem B148022153 : Blo 2249435 148022153 := bstep (se 2 (by rfl) ⟨55508307, by rfl⟩ : syracuseStep 148022153 = 111016615) B111016615
theorem B98681435 : Blo 2249435 98681435 := bstep (se 1 (by rfl) ⟨74011076, by rfl⟩ : syracuseStep 98681435 = 148022153) B148022153
theorem B65787623 : Blo 2249435 65787623 := bstep (se 1 (by rfl) ⟨49340717, by rfl⟩ : syracuseStep 65787623 = 98681435) B98681435
theorem B43858415 : Blo 2249435 43858415 := bstep (se 1 (by rfl) ⟨32893811, by rfl⟩ : syracuseStep 43858415 = 65787623) B65787623
theorem B29238943 : Blo 2249435 29238943 := bstep (se 1 (by rfl) ⟨21929207, by rfl⟩ : syracuseStep 29238943 = 43858415) B43858415
theorem B38985257 : Blo 2249435 38985257 := bstep (se 2 (by rfl) ⟨14619471, by rfl⟩ : syracuseStep 38985257 = 29238943) B29238943
theorem B103960685 : Blo 2249435 103960685 := bstep (se 3 (by rfl) ⟨19492628, by rfl⟩ : syracuseStep 103960685 = 38985257) B38985257
theorem B277228493 : Blo 2249435 277228493 := bstep (se 3 (by rfl) ⟨51980342, by rfl⟩ : syracuseStep 277228493 = 103960685) B103960685
theorem B184818995 : Blo 2249435 184818995 := bstep (se 1 (by rfl) ⟨138614246, by rfl⟩ : syracuseStep 184818995 = 277228493) B277228493
theorem B123212663 : Blo 2249435 123212663 := bstep (se 1 (by rfl) ⟨92409497, by rfl⟩ : syracuseStep 123212663 = 184818995) B184818995
theorem B82141775 : Blo 2249435 82141775 := bstep (se 1 (by rfl) ⟨61606331, by rfl⟩ : syracuseStep 82141775 = 123212663) B123212663
theorem B54761183 : Blo 2249435 54761183 := bstep (se 1 (by rfl) ⟨41070887, by rfl⟩ : syracuseStep 54761183 = 82141775) B82141775
theorem B36507455 : Blo 2249435 36507455 := bstep (se 1 (by rfl) ⟨27380591, by rfl⟩ : syracuseStep 36507455 = 54761183) B54761183
theorem B24338303 : Blo 2249435 24338303 := bstep (se 1 (by rfl) ⟨18253727, by rfl⟩ : syracuseStep 24338303 = 36507455) B36507455
theorem B16225535 : Blo 2249435 16225535 := bstep (se 1 (by rfl) ⟨12169151, by rfl⟩ : syracuseStep 16225535 = 24338303) B24338303
theorem B10817023 : Blo 2249435 10817023 := bstep (se 1 (by rfl) ⟨8112767, by rfl⟩ : syracuseStep 10817023 = 16225535) B16225535
theorem B14422697 : Blo 2249435 14422697 := bstep (se 2 (by rfl) ⟨5408511, by rfl⟩ : syracuseStep 14422697 = 10817023) B10817023
theorem B9615131 : Blo 2249435 9615131 := bstep (se 1 (by rfl) ⟨7211348, by rfl⟩ : syracuseStep 9615131 = 14422697) B14422697
theorem B6410087 : Blo 2249435 6410087 := bstep (se 1 (by rfl) ⟨4807565, by rfl⟩ : syracuseStep 6410087 = 9615131) B9615131
theorem B4273391 : Blo 2249435 4273391 := bstep (se 1 (by rfl) ⟨3205043, by rfl⟩ : syracuseStep 4273391 = 6410087) B6410087
theorem B2848927 : Blo 2249435 2848927 := bstep (se 1 (by rfl) ⟨2136695, by rfl⟩ : syracuseStep 2848927 = 4273391) B4273391
theorem B3798569 : Blo 2249435 3798569 := bstep (se 2 (by rfl) ⟨1424463, by rfl⟩ : syracuseStep 3798569 = 2848927) B2848927
theorem B2532379 : Blo 2249435 2532379 := bstep (se 1 (by rfl) ⟨1899284, by rfl⟩ : syracuseStep 2532379 = 3798569) B3798569
theorem B3376505 : Blo 2249435 3376505 := bstep (se 2 (by rfl) ⟨1266189, by rfl⟩ : syracuseStep 3376505 = 2532379) B2532379
theorem B2251003 : Blo 2249435 2251003 := bstep (se 1 (by rfl) ⟨1688252, by rfl⟩ : syracuseStep 2251003 = 3376505) B3376505
theorem B5133869 : Blo 2249435 5133869 := bbase (se 3 (by rfl) ⟨962600, by rfl⟩ : syracuseStep 5133869 = 1925201) (by norm_num)
theorem B3422579 : Blo 2249435 3422579 := bstep (se 1 (by rfl) ⟨2566934, by rfl⟩ : syracuseStep 3422579 = 5133869) B5133869
theorem B36507509 : Blo 2249435 36507509 := bstep (se 5 (by rfl) ⟨1711289, by rfl⟩ : syracuseStep 36507509 = 3422579) B3422579
theorem B24338339 : Blo 2249435 24338339 := bstep (se 1 (by rfl) ⟨18253754, by rfl⟩ : syracuseStep 24338339 = 36507509) B36507509
theorem B16225559 : Blo 2249435 16225559 := bstep (se 1 (by rfl) ⟨12169169, by rfl⟩ : syracuseStep 16225559 = 24338339) B24338339
theorem B10817039 : Blo 2249435 10817039 := bstep (se 1 (by rfl) ⟨8112779, by rfl⟩ : syracuseStep 10817039 = 16225559) B16225559
theorem B7211359 : Blo 2249435 7211359 := bstep (se 1 (by rfl) ⟨5408519, by rfl⟩ : syracuseStep 7211359 = 10817039) B10817039
theorem B38460581 : Blo 2249435 38460581 := bstep (se 4 (by rfl) ⟨3605679, by rfl⟩ : syracuseStep 38460581 = 7211359) B7211359
theorem B25640387 : Blo 2249435 25640387 := bstep (se 1 (by rfl) ⟨19230290, by rfl⟩ : syracuseStep 25640387 = 38460581) B38460581
theorem B17093591 : Blo 2249435 17093591 := bstep (se 1 (by rfl) ⟨12820193, by rfl⟩ : syracuseStep 17093591 = 25640387) B25640387
theorem B11395727 : Blo 2249435 11395727 := bstep (se 1 (by rfl) ⟨8546795, by rfl⟩ : syracuseStep 11395727 = 17093591) B17093591
theorem B7597151 : Blo 2249435 7597151 := bstep (se 1 (by rfl) ⟨5697863, by rfl⟩ : syracuseStep 7597151 = 11395727) B11395727
theorem B5064767 : Blo 2249435 5064767 := bstep (se 1 (by rfl) ⟨3798575, by rfl⟩ : syracuseStep 5064767 = 7597151) B7597151
theorem B3376511 : Blo 2249435 3376511 := bstep (se 1 (by rfl) ⟨2532383, by rfl⟩ : syracuseStep 3376511 = 5064767) B5064767
theorem B2251007 : Blo 2249435 2251007 := bstep (se 1 (by rfl) ⟨1688255, by rfl⟩ : syracuseStep 2251007 = 3376511) B3376511
theorem B3376517 : Blo 2249435 3376517 := bbase (se 4 (by rfl) ⟨316548, by rfl⟩ : syracuseStep 3376517 = 633097) (by norm_num)
theorem B2251011 : Blo 2249435 2251011 := bstep (se 1 (by rfl) ⟨1688258, by rfl⟩ : syracuseStep 2251011 = 3376517) B3376517
theorem B3798589 : Blo 2249435 3798589 := bbase (se 3 (by rfl) ⟨712235, by rfl⟩ : syracuseStep 3798589 = 1424471) (by norm_num)
theorem B5064785 : Blo 2249435 5064785 := bstep (se 2 (by rfl) ⟨1899294, by rfl⟩ : syracuseStep 5064785 = 3798589) B3798589
theorem B3376523 : Blo 2249435 3376523 := bstep (se 1 (by rfl) ⟨2532392, by rfl⟩ : syracuseStep 3376523 = 5064785) B5064785
theorem B2251015 : Blo 2249435 2251015 := bstep (se 1 (by rfl) ⟨1688261, by rfl⟩ : syracuseStep 2251015 = 3376523) B3376523
theorem B2532397 : Blo 2249435 2532397 := bbase (se 3 (by rfl) ⟨474824, by rfl⟩ : syracuseStep 2532397 = 949649) (by norm_num)
theorem B3376529 : Blo 2249435 3376529 := bstep (se 2 (by rfl) ⟨1266198, by rfl⟩ : syracuseStep 3376529 = 2532397) B2532397
theorem B2251019 : Blo 2249435 2251019 := bstep (se 1 (by rfl) ⟨1688264, by rfl⟩ : syracuseStep 2251019 = 3376529) B3376529
theorem B7597205 : Blo 2249435 7597205 := bbase (se 6 (by rfl) ⟨178059, by rfl⟩ : syracuseStep 7597205 = 356119) (by norm_num)
theorem B5064803 : Blo 2249435 5064803 := bstep (se 1 (by rfl) ⟨3798602, by rfl⟩ : syracuseStep 5064803 = 7597205) B7597205
theorem B3376535 : Blo 2249435 3376535 := bstep (se 1 (by rfl) ⟨2532401, by rfl⟩ : syracuseStep 3376535 = 5064803) B5064803
theorem B2251023 : Blo 2249435 2251023 := bstep (se 1 (by rfl) ⟨1688267, by rfl⟩ : syracuseStep 2251023 = 3376535) B3376535
theorem B3376541 : Blo 2249435 3376541 := bbase (se 3 (by rfl) ⟨633101, by rfl⟩ : syracuseStep 3376541 = 1266203) (by norm_num)
theorem B2251027 : Blo 2249435 2251027 := bstep (se 1 (by rfl) ⟨1688270, by rfl⟩ : syracuseStep 2251027 = 3376541) B3376541
theorem B5064821 : Blo 2249435 5064821 := bbase (se 5 (by rfl) ⟨237413, by rfl⟩ : syracuseStep 5064821 = 474827) (by norm_num)
theorem B3376547 : Blo 2249435 3376547 := bstep (se 1 (by rfl) ⟨2532410, by rfl⟩ : syracuseStep 3376547 = 5064821) B5064821
theorem B2251031 : Blo 2249435 2251031 := bstep (se 1 (by rfl) ⟨1688273, by rfl⟩ : syracuseStep 2251031 = 3376547) B3376547
theorem B3605725 : Blo 2249435 3605725 := bbase (se 3 (by rfl) ⟨676073, by rfl⟩ : syracuseStep 3605725 = 1352147) (by norm_num)
theorem B19230533 : Blo 2249435 19230533 := bstep (se 4 (by rfl) ⟨1802862, by rfl⟩ : syracuseStep 19230533 = 3605725) B3605725
theorem B12820355 : Blo 2249435 12820355 := bstep (se 1 (by rfl) ⟨9615266, by rfl⟩ : syracuseStep 12820355 = 19230533) B19230533
theorem B8546903 : Blo 2249435 8546903 := bstep (se 1 (by rfl) ⟨6410177, by rfl⟩ : syracuseStep 8546903 = 12820355) B12820355
theorem B5697935 : Blo 2249435 5697935 := bstep (se 1 (by rfl) ⟨4273451, by rfl⟩ : syracuseStep 5697935 = 8546903) B8546903
theorem B3798623 : Blo 2249435 3798623 := bstep (se 1 (by rfl) ⟨2848967, by rfl⟩ : syracuseStep 3798623 = 5697935) B5697935
theorem B2532415 : Blo 2249435 2532415 := bstep (se 1 (by rfl) ⟨1899311, by rfl⟩ : syracuseStep 2532415 = 3798623) B3798623
theorem B3376553 : Blo 2249435 3376553 := bstep (se 2 (by rfl) ⟨1266207, by rfl⟩ : syracuseStep 3376553 = 2532415) B2532415
theorem B2251035 : Blo 2249435 2251035 := bstep (se 1 (by rfl) ⟨1688276, by rfl⟩ : syracuseStep 2251035 = 3376553) B3376553
theorem B8546917 : Blo 2249435 8546917 := bbase (se 4 (by rfl) ⟨801273, by rfl⟩ : syracuseStep 8546917 = 1602547) (by norm_num)
theorem B11395889 : Blo 2249435 11395889 := bstep (se 2 (by rfl) ⟨4273458, by rfl⟩ : syracuseStep 11395889 = 8546917) B8546917
theorem B7597259 : Blo 2249435 7597259 := bstep (se 1 (by rfl) ⟨5697944, by rfl⟩ : syracuseStep 7597259 = 11395889) B11395889
theorem B5064839 : Blo 2249435 5064839 := bstep (se 1 (by rfl) ⟨3798629, by rfl⟩ : syracuseStep 5064839 = 7597259) B7597259
theorem B3376559 : Blo 2249435 3376559 := bstep (se 1 (by rfl) ⟨2532419, by rfl⟩ : syracuseStep 3376559 = 5064839) B5064839
theorem B2251039 : Blo 2249435 2251039 := bstep (se 1 (by rfl) ⟨1688279, by rfl⟩ : syracuseStep 2251039 = 3376559) B3376559
theorem B3376565 : Blo 2249435 3376565 := bbase (se 5 (by rfl) ⟨158276, by rfl⟩ : syracuseStep 3376565 = 316553) (by norm_num)
theorem B2251043 : Blo 2249435 2251043 := bstep (se 1 (by rfl) ⟨1688282, by rfl⟩ : syracuseStep 2251043 = 3376565) B3376565
theorem B5697965 : Blo 2249435 5697965 := bbase (se 3 (by rfl) ⟨1068368, by rfl⟩ : syracuseStep 5697965 = 2136737) (by norm_num)
theorem B3798643 : Blo 2249435 3798643 := bstep (se 1 (by rfl) ⟨2848982, by rfl⟩ : syracuseStep 3798643 = 5697965) B5697965
theorem B5064857 : Blo 2249435 5064857 := bstep (se 2 (by rfl) ⟨1899321, by rfl⟩ : syracuseStep 5064857 = 3798643) B3798643
theorem B3376571 : Blo 2249435 3376571 := bstep (se 1 (by rfl) ⟨2532428, by rfl⟩ : syracuseStep 3376571 = 5064857) B5064857
theorem B2251047 : Blo 2249435 2251047 := bstep (se 1 (by rfl) ⟨1688285, by rfl⟩ : syracuseStep 2251047 = 3376571) B3376571
theorem B2532433 : Blo 2249435 2532433 := bbase (se 2 (by rfl) ⟨949662, by rfl⟩ : syracuseStep 2532433 = 1899325) (by norm_num)
theorem B3376577 : Blo 2249435 3376577 := bstep (se 2 (by rfl) ⟨1266216, by rfl⟩ : syracuseStep 3376577 = 2532433) B2532433
theorem B2251051 : Blo 2249435 2251051 := bstep (se 1 (by rfl) ⟨1688288, by rfl⟩ : syracuseStep 2251051 = 3376577) B3376577
theorem B3205117 : Blo 2249435 3205117 := bbase (se 3 (by rfl) ⟨600959, by rfl⟩ : syracuseStep 3205117 = 1201919) (by norm_num)
theorem B4273489 : Blo 2249435 4273489 := bstep (se 2 (by rfl) ⟨1602558, by rfl⟩ : syracuseStep 4273489 = 3205117) B3205117
theorem B5697985 : Blo 2249435 5697985 := bstep (se 2 (by rfl) ⟨2136744, by rfl⟩ : syracuseStep 5697985 = 4273489) B4273489
theorem B7597313 : Blo 2249435 7597313 := bstep (se 2 (by rfl) ⟨2848992, by rfl⟩ : syracuseStep 7597313 = 5697985) B5697985
theorem B5064875 : Blo 2249435 5064875 := bstep (se 1 (by rfl) ⟨3798656, by rfl⟩ : syracuseStep 5064875 = 7597313) B7597313
theorem B3376583 : Blo 2249435 3376583 := bstep (se 1 (by rfl) ⟨2532437, by rfl⟩ : syracuseStep 3376583 = 5064875) B5064875
theorem B2251055 : Blo 2249435 2251055 := bstep (se 1 (by rfl) ⟨1688291, by rfl⟩ : syracuseStep 2251055 = 3376583) B3376583
theorem B3376589 : Blo 2249435 3376589 := bbase (se 3 (by rfl) ⟨633110, by rfl⟩ : syracuseStep 3376589 = 1266221) (by norm_num)
theorem B2251059 : Blo 2249435 2251059 := bstep (se 1 (by rfl) ⟨1688294, by rfl⟩ : syracuseStep 2251059 = 3376589) B3376589
theorem B5064893 : Blo 2249435 5064893 := bbase (se 3 (by rfl) ⟨949667, by rfl⟩ : syracuseStep 5064893 = 1899335) (by norm_num)
theorem B3376595 : Blo 2249435 3376595 := bstep (se 1 (by rfl) ⟨2532446, by rfl⟩ : syracuseStep 3376595 = 5064893) B5064893
theorem B2251063 : Blo 2249435 2251063 := bstep (se 1 (by rfl) ⟨1688297, by rfl⟩ : syracuseStep 2251063 = 3376595) B3376595
theorem B3798677 : Blo 2249435 3798677 := bbase (se 6 (by rfl) ⟨89031, by rfl⟩ : syracuseStep 3798677 = 178063) (by norm_num)
theorem B2532451 : Blo 2249435 2532451 := bstep (se 1 (by rfl) ⟨1899338, by rfl⟩ : syracuseStep 2532451 = 3798677) B3798677
theorem B3376601 : Blo 2249435 3376601 := bstep (se 2 (by rfl) ⟨1266225, by rfl⟩ : syracuseStep 3376601 = 2532451) B2532451
theorem B2251067 : Blo 2249435 2251067 := bstep (se 1 (by rfl) ⟨1688300, by rfl⟩ : syracuseStep 2251067 = 3376601) B3376601
theorem B3422677 : Blo 2249435 3422677 := bbase (se 7 (by rfl) ⟨40109, by rfl⟩ : syracuseStep 3422677 = 80219) (by norm_num)
theorem B4563569 : Blo 2249435 4563569 := bstep (se 2 (by rfl) ⟨1711338, by rfl⟩ : syracuseStep 4563569 = 3422677) B3422677
theorem B3042379 : Blo 2249435 3042379 := bstep (se 1 (by rfl) ⟨2281784, by rfl⟩ : syracuseStep 3042379 = 4563569) B4563569
theorem B16226021 : Blo 2249435 16226021 := bstep (se 4 (by rfl) ⟨1521189, by rfl⟩ : syracuseStep 16226021 = 3042379) B3042379
theorem B10817347 : Blo 2249435 10817347 := bstep (se 1 (by rfl) ⟨8113010, by rfl⟩ : syracuseStep 10817347 = 16226021) B16226021
theorem B14423129 : Blo 2249435 14423129 := bstep (se 2 (by rfl) ⟨5408673, by rfl⟩ : syracuseStep 14423129 = 10817347) B10817347
theorem B9615419 : Blo 2249435 9615419 := bstep (se 1 (by rfl) ⟨7211564, by rfl⟩ : syracuseStep 9615419 = 14423129) B14423129
theorem B6410279 : Blo 2249435 6410279 := bstep (se 1 (by rfl) ⟨4807709, by rfl⟩ : syracuseStep 6410279 = 9615419) B9615419
theorem B17094077 : Blo 2249435 17094077 := bstep (se 3 (by rfl) ⟨3205139, by rfl⟩ : syracuseStep 17094077 = 6410279) B6410279
theorem B11396051 : Blo 2249435 11396051 := bstep (se 1 (by rfl) ⟨8547038, by rfl⟩ : syracuseStep 11396051 = 17094077) B17094077
theorem B7597367 : Blo 2249435 7597367 := bstep (se 1 (by rfl) ⟨5698025, by rfl⟩ : syracuseStep 7597367 = 11396051) B11396051
theorem B5064911 : Blo 2249435 5064911 := bstep (se 1 (by rfl) ⟨3798683, by rfl⟩ : syracuseStep 5064911 = 7597367) B7597367
theorem B3376607 : Blo 2249435 3376607 := bstep (se 1 (by rfl) ⟨2532455, by rfl⟩ : syracuseStep 3376607 = 5064911) B5064911
theorem B2251071 : Blo 2249435 2251071 := bstep (se 1 (by rfl) ⟨1688303, by rfl⟩ : syracuseStep 2251071 = 3376607) B3376607
theorem B3376613 : Blo 2249435 3376613 := bbase (se 4 (by rfl) ⟨316557, by rfl⟩ : syracuseStep 3376613 = 633115) (by norm_num)
theorem B2251075 : Blo 2249435 2251075 := bstep (se 1 (by rfl) ⟨1688306, by rfl⟩ : syracuseStep 2251075 = 3376613) B3376613
theorem B2567017 : Blo 2249435 2567017 := bbase (se 2 (by rfl) ⟨962631, by rfl⟩ : syracuseStep 2567017 = 1925263) (by norm_num)
theorem B13690757 : Blo 2249435 13690757 := bstep (se 4 (by rfl) ⟨1283508, by rfl⟩ : syracuseStep 13690757 = 2567017) B2567017
theorem B9127171 : Blo 2249435 9127171 := bstep (se 1 (by rfl) ⟨6845378, by rfl⟩ : syracuseStep 9127171 = 13690757) B13690757
theorem B48678245 : Blo 2249435 48678245 := bstep (se 4 (by rfl) ⟨4563585, by rfl⟩ : syracuseStep 48678245 = 9127171) B9127171
theorem B32452163 : Blo 2249435 32452163 := bstep (se 1 (by rfl) ⟨24339122, by rfl⟩ : syracuseStep 32452163 = 48678245) B48678245
theorem B21634775 : Blo 2249435 21634775 := bstep (se 1 (by rfl) ⟨16226081, by rfl⟩ : syracuseStep 21634775 = 32452163) B32452163
theorem B14423183 : Blo 2249435 14423183 := bstep (se 1 (by rfl) ⟨10817387, by rfl⟩ : syracuseStep 14423183 = 21634775) B21634775
theorem B9615455 : Blo 2249435 9615455 := bstep (se 1 (by rfl) ⟨7211591, by rfl⟩ : syracuseStep 9615455 = 14423183) B14423183
theorem B6410303 : Blo 2249435 6410303 := bstep (se 1 (by rfl) ⟨4807727, by rfl⟩ : syracuseStep 6410303 = 9615455) B9615455
theorem B4273535 : Blo 2249435 4273535 := bstep (se 1 (by rfl) ⟨3205151, by rfl⟩ : syracuseStep 4273535 = 6410303) B6410303
theorem B2849023 : Blo 2249435 2849023 := bstep (se 1 (by rfl) ⟨2136767, by rfl⟩ : syracuseStep 2849023 = 4273535) B4273535
theorem B3798697 : Blo 2249435 3798697 := bstep (se 2 (by rfl) ⟨1424511, by rfl⟩ : syracuseStep 3798697 = 2849023) B2849023
theorem B5064929 : Blo 2249435 5064929 := bstep (se 2 (by rfl) ⟨1899348, by rfl⟩ : syracuseStep 5064929 = 3798697) B3798697
theorem B3376619 : Blo 2249435 3376619 := bstep (se 1 (by rfl) ⟨2532464, by rfl⟩ : syracuseStep 3376619 = 5064929) B5064929
theorem B2251079 : Blo 2249435 2251079 := bstep (se 1 (by rfl) ⟨1688309, by rfl⟩ : syracuseStep 2251079 = 3376619) B3376619
theorem B2532469 : Blo 2249435 2532469 := bbase (se 5 (by rfl) ⟨118709, by rfl⟩ : syracuseStep 2532469 = 237419) (by norm_num)
theorem B3376625 : Blo 2249435 3376625 := bstep (se 2 (by rfl) ⟨1266234, by rfl⟩ : syracuseStep 3376625 = 2532469) B2532469
theorem B2251083 : Blo 2249435 2251083 := bstep (se 1 (by rfl) ⟨1688312, by rfl⟩ : syracuseStep 2251083 = 3376625) B3376625
theorem B2849033 : Blo 2249435 2849033 := bbase (se 2 (by rfl) ⟨1068387, by rfl⟩ : syracuseStep 2849033 = 2136775) (by norm_num)
theorem B7597421 : Blo 2249435 7597421 := bstep (se 3 (by rfl) ⟨1424516, by rfl⟩ : syracuseStep 7597421 = 2849033) B2849033
theorem B5064947 : Blo 2249435 5064947 := bstep (se 1 (by rfl) ⟨3798710, by rfl⟩ : syracuseStep 5064947 = 7597421) B7597421
theorem B3376631 : Blo 2249435 3376631 := bstep (se 1 (by rfl) ⟨2532473, by rfl⟩ : syracuseStep 3376631 = 5064947) B5064947
theorem B2251087 : Blo 2249435 2251087 := bstep (se 1 (by rfl) ⟨1688315, by rfl⟩ : syracuseStep 2251087 = 3376631) B3376631
theorem B3376637 : Blo 2249435 3376637 := bbase (se 3 (by rfl) ⟨633119, by rfl⟩ : syracuseStep 3376637 = 1266239) (by norm_num)
theorem B2251091 : Blo 2249435 2251091 := bstep (se 1 (by rfl) ⟨1688318, by rfl⟩ : syracuseStep 2251091 = 3376637) B3376637
theorem B5064965 : Blo 2249435 5064965 := bbase (se 4 (by rfl) ⟨474840, by rfl⟩ : syracuseStep 5064965 = 949681) (by norm_num)
theorem B3376643 : Blo 2249435 3376643 := bstep (se 1 (by rfl) ⟨2532482, by rfl⟩ : syracuseStep 3376643 = 5064965) B5064965
theorem B2251095 : Blo 2249435 2251095 := bstep (se 1 (by rfl) ⟨1688321, by rfl⟩ : syracuseStep 2251095 = 3376643) B3376643
theorem B4273573 : Blo 2249435 4273573 := bbase (se 4 (by rfl) ⟨400647, by rfl⟩ : syracuseStep 4273573 = 801295) (by norm_num)
theorem B5698097 : Blo 2249435 5698097 := bstep (se 2 (by rfl) ⟨2136786, by rfl⟩ : syracuseStep 5698097 = 4273573) B4273573
theorem B3798731 : Blo 2249435 3798731 := bstep (se 1 (by rfl) ⟨2849048, by rfl⟩ : syracuseStep 3798731 = 5698097) B5698097
theorem B2532487 : Blo 2249435 2532487 := bstep (se 1 (by rfl) ⟨1899365, by rfl⟩ : syracuseStep 2532487 = 3798731) B3798731
theorem B3376649 : Blo 2249435 3376649 := bstep (se 2 (by rfl) ⟨1266243, by rfl⟩ : syracuseStep 3376649 = 2532487) B2532487
theorem B2251099 : Blo 2249435 2251099 := bstep (se 1 (by rfl) ⟨1688324, by rfl⟩ : syracuseStep 2251099 = 3376649) B3376649
theorem B11396213 : Blo 2249435 11396213 := bbase (se 5 (by rfl) ⟨534197, by rfl⟩ : syracuseStep 11396213 = 1068395) (by norm_num)
theorem B7597475 : Blo 2249435 7597475 := bstep (se 1 (by rfl) ⟨5698106, by rfl⟩ : syracuseStep 7597475 = 11396213) B11396213
theorem B5064983 : Blo 2249435 5064983 := bstep (se 1 (by rfl) ⟨3798737, by rfl⟩ : syracuseStep 5064983 = 7597475) B7597475
theorem B3376655 : Blo 2249435 3376655 := bstep (se 1 (by rfl) ⟨2532491, by rfl⟩ : syracuseStep 3376655 = 5064983) B5064983
theorem B2251103 : Blo 2249435 2251103 := bstep (se 1 (by rfl) ⟨1688327, by rfl⟩ : syracuseStep 2251103 = 3376655) B3376655
theorem B3376661 : Blo 2249435 3376661 := bbase (se 6 (by rfl) ⟨79140, by rfl⟩ : syracuseStep 3376661 = 158281) (by norm_num)
theorem B2251107 : Blo 2249435 2251107 := bstep (se 1 (by rfl) ⟨1688330, by rfl⟩ : syracuseStep 2251107 = 3376661) B3376661
theorem B2704385 : Blo 2249435 2704385 := bbase (se 2 (by rfl) ⟨1014144, by rfl⟩ : syracuseStep 2704385 = 2028289) (by norm_num)
theorem B7211693 : Blo 2249435 7211693 := bstep (se 3 (by rfl) ⟨1352192, by rfl⟩ : syracuseStep 7211693 = 2704385) B2704385
theorem B19231181 : Blo 2249435 19231181 := bstep (se 3 (by rfl) ⟨3605846, by rfl⟩ : syracuseStep 19231181 = 7211693) B7211693
theorem B12820787 : Blo 2249435 12820787 := bstep (se 1 (by rfl) ⟨9615590, by rfl⟩ : syracuseStep 12820787 = 19231181) B19231181
theorem B8547191 : Blo 2249435 8547191 := bstep (se 1 (by rfl) ⟨6410393, by rfl⟩ : syracuseStep 8547191 = 12820787) B12820787
theorem B5698127 : Blo 2249435 5698127 := bstep (se 1 (by rfl) ⟨4273595, by rfl⟩ : syracuseStep 5698127 = 8547191) B8547191
theorem B3798751 : Blo 2249435 3798751 := bstep (se 1 (by rfl) ⟨2849063, by rfl⟩ : syracuseStep 3798751 = 5698127) B5698127
theorem B5065001 : Blo 2249435 5065001 := bstep (se 2 (by rfl) ⟨1899375, by rfl⟩ : syracuseStep 5065001 = 3798751) B3798751
theorem B3376667 : Blo 2249435 3376667 := bstep (se 1 (by rfl) ⟨2532500, by rfl⟩ : syracuseStep 3376667 = 5065001) B5065001
theorem B2251111 : Blo 2249435 2251111 := bstep (se 1 (by rfl) ⟨1688333, by rfl⟩ : syracuseStep 2251111 = 3376667) B3376667
theorem B2532505 : Blo 2249435 2532505 := bbase (se 2 (by rfl) ⟨949689, by rfl⟩ : syracuseStep 2532505 = 1899379) (by norm_num)
theorem B3376673 : Blo 2249435 3376673 := bstep (se 2 (by rfl) ⟨1266252, by rfl⟩ : syracuseStep 3376673 = 2532505) B2532505
theorem B2251115 : Blo 2249435 2251115 := bstep (se 1 (by rfl) ⟨1688336, by rfl⟩ : syracuseStep 2251115 = 3376673) B3376673
theorem B8547221 : Blo 2249435 8547221 := bbase (se 6 (by rfl) ⟨200325, by rfl⟩ : syracuseStep 8547221 = 400651) (by norm_num)
theorem B5698147 : Blo 2249435 5698147 := bstep (se 1 (by rfl) ⟨4273610, by rfl⟩ : syracuseStep 5698147 = 8547221) B8547221
theorem B7597529 : Blo 2249435 7597529 := bstep (se 2 (by rfl) ⟨2849073, by rfl⟩ : syracuseStep 7597529 = 5698147) B5698147
theorem B5065019 : Blo 2249435 5065019 := bstep (se 1 (by rfl) ⟨3798764, by rfl⟩ : syracuseStep 5065019 = 7597529) B7597529
theorem B3376679 : Blo 2249435 3376679 := bstep (se 1 (by rfl) ⟨2532509, by rfl⟩ : syracuseStep 3376679 = 5065019) B5065019
theorem B2251119 : Blo 2249435 2251119 := bstep (se 1 (by rfl) ⟨1688339, by rfl⟩ : syracuseStep 2251119 = 3376679) B3376679
theorem B3376685 : Blo 2249435 3376685 := bbase (se 3 (by rfl) ⟨633128, by rfl⟩ : syracuseStep 3376685 = 1266257) (by norm_num)
theorem B2251123 : Blo 2249435 2251123 := bstep (se 1 (by rfl) ⟨1688342, by rfl⟩ : syracuseStep 2251123 = 3376685) B3376685
theorem B5065037 : Blo 2249435 5065037 := bbase (se 3 (by rfl) ⟨949694, by rfl⟩ : syracuseStep 5065037 = 1899389) (by norm_num)
theorem B3376691 : Blo 2249435 3376691 := bstep (se 1 (by rfl) ⟨2532518, by rfl⟩ : syracuseStep 3376691 = 5065037) B5065037
theorem B2251127 : Blo 2249435 2251127 := bstep (se 1 (by rfl) ⟨1688345, by rfl⟩ : syracuseStep 2251127 = 3376691) B3376691
theorem B2849089 : Blo 2249435 2849089 := bbase (se 2 (by rfl) ⟨1068408, by rfl⟩ : syracuseStep 2849089 = 2136817) (by norm_num)
theorem B3798785 : Blo 2249435 3798785 := bstep (se 2 (by rfl) ⟨1424544, by rfl⟩ : syracuseStep 3798785 = 2849089) B2849089
theorem B2532523 : Blo 2249435 2532523 := bstep (se 1 (by rfl) ⟨1899392, by rfl⟩ : syracuseStep 2532523 = 3798785) B3798785
theorem B3376697 : Blo 2249435 3376697 := bstep (se 2 (by rfl) ⟨1266261, by rfl⟩ : syracuseStep 3376697 = 2532523) B2532523
theorem B2251131 : Blo 2249435 2251131 := bstep (se 1 (by rfl) ⟨1688348, by rfl⟩ : syracuseStep 2251131 = 3376697) B3376697
theorem B3605885 : Blo 2249435 3605885 := bbase (se 3 (by rfl) ⟨676103, by rfl⟩ : syracuseStep 3605885 = 1352207) (by norm_num)
theorem B2403923 : Blo 2249435 2403923 := bstep (se 1 (by rfl) ⟨1802942, by rfl⟩ : syracuseStep 2403923 = 3605885) B3605885
theorem B25641845 : Blo 2249435 25641845 := bstep (se 5 (by rfl) ⟨1201961, by rfl⟩ : syracuseStep 25641845 = 2403923) B2403923
theorem B17094563 : Blo 2249435 17094563 := bstep (se 1 (by rfl) ⟨12820922, by rfl⟩ : syracuseStep 17094563 = 25641845) B25641845
theorem B11396375 : Blo 2249435 11396375 := bstep (se 1 (by rfl) ⟨8547281, by rfl⟩ : syracuseStep 11396375 = 17094563) B17094563
theorem B7597583 : Blo 2249435 7597583 := bstep (se 1 (by rfl) ⟨5698187, by rfl⟩ : syracuseStep 7597583 = 11396375) B11396375
theorem B5065055 : Blo 2249435 5065055 := bstep (se 1 (by rfl) ⟨3798791, by rfl⟩ : syracuseStep 5065055 = 7597583) B7597583
theorem B3376703 : Blo 2249435 3376703 := bstep (se 1 (by rfl) ⟨2532527, by rfl⟩ : syracuseStep 3376703 = 5065055) B5065055
theorem B2251135 : Blo 2249435 2251135 := bstep (se 1 (by rfl) ⟨1688351, by rfl⟩ : syracuseStep 2251135 = 3376703) B3376703
theorem B3376709 : Blo 2249435 3376709 := bbase (se 4 (by rfl) ⟨316566, by rfl⟩ : syracuseStep 3376709 = 633133) (by norm_num)
theorem B2251139 : Blo 2249435 2251139 := bstep (se 1 (by rfl) ⟨1688354, by rfl⟩ : syracuseStep 2251139 = 3376709) B3376709
theorem B3798805 : Blo 2249435 3798805 := bbase (se 6 (by rfl) ⟨89034, by rfl⟩ : syracuseStep 3798805 = 178069) (by norm_num)
theorem B5065073 : Blo 2249435 5065073 := bstep (se 2 (by rfl) ⟨1899402, by rfl⟩ : syracuseStep 5065073 = 3798805) B3798805
theorem B3376715 : Blo 2249435 3376715 := bstep (se 1 (by rfl) ⟨2532536, by rfl⟩ : syracuseStep 3376715 = 5065073) B5065073
theorem B2251143 : Blo 2249435 2251143 := bstep (se 1 (by rfl) ⟨1688357, by rfl⟩ : syracuseStep 2251143 = 3376715) B3376715
theorem B2532541 : Blo 2249435 2532541 := bbase (se 3 (by rfl) ⟨474851, by rfl⟩ : syracuseStep 2532541 = 949703) (by norm_num)
theorem B3376721 : Blo 2249435 3376721 := bstep (se 2 (by rfl) ⟨1266270, by rfl⟩ : syracuseStep 3376721 = 2532541) B2532541
theorem B2251147 : Blo 2249435 2251147 := bstep (se 1 (by rfl) ⟨1688360, by rfl⟩ : syracuseStep 2251147 = 3376721) B3376721
theorem B7597637 : Blo 2249435 7597637 := bbase (se 4 (by rfl) ⟨712278, by rfl⟩ : syracuseStep 7597637 = 1424557) (by norm_num)
theorem B5065091 : Blo 2249435 5065091 := bstep (se 1 (by rfl) ⟨3798818, by rfl⟩ : syracuseStep 5065091 = 7597637) B7597637
theorem B3376727 : Blo 2249435 3376727 := bstep (se 1 (by rfl) ⟨2532545, by rfl⟩ : syracuseStep 3376727 = 5065091) B5065091
theorem B2251151 : Blo 2249435 2251151 := bstep (se 1 (by rfl) ⟨1688363, by rfl⟩ : syracuseStep 2251151 = 3376727) B3376727
theorem B3376733 : Blo 2249435 3376733 := bbase (se 3 (by rfl) ⟨633137, by rfl⟩ : syracuseStep 3376733 = 1266275) (by norm_num)
theorem B2251155 : Blo 2249435 2251155 := bstep (se 1 (by rfl) ⟨1688366, by rfl⟩ : syracuseStep 2251155 = 3376733) B3376733
theorem B5065109 : Blo 2249435 5065109 := bbase (se 6 (by rfl) ⟨118713, by rfl⟩ : syracuseStep 5065109 = 237427) (by norm_num)
theorem B3376739 : Blo 2249435 3376739 := bstep (se 1 (by rfl) ⟨2532554, by rfl⟩ : syracuseStep 3376739 = 5065109) B5065109
theorem B2251159 : Blo 2249435 2251159 := bstep (se 1 (by rfl) ⟨1688369, by rfl⟩ : syracuseStep 2251159 = 3376739) B3376739
theorem B7211861 : Blo 2249435 7211861 := bbase (se 9 (by rfl) ⟨21128, by rfl⟩ : syracuseStep 7211861 = 42257) (by norm_num)
theorem B4807907 : Blo 2249435 4807907 := bstep (se 1 (by rfl) ⟨3605930, by rfl⟩ : syracuseStep 4807907 = 7211861) B7211861
theorem B3205271 : Blo 2249435 3205271 := bstep (se 1 (by rfl) ⟨2403953, by rfl⟩ : syracuseStep 3205271 = 4807907) B4807907
theorem B8547389 : Blo 2249435 8547389 := bstep (se 3 (by rfl) ⟨1602635, by rfl⟩ : syracuseStep 8547389 = 3205271) B3205271
theorem B5698259 : Blo 2249435 5698259 := bstep (se 1 (by rfl) ⟨4273694, by rfl⟩ : syracuseStep 5698259 = 8547389) B8547389
theorem B3798839 : Blo 2249435 3798839 := bstep (se 1 (by rfl) ⟨2849129, by rfl⟩ : syracuseStep 3798839 = 5698259) B5698259
theorem B2532559 : Blo 2249435 2532559 := bstep (se 1 (by rfl) ⟨1899419, by rfl⟩ : syracuseStep 2532559 = 3798839) B3798839
theorem B3376745 : Blo 2249435 3376745 := bstep (se 2 (by rfl) ⟨1266279, by rfl⟩ : syracuseStep 3376745 = 2532559) B2532559
theorem B2251163 : Blo 2249435 2251163 := bstep (se 1 (by rfl) ⟨1688372, by rfl⟩ : syracuseStep 2251163 = 3376745) B3376745
theorem B9615829 : Blo 2249435 9615829 := bbase (se 7 (by rfl) ⟨112685, by rfl⟩ : syracuseStep 9615829 = 225371) (by norm_num)
theorem B12821105 : Blo 2249435 12821105 := bstep (se 2 (by rfl) ⟨4807914, by rfl⟩ : syracuseStep 12821105 = 9615829) B9615829
theorem B8547403 : Blo 2249435 8547403 := bstep (se 1 (by rfl) ⟨6410552, by rfl⟩ : syracuseStep 8547403 = 12821105) B12821105
theorem B11396537 : Blo 2249435 11396537 := bstep (se 2 (by rfl) ⟨4273701, by rfl⟩ : syracuseStep 11396537 = 8547403) B8547403
theorem B7597691 : Blo 2249435 7597691 := bstep (se 1 (by rfl) ⟨5698268, by rfl⟩ : syracuseStep 7597691 = 11396537) B11396537
theorem B5065127 : Blo 2249435 5065127 := bstep (se 1 (by rfl) ⟨3798845, by rfl⟩ : syracuseStep 5065127 = 7597691) B7597691
theorem B3376751 : Blo 2249435 3376751 := bstep (se 1 (by rfl) ⟨2532563, by rfl⟩ : syracuseStep 3376751 = 5065127) B5065127
theorem B2251167 : Blo 2249435 2251167 := bstep (se 1 (by rfl) ⟨1688375, by rfl⟩ : syracuseStep 2251167 = 3376751) B3376751
theorem B3376757 : Blo 2249435 3376757 := bbase (se 5 (by rfl) ⟨158285, by rfl⟩ : syracuseStep 3376757 = 316571) (by norm_num)
theorem B2251171 : Blo 2249435 2251171 := bstep (se 1 (by rfl) ⟨1688378, by rfl⟩ : syracuseStep 2251171 = 3376757) B3376757
theorem B4273717 : Blo 2249435 4273717 := bbase (se 5 (by rfl) ⟨200330, by rfl⟩ : syracuseStep 4273717 = 400661) (by norm_num)
theorem B5698289 : Blo 2249435 5698289 := bstep (se 2 (by rfl) ⟨2136858, by rfl⟩ : syracuseStep 5698289 = 4273717) B4273717
theorem B3798859 : Blo 2249435 3798859 := bstep (se 1 (by rfl) ⟨2849144, by rfl⟩ : syracuseStep 3798859 = 5698289) B5698289
theorem B5065145 : Blo 2249435 5065145 := bstep (se 2 (by rfl) ⟨1899429, by rfl⟩ : syracuseStep 5065145 = 3798859) B3798859
theorem B3376763 : Blo 2249435 3376763 := bstep (se 1 (by rfl) ⟨2532572, by rfl⟩ : syracuseStep 3376763 = 5065145) B5065145
theorem B2251175 : Blo 2249435 2251175 := bstep (se 1 (by rfl) ⟨1688381, by rfl⟩ : syracuseStep 2251175 = 3376763) B3376763
theorem B2532577 : Blo 2249435 2532577 := bbase (se 2 (by rfl) ⟨949716, by rfl⟩ : syracuseStep 2532577 = 1899433) (by norm_num)
theorem B3376769 : Blo 2249435 3376769 := bstep (se 2 (by rfl) ⟨1266288, by rfl⟩ : syracuseStep 3376769 = 2532577) B2532577
theorem B2251179 : Blo 2249435 2251179 := bstep (se 1 (by rfl) ⟨1688384, by rfl⟩ : syracuseStep 2251179 = 3376769) B3376769
theorem B5698309 : Blo 2249435 5698309 := bbase (se 4 (by rfl) ⟨534216, by rfl⟩ : syracuseStep 5698309 = 1068433) (by norm_num)
theorem B7597745 : Blo 2249435 7597745 := bstep (se 2 (by rfl) ⟨2849154, by rfl⟩ : syracuseStep 7597745 = 5698309) B5698309
theorem B5065163 : Blo 2249435 5065163 := bstep (se 1 (by rfl) ⟨3798872, by rfl⟩ : syracuseStep 5065163 = 7597745) B7597745
theorem B3376775 : Blo 2249435 3376775 := bstep (se 1 (by rfl) ⟨2532581, by rfl⟩ : syracuseStep 3376775 = 5065163) B5065163
theorem B2251183 : Blo 2249435 2251183 := bstep (se 1 (by rfl) ⟨1688387, by rfl⟩ : syracuseStep 2251183 = 3376775) B3376775
theorem B3376781 : Blo 2249435 3376781 := bbase (se 3 (by rfl) ⟨633146, by rfl⟩ : syracuseStep 3376781 = 1266293) (by norm_num)
theorem B2251187 : Blo 2249435 2251187 := bstep (se 1 (by rfl) ⟨1688390, by rfl⟩ : syracuseStep 2251187 = 3376781) B3376781
theorem B5065181 : Blo 2249435 5065181 := bbase (se 3 (by rfl) ⟨949721, by rfl⟩ : syracuseStep 5065181 = 1899443) (by norm_num)
theorem B3376787 : Blo 2249435 3376787 := bstep (se 1 (by rfl) ⟨2532590, by rfl⟩ : syracuseStep 3376787 = 5065181) B5065181
theorem B2251191 : Blo 2249435 2251191 := bstep (se 1 (by rfl) ⟨1688393, by rfl⟩ : syracuseStep 2251191 = 3376787) B3376787
theorem B3798893 : Blo 2249435 3798893 := bbase (se 3 (by rfl) ⟨712292, by rfl⟩ : syracuseStep 3798893 = 1424585) (by norm_num)
theorem B2532595 : Blo 2249435 2532595 := bstep (se 1 (by rfl) ⟨1899446, by rfl⟩ : syracuseStep 2532595 = 3798893) B3798893
theorem B3376793 : Blo 2249435 3376793 := bstep (se 2 (by rfl) ⟨1266297, by rfl⟩ : syracuseStep 3376793 = 2532595) B2532595
theorem B2251195 : Blo 2249435 2251195 := bstep (se 1 (by rfl) ⟨1688396, by rfl⟩ : syracuseStep 2251195 = 3376793) B3376793
theorem B22230325 : Blo 2249435 22230325 := bbase (se 5 (by rfl) ⟨1042046, by rfl⟩ : syracuseStep 22230325 = 2084093) (by norm_num)
theorem B29640433 : Blo 2249435 29640433 := bstep (se 2 (by rfl) ⟨11115162, by rfl⟩ : syracuseStep 29640433 = 22230325) B22230325
theorem B39520577 : Blo 2249435 39520577 := bstep (se 2 (by rfl) ⟨14820216, by rfl⟩ : syracuseStep 39520577 = 29640433) B29640433
theorem B26347051 : Blo 2249435 26347051 := bstep (se 1 (by rfl) ⟨19760288, by rfl⟩ : syracuseStep 26347051 = 39520577) B39520577
theorem B140517605 : Blo 2249435 140517605 := bstep (se 4 (by rfl) ⟨13173525, by rfl⟩ : syracuseStep 140517605 = 26347051) B26347051
theorem B93678403 : Blo 2249435 93678403 := bstep (se 1 (by rfl) ⟨70258802, by rfl⟩ : syracuseStep 93678403 = 140517605) B140517605
theorem B124904537 : Blo 2249435 124904537 := bstep (se 2 (by rfl) ⟨46839201, by rfl⟩ : syracuseStep 124904537 = 93678403) B93678403
theorem B83269691 : Blo 2249435 83269691 := bstep (se 1 (by rfl) ⟨62452268, by rfl⟩ : syracuseStep 83269691 = 124904537) B124904537
theorem B55513127 : Blo 2249435 55513127 := bstep (se 1 (by rfl) ⟨41634845, by rfl⟩ : syracuseStep 55513127 = 83269691) B83269691
theorem B37008751 : Blo 2249435 37008751 := bstep (se 1 (by rfl) ⟨27756563, by rfl⟩ : syracuseStep 37008751 = 55513127) B55513127
theorem B49345001 : Blo 2249435 49345001 := bstep (se 2 (by rfl) ⟨18504375, by rfl⟩ : syracuseStep 49345001 = 37008751) B37008751
theorem B32896667 : Blo 2249435 32896667 := bstep (se 1 (by rfl) ⟨24672500, by rfl⟩ : syracuseStep 32896667 = 49345001) B49345001
theorem B21931111 : Blo 2249435 21931111 := bstep (se 1 (by rfl) ⟨16448333, by rfl⟩ : syracuseStep 21931111 = 32896667) B32896667
theorem B29241481 : Blo 2249435 29241481 := bstep (se 2 (by rfl) ⟨10965555, by rfl⟩ : syracuseStep 29241481 = 21931111) B21931111
theorem B38988641 : Blo 2249435 38988641 := bstep (se 2 (by rfl) ⟨14620740, by rfl⟩ : syracuseStep 38988641 = 29241481) B29241481
theorem B25992427 : Blo 2249435 25992427 := bstep (se 1 (by rfl) ⟨19494320, by rfl⟩ : syracuseStep 25992427 = 38988641) B38988641
theorem B34656569 : Blo 2249435 34656569 := bstep (se 2 (by rfl) ⟨12996213, by rfl⟩ : syracuseStep 34656569 = 25992427) B25992427
theorem B23104379 : Blo 2249435 23104379 := bstep (se 1 (by rfl) ⟨17328284, by rfl⟩ : syracuseStep 23104379 = 34656569) B34656569
theorem B61611677 : Blo 2249435 61611677 := bstep (se 3 (by rfl) ⟨11552189, by rfl⟩ : syracuseStep 61611677 = 23104379) B23104379
theorem B41074451 : Blo 2249435 41074451 := bstep (se 1 (by rfl) ⟨30805838, by rfl⟩ : syracuseStep 41074451 = 61611677) B61611677
theorem B27382967 : Blo 2249435 27382967 := bstep (se 1 (by rfl) ⟨20537225, by rfl⟩ : syracuseStep 27382967 = 41074451) B41074451
theorem B18255311 : Blo 2249435 18255311 := bstep (se 1 (by rfl) ⟨13691483, by rfl⟩ : syracuseStep 18255311 = 27382967) B27382967
theorem B12170207 : Blo 2249435 12170207 := bstep (se 1 (by rfl) ⟨9127655, by rfl⟩ : syracuseStep 12170207 = 18255311) B18255311
theorem B32453885 : Blo 2249435 32453885 := bstep (se 3 (by rfl) ⟨6085103, by rfl⟩ : syracuseStep 32453885 = 12170207) B12170207
theorem B21635923 : Blo 2249435 21635923 := bstep (se 1 (by rfl) ⟨16226942, by rfl⟩ : syracuseStep 21635923 = 32453885) B32453885
theorem B28847897 : Blo 2249435 28847897 := bstep (se 2 (by rfl) ⟨10817961, by rfl⟩ : syracuseStep 28847897 = 21635923) B21635923
theorem B19231931 : Blo 2249435 19231931 := bstep (se 1 (by rfl) ⟨14423948, by rfl⟩ : syracuseStep 19231931 = 28847897) B28847897
theorem B12821287 : Blo 2249435 12821287 := bstep (se 1 (by rfl) ⟨9615965, by rfl⟩ : syracuseStep 12821287 = 19231931) B19231931
theorem B17095049 : Blo 2249435 17095049 := bstep (se 2 (by rfl) ⟨6410643, by rfl⟩ : syracuseStep 17095049 = 12821287) B12821287
theorem B11396699 : Blo 2249435 11396699 := bstep (se 1 (by rfl) ⟨8547524, by rfl⟩ : syracuseStep 11396699 = 17095049) B17095049
theorem B7597799 : Blo 2249435 7597799 := bstep (se 1 (by rfl) ⟨5698349, by rfl⟩ : syracuseStep 7597799 = 11396699) B11396699
theorem B5065199 : Blo 2249435 5065199 := bstep (se 1 (by rfl) ⟨3798899, by rfl⟩ : syracuseStep 5065199 = 7597799) B7597799
theorem B3376799 : Blo 2249435 3376799 := bstep (se 1 (by rfl) ⟨2532599, by rfl⟩ : syracuseStep 3376799 = 5065199) B5065199
theorem B2251199 : Blo 2249435 2251199 := bstep (se 1 (by rfl) ⟨1688399, by rfl⟩ : syracuseStep 2251199 = 3376799) B3376799
theorem B3376805 : Blo 2249435 3376805 := bbase (se 4 (by rfl) ⟨316575, by rfl⟩ : syracuseStep 3376805 = 633151) (by norm_num)
theorem B2251203 : Blo 2249435 2251203 := bstep (se 1 (by rfl) ⟨1688402, by rfl⟩ : syracuseStep 2251203 = 3376805) B3376805
theorem B2849185 : Blo 2249435 2849185 := bbase (se 2 (by rfl) ⟨1068444, by rfl⟩ : syracuseStep 2849185 = 2136889) (by norm_num)
theorem B3798913 : Blo 2249435 3798913 := bstep (se 2 (by rfl) ⟨1424592, by rfl⟩ : syracuseStep 3798913 = 2849185) B2849185
theorem B5065217 : Blo 2249435 5065217 := bstep (se 2 (by rfl) ⟨1899456, by rfl⟩ : syracuseStep 5065217 = 3798913) B3798913
theorem B3376811 : Blo 2249435 3376811 := bstep (se 1 (by rfl) ⟨2532608, by rfl⟩ : syracuseStep 3376811 = 5065217) B5065217
theorem B2251207 : Blo 2249435 2251207 := bstep (se 1 (by rfl) ⟨1688405, by rfl⟩ : syracuseStep 2251207 = 3376811) B3376811
theorem B2532613 : Blo 2249435 2532613 := bbase (se 4 (by rfl) ⟨237432, by rfl⟩ : syracuseStep 2532613 = 474865) (by norm_num)
theorem B3376817 : Blo 2249435 3376817 := bstep (se 2 (by rfl) ⟨1266306, by rfl⟩ : syracuseStep 3376817 = 2532613) B2532613
theorem B2251211 : Blo 2249435 2251211 := bstep (se 1 (by rfl) ⟨1688408, by rfl⟩ : syracuseStep 2251211 = 3376817) B3376817
theorem B2404009 : Blo 2249435 2404009 := bbase (se 2 (by rfl) ⟨901503, by rfl⟩ : syracuseStep 2404009 = 1803007) (by norm_num)
theorem B3205345 : Blo 2249435 3205345 := bstep (se 2 (by rfl) ⟨1202004, by rfl⟩ : syracuseStep 3205345 = 2404009) B2404009
theorem B4273793 : Blo 2249435 4273793 := bstep (se 2 (by rfl) ⟨1602672, by rfl⟩ : syracuseStep 4273793 = 3205345) B3205345
theorem B2849195 : Blo 2249435 2849195 := bstep (se 1 (by rfl) ⟨2136896, by rfl⟩ : syracuseStep 2849195 = 4273793) B4273793
theorem B7597853 : Blo 2249435 7597853 := bstep (se 3 (by rfl) ⟨1424597, by rfl⟩ : syracuseStep 7597853 = 2849195) B2849195
theorem B5065235 : Blo 2249435 5065235 := bstep (se 1 (by rfl) ⟨3798926, by rfl⟩ : syracuseStep 5065235 = 7597853) B7597853
theorem B3376823 : Blo 2249435 3376823 := bstep (se 1 (by rfl) ⟨2532617, by rfl⟩ : syracuseStep 3376823 = 5065235) B5065235
theorem B2251215 : Blo 2249435 2251215 := bstep (se 1 (by rfl) ⟨1688411, by rfl⟩ : syracuseStep 2251215 = 3376823) B3376823
theorem B3376829 : Blo 2249435 3376829 := bbase (se 3 (by rfl) ⟨633155, by rfl⟩ : syracuseStep 3376829 = 1266311) (by norm_num)
theorem B2251219 : Blo 2249435 2251219 := bstep (se 1 (by rfl) ⟨1688414, by rfl⟩ : syracuseStep 2251219 = 3376829) B3376829
theorem B5065253 : Blo 2249435 5065253 := bbase (se 4 (by rfl) ⟨474867, by rfl⟩ : syracuseStep 5065253 = 949735) (by norm_num)
theorem B3376835 : Blo 2249435 3376835 := bstep (se 1 (by rfl) ⟨2532626, by rfl⟩ : syracuseStep 3376835 = 5065253) B5065253
theorem B2251223 : Blo 2249435 2251223 := bstep (se 1 (by rfl) ⟨1688417, by rfl⟩ : syracuseStep 2251223 = 3376835) B3376835
theorem B5698421 : Blo 2249435 5698421 := bbase (se 5 (by rfl) ⟨267113, by rfl⟩ : syracuseStep 5698421 = 534227) (by norm_num)
theorem B3798947 : Blo 2249435 3798947 := bstep (se 1 (by rfl) ⟨2849210, by rfl⟩ : syracuseStep 3798947 = 5698421) B5698421
theorem B2532631 : Blo 2249435 2532631 := bstep (se 1 (by rfl) ⟨1899473, by rfl⟩ : syracuseStep 2532631 = 3798947) B3798947
theorem B3376841 : Blo 2249435 3376841 := bstep (se 2 (by rfl) ⟨1266315, by rfl⟩ : syracuseStep 3376841 = 2532631) B2532631
theorem B2251227 : Blo 2249435 2251227 := bstep (se 1 (by rfl) ⟨1688420, by rfl⟩ : syracuseStep 2251227 = 3376841) B3376841
theorem B24672853 : Blo 2249435 24672853 := bbase (se 8 (by rfl) ⟨144567, by rfl⟩ : syracuseStep 24672853 = 289135) (by norm_num)
theorem B32897137 : Blo 2249435 32897137 := bstep (se 2 (by rfl) ⟨12336426, by rfl⟩ : syracuseStep 32897137 = 24672853) B24672853
theorem B43862849 : Blo 2249435 43862849 := bstep (se 2 (by rfl) ⟨16448568, by rfl⟩ : syracuseStep 43862849 = 32897137) B32897137
theorem B29241899 : Blo 2249435 29241899 := bstep (se 1 (by rfl) ⟨21931424, by rfl⟩ : syracuseStep 29241899 = 43862849) B43862849
theorem B19494599 : Blo 2249435 19494599 := bstep (se 1 (by rfl) ⟨14620949, by rfl⟩ : syracuseStep 19494599 = 29241899) B29241899
theorem B207942389 : Blo 2249435 207942389 := bstep (se 5 (by rfl) ⟨9747299, by rfl⟩ : syracuseStep 207942389 = 19494599) B19494599
theorem B138628259 : Blo 2249435 138628259 := bstep (se 1 (by rfl) ⟨103971194, by rfl⟩ : syracuseStep 138628259 = 207942389) B207942389
theorem B92418839 : Blo 2249435 92418839 := bstep (se 1 (by rfl) ⟨69314129, by rfl⟩ : syracuseStep 92418839 = 138628259) B138628259
theorem B61612559 : Blo 2249435 61612559 := bstep (se 1 (by rfl) ⟨46209419, by rfl⟩ : syracuseStep 61612559 = 92418839) B92418839
theorem B41075039 : Blo 2249435 41075039 := bstep (se 1 (by rfl) ⟨30806279, by rfl⟩ : syracuseStep 41075039 = 61612559) B61612559
theorem B27383359 : Blo 2249435 27383359 := bstep (se 1 (by rfl) ⟨20537519, by rfl⟩ : syracuseStep 27383359 = 41075039) B41075039
theorem B36511145 : Blo 2249435 36511145 := bstep (se 2 (by rfl) ⟨13691679, by rfl⟩ : syracuseStep 36511145 = 27383359) B27383359
theorem B24340763 : Blo 2249435 24340763 := bstep (se 1 (by rfl) ⟨18255572, by rfl⟩ : syracuseStep 24340763 = 36511145) B36511145
theorem B16227175 : Blo 2249435 16227175 := bstep (se 1 (by rfl) ⟨12170381, by rfl⟩ : syracuseStep 16227175 = 24340763) B24340763
theorem B21636233 : Blo 2249435 21636233 := bstep (se 2 (by rfl) ⟨8113587, by rfl⟩ : syracuseStep 21636233 = 16227175) B16227175
theorem B14424155 : Blo 2249435 14424155 := bstep (se 1 (by rfl) ⟨10818116, by rfl⟩ : syracuseStep 14424155 = 21636233) B21636233
theorem B9616103 : Blo 2249435 9616103 := bstep (se 1 (by rfl) ⟨7212077, by rfl⟩ : syracuseStep 9616103 = 14424155) B14424155
theorem B6410735 : Blo 2249435 6410735 := bstep (se 1 (by rfl) ⟨4808051, by rfl⟩ : syracuseStep 6410735 = 9616103) B9616103
theorem B4273823 : Blo 2249435 4273823 := bstep (se 1 (by rfl) ⟨3205367, by rfl⟩ : syracuseStep 4273823 = 6410735) B6410735
theorem B11396861 : Blo 2249435 11396861 := bstep (se 3 (by rfl) ⟨2136911, by rfl⟩ : syracuseStep 11396861 = 4273823) B4273823
theorem B7597907 : Blo 2249435 7597907 := bstep (se 1 (by rfl) ⟨5698430, by rfl⟩ : syracuseStep 7597907 = 11396861) B11396861
theorem B5065271 : Blo 2249435 5065271 := bstep (se 1 (by rfl) ⟨3798953, by rfl⟩ : syracuseStep 5065271 = 7597907) B7597907
theorem B3376847 : Blo 2249435 3376847 := bstep (se 1 (by rfl) ⟨2532635, by rfl⟩ : syracuseStep 3376847 = 5065271) B5065271
theorem B2251231 : Blo 2249435 2251231 := bstep (se 1 (by rfl) ⟨1688423, by rfl⟩ : syracuseStep 2251231 = 3376847) B3376847
theorem B3376853 : Blo 2249435 3376853 := bbase (se 7 (by rfl) ⟨39572, by rfl⟩ : syracuseStep 3376853 = 79145) (by norm_num)
theorem B2251235 : Blo 2249435 2251235 := bstep (se 1 (by rfl) ⟨1688426, by rfl⟩ : syracuseStep 2251235 = 3376853) B3376853
theorem B4808069 : Blo 2249435 4808069 := bbase (se 4 (by rfl) ⟨450756, by rfl⟩ : syracuseStep 4808069 = 901513) (by norm_num)
theorem B3205379 : Blo 2249435 3205379 := bstep (se 1 (by rfl) ⟨2404034, by rfl⟩ : syracuseStep 3205379 = 4808069) B4808069
theorem B8547677 : Blo 2249435 8547677 := bstep (se 3 (by rfl) ⟨1602689, by rfl⟩ : syracuseStep 8547677 = 3205379) B3205379
theorem B5698451 : Blo 2249435 5698451 := bstep (se 1 (by rfl) ⟨4273838, by rfl⟩ : syracuseStep 5698451 = 8547677) B8547677
theorem B3798967 : Blo 2249435 3798967 := bstep (se 1 (by rfl) ⟨2849225, by rfl⟩ : syracuseStep 3798967 = 5698451) B5698451
theorem B5065289 : Blo 2249435 5065289 := bstep (se 2 (by rfl) ⟨1899483, by rfl⟩ : syracuseStep 5065289 = 3798967) B3798967
theorem B3376859 : Blo 2249435 3376859 := bstep (se 1 (by rfl) ⟨2532644, by rfl⟩ : syracuseStep 3376859 = 5065289) B5065289
theorem B2251239 : Blo 2249435 2251239 := bstep (se 1 (by rfl) ⟨1688429, by rfl⟩ : syracuseStep 2251239 = 3376859) B3376859
theorem B2532649 : Blo 2249435 2532649 := bbase (se 2 (by rfl) ⟨949743, by rfl⟩ : syracuseStep 2532649 = 1899487) (by norm_num)
theorem B3376865 : Blo 2249435 3376865 := bstep (se 2 (by rfl) ⟨1266324, by rfl⟩ : syracuseStep 3376865 = 2532649) B2532649
theorem B2251243 : Blo 2249435 2251243 := bstep (se 1 (by rfl) ⟨1688432, by rfl⟩ : syracuseStep 2251243 = 3376865) B3376865
theorem B2567209 : Blo 2249435 2567209 := bbase (se 2 (by rfl) ⟨962703, by rfl⟩ : syracuseStep 2567209 = 1925407) (by norm_num)
theorem B3422945 : Blo 2249435 3422945 := bstep (se 2 (by rfl) ⟨1283604, by rfl⟩ : syracuseStep 3422945 = 2567209) B2567209
theorem B2281963 : Blo 2249435 2281963 := bstep (se 1 (by rfl) ⟨1711472, by rfl⟩ : syracuseStep 2281963 = 3422945) B3422945
theorem B3042617 : Blo 2249435 3042617 := bstep (se 2 (by rfl) ⟨1140981, by rfl⟩ : syracuseStep 3042617 = 2281963) B2281963
theorem B8113645 : Blo 2249435 8113645 := bstep (se 3 (by rfl) ⟨1521308, by rfl⟩ : syracuseStep 8113645 = 3042617) B3042617
theorem B10818193 : Blo 2249435 10818193 := bstep (se 2 (by rfl) ⟨4056822, by rfl⟩ : syracuseStep 10818193 = 8113645) B8113645
theorem B14424257 : Blo 2249435 14424257 := bstep (se 2 (by rfl) ⟨5409096, by rfl⟩ : syracuseStep 14424257 = 10818193) B10818193
theorem B9616171 : Blo 2249435 9616171 := bstep (se 1 (by rfl) ⟨7212128, by rfl⟩ : syracuseStep 9616171 = 14424257) B14424257
theorem B12821561 : Blo 2249435 12821561 := bstep (se 2 (by rfl) ⟨4808085, by rfl⟩ : syracuseStep 12821561 = 9616171) B9616171
theorem B8547707 : Blo 2249435 8547707 := bstep (se 1 (by rfl) ⟨6410780, by rfl⟩ : syracuseStep 8547707 = 12821561) B12821561
theorem B5698471 : Blo 2249435 5698471 := bstep (se 1 (by rfl) ⟨4273853, by rfl⟩ : syracuseStep 5698471 = 8547707) B8547707
theorem B7597961 : Blo 2249435 7597961 := bstep (se 2 (by rfl) ⟨2849235, by rfl⟩ : syracuseStep 7597961 = 5698471) B5698471
theorem B5065307 : Blo 2249435 5065307 := bstep (se 1 (by rfl) ⟨3798980, by rfl⟩ : syracuseStep 5065307 = 7597961) B7597961
theorem B3376871 : Blo 2249435 3376871 := bstep (se 1 (by rfl) ⟨2532653, by rfl⟩ : syracuseStep 3376871 = 5065307) B5065307
theorem B2251247 : Blo 2249435 2251247 := bstep (se 1 (by rfl) ⟨1688435, by rfl⟩ : syracuseStep 2251247 = 3376871) B3376871
theorem B3376877 : Blo 2249435 3376877 := bbase (se 3 (by rfl) ⟨633164, by rfl⟩ : syracuseStep 3376877 = 1266329) (by norm_num)
theorem B2251251 : Blo 2249435 2251251 := bstep (se 1 (by rfl) ⟨1688438, by rfl⟩ : syracuseStep 2251251 = 3376877) B3376877
theorem B5065325 : Blo 2249435 5065325 := bbase (se 3 (by rfl) ⟨949748, by rfl⟩ : syracuseStep 5065325 = 1899497) (by norm_num)
theorem B3376883 : Blo 2249435 3376883 := bstep (se 1 (by rfl) ⟨2532662, by rfl⟩ : syracuseStep 3376883 = 5065325) B5065325
theorem B2251255 : Blo 2249435 2251255 := bstep (se 1 (by rfl) ⟨1688441, by rfl⟩ : syracuseStep 2251255 = 3376883) B3376883
theorem B4273877 : Blo 2249435 4273877 := bbase (se 7 (by rfl) ⟨50084, by rfl⟩ : syracuseStep 4273877 = 100169) (by norm_num)
theorem B2849251 : Blo 2249435 2849251 := bstep (se 1 (by rfl) ⟨2136938, by rfl⟩ : syracuseStep 2849251 = 4273877) B4273877
theorem B3799001 : Blo 2249435 3799001 := bstep (se 2 (by rfl) ⟨1424625, by rfl⟩ : syracuseStep 3799001 = 2849251) B2849251
theorem B2532667 : Blo 2249435 2532667 := bstep (se 1 (by rfl) ⟨1899500, by rfl⟩ : syracuseStep 2532667 = 3799001) B3799001
theorem B3376889 : Blo 2249435 3376889 := bstep (se 2 (by rfl) ⟨1266333, by rfl⟩ : syracuseStep 3376889 = 2532667) B2532667
theorem B2251259 : Blo 2249435 2251259 := bstep (se 1 (by rfl) ⟨1688444, by rfl⟩ : syracuseStep 2251259 = 3376889) B3376889
theorem B18255829 : Blo 2249435 18255829 := bbase (se 7 (by rfl) ⟨213935, by rfl⟩ : syracuseStep 18255829 = 427871) (by norm_num)
theorem B24341105 : Blo 2249435 24341105 := bstep (se 2 (by rfl) ⟨9127914, by rfl⟩ : syracuseStep 24341105 = 18255829) B18255829
theorem B64909613 : Blo 2249435 64909613 := bstep (se 3 (by rfl) ⟨12170552, by rfl⟩ : syracuseStep 64909613 = 24341105) B24341105
theorem B43273075 : Blo 2249435 43273075 := bstep (se 1 (by rfl) ⟨32454806, by rfl⟩ : syracuseStep 43273075 = 64909613) B64909613
theorem B57697433 : Blo 2249435 57697433 := bstep (se 2 (by rfl) ⟨21636537, by rfl⟩ : syracuseStep 57697433 = 43273075) B43273075
theorem B38464955 : Blo 2249435 38464955 := bstep (se 1 (by rfl) ⟨28848716, by rfl⟩ : syracuseStep 38464955 = 57697433) B57697433
theorem B25643303 : Blo 2249435 25643303 := bstep (se 1 (by rfl) ⟨19232477, by rfl⟩ : syracuseStep 25643303 = 38464955) B38464955
theorem B17095535 : Blo 2249435 17095535 := bstep (se 1 (by rfl) ⟨12821651, by rfl⟩ : syracuseStep 17095535 = 25643303) B25643303
theorem B11397023 : Blo 2249435 11397023 := bstep (se 1 (by rfl) ⟨8547767, by rfl⟩ : syracuseStep 11397023 = 17095535) B17095535
theorem B7598015 : Blo 2249435 7598015 := bstep (se 1 (by rfl) ⟨5698511, by rfl⟩ : syracuseStep 7598015 = 11397023) B11397023
theorem B5065343 : Blo 2249435 5065343 := bstep (se 1 (by rfl) ⟨3799007, by rfl⟩ : syracuseStep 5065343 = 7598015) B7598015
theorem B3376895 : Blo 2249435 3376895 := bstep (se 1 (by rfl) ⟨2532671, by rfl⟩ : syracuseStep 3376895 = 5065343) B5065343
theorem B2251263 : Blo 2249435 2251263 := bstep (se 1 (by rfl) ⟨1688447, by rfl⟩ : syracuseStep 2251263 = 3376895) B3376895
theorem B3376901 : Blo 2249435 3376901 := bbase (se 4 (by rfl) ⟨316584, by rfl⟩ : syracuseStep 3376901 = 633169) (by norm_num)
theorem B2251267 : Blo 2249435 2251267 := bstep (se 1 (by rfl) ⟨1688450, by rfl⟩ : syracuseStep 2251267 = 3376901) B3376901
theorem B3799021 : Blo 2249435 3799021 := bbase (se 3 (by rfl) ⟨712316, by rfl⟩ : syracuseStep 3799021 = 1424633) (by norm_num)
theorem B5065361 : Blo 2249435 5065361 := bstep (se 2 (by rfl) ⟨1899510, by rfl⟩ : syracuseStep 5065361 = 3799021) B3799021
theorem B3376907 : Blo 2249435 3376907 := bstep (se 1 (by rfl) ⟨2532680, by rfl⟩ : syracuseStep 3376907 = 5065361) B5065361
theorem B2251271 : Blo 2249435 2251271 := bstep (se 1 (by rfl) ⟨1688453, by rfl⟩ : syracuseStep 2251271 = 3376907) B3376907
theorem B2532685 : Blo 2249435 2532685 := bbase (se 3 (by rfl) ⟨474878, by rfl⟩ : syracuseStep 2532685 = 949757) (by norm_num)
theorem B3376913 : Blo 2249435 3376913 := bstep (se 2 (by rfl) ⟨1266342, by rfl⟩ : syracuseStep 3376913 = 2532685) B2532685
theorem B2251275 : Blo 2249435 2251275 := bstep (se 1 (by rfl) ⟨1688456, by rfl⟩ : syracuseStep 2251275 = 3376913) B3376913
theorem B7598069 : Blo 2249435 7598069 := bbase (se 5 (by rfl) ⟨356159, by rfl⟩ : syracuseStep 7598069 = 712319) (by norm_num)
theorem B5065379 : Blo 2249435 5065379 := bstep (se 1 (by rfl) ⟨3799034, by rfl⟩ : syracuseStep 5065379 = 7598069) B7598069
theorem B3376919 : Blo 2249435 3376919 := bstep (se 1 (by rfl) ⟨2532689, by rfl⟩ : syracuseStep 3376919 = 5065379) B5065379
theorem B2251279 : Blo 2249435 2251279 := bstep (se 1 (by rfl) ⟨1688459, by rfl⟩ : syracuseStep 2251279 = 3376919) B3376919
theorem B3376925 : Blo 2249435 3376925 := bbase (se 3 (by rfl) ⟨633173, by rfl⟩ : syracuseStep 3376925 = 1266347) (by norm_num)
theorem B2251283 : Blo 2249435 2251283 := bstep (se 1 (by rfl) ⟨1688462, by rfl⟩ : syracuseStep 2251283 = 3376925) B3376925
theorem B5065397 : Blo 2249435 5065397 := bbase (se 5 (by rfl) ⟨237440, by rfl⟩ : syracuseStep 5065397 = 474881) (by norm_num)
theorem B3376931 : Blo 2249435 3376931 := bstep (se 1 (by rfl) ⟨2532698, by rfl⟩ : syracuseStep 3376931 = 5065397) B5065397
theorem B2251287 : Blo 2249435 2251287 := bstep (se 1 (by rfl) ⟨1688465, by rfl⟩ : syracuseStep 2251287 = 3376931) B3376931
theorem B12821813 : Blo 2249435 12821813 := bbase (se 5 (by rfl) ⟨601022, by rfl⟩ : syracuseStep 12821813 = 1202045) (by norm_num)
theorem B8547875 : Blo 2249435 8547875 := bstep (se 1 (by rfl) ⟨6410906, by rfl⟩ : syracuseStep 8547875 = 12821813) B12821813
theorem B5698583 : Blo 2249435 5698583 := bstep (se 1 (by rfl) ⟨4273937, by rfl⟩ : syracuseStep 5698583 = 8547875) B8547875
theorem B3799055 : Blo 2249435 3799055 := bstep (se 1 (by rfl) ⟨2849291, by rfl⟩ : syracuseStep 3799055 = 5698583) B5698583
theorem B2532703 : Blo 2249435 2532703 := bstep (se 1 (by rfl) ⟨1899527, by rfl⟩ : syracuseStep 2532703 = 3799055) B3799055
theorem B3376937 : Blo 2249435 3376937 := bstep (se 2 (by rfl) ⟨1266351, by rfl⟩ : syracuseStep 3376937 = 2532703) B2532703
theorem B2251291 : Blo 2249435 2251291 := bstep (se 1 (by rfl) ⟨1688468, by rfl⟩ : syracuseStep 2251291 = 3376937) B3376937
theorem B6410917 : Blo 2249435 6410917 := bbase (se 4 (by rfl) ⟨601023, by rfl⟩ : syracuseStep 6410917 = 1202047) (by norm_num)
theorem B8547889 : Blo 2249435 8547889 := bstep (se 2 (by rfl) ⟨3205458, by rfl⟩ : syracuseStep 8547889 = 6410917) B6410917
theorem B11397185 : Blo 2249435 11397185 := bstep (se 2 (by rfl) ⟨4273944, by rfl⟩ : syracuseStep 11397185 = 8547889) B8547889
theorem B7598123 : Blo 2249435 7598123 := bstep (se 1 (by rfl) ⟨5698592, by rfl⟩ : syracuseStep 7598123 = 11397185) B11397185
theorem B5065415 : Blo 2249435 5065415 := bstep (se 1 (by rfl) ⟨3799061, by rfl⟩ : syracuseStep 5065415 = 7598123) B7598123
theorem B3376943 : Blo 2249435 3376943 := bstep (se 1 (by rfl) ⟨2532707, by rfl⟩ : syracuseStep 3376943 = 5065415) B5065415
theorem B2251295 : Blo 2249435 2251295 := bstep (se 1 (by rfl) ⟨1688471, by rfl⟩ : syracuseStep 2251295 = 3376943) B3376943
theorem B3376949 : Blo 2249435 3376949 := bbase (se 5 (by rfl) ⟨158294, by rfl⟩ : syracuseStep 3376949 = 316589) (by norm_num)
theorem B2251299 : Blo 2249435 2251299 := bstep (se 1 (by rfl) ⟨1688474, by rfl⟩ : syracuseStep 2251299 = 3376949) B3376949
theorem B5698613 : Blo 2249435 5698613 := bbase (se 5 (by rfl) ⟨267122, by rfl⟩ : syracuseStep 5698613 = 534245) (by norm_num)
theorem B3799075 : Blo 2249435 3799075 := bstep (se 1 (by rfl) ⟨2849306, by rfl⟩ : syracuseStep 3799075 = 5698613) B5698613
theorem B5065433 : Blo 2249435 5065433 := bstep (se 2 (by rfl) ⟨1899537, by rfl⟩ : syracuseStep 5065433 = 3799075) B3799075
theorem B3376955 : Blo 2249435 3376955 := bstep (se 1 (by rfl) ⟨2532716, by rfl⟩ : syracuseStep 3376955 = 5065433) B5065433
theorem B2251303 : Blo 2249435 2251303 := bstep (se 1 (by rfl) ⟨1688477, by rfl⟩ : syracuseStep 2251303 = 3376955) B3376955
theorem B2532721 : Blo 2249435 2532721 := bbase (se 2 (by rfl) ⟨949770, by rfl⟩ : syracuseStep 2532721 = 1899541) (by norm_num)
theorem B3376961 : Blo 2249435 3376961 := bstep (se 2 (by rfl) ⟨1266360, by rfl⟩ : syracuseStep 3376961 = 2532721) B2532721
theorem B2251307 : Blo 2249435 2251307 := bstep (se 1 (by rfl) ⟨1688480, by rfl⟩ : syracuseStep 2251307 = 3376961) B3376961
theorem B8113877 : Blo 2249435 8113877 := bbase (se 7 (by rfl) ⟨95084, by rfl⟩ : syracuseStep 8113877 = 190169) (by norm_num)
theorem B5409251 : Blo 2249435 5409251 := bstep (se 1 (by rfl) ⟨4056938, by rfl⟩ : syracuseStep 5409251 = 8113877) B8113877
theorem B3606167 : Blo 2249435 3606167 := bstep (se 1 (by rfl) ⟨2704625, by rfl⟩ : syracuseStep 3606167 = 5409251) B5409251
theorem B9616445 : Blo 2249435 9616445 := bstep (se 3 (by rfl) ⟨1803083, by rfl⟩ : syracuseStep 9616445 = 3606167) B3606167
theorem B6410963 : Blo 2249435 6410963 := bstep (se 1 (by rfl) ⟨4808222, by rfl⟩ : syracuseStep 6410963 = 9616445) B9616445
theorem B4273975 : Blo 2249435 4273975 := bstep (se 1 (by rfl) ⟨3205481, by rfl⟩ : syracuseStep 4273975 = 6410963) B6410963
theorem B5698633 : Blo 2249435 5698633 := bstep (se 2 (by rfl) ⟨2136987, by rfl⟩ : syracuseStep 5698633 = 4273975) B4273975
theorem B7598177 : Blo 2249435 7598177 := bstep (se 2 (by rfl) ⟨2849316, by rfl⟩ : syracuseStep 7598177 = 5698633) B5698633
theorem B5065451 : Blo 2249435 5065451 := bstep (se 1 (by rfl) ⟨3799088, by rfl⟩ : syracuseStep 5065451 = 7598177) B7598177
theorem B3376967 : Blo 2249435 3376967 := bstep (se 1 (by rfl) ⟨2532725, by rfl⟩ : syracuseStep 3376967 = 5065451) B5065451
theorem B2251311 : Blo 2249435 2251311 := bstep (se 1 (by rfl) ⟨1688483, by rfl⟩ : syracuseStep 2251311 = 3376967) B3376967
theorem B3376973 : Blo 2249435 3376973 := bbase (se 3 (by rfl) ⟨633182, by rfl⟩ : syracuseStep 3376973 = 1266365) (by norm_num)
theorem B2251315 : Blo 2249435 2251315 := bstep (se 1 (by rfl) ⟨1688486, by rfl⟩ : syracuseStep 2251315 = 3376973) B3376973
theorem B5065469 : Blo 2249435 5065469 := bbase (se 3 (by rfl) ⟨949775, by rfl⟩ : syracuseStep 5065469 = 1899551) (by norm_num)
theorem B3376979 : Blo 2249435 3376979 := bstep (se 1 (by rfl) ⟨2532734, by rfl⟩ : syracuseStep 3376979 = 5065469) B5065469
theorem B2251319 : Blo 2249435 2251319 := bstep (se 1 (by rfl) ⟨1688489, by rfl⟩ : syracuseStep 2251319 = 3376979) B3376979
theorem B3799109 : Blo 2249435 3799109 := bbase (se 4 (by rfl) ⟨356166, by rfl⟩ : syracuseStep 3799109 = 712333) (by norm_num)
theorem B2532739 : Blo 2249435 2532739 := bstep (se 1 (by rfl) ⟨1899554, by rfl⟩ : syracuseStep 2532739 = 3799109) B3799109
theorem B3376985 : Blo 2249435 3376985 := bstep (se 2 (by rfl) ⟨1266369, by rfl⟩ : syracuseStep 3376985 = 2532739) B2532739
theorem B2251323 : Blo 2249435 2251323 := bstep (se 1 (by rfl) ⟨1688492, by rfl⟩ : syracuseStep 2251323 = 3376985) B3376985
theorem B17096021 : Blo 2249435 17096021 := bbase (se 11 (by rfl) ⟨12521, by rfl⟩ : syracuseStep 17096021 = 25043) (by norm_num)
theorem B11397347 : Blo 2249435 11397347 := bstep (se 1 (by rfl) ⟨8548010, by rfl⟩ : syracuseStep 11397347 = 17096021) B17096021
theorem B7598231 : Blo 2249435 7598231 := bstep (se 1 (by rfl) ⟨5698673, by rfl⟩ : syracuseStep 7598231 = 11397347) B11397347
theorem B5065487 : Blo 2249435 5065487 := bstep (se 1 (by rfl) ⟨3799115, by rfl⟩ : syracuseStep 5065487 = 7598231) B7598231
theorem B3376991 : Blo 2249435 3376991 := bstep (se 1 (by rfl) ⟨2532743, by rfl⟩ : syracuseStep 3376991 = 5065487) B5065487
theorem B2251327 : Blo 2249435 2251327 := bstep (se 1 (by rfl) ⟨1688495, by rfl⟩ : syracuseStep 2251327 = 3376991) B3376991
theorem B3376997 : Blo 2249435 3376997 := bbase (se 4 (by rfl) ⟨316593, by rfl⟩ : syracuseStep 3376997 = 633187) (by norm_num)
theorem B2251331 : Blo 2249435 2251331 := bstep (se 1 (by rfl) ⟨1688498, by rfl⟩ : syracuseStep 2251331 = 3376997) B3376997
theorem B4274021 : Blo 2249435 4274021 := bbase (se 4 (by rfl) ⟨400689, by rfl⟩ : syracuseStep 4274021 = 801379) (by norm_num)
theorem B2849347 : Blo 2249435 2849347 := bstep (se 1 (by rfl) ⟨2137010, by rfl⟩ : syracuseStep 2849347 = 4274021) B4274021
theorem B3799129 : Blo 2249435 3799129 := bstep (se 2 (by rfl) ⟨1424673, by rfl⟩ : syracuseStep 3799129 = 2849347) B2849347
theorem B5065505 : Blo 2249435 5065505 := bstep (se 2 (by rfl) ⟨1899564, by rfl⟩ : syracuseStep 5065505 = 3799129) B3799129
theorem B3377003 : Blo 2249435 3377003 := bstep (se 1 (by rfl) ⟨2532752, by rfl⟩ : syracuseStep 3377003 = 5065505) B5065505
theorem B2251335 : Blo 2249435 2251335 := bstep (se 1 (by rfl) ⟨1688501, by rfl⟩ : syracuseStep 2251335 = 3377003) B3377003
theorem B2532757 : Blo 2249435 2532757 := bbase (se 6 (by rfl) ⟨59361, by rfl⟩ : syracuseStep 2532757 = 118723) (by norm_num)
theorem B3377009 : Blo 2249435 3377009 := bstep (se 2 (by rfl) ⟨1266378, by rfl⟩ : syracuseStep 3377009 = 2532757) B2532757
theorem B2251339 : Blo 2249435 2251339 := bstep (se 1 (by rfl) ⟨1688504, by rfl⟩ : syracuseStep 2251339 = 3377009) B3377009
theorem B2849357 : Blo 2249435 2849357 := bbase (se 3 (by rfl) ⟨534254, by rfl⟩ : syracuseStep 2849357 = 1068509) (by norm_num)
theorem B7598285 : Blo 2249435 7598285 := bstep (se 3 (by rfl) ⟨1424678, by rfl⟩ : syracuseStep 7598285 = 2849357) B2849357
theorem B5065523 : Blo 2249435 5065523 := bstep (se 1 (by rfl) ⟨3799142, by rfl⟩ : syracuseStep 5065523 = 7598285) B7598285
theorem B3377015 : Blo 2249435 3377015 := bstep (se 1 (by rfl) ⟨2532761, by rfl⟩ : syracuseStep 3377015 = 5065523) B5065523
theorem B2251343 : Blo 2249435 2251343 := bstep (se 1 (by rfl) ⟨1688507, by rfl⟩ : syracuseStep 2251343 = 3377015) B3377015
theorem B3377021 : Blo 2249435 3377021 := bbase (se 3 (by rfl) ⟨633191, by rfl⟩ : syracuseStep 3377021 = 1266383) (by norm_num)
theorem B2251347 : Blo 2249435 2251347 := bstep (se 1 (by rfl) ⟨1688510, by rfl⟩ : syracuseStep 2251347 = 3377021) B3377021
theorem B5065541 : Blo 2249435 5065541 := bbase (se 4 (by rfl) ⟨474894, by rfl⟩ : syracuseStep 5065541 = 949789) (by norm_num)
theorem B3377027 : Blo 2249435 3377027 := bstep (se 1 (by rfl) ⟨2532770, by rfl⟩ : syracuseStep 3377027 = 5065541) B5065541
theorem B2251351 : Blo 2249435 2251351 := bstep (se 1 (by rfl) ⟨1688513, by rfl⟩ : syracuseStep 2251351 = 3377027) B3377027
theorem B4808317 : Blo 2249435 4808317 := bbase (se 3 (by rfl) ⟨901559, by rfl⟩ : syracuseStep 4808317 = 1803119) (by norm_num)
theorem B6411089 : Blo 2249435 6411089 := bstep (se 2 (by rfl) ⟨2404158, by rfl⟩ : syracuseStep 6411089 = 4808317) B4808317
theorem B4274059 : Blo 2249435 4274059 := bstep (se 1 (by rfl) ⟨3205544, by rfl⟩ : syracuseStep 4274059 = 6411089) B6411089
theorem B5698745 : Blo 2249435 5698745 := bstep (se 2 (by rfl) ⟨2137029, by rfl⟩ : syracuseStep 5698745 = 4274059) B4274059
theorem B3799163 : Blo 2249435 3799163 := bstep (se 1 (by rfl) ⟨2849372, by rfl⟩ : syracuseStep 3799163 = 5698745) B5698745
theorem B2532775 : Blo 2249435 2532775 := bstep (se 1 (by rfl) ⟨1899581, by rfl⟩ : syracuseStep 2532775 = 3799163) B3799163
theorem B3377033 : Blo 2249435 3377033 := bstep (se 2 (by rfl) ⟨1266387, by rfl⟩ : syracuseStep 3377033 = 2532775) B2532775
theorem B2251355 : Blo 2249435 2251355 := bstep (se 1 (by rfl) ⟨1688516, by rfl⟩ : syracuseStep 2251355 = 3377033) B3377033
theorem B11397509 : Blo 2249435 11397509 := bbase (se 4 (by rfl) ⟨1068516, by rfl⟩ : syracuseStep 11397509 = 2137033) (by norm_num)
theorem B7598339 : Blo 2249435 7598339 := bstep (se 1 (by rfl) ⟨5698754, by rfl⟩ : syracuseStep 7598339 = 11397509) B11397509
theorem B5065559 : Blo 2249435 5065559 := bstep (se 1 (by rfl) ⟨3799169, by rfl⟩ : syracuseStep 5065559 = 7598339) B7598339
theorem B3377039 : Blo 2249435 3377039 := bstep (se 1 (by rfl) ⟨2532779, by rfl⟩ : syracuseStep 3377039 = 5065559) B5065559
theorem B2251359 : Blo 2249435 2251359 := bstep (se 1 (by rfl) ⟨1688519, by rfl⟩ : syracuseStep 2251359 = 3377039) B3377039
theorem B3377045 : Blo 2249435 3377045 := bbase (se 6 (by rfl) ⟨79149, by rfl⟩ : syracuseStep 3377045 = 158299) (by norm_num)
theorem B2251363 : Blo 2249435 2251363 := bstep (se 1 (by rfl) ⟨1688522, by rfl⟩ : syracuseStep 2251363 = 3377045) B3377045
theorem B2704693 : Blo 2249435 2704693 := bbase (se 5 (by rfl) ⟨126782, by rfl⟩ : syracuseStep 2704693 = 253565) (by norm_num)
theorem B3606257 : Blo 2249435 3606257 := bstep (se 2 (by rfl) ⟨1352346, by rfl⟩ : syracuseStep 3606257 = 2704693) B2704693
theorem B2404171 : Blo 2249435 2404171 := bstep (se 1 (by rfl) ⟨1803128, by rfl⟩ : syracuseStep 2404171 = 3606257) B3606257
theorem B12822245 : Blo 2249435 12822245 := bstep (se 4 (by rfl) ⟨1202085, by rfl⟩ : syracuseStep 12822245 = 2404171) B2404171
theorem B8548163 : Blo 2249435 8548163 := bstep (se 1 (by rfl) ⟨6411122, by rfl⟩ : syracuseStep 8548163 = 12822245) B12822245
theorem B5698775 : Blo 2249435 5698775 := bstep (se 1 (by rfl) ⟨4274081, by rfl⟩ : syracuseStep 5698775 = 8548163) B8548163
theorem B3799183 : Blo 2249435 3799183 := bstep (se 1 (by rfl) ⟨2849387, by rfl⟩ : syracuseStep 3799183 = 5698775) B5698775
theorem B5065577 : Blo 2249435 5065577 := bstep (se 2 (by rfl) ⟨1899591, by rfl⟩ : syracuseStep 5065577 = 3799183) B3799183
theorem B3377051 : Blo 2249435 3377051 := bstep (se 1 (by rfl) ⟨2532788, by rfl⟩ : syracuseStep 3377051 = 5065577) B5065577
theorem B2251367 : Blo 2249435 2251367 := bstep (se 1 (by rfl) ⟨1688525, by rfl⟩ : syracuseStep 2251367 = 3377051) B3377051
theorem B2532793 : Blo 2249435 2532793 := bbase (se 2 (by rfl) ⟨949797, by rfl⟩ : syracuseStep 2532793 = 1899595) (by norm_num)
theorem B3377057 : Blo 2249435 3377057 := bstep (se 2 (by rfl) ⟨1266396, by rfl⟩ : syracuseStep 3377057 = 2532793) B2532793
theorem B2251371 : Blo 2249435 2251371 := bstep (se 1 (by rfl) ⟨1688528, by rfl⟩ : syracuseStep 2251371 = 3377057) B3377057
theorem B5134709 : Blo 2249435 5134709 := bbase (se 5 (by rfl) ⟨240689, by rfl⟩ : syracuseStep 5134709 = 481379) (by norm_num)
theorem B13692557 : Blo 2249435 13692557 := bstep (se 3 (by rfl) ⟨2567354, by rfl⟩ : syracuseStep 13692557 = 5134709) B5134709
theorem B9128371 : Blo 2249435 9128371 := bstep (se 1 (by rfl) ⟨6846278, by rfl⟩ : syracuseStep 9128371 = 13692557) B13692557
theorem B12171161 : Blo 2249435 12171161 := bstep (se 2 (by rfl) ⟨4564185, by rfl⟩ : syracuseStep 12171161 = 9128371) B9128371
theorem B8114107 : Blo 2249435 8114107 := bstep (se 1 (by rfl) ⟨6085580, by rfl⟩ : syracuseStep 8114107 = 12171161) B12171161
theorem B10818809 : Blo 2249435 10818809 := bstep (se 2 (by rfl) ⟨4057053, by rfl⟩ : syracuseStep 10818809 = 8114107) B8114107
theorem B7212539 : Blo 2249435 7212539 := bstep (se 1 (by rfl) ⟨5409404, by rfl⟩ : syracuseStep 7212539 = 10818809) B10818809
theorem B4808359 : Blo 2249435 4808359 := bstep (se 1 (by rfl) ⟨3606269, by rfl⟩ : syracuseStep 4808359 = 7212539) B7212539
theorem B6411145 : Blo 2249435 6411145 := bstep (se 2 (by rfl) ⟨2404179, by rfl⟩ : syracuseStep 6411145 = 4808359) B4808359
theorem B8548193 : Blo 2249435 8548193 := bstep (se 2 (by rfl) ⟨3205572, by rfl⟩ : syracuseStep 8548193 = 6411145) B6411145
theorem B5698795 : Blo 2249435 5698795 := bstep (se 1 (by rfl) ⟨4274096, by rfl⟩ : syracuseStep 5698795 = 8548193) B8548193
theorem B7598393 : Blo 2249435 7598393 := bstep (se 2 (by rfl) ⟨2849397, by rfl⟩ : syracuseStep 7598393 = 5698795) B5698795
theorem B5065595 : Blo 2249435 5065595 := bstep (se 1 (by rfl) ⟨3799196, by rfl⟩ : syracuseStep 5065595 = 7598393) B7598393
theorem B3377063 : Blo 2249435 3377063 := bstep (se 1 (by rfl) ⟨2532797, by rfl⟩ : syracuseStep 3377063 = 5065595) B5065595
theorem B2251375 : Blo 2249435 2251375 := bstep (se 1 (by rfl) ⟨1688531, by rfl⟩ : syracuseStep 2251375 = 3377063) B3377063
theorem B3377069 : Blo 2249435 3377069 := bbase (se 3 (by rfl) ⟨633200, by rfl⟩ : syracuseStep 3377069 = 1266401) (by norm_num)
theorem B2251379 : Blo 2249435 2251379 := bstep (se 1 (by rfl) ⟨1688534, by rfl⟩ : syracuseStep 2251379 = 3377069) B3377069
theorem B5065613 : Blo 2249435 5065613 := bbase (se 3 (by rfl) ⟨949802, by rfl⟩ : syracuseStep 5065613 = 1899605) (by norm_num)
theorem B3377075 : Blo 2249435 3377075 := bstep (se 1 (by rfl) ⟨2532806, by rfl⟩ : syracuseStep 3377075 = 5065613) B5065613
theorem B2251383 : Blo 2249435 2251383 := bstep (se 1 (by rfl) ⟨1688537, by rfl⟩ : syracuseStep 2251383 = 3377075) B3377075
theorem B2849413 : Blo 2249435 2849413 := bbase (se 4 (by rfl) ⟨267132, by rfl⟩ : syracuseStep 2849413 = 534265) (by norm_num)
theorem B3799217 : Blo 2249435 3799217 := bstep (se 2 (by rfl) ⟨1424706, by rfl⟩ : syracuseStep 3799217 = 2849413) B2849413
theorem B2532811 : Blo 2249435 2532811 := bstep (se 1 (by rfl) ⟨1899608, by rfl⟩ : syracuseStep 2532811 = 3799217) B3799217
theorem B3377081 : Blo 2249435 3377081 := bstep (se 2 (by rfl) ⟨1266405, by rfl⟩ : syracuseStep 3377081 = 2532811) B2532811
theorem B2251387 : Blo 2249435 2251387 := bstep (se 1 (by rfl) ⟨1688540, by rfl⟩ : syracuseStep 2251387 = 3377081) B3377081
theorem B2704721 : Blo 2249435 2704721 := bbase (se 2 (by rfl) ⟨1014270, by rfl⟩ : syracuseStep 2704721 = 2028541) (by norm_num)
theorem B28850357 : Blo 2249435 28850357 := bstep (se 5 (by rfl) ⟨1352360, by rfl⟩ : syracuseStep 28850357 = 2704721) B2704721
theorem B19233571 : Blo 2249435 19233571 := bstep (se 1 (by rfl) ⟨14425178, by rfl⟩ : syracuseStep 19233571 = 28850357) B28850357
theorem B25644761 : Blo 2249435 25644761 := bstep (se 2 (by rfl) ⟨9616785, by rfl⟩ : syracuseStep 25644761 = 19233571) B19233571
theorem B17096507 : Blo 2249435 17096507 := bstep (se 1 (by rfl) ⟨12822380, by rfl⟩ : syracuseStep 17096507 = 25644761) B25644761
theorem B11397671 : Blo 2249435 11397671 := bstep (se 1 (by rfl) ⟨8548253, by rfl⟩ : syracuseStep 11397671 = 17096507) B17096507
theorem B7598447 : Blo 2249435 7598447 := bstep (se 1 (by rfl) ⟨5698835, by rfl⟩ : syracuseStep 7598447 = 11397671) B11397671
theorem B5065631 : Blo 2249435 5065631 := bstep (se 1 (by rfl) ⟨3799223, by rfl⟩ : syracuseStep 5065631 = 7598447) B7598447
theorem B3377087 : Blo 2249435 3377087 := bstep (se 1 (by rfl) ⟨2532815, by rfl⟩ : syracuseStep 3377087 = 5065631) B5065631
theorem B2251391 : Blo 2249435 2251391 := bstep (se 1 (by rfl) ⟨1688543, by rfl⟩ : syracuseStep 2251391 = 3377087) B3377087
theorem B3377093 : Blo 2249435 3377093 := bbase (se 4 (by rfl) ⟨316602, by rfl⟩ : syracuseStep 3377093 = 633205) (by norm_num)
theorem B2251395 : Blo 2249435 2251395 := bstep (se 1 (by rfl) ⟨1688546, by rfl⟩ : syracuseStep 2251395 = 3377093) B3377093
theorem B3799237 : Blo 2249435 3799237 := bbase (se 4 (by rfl) ⟨356178, by rfl⟩ : syracuseStep 3799237 = 712357) (by norm_num)
theorem B5065649 : Blo 2249435 5065649 := bstep (se 2 (by rfl) ⟨1899618, by rfl⟩ : syracuseStep 5065649 = 3799237) B3799237
theorem B3377099 : Blo 2249435 3377099 := bstep (se 1 (by rfl) ⟨2532824, by rfl⟩ : syracuseStep 3377099 = 5065649) B5065649
theorem B2251399 : Blo 2249435 2251399 := bstep (se 1 (by rfl) ⟨1688549, by rfl⟩ : syracuseStep 2251399 = 3377099) B3377099
theorem B2532829 : Blo 2249435 2532829 := bbase (se 3 (by rfl) ⟨474905, by rfl⟩ : syracuseStep 2532829 = 949811) (by norm_num)
theorem B3377105 : Blo 2249435 3377105 := bstep (se 2 (by rfl) ⟨1266414, by rfl⟩ : syracuseStep 3377105 = 2532829) B2532829
theorem B2251403 : Blo 2249435 2251403 := bstep (se 1 (by rfl) ⟨1688552, by rfl⟩ : syracuseStep 2251403 = 3377105) B3377105
theorem B7598501 : Blo 2249435 7598501 := bbase (se 4 (by rfl) ⟨712359, by rfl⟩ : syracuseStep 7598501 = 1424719) (by norm_num)
theorem B5065667 : Blo 2249435 5065667 := bstep (se 1 (by rfl) ⟨3799250, by rfl⟩ : syracuseStep 5065667 = 7598501) B7598501
theorem B3377111 : Blo 2249435 3377111 := bstep (se 1 (by rfl) ⟨2532833, by rfl⟩ : syracuseStep 3377111 = 5065667) B5065667
theorem B2251407 : Blo 2249435 2251407 := bstep (se 1 (by rfl) ⟨1688555, by rfl⟩ : syracuseStep 2251407 = 3377111) B3377111
theorem B3377117 : Blo 2249435 3377117 := bbase (se 3 (by rfl) ⟨633209, by rfl⟩ : syracuseStep 3377117 = 1266419) (by norm_num)
theorem B2251411 : Blo 2249435 2251411 := bstep (se 1 (by rfl) ⟨1688558, by rfl⟩ : syracuseStep 2251411 = 3377117) B3377117
theorem B5065685 : Blo 2249435 5065685 := bbase (se 7 (by rfl) ⟨59363, by rfl⟩ : syracuseStep 5065685 = 118727) (by norm_num)
theorem B3377123 : Blo 2249435 3377123 := bstep (se 1 (by rfl) ⟨2532842, by rfl⟩ : syracuseStep 3377123 = 5065685) B5065685
theorem B2251415 : Blo 2249435 2251415 := bstep (se 1 (by rfl) ⟨1688561, by rfl⟩ : syracuseStep 2251415 = 3377123) B3377123
theorem B4057133 : Blo 2249435 4057133 := bbase (se 3 (by rfl) ⟨760712, by rfl⟩ : syracuseStep 4057133 = 1521425) (by norm_num)
theorem B10819021 : Blo 2249435 10819021 := bstep (se 3 (by rfl) ⟨2028566, by rfl⟩ : syracuseStep 10819021 = 4057133) B4057133
theorem B14425361 : Blo 2249435 14425361 := bstep (se 2 (by rfl) ⟨5409510, by rfl⟩ : syracuseStep 14425361 = 10819021) B10819021
theorem B9616907 : Blo 2249435 9616907 := bstep (se 1 (by rfl) ⟨7212680, by rfl⟩ : syracuseStep 9616907 = 14425361) B14425361
theorem B6411271 : Blo 2249435 6411271 := bstep (se 1 (by rfl) ⟨4808453, by rfl⟩ : syracuseStep 6411271 = 9616907) B9616907
theorem B8548361 : Blo 2249435 8548361 := bstep (se 2 (by rfl) ⟨3205635, by rfl⟩ : syracuseStep 8548361 = 6411271) B6411271
theorem B5698907 : Blo 2249435 5698907 := bstep (se 1 (by rfl) ⟨4274180, by rfl⟩ : syracuseStep 5698907 = 8548361) B8548361
theorem B3799271 : Blo 2249435 3799271 := bstep (se 1 (by rfl) ⟨2849453, by rfl⟩ : syracuseStep 3799271 = 5698907) B5698907
theorem B2532847 : Blo 2249435 2532847 := bstep (se 1 (by rfl) ⟨1899635, by rfl⟩ : syracuseStep 2532847 = 3799271) B3799271
theorem B3377129 : Blo 2249435 3377129 := bstep (se 2 (by rfl) ⟨1266423, by rfl⟩ : syracuseStep 3377129 = 2532847) B2532847
theorem B2251419 : Blo 2249435 2251419 := bstep (se 1 (by rfl) ⟨1688564, by rfl⟩ : syracuseStep 2251419 = 3377129) B3377129
theorem B19233845 : Blo 2249435 19233845 := bbase (se 5 (by rfl) ⟨901586, by rfl⟩ : syracuseStep 19233845 = 1803173) (by norm_num)
theorem B12822563 : Blo 2249435 12822563 := bstep (se 1 (by rfl) ⟨9616922, by rfl⟩ : syracuseStep 12822563 = 19233845) B19233845
theorem B8548375 : Blo 2249435 8548375 := bstep (se 1 (by rfl) ⟨6411281, by rfl⟩ : syracuseStep 8548375 = 12822563) B12822563
theorem B11397833 : Blo 2249435 11397833 := bstep (se 2 (by rfl) ⟨4274187, by rfl⟩ : syracuseStep 11397833 = 8548375) B8548375
theorem B7598555 : Blo 2249435 7598555 := bstep (se 1 (by rfl) ⟨5698916, by rfl⟩ : syracuseStep 7598555 = 11397833) B11397833
theorem B5065703 : Blo 2249435 5065703 := bstep (se 1 (by rfl) ⟨3799277, by rfl⟩ : syracuseStep 5065703 = 7598555) B7598555
theorem B3377135 : Blo 2249435 3377135 := bstep (se 1 (by rfl) ⟨2532851, by rfl⟩ : syracuseStep 3377135 = 5065703) B5065703
theorem B2251423 : Blo 2249435 2251423 := bstep (se 1 (by rfl) ⟨1688567, by rfl⟩ : syracuseStep 2251423 = 3377135) B3377135
theorem B3377141 : Blo 2249435 3377141 := bbase (se 5 (by rfl) ⟨158303, by rfl⟩ : syracuseStep 3377141 = 316607) (by norm_num)
theorem B2251427 : Blo 2249435 2251427 := bstep (se 1 (by rfl) ⟨1688570, by rfl⟩ : syracuseStep 2251427 = 3377141) B3377141
theorem B5134837 : Blo 2249435 5134837 := bbase (se 5 (by rfl) ⟨240695, by rfl⟩ : syracuseStep 5134837 = 481391) (by norm_num)
theorem B6846449 : Blo 2249435 6846449 := bstep (se 2 (by rfl) ⟨2567418, by rfl⟩ : syracuseStep 6846449 = 5134837) B5134837
theorem B18257197 : Blo 2249435 18257197 := bstep (se 3 (by rfl) ⟨3423224, by rfl⟩ : syracuseStep 18257197 = 6846449) B6846449
theorem B24342929 : Blo 2249435 24342929 := bstep (se 2 (by rfl) ⟨9128598, by rfl⟩ : syracuseStep 24342929 = 18257197) B18257197
theorem B16228619 : Blo 2249435 16228619 := bstep (se 1 (by rfl) ⟨12171464, by rfl⟩ : syracuseStep 16228619 = 24342929) B24342929
theorem B10819079 : Blo 2249435 10819079 := bstep (se 1 (by rfl) ⟨8114309, by rfl⟩ : syracuseStep 10819079 = 16228619) B16228619
theorem B7212719 : Blo 2249435 7212719 := bstep (se 1 (by rfl) ⟨5409539, by rfl⟩ : syracuseStep 7212719 = 10819079) B10819079
theorem B4808479 : Blo 2249435 4808479 := bstep (se 1 (by rfl) ⟨3606359, by rfl⟩ : syracuseStep 4808479 = 7212719) B7212719
theorem B6411305 : Blo 2249435 6411305 := bstep (se 2 (by rfl) ⟨2404239, by rfl⟩ : syracuseStep 6411305 = 4808479) B4808479
theorem B4274203 : Blo 2249435 4274203 := bstep (se 1 (by rfl) ⟨3205652, by rfl⟩ : syracuseStep 4274203 = 6411305) B6411305
theorem B5698937 : Blo 2249435 5698937 := bstep (se 2 (by rfl) ⟨2137101, by rfl⟩ : syracuseStep 5698937 = 4274203) B4274203
theorem B3799291 : Blo 2249435 3799291 := bstep (se 1 (by rfl) ⟨2849468, by rfl⟩ : syracuseStep 3799291 = 5698937) B5698937
theorem B5065721 : Blo 2249435 5065721 := bstep (se 2 (by rfl) ⟨1899645, by rfl⟩ : syracuseStep 5065721 = 3799291) B3799291
theorem B3377147 : Blo 2249435 3377147 := bstep (se 1 (by rfl) ⟨2532860, by rfl⟩ : syracuseStep 3377147 = 5065721) B5065721
theorem B2251431 : Blo 2249435 2251431 := bstep (se 1 (by rfl) ⟨1688573, by rfl⟩ : syracuseStep 2251431 = 3377147) B3377147
theorem B2532865 : Blo 2249435 2532865 := bbase (se 2 (by rfl) ⟨949824, by rfl⟩ : syracuseStep 2532865 = 1899649) (by norm_num)
theorem B3377153 : Blo 2249435 3377153 := bstep (se 2 (by rfl) ⟨1266432, by rfl⟩ : syracuseStep 3377153 = 2532865) B2532865
theorem B2251435 : Blo 2249435 2251435 := bstep (se 1 (by rfl) ⟨1688576, by rfl⟩ : syracuseStep 2251435 = 3377153) B3377153
theorem C0 (j : ℕ) (h1 : 562358 ≤ j) (h2 : j ≤ 562858) : Blo 2249435 (4 * j + 3) := by
  interval_cases j
  · exact B2249435
  · exact B2249439
  · exact B2249443
  · exact B2249447
  · exact B2249451
  · exact B2249455
  · exact B2249459
  · exact B2249463
  · exact B2249467
  · exact B2249471
  · exact B2249475
  · exact B2249479
  · exact B2249483
  · exact B2249487
  · exact B2249491
  · exact B2249495
  · exact B2249499
  · exact B2249503
  · exact B2249507
  · exact B2249511
  · exact B2249515
  · exact B2249519
  · exact B2249523
  · exact B2249527
  · exact B2249531
  · exact B2249535
  · exact B2249539
  · exact B2249543
  · exact B2249547
  · exact B2249551
  · exact B2249555
  · exact B2249559
  · exact B2249563
  · exact B2249567
  · exact B2249571
  · exact B2249575
  · exact B2249579
  · exact B2249583
  · exact B2249587
  · exact B2249591
  · exact B2249595
  · exact B2249599
  · exact B2249603
  · exact B2249607
  · exact B2249611
  · exact B2249615
  · exact B2249619
  · exact B2249623
  · exact B2249627
  · exact B2249631
  · exact B2249635
  · exact B2249639
  · exact B2249643
  · exact B2249647
  · exact B2249651
  · exact B2249655
  · exact B2249659
  · exact B2249663
  · exact B2249667
  · exact B2249671
  · exact B2249675
  · exact B2249679
  · exact B2249683
  · exact B2249687
  · exact B2249691
  · exact B2249695
  · exact B2249699
  · exact B2249703
  · exact B2249707
  · exact B2249711
  · exact B2249715
  · exact B2249719
  · exact B2249723
  · exact B2249727
  · exact B2249731
  · exact B2249735
  · exact B2249739
  · exact B2249743
  · exact B2249747
  · exact B2249751
  · exact B2249755
  · exact B2249759
  · exact B2249763
  · exact B2249767
  · exact B2249771
  · exact B2249775
  · exact B2249779
  · exact B2249783
  · exact B2249787
  · exact B2249791
  · exact B2249795
  · exact B2249799
  · exact B2249803
  · exact B2249807
  · exact B2249811
  · exact B2249815
  · exact B2249819
  · exact B2249823
  · exact B2249827
  · exact B2249831
  · exact B2249835
  · exact B2249839
  · exact B2249843
  · exact B2249847
  · exact B2249851
  · exact B2249855
  · exact B2249859
  · exact B2249863
  · exact B2249867
  · exact B2249871
  · exact B2249875
  · exact B2249879
  · exact B2249883
  · exact B2249887
  · exact B2249891
  · exact B2249895
  · exact B2249899
  · exact B2249903
  · exact B2249907
  · exact B2249911
  · exact B2249915
  · exact B2249919
  · exact B2249923
  · exact B2249927
  · exact B2249931
  · exact B2249935
  · exact B2249939
  · exact B2249943
  · exact B2249947
  · exact B2249951
  · exact B2249955
  · exact B2249959
  · exact B2249963
  · exact B2249967
  · exact B2249971
  · exact B2249975
  · exact B2249979
  · exact B2249983
  · exact B2249987
  · exact B2249991
  · exact B2249995
  · exact B2249999
  · exact B2250003
  · exact B2250007
  · exact B2250011
  · exact B2250015
  · exact B2250019
  · exact B2250023
  · exact B2250027
  · exact B2250031
  · exact B2250035
  · exact B2250039
  · exact B2250043
  · exact B2250047
  · exact B2250051
  · exact B2250055
  · exact B2250059
  · exact B2250063
  · exact B2250067
  · exact B2250071
  · exact B2250075
  · exact B2250079
  · exact B2250083
  · exact B2250087
  · exact B2250091
  · exact B2250095
  · exact B2250099
  · exact B2250103
  · exact B2250107
  · exact B2250111
  · exact B2250115
  · exact B2250119
  · exact B2250123
  · exact B2250127
  · exact B2250131
  · exact B2250135
  · exact B2250139
  · exact B2250143
  · exact B2250147
  · exact B2250151
  · exact B2250155
  · exact B2250159
  · exact B2250163
  · exact B2250167
  · exact B2250171
  · exact B2250175
  · exact B2250179
  · exact B2250183
  · exact B2250187
  · exact B2250191
  · exact B2250195
  · exact B2250199
  · exact B2250203
  · exact B2250207
  · exact B2250211
  · exact B2250215
  · exact B2250219
  · exact B2250223
  · exact B2250227
  · exact B2250231
  · exact B2250235
  · exact B2250239
  · exact B2250243
  · exact B2250247
  · exact B2250251
  · exact B2250255
  · exact B2250259
  · exact B2250263
  · exact B2250267
  · exact B2250271
  · exact B2250275
  · exact B2250279
  · exact B2250283
  · exact B2250287
  · exact B2250291
  · exact B2250295
  · exact B2250299
  · exact B2250303
  · exact B2250307
  · exact B2250311
  · exact B2250315
  · exact B2250319
  · exact B2250323
  · exact B2250327
  · exact B2250331
  · exact B2250335
  · exact B2250339
  · exact B2250343
  · exact B2250347
  · exact B2250351
  · exact B2250355
  · exact B2250359
  · exact B2250363
  · exact B2250367
  · exact B2250371
  · exact B2250375
  · exact B2250379
  · exact B2250383
  · exact B2250387
  · exact B2250391
  · exact B2250395
  · exact B2250399
  · exact B2250403
  · exact B2250407
  · exact B2250411
  · exact B2250415
  · exact B2250419
  · exact B2250423
  · exact B2250427
  · exact B2250431
  · exact B2250435
  · exact B2250439
  · exact B2250443
  · exact B2250447
  · exact B2250451
  · exact B2250455
  · exact B2250459
  · exact B2250463
  · exact B2250467
  · exact B2250471
  · exact B2250475
  · exact B2250479
  · exact B2250483
  · exact B2250487
  · exact B2250491
  · exact B2250495
  · exact B2250499
  · exact B2250503
  · exact B2250507
  · exact B2250511
  · exact B2250515
  · exact B2250519
  · exact B2250523
  · exact B2250527
  · exact B2250531
  · exact B2250535
  · exact B2250539
  · exact B2250543
  · exact B2250547
  · exact B2250551
  · exact B2250555
  · exact B2250559
  · exact B2250563
  · exact B2250567
  · exact B2250571
  · exact B2250575
  · exact B2250579
  · exact B2250583
  · exact B2250587
  · exact B2250591
  · exact B2250595
  · exact B2250599
  · exact B2250603
  · exact B2250607
  · exact B2250611
  · exact B2250615
  · exact B2250619
  · exact B2250623
  · exact B2250627
  · exact B2250631
  · exact B2250635
  · exact B2250639
  · exact B2250643
  · exact B2250647
  · exact B2250651
  · exact B2250655
  · exact B2250659
  · exact B2250663
  · exact B2250667
  · exact B2250671
  · exact B2250675
  · exact B2250679
  · exact B2250683
  · exact B2250687
  · exact B2250691
  · exact B2250695
  · exact B2250699
  · exact B2250703
  · exact B2250707
  · exact B2250711
  · exact B2250715
  · exact B2250719
  · exact B2250723
  · exact B2250727
  · exact B2250731
  · exact B2250735
  · exact B2250739
  · exact B2250743
  · exact B2250747
  · exact B2250751
  · exact B2250755
  · exact B2250759
  · exact B2250763
  · exact B2250767
  · exact B2250771
  · exact B2250775
  · exact B2250779
  · exact B2250783
  · exact B2250787
  · exact B2250791
  · exact B2250795
  · exact B2250799
  · exact B2250803
  · exact B2250807
  · exact B2250811
  · exact B2250815
  · exact B2250819
  · exact B2250823
  · exact B2250827
  · exact B2250831
  · exact B2250835
  · exact B2250839
  · exact B2250843
  · exact B2250847
  · exact B2250851
  · exact B2250855
  · exact B2250859
  · exact B2250863
  · exact B2250867
  · exact B2250871
  · exact B2250875
  · exact B2250879
  · exact B2250883
  · exact B2250887
  · exact B2250891
  · exact B2250895
  · exact B2250899
  · exact B2250903
  · exact B2250907
  · exact B2250911
  · exact B2250915
  · exact B2250919
  · exact B2250923
  · exact B2250927
  · exact B2250931
  · exact B2250935
  · exact B2250939
  · exact B2250943
  · exact B2250947
  · exact B2250951
  · exact B2250955
  · exact B2250959
  · exact B2250963
  · exact B2250967
  · exact B2250971
  · exact B2250975
  · exact B2250979
  · exact B2250983
  · exact B2250987
  · exact B2250991
  · exact B2250995
  · exact B2250999
  · exact B2251003
  · exact B2251007
  · exact B2251011
  · exact B2251015
  · exact B2251019
  · exact B2251023
  · exact B2251027
  · exact B2251031
  · exact B2251035
  · exact B2251039
  · exact B2251043
  · exact B2251047
  · exact B2251051
  · exact B2251055
  · exact B2251059
  · exact B2251063
  · exact B2251067
  · exact B2251071
  · exact B2251075
  · exact B2251079
  · exact B2251083
  · exact B2251087
  · exact B2251091
  · exact B2251095
  · exact B2251099
  · exact B2251103
  · exact B2251107
  · exact B2251111
  · exact B2251115
  · exact B2251119
  · exact B2251123
  · exact B2251127
  · exact B2251131
  · exact B2251135
  · exact B2251139
  · exact B2251143
  · exact B2251147
  · exact B2251151
  · exact B2251155
  · exact B2251159
  · exact B2251163
  · exact B2251167
  · exact B2251171
  · exact B2251175
  · exact B2251179
  · exact B2251183
  · exact B2251187
  · exact B2251191
  · exact B2251195
  · exact B2251199
  · exact B2251203
  · exact B2251207
  · exact B2251211
  · exact B2251215
  · exact B2251219
  · exact B2251223
  · exact B2251227
  · exact B2251231
  · exact B2251235
  · exact B2251239
  · exact B2251243
  · exact B2251247
  · exact B2251251
  · exact B2251255
  · exact B2251259
  · exact B2251263
  · exact B2251267
  · exact B2251271
  · exact B2251275
  · exact B2251279
  · exact B2251283
  · exact B2251287
  · exact B2251291
  · exact B2251295
  · exact B2251299
  · exact B2251303
  · exact B2251307
  · exact B2251311
  · exact B2251315
  · exact B2251319
  · exact B2251323
  · exact B2251327
  · exact B2251331
  · exact B2251335
  · exact B2251339
  · exact B2251343
  · exact B2251347
  · exact B2251351
  · exact B2251355
  · exact B2251359
  · exact B2251363
  · exact B2251367
  · exact B2251371
  · exact B2251375
  · exact B2251379
  · exact B2251383
  · exact B2251387
  · exact B2251391
  · exact B2251395
  · exact B2251399
  · exact B2251403
  · exact B2251407
  · exact B2251411
  · exact B2251415
  · exact B2251419
  · exact B2251423
  · exact B2251427
  · exact B2251431
  · exact B2251435
theorem solution (m : ℕ) (hlo : 2249435 ≤ m) (hhi : m ≤ 2251435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 562358 ≤ j := by omega
    have hj2 : j ≤ 562858 := by omega
    have hb : Blo 2249435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
