-- Prove2me | solution 1 for syracuse_descends_range_143792_147792
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:37.821953+00:00
-- url     : https://prove2.me/submissions/6eae3450-8cf0-44cb-88e4-b3f20e66d2fc

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


theorem B163849 : Blo 143792 163849 := bbase (se 2 (by rfl) ⟨61443, by rfl⟩ : syracuseStep 163849 = 122887) (by norm_num)
theorem B557077 : Blo 143792 557077 := bbase (se 6 (by rfl) ⟨13056, by rfl⟩ : syracuseStep 557077 = 26113) (by norm_num)
theorem B327725 : Blo 143792 327725 := bbase (se 3 (by rfl) ⟨61448, by rfl⟩ : syracuseStep 327725 = 122897) (by norm_num)
theorem B163885 : Blo 143792 163885 := bbase (se 3 (by rfl) ⟨30728, by rfl⟩ : syracuseStep 163885 = 61457) (by norm_num)
theorem B163921 : Blo 143792 163921 := bbase (se 2 (by rfl) ⟨61470, by rfl⟩ : syracuseStep 163921 = 122941) (by norm_num)
theorem B262261 : Blo 143792 262261 := bbase (se 5 (by rfl) ⟨12293, by rfl⟩ : syracuseStep 262261 = 24587) (by norm_num)
theorem B327797 : Blo 143792 327797 := bbase (se 5 (by rfl) ⟨15365, by rfl⟩ : syracuseStep 327797 = 30731) (by norm_num)
theorem B163957 : Blo 143792 163957 := bbase (se 5 (by rfl) ⟨7685, by rfl⟩ : syracuseStep 163957 = 15371) (by norm_num)
theorem B393349 : Blo 143792 393349 := bbase (se 4 (by rfl) ⟨36876, by rfl⟩ : syracuseStep 393349 = 73753) (by norm_num)
theorem B491669 : Blo 143792 491669 := bbase (se 6 (by rfl) ⟨11523, by rfl⟩ : syracuseStep 491669 = 23047) (by norm_num)
theorem B163993 : Blo 143792 163993 := bbase (se 2 (by rfl) ⟨61497, by rfl⟩ : syracuseStep 163993 = 122995) (by norm_num)
theorem B327869 : Blo 143792 327869 := bbase (se 3 (by rfl) ⟨61475, by rfl⟩ : syracuseStep 327869 = 122951) (by norm_num)
theorem B164029 : Blo 143792 164029 := bbase (se 3 (by rfl) ⟨30755, by rfl⟩ : syracuseStep 164029 = 61511) (by norm_num)
theorem B164065 : Blo 143792 164065 := bbase (se 2 (by rfl) ⟨61524, by rfl⟩ : syracuseStep 164065 = 123049) (by norm_num)
theorem B327941 : Blo 143792 327941 := bbase (se 4 (by rfl) ⟨30744, by rfl⟩ : syracuseStep 327941 = 61489) (by norm_num)
theorem B164101 : Blo 143792 164101 := bbase (se 4 (by rfl) ⟨15384, by rfl⟩ : syracuseStep 164101 = 30769) (by norm_num)
theorem B622885 : Blo 143792 622885 := bbase (se 4 (by rfl) ⟨58395, by rfl⟩ : syracuseStep 622885 = 116791) (by norm_num)
theorem B164137 : Blo 143792 164137 := bbase (se 2 (by rfl) ⟨61551, by rfl⟩ : syracuseStep 164137 = 123103) (by norm_num)
theorem B557381 : Blo 143792 557381 := bbase (se 4 (by rfl) ⟨52254, by rfl⟩ : syracuseStep 557381 = 104509) (by norm_num)
theorem B328013 : Blo 143792 328013 := bbase (se 3 (by rfl) ⟨61502, by rfl⟩ : syracuseStep 328013 = 123005) (by norm_num)
theorem B164173 : Blo 143792 164173 := bbase (se 3 (by rfl) ⟨30782, by rfl⟩ : syracuseStep 164173 = 61565) (by norm_num)
theorem B164209 : Blo 143792 164209 := bbase (se 2 (by rfl) ⟨61578, by rfl⟩ : syracuseStep 164209 = 123157) (by norm_num)
theorem B328085 : Blo 143792 328085 := bbase (se 6 (by rfl) ⟨7689, by rfl⟩ : syracuseStep 328085 = 15379) (by norm_num)
theorem B164245 : Blo 143792 164245 := bbase (se 6 (by rfl) ⟨3849, by rfl⟩ : syracuseStep 164245 = 7699) (by norm_num)
theorem B393653 : Blo 143792 393653 := bbase (se 5 (by rfl) ⟨18452, by rfl⟩ : syracuseStep 393653 = 36905) (by norm_num)
theorem B164281 : Blo 143792 164281 := bbase (se 2 (by rfl) ⟨61605, by rfl⟩ : syracuseStep 164281 = 123211) (by norm_num)
theorem B328157 : Blo 143792 328157 := bbase (se 3 (by rfl) ⟨61529, by rfl⟩ : syracuseStep 328157 = 123059) (by norm_num)
theorem B164317 : Blo 143792 164317 := bbase (se 3 (by rfl) ⟨30809, by rfl⟩ : syracuseStep 164317 = 61619) (by norm_num)
theorem B164353 : Blo 143792 164353 := bbase (se 2 (by rfl) ⟨61632, by rfl⟩ : syracuseStep 164353 = 123265) (by norm_num)
theorem B328205 : Blo 143792 328205 := bbase (se 3 (by rfl) ⟨61538, by rfl⟩ : syracuseStep 328205 = 123077) (by norm_num)
theorem B328229 : Blo 143792 328229 := bbase (se 4 (by rfl) ⟨30771, by rfl⟩ : syracuseStep 328229 = 61543) (by norm_num)
theorem B164389 : Blo 143792 164389 := bbase (se 4 (by rfl) ⟨15411, by rfl⟩ : syracuseStep 164389 = 30823) (by norm_num)
theorem B492101 : Blo 143792 492101 := bbase (se 4 (by rfl) ⟨46134, by rfl⟩ : syracuseStep 492101 = 92269) (by norm_num)
theorem B164425 : Blo 143792 164425 := bbase (se 2 (by rfl) ⟨61659, by rfl⟩ : syracuseStep 164425 = 123319) (by norm_num)
theorem B328301 : Blo 143792 328301 := bbase (se 3 (by rfl) ⟨61556, by rfl⟩ : syracuseStep 328301 = 123113) (by norm_num)
theorem B164461 : Blo 143792 164461 := bbase (se 3 (by rfl) ⟨30836, by rfl⟩ : syracuseStep 164461 = 61673) (by norm_num)
theorem B164497 : Blo 143792 164497 := bbase (se 2 (by rfl) ⟨61686, by rfl⟩ : syracuseStep 164497 = 123373) (by norm_num)
theorem B2523797 : Blo 143792 2523797 := bbase (se 6 (by rfl) ⟨59151, by rfl⟩ : syracuseStep 2523797 = 118303) (by norm_num)
theorem B328373 : Blo 143792 328373 := bbase (se 5 (by rfl) ⟨15392, by rfl⟩ : syracuseStep 328373 = 30785) (by norm_num)
theorem B164533 : Blo 143792 164533 := bbase (se 5 (by rfl) ⟨7712, by rfl⟩ : syracuseStep 164533 = 15425) (by norm_num)
theorem B164569 : Blo 143792 164569 := bbase (se 2 (by rfl) ⟨61713, by rfl⟩ : syracuseStep 164569 = 123427) (by norm_num)
theorem B328421 : Blo 143792 328421 := bbase (se 4 (by rfl) ⟨30789, by rfl⟩ : syracuseStep 328421 = 61579) (by norm_num)
theorem B328445 : Blo 143792 328445 := bbase (se 3 (by rfl) ⟨61583, by rfl⟩ : syracuseStep 328445 = 123167) (by norm_num)
theorem B164605 : Blo 143792 164605 := bbase (se 3 (by rfl) ⟨30863, by rfl⟩ : syracuseStep 164605 = 61727) (by norm_num)
theorem B819989 : Blo 143792 819989 := bbase (se 6 (by rfl) ⟨19218, by rfl⟩ : syracuseStep 819989 = 38437) (by norm_num)
theorem B164641 : Blo 143792 164641 := bbase (se 2 (by rfl) ⟨61740, by rfl⟩ : syracuseStep 164641 = 123481) (by norm_num)
theorem B328517 : Blo 143792 328517 := bbase (se 4 (by rfl) ⟨30798, by rfl⟩ : syracuseStep 328517 = 61597) (by norm_num)
theorem B164677 : Blo 143792 164677 := bbase (se 4 (by rfl) ⟨15438, by rfl⟩ : syracuseStep 164677 = 30877) (by norm_num)
theorem B394085 : Blo 143792 394085 := bbase (se 4 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 394085 = 73891) (by norm_num)
theorem B164713 : Blo 143792 164713 := bbase (se 2 (by rfl) ⟨61767, by rfl⟩ : syracuseStep 164713 = 123535) (by norm_num)
theorem B328589 : Blo 143792 328589 := bbase (se 3 (by rfl) ⟨61610, by rfl⟩ : syracuseStep 328589 = 123221) (by norm_num)
theorem B164749 : Blo 143792 164749 := bbase (se 3 (by rfl) ⟨30890, by rfl⟩ : syracuseStep 164749 = 61781) (by norm_num)
theorem B164785 : Blo 143792 164785 := bbase (se 2 (by rfl) ⟨61794, by rfl⟩ : syracuseStep 164785 = 123589) (by norm_num)
theorem B263093 : Blo 143792 263093 := bbase (se 5 (by rfl) ⟨12332, by rfl⟩ : syracuseStep 263093 = 24665) (by norm_num)
theorem B328661 : Blo 143792 328661 := bbase (se 7 (by rfl) ⟨3851, by rfl⟩ : syracuseStep 328661 = 7703) (by norm_num)
theorem B164821 : Blo 143792 164821 := bbase (se 7 (by rfl) ⟨1931, by rfl⟩ : syracuseStep 164821 = 3863) (by norm_num)
theorem B492533 : Blo 143792 492533 := bbase (se 5 (by rfl) ⟨23087, by rfl⟩ : syracuseStep 492533 = 46175) (by norm_num)
theorem B164857 : Blo 143792 164857 := bbase (se 2 (by rfl) ⟨61821, by rfl⟩ : syracuseStep 164857 = 123643) (by norm_num)
theorem B328733 : Blo 143792 328733 := bbase (se 3 (by rfl) ⟨61637, by rfl⟩ : syracuseStep 328733 = 123275) (by norm_num)
theorem B164893 : Blo 143792 164893 := bbase (se 3 (by rfl) ⟨30917, by rfl⟩ : syracuseStep 164893 = 61835) (by norm_num)
theorem B492581 : Blo 143792 492581 := bbase (se 4 (by rfl) ⟨46179, by rfl⟩ : syracuseStep 492581 = 92359) (by norm_num)
theorem B164929 : Blo 143792 164929 := bbase (se 2 (by rfl) ⟨61848, by rfl⟩ : syracuseStep 164929 = 123697) (by norm_num)
theorem B230501 : Blo 143792 230501 := bbase (se 4 (by rfl) ⟨21609, by rfl⟩ : syracuseStep 230501 = 43219) (by norm_num)
theorem B328805 : Blo 143792 328805 := bbase (se 4 (by rfl) ⟨30825, by rfl⟩ : syracuseStep 328805 = 61651) (by norm_num)
theorem B164965 : Blo 143792 164965 := bbase (se 4 (by rfl) ⟨15465, by rfl⟩ : syracuseStep 164965 = 30931) (by norm_num)
theorem B165001 : Blo 143792 165001 := bbase (se 2 (by rfl) ⟨61875, by rfl⟩ : syracuseStep 165001 = 123751) (by norm_num)
theorem B328877 : Blo 143792 328877 := bbase (se 3 (by rfl) ⟨61664, by rfl⟩ : syracuseStep 328877 = 123329) (by norm_num)
theorem B165037 : Blo 143792 165037 := bbase (se 3 (by rfl) ⟨30944, by rfl⟩ : syracuseStep 165037 = 61889) (by norm_num)
theorem B165073 : Blo 143792 165073 := bbase (se 2 (by rfl) ⟨61902, by rfl⟩ : syracuseStep 165073 = 123805) (by norm_num)
theorem B2819285 : Blo 143792 2819285 := bbase (se 7 (by rfl) ⟨33038, by rfl⟩ : syracuseStep 2819285 = 66077) (by norm_num)
theorem B328949 : Blo 143792 328949 := bbase (se 5 (by rfl) ⟨15419, by rfl⟩ : syracuseStep 328949 = 30839) (by norm_num)
theorem B165109 : Blo 143792 165109 := bbase (se 5 (by rfl) ⟨7739, by rfl⟩ : syracuseStep 165109 = 15479) (by norm_num)
theorem B165145 : Blo 143792 165145 := bbase (se 2 (by rfl) ⟨61929, by rfl⟩ : syracuseStep 165145 = 123859) (by norm_num)
theorem B329005 : Blo 143792 329005 := bbase (se 3 (by rfl) ⟨61688, by rfl⟩ : syracuseStep 329005 = 123377) (by norm_num)
theorem B296245 : Blo 143792 296245 := bbase (se 5 (by rfl) ⟨13886, by rfl⟩ : syracuseStep 296245 = 27773) (by norm_num)
theorem B329021 : Blo 143792 329021 := bbase (se 3 (by rfl) ⟨61691, by rfl⟩ : syracuseStep 329021 = 123383) (by norm_num)
theorem B165181 : Blo 143792 165181 := bbase (se 3 (by rfl) ⟨30971, by rfl⟩ : syracuseStep 165181 = 61943) (by norm_num)
theorem B230725 : Blo 143792 230725 := bbase (se 4 (by rfl) ⟨21630, by rfl⟩ : syracuseStep 230725 = 43261) (by norm_num)
theorem B165217 : Blo 143792 165217 := bbase (se 2 (by rfl) ⟨61956, by rfl⟩ : syracuseStep 165217 = 123913) (by norm_num)
theorem B296309 : Blo 143792 296309 := bbase (se 5 (by rfl) ⟨13889, by rfl⟩ : syracuseStep 296309 = 27779) (by norm_num)
theorem B230789 : Blo 143792 230789 := bbase (se 4 (by rfl) ⟨21636, by rfl⟩ : syracuseStep 230789 = 43273) (by norm_num)
theorem B329093 : Blo 143792 329093 := bbase (se 4 (by rfl) ⟨30852, by rfl⟩ : syracuseStep 329093 = 61705) (by norm_num)
theorem B165253 : Blo 143792 165253 := bbase (se 4 (by rfl) ⟨15492, by rfl⟩ : syracuseStep 165253 = 30985) (by norm_num)
theorem B492965 : Blo 143792 492965 := bbase (se 4 (by rfl) ⟨46215, by rfl⟩ : syracuseStep 492965 = 92431) (by norm_num)
theorem B165289 : Blo 143792 165289 := bbase (se 2 (by rfl) ⟨61983, by rfl⟩ : syracuseStep 165289 = 123967) (by norm_num)
theorem B329165 : Blo 143792 329165 := bbase (se 3 (by rfl) ⟨61718, by rfl⟩ : syracuseStep 329165 = 123437) (by norm_num)
theorem B165325 : Blo 143792 165325 := bbase (se 3 (by rfl) ⟨30998, by rfl⟩ : syracuseStep 165325 = 61997) (by norm_num)
theorem B165361 : Blo 143792 165361 := bbase (se 2 (by rfl) ⟨62010, by rfl⟩ : syracuseStep 165361 = 124021) (by norm_num)
theorem B230917 : Blo 143792 230917 := bbase (se 4 (by rfl) ⟨21648, by rfl⟩ : syracuseStep 230917 = 43297) (by norm_num)
theorem B329237 : Blo 143792 329237 := bbase (se 6 (by rfl) ⟨7716, by rfl⟩ : syracuseStep 329237 = 15433) (by norm_num)
theorem B165397 : Blo 143792 165397 := bbase (se 6 (by rfl) ⟨3876, by rfl⟩ : syracuseStep 165397 = 7753) (by norm_num)
theorem B165433 : Blo 143792 165433 := bbase (se 2 (by rfl) ⟨62037, by rfl⟩ : syracuseStep 165433 = 124075) (by norm_num)
theorem B329309 : Blo 143792 329309 := bbase (se 3 (by rfl) ⟨61745, by rfl⟩ : syracuseStep 329309 = 123491) (by norm_num)
theorem B165469 : Blo 143792 165469 := bbase (se 3 (by rfl) ⟨31025, by rfl⟩ : syracuseStep 165469 = 62051) (by norm_num)
theorem B165505 : Blo 143792 165505 := bbase (se 2 (by rfl) ⟨62064, by rfl⟩ : syracuseStep 165505 = 124129) (by norm_num)
theorem B394885 : Blo 143792 394885 := bbase (se 4 (by rfl) ⟨37020, by rfl⟩ : syracuseStep 394885 = 74041) (by norm_num)
theorem B329381 : Blo 143792 329381 := bbase (se 4 (by rfl) ⟨30879, by rfl⟩ : syracuseStep 329381 = 61759) (by norm_num)
theorem B165541 : Blo 143792 165541 := bbase (se 4 (by rfl) ⟨15519, by rfl⟩ : syracuseStep 165541 = 31039) (by norm_num)
theorem B394949 : Blo 143792 394949 := bbase (se 4 (by rfl) ⟨37026, by rfl⟩ : syracuseStep 394949 = 74053) (by norm_num)
theorem B165577 : Blo 143792 165577 := bbase (se 2 (by rfl) ⟨62091, by rfl⟩ : syracuseStep 165577 = 124183) (by norm_num)
theorem B329453 : Blo 143792 329453 := bbase (se 3 (by rfl) ⟨61772, by rfl⟩ : syracuseStep 329453 = 123545) (by norm_num)
theorem B165613 : Blo 143792 165613 := bbase (se 3 (by rfl) ⟨31052, by rfl⟩ : syracuseStep 165613 = 62105) (by norm_num)
theorem B165649 : Blo 143792 165649 := bbase (se 2 (by rfl) ⟨62118, by rfl⟩ : syracuseStep 165649 = 124237) (by norm_num)
theorem B329525 : Blo 143792 329525 := bbase (se 5 (by rfl) ⟨15446, by rfl⟩ : syracuseStep 329525 = 30893) (by norm_num)
theorem B165685 : Blo 143792 165685 := bbase (se 5 (by rfl) ⟨7766, by rfl⟩ : syracuseStep 165685 = 15533) (by norm_num)
theorem B198469 : Blo 143792 198469 := bbase (se 4 (by rfl) ⟨18606, by rfl⟩ : syracuseStep 198469 = 37213) (by norm_num)
theorem B493397 : Blo 143792 493397 := bbase (se 9 (by rfl) ⟨1445, by rfl⟩ : syracuseStep 493397 = 2891) (by norm_num)
theorem B165721 : Blo 143792 165721 := bbase (se 2 (by rfl) ⟨62145, by rfl⟩ : syracuseStep 165721 = 124291) (by norm_num)
theorem B264029 : Blo 143792 264029 := bbase (se 3 (by rfl) ⟨49505, by rfl⟩ : syracuseStep 264029 = 99011) (by norm_num)
theorem B296797 : Blo 143792 296797 := bbase (se 3 (by rfl) ⟨55649, by rfl⟩ : syracuseStep 296797 = 111299) (by norm_num)
theorem B329597 : Blo 143792 329597 := bbase (se 3 (by rfl) ⟨61799, by rfl⟩ : syracuseStep 329597 = 123599) (by norm_num)
theorem B165757 : Blo 143792 165757 := bbase (se 3 (by rfl) ⟨31079, by rfl⟩ : syracuseStep 165757 = 62159) (by norm_num)
theorem B165793 : Blo 143792 165793 := bbase (se 2 (by rfl) ⟨62172, by rfl⟩ : syracuseStep 165793 = 124345) (by norm_num)
theorem B329669 : Blo 143792 329669 := bbase (se 4 (by rfl) ⟨30906, by rfl⟩ : syracuseStep 329669 = 61813) (by norm_num)
theorem B165829 : Blo 143792 165829 := bbase (se 4 (by rfl) ⟨15546, by rfl⟩ : syracuseStep 165829 = 31093) (by norm_num)
theorem B165865 : Blo 143792 165865 := bbase (se 2 (by rfl) ⟨62199, by rfl⟩ : syracuseStep 165865 = 124399) (by norm_num)
theorem B329741 : Blo 143792 329741 := bbase (se 3 (by rfl) ⟨61826, by rfl⟩ : syracuseStep 329741 = 123653) (by norm_num)
theorem B165901 : Blo 143792 165901 := bbase (se 3 (by rfl) ⟨31106, by rfl⟩ : syracuseStep 165901 = 62213) (by norm_num)
theorem B165937 : Blo 143792 165937 := bbase (se 2 (by rfl) ⟨62226, by rfl⟩ : syracuseStep 165937 = 124453) (by norm_num)
theorem B329813 : Blo 143792 329813 := bbase (se 8 (by rfl) ⟨1932, by rfl⟩ : syracuseStep 329813 = 3865) (by norm_num)
theorem B165973 : Blo 143792 165973 := bbase (se 8 (by rfl) ⟨972, by rfl⟩ : syracuseStep 165973 = 1945) (by norm_num)
theorem B166009 : Blo 143792 166009 := bbase (se 2 (by rfl) ⟨62253, by rfl⟩ : syracuseStep 166009 = 124507) (by norm_num)
theorem B329885 : Blo 143792 329885 := bbase (se 3 (by rfl) ⟨61853, by rfl⟩ : syracuseStep 329885 = 123707) (by norm_num)
theorem B166045 : Blo 143792 166045 := bbase (se 3 (by rfl) ⟨31133, by rfl⟩ : syracuseStep 166045 = 62267) (by norm_num)
theorem B1116341 : Blo 143792 1116341 := bbase (se 5 (by rfl) ⟨52328, by rfl⟩ : syracuseStep 1116341 = 104657) (by norm_num)
theorem B166081 : Blo 143792 166081 := bbase (se 2 (by rfl) ⟨62280, by rfl⟩ : syracuseStep 166081 = 124561) (by norm_num)
theorem B592069 : Blo 143792 592069 := bbase (se 4 (by rfl) ⟨55506, by rfl⟩ : syracuseStep 592069 = 111013) (by norm_num)
theorem B329957 : Blo 143792 329957 := bbase (se 4 (by rfl) ⟨30933, by rfl⟩ : syracuseStep 329957 = 61867) (by norm_num)
theorem B166117 : Blo 143792 166117 := bbase (se 4 (by rfl) ⟨15573, by rfl⟩ : syracuseStep 166117 = 31147) (by norm_num)
theorem B166141 : Blo 143792 166141 := bbase (se 3 (by rfl) ⟨31151, by rfl⟩ : syracuseStep 166141 = 62303) (by norm_num)
theorem B493829 : Blo 143792 493829 := bbase (se 4 (by rfl) ⟨46296, by rfl⟩ : syracuseStep 493829 = 92593) (by norm_num)
theorem B166153 : Blo 143792 166153 := bbase (se 2 (by rfl) ⟨62307, by rfl⟩ : syracuseStep 166153 = 124615) (by norm_num)
theorem B2787605 : Blo 143792 2787605 := bbase (se 6 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 2787605 = 130669) (by norm_num)
theorem B330029 : Blo 143792 330029 := bbase (se 3 (by rfl) ⟨61880, by rfl⟩ : syracuseStep 330029 = 123761) (by norm_num)
theorem B166189 : Blo 143792 166189 := bbase (se 3 (by rfl) ⟨31160, by rfl⟩ : syracuseStep 166189 = 62321) (by norm_num)
theorem B166225 : Blo 143792 166225 := bbase (se 2 (by rfl) ⟨62334, by rfl⟩ : syracuseStep 166225 = 124669) (by norm_num)
theorem B330101 : Blo 143792 330101 := bbase (se 5 (by rfl) ⟨15473, by rfl⟩ : syracuseStep 330101 = 30947) (by norm_num)
theorem B166261 : Blo 143792 166261 := bbase (se 5 (by rfl) ⟨7793, by rfl⟩ : syracuseStep 166261 = 15587) (by norm_num)
theorem B559493 : Blo 143792 559493 := bbase (se 4 (by rfl) ⟨52452, by rfl⟩ : syracuseStep 559493 = 104905) (by norm_num)
theorem B297373 : Blo 143792 297373 := bbase (se 3 (by rfl) ⟨55757, by rfl⟩ : syracuseStep 297373 = 111515) (by norm_num)
theorem B330173 : Blo 143792 330173 := bbase (se 3 (by rfl) ⟨61907, by rfl⟩ : syracuseStep 330173 = 123815) (by norm_num)
theorem B330245 : Blo 143792 330245 := bbase (se 4 (by rfl) ⟨30960, by rfl⟩ : syracuseStep 330245 = 61921) (by norm_num)
theorem B330317 : Blo 143792 330317 := bbase (se 3 (by rfl) ⟨61934, by rfl⟩ : syracuseStep 330317 = 123869) (by norm_num)
theorem B330389 : Blo 143792 330389 := bbase (se 6 (by rfl) ⟨7743, by rfl⟩ : syracuseStep 330389 = 15487) (by norm_num)
theorem B559781 : Blo 143792 559781 := bbase (se 4 (by rfl) ⟨52479, by rfl⟩ : syracuseStep 559781 = 104959) (by norm_num)
theorem B494261 : Blo 143792 494261 := bbase (se 5 (by rfl) ⟨23168, by rfl⟩ : syracuseStep 494261 = 46337) (by norm_num)
theorem B232141 : Blo 143792 232141 := bbase (se 3 (by rfl) ⟨43526, by rfl⟩ : syracuseStep 232141 = 87053) (by norm_num)
theorem B1247957 : Blo 143792 1247957 := bbase (se 7 (by rfl) ⟨14624, by rfl⟩ : syracuseStep 1247957 = 29249) (by norm_num)
theorem B330461 : Blo 143792 330461 := bbase (se 3 (by rfl) ⟨61961, by rfl⟩ : syracuseStep 330461 = 123923) (by norm_num)
theorem B330533 : Blo 143792 330533 := bbase (se 4 (by rfl) ⟨30987, by rfl⟩ : syracuseStep 330533 = 61975) (by norm_num)
theorem B330605 : Blo 143792 330605 := bbase (se 3 (by rfl) ⟨61988, by rfl⟩ : syracuseStep 330605 = 123977) (by norm_num)
theorem B330677 : Blo 143792 330677 := bbase (se 5 (by rfl) ⟨15500, by rfl⟩ : syracuseStep 330677 = 31001) (by norm_num)
theorem B330749 : Blo 143792 330749 := bbase (se 3 (by rfl) ⟨62015, by rfl⟩ : syracuseStep 330749 = 124031) (by norm_num)
theorem B691253 : Blo 143792 691253 := bbase (se 5 (by rfl) ⟨32402, by rfl⟩ : syracuseStep 691253 = 64805) (by norm_num)
theorem B330821 : Blo 143792 330821 := bbase (se 4 (by rfl) ⟨31014, by rfl⟩ : syracuseStep 330821 = 62029) (by norm_num)
theorem B1346645 : Blo 143792 1346645 := bbase (se 8 (by rfl) ⟨7890, by rfl⟩ : syracuseStep 1346645 = 15781) (by norm_num)
theorem B494693 : Blo 143792 494693 := bbase (se 4 (by rfl) ⟨46377, by rfl⟩ : syracuseStep 494693 = 92755) (by norm_num)
theorem B167017 : Blo 143792 167017 := bbase (se 2 (by rfl) ⟨62631, by rfl⟩ : syracuseStep 167017 = 125263) (by norm_num)
theorem B330893 : Blo 143792 330893 := bbase (se 3 (by rfl) ⟨62042, by rfl⟩ : syracuseStep 330893 = 124085) (by norm_num)
theorem B625877 : Blo 143792 625877 := bbase (se 7 (by rfl) ⟨7334, by rfl⟩ : syracuseStep 625877 = 14669) (by norm_num)
theorem B330965 : Blo 143792 330965 := bbase (se 7 (by rfl) ⟨3878, by rfl⟩ : syracuseStep 330965 = 7757) (by norm_num)
theorem B331037 : Blo 143792 331037 := bbase (se 3 (by rfl) ⟨62069, by rfl⟩ : syracuseStep 331037 = 124139) (by norm_num)
theorem B331109 : Blo 143792 331109 := bbase (se 4 (by rfl) ⟨31041, by rfl⟩ : syracuseStep 331109 = 62083) (by norm_num)
theorem B232813 : Blo 143792 232813 := bbase (se 3 (by rfl) ⟨43652, by rfl⟩ : syracuseStep 232813 = 87305) (by norm_num)
theorem B331181 : Blo 143792 331181 := bbase (se 3 (by rfl) ⟨62096, by rfl⟩ : syracuseStep 331181 = 124193) (by norm_num)
theorem B265693 : Blo 143792 265693 := bbase (se 3 (by rfl) ⟨49817, by rfl⟩ : syracuseStep 265693 = 99635) (by norm_num)
theorem B331253 : Blo 143792 331253 := bbase (se 5 (by rfl) ⟨15527, by rfl⟩ : syracuseStep 331253 = 31055) (by norm_num)
theorem B495125 : Blo 143792 495125 := bbase (se 6 (by rfl) ⟨11604, by rfl⟩ : syracuseStep 495125 = 23209) (by norm_num)
theorem B364085 : Blo 143792 364085 := bbase (se 5 (by rfl) ⟨17066, by rfl⟩ : syracuseStep 364085 = 34133) (by norm_num)
theorem B331325 : Blo 143792 331325 := bbase (se 3 (by rfl) ⟨62123, by rfl⟩ : syracuseStep 331325 = 124247) (by norm_num)
theorem B265837 : Blo 143792 265837 := bbase (se 3 (by rfl) ⟨49844, by rfl⟩ : syracuseStep 265837 = 99689) (by norm_num)
theorem B331397 : Blo 143792 331397 := bbase (se 4 (by rfl) ⟨31068, by rfl⟩ : syracuseStep 331397 = 62137) (by norm_num)
theorem B265909 : Blo 143792 265909 := bbase (se 5 (by rfl) ⟨12464, by rfl⟩ : syracuseStep 265909 = 24929) (by norm_num)
theorem B331469 : Blo 143792 331469 := bbase (se 3 (by rfl) ⟨62150, by rfl⟩ : syracuseStep 331469 = 124301) (by norm_num)
theorem B364277 : Blo 143792 364277 := bbase (se 5 (by rfl) ⟨17075, by rfl⟩ : syracuseStep 364277 = 34151) (by norm_num)
theorem B331541 : Blo 143792 331541 := bbase (se 6 (by rfl) ⟨7770, by rfl⟩ : syracuseStep 331541 = 15541) (by norm_num)
theorem B560965 : Blo 143792 560965 := bbase (se 4 (by rfl) ⟨52590, by rfl⟩ : syracuseStep 560965 = 105181) (by norm_num)
theorem B15109973 : Blo 143792 15109973 := bbase (se 9 (by rfl) ⟨44267, by rfl⟩ : syracuseStep 15109973 = 88535) (by norm_num)
theorem B331613 : Blo 143792 331613 := bbase (se 3 (by rfl) ⟨62177, by rfl⟩ : syracuseStep 331613 = 124355) (by norm_num)
theorem B331685 : Blo 143792 331685 := bbase (se 4 (by rfl) ⟨31095, by rfl⟩ : syracuseStep 331685 = 62191) (by norm_num)
theorem B495557 : Blo 143792 495557 := bbase (se 4 (by rfl) ⟨46458, by rfl⟩ : syracuseStep 495557 = 92917) (by norm_num)
theorem B331757 : Blo 143792 331757 := bbase (se 3 (by rfl) ⟨62204, by rfl⟩ : syracuseStep 331757 = 124409) (by norm_num)
theorem B331829 : Blo 143792 331829 := bbase (se 5 (by rfl) ⟨15554, by rfl⟩ : syracuseStep 331829 = 31109) (by norm_num)
theorem B364621 : Blo 143792 364621 := bbase (se 3 (by rfl) ⟨68366, by rfl⟩ : syracuseStep 364621 = 136733) (by norm_num)
theorem B331901 : Blo 143792 331901 := bbase (se 3 (by rfl) ⟨62231, by rfl⟩ : syracuseStep 331901 = 124463) (by norm_num)
theorem B364733 : Blo 143792 364733 := bbase (se 3 (by rfl) ⟨68387, by rfl⟩ : syracuseStep 364733 = 136775) (by norm_num)
theorem B626885 : Blo 143792 626885 := bbase (se 4 (by rfl) ⟨58770, by rfl⟩ : syracuseStep 626885 = 117541) (by norm_num)
theorem B331973 : Blo 143792 331973 := bbase (se 4 (by rfl) ⟨31122, by rfl⟩ : syracuseStep 331973 = 62245) (by norm_num)
theorem B299261 : Blo 143792 299261 := bbase (se 3 (by rfl) ⟨56111, by rfl⟩ : syracuseStep 299261 = 112223) (by norm_num)
theorem B332045 : Blo 143792 332045 := bbase (se 3 (by rfl) ⟨62258, by rfl⟩ : syracuseStep 332045 = 124517) (by norm_num)
theorem B233813 : Blo 143792 233813 := bbase (se 10 (by rfl) ⟨342, by rfl⟩ : syracuseStep 233813 = 685) (by norm_num)
theorem B332117 : Blo 143792 332117 := bbase (se 10 (by rfl) ⟨486, by rfl⟩ : syracuseStep 332117 = 973) (by norm_num)
theorem B495989 : Blo 143792 495989 := bbase (se 5 (by rfl) ⟨23249, by rfl⟩ : syracuseStep 495989 = 46499) (by norm_num)
theorem B364925 : Blo 143792 364925 := bbase (se 3 (by rfl) ⟨68423, by rfl⟩ : syracuseStep 364925 = 136847) (by norm_num)
theorem B332189 : Blo 143792 332189 := bbase (se 3 (by rfl) ⟨62285, by rfl⟩ : syracuseStep 332189 = 124571) (by norm_num)
theorem B332261 : Blo 143792 332261 := bbase (se 4 (by rfl) ⟨31149, by rfl⟩ : syracuseStep 332261 = 62299) (by norm_num)
theorem B332333 : Blo 143792 332333 := bbase (se 3 (by rfl) ⟨62312, by rfl⟩ : syracuseStep 332333 = 124625) (by norm_num)
theorem B168517 : Blo 143792 168517 := bbase (se 4 (by rfl) ⟨15798, by rfl⟩ : syracuseStep 168517 = 31597) (by norm_num)
theorem B332405 : Blo 143792 332405 := bbase (se 5 (by rfl) ⟨15581, by rfl⟩ : syracuseStep 332405 = 31163) (by norm_num)
theorem B332477 : Blo 143792 332477 := bbase (se 3 (by rfl) ⟨62339, by rfl⟩ : syracuseStep 332477 = 124679) (by norm_num)
theorem B365269 : Blo 143792 365269 := bbase (se 7 (by rfl) ⟨4280, by rfl⟩ : syracuseStep 365269 = 8561) (by norm_num)
theorem B266965 : Blo 143792 266965 := bbase (se 7 (by rfl) ⟨3128, by rfl⟩ : syracuseStep 266965 = 6257) (by norm_num)
theorem B496421 : Blo 143792 496421 := bbase (se 4 (by rfl) ⟨46539, by rfl⟩ : syracuseStep 496421 = 93079) (by norm_num)
theorem B365381 : Blo 143792 365381 := bbase (se 4 (by rfl) ⟨34254, by rfl⟩ : syracuseStep 365381 = 68509) (by norm_num)
theorem B463781 : Blo 143792 463781 := bbase (se 4 (by rfl) ⟨43479, by rfl⟩ : syracuseStep 463781 = 86959) (by norm_num)
theorem B332765 : Blo 143792 332765 := bbase (se 3 (by rfl) ⟨62393, by rfl⟩ : syracuseStep 332765 = 124787) (by norm_num)
theorem B365573 : Blo 143792 365573 := bbase (se 4 (by rfl) ⟨34272, by rfl⟩ : syracuseStep 365573 = 68545) (by norm_num)
theorem B496853 : Blo 143792 496853 := bbase (se 7 (by rfl) ⟨5822, by rfl⟩ : syracuseStep 496853 = 11645) (by norm_num)
theorem B365917 : Blo 143792 365917 := bbase (se 3 (by rfl) ⟨68609, by rfl⟩ : syracuseStep 365917 = 137219) (by norm_num)
theorem B333157 : Blo 143792 333157 := bbase (se 4 (by rfl) ⟨31233, by rfl⟩ : syracuseStep 333157 = 62467) (by norm_num)
theorem B169393 : Blo 143792 169393 := bbase (se 2 (by rfl) ⟨63522, by rfl⟩ : syracuseStep 169393 = 127045) (by norm_num)
theorem B366029 : Blo 143792 366029 := bbase (se 3 (by rfl) ⟨68630, by rfl⟩ : syracuseStep 366029 = 137261) (by norm_num)
theorem B988661 : Blo 143792 988661 := bbase (se 5 (by rfl) ⟨46343, by rfl⟩ : syracuseStep 988661 = 92687) (by norm_num)
theorem B529973 : Blo 143792 529973 := bbase (se 5 (by rfl) ⟨24842, by rfl⟩ : syracuseStep 529973 = 49685) (by norm_num)
theorem B497285 : Blo 143792 497285 := bbase (se 4 (by rfl) ⟨46620, by rfl⟩ : syracuseStep 497285 = 93241) (by norm_num)
theorem B366221 : Blo 143792 366221 := bbase (se 3 (by rfl) ⟨68666, by rfl⟩ : syracuseStep 366221 = 137333) (by norm_num)
theorem B890677 : Blo 143792 890677 := bbase (se 5 (by rfl) ⟨41750, by rfl⟩ : syracuseStep 890677 = 83501) (by norm_num)
theorem B235325 : Blo 143792 235325 := bbase (se 3 (by rfl) ⟨44123, by rfl⟩ : syracuseStep 235325 = 88247) (by norm_num)
theorem B628661 : Blo 143792 628661 := bbase (se 5 (by rfl) ⟨29468, by rfl⟩ : syracuseStep 628661 = 58937) (by norm_num)
theorem B366565 : Blo 143792 366565 := bbase (se 4 (by rfl) ⟨34365, by rfl⟩ : syracuseStep 366565 = 68731) (by norm_num)
theorem B497717 : Blo 143792 497717 := bbase (se 5 (by rfl) ⟨23330, by rfl⟩ : syracuseStep 497717 = 46661) (by norm_num)
theorem B366677 : Blo 143792 366677 := bbase (se 8 (by rfl) ⟨2148, by rfl⟩ : syracuseStep 366677 = 4297) (by norm_num)
theorem B5445845 : Blo 143792 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B235781 : Blo 143792 235781 := bbase (se 4 (by rfl) ⟨22104, by rfl⟩ : syracuseStep 235781 = 44209) (by norm_num)
theorem B891157 : Blo 143792 891157 := bbase (se 6 (by rfl) ⟨20886, by rfl⟩ : syracuseStep 891157 = 41773) (by norm_num)
theorem B366869 : Blo 143792 366869 := bbase (se 6 (by rfl) ⟨8598, by rfl⟩ : syracuseStep 366869 = 17197) (by norm_num)
theorem B498149 : Blo 143792 498149 := bbase (se 4 (by rfl) ⟨46701, by rfl⟩ : syracuseStep 498149 = 93403) (by norm_num)
theorem B530981 : Blo 143792 530981 := bbase (se 4 (by rfl) ⟨49779, by rfl⟩ : syracuseStep 530981 = 99559) (by norm_num)
theorem B367213 : Blo 143792 367213 := bbase (se 3 (by rfl) ⟨68852, by rfl⟩ : syracuseStep 367213 = 137705) (by norm_num)
theorem B498325 : Blo 143792 498325 := bbase (se 6 (by rfl) ⟨11679, by rfl⟩ : syracuseStep 498325 = 23359) (by norm_num)
theorem B3185365 : Blo 143792 3185365 := bbase (se 7 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 3185365 = 74657) (by norm_num)
theorem B367325 : Blo 143792 367325 := bbase (se 3 (by rfl) ⟨68873, by rfl⟩ : syracuseStep 367325 = 137747) (by norm_num)
theorem B1579925 : Blo 143792 1579925 := bbase (se 6 (by rfl) ⟨37029, by rfl⟩ : syracuseStep 1579925 = 74059) (by norm_num)
theorem B498581 : Blo 143792 498581 := bbase (se 6 (by rfl) ⟨11685, by rfl⟩ : syracuseStep 498581 = 23371) (by norm_num)
theorem B367517 : Blo 143792 367517 := bbase (se 3 (by rfl) ⟨68909, by rfl⟩ : syracuseStep 367517 = 137819) (by norm_num)
theorem B466037 : Blo 143792 466037 := bbase (se 5 (by rfl) ⟨21845, by rfl⟩ : syracuseStep 466037 = 43691) (by norm_num)
theorem B302293 : Blo 143792 302293 := bbase (se 7 (by rfl) ⟨3542, by rfl⟩ : syracuseStep 302293 = 7085) (by norm_num)
theorem B367861 : Blo 143792 367861 := bbase (se 5 (by rfl) ⟨17243, by rfl⟩ : syracuseStep 367861 = 34487) (by norm_num)
theorem B466165 : Blo 143792 466165 := bbase (se 5 (by rfl) ⟨21851, by rfl⟩ : syracuseStep 466165 = 43703) (by norm_num)
theorem B695557 : Blo 143792 695557 := bbase (se 4 (by rfl) ⟨65208, by rfl⟩ : syracuseStep 695557 = 130417) (by norm_num)
theorem B367973 : Blo 143792 367973 := bbase (se 4 (by rfl) ⟨34497, by rfl⟩ : syracuseStep 367973 = 68995) (by norm_num)
theorem B368165 : Blo 143792 368165 := bbase (se 4 (by rfl) ⟨34515, by rfl⟩ : syracuseStep 368165 = 69031) (by norm_num)
theorem B728837 : Blo 143792 728837 := bbase (se 4 (by rfl) ⟨68328, by rfl⟩ : syracuseStep 728837 = 136657) (by norm_num)
theorem B368509 : Blo 143792 368509 := bbase (se 3 (by rfl) ⟨69095, by rfl⟩ : syracuseStep 368509 = 138191) (by norm_num)
theorem B794549 : Blo 143792 794549 := bbase (se 5 (by rfl) ⟨37244, by rfl⟩ : syracuseStep 794549 = 74489) (by norm_num)
theorem B204781 : Blo 143792 204781 := bbase (se 3 (by rfl) ⟨38396, by rfl⟩ : syracuseStep 204781 = 76793) (by norm_num)
theorem B368621 : Blo 143792 368621 := bbase (se 3 (by rfl) ⟨69116, by rfl⟩ : syracuseStep 368621 = 138233) (by norm_num)
theorem B335933 : Blo 143792 335933 := bbase (se 3 (by rfl) ⟨62987, by rfl⟩ : syracuseStep 335933 = 125975) (by norm_num)
theorem B368813 : Blo 143792 368813 := bbase (se 3 (by rfl) ⟨69152, by rfl⟩ : syracuseStep 368813 = 138305) (by norm_num)
theorem B237757 : Blo 143792 237757 := bbase (se 3 (by rfl) ⟨44579, by rfl⟩ : syracuseStep 237757 = 89159) (by norm_num)
theorem B369157 : Blo 143792 369157 := bbase (se 4 (by rfl) ⟨34608, by rfl⟩ : syracuseStep 369157 = 69217) (by norm_num)
theorem B205373 : Blo 143792 205373 := bbase (se 3 (by rfl) ⟨38507, by rfl⟩ : syracuseStep 205373 = 77015) (by norm_num)
theorem B1679957 : Blo 143792 1679957 := bbase (se 8 (by rfl) ⟨9843, by rfl⟩ : syracuseStep 1679957 = 19687) (by norm_num)
theorem B369269 : Blo 143792 369269 := bbase (se 5 (by rfl) ⟨17309, by rfl⟩ : syracuseStep 369269 = 34619) (by norm_num)
theorem B205453 : Blo 143792 205453 := bbase (se 3 (by rfl) ⟨38522, by rfl⟩ : syracuseStep 205453 = 77045) (by norm_num)
theorem B828053 : Blo 143792 828053 := bbase (se 6 (by rfl) ⟨19407, by rfl⟩ : syracuseStep 828053 = 38815) (by norm_num)
theorem B205573 : Blo 143792 205573 := bbase (se 4 (by rfl) ⟨19272, by rfl⟩ : syracuseStep 205573 = 38545) (by norm_num)
theorem B369461 : Blo 143792 369461 := bbase (se 5 (by rfl) ⟨17318, by rfl⟩ : syracuseStep 369461 = 34637) (by norm_num)
theorem B205669 : Blo 143792 205669 := bbase (se 4 (by rfl) ⟨19281, by rfl⟩ : syracuseStep 205669 = 38563) (by norm_num)
theorem B1254325 : Blo 143792 1254325 := bbase (se 5 (by rfl) ⟨58796, by rfl⟩ : syracuseStep 1254325 = 117593) (by norm_num)
theorem B730133 : Blo 143792 730133 := bbase (se 6 (by rfl) ⟨17112, by rfl⟩ : syracuseStep 730133 = 34225) (by norm_num)
theorem B926741 : Blo 143792 926741 := bbase (se 6 (by rfl) ⟨21720, by rfl⟩ : syracuseStep 926741 = 43441) (by norm_num)
theorem B369805 : Blo 143792 369805 := bbase (se 3 (by rfl) ⟨69338, by rfl⟩ : syracuseStep 369805 = 138677) (by norm_num)
theorem B369917 : Blo 143792 369917 := bbase (se 3 (by rfl) ⟨69359, by rfl⟩ : syracuseStep 369917 = 138719) (by norm_num)
theorem B206165 : Blo 143792 206165 := bbase (se 12 (by rfl) ⟨75, by rfl⟩ : syracuseStep 206165 = 151) (by norm_num)
theorem B370109 : Blo 143792 370109 := bbase (se 3 (by rfl) ⟨69395, by rfl⟩ : syracuseStep 370109 = 138791) (by norm_num)
theorem B370453 : Blo 143792 370453 := bbase (se 6 (by rfl) ⟨8682, by rfl⟩ : syracuseStep 370453 = 17365) (by norm_num)
theorem B829237 : Blo 143792 829237 := bbase (se 5 (by rfl) ⟨38870, by rfl⟩ : syracuseStep 829237 = 77741) (by norm_num)
theorem B206717 : Blo 143792 206717 := bbase (se 3 (by rfl) ⟨38759, by rfl⟩ : syracuseStep 206717 = 77519) (by norm_num)
theorem B370565 : Blo 143792 370565 := bbase (se 4 (by rfl) ⟨34740, by rfl⟩ : syracuseStep 370565 = 69481) (by norm_num)
theorem B567269 : Blo 143792 567269 := bbase (se 4 (by rfl) ⟨53181, by rfl⟩ : syracuseStep 567269 = 106363) (by norm_num)
theorem B469061 : Blo 143792 469061 := bbase (se 4 (by rfl) ⟨43974, by rfl⟩ : syracuseStep 469061 = 87949) (by norm_num)
theorem B370757 : Blo 143792 370757 := bbase (se 4 (by rfl) ⟨34758, by rfl⟩ : syracuseStep 370757 = 69517) (by norm_num)
theorem B174197 : Blo 143792 174197 := bbase (se 5 (by rfl) ⟨8165, by rfl⟩ : syracuseStep 174197 = 16331) (by norm_num)
theorem B895157 : Blo 143792 895157 := bbase (se 5 (by rfl) ⟨41960, by rfl⟩ : syracuseStep 895157 = 83921) (by norm_num)
theorem B731429 : Blo 143792 731429 := bbase (se 4 (by rfl) ⟨68571, by rfl⟩ : syracuseStep 731429 = 137143) (by norm_num)
theorem B9382229 : Blo 143792 9382229 := bbase (se 10 (by rfl) ⟨13743, by rfl⟩ : syracuseStep 9382229 = 27487) (by norm_num)
theorem B1419605 : Blo 143792 1419605 := bbase (se 10 (by rfl) ⟨2079, by rfl⟩ : syracuseStep 1419605 = 4159) (by norm_num)
theorem B371101 : Blo 143792 371101 := bbase (se 3 (by rfl) ⟨69581, by rfl⟩ : syracuseStep 371101 = 139163) (by norm_num)
theorem B174533 : Blo 143792 174533 := bbase (se 4 (by rfl) ⟨16362, by rfl⟩ : syracuseStep 174533 = 32725) (by norm_num)
theorem B371213 : Blo 143792 371213 := bbase (se 3 (by rfl) ⟨69602, by rfl⟩ : syracuseStep 371213 = 139205) (by norm_num)
theorem B174649 : Blo 143792 174649 := bbase (se 2 (by rfl) ⟨65493, by rfl⟩ : syracuseStep 174649 = 130987) (by norm_num)
theorem B207469 : Blo 143792 207469 := bbase (se 3 (by rfl) ⟨38900, by rfl⟩ : syracuseStep 207469 = 77801) (by norm_num)
theorem B174721 : Blo 143792 174721 := bbase (se 2 (by rfl) ⟨65520, by rfl⟩ : syracuseStep 174721 = 131041) (by norm_num)
theorem B174745 : Blo 143792 174745 := bbase (se 2 (by rfl) ⟨65529, by rfl⟩ : syracuseStep 174745 = 131059) (by norm_num)
theorem B371405 : Blo 143792 371405 := bbase (se 3 (by rfl) ⟨69638, by rfl⟩ : syracuseStep 371405 = 139277) (by norm_num)
theorem B273125 : Blo 143792 273125 := bbase (se 4 (by rfl) ⟨25605, by rfl⟩ : syracuseStep 273125 = 51211) (by norm_num)
theorem B174889 : Blo 143792 174889 := bbase (se 2 (by rfl) ⟨65583, by rfl⟩ : syracuseStep 174889 = 131167) (by norm_num)
theorem B273269 : Blo 143792 273269 := bbase (se 5 (by rfl) ⟨12809, by rfl⟩ : syracuseStep 273269 = 25619) (by norm_num)
theorem B371749 : Blo 143792 371749 := bbase (se 4 (by rfl) ⟨34851, by rfl⟩ : syracuseStep 371749 = 69703) (by norm_num)
theorem B371773 : Blo 143792 371773 := bbase (se 3 (by rfl) ⟨69707, by rfl⟩ : syracuseStep 371773 = 139415) (by norm_num)
theorem B273557 : Blo 143792 273557 := bbase (se 6 (by rfl) ⟨6411, by rfl⟩ : syracuseStep 273557 = 12823) (by norm_num)
theorem B371861 : Blo 143792 371861 := bbase (se 6 (by rfl) ⟨8715, by rfl⟩ : syracuseStep 371861 = 17431) (by norm_num)
theorem B208165 : Blo 143792 208165 := bbase (se 4 (by rfl) ⟨19515, by rfl⟩ : syracuseStep 208165 = 39031) (by norm_num)
theorem B666917 : Blo 143792 666917 := bbase (se 4 (by rfl) ⟨62523, by rfl⟩ : syracuseStep 666917 = 125047) (by norm_num)
theorem B273709 : Blo 143792 273709 := bbase (se 3 (by rfl) ⟨51320, by rfl⟩ : syracuseStep 273709 = 102641) (by norm_num)
theorem B372053 : Blo 143792 372053 := bbase (se 11 (by rfl) ⟨272, by rfl⟩ : syracuseStep 372053 = 545) (by norm_num)
theorem B699749 : Blo 143792 699749 := bbase (se 4 (by rfl) ⟨65601, by rfl⟩ : syracuseStep 699749 = 131203) (by norm_num)
theorem B175493 : Blo 143792 175493 := bbase (se 4 (by rfl) ⟨16452, by rfl⟩ : syracuseStep 175493 = 32905) (by norm_num)
theorem B208261 : Blo 143792 208261 := bbase (se 4 (by rfl) ⟨19524, by rfl⟩ : syracuseStep 208261 = 39049) (by norm_num)
theorem B437653 : Blo 143792 437653 := bbase (se 6 (by rfl) ⟨10257, by rfl⟩ : syracuseStep 437653 = 20515) (by norm_num)
theorem B1093013 : Blo 143792 1093013 := bbase (se 6 (by rfl) ⟨25617, by rfl⟩ : syracuseStep 1093013 = 51235) (by norm_num)
theorem B1387925 : Blo 143792 1387925 := bbase (se 6 (by rfl) ⟨32529, by rfl⟩ : syracuseStep 1387925 = 65059) (by norm_num)
theorem B732725 : Blo 143792 732725 := bbase (se 5 (by rfl) ⟨34346, by rfl⟩ : syracuseStep 732725 = 68693) (by norm_num)
theorem B274013 : Blo 143792 274013 := bbase (se 3 (by rfl) ⟨51377, by rfl⟩ : syracuseStep 274013 = 102755) (by norm_num)
theorem B372397 : Blo 143792 372397 := bbase (se 3 (by rfl) ⟨69824, by rfl⟩ : syracuseStep 372397 = 139649) (by norm_num)
theorem B208597 : Blo 143792 208597 := bbase (se 7 (by rfl) ⟨2444, by rfl⟩ : syracuseStep 208597 = 4889) (by norm_num)
theorem B831221 : Blo 143792 831221 := bbase (se 5 (by rfl) ⟨38963, by rfl⟩ : syracuseStep 831221 = 77927) (by norm_num)
theorem B372509 : Blo 143792 372509 := bbase (se 3 (by rfl) ⟨69845, by rfl⟩ : syracuseStep 372509 = 139691) (by norm_num)
theorem B208813 : Blo 143792 208813 := bbase (se 3 (by rfl) ⟨39152, by rfl⟩ : syracuseStep 208813 = 78305) (by norm_num)
theorem B929717 : Blo 143792 929717 := bbase (se 5 (by rfl) ⟨43580, by rfl⟩ : syracuseStep 929717 = 87161) (by norm_num)
theorem B372701 : Blo 143792 372701 := bbase (se 3 (by rfl) ⟨69881, by rfl⟩ : syracuseStep 372701 = 139763) (by norm_num)
theorem B176105 : Blo 143792 176105 := bbase (se 2 (by rfl) ⟨66039, by rfl⟩ : syracuseStep 176105 = 132079) (by norm_num)
theorem B471253 : Blo 143792 471253 := bbase (se 7 (by rfl) ⟨5522, by rfl⟩ : syracuseStep 471253 = 11045) (by norm_num)
theorem B176369 : Blo 143792 176369 := bbase (se 2 (by rfl) ⟨66138, by rfl⟩ : syracuseStep 176369 = 132277) (by norm_num)
theorem B667925 : Blo 143792 667925 := bbase (se 6 (by rfl) ⟨15654, by rfl⟩ : syracuseStep 667925 = 31309) (by norm_num)
theorem B176413 : Blo 143792 176413 := bbase (se 3 (by rfl) ⟨33077, by rfl⟩ : syracuseStep 176413 = 66155) (by norm_num)
theorem B209189 : Blo 143792 209189 := bbase (se 4 (by rfl) ⟨19611, by rfl⟩ : syracuseStep 209189 = 39223) (by norm_num)
theorem B373045 : Blo 143792 373045 := bbase (se 5 (by rfl) ⟨17486, by rfl⟩ : syracuseStep 373045 = 34973) (by norm_num)
theorem B274765 : Blo 143792 274765 := bbase (se 3 (by rfl) ⟨51518, by rfl⟩ : syracuseStep 274765 = 103037) (by norm_num)
theorem B176513 : Blo 143792 176513 := bbase (se 2 (by rfl) ⟨66192, by rfl⟩ : syracuseStep 176513 = 132385) (by norm_num)
theorem B373157 : Blo 143792 373157 := bbase (se 4 (by rfl) ⟨34983, by rfl⟩ : syracuseStep 373157 = 69967) (by norm_num)
theorem B274909 : Blo 143792 274909 := bbase (se 3 (by rfl) ⟨51545, by rfl⟩ : syracuseStep 274909 = 103091) (by norm_num)
theorem B307813 : Blo 143792 307813 := bbase (se 4 (by rfl) ⟨28857, by rfl⟩ : syracuseStep 307813 = 57715) (by norm_num)
theorem B373349 : Blo 143792 373349 := bbase (se 4 (by rfl) ⟨35001, by rfl⟩ : syracuseStep 373349 = 70003) (by norm_num)
theorem B275069 : Blo 143792 275069 := bbase (se 3 (by rfl) ⟨51575, by rfl⟩ : syracuseStep 275069 = 103151) (by norm_num)
theorem B209533 : Blo 143792 209533 := bbase (se 3 (by rfl) ⟨39287, by rfl⟩ : syracuseStep 209533 = 78575) (by norm_num)
theorem B2765461 : Blo 143792 2765461 := bbase (se 6 (by rfl) ⟨64815, by rfl⟩ : syracuseStep 2765461 = 129631) (by norm_num)
theorem B144049 : Blo 143792 144049 := bbase (se 2 (by rfl) ⟨54018, by rfl⟩ : syracuseStep 144049 = 108037) (by norm_num)
theorem B307957 : Blo 143792 307957 := bbase (se 5 (by rfl) ⟨14435, by rfl⟩ : syracuseStep 307957 = 28871) (by norm_num)
theorem B275213 : Blo 143792 275213 := bbase (se 3 (by rfl) ⟨51602, by rfl⟩ : syracuseStep 275213 = 103205) (by norm_num)
theorem B176917 : Blo 143792 176917 := bbase (se 6 (by rfl) ⟨4146, by rfl⟩ : syracuseStep 176917 = 8293) (by norm_num)
theorem B734021 : Blo 143792 734021 := bbase (se 4 (by rfl) ⟨68814, by rfl⟩ : syracuseStep 734021 = 137629) (by norm_num)
theorem B373693 : Blo 143792 373693 := bbase (se 3 (by rfl) ⟨70067, by rfl⟩ : syracuseStep 373693 = 140135) (by norm_num)
theorem B242669 : Blo 143792 242669 := bbase (se 3 (by rfl) ⟨45500, by rfl⟩ : syracuseStep 242669 = 91001) (by norm_num)
theorem B472085 : Blo 143792 472085 := bbase (se 6 (by rfl) ⟨11064, by rfl⟩ : syracuseStep 472085 = 22129) (by norm_num)
theorem B766997 : Blo 143792 766997 := bbase (se 6 (by rfl) ⟨17976, by rfl⟩ : syracuseStep 766997 = 35953) (by norm_num)
theorem B275501 : Blo 143792 275501 := bbase (se 3 (by rfl) ⟨51656, by rfl⟩ : syracuseStep 275501 = 103313) (by norm_num)
theorem B373805 : Blo 143792 373805 := bbase (se 3 (by rfl) ⟨70088, by rfl⟩ : syracuseStep 373805 = 140177) (by norm_num)
theorem B242797 : Blo 143792 242797 := bbase (se 3 (by rfl) ⟨45524, by rfl⟩ : syracuseStep 242797 = 91049) (by norm_num)
theorem B308333 : Blo 143792 308333 := bbase (se 3 (by rfl) ⟨57812, by rfl⟩ : syracuseStep 308333 = 115625) (by norm_num)
theorem B177265 : Blo 143792 177265 := bbase (se 2 (by rfl) ⟨66474, by rfl⟩ : syracuseStep 177265 = 132949) (by norm_num)
theorem B373909 : Blo 143792 373909 := bbase (se 6 (by rfl) ⟨8763, by rfl⟩ : syracuseStep 373909 = 17527) (by norm_num)
theorem B177301 : Blo 143792 177301 := bbase (se 6 (by rfl) ⟨4155, by rfl⟩ : syracuseStep 177301 = 8311) (by norm_num)
theorem B242885 : Blo 143792 242885 := bbase (se 4 (by rfl) ⟨22770, by rfl⟩ : syracuseStep 242885 = 45541) (by norm_num)
theorem B275653 : Blo 143792 275653 := bbase (se 4 (by rfl) ⟨25842, by rfl⟩ : syracuseStep 275653 = 51685) (by norm_num)
theorem B373997 : Blo 143792 373997 := bbase (se 3 (by rfl) ⟨70124, by rfl⟩ : syracuseStep 373997 = 140249) (by norm_num)
theorem B243013 : Blo 143792 243013 := bbase (se 4 (by rfl) ⟨22782, by rfl⟩ : syracuseStep 243013 = 45565) (by norm_num)
theorem B243101 : Blo 143792 243101 := bbase (se 3 (by rfl) ⟨45581, by rfl⟩ : syracuseStep 243101 = 91163) (by norm_num)
theorem B308701 : Blo 143792 308701 := bbase (se 3 (by rfl) ⟨57881, by rfl⟩ : syracuseStep 308701 = 115763) (by norm_num)
theorem B275957 : Blo 143792 275957 := bbase (se 5 (by rfl) ⟨12935, by rfl⟩ : syracuseStep 275957 = 25871) (by norm_num)
theorem B243229 : Blo 143792 243229 := bbase (se 3 (by rfl) ⟨45605, by rfl⟩ : syracuseStep 243229 = 91211) (by norm_num)
theorem B243317 : Blo 143792 243317 := bbase (se 5 (by rfl) ⟨11405, by rfl⟩ : syracuseStep 243317 = 22811) (by norm_num)
theorem B3192533 : Blo 143792 3192533 := bbase (se 7 (by rfl) ⟨37412, by rfl⟩ : syracuseStep 3192533 = 74825) (by norm_num)
theorem B669397 : Blo 143792 669397 := bbase (se 7 (by rfl) ⟨7844, by rfl⟩ : syracuseStep 669397 = 15689) (by norm_num)
theorem B243445 : Blo 143792 243445 := bbase (se 5 (by rfl) ⟨11411, by rfl⟩ : syracuseStep 243445 = 22823) (by norm_num)
theorem B243533 : Blo 143792 243533 := bbase (se 3 (by rfl) ⟨45662, by rfl⟩ : syracuseStep 243533 = 91325) (by norm_num)
theorem B833429 : Blo 143792 833429 := bbase (se 6 (by rfl) ⟨19533, by rfl⟩ : syracuseStep 833429 = 39067) (by norm_num)
theorem B243661 : Blo 143792 243661 := bbase (se 3 (by rfl) ⟨45686, by rfl⟩ : syracuseStep 243661 = 91373) (by norm_num)
theorem B145361 : Blo 143792 145361 := bbase (se 2 (by rfl) ⟨54510, by rfl⟩ : syracuseStep 145361 = 109021) (by norm_num)
theorem B702437 : Blo 143792 702437 := bbase (se 4 (by rfl) ⟨65853, by rfl⟩ : syracuseStep 702437 = 131707) (by norm_num)
theorem B243749 : Blo 143792 243749 := bbase (se 4 (by rfl) ⟨22851, by rfl⟩ : syracuseStep 243749 = 45703) (by norm_num)
theorem B735317 : Blo 143792 735317 := bbase (se 8 (by rfl) ⟨4308, by rfl⟩ : syracuseStep 735317 = 8617) (by norm_num)
theorem B243877 : Blo 143792 243877 := bbase (se 4 (by rfl) ⟨22863, by rfl⟩ : syracuseStep 243877 = 45727) (by norm_num)
theorem B276709 : Blo 143792 276709 := bbase (se 4 (by rfl) ⟨25941, by rfl⟩ : syracuseStep 276709 = 51883) (by norm_num)
theorem B243965 : Blo 143792 243965 := bbase (se 3 (by rfl) ⟨45743, by rfl⟩ : syracuseStep 243965 = 91487) (by norm_num)
theorem B899381 : Blo 143792 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B276853 : Blo 143792 276853 := bbase (se 5 (by rfl) ⟨12977, by rfl⟩ : syracuseStep 276853 = 25955) (by norm_num)
theorem B244093 : Blo 143792 244093 := bbase (se 3 (by rfl) ⟨45767, by rfl⟩ : syracuseStep 244093 = 91535) (by norm_num)
theorem B244181 : Blo 143792 244181 := bbase (se 7 (by rfl) ⟨2861, by rfl⟩ : syracuseStep 244181 = 5723) (by norm_num)
theorem B277013 : Blo 143792 277013 := bbase (se 6 (by rfl) ⟨6492, by rfl⟩ : syracuseStep 277013 = 12985) (by norm_num)
theorem B244309 : Blo 143792 244309 := bbase (se 8 (by rfl) ⟨1431, by rfl⟩ : syracuseStep 244309 = 2863) (by norm_num)
theorem B277157 : Blo 143792 277157 := bbase (se 4 (by rfl) ⟨25983, by rfl⟩ : syracuseStep 277157 = 51967) (by norm_num)
theorem B244397 : Blo 143792 244397 := bbase (se 3 (by rfl) ⟨45824, by rfl⟩ : syracuseStep 244397 = 91649) (by norm_num)
theorem B277229 : Blo 143792 277229 := bbase (se 3 (by rfl) ⟨51980, by rfl⟩ : syracuseStep 277229 = 103961) (by norm_num)
theorem B244525 : Blo 143792 244525 := bbase (se 3 (by rfl) ⟨45848, by rfl⟩ : syracuseStep 244525 = 91697) (by norm_num)
theorem B244613 : Blo 143792 244613 := bbase (se 4 (by rfl) ⟨22932, by rfl⟩ : syracuseStep 244613 = 45865) (by norm_num)
theorem B310205 : Blo 143792 310205 := bbase (se 3 (by rfl) ⟨58163, by rfl⟩ : syracuseStep 310205 = 116327) (by norm_num)
theorem B277445 : Blo 143792 277445 := bbase (se 4 (by rfl) ⟨26010, by rfl⟩ : syracuseStep 277445 = 52021) (by norm_num)
theorem B375797 : Blo 143792 375797 := bbase (se 5 (by rfl) ⟨17615, by rfl⟩ : syracuseStep 375797 = 35231) (by norm_num)
theorem B244741 : Blo 143792 244741 := bbase (se 4 (by rfl) ⟨22944, by rfl⟩ : syracuseStep 244741 = 45889) (by norm_num)
theorem B310349 : Blo 143792 310349 := bbase (se 3 (by rfl) ⟨58190, by rfl⟩ : syracuseStep 310349 = 116381) (by norm_num)
theorem B244829 : Blo 143792 244829 := bbase (se 3 (by rfl) ⟨45905, by rfl⟩ : syracuseStep 244829 = 91811) (by norm_num)
theorem B277597 : Blo 143792 277597 := bbase (se 3 (by rfl) ⟨52049, by rfl⟩ : syracuseStep 277597 = 104099) (by norm_num)
theorem B244957 : Blo 143792 244957 := bbase (se 3 (by rfl) ⟨45929, by rfl⟩ : syracuseStep 244957 = 91859) (by norm_num)
theorem B245045 : Blo 143792 245045 := bbase (se 5 (by rfl) ⟨11486, by rfl⟩ : syracuseStep 245045 = 22973) (by norm_num)
theorem B736613 : Blo 143792 736613 := bbase (se 4 (by rfl) ⟨69057, by rfl⟩ : syracuseStep 736613 = 138115) (by norm_num)
theorem B277901 : Blo 143792 277901 := bbase (se 3 (by rfl) ⟨52106, by rfl⟩ : syracuseStep 277901 = 104213) (by norm_num)
theorem B179605 : Blo 143792 179605 := bbase (se 6 (by rfl) ⟨4209, by rfl⟩ : syracuseStep 179605 = 8419) (by norm_num)
theorem B146857 : Blo 143792 146857 := bbase (se 2 (by rfl) ⟨55071, by rfl⟩ : syracuseStep 146857 = 110143) (by norm_num)
theorem B245173 : Blo 143792 245173 := bbase (se 5 (by rfl) ⟨11492, by rfl⟩ : syracuseStep 245173 = 22985) (by norm_num)
theorem B310709 : Blo 143792 310709 := bbase (se 5 (by rfl) ⟨14564, by rfl⟩ : syracuseStep 310709 = 29129) (by norm_num)
theorem B245261 : Blo 143792 245261 := bbase (se 3 (by rfl) ⟨45986, by rfl⟩ : syracuseStep 245261 = 91973) (by norm_num)
theorem B1064501 : Blo 143792 1064501 := bbase (se 5 (by rfl) ⟨49898, by rfl⟩ : syracuseStep 1064501 = 99797) (by norm_num)
theorem B245389 : Blo 143792 245389 := bbase (se 3 (by rfl) ⟨46010, by rfl⟩ : syracuseStep 245389 = 92021) (by norm_num)
theorem B245477 : Blo 143792 245477 := bbase (se 4 (by rfl) ⟨23013, by rfl⟩ : syracuseStep 245477 = 46027) (by norm_num)
theorem B245605 : Blo 143792 245605 := bbase (se 4 (by rfl) ⟨23025, by rfl⟩ : syracuseStep 245605 = 46051) (by norm_num)
theorem B245693 : Blo 143792 245693 := bbase (se 3 (by rfl) ⟨46067, by rfl⟩ : syracuseStep 245693 = 92135) (by norm_num)
theorem B147425 : Blo 143792 147425 := bbase (se 2 (by rfl) ⟨55284, by rfl⟩ : syracuseStep 147425 = 110569) (by norm_num)
theorem B245821 : Blo 143792 245821 := bbase (se 3 (by rfl) ⟨46091, by rfl⟩ : syracuseStep 245821 = 92183) (by norm_num)
theorem B278653 : Blo 143792 278653 := bbase (se 3 (by rfl) ⟨52247, by rfl⟩ : syracuseStep 278653 = 104495) (by norm_num)
theorem B245909 : Blo 143792 245909 := bbase (se 6 (by rfl) ⟨5763, by rfl⟩ : syracuseStep 245909 = 11527) (by norm_num)
theorem B213229 : Blo 143792 213229 := bbase (se 3 (by rfl) ⟨39980, by rfl⟩ : syracuseStep 213229 = 79961) (by norm_num)
theorem B147725 : Blo 143792 147725 := bbase (se 3 (by rfl) ⟨27698, by rfl⟩ : syracuseStep 147725 = 55397) (by norm_num)
theorem B278797 : Blo 143792 278797 := bbase (se 3 (by rfl) ⟨52274, by rfl⟩ : syracuseStep 278797 = 104549) (by norm_num)
theorem B246037 : Blo 143792 246037 := bbase (se 6 (by rfl) ⟨5766, by rfl⟩ : syracuseStep 246037 = 11533) (by norm_num)
theorem B311597 : Blo 143792 311597 := bbase (se 3 (by rfl) ⟨58424, by rfl⟩ : syracuseStep 311597 = 116849) (by norm_num)
theorem B246125 : Blo 143792 246125 := bbase (se 3 (by rfl) ⟨46148, by rfl⟩ : syracuseStep 246125 = 92297) (by norm_num)
theorem B278957 : Blo 143792 278957 := bbase (se 3 (by rfl) ⟨52304, by rfl⟩ : syracuseStep 278957 = 104609) (by norm_num)
theorem B246253 : Blo 143792 246253 := bbase (se 3 (by rfl) ⟨46172, by rfl⟩ : syracuseStep 246253 = 92345) (by norm_num)
theorem B311845 : Blo 143792 311845 := bbase (se 4 (by rfl) ⟨29235, by rfl⟩ : syracuseStep 311845 = 58471) (by norm_num)
theorem B148025 : Blo 143792 148025 := bbase (se 2 (by rfl) ⟨55509, by rfl⟩ : syracuseStep 148025 = 111019) (by norm_num)
theorem B279101 : Blo 143792 279101 := bbase (se 3 (by rfl) ⟨52331, by rfl⟩ : syracuseStep 279101 = 104663) (by norm_num)
theorem B246341 : Blo 143792 246341 := bbase (se 4 (by rfl) ⟨23094, by rfl⟩ : syracuseStep 246341 = 46189) (by norm_num)
theorem B246365 : Blo 143792 246365 := bbase (se 3 (by rfl) ⟨46193, by rfl⟩ : syracuseStep 246365 = 92387) (by norm_num)
theorem B737909 : Blo 143792 737909 := bbase (se 5 (by rfl) ⟨34589, by rfl⟩ : syracuseStep 737909 = 69179) (by norm_num)
theorem B246469 : Blo 143792 246469 := bbase (se 4 (by rfl) ⟨23106, by rfl⟩ : syracuseStep 246469 = 46213) (by norm_num)
theorem B246557 : Blo 143792 246557 := bbase (se 3 (by rfl) ⟨46229, by rfl⟩ : syracuseStep 246557 = 92459) (by norm_num)
theorem B279389 : Blo 143792 279389 := bbase (se 3 (by rfl) ⟨52385, by rfl⟩ : syracuseStep 279389 = 104771) (by norm_num)
theorem B246685 : Blo 143792 246685 := bbase (se 3 (by rfl) ⟨46253, by rfl⟩ : syracuseStep 246685 = 92507) (by norm_num)
theorem B246773 : Blo 143792 246773 := bbase (se 5 (by rfl) ⟨11567, by rfl⟩ : syracuseStep 246773 = 23135) (by norm_num)
theorem B279541 : Blo 143792 279541 := bbase (se 5 (by rfl) ⟨13103, by rfl⟩ : syracuseStep 279541 = 26207) (by norm_num)
theorem B312349 : Blo 143792 312349 := bbase (se 3 (by rfl) ⟨58565, by rfl⟩ : syracuseStep 312349 = 117131) (by norm_num)
theorem B1197109 : Blo 143792 1197109 := bbase (se 5 (by rfl) ⟨56114, by rfl⟩ : syracuseStep 1197109 = 112229) (by norm_num)
theorem B246901 : Blo 143792 246901 := bbase (se 5 (by rfl) ⟨11573, by rfl⟩ : syracuseStep 246901 = 23147) (by norm_num)
theorem B148601 : Blo 143792 148601 := bbase (se 2 (by rfl) ⟨55725, by rfl⟩ : syracuseStep 148601 = 111451) (by norm_num)
theorem B246989 : Blo 143792 246989 := bbase (se 3 (by rfl) ⟨46310, by rfl⟩ : syracuseStep 246989 = 92621) (by norm_num)
theorem B279845 : Blo 143792 279845 := bbase (se 4 (by rfl) ⟨26235, by rfl⟩ : syracuseStep 279845 = 52471) (by norm_num)
theorem B247117 : Blo 143792 247117 := bbase (se 3 (by rfl) ⟨46334, by rfl⟩ : syracuseStep 247117 = 92669) (by norm_num)
theorem B247205 : Blo 143792 247205 := bbase (se 4 (by rfl) ⟨23175, by rfl⟩ : syracuseStep 247205 = 46351) (by norm_num)
theorem B378341 : Blo 143792 378341 := bbase (se 4 (by rfl) ⟨35469, by rfl⟩ : syracuseStep 378341 = 70939) (by norm_num)
theorem B247333 : Blo 143792 247333 := bbase (se 4 (by rfl) ⟨23187, by rfl⟩ : syracuseStep 247333 = 46375) (by norm_num)
theorem B247421 : Blo 143792 247421 := bbase (se 3 (by rfl) ⟨46391, by rfl⟩ : syracuseStep 247421 = 92783) (by norm_num)
theorem B247549 : Blo 143792 247549 := bbase (se 3 (by rfl) ⟨46415, by rfl⟩ : syracuseStep 247549 = 92831) (by norm_num)
theorem B182017 : Blo 143792 182017 := bbase (se 2 (by rfl) ⟨68256, by rfl⟩ : syracuseStep 182017 = 136513) (by norm_num)
theorem B247637 : Blo 143792 247637 := bbase (se 9 (by rfl) ⟨725, by rfl⟩ : syracuseStep 247637 = 1451) (by norm_num)
theorem B739205 : Blo 143792 739205 := bbase (se 4 (by rfl) ⟨69300, by rfl⟩ : syracuseStep 739205 = 138601) (by norm_num)
theorem B313237 : Blo 143792 313237 := bbase (se 6 (by rfl) ⟨7341, by rfl⟩ : syracuseStep 313237 = 14683) (by norm_num)
theorem B182189 : Blo 143792 182189 := bbase (se 3 (by rfl) ⟨34160, by rfl⟩ : syracuseStep 182189 = 68321) (by norm_num)
theorem B247765 : Blo 143792 247765 := bbase (se 7 (by rfl) ⟨2903, by rfl⟩ : syracuseStep 247765 = 5807) (by norm_num)
theorem B182245 : Blo 143792 182245 := bbase (se 4 (by rfl) ⟨17085, by rfl⟩ : syracuseStep 182245 = 34171) (by norm_num)
theorem B247853 : Blo 143792 247853 := bbase (se 3 (by rfl) ⟨46472, by rfl⟩ : syracuseStep 247853 = 92945) (by norm_num)
theorem B182341 : Blo 143792 182341 := bbase (se 4 (by rfl) ⟨17094, by rfl⟩ : syracuseStep 182341 = 34189) (by norm_num)
theorem B411749 : Blo 143792 411749 := bbase (se 4 (by rfl) ⟨38601, by rfl⟩ : syracuseStep 411749 = 77203) (by norm_num)
theorem B247981 : Blo 143792 247981 := bbase (se 3 (by rfl) ⟨46496, by rfl⟩ : syracuseStep 247981 = 92993) (by norm_num)
theorem B182513 : Blo 143792 182513 := bbase (se 2 (by rfl) ⟨68442, by rfl⟩ : syracuseStep 182513 = 136885) (by norm_num)
theorem B248069 : Blo 143792 248069 := bbase (se 4 (by rfl) ⟨23256, by rfl⟩ : syracuseStep 248069 = 46513) (by norm_num)
theorem B182569 : Blo 143792 182569 := bbase (se 2 (by rfl) ⟨68463, by rfl⟩ : syracuseStep 182569 = 136927) (by norm_num)
theorem B149801 : Blo 143792 149801 := bbase (se 2 (by rfl) ⟨56175, by rfl⟩ : syracuseStep 149801 = 112351) (by norm_num)
theorem B313733 : Blo 143792 313733 := bbase (se 4 (by rfl) ⟨29412, by rfl⟩ : syracuseStep 313733 = 58825) (by norm_num)
theorem B248197 : Blo 143792 248197 := bbase (se 4 (by rfl) ⟨23268, by rfl⟩ : syracuseStep 248197 = 46537) (by norm_num)
theorem B182665 : Blo 143792 182665 := bbase (se 2 (by rfl) ⟨68499, by rfl⟩ : syracuseStep 182665 = 136999) (by norm_num)
theorem B149929 : Blo 143792 149929 := bbase (se 2 (by rfl) ⟨56223, by rfl⟩ : syracuseStep 149929 = 112447) (by norm_num)
theorem B248285 : Blo 143792 248285 := bbase (se 3 (by rfl) ⟨46553, by rfl⟩ : syracuseStep 248285 = 93107) (by norm_num)
theorem B444901 : Blo 143792 444901 := bbase (se 4 (by rfl) ⟨41709, by rfl⟩ : syracuseStep 444901 = 83419) (by norm_num)
theorem B182837 : Blo 143792 182837 := bbase (se 5 (by rfl) ⟨8570, by rfl⟩ : syracuseStep 182837 = 17141) (by norm_num)
theorem B248413 : Blo 143792 248413 := bbase (se 3 (by rfl) ⟨46577, by rfl⟩ : syracuseStep 248413 = 93155) (by norm_num)
theorem B182893 : Blo 143792 182893 := bbase (se 3 (by rfl) ⟨34292, by rfl⟩ : syracuseStep 182893 = 68585) (by norm_num)
theorem B215693 : Blo 143792 215693 := bbase (se 3 (by rfl) ⟨40442, by rfl⟩ : syracuseStep 215693 = 80885) (by norm_num)
theorem B215717 : Blo 143792 215717 := bbase (se 4 (by rfl) ⟨20223, by rfl⟩ : syracuseStep 215717 = 40447) (by norm_num)
theorem B248501 : Blo 143792 248501 := bbase (se 5 (by rfl) ⟨11648, by rfl⟩ : syracuseStep 248501 = 23297) (by norm_num)
theorem B215741 : Blo 143792 215741 := bbase (se 3 (by rfl) ⟨40451, by rfl⟩ : syracuseStep 215741 = 80903) (by norm_num)
theorem B182989 : Blo 143792 182989 := bbase (se 3 (by rfl) ⟨34310, by rfl⟩ : syracuseStep 182989 = 68621) (by norm_num)
theorem B215765 : Blo 143792 215765 := bbase (se 7 (by rfl) ⟨2528, by rfl⟩ : syracuseStep 215765 = 5057) (by norm_num)
theorem B346837 : Blo 143792 346837 := bbase (se 7 (by rfl) ⟨4064, by rfl⟩ : syracuseStep 346837 = 8129) (by norm_num)
theorem B215789 : Blo 143792 215789 := bbase (se 3 (by rfl) ⟨40460, by rfl⟩ : syracuseStep 215789 = 80921) (by norm_num)
theorem B215813 : Blo 143792 215813 := bbase (se 4 (by rfl) ⟨20232, by rfl⟩ : syracuseStep 215813 = 40465) (by norm_num)
theorem B215837 : Blo 143792 215837 := bbase (se 3 (by rfl) ⟨40469, by rfl⟩ : syracuseStep 215837 = 80939) (by norm_num)
theorem B215861 : Blo 143792 215861 := bbase (se 5 (by rfl) ⟨10118, by rfl⟩ : syracuseStep 215861 = 20237) (by norm_num)
theorem B248629 : Blo 143792 248629 := bbase (se 5 (by rfl) ⟨11654, by rfl⟩ : syracuseStep 248629 = 23309) (by norm_num)
theorem B215885 : Blo 143792 215885 := bbase (se 3 (by rfl) ⟨40478, by rfl⟩ : syracuseStep 215885 = 80957) (by norm_num)
theorem B215909 : Blo 143792 215909 := bbase (se 4 (by rfl) ⟨20241, by rfl⟩ : syracuseStep 215909 = 40483) (by norm_num)
theorem B183161 : Blo 143792 183161 := bbase (se 2 (by rfl) ⟨68685, by rfl⟩ : syracuseStep 183161 = 137371) (by norm_num)
theorem B215933 : Blo 143792 215933 := bbase (se 3 (by rfl) ⟨40487, by rfl⟩ : syracuseStep 215933 = 80975) (by norm_num)
theorem B248717 : Blo 143792 248717 := bbase (se 3 (by rfl) ⟨46634, by rfl⟩ : syracuseStep 248717 = 93269) (by norm_num)
theorem B215957 : Blo 143792 215957 := bbase (se 6 (by rfl) ⟨5061, by rfl⟩ : syracuseStep 215957 = 10123) (by norm_num)
theorem B215981 : Blo 143792 215981 := bbase (se 3 (by rfl) ⟨40496, by rfl⟩ : syracuseStep 215981 = 80993) (by norm_num)
theorem B183217 : Blo 143792 183217 := bbase (se 2 (by rfl) ⟨68706, by rfl⟩ : syracuseStep 183217 = 137413) (by norm_num)
theorem B216005 : Blo 143792 216005 := bbase (se 4 (by rfl) ⟨20250, by rfl⟩ : syracuseStep 216005 = 40501) (by norm_num)
theorem B216029 : Blo 143792 216029 := bbase (se 3 (by rfl) ⟨40505, by rfl⟩ : syracuseStep 216029 = 81011) (by norm_num)
theorem B216053 : Blo 143792 216053 := bbase (se 5 (by rfl) ⟨10127, by rfl⟩ : syracuseStep 216053 = 20255) (by norm_num)
theorem B1100789 : Blo 143792 1100789 := bbase (se 5 (by rfl) ⟨51599, by rfl⟩ : syracuseStep 1100789 = 103199) (by norm_num)
theorem B216077 : Blo 143792 216077 := bbase (se 3 (by rfl) ⟨40514, by rfl⟩ : syracuseStep 216077 = 81029) (by norm_num)
theorem B248845 : Blo 143792 248845 := bbase (se 3 (by rfl) ⟨46658, by rfl⟩ : syracuseStep 248845 = 93317) (by norm_num)
theorem B183313 : Blo 143792 183313 := bbase (se 2 (by rfl) ⟨68742, by rfl⟩ : syracuseStep 183313 = 137485) (by norm_num)
theorem B216101 : Blo 143792 216101 := bbase (se 4 (by rfl) ⟨20259, by rfl⟩ : syracuseStep 216101 = 40519) (by norm_num)
theorem B216125 : Blo 143792 216125 := bbase (se 3 (by rfl) ⟨40523, by rfl⟩ : syracuseStep 216125 = 81047) (by norm_num)
theorem B216149 : Blo 143792 216149 := bbase (se 8 (by rfl) ⟨1266, by rfl⟩ : syracuseStep 216149 = 2533) (by norm_num)
theorem B248933 : Blo 143792 248933 := bbase (se 4 (by rfl) ⟨23337, by rfl⟩ : syracuseStep 248933 = 46675) (by norm_num)
theorem B216173 : Blo 143792 216173 := bbase (se 3 (by rfl) ⟨40532, by rfl⟩ : syracuseStep 216173 = 81065) (by norm_num)
theorem B216197 : Blo 143792 216197 := bbase (se 4 (by rfl) ⟨20268, by rfl⟩ : syracuseStep 216197 = 40537) (by norm_num)
theorem B740501 : Blo 143792 740501 := bbase (se 6 (by rfl) ⟨17355, by rfl⟩ : syracuseStep 740501 = 34711) (by norm_num)
theorem B216221 : Blo 143792 216221 := bbase (se 3 (by rfl) ⟨40541, by rfl⟩ : syracuseStep 216221 = 81083) (by norm_num)
theorem B216245 : Blo 143792 216245 := bbase (se 5 (by rfl) ⟨10136, by rfl⟩ : syracuseStep 216245 = 20273) (by norm_num)
theorem B183485 : Blo 143792 183485 := bbase (se 3 (by rfl) ⟨34403, by rfl⟩ : syracuseStep 183485 = 68807) (by norm_num)
theorem B216269 : Blo 143792 216269 := bbase (se 3 (by rfl) ⟨40550, by rfl⟩ : syracuseStep 216269 = 81101) (by norm_num)
theorem B216293 : Blo 143792 216293 := bbase (se 4 (by rfl) ⟨20277, by rfl⟩ : syracuseStep 216293 = 40555) (by norm_num)
theorem B249061 : Blo 143792 249061 := bbase (se 4 (by rfl) ⟨23349, by rfl⟩ : syracuseStep 249061 = 46699) (by norm_num)
theorem B183541 : Blo 143792 183541 := bbase (se 5 (by rfl) ⟨8603, by rfl⟩ : syracuseStep 183541 = 17207) (by norm_num)
theorem B216317 : Blo 143792 216317 := bbase (se 3 (by rfl) ⟨40559, by rfl⟩ : syracuseStep 216317 = 81119) (by norm_num)
theorem B314621 : Blo 143792 314621 := bbase (se 3 (by rfl) ⟨58991, by rfl⟩ : syracuseStep 314621 = 117983) (by norm_num)
theorem B412933 : Blo 143792 412933 := bbase (se 4 (by rfl) ⟨38712, by rfl⟩ : syracuseStep 412933 = 77425) (by norm_num)
theorem B216341 : Blo 143792 216341 := bbase (se 6 (by rfl) ⟨5070, by rfl⟩ : syracuseStep 216341 = 10141) (by norm_num)
theorem B2379029 : Blo 143792 2379029 := bbase (se 6 (by rfl) ⟨55758, by rfl⟩ : syracuseStep 2379029 = 111517) (by norm_num)
theorem B216365 : Blo 143792 216365 := bbase (se 3 (by rfl) ⟨40568, by rfl⟩ : syracuseStep 216365 = 81137) (by norm_num)
theorem B347453 : Blo 143792 347453 := bbase (se 3 (by rfl) ⟨65147, by rfl⟩ : syracuseStep 347453 = 130295) (by norm_num)
theorem B249149 : Blo 143792 249149 := bbase (se 3 (by rfl) ⟨46715, by rfl⟩ : syracuseStep 249149 = 93431) (by norm_num)
theorem B216389 : Blo 143792 216389 := bbase (se 4 (by rfl) ⟨20286, by rfl⟩ : syracuseStep 216389 = 40573) (by norm_num)
theorem B249157 : Blo 143792 249157 := bbase (se 4 (by rfl) ⟨23358, by rfl⟩ : syracuseStep 249157 = 46717) (by norm_num)
theorem B183637 : Blo 143792 183637 := bbase (se 11 (by rfl) ⟨134, by rfl⟩ : syracuseStep 183637 = 269) (by norm_num)
theorem B216413 : Blo 143792 216413 := bbase (se 3 (by rfl) ⟨40577, by rfl⟩ : syracuseStep 216413 = 81155) (by norm_num)
theorem B216437 : Blo 143792 216437 := bbase (se 5 (by rfl) ⟨10145, by rfl⟩ : syracuseStep 216437 = 20291) (by norm_num)
theorem B314741 : Blo 143792 314741 := bbase (se 5 (by rfl) ⟨14753, by rfl⟩ : syracuseStep 314741 = 29507) (by norm_num)
theorem B216461 : Blo 143792 216461 := bbase (se 3 (by rfl) ⟨40586, by rfl⟩ : syracuseStep 216461 = 81173) (by norm_num)
theorem B216485 : Blo 143792 216485 := bbase (se 4 (by rfl) ⟨20295, by rfl⟩ : syracuseStep 216485 = 40591) (by norm_num)
theorem B413093 : Blo 143792 413093 := bbase (se 4 (by rfl) ⟨38727, by rfl⟩ : syracuseStep 413093 = 77455) (by norm_num)
theorem B216509 : Blo 143792 216509 := bbase (se 3 (by rfl) ⟨40595, by rfl⟩ : syracuseStep 216509 = 81191) (by norm_num)
theorem B249277 : Blo 143792 249277 := bbase (se 3 (by rfl) ⟨46739, by rfl⟩ : syracuseStep 249277 = 93479) (by norm_num)
theorem B216533 : Blo 143792 216533 := bbase (se 7 (by rfl) ⟨2537, by rfl⟩ : syracuseStep 216533 = 5075) (by norm_num)
theorem B216557 : Blo 143792 216557 := bbase (se 3 (by rfl) ⟨40604, by rfl⟩ : syracuseStep 216557 = 81209) (by norm_num)
theorem B347645 : Blo 143792 347645 := bbase (se 3 (by rfl) ⟨65183, by rfl⟩ : syracuseStep 347645 = 130367) (by norm_num)
theorem B183809 : Blo 143792 183809 := bbase (se 2 (by rfl) ⟨68928, by rfl⟩ : syracuseStep 183809 = 137857) (by norm_num)
theorem B216581 : Blo 143792 216581 := bbase (se 4 (by rfl) ⟨20304, by rfl⟩ : syracuseStep 216581 = 40609) (by norm_num)
theorem B249365 : Blo 143792 249365 := bbase (se 6 (by rfl) ⟨5844, by rfl⟩ : syracuseStep 249365 = 11689) (by norm_num)
theorem B216605 : Blo 143792 216605 := bbase (se 3 (by rfl) ⟨40613, by rfl⟩ : syracuseStep 216605 = 81227) (by norm_num)
theorem B216629 : Blo 143792 216629 := bbase (se 5 (by rfl) ⟨10154, by rfl⟩ : syracuseStep 216629 = 20309) (by norm_num)
theorem B183865 : Blo 143792 183865 := bbase (se 2 (by rfl) ⟨68949, by rfl⟩ : syracuseStep 183865 = 137899) (by norm_num)
theorem B216653 : Blo 143792 216653 := bbase (se 3 (by rfl) ⟨40622, by rfl⟩ : syracuseStep 216653 = 81245) (by norm_num)
theorem B216677 : Blo 143792 216677 := bbase (se 4 (by rfl) ⟨20313, by rfl⟩ : syracuseStep 216677 = 40627) (by norm_num)
theorem B446069 : Blo 143792 446069 := bbase (se 5 (by rfl) ⟨20909, by rfl⟩ : syracuseStep 446069 = 41819) (by norm_num)
theorem B216701 : Blo 143792 216701 := bbase (se 3 (by rfl) ⟨40631, by rfl⟩ : syracuseStep 216701 = 81263) (by norm_num)
theorem B216725 : Blo 143792 216725 := bbase (se 6 (by rfl) ⟨5079, by rfl⟩ : syracuseStep 216725 = 10159) (by norm_num)
theorem B413333 : Blo 143792 413333 := bbase (se 6 (by rfl) ⟨9687, by rfl⟩ : syracuseStep 413333 = 19375) (by norm_num)
theorem B183961 : Blo 143792 183961 := bbase (se 2 (by rfl) ⟨68985, by rfl⟩ : syracuseStep 183961 = 137971) (by norm_num)
theorem B216749 : Blo 143792 216749 := bbase (se 3 (by rfl) ⟨40640, by rfl⟩ : syracuseStep 216749 = 81281) (by norm_num)
theorem B216773 : Blo 143792 216773 := bbase (se 4 (by rfl) ⟨20322, by rfl⟩ : syracuseStep 216773 = 40645) (by norm_num)
theorem B216797 : Blo 143792 216797 := bbase (se 3 (by rfl) ⟨40649, by rfl⟩ : syracuseStep 216797 = 81299) (by norm_num)
theorem B216821 : Blo 143792 216821 := bbase (se 5 (by rfl) ⟨10163, by rfl⟩ : syracuseStep 216821 = 20327) (by norm_num)
theorem B216845 : Blo 143792 216845 := bbase (se 3 (by rfl) ⟨40658, by rfl⟩ : syracuseStep 216845 = 81317) (by norm_num)
theorem B216869 : Blo 143792 216869 := bbase (se 4 (by rfl) ⟨20331, by rfl⟩ : syracuseStep 216869 = 40663) (by norm_num)
theorem B216893 : Blo 143792 216893 := bbase (se 3 (by rfl) ⟨40667, by rfl⟩ : syracuseStep 216893 = 81335) (by norm_num)
theorem B184133 : Blo 143792 184133 := bbase (se 4 (by rfl) ⟨17262, by rfl⟩ : syracuseStep 184133 = 34525) (by norm_num)
theorem B2117461 : Blo 143792 2117461 := bbase (se 9 (by rfl) ⟨6203, by rfl⟩ : syracuseStep 2117461 = 12407) (by norm_num)
theorem B216917 : Blo 143792 216917 := bbase (se 9 (by rfl) ⟨635, by rfl⟩ : syracuseStep 216917 = 1271) (by norm_num)
theorem B413525 : Blo 143792 413525 := bbase (se 9 (by rfl) ⟨1211, by rfl⟩ : syracuseStep 413525 = 2423) (by norm_num)
theorem B937813 : Blo 143792 937813 := bbase (se 9 (by rfl) ⟨2747, by rfl⟩ : syracuseStep 937813 = 5495) (by norm_num)
theorem B216941 : Blo 143792 216941 := bbase (se 3 (by rfl) ⟨40676, by rfl⟩ : syracuseStep 216941 = 81353) (by norm_num)
theorem B184189 : Blo 143792 184189 := bbase (se 3 (by rfl) ⟨34535, by rfl⟩ : syracuseStep 184189 = 69071) (by norm_num)
theorem B216965 : Blo 143792 216965 := bbase (se 4 (by rfl) ⟨20340, by rfl⟩ : syracuseStep 216965 = 40681) (by norm_num)
theorem B216989 : Blo 143792 216989 := bbase (se 3 (by rfl) ⟨40685, by rfl⟩ : syracuseStep 216989 = 81371) (by norm_num)
theorem B217013 : Blo 143792 217013 := bbase (se 5 (by rfl) ⟨10172, by rfl⟩ : syracuseStep 217013 = 20345) (by norm_num)
theorem B217037 : Blo 143792 217037 := bbase (se 3 (by rfl) ⟨40694, by rfl⟩ : syracuseStep 217037 = 81389) (by norm_num)
theorem B184285 : Blo 143792 184285 := bbase (se 3 (by rfl) ⟨34553, by rfl⟩ : syracuseStep 184285 = 69107) (by norm_num)
theorem B217061 : Blo 143792 217061 := bbase (se 4 (by rfl) ⟨20349, by rfl⟩ : syracuseStep 217061 = 40699) (by norm_num)
theorem B315373 : Blo 143792 315373 := bbase (se 3 (by rfl) ⟨59132, by rfl⟩ : syracuseStep 315373 = 118265) (by norm_num)
theorem B217085 : Blo 143792 217085 := bbase (se 3 (by rfl) ⟨40703, by rfl⟩ : syracuseStep 217085 = 81407) (by norm_num)
theorem B217109 : Blo 143792 217109 := bbase (se 6 (by rfl) ⟨5088, by rfl⟩ : syracuseStep 217109 = 10177) (by norm_num)
theorem B217133 : Blo 143792 217133 := bbase (se 3 (by rfl) ⟨40712, by rfl⟩ : syracuseStep 217133 = 81425) (by norm_num)
theorem B348221 : Blo 143792 348221 := bbase (se 3 (by rfl) ⟨65291, by rfl⟩ : syracuseStep 348221 = 130583) (by norm_num)
theorem B217157 : Blo 143792 217157 := bbase (se 4 (by rfl) ⟨20358, by rfl⟩ : syracuseStep 217157 = 40717) (by norm_num)
theorem B217181 : Blo 143792 217181 := bbase (se 3 (by rfl) ⟨40721, by rfl⟩ : syracuseStep 217181 = 81443) (by norm_num)
theorem B217205 : Blo 143792 217205 := bbase (se 5 (by rfl) ⟨10181, by rfl⟩ : syracuseStep 217205 = 20363) (by norm_num)
theorem B708725 : Blo 143792 708725 := bbase (se 5 (by rfl) ⟨33221, by rfl⟩ : syracuseStep 708725 = 66443) (by norm_num)
theorem B184457 : Blo 143792 184457 := bbase (se 2 (by rfl) ⟨69171, by rfl⟩ : syracuseStep 184457 = 138343) (by norm_num)
theorem B217229 : Blo 143792 217229 := bbase (se 3 (by rfl) ⟨40730, by rfl⟩ : syracuseStep 217229 = 81461) (by norm_num)
theorem B217253 : Blo 143792 217253 := bbase (se 4 (by rfl) ⟨20367, by rfl⟩ : syracuseStep 217253 = 40735) (by norm_num)
theorem B217277 : Blo 143792 217277 := bbase (se 3 (by rfl) ⟨40739, by rfl⟩ : syracuseStep 217277 = 81479) (by norm_num)
theorem B184513 : Blo 143792 184513 := bbase (se 2 (by rfl) ⟨69192, by rfl⟩ : syracuseStep 184513 = 138385) (by norm_num)
theorem B217301 : Blo 143792 217301 := bbase (se 7 (by rfl) ⟨2546, by rfl⟩ : syracuseStep 217301 = 5093) (by norm_num)
theorem B708821 : Blo 143792 708821 := bbase (se 7 (by rfl) ⟨8306, by rfl⟩ : syracuseStep 708821 = 16613) (by norm_num)
theorem B217325 : Blo 143792 217325 := bbase (se 3 (by rfl) ⟨40748, by rfl⟩ : syracuseStep 217325 = 81497) (by norm_num)
theorem B217349 : Blo 143792 217349 := bbase (se 4 (by rfl) ⟨20376, by rfl⟩ : syracuseStep 217349 = 40753) (by norm_num)
theorem B217373 : Blo 143792 217373 := bbase (se 3 (by rfl) ⟨40757, by rfl⟩ : syracuseStep 217373 = 81515) (by norm_num)
theorem B184609 : Blo 143792 184609 := bbase (se 2 (by rfl) ⟨69228, by rfl⟩ : syracuseStep 184609 = 138457) (by norm_num)
theorem B217397 : Blo 143792 217397 := bbase (se 5 (by rfl) ⟨10190, by rfl⟩ : syracuseStep 217397 = 20381) (by norm_num)
theorem B217421 : Blo 143792 217421 := bbase (se 3 (by rfl) ⟨40766, by rfl⟩ : syracuseStep 217421 = 81533) (by norm_num)
theorem B217445 : Blo 143792 217445 := bbase (se 4 (by rfl) ⟨20385, by rfl⟩ : syracuseStep 217445 = 40771) (by norm_num)
theorem B217469 : Blo 143792 217469 := bbase (se 3 (by rfl) ⟨40775, by rfl⟩ : syracuseStep 217469 = 81551) (by norm_num)
theorem B217493 : Blo 143792 217493 := bbase (se 6 (by rfl) ⟨5097, by rfl⟩ : syracuseStep 217493 = 10195) (by norm_num)
theorem B741797 : Blo 143792 741797 := bbase (se 4 (by rfl) ⟨69543, by rfl⟩ : syracuseStep 741797 = 139087) (by norm_num)
theorem B217517 : Blo 143792 217517 := bbase (se 3 (by rfl) ⟨40784, by rfl⟩ : syracuseStep 217517 = 81569) (by norm_num)
theorem B348605 : Blo 143792 348605 := bbase (se 3 (by rfl) ⟨65363, by rfl⟩ : syracuseStep 348605 = 130727) (by norm_num)
theorem B217541 : Blo 143792 217541 := bbase (se 4 (by rfl) ⟨20394, by rfl⟩ : syracuseStep 217541 = 40789) (by norm_num)
theorem B184781 : Blo 143792 184781 := bbase (se 3 (by rfl) ⟨34646, by rfl⟩ : syracuseStep 184781 = 69293) (by norm_num)
theorem B217565 : Blo 143792 217565 := bbase (se 3 (by rfl) ⟨40793, by rfl⟩ : syracuseStep 217565 = 81587) (by norm_num)
theorem B217589 : Blo 143792 217589 := bbase (se 5 (by rfl) ⟨10199, by rfl⟩ : syracuseStep 217589 = 20399) (by norm_num)
theorem B184837 : Blo 143792 184837 := bbase (se 4 (by rfl) ⟨17328, by rfl⟩ : syracuseStep 184837 = 34657) (by norm_num)
theorem B217613 : Blo 143792 217613 := bbase (se 3 (by rfl) ⟨40802, by rfl⟩ : syracuseStep 217613 = 81605) (by norm_num)
theorem B217637 : Blo 143792 217637 := bbase (se 4 (by rfl) ⟨20403, by rfl⟩ : syracuseStep 217637 = 40807) (by norm_num)
theorem B217661 : Blo 143792 217661 := bbase (se 3 (by rfl) ⟨40811, by rfl⟩ : syracuseStep 217661 = 81623) (by norm_num)
theorem B217685 : Blo 143792 217685 := bbase (se 8 (by rfl) ⟨1275, by rfl⟩ : syracuseStep 217685 = 2551) (by norm_num)
theorem B184933 : Blo 143792 184933 := bbase (se 4 (by rfl) ⟨17337, by rfl⟩ : syracuseStep 184933 = 34675) (by norm_num)
theorem B217709 : Blo 143792 217709 := bbase (se 3 (by rfl) ⟨40820, by rfl⟩ : syracuseStep 217709 = 81641) (by norm_num)
theorem B217733 : Blo 143792 217733 := bbase (se 4 (by rfl) ⟨20412, by rfl⟩ : syracuseStep 217733 = 40825) (by norm_num)
theorem B217757 : Blo 143792 217757 := bbase (se 3 (by rfl) ⟨40829, by rfl⟩ : syracuseStep 217757 = 81659) (by norm_num)
theorem B217781 : Blo 143792 217781 := bbase (se 5 (by rfl) ⟨10208, by rfl⟩ : syracuseStep 217781 = 20417) (by norm_num)
theorem B217805 : Blo 143792 217805 := bbase (se 3 (by rfl) ⟨40838, by rfl⟩ : syracuseStep 217805 = 81677) (by norm_num)
theorem B217829 : Blo 143792 217829 := bbase (se 4 (by rfl) ⟨20421, by rfl⟩ : syracuseStep 217829 = 40843) (by norm_num)
theorem B217853 : Blo 143792 217853 := bbase (se 3 (by rfl) ⟨40847, by rfl⟩ : syracuseStep 217853 = 81695) (by norm_num)
theorem B185105 : Blo 143792 185105 := bbase (se 2 (by rfl) ⟨69414, by rfl⟩ : syracuseStep 185105 = 138829) (by norm_num)
theorem B217877 : Blo 143792 217877 := bbase (se 6 (by rfl) ⟨5106, by rfl⟩ : syracuseStep 217877 = 10213) (by norm_num)
theorem B217901 : Blo 143792 217901 := bbase (se 3 (by rfl) ⟨40856, by rfl⟩ : syracuseStep 217901 = 81713) (by norm_num)
theorem B414517 : Blo 143792 414517 := bbase (se 5 (by rfl) ⟨19430, by rfl⟩ : syracuseStep 414517 = 38861) (by norm_num)
theorem B217925 : Blo 143792 217925 := bbase (se 4 (by rfl) ⟨20430, by rfl⟩ : syracuseStep 217925 = 40861) (by norm_num)
theorem B185161 : Blo 143792 185161 := bbase (se 2 (by rfl) ⟨69435, by rfl⟩ : syracuseStep 185161 = 138871) (by norm_num)
theorem B217949 : Blo 143792 217949 := bbase (se 3 (by rfl) ⟨40865, by rfl⟩ : syracuseStep 217949 = 81731) (by norm_num)
theorem B217973 : Blo 143792 217973 := bbase (se 5 (by rfl) ⟨10217, by rfl⟩ : syracuseStep 217973 = 20435) (by norm_num)
theorem B217997 : Blo 143792 217997 := bbase (se 3 (by rfl) ⟨40874, by rfl⟩ : syracuseStep 217997 = 81749) (by norm_num)
theorem B218021 : Blo 143792 218021 := bbase (se 4 (by rfl) ⟨20439, by rfl⟩ : syracuseStep 218021 = 40879) (by norm_num)
theorem B185257 : Blo 143792 185257 := bbase (se 2 (by rfl) ⟨69471, by rfl⟩ : syracuseStep 185257 = 138943) (by norm_num)
theorem B250805 : Blo 143792 250805 := bbase (se 5 (by rfl) ⟨11756, by rfl⟩ : syracuseStep 250805 = 23513) (by norm_num)
theorem B218045 : Blo 143792 218045 := bbase (se 3 (by rfl) ⟨40883, by rfl⟩ : syracuseStep 218045 = 81767) (by norm_num)
theorem B218069 : Blo 143792 218069 := bbase (se 7 (by rfl) ⟨2555, by rfl⟩ : syracuseStep 218069 = 5111) (by norm_num)
theorem B218093 : Blo 143792 218093 := bbase (se 3 (by rfl) ⟨40892, by rfl⟩ : syracuseStep 218093 = 81785) (by norm_num)
theorem B218117 : Blo 143792 218117 := bbase (se 4 (by rfl) ⟨20448, by rfl⟩ : syracuseStep 218117 = 40897) (by norm_num)
theorem B218141 : Blo 143792 218141 := bbase (se 3 (by rfl) ⟨40901, by rfl⟩ : syracuseStep 218141 = 81803) (by norm_num)
theorem B218165 : Blo 143792 218165 := bbase (se 5 (by rfl) ⟨10226, by rfl⟩ : syracuseStep 218165 = 20453) (by norm_num)
theorem B218189 : Blo 143792 218189 := bbase (se 3 (by rfl) ⟨40910, by rfl⟩ : syracuseStep 218189 = 81821) (by norm_num)
theorem B185429 : Blo 143792 185429 := bbase (se 8 (by rfl) ⟨1086, by rfl⟩ : syracuseStep 185429 = 2173) (by norm_num)
theorem B218213 : Blo 143792 218213 := bbase (se 4 (by rfl) ⟨20457, by rfl⟩ : syracuseStep 218213 = 40915) (by norm_num)
theorem B250997 : Blo 143792 250997 := bbase (se 5 (by rfl) ⟨11765, by rfl⟩ : syracuseStep 250997 = 23531) (by norm_num)
theorem B218237 : Blo 143792 218237 := bbase (se 3 (by rfl) ⟨40919, by rfl⟩ : syracuseStep 218237 = 81839) (by norm_num)
theorem B185485 : Blo 143792 185485 := bbase (se 3 (by rfl) ⟨34778, by rfl⟩ : syracuseStep 185485 = 69557) (by norm_num)
theorem B218261 : Blo 143792 218261 := bbase (se 6 (by rfl) ⟨5115, by rfl⟩ : syracuseStep 218261 = 10231) (by norm_num)
theorem B218285 : Blo 143792 218285 := bbase (se 3 (by rfl) ⟨40928, by rfl⟩ : syracuseStep 218285 = 81857) (by norm_num)
theorem B218309 : Blo 143792 218309 := bbase (se 4 (by rfl) ⟨20466, by rfl⟩ : syracuseStep 218309 = 40933) (by norm_num)
theorem B251093 : Blo 143792 251093 := bbase (se 7 (by rfl) ⟨2942, by rfl⟩ : syracuseStep 251093 = 5885) (by norm_num)
theorem B218333 : Blo 143792 218333 := bbase (se 3 (by rfl) ⟨40937, by rfl⟩ : syracuseStep 218333 = 81875) (by norm_num)
theorem B185581 : Blo 143792 185581 := bbase (se 3 (by rfl) ⟨34796, by rfl⟩ : syracuseStep 185581 = 69593) (by norm_num)
theorem B218357 : Blo 143792 218357 := bbase (se 5 (by rfl) ⟨10235, by rfl⟩ : syracuseStep 218357 = 20471) (by norm_num)
theorem B218381 : Blo 143792 218381 := bbase (se 3 (by rfl) ⟨40946, by rfl⟩ : syracuseStep 218381 = 81893) (by norm_num)
theorem B218405 : Blo 143792 218405 := bbase (se 4 (by rfl) ⟨20475, by rfl⟩ : syracuseStep 218405 = 40951) (by norm_num)
theorem B218429 : Blo 143792 218429 := bbase (se 3 (by rfl) ⟨40955, by rfl⟩ : syracuseStep 218429 = 81911) (by norm_num)
theorem B218453 : Blo 143792 218453 := bbase (se 17 (by rfl) ⟨2, by rfl⟩ : syracuseStep 218453 = 5) (by norm_num)
theorem B218477 : Blo 143792 218477 := bbase (se 3 (by rfl) ⟨40964, by rfl⟩ : syracuseStep 218477 = 81929) (by norm_num)
theorem B218501 : Blo 143792 218501 := bbase (se 4 (by rfl) ⟨20484, by rfl⟩ : syracuseStep 218501 = 40969) (by norm_num)
theorem B1037717 : Blo 143792 1037717 := bbase (se 6 (by rfl) ⟨24321, by rfl⟩ : syracuseStep 1037717 = 48643) (by norm_num)
theorem B185753 : Blo 143792 185753 := bbase (se 2 (by rfl) ⟨69657, by rfl⟩ : syracuseStep 185753 = 139315) (by norm_num)
theorem B218525 : Blo 143792 218525 := bbase (se 3 (by rfl) ⟨40973, by rfl⟩ : syracuseStep 218525 = 81947) (by norm_num)
theorem B218549 : Blo 143792 218549 := bbase (se 5 (by rfl) ⟨10244, by rfl⟩ : syracuseStep 218549 = 20489) (by norm_num)
theorem B218573 : Blo 143792 218573 := bbase (se 3 (by rfl) ⟨40982, by rfl⟩ : syracuseStep 218573 = 81965) (by norm_num)
theorem B185809 : Blo 143792 185809 := bbase (se 2 (by rfl) ⟨69678, by rfl⟩ : syracuseStep 185809 = 139357) (by norm_num)
theorem B218597 : Blo 143792 218597 := bbase (se 4 (by rfl) ⟨20493, by rfl⟩ : syracuseStep 218597 = 40987) (by norm_num)
theorem B218621 : Blo 143792 218621 := bbase (se 3 (by rfl) ⟨40991, by rfl⟩ : syracuseStep 218621 = 81983) (by norm_num)
theorem B218645 : Blo 143792 218645 := bbase (se 6 (by rfl) ⟨5124, by rfl⟩ : syracuseStep 218645 = 10249) (by norm_num)
theorem B218669 : Blo 143792 218669 := bbase (se 3 (by rfl) ⟨41000, by rfl⟩ : syracuseStep 218669 = 82001) (by norm_num)
theorem B185905 : Blo 143792 185905 := bbase (se 2 (by rfl) ⟨69714, by rfl⟩ : syracuseStep 185905 = 139429) (by norm_num)
theorem B218693 : Blo 143792 218693 := bbase (se 4 (by rfl) ⟨20502, by rfl⟩ : syracuseStep 218693 = 41005) (by norm_num)
theorem B218717 : Blo 143792 218717 := bbase (se 3 (by rfl) ⟨41009, by rfl⟩ : syracuseStep 218717 = 82019) (by norm_num)
theorem B218741 : Blo 143792 218741 := bbase (se 5 (by rfl) ⟨10253, by rfl⟩ : syracuseStep 218741 = 20507) (by norm_num)
theorem B218765 : Blo 143792 218765 := bbase (se 3 (by rfl) ⟨41018, by rfl⟩ : syracuseStep 218765 = 82037) (by norm_num)
theorem B218789 : Blo 143792 218789 := bbase (se 4 (by rfl) ⟨20511, by rfl⟩ : syracuseStep 218789 = 41023) (by norm_num)
theorem B743093 : Blo 143792 743093 := bbase (se 5 (by rfl) ⟨34832, by rfl⟩ : syracuseStep 743093 = 69665) (by norm_num)
theorem B218813 : Blo 143792 218813 := bbase (se 3 (by rfl) ⟨41027, by rfl⟩ : syracuseStep 218813 = 82055) (by norm_num)
theorem B218837 : Blo 143792 218837 := bbase (se 7 (by rfl) ⟨2564, by rfl⟩ : syracuseStep 218837 = 5129) (by norm_num)
theorem B186077 : Blo 143792 186077 := bbase (se 3 (by rfl) ⟨34889, by rfl⟩ : syracuseStep 186077 = 69779) (by norm_num)
theorem B218861 : Blo 143792 218861 := bbase (se 3 (by rfl) ⟨41036, by rfl⟩ : syracuseStep 218861 = 82073) (by norm_num)
theorem B218885 : Blo 143792 218885 := bbase (se 4 (by rfl) ⟨20520, by rfl⟩ : syracuseStep 218885 = 41041) (by norm_num)
theorem B186133 : Blo 143792 186133 := bbase (se 6 (by rfl) ⟨4362, by rfl⟩ : syracuseStep 186133 = 8725) (by norm_num)
theorem B218909 : Blo 143792 218909 := bbase (se 3 (by rfl) ⟨41045, by rfl⟩ : syracuseStep 218909 = 82091) (by norm_num)
theorem B218933 : Blo 143792 218933 := bbase (se 5 (by rfl) ⟨10262, by rfl⟩ : syracuseStep 218933 = 20525) (by norm_num)
theorem B186185 : Blo 143792 186185 := bbase (se 2 (by rfl) ⟨69819, by rfl⟩ : syracuseStep 186185 = 139639) (by norm_num)
theorem B218957 : Blo 143792 218957 := bbase (se 3 (by rfl) ⟨41054, by rfl⟩ : syracuseStep 218957 = 82109) (by norm_num)
theorem B218981 : Blo 143792 218981 := bbase (se 4 (by rfl) ⟨20529, by rfl⟩ : syracuseStep 218981 = 41059) (by norm_num)
theorem B186229 : Blo 143792 186229 := bbase (se 5 (by rfl) ⟨8729, by rfl⟩ : syracuseStep 186229 = 17459) (by norm_num)
theorem B219005 : Blo 143792 219005 := bbase (se 3 (by rfl) ⟨41063, by rfl⟩ : syracuseStep 219005 = 82127) (by norm_num)
theorem B415621 : Blo 143792 415621 := bbase (se 4 (by rfl) ⟨38964, by rfl⟩ : syracuseStep 415621 = 77929) (by norm_num)
theorem B219029 : Blo 143792 219029 := bbase (se 6 (by rfl) ⟨5133, by rfl⟩ : syracuseStep 219029 = 10267) (by norm_num)
theorem B219053 : Blo 143792 219053 := bbase (se 3 (by rfl) ⟨41072, by rfl⟩ : syracuseStep 219053 = 82145) (by norm_num)
theorem B219077 : Blo 143792 219077 := bbase (se 4 (by rfl) ⟨20538, by rfl⟩ : syracuseStep 219077 = 41077) (by norm_num)
theorem B219101 : Blo 143792 219101 := bbase (se 3 (by rfl) ⟨41081, by rfl⟩ : syracuseStep 219101 = 82163) (by norm_num)
theorem B186349 : Blo 143792 186349 := bbase (se 3 (by rfl) ⟨34940, by rfl⟩ : syracuseStep 186349 = 69881) (by norm_num)
theorem B219125 : Blo 143792 219125 := bbase (se 5 (by rfl) ⟨10271, by rfl⟩ : syracuseStep 219125 = 20543) (by norm_num)
theorem B219149 : Blo 143792 219149 := bbase (se 3 (by rfl) ⟨41090, by rfl⟩ : syracuseStep 219149 = 82181) (by norm_num)
theorem B186401 : Blo 143792 186401 := bbase (se 2 (by rfl) ⟨69900, by rfl⟩ : syracuseStep 186401 = 139801) (by norm_num)
theorem B219173 : Blo 143792 219173 := bbase (se 4 (by rfl) ⟨20547, by rfl⟩ : syracuseStep 219173 = 41095) (by norm_num)
theorem B219197 : Blo 143792 219197 := bbase (se 3 (by rfl) ⟨41099, by rfl⟩ : syracuseStep 219197 = 82199) (by norm_num)
theorem B219221 : Blo 143792 219221 := bbase (se 8 (by rfl) ⟨1284, by rfl⟩ : syracuseStep 219221 = 2569) (by norm_num)
theorem B186457 : Blo 143792 186457 := bbase (se 2 (by rfl) ⟨69921, by rfl⟩ : syracuseStep 186457 = 139843) (by norm_num)
theorem B219245 : Blo 143792 219245 := bbase (se 3 (by rfl) ⟨41108, by rfl⟩ : syracuseStep 219245 = 82217) (by norm_num)
theorem B219253 : Blo 143792 219253 := bbase (se 5 (by rfl) ⟨10277, by rfl⟩ : syracuseStep 219253 = 20555) (by norm_num)
theorem B219269 : Blo 143792 219269 := bbase (se 4 (by rfl) ⟨20556, by rfl⟩ : syracuseStep 219269 = 41113) (by norm_num)
theorem B350365 : Blo 143792 350365 := bbase (se 3 (by rfl) ⟨65693, by rfl⟩ : syracuseStep 350365 = 131387) (by norm_num)
theorem B219293 : Blo 143792 219293 := bbase (se 3 (by rfl) ⟨41117, by rfl⟩ : syracuseStep 219293 = 82235) (by norm_num)
theorem B219317 : Blo 143792 219317 := bbase (se 5 (by rfl) ⟨10280, by rfl⟩ : syracuseStep 219317 = 20561) (by norm_num)
theorem B186553 : Blo 143792 186553 := bbase (se 2 (by rfl) ⟨69957, by rfl⟩ : syracuseStep 186553 = 139915) (by norm_num)
theorem B219341 : Blo 143792 219341 := bbase (se 3 (by rfl) ⟨41126, by rfl⟩ : syracuseStep 219341 = 82253) (by norm_num)
theorem B219365 : Blo 143792 219365 := bbase (se 4 (by rfl) ⟨20565, by rfl⟩ : syracuseStep 219365 = 41131) (by norm_num)
theorem B219389 : Blo 143792 219389 := bbase (se 3 (by rfl) ⟨41135, by rfl⟩ : syracuseStep 219389 = 82271) (by norm_num)
theorem B219413 : Blo 143792 219413 := bbase (se 6 (by rfl) ⟨5142, by rfl⟩ : syracuseStep 219413 = 10285) (by norm_num)
theorem B219437 : Blo 143792 219437 := bbase (se 3 (by rfl) ⟨41144, by rfl⟩ : syracuseStep 219437 = 82289) (by norm_num)
theorem B219461 : Blo 143792 219461 := bbase (se 4 (by rfl) ⟨20574, by rfl⟩ : syracuseStep 219461 = 41149) (by norm_num)
theorem B219485 : Blo 143792 219485 := bbase (se 3 (by rfl) ⟨41153, by rfl⟩ : syracuseStep 219485 = 82307) (by norm_num)
theorem B186725 : Blo 143792 186725 := bbase (se 4 (by rfl) ⟨17505, by rfl⟩ : syracuseStep 186725 = 35011) (by norm_num)
theorem B219509 : Blo 143792 219509 := bbase (se 5 (by rfl) ⟨10289, by rfl⟩ : syracuseStep 219509 = 20579) (by norm_num)
theorem B219533 : Blo 143792 219533 := bbase (se 3 (by rfl) ⟨41162, by rfl⟩ : syracuseStep 219533 = 82325) (by norm_num)
theorem B154009 : Blo 143792 154009 := bbase (se 2 (by rfl) ⟨57753, by rfl⟩ : syracuseStep 154009 = 115507) (by norm_num)
theorem B186781 : Blo 143792 186781 := bbase (se 3 (by rfl) ⟨35021, by rfl⟩ : syracuseStep 186781 = 70043) (by norm_num)
theorem B219557 : Blo 143792 219557 := bbase (se 4 (by rfl) ⟨20583, by rfl⟩ : syracuseStep 219557 = 41167) (by norm_num)
theorem B219581 : Blo 143792 219581 := bbase (se 3 (by rfl) ⟨41171, by rfl⟩ : syracuseStep 219581 = 82343) (by norm_num)
theorem B219605 : Blo 143792 219605 := bbase (se 7 (by rfl) ⟨2573, by rfl⟩ : syracuseStep 219605 = 5147) (by norm_num)
theorem B154081 : Blo 143792 154081 := bbase (se 2 (by rfl) ⟨57780, by rfl⟩ : syracuseStep 154081 = 115561) (by norm_num)
theorem B219629 : Blo 143792 219629 := bbase (se 3 (by rfl) ⟨41180, by rfl⟩ : syracuseStep 219629 = 82361) (by norm_num)
theorem B186877 : Blo 143792 186877 := bbase (se 3 (by rfl) ⟨35039, by rfl⟩ : syracuseStep 186877 = 70079) (by norm_num)
theorem B219653 : Blo 143792 219653 := bbase (se 4 (by rfl) ⟨20592, by rfl⟩ : syracuseStep 219653 = 41185) (by norm_num)
theorem B219677 : Blo 143792 219677 := bbase (se 3 (by rfl) ⟨41189, by rfl⟩ : syracuseStep 219677 = 82379) (by norm_num)
theorem B219701 : Blo 143792 219701 := bbase (se 5 (by rfl) ⟨10298, by rfl⟩ : syracuseStep 219701 = 20597) (by norm_num)
theorem B219725 : Blo 143792 219725 := bbase (se 3 (by rfl) ⟨41198, by rfl⟩ : syracuseStep 219725 = 82397) (by norm_num)
theorem B219749 : Blo 143792 219749 := bbase (se 4 (by rfl) ⟨20601, by rfl⟩ : syracuseStep 219749 = 41203) (by norm_num)
theorem B219773 : Blo 143792 219773 := bbase (se 3 (by rfl) ⟨41207, by rfl⟩ : syracuseStep 219773 = 82415) (by norm_num)
theorem B154261 : Blo 143792 154261 := bbase (se 6 (by rfl) ⟨3615, by rfl⟩ : syracuseStep 154261 = 7231) (by norm_num)
theorem B219797 : Blo 143792 219797 := bbase (se 6 (by rfl) ⟨5151, by rfl⟩ : syracuseStep 219797 = 10303) (by norm_num)
theorem B187049 : Blo 143792 187049 := bbase (se 2 (by rfl) ⟨70143, by rfl⟩ : syracuseStep 187049 = 140287) (by norm_num)
theorem B219821 : Blo 143792 219821 := bbase (se 3 (by rfl) ⟨41216, by rfl⟩ : syracuseStep 219821 = 82433) (by norm_num)
theorem B219845 : Blo 143792 219845 := bbase (se 4 (by rfl) ⟨20610, by rfl⟩ : syracuseStep 219845 = 41221) (by norm_num)
theorem B219869 : Blo 143792 219869 := bbase (se 3 (by rfl) ⟨41225, by rfl⟩ : syracuseStep 219869 = 82451) (by norm_num)
theorem B219893 : Blo 143792 219893 := bbase (se 5 (by rfl) ⟨10307, by rfl⟩ : syracuseStep 219893 = 20615) (by norm_num)
theorem B219917 : Blo 143792 219917 := bbase (se 3 (by rfl) ⟨41234, by rfl⟩ : syracuseStep 219917 = 82469) (by norm_num)
theorem B219941 : Blo 143792 219941 := bbase (se 4 (by rfl) ⟨20619, by rfl⟩ : syracuseStep 219941 = 41239) (by norm_num)
theorem B219965 : Blo 143792 219965 := bbase (se 3 (by rfl) ⟨41243, by rfl⟩ : syracuseStep 219965 = 82487) (by norm_num)
theorem B219989 : Blo 143792 219989 := bbase (se 9 (by rfl) ⟨644, by rfl⟩ : syracuseStep 219989 = 1289) (by norm_num)
theorem B220013 : Blo 143792 220013 := bbase (se 3 (by rfl) ⟨41252, by rfl⟩ : syracuseStep 220013 = 82505) (by norm_num)
theorem B220037 : Blo 143792 220037 := bbase (se 4 (by rfl) ⟨20628, by rfl⟩ : syracuseStep 220037 = 41257) (by norm_num)
theorem B220061 : Blo 143792 220061 := bbase (se 3 (by rfl) ⟨41261, by rfl⟩ : syracuseStep 220061 = 82523) (by norm_num)
theorem B220085 : Blo 143792 220085 := bbase (se 5 (by rfl) ⟨10316, by rfl⟩ : syracuseStep 220085 = 20633) (by norm_num)
theorem B744389 : Blo 143792 744389 := bbase (se 4 (by rfl) ⟨69786, by rfl⟩ : syracuseStep 744389 = 139573) (by norm_num)
theorem B220109 : Blo 143792 220109 := bbase (se 3 (by rfl) ⟨41270, by rfl⟩ : syracuseStep 220109 = 82541) (by norm_num)
theorem B220133 : Blo 143792 220133 := bbase (se 4 (by rfl) ⟨20637, by rfl⟩ : syracuseStep 220133 = 41275) (by norm_num)
theorem B547829 : Blo 143792 547829 := bbase (se 5 (by rfl) ⟨25679, by rfl⟩ : syracuseStep 547829 = 51359) (by norm_num)
theorem B220157 : Blo 143792 220157 := bbase (se 3 (by rfl) ⟨41279, by rfl⟩ : syracuseStep 220157 = 82559) (by norm_num)
theorem B220181 : Blo 143792 220181 := bbase (se 6 (by rfl) ⟨5160, by rfl⟩ : syracuseStep 220181 = 10321) (by norm_num)
theorem B220205 : Blo 143792 220205 := bbase (se 3 (by rfl) ⟨41288, by rfl⟩ : syracuseStep 220205 = 82577) (by norm_num)
theorem B220229 : Blo 143792 220229 := bbase (se 4 (by rfl) ⟨20646, by rfl⟩ : syracuseStep 220229 = 41293) (by norm_num)
theorem B154705 : Blo 143792 154705 := bbase (se 2 (by rfl) ⟨58014, by rfl⟩ : syracuseStep 154705 = 116029) (by norm_num)
theorem B220253 : Blo 143792 220253 := bbase (se 3 (by rfl) ⟨41297, by rfl⟩ : syracuseStep 220253 = 82595) (by norm_num)
theorem B220277 : Blo 143792 220277 := bbase (se 5 (by rfl) ⟨10325, by rfl⟩ : syracuseStep 220277 = 20651) (by norm_num)
theorem B187525 : Blo 143792 187525 := bbase (se 4 (by rfl) ⟨17580, by rfl⟩ : syracuseStep 187525 = 35161) (by norm_num)
theorem B351373 : Blo 143792 351373 := bbase (se 3 (by rfl) ⟨65882, by rfl⟩ : syracuseStep 351373 = 131765) (by norm_num)
theorem B220301 : Blo 143792 220301 := bbase (se 3 (by rfl) ⟨41306, by rfl⟩ : syracuseStep 220301 = 82613) (by norm_num)
theorem B220325 : Blo 143792 220325 := bbase (se 4 (by rfl) ⟨20655, by rfl⟩ : syracuseStep 220325 = 41311) (by norm_num)
theorem B220349 : Blo 143792 220349 := bbase (se 3 (by rfl) ⟨41315, by rfl⟩ : syracuseStep 220349 = 82631) (by norm_num)
theorem B154829 : Blo 143792 154829 := bbase (se 3 (by rfl) ⟨29030, by rfl⟩ : syracuseStep 154829 = 58061) (by norm_num)
theorem B220373 : Blo 143792 220373 := bbase (se 7 (by rfl) ⟨2582, by rfl⟩ : syracuseStep 220373 = 5165) (by norm_num)
theorem B351469 : Blo 143792 351469 := bbase (se 3 (by rfl) ⟨65900, by rfl⟩ : syracuseStep 351469 = 131801) (by norm_num)
theorem B220397 : Blo 143792 220397 := bbase (se 3 (by rfl) ⟨41324, by rfl⟩ : syracuseStep 220397 = 82649) (by norm_num)
theorem B220421 : Blo 143792 220421 := bbase (se 4 (by rfl) ⟨20664, by rfl⟩ : syracuseStep 220421 = 41329) (by norm_num)
theorem B548117 : Blo 143792 548117 := bbase (se 6 (by rfl) ⟨12846, by rfl⟩ : syracuseStep 548117 = 25693) (by norm_num)
theorem B220445 : Blo 143792 220445 := bbase (se 3 (by rfl) ⟨41333, by rfl⟩ : syracuseStep 220445 = 82667) (by norm_num)
theorem B220469 : Blo 143792 220469 := bbase (se 5 (by rfl) ⟨10334, by rfl⟩ : syracuseStep 220469 = 20669) (by norm_num)
theorem B220493 : Blo 143792 220493 := bbase (se 3 (by rfl) ⟨41342, by rfl⟩ : syracuseStep 220493 = 82685) (by norm_num)
theorem B417125 : Blo 143792 417125 := bbase (se 4 (by rfl) ⟨39105, by rfl⟩ : syracuseStep 417125 = 78211) (by norm_num)
theorem B220517 : Blo 143792 220517 := bbase (se 4 (by rfl) ⟨20673, by rfl⟩ : syracuseStep 220517 = 41347) (by norm_num)
theorem B253309 : Blo 143792 253309 := bbase (se 3 (by rfl) ⟨47495, by rfl⟩ : syracuseStep 253309 = 94991) (by norm_num)
theorem B220541 : Blo 143792 220541 := bbase (se 3 (by rfl) ⟨41351, by rfl⟩ : syracuseStep 220541 = 82703) (by norm_num)
theorem B220565 : Blo 143792 220565 := bbase (se 6 (by rfl) ⟨5169, by rfl⟩ : syracuseStep 220565 = 10339) (by norm_num)
theorem B220589 : Blo 143792 220589 := bbase (se 3 (by rfl) ⟨41360, by rfl⟩ : syracuseStep 220589 = 82721) (by norm_num)
theorem B220613 : Blo 143792 220613 := bbase (se 4 (by rfl) ⟨20682, by rfl⟩ : syracuseStep 220613 = 41365) (by norm_num)
theorem B155081 : Blo 143792 155081 := bbase (se 2 (by rfl) ⟨58155, by rfl⟩ : syracuseStep 155081 = 116311) (by norm_num)
theorem B220637 : Blo 143792 220637 := bbase (se 3 (by rfl) ⟨41369, by rfl⟩ : syracuseStep 220637 = 82739) (by norm_num)
theorem B220661 : Blo 143792 220661 := bbase (se 5 (by rfl) ⟨10343, by rfl⟩ : syracuseStep 220661 = 20687) (by norm_num)
theorem B220685 : Blo 143792 220685 := bbase (se 3 (by rfl) ⟨41378, by rfl⟩ : syracuseStep 220685 = 82757) (by norm_num)
theorem B220709 : Blo 143792 220709 := bbase (se 4 (by rfl) ⟨20691, by rfl⟩ : syracuseStep 220709 = 41383) (by norm_num)
theorem B220733 : Blo 143792 220733 := bbase (se 3 (by rfl) ⟨41387, by rfl⟩ : syracuseStep 220733 = 82775) (by norm_num)
theorem B220757 : Blo 143792 220757 := bbase (se 8 (by rfl) ⟨1293, by rfl⟩ : syracuseStep 220757 = 2587) (by norm_num)
theorem B220781 : Blo 143792 220781 := bbase (se 3 (by rfl) ⟨41396, by rfl⟩ : syracuseStep 220781 = 82793) (by norm_num)
theorem B220805 : Blo 143792 220805 := bbase (se 4 (by rfl) ⟨20700, by rfl⟩ : syracuseStep 220805 = 41401) (by norm_num)
theorem B1171093 : Blo 143792 1171093 := bbase (se 6 (by rfl) ⟨27447, by rfl⟩ : syracuseStep 1171093 = 54895) (by norm_num)
theorem B220829 : Blo 143792 220829 := bbase (se 3 (by rfl) ⟨41405, by rfl⟩ : syracuseStep 220829 = 82811) (by norm_num)
theorem B220853 : Blo 143792 220853 := bbase (se 5 (by rfl) ⟨10352, by rfl⟩ : syracuseStep 220853 = 20705) (by norm_num)
theorem B220877 : Blo 143792 220877 := bbase (se 3 (by rfl) ⟨41414, by rfl⟩ : syracuseStep 220877 = 82829) (by norm_num)
theorem B220901 : Blo 143792 220901 := bbase (se 4 (by rfl) ⟨20709, by rfl⟩ : syracuseStep 220901 = 41419) (by norm_num)
theorem B351989 : Blo 143792 351989 := bbase (se 5 (by rfl) ⟨16499, by rfl⟩ : syracuseStep 351989 = 32999) (by norm_num)
theorem B941813 : Blo 143792 941813 := bbase (se 5 (by rfl) ⟨44147, by rfl⟩ : syracuseStep 941813 = 88295) (by norm_num)
theorem B220925 : Blo 143792 220925 := bbase (se 3 (by rfl) ⟨41423, by rfl⟩ : syracuseStep 220925 = 82847) (by norm_num)
theorem B220949 : Blo 143792 220949 := bbase (se 6 (by rfl) ⟨5178, by rfl⟩ : syracuseStep 220949 = 10357) (by norm_num)
theorem B220973 : Blo 143792 220973 := bbase (se 3 (by rfl) ⟨41432, by rfl⟩ : syracuseStep 220973 = 82865) (by norm_num)
theorem B220997 : Blo 143792 220997 := bbase (se 4 (by rfl) ⟨20718, by rfl⟩ : syracuseStep 220997 = 41437) (by norm_num)
theorem B221021 : Blo 143792 221021 := bbase (se 3 (by rfl) ⟨41441, by rfl⟩ : syracuseStep 221021 = 82883) (by norm_num)
theorem B221045 : Blo 143792 221045 := bbase (se 5 (by rfl) ⟨10361, by rfl⟩ : syracuseStep 221045 = 20723) (by norm_num)
theorem B155525 : Blo 143792 155525 := bbase (se 4 (by rfl) ⟨14580, by rfl⟩ : syracuseStep 155525 = 29161) (by norm_num)
theorem B221069 : Blo 143792 221069 := bbase (se 3 (by rfl) ⟨41450, by rfl⟩ : syracuseStep 221069 = 82901) (by norm_num)
theorem B221093 : Blo 143792 221093 := bbase (se 4 (by rfl) ⟨20727, by rfl⟩ : syracuseStep 221093 = 41455) (by norm_num)
theorem B221117 : Blo 143792 221117 := bbase (se 3 (by rfl) ⟨41459, by rfl⟩ : syracuseStep 221117 = 82919) (by norm_num)
theorem B221141 : Blo 143792 221141 := bbase (se 7 (by rfl) ⟨2591, by rfl⟩ : syracuseStep 221141 = 5183) (by norm_num)
theorem B221165 : Blo 143792 221165 := bbase (se 3 (by rfl) ⟨41468, by rfl⟩ : syracuseStep 221165 = 82937) (by norm_num)
theorem B319469 : Blo 143792 319469 := bbase (se 3 (by rfl) ⟨59900, by rfl⟩ : syracuseStep 319469 = 119801) (by norm_num)
theorem B221189 : Blo 143792 221189 := bbase (se 4 (by rfl) ⟨20736, by rfl⟩ : syracuseStep 221189 = 41473) (by norm_num)
theorem B221213 : Blo 143792 221213 := bbase (se 3 (by rfl) ⟨41477, by rfl⟩ : syracuseStep 221213 = 82955) (by norm_num)
theorem B221237 : Blo 143792 221237 := bbase (se 5 (by rfl) ⟨10370, by rfl⟩ : syracuseStep 221237 = 20741) (by norm_num)
theorem B221261 : Blo 143792 221261 := bbase (se 3 (by rfl) ⟨41486, by rfl⟩ : syracuseStep 221261 = 82973) (by norm_num)
theorem B221285 : Blo 143792 221285 := bbase (se 4 (by rfl) ⟨20745, by rfl⟩ : syracuseStep 221285 = 41491) (by norm_num)
theorem B155773 : Blo 143792 155773 := bbase (se 3 (by rfl) ⟨29207, by rfl⟩ : syracuseStep 155773 = 58415) (by norm_num)
theorem B221309 : Blo 143792 221309 := bbase (se 3 (by rfl) ⟨41495, by rfl⟩ : syracuseStep 221309 = 82991) (by norm_num)
theorem B1597589 : Blo 143792 1597589 := bbase (se 6 (by rfl) ⟨37443, by rfl⟩ : syracuseStep 1597589 = 74887) (by norm_num)
theorem B221333 : Blo 143792 221333 := bbase (se 6 (by rfl) ⟨5187, by rfl⟩ : syracuseStep 221333 = 10375) (by norm_num)
theorem B221357 : Blo 143792 221357 := bbase (se 3 (by rfl) ⟨41504, by rfl⟩ : syracuseStep 221357 = 83009) (by norm_num)
theorem B221381 : Blo 143792 221381 := bbase (se 4 (by rfl) ⟨20754, by rfl⟩ : syracuseStep 221381 = 41509) (by norm_num)
theorem B745685 : Blo 143792 745685 := bbase (se 7 (by rfl) ⟨8738, by rfl⟩ : syracuseStep 745685 = 17477) (by norm_num)
theorem B254173 : Blo 143792 254173 := bbase (se 3 (by rfl) ⟨47657, by rfl⟩ : syracuseStep 254173 = 95315) (by norm_num)
theorem B221405 : Blo 143792 221405 := bbase (se 3 (by rfl) ⟨41513, by rfl⟩ : syracuseStep 221405 = 83027) (by norm_num)
theorem B221429 : Blo 143792 221429 := bbase (se 5 (by rfl) ⟨10379, by rfl⟩ : syracuseStep 221429 = 20759) (by norm_num)
theorem B352517 : Blo 143792 352517 := bbase (se 4 (by rfl) ⟨33048, by rfl⟩ : syracuseStep 352517 = 66097) (by norm_num)
theorem B221453 : Blo 143792 221453 := bbase (se 3 (by rfl) ⟨41522, by rfl⟩ : syracuseStep 221453 = 83045) (by norm_num)
theorem B221477 : Blo 143792 221477 := bbase (se 4 (by rfl) ⟨20763, by rfl⟩ : syracuseStep 221477 = 41527) (by norm_num)
theorem B221501 : Blo 143792 221501 := bbase (se 3 (by rfl) ⟨41531, by rfl⟩ : syracuseStep 221501 = 83063) (by norm_num)
theorem B221525 : Blo 143792 221525 := bbase (se 10 (by rfl) ⟨324, by rfl⟩ : syracuseStep 221525 = 649) (by norm_num)
theorem B680293 : Blo 143792 680293 := bbase (se 4 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 680293 = 127555) (by norm_num)
theorem B483685 : Blo 143792 483685 := bbase (se 4 (by rfl) ⟨45345, by rfl⟩ : syracuseStep 483685 = 90691) (by norm_num)
theorem B221549 : Blo 143792 221549 := bbase (se 3 (by rfl) ⟨41540, by rfl⟩ : syracuseStep 221549 = 83081) (by norm_num)
theorem B680309 : Blo 143792 680309 := bbase (se 5 (by rfl) ⟨31889, by rfl⟩ : syracuseStep 680309 = 63779) (by norm_num)
theorem B221573 : Blo 143792 221573 := bbase (se 4 (by rfl) ⟨20772, by rfl⟩ : syracuseStep 221573 = 41545) (by norm_num)
theorem B221597 : Blo 143792 221597 := bbase (se 3 (by rfl) ⟨41549, by rfl⟩ : syracuseStep 221597 = 83099) (by norm_num)
theorem B549301 : Blo 143792 549301 := bbase (se 5 (by rfl) ⟨25748, by rfl⟩ : syracuseStep 549301 = 51497) (by norm_num)
theorem B221621 : Blo 143792 221621 := bbase (se 5 (by rfl) ⟨10388, by rfl⟩ : syracuseStep 221621 = 20777) (by norm_num)
theorem B221645 : Blo 143792 221645 := bbase (se 3 (by rfl) ⟨41558, by rfl⟩ : syracuseStep 221645 = 83117) (by norm_num)
theorem B221669 : Blo 143792 221669 := bbase (se 4 (by rfl) ⟨20781, by rfl⟩ : syracuseStep 221669 = 41563) (by norm_num)
theorem B352757 : Blo 143792 352757 := bbase (se 5 (by rfl) ⟨16535, by rfl⟩ : syracuseStep 352757 = 33071) (by norm_num)
theorem B156217 : Blo 143792 156217 := bbase (se 2 (by rfl) ⟨58581, by rfl⟩ : syracuseStep 156217 = 117163) (by norm_num)
theorem B156277 : Blo 143792 156277 := bbase (se 5 (by rfl) ⟨7325, by rfl⟩ : syracuseStep 156277 = 14651) (by norm_num)
theorem B549605 : Blo 143792 549605 := bbase (se 4 (by rfl) ⟨51525, by rfl⟩ : syracuseStep 549605 = 103051) (by norm_num)
theorem B418709 : Blo 143792 418709 := bbase (se 6 (by rfl) ⟨9813, by rfl⟩ : syracuseStep 418709 = 19627) (by norm_num)
theorem B156593 : Blo 143792 156593 := bbase (se 2 (by rfl) ⟨58722, by rfl⟩ : syracuseStep 156593 = 117445) (by norm_num)
theorem B157037 : Blo 143792 157037 := bbase (se 3 (by rfl) ⟨29444, by rfl⟩ : syracuseStep 157037 = 58889) (by norm_num)
theorem B157097 : Blo 143792 157097 := bbase (se 2 (by rfl) ⟨58911, by rfl⟩ : syracuseStep 157097 = 117823) (by norm_num)
theorem B746981 : Blo 143792 746981 := bbase (se 4 (by rfl) ⟨70029, by rfl⟩ : syracuseStep 746981 = 140059) (by norm_num)
theorem B222725 : Blo 143792 222725 := bbase (se 4 (by rfl) ⟨20880, by rfl⟩ : syracuseStep 222725 = 41761) (by norm_num)
theorem B157225 : Blo 143792 157225 := bbase (se 2 (by rfl) ⟨58959, by rfl⟩ : syracuseStep 157225 = 117919) (by norm_num)
theorem B419381 : Blo 143792 419381 := bbase (se 5 (by rfl) ⟨19658, by rfl⟩ : syracuseStep 419381 = 39317) (by norm_num)
theorem B419717 : Blo 143792 419717 := bbase (se 4 (by rfl) ⟨39348, by rfl⟩ : syracuseStep 419717 = 78697) (by norm_num)
theorem B419813 : Blo 143792 419813 := bbase (se 4 (by rfl) ⟨39357, by rfl⟩ : syracuseStep 419813 = 78715) (by norm_num)
theorem B157669 : Blo 143792 157669 := bbase (se 4 (by rfl) ⟨14781, by rfl⟩ : syracuseStep 157669 = 29563) (by norm_num)
theorem B157789 : Blo 143792 157789 := bbase (se 3 (by rfl) ⟨29585, by rfl⟩ : syracuseStep 157789 = 59171) (by norm_num)
theorem B354469 : Blo 143792 354469 := bbase (se 4 (by rfl) ⟨33231, by rfl⟩ : syracuseStep 354469 = 66463) (by norm_num)
theorem B485621 : Blo 143792 485621 := bbase (se 5 (by rfl) ⟨22763, by rfl⟩ : syracuseStep 485621 = 45527) (by norm_num)
theorem B158089 : Blo 143792 158089 := bbase (se 2 (by rfl) ⟨59283, by rfl⟩ : syracuseStep 158089 = 118567) (by norm_num)
theorem B1108565 : Blo 143792 1108565 := bbase (se 8 (by rfl) ⟨6495, by rfl⟩ : syracuseStep 1108565 = 12991) (by norm_num)
theorem B486053 : Blo 143792 486053 := bbase (se 4 (by rfl) ⟨45567, by rfl⟩ : syracuseStep 486053 = 91135) (by norm_num)
theorem B420565 : Blo 143792 420565 := bbase (se 7 (by rfl) ⟨4928, by rfl⟩ : syracuseStep 420565 = 9857) (by norm_num)
theorem B551717 : Blo 143792 551717 := bbase (se 4 (by rfl) ⟨51723, by rfl⟩ : syracuseStep 551717 = 103447) (by norm_num)
theorem B1239893 : Blo 143792 1239893 := bbase (se 9 (by rfl) ⟨3632, by rfl⟩ : syracuseStep 1239893 = 7265) (by norm_num)
theorem B552005 : Blo 143792 552005 := bbase (se 4 (by rfl) ⟨51750, by rfl⟩ : syracuseStep 552005 = 103501) (by norm_num)
theorem B486485 : Blo 143792 486485 := bbase (se 8 (by rfl) ⟨2850, by rfl⟩ : syracuseStep 486485 = 5701) (by norm_num)
theorem B617813 : Blo 143792 617813 := bbase (se 11 (by rfl) ⟨452, by rfl⟩ : syracuseStep 617813 = 905) (by norm_num)
theorem B585157 : Blo 143792 585157 := bbase (se 4 (by rfl) ⟨54858, by rfl⟩ : syracuseStep 585157 = 109717) (by norm_num)
theorem B323021 : Blo 143792 323021 := bbase (se 3 (by rfl) ⟨60566, by rfl⟩ : syracuseStep 323021 = 121133) (by norm_num)
theorem B159197 : Blo 143792 159197 := bbase (se 3 (by rfl) ⟨29849, by rfl⟩ : syracuseStep 159197 = 59699) (by norm_num)
theorem B486917 : Blo 143792 486917 := bbase (se 4 (by rfl) ⟨45648, by rfl⟩ : syracuseStep 486917 = 91297) (by norm_num)
theorem B618101 : Blo 143792 618101 := bbase (se 5 (by rfl) ⟨28973, by rfl⟩ : syracuseStep 618101 = 57947) (by norm_num)
theorem B487349 : Blo 143792 487349 := bbase (se 5 (by rfl) ⟨22844, by rfl⟩ : syracuseStep 487349 = 45689) (by norm_num)
theorem B1142741 : Blo 143792 1142741 := bbase (se 7 (by rfl) ⟨13391, by rfl⟩ : syracuseStep 1142741 = 26783) (by norm_num)
theorem B323549 : Blo 143792 323549 := bbase (se 3 (by rfl) ⟨60665, by rfl⟩ : syracuseStep 323549 = 121331) (by norm_num)
theorem B159713 : Blo 143792 159713 := bbase (se 2 (by rfl) ⟨59892, by rfl⟩ : syracuseStep 159713 = 119785) (by norm_num)
theorem B323621 : Blo 143792 323621 := bbase (se 4 (by rfl) ⟨30339, by rfl⟩ : syracuseStep 323621 = 60679) (by norm_num)
theorem B323693 : Blo 143792 323693 := bbase (se 3 (by rfl) ⟨60692, by rfl⟩ : syracuseStep 323693 = 121385) (by norm_num)
theorem B422021 : Blo 143792 422021 := bbase (se 4 (by rfl) ⟨39564, by rfl⟩ : syracuseStep 422021 = 79129) (by norm_num)
theorem B323765 : Blo 143792 323765 := bbase (se 5 (by rfl) ⟨15176, by rfl⟩ : syracuseStep 323765 = 30353) (by norm_num)
theorem B553189 : Blo 143792 553189 := bbase (se 4 (by rfl) ⟨51861, by rfl⟩ : syracuseStep 553189 = 103723) (by norm_num)
theorem B323837 : Blo 143792 323837 := bbase (se 3 (by rfl) ⟨60719, by rfl⟩ : syracuseStep 323837 = 121439) (by norm_num)
theorem B323909 : Blo 143792 323909 := bbase (se 4 (by rfl) ⟨30366, by rfl⟩ : syracuseStep 323909 = 60733) (by norm_num)
theorem B487781 : Blo 143792 487781 := bbase (se 4 (by rfl) ⟨45729, by rfl⟩ : syracuseStep 487781 = 91459) (by norm_num)
theorem B618853 : Blo 143792 618853 := bbase (se 4 (by rfl) ⟨58017, by rfl⟩ : syracuseStep 618853 = 116035) (by norm_num)
theorem B323981 : Blo 143792 323981 := bbase (se 3 (by rfl) ⟨60746, by rfl⟩ : syracuseStep 323981 = 121493) (by norm_num)
theorem B324053 : Blo 143792 324053 := bbase (se 7 (by rfl) ⟨3797, by rfl⟩ : syracuseStep 324053 = 7595) (by norm_num)
theorem B553493 : Blo 143792 553493 := bbase (se 6 (by rfl) ⟨12972, by rfl⟩ : syracuseStep 553493 = 25945) (by norm_num)
theorem B324125 : Blo 143792 324125 := bbase (se 3 (by rfl) ⟨60773, by rfl⟩ : syracuseStep 324125 = 121547) (by norm_num)
theorem B225845 : Blo 143792 225845 := bbase (se 5 (by rfl) ⟨10586, by rfl⟩ : syracuseStep 225845 = 21173) (by norm_num)
theorem B324197 : Blo 143792 324197 := bbase (se 4 (by rfl) ⟨30393, by rfl⟩ : syracuseStep 324197 = 60787) (by norm_num)
theorem B848501 : Blo 143792 848501 := bbase (se 5 (by rfl) ⟨39773, by rfl⟩ : syracuseStep 848501 = 79547) (by norm_num)
theorem B324269 : Blo 143792 324269 := bbase (se 3 (by rfl) ⟨60800, by rfl⟩ : syracuseStep 324269 = 121601) (by norm_num)
theorem B291541 : Blo 143792 291541 := bbase (se 7 (by rfl) ⟨3416, by rfl⟩ : syracuseStep 291541 = 6833) (by norm_num)
theorem B324341 : Blo 143792 324341 := bbase (se 5 (by rfl) ⟨15203, by rfl⟩ : syracuseStep 324341 = 30407) (by norm_num)
theorem B488213 : Blo 143792 488213 := bbase (se 6 (by rfl) ⟨11442, by rfl⟩ : syracuseStep 488213 = 22885) (by norm_num)
theorem B324413 : Blo 143792 324413 := bbase (se 3 (by rfl) ⟨60827, by rfl⟩ : syracuseStep 324413 = 121655) (by norm_num)
theorem B324485 : Blo 143792 324485 := bbase (se 4 (by rfl) ⟨30420, by rfl⟩ : syracuseStep 324485 = 60841) (by norm_num)
theorem B324557 : Blo 143792 324557 := bbase (se 3 (by rfl) ⟨60854, by rfl⟩ : syracuseStep 324557 = 121709) (by norm_num)
theorem B324629 : Blo 143792 324629 := bbase (se 6 (by rfl) ⟨7608, by rfl⟩ : syracuseStep 324629 = 15217) (by norm_num)
theorem B619589 : Blo 143792 619589 := bbase (se 4 (by rfl) ⟨58086, by rfl⟩ : syracuseStep 619589 = 116173) (by norm_num)
theorem B947285 : Blo 143792 947285 := bbase (se 8 (by rfl) ⟨5550, by rfl⟩ : syracuseStep 947285 = 11101) (by norm_num)
theorem B324701 : Blo 143792 324701 := bbase (se 3 (by rfl) ⟨60881, by rfl⟩ : syracuseStep 324701 = 121763) (by norm_num)
theorem B259205 : Blo 143792 259205 := bbase (se 4 (by rfl) ⟨24300, by rfl⟩ : syracuseStep 259205 = 48601) (by norm_num)
theorem B390277 : Blo 143792 390277 := bbase (se 4 (by rfl) ⟨36588, by rfl⟩ : syracuseStep 390277 = 73177) (by norm_num)
theorem B324773 : Blo 143792 324773 := bbase (se 4 (by rfl) ⟨30447, by rfl⟩ : syracuseStep 324773 = 60895) (by norm_num)
theorem B488645 : Blo 143792 488645 := bbase (se 4 (by rfl) ⟨45810, by rfl⟩ : syracuseStep 488645 = 91621) (by norm_num)
theorem B324845 : Blo 143792 324845 := bbase (se 3 (by rfl) ⟨60908, by rfl⟩ : syracuseStep 324845 = 121817) (by norm_num)
theorem B324917 : Blo 143792 324917 := bbase (se 5 (by rfl) ⟨15230, by rfl⟩ : syracuseStep 324917 = 30461) (by norm_num)
theorem B324989 : Blo 143792 324989 := bbase (se 3 (by rfl) ⟨60935, by rfl⟩ : syracuseStep 324989 = 121871) (by norm_num)
theorem B325061 : Blo 143792 325061 := bbase (se 4 (by rfl) ⟨30474, by rfl⟩ : syracuseStep 325061 = 60949) (by norm_num)
theorem B325133 : Blo 143792 325133 := bbase (se 3 (by rfl) ⟨60962, by rfl⟩ : syracuseStep 325133 = 121925) (by norm_num)
theorem B325205 : Blo 143792 325205 := bbase (se 8 (by rfl) ⟨1905, by rfl⟩ : syracuseStep 325205 = 3811) (by norm_num)
theorem B489077 : Blo 143792 489077 := bbase (se 5 (by rfl) ⟨22925, by rfl⟩ : syracuseStep 489077 = 45851) (by norm_num)
theorem B325277 : Blo 143792 325277 := bbase (se 3 (by rfl) ⟨60989, by rfl⟩ : syracuseStep 325277 = 121979) (by norm_num)
theorem B325349 : Blo 143792 325349 := bbase (se 4 (by rfl) ⟨30501, by rfl⟩ : syracuseStep 325349 = 61003) (by norm_num)
theorem B325421 : Blo 143792 325421 := bbase (se 3 (by rfl) ⟨61016, by rfl⟩ : syracuseStep 325421 = 122033) (by norm_num)
theorem B325493 : Blo 143792 325493 := bbase (se 5 (by rfl) ⟨15257, by rfl⟩ : syracuseStep 325493 = 30515) (by norm_num)
theorem B522101 : Blo 143792 522101 := bbase (se 5 (by rfl) ⟨24473, by rfl⟩ : syracuseStep 522101 = 48947) (by norm_num)
theorem B325565 : Blo 143792 325565 := bbase (se 3 (by rfl) ⟨61043, by rfl⟩ : syracuseStep 325565 = 122087) (by norm_num)
theorem B161797 : Blo 143792 161797 := bbase (se 4 (by rfl) ⟨15168, by rfl⟩ : syracuseStep 161797 = 30337) (by norm_num)
theorem B325637 : Blo 143792 325637 := bbase (se 4 (by rfl) ⟨30528, by rfl⟩ : syracuseStep 325637 = 61057) (by norm_num)
theorem B489509 : Blo 143792 489509 := bbase (se 4 (by rfl) ⟨45891, by rfl⟩ : syracuseStep 489509 = 91783) (by norm_num)
theorem B161833 : Blo 143792 161833 := bbase (se 2 (by rfl) ⟨60687, by rfl⟩ : syracuseStep 161833 = 121375) (by norm_num)
theorem B161869 : Blo 143792 161869 := bbase (se 3 (by rfl) ⟨30350, by rfl⟩ : syracuseStep 161869 = 60701) (by norm_num)
theorem B325709 : Blo 143792 325709 := bbase (se 3 (by rfl) ⟨61070, by rfl⟩ : syracuseStep 325709 = 122141) (by norm_num)
theorem B161905 : Blo 143792 161905 := bbase (se 2 (by rfl) ⟨60714, by rfl⟩ : syracuseStep 161905 = 121429) (by norm_num)
theorem B161941 : Blo 143792 161941 := bbase (se 6 (by rfl) ⟨3795, by rfl⟩ : syracuseStep 161941 = 7591) (by norm_num)
theorem B325781 : Blo 143792 325781 := bbase (se 6 (by rfl) ⟨7635, by rfl⟩ : syracuseStep 325781 = 15271) (by norm_num)
theorem B522389 : Blo 143792 522389 := bbase (se 6 (by rfl) ⟨12243, by rfl⟩ : syracuseStep 522389 = 24487) (by norm_num)
theorem B161977 : Blo 143792 161977 := bbase (se 2 (by rfl) ⟨60741, by rfl⟩ : syracuseStep 161977 = 121483) (by norm_num)
theorem B162013 : Blo 143792 162013 := bbase (se 3 (by rfl) ⟨30377, by rfl⟩ : syracuseStep 162013 = 60755) (by norm_num)
theorem B325853 : Blo 143792 325853 := bbase (se 3 (by rfl) ⟨61097, by rfl⟩ : syracuseStep 325853 = 122195) (by norm_num)
theorem B162049 : Blo 143792 162049 := bbase (se 2 (by rfl) ⟨60768, by rfl⟩ : syracuseStep 162049 = 121537) (by norm_num)
theorem B162085 : Blo 143792 162085 := bbase (se 4 (by rfl) ⟨15195, by rfl⟩ : syracuseStep 162085 = 30391) (by norm_num)
theorem B325925 : Blo 143792 325925 := bbase (se 4 (by rfl) ⟨30555, by rfl⟩ : syracuseStep 325925 = 61111) (by norm_num)
theorem B162121 : Blo 143792 162121 := bbase (se 2 (by rfl) ⟨60795, by rfl⟩ : syracuseStep 162121 = 121591) (by norm_num)
theorem B162157 : Blo 143792 162157 := bbase (se 3 (by rfl) ⟨30404, by rfl⟩ : syracuseStep 162157 = 60809) (by norm_num)
theorem B325997 : Blo 143792 325997 := bbase (se 3 (by rfl) ⟨61124, by rfl⟩ : syracuseStep 325997 = 122249) (by norm_num)
theorem B1177973 : Blo 143792 1177973 := bbase (se 5 (by rfl) ⟨55217, by rfl⟩ : syracuseStep 1177973 = 110435) (by norm_num)
theorem B162193 : Blo 143792 162193 := bbase (se 2 (by rfl) ⟨60822, by rfl⟩ : syracuseStep 162193 = 121645) (by norm_num)
theorem B293285 : Blo 143792 293285 := bbase (se 4 (by rfl) ⟨27495, by rfl⟩ : syracuseStep 293285 = 54991) (by norm_num)
theorem B162229 : Blo 143792 162229 := bbase (se 5 (by rfl) ⟨7604, by rfl⟩ : syracuseStep 162229 = 15209) (by norm_num)
theorem B326069 : Blo 143792 326069 := bbase (se 5 (by rfl) ⟨15284, by rfl⟩ : syracuseStep 326069 = 30569) (by norm_num)
theorem B489941 : Blo 143792 489941 := bbase (se 7 (by rfl) ⟨5741, by rfl⟩ : syracuseStep 489941 = 11483) (by norm_num)
theorem B162265 : Blo 143792 162265 := bbase (se 2 (by rfl) ⟨60849, by rfl⟩ : syracuseStep 162265 = 121699) (by norm_num)
theorem B162301 : Blo 143792 162301 := bbase (se 3 (by rfl) ⟨30431, by rfl⟩ : syracuseStep 162301 = 60863) (by norm_num)
theorem B326141 : Blo 143792 326141 := bbase (se 3 (by rfl) ⟨61151, by rfl⟩ : syracuseStep 326141 = 122303) (by norm_num)
theorem B162337 : Blo 143792 162337 := bbase (se 2 (by rfl) ⟨60876, by rfl⟩ : syracuseStep 162337 = 121753) (by norm_num)
theorem B162373 : Blo 143792 162373 := bbase (se 4 (by rfl) ⟨15222, by rfl⟩ : syracuseStep 162373 = 30445) (by norm_num)
theorem B326213 : Blo 143792 326213 := bbase (se 4 (by rfl) ⟨30582, by rfl⟩ : syracuseStep 326213 = 61165) (by norm_num)
theorem B555605 : Blo 143792 555605 := bbase (se 8 (by rfl) ⟨3255, by rfl⟩ : syracuseStep 555605 = 6511) (by norm_num)
theorem B162409 : Blo 143792 162409 := bbase (se 2 (by rfl) ⟨60903, by rfl⟩ : syracuseStep 162409 = 121807) (by norm_num)
theorem B195205 : Blo 143792 195205 := bbase (se 4 (by rfl) ⟨18300, by rfl⟩ : syracuseStep 195205 = 36601) (by norm_num)
theorem B162445 : Blo 143792 162445 := bbase (se 3 (by rfl) ⟨30458, by rfl⟩ : syracuseStep 162445 = 60917) (by norm_num)
theorem B326285 : Blo 143792 326285 := bbase (se 3 (by rfl) ⟨61178, by rfl⟩ : syracuseStep 326285 = 122357) (by norm_num)
theorem B162481 : Blo 143792 162481 := bbase (se 2 (by rfl) ⟨60930, by rfl⟩ : syracuseStep 162481 = 121861) (by norm_num)
theorem B162517 : Blo 143792 162517 := bbase (se 7 (by rfl) ⟨1904, by rfl⟩ : syracuseStep 162517 = 3809) (by norm_num)
theorem B326357 : Blo 143792 326357 := bbase (se 7 (by rfl) ⟨3824, by rfl⟩ : syracuseStep 326357 = 7649) (by norm_num)
theorem B162553 : Blo 143792 162553 := bbase (se 2 (by rfl) ⟨60957, by rfl⟩ : syracuseStep 162553 = 121915) (by norm_num)
theorem B162589 : Blo 143792 162589 := bbase (se 3 (by rfl) ⟨30485, by rfl⟩ : syracuseStep 162589 = 60971) (by norm_num)
theorem B326429 : Blo 143792 326429 := bbase (se 3 (by rfl) ⟨61205, by rfl⟩ : syracuseStep 326429 = 122411) (by norm_num)
theorem B162625 : Blo 143792 162625 := bbase (se 2 (by rfl) ⟨60984, by rfl⟩ : syracuseStep 162625 = 121969) (by norm_num)
theorem B162661 : Blo 143792 162661 := bbase (se 4 (by rfl) ⟨15249, by rfl⟩ : syracuseStep 162661 = 30499) (by norm_num)
theorem B326501 : Blo 143792 326501 := bbase (se 4 (by rfl) ⟨30609, by rfl⟩ : syracuseStep 326501 = 61219) (by norm_num)
theorem B555893 : Blo 143792 555893 := bbase (se 5 (by rfl) ⟨26057, by rfl⟩ : syracuseStep 555893 = 52115) (by norm_num)
theorem B490373 : Blo 143792 490373 := bbase (se 4 (by rfl) ⟨45972, by rfl⟩ : syracuseStep 490373 = 91945) (by norm_num)
theorem B162697 : Blo 143792 162697 := bbase (se 2 (by rfl) ⟨61011, by rfl⟩ : syracuseStep 162697 = 122023) (by norm_num)
theorem B162733 : Blo 143792 162733 := bbase (se 3 (by rfl) ⟨30512, by rfl⟩ : syracuseStep 162733 = 61025) (by norm_num)
theorem B326573 : Blo 143792 326573 := bbase (se 3 (by rfl) ⟨61232, by rfl⟩ : syracuseStep 326573 = 122465) (by norm_num)
theorem B162769 : Blo 143792 162769 := bbase (se 2 (by rfl) ⟨61038, by rfl⟩ : syracuseStep 162769 = 122077) (by norm_num)
theorem B162805 : Blo 143792 162805 := bbase (se 5 (by rfl) ⟨7631, by rfl⟩ : syracuseStep 162805 = 15263) (by norm_num)
theorem B326645 : Blo 143792 326645 := bbase (se 5 (by rfl) ⟨15311, by rfl⟩ : syracuseStep 326645 = 30623) (by norm_num)
theorem B162841 : Blo 143792 162841 := bbase (se 2 (by rfl) ⟨61065, by rfl⟩ : syracuseStep 162841 = 122131) (by norm_num)
theorem B162877 : Blo 143792 162877 := bbase (se 3 (by rfl) ⟨30539, by rfl⟩ : syracuseStep 162877 = 61079) (by norm_num)
theorem B326717 : Blo 143792 326717 := bbase (se 3 (by rfl) ⟨61259, by rfl⟩ : syracuseStep 326717 = 122519) (by norm_num)
theorem B162913 : Blo 143792 162913 := bbase (se 2 (by rfl) ⟨61092, by rfl⟩ : syracuseStep 162913 = 122185) (by norm_num)
theorem B195701 : Blo 143792 195701 := bbase (se 5 (by rfl) ⟨9173, by rfl⟩ : syracuseStep 195701 = 18347) (by norm_num)
theorem B162949 : Blo 143792 162949 := bbase (se 4 (by rfl) ⟨15276, by rfl⟩ : syracuseStep 162949 = 30553) (by norm_num)
theorem B326789 : Blo 143792 326789 := bbase (se 4 (by rfl) ⟨30636, by rfl⟩ : syracuseStep 326789 = 61273) (by norm_num)
theorem B162985 : Blo 143792 162985 := bbase (se 2 (by rfl) ⟨61119, by rfl⟩ : syracuseStep 162985 = 122239) (by norm_num)
theorem B163021 : Blo 143792 163021 := bbase (se 3 (by rfl) ⟨30566, by rfl⟩ : syracuseStep 163021 = 61133) (by norm_num)
theorem B326861 : Blo 143792 326861 := bbase (se 3 (by rfl) ⟨61286, by rfl⟩ : syracuseStep 326861 = 122573) (by norm_num)
theorem B163057 : Blo 143792 163057 := bbase (se 2 (by rfl) ⟨61146, by rfl⟩ : syracuseStep 163057 = 122293) (by norm_num)
theorem B163093 : Blo 143792 163093 := bbase (se 6 (by rfl) ⟨3822, by rfl⟩ : syracuseStep 163093 = 7645) (by norm_num)
theorem B326933 : Blo 143792 326933 := bbase (se 6 (by rfl) ⟨7662, by rfl⟩ : syracuseStep 326933 = 15325) (by norm_num)
theorem B490805 : Blo 143792 490805 := bbase (se 5 (by rfl) ⟨23006, by rfl⟩ : syracuseStep 490805 = 46013) (by norm_num)
theorem B163129 : Blo 143792 163129 := bbase (se 2 (by rfl) ⟨61173, by rfl⟩ : syracuseStep 163129 = 122347) (by norm_num)
theorem B163165 : Blo 143792 163165 := bbase (se 3 (by rfl) ⟨30593, by rfl⟩ : syracuseStep 163165 = 61187) (by norm_num)
theorem B327005 : Blo 143792 327005 := bbase (se 3 (by rfl) ⟨61313, by rfl⟩ : syracuseStep 327005 = 122627) (by norm_num)
theorem B163201 : Blo 143792 163201 := bbase (se 2 (by rfl) ⟨61200, by rfl⟩ : syracuseStep 163201 = 122401) (by norm_num)
theorem B163237 : Blo 143792 163237 := bbase (se 4 (by rfl) ⟨15303, by rfl⟩ : syracuseStep 163237 = 30607) (by norm_num)
theorem B327077 : Blo 143792 327077 := bbase (se 4 (by rfl) ⟨30663, by rfl⟩ : syracuseStep 327077 = 61327) (by norm_num)
theorem B163273 : Blo 143792 163273 := bbase (se 2 (by rfl) ⟨61227, by rfl⟩ : syracuseStep 163273 = 122455) (by norm_num)
theorem B163309 : Blo 143792 163309 := bbase (se 3 (by rfl) ⟨30620, by rfl⟩ : syracuseStep 163309 = 61241) (by norm_num)
theorem B327149 : Blo 143792 327149 := bbase (se 3 (by rfl) ⟨61340, by rfl⟩ : syracuseStep 327149 = 122681) (by norm_num)
theorem B163345 : Blo 143792 163345 := bbase (se 2 (by rfl) ⟨61254, by rfl⟩ : syracuseStep 163345 = 122509) (by norm_num)
theorem B163381 : Blo 143792 163381 := bbase (se 5 (by rfl) ⟨7658, by rfl⟩ : syracuseStep 163381 = 15317) (by norm_num)
theorem B327221 : Blo 143792 327221 := bbase (se 5 (by rfl) ⟨15338, by rfl⟩ : syracuseStep 327221 = 30677) (by norm_num)
theorem B1408565 : Blo 143792 1408565 := bbase (se 5 (by rfl) ⟨66026, by rfl⟩ : syracuseStep 1408565 = 132053) (by norm_num)
theorem B163417 : Blo 143792 163417 := bbase (se 2 (by rfl) ⟨61281, by rfl⟩ : syracuseStep 163417 = 122563) (by norm_num)
theorem B163453 : Blo 143792 163453 := bbase (se 3 (by rfl) ⟨30647, by rfl⟩ : syracuseStep 163453 = 61295) (by norm_num)
theorem B327293 : Blo 143792 327293 := bbase (se 3 (by rfl) ⟨61367, by rfl⟩ : syracuseStep 327293 = 122735) (by norm_num)
theorem B163489 : Blo 143792 163489 := bbase (se 2 (by rfl) ⟨61308, by rfl⟩ : syracuseStep 163489 = 122617) (by norm_num)
theorem B163525 : Blo 143792 163525 := bbase (se 4 (by rfl) ⟨15330, by rfl⟩ : syracuseStep 163525 = 30661) (by norm_num)
theorem B327365 : Blo 143792 327365 := bbase (se 4 (by rfl) ⟨30690, by rfl⟩ : syracuseStep 327365 = 61381) (by norm_num)
theorem B491237 : Blo 143792 491237 := bbase (se 4 (by rfl) ⟨46053, by rfl⟩ : syracuseStep 491237 = 92107) (by norm_num)
theorem B163561 : Blo 143792 163561 := bbase (se 2 (by rfl) ⟨61335, by rfl⟩ : syracuseStep 163561 = 122671) (by norm_num)
theorem B163597 : Blo 143792 163597 := bbase (se 3 (by rfl) ⟨30674, by rfl⟩ : syracuseStep 163597 = 61349) (by norm_num)
theorem B327437 : Blo 143792 327437 := bbase (se 3 (by rfl) ⟨61394, by rfl⟩ : syracuseStep 327437 = 122789) (by norm_num)
theorem B163633 : Blo 143792 163633 := bbase (se 2 (by rfl) ⟨61362, by rfl⟩ : syracuseStep 163633 = 122725) (by norm_num)
theorem B1408853 : Blo 143792 1408853 := bbase (se 9 (by rfl) ⟨4127, by rfl⟩ : syracuseStep 1408853 = 8255) (by norm_num)
theorem B163669 : Blo 143792 163669 := bbase (se 9 (by rfl) ⟨479, by rfl⟩ : syracuseStep 163669 = 959) (by norm_num)
theorem B327509 : Blo 143792 327509 := bbase (se 9 (by rfl) ⟨959, by rfl⟩ : syracuseStep 327509 = 1919) (by norm_num)
theorem B163705 : Blo 143792 163705 := bbase (se 2 (by rfl) ⟨61389, by rfl⟩ : syracuseStep 163705 = 122779) (by norm_num)
theorem B163741 : Blo 143792 163741 := bbase (se 3 (by rfl) ⟨30701, by rfl⟩ : syracuseStep 163741 = 61403) (by norm_num)
theorem B327581 : Blo 143792 327581 := bbase (se 3 (by rfl) ⟨61421, by rfl⟩ : syracuseStep 327581 = 122843) (by norm_num)
theorem B163777 : Blo 143792 163777 := bbase (se 2 (by rfl) ⟨61416, by rfl⟩ : syracuseStep 163777 = 122833) (by norm_num)
theorem B163813 : Blo 143792 163813 := bbase (se 4 (by rfl) ⟨15357, by rfl⟩ : syracuseStep 163813 = 30715) (by norm_num)
theorem B327653 : Blo 143792 327653 := bbase (se 4 (by rfl) ⟨30717, by rfl⟩ : syracuseStep 327653 = 61435) (by norm_num)
theorem B327761 : Blo 143792 327761 := bstep (se 2 (by rfl) ⟨122910, by rfl⟩ : syracuseStep 327761 = 245821) B245821
theorem B327779 : Blo 143792 327779 := bstep (se 1 (by rfl) ⟨245834, by rfl⟩ : syracuseStep 327779 = 491669) B491669
theorem B163939 : Blo 143792 163939 := bstep (se 1 (by rfl) ⟨122954, by rfl⟩ : syracuseStep 163939 = 245909) B245909
theorem B524465 : Blo 143792 524465 := bstep (se 2 (by rfl) ⟨196674, by rfl⟩ : syracuseStep 524465 = 393349) B393349
theorem B164083 : Blo 143792 164083 := bstep (se 1 (by rfl) ⟨123062, by rfl⟩ : syracuseStep 164083 = 246125) B246125
theorem B262435 : Blo 143792 262435 := bstep (se 1 (by rfl) ⟨196826, by rfl⟩ : syracuseStep 262435 = 393653) B393653
theorem B491885 : Blo 143792 491885 := bstep (se 3 (by rfl) ⟨92228, by rfl⟩ : syracuseStep 491885 = 184457) B184457
theorem B328049 : Blo 143792 328049 := bstep (se 2 (by rfl) ⟨123018, by rfl⟩ : syracuseStep 328049 = 246037) B246037
theorem B328067 : Blo 143792 328067 := bstep (se 1 (by rfl) ⟨246050, by rfl⟩ : syracuseStep 328067 = 492101) B492101
theorem B164227 : Blo 143792 164227 := bstep (se 1 (by rfl) ⟨123170, by rfl⟩ : syracuseStep 164227 = 246341) B246341
theorem B164243 : Blo 143792 164243 := bstep (se 1 (by rfl) ⟨123182, by rfl⟩ : syracuseStep 164243 = 246365) B246365
theorem B491939 : Blo 143792 491939 := bstep (se 1 (by rfl) ⟨368954, by rfl⟩ : syracuseStep 491939 = 737909) B737909
theorem B164371 : Blo 143792 164371 := bstep (se 1 (by rfl) ⟨123278, by rfl⟩ : syracuseStep 164371 = 246557) B246557
theorem B262723 : Blo 143792 262723 := bstep (se 1 (by rfl) ⟨197042, by rfl⟩ : syracuseStep 262723 = 394085) B394085
theorem B328337 : Blo 143792 328337 := bstep (se 2 (by rfl) ⟨123126, by rfl⟩ : syracuseStep 328337 = 246253) B246253
theorem B328355 : Blo 143792 328355 := bstep (se 1 (by rfl) ⟨246266, by rfl⟩ : syracuseStep 328355 = 492533) B492533
theorem B164515 : Blo 143792 164515 := bstep (se 1 (by rfl) ⟨123386, by rfl⟩ : syracuseStep 164515 = 246773) B246773
theorem B492209 : Blo 143792 492209 := bstep (se 2 (by rfl) ⟨184578, by rfl⟩ : syracuseStep 492209 = 369157) B369157
theorem B328387 : Blo 143792 328387 := bstep (se 1 (by rfl) ⟨246290, by rfl⟩ : syracuseStep 328387 = 492581) B492581
theorem B557837 : Blo 143792 557837 := bstep (se 3 (by rfl) ⟨104594, by rfl⟩ : syracuseStep 557837 = 209189) B209189
theorem B164659 : Blo 143792 164659 := bstep (se 1 (by rfl) ⟨123494, by rfl⟩ : syracuseStep 164659 = 246989) B246989
theorem B623501 : Blo 143792 623501 := bstep (se 3 (by rfl) ⟨116906, by rfl⟩ : syracuseStep 623501 = 233813) B233813
theorem B328625 : Blo 143792 328625 := bstep (se 2 (by rfl) ⟨123234, by rfl⟩ : syracuseStep 328625 = 246469) B246469
theorem B328643 : Blo 143792 328643 := bstep (se 1 (by rfl) ⟨246482, by rfl⟩ : syracuseStep 328643 = 492965) B492965
theorem B164803 : Blo 143792 164803 := bstep (se 1 (by rfl) ⟨123602, by rfl⟩ : syracuseStep 164803 = 247205) B247205
theorem B164947 : Blo 143792 164947 := bstep (se 1 (by rfl) ⟨123710, by rfl⟩ : syracuseStep 164947 = 247421) B247421
theorem B263299 : Blo 143792 263299 := bstep (se 1 (by rfl) ⟨197474, by rfl⟩ : syracuseStep 263299 = 394949) B394949
theorem B492749 : Blo 143792 492749 := bstep (se 3 (by rfl) ⟨92390, by rfl⟩ : syracuseStep 492749 = 184781) B184781
theorem B328913 : Blo 143792 328913 := bstep (se 2 (by rfl) ⟨123342, by rfl⟩ : syracuseStep 328913 = 246685) B246685
theorem B328931 : Blo 143792 328931 := bstep (se 1 (by rfl) ⟨246698, by rfl⟩ : syracuseStep 328931 = 493397) B493397
theorem B165091 : Blo 143792 165091 := bstep (se 1 (by rfl) ⟨123818, by rfl⟩ : syracuseStep 165091 = 247637) B247637
theorem B1672433 : Blo 143792 1672433 := bstep (se 2 (by rfl) ⟨627162, by rfl⟩ : syracuseStep 1672433 = 1254325) B1254325
theorem B492803 : Blo 143792 492803 := bstep (se 1 (by rfl) ⟨369602, by rfl⟩ : syracuseStep 492803 = 739205) B739205
theorem B886085 : Blo 143792 886085 := bstep (se 4 (by rfl) ⟨83070, by rfl⟩ : syracuseStep 886085 = 166141) B166141
theorem B165235 : Blo 143792 165235 := bstep (se 1 (by rfl) ⟨123926, by rfl⟩ : syracuseStep 165235 = 247853) B247853
theorem B394733 : Blo 143792 394733 := bstep (se 3 (by rfl) ⟨74012, by rfl⟩ : syracuseStep 394733 = 148025) B148025
theorem B329201 : Blo 143792 329201 := bstep (se 2 (by rfl) ⟨123450, by rfl⟩ : syracuseStep 329201 = 246901) B246901
theorem B329219 : Blo 143792 329219 := bstep (se 1 (by rfl) ⟨246914, by rfl⟩ : syracuseStep 329219 = 493829) B493829
theorem B165379 : Blo 143792 165379 := bstep (se 1 (by rfl) ⟨124034, by rfl⟩ : syracuseStep 165379 = 248069) B248069
theorem B493073 : Blo 143792 493073 := bstep (se 2 (by rfl) ⟨184902, by rfl⟩ : syracuseStep 493073 = 369805) B369805
theorem B165523 : Blo 143792 165523 := bstep (se 1 (by rfl) ⟨124142, by rfl⟩ : syracuseStep 165523 = 248285) B248285
theorem B394993 : Blo 143792 394993 := bstep (se 2 (by rfl) ⟨148122, by rfl⟩ : syracuseStep 394993 = 296245) B296245
theorem B329489 : Blo 143792 329489 := bstep (se 2 (by rfl) ⟨123558, by rfl⟩ : syracuseStep 329489 = 247117) B247117
theorem B329507 : Blo 143792 329507 := bstep (se 1 (by rfl) ⟨247130, by rfl⟩ : syracuseStep 329507 = 494261) B494261
theorem B165667 : Blo 143792 165667 := bstep (se 1 (by rfl) ⟨124250, by rfl⟩ : syracuseStep 165667 = 248501) B248501
theorem B165811 : Blo 143792 165811 := bstep (se 1 (by rfl) ⟨124358, by rfl⟩ : syracuseStep 165811 = 248717) B248717
theorem B460835 : Blo 143792 460835 := bstep (se 1 (by rfl) ⟨345626, by rfl⟩ : syracuseStep 460835 = 691253) B691253
theorem B493613 : Blo 143792 493613 := bstep (se 3 (by rfl) ⟨92552, by rfl⟩ : syracuseStep 493613 = 185105) B185105
theorem B329777 : Blo 143792 329777 := bstep (se 2 (by rfl) ⟨123666, by rfl⟩ : syracuseStep 329777 = 247333) B247333
theorem B329795 : Blo 143792 329795 := bstep (se 1 (by rfl) ⟨247346, by rfl⟩ : syracuseStep 329795 = 494693) B494693
theorem B165955 : Blo 143792 165955 := bstep (se 1 (by rfl) ⟨124466, by rfl⟩ : syracuseStep 165955 = 248933) B248933
theorem B493667 : Blo 143792 493667 := bstep (se 1 (by rfl) ⟨370250, by rfl⟩ : syracuseStep 493667 = 740501) B740501
theorem B526513 : Blo 143792 526513 := bstep (se 2 (by rfl) ⟨197442, by rfl⟩ : syracuseStep 526513 = 394885) B394885
theorem B231635 : Blo 143792 231635 := bstep (se 1 (by rfl) ⟨173726, by rfl⟩ : syracuseStep 231635 = 347453) B347453
theorem B166099 : Blo 143792 166099 := bstep (se 1 (by rfl) ⟨124574, by rfl⟩ : syracuseStep 166099 = 249149) B249149
theorem B330065 : Blo 143792 330065 := bstep (se 2 (by rfl) ⟨123774, by rfl⟩ : syracuseStep 330065 = 247549) B247549
theorem B231763 : Blo 143792 231763 := bstep (se 1 (by rfl) ⟨173822, by rfl⟩ : syracuseStep 231763 = 347645) B347645
theorem B330083 : Blo 143792 330083 := bstep (se 1 (by rfl) ⟨247562, by rfl⟩ : syracuseStep 330083 = 495125) B495125
theorem B166243 : Blo 143792 166243 := bstep (se 1 (by rfl) ⟨124682, by rfl⟩ : syracuseStep 166243 = 249365) B249365
theorem B493937 : Blo 143792 493937 := bstep (se 2 (by rfl) ⟨185226, by rfl⟩ : syracuseStep 493937 = 370453) B370453
theorem B297379 : Blo 143792 297379 := bstep (se 1 (by rfl) ⟨223034, by rfl⟩ : syracuseStep 297379 = 446069) B446069
theorem B395729 : Blo 143792 395729 := bstep (se 2 (by rfl) ⟨148398, by rfl⟩ : syracuseStep 395729 = 296797) B296797
theorem B821765 : Blo 143792 821765 := bstep (se 4 (by rfl) ⟨77040, by rfl⟩ : syracuseStep 821765 = 154081) B154081
theorem B330353 : Blo 143792 330353 := bstep (se 2 (by rfl) ⟨123882, by rfl⟩ : syracuseStep 330353 = 247765) B247765
theorem B330371 : Blo 143792 330371 := bstep (se 1 (by rfl) ⟨247778, by rfl⟩ : syracuseStep 330371 = 495557) B495557
theorem B232147 : Blo 143792 232147 := bstep (se 1 (by rfl) ⟨174110, by rfl⟩ : syracuseStep 232147 = 348221) B348221
theorem B1575733 : Blo 143792 1575733 := bstep (se 5 (by rfl) ⟨73862, by rfl⟩ : syracuseStep 1575733 = 147725) B147725
theorem B199507 : Blo 143792 199507 := bstep (se 1 (by rfl) ⟨149630, by rfl⟩ : syracuseStep 199507 = 299261) B299261
theorem B494477 : Blo 143792 494477 := bstep (se 3 (by rfl) ⟨92714, by rfl⟩ : syracuseStep 494477 = 185429) B185429
theorem B330641 : Blo 143792 330641 := bstep (se 2 (by rfl) ⟨123990, by rfl⟩ : syracuseStep 330641 = 247981) B247981
theorem B330659 : Blo 143792 330659 := bstep (se 1 (by rfl) ⟨247994, by rfl⟩ : syracuseStep 330659 = 495989) B495989
theorem B789425 : Blo 143792 789425 := bstep (se 2 (by rfl) ⟨296034, by rfl⟩ : syracuseStep 789425 = 592069) B592069
theorem B494531 : Blo 143792 494531 := bstep (se 1 (by rfl) ⟨370898, by rfl⟩ : syracuseStep 494531 = 741797) B741797
theorem B822221 : Blo 143792 822221 := bstep (se 3 (by rfl) ⟨154166, by rfl⟩ : syracuseStep 822221 = 308333) B308333
theorem B232403 : Blo 143792 232403 := bstep (se 1 (by rfl) ⟨174302, by rfl⟩ : syracuseStep 232403 = 348605) B348605
theorem B396269 : Blo 143792 396269 := bstep (se 3 (by rfl) ⟨74300, by rfl⟩ : syracuseStep 396269 = 148601) B148601
theorem B691213 : Blo 143792 691213 := bstep (se 3 (by rfl) ⟨129602, by rfl⟩ : syracuseStep 691213 = 259205) B259205
theorem B330929 : Blo 143792 330929 := bstep (se 2 (by rfl) ⟨124098, by rfl⟩ : syracuseStep 330929 = 248197) B248197
theorem B330947 : Blo 143792 330947 := bstep (se 1 (by rfl) ⟨248210, by rfl⟩ : syracuseStep 330947 = 496421) B496421
theorem B494801 : Blo 143792 494801 := bstep (se 2 (by rfl) ⟨185550, by rfl⟩ : syracuseStep 494801 = 371101) B371101
theorem B396497 : Blo 143792 396497 := bstep (se 2 (by rfl) ⟨148686, by rfl⟩ : syracuseStep 396497 = 297373) B297373
theorem B167203 : Blo 143792 167203 := bstep (se 1 (by rfl) ⟨125402, by rfl⟩ : syracuseStep 167203 = 250805) B250805
theorem B593201 : Blo 143792 593201 := bstep (se 2 (by rfl) ⟨222450, by rfl⟩ : syracuseStep 593201 = 444901) B444901
theorem B232865 : Blo 143792 232865 := bstep (se 2 (by rfl) ⟨87324, by rfl⟩ : syracuseStep 232865 = 174649) B174649
theorem B331217 : Blo 143792 331217 := bstep (se 2 (by rfl) ⟨124206, by rfl⟩ : syracuseStep 331217 = 248413) B248413
theorem B167395 : Blo 143792 167395 := bstep (se 1 (by rfl) ⟨125546, by rfl⟩ : syracuseStep 167395 = 251093) B251093
theorem B331235 : Blo 143792 331235 := bstep (se 1 (by rfl) ⟨248426, by rfl⟩ : syracuseStep 331235 = 496853) B496853
theorem B232961 : Blo 143792 232961 := bstep (se 2 (by rfl) ⟨87360, by rfl⟩ : syracuseStep 232961 = 174721) B174721
theorem B232993 : Blo 143792 232993 := bstep (se 2 (by rfl) ⟨87372, by rfl⟩ : syracuseStep 232993 = 174745) B174745
theorem B691811 : Blo 143792 691811 := bstep (se 1 (by rfl) ⟨518858, by rfl⟩ : syracuseStep 691811 = 1037717) B1037717
theorem B462449 : Blo 143792 462449 := bstep (se 2 (by rfl) ⟨173418, by rfl⟩ : syracuseStep 462449 = 346837) B346837
theorem B560753 : Blo 143792 560753 := bstep (se 2 (by rfl) ⟨210282, by rfl⟩ : syracuseStep 560753 = 420565) B420565
theorem B790157 : Blo 143792 790157 := bstep (se 3 (by rfl) ⟨148154, by rfl⟩ : syracuseStep 790157 = 296309) B296309
theorem B659107 : Blo 143792 659107 := bstep (se 1 (by rfl) ⟨494330, by rfl⟩ : syracuseStep 659107 = 988661) B988661
theorem B495341 : Blo 143792 495341 := bstep (se 3 (by rfl) ⟨92876, by rfl⟩ : syracuseStep 495341 = 185753) B185753
theorem B331505 : Blo 143792 331505 := bstep (se 2 (by rfl) ⟨124314, by rfl⟩ : syracuseStep 331505 = 248629) B248629
theorem B331523 : Blo 143792 331523 := bstep (se 1 (by rfl) ⟨248642, by rfl⟩ : syracuseStep 331523 = 497285) B497285
theorem B495395 : Blo 143792 495395 := bstep (se 1 (by rfl) ⟨371546, by rfl⟩ : syracuseStep 495395 = 743093) B743093
theorem B331793 : Blo 143792 331793 := bstep (se 2 (by rfl) ⟨124422, by rfl⟩ : syracuseStep 331793 = 248845) B248845
theorem B331811 : Blo 143792 331811 := bstep (se 1 (by rfl) ⟨248858, by rfl⟩ : syracuseStep 331811 = 497717) B497717
theorem B495665 : Blo 143792 495665 := bstep (se 2 (by rfl) ⟨185874, by rfl⟩ : syracuseStep 495665 = 371749) B371749
theorem B332081 : Blo 143792 332081 := bstep (se 2 (by rfl) ⟨124530, by rfl⟩ : syracuseStep 332081 = 249061) B249061
theorem B332099 : Blo 143792 332099 := bstep (se 1 (by rfl) ⟨249074, by rfl⟩ : syracuseStep 332099 = 498149) B498149
theorem B364945 : Blo 143792 364945 := bstep (se 2 (by rfl) ⟨136854, by rfl⟩ : syracuseStep 364945 = 273709) B273709
theorem B332209 : Blo 143792 332209 := bstep (se 2 (by rfl) ⟨124578, by rfl⟩ : syracuseStep 332209 = 249157) B249157
theorem B496205 : Blo 143792 496205 := bstep (se 3 (by rfl) ⟨93038, by rfl⟩ : syracuseStep 496205 = 186077) B186077
theorem B332369 : Blo 143792 332369 := bstep (se 2 (by rfl) ⟨124638, by rfl⟩ : syracuseStep 332369 = 249277) B249277
theorem B1053283 : Blo 143792 1053283 := bstep (se 1 (by rfl) ⟨789962, by rfl⟩ : syracuseStep 1053283 = 1579925) B1579925
theorem B332387 : Blo 143792 332387 := bstep (se 1 (by rfl) ⟨249290, by rfl⟩ : syracuseStep 332387 = 498581) B498581
theorem B496259 : Blo 143792 496259 := bstep (se 1 (by rfl) ⟨372194, by rfl⟩ : syracuseStep 496259 = 744389) B744389
theorem B365219 : Blo 143792 365219 := bstep (se 1 (by rfl) ⟨273914, by rfl⟩ : syracuseStep 365219 = 547829) B547829
theorem B627533 : Blo 143792 627533 := bstep (se 3 (by rfl) ⟨117662, by rfl⟩ : syracuseStep 627533 = 235325) B235325
theorem B365411 : Blo 143792 365411 := bstep (se 1 (by rfl) ⟨274058, by rfl⟩ : syracuseStep 365411 = 548117) B548117
theorem B496493 : Blo 143792 496493 := bstep (se 3 (by rfl) ⟨93092, by rfl⟩ : syracuseStep 496493 = 186185) B186185
theorem B496529 : Blo 143792 496529 := bstep (se 2 (by rfl) ⟨186198, by rfl⟩ : syracuseStep 496529 = 372397) B372397
theorem B1250417 : Blo 143792 1250417 := bstep (se 2 (by rfl) ⟨468906, by rfl⟩ : syracuseStep 1250417 = 937813) B937813
theorem B2823281 : Blo 143792 2823281 := bstep (se 2 (by rfl) ⟨1058730, by rfl⟩ : syracuseStep 2823281 = 2117461) B2117461
theorem B234659 : Blo 143792 234659 := bstep (se 1 (by rfl) ⟨175994, by rfl⟩ : syracuseStep 234659 = 351989) B351989
theorem B627875 : Blo 143792 627875 := bstep (se 1 (by rfl) ⟨470906, by rfl⟩ : syracuseStep 627875 = 941813) B941813
theorem B1873165 : Blo 143792 1873165 := bstep (se 3 (by rfl) ⟨351218, by rfl⟩ : syracuseStep 1873165 = 702437) B702437
theorem B529699 : Blo 143792 529699 := bstep (se 1 (by rfl) ⟨397274, by rfl⟩ : syracuseStep 529699 = 794549) B794549
theorem B497069 : Blo 143792 497069 := bstep (se 3 (by rfl) ⟨93200, by rfl⟩ : syracuseStep 497069 = 186401) B186401
theorem B497123 : Blo 143792 497123 := bstep (se 1 (by rfl) ⟨372842, by rfl⟩ : syracuseStep 497123 = 745685) B745685
theorem B628337 : Blo 143792 628337 := bstep (se 2 (by rfl) ⟨235626, by rfl⟩ : syracuseStep 628337 = 471253) B471253
theorem B464525 : Blo 143792 464525 := bstep (se 3 (by rfl) ⟨87098, by rfl⟩ : syracuseStep 464525 = 174197) B174197
theorem B235171 : Blo 143792 235171 := bstep (se 1 (by rfl) ⟨176378, by rfl⟩ : syracuseStep 235171 = 352757) B352757
theorem B235217 : Blo 143792 235217 := bstep (se 2 (by rfl) ⟨88206, by rfl⟩ : syracuseStep 235217 = 176413) B176413
theorem B1119971 : Blo 143792 1119971 := bstep (se 1 (by rfl) ⟨839978, by rfl⟩ : syracuseStep 1119971 = 1679957) B1679957
theorem B497393 : Blo 143792 497393 := bstep (se 2 (by rfl) ⟨186522, by rfl⟩ : syracuseStep 497393 = 373045) B373045
theorem B366353 : Blo 143792 366353 := bstep (se 2 (by rfl) ⟨137382, by rfl⟩ : syracuseStep 366353 = 274765) B274765
theorem B825137 : Blo 143792 825137 := bstep (se 2 (by rfl) ⟨309426, by rfl⟩ : syracuseStep 825137 = 618853) B618853
theorem B366403 : Blo 143792 366403 := bstep (se 1 (by rfl) ⟨274802, by rfl⟩ : syracuseStep 366403 = 549605) B549605
theorem B366545 : Blo 143792 366545 := bstep (se 2 (by rfl) ⟨137454, by rfl⟩ : syracuseStep 366545 = 274909) B274909
theorem B2398349 : Blo 143792 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B497933 : Blo 143792 497933 := bstep (se 3 (by rfl) ⟨93362, by rfl⟩ : syracuseStep 497933 = 186725) B186725
theorem B497987 : Blo 143792 497987 := bstep (se 1 (by rfl) ⟨373490, by rfl⟩ : syracuseStep 497987 = 746981) B746981
theorem B235889 : Blo 143792 235889 := bstep (se 2 (by rfl) ⟨88458, by rfl⟩ : syracuseStep 235889 = 176917) B176917
theorem B1612229 : Blo 143792 1612229 := bstep (se 4 (by rfl) ⟨151146, by rfl⟩ : syracuseStep 1612229 = 302293) B302293
theorem B465421 : Blo 143792 465421 := bstep (se 3 (by rfl) ⟨87266, by rfl⟩ : syracuseStep 465421 = 174533) B174533
theorem B1874501 : Blo 143792 1874501 := bstep (se 4 (by rfl) ⟨175734, by rfl⟩ : syracuseStep 1874501 = 351469) B351469
theorem B498257 : Blo 143792 498257 := bstep (se 2 (by rfl) ⟨186846, by rfl⟩ : syracuseStep 498257 = 373693) B373693
theorem B596771 : Blo 143792 596771 := bstep (se 1 (by rfl) ⟨447578, by rfl⟩ : syracuseStep 596771 = 895157) B895157
theorem B498545 : Blo 143792 498545 := bstep (se 2 (by rfl) ⟨186954, by rfl⟩ : syracuseStep 498545 = 373909) B373909
theorem B236401 : Blo 143792 236401 := bstep (se 2 (by rfl) ⟨88650, by rfl⟩ : syracuseStep 236401 = 177301) B177301
theorem B367537 : Blo 143792 367537 := bstep (se 2 (by rfl) ⟨137826, by rfl⟩ : syracuseStep 367537 = 275653) B275653
theorem B498797 : Blo 143792 498797 := bstep (se 3 (by rfl) ⟨93524, by rfl⟩ : syracuseStep 498797 = 187049) B187049
theorem B367811 : Blo 143792 367811 := bstep (se 1 (by rfl) ⟨275858, by rfl⟩ : syracuseStep 367811 = 551717) B551717
theorem B826595 : Blo 143792 826595 := bstep (se 1 (by rfl) ⟨619946, by rfl⟩ : syracuseStep 826595 = 1239893) B1239893
theorem B368003 : Blo 143792 368003 := bstep (se 1 (by rfl) ⟨276002, by rfl⟩ : syracuseStep 368003 = 552005) B552005
theorem B466499 : Blo 143792 466499 := bstep (se 1 (by rfl) ⟨349874, by rfl⟩ : syracuseStep 466499 = 699749) B699749
theorem B728675 : Blo 143792 728675 := bstep (se 1 (by rfl) ⟨546506, by rfl⟩ : syracuseStep 728675 = 1093013) B1093013
theorem B925283 : Blo 143792 925283 := bstep (se 1 (by rfl) ⟨693962, by rfl⟩ : syracuseStep 925283 = 1387925) B1387925
theorem B892529 : Blo 143792 892529 := bstep (se 2 (by rfl) ⟨334698, by rfl⟩ : syracuseStep 892529 = 669397) B669397
theorem B1187569 : Blo 143792 1187569 := bstep (se 2 (by rfl) ⟨445338, by rfl⟩ : syracuseStep 1187569 = 890677) B890677
theorem B761827 : Blo 143792 761827 := bstep (se 1 (by rfl) ⟨571370, by rfl⟩ : syracuseStep 761827 = 1142741) B1142741
theorem B827597 : Blo 143792 827597 := bstep (se 3 (by rfl) ⟨155174, by rfl⟩ : syracuseStep 827597 = 310349) B310349
theorem B467153 : Blo 143792 467153 := bstep (se 2 (by rfl) ⟨175182, by rfl⟩ : syracuseStep 467153 = 350365) B350365
theorem B368945 : Blo 143792 368945 := bstep (se 2 (by rfl) ⟨138354, by rfl⟩ : syracuseStep 368945 = 276709) B276709
theorem B368995 : Blo 143792 368995 := bstep (se 1 (by rfl) ⟨276746, by rfl⟩ : syracuseStep 368995 = 553493) B553493
theorem B1188209 : Blo 143792 1188209 := bstep (se 2 (by rfl) ⟨445578, by rfl⟩ : syracuseStep 1188209 = 891157) B891157
theorem B729485 : Blo 143792 729485 := bstep (se 3 (by rfl) ⟨136778, by rfl⟩ : syracuseStep 729485 = 273557) B273557
theorem B565667 : Blo 143792 565667 := bstep (se 1 (by rfl) ⟨424250, by rfl⟩ : syracuseStep 565667 = 848501) B848501
theorem B369137 : Blo 143792 369137 := bstep (se 2 (by rfl) ⟨138426, by rfl⟩ : syracuseStep 369137 = 276853) B276853
theorem B205345 : Blo 143792 205345 := bstep (se 2 (by rfl) ⟨77004, by rfl⟩ : syracuseStep 205345 = 154009) B154009
theorem B631523 : Blo 143792 631523 := bstep (se 1 (by rfl) ⟨473642, by rfl⟩ : syracuseStep 631523 = 947285) B947285
theorem B205681 : Blo 143792 205681 := bstep (se 2 (by rfl) ⟨77130, by rfl⟩ : syracuseStep 205681 = 154261) B154261
theorem B664433 : Blo 143792 664433 := bstep (se 2 (by rfl) ⟨249162, by rfl⟩ : syracuseStep 664433 = 498325) B498325
theorem B467981 : Blo 143792 467981 := bstep (se 3 (by rfl) ⟨87746, by rfl⟩ : syracuseStep 467981 = 175493) B175493
theorem B206273 : Blo 143792 206273 := bstep (se 2 (by rfl) ⟨77352, by rfl⟩ : syracuseStep 206273 = 154705) B154705
theorem B370129 : Blo 143792 370129 := bstep (se 2 (by rfl) ⟨138798, by rfl⟩ : syracuseStep 370129 = 277597) B277597
theorem B468497 : Blo 143792 468497 := bstep (se 2 (by rfl) ⟨175686, by rfl⟩ : syracuseStep 468497 = 351373) B351373
theorem B927409 : Blo 143792 927409 := bstep (se 2 (by rfl) ⟨347778, by rfl⟩ : syracuseStep 927409 = 695557) B695557
theorem B1058501 : Blo 143792 1058501 := bstep (se 4 (by rfl) ⟨99234, by rfl⟩ : syracuseStep 1058501 = 198469) B198469
theorem B370403 : Blo 143792 370403 := bstep (se 1 (by rfl) ⟨277802, by rfl⟩ : syracuseStep 370403 = 555605) B555605
theorem B337745 : Blo 143792 337745 := bstep (se 2 (by rfl) ⟨126654, by rfl⟩ : syracuseStep 337745 = 253309) B253309
theorem B239473 : Blo 143792 239473 := bstep (se 2 (by rfl) ⟨89802, by rfl⟩ : syracuseStep 239473 = 179605) B179605
theorem B370595 : Blo 143792 370595 := bstep (se 1 (by rfl) ⟨277946, by rfl⟩ : syracuseStep 370595 = 555893) B555893
theorem B206803 : Blo 143792 206803 := bstep (se 1 (by rfl) ⟨155102, by rfl⟩ : syracuseStep 206803 = 310205) B310205
theorem B207139 : Blo 143792 207139 := bstep (se 1 (by rfl) ⟨155354, by rfl⟩ : syracuseStep 207139 = 310709) B310709
theorem B469613 : Blo 143792 469613 := bstep (se 3 (by rfl) ⟨88052, by rfl⟩ : syracuseStep 469613 = 176105) B176105
theorem B273041 : Blo 143792 273041 := bstep (se 2 (by rfl) ⟨102390, by rfl⟩ : syracuseStep 273041 = 204781) B204781
theorem B207697 : Blo 143792 207697 := bstep (se 2 (by rfl) ⟨77886, by rfl⟩ : syracuseStep 207697 = 155773) B155773
theorem B371537 : Blo 143792 371537 := bstep (se 2 (by rfl) ⟨139326, by rfl⟩ : syracuseStep 371537 = 278653) B278653
theorem B207731 : Blo 143792 207731 := bstep (se 1 (by rfl) ⟨155798, by rfl⟩ : syracuseStep 207731 = 311597) B311597
theorem B371587 : Blo 143792 371587 := bstep (se 1 (by rfl) ⟨278690, by rfl⟩ : syracuseStep 371587 = 557381) B557381
theorem B338897 : Blo 143792 338897 := bstep (se 2 (by rfl) ⟨127086, by rfl⟩ : syracuseStep 338897 = 254173) B254173
theorem B1125389 : Blo 143792 1125389 := bstep (se 3 (by rfl) ⟨211010, by rfl⟩ : syracuseStep 1125389 = 422021) B422021
theorem B371729 : Blo 143792 371729 := bstep (se 2 (by rfl) ⟨139398, by rfl⟩ : syracuseStep 371729 = 278797) B278797
theorem B830513 : Blo 143792 830513 := bstep (se 2 (by rfl) ⟨311442, by rfl⟩ : syracuseStep 830513 = 622885) B622885
theorem B1682531 : Blo 143792 1682531 := bstep (se 1 (by rfl) ⟨1261898, by rfl⟩ : syracuseStep 1682531 = 2523797) B2523797
theorem B732401 : Blo 143792 732401 := bstep (se 2 (by rfl) ⟨274650, by rfl⟩ : syracuseStep 732401 = 549301) B549301
theorem B208289 : Blo 143792 208289 := bstep (se 2 (by rfl) ⟨78108, by rfl⟩ : syracuseStep 208289 = 156217) B156217
theorem B1879523 : Blo 143792 1879523 := bstep (se 1 (by rfl) ⟨1409642, by rfl⟩ : syracuseStep 1879523 = 2819285) B2819285
theorem B208369 : Blo 143792 208369 := bstep (se 2 (by rfl) ⟨78138, by rfl⟩ : syracuseStep 208369 = 156277) B156277
theorem B273937 : Blo 143792 273937 := bstep (se 2 (by rfl) ⟨102726, by rfl⟩ : syracuseStep 273937 = 205453) B205453
theorem B470701 : Blo 143792 470701 := bstep (se 3 (by rfl) ⟨88256, by rfl⟩ : syracuseStep 470701 = 176513) B176513
theorem B274097 : Blo 143792 274097 := bstep (se 2 (by rfl) ⟨102786, by rfl⟩ : syracuseStep 274097 = 205573) B205573
theorem B372721 : Blo 143792 372721 := bstep (se 2 (by rfl) ⟨139770, by rfl⟩ : syracuseStep 372721 = 279541) B279541
theorem B274499 : Blo 143792 274499 := bstep (se 1 (by rfl) ⟨205874, by rfl⟩ : syracuseStep 274499 = 411749) B411749
theorem B209155 : Blo 143792 209155 := bstep (se 1 (by rfl) ⟨156866, by rfl⟩ : syracuseStep 209155 = 313733) B313733
theorem B372995 : Blo 143792 372995 := bstep (se 1 (by rfl) ⟨279746, by rfl⟩ : syracuseStep 372995 = 559493) B559493
theorem B307633 : Blo 143792 307633 := bstep (se 2 (by rfl) ⟨115362, by rfl⟩ : syracuseStep 307633 = 230725) B230725
theorem B143795 : Blo 143792 143795 := bstep (se 1 (by rfl) ⟨107846, by rfl⟩ : syracuseStep 143795 = 215693) B215693
theorem B143811 : Blo 143792 143811 := bstep (se 1 (by rfl) ⟨107858, by rfl⟩ : syracuseStep 143811 = 215717) B215717
theorem B373187 : Blo 143792 373187 := bstep (se 1 (by rfl) ⟨279890, by rfl⟩ : syracuseStep 373187 = 559781) B559781
theorem B143827 : Blo 143792 143827 := bstep (se 1 (by rfl) ⟨107870, by rfl⟩ : syracuseStep 143827 = 215741) B215741
theorem B143843 : Blo 143792 143843 := bstep (se 1 (by rfl) ⟨107882, by rfl⟩ : syracuseStep 143843 = 215765) B215765
theorem B831971 : Blo 143792 831971 := bstep (se 1 (by rfl) ⟨623978, by rfl⟩ : syracuseStep 831971 = 1247957) B1247957
theorem B143859 : Blo 143792 143859 := bstep (se 1 (by rfl) ⟨107894, by rfl⟩ : syracuseStep 143859 = 215789) B215789
theorem B143875 : Blo 143792 143875 := bstep (se 1 (by rfl) ⟨107906, by rfl⟩ : syracuseStep 143875 = 215813) B215813
theorem B143891 : Blo 143792 143891 := bstep (se 1 (by rfl) ⟨107918, by rfl⟩ : syracuseStep 143891 = 215837) B215837
theorem B143907 : Blo 143792 143907 := bstep (se 1 (by rfl) ⟨107930, by rfl⟩ : syracuseStep 143907 = 215861) B215861
theorem B143923 : Blo 143792 143923 := bstep (se 1 (by rfl) ⟨107942, by rfl⟩ : syracuseStep 143923 = 215885) B215885
theorem B143939 : Blo 143792 143939 := bstep (se 1 (by rfl) ⟨107954, by rfl⟩ : syracuseStep 143939 = 215909) B215909
theorem B143955 : Blo 143792 143955 := bstep (se 1 (by rfl) ⟨107966, by rfl⟩ : syracuseStep 143955 = 215933) B215933
theorem B143971 : Blo 143792 143971 := bstep (se 1 (by rfl) ⟨107978, by rfl⟩ : syracuseStep 143971 = 215957) B215957
theorem B143987 : Blo 143792 143987 := bstep (se 1 (by rfl) ⟨107990, by rfl⟩ : syracuseStep 143987 = 215981) B215981
theorem B144003 : Blo 143792 144003 := bstep (se 1 (by rfl) ⟨108002, by rfl⟩ : syracuseStep 144003 = 216005) B216005
theorem B144019 : Blo 143792 144019 := bstep (se 1 (by rfl) ⟨108014, by rfl⟩ : syracuseStep 144019 = 216029) B216029
theorem B144035 : Blo 143792 144035 := bstep (se 1 (by rfl) ⟨108026, by rfl⟩ : syracuseStep 144035 = 216053) B216053
theorem B733859 : Blo 143792 733859 := bstep (se 1 (by rfl) ⟨550394, by rfl⟩ : syracuseStep 733859 = 1100789) B1100789
theorem B307889 : Blo 143792 307889 := bstep (se 2 (by rfl) ⟨115458, by rfl⟩ : syracuseStep 307889 = 230917) B230917
theorem B144051 : Blo 143792 144051 := bstep (se 1 (by rfl) ⟨108038, by rfl⟩ : syracuseStep 144051 = 216077) B216077
theorem B144067 : Blo 143792 144067 := bstep (se 1 (by rfl) ⟨108050, by rfl⟩ : syracuseStep 144067 = 216101) B216101
theorem B144083 : Blo 143792 144083 := bstep (se 1 (by rfl) ⟨108062, by rfl⟩ : syracuseStep 144083 = 216125) B216125
theorem B209633 : Blo 143792 209633 := bstep (se 2 (by rfl) ⟨78612, by rfl⟩ : syracuseStep 209633 = 157225) B157225
theorem B144099 : Blo 143792 144099 := bstep (se 1 (by rfl) ⟨108074, by rfl⟩ : syracuseStep 144099 = 216149) B216149
theorem B897763 : Blo 143792 897763 := bstep (se 1 (by rfl) ⟨673322, by rfl⟩ : syracuseStep 897763 = 1346645) B1346645
theorem B144115 : Blo 143792 144115 := bstep (se 1 (by rfl) ⟨108086, by rfl⟩ : syracuseStep 144115 = 216173) B216173
theorem B144131 : Blo 143792 144131 := bstep (se 1 (by rfl) ⟨108098, by rfl⟩ : syracuseStep 144131 = 216197) B216197
theorem B144147 : Blo 143792 144147 := bstep (se 1 (by rfl) ⟨108110, by rfl⟩ : syracuseStep 144147 = 216221) B216221
theorem B144163 : Blo 143792 144163 := bstep (se 1 (by rfl) ⟨108122, by rfl⟩ : syracuseStep 144163 = 216245) B216245
theorem B144179 : Blo 143792 144179 := bstep (se 1 (by rfl) ⟨108134, by rfl⟩ : syracuseStep 144179 = 216269) B216269
theorem B144195 : Blo 143792 144195 := bstep (se 1 (by rfl) ⟨108146, by rfl⟩ : syracuseStep 144195 = 216293) B216293
theorem B144211 : Blo 143792 144211 := bstep (se 1 (by rfl) ⟨108158, by rfl⟩ : syracuseStep 144211 = 216317) B216317
theorem B209747 : Blo 143792 209747 := bstep (se 1 (by rfl) ⟨157310, by rfl⟩ : syracuseStep 209747 = 314621) B314621
theorem B144227 : Blo 143792 144227 := bstep (se 1 (by rfl) ⟨108170, by rfl⟩ : syracuseStep 144227 = 216341) B216341
theorem B144243 : Blo 143792 144243 := bstep (se 1 (by rfl) ⟨108182, by rfl⟩ : syracuseStep 144243 = 216365) B216365
theorem B144259 : Blo 143792 144259 := bstep (se 1 (by rfl) ⟨108194, by rfl⟩ : syracuseStep 144259 = 216389) B216389
theorem B799621 : Blo 143792 799621 := bstep (se 4 (by rfl) ⟨74964, by rfl⟩ : syracuseStep 799621 = 149929) B149929
theorem B144275 : Blo 143792 144275 := bstep (se 1 (by rfl) ⟨108206, by rfl⟩ : syracuseStep 144275 = 216413) B216413
theorem B144291 : Blo 143792 144291 := bstep (se 1 (by rfl) ⟨108218, by rfl⟩ : syracuseStep 144291 = 216437) B216437
theorem B209827 : Blo 143792 209827 := bstep (se 1 (by rfl) ⟨157370, by rfl⟩ : syracuseStep 209827 = 314741) B314741
theorem B144307 : Blo 143792 144307 := bstep (se 1 (by rfl) ⟨108230, by rfl⟩ : syracuseStep 144307 = 216461) B216461
theorem B144323 : Blo 143792 144323 := bstep (se 1 (by rfl) ⟨108242, by rfl⟩ : syracuseStep 144323 = 216485) B216485
theorem B275395 : Blo 143792 275395 := bstep (se 1 (by rfl) ⟨206546, by rfl⟩ : syracuseStep 275395 = 413093) B413093
theorem B144339 : Blo 143792 144339 := bstep (se 1 (by rfl) ⟨108254, by rfl⟩ : syracuseStep 144339 = 216509) B216509
theorem B144355 : Blo 143792 144355 := bstep (se 1 (by rfl) ⟨108266, by rfl⟩ : syracuseStep 144355 = 216533) B216533
theorem B144371 : Blo 143792 144371 := bstep (se 1 (by rfl) ⟨108278, by rfl⟩ : syracuseStep 144371 = 216557) B216557
theorem B242689 : Blo 143792 242689 := bstep (se 2 (by rfl) ⟨91008, by rfl⟩ : syracuseStep 242689 = 182017) B182017
theorem B144387 : Blo 143792 144387 := bstep (se 1 (by rfl) ⟨108290, by rfl⟩ : syracuseStep 144387 = 216581) B216581
theorem B144403 : Blo 143792 144403 := bstep (se 1 (by rfl) ⟨108302, by rfl⟩ : syracuseStep 144403 = 216605) B216605
theorem B242723 : Blo 143792 242723 := bstep (se 1 (by rfl) ⟨182042, by rfl⟩ : syracuseStep 242723 = 364085) B364085
theorem B144419 : Blo 143792 144419 := bstep (se 1 (by rfl) ⟨108314, by rfl⟩ : syracuseStep 144419 = 216629) B216629
theorem B144435 : Blo 143792 144435 := bstep (se 1 (by rfl) ⟨108326, by rfl⟩ : syracuseStep 144435 = 216653) B216653
theorem B144451 : Blo 143792 144451 := bstep (se 1 (by rfl) ⟨108338, by rfl⟩ : syracuseStep 144451 = 216677) B216677
theorem B144467 : Blo 143792 144467 := bstep (se 1 (by rfl) ⟨108350, by rfl⟩ : syracuseStep 144467 = 216701) B216701
theorem B144483 : Blo 143792 144483 := bstep (se 1 (by rfl) ⟨108362, by rfl⟩ : syracuseStep 144483 = 216725) B216725
theorem B275555 : Blo 143792 275555 := bstep (se 1 (by rfl) ⟨206666, by rfl⟩ : syracuseStep 275555 = 413333) B413333
theorem B144499 : Blo 143792 144499 := bstep (se 1 (by rfl) ⟨108374, by rfl⟩ : syracuseStep 144499 = 216749) B216749
theorem B144515 : Blo 143792 144515 := bstep (se 1 (by rfl) ⟨108386, by rfl⟩ : syracuseStep 144515 = 216773) B216773
theorem B701581 : Blo 143792 701581 := bstep (se 3 (by rfl) ⟨131546, by rfl⟩ : syracuseStep 701581 = 263093) B263093
theorem B144531 : Blo 143792 144531 := bstep (se 1 (by rfl) ⟨108398, by rfl⟩ : syracuseStep 144531 = 216797) B216797
theorem B242851 : Blo 143792 242851 := bstep (se 1 (by rfl) ⟨182138, by rfl⟩ : syracuseStep 242851 = 364277) B364277
theorem B144547 : Blo 143792 144547 := bstep (se 1 (by rfl) ⟨108410, by rfl⟩ : syracuseStep 144547 = 216821) B216821
theorem B144563 : Blo 143792 144563 := bstep (se 1 (by rfl) ⟨108422, by rfl⟩ : syracuseStep 144563 = 216845) B216845
theorem B1881269 : Blo 143792 1881269 := bstep (se 5 (by rfl) ⟨88184, by rfl⟩ : syracuseStep 1881269 = 176369) B176369
theorem B144579 : Blo 143792 144579 := bstep (se 1 (by rfl) ⟨108434, by rfl⟩ : syracuseStep 144579 = 216869) B216869
theorem B144595 : Blo 143792 144595 := bstep (se 1 (by rfl) ⟨108446, by rfl⟩ : syracuseStep 144595 = 216893) B216893
theorem B144611 : Blo 143792 144611 := bstep (se 1 (by rfl) ⟨108458, by rfl⟩ : syracuseStep 144611 = 216917) B216917
theorem B10073315 : Blo 143792 10073315 := bstep (se 1 (by rfl) ⟨7554986, by rfl⟩ : syracuseStep 10073315 = 15109973) B15109973
theorem B144627 : Blo 143792 144627 := bstep (se 1 (by rfl) ⟨108470, by rfl⟩ : syracuseStep 144627 = 216941) B216941
theorem B144643 : Blo 143792 144643 := bstep (se 1 (by rfl) ⟨108482, by rfl⟩ : syracuseStep 144643 = 216965) B216965
theorem B144659 : Blo 143792 144659 := bstep (se 1 (by rfl) ⟨108494, by rfl⟩ : syracuseStep 144659 = 216989) B216989
theorem B144675 : Blo 143792 144675 := bstep (se 1 (by rfl) ⟨108506, by rfl⟩ : syracuseStep 144675 = 217013) B217013
theorem B242993 : Blo 143792 242993 := bstep (se 2 (by rfl) ⟨91122, by rfl⟩ : syracuseStep 242993 = 182245) B182245
theorem B144691 : Blo 143792 144691 := bstep (se 1 (by rfl) ⟨108518, by rfl⟩ : syracuseStep 144691 = 217037) B217037
theorem B144707 : Blo 143792 144707 := bstep (se 1 (by rfl) ⟨108530, by rfl⟩ : syracuseStep 144707 = 217061) B217061
theorem B144723 : Blo 143792 144723 := bstep (se 1 (by rfl) ⟨108542, by rfl⟩ : syracuseStep 144723 = 217085) B217085
theorem B144739 : Blo 143792 144739 := bstep (se 1 (by rfl) ⟨108554, by rfl⟩ : syracuseStep 144739 = 217109) B217109
theorem B144755 : Blo 143792 144755 := bstep (se 1 (by rfl) ⟨108566, by rfl⟩ : syracuseStep 144755 = 217133) B217133
theorem B144771 : Blo 143792 144771 := bstep (se 1 (by rfl) ⟨108578, by rfl⟩ : syracuseStep 144771 = 217157) B217157
theorem B2471309 : Blo 143792 2471309 := bstep (se 3 (by rfl) ⟨463370, by rfl⟩ : syracuseStep 2471309 = 926741) B926741
theorem B144787 : Blo 143792 144787 := bstep (se 1 (by rfl) ⟨108590, by rfl⟩ : syracuseStep 144787 = 217181) B217181
theorem B144803 : Blo 143792 144803 := bstep (se 1 (by rfl) ⟨108602, by rfl⟩ : syracuseStep 144803 = 217205) B217205
theorem B472483 : Blo 143792 472483 := bstep (se 1 (by rfl) ⟨354362, by rfl⟩ : syracuseStep 472483 = 708725) B708725
theorem B243121 : Blo 143792 243121 := bstep (se 2 (by rfl) ⟨91170, by rfl⟩ : syracuseStep 243121 = 182341) B182341
theorem B144819 : Blo 143792 144819 := bstep (se 1 (by rfl) ⟨108614, by rfl⟩ : syracuseStep 144819 = 217229) B217229
theorem B144835 : Blo 143792 144835 := bstep (se 1 (by rfl) ⟨108626, by rfl⟩ : syracuseStep 144835 = 217253) B217253
theorem B734669 : Blo 143792 734669 := bstep (se 3 (by rfl) ⟨137750, by rfl⟩ : syracuseStep 734669 = 275501) B275501
theorem B210385 : Blo 143792 210385 := bstep (se 2 (by rfl) ⟨78894, by rfl⟩ : syracuseStep 210385 = 157789) B157789
theorem B243155 : Blo 143792 243155 := bstep (se 1 (by rfl) ⟨182366, by rfl⟩ : syracuseStep 243155 = 364733) B364733
theorem B144851 : Blo 143792 144851 := bstep (se 1 (by rfl) ⟨108638, by rfl⟩ : syracuseStep 144851 = 217277) B217277
theorem B144867 : Blo 143792 144867 := bstep (se 1 (by rfl) ⟨108650, by rfl⟩ : syracuseStep 144867 = 217301) B217301
theorem B472547 : Blo 143792 472547 := bstep (se 1 (by rfl) ⟨354410, by rfl⟩ : syracuseStep 472547 = 708821) B708821
theorem B144883 : Blo 143792 144883 := bstep (se 1 (by rfl) ⟨108662, by rfl⟩ : syracuseStep 144883 = 217325) B217325
theorem B144899 : Blo 143792 144899 := bstep (se 1 (by rfl) ⟨108674, by rfl⟩ : syracuseStep 144899 = 217349) B217349
theorem B144915 : Blo 143792 144915 := bstep (se 1 (by rfl) ⟨108686, by rfl⟩ : syracuseStep 144915 = 217373) B217373
theorem B144931 : Blo 143792 144931 := bstep (se 1 (by rfl) ⟨108698, by rfl⟩ : syracuseStep 144931 = 217397) B217397
theorem B472625 : Blo 143792 472625 := bstep (se 2 (by rfl) ⟨177234, by rfl⟩ : syracuseStep 472625 = 354469) B354469
theorem B144947 : Blo 143792 144947 := bstep (se 1 (by rfl) ⟨108710, by rfl⟩ : syracuseStep 144947 = 217421) B217421
theorem B144963 : Blo 143792 144963 := bstep (se 1 (by rfl) ⟨108722, by rfl⟩ : syracuseStep 144963 = 217445) B217445
theorem B243283 : Blo 143792 243283 := bstep (se 1 (by rfl) ⟨182462, by rfl⟩ : syracuseStep 243283 = 364925) B364925
theorem B144979 : Blo 143792 144979 := bstep (se 1 (by rfl) ⟨108734, by rfl⟩ : syracuseStep 144979 = 217469) B217469
theorem B144995 : Blo 143792 144995 := bstep (se 1 (by rfl) ⟨108746, by rfl⟩ : syracuseStep 144995 = 217493) B217493
theorem B145011 : Blo 143792 145011 := bstep (se 1 (by rfl) ⟨108758, by rfl⟩ : syracuseStep 145011 = 217517) B217517
theorem B145027 : Blo 143792 145027 := bstep (se 1 (by rfl) ⟨108770, by rfl⟩ : syracuseStep 145027 = 217541) B217541
theorem B669325 : Blo 143792 669325 := bstep (se 3 (by rfl) ⟨125498, by rfl⟩ : syracuseStep 669325 = 250997) B250997
theorem B145043 : Blo 143792 145043 := bstep (se 1 (by rfl) ⟨108782, by rfl⟩ : syracuseStep 145043 = 217565) B217565
theorem B145059 : Blo 143792 145059 := bstep (se 1 (by rfl) ⟨108794, by rfl⟩ : syracuseStep 145059 = 217589) B217589
theorem B145075 : Blo 143792 145075 := bstep (se 1 (by rfl) ⟨108806, by rfl⟩ : syracuseStep 145075 = 217613) B217613
theorem B145091 : Blo 143792 145091 := bstep (se 1 (by rfl) ⟨108818, by rfl⟩ : syracuseStep 145091 = 217637) B217637
theorem B145107 : Blo 143792 145107 := bstep (se 1 (by rfl) ⟨108830, by rfl⟩ : syracuseStep 145107 = 217661) B217661
theorem B243425 : Blo 143792 243425 := bstep (se 2 (by rfl) ⟨91284, by rfl⟩ : syracuseStep 243425 = 182569) B182569
theorem B145123 : Blo 143792 145123 := bstep (se 1 (by rfl) ⟨108842, by rfl⟩ : syracuseStep 145123 = 217685) B217685
theorem B145139 : Blo 143792 145139 := bstep (se 1 (by rfl) ⟨108854, by rfl⟩ : syracuseStep 145139 = 217709) B217709
theorem B145155 : Blo 143792 145155 := bstep (se 1 (by rfl) ⟨108866, by rfl⟩ : syracuseStep 145155 = 217733) B217733
theorem B145171 : Blo 143792 145171 := bstep (se 1 (by rfl) ⟨108878, by rfl⟩ : syracuseStep 145171 = 217757) B217757
theorem B145187 : Blo 143792 145187 := bstep (se 1 (by rfl) ⟨108890, by rfl⟩ : syracuseStep 145187 = 217781) B217781
theorem B145203 : Blo 143792 145203 := bstep (se 1 (by rfl) ⟨108902, by rfl⟩ : syracuseStep 145203 = 217805) B217805
theorem B145219 : Blo 143792 145219 := bstep (se 1 (by rfl) ⟨108914, by rfl⟩ : syracuseStep 145219 = 217829) B217829
theorem B145235 : Blo 143792 145235 := bstep (se 1 (by rfl) ⟨108926, by rfl⟩ : syracuseStep 145235 = 217853) B217853
theorem B243553 : Blo 143792 243553 := bstep (se 2 (by rfl) ⟨91332, by rfl⟩ : syracuseStep 243553 = 182665) B182665
theorem B210785 : Blo 143792 210785 := bstep (se 2 (by rfl) ⟨79044, by rfl⟩ : syracuseStep 210785 = 158089) B158089
theorem B145251 : Blo 143792 145251 := bstep (se 1 (by rfl) ⟨108938, by rfl⟩ : syracuseStep 145251 = 217877) B217877
theorem B145267 : Blo 143792 145267 := bstep (se 1 (by rfl) ⟨108950, by rfl⟩ : syracuseStep 145267 = 217901) B217901
theorem B243587 : Blo 143792 243587 := bstep (se 1 (by rfl) ⟨182690, by rfl⟩ : syracuseStep 243587 = 365381) B365381
theorem B145283 : Blo 143792 145283 := bstep (se 1 (by rfl) ⟨108962, by rfl⟩ : syracuseStep 145283 = 217925) B217925
theorem B145299 : Blo 143792 145299 := bstep (se 1 (by rfl) ⟨108974, by rfl⟩ : syracuseStep 145299 = 217949) B217949
theorem B145315 : Blo 143792 145315 := bstep (se 1 (by rfl) ⟨108986, by rfl⟩ : syracuseStep 145315 = 217973) B217973
theorem B145331 : Blo 143792 145331 := bstep (se 1 (by rfl) ⟨108998, by rfl⟩ : syracuseStep 145331 = 217997) B217997
theorem B309187 : Blo 143792 309187 := bstep (se 1 (by rfl) ⟨231890, by rfl⟩ : syracuseStep 309187 = 463781) B463781
theorem B145347 : Blo 143792 145347 := bstep (se 1 (by rfl) ⟨109010, by rfl⟩ : syracuseStep 145347 = 218021) B218021
theorem B145363 : Blo 143792 145363 := bstep (se 1 (by rfl) ⟨109022, by rfl⟩ : syracuseStep 145363 = 218045) B218045
theorem B145379 : Blo 143792 145379 := bstep (se 1 (by rfl) ⟨109034, by rfl⟩ : syracuseStep 145379 = 218069) B218069
theorem B145395 : Blo 143792 145395 := bstep (se 1 (by rfl) ⟨109046, by rfl⟩ : syracuseStep 145395 = 218093) B218093
theorem B243715 : Blo 143792 243715 := bstep (se 1 (by rfl) ⟨182786, by rfl⟩ : syracuseStep 243715 = 365573) B365573
theorem B145411 : Blo 143792 145411 := bstep (se 1 (by rfl) ⟨109058, by rfl⟩ : syracuseStep 145411 = 218117) B218117
theorem B145427 : Blo 143792 145427 := bstep (se 1 (by rfl) ⟨109070, by rfl⟩ : syracuseStep 145427 = 218141) B218141
theorem B145443 : Blo 143792 145443 := bstep (se 1 (by rfl) ⟨109082, by rfl⟩ : syracuseStep 145443 = 218165) B218165
theorem B145459 : Blo 143792 145459 := bstep (se 1 (by rfl) ⟨109094, by rfl⟩ : syracuseStep 145459 = 218189) B218189
theorem B145475 : Blo 143792 145475 := bstep (se 1 (by rfl) ⟨109106, by rfl⟩ : syracuseStep 145475 = 218213) B218213
theorem B145491 : Blo 143792 145491 := bstep (se 1 (by rfl) ⟨109118, by rfl⟩ : syracuseStep 145491 = 218237) B218237
theorem B145507 : Blo 143792 145507 := bstep (se 1 (by rfl) ⟨109130, by rfl⟩ : syracuseStep 145507 = 218261) B218261
theorem B145523 : Blo 143792 145523 := bstep (se 1 (by rfl) ⟨109142, by rfl⟩ : syracuseStep 145523 = 218285) B218285
theorem B145539 : Blo 143792 145539 := bstep (se 1 (by rfl) ⟨109154, by rfl⟩ : syracuseStep 145539 = 218309) B218309
theorem B243857 : Blo 143792 243857 := bstep (se 2 (by rfl) ⟨91446, by rfl⟩ : syracuseStep 243857 = 182893) B182893
theorem B276625 : Blo 143792 276625 := bstep (se 2 (by rfl) ⟨103734, by rfl⟩ : syracuseStep 276625 = 207469) B207469
theorem B145555 : Blo 143792 145555 := bstep (se 1 (by rfl) ⟨109166, by rfl⟩ : syracuseStep 145555 = 218333) B218333
theorem B145571 : Blo 143792 145571 := bstep (se 1 (by rfl) ⟨109178, by rfl⟩ : syracuseStep 145571 = 218357) B218357
theorem B145587 : Blo 143792 145587 := bstep (se 1 (by rfl) ⟨109190, by rfl⟩ : syracuseStep 145587 = 218381) B218381
theorem B145603 : Blo 143792 145603 := bstep (se 1 (by rfl) ⟨109202, by rfl⟩ : syracuseStep 145603 = 218405) B218405
theorem B145619 : Blo 143792 145619 := bstep (se 1 (by rfl) ⟨109214, by rfl⟩ : syracuseStep 145619 = 218429) B218429
theorem B145635 : Blo 143792 145635 := bstep (se 1 (by rfl) ⟨109226, by rfl⟩ : syracuseStep 145635 = 218453) B218453
theorem B145651 : Blo 143792 145651 := bstep (se 1 (by rfl) ⟨109238, by rfl⟩ : syracuseStep 145651 = 218477) B218477
theorem B145667 : Blo 143792 145667 := bstep (se 1 (by rfl) ⟨109250, by rfl⟩ : syracuseStep 145667 = 218501) B218501
theorem B243985 : Blo 143792 243985 := bstep (se 2 (by rfl) ⟨91494, by rfl⟩ : syracuseStep 243985 = 182989) B182989
theorem B309521 : Blo 143792 309521 := bstep (se 2 (by rfl) ⟨116070, by rfl⟩ : syracuseStep 309521 = 232141) B232141
theorem B145683 : Blo 143792 145683 := bstep (se 1 (by rfl) ⟨109262, by rfl⟩ : syracuseStep 145683 = 218525) B218525
theorem B145699 : Blo 143792 145699 := bstep (se 1 (by rfl) ⟨109274, by rfl⟩ : syracuseStep 145699 = 218549) B218549
theorem B244019 : Blo 143792 244019 := bstep (se 1 (by rfl) ⟨183014, by rfl⟩ : syracuseStep 244019 = 366029) B366029
theorem B145715 : Blo 143792 145715 := bstep (se 1 (by rfl) ⟨109286, by rfl⟩ : syracuseStep 145715 = 218573) B218573
theorem B145731 : Blo 143792 145731 := bstep (se 1 (by rfl) ⟨109298, by rfl⟩ : syracuseStep 145731 = 218597) B218597
theorem B145747 : Blo 143792 145747 := bstep (se 1 (by rfl) ⟨109310, by rfl⟩ : syracuseStep 145747 = 218621) B218621
theorem B145763 : Blo 143792 145763 := bstep (se 1 (by rfl) ⟨109322, by rfl⟩ : syracuseStep 145763 = 218645) B218645
theorem B145779 : Blo 143792 145779 := bstep (se 1 (by rfl) ⟨109334, by rfl⟩ : syracuseStep 145779 = 218669) B218669
theorem B145795 : Blo 143792 145795 := bstep (se 1 (by rfl) ⟨109346, by rfl⟩ : syracuseStep 145795 = 218693) B218693
theorem B145811 : Blo 143792 145811 := bstep (se 1 (by rfl) ⟨109358, by rfl⟩ : syracuseStep 145811 = 218717) B218717
theorem B145827 : Blo 143792 145827 := bstep (se 1 (by rfl) ⟨109370, by rfl⟩ : syracuseStep 145827 = 218741) B218741
theorem B244147 : Blo 143792 244147 := bstep (se 1 (by rfl) ⟨183110, by rfl⟩ : syracuseStep 244147 = 366221) B366221
theorem B145843 : Blo 143792 145843 := bstep (se 1 (by rfl) ⟨109382, by rfl⟩ : syracuseStep 145843 = 218765) B218765
theorem B145859 : Blo 143792 145859 := bstep (se 1 (by rfl) ⟨109394, by rfl⟩ : syracuseStep 145859 = 218789) B218789
theorem B1423813 : Blo 143792 1423813 := bstep (se 4 (by rfl) ⟨133482, by rfl⟩ : syracuseStep 1423813 = 266965) B266965
theorem B145875 : Blo 143792 145875 := bstep (se 1 (by rfl) ⟨109406, by rfl⟩ : syracuseStep 145875 = 218813) B218813
theorem B145891 : Blo 143792 145891 := bstep (se 1 (by rfl) ⟨109418, by rfl⟩ : syracuseStep 145891 = 218837) B218837
theorem B145907 : Blo 143792 145907 := bstep (se 1 (by rfl) ⟨109430, by rfl⟩ : syracuseStep 145907 = 218861) B218861
theorem B145923 : Blo 143792 145923 := bstep (se 1 (by rfl) ⟨109442, by rfl⟩ : syracuseStep 145923 = 218885) B218885
theorem B145939 : Blo 143792 145939 := bstep (se 1 (by rfl) ⟨109454, by rfl⟩ : syracuseStep 145939 = 218909) B218909
theorem B145955 : Blo 143792 145955 := bstep (se 1 (by rfl) ⟨109466, by rfl⟩ : syracuseStep 145955 = 218933) B218933
theorem B145971 : Blo 143792 145971 := bstep (se 1 (by rfl) ⟨109478, by rfl⟩ : syracuseStep 145971 = 218957) B218957
theorem B244289 : Blo 143792 244289 := bstep (se 2 (by rfl) ⟨91608, by rfl⟩ : syracuseStep 244289 = 183217) B183217
theorem B145987 : Blo 143792 145987 := bstep (se 1 (by rfl) ⟨109490, by rfl⟩ : syracuseStep 145987 = 218981) B218981
theorem B146003 : Blo 143792 146003 := bstep (se 1 (by rfl) ⟨109502, by rfl⟩ : syracuseStep 146003 = 219005) B219005
theorem B146019 : Blo 143792 146019 := bstep (se 1 (by rfl) ⟨109514, by rfl⟩ : syracuseStep 146019 = 219029) B219029
theorem B146035 : Blo 143792 146035 := bstep (se 1 (by rfl) ⟨109526, by rfl⟩ : syracuseStep 146035 = 219053) B219053
theorem B146051 : Blo 143792 146051 := bstep (se 1 (by rfl) ⟨109538, by rfl⟩ : syracuseStep 146051 = 219077) B219077
theorem B146067 : Blo 143792 146067 := bstep (se 1 (by rfl) ⟨109550, by rfl⟩ : syracuseStep 146067 = 219101) B219101
theorem B146083 : Blo 143792 146083 := bstep (se 1 (by rfl) ⟨109562, by rfl⟩ : syracuseStep 146083 = 219125) B219125
theorem B146099 : Blo 143792 146099 := bstep (se 1 (by rfl) ⟨109574, by rfl⟩ : syracuseStep 146099 = 219149) B219149
theorem B244417 : Blo 143792 244417 := bstep (se 2 (by rfl) ⟨91656, by rfl⟩ : syracuseStep 244417 = 183313) B183313
theorem B146115 : Blo 143792 146115 := bstep (se 1 (by rfl) ⟨109586, by rfl⟩ : syracuseStep 146115 = 219173) B219173
theorem B146131 : Blo 143792 146131 := bstep (se 1 (by rfl) ⟨109598, by rfl⟩ : syracuseStep 146131 = 219197) B219197
theorem B244451 : Blo 143792 244451 := bstep (se 1 (by rfl) ⟨183338, by rfl⟩ : syracuseStep 244451 = 366677) B366677
theorem B146147 : Blo 143792 146147 := bstep (se 1 (by rfl) ⟨109610, by rfl⟩ : syracuseStep 146147 = 219221) B219221
theorem B146163 : Blo 143792 146163 := bstep (se 1 (by rfl) ⟨109622, by rfl⟩ : syracuseStep 146163 = 219245) B219245
theorem B146179 : Blo 143792 146179 := bstep (se 1 (by rfl) ⟨109634, by rfl⟩ : syracuseStep 146179 = 219269) B219269
theorem B146195 : Blo 143792 146195 := bstep (se 1 (by rfl) ⟨109646, by rfl⟩ : syracuseStep 146195 = 219293) B219293
theorem B146211 : Blo 143792 146211 := bstep (se 1 (by rfl) ⟨109658, by rfl⟩ : syracuseStep 146211 = 219317) B219317
theorem B146227 : Blo 143792 146227 := bstep (se 1 (by rfl) ⟨109670, by rfl⟩ : syracuseStep 146227 = 219341) B219341
theorem B146243 : Blo 143792 146243 := bstep (se 1 (by rfl) ⟨109682, by rfl⟩ : syracuseStep 146243 = 219365) B219365
theorem B146259 : Blo 143792 146259 := bstep (se 1 (by rfl) ⟨109694, by rfl⟩ : syracuseStep 146259 = 219389) B219389
theorem B244579 : Blo 143792 244579 := bstep (se 1 (by rfl) ⟨183434, by rfl⟩ : syracuseStep 244579 = 366869) B366869
theorem B146275 : Blo 143792 146275 := bstep (se 1 (by rfl) ⟨109706, by rfl⟩ : syracuseStep 146275 = 219413) B219413
theorem B146291 : Blo 143792 146291 := bstep (se 1 (by rfl) ⟨109718, by rfl⟩ : syracuseStep 146291 = 219437) B219437
theorem B146307 : Blo 143792 146307 := bstep (se 1 (by rfl) ⟨109730, by rfl⟩ : syracuseStep 146307 = 219461) B219461
theorem B932741 : Blo 143792 932741 := bstep (se 4 (by rfl) ⟨87444, by rfl⟩ : syracuseStep 932741 = 174889) B174889
theorem B146323 : Blo 143792 146323 := bstep (se 1 (by rfl) ⟨109742, by rfl⟩ : syracuseStep 146323 = 219485) B219485
theorem B146339 : Blo 143792 146339 := bstep (se 1 (by rfl) ⟨109754, by rfl⟩ : syracuseStep 146339 = 219509) B219509
theorem B146355 : Blo 143792 146355 := bstep (se 1 (by rfl) ⟨109766, by rfl⟩ : syracuseStep 146355 = 219533) B219533
theorem B146371 : Blo 143792 146371 := bstep (se 1 (by rfl) ⟨109778, by rfl⟩ : syracuseStep 146371 = 219557) B219557
theorem B146387 : Blo 143792 146387 := bstep (se 1 (by rfl) ⟨109790, by rfl⟩ : syracuseStep 146387 = 219581) B219581
theorem B146403 : Blo 143792 146403 := bstep (se 1 (by rfl) ⟨109802, by rfl⟩ : syracuseStep 146403 = 219605) B219605
theorem B244721 : Blo 143792 244721 := bstep (se 2 (by rfl) ⟨91770, by rfl⟩ : syracuseStep 244721 = 183541) B183541
theorem B146419 : Blo 143792 146419 := bstep (se 1 (by rfl) ⟨109814, by rfl⟩ : syracuseStep 146419 = 219629) B219629
theorem B146435 : Blo 143792 146435 := bstep (se 1 (by rfl) ⟨109826, by rfl⟩ : syracuseStep 146435 = 219653) B219653
theorem B146451 : Blo 143792 146451 := bstep (se 1 (by rfl) ⟨109838, by rfl⟩ : syracuseStep 146451 = 219677) B219677
theorem B146467 : Blo 143792 146467 := bstep (se 1 (by rfl) ⟨109850, by rfl⟩ : syracuseStep 146467 = 219701) B219701
theorem B277553 : Blo 143792 277553 := bstep (se 2 (by rfl) ⟨104082, by rfl⟩ : syracuseStep 277553 = 208165) B208165
theorem B146483 : Blo 143792 146483 := bstep (se 1 (by rfl) ⟨109862, by rfl⟩ : syracuseStep 146483 = 219725) B219725
theorem B146499 : Blo 143792 146499 := bstep (se 1 (by rfl) ⟨109874, by rfl⟩ : syracuseStep 146499 = 219749) B219749
theorem B146515 : Blo 143792 146515 := bstep (se 1 (by rfl) ⟨109886, by rfl⟩ : syracuseStep 146515 = 219773) B219773
theorem B146531 : Blo 143792 146531 := bstep (se 1 (by rfl) ⟨109898, by rfl⟩ : syracuseStep 146531 = 219797) B219797
theorem B244849 : Blo 143792 244849 := bstep (se 2 (by rfl) ⟨91818, by rfl⟩ : syracuseStep 244849 = 183637) B183637
theorem B146547 : Blo 143792 146547 := bstep (se 1 (by rfl) ⟨109910, by rfl⟩ : syracuseStep 146547 = 219821) B219821
theorem B146563 : Blo 143792 146563 := bstep (se 1 (by rfl) ⟨109922, by rfl⟩ : syracuseStep 146563 = 219845) B219845
theorem B244883 : Blo 143792 244883 := bstep (se 1 (by rfl) ⟨183662, by rfl⟩ : syracuseStep 244883 = 367325) B367325
theorem B146579 : Blo 143792 146579 := bstep (se 1 (by rfl) ⟨109934, by rfl⟩ : syracuseStep 146579 = 219869) B219869
theorem B146595 : Blo 143792 146595 := bstep (se 1 (by rfl) ⟨109946, by rfl⟩ : syracuseStep 146595 = 219893) B219893
theorem B277681 : Blo 143792 277681 := bstep (se 2 (by rfl) ⟨104130, by rfl⟩ : syracuseStep 277681 = 208261) B208261
theorem B146611 : Blo 143792 146611 := bstep (se 1 (by rfl) ⟨109958, by rfl⟩ : syracuseStep 146611 = 219917) B219917
theorem B146627 : Blo 143792 146627 := bstep (se 1 (by rfl) ⟨109970, by rfl⟩ : syracuseStep 146627 = 219941) B219941
theorem B1096901 : Blo 143792 1096901 := bstep (se 4 (by rfl) ⟨102834, by rfl⟩ : syracuseStep 1096901 = 205669) B205669
theorem B146643 : Blo 143792 146643 := bstep (se 1 (by rfl) ⟨109982, by rfl⟩ : syracuseStep 146643 = 219965) B219965
theorem B146659 : Blo 143792 146659 := bstep (se 1 (by rfl) ⟨109994, by rfl⟩ : syracuseStep 146659 = 219989) B219989
theorem B146675 : Blo 143792 146675 := bstep (se 1 (by rfl) ⟨110006, by rfl⟩ : syracuseStep 146675 = 220013) B220013
theorem B146691 : Blo 143792 146691 := bstep (se 1 (by rfl) ⟨110018, by rfl⟩ : syracuseStep 146691 = 220037) B220037
theorem B245011 : Blo 143792 245011 := bstep (se 1 (by rfl) ⟨183758, by rfl⟩ : syracuseStep 245011 = 367517) B367517
theorem B146707 : Blo 143792 146707 := bstep (se 1 (by rfl) ⟨110030, by rfl⟩ : syracuseStep 146707 = 220061) B220061
theorem B146723 : Blo 143792 146723 := bstep (se 1 (by rfl) ⟨110042, by rfl⟩ : syracuseStep 146723 = 220085) B220085
theorem B146739 : Blo 143792 146739 := bstep (se 1 (by rfl) ⟨110054, by rfl⟩ : syracuseStep 146739 = 220109) B220109
theorem B146755 : Blo 143792 146755 := bstep (se 1 (by rfl) ⟨110066, by rfl⟩ : syracuseStep 146755 = 220133) B220133
theorem B146771 : Blo 143792 146771 := bstep (se 1 (by rfl) ⟨110078, by rfl⟩ : syracuseStep 146771 = 220157) B220157
theorem B146787 : Blo 143792 146787 := bstep (se 1 (by rfl) ⟨110090, by rfl⟩ : syracuseStep 146787 = 220181) B220181
theorem B146803 : Blo 143792 146803 := bstep (se 1 (by rfl) ⟨110102, by rfl⟩ : syracuseStep 146803 = 220205) B220205
theorem B146819 : Blo 143792 146819 := bstep (se 1 (by rfl) ⟨110114, by rfl⟩ : syracuseStep 146819 = 220229) B220229
theorem B146835 : Blo 143792 146835 := bstep (se 1 (by rfl) ⟨110126, by rfl⟩ : syracuseStep 146835 = 220253) B220253
theorem B245153 : Blo 143792 245153 := bstep (se 2 (by rfl) ⟨91932, by rfl⟩ : syracuseStep 245153 = 183865) B183865
theorem B310691 : Blo 143792 310691 := bstep (se 1 (by rfl) ⟨233018, by rfl⟩ : syracuseStep 310691 = 466037) B466037
theorem B146851 : Blo 143792 146851 := bstep (se 1 (by rfl) ⟨110138, by rfl⟩ : syracuseStep 146851 = 220277) B220277
theorem B146867 : Blo 143792 146867 := bstep (se 1 (by rfl) ⟨110150, by rfl⟩ : syracuseStep 146867 = 220301) B220301
theorem B146883 : Blo 143792 146883 := bstep (se 1 (by rfl) ⟨110162, by rfl⟩ : syracuseStep 146883 = 220325) B220325
theorem B146899 : Blo 143792 146899 := bstep (se 1 (by rfl) ⟨110174, by rfl⟩ : syracuseStep 146899 = 220349) B220349
theorem B146915 : Blo 143792 146915 := bstep (se 1 (by rfl) ⟨110186, by rfl⟩ : syracuseStep 146915 = 220373) B220373
theorem B146931 : Blo 143792 146931 := bstep (se 1 (by rfl) ⟨110198, by rfl⟩ : syracuseStep 146931 = 220397) B220397
theorem B146947 : Blo 143792 146947 := bstep (se 1 (by rfl) ⟨110210, by rfl⟩ : syracuseStep 146947 = 220421) B220421
theorem B146963 : Blo 143792 146963 := bstep (se 1 (by rfl) ⟨110222, by rfl⟩ : syracuseStep 146963 = 220445) B220445
theorem B245281 : Blo 143792 245281 := bstep (se 2 (by rfl) ⟨91980, by rfl⟩ : syracuseStep 245281 = 183961) B183961
theorem B146979 : Blo 143792 146979 := bstep (se 1 (by rfl) ⟨110234, by rfl⟩ : syracuseStep 146979 = 220469) B220469
theorem B146995 : Blo 143792 146995 := bstep (se 1 (by rfl) ⟨110246, by rfl⟩ : syracuseStep 146995 = 220493) B220493
theorem B245315 : Blo 143792 245315 := bstep (se 1 (by rfl) ⟨183986, by rfl⟩ : syracuseStep 245315 = 367973) B367973
theorem B278083 : Blo 143792 278083 := bstep (se 1 (by rfl) ⟨208562, by rfl⟩ : syracuseStep 278083 = 417125) B417125
theorem B147011 : Blo 143792 147011 := bstep (se 1 (by rfl) ⟨110258, by rfl⟩ : syracuseStep 147011 = 220517) B220517
theorem B147027 : Blo 143792 147027 := bstep (se 1 (by rfl) ⟨110270, by rfl⟩ : syracuseStep 147027 = 220541) B220541
theorem B147043 : Blo 143792 147043 := bstep (se 1 (by rfl) ⟨110282, by rfl⟩ : syracuseStep 147043 = 220565) B220565
theorem B278129 : Blo 143792 278129 := bstep (se 2 (by rfl) ⟨104298, by rfl⟩ : syracuseStep 278129 = 208597) B208597
theorem B147059 : Blo 143792 147059 := bstep (se 1 (by rfl) ⟨110294, by rfl⟩ : syracuseStep 147059 = 220589) B220589
theorem B147075 : Blo 143792 147075 := bstep (se 1 (by rfl) ⟨110306, by rfl⟩ : syracuseStep 147075 = 220613) B220613
theorem B147091 : Blo 143792 147091 := bstep (se 1 (by rfl) ⟨110318, by rfl⟩ : syracuseStep 147091 = 220637) B220637
theorem B147107 : Blo 143792 147107 := bstep (se 1 (by rfl) ⟨110330, by rfl⟩ : syracuseStep 147107 = 220661) B220661
theorem B147123 : Blo 143792 147123 := bstep (se 1 (by rfl) ⟨110342, by rfl⟩ : syracuseStep 147123 = 220685) B220685
theorem B245443 : Blo 143792 245443 := bstep (se 1 (by rfl) ⟨184082, by rfl⟩ : syracuseStep 245443 = 368165) B368165
theorem B147139 : Blo 143792 147139 := bstep (se 1 (by rfl) ⟨110354, by rfl⟩ : syracuseStep 147139 = 220709) B220709
theorem B147155 : Blo 143792 147155 := bstep (se 1 (by rfl) ⟨110366, by rfl⟩ : syracuseStep 147155 = 220733) B220733
theorem B147171 : Blo 143792 147171 := bstep (se 1 (by rfl) ⟨110378, by rfl⟩ : syracuseStep 147171 = 220757) B220757
theorem B147187 : Blo 143792 147187 := bstep (se 1 (by rfl) ⟨110390, by rfl⟩ : syracuseStep 147187 = 220781) B220781
theorem B147203 : Blo 143792 147203 := bstep (se 1 (by rfl) ⟨110402, by rfl⟩ : syracuseStep 147203 = 220805) B220805
theorem B147219 : Blo 143792 147219 := bstep (se 1 (by rfl) ⟨110414, by rfl⟩ : syracuseStep 147219 = 220829) B220829
theorem B147235 : Blo 143792 147235 := bstep (se 1 (by rfl) ⟨110426, by rfl⟩ : syracuseStep 147235 = 220853) B220853
theorem B147251 : Blo 143792 147251 := bstep (se 1 (by rfl) ⟨110438, by rfl⟩ : syracuseStep 147251 = 220877) B220877
theorem B147267 : Blo 143792 147267 := bstep (se 1 (by rfl) ⟨110450, by rfl⟩ : syracuseStep 147267 = 220901) B220901
theorem B245585 : Blo 143792 245585 := bstep (se 2 (by rfl) ⟨92094, by rfl⟩ : syracuseStep 245585 = 184189) B184189
theorem B147283 : Blo 143792 147283 := bstep (se 1 (by rfl) ⟨110462, by rfl⟩ : syracuseStep 147283 = 220925) B220925
theorem B147299 : Blo 143792 147299 := bstep (se 1 (by rfl) ⟨110474, by rfl⟩ : syracuseStep 147299 = 220949) B220949
theorem B147315 : Blo 143792 147315 := bstep (se 1 (by rfl) ⟨110486, by rfl⟩ : syracuseStep 147315 = 220973) B220973
theorem B147331 : Blo 143792 147331 := bstep (se 1 (by rfl) ⟨110498, by rfl⟩ : syracuseStep 147331 = 220997) B220997
theorem B278417 : Blo 143792 278417 := bstep (se 2 (by rfl) ⟨104406, by rfl⟩ : syracuseStep 278417 = 208813) B208813
theorem B147347 : Blo 143792 147347 := bstep (se 1 (by rfl) ⟨110510, by rfl⟩ : syracuseStep 147347 = 221021) B221021
theorem B147363 : Blo 143792 147363 := bstep (se 1 (by rfl) ⟨110522, by rfl⟩ : syracuseStep 147363 = 221045) B221045
theorem B147379 : Blo 143792 147379 := bstep (se 1 (by rfl) ⟨110534, by rfl⟩ : syracuseStep 147379 = 221069) B221069
theorem B147395 : Blo 143792 147395 := bstep (se 1 (by rfl) ⟨110546, by rfl⟩ : syracuseStep 147395 = 221093) B221093
theorem B245713 : Blo 143792 245713 := bstep (se 2 (by rfl) ⟨92142, by rfl⟩ : syracuseStep 245713 = 184285) B184285
theorem B147411 : Blo 143792 147411 := bstep (se 1 (by rfl) ⟨110558, by rfl⟩ : syracuseStep 147411 = 221117) B221117
theorem B147427 : Blo 143792 147427 := bstep (se 1 (by rfl) ⟨110570, by rfl⟩ : syracuseStep 147427 = 221141) B221141
theorem B245747 : Blo 143792 245747 := bstep (se 1 (by rfl) ⟨184310, by rfl⟩ : syracuseStep 245747 = 368621) B368621
theorem B147443 : Blo 143792 147443 := bstep (se 1 (by rfl) ⟨110582, by rfl⟩ : syracuseStep 147443 = 221165) B221165
theorem B147459 : Blo 143792 147459 := bstep (se 1 (by rfl) ⟨110594, by rfl⟩ : syracuseStep 147459 = 221189) B221189
theorem B147475 : Blo 143792 147475 := bstep (se 1 (by rfl) ⟨110606, by rfl⟩ : syracuseStep 147475 = 221213) B221213
theorem B147491 : Blo 143792 147491 := bstep (se 1 (by rfl) ⟨110618, by rfl⟩ : syracuseStep 147491 = 221237) B221237
theorem B147507 : Blo 143792 147507 := bstep (se 1 (by rfl) ⟨110630, by rfl⟩ : syracuseStep 147507 = 221261) B221261
theorem B147523 : Blo 143792 147523 := bstep (se 1 (by rfl) ⟨110642, by rfl⟩ : syracuseStep 147523 = 221285) B221285
theorem B147539 : Blo 143792 147539 := bstep (se 1 (by rfl) ⟨110654, by rfl⟩ : syracuseStep 147539 = 221309) B221309
theorem B1065059 : Blo 143792 1065059 := bstep (se 1 (by rfl) ⟨798794, by rfl⟩ : syracuseStep 1065059 = 1597589) B1597589
theorem B147555 : Blo 143792 147555 := bstep (se 1 (by rfl) ⟨110666, by rfl⟩ : syracuseStep 147555 = 221333) B221333
theorem B245875 : Blo 143792 245875 := bstep (se 1 (by rfl) ⟨184406, by rfl⟩ : syracuseStep 245875 = 368813) B368813
theorem B147571 : Blo 143792 147571 := bstep (se 1 (by rfl) ⟨110678, by rfl⟩ : syracuseStep 147571 = 221357) B221357
theorem B147587 : Blo 143792 147587 := bstep (se 1 (by rfl) ⟨110690, by rfl⟩ : syracuseStep 147587 = 221381) B221381
theorem B147603 : Blo 143792 147603 := bstep (se 1 (by rfl) ⟨110702, by rfl⟩ : syracuseStep 147603 = 221405) B221405
theorem B147619 : Blo 143792 147619 := bstep (se 1 (by rfl) ⟨110714, by rfl⟩ : syracuseStep 147619 = 221429) B221429
theorem B147635 : Blo 143792 147635 := bstep (se 1 (by rfl) ⟨110726, by rfl⟩ : syracuseStep 147635 = 221453) B221453
theorem B147651 : Blo 143792 147651 := bstep (se 1 (by rfl) ⟨110738, by rfl⟩ : syracuseStep 147651 = 221477) B221477
theorem B147667 : Blo 143792 147667 := bstep (se 1 (by rfl) ⟨110750, by rfl⟩ : syracuseStep 147667 = 221501) B221501
theorem B147683 : Blo 143792 147683 := bstep (se 1 (by rfl) ⟨110762, by rfl⟩ : syracuseStep 147683 = 221525) B221525
theorem B147699 : Blo 143792 147699 := bstep (se 1 (by rfl) ⟨110774, by rfl⟩ : syracuseStep 147699 = 221549) B221549
theorem B246017 : Blo 143792 246017 := bstep (se 2 (by rfl) ⟨92256, by rfl⟩ : syracuseStep 246017 = 184513) B184513
theorem B147715 : Blo 143792 147715 := bstep (se 1 (by rfl) ⟨110786, by rfl⟩ : syracuseStep 147715 = 221573) B221573
theorem B147731 : Blo 143792 147731 := bstep (se 1 (by rfl) ⟨110798, by rfl⟩ : syracuseStep 147731 = 221597) B221597
theorem B147747 : Blo 143792 147747 := bstep (se 1 (by rfl) ⟨110810, by rfl⟩ : syracuseStep 147747 = 221621) B221621
theorem B737585 : Blo 143792 737585 := bstep (se 2 (by rfl) ⟨276594, by rfl⟩ : syracuseStep 737585 = 553189) B553189
theorem B147763 : Blo 143792 147763 := bstep (se 1 (by rfl) ⟨110822, by rfl⟩ : syracuseStep 147763 = 221645) B221645
theorem B147779 : Blo 143792 147779 := bstep (se 1 (by rfl) ⟨110834, by rfl⟩ : syracuseStep 147779 = 221669) B221669
theorem B1982789 : Blo 143792 1982789 := bstep (se 4 (by rfl) ⟨185886, by rfl⟩ : syracuseStep 1982789 = 371773) B371773
theorem B246145 : Blo 143792 246145 := bstep (se 2 (by rfl) ⟨92304, by rfl⟩ : syracuseStep 246145 = 184609) B184609
theorem B1393037 : Blo 143792 1393037 := bstep (se 3 (by rfl) ⟨261194, by rfl⟩ : syracuseStep 1393037 = 522389) B522389
theorem B246179 : Blo 143792 246179 := bstep (se 1 (by rfl) ⟨184634, by rfl⟩ : syracuseStep 246179 = 369269) B369269
theorem B246307 : Blo 143792 246307 := bstep (se 1 (by rfl) ⟨184730, by rfl⟩ : syracuseStep 246307 = 369461) B369461
theorem B279139 : Blo 143792 279139 := bstep (se 1 (by rfl) ⟨209354, by rfl⟩ : syracuseStep 279139 = 418709) B418709
theorem B246449 : Blo 143792 246449 := bstep (se 2 (by rfl) ⟨92418, by rfl⟩ : syracuseStep 246449 = 184837) B184837
theorem B2081477 : Blo 143792 2081477 := bstep (se 4 (by rfl) ⟨195138, by rfl⟩ : syracuseStep 2081477 = 390277) B390277
theorem B1000133 : Blo 143792 1000133 := bstep (se 4 (by rfl) ⟨93762, by rfl⟩ : syracuseStep 1000133 = 187525) B187525
theorem B410417 : Blo 143792 410417 := bstep (se 2 (by rfl) ⟨153906, by rfl⟩ : syracuseStep 410417 = 307813) B307813
theorem B246577 : Blo 143792 246577 := bstep (se 2 (by rfl) ⟨92466, by rfl⟩ : syracuseStep 246577 = 184933) B184933
theorem B279377 : Blo 143792 279377 := bstep (se 2 (by rfl) ⟨104766, by rfl⟩ : syracuseStep 279377 = 209533) B209533
theorem B246611 : Blo 143792 246611 := bstep (se 1 (by rfl) ⟨184958, by rfl⟩ : syracuseStep 246611 = 369917) B369917
theorem B3687281 : Blo 143792 3687281 := bstep (se 2 (by rfl) ⟨1382730, by rfl⟩ : syracuseStep 3687281 = 2765461) B2765461
theorem B246739 : Blo 143792 246739 := bstep (se 1 (by rfl) ⟨185054, by rfl⟩ : syracuseStep 246739 = 370109) B370109
theorem B410609 : Blo 143792 410609 := bstep (se 2 (by rfl) ⟨153978, by rfl⟩ : syracuseStep 410609 = 307957) B307957
theorem B148483 : Blo 143792 148483 := bstep (se 1 (by rfl) ⟨111362, by rfl⟩ : syracuseStep 148483 = 222725) B222725
theorem B279587 : Blo 143792 279587 := bstep (se 1 (by rfl) ⟨209690, by rfl⟩ : syracuseStep 279587 = 419381) B419381
theorem B246881 : Blo 143792 246881 := bstep (se 2 (by rfl) ⟨92580, by rfl⟩ : syracuseStep 246881 = 185161) B185161
theorem B247009 : Blo 143792 247009 := bstep (se 2 (by rfl) ⟨92628, by rfl⟩ : syracuseStep 247009 = 185257) B185257
theorem B279811 : Blo 143792 279811 := bstep (se 1 (by rfl) ⟨209858, by rfl⟩ : syracuseStep 279811 = 419717) B419717
theorem B247043 : Blo 143792 247043 := bstep (se 1 (by rfl) ⟨185282, by rfl⟩ : syracuseStep 247043 = 370565) B370565
theorem B378179 : Blo 143792 378179 := bstep (se 1 (by rfl) ⟨283634, by rfl⟩ : syracuseStep 378179 = 567269) B567269
theorem B279875 : Blo 143792 279875 := bstep (se 1 (by rfl) ⟨209906, by rfl⟩ : syracuseStep 279875 = 419813) B419813
theorem B312707 : Blo 143792 312707 := bstep (se 1 (by rfl) ⟨234530, by rfl⟩ : syracuseStep 312707 = 469061) B469061
theorem B247171 : Blo 143792 247171 := bstep (se 1 (by rfl) ⟨185378, by rfl⟩ : syracuseStep 247171 = 370757) B370757
theorem B247313 : Blo 143792 247313 := bstep (se 2 (by rfl) ⟨92742, by rfl⟩ : syracuseStep 247313 = 185485) B185485
theorem B1754693 : Blo 143792 1754693 := bstep (se 4 (by rfl) ⟨164502, by rfl⟩ : syracuseStep 1754693 = 329005) B329005
theorem B247441 : Blo 143792 247441 := bstep (se 2 (by rfl) ⟨92790, by rfl⟩ : syracuseStep 247441 = 185581) B185581
theorem B247475 : Blo 143792 247475 := bstep (se 1 (by rfl) ⟨185606, by rfl⟩ : syracuseStep 247475 = 371213) B371213
theorem B739043 : Blo 143792 739043 := bstep (se 1 (by rfl) ⟨554282, by rfl⟩ : syracuseStep 739043 = 1108565) B1108565
theorem B444209 : Blo 143792 444209 := bstep (se 2 (by rfl) ⟨166578, by rfl⟩ : syracuseStep 444209 = 333157) B333157
theorem B247603 : Blo 143792 247603 := bstep (se 1 (by rfl) ⟨185702, by rfl⟩ : syracuseStep 247603 = 371405) B371405
theorem B182083 : Blo 143792 182083 := bstep (se 1 (by rfl) ⟨136562, by rfl⟩ : syracuseStep 182083 = 273125) B273125
theorem B182179 : Blo 143792 182179 := bstep (se 1 (by rfl) ⟨136634, by rfl⟩ : syracuseStep 182179 = 273269) B273269
theorem B247745 : Blo 143792 247745 := bstep (se 2 (by rfl) ⟨92904, by rfl⟩ : syracuseStep 247745 = 185809) B185809
theorem B739277 : Blo 143792 739277 := bstep (se 3 (by rfl) ⟨138614, by rfl⟩ : syracuseStep 739277 = 277229) B277229
theorem B411601 : Blo 143792 411601 := bstep (se 2 (by rfl) ⟨154350, by rfl⟩ : syracuseStep 411601 = 308701) B308701
theorem B247873 : Blo 143792 247873 := bstep (se 2 (by rfl) ⟨92952, by rfl⟩ : syracuseStep 247873 = 185905) B185905
theorem B247907 : Blo 143792 247907 := bstep (se 1 (by rfl) ⟨185930, by rfl⟩ : syracuseStep 247907 = 371861) B371861
theorem B444611 : Blo 143792 444611 := bstep (se 1 (by rfl) ⟨333458, by rfl⟩ : syracuseStep 444611 = 666917) B666917
theorem B411875 : Blo 143792 411875 := bstep (se 1 (by rfl) ⟨308906, by rfl⟩ : syracuseStep 411875 = 617813) B617813
theorem B248035 : Blo 143792 248035 := bstep (se 1 (by rfl) ⟨186026, by rfl⟩ : syracuseStep 248035 = 372053) B372053
theorem B215347 : Blo 143792 215347 := bstep (se 1 (by rfl) ⟨161510, by rfl⟩ : syracuseStep 215347 = 323021) B323021
theorem B248177 : Blo 143792 248177 := bstep (se 2 (by rfl) ⟨93066, by rfl⟩ : syracuseStep 248177 = 186133) B186133
theorem B182675 : Blo 143792 182675 := bstep (se 1 (by rfl) ⟨137006, by rfl⟩ : syracuseStep 182675 = 274013) B274013
theorem B412067 : Blo 143792 412067 := bstep (se 1 (by rfl) ⟨309050, by rfl⟩ : syracuseStep 412067 = 618101) B618101
theorem B248305 : Blo 143792 248305 := bstep (se 2 (by rfl) ⟨93114, by rfl⟩ : syracuseStep 248305 = 186229) B186229
theorem B739853 : Blo 143792 739853 := bstep (se 3 (by rfl) ⟨138722, by rfl⟩ : syracuseStep 739853 = 277445) B277445
theorem B248339 : Blo 143792 248339 := bstep (se 1 (by rfl) ⟨186254, by rfl⟩ : syracuseStep 248339 = 372509) B372509
theorem B1002125 : Blo 143792 1002125 := bstep (se 3 (by rfl) ⟨187898, by rfl⟩ : syracuseStep 1002125 = 375797) B375797
theorem B248465 : Blo 143792 248465 := bstep (se 2 (by rfl) ⟨93174, by rfl⟩ : syracuseStep 248465 = 186349) B186349
theorem B215699 : Blo 143792 215699 := bstep (se 1 (by rfl) ⟨161774, by rfl⟩ : syracuseStep 215699 = 323549) B323549
theorem B248467 : Blo 143792 248467 := bstep (se 1 (by rfl) ⟨186350, by rfl⟩ : syracuseStep 248467 = 372701) B372701
theorem B215729 : Blo 143792 215729 := bstep (se 2 (by rfl) ⟨80898, by rfl⟩ : syracuseStep 215729 = 161797) B161797
theorem B215747 : Blo 143792 215747 := bstep (se 1 (by rfl) ⟨161810, by rfl⟩ : syracuseStep 215747 = 323621) B323621
theorem B215777 : Blo 143792 215777 := bstep (se 2 (by rfl) ⟨80916, by rfl⟩ : syracuseStep 215777 = 161833) B161833
theorem B215795 : Blo 143792 215795 := bstep (se 1 (by rfl) ⟨161846, by rfl⟩ : syracuseStep 215795 = 323693) B323693
theorem B215825 : Blo 143792 215825 := bstep (se 2 (by rfl) ⟨80934, by rfl⟩ : syracuseStep 215825 = 161869) B161869
theorem B248609 : Blo 143792 248609 := bstep (se 2 (by rfl) ⟨93228, by rfl⟩ : syracuseStep 248609 = 186457) B186457
theorem B215843 : Blo 143792 215843 := bstep (se 1 (by rfl) ⟨161882, by rfl⟩ : syracuseStep 215843 = 323765) B323765
theorem B215873 : Blo 143792 215873 := bstep (se 2 (by rfl) ⟨80952, by rfl⟩ : syracuseStep 215873 = 161905) B161905
theorem B215891 : Blo 143792 215891 := bstep (se 1 (by rfl) ⟨161918, by rfl⟩ : syracuseStep 215891 = 323837) B323837
theorem B445283 : Blo 143792 445283 := bstep (se 1 (by rfl) ⟨333962, by rfl⟩ : syracuseStep 445283 = 667925) B667925
theorem B215921 : Blo 143792 215921 := bstep (se 2 (by rfl) ⟨80970, by rfl⟩ : syracuseStep 215921 = 161941) B161941
theorem B215939 : Blo 143792 215939 := bstep (se 1 (by rfl) ⟨161954, by rfl⟩ : syracuseStep 215939 = 323909) B323909
theorem B215969 : Blo 143792 215969 := bstep (se 2 (by rfl) ⟨80988, by rfl⟩ : syracuseStep 215969 = 161977) B161977
theorem B248737 : Blo 143792 248737 := bstep (se 2 (by rfl) ⟨93276, by rfl⟩ : syracuseStep 248737 = 186553) B186553
theorem B215987 : Blo 143792 215987 := bstep (se 1 (by rfl) ⟨161990, by rfl⟩ : syracuseStep 215987 = 323981) B323981
theorem B248771 : Blo 143792 248771 := bstep (se 1 (by rfl) ⟨186578, by rfl⟩ : syracuseStep 248771 = 373157) B373157
theorem B216017 : Blo 143792 216017 := bstep (se 2 (by rfl) ⟨81006, by rfl⟩ : syracuseStep 216017 = 162013) B162013
theorem B216035 : Blo 143792 216035 := bstep (se 1 (by rfl) ⟨162026, by rfl⟩ : syracuseStep 216035 = 324053) B324053
theorem B216065 : Blo 143792 216065 := bstep (se 2 (by rfl) ⟨81024, by rfl⟩ : syracuseStep 216065 = 162049) B162049
theorem B216083 : Blo 143792 216083 := bstep (se 1 (by rfl) ⟨162062, by rfl⟩ : syracuseStep 216083 = 324125) B324125
theorem B150563 : Blo 143792 150563 := bstep (se 1 (by rfl) ⟨112922, by rfl⟩ : syracuseStep 150563 = 225845) B225845
theorem B216113 : Blo 143792 216113 := bstep (se 2 (by rfl) ⟨81042, by rfl⟩ : syracuseStep 216113 = 162085) B162085
theorem B216131 : Blo 143792 216131 := bstep (se 1 (by rfl) ⟨162098, by rfl⟩ : syracuseStep 216131 = 324197) B324197
theorem B248899 : Blo 143792 248899 := bstep (se 1 (by rfl) ⟨186674, by rfl⟩ : syracuseStep 248899 = 373349) B373349
theorem B183379 : Blo 143792 183379 := bstep (se 1 (by rfl) ⟨137534, by rfl⟩ : syracuseStep 183379 = 275069) B275069
theorem B216161 : Blo 143792 216161 := bstep (se 2 (by rfl) ⟨81060, by rfl⟩ : syracuseStep 216161 = 162121) B162121
theorem B216179 : Blo 143792 216179 := bstep (se 1 (by rfl) ⟨162134, by rfl⟩ : syracuseStep 216179 = 324269) B324269
theorem B216209 : Blo 143792 216209 := bstep (se 2 (by rfl) ⟨81078, by rfl⟩ : syracuseStep 216209 = 162157) B162157
theorem B216227 : Blo 143792 216227 := bstep (se 1 (by rfl) ⟨162170, by rfl⟩ : syracuseStep 216227 = 324341) B324341
theorem B183475 : Blo 143792 183475 := bstep (se 1 (by rfl) ⟨137606, by rfl⟩ : syracuseStep 183475 = 275213) B275213
theorem B216257 : Blo 143792 216257 := bstep (se 2 (by rfl) ⟨81096, by rfl⟩ : syracuseStep 216257 = 162193) B162193
theorem B412877 : Blo 143792 412877 := bstep (se 3 (by rfl) ⟨77414, by rfl⟩ : syracuseStep 412877 = 154829) B154829
theorem B249041 : Blo 143792 249041 := bstep (se 2 (by rfl) ⟨93390, by rfl⟩ : syracuseStep 249041 = 186781) B186781
theorem B216275 : Blo 143792 216275 := bstep (se 1 (by rfl) ⟨162206, by rfl⟩ : syracuseStep 216275 = 324413) B324413
theorem B216305 : Blo 143792 216305 := bstep (se 2 (by rfl) ⟨81114, by rfl⟩ : syracuseStep 216305 = 162229) B162229
theorem B216323 : Blo 143792 216323 := bstep (se 1 (by rfl) ⟨162242, by rfl⟩ : syracuseStep 216323 = 324485) B324485
theorem B216353 : Blo 143792 216353 := bstep (se 2 (by rfl) ⟨81132, by rfl⟩ : syracuseStep 216353 = 162265) B162265
theorem B216371 : Blo 143792 216371 := bstep (se 1 (by rfl) ⟨162278, by rfl⟩ : syracuseStep 216371 = 324557) B324557
theorem B216401 : Blo 143792 216401 := bstep (se 2 (by rfl) ⟨81150, by rfl⟩ : syracuseStep 216401 = 162301) B162301
theorem B249169 : Blo 143792 249169 := bstep (se 2 (by rfl) ⟨93438, by rfl⟩ : syracuseStep 249169 = 186877) B186877
theorem B216419 : Blo 143792 216419 := bstep (se 1 (by rfl) ⟨162314, by rfl⟩ : syracuseStep 216419 = 324629) B324629
theorem B314723 : Blo 143792 314723 := bstep (se 1 (by rfl) ⟨236042, by rfl⟩ : syracuseStep 314723 = 472085) B472085
theorem B511331 : Blo 143792 511331 := bstep (se 1 (by rfl) ⟨383498, by rfl⟩ : syracuseStep 511331 = 766997) B766997
theorem B249203 : Blo 143792 249203 := bstep (se 1 (by rfl) ⟨186902, by rfl⟩ : syracuseStep 249203 = 373805) B373805
theorem B216449 : Blo 143792 216449 := bstep (se 2 (by rfl) ⟨81168, by rfl⟩ : syracuseStep 216449 = 162337) B162337
theorem B413059 : Blo 143792 413059 := bstep (se 1 (by rfl) ⟨309794, by rfl⟩ : syracuseStep 413059 = 619589) B619589
theorem B6344077 : Blo 143792 6344077 := bstep (se 3 (by rfl) ⟨1189514, by rfl⟩ : syracuseStep 6344077 = 2379029) B2379029
theorem B216467 : Blo 143792 216467 := bstep (se 1 (by rfl) ⟨162350, by rfl⟩ : syracuseStep 216467 = 324701) B324701
theorem B216497 : Blo 143792 216497 := bstep (se 2 (by rfl) ⟨81186, by rfl⟩ : syracuseStep 216497 = 162373) B162373
theorem B216515 : Blo 143792 216515 := bstep (se 1 (by rfl) ⟨162386, by rfl⟩ : syracuseStep 216515 = 324773) B324773
theorem B216545 : Blo 143792 216545 := bstep (se 2 (by rfl) ⟨81204, by rfl⟩ : syracuseStep 216545 = 162409) B162409
theorem B216563 : Blo 143792 216563 := bstep (se 1 (by rfl) ⟨162422, by rfl⟩ : syracuseStep 216563 = 324845) B324845
theorem B249331 : Blo 143792 249331 := bstep (se 1 (by rfl) ⟨186998, by rfl⟩ : syracuseStep 249331 = 373997) B373997
theorem B216593 : Blo 143792 216593 := bstep (se 2 (by rfl) ⟨81222, by rfl⟩ : syracuseStep 216593 = 162445) B162445
theorem B216611 : Blo 143792 216611 := bstep (se 1 (by rfl) ⟨162458, by rfl⟩ : syracuseStep 216611 = 324917) B324917
theorem B216641 : Blo 143792 216641 := bstep (se 2 (by rfl) ⟨81240, by rfl⟩ : syracuseStep 216641 = 162481) B162481
theorem B216659 : Blo 143792 216659 := bstep (se 1 (by rfl) ⟨162494, by rfl⟩ : syracuseStep 216659 = 324989) B324989
theorem B216689 : Blo 143792 216689 := bstep (se 2 (by rfl) ⟨81258, by rfl⟩ : syracuseStep 216689 = 162517) B162517
theorem B4247153 : Blo 143792 4247153 := bstep (se 2 (by rfl) ⟨1592682, by rfl⟩ : syracuseStep 4247153 = 3185365) B3185365
theorem B216707 : Blo 143792 216707 := bstep (se 1 (by rfl) ⟨162530, by rfl⟩ : syracuseStep 216707 = 325061) B325061
theorem B216737 : Blo 143792 216737 := bstep (se 2 (by rfl) ⟨81276, by rfl⟩ : syracuseStep 216737 = 162553) B162553
theorem B183971 : Blo 143792 183971 := bstep (se 1 (by rfl) ⟨137978, by rfl⟩ : syracuseStep 183971 = 275957) B275957
theorem B216755 : Blo 143792 216755 := bstep (se 1 (by rfl) ⟨162566, by rfl⟩ : syracuseStep 216755 = 325133) B325133
theorem B216785 : Blo 143792 216785 := bstep (se 2 (by rfl) ⟨81294, by rfl⟩ : syracuseStep 216785 = 162589) B162589
theorem B216803 : Blo 143792 216803 := bstep (se 1 (by rfl) ⟨162602, by rfl⟩ : syracuseStep 216803 = 325205) B325205
theorem B216833 : Blo 143792 216833 := bstep (se 2 (by rfl) ⟨81312, by rfl⟩ : syracuseStep 216833 = 162625) B162625
theorem B216851 : Blo 143792 216851 := bstep (se 1 (by rfl) ⟨162638, by rfl⟩ : syracuseStep 216851 = 325277) B325277
theorem B216881 : Blo 143792 216881 := bstep (se 2 (by rfl) ⟨81330, by rfl⟩ : syracuseStep 216881 = 162661) B162661
theorem B216899 : Blo 143792 216899 := bstep (se 1 (by rfl) ⟨162674, by rfl⟩ : syracuseStep 216899 = 325349) B325349
theorem B216929 : Blo 143792 216929 := bstep (se 2 (by rfl) ⟨81348, by rfl⟩ : syracuseStep 216929 = 162697) B162697
theorem B413549 : Blo 143792 413549 := bstep (se 3 (by rfl) ⟨77540, by rfl⟩ : syracuseStep 413549 = 155081) B155081
theorem B216947 : Blo 143792 216947 := bstep (se 1 (by rfl) ⟨162710, by rfl⟩ : syracuseStep 216947 = 325421) B325421
theorem B216977 : Blo 143792 216977 := bstep (se 2 (by rfl) ⟨81366, by rfl⟩ : syracuseStep 216977 = 162733) B162733
theorem B216995 : Blo 143792 216995 := bstep (se 1 (by rfl) ⟨162746, by rfl⟩ : syracuseStep 216995 = 325493) B325493
theorem B348067 : Blo 143792 348067 := bstep (se 1 (by rfl) ⟨261050, by rfl⟩ : syracuseStep 348067 = 522101) B522101
theorem B217025 : Blo 143792 217025 := bstep (se 2 (by rfl) ⟨81384, by rfl⟩ : syracuseStep 217025 = 162769) B162769
theorem B217043 : Blo 143792 217043 := bstep (se 1 (by rfl) ⟨162782, by rfl⟩ : syracuseStep 217043 = 325565) B325565
theorem B217073 : Blo 143792 217073 := bstep (se 2 (by rfl) ⟨81402, by rfl⟩ : syracuseStep 217073 = 162805) B162805
theorem B217091 : Blo 143792 217091 := bstep (se 1 (by rfl) ⟨162818, by rfl⟩ : syracuseStep 217091 = 325637) B325637
theorem B217121 : Blo 143792 217121 := bstep (se 2 (by rfl) ⟨81420, by rfl⟩ : syracuseStep 217121 = 162841) B162841
theorem B217139 : Blo 143792 217139 := bstep (se 1 (by rfl) ⟨162854, by rfl⟩ : syracuseStep 217139 = 325709) B325709
theorem B217169 : Blo 143792 217169 := bstep (se 2 (by rfl) ⟨81438, by rfl⟩ : syracuseStep 217169 = 162877) B162877
theorem B217187 : Blo 143792 217187 := bstep (se 1 (by rfl) ⟨162890, by rfl⟩ : syracuseStep 217187 = 325781) B325781
theorem B217217 : Blo 143792 217217 := bstep (se 2 (by rfl) ⟨81456, by rfl⟩ : syracuseStep 217217 = 162913) B162913
theorem B217235 : Blo 143792 217235 := bstep (se 1 (by rfl) ⟨162926, by rfl⟩ : syracuseStep 217235 = 325853) B325853
theorem B217265 : Blo 143792 217265 := bstep (se 2 (by rfl) ⟨81474, by rfl⟩ : syracuseStep 217265 = 162949) B162949
theorem B217283 : Blo 143792 217283 := bstep (se 1 (by rfl) ⟨162962, by rfl⟩ : syracuseStep 217283 = 325925) B325925
theorem B217313 : Blo 143792 217313 := bstep (se 2 (by rfl) ⟨81492, by rfl⟩ : syracuseStep 217313 = 162985) B162985
theorem B217331 : Blo 143792 217331 := bstep (se 1 (by rfl) ⟨162998, by rfl⟩ : syracuseStep 217331 = 325997) B325997
theorem B217361 : Blo 143792 217361 := bstep (se 2 (by rfl) ⟨81510, by rfl⟩ : syracuseStep 217361 = 163021) B163021
theorem B217379 : Blo 143792 217379 := bstep (se 1 (by rfl) ⟨163034, by rfl⟩ : syracuseStep 217379 = 326069) B326069
theorem B217409 : Blo 143792 217409 := bstep (se 2 (by rfl) ⟨81528, by rfl⟩ : syracuseStep 217409 = 163057) B163057
theorem B217427 : Blo 143792 217427 := bstep (se 1 (by rfl) ⟨163070, by rfl⟩ : syracuseStep 217427 = 326141) B326141
theorem B184675 : Blo 143792 184675 := bstep (se 1 (by rfl) ⟨138506, by rfl⟩ : syracuseStep 184675 = 277013) B277013
theorem B217457 : Blo 143792 217457 := bstep (se 2 (by rfl) ⟨81546, by rfl⟩ : syracuseStep 217457 = 163093) B163093
theorem B217475 : Blo 143792 217475 := bstep (se 1 (by rfl) ⟨163106, by rfl⟩ : syracuseStep 217475 = 326213) B326213
theorem B217505 : Blo 143792 217505 := bstep (se 2 (by rfl) ⟨81564, by rfl⟩ : syracuseStep 217505 = 163129) B163129
theorem B217523 : Blo 143792 217523 := bstep (se 1 (by rfl) ⟨163142, by rfl⟩ : syracuseStep 217523 = 326285) B326285
theorem B184771 : Blo 143792 184771 := bstep (se 1 (by rfl) ⟨138578, by rfl⟩ : syracuseStep 184771 = 277157) B277157
theorem B217553 : Blo 143792 217553 := bstep (se 2 (by rfl) ⟨81582, by rfl⟩ : syracuseStep 217553 = 163165) B163165
theorem B217571 : Blo 143792 217571 := bstep (se 1 (by rfl) ⟨163178, by rfl⟩ : syracuseStep 217571 = 326357) B326357
theorem B217601 : Blo 143792 217601 := bstep (se 2 (by rfl) ⟨81600, by rfl⟩ : syracuseStep 217601 = 163201) B163201
theorem B217619 : Blo 143792 217619 := bstep (se 1 (by rfl) ⟨163214, by rfl⟩ : syracuseStep 217619 = 326429) B326429
theorem B217649 : Blo 143792 217649 := bstep (se 2 (by rfl) ⟨81618, by rfl⟩ : syracuseStep 217649 = 163237) B163237
theorem B217667 : Blo 143792 217667 := bstep (se 1 (by rfl) ⟨163250, by rfl⟩ : syracuseStep 217667 = 326501) B326501
theorem B217697 : Blo 143792 217697 := bstep (se 2 (by rfl) ⟨81636, by rfl⟩ : syracuseStep 217697 = 163273) B163273
theorem B217715 : Blo 143792 217715 := bstep (se 1 (by rfl) ⟨163286, by rfl⟩ : syracuseStep 217715 = 326573) B326573
theorem B217745 : Blo 143792 217745 := bstep (se 2 (by rfl) ⟨81654, by rfl⟩ : syracuseStep 217745 = 163309) B163309
theorem B217763 : Blo 143792 217763 := bstep (se 1 (by rfl) ⟨163322, by rfl⟩ : syracuseStep 217763 = 326645) B326645
theorem B217793 : Blo 143792 217793 := bstep (se 2 (by rfl) ⟨81672, by rfl⟩ : syracuseStep 217793 = 163345) B163345
theorem B217811 : Blo 143792 217811 := bstep (se 1 (by rfl) ⟨163358, by rfl⟩ : syracuseStep 217811 = 326717) B326717
theorem B217841 : Blo 143792 217841 := bstep (se 2 (by rfl) ⟨81690, by rfl⟩ : syracuseStep 217841 = 163381) B163381
theorem B217859 : Blo 143792 217859 := bstep (se 1 (by rfl) ⟨163394, by rfl⟩ : syracuseStep 217859 = 326789) B326789
theorem B217889 : Blo 143792 217889 := bstep (se 2 (by rfl) ⟨81708, by rfl⟩ : syracuseStep 217889 = 163417) B163417
theorem B217907 : Blo 143792 217907 := bstep (se 1 (by rfl) ⟨163430, by rfl⟩ : syracuseStep 217907 = 326861) B326861
theorem B217937 : Blo 143792 217937 := bstep (se 2 (by rfl) ⟨81726, by rfl⟩ : syracuseStep 217937 = 163453) B163453
theorem B217955 : Blo 143792 217955 := bstep (se 1 (by rfl) ⟨163466, by rfl⟩ : syracuseStep 217955 = 326933) B326933
theorem B1561457 : Blo 143792 1561457 := bstep (se 2 (by rfl) ⟨585546, by rfl⟩ : syracuseStep 1561457 = 1171093) B1171093
theorem B217985 : Blo 143792 217985 := bstep (se 2 (by rfl) ⟨81744, by rfl⟩ : syracuseStep 217985 = 163489) B163489
theorem B1102733 : Blo 143792 1102733 := bstep (se 3 (by rfl) ⟨206762, by rfl⟩ : syracuseStep 1102733 = 413525) B413525
theorem B218003 : Blo 143792 218003 := bstep (se 1 (by rfl) ⟨163502, by rfl⟩ : syracuseStep 218003 = 327005) B327005
theorem B218033 : Blo 143792 218033 := bstep (se 2 (by rfl) ⟨81762, by rfl⟩ : syracuseStep 218033 = 163525) B163525
theorem B185267 : Blo 143792 185267 := bstep (se 1 (by rfl) ⟨138950, by rfl⟩ : syracuseStep 185267 = 277901) B277901
theorem B218051 : Blo 143792 218051 := bstep (se 1 (by rfl) ⟨163538, by rfl⟩ : syracuseStep 218051 = 327077) B327077
theorem B218081 : Blo 143792 218081 := bstep (se 2 (by rfl) ⟨81780, by rfl⟩ : syracuseStep 218081 = 163561) B163561
theorem B218099 : Blo 143792 218099 := bstep (se 1 (by rfl) ⟨163574, by rfl⟩ : syracuseStep 218099 = 327149) B327149
theorem B414733 : Blo 143792 414733 := bstep (se 3 (by rfl) ⟨77762, by rfl⟩ : syracuseStep 414733 = 155525) B155525
theorem B218129 : Blo 143792 218129 := bstep (se 2 (by rfl) ⟨81798, by rfl⟩ : syracuseStep 218129 = 163597) B163597
theorem B218147 : Blo 143792 218147 := bstep (se 1 (by rfl) ⟨163610, by rfl⟩ : syracuseStep 218147 = 327221) B327221
theorem B939043 : Blo 143792 939043 := bstep (se 1 (by rfl) ⟨704282, by rfl⟩ : syracuseStep 939043 = 1408565) B1408565
theorem B709667 : Blo 143792 709667 := bstep (se 1 (by rfl) ⟨532250, by rfl⟩ : syracuseStep 709667 = 1064501) B1064501
theorem B218177 : Blo 143792 218177 := bstep (se 2 (by rfl) ⟨81816, by rfl⟩ : syracuseStep 218177 = 163633) B163633
theorem B218195 : Blo 143792 218195 := bstep (se 1 (by rfl) ⟨163646, by rfl⟩ : syracuseStep 218195 = 327293) B327293
theorem B218225 : Blo 143792 218225 := bstep (se 2 (by rfl) ⟨81834, by rfl⟩ : syracuseStep 218225 = 163669) B163669
theorem B218243 : Blo 143792 218243 := bstep (se 1 (by rfl) ⟨163682, by rfl⟩ : syracuseStep 218243 = 327365) B327365
theorem B218273 : Blo 143792 218273 := bstep (se 2 (by rfl) ⟨81852, by rfl⟩ : syracuseStep 218273 = 163705) B163705
theorem B218291 : Blo 143792 218291 := bstep (se 1 (by rfl) ⟨163718, by rfl⟩ : syracuseStep 218291 = 327437) B327437
theorem B840901 : Blo 143792 840901 := bstep (se 4 (by rfl) ⟨78834, by rfl⟩ : syracuseStep 840901 = 157669) B157669
theorem B218321 : Blo 143792 218321 := bstep (se 2 (by rfl) ⟨81870, by rfl⟩ : syracuseStep 218321 = 163741) B163741
theorem B939235 : Blo 143792 939235 := bstep (se 1 (by rfl) ⟨704426, by rfl⟩ : syracuseStep 939235 = 1408853) B1408853
theorem B218339 : Blo 143792 218339 := bstep (se 1 (by rfl) ⟨163754, by rfl⟩ : syracuseStep 218339 = 327509) B327509
theorem B218369 : Blo 143792 218369 := bstep (se 2 (by rfl) ⟨81888, by rfl⟩ : syracuseStep 218369 = 163777) B163777
theorem B218387 : Blo 143792 218387 := bstep (se 1 (by rfl) ⟨163790, by rfl⟩ : syracuseStep 218387 = 327581) B327581
theorem B218417 : Blo 143792 218417 := bstep (se 2 (by rfl) ⟨81906, by rfl⟩ : syracuseStep 218417 = 163813) B163813
theorem B218435 : Blo 143792 218435 := bstep (se 1 (by rfl) ⟨163826, by rfl⟩ : syracuseStep 218435 = 327653) B327653
theorem B218465 : Blo 143792 218465 := bstep (se 2 (by rfl) ⟨81924, by rfl⟩ : syracuseStep 218465 = 163849) B163849
theorem B742769 : Blo 143792 742769 := bstep (se 2 (by rfl) ⟨278538, by rfl⟩ : syracuseStep 742769 = 557077) B557077
theorem B218483 : Blo 143792 218483 := bstep (se 1 (by rfl) ⟨163862, by rfl⟩ : syracuseStep 218483 = 327725) B327725
theorem B218513 : Blo 143792 218513 := bstep (se 2 (by rfl) ⟨81942, by rfl⟩ : syracuseStep 218513 = 163885) B163885
theorem B218531 : Blo 143792 218531 := bstep (se 1 (by rfl) ⟨163898, by rfl⟩ : syracuseStep 218531 = 327797) B327797
theorem B218561 : Blo 143792 218561 := bstep (se 2 (by rfl) ⟨81960, by rfl⟩ : syracuseStep 218561 = 163921) B163921
theorem B218579 : Blo 143792 218579 := bstep (se 1 (by rfl) ⟨163934, by rfl⟩ : syracuseStep 218579 = 327869) B327869
theorem B349681 : Blo 143792 349681 := bstep (se 2 (by rfl) ⟨131130, by rfl⟩ : syracuseStep 349681 = 262261) B262261
theorem B218609 : Blo 143792 218609 := bstep (se 2 (by rfl) ⟨81978, by rfl⟩ : syracuseStep 218609 = 163957) B163957
theorem B218627 : Blo 143792 218627 := bstep (se 1 (by rfl) ⟨163970, by rfl⟩ : syracuseStep 218627 = 327941) B327941
theorem B218657 : Blo 143792 218657 := bstep (se 2 (by rfl) ⟨81996, by rfl⟩ : syracuseStep 218657 = 163993) B163993
theorem B218675 : Blo 143792 218675 := bstep (se 1 (by rfl) ⟨164006, by rfl⟩ : syracuseStep 218675 = 328013) B328013
theorem B218705 : Blo 143792 218705 := bstep (se 2 (by rfl) ⟨82014, by rfl⟩ : syracuseStep 218705 = 164029) B164029
theorem B317009 : Blo 143792 317009 := bstep (se 2 (by rfl) ⟨118878, by rfl⟩ : syracuseStep 317009 = 237757) B237757
theorem B218723 : Blo 143792 218723 := bstep (se 1 (by rfl) ⟨164042, by rfl⟩ : syracuseStep 218723 = 328085) B328085
theorem B185971 : Blo 143792 185971 := bstep (se 1 (by rfl) ⟨139478, by rfl⟩ : syracuseStep 185971 = 278957) B278957
theorem B218753 : Blo 143792 218753 := bstep (se 2 (by rfl) ⟨82032, by rfl⟩ : syracuseStep 218753 = 164065) B164065
theorem B284305 : Blo 143792 284305 := bstep (se 2 (by rfl) ⟨106614, by rfl⟩ : syracuseStep 284305 = 213229) B213229
theorem B218771 : Blo 143792 218771 := bstep (se 1 (by rfl) ⟨164078, by rfl⟩ : syracuseStep 218771 = 328157) B328157
theorem B218801 : Blo 143792 218801 := bstep (se 2 (by rfl) ⟨82050, by rfl⟩ : syracuseStep 218801 = 164101) B164101
theorem B218803 : Blo 143792 218803 := bstep (se 1 (by rfl) ⟨164102, by rfl⟩ : syracuseStep 218803 = 328205) B328205
theorem B218819 : Blo 143792 218819 := bstep (se 1 (by rfl) ⟨164114, by rfl⟩ : syracuseStep 218819 = 328229) B328229
theorem B186067 : Blo 143792 186067 := bstep (se 1 (by rfl) ⟨139550, by rfl⟩ : syracuseStep 186067 = 279101) B279101
theorem B218849 : Blo 143792 218849 := bstep (se 2 (by rfl) ⟨82068, by rfl⟩ : syracuseStep 218849 = 164137) B164137
theorem B218867 : Blo 143792 218867 := bstep (se 1 (by rfl) ⟨164150, by rfl⟩ : syracuseStep 218867 = 328301) B328301
theorem B218897 : Blo 143792 218897 := bstep (se 2 (by rfl) ⟨82086, by rfl⟩ : syracuseStep 218897 = 164173) B164173
theorem B218915 : Blo 143792 218915 := bstep (se 1 (by rfl) ⟨164186, by rfl⟩ : syracuseStep 218915 = 328373) B328373
theorem B907057 : Blo 143792 907057 := bstep (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) B680293
theorem B218945 : Blo 143792 218945 := bstep (se 2 (by rfl) ⟨82104, by rfl⟩ : syracuseStep 218945 = 164209) B164209
theorem B218963 : Blo 143792 218963 := bstep (se 1 (by rfl) ⟨164222, by rfl⟩ : syracuseStep 218963 = 328445) B328445
theorem B546659 : Blo 143792 546659 := bstep (se 1 (by rfl) ⟨409994, by rfl⟩ : syracuseStep 546659 = 819989) B819989
theorem B218993 : Blo 143792 218993 := bstep (se 2 (by rfl) ⟨82122, by rfl⟩ : syracuseStep 218993 = 164245) B164245
theorem B219011 : Blo 143792 219011 := bstep (se 1 (by rfl) ⟨164258, by rfl⟩ : syracuseStep 219011 = 328517) B328517
theorem B219041 : Blo 143792 219041 := bstep (se 2 (by rfl) ⟨82140, by rfl⟩ : syracuseStep 219041 = 164281) B164281
theorem B219059 : Blo 143792 219059 := bstep (se 1 (by rfl) ⟨164294, by rfl⟩ : syracuseStep 219059 = 328589) B328589
theorem B219089 : Blo 143792 219089 := bstep (se 2 (by rfl) ⟨82158, by rfl⟩ : syracuseStep 219089 = 164317) B164317
theorem B219107 : Blo 143792 219107 := bstep (se 1 (by rfl) ⟨164330, by rfl⟩ : syracuseStep 219107 = 328661) B328661
theorem B219137 : Blo 143792 219137 := bstep (se 2 (by rfl) ⟨82176, by rfl⟩ : syracuseStep 219137 = 164353) B164353
theorem B940045 : Blo 143792 940045 := bstep (se 3 (by rfl) ⟨176258, by rfl⟩ : syracuseStep 940045 = 352517) B352517
theorem B219155 : Blo 143792 219155 := bstep (se 1 (by rfl) ⟨164366, by rfl⟩ : syracuseStep 219155 = 328733) B328733
theorem B415793 : Blo 143792 415793 := bstep (se 2 (by rfl) ⟨155922, by rfl⟩ : syracuseStep 415793 = 311845) B311845
theorem B219185 : Blo 143792 219185 := bstep (se 2 (by rfl) ⟨82194, by rfl⟩ : syracuseStep 219185 = 164389) B164389
theorem B153667 : Blo 143792 153667 := bstep (se 1 (by rfl) ⟨115250, by rfl⟩ : syracuseStep 153667 = 230501) B230501
theorem B219203 : Blo 143792 219203 := bstep (se 1 (by rfl) ⟨164402, by rfl⟩ : syracuseStep 219203 = 328805) B328805
theorem B219233 : Blo 143792 219233 := bstep (se 2 (by rfl) ⟨82212, by rfl⟩ : syracuseStep 219233 = 164425) B164425
theorem B219251 : Blo 143792 219251 := bstep (se 1 (by rfl) ⟨164438, by rfl⟩ : syracuseStep 219251 = 328877) B328877
theorem B219281 : Blo 143792 219281 := bstep (se 2 (by rfl) ⟨82230, by rfl⟩ : syracuseStep 219281 = 164461) B164461
theorem B219299 : Blo 143792 219299 := bstep (se 1 (by rfl) ⟨164474, by rfl⟩ : syracuseStep 219299 = 328949) B328949
theorem B219329 : Blo 143792 219329 := bstep (se 2 (by rfl) ⟨82248, by rfl⟩ : syracuseStep 219329 = 164497) B164497
theorem B186563 : Blo 143792 186563 := bstep (se 1 (by rfl) ⟨139922, by rfl⟩ : syracuseStep 186563 = 279845) B279845
theorem B219347 : Blo 143792 219347 := bstep (se 1 (by rfl) ⟨164510, by rfl⟩ : syracuseStep 219347 = 329021) B329021
theorem B219377 : Blo 143792 219377 := bstep (se 2 (by rfl) ⟨82266, by rfl⟩ : syracuseStep 219377 = 164533) B164533
theorem B219395 : Blo 143792 219395 := bstep (se 1 (by rfl) ⟨164546, by rfl⟩ : syracuseStep 219395 = 329093) B329093
theorem B219425 : Blo 143792 219425 := bstep (se 2 (by rfl) ⟨82284, by rfl⟩ : syracuseStep 219425 = 164569) B164569
theorem B219443 : Blo 143792 219443 := bstep (se 1 (by rfl) ⟨164582, by rfl⟩ : syracuseStep 219443 = 329165) B329165
theorem B252227 : Blo 143792 252227 := bstep (se 1 (by rfl) ⟨189170, by rfl⟩ : syracuseStep 252227 = 378341) B378341
theorem B219473 : Blo 143792 219473 := bstep (se 2 (by rfl) ⟨82302, by rfl⟩ : syracuseStep 219473 = 164605) B164605
theorem B219491 : Blo 143792 219491 := bstep (se 1 (by rfl) ⟨164618, by rfl⟩ : syracuseStep 219491 = 329237) B329237
theorem B219521 : Blo 143792 219521 := bstep (se 2 (by rfl) ⟨82320, by rfl⟩ : syracuseStep 219521 = 164641) B164641
theorem B219539 : Blo 143792 219539 := bstep (se 1 (by rfl) ⟨164654, by rfl⟩ : syracuseStep 219539 = 329309) B329309
theorem B219569 : Blo 143792 219569 := bstep (se 2 (by rfl) ⟨82338, by rfl⟩ : syracuseStep 219569 = 164677) B164677
theorem B219587 : Blo 143792 219587 := bstep (se 1 (by rfl) ⟨164690, by rfl⟩ : syracuseStep 219587 = 329381) B329381
theorem B219617 : Blo 143792 219617 := bstep (se 2 (by rfl) ⟨82356, by rfl⟩ : syracuseStep 219617 = 164713) B164713
theorem B219635 : Blo 143792 219635 := bstep (se 1 (by rfl) ⟨164726, by rfl⟩ : syracuseStep 219635 = 329453) B329453
theorem B219665 : Blo 143792 219665 := bstep (se 2 (by rfl) ⟨82374, by rfl⟩ : syracuseStep 219665 = 164749) B164749
theorem B219683 : Blo 143792 219683 := bstep (se 1 (by rfl) ⟨164762, by rfl⟩ : syracuseStep 219683 = 329525) B329525
theorem B2087477 : Blo 143792 2087477 := bstep (se 5 (by rfl) ⟨97850, by rfl⟩ : syracuseStep 2087477 = 195701) B195701
theorem B219713 : Blo 143792 219713 := bstep (se 2 (by rfl) ⟨82392, by rfl⟩ : syracuseStep 219713 = 164785) B164785
theorem B219731 : Blo 143792 219731 := bstep (se 1 (by rfl) ⟨164798, by rfl⟩ : syracuseStep 219731 = 329597) B329597
theorem B219761 : Blo 143792 219761 := bstep (se 2 (by rfl) ⟨82410, by rfl⟩ : syracuseStep 219761 = 164821) B164821
theorem B219779 : Blo 143792 219779 := bstep (se 1 (by rfl) ⟨164834, by rfl⟩ : syracuseStep 219779 = 329669) B329669
theorem B219809 : Blo 143792 219809 := bstep (se 2 (by rfl) ⟨82428, by rfl⟩ : syracuseStep 219809 = 164857) B164857
theorem B219827 : Blo 143792 219827 := bstep (se 1 (by rfl) ⟨164870, by rfl⟩ : syracuseStep 219827 = 329741) B329741
theorem B416465 : Blo 143792 416465 := bstep (se 2 (by rfl) ⟨156174, by rfl⟩ : syracuseStep 416465 = 312349) B312349
theorem B219857 : Blo 143792 219857 := bstep (se 2 (by rfl) ⟨82446, by rfl⟩ : syracuseStep 219857 = 164893) B164893
theorem B219875 : Blo 143792 219875 := bstep (se 1 (by rfl) ⟨164906, by rfl⟩ : syracuseStep 219875 = 329813) B329813
theorem B1596145 : Blo 143792 1596145 := bstep (se 2 (by rfl) ⟨598554, by rfl⟩ : syracuseStep 1596145 = 1197109) B1197109
theorem B219905 : Blo 143792 219905 := bstep (se 2 (by rfl) ⟨82464, by rfl⟩ : syracuseStep 219905 = 164929) B164929
theorem B219923 : Blo 143792 219923 := bstep (se 1 (by rfl) ⟨164942, by rfl⟩ : syracuseStep 219923 = 329885) B329885
theorem B744227 : Blo 143792 744227 := bstep (se 1 (by rfl) ⟨558170, by rfl⟩ : syracuseStep 744227 = 1116341) B1116341
theorem B219953 : Blo 143792 219953 := bstep (se 2 (by rfl) ⟨82482, by rfl⟩ : syracuseStep 219953 = 164965) B164965
theorem B219971 : Blo 143792 219971 := bstep (se 1 (by rfl) ⟨164978, by rfl⟩ : syracuseStep 219971 = 329957) B329957
theorem B547661 : Blo 143792 547661 := bstep (se 3 (by rfl) ⟨102686, by rfl⟩ : syracuseStep 547661 = 205373) B205373
theorem B220001 : Blo 143792 220001 := bstep (se 2 (by rfl) ⟨82500, by rfl⟩ : syracuseStep 220001 = 165001) B165001
theorem B1858403 : Blo 143792 1858403 := bstep (se 1 (by rfl) ⟨1393802, by rfl⟩ : syracuseStep 1858403 = 2787605) B2787605
theorem B220019 : Blo 143792 220019 := bstep (se 1 (by rfl) ⟨165014, by rfl⟩ : syracuseStep 220019 = 330029) B330029
theorem B220049 : Blo 143792 220049 := bstep (se 2 (by rfl) ⟨82518, by rfl⟩ : syracuseStep 220049 = 165037) B165037
theorem B220067 : Blo 143792 220067 := bstep (se 1 (by rfl) ⟨165050, by rfl⟩ : syracuseStep 220067 = 330101) B330101
theorem B220097 : Blo 143792 220097 := bstep (se 2 (by rfl) ⟨82536, by rfl⟩ : syracuseStep 220097 = 165073) B165073
theorem B220115 : Blo 143792 220115 := bstep (se 1 (by rfl) ⟨165086, by rfl⟩ : syracuseStep 220115 = 330173) B330173
theorem B220145 : Blo 143792 220145 := bstep (se 2 (by rfl) ⟨82554, by rfl⟩ : syracuseStep 220145 = 165109) B165109
theorem B220163 : Blo 143792 220163 := bstep (se 1 (by rfl) ⟨165122, by rfl⟩ : syracuseStep 220163 = 330245) B330245
theorem B220193 : Blo 143792 220193 := bstep (se 2 (by rfl) ⟨82572, by rfl⟩ : syracuseStep 220193 = 165145) B165145
theorem B220211 : Blo 143792 220211 := bstep (se 1 (by rfl) ⟨165158, by rfl⟩ : syracuseStep 220211 = 330317) B330317
theorem B220241 : Blo 143792 220241 := bstep (se 2 (by rfl) ⟨82590, by rfl⟩ : syracuseStep 220241 = 165181) B165181
theorem B220259 : Blo 143792 220259 := bstep (se 1 (by rfl) ⟨165194, by rfl⟩ : syracuseStep 220259 = 330389) B330389
theorem B220289 : Blo 143792 220289 := bstep (se 2 (by rfl) ⟨82608, by rfl⟩ : syracuseStep 220289 = 165217) B165217
theorem B220307 : Blo 143792 220307 := bstep (se 1 (by rfl) ⟨165230, by rfl⟩ : syracuseStep 220307 = 330461) B330461
theorem B220337 : Blo 143792 220337 := bstep (se 2 (by rfl) ⟨82626, by rfl⟩ : syracuseStep 220337 = 165253) B165253
theorem B220355 : Blo 143792 220355 := bstep (se 1 (by rfl) ⟨165266, by rfl⟩ : syracuseStep 220355 = 330533) B330533
theorem B2579653 : Blo 143792 2579653 := bstep (se 4 (by rfl) ⟨241842, by rfl⟩ : syracuseStep 2579653 = 483685) B483685
theorem B220385 : Blo 143792 220385 := bstep (se 2 (by rfl) ⟨82644, by rfl⟩ : syracuseStep 220385 = 165289) B165289
theorem B220403 : Blo 143792 220403 := bstep (se 1 (by rfl) ⟨165302, by rfl⟩ : syracuseStep 220403 = 330605) B330605
theorem B875789 : Blo 143792 875789 := bstep (se 3 (by rfl) ⟨164210, by rfl⟩ : syracuseStep 875789 = 328421) B328421
theorem B220433 : Blo 143792 220433 := bstep (se 2 (by rfl) ⟨82662, by rfl⟩ : syracuseStep 220433 = 165325) B165325
theorem B220451 : Blo 143792 220451 := bstep (se 1 (by rfl) ⟨165338, by rfl⟩ : syracuseStep 220451 = 330677) B330677
theorem B220481 : Blo 143792 220481 := bstep (se 2 (by rfl) ⟨82680, by rfl⟩ : syracuseStep 220481 = 165361) B165361
theorem B220499 : Blo 143792 220499 := bstep (se 1 (by rfl) ⟨165374, by rfl⟩ : syracuseStep 220499 = 330749) B330749
theorem B220529 : Blo 143792 220529 := bstep (se 2 (by rfl) ⟨82698, by rfl⟩ : syracuseStep 220529 = 165397) B165397
theorem B220547 : Blo 143792 220547 := bstep (se 1 (by rfl) ⟨165410, by rfl⟩ : syracuseStep 220547 = 330821) B330821
theorem B220577 : Blo 143792 220577 := bstep (se 2 (by rfl) ⟨82716, by rfl⟩ : syracuseStep 220577 = 165433) B165433
theorem B220595 : Blo 143792 220595 := bstep (se 1 (by rfl) ⟨165446, by rfl⟩ : syracuseStep 220595 = 330893) B330893
theorem B220625 : Blo 143792 220625 := bstep (se 2 (by rfl) ⟨82734, by rfl⟩ : syracuseStep 220625 = 165469) B165469
theorem B417251 : Blo 143792 417251 := bstep (se 1 (by rfl) ⟨312938, by rfl⟩ : syracuseStep 417251 = 625877) B625877
theorem B220643 : Blo 143792 220643 := bstep (se 1 (by rfl) ⟨165482, by rfl⟩ : syracuseStep 220643 = 330965) B330965
theorem B220673 : Blo 143792 220673 := bstep (se 2 (by rfl) ⟨82752, by rfl⟩ : syracuseStep 220673 = 165505) B165505
theorem B220691 : Blo 143792 220691 := bstep (se 1 (by rfl) ⟨165518, by rfl⟩ : syracuseStep 220691 = 331037) B331037
theorem B220721 : Blo 143792 220721 := bstep (se 2 (by rfl) ⟨82770, by rfl⟩ : syracuseStep 220721 = 165541) B165541
theorem B220739 : Blo 143792 220739 := bstep (se 1 (by rfl) ⟨165554, by rfl⟩ : syracuseStep 220739 = 331109) B331109
theorem B745037 : Blo 143792 745037 := bstep (se 3 (by rfl) ⟨139694, by rfl⟩ : syracuseStep 745037 = 279389) B279389
theorem B220769 : Blo 143792 220769 := bstep (se 2 (by rfl) ⟨82788, by rfl⟩ : syracuseStep 220769 = 165577) B165577
theorem B220787 : Blo 143792 220787 := bstep (se 1 (by rfl) ⟨165590, by rfl⟩ : syracuseStep 220787 = 331181) B331181
theorem B220817 : Blo 143792 220817 := bstep (se 2 (by rfl) ⟨82806, by rfl⟩ : syracuseStep 220817 = 165613) B165613
theorem B220835 : Blo 143792 220835 := bstep (se 1 (by rfl) ⟨165626, by rfl⟩ : syracuseStep 220835 = 331253) B331253
theorem B220865 : Blo 143792 220865 := bstep (se 2 (by rfl) ⟨82824, by rfl⟩ : syracuseStep 220865 = 165649) B165649
theorem B220883 : Blo 143792 220883 := bstep (se 1 (by rfl) ⟨165662, by rfl⟩ : syracuseStep 220883 = 331325) B331325
theorem B1105649 : Blo 143792 1105649 := bstep (se 2 (by rfl) ⟨414618, by rfl⟩ : syracuseStep 1105649 = 829237) B829237
theorem B220913 : Blo 143792 220913 := bstep (se 2 (by rfl) ⟨82842, by rfl⟩ : syracuseStep 220913 = 165685) B165685
theorem B220931 : Blo 143792 220931 := bstep (se 1 (by rfl) ⟨165698, by rfl⟩ : syracuseStep 220931 = 331397) B331397
theorem B220961 : Blo 143792 220961 := bstep (se 2 (by rfl) ⟨82860, by rfl⟩ : syracuseStep 220961 = 165721) B165721
theorem B417581 : Blo 143792 417581 := bstep (se 3 (by rfl) ⟨78296, by rfl⟩ : syracuseStep 417581 = 156593) B156593
theorem B220979 : Blo 143792 220979 := bstep (se 1 (by rfl) ⟨165734, by rfl⟩ : syracuseStep 220979 = 331469) B331469
theorem B221009 : Blo 143792 221009 := bstep (se 2 (by rfl) ⟨82878, by rfl⟩ : syracuseStep 221009 = 165757) B165757
theorem B221027 : Blo 143792 221027 := bstep (se 1 (by rfl) ⟨165770, by rfl⟩ : syracuseStep 221027 = 331541) B331541
theorem B417649 : Blo 143792 417649 := bstep (se 2 (by rfl) ⟨156618, by rfl⟩ : syracuseStep 417649 = 313237) B313237
theorem B221057 : Blo 143792 221057 := bstep (se 2 (by rfl) ⟨82896, by rfl⟩ : syracuseStep 221057 = 165793) B165793
theorem B221075 : Blo 143792 221075 := bstep (se 1 (by rfl) ⟨165806, by rfl⟩ : syracuseStep 221075 = 331613) B331613
theorem B221105 : Blo 143792 221105 := bstep (se 2 (by rfl) ⟨82914, by rfl⟩ : syracuseStep 221105 = 165829) B165829
theorem B221123 : Blo 143792 221123 := bstep (se 1 (by rfl) ⟨165842, by rfl⟩ : syracuseStep 221123 = 331685) B331685
theorem B221153 : Blo 143792 221153 := bstep (se 2 (by rfl) ⟨82932, by rfl⟩ : syracuseStep 221153 = 165865) B165865
theorem B221171 : Blo 143792 221171 := bstep (se 1 (by rfl) ⟨165878, by rfl⟩ : syracuseStep 221171 = 331757) B331757
theorem B221201 : Blo 143792 221201 := bstep (se 2 (by rfl) ⟨82950, by rfl⟩ : syracuseStep 221201 = 165901) B165901
theorem B221219 : Blo 143792 221219 := bstep (se 1 (by rfl) ⟨165914, by rfl⟩ : syracuseStep 221219 = 331829) B331829
theorem B221249 : Blo 143792 221249 := bstep (se 2 (by rfl) ⟨82968, by rfl⟩ : syracuseStep 221249 = 165937) B165937
theorem B221267 : Blo 143792 221267 := bstep (se 1 (by rfl) ⟨165950, by rfl⟩ : syracuseStep 221267 = 331901) B331901
theorem B221297 : Blo 143792 221297 := bstep (se 2 (by rfl) ⟨82986, by rfl⟩ : syracuseStep 221297 = 165973) B165973
theorem B417923 : Blo 143792 417923 := bstep (se 1 (by rfl) ⟨313442, by rfl⟩ : syracuseStep 417923 = 626885) B626885
theorem B221315 : Blo 143792 221315 := bstep (se 1 (by rfl) ⟨165986, by rfl⟩ : syracuseStep 221315 = 331973) B331973
theorem B221345 : Blo 143792 221345 := bstep (se 2 (by rfl) ⟨83004, by rfl⟩ : syracuseStep 221345 = 166009) B166009
theorem B221363 : Blo 143792 221363 := bstep (se 1 (by rfl) ⟨166022, by rfl⟩ : syracuseStep 221363 = 332045) B332045
theorem B221393 : Blo 143792 221393 := bstep (se 2 (by rfl) ⟨83022, by rfl⟩ : syracuseStep 221393 = 166045) B166045
theorem B221411 : Blo 143792 221411 := bstep (se 1 (by rfl) ⟨166058, by rfl⟩ : syracuseStep 221411 = 332117) B332117
theorem B221441 : Blo 143792 221441 := bstep (se 2 (by rfl) ⟨83040, by rfl⟩ : syracuseStep 221441 = 166081) B166081
theorem B221459 : Blo 143792 221459 := bstep (se 1 (by rfl) ⟨166094, by rfl⟩ : syracuseStep 221459 = 332189) B332189
theorem B221489 : Blo 143792 221489 := bstep (se 2 (by rfl) ⟨83058, by rfl⟩ : syracuseStep 221489 = 166117) B166117
theorem B221507 : Blo 143792 221507 := bstep (se 1 (by rfl) ⟨166130, by rfl⟩ : syracuseStep 221507 = 332261) B332261
theorem B221537 : Blo 143792 221537 := bstep (se 2 (by rfl) ⟨83076, by rfl⟩ : syracuseStep 221537 = 166153) B166153
theorem B221555 : Blo 143792 221555 := bstep (se 1 (by rfl) ⟨166166, by rfl⟩ : syracuseStep 221555 = 332333) B332333
theorem B221585 : Blo 143792 221585 := bstep (se 2 (by rfl) ⟨83094, by rfl⟩ : syracuseStep 221585 = 166189) B166189
theorem B221603 : Blo 143792 221603 := bstep (se 1 (by rfl) ⟨166202, by rfl⟩ : syracuseStep 221603 = 332405) B332405
theorem B1597877 : Blo 143792 1597877 := bstep (se 5 (by rfl) ⟨74900, by rfl⟩ : syracuseStep 1597877 = 149801) B149801
theorem B221633 : Blo 143792 221633 := bstep (se 2 (by rfl) ⟨83112, by rfl⟩ : syracuseStep 221633 = 166225) B166225
theorem B221651 : Blo 143792 221651 := bstep (se 1 (by rfl) ⟨166238, by rfl⟩ : syracuseStep 221651 = 332477) B332477
theorem B221681 : Blo 143792 221681 := bstep (se 2 (by rfl) ⟨83130, by rfl⟩ : syracuseStep 221681 = 166261) B166261
theorem B221843 : Blo 143792 221843 := bstep (se 1 (by rfl) ⟨166382, by rfl⟩ : syracuseStep 221843 = 332765) B332765
theorem B549773 : Blo 143792 549773 := bstep (se 3 (by rfl) ⟨103082, by rfl⟩ : syracuseStep 549773 = 206165) B206165
theorem B418765 : Blo 143792 418765 := bstep (se 3 (by rfl) ⟨78518, by rfl⟩ : syracuseStep 418765 = 157037) B157037
theorem B615437 : Blo 143792 615437 := bstep (se 3 (by rfl) ⟨115394, by rfl⟩ : syracuseStep 615437 = 230789) B230789
theorem B353315 : Blo 143792 353315 := bstep (se 1 (by rfl) ⟨264986, by rfl⟩ : syracuseStep 353315 = 529973) B529973
theorem B418925 : Blo 143792 418925 := bstep (se 3 (by rfl) ⟨78548, by rfl⟩ : syracuseStep 418925 = 157097) B157097
theorem B419107 : Blo 143792 419107 := bstep (se 1 (by rfl) ⟨314330, by rfl⟩ : syracuseStep 419107 = 628661) B628661
theorem B222689 : Blo 143792 222689 := bstep (se 2 (by rfl) ⟨83508, by rfl⟩ : syracuseStep 222689 = 167017) B167017
theorem B3630563 : Blo 143792 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B157187 : Blo 143792 157187 := bstep (se 1 (by rfl) ⟨117890, by rfl⟩ : syracuseStep 157187 = 235781) B235781
theorem B550577 : Blo 143792 550577 := bstep (se 2 (by rfl) ⟨206466, by rfl⟩ : syracuseStep 550577 = 412933) B412933
theorem B353987 : Blo 143792 353987 := bstep (se 1 (by rfl) ⟨265490, by rfl⟩ : syracuseStep 353987 = 530981) B530981
theorem B583537 : Blo 143792 583537 := bstep (se 2 (by rfl) ⟨218826, by rfl⟩ : syracuseStep 583537 = 437653) B437653
theorem B780209 : Blo 143792 780209 := bstep (se 2 (by rfl) ⟨292578, by rfl⟩ : syracuseStep 780209 = 585157) B585157
theorem B354257 : Blo 143792 354257 := bstep (se 2 (by rfl) ⟨132846, by rfl⟩ : syracuseStep 354257 = 265693) B265693
theorem B354449 : Blo 143792 354449 := bstep (se 2 (by rfl) ⟨132918, by rfl⟩ : syracuseStep 354449 = 265837) B265837
theorem B354545 : Blo 143792 354545 := bstep (se 2 (by rfl) ⟨132954, by rfl⟩ : syracuseStep 354545 = 265909) B265909
theorem B551245 : Blo 143792 551245 := bstep (se 3 (by rfl) ⟨103358, by rfl⟩ : syracuseStep 551245 = 206717) B206717
theorem B747953 : Blo 143792 747953 := bstep (se 2 (by rfl) ⟨280482, by rfl⟩ : syracuseStep 747953 = 560965) B560965
theorem B485837 : Blo 143792 485837 := bstep (se 3 (by rfl) ⟨91094, by rfl⟩ : syracuseStep 485837 = 182189) B182189
theorem B485891 : Blo 143792 485891 := bstep (se 1 (by rfl) ⟨364418, by rfl⟩ : syracuseStep 485891 = 728837) B728837
theorem B387629 : Blo 143792 387629 := bstep (se 3 (by rfl) ⟨72680, by rfl⟩ : syracuseStep 387629 = 145361) B145361
theorem B420497 : Blo 143792 420497 := bstep (se 2 (by rfl) ⟨157686, by rfl⟩ : syracuseStep 420497 = 315373) B315373
theorem B223955 : Blo 143792 223955 := bstep (se 1 (by rfl) ⟨167966, by rfl⟩ : syracuseStep 223955 = 335933) B335933
theorem B486161 : Blo 143792 486161 := bstep (se 2 (by rfl) ⟨182310, by rfl⟩ : syracuseStep 486161 = 364621) B364621
theorem B453539 : Blo 143792 453539 := bstep (se 1 (by rfl) ⟨340154, by rfl⟩ : syracuseStep 453539 = 680309) B680309
theorem B552035 : Blo 143792 552035 := bstep (se 1 (by rfl) ⟨414026, by rfl⟩ : syracuseStep 552035 = 828053) B828053
theorem B945413 : Blo 143792 945413 := bstep (se 4 (by rfl) ⟨88632, by rfl⟩ : syracuseStep 945413 = 177265) B177265
theorem B486701 : Blo 143792 486701 := bstep (se 3 (by rfl) ⟨91256, by rfl⟩ : syracuseStep 486701 = 182513) B182513
theorem B486755 : Blo 143792 486755 := bstep (se 1 (by rfl) ⟨365066, by rfl⟩ : syracuseStep 486755 = 730133) B730133
theorem B224689 : Blo 143792 224689 := bstep (se 2 (by rfl) ⟨84258, by rfl⟩ : syracuseStep 224689 = 168517) B168517
theorem B192065 : Blo 143792 192065 := bstep (se 2 (by rfl) ⟨72024, by rfl⟩ : syracuseStep 192065 = 144049) B144049
theorem B388721 : Blo 143792 388721 := bstep (se 2 (by rfl) ⟨145770, by rfl⟩ : syracuseStep 388721 = 291541) B291541
theorem B487025 : Blo 143792 487025 := bstep (se 2 (by rfl) ⟨182634, by rfl⟩ : syracuseStep 487025 = 365269) B365269
theorem B552689 : Blo 143792 552689 := bstep (se 2 (by rfl) ⟨207258, by rfl⟩ : syracuseStep 552689 = 414517) B414517
theorem B487565 : Blo 143792 487565 := bstep (se 3 (by rfl) ⟨91418, by rfl⟩ : syracuseStep 487565 = 182837) B182837
theorem B323729 : Blo 143792 323729 := bstep (se 2 (by rfl) ⟨121398, by rfl⟩ : syracuseStep 323729 = 242797) B242797
theorem B323747 : Blo 143792 323747 := bstep (se 1 (by rfl) ⟨242810, by rfl⟩ : syracuseStep 323747 = 485621) B485621
theorem B487619 : Blo 143792 487619 := bstep (se 1 (by rfl) ⟨365714, by rfl⟩ : syracuseStep 487619 = 731429) B731429
theorem B6254819 : Blo 143792 6254819 := bstep (se 1 (by rfl) ⟨4691114, by rfl⟩ : syracuseStep 6254819 = 9382229) B9382229
theorem B946403 : Blo 143792 946403 := bstep (se 1 (by rfl) ⟨709802, by rfl⟩ : syracuseStep 946403 = 1419605) B1419605
theorem B324017 : Blo 143792 324017 := bstep (se 2 (by rfl) ⟨121506, by rfl⟩ : syracuseStep 324017 = 243013) B243013
theorem B324035 : Blo 143792 324035 := bstep (se 1 (by rfl) ⟨243026, by rfl⟩ : syracuseStep 324035 = 486053) B486053
theorem B487889 : Blo 143792 487889 := bstep (se 2 (by rfl) ⟨182958, by rfl⟩ : syracuseStep 487889 = 365917) B365917
theorem B225857 : Blo 143792 225857 := bstep (se 2 (by rfl) ⟨84696, by rfl⟩ : syracuseStep 225857 = 169393) B169393
theorem B1241669 : Blo 143792 1241669 := bstep (se 4 (by rfl) ⟨116406, by rfl⟩ : syracuseStep 1241669 = 232813) B232813
theorem B324305 : Blo 143792 324305 := bstep (se 2 (by rfl) ⟨121614, by rfl⟩ : syracuseStep 324305 = 243229) B243229
theorem B324323 : Blo 143792 324323 := bstep (se 1 (by rfl) ⟨243242, by rfl⟩ : syracuseStep 324323 = 486485) B486485
theorem B488429 : Blo 143792 488429 := bstep (se 3 (by rfl) ⟨91580, by rfl⟩ : syracuseStep 488429 = 183161) B183161
theorem B324593 : Blo 143792 324593 := bstep (se 2 (by rfl) ⟨121722, by rfl⟩ : syracuseStep 324593 = 243445) B243445
theorem B324611 : Blo 143792 324611 := bstep (se 1 (by rfl) ⟨243458, by rfl⟩ : syracuseStep 324611 = 486917) B486917
theorem B488483 : Blo 143792 488483 := bstep (se 1 (by rfl) ⟨366362, by rfl⟩ : syracuseStep 488483 = 732725) B732725
theorem B554147 : Blo 143792 554147 := bstep (se 1 (by rfl) ⟨415610, by rfl⟩ : syracuseStep 554147 = 831221) B831221
theorem B554161 : Blo 143792 554161 := bstep (se 2 (by rfl) ⟨207810, by rfl⟩ : syracuseStep 554161 = 415621) B415621
theorem B324881 : Blo 143792 324881 := bstep (se 2 (by rfl) ⟨121830, by rfl⟩ : syracuseStep 324881 = 243661) B243661
theorem B324899 : Blo 143792 324899 := bstep (se 1 (by rfl) ⟨243674, by rfl⟩ : syracuseStep 324899 = 487349) B487349
theorem B619811 : Blo 143792 619811 := bstep (se 1 (by rfl) ⟨464858, by rfl⟩ : syracuseStep 619811 = 929717) B929717
theorem B488753 : Blo 143792 488753 := bstep (se 2 (by rfl) ⟨183282, by rfl⟩ : syracuseStep 488753 = 366565) B366565
theorem B292337 : Blo 143792 292337 := bstep (se 2 (by rfl) ⟨109626, by rfl⟩ : syracuseStep 292337 = 219253) B219253
theorem B325169 : Blo 143792 325169 := bstep (se 2 (by rfl) ⟨121938, by rfl⟩ : syracuseStep 325169 = 243877) B243877
theorem B325187 : Blo 143792 325187 := bstep (se 1 (by rfl) ⟨243890, by rfl⟩ : syracuseStep 325187 = 487781) B487781
theorem B489293 : Blo 143792 489293 := bstep (se 3 (by rfl) ⟨91742, by rfl⟩ : syracuseStep 489293 = 183485) B183485
theorem B325457 : Blo 143792 325457 := bstep (se 2 (by rfl) ⟨122046, by rfl⟩ : syracuseStep 325457 = 244093) B244093
theorem B325475 : Blo 143792 325475 := bstep (se 1 (by rfl) ⟨244106, by rfl⟩ : syracuseStep 325475 = 488213) B488213
theorem B489347 : Blo 143792 489347 := bstep (se 1 (by rfl) ⟨367010, by rfl⟩ : syracuseStep 489347 = 734021) B734021
theorem B161779 : Blo 143792 161779 := bstep (se 1 (by rfl) ⟨121334, by rfl⟩ : syracuseStep 161779 = 242669) B242669
theorem B325745 : Blo 143792 325745 := bstep (se 2 (by rfl) ⟨122154, by rfl⟩ : syracuseStep 325745 = 244309) B244309
theorem B161923 : Blo 143792 161923 := bstep (se 1 (by rfl) ⟨121442, by rfl⟩ : syracuseStep 161923 = 242885) B242885
theorem B325763 : Blo 143792 325763 := bstep (se 1 (by rfl) ⟨244322, by rfl⟩ : syracuseStep 325763 = 488645) B488645
theorem B489617 : Blo 143792 489617 := bstep (se 2 (by rfl) ⟨183606, by rfl⟩ : syracuseStep 489617 = 367213) B367213
theorem B260273 : Blo 143792 260273 := bstep (se 2 (by rfl) ⟨97602, by rfl⟩ : syracuseStep 260273 = 195205) B195205
theorem B162067 : Blo 143792 162067 := bstep (se 1 (by rfl) ⟨121550, by rfl⟩ : syracuseStep 162067 = 243101) B243101
theorem B2816309 : Blo 143792 2816309 := bstep (se 5 (by rfl) ⟨132014, by rfl⟩ : syracuseStep 2816309 = 264029) B264029
theorem B326033 : Blo 143792 326033 := bstep (se 2 (by rfl) ⟨122262, by rfl⟩ : syracuseStep 326033 = 244525) B244525
theorem B162211 : Blo 143792 162211 := bstep (se 1 (by rfl) ⟨121658, by rfl⟩ : syracuseStep 162211 = 243317) B243317
theorem B326051 : Blo 143792 326051 := bstep (se 1 (by rfl) ⟨244538, by rfl⟩ : syracuseStep 326051 = 489077) B489077
theorem B2128355 : Blo 143792 2128355 := bstep (se 1 (by rfl) ⟨1596266, by rfl⟩ : syracuseStep 2128355 = 3192533) B3192533
theorem B162355 : Blo 143792 162355 := bstep (se 1 (by rfl) ⟨121766, by rfl⟩ : syracuseStep 162355 = 243533) B243533
theorem B424525 : Blo 143792 424525 := bstep (se 3 (by rfl) ⟨79598, by rfl⟩ : syracuseStep 424525 = 159197) B159197
theorem B555619 : Blo 143792 555619 := bstep (se 1 (by rfl) ⟨416714, by rfl⟩ : syracuseStep 555619 = 833429) B833429
theorem B490157 : Blo 143792 490157 := bstep (se 3 (by rfl) ⟨91904, by rfl⟩ : syracuseStep 490157 = 183809) B183809
theorem B326321 : Blo 143792 326321 := bstep (se 2 (by rfl) ⟨122370, by rfl⟩ : syracuseStep 326321 = 244741) B244741
theorem B162499 : Blo 143792 162499 := bstep (se 1 (by rfl) ⟨121874, by rfl⟩ : syracuseStep 162499 = 243749) B243749
theorem B326339 : Blo 143792 326339 := bstep (se 1 (by rfl) ⟨244754, by rfl⟩ : syracuseStep 326339 = 489509) B489509
theorem B490211 : Blo 143792 490211 := bstep (se 1 (by rfl) ⟨367658, by rfl⟩ : syracuseStep 490211 = 735317) B735317
theorem B162643 : Blo 143792 162643 := bstep (se 1 (by rfl) ⟨121982, by rfl⟩ : syracuseStep 162643 = 243965) B243965
theorem B785315 : Blo 143792 785315 := bstep (se 1 (by rfl) ⟨588986, by rfl⟩ : syracuseStep 785315 = 1177973) B1177973
theorem B195523 : Blo 143792 195523 := bstep (se 1 (by rfl) ⟨146642, by rfl⟩ : syracuseStep 195523 = 293285) B293285
theorem B326609 : Blo 143792 326609 := bstep (se 2 (by rfl) ⟨122478, by rfl⟩ : syracuseStep 326609 = 244957) B244957
theorem B162787 : Blo 143792 162787 := bstep (se 1 (by rfl) ⟨122090, by rfl⟩ : syracuseStep 162787 = 244181) B244181
theorem B326627 : Blo 143792 326627 := bstep (se 1 (by rfl) ⟨244970, by rfl⟩ : syracuseStep 326627 = 489941) B489941
theorem B490481 : Blo 143792 490481 := bstep (se 2 (by rfl) ⟨183930, by rfl⟩ : syracuseStep 490481 = 367861) B367861
theorem B621553 : Blo 143792 621553 := bstep (se 2 (by rfl) ⟨233082, by rfl⟩ : syracuseStep 621553 = 466165) B466165
theorem B162931 : Blo 143792 162931 := bstep (se 1 (by rfl) ⟨122198, by rfl⟩ : syracuseStep 162931 = 244397) B244397
theorem B195809 : Blo 143792 195809 := bstep (se 2 (by rfl) ⟨73428, by rfl⟩ : syracuseStep 195809 = 146857) B146857
theorem B326897 : Blo 143792 326897 := bstep (se 2 (by rfl) ⟨122586, by rfl⟩ : syracuseStep 326897 = 245173) B245173
theorem B163075 : Blo 143792 163075 := bstep (se 1 (by rfl) ⟨122306, by rfl⟩ : syracuseStep 163075 = 244613) B244613
theorem B326915 : Blo 143792 326915 := bstep (se 1 (by rfl) ⟨245186, by rfl⟩ : syracuseStep 326915 = 490373) B490373
theorem B163219 : Blo 143792 163219 := bstep (se 1 (by rfl) ⟨122414, by rfl⟩ : syracuseStep 163219 = 244829) B244829
theorem B491021 : Blo 143792 491021 := bstep (se 3 (by rfl) ⟨92066, by rfl⟩ : syracuseStep 491021 = 184133) B184133
theorem B327185 : Blo 143792 327185 := bstep (se 2 (by rfl) ⟨122694, by rfl⟩ : syracuseStep 327185 = 245389) B245389
theorem B163363 : Blo 143792 163363 := bstep (se 1 (by rfl) ⟨122522, by rfl⟩ : syracuseStep 163363 = 245045) B245045
theorem B327203 : Blo 143792 327203 := bstep (se 1 (by rfl) ⟨245402, by rfl⟩ : syracuseStep 327203 = 490805) B490805
theorem B491075 : Blo 143792 491075 := bstep (se 1 (by rfl) ⟨368306, by rfl⟩ : syracuseStep 491075 = 736613) B736613
theorem B163507 : Blo 143792 163507 := bstep (se 1 (by rfl) ⟨122630, by rfl⟩ : syracuseStep 163507 = 245261) B245261
theorem B1703605 : Blo 143792 1703605 := bstep (se 5 (by rfl) ⟨79856, by rfl⟩ : syracuseStep 1703605 = 159713) B159713
theorem B327473 : Blo 143792 327473 := bstep (se 2 (by rfl) ⟨122802, by rfl⟩ : syracuseStep 327473 = 245605) B245605
theorem B163651 : Blo 143792 163651 := bstep (se 1 (by rfl) ⟨122738, by rfl⟩ : syracuseStep 163651 = 245477) B245477
theorem B327491 : Blo 143792 327491 := bstep (se 1 (by rfl) ⟨245618, by rfl⟩ : syracuseStep 327491 = 491237) B491237
theorem B491345 : Blo 143792 491345 := bstep (se 2 (by rfl) ⟨184254, by rfl⟩ : syracuseStep 491345 = 368509) B368509
theorem B393133 : Blo 143792 393133 := bstep (se 3 (by rfl) ⟨73712, by rfl⟩ : syracuseStep 393133 = 147425) B147425
theorem B851917 : Blo 143792 851917 := bstep (se 3 (by rfl) ⟨159734, by rfl⟩ : syracuseStep 851917 = 319469) B319469
theorem B163795 : Blo 143792 163795 := bstep (se 1 (by rfl) ⟨122846, by rfl⟩ : syracuseStep 163795 = 245693) B245693
theorem B327833 : Blo 143792 327833 := bstep (se 2 (by rfl) ⟨122937, by rfl⟩ : syracuseStep 327833 = 245875) B245875
theorem B164011 : Blo 143792 164011 := bstep (se 1 (by rfl) ⟨123008, by rfl⟩ : syracuseStep 164011 = 246017) B246017
theorem B491723 : Blo 143792 491723 := bstep (se 1 (by rfl) ⟨368792, by rfl⟩ : syracuseStep 491723 = 737585) B737585
theorem B40337621 : Blo 143792 40337621 := bstep (se 7 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 40337621 = 945413) B945413
theorem B327923 : Blo 143792 327923 := bstep (se 1 (by rfl) ⟨245942, by rfl⟩ : syracuseStep 327923 = 491885) B491885
theorem B327959 : Blo 143792 327959 := bstep (se 1 (by rfl) ⟨245969, by rfl⟩ : syracuseStep 327959 = 491939) B491939
theorem B164119 : Blo 143792 164119 := bstep (se 1 (by rfl) ⟨123089, by rfl⟩ : syracuseStep 164119 = 246179) B246179
theorem B819557 : Blo 143792 819557 := bstep (se 4 (by rfl) ⟨76833, by rfl⟩ : syracuseStep 819557 = 153667) B153667
theorem B328139 : Blo 143792 328139 := bstep (se 1 (by rfl) ⟨246104, by rfl⟩ : syracuseStep 328139 = 492209) B492209
theorem B164299 : Blo 143792 164299 := bstep (se 1 (by rfl) ⟨123224, by rfl⟩ : syracuseStep 164299 = 246449) B246449
theorem B491993 : Blo 143792 491993 := bstep (se 2 (by rfl) ⟨184497, by rfl⟩ : syracuseStep 491993 = 368995) B368995
theorem B328193 : Blo 143792 328193 := bstep (se 2 (by rfl) ⟨123072, by rfl⟩ : syracuseStep 328193 = 246145) B246145
theorem B164407 : Blo 143792 164407 := bstep (se 1 (by rfl) ⟨123305, by rfl⟩ : syracuseStep 164407 = 246611) B246611
theorem B2458187 : Blo 143792 2458187 := bstep (se 1 (by rfl) ⟨1843640, by rfl⟩ : syracuseStep 2458187 = 3687281) B3687281
theorem B328409 : Blo 143792 328409 := bstep (se 2 (by rfl) ⟨123153, by rfl⟩ : syracuseStep 328409 = 246307) B246307
theorem B164587 : Blo 143792 164587 := bstep (se 1 (by rfl) ⟨123440, by rfl⟩ : syracuseStep 164587 = 246881) B246881
theorem B328499 : Blo 143792 328499 := bstep (se 1 (by rfl) ⟨246374, by rfl⟩ : syracuseStep 328499 = 492749) B492749
theorem B1114955 : Blo 143792 1114955 := bstep (se 1 (by rfl) ⟨836216, by rfl⟩ : syracuseStep 1114955 = 1672433) B1672433
theorem B328535 : Blo 143792 328535 := bstep (se 1 (by rfl) ⟨246401, by rfl⟩ : syracuseStep 328535 = 492803) B492803
theorem B164695 : Blo 143792 164695 := bstep (se 1 (by rfl) ⟨123521, by rfl⟩ : syracuseStep 164695 = 247043) B247043
theorem B590723 : Blo 143792 590723 := bstep (se 1 (by rfl) ⟨443042, by rfl⟩ : syracuseStep 590723 = 886085) B886085
theorem B328715 : Blo 143792 328715 := bstep (se 1 (by rfl) ⟨246536, by rfl⟩ : syracuseStep 328715 = 493073) B493073
theorem B164875 : Blo 143792 164875 := bstep (se 1 (by rfl) ⟨123656, by rfl⟩ : syracuseStep 164875 = 247313) B247313
theorem B328769 : Blo 143792 328769 := bstep (se 2 (by rfl) ⟨123288, by rfl⟩ : syracuseStep 328769 = 246577) B246577
theorem B164983 : Blo 143792 164983 := bstep (se 1 (by rfl) ⟨123737, by rfl⟩ : syracuseStep 164983 = 247475) B247475
theorem B492695 : Blo 143792 492695 := bstep (se 1 (by rfl) ⟨369521, by rfl⟩ : syracuseStep 492695 = 739043) B739043
theorem B558353 : Blo 143792 558353 := bstep (se 2 (by rfl) ⟨209382, by rfl⟩ : syracuseStep 558353 = 418765) B418765
theorem B328985 : Blo 143792 328985 := bstep (se 2 (by rfl) ⟨123369, by rfl⟩ : syracuseStep 328985 = 246739) B246739
theorem B165163 : Blo 143792 165163 := bstep (se 1 (by rfl) ⟨123872, by rfl⟩ : syracuseStep 165163 = 247745) B247745
theorem B492851 : Blo 143792 492851 := bstep (se 1 (by rfl) ⟨369638, by rfl⟩ : syracuseStep 492851 = 739277) B739277
theorem B197977 : Blo 143792 197977 := bstep (se 2 (by rfl) ⟨74241, by rfl⟩ : syracuseStep 197977 = 148483) B148483
theorem B329075 : Blo 143792 329075 := bstep (se 1 (by rfl) ⟨246806, by rfl⟩ : syracuseStep 329075 = 493613) B493613
theorem B329111 : Blo 143792 329111 := bstep (se 1 (by rfl) ⟨246833, by rfl⟩ : syracuseStep 329111 = 493667) B493667
theorem B165271 : Blo 143792 165271 := bstep (se 1 (by rfl) ⟨123953, by rfl⟩ : syracuseStep 165271 = 247907) B247907
theorem B296407 : Blo 143792 296407 := bstep (se 1 (by rfl) ⟨222305, by rfl⟩ : syracuseStep 296407 = 444611) B444611
theorem B329291 : Blo 143792 329291 := bstep (se 1 (by rfl) ⟨246968, by rfl⟩ : syracuseStep 329291 = 493937) B493937
theorem B165451 : Blo 143792 165451 := bstep (se 1 (by rfl) ⟨124088, by rfl⟩ : syracuseStep 165451 = 248177) B248177
theorem B329345 : Blo 143792 329345 := bstep (se 2 (by rfl) ⟨123504, by rfl⟩ : syracuseStep 329345 = 247009) B247009
theorem B263819 : Blo 143792 263819 := bstep (se 1 (by rfl) ⟨197864, by rfl⟩ : syracuseStep 263819 = 395729) B395729
theorem B493235 : Blo 143792 493235 := bstep (se 1 (by rfl) ⟨369926, by rfl⟩ : syracuseStep 493235 = 739853) B739853
theorem B165559 : Blo 143792 165559 := bstep (se 1 (by rfl) ⟨124169, by rfl⟩ : syracuseStep 165559 = 248339) B248339
theorem B558809 : Blo 143792 558809 := bstep (se 2 (by rfl) ⟨209553, by rfl⟩ : syracuseStep 558809 = 419107) B419107
theorem B329561 : Blo 143792 329561 := bstep (se 2 (by rfl) ⟨123585, by rfl⟩ : syracuseStep 329561 = 247171) B247171
theorem B165739 : Blo 143792 165739 := bstep (se 1 (by rfl) ⟨124304, by rfl⟩ : syracuseStep 165739 = 248609) B248609
theorem B296855 : Blo 143792 296855 := bstep (se 1 (by rfl) ⟨222641, by rfl⟩ : syracuseStep 296855 = 445283) B445283
theorem B559021 : Blo 143792 559021 := bstep (se 3 (by rfl) ⟨104816, by rfl⟩ : syracuseStep 559021 = 209633) B209633
theorem B329651 : Blo 143792 329651 := bstep (se 1 (by rfl) ⟨247238, by rfl⟩ : syracuseStep 329651 = 494477) B494477
theorem B493505 : Blo 143792 493505 := bstep (se 2 (by rfl) ⟨185064, by rfl⟩ : syracuseStep 493505 = 370129) B370129
theorem B526283 : Blo 143792 526283 := bstep (se 1 (by rfl) ⟨394712, by rfl⟩ : syracuseStep 526283 = 789425) B789425
theorem B329687 : Blo 143792 329687 := bstep (se 1 (by rfl) ⟨247265, by rfl⟩ : syracuseStep 329687 = 494531) B494531
theorem B165847 : Blo 143792 165847 := bstep (se 1 (by rfl) ⟨124385, by rfl⟩ : syracuseStep 165847 = 248771) B248771
theorem B264179 : Blo 143792 264179 := bstep (se 1 (by rfl) ⟨198134, by rfl⟩ : syracuseStep 264179 = 396269) B396269
theorem B329867 : Blo 143792 329867 := bstep (se 1 (by rfl) ⟨247400, by rfl⟩ : syracuseStep 329867 = 494801) B494801
theorem B264331 : Blo 143792 264331 := bstep (se 1 (by rfl) ⟨198248, by rfl⟩ : syracuseStep 264331 = 396497) B396497
theorem B166027 : Blo 143792 166027 := bstep (se 1 (by rfl) ⟨124520, by rfl⟩ : syracuseStep 166027 = 249041) B249041
theorem B329921 : Blo 143792 329921 := bstep (se 2 (by rfl) ⟨123720, by rfl⟩ : syracuseStep 329921 = 247441) B247441
theorem B559325 : Blo 143792 559325 := bstep (se 3 (by rfl) ⟨104873, by rfl⟩ : syracuseStep 559325 = 209747) B209747
theorem B166135 : Blo 143792 166135 := bstep (se 1 (by rfl) ⟨124601, by rfl⟩ : syracuseStep 166135 = 249203) B249203
theorem B526657 : Blo 143792 526657 := bstep (se 2 (by rfl) ⟨197496, by rfl⟩ : syracuseStep 526657 = 394993) B394993
theorem B461207 : Blo 143792 461207 := bstep (se 1 (by rfl) ⟨345905, by rfl⟩ : syracuseStep 461207 = 691811) B691811
theorem B330137 : Blo 143792 330137 := bstep (se 2 (by rfl) ⟨123801, by rfl⟩ : syracuseStep 330137 = 247603) B247603
theorem B526771 : Blo 143792 526771 := bstep (se 1 (by rfl) ⟨395078, by rfl⟩ : syracuseStep 526771 = 790157) B790157
theorem B494045 : Blo 143792 494045 := bstep (se 3 (by rfl) ⟨92633, by rfl⟩ : syracuseStep 494045 = 185267) B185267
theorem B330227 : Blo 143792 330227 := bstep (se 1 (by rfl) ⟨247670, by rfl⟩ : syracuseStep 330227 = 495341) B495341
theorem B330263 : Blo 143792 330263 := bstep (se 1 (by rfl) ⟨247697, by rfl⟩ : syracuseStep 330263 = 495395) B495395
theorem B330443 : Blo 143792 330443 := bstep (se 1 (by rfl) ⟨247832, by rfl⟩ : syracuseStep 330443 = 495665) B495665
theorem B330497 : Blo 143792 330497 := bstep (se 2 (by rfl) ⟨123936, by rfl⟩ : syracuseStep 330497 = 247873) B247873
theorem B330713 : Blo 143792 330713 := bstep (se 2 (by rfl) ⟨124017, by rfl⟩ : syracuseStep 330713 = 248035) B248035
theorem B330803 : Blo 143792 330803 := bstep (se 1 (by rfl) ⟨248102, by rfl⟩ : syracuseStep 330803 = 496205) B496205
theorem B330839 : Blo 143792 330839 := bstep (se 1 (by rfl) ⟨248129, by rfl⟩ : syracuseStep 330839 = 496259) B496259
theorem B396505 : Blo 143792 396505 := bstep (se 2 (by rfl) ⟨148689, by rfl⟩ : syracuseStep 396505 = 297379) B297379
theorem B330995 : Blo 143792 330995 := bstep (se 1 (by rfl) ⟨248246, by rfl⟩ : syracuseStep 330995 = 496493) B496493
theorem B331019 : Blo 143792 331019 := bstep (se 1 (by rfl) ⟨248264, by rfl⟩ : syracuseStep 331019 = 496529) B496529
theorem B331073 : Blo 143792 331073 := bstep (se 2 (by rfl) ⟨124152, by rfl⟩ : syracuseStep 331073 = 248305) B248305
theorem B331289 : Blo 143792 331289 := bstep (se 2 (by rfl) ⟨124233, by rfl⟩ : syracuseStep 331289 = 248467) B248467
theorem B495179 : Blo 143792 495179 := bstep (se 1 (by rfl) ⟨371384, by rfl⟩ : syracuseStep 495179 = 742769) B742769
theorem B331379 : Blo 143792 331379 := bstep (se 1 (by rfl) ⟨248534, by rfl⟩ : syracuseStep 331379 = 497069) B497069
theorem B331415 : Blo 143792 331415 := bstep (se 1 (by rfl) ⟨248561, by rfl⟩ : syracuseStep 331415 = 497123) B497123
theorem B2100977 : Blo 143792 2100977 := bstep (se 2 (by rfl) ⟨787866, by rfl⟩ : syracuseStep 2100977 = 1575733) B1575733
theorem B266009 : Blo 143792 266009 := bstep (se 2 (by rfl) ⟨99753, by rfl⟩ : syracuseStep 266009 = 199507) B199507
theorem B331595 : Blo 143792 331595 := bstep (se 1 (by rfl) ⟨248696, by rfl⟩ : syracuseStep 331595 = 497393) B497393
theorem B495449 : Blo 143792 495449 := bstep (se 2 (by rfl) ⟨185793, by rfl⟩ : syracuseStep 495449 = 371587) B371587
theorem B331649 : Blo 143792 331649 := bstep (se 2 (by rfl) ⟨124368, by rfl⟩ : syracuseStep 331649 = 248737) B248737
theorem B364439 : Blo 143792 364439 := bstep (se 1 (by rfl) ⟨273329, by rfl⟩ : syracuseStep 364439 = 546659) B546659
theorem B593837 : Blo 143792 593837 := bstep (se 3 (by rfl) ⟨111344, by rfl⟩ : syracuseStep 593837 = 222689) B222689
theorem B1052621 : Blo 143792 1052621 := bstep (se 3 (by rfl) ⟨197366, by rfl⟩ : syracuseStep 1052621 = 394733) B394733
theorem B921617 : Blo 143792 921617 := bstep (se 2 (by rfl) ⟨345606, by rfl⟩ : syracuseStep 921617 = 691213) B691213
theorem B331865 : Blo 143792 331865 := bstep (se 2 (by rfl) ⟨124449, by rfl⟩ : syracuseStep 331865 = 248899) B248899
theorem B331955 : Blo 143792 331955 := bstep (se 1 (by rfl) ⟨248966, by rfl⟩ : syracuseStep 331955 = 497933) B497933
theorem B331991 : Blo 143792 331991 := bstep (se 1 (by rfl) ⟨248993, by rfl⟩ : syracuseStep 331991 = 497987) B497987
theorem B1249667 : Blo 143792 1249667 := bstep (se 1 (by rfl) ⟨937250, by rfl⟩ : syracuseStep 1249667 = 1874501) B1874501
theorem B332171 : Blo 143792 332171 := bstep (se 1 (by rfl) ⟨249128, by rfl⟩ : syracuseStep 332171 = 498257) B498257
theorem B332225 : Blo 143792 332225 := bstep (se 2 (by rfl) ⟨124584, by rfl⟩ : syracuseStep 332225 = 249169) B249169
theorem B8458769 : Blo 143792 8458769 := bstep (se 2 (by rfl) ⟨3172038, by rfl⟩ : syracuseStep 8458769 = 6344077) B6344077
theorem B496151 : Blo 143792 496151 := bstep (se 1 (by rfl) ⟨372113, by rfl⟩ : syracuseStep 496151 = 744227) B744227
theorem B397847 : Blo 143792 397847 := bstep (se 1 (by rfl) ⟨298385, by rfl⟩ : syracuseStep 397847 = 596771) B596771
theorem B365107 : Blo 143792 365107 := bstep (se 1 (by rfl) ⟨273830, by rfl⟩ : syracuseStep 365107 = 547661) B547661
theorem B299585 : Blo 143792 299585 := bstep (se 2 (by rfl) ⟨112344, by rfl⟩ : syracuseStep 299585 = 224689) B224689
theorem B332363 : Blo 143792 332363 := bstep (se 1 (by rfl) ⟨249272, by rfl⟩ : syracuseStep 332363 = 498545) B498545
theorem B332441 : Blo 143792 332441 := bstep (se 2 (by rfl) ⟨124665, by rfl⟩ : syracuseStep 332441 = 249331) B249331
theorem B365249 : Blo 143792 365249 := bstep (se 2 (by rfl) ⟨136968, by rfl⟩ : syracuseStep 365249 = 273937) B273937
theorem B4264645 : Blo 143792 4264645 := bstep (se 4 (by rfl) ⟨399810, by rfl⟩ : syracuseStep 4264645 = 799621) B799621
theorem B332531 : Blo 143792 332531 := bstep (se 1 (by rfl) ⟨249398, by rfl⟩ : syracuseStep 332531 = 498797) B498797
theorem B1184557 : Blo 143792 1184557 := bstep (se 3 (by rfl) ⟨222104, by rfl⟩ : syracuseStep 1184557 = 444209) B444209
theorem B627601 : Blo 143792 627601 := bstep (se 2 (by rfl) ⟨235350, by rfl⟩ : syracuseStep 627601 = 470701) B470701
theorem B163831 : Blo 143792 163831 := bstep (se 1 (by rfl) ⟨122873, by rfl⟩ : syracuseStep 163831 = 245747) B245747
theorem B496691 : Blo 143792 496691 := bstep (se 1 (by rfl) ⟨372518, by rfl⟩ : syracuseStep 496691 = 745037) B745037
theorem B595019 : Blo 143792 595019 := bstep (se 1 (by rfl) ⟨446264, by rfl⟩ : syracuseStep 595019 = 892529) B892529
theorem B464089 : Blo 143792 464089 := bstep (se 2 (by rfl) ⟨174033, by rfl⟩ : syracuseStep 464089 = 348067) B348067
theorem B496961 : Blo 143792 496961 := bstep (se 2 (by rfl) ⟨186360, by rfl⟩ : syracuseStep 496961 = 372721) B372721
theorem B792139 : Blo 143792 792139 := bstep (se 1 (by rfl) ⟨594104, by rfl⟩ : syracuseStep 792139 = 1188209) B1188209
theorem B497501 : Blo 143792 497501 := bstep (se 3 (by rfl) ⟨93281, by rfl⟩ : syracuseStep 497501 = 186563) B186563
theorem B366515 : Blo 143792 366515 := bstep (se 1 (by rfl) ⟨274886, by rfl⟩ : syracuseStep 366515 = 549773) B549773
theorem B235543 : Blo 143792 235543 := bstep (se 1 (by rfl) ⟨176657, by rfl⟩ : syracuseStep 235543 = 353315) B353315
theorem B825389 : Blo 143792 825389 := bstep (se 3 (by rfl) ⟨154760, by rfl⟩ : syracuseStep 825389 = 309521) B309521
theorem B367051 : Blo 143792 367051 := bstep (se 1 (by rfl) ⟨275288, by rfl⟩ : syracuseStep 367051 = 550577) B550577
theorem B235991 : Blo 143792 235991 := bstep (se 1 (by rfl) ⟨176993, by rfl⟩ : syracuseStep 235991 = 353987) B353987
theorem B4299277 : Blo 143792 4299277 := bstep (se 3 (by rfl) ⟨806114, by rfl⟩ : syracuseStep 4299277 = 1612229) B1612229
theorem B367193 : Blo 143792 367193 := bstep (se 2 (by rfl) ⟨137697, by rfl⟩ : syracuseStep 367193 = 275395) B275395
theorem B236171 : Blo 143792 236171 := bstep (se 1 (by rfl) ⟨177128, by rfl⟩ : syracuseStep 236171 = 354257) B354257
theorem B1252057 : Blo 143792 1252057 := bstep (se 2 (by rfl) ⟨469521, by rfl⟩ : syracuseStep 1252057 = 939043) B939043
theorem B236299 : Blo 143792 236299 := bstep (se 1 (by rfl) ⟨177224, by rfl⟩ : syracuseStep 236299 = 354449) B354449
theorem B236363 : Blo 143792 236363 := bstep (se 1 (by rfl) ⟨177272, by rfl⟩ : syracuseStep 236363 = 354545) B354545
theorem B891749 : Blo 143792 891749 := bstep (se 4 (by rfl) ⟨83601, by rfl⟩ : syracuseStep 891749 = 167203) B167203
theorem B1121201 : Blo 143792 1121201 := bstep (se 2 (by rfl) ⟨420450, by rfl⟩ : syracuseStep 1121201 = 840901) B840901
theorem B498635 : Blo 143792 498635 := bstep (se 1 (by rfl) ⟨373976, by rfl⟩ : syracuseStep 498635 = 747953) B747953
theorem B1252313 : Blo 143792 1252313 := bstep (se 2 (by rfl) ⟨469617, by rfl⟩ : syracuseStep 1252313 = 939235) B939235
theorem B2497553 : Blo 143792 2497553 := bstep (se 2 (by rfl) ⟨936582, by rfl⟩ : syracuseStep 2497553 = 1873165) B1873165
theorem B662573 : Blo 143792 662573 := bstep (se 3 (by rfl) ⟨124232, by rfl⟩ : syracuseStep 662573 = 248465) B248465
theorem B629977 : Blo 143792 629977 := bstep (se 2 (by rfl) ⟨236241, by rfl⟩ : syracuseStep 629977 = 472483) B472483
theorem B302359 : Blo 143792 302359 := bstep (se 1 (by rfl) ⟨226769, by rfl⟩ : syracuseStep 302359 = 453539) B453539
theorem B466241 : Blo 143792 466241 := bstep (se 2 (by rfl) ⟨174840, by rfl⟩ : syracuseStep 466241 = 349681) B349681
theorem B368023 : Blo 143792 368023 := bstep (se 1 (by rfl) ⟨276017, by rfl⟩ : syracuseStep 368023 = 552035) B552035
theorem B1121687 : Blo 143792 1121687 := bstep (se 1 (by rfl) ⟨841265, by rfl⟩ : syracuseStep 1121687 = 1682531) B1682531
theorem B892433 : Blo 143792 892433 := bstep (se 2 (by rfl) ⟨334662, by rfl⟩ : syracuseStep 892433 = 669325) B669325
theorem B1253015 : Blo 143792 1253015 := bstep (se 1 (by rfl) ⟨939761, by rfl⟩ : syracuseStep 1253015 = 1879523) B1879523
theorem B368459 : Blo 143792 368459 := bstep (se 1 (by rfl) ⟨276344, by rfl⟩ : syracuseStep 368459 = 552689) B552689
theorem B1253393 : Blo 143792 1253393 := bstep (se 2 (by rfl) ⟨470022, by rfl⟩ : syracuseStep 1253393 = 940045) B940045
theorem B401501 : Blo 143792 401501 := bstep (se 3 (by rfl) ⟨75281, by rfl⟩ : syracuseStep 401501 = 150563) B150563
theorem B4169879 : Blo 143792 4169879 := bstep (se 1 (by rfl) ⟨3127409, by rfl⟩ : syracuseStep 4169879 = 6254819) B6254819
theorem B630935 : Blo 143792 630935 := bstep (se 1 (by rfl) ⟨473201, by rfl⟩ : syracuseStep 630935 = 946403) B946403
theorem B368833 : Blo 143792 368833 := bstep (se 2 (by rfl) ⟨138312, by rfl⟩ : syracuseStep 368833 = 276625) B276625
theorem B827779 : Blo 143792 827779 := bstep (se 1 (by rfl) ⟨620834, by rfl⟩ : syracuseStep 827779 = 1241669) B1241669
theorem B205259 : Blo 143792 205259 := bstep (se 1 (by rfl) ⟨153944, by rfl⟩ : syracuseStep 205259 = 307889) B307889
theorem B566033 : Blo 143792 566033 := bstep (se 2 (by rfl) ⟨212262, by rfl⟩ : syracuseStep 566033 = 424525) B424525
theorem B369431 : Blo 143792 369431 := bstep (se 1 (by rfl) ⟨277073, by rfl⟩ : syracuseStep 369431 = 554147) B554147
theorem B1254179 : Blo 143792 1254179 := bstep (se 1 (by rfl) ⟨940634, by rfl⟩ : syracuseStep 1254179 = 1881269) B1881269
theorem B1581869 : Blo 143792 1581869 := bstep (se 3 (by rfl) ⟨296600, by rfl⟩ : syracuseStep 1581869 = 593201) B593201
theorem B1647539 : Blo 143792 1647539 := bstep (se 1 (by rfl) ⟨1235654, by rfl⟩ : syracuseStep 1647539 = 2471309) B2471309
theorem B828737 : Blo 143792 828737 := bstep (se 2 (by rfl) ⟨310776, by rfl⟩ : syracuseStep 828737 = 621553) B621553
theorem B173515 : Blo 143792 173515 := bstep (se 1 (by rfl) ⟨130136, by rfl⟩ : syracuseStep 173515 = 260273) B260273
theorem B1877539 : Blo 143792 1877539 := bstep (se 1 (by rfl) ⟨1408154, by rfl⟩ : syracuseStep 1877539 = 2816309) B2816309
theorem B370241 : Blo 143792 370241 := bstep (se 2 (by rfl) ⟨138840, by rfl⟩ : syracuseStep 370241 = 277681) B277681
theorem B1418903 : Blo 143792 1418903 := bstep (se 1 (by rfl) ⟨1064177, by rfl⟩ : syracuseStep 1418903 = 2128355) B2128355
theorem B370777 : Blo 143792 370777 := bstep (se 2 (by rfl) ⟨139041, by rfl⟩ : syracuseStep 370777 = 278083) B278083
theorem B731267 : Blo 143792 731267 := bstep (se 1 (by rfl) ⟨548450, by rfl⟩ : syracuseStep 731267 = 1096901) B1096901
theorem B2271473 : Blo 143792 2271473 := bstep (se 2 (by rfl) ⟨851802, by rfl⟩ : syracuseStep 2271473 = 1703605) B1703605
theorem B207127 : Blo 143792 207127 := bstep (se 1 (by rfl) ⟨155345, by rfl⟩ : syracuseStep 207127 = 310691) B310691
theorem B1583425 : Blo 143792 1583425 := bstep (se 2 (by rfl) ⟨593784, by rfl⟩ : syracuseStep 1583425 = 1187569) B1187569
theorem B1648997 : Blo 143792 1648997 := bstep (se 4 (by rfl) ⟨154593, by rfl⟩ : syracuseStep 1648997 = 309187) B309187
theorem B1321859 : Blo 143792 1321859 := bstep (se 1 (by rfl) ⟨991394, by rfl⟩ : syracuseStep 1321859 = 1982789) B1982789
theorem B928691 : Blo 143792 928691 := bstep (se 1 (by rfl) ⟨696518, by rfl⟩ : syracuseStep 928691 = 1393037) B1393037
theorem B666755 : Blo 143792 666755 := bstep (se 1 (by rfl) ⟨500066, by rfl⟩ : syracuseStep 666755 = 1000133) B1000133
theorem B371891 : Blo 143792 371891 := bstep (se 1 (by rfl) ⟨278918, by rfl⟩ : syracuseStep 371891 = 557837) B557837
theorem B273611 : Blo 143792 273611 := bstep (se 1 (by rfl) ⟨205208, by rfl⟩ : syracuseStep 273611 = 410417) B410417
theorem B273793 : Blo 143792 273793 := bstep (se 2 (by rfl) ⟨102672, by rfl⟩ : syracuseStep 273793 = 205345) B205345
theorem B372185 : Blo 143792 372185 := bstep (se 2 (by rfl) ⟨139569, by rfl⟩ : syracuseStep 372185 = 279139) B279139
theorem B437849 : Blo 143792 437849 := bstep (se 2 (by rfl) ⟨164193, by rfl⟩ : syracuseStep 437849 = 328387) B328387
theorem B437981 : Blo 143792 437981 := bstep (se 3 (by rfl) ⟨82121, by rfl⟩ : syracuseStep 437981 = 164243) B164243
theorem B274241 : Blo 143792 274241 := bstep (se 2 (by rfl) ⟨102840, by rfl⟩ : syracuseStep 274241 = 205681) B205681
theorem B307223 : Blo 143792 307223 := bstep (se 1 (by rfl) ⟨230417, by rfl⟩ : syracuseStep 307223 = 460835) B460835
theorem B274583 : Blo 143792 274583 := bstep (se 1 (by rfl) ⟨205937, by rfl⟩ : syracuseStep 274583 = 411875) B411875
theorem B373081 : Blo 143792 373081 := bstep (se 2 (by rfl) ⟨139905, by rfl⟩ : syracuseStep 373081 = 279811) B279811
theorem B668083 : Blo 143792 668083 := bstep (se 1 (by rfl) ⟨501062, by rfl⟩ : syracuseStep 668083 = 1002125) B1002125
theorem B143799 : Blo 143792 143799 := bstep (se 1 (by rfl) ⟨107849, by rfl⟩ : syracuseStep 143799 = 215699) B215699
theorem B143819 : Blo 143792 143819 := bstep (se 1 (by rfl) ⟨107864, by rfl⟩ : syracuseStep 143819 = 215729) B215729
theorem B143831 : Blo 143792 143831 := bstep (se 1 (by rfl) ⟨107873, by rfl⟩ : syracuseStep 143831 = 215747) B215747
theorem B143851 : Blo 143792 143851 := bstep (se 1 (by rfl) ⟨107888, by rfl⟩ : syracuseStep 143851 = 215777) B215777
theorem B143863 : Blo 143792 143863 := bstep (se 1 (by rfl) ⟨107897, by rfl⟩ : syracuseStep 143863 = 215795) B215795
theorem B143883 : Blo 143792 143883 := bstep (se 1 (by rfl) ⟨107912, by rfl⟩ : syracuseStep 143883 = 215825) B215825
theorem B5550605 : Blo 143792 5550605 := bstep (se 3 (by rfl) ⟨1040738, by rfl⟩ : syracuseStep 5550605 = 2081477) B2081477
theorem B143895 : Blo 143792 143895 := bstep (se 1 (by rfl) ⟨107921, by rfl⟩ : syracuseStep 143895 = 215843) B215843
theorem B143915 : Blo 143792 143915 := bstep (se 1 (by rfl) ⟨107936, by rfl⟩ : syracuseStep 143915 = 215873) B215873
theorem B143927 : Blo 143792 143927 := bstep (se 1 (by rfl) ⟨107945, by rfl⟩ : syracuseStep 143927 = 215891) B215891
theorem B143947 : Blo 143792 143947 := bstep (se 1 (by rfl) ⟨107960, by rfl⟩ : syracuseStep 143947 = 215921) B215921
theorem B143959 : Blo 143792 143959 := bstep (se 1 (by rfl) ⟨107969, by rfl⟩ : syracuseStep 143959 = 215939) B215939
theorem B1684061 : Blo 143792 1684061 := bstep (se 3 (by rfl) ⟨315761, by rfl⟩ : syracuseStep 1684061 = 631523) B631523
theorem B143979 : Blo 143792 143979 := bstep (se 1 (by rfl) ⟨107984, by rfl⟩ : syracuseStep 143979 = 215969) B215969
theorem B143991 : Blo 143792 143991 := bstep (se 1 (by rfl) ⟨107993, by rfl⟩ : syracuseStep 143991 = 215987) B215987
theorem B144011 : Blo 143792 144011 := bstep (se 1 (by rfl) ⟨108008, by rfl⟩ : syracuseStep 144011 = 216017) B216017
theorem B144023 : Blo 143792 144023 := bstep (se 1 (by rfl) ⟨108017, by rfl⟩ : syracuseStep 144023 = 216035) B216035
theorem B144043 : Blo 143792 144043 := bstep (se 1 (by rfl) ⟨108032, by rfl⟩ : syracuseStep 144043 = 216065) B216065
theorem B144055 : Blo 143792 144055 := bstep (se 1 (by rfl) ⟨108041, by rfl⟩ : syracuseStep 144055 = 216083) B216083
theorem B144075 : Blo 143792 144075 := bstep (se 1 (by rfl) ⟨108056, by rfl⟩ : syracuseStep 144075 = 216113) B216113
theorem B144087 : Blo 143792 144087 := bstep (se 1 (by rfl) ⟨108065, by rfl⟩ : syracuseStep 144087 = 216131) B216131
theorem B144107 : Blo 143792 144107 := bstep (se 1 (by rfl) ⟨108080, by rfl⟩ : syracuseStep 144107 = 216161) B216161
theorem B144119 : Blo 143792 144119 := bstep (se 1 (by rfl) ⟨108089, by rfl⟩ : syracuseStep 144119 = 216179) B216179
theorem B144139 : Blo 143792 144139 := bstep (se 1 (by rfl) ⟨108104, by rfl⟩ : syracuseStep 144139 = 216209) B216209
theorem B144151 : Blo 143792 144151 := bstep (se 1 (by rfl) ⟨108113, by rfl⟩ : syracuseStep 144151 = 216227) B216227
theorem B144171 : Blo 143792 144171 := bstep (se 1 (by rfl) ⟨108128, by rfl⟩ : syracuseStep 144171 = 216257) B216257
theorem B275251 : Blo 143792 275251 := bstep (se 1 (by rfl) ⟨206438, by rfl⟩ : syracuseStep 275251 = 412877) B412877
theorem B144183 : Blo 143792 144183 := bstep (se 1 (by rfl) ⟨108137, by rfl⟩ : syracuseStep 144183 = 216275) B216275
theorem B144203 : Blo 143792 144203 := bstep (se 1 (by rfl) ⟨108152, by rfl⟩ : syracuseStep 144203 = 216305) B216305
theorem B144215 : Blo 143792 144215 := bstep (se 1 (by rfl) ⟨108161, by rfl⟩ : syracuseStep 144215 = 216323) B216323
theorem B144235 : Blo 143792 144235 := bstep (se 1 (by rfl) ⟨108176, by rfl⟩ : syracuseStep 144235 = 216353) B216353
theorem B144247 : Blo 143792 144247 := bstep (se 1 (by rfl) ⟨108185, by rfl⟩ : syracuseStep 144247 = 216371) B216371
theorem B144267 : Blo 143792 144267 := bstep (se 1 (by rfl) ⟨108200, by rfl⟩ : syracuseStep 144267 = 216401) B216401
theorem B144279 : Blo 143792 144279 := bstep (se 1 (by rfl) ⟨108209, by rfl⟩ : syracuseStep 144279 = 216419) B216419
theorem B144299 : Blo 143792 144299 := bstep (se 1 (by rfl) ⟨108224, by rfl⟩ : syracuseStep 144299 = 216449) B216449
theorem B144311 : Blo 143792 144311 := bstep (se 1 (by rfl) ⟨108233, by rfl⟩ : syracuseStep 144311 = 216467) B216467
theorem B144331 : Blo 143792 144331 := bstep (se 1 (by rfl) ⟨108248, by rfl⟩ : syracuseStep 144331 = 216497) B216497
theorem B144343 : Blo 143792 144343 := bstep (se 1 (by rfl) ⟨108257, by rfl⟩ : syracuseStep 144343 = 216515) B216515
theorem B144363 : Blo 143792 144363 := bstep (se 1 (by rfl) ⟨108272, by rfl⟩ : syracuseStep 144363 = 216545) B216545
theorem B144375 : Blo 143792 144375 := bstep (se 1 (by rfl) ⟨108281, by rfl⟩ : syracuseStep 144375 = 216563) B216563
theorem B144395 : Blo 143792 144395 := bstep (se 1 (by rfl) ⟨108296, by rfl⟩ : syracuseStep 144395 = 216593) B216593
theorem B144407 : Blo 143792 144407 := bstep (se 1 (by rfl) ⟨108305, by rfl⟩ : syracuseStep 144407 = 216611) B216611
theorem B144427 : Blo 143792 144427 := bstep (se 1 (by rfl) ⟨108320, by rfl⟩ : syracuseStep 144427 = 216641) B216641
theorem B144439 : Blo 143792 144439 := bstep (se 1 (by rfl) ⟨108329, by rfl⟩ : syracuseStep 144439 = 216659) B216659
theorem B308299 : Blo 143792 308299 := bstep (se 1 (by rfl) ⟨231224, by rfl⟩ : syracuseStep 308299 = 462449) B462449
theorem B144459 : Blo 143792 144459 := bstep (se 1 (by rfl) ⟨108344, by rfl⟩ : syracuseStep 144459 = 216689) B216689
theorem B2831435 : Blo 143792 2831435 := bstep (se 1 (by rfl) ⟨2123576, by rfl⟩ : syracuseStep 2831435 = 4247153) B4247153
theorem B373835 : Blo 143792 373835 := bstep (se 1 (by rfl) ⟨280376, by rfl⟩ : syracuseStep 373835 = 560753) B560753
theorem B144471 : Blo 143792 144471 := bstep (se 1 (by rfl) ⟨108353, by rfl⟩ : syracuseStep 144471 = 216707) B216707
theorem B242777 : Blo 143792 242777 := bstep (se 2 (by rfl) ⟨91041, by rfl⟩ : syracuseStep 242777 = 182083) B182083
theorem B144491 : Blo 143792 144491 := bstep (se 1 (by rfl) ⟨108368, by rfl⟩ : syracuseStep 144491 = 216737) B216737
theorem B144503 : Blo 143792 144503 := bstep (se 1 (by rfl) ⟨108377, by rfl⟩ : syracuseStep 144503 = 216755) B216755
theorem B144523 : Blo 143792 144523 := bstep (se 1 (by rfl) ⟨108392, by rfl⟩ : syracuseStep 144523 = 216785) B216785
theorem B144535 : Blo 143792 144535 := bstep (se 1 (by rfl) ⟨108401, by rfl⟩ : syracuseStep 144535 = 216803) B216803
theorem B144555 : Blo 143792 144555 := bstep (se 1 (by rfl) ⟨108416, by rfl⟩ : syracuseStep 144555 = 216833) B216833
theorem B144567 : Blo 143792 144567 := bstep (se 1 (by rfl) ⟨108425, by rfl⟩ : syracuseStep 144567 = 216851) B216851
theorem B144587 : Blo 143792 144587 := bstep (se 1 (by rfl) ⟨108440, by rfl⟩ : syracuseStep 144587 = 216881) B216881
theorem B144599 : Blo 143792 144599 := bstep (se 1 (by rfl) ⟨108449, by rfl⟩ : syracuseStep 144599 = 216899) B216899
theorem B242905 : Blo 143792 242905 := bstep (se 2 (by rfl) ⟨91089, by rfl⟩ : syracuseStep 242905 = 182179) B182179
theorem B144619 : Blo 143792 144619 := bstep (se 1 (by rfl) ⟨108464, by rfl⟩ : syracuseStep 144619 = 216929) B216929
theorem B275699 : Blo 143792 275699 := bstep (se 1 (by rfl) ⟨206774, by rfl⟩ : syracuseStep 275699 = 413549) B413549
theorem B144631 : Blo 143792 144631 := bstep (se 1 (by rfl) ⟨108473, by rfl⟩ : syracuseStep 144631 = 216947) B216947
theorem B144651 : Blo 143792 144651 := bstep (se 1 (by rfl) ⟨108488, by rfl⟩ : syracuseStep 144651 = 216977) B216977
theorem B144663 : Blo 143792 144663 := bstep (se 1 (by rfl) ⟨108497, by rfl⟩ : syracuseStep 144663 = 216995) B216995
theorem B275737 : Blo 143792 275737 := bstep (se 2 (by rfl) ⟨103401, by rfl⟩ : syracuseStep 275737 = 206803) B206803
theorem B144683 : Blo 143792 144683 := bstep (se 1 (by rfl) ⟨108512, by rfl⟩ : syracuseStep 144683 = 217025) B217025
theorem B1094957 : Blo 143792 1094957 := bstep (se 3 (by rfl) ⟨205304, by rfl⟩ : syracuseStep 1094957 = 410609) B410609
theorem B144695 : Blo 143792 144695 := bstep (se 1 (by rfl) ⟨108521, by rfl⟩ : syracuseStep 144695 = 217043) B217043
theorem B144715 : Blo 143792 144715 := bstep (se 1 (by rfl) ⟨108536, by rfl⟩ : syracuseStep 144715 = 217073) B217073
theorem B144727 : Blo 143792 144727 := bstep (se 1 (by rfl) ⟨108545, by rfl⟩ : syracuseStep 144727 = 217091) B217091
theorem B144747 : Blo 143792 144747 := bstep (se 1 (by rfl) ⟨108560, by rfl⟩ : syracuseStep 144747 = 217121) B217121
theorem B144759 : Blo 143792 144759 := bstep (se 1 (by rfl) ⟨108569, by rfl⟩ : syracuseStep 144759 = 217139) B217139
theorem B144779 : Blo 143792 144779 := bstep (se 1 (by rfl) ⟨108584, by rfl⟩ : syracuseStep 144779 = 217169) B217169
theorem B144791 : Blo 143792 144791 := bstep (se 1 (by rfl) ⟨108593, by rfl⟩ : syracuseStep 144791 = 217187) B217187
theorem B144811 : Blo 143792 144811 := bstep (se 1 (by rfl) ⟨108608, by rfl⟩ : syracuseStep 144811 = 217217) B217217
theorem B144823 : Blo 143792 144823 := bstep (se 1 (by rfl) ⟨108617, by rfl⟩ : syracuseStep 144823 = 217235) B217235
theorem B144843 : Blo 143792 144843 := bstep (se 1 (by rfl) ⟨108632, by rfl⟩ : syracuseStep 144843 = 217265) B217265
theorem B144855 : Blo 143792 144855 := bstep (se 1 (by rfl) ⟨108641, by rfl⟩ : syracuseStep 144855 = 217283) B217283
theorem B144875 : Blo 143792 144875 := bstep (se 1 (by rfl) ⟨108656, by rfl⟩ : syracuseStep 144875 = 217313) B217313
theorem B144887 : Blo 143792 144887 := bstep (se 1 (by rfl) ⟨108665, by rfl⟩ : syracuseStep 144887 = 217331) B217331
theorem B144907 : Blo 143792 144907 := bstep (se 1 (by rfl) ⟨108680, by rfl⟩ : syracuseStep 144907 = 217361) B217361
theorem B144919 : Blo 143792 144919 := bstep (se 1 (by rfl) ⟨108689, by rfl⟩ : syracuseStep 144919 = 217379) B217379
theorem B144939 : Blo 143792 144939 := bstep (se 1 (by rfl) ⟨108704, by rfl⟩ : syracuseStep 144939 = 217409) B217409
theorem B144951 : Blo 143792 144951 := bstep (se 1 (by rfl) ⟨108713, by rfl⟩ : syracuseStep 144951 = 217427) B217427
theorem B702017 : Blo 143792 702017 := bstep (se 2 (by rfl) ⟨263256, by rfl⟩ : syracuseStep 702017 = 526513) B526513
theorem B144971 : Blo 143792 144971 := bstep (se 1 (by rfl) ⟨108728, by rfl⟩ : syracuseStep 144971 = 217457) B217457
theorem B144983 : Blo 143792 144983 := bstep (se 1 (by rfl) ⟨108737, by rfl⟩ : syracuseStep 144983 = 217475) B217475
theorem B145003 : Blo 143792 145003 := bstep (se 1 (by rfl) ⟨108752, by rfl⟩ : syracuseStep 145003 = 217505) B217505
theorem B145015 : Blo 143792 145015 := bstep (se 1 (by rfl) ⟨108761, by rfl⟩ : syracuseStep 145015 = 217523) B217523
theorem B145035 : Blo 143792 145035 := bstep (se 1 (by rfl) ⟨108776, by rfl⟩ : syracuseStep 145035 = 217553) B217553
theorem B145047 : Blo 143792 145047 := bstep (se 1 (by rfl) ⟨108785, by rfl⟩ : syracuseStep 145047 = 217571) B217571
theorem B145067 : Blo 143792 145067 := bstep (se 1 (by rfl) ⟨108800, by rfl⟩ : syracuseStep 145067 = 217601) B217601
theorem B145079 : Blo 143792 145079 := bstep (se 1 (by rfl) ⟨108809, by rfl⟩ : syracuseStep 145079 = 217619) B217619
theorem B145099 : Blo 143792 145099 := bstep (se 1 (by rfl) ⟨108824, by rfl⟩ : syracuseStep 145099 = 217649) B217649
theorem B145111 : Blo 143792 145111 := bstep (se 1 (by rfl) ⟨108833, by rfl⟩ : syracuseStep 145111 = 217667) B217667
theorem B276185 : Blo 143792 276185 := bstep (se 2 (by rfl) ⟨103569, by rfl⟩ : syracuseStep 276185 = 207139) B207139
theorem B145131 : Blo 143792 145131 := bstep (se 1 (by rfl) ⟨108848, by rfl⟩ : syracuseStep 145131 = 217697) B217697
theorem B145143 : Blo 143792 145143 := bstep (se 1 (by rfl) ⟨108857, by rfl⟩ : syracuseStep 145143 = 217715) B217715
theorem B145163 : Blo 143792 145163 := bstep (se 1 (by rfl) ⟨108872, by rfl⟩ : syracuseStep 145163 = 217745) B217745
theorem B734993 : Blo 143792 734993 := bstep (se 2 (by rfl) ⟨275622, by rfl⟩ : syracuseStep 734993 = 551245) B551245
theorem B243479 : Blo 143792 243479 := bstep (se 1 (by rfl) ⟨182609, by rfl⟩ : syracuseStep 243479 = 365219) B365219
theorem B145175 : Blo 143792 145175 := bstep (se 1 (by rfl) ⟨108881, by rfl⟩ : syracuseStep 145175 = 217763) B217763
theorem B309017 : Blo 143792 309017 := bstep (se 2 (by rfl) ⟨115881, by rfl⟩ : syracuseStep 309017 = 231763) B231763
theorem B145195 : Blo 143792 145195 := bstep (se 1 (by rfl) ⟨108896, by rfl⟩ : syracuseStep 145195 = 217793) B217793
theorem B145207 : Blo 143792 145207 := bstep (se 1 (by rfl) ⟨108905, by rfl⟩ : syracuseStep 145207 = 217811) B217811
theorem B145227 : Blo 143792 145227 := bstep (se 1 (by rfl) ⟨108920, by rfl⟩ : syracuseStep 145227 = 217841) B217841
theorem B145239 : Blo 143792 145239 := bstep (se 1 (by rfl) ⟨108929, by rfl⟩ : syracuseStep 145239 = 217859) B217859
theorem B145259 : Blo 143792 145259 := bstep (se 1 (by rfl) ⟨108944, by rfl⟩ : syracuseStep 145259 = 217889) B217889
theorem B145271 : Blo 143792 145271 := bstep (se 1 (by rfl) ⟨108953, by rfl⟩ : syracuseStep 145271 = 217907) B217907
theorem B145291 : Blo 143792 145291 := bstep (se 1 (by rfl) ⟨108968, by rfl⟩ : syracuseStep 145291 = 217937) B217937
theorem B243607 : Blo 143792 243607 := bstep (se 1 (by rfl) ⟨182705, by rfl⟩ : syracuseStep 243607 = 365411) B365411
theorem B145303 : Blo 143792 145303 := bstep (se 1 (by rfl) ⟨108977, by rfl⟩ : syracuseStep 145303 = 217955) B217955
theorem B145323 : Blo 143792 145323 := bstep (se 1 (by rfl) ⟨108992, by rfl⟩ : syracuseStep 145323 = 217985) B217985
theorem B735155 : Blo 143792 735155 := bstep (se 1 (by rfl) ⟨551366, by rfl⟩ : syracuseStep 735155 = 1102733) B1102733
theorem B145335 : Blo 143792 145335 := bstep (se 1 (by rfl) ⟨109001, by rfl⟩ : syracuseStep 145335 = 218003) B218003
theorem B145355 : Blo 143792 145355 := bstep (se 1 (by rfl) ⟨109016, by rfl⟩ : syracuseStep 145355 = 218033) B218033
theorem B145367 : Blo 143792 145367 := bstep (se 1 (by rfl) ⟨109025, by rfl⟩ : syracuseStep 145367 = 218051) B218051
theorem B145387 : Blo 143792 145387 := bstep (se 1 (by rfl) ⟨109040, by rfl⟩ : syracuseStep 145387 = 218081) B218081
theorem B145399 : Blo 143792 145399 := bstep (se 1 (by rfl) ⟨109049, by rfl⟩ : syracuseStep 145399 = 218099) B218099
theorem B145419 : Blo 143792 145419 := bstep (se 1 (by rfl) ⟨109064, by rfl⟩ : syracuseStep 145419 = 218129) B218129
theorem B145431 : Blo 143792 145431 := bstep (se 1 (by rfl) ⟨109073, by rfl⟩ : syracuseStep 145431 = 218147) B218147
theorem B473111 : Blo 143792 473111 := bstep (se 1 (by rfl) ⟨354833, by rfl⟩ : syracuseStep 473111 = 709667) B709667
theorem B145451 : Blo 143792 145451 := bstep (se 1 (by rfl) ⟨109088, by rfl⟩ : syracuseStep 145451 = 218177) B218177
theorem B145463 : Blo 143792 145463 := bstep (se 1 (by rfl) ⟨109097, by rfl⟩ : syracuseStep 145463 = 218195) B218195
theorem B145483 : Blo 143792 145483 := bstep (se 1 (by rfl) ⟨109112, by rfl⟩ : syracuseStep 145483 = 218225) B218225
theorem B833611 : Blo 143792 833611 := bstep (se 1 (by rfl) ⟨625208, by rfl⟩ : syracuseStep 833611 = 1250417) B1250417
theorem B1882187 : Blo 143792 1882187 := bstep (se 1 (by rfl) ⟨1411640, by rfl⟩ : syracuseStep 1882187 = 2823281) B2823281
theorem B145495 : Blo 143792 145495 := bstep (se 1 (by rfl) ⟨109121, by rfl⟩ : syracuseStep 145495 = 218243) B218243
theorem B145515 : Blo 143792 145515 := bstep (se 1 (by rfl) ⟨109136, by rfl⟩ : syracuseStep 145515 = 218273) B218273
theorem B145527 : Blo 143792 145527 := bstep (se 1 (by rfl) ⟨109145, by rfl⟩ : syracuseStep 145527 = 218291) B218291
theorem B145547 : Blo 143792 145547 := bstep (se 1 (by rfl) ⟨109160, by rfl⟩ : syracuseStep 145547 = 218321) B218321
theorem B145559 : Blo 143792 145559 := bstep (se 1 (by rfl) ⟨109169, by rfl⟩ : syracuseStep 145559 = 218339) B218339
theorem B145579 : Blo 143792 145579 := bstep (se 1 (by rfl) ⟨109184, by rfl⟩ : syracuseStep 145579 = 218369) B218369
theorem B145591 : Blo 143792 145591 := bstep (se 1 (by rfl) ⟨109193, by rfl⟩ : syracuseStep 145591 = 218387) B218387
theorem B145611 : Blo 143792 145611 := bstep (se 1 (by rfl) ⟨109208, by rfl⟩ : syracuseStep 145611 = 218417) B218417
theorem B145623 : Blo 143792 145623 := bstep (se 1 (by rfl) ⟨109217, by rfl⟩ : syracuseStep 145623 = 218435) B218435
theorem B145643 : Blo 143792 145643 := bstep (se 1 (by rfl) ⟨109232, by rfl⟩ : syracuseStep 145643 = 218465) B218465
theorem B145655 : Blo 143792 145655 := bstep (se 1 (by rfl) ⟨109241, by rfl⟩ : syracuseStep 145655 = 218483) B218483
theorem B145675 : Blo 143792 145675 := bstep (se 1 (by rfl) ⟨109256, by rfl⟩ : syracuseStep 145675 = 218513) B218513
theorem B145687 : Blo 143792 145687 := bstep (se 1 (by rfl) ⟨109265, by rfl⟩ : syracuseStep 145687 = 218531) B218531
theorem B309529 : Blo 143792 309529 := bstep (se 2 (by rfl) ⟨116073, by rfl⟩ : syracuseStep 309529 = 232147) B232147
theorem B145707 : Blo 143792 145707 := bstep (se 1 (by rfl) ⟨109280, by rfl⟩ : syracuseStep 145707 = 218561) B218561
theorem B145719 : Blo 143792 145719 := bstep (se 1 (by rfl) ⟨109289, by rfl⟩ : syracuseStep 145719 = 218579) B218579
theorem B145739 : Blo 143792 145739 := bstep (se 1 (by rfl) ⟨109304, by rfl⟩ : syracuseStep 145739 = 218609) B218609
theorem B145751 : Blo 143792 145751 := bstep (se 1 (by rfl) ⟨109313, by rfl⟩ : syracuseStep 145751 = 218627) B218627
theorem B833885 : Blo 143792 833885 := bstep (se 3 (by rfl) ⟨156353, by rfl⟩ : syracuseStep 833885 = 312707) B312707
theorem B145771 : Blo 143792 145771 := bstep (se 1 (by rfl) ⟨109328, by rfl⟩ : syracuseStep 145771 = 218657) B218657
theorem B145783 : Blo 143792 145783 := bstep (se 1 (by rfl) ⟨109337, by rfl⟩ : syracuseStep 145783 = 218675) B218675
theorem B145803 : Blo 143792 145803 := bstep (se 1 (by rfl) ⟨109352, by rfl⟩ : syracuseStep 145803 = 218705) B218705
theorem B211339 : Blo 143792 211339 := bstep (se 1 (by rfl) ⟨158504, by rfl⟩ : syracuseStep 211339 = 317009) B317009
theorem B145815 : Blo 143792 145815 := bstep (se 1 (by rfl) ⟨109361, by rfl⟩ : syracuseStep 145815 = 218723) B218723
theorem B145835 : Blo 143792 145835 := bstep (se 1 (by rfl) ⟨109376, by rfl⟩ : syracuseStep 145835 = 218753) B218753
theorem B309683 : Blo 143792 309683 := bstep (se 1 (by rfl) ⟨232262, by rfl⟩ : syracuseStep 309683 = 464525) B464525
theorem B145847 : Blo 143792 145847 := bstep (se 1 (by rfl) ⟨109385, by rfl⟩ : syracuseStep 145847 = 218771) B218771
theorem B276929 : Blo 143792 276929 := bstep (se 2 (by rfl) ⟨103848, by rfl⟩ : syracuseStep 276929 = 207697) B207697
theorem B145867 : Blo 143792 145867 := bstep (se 1 (by rfl) ⟨109400, by rfl⟩ : syracuseStep 145867 = 218801) B218801
theorem B145879 : Blo 143792 145879 := bstep (se 1 (by rfl) ⟨109409, by rfl⟩ : syracuseStep 145879 = 218819) B218819
theorem B145899 : Blo 143792 145899 := bstep (se 1 (by rfl) ⟨109424, by rfl⟩ : syracuseStep 145899 = 218849) B218849
theorem B145911 : Blo 143792 145911 := bstep (se 1 (by rfl) ⟨109433, by rfl⟩ : syracuseStep 145911 = 218867) B218867
theorem B244235 : Blo 143792 244235 := bstep (se 1 (by rfl) ⟨183176, by rfl⟩ : syracuseStep 244235 = 366353) B366353
theorem B145931 : Blo 143792 145931 := bstep (se 1 (by rfl) ⟨109448, by rfl⟩ : syracuseStep 145931 = 218897) B218897
theorem B145943 : Blo 143792 145943 := bstep (se 1 (by rfl) ⟨109457, by rfl⟩ : syracuseStep 145943 = 218915) B218915
theorem B145963 : Blo 143792 145963 := bstep (se 1 (by rfl) ⟨109472, by rfl⟩ : syracuseStep 145963 = 218945) B218945
theorem B145975 : Blo 143792 145975 := bstep (se 1 (by rfl) ⟨109481, by rfl⟩ : syracuseStep 145975 = 218963) B218963
theorem B145995 : Blo 143792 145995 := bstep (se 1 (by rfl) ⟨109496, by rfl⟩ : syracuseStep 145995 = 218993) B218993
theorem B146007 : Blo 143792 146007 := bstep (se 1 (by rfl) ⟨109505, by rfl⟩ : syracuseStep 146007 = 219011) B219011
theorem B146027 : Blo 143792 146027 := bstep (se 1 (by rfl) ⟨109520, by rfl⟩ : syracuseStep 146027 = 219041) B219041
theorem B146039 : Blo 143792 146039 := bstep (se 1 (by rfl) ⟨109529, by rfl⟩ : syracuseStep 146039 = 219059) B219059
theorem B244363 : Blo 143792 244363 := bstep (se 1 (by rfl) ⟨183272, by rfl⟩ : syracuseStep 244363 = 366545) B366545
theorem B146059 : Blo 143792 146059 := bstep (se 1 (by rfl) ⟨109544, by rfl⟩ : syracuseStep 146059 = 219089) B219089
theorem B146071 : Blo 143792 146071 := bstep (se 1 (by rfl) ⟨109553, by rfl⟩ : syracuseStep 146071 = 219107) B219107
theorem B146091 : Blo 143792 146091 := bstep (se 1 (by rfl) ⟨109568, by rfl⟩ : syracuseStep 146091 = 219137) B219137
theorem B146103 : Blo 143792 146103 := bstep (se 1 (by rfl) ⟨109577, by rfl⟩ : syracuseStep 146103 = 219155) B219155
theorem B277195 : Blo 143792 277195 := bstep (se 1 (by rfl) ⟨207896, by rfl⟩ : syracuseStep 277195 = 415793) B415793
theorem B146123 : Blo 143792 146123 := bstep (se 1 (by rfl) ⟨109592, by rfl⟩ : syracuseStep 146123 = 219185) B219185
theorem B146135 : Blo 143792 146135 := bstep (se 1 (by rfl) ⟨109601, by rfl⟩ : syracuseStep 146135 = 219203) B219203
theorem B146155 : Blo 143792 146155 := bstep (se 1 (by rfl) ⟨109616, by rfl⟩ : syracuseStep 146155 = 219233) B219233
theorem B146167 : Blo 143792 146167 := bstep (se 1 (by rfl) ⟨109625, by rfl⟩ : syracuseStep 146167 = 219251) B219251
theorem B146187 : Blo 143792 146187 := bstep (se 1 (by rfl) ⟨109640, by rfl⟩ : syracuseStep 146187 = 219281) B219281
theorem B146199 : Blo 143792 146199 := bstep (se 1 (by rfl) ⟨109649, by rfl⟩ : syracuseStep 146199 = 219299) B219299
theorem B244505 : Blo 143792 244505 := bstep (se 2 (by rfl) ⟨91689, by rfl⟩ : syracuseStep 244505 = 183379) B183379
theorem B146219 : Blo 143792 146219 := bstep (se 1 (by rfl) ⟨109664, by rfl⟩ : syracuseStep 146219 = 219329) B219329
theorem B146231 : Blo 143792 146231 := bstep (se 1 (by rfl) ⟨109673, by rfl⟩ : syracuseStep 146231 = 219347) B219347
theorem B146251 : Blo 143792 146251 := bstep (se 1 (by rfl) ⟨109688, by rfl⟩ : syracuseStep 146251 = 219377) B219377
theorem B146263 : Blo 143792 146263 := bstep (se 1 (by rfl) ⟨109697, by rfl⟩ : syracuseStep 146263 = 219395) B219395
theorem B146283 : Blo 143792 146283 := bstep (se 1 (by rfl) ⟨109712, by rfl⟩ : syracuseStep 146283 = 219425) B219425
theorem B146295 : Blo 143792 146295 := bstep (se 1 (by rfl) ⟨109721, by rfl⟩ : syracuseStep 146295 = 219443) B219443
theorem B146315 : Blo 143792 146315 := bstep (se 1 (by rfl) ⟨109736, by rfl⟩ : syracuseStep 146315 = 219473) B219473
theorem B146327 : Blo 143792 146327 := bstep (se 1 (by rfl) ⟨109745, by rfl⟩ : syracuseStep 146327 = 219491) B219491
theorem B244633 : Blo 143792 244633 := bstep (se 2 (by rfl) ⟨91737, by rfl⟩ : syracuseStep 244633 = 183475) B183475
theorem B146347 : Blo 143792 146347 := bstep (se 1 (by rfl) ⟨109760, by rfl⟩ : syracuseStep 146347 = 219521) B219521
theorem B146359 : Blo 143792 146359 := bstep (se 1 (by rfl) ⟨109769, by rfl⟩ : syracuseStep 146359 = 219539) B219539
theorem B146379 : Blo 143792 146379 := bstep (se 1 (by rfl) ⟨109784, by rfl⟩ : syracuseStep 146379 = 219569) B219569
theorem B146391 : Blo 143792 146391 := bstep (se 1 (by rfl) ⟨109793, by rfl⟩ : syracuseStep 146391 = 219587) B219587
theorem B146411 : Blo 143792 146411 := bstep (se 1 (by rfl) ⟨109808, by rfl⟩ : syracuseStep 146411 = 219617) B219617
theorem B146423 : Blo 143792 146423 := bstep (se 1 (by rfl) ⟨109817, by rfl⟩ : syracuseStep 146423 = 219635) B219635
theorem B146443 : Blo 143792 146443 := bstep (se 1 (by rfl) ⟨109832, by rfl⟩ : syracuseStep 146443 = 219665) B219665
theorem B146455 : Blo 143792 146455 := bstep (se 1 (by rfl) ⟨109841, by rfl⟩ : syracuseStep 146455 = 219683) B219683
theorem B1391651 : Blo 143792 1391651 := bstep (se 1 (by rfl) ⟨1043738, by rfl⟩ : syracuseStep 1391651 = 2087477) B2087477
theorem B146475 : Blo 143792 146475 := bstep (se 1 (by rfl) ⟨109856, by rfl⟩ : syracuseStep 146475 = 219713) B219713
theorem B146487 : Blo 143792 146487 := bstep (se 1 (by rfl) ⟨109865, by rfl⟩ : syracuseStep 146487 = 219731) B219731
theorem B146507 : Blo 143792 146507 := bstep (se 1 (by rfl) ⟨109880, by rfl⟩ : syracuseStep 146507 = 219761) B219761
theorem B146519 : Blo 143792 146519 := bstep (se 1 (by rfl) ⟨109889, by rfl⟩ : syracuseStep 146519 = 219779) B219779
theorem B146539 : Blo 143792 146539 := bstep (se 1 (by rfl) ⟨109904, by rfl⟩ : syracuseStep 146539 = 219809) B219809
theorem B146551 : Blo 143792 146551 := bstep (se 1 (by rfl) ⟨109913, by rfl⟩ : syracuseStep 146551 = 219827) B219827
theorem B277643 : Blo 143792 277643 := bstep (se 1 (by rfl) ⟨208232, by rfl⟩ : syracuseStep 277643 = 416465) B416465
theorem B146571 : Blo 143792 146571 := bstep (se 1 (by rfl) ⟨109928, by rfl⟩ : syracuseStep 146571 = 219857) B219857
theorem B146583 : Blo 143792 146583 := bstep (se 1 (by rfl) ⟨109937, by rfl⟩ : syracuseStep 146583 = 219875) B219875
theorem B146603 : Blo 143792 146603 := bstep (se 1 (by rfl) ⟨109952, by rfl⟩ : syracuseStep 146603 = 219905) B219905
theorem B146615 : Blo 143792 146615 := bstep (se 1 (by rfl) ⟨109961, by rfl⟩ : syracuseStep 146615 = 219923) B219923
theorem B146635 : Blo 143792 146635 := bstep (se 1 (by rfl) ⟨109976, by rfl⟩ : syracuseStep 146635 = 219953) B219953
theorem B146647 : Blo 143792 146647 := bstep (se 1 (by rfl) ⟨109985, by rfl⟩ : syracuseStep 146647 = 219971) B219971
theorem B146667 : Blo 143792 146667 := bstep (se 1 (by rfl) ⟨110000, by rfl⟩ : syracuseStep 146667 = 220001) B220001
theorem B146679 : Blo 143792 146679 := bstep (se 1 (by rfl) ⟨110009, by rfl⟩ : syracuseStep 146679 = 220019) B220019
theorem B1260805 : Blo 143792 1260805 := bstep (se 4 (by rfl) ⟨118200, by rfl⟩ : syracuseStep 1260805 = 236401) B236401
theorem B146699 : Blo 143792 146699 := bstep (se 1 (by rfl) ⟨110024, by rfl⟩ : syracuseStep 146699 = 220049) B220049
theorem B146711 : Blo 143792 146711 := bstep (se 1 (by rfl) ⟨110033, by rfl⟩ : syracuseStep 146711 = 220067) B220067
theorem B146731 : Blo 143792 146731 := bstep (se 1 (by rfl) ⟨110048, by rfl⟩ : syracuseStep 146731 = 220097) B220097
theorem B146743 : Blo 143792 146743 := bstep (se 1 (by rfl) ⟨110057, by rfl⟩ : syracuseStep 146743 = 220115) B220115
theorem B277825 : Blo 143792 277825 := bstep (se 2 (by rfl) ⟨104184, by rfl⟩ : syracuseStep 277825 = 208369) B208369
theorem B146763 : Blo 143792 146763 := bstep (se 1 (by rfl) ⟨110072, by rfl⟩ : syracuseStep 146763 = 220145) B220145
theorem B146775 : Blo 143792 146775 := bstep (se 1 (by rfl) ⟨110081, by rfl⟩ : syracuseStep 146775 = 220163) B220163
theorem B146795 : Blo 143792 146795 := bstep (se 1 (by rfl) ⟨110096, by rfl⟩ : syracuseStep 146795 = 220193) B220193
theorem B146807 : Blo 143792 146807 := bstep (se 1 (by rfl) ⟨110105, by rfl⟩ : syracuseStep 146807 = 220211) B220211
theorem B310657 : Blo 143792 310657 := bstep (se 2 (by rfl) ⟨116496, by rfl⟩ : syracuseStep 310657 = 232993) B232993
theorem B146827 : Blo 143792 146827 := bstep (se 1 (by rfl) ⟨110120, by rfl⟩ : syracuseStep 146827 = 220241) B220241
theorem B146839 : Blo 143792 146839 := bstep (se 1 (by rfl) ⟨110129, by rfl⟩ : syracuseStep 146839 = 220259) B220259
theorem B146859 : Blo 143792 146859 := bstep (se 1 (by rfl) ⟨110144, by rfl⟩ : syracuseStep 146859 = 220289) B220289
theorem B146871 : Blo 143792 146871 := bstep (se 1 (by rfl) ⟨110153, by rfl⟩ : syracuseStep 146871 = 220307) B220307
theorem B146891 : Blo 143792 146891 := bstep (se 1 (by rfl) ⟨110168, by rfl⟩ : syracuseStep 146891 = 220337) B220337
theorem B245207 : Blo 143792 245207 := bstep (se 1 (by rfl) ⟨183905, by rfl⟩ : syracuseStep 245207 = 367811) B367811
theorem B146903 : Blo 143792 146903 := bstep (se 1 (by rfl) ⟨110177, by rfl⟩ : syracuseStep 146903 = 220355) B220355
theorem B146923 : Blo 143792 146923 := bstep (se 1 (by rfl) ⟨110192, by rfl⟩ : syracuseStep 146923 = 220385) B220385
theorem B146935 : Blo 143792 146935 := bstep (se 1 (by rfl) ⟨110201, by rfl⟩ : syracuseStep 146935 = 220403) B220403
theorem B146955 : Blo 143792 146955 := bstep (se 1 (by rfl) ⟨110216, by rfl⟩ : syracuseStep 146955 = 220433) B220433
theorem B146967 : Blo 143792 146967 := bstep (se 1 (by rfl) ⟨110225, by rfl⟩ : syracuseStep 146967 = 220451) B220451
theorem B146987 : Blo 143792 146987 := bstep (se 1 (by rfl) ⟨110240, by rfl⟩ : syracuseStep 146987 = 220481) B220481
theorem B146999 : Blo 143792 146999 := bstep (se 1 (by rfl) ⟨110249, by rfl⟩ : syracuseStep 146999 = 220499) B220499
theorem B147019 : Blo 143792 147019 := bstep (se 1 (by rfl) ⟨110264, by rfl⟩ : syracuseStep 147019 = 220529) B220529
theorem B245335 : Blo 143792 245335 := bstep (se 1 (by rfl) ⟨184001, by rfl⟩ : syracuseStep 245335 = 368003) B368003
theorem B147031 : Blo 143792 147031 := bstep (se 1 (by rfl) ⟨110273, by rfl⟩ : syracuseStep 147031 = 220547) B220547
theorem B147051 : Blo 143792 147051 := bstep (se 1 (by rfl) ⟨110288, by rfl⟩ : syracuseStep 147051 = 220577) B220577
theorem B147063 : Blo 143792 147063 := bstep (se 1 (by rfl) ⟨110297, by rfl⟩ : syracuseStep 147063 = 220595) B220595
theorem B147083 : Blo 143792 147083 := bstep (se 1 (by rfl) ⟨110312, by rfl⟩ : syracuseStep 147083 = 220625) B220625
theorem B278167 : Blo 143792 278167 := bstep (se 1 (by rfl) ⟨208625, by rfl⟩ : syracuseStep 278167 = 417251) B417251
theorem B147095 : Blo 143792 147095 := bstep (se 1 (by rfl) ⟨110321, by rfl⟩ : syracuseStep 147095 = 220643) B220643
theorem B147115 : Blo 143792 147115 := bstep (se 1 (by rfl) ⟨110336, by rfl⟩ : syracuseStep 147115 = 220673) B220673
theorem B147127 : Blo 143792 147127 := bstep (se 1 (by rfl) ⟨110345, by rfl⟩ : syracuseStep 147127 = 220691) B220691
theorem B147147 : Blo 143792 147147 := bstep (se 1 (by rfl) ⟨110360, by rfl⟩ : syracuseStep 147147 = 220721) B220721
theorem B310999 : Blo 143792 310999 := bstep (se 1 (by rfl) ⟨233249, by rfl⟩ : syracuseStep 310999 = 466499) B466499
theorem B147159 : Blo 143792 147159 := bstep (se 1 (by rfl) ⟨110369, by rfl⟩ : syracuseStep 147159 = 220739) B220739
theorem B147179 : Blo 143792 147179 := bstep (se 1 (by rfl) ⟨110384, by rfl⟩ : syracuseStep 147179 = 220769) B220769
theorem B147191 : Blo 143792 147191 := bstep (se 1 (by rfl) ⟨110393, by rfl⟩ : syracuseStep 147191 = 220787) B220787
theorem B147211 : Blo 143792 147211 := bstep (se 1 (by rfl) ⟨110408, by rfl⟩ : syracuseStep 147211 = 220817) B220817
theorem B147223 : Blo 143792 147223 := bstep (se 1 (by rfl) ⟨110417, by rfl⟩ : syracuseStep 147223 = 220835) B220835
theorem B147243 : Blo 143792 147243 := bstep (se 1 (by rfl) ⟨110432, by rfl⟩ : syracuseStep 147243 = 220865) B220865
theorem B147255 : Blo 143792 147255 := bstep (se 1 (by rfl) ⟨110441, by rfl⟩ : syracuseStep 147255 = 220883) B220883
theorem B737099 : Blo 143792 737099 := bstep (se 1 (by rfl) ⟨552824, by rfl⟩ : syracuseStep 737099 = 1105649) B1105649
theorem B147275 : Blo 143792 147275 := bstep (se 1 (by rfl) ⟨110456, by rfl⟩ : syracuseStep 147275 = 220913) B220913
theorem B147287 : Blo 143792 147287 := bstep (se 1 (by rfl) ⟨110465, by rfl⟩ : syracuseStep 147287 = 220931) B220931
theorem B147307 : Blo 143792 147307 := bstep (se 1 (by rfl) ⟨110480, by rfl⟩ : syracuseStep 147307 = 220961) B220961
theorem B278387 : Blo 143792 278387 := bstep (se 1 (by rfl) ⟨208790, by rfl⟩ : syracuseStep 278387 = 417581) B417581
theorem B147319 : Blo 143792 147319 := bstep (se 1 (by rfl) ⟨110489, by rfl⟩ : syracuseStep 147319 = 220979) B220979
theorem B147339 : Blo 143792 147339 := bstep (se 1 (by rfl) ⟨110504, by rfl⟩ : syracuseStep 147339 = 221009) B221009
theorem B147351 : Blo 143792 147351 := bstep (se 1 (by rfl) ⟨110513, by rfl⟩ : syracuseStep 147351 = 221027) B221027
theorem B147371 : Blo 143792 147371 := bstep (se 1 (by rfl) ⟨110528, by rfl⟩ : syracuseStep 147371 = 221057) B221057
theorem B147383 : Blo 143792 147383 := bstep (se 1 (by rfl) ⟨110537, by rfl⟩ : syracuseStep 147383 = 221075) B221075
theorem B147403 : Blo 143792 147403 := bstep (se 1 (by rfl) ⟨110552, by rfl⟩ : syracuseStep 147403 = 221105) B221105
theorem B147415 : Blo 143792 147415 := bstep (se 1 (by rfl) ⟨110561, by rfl⟩ : syracuseStep 147415 = 221123) B221123
theorem B147435 : Blo 143792 147435 := bstep (se 1 (by rfl) ⟨110576, by rfl⟩ : syracuseStep 147435 = 221153) B221153
theorem B147447 : Blo 143792 147447 := bstep (se 1 (by rfl) ⟨110585, by rfl⟩ : syracuseStep 147447 = 221171) B221171
theorem B147467 : Blo 143792 147467 := bstep (se 1 (by rfl) ⟨110600, by rfl⟩ : syracuseStep 147467 = 221201) B221201
theorem B147479 : Blo 143792 147479 := bstep (se 1 (by rfl) ⟨110609, by rfl⟩ : syracuseStep 147479 = 221219) B221219
theorem B147499 : Blo 143792 147499 := bstep (se 1 (by rfl) ⟨110624, by rfl⟩ : syracuseStep 147499 = 221249) B221249
theorem B147511 : Blo 143792 147511 := bstep (se 1 (by rfl) ⟨110633, by rfl⟩ : syracuseStep 147511 = 221267) B221267
theorem B147531 : Blo 143792 147531 := bstep (se 1 (by rfl) ⟨110648, by rfl⟩ : syracuseStep 147531 = 221297) B221297
theorem B278615 : Blo 143792 278615 := bstep (se 1 (by rfl) ⟨208961, by rfl⟩ : syracuseStep 278615 = 417923) B417923
theorem B147543 : Blo 143792 147543 := bstep (se 1 (by rfl) ⟨110657, by rfl⟩ : syracuseStep 147543 = 221315) B221315
theorem B147563 : Blo 143792 147563 := bstep (se 1 (by rfl) ⟨110672, by rfl⟩ : syracuseStep 147563 = 221345) B221345
theorem B147575 : Blo 143792 147575 := bstep (se 1 (by rfl) ⟨110681, by rfl⟩ : syracuseStep 147575 = 221363) B221363
theorem B311435 : Blo 143792 311435 := bstep (se 1 (by rfl) ⟨233576, by rfl⟩ : syracuseStep 311435 = 467153) B467153
theorem B147595 : Blo 143792 147595 := bstep (se 1 (by rfl) ⟨110696, by rfl⟩ : syracuseStep 147595 = 221393) B221393
theorem B147607 : Blo 143792 147607 := bstep (se 1 (by rfl) ⟨110705, by rfl⟩ : syracuseStep 147607 = 221411) B221411
theorem B147627 : Blo 143792 147627 := bstep (se 1 (by rfl) ⟨110720, by rfl⟩ : syracuseStep 147627 = 221441) B221441
theorem B147639 : Blo 143792 147639 := bstep (se 1 (by rfl) ⟨110729, by rfl⟩ : syracuseStep 147639 = 221459) B221459
theorem B245963 : Blo 143792 245963 := bstep (se 1 (by rfl) ⟨184472, by rfl⟩ : syracuseStep 245963 = 368945) B368945
theorem B147659 : Blo 143792 147659 := bstep (se 1 (by rfl) ⟨110744, by rfl⟩ : syracuseStep 147659 = 221489) B221489
theorem B147671 : Blo 143792 147671 := bstep (se 1 (by rfl) ⟨110753, by rfl⟩ : syracuseStep 147671 = 221507) B221507
theorem B147691 : Blo 143792 147691 := bstep (se 1 (by rfl) ⟨110768, by rfl⟩ : syracuseStep 147691 = 221537) B221537
theorem B147703 : Blo 143792 147703 := bstep (se 1 (by rfl) ⟨110777, by rfl⟩ : syracuseStep 147703 = 221555) B221555
theorem B147723 : Blo 143792 147723 := bstep (se 1 (by rfl) ⟨110792, by rfl⟩ : syracuseStep 147723 = 221585) B221585
theorem B377111 : Blo 143792 377111 := bstep (se 1 (by rfl) ⟨282833, by rfl⟩ : syracuseStep 377111 = 565667) B565667
theorem B147735 : Blo 143792 147735 := bstep (se 1 (by rfl) ⟨110801, by rfl⟩ : syracuseStep 147735 = 221603) B221603
theorem B1065251 : Blo 143792 1065251 := bstep (se 1 (by rfl) ⟨798938, by rfl⟩ : syracuseStep 1065251 = 1597877) B1597877
theorem B147755 : Blo 143792 147755 := bstep (se 1 (by rfl) ⟨110816, by rfl⟩ : syracuseStep 147755 = 221633) B221633
theorem B147767 : Blo 143792 147767 := bstep (se 1 (by rfl) ⟨110825, by rfl⟩ : syracuseStep 147767 = 221651) B221651
theorem B246091 : Blo 143792 246091 := bstep (se 1 (by rfl) ⟨184568, by rfl⟩ : syracuseStep 246091 = 369137) B369137
theorem B147787 : Blo 143792 147787 := bstep (se 1 (by rfl) ⟨110840, by rfl⟩ : syracuseStep 147787 = 221681) B221681
theorem B278873 : Blo 143792 278873 := bstep (se 2 (by rfl) ⟨104577, by rfl⟩ : syracuseStep 278873 = 209155) B209155
theorem B147895 : Blo 143792 147895 := bstep (se 1 (by rfl) ⟨110921, by rfl⟩ : syracuseStep 147895 = 221843) B221843
theorem B246233 : Blo 143792 246233 := bstep (se 2 (by rfl) ⟨92337, by rfl⟩ : syracuseStep 246233 = 184675) B184675
theorem B410177 : Blo 143792 410177 := bstep (se 2 (by rfl) ⟨153816, by rfl⟩ : syracuseStep 410177 = 307633) B307633
theorem B442945 : Blo 143792 442945 := bstep (se 2 (by rfl) ⟨166104, by rfl⟩ : syracuseStep 442945 = 332209) B332209
theorem B442955 : Blo 143792 442955 := bstep (se 1 (by rfl) ⟨332216, by rfl⟩ : syracuseStep 442955 = 664433) B664433
theorem B246361 : Blo 143792 246361 := bstep (se 2 (by rfl) ⟨92385, by rfl⟩ : syracuseStep 246361 = 184771) B184771
theorem B410291 : Blo 143792 410291 := bstep (se 1 (by rfl) ⟨307718, by rfl⟩ : syracuseStep 410291 = 615437) B615437
theorem B311987 : Blo 143792 311987 := bstep (se 1 (by rfl) ⟨233990, by rfl⟩ : syracuseStep 311987 = 467981) B467981
theorem B279283 : Blo 143792 279283 := bstep (se 1 (by rfl) ⟨209462, by rfl⟩ : syracuseStep 279283 = 418925) B418925
theorem B672605 : Blo 143792 672605 := bstep (se 3 (by rfl) ⟨126113, by rfl⟩ : syracuseStep 672605 = 252227) B252227
theorem B1197017 : Blo 143792 1197017 := bstep (se 2 (by rfl) ⟨448881, by rfl⟩ : syracuseStep 1197017 = 897763) B897763
theorem B312331 : Blo 143792 312331 := bstep (se 1 (by rfl) ⟨234248, by rfl⟩ : syracuseStep 312331 = 468497) B468497
theorem B1098845 : Blo 143792 1098845 := bstep (se 3 (by rfl) ⟨206033, by rfl⟩ : syracuseStep 1098845 = 412067) B412067
theorem B705667 : Blo 143792 705667 := bstep (se 1 (by rfl) ⟨529250, by rfl⟩ : syracuseStep 705667 = 1058501) B1058501
theorem B246935 : Blo 143792 246935 := bstep (se 1 (by rfl) ⟨185201, by rfl⟩ : syracuseStep 246935 = 370403) B370403
theorem B279769 : Blo 143792 279769 := bstep (se 2 (by rfl) ⟨104913, by rfl⟩ : syracuseStep 279769 = 209827) B209827
theorem B247063 : Blo 143792 247063 := bstep (se 1 (by rfl) ⟨185297, by rfl⟩ : syracuseStep 247063 = 370595) B370595
theorem B935441 : Blo 143792 935441 := bstep (se 2 (by rfl) ⟨350790, by rfl⟩ : syracuseStep 935441 = 701581) B701581
theorem B738881 : Blo 143792 738881 := bstep (se 2 (by rfl) ⟨277080, by rfl⟩ : syracuseStep 738881 = 554161) B554161
theorem B706265 : Blo 143792 706265 := bstep (se 2 (by rfl) ⟨264849, by rfl⟩ : syracuseStep 706265 = 529699) B529699
theorem B313075 : Blo 143792 313075 := bstep (se 1 (by rfl) ⟨234806, by rfl⟩ : syracuseStep 313075 = 469613) B469613
theorem B182027 : Blo 143792 182027 := bstep (se 1 (by rfl) ⟨136520, by rfl⟩ : syracuseStep 182027 = 273041) B273041
theorem B280331 : Blo 143792 280331 := bstep (se 1 (by rfl) ⟨210248, by rfl⟩ : syracuseStep 280331 = 420497) B420497
theorem B149303 : Blo 143792 149303 := bstep (se 1 (by rfl) ⟨111977, by rfl⟩ : syracuseStep 149303 = 223955) B223955
theorem B247691 : Blo 143792 247691 := bstep (se 1 (by rfl) ⟨185768, by rfl⟩ : syracuseStep 247691 = 371537) B371537
theorem B280513 : Blo 143792 280513 := bstep (se 2 (by rfl) ⟨105192, by rfl⟩ : syracuseStep 280513 = 210385) B210385
theorem B247819 : Blo 143792 247819 := bstep (se 1 (by rfl) ⟨185864, by rfl⟩ : syracuseStep 247819 = 371729) B371729
theorem B247961 : Blo 143792 247961 := bstep (se 2 (by rfl) ⟨92985, by rfl⟩ : syracuseStep 247961 = 185971) B185971
theorem B379073 : Blo 143792 379073 := bstep (se 2 (by rfl) ⟨142152, by rfl⟩ : syracuseStep 379073 = 284305) B284305
theorem B313561 : Blo 143792 313561 := bstep (se 2 (by rfl) ⟨117585, by rfl⟩ : syracuseStep 313561 = 235171) B235171
theorem B248089 : Blo 143792 248089 := bstep (se 2 (by rfl) ⟨93033, by rfl⟩ : syracuseStep 248089 = 186067) B186067
theorem B182731 : Blo 143792 182731 := bstep (se 1 (by rfl) ⟨137048, by rfl⟩ : syracuseStep 182731 = 274097) B274097
theorem B215705 : Blo 143792 215705 := bstep (se 2 (by rfl) ⟨80889, by rfl⟩ : syracuseStep 215705 = 161779) B161779
theorem B182999 : Blo 143792 182999 := bstep (se 1 (by rfl) ⟨137249, by rfl⟩ : syracuseStep 182999 = 274499) B274499
theorem B215819 : Blo 143792 215819 := bstep (se 1 (by rfl) ⟨161864, by rfl⟩ : syracuseStep 215819 = 323729) B323729
theorem B215831 : Blo 143792 215831 := bstep (se 1 (by rfl) ⟨161873, by rfl⟩ : syracuseStep 215831 = 323747) B323747
theorem B740141 : Blo 143792 740141 := bstep (se 3 (by rfl) ⟨138776, by rfl⟩ : syracuseStep 740141 = 277553) B277553
theorem B248663 : Blo 143792 248663 := bstep (se 1 (by rfl) ⟨186497, by rfl⟩ : syracuseStep 248663 = 372995) B372995
theorem B215897 : Blo 143792 215897 := bstep (se 2 (by rfl) ⟨80961, by rfl⟩ : syracuseStep 215897 = 161923) B161923
theorem B216011 : Blo 143792 216011 := bstep (se 1 (by rfl) ⟨162008, by rfl⟩ : syracuseStep 216011 = 324017) B324017
theorem B216023 : Blo 143792 216023 := bstep (se 1 (by rfl) ⟨162017, by rfl⟩ : syracuseStep 216023 = 324035) B324035
theorem B248791 : Blo 143792 248791 := bstep (se 1 (by rfl) ⟨186593, by rfl⟩ : syracuseStep 248791 = 373187) B373187
theorem B216089 : Blo 143792 216089 := bstep (se 2 (by rfl) ⟨81033, by rfl⟩ : syracuseStep 216089 = 162067) B162067
theorem B150571 : Blo 143792 150571 := bstep (se 1 (by rfl) ⟨112928, by rfl⟩ : syracuseStep 150571 = 225857) B225857
theorem B216203 : Blo 143792 216203 := bstep (se 1 (by rfl) ⟨162152, by rfl⟩ : syracuseStep 216203 = 324305) B324305
theorem B216215 : Blo 143792 216215 := bstep (se 1 (by rfl) ⟨162161, by rfl⟩ : syracuseStep 216215 = 324323) B324323
theorem B216281 : Blo 143792 216281 := bstep (se 2 (by rfl) ⟨81105, by rfl⟩ : syracuseStep 216281 = 162211) B162211
theorem B216395 : Blo 143792 216395 := bstep (se 1 (by rfl) ⟨162296, by rfl⟩ : syracuseStep 216395 = 324593) B324593
theorem B216407 : Blo 143792 216407 := bstep (se 1 (by rfl) ⟨162305, by rfl⟩ : syracuseStep 216407 = 324611) B324611
theorem B183703 : Blo 143792 183703 := bstep (se 1 (by rfl) ⟨137777, by rfl⟩ : syracuseStep 183703 = 275555) B275555
theorem B216473 : Blo 143792 216473 := bstep (se 2 (by rfl) ⟨81177, by rfl⟩ : syracuseStep 216473 = 162355) B162355
theorem B740825 : Blo 143792 740825 := bstep (se 2 (by rfl) ⟨277809, by rfl⟩ : syracuseStep 740825 = 555619) B555619
theorem B216587 : Blo 143792 216587 := bstep (se 1 (by rfl) ⟨162440, by rfl⟩ : syracuseStep 216587 = 324881) B324881
theorem B216599 : Blo 143792 216599 := bstep (se 1 (by rfl) ⟨162449, by rfl⟩ : syracuseStep 216599 = 324899) B324899
theorem B413207 : Blo 143792 413207 := bstep (se 1 (by rfl) ⟨309905, by rfl⟩ : syracuseStep 413207 = 619811) B619811
theorem B216665 : Blo 143792 216665 := bstep (se 2 (by rfl) ⟨81249, by rfl⟩ : syracuseStep 216665 = 162499) B162499
theorem B839261 : Blo 143792 839261 := bstep (se 3 (by rfl) ⟨157361, by rfl⟩ : syracuseStep 839261 = 314723) B314723
theorem B1363549 : Blo 143792 1363549 := bstep (se 3 (by rfl) ⟨255665, by rfl⟩ : syracuseStep 1363549 = 511331) B511331
theorem B315031 : Blo 143792 315031 := bstep (se 1 (by rfl) ⟨236273, by rfl⟩ : syracuseStep 315031 = 472547) B472547
theorem B2248373 : Blo 143792 2248373 := bstep (se 5 (by rfl) ⟨105392, by rfl⟩ : syracuseStep 2248373 = 210785) B210785
theorem B216779 : Blo 143792 216779 := bstep (se 1 (by rfl) ⟨162584, by rfl⟩ : syracuseStep 216779 = 325169) B325169
theorem B315083 : Blo 143792 315083 := bstep (se 1 (by rfl) ⟨236312, by rfl⟩ : syracuseStep 315083 = 472625) B472625
theorem B216791 : Blo 143792 216791 := bstep (se 1 (by rfl) ⟨162593, by rfl⟩ : syracuseStep 216791 = 325187) B325187
theorem B216857 : Blo 143792 216857 := bstep (se 2 (by rfl) ⟨81321, by rfl⟩ : syracuseStep 216857 = 162643) B162643
theorem B216971 : Blo 143792 216971 := bstep (se 1 (by rfl) ⟨162728, by rfl⟩ : syracuseStep 216971 = 325457) B325457
theorem B216983 : Blo 143792 216983 := bstep (se 1 (by rfl) ⟨162737, by rfl⟩ : syracuseStep 216983 = 325475) B325475
theorem B217049 : Blo 143792 217049 := bstep (se 2 (by rfl) ⟨81393, by rfl⟩ : syracuseStep 217049 = 162787) B162787
theorem B217163 : Blo 143792 217163 := bstep (se 1 (by rfl) ⟨162872, by rfl⟩ : syracuseStep 217163 = 325745) B325745
theorem B217175 : Blo 143792 217175 := bstep (se 1 (by rfl) ⟨162881, by rfl⟩ : syracuseStep 217175 = 325763) B325763
theorem B217241 : Blo 143792 217241 := bstep (se 2 (by rfl) ⟨81465, by rfl⟩ : syracuseStep 217241 = 162931) B162931
theorem B512173 : Blo 143792 512173 := bstep (se 3 (by rfl) ⟨96032, by rfl⟩ : syracuseStep 512173 = 192065) B192065
theorem B4837637 : Blo 143792 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B217355 : Blo 143792 217355 := bstep (se 1 (by rfl) ⟨163016, by rfl⟩ : syracuseStep 217355 = 326033) B326033
theorem B217367 : Blo 143792 217367 := bstep (se 1 (by rfl) ⟨163025, by rfl⟩ : syracuseStep 217367 = 326051) B326051
theorem B217433 : Blo 143792 217433 := bstep (se 2 (by rfl) ⟨81537, by rfl⟩ : syracuseStep 217433 = 163075) B163075
theorem B217547 : Blo 143792 217547 := bstep (se 1 (by rfl) ⟨163160, by rfl⟩ : syracuseStep 217547 = 326321) B326321
theorem B217559 : Blo 143792 217559 := bstep (se 1 (by rfl) ⟨163169, by rfl⟩ : syracuseStep 217559 = 326339) B326339
theorem B217625 : Blo 143792 217625 := bstep (se 2 (by rfl) ⟨81609, by rfl⟩ : syracuseStep 217625 = 163219) B163219
theorem B217739 : Blo 143792 217739 := bstep (se 1 (by rfl) ⟨163304, by rfl⟩ : syracuseStep 217739 = 326609) B326609
theorem B217751 : Blo 143792 217751 := bstep (se 1 (by rfl) ⟨163313, by rfl⟩ : syracuseStep 217751 = 326627) B326627
theorem B217817 : Blo 143792 217817 := bstep (se 2 (by rfl) ⟨81681, by rfl⟩ : syracuseStep 217817 = 163363) B163363
theorem B217931 : Blo 143792 217931 := bstep (se 1 (by rfl) ⟨163448, by rfl⟩ : syracuseStep 217931 = 326897) B326897
theorem B217943 : Blo 143792 217943 := bstep (se 1 (by rfl) ⟨163457, by rfl⟩ : syracuseStep 217943 = 326915) B326915
theorem B218009 : Blo 143792 218009 := bstep (se 2 (by rfl) ⟨81753, by rfl⟩ : syracuseStep 218009 = 163507) B163507
theorem B218123 : Blo 143792 218123 := bstep (se 1 (by rfl) ⟨163592, by rfl⟩ : syracuseStep 218123 = 327185) B327185
theorem B218135 : Blo 143792 218135 := bstep (se 1 (by rfl) ⟨163601, by rfl⟩ : syracuseStep 218135 = 327203) B327203
theorem B742445 : Blo 143792 742445 := bstep (se 3 (by rfl) ⟨139208, by rfl⟩ : syracuseStep 742445 = 278417) B278417
theorem B185419 : Blo 143792 185419 := bstep (se 1 (by rfl) ⟨139064, by rfl⟩ : syracuseStep 185419 = 278129) B278129
theorem B218201 : Blo 143792 218201 := bstep (se 2 (by rfl) ⟨81825, by rfl⟩ : syracuseStep 218201 = 163651) B163651
theorem B218315 : Blo 143792 218315 := bstep (se 1 (by rfl) ⟨163736, by rfl⟩ : syracuseStep 218315 = 327473) B327473
theorem B218327 : Blo 143792 218327 := bstep (se 1 (by rfl) ⟨163745, by rfl⟩ : syracuseStep 218327 = 327491) B327491
theorem B1135889 : Blo 143792 1135889 := bstep (se 2 (by rfl) ⟨425958, by rfl⟩ : syracuseStep 1135889 = 851917) B851917
theorem B218393 : Blo 143792 218393 := bstep (se 2 (by rfl) ⟨81897, by rfl⟩ : syracuseStep 218393 = 163795) B163795
theorem B218507 : Blo 143792 218507 := bstep (se 1 (by rfl) ⟨163880, by rfl⟩ : syracuseStep 218507 = 327761) B327761
theorem B218519 : Blo 143792 218519 := bstep (se 1 (by rfl) ⟨163889, by rfl⟩ : syracuseStep 218519 = 327779) B327779
theorem B710039 : Blo 143792 710039 := bstep (se 1 (by rfl) ⟨532529, by rfl⟩ : syracuseStep 710039 = 1065059) B1065059
theorem B349643 : Blo 143792 349643 := bstep (se 1 (by rfl) ⟨262232, by rfl⟩ : syracuseStep 349643 = 524465) B524465
theorem B218585 : Blo 143792 218585 := bstep (se 2 (by rfl) ⟨81969, by rfl⟩ : syracuseStep 218585 = 163939) B163939
theorem B218699 : Blo 143792 218699 := bstep (se 1 (by rfl) ⟨164024, by rfl⟩ : syracuseStep 218699 = 328049) B328049
theorem B218711 : Blo 143792 218711 := bstep (se 1 (by rfl) ⟨164033, by rfl⟩ : syracuseStep 218711 = 328067) B328067
theorem B218777 : Blo 143792 218777 := bstep (se 2 (by rfl) ⟨82041, by rfl⟩ : syracuseStep 218777 = 164083) B164083
theorem B349913 : Blo 143792 349913 := bstep (se 2 (by rfl) ⟨131217, by rfl⟩ : syracuseStep 349913 = 262435) B262435
theorem B218891 : Blo 143792 218891 := bstep (se 1 (by rfl) ⟨164168, by rfl⟩ : syracuseStep 218891 = 328337) B328337
theorem B218903 : Blo 143792 218903 := bstep (se 1 (by rfl) ⟨164177, by rfl⟩ : syracuseStep 218903 = 328355) B328355
theorem B218969 : Blo 143792 218969 := bstep (se 2 (by rfl) ⟨82113, by rfl⟩ : syracuseStep 218969 = 164227) B164227
theorem B186251 : Blo 143792 186251 := bstep (se 1 (by rfl) ⟨139688, by rfl⟩ : syracuseStep 186251 = 279377) B279377
theorem B415667 : Blo 143792 415667 := bstep (se 1 (by rfl) ⟨311750, by rfl⟩ : syracuseStep 415667 = 623501) B623501
theorem B219083 : Blo 143792 219083 := bstep (se 1 (by rfl) ⟨164312, by rfl⟩ : syracuseStep 219083 = 328625) B328625
theorem B219095 : Blo 143792 219095 := bstep (se 1 (by rfl) ⟨164321, by rfl⟩ : syracuseStep 219095 = 328643) B328643
theorem B186391 : Blo 143792 186391 := bstep (se 1 (by rfl) ⟨139793, by rfl⟩ : syracuseStep 186391 = 279587) B279587
theorem B219161 : Blo 143792 219161 := bstep (se 2 (by rfl) ⟨82185, by rfl⟩ : syracuseStep 219161 = 164371) B164371
theorem B350297 : Blo 143792 350297 := bstep (se 2 (by rfl) ⟨131361, by rfl⟩ : syracuseStep 350297 = 262723) B262723
theorem B219275 : Blo 143792 219275 := bstep (se 1 (by rfl) ⟨164456, by rfl⟩ : syracuseStep 219275 = 328913) B328913
theorem B219287 : Blo 143792 219287 := bstep (se 1 (by rfl) ⟨164465, by rfl⟩ : syracuseStep 219287 = 328931) B328931
theorem B252119 : Blo 143792 252119 := bstep (se 1 (by rfl) ⟨189089, by rfl⟩ : syracuseStep 252119 = 378179) B378179
theorem B219353 : Blo 143792 219353 := bstep (se 2 (by rfl) ⟨82257, by rfl⟩ : syracuseStep 219353 = 164515) B164515
theorem B219467 : Blo 143792 219467 := bstep (se 1 (by rfl) ⟨164600, by rfl⟩ : syracuseStep 219467 = 329201) B329201
theorem B219479 : Blo 143792 219479 := bstep (se 1 (by rfl) ⟨164609, by rfl⟩ : syracuseStep 219479 = 329219) B329219
theorem B1169795 : Blo 143792 1169795 := bstep (se 1 (by rfl) ⟨877346, by rfl⟩ : syracuseStep 1169795 = 1754693) B1754693
theorem B219545 : Blo 143792 219545 := bstep (se 2 (by rfl) ⟨82329, by rfl⟩ : syracuseStep 219545 = 164659) B164659
theorem B219659 : Blo 143792 219659 := bstep (se 1 (by rfl) ⟨164744, by rfl⟩ : syracuseStep 219659 = 329489) B329489
theorem B219671 : Blo 143792 219671 := bstep (se 1 (by rfl) ⟨164753, by rfl⟩ : syracuseStep 219671 = 329507) B329507
theorem B219737 : Blo 143792 219737 := bstep (se 2 (by rfl) ⟨82401, by rfl⟩ : syracuseStep 219737 = 164803) B164803
theorem B219851 : Blo 143792 219851 := bstep (se 1 (by rfl) ⟨164888, by rfl⟩ : syracuseStep 219851 = 329777) B329777
theorem B219863 : Blo 143792 219863 := bstep (se 1 (by rfl) ⟨164897, by rfl⟩ : syracuseStep 219863 = 329795) B329795
theorem B219929 : Blo 143792 219929 := bstep (se 2 (by rfl) ⟨82473, by rfl⟩ : syracuseStep 219929 = 164947) B164947
theorem B154423 : Blo 143792 154423 := bstep (se 1 (by rfl) ⟨115817, by rfl⟩ : syracuseStep 154423 = 231635) B231635
theorem B351065 : Blo 143792 351065 := bstep (se 2 (by rfl) ⟨131649, by rfl⟩ : syracuseStep 351065 = 263299) B263299
theorem B220043 : Blo 143792 220043 := bstep (se 1 (by rfl) ⟨165032, by rfl⟩ : syracuseStep 220043 = 330065) B330065
theorem B220055 : Blo 143792 220055 := bstep (se 1 (by rfl) ⟨165041, by rfl⟩ : syracuseStep 220055 = 330083) B330083
theorem B220121 : Blo 143792 220121 := bstep (se 2 (by rfl) ⟨82545, by rfl⟩ : syracuseStep 220121 = 165091) B165091
theorem B547843 : Blo 143792 547843 := bstep (se 1 (by rfl) ⟨410882, by rfl⟩ : syracuseStep 547843 = 821765) B821765
theorem B220235 : Blo 143792 220235 := bstep (se 1 (by rfl) ⟨165176, by rfl⟩ : syracuseStep 220235 = 330353) B330353
theorem B220247 : Blo 143792 220247 := bstep (se 1 (by rfl) ⟨165185, by rfl⟩ : syracuseStep 220247 = 330371) B330371
theorem B220313 : Blo 143792 220313 := bstep (se 2 (by rfl) ⟨82617, by rfl⟩ : syracuseStep 220313 = 165235) B165235
theorem B220427 : Blo 143792 220427 := bstep (se 1 (by rfl) ⟨165320, by rfl⟩ : syracuseStep 220427 = 330641) B330641
theorem B220439 : Blo 143792 220439 := bstep (se 1 (by rfl) ⟨165329, by rfl⟩ : syracuseStep 220439 = 330659) B330659
theorem B548147 : Blo 143792 548147 := bstep (se 1 (by rfl) ⟨411110, by rfl⟩ : syracuseStep 548147 = 822221) B822221
theorem B220505 : Blo 143792 220505 := bstep (se 2 (by rfl) ⟨82689, by rfl⟩ : syracuseStep 220505 = 165379) B165379
theorem B220619 : Blo 143792 220619 := bstep (se 1 (by rfl) ⟨165464, by rfl⟩ : syracuseStep 220619 = 330929) B330929
theorem B220631 : Blo 143792 220631 := bstep (se 1 (by rfl) ⟨165473, by rfl⟩ : syracuseStep 220631 = 330947) B330947
theorem B220697 : Blo 143792 220697 := bstep (se 2 (by rfl) ⟨82761, by rfl⟩ : syracuseStep 220697 = 165523) B165523
theorem B1236545 : Blo 143792 1236545 := bstep (se 2 (by rfl) ⟨463704, by rfl⟩ : syracuseStep 1236545 = 927409) B927409
theorem B155243 : Blo 143792 155243 := bstep (se 1 (by rfl) ⟨116432, by rfl⟩ : syracuseStep 155243 = 232865) B232865
theorem B220811 : Blo 143792 220811 := bstep (se 1 (by rfl) ⟨165608, by rfl⟩ : syracuseStep 220811 = 331217) B331217
theorem B220823 : Blo 143792 220823 := bstep (se 1 (by rfl) ⟨165617, by rfl⟩ : syracuseStep 220823 = 331235) B331235
theorem B2088629 : Blo 143792 2088629 := bstep (se 5 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 2088629 = 195809) B195809
theorem B220889 : Blo 143792 220889 := bstep (se 2 (by rfl) ⟨82833, by rfl⟩ : syracuseStep 220889 = 165667) B165667
theorem B778049 : Blo 143792 778049 := bstep (se 2 (by rfl) ⟨291768, by rfl⟩ : syracuseStep 778049 = 583537) B583537
theorem B319297 : Blo 143792 319297 := bstep (se 2 (by rfl) ⟨119736, by rfl⟩ : syracuseStep 319297 = 239473) B239473
theorem B221003 : Blo 143792 221003 := bstep (se 1 (by rfl) ⟨165752, by rfl⟩ : syracuseStep 221003 = 331505) B331505
theorem B221015 : Blo 143792 221015 := bstep (se 1 (by rfl) ⟨165761, by rfl⟩ : syracuseStep 221015 = 331523) B331523
theorem B221081 : Blo 143792 221081 := bstep (se 2 (by rfl) ⟨82905, by rfl⟩ : syracuseStep 221081 = 165811) B165811
theorem B548801 : Blo 143792 548801 := bstep (se 2 (by rfl) ⟨205800, by rfl⟩ : syracuseStep 548801 = 411601) B411601
theorem B221195 : Blo 143792 221195 := bstep (se 1 (by rfl) ⟨165896, by rfl⟩ : syracuseStep 221195 = 331793) B331793
theorem B221207 : Blo 143792 221207 := bstep (se 1 (by rfl) ⟨165905, by rfl⟩ : syracuseStep 221207 = 331811) B331811
theorem B221273 : Blo 143792 221273 := bstep (se 2 (by rfl) ⟨82977, by rfl⟩ : syracuseStep 221273 = 165955) B165955
theorem B221387 : Blo 143792 221387 := bstep (se 1 (by rfl) ⟨166040, by rfl⟩ : syracuseStep 221387 = 332081) B332081
theorem B221399 : Blo 143792 221399 := bstep (se 1 (by rfl) ⟨166049, by rfl⟩ : syracuseStep 221399 = 332099) B332099
theorem B221465 : Blo 143792 221465 := bstep (se 2 (by rfl) ⟨83049, by rfl⟩ : syracuseStep 221465 = 166099) B166099
theorem B221579 : Blo 143792 221579 := bstep (se 1 (by rfl) ⟨166184, by rfl⟩ : syracuseStep 221579 = 332369) B332369
theorem B221591 : Blo 143792 221591 := bstep (se 1 (by rfl) ⟨166193, by rfl⟩ : syracuseStep 221591 = 332387) B332387
theorem B287129 : Blo 143792 287129 := bstep (se 2 (by rfl) ⟨107673, by rfl⟩ : syracuseStep 287129 = 215347) B215347
theorem B221657 : Blo 143792 221657 := bstep (se 2 (by rfl) ⟨83121, by rfl⟩ : syracuseStep 221657 = 166243) B166243
theorem B418355 : Blo 143792 418355 := bstep (se 1 (by rfl) ⟨313766, by rfl⟩ : syracuseStep 418355 = 627533) B627533
theorem B1040971 : Blo 143792 1040971 := bstep (se 1 (by rfl) ⟨780728, by rfl⟩ : syracuseStep 1040971 = 1561457) B1561457
theorem B156439 : Blo 143792 156439 := bstep (se 1 (by rfl) ⟨117329, by rfl⟩ : syracuseStep 156439 = 234659) B234659
theorem B418583 : Blo 143792 418583 := bstep (se 1 (by rfl) ⟨313937, by rfl⟩ : syracuseStep 418583 = 627875) B627875
theorem B746333 : Blo 143792 746333 := bstep (se 3 (by rfl) ⟨139937, by rfl⟩ : syracuseStep 746333 = 279875) B279875
theorem B418891 : Blo 143792 418891 := bstep (se 1 (by rfl) ⟨314168, by rfl⟩ : syracuseStep 418891 = 628337) B628337
theorem B156811 : Blo 143792 156811 := bstep (se 1 (by rfl) ⟨117608, by rfl⟩ : syracuseStep 156811 = 235217) B235217
theorem B746647 : Blo 143792 746647 := bstep (se 1 (by rfl) ⟨559985, by rfl⟩ : syracuseStep 746647 = 1119971) B1119971
theorem B550061 : Blo 143792 550061 := bstep (se 3 (by rfl) ⟨103136, by rfl⟩ : syracuseStep 550061 = 206273) B206273
theorem B550091 : Blo 143792 550091 := bstep (se 1 (by rfl) ⟨412568, by rfl⟩ : syracuseStep 550091 = 825137) B825137
theorem B419165 : Blo 143792 419165 := bstep (se 3 (by rfl) ⟨78593, by rfl⟩ : syracuseStep 419165 = 157187) B157187
theorem B1598899 : Blo 143792 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B157259 : Blo 143792 157259 := bstep (se 1 (by rfl) ⟨117944, by rfl⟩ : syracuseStep 157259 = 235889) B235889
theorem B550745 : Blo 143792 550745 := bstep (se 2 (by rfl) ⟨206529, by rfl⟩ : syracuseStep 550745 = 413059) B413059
theorem B1238935 : Blo 143792 1238935 := bstep (se 1 (by rfl) ⟨929201, by rfl⟩ : syracuseStep 1238935 = 1858403) B1858403
theorem B223193 : Blo 143792 223193 := bstep (se 2 (by rfl) ⟨83697, by rfl⟩ : syracuseStep 223193 = 167395) B167395
theorem B551063 : Blo 143792 551063 := bstep (se 1 (by rfl) ⟨413297, by rfl⟩ : syracuseStep 551063 = 826595) B826595
theorem B583859 : Blo 143792 583859 := bstep (se 1 (by rfl) ⟨437894, by rfl⟩ : syracuseStep 583859 = 875789) B875789
theorem B878809 : Blo 143792 878809 := bstep (se 2 (by rfl) ⟨329553, by rfl⟩ : syracuseStep 878809 = 659107) B659107
theorem B1042789 : Blo 143792 1042789 := bstep (se 4 (by rfl) ⟨97761, by rfl⟩ : syracuseStep 1042789 = 195523) B195523
theorem B485783 : Blo 143792 485783 := bstep (se 1 (by rfl) ⟨364337, by rfl⟩ : syracuseStep 485783 = 728675) B728675
theorem B616855 : Blo 143792 616855 := bstep (se 1 (by rfl) ⟨462641, by rfl⟩ : syracuseStep 616855 = 925283) B925283
theorem B551731 : Blo 143792 551731 := bstep (se 1 (by rfl) ⟨413798, by rfl⟩ : syracuseStep 551731 = 827597) B827597
theorem B486323 : Blo 143792 486323 := bstep (se 1 (by rfl) ⟨364742, by rfl⟩ : syracuseStep 486323 = 729485) B729485
theorem B486593 : Blo 143792 486593 := bstep (se 2 (by rfl) ⟨182472, by rfl⟩ : syracuseStep 486593 = 364945) B364945
theorem B1404377 : Blo 143792 1404377 := bstep (se 2 (by rfl) ⟨526641, by rfl⟩ : syracuseStep 1404377 = 1053283) B1053283
theorem B2420375 : Blo 143792 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B13758149 : Blo 143792 13758149 := bstep (se 4 (by rfl) ⟨1289826, by rfl⟩ : syracuseStep 13758149 = 2579653) B2579653
theorem B487133 : Blo 143792 487133 := bstep (se 3 (by rfl) ⟨91337, by rfl⟩ : syracuseStep 487133 = 182675) B182675
theorem B225163 : Blo 143792 225163 := bstep (se 1 (by rfl) ⟨168872, by rfl⟩ : syracuseStep 225163 = 337745) B337745
theorem B520139 : Blo 143792 520139 := bstep (se 1 (by rfl) ⟨390104, by rfl⟩ : syracuseStep 520139 = 780209) B780209
theorem B323585 : Blo 143792 323585 := bstep (se 2 (by rfl) ⟨121344, by rfl⟩ : syracuseStep 323585 = 242689) B242689
theorem B552977 : Blo 143792 552977 := bstep (se 2 (by rfl) ⟨207366, by rfl⟩ : syracuseStep 552977 = 414733) B414733
theorem B323801 : Blo 143792 323801 := bstep (se 2 (by rfl) ⟨121425, by rfl⟩ : syracuseStep 323801 = 242851) B242851
theorem B323891 : Blo 143792 323891 := bstep (se 1 (by rfl) ⟨242918, by rfl⟩ : syracuseStep 323891 = 485837) B485837
theorem B323927 : Blo 143792 323927 := bstep (se 1 (by rfl) ⟨242945, by rfl⟩ : syracuseStep 323927 = 485891) B485891
theorem B258419 : Blo 143792 258419 := bstep (se 1 (by rfl) ⟨193814, by rfl⟩ : syracuseStep 258419 = 387629) B387629
theorem B324107 : Blo 143792 324107 := bstep (se 1 (by rfl) ⟨243080, by rfl⟩ : syracuseStep 324107 = 486161) B486161
theorem B324161 : Blo 143792 324161 := bstep (se 2 (by rfl) ⟨121560, by rfl⟩ : syracuseStep 324161 = 243121) B243121
theorem B225931 : Blo 143792 225931 := bstep (se 1 (by rfl) ⟨169448, by rfl⟩ : syracuseStep 225931 = 338897) B338897
theorem B750259 : Blo 143792 750259 := bstep (se 1 (by rfl) ⟨562694, by rfl⟩ : syracuseStep 750259 = 1125389) B1125389
theorem B553675 : Blo 143792 553675 := bstep (se 1 (by rfl) ⟨415256, by rfl⟩ : syracuseStep 553675 = 830513) B830513
theorem B324377 : Blo 143792 324377 := bstep (se 2 (by rfl) ⟨121641, by rfl⟩ : syracuseStep 324377 = 243283) B243283
theorem B488267 : Blo 143792 488267 := bstep (se 1 (by rfl) ⟨366200, by rfl⟩ : syracuseStep 488267 = 732401) B732401
theorem B324467 : Blo 143792 324467 := bstep (se 1 (by rfl) ⟨243350, by rfl⟩ : syracuseStep 324467 = 486701) B486701
theorem B324503 : Blo 143792 324503 := bstep (se 1 (by rfl) ⟨243377, by rfl⟩ : syracuseStep 324503 = 486755) B486755
theorem B291737 : Blo 143792 291737 := bstep (se 2 (by rfl) ⟨109401, by rfl⟩ : syracuseStep 291737 = 218803) B218803
theorem B553949 : Blo 143792 553949 := bstep (se 3 (by rfl) ⟨103865, by rfl⟩ : syracuseStep 553949 = 207731) B207731
theorem B259147 : Blo 143792 259147 := bstep (se 1 (by rfl) ⟨194360, by rfl⟩ : syracuseStep 259147 = 388721) B388721
theorem B324683 : Blo 143792 324683 := bstep (se 1 (by rfl) ⟨243512, by rfl⟩ : syracuseStep 324683 = 487025) B487025
theorem B488537 : Blo 143792 488537 := bstep (se 2 (by rfl) ⟨183201, by rfl⟩ : syracuseStep 488537 = 366403) B366403
theorem B324737 : Blo 143792 324737 := bstep (se 2 (by rfl) ⟨121776, by rfl⟩ : syracuseStep 324737 = 243553) B243553
theorem B619741 : Blo 143792 619741 := bstep (se 3 (by rfl) ⟨116201, by rfl⟩ : syracuseStep 619741 = 232403) B232403
theorem B324953 : Blo 143792 324953 := bstep (se 2 (by rfl) ⟨121857, by rfl⟩ : syracuseStep 324953 = 243715) B243715
theorem B325043 : Blo 143792 325043 := bstep (se 1 (by rfl) ⟨243782, by rfl⟩ : syracuseStep 325043 = 487565) B487565
theorem B325079 : Blo 143792 325079 := bstep (se 1 (by rfl) ⟨243809, by rfl⟩ : syracuseStep 325079 = 487619) B487619
theorem B325259 : Blo 143792 325259 := bstep (se 1 (by rfl) ⟨243944, by rfl⟩ : syracuseStep 325259 = 487889) B487889
theorem B554647 : Blo 143792 554647 := bstep (se 1 (by rfl) ⟨415985, by rfl⟩ : syracuseStep 554647 = 831971) B831971
theorem B325313 : Blo 143792 325313 := bstep (se 2 (by rfl) ⟨121992, by rfl⟩ : syracuseStep 325313 = 243985) B243985
theorem B489239 : Blo 143792 489239 := bstep (se 1 (by rfl) ⟨366929, by rfl⟩ : syracuseStep 489239 = 733859) B733859
theorem B325529 : Blo 143792 325529 := bstep (se 2 (by rfl) ⟨122073, by rfl⟩ : syracuseStep 325529 = 244147) B244147
theorem B1898417 : Blo 143792 1898417 := bstep (se 2 (by rfl) ⟨711906, by rfl⟩ : syracuseStep 1898417 = 1423813) B1423813
theorem B325619 : Blo 143792 325619 := bstep (se 1 (by rfl) ⟨244214, by rfl⟩ : syracuseStep 325619 = 488429) B488429
theorem B620561 : Blo 143792 620561 := bstep (se 2 (by rfl) ⟨232710, by rfl⟩ : syracuseStep 620561 = 465421) B465421
theorem B161815 : Blo 143792 161815 := bstep (se 1 (by rfl) ⟨121361, by rfl⟩ : syracuseStep 161815 = 242723) B242723
theorem B325655 : Blo 143792 325655 := bstep (se 1 (by rfl) ⟨244241, by rfl⟩ : syracuseStep 325655 = 488483) B488483
theorem B6715543 : Blo 143792 6715543 := bstep (se 1 (by rfl) ⟨5036657, by rfl⟩ : syracuseStep 6715543 = 10073315) B10073315
theorem B161995 : Blo 143792 161995 := bstep (se 1 (by rfl) ⟨121496, by rfl⟩ : syracuseStep 161995 = 242993) B242993
theorem B325835 : Blo 143792 325835 := bstep (se 1 (by rfl) ⟨244376, by rfl⟩ : syracuseStep 325835 = 488753) B488753
theorem B325889 : Blo 143792 325889 := bstep (se 2 (by rfl) ⟨122208, by rfl⟩ : syracuseStep 325889 = 244417) B244417
theorem B489779 : Blo 143792 489779 := bstep (se 1 (by rfl) ⟨367334, by rfl⟩ : syracuseStep 489779 = 734669) B734669
theorem B162103 : Blo 143792 162103 := bstep (se 1 (by rfl) ⟨121577, by rfl⟩ : syracuseStep 162103 = 243155) B243155
theorem B2128193 : Blo 143792 2128193 := bstep (se 2 (by rfl) ⟨798072, by rfl⟩ : syracuseStep 2128193 = 1596145) B1596145
theorem B194891 : Blo 143792 194891 := bstep (se 1 (by rfl) ⟨146168, by rfl⟩ : syracuseStep 194891 = 292337) B292337
theorem B555437 : Blo 143792 555437 := bstep (se 3 (by rfl) ⟨104144, by rfl⟩ : syracuseStep 555437 = 208289) B208289
theorem B326105 : Blo 143792 326105 := bstep (se 2 (by rfl) ⟨122289, by rfl⟩ : syracuseStep 326105 = 244579) B244579
theorem B162283 : Blo 143792 162283 := bstep (se 1 (by rfl) ⟨121712, by rfl⟩ : syracuseStep 162283 = 243425) B243425
theorem B326195 : Blo 143792 326195 := bstep (se 1 (by rfl) ⟨244646, by rfl⟩ : syracuseStep 326195 = 489293) B489293
theorem B490049 : Blo 143792 490049 := bstep (se 2 (by rfl) ⟨183768, by rfl⟩ : syracuseStep 490049 = 367537) B367537
theorem B162391 : Blo 143792 162391 := bstep (se 1 (by rfl) ⟨121793, by rfl⟩ : syracuseStep 162391 = 243587) B243587
theorem B326231 : Blo 143792 326231 := bstep (se 1 (by rfl) ⟨244673, by rfl⟩ : syracuseStep 326231 = 489347) B489347
theorem B621229 : Blo 143792 621229 := bstep (se 3 (by rfl) ⟨116480, by rfl⟩ : syracuseStep 621229 = 232961) B232961
theorem B162571 : Blo 143792 162571 := bstep (se 1 (by rfl) ⟨121928, by rfl⟩ : syracuseStep 162571 = 243857) B243857
theorem B326411 : Blo 143792 326411 := bstep (se 1 (by rfl) ⟨244808, by rfl⟩ : syracuseStep 326411 = 489617) B489617
theorem B326465 : Blo 143792 326465 := bstep (se 2 (by rfl) ⟨122424, by rfl⟩ : syracuseStep 326465 = 244849) B244849
theorem B162679 : Blo 143792 162679 := bstep (se 1 (by rfl) ⟨122009, by rfl⟩ : syracuseStep 162679 = 244019) B244019
theorem B326681 : Blo 143792 326681 := bstep (se 2 (by rfl) ⟨122505, by rfl⟩ : syracuseStep 326681 = 245011) B245011
theorem B162859 : Blo 143792 162859 := bstep (se 1 (by rfl) ⟨122144, by rfl⟩ : syracuseStep 162859 = 244289) B244289
theorem B490589 : Blo 143792 490589 := bstep (se 3 (by rfl) ⟨91985, by rfl⟩ : syracuseStep 490589 = 183971) B183971
theorem B326771 : Blo 143792 326771 := bstep (se 1 (by rfl) ⟨245078, by rfl⟩ : syracuseStep 326771 = 490157) B490157
theorem B162967 : Blo 143792 162967 := bstep (se 1 (by rfl) ⟨122225, by rfl⟩ : syracuseStep 162967 = 244451) B244451
theorem B326807 : Blo 143792 326807 := bstep (se 1 (by rfl) ⟨245105, by rfl⟩ : syracuseStep 326807 = 490211) B490211
theorem B621827 : Blo 143792 621827 := bstep (se 1 (by rfl) ⟨466370, by rfl⟩ : syracuseStep 621827 = 932741) B932741
theorem B523543 : Blo 143792 523543 := bstep (se 1 (by rfl) ⟨392657, by rfl⟩ : syracuseStep 523543 = 785315) B785315
theorem B163147 : Blo 143792 163147 := bstep (se 1 (by rfl) ⟨122360, by rfl⟩ : syracuseStep 163147 = 244721) B244721
theorem B326987 : Blo 143792 326987 := bstep (se 1 (by rfl) ⟨245240, by rfl⟩ : syracuseStep 326987 = 490481) B490481
theorem B327041 : Blo 143792 327041 := bstep (se 2 (by rfl) ⟨122640, by rfl⟩ : syracuseStep 327041 = 245281) B245281
theorem B163255 : Blo 143792 163255 := bstep (se 1 (by rfl) ⟨122441, by rfl⟩ : syracuseStep 163255 = 244883) B244883
theorem B327257 : Blo 143792 327257 := bstep (se 2 (by rfl) ⟨122721, by rfl⟩ : syracuseStep 327257 = 245443) B245443
theorem B163435 : Blo 143792 163435 := bstep (se 1 (by rfl) ⟨122576, by rfl⟩ : syracuseStep 163435 = 245153) B245153
theorem B327347 : Blo 143792 327347 := bstep (se 1 (by rfl) ⟨245510, by rfl⟩ : syracuseStep 327347 = 491021) B491021
theorem B163543 : Blo 143792 163543 := bstep (se 1 (by rfl) ⟨122657, by rfl⟩ : syracuseStep 163543 = 245315) B245315
theorem B327383 : Blo 143792 327383 := bstep (se 1 (by rfl) ⟨245537, by rfl⟩ : syracuseStep 327383 = 491075) B491075
theorem B556865 : Blo 143792 556865 := bstep (se 2 (by rfl) ⟨208824, by rfl⟩ : syracuseStep 556865 = 417649) B417649
theorem B163723 : Blo 143792 163723 := bstep (se 1 (by rfl) ⟨122792, by rfl⟩ : syracuseStep 163723 = 245585) B245585
theorem B327563 : Blo 143792 327563 := bstep (se 1 (by rfl) ⟨245672, by rfl⟩ : syracuseStep 327563 = 491345) B491345
theorem B524177 : Blo 143792 524177 := bstep (se 2 (by rfl) ⟨196566, by rfl⟩ : syracuseStep 524177 = 393133) B393133
theorem B327617 : Blo 143792 327617 := bstep (se 2 (by rfl) ⟨122856, by rfl⟩ : syracuseStep 327617 = 245713) B245713
theorem B1015769 : Blo 143792 1015769 := bstep (se 2 (by rfl) ⟨380913, by rfl⟩ : syracuseStep 1015769 = 761827) B761827
theorem B589853 : Blo 143792 589853 := bstep (se 3 (by rfl) ⟨110597, by rfl⟩ : syracuseStep 589853 = 221195) B221195
theorem B327815 : Blo 143792 327815 := bstep (se 1 (by rfl) ⟨245861, by rfl⟩ : syracuseStep 327815 = 491723) B491723
theorem B163975 : Blo 143792 163975 := bstep (se 1 (by rfl) ⟨122981, by rfl⟩ : syracuseStep 163975 = 245963) B245963
theorem B491777 : Blo 143792 491777 := bstep (se 2 (by rfl) ⟨184416, by rfl⟩ : syracuseStep 491777 = 368833) B368833
theorem B327995 : Blo 143792 327995 := bstep (se 1 (by rfl) ⟨245996, by rfl⟩ : syracuseStep 327995 = 491993) B491993
theorem B164155 : Blo 143792 164155 := bstep (se 1 (by rfl) ⟨123116, by rfl⟩ : syracuseStep 164155 = 246233) B246233
theorem B1638791 : Blo 143792 1638791 := bstep (se 1 (by rfl) ⟨1229093, by rfl⟩ : syracuseStep 1638791 = 2458187) B2458187
theorem B328121 : Blo 143792 328121 := bstep (se 2 (by rfl) ⟨123045, by rfl⟩ : syracuseStep 328121 = 246091) B246091
theorem B393815 : Blo 143792 393815 := bstep (se 1 (by rfl) ⟨295361, by rfl⟩ : syracuseStep 393815 = 590723) B590723
theorem B590593 : Blo 143792 590593 := bstep (se 2 (by rfl) ⟨221472, by rfl⟩ : syracuseStep 590593 = 442945) B442945
theorem B328463 : Blo 143792 328463 := bstep (se 1 (by rfl) ⟨246347, by rfl⟩ : syracuseStep 328463 = 492695) B492695
theorem B164623 : Blo 143792 164623 := bstep (se 1 (by rfl) ⟨123467, by rfl⟩ : syracuseStep 164623 = 246935) B246935
theorem B328481 : Blo 143792 328481 := bstep (se 2 (by rfl) ⟨123180, by rfl⟩ : syracuseStep 328481 = 246361) B246361
theorem B623627 : Blo 143792 623627 := bstep (se 1 (by rfl) ⟨467720, by rfl⟩ : syracuseStep 623627 = 935441) B935441
theorem B492587 : Blo 143792 492587 := bstep (se 1 (by rfl) ⟨369440, by rfl⟩ : syracuseStep 492587 = 738881) B738881
theorem B328823 : Blo 143792 328823 := bstep (se 1 (by rfl) ⟨246617, by rfl⟩ : syracuseStep 328823 = 493235) B493235
theorem B1672325 : Blo 143792 1672325 := bstep (se 4 (by rfl) ⟨156780, by rfl⟩ : syracuseStep 1672325 = 313561) B313561
theorem B165127 : Blo 143792 165127 := bstep (se 1 (by rfl) ⟨123845, by rfl⟩ : syracuseStep 165127 = 247691) B247691
theorem B197903 : Blo 143792 197903 := bstep (se 1 (by rfl) ⟨148427, by rfl⟩ : syracuseStep 197903 = 296855) B296855
theorem B329003 : Blo 143792 329003 := bstep (se 1 (by rfl) ⟨246752, by rfl⟩ : syracuseStep 329003 = 493505) B493505
theorem B558521 : Blo 143792 558521 := bstep (se 2 (by rfl) ⟨209445, by rfl⟩ : syracuseStep 558521 = 418891) B418891
theorem B165307 : Blo 143792 165307 := bstep (se 1 (by rfl) ⟨123980, by rfl⟩ : syracuseStep 165307 = 247961) B247961
theorem B1181213 : Blo 143792 1181213 := bstep (se 3 (by rfl) ⟨221477, by rfl⟩ : syracuseStep 1181213 = 442955) B442955
theorem B886301 : Blo 143792 886301 := bstep (se 3 (by rfl) ⟨166181, by rfl⟩ : syracuseStep 886301 = 332363) B332363
theorem B329363 : Blo 143792 329363 := bstep (se 1 (by rfl) ⟨247022, by rfl⟩ : syracuseStep 329363 = 494045) B494045
theorem B329417 : Blo 143792 329417 := bstep (se 2 (by rfl) ⟨123531, by rfl⟩ : syracuseStep 329417 = 247063) B247063
theorem B263969 : Blo 143792 263969 := bstep (se 2 (by rfl) ⟨98988, by rfl⟩ : syracuseStep 263969 = 197977) B197977
theorem B493427 : Blo 143792 493427 := bstep (se 1 (by rfl) ⟨370070, by rfl⟩ : syracuseStep 493427 = 740141) B740141
theorem B165775 : Blo 143792 165775 := bstep (se 1 (by rfl) ⟨124331, by rfl⟩ : syracuseStep 165775 = 248663) B248663
theorem B2131865 : Blo 143792 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B231353 : Blo 143792 231353 := bstep (se 2 (by rfl) ⟨86757, by rfl⟩ : syracuseStep 231353 = 173515) B173515
theorem B395209 : Blo 143792 395209 := bstep (se 2 (by rfl) ⟨148203, by rfl⟩ : syracuseStep 395209 = 296407) B296407
theorem B788773 : Blo 143792 788773 := bstep (se 4 (by rfl) ⟨73947, by rfl⟩ : syracuseStep 788773 = 147895) B147895
theorem B493883 : Blo 143792 493883 := bstep (se 1 (by rfl) ⟨370412, by rfl⟩ : syracuseStep 493883 = 740825) B740825
theorem B330119 : Blo 143792 330119 := bstep (se 1 (by rfl) ⟨247589, by rfl⟩ : syracuseStep 330119 = 495179) B495179
theorem B559507 : Blo 143792 559507 := bstep (se 1 (by rfl) ⟨419630, by rfl⟩ : syracuseStep 559507 = 839261) B839261
theorem B330299 : Blo 143792 330299 := bstep (se 1 (by rfl) ⟨247724, by rfl⟩ : syracuseStep 330299 = 495449) B495449
theorem B395891 : Blo 143792 395891 := bstep (se 1 (by rfl) ⟨296918, by rfl⟩ : syracuseStep 395891 = 593837) B593837
theorem B330425 : Blo 143792 330425 := bstep (se 2 (by rfl) ⟨123909, by rfl⟩ : syracuseStep 330425 = 247819) B247819
theorem B494369 : Blo 143792 494369 := bstep (se 2 (by rfl) ⟨185388, by rfl⟩ : syracuseStep 494369 = 370777) B370777
theorem B5639179 : Blo 143792 5639179 := bstep (se 1 (by rfl) ⟨4229384, by rfl⟩ : syracuseStep 5639179 = 8458769) B8458769
theorem B330767 : Blo 143792 330767 := bstep (se 1 (by rfl) ⟨248075, by rfl⟩ : syracuseStep 330767 = 496151) B496151
theorem B265231 : Blo 143792 265231 := bstep (se 1 (by rfl) ⟨198923, by rfl⟩ : syracuseStep 265231 = 397847) B397847
theorem B330785 : Blo 143792 330785 := bstep (se 2 (by rfl) ⟨124044, by rfl⟩ : syracuseStep 330785 = 248089) B248089
theorem B822473 : Blo 143792 822473 := bstep (se 2 (by rfl) ⟨308427, by rfl⟩ : syracuseStep 822473 = 616855) B616855
theorem B494963 : Blo 143792 494963 := bstep (se 1 (by rfl) ⟨371222, by rfl⟩ : syracuseStep 494963 = 742445) B742445
theorem B331127 : Blo 143792 331127 := bstep (se 1 (by rfl) ⟨248345, by rfl⟩ : syracuseStep 331127 = 496691) B496691
theorem B396679 : Blo 143792 396679 := bstep (se 1 (by rfl) ⟨297509, by rfl⟩ : syracuseStep 396679 = 595019) B595019
theorem B1314269 : Blo 143792 1314269 := bstep (se 3 (by rfl) ⟨246425, by rfl⟩ : syracuseStep 1314269 = 492851) B492851
theorem B757259 : Blo 143792 757259 := bstep (se 1 (by rfl) ⟨567944, by rfl⟩ : syracuseStep 757259 = 1135889) B1135889
theorem B331307 : Blo 143792 331307 := bstep (se 1 (by rfl) ⟨248480, by rfl⟩ : syracuseStep 331307 = 496961) B496961
theorem B233275 : Blo 143792 233275 := bstep (se 1 (by rfl) ⟨174956, by rfl⟩ : syracuseStep 233275 = 349913) B349913
theorem B331667 : Blo 143792 331667 := bstep (se 1 (by rfl) ⟨248750, by rfl⟩ : syracuseStep 331667 = 497501) B497501
theorem B331721 : Blo 143792 331721 := bstep (se 2 (by rfl) ⟨124395, by rfl⟩ : syracuseStep 331721 = 248791) B248791
theorem B200761 : Blo 143792 200761 := bstep (se 2 (by rfl) ⟨75285, by rfl⟩ : syracuseStep 200761 = 150571) B150571
theorem B233531 : Blo 143792 233531 := bstep (se 1 (by rfl) ⟨175148, by rfl⟩ : syracuseStep 233531 = 350297) B350297
theorem B168079 : Blo 143792 168079 := bstep (se 1 (by rfl) ⟨126059, by rfl⟩ : syracuseStep 168079 = 252119) B252119
theorem B365057 : Blo 143792 365057 := bstep (se 2 (by rfl) ⟨136896, by rfl⟩ : syracuseStep 365057 = 273793) B273793
theorem B332423 : Blo 143792 332423 := bstep (se 1 (by rfl) ⟨249317, by rfl⟩ : syracuseStep 332423 = 498635) B498635
theorem B398141 : Blo 143792 398141 := bstep (se 3 (by rfl) ⟨74651, by rfl⟩ : syracuseStep 398141 = 149303) B149303
theorem B365431 : Blo 143792 365431 := bstep (se 1 (by rfl) ⟨274073, by rfl⟩ : syracuseStep 365431 = 548147) B548147
theorem B594955 : Blo 143792 594955 := bstep (se 1 (by rfl) ⟨446216, by rfl⟩ : syracuseStep 594955 = 892433) B892433
theorem B824363 : Blo 143792 824363 := bstep (se 1 (by rfl) ⟨618272, by rfl⟩ : syracuseStep 824363 = 1236545) B1236545
theorem B300217 : Blo 143792 300217 := bstep (se 2 (by rfl) ⟨112581, by rfl⟩ : syracuseStep 300217 = 225163) B225163
theorem B595181 : Blo 143792 595181 := bstep (se 3 (by rfl) ⟨111596, by rfl⟩ : syracuseStep 595181 = 223193) B223193
theorem B365867 : Blo 143792 365867 := bstep (se 1 (by rfl) ⟨274400, by rfl⟩ : syracuseStep 365867 = 548801) B548801
theorem B267667 : Blo 143792 267667 := bstep (se 1 (by rfl) ⟨200750, by rfl⟩ : syracuseStep 267667 = 401501) B401501
theorem B497441 : Blo 143792 497441 := bstep (se 2 (by rfl) ⟨186540, by rfl⟩ : syracuseStep 497441 = 373081) B373081
theorem B1054579 : Blo 143792 1054579 := bstep (se 1 (by rfl) ⟨790934, by rfl⟩ : syracuseStep 1054579 = 1581869) B1581869
theorem B497555 : Blo 143792 497555 := bstep (se 1 (by rfl) ⟨373166, by rfl⟩ : syracuseStep 497555 = 746333) B746333
theorem B890777 : Blo 143792 890777 := bstep (se 2 (by rfl) ⟨334041, by rfl⟩ : syracuseStep 890777 = 668083) B668083
theorem B366707 : Blo 143792 366707 := bstep (se 1 (by rfl) ⟨275030, by rfl⟩ : syracuseStep 366707 = 550061) B550061
theorem B366727 : Blo 143792 366727 := bstep (se 1 (by rfl) ⟨275045, by rfl⟩ : syracuseStep 366727 = 550091) B550091
theorem B301241 : Blo 143792 301241 := bstep (se 2 (by rfl) ⟨112965, by rfl⟩ : syracuseStep 301241 = 225931) B225931
theorem B1579409 : Blo 143792 1579409 := bstep (se 2 (by rfl) ⟨592278, by rfl⟩ : syracuseStep 1579409 = 1184557) B1184557
theorem B367001 : Blo 143792 367001 := bstep (se 2 (by rfl) ⟨137625, by rfl⟩ : syracuseStep 367001 = 275251) B275251
theorem B825821 : Blo 143792 825821 := bstep (se 3 (by rfl) ⟨154841, by rfl⟩ : syracuseStep 825821 = 309683) B309683
theorem B367163 : Blo 143792 367163 := bstep (se 1 (by rfl) ⟨275372, by rfl⟩ : syracuseStep 367163 = 550745) B550745
theorem B629309 : Blo 143792 629309 := bstep (se 3 (by rfl) ⟨117995, by rfl⟩ : syracuseStep 629309 = 235991) B235991
theorem B367375 : Blo 143792 367375 := bstep (se 1 (by rfl) ⟨275531, by rfl⟩ : syracuseStep 367375 = 551063) B551063
theorem B1514315 : Blo 143792 1514315 := bstep (se 1 (by rfl) ⟨1135736, by rfl⟩ : syracuseStep 1514315 = 2271473) B2271473
theorem B826321 : Blo 143792 826321 := bstep (se 2 (by rfl) ⟨309870, by rfl⟩ : syracuseStep 826321 = 619741) B619741
theorem B367649 : Blo 143792 367649 := bstep (se 2 (by rfl) ⟨137868, by rfl⟩ : syracuseStep 367649 = 275737) B275737
theorem B1056185 : Blo 143792 1056185 := bstep (se 2 (by rfl) ⟨396069, by rfl⟩ : syracuseStep 1056185 = 792139) B792139
theorem B630301 : Blo 143792 630301 := bstep (se 3 (by rfl) ⟨118181, by rfl⟩ : syracuseStep 630301 = 236363) B236363
theorem B368651 : Blo 143792 368651 := bstep (se 1 (by rfl) ⟨276488, by rfl⟩ : syracuseStep 368651 = 552977) B552977
theorem B204815 : Blo 143792 204815 := bstep (se 1 (by rfl) ⟨153611, by rfl⟩ : syracuseStep 204815 = 307223) B307223
theorem B6037685 : Blo 143792 6037685 := bstep (se 5 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 6037685 = 566033) B566033
theorem B8954057 : Blo 143792 8954057 := bstep (se 2 (by rfl) ⟨3357771, by rfl⟩ : syracuseStep 8954057 = 6715543) B6715543
theorem B172279 : Blo 143792 172279 := bstep (se 1 (by rfl) ⟨129209, by rfl⟩ : syracuseStep 172279 = 258419) B258419
theorem B1122707 : Blo 143792 1122707 := bstep (se 1 (by rfl) ⟨842030, by rfl⟩ : syracuseStep 1122707 = 1684061) B1684061
theorem B369299 : Blo 143792 369299 := bstep (se 1 (by rfl) ⟨276974, by rfl⟩ : syracuseStep 369299 = 553949) B553949
theorem B729971 : Blo 143792 729971 := bstep (se 1 (by rfl) ⟨547478, by rfl⟩ : syracuseStep 729971 = 1094957) B1094957
theorem B828305 : Blo 143792 828305 := bstep (se 2 (by rfl) ⟨310614, by rfl⟩ : syracuseStep 828305 = 621229) B621229
theorem B369593 : Blo 143792 369593 := bstep (se 2 (by rfl) ⟨138597, by rfl⟩ : syracuseStep 369593 = 277195) B277195
theorem B468011 : Blo 143792 468011 := bstep (se 1 (by rfl) ⟨351008, by rfl⟩ : syracuseStep 468011 = 702017) B702017
theorem B205897 : Blo 143792 205897 := bstep (se 2 (by rfl) ⟨77211, by rfl⟩ : syracuseStep 205897 = 154423) B154423
theorem B206011 : Blo 143792 206011 := bstep (se 1 (by rfl) ⟨154508, by rfl⟩ : syracuseStep 206011 = 309017) B309017
theorem B730457 : Blo 143792 730457 := bstep (se 2 (by rfl) ⟨273921, by rfl⟩ : syracuseStep 730457 = 547843) B547843
theorem B1254791 : Blo 143792 1254791 := bstep (se 1 (by rfl) ⟨941093, by rfl⟩ : syracuseStep 1254791 = 1882187) B1882187
theorem B1418795 : Blo 143792 1418795 := bstep (se 1 (by rfl) ⟨1064096, by rfl⟩ : syracuseStep 1418795 = 2128193) B2128193
theorem B370291 : Blo 143792 370291 := bstep (se 1 (by rfl) ⟨277718, by rfl⟩ : syracuseStep 370291 = 555437) B555437
theorem B1681073 : Blo 143792 1681073 := bstep (se 2 (by rfl) ⟨630402, by rfl⟩ : syracuseStep 1681073 = 1260805) B1260805
theorem B698057 : Blo 143792 698057 := bstep (se 2 (by rfl) ⟨261771, by rfl⟩ : syracuseStep 698057 = 523543) B523543
theorem B403145 : Blo 143792 403145 := bstep (se 2 (by rfl) ⟨151179, by rfl⟩ : syracuseStep 403145 = 302359) B302359
theorem B370433 : Blo 143792 370433 := bstep (se 2 (by rfl) ⟨138912, by rfl⟩ : syracuseStep 370433 = 277825) B277825
theorem B927767 : Blo 143792 927767 := bstep (se 1 (by rfl) ⟨695825, by rfl⟩ : syracuseStep 927767 = 1391651) B1391651
theorem B370889 : Blo 143792 370889 := bstep (se 2 (by rfl) ⟨139083, by rfl⟩ : syracuseStep 370889 = 278167) B278167
theorem B1387037 : Blo 143792 1387037 := bstep (se 3 (by rfl) ⟨260069, by rfl⟩ : syracuseStep 1387037 = 520139) B520139
theorem B371243 : Blo 143792 371243 := bstep (se 1 (by rfl) ⟨278432, by rfl⟩ : syracuseStep 371243 = 556865) B556865
theorem B207623 : Blo 143792 207623 := bstep (se 1 (by rfl) ⟨155717, by rfl⟩ : syracuseStep 207623 = 311435) B311435
theorem B273451 : Blo 143792 273451 := bstep (se 1 (by rfl) ⟨205088, by rfl⟩ : syracuseStep 273451 = 410177) B410177
theorem B273527 : Blo 143792 273527 := bstep (se 1 (by rfl) ⟨205145, by rfl⟩ : syracuseStep 273527 = 410291) B410291
theorem B207991 : Blo 143792 207991 := bstep (se 1 (by rfl) ⟨155993, by rfl⟩ : syracuseStep 207991 = 311987) B311987
theorem B798011 : Blo 143792 798011 := bstep (se 1 (by rfl) ⟨598508, by rfl⟩ : syracuseStep 798011 = 1197017) B1197017
theorem B732563 : Blo 143792 732563 := bstep (se 1 (by rfl) ⟨549422, by rfl⟩ : syracuseStep 732563 = 1098845) B1098845
theorem B1387961 : Blo 143792 1387961 := bstep (se 2 (by rfl) ⟨520485, by rfl⟩ : syracuseStep 1387961 = 1040971) B1040971
theorem B372235 : Blo 143792 372235 := bstep (se 1 (by rfl) ⟨279176, by rfl⟩ : syracuseStep 372235 = 558353) B558353
theorem B372377 : Blo 143792 372377 := bstep (se 2 (by rfl) ⟨139641, by rfl⟩ : syracuseStep 372377 = 279283) B279283
theorem B208585 : Blo 143792 208585 := bstep (se 2 (by rfl) ⟨78219, by rfl⟩ : syracuseStep 208585 = 156439) B156439
theorem B765677 : Blo 143792 765677 := bstep (se 3 (by rfl) ⟨143564, by rfl⟩ : syracuseStep 765677 = 287129) B287129
theorem B175879 : Blo 143792 175879 := bstep (se 1 (by rfl) ⟨131909, by rfl⟩ : syracuseStep 175879 = 263819) B263819
theorem B470843 : Blo 143792 470843 := bstep (se 1 (by rfl) ⟨353132, by rfl⟩ : syracuseStep 470843 = 706265) B706265
theorem B372539 : Blo 143792 372539 := bstep (se 1 (by rfl) ⟨279404, by rfl⟩ : syracuseStep 372539 = 558809) B558809
theorem B372883 : Blo 143792 372883 := bstep (se 1 (by rfl) ⟨279662, by rfl⟩ : syracuseStep 372883 = 559325) B559325
theorem B798893 : Blo 143792 798893 := bstep (se 3 (by rfl) ⟨149792, by rfl⟩ : syracuseStep 798893 = 299585) B299585
theorem B209081 : Blo 143792 209081 := bstep (se 2 (by rfl) ⟨78405, by rfl⟩ : syracuseStep 209081 = 156811) B156811
theorem B307471 : Blo 143792 307471 := bstep (se 1 (by rfl) ⟨230603, by rfl⟩ : syracuseStep 307471 = 461207) B461207
theorem B373025 : Blo 143792 373025 := bstep (se 2 (by rfl) ⟨139884, by rfl⟩ : syracuseStep 373025 = 279769) B279769
theorem B143803 : Blo 143792 143803 := bstep (se 1 (by rfl) ⟨107852, by rfl⟩ : syracuseStep 143803 = 215705) B215705
theorem B143879 : Blo 143792 143879 := bstep (se 1 (by rfl) ⟨107909, by rfl⟩ : syracuseStep 143879 = 215819) B215819
theorem B143887 : Blo 143792 143887 := bstep (se 1 (by rfl) ⟨107915, by rfl⟩ : syracuseStep 143887 = 215831) B215831
theorem B143931 : Blo 143792 143931 := bstep (se 1 (by rfl) ⟨107948, by rfl⟩ : syracuseStep 143931 = 215897) B215897
theorem B144007 : Blo 143792 144007 := bstep (se 1 (by rfl) ⟨108005, by rfl⟩ : syracuseStep 144007 = 216011) B216011
theorem B144015 : Blo 143792 144015 := bstep (se 1 (by rfl) ⟨108011, by rfl⟩ : syracuseStep 144015 = 216023) B216023
theorem B144059 : Blo 143792 144059 := bstep (se 1 (by rfl) ⟨108044, by rfl⟩ : syracuseStep 144059 = 216089) B216089
theorem B2503385 : Blo 143792 2503385 := bstep (se 2 (by rfl) ⟨938769, by rfl⟩ : syracuseStep 2503385 = 1877539) B1877539
theorem B1127141 : Blo 143792 1127141 := bstep (se 4 (by rfl) ⟨105669, by rfl⟩ : syracuseStep 1127141 = 211339) B211339
theorem B144135 : Blo 143792 144135 := bstep (se 1 (by rfl) ⟨108101, by rfl⟩ : syracuseStep 144135 = 216203) B216203
theorem B144143 : Blo 143792 144143 := bstep (se 1 (by rfl) ⟨108107, by rfl⟩ : syracuseStep 144143 = 216215) B216215
theorem B144187 : Blo 143792 144187 := bstep (se 1 (by rfl) ⟨108140, by rfl⟩ : syracuseStep 144187 = 216281) B216281
theorem B144263 : Blo 143792 144263 := bstep (se 1 (by rfl) ⟨108197, by rfl⟩ : syracuseStep 144263 = 216395) B216395
theorem B144271 : Blo 143792 144271 := bstep (se 1 (by rfl) ⟨108203, by rfl⟩ : syracuseStep 144271 = 216407) B216407
theorem B144315 : Blo 143792 144315 := bstep (se 1 (by rfl) ⟨108236, by rfl⟩ : syracuseStep 144315 = 216473) B216473
theorem B144391 : Blo 143792 144391 := bstep (se 1 (by rfl) ⟨108293, by rfl⟩ : syracuseStep 144391 = 216587) B216587
theorem B144399 : Blo 143792 144399 := bstep (se 1 (by rfl) ⟨108299, by rfl⟩ : syracuseStep 144399 = 216599) B216599
theorem B275471 : Blo 143792 275471 := bstep (se 1 (by rfl) ⟨206603, by rfl⟩ : syracuseStep 275471 = 413207) B413207
theorem B144443 : Blo 143792 144443 := bstep (se 1 (by rfl) ⟨108332, by rfl⟩ : syracuseStep 144443 = 216665) B216665
theorem B144519 : Blo 143792 144519 := bstep (se 1 (by rfl) ⟨108389, by rfl⟩ : syracuseStep 144519 = 216779) B216779
theorem B210055 : Blo 143792 210055 := bstep (se 1 (by rfl) ⟨157541, by rfl⟩ : syracuseStep 210055 = 315083) B315083
theorem B144527 : Blo 143792 144527 := bstep (se 1 (by rfl) ⟨108395, by rfl⟩ : syracuseStep 144527 = 216791) B216791
theorem B144571 : Blo 143792 144571 := bstep (se 1 (by rfl) ⟨108428, by rfl⟩ : syracuseStep 144571 = 216857) B216857
theorem B1651913 : Blo 143792 1651913 := bstep (se 2 (by rfl) ⟨619467, by rfl⟩ : syracuseStep 1651913 = 1238935) B1238935
theorem B374017 : Blo 143792 374017 := bstep (se 2 (by rfl) ⟨140256, by rfl⟩ : syracuseStep 374017 = 280513) B280513
theorem B144647 : Blo 143792 144647 := bstep (se 1 (by rfl) ⟨108485, by rfl⟩ : syracuseStep 144647 = 216971) B216971
theorem B242959 : Blo 143792 242959 := bstep (se 1 (by rfl) ⟨182219, by rfl⟩ : syracuseStep 242959 = 364439) B364439
theorem B144655 : Blo 143792 144655 := bstep (se 1 (by rfl) ⟨108491, by rfl⟩ : syracuseStep 144655 = 216983) B216983
theorem B701747 : Blo 143792 701747 := bstep (se 1 (by rfl) ⟨526310, by rfl⟩ : syracuseStep 701747 = 1052621) B1052621
theorem B144699 : Blo 143792 144699 := bstep (se 1 (by rfl) ⟨108524, by rfl⟩ : syracuseStep 144699 = 217049) B217049
theorem B144775 : Blo 143792 144775 := bstep (se 1 (by rfl) ⟨108581, by rfl⟩ : syracuseStep 144775 = 217163) B217163
theorem B144783 : Blo 143792 144783 := bstep (se 1 (by rfl) ⟨108587, by rfl⟩ : syracuseStep 144783 = 217175) B217175
theorem B144827 : Blo 143792 144827 := bstep (se 1 (by rfl) ⟨108620, by rfl⟩ : syracuseStep 144827 = 217241) B217241
theorem B3225091 : Blo 143792 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B144903 : Blo 143792 144903 := bstep (se 1 (by rfl) ⟨108677, by rfl⟩ : syracuseStep 144903 = 217355) B217355
theorem B144911 : Blo 143792 144911 := bstep (se 1 (by rfl) ⟨108683, by rfl⟩ : syracuseStep 144911 = 217367) B217367
theorem B144955 : Blo 143792 144955 := bstep (se 1 (by rfl) ⟨108716, by rfl⟩ : syracuseStep 144955 = 217433) B217433
theorem B833111 : Blo 143792 833111 := bstep (se 1 (by rfl) ⟨624833, by rfl⟩ : syracuseStep 833111 = 1249667) B1249667
theorem B145031 : Blo 143792 145031 := bstep (se 1 (by rfl) ⟨108773, by rfl⟩ : syracuseStep 145031 = 217547) B217547
theorem B145039 : Blo 143792 145039 := bstep (se 1 (by rfl) ⟨108779, by rfl⟩ : syracuseStep 145039 = 217559) B217559
theorem B145083 : Blo 143792 145083 := bstep (se 1 (by rfl) ⟨108812, by rfl⟩ : syracuseStep 145083 = 217625) B217625
theorem B2111233 : Blo 143792 2111233 := bstep (se 2 (by rfl) ⟨791712, by rfl⟩ : syracuseStep 2111233 = 1583425) B1583425
theorem B702209 : Blo 143792 702209 := bstep (se 2 (by rfl) ⟨263328, by rfl⟩ : syracuseStep 702209 = 526657) B526657
theorem B145159 : Blo 143792 145159 := bstep (se 1 (by rfl) ⟨108869, by rfl⟩ : syracuseStep 145159 = 217739) B217739
theorem B145167 : Blo 143792 145167 := bstep (se 1 (by rfl) ⟨108875, by rfl⟩ : syracuseStep 145167 = 217751) B217751
theorem B243499 : Blo 143792 243499 := bstep (se 1 (by rfl) ⟨182624, by rfl⟩ : syracuseStep 243499 = 365249) B365249
theorem B1390385 : Blo 143792 1390385 := bstep (se 2 (by rfl) ⟨521394, by rfl⟩ : syracuseStep 1390385 = 1042789) B1042789
theorem B145211 : Blo 143792 145211 := bstep (se 1 (by rfl) ⟨108908, by rfl⟩ : syracuseStep 145211 = 217817) B217817
theorem B145287 : Blo 143792 145287 := bstep (se 1 (by rfl) ⟨108965, by rfl⟩ : syracuseStep 145287 = 217931) B217931
theorem B145295 : Blo 143792 145295 := bstep (se 1 (by rfl) ⟨108971, by rfl⟩ : syracuseStep 145295 = 217943) B217943
theorem B702361 : Blo 143792 702361 := bstep (se 2 (by rfl) ⟨263385, by rfl⟩ : syracuseStep 702361 = 526771) B526771
theorem B243641 : Blo 143792 243641 := bstep (se 2 (by rfl) ⟨91365, by rfl⟩ : syracuseStep 243641 = 182731) B182731
theorem B145339 : Blo 143792 145339 := bstep (se 1 (by rfl) ⟨109004, by rfl⟩ : syracuseStep 145339 = 218009) B218009
theorem B145415 : Blo 143792 145415 := bstep (se 1 (by rfl) ⟨109061, by rfl⟩ : syracuseStep 145415 = 218123) B218123
theorem B145423 : Blo 143792 145423 := bstep (se 1 (by rfl) ⟨109067, by rfl⟩ : syracuseStep 145423 = 218135) B218135
theorem B145467 : Blo 143792 145467 := bstep (se 1 (by rfl) ⟨109100, by rfl⟩ : syracuseStep 145467 = 218201) B218201
theorem B145543 : Blo 143792 145543 := bstep (se 1 (by rfl) ⟨109157, by rfl⟩ : syracuseStep 145543 = 218315) B218315
theorem B145551 : Blo 143792 145551 := bstep (se 1 (by rfl) ⟨109163, by rfl⟩ : syracuseStep 145551 = 218327) B218327
theorem B145595 : Blo 143792 145595 := bstep (se 1 (by rfl) ⟨109196, by rfl⟩ : syracuseStep 145595 = 218393) B218393
theorem B145671 : Blo 143792 145671 := bstep (se 1 (by rfl) ⟨109253, by rfl⟩ : syracuseStep 145671 = 218507) B218507
theorem B145679 : Blo 143792 145679 := bstep (se 1 (by rfl) ⟨109259, by rfl⟩ : syracuseStep 145679 = 218519) B218519
theorem B473359 : Blo 143792 473359 := bstep (se 1 (by rfl) ⟨355019, by rfl⟩ : syracuseStep 473359 = 710039) B710039
theorem B145723 : Blo 143792 145723 := bstep (se 1 (by rfl) ⟨109292, by rfl⟩ : syracuseStep 145723 = 218585) B218585
theorem B145799 : Blo 143792 145799 := bstep (se 1 (by rfl) ⟨109349, by rfl⟩ : syracuseStep 145799 = 218699) B218699
theorem B145807 : Blo 143792 145807 := bstep (se 1 (by rfl) ⟨109355, by rfl⟩ : syracuseStep 145807 = 218711) B218711
theorem B735641 : Blo 143792 735641 := bstep (se 2 (by rfl) ⟨275865, by rfl⟩ : syracuseStep 735641 = 551731) B551731
theorem B145851 : Blo 143792 145851 := bstep (se 1 (by rfl) ⟨109388, by rfl⟩ : syracuseStep 145851 = 218777) B218777
theorem B145927 : Blo 143792 145927 := bstep (se 1 (by rfl) ⟨109445, by rfl⟩ : syracuseStep 145927 = 218891) B218891
theorem B145935 : Blo 143792 145935 := bstep (se 1 (by rfl) ⟨109451, by rfl⟩ : syracuseStep 145935 = 218903) B218903
theorem B932381 : Blo 143792 932381 := bstep (se 3 (by rfl) ⟨174821, by rfl⟩ : syracuseStep 932381 = 349643) B349643
theorem B145979 : Blo 143792 145979 := bstep (se 1 (by rfl) ⟨109484, by rfl⟩ : syracuseStep 145979 = 218969) B218969
theorem B244343 : Blo 143792 244343 := bstep (se 1 (by rfl) ⟨183257, by rfl⟩ : syracuseStep 244343 = 366515) B366515
theorem B277111 : Blo 143792 277111 := bstep (se 1 (by rfl) ⟨207833, by rfl⟩ : syracuseStep 277111 = 415667) B415667
theorem B146055 : Blo 143792 146055 := bstep (se 1 (by rfl) ⟨109541, by rfl⟩ : syracuseStep 146055 = 219083) B219083
theorem B146063 : Blo 143792 146063 := bstep (se 1 (by rfl) ⟨109547, by rfl⟩ : syracuseStep 146063 = 219095) B219095
theorem B146107 : Blo 143792 146107 := bstep (se 1 (by rfl) ⟨109580, by rfl⟩ : syracuseStep 146107 = 219161) B219161
theorem B146183 : Blo 143792 146183 := bstep (se 1 (by rfl) ⟨109637, by rfl⟩ : syracuseStep 146183 = 219275) B219275
theorem B146191 : Blo 143792 146191 := bstep (se 1 (by rfl) ⟨109643, by rfl⟩ : syracuseStep 146191 = 219287) B219287
theorem B146235 : Blo 143792 146235 := bstep (se 1 (by rfl) ⟨109676, by rfl⟩ : syracuseStep 146235 = 219353) B219353
theorem B146311 : Blo 143792 146311 := bstep (se 1 (by rfl) ⟨109733, by rfl⟩ : syracuseStep 146311 = 219467) B219467
theorem B146319 : Blo 143792 146319 := bstep (se 1 (by rfl) ⟨109739, by rfl⟩ : syracuseStep 146319 = 219479) B219479
theorem B146363 : Blo 143792 146363 := bstep (se 1 (by rfl) ⟨109772, by rfl⟩ : syracuseStep 146363 = 219545) B219545
theorem B146439 : Blo 143792 146439 := bstep (se 1 (by rfl) ⟨109829, by rfl⟩ : syracuseStep 146439 = 219659) B219659
theorem B146447 : Blo 143792 146447 := bstep (se 1 (by rfl) ⟨109835, by rfl⟩ : syracuseStep 146447 = 219671) B219671
theorem B244795 : Blo 143792 244795 := bstep (se 1 (by rfl) ⟨183596, by rfl⟩ : syracuseStep 244795 = 367193) B367193
theorem B146491 : Blo 143792 146491 := bstep (se 1 (by rfl) ⟨109868, by rfl⟩ : syracuseStep 146491 = 219737) B219737
theorem B146567 : Blo 143792 146567 := bstep (se 1 (by rfl) ⟨109925, by rfl⟩ : syracuseStep 146567 = 219851) B219851
theorem B146575 : Blo 143792 146575 := bstep (se 1 (by rfl) ⟨109931, by rfl⟩ : syracuseStep 146575 = 219863) B219863
theorem B146619 : Blo 143792 146619 := bstep (se 1 (by rfl) ⟨109964, by rfl⟩ : syracuseStep 146619 = 219929) B219929
theorem B244937 : Blo 143792 244937 := bstep (se 2 (by rfl) ⟨91851, by rfl⟩ : syracuseStep 244937 = 183703) B183703
theorem B146695 : Blo 143792 146695 := bstep (se 1 (by rfl) ⟨110021, by rfl⟩ : syracuseStep 146695 = 220043) B220043
theorem B146703 : Blo 143792 146703 := bstep (se 1 (by rfl) ⟨110027, by rfl⟩ : syracuseStep 146703 = 220055) B220055
theorem B834875 : Blo 143792 834875 := bstep (se 1 (by rfl) ⟨626156, by rfl⟩ : syracuseStep 834875 = 1252313) B1252313
theorem B146747 : Blo 143792 146747 := bstep (se 1 (by rfl) ⟨110060, by rfl⟩ : syracuseStep 146747 = 220121) B220121
theorem B441715 : Blo 143792 441715 := bstep (se 1 (by rfl) ⟨331286, by rfl⟩ : syracuseStep 441715 = 662573) B662573
theorem B146823 : Blo 143792 146823 := bstep (se 1 (by rfl) ⟨110117, by rfl⟩ : syracuseStep 146823 = 220235) B220235
theorem B146831 : Blo 143792 146831 := bstep (se 1 (by rfl) ⟨110123, by rfl⟩ : syracuseStep 146831 = 220247) B220247
theorem B146875 : Blo 143792 146875 := bstep (se 1 (by rfl) ⟨110156, by rfl⟩ : syracuseStep 146875 = 220313) B220313
theorem B1818065 : Blo 143792 1818065 := bstep (se 2 (by rfl) ⟨681774, by rfl⟩ : syracuseStep 1818065 = 1363549) B1363549
theorem B146951 : Blo 143792 146951 := bstep (se 1 (by rfl) ⟨110213, by rfl⟩ : syracuseStep 146951 = 220427) B220427
theorem B146959 : Blo 143792 146959 := bstep (se 1 (by rfl) ⟨110219, by rfl⟩ : syracuseStep 146959 = 220439) B220439
theorem B147003 : Blo 143792 147003 := bstep (se 1 (by rfl) ⟨110252, by rfl⟩ : syracuseStep 147003 = 220505) B220505
theorem B147079 : Blo 143792 147079 := bstep (se 1 (by rfl) ⟨110309, by rfl⟩ : syracuseStep 147079 = 220619) B220619
theorem B147087 : Blo 143792 147087 := bstep (se 1 (by rfl) ⟨110315, by rfl⟩ : syracuseStep 147087 = 220631) B220631
theorem B147131 : Blo 143792 147131 := bstep (se 1 (by rfl) ⟨110348, by rfl⟩ : syracuseStep 147131 = 220697) B220697
theorem B147207 : Blo 143792 147207 := bstep (se 1 (by rfl) ⟨110405, by rfl⟩ : syracuseStep 147207 = 220811) B220811
theorem B835343 : Blo 143792 835343 := bstep (se 1 (by rfl) ⟨626507, by rfl⟩ : syracuseStep 835343 = 1253015) B1253015
theorem B147215 : Blo 143792 147215 := bstep (se 1 (by rfl) ⟨110411, by rfl⟩ : syracuseStep 147215 = 220823) B220823
theorem B1392419 : Blo 143792 1392419 := bstep (se 1 (by rfl) ⟨1044314, by rfl⟩ : syracuseStep 1392419 = 2088629) B2088629
theorem B5062445 : Blo 143792 5062445 := bstep (se 3 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 5062445 = 1898417) B1898417
theorem B147259 : Blo 143792 147259 := bstep (se 1 (by rfl) ⟨110444, by rfl⟩ : syracuseStep 147259 = 220889) B220889
theorem B245639 : Blo 143792 245639 := bstep (se 1 (by rfl) ⟨184229, by rfl⟩ : syracuseStep 245639 = 368459) B368459
theorem B147335 : Blo 143792 147335 := bstep (se 1 (by rfl) ⟨110501, by rfl⟩ : syracuseStep 147335 = 221003) B221003
theorem B147343 : Blo 143792 147343 := bstep (se 1 (by rfl) ⟨110507, by rfl⟩ : syracuseStep 147343 = 221015) B221015
theorem B147387 : Blo 143792 147387 := bstep (se 1 (by rfl) ⟨110540, by rfl⟩ : syracuseStep 147387 = 221081) B221081
theorem B704477 : Blo 143792 704477 := bstep (se 3 (by rfl) ⟨132089, by rfl⟩ : syracuseStep 704477 = 264179) B264179
theorem B147463 : Blo 143792 147463 := bstep (se 1 (by rfl) ⟨110597, by rfl⟩ : syracuseStep 147463 = 221195) B221195
theorem B835595 : Blo 143792 835595 := bstep (se 1 (by rfl) ⟨626696, by rfl⟩ : syracuseStep 835595 = 1253393) B1253393
theorem B147471 : Blo 143792 147471 := bstep (se 1 (by rfl) ⟨110603, by rfl⟩ : syracuseStep 147471 = 221207) B221207
theorem B1654829 : Blo 143792 1654829 := bstep (se 3 (by rfl) ⟨310280, by rfl⟩ : syracuseStep 1654829 = 620561) B620561
theorem B147515 : Blo 143792 147515 := bstep (se 1 (by rfl) ⟨110636, by rfl⟩ : syracuseStep 147515 = 221273) B221273
theorem B147591 : Blo 143792 147591 := bstep (se 1 (by rfl) ⟨110693, by rfl⟩ : syracuseStep 147591 = 221387) B221387
theorem B147599 : Blo 143792 147599 := bstep (se 1 (by rfl) ⟨110699, by rfl⟩ : syracuseStep 147599 = 221399) B221399
theorem B147643 : Blo 143792 147643 := bstep (se 1 (by rfl) ⟨110732, by rfl⟩ : syracuseStep 147643 = 221465) B221465
theorem B147719 : Blo 143792 147719 := bstep (se 1 (by rfl) ⟨110789, by rfl⟩ : syracuseStep 147719 = 221579) B221579
theorem B147727 : Blo 143792 147727 := bstep (se 1 (by rfl) ⟨110795, by rfl⟩ : syracuseStep 147727 = 221591) B221591
theorem B147771 : Blo 143792 147771 := bstep (se 1 (by rfl) ⟨110828, by rfl⟩ : syracuseStep 147771 = 221657) B221657
theorem B278903 : Blo 143792 278903 := bstep (se 1 (by rfl) ⟨209177, by rfl⟩ : syracuseStep 278903 = 418355) B418355
theorem B1556957 : Blo 143792 1556957 := bstep (se 3 (by rfl) ⟨291929, by rfl⟩ : syracuseStep 1556957 = 583859) B583859
theorem B246287 : Blo 143792 246287 := bstep (se 1 (by rfl) ⟨184715, by rfl⟩ : syracuseStep 246287 = 369431) B369431
theorem B279055 : Blo 143792 279055 := bstep (se 1 (by rfl) ⟨209291, by rfl⟩ : syracuseStep 279055 = 418583) B418583
theorem B836119 : Blo 143792 836119 := bstep (se 1 (by rfl) ⟨627089, by rfl⟩ : syracuseStep 836119 = 1254179) B1254179
theorem B1098359 : Blo 143792 1098359 := bstep (se 1 (by rfl) ⟨823769, by rfl⟩ : syracuseStep 1098359 = 1647539) B1647539
theorem B3982117 : Blo 143792 3982117 := bstep (se 4 (by rfl) ⟨373323, by rfl⟩ : syracuseStep 3982117 = 746647) B746647
theorem B279443 : Blo 143792 279443 := bstep (se 1 (by rfl) ⟨209582, by rfl⟩ : syracuseStep 279443 = 419165) B419165
theorem B1000345 : Blo 143792 1000345 := bstep (se 2 (by rfl) ⟨375129, by rfl⟩ : syracuseStep 1000345 = 750259) B750259
theorem B5686193 : Blo 143792 5686193 := bstep (se 2 (by rfl) ⟨2132322, by rfl⟩ : syracuseStep 5686193 = 4264645) B4264645
theorem B738233 : Blo 143792 738233 := bstep (se 2 (by rfl) ⟨276837, by rfl⟩ : syracuseStep 738233 = 553675) B553675
theorem B246827 : Blo 143792 246827 := bstep (se 1 (by rfl) ⟨185120, by rfl⟩ : syracuseStep 246827 = 370241) B370241
theorem B2114693 : Blo 143792 2114693 := bstep (se 4 (by rfl) ⟨198252, by rfl⟩ : syracuseStep 2114693 = 396505) B396505
theorem B836801 : Blo 143792 836801 := bstep (se 2 (by rfl) ⟨313800, by rfl⟩ : syracuseStep 836801 = 627601) B627601
theorem B345529 : Blo 143792 345529 := bstep (se 2 (by rfl) ⟨129573, by rfl⟩ : syracuseStep 345529 = 259147) B259147
theorem B411065 : Blo 143792 411065 := bstep (se 2 (by rfl) ⟨154149, by rfl⟩ : syracuseStep 411065 = 308299) B308299
theorem B247225 : Blo 143792 247225 := bstep (se 2 (by rfl) ⟨92709, by rfl⟩ : syracuseStep 247225 = 185419) B185419
theorem B1099331 : Blo 143792 1099331 := bstep (se 1 (by rfl) ⟨824498, by rfl⟩ : syracuseStep 1099331 = 1648997) B1648997
theorem B444503 : Blo 143792 444503 := bstep (se 1 (by rfl) ⟨333377, by rfl⟩ : syracuseStep 444503 = 666755) B666755
theorem B247927 : Blo 143792 247927 := bstep (se 1 (by rfl) ⟨185945, by rfl⟩ : syracuseStep 247927 = 371891) B371891
theorem B182407 : Blo 143792 182407 := bstep (se 1 (by rfl) ⟨136805, by rfl⟩ : syracuseStep 182407 = 273611) B273611
theorem B739529 : Blo 143792 739529 := bstep (se 2 (by rfl) ⟨277323, by rfl⟩ : syracuseStep 739529 = 554647) B554647
theorem B936173 : Blo 143792 936173 := bstep (se 3 (by rfl) ⟨175532, by rfl⟩ : syracuseStep 936173 = 351065) B351065
theorem B2377997 : Blo 143792 2377997 := bstep (se 3 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 2377997 = 891749) B891749
theorem B936251 : Blo 143792 936251 := bstep (se 1 (by rfl) ⟨702188, by rfl⟩ : syracuseStep 936251 = 1404377) B1404377
theorem B248123 : Blo 143792 248123 := bstep (se 1 (by rfl) ⟨186092, by rfl⟩ : syracuseStep 248123 = 372185) B372185
theorem B182827 : Blo 143792 182827 := bstep (se 1 (by rfl) ⟨137120, by rfl⟩ : syracuseStep 182827 = 274241) B274241
theorem B215723 : Blo 143792 215723 := bstep (se 1 (by rfl) ⟨161792, by rfl⟩ : syracuseStep 215723 = 323585) B323585
theorem B215753 : Blo 143792 215753 := bstep (se 2 (by rfl) ⟨80907, by rfl⟩ : syracuseStep 215753 = 161815) B161815
theorem B314057 : Blo 143792 314057 := bstep (se 2 (by rfl) ⟨117771, by rfl⟩ : syracuseStep 314057 = 235543) B235543
theorem B248521 : Blo 143792 248521 := bstep (se 2 (by rfl) ⟨93195, by rfl⟩ : syracuseStep 248521 = 186391) B186391
theorem B183055 : Blo 143792 183055 := bstep (se 1 (by rfl) ⟨137291, by rfl⟩ : syracuseStep 183055 = 274583) B274583
theorem B215867 : Blo 143792 215867 := bstep (se 1 (by rfl) ⟨161900, by rfl⟩ : syracuseStep 215867 = 323801) B323801
theorem B215927 : Blo 143792 215927 := bstep (se 1 (by rfl) ⟨161945, by rfl⟩ : syracuseStep 215927 = 323891) B323891
theorem B215951 : Blo 143792 215951 := bstep (se 1 (by rfl) ⟨161963, by rfl⟩ : syracuseStep 215951 = 323927) B323927
theorem B2837429 : Blo 143792 2837429 := bstep (se 5 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 2837429 = 266009) B266009
theorem B215993 : Blo 143792 215993 := bstep (se 2 (by rfl) ⟨80997, by rfl⟩ : syracuseStep 215993 = 161995) B161995
theorem B216071 : Blo 143792 216071 := bstep (se 1 (by rfl) ⟨162053, by rfl⟩ : syracuseStep 216071 = 324107) B324107
theorem B412705 : Blo 143792 412705 := bstep (se 2 (by rfl) ⟨154764, by rfl⟩ : syracuseStep 412705 = 309529) B309529
theorem B216107 : Blo 143792 216107 := bstep (se 1 (by rfl) ⟨162080, by rfl⟩ : syracuseStep 216107 = 324161) B324161
theorem B216137 : Blo 143792 216137 := bstep (se 2 (by rfl) ⟨81051, by rfl⟩ : syracuseStep 216137 = 162103) B162103
theorem B216251 : Blo 143792 216251 := bstep (se 1 (by rfl) ⟨162188, by rfl⟩ : syracuseStep 216251 = 324377) B324377
theorem B216311 : Blo 143792 216311 := bstep (se 1 (by rfl) ⟨162233, by rfl⟩ : syracuseStep 216311 = 324467) B324467
theorem B216335 : Blo 143792 216335 := bstep (se 1 (by rfl) ⟨162251, by rfl⟩ : syracuseStep 216335 = 324503) B324503
theorem B216377 : Blo 143792 216377 := bstep (se 2 (by rfl) ⟨81141, by rfl⟩ : syracuseStep 216377 = 162283) B162283
theorem B216455 : Blo 143792 216455 := bstep (se 1 (by rfl) ⟨162341, by rfl⟩ : syracuseStep 216455 = 324683) B324683
theorem B1887623 : Blo 143792 1887623 := bstep (se 1 (by rfl) ⟨1415717, by rfl⟩ : syracuseStep 1887623 = 2831435) B2831435
theorem B249223 : Blo 143792 249223 := bstep (se 1 (by rfl) ⟨186917, by rfl⟩ : syracuseStep 249223 = 373835) B373835
theorem B216491 : Blo 143792 216491 := bstep (se 1 (by rfl) ⟨162368, by rfl⟩ : syracuseStep 216491 = 324737) B324737
theorem B216521 : Blo 143792 216521 := bstep (se 2 (by rfl) ⟨81195, by rfl⟩ : syracuseStep 216521 = 162391) B162391
theorem B183799 : Blo 143792 183799 := bstep (se 1 (by rfl) ⟨137849, by rfl⟩ : syracuseStep 183799 = 275699) B275699
theorem B216635 : Blo 143792 216635 := bstep (se 1 (by rfl) ⟨162476, by rfl⟩ : syracuseStep 216635 = 324953) B324953
theorem B216695 : Blo 143792 216695 := bstep (se 1 (by rfl) ⟨162521, by rfl⟩ : syracuseStep 216695 = 325043) B325043
theorem B216719 : Blo 143792 216719 := bstep (se 1 (by rfl) ⟨162539, by rfl⟩ : syracuseStep 216719 = 325079) B325079
theorem B216761 : Blo 143792 216761 := bstep (se 2 (by rfl) ⟨81285, by rfl⟩ : syracuseStep 216761 = 162571) B162571
theorem B315065 : Blo 143792 315065 := bstep (se 2 (by rfl) ⟨118149, by rfl⟩ : syracuseStep 315065 = 236299) B236299
theorem B216839 : Blo 143792 216839 := bstep (se 1 (by rfl) ⟨162629, by rfl⟩ : syracuseStep 216839 = 325259) B325259
theorem B216875 : Blo 143792 216875 := bstep (se 1 (by rfl) ⟨162656, by rfl⟩ : syracuseStep 216875 = 325313) B325313
theorem B184123 : Blo 143792 184123 := bstep (se 1 (by rfl) ⟨138092, by rfl⟩ : syracuseStep 184123 = 276185) B276185
theorem B216905 : Blo 143792 216905 := bstep (se 2 (by rfl) ⟨81339, by rfl⟩ : syracuseStep 216905 = 162679) B162679
theorem B217019 : Blo 143792 217019 := bstep (se 1 (by rfl) ⟨162764, by rfl⟩ : syracuseStep 217019 = 325529) B325529
theorem B217079 : Blo 143792 217079 := bstep (se 1 (by rfl) ⟨162809, by rfl⟩ : syracuseStep 217079 = 325619) B325619
theorem B217103 : Blo 143792 217103 := bstep (se 1 (by rfl) ⟨162827, by rfl⟩ : syracuseStep 217103 = 325655) B325655
theorem B315407 : Blo 143792 315407 := bstep (se 1 (by rfl) ⟨236555, by rfl⟩ : syracuseStep 315407 = 473111) B473111
theorem B217145 : Blo 143792 217145 := bstep (se 2 (by rfl) ⟨81429, by rfl⟩ : syracuseStep 217145 = 162859) B162859
theorem B1986677 : Blo 143792 1986677 := bstep (se 5 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 1986677 = 186251) B186251
theorem B217223 : Blo 143792 217223 := bstep (se 1 (by rfl) ⟨162917, by rfl⟩ : syracuseStep 217223 = 325835) B325835
theorem B217259 : Blo 143792 217259 := bstep (se 1 (by rfl) ⟨162944, by rfl⟩ : syracuseStep 217259 = 325889) B325889
theorem B217289 : Blo 143792 217289 := bstep (se 2 (by rfl) ⟨81483, by rfl⟩ : syracuseStep 217289 = 162967) B162967
theorem B413981 : Blo 143792 413981 := bstep (se 3 (by rfl) ⟨77621, by rfl⟩ : syracuseStep 413981 = 155243) B155243
theorem B839969 : Blo 143792 839969 := bstep (se 2 (by rfl) ⟨314988, by rfl⟩ : syracuseStep 839969 = 629977) B629977
theorem B184619 : Blo 143792 184619 := bstep (se 1 (by rfl) ⟨138464, by rfl⟩ : syracuseStep 184619 = 276929) B276929
theorem B217403 : Blo 143792 217403 := bstep (se 1 (by rfl) ⟨163052, by rfl⟩ : syracuseStep 217403 = 326105) B326105
theorem B217463 : Blo 143792 217463 := bstep (se 1 (by rfl) ⟨163097, by rfl⟩ : syracuseStep 217463 = 326195) B326195
theorem B217487 : Blo 143792 217487 := bstep (se 1 (by rfl) ⟨163115, by rfl⟩ : syracuseStep 217487 = 326231) B326231
theorem B217529 : Blo 143792 217529 := bstep (se 2 (by rfl) ⟨81573, by rfl⟩ : syracuseStep 217529 = 163147) B163147
theorem B414209 : Blo 143792 414209 := bstep (se 2 (by rfl) ⟨155328, by rfl⟩ : syracuseStep 414209 = 310657) B310657
theorem B217607 : Blo 143792 217607 := bstep (se 1 (by rfl) ⟨163205, by rfl⟩ : syracuseStep 217607 = 326411) B326411
theorem B217643 : Blo 143792 217643 := bstep (se 1 (by rfl) ⟨163232, by rfl⟩ : syracuseStep 217643 = 326465) B326465
theorem B217673 : Blo 143792 217673 := bstep (se 2 (by rfl) ⟨81627, by rfl⟩ : syracuseStep 217673 = 163255) B163255
theorem B1167949 : Blo 143792 1167949 := bstep (se 3 (by rfl) ⟨218990, by rfl⟩ : syracuseStep 1167949 = 437981) B437981
theorem B217787 : Blo 143792 217787 := bstep (se 1 (by rfl) ⟨163340, by rfl⟩ : syracuseStep 217787 = 326681) B326681
theorem B217847 : Blo 143792 217847 := bstep (se 1 (by rfl) ⟨163385, by rfl⟩ : syracuseStep 217847 = 326771) B326771
theorem B185095 : Blo 143792 185095 := bstep (se 1 (by rfl) ⟨138821, by rfl⟩ : syracuseStep 185095 = 277643) B277643
theorem B217871 : Blo 143792 217871 := bstep (se 1 (by rfl) ⟨163403, by rfl⟩ : syracuseStep 217871 = 326807) B326807
theorem B217913 : Blo 143792 217913 := bstep (se 2 (by rfl) ⟨81717, by rfl⟩ : syracuseStep 217913 = 163435) B163435
theorem B414551 : Blo 143792 414551 := bstep (se 1 (by rfl) ⟨310913, by rfl⟩ : syracuseStep 414551 = 621827) B621827
theorem B217991 : Blo 143792 217991 := bstep (se 1 (by rfl) ⟨163493, by rfl⟩ : syracuseStep 217991 = 326987) B326987
theorem B218027 : Blo 143792 218027 := bstep (se 1 (by rfl) ⟨163520, by rfl⟩ : syracuseStep 218027 = 327041) B327041
theorem B218057 : Blo 143792 218057 := bstep (se 2 (by rfl) ⟨81771, by rfl⟩ : syracuseStep 218057 = 163543) B163543
theorem B414665 : Blo 143792 414665 := bstep (se 2 (by rfl) ⟨155499, by rfl⟩ : syracuseStep 414665 = 310999) B310999
theorem B218171 : Blo 143792 218171 := bstep (se 1 (by rfl) ⟨163628, by rfl⟩ : syracuseStep 218171 = 327257) B327257
theorem B218231 : Blo 143792 218231 := bstep (se 1 (by rfl) ⟨163673, by rfl⟩ : syracuseStep 218231 = 327347) B327347
theorem B218255 : Blo 143792 218255 := bstep (se 1 (by rfl) ⟨163691, by rfl⟩ : syracuseStep 218255 = 327383) B327383
theorem B218297 : Blo 143792 218297 := bstep (se 2 (by rfl) ⟨81861, by rfl⟩ : syracuseStep 218297 = 163723) B163723
theorem B185591 : Blo 143792 185591 := bstep (se 1 (by rfl) ⟨139193, by rfl⟩ : syracuseStep 185591 = 278387) B278387
theorem B218375 : Blo 143792 218375 := bstep (se 1 (by rfl) ⟨163781, by rfl⟩ : syracuseStep 218375 = 327563) B327563
theorem B349451 : Blo 143792 349451 := bstep (se 1 (by rfl) ⟨262088, by rfl⟩ : syracuseStep 349451 = 524177) B524177
theorem B218411 : Blo 143792 218411 := bstep (se 1 (by rfl) ⟨163808, by rfl⟩ : syracuseStep 218411 = 327617) B327617
theorem B677179 : Blo 143792 677179 := bstep (se 1 (by rfl) ⟨507884, by rfl⟩ : syracuseStep 677179 = 1015769) B1015769
theorem B218441 : Blo 143792 218441 := bstep (se 2 (by rfl) ⟨81915, by rfl⟩ : syracuseStep 218441 = 163831) B163831
theorem B185743 : Blo 143792 185743 := bstep (se 1 (by rfl) ⟨139307, by rfl⟩ : syracuseStep 185743 = 278615) B278615
theorem B218555 : Blo 143792 218555 := bstep (se 1 (by rfl) ⟨163916, by rfl⟩ : syracuseStep 218555 = 327833) B327833
theorem B26891747 : Blo 143792 26891747 := bstep (se 1 (by rfl) ⟨20168810, by rfl⟩ : syracuseStep 26891747 = 40337621) B40337621
theorem B218615 : Blo 143792 218615 := bstep (se 1 (by rfl) ⟨163961, by rfl⟩ : syracuseStep 218615 = 327923) B327923
theorem B218639 : Blo 143792 218639 := bstep (se 1 (by rfl) ⟨163979, by rfl⟩ : syracuseStep 218639 = 327959) B327959
theorem B251407 : Blo 143792 251407 := bstep (se 1 (by rfl) ⟨188555, by rfl⟩ : syracuseStep 251407 = 377111) B377111
theorem B710167 : Blo 143792 710167 := bstep (se 1 (by rfl) ⟨532625, by rfl⟩ : syracuseStep 710167 = 1065251) B1065251
theorem B218681 : Blo 143792 218681 := bstep (se 2 (by rfl) ⟨82005, by rfl⟩ : syracuseStep 218681 = 164011) B164011
theorem B185915 : Blo 143792 185915 := bstep (se 1 (by rfl) ⟨139436, by rfl⟩ : syracuseStep 185915 = 278873) B278873
theorem B546371 : Blo 143792 546371 := bstep (se 1 (by rfl) ⟨409778, by rfl⟩ : syracuseStep 546371 = 819557) B819557
theorem B218759 : Blo 143792 218759 := bstep (se 1 (by rfl) ⟨164069, by rfl⟩ : syracuseStep 218759 = 328139) B328139
theorem B218795 : Blo 143792 218795 := bstep (se 1 (by rfl) ⟨164096, by rfl⟩ : syracuseStep 218795 = 328193) B328193
theorem B218825 : Blo 143792 218825 := bstep (se 2 (by rfl) ⟨82059, by rfl⟩ : syracuseStep 218825 = 164119) B164119
theorem B218939 : Blo 143792 218939 := bstep (se 1 (by rfl) ⟨164204, by rfl⟩ : syracuseStep 218939 = 328409) B328409
theorem B1103705 : Blo 143792 1103705 := bstep (se 2 (by rfl) ⟨413889, by rfl⟩ : syracuseStep 1103705 = 827779) B827779
theorem B218999 : Blo 143792 218999 := bstep (se 1 (by rfl) ⟨164249, by rfl⟩ : syracuseStep 218999 = 328499) B328499
theorem B743303 : Blo 143792 743303 := bstep (se 1 (by rfl) ⟨557477, by rfl⟩ : syracuseStep 743303 = 1114955) B1114955
theorem B219023 : Blo 143792 219023 := bstep (se 1 (by rfl) ⟨164267, by rfl⟩ : syracuseStep 219023 = 328535) B328535
theorem B219065 : Blo 143792 219065 := bstep (se 2 (by rfl) ⟨82149, by rfl⟩ : syracuseStep 219065 = 164299) B164299
theorem B219143 : Blo 143792 219143 := bstep (se 1 (by rfl) ⟨164357, by rfl⟩ : syracuseStep 219143 = 328715) B328715
theorem B219179 : Blo 143792 219179 := bstep (se 1 (by rfl) ⟨164384, by rfl⟩ : syracuseStep 219179 = 328769) B328769
theorem B219209 : Blo 143792 219209 := bstep (se 2 (by rfl) ⟨82203, by rfl⟩ : syracuseStep 219209 = 164407) B164407
theorem B219323 : Blo 143792 219323 := bstep (se 1 (by rfl) ⟨164492, by rfl⟩ : syracuseStep 219323 = 328985) B328985
theorem B219383 : Blo 143792 219383 := bstep (se 1 (by rfl) ⟨164537, by rfl⟩ : syracuseStep 219383 = 329075) B329075
theorem B219407 : Blo 143792 219407 := bstep (se 1 (by rfl) ⟨164555, by rfl⟩ : syracuseStep 219407 = 329111) B329111
theorem B219449 : Blo 143792 219449 := bstep (se 2 (by rfl) ⟨82293, by rfl⟩ : syracuseStep 219449 = 164587) B164587
theorem B219527 : Blo 143792 219527 := bstep (se 1 (by rfl) ⟨164645, by rfl⟩ : syracuseStep 219527 = 329291) B329291
theorem B219563 : Blo 143792 219563 := bstep (se 1 (by rfl) ⟨164672, by rfl⟩ : syracuseStep 219563 = 329345) B329345
theorem B219593 : Blo 143792 219593 := bstep (se 2 (by rfl) ⟨82347, by rfl⟩ : syracuseStep 219593 = 164695) B164695
theorem B186887 : Blo 143792 186887 := bstep (se 1 (by rfl) ⟨140165, by rfl⟩ : syracuseStep 186887 = 280331) B280331
theorem B547357 : Blo 143792 547357 := bstep (se 3 (by rfl) ⟨102629, by rfl⟩ : syracuseStep 547357 = 205259) B205259
theorem B219707 : Blo 143792 219707 := bstep (se 1 (by rfl) ⟨164780, by rfl⟩ : syracuseStep 219707 = 329561) B329561
theorem B219767 : Blo 143792 219767 := bstep (se 1 (by rfl) ⟨164825, by rfl⟩ : syracuseStep 219767 = 329651) B329651
theorem B350855 : Blo 143792 350855 := bstep (se 1 (by rfl) ⟨263141, by rfl⟩ : syracuseStep 350855 = 526283) B526283
theorem B219791 : Blo 143792 219791 := bstep (se 1 (by rfl) ⟨164843, by rfl⟩ : syracuseStep 219791 = 329687) B329687
theorem B416441 : Blo 143792 416441 := bstep (se 2 (by rfl) ⟨156165, by rfl⟩ : syracuseStep 416441 = 312331) B312331
theorem B219833 : Blo 143792 219833 := bstep (se 2 (by rfl) ⟨82437, by rfl⟩ : syracuseStep 219833 = 164875) B164875
theorem B219911 : Blo 143792 219911 := bstep (se 1 (by rfl) ⟨164933, by rfl⟩ : syracuseStep 219911 = 329867) B329867
theorem B1104677 : Blo 143792 1104677 := bstep (se 4 (by rfl) ⟨103563, by rfl⟩ : syracuseStep 1104677 = 207127) B207127
theorem B219947 : Blo 143792 219947 := bstep (se 1 (by rfl) ⟨164960, by rfl⟩ : syracuseStep 219947 = 329921) B329921
theorem B252715 : Blo 143792 252715 := bstep (se 1 (by rfl) ⟨189536, by rfl⟩ : syracuseStep 252715 = 379073) B379073
theorem B219977 : Blo 143792 219977 := bstep (se 2 (by rfl) ⟨82491, by rfl⟩ : syracuseStep 219977 = 164983) B164983
theorem B940889 : Blo 143792 940889 := bstep (se 2 (by rfl) ⟨352833, by rfl⟩ : syracuseStep 940889 = 705667) B705667
theorem B220091 : Blo 143792 220091 := bstep (se 1 (by rfl) ⟨165068, by rfl⟩ : syracuseStep 220091 = 330137) B330137
theorem B220151 : Blo 143792 220151 := bstep (se 1 (by rfl) ⟨165113, by rfl⟩ : syracuseStep 220151 = 330227) B330227
theorem B220175 : Blo 143792 220175 := bstep (se 1 (by rfl) ⟨165131, by rfl⟩ : syracuseStep 220175 = 330263) B330263
theorem B220217 : Blo 143792 220217 := bstep (se 2 (by rfl) ⟨82581, by rfl⟩ : syracuseStep 220217 = 165163) B165163
theorem B220295 : Blo 143792 220295 := bstep (se 1 (by rfl) ⟨165221, by rfl⟩ : syracuseStep 220295 = 330443) B330443
theorem B220331 : Blo 143792 220331 := bstep (se 1 (by rfl) ⟨165248, by rfl⟩ : syracuseStep 220331 = 330497) B330497
theorem B220361 : Blo 143792 220361 := bstep (se 2 (by rfl) ⟨82635, by rfl⟩ : syracuseStep 220361 = 165271) B165271
theorem B220475 : Blo 143792 220475 := bstep (se 1 (by rfl) ⟨165356, by rfl⟩ : syracuseStep 220475 = 330713) B330713
theorem B220535 : Blo 143792 220535 := bstep (se 1 (by rfl) ⟨165401, by rfl⟩ : syracuseStep 220535 = 330803) B330803
theorem B220559 : Blo 143792 220559 := bstep (se 1 (by rfl) ⟨165419, by rfl⟩ : syracuseStep 220559 = 330839) B330839
theorem B220601 : Blo 143792 220601 := bstep (se 2 (by rfl) ⟨82725, by rfl⟩ : syracuseStep 220601 = 165451) B165451
theorem B220663 : Blo 143792 220663 := bstep (se 1 (by rfl) ⟨165497, by rfl⟩ : syracuseStep 220663 = 330995) B330995
theorem B220679 : Blo 143792 220679 := bstep (se 1 (by rfl) ⟨165509, by rfl⟩ : syracuseStep 220679 = 331019) B331019
theorem B220715 : Blo 143792 220715 := bstep (se 1 (by rfl) ⟨165536, by rfl⟩ : syracuseStep 220715 = 331073) B331073
theorem B220745 : Blo 143792 220745 := bstep (se 2 (by rfl) ⟨82779, by rfl⟩ : syracuseStep 220745 = 165559) B165559
theorem B417433 : Blo 143792 417433 := bstep (se 2 (by rfl) ⟨156537, by rfl⟩ : syracuseStep 417433 = 313075) B313075
theorem B220859 : Blo 143792 220859 := bstep (se 1 (by rfl) ⟨165644, by rfl⟩ : syracuseStep 220859 = 331289) B331289
theorem B220919 : Blo 143792 220919 := bstep (se 1 (by rfl) ⟨165689, by rfl⟩ : syracuseStep 220919 = 331379) B331379
theorem B220943 : Blo 143792 220943 := bstep (se 1 (by rfl) ⟨165707, by rfl⟩ : syracuseStep 220943 = 331415) B331415
theorem B1498915 : Blo 143792 1498915 := bstep (se 1 (by rfl) ⟨1124186, by rfl⟩ : syracuseStep 1498915 = 2248373) B2248373
theorem B220985 : Blo 143792 220985 := bstep (se 2 (by rfl) ⟨82869, by rfl⟩ : syracuseStep 220985 = 165739) B165739
theorem B1400651 : Blo 143792 1400651 := bstep (se 1 (by rfl) ⟨1050488, by rfl⟩ : syracuseStep 1400651 = 2100977) B2100977
theorem B221063 : Blo 143792 221063 := bstep (se 1 (by rfl) ⟨165797, by rfl⟩ : syracuseStep 221063 = 331595) B331595
theorem B745361 : Blo 143792 745361 := bstep (se 2 (by rfl) ⟨279510, by rfl⟩ : syracuseStep 745361 = 559021) B559021
theorem B221099 : Blo 143792 221099 := bstep (se 1 (by rfl) ⟨165824, by rfl⟩ : syracuseStep 221099 = 331649) B331649
theorem B221129 : Blo 143792 221129 := bstep (se 2 (by rfl) ⟨82923, by rfl⟩ : syracuseStep 221129 = 165847) B165847
theorem B614411 : Blo 143792 614411 := bstep (se 1 (by rfl) ⟨460808, by rfl⟩ : syracuseStep 614411 = 921617) B921617
theorem B221243 : Blo 143792 221243 := bstep (se 1 (by rfl) ⟨165932, by rfl⟩ : syracuseStep 221243 = 331865) B331865
theorem B221303 : Blo 143792 221303 := bstep (se 1 (by rfl) ⟨165977, by rfl⟩ : syracuseStep 221303 = 331955) B331955
theorem B221327 : Blo 143792 221327 := bstep (se 1 (by rfl) ⟨165995, by rfl⟩ : syracuseStep 221327 = 331991) B331991
theorem B352441 : Blo 143792 352441 := bstep (se 2 (by rfl) ⟨132165, by rfl⟩ : syracuseStep 352441 = 264331) B264331
theorem B221369 : Blo 143792 221369 := bstep (se 2 (by rfl) ⟨83013, by rfl⟩ : syracuseStep 221369 = 166027) B166027
theorem B221447 : Blo 143792 221447 := bstep (se 1 (by rfl) ⟨166085, by rfl⟩ : syracuseStep 221447 = 332171) B332171
theorem B1171745 : Blo 143792 1171745 := bstep (se 2 (by rfl) ⟨439404, by rfl⟩ : syracuseStep 1171745 = 878809) B878809
theorem B221483 : Blo 143792 221483 := bstep (se 1 (by rfl) ⟨166112, by rfl⟩ : syracuseStep 221483 = 332225) B332225
theorem B221513 : Blo 143792 221513 := bstep (se 2 (by rfl) ⟨83067, by rfl⟩ : syracuseStep 221513 = 166135) B166135
theorem B221627 : Blo 143792 221627 := bstep (se 1 (by rfl) ⟨166220, by rfl⟩ : syracuseStep 221627 = 332441) B332441
theorem B221687 : Blo 143792 221687 := bstep (se 1 (by rfl) ⟨166265, by rfl⟩ : syracuseStep 221687 = 332531) B332531
theorem B28697813 : Blo 143792 28697813 := bstep (se 7 (by rfl) ⟨336302, by rfl⟩ : syracuseStep 28697813 = 672605) B672605
theorem B550259 : Blo 143792 550259 := bstep (se 1 (by rfl) ⟨412694, by rfl⟩ : syracuseStep 550259 = 825389) B825389
theorem B419357 : Blo 143792 419357 := bstep (se 3 (by rfl) ⟨78629, by rfl⟩ : syracuseStep 419357 = 157259) B157259
theorem B779863 : Blo 143792 779863 := bstep (se 1 (by rfl) ⟨584897, by rfl⟩ : syracuseStep 779863 = 1169795) B1169795
theorem B157447 : Blo 143792 157447 := bstep (se 1 (by rfl) ⟨118085, by rfl⟩ : syracuseStep 157447 = 236171) B236171
theorem B747467 : Blo 143792 747467 := bstep (se 1 (by rfl) ⟨560600, by rfl⟩ : syracuseStep 747467 = 1121201) B1121201
theorem B1665035 : Blo 143792 1665035 := bstep (se 1 (by rfl) ⟨1248776, by rfl⟩ : syracuseStep 1665035 = 2497553) B2497553
theorem B485405 : Blo 143792 485405 := bstep (se 3 (by rfl) ⟨91013, by rfl⟩ : syracuseStep 485405 = 182027) B182027
theorem B420041 : Blo 143792 420041 := bstep (se 2 (by rfl) ⟨157515, by rfl⟩ : syracuseStep 420041 = 315031) B315031
theorem B747791 : Blo 143792 747791 := bstep (se 1 (by rfl) ⟨560843, by rfl⟩ : syracuseStep 747791 = 1121687) B1121687
theorem B518699 : Blo 143792 518699 := bstep (se 1 (by rfl) ⟨389024, by rfl⟩ : syracuseStep 518699 = 778049) B778049
theorem B2779919 : Blo 143792 2779919 := bstep (se 1 (by rfl) ⟨2084939, by rfl⟩ : syracuseStep 2779919 = 4169879) B4169879
theorem B420623 : Blo 143792 420623 := bstep (se 1 (by rfl) ⟨315467, by rfl⟩ : syracuseStep 420623 = 630935) B630935
theorem B682897 : Blo 143792 682897 := bstep (se 2 (by rfl) ⟨256086, by rfl⟩ : syracuseStep 682897 = 512173) B512173
theorem B486809 : Blo 143792 486809 := bstep (se 2 (by rfl) ⟨182553, by rfl⟩ : syracuseStep 486809 = 365107) B365107
theorem B519709 : Blo 143792 519709 := bstep (se 3 (by rfl) ⟨97445, by rfl⟩ : syracuseStep 519709 = 194891) B194891
theorem B552491 : Blo 143792 552491 := bstep (se 1 (by rfl) ⟨414368, by rfl⟩ : syracuseStep 552491 = 828737) B828737
theorem B945935 : Blo 143792 945935 := bstep (se 1 (by rfl) ⟨709451, by rfl⟩ : syracuseStep 945935 = 1418903) B1418903
theorem B487511 : Blo 143792 487511 := bstep (se 1 (by rfl) ⟨365633, by rfl⟩ : syracuseStep 487511 = 731267) B731267
theorem B323855 : Blo 143792 323855 := bstep (se 1 (by rfl) ⟨242891, by rfl⟩ : syracuseStep 323855 = 485783) B485783
theorem B323873 : Blo 143792 323873 := bstep (se 2 (by rfl) ⟨121452, by rfl⟩ : syracuseStep 323873 = 242905) B242905
theorem B618785 : Blo 143792 618785 := bstep (se 2 (by rfl) ⟨232044, by rfl⟩ : syracuseStep 618785 = 464089) B464089
theorem B487997 : Blo 143792 487997 := bstep (se 3 (by rfl) ⟨91499, by rfl⟩ : syracuseStep 487997 = 182999) B182999
theorem B881239 : Blo 143792 881239 := bstep (se 1 (by rfl) ⟨660929, by rfl⟩ : syracuseStep 881239 = 1321859) B1321859
theorem B324215 : Blo 143792 324215 := bstep (se 1 (by rfl) ⟨243161, by rfl⟩ : syracuseStep 324215 = 486323) B486323
theorem B619127 : Blo 143792 619127 := bstep (se 1 (by rfl) ⟨464345, by rfl⟩ : syracuseStep 619127 = 928691) B928691
theorem B324395 : Blo 143792 324395 := bstep (se 1 (by rfl) ⟨243296, by rfl⟩ : syracuseStep 324395 = 486593) B486593
theorem B291899 : Blo 143792 291899 := bstep (se 1 (by rfl) ⟨218924, by rfl⟩ : syracuseStep 291899 = 437849) B437849
theorem B9172099 : Blo 143792 9172099 := bstep (se 1 (by rfl) ⟨6879074, by rfl⟩ : syracuseStep 9172099 = 13758149) B13758149
theorem B324755 : Blo 143792 324755 := bstep (se 1 (by rfl) ⟨243566, by rfl⟩ : syracuseStep 324755 = 487133) B487133
theorem B324809 : Blo 143792 324809 := bstep (se 2 (by rfl) ⟨121803, by rfl⟩ : syracuseStep 324809 = 243607) B243607
theorem B1111481 : Blo 143792 1111481 := bstep (se 2 (by rfl) ⟨416805, by rfl⟩ : syracuseStep 1111481 = 833611) B833611
theorem B3700403 : Blo 143792 3700403 := bstep (se 1 (by rfl) ⟨2775302, by rfl⟩ : syracuseStep 3700403 = 5550605) B5550605
theorem B325511 : Blo 143792 325511 := bstep (se 1 (by rfl) ⟨244133, by rfl⟩ : syracuseStep 325511 = 488267) B488267
theorem B489401 : Blo 143792 489401 := bstep (se 2 (by rfl) ⟨183525, by rfl⟩ : syracuseStep 489401 = 367051) B367051
theorem B194491 : Blo 143792 194491 := bstep (se 1 (by rfl) ⟨145868, by rfl⟩ : syracuseStep 194491 = 291737) B291737
theorem B5732369 : Blo 143792 5732369 := bstep (se 2 (by rfl) ⟨2149638, by rfl⟩ : syracuseStep 5732369 = 4299277) B4299277
theorem B161851 : Blo 143792 161851 := bstep (se 1 (by rfl) ⟨121388, by rfl⟩ : syracuseStep 161851 = 242777) B242777
theorem B325691 : Blo 143792 325691 := bstep (se 1 (by rfl) ⟨244268, by rfl⟩ : syracuseStep 325691 = 488537) B488537
theorem B1243309 : Blo 143792 1243309 := bstep (se 3 (by rfl) ⟨233120, by rfl⟩ : syracuseStep 1243309 = 466241) B466241
theorem B325817 : Blo 143792 325817 := bstep (se 2 (by rfl) ⟨122181, by rfl⟩ : syracuseStep 325817 = 244363) B244363
theorem B194761 : Blo 143792 194761 := bstep (se 2 (by rfl) ⟨73035, by rfl⟩ : syracuseStep 194761 = 146071) B146071
theorem B1669409 : Blo 143792 1669409 := bstep (se 2 (by rfl) ⟨626028, by rfl⟩ : syracuseStep 1669409 = 1252057) B1252057
theorem B489995 : Blo 143792 489995 := bstep (se 1 (by rfl) ⟨367496, by rfl⟩ : syracuseStep 489995 = 734993) B734993
theorem B162319 : Blo 143792 162319 := bstep (se 1 (by rfl) ⟨121739, by rfl⟩ : syracuseStep 162319 = 243479) B243479
theorem B326159 : Blo 143792 326159 := bstep (se 1 (by rfl) ⟨244619, by rfl⟩ : syracuseStep 326159 = 489239) B489239
theorem B326177 : Blo 143792 326177 := bstep (se 2 (by rfl) ⟨122316, by rfl⟩ : syracuseStep 326177 = 244633) B244633
theorem B490103 : Blo 143792 490103 := bstep (se 1 (by rfl) ⟨367577, by rfl⟩ : syracuseStep 490103 = 735155) B735155
theorem B326519 : Blo 143792 326519 := bstep (se 1 (by rfl) ⟨244889, by rfl⟩ : syracuseStep 326519 = 489779) B489779
theorem B555923 : Blo 143792 555923 := bstep (se 1 (by rfl) ⟨416942, by rfl⟩ : syracuseStep 555923 = 833885) B833885
theorem B162823 : Blo 143792 162823 := bstep (se 1 (by rfl) ⟨122117, by rfl⟩ : syracuseStep 162823 = 244235) B244235
theorem B326699 : Blo 143792 326699 := bstep (se 1 (by rfl) ⟨245024, by rfl⟩ : syracuseStep 326699 = 490049) B490049
theorem B6454333 : Blo 143792 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B163003 : Blo 143792 163003 := bstep (se 1 (by rfl) ⟨122252, by rfl⟩ : syracuseStep 163003 = 244505) B244505
theorem B490697 : Blo 143792 490697 := bstep (se 2 (by rfl) ⟨184011, by rfl⟩ : syracuseStep 490697 = 368023) B368023
theorem B327059 : Blo 143792 327059 := bstep (se 1 (by rfl) ⟨245294, by rfl⟩ : syracuseStep 327059 = 490589) B490589
theorem B327113 : Blo 143792 327113 := bstep (se 2 (by rfl) ⟨122667, by rfl⟩ : syracuseStep 327113 = 245335) B245335
theorem B163471 : Blo 143792 163471 := bstep (se 1 (by rfl) ⟨122603, by rfl⟩ : syracuseStep 163471 = 245207) B245207
theorem B425729 : Blo 143792 425729 := bstep (se 2 (by rfl) ⟨159648, by rfl⟩ : syracuseStep 425729 = 319297) B319297
theorem B491399 : Blo 143792 491399 := bstep (se 1 (by rfl) ⟨368549, by rfl⟩ : syracuseStep 491399 = 737099) B737099
theorem B557063 : Blo 143792 557063 := bstep (se 1 (by rfl) ⟨417797, by rfl⟩ : syracuseStep 557063 = 835595) B835595
theorem B1572941 : Blo 143792 1572941 := bstep (se 3 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 1572941 = 589853) B589853
theorem B327851 : Blo 143792 327851 := bstep (se 1 (by rfl) ⟨245888, by rfl⟩ : syracuseStep 327851 = 491777) B491777
theorem B164191 : Blo 143792 164191 := bstep (se 1 (by rfl) ⟨123143, by rfl⟩ : syracuseStep 164191 = 246287) B246287
theorem B262543 : Blo 143792 262543 := bstep (se 1 (by rfl) ⟨196907, by rfl⟩ : syracuseStep 262543 = 393815) B393815
theorem B557549 : Blo 143792 557549 := bstep (se 3 (by rfl) ⟨104540, by rfl⟩ : syracuseStep 557549 = 209081) B209081
theorem B492155 : Blo 143792 492155 := bstep (se 1 (by rfl) ⟨369116, by rfl⟩ : syracuseStep 492155 = 738233) B738233
theorem B328391 : Blo 143792 328391 := bstep (se 1 (by rfl) ⟨246293, by rfl⟩ : syracuseStep 328391 = 492587) B492587
theorem B164551 : Blo 143792 164551 := bstep (se 1 (by rfl) ⟨123413, by rfl⟩ : syracuseStep 164551 = 246827) B246827
theorem B1114825 : Blo 143792 1114825 := bstep (se 2 (by rfl) ⟨418059, by rfl⟩ : syracuseStep 1114825 = 836119) B836119
theorem B1409795 : Blo 143792 1409795 := bstep (se 1 (by rfl) ⟨1057346, by rfl⟩ : syracuseStep 1409795 = 2114693) B2114693
theorem B1114883 : Blo 143792 1114883 := bstep (se 1 (by rfl) ⟨836162, by rfl⟩ : syracuseStep 1114883 = 1672325) B1672325
theorem B492317 : Blo 143792 492317 := bstep (se 3 (by rfl) ⟨92309, by rfl⟩ : syracuseStep 492317 = 184619) B184619
theorem B557867 : Blo 143792 557867 := bstep (se 1 (by rfl) ⟨418400, by rfl⟩ : syracuseStep 557867 = 836801) B836801
theorem B787457 : Blo 143792 787457 := bstep (se 2 (by rfl) ⟨295296, by rfl⟩ : syracuseStep 787457 = 590593) B590593
theorem B787475 : Blo 143792 787475 := bstep (se 1 (by rfl) ⟨590606, by rfl⟩ : syracuseStep 787475 = 1181213) B1181213
theorem B590867 : Blo 143792 590867 := bstep (se 1 (by rfl) ⟨443150, by rfl⟩ : syracuseStep 590867 = 886301) B886301
theorem B5309489 : Blo 143792 5309489 := bstep (se 2 (by rfl) ⟨1991058, by rfl⟩ : syracuseStep 5309489 = 3982117) B3982117
theorem B328951 : Blo 143792 328951 := bstep (se 1 (by rfl) ⟨246713, by rfl⟩ : syracuseStep 328951 = 493427) B493427
theorem B918821 : Blo 143792 918821 := bstep (se 4 (by rfl) ⟨86139, by rfl⟩ : syracuseStep 918821 = 172279) B172279
theorem B296335 : Blo 143792 296335 := bstep (se 1 (by rfl) ⟨222251, by rfl⟩ : syracuseStep 296335 = 444503) B444503
theorem B493019 : Blo 143792 493019 := bstep (se 1 (by rfl) ⟨369764, by rfl⟩ : syracuseStep 493019 = 739529) B739529
theorem B624115 : Blo 143792 624115 := bstep (se 1 (by rfl) ⟨468086, by rfl⟩ : syracuseStep 624115 = 936173) B936173
theorem B624167 : Blo 143792 624167 := bstep (se 1 (by rfl) ⟨468125, by rfl⟩ : syracuseStep 624167 = 936251) B936251
theorem B329255 : Blo 143792 329255 := bstep (se 1 (by rfl) ⟨246941, by rfl⟩ : syracuseStep 329255 = 493883) B493883
theorem B165415 : Blo 143792 165415 := bstep (se 1 (by rfl) ⟨124061, by rfl⟩ : syracuseStep 165415 = 248123) B248123
theorem B263927 : Blo 143792 263927 := bstep (se 1 (by rfl) ⟨197945, by rfl⟩ : syracuseStep 263927 = 395891) B395891
theorem B329579 : Blo 143792 329579 := bstep (se 1 (by rfl) ⟨247184, by rfl⟩ : syracuseStep 329579 = 494369) B494369
theorem B329633 : Blo 143792 329633 := bstep (se 2 (by rfl) ⟨123612, by rfl⟩ : syracuseStep 329633 = 247225) B247225
theorem B493721 : Blo 143792 493721 := bstep (se 2 (by rfl) ⟨185145, by rfl⟩ : syracuseStep 493721 = 370291) B370291
theorem B329975 : Blo 143792 329975 := bstep (se 1 (by rfl) ⟨247481, by rfl⟩ : syracuseStep 329975 = 494963) B494963
theorem B526945 : Blo 143792 526945 := bstep (se 2 (by rfl) ⟨197604, by rfl⟩ : syracuseStep 526945 = 395209) B395209
theorem B330569 : Blo 143792 330569 := bstep (se 2 (by rfl) ⟨123963, by rfl⟩ : syracuseStep 330569 = 247927) B247927
theorem B559979 : Blo 143792 559979 := bstep (se 1 (by rfl) ⟨419984, by rfl⟩ : syracuseStep 559979 = 839969) B839969
theorem B1051697 : Blo 143792 1051697 := bstep (se 2 (by rfl) ⟨394386, by rfl⟩ : syracuseStep 1051697 = 788773) B788773
theorem B265427 : Blo 143792 265427 := bstep (se 1 (by rfl) ⟨199070, by rfl⟩ : syracuseStep 265427 = 398141) B398141
theorem B494909 : Blo 143792 494909 := bstep (se 3 (by rfl) ⟨92795, by rfl⟩ : syracuseStep 494909 = 185591) B185591
theorem B527741 : Blo 143792 527741 := bstep (se 3 (by rfl) ⟨98951, by rfl⟩ : syracuseStep 527741 = 197903) B197903
theorem B396787 : Blo 143792 396787 := bstep (se 1 (by rfl) ⟨297590, by rfl⟩ : syracuseStep 396787 = 595181) B595181
theorem B232967 : Blo 143792 232967 := bstep (se 1 (by rfl) ⟨174725, by rfl⟩ : syracuseStep 232967 = 349451) B349451
theorem B331361 : Blo 143792 331361 := bstep (se 2 (by rfl) ⟨124260, by rfl⟩ : syracuseStep 331361 = 248521) B248521
theorem B17927831 : Blo 143792 17927831 := bstep (se 1 (by rfl) ⟨13445873, by rfl⟩ : syracuseStep 17927831 = 26891747) B26891747
theorem B364247 : Blo 143792 364247 := bstep (se 1 (by rfl) ⟨273185, by rfl⟩ : syracuseStep 364247 = 546371) B546371
theorem B331627 : Blo 143792 331627 := bstep (se 1 (by rfl) ⟨248720, by rfl⟩ : syracuseStep 331627 = 497441) B497441
theorem B331703 : Blo 143792 331703 := bstep (se 1 (by rfl) ⟨248777, by rfl⟩ : syracuseStep 331703 = 497555) B497555
theorem B593851 : Blo 143792 593851 := bstep (se 1 (by rfl) ⟨445388, by rfl⟩ : syracuseStep 593851 = 890777) B890777
theorem B364601 : Blo 143792 364601 := bstep (se 2 (by rfl) ⟨136725, by rfl⟩ : syracuseStep 364601 = 273451) B273451
theorem B1118285 : Blo 143792 1118285 := bstep (se 3 (by rfl) ⟨209678, by rfl⟩ : syracuseStep 1118285 = 419357) B419357
theorem B200827 : Blo 143792 200827 := bstep (se 1 (by rfl) ⟨150620, by rfl⟩ : syracuseStep 200827 = 301241) B301241
theorem B495773 : Blo 143792 495773 := bstep (se 3 (by rfl) ⟨92957, by rfl⟩ : syracuseStep 495773 = 185915) B185915
theorem B1052939 : Blo 143792 1052939 := bstep (se 1 (by rfl) ⟨789704, by rfl⟩ : syracuseStep 1052939 = 1579409) B1579409
theorem B233903 : Blo 143792 233903 := bstep (se 1 (by rfl) ⟨175427, by rfl⟩ : syracuseStep 233903 = 350855) B350855
theorem B528905 : Blo 143792 528905 := bstep (se 2 (by rfl) ⟨198339, by rfl⟩ : syracuseStep 528905 = 396679) B396679
theorem B332297 : Blo 143792 332297 := bstep (se 2 (by rfl) ⟨124611, by rfl⟩ : syracuseStep 332297 = 249223) B249223
theorem B627259 : Blo 143792 627259 := bstep (se 1 (by rfl) ⟨470444, by rfl⟩ : syracuseStep 627259 = 940889) B940889
theorem B496313 : Blo 143792 496313 := bstep (se 2 (by rfl) ⟨186117, by rfl⟩ : syracuseStep 496313 = 372235) B372235
theorem B692945 : Blo 143792 692945 := bstep (se 2 (by rfl) ⟨259854, by rfl⟩ : syracuseStep 692945 = 519709) B519709
theorem B234505 : Blo 143792 234505 := bstep (se 2 (by rfl) ⟨87939, by rfl⟩ : syracuseStep 234505 = 175879) B175879
theorem B496907 : Blo 143792 496907 := bstep (se 1 (by rfl) ⟨372680, by rfl⟩ : syracuseStep 496907 = 745361) B745361
theorem B5969371 : Blo 143792 5969371 := bstep (se 1 (by rfl) ⟨4477028, by rfl⟩ : syracuseStep 5969371 = 8954057) B8954057
theorem B497177 : Blo 143792 497177 := bstep (se 2 (by rfl) ⟨186441, by rfl⟩ : syracuseStep 497177 = 372883) B372883
theorem B366839 : Blo 143792 366839 := bstep (se 1 (by rfl) ⟨275129, by rfl⟩ : syracuseStep 366839 = 550259) B550259
theorem B1120715 : Blo 143792 1120715 := bstep (se 1 (by rfl) ⟨840536, by rfl⟩ : syracuseStep 1120715 = 1681073) B1681073
theorem B268763 : Blo 143792 268763 := bstep (se 1 (by rfl) ⟨201572, by rfl⟩ : syracuseStep 268763 = 403145) B403145
theorem B465371 : Blo 143792 465371 := bstep (se 1 (by rfl) ⟨349028, by rfl⟩ : syracuseStep 465371 = 698057) B698057
theorem B498311 : Blo 143792 498311 := bstep (se 1 (by rfl) ⟨373733, by rfl⟩ : syracuseStep 498311 = 747467) B747467
theorem B793273 : Blo 143792 793273 := bstep (se 2 (by rfl) ⟨297477, by rfl⟩ : syracuseStep 793273 = 594955) B594955
theorem B498365 : Blo 143792 498365 := bstep (se 3 (by rfl) ⟨93443, by rfl⟩ : syracuseStep 498365 = 186887) B186887
theorem B1678157 : Blo 143792 1678157 := bstep (se 3 (by rfl) ⟨314654, by rfl⟩ : syracuseStep 1678157 = 629309) B629309
theorem B12229465 : Blo 143792 12229465 := bstep (se 2 (by rfl) ⟨4586049, by rfl⟩ : syracuseStep 12229465 = 9172099) B9172099
theorem B498527 : Blo 143792 498527 := bstep (se 1 (by rfl) ⟨373895, by rfl⟩ : syracuseStep 498527 = 747791) B747791
theorem B3611621 : Blo 143792 3611621 := bstep (se 4 (by rfl) ⟨338589, by rfl⟩ : syracuseStep 3611621 = 677179) B677179
theorem B498689 : Blo 143792 498689 := bstep (se 2 (by rfl) ⟨187008, by rfl⟩ : syracuseStep 498689 = 374017) B374017
theorem B924691 : Blo 143792 924691 := bstep (se 1 (by rfl) ⟨693518, by rfl⟩ : syracuseStep 924691 = 1387037) B1387037
theorem B4300121 : Blo 143792 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B4038173 : Blo 143792 4038173 := bstep (se 3 (by rfl) ⟨757157, by rfl⟩ : syracuseStep 4038173 = 1514315) B1514315
theorem B532007 : Blo 143792 532007 := bstep (se 1 (by rfl) ⟨399005, by rfl⟩ : syracuseStep 532007 = 798011) B798011
theorem B925307 : Blo 143792 925307 := bstep (se 1 (by rfl) ⟨693980, by rfl⟩ : syracuseStep 925307 = 1387961) B1387961
theorem B1842821 : Blo 143792 1842821 := bstep (se 4 (by rfl) ⟨172764, by rfl⟩ : syracuseStep 1842821 = 345529) B345529
theorem B368327 : Blo 143792 368327 := bstep (se 1 (by rfl) ⟨276245, by rfl⟩ : syracuseStep 368327 = 552491) B552491
theorem B630623 : Blo 143792 630623 := bstep (se 1 (by rfl) ⟨472967, by rfl⟩ : syracuseStep 630623 = 945935) B945935
theorem B532595 : Blo 143792 532595 := bstep (se 1 (by rfl) ⟨399446, by rfl⟩ : syracuseStep 532595 = 798893) B798893
theorem B631145 : Blo 143792 631145 := bstep (se 2 (by rfl) ⟨236679, by rfl⟩ : syracuseStep 631145 = 473359) B473359
theorem B729809 : Blo 143792 729809 := bstep (se 2 (by rfl) ⟨273678, by rfl⟩ : syracuseStep 729809 = 547357) B547357
theorem B369481 : Blo 143792 369481 := bstep (se 2 (by rfl) ⟨138555, by rfl⟩ : syracuseStep 369481 = 277111) B277111
theorem B467831 : Blo 143792 467831 := bstep (se 1 (by rfl) ⟨350873, by rfl⟩ : syracuseStep 467831 = 701747) B701747
theorem B336953 : Blo 143792 336953 := bstep (se 2 (by rfl) ⟨126357, by rfl⟩ : syracuseStep 336953 = 252715) B252715
theorem B2466935 : Blo 143792 2466935 := bstep (se 1 (by rfl) ⟨1850201, by rfl⟩ : syracuseStep 2466935 = 3700403) B3700403
theorem B468139 : Blo 143792 468139 := bstep (se 1 (by rfl) ⟨351104, by rfl⟩ : syracuseStep 468139 = 702209) B702209
theorem B926923 : Blo 143792 926923 := bstep (se 1 (by rfl) ⟨695192, by rfl⟩ : syracuseStep 926923 = 1390385) B1390385
theorem B370615 : Blo 143792 370615 := bstep (se 1 (by rfl) ⟨277961, by rfl⟩ : syracuseStep 370615 = 555923) B555923
theorem B928279 : Blo 143792 928279 := bstep (se 1 (by rfl) ⟨696209, by rfl⟩ : syracuseStep 928279 = 1392419) B1392419
theorem B469651 : Blo 143792 469651 := bstep (se 1 (by rfl) ⟨352238, by rfl⟩ : syracuseStep 469651 = 704477) B704477
theorem B469921 : Blo 143792 469921 := bstep (se 2 (by rfl) ⟨176220, by rfl⟩ : syracuseStep 469921 = 352441) B352441
theorem B1092527 : Blo 143792 1092527 := bstep (se 1 (by rfl) ⟨819395, by rfl⟩ : syracuseStep 1092527 = 1638791) B1638791
theorem B732239 : Blo 143792 732239 := bstep (se 1 (by rfl) ⟨549179, by rfl⟩ : syracuseStep 732239 = 1098359) B1098359
theorem B372073 : Blo 143792 372073 := bstep (se 2 (by rfl) ⟨139527, by rfl⟩ : syracuseStep 372073 = 279055) B279055
theorem B274043 : Blo 143792 274043 := bstep (se 1 (by rfl) ⟨205532, by rfl⟩ : syracuseStep 274043 = 411065) B411065
theorem B372347 : Blo 143792 372347 := bstep (se 1 (by rfl) ⟨279260, by rfl⟩ : syracuseStep 372347 = 558521) B558521
theorem B732887 : Blo 143792 732887 := bstep (se 1 (by rfl) ⟨549665, by rfl⟩ : syracuseStep 732887 = 1099331) B1099331
theorem B2993885 : Blo 143792 2993885 := bstep (se 3 (by rfl) ⟨561353, by rfl⟩ : syracuseStep 2993885 = 1122707) B1122707
theorem B1421243 : Blo 143792 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B274529 : Blo 143792 274529 := bstep (se 2 (by rfl) ⟨102948, by rfl⟩ : syracuseStep 274529 = 205897) B205897
theorem B1585331 : Blo 143792 1585331 := bstep (se 1 (by rfl) ⟨1188998, by rfl⟩ : syracuseStep 1585331 = 2377997) B2377997
theorem B274681 : Blo 143792 274681 := bstep (se 2 (by rfl) ⟨103005, by rfl⟩ : syracuseStep 274681 = 206011) B206011
theorem B143815 : Blo 143792 143815 := bstep (se 1 (by rfl) ⟨107861, by rfl⟩ : syracuseStep 143815 = 215723) B215723
theorem B143835 : Blo 143792 143835 := bstep (se 1 (by rfl) ⟨107876, by rfl⟩ : syracuseStep 143835 = 215753) B215753
theorem B143911 : Blo 143792 143911 := bstep (se 1 (by rfl) ⟨107933, by rfl⟩ : syracuseStep 143911 = 215867) B215867
theorem B143951 : Blo 143792 143951 := bstep (se 1 (by rfl) ⟨107963, by rfl⟩ : syracuseStep 143951 = 215927) B215927
theorem B143967 : Blo 143792 143967 := bstep (se 1 (by rfl) ⟨107975, by rfl⟩ : syracuseStep 143967 = 215951) B215951
theorem B143995 : Blo 143792 143995 := bstep (se 1 (by rfl) ⟨107996, by rfl⟩ : syracuseStep 143995 = 215993) B215993
theorem B144047 : Blo 143792 144047 := bstep (se 1 (by rfl) ⟨108035, by rfl⟩ : syracuseStep 144047 = 216071) B216071
theorem B144071 : Blo 143792 144071 := bstep (se 1 (by rfl) ⟨108053, by rfl⟩ : syracuseStep 144071 = 216107) B216107
theorem B144091 : Blo 143792 144091 := bstep (se 1 (by rfl) ⟨108068, by rfl⟩ : syracuseStep 144091 = 216137) B216137
theorem B144167 : Blo 143792 144167 := bstep (se 1 (by rfl) ⟨108125, by rfl⟩ : syracuseStep 144167 = 216251) B216251
theorem B144207 : Blo 143792 144207 := bstep (se 1 (by rfl) ⟨108155, by rfl⟩ : syracuseStep 144207 = 216311) B216311
theorem B144223 : Blo 143792 144223 := bstep (se 1 (by rfl) ⟨108167, by rfl⟩ : syracuseStep 144223 = 216335) B216335
theorem B144251 : Blo 143792 144251 := bstep (se 1 (by rfl) ⟨108188, by rfl⟩ : syracuseStep 144251 = 216377) B216377
theorem B144303 : Blo 143792 144303 := bstep (se 1 (by rfl) ⟨108227, by rfl⟩ : syracuseStep 144303 = 216455) B216455
theorem B1258415 : Blo 143792 1258415 := bstep (se 1 (by rfl) ⟨943811, by rfl⟩ : syracuseStep 1258415 = 1887623) B1887623
theorem B144327 : Blo 143792 144327 := bstep (se 1 (by rfl) ⟨108245, by rfl⟩ : syracuseStep 144327 = 216491) B216491
theorem B144347 : Blo 143792 144347 := bstep (se 1 (by rfl) ⟨108260, by rfl⟩ : syracuseStep 144347 = 216521) B216521
theorem B504839 : Blo 143792 504839 := bstep (se 1 (by rfl) ⟨378629, by rfl⟩ : syracuseStep 504839 = 757259) B757259
theorem B144423 : Blo 143792 144423 := bstep (se 1 (by rfl) ⟨108317, by rfl⟩ : syracuseStep 144423 = 216635) B216635
theorem B144463 : Blo 143792 144463 := bstep (se 1 (by rfl) ⟨108347, by rfl⟩ : syracuseStep 144463 = 216695) B216695
theorem B144479 : Blo 143792 144479 := bstep (se 1 (by rfl) ⟨108359, by rfl⟩ : syracuseStep 144479 = 216719) B216719
theorem B144507 : Blo 143792 144507 := bstep (se 1 (by rfl) ⟨108380, by rfl⟩ : syracuseStep 144507 = 216761) B216761
theorem B210043 : Blo 143792 210043 := bstep (se 1 (by rfl) ⟨157532, by rfl⟩ : syracuseStep 210043 = 315065) B315065
theorem B144559 : Blo 143792 144559 := bstep (se 1 (by rfl) ⟨108419, by rfl⟩ : syracuseStep 144559 = 216839) B216839
theorem B144583 : Blo 143792 144583 := bstep (se 1 (by rfl) ⟨108437, by rfl⟩ : syracuseStep 144583 = 216875) B216875
theorem B144603 : Blo 143792 144603 := bstep (se 1 (by rfl) ⟨108452, by rfl⟩ : syracuseStep 144603 = 216905) B216905
theorem B144679 : Blo 143792 144679 := bstep (se 1 (by rfl) ⟨108509, by rfl⟩ : syracuseStep 144679 = 217019) B217019
theorem B144719 : Blo 143792 144719 := bstep (se 1 (by rfl) ⟨108539, by rfl⟩ : syracuseStep 144719 = 217079) B217079
theorem B144735 : Blo 143792 144735 := bstep (se 1 (by rfl) ⟨108551, by rfl⟩ : syracuseStep 144735 = 217103) B217103
theorem B210271 : Blo 143792 210271 := bstep (se 1 (by rfl) ⟨157703, by rfl⟩ : syracuseStep 210271 = 315407) B315407
theorem B144763 : Blo 143792 144763 := bstep (se 1 (by rfl) ⟨108572, by rfl⟩ : syracuseStep 144763 = 217145) B217145
theorem B1324451 : Blo 143792 1324451 := bstep (se 1 (by rfl) ⟨993338, by rfl⟩ : syracuseStep 1324451 = 1986677) B1986677
theorem B144815 : Blo 143792 144815 := bstep (se 1 (by rfl) ⟨108611, by rfl⟩ : syracuseStep 144815 = 217223) B217223
theorem B144839 : Blo 143792 144839 := bstep (se 1 (by rfl) ⟨108629, by rfl⟩ : syracuseStep 144839 = 217259) B217259
theorem B144859 : Blo 143792 144859 := bstep (se 1 (by rfl) ⟨108644, by rfl⟩ : syracuseStep 144859 = 217289) B217289
theorem B243209 : Blo 143792 243209 := bstep (se 2 (by rfl) ⟨91203, by rfl⟩ : syracuseStep 243209 = 182407) B182407
theorem B275987 : Blo 143792 275987 := bstep (se 1 (by rfl) ⟨206990, by rfl⟩ : syracuseStep 275987 = 413981) B413981
theorem B144935 : Blo 143792 144935 := bstep (se 1 (by rfl) ⟨108701, by rfl⟩ : syracuseStep 144935 = 217403) B217403
theorem B144975 : Blo 143792 144975 := bstep (se 1 (by rfl) ⟨108731, by rfl⟩ : syracuseStep 144975 = 217463) B217463
theorem B144991 : Blo 143792 144991 := bstep (se 1 (by rfl) ⟨108743, by rfl⟩ : syracuseStep 144991 = 217487) B217487
theorem B145019 : Blo 143792 145019 := bstep (se 1 (by rfl) ⟨108764, by rfl⟩ : syracuseStep 145019 = 217529) B217529
theorem B243371 : Blo 143792 243371 := bstep (se 1 (by rfl) ⟨182528, by rfl⟩ : syracuseStep 243371 = 365057) B365057
theorem B276139 : Blo 143792 276139 := bstep (se 1 (by rfl) ⟨207104, by rfl⟩ : syracuseStep 276139 = 414209) B414209
theorem B145071 : Blo 143792 145071 := bstep (se 1 (by rfl) ⟨108803, by rfl⟩ : syracuseStep 145071 = 217607) B217607
theorem B145095 : Blo 143792 145095 := bstep (se 1 (by rfl) ⟨108821, by rfl⟩ : syracuseStep 145095 = 217643) B217643
theorem B145115 : Blo 143792 145115 := bstep (se 1 (by rfl) ⟨108836, by rfl⟩ : syracuseStep 145115 = 217673) B217673
theorem B145191 : Blo 143792 145191 := bstep (se 1 (by rfl) ⟨108893, by rfl⟩ : syracuseStep 145191 = 217787) B217787
theorem B145231 : Blo 143792 145231 := bstep (se 1 (by rfl) ⟨108923, by rfl⟩ : syracuseStep 145231 = 217847) B217847
theorem B145247 : Blo 143792 145247 := bstep (se 1 (by rfl) ⟨108935, by rfl⟩ : syracuseStep 145247 = 217871) B217871
theorem B145275 : Blo 143792 145275 := bstep (se 1 (by rfl) ⟨108956, by rfl⟩ : syracuseStep 145275 = 217913) B217913
theorem B276367 : Blo 143792 276367 := bstep (se 1 (by rfl) ⟨207275, by rfl⟩ : syracuseStep 276367 = 414551) B414551
theorem B145327 : Blo 143792 145327 := bstep (se 1 (by rfl) ⟨108995, by rfl⟩ : syracuseStep 145327 = 217991) B217991
theorem B145351 : Blo 143792 145351 := bstep (se 1 (by rfl) ⟨109013, by rfl⟩ : syracuseStep 145351 = 218027) B218027
theorem B145371 : Blo 143792 145371 := bstep (se 1 (by rfl) ⟨109028, by rfl⟩ : syracuseStep 145371 = 218057) B218057
theorem B276443 : Blo 143792 276443 := bstep (se 1 (by rfl) ⟨207332, by rfl⟩ : syracuseStep 276443 = 414665) B414665
theorem B145447 : Blo 143792 145447 := bstep (se 1 (by rfl) ⟨109085, by rfl⟩ : syracuseStep 145447 = 218171) B218171
theorem B243769 : Blo 143792 243769 := bstep (se 2 (by rfl) ⟨91413, by rfl⟩ : syracuseStep 243769 = 182827) B182827
theorem B145487 : Blo 143792 145487 := bstep (se 1 (by rfl) ⟨109115, by rfl⟩ : syracuseStep 145487 = 218231) B218231
theorem B145503 : Blo 143792 145503 := bstep (se 1 (by rfl) ⟨109127, by rfl⟩ : syracuseStep 145503 = 218255) B218255
theorem B145531 : Blo 143792 145531 := bstep (se 1 (by rfl) ⟨109148, by rfl⟩ : syracuseStep 145531 = 218297) B218297
theorem B145583 : Blo 143792 145583 := bstep (se 1 (by rfl) ⟨109187, by rfl⟩ : syracuseStep 145583 = 218375) B218375
theorem B243911 : Blo 143792 243911 := bstep (se 1 (by rfl) ⟨182933, by rfl⟩ : syracuseStep 243911 = 365867) B365867
theorem B145607 : Blo 143792 145607 := bstep (se 1 (by rfl) ⟨109205, by rfl⟩ : syracuseStep 145607 = 218411) B218411
theorem B145627 : Blo 143792 145627 := bstep (se 1 (by rfl) ⟨109220, by rfl⟩ : syracuseStep 145627 = 218441) B218441
theorem B145703 : Blo 143792 145703 := bstep (se 1 (by rfl) ⟨109277, by rfl⟩ : syracuseStep 145703 = 218555) B218555
theorem B145743 : Blo 143792 145743 := bstep (se 1 (by rfl) ⟨109307, by rfl⟩ : syracuseStep 145743 = 218615) B218615
theorem B145759 : Blo 143792 145759 := bstep (se 1 (by rfl) ⟨109319, by rfl⟩ : syracuseStep 145759 = 218639) B218639
theorem B244073 : Blo 143792 244073 := bstep (se 2 (by rfl) ⟨91527, by rfl⟩ : syracuseStep 244073 = 183055) B183055
theorem B145787 : Blo 143792 145787 := bstep (se 1 (by rfl) ⟨109340, by rfl⟩ : syracuseStep 145787 = 218681) B218681
theorem B145839 : Blo 143792 145839 := bstep (se 1 (by rfl) ⟨109379, by rfl⟩ : syracuseStep 145839 = 218759) B218759
theorem B145863 : Blo 143792 145863 := bstep (se 1 (by rfl) ⟨109397, by rfl⟩ : syracuseStep 145863 = 218795) B218795
theorem B145883 : Blo 143792 145883 := bstep (se 1 (by rfl) ⟨109412, by rfl⟩ : syracuseStep 145883 = 218825) B218825
theorem B6404629 : Blo 143792 6404629 := bstep (se 6 (by rfl) ⟨150108, by rfl⟩ : syracuseStep 6404629 = 300217) B300217
theorem B145959 : Blo 143792 145959 := bstep (se 1 (by rfl) ⟨109469, by rfl⟩ : syracuseStep 145959 = 218939) B218939
theorem B735803 : Blo 143792 735803 := bstep (se 1 (by rfl) ⟨551852, by rfl⟩ : syracuseStep 735803 = 1103705) B1103705
theorem B145999 : Blo 143792 145999 := bstep (se 1 (by rfl) ⟨109499, by rfl⟩ : syracuseStep 145999 = 218999) B218999
theorem B146015 : Blo 143792 146015 := bstep (se 1 (by rfl) ⟨109511, by rfl⟩ : syracuseStep 146015 = 219023) B219023
theorem B146043 : Blo 143792 146043 := bstep (se 1 (by rfl) ⟨109532, by rfl⟩ : syracuseStep 146043 = 219065) B219065
theorem B146095 : Blo 143792 146095 := bstep (se 1 (by rfl) ⟨109571, by rfl⟩ : syracuseStep 146095 = 219143) B219143
theorem B7518905 : Blo 143792 7518905 := bstep (se 2 (by rfl) ⟨2819589, by rfl⟩ : syracuseStep 7518905 = 5639179) B5639179
theorem B146119 : Blo 143792 146119 := bstep (se 1 (by rfl) ⟨109589, by rfl⟩ : syracuseStep 146119 = 219179) B219179
theorem B146139 : Blo 143792 146139 := bstep (se 1 (by rfl) ⟨109604, by rfl⟩ : syracuseStep 146139 = 219209) B219209
theorem B244471 : Blo 143792 244471 := bstep (se 1 (by rfl) ⟨183353, by rfl⟩ : syracuseStep 244471 = 366707) B366707
theorem B146215 : Blo 143792 146215 := bstep (se 1 (by rfl) ⟨109661, by rfl⟩ : syracuseStep 146215 = 219323) B219323
theorem B146255 : Blo 143792 146255 := bstep (se 1 (by rfl) ⟨109691, by rfl⟩ : syracuseStep 146255 = 219383) B219383
theorem B146271 : Blo 143792 146271 := bstep (se 1 (by rfl) ⟨109703, by rfl⟩ : syracuseStep 146271 = 219407) B219407
theorem B146299 : Blo 143792 146299 := bstep (se 1 (by rfl) ⟨109724, by rfl⟩ : syracuseStep 146299 = 219449) B219449
theorem B146351 : Blo 143792 146351 := bstep (se 1 (by rfl) ⟨109763, by rfl⟩ : syracuseStep 146351 = 219527) B219527
theorem B244667 : Blo 143792 244667 := bstep (se 1 (by rfl) ⟨183500, by rfl⟩ : syracuseStep 244667 = 367001) B367001
theorem B146375 : Blo 143792 146375 := bstep (se 1 (by rfl) ⟨109781, by rfl⟩ : syracuseStep 146375 = 219563) B219563
theorem B146395 : Blo 143792 146395 := bstep (se 1 (by rfl) ⟨109796, by rfl⟩ : syracuseStep 146395 = 219593) B219593
theorem B244775 : Blo 143792 244775 := bstep (se 1 (by rfl) ⟨183581, by rfl⟩ : syracuseStep 244775 = 367163) B367163
theorem B146471 : Blo 143792 146471 := bstep (se 1 (by rfl) ⟨109853, by rfl⟩ : syracuseStep 146471 = 219707) B219707
theorem B146511 : Blo 143792 146511 := bstep (se 1 (by rfl) ⟨109883, by rfl⟩ : syracuseStep 146511 = 219767) B219767
theorem B146527 : Blo 143792 146527 := bstep (se 1 (by rfl) ⟨109895, by rfl⟩ : syracuseStep 146527 = 219791) B219791
theorem B146555 : Blo 143792 146555 := bstep (se 1 (by rfl) ⟨109916, by rfl⟩ : syracuseStep 146555 = 219833) B219833
theorem B146607 : Blo 143792 146607 := bstep (se 1 (by rfl) ⟨109955, by rfl⟩ : syracuseStep 146607 = 219911) B219911
theorem B736451 : Blo 143792 736451 := bstep (se 1 (by rfl) ⟨552338, by rfl⟩ : syracuseStep 736451 = 1104677) B1104677
theorem B146631 : Blo 143792 146631 := bstep (se 1 (by rfl) ⟨109973, by rfl⟩ : syracuseStep 146631 = 219947) B219947
theorem B146651 : Blo 143792 146651 := bstep (se 1 (by rfl) ⟨109988, by rfl⟩ : syracuseStep 146651 = 219977) B219977
theorem B146727 : Blo 143792 146727 := bstep (se 1 (by rfl) ⟨110045, by rfl⟩ : syracuseStep 146727 = 220091) B220091
theorem B245065 : Blo 143792 245065 := bstep (se 2 (by rfl) ⟨91899, by rfl⟩ : syracuseStep 245065 = 183799) B183799
theorem B146767 : Blo 143792 146767 := bstep (se 1 (by rfl) ⟨110075, by rfl⟩ : syracuseStep 146767 = 220151) B220151
theorem B146783 : Blo 143792 146783 := bstep (se 1 (by rfl) ⟨110087, by rfl⟩ : syracuseStep 146783 = 220175) B220175
theorem B245099 : Blo 143792 245099 := bstep (se 1 (by rfl) ⟨183824, by rfl⟩ : syracuseStep 245099 = 367649) B367649
theorem B146811 : Blo 143792 146811 := bstep (se 1 (by rfl) ⟨110108, by rfl⟩ : syracuseStep 146811 = 220217) B220217
theorem B146863 : Blo 143792 146863 := bstep (se 1 (by rfl) ⟨110147, by rfl⟩ : syracuseStep 146863 = 220295) B220295
theorem B146887 : Blo 143792 146887 := bstep (se 1 (by rfl) ⟨110165, by rfl⟩ : syracuseStep 146887 = 220331) B220331
theorem B146907 : Blo 143792 146907 := bstep (se 1 (by rfl) ⟨110180, by rfl⟩ : syracuseStep 146907 = 220361) B220361
theorem B146983 : Blo 143792 146983 := bstep (se 1 (by rfl) ⟨110237, by rfl⟩ : syracuseStep 146983 = 220475) B220475
theorem B147023 : Blo 143792 147023 := bstep (se 1 (by rfl) ⟨110267, by rfl⟩ : syracuseStep 147023 = 220535) B220535
theorem B147039 : Blo 143792 147039 := bstep (se 1 (by rfl) ⟨110279, by rfl⟩ : syracuseStep 147039 = 220559) B220559
theorem B704123 : Blo 143792 704123 := bstep (se 1 (by rfl) ⟨528092, by rfl⟩ : syracuseStep 704123 = 1056185) B1056185
theorem B147067 : Blo 143792 147067 := bstep (se 1 (by rfl) ⟨110300, by rfl⟩ : syracuseStep 147067 = 220601) B220601
theorem B147119 : Blo 143792 147119 := bstep (se 1 (by rfl) ⟨110339, by rfl⟩ : syracuseStep 147119 = 220679) B220679
theorem B1982141 : Blo 143792 1982141 := bstep (se 3 (by rfl) ⟨371651, by rfl⟩ : syracuseStep 1982141 = 743303) B743303
theorem B147143 : Blo 143792 147143 := bstep (se 1 (by rfl) ⟨110357, by rfl⟩ : syracuseStep 147143 = 220715) B220715
theorem B147163 : Blo 143792 147163 := bstep (se 1 (by rfl) ⟨110372, by rfl⟩ : syracuseStep 147163 = 220745) B220745
theorem B245497 : Blo 143792 245497 := bstep (se 2 (by rfl) ⟨92061, by rfl⟩ : syracuseStep 245497 = 184123) B184123
theorem B311033 : Blo 143792 311033 := bstep (se 2 (by rfl) ⟨116637, by rfl⟩ : syracuseStep 311033 = 233275) B233275
theorem B147239 : Blo 143792 147239 := bstep (se 1 (by rfl) ⟨110429, by rfl⟩ : syracuseStep 147239 = 220859) B220859
theorem B147279 : Blo 143792 147279 := bstep (se 1 (by rfl) ⟨110459, by rfl⟩ : syracuseStep 147279 = 220919) B220919
theorem B147295 : Blo 143792 147295 := bstep (se 1 (by rfl) ⟨110471, by rfl⟩ : syracuseStep 147295 = 220943) B220943
theorem B147323 : Blo 143792 147323 := bstep (se 1 (by rfl) ⟨110492, by rfl⟩ : syracuseStep 147323 = 220985) B220985
theorem B933767 : Blo 143792 933767 := bstep (se 1 (by rfl) ⟨700325, by rfl⟩ : syracuseStep 933767 = 1400651) B1400651
theorem B147375 : Blo 143792 147375 := bstep (se 1 (by rfl) ⟨110531, by rfl⟩ : syracuseStep 147375 = 221063) B221063
theorem B147399 : Blo 143792 147399 := bstep (se 1 (by rfl) ⟨110549, by rfl⟩ : syracuseStep 147399 = 221099) B221099
theorem B147419 : Blo 143792 147419 := bstep (se 1 (by rfl) ⟨110564, by rfl⟩ : syracuseStep 147419 = 221129) B221129
theorem B409607 : Blo 143792 409607 := bstep (se 1 (by rfl) ⟨307205, by rfl⟩ : syracuseStep 409607 = 614411) B614411
theorem B245767 : Blo 143792 245767 := bstep (se 1 (by rfl) ⟨184325, by rfl⟩ : syracuseStep 245767 = 368651) B368651
theorem B147495 : Blo 143792 147495 := bstep (se 1 (by rfl) ⟨110621, by rfl⟩ : syracuseStep 147495 = 221243) B221243
theorem B147535 : Blo 143792 147535 := bstep (se 1 (by rfl) ⟨110651, by rfl⟩ : syracuseStep 147535 = 221303) B221303
theorem B147551 : Blo 143792 147551 := bstep (se 1 (by rfl) ⟨110663, by rfl⟩ : syracuseStep 147551 = 221327) B221327
theorem B147579 : Blo 143792 147579 := bstep (se 1 (by rfl) ⟨110684, by rfl⟩ : syracuseStep 147579 = 221369) B221369
theorem B147631 : Blo 143792 147631 := bstep (se 1 (by rfl) ⟨110723, by rfl⟩ : syracuseStep 147631 = 221447) B221447
theorem B147655 : Blo 143792 147655 := bstep (se 1 (by rfl) ⟨110741, by rfl⟩ : syracuseStep 147655 = 221483) B221483
theorem B147675 : Blo 143792 147675 := bstep (se 1 (by rfl) ⟨110756, by rfl⟩ : syracuseStep 147675 = 221513) B221513
theorem B147751 : Blo 143792 147751 := bstep (se 1 (by rfl) ⟨110813, by rfl⟩ : syracuseStep 147751 = 221627) B221627
theorem B147791 : Blo 143792 147791 := bstep (se 1 (by rfl) ⟨110843, by rfl⟩ : syracuseStep 147791 = 221687) B221687
theorem B409961 : Blo 143792 409961 := bstep (se 2 (by rfl) ⟨153735, by rfl⟩ : syracuseStep 409961 = 307471) B307471
theorem B246199 : Blo 143792 246199 := bstep (se 1 (by rfl) ⟨184649, by rfl⟩ : syracuseStep 246199 = 369299) B369299
theorem B246395 : Blo 143792 246395 := bstep (se 1 (by rfl) ⟨184796, by rfl⟩ : syracuseStep 246395 = 369593) B369593
theorem B312007 : Blo 143792 312007 := bstep (se 1 (by rfl) ⟨234005, by rfl⟩ : syracuseStep 312007 = 468011) B468011
theorem B1557265 : Blo 143792 1557265 := bstep (se 2 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 1557265 = 1167949) B1167949
theorem B836527 : Blo 143792 836527 := bstep (se 1 (by rfl) ⟨627395, by rfl⟩ : syracuseStep 836527 = 1254791) B1254791
theorem B246793 : Blo 143792 246793 := bstep (se 2 (by rfl) ⟨92547, by rfl⟩ : syracuseStep 246793 = 185095) B185095
theorem B246955 : Blo 143792 246955 := bstep (se 1 (by rfl) ⟨185216, by rfl⟩ : syracuseStep 246955 = 370433) B370433
theorem B247259 : Blo 143792 247259 := bstep (se 1 (by rfl) ⟨185444, by rfl⟩ : syracuseStep 247259 = 370889) B370889
theorem B280027 : Blo 143792 280027 := bstep (se 1 (by rfl) ⟨210020, by rfl⟩ : syracuseStep 280027 = 420041) B420041
theorem B280073 : Blo 143792 280073 := bstep (se 2 (by rfl) ⟨105027, by rfl⟩ : syracuseStep 280073 = 210055) B210055
theorem B345799 : Blo 143792 345799 := bstep (se 1 (by rfl) ⟨259349, by rfl⟩ : syracuseStep 345799 = 518699) B518699
theorem B247495 : Blo 143792 247495 := bstep (se 1 (by rfl) ⟨185621, by rfl⟩ : syracuseStep 247495 = 371243) B371243
theorem B1853279 : Blo 143792 1853279 := bstep (se 1 (by rfl) ⟨1389959, by rfl⟩ : syracuseStep 1853279 = 2779919) B2779919
theorem B280415 : Blo 143792 280415 := bstep (se 1 (by rfl) ⟨210311, by rfl⟩ : syracuseStep 280415 = 420623) B420623
theorem B247657 : Blo 143792 247657 := bstep (se 2 (by rfl) ⟨92871, by rfl⟩ : syracuseStep 247657 = 185743) B185743
theorem B837485 : Blo 143792 837485 := bstep (se 3 (by rfl) ⟨157028, by rfl⟩ : syracuseStep 837485 = 314057) B314057
theorem B182351 : Blo 143792 182351 := bstep (se 1 (by rfl) ⟨136763, by rfl⟩ : syracuseStep 182351 = 273527) B273527
theorem B1427557 : Blo 143792 1427557 := bstep (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) B267667
theorem B248251 : Blo 143792 248251 := bstep (se 1 (by rfl) ⟨186188, by rfl⟩ : syracuseStep 248251 = 372377) B372377
theorem B510451 : Blo 143792 510451 := bstep (se 1 (by rfl) ⟨382838, by rfl⟩ : syracuseStep 510451 = 765677) B765677
theorem B936481 : Blo 143792 936481 := bstep (se 2 (by rfl) ⟨351180, by rfl⟩ : syracuseStep 936481 = 702361) B702361
theorem B313895 : Blo 143792 313895 := bstep (se 1 (by rfl) ⟨235421, by rfl⟩ : syracuseStep 313895 = 470843) B470843
theorem B248359 : Blo 143792 248359 := bstep (se 1 (by rfl) ⟨186269, by rfl⟩ : syracuseStep 248359 = 372539) B372539
theorem B215801 : Blo 143792 215801 := bstep (se 2 (by rfl) ⟨80925, by rfl⟩ : syracuseStep 215801 = 161851) B161851
theorem B215903 : Blo 143792 215903 := bstep (se 1 (by rfl) ⟨161927, by rfl⟩ : syracuseStep 215903 = 323855) B323855
theorem B215915 : Blo 143792 215915 := bstep (se 1 (by rfl) ⟨161936, by rfl⟩ : syracuseStep 215915 = 323873) B323873
theorem B412523 : Blo 143792 412523 := bstep (se 1 (by rfl) ⟨309392, by rfl⟩ : syracuseStep 412523 = 618785) B618785
theorem B248683 : Blo 143792 248683 := bstep (se 1 (by rfl) ⟨186512, by rfl⟩ : syracuseStep 248683 = 373025) B373025
theorem B1657745 : Blo 143792 1657745 := bstep (se 2 (by rfl) ⟨621654, by rfl⟩ : syracuseStep 1657745 = 1243309) B1243309
theorem B216143 : Blo 143792 216143 := bstep (se 1 (by rfl) ⟨162107, by rfl⟩ : syracuseStep 216143 = 324215) B324215
theorem B412751 : Blo 143792 412751 := bstep (se 1 (by rfl) ⟨309563, by rfl⟩ : syracuseStep 412751 = 619127) B619127
theorem B216263 : Blo 143792 216263 := bstep (se 1 (by rfl) ⟨162197, by rfl⟩ : syracuseStep 216263 = 324395) B324395
theorem B183647 : Blo 143792 183647 := bstep (se 1 (by rfl) ⟨137735, by rfl⟩ : syracuseStep 183647 = 275471) B275471
theorem B216425 : Blo 143792 216425 := bstep (se 2 (by rfl) ⟨81159, by rfl⟩ : syracuseStep 216425 = 162319) B162319
theorem B216503 : Blo 143792 216503 := bstep (se 1 (by rfl) ⟨162377, by rfl⟩ : syracuseStep 216503 = 324755) B324755
theorem B216539 : Blo 143792 216539 := bstep (se 1 (by rfl) ⟨162404, by rfl⟩ : syracuseStep 216539 = 324809) B324809
theorem B1101275 : Blo 143792 1101275 := bstep (se 1 (by rfl) ⟨825956, by rfl⟩ : syracuseStep 1101275 = 1651913) B1651913
theorem B740987 : Blo 143792 740987 := bstep (se 1 (by rfl) ⟨555740, by rfl⟩ : syracuseStep 740987 = 1111481) B1111481
theorem B217007 : Blo 143792 217007 := bstep (se 1 (by rfl) ⟨162755, by rfl⟩ : syracuseStep 217007 = 325511) B325511
theorem B1101761 : Blo 143792 1101761 := bstep (se 2 (by rfl) ⟨413160, by rfl⟩ : syracuseStep 1101761 = 826321) B826321
theorem B217097 : Blo 143792 217097 := bstep (se 2 (by rfl) ⟨81411, by rfl⟩ : syracuseStep 217097 = 162823) B162823
theorem B3821579 : Blo 143792 3821579 := bstep (se 1 (by rfl) ⟨2866184, by rfl⟩ : syracuseStep 3821579 = 5732369) B5732369
theorem B839717 : Blo 143792 839717 := bstep (se 4 (by rfl) ⟨78723, by rfl⟩ : syracuseStep 839717 = 157447) B157447
theorem B217127 : Blo 143792 217127 := bstep (se 1 (by rfl) ⟨162845, by rfl⟩ : syracuseStep 217127 = 325691) B325691
theorem B8605777 : Blo 143792 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B217211 : Blo 143792 217211 := bstep (se 1 (by rfl) ⟨162908, by rfl⟩ : syracuseStep 217211 = 325817) B325817
theorem B217337 : Blo 143792 217337 := bstep (se 2 (by rfl) ⟨81501, by rfl⟩ : syracuseStep 217337 = 163003) B163003
theorem B217439 : Blo 143792 217439 := bstep (se 1 (by rfl) ⟨163079, by rfl⟩ : syracuseStep 217439 = 326159) B326159
theorem B217451 : Blo 143792 217451 := bstep (se 1 (by rfl) ⟨163088, by rfl⟩ : syracuseStep 217451 = 326177) B326177
theorem B217679 : Blo 143792 217679 := bstep (se 1 (by rfl) ⟨163259, by rfl⟩ : syracuseStep 217679 = 326519) B326519
theorem B217799 : Blo 143792 217799 := bstep (se 1 (by rfl) ⟨163349, by rfl⟩ : syracuseStep 217799 = 326699) B326699
theorem B840401 : Blo 143792 840401 := bstep (se 2 (by rfl) ⟨315150, by rfl⟩ : syracuseStep 840401 = 630301) B630301
theorem B217961 : Blo 143792 217961 := bstep (se 2 (by rfl) ⟨81735, by rfl⟩ : syracuseStep 217961 = 163471) B163471
theorem B218039 : Blo 143792 218039 := bstep (se 1 (by rfl) ⟨163529, by rfl⟩ : syracuseStep 218039 = 327059) B327059
theorem B218075 : Blo 143792 218075 := bstep (se 1 (by rfl) ⟨163556, by rfl⟩ : syracuseStep 218075 = 327113) B327113
theorem B283819 : Blo 143792 283819 := bstep (se 1 (by rfl) ⟨212864, by rfl⟩ : syracuseStep 283819 = 425729) B425729
theorem B1103219 : Blo 143792 1103219 := bstep (se 1 (by rfl) ⟨827414, by rfl⟩ : syracuseStep 1103219 = 1654829) B1654829
theorem B546173 : Blo 143792 546173 := bstep (se 3 (by rfl) ⟨102407, by rfl⟩ : syracuseStep 546173 = 204815) B204815
theorem B218543 : Blo 143792 218543 := bstep (se 1 (by rfl) ⟨163907, by rfl⟩ : syracuseStep 218543 = 327815) B327815
theorem B218633 : Blo 143792 218633 := bstep (se 2 (by rfl) ⟨81987, by rfl⟩ : syracuseStep 218633 = 163975) B163975
theorem B218663 : Blo 143792 218663 := bstep (se 1 (by rfl) ⟨163997, by rfl⟩ : syracuseStep 218663 = 327995) B327995
theorem B218747 : Blo 143792 218747 := bstep (se 1 (by rfl) ⟨164060, by rfl⟩ : syracuseStep 218747 = 328121) B328121
theorem B1070725 : Blo 143792 1070725 := bstep (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) B200761
theorem B1037971 : Blo 143792 1037971 := bstep (se 1 (by rfl) ⟨778478, by rfl⟩ : syracuseStep 1037971 = 1556957) B1556957
theorem B218873 : Blo 143792 218873 := bstep (se 2 (by rfl) ⟨82077, by rfl⟩ : syracuseStep 218873 = 164155) B164155
theorem B218975 : Blo 143792 218975 := bstep (se 1 (by rfl) ⟨164231, by rfl⟩ : syracuseStep 218975 = 328463) B328463
theorem B218987 : Blo 143792 218987 := bstep (se 1 (by rfl) ⟨164240, by rfl⟩ : syracuseStep 218987 = 328481) B328481
theorem B186295 : Blo 143792 186295 := bstep (se 1 (by rfl) ⟨139721, by rfl⟩ : syracuseStep 186295 = 279443) B279443
theorem B3790795 : Blo 143792 3790795 := bstep (se 1 (by rfl) ⟨2843096, by rfl⟩ : syracuseStep 3790795 = 5686193) B5686193
theorem B415751 : Blo 143792 415751 := bstep (se 1 (by rfl) ⟨311813, by rfl⟩ : syracuseStep 415751 = 623627) B623627
theorem B219215 : Blo 143792 219215 := bstep (se 1 (by rfl) ⟨164411, by rfl⟩ : syracuseStep 219215 = 328823) B328823
theorem B219335 : Blo 143792 219335 := bstep (se 1 (by rfl) ⟨164501, by rfl⟩ : syracuseStep 219335 = 329003) B329003
theorem B743741 : Blo 143792 743741 := bstep (se 3 (by rfl) ⟨139451, by rfl⟩ : syracuseStep 743741 = 278903) B278903
theorem B219497 : Blo 143792 219497 := bstep (se 2 (by rfl) ⟨82311, by rfl⟩ : syracuseStep 219497 = 164623) B164623
theorem B219575 : Blo 143792 219575 := bstep (se 1 (by rfl) ⟨164681, by rfl⟩ : syracuseStep 219575 = 329363) B329363
theorem B219611 : Blo 143792 219611 := bstep (se 1 (by rfl) ⟨164708, by rfl⟩ : syracuseStep 219611 = 329417) B329417
theorem B1333793 : Blo 143792 1333793 := bstep (se 2 (by rfl) ⟨500172, by rfl⟩ : syracuseStep 1333793 = 1000345) B1000345
theorem B154235 : Blo 143792 154235 := bstep (se 1 (by rfl) ⟨115676, by rfl⟩ : syracuseStep 154235 = 231353) B231353
theorem B220079 : Blo 143792 220079 := bstep (se 1 (by rfl) ⟨165059, by rfl⟩ : syracuseStep 220079 = 330119) B330119
theorem B220169 : Blo 143792 220169 := bstep (se 2 (by rfl) ⟨82563, by rfl⟩ : syracuseStep 220169 = 165127) B165127
theorem B220199 : Blo 143792 220199 := bstep (se 1 (by rfl) ⟨165149, by rfl⟩ : syracuseStep 220199 = 330299) B330299
theorem B220283 : Blo 143792 220283 := bstep (se 1 (by rfl) ⟨165212, by rfl⟩ : syracuseStep 220283 = 330425) B330425
theorem B220409 : Blo 143792 220409 := bstep (se 2 (by rfl) ⟨82653, by rfl⟩ : syracuseStep 220409 = 165307) B165307
theorem B1891619 : Blo 143792 1891619 := bstep (se 1 (by rfl) ⟨1418714, by rfl⟩ : syracuseStep 1891619 = 2837429) B2837429
theorem B220511 : Blo 143792 220511 := bstep (se 1 (by rfl) ⟨165383, by rfl⟩ : syracuseStep 220511 = 330767) B330767
theorem B220523 : Blo 143792 220523 := bstep (se 1 (by rfl) ⟨165392, by rfl⟩ : syracuseStep 220523 = 330785) B330785
theorem B1039817 : Blo 143792 1039817 := bstep (se 2 (by rfl) ⟨389931, by rfl⟩ : syracuseStep 1039817 = 779863) B779863
theorem B548315 : Blo 143792 548315 := bstep (se 1 (by rfl) ⟨411236, by rfl⟩ : syracuseStep 548315 = 822473) B822473
theorem B220751 : Blo 143792 220751 := bstep (se 1 (by rfl) ⟨165563, by rfl⟩ : syracuseStep 220751 = 331127) B331127
theorem B876179 : Blo 143792 876179 := bstep (se 1 (by rfl) ⟨657134, by rfl⟩ : syracuseStep 876179 = 1314269) B1314269
theorem B220871 : Blo 143792 220871 := bstep (se 1 (by rfl) ⟨165653, by rfl⟩ : syracuseStep 220871 = 331307) B331307
theorem B221033 : Blo 143792 221033 := bstep (se 2 (by rfl) ⟨82887, by rfl⟩ : syracuseStep 221033 = 165775) B165775
theorem B221111 : Blo 143792 221111 := bstep (se 1 (by rfl) ⟨165833, by rfl⟩ : syracuseStep 221111 = 331667) B331667
theorem B221147 : Blo 143792 221147 := bstep (se 1 (by rfl) ⟨165860, by rfl⟩ : syracuseStep 221147 = 331721) B331721
theorem B155687 : Blo 143792 155687 := bstep (se 1 (by rfl) ⟨116765, by rfl⟩ : syracuseStep 155687 = 233531) B233531
theorem B221615 : Blo 143792 221615 := bstep (se 1 (by rfl) ⟨166211, by rfl⟩ : syracuseStep 221615 = 332423) B332423
theorem B746009 : Blo 143792 746009 := bstep (se 2 (by rfl) ⟨279753, by rfl⟩ : syracuseStep 746009 = 559507) B559507
theorem B549575 : Blo 143792 549575 := bstep (se 1 (by rfl) ⟨412181, by rfl⟩ : syracuseStep 549575 = 824363) B824363
theorem B910529 : Blo 143792 910529 := bstep (se 2 (by rfl) ⟨341448, by rfl⟩ : syracuseStep 910529 = 682897) B682897
theorem B353641 : Blo 143792 353641 := bstep (se 2 (by rfl) ⟨132615, by rfl⟩ : syracuseStep 353641 = 265231) B265231
theorem B550273 : Blo 143792 550273 := bstep (se 2 (by rfl) ⟨206352, by rfl⟩ : syracuseStep 550273 = 412705) B412705
theorem B550547 : Blo 143792 550547 := bstep (se 1 (by rfl) ⟨412910, by rfl⟩ : syracuseStep 550547 = 825821) B825821
theorem B4025123 : Blo 143792 4025123 := bstep (se 1 (by rfl) ⟨3018842, by rfl⟩ : syracuseStep 4025123 = 6037685) B6037685
theorem B224105 : Blo 143792 224105 := bstep (se 2 (by rfl) ⟨84039, by rfl⟩ : syracuseStep 224105 = 168079) B168079
theorem B781163 : Blo 143792 781163 := bstep (se 1 (by rfl) ⟨585872, by rfl⟩ : syracuseStep 781163 = 1171745) B1171745
theorem B486647 : Blo 143792 486647 := bstep (se 1 (by rfl) ⟨364985, by rfl⟩ : syracuseStep 486647 = 729971) B729971
theorem B552203 : Blo 143792 552203 := bstep (se 1 (by rfl) ⟨414152, by rfl⟩ : syracuseStep 552203 = 828305) B828305
theorem B1109285 : Blo 143792 1109285 := bstep (se 4 (by rfl) ⟨103995, by rfl⟩ : syracuseStep 1109285 = 207991) B207991
theorem B1174985 : Blo 143792 1174985 := bstep (se 2 (by rfl) ⟨440619, by rfl⟩ : syracuseStep 1174985 = 881239) B881239
theorem B19131875 : Blo 143792 19131875 := bstep (se 1 (by rfl) ⟨14348906, by rfl⟩ : syracuseStep 19131875 = 28697813) B28697813
theorem B486971 : Blo 143792 486971 := bstep (se 1 (by rfl) ⟨365228, by rfl⟩ : syracuseStep 486971 = 730457) B730457
theorem B945863 : Blo 143792 945863 := bstep (se 1 (by rfl) ⟨709397, by rfl⟩ : syracuseStep 945863 = 1418795) B1418795
theorem B487241 : Blo 143792 487241 := bstep (se 2 (by rfl) ⟨182715, by rfl⟩ : syracuseStep 487241 = 365431) B365431
theorem B1110023 : Blo 143792 1110023 := bstep (se 1 (by rfl) ⟨832517, by rfl⟩ : syracuseStep 1110023 = 1665035) B1665035
theorem B618511 : Blo 143792 618511 := bstep (se 1 (by rfl) ⟨463883, by rfl⟩ : syracuseStep 618511 = 927767) B927767
theorem B323603 : Blo 143792 323603 := bstep (se 1 (by rfl) ⟨242702, by rfl⟩ : syracuseStep 323603 = 485405) B485405
theorem B323945 : Blo 143792 323945 := bstep (se 2 (by rfl) ⟨121479, by rfl⟩ : syracuseStep 323945 = 242959) B242959
theorem B1110509 : Blo 143792 1110509 := bstep (se 3 (by rfl) ⟨208220, by rfl⟩ : syracuseStep 1110509 = 416441) B416441
theorem B553661 : Blo 143792 553661 := bstep (se 3 (by rfl) ⟨103811, by rfl⟩ : syracuseStep 553661 = 207623) B207623
theorem B946889 : Blo 143792 946889 := bstep (se 2 (by rfl) ⟨355083, by rfl⟩ : syracuseStep 946889 = 710167) B710167
theorem B488375 : Blo 143792 488375 := bstep (se 1 (by rfl) ⟨366281, by rfl⟩ : syracuseStep 488375 = 732563) B732563
theorem B324539 : Blo 143792 324539 := bstep (se 1 (by rfl) ⟨243404, by rfl⟩ : syracuseStep 324539 = 486809) B486809
theorem B2814977 : Blo 143792 2814977 := bstep (se 2 (by rfl) ⟨1055616, by rfl⟩ : syracuseStep 2814977 = 2111233) B2111233
theorem B324665 : Blo 143792 324665 := bstep (se 2 (by rfl) ⟨121749, by rfl⟩ : syracuseStep 324665 = 243499) B243499
theorem B1406105 : Blo 143792 1406105 := bstep (se 2 (by rfl) ⟨527289, by rfl⟩ : syracuseStep 1406105 = 1054579) B1054579
theorem B259321 : Blo 143792 259321 := bstep (se 2 (by rfl) ⟨97245, by rfl⟩ : syracuseStep 259321 = 194491) B194491
theorem B1176869 : Blo 143792 1176869 := bstep (se 4 (by rfl) ⟨110331, by rfl⟩ : syracuseStep 1176869 = 220663) B220663
theorem B325007 : Blo 143792 325007 := bstep (se 1 (by rfl) ⟨243755, by rfl⟩ : syracuseStep 325007 = 487511) B487511
theorem B1340837 : Blo 143792 1340837 := bstep (se 4 (by rfl) ⟨125703, by rfl⟩ : syracuseStep 1340837 = 251407) B251407
theorem B488969 : Blo 143792 488969 := bstep (se 2 (by rfl) ⟨183363, by rfl⟩ : syracuseStep 488969 = 366727) B366727
theorem B259681 : Blo 143792 259681 := bstep (se 2 (by rfl) ⟨97380, by rfl⟩ : syracuseStep 259681 = 194761) B194761
theorem B2815669 : Blo 143792 2815669 := bstep (se 5 (by rfl) ⟨131984, by rfl⟩ : syracuseStep 2815669 = 263969) B263969
theorem B325331 : Blo 143792 325331 := bstep (se 1 (by rfl) ⟨243998, by rfl⟩ : syracuseStep 325331 = 487997) B487997
theorem B1668923 : Blo 143792 1668923 := bstep (se 1 (by rfl) ⟨1251692, by rfl⟩ : syracuseStep 1668923 = 2503385) B2503385
theorem B751427 : Blo 143792 751427 := bstep (se 1 (by rfl) ⟨563570, by rfl⟩ : syracuseStep 751427 = 1127141) B1127141
theorem B194599 : Blo 143792 194599 := bstep (se 1 (by rfl) ⟨145949, by rfl⟩ : syracuseStep 194599 = 291899) B291899
theorem B489833 : Blo 143792 489833 := bstep (se 2 (by rfl) ⟨183687, by rfl⟩ : syracuseStep 489833 = 367375) B367375
theorem B1112453 : Blo 143792 1112453 := bstep (se 4 (by rfl) ⟨104292, by rfl⟩ : syracuseStep 1112453 = 208585) B208585
theorem B555407 : Blo 143792 555407 := bstep (se 1 (by rfl) ⟨416555, by rfl⟩ : syracuseStep 555407 = 833111) B833111
theorem B162427 : Blo 143792 162427 := bstep (se 1 (by rfl) ⟨121820, by rfl⟩ : syracuseStep 162427 = 243641) B243641
theorem B326267 : Blo 143792 326267 := bstep (se 1 (by rfl) ⟨244700, by rfl⟩ : syracuseStep 326267 = 489401) B489401
theorem B326393 : Blo 143792 326393 := bstep (se 2 (by rfl) ⟨122397, by rfl⟩ : syracuseStep 326393 = 244795) B244795
theorem B1112939 : Blo 143792 1112939 := bstep (se 1 (by rfl) ⟨834704, by rfl⟩ : syracuseStep 1112939 = 1669409) B1669409
theorem B490427 : Blo 143792 490427 := bstep (se 1 (by rfl) ⟨367820, by rfl⟩ : syracuseStep 490427 = 735641) B735641
theorem B326663 : Blo 143792 326663 := bstep (se 1 (by rfl) ⟨244997, by rfl⟩ : syracuseStep 326663 = 489995) B489995
theorem B621587 : Blo 143792 621587 := bstep (se 1 (by rfl) ⟨466190, by rfl⟩ : syracuseStep 621587 = 932381) B932381
theorem B162895 : Blo 143792 162895 := bstep (se 1 (by rfl) ⟨122171, by rfl⟩ : syracuseStep 162895 = 244343) B244343
theorem B326735 : Blo 143792 326735 := bstep (se 1 (by rfl) ⟨245051, by rfl⟩ : syracuseStep 326735 = 490103) B490103
theorem B588953 : Blo 143792 588953 := bstep (se 2 (by rfl) ⟨220857, by rfl⟩ : syracuseStep 588953 = 441715) B441715
theorem B163291 : Blo 143792 163291 := bstep (se 1 (by rfl) ⟨122468, by rfl⟩ : syracuseStep 163291 = 244937) B244937
theorem B327131 : Blo 143792 327131 := bstep (se 1 (by rfl) ⟨245348, by rfl⟩ : syracuseStep 327131 = 490697) B490697
theorem B556577 : Blo 143792 556577 := bstep (se 2 (by rfl) ⟨208716, by rfl⟩ : syracuseStep 556577 = 417433) B417433
theorem B556583 : Blo 143792 556583 := bstep (se 1 (by rfl) ⟨417437, by rfl⟩ : syracuseStep 556583 = 834875) B834875
theorem B1212043 : Blo 143792 1212043 := bstep (se 1 (by rfl) ⟨909032, by rfl⟩ : syracuseStep 1212043 = 1818065) B1818065
theorem B1998553 : Blo 143792 1998553 := bstep (se 2 (by rfl) ⟨749457, by rfl⟩ : syracuseStep 1998553 = 1498915) B1498915
theorem B556895 : Blo 143792 556895 := bstep (se 1 (by rfl) ⟨417671, by rfl⟩ : syracuseStep 556895 = 835343) B835343
theorem B3374963 : Blo 143792 3374963 := bstep (se 1 (by rfl) ⟨2531222, by rfl⟩ : syracuseStep 3374963 = 5062445) B5062445
theorem B163759 : Blo 143792 163759 := bstep (se 1 (by rfl) ⟨122819, by rfl⟩ : syracuseStep 163759 = 245639) B245639
theorem B327599 : Blo 143792 327599 := bstep (se 1 (by rfl) ⟨245699, by rfl⟩ : syracuseStep 327599 = 491399) B491399
theorem B327689 : Blo 143792 327689 := bstep (se 2 (by rfl) ⟨122883, by rfl⟩ : syracuseStep 327689 = 245767) B245767
theorem B1048627 : Blo 143792 1048627 := bstep (se 1 (by rfl) ⟨786470, by rfl⟩ : syracuseStep 1048627 = 1572941) B1572941
theorem B328103 : Blo 143792 328103 := bstep (se 1 (by rfl) ⟨246077, by rfl⟩ : syracuseStep 328103 = 492155) B492155
theorem B164263 : Blo 143792 164263 := bstep (se 1 (by rfl) ⟨123197, by rfl⟩ : syracuseStep 164263 = 246395) B246395
theorem B328211 : Blo 143792 328211 := bstep (se 1 (by rfl) ⟨246158, by rfl⟩ : syracuseStep 328211 = 492317) B492317
theorem B328265 : Blo 143792 328265 := bstep (se 2 (by rfl) ⟨123099, by rfl⟩ : syracuseStep 328265 = 246199) B246199
theorem B524971 : Blo 143792 524971 := bstep (se 1 (by rfl) ⟨393728, by rfl⟩ : syracuseStep 524971 = 787457) B787457
theorem B524983 : Blo 143792 524983 := bstep (se 1 (by rfl) ⟨393737, by rfl⟩ : syracuseStep 524983 = 787475) B787475
theorem B393911 : Blo 143792 393911 := bstep (se 1 (by rfl) ⟨295433, by rfl⟩ : syracuseStep 393911 = 590867) B590867
theorem B3539659 : Blo 143792 3539659 := bstep (se 1 (by rfl) ⟨2654744, by rfl⟩ : syracuseStep 3539659 = 5309489) B5309489
theorem B328679 : Blo 143792 328679 := bstep (se 1 (by rfl) ⟨246509, by rfl⟩ : syracuseStep 328679 = 493019) B493019
theorem B164839 : Blo 143792 164839 := bstep (se 1 (by rfl) ⟨123629, by rfl⟩ : syracuseStep 164839 = 247259) B247259
theorem B492641 : Blo 143792 492641 := bstep (se 2 (by rfl) ⟨184740, by rfl⟩ : syracuseStep 492641 = 369481) B369481
theorem B1115369 : Blo 143792 1115369 := bstep (se 2 (by rfl) ⟨418263, by rfl⟩ : syracuseStep 1115369 = 836527) B836527
theorem B558323 : Blo 143792 558323 := bstep (se 1 (by rfl) ⟨418742, by rfl⟩ : syracuseStep 558323 = 837485) B837485
theorem B329057 : Blo 143792 329057 := bstep (se 2 (by rfl) ⟨123396, by rfl⟩ : syracuseStep 329057 = 246793) B246793
theorem B329147 : Blo 143792 329147 := bstep (se 1 (by rfl) ⟨246860, by rfl⟩ : syracuseStep 329147 = 493721) B493721
theorem B624185 : Blo 143792 624185 := bstep (se 2 (by rfl) ⟨234069, by rfl⟩ : syracuseStep 624185 = 468139) B468139
theorem B329273 : Blo 143792 329273 := bstep (se 2 (by rfl) ⟨123477, by rfl⟩ : syracuseStep 329273 = 246955) B246955
theorem B395113 : Blo 143792 395113 := bstep (se 2 (by rfl) ⟨148167, by rfl⟩ : syracuseStep 395113 = 296335) B296335
theorem B329939 : Blo 143792 329939 := bstep (se 1 (by rfl) ⟨247454, by rfl⟩ : syracuseStep 329939 = 494909) B494909
theorem B461065 : Blo 143792 461065 := bstep (se 2 (by rfl) ⟨172899, by rfl⟩ : syracuseStep 461065 = 345799) B345799
theorem B329993 : Blo 143792 329993 := bstep (se 2 (by rfl) ⟨123747, by rfl⟩ : syracuseStep 329993 = 247495) B247495
theorem B493991 : Blo 143792 493991 := bstep (se 1 (by rfl) ⟨370493, by rfl⟩ : syracuseStep 493991 = 740987) B740987
theorem B330209 : Blo 143792 330209 := bstep (se 2 (by rfl) ⟨123828, by rfl⟩ : syracuseStep 330209 = 247657) B247657
theorem B494153 : Blo 143792 494153 := bstep (se 2 (by rfl) ⟨185307, by rfl⟩ : syracuseStep 494153 = 370615) B370615
theorem B2722405 : Blo 143792 2722405 := bstep (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) B510451
theorem B559811 : Blo 143792 559811 := bstep (se 1 (by rfl) ⟨419858, by rfl⟩ : syracuseStep 559811 = 839717) B839717
theorem B330515 : Blo 143792 330515 := bstep (se 1 (by rfl) ⟨247886, by rfl⟩ : syracuseStep 330515 = 495773) B495773
theorem B4950821 : Blo 143792 4950821 := bstep (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) B928279
theorem B1903409 : Blo 143792 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B330875 : Blo 143792 330875 := bstep (se 1 (by rfl) ⟨248156, by rfl⟩ : syracuseStep 330875 = 496313) B496313
theorem B461963 : Blo 143792 461963 := bstep (se 1 (by rfl) ⟨346472, by rfl⟩ : syracuseStep 461963 = 692945) B692945
theorem B560267 : Blo 143792 560267 := bstep (se 1 (by rfl) ⟨420200, by rfl⟩ : syracuseStep 560267 = 840401) B840401
theorem B331001 : Blo 143792 331001 := bstep (se 2 (by rfl) ⟨124125, by rfl⟩ : syracuseStep 331001 = 248251) B248251
theorem B1248641 : Blo 143792 1248641 := bstep (se 2 (by rfl) ⟨468240, by rfl⟩ : syracuseStep 1248641 = 936481) B936481
theorem B331145 : Blo 143792 331145 := bstep (se 2 (by rfl) ⟨124179, by rfl⟩ : syracuseStep 331145 = 248359) B248359
theorem B331271 : Blo 143792 331271 := bstep (se 1 (by rfl) ⟨248453, by rfl⟩ : syracuseStep 331271 = 496907) B496907
theorem B626201 : Blo 143792 626201 := bstep (se 2 (by rfl) ⟨234825, by rfl⟩ : syracuseStep 626201 = 469651) B469651
theorem B364115 : Blo 143792 364115 := bstep (se 1 (by rfl) ⟨273086, by rfl⟩ : syracuseStep 364115 = 546173) B546173
theorem B331451 : Blo 143792 331451 := bstep (se 1 (by rfl) ⟨248588, by rfl⟩ : syracuseStep 331451 = 497177) B497177
theorem B331577 : Blo 143792 331577 := bstep (se 2 (by rfl) ⟨124341, by rfl⟩ : syracuseStep 331577 = 248683) B248683
theorem B626561 : Blo 143792 626561 := bstep (se 2 (by rfl) ⟨234960, by rfl⟩ : syracuseStep 626561 = 469921) B469921
theorem B495827 : Blo 143792 495827 := bstep (se 1 (by rfl) ⟨371870, by rfl⟩ : syracuseStep 495827 = 743741) B743741
theorem B332207 : Blo 143792 332207 := bstep (se 1 (by rfl) ⟨249155, by rfl⟩ : syracuseStep 332207 = 498311) B498311
theorem B332243 : Blo 143792 332243 := bstep (se 1 (by rfl) ⟨249182, by rfl⟩ : syracuseStep 332243 = 498365) B498365
theorem B496097 : Blo 143792 496097 := bstep (se 2 (by rfl) ⟨186036, by rfl⟩ : syracuseStep 496097 = 372073) B372073
theorem B1118771 : Blo 143792 1118771 := bstep (se 1 (by rfl) ⟨839078, by rfl⟩ : syracuseStep 1118771 = 1678157) B1678157
theorem B332351 : Blo 143792 332351 := bstep (se 1 (by rfl) ⟨249263, by rfl⟩ : syracuseStep 332351 = 498527) B498527
theorem B529049 : Blo 143792 529049 := bstep (se 2 (by rfl) ⟨198393, by rfl⟩ : syracuseStep 529049 = 396787) B396787
theorem B332459 : Blo 143792 332459 := bstep (se 1 (by rfl) ⟨249344, by rfl⟩ : syracuseStep 332459 = 498689) B498689
theorem B693211 : Blo 143792 693211 := bstep (se 1 (by rfl) ⟨519908, by rfl⟩ : syracuseStep 693211 = 1039817) B1039817
theorem B365543 : Blo 143792 365543 := bstep (se 1 (by rfl) ⟨274157, by rfl⟩ : syracuseStep 365543 = 548315) B548315
theorem B2692115 : Blo 143792 2692115 := bstep (se 1 (by rfl) ⟨2019086, by rfl⟩ : syracuseStep 2692115 = 4038173) B4038173
theorem B791801 : Blo 143792 791801 := bstep (se 2 (by rfl) ⟨296925, by rfl⟩ : syracuseStep 791801 = 593851) B593851
theorem B824681 : Blo 143792 824681 := bstep (se 2 (by rfl) ⟨309255, by rfl⟩ : syracuseStep 824681 = 618511) B618511
theorem B11474369 : Blo 143792 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B267769 : Blo 143792 267769 := bstep (se 2 (by rfl) ⟨100413, by rfl⟩ : syracuseStep 267769 = 200827) B200827
theorem B366241 : Blo 143792 366241 := bstep (se 2 (by rfl) ⟨137340, by rfl⟩ : syracuseStep 366241 = 274681) B274681
theorem B497339 : Blo 143792 497339 := bstep (se 1 (by rfl) ⟨373004, by rfl⟩ : syracuseStep 497339 = 746009) B746009
theorem B5936885 : Blo 143792 5936885 := bstep (se 5 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 5936885 = 556583) B556583
theorem B366383 : Blo 143792 366383 := bstep (se 1 (by rfl) ⟨274787, by rfl⟩ : syracuseStep 366383 = 549575) B549575
theorem B1120229 : Blo 143792 1120229 := bstep (se 4 (by rfl) ⟨105021, by rfl⟩ : syracuseStep 1120229 = 210043) B210043
theorem B1644623 : Blo 143792 1644623 := bstep (se 1 (by rfl) ⟨1233467, by rfl⟩ : syracuseStep 1644623 = 2466935) B2466935
theorem B367031 : Blo 143792 367031 := bstep (se 1 (by rfl) ⟨275273, by rfl⟩ : syracuseStep 367031 = 550547) B550547
theorem B728351 : Blo 143792 728351 := bstep (se 1 (by rfl) ⟨546263, by rfl⟩ : syracuseStep 728351 = 1092527) B1092527
theorem B368135 : Blo 143792 368135 := bstep (se 1 (by rfl) ⟨276101, by rfl⟩ : syracuseStep 368135 = 552203) B552203
theorem B1383961 : Blo 143792 1383961 := bstep (se 2 (by rfl) ⟨518985, by rfl⟩ : syracuseStep 1383961 = 1037971) B1037971
theorem B368185 : Blo 143792 368185 := bstep (se 2 (by rfl) ⟨138069, by rfl⟩ : syracuseStep 368185 = 276139) B276139
theorem B597613 : Blo 143792 597613 := bstep (se 3 (by rfl) ⟨112052, by rfl⟩ : syracuseStep 597613 = 224105) B224105
theorem B12754583 : Blo 143792 12754583 := bstep (se 1 (by rfl) ⟨9565937, by rfl⟩ : syracuseStep 12754583 = 19131875) B19131875
theorem B630575 : Blo 143792 630575 := bstep (se 1 (by rfl) ⟨472931, by rfl⟩ : syracuseStep 630575 = 945863) B945863
theorem B368489 : Blo 143792 368489 := bstep (se 2 (by rfl) ⟨138183, by rfl⟩ : syracuseStep 368489 = 276367) B276367
theorem B5054393 : Blo 143792 5054393 := bstep (se 2 (by rfl) ⟨1895397, by rfl⟩ : syracuseStep 5054393 = 3790795) B3790795
theorem B1056887 : Blo 143792 1056887 := bstep (se 1 (by rfl) ⟨792665, by rfl⟩ : syracuseStep 1056887 = 1585331) B1585331
theorem B369107 : Blo 143792 369107 := bstep (se 1 (by rfl) ⟨276830, by rfl⟩ : syracuseStep 369107 = 553661) B553661
theorem B631259 : Blo 143792 631259 := bstep (se 1 (by rfl) ⟨473444, by rfl⟩ : syracuseStep 631259 = 946889) B946889
theorem B1876651 : Blo 143792 1876651 := bstep (se 1 (by rfl) ⟨1407488, by rfl⟩ : syracuseStep 1876651 = 2814977) B2814977
theorem B336559 : Blo 143792 336559 := bstep (se 1 (by rfl) ⟨252419, by rfl⟩ : syracuseStep 336559 = 504839) B504839
theorem B1057697 : Blo 143792 1057697 := bstep (se 2 (by rfl) ⟨396636, by rfl⟩ : syracuseStep 1057697 = 793273) B793273
theorem B893891 : Blo 143792 893891 := bstep (se 1 (by rfl) ⟨670418, by rfl⟩ : syracuseStep 893891 = 1340837) B1340837
theorem B500951 : Blo 143792 500951 := bstep (se 1 (by rfl) ⟨375713, by rfl⟩ : syracuseStep 500951 = 751427) B751427
theorem B370271 : Blo 143792 370271 := bstep (se 1 (by rfl) ⟨277703, by rfl⟩ : syracuseStep 370271 = 555407) B555407
theorem B730781 : Blo 143792 730781 := bstep (se 3 (by rfl) ⟨137021, by rfl⟩ : syracuseStep 730781 = 274043) B274043
theorem B1616057 : Blo 143792 1616057 := bstep (se 2 (by rfl) ⟨606021, by rfl⟩ : syracuseStep 1616057 = 1212043) B1212043
theorem B1681661 : Blo 143792 1681661 := bstep (se 3 (by rfl) ⟨315311, by rfl⟩ : syracuseStep 1681661 = 630623) B630623
theorem B2664737 : Blo 143792 2664737 := bstep (se 2 (by rfl) ⟨999276, by rfl⟩ : syracuseStep 2664737 = 1998553) B1998553
theorem B371051 : Blo 143792 371051 := bstep (se 1 (by rfl) ⟨278288, by rfl⟩ : syracuseStep 371051 = 556577) B556577
theorem B469415 : Blo 143792 469415 := bstep (se 1 (by rfl) ⟨352061, by rfl⟩ : syracuseStep 469415 = 704123) B704123
theorem B1321427 : Blo 143792 1321427 := bstep (se 1 (by rfl) ⟨991070, by rfl⟩ : syracuseStep 1321427 = 1982141) B1982141
theorem B207355 : Blo 143792 207355 := bstep (se 1 (by rfl) ⟨155516, by rfl⟩ : syracuseStep 207355 = 311033) B311033
theorem B371263 : Blo 143792 371263 := bstep (se 1 (by rfl) ⟨278447, by rfl⟩ : syracuseStep 371263 = 556895) B556895
theorem B273071 : Blo 143792 273071 := bstep (se 1 (by rfl) ⟨204803, by rfl⟩ : syracuseStep 273071 = 409607) B409607
theorem B371375 : Blo 143792 371375 := bstep (se 1 (by rfl) ⟨278531, by rfl⟩ : syracuseStep 371375 = 557063) B557063
theorem B273307 : Blo 143792 273307 := bstep (se 1 (by rfl) ⟨204980, by rfl⟩ : syracuseStep 273307 = 409961) B409961
theorem B732077 : Blo 143792 732077 := bstep (se 3 (by rfl) ⟨137264, by rfl⟩ : syracuseStep 732077 = 274529) B274529
theorem B1420253 : Blo 143792 1420253 := bstep (se 3 (by rfl) ⟨266297, by rfl⟩ : syracuseStep 1420253 = 532595) B532595
theorem B371699 : Blo 143792 371699 := bstep (se 1 (by rfl) ⟨278774, by rfl⟩ : syracuseStep 371699 = 557549) B557549
theorem B371911 : Blo 143792 371911 := bstep (se 1 (by rfl) ⟨278933, by rfl⟩ : syracuseStep 371911 = 557867) B557867
theorem B1486433 : Blo 143792 1486433 := bstep (se 2 (by rfl) ⟨557412, by rfl⟩ : syracuseStep 1486433 = 1114825) B1114825
theorem B2076353 : Blo 143792 2076353 := bstep (se 2 (by rfl) ⟨778632, by rfl⟩ : syracuseStep 2076353 = 1557265) B1557265
theorem B175951 : Blo 143792 175951 := bstep (se 1 (by rfl) ⟨131963, by rfl⟩ : syracuseStep 175951 = 263927) B263927
theorem B438601 : Blo 143792 438601 := bstep (se 2 (by rfl) ⟨164475, by rfl⟩ : syracuseStep 438601 = 328951) B328951
theorem B471521 : Blo 143792 471521 := bstep (se 2 (by rfl) ⟨176820, by rfl⟩ : syracuseStep 471521 = 353641) B353641
theorem B143867 : Blo 143792 143867 := bstep (se 1 (by rfl) ⟨107900, by rfl⟩ : syracuseStep 143867 = 215801) B215801
theorem B733697 : Blo 143792 733697 := bstep (se 2 (by rfl) ⟨275136, by rfl⟩ : syracuseStep 733697 = 550273) B550273
theorem B143935 : Blo 143792 143935 := bstep (se 1 (by rfl) ⟨107951, by rfl⟩ : syracuseStep 143935 = 215903) B215903
theorem B143943 : Blo 143792 143943 := bstep (se 1 (by rfl) ⟨107957, by rfl⟩ : syracuseStep 143943 = 215915) B215915
theorem B275015 : Blo 143792 275015 := bstep (se 1 (by rfl) ⟨206261, by rfl⟩ : syracuseStep 275015 = 412523) B412523
theorem B373319 : Blo 143792 373319 := bstep (se 1 (by rfl) ⟨279989, by rfl⟩ : syracuseStep 373319 = 559979) B559979
theorem B373369 : Blo 143792 373369 := bstep (se 2 (by rfl) ⟨140013, by rfl⟩ : syracuseStep 373369 = 280027) B280027
theorem B832153 : Blo 143792 832153 := bstep (se 2 (by rfl) ⟨312057, by rfl⟩ : syracuseStep 832153 = 624115) B624115
theorem B701131 : Blo 143792 701131 := bstep (se 1 (by rfl) ⟨525848, by rfl⟩ : syracuseStep 701131 = 1051697) B1051697
theorem B144095 : Blo 143792 144095 := bstep (se 1 (by rfl) ⟨108071, by rfl⟩ : syracuseStep 144095 = 216143) B216143
theorem B275167 : Blo 143792 275167 := bstep (se 1 (by rfl) ⟨206375, by rfl⟩ : syracuseStep 275167 = 412751) B412751
theorem B144175 : Blo 143792 144175 := bstep (se 1 (by rfl) ⟨108131, by rfl⟩ : syracuseStep 144175 = 216263) B216263
theorem B176951 : Blo 143792 176951 := bstep (se 1 (by rfl) ⟨132713, by rfl⟩ : syracuseStep 176951 = 265427) B265427
theorem B144283 : Blo 143792 144283 := bstep (se 1 (by rfl) ⟨108212, by rfl⟩ : syracuseStep 144283 = 216425) B216425
theorem B144335 : Blo 143792 144335 := bstep (se 1 (by rfl) ⟨108251, by rfl⟩ : syracuseStep 144335 = 216503) B216503
theorem B144359 : Blo 143792 144359 := bstep (se 1 (by rfl) ⟨108269, by rfl⟩ : syracuseStep 144359 = 216539) B216539
theorem B734183 : Blo 143792 734183 := bstep (se 1 (by rfl) ⟨550637, by rfl⟩ : syracuseStep 734183 = 1101275) B1101275
theorem B242831 : Blo 143792 242831 := bstep (se 1 (by rfl) ⟨182123, by rfl⟩ : syracuseStep 242831 = 364247) B364247
theorem B144671 : Blo 143792 144671 := bstep (se 1 (by rfl) ⟨108503, by rfl⟩ : syracuseStep 144671 = 217007) B217007
theorem B734507 : Blo 143792 734507 := bstep (se 1 (by rfl) ⟨550880, by rfl⟩ : syracuseStep 734507 = 1101761) B1101761
theorem B144731 : Blo 143792 144731 := bstep (se 1 (by rfl) ⟨108548, by rfl⟩ : syracuseStep 144731 = 217097) B217097
theorem B144751 : Blo 143792 144751 := bstep (se 1 (by rfl) ⟨108563, by rfl⟩ : syracuseStep 144751 = 217127) B217127
theorem B243067 : Blo 143792 243067 := bstep (se 1 (by rfl) ⟨182300, by rfl⟩ : syracuseStep 243067 = 364601) B364601
theorem B144807 : Blo 143792 144807 := bstep (se 1 (by rfl) ⟨108605, by rfl⟩ : syracuseStep 144807 = 217211) B217211
theorem B144891 : Blo 143792 144891 := bstep (se 1 (by rfl) ⟨108668, by rfl⟩ : syracuseStep 144891 = 217337) B217337
theorem B701959 : Blo 143792 701959 := bstep (se 1 (by rfl) ⟨526469, by rfl⟩ : syracuseStep 701959 = 1052939) B1052939
theorem B144959 : Blo 143792 144959 := bstep (se 1 (by rfl) ⟨108719, by rfl⟩ : syracuseStep 144959 = 217439) B217439
theorem B144967 : Blo 143792 144967 := bstep (se 1 (by rfl) ⟨108725, by rfl⟩ : syracuseStep 144967 = 217451) B217451
theorem B145119 : Blo 143792 145119 := bstep (se 1 (by rfl) ⟨108839, by rfl⟩ : syracuseStep 145119 = 217679) B217679
theorem B145199 : Blo 143792 145199 := bstep (se 1 (by rfl) ⟨108899, by rfl⟩ : syracuseStep 145199 = 217799) B217799
theorem B145307 : Blo 143792 145307 := bstep (se 1 (by rfl) ⟨108980, by rfl⟩ : syracuseStep 145307 = 217961) B217961
theorem B145359 : Blo 143792 145359 := bstep (se 1 (by rfl) ⟨109019, by rfl⟩ : syracuseStep 145359 = 218039) B218039
theorem B145383 : Blo 143792 145383 := bstep (se 1 (by rfl) ⟨109037, by rfl⟩ : syracuseStep 145383 = 218075) B218075
theorem B702593 : Blo 143792 702593 := bstep (se 2 (by rfl) ⟨263472, by rfl⟩ : syracuseStep 702593 = 526945) B526945
theorem B735479 : Blo 143792 735479 := bstep (se 1 (by rfl) ⟨551609, by rfl⟩ : syracuseStep 735479 = 1103219) B1103219
theorem B145695 : Blo 143792 145695 := bstep (se 1 (by rfl) ⟨109271, by rfl⟩ : syracuseStep 145695 = 218543) B218543
theorem B145755 : Blo 143792 145755 := bstep (se 1 (by rfl) ⟨109316, by rfl⟩ : syracuseStep 145755 = 218633) B218633
theorem B145775 : Blo 143792 145775 := bstep (se 1 (by rfl) ⟨109331, by rfl⟩ : syracuseStep 145775 = 218663) B218663
theorem B145831 : Blo 143792 145831 := bstep (se 1 (by rfl) ⟨109373, by rfl⟩ : syracuseStep 145831 = 218747) B218747
theorem B145915 : Blo 143792 145915 := bstep (se 1 (by rfl) ⟨109436, by rfl⟩ : syracuseStep 145915 = 218873) B218873
theorem B145983 : Blo 143792 145983 := bstep (se 1 (by rfl) ⟨109487, by rfl⟩ : syracuseStep 145983 = 218975) B218975
theorem B145991 : Blo 143792 145991 := bstep (se 1 (by rfl) ⟨109493, by rfl⟩ : syracuseStep 145991 = 218987) B218987
theorem B735965 : Blo 143792 735965 := bstep (se 3 (by rfl) ⟨137993, by rfl⟩ : syracuseStep 735965 = 275987) B275987
theorem B146143 : Blo 143792 146143 := bstep (se 1 (by rfl) ⟨109607, by rfl⟩ : syracuseStep 146143 = 219215) B219215
theorem B146223 : Blo 143792 146223 := bstep (se 1 (by rfl) ⟨109667, by rfl⟩ : syracuseStep 146223 = 219335) B219335
theorem B244559 : Blo 143792 244559 := bstep (se 1 (by rfl) ⟨183419, by rfl⟩ : syracuseStep 244559 = 366839) B366839
theorem B146331 : Blo 143792 146331 := bstep (se 1 (by rfl) ⟨109748, by rfl⟩ : syracuseStep 146331 = 219497) B219497
theorem B146383 : Blo 143792 146383 := bstep (se 1 (by rfl) ⟨109787, by rfl⟩ : syracuseStep 146383 = 219575) B219575
theorem B310247 : Blo 143792 310247 := bstep (se 1 (by rfl) ⟨232685, by rfl⟩ : syracuseStep 310247 = 465371) B465371
theorem B146407 : Blo 143792 146407 := bstep (se 1 (by rfl) ⟨109805, by rfl⟩ : syracuseStep 146407 = 219611) B219611
theorem B146719 : Blo 143792 146719 := bstep (se 1 (by rfl) ⟨110039, by rfl⟩ : syracuseStep 146719 = 220079) B220079
theorem B2407747 : Blo 143792 2407747 := bstep (se 1 (by rfl) ⟨1805810, by rfl⟩ : syracuseStep 2407747 = 3611621) B3611621
theorem B146779 : Blo 143792 146779 := bstep (se 1 (by rfl) ⟨110084, by rfl⟩ : syracuseStep 146779 = 220169) B220169
theorem B146799 : Blo 143792 146799 := bstep (se 1 (by rfl) ⟨110099, by rfl⟩ : syracuseStep 146799 = 220199) B220199
theorem B146855 : Blo 143792 146855 := bstep (se 1 (by rfl) ⟨110141, by rfl⟩ : syracuseStep 146855 = 220283) B220283
theorem B146939 : Blo 143792 146939 := bstep (se 1 (by rfl) ⟨110204, by rfl⟩ : syracuseStep 146939 = 220409) B220409
theorem B1261079 : Blo 143792 1261079 := bstep (se 1 (by rfl) ⟨945809, by rfl⟩ : syracuseStep 1261079 = 1891619) B1891619
theorem B2866747 : Blo 143792 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B147007 : Blo 143792 147007 := bstep (se 1 (by rfl) ⟨110255, by rfl⟩ : syracuseStep 147007 = 220511) B220511
theorem B147015 : Blo 143792 147015 := bstep (se 1 (by rfl) ⟨110261, by rfl⟩ : syracuseStep 147015 = 220523) B220523
theorem B147167 : Blo 143792 147167 := bstep (se 1 (by rfl) ⟨110375, by rfl⟩ : syracuseStep 147167 = 220751) B220751
theorem B1228547 : Blo 143792 1228547 := bstep (se 1 (by rfl) ⟨921410, by rfl⟩ : syracuseStep 1228547 = 1842821) B1842821
theorem B245551 : Blo 143792 245551 := bstep (se 1 (by rfl) ⟨184163, by rfl⟩ : syracuseStep 245551 = 368327) B368327
theorem B147247 : Blo 143792 147247 := bstep (se 1 (by rfl) ⟨110435, by rfl⟩ : syracuseStep 147247 = 220871) B220871
theorem B442169 : Blo 143792 442169 := bstep (se 2 (by rfl) ⟨165813, by rfl⟩ : syracuseStep 442169 = 331627) B331627
theorem B147355 : Blo 143792 147355 := bstep (se 1 (by rfl) ⟨110516, by rfl⟩ : syracuseStep 147355 = 221033) B221033
theorem B147407 : Blo 143792 147407 := bstep (se 1 (by rfl) ⟨110555, by rfl⟩ : syracuseStep 147407 = 221111) B221111
theorem B147431 : Blo 143792 147431 := bstep (se 1 (by rfl) ⟨110573, by rfl⟩ : syracuseStep 147431 = 221147) B221147
theorem B147743 : Blo 143792 147743 := bstep (se 1 (by rfl) ⟨110807, by rfl⟩ : syracuseStep 147743 = 221615) B221615
theorem B311887 : Blo 143792 311887 := bstep (se 1 (by rfl) ⟨233915, by rfl⟩ : syracuseStep 311887 = 467831) B467831
theorem B836345 : Blo 143792 836345 := bstep (se 2 (by rfl) ⟨313629, by rfl⟩ : syracuseStep 836345 = 627259) B627259
theorem B607019 : Blo 143792 607019 := bstep (se 1 (by rfl) ⟨455264, by rfl⟩ : syracuseStep 607019 = 910529) B910529
theorem B312673 : Blo 143792 312673 := bstep (se 2 (by rfl) ⟨117252, by rfl⟩ : syracuseStep 312673 = 234505) B234505
theorem B3556781 : Blo 143792 3556781 := bstep (se 3 (by rfl) ⟨666896, by rfl⟩ : syracuseStep 3556781 = 1333793) B1333793
theorem B837053 : Blo 143792 837053 := bstep (se 3 (by rfl) ⟨156947, by rfl⟩ : syracuseStep 837053 = 313895) B313895
theorem B378425 : Blo 143792 378425 := bstep (se 2 (by rfl) ⟨141909, by rfl⟩ : syracuseStep 378425 = 283819) B283819
theorem B411293 : Blo 143792 411293 := bstep (se 3 (by rfl) ⟨77117, by rfl⟩ : syracuseStep 411293 = 154235) B154235
theorem B345761 : Blo 143792 345761 := bstep (se 2 (by rfl) ⟨129660, by rfl⟩ : syracuseStep 345761 = 259321) B259321
theorem B280361 : Blo 143792 280361 := bstep (se 2 (by rfl) ⟨105135, by rfl⟩ : syracuseStep 280361 = 210271) B210271
theorem B346241 : Blo 143792 346241 := bstep (se 2 (by rfl) ⟨129840, by rfl⟩ : syracuseStep 346241 = 259681) B259681
theorem B1427633 : Blo 143792 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B739523 : Blo 143792 739523 := bstep (se 1 (by rfl) ⟨554642, by rfl⟩ : syracuseStep 739523 = 1109285) B1109285
theorem B3754225 : Blo 143792 3754225 := bstep (se 2 (by rfl) ⟨1407834, by rfl⟩ : syracuseStep 3754225 = 2815669) B2815669
theorem B248231 : Blo 143792 248231 := bstep (se 1 (by rfl) ⟨186173, by rfl⟩ : syracuseStep 248231 = 372347) B372347
theorem B248393 : Blo 143792 248393 := bstep (se 2 (by rfl) ⟨93147, by rfl⟩ : syracuseStep 248393 = 186295) B186295
theorem B740015 : Blo 143792 740015 := bstep (se 1 (by rfl) ⟨555011, by rfl⟩ : syracuseStep 740015 = 1110023) B1110023
theorem B215735 : Blo 143792 215735 := bstep (se 1 (by rfl) ⟨161801, by rfl⟩ : syracuseStep 215735 = 323603) B323603
theorem B215963 : Blo 143792 215963 := bstep (se 1 (by rfl) ⟨161972, by rfl⟩ : syracuseStep 215963 = 323945) B323945
theorem B740339 : Blo 143792 740339 := bstep (se 1 (by rfl) ⟨555254, by rfl⟩ : syracuseStep 740339 = 1110509) B1110509
theorem B838943 : Blo 143792 838943 := bstep (se 1 (by rfl) ⟨629207, by rfl⟩ : syracuseStep 838943 = 1258415) B1258415
theorem B216359 : Blo 143792 216359 := bstep (se 1 (by rfl) ⟨162269, by rfl⟩ : syracuseStep 216359 = 324539) B324539
theorem B8539505 : Blo 143792 8539505 := bstep (se 2 (by rfl) ⟨3202314, by rfl⟩ : syracuseStep 8539505 = 6404629) B6404629
theorem B216443 : Blo 143792 216443 := bstep (se 1 (by rfl) ⟨162332, by rfl⟩ : syracuseStep 216443 = 324665) B324665
theorem B937403 : Blo 143792 937403 := bstep (se 1 (by rfl) ⟨703052, by rfl⟩ : syracuseStep 937403 = 1406105) B1406105
theorem B216569 : Blo 143792 216569 := bstep (se 2 (by rfl) ⟨81213, by rfl⟩ : syracuseStep 216569 = 162427) B162427
theorem B216671 : Blo 143792 216671 := bstep (se 1 (by rfl) ⟨162503, by rfl⟩ : syracuseStep 216671 = 325007) B325007
theorem B16305953 : Blo 143792 16305953 := bstep (se 2 (by rfl) ⟨6114732, by rfl⟩ : syracuseStep 16305953 = 12229465) B12229465
theorem B216887 : Blo 143792 216887 := bstep (se 1 (by rfl) ⟨162665, by rfl⟩ : syracuseStep 216887 = 325331) B325331
theorem B184295 : Blo 143792 184295 := bstep (se 1 (by rfl) ⟨138221, by rfl⟩ : syracuseStep 184295 = 276443) B276443
theorem B1232921 : Blo 143792 1232921 := bstep (se 2 (by rfl) ⟨462345, by rfl⟩ : syracuseStep 1232921 = 924691) B924691
theorem B217193 : Blo 143792 217193 := bstep (se 2 (by rfl) ⟨81447, by rfl⟩ : syracuseStep 217193 = 162895) B162895
theorem B741635 : Blo 143792 741635 := bstep (se 1 (by rfl) ⟨556226, by rfl⟩ : syracuseStep 741635 = 1112453) B1112453
theorem B217511 : Blo 143792 217511 := bstep (se 1 (by rfl) ⟨163133, by rfl⟩ : syracuseStep 217511 = 326267) B326267
theorem B217595 : Blo 143792 217595 := bstep (se 1 (by rfl) ⟨163196, by rfl⟩ : syracuseStep 217595 = 326393) B326393
theorem B741959 : Blo 143792 741959 := bstep (se 1 (by rfl) ⟨556469, by rfl⟩ : syracuseStep 741959 = 1112939) B1112939
theorem B217721 : Blo 143792 217721 := bstep (se 2 (by rfl) ⟨81645, by rfl⟩ : syracuseStep 217721 = 163291) B163291
theorem B217775 : Blo 143792 217775 := bstep (se 1 (by rfl) ⟨163331, by rfl⟩ : syracuseStep 217775 = 326663) B326663
theorem B414391 : Blo 143792 414391 := bstep (se 1 (by rfl) ⟨310793, by rfl⟩ : syracuseStep 414391 = 621587) B621587
theorem B217823 : Blo 143792 217823 := bstep (se 1 (by rfl) ⟨163367, by rfl⟩ : syracuseStep 217823 = 326735) B326735
theorem B218087 : Blo 143792 218087 := bstep (se 1 (by rfl) ⟨163565, by rfl⟩ : syracuseStep 218087 = 327131) B327131
theorem B218345 : Blo 143792 218345 := bstep (se 2 (by rfl) ⟨81879, by rfl⟩ : syracuseStep 218345 = 163759) B163759
theorem B2249975 : Blo 143792 2249975 := bstep (se 1 (by rfl) ⟨1687481, by rfl⟩ : syracuseStep 2249975 = 3374963) B3374963
theorem B218399 : Blo 143792 218399 := bstep (se 1 (by rfl) ⟨163799, by rfl⟩ : syracuseStep 218399 = 327599) B327599
theorem B218567 : Blo 143792 218567 := bstep (se 1 (by rfl) ⟨163925, by rfl⟩ : syracuseStep 218567 = 327851) B327851
theorem B1660661 : Blo 143792 1660661 := bstep (se 5 (by rfl) ⟨77843, by rfl⟩ : syracuseStep 1660661 = 155687) B155687
theorem B218921 : Blo 143792 218921 := bstep (se 2 (by rfl) ⟨82095, by rfl⟩ : syracuseStep 218921 = 164191) B164191
theorem B218927 : Blo 143792 218927 := bstep (se 1 (by rfl) ⟨164195, by rfl⟩ : syracuseStep 218927 = 328391) B328391
theorem B939863 : Blo 143792 939863 := bstep (se 1 (by rfl) ⟨704897, by rfl⟩ : syracuseStep 939863 = 1409795) B1409795
theorem B743255 : Blo 143792 743255 := bstep (se 1 (by rfl) ⟨557441, by rfl⟩ : syracuseStep 743255 = 1114883) B1114883
theorem B350057 : Blo 143792 350057 := bstep (se 2 (by rfl) ⟨131271, by rfl⟩ : syracuseStep 350057 = 262543) B262543
theorem B416009 : Blo 143792 416009 := bstep (se 2 (by rfl) ⟨156003, by rfl⟩ : syracuseStep 416009 = 312007) B312007
theorem B219401 : Blo 143792 219401 := bstep (se 2 (by rfl) ⟨82275, by rfl⟩ : syracuseStep 219401 = 164551) B164551
theorem B186715 : Blo 143792 186715 := bstep (se 1 (by rfl) ⟨140036, by rfl⟩ : syracuseStep 186715 = 280073) B280073
theorem B416111 : Blo 143792 416111 := bstep (se 1 (by rfl) ⟨312083, by rfl⟩ : syracuseStep 416111 = 624167) B624167
theorem B219503 : Blo 143792 219503 := bstep (se 1 (by rfl) ⟨164627, by rfl⟩ : syracuseStep 219503 = 329255) B329255
theorem B1235519 : Blo 143792 1235519 := bstep (se 1 (by rfl) ⟨926639, by rfl⟩ : syracuseStep 1235519 = 1853279) B1853279
theorem B186943 : Blo 143792 186943 := bstep (se 1 (by rfl) ⟨140207, by rfl⟩ : syracuseStep 186943 = 280415) B280415
theorem B219719 : Blo 143792 219719 := bstep (se 1 (by rfl) ⟨164789, by rfl⟩ : syracuseStep 219719 = 329579) B329579
theorem B219755 : Blo 143792 219755 := bstep (se 1 (by rfl) ⟨164816, by rfl⟩ : syracuseStep 219755 = 329633) B329633
theorem B219983 : Blo 143792 219983 := bstep (se 1 (by rfl) ⟨164987, by rfl⟩ : syracuseStep 219983 = 329975) B329975
theorem B1235897 : Blo 143792 1235897 := bstep (se 2 (by rfl) ⟨463461, by rfl⟩ : syracuseStep 1235897 = 926923) B926923
theorem B220379 : Blo 143792 220379 := bstep (se 1 (by rfl) ⟨165284, by rfl⟩ : syracuseStep 220379 = 330569) B330569
theorem B1105163 : Blo 143792 1105163 := bstep (se 1 (by rfl) ⟨828872, by rfl⟩ : syracuseStep 1105163 = 1657745) B1657745
theorem B220553 : Blo 143792 220553 := bstep (se 2 (by rfl) ⟨82707, by rfl⟩ : syracuseStep 220553 = 165415) B165415
theorem B351827 : Blo 143792 351827 := bstep (se 1 (by rfl) ⟨263870, by rfl⟩ : syracuseStep 351827 = 527741) B527741
theorem B220907 : Blo 143792 220907 := bstep (se 1 (by rfl) ⟨165680, by rfl⟩ : syracuseStep 220907 = 331361) B331361
theorem B11951887 : Blo 143792 11951887 := bstep (se 1 (by rfl) ⟨8963915, by rfl⟩ : syracuseStep 11951887 = 17927831) B17927831
theorem B221135 : Blo 143792 221135 := bstep (se 1 (by rfl) ⟨165851, by rfl⟩ : syracuseStep 221135 = 331703) B331703
theorem B2547719 : Blo 143792 2547719 := bstep (se 1 (by rfl) ⟨1910789, by rfl⟩ : syracuseStep 2547719 = 3821579) B3821579
theorem B745523 : Blo 143792 745523 := bstep (se 1 (by rfl) ⟨559142, by rfl⟩ : syracuseStep 745523 = 1118285) B1118285
theorem B155935 : Blo 143792 155935 := bstep (se 1 (by rfl) ⟨116951, by rfl⟩ : syracuseStep 155935 = 233903) B233903
theorem B352603 : Blo 143792 352603 := bstep (se 1 (by rfl) ⟨264452, by rfl⟩ : syracuseStep 352603 = 528905) B528905
theorem B221531 : Blo 143792 221531 := bstep (se 1 (by rfl) ⟨166148, by rfl⟩ : syracuseStep 221531 = 332297) B332297
theorem B2450189 : Blo 143792 2450189 := bstep (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) B918821
theorem B3531869 : Blo 143792 3531869 := bstep (se 3 (by rfl) ⟨662225, by rfl⟩ : syracuseStep 3531869 = 1324451) B1324451
theorem B747143 : Blo 143792 747143 := bstep (se 1 (by rfl) ⟨560357, by rfl⟩ : syracuseStep 747143 = 1120715) B1120715
theorem B354671 : Blo 143792 354671 := bstep (se 1 (by rfl) ⟨266003, by rfl⟩ : syracuseStep 354671 = 532007) B532007
theorem B616871 : Blo 143792 616871 := bstep (se 1 (by rfl) ⟨462653, by rfl⟩ : syracuseStep 616871 = 925307) B925307
theorem B584119 : Blo 143792 584119 := bstep (se 1 (by rfl) ⟨438089, by rfl⟩ : syracuseStep 584119 = 876179) B876179
theorem B1108669 : Blo 143792 1108669 := bstep (se 3 (by rfl) ⟨207875, by rfl⟩ : syracuseStep 1108669 = 415751) B415751
theorem B486269 : Blo 143792 486269 := bstep (se 3 (by rfl) ⟨91175, by rfl⟩ : syracuseStep 486269 = 182351) B182351
theorem B420763 : Blo 143792 420763 := bstep (se 1 (by rfl) ⟨315572, by rfl⟩ : syracuseStep 420763 = 631145) B631145
theorem B486539 : Blo 143792 486539 := bstep (se 1 (by rfl) ⟨364904, by rfl⟩ : syracuseStep 486539 = 729809) B729809
theorem B224635 : Blo 143792 224635 := bstep (se 1 (by rfl) ⟨168476, by rfl⟩ : syracuseStep 224635 = 336953) B336953
theorem B716701 : Blo 143792 716701 := bstep (se 3 (by rfl) ⟨134381, by rfl⟩ : syracuseStep 716701 = 268763) B268763
theorem B2683415 : Blo 143792 2683415 := bstep (se 1 (by rfl) ⟨2012561, by rfl⟩ : syracuseStep 2683415 = 4025123) B4025123
theorem B520775 : Blo 143792 520775 := bstep (se 1 (by rfl) ⟨390581, by rfl⟩ : syracuseStep 520775 = 781163) B781163
theorem B7959161 : Blo 143792 7959161 := bstep (se 2 (by rfl) ⟨2984685, by rfl⟩ : syracuseStep 7959161 = 5969371) B5969371
theorem B488159 : Blo 143792 488159 := bstep (se 1 (by rfl) ⟨366119, by rfl⟩ : syracuseStep 488159 = 732239) B732239
theorem B324431 : Blo 143792 324431 := bstep (se 1 (by rfl) ⟨243323, by rfl⟩ : syracuseStep 324431 = 486647) B486647
theorem B783323 : Blo 143792 783323 := bstep (se 1 (by rfl) ⟨587492, by rfl⟩ : syracuseStep 783323 = 1174985) B1174985
theorem B324647 : Blo 143792 324647 := bstep (se 1 (by rfl) ⟨243485, by rfl⟩ : syracuseStep 324647 = 486971) B486971
theorem B488591 : Blo 143792 488591 := bstep (se 1 (by rfl) ⟨366443, by rfl⟩ : syracuseStep 488591 = 732887) B732887
theorem B1995923 : Blo 143792 1995923 := bstep (se 1 (by rfl) ⟨1496942, by rfl⟩ : syracuseStep 1995923 = 2993885) B2993885
theorem B324827 : Blo 143792 324827 := bstep (se 1 (by rfl) ⟨243620, by rfl⟩ : syracuseStep 324827 = 487241) B487241
theorem B947495 : Blo 143792 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B259465 : Blo 143792 259465 := bstep (se 2 (by rfl) ⟨97299, by rfl⟩ : syracuseStep 259465 = 194599) B194599
theorem B325025 : Blo 143792 325025 := bstep (se 2 (by rfl) ⟨121884, by rfl⟩ : syracuseStep 325025 = 243769) B243769
theorem B325583 : Blo 143792 325583 := bstep (se 1 (by rfl) ⟨244187, by rfl⟩ : syracuseStep 325583 = 488375) B488375
theorem B784579 : Blo 143792 784579 := bstep (se 1 (by rfl) ⟨588434, by rfl⟩ : syracuseStep 784579 = 1176869) B1176869
theorem B489725 : Blo 143792 489725 := bstep (se 3 (by rfl) ⟨91823, by rfl⟩ : syracuseStep 489725 = 183647) B183647
theorem B325961 : Blo 143792 325961 := bstep (se 2 (by rfl) ⟨122235, by rfl⟩ : syracuseStep 325961 = 244471) B244471
theorem B162139 : Blo 143792 162139 := bstep (se 1 (by rfl) ⟨121604, by rfl⟩ : syracuseStep 162139 = 243209) B243209
theorem B325979 : Blo 143792 325979 := bstep (se 1 (by rfl) ⟨244484, by rfl⟩ : syracuseStep 325979 = 488969) B488969
theorem B162247 : Blo 143792 162247 := bstep (se 1 (by rfl) ⟨121685, by rfl⟩ : syracuseStep 162247 = 243371) B243371
theorem B1112615 : Blo 143792 1112615 := bstep (se 1 (by rfl) ⟨834461, by rfl⟩ : syracuseStep 1112615 = 1668923) B1668923
theorem B621245 : Blo 143792 621245 := bstep (se 3 (by rfl) ⟨116483, by rfl⟩ : syracuseStep 621245 = 232967) B232967
theorem B162607 : Blo 143792 162607 := bstep (se 1 (by rfl) ⟨121955, by rfl⟩ : syracuseStep 162607 = 243911) B243911
theorem B162715 : Blo 143792 162715 := bstep (se 1 (by rfl) ⟨122036, by rfl⟩ : syracuseStep 162715 = 244073) B244073
theorem B326555 : Blo 143792 326555 := bstep (se 1 (by rfl) ⟨244916, by rfl⟩ : syracuseStep 326555 = 489833) B489833
theorem B490535 : Blo 143792 490535 := bstep (se 1 (by rfl) ⟨367901, by rfl⟩ : syracuseStep 490535 = 735803) B735803
theorem B326753 : Blo 143792 326753 := bstep (se 2 (by rfl) ⟨122532, by rfl⟩ : syracuseStep 326753 = 245065) B245065
theorem B5012603 : Blo 143792 5012603 := bstep (se 1 (by rfl) ⟨3759452, by rfl⟩ : syracuseStep 5012603 = 7518905) B7518905
theorem B163111 : Blo 143792 163111 := bstep (se 1 (by rfl) ⟨122333, by rfl⟩ : syracuseStep 163111 = 244667) B244667
theorem B326951 : Blo 143792 326951 := bstep (se 1 (by rfl) ⟨245213, by rfl⟩ : syracuseStep 326951 = 490427) B490427
theorem B163183 : Blo 143792 163183 := bstep (se 1 (by rfl) ⟨122387, by rfl⟩ : syracuseStep 163183 = 244775) B244775
theorem B392635 : Blo 143792 392635 := bstep (se 1 (by rfl) ⟨294476, by rfl⟩ : syracuseStep 392635 = 588953) B588953
theorem B490967 : Blo 143792 490967 := bstep (se 1 (by rfl) ⟨368225, by rfl⟩ : syracuseStep 490967 = 736451) B736451
theorem B163399 : Blo 143792 163399 := bstep (se 1 (by rfl) ⟨122549, by rfl⟩ : syracuseStep 163399 = 245099) B245099
theorem B327329 : Blo 143792 327329 := bstep (se 2 (by rfl) ⟨122748, by rfl⟩ : syracuseStep 327329 = 245497) B245497
theorem B622511 : Blo 143792 622511 := bstep (se 1 (by rfl) ⟨466883, by rfl⟩ : syracuseStep 622511 = 933767) B933767
theorem B262607 : Blo 143792 262607 := bstep (se 1 (by rfl) ⟨196955, by rfl⟩ : syracuseStep 262607 = 393911) B393911
theorem B557563 : Blo 143792 557563 := bstep (se 1 (by rfl) ⟨418172, by rfl⟩ : syracuseStep 557563 = 836345) B836345
theorem B328427 : Blo 143792 328427 := bstep (se 1 (by rfl) ⟨246320, by rfl⟩ : syracuseStep 328427 = 492641) B492641
theorem B4719545 : Blo 143792 4719545 := bstep (se 2 (by rfl) ⟨1769829, by rfl⟩ : syracuseStep 4719545 = 3539659) B3539659
theorem B558035 : Blo 143792 558035 := bstep (se 1 (by rfl) ⟨418526, by rfl⟩ : syracuseStep 558035 = 837053) B837053
theorem B230507 : Blo 143792 230507 := bstep (se 1 (by rfl) ⟨172880, by rfl⟩ : syracuseStep 230507 = 345761) B345761
theorem B951755 : Blo 143792 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B493015 : Blo 143792 493015 := bstep (se 1 (by rfl) ⟨369761, by rfl⟩ : syracuseStep 493015 = 739523) B739523
theorem B329327 : Blo 143792 329327 := bstep (se 1 (by rfl) ⟨246995, by rfl⟩ : syracuseStep 329327 = 493991) B493991
theorem B165487 : Blo 143792 165487 := bstep (se 1 (by rfl) ⟨124115, by rfl⟩ : syracuseStep 165487 = 248231) B248231
theorem B329435 : Blo 143792 329435 := bstep (se 1 (by rfl) ⟨247076, by rfl⟩ : syracuseStep 329435 = 494153) B494153
theorem B165595 : Blo 143792 165595 := bstep (se 1 (by rfl) ⟨124196, by rfl⟩ : syracuseStep 165595 = 248393) B248393
theorem B1410797 : Blo 143792 1410797 := bstep (se 3 (by rfl) ⟨264524, by rfl⟩ : syracuseStep 1410797 = 529049) B529049
theorem B493343 : Blo 143792 493343 := bstep (se 1 (by rfl) ⟨370007, by rfl⟩ : syracuseStep 493343 = 740015) B740015
theorem B493559 : Blo 143792 493559 := bstep (se 1 (by rfl) ⟨370169, by rfl⟩ : syracuseStep 493559 = 740339) B740339
theorem B559295 : Blo 143792 559295 := bstep (se 1 (by rfl) ⟨419471, by rfl⟩ : syracuseStep 559295 = 838943) B838943
theorem B624935 : Blo 143792 624935 := bstep (se 1 (by rfl) ⟨468701, by rfl⟩ : syracuseStep 624935 = 937403) B937403
theorem B526817 : Blo 143792 526817 := bstep (se 2 (by rfl) ⟨197556, by rfl⟩ : syracuseStep 526817 = 395113) B395113
theorem B821947 : Blo 143792 821947 := bstep (se 1 (by rfl) ⟨616460, by rfl⟩ : syracuseStep 821947 = 1232921) B1232921
theorem B330551 : Blo 143792 330551 := bstep (se 1 (by rfl) ⟨247913, by rfl⟩ : syracuseStep 330551 = 495827) B495827
theorem B494423 : Blo 143792 494423 := bstep (se 1 (by rfl) ⟨370817, by rfl⟩ : syracuseStep 494423 = 741635) B741635
theorem B330731 : Blo 143792 330731 := bstep (se 1 (by rfl) ⟨248048, by rfl⟩ : syracuseStep 330731 = 496097) B496097
theorem B494639 : Blo 143792 494639 := bstep (se 1 (by rfl) ⟨370979, by rfl⟩ : syracuseStep 494639 = 741959) B741959
theorem B5999933 : Blo 143792 5999933 := bstep (se 3 (by rfl) ⟨1124987, by rfl⟩ : syracuseStep 5999933 = 2249975) B2249975
theorem B495017 : Blo 143792 495017 := bstep (se 2 (by rfl) ⟨185631, by rfl⟩ : syracuseStep 495017 = 371263) B371263
theorem B2526653 : Blo 143792 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B527867 : Blo 143792 527867 := bstep (se 1 (by rfl) ⟨395900, by rfl⟩ : syracuseStep 527867 = 791801) B791801
theorem B1478225 : Blo 143792 1478225 := bstep (se 2 (by rfl) ⟨554334, by rfl⟩ : syracuseStep 1478225 = 1108669) B1108669
theorem B331559 : Blo 143792 331559 := bstep (se 1 (by rfl) ⟨248669, by rfl⟩ : syracuseStep 331559 = 497339) B497339
theorem B364409 : Blo 143792 364409 := bstep (se 2 (by rfl) ⟨136653, by rfl⟩ : syracuseStep 364409 = 273307) B273307
theorem B561017 : Blo 143792 561017 := bstep (se 2 (by rfl) ⟨210381, by rfl⟩ : syracuseStep 561017 = 420763) B420763
theorem B495503 : Blo 143792 495503 := bstep (se 1 (by rfl) ⟨371627, by rfl⟩ : syracuseStep 495503 = 743255) B743255
theorem B233371 : Blo 143792 233371 := bstep (se 1 (by rfl) ⟨175028, by rfl⟩ : syracuseStep 233371 = 350057) B350057
theorem B495881 : Blo 143792 495881 := bstep (se 2 (by rfl) ⟨185955, by rfl⟩ : syracuseStep 495881 = 371911) B371911
theorem B823679 : Blo 143792 823679 := bstep (se 1 (by rfl) ⟨617759, by rfl⟩ : syracuseStep 823679 = 1235519) B1235519
theorem B299513 : Blo 143792 299513 := bstep (se 2 (by rfl) ⟨112317, by rfl⟩ : syracuseStep 299513 = 224635) B224635
theorem B823931 : Blo 143792 823931 := bstep (se 1 (by rfl) ⟨617948, by rfl⟩ : syracuseStep 823931 = 1235897) B1235897
theorem B234551 : Blo 143792 234551 := bstep (se 1 (by rfl) ⟨175913, by rfl⟩ : syracuseStep 234551 = 351827) B351827
theorem B955601 : Blo 143792 955601 := bstep (se 2 (by rfl) ⟨358350, by rfl⟩ : syracuseStep 955601 = 716701) B716701
theorem B497015 : Blo 143792 497015 := bstep (se 1 (by rfl) ⟨372761, by rfl⟩ : syracuseStep 497015 = 745523) B745523
theorem B923309 : Blo 143792 923309 := bstep (se 3 (by rfl) ⟨173120, by rfl⟩ : syracuseStep 923309 = 346241) B346241
theorem B595927 : Blo 143792 595927 := bstep (se 1 (by rfl) ⟨446945, by rfl⟩ : syracuseStep 595927 = 893891) B893891
theorem B497825 : Blo 143792 497825 := bstep (se 2 (by rfl) ⟨186684, by rfl⟩ : syracuseStep 497825 = 373369) B373369
theorem B366889 : Blo 143792 366889 := bstep (se 2 (by rfl) ⟨137583, by rfl⟩ : syracuseStep 366889 = 275167) B275167
theorem B498095 : Blo 143792 498095 := bstep (se 1 (by rfl) ⟨373571, by rfl⟩ : syracuseStep 498095 = 747143) B747143
theorem B924281 : Blo 143792 924281 := bstep (se 2 (by rfl) ⟨346605, by rfl⟩ : syracuseStep 924281 = 693211) B693211
theorem B1776491 : Blo 143792 1776491 := bstep (se 1 (by rfl) ⟨1332368, by rfl⟩ : syracuseStep 1776491 = 2664737) B2664737
theorem B236447 : Blo 143792 236447 := bstep (se 1 (by rfl) ⟨177335, by rfl⟩ : syracuseStep 236447 = 354671) B354671
theorem B728189 : Blo 143792 728189 := bstep (se 3 (by rfl) ⟨136535, by rfl⟩ : syracuseStep 728189 = 273071) B273071
theorem B990955 : Blo 143792 990955 := bstep (se 1 (by rfl) ⟨743216, by rfl⟩ : syracuseStep 990955 = 1486433) B1486433
theorem B1384235 : Blo 143792 1384235 := bstep (se 1 (by rfl) ⟨1038176, by rfl⟩ : syracuseStep 1384235 = 2076353) B2076353
theorem B468395 : Blo 143792 468395 := bstep (se 1 (by rfl) ⟨351296, by rfl⟩ : syracuseStep 468395 = 702593) B702593
theorem B206831 : Blo 143792 206831 := bstep (se 1 (by rfl) ⟨155123, by rfl⟩ : syracuseStep 206831 = 310247) B310247
theorem B1845281 : Blo 143792 1845281 := bstep (se 2 (by rfl) ⟨691980, by rfl⟩ : syracuseStep 1845281 = 1383961) B1383961
theorem B796817 : Blo 143792 796817 := bstep (se 2 (by rfl) ⟨298806, by rfl⟩ : syracuseStep 796817 = 597613) B597613
theorem B15935849 : Blo 143792 15935849 := bstep (se 2 (by rfl) ⟨5975943, by rfl⟩ : syracuseStep 15935849 = 11951887) B11951887
theorem B470137 : Blo 143792 470137 := bstep (se 2 (by rfl) ⟨176301, by rfl⟩ : syracuseStep 470137 = 352603) B352603
theorem B372215 : Blo 143792 372215 := bstep (se 1 (by rfl) ⟨279161, by rfl⟩ : syracuseStep 372215 = 558323) B558323
theorem B699961 : Blo 143792 699961 := bstep (se 2 (by rfl) ⟨262485, by rfl⟩ : syracuseStep 699961 = 524971) B524971
theorem B699977 : Blo 143792 699977 := bstep (se 2 (by rfl) ⟨262491, by rfl⟩ : syracuseStep 699977 = 524983) B524983
theorem B2371187 : Blo 143792 2371187 := bstep (se 1 (by rfl) ⟨1778390, by rfl⟩ : syracuseStep 2371187 = 3556781) B3556781
theorem B274195 : Blo 143792 274195 := bstep (se 1 (by rfl) ⟨205646, by rfl⟩ : syracuseStep 274195 = 411293) B411293
theorem B1257389 : Blo 143792 1257389 := bstep (se 3 (by rfl) ⟨235760, by rfl⟩ : syracuseStep 1257389 = 471521) B471521
theorem B7155773 : Blo 143792 7155773 := bstep (se 3 (by rfl) ⟨1341707, by rfl⟩ : syracuseStep 7155773 = 2683415) B2683415
theorem B831653 : Blo 143792 831653 := bstep (se 4 (by rfl) ⟨77967, by rfl⟩ : syracuseStep 831653 = 155935) B155935
theorem B733373 : Blo 143792 733373 := bstep (se 3 (by rfl) ⟨137507, by rfl⟩ : syracuseStep 733373 = 275015) B275015
theorem B143823 : Blo 143792 143823 := bstep (se 1 (by rfl) ⟨107867, by rfl⟩ : syracuseStep 143823 = 215735) B215735
theorem B373207 : Blo 143792 373207 := bstep (se 1 (by rfl) ⟨279905, by rfl⟩ : syracuseStep 373207 = 559811) B559811
theorem B143975 : Blo 143792 143975 := bstep (se 1 (by rfl) ⟨107981, by rfl⟩ : syracuseStep 143975 = 215963) B215963
theorem B307975 : Blo 143792 307975 := bstep (se 1 (by rfl) ⟨230981, by rfl⟩ : syracuseStep 307975 = 461963) B461963
theorem B373511 : Blo 143792 373511 := bstep (se 1 (by rfl) ⟨280133, by rfl⟩ : syracuseStep 373511 = 560267) B560267
theorem B1618717 : Blo 143792 1618717 := bstep (se 3 (by rfl) ⟨303509, by rfl⟩ : syracuseStep 1618717 = 607019) B607019
theorem B471869 : Blo 143792 471869 := bstep (se 3 (by rfl) ⟨88475, by rfl⟩ : syracuseStep 471869 = 176951) B176951
theorem B144239 : Blo 143792 144239 := bstep (se 1 (by rfl) ⟨108179, by rfl⟩ : syracuseStep 144239 = 216359) B216359
theorem B144295 : Blo 143792 144295 := bstep (se 1 (by rfl) ⟨108221, by rfl⟩ : syracuseStep 144295 = 216443) B216443
theorem B832427 : Blo 143792 832427 := bstep (se 1 (by rfl) ⟨624320, by rfl⟩ : syracuseStep 832427 = 1248641) B1248641
theorem B144379 : Blo 143792 144379 := bstep (se 1 (by rfl) ⟨108284, by rfl⟩ : syracuseStep 144379 = 216569) B216569
theorem B242743 : Blo 143792 242743 := bstep (se 1 (by rfl) ⟨182057, by rfl⟩ : syracuseStep 242743 = 364115) B364115
theorem B144447 : Blo 143792 144447 := bstep (se 1 (by rfl) ⟨108335, by rfl⟩ : syracuseStep 144447 = 216671) B216671
theorem B144591 : Blo 143792 144591 := bstep (se 1 (by rfl) ⟨108443, by rfl⟩ : syracuseStep 144591 = 216887) B216887
theorem B144795 : Blo 143792 144795 := bstep (se 1 (by rfl) ⟨108596, by rfl⟩ : syracuseStep 144795 = 217193) B217193
theorem B145007 : Blo 143792 145007 := bstep (se 1 (by rfl) ⟨108755, by rfl⟩ : syracuseStep 145007 = 217511) B217511
theorem B145063 : Blo 143792 145063 := bstep (se 1 (by rfl) ⟨108797, by rfl⟩ : syracuseStep 145063 = 217595) B217595
theorem B145147 : Blo 143792 145147 := bstep (se 1 (by rfl) ⟨108860, by rfl⟩ : syracuseStep 145147 = 217721) B217721
theorem B145183 : Blo 143792 145183 := bstep (se 1 (by rfl) ⟨108887, by rfl⟩ : syracuseStep 145183 = 217775) B217775
theorem B145215 : Blo 143792 145215 := bstep (se 1 (by rfl) ⟨108911, by rfl⟩ : syracuseStep 145215 = 217823) B217823
theorem B243695 : Blo 143792 243695 := bstep (se 1 (by rfl) ⟨182771, by rfl⟩ : syracuseStep 243695 = 365543) B365543
theorem B145391 : Blo 143792 145391 := bstep (se 1 (by rfl) ⟨109043, by rfl⟩ : syracuseStep 145391 = 218087) B218087
theorem B276473 : Blo 143792 276473 := bstep (se 2 (by rfl) ⟨103677, by rfl⟩ : syracuseStep 276473 = 207355) B207355
theorem B145563 : Blo 143792 145563 := bstep (se 1 (by rfl) ⟨109172, by rfl⟩ : syracuseStep 145563 = 218345) B218345
theorem B145599 : Blo 143792 145599 := bstep (se 1 (by rfl) ⟨109199, by rfl⟩ : syracuseStep 145599 = 218399) B218399
theorem B7649579 : Blo 143792 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B145711 : Blo 143792 145711 := bstep (se 1 (by rfl) ⟨109283, by rfl⟩ : syracuseStep 145711 = 218567) B218567
theorem B145947 : Blo 143792 145947 := bstep (se 1 (by rfl) ⟨109460, by rfl⟩ : syracuseStep 145947 = 218921) B218921
theorem B244255 : Blo 143792 244255 := bstep (se 1 (by rfl) ⟨183191, by rfl⟩ : syracuseStep 244255 = 366383) B366383
theorem B145951 : Blo 143792 145951 := bstep (se 1 (by rfl) ⟨109463, by rfl⟩ : syracuseStep 145951 = 218927) B218927
theorem B1096415 : Blo 143792 1096415 := bstep (se 1 (by rfl) ⟨822311, by rfl⟩ : syracuseStep 1096415 = 1644623) B1644623
theorem B277339 : Blo 143792 277339 := bstep (se 1 (by rfl) ⟨208004, by rfl⟩ : syracuseStep 277339 = 416009) B416009
theorem B146267 : Blo 143792 146267 := bstep (se 1 (by rfl) ⟨109700, by rfl⟩ : syracuseStep 146267 = 219401) B219401
theorem B146335 : Blo 143792 146335 := bstep (se 1 (by rfl) ⟨109751, by rfl⟩ : syracuseStep 146335 = 219503) B219503
theorem B244687 : Blo 143792 244687 := bstep (se 1 (by rfl) ⟨183515, by rfl⟩ : syracuseStep 244687 = 367031) B367031
theorem B146479 : Blo 143792 146479 := bstep (se 1 (by rfl) ⟨109859, by rfl⟩ : syracuseStep 146479 = 219719) B219719
theorem B146503 : Blo 143792 146503 := bstep (se 1 (by rfl) ⟨109877, by rfl⟩ : syracuseStep 146503 = 219755) B219755
theorem B146655 : Blo 143792 146655 := bstep (se 1 (by rfl) ⟨109991, by rfl⟩ : syracuseStep 146655 = 219983) B219983
theorem B146919 : Blo 143792 146919 := bstep (se 1 (by rfl) ⟨110189, by rfl⟩ : syracuseStep 146919 = 220379) B220379
theorem B736775 : Blo 143792 736775 := bstep (se 1 (by rfl) ⟨552581, by rfl⟩ : syracuseStep 736775 = 1105163) B1105163
theorem B2506301 : Blo 143792 2506301 := bstep (se 3 (by rfl) ⟨469931, by rfl⟩ : syracuseStep 2506301 = 939863) B939863
theorem B147035 : Blo 143792 147035 := bstep (se 1 (by rfl) ⟨110276, by rfl⟩ : syracuseStep 147035 = 220553) B220553
theorem B245423 : Blo 143792 245423 := bstep (se 1 (by rfl) ⟨184067, by rfl⟩ : syracuseStep 245423 = 368135) B368135
theorem B8503055 : Blo 143792 8503055 := bstep (se 1 (by rfl) ⟨6377291, by rfl⟩ : syracuseStep 8503055 = 12754583) B12754583
theorem B147271 : Blo 143792 147271 := bstep (se 1 (by rfl) ⟨110453, by rfl⟩ : syracuseStep 147271 = 220907) B220907
theorem B245659 : Blo 143792 245659 := bstep (se 1 (by rfl) ⟨184244, by rfl⟩ : syracuseStep 245659 = 368489) B368489
theorem B147423 : Blo 143792 147423 := bstep (se 1 (by rfl) ⟨110567, by rfl⟩ : syracuseStep 147423 = 221135) B221135
theorem B704591 : Blo 143792 704591 := bstep (se 1 (by rfl) ⟨528443, by rfl⟩ : syracuseStep 704591 = 1056887) B1056887
theorem B147687 : Blo 143792 147687 := bstep (se 1 (by rfl) ⟨110765, by rfl⟩ : syracuseStep 147687 = 221531) B221531
theorem B246071 : Blo 143792 246071 := bstep (se 1 (by rfl) ⟨184553, by rfl⟩ : syracuseStep 246071 = 369107) B369107
theorem B705131 : Blo 143792 705131 := bstep (se 1 (by rfl) ⟨528848, by rfl⟩ : syracuseStep 705131 = 1057697) B1057697
theorem B934841 : Blo 143792 934841 := bstep (se 2 (by rfl) ⟨350565, by rfl⟩ : syracuseStep 934841 = 701131) B701131
theorem B246847 : Blo 143792 246847 := bstep (se 1 (by rfl) ⟨185135, by rfl⟩ : syracuseStep 246847 = 370271) B370271
theorem B247367 : Blo 143792 247367 := bstep (se 1 (by rfl) ⟨185525, by rfl⟩ : syracuseStep 247367 = 371051) B371051
theorem B411247 : Blo 143792 411247 := bstep (se 1 (by rfl) ⟨308435, by rfl⟩ : syracuseStep 411247 = 616871) B616871
theorem B312943 : Blo 143792 312943 := bstep (se 1 (by rfl) ⟨234707, by rfl⟩ : syracuseStep 312943 = 469415) B469415
theorem B247583 : Blo 143792 247583 := bstep (se 1 (by rfl) ⟨185687, by rfl⟩ : syracuseStep 247583 = 371375) B371375
theorem B345953 : Blo 143792 345953 := bstep (se 2 (by rfl) ⟨129732, by rfl⟩ : syracuseStep 345953 = 259465) B259465
theorem B247799 : Blo 143792 247799 := bstep (se 1 (by rfl) ⟨185849, by rfl⟩ : syracuseStep 247799 = 371699) B371699
theorem B935945 : Blo 143792 935945 := bstep (se 2 (by rfl) ⟨350979, by rfl⟩ : syracuseStep 935945 = 701959) B701959
theorem B1428101 : Blo 143792 1428101 := bstep (se 4 (by rfl) ⟨133884, by rfl⟩ : syracuseStep 1428101 = 267769) B267769
theorem B347183 : Blo 143792 347183 := bstep (se 1 (by rfl) ⟨260387, by rfl⟩ : syracuseStep 347183 = 520775) B520775
theorem B248879 : Blo 143792 248879 := bstep (se 1 (by rfl) ⟨186659, by rfl⟩ : syracuseStep 248879 = 373319) B373319
theorem B216185 : Blo 143792 216185 := bstep (se 2 (by rfl) ⟨81069, by rfl⟩ : syracuseStep 216185 = 162139) B162139
theorem B248953 : Blo 143792 248953 := bstep (se 2 (by rfl) ⟨93357, by rfl⟩ : syracuseStep 248953 = 186715) B186715
theorem B216287 : Blo 143792 216287 := bstep (se 1 (by rfl) ⟨162215, by rfl⟩ : syracuseStep 216287 = 324431) B324431
theorem B216329 : Blo 143792 216329 := bstep (se 2 (by rfl) ⟨81123, by rfl⟩ : syracuseStep 216329 = 162247) B162247
theorem B216431 : Blo 143792 216431 := bstep (se 1 (by rfl) ⟨162323, by rfl⟩ : syracuseStep 216431 = 324647) B324647
theorem B249257 : Blo 143792 249257 := bstep (se 2 (by rfl) ⟨93471, by rfl⟩ : syracuseStep 249257 = 186943) B186943
theorem B1330615 : Blo 143792 1330615 := bstep (se 1 (by rfl) ⟨997961, by rfl⟩ : syracuseStep 1330615 = 1995923) B1995923
theorem B216551 : Blo 143792 216551 := bstep (se 1 (by rfl) ⟨162413, by rfl⟩ : syracuseStep 216551 = 324827) B324827
theorem B216683 : Blo 143792 216683 := bstep (se 1 (by rfl) ⟨162512, by rfl⟩ : syracuseStep 216683 = 325025) B325025
theorem B216809 : Blo 143792 216809 := bstep (se 2 (by rfl) ⟨81303, by rfl⟩ : syracuseStep 216809 = 162607) B162607
theorem B216953 : Blo 143792 216953 := bstep (se 2 (by rfl) ⟨81357, by rfl⟩ : syracuseStep 216953 = 162715) B162715
theorem B217055 : Blo 143792 217055 := bstep (se 1 (by rfl) ⟨162791, by rfl⟩ : syracuseStep 217055 = 325583) B325583
theorem B217307 : Blo 143792 217307 := bstep (se 1 (by rfl) ⟨162980, by rfl⟩ : syracuseStep 217307 = 325961) B325961
theorem B217319 : Blo 143792 217319 := bstep (se 1 (by rfl) ⟨162989, by rfl⟩ : syracuseStep 217319 = 325979) B325979
theorem B741743 : Blo 143792 741743 := bstep (se 1 (by rfl) ⟨556307, by rfl⟩ : syracuseStep 741743 = 1112615) B1112615
theorem B217481 : Blo 143792 217481 := bstep (se 2 (by rfl) ⟨81555, by rfl⟩ : syracuseStep 217481 = 163111) B163111
theorem B938405 : Blo 143792 938405 := bstep (se 4 (by rfl) ⟨87975, by rfl⟩ : syracuseStep 938405 = 175951) B175951
theorem B414163 : Blo 143792 414163 := bstep (se 1 (by rfl) ⟨310622, by rfl⟩ : syracuseStep 414163 = 621245) B621245
theorem B217577 : Blo 143792 217577 := bstep (se 2 (by rfl) ⟨81591, by rfl⟩ : syracuseStep 217577 = 163183) B163183
theorem B217703 : Blo 143792 217703 := bstep (se 1 (by rfl) ⟨163277, by rfl⟩ : syracuseStep 217703 = 326555) B326555
theorem B217835 : Blo 143792 217835 := bstep (se 1 (by rfl) ⟨163376, by rfl⟩ : syracuseStep 217835 = 326753) B326753
theorem B3822329 : Blo 143792 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B217865 : Blo 143792 217865 := bstep (se 2 (by rfl) ⟨81699, by rfl⟩ : syracuseStep 217865 = 163399) B163399
theorem B217967 : Blo 143792 217967 := bstep (se 1 (by rfl) ⟨163475, by rfl⟩ : syracuseStep 217967 = 326951) B326951
theorem B840719 : Blo 143792 840719 := bstep (se 1 (by rfl) ⟨630539, by rfl⟩ : syracuseStep 840719 = 1261079) B1261079
theorem B218219 : Blo 143792 218219 := bstep (se 1 (by rfl) ⟨163664, by rfl⟩ : syracuseStep 218219 = 327329) B327329
theorem B415007 : Blo 143792 415007 := bstep (se 1 (by rfl) ⟨311255, by rfl⟩ : syracuseStep 415007 = 622511) B622511
theorem B218459 : Blo 143792 218459 := bstep (se 1 (by rfl) ⟨163844, by rfl⟩ : syracuseStep 218459 = 327689) B327689
theorem B1398169 : Blo 143792 1398169 := bstep (se 2 (by rfl) ⟨524313, by rfl⟩ : syracuseStep 1398169 = 1048627) B1048627
theorem B218735 : Blo 143792 218735 := bstep (se 1 (by rfl) ⟨164051, by rfl⟩ : syracuseStep 218735 = 328103) B328103
theorem B218807 : Blo 143792 218807 := bstep (se 1 (by rfl) ⟨164105, by rfl⟩ : syracuseStep 218807 = 328211) B328211
theorem B218843 : Blo 143792 218843 := bstep (se 1 (by rfl) ⟨164132, by rfl⟩ : syracuseStep 218843 = 328265) B328265
theorem B219017 : Blo 143792 219017 := bstep (se 2 (by rfl) ⟨82131, by rfl⟩ : syracuseStep 219017 = 164263) B164263
theorem B219119 : Blo 143792 219119 := bstep (se 1 (by rfl) ⟨164339, by rfl⟩ : syracuseStep 219119 = 328679) B328679
theorem B415849 : Blo 143792 415849 := bstep (se 2 (by rfl) ⟨155943, by rfl⟩ : syracuseStep 415849 = 311887) B311887
theorem B743579 : Blo 143792 743579 := bstep (se 1 (by rfl) ⟨557684, by rfl⟩ : syracuseStep 743579 = 1115369) B1115369
theorem B448745 : Blo 143792 448745 := bstep (se 2 (by rfl) ⟨168279, by rfl⟩ : syracuseStep 448745 = 336559) B336559
theorem B219371 : Blo 143792 219371 := bstep (se 1 (by rfl) ⟨164528, by rfl⟩ : syracuseStep 219371 = 329057) B329057
theorem B219431 : Blo 143792 219431 := bstep (se 1 (by rfl) ⟨164573, by rfl⟩ : syracuseStep 219431 = 329147) B329147
theorem B416123 : Blo 143792 416123 := bstep (se 1 (by rfl) ⟨312092, by rfl⟩ : syracuseStep 416123 = 624185) B624185
theorem B219515 : Blo 143792 219515 := bstep (se 1 (by rfl) ⟨164636, by rfl⟩ : syracuseStep 219515 = 329273) B329273
theorem B252283 : Blo 143792 252283 := bstep (se 1 (by rfl) ⟨189212, by rfl⟩ : syracuseStep 252283 = 378425) B378425
theorem B219785 : Blo 143792 219785 := bstep (se 2 (by rfl) ⟨82419, by rfl⟩ : syracuseStep 219785 = 164839) B164839
theorem B219959 : Blo 143792 219959 := bstep (se 1 (by rfl) ⟨164969, by rfl⟩ : syracuseStep 219959 = 329939) B329939
theorem B219995 : Blo 143792 219995 := bstep (se 1 (by rfl) ⟨164996, by rfl⟩ : syracuseStep 219995 = 329993) B329993
theorem B220139 : Blo 143792 220139 := bstep (se 1 (by rfl) ⟨165104, by rfl⟩ : syracuseStep 220139 = 330209) B330209
theorem B416897 : Blo 143792 416897 := bstep (se 2 (by rfl) ⟨156336, by rfl⟩ : syracuseStep 416897 = 312673) B312673
theorem B220343 : Blo 143792 220343 := bstep (se 1 (by rfl) ⟨165257, by rfl⟩ : syracuseStep 220343 = 330515) B330515
theorem B1268939 : Blo 143792 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B220583 : Blo 143792 220583 := bstep (se 1 (by rfl) ⟨165437, by rfl⟩ : syracuseStep 220583 = 330875) B330875
theorem B220667 : Blo 143792 220667 := bstep (se 1 (by rfl) ⟨165500, by rfl⟩ : syracuseStep 220667 = 331001) B331001
theorem B5693003 : Blo 143792 5693003 := bstep (se 1 (by rfl) ⟨4269752, by rfl⟩ : syracuseStep 5693003 = 8539505) B8539505
theorem B220763 : Blo 143792 220763 := bstep (se 1 (by rfl) ⟨165572, by rfl⟩ : syracuseStep 220763 = 331145) B331145
theorem B220847 : Blo 143792 220847 := bstep (se 1 (by rfl) ⟨165635, by rfl⟩ : syracuseStep 220847 = 331271) B331271
theorem B417467 : Blo 143792 417467 := bstep (se 1 (by rfl) ⟨313100, by rfl⟩ : syracuseStep 417467 = 626201) B626201
theorem B220967 : Blo 143792 220967 := bstep (se 1 (by rfl) ⟨165725, by rfl⟩ : syracuseStep 220967 = 331451) B331451
theorem B221051 : Blo 143792 221051 := bstep (se 1 (by rfl) ⟨165788, by rfl⟩ : syracuseStep 221051 = 331577) B331577
theorem B417707 : Blo 143792 417707 := bstep (se 1 (by rfl) ⟨313280, by rfl⟩ : syracuseStep 417707 = 626561) B626561
theorem B221471 : Blo 143792 221471 := bstep (se 1 (by rfl) ⟨166103, by rfl⟩ : syracuseStep 221471 = 332207) B332207
theorem B221495 : Blo 143792 221495 := bstep (se 1 (by rfl) ⟨166121, by rfl⟩ : syracuseStep 221495 = 332243) B332243
theorem B5005633 : Blo 143792 5005633 := bstep (se 2 (by rfl) ⟨1877112, by rfl⟩ : syracuseStep 5005633 = 3754225) B3754225
theorem B614753 : Blo 143792 614753 := bstep (se 2 (by rfl) ⟨230532, by rfl⟩ : syracuseStep 614753 = 461065) B461065
theorem B745847 : Blo 143792 745847 := bstep (se 1 (by rfl) ⟨559385, by rfl⟩ : syracuseStep 745847 = 1118771) B1118771
theorem B221567 : Blo 143792 221567 := bstep (se 1 (by rfl) ⟨166175, by rfl⟩ : syracuseStep 221567 = 332351) B332351
theorem B221639 : Blo 143792 221639 := bstep (se 1 (by rfl) ⟨166229, by rfl⟩ : syracuseStep 221639 = 332459) B332459
theorem B1335869 : Blo 143792 1335869 := bstep (se 3 (by rfl) ⟨250475, by rfl⟩ : syracuseStep 1335869 = 500951) B500951
theorem B778825 : Blo 143792 778825 := bstep (se 2 (by rfl) ⟨292059, by rfl⟩ : syracuseStep 778825 = 584119) B584119
theorem B1794743 : Blo 143792 1794743 := bstep (se 1 (by rfl) ⟨1346057, by rfl⟩ : syracuseStep 1794743 = 2692115) B2692115
theorem B3629873 : Blo 143792 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B40035221 : Blo 143792 40035221 := bstep (se 6 (by rfl) ⟨938325, by rfl⟩ : syracuseStep 40035221 = 1876651) B1876651
theorem B549787 : Blo 143792 549787 := bstep (se 1 (by rfl) ⟨412340, by rfl⟩ : syracuseStep 549787 = 824681) B824681
theorem B3957923 : Blo 143792 3957923 := bstep (se 1 (by rfl) ⟨2968442, by rfl⟩ : syracuseStep 3957923 = 5936885) B5936885
theorem B1107107 : Blo 143792 1107107 := bstep (se 1 (by rfl) ⟨830330, by rfl⟩ : syracuseStep 1107107 = 1660661) B1660661
theorem B746819 : Blo 143792 746819 := bstep (se 1 (by rfl) ⟨560114, by rfl⟩ : syracuseStep 746819 = 1120229) B1120229
theorem B747629 : Blo 143792 747629 := bstep (se 3 (by rfl) ⟨140180, by rfl⟩ : syracuseStep 747629 = 280361) B280361
theorem B485567 : Blo 143792 485567 := bstep (se 1 (by rfl) ⟨364175, by rfl⟩ : syracuseStep 485567 = 728351) B728351
theorem B420383 : Blo 143792 420383 := bstep (se 1 (by rfl) ⟨315287, by rfl⟩ : syracuseStep 420383 = 630575) B630575
theorem B3369595 : Blo 143792 3369595 := bstep (se 1 (by rfl) ⟨2527196, by rfl⟩ : syracuseStep 3369595 = 5054393) B5054393
theorem B1698479 : Blo 143792 1698479 := bstep (se 1 (by rfl) ⟨1273859, by rfl⟩ : syracuseStep 1698479 = 2547719) B2547719
theorem B420839 : Blo 143792 420839 := bstep (se 1 (by rfl) ⟨315629, by rfl⟩ : syracuseStep 420839 = 631259) B631259
theorem B584801 : Blo 143792 584801 := bstep (se 2 (by rfl) ⟨219300, by rfl⟩ : syracuseStep 584801 = 438601) B438601
theorem B1633459 : Blo 143792 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B4484429 : Blo 143792 4484429 := bstep (se 3 (by rfl) ⟨840830, by rfl⟩ : syracuseStep 4484429 = 1681661) B1681661
theorem B2354579 : Blo 143792 2354579 := bstep (se 1 (by rfl) ⟨1765934, by rfl⟩ : syracuseStep 2354579 = 3531869) B3531869
theorem B1109537 : Blo 143792 1109537 := bstep (se 2 (by rfl) ⟨416076, by rfl⟩ : syracuseStep 1109537 = 832153) B832153
theorem B552521 : Blo 143792 552521 := bstep (se 2 (by rfl) ⟨207195, by rfl⟩ : syracuseStep 552521 = 414391) B414391
theorem B1109629 : Blo 143792 1109629 := bstep (se 3 (by rfl) ⟨208055, by rfl⟩ : syracuseStep 1109629 = 416111) B416111
theorem B487187 : Blo 143792 487187 := bstep (se 1 (by rfl) ⟨365390, by rfl⟩ : syracuseStep 487187 = 730781) B730781
theorem B1077371 : Blo 143792 1077371 := bstep (se 1 (by rfl) ⟨808028, by rfl⟩ : syracuseStep 1077371 = 1616057) B1616057
theorem B880951 : Blo 143792 880951 := bstep (se 1 (by rfl) ⟨660713, by rfl⟩ : syracuseStep 880951 = 1321427) B1321427
theorem B324089 : Blo 143792 324089 := bstep (se 2 (by rfl) ⟨121533, by rfl⟩ : syracuseStep 324089 = 243067) B243067
theorem B324179 : Blo 143792 324179 := bstep (se 1 (by rfl) ⟨243134, by rfl⟩ : syracuseStep 324179 = 486269) B486269
theorem B488051 : Blo 143792 488051 := bstep (se 1 (by rfl) ⟨366038, by rfl⟩ : syracuseStep 488051 = 732077) B732077
theorem B946835 : Blo 143792 946835 := bstep (se 1 (by rfl) ⟨710126, by rfl⟩ : syracuseStep 946835 = 1420253) B1420253
theorem B324359 : Blo 143792 324359 := bstep (se 1 (by rfl) ⟨243269, by rfl⟩ : syracuseStep 324359 = 486539) B486539
theorem B13202189 : Blo 143792 13202189 := bstep (se 3 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 13202189 = 4950821) B4950821
theorem B488321 : Blo 143792 488321 := bstep (se 2 (by rfl) ⟨183120, by rfl⟩ : syracuseStep 488321 = 366241) B366241
theorem B1046105 : Blo 143792 1046105 := bstep (se 2 (by rfl) ⟨392289, by rfl⟩ : syracuseStep 1046105 = 784579) B784579
theorem B489131 : Blo 143792 489131 := bstep (se 1 (by rfl) ⟨366848, by rfl⟩ : syracuseStep 489131 = 733697) B733697
theorem B173930165 : Blo 143792 173930165 := bstep (se 5 (by rfl) ⟨8152976, by rfl⟩ : syracuseStep 173930165 = 16305953) B16305953
theorem B5306107 : Blo 143792 5306107 := bstep (se 1 (by rfl) ⟨3979580, by rfl⟩ : syracuseStep 5306107 = 7959161) B7959161
theorem B325439 : Blo 143792 325439 := bstep (se 1 (by rfl) ⟨244079, by rfl⟩ : syracuseStep 325439 = 488159) B488159
theorem B522215 : Blo 143792 522215 := bstep (se 1 (by rfl) ⟨391661, by rfl⟩ : syracuseStep 522215 = 783323) B783323
theorem B489455 : Blo 143792 489455 := bstep (se 1 (by rfl) ⟨367091, by rfl⟩ : syracuseStep 489455 = 734183) B734183
theorem B161887 : Blo 143792 161887 := bstep (se 1 (by rfl) ⟨121415, by rfl⟩ : syracuseStep 161887 = 242831) B242831
theorem B325727 : Blo 143792 325727 := bstep (se 1 (by rfl) ⟨244295, by rfl⟩ : syracuseStep 325727 = 488591) B488591
theorem B489671 : Blo 143792 489671 := bstep (se 1 (by rfl) ⟨367253, by rfl⟩ : syracuseStep 489671 = 734507) B734507
theorem B490319 : Blo 143792 490319 := bstep (se 1 (by rfl) ⟨367739, by rfl⟩ : syracuseStep 490319 = 735479) B735479
theorem B326483 : Blo 143792 326483 := bstep (se 1 (by rfl) ⟨244862, by rfl⟩ : syracuseStep 326483 = 489725) B489725
theorem B3210329 : Blo 143792 3210329 := bstep (se 2 (by rfl) ⟨1203873, by rfl⟩ : syracuseStep 3210329 = 2407747) B2407747
theorem B490643 : Blo 143792 490643 := bstep (se 1 (by rfl) ⟨367982, by rfl⟩ : syracuseStep 490643 = 735965) B735965
theorem B163039 : Blo 143792 163039 := bstep (se 1 (by rfl) ⟨122279, by rfl⟩ : syracuseStep 163039 = 244559) B244559
theorem B523513 : Blo 143792 523513 := bstep (se 2 (by rfl) ⟨196317, by rfl⟩ : syracuseStep 523513 = 392635) B392635
theorem B327023 : Blo 143792 327023 := bstep (se 1 (by rfl) ⟨245267, by rfl⟩ : syracuseStep 327023 = 490535) B490535
theorem B490913 : Blo 143792 490913 := bstep (se 2 (by rfl) ⟨184092, by rfl⟩ : syracuseStep 490913 = 368185) B368185
theorem B3341735 : Blo 143792 3341735 := bstep (se 1 (by rfl) ⟨2506301, by rfl⟩ : syracuseStep 3341735 = 5012603) B5012603
theorem B327311 : Blo 143792 327311 := bstep (se 1 (by rfl) ⟨245483, by rfl⟩ : syracuseStep 327311 = 490967) B490967
theorem B327401 : Blo 143792 327401 := bstep (se 2 (by rfl) ⟨122775, by rfl⟩ : syracuseStep 327401 = 245551) B245551
theorem B819031 : Blo 143792 819031 := bstep (se 1 (by rfl) ⟨614273, by rfl⟩ : syracuseStep 819031 = 1228547) B1228547
theorem B294779 : Blo 143792 294779 := bstep (se 1 (by rfl) ⟨221084, by rfl⟩ : syracuseStep 294779 = 442169) B442169
theorem B491453 : Blo 143792 491453 := bstep (se 3 (by rfl) ⟨92147, by rfl⟩ : syracuseStep 491453 = 184295) B184295
theorem B164047 : Blo 143792 164047 := bstep (se 1 (by rfl) ⟨123035, by rfl⟩ : syracuseStep 164047 = 246071) B246071
theorem B3146363 : Blo 143792 3146363 := bstep (se 1 (by rfl) ⟨2359772, by rfl⟩ : syracuseStep 3146363 = 4719545) B4719545
theorem B623227 : Blo 143792 623227 := bstep (se 1 (by rfl) ⟨467420, by rfl⟩ : syracuseStep 623227 = 934841) B934841
theorem B164911 : Blo 143792 164911 := bstep (se 1 (by rfl) ⟨123683, by rfl⟩ : syracuseStep 164911 = 247367) B247367
theorem B328895 : Blo 143792 328895 := bstep (se 1 (by rfl) ⟨246671, by rfl⟩ : syracuseStep 328895 = 493343) B493343
theorem B165055 : Blo 143792 165055 := bstep (se 1 (by rfl) ⟨123791, by rfl⟩ : syracuseStep 165055 = 247583) B247583
theorem B230635 : Blo 143792 230635 := bstep (se 1 (by rfl) ⟨172976, by rfl⟩ : syracuseStep 230635 = 345953) B345953
theorem B329039 : Blo 143792 329039 := bstep (se 1 (by rfl) ⟨246779, by rfl⟩ : syracuseStep 329039 = 493559) B493559
theorem B165199 : Blo 143792 165199 := bstep (se 1 (by rfl) ⟨123899, by rfl⟩ : syracuseStep 165199 = 247799) B247799
theorem B623963 : Blo 143792 623963 := bstep (se 1 (by rfl) ⟨467972, by rfl⟩ : syracuseStep 623963 = 935945) B935945
theorem B329129 : Blo 143792 329129 := bstep (se 2 (by rfl) ⟨123423, by rfl⟩ : syracuseStep 329129 = 246847) B246847
theorem B952067 : Blo 143792 952067 := bstep (se 1 (by rfl) ⟨714050, by rfl⟩ : syracuseStep 952067 = 1428101) B1428101
theorem B329615 : Blo 143792 329615 := bstep (se 1 (by rfl) ⟨247211, by rfl⟩ : syracuseStep 329615 = 494423) B494423
theorem B657353 : Blo 143792 657353 := bstep (se 2 (by rfl) ⟨246507, by rfl⟩ : syracuseStep 657353 = 493015) B493015
theorem B10192877 : Blo 143792 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B231455 : Blo 143792 231455 := bstep (se 1 (by rfl) ⟨173591, by rfl⟩ : syracuseStep 231455 = 347183) B347183
theorem B329759 : Blo 143792 329759 := bstep (se 1 (by rfl) ⟨247319, by rfl⟩ : syracuseStep 329759 = 494639) B494639
theorem B165919 : Blo 143792 165919 := bstep (se 1 (by rfl) ⟨124439, by rfl⟩ : syracuseStep 165919 = 248879) B248879
theorem B3999955 : Blo 143792 3999955 := bstep (se 1 (by rfl) ⟨2999966, by rfl⟩ : syracuseStep 3999955 = 5999933) B5999933
theorem B330011 : Blo 143792 330011 := bstep (se 1 (by rfl) ⟨247508, by rfl⟩ : syracuseStep 330011 = 495017) B495017
theorem B166171 : Blo 143792 166171 := bstep (se 1 (by rfl) ⟨124628, by rfl⟩ : syracuseStep 166171 = 249257) B249257
theorem B985483 : Blo 143792 985483 := bstep (se 1 (by rfl) ⟨739112, by rfl⟩ : syracuseStep 985483 = 1478225) B1478225
theorem B4786613 : Blo 143792 4786613 := bstep (se 5 (by rfl) ⟨224372, by rfl⟩ : syracuseStep 4786613 = 448745) B448745
theorem B330335 : Blo 143792 330335 := bstep (se 1 (by rfl) ⟨247751, by rfl⟩ : syracuseStep 330335 = 495503) B495503
theorem B330587 : Blo 143792 330587 := bstep (se 1 (by rfl) ⟨247940, by rfl⟩ : syracuseStep 330587 = 495881) B495881
theorem B494495 : Blo 143792 494495 := bstep (se 1 (by rfl) ⟨370871, by rfl⟩ : syracuseStep 494495 = 741743) B741743
theorem B625603 : Blo 143792 625603 := bstep (se 1 (by rfl) ⟨469202, by rfl⟩ : syracuseStep 625603 = 938405) B938405
theorem B199675 : Blo 143792 199675 := bstep (se 1 (by rfl) ⟨149756, by rfl⟩ : syracuseStep 199675 = 299513) B299513
theorem B560479 : Blo 143792 560479 := bstep (se 1 (by rfl) ⟨420359, by rfl⟩ : syracuseStep 560479 = 840719) B840719
theorem B4492793 : Blo 143792 4492793 := bstep (se 2 (by rfl) ⟨1684797, by rfl⟩ : syracuseStep 4492793 = 3369595) B3369595
theorem B331343 : Blo 143792 331343 := bstep (se 1 (by rfl) ⟨248507, by rfl⟩ : syracuseStep 331343 = 497015) B497015
theorem B495719 : Blo 143792 495719 := bstep (se 1 (by rfl) ⟨371789, by rfl⟩ : syracuseStep 495719 = 743579) B743579
theorem B331883 : Blo 143792 331883 := bstep (se 1 (by rfl) ⟨248912, by rfl⟩ : syracuseStep 331883 = 497825) B497825
theorem B626849 : Blo 143792 626849 := bstep (se 2 (by rfl) ⟨235068, by rfl⟩ : syracuseStep 626849 = 470137) B470137
theorem B331937 : Blo 143792 331937 := bstep (se 2 (by rfl) ⟨124476, by rfl⟩ : syracuseStep 331937 = 248953) B248953
theorem B332063 : Blo 143792 332063 := bstep (se 1 (by rfl) ⟨249047, by rfl⟩ : syracuseStep 332063 = 498095) B498095
theorem B1184327 : Blo 143792 1184327 := bstep (se 1 (by rfl) ⟨888245, by rfl⟩ : syracuseStep 1184327 = 1776491) B1776491
theorem B1774153 : Blo 143792 1774153 := bstep (se 2 (by rfl) ⟨665307, by rfl⟩ : syracuseStep 1774153 = 1330615) B1330615
theorem B1479505 : Blo 143792 1479505 := bstep (se 2 (by rfl) ⟨554814, by rfl⟩ : syracuseStep 1479505 = 1109629) B1109629
theorem B365593 : Blo 143792 365593 := bstep (se 2 (by rfl) ⟨137097, by rfl⟩ : syracuseStep 365593 = 274195) B274195
theorem B922823 : Blo 143792 922823 := bstep (se 1 (by rfl) ⟨692117, by rfl⟩ : syracuseStep 922823 = 1384235) B1384235
theorem B497231 : Blo 143792 497231 := bstep (se 1 (by rfl) ⟨372923, by rfl⟩ : syracuseStep 497231 = 745847) B745847
theorem B890579 : Blo 143792 890579 := bstep (se 1 (by rfl) ⟨667934, by rfl⟩ : syracuseStep 890579 = 1335869) B1335869
theorem B497609 : Blo 143792 497609 := bstep (se 2 (by rfl) ⟨186603, by rfl⟩ : syracuseStep 497609 = 373207) B373207
theorem B497879 : Blo 143792 497879 := bstep (se 1 (by rfl) ⟨373409, by rfl⟩ : syracuseStep 497879 = 746819) B746819
theorem B2792069 : Blo 143792 2792069 := bstep (se 4 (by rfl) ⟨261756, by rfl⟩ : syracuseStep 2792069 = 523513) B523513
theorem B498419 : Blo 143792 498419 := bstep (se 1 (by rfl) ⟨373814, by rfl⟩ : syracuseStep 498419 = 747629) B747629
theorem B531211 : Blo 143792 531211 := bstep (se 1 (by rfl) ⟨398408, by rfl⟩ : syracuseStep 531211 = 796817) B796817
theorem B10623899 : Blo 143792 10623899 := bstep (se 1 (by rfl) ⟨7967924, by rfl⟩ : syracuseStep 10623899 = 15935849) B15935849
theorem B2989619 : Blo 143792 2989619 := bstep (se 1 (by rfl) ⟨2242214, by rfl⟩ : syracuseStep 2989619 = 4484429) B4484429
theorem B368347 : Blo 143792 368347 := bstep (se 1 (by rfl) ⟨276260, by rfl⟩ : syracuseStep 368347 = 552521) B552521
theorem B466651 : Blo 143792 466651 := bstep (se 1 (by rfl) ⟨349988, by rfl⟩ : syracuseStep 466651 = 699977) B699977
theorem B1580791 : Blo 143792 1580791 := bstep (se 1 (by rfl) ⟨1185593, by rfl⟩ : syracuseStep 1580791 = 2371187) B2371187
theorem B794569 : Blo 143792 794569 := bstep (se 2 (by rfl) ⟨297963, by rfl⟩ : syracuseStep 794569 = 595927) B595927
theorem B631223 : Blo 143792 631223 := bstep (se 1 (by rfl) ⟨473417, by rfl⟩ : syracuseStep 631223 = 946835) B946835
theorem B336377 : Blo 143792 336377 := bstep (se 2 (by rfl) ⟨126141, by rfl⟩ : syracuseStep 336377 = 252283) B252283
theorem B697403 : Blo 143792 697403 := bstep (se 1 (by rfl) ⟨523052, by rfl⟩ : syracuseStep 697403 = 1046105) B1046105
theorem B369785 : Blo 143792 369785 := bstep (se 2 (by rfl) ⟨138669, by rfl⟩ : syracuseStep 369785 = 277339) B277339
theorem B730943 : Blo 143792 730943 := bstep (se 1 (by rfl) ⟨548207, by rfl⟩ : syracuseStep 730943 = 1096415) B1096415
theorem B2140219 : Blo 143792 2140219 := bstep (se 1 (by rfl) ⟨1605164, by rfl⟩ : syracuseStep 2140219 = 3210329) B3210329
theorem B1321273 : Blo 143792 1321273 := bstep (se 2 (by rfl) ⟨495477, by rfl⟩ : syracuseStep 1321273 = 990955) B990955
theorem B1092041 : Blo 143792 1092041 := bstep (se 2 (by rfl) ⟨409515, by rfl⟩ : syracuseStep 1092041 = 819031) B819031
theorem B469727 : Blo 143792 469727 := bstep (se 1 (by rfl) ⟨352295, by rfl⟩ : syracuseStep 469727 = 704591) B704591
theorem B470087 : Blo 143792 470087 := bstep (se 1 (by rfl) ⟨352565, by rfl⟩ : syracuseStep 470087 = 705131) B705131
theorem B372023 : Blo 143792 372023 := bstep (se 1 (by rfl) ⟨279017, by rfl⟩ : syracuseStep 372023 = 558035) B558035
theorem B733049 : Blo 143792 733049 := bstep (se 2 (by rfl) ⟨274893, by rfl⟩ : syracuseStep 733049 = 549787) B549787
theorem B700285 : Blo 143792 700285 := bstep (se 3 (by rfl) ⟨131303, by rfl⟩ : syracuseStep 700285 = 262607) B262607
theorem B372863 : Blo 143792 372863 := bstep (se 1 (by rfl) ⟨279647, by rfl⟩ : syracuseStep 372863 = 559295) B559295
theorem B144123 : Blo 143792 144123 := bstep (se 1 (by rfl) ⟨108092, by rfl⟩ : syracuseStep 144123 = 216185) B216185
theorem B9679661 : Blo 143792 9679661 := bstep (se 3 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 9679661 = 3629873) B3629873
theorem B144191 : Blo 143792 144191 := bstep (se 1 (by rfl) ⟨108143, by rfl⟩ : syracuseStep 144191 = 216287) B216287
theorem B144219 : Blo 143792 144219 := bstep (se 1 (by rfl) ⟨108164, by rfl⟩ : syracuseStep 144219 = 216329) B216329
theorem B144287 : Blo 143792 144287 := bstep (se 1 (by rfl) ⟨108215, by rfl⟩ : syracuseStep 144287 = 216431) B216431
theorem B1684435 : Blo 143792 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B144367 : Blo 143792 144367 := bstep (se 1 (by rfl) ⟨108275, by rfl⟩ : syracuseStep 144367 = 216551) B216551
theorem B144455 : Blo 143792 144455 := bstep (se 1 (by rfl) ⟨108341, by rfl⟩ : syracuseStep 144455 = 216683) B216683
theorem B144539 : Blo 143792 144539 := bstep (se 1 (by rfl) ⟨108404, by rfl⟩ : syracuseStep 144539 = 216809) B216809
theorem B242939 : Blo 143792 242939 := bstep (se 1 (by rfl) ⟨182204, by rfl⟩ : syracuseStep 242939 = 364409) B364409
theorem B144635 : Blo 143792 144635 := bstep (se 1 (by rfl) ⟨108476, by rfl⟩ : syracuseStep 144635 = 216953) B216953
theorem B144703 : Blo 143792 144703 := bstep (se 1 (by rfl) ⟨108527, by rfl⟩ : syracuseStep 144703 = 217055) B217055
theorem B144871 : Blo 143792 144871 := bstep (se 1 (by rfl) ⟨108653, by rfl⟩ : syracuseStep 144871 = 217307) B217307
theorem B144879 : Blo 143792 144879 := bstep (se 1 (by rfl) ⟨108659, by rfl⟩ : syracuseStep 144879 = 217319) B217319
theorem B144987 : Blo 143792 144987 := bstep (se 1 (by rfl) ⟨108740, by rfl⟩ : syracuseStep 144987 = 217481) B217481
theorem B145051 : Blo 143792 145051 := bstep (se 1 (by rfl) ⟨108788, by rfl⟩ : syracuseStep 145051 = 217577) B217577
theorem B145135 : Blo 143792 145135 := bstep (se 1 (by rfl) ⟨108851, by rfl⟩ : syracuseStep 145135 = 217703) B217703
theorem B145223 : Blo 143792 145223 := bstep (se 1 (by rfl) ⟨108917, by rfl⟩ : syracuseStep 145223 = 217835) B217835
theorem B145243 : Blo 143792 145243 := bstep (se 1 (by rfl) ⟨108932, by rfl⟩ : syracuseStep 145243 = 217865) B217865
theorem B145311 : Blo 143792 145311 := bstep (se 1 (by rfl) ⟨108983, by rfl⟩ : syracuseStep 145311 = 217967) B217967
theorem B145479 : Blo 143792 145479 := bstep (se 1 (by rfl) ⟨109109, by rfl⟩ : syracuseStep 145479 = 218219) B218219
theorem B637067 : Blo 143792 637067 := bstep (se 1 (by rfl) ⟨477800, by rfl⟩ : syracuseStep 637067 = 955601) B955601
theorem B276671 : Blo 143792 276671 := bstep (se 1 (by rfl) ⟨207503, by rfl⟩ : syracuseStep 276671 = 415007) B415007
theorem B145639 : Blo 143792 145639 := bstep (se 1 (by rfl) ⟨109229, by rfl⟩ : syracuseStep 145639 = 218459) B218459
theorem B1095929 : Blo 143792 1095929 := bstep (se 2 (by rfl) ⟨410973, by rfl⟩ : syracuseStep 1095929 = 821947) B821947
theorem B145823 : Blo 143792 145823 := bstep (se 1 (by rfl) ⟨109367, by rfl⟩ : syracuseStep 145823 = 218735) B218735
theorem B145871 : Blo 143792 145871 := bstep (se 1 (by rfl) ⟨109403, by rfl⟩ : syracuseStep 145871 = 218807) B218807
theorem B145895 : Blo 143792 145895 := bstep (se 1 (by rfl) ⟨109421, by rfl⟩ : syracuseStep 145895 = 218843) B218843
theorem B146011 : Blo 143792 146011 := bstep (se 1 (by rfl) ⟨109508, by rfl⟩ : syracuseStep 146011 = 219017) B219017
theorem B146079 : Blo 143792 146079 := bstep (se 1 (by rfl) ⟨109559, by rfl⟩ : syracuseStep 146079 = 219119) B219119
theorem B146247 : Blo 143792 146247 := bstep (se 1 (by rfl) ⟨109685, by rfl⟩ : syracuseStep 146247 = 219371) B219371
theorem B146287 : Blo 143792 146287 := bstep (se 1 (by rfl) ⟨109715, by rfl⟩ : syracuseStep 146287 = 219431) B219431
theorem B2177945 : Blo 143792 2177945 := bstep (se 2 (by rfl) ⟨816729, by rfl⟩ : syracuseStep 2177945 = 1633459) B1633459
theorem B277415 : Blo 143792 277415 := bstep (se 1 (by rfl) ⟨208061, by rfl⟩ : syracuseStep 277415 = 416123) B416123
theorem B146343 : Blo 143792 146343 := bstep (se 1 (by rfl) ⟨109757, by rfl⟩ : syracuseStep 146343 = 219515) B219515
theorem B146523 : Blo 143792 146523 := bstep (se 1 (by rfl) ⟨109892, by rfl⟩ : syracuseStep 146523 = 219785) B219785
theorem B146639 : Blo 143792 146639 := bstep (se 1 (by rfl) ⟨109979, by rfl⟩ : syracuseStep 146639 = 219959) B219959
theorem B146663 : Blo 143792 146663 := bstep (se 1 (by rfl) ⟨109997, by rfl⟩ : syracuseStep 146663 = 219995) B219995
theorem B146759 : Blo 143792 146759 := bstep (se 1 (by rfl) ⟨110069, by rfl⟩ : syracuseStep 146759 = 220139) B220139
theorem B933281 : Blo 143792 933281 := bstep (se 2 (by rfl) ⟨349980, by rfl⟩ : syracuseStep 933281 = 699961) B699961
theorem B277931 : Blo 143792 277931 := bstep (se 1 (by rfl) ⟨208448, by rfl⟩ : syracuseStep 277931 = 416897) B416897
theorem B146895 : Blo 143792 146895 := bstep (se 1 (by rfl) ⟨110171, by rfl⟩ : syracuseStep 146895 = 220343) B220343
theorem B147055 : Blo 143792 147055 := bstep (se 1 (by rfl) ⟨110291, by rfl⟩ : syracuseStep 147055 = 220583) B220583
theorem B147111 : Blo 143792 147111 := bstep (se 1 (by rfl) ⟨110333, by rfl⟩ : syracuseStep 147111 = 220667) B220667
theorem B147175 : Blo 143792 147175 := bstep (se 1 (by rfl) ⟨110381, by rfl⟩ : syracuseStep 147175 = 220763) B220763
theorem B147231 : Blo 143792 147231 := bstep (se 1 (by rfl) ⟨110423, by rfl⟩ : syracuseStep 147231 = 220847) B220847
theorem B278311 : Blo 143792 278311 := bstep (se 1 (by rfl) ⟨208733, by rfl⟩ : syracuseStep 278311 = 417467) B417467
theorem B147311 : Blo 143792 147311 := bstep (se 1 (by rfl) ⟨110483, by rfl⟩ : syracuseStep 147311 = 220967) B220967
theorem B147367 : Blo 143792 147367 := bstep (se 1 (by rfl) ⟨110525, by rfl⟩ : syracuseStep 147367 = 221051) B221051
theorem B278471 : Blo 143792 278471 := bstep (se 1 (by rfl) ⟨208853, by rfl⟩ : syracuseStep 278471 = 417707) B417707
theorem B737261 : Blo 143792 737261 := bstep (se 3 (by rfl) ⟨138236, by rfl⟩ : syracuseStep 737261 = 276473) B276473
theorem B147647 : Blo 143792 147647 := bstep (se 1 (by rfl) ⟨110735, by rfl⟩ : syracuseStep 147647 = 221471) B221471
theorem B147663 : Blo 143792 147663 := bstep (se 1 (by rfl) ⟨110747, by rfl⟩ : syracuseStep 147663 = 221495) B221495
theorem B409835 : Blo 143792 409835 := bstep (se 1 (by rfl) ⟨307376, by rfl⟩ : syracuseStep 409835 = 614753) B614753
theorem B147711 : Blo 143792 147711 := bstep (se 1 (by rfl) ⟨110783, by rfl⟩ : syracuseStep 147711 = 221567) B221567
theorem B147759 : Blo 143792 147759 := bstep (se 1 (by rfl) ⟨110819, by rfl⟩ : syracuseStep 147759 = 221639) B221639
theorem B1196495 : Blo 143792 1196495 := bstep (se 1 (by rfl) ⟨897371, by rfl⟩ : syracuseStep 1196495 = 1794743) B1794743
theorem B26690147 : Blo 143792 26690147 := bstep (se 1 (by rfl) ⟨20017610, by rfl⟩ : syracuseStep 26690147 = 40035221) B40035221
theorem B2638615 : Blo 143792 2638615 := bstep (se 1 (by rfl) ⟨1978961, by rfl⟩ : syracuseStep 2638615 = 3957923) B3957923
theorem B738071 : Blo 143792 738071 := bstep (se 1 (by rfl) ⟨553553, by rfl⟩ : syracuseStep 738071 = 1107107) B1107107
theorem B312263 : Blo 143792 312263 := bstep (se 1 (by rfl) ⟨234197, by rfl⟩ : syracuseStep 312263 = 468395) B468395
theorem B410633 : Blo 143792 410633 := bstep (se 2 (by rfl) ⟨153987, by rfl⟩ : syracuseStep 410633 = 307975) B307975
theorem B1230187 : Blo 143792 1230187 := bstep (se 1 (by rfl) ⟨922640, by rfl⟩ : syracuseStep 1230187 = 1845281) B1845281
theorem B280255 : Blo 143792 280255 := bstep (se 1 (by rfl) ⟨210191, by rfl⟩ : syracuseStep 280255 = 420383) B420383
theorem B1132319 : Blo 143792 1132319 := bstep (se 1 (by rfl) ⟨849239, by rfl⟩ : syracuseStep 1132319 = 1698479) B1698479
theorem B280559 : Blo 143792 280559 := bstep (se 1 (by rfl) ⟨210419, by rfl⟩ : syracuseStep 280559 = 420839) B420839
theorem B248143 : Blo 143792 248143 := bstep (se 1 (by rfl) ⟨186107, by rfl⟩ : syracuseStep 248143 = 372215) B372215
theorem B739691 : Blo 143792 739691 := bstep (se 1 (by rfl) ⟨554768, by rfl⟩ : syracuseStep 739691 = 1109537) B1109537
theorem B838259 : Blo 143792 838259 := bstep (se 1 (by rfl) ⟨628694, by rfl⟩ : syracuseStep 838259 = 1257389) B1257389
theorem B4770515 : Blo 143792 4770515 := bstep (se 1 (by rfl) ⟨3577886, by rfl⟩ : syracuseStep 4770515 = 7155773) B7155773
theorem B215849 : Blo 143792 215849 := bstep (se 2 (by rfl) ⟨80943, by rfl⟩ : syracuseStep 215849 = 161887) B161887
theorem B216059 : Blo 143792 216059 := bstep (se 1 (by rfl) ⟨162044, by rfl⟩ : syracuseStep 216059 = 324089) B324089
theorem B216119 : Blo 143792 216119 := bstep (se 1 (by rfl) ⟨162089, by rfl⟩ : syracuseStep 216119 = 324179) B324179
theorem B216239 : Blo 143792 216239 := bstep (se 1 (by rfl) ⟨162179, by rfl⟩ : syracuseStep 216239 = 324359) B324359
theorem B249007 : Blo 143792 249007 := bstep (se 1 (by rfl) ⟨186755, by rfl⟩ : syracuseStep 249007 = 373511) B373511
theorem B8801459 : Blo 143792 8801459 := bstep (se 1 (by rfl) ⟨6601094, by rfl⟩ : syracuseStep 8801459 = 13202189) B13202189
theorem B314579 : Blo 143792 314579 := bstep (se 1 (by rfl) ⟨235934, by rfl⟩ : syracuseStep 314579 = 471869) B471869
theorem B115953443 : Blo 143792 115953443 := bstep (se 1 (by rfl) ⟨86965082, by rfl⟩ : syracuseStep 115953443 = 173930165) B173930165
theorem B216959 : Blo 143792 216959 := bstep (se 1 (by rfl) ⟨162719, by rfl⟩ : syracuseStep 216959 = 325439) B325439
theorem B348143 : Blo 143792 348143 := bstep (se 1 (by rfl) ⟨261107, by rfl⟩ : syracuseStep 348143 = 522215) B522215
theorem B217151 : Blo 143792 217151 := bstep (se 1 (by rfl) ⟨162863, by rfl⟩ : syracuseStep 217151 = 325727) B325727
theorem B5099719 : Blo 143792 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B217385 : Blo 143792 217385 := bstep (se 2 (by rfl) ⟨81519, by rfl⟩ : syracuseStep 217385 = 163039) B163039
theorem B217655 : Blo 143792 217655 := bstep (se 1 (by rfl) ⟨163241, by rfl⟩ : syracuseStep 217655 = 326483) B326483
theorem B218015 : Blo 143792 218015 := bstep (se 1 (by rfl) ⟨163511, by rfl⟩ : syracuseStep 218015 = 327023) B327023
theorem B1496045 : Blo 143792 1496045 := bstep (se 3 (by rfl) ⟨280508, by rfl⟩ : syracuseStep 1496045 = 561017) B561017
theorem B218207 : Blo 143792 218207 := bstep (se 1 (by rfl) ⟨163655, by rfl⟩ : syracuseStep 218207 = 327311) B327311
theorem B218267 : Blo 143792 218267 := bstep (se 1 (by rfl) ⟨163700, by rfl⟩ : syracuseStep 218267 = 327401) B327401
theorem B6674177 : Blo 143792 6674177 := bstep (se 2 (by rfl) ⟨2502816, by rfl⟩ : syracuseStep 6674177 = 5005633) B5005633
theorem B218951 : Blo 143792 218951 := bstep (se 1 (by rfl) ⟨164213, by rfl⟩ : syracuseStep 218951 = 328427) B328427
theorem B743417 : Blo 143792 743417 := bstep (se 2 (by rfl) ⟨278781, by rfl⟩ : syracuseStep 743417 = 557563) B557563
theorem B153671 : Blo 143792 153671 := bstep (se 1 (by rfl) ⟨115253, by rfl⟩ : syracuseStep 153671 = 230507) B230507
theorem B1038433 : Blo 143792 1038433 := bstep (se 2 (by rfl) ⟨389412, by rfl⟩ : syracuseStep 1038433 = 778825) B778825
theorem B219551 : Blo 143792 219551 := bstep (se 1 (by rfl) ⟨164663, by rfl⟩ : syracuseStep 219551 = 329327) B329327
theorem B219623 : Blo 143792 219623 := bstep (se 1 (by rfl) ⟨164717, by rfl⟩ : syracuseStep 219623 = 329435) B329435
theorem B940531 : Blo 143792 940531 := bstep (se 1 (by rfl) ⟨705398, by rfl⟩ : syracuseStep 940531 = 1410797) B1410797
theorem B351211 : Blo 143792 351211 := bstep (se 1 (by rfl) ⟨263408, by rfl⟩ : syracuseStep 351211 = 526817) B526817
theorem B220367 : Blo 143792 220367 := bstep (se 1 (by rfl) ⟨165275, by rfl⟩ : syracuseStep 220367 = 330551) B330551
theorem B220487 : Blo 143792 220487 := bstep (se 1 (by rfl) ⟨165365, by rfl⟩ : syracuseStep 220487 = 330731) B330731
theorem B548329 : Blo 143792 548329 := bstep (se 2 (by rfl) ⟨205623, by rfl⟩ : syracuseStep 548329 = 411247) B411247
theorem B417257 : Blo 143792 417257 := bstep (se 2 (by rfl) ⟨156471, by rfl⟩ : syracuseStep 417257 = 312943) B312943
theorem B220649 : Blo 143792 220649 := bstep (se 2 (by rfl) ⟨82743, by rfl⟩ : syracuseStep 220649 = 165487) B165487
theorem B220793 : Blo 143792 220793 := bstep (se 2 (by rfl) ⟨82797, by rfl⟩ : syracuseStep 220793 = 165595) B165595
theorem B351911 : Blo 143792 351911 := bstep (se 1 (by rfl) ⟨263933, by rfl⟩ : syracuseStep 351911 = 527867) B527867
theorem B221039 : Blo 143792 221039 := bstep (se 1 (by rfl) ⟨165779, by rfl⟩ : syracuseStep 221039 = 331559) B331559
theorem B549119 : Blo 143792 549119 := bstep (se 1 (by rfl) ⟨411839, by rfl⟩ : syracuseStep 549119 = 823679) B823679
theorem B549287 : Blo 143792 549287 := bstep (se 1 (by rfl) ⟨411965, by rfl⟩ : syracuseStep 549287 = 823931) B823931
theorem B156367 : Blo 143792 156367 := bstep (se 1 (by rfl) ⟨117275, by rfl⟩ : syracuseStep 156367 = 234551) B234551
theorem B615539 : Blo 143792 615539 := bstep (se 1 (by rfl) ⟨461654, by rfl⟩ : syracuseStep 615539 = 923309) B923309
theorem B616187 : Blo 143792 616187 := bstep (se 1 (by rfl) ⟨462140, by rfl⟩ : syracuseStep 616187 = 924281) B924281
theorem B157631 : Blo 143792 157631 := bstep (se 1 (by rfl) ⟨118223, by rfl⟩ : syracuseStep 157631 = 236447) B236447
theorem B485459 : Blo 143792 485459 := bstep (se 1 (by rfl) ⟨364094, by rfl⟩ : syracuseStep 485459 = 728189) B728189
theorem B10152053 : Blo 143792 10152053 := bstep (se 5 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 10152053 = 951755) B951755
theorem B845959 : Blo 143792 845959 := bstep (se 1 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 845959 = 1268939) B1268939
theorem B3795335 : Blo 143792 3795335 := bstep (se 1 (by rfl) ⟨2846501, by rfl⟩ : syracuseStep 3795335 = 5693003) B5693003
theorem B551549 : Blo 143792 551549 := bstep (se 3 (by rfl) ⟨103415, by rfl⟩ : syracuseStep 551549 = 206831) B206831
theorem B1174601 : Blo 143792 1174601 := bstep (se 2 (by rfl) ⟨440475, by rfl⟩ : syracuseStep 1174601 = 880951) B880951
theorem B552217 : Blo 143792 552217 := bstep (se 2 (by rfl) ⟨207081, by rfl⟩ : syracuseStep 552217 = 414163) B414163
theorem B1666493 : Blo 143792 1666493 := bstep (se 3 (by rfl) ⟨312467, by rfl⟩ : syracuseStep 1666493 = 624935) B624935
theorem B2158289 : Blo 143792 2158289 := bstep (se 2 (by rfl) ⟨809358, by rfl⟩ : syracuseStep 2158289 = 1618717) B1618717
theorem B323657 : Blo 143792 323657 := bstep (se 2 (by rfl) ⟨121371, by rfl⟩ : syracuseStep 323657 = 242743) B242743
theorem B323711 : Blo 143792 323711 := bstep (se 1 (by rfl) ⟨242783, by rfl⟩ : syracuseStep 323711 = 485567) B485567
theorem B1864225 : Blo 143792 1864225 := bstep (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) B1398169
theorem B389867 : Blo 143792 389867 := bstep (se 1 (by rfl) ⟨292400, by rfl⟩ : syracuseStep 389867 = 584801) B584801
theorem B1569719 : Blo 143792 1569719 := bstep (se 1 (by rfl) ⟨1177289, by rfl⟩ : syracuseStep 1569719 = 2354579) B2354579
theorem B7074809 : Blo 143792 7074809 := bstep (se 2 (by rfl) ⟨2653053, by rfl⟩ : syracuseStep 7074809 = 5306107) B5306107
theorem B324791 : Blo 143792 324791 := bstep (se 1 (by rfl) ⟨243593, by rfl⟩ : syracuseStep 324791 = 487187) B487187
theorem B718247 : Blo 143792 718247 := bstep (se 1 (by rfl) ⟨538685, by rfl⟩ : syracuseStep 718247 = 1077371) B1077371
theorem B554435 : Blo 143792 554435 := bstep (se 1 (by rfl) ⟨415826, by rfl⟩ : syracuseStep 554435 = 831653) B831653
theorem B488915 : Blo 143792 488915 := bstep (se 1 (by rfl) ⟨366686, by rfl⟩ : syracuseStep 488915 = 733373) B733373
theorem B554465 : Blo 143792 554465 := bstep (se 2 (by rfl) ⟨207924, by rfl⟩ : syracuseStep 554465 = 415849) B415849
theorem B489185 : Blo 143792 489185 := bstep (se 2 (by rfl) ⟨183444, by rfl⟩ : syracuseStep 489185 = 366889) B366889
theorem B325367 : Blo 143792 325367 := bstep (se 1 (by rfl) ⟨244025, by rfl⟩ : syracuseStep 325367 = 488051) B488051
theorem B325547 : Blo 143792 325547 := bstep (se 1 (by rfl) ⟨244160, by rfl⟩ : syracuseStep 325547 = 488321) B488321
theorem B554951 : Blo 143792 554951 := bstep (se 1 (by rfl) ⟨416213, by rfl⟩ : syracuseStep 554951 = 832427) B832427
theorem B325673 : Blo 143792 325673 := bstep (se 2 (by rfl) ⟨122127, by rfl⟩ : syracuseStep 325673 = 244255) B244255
theorem B326087 : Blo 143792 326087 := bstep (se 1 (by rfl) ⟨244565, by rfl⟩ : syracuseStep 326087 = 489131) B489131
theorem B326249 : Blo 143792 326249 := bstep (se 2 (by rfl) ⟨122343, by rfl⟩ : syracuseStep 326249 = 244687) B244687
theorem B162463 : Blo 143792 162463 := bstep (se 1 (by rfl) ⟨121847, by rfl⟩ : syracuseStep 162463 = 243695) B243695
theorem B326303 : Blo 143792 326303 := bstep (se 1 (by rfl) ⟨244727, by rfl⟩ : syracuseStep 326303 = 489455) B489455
theorem B326447 : Blo 143792 326447 := bstep (se 1 (by rfl) ⟨244835, by rfl⟩ : syracuseStep 326447 = 489671) B489671
theorem B326879 : Blo 143792 326879 := bstep (se 1 (by rfl) ⟨245159, by rfl⟩ : syracuseStep 326879 = 490319) B490319
theorem B327095 : Blo 143792 327095 := bstep (se 1 (by rfl) ⟨245321, by rfl⟩ : syracuseStep 327095 = 490643) B490643
theorem B1244645 : Blo 143792 1244645 := bstep (se 4 (by rfl) ⟨116685, by rfl⟩ : syracuseStep 1244645 = 233371) B233371
theorem B327275 : Blo 143792 327275 := bstep (se 1 (by rfl) ⟨245456, by rfl⟩ : syracuseStep 327275 = 490913) B490913
theorem B2227823 : Blo 143792 2227823 := bstep (se 1 (by rfl) ⟨1670867, by rfl⟩ : syracuseStep 2227823 = 3341735) B3341735
theorem B491183 : Blo 143792 491183 := bstep (se 1 (by rfl) ⟨368387, by rfl⟩ : syracuseStep 491183 = 736775) B736775
theorem B1670867 : Blo 143792 1670867 := bstep (se 1 (by rfl) ⟨1253150, by rfl⟩ : syracuseStep 1670867 = 2506301) B2506301
theorem B163615 : Blo 143792 163615 := bstep (se 1 (by rfl) ⟨122711, by rfl⟩ : syracuseStep 163615 = 245423) B245423
theorem B5668703 : Blo 143792 5668703 := bstep (se 1 (by rfl) ⟨4251527, by rfl⟩ : syracuseStep 5668703 = 8503055) B8503055
theorem B327545 : Blo 143792 327545 := bstep (se 2 (by rfl) ⟨122829, by rfl⟩ : syracuseStep 327545 = 245659) B245659
theorem B196519 : Blo 143792 196519 := bstep (se 1 (by rfl) ⟨147389, by rfl⟩ : syracuseStep 196519 = 294779) B294779
theorem B327635 : Blo 143792 327635 := bstep (se 1 (by rfl) ⟨245726, by rfl⟩ : syracuseStep 327635 = 491453) B491453
theorem B17793431 : Blo 143792 17793431 := bstep (se 1 (by rfl) ⟨13345073, by rfl⟩ : syracuseStep 17793431 = 26690147) B26690147
theorem B2097575 : Blo 143792 2097575 := bstep (se 1 (by rfl) ⟨1573181, by rfl⟩ : syracuseStep 2097575 = 3146363) B3146363
theorem B492047 : Blo 143792 492047 := bstep (se 1 (by rfl) ⟨369035, by rfl⟩ : syracuseStep 492047 = 738071) B738071
theorem B754879 : Blo 143792 754879 := bstep (se 1 (by rfl) ⟨566159, by rfl⟩ : syracuseStep 754879 = 1132319) B1132319
theorem B493127 : Blo 143792 493127 := bstep (se 1 (by rfl) ⟨369845, by rfl⟩ : syracuseStep 493127 = 739691) B739691
theorem B558839 : Blo 143792 558839 := bstep (se 1 (by rfl) ⟨419129, by rfl⟩ : syracuseStep 558839 = 838259) B838259
theorem B3180343 : Blo 143792 3180343 := bstep (se 1 (by rfl) ⟨2385257, by rfl⟩ : syracuseStep 3180343 = 4770515) B4770515
theorem B1640249 : Blo 143792 1640249 := bstep (se 2 (by rfl) ⟨615093, by rfl⟩ : syracuseStep 1640249 = 1230187) B1230187
theorem B329663 : Blo 143792 329663 := bstep (se 1 (by rfl) ⟨247247, by rfl⟩ : syracuseStep 329663 = 494495) B494495
theorem B5867639 : Blo 143792 5867639 := bstep (se 1 (by rfl) ⟨4400729, by rfl⟩ : syracuseStep 5867639 = 8801459) B8801459
theorem B77302295 : Blo 143792 77302295 := bstep (se 1 (by rfl) ⟨57976721, by rfl⟩ : syracuseStep 77302295 = 115953443) B115953443
theorem B330479 : Blo 143792 330479 := bstep (se 1 (by rfl) ⟨247859, by rfl⟩ : syracuseStep 330479 = 495719) B495719
theorem B2853625 : Blo 143792 2853625 := bstep (se 2 (by rfl) ⟨1070109, by rfl⟩ : syracuseStep 2853625 = 2140219) B2140219
theorem B789551 : Blo 143792 789551 := bstep (se 1 (by rfl) ⟨592163, by rfl⟩ : syracuseStep 789551 = 1184327) B1184327
theorem B330857 : Blo 143792 330857 := bstep (se 2 (by rfl) ⟨124071, by rfl⟩ : syracuseStep 330857 = 248143) B248143
theorem B1313977 : Blo 143792 1313977 := bstep (se 2 (by rfl) ⟨492741, by rfl⟩ : syracuseStep 1313977 = 985483) B985483
theorem B331487 : Blo 143792 331487 := bstep (se 1 (by rfl) ⟨248615, by rfl⟩ : syracuseStep 331487 = 497231) B497231
theorem B331739 : Blo 143792 331739 := bstep (se 1 (by rfl) ⟨248804, by rfl⟩ : syracuseStep 331739 = 497609) B497609
theorem B495611 : Blo 143792 495611 := bstep (se 1 (by rfl) ⟨371708, by rfl⟩ : syracuseStep 495611 = 743417) B743417
theorem B331919 : Blo 143792 331919 := bstep (se 1 (by rfl) ⟨248939, by rfl⟩ : syracuseStep 331919 = 497879) B497879
theorem B332009 : Blo 143792 332009 := bstep (se 2 (by rfl) ⟨124503, by rfl⟩ : syracuseStep 332009 = 249007) B249007
theorem B332279 : Blo 143792 332279 := bstep (se 1 (by rfl) ⟨249209, by rfl⟩ : syracuseStep 332279 = 498419) B498419
theorem B7082599 : Blo 143792 7082599 := bstep (se 1 (by rfl) ⟨5311949, by rfl⟩ : syracuseStep 7082599 = 10623899) B10623899
theorem B1643165 : Blo 143792 1643165 := bstep (se 3 (by rfl) ⟨308093, by rfl⟩ : syracuseStep 1643165 = 616187) B616187
theorem B366079 : Blo 143792 366079 := bstep (se 1 (by rfl) ⟨274559, by rfl⟩ : syracuseStep 366079 = 549119) B549119
theorem B366191 : Blo 143792 366191 := bstep (se 1 (by rfl) ⟨274643, by rfl⟩ : syracuseStep 366191 = 549287) B549287
theorem B464935 : Blo 143792 464935 := bstep (se 1 (by rfl) ⟨348701, by rfl⟩ : syracuseStep 464935 = 697403) B697403
theorem B2365537 : Blo 143792 2365537 := bstep (se 2 (by rfl) ⟨887076, by rfl⟩ : syracuseStep 2365537 = 1774153) B1774153
theorem B1972673 : Blo 143792 1972673 := bstep (se 2 (by rfl) ⟨739752, by rfl⟩ : syracuseStep 1972673 = 1479505) B1479505
theorem B2530223 : Blo 143792 2530223 := bstep (se 1 (by rfl) ⟨1897667, by rfl⟩ : syracuseStep 2530223 = 3795335) B3795335
theorem B728027 : Blo 143792 728027 := bstep (se 1 (by rfl) ⟨546020, by rfl⟩ : syracuseStep 728027 = 1092041) B1092041
theorem B367699 : Blo 143792 367699 := bstep (se 1 (by rfl) ⟨275774, by rfl⟩ : syracuseStep 367699 = 551549) B551549
theorem B1384577 : Blo 143792 1384577 := bstep (se 2 (by rfl) ⟨519216, by rfl⟩ : syracuseStep 1384577 = 1038433) B1038433
theorem B1254041 : Blo 143792 1254041 := bstep (se 2 (by rfl) ⟨470265, by rfl⟩ : syracuseStep 1254041 = 940531) B940531
theorem B369623 : Blo 143792 369623 := bstep (se 1 (by rfl) ⟨277217, by rfl⟩ : syracuseStep 369623 = 554435) B554435
theorem B369643 : Blo 143792 369643 := bstep (se 1 (by rfl) ⟨277232, by rfl⟩ : syracuseStep 369643 = 554465) B554465
theorem B369967 : Blo 143792 369967 := bstep (se 1 (by rfl) ⟨277475, by rfl⟩ : syracuseStep 369967 = 554951) B554951
theorem B468281 : Blo 143792 468281 := bstep (se 2 (by rfl) ⟨175605, by rfl⟩ : syracuseStep 468281 = 351211) B351211
theorem B730619 : Blo 143792 730619 := bstep (se 1 (by rfl) ⟨547964, by rfl⟩ : syracuseStep 730619 = 1095929) B1095929
theorem B1451963 : Blo 143792 1451963 := bstep (se 1 (by rfl) ⟨1088972, by rfl⟩ : syracuseStep 1451963 = 2177945) B2177945
theorem B731105 : Blo 143792 731105 := bstep (se 2 (by rfl) ⟨274164, by rfl⟩ : syracuseStep 731105 = 548329) B548329
theorem B829763 : Blo 143792 829763 := bstep (se 1 (by rfl) ⟨622322, by rfl⟩ : syracuseStep 829763 = 1244645) B1244645
theorem B2107721 : Blo 143792 2107721 := bstep (se 2 (by rfl) ⟨790395, by rfl⟩ : syracuseStep 2107721 = 1580791) B1580791
theorem B371081 : Blo 143792 371081 := bstep (se 2 (by rfl) ⟨139155, by rfl⟩ : syracuseStep 371081 = 278311) B278311
theorem B1485215 : Blo 143792 1485215 := bstep (se 1 (by rfl) ⟨1113911, by rfl⟩ : syracuseStep 1485215 = 2227823) B2227823
theorem B3713525 : Blo 143792 3713525 := bstep (se 5 (by rfl) ⟨174071, by rfl⟩ : syracuseStep 3713525 = 348143) B348143
theorem B3779135 : Blo 143792 3779135 := bstep (se 1 (by rfl) ⟨2834351, by rfl⟩ : syracuseStep 3779135 = 5668703) B5668703
theorem B1059425 : Blo 143792 1059425 := bstep (se 2 (by rfl) ⟨397284, by rfl⟩ : syracuseStep 1059425 = 794569) B794569
theorem B273223 : Blo 143792 273223 := bstep (se 1 (by rfl) ⟨204917, by rfl⟩ : syracuseStep 273223 = 409835) B409835
theorem B797663 : Blo 143792 797663 := bstep (se 1 (by rfl) ⟨598247, by rfl⟩ : syracuseStep 797663 = 1196495) B1196495
theorem B994301 : Blo 143792 994301 := bstep (se 3 (by rfl) ⟨186431, by rfl⟩ : syracuseStep 994301 = 372863) B372863
theorem B208175 : Blo 143792 208175 := bstep (se 1 (by rfl) ⟨156131, by rfl⟩ : syracuseStep 208175 = 312263) B312263
theorem B273755 : Blo 143792 273755 := bstep (se 1 (by rfl) ⟨205316, by rfl⟩ : syracuseStep 273755 = 410633) B410633
theorem B830969 : Blo 143792 830969 := bstep (se 2 (by rfl) ⟨311613, by rfl⟩ : syracuseStep 830969 = 623227) B623227
theorem B208489 : Blo 143792 208489 := bstep (se 2 (by rfl) ⟨78183, by rfl⟩ : syracuseStep 208489 = 156367) B156367
theorem B3518153 : Blo 143792 3518153 := bstep (se 2 (by rfl) ⟨1319307, by rfl⟩ : syracuseStep 3518153 = 2638615) B2638615
theorem B634711 : Blo 143792 634711 := bstep (se 1 (by rfl) ⟨476033, by rfl⟩ : syracuseStep 634711 = 952067) B952067
theorem B6795251 : Blo 143792 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B3191075 : Blo 143792 3191075 := bstep (se 1 (by rfl) ⟨2393306, by rfl⟩ : syracuseStep 3191075 = 4786613) B4786613
theorem B307513 : Blo 143792 307513 := bstep (se 2 (by rfl) ⟨115317, by rfl⟩ : syracuseStep 307513 = 230635) B230635
theorem B143899 : Blo 143792 143899 := bstep (se 1 (by rfl) ⟨107924, by rfl⟩ : syracuseStep 143899 = 215849) B215849
theorem B144039 : Blo 143792 144039 := bstep (se 1 (by rfl) ⟨108029, by rfl⟩ : syracuseStep 144039 = 216059) B216059
theorem B144079 : Blo 143792 144079 := bstep (se 1 (by rfl) ⟨108059, by rfl⟩ : syracuseStep 144079 = 216119) B216119
theorem B144159 : Blo 143792 144159 := bstep (se 1 (by rfl) ⟨108119, by rfl⟩ : syracuseStep 144159 = 216239) B216239
theorem B209719 : Blo 143792 209719 := bstep (se 1 (by rfl) ⟨157289, by rfl⟩ : syracuseStep 209719 = 314579) B314579
theorem B373673 : Blo 143792 373673 := bstep (se 2 (by rfl) ⟨140127, by rfl⟩ : syracuseStep 373673 = 280255) B280255
theorem B144639 : Blo 143792 144639 := bstep (se 1 (by rfl) ⟨108479, by rfl⟩ : syracuseStep 144639 = 216959) B216959
theorem B144767 : Blo 143792 144767 := bstep (se 1 (by rfl) ⟨108575, by rfl⟩ : syracuseStep 144767 = 217151) B217151
theorem B1127945 : Blo 143792 1127945 := bstep (se 2 (by rfl) ⟨422979, by rfl⟩ : syracuseStep 1127945 = 845959) B845959
theorem B144923 : Blo 143792 144923 := bstep (se 1 (by rfl) ⟨108692, by rfl⟩ : syracuseStep 144923 = 217385) B217385
theorem B145103 : Blo 143792 145103 := bstep (se 1 (by rfl) ⟨108827, by rfl⟩ : syracuseStep 145103 = 217655) B217655
theorem B145343 : Blo 143792 145343 := bstep (se 1 (by rfl) ⟨109007, by rfl⟩ : syracuseStep 145343 = 218015) B218015
theorem B997363 : Blo 143792 997363 := bstep (se 1 (by rfl) ⟨748022, by rfl⟩ : syracuseStep 997363 = 1496045) B1496045
theorem B145471 : Blo 143792 145471 := bstep (se 1 (by rfl) ⟨109103, by rfl⟩ : syracuseStep 145471 = 218207) B218207
theorem B145511 : Blo 143792 145511 := bstep (se 1 (by rfl) ⟨109133, by rfl⟩ : syracuseStep 145511 = 218267) B218267
theorem B145967 : Blo 143792 145967 := bstep (se 1 (by rfl) ⟨109475, by rfl⟩ : syracuseStep 145967 = 218951) B218951
theorem B834137 : Blo 143792 834137 := bstep (se 2 (by rfl) ⟨312801, by rfl⟩ : syracuseStep 834137 = 625603) B625603
theorem B146367 : Blo 143792 146367 := bstep (se 1 (by rfl) ⟨109775, by rfl⟩ : syracuseStep 146367 = 219551) B219551
theorem B146415 : Blo 143792 146415 := bstep (se 1 (by rfl) ⟨109811, by rfl⟩ : syracuseStep 146415 = 219623) B219623
theorem B736289 : Blo 143792 736289 := bstep (se 2 (by rfl) ⟨276108, by rfl⟩ : syracuseStep 736289 = 552217) B552217
theorem B2374877 : Blo 143792 2374877 := bstep (se 3 (by rfl) ⟨445289, by rfl⟩ : syracuseStep 2374877 = 890579) B890579
theorem B146911 : Blo 143792 146911 := bstep (se 1 (by rfl) ⟨110183, by rfl⟩ : syracuseStep 146911 = 220367) B220367
theorem B146991 : Blo 143792 146991 := bstep (se 1 (by rfl) ⟨110243, by rfl⟩ : syracuseStep 146991 = 220487) B220487
theorem B278171 : Blo 143792 278171 := bstep (se 1 (by rfl) ⟨208628, by rfl⟩ : syracuseStep 278171 = 417257) B417257
theorem B147099 : Blo 143792 147099 := bstep (se 1 (by rfl) ⟨110324, by rfl⟩ : syracuseStep 147099 = 220649) B220649
theorem B147195 : Blo 143792 147195 := bstep (se 1 (by rfl) ⟨110396, by rfl⟩ : syracuseStep 147195 = 220793) B220793
theorem B933713 : Blo 143792 933713 := bstep (se 2 (by rfl) ⟨350142, by rfl⟩ : syracuseStep 933713 = 700285) B700285
theorem B1752941 : Blo 143792 1752941 := bstep (se 3 (by rfl) ⟨328676, by rfl⟩ : syracuseStep 1752941 = 657353) B657353
theorem B147359 : Blo 143792 147359 := bstep (se 1 (by rfl) ⟨110519, by rfl⟩ : syracuseStep 147359 = 221039) B221039
theorem B1064933 : Blo 143792 1064933 := bstep (se 4 (by rfl) ⟨99837, by rfl⟩ : syracuseStep 1064933 = 199675) B199675
theorem B409789 : Blo 143792 409789 := bstep (se 3 (by rfl) ⟨76835, by rfl⟩ : syracuseStep 409789 = 153671) B153671
theorem B6799625 : Blo 143792 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B410359 : Blo 143792 410359 := bstep (se 1 (by rfl) ⟨307769, by rfl⟩ : syracuseStep 410359 = 615539) B615539
theorem B246523 : Blo 143792 246523 := bstep (se 1 (by rfl) ⟨184892, by rfl⟩ : syracuseStep 246523 = 369785) B369785
theorem B2245913 : Blo 143792 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B6768035 : Blo 143792 6768035 := bstep (se 1 (by rfl) ⟨5076026, by rfl⟩ : syracuseStep 6768035 = 10152053) B10152053
theorem B313151 : Blo 143792 313151 := bstep (se 1 (by rfl) ⟨234863, by rfl⟩ : syracuseStep 313151 = 469727) B469727
theorem B313391 : Blo 143792 313391 := bstep (se 1 (by rfl) ⟨235043, by rfl⟩ : syracuseStep 313391 = 470087) B470087
theorem B248015 : Blo 143792 248015 := bstep (se 1 (by rfl) ⟨186011, by rfl⟩ : syracuseStep 248015 = 372023) B372023
theorem B215771 : Blo 143792 215771 := bstep (se 1 (by rfl) ⟨161828, by rfl⟩ : syracuseStep 215771 = 323657) B323657
theorem B215807 : Blo 143792 215807 := bstep (se 1 (by rfl) ⟨161855, by rfl⟩ : syracuseStep 215807 = 323711) B323711
theorem B248575 : Blo 143792 248575 := bstep (se 1 (by rfl) ⟨186431, by rfl⟩ : syracuseStep 248575 = 372863) B372863
theorem B216527 : Blo 143792 216527 := bstep (se 1 (by rfl) ⟨162395, by rfl⟩ : syracuseStep 216527 = 324791) B324791
theorem B216617 : Blo 143792 216617 := bstep (se 2 (by rfl) ⟨81231, by rfl⟩ : syracuseStep 216617 = 162463) B162463
theorem B478831 : Blo 143792 478831 := bstep (se 1 (by rfl) ⟨359123, by rfl⟩ : syracuseStep 478831 = 718247) B718247
theorem B708281 : Blo 143792 708281 := bstep (se 2 (by rfl) ⟨265605, by rfl⟩ : syracuseStep 708281 = 531211) B531211
theorem B741149 : Blo 143792 741149 := bstep (se 3 (by rfl) ⟨138965, by rfl⟩ : syracuseStep 741149 = 277931) B277931
theorem B216911 : Blo 143792 216911 := bstep (se 1 (by rfl) ⟨162683, by rfl⟩ : syracuseStep 216911 = 325367) B325367
theorem B217031 : Blo 143792 217031 := bstep (se 1 (by rfl) ⟨162773, by rfl⟩ : syracuseStep 217031 = 325547) B325547
theorem B11980781 : Blo 143792 11980781 := bstep (se 3 (by rfl) ⟨2246396, by rfl⟩ : syracuseStep 11980781 = 4492793) B4492793
theorem B217115 : Blo 143792 217115 := bstep (se 1 (by rfl) ⟨162836, by rfl⟩ : syracuseStep 217115 = 325673) B325673
theorem B184447 : Blo 143792 184447 := bstep (se 1 (by rfl) ⟨138335, by rfl⟩ : syracuseStep 184447 = 276671) B276671
theorem B217391 : Blo 143792 217391 := bstep (se 1 (by rfl) ⟨163043, by rfl⟩ : syracuseStep 217391 = 326087) B326087
theorem B217499 : Blo 143792 217499 := bstep (se 1 (by rfl) ⟨163124, by rfl⟩ : syracuseStep 217499 = 326249) B326249
theorem B938429 : Blo 143792 938429 := bstep (se 3 (by rfl) ⟨175955, by rfl⟩ : syracuseStep 938429 = 351911) B351911
theorem B217535 : Blo 143792 217535 := bstep (se 1 (by rfl) ⟨163151, by rfl⟩ : syracuseStep 217535 = 326303) B326303
theorem B217631 : Blo 143792 217631 := bstep (se 1 (by rfl) ⟨163223, by rfl⟩ : syracuseStep 217631 = 326447) B326447
theorem B184943 : Blo 143792 184943 := bstep (se 1 (by rfl) ⟨138707, by rfl⟩ : syracuseStep 184943 = 277415) B277415
theorem B217919 : Blo 143792 217919 := bstep (se 1 (by rfl) ⟨163439, by rfl⟩ : syracuseStep 217919 = 326879) B326879
theorem B218063 : Blo 143792 218063 := bstep (se 1 (by rfl) ⟨163547, by rfl⟩ : syracuseStep 218063 = 327095) B327095
theorem B218153 : Blo 143792 218153 := bstep (se 2 (by rfl) ⟨81807, by rfl⟩ : syracuseStep 218153 = 163615) B163615
theorem B218183 : Blo 143792 218183 := bstep (se 1 (by rfl) ⟨163637, by rfl⟩ : syracuseStep 218183 = 327275) B327275
theorem B218363 : Blo 143792 218363 := bstep (se 1 (by rfl) ⟨163772, by rfl⟩ : syracuseStep 218363 = 327545) B327545
theorem B185647 : Blo 143792 185647 := bstep (se 1 (by rfl) ⟨139235, by rfl⟩ : syracuseStep 185647 = 278471) B278471
theorem B218423 : Blo 143792 218423 := bstep (se 1 (by rfl) ⟨163817, by rfl⟩ : syracuseStep 218423 = 327635) B327635
theorem B218729 : Blo 143792 218729 := bstep (se 2 (by rfl) ⟨82023, by rfl⟩ : syracuseStep 218729 = 164047) B164047
theorem B219263 : Blo 143792 219263 := bstep (se 1 (by rfl) ⟨164447, by rfl⟩ : syracuseStep 219263 = 328895) B328895
theorem B219359 : Blo 143792 219359 := bstep (se 1 (by rfl) ⟨164519, by rfl⟩ : syracuseStep 219359 = 329039) B329039
theorem B415975 : Blo 143792 415975 := bstep (se 1 (by rfl) ⟨311981, by rfl⟩ : syracuseStep 415975 = 623963) B623963
theorem B219419 : Blo 143792 219419 := bstep (se 1 (by rfl) ⟨164564, by rfl⟩ : syracuseStep 219419 = 329129) B329129
theorem B219743 : Blo 143792 219743 := bstep (se 1 (by rfl) ⟨164807, by rfl⟩ : syracuseStep 219743 = 329615) B329615
theorem B187039 : Blo 143792 187039 := bstep (se 1 (by rfl) ⟨140279, by rfl⟩ : syracuseStep 187039 = 280559) B280559
theorem B219839 : Blo 143792 219839 := bstep (se 1 (by rfl) ⟨164879, by rfl⟩ : syracuseStep 219839 = 329759) B329759
theorem B219881 : Blo 143792 219881 := bstep (se 2 (by rfl) ⟨82455, by rfl⟩ : syracuseStep 219881 = 164911) B164911
theorem B220007 : Blo 143792 220007 := bstep (se 1 (by rfl) ⟨165005, by rfl⟩ : syracuseStep 220007 = 330011) B330011
theorem B220073 : Blo 143792 220073 := bstep (se 2 (by rfl) ⟨82527, by rfl⟩ : syracuseStep 220073 = 165055) B165055
theorem B220223 : Blo 143792 220223 := bstep (se 1 (by rfl) ⟨165167, by rfl⟩ : syracuseStep 220223 = 330335) B330335
theorem B220265 : Blo 143792 220265 := bstep (se 2 (by rfl) ⟨82599, by rfl⟩ : syracuseStep 220265 = 165199) B165199
theorem B220391 : Blo 143792 220391 := bstep (se 1 (by rfl) ⟨165293, by rfl⟩ : syracuseStep 220391 = 330587) B330587
theorem B1039645 : Blo 143792 1039645 := bstep (se 3 (by rfl) ⟨194933, by rfl⟩ : syracuseStep 1039645 = 389867) B389867
theorem B220895 : Blo 143792 220895 := bstep (se 1 (by rfl) ⟨165671, by rfl⟩ : syracuseStep 220895 = 331343) B331343
theorem B4185917 : Blo 143792 4185917 := bstep (se 3 (by rfl) ⟨784859, by rfl⟩ : syracuseStep 4185917 = 1569719) B1569719
theorem B221225 : Blo 143792 221225 := bstep (se 2 (by rfl) ⟨82959, by rfl⟩ : syracuseStep 221225 = 165919) B165919
theorem B221255 : Blo 143792 221255 := bstep (se 1 (by rfl) ⟨165941, by rfl⟩ : syracuseStep 221255 = 331883) B331883
theorem B417899 : Blo 143792 417899 := bstep (se 1 (by rfl) ⟨313424, by rfl⟩ : syracuseStep 417899 = 626849) B626849
theorem B221291 : Blo 143792 221291 := bstep (se 1 (by rfl) ⟨165968, by rfl⟩ : syracuseStep 221291 = 331937) B331937
theorem B221375 : Blo 143792 221375 := bstep (se 1 (by rfl) ⟨166031, by rfl⟩ : syracuseStep 221375 = 332063) B332063
theorem B5333273 : Blo 143792 5333273 := bstep (se 2 (by rfl) ⟨1999977, by rfl⟩ : syracuseStep 5333273 = 3999955) B3999955
theorem B221561 : Blo 143792 221561 := bstep (se 2 (by rfl) ⟨83085, by rfl⟩ : syracuseStep 221561 = 166171) B166171
theorem B1761697 : Blo 143792 1761697 := bstep (se 2 (by rfl) ⟨660636, by rfl⟩ : syracuseStep 1761697 = 1321273) B1321273
theorem B615215 : Blo 143792 615215 := bstep (se 1 (by rfl) ⟨461411, by rfl⟩ : syracuseStep 615215 = 922823) B922823
theorem B4449451 : Blo 143792 4449451 := bstep (se 1 (by rfl) ⟨3337088, by rfl⟩ : syracuseStep 4449451 = 6674177) B6674177
theorem B1861379 : Blo 143792 1861379 := bstep (se 1 (by rfl) ⟨1396034, by rfl⟩ : syracuseStep 1861379 = 2792069) B2792069
theorem B747305 : Blo 143792 747305 := bstep (se 2 (by rfl) ⟨280239, by rfl⟩ : syracuseStep 747305 = 560479) B560479
theorem B1993079 : Blo 143792 1993079 := bstep (se 1 (by rfl) ⟨1494809, by rfl⟩ : syracuseStep 1993079 = 2989619) B2989619
theorem B420349 : Blo 143792 420349 := bstep (se 3 (by rfl) ⟨78815, by rfl⟩ : syracuseStep 420349 = 157631) B157631
theorem B617213 : Blo 143792 617213 := bstep (se 3 (by rfl) ⟨115727, by rfl⟩ : syracuseStep 617213 = 231455) B231455
theorem B420815 : Blo 143792 420815 := bstep (se 1 (by rfl) ⟨315611, by rfl⟩ : syracuseStep 420815 = 631223) B631223
theorem B224251 : Blo 143792 224251 := bstep (se 1 (by rfl) ⟨168188, by rfl⟩ : syracuseStep 224251 = 336377) B336377
theorem B2485633 : Blo 143792 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B487295 : Blo 143792 487295 := bstep (se 1 (by rfl) ⟨365471, by rfl⟩ : syracuseStep 487295 = 730943) B730943
theorem B487457 : Blo 143792 487457 := bstep (se 2 (by rfl) ⟨182796, by rfl⟩ : syracuseStep 487457 = 365593) B365593
theorem B323639 : Blo 143792 323639 := bstep (se 1 (by rfl) ⟨242729, by rfl⟩ : syracuseStep 323639 = 485459) B485459
theorem B783067 : Blo 143792 783067 := bstep (se 1 (by rfl) ⟨587300, by rfl⟩ : syracuseStep 783067 = 1174601) B1174601
theorem B1110995 : Blo 143792 1110995 := bstep (se 1 (by rfl) ⟨833246, by rfl⟩ : syracuseStep 1110995 = 1666493) B1666493
theorem B1438859 : Blo 143792 1438859 := bstep (se 1 (by rfl) ⟨1079144, by rfl⟩ : syracuseStep 1438859 = 2158289) B2158289
theorem B488699 : Blo 143792 488699 := bstep (se 1 (by rfl) ⟨366524, by rfl⟩ : syracuseStep 488699 = 733049) B733049
theorem B6453107 : Blo 143792 6453107 := bstep (se 1 (by rfl) ⟨4839830, by rfl⟩ : syracuseStep 6453107 = 9679661) B9679661
theorem B4716539 : Blo 143792 4716539 := bstep (se 1 (by rfl) ⟨3537404, by rfl⟩ : syracuseStep 4716539 = 7074809) B7074809
theorem B161959 : Blo 143792 161959 := bstep (se 1 (by rfl) ⟨121469, by rfl⟩ : syracuseStep 161959 = 242939) B242939
theorem B325943 : Blo 143792 325943 := bstep (se 1 (by rfl) ⟨244457, by rfl⟩ : syracuseStep 325943 = 488915) B488915
theorem B2488805 : Blo 143792 2488805 := bstep (se 4 (by rfl) ⟨233325, by rfl⟩ : syracuseStep 2488805 = 466651) B466651
theorem B326123 : Blo 143792 326123 := bstep (se 1 (by rfl) ⟨244592, by rfl⟩ : syracuseStep 326123 = 489185) B489185
theorem B424711 : Blo 143792 424711 := bstep (se 1 (by rfl) ⟨318533, by rfl⟩ : syracuseStep 424711 = 637067) B637067
theorem B622187 : Blo 143792 622187 := bstep (se 1 (by rfl) ⟨466640, by rfl⟩ : syracuseStep 622187 = 933281) B933281
theorem B491129 : Blo 143792 491129 := bstep (se 2 (by rfl) ⟨184173, by rfl⟩ : syracuseStep 491129 = 368347) B368347
theorem B327455 : Blo 143792 327455 := bstep (se 1 (by rfl) ⟨245591, by rfl⟩ : syracuseStep 327455 = 491183) B491183
theorem B1113911 : Blo 143792 1113911 := bstep (se 1 (by rfl) ⟨835433, by rfl⟩ : syracuseStep 1113911 = 1670867) B1670867
theorem B262025 : Blo 143792 262025 := bstep (se 2 (by rfl) ⟨98259, by rfl⟩ : syracuseStep 262025 = 196519) B196519
theorem B491507 : Blo 143792 491507 := bstep (se 1 (by rfl) ⟨368630, by rfl⟩ : syracuseStep 491507 = 737261) B737261
theorem B11862287 : Blo 143792 11862287 := bstep (se 1 (by rfl) ⟨8896715, by rfl⟩ : syracuseStep 11862287 = 17793431) B17793431
theorem B1114397 : Blo 143792 1114397 := bstep (se 3 (by rfl) ⟨208949, by rfl⟩ : syracuseStep 1114397 = 417899) B417899
theorem B328031 : Blo 143792 328031 := bstep (se 1 (by rfl) ⟨246023, by rfl⟩ : syracuseStep 328031 = 492047) B492047
theorem B328697 : Blo 143792 328697 := bstep (se 2 (by rfl) ⟨123261, by rfl⟩ : syracuseStep 328697 = 246523) B246523
theorem B328751 : Blo 143792 328751 := bstep (se 1 (by rfl) ⟨246563, by rfl⟩ : syracuseStep 328751 = 493127) B493127
theorem B492857 : Blo 143792 492857 := bstep (se 2 (by rfl) ⟨184821, by rfl⟩ : syracuseStep 492857 = 369643) B369643
theorem B165343 : Blo 143792 165343 := bstep (se 1 (by rfl) ⟨124007, by rfl⟩ : syracuseStep 165343 = 248015) B248015
theorem B5932601 : Blo 143792 5932601 := bstep (se 2 (by rfl) ⟨2224725, by rfl⟩ : syracuseStep 5932601 = 4449451) B4449451
theorem B493181 : Blo 143792 493181 := bstep (se 3 (by rfl) ⟨92471, by rfl⟩ : syracuseStep 493181 = 184943) B184943
theorem B493289 : Blo 143792 493289 := bstep (se 2 (by rfl) ⟨184983, by rfl⟩ : syracuseStep 493289 = 369967) B369967
theorem B526367 : Blo 143792 526367 := bstep (se 1 (by rfl) ⟨394775, by rfl⟩ : syracuseStep 526367 = 789551) B789551
theorem B494099 : Blo 143792 494099 := bstep (se 1 (by rfl) ⟨370574, by rfl⟩ : syracuseStep 494099 = 741149) B741149
theorem B330407 : Blo 143792 330407 := bstep (se 1 (by rfl) ⟨247805, by rfl⟩ : syracuseStep 330407 = 495611) B495611
theorem B625619 : Blo 143792 625619 := bstep (se 1 (by rfl) ⟨469214, by rfl⟩ : syracuseStep 625619 = 938429) B938429
theorem B560465 : Blo 143792 560465 := bstep (se 2 (by rfl) ⟨210174, by rfl⟩ : syracuseStep 560465 = 420349) B420349
theorem B3804833 : Blo 143792 3804833 := bstep (se 2 (by rfl) ⟨1426812, by rfl⟩ : syracuseStep 3804833 = 2853625) B2853625
theorem B331433 : Blo 143792 331433 := bstep (se 2 (by rfl) ⟨124287, by rfl⟩ : syracuseStep 331433 = 248575) B248575
theorem B364297 : Blo 143792 364297 := bstep (se 2 (by rfl) ⟨136611, by rfl⟩ : syracuseStep 364297 = 273223) B273223
theorem B1315115 : Blo 143792 1315115 := bstep (se 1 (by rfl) ⟨986336, by rfl⟩ : syracuseStep 1315115 = 1972673) B1972673
theorem B3314177 : Blo 143792 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B3871901 : Blo 143792 3871901 := bstep (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) B1451963
theorem B2790611 : Blo 143792 2790611 := bstep (se 1 (by rfl) ⟨2092958, by rfl⟩ : syracuseStep 2790611 = 4185917) B4185917
theorem B923051 : Blo 143792 923051 := bstep (se 1 (by rfl) ⟨692288, by rfl⟩ : syracuseStep 923051 = 1384577) B1384577
theorem B9443465 : Blo 143792 9443465 := bstep (se 2 (by rfl) ⟨3541299, by rfl⟩ : syracuseStep 9443465 = 7082599) B7082599
theorem B498203 : Blo 143792 498203 := bstep (se 1 (by rfl) ⟨373652, by rfl⟩ : syracuseStep 498203 = 747305) B747305
theorem B990143 : Blo 143792 990143 := bstep (se 1 (by rfl) ⟨742607, by rfl⟩ : syracuseStep 990143 = 1485215) B1485215
theorem B531775 : Blo 143792 531775 := bstep (se 1 (by rfl) ⟨398831, by rfl⟩ : syracuseStep 531775 = 797663) B797663
theorem B662867 : Blo 143792 662867 := bstep (se 1 (by rfl) ⟨497150, by rfl⟩ : syracuseStep 662867 = 994301) B994301
theorem B1122173 : Blo 143792 1122173 := bstep (se 3 (by rfl) ⟨210407, by rfl⟩ : syracuseStep 1122173 = 420815) B420815
theorem B4530167 : Blo 143792 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B3154049 : Blo 143792 3154049 := bstep (se 2 (by rfl) ⟨1182768, by rfl⟩ : syracuseStep 3154049 = 2365537) B2365537
theorem B6333005 : Blo 143792 6333005 := bstep (se 3 (by rfl) ⟨1187438, by rfl⟩ : syracuseStep 6333005 = 2374877) B2374877
theorem B959239 : Blo 143792 959239 := bstep (se 1 (by rfl) ⟨719429, by rfl⟩ : syracuseStep 959239 = 1438859) B1438859
theorem B566281 : Blo 143792 566281 := bstep (se 2 (by rfl) ⟨212355, by rfl⟩ : syracuseStep 566281 = 424711) B424711
theorem B4302071 : Blo 143792 4302071 := bstep (se 1 (by rfl) ⟨3226553, by rfl⟩ : syracuseStep 4302071 = 6453107) B6453107
theorem B1386193 : Blo 143792 1386193 := bstep (se 2 (by rfl) ⟨519822, by rfl⟩ : syracuseStep 1386193 = 1039645) B1039645
theorem B174683 : Blo 143792 174683 := bstep (se 1 (by rfl) ⟨131012, by rfl⟩ : syracuseStep 174683 = 262025) B262025
theorem B4533083 : Blo 143792 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B372559 : Blo 143792 372559 := bstep (se 1 (by rfl) ⟨279419, by rfl⟩ : syracuseStep 372559 = 558839) B558839
theorem B1093499 : Blo 143792 1093499 := bstep (se 1 (by rfl) ⟨820124, by rfl⟩ : syracuseStep 1093499 = 1640249) B1640249
theorem B208927 : Blo 143792 208927 := bstep (se 1 (by rfl) ⟨156695, by rfl⟩ : syracuseStep 208927 = 313391) B313391
theorem B3911759 : Blo 143792 3911759 := bstep (se 1 (by rfl) ⟨2933819, by rfl⟩ : syracuseStep 3911759 = 5867639) B5867639
theorem B143847 : Blo 143792 143847 := bstep (se 1 (by rfl) ⟨107885, by rfl⟩ : syracuseStep 143847 = 215771) B215771
theorem B143871 : Blo 143792 143871 := bstep (se 1 (by rfl) ⟨107903, by rfl⟩ : syracuseStep 143871 = 215807) B215807
theorem B144351 : Blo 143792 144351 := bstep (se 1 (by rfl) ⟨108263, by rfl⟩ : syracuseStep 144351 = 216527) B216527
theorem B144411 : Blo 143792 144411 := bstep (se 1 (by rfl) ⟨108308, by rfl⟩ : syracuseStep 144411 = 216617) B216617
theorem B4240457 : Blo 143792 4240457 := bstep (se 2 (by rfl) ⟨1590171, by rfl⟩ : syracuseStep 4240457 = 3180343) B3180343
theorem B472187 : Blo 143792 472187 := bstep (se 1 (by rfl) ⟨354140, by rfl⟩ : syracuseStep 472187 = 708281) B708281
theorem B144607 : Blo 143792 144607 := bstep (se 1 (by rfl) ⟨108455, by rfl⟩ : syracuseStep 144607 = 216911) B216911
theorem B144687 : Blo 143792 144687 := bstep (se 1 (by rfl) ⟨108515, by rfl⟩ : syracuseStep 144687 = 217031) B217031
theorem B144743 : Blo 143792 144743 := bstep (se 1 (by rfl) ⟨108557, by rfl⟩ : syracuseStep 144743 = 217115) B217115
theorem B144927 : Blo 143792 144927 := bstep (se 1 (by rfl) ⟨108695, by rfl⟩ : syracuseStep 144927 = 217391) B217391
theorem B144999 : Blo 143792 144999 := bstep (se 1 (by rfl) ⟨108749, by rfl⟩ : syracuseStep 144999 = 217499) B217499
theorem B145023 : Blo 143792 145023 := bstep (se 1 (by rfl) ⟨108767, by rfl⟩ : syracuseStep 145023 = 217535) B217535
theorem B145087 : Blo 143792 145087 := bstep (se 1 (by rfl) ⟨108815, by rfl⟩ : syracuseStep 145087 = 217631) B217631
theorem B1095443 : Blo 143792 1095443 := bstep (se 1 (by rfl) ⟨821582, by rfl⟩ : syracuseStep 1095443 = 1643165) B1643165
theorem B145279 : Blo 143792 145279 := bstep (se 1 (by rfl) ⟨108959, by rfl⟩ : syracuseStep 145279 = 217919) B217919
theorem B145375 : Blo 143792 145375 := bstep (se 1 (by rfl) ⟨109031, by rfl⟩ : syracuseStep 145375 = 218063) B218063
theorem B145435 : Blo 143792 145435 := bstep (se 1 (by rfl) ⟨109076, by rfl⟩ : syracuseStep 145435 = 218153) B218153
theorem B145455 : Blo 143792 145455 := bstep (se 1 (by rfl) ⟨109091, by rfl⟩ : syracuseStep 145455 = 218183) B218183
theorem B145575 : Blo 143792 145575 := bstep (se 1 (by rfl) ⟨109181, by rfl⟩ : syracuseStep 145575 = 218363) B218363
theorem B145615 : Blo 143792 145615 := bstep (se 1 (by rfl) ⟨109211, by rfl⟩ : syracuseStep 145615 = 218423) B218423
theorem B145819 : Blo 143792 145819 := bstep (se 1 (by rfl) ⟨109364, by rfl⟩ : syracuseStep 145819 = 218729) B218729
theorem B244127 : Blo 143792 244127 := bstep (se 1 (by rfl) ⟨183095, by rfl⟩ : syracuseStep 244127 = 366191) B366191
theorem B146175 : Blo 143792 146175 := bstep (se 1 (by rfl) ⟨109631, by rfl⟩ : syracuseStep 146175 = 219263) B219263
theorem B146239 : Blo 143792 146239 := bstep (se 1 (by rfl) ⟨109679, by rfl⟩ : syracuseStep 146239 = 219359) B219359
theorem B146279 : Blo 143792 146279 := bstep (se 1 (by rfl) ⟨109709, by rfl⟩ : syracuseStep 146279 = 219419) B219419
theorem B1751969 : Blo 143792 1751969 := bstep (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) B1313977
theorem B146495 : Blo 143792 146495 := bstep (se 1 (by rfl) ⟨109871, by rfl⟩ : syracuseStep 146495 = 219743) B219743
theorem B146559 : Blo 143792 146559 := bstep (se 1 (by rfl) ⟨109919, by rfl⟩ : syracuseStep 146559 = 219839) B219839
theorem B146587 : Blo 143792 146587 := bstep (se 1 (by rfl) ⟨109940, by rfl⟩ : syracuseStep 146587 = 219881) B219881
theorem B146671 : Blo 143792 146671 := bstep (se 1 (by rfl) ⟨110003, by rfl⟩ : syracuseStep 146671 = 220007) B220007
theorem B146715 : Blo 143792 146715 := bstep (se 1 (by rfl) ⟨110036, by rfl⟩ : syracuseStep 146715 = 220073) B220073
theorem B1686815 : Blo 143792 1686815 := bstep (se 1 (by rfl) ⟨1265111, by rfl⟩ : syracuseStep 1686815 = 2530223) B2530223
theorem B146815 : Blo 143792 146815 := bstep (se 1 (by rfl) ⟨110111, by rfl⟩ : syracuseStep 146815 = 220223) B220223
theorem B146843 : Blo 143792 146843 := bstep (se 1 (by rfl) ⟨110132, by rfl⟩ : syracuseStep 146843 = 220265) B220265
theorem B277985 : Blo 143792 277985 := bstep (se 2 (by rfl) ⟨104244, by rfl⟩ : syracuseStep 277985 = 208489) B208489
theorem B638441 : Blo 143792 638441 := bstep (se 2 (by rfl) ⟨239415, by rfl⟩ : syracuseStep 638441 = 478831) B478831
theorem B146927 : Blo 143792 146927 := bstep (se 1 (by rfl) ⟨110195, by rfl⟩ : syracuseStep 146927 = 220391) B220391
theorem B835069 : Blo 143792 835069 := bstep (se 3 (by rfl) ⟨156575, by rfl⟩ : syracuseStep 835069 = 313151) B313151
theorem B147263 : Blo 143792 147263 := bstep (se 1 (by rfl) ⟨110447, by rfl⟩ : syracuseStep 147263 = 220895) B220895
theorem B1196005 : Blo 143792 1196005 := bstep (se 4 (by rfl) ⟨112125, by rfl⟩ : syracuseStep 1196005 = 224251) B224251
theorem B147483 : Blo 143792 147483 := bstep (se 1 (by rfl) ⟨110612, by rfl⟩ : syracuseStep 147483 = 221225) B221225
theorem B147503 : Blo 143792 147503 := bstep (se 1 (by rfl) ⟨110627, by rfl⟩ : syracuseStep 147503 = 221255) B221255
theorem B147527 : Blo 143792 147527 := bstep (se 1 (by rfl) ⟨110645, by rfl⟩ : syracuseStep 147527 = 221291) B221291
theorem B147583 : Blo 143792 147583 := bstep (se 1 (by rfl) ⟨110687, by rfl⟩ : syracuseStep 147583 = 221375) B221375
theorem B245929 : Blo 143792 245929 := bstep (se 2 (by rfl) ⟨92223, by rfl⟩ : syracuseStep 245929 = 184447) B184447
theorem B3555515 : Blo 143792 3555515 := bstep (se 1 (by rfl) ⟨2666636, by rfl⟩ : syracuseStep 3555515 = 5333273) B5333273
theorem B147707 : Blo 143792 147707 := bstep (se 1 (by rfl) ⟨110780, by rfl⟩ : syracuseStep 147707 = 221561) B221561
theorem B410017 : Blo 143792 410017 := bstep (se 2 (by rfl) ⟨153756, by rfl⟩ : syracuseStep 410017 = 307513) B307513
theorem B836027 : Blo 143792 836027 := bstep (se 1 (by rfl) ⟨627020, by rfl⟩ : syracuseStep 836027 = 1254041) B1254041
theorem B410143 : Blo 143792 410143 := bstep (se 1 (by rfl) ⟨307607, by rfl⟩ : syracuseStep 410143 = 615215) B615215
theorem B246415 : Blo 143792 246415 := bstep (se 1 (by rfl) ⟨184811, by rfl⟩ : syracuseStep 246415 = 369623) B369623
theorem B312187 : Blo 143792 312187 := bstep (se 1 (by rfl) ⟨234140, by rfl⟩ : syracuseStep 312187 = 468281) B468281
theorem B279625 : Blo 143792 279625 := bstep (se 2 (by rfl) ⟨104859, by rfl⟩ : syracuseStep 279625 = 209719) B209719
theorem B1328719 : Blo 143792 1328719 := bstep (se 1 (by rfl) ⟨996539, by rfl⟩ : syracuseStep 1328719 = 1993079) B1993079
theorem B247387 : Blo 143792 247387 := bstep (se 1 (by rfl) ⟨185540, by rfl⟩ : syracuseStep 247387 = 371081) B371081
theorem B2475683 : Blo 143792 2475683 := bstep (se 1 (by rfl) ⟨1856762, by rfl⟩ : syracuseStep 2475683 = 3713525) B3713525
theorem B247529 : Blo 143792 247529 := bstep (se 2 (by rfl) ⟨92823, by rfl⟩ : syracuseStep 247529 = 185647) B185647
theorem B706283 : Blo 143792 706283 := bstep (se 1 (by rfl) ⟨529712, by rfl⟩ : syracuseStep 706283 = 1059425) B1059425
theorem B411475 : Blo 143792 411475 := bstep (se 1 (by rfl) ⟨308606, by rfl⟩ : syracuseStep 411475 = 617213) B617213
theorem B182503 : Blo 143792 182503 := bstep (se 1 (by rfl) ⟨136877, by rfl⟩ : syracuseStep 182503 = 273755) B273755
theorem B2345435 : Blo 143792 2345435 := bstep (se 1 (by rfl) ⟨1759076, by rfl⟩ : syracuseStep 2345435 = 3518153) B3518153
theorem B1329817 : Blo 143792 1329817 := bstep (se 2 (by rfl) ⟨498681, by rfl⟩ : syracuseStep 1329817 = 997363) B997363
theorem B215759 : Blo 143792 215759 := bstep (se 1 (by rfl) ⟨161819, by rfl⟩ : syracuseStep 215759 = 323639) B323639
theorem B215945 : Blo 143792 215945 := bstep (se 2 (by rfl) ⟨80979, by rfl⟩ : syracuseStep 215945 = 161959) B161959
theorem B249115 : Blo 143792 249115 := bstep (se 1 (by rfl) ⟨186836, by rfl⟩ : syracuseStep 249115 = 373673) B373673
theorem B740663 : Blo 143792 740663 := bstep (se 1 (by rfl) ⟨555497, by rfl⟩ : syracuseStep 740663 = 1110995) B1110995
theorem B249385 : Blo 143792 249385 := bstep (se 2 (by rfl) ⟨93519, by rfl⟩ : syracuseStep 249385 = 187039) B187039
theorem B217295 : Blo 143792 217295 := bstep (se 1 (by rfl) ⟨162971, by rfl⟩ : syracuseStep 217295 = 325943) B325943
theorem B1659203 : Blo 143792 1659203 := bstep (se 1 (by rfl) ⟨1244402, by rfl⟩ : syracuseStep 1659203 = 2488805) B2488805
theorem B217415 : Blo 143792 217415 := bstep (se 1 (by rfl) ⟨163061, by rfl⟩ : syracuseStep 217415 = 326123) B326123
theorem B4674509 : Blo 143792 4674509 := bstep (se 3 (by rfl) ⟨876470, by rfl⟩ : syracuseStep 4674509 = 1752941) B1752941
theorem B414791 : Blo 143792 414791 := bstep (se 1 (by rfl) ⟨311093, by rfl⟩ : syracuseStep 414791 = 622187) B622187
theorem B185447 : Blo 143792 185447 := bstep (se 1 (by rfl) ⟨139085, by rfl⟩ : syracuseStep 185447 = 278171) B278171
theorem B218303 : Blo 143792 218303 := bstep (se 1 (by rfl) ⟨163727, by rfl⟩ : syracuseStep 218303 = 327455) B327455
theorem B742607 : Blo 143792 742607 := bstep (se 1 (by rfl) ⟨556955, by rfl⟩ : syracuseStep 742607 = 1113911) B1113911
theorem B709955 : Blo 143792 709955 := bstep (se 1 (by rfl) ⟨532466, by rfl⟩ : syracuseStep 709955 = 1064933) B1064933
theorem B546385 : Blo 143792 546385 := bstep (se 2 (by rfl) ⟨204894, by rfl⟩ : syracuseStep 546385 = 409789) B409789
theorem B1398383 : Blo 143792 1398383 := bstep (se 1 (by rfl) ⟨1048787, by rfl⟩ : syracuseStep 1398383 = 2097575) B2097575
theorem B2348929 : Blo 143792 2348929 := bstep (se 2 (by rfl) ⟨880848, by rfl⟩ : syracuseStep 2348929 = 1761697) B1761697
theorem B1497275 : Blo 143792 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B4512023 : Blo 143792 4512023 := bstep (se 1 (by rfl) ⟨3384017, by rfl⟩ : syracuseStep 4512023 = 6768035) B6768035
theorem B547145 : Blo 143792 547145 := bstep (se 2 (by rfl) ⟨205179, by rfl⟩ : syracuseStep 547145 = 410359) B410359
theorem B219775 : Blo 143792 219775 := bstep (se 1 (by rfl) ⟨164831, by rfl⟩ : syracuseStep 219775 = 329663) B329663
theorem B1006505 : Blo 143792 1006505 := bstep (se 2 (by rfl) ⟨377439, by rfl⟩ : syracuseStep 1006505 = 754879) B754879
theorem B51534863 : Blo 143792 51534863 := bstep (se 1 (by rfl) ⟨38651147, by rfl⟩ : syracuseStep 51534863 = 77302295) B77302295
theorem B220319 : Blo 143792 220319 := bstep (se 1 (by rfl) ⟨165239, by rfl⟩ : syracuseStep 220319 = 330479) B330479
theorem B220571 : Blo 143792 220571 := bstep (se 1 (by rfl) ⟨165428, by rfl⟩ : syracuseStep 220571 = 330857) B330857
theorem B220991 : Blo 143792 220991 := bstep (se 1 (by rfl) ⟨165743, by rfl⟩ : syracuseStep 220991 = 331487) B331487
theorem B221159 : Blo 143792 221159 := bstep (se 1 (by rfl) ⟨165869, by rfl⟩ : syracuseStep 221159 = 331739) B331739
theorem B7987187 : Blo 143792 7987187 := bstep (se 1 (by rfl) ⟨5990390, by rfl⟩ : syracuseStep 7987187 = 11980781) B11980781
theorem B221279 : Blo 143792 221279 := bstep (se 1 (by rfl) ⟨165959, by rfl⟩ : syracuseStep 221279 = 331919) B331919
theorem B221339 : Blo 143792 221339 := bstep (se 1 (by rfl) ⟨166004, by rfl⟩ : syracuseStep 221339 = 332009) B332009
theorem B221519 : Blo 143792 221519 := bstep (se 1 (by rfl) ⟨166139, by rfl⟩ : syracuseStep 221519 = 332279) B332279
theorem B3007853 : Blo 143792 3007853 := bstep (se 3 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 3007853 = 1127945) B1127945
theorem B485351 : Blo 143792 485351 := bstep (se 1 (by rfl) ⟨364013, by rfl⟩ : syracuseStep 485351 = 728027) B728027
theorem B846281 : Blo 143792 846281 := bstep (se 2 (by rfl) ⟨317355, by rfl⟩ : syracuseStep 846281 = 634711) B634711
theorem B1044089 : Blo 143792 1044089 := bstep (se 2 (by rfl) ⟨391533, by rfl⟩ : syracuseStep 1044089 = 783067) B783067
theorem B487079 : Blo 143792 487079 := bstep (se 1 (by rfl) ⟨365309, by rfl⟩ : syracuseStep 487079 = 730619) B730619
theorem B1240919 : Blo 143792 1240919 := bstep (se 1 (by rfl) ⟨930689, by rfl⟩ : syracuseStep 1240919 = 1861379) B1861379
theorem B487403 : Blo 143792 487403 := bstep (se 1 (by rfl) ⟨365552, by rfl⟩ : syracuseStep 487403 = 731105) B731105
theorem B553175 : Blo 143792 553175 := bstep (se 1 (by rfl) ⟨414881, by rfl⟩ : syracuseStep 553175 = 829763) B829763
theorem B1405147 : Blo 143792 1405147 := bstep (se 1 (by rfl) ⟨1053860, by rfl⟩ : syracuseStep 1405147 = 2107721) B2107721
theorem B2519423 : Blo 143792 2519423 := bstep (se 1 (by rfl) ⟨1889567, by rfl⟩ : syracuseStep 2519423 = 3779135) B3779135
theorem B488105 : Blo 143792 488105 := bstep (se 2 (by rfl) ⟨183039, by rfl⟩ : syracuseStep 488105 = 366079) B366079
theorem B553979 : Blo 143792 553979 := bstep (se 1 (by rfl) ⟨415484, by rfl⟩ : syracuseStep 553979 = 830969) B830969
theorem B324863 : Blo 143792 324863 := bstep (se 1 (by rfl) ⟨243647, by rfl⟩ : syracuseStep 324863 = 487295) B487295
theorem B324971 : Blo 143792 324971 := bstep (se 1 (by rfl) ⟨243728, by rfl⟩ : syracuseStep 324971 = 487457) B487457
theorem B619913 : Blo 143792 619913 := bstep (se 2 (by rfl) ⟨232467, by rfl⟩ : syracuseStep 619913 = 464935) B464935
theorem B2127383 : Blo 143792 2127383 := bstep (se 1 (by rfl) ⟨1595537, by rfl⟩ : syracuseStep 2127383 = 3191075) B3191075
theorem B554633 : Blo 143792 554633 := bstep (se 2 (by rfl) ⟨207987, by rfl⟩ : syracuseStep 554633 = 415975) B415975
theorem B555133 : Blo 143792 555133 := bstep (se 3 (by rfl) ⟨104087, by rfl⟩ : syracuseStep 555133 = 208175) B208175
theorem B325799 : Blo 143792 325799 := bstep (se 1 (by rfl) ⟨244349, by rfl⟩ : syracuseStep 325799 = 488699) B488699
theorem B3144359 : Blo 143792 3144359 := bstep (se 1 (by rfl) ⟨2358269, by rfl⟩ : syracuseStep 3144359 = 4716539) B4716539
theorem B490265 : Blo 143792 490265 := bstep (se 2 (by rfl) ⟨183849, by rfl⟩ : syracuseStep 490265 = 367699) B367699
theorem B556091 : Blo 143792 556091 := bstep (se 1 (by rfl) ⟨417068, by rfl⟩ : syracuseStep 556091 = 834137) B834137
theorem B490859 : Blo 143792 490859 := bstep (se 1 (by rfl) ⟨368144, by rfl⟩ : syracuseStep 490859 = 736289) B736289
theorem B327419 : Blo 143792 327419 := bstep (se 1 (by rfl) ⟨245564, by rfl⟩ : syracuseStep 327419 = 491129) B491129
theorem B622475 : Blo 143792 622475 := bstep (se 1 (by rfl) ⟨466856, by rfl⟩ : syracuseStep 622475 = 933713) B933713
theorem B327671 : Blo 143792 327671 := bstep (se 1 (by rfl) ⟨245753, by rfl⟩ : syracuseStep 327671 = 491507) B491507
theorem B327905 : Blo 143792 327905 := bstep (se 2 (by rfl) ⟨122964, by rfl⟩ : syracuseStep 327905 = 245929) B245929
theorem B557351 : Blo 143792 557351 := bstep (se 1 (by rfl) ⟨418013, by rfl⟩ : syracuseStep 557351 = 836027) B836027
theorem B328553 : Blo 143792 328553 := bstep (se 2 (by rfl) ⟨123207, by rfl⟩ : syracuseStep 328553 = 246415) B246415
theorem B328571 : Blo 143792 328571 := bstep (se 1 (by rfl) ⟨246428, by rfl⟩ : syracuseStep 328571 = 492857) B492857
theorem B1278985 : Blo 143792 1278985 := bstep (se 2 (by rfl) ⟨479619, by rfl⟩ : syracuseStep 1278985 = 959239) B959239
theorem B328787 : Blo 143792 328787 := bstep (se 1 (by rfl) ⟨246590, by rfl⟩ : syracuseStep 328787 = 493181) B493181
theorem B328859 : Blo 143792 328859 := bstep (se 1 (by rfl) ⟨246644, by rfl⟩ : syracuseStep 328859 = 493289) B493289
theorem B165019 : Blo 143792 165019 := bstep (se 1 (by rfl) ⟨123764, by rfl⟩ : syracuseStep 165019 = 247529) B247529
theorem B329399 : Blo 143792 329399 := bstep (se 1 (by rfl) ⟨247049, by rfl⟩ : syracuseStep 329399 = 494099) B494099
theorem B1771625 : Blo 143792 1771625 := bstep (se 2 (by rfl) ⟨664359, by rfl⟩ : syracuseStep 1771625 = 1328719) B1328719
theorem B329849 : Blo 143792 329849 := bstep (se 2 (by rfl) ⟨123693, by rfl⟩ : syracuseStep 329849 = 247387) B247387
theorem B493775 : Blo 143792 493775 := bstep (se 1 (by rfl) ⟨370331, by rfl⟩ : syracuseStep 493775 = 740663) B740663
theorem B494525 : Blo 143792 494525 := bstep (se 3 (by rfl) ⟨92723, by rfl⟩ : syracuseStep 494525 = 185447) B185447
theorem B10325069 : Blo 143792 10325069 := bstep (se 3 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 10325069 = 3871901) B3871901
theorem B3116339 : Blo 143792 3116339 := bstep (se 1 (by rfl) ⟨2337254, by rfl⟩ : syracuseStep 3116339 = 4674509) B4674509
theorem B495071 : Blo 143792 495071 := bstep (se 1 (by rfl) ⟨371303, by rfl⟩ : syracuseStep 495071 = 742607) B742607
theorem B1773089 : Blo 143792 1773089 := bstep (se 2 (by rfl) ⟨664908, by rfl⟩ : syracuseStep 1773089 = 1329817) B1329817
theorem B6295643 : Blo 143792 6295643 := bstep (se 1 (by rfl) ⟨4721732, by rfl⟩ : syracuseStep 6295643 = 9443465) B9443465
theorem B364763 : Blo 143792 364763 := bstep (se 1 (by rfl) ⟨273572, by rfl⟩ : syracuseStep 364763 = 547145) B547145
theorem B332135 : Blo 143792 332135 := bstep (se 1 (by rfl) ⟨249101, by rfl⟩ : syracuseStep 332135 = 498203) B498203
theorem B332153 : Blo 143792 332153 := bstep (se 2 (by rfl) ⟨124557, by rfl⟩ : syracuseStep 332153 = 249115) B249115
theorem B660095 : Blo 143792 660095 := bstep (se 1 (by rfl) ⟨495071, by rfl⟩ : syracuseStep 660095 = 990143) B990143
theorem B332513 : Blo 143792 332513 := bstep (se 2 (by rfl) ⟨124692, by rfl⟩ : syracuseStep 332513 = 249385) B249385
theorem B496745 : Blo 143792 496745 := bstep (se 2 (by rfl) ⟨186279, by rfl⟩ : syracuseStep 496745 = 372559) B372559
theorem B3020111 : Blo 143792 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B3020165 : Blo 143792 3020165 := bstep (se 4 (by rfl) ⟨283140, by rfl⟩ : syracuseStep 3020165 = 566281) B566281
theorem B2102699 : Blo 143792 2102699 := bstep (se 1 (by rfl) ⟨1577024, by rfl⟩ : syracuseStep 2102699 = 3154049) B3154049
theorem B1873529 : Blo 143792 1873529 := bstep (se 2 (by rfl) ⟨702573, by rfl⟩ : syracuseStep 1873529 = 1405147) B1405147
theorem B2005235 : Blo 143792 2005235 := bstep (se 1 (by rfl) ⟨1503926, by rfl⟩ : syracuseStep 2005235 = 3007853) B3007853
theorem B465821 : Blo 143792 465821 := bstep (se 3 (by rfl) ⟨87341, by rfl⟩ : syracuseStep 465821 = 174683) B174683
theorem B564187 : Blo 143792 564187 := bstep (se 1 (by rfl) ⟨423140, by rfl⟩ : syracuseStep 564187 = 846281) B846281
theorem B3022055 : Blo 143792 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B728513 : Blo 143792 728513 := bstep (se 2 (by rfl) ⟨273192, by rfl⟩ : syracuseStep 728513 = 546385) B546385
theorem B696059 : Blo 143792 696059 := bstep (se 1 (by rfl) ⟨522044, by rfl⟩ : syracuseStep 696059 = 1044089) B1044089
theorem B827279 : Blo 143792 827279 := bstep (se 1 (by rfl) ⟨620459, by rfl⟩ : syracuseStep 827279 = 1240919) B1240919
theorem B728999 : Blo 143792 728999 := bstep (se 1 (by rfl) ⟨546749, by rfl⟩ : syracuseStep 728999 = 1093499) B1093499
theorem B368783 : Blo 143792 368783 := bstep (se 1 (by rfl) ⟨276587, by rfl⟩ : syracuseStep 368783 = 553175) B553175
theorem B1679615 : Blo 143792 1679615 := bstep (se 1 (by rfl) ⟨1259711, by rfl⟩ : syracuseStep 1679615 = 2519423) B2519423
theorem B369319 : Blo 143792 369319 := bstep (se 1 (by rfl) ⟨276989, by rfl⟩ : syracuseStep 369319 = 553979) B553979
theorem B2826971 : Blo 143792 2826971 := bstep (se 1 (by rfl) ⟨2120228, by rfl⟩ : syracuseStep 2826971 = 4240457) B4240457
theorem B1418255 : Blo 143792 1418255 := bstep (se 1 (by rfl) ⟨1063691, by rfl⟩ : syracuseStep 1418255 = 2127383) B2127383
theorem B369755 : Blo 143792 369755 := bstep (se 1 (by rfl) ⟨277316, by rfl⟩ : syracuseStep 369755 = 554633) B554633
theorem B730295 : Blo 143792 730295 := bstep (se 1 (by rfl) ⟨547721, by rfl⟩ : syracuseStep 730295 = 1095443) B1095443
theorem B370727 : Blo 143792 370727 := bstep (se 1 (by rfl) ⟨278045, by rfl⟩ : syracuseStep 370727 = 556091) B556091
theorem B1124543 : Blo 143792 1124543 := bstep (se 1 (by rfl) ⟨843407, by rfl⟩ : syracuseStep 1124543 = 1686815) B1686815
theorem B2370343 : Blo 143792 2370343 := bstep (se 1 (by rfl) ⟨1777757, by rfl⟩ : syracuseStep 2370343 = 3555515) B3555515
theorem B7908191 : Blo 143792 7908191 := bstep (se 1 (by rfl) ⟨5931143, by rfl⟩ : syracuseStep 7908191 = 11862287) B11862287
theorem B1650455 : Blo 143792 1650455 := bstep (se 1 (by rfl) ⟨1237841, by rfl⟩ : syracuseStep 1650455 = 2475683) B2475683
theorem B470855 : Blo 143792 470855 := bstep (se 1 (by rfl) ⟨353141, by rfl⟩ : syracuseStep 470855 = 706283) B706283
theorem B372833 : Blo 143792 372833 := bstep (se 2 (by rfl) ⟨139812, by rfl⟩ : syracuseStep 372833 = 279625) B279625
theorem B143839 : Blo 143792 143839 := bstep (se 1 (by rfl) ⟨107879, by rfl⟩ : syracuseStep 143839 = 215759) B215759
theorem B143963 : Blo 143792 143963 := bstep (se 1 (by rfl) ⟨107972, by rfl⟩ : syracuseStep 143963 = 215945) B215945
theorem B373643 : Blo 143792 373643 := bstep (se 1 (by rfl) ⟨280232, by rfl⟩ : syracuseStep 373643 = 560465) B560465
theorem B1848257 : Blo 143792 1848257 := bstep (se 2 (by rfl) ⟨693096, by rfl⟩ : syracuseStep 1848257 = 1386193) B1386193
theorem B2536555 : Blo 143792 2536555 := bstep (se 1 (by rfl) ⟨1902416, by rfl⟩ : syracuseStep 2536555 = 3804833) B3804833
theorem B144863 : Blo 143792 144863 := bstep (se 1 (by rfl) ⟨108647, by rfl⟩ : syracuseStep 144863 = 217295) B217295
theorem B144943 : Blo 143792 144943 := bstep (se 1 (by rfl) ⟨108707, by rfl⟩ : syracuseStep 144943 = 217415) B217415
theorem B243337 : Blo 143792 243337 := bstep (se 2 (by rfl) ⟨91251, by rfl⟩ : syracuseStep 243337 = 182503) B182503
theorem B1259165 : Blo 143792 1259165 := bstep (se 3 (by rfl) ⟨236093, by rfl⟩ : syracuseStep 1259165 = 472187) B472187
theorem B2209451 : Blo 143792 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B276527 : Blo 143792 276527 := bstep (se 1 (by rfl) ⟨207395, by rfl⟩ : syracuseStep 276527 = 414791) B414791
theorem B145535 : Blo 143792 145535 := bstep (se 1 (by rfl) ⟨109151, by rfl⟩ : syracuseStep 145535 = 218303) B218303
theorem B473303 : Blo 143792 473303 := bstep (se 1 (by rfl) ⟨354977, by rfl⟩ : syracuseStep 473303 = 709955) B709955
theorem B932255 : Blo 143792 932255 := bstep (se 1 (by rfl) ⟨699191, by rfl⟩ : syracuseStep 932255 = 1398383) B1398383
theorem B998183 : Blo 143792 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B671003 : Blo 143792 671003 := bstep (se 1 (by rfl) ⟨503252, by rfl⟩ : syracuseStep 671003 = 1006505) B1006505
theorem B34356575 : Blo 143792 34356575 := bstep (se 1 (by rfl) ⟨25767431, by rfl⟩ : syracuseStep 34356575 = 51534863) B51534863
theorem B146879 : Blo 143792 146879 := bstep (se 1 (by rfl) ⟨110159, by rfl⟩ : syracuseStep 146879 = 220319) B220319
theorem B441911 : Blo 143792 441911 := bstep (se 1 (by rfl) ⟨331433, by rfl⟩ : syracuseStep 441911 = 662867) B662867
theorem B147047 : Blo 143792 147047 := bstep (se 1 (by rfl) ⟨110285, by rfl⟩ : syracuseStep 147047 = 220571) B220571
theorem B147327 : Blo 143792 147327 := bstep (se 1 (by rfl) ⟨110495, by rfl⟩ : syracuseStep 147327 = 220991) B220991
theorem B147439 : Blo 143792 147439 := bstep (se 1 (by rfl) ⟨110579, by rfl⟩ : syracuseStep 147439 = 221159) B221159
theorem B5324791 : Blo 143792 5324791 := bstep (se 1 (by rfl) ⟨3993593, by rfl⟩ : syracuseStep 5324791 = 7987187) B7987187
theorem B278569 : Blo 143792 278569 := bstep (se 2 (by rfl) ⟨104463, by rfl⟩ : syracuseStep 278569 = 208927) B208927
theorem B147519 : Blo 143792 147519 := bstep (se 1 (by rfl) ⟨110639, by rfl⟩ : syracuseStep 147519 = 221279) B221279
theorem B147559 : Blo 143792 147559 := bstep (se 1 (by rfl) ⟨110669, by rfl⟩ : syracuseStep 147559 = 221339) B221339
theorem B147679 : Blo 143792 147679 := bstep (se 1 (by rfl) ⟨110759, by rfl⟩ : syracuseStep 147679 = 221519) B221519
theorem B2868047 : Blo 143792 2868047 := bstep (se 1 (by rfl) ⟨2151035, by rfl⟩ : syracuseStep 2868047 = 4302071) B4302071
theorem B3131905 : Blo 143792 3131905 := bstep (se 2 (by rfl) ⟨1174464, by rfl⟩ : syracuseStep 3131905 = 2348929) B2348929
theorem B2607839 : Blo 143792 2607839 := bstep (se 1 (by rfl) ⟨1955879, by rfl⟩ : syracuseStep 2607839 = 3911759) B3911759
theorem B740177 : Blo 143792 740177 := bstep (se 2 (by rfl) ⟨277566, by rfl⟩ : syracuseStep 740177 = 555133) B555133
theorem B216575 : Blo 143792 216575 := bstep (se 1 (by rfl) ⟨162431, by rfl⟩ : syracuseStep 216575 = 324863) B324863
theorem B216647 : Blo 143792 216647 := bstep (se 1 (by rfl) ⟨162485, by rfl⟩ : syracuseStep 216647 = 324971) B324971
theorem B413275 : Blo 143792 413275 := bstep (se 1 (by rfl) ⟨309956, by rfl⟩ : syracuseStep 413275 = 619913) B619913
theorem B217199 : Blo 143792 217199 := bstep (se 1 (by rfl) ⟨162899, by rfl⟩ : syracuseStep 217199 = 325799) B325799
theorem B709033 : Blo 143792 709033 := bstep (se 2 (by rfl) ⟨265887, by rfl⟩ : syracuseStep 709033 = 531775) B531775
theorem B1167979 : Blo 143792 1167979 := bstep (se 1 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 1167979 = 1751969) B1751969
theorem B185323 : Blo 143792 185323 := bstep (se 1 (by rfl) ⟨138992, by rfl⟩ : syracuseStep 185323 = 277985) B277985
theorem B218279 : Blo 143792 218279 := bstep (se 1 (by rfl) ⟨163709, by rfl⟩ : syracuseStep 218279 = 327419) B327419
theorem B414983 : Blo 143792 414983 := bstep (se 1 (by rfl) ⟨311237, by rfl⟩ : syracuseStep 414983 = 622475) B622475
theorem B1594673 : Blo 143792 1594673 := bstep (se 2 (by rfl) ⟨598002, by rfl⟩ : syracuseStep 1594673 = 1196005) B1196005
theorem B218447 : Blo 143792 218447 := bstep (se 1 (by rfl) ⟨163835, by rfl⟩ : syracuseStep 218447 = 327671) B327671
theorem B742931 : Blo 143792 742931 := bstep (se 1 (by rfl) ⟨557198, by rfl⟩ : syracuseStep 742931 = 1114397) B1114397
theorem B218687 : Blo 143792 218687 := bstep (se 1 (by rfl) ⟨164015, by rfl⟩ : syracuseStep 218687 = 328031) B328031
theorem B546689 : Blo 143792 546689 := bstep (se 2 (by rfl) ⟨205008, by rfl⟩ : syracuseStep 546689 = 410017) B410017
theorem B219131 : Blo 143792 219131 := bstep (se 1 (by rfl) ⟨164348, by rfl⟩ : syracuseStep 219131 = 328697) B328697
theorem B219167 : Blo 143792 219167 := bstep (se 1 (by rfl) ⟨164375, by rfl⟩ : syracuseStep 219167 = 328751) B328751
theorem B546857 : Blo 143792 546857 := bstep (se 2 (by rfl) ⟨205071, by rfl⟩ : syracuseStep 546857 = 410143) B410143
theorem B3955067 : Blo 143792 3955067 := bstep (se 1 (by rfl) ⟨2966300, by rfl⟩ : syracuseStep 3955067 = 5932601) B5932601
theorem B416249 : Blo 143792 416249 := bstep (se 2 (by rfl) ⟨156093, by rfl⟩ : syracuseStep 416249 = 312187) B312187
theorem B350911 : Blo 143792 350911 := bstep (se 1 (by rfl) ⟨263183, by rfl⟩ : syracuseStep 350911 = 526367) B526367
theorem B1563623 : Blo 143792 1563623 := bstep (se 1 (by rfl) ⟨1172717, by rfl⟩ : syracuseStep 1563623 = 2345435) B2345435
theorem B220271 : Blo 143792 220271 := bstep (se 1 (by rfl) ⟨165203, by rfl⟩ : syracuseStep 220271 = 330407) B330407
theorem B220457 : Blo 143792 220457 := bstep (se 2 (by rfl) ⟨82671, by rfl⟩ : syracuseStep 220457 = 165343) B165343
theorem B417079 : Blo 143792 417079 := bstep (se 1 (by rfl) ⟨312809, by rfl⟩ : syracuseStep 417079 = 625619) B625619
theorem B777701 : Blo 143792 777701 := bstep (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) B145819
theorem B548633 : Blo 143792 548633 := bstep (se 2 (by rfl) ⟨205737, by rfl⟩ : syracuseStep 548633 = 411475) B411475
theorem B220955 : Blo 143792 220955 := bstep (se 1 (by rfl) ⟨165716, by rfl⟩ : syracuseStep 220955 = 331433) B331433
theorem B876743 : Blo 143792 876743 := bstep (se 1 (by rfl) ⟨657557, by rfl⟩ : syracuseStep 876743 = 1315115) B1315115
theorem B1106135 : Blo 143792 1106135 := bstep (se 1 (by rfl) ⟨829601, by rfl⟩ : syracuseStep 1106135 = 1659203) B1659203
theorem B1860407 : Blo 143792 1860407 := bstep (se 1 (by rfl) ⟨1395305, by rfl⟩ : syracuseStep 1860407 = 2790611) B2790611
theorem B615367 : Blo 143792 615367 := bstep (se 1 (by rfl) ⟨461525, by rfl⟩ : syracuseStep 615367 = 923051) B923051
theorem B3008015 : Blo 143792 3008015 := bstep (se 1 (by rfl) ⟨2256011, by rfl⟩ : syracuseStep 3008015 = 4512023) B4512023
theorem B485729 : Blo 143792 485729 := bstep (se 2 (by rfl) ⟨182148, by rfl⟩ : syracuseStep 485729 = 364297) B364297
theorem B748115 : Blo 143792 748115 := bstep (se 1 (by rfl) ⟨561086, by rfl⟩ : syracuseStep 748115 = 1122173) B1122173
theorem B4222003 : Blo 143792 4222003 := bstep (se 1 (by rfl) ⟨3166502, by rfl⟩ : syracuseStep 4222003 = 6333005) B6333005
theorem B323567 : Blo 143792 323567 := bstep (se 1 (by rfl) ⟨242675, by rfl⟩ : syracuseStep 323567 = 485351) B485351
theorem B8384957 : Blo 143792 8384957 := bstep (se 3 (by rfl) ⟨1572179, by rfl⟩ : syracuseStep 8384957 = 3144359) B3144359
theorem B324719 : Blo 143792 324719 := bstep (se 1 (by rfl) ⟨243539, by rfl⟩ : syracuseStep 324719 = 487079) B487079
theorem B324935 : Blo 143792 324935 := bstep (se 1 (by rfl) ⟨243701, by rfl⟩ : syracuseStep 324935 = 487403) B487403
theorem B325403 : Blo 143792 325403 := bstep (se 1 (by rfl) ⟨244052, by rfl⟩ : syracuseStep 325403 = 488105) B488105
theorem B293033 : Blo 143792 293033 := bstep (se 2 (by rfl) ⟨109887, by rfl⟩ : syracuseStep 293033 = 219775) B219775
theorem B162751 : Blo 143792 162751 := bstep (se 1 (by rfl) ⟨122063, by rfl⟩ : syracuseStep 162751 = 244127) B244127
theorem B326843 : Blo 143792 326843 := bstep (se 1 (by rfl) ⟨245132, by rfl⟩ : syracuseStep 326843 = 490265) B490265
theorem B1113425 : Blo 143792 1113425 := bstep (se 2 (by rfl) ⟨417534, by rfl⟩ : syracuseStep 1113425 = 835069) B835069
theorem B327239 : Blo 143792 327239 := bstep (se 1 (by rfl) ⟨245429, by rfl⟩ : syracuseStep 327239 = 490859) B490859
theorem B425627 : Blo 143792 425627 := bstep (se 1 (by rfl) ⟨319220, by rfl⟩ : syracuseStep 425627 = 638441) B638441
theorem B492425 : Blo 143792 492425 := bstep (se 2 (by rfl) ⟨184659, by rfl⟩ : syracuseStep 492425 = 369319) B369319
theorem B820489 : Blo 143792 820489 := bstep (se 2 (by rfl) ⟨307683, by rfl⟩ : syracuseStep 820489 = 615367) B615367
theorem B1705313 : Blo 143792 1705313 := bstep (se 2 (by rfl) ⟨639492, by rfl⟩ : syracuseStep 1705313 = 1278985) B1278985
theorem B1181083 : Blo 143792 1181083 := bstep (se 1 (by rfl) ⟨885812, by rfl⟩ : syracuseStep 1181083 = 1771625) B1771625
theorem B329183 : Blo 143792 329183 := bstep (se 1 (by rfl) ⟨246887, by rfl⟩ : syracuseStep 329183 = 493775) B493775
theorem B1738559 : Blo 143792 1738559 := bstep (se 1 (by rfl) ⟨1303919, by rfl⟩ : syracuseStep 1738559 = 2607839) B2607839
theorem B493451 : Blo 143792 493451 := bstep (se 1 (by rfl) ⟨370088, by rfl⟩ : syracuseStep 493451 = 740177) B740177
theorem B329683 : Blo 143792 329683 := bstep (se 1 (by rfl) ⟨247262, by rfl⟩ : syracuseStep 329683 = 494525) B494525
theorem B6883379 : Blo 143792 6883379 := bstep (se 1 (by rfl) ⟨5162534, by rfl⟩ : syracuseStep 6883379 = 10325069) B10325069
theorem B330047 : Blo 143792 330047 := bstep (se 1 (by rfl) ⟨247535, by rfl⟩ : syracuseStep 330047 = 495071) B495071
theorem B1182059 : Blo 143792 1182059 := bstep (se 1 (by rfl) ⟨886544, by rfl⟩ : syracuseStep 1182059 = 1773089) B1773089
theorem B4197095 : Blo 143792 4197095 := bstep (se 1 (by rfl) ⟨3147821, by rfl⟩ : syracuseStep 4197095 = 6295643) B6295643
theorem B331163 : Blo 143792 331163 := bstep (se 1 (by rfl) ⟨248372, by rfl⟩ : syracuseStep 331163 = 496745) B496745
theorem B1871525 : Blo 143792 1871525 := bstep (se 4 (by rfl) ⟨175455, by rfl⟩ : syracuseStep 1871525 = 350911) B350911
theorem B495287 : Blo 143792 495287 := bstep (se 1 (by rfl) ⟨371465, by rfl⟩ : syracuseStep 495287 = 742931) B742931
theorem B1249019 : Blo 143792 1249019 := bstep (se 1 (by rfl) ⟨936764, by rfl⟩ : syracuseStep 1249019 = 1873529) B1873529
theorem B364459 : Blo 143792 364459 := bstep (se 1 (by rfl) ⟨273344, by rfl⟩ : syracuseStep 364459 = 546689) B546689
theorem B364571 : Blo 143792 364571 := bstep (se 1 (by rfl) ⟨273428, by rfl⟩ : syracuseStep 364571 = 546857) B546857
theorem B464039 : Blo 143792 464039 := bstep (se 1 (by rfl) ⟨348029, by rfl⟩ : syracuseStep 464039 = 696059) B696059
theorem B365755 : Blo 143792 365755 := bstep (se 1 (by rfl) ⟨274316, by rfl⟩ : syracuseStep 365755 = 548633) B548633
theorem B1119743 : Blo 143792 1119743 := bstep (se 1 (by rfl) ⟨839807, by rfl⟩ : syracuseStep 1119743 = 1679615) B1679615
theorem B2005343 : Blo 143792 2005343 := bstep (se 1 (by rfl) ⟨1504007, by rfl⟩ : syracuseStep 2005343 = 3008015) B3008015
theorem B3382073 : Blo 143792 3382073 := bstep (se 2 (by rfl) ⟨1268277, by rfl⟩ : syracuseStep 3382073 = 2536555) B2536555
theorem B498743 : Blo 143792 498743 := bstep (se 1 (by rfl) ⟨374057, by rfl⟩ : syracuseStep 498743 = 748115) B748115
theorem B2661821 : Blo 143792 2661821 := bstep (se 3 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 2661821 = 998183) B998183
theorem B2073869 : Blo 143792 2073869 := bstep (se 3 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 2073869 = 777701) B777701
theorem B371425 : Blo 143792 371425 := bstep (se 2 (by rfl) ⟨139284, by rfl⟩ : syracuseStep 371425 = 278569) B278569
theorem B371567 : Blo 143792 371567 := bstep (se 1 (by rfl) ⟨278675, by rfl⟩ : syracuseStep 371567 = 557351) B557351
theorem B1912031 : Blo 143792 1912031 := bstep (se 1 (by rfl) ⟨1434023, by rfl⟩ : syracuseStep 1912031 = 2868047) B2868047
theorem B2077559 : Blo 143792 2077559 := bstep (se 1 (by rfl) ⟨1558169, by rfl⟩ : syracuseStep 2077559 = 3116339) B3116339
theorem B144383 : Blo 143792 144383 := bstep (se 1 (by rfl) ⟨108287, by rfl⟩ : syracuseStep 144383 = 216575) B216575
theorem B144431 : Blo 143792 144431 := bstep (se 1 (by rfl) ⟨108323, by rfl⟩ : syracuseStep 144431 = 216647) B216647
theorem B144799 : Blo 143792 144799 := bstep (se 1 (by rfl) ⟨108599, by rfl⟩ : syracuseStep 144799 = 217199) B217199
theorem B243175 : Blo 143792 243175 := bstep (se 1 (by rfl) ⟨182381, by rfl⟩ : syracuseStep 243175 = 364763) B364763
theorem B440063 : Blo 143792 440063 := bstep (se 1 (by rfl) ⟨330047, by rfl⟩ : syracuseStep 440063 = 660095) B660095
theorem B4175873 : Blo 143792 4175873 := bstep (se 2 (by rfl) ⟨1565952, by rfl⟩ : syracuseStep 4175873 = 3131905) B3131905
theorem B145519 : Blo 143792 145519 := bstep (se 1 (by rfl) ⟨109139, by rfl⟩ : syracuseStep 145519 = 218279) B218279
theorem B1063115 : Blo 143792 1063115 := bstep (se 1 (by rfl) ⟨797336, by rfl⟩ : syracuseStep 1063115 = 1594673) B1594673
theorem B2013407 : Blo 143792 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B145631 : Blo 143792 145631 := bstep (se 1 (by rfl) ⟨109223, by rfl⟩ : syracuseStep 145631 = 218447) B218447
theorem B2013443 : Blo 143792 2013443 := bstep (se 1 (by rfl) ⟨1510082, by rfl⟩ : syracuseStep 2013443 = 3020165) B3020165
theorem B145791 : Blo 143792 145791 := bstep (se 1 (by rfl) ⟨109343, by rfl⟩ : syracuseStep 145791 = 218687) B218687
theorem B3160457 : Blo 143792 3160457 := bstep (se 2 (by rfl) ⟨1185171, by rfl⟩ : syracuseStep 3160457 = 2370343) B2370343
theorem B146087 : Blo 143792 146087 := bstep (se 1 (by rfl) ⟨109565, by rfl⟩ : syracuseStep 146087 = 219131) B219131
theorem B146111 : Blo 143792 146111 := bstep (se 1 (by rfl) ⟨109583, by rfl⟩ : syracuseStep 146111 = 219167) B219167
theorem B2636711 : Blo 143792 2636711 := bstep (se 1 (by rfl) ⟨1977533, by rfl⟩ : syracuseStep 2636711 = 3955067) B3955067
theorem B277499 : Blo 143792 277499 := bstep (se 1 (by rfl) ⟨208124, by rfl⟩ : syracuseStep 277499 = 416249) B416249
theorem B310547 : Blo 143792 310547 := bstep (se 1 (by rfl) ⟨232910, by rfl⟩ : syracuseStep 310547 = 465821) B465821
theorem B146847 : Blo 143792 146847 := bstep (se 1 (by rfl) ⟨110135, by rfl⟩ : syracuseStep 146847 = 220271) B220271
theorem B2014703 : Blo 143792 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B146971 : Blo 143792 146971 := bstep (se 1 (by rfl) ⟨110228, by rfl⟩ : syracuseStep 146971 = 220457) B220457
theorem B147303 : Blo 143792 147303 := bstep (se 1 (by rfl) ⟨110477, by rfl⟩ : syracuseStep 147303 = 220955) B220955
theorem B245855 : Blo 143792 245855 := bstep (se 1 (by rfl) ⟨184391, by rfl⟩ : syracuseStep 245855 = 368783) B368783
theorem B737423 : Blo 143792 737423 := bstep (se 1 (by rfl) ⟨553067, by rfl⟩ : syracuseStep 737423 = 1106135) B1106135
theorem B1884647 : Blo 143792 1884647 := bstep (se 1 (by rfl) ⟨1413485, by rfl⟩ : syracuseStep 1884647 = 2826971) B2826971
theorem B2998781 : Blo 143792 2998781 := bstep (se 3 (by rfl) ⟨562271, by rfl⟩ : syracuseStep 2998781 = 1124543) B1124543
theorem B1262141 : Blo 143792 1262141 := bstep (se 3 (by rfl) ⟨236651, by rfl⟩ : syracuseStep 1262141 = 473303) B473303
theorem B246503 : Blo 143792 246503 := bstep (se 1 (by rfl) ⟨184877, by rfl⟩ : syracuseStep 246503 = 369755) B369755
theorem B1557305 : Blo 143792 1557305 := bstep (se 2 (by rfl) ⟨583989, by rfl⟩ : syracuseStep 1557305 = 1167979) B1167979
theorem B247097 : Blo 143792 247097 := bstep (se 2 (by rfl) ⟨92661, by rfl⟩ : syracuseStep 247097 = 185323) B185323
theorem B247151 : Blo 143792 247151 := bstep (se 1 (by rfl) ⟨185363, by rfl⟩ : syracuseStep 247151 = 370727) B370727
theorem B1100303 : Blo 143792 1100303 := bstep (se 1 (by rfl) ⟨825227, by rfl⟩ : syracuseStep 1100303 = 1650455) B1650455
theorem B313903 : Blo 143792 313903 := bstep (se 1 (by rfl) ⟨235427, by rfl⟩ : syracuseStep 313903 = 470855) B470855
theorem B215711 : Blo 143792 215711 := bstep (se 1 (by rfl) ⟨161783, by rfl⟩ : syracuseStep 215711 = 323567) B323567
theorem B248555 : Blo 143792 248555 := bstep (se 1 (by rfl) ⟨186416, by rfl⟩ : syracuseStep 248555 = 372833) B372833
theorem B5589971 : Blo 143792 5589971 := bstep (se 1 (by rfl) ⟨4192478, by rfl⟩ : syracuseStep 5589971 = 8384957) B8384957
theorem B249095 : Blo 143792 249095 := bstep (se 1 (by rfl) ⟨186821, by rfl⟩ : syracuseStep 249095 = 373643) B373643
theorem B1232171 : Blo 143792 1232171 := bstep (se 1 (by rfl) ⟨924128, by rfl⟩ : syracuseStep 1232171 = 1848257) B1848257
theorem B216479 : Blo 143792 216479 := bstep (se 1 (by rfl) ⟨162359, by rfl⟩ : syracuseStep 216479 = 324719) B324719
theorem B216623 : Blo 143792 216623 := bstep (se 1 (by rfl) ⟨162467, by rfl⟩ : syracuseStep 216623 = 324935) B324935
theorem B839443 : Blo 143792 839443 := bstep (se 1 (by rfl) ⟨629582, by rfl⟩ : syracuseStep 839443 = 1259165) B1259165
theorem B216935 : Blo 143792 216935 := bstep (se 1 (by rfl) ⟨162701, by rfl⟩ : syracuseStep 216935 = 325403) B325403
theorem B217001 : Blo 143792 217001 := bstep (se 2 (by rfl) ⟨81375, by rfl⟩ : syracuseStep 217001 = 162751) B162751
theorem B184351 : Blo 143792 184351 := bstep (se 1 (by rfl) ⟨138263, by rfl⟩ : syracuseStep 184351 = 276527) B276527
theorem B217895 : Blo 143792 217895 := bstep (se 1 (by rfl) ⟨163421, by rfl⟩ : syracuseStep 217895 = 326843) B326843
theorem B447335 : Blo 143792 447335 := bstep (se 1 (by rfl) ⟨335501, by rfl⟩ : syracuseStep 447335 = 671003) B671003
theorem B742283 : Blo 143792 742283 := bstep (se 1 (by rfl) ⟨556712, by rfl⟩ : syracuseStep 742283 = 1113425) B1113425
theorem B218159 : Blo 143792 218159 := bstep (se 1 (by rfl) ⟨163619, by rfl⟩ : syracuseStep 218159 = 327239) B327239
theorem B283751 : Blo 143792 283751 := bstep (se 1 (by rfl) ⟨212813, by rfl⟩ : syracuseStep 283751 = 425627) B425627
theorem B7099721 : Blo 143792 7099721 := bstep (se 2 (by rfl) ⟨2662395, by rfl⟩ : syracuseStep 7099721 = 5324791) B5324791
theorem B218603 : Blo 143792 218603 := bstep (se 1 (by rfl) ⟨163952, by rfl⟩ : syracuseStep 218603 = 327905) B327905
theorem B219035 : Blo 143792 219035 := bstep (se 1 (by rfl) ⟨164276, by rfl⟩ : syracuseStep 219035 = 328553) B328553
theorem B219047 : Blo 143792 219047 := bstep (se 1 (by rfl) ⟨164285, by rfl⟩ : syracuseStep 219047 = 328571) B328571
theorem B219191 : Blo 143792 219191 := bstep (se 1 (by rfl) ⟨164393, by rfl⟩ : syracuseStep 219191 = 328787) B328787
theorem B219239 : Blo 143792 219239 := bstep (se 1 (by rfl) ⟨164429, by rfl⟩ : syracuseStep 219239 = 328859) B328859
theorem B219599 : Blo 143792 219599 := bstep (se 1 (by rfl) ⟨164699, by rfl⟩ : syracuseStep 219599 = 329399) B329399
theorem B219899 : Blo 143792 219899 := bstep (se 1 (by rfl) ⟨164924, by rfl⟩ : syracuseStep 219899 = 329849) B329849
theorem B220025 : Blo 143792 220025 := bstep (se 2 (by rfl) ⟨82509, by rfl⟩ : syracuseStep 220025 = 165019) B165019
theorem B221423 : Blo 143792 221423 := bstep (se 1 (by rfl) ⟨166067, by rfl⟩ : syracuseStep 221423 = 332135) B332135
theorem B221435 : Blo 143792 221435 := bstep (se 1 (by rfl) ⟨166076, by rfl⟩ : syracuseStep 221435 = 332153) B332153
theorem B221675 : Blo 143792 221675 := bstep (se 1 (by rfl) ⟨166256, by rfl⟩ : syracuseStep 221675 = 332513) B332513
theorem B1106621 : Blo 143792 1106621 := bstep (se 3 (by rfl) ⟨207491, by rfl⟩ : syracuseStep 1106621 = 414983) B414983
theorem B1401799 : Blo 143792 1401799 := bstep (se 1 (by rfl) ⟨1051349, by rfl⟩ : syracuseStep 1401799 = 2102699) B2102699
theorem B5629337 : Blo 143792 5629337 := bstep (se 2 (by rfl) ⟨2111001, by rfl⟩ : syracuseStep 5629337 = 4222003) B4222003
theorem B1336823 : Blo 143792 1336823 := bstep (se 1 (by rfl) ⟨1002617, by rfl⟩ : syracuseStep 1336823 = 2005235) B2005235
theorem B5891869 : Blo 143792 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B1042415 : Blo 143792 1042415 := bstep (se 1 (by rfl) ⟨781811, by rfl⟩ : syracuseStep 1042415 = 1563623) B1563623
theorem B551033 : Blo 143792 551033 := bstep (se 2 (by rfl) ⟨206637, by rfl⟩ : syracuseStep 551033 = 413275) B413275
theorem B485675 : Blo 143792 485675 := bstep (se 1 (by rfl) ⟨364256, by rfl⟩ : syracuseStep 485675 = 728513) B728513
theorem B551519 : Blo 143792 551519 := bstep (se 1 (by rfl) ⟨413639, by rfl⟩ : syracuseStep 551519 = 827279) B827279
theorem B485999 : Blo 143792 485999 := bstep (se 1 (by rfl) ⟨364499, by rfl⟩ : syracuseStep 485999 = 728999) B728999
theorem B584495 : Blo 143792 584495 := bstep (se 1 (by rfl) ⟨438371, by rfl⟩ : syracuseStep 584495 = 876743) B876743
theorem B1240271 : Blo 143792 1240271 := bstep (se 1 (by rfl) ⟨930203, by rfl⟩ : syracuseStep 1240271 = 1860407) B1860407
theorem B945377 : Blo 143792 945377 := bstep (se 2 (by rfl) ⟨354516, by rfl⟩ : syracuseStep 945377 = 709033) B709033
theorem B945503 : Blo 143792 945503 := bstep (se 1 (by rfl) ⟨709127, by rfl⟩ : syracuseStep 945503 = 1418255) B1418255
theorem B486863 : Blo 143792 486863 := bstep (se 1 (by rfl) ⟨365147, by rfl⟩ : syracuseStep 486863 = 730295) B730295
theorem B323819 : Blo 143792 323819 := bstep (se 1 (by rfl) ⟨242864, by rfl⟩ : syracuseStep 323819 = 485729) B485729
theorem B5272127 : Blo 143792 5272127 := bstep (se 1 (by rfl) ⟨3954095, by rfl⟩ : syracuseStep 5272127 = 7908191) B7908191
theorem B324449 : Blo 143792 324449 := bstep (se 2 (by rfl) ⟨121668, by rfl⟩ : syracuseStep 324449 = 243337) B243337
theorem B752249 : Blo 143792 752249 := bstep (se 2 (by rfl) ⟨282093, by rfl⟩ : syracuseStep 752249 = 564187) B564187
theorem B195355 : Blo 143792 195355 := bstep (se 1 (by rfl) ⟨146516, by rfl⟩ : syracuseStep 195355 = 293033) B293033
theorem B621503 : Blo 143792 621503 := bstep (se 1 (by rfl) ⟨466127, by rfl⟩ : syracuseStep 621503 = 932255) B932255
theorem B556105 : Blo 143792 556105 := bstep (se 2 (by rfl) ⟨208539, by rfl⟩ : syracuseStep 556105 = 417079) B417079
theorem B22904383 : Blo 143792 22904383 := bstep (se 1 (by rfl) ⟨17178287, by rfl⟩ : syracuseStep 22904383 = 34356575) B34356575
theorem B294607 : Blo 143792 294607 := bstep (se 1 (by rfl) ⟨220955, by rfl⟩ : syracuseStep 294607 = 441911) B441911
theorem B163903 : Blo 143792 163903 := bstep (se 1 (by rfl) ⟨122927, by rfl⟩ : syracuseStep 163903 = 245855) B245855
theorem B491615 : Blo 143792 491615 := bstep (se 1 (by rfl) ⟨368711, by rfl⟩ : syracuseStep 491615 = 737423) B737423
theorem B1999187 : Blo 143792 1999187 := bstep (se 1 (by rfl) ⟨1499390, by rfl⟩ : syracuseStep 1999187 = 2998781) B2998781
theorem B164335 : Blo 143792 164335 := bstep (se 1 (by rfl) ⟨123251, by rfl⟩ : syracuseStep 164335 = 246503) B246503
theorem B328283 : Blo 143792 328283 := bstep (se 1 (by rfl) ⟨246212, by rfl⟩ : syracuseStep 328283 = 492425) B492425
theorem B164731 : Blo 143792 164731 := bstep (se 1 (by rfl) ⟨123548, by rfl⟩ : syracuseStep 164731 = 247097) B247097
theorem B164767 : Blo 143792 164767 := bstep (se 1 (by rfl) ⟨123575, by rfl⟩ : syracuseStep 164767 = 247151) B247151
theorem B328967 : Blo 143792 328967 := bstep (se 1 (by rfl) ⟨246725, by rfl⟩ : syracuseStep 328967 = 493451) B493451
theorem B1869065 : Blo 143792 1869065 := bstep (se 2 (by rfl) ⟨700899, by rfl⟩ : syracuseStep 1869065 = 1401799) B1401799
theorem B4588919 : Blo 143792 4588919 := bstep (se 1 (by rfl) ⟨3441689, by rfl⟩ : syracuseStep 4588919 = 6883379) B6883379
theorem B788039 : Blo 143792 788039 := bstep (se 1 (by rfl) ⟨591029, by rfl⟩ : syracuseStep 788039 = 1182059) B1182059
theorem B165703 : Blo 143792 165703 := bstep (se 1 (by rfl) ⟨124277, by rfl⟩ : syracuseStep 165703 = 248555) B248555
theorem B1574777 : Blo 143792 1574777 := bstep (se 2 (by rfl) ⟨590541, by rfl⟩ : syracuseStep 1574777 = 1181083) B1181083
theorem B166063 : Blo 143792 166063 := bstep (se 1 (by rfl) ⟨124547, by rfl⟩ : syracuseStep 166063 = 249095) B249095
theorem B821447 : Blo 143792 821447 := bstep (se 1 (by rfl) ⟨616085, by rfl⟩ : syracuseStep 821447 = 1232171) B1232171
theorem B1247683 : Blo 143792 1247683 := bstep (se 1 (by rfl) ⟨935762, by rfl⟩ : syracuseStep 1247683 = 1871525) B1871525
theorem B330191 : Blo 143792 330191 := bstep (se 1 (by rfl) ⟨247643, by rfl⟩ : syracuseStep 330191 = 495287) B495287
theorem B298223 : Blo 143792 298223 := bstep (se 1 (by rfl) ⟨223667, by rfl⟩ : syracuseStep 298223 = 447335) B447335
theorem B494855 : Blo 143792 494855 := bstep (se 1 (by rfl) ⟨371141, by rfl⟩ : syracuseStep 494855 = 742283) B742283
theorem B495233 : Blo 143792 495233 := bstep (se 2 (by rfl) ⟨185712, by rfl⟩ : syracuseStep 495233 = 371425) B371425
theorem B332495 : Blo 143792 332495 := bstep (se 1 (by rfl) ⟨249371, by rfl⟩ : syracuseStep 332495 = 498743) B498743
theorem B1774547 : Blo 143792 1774547 := bstep (se 1 (by rfl) ⟨1330910, by rfl⟩ : syracuseStep 1774547 = 2661821) B2661821
theorem B1119257 : Blo 143792 1119257 := bstep (se 2 (by rfl) ⟨419721, by rfl⟩ : syracuseStep 1119257 = 839443) B839443
theorem B1382579 : Blo 143792 1382579 := bstep (se 1 (by rfl) ⟨1036934, by rfl⟩ : syracuseStep 1382579 = 2073869) B2073869
theorem B891215 : Blo 143792 891215 := bstep (se 1 (by rfl) ⟨668411, by rfl⟩ : syracuseStep 891215 = 1336823) B1336823
theorem B694943 : Blo 143792 694943 := bstep (se 1 (by rfl) ⟨521207, by rfl⟩ : syracuseStep 694943 = 1042415) B1042415
theorem B367355 : Blo 143792 367355 := bstep (se 1 (by rfl) ⟨275516, by rfl⟩ : syracuseStep 367355 = 551033) B551033
theorem B367679 : Blo 143792 367679 := bstep (se 1 (by rfl) ⟨275759, by rfl⟩ : syracuseStep 367679 = 551519) B551519
theorem B826847 : Blo 143792 826847 := bstep (se 1 (by rfl) ⟨620135, by rfl⟩ : syracuseStep 826847 = 1240271) B1240271
theorem B630251 : Blo 143792 630251 := bstep (se 1 (by rfl) ⟨472688, by rfl⟩ : syracuseStep 630251 = 945377) B945377
theorem B630335 : Blo 143792 630335 := bstep (se 1 (by rfl) ⟨472751, by rfl⟩ : syracuseStep 630335 = 945503) B945503
theorem B3514751 : Blo 143792 3514751 := bstep (se 1 (by rfl) ⟨2636063, by rfl⟩ : syracuseStep 3514751 = 5272127) B5272127
theorem B1385039 : Blo 143792 1385039 := bstep (se 1 (by rfl) ⟨1038779, by rfl⟩ : syracuseStep 1385039 = 2077559) B2077559
theorem B2106971 : Blo 143792 2106971 := bstep (se 1 (by rfl) ⟨1580228, by rfl⟩ : syracuseStep 2106971 = 3160457) B3160457
theorem B501499 : Blo 143792 501499 := bstep (se 1 (by rfl) ⟨376124, by rfl⟩ : syracuseStep 501499 = 752249) B752249
theorem B207031 : Blo 143792 207031 := bstep (se 1 (by rfl) ⟨155273, by rfl⟩ : syracuseStep 207031 = 310547) B310547
theorem B1256431 : Blo 143792 1256431 := bstep (se 1 (by rfl) ⟨942323, by rfl⟩ : syracuseStep 1256431 = 1884647) B1884647
theorem B1159039 : Blo 143792 1159039 := bstep (se 1 (by rfl) ⟨869279, by rfl⟩ : syracuseStep 1159039 = 1738559) B1738559
theorem B733535 : Blo 143792 733535 := bstep (se 1 (by rfl) ⟨550151, by rfl⟩ : syracuseStep 733535 = 1100303) B1100303
theorem B1093985 : Blo 143792 1093985 := bstep (se 2 (by rfl) ⟨410244, by rfl⟩ : syracuseStep 1093985 = 820489) B820489
theorem B143807 : Blo 143792 143807 := bstep (se 1 (by rfl) ⟨107855, by rfl⟩ : syracuseStep 143807 = 215711) B215711
theorem B2798063 : Blo 143792 2798063 := bstep (se 1 (by rfl) ⟨2098547, by rfl⟩ : syracuseStep 2798063 = 4197095) B4197095
theorem B144319 : Blo 143792 144319 := bstep (se 1 (by rfl) ⟨108239, by rfl⟩ : syracuseStep 144319 = 216479) B216479
theorem B144415 : Blo 143792 144415 := bstep (se 1 (by rfl) ⟨108311, by rfl⟩ : syracuseStep 144415 = 216623) B216623
theorem B832679 : Blo 143792 832679 := bstep (se 1 (by rfl) ⟨624509, by rfl⟩ : syracuseStep 832679 = 1249019) B1249019
theorem B144623 : Blo 143792 144623 := bstep (se 1 (by rfl) ⟨108467, by rfl⟩ : syracuseStep 144623 = 216935) B216935
theorem B439577 : Blo 143792 439577 := bstep (se 2 (by rfl) ⟨164841, by rfl⟩ : syracuseStep 439577 = 329683) B329683
theorem B144667 : Blo 143792 144667 := bstep (se 1 (by rfl) ⟨108500, by rfl⟩ : syracuseStep 144667 = 217001) B217001
theorem B243047 : Blo 143792 243047 := bstep (se 1 (by rfl) ⟨182285, by rfl⟩ : syracuseStep 243047 = 364571) B364571
theorem B145263 : Blo 143792 145263 := bstep (se 1 (by rfl) ⟨108947, by rfl⟩ : syracuseStep 145263 = 217895) B217895
theorem B145439 : Blo 143792 145439 := bstep (se 1 (by rfl) ⟨109079, by rfl⟩ : syracuseStep 145439 = 218159) B218159
theorem B309359 : Blo 143792 309359 := bstep (se 1 (by rfl) ⟨232019, by rfl⟩ : syracuseStep 309359 = 464039) B464039
theorem B4733147 : Blo 143792 4733147 := bstep (se 1 (by rfl) ⟨3549860, by rfl⟩ : syracuseStep 4733147 = 7099721) B7099721
theorem B145735 : Blo 143792 145735 := bstep (se 1 (by rfl) ⟨109301, by rfl⟩ : syracuseStep 145735 = 218603) B218603
theorem B146023 : Blo 143792 146023 := bstep (se 1 (by rfl) ⟨109517, by rfl⟩ : syracuseStep 146023 = 219035) B219035
theorem B146031 : Blo 143792 146031 := bstep (se 1 (by rfl) ⟨109523, by rfl⟩ : syracuseStep 146031 = 219047) B219047
theorem B146127 : Blo 143792 146127 := bstep (se 1 (by rfl) ⟨109595, by rfl⟩ : syracuseStep 146127 = 219191) B219191
theorem B146159 : Blo 143792 146159 := bstep (se 1 (by rfl) ⟨109619, by rfl⟩ : syracuseStep 146159 = 219239) B219239
theorem B146399 : Blo 143792 146399 := bstep (se 1 (by rfl) ⟨109799, by rfl⟩ : syracuseStep 146399 = 219599) B219599
theorem B146599 : Blo 143792 146599 := bstep (se 1 (by rfl) ⟨109949, by rfl⟩ : syracuseStep 146599 = 219899) B219899
theorem B146683 : Blo 143792 146683 := bstep (se 1 (by rfl) ⟨110012, by rfl⟩ : syracuseStep 146683 = 220025) B220025
theorem B245801 : Blo 143792 245801 := bstep (se 2 (by rfl) ⟨92175, by rfl⟩ : syracuseStep 245801 = 184351) B184351
theorem B147615 : Blo 143792 147615 := bstep (se 1 (by rfl) ⟨110711, by rfl⟩ : syracuseStep 147615 = 221423) B221423
theorem B147623 : Blo 143792 147623 := bstep (se 1 (by rfl) ⟨110717, by rfl⟩ : syracuseStep 147623 = 221435) B221435
theorem B147783 : Blo 143792 147783 := bstep (se 1 (by rfl) ⟨110837, by rfl⟩ : syracuseStep 147783 = 221675) B221675
theorem B737747 : Blo 143792 737747 := bstep (se 1 (by rfl) ⟨553310, by rfl⟩ : syracuseStep 737747 = 1106621) B1106621
theorem B3752891 : Blo 143792 3752891 := bstep (se 1 (by rfl) ⟨2814668, by rfl⟩ : syracuseStep 3752891 = 5629337) B5629337
theorem B247711 : Blo 143792 247711 := bstep (se 1 (by rfl) ⟨185783, by rfl⟩ : syracuseStep 247711 = 371567) B371567
theorem B215879 : Blo 143792 215879 := bstep (se 1 (by rfl) ⟨161909, by rfl⟩ : syracuseStep 215879 = 323819) B323819
theorem B216299 : Blo 143792 216299 := bstep (se 1 (by rfl) ⟨162224, by rfl⟩ : syracuseStep 216299 = 324449) B324449
theorem B741473 : Blo 143792 741473 := bstep (se 2 (by rfl) ⟨278052, by rfl⟩ : syracuseStep 741473 = 556105) B556105
theorem B708743 : Blo 143792 708743 := bstep (se 1 (by rfl) ⟨531557, by rfl⟩ : syracuseStep 708743 = 1063115) B1063115
theorem B1757807 : Blo 143792 1757807 := bstep (se 1 (by rfl) ⟨1318355, by rfl⟩ : syracuseStep 1757807 = 2636711) B2636711
theorem B414335 : Blo 143792 414335 := bstep (se 1 (by rfl) ⟨310751, by rfl⟩ : syracuseStep 414335 = 621503) B621503
theorem B184999 : Blo 143792 184999 := bstep (se 1 (by rfl) ⟨138749, by rfl⟩ : syracuseStep 184999 = 277499) B277499
theorem B841427 : Blo 143792 841427 := bstep (se 1 (by rfl) ⟨631070, by rfl⟩ : syracuseStep 841427 = 1262141) B1262141
theorem B1038203 : Blo 143792 1038203 := bstep (se 1 (by rfl) ⟨778652, by rfl⟩ : syracuseStep 1038203 = 1557305) B1557305
theorem B1136875 : Blo 143792 1136875 := bstep (se 1 (by rfl) ⟨852656, by rfl⟩ : syracuseStep 1136875 = 1705313) B1705313
theorem B219455 : Blo 143792 219455 := bstep (se 1 (by rfl) ⟨164591, by rfl⟩ : syracuseStep 219455 = 329183) B329183
theorem B220031 : Blo 143792 220031 := bstep (se 1 (by rfl) ⟨165023, by rfl⟩ : syracuseStep 220031 = 330047) B330047
theorem B3726647 : Blo 143792 3726647 := bstep (se 1 (by rfl) ⟨2794985, by rfl⟩ : syracuseStep 3726647 = 5589971) B5589971
theorem B220775 : Blo 143792 220775 := bstep (se 1 (by rfl) ⟨165581, by rfl⟩ : syracuseStep 220775 = 331163) B331163
theorem B7855825 : Blo 143792 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B418537 : Blo 143792 418537 := bstep (se 2 (by rfl) ⟨156951, by rfl⟩ : syracuseStep 418537 = 313903) B313903
theorem B189167 : Blo 143792 189167 := bstep (se 1 (by rfl) ⟨141875, by rfl⟩ : syracuseStep 189167 = 283751) B283751
theorem B746495 : Blo 143792 746495 := bstep (se 1 (by rfl) ⟨559871, by rfl⟩ : syracuseStep 746495 = 1119743) B1119743
theorem B1041893 : Blo 143792 1041893 := bstep (se 4 (by rfl) ⟨97677, by rfl⟩ : syracuseStep 1041893 = 195355) B195355
theorem B1336895 : Blo 143792 1336895 := bstep (se 1 (by rfl) ⟨1002671, by rfl⟩ : syracuseStep 1336895 = 2005343) B2005343
theorem B2254715 : Blo 143792 2254715 := bstep (se 1 (by rfl) ⟨1691036, by rfl⟩ : syracuseStep 2254715 = 3382073) B3382073
theorem B485945 : Blo 143792 485945 := bstep (se 2 (by rfl) ⟨182229, by rfl⟩ : syracuseStep 485945 = 364459) B364459
theorem B323783 : Blo 143792 323783 := bstep (se 1 (by rfl) ⟨242837, by rfl⟩ : syracuseStep 323783 = 485675) B485675
theorem B487673 : Blo 143792 487673 := bstep (se 2 (by rfl) ⟨182877, by rfl⟩ : syracuseStep 487673 = 365755) B365755
theorem B323999 : Blo 143792 323999 := bstep (se 1 (by rfl) ⟨242999, by rfl⟩ : syracuseStep 323999 = 485999) B485999
theorem B389663 : Blo 143792 389663 := bstep (se 1 (by rfl) ⟨292247, by rfl⟩ : syracuseStep 389663 = 584495) B584495
theorem B324233 : Blo 143792 324233 := bstep (se 2 (by rfl) ⟨121587, by rfl⟩ : syracuseStep 324233 = 243175) B243175
theorem B1274687 : Blo 143792 1274687 := bstep (se 1 (by rfl) ⟨956015, by rfl⟩ : syracuseStep 1274687 = 1912031) B1912031
theorem B324575 : Blo 143792 324575 := bstep (se 1 (by rfl) ⟨243431, by rfl⟩ : syracuseStep 324575 = 486863) B486863
theorem B1571237 : Blo 143792 1571237 := bstep (se 4 (by rfl) ⟨147303, by rfl⟩ : syracuseStep 1571237 = 294607) B294607
theorem B293375 : Blo 143792 293375 := bstep (se 1 (by rfl) ⟨220031, by rfl⟩ : syracuseStep 293375 = 440063) B440063
theorem B2783915 : Blo 143792 2783915 := bstep (se 1 (by rfl) ⟨2087936, by rfl⟩ : syracuseStep 2783915 = 4175873) B4175873
theorem B1342271 : Blo 143792 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B1342295 : Blo 143792 1342295 := bstep (se 1 (by rfl) ⟨1006721, by rfl⟩ : syracuseStep 1342295 = 2013443) B2013443
theorem B30539177 : Blo 143792 30539177 := bstep (se 2 (by rfl) ⟨11452191, by rfl⟩ : syracuseStep 30539177 = 22904383) B22904383
theorem B1343135 : Blo 143792 1343135 := bstep (se 1 (by rfl) ⟨1007351, by rfl⟩ : syracuseStep 1343135 = 2014703) B2014703
theorem B163867 : Blo 143792 163867 := bstep (se 1 (by rfl) ⟨122900, by rfl⟩ : syracuseStep 163867 = 245801) B245801
theorem B327743 : Blo 143792 327743 := bstep (se 1 (by rfl) ⟨245807, by rfl⟩ : syracuseStep 327743 = 491615) B491615
theorem B491831 : Blo 143792 491831 := bstep (se 1 (by rfl) ⟨368873, by rfl⟩ : syracuseStep 491831 = 737747) B737747
theorem B1246043 : Blo 143792 1246043 := bstep (se 1 (by rfl) ⟨934532, by rfl⟩ : syracuseStep 1246043 = 1869065) B1869065
theorem B558049 : Blo 143792 558049 := bstep (se 2 (by rfl) ⟨209268, by rfl⟩ : syracuseStep 558049 = 418537) B418537
theorem B525359 : Blo 143792 525359 := bstep (se 1 (by rfl) ⟨394019, by rfl⟩ : syracuseStep 525359 = 788039) B788039
theorem B1049851 : Blo 143792 1049851 := bstep (se 1 (by rfl) ⟨787388, by rfl⟩ : syracuseStep 1049851 = 1574777) B1574777
theorem B198815 : Blo 143792 198815 := bstep (se 1 (by rfl) ⟨149111, by rfl⟩ : syracuseStep 198815 = 298223) B298223
theorem B329903 : Blo 143792 329903 := bstep (se 1 (by rfl) ⟨247427, by rfl⟩ : syracuseStep 329903 = 494855) B494855
theorem B330155 : Blo 143792 330155 := bstep (se 1 (by rfl) ⟨247616, by rfl⟩ : syracuseStep 330155 = 495233) B495233
theorem B330281 : Blo 143792 330281 := bstep (se 2 (by rfl) ⟨123855, by rfl⟩ : syracuseStep 330281 = 247711) B247711
theorem B494315 : Blo 143792 494315 := bstep (se 1 (by rfl) ⟨370736, by rfl⟩ : syracuseStep 494315 = 741473) B741473
theorem B1183031 : Blo 143792 1183031 := bstep (se 1 (by rfl) ⟨887273, by rfl⟩ : syracuseStep 1183031 = 1774547) B1774547
theorem B560951 : Blo 143792 560951 := bstep (se 1 (by rfl) ⟨420713, by rfl⟩ : syracuseStep 560951 = 841427) B841427
theorem B692135 : Blo 143792 692135 := bstep (se 1 (by rfl) ⟨519101, by rfl⟩ : syracuseStep 692135 = 1038203) B1038203
theorem B1675241 : Blo 143792 1675241 := bstep (se 2 (by rfl) ⟨628215, by rfl⟩ : syracuseStep 1675241 = 1256431) B1256431
theorem B921719 : Blo 143792 921719 := bstep (se 1 (by rfl) ⟨691289, by rfl⟩ : syracuseStep 921719 = 1382579) B1382579
theorem B594143 : Blo 143792 594143 := bstep (se 1 (by rfl) ⟨445607, by rfl⟩ : syracuseStep 594143 = 891215) B891215
theorem B463295 : Blo 143792 463295 := bstep (se 1 (by rfl) ⟨347471, by rfl⟩ : syracuseStep 463295 = 694943) B694943
theorem B923359 : Blo 143792 923359 := bstep (se 1 (by rfl) ⟨692519, by rfl⟩ : syracuseStep 923359 = 1385039) B1385039
theorem B497663 : Blo 143792 497663 := bstep (se 1 (by rfl) ⟨373247, by rfl⟩ : syracuseStep 497663 = 746495) B746495
theorem B694595 : Blo 143792 694595 := bstep (se 1 (by rfl) ⟨520946, by rfl⟩ : syracuseStep 694595 = 1041893) B1041893
theorem B891263 : Blo 143792 891263 := bstep (se 1 (by rfl) ⟨668447, by rfl⟩ : syracuseStep 891263 = 1336895) B1336895
theorem B3579389 : Blo 143792 3579389 := bstep (se 3 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 3579389 = 1342271) B1342271
theorem B729323 : Blo 143792 729323 := bstep (se 1 (by rfl) ⟨546992, by rfl⟩ : syracuseStep 729323 = 1093985) B1093985
theorem B1515833 : Blo 143792 1515833 := bstep (se 2 (by rfl) ⟨568437, by rfl⟩ : syracuseStep 1515833 = 1136875) B1136875
theorem B206239 : Blo 143792 206239 := bstep (se 1 (by rfl) ⟨154679, by rfl⟩ : syracuseStep 206239 = 309359) B309359
theorem B3155431 : Blo 143792 3155431 := bstep (se 1 (by rfl) ⟨2366573, by rfl⟩ : syracuseStep 3155431 = 4733147) B4733147
theorem B894863 : Blo 143792 894863 := bstep (se 1 (by rfl) ⟨671147, by rfl⟩ : syracuseStep 894863 = 1342295) B1342295
theorem B20359451 : Blo 143792 20359451 := bstep (se 1 (by rfl) ⟨15269588, by rfl⟩ : syracuseStep 20359451 = 30539177) B30539177
theorem B895423 : Blo 143792 895423 := bstep (se 1 (by rfl) ⟨671567, by rfl⟩ : syracuseStep 895423 = 1343135) B1343135
theorem B2501927 : Blo 143792 2501927 := bstep (se 1 (by rfl) ⟨1876445, by rfl⟩ : syracuseStep 2501927 = 3752891) B3752891
theorem B3059279 : Blo 143792 3059279 := bstep (se 1 (by rfl) ⟨2294459, by rfl⟩ : syracuseStep 3059279 = 4588919) B4588919
theorem B143919 : Blo 143792 143919 := bstep (se 1 (by rfl) ⟨107939, by rfl⟩ : syracuseStep 143919 = 215879) B215879
theorem B144199 : Blo 143792 144199 := bstep (se 1 (by rfl) ⟨108149, by rfl⟩ : syracuseStep 144199 = 216299) B216299
theorem B668665 : Blo 143792 668665 := bstep (se 2 (by rfl) ⟨250749, by rfl⟩ : syracuseStep 668665 = 501499) B501499
theorem B472495 : Blo 143792 472495 := bstep (se 1 (by rfl) ⟨354371, by rfl⟩ : syracuseStep 472495 = 708743) B708743
theorem B276041 : Blo 143792 276041 := bstep (se 2 (by rfl) ⟨103515, by rfl⟩ : syracuseStep 276041 = 207031) B207031
theorem B276223 : Blo 143792 276223 := bstep (se 1 (by rfl) ⟨207167, by rfl⟩ : syracuseStep 276223 = 414335) B414335
theorem B146303 : Blo 143792 146303 := bstep (se 1 (by rfl) ⟨109727, by rfl⟩ : syracuseStep 146303 = 219455) B219455
theorem B244903 : Blo 143792 244903 := bstep (se 1 (by rfl) ⟨183677, by rfl⟩ : syracuseStep 244903 = 367355) B367355
theorem B146687 : Blo 143792 146687 := bstep (se 1 (by rfl) ⟨110015, by rfl⟩ : syracuseStep 146687 = 220031) B220031
theorem B245119 : Blo 143792 245119 := bstep (se 1 (by rfl) ⟨183839, by rfl⟩ : syracuseStep 245119 = 367679) B367679
theorem B147183 : Blo 143792 147183 := bstep (se 1 (by rfl) ⟨110387, by rfl⟩ : syracuseStep 147183 = 220775) B220775
theorem B2343167 : Blo 143792 2343167 := bstep (se 1 (by rfl) ⟨1757375, by rfl⟩ : syracuseStep 2343167 = 3514751) B3514751
theorem B246665 : Blo 143792 246665 := bstep (se 2 (by rfl) ⟨92499, by rfl⟩ : syracuseStep 246665 = 184999) B184999
theorem B2017781 : Blo 143792 2017781 := bstep (se 5 (by rfl) ⟨94583, by rfl⟩ : syracuseStep 2017781 = 189167) B189167
theorem B215855 : Blo 143792 215855 := bstep (se 1 (by rfl) ⟨161891, by rfl⟩ : syracuseStep 215855 = 323783) B323783
theorem B215999 : Blo 143792 215999 := bstep (se 1 (by rfl) ⟨161999, by rfl⟩ : syracuseStep 215999 = 323999) B323999
theorem B216155 : Blo 143792 216155 := bstep (se 1 (by rfl) ⟨162116, by rfl⟩ : syracuseStep 216155 = 324233) B324233
theorem B216383 : Blo 143792 216383 := bstep (se 1 (by rfl) ⟨162287, by rfl⟩ : syracuseStep 216383 = 324575) B324575
theorem B1855943 : Blo 143792 1855943 := bstep (se 1 (by rfl) ⟨1391957, by rfl⟩ : syracuseStep 1855943 = 2783915) B2783915
theorem B6181541 : Blo 143792 6181541 := bstep (se 4 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 6181541 = 1159039) B1159039
theorem B10474433 : Blo 143792 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B218537 : Blo 143792 218537 := bstep (se 2 (by rfl) ⟨81951, by rfl⟩ : syracuseStep 218537 = 163903) B163903
theorem B1332791 : Blo 143792 1332791 := bstep (se 1 (by rfl) ⟨999593, by rfl⟩ : syracuseStep 1332791 = 1999187) B1999187
theorem B218855 : Blo 143792 218855 := bstep (se 1 (by rfl) ⟨164141, by rfl⟩ : syracuseStep 218855 = 328283) B328283
theorem B219113 : Blo 143792 219113 := bstep (se 2 (by rfl) ⟨82167, by rfl⟩ : syracuseStep 219113 = 164335) B164335
theorem B219311 : Blo 143792 219311 := bstep (se 1 (by rfl) ⟨164483, by rfl⟩ : syracuseStep 219311 = 328967) B328967
theorem B219641 : Blo 143792 219641 := bstep (se 2 (by rfl) ⟨82365, by rfl⟩ : syracuseStep 219641 = 164731) B164731
theorem B219689 : Blo 143792 219689 := bstep (se 2 (by rfl) ⟨82383, by rfl⟩ : syracuseStep 219689 = 164767) B164767
theorem B547631 : Blo 143792 547631 := bstep (se 1 (by rfl) ⟨410723, by rfl⟩ : syracuseStep 547631 = 821447) B821447
theorem B220127 : Blo 143792 220127 := bstep (se 1 (by rfl) ⟨165095, by rfl⟩ : syracuseStep 220127 = 330191) B330191
theorem B220937 : Blo 143792 220937 := bstep (se 2 (by rfl) ⟨82851, by rfl⟩ : syracuseStep 220937 = 165703) B165703
theorem B221417 : Blo 143792 221417 := bstep (se 2 (by rfl) ⟨83031, by rfl⟩ : syracuseStep 221417 = 166063) B166063
theorem B1171871 : Blo 143792 1171871 := bstep (se 1 (by rfl) ⟨878903, by rfl⟩ : syracuseStep 1171871 = 1757807) B1757807
theorem B221663 : Blo 143792 221663 := bstep (se 1 (by rfl) ⟨166247, by rfl⟩ : syracuseStep 221663 = 332495) B332495
theorem B1663577 : Blo 143792 1663577 := bstep (se 2 (by rfl) ⟨623841, by rfl⟩ : syracuseStep 1663577 = 1247683) B1247683
theorem B746171 : Blo 143792 746171 := bstep (se 1 (by rfl) ⟨559628, by rfl⟩ : syracuseStep 746171 = 1119257) B1119257
theorem B2484431 : Blo 143792 2484431 := bstep (se 1 (by rfl) ⟨1863323, by rfl⟩ : syracuseStep 2484431 = 3726647) B3726647
theorem B551231 : Blo 143792 551231 := bstep (se 1 (by rfl) ⟨413423, by rfl⟩ : syracuseStep 551231 = 826847) B826847
theorem B420167 : Blo 143792 420167 := bstep (se 1 (by rfl) ⟨315125, by rfl⟩ : syracuseStep 420167 = 630251) B630251
theorem B420223 : Blo 143792 420223 := bstep (se 1 (by rfl) ⟨315167, by rfl⟩ : syracuseStep 420223 = 630335) B630335
theorem B1404647 : Blo 143792 1404647 := bstep (se 1 (by rfl) ⟨1053485, by rfl⟩ : syracuseStep 1404647 = 2106971) B2106971
theorem B1503143 : Blo 143792 1503143 := bstep (se 1 (by rfl) ⟨1127357, by rfl⟩ : syracuseStep 1503143 = 2254715) B2254715
theorem B323963 : Blo 143792 323963 := bstep (se 1 (by rfl) ⟨242972, by rfl⟩ : syracuseStep 323963 = 485945) B485945
theorem B325115 : Blo 143792 325115 := bstep (se 1 (by rfl) ⟨243836, by rfl⟩ : syracuseStep 325115 = 487673) B487673
theorem B489023 : Blo 143792 489023 := bstep (se 1 (by rfl) ⟨366767, by rfl⟩ : syracuseStep 489023 = 733535) B733535
theorem B1865375 : Blo 143792 1865375 := bstep (se 1 (by rfl) ⟨1399031, by rfl⟩ : syracuseStep 1865375 = 2798063) B2798063
theorem B259775 : Blo 143792 259775 := bstep (se 1 (by rfl) ⟨194831, by rfl⟩ : syracuseStep 259775 = 389663) B389663
theorem B849791 : Blo 143792 849791 := bstep (se 1 (by rfl) ⟨637343, by rfl⟩ : syracuseStep 849791 = 1274687) B1274687
theorem B555119 : Blo 143792 555119 := bstep (se 1 (by rfl) ⟨416339, by rfl⟩ : syracuseStep 555119 = 832679) B832679
theorem B293051 : Blo 143792 293051 := bstep (se 1 (by rfl) ⟨219788, by rfl⟩ : syracuseStep 293051 = 439577) B439577
theorem B162031 : Blo 143792 162031 := bstep (se 1 (by rfl) ⟨121523, by rfl⟩ : syracuseStep 162031 = 243047) B243047
theorem B1047491 : Blo 143792 1047491 := bstep (se 1 (by rfl) ⟨785618, by rfl⟩ : syracuseStep 1047491 = 1571237) B1571237
theorem B195583 : Blo 143792 195583 := bstep (se 1 (by rfl) ⟨146687, by rfl⟩ : syracuseStep 195583 = 293375) B293375
theorem B327887 : Blo 143792 327887 := bstep (se 1 (by rfl) ⟨245915, by rfl⟩ : syracuseStep 327887 = 491831) B491831
theorem B164443 : Blo 143792 164443 := bstep (se 1 (by rfl) ⟨123332, by rfl⟩ : syracuseStep 164443 = 246665) B246665
theorem B1345187 : Blo 143792 1345187 := bstep (se 1 (by rfl) ⟨1008890, by rfl⟩ : syracuseStep 1345187 = 2017781) B2017781
theorem B329543 : Blo 143792 329543 := bstep (se 1 (by rfl) ⟨247157, by rfl⟩ : syracuseStep 329543 = 494315) B494315
theorem B788687 : Blo 143792 788687 := bstep (se 1 (by rfl) ⟨591515, by rfl⟩ : syracuseStep 788687 = 1183031) B1183031
theorem B461423 : Blo 143792 461423 := bstep (se 1 (by rfl) ⟨346067, by rfl⟩ : syracuseStep 461423 = 692135) B692135
theorem B1116827 : Blo 143792 1116827 := bstep (se 1 (by rfl) ⟨837620, by rfl⟩ : syracuseStep 1116827 = 1675241) B1675241
theorem B396095 : Blo 143792 396095 := bstep (se 1 (by rfl) ⟨297071, by rfl⟩ : syracuseStep 396095 = 594143) B594143
theorem B560297 : Blo 143792 560297 := bstep (se 2 (by rfl) ⟨210111, by rfl⟩ : syracuseStep 560297 = 420223) B420223
theorem B6982955 : Blo 143792 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B888527 : Blo 143792 888527 := bstep (se 1 (by rfl) ⟨666395, by rfl⟩ : syracuseStep 888527 = 1332791) B1332791
theorem B331775 : Blo 143792 331775 := bstep (se 1 (by rfl) ⟨248831, by rfl⟩ : syracuseStep 331775 = 497663) B497663
theorem B365087 : Blo 143792 365087 := bstep (se 1 (by rfl) ⟨273815, by rfl⟩ : syracuseStep 365087 = 547631) B547631
theorem B530173 : Blo 143792 530173 := bstep (se 3 (by rfl) ⟨99407, by rfl⟩ : syracuseStep 530173 = 198815) B198815
theorem B497447 : Blo 143792 497447 := bstep (se 1 (by rfl) ⟨373085, by rfl⟩ : syracuseStep 497447 = 746171) B746171
theorem B596575 : Blo 143792 596575 := bstep (se 1 (by rfl) ⟨447431, by rfl⟩ : syracuseStep 596575 = 894863) B894863
theorem B13572967 : Blo 143792 13572967 := bstep (se 1 (by rfl) ⟨10179725, by rfl⟩ : syracuseStep 13572967 = 20359451) B20359451
theorem B367487 : Blo 143792 367487 := bstep (se 1 (by rfl) ⟨275615, by rfl⟩ : syracuseStep 367487 = 551231) B551231
theorem B629993 : Blo 143792 629993 := bstep (se 2 (by rfl) ⟨236247, by rfl⟩ : syracuseStep 629993 = 472495) B472495
theorem B368297 : Blo 143792 368297 := bstep (se 2 (by rfl) ⟨138111, by rfl⟩ : syracuseStep 368297 = 276223) B276223
theorem B2039519 : Blo 143792 2039519 := bstep (se 1 (by rfl) ⟨1529639, by rfl⟩ : syracuseStep 2039519 = 3059279) B3059279
theorem B173183 : Blo 143792 173183 := bstep (se 1 (by rfl) ⟨129887, by rfl⟩ : syracuseStep 173183 = 259775) B259775
theorem B566527 : Blo 143792 566527 := bstep (se 1 (by rfl) ⟨424895, by rfl⟩ : syracuseStep 566527 = 849791) B849791
theorem B370079 : Blo 143792 370079 := bstep (se 1 (by rfl) ⟨277559, by rfl⟩ : syracuseStep 370079 = 555119) B555119
theorem B698327 : Blo 143792 698327 := bstep (se 1 (by rfl) ⟨523745, by rfl⟩ : syracuseStep 698327 = 1047491) B1047491
theorem B830695 : Blo 143792 830695 := bstep (se 1 (by rfl) ⟨623021, by rfl⟩ : syracuseStep 830695 = 1246043) B1246043
theorem B143903 : Blo 143792 143903 := bstep (se 1 (by rfl) ⟨107927, by rfl⟩ : syracuseStep 143903 = 215855) B215855
theorem B274985 : Blo 143792 274985 := bstep (se 2 (by rfl) ⟨103119, by rfl⟩ : syracuseStep 274985 = 206239) B206239
theorem B143999 : Blo 143792 143999 := bstep (se 1 (by rfl) ⟨107999, by rfl⟩ : syracuseStep 143999 = 215999) B215999
theorem B4207241 : Blo 143792 4207241 := bstep (se 2 (by rfl) ⟨1577715, by rfl⟩ : syracuseStep 4207241 = 3155431) B3155431
theorem B144103 : Blo 143792 144103 := bstep (se 1 (by rfl) ⟨108077, by rfl⟩ : syracuseStep 144103 = 216155) B216155
theorem B144255 : Blo 143792 144255 := bstep (se 1 (by rfl) ⟨108191, by rfl⟩ : syracuseStep 144255 = 216383) B216383
theorem B373967 : Blo 143792 373967 := bstep (se 1 (by rfl) ⟨280475, by rfl⟩ : syracuseStep 373967 = 560951) B560951
theorem B308863 : Blo 143792 308863 := bstep (se 1 (by rfl) ⟨231647, by rfl⟩ : syracuseStep 308863 = 463295) B463295
theorem B1193897 : Blo 143792 1193897 := bstep (se 2 (by rfl) ⟨447711, by rfl⟩ : syracuseStep 1193897 = 895423) B895423
theorem B145691 : Blo 143792 145691 := bstep (se 1 (by rfl) ⟨109268, by rfl⟩ : syracuseStep 145691 = 218537) B218537
theorem B145903 : Blo 143792 145903 := bstep (se 1 (by rfl) ⟨109427, by rfl⟩ : syracuseStep 145903 = 218855) B218855
theorem B146075 : Blo 143792 146075 := bstep (se 1 (by rfl) ⟨109556, by rfl⟩ : syracuseStep 146075 = 219113) B219113
theorem B146207 : Blo 143792 146207 := bstep (se 1 (by rfl) ⟨109655, by rfl⟩ : syracuseStep 146207 = 219311) B219311
theorem B146427 : Blo 143792 146427 := bstep (se 1 (by rfl) ⟨109820, by rfl⟩ : syracuseStep 146427 = 219641) B219641
theorem B146459 : Blo 143792 146459 := bstep (se 1 (by rfl) ⟨109844, by rfl⟩ : syracuseStep 146459 = 219689) B219689
theorem B146751 : Blo 143792 146751 := bstep (se 1 (by rfl) ⟨110063, by rfl⟩ : syracuseStep 146751 = 220127) B220127
theorem B147291 : Blo 143792 147291 := bstep (se 1 (by rfl) ⟨110468, by rfl⟩ : syracuseStep 147291 = 220937) B220937
theorem B147611 : Blo 143792 147611 := bstep (se 1 (by rfl) ⟨110708, by rfl⟩ : syracuseStep 147611 = 221417) B221417
theorem B147775 : Blo 143792 147775 := bstep (se 1 (by rfl) ⟨110831, by rfl⟩ : syracuseStep 147775 = 221663) B221663
theorem B1852253 : Blo 143792 1852253 := bstep (se 3 (by rfl) ⟨347297, by rfl⟩ : syracuseStep 1852253 = 694595) B694595
theorem B2376701 : Blo 143792 2376701 := bstep (se 3 (by rfl) ⟨445631, by rfl⟩ : syracuseStep 2376701 = 891263) B891263
theorem B1656287 : Blo 143792 1656287 := bstep (se 1 (by rfl) ⟨1242215, by rfl⟩ : syracuseStep 1656287 = 2484431) B2484431
theorem B280111 : Blo 143792 280111 := bstep (se 1 (by rfl) ⟨210083, by rfl⟩ : syracuseStep 280111 = 420167) B420167
theorem B1231145 : Blo 143792 1231145 := bstep (se 2 (by rfl) ⟨461679, by rfl⟩ : syracuseStep 1231145 = 923359) B923359
theorem B936431 : Blo 143792 936431 := bstep (se 1 (by rfl) ⟨702323, by rfl⟩ : syracuseStep 936431 = 1404647) B1404647
theorem B1002095 : Blo 143792 1002095 := bstep (se 1 (by rfl) ⟨751571, by rfl⟩ : syracuseStep 1002095 = 1503143) B1503143
theorem B215975 : Blo 143792 215975 := bstep (se 1 (by rfl) ⟨161981, by rfl⟩ : syracuseStep 215975 = 323963) B323963
theorem B216041 : Blo 143792 216041 := bstep (se 2 (by rfl) ⟨81015, by rfl⟩ : syracuseStep 216041 = 162031) B162031
theorem B216743 : Blo 143792 216743 := bstep (se 1 (by rfl) ⟨162557, by rfl⟩ : syracuseStep 216743 = 325115) B325115
theorem B184027 : Blo 143792 184027 := bstep (se 1 (by rfl) ⟨138020, by rfl⟩ : syracuseStep 184027 = 276041) B276041
theorem B218489 : Blo 143792 218489 := bstep (se 2 (by rfl) ⟨81933, by rfl⟩ : syracuseStep 218489 = 163867) B163867
theorem B218495 : Blo 143792 218495 := bstep (se 1 (by rfl) ⟨163871, by rfl⟩ : syracuseStep 218495 = 327743) B327743
theorem B1562111 : Blo 143792 1562111 := bstep (se 1 (by rfl) ⟨1171583, by rfl⟩ : syracuseStep 1562111 = 2343167) B2343167
theorem B350239 : Blo 143792 350239 := bstep (se 1 (by rfl) ⟨262679, by rfl⟩ : syracuseStep 350239 = 525359) B525359
theorem B744065 : Blo 143792 744065 := bstep (se 2 (by rfl) ⟨279024, by rfl⟩ : syracuseStep 744065 = 558049) B558049
theorem B219935 : Blo 143792 219935 := bstep (se 1 (by rfl) ⟨164951, by rfl⟩ : syracuseStep 219935 = 329903) B329903
theorem B220103 : Blo 143792 220103 := bstep (se 1 (by rfl) ⟨165077, by rfl⟩ : syracuseStep 220103 = 330155) B330155
theorem B1399801 : Blo 143792 1399801 := bstep (se 2 (by rfl) ⟨524925, by rfl⟩ : syracuseStep 1399801 = 1049851) B1049851
theorem B220187 : Blo 143792 220187 := bstep (se 1 (by rfl) ⟨165140, by rfl⟩ : syracuseStep 220187 = 330281) B330281
theorem B614479 : Blo 143792 614479 := bstep (se 1 (by rfl) ⟨460859, by rfl⟩ : syracuseStep 614479 = 921719) B921719
theorem B1237295 : Blo 143792 1237295 := bstep (se 1 (by rfl) ⟨927971, by rfl⟩ : syracuseStep 1237295 = 1855943) B1855943
theorem B4121027 : Blo 143792 4121027 := bstep (se 1 (by rfl) ⟨3090770, by rfl⟩ : syracuseStep 4121027 = 6181541) B6181541
theorem B2386259 : Blo 143792 2386259 := bstep (se 1 (by rfl) ⟨1789694, by rfl⟩ : syracuseStep 2386259 = 3579389) B3579389
theorem B3566213 : Blo 143792 3566213 := bstep (se 4 (by rfl) ⟨334332, by rfl⟩ : syracuseStep 3566213 = 668665) B668665
theorem B486215 : Blo 143792 486215 := bstep (se 1 (by rfl) ⟨364661, by rfl⟩ : syracuseStep 486215 = 729323) B729323
theorem B1010555 : Blo 143792 1010555 := bstep (se 1 (by rfl) ⟨757916, by rfl⟩ : syracuseStep 1010555 = 1515833) B1515833
theorem B781247 : Blo 143792 781247 := bstep (se 1 (by rfl) ⟨585935, by rfl⟩ : syracuseStep 781247 = 1171871) B1171871
theorem B1109051 : Blo 143792 1109051 := bstep (se 1 (by rfl) ⟨831788, by rfl⟩ : syracuseStep 1109051 = 1663577) B1663577
theorem B1667951 : Blo 143792 1667951 := bstep (se 1 (by rfl) ⟨1250963, by rfl⟩ : syracuseStep 1667951 = 2501927) B2501927
theorem B326015 : Blo 143792 326015 := bstep (se 1 (by rfl) ⟨244511, by rfl⟩ : syracuseStep 326015 = 489023) B489023
theorem B1243583 : Blo 143792 1243583 := bstep (se 1 (by rfl) ⟨932687, by rfl⟩ : syracuseStep 1243583 = 1865375) B1865375
theorem B260777 : Blo 143792 260777 := bstep (se 2 (by rfl) ⟨97791, by rfl⟩ : syracuseStep 260777 = 195583) B195583
theorem B195367 : Blo 143792 195367 := bstep (se 1 (by rfl) ⟨146525, by rfl⟩ : syracuseStep 195367 = 293051) B293051
theorem B326537 : Blo 143792 326537 := bstep (se 2 (by rfl) ⟨122451, by rfl⟩ : syracuseStep 326537 = 244903) B244903
theorem B326825 : Blo 143792 326825 := bstep (se 2 (by rfl) ⟨122559, by rfl⟩ : syracuseStep 326825 = 245119) B245119
theorem B819305 : Blo 143792 819305 := bstep (se 2 (by rfl) ⟨307239, by rfl⟩ : syracuseStep 819305 = 614479) B614479
theorem B525791 : Blo 143792 525791 := bstep (se 1 (by rfl) ⟨394343, by rfl⟩ : syracuseStep 525791 = 788687) B788687
theorem B820763 : Blo 143792 820763 := bstep (se 1 (by rfl) ⟨615572, by rfl⟩ : syracuseStep 820763 = 1231145) B1231145
theorem B624287 : Blo 143792 624287 := bstep (se 1 (by rfl) ⟨468215, by rfl⟩ : syracuseStep 624287 = 936431) B936431
theorem B755369 : Blo 143792 755369 := bstep (se 2 (by rfl) ⟨283263, by rfl⟩ : syracuseStep 755369 = 566527) B566527
theorem B4655303 : Blo 143792 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B592351 : Blo 143792 592351 := bstep (se 1 (by rfl) ⟨444263, by rfl⟩ : syracuseStep 592351 = 888527) B888527
theorem B331631 : Blo 143792 331631 := bstep (se 1 (by rfl) ⟨248723, by rfl⟩ : syracuseStep 331631 = 497447) B497447
theorem B496043 : Blo 143792 496043 := bstep (se 1 (by rfl) ⟨372032, by rfl⟩ : syracuseStep 496043 = 744065) B744065
theorem B3183725 : Blo 143792 3183725 := bstep (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) B1193897
theorem B824863 : Blo 143792 824863 := bstep (se 1 (by rfl) ⟨618647, by rfl⟩ : syracuseStep 824863 = 1237295) B1237295
theorem B465551 : Blo 143792 465551 := bstep (se 1 (by rfl) ⟨349163, by rfl⟩ : syracuseStep 465551 = 698327) B698327
theorem B695405 : Blo 143792 695405 := bstep (se 3 (by rfl) ⟨130388, by rfl⟩ : syracuseStep 695405 = 260777) B260777
theorem B1056253 : Blo 143792 1056253 := bstep (se 3 (by rfl) ⟨198047, by rfl⟩ : syracuseStep 1056253 = 396095) B396095
theorem B466985 : Blo 143792 466985 := bstep (se 2 (by rfl) ⟨175119, by rfl⟩ : syracuseStep 466985 = 350239) B350239
theorem B795433 : Blo 143792 795433 := bstep (se 2 (by rfl) ⟨298287, by rfl⟩ : syracuseStep 795433 = 596575) B596575
theorem B18097289 : Blo 143792 18097289 := bstep (se 2 (by rfl) ⟨6786483, by rfl⟩ : syracuseStep 18097289 = 13572967) B13572967
theorem B829055 : Blo 143792 829055 := bstep (se 1 (by rfl) ⟨621791, by rfl⟩ : syracuseStep 829055 = 1243583) B1243583
theorem B1584467 : Blo 143792 1584467 := bstep (se 1 (by rfl) ⟨1188350, by rfl⟩ : syracuseStep 1584467 = 2376701) B2376701
theorem B896791 : Blo 143792 896791 := bstep (se 1 (by rfl) ⟨672593, by rfl⟩ : syracuseStep 896791 = 1345187) B1345187
theorem B1847285 : Blo 143792 1847285 := bstep (se 5 (by rfl) ⟨86591, by rfl⟩ : syracuseStep 1847285 = 173183) B173183
theorem B668063 : Blo 143792 668063 := bstep (se 1 (by rfl) ⟨501047, by rfl⟩ : syracuseStep 668063 = 1002095) B1002095
theorem B143983 : Blo 143792 143983 := bstep (se 1 (by rfl) ⟨107987, by rfl⟩ : syracuseStep 143983 = 215975) B215975
theorem B144027 : Blo 143792 144027 := bstep (se 1 (by rfl) ⟨108020, by rfl⟩ : syracuseStep 144027 = 216041) B216041
theorem B373481 : Blo 143792 373481 := bstep (se 2 (by rfl) ⟨140055, by rfl⟩ : syracuseStep 373481 = 280111) B280111
theorem B373531 : Blo 143792 373531 := bstep (se 1 (by rfl) ⟨280148, by rfl⟩ : syracuseStep 373531 = 560297) B560297
theorem B144495 : Blo 143792 144495 := bstep (se 1 (by rfl) ⟨108371, by rfl⟩ : syracuseStep 144495 = 216743) B216743
theorem B243391 : Blo 143792 243391 := bstep (se 1 (by rfl) ⟨182543, by rfl⟩ : syracuseStep 243391 = 365087) B365087
theorem B145659 : Blo 143792 145659 := bstep (se 1 (by rfl) ⟨109244, by rfl⟩ : syracuseStep 145659 = 218489) B218489
theorem B145663 : Blo 143792 145663 := bstep (se 1 (by rfl) ⟨109247, by rfl⟩ : syracuseStep 145663 = 218495) B218495
theorem B146623 : Blo 143792 146623 := bstep (se 1 (by rfl) ⟨109967, by rfl⟩ : syracuseStep 146623 = 219935) B219935
theorem B244991 : Blo 143792 244991 := bstep (se 1 (by rfl) ⟨183743, by rfl⟩ : syracuseStep 244991 = 367487) B367487
theorem B146735 : Blo 143792 146735 := bstep (se 1 (by rfl) ⟨110051, by rfl⟩ : syracuseStep 146735 = 220103) B220103
theorem B146791 : Blo 143792 146791 := bstep (se 1 (by rfl) ⟨110093, by rfl⟩ : syracuseStep 146791 = 220187) B220187
theorem B245369 : Blo 143792 245369 := bstep (se 2 (by rfl) ⟨92013, by rfl⟩ : syracuseStep 245369 = 184027) B184027
theorem B245531 : Blo 143792 245531 := bstep (se 1 (by rfl) ⟨184148, by rfl⟩ : syracuseStep 245531 = 368297) B368297
theorem B1359679 : Blo 143792 1359679 := bstep (se 1 (by rfl) ⟨1019759, by rfl⟩ : syracuseStep 1359679 = 2039519) B2039519
theorem B246719 : Blo 143792 246719 := bstep (se 1 (by rfl) ⟨185039, by rfl⟩ : syracuseStep 246719 = 370079) B370079
theorem B1590839 : Blo 143792 1590839 := bstep (se 1 (by rfl) ⟨1193129, by rfl⟩ : syracuseStep 1590839 = 2386259) B2386259
theorem B1230461 : Blo 143792 1230461 := bstep (se 3 (by rfl) ⟨230711, by rfl⟩ : syracuseStep 1230461 = 461423) B461423
theorem B2377475 : Blo 143792 2377475 := bstep (se 1 (by rfl) ⟨1783106, by rfl⟩ : syracuseStep 2377475 = 3566213) B3566213
theorem B673703 : Blo 143792 673703 := bstep (se 1 (by rfl) ⟨505277, by rfl⟩ : syracuseStep 673703 = 1010555) B1010555
theorem B739367 : Blo 143792 739367 := bstep (se 1 (by rfl) ⟨554525, by rfl⟩ : syracuseStep 739367 = 1109051) B1109051
theorem B411817 : Blo 143792 411817 := bstep (se 2 (by rfl) ⟨154431, by rfl⟩ : syracuseStep 411817 = 308863) B308863
theorem B706897 : Blo 143792 706897 := bstep (se 2 (by rfl) ⟨265086, by rfl⟩ : syracuseStep 706897 = 530173) B530173
theorem B183323 : Blo 143792 183323 := bstep (se 1 (by rfl) ⟨137492, by rfl⟩ : syracuseStep 183323 = 274985) B274985
theorem B2804827 : Blo 143792 2804827 := bstep (se 1 (by rfl) ⟨2103620, by rfl⟩ : syracuseStep 2804827 = 4207241) B4207241
theorem B249311 : Blo 143792 249311 := bstep (se 1 (by rfl) ⟨186983, by rfl⟩ : syracuseStep 249311 = 373967) B373967
theorem B217343 : Blo 143792 217343 := bstep (se 1 (by rfl) ⟨163007, by rfl⟩ : syracuseStep 217343 = 326015) B326015
theorem B217691 : Blo 143792 217691 := bstep (se 1 (by rfl) ⟨163268, by rfl⟩ : syracuseStep 217691 = 326537) B326537
theorem B217883 : Blo 143792 217883 := bstep (se 1 (by rfl) ⟨163412, by rfl⟩ : syracuseStep 217883 = 326825) B326825
theorem B218591 : Blo 143792 218591 := bstep (se 1 (by rfl) ⟨163943, by rfl⟩ : syracuseStep 218591 = 327887) B327887
theorem B1234835 : Blo 143792 1234835 := bstep (se 1 (by rfl) ⟨926126, by rfl⟩ : syracuseStep 1234835 = 1852253) B1852253
theorem B219257 : Blo 143792 219257 := bstep (se 2 (by rfl) ⟨82221, by rfl⟩ : syracuseStep 219257 = 164443) B164443
theorem B1104191 : Blo 143792 1104191 := bstep (se 1 (by rfl) ⟨828143, by rfl⟩ : syracuseStep 1104191 = 1656287) B1656287
theorem B219695 : Blo 143792 219695 := bstep (se 1 (by rfl) ⟨164771, by rfl⟩ : syracuseStep 219695 = 329543) B329543
theorem B744551 : Blo 143792 744551 := bstep (se 1 (by rfl) ⟨558413, by rfl⟩ : syracuseStep 744551 = 1116827) B1116827
theorem B221183 : Blo 143792 221183 := bstep (se 1 (by rfl) ⟨165887, by rfl⟩ : syracuseStep 221183 = 331775) B331775
theorem B1041407 : Blo 143792 1041407 := bstep (se 1 (by rfl) ⟨781055, by rfl⟩ : syracuseStep 1041407 = 1562111) B1562111
theorem B1107593 : Blo 143792 1107593 := bstep (se 2 (by rfl) ⟨415347, by rfl⟩ : syracuseStep 1107593 = 830695) B830695
theorem B419995 : Blo 143792 419995 := bstep (se 1 (by rfl) ⟨314996, by rfl⟩ : syracuseStep 419995 = 629993) B629993
theorem B2747351 : Blo 143792 2747351 := bstep (se 1 (by rfl) ⟨2060513, by rfl⟩ : syracuseStep 2747351 = 4121027) B4121027
theorem B324143 : Blo 143792 324143 := bstep (se 1 (by rfl) ⟨243107, by rfl⟩ : syracuseStep 324143 = 486215) B486215
theorem B520831 : Blo 143792 520831 := bstep (se 1 (by rfl) ⟨390623, by rfl⟩ : syracuseStep 520831 = 781247) B781247
theorem B1111967 : Blo 143792 1111967 := bstep (se 1 (by rfl) ⟨833975, by rfl⟩ : syracuseStep 1111967 = 1667951) B1667951
theorem B260489 : Blo 143792 260489 := bstep (se 2 (by rfl) ⟨97683, by rfl⟩ : syracuseStep 260489 = 195367) B195367
theorem B1866401 : Blo 143792 1866401 := bstep (se 2 (by rfl) ⟨699900, by rfl⟩ : syracuseStep 1866401 = 1399801) B1399801
theorem B1245293 : Blo 143792 1245293 := bstep (se 3 (by rfl) ⟨233492, by rfl⟩ : syracuseStep 1245293 = 466985) B466985
theorem B164479 : Blo 143792 164479 := bstep (se 1 (by rfl) ⟨123359, by rfl⟩ : syracuseStep 164479 = 246719) B246719
theorem B820307 : Blo 143792 820307 := bstep (se 1 (by rfl) ⟨615230, by rfl⟩ : syracuseStep 820307 = 1230461) B1230461
theorem B492911 : Blo 143792 492911 := bstep (se 1 (by rfl) ⟨369683, by rfl⟩ : syracuseStep 492911 = 739367) B739367
theorem B166207 : Blo 143792 166207 := bstep (se 1 (by rfl) ⟨124655, by rfl⟩ : syracuseStep 166207 = 249311) B249311
theorem B559993 : Blo 143792 559993 := bstep (se 2 (by rfl) ⟨209997, by rfl⟩ : syracuseStep 559993 = 419995) B419995
theorem B330695 : Blo 143792 330695 := bstep (se 1 (by rfl) ⟨248021, by rfl⟩ : syracuseStep 330695 = 496043) B496043
theorem B823223 : Blo 143792 823223 := bstep (se 1 (by rfl) ⟨617417, by rfl⟩ : syracuseStep 823223 = 1234835) B1234835
theorem B3739769 : Blo 143792 3739769 := bstep (se 2 (by rfl) ⟨1402413, by rfl⟩ : syracuseStep 3739769 = 2804827) B2804827
theorem B496367 : Blo 143792 496367 := bstep (se 1 (by rfl) ⟨372275, by rfl⟩ : syracuseStep 496367 = 744551) B744551
theorem B463603 : Blo 143792 463603 := bstep (se 1 (by rfl) ⟨347702, by rfl⟩ : syracuseStep 463603 = 695405) B695405
theorem B694271 : Blo 143792 694271 := bstep (se 1 (by rfl) ⟨520703, by rfl⟩ : syracuseStep 694271 = 1041407) B1041407
theorem B12064859 : Blo 143792 12064859 := bstep (se 1 (by rfl) ⟨9048644, by rfl⟩ : syracuseStep 12064859 = 18097289) B18097289
theorem B694441 : Blo 143792 694441 := bstep (se 2 (by rfl) ⟨260415, by rfl⟩ : syracuseStep 694441 = 520831) B520831
theorem B498041 : Blo 143792 498041 := bstep (se 2 (by rfl) ⟨186765, by rfl⟩ : syracuseStep 498041 = 373531) B373531
theorem B1056311 : Blo 143792 1056311 := bstep (se 1 (by rfl) ⟨792233, by rfl⟩ : syracuseStep 1056311 = 1584467) B1584467
theorem B173659 : Blo 143792 173659 := bstep (se 1 (by rfl) ⟨130244, by rfl⟩ : syracuseStep 173659 = 260489) B260489
theorem B1812905 : Blo 143792 1812905 := bstep (se 2 (by rfl) ⟨679839, by rfl⟩ : syracuseStep 1812905 = 1359679) B1359679
theorem B1060559 : Blo 143792 1060559 := bstep (se 1 (by rfl) ⟨795419, by rfl⟩ : syracuseStep 1060559 = 1590839) B1590839
theorem B1060577 : Blo 143792 1060577 := bstep (se 2 (by rfl) ⟨397716, by rfl⟩ : syracuseStep 1060577 = 795433) B795433
theorem B503579 : Blo 143792 503579 := bstep (se 1 (by rfl) ⟨377684, by rfl⟩ : syracuseStep 503579 = 755369) B755369
theorem B1584983 : Blo 143792 1584983 := bstep (se 1 (by rfl) ⟨1188737, by rfl⟩ : syracuseStep 1584983 = 2377475) B2377475
theorem B3159205 : Blo 143792 3159205 := bstep (se 4 (by rfl) ⟨296175, by rfl⟩ : syracuseStep 3159205 = 592351) B592351
theorem B144895 : Blo 143792 144895 := bstep (se 1 (by rfl) ⟨108671, by rfl⟩ : syracuseStep 144895 = 217343) B217343
theorem B145127 : Blo 143792 145127 := bstep (se 1 (by rfl) ⟨108845, by rfl⟩ : syracuseStep 145127 = 217691) B217691
theorem B145255 : Blo 143792 145255 := bstep (se 1 (by rfl) ⟨108941, by rfl⟩ : syracuseStep 145255 = 217883) B217883
theorem B145727 : Blo 143792 145727 := bstep (se 1 (by rfl) ⟨109295, by rfl⟩ : syracuseStep 145727 = 218591) B218591
theorem B146171 : Blo 143792 146171 := bstep (se 1 (by rfl) ⟨109628, by rfl⟩ : syracuseStep 146171 = 219257) B219257
theorem B736127 : Blo 143792 736127 := bstep (se 1 (by rfl) ⟨552095, by rfl⟩ : syracuseStep 736127 = 1104191) B1104191
theorem B146463 : Blo 143792 146463 := bstep (se 1 (by rfl) ⟨109847, by rfl⟩ : syracuseStep 146463 = 219695) B219695
theorem B310367 : Blo 143792 310367 := bstep (se 1 (by rfl) ⟨232775, by rfl⟩ : syracuseStep 310367 = 465551) B465551
theorem B1195721 : Blo 143792 1195721 := bstep (se 2 (by rfl) ⟨448395, by rfl⟩ : syracuseStep 1195721 = 896791) B896791
theorem B147455 : Blo 143792 147455 := bstep (se 1 (by rfl) ⟨110591, by rfl⟩ : syracuseStep 147455 = 221183) B221183
theorem B738395 : Blo 143792 738395 := bstep (se 1 (by rfl) ⟨553796, by rfl⟩ : syracuseStep 738395 = 1107593) B1107593
theorem B1099817 : Blo 143792 1099817 := bstep (se 2 (by rfl) ⟨412431, by rfl⟩ : syracuseStep 1099817 = 824863) B824863
theorem B1231523 : Blo 143792 1231523 := bstep (se 1 (by rfl) ⟨923642, by rfl⟩ : syracuseStep 1231523 = 1847285) B1847285
theorem B445375 : Blo 143792 445375 := bstep (se 1 (by rfl) ⟨334031, by rfl⟩ : syracuseStep 445375 = 668063) B668063
theorem B216095 : Blo 143792 216095 := bstep (se 1 (by rfl) ⟨162071, by rfl⟩ : syracuseStep 216095 = 324143) B324143
theorem B248987 : Blo 143792 248987 := bstep (se 1 (by rfl) ⟨186740, by rfl⟩ : syracuseStep 248987 = 373481) B373481
theorem B741311 : Blo 143792 741311 := bstep (se 1 (by rfl) ⟨555983, by rfl⟩ : syracuseStep 741311 = 1111967) B1111967
theorem B546203 : Blo 143792 546203 := bstep (se 1 (by rfl) ⟨409652, by rfl⟩ : syracuseStep 546203 = 819305) B819305
theorem B547175 : Blo 143792 547175 := bstep (se 1 (by rfl) ⟨410381, by rfl⟩ : syracuseStep 547175 = 820763) B820763
theorem B416191 : Blo 143792 416191 := bstep (se 1 (by rfl) ⟨312143, by rfl⟩ : syracuseStep 416191 = 624287) B624287
theorem B449135 : Blo 143792 449135 := bstep (se 1 (by rfl) ⟨336851, by rfl⟩ : syracuseStep 449135 = 673703) B673703
theorem B3103535 : Blo 143792 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B221087 : Blo 143792 221087 := bstep (se 1 (by rfl) ⟨165815, by rfl⟩ : syracuseStep 221087 = 331631) B331631
theorem B549089 : Blo 143792 549089 := bstep (se 2 (by rfl) ⟨205908, by rfl⟩ : syracuseStep 549089 = 411817) B411817
theorem B942529 : Blo 143792 942529 := bstep (se 2 (by rfl) ⟨353448, by rfl⟩ : syracuseStep 942529 = 706897) B706897
theorem B2122483 : Blo 143792 2122483 := bstep (se 1 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 2122483 = 3183725) B3183725
theorem B1402109 : Blo 143792 1402109 := bstep (se 3 (by rfl) ⟨262895, by rfl⟩ : syracuseStep 1402109 = 525791) B525791
theorem B552703 : Blo 143792 552703 := bstep (se 1 (by rfl) ⟨414527, by rfl⟩ : syracuseStep 552703 = 829055) B829055
theorem B1831567 : Blo 143792 1831567 := bstep (se 1 (by rfl) ⟨1373675, by rfl⟩ : syracuseStep 1831567 = 2747351) B2747351
theorem B324521 : Blo 143792 324521 := bstep (se 2 (by rfl) ⟨121695, by rfl⟩ : syracuseStep 324521 = 243391) B243391
theorem B488861 : Blo 143792 488861 := bstep (se 3 (by rfl) ⟨91661, by rfl⟩ : syracuseStep 488861 = 183323) B183323
theorem B1244267 : Blo 143792 1244267 := bstep (se 1 (by rfl) ⟨933200, by rfl⟩ : syracuseStep 1244267 = 1866401) B1866401
theorem B1408337 : Blo 143792 1408337 := bstep (se 2 (by rfl) ⟨528126, by rfl⟩ : syracuseStep 1408337 = 1056253) B1056253
theorem B163327 : Blo 143792 163327 := bstep (se 1 (by rfl) ⟨122495, by rfl⟩ : syracuseStep 163327 = 244991) B244991
theorem B163579 : Blo 143792 163579 := bstep (se 1 (by rfl) ⟨122684, by rfl⟩ : syracuseStep 163579 = 245369) B245369
theorem B163687 : Blo 143792 163687 := bstep (se 1 (by rfl) ⟨122765, by rfl⟩ : syracuseStep 163687 = 245531) B245531
theorem B492263 : Blo 143792 492263 := bstep (se 1 (by rfl) ⟨369197, by rfl⟩ : syracuseStep 492263 = 738395) B738395
theorem B328607 : Blo 143792 328607 := bstep (se 1 (by rfl) ⟨246455, by rfl⟩ : syracuseStep 328607 = 492911) B492911
theorem B821015 : Blo 143792 821015 := bstep (se 1 (by rfl) ⟨615761, by rfl⟩ : syracuseStep 821015 = 1231523) B1231523
theorem B165991 : Blo 143792 165991 := bstep (se 1 (by rfl) ⟨124493, by rfl⟩ : syracuseStep 165991 = 248987) B248987
theorem B231545 : Blo 143792 231545 := bstep (se 2 (by rfl) ⟨86829, by rfl⟩ : syracuseStep 231545 = 173659) B173659
theorem B494207 : Blo 143792 494207 := bstep (se 1 (by rfl) ⟨370655, by rfl⟩ : syracuseStep 494207 = 741311) B741311
theorem B2493179 : Blo 143792 2493179 := bstep (se 1 (by rfl) ⟨1869884, by rfl⟩ : syracuseStep 2493179 = 3739769) B3739769
theorem B330911 : Blo 143792 330911 := bstep (se 1 (by rfl) ⟨248183, by rfl⟩ : syracuseStep 330911 = 496367) B496367
theorem B364135 : Blo 143792 364135 := bstep (se 1 (by rfl) ⟨273101, by rfl⟩ : syracuseStep 364135 = 546203) B546203
theorem B462847 : Blo 143792 462847 := bstep (se 1 (by rfl) ⟨347135, by rfl⟩ : syracuseStep 462847 = 694271) B694271
theorem B364783 : Blo 143792 364783 := bstep (se 1 (by rfl) ⟨273587, by rfl⟩ : syracuseStep 364783 = 547175) B547175
theorem B332027 : Blo 143792 332027 := bstep (se 1 (by rfl) ⟨249020, by rfl⟩ : syracuseStep 332027 = 498041) B498041
theorem B299423 : Blo 143792 299423 := bstep (se 1 (by rfl) ⟨224567, by rfl⟩ : syracuseStep 299423 = 449135) B449135
theorem B2069023 : Blo 143792 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B366059 : Blo 143792 366059 := bstep (se 1 (by rfl) ⟨274544, by rfl⟩ : syracuseStep 366059 = 549089) B549089
theorem B16849093 : Blo 143792 16849093 := bstep (se 4 (by rfl) ⟨1579602, by rfl⟩ : syracuseStep 16849093 = 3159205) B3159205
theorem B335719 : Blo 143792 335719 := bstep (se 1 (by rfl) ⟨251789, by rfl⟩ : syracuseStep 335719 = 503579) B503579
theorem B1056655 : Blo 143792 1056655 := bstep (se 1 (by rfl) ⟨792491, by rfl⟩ : syracuseStep 1056655 = 1584983) B1584983
theorem B925921 : Blo 143792 925921 := bstep (se 2 (by rfl) ⟨347220, by rfl⟩ : syracuseStep 925921 = 694441) B694441
theorem B206911 : Blo 143792 206911 := bstep (se 1 (by rfl) ⟨155183, by rfl⟩ : syracuseStep 206911 = 310367) B310367
theorem B829511 : Blo 143792 829511 := bstep (se 1 (by rfl) ⟨622133, by rfl⟩ : syracuseStep 829511 = 1244267) B1244267
theorem B797147 : Blo 143792 797147 := bstep (se 1 (by rfl) ⟨597860, by rfl⟩ : syracuseStep 797147 = 1195721) B1195721
theorem B830195 : Blo 143792 830195 := bstep (se 1 (by rfl) ⟨622646, by rfl⟩ : syracuseStep 830195 = 1245293) B1245293
theorem B1256705 : Blo 143792 1256705 := bstep (se 2 (by rfl) ⟨471264, by rfl⟩ : syracuseStep 1256705 = 942529) B942529
theorem B2829977 : Blo 143792 2829977 := bstep (se 2 (by rfl) ⟨1061241, by rfl⟩ : syracuseStep 2829977 = 2122483) B2122483
theorem B733211 : Blo 143792 733211 := bstep (se 1 (by rfl) ⟨549908, by rfl⟩ : syracuseStep 733211 = 1099817) B1099817
theorem B144063 : Blo 143792 144063 := bstep (se 1 (by rfl) ⟨108047, by rfl⟩ : syracuseStep 144063 = 216095) B216095
theorem B8043239 : Blo 143792 8043239 := bstep (se 1 (by rfl) ⟨6032429, by rfl⟩ : syracuseStep 8043239 = 12064859) B12064859
theorem B2375333 : Blo 143792 2375333 := bstep (se 4 (by rfl) ⟨222687, by rfl⟩ : syracuseStep 2375333 = 445375) B445375
theorem B736937 : Blo 143792 736937 := bstep (se 2 (by rfl) ⟨276351, by rfl⟩ : syracuseStep 736937 = 552703) B552703
theorem B704207 : Blo 143792 704207 := bstep (se 1 (by rfl) ⟨528155, by rfl⟩ : syracuseStep 704207 = 1056311) B1056311
theorem B147391 : Blo 143792 147391 := bstep (se 1 (by rfl) ⟨110543, by rfl⟩ : syracuseStep 147391 = 221087) B221087
theorem B934739 : Blo 143792 934739 := bstep (se 1 (by rfl) ⟨701054, by rfl⟩ : syracuseStep 934739 = 1402109) B1402109
theorem B2442089 : Blo 143792 2442089 := bstep (se 2 (by rfl) ⟨915783, by rfl⟩ : syracuseStep 2442089 = 1831567) B1831567
theorem B707039 : Blo 143792 707039 := bstep (se 1 (by rfl) ⟨530279, by rfl⟩ : syracuseStep 707039 = 1060559) B1060559
theorem B707051 : Blo 143792 707051 := bstep (se 1 (by rfl) ⟨530288, by rfl⟩ : syracuseStep 707051 = 1060577) B1060577
theorem B216347 : Blo 143792 216347 := bstep (se 1 (by rfl) ⟨162260, by rfl⟩ : syracuseStep 216347 = 324521) B324521
theorem B217769 : Blo 143792 217769 := bstep (se 2 (by rfl) ⟨81663, by rfl⟩ : syracuseStep 217769 = 163327) B163327
theorem B938891 : Blo 143792 938891 := bstep (se 1 (by rfl) ⟨704168, by rfl⟩ : syracuseStep 938891 = 1408337) B1408337
theorem B218105 : Blo 143792 218105 := bstep (se 2 (by rfl) ⟨81789, by rfl⟩ : syracuseStep 218105 = 163579) B163579
theorem B218249 : Blo 143792 218249 := bstep (se 2 (by rfl) ⟨81843, by rfl⟩ : syracuseStep 218249 = 163687) B163687
theorem B546871 : Blo 143792 546871 := bstep (se 1 (by rfl) ⟨410153, by rfl⟩ : syracuseStep 546871 = 820307) B820307
theorem B219305 : Blo 143792 219305 := bstep (se 2 (by rfl) ⟨82239, by rfl⟩ : syracuseStep 219305 = 164479) B164479
theorem B220463 : Blo 143792 220463 := bstep (se 1 (by rfl) ⟨165347, by rfl⟩ : syracuseStep 220463 = 330695) B330695
theorem B548815 : Blo 143792 548815 := bstep (se 1 (by rfl) ⟨411611, by rfl⟩ : syracuseStep 548815 = 823223) B823223
theorem B221609 : Blo 143792 221609 := bstep (se 2 (by rfl) ⟨83103, by rfl⟩ : syracuseStep 221609 = 166207) B166207
theorem B746657 : Blo 143792 746657 := bstep (se 2 (by rfl) ⟨279996, by rfl⟩ : syracuseStep 746657 = 559993) B559993
theorem B618137 : Blo 143792 618137 := bstep (se 2 (by rfl) ⟨231801, by rfl⟩ : syracuseStep 618137 = 463603) B463603
theorem B1208603 : Blo 143792 1208603 := bstep (se 1 (by rfl) ⟨906452, by rfl⟩ : syracuseStep 1208603 = 1812905) B1812905
theorem B554921 : Blo 143792 554921 := bstep (se 2 (by rfl) ⟨208095, by rfl⟩ : syracuseStep 554921 = 416191) B416191
theorem B325907 : Blo 143792 325907 := bstep (se 1 (by rfl) ⟨244430, by rfl⟩ : syracuseStep 325907 = 488861) B488861
theorem B490751 : Blo 143792 490751 := bstep (se 1 (by rfl) ⟨368063, by rfl⟩ : syracuseStep 490751 = 736127) B736127
theorem B328175 : Blo 143792 328175 := bstep (se 1 (by rfl) ⟨246131, by rfl⟩ : syracuseStep 328175 = 492263) B492263
theorem B623159 : Blo 143792 623159 := bstep (se 1 (by rfl) ⟨467369, by rfl⟩ : syracuseStep 623159 = 934739) B934739
theorem B329471 : Blo 143792 329471 := bstep (se 1 (by rfl) ⟨247103, by rfl⟩ : syracuseStep 329471 = 494207) B494207
theorem B625927 : Blo 143792 625927 := bstep (se 1 (by rfl) ⟨469445, by rfl⟩ : syracuseStep 625927 = 938891) B938891
theorem B2758697 : Blo 143792 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B497771 : Blo 143792 497771 := bstep (se 1 (by rfl) ⟨373328, by rfl⟩ : syracuseStep 497771 = 746657) B746657
theorem B531431 : Blo 143792 531431 := bstep (se 1 (by rfl) ⟨398573, by rfl⟩ : syracuseStep 531431 = 797147) B797147
theorem B729161 : Blo 143792 729161 := bstep (se 2 (by rfl) ⟨273435, by rfl⟩ : syracuseStep 729161 = 546871) B546871
theorem B369947 : Blo 143792 369947 := bstep (se 1 (by rfl) ⟨277460, by rfl⟩ : syracuseStep 369947 = 554921) B554921
theorem B1583555 : Blo 143792 1583555 := bstep (se 1 (by rfl) ⟨1187666, by rfl⟩ : syracuseStep 1583555 = 2375333) B2375333
theorem B469471 : Blo 143792 469471 := bstep (se 1 (by rfl) ⟨352103, by rfl⟩ : syracuseStep 469471 = 704207) B704207
theorem B731753 : Blo 143792 731753 := bstep (se 2 (by rfl) ⟨274407, by rfl⟩ : syracuseStep 731753 = 548815) B548815
theorem B798461 : Blo 143792 798461 := bstep (se 3 (by rfl) ⟨149711, by rfl⟩ : syracuseStep 798461 = 299423) B299423
theorem B471359 : Blo 143792 471359 := bstep (se 1 (by rfl) ⟨353519, by rfl⟩ : syracuseStep 471359 = 707039) B707039
theorem B471367 : Blo 143792 471367 := bstep (se 1 (by rfl) ⟨353525, by rfl⟩ : syracuseStep 471367 = 707051) B707051
theorem B144231 : Blo 143792 144231 := bstep (se 1 (by rfl) ⟨108173, by rfl⟩ : syracuseStep 144231 = 216347) B216347
theorem B275881 : Blo 143792 275881 := bstep (se 2 (by rfl) ⟨103455, by rfl⟩ : syracuseStep 275881 = 206911) B206911
theorem B145179 : Blo 143792 145179 := bstep (se 1 (by rfl) ⟨108884, by rfl⟩ : syracuseStep 145179 = 217769) B217769
theorem B145403 : Blo 143792 145403 := bstep (se 1 (by rfl) ⟨109052, by rfl⟩ : syracuseStep 145403 = 218105) B218105
theorem B145499 : Blo 143792 145499 := bstep (se 1 (by rfl) ⟨109124, by rfl⟩ : syracuseStep 145499 = 218249) B218249
theorem B244039 : Blo 143792 244039 := bstep (se 1 (by rfl) ⟨183029, by rfl⟩ : syracuseStep 244039 = 366059) B366059
theorem B146203 : Blo 143792 146203 := bstep (se 1 (by rfl) ⟨109652, by rfl⟩ : syracuseStep 146203 = 219305) B219305
theorem B146975 : Blo 143792 146975 := bstep (se 1 (by rfl) ⟨110231, by rfl⟩ : syracuseStep 146975 = 220463) B220463
theorem B147739 : Blo 143792 147739 := bstep (se 1 (by rfl) ⟨110804, by rfl⟩ : syracuseStep 147739 = 221609) B221609
theorem B837803 : Blo 143792 837803 := bstep (se 1 (by rfl) ⟨628352, by rfl⟩ : syracuseStep 837803 = 1256705) B1256705
theorem B412091 : Blo 143792 412091 := bstep (se 1 (by rfl) ⟨309068, by rfl⟩ : syracuseStep 412091 = 618137) B618137
theorem B1886651 : Blo 143792 1886651 := bstep (se 1 (by rfl) ⟨1414988, by rfl⟩ : syracuseStep 1886651 = 2829977) B2829977
theorem B805735 : Blo 143792 805735 := bstep (se 1 (by rfl) ⟨604301, by rfl⟩ : syracuseStep 805735 = 1208603) B1208603
theorem B22465457 : Blo 143792 22465457 := bstep (se 2 (by rfl) ⟨8424546, by rfl⟩ : syracuseStep 22465457 = 16849093) B16849093
theorem B217271 : Blo 143792 217271 := bstep (se 1 (by rfl) ⟨162953, by rfl⟩ : syracuseStep 217271 = 325907) B325907
theorem B5362159 : Blo 143792 5362159 := bstep (se 1 (by rfl) ⟨4021619, by rfl⟩ : syracuseStep 5362159 = 8043239) B8043239
theorem B447625 : Blo 143792 447625 := bstep (se 2 (by rfl) ⟨167859, by rfl⟩ : syracuseStep 447625 = 335719) B335719
theorem B1234561 : Blo 143792 1234561 := bstep (se 2 (by rfl) ⟨462960, by rfl⟩ : syracuseStep 1234561 = 925921) B925921
theorem B1628059 : Blo 143792 1628059 := bstep (se 1 (by rfl) ⟨1221044, by rfl⟩ : syracuseStep 1628059 = 2442089) B2442089
theorem B219071 : Blo 143792 219071 := bstep (se 1 (by rfl) ⟨164303, by rfl⟩ : syracuseStep 219071 = 328607) B328607
theorem B547343 : Blo 143792 547343 := bstep (se 1 (by rfl) ⟨410507, by rfl⟩ : syracuseStep 547343 = 821015) B821015
theorem B1662119 : Blo 143792 1662119 := bstep (se 1 (by rfl) ⟨1246589, by rfl⟩ : syracuseStep 1662119 = 2493179) B2493179
theorem B220607 : Blo 143792 220607 := bstep (se 1 (by rfl) ⟨165455, by rfl⟩ : syracuseStep 220607 = 330911) B330911
theorem B221321 : Blo 143792 221321 := bstep (se 2 (by rfl) ⟨82995, by rfl⟩ : syracuseStep 221321 = 165991) B165991
theorem B221351 : Blo 143792 221351 := bstep (se 1 (by rfl) ⟨166013, by rfl⟩ : syracuseStep 221351 = 332027) B332027
theorem B485513 : Blo 143792 485513 := bstep (se 2 (by rfl) ⟨182067, by rfl⟩ : syracuseStep 485513 = 364135) B364135
theorem B617129 : Blo 143792 617129 := bstep (se 2 (by rfl) ⟨231423, by rfl⟩ : syracuseStep 617129 = 462847) B462847
theorem B486377 : Blo 143792 486377 := bstep (se 2 (by rfl) ⟨182391, by rfl⟩ : syracuseStep 486377 = 364783) B364783
theorem B617453 : Blo 143792 617453 := bstep (se 3 (by rfl) ⟨115772, by rfl⟩ : syracuseStep 617453 = 231545) B231545
theorem B553007 : Blo 143792 553007 := bstep (se 1 (by rfl) ⟨414755, by rfl⟩ : syracuseStep 553007 = 829511) B829511
theorem B553463 : Blo 143792 553463 := bstep (se 1 (by rfl) ⟨415097, by rfl⟩ : syracuseStep 553463 = 830195) B830195
theorem B488807 : Blo 143792 488807 := bstep (se 1 (by rfl) ⟨366605, by rfl⟩ : syracuseStep 488807 = 733211) B733211
theorem B327167 : Blo 143792 327167 := bstep (se 1 (by rfl) ⟨245375, by rfl⟩ : syracuseStep 327167 = 490751) B490751
theorem B491291 : Blo 143792 491291 := bstep (se 1 (by rfl) ⟨368468, by rfl⟩ : syracuseStep 491291 = 736937) B736937
theorem B1408873 : Blo 143792 1408873 := bstep (se 2 (by rfl) ⟨528327, by rfl⟩ : syracuseStep 1408873 = 1056655) B1056655
theorem B558535 : Blo 143792 558535 := bstep (se 1 (by rfl) ⟨418901, by rfl⟩ : syracuseStep 558535 = 837803) B837803
theorem B14976971 : Blo 143792 14976971 := bstep (se 1 (by rfl) ⟨11232728, by rfl⟩ : syracuseStep 14976971 = 22465457) B22465457
theorem B625961 : Blo 143792 625961 := bstep (se 2 (by rfl) ⟨234735, by rfl⟩ : syracuseStep 625961 = 469471) B469471
theorem B1839131 : Blo 143792 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B331847 : Blo 143792 331847 := bstep (se 1 (by rfl) ⟨248885, by rfl⟩ : syracuseStep 331847 = 497771) B497771
theorem B364895 : Blo 143792 364895 := bstep (se 1 (by rfl) ⟨273671, by rfl⟩ : syracuseStep 364895 = 547343) B547343
theorem B628489 : Blo 143792 628489 := bstep (se 2 (by rfl) ⟨235683, by rfl⟩ : syracuseStep 628489 = 471367) B471367
theorem B7149545 : Blo 143792 7149545 := bstep (se 2 (by rfl) ⟨2681079, by rfl⟩ : syracuseStep 7149545 = 5362159) B5362159
theorem B367841 : Blo 143792 367841 := bstep (se 2 (by rfl) ⟨137940, by rfl⟩ : syracuseStep 367841 = 275881) B275881
theorem B1646081 : Blo 143792 1646081 := bstep (se 2 (by rfl) ⟨617280, by rfl⟩ : syracuseStep 1646081 = 1234561) B1234561
theorem B532307 : Blo 143792 532307 := bstep (se 1 (by rfl) ⟨399230, by rfl⟩ : syracuseStep 532307 = 798461) B798461
theorem B2170745 : Blo 143792 2170745 := bstep (se 2 (by rfl) ⟨814029, by rfl⟩ : syracuseStep 2170745 = 1628059) B1628059
theorem B368671 : Blo 143792 368671 := bstep (se 1 (by rfl) ⟨276503, by rfl⟩ : syracuseStep 368671 = 553007) B553007
theorem B368975 : Blo 143792 368975 := bstep (se 1 (by rfl) ⟨276731, by rfl⟩ : syracuseStep 368975 = 553463) B553463
theorem B1878497 : Blo 143792 1878497 := bstep (se 2 (by rfl) ⟨704436, by rfl⟩ : syracuseStep 1878497 = 1408873) B1408873
theorem B1256957 : Blo 143792 1256957 := bstep (se 3 (by rfl) ⟨235679, by rfl⟩ : syracuseStep 1256957 = 471359) B471359
theorem B274727 : Blo 143792 274727 := bstep (se 1 (by rfl) ⟨206045, by rfl⟩ : syracuseStep 274727 = 412091) B412091
theorem B1257767 : Blo 143792 1257767 := bstep (se 1 (by rfl) ⟨943325, by rfl⟩ : syracuseStep 1257767 = 1886651) B1886651
theorem B144847 : Blo 143792 144847 := bstep (se 1 (by rfl) ⟨108635, by rfl⟩ : syracuseStep 144847 = 217271) B217271
theorem B146047 : Blo 143792 146047 := bstep (se 1 (by rfl) ⟨109535, by rfl⟩ : syracuseStep 146047 = 219071) B219071
theorem B834569 : Blo 143792 834569 := bstep (se 2 (by rfl) ⟨312963, by rfl⟩ : syracuseStep 834569 = 625927) B625927
theorem B147071 : Blo 143792 147071 := bstep (se 1 (by rfl) ⟨110303, by rfl⟩ : syracuseStep 147071 = 220607) B220607
theorem B147547 : Blo 143792 147547 := bstep (se 1 (by rfl) ⟨110660, by rfl⟩ : syracuseStep 147547 = 221321) B221321
theorem B147567 : Blo 143792 147567 := bstep (se 1 (by rfl) ⟨110675, by rfl⟩ : syracuseStep 147567 = 221351) B221351
theorem B246631 : Blo 143792 246631 := bstep (se 1 (by rfl) ⟨184973, by rfl⟩ : syracuseStep 246631 = 369947) B369947
theorem B411419 : Blo 143792 411419 := bstep (se 1 (by rfl) ⟨308564, by rfl⟩ : syracuseStep 411419 = 617129) B617129
theorem B411635 : Blo 143792 411635 := bstep (se 1 (by rfl) ⟨308726, by rfl⟩ : syracuseStep 411635 = 617453) B617453
theorem B218111 : Blo 143792 218111 := bstep (se 1 (by rfl) ⟨163583, by rfl⟩ : syracuseStep 218111 = 327167) B327167
theorem B218783 : Blo 143792 218783 := bstep (se 1 (by rfl) ⟨164087, by rfl⟩ : syracuseStep 218783 = 328175) B328175
theorem B415439 : Blo 143792 415439 := bstep (se 1 (by rfl) ⟨311579, by rfl⟩ : syracuseStep 415439 = 623159) B623159
theorem B219647 : Blo 143792 219647 := bstep (se 1 (by rfl) ⟨164735, by rfl⟩ : syracuseStep 219647 = 329471) B329471
theorem B1074313 : Blo 143792 1074313 := bstep (se 2 (by rfl) ⟨402867, by rfl⟩ : syracuseStep 1074313 = 805735) B805735
theorem B354287 : Blo 143792 354287 := bstep (se 1 (by rfl) ⟨265715, by rfl⟩ : syracuseStep 354287 = 531431) B531431
theorem B1108079 : Blo 143792 1108079 := bstep (se 1 (by rfl) ⟨831059, by rfl⟩ : syracuseStep 1108079 = 1662119) B1662119
theorem B486107 : Blo 143792 486107 := bstep (se 1 (by rfl) ⟨364580, by rfl⟩ : syracuseStep 486107 = 729161) B729161
theorem B2387333 : Blo 143792 2387333 := bstep (se 4 (by rfl) ⟨223812, by rfl⟩ : syracuseStep 2387333 = 447625) B447625
theorem B4222813 : Blo 143792 4222813 := bstep (se 3 (by rfl) ⟨791777, by rfl⟩ : syracuseStep 4222813 = 1583555) B1583555
theorem B323675 : Blo 143792 323675 := bstep (se 1 (by rfl) ⟨242756, by rfl⟩ : syracuseStep 323675 = 485513) B485513
theorem B487835 : Blo 143792 487835 := bstep (se 1 (by rfl) ⟨365876, by rfl⟩ : syracuseStep 487835 = 731753) B731753
theorem B324251 : Blo 143792 324251 := bstep (se 1 (by rfl) ⟨243188, by rfl⟩ : syracuseStep 324251 = 486377) B486377
theorem B325385 : Blo 143792 325385 := bstep (se 2 (by rfl) ⟨122019, by rfl⟩ : syracuseStep 325385 = 244039) B244039
theorem B325871 : Blo 143792 325871 := bstep (se 1 (by rfl) ⟨244403, by rfl⟩ : syracuseStep 325871 = 488807) B488807
theorem B327527 : Blo 143792 327527 := bstep (se 1 (by rfl) ⟨245645, by rfl⟩ : syracuseStep 327527 = 491291) B491291
theorem B491561 : Blo 143792 491561 := bstep (se 2 (by rfl) ⟨184335, by rfl⟩ : syracuseStep 491561 = 368671) B368671
theorem B328841 : Blo 143792 328841 := bstep (se 2 (by rfl) ⟨123315, by rfl⟩ : syracuseStep 328841 = 246631) B246631
theorem B1447163 : Blo 143792 1447163 := bstep (se 1 (by rfl) ⟨1085372, by rfl⟩ : syracuseStep 1447163 = 2170745) B2170745
theorem B236191 : Blo 143792 236191 := bstep (se 1 (by rfl) ⟨177143, by rfl⟩ : syracuseStep 236191 = 354287) B354287
theorem B1252331 : Blo 143792 1252331 := bstep (se 1 (by rfl) ⟨939248, by rfl⟩ : syracuseStep 1252331 = 1878497) B1878497
theorem B6366221 : Blo 143792 6366221 := bstep (se 3 (by rfl) ⟨1193666, by rfl⟩ : syracuseStep 6366221 = 2387333) B2387333
theorem B274279 : Blo 143792 274279 := bstep (se 1 (by rfl) ⟨205709, by rfl⟩ : syracuseStep 274279 = 411419) B411419
theorem B274423 : Blo 143792 274423 := bstep (se 1 (by rfl) ⟨205817, by rfl⟩ : syracuseStep 274423 = 411635) B411635
theorem B1226087 : Blo 143792 1226087 := bstep (se 1 (by rfl) ⟨919565, by rfl⟩ : syracuseStep 1226087 = 1839131) B1839131
theorem B243263 : Blo 143792 243263 := bstep (se 1 (by rfl) ⟨182447, by rfl⟩ : syracuseStep 243263 = 364895) B364895
theorem B145407 : Blo 143792 145407 := bstep (se 1 (by rfl) ⟨109055, by rfl⟩ : syracuseStep 145407 = 218111) B218111
theorem B145855 : Blo 143792 145855 := bstep (se 1 (by rfl) ⟨109391, by rfl⟩ : syracuseStep 145855 = 218783) B218783
theorem B276959 : Blo 143792 276959 := bstep (se 1 (by rfl) ⟨207719, by rfl⟩ : syracuseStep 276959 = 415439) B415439
theorem B4766363 : Blo 143792 4766363 := bstep (se 1 (by rfl) ⟨3574772, by rfl⟩ : syracuseStep 4766363 = 7149545) B7149545
theorem B146431 : Blo 143792 146431 := bstep (se 1 (by rfl) ⟨109823, by rfl⟩ : syracuseStep 146431 = 219647) B219647
theorem B245227 : Blo 143792 245227 := bstep (se 1 (by rfl) ⟨183920, by rfl⟩ : syracuseStep 245227 = 367841) B367841
theorem B1097387 : Blo 143792 1097387 := bstep (se 1 (by rfl) ⟨823040, by rfl⟩ : syracuseStep 1097387 = 1646081) B1646081
theorem B245983 : Blo 143792 245983 := bstep (se 1 (by rfl) ⟨184487, by rfl⟩ : syracuseStep 245983 = 368975) B368975
theorem B738719 : Blo 143792 738719 := bstep (se 1 (by rfl) ⟨554039, by rfl⟩ : syracuseStep 738719 = 1108079) B1108079
theorem B837971 : Blo 143792 837971 := bstep (se 1 (by rfl) ⟨628478, by rfl⟩ : syracuseStep 837971 = 1256957) B1256957
theorem B837985 : Blo 143792 837985 := bstep (se 2 (by rfl) ⟨314244, by rfl⟩ : syracuseStep 837985 = 628489) B628489
theorem B215783 : Blo 143792 215783 := bstep (se 1 (by rfl) ⟨161837, by rfl⟩ : syracuseStep 215783 = 323675) B323675
theorem B183151 : Blo 143792 183151 := bstep (se 1 (by rfl) ⟨137363, by rfl⟩ : syracuseStep 183151 = 274727) B274727
theorem B838511 : Blo 143792 838511 := bstep (se 1 (by rfl) ⟨628883, by rfl⟩ : syracuseStep 838511 = 1257767) B1257767
theorem B216167 : Blo 143792 216167 := bstep (se 1 (by rfl) ⟨162125, by rfl⟩ : syracuseStep 216167 = 324251) B324251
theorem B216923 : Blo 143792 216923 := bstep (se 1 (by rfl) ⟨162692, by rfl⟩ : syracuseStep 216923 = 325385) B325385
theorem B217247 : Blo 143792 217247 := bstep (se 1 (by rfl) ⟨162935, by rfl⟩ : syracuseStep 217247 = 325871) B325871
theorem B218351 : Blo 143792 218351 := bstep (se 1 (by rfl) ⟨163763, by rfl⟩ : syracuseStep 218351 = 327527) B327527
theorem B9984647 : Blo 143792 9984647 := bstep (se 1 (by rfl) ⟨7488485, by rfl⟩ : syracuseStep 9984647 = 14976971) B14976971
theorem B1432417 : Blo 143792 1432417 := bstep (se 2 (by rfl) ⟨537156, by rfl⟩ : syracuseStep 1432417 = 1074313) B1074313
theorem B744713 : Blo 143792 744713 := bstep (se 2 (by rfl) ⟨279267, by rfl⟩ : syracuseStep 744713 = 558535) B558535
theorem B417307 : Blo 143792 417307 := bstep (se 1 (by rfl) ⟨312980, by rfl⟩ : syracuseStep 417307 = 625961) B625961
theorem B221231 : Blo 143792 221231 := bstep (se 1 (by rfl) ⟨165923, by rfl⟩ : syracuseStep 221231 = 331847) B331847
theorem B5630417 : Blo 143792 5630417 := bstep (se 2 (by rfl) ⟨2111406, by rfl⟩ : syracuseStep 5630417 = 4222813) B4222813
theorem B354871 : Blo 143792 354871 := bstep (se 1 (by rfl) ⟨266153, by rfl⟩ : syracuseStep 354871 = 532307) B532307
theorem B324071 : Blo 143792 324071 := bstep (se 1 (by rfl) ⟨243053, by rfl⟩ : syracuseStep 324071 = 486107) B486107
theorem B325223 : Blo 143792 325223 := bstep (se 1 (by rfl) ⟨243917, by rfl⟩ : syracuseStep 325223 = 487835) B487835
theorem B556379 : Blo 143792 556379 := bstep (se 1 (by rfl) ⟨417284, by rfl⟩ : syracuseStep 556379 = 834569) B834569
theorem B327707 : Blo 143792 327707 := bstep (se 1 (by rfl) ⟨245780, by rfl⟩ : syracuseStep 327707 = 491561) B491561
theorem B327977 : Blo 143792 327977 := bstep (se 2 (by rfl) ⟨122991, by rfl⟩ : syracuseStep 327977 = 245983) B245983
theorem B492479 : Blo 143792 492479 := bstep (se 1 (by rfl) ⟨369359, by rfl⟩ : syracuseStep 492479 = 738719) B738719
theorem B558647 : Blo 143792 558647 := bstep (se 1 (by rfl) ⟨418985, by rfl⟩ : syracuseStep 558647 = 837971) B837971
theorem B559007 : Blo 143792 559007 := bstep (se 1 (by rfl) ⟨419255, by rfl⟩ : syracuseStep 559007 = 838511) B838511
theorem B1117313 : Blo 143792 1117313 := bstep (se 2 (by rfl) ⟨418992, by rfl⟩ : syracuseStep 1117313 = 837985) B837985
theorem B6656431 : Blo 143792 6656431 := bstep (se 1 (by rfl) ⟨4992323, by rfl⟩ : syracuseStep 6656431 = 9984647) B9984647
theorem B496475 : Blo 143792 496475 := bstep (se 1 (by rfl) ⟨372356, by rfl⟩ : syracuseStep 496475 = 744713) B744713
theorem B365705 : Blo 143792 365705 := bstep (se 2 (by rfl) ⟨137139, by rfl⟩ : syracuseStep 365705 = 274279) B274279
theorem B365897 : Blo 143792 365897 := bstep (se 2 (by rfl) ⟨137211, by rfl⟩ : syracuseStep 365897 = 274423) B274423
theorem B1909889 : Blo 143792 1909889 := bstep (se 2 (by rfl) ⟨716208, by rfl⟩ : syracuseStep 1909889 = 1432417) B1432417
theorem B370919 : Blo 143792 370919 := bstep (se 1 (by rfl) ⟨278189, by rfl⟩ : syracuseStep 370919 = 556379) B556379
theorem B731591 : Blo 143792 731591 := bstep (se 1 (by rfl) ⟨548693, by rfl⟩ : syracuseStep 731591 = 1097387) B1097387
theorem B143855 : Blo 143792 143855 := bstep (se 1 (by rfl) ⟨107891, by rfl⟩ : syracuseStep 143855 = 215783) B215783
theorem B144111 : Blo 143792 144111 := bstep (se 1 (by rfl) ⟨108083, by rfl⟩ : syracuseStep 144111 = 216167) B216167
theorem B144615 : Blo 143792 144615 := bstep (se 1 (by rfl) ⟨108461, by rfl⟩ : syracuseStep 144615 = 216923) B216923
theorem B144831 : Blo 143792 144831 := bstep (se 1 (by rfl) ⟨108623, by rfl⟩ : syracuseStep 144831 = 217247) B217247
theorem B145567 : Blo 143792 145567 := bstep (se 1 (by rfl) ⟨109175, by rfl⟩ : syracuseStep 145567 = 218351) B218351
theorem B964775 : Blo 143792 964775 := bstep (se 1 (by rfl) ⟨723581, by rfl⟩ : syracuseStep 964775 = 1447163) B1447163
theorem B244201 : Blo 143792 244201 := bstep (se 2 (by rfl) ⟨91575, by rfl⟩ : syracuseStep 244201 = 183151) B183151
theorem B834887 : Blo 143792 834887 := bstep (se 1 (by rfl) ⟨626165, by rfl⟩ : syracuseStep 834887 = 1252331) B1252331
theorem B147487 : Blo 143792 147487 := bstep (se 1 (by rfl) ⟨110615, by rfl⟩ : syracuseStep 147487 = 221231) B221231
theorem B4244147 : Blo 143792 4244147 := bstep (se 1 (by rfl) ⟨3183110, by rfl⟩ : syracuseStep 4244147 = 6366221) B6366221
theorem B738557 : Blo 143792 738557 := bstep (se 3 (by rfl) ⟨138479, by rfl⟩ : syracuseStep 738557 = 276959) B276959
theorem B3753611 : Blo 143792 3753611 := bstep (se 1 (by rfl) ⟨2815208, by rfl⟩ : syracuseStep 3753611 = 5630417) B5630417
theorem B216047 : Blo 143792 216047 := bstep (se 1 (by rfl) ⟨162035, by rfl⟩ : syracuseStep 216047 = 324071) B324071
theorem B314921 : Blo 143792 314921 := bstep (se 2 (by rfl) ⟨118095, by rfl⟩ : syracuseStep 314921 = 236191) B236191
theorem B216815 : Blo 143792 216815 := bstep (se 1 (by rfl) ⟨162611, by rfl⟩ : syracuseStep 216815 = 325223) B325223
theorem B219227 : Blo 143792 219227 := bstep (se 1 (by rfl) ⟨164420, by rfl⟩ : syracuseStep 219227 = 328841) B328841
theorem B1892645 : Blo 143792 1892645 := bstep (se 4 (by rfl) ⟨177435, by rfl⟩ : syracuseStep 1892645 = 354871) B354871
theorem B817391 : Blo 143792 817391 := bstep (se 1 (by rfl) ⟨613043, by rfl⟩ : syracuseStep 817391 = 1226087) B1226087
theorem B162175 : Blo 143792 162175 := bstep (se 1 (by rfl) ⟨121631, by rfl⟩ : syracuseStep 162175 = 243263) B243263
theorem B3177575 : Blo 143792 3177575 := bstep (se 1 (by rfl) ⟨2383181, by rfl⟩ : syracuseStep 3177575 = 4766363) B4766363
theorem B326969 : Blo 143792 326969 := bstep (se 2 (by rfl) ⟨122613, by rfl⟩ : syracuseStep 326969 = 245227) B245227
theorem B556409 : Blo 143792 556409 := bstep (se 2 (by rfl) ⟨208653, by rfl⟩ : syracuseStep 556409 = 417307) B417307
theorem B328319 : Blo 143792 328319 := bstep (se 1 (by rfl) ⟨246239, by rfl⟩ : syracuseStep 328319 = 492479) B492479
theorem B492371 : Blo 143792 492371 := bstep (se 1 (by rfl) ⟨369278, by rfl⟩ : syracuseStep 492371 = 738557) B738557
theorem B330983 : Blo 143792 330983 := bstep (se 1 (by rfl) ⟨248237, by rfl⟩ : syracuseStep 330983 = 496475) B496475
theorem B370939 : Blo 143792 370939 := bstep (se 1 (by rfl) ⟨278204, by rfl⟩ : syracuseStep 370939 = 556409) B556409
theorem B2829431 : Blo 143792 2829431 := bstep (se 1 (by rfl) ⟨2122073, by rfl⟩ : syracuseStep 2829431 = 4244147) B4244147
theorem B372431 : Blo 143792 372431 := bstep (se 1 (by rfl) ⟨279323, by rfl⟩ : syracuseStep 372431 = 558647) B558647
theorem B2502407 : Blo 143792 2502407 := bstep (se 1 (by rfl) ⟨1876805, by rfl⟩ : syracuseStep 2502407 = 3753611) B3753611
theorem B372671 : Blo 143792 372671 := bstep (se 1 (by rfl) ⟨279503, by rfl⟩ : syracuseStep 372671 = 559007) B559007
theorem B144031 : Blo 143792 144031 := bstep (se 1 (by rfl) ⟨108023, by rfl⟩ : syracuseStep 144031 = 216047) B216047
theorem B209947 : Blo 143792 209947 := bstep (se 1 (by rfl) ⟨157460, by rfl⟩ : syracuseStep 209947 = 314921) B314921
theorem B144543 : Blo 143792 144543 := bstep (se 1 (by rfl) ⟨108407, by rfl⟩ : syracuseStep 144543 = 216815) B216815
theorem B243803 : Blo 143792 243803 := bstep (se 1 (by rfl) ⟨182852, by rfl⟩ : syracuseStep 243803 = 365705) B365705
theorem B243931 : Blo 143792 243931 := bstep (se 1 (by rfl) ⟨182948, by rfl⟩ : syracuseStep 243931 = 365897) B365897
theorem B146151 : Blo 143792 146151 := bstep (se 1 (by rfl) ⟨109613, by rfl⟩ : syracuseStep 146151 = 219227) B219227
theorem B1261763 : Blo 143792 1261763 := bstep (se 1 (by rfl) ⟨946322, by rfl⟩ : syracuseStep 1261763 = 1892645) B1892645
theorem B2179709 : Blo 143792 2179709 := bstep (se 3 (by rfl) ⟨408695, by rfl⟩ : syracuseStep 2179709 = 817391) B817391
theorem B247279 : Blo 143792 247279 := bstep (se 1 (by rfl) ⟨185459, by rfl⟩ : syracuseStep 247279 = 370919) B370919
theorem B216233 : Blo 143792 216233 := bstep (se 2 (by rfl) ⟨81087, by rfl⟩ : syracuseStep 216233 = 162175) B162175
theorem B643183 : Blo 143792 643183 := bstep (se 1 (by rfl) ⟨482387, by rfl⟩ : syracuseStep 643183 = 964775) B964775
theorem B2118383 : Blo 143792 2118383 := bstep (se 1 (by rfl) ⟨1588787, by rfl⟩ : syracuseStep 2118383 = 3177575) B3177575
theorem B217979 : Blo 143792 217979 := bstep (se 1 (by rfl) ⟨163484, by rfl⟩ : syracuseStep 217979 = 326969) B326969
theorem B218471 : Blo 143792 218471 := bstep (se 1 (by rfl) ⟨163853, by rfl⟩ : syracuseStep 218471 = 327707) B327707
theorem B218651 : Blo 143792 218651 := bstep (se 1 (by rfl) ⟨163988, by rfl⟩ : syracuseStep 218651 = 327977) B327977
theorem B744875 : Blo 143792 744875 := bstep (se 1 (by rfl) ⟨558656, by rfl⟩ : syracuseStep 744875 = 1117313) B1117313
theorem B8875241 : Blo 143792 8875241 := bstep (se 2 (by rfl) ⟨3328215, by rfl⟩ : syracuseStep 8875241 = 6656431) B6656431
theorem B1273259 : Blo 143792 1273259 := bstep (se 1 (by rfl) ⟨954944, by rfl⟩ : syracuseStep 1273259 = 1909889) B1909889
theorem B487727 : Blo 143792 487727 := bstep (se 1 (by rfl) ⟨365795, by rfl⟩ : syracuseStep 487727 = 731591) B731591
theorem B325601 : Blo 143792 325601 := bstep (se 2 (by rfl) ⟨122100, by rfl⟩ : syracuseStep 325601 = 244201) B244201
theorem B556591 : Blo 143792 556591 := bstep (se 1 (by rfl) ⟨417443, by rfl⟩ : syracuseStep 556591 = 834887) B834887
theorem B328247 : Blo 143792 328247 := bstep (se 1 (by rfl) ⟨246185, by rfl⟩ : syracuseStep 328247 = 492371) B492371
theorem B329705 : Blo 143792 329705 := bstep (se 2 (by rfl) ⟨123639, by rfl⟩ : syracuseStep 329705 = 247279) B247279
theorem B494585 : Blo 143792 494585 := bstep (se 2 (by rfl) ⟨185469, by rfl⟩ : syracuseStep 494585 = 370939) B370939
theorem B1412255 : Blo 143792 1412255 := bstep (se 1 (by rfl) ⟨1059191, by rfl⟩ : syracuseStep 1412255 = 2118383) B2118383
theorem B496583 : Blo 143792 496583 := bstep (se 1 (by rfl) ⟨372437, by rfl⟩ : syracuseStep 496583 = 744875) B744875
theorem B1453139 : Blo 143792 1453139 := bstep (se 1 (by rfl) ⟨1089854, by rfl⟩ : syracuseStep 1453139 = 2179709) B2179709
theorem B144155 : Blo 143792 144155 := bstep (se 1 (by rfl) ⟨108116, by rfl⟩ : syracuseStep 144155 = 216233) B216233
theorem B145319 : Blo 143792 145319 := bstep (se 1 (by rfl) ⟨108989, by rfl⟩ : syracuseStep 145319 = 217979) B217979
theorem B145647 : Blo 143792 145647 := bstep (se 1 (by rfl) ⟨109235, by rfl⟩ : syracuseStep 145647 = 218471) B218471
theorem B145767 : Blo 143792 145767 := bstep (se 1 (by rfl) ⟨109325, by rfl⟩ : syracuseStep 145767 = 218651) B218651
theorem B279929 : Blo 143792 279929 := bstep (se 2 (by rfl) ⟨104973, by rfl⟩ : syracuseStep 279929 = 209947) B209947
theorem B1886287 : Blo 143792 1886287 := bstep (se 1 (by rfl) ⟨1414715, by rfl⟩ : syracuseStep 1886287 = 2829431) B2829431
theorem B5916827 : Blo 143792 5916827 := bstep (se 1 (by rfl) ⟨4437620, by rfl⟩ : syracuseStep 5916827 = 8875241) B8875241
theorem B248287 : Blo 143792 248287 := bstep (se 1 (by rfl) ⟨186215, by rfl⟩ : syracuseStep 248287 = 372431) B372431
theorem B248447 : Blo 143792 248447 := bstep (se 1 (by rfl) ⟨186335, by rfl⟩ : syracuseStep 248447 = 372671) B372671
theorem B217067 : Blo 143792 217067 := bstep (se 1 (by rfl) ⟨162800, by rfl⟩ : syracuseStep 217067 = 325601) B325601
theorem B742121 : Blo 143792 742121 := bstep (se 2 (by rfl) ⟨278295, by rfl⟩ : syracuseStep 742121 = 556591) B556591
theorem B841175 : Blo 143792 841175 := bstep (se 1 (by rfl) ⟨630881, by rfl⟩ : syracuseStep 841175 = 1261763) B1261763
theorem B218879 : Blo 143792 218879 := bstep (se 1 (by rfl) ⟨164159, by rfl⟩ : syracuseStep 218879 = 328319) B328319
theorem B220655 : Blo 143792 220655 := bstep (se 1 (by rfl) ⟨165491, by rfl⟩ : syracuseStep 220655 = 330983) B330983
theorem B13721237 : Blo 143792 13721237 := bstep (se 6 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 13721237 = 643183) B643183
theorem B848839 : Blo 143792 848839 := bstep (se 1 (by rfl) ⟨636629, by rfl⟩ : syracuseStep 848839 = 1273259) B1273259
theorem B1668271 : Blo 143792 1668271 := bstep (se 1 (by rfl) ⟨1251203, by rfl⟩ : syracuseStep 1668271 = 2502407) B2502407
theorem B325151 : Blo 143792 325151 := bstep (se 1 (by rfl) ⟨243863, by rfl⟩ : syracuseStep 325151 = 487727) B487727
theorem B325241 : Blo 143792 325241 := bstep (se 2 (by rfl) ⟨121965, by rfl⟩ : syracuseStep 325241 = 243931) B243931
theorem B162535 : Blo 143792 162535 := bstep (se 1 (by rfl) ⟨121901, by rfl⟩ : syracuseStep 162535 = 243803) B243803
theorem B165631 : Blo 143792 165631 := bstep (se 1 (by rfl) ⟨124223, by rfl⟩ : syracuseStep 165631 = 248447) B248447
theorem B329723 : Blo 143792 329723 := bstep (se 1 (by rfl) ⟨247292, by rfl⟩ : syracuseStep 329723 = 494585) B494585
theorem B494747 : Blo 143792 494747 := bstep (se 1 (by rfl) ⟨371060, by rfl⟩ : syracuseStep 494747 = 742121) B742121
theorem B331049 : Blo 143792 331049 := bstep (se 2 (by rfl) ⟨124143, by rfl⟩ : syracuseStep 331049 = 248287) B248287
theorem B331055 : Blo 143792 331055 := bstep (se 1 (by rfl) ⟨248291, by rfl⟩ : syracuseStep 331055 = 496583) B496583
theorem B560783 : Blo 143792 560783 := bstep (se 1 (by rfl) ⟨420587, by rfl⟩ : syracuseStep 560783 = 841175) B841175
theorem B9147491 : Blo 143792 9147491 := bstep (se 1 (by rfl) ⟨6860618, by rfl⟩ : syracuseStep 9147491 = 13721237) B13721237
theorem B3944551 : Blo 143792 3944551 := bstep (se 1 (by rfl) ⟨2958413, by rfl⟩ : syracuseStep 3944551 = 5916827) B5916827
theorem B144711 : Blo 143792 144711 := bstep (se 1 (by rfl) ⟨108533, by rfl⟩ : syracuseStep 144711 = 217067) B217067
theorem B145919 : Blo 143792 145919 := bstep (se 1 (by rfl) ⟨109439, by rfl⟩ : syracuseStep 145919 = 218879) B218879
theorem B147103 : Blo 143792 147103 := bstep (se 1 (by rfl) ⟨110327, by rfl⟩ : syracuseStep 147103 = 220655) B220655
theorem B1131785 : Blo 143792 1131785 := bstep (se 2 (by rfl) ⟨424419, by rfl⟩ : syracuseStep 1131785 = 848839) B848839
theorem B968759 : Blo 143792 968759 := bstep (se 1 (by rfl) ⟨726569, by rfl⟩ : syracuseStep 968759 = 1453139) B1453139
theorem B216713 : Blo 143792 216713 := bstep (se 2 (by rfl) ⟨81267, by rfl⟩ : syracuseStep 216713 = 162535) B162535
theorem B216767 : Blo 143792 216767 := bstep (se 1 (by rfl) ⟨162575, by rfl⟩ : syracuseStep 216767 = 325151) B325151
theorem B216827 : Blo 143792 216827 := bstep (se 1 (by rfl) ⟨162620, by rfl⟩ : syracuseStep 216827 = 325241) B325241
theorem B218831 : Blo 143792 218831 := bstep (se 1 (by rfl) ⟨164123, by rfl⟩ : syracuseStep 218831 = 328247) B328247
theorem B186619 : Blo 143792 186619 := bstep (se 1 (by rfl) ⟨139964, by rfl⟩ : syracuseStep 186619 = 279929) B279929
theorem B219803 : Blo 143792 219803 := bstep (se 1 (by rfl) ⟨164852, by rfl⟩ : syracuseStep 219803 = 329705) B329705
theorem B2515049 : Blo 143792 2515049 := bstep (se 2 (by rfl) ⟨943143, by rfl⟩ : syracuseStep 2515049 = 1886287) B1886287
theorem B2224361 : Blo 143792 2224361 := bstep (se 2 (by rfl) ⟨834135, by rfl⟩ : syracuseStep 2224361 = 1668271) B1668271
theorem B3766013 : Blo 143792 3766013 := bstep (se 3 (by rfl) ⟨706127, by rfl⟩ : syracuseStep 3766013 = 1412255) B1412255
theorem B754523 : Blo 143792 754523 := bstep (se 1 (by rfl) ⟨565892, by rfl⟩ : syracuseStep 754523 = 1131785) B1131785
theorem B329831 : Blo 143792 329831 := bstep (se 1 (by rfl) ⟨247373, by rfl⟩ : syracuseStep 329831 = 494747) B494747
theorem B6098327 : Blo 143792 6098327 := bstep (se 1 (by rfl) ⟨4573745, by rfl⟩ : syracuseStep 6098327 = 9147491) B9147491
theorem B1676699 : Blo 143792 1676699 := bstep (se 1 (by rfl) ⟨1257524, by rfl⟩ : syracuseStep 1676699 = 2515049) B2515049
theorem B1482907 : Blo 143792 1482907 := bstep (se 1 (by rfl) ⟨1112180, by rfl⟩ : syracuseStep 1482907 = 2224361) B2224361
theorem B144475 : Blo 143792 144475 := bstep (se 1 (by rfl) ⟨108356, by rfl⟩ : syracuseStep 144475 = 216713) B216713
theorem B373855 : Blo 143792 373855 := bstep (se 1 (by rfl) ⟨280391, by rfl⟩ : syracuseStep 373855 = 560783) B560783
theorem B144511 : Blo 143792 144511 := bstep (se 1 (by rfl) ⟨108383, by rfl⟩ : syracuseStep 144511 = 216767) B216767
theorem B144551 : Blo 143792 144551 := bstep (se 1 (by rfl) ⟨108413, by rfl⟩ : syracuseStep 144551 = 216827) B216827
theorem B145887 : Blo 143792 145887 := bstep (se 1 (by rfl) ⟨109415, by rfl⟩ : syracuseStep 145887 = 218831) B218831
theorem B146535 : Blo 143792 146535 := bstep (se 1 (by rfl) ⟨109901, by rfl⟩ : syracuseStep 146535 = 219803) B219803
theorem B5259401 : Blo 143792 5259401 := bstep (se 2 (by rfl) ⟨1972275, by rfl⟩ : syracuseStep 5259401 = 3944551) B3944551
theorem B248825 : Blo 143792 248825 := bstep (se 2 (by rfl) ⟨93309, by rfl⟩ : syracuseStep 248825 = 186619) B186619
theorem B2510675 : Blo 143792 2510675 := bstep (se 1 (by rfl) ⟨1883006, by rfl⟩ : syracuseStep 2510675 = 3766013) B3766013
theorem B219815 : Blo 143792 219815 := bstep (se 1 (by rfl) ⟨164861, by rfl⟩ : syracuseStep 219815 = 329723) B329723
theorem B645839 : Blo 143792 645839 := bstep (se 1 (by rfl) ⟨484379, by rfl⟩ : syracuseStep 645839 = 968759) B968759
theorem B220699 : Blo 143792 220699 := bstep (se 1 (by rfl) ⟨165524, by rfl⟩ : syracuseStep 220699 = 331049) B331049
theorem B220703 : Blo 143792 220703 := bstep (se 1 (by rfl) ⟨165527, by rfl⟩ : syracuseStep 220703 = 331055) B331055
theorem B220841 : Blo 143792 220841 := bstep (se 2 (by rfl) ⟨82815, by rfl⟩ : syracuseStep 220841 = 165631) B165631
theorem B3506267 : Blo 143792 3506267 := bstep (se 1 (by rfl) ⟨2629700, by rfl⟩ : syracuseStep 3506267 = 5259401) B5259401
theorem B165883 : Blo 143792 165883 := bstep (se 1 (by rfl) ⟨124412, by rfl⟩ : syracuseStep 165883 = 248825) B248825
theorem B4065551 : Blo 143792 4065551 := bstep (se 1 (by rfl) ⟨3049163, by rfl⟩ : syracuseStep 4065551 = 6098327) B6098327
theorem B1673783 : Blo 143792 1673783 := bstep (se 1 (by rfl) ⟨1255337, by rfl⟩ : syracuseStep 1673783 = 2510675) B2510675
theorem B1117799 : Blo 143792 1117799 := bstep (se 1 (by rfl) ⟨838349, by rfl⟩ : syracuseStep 1117799 = 1676699) B1676699
theorem B430559 : Blo 143792 430559 := bstep (se 1 (by rfl) ⟨322919, by rfl⟩ : syracuseStep 430559 = 645839) B645839
theorem B498473 : Blo 143792 498473 := bstep (se 2 (by rfl) ⟨186927, by rfl⟩ : syracuseStep 498473 = 373855) B373855
theorem B1977209 : Blo 143792 1977209 := bstep (se 2 (by rfl) ⟨741453, by rfl⟩ : syracuseStep 1977209 = 1482907) B1482907
theorem B503015 : Blo 143792 503015 := bstep (se 1 (by rfl) ⟨377261, by rfl⟩ : syracuseStep 503015 = 754523) B754523
theorem B146543 : Blo 143792 146543 := bstep (se 1 (by rfl) ⟨109907, by rfl⟩ : syracuseStep 146543 = 219815) B219815
theorem B147135 : Blo 143792 147135 := bstep (se 1 (by rfl) ⟨110351, by rfl⟩ : syracuseStep 147135 = 220703) B220703
theorem B147227 : Blo 143792 147227 := bstep (se 1 (by rfl) ⟨110420, by rfl⟩ : syracuseStep 147227 = 220841) B220841
theorem B219887 : Blo 143792 219887 := bstep (se 1 (by rfl) ⟨164915, by rfl⟩ : syracuseStep 219887 = 329831) B329831
theorem B294265 : Blo 143792 294265 := bstep (se 2 (by rfl) ⟨110349, by rfl⟩ : syracuseStep 294265 = 220699) B220699
theorem B1115855 : Blo 143792 1115855 := bstep (se 1 (by rfl) ⟨836891, by rfl⟩ : syracuseStep 1115855 = 1673783) B1673783
theorem B332315 : Blo 143792 332315 := bstep (se 1 (by rfl) ⟨249236, by rfl⟩ : syracuseStep 332315 = 498473) B498473
theorem B1318139 : Blo 143792 1318139 := bstep (se 1 (by rfl) ⟨988604, by rfl⟩ : syracuseStep 1318139 = 1977209) B1977209
theorem B2337511 : Blo 143792 2337511 := bstep (se 1 (by rfl) ⟨1753133, by rfl⟩ : syracuseStep 2337511 = 3506267) B3506267
theorem B146591 : Blo 143792 146591 := bstep (se 1 (by rfl) ⟨109943, by rfl⟩ : syracuseStep 146591 = 219887) B219887
theorem B2710367 : Blo 143792 2710367 := bstep (se 1 (by rfl) ⟨2032775, by rfl⟩ : syracuseStep 2710367 = 4065551) B4065551
theorem B745199 : Blo 143792 745199 := bstep (se 1 (by rfl) ⟨558899, by rfl⟩ : syracuseStep 745199 = 1117799) B1117799
theorem B221177 : Blo 143792 221177 := bstep (se 2 (by rfl) ⟨82941, by rfl⟩ : syracuseStep 221177 = 165883) B165883
theorem B287039 : Blo 143792 287039 := bstep (se 1 (by rfl) ⟨215279, by rfl⟩ : syracuseStep 287039 = 430559) B430559
theorem B1341373 : Blo 143792 1341373 := bstep (se 3 (by rfl) ⟨251507, by rfl⟩ : syracuseStep 1341373 = 503015) B503015
theorem B392353 : Blo 143792 392353 := bstep (se 2 (by rfl) ⟨147132, by rfl⟩ : syracuseStep 392353 = 294265) B294265
theorem B3116681 : Blo 143792 3116681 := bstep (se 2 (by rfl) ⟨1168755, by rfl⟩ : syracuseStep 3116681 = 2337511) B2337511
theorem B1806911 : Blo 143792 1806911 := bstep (se 1 (by rfl) ⟨1355183, by rfl⟩ : syracuseStep 1806911 = 2710367) B2710367
theorem B496799 : Blo 143792 496799 := bstep (se 1 (by rfl) ⟨372599, by rfl⟩ : syracuseStep 496799 = 745199) B745199
theorem B147451 : Blo 143792 147451 := bstep (se 1 (by rfl) ⟨110588, by rfl⟩ : syracuseStep 147451 = 221177) B221177
theorem B1788497 : Blo 143792 1788497 := bstep (se 2 (by rfl) ⟨670686, by rfl⟩ : syracuseStep 1788497 = 1341373) B1341373
theorem B743903 : Blo 143792 743903 := bstep (se 1 (by rfl) ⟨557927, by rfl⟩ : syracuseStep 743903 = 1115855) B1115855
theorem B221543 : Blo 143792 221543 := bstep (se 1 (by rfl) ⟨166157, by rfl⟩ : syracuseStep 221543 = 332315) B332315
theorem B878759 : Blo 143792 878759 := bstep (se 1 (by rfl) ⟨659069, by rfl⟩ : syracuseStep 878759 = 1318139) B1318139
theorem B191359 : Blo 143792 191359 := bstep (se 1 (by rfl) ⟨143519, by rfl⟩ : syracuseStep 191359 = 287039) B287039
theorem B2092549 : Blo 143792 2092549 := bstep (se 4 (by rfl) ⟨196176, by rfl⟩ : syracuseStep 2092549 = 392353) B392353
theorem B331199 : Blo 143792 331199 := bstep (se 1 (by rfl) ⟨248399, by rfl⟩ : syracuseStep 331199 = 496799) B496799
theorem B495935 : Blo 143792 495935 := bstep (se 1 (by rfl) ⟨371951, by rfl⟩ : syracuseStep 495935 = 743903) B743903
theorem B2790065 : Blo 143792 2790065 := bstep (se 2 (by rfl) ⟨1046274, by rfl⟩ : syracuseStep 2790065 = 2092549) B2092549
theorem B1192331 : Blo 143792 1192331 := bstep (se 1 (by rfl) ⟨894248, by rfl⟩ : syracuseStep 1192331 = 1788497) B1788497
theorem B2077787 : Blo 143792 2077787 := bstep (se 1 (by rfl) ⟨1558340, by rfl⟩ : syracuseStep 2077787 = 3116681) B3116681
theorem B147695 : Blo 143792 147695 := bstep (se 1 (by rfl) ⟨110771, by rfl⟩ : syracuseStep 147695 = 221543) B221543
theorem B1204607 : Blo 143792 1204607 := bstep (se 1 (by rfl) ⟨903455, by rfl⟩ : syracuseStep 1204607 = 1806911) B1806911
theorem B255145 : Blo 143792 255145 := bstep (se 2 (by rfl) ⟨95679, by rfl⟩ : syracuseStep 255145 = 191359) B191359
theorem B585839 : Blo 143792 585839 := bstep (se 1 (by rfl) ⟨439379, by rfl⟩ : syracuseStep 585839 = 878759) B878759
theorem B330623 : Blo 143792 330623 := bstep (se 1 (by rfl) ⟨247967, by rfl⟩ : syracuseStep 330623 = 495935) B495935
theorem B794887 : Blo 143792 794887 := bstep (se 1 (by rfl) ⟨596165, by rfl⟩ : syracuseStep 794887 = 1192331) B1192331
theorem B1385191 : Blo 143792 1385191 := bstep (se 1 (by rfl) ⟨1038893, by rfl⟩ : syracuseStep 1385191 = 2077787) B2077787
theorem B340193 : Blo 143792 340193 := bstep (se 2 (by rfl) ⟨127572, by rfl⟩ : syracuseStep 340193 = 255145) B255145
theorem B803071 : Blo 143792 803071 := bstep (se 1 (by rfl) ⟨602303, by rfl⟩ : syracuseStep 803071 = 1204607) B1204607
theorem B1562237 : Blo 143792 1562237 := bstep (se 3 (by rfl) ⟨292919, by rfl⟩ : syracuseStep 1562237 = 585839) B585839
theorem B220799 : Blo 143792 220799 := bstep (se 1 (by rfl) ⟨165599, by rfl⟩ : syracuseStep 220799 = 331199) B331199
theorem B1860043 : Blo 143792 1860043 := bstep (se 1 (by rfl) ⟨1395032, by rfl⟩ : syracuseStep 1860043 = 2790065) B2790065
theorem B1846921 : Blo 143792 1846921 := bstep (se 2 (by rfl) ⟨692595, by rfl⟩ : syracuseStep 1846921 = 1385191) B1385191
theorem B4239397 : Blo 143792 4239397 := bstep (se 4 (by rfl) ⟨397443, by rfl⟩ : syracuseStep 4239397 = 794887) B794887
theorem B147199 : Blo 143792 147199 := bstep (se 1 (by rfl) ⟨110399, by rfl⟩ : syracuseStep 147199 = 220799) B220799
theorem B1070761 : Blo 143792 1070761 := bstep (se 2 (by rfl) ⟨401535, by rfl⟩ : syracuseStep 1070761 = 803071) B803071
theorem B2480057 : Blo 143792 2480057 := bstep (se 2 (by rfl) ⟨930021, by rfl⟩ : syracuseStep 2480057 = 1860043) B1860043
theorem B220415 : Blo 143792 220415 := bstep (se 1 (by rfl) ⟨165311, by rfl⟩ : syracuseStep 220415 = 330623) B330623
theorem B1041491 : Blo 143792 1041491 := bstep (se 1 (by rfl) ⟨781118, by rfl⟩ : syracuseStep 1041491 = 1562237) B1562237
theorem B226795 : Blo 143792 226795 := bstep (se 1 (by rfl) ⟨170096, by rfl⟩ : syracuseStep 226795 = 340193) B340193
theorem B22610117 : Blo 143792 22610117 := bstep (se 4 (by rfl) ⟨2119698, by rfl⟩ : syracuseStep 22610117 = 4239397) B4239397
theorem B2462561 : Blo 143792 2462561 := bstep (se 2 (by rfl) ⟨923460, by rfl⟩ : syracuseStep 2462561 = 1846921) B1846921
theorem B694327 : Blo 143792 694327 := bstep (se 1 (by rfl) ⟨520745, by rfl⟩ : syracuseStep 694327 = 1041491) B1041491
theorem B302393 : Blo 143792 302393 := bstep (se 2 (by rfl) ⟨113397, by rfl⟩ : syracuseStep 302393 = 226795) B226795
theorem B1653371 : Blo 143792 1653371 := bstep (se 1 (by rfl) ⟨1240028, by rfl⟩ : syracuseStep 1653371 = 2480057) B2480057
theorem B146943 : Blo 143792 146943 := bstep (se 1 (by rfl) ⟨110207, by rfl⟩ : syracuseStep 146943 = 220415) B220415
theorem B1427681 : Blo 143792 1427681 := bstep (se 2 (by rfl) ⟨535380, by rfl⟩ : syracuseStep 1427681 = 1070761) B1070761
theorem B60293645 : Blo 143792 60293645 := bstep (se 3 (by rfl) ⟨11305058, by rfl⟩ : syracuseStep 60293645 = 22610117) B22610117
theorem B951787 : Blo 143792 951787 := bstep (se 1 (by rfl) ⟨713840, by rfl⟩ : syracuseStep 951787 = 1427681) B1427681
theorem B1641707 : Blo 143792 1641707 := bstep (se 1 (by rfl) ⟨1231280, by rfl⟩ : syracuseStep 1641707 = 2462561) B2462561
theorem B925769 : Blo 143792 925769 := bstep (se 2 (by rfl) ⟨347163, by rfl⟩ : syracuseStep 925769 = 694327) B694327
theorem B806381 : Blo 143792 806381 := bstep (se 3 (by rfl) ⟨151196, by rfl⟩ : syracuseStep 806381 = 302393) B302393
theorem B1102247 : Blo 143792 1102247 := bstep (se 1 (by rfl) ⟨826685, by rfl⟩ : syracuseStep 1102247 = 1653371) B1653371
theorem B1094471 : Blo 143792 1094471 := bstep (se 1 (by rfl) ⟨820853, by rfl⟩ : syracuseStep 1094471 = 1641707) B1641707
theorem B537587 : Blo 143792 537587 := bstep (se 1 (by rfl) ⟨403190, by rfl⟩ : syracuseStep 537587 = 806381) B806381
theorem B734831 : Blo 143792 734831 := bstep (se 1 (by rfl) ⟨551123, by rfl⟩ : syracuseStep 734831 = 1102247) B1102247
theorem B40195763 : Blo 143792 40195763 := bstep (se 1 (by rfl) ⟨30146822, by rfl⟩ : syracuseStep 40195763 = 60293645) B60293645
theorem B1269049 : Blo 143792 1269049 := bstep (se 2 (by rfl) ⟨475893, by rfl⟩ : syracuseStep 1269049 = 951787) B951787
theorem B617179 : Blo 143792 617179 := bstep (se 1 (by rfl) ⟨462884, by rfl⟩ : syracuseStep 617179 = 925769) B925769
theorem B822905 : Blo 143792 822905 := bstep (se 2 (by rfl) ⟨308589, by rfl⟩ : syracuseStep 822905 = 617179) B617179
theorem B729647 : Blo 143792 729647 := bstep (se 1 (by rfl) ⟨547235, by rfl⟩ : syracuseStep 729647 = 1094471) B1094471
theorem B1692065 : Blo 143792 1692065 := bstep (se 2 (by rfl) ⟨634524, by rfl⟩ : syracuseStep 1692065 = 1269049) B1269049
theorem B26797175 : Blo 143792 26797175 := bstep (se 1 (by rfl) ⟨20097881, by rfl⟩ : syracuseStep 26797175 = 40195763) B40195763
theorem B358391 : Blo 143792 358391 := bstep (se 1 (by rfl) ⟨268793, by rfl⟩ : syracuseStep 358391 = 537587) B537587
theorem B489887 : Blo 143792 489887 := bstep (se 1 (by rfl) ⟨367415, by rfl⟩ : syracuseStep 489887 = 734831) B734831
theorem B955709 : Blo 143792 955709 := bstep (se 3 (by rfl) ⟨179195, by rfl⟩ : syracuseStep 955709 = 358391) B358391
theorem B17864783 : Blo 143792 17864783 := bstep (se 1 (by rfl) ⟨13398587, by rfl⟩ : syracuseStep 17864783 = 26797175) B26797175
theorem B1128043 : Blo 143792 1128043 := bstep (se 1 (by rfl) ⟨846032, by rfl⟩ : syracuseStep 1128043 = 1692065) B1692065
theorem B548603 : Blo 143792 548603 := bstep (se 1 (by rfl) ⟨411452, by rfl⟩ : syracuseStep 548603 = 822905) B822905
theorem B486431 : Blo 143792 486431 := bstep (se 1 (by rfl) ⟨364823, by rfl⟩ : syracuseStep 486431 = 729647) B729647
theorem B326591 : Blo 143792 326591 := bstep (se 1 (by rfl) ⟨244943, by rfl⟩ : syracuseStep 326591 = 489887) B489887
theorem B365735 : Blo 143792 365735 := bstep (se 1 (by rfl) ⟨274301, by rfl⟩ : syracuseStep 365735 = 548603) B548603
theorem B637139 : Blo 143792 637139 := bstep (se 1 (by rfl) ⟨477854, by rfl⟩ : syracuseStep 637139 = 955709) B955709
theorem B11909855 : Blo 143792 11909855 := bstep (se 1 (by rfl) ⟨8932391, by rfl⟩ : syracuseStep 11909855 = 17864783) B17864783
theorem B217727 : Blo 143792 217727 := bstep (se 1 (by rfl) ⟨163295, by rfl⟩ : syracuseStep 217727 = 326591) B326591
theorem B324287 : Blo 143792 324287 := bstep (se 1 (by rfl) ⟨243215, by rfl⟩ : syracuseStep 324287 = 486431) B486431
theorem B1504057 : Blo 143792 1504057 := bstep (se 2 (by rfl) ⟨564021, by rfl⟩ : syracuseStep 1504057 = 1128043) B1128043
theorem B2005409 : Blo 143792 2005409 := bstep (se 2 (by rfl) ⟨752028, by rfl⟩ : syracuseStep 2005409 = 1504057) B1504057
theorem B7939903 : Blo 143792 7939903 := bstep (se 1 (by rfl) ⟨5954927, by rfl⟩ : syracuseStep 7939903 = 11909855) B11909855
theorem B145151 : Blo 143792 145151 := bstep (se 1 (by rfl) ⟨108863, by rfl⟩ : syracuseStep 145151 = 217727) B217727
theorem B243823 : Blo 143792 243823 := bstep (se 1 (by rfl) ⟨182867, by rfl⟩ : syracuseStep 243823 = 365735) B365735
theorem B216191 : Blo 143792 216191 := bstep (se 1 (by rfl) ⟨162143, by rfl⟩ : syracuseStep 216191 = 324287) B324287
theorem B424759 : Blo 143792 424759 := bstep (se 1 (by rfl) ⟨318569, by rfl⟩ : syracuseStep 424759 = 637139) B637139
theorem B10586537 : Blo 143792 10586537 := bstep (se 2 (by rfl) ⟨3969951, by rfl⟩ : syracuseStep 10586537 = 7939903) B7939903
theorem B5347757 : Blo 143792 5347757 := bstep (se 3 (by rfl) ⟨1002704, by rfl⟩ : syracuseStep 5347757 = 2005409) B2005409
theorem B566345 : Blo 143792 566345 := bstep (se 2 (by rfl) ⟨212379, by rfl⟩ : syracuseStep 566345 = 424759) B424759
theorem B144127 : Blo 143792 144127 := bstep (se 1 (by rfl) ⟨108095, by rfl⟩ : syracuseStep 144127 = 216191) B216191
theorem B325097 : Blo 143792 325097 := bstep (se 2 (by rfl) ⟨121911, by rfl⟩ : syracuseStep 325097 = 243823) B243823
theorem B7057691 : Blo 143792 7057691 := bstep (se 1 (by rfl) ⟨5293268, by rfl⟩ : syracuseStep 7057691 = 10586537) B10586537
theorem B377563 : Blo 143792 377563 := bstep (se 1 (by rfl) ⟨283172, by rfl⟩ : syracuseStep 377563 = 566345) B566345
theorem B216731 : Blo 143792 216731 := bstep (se 1 (by rfl) ⟨162548, by rfl⟩ : syracuseStep 216731 = 325097) B325097
theorem B3565171 : Blo 143792 3565171 := bstep (se 1 (by rfl) ⟨2673878, by rfl⟩ : syracuseStep 3565171 = 5347757) B5347757
theorem B4753561 : Blo 143792 4753561 := bstep (se 2 (by rfl) ⟨1782585, by rfl⟩ : syracuseStep 4753561 = 3565171) B3565171
theorem B503417 : Blo 143792 503417 := bstep (se 2 (by rfl) ⟨188781, by rfl⟩ : syracuseStep 503417 = 377563) B377563
theorem B144487 : Blo 143792 144487 := bstep (se 1 (by rfl) ⟨108365, by rfl⟩ : syracuseStep 144487 = 216731) B216731
theorem B4705127 : Blo 143792 4705127 := bstep (se 1 (by rfl) ⟨3528845, by rfl⟩ : syracuseStep 4705127 = 7057691) B7057691
theorem B335611 : Blo 143792 335611 := bstep (se 1 (by rfl) ⟨251708, by rfl⟩ : syracuseStep 335611 = 503417) B503417
theorem B6338081 : Blo 143792 6338081 := bstep (se 2 (by rfl) ⟨2376780, by rfl⟩ : syracuseStep 6338081 = 4753561) B4753561
theorem B3136751 : Blo 143792 3136751 := bstep (se 1 (by rfl) ⟨2352563, by rfl⟩ : syracuseStep 3136751 = 4705127) B4705127
theorem B447481 : Blo 143792 447481 := bstep (se 2 (by rfl) ⟨167805, by rfl⟩ : syracuseStep 447481 = 335611) B335611
theorem B2091167 : Blo 143792 2091167 := bstep (se 1 (by rfl) ⟨1568375, by rfl⟩ : syracuseStep 2091167 = 3136751) B3136751
theorem B4225387 : Blo 143792 4225387 := bstep (se 1 (by rfl) ⟨3169040, by rfl⟩ : syracuseStep 4225387 = 6338081) B6338081
theorem B596641 : Blo 143792 596641 := bstep (se 2 (by rfl) ⟨223740, by rfl⟩ : syracuseStep 596641 = 447481) B447481
theorem B1394111 : Blo 143792 1394111 := bstep (se 1 (by rfl) ⟨1045583, by rfl⟩ : syracuseStep 1394111 = 2091167) B2091167
theorem B5633849 : Blo 143792 5633849 := bstep (se 2 (by rfl) ⟨2112693, by rfl⟩ : syracuseStep 5633849 = 4225387) B4225387
theorem B795521 : Blo 143792 795521 := bstep (se 2 (by rfl) ⟨298320, by rfl⟩ : syracuseStep 795521 = 596641) B596641
theorem B929407 : Blo 143792 929407 := bstep (se 1 (by rfl) ⟨697055, by rfl⟩ : syracuseStep 929407 = 1394111) B1394111
theorem B3755899 : Blo 143792 3755899 := bstep (se 1 (by rfl) ⟨2816924, by rfl⟩ : syracuseStep 3755899 = 5633849) B5633849
theorem B2121389 : Blo 143792 2121389 := bstep (se 3 (by rfl) ⟨397760, by rfl⟩ : syracuseStep 2121389 = 795521) B795521
theorem B1239209 : Blo 143792 1239209 := bstep (se 2 (by rfl) ⟨464703, by rfl⟩ : syracuseStep 1239209 = 929407) B929407
theorem B5007865 : Blo 143792 5007865 := bstep (se 2 (by rfl) ⟨1877949, by rfl⟩ : syracuseStep 5007865 = 3755899) B3755899
theorem B1414259 : Blo 143792 1414259 := bstep (se 1 (by rfl) ⟨1060694, by rfl⟩ : syracuseStep 1414259 = 2121389) B2121389
theorem B826139 : Blo 143792 826139 := bstep (se 1 (by rfl) ⟨619604, by rfl⟩ : syracuseStep 826139 = 1239209) B1239209
theorem B6677153 : Blo 143792 6677153 := bstep (se 2 (by rfl) ⟨2503932, by rfl⟩ : syracuseStep 6677153 = 5007865) B5007865
theorem B942839 : Blo 143792 942839 := bstep (se 1 (by rfl) ⟨707129, by rfl⟩ : syracuseStep 942839 = 1414259) B1414259
theorem B550759 : Blo 143792 550759 := bstep (se 1 (by rfl) ⟨413069, by rfl⟩ : syracuseStep 550759 = 826139) B826139
theorem B4451435 : Blo 143792 4451435 := bstep (se 1 (by rfl) ⟨3338576, by rfl⟩ : syracuseStep 4451435 = 6677153) B6677153
theorem B628559 : Blo 143792 628559 := bstep (se 1 (by rfl) ⟨471419, by rfl⟩ : syracuseStep 628559 = 942839) B942839
theorem B734345 : Blo 143792 734345 := bstep (se 2 (by rfl) ⟨275379, by rfl⟩ : syracuseStep 734345 = 550759) B550759
theorem B2967623 : Blo 143792 2967623 := bstep (se 1 (by rfl) ⟨2225717, by rfl⟩ : syracuseStep 2967623 = 4451435) B4451435
theorem B1978415 : Blo 143792 1978415 := bstep (se 1 (by rfl) ⟨1483811, by rfl⟩ : syracuseStep 1978415 = 2967623) B2967623
theorem B419039 : Blo 143792 419039 := bstep (se 1 (by rfl) ⟨314279, by rfl⟩ : syracuseStep 419039 = 628559) B628559
theorem B489563 : Blo 143792 489563 := bstep (se 1 (by rfl) ⟨367172, by rfl⟩ : syracuseStep 489563 = 734345) B734345
theorem B1318943 : Blo 143792 1318943 := bstep (se 1 (by rfl) ⟨989207, by rfl⟩ : syracuseStep 1318943 = 1978415) B1978415
theorem B279359 : Blo 143792 279359 := bstep (se 1 (by rfl) ⟨209519, by rfl⟩ : syracuseStep 279359 = 419039) B419039
theorem B326375 : Blo 143792 326375 := bstep (se 1 (by rfl) ⟨244781, by rfl⟩ : syracuseStep 326375 = 489563) B489563
theorem B217583 : Blo 143792 217583 := bstep (se 1 (by rfl) ⟨163187, by rfl⟩ : syracuseStep 217583 = 326375) B326375
theorem B186239 : Blo 143792 186239 := bstep (se 1 (by rfl) ⟨139679, by rfl⟩ : syracuseStep 186239 = 279359) B279359
theorem B879295 : Blo 143792 879295 := bstep (se 1 (by rfl) ⟨659471, by rfl⟩ : syracuseStep 879295 = 1318943) B1318943
theorem B496637 : Blo 143792 496637 := bstep (se 3 (by rfl) ⟨93119, by rfl⟩ : syracuseStep 496637 = 186239) B186239
theorem B145055 : Blo 143792 145055 := bstep (se 1 (by rfl) ⟨108791, by rfl⟩ : syracuseStep 145055 = 217583) B217583
theorem B1172393 : Blo 143792 1172393 := bstep (se 2 (by rfl) ⟨439647, by rfl⟩ : syracuseStep 1172393 = 879295) B879295
theorem B331091 : Blo 143792 331091 := bstep (se 1 (by rfl) ⟨248318, by rfl⟩ : syracuseStep 331091 = 496637) B496637
theorem B781595 : Blo 143792 781595 := bstep (se 1 (by rfl) ⟨586196, by rfl⟩ : syracuseStep 781595 = 1172393) B1172393
theorem B220727 : Blo 143792 220727 := bstep (se 1 (by rfl) ⟨165545, by rfl⟩ : syracuseStep 220727 = 331091) B331091
theorem B521063 : Blo 143792 521063 := bstep (se 1 (by rfl) ⟨390797, by rfl⟩ : syracuseStep 521063 = 781595) B781595
theorem B147151 : Blo 143792 147151 := bstep (se 1 (by rfl) ⟨110363, by rfl⟩ : syracuseStep 147151 = 220727) B220727
theorem B347375 : Blo 143792 347375 := bstep (se 1 (by rfl) ⟨260531, by rfl⟩ : syracuseStep 347375 = 521063) B521063
theorem B231583 : Blo 143792 231583 := bstep (se 1 (by rfl) ⟨173687, by rfl⟩ : syracuseStep 231583 = 347375) B347375
theorem B308777 : Blo 143792 308777 := bstep (se 2 (by rfl) ⟨115791, by rfl⟩ : syracuseStep 308777 = 231583) B231583
theorem B823405 : Blo 143792 823405 := bstep (se 3 (by rfl) ⟨154388, by rfl⟩ : syracuseStep 823405 = 308777) B308777
theorem B1097873 : Blo 143792 1097873 := bstep (se 2 (by rfl) ⟨411702, by rfl⟩ : syracuseStep 1097873 = 823405) B823405
theorem B731915 : Blo 143792 731915 := bstep (se 1 (by rfl) ⟨548936, by rfl⟩ : syracuseStep 731915 = 1097873) B1097873
theorem B487943 : Blo 143792 487943 := bstep (se 1 (by rfl) ⟨365957, by rfl⟩ : syracuseStep 487943 = 731915) B731915
theorem B325295 : Blo 143792 325295 := bstep (se 1 (by rfl) ⟨243971, by rfl⟩ : syracuseStep 325295 = 487943) B487943
theorem B216863 : Blo 143792 216863 := bstep (se 1 (by rfl) ⟨162647, by rfl⟩ : syracuseStep 216863 = 325295) B325295
theorem B144575 : Blo 143792 144575 := bstep (se 1 (by rfl) ⟨108431, by rfl⟩ : syracuseStep 144575 = 216863) B216863

theorem C0 (j : ℕ) (h1 : 35948 ≤ j) (h2 : j ≤ 36647) : Blo 143792 (4 * j + 3) := by
  interval_cases j
  · exact B143795
  · exact B143799
  · exact B143803
  · exact B143807
  · exact B143811
  · exact B143815
  · exact B143819
  · exact B143823
  · exact B143827
  · exact B143831
  · exact B143835
  · exact B143839
  · exact B143843
  · exact B143847
  · exact B143851
  · exact B143855
  · exact B143859
  · exact B143863
  · exact B143867
  · exact B143871
  · exact B143875
  · exact B143879
  · exact B143883
  · exact B143887
  · exact B143891
  · exact B143895
  · exact B143899
  · exact B143903
  · exact B143907
  · exact B143911
  · exact B143915
  · exact B143919
  · exact B143923
  · exact B143927
  · exact B143931
  · exact B143935
  · exact B143939
  · exact B143943
  · exact B143947
  · exact B143951
  · exact B143955
  · exact B143959
  · exact B143963
  · exact B143967
  · exact B143971
  · exact B143975
  · exact B143979
  · exact B143983
  · exact B143987
  · exact B143991
  · exact B143995
  · exact B143999
  · exact B144003
  · exact B144007
  · exact B144011
  · exact B144015
  · exact B144019
  · exact B144023
  · exact B144027
  · exact B144031
  · exact B144035
  · exact B144039
  · exact B144043
  · exact B144047
  · exact B144051
  · exact B144055
  · exact B144059
  · exact B144063
  · exact B144067
  · exact B144071
  · exact B144075
  · exact B144079
  · exact B144083
  · exact B144087
  · exact B144091
  · exact B144095
  · exact B144099
  · exact B144103
  · exact B144107
  · exact B144111
  · exact B144115
  · exact B144119
  · exact B144123
  · exact B144127
  · exact B144131
  · exact B144135
  · exact B144139
  · exact B144143
  · exact B144147
  · exact B144151
  · exact B144155
  · exact B144159
  · exact B144163
  · exact B144167
  · exact B144171
  · exact B144175
  · exact B144179
  · exact B144183
  · exact B144187
  · exact B144191
  · exact B144195
  · exact B144199
  · exact B144203
  · exact B144207
  · exact B144211
  · exact B144215
  · exact B144219
  · exact B144223
  · exact B144227
  · exact B144231
  · exact B144235
  · exact B144239
  · exact B144243
  · exact B144247
  · exact B144251
  · exact B144255
  · exact B144259
  · exact B144263
  · exact B144267
  · exact B144271
  · exact B144275
  · exact B144279
  · exact B144283
  · exact B144287
  · exact B144291
  · exact B144295
  · exact B144299
  · exact B144303
  · exact B144307
  · exact B144311
  · exact B144315
  · exact B144319
  · exact B144323
  · exact B144327
  · exact B144331
  · exact B144335
  · exact B144339
  · exact B144343
  · exact B144347
  · exact B144351
  · exact B144355
  · exact B144359
  · exact B144363
  · exact B144367
  · exact B144371
  · exact B144375
  · exact B144379
  · exact B144383
  · exact B144387
  · exact B144391
  · exact B144395
  · exact B144399
  · exact B144403
  · exact B144407
  · exact B144411
  · exact B144415
  · exact B144419
  · exact B144423
  · exact B144427
  · exact B144431
  · exact B144435
  · exact B144439
  · exact B144443
  · exact B144447
  · exact B144451
  · exact B144455
  · exact B144459
  · exact B144463
  · exact B144467
  · exact B144471
  · exact B144475
  · exact B144479
  · exact B144483
  · exact B144487
  · exact B144491
  · exact B144495
  · exact B144499
  · exact B144503
  · exact B144507
  · exact B144511
  · exact B144515
  · exact B144519
  · exact B144523
  · exact B144527
  · exact B144531
  · exact B144535
  · exact B144539
  · exact B144543
  · exact B144547
  · exact B144551
  · exact B144555
  · exact B144559
  · exact B144563
  · exact B144567
  · exact B144571
  · exact B144575
  · exact B144579
  · exact B144583
  · exact B144587
  · exact B144591
  · exact B144595
  · exact B144599
  · exact B144603
  · exact B144607
  · exact B144611
  · exact B144615
  · exact B144619
  · exact B144623
  · exact B144627
  · exact B144631
  · exact B144635
  · exact B144639
  · exact B144643
  · exact B144647
  · exact B144651
  · exact B144655
  · exact B144659
  · exact B144663
  · exact B144667
  · exact B144671
  · exact B144675
  · exact B144679
  · exact B144683
  · exact B144687
  · exact B144691
  · exact B144695
  · exact B144699
  · exact B144703
  · exact B144707
  · exact B144711
  · exact B144715
  · exact B144719
  · exact B144723
  · exact B144727
  · exact B144731
  · exact B144735
  · exact B144739
  · exact B144743
  · exact B144747
  · exact B144751
  · exact B144755
  · exact B144759
  · exact B144763
  · exact B144767
  · exact B144771
  · exact B144775
  · exact B144779
  · exact B144783
  · exact B144787
  · exact B144791
  · exact B144795
  · exact B144799
  · exact B144803
  · exact B144807
  · exact B144811
  · exact B144815
  · exact B144819
  · exact B144823
  · exact B144827
  · exact B144831
  · exact B144835
  · exact B144839
  · exact B144843
  · exact B144847
  · exact B144851
  · exact B144855
  · exact B144859
  · exact B144863
  · exact B144867
  · exact B144871
  · exact B144875
  · exact B144879
  · exact B144883
  · exact B144887
  · exact B144891
  · exact B144895
  · exact B144899
  · exact B144903
  · exact B144907
  · exact B144911
  · exact B144915
  · exact B144919
  · exact B144923
  · exact B144927
  · exact B144931
  · exact B144935
  · exact B144939
  · exact B144943
  · exact B144947
  · exact B144951
  · exact B144955
  · exact B144959
  · exact B144963
  · exact B144967
  · exact B144971
  · exact B144975
  · exact B144979
  · exact B144983
  · exact B144987
  · exact B144991
  · exact B144995
  · exact B144999
  · exact B145003
  · exact B145007
  · exact B145011
  · exact B145015
  · exact B145019
  · exact B145023
  · exact B145027
  · exact B145031
  · exact B145035
  · exact B145039
  · exact B145043
  · exact B145047
  · exact B145051
  · exact B145055
  · exact B145059
  · exact B145063
  · exact B145067
  · exact B145071
  · exact B145075
  · exact B145079
  · exact B145083
  · exact B145087
  · exact B145091
  · exact B145095
  · exact B145099
  · exact B145103
  · exact B145107
  · exact B145111
  · exact B145115
  · exact B145119
  · exact B145123
  · exact B145127
  · exact B145131
  · exact B145135
  · exact B145139
  · exact B145143
  · exact B145147
  · exact B145151
  · exact B145155
  · exact B145159
  · exact B145163
  · exact B145167
  · exact B145171
  · exact B145175
  · exact B145179
  · exact B145183
  · exact B145187
  · exact B145191
  · exact B145195
  · exact B145199
  · exact B145203
  · exact B145207
  · exact B145211
  · exact B145215
  · exact B145219
  · exact B145223
  · exact B145227
  · exact B145231
  · exact B145235
  · exact B145239
  · exact B145243
  · exact B145247
  · exact B145251
  · exact B145255
  · exact B145259
  · exact B145263
  · exact B145267
  · exact B145271
  · exact B145275
  · exact B145279
  · exact B145283
  · exact B145287
  · exact B145291
  · exact B145295
  · exact B145299
  · exact B145303
  · exact B145307
  · exact B145311
  · exact B145315
  · exact B145319
  · exact B145323
  · exact B145327
  · exact B145331
  · exact B145335
  · exact B145339
  · exact B145343
  · exact B145347
  · exact B145351
  · exact B145355
  · exact B145359
  · exact B145363
  · exact B145367
  · exact B145371
  · exact B145375
  · exact B145379
  · exact B145383
  · exact B145387
  · exact B145391
  · exact B145395
  · exact B145399
  · exact B145403
  · exact B145407
  · exact B145411
  · exact B145415
  · exact B145419
  · exact B145423
  · exact B145427
  · exact B145431
  · exact B145435
  · exact B145439
  · exact B145443
  · exact B145447
  · exact B145451
  · exact B145455
  · exact B145459
  · exact B145463
  · exact B145467
  · exact B145471
  · exact B145475
  · exact B145479
  · exact B145483
  · exact B145487
  · exact B145491
  · exact B145495
  · exact B145499
  · exact B145503
  · exact B145507
  · exact B145511
  · exact B145515
  · exact B145519
  · exact B145523
  · exact B145527
  · exact B145531
  · exact B145535
  · exact B145539
  · exact B145543
  · exact B145547
  · exact B145551
  · exact B145555
  · exact B145559
  · exact B145563
  · exact B145567
  · exact B145571
  · exact B145575
  · exact B145579
  · exact B145583
  · exact B145587
  · exact B145591
  · exact B145595
  · exact B145599
  · exact B145603
  · exact B145607
  · exact B145611
  · exact B145615
  · exact B145619
  · exact B145623
  · exact B145627
  · exact B145631
  · exact B145635
  · exact B145639
  · exact B145643
  · exact B145647
  · exact B145651
  · exact B145655
  · exact B145659
  · exact B145663
  · exact B145667
  · exact B145671
  · exact B145675
  · exact B145679
  · exact B145683
  · exact B145687
  · exact B145691
  · exact B145695
  · exact B145699
  · exact B145703
  · exact B145707
  · exact B145711
  · exact B145715
  · exact B145719
  · exact B145723
  · exact B145727
  · exact B145731
  · exact B145735
  · exact B145739
  · exact B145743
  · exact B145747
  · exact B145751
  · exact B145755
  · exact B145759
  · exact B145763
  · exact B145767
  · exact B145771
  · exact B145775
  · exact B145779
  · exact B145783
  · exact B145787
  · exact B145791
  · exact B145795
  · exact B145799
  · exact B145803
  · exact B145807
  · exact B145811
  · exact B145815
  · exact B145819
  · exact B145823
  · exact B145827
  · exact B145831
  · exact B145835
  · exact B145839
  · exact B145843
  · exact B145847
  · exact B145851
  · exact B145855
  · exact B145859
  · exact B145863
  · exact B145867
  · exact B145871
  · exact B145875
  · exact B145879
  · exact B145883
  · exact B145887
  · exact B145891
  · exact B145895
  · exact B145899
  · exact B145903
  · exact B145907
  · exact B145911
  · exact B145915
  · exact B145919
  · exact B145923
  · exact B145927
  · exact B145931
  · exact B145935
  · exact B145939
  · exact B145943
  · exact B145947
  · exact B145951
  · exact B145955
  · exact B145959
  · exact B145963
  · exact B145967
  · exact B145971
  · exact B145975
  · exact B145979
  · exact B145983
  · exact B145987
  · exact B145991
  · exact B145995
  · exact B145999
  · exact B146003
  · exact B146007
  · exact B146011
  · exact B146015
  · exact B146019
  · exact B146023
  · exact B146027
  · exact B146031
  · exact B146035
  · exact B146039
  · exact B146043
  · exact B146047
  · exact B146051
  · exact B146055
  · exact B146059
  · exact B146063
  · exact B146067
  · exact B146071
  · exact B146075
  · exact B146079
  · exact B146083
  · exact B146087
  · exact B146091
  · exact B146095
  · exact B146099
  · exact B146103
  · exact B146107
  · exact B146111
  · exact B146115
  · exact B146119
  · exact B146123
  · exact B146127
  · exact B146131
  · exact B146135
  · exact B146139
  · exact B146143
  · exact B146147
  · exact B146151
  · exact B146155
  · exact B146159
  · exact B146163
  · exact B146167
  · exact B146171
  · exact B146175
  · exact B146179
  · exact B146183
  · exact B146187
  · exact B146191
  · exact B146195
  · exact B146199
  · exact B146203
  · exact B146207
  · exact B146211
  · exact B146215
  · exact B146219
  · exact B146223
  · exact B146227
  · exact B146231
  · exact B146235
  · exact B146239
  · exact B146243
  · exact B146247
  · exact B146251
  · exact B146255
  · exact B146259
  · exact B146263
  · exact B146267
  · exact B146271
  · exact B146275
  · exact B146279
  · exact B146283
  · exact B146287
  · exact B146291
  · exact B146295
  · exact B146299
  · exact B146303
  · exact B146307
  · exact B146311
  · exact B146315
  · exact B146319
  · exact B146323
  · exact B146327
  · exact B146331
  · exact B146335
  · exact B146339
  · exact B146343
  · exact B146347
  · exact B146351
  · exact B146355
  · exact B146359
  · exact B146363
  · exact B146367
  · exact B146371
  · exact B146375
  · exact B146379
  · exact B146383
  · exact B146387
  · exact B146391
  · exact B146395
  · exact B146399
  · exact B146403
  · exact B146407
  · exact B146411
  · exact B146415
  · exact B146419
  · exact B146423
  · exact B146427
  · exact B146431
  · exact B146435
  · exact B146439
  · exact B146443
  · exact B146447
  · exact B146451
  · exact B146455
  · exact B146459
  · exact B146463
  · exact B146467
  · exact B146471
  · exact B146475
  · exact B146479
  · exact B146483
  · exact B146487
  · exact B146491
  · exact B146495
  · exact B146499
  · exact B146503
  · exact B146507
  · exact B146511
  · exact B146515
  · exact B146519
  · exact B146523
  · exact B146527
  · exact B146531
  · exact B146535
  · exact B146539
  · exact B146543
  · exact B146547
  · exact B146551
  · exact B146555
  · exact B146559
  · exact B146563
  · exact B146567
  · exact B146571
  · exact B146575
  · exact B146579
  · exact B146583
  · exact B146587
  · exact B146591

theorem C1 (j : ℕ) (h1 : 36648 ≤ j) (h2 : j ≤ 36947) : Blo 143792 (4 * j + 3) := by
  interval_cases j
  · exact B146595
  · exact B146599
  · exact B146603
  · exact B146607
  · exact B146611
  · exact B146615
  · exact B146619
  · exact B146623
  · exact B146627
  · exact B146631
  · exact B146635
  · exact B146639
  · exact B146643
  · exact B146647
  · exact B146651
  · exact B146655
  · exact B146659
  · exact B146663
  · exact B146667
  · exact B146671
  · exact B146675
  · exact B146679
  · exact B146683
  · exact B146687
  · exact B146691
  · exact B146695
  · exact B146699
  · exact B146703
  · exact B146707
  · exact B146711
  · exact B146715
  · exact B146719
  · exact B146723
  · exact B146727
  · exact B146731
  · exact B146735
  · exact B146739
  · exact B146743
  · exact B146747
  · exact B146751
  · exact B146755
  · exact B146759
  · exact B146763
  · exact B146767
  · exact B146771
  · exact B146775
  · exact B146779
  · exact B146783
  · exact B146787
  · exact B146791
  · exact B146795
  · exact B146799
  · exact B146803
  · exact B146807
  · exact B146811
  · exact B146815
  · exact B146819
  · exact B146823
  · exact B146827
  · exact B146831
  · exact B146835
  · exact B146839
  · exact B146843
  · exact B146847
  · exact B146851
  · exact B146855
  · exact B146859
  · exact B146863
  · exact B146867
  · exact B146871
  · exact B146875
  · exact B146879
  · exact B146883
  · exact B146887
  · exact B146891
  · exact B146895
  · exact B146899
  · exact B146903
  · exact B146907
  · exact B146911
  · exact B146915
  · exact B146919
  · exact B146923
  · exact B146927
  · exact B146931
  · exact B146935
  · exact B146939
  · exact B146943
  · exact B146947
  · exact B146951
  · exact B146955
  · exact B146959
  · exact B146963
  · exact B146967
  · exact B146971
  · exact B146975
  · exact B146979
  · exact B146983
  · exact B146987
  · exact B146991
  · exact B146995
  · exact B146999
  · exact B147003
  · exact B147007
  · exact B147011
  · exact B147015
  · exact B147019
  · exact B147023
  · exact B147027
  · exact B147031
  · exact B147035
  · exact B147039
  · exact B147043
  · exact B147047
  · exact B147051
  · exact B147055
  · exact B147059
  · exact B147063
  · exact B147067
  · exact B147071
  · exact B147075
  · exact B147079
  · exact B147083
  · exact B147087
  · exact B147091
  · exact B147095
  · exact B147099
  · exact B147103
  · exact B147107
  · exact B147111
  · exact B147115
  · exact B147119
  · exact B147123
  · exact B147127
  · exact B147131
  · exact B147135
  · exact B147139
  · exact B147143
  · exact B147147
  · exact B147151
  · exact B147155
  · exact B147159
  · exact B147163
  · exact B147167
  · exact B147171
  · exact B147175
  · exact B147179
  · exact B147183
  · exact B147187
  · exact B147191
  · exact B147195
  · exact B147199
  · exact B147203
  · exact B147207
  · exact B147211
  · exact B147215
  · exact B147219
  · exact B147223
  · exact B147227
  · exact B147231
  · exact B147235
  · exact B147239
  · exact B147243
  · exact B147247
  · exact B147251
  · exact B147255
  · exact B147259
  · exact B147263
  · exact B147267
  · exact B147271
  · exact B147275
  · exact B147279
  · exact B147283
  · exact B147287
  · exact B147291
  · exact B147295
  · exact B147299
  · exact B147303
  · exact B147307
  · exact B147311
  · exact B147315
  · exact B147319
  · exact B147323
  · exact B147327
  · exact B147331
  · exact B147335
  · exact B147339
  · exact B147343
  · exact B147347
  · exact B147351
  · exact B147355
  · exact B147359
  · exact B147363
  · exact B147367
  · exact B147371
  · exact B147375
  · exact B147379
  · exact B147383
  · exact B147387
  · exact B147391
  · exact B147395
  · exact B147399
  · exact B147403
  · exact B147407
  · exact B147411
  · exact B147415
  · exact B147419
  · exact B147423
  · exact B147427
  · exact B147431
  · exact B147435
  · exact B147439
  · exact B147443
  · exact B147447
  · exact B147451
  · exact B147455
  · exact B147459
  · exact B147463
  · exact B147467
  · exact B147471
  · exact B147475
  · exact B147479
  · exact B147483
  · exact B147487
  · exact B147491
  · exact B147495
  · exact B147499
  · exact B147503
  · exact B147507
  · exact B147511
  · exact B147515
  · exact B147519
  · exact B147523
  · exact B147527
  · exact B147531
  · exact B147535
  · exact B147539
  · exact B147543
  · exact B147547
  · exact B147551
  · exact B147555
  · exact B147559
  · exact B147563
  · exact B147567
  · exact B147571
  · exact B147575
  · exact B147579
  · exact B147583
  · exact B147587
  · exact B147591
  · exact B147595
  · exact B147599
  · exact B147603
  · exact B147607
  · exact B147611
  · exact B147615
  · exact B147619
  · exact B147623
  · exact B147627
  · exact B147631
  · exact B147635
  · exact B147639
  · exact B147643
  · exact B147647
  · exact B147651
  · exact B147655
  · exact B147659
  · exact B147663
  · exact B147667
  · exact B147671
  · exact B147675
  · exact B147679
  · exact B147683
  · exact B147687
  · exact B147691
  · exact B147695
  · exact B147699
  · exact B147703
  · exact B147707
  · exact B147711
  · exact B147715
  · exact B147719
  · exact B147723
  · exact B147727
  · exact B147731
  · exact B147735
  · exact B147739
  · exact B147743
  · exact B147747
  · exact B147751
  · exact B147755
  · exact B147759
  · exact B147763
  · exact B147767
  · exact B147771
  · exact B147775
  · exact B147779
  · exact B147783
  · exact B147787
  · exact B147791

theorem solution (m : ℕ) (hlo : 143792 ≤ m) (hhi : m ≤ 147792) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 35948 ≤ j := by omega
    have hj2 : j ≤ 36947 := by omega
    have hb : Blo 143792 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 36648 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
