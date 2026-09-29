-- Prove2me | solution 1 for syracuse_descends_range_658307_662307
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:49.647916+00:00
-- url     : https://prove2.me/submissions/7f38cb8b-3e4d-44ae-8909-15642a60d9bf

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


theorem B950285 : Blo 658307 950285 := bbase (se 3 (by rfl) ⟨178178, by rfl⟩ : syracuseStep 950285 = 356357) (by norm_num)
theorem B1114141 : Blo 658307 1114141 := bbase (se 3 (by rfl) ⟨208901, by rfl⟩ : syracuseStep 1114141 = 417803) (by norm_num)
theorem B2228309 : Blo 658307 2228309 := bbase (se 8 (by rfl) ⟨13056, by rfl⟩ : syracuseStep 2228309 = 26113) (by norm_num)
theorem B1114229 : Blo 658307 1114229 := bbase (se 5 (by rfl) ⟨52229, by rfl⟩ : syracuseStep 1114229 = 104459) (by norm_num)
theorem B1671293 : Blo 658307 1671293 := bbase (se 3 (by rfl) ⟨313367, by rfl⟩ : syracuseStep 1671293 = 626735) (by norm_num)
theorem B753817 : Blo 658307 753817 := bbase (se 2 (by rfl) ⟨282681, by rfl⟩ : syracuseStep 753817 = 565363) (by norm_num)
theorem B753881 : Blo 658307 753881 := bbase (se 2 (by rfl) ⟨282705, by rfl⟩ : syracuseStep 753881 = 565411) (by norm_num)
theorem B1114357 : Blo 658307 1114357 := bbase (se 5 (by rfl) ⟨52235, by rfl⟩ : syracuseStep 1114357 = 104471) (by norm_num)
theorem B3768565 : Blo 658307 3768565 := bbase (se 5 (by rfl) ⟨176651, by rfl⟩ : syracuseStep 3768565 = 353303) (by norm_num)
theorem B1409309 : Blo 658307 1409309 := bbase (se 3 (by rfl) ⟨264245, by rfl⟩ : syracuseStep 1409309 = 528491) (by norm_num)
theorem B1114445 : Blo 658307 1114445 := bbase (se 3 (by rfl) ⟨208958, by rfl⟩ : syracuseStep 1114445 = 417917) (by norm_num)
theorem B1114573 : Blo 658307 1114573 := bbase (se 3 (by rfl) ⟨208982, by rfl⟩ : syracuseStep 1114573 = 417965) (by norm_num)
theorem B1671637 : Blo 658307 1671637 := bbase (se 7 (by rfl) ⟨19589, by rfl⟩ : syracuseStep 1671637 = 39179) (by norm_num)
theorem B2228741 : Blo 658307 2228741 := bbase (se 4 (by rfl) ⟨208944, by rfl⟩ : syracuseStep 2228741 = 417889) (by norm_num)
theorem B3342869 : Blo 658307 3342869 := bbase (se 6 (by rfl) ⟨78348, by rfl⟩ : syracuseStep 3342869 = 156697) (by norm_num)
theorem B1114661 : Blo 658307 1114661 := bbase (se 4 (by rfl) ⟨104499, by rfl⟩ : syracuseStep 1114661 = 208999) (by norm_num)
theorem B1671749 : Blo 658307 1671749 := bbase (se 4 (by rfl) ⟨156726, by rfl⟩ : syracuseStep 1671749 = 313453) (by norm_num)
theorem B1114789 : Blo 658307 1114789 := bbase (se 4 (by rfl) ⟨104511, by rfl⟩ : syracuseStep 1114789 = 209023) (by norm_num)
theorem B5636789 : Blo 658307 5636789 := bbase (se 5 (by rfl) ⟨264224, by rfl⟩ : syracuseStep 5636789 = 528449) (by norm_num)
theorem B1114877 : Blo 658307 1114877 := bbase (se 3 (by rfl) ⟨209039, by rfl⟩ : syracuseStep 1114877 = 418079) (by norm_num)
theorem B1671941 : Blo 658307 1671941 := bbase (se 4 (by rfl) ⟨156744, by rfl⟩ : syracuseStep 1671941 = 313489) (by norm_num)
theorem B5079829 : Blo 658307 5079829 := bbase (se 6 (by rfl) ⟨119058, by rfl⟩ : syracuseStep 5079829 = 238117) (by norm_num)
theorem B1115005 : Blo 658307 1115005 := bbase (se 3 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 1115005 = 418127) (by norm_num)
theorem B2229173 : Blo 658307 2229173 := bbase (se 5 (by rfl) ⟨104492, by rfl⟩ : syracuseStep 2229173 = 208985) (by norm_num)
theorem B1115093 : Blo 658307 1115093 := bbase (se 7 (by rfl) ⟨13067, by rfl⟩ : syracuseStep 1115093 = 26135) (by norm_num)
theorem B1410061 : Blo 658307 1410061 := bbase (se 3 (by rfl) ⟨264386, by rfl⟩ : syracuseStep 1410061 = 528773) (by norm_num)
theorem B1115221 : Blo 658307 1115221 := bbase (se 8 (by rfl) ⟨6534, by rfl⟩ : syracuseStep 1115221 = 13069) (by norm_num)
theorem B1672285 : Blo 658307 1672285 := bbase (se 3 (by rfl) ⟨313553, by rfl⟩ : syracuseStep 1672285 = 627107) (by norm_num)
theorem B1410205 : Blo 658307 1410205 := bbase (se 3 (by rfl) ⟨264413, by rfl⟩ : syracuseStep 1410205 = 528827) (by norm_num)
theorem B1115309 : Blo 658307 1115309 := bbase (se 3 (by rfl) ⟨209120, by rfl⟩ : syracuseStep 1115309 = 418241) (by norm_num)
theorem B1672397 : Blo 658307 1672397 := bbase (se 3 (by rfl) ⟨313574, by rfl⟩ : syracuseStep 1672397 = 627149) (by norm_num)
theorem B1115437 : Blo 658307 1115437 := bbase (se 3 (by rfl) ⟨209144, by rfl⟩ : syracuseStep 1115437 = 418289) (by norm_num)
theorem B2229605 : Blo 658307 2229605 := bbase (se 4 (by rfl) ⟨209025, by rfl⟩ : syracuseStep 2229605 = 418051) (by norm_num)
theorem B1115525 : Blo 658307 1115525 := bbase (se 4 (by rfl) ⟨104580, by rfl⟩ : syracuseStep 1115525 = 209161) (by norm_num)
theorem B1672589 : Blo 658307 1672589 := bbase (se 3 (by rfl) ⟨313610, by rfl⟩ : syracuseStep 1672589 = 627221) (by norm_num)
theorem B1115653 : Blo 658307 1115653 := bbase (se 4 (by rfl) ⟨104592, by rfl⟩ : syracuseStep 1115653 = 209185) (by norm_num)
theorem B1410581 : Blo 658307 1410581 := bbase (se 6 (by rfl) ⟨33060, by rfl⟩ : syracuseStep 1410581 = 66121) (by norm_num)
theorem B951869 : Blo 658307 951869 := bbase (se 3 (by rfl) ⟨178475, by rfl⟩ : syracuseStep 951869 = 356951) (by norm_num)
theorem B1115741 : Blo 658307 1115741 := bbase (se 3 (by rfl) ⟨209201, by rfl⟩ : syracuseStep 1115741 = 418403) (by norm_num)
theorem B1115869 : Blo 658307 1115869 := bbase (se 3 (by rfl) ⟨209225, by rfl⟩ : syracuseStep 1115869 = 418451) (by norm_num)
theorem B1672933 : Blo 658307 1672933 := bbase (se 4 (by rfl) ⟨156837, by rfl⟩ : syracuseStep 1672933 = 313675) (by norm_num)
theorem B2230037 : Blo 658307 2230037 := bbase (se 6 (by rfl) ⟨52266, by rfl⟩ : syracuseStep 2230037 = 104533) (by norm_num)
theorem B3344165 : Blo 658307 3344165 := bbase (se 4 (by rfl) ⟨313515, by rfl⟩ : syracuseStep 3344165 = 627031) (by norm_num)
theorem B1115957 : Blo 658307 1115957 := bbase (se 5 (by rfl) ⟨52310, by rfl⟩ : syracuseStep 1115957 = 104621) (by norm_num)
theorem B1673045 : Blo 658307 1673045 := bbase (se 9 (by rfl) ⟨4901, by rfl⟩ : syracuseStep 1673045 = 9803) (by norm_num)
theorem B1509205 : Blo 658307 1509205 := bbase (se 9 (by rfl) ⟨4421, by rfl⟩ : syracuseStep 1509205 = 8843) (by norm_num)
theorem B1410949 : Blo 658307 1410949 := bbase (se 4 (by rfl) ⟨132276, by rfl⟩ : syracuseStep 1410949 = 264553) (by norm_num)
theorem B1116085 : Blo 658307 1116085 := bbase (se 5 (by rfl) ⟨52316, by rfl⟩ : syracuseStep 1116085 = 104633) (by norm_num)
theorem B1116173 : Blo 658307 1116173 := bbase (se 3 (by rfl) ⟨209282, by rfl⟩ : syracuseStep 1116173 = 418565) (by norm_num)
theorem B1673237 : Blo 658307 1673237 := bbase (se 6 (by rfl) ⟨39216, by rfl⟩ : syracuseStep 1673237 = 78433) (by norm_num)
theorem B1116301 : Blo 658307 1116301 := bbase (se 3 (by rfl) ⟨209306, by rfl⟩ : syracuseStep 1116301 = 418613) (by norm_num)
theorem B3770549 : Blo 658307 3770549 := bbase (se 5 (by rfl) ⟨176744, by rfl⟩ : syracuseStep 3770549 = 353489) (by norm_num)
theorem B2230469 : Blo 658307 2230469 := bbase (se 4 (by rfl) ⟨209106, by rfl⟩ : syracuseStep 2230469 = 418213) (by norm_num)
theorem B9537749 : Blo 658307 9537749 := bbase (se 7 (by rfl) ⟨111770, by rfl⟩ : syracuseStep 9537749 = 223541) (by norm_num)
theorem B1116389 : Blo 658307 1116389 := bbase (se 4 (by rfl) ⟨104661, by rfl⟩ : syracuseStep 1116389 = 209323) (by norm_num)
theorem B1116517 : Blo 658307 1116517 := bbase (se 4 (by rfl) ⟨104673, by rfl⟩ : syracuseStep 1116517 = 209347) (by norm_num)
theorem B1673581 : Blo 658307 1673581 := bbase (se 3 (by rfl) ⟨313796, by rfl⟩ : syracuseStep 1673581 = 627593) (by norm_num)
theorem B2263477 : Blo 658307 2263477 := bbase (se 5 (by rfl) ⟨106100, by rfl⟩ : syracuseStep 2263477 = 212201) (by norm_num)
theorem B1116605 : Blo 658307 1116605 := bbase (se 3 (by rfl) ⟨209363, by rfl⟩ : syracuseStep 1116605 = 418727) (by norm_num)
theorem B1673693 : Blo 658307 1673693 := bbase (se 3 (by rfl) ⟨313817, by rfl⟩ : syracuseStep 1673693 = 627635) (by norm_num)
theorem B1116733 : Blo 658307 1116733 := bbase (se 3 (by rfl) ⟨209387, by rfl⟩ : syracuseStep 1116733 = 418775) (by norm_num)
theorem B2230901 : Blo 658307 2230901 := bbase (se 5 (by rfl) ⟨104573, by rfl⟩ : syracuseStep 2230901 = 209147) (by norm_num)
theorem B3181189 : Blo 658307 3181189 := bbase (se 4 (by rfl) ⟨298236, by rfl⟩ : syracuseStep 3181189 = 596473) (by norm_num)
theorem B1116821 : Blo 658307 1116821 := bbase (se 6 (by rfl) ⟨26175, by rfl⟩ : syracuseStep 1116821 = 52351) (by norm_num)
theorem B1673885 : Blo 658307 1673885 := bbase (se 3 (by rfl) ⟨313853, by rfl⟩ : syracuseStep 1673885 = 627707) (by norm_num)
theorem B1116949 : Blo 658307 1116949 := bbase (se 6 (by rfl) ⟨26178, by rfl⟩ : syracuseStep 1116949 = 52357) (by norm_num)
theorem B1543013 : Blo 658307 1543013 := bbase (se 4 (by rfl) ⟨144657, by rfl⟩ : syracuseStep 1543013 = 289315) (by norm_num)
theorem B1117037 : Blo 658307 1117037 := bbase (se 3 (by rfl) ⟨209444, by rfl⟩ : syracuseStep 1117037 = 418889) (by norm_num)
theorem B1117165 : Blo 658307 1117165 := bbase (se 3 (by rfl) ⟨209468, by rfl⟩ : syracuseStep 1117165 = 418937) (by norm_num)
theorem B1674229 : Blo 658307 1674229 := bbase (se 5 (by rfl) ⟨78479, by rfl⟩ : syracuseStep 1674229 = 156959) (by norm_num)
theorem B1903621 : Blo 658307 1903621 := bbase (se 4 (by rfl) ⟨178464, by rfl⟩ : syracuseStep 1903621 = 356929) (by norm_num)
theorem B2231333 : Blo 658307 2231333 := bbase (se 4 (by rfl) ⟨209187, by rfl⟩ : syracuseStep 2231333 = 418375) (by norm_num)
theorem B3345461 : Blo 658307 3345461 := bbase (se 5 (by rfl) ⟨156818, by rfl⟩ : syracuseStep 3345461 = 313637) (by norm_num)
theorem B1117253 : Blo 658307 1117253 := bbase (se 4 (by rfl) ⟨104742, by rfl⟩ : syracuseStep 1117253 = 209485) (by norm_num)
theorem B1674341 : Blo 658307 1674341 := bbase (se 4 (by rfl) ⟨156969, by rfl⟩ : syracuseStep 1674341 = 313939) (by norm_num)
theorem B1510517 : Blo 658307 1510517 := bbase (se 5 (by rfl) ⟨70805, by rfl⟩ : syracuseStep 1510517 = 141611) (by norm_num)
theorem B1117381 : Blo 658307 1117381 := bbase (se 4 (by rfl) ⟨104754, by rfl⟩ : syracuseStep 1117381 = 209509) (by norm_num)
theorem B1117469 : Blo 658307 1117469 := bbase (se 3 (by rfl) ⟨209525, by rfl⟩ : syracuseStep 1117469 = 419051) (by norm_num)
theorem B1674533 : Blo 658307 1674533 := bbase (se 4 (by rfl) ⟨156987, by rfl⟩ : syracuseStep 1674533 = 313975) (by norm_num)
theorem B1412453 : Blo 658307 1412453 := bbase (se 4 (by rfl) ⟨132417, by rfl⟩ : syracuseStep 1412453 = 264835) (by norm_num)
theorem B1117597 : Blo 658307 1117597 := bbase (se 3 (by rfl) ⟨209549, by rfl⟩ : syracuseStep 1117597 = 419099) (by norm_num)
theorem B2231765 : Blo 658307 2231765 := bbase (se 7 (by rfl) ⟨26153, by rfl⟩ : syracuseStep 2231765 = 52307) (by norm_num)
theorem B1412597 : Blo 658307 1412597 := bbase (se 5 (by rfl) ⟨66215, by rfl⟩ : syracuseStep 1412597 = 132431) (by norm_num)
theorem B1674877 : Blo 658307 1674877 := bbase (se 3 (by rfl) ⟨314039, by rfl⟩ : syracuseStep 1674877 = 628079) (by norm_num)
theorem B1085093 : Blo 658307 1085093 := bbase (se 4 (by rfl) ⟨101727, by rfl⟩ : syracuseStep 1085093 = 203455) (by norm_num)
theorem B6786773 : Blo 658307 6786773 := bbase (se 7 (by rfl) ⟨79532, by rfl⟩ : syracuseStep 6786773 = 159065) (by norm_num)
theorem B1674989 : Blo 658307 1674989 := bbase (se 3 (by rfl) ⟨314060, by rfl⟩ : syracuseStep 1674989 = 628121) (by norm_num)
theorem B1412957 : Blo 658307 1412957 := bbase (se 3 (by rfl) ⟨264929, by rfl⟩ : syracuseStep 1412957 = 529859) (by norm_num)
theorem B2232197 : Blo 658307 2232197 := bbase (se 4 (by rfl) ⟨209268, by rfl⟩ : syracuseStep 2232197 = 418537) (by norm_num)
theorem B10719125 : Blo 658307 10719125 := bbase (se 6 (by rfl) ⟨251229, by rfl⟩ : syracuseStep 10719125 = 502459) (by norm_num)
theorem B1675181 : Blo 658307 1675181 := bbase (se 3 (by rfl) ⟨314096, by rfl⟩ : syracuseStep 1675181 = 628193) (by norm_num)
theorem B2822309 : Blo 658307 2822309 := bbase (se 4 (by rfl) ⟨264591, by rfl⟩ : syracuseStep 2822309 = 529183) (by norm_num)
theorem B1675525 : Blo 658307 1675525 := bbase (se 4 (by rfl) ⟨157080, by rfl⟩ : syracuseStep 1675525 = 314161) (by norm_num)
theorem B2265365 : Blo 658307 2265365 := bbase (se 6 (by rfl) ⟨53094, by rfl⟩ : syracuseStep 2265365 = 106189) (by norm_num)
theorem B2232629 : Blo 658307 2232629 := bbase (se 5 (by rfl) ⟨104654, by rfl⟩ : syracuseStep 2232629 = 209309) (by norm_num)
theorem B987461 : Blo 658307 987461 := bbase (se 4 (by rfl) ⟨92574, by rfl⟩ : syracuseStep 987461 = 185149) (by norm_num)
theorem B3346757 : Blo 658307 3346757 := bbase (se 4 (by rfl) ⟨313758, by rfl⟩ : syracuseStep 3346757 = 627517) (by norm_num)
theorem B987485 : Blo 658307 987485 := bbase (se 3 (by rfl) ⟨185153, by rfl⟩ : syracuseStep 987485 = 370307) (by norm_num)
theorem B987509 : Blo 658307 987509 := bbase (se 5 (by rfl) ⟨46289, by rfl⟩ : syracuseStep 987509 = 92579) (by norm_num)
theorem B1675637 : Blo 658307 1675637 := bbase (se 5 (by rfl) ⟨78545, by rfl⟩ : syracuseStep 1675637 = 157091) (by norm_num)
theorem B987533 : Blo 658307 987533 := bbase (se 3 (by rfl) ⟨185162, by rfl⟩ : syracuseStep 987533 = 370325) (by norm_num)
theorem B987557 : Blo 658307 987557 := bbase (se 4 (by rfl) ⟨92583, by rfl⟩ : syracuseStep 987557 = 185167) (by norm_num)
theorem B987581 : Blo 658307 987581 := bbase (se 3 (by rfl) ⟨185171, by rfl⟩ : syracuseStep 987581 = 370343) (by norm_num)
theorem B2822597 : Blo 658307 2822597 := bbase (se 4 (by rfl) ⟨264618, by rfl⟩ : syracuseStep 2822597 = 529237) (by norm_num)
theorem B987605 : Blo 658307 987605 := bbase (se 7 (by rfl) ⟨11573, by rfl⟩ : syracuseStep 987605 = 23147) (by norm_num)
theorem B987629 : Blo 658307 987629 := bbase (se 3 (by rfl) ⟨185180, by rfl⟩ : syracuseStep 987629 = 370361) (by norm_num)
theorem B987653 : Blo 658307 987653 := bbase (se 4 (by rfl) ⟨92592, by rfl⟩ : syracuseStep 987653 = 185185) (by norm_num)
theorem B987677 : Blo 658307 987677 := bbase (se 3 (by rfl) ⟨185189, by rfl⟩ : syracuseStep 987677 = 370379) (by norm_num)
theorem B987701 : Blo 658307 987701 := bbase (se 5 (by rfl) ⟨46298, by rfl⟩ : syracuseStep 987701 = 92597) (by norm_num)
theorem B1675829 : Blo 658307 1675829 := bbase (se 5 (by rfl) ⟨78554, by rfl⟩ : syracuseStep 1675829 = 157109) (by norm_num)
theorem B987725 : Blo 658307 987725 := bbase (se 3 (by rfl) ⟨185198, by rfl⟩ : syracuseStep 987725 = 370397) (by norm_num)
theorem B987749 : Blo 658307 987749 := bbase (se 4 (by rfl) ⟨92601, by rfl⟩ : syracuseStep 987749 = 185203) (by norm_num)
theorem B1249901 : Blo 658307 1249901 := bbase (se 3 (by rfl) ⟨234356, by rfl⟩ : syracuseStep 1249901 = 468713) (by norm_num)
theorem B987773 : Blo 658307 987773 := bbase (se 3 (by rfl) ⟨185207, by rfl⟩ : syracuseStep 987773 = 370415) (by norm_num)
theorem B987797 : Blo 658307 987797 := bbase (se 6 (by rfl) ⟨23151, by rfl⟩ : syracuseStep 987797 = 46303) (by norm_num)
theorem B987821 : Blo 658307 987821 := bbase (se 3 (by rfl) ⟨185216, by rfl⟩ : syracuseStep 987821 = 370433) (by norm_num)
theorem B791213 : Blo 658307 791213 := bbase (se 3 (by rfl) ⟨148352, by rfl⟩ : syracuseStep 791213 = 296705) (by norm_num)
theorem B987845 : Blo 658307 987845 := bbase (se 4 (by rfl) ⟨92610, by rfl⟩ : syracuseStep 987845 = 185221) (by norm_num)
theorem B1413845 : Blo 658307 1413845 := bbase (se 7 (by rfl) ⟨16568, by rfl⟩ : syracuseStep 1413845 = 33137) (by norm_num)
theorem B1020629 : Blo 658307 1020629 := bbase (se 7 (by rfl) ⟨11960, by rfl⟩ : syracuseStep 1020629 = 23921) (by norm_num)
theorem B987869 : Blo 658307 987869 := bbase (se 3 (by rfl) ⟨185225, by rfl⟩ : syracuseStep 987869 = 370451) (by norm_num)
theorem B2233061 : Blo 658307 2233061 := bbase (se 4 (by rfl) ⟨209349, by rfl⟩ : syracuseStep 2233061 = 418699) (by norm_num)
theorem B987893 : Blo 658307 987893 := bbase (se 5 (by rfl) ⟨46307, by rfl⟩ : syracuseStep 987893 = 92615) (by norm_num)
theorem B987917 : Blo 658307 987917 := bbase (se 3 (by rfl) ⟨185234, by rfl⟩ : syracuseStep 987917 = 370469) (by norm_num)
theorem B987941 : Blo 658307 987941 := bbase (se 4 (by rfl) ⟨92619, by rfl⟩ : syracuseStep 987941 = 185239) (by norm_num)
theorem B987965 : Blo 658307 987965 := bbase (se 3 (by rfl) ⟨185243, by rfl⟩ : syracuseStep 987965 = 370487) (by norm_num)
theorem B987989 : Blo 658307 987989 := bbase (se 9 (by rfl) ⟨2894, by rfl⟩ : syracuseStep 987989 = 5789) (by norm_num)
theorem B988013 : Blo 658307 988013 := bbase (se 3 (by rfl) ⟨185252, by rfl⟩ : syracuseStep 988013 = 370505) (by norm_num)
theorem B988037 : Blo 658307 988037 := bbase (se 4 (by rfl) ⟨92628, by rfl⟩ : syracuseStep 988037 = 185257) (by norm_num)
theorem B1676173 : Blo 658307 1676173 := bbase (se 3 (by rfl) ⟨314282, by rfl⟩ : syracuseStep 1676173 = 628565) (by norm_num)
theorem B988061 : Blo 658307 988061 := bbase (se 3 (by rfl) ⟨185261, by rfl⟩ : syracuseStep 988061 = 370523) (by norm_num)
theorem B988085 : Blo 658307 988085 := bbase (se 5 (by rfl) ⟨46316, by rfl⟩ : syracuseStep 988085 = 92633) (by norm_num)
theorem B3019717 : Blo 658307 3019717 := bbase (se 4 (by rfl) ⟨283098, by rfl⟩ : syracuseStep 3019717 = 566197) (by norm_num)
theorem B988109 : Blo 658307 988109 := bbase (se 3 (by rfl) ⟨185270, by rfl⟩ : syracuseStep 988109 = 370541) (by norm_num)
theorem B1414093 : Blo 658307 1414093 := bbase (se 3 (by rfl) ⟨265142, by rfl⟩ : syracuseStep 1414093 = 530285) (by norm_num)
theorem B988133 : Blo 658307 988133 := bbase (se 4 (by rfl) ⟨92637, by rfl⟩ : syracuseStep 988133 = 185275) (by norm_num)
theorem B988157 : Blo 658307 988157 := bbase (se 3 (by rfl) ⟨185279, by rfl⟩ : syracuseStep 988157 = 370559) (by norm_num)
theorem B1676285 : Blo 658307 1676285 := bbase (se 3 (by rfl) ⟨314303, by rfl⟩ : syracuseStep 1676285 = 628607) (by norm_num)
theorem B791569 : Blo 658307 791569 := bbase (se 2 (by rfl) ⟨296838, by rfl⟩ : syracuseStep 791569 = 593677) (by norm_num)
theorem B988181 : Blo 658307 988181 := bbase (se 6 (by rfl) ⟨23160, by rfl⟩ : syracuseStep 988181 = 46321) (by norm_num)
theorem B988205 : Blo 658307 988205 := bbase (se 3 (by rfl) ⟨185288, by rfl⟩ : syracuseStep 988205 = 370577) (by norm_num)
theorem B988229 : Blo 658307 988229 := bbase (se 4 (by rfl) ⟨92646, by rfl⟩ : syracuseStep 988229 = 185293) (by norm_num)
theorem B988253 : Blo 658307 988253 := bbase (se 3 (by rfl) ⟨185297, by rfl⟩ : syracuseStep 988253 = 370595) (by norm_num)
theorem B988277 : Blo 658307 988277 := bbase (se 5 (by rfl) ⟨46325, by rfl⟩ : syracuseStep 988277 = 92651) (by norm_num)
theorem B988301 : Blo 658307 988301 := bbase (se 3 (by rfl) ⟨185306, by rfl⟩ : syracuseStep 988301 = 370613) (by norm_num)
theorem B2233493 : Blo 658307 2233493 := bbase (se 6 (by rfl) ⟨52347, by rfl⟩ : syracuseStep 2233493 = 104695) (by norm_num)
theorem B988325 : Blo 658307 988325 := bbase (se 4 (by rfl) ⟨92655, by rfl⟩ : syracuseStep 988325 = 185311) (by norm_num)
theorem B2823349 : Blo 658307 2823349 := bbase (se 5 (by rfl) ⟨132344, by rfl⟩ : syracuseStep 2823349 = 264689) (by norm_num)
theorem B988349 : Blo 658307 988349 := bbase (se 3 (by rfl) ⟨185315, by rfl⟩ : syracuseStep 988349 = 370631) (by norm_num)
theorem B791761 : Blo 658307 791761 := bbase (se 2 (by rfl) ⟨296910, by rfl⟩ : syracuseStep 791761 = 593821) (by norm_num)
theorem B988373 : Blo 658307 988373 := bbase (se 7 (by rfl) ⟨11582, by rfl⟩ : syracuseStep 988373 = 23165) (by norm_num)
theorem B988397 : Blo 658307 988397 := bbase (se 3 (by rfl) ⟨185324, by rfl⟩ : syracuseStep 988397 = 370649) (by norm_num)
theorem B988421 : Blo 658307 988421 := bbase (se 4 (by rfl) ⟨92664, by rfl⟩ : syracuseStep 988421 = 185329) (by norm_num)
theorem B988445 : Blo 658307 988445 := bbase (se 3 (by rfl) ⟨185333, by rfl⟩ : syracuseStep 988445 = 370667) (by norm_num)
theorem B955685 : Blo 658307 955685 := bbase (se 4 (by rfl) ⟨89595, by rfl⟩ : syracuseStep 955685 = 179191) (by norm_num)
theorem B988469 : Blo 658307 988469 := bbase (se 5 (by rfl) ⟨46334, by rfl⟩ : syracuseStep 988469 = 92669) (by norm_num)
theorem B988493 : Blo 658307 988493 := bbase (se 3 (by rfl) ⟨185342, by rfl⟩ : syracuseStep 988493 = 370685) (by norm_num)
theorem B1250653 : Blo 658307 1250653 := bbase (se 3 (by rfl) ⟨234497, by rfl⟩ : syracuseStep 1250653 = 468995) (by norm_num)
theorem B791905 : Blo 658307 791905 := bbase (se 2 (by rfl) ⟨296964, by rfl⟩ : syracuseStep 791905 = 593929) (by norm_num)
theorem B988517 : Blo 658307 988517 := bbase (se 4 (by rfl) ⟨92673, by rfl⟩ : syracuseStep 988517 = 185347) (by norm_num)
theorem B988541 : Blo 658307 988541 := bbase (se 3 (by rfl) ⟨185351, by rfl⟩ : syracuseStep 988541 = 370703) (by norm_num)
theorem B988565 : Blo 658307 988565 := bbase (se 6 (by rfl) ⟨23169, by rfl⟩ : syracuseStep 988565 = 46339) (by norm_num)
theorem B2004389 : Blo 658307 2004389 := bbase (se 4 (by rfl) ⟨187911, by rfl⟩ : syracuseStep 2004389 = 375823) (by norm_num)
theorem B988589 : Blo 658307 988589 := bbase (se 3 (by rfl) ⟨185360, by rfl⟩ : syracuseStep 988589 = 370721) (by norm_num)
theorem B988613 : Blo 658307 988613 := bbase (se 4 (by rfl) ⟨92682, by rfl⟩ : syracuseStep 988613 = 185365) (by norm_num)
theorem B2004437 : Blo 658307 2004437 := bbase (se 7 (by rfl) ⟨23489, by rfl⟩ : syracuseStep 2004437 = 46979) (by norm_num)
theorem B988637 : Blo 658307 988637 := bbase (se 3 (by rfl) ⟨185369, by rfl⟩ : syracuseStep 988637 = 370739) (by norm_num)
theorem B1250797 : Blo 658307 1250797 := bbase (se 3 (by rfl) ⟨234524, by rfl⟩ : syracuseStep 1250797 = 469049) (by norm_num)
theorem B988661 : Blo 658307 988661 := bbase (se 5 (by rfl) ⟨46343, by rfl⟩ : syracuseStep 988661 = 92687) (by norm_num)
theorem B988685 : Blo 658307 988685 := bbase (se 3 (by rfl) ⟨185378, by rfl⟩ : syracuseStep 988685 = 370757) (by norm_num)
theorem B988709 : Blo 658307 988709 := bbase (se 4 (by rfl) ⟨92691, by rfl⟩ : syracuseStep 988709 = 185383) (by norm_num)
theorem B988733 : Blo 658307 988733 := bbase (se 3 (by rfl) ⟨185387, by rfl⟩ : syracuseStep 988733 = 370775) (by norm_num)
theorem B2233925 : Blo 658307 2233925 := bbase (se 4 (by rfl) ⟨209430, by rfl⟩ : syracuseStep 2233925 = 418861) (by norm_num)
theorem B988757 : Blo 658307 988757 := bbase (se 8 (by rfl) ⟨5793, by rfl⟩ : syracuseStep 988757 = 11587) (by norm_num)
theorem B3348053 : Blo 658307 3348053 := bbase (se 8 (by rfl) ⟨19617, by rfl⟩ : syracuseStep 3348053 = 39235) (by norm_num)
theorem B988781 : Blo 658307 988781 := bbase (se 3 (by rfl) ⟨185396, by rfl⟩ : syracuseStep 988781 = 370793) (by norm_num)
theorem B988805 : Blo 658307 988805 := bbase (se 4 (by rfl) ⟨92700, by rfl⟩ : syracuseStep 988805 = 185401) (by norm_num)
theorem B1250957 : Blo 658307 1250957 := bbase (se 3 (by rfl) ⟨234554, by rfl⟩ : syracuseStep 1250957 = 469109) (by norm_num)
theorem B988829 : Blo 658307 988829 := bbase (se 3 (by rfl) ⟨185405, by rfl⟩ : syracuseStep 988829 = 370811) (by norm_num)
theorem B988853 : Blo 658307 988853 := bbase (se 5 (by rfl) ⟨46352, by rfl⟩ : syracuseStep 988853 = 92705) (by norm_num)
theorem B988877 : Blo 658307 988877 := bbase (se 3 (by rfl) ⟨185414, by rfl⟩ : syracuseStep 988877 = 370829) (by norm_num)
theorem B988901 : Blo 658307 988901 := bbase (se 4 (by rfl) ⟨92709, by rfl⟩ : syracuseStep 988901 = 185419) (by norm_num)
theorem B988925 : Blo 658307 988925 := bbase (se 3 (by rfl) ⟨185423, by rfl⟩ : syracuseStep 988925 = 370847) (by norm_num)
theorem B988949 : Blo 658307 988949 := bbase (se 6 (by rfl) ⟨23178, by rfl⟩ : syracuseStep 988949 = 46357) (by norm_num)
theorem B1251101 : Blo 658307 1251101 := bbase (se 3 (by rfl) ⟨234581, by rfl⟩ : syracuseStep 1251101 = 469163) (by norm_num)
theorem B988973 : Blo 658307 988973 := bbase (se 3 (by rfl) ⟨185432, by rfl⟩ : syracuseStep 988973 = 370865) (by norm_num)
theorem B3020597 : Blo 658307 3020597 := bbase (se 5 (by rfl) ⟨141590, by rfl⟩ : syracuseStep 3020597 = 283181) (by norm_num)
theorem B988997 : Blo 658307 988997 := bbase (se 4 (by rfl) ⟨92718, by rfl⟩ : syracuseStep 988997 = 185437) (by norm_num)
theorem B1054541 : Blo 658307 1054541 := bbase (se 3 (by rfl) ⟨197726, by rfl⟩ : syracuseStep 1054541 = 395453) (by norm_num)
theorem B989021 : Blo 658307 989021 := bbase (se 3 (by rfl) ⟨185441, by rfl⟩ : syracuseStep 989021 = 370883) (by norm_num)
theorem B989045 : Blo 658307 989045 := bbase (se 5 (by rfl) ⟨46361, by rfl⟩ : syracuseStep 989045 = 92723) (by norm_num)
theorem B989069 : Blo 658307 989069 := bbase (se 3 (by rfl) ⟨185450, by rfl⟩ : syracuseStep 989069 = 370901) (by norm_num)
theorem B2824085 : Blo 658307 2824085 := bbase (se 6 (by rfl) ⟨66189, by rfl⟩ : syracuseStep 2824085 = 132379) (by norm_num)
theorem B989093 : Blo 658307 989093 := bbase (se 4 (by rfl) ⟨92727, by rfl⟩ : syracuseStep 989093 = 185455) (by norm_num)
theorem B989117 : Blo 658307 989117 := bbase (se 3 (by rfl) ⟨185459, by rfl⟩ : syracuseStep 989117 = 370919) (by norm_num)
theorem B989141 : Blo 658307 989141 := bbase (se 7 (by rfl) ⟨11591, by rfl⟩ : syracuseStep 989141 = 23183) (by norm_num)
theorem B9050069 : Blo 658307 9050069 := bbase (se 7 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 9050069 = 212111) (by norm_num)
theorem B989165 : Blo 658307 989165 := bbase (se 3 (by rfl) ⟨185468, by rfl⟩ : syracuseStep 989165 = 370937) (by norm_num)
theorem B6789109 : Blo 658307 6789109 := bbase (se 5 (by rfl) ⟨318239, by rfl⟩ : syracuseStep 6789109 = 636479) (by norm_num)
theorem B2234357 : Blo 658307 2234357 := bbase (se 5 (by rfl) ⟨104735, by rfl⟩ : syracuseStep 2234357 = 209471) (by norm_num)
theorem B989189 : Blo 658307 989189 := bbase (se 4 (by rfl) ⟨92736, by rfl⟩ : syracuseStep 989189 = 185473) (by norm_num)
theorem B989213 : Blo 658307 989213 := bbase (se 3 (by rfl) ⟨185477, by rfl⟩ : syracuseStep 989213 = 370955) (by norm_num)
theorem B989237 : Blo 658307 989237 := bbase (se 5 (by rfl) ⟨46370, by rfl⟩ : syracuseStep 989237 = 92741) (by norm_num)
theorem B1251389 : Blo 658307 1251389 := bbase (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) (by norm_num)
theorem B989261 : Blo 658307 989261 := bbase (se 3 (by rfl) ⟨185486, by rfl⟩ : syracuseStep 989261 = 370973) (by norm_num)
theorem B989285 : Blo 658307 989285 := bbase (se 4 (by rfl) ⟨92745, by rfl⟩ : syracuseStep 989285 = 185491) (by norm_num)
theorem B1054829 : Blo 658307 1054829 := bbase (se 3 (by rfl) ⟨197780, by rfl⟩ : syracuseStep 1054829 = 395561) (by norm_num)
theorem B989309 : Blo 658307 989309 := bbase (se 3 (by rfl) ⟨185495, by rfl⟩ : syracuseStep 989309 = 370991) (by norm_num)
theorem B989333 : Blo 658307 989333 := bbase (se 6 (by rfl) ⟨23187, by rfl⟩ : syracuseStep 989333 = 46375) (by norm_num)
theorem B989357 : Blo 658307 989357 := bbase (se 3 (by rfl) ⟨185504, by rfl⟩ : syracuseStep 989357 = 371009) (by norm_num)
theorem B989381 : Blo 658307 989381 := bbase (se 4 (by rfl) ⟨92754, by rfl⟩ : syracuseStep 989381 = 185509) (by norm_num)
theorem B17832149 : Blo 658307 17832149 := bbase (se 7 (by rfl) ⟨208970, by rfl⟩ : syracuseStep 17832149 = 417941) (by norm_num)
theorem B1251541 : Blo 658307 1251541 := bbase (se 7 (by rfl) ⟨14666, by rfl⟩ : syracuseStep 1251541 = 29333) (by norm_num)
theorem B989405 : Blo 658307 989405 := bbase (se 3 (by rfl) ⟨185513, by rfl⟩ : syracuseStep 989405 = 371027) (by norm_num)
theorem B989429 : Blo 658307 989429 := bbase (se 5 (by rfl) ⟨46379, by rfl⟩ : syracuseStep 989429 = 92759) (by norm_num)
theorem B5019893 : Blo 658307 5019893 := bbase (se 5 (by rfl) ⟨235307, by rfl⟩ : syracuseStep 5019893 = 470615) (by norm_num)
theorem B989453 : Blo 658307 989453 := bbase (se 3 (by rfl) ⟨185522, by rfl⟩ : syracuseStep 989453 = 371045) (by norm_num)
theorem B989477 : Blo 658307 989477 := bbase (se 4 (by rfl) ⟨92763, by rfl⟩ : syracuseStep 989477 = 185527) (by norm_num)
theorem B989501 : Blo 658307 989501 := bbase (se 3 (by rfl) ⟨185531, by rfl⟩ : syracuseStep 989501 = 371063) (by norm_num)
theorem B1055053 : Blo 658307 1055053 := bbase (se 3 (by rfl) ⟨197822, by rfl⟩ : syracuseStep 1055053 = 395645) (by norm_num)
theorem B989525 : Blo 658307 989525 := bbase (se 10 (by rfl) ⟨1449, by rfl⟩ : syracuseStep 989525 = 2899) (by norm_num)
theorem B989549 : Blo 658307 989549 := bbase (se 3 (by rfl) ⟨185540, by rfl⟩ : syracuseStep 989549 = 371081) (by norm_num)
theorem B989573 : Blo 658307 989573 := bbase (se 4 (by rfl) ⟨92772, by rfl⟩ : syracuseStep 989573 = 185545) (by norm_num)
theorem B989597 : Blo 658307 989597 := bbase (se 3 (by rfl) ⟨185549, by rfl⟩ : syracuseStep 989597 = 371099) (by norm_num)
theorem B2234789 : Blo 658307 2234789 := bbase (se 4 (by rfl) ⟨209511, by rfl⟩ : syracuseStep 2234789 = 419023) (by norm_num)
theorem B989621 : Blo 658307 989621 := bbase (se 5 (by rfl) ⟨46388, by rfl⟩ : syracuseStep 989621 = 92777) (by norm_num)
theorem B989645 : Blo 658307 989645 := bbase (se 3 (by rfl) ⟨185558, by rfl⟩ : syracuseStep 989645 = 371117) (by norm_num)
theorem B3807701 : Blo 658307 3807701 := bbase (se 7 (by rfl) ⟨44621, by rfl⟩ : syracuseStep 3807701 = 89243) (by norm_num)
theorem B989669 : Blo 658307 989669 := bbase (se 4 (by rfl) ⟨92781, by rfl⟩ : syracuseStep 989669 = 185563) (by norm_num)
theorem B989693 : Blo 658307 989693 := bbase (se 3 (by rfl) ⟨185567, by rfl⟩ : syracuseStep 989693 = 371135) (by norm_num)
theorem B1251845 : Blo 658307 1251845 := bbase (se 4 (by rfl) ⟨117360, by rfl⟩ : syracuseStep 1251845 = 234721) (by norm_num)
theorem B1481237 : Blo 658307 1481237 := bbase (se 6 (by rfl) ⟨34716, by rfl⟩ : syracuseStep 1481237 = 69433) (by norm_num)
theorem B989717 : Blo 658307 989717 := bbase (se 6 (by rfl) ⟨23196, by rfl⟩ : syracuseStep 989717 = 46393) (by norm_num)
theorem B989741 : Blo 658307 989741 := bbase (se 3 (by rfl) ⟨185576, by rfl⟩ : syracuseStep 989741 = 371153) (by norm_num)
theorem B989765 : Blo 658307 989765 := bbase (se 4 (by rfl) ⟨92790, by rfl⟩ : syracuseStep 989765 = 185581) (by norm_num)
theorem B1481309 : Blo 658307 1481309 := bbase (se 3 (by rfl) ⟨277745, by rfl⟩ : syracuseStep 1481309 = 555491) (by norm_num)
theorem B989789 : Blo 658307 989789 := bbase (se 3 (by rfl) ⟨185585, by rfl⟩ : syracuseStep 989789 = 371171) (by norm_num)
theorem B989813 : Blo 658307 989813 := bbase (se 5 (by rfl) ⟨46397, by rfl⟩ : syracuseStep 989813 = 92795) (by norm_num)
theorem B989837 : Blo 658307 989837 := bbase (se 3 (by rfl) ⟨185594, by rfl⟩ : syracuseStep 989837 = 371189) (by norm_num)
theorem B1481381 : Blo 658307 1481381 := bbase (se 4 (by rfl) ⟨138879, by rfl⟩ : syracuseStep 1481381 = 277759) (by norm_num)
theorem B989861 : Blo 658307 989861 := bbase (se 4 (by rfl) ⟨92799, by rfl⟩ : syracuseStep 989861 = 185599) (by norm_num)
theorem B989885 : Blo 658307 989885 := bbase (se 3 (by rfl) ⟨185603, by rfl⟩ : syracuseStep 989885 = 371207) (by norm_num)
theorem B989909 : Blo 658307 989909 := bbase (se 7 (by rfl) ⟨11600, by rfl⟩ : syracuseStep 989909 = 23201) (by norm_num)
theorem B1481453 : Blo 658307 1481453 := bbase (se 3 (by rfl) ⟨277772, by rfl⟩ : syracuseStep 1481453 = 555545) (by norm_num)
theorem B989933 : Blo 658307 989933 := bbase (se 3 (by rfl) ⟨185612, by rfl⟩ : syracuseStep 989933 = 371225) (by norm_num)
theorem B989957 : Blo 658307 989957 := bbase (se 4 (by rfl) ⟨92808, by rfl⟩ : syracuseStep 989957 = 185617) (by norm_num)
theorem B989981 : Blo 658307 989981 := bbase (se 3 (by rfl) ⟨185621, by rfl⟩ : syracuseStep 989981 = 371243) (by norm_num)
theorem B1481525 : Blo 658307 1481525 := bbase (se 5 (by rfl) ⟨69446, by rfl⟩ : syracuseStep 1481525 = 138893) (by norm_num)
theorem B990005 : Blo 658307 990005 := bbase (se 5 (by rfl) ⟨46406, by rfl⟩ : syracuseStep 990005 = 92813) (by norm_num)
theorem B990029 : Blo 658307 990029 := bbase (se 3 (by rfl) ⟨185630, by rfl⟩ : syracuseStep 990029 = 371261) (by norm_num)
theorem B2235221 : Blo 658307 2235221 := bbase (se 9 (by rfl) ⟨6548, by rfl⟩ : syracuseStep 2235221 = 13097) (by norm_num)
theorem B793433 : Blo 658307 793433 := bbase (se 2 (by rfl) ⟨297537, by rfl⟩ : syracuseStep 793433 = 595075) (by norm_num)
theorem B990053 : Blo 658307 990053 := bbase (se 4 (by rfl) ⟨92817, by rfl⟩ : syracuseStep 990053 = 185635) (by norm_num)
theorem B3349349 : Blo 658307 3349349 := bbase (se 4 (by rfl) ⟨314001, by rfl⟩ : syracuseStep 3349349 = 628003) (by norm_num)
theorem B1481597 : Blo 658307 1481597 := bbase (se 3 (by rfl) ⟨277799, by rfl⟩ : syracuseStep 1481597 = 555599) (by norm_num)
theorem B990077 : Blo 658307 990077 := bbase (se 3 (by rfl) ⟨185639, by rfl⟩ : syracuseStep 990077 = 371279) (by norm_num)
theorem B990101 : Blo 658307 990101 := bbase (se 6 (by rfl) ⟨23205, by rfl⟩ : syracuseStep 990101 = 46411) (by norm_num)
theorem B990125 : Blo 658307 990125 := bbase (se 3 (by rfl) ⟨185648, by rfl⟩ : syracuseStep 990125 = 371297) (by norm_num)
theorem B3218357 : Blo 658307 3218357 := bbase (se 5 (by rfl) ⟨150860, by rfl⟩ : syracuseStep 3218357 = 301721) (by norm_num)
theorem B1481669 : Blo 658307 1481669 := bbase (se 4 (by rfl) ⟨138906, by rfl⟩ : syracuseStep 1481669 = 277813) (by norm_num)
theorem B990149 : Blo 658307 990149 := bbase (se 4 (by rfl) ⟨92826, by rfl⟩ : syracuseStep 990149 = 185653) (by norm_num)
theorem B990173 : Blo 658307 990173 := bbase (se 3 (by rfl) ⟨185657, by rfl⟩ : syracuseStep 990173 = 371315) (by norm_num)
theorem B891877 : Blo 658307 891877 := bbase (se 4 (by rfl) ⟨83613, by rfl⟩ : syracuseStep 891877 = 167227) (by norm_num)
theorem B990197 : Blo 658307 990197 := bbase (se 5 (by rfl) ⟨46415, by rfl⟩ : syracuseStep 990197 = 92831) (by norm_num)
theorem B1481741 : Blo 658307 1481741 := bbase (se 3 (by rfl) ⟨277826, by rfl⟩ : syracuseStep 1481741 = 555653) (by norm_num)
theorem B990221 : Blo 658307 990221 := bbase (se 3 (by rfl) ⟨185666, by rfl⟩ : syracuseStep 990221 = 371333) (by norm_num)
theorem B990245 : Blo 658307 990245 := bbase (se 4 (by rfl) ⟨92835, by rfl⟩ : syracuseStep 990245 = 185671) (by norm_num)
theorem B990269 : Blo 658307 990269 := bbase (se 3 (by rfl) ⟨185675, by rfl⟩ : syracuseStep 990269 = 371351) (by norm_num)
theorem B1481813 : Blo 658307 1481813 := bbase (se 8 (by rfl) ⟨8682, by rfl⟩ : syracuseStep 1481813 = 17365) (by norm_num)
theorem B990293 : Blo 658307 990293 := bbase (se 8 (by rfl) ⟨5802, by rfl⟩ : syracuseStep 990293 = 11605) (by norm_num)
theorem B990317 : Blo 658307 990317 := bbase (se 3 (by rfl) ⟨185684, by rfl⟩ : syracuseStep 990317 = 371369) (by norm_num)
theorem B990341 : Blo 658307 990341 := bbase (se 4 (by rfl) ⟨92844, by rfl⟩ : syracuseStep 990341 = 185689) (by norm_num)
theorem B793741 : Blo 658307 793741 := bbase (se 3 (by rfl) ⟨148826, by rfl⟩ : syracuseStep 793741 = 297653) (by norm_num)
theorem B1481885 : Blo 658307 1481885 := bbase (se 3 (by rfl) ⟨277853, by rfl⟩ : syracuseStep 1481885 = 555707) (by norm_num)
theorem B990365 : Blo 658307 990365 := bbase (se 3 (by rfl) ⟨185693, by rfl⟩ : syracuseStep 990365 = 371387) (by norm_num)
theorem B1875125 : Blo 658307 1875125 := bbase (se 5 (by rfl) ⟨87896, by rfl⟩ : syracuseStep 1875125 = 175793) (by norm_num)
theorem B990389 : Blo 658307 990389 := bbase (se 5 (by rfl) ⟨46424, by rfl⟩ : syracuseStep 990389 = 92849) (by norm_num)
theorem B990413 : Blo 658307 990413 := bbase (se 3 (by rfl) ⟨185702, by rfl⟩ : syracuseStep 990413 = 371405) (by norm_num)
theorem B1481957 : Blo 658307 1481957 := bbase (se 4 (by rfl) ⟨138933, by rfl⟩ : syracuseStep 1481957 = 277867) (by norm_num)
theorem B990437 : Blo 658307 990437 := bbase (se 4 (by rfl) ⟨92853, by rfl⟩ : syracuseStep 990437 = 185707) (by norm_num)
theorem B1613029 : Blo 658307 1613029 := bbase (se 4 (by rfl) ⟨151221, by rfl⟩ : syracuseStep 1613029 = 302443) (by norm_num)
theorem B793837 : Blo 658307 793837 := bbase (se 3 (by rfl) ⟨148844, by rfl⟩ : syracuseStep 793837 = 297689) (by norm_num)
theorem B1252597 : Blo 658307 1252597 := bbase (se 5 (by rfl) ⟨58715, by rfl⟩ : syracuseStep 1252597 = 117431) (by norm_num)
theorem B990461 : Blo 658307 990461 := bbase (se 3 (by rfl) ⟨185711, by rfl⟩ : syracuseStep 990461 = 371423) (by norm_num)
theorem B1187093 : Blo 658307 1187093 := bbase (se 6 (by rfl) ⟨27822, by rfl⟩ : syracuseStep 1187093 = 55645) (by norm_num)
theorem B990485 : Blo 658307 990485 := bbase (se 6 (by rfl) ⟨23214, by rfl⟩ : syracuseStep 990485 = 46429) (by norm_num)
theorem B1482029 : Blo 658307 1482029 := bbase (se 3 (by rfl) ⟨277880, by rfl⟩ : syracuseStep 1482029 = 555761) (by norm_num)
theorem B990509 : Blo 658307 990509 := bbase (se 3 (by rfl) ⟨185720, by rfl⟩ : syracuseStep 990509 = 371441) (by norm_num)
theorem B990533 : Blo 658307 990533 := bbase (se 4 (by rfl) ⟨92862, by rfl⟩ : syracuseStep 990533 = 185725) (by norm_num)
theorem B990557 : Blo 658307 990557 := bbase (se 3 (by rfl) ⟨185729, by rfl⟩ : syracuseStep 990557 = 371459) (by norm_num)
theorem B1482101 : Blo 658307 1482101 := bbase (se 5 (by rfl) ⟨69473, by rfl⟩ : syracuseStep 1482101 = 138947) (by norm_num)
theorem B990581 : Blo 658307 990581 := bbase (se 5 (by rfl) ⟨46433, by rfl⟩ : syracuseStep 990581 = 92867) (by norm_num)
theorem B1252741 : Blo 658307 1252741 := bbase (se 4 (by rfl) ⟨117444, by rfl⟩ : syracuseStep 1252741 = 234889) (by norm_num)
theorem B990605 : Blo 658307 990605 := bbase (se 3 (by rfl) ⟨185738, by rfl⟩ : syracuseStep 990605 = 371477) (by norm_num)
theorem B990629 : Blo 658307 990629 := bbase (se 4 (by rfl) ⟨92871, by rfl⟩ : syracuseStep 990629 = 185743) (by norm_num)
theorem B1056181 : Blo 658307 1056181 := bbase (se 5 (by rfl) ⟨49508, by rfl⟩ : syracuseStep 1056181 = 99017) (by norm_num)
theorem B1482173 : Blo 658307 1482173 := bbase (se 3 (by rfl) ⟨277907, by rfl⟩ : syracuseStep 1482173 = 555815) (by norm_num)
theorem B990653 : Blo 658307 990653 := bbase (se 3 (by rfl) ⟨185747, by rfl⟩ : syracuseStep 990653 = 371495) (by norm_num)
theorem B990677 : Blo 658307 990677 := bbase (se 7 (by rfl) ⟨11609, by rfl⟩ : syracuseStep 990677 = 23219) (by norm_num)
theorem B990701 : Blo 658307 990701 := bbase (se 3 (by rfl) ⟨185756, by rfl⟩ : syracuseStep 990701 = 371513) (by norm_num)
theorem B1482245 : Blo 658307 1482245 := bbase (se 4 (by rfl) ⟨138960, by rfl⟩ : syracuseStep 1482245 = 277921) (by norm_num)
theorem B990725 : Blo 658307 990725 := bbase (se 4 (by rfl) ⟨92880, by rfl⟩ : syracuseStep 990725 = 185761) (by norm_num)
theorem B794125 : Blo 658307 794125 := bbase (se 3 (by rfl) ⟨148898, by rfl⟩ : syracuseStep 794125 = 297797) (by norm_num)
theorem B990749 : Blo 658307 990749 := bbase (se 3 (by rfl) ⟨185765, by rfl⟩ : syracuseStep 990749 = 371531) (by norm_num)
theorem B1252901 : Blo 658307 1252901 := bbase (se 4 (by rfl) ⟨117459, by rfl⟩ : syracuseStep 1252901 = 234919) (by norm_num)
theorem B990773 : Blo 658307 990773 := bbase (se 5 (by rfl) ⟨46442, by rfl⟩ : syracuseStep 990773 = 92885) (by norm_num)
theorem B1482317 : Blo 658307 1482317 := bbase (se 3 (by rfl) ⟨277934, by rfl⟩ : syracuseStep 1482317 = 555869) (by norm_num)
theorem B990797 : Blo 658307 990797 := bbase (se 3 (by rfl) ⟨185774, by rfl⟩ : syracuseStep 990797 = 371549) (by norm_num)
theorem B990821 : Blo 658307 990821 := bbase (se 4 (by rfl) ⟨92889, by rfl⟩ : syracuseStep 990821 = 185779) (by norm_num)
theorem B990845 : Blo 658307 990845 := bbase (se 3 (by rfl) ⟨185783, by rfl⟩ : syracuseStep 990845 = 371567) (by norm_num)
theorem B1482389 : Blo 658307 1482389 := bbase (se 6 (by rfl) ⟨34743, by rfl⟩ : syracuseStep 1482389 = 69487) (by norm_num)
theorem B990869 : Blo 658307 990869 := bbase (se 6 (by rfl) ⟨23223, by rfl⟩ : syracuseStep 990869 = 46447) (by norm_num)
theorem B990893 : Blo 658307 990893 := bbase (se 3 (by rfl) ⟨185792, by rfl⟩ : syracuseStep 990893 = 371585) (by norm_num)
theorem B1253045 : Blo 658307 1253045 := bbase (se 5 (by rfl) ⟨58736, by rfl⟩ : syracuseStep 1253045 = 117473) (by norm_num)
theorem B990917 : Blo 658307 990917 := bbase (se 4 (by rfl) ⟨92898, by rfl⟩ : syracuseStep 990917 = 185797) (by norm_num)
theorem B794317 : Blo 658307 794317 := bbase (se 3 (by rfl) ⟨148934, by rfl⟩ : syracuseStep 794317 = 297869) (by norm_num)
theorem B1482461 : Blo 658307 1482461 := bbase (se 3 (by rfl) ⟨277961, by rfl⟩ : syracuseStep 1482461 = 555923) (by norm_num)
theorem B990941 : Blo 658307 990941 := bbase (se 3 (by rfl) ⟨185801, by rfl⟩ : syracuseStep 990941 = 371603) (by norm_num)
theorem B990965 : Blo 658307 990965 := bbase (se 5 (by rfl) ⟨46451, by rfl⟩ : syracuseStep 990965 = 92903) (by norm_num)
theorem B990989 : Blo 658307 990989 := bbase (se 3 (by rfl) ⟨185810, by rfl⟩ : syracuseStep 990989 = 371621) (by norm_num)
theorem B1482533 : Blo 658307 1482533 := bbase (se 4 (by rfl) ⟨138987, by rfl⟩ : syracuseStep 1482533 = 277975) (by norm_num)
theorem B991013 : Blo 658307 991013 := bbase (se 4 (by rfl) ⟨92907, by rfl⟩ : syracuseStep 991013 = 185815) (by norm_num)
theorem B991037 : Blo 658307 991037 := bbase (se 3 (by rfl) ⟨185819, by rfl⟩ : syracuseStep 991037 = 371639) (by norm_num)
theorem B991061 : Blo 658307 991061 := bbase (se 9 (by rfl) ⟨2903, by rfl⟩ : syracuseStep 991061 = 5807) (by norm_num)
theorem B1482605 : Blo 658307 1482605 := bbase (se 3 (by rfl) ⟨277988, by rfl⟩ : syracuseStep 1482605 = 555977) (by norm_num)
theorem B991085 : Blo 658307 991085 := bbase (se 3 (by rfl) ⟨185828, by rfl⟩ : syracuseStep 991085 = 371657) (by norm_num)
theorem B1056629 : Blo 658307 1056629 := bbase (se 5 (by rfl) ⟨49529, by rfl⟩ : syracuseStep 1056629 = 99059) (by norm_num)
theorem B1810309 : Blo 658307 1810309 := bbase (se 4 (by rfl) ⟨169716, by rfl⟩ : syracuseStep 1810309 = 339433) (by norm_num)
theorem B991109 : Blo 658307 991109 := bbase (se 4 (by rfl) ⟨92916, by rfl⟩ : syracuseStep 991109 = 185833) (by norm_num)
theorem B991133 : Blo 658307 991133 := bbase (se 3 (by rfl) ⟨185837, by rfl⟩ : syracuseStep 991133 = 371675) (by norm_num)
theorem B1482677 : Blo 658307 1482677 := bbase (se 5 (by rfl) ⟨69500, by rfl⟩ : syracuseStep 1482677 = 139001) (by norm_num)
theorem B991157 : Blo 658307 991157 := bbase (se 5 (by rfl) ⟨46460, by rfl⟩ : syracuseStep 991157 = 92921) (by norm_num)
theorem B991181 : Blo 658307 991181 := bbase (se 3 (by rfl) ⟨185846, by rfl⟩ : syracuseStep 991181 = 371693) (by norm_num)
theorem B1253333 : Blo 658307 1253333 := bbase (se 7 (by rfl) ⟨14687, by rfl⟩ : syracuseStep 1253333 = 29375) (by norm_num)
theorem B991205 : Blo 658307 991205 := bbase (se 4 (by rfl) ⟨92925, by rfl⟩ : syracuseStep 991205 = 185851) (by norm_num)
theorem B991229 : Blo 658307 991229 := bbase (se 3 (by rfl) ⟨185855, by rfl⟩ : syracuseStep 991229 = 371711) (by norm_num)
theorem B1482749 : Blo 658307 1482749 := bbase (se 3 (by rfl) ⟨278015, by rfl⟩ : syracuseStep 1482749 = 556031) (by norm_num)
theorem B991253 : Blo 658307 991253 := bbase (se 6 (by rfl) ⟨23232, by rfl⟩ : syracuseStep 991253 = 46465) (by norm_num)
theorem B991277 : Blo 658307 991277 := bbase (se 3 (by rfl) ⟨185864, by rfl⟩ : syracuseStep 991277 = 371729) (by norm_num)
theorem B1482821 : Blo 658307 1482821 := bbase (se 4 (by rfl) ⟨139014, by rfl⟩ : syracuseStep 1482821 = 278029) (by norm_num)
theorem B991301 : Blo 658307 991301 := bbase (se 4 (by rfl) ⟨92934, by rfl⟩ : syracuseStep 991301 = 185869) (by norm_num)
theorem B991325 : Blo 658307 991325 := bbase (se 3 (by rfl) ⟨185873, by rfl⟩ : syracuseStep 991325 = 371747) (by norm_num)
theorem B1253485 : Blo 658307 1253485 := bbase (se 3 (by rfl) ⟨235028, by rfl⟩ : syracuseStep 1253485 = 470057) (by norm_num)
theorem B991349 : Blo 658307 991349 := bbase (se 5 (by rfl) ⟨46469, by rfl⟩ : syracuseStep 991349 = 92939) (by norm_num)
theorem B3350645 : Blo 658307 3350645 := bbase (se 5 (by rfl) ⟨157061, by rfl⟩ : syracuseStep 3350645 = 314123) (by norm_num)
theorem B1482893 : Blo 658307 1482893 := bbase (se 3 (by rfl) ⟨278042, by rfl⟩ : syracuseStep 1482893 = 556085) (by norm_num)
theorem B991373 : Blo 658307 991373 := bbase (se 3 (by rfl) ⟨185882, by rfl⟩ : syracuseStep 991373 = 371765) (by norm_num)
theorem B991397 : Blo 658307 991397 := bbase (se 4 (by rfl) ⟨92943, by rfl⟩ : syracuseStep 991397 = 185887) (by norm_num)
theorem B6037685 : Blo 658307 6037685 := bbase (se 5 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 6037685 = 566033) (by norm_num)
theorem B991421 : Blo 658307 991421 := bbase (se 3 (by rfl) ⟨185891, by rfl⟩ : syracuseStep 991421 = 371783) (by norm_num)
theorem B1482965 : Blo 658307 1482965 := bbase (se 7 (by rfl) ⟨17378, by rfl⟩ : syracuseStep 1482965 = 34757) (by norm_num)
theorem B991445 : Blo 658307 991445 := bbase (se 7 (by rfl) ⟨11618, by rfl⟩ : syracuseStep 991445 = 23237) (by norm_num)
theorem B991469 : Blo 658307 991469 := bbase (se 3 (by rfl) ⟨185900, by rfl⟩ : syracuseStep 991469 = 371801) (by norm_num)
theorem B991493 : Blo 658307 991493 := bbase (se 4 (by rfl) ⟨92952, by rfl⟩ : syracuseStep 991493 = 185905) (by norm_num)
theorem B1483037 : Blo 658307 1483037 := bbase (se 3 (by rfl) ⟨278069, by rfl⟩ : syracuseStep 1483037 = 556139) (by norm_num)
theorem B991517 : Blo 658307 991517 := bbase (se 3 (by rfl) ⟨185909, by rfl⟩ : syracuseStep 991517 = 371819) (by norm_num)
theorem B991541 : Blo 658307 991541 := bbase (se 5 (by rfl) ⟨46478, by rfl⟩ : syracuseStep 991541 = 92957) (by norm_num)
theorem B991565 : Blo 658307 991565 := bbase (se 3 (by rfl) ⟨185918, by rfl⟩ : syracuseStep 991565 = 371837) (by norm_num)
theorem B1483109 : Blo 658307 1483109 := bbase (se 4 (by rfl) ⟨139041, by rfl⟩ : syracuseStep 1483109 = 278083) (by norm_num)
theorem B991589 : Blo 658307 991589 := bbase (se 4 (by rfl) ⟨92961, by rfl⟩ : syracuseStep 991589 = 185923) (by norm_num)
theorem B991613 : Blo 658307 991613 := bbase (se 3 (by rfl) ⟨185927, by rfl⟩ : syracuseStep 991613 = 371855) (by norm_num)
theorem B991637 : Blo 658307 991637 := bbase (se 6 (by rfl) ⟨23241, by rfl⟩ : syracuseStep 991637 = 46483) (by norm_num)
theorem B1253789 : Blo 658307 1253789 := bbase (se 3 (by rfl) ⟨235085, by rfl⟩ : syracuseStep 1253789 = 470171) (by norm_num)
theorem B1483181 : Blo 658307 1483181 := bbase (se 3 (by rfl) ⟨278096, by rfl⟩ : syracuseStep 1483181 = 556193) (by norm_num)
theorem B991661 : Blo 658307 991661 := bbase (se 3 (by rfl) ⟨185936, by rfl⟩ : syracuseStep 991661 = 371873) (by norm_num)
theorem B991685 : Blo 658307 991685 := bbase (se 4 (by rfl) ⟨92970, by rfl⟩ : syracuseStep 991685 = 185941) (by norm_num)
theorem B991709 : Blo 658307 991709 := bbase (se 3 (by rfl) ⟨185945, by rfl⟩ : syracuseStep 991709 = 371891) (by norm_num)
theorem B1483253 : Blo 658307 1483253 := bbase (se 5 (by rfl) ⟨69527, by rfl⟩ : syracuseStep 1483253 = 139055) (by norm_num)
theorem B991733 : Blo 658307 991733 := bbase (se 5 (by rfl) ⟨46487, by rfl⟩ : syracuseStep 991733 = 92975) (by norm_num)
theorem B991757 : Blo 658307 991757 := bbase (se 3 (by rfl) ⟨185954, by rfl⟩ : syracuseStep 991757 = 371909) (by norm_num)
theorem B991781 : Blo 658307 991781 := bbase (se 4 (by rfl) ⟨92979, by rfl⟩ : syracuseStep 991781 = 185959) (by norm_num)
theorem B3875381 : Blo 658307 3875381 := bbase (se 5 (by rfl) ⟨181658, by rfl⟩ : syracuseStep 3875381 = 363317) (by norm_num)
theorem B1483325 : Blo 658307 1483325 := bbase (se 3 (by rfl) ⟨278123, by rfl⟩ : syracuseStep 1483325 = 556247) (by norm_num)
theorem B1188413 : Blo 658307 1188413 := bbase (se 3 (by rfl) ⟨222827, by rfl⟩ : syracuseStep 1188413 = 445655) (by norm_num)
theorem B991805 : Blo 658307 991805 := bbase (se 3 (by rfl) ⟨185963, by rfl⟩ : syracuseStep 991805 = 371927) (by norm_num)
theorem B795197 : Blo 658307 795197 := bbase (se 3 (by rfl) ⟨149099, by rfl⟩ : syracuseStep 795197 = 298199) (by norm_num)
theorem B991829 : Blo 658307 991829 := bbase (se 8 (by rfl) ⟨5811, by rfl⟩ : syracuseStep 991829 = 11623) (by norm_num)
theorem B991853 : Blo 658307 991853 := bbase (se 3 (by rfl) ⟨185972, by rfl⟩ : syracuseStep 991853 = 371945) (by norm_num)
theorem B1483397 : Blo 658307 1483397 := bbase (se 4 (by rfl) ⟨139068, by rfl⟩ : syracuseStep 1483397 = 278137) (by norm_num)
theorem B991877 : Blo 658307 991877 := bbase (se 4 (by rfl) ⟨92988, by rfl⟩ : syracuseStep 991877 = 185977) (by norm_num)
theorem B991901 : Blo 658307 991901 := bbase (se 3 (by rfl) ⟨185981, by rfl⟩ : syracuseStep 991901 = 371963) (by norm_num)
theorem B991925 : Blo 658307 991925 := bbase (se 5 (by rfl) ⟨46496, by rfl⟩ : syracuseStep 991925 = 92993) (by norm_num)
theorem B893629 : Blo 658307 893629 := bbase (se 3 (by rfl) ⟨167555, by rfl⟩ : syracuseStep 893629 = 335111) (by norm_num)
theorem B1483469 : Blo 658307 1483469 := bbase (se 3 (by rfl) ⟨278150, by rfl⟩ : syracuseStep 1483469 = 556301) (by norm_num)
theorem B991949 : Blo 658307 991949 := bbase (se 3 (by rfl) ⟨185990, by rfl⟩ : syracuseStep 991949 = 371981) (by norm_num)
theorem B1876709 : Blo 658307 1876709 := bbase (se 4 (by rfl) ⟨175941, by rfl⟩ : syracuseStep 1876709 = 351883) (by norm_num)
theorem B991973 : Blo 658307 991973 := bbase (se 4 (by rfl) ⟨92997, by rfl⟩ : syracuseStep 991973 = 185995) (by norm_num)
theorem B991997 : Blo 658307 991997 := bbase (se 3 (by rfl) ⟨185999, by rfl⟩ : syracuseStep 991997 = 371999) (by norm_num)
theorem B1483541 : Blo 658307 1483541 := bbase (se 6 (by rfl) ⟨34770, by rfl⟩ : syracuseStep 1483541 = 69541) (by norm_num)
theorem B992021 : Blo 658307 992021 := bbase (se 6 (by rfl) ⟨23250, by rfl⟩ : syracuseStep 992021 = 46501) (by norm_num)
theorem B992045 : Blo 658307 992045 := bbase (se 3 (by rfl) ⟨186008, by rfl⟩ : syracuseStep 992045 = 372017) (by norm_num)
theorem B992069 : Blo 658307 992069 := bbase (se 4 (by rfl) ⟨93006, by rfl⟩ : syracuseStep 992069 = 186013) (by norm_num)
theorem B1483613 : Blo 658307 1483613 := bbase (se 3 (by rfl) ⟨278177, by rfl⟩ : syracuseStep 1483613 = 556355) (by norm_num)
theorem B992093 : Blo 658307 992093 := bbase (se 3 (by rfl) ⟨186017, by rfl⟩ : syracuseStep 992093 = 372035) (by norm_num)
theorem B992117 : Blo 658307 992117 := bbase (se 5 (by rfl) ⟨46505, by rfl⟩ : syracuseStep 992117 = 93011) (by norm_num)
theorem B992141 : Blo 658307 992141 := bbase (se 3 (by rfl) ⟨186026, by rfl⟩ : syracuseStep 992141 = 372053) (by norm_num)
theorem B893845 : Blo 658307 893845 := bbase (se 6 (by rfl) ⟨20949, by rfl⟩ : syracuseStep 893845 = 41899) (by norm_num)
theorem B1483685 : Blo 658307 1483685 := bbase (se 4 (by rfl) ⟨139095, by rfl⟩ : syracuseStep 1483685 = 278191) (by norm_num)
theorem B992165 : Blo 658307 992165 := bbase (se 4 (by rfl) ⟨93015, by rfl⟩ : syracuseStep 992165 = 186031) (by norm_num)
theorem B992189 : Blo 658307 992189 := bbase (se 3 (by rfl) ⟨186035, by rfl⟩ : syracuseStep 992189 = 372071) (by norm_num)
theorem B992213 : Blo 658307 992213 := bbase (se 7 (by rfl) ⟨11627, by rfl⟩ : syracuseStep 992213 = 23255) (by norm_num)
theorem B1483757 : Blo 658307 1483757 := bbase (se 3 (by rfl) ⟨278204, by rfl⟩ : syracuseStep 1483757 = 556409) (by norm_num)
theorem B992237 : Blo 658307 992237 := bbase (se 3 (by rfl) ⟨186044, by rfl⟩ : syracuseStep 992237 = 372089) (by norm_num)
theorem B992261 : Blo 658307 992261 := bbase (se 4 (by rfl) ⟨93024, by rfl⟩ : syracuseStep 992261 = 186049) (by norm_num)
theorem B2499605 : Blo 658307 2499605 := bbase (se 6 (by rfl) ⟨58584, by rfl⟩ : syracuseStep 2499605 = 117169) (by norm_num)
theorem B10298389 : Blo 658307 10298389 := bbase (se 6 (by rfl) ⟨241368, by rfl⟩ : syracuseStep 10298389 = 482737) (by norm_num)
theorem B992285 : Blo 658307 992285 := bbase (se 3 (by rfl) ⟨186053, by rfl⟩ : syracuseStep 992285 = 372107) (by norm_num)
theorem B1483829 : Blo 658307 1483829 := bbase (se 5 (by rfl) ⟨69554, by rfl⟩ : syracuseStep 1483829 = 139109) (by norm_num)
theorem B992309 : Blo 658307 992309 := bbase (se 5 (by rfl) ⟨46514, by rfl⟩ : syracuseStep 992309 = 93029) (by norm_num)
theorem B992333 : Blo 658307 992333 := bbase (se 3 (by rfl) ⟨186062, by rfl⟩ : syracuseStep 992333 = 372125) (by norm_num)
theorem B992357 : Blo 658307 992357 := bbase (se 4 (by rfl) ⟨93033, by rfl⟩ : syracuseStep 992357 = 186067) (by norm_num)
theorem B2827381 : Blo 658307 2827381 := bbase (se 5 (by rfl) ⟨132533, by rfl⟩ : syracuseStep 2827381 = 265067) (by norm_num)
theorem B1483901 : Blo 658307 1483901 := bbase (se 3 (by rfl) ⟨278231, by rfl⟩ : syracuseStep 1483901 = 556463) (by norm_num)
theorem B992381 : Blo 658307 992381 := bbase (se 3 (by rfl) ⟨186071, by rfl⟩ : syracuseStep 992381 = 372143) (by norm_num)
theorem B1254541 : Blo 658307 1254541 := bbase (se 3 (by rfl) ⟨235226, by rfl⟩ : syracuseStep 1254541 = 470453) (by norm_num)
theorem B992405 : Blo 658307 992405 := bbase (se 6 (by rfl) ⟨23259, by rfl⟩ : syracuseStep 992405 = 46519) (by norm_num)
theorem B992429 : Blo 658307 992429 := bbase (se 3 (by rfl) ⟨186080, by rfl⟩ : syracuseStep 992429 = 372161) (by norm_num)
theorem B1483973 : Blo 658307 1483973 := bbase (se 4 (by rfl) ⟨139122, by rfl⟩ : syracuseStep 1483973 = 278245) (by norm_num)
theorem B992453 : Blo 658307 992453 := bbase (se 4 (by rfl) ⟨93042, by rfl⟩ : syracuseStep 992453 = 186085) (by norm_num)
theorem B992477 : Blo 658307 992477 := bbase (se 3 (by rfl) ⟨186089, by rfl⟩ : syracuseStep 992477 = 372179) (by norm_num)
theorem B992501 : Blo 658307 992501 := bbase (se 5 (by rfl) ⟨46523, by rfl⟩ : syracuseStep 992501 = 93047) (by norm_num)
theorem B1484045 : Blo 658307 1484045 := bbase (se 3 (by rfl) ⟨278258, by rfl⟩ : syracuseStep 1484045 = 556517) (by norm_num)
theorem B992525 : Blo 658307 992525 := bbase (se 3 (by rfl) ⟨186098, by rfl⟩ : syracuseStep 992525 = 372197) (by norm_num)
theorem B1254685 : Blo 658307 1254685 := bbase (se 3 (by rfl) ⟨235253, by rfl⟩ : syracuseStep 1254685 = 470507) (by norm_num)
theorem B992549 : Blo 658307 992549 := bbase (se 4 (by rfl) ⟨93051, by rfl⟩ : syracuseStep 992549 = 186103) (by norm_num)
theorem B2499893 : Blo 658307 2499893 := bbase (se 5 (by rfl) ⟨117182, by rfl⟩ : syracuseStep 2499893 = 234365) (by norm_num)
theorem B992573 : Blo 658307 992573 := bbase (se 3 (by rfl) ⟨186107, by rfl⟩ : syracuseStep 992573 = 372215) (by norm_num)
theorem B1484117 : Blo 658307 1484117 := bbase (se 12 (by rfl) ⟨543, by rfl⟩ : syracuseStep 1484117 = 1087) (by norm_num)
theorem B992597 : Blo 658307 992597 := bbase (se 12 (by rfl) ⟨363, by rfl⟩ : syracuseStep 992597 = 727) (by norm_num)
theorem B1058141 : Blo 658307 1058141 := bbase (se 3 (by rfl) ⟨198401, by rfl⟩ : syracuseStep 1058141 = 396803) (by norm_num)
theorem B992621 : Blo 658307 992621 := bbase (se 3 (by rfl) ⟨186116, by rfl⟩ : syracuseStep 992621 = 372233) (by norm_num)
theorem B1877381 : Blo 658307 1877381 := bbase (se 4 (by rfl) ⟨176004, by rfl⟩ : syracuseStep 1877381 = 352009) (by norm_num)
theorem B992645 : Blo 658307 992645 := bbase (se 4 (by rfl) ⟨93060, by rfl⟩ : syracuseStep 992645 = 186121) (by norm_num)
theorem B3351941 : Blo 658307 3351941 := bbase (se 4 (by rfl) ⟨314244, by rfl⟩ : syracuseStep 3351941 = 628489) (by norm_num)
theorem B1484189 : Blo 658307 1484189 := bbase (se 3 (by rfl) ⟨278285, by rfl⟩ : syracuseStep 1484189 = 556571) (by norm_num)
theorem B992669 : Blo 658307 992669 := bbase (se 3 (by rfl) ⟨186125, by rfl⟩ : syracuseStep 992669 = 372251) (by norm_num)
theorem B992693 : Blo 658307 992693 := bbase (se 5 (by rfl) ⟨46532, by rfl⟩ : syracuseStep 992693 = 93065) (by norm_num)
theorem B1254845 : Blo 658307 1254845 := bbase (se 3 (by rfl) ⟨235283, by rfl⟩ : syracuseStep 1254845 = 470567) (by norm_num)
theorem B992717 : Blo 658307 992717 := bbase (se 3 (by rfl) ⟨186134, by rfl⟩ : syracuseStep 992717 = 372269) (by norm_num)
theorem B1058269 : Blo 658307 1058269 := bbase (se 3 (by rfl) ⟨198425, by rfl⟩ : syracuseStep 1058269 = 396851) (by norm_num)
theorem B1484261 : Blo 658307 1484261 := bbase (se 4 (by rfl) ⟨139149, by rfl⟩ : syracuseStep 1484261 = 278299) (by norm_num)
theorem B992741 : Blo 658307 992741 := bbase (se 4 (by rfl) ⟨93069, by rfl⟩ : syracuseStep 992741 = 186139) (by norm_num)
theorem B992765 : Blo 658307 992765 := bbase (se 3 (by rfl) ⟨186143, by rfl⟩ : syracuseStep 992765 = 372287) (by norm_num)
theorem B992789 : Blo 658307 992789 := bbase (se 6 (by rfl) ⟨23268, by rfl⟩ : syracuseStep 992789 = 46537) (by norm_num)
theorem B1484333 : Blo 658307 1484333 := bbase (se 3 (by rfl) ⟨278312, by rfl⟩ : syracuseStep 1484333 = 556625) (by norm_num)
theorem B992813 : Blo 658307 992813 := bbase (se 3 (by rfl) ⟨186152, by rfl⟩ : syracuseStep 992813 = 372305) (by norm_num)
theorem B992837 : Blo 658307 992837 := bbase (se 4 (by rfl) ⟨93078, by rfl⟩ : syracuseStep 992837 = 186157) (by norm_num)
theorem B1254989 : Blo 658307 1254989 := bbase (se 3 (by rfl) ⟨235310, by rfl⟩ : syracuseStep 1254989 = 470621) (by norm_num)
theorem B992861 : Blo 658307 992861 := bbase (se 3 (by rfl) ⟨186161, by rfl⟩ : syracuseStep 992861 = 372323) (by norm_num)
theorem B1484405 : Blo 658307 1484405 := bbase (se 5 (by rfl) ⟨69581, by rfl⟩ : syracuseStep 1484405 = 139163) (by norm_num)
theorem B992885 : Blo 658307 992885 := bbase (se 5 (by rfl) ⟨46541, by rfl⟩ : syracuseStep 992885 = 93083) (by norm_num)
theorem B992909 : Blo 658307 992909 := bbase (se 3 (by rfl) ⟨186170, by rfl⟩ : syracuseStep 992909 = 372341) (by norm_num)
theorem B992933 : Blo 658307 992933 := bbase (se 4 (by rfl) ⟨93087, by rfl⟩ : syracuseStep 992933 = 186175) (by norm_num)
theorem B1484477 : Blo 658307 1484477 := bbase (se 3 (by rfl) ⟨278339, by rfl⟩ : syracuseStep 1484477 = 556679) (by norm_num)
theorem B992957 : Blo 658307 992957 := bbase (se 3 (by rfl) ⟨186179, by rfl⟩ : syracuseStep 992957 = 372359) (by norm_num)
theorem B992981 : Blo 658307 992981 := bbase (se 7 (by rfl) ⟨11636, by rfl⟩ : syracuseStep 992981 = 23273) (by norm_num)
theorem B993005 : Blo 658307 993005 := bbase (se 3 (by rfl) ⟨186188, by rfl⟩ : syracuseStep 993005 = 372377) (by norm_num)
theorem B1484549 : Blo 658307 1484549 := bbase (se 4 (by rfl) ⟨139176, by rfl⟩ : syracuseStep 1484549 = 278353) (by norm_num)
theorem B993029 : Blo 658307 993029 := bbase (se 4 (by rfl) ⟨93096, by rfl⟩ : syracuseStep 993029 = 186193) (by norm_num)
theorem B993053 : Blo 658307 993053 := bbase (se 3 (by rfl) ⟨186197, by rfl⟩ : syracuseStep 993053 = 372395) (by norm_num)
theorem B1877813 : Blo 658307 1877813 := bbase (se 5 (by rfl) ⟨88022, by rfl⟩ : syracuseStep 1877813 = 176045) (by norm_num)
theorem B993077 : Blo 658307 993077 := bbase (se 5 (by rfl) ⟨46550, by rfl⟩ : syracuseStep 993077 = 93101) (by norm_num)
theorem B1484621 : Blo 658307 1484621 := bbase (se 3 (by rfl) ⟨278366, by rfl⟩ : syracuseStep 1484621 = 556733) (by norm_num)
theorem B993101 : Blo 658307 993101 := bbase (se 3 (by rfl) ⟨186206, by rfl⟩ : syracuseStep 993101 = 372413) (by norm_num)
theorem B993125 : Blo 658307 993125 := bbase (se 4 (by rfl) ⟨93105, by rfl⟩ : syracuseStep 993125 = 186211) (by norm_num)
theorem B1255277 : Blo 658307 1255277 := bbase (se 3 (by rfl) ⟨235364, by rfl⟩ : syracuseStep 1255277 = 470729) (by norm_num)
theorem B993149 : Blo 658307 993149 := bbase (se 3 (by rfl) ⟨186215, by rfl⟩ : syracuseStep 993149 = 372431) (by norm_num)
theorem B1484693 : Blo 658307 1484693 := bbase (se 6 (by rfl) ⟨34797, by rfl⟩ : syracuseStep 1484693 = 69595) (by norm_num)
theorem B993173 : Blo 658307 993173 := bbase (se 6 (by rfl) ⟨23277, by rfl⟩ : syracuseStep 993173 = 46555) (by norm_num)
theorem B1583021 : Blo 658307 1583021 := bbase (se 3 (by rfl) ⟨296816, by rfl⟩ : syracuseStep 1583021 = 593633) (by norm_num)
theorem B993197 : Blo 658307 993197 := bbase (se 3 (by rfl) ⟨186224, by rfl⟩ : syracuseStep 993197 = 372449) (by norm_num)
theorem B993221 : Blo 658307 993221 := bbase (se 4 (by rfl) ⟨93114, by rfl⟩ : syracuseStep 993221 = 186229) (by norm_num)
theorem B1484765 : Blo 658307 1484765 := bbase (se 3 (by rfl) ⟨278393, by rfl⟩ : syracuseStep 1484765 = 556787) (by norm_num)
theorem B993245 : Blo 658307 993245 := bbase (se 3 (by rfl) ⟨186233, by rfl⟩ : syracuseStep 993245 = 372467) (by norm_num)
theorem B993269 : Blo 658307 993269 := bbase (se 5 (by rfl) ⟨46559, by rfl⟩ : syracuseStep 993269 = 93119) (by norm_num)
theorem B1255429 : Blo 658307 1255429 := bbase (se 4 (by rfl) ⟨117696, by rfl⟩ : syracuseStep 1255429 = 235393) (by norm_num)
theorem B993293 : Blo 658307 993293 := bbase (se 3 (by rfl) ⟨186242, by rfl⟩ : syracuseStep 993293 = 372485) (by norm_num)
theorem B1484837 : Blo 658307 1484837 := bbase (se 4 (by rfl) ⟨139203, by rfl⟩ : syracuseStep 1484837 = 278407) (by norm_num)
theorem B993317 : Blo 658307 993317 := bbase (se 4 (by rfl) ⟨93123, by rfl⟩ : syracuseStep 993317 = 186247) (by norm_num)
theorem B1189933 : Blo 658307 1189933 := bbase (se 3 (by rfl) ⟨223112, by rfl⟩ : syracuseStep 1189933 = 446225) (by norm_num)
theorem B993341 : Blo 658307 993341 := bbase (se 3 (by rfl) ⟨186251, by rfl⟩ : syracuseStep 993341 = 372503) (by norm_num)
theorem B993365 : Blo 658307 993365 := bbase (se 8 (by rfl) ⟨5820, by rfl⟩ : syracuseStep 993365 = 11641) (by norm_num)
theorem B1484909 : Blo 658307 1484909 := bbase (se 3 (by rfl) ⟨278420, by rfl⟩ : syracuseStep 1484909 = 556841) (by norm_num)
theorem B993389 : Blo 658307 993389 := bbase (se 3 (by rfl) ⟨186260, by rfl⟩ : syracuseStep 993389 = 372521) (by norm_num)
theorem B993413 : Blo 658307 993413 := bbase (se 4 (by rfl) ⟨93132, by rfl⟩ : syracuseStep 993413 = 186265) (by norm_num)
theorem B4761749 : Blo 658307 4761749 := bbase (se 6 (by rfl) ⟨111603, by rfl⟩ : syracuseStep 4761749 = 223207) (by norm_num)
theorem B993437 : Blo 658307 993437 := bbase (se 3 (by rfl) ⟨186269, by rfl⟩ : syracuseStep 993437 = 372539) (by norm_num)
theorem B1484981 : Blo 658307 1484981 := bbase (se 5 (by rfl) ⟨69608, by rfl⟩ : syracuseStep 1484981 = 139217) (by norm_num)
theorem B993461 : Blo 658307 993461 := bbase (se 5 (by rfl) ⟨46568, by rfl⟩ : syracuseStep 993461 = 93137) (by norm_num)
theorem B1485053 : Blo 658307 1485053 := bbase (se 3 (by rfl) ⟨278447, by rfl⟩ : syracuseStep 1485053 = 556895) (by norm_num)
theorem B1255733 : Blo 658307 1255733 := bbase (se 5 (by rfl) ⟨58862, by rfl⟩ : syracuseStep 1255733 = 117725) (by norm_num)
theorem B1485125 : Blo 658307 1485125 := bbase (se 4 (by rfl) ⟨139230, by rfl⟩ : syracuseStep 1485125 = 278461) (by norm_num)
theorem B7317845 : Blo 658307 7317845 := bbase (se 10 (by rfl) ⟨10719, by rfl⟩ : syracuseStep 7317845 = 21439) (by norm_num)
theorem B1485197 : Blo 658307 1485197 := bbase (se 3 (by rfl) ⟨278474, by rfl⟩ : syracuseStep 1485197 = 556949) (by norm_num)
theorem B2501077 : Blo 658307 2501077 := bbase (se 7 (by rfl) ⟨29309, by rfl⟩ : syracuseStep 2501077 = 58619) (by norm_num)
theorem B1485269 : Blo 658307 1485269 := bbase (se 7 (by rfl) ⟨17405, by rfl⟩ : syracuseStep 1485269 = 34811) (by norm_num)
theorem B1485341 : Blo 658307 1485341 := bbase (se 3 (by rfl) ⟨278501, by rfl⟩ : syracuseStep 1485341 = 557003) (by norm_num)
theorem B1878565 : Blo 658307 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B1485413 : Blo 658307 1485413 := bbase (se 4 (by rfl) ⟨139257, by rfl⟩ : syracuseStep 1485413 = 278515) (by norm_num)
theorem B1485485 : Blo 658307 1485485 := bbase (se 3 (by rfl) ⟨278528, by rfl⟩ : syracuseStep 1485485 = 557057) (by norm_num)
theorem B1288885 : Blo 658307 1288885 := bbase (se 5 (by rfl) ⟨60416, by rfl⟩ : syracuseStep 1288885 = 120833) (by norm_num)
theorem B1485557 : Blo 658307 1485557 := bbase (se 5 (by rfl) ⟨69635, by rfl⟩ : syracuseStep 1485557 = 139271) (by norm_num)
theorem B2501381 : Blo 658307 2501381 := bbase (se 4 (by rfl) ⟨234504, by rfl⟩ : syracuseStep 2501381 = 469009) (by norm_num)
theorem B1485629 : Blo 658307 1485629 := bbase (se 3 (by rfl) ⟨278555, by rfl⟩ : syracuseStep 1485629 = 557111) (by norm_num)
theorem B1059653 : Blo 658307 1059653 := bbase (se 4 (by rfl) ⟨99342, by rfl⟩ : syracuseStep 1059653 = 198685) (by norm_num)
theorem B1485701 : Blo 658307 1485701 := bbase (se 4 (by rfl) ⟨139284, by rfl⟩ : syracuseStep 1485701 = 278569) (by norm_num)
theorem B1485773 : Blo 658307 1485773 := bbase (se 3 (by rfl) ⟨278582, by rfl⟩ : syracuseStep 1485773 = 557165) (by norm_num)
theorem B1485845 : Blo 658307 1485845 := bbase (se 6 (by rfl) ⟨34824, by rfl⟩ : syracuseStep 1485845 = 69649) (by norm_num)
theorem B1256485 : Blo 658307 1256485 := bbase (se 4 (by rfl) ⟨117795, by rfl⟩ : syracuseStep 1256485 = 235591) (by norm_num)
theorem B765017 : Blo 658307 765017 := bbase (se 2 (by rfl) ⟨286881, by rfl⟩ : syracuseStep 765017 = 573763) (by norm_num)
theorem B1485917 : Blo 658307 1485917 := bbase (se 3 (by rfl) ⟨278609, by rfl⟩ : syracuseStep 1485917 = 557219) (by norm_num)
theorem B1485989 : Blo 658307 1485989 := bbase (se 4 (by rfl) ⟨139311, by rfl⟩ : syracuseStep 1485989 = 278623) (by norm_num)
theorem B1256629 : Blo 658307 1256629 := bbase (se 5 (by rfl) ⟨58904, by rfl⟩ : syracuseStep 1256629 = 117809) (by norm_num)
theorem B1486061 : Blo 658307 1486061 := bbase (se 3 (by rfl) ⟨278636, by rfl⟩ : syracuseStep 1486061 = 557273) (by norm_num)
theorem B1191181 : Blo 658307 1191181 := bbase (se 3 (by rfl) ⟨223346, by rfl⟩ : syracuseStep 1191181 = 446693) (by norm_num)
theorem B1486133 : Blo 658307 1486133 := bbase (se 5 (by rfl) ⟨69662, by rfl⟩ : syracuseStep 1486133 = 139325) (by norm_num)
theorem B1256789 : Blo 658307 1256789 := bbase (se 11 (by rfl) ⟨920, by rfl⟩ : syracuseStep 1256789 = 1841) (by norm_num)
theorem B1486205 : Blo 658307 1486205 := bbase (se 3 (by rfl) ⟨278663, by rfl⟩ : syracuseStep 1486205 = 557327) (by norm_num)
theorem B1486277 : Blo 658307 1486277 := bbase (se 4 (by rfl) ⟨139338, by rfl⟩ : syracuseStep 1486277 = 278677) (by norm_num)
theorem B1256933 : Blo 658307 1256933 := bbase (se 4 (by rfl) ⟨117837, by rfl⟩ : syracuseStep 1256933 = 235675) (by norm_num)
theorem B1486349 : Blo 658307 1486349 := bbase (se 3 (by rfl) ⟨278690, by rfl⟩ : syracuseStep 1486349 = 557381) (by norm_num)
theorem B929333 : Blo 658307 929333 := bbase (se 5 (by rfl) ⟨43562, by rfl⟩ : syracuseStep 929333 = 87125) (by norm_num)
theorem B1486421 : Blo 658307 1486421 := bbase (se 8 (by rfl) ⟨8709, by rfl⟩ : syracuseStep 1486421 = 17419) (by norm_num)
theorem B3059333 : Blo 658307 3059333 := bbase (se 4 (by rfl) ⟨286812, by rfl⟩ : syracuseStep 3059333 = 573625) (by norm_num)
theorem B7614101 : Blo 658307 7614101 := bbase (se 6 (by rfl) ⟨178455, by rfl⟩ : syracuseStep 7614101 = 356911) (by norm_num)
theorem B1486493 : Blo 658307 1486493 := bbase (se 3 (by rfl) ⟨278717, by rfl⟩ : syracuseStep 1486493 = 557435) (by norm_num)
theorem B1486565 : Blo 658307 1486565 := bbase (se 4 (by rfl) ⟨139365, by rfl⟩ : syracuseStep 1486565 = 278731) (by norm_num)
theorem B1060589 : Blo 658307 1060589 := bbase (se 3 (by rfl) ⟨198860, by rfl⟩ : syracuseStep 1060589 = 397721) (by norm_num)
theorem B1257221 : Blo 658307 1257221 := bbase (se 4 (by rfl) ⟨117864, by rfl⟩ : syracuseStep 1257221 = 235729) (by norm_num)
theorem B4239125 : Blo 658307 4239125 := bbase (se 6 (by rfl) ⟨99354, by rfl⟩ : syracuseStep 4239125 = 198709) (by norm_num)
theorem B1486637 : Blo 658307 1486637 := bbase (se 3 (by rfl) ⟨278744, by rfl⟩ : syracuseStep 1486637 = 557489) (by norm_num)
theorem B7515989 : Blo 658307 7515989 := bbase (se 9 (by rfl) ⟨22019, by rfl⟩ : syracuseStep 7515989 = 44039) (by norm_num)
theorem B1486709 : Blo 658307 1486709 := bbase (se 5 (by rfl) ⟨69689, by rfl⟩ : syracuseStep 1486709 = 139379) (by norm_num)
theorem B3387253 : Blo 658307 3387253 := bbase (se 5 (by rfl) ⟨158777, by rfl⟩ : syracuseStep 3387253 = 317555) (by norm_num)
theorem B1585021 : Blo 658307 1585021 := bbase (se 3 (by rfl) ⟨297191, by rfl⟩ : syracuseStep 1585021 = 594383) (by norm_num)
theorem B1486781 : Blo 658307 1486781 := bbase (se 3 (by rfl) ⟨278771, by rfl⟩ : syracuseStep 1486781 = 557543) (by norm_num)
theorem B1486853 : Blo 658307 1486853 := bbase (se 4 (by rfl) ⟨139392, by rfl⟩ : syracuseStep 1486853 = 278785) (by norm_num)
theorem B1585165 : Blo 658307 1585165 := bbase (se 3 (by rfl) ⟨297218, by rfl⟩ : syracuseStep 1585165 = 594437) (by norm_num)
theorem B1486925 : Blo 658307 1486925 := bbase (se 3 (by rfl) ⟨278798, by rfl⟩ : syracuseStep 1486925 = 557597) (by norm_num)
theorem B1486997 : Blo 658307 1486997 := bbase (se 6 (by rfl) ⟨34851, by rfl⟩ : syracuseStep 1486997 = 69703) (by norm_num)
theorem B1487069 : Blo 658307 1487069 := bbase (se 3 (by rfl) ⟨278825, by rfl⟩ : syracuseStep 1487069 = 557651) (by norm_num)
theorem B1487141 : Blo 658307 1487141 := bbase (se 4 (by rfl) ⟨139419, by rfl⟩ : syracuseStep 1487141 = 278839) (by norm_num)
theorem B1782101 : Blo 658307 1782101 := bbase (se 10 (by rfl) ⟨2610, by rfl⟩ : syracuseStep 1782101 = 5221) (by norm_num)
theorem B2011493 : Blo 658307 2011493 := bbase (se 4 (by rfl) ⟨188577, by rfl⟩ : syracuseStep 2011493 = 377155) (by norm_num)
theorem B1487213 : Blo 658307 1487213 := bbase (se 3 (by rfl) ⟨278852, by rfl⟩ : syracuseStep 1487213 = 557705) (by norm_num)
theorem B1487285 : Blo 658307 1487285 := bbase (se 5 (by rfl) ⟨69716, by rfl⟩ : syracuseStep 1487285 = 139433) (by norm_num)
theorem B668093 : Blo 658307 668093 := bbase (se 3 (by rfl) ⟨125267, by rfl⟩ : syracuseStep 668093 = 250535) (by norm_num)
theorem B5648885 : Blo 658307 5648885 := bbase (se 5 (by rfl) ⟨264791, by rfl⟩ : syracuseStep 5648885 = 529583) (by norm_num)
theorem B1487357 : Blo 658307 1487357 := bbase (se 3 (by rfl) ⟨278879, by rfl⟩ : syracuseStep 1487357 = 557759) (by norm_num)
theorem B1487429 : Blo 658307 1487429 := bbase (se 4 (by rfl) ⟨139446, by rfl⟩ : syracuseStep 1487429 = 278893) (by norm_num)
theorem B1585781 : Blo 658307 1585781 := bbase (se 5 (by rfl) ⟨74333, by rfl⟩ : syracuseStep 1585781 = 148667) (by norm_num)
theorem B1192565 : Blo 658307 1192565 := bbase (se 5 (by rfl) ⟨55901, by rfl⟩ : syracuseStep 1192565 = 111803) (by norm_num)
theorem B1487501 : Blo 658307 1487501 := bbase (se 3 (by rfl) ⟨278906, by rfl⟩ : syracuseStep 1487501 = 557813) (by norm_num)
theorem B1487573 : Blo 658307 1487573 := bbase (se 7 (by rfl) ⟨17432, by rfl⟩ : syracuseStep 1487573 = 34865) (by norm_num)
theorem B1487645 : Blo 658307 1487645 := bbase (se 3 (by rfl) ⟨278933, by rfl⟩ : syracuseStep 1487645 = 557867) (by norm_num)
theorem B2503493 : Blo 658307 2503493 := bbase (se 4 (by rfl) ⟨234702, by rfl⟩ : syracuseStep 2503493 = 469405) (by norm_num)
theorem B1487717 : Blo 658307 1487717 := bbase (se 4 (by rfl) ⟨139473, by rfl⟩ : syracuseStep 1487717 = 278947) (by norm_num)
theorem B1487789 : Blo 658307 1487789 := bbase (se 3 (by rfl) ⟨278960, by rfl⟩ : syracuseStep 1487789 = 557921) (by norm_num)
theorem B1586117 : Blo 658307 1586117 := bbase (se 4 (by rfl) ⟨148698, by rfl⟩ : syracuseStep 1586117 = 297397) (by norm_num)
theorem B1487861 : Blo 658307 1487861 := bbase (se 5 (by rfl) ⟨69743, by rfl⟩ : syracuseStep 1487861 = 139487) (by norm_num)
theorem B668665 : Blo 658307 668665 := bbase (se 2 (by rfl) ⟨250749, by rfl⟩ : syracuseStep 668665 = 501499) (by norm_num)
theorem B1586213 : Blo 658307 1586213 := bbase (se 4 (by rfl) ⟨148707, by rfl⟩ : syracuseStep 1586213 = 297415) (by norm_num)
theorem B1487933 : Blo 658307 1487933 := bbase (se 3 (by rfl) ⟨278987, by rfl⟩ : syracuseStep 1487933 = 557975) (by norm_num)
theorem B2503781 : Blo 658307 2503781 := bbase (se 4 (by rfl) ⟨234729, by rfl⟩ : syracuseStep 2503781 = 469459) (by norm_num)
theorem B1488005 : Blo 658307 1488005 := bbase (se 4 (by rfl) ⟨139500, by rfl⟩ : syracuseStep 1488005 = 279001) (by norm_num)
theorem B2012357 : Blo 658307 2012357 := bbase (se 4 (by rfl) ⟨188658, by rfl⟩ : syracuseStep 2012357 = 377317) (by norm_num)
theorem B1488077 : Blo 658307 1488077 := bbase (se 3 (by rfl) ⟨279014, by rfl⟩ : syracuseStep 1488077 = 558029) (by norm_num)
theorem B1586405 : Blo 658307 1586405 := bbase (se 4 (by rfl) ⟨148725, by rfl⟩ : syracuseStep 1586405 = 297451) (by norm_num)
theorem B4568309 : Blo 658307 4568309 := bbase (se 5 (by rfl) ⟨214139, by rfl⟩ : syracuseStep 4568309 = 428279) (by norm_num)
theorem B1488149 : Blo 658307 1488149 := bbase (se 6 (by rfl) ⟨34878, by rfl⟩ : syracuseStep 1488149 = 69757) (by norm_num)
theorem B1881413 : Blo 658307 1881413 := bbase (se 4 (by rfl) ⟨176382, by rfl⟩ : syracuseStep 1881413 = 352765) (by norm_num)
theorem B1488221 : Blo 658307 1488221 := bbase (se 3 (by rfl) ⟨279041, by rfl⟩ : syracuseStep 1488221 = 558083) (by norm_num)
theorem B1488293 : Blo 658307 1488293 := bbase (se 4 (by rfl) ⟨139527, by rfl⟩ : syracuseStep 1488293 = 279055) (by norm_num)
theorem B1488365 : Blo 658307 1488365 := bbase (se 3 (by rfl) ⟨279068, by rfl⟩ : syracuseStep 1488365 = 558137) (by norm_num)
theorem B3749429 : Blo 658307 3749429 := bbase (se 5 (by rfl) ⟨175754, by rfl⟩ : syracuseStep 3749429 = 351509) (by norm_num)
theorem B1488437 : Blo 658307 1488437 := bbase (se 5 (by rfl) ⟨69770, by rfl⟩ : syracuseStep 1488437 = 139541) (by norm_num)
theorem B2111093 : Blo 658307 2111093 := bbase (se 5 (by rfl) ⟨98957, by rfl⟩ : syracuseStep 2111093 = 197915) (by norm_num)
theorem B1488509 : Blo 658307 1488509 := bbase (se 3 (by rfl) ⟨279095, by rfl⟩ : syracuseStep 1488509 = 558191) (by norm_num)
theorem B1488581 : Blo 658307 1488581 := bbase (se 4 (by rfl) ⟨139554, by rfl⟩ : syracuseStep 1488581 = 279109) (by norm_num)
theorem B833257 : Blo 658307 833257 := bbase (se 2 (by rfl) ⟨312471, by rfl⟩ : syracuseStep 833257 = 624943) (by norm_num)
theorem B1488653 : Blo 658307 1488653 := bbase (se 3 (by rfl) ⟨279122, by rfl⟩ : syracuseStep 1488653 = 558245) (by norm_num)
theorem B1488725 : Blo 658307 1488725 := bbase (se 9 (by rfl) ⟨4361, by rfl⟩ : syracuseStep 1488725 = 8723) (by norm_num)
theorem B5027669 : Blo 658307 5027669 := bbase (se 9 (by rfl) ⟨14729, by rfl⟩ : syracuseStep 5027669 = 29459) (by norm_num)
theorem B669541 : Blo 658307 669541 := bbase (se 4 (by rfl) ⟨62769, by rfl⟩ : syracuseStep 669541 = 125539) (by norm_num)
theorem B833429 : Blo 658307 833429 := bbase (se 6 (by rfl) ⟨19533, by rfl⟩ : syracuseStep 833429 = 39067) (by norm_num)
theorem B1488797 : Blo 658307 1488797 := bbase (se 3 (by rfl) ⟨279149, by rfl⟩ : syracuseStep 1488797 = 558299) (by norm_num)
theorem B833485 : Blo 658307 833485 := bbase (se 3 (by rfl) ⟨156278, by rfl⟩ : syracuseStep 833485 = 312557) (by norm_num)
theorem B1488869 : Blo 658307 1488869 := bbase (se 4 (by rfl) ⟨139581, by rfl⟩ : syracuseStep 1488869 = 279163) (by norm_num)
theorem B833581 : Blo 658307 833581 := bbase (se 3 (by rfl) ⟨156296, by rfl⟩ : syracuseStep 833581 = 312593) (by norm_num)
theorem B1488941 : Blo 658307 1488941 := bbase (se 3 (by rfl) ⟨279176, by rfl⟩ : syracuseStep 1488941 = 558353) (by norm_num)
theorem B1489013 : Blo 658307 1489013 := bbase (se 5 (by rfl) ⟨69797, by rfl⟩ : syracuseStep 1489013 = 139595) (by norm_num)
theorem B669881 : Blo 658307 669881 := bbase (se 2 (by rfl) ⟨251205, by rfl⟩ : syracuseStep 669881 = 502411) (by norm_num)
theorem B1489085 : Blo 658307 1489085 := bbase (se 3 (by rfl) ⟨279203, by rfl⟩ : syracuseStep 1489085 = 558407) (by norm_num)
theorem B833753 : Blo 658307 833753 := bbase (se 2 (by rfl) ⟨312657, by rfl⟩ : syracuseStep 833753 = 625315) (by norm_num)
theorem B669913 : Blo 658307 669913 := bbase (se 2 (by rfl) ⟨251217, by rfl⟩ : syracuseStep 669913 = 502435) (by norm_num)
theorem B2504965 : Blo 658307 2504965 := bbase (se 4 (by rfl) ⟨234840, by rfl⟩ : syracuseStep 2504965 = 469681) (by norm_num)
theorem B1489157 : Blo 658307 1489157 := bbase (se 4 (by rfl) ⟨139608, by rfl⟩ : syracuseStep 1489157 = 279217) (by norm_num)
theorem B833809 : Blo 658307 833809 := bbase (se 2 (by rfl) ⟨312678, by rfl⟩ : syracuseStep 833809 = 625357) (by norm_num)
theorem B2406725 : Blo 658307 2406725 := bbase (se 4 (by rfl) ⟨225630, by rfl⟩ : syracuseStep 2406725 = 451261) (by norm_num)
theorem B1489229 : Blo 658307 1489229 := bbase (se 3 (by rfl) ⟨279230, by rfl⟩ : syracuseStep 1489229 = 558461) (by norm_num)
theorem B1587557 : Blo 658307 1587557 := bbase (se 4 (by rfl) ⟨148833, by rfl⟩ : syracuseStep 1587557 = 297667) (by norm_num)
theorem B833905 : Blo 658307 833905 := bbase (se 2 (by rfl) ⟨312714, by rfl⟩ : syracuseStep 833905 = 625429) (by norm_num)
theorem B1489301 : Blo 658307 1489301 := bbase (se 6 (by rfl) ⟨34905, by rfl⟩ : syracuseStep 1489301 = 69811) (by norm_num)
theorem B1489373 : Blo 658307 1489373 := bbase (se 3 (by rfl) ⟨279257, by rfl⟩ : syracuseStep 1489373 = 558515) (by norm_num)
theorem B1882597 : Blo 658307 1882597 := bbase (se 4 (by rfl) ⟨176493, by rfl⟩ : syracuseStep 1882597 = 352987) (by norm_num)
theorem B834077 : Blo 658307 834077 := bbase (se 3 (by rfl) ⟨156389, by rfl⟩ : syracuseStep 834077 = 312779) (by norm_num)
theorem B1489445 : Blo 658307 1489445 := bbase (se 4 (by rfl) ⟨139635, by rfl⟩ : syracuseStep 1489445 = 279271) (by norm_num)
theorem B2505269 : Blo 658307 2505269 := bbase (se 5 (by rfl) ⟨117434, by rfl⟩ : syracuseStep 2505269 = 234869) (by norm_num)
theorem B834133 : Blo 658307 834133 := bbase (se 8 (by rfl) ⟨4887, by rfl⟩ : syracuseStep 834133 = 9775) (by norm_num)
theorem B1489517 : Blo 658307 1489517 := bbase (se 3 (by rfl) ⟨279284, by rfl⟩ : syracuseStep 1489517 = 558569) (by norm_num)
theorem B1882757 : Blo 658307 1882757 := bbase (se 4 (by rfl) ⟨176508, by rfl⟩ : syracuseStep 1882757 = 353017) (by norm_num)
theorem B703117 : Blo 658307 703117 := bbase (se 3 (by rfl) ⟨131834, by rfl⟩ : syracuseStep 703117 = 263669) (by norm_num)
theorem B834229 : Blo 658307 834229 := bbase (se 5 (by rfl) ⟨39104, by rfl⟩ : syracuseStep 834229 = 78209) (by norm_num)
theorem B1489589 : Blo 658307 1489589 := bbase (se 5 (by rfl) ⟨69824, by rfl⟩ : syracuseStep 1489589 = 139649) (by norm_num)
theorem B703189 : Blo 658307 703189 := bbase (se 7 (by rfl) ⟨8240, by rfl⟩ : syracuseStep 703189 = 16481) (by norm_num)
theorem B670441 : Blo 658307 670441 := bbase (se 2 (by rfl) ⟨251415, by rfl⟩ : syracuseStep 670441 = 502831) (by norm_num)
theorem B1489661 : Blo 658307 1489661 := bbase (se 3 (by rfl) ⟨279311, by rfl⟩ : syracuseStep 1489661 = 558623) (by norm_num)
theorem B670465 : Blo 658307 670465 := bbase (se 2 (by rfl) ⟨251424, by rfl⟩ : syracuseStep 670465 = 502849) (by norm_num)
theorem B1489733 : Blo 658307 1489733 := bbase (se 4 (by rfl) ⟨139662, by rfl⟩ : syracuseStep 1489733 = 279325) (by norm_num)
theorem B834401 : Blo 658307 834401 := bbase (se 2 (by rfl) ⟨312900, by rfl⟩ : syracuseStep 834401 = 625801) (by norm_num)
theorem B1882997 : Blo 658307 1882997 := bbase (se 5 (by rfl) ⟨88265, by rfl⟩ : syracuseStep 1882997 = 176531) (by norm_num)
theorem B1489805 : Blo 658307 1489805 := bbase (se 3 (by rfl) ⟨279338, by rfl⟩ : syracuseStep 1489805 = 558677) (by norm_num)
theorem B834457 : Blo 658307 834457 := bbase (se 2 (by rfl) ⟨312921, by rfl⟩ : syracuseStep 834457 = 625843) (by norm_num)
theorem B2112437 : Blo 658307 2112437 := bbase (se 5 (by rfl) ⟨99020, by rfl⟩ : syracuseStep 2112437 = 198041) (by norm_num)
theorem B1489877 : Blo 658307 1489877 := bbase (se 7 (by rfl) ⟨17459, by rfl⟩ : syracuseStep 1489877 = 34919) (by norm_num)
theorem B834553 : Blo 658307 834553 := bbase (se 2 (by rfl) ⟨312957, by rfl⟩ : syracuseStep 834553 = 625915) (by norm_num)
theorem B1489949 : Blo 658307 1489949 := bbase (se 3 (by rfl) ⟨279365, by rfl⟩ : syracuseStep 1489949 = 558731) (by norm_num)
theorem B1883189 : Blo 658307 1883189 := bbase (se 5 (by rfl) ⟨88274, by rfl⟩ : syracuseStep 1883189 = 176549) (by norm_num)
theorem B670789 : Blo 658307 670789 := bbase (se 4 (by rfl) ⟨62886, by rfl⟩ : syracuseStep 670789 = 125773) (by norm_num)
theorem B703561 : Blo 658307 703561 := bbase (se 2 (by rfl) ⟨263835, by rfl⟩ : syracuseStep 703561 = 527671) (by norm_num)
theorem B1490021 : Blo 658307 1490021 := bbase (se 4 (by rfl) ⟨139689, by rfl⟩ : syracuseStep 1490021 = 279379) (by norm_num)
theorem B834725 : Blo 658307 834725 := bbase (se 4 (by rfl) ⟨78255, by rfl⟩ : syracuseStep 834725 = 156511) (by norm_num)
theorem B1490093 : Blo 658307 1490093 := bbase (se 3 (by rfl) ⟨279392, by rfl⟩ : syracuseStep 1490093 = 558785) (by norm_num)
theorem B834781 : Blo 658307 834781 := bbase (se 3 (by rfl) ⟨156521, by rfl⟩ : syracuseStep 834781 = 313043) (by norm_num)
theorem B1490165 : Blo 658307 1490165 := bbase (se 5 (by rfl) ⟨69851, by rfl⟩ : syracuseStep 1490165 = 139703) (by norm_num)
theorem B834877 : Blo 658307 834877 := bbase (se 3 (by rfl) ⟨156539, by rfl⟩ : syracuseStep 834877 = 313079) (by norm_num)
theorem B2571605 : Blo 658307 2571605 := bbase (se 11 (by rfl) ⟨1883, by rfl⟩ : syracuseStep 2571605 = 3767) (by norm_num)
theorem B703937 : Blo 658307 703937 := bbase (se 2 (by rfl) ⟨263976, by rfl⟩ : syracuseStep 703937 = 527953) (by norm_num)
theorem B835049 : Blo 658307 835049 := bbase (se 2 (by rfl) ⟨313143, by rfl⟩ : syracuseStep 835049 = 626287) (by norm_num)
theorem B704009 : Blo 658307 704009 := bbase (se 2 (by rfl) ⟨264003, by rfl⟩ : syracuseStep 704009 = 528007) (by norm_num)
theorem B835105 : Blo 658307 835105 := bbase (se 2 (by rfl) ⟨313164, by rfl⟩ : syracuseStep 835105 = 626329) (by norm_num)
theorem B1785397 : Blo 658307 1785397 := bbase (se 5 (by rfl) ⟨83690, by rfl⟩ : syracuseStep 1785397 = 167381) (by norm_num)
theorem B835201 : Blo 658307 835201 := bbase (se 2 (by rfl) ⟨313200, by rfl⟩ : syracuseStep 835201 = 626401) (by norm_num)
theorem B704197 : Blo 658307 704197 := bbase (se 4 (by rfl) ⟨66018, by rfl⟩ : syracuseStep 704197 = 132037) (by norm_num)
theorem B835373 : Blo 658307 835373 := bbase (se 3 (by rfl) ⟨156632, by rfl⟩ : syracuseStep 835373 = 313265) (by norm_num)
theorem B802633 : Blo 658307 802633 := bbase (se 2 (by rfl) ⟨300987, by rfl⟩ : syracuseStep 802633 = 601975) (by norm_num)
theorem B835429 : Blo 658307 835429 := bbase (se 4 (by rfl) ⟨78321, by rfl⟩ : syracuseStep 835429 = 156643) (by norm_num)
theorem B704381 : Blo 658307 704381 := bbase (se 3 (by rfl) ⟨132071, by rfl⟩ : syracuseStep 704381 = 264143) (by norm_num)
theorem B835525 : Blo 658307 835525 := bbase (se 4 (by rfl) ⟨78330, by rfl⟩ : syracuseStep 835525 = 156661) (by norm_num)
theorem B1884181 : Blo 658307 1884181 := bbase (se 6 (by rfl) ⟨44160, by rfl⟩ : syracuseStep 1884181 = 88321) (by norm_num)
theorem B802877 : Blo 658307 802877 := bbase (se 3 (by rfl) ⟨150539, by rfl⟩ : syracuseStep 802877 = 301079) (by norm_num)
theorem B835697 : Blo 658307 835697 := bbase (se 2 (by rfl) ⟨313386, by rfl⟩ : syracuseStep 835697 = 626773) (by norm_num)
theorem B835753 : Blo 658307 835753 := bbase (se 2 (by rfl) ⟨313407, by rfl⟩ : syracuseStep 835753 = 626815) (by norm_num)
theorem B835849 : Blo 658307 835849 := bbase (se 2 (by rfl) ⟨313443, by rfl⟩ : syracuseStep 835849 = 626887) (by norm_num)
theorem B1589557 : Blo 658307 1589557 := bbase (se 5 (by rfl) ⟨74510, by rfl⟩ : syracuseStep 1589557 = 149021) (by norm_num)
theorem B1589653 : Blo 658307 1589653 := bbase (se 6 (by rfl) ⟨37257, by rfl⟩ : syracuseStep 1589653 = 74515) (by norm_num)
theorem B1130917 : Blo 658307 1130917 := bbase (se 4 (by rfl) ⟨106023, by rfl⟩ : syracuseStep 1130917 = 212047) (by norm_num)
theorem B836021 : Blo 658307 836021 := bbase (se 5 (by rfl) ⟨39188, by rfl⟩ : syracuseStep 836021 = 78377) (by norm_num)
theorem B836077 : Blo 658307 836077 := bbase (se 3 (by rfl) ⟨156764, by rfl⟩ : syracuseStep 836077 = 313529) (by norm_num)
theorem B836173 : Blo 658307 836173 := bbase (se 3 (by rfl) ⟨156782, by rfl⟩ : syracuseStep 836173 = 313565) (by norm_num)
theorem B705133 : Blo 658307 705133 := bbase (se 3 (by rfl) ⟨132212, by rfl⟩ : syracuseStep 705133 = 264425) (by norm_num)
theorem B2507381 : Blo 658307 2507381 := bbase (se 5 (by rfl) ⟨117533, by rfl⟩ : syracuseStep 2507381 = 235067) (by norm_num)
theorem B705205 : Blo 658307 705205 := bbase (se 5 (by rfl) ⟨33056, by rfl⟩ : syracuseStep 705205 = 66113) (by norm_num)
theorem B836345 : Blo 658307 836345 := bbase (se 2 (by rfl) ⟨313629, by rfl⟩ : syracuseStep 836345 = 627259) (by norm_num)
theorem B836401 : Blo 658307 836401 := bbase (se 2 (by rfl) ⟨313650, by rfl⟩ : syracuseStep 836401 = 627301) (by norm_num)
theorem B705385 : Blo 658307 705385 := bbase (se 2 (by rfl) ⟨264519, by rfl⟩ : syracuseStep 705385 = 529039) (by norm_num)
theorem B2114437 : Blo 658307 2114437 := bbase (se 4 (by rfl) ⟨198228, by rfl⟩ : syracuseStep 2114437 = 396457) (by norm_num)
theorem B836497 : Blo 658307 836497 := bbase (se 2 (by rfl) ⟨313686, by rfl⟩ : syracuseStep 836497 = 627373) (by norm_num)
theorem B2507669 : Blo 658307 2507669 := bbase (se 6 (by rfl) ⟨58773, by rfl⟩ : syracuseStep 2507669 = 117547) (by norm_num)
theorem B836669 : Blo 658307 836669 := bbase (se 3 (by rfl) ⟨156875, by rfl⟩ : syracuseStep 836669 = 313751) (by norm_num)
theorem B1885285 : Blo 658307 1885285 := bbase (se 4 (by rfl) ⟨176745, by rfl⟩ : syracuseStep 1885285 = 353491) (by norm_num)
theorem B836725 : Blo 658307 836725 := bbase (se 5 (by rfl) ⟨39221, by rfl⟩ : syracuseStep 836725 = 78443) (by norm_num)
theorem B836821 : Blo 658307 836821 := bbase (se 7 (by rfl) ⟨9806, by rfl⟩ : syracuseStep 836821 = 19613) (by norm_num)
theorem B705829 : Blo 658307 705829 := bbase (se 4 (by rfl) ⟨66171, by rfl⟩ : syracuseStep 705829 = 132343) (by norm_num)
theorem B836993 : Blo 658307 836993 := bbase (se 2 (by rfl) ⟨313872, by rfl⟩ : syracuseStep 836993 = 627745) (by norm_num)
theorem B705953 : Blo 658307 705953 := bbase (se 2 (by rfl) ⟨264732, by rfl⟩ : syracuseStep 705953 = 529465) (by norm_num)
theorem B837049 : Blo 658307 837049 := bbase (se 2 (by rfl) ⟨313893, by rfl⟩ : syracuseStep 837049 = 627787) (by norm_num)
theorem B1590749 : Blo 658307 1590749 := bbase (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) (by norm_num)
theorem B837145 : Blo 658307 837145 := bbase (se 2 (by rfl) ⟨313929, by rfl⟩ : syracuseStep 837145 = 627859) (by norm_num)
theorem B706205 : Blo 658307 706205 := bbase (se 3 (by rfl) ⟨132413, by rfl⟩ : syracuseStep 706205 = 264827) (by norm_num)
theorem B837317 : Blo 658307 837317 := bbase (se 4 (by rfl) ⟨78498, by rfl⟩ : syracuseStep 837317 = 156997) (by norm_num)
theorem B837373 : Blo 658307 837373 := bbase (se 3 (by rfl) ⟨157007, by rfl⟩ : syracuseStep 837373 = 314015) (by norm_num)
theorem B1132285 : Blo 658307 1132285 := bbase (se 3 (by rfl) ⟨212303, by rfl⟩ : syracuseStep 1132285 = 424607) (by norm_num)
theorem B837469 : Blo 658307 837469 := bbase (se 3 (by rfl) ⟨157025, by rfl⟩ : syracuseStep 837469 = 314051) (by norm_num)
theorem B837641 : Blo 658307 837641 := bbase (se 2 (by rfl) ⟨314115, by rfl⟩ : syracuseStep 837641 = 628231) (by norm_num)
theorem B3164197 : Blo 658307 3164197 := bbase (se 4 (by rfl) ⟨296643, by rfl⟩ : syracuseStep 3164197 = 593287) (by norm_num)
theorem B2508853 : Blo 658307 2508853 := bbase (se 5 (by rfl) ⟨117602, by rfl⟩ : syracuseStep 2508853 = 235205) (by norm_num)
theorem B837697 : Blo 658307 837697 := bbase (se 2 (by rfl) ⟨314136, by rfl⟩ : syracuseStep 837697 = 628273) (by norm_num)
theorem B706649 : Blo 658307 706649 := bbase (se 2 (by rfl) ⟨264993, by rfl⟩ : syracuseStep 706649 = 529987) (by norm_num)
theorem B837793 : Blo 658307 837793 := bbase (se 2 (by rfl) ⟨314172, by rfl⟩ : syracuseStep 837793 = 628345) (by norm_num)
theorem B837965 : Blo 658307 837965 := bbase (se 3 (by rfl) ⟨157118, by rfl⟩ : syracuseStep 837965 = 314237) (by norm_num)
theorem B706897 : Blo 658307 706897 := bbase (se 2 (by rfl) ⟨265086, by rfl⟩ : syracuseStep 706897 = 530173) (by norm_num)
theorem B2509157 : Blo 658307 2509157 := bbase (se 4 (by rfl) ⟨235233, by rfl⟩ : syracuseStep 2509157 = 470467) (by norm_num)
theorem B838021 : Blo 658307 838021 := bbase (se 4 (by rfl) ⟨78564, by rfl⟩ : syracuseStep 838021 = 157129) (by norm_num)
theorem B838117 : Blo 658307 838117 := bbase (se 4 (by rfl) ⟨78573, by rfl⟩ : syracuseStep 838117 = 157147) (by norm_num)
theorem B2542085 : Blo 658307 2542085 := bbase (se 4 (by rfl) ⟨238320, by rfl⟩ : syracuseStep 2542085 = 476641) (by norm_num)
theorem B1002341 : Blo 658307 1002341 := bbase (se 4 (by rfl) ⟨93969, by rfl⟩ : syracuseStep 1002341 = 187939) (by norm_num)
theorem B904133 : Blo 658307 904133 := bbase (se 4 (by rfl) ⟨84762, by rfl⟩ : syracuseStep 904133 = 169525) (by norm_num)
theorem B1690669 : Blo 658307 1690669 := bbase (se 3 (by rfl) ⟨317000, by rfl⟩ : syracuseStep 1690669 = 634001) (by norm_num)
theorem B740605 : Blo 658307 740605 := bbase (se 3 (by rfl) ⟨138863, by rfl⟩ : syracuseStep 740605 = 277727) (by norm_num)
theorem B2379029 : Blo 658307 2379029 := bbase (se 6 (by rfl) ⟨55758, by rfl⟩ : syracuseStep 2379029 = 111517) (by norm_num)
theorem B740641 : Blo 658307 740641 := bbase (se 2 (by rfl) ⟨277740, by rfl⟩ : syracuseStep 740641 = 555481) (by norm_num)
theorem B740677 : Blo 658307 740677 := bbase (se 4 (by rfl) ⟨69438, by rfl⟩ : syracuseStep 740677 = 138877) (by norm_num)
theorem B740713 : Blo 658307 740713 := bbase (se 2 (by rfl) ⟨277767, by rfl⟩ : syracuseStep 740713 = 555535) (by norm_num)
theorem B740749 : Blo 658307 740749 := bbase (se 3 (by rfl) ⟨138890, by rfl⟩ : syracuseStep 740749 = 277781) (by norm_num)
theorem B10833301 : Blo 658307 10833301 := bbase (se 6 (by rfl) ⟨253905, by rfl⟩ : syracuseStep 10833301 = 507811) (by norm_num)
theorem B740785 : Blo 658307 740785 := bbase (se 2 (by rfl) ⟨277794, by rfl⟩ : syracuseStep 740785 = 555589) (by norm_num)
theorem B740821 : Blo 658307 740821 := bbase (se 7 (by rfl) ⟨8681, by rfl⟩ : syracuseStep 740821 = 17363) (by norm_num)
theorem B1101269 : Blo 658307 1101269 := bbase (se 7 (by rfl) ⟨12905, by rfl⟩ : syracuseStep 1101269 = 25811) (by norm_num)
theorem B740857 : Blo 658307 740857 := bbase (se 2 (by rfl) ⟨277821, by rfl⟩ : syracuseStep 740857 = 555643) (by norm_num)
theorem B740893 : Blo 658307 740893 := bbase (se 3 (by rfl) ⟨138917, by rfl⟩ : syracuseStep 740893 = 277835) (by norm_num)
theorem B740929 : Blo 658307 740929 := bbase (se 2 (by rfl) ⟨277848, by rfl⟩ : syracuseStep 740929 = 555697) (by norm_num)
theorem B740965 : Blo 658307 740965 := bbase (se 4 (by rfl) ⟨69465, by rfl⟩ : syracuseStep 740965 = 138931) (by norm_num)
theorem B937597 : Blo 658307 937597 := bbase (se 3 (by rfl) ⟨175799, by rfl⟩ : syracuseStep 937597 = 351599) (by norm_num)
theorem B741001 : Blo 658307 741001 := bbase (se 2 (by rfl) ⟨277875, by rfl⟩ : syracuseStep 741001 = 555751) (by norm_num)
theorem B741037 : Blo 658307 741037 := bbase (se 3 (by rfl) ⟨138944, by rfl⟩ : syracuseStep 741037 = 277889) (by norm_num)
theorem B741073 : Blo 658307 741073 := bbase (se 2 (by rfl) ⟨277902, by rfl⟩ : syracuseStep 741073 = 555805) (by norm_num)
theorem B741109 : Blo 658307 741109 := bbase (se 5 (by rfl) ⟨34739, by rfl⟩ : syracuseStep 741109 = 69479) (by norm_num)
theorem B741145 : Blo 658307 741145 := bbase (se 2 (by rfl) ⟨277929, by rfl⟩ : syracuseStep 741145 = 555859) (by norm_num)
theorem B741181 : Blo 658307 741181 := bbase (se 3 (by rfl) ⟨138971, by rfl⟩ : syracuseStep 741181 = 277943) (by norm_num)
theorem B937813 : Blo 658307 937813 := bbase (se 9 (by rfl) ⟨2747, by rfl⟩ : syracuseStep 937813 = 5495) (by norm_num)
theorem B2117461 : Blo 658307 2117461 := bbase (se 9 (by rfl) ⟨6203, by rfl⟩ : syracuseStep 2117461 = 12407) (by norm_num)
theorem B4771669 : Blo 658307 4771669 := bbase (se 9 (by rfl) ⟨13979, by rfl⟩ : syracuseStep 4771669 = 27959) (by norm_num)
theorem B741217 : Blo 658307 741217 := bbase (se 2 (by rfl) ⟨277956, by rfl⟩ : syracuseStep 741217 = 555913) (by norm_num)
theorem B741253 : Blo 658307 741253 := bbase (se 4 (by rfl) ⟨69492, by rfl⟩ : syracuseStep 741253 = 138985) (by norm_num)
theorem B741289 : Blo 658307 741289 := bbase (se 2 (by rfl) ⟨277983, by rfl⟩ : syracuseStep 741289 = 555967) (by norm_num)
theorem B741325 : Blo 658307 741325 := bbase (se 3 (by rfl) ⟨138998, by rfl⟩ : syracuseStep 741325 = 277997) (by norm_num)
theorem B741361 : Blo 658307 741361 := bbase (se 2 (by rfl) ⟨278010, by rfl⟩ : syracuseStep 741361 = 556021) (by norm_num)
theorem B6344693 : Blo 658307 6344693 := bbase (se 5 (by rfl) ⟨297407, by rfl⟩ : syracuseStep 6344693 = 594815) (by norm_num)
theorem B741397 : Blo 658307 741397 := bbase (se 6 (by rfl) ⟨17376, by rfl⟩ : syracuseStep 741397 = 34753) (by norm_num)
theorem B8572949 : Blo 658307 8572949 := bbase (se 6 (by rfl) ⟨200928, by rfl⟩ : syracuseStep 8572949 = 401857) (by norm_num)
theorem B741433 : Blo 658307 741433 := bbase (se 2 (by rfl) ⟨278037, by rfl⟩ : syracuseStep 741433 = 556075) (by norm_num)
theorem B741469 : Blo 658307 741469 := bbase (se 3 (by rfl) ⟨139025, by rfl⟩ : syracuseStep 741469 = 278051) (by norm_num)
theorem B741505 : Blo 658307 741505 := bbase (se 2 (by rfl) ⟨278064, by rfl⟩ : syracuseStep 741505 = 556129) (by norm_num)
theorem B741541 : Blo 658307 741541 := bbase (se 4 (by rfl) ⟨69519, by rfl⟩ : syracuseStep 741541 = 139039) (by norm_num)
theorem B2674853 : Blo 658307 2674853 := bbase (se 4 (by rfl) ⟨250767, by rfl⟩ : syracuseStep 2674853 = 501535) (by norm_num)
theorem B741577 : Blo 658307 741577 := bbase (se 2 (by rfl) ⟨278091, by rfl⟩ : syracuseStep 741577 = 556183) (by norm_num)
theorem B938189 : Blo 658307 938189 := bbase (se 3 (by rfl) ⟨175910, by rfl⟩ : syracuseStep 938189 = 351821) (by norm_num)
theorem B741613 : Blo 658307 741613 := bbase (se 3 (by rfl) ⟨139052, by rfl⟩ : syracuseStep 741613 = 278105) (by norm_num)
theorem B741649 : Blo 658307 741649 := bbase (se 2 (by rfl) ⟨278118, by rfl⟩ : syracuseStep 741649 = 556237) (by norm_num)
theorem B741685 : Blo 658307 741685 := bbase (se 5 (by rfl) ⟨34766, by rfl⟩ : syracuseStep 741685 = 69533) (by norm_num)
theorem B741721 : Blo 658307 741721 := bbase (se 2 (by rfl) ⟨278145, by rfl⟩ : syracuseStep 741721 = 556291) (by norm_num)
theorem B5656949 : Blo 658307 5656949 := bbase (se 5 (by rfl) ⟨265169, by rfl⟩ : syracuseStep 5656949 = 530339) (by norm_num)
theorem B741757 : Blo 658307 741757 := bbase (se 3 (by rfl) ⟨139079, by rfl⟩ : syracuseStep 741757 = 278159) (by norm_num)
theorem B741793 : Blo 658307 741793 := bbase (se 2 (by rfl) ⟨278172, by rfl⟩ : syracuseStep 741793 = 556345) (by norm_num)
theorem B2511269 : Blo 658307 2511269 := bbase (se 4 (by rfl) ⟨235431, by rfl⟩ : syracuseStep 2511269 = 470863) (by norm_num)
theorem B741829 : Blo 658307 741829 := bbase (se 4 (by rfl) ⟨69546, by rfl⟩ : syracuseStep 741829 = 139093) (by norm_num)
theorem B741865 : Blo 658307 741865 := bbase (se 2 (by rfl) ⟨278199, by rfl⟩ : syracuseStep 741865 = 556399) (by norm_num)
theorem B741901 : Blo 658307 741901 := bbase (se 3 (by rfl) ⟨139106, by rfl⟩ : syracuseStep 741901 = 278213) (by norm_num)
theorem B741937 : Blo 658307 741937 := bbase (se 2 (by rfl) ⟨278226, by rfl⟩ : syracuseStep 741937 = 556453) (by norm_num)
theorem B741973 : Blo 658307 741973 := bbase (se 8 (by rfl) ⟨4347, by rfl⟩ : syracuseStep 741973 = 8695) (by norm_num)
theorem B742009 : Blo 658307 742009 := bbase (se 2 (by rfl) ⟨278253, by rfl⟩ : syracuseStep 742009 = 556507) (by norm_num)
theorem B742045 : Blo 658307 742045 := bbase (se 3 (by rfl) ⟨139133, by rfl⟩ : syracuseStep 742045 = 278267) (by norm_num)
theorem B742081 : Blo 658307 742081 := bbase (se 2 (by rfl) ⟨278280, by rfl⟩ : syracuseStep 742081 = 556561) (by norm_num)
theorem B2511557 : Blo 658307 2511557 := bbase (se 4 (by rfl) ⟨235458, by rfl⟩ : syracuseStep 2511557 = 470917) (by norm_num)
theorem B742117 : Blo 658307 742117 := bbase (se 4 (by rfl) ⟨69573, by rfl⟩ : syracuseStep 742117 = 139147) (by norm_num)
theorem B742153 : Blo 658307 742153 := bbase (se 2 (by rfl) ⟨278307, by rfl⟩ : syracuseStep 742153 = 556615) (by norm_num)
theorem B742189 : Blo 658307 742189 := bbase (se 3 (by rfl) ⟨139160, by rfl⟩ : syracuseStep 742189 = 278321) (by norm_num)
theorem B742225 : Blo 658307 742225 := bbase (se 2 (by rfl) ⟨278334, by rfl⟩ : syracuseStep 742225 = 556669) (by norm_num)
theorem B7131989 : Blo 658307 7131989 := bbase (se 9 (by rfl) ⟨20894, by rfl⟩ : syracuseStep 7131989 = 41789) (by norm_num)
theorem B742261 : Blo 658307 742261 := bbase (se 5 (by rfl) ⟨34793, by rfl⟩ : syracuseStep 742261 = 69587) (by norm_num)
theorem B742297 : Blo 658307 742297 := bbase (se 2 (by rfl) ⟨278361, by rfl⟩ : syracuseStep 742297 = 556723) (by norm_num)
theorem B4281269 : Blo 658307 4281269 := bbase (se 5 (by rfl) ⟨200684, by rfl⟩ : syracuseStep 4281269 = 401369) (by norm_num)
theorem B742333 : Blo 658307 742333 := bbase (se 3 (by rfl) ⟨139187, by rfl⟩ : syracuseStep 742333 = 278375) (by norm_num)
theorem B742369 : Blo 658307 742369 := bbase (se 2 (by rfl) ⟨278388, by rfl⟩ : syracuseStep 742369 = 556777) (by norm_num)
theorem B2380789 : Blo 658307 2380789 := bbase (se 5 (by rfl) ⟨111599, by rfl⟩ : syracuseStep 2380789 = 223199) (by norm_num)
theorem B742405 : Blo 658307 742405 := bbase (se 4 (by rfl) ⟨69600, by rfl⟩ : syracuseStep 742405 = 139201) (by norm_num)
theorem B906277 : Blo 658307 906277 := bbase (se 4 (by rfl) ⟨84963, by rfl⟩ : syracuseStep 906277 = 169927) (by norm_num)
theorem B742441 : Blo 658307 742441 := bbase (se 2 (by rfl) ⟨278415, by rfl⟩ : syracuseStep 742441 = 556831) (by norm_num)
theorem B742477 : Blo 658307 742477 := bbase (se 3 (by rfl) ⟨139214, by rfl⟩ : syracuseStep 742477 = 278429) (by norm_num)
theorem B742513 : Blo 658307 742513 := bbase (se 2 (by rfl) ⟨278442, by rfl⟩ : syracuseStep 742513 = 556885) (by norm_num)
theorem B742549 : Blo 658307 742549 := bbase (se 6 (by rfl) ⟨17403, by rfl⟩ : syracuseStep 742549 = 34807) (by norm_num)
theorem B742585 : Blo 658307 742585 := bbase (se 2 (by rfl) ⟨278469, by rfl⟩ : syracuseStep 742585 = 556939) (by norm_num)
theorem B742621 : Blo 658307 742621 := bbase (se 3 (by rfl) ⟨139241, by rfl⟩ : syracuseStep 742621 = 278483) (by norm_num)
theorem B742657 : Blo 658307 742657 := bbase (se 2 (by rfl) ⟨278496, by rfl⟩ : syracuseStep 742657 = 556993) (by norm_num)
theorem B742693 : Blo 658307 742693 := bbase (se 4 (by rfl) ⟨69627, by rfl⟩ : syracuseStep 742693 = 139255) (by norm_num)
theorem B742729 : Blo 658307 742729 := bbase (se 2 (by rfl) ⟨278523, by rfl⟩ : syracuseStep 742729 = 557047) (by norm_num)
theorem B742765 : Blo 658307 742765 := bbase (se 3 (by rfl) ⟨139268, by rfl⟩ : syracuseStep 742765 = 278537) (by norm_num)
theorem B742801 : Blo 658307 742801 := bbase (se 2 (by rfl) ⟨278550, by rfl⟩ : syracuseStep 742801 = 557101) (by norm_num)
theorem B742837 : Blo 658307 742837 := bbase (se 5 (by rfl) ⟨34820, by rfl⟩ : syracuseStep 742837 = 69641) (by norm_num)
theorem B742873 : Blo 658307 742873 := bbase (se 2 (by rfl) ⟨278577, by rfl⟩ : syracuseStep 742873 = 557155) (by norm_num)
theorem B742909 : Blo 658307 742909 := bbase (se 3 (by rfl) ⟨139295, by rfl⟩ : syracuseStep 742909 = 278591) (by norm_num)
theorem B742945 : Blo 658307 742945 := bbase (se 2 (by rfl) ⟨278604, by rfl⟩ : syracuseStep 742945 = 557209) (by norm_num)
theorem B1398325 : Blo 658307 1398325 := bbase (se 5 (by rfl) ⟨65546, by rfl⟩ : syracuseStep 1398325 = 131093) (by norm_num)
theorem B742981 : Blo 658307 742981 := bbase (se 4 (by rfl) ⟨69654, by rfl⟩ : syracuseStep 742981 = 139309) (by norm_num)
theorem B939613 : Blo 658307 939613 := bbase (se 3 (by rfl) ⟨176177, by rfl⟩ : syracuseStep 939613 = 352355) (by norm_num)
theorem B743017 : Blo 658307 743017 := bbase (se 2 (by rfl) ⟨278631, by rfl⟩ : syracuseStep 743017 = 557263) (by norm_num)
theorem B743053 : Blo 658307 743053 := bbase (se 3 (by rfl) ⟨139322, by rfl⟩ : syracuseStep 743053 = 278645) (by norm_num)
theorem B743089 : Blo 658307 743089 := bbase (se 2 (by rfl) ⟨278658, by rfl⟩ : syracuseStep 743089 = 557317) (by norm_num)
theorem B743125 : Blo 658307 743125 := bbase (se 7 (by rfl) ⟨8708, by rfl⟩ : syracuseStep 743125 = 17417) (by norm_num)
theorem B743161 : Blo 658307 743161 := bbase (se 2 (by rfl) ⟨278685, by rfl⟩ : syracuseStep 743161 = 557371) (by norm_num)
theorem B743197 : Blo 658307 743197 := bbase (se 3 (by rfl) ⟨139349, by rfl⟩ : syracuseStep 743197 = 278699) (by norm_num)
theorem B743233 : Blo 658307 743233 := bbase (se 2 (by rfl) ⟨278712, by rfl⟩ : syracuseStep 743233 = 557425) (by norm_num)
theorem B743269 : Blo 658307 743269 := bbase (se 4 (by rfl) ⟨69681, by rfl⟩ : syracuseStep 743269 = 139363) (by norm_num)
theorem B2512741 : Blo 658307 2512741 := bbase (se 4 (by rfl) ⟨235569, by rfl⟩ : syracuseStep 2512741 = 471139) (by norm_num)
theorem B743305 : Blo 658307 743305 := bbase (se 2 (by rfl) ⟨278739, by rfl⟩ : syracuseStep 743305 = 557479) (by norm_num)
theorem B743341 : Blo 658307 743341 := bbase (se 3 (by rfl) ⟨139376, by rfl⟩ : syracuseStep 743341 = 278753) (by norm_num)
theorem B743377 : Blo 658307 743377 := bbase (se 2 (by rfl) ⟨278766, by rfl⟩ : syracuseStep 743377 = 557533) (by norm_num)
theorem B743413 : Blo 658307 743413 := bbase (se 5 (by rfl) ⟨34847, by rfl⟩ : syracuseStep 743413 = 69695) (by norm_num)
theorem B743449 : Blo 658307 743449 := bbase (se 2 (by rfl) ⟨278793, by rfl⟩ : syracuseStep 743449 = 557587) (by norm_num)
theorem B743485 : Blo 658307 743485 := bbase (se 3 (by rfl) ⟨139403, by rfl⟩ : syracuseStep 743485 = 278807) (by norm_num)
theorem B743521 : Blo 658307 743521 := bbase (se 2 (by rfl) ⟨278820, by rfl⟩ : syracuseStep 743521 = 557641) (by norm_num)
theorem B743557 : Blo 658307 743557 := bbase (se 4 (by rfl) ⟨69708, by rfl⟩ : syracuseStep 743557 = 139417) (by norm_num)
theorem B2513045 : Blo 658307 2513045 := bbase (se 6 (by rfl) ⟨58899, by rfl⟩ : syracuseStep 2513045 = 117799) (by norm_num)
theorem B743593 : Blo 658307 743593 := bbase (se 2 (by rfl) ⟨278847, by rfl⟩ : syracuseStep 743593 = 557695) (by norm_num)
theorem B940205 : Blo 658307 940205 := bbase (se 3 (by rfl) ⟨176288, by rfl⟩ : syracuseStep 940205 = 352577) (by norm_num)
theorem B743629 : Blo 658307 743629 := bbase (se 3 (by rfl) ⟨139430, by rfl⟩ : syracuseStep 743629 = 278861) (by norm_num)
theorem B743665 : Blo 658307 743665 := bbase (se 2 (by rfl) ⟨278874, by rfl⟩ : syracuseStep 743665 = 557749) (by norm_num)
theorem B940285 : Blo 658307 940285 := bbase (se 3 (by rfl) ⟨176303, by rfl⟩ : syracuseStep 940285 = 352607) (by norm_num)
theorem B743701 : Blo 658307 743701 := bbase (se 6 (by rfl) ⟨17430, by rfl⟩ : syracuseStep 743701 = 34861) (by norm_num)
theorem B743737 : Blo 658307 743737 := bbase (se 2 (by rfl) ⟨278901, by rfl⟩ : syracuseStep 743737 = 557803) (by norm_num)
theorem B743773 : Blo 658307 743773 := bbase (se 3 (by rfl) ⟨139457, by rfl⟩ : syracuseStep 743773 = 278915) (by norm_num)
theorem B940405 : Blo 658307 940405 := bbase (se 5 (by rfl) ⟨44081, by rfl⟩ : syracuseStep 940405 = 88163) (by norm_num)
theorem B743809 : Blo 658307 743809 := bbase (se 2 (by rfl) ⟨278928, by rfl⟩ : syracuseStep 743809 = 557857) (by norm_num)
theorem B743845 : Blo 658307 743845 := bbase (se 4 (by rfl) ⟨69735, by rfl⟩ : syracuseStep 743845 = 139471) (by norm_num)
theorem B743881 : Blo 658307 743881 := bbase (se 2 (by rfl) ⟨278955, by rfl⟩ : syracuseStep 743881 = 557911) (by norm_num)
theorem B940501 : Blo 658307 940501 := bbase (se 7 (by rfl) ⟨11021, by rfl⟩ : syracuseStep 940501 = 22043) (by norm_num)
theorem B743917 : Blo 658307 743917 := bbase (se 3 (by rfl) ⟨139484, by rfl⟩ : syracuseStep 743917 = 278969) (by norm_num)
theorem B743953 : Blo 658307 743953 := bbase (se 2 (by rfl) ⟨278982, by rfl⟩ : syracuseStep 743953 = 557965) (by norm_num)
theorem B743989 : Blo 658307 743989 := bbase (se 5 (by rfl) ⟨34874, by rfl⟩ : syracuseStep 743989 = 69749) (by norm_num)
theorem B744025 : Blo 658307 744025 := bbase (se 2 (by rfl) ⟨279009, by rfl⟩ : syracuseStep 744025 = 558019) (by norm_num)
theorem B744061 : Blo 658307 744061 := bbase (se 3 (by rfl) ⟨139511, by rfl⟩ : syracuseStep 744061 = 279023) (by norm_num)
theorem B8575637 : Blo 658307 8575637 := bbase (se 6 (by rfl) ⟨200991, by rfl⟩ : syracuseStep 8575637 = 401983) (by norm_num)
theorem B744097 : Blo 658307 744097 := bbase (se 2 (by rfl) ⟨279036, by rfl⟩ : syracuseStep 744097 = 558073) (by norm_num)
theorem B2120357 : Blo 658307 2120357 := bbase (se 4 (by rfl) ⟨198783, by rfl⟩ : syracuseStep 2120357 = 397567) (by norm_num)
theorem B744133 : Blo 658307 744133 := bbase (se 4 (by rfl) ⟨69762, by rfl⟩ : syracuseStep 744133 = 139525) (by norm_num)
theorem B744169 : Blo 658307 744169 := bbase (se 2 (by rfl) ⟨279063, by rfl⟩ : syracuseStep 744169 = 558127) (by norm_num)
theorem B744205 : Blo 658307 744205 := bbase (se 3 (by rfl) ⟨139538, by rfl⟩ : syracuseStep 744205 = 279077) (by norm_num)
theorem B744241 : Blo 658307 744241 := bbase (se 2 (by rfl) ⟨279090, by rfl⟩ : syracuseStep 744241 = 558181) (by norm_num)
theorem B2448181 : Blo 658307 2448181 := bbase (se 5 (by rfl) ⟨114758, by rfl⟩ : syracuseStep 2448181 = 229517) (by norm_num)
theorem B744277 : Blo 658307 744277 := bbase (se 9 (by rfl) ⟨2180, by rfl⟩ : syracuseStep 744277 = 4361) (by norm_num)
theorem B744313 : Blo 658307 744313 := bbase (se 2 (by rfl) ⟨279117, by rfl⟩ : syracuseStep 744313 = 558235) (by norm_num)
theorem B5364629 : Blo 658307 5364629 := bbase (se 6 (by rfl) ⟨125733, by rfl⟩ : syracuseStep 5364629 = 251467) (by norm_num)
theorem B744349 : Blo 658307 744349 := bbase (se 3 (by rfl) ⟨139565, by rfl⟩ : syracuseStep 744349 = 279131) (by norm_num)
theorem B744385 : Blo 658307 744385 := bbase (se 2 (by rfl) ⟨279144, by rfl⟩ : syracuseStep 744385 = 558289) (by norm_num)
theorem B940997 : Blo 658307 940997 := bbase (se 4 (by rfl) ⟨88218, by rfl⟩ : syracuseStep 940997 = 176437) (by norm_num)
theorem B744421 : Blo 658307 744421 := bbase (se 4 (by rfl) ⟨69789, by rfl⟩ : syracuseStep 744421 = 139579) (by norm_num)
theorem B744457 : Blo 658307 744457 := bbase (se 2 (by rfl) ⟨279171, by rfl⟩ : syracuseStep 744457 = 558343) (by norm_num)
theorem B744493 : Blo 658307 744493 := bbase (se 3 (by rfl) ⟨139592, by rfl⟩ : syracuseStep 744493 = 279185) (by norm_num)
theorem B5004341 : Blo 658307 5004341 := bbase (se 5 (by rfl) ⟨234578, by rfl⟩ : syracuseStep 5004341 = 469157) (by norm_num)
theorem B744529 : Blo 658307 744529 := bbase (se 2 (by rfl) ⟨279198, by rfl⟩ : syracuseStep 744529 = 558397) (by norm_num)
theorem B744565 : Blo 658307 744565 := bbase (se 5 (by rfl) ⟨34901, by rfl⟩ : syracuseStep 744565 = 69803) (by norm_num)
theorem B744601 : Blo 658307 744601 := bbase (se 2 (by rfl) ⟨279225, by rfl⟩ : syracuseStep 744601 = 558451) (by norm_num)
theorem B744637 : Blo 658307 744637 := bbase (se 3 (by rfl) ⟨139619, by rfl⟩ : syracuseStep 744637 = 279239) (by norm_num)
theorem B3759317 : Blo 658307 3759317 := bbase (se 7 (by rfl) ⟨44054, by rfl⟩ : syracuseStep 3759317 = 88109) (by norm_num)
theorem B744673 : Blo 658307 744673 := bbase (se 2 (by rfl) ⟨279252, by rfl⟩ : syracuseStep 744673 = 558505) (by norm_num)
theorem B744709 : Blo 658307 744709 := bbase (se 4 (by rfl) ⟨69816, by rfl⟩ : syracuseStep 744709 = 139633) (by norm_num)
theorem B744745 : Blo 658307 744745 := bbase (se 2 (by rfl) ⟨279279, by rfl⟩ : syracuseStep 744745 = 558559) (by norm_num)
theorem B744781 : Blo 658307 744781 := bbase (se 3 (by rfl) ⟨139646, by rfl⟩ : syracuseStep 744781 = 279293) (by norm_num)
theorem B744817 : Blo 658307 744817 := bbase (se 2 (by rfl) ⟨279306, by rfl⟩ : syracuseStep 744817 = 558613) (by norm_num)
theorem B744853 : Blo 658307 744853 := bbase (se 6 (by rfl) ⟨17457, by rfl⟩ : syracuseStep 744853 = 34915) (by norm_num)
theorem B1334701 : Blo 658307 1334701 := bbase (se 3 (by rfl) ⟨250256, by rfl⟩ : syracuseStep 1334701 = 500513) (by norm_num)
theorem B744889 : Blo 658307 744889 := bbase (se 2 (by rfl) ⟨279333, by rfl⟩ : syracuseStep 744889 = 558667) (by norm_num)
theorem B9493973 : Blo 658307 9493973 := bbase (se 7 (by rfl) ⟨111257, by rfl⟩ : syracuseStep 9493973 = 222515) (by norm_num)
theorem B744925 : Blo 658307 744925 := bbase (se 3 (by rfl) ⟨139673, by rfl⟩ : syracuseStep 744925 = 279347) (by norm_num)
theorem B941549 : Blo 658307 941549 := bbase (se 3 (by rfl) ⟨176540, by rfl⟩ : syracuseStep 941549 = 353081) (by norm_num)
theorem B744961 : Blo 658307 744961 := bbase (se 2 (by rfl) ⟨279360, by rfl⟩ : syracuseStep 744961 = 558721) (by norm_num)
theorem B744997 : Blo 658307 744997 := bbase (se 4 (by rfl) ⟨69843, by rfl⟩ : syracuseStep 744997 = 139687) (by norm_num)
theorem B2678341 : Blo 658307 2678341 := bbase (se 4 (by rfl) ⟨251094, by rfl⟩ : syracuseStep 2678341 = 502189) (by norm_num)
theorem B745033 : Blo 658307 745033 := bbase (se 2 (by rfl) ⟨279387, by rfl⟩ : syracuseStep 745033 = 558775) (by norm_num)
theorem B745069 : Blo 658307 745069 := bbase (se 3 (by rfl) ⟨139700, by rfl⟩ : syracuseStep 745069 = 279401) (by norm_num)
theorem B3333797 : Blo 658307 3333797 := bbase (se 4 (by rfl) ⟨312543, by rfl⟩ : syracuseStep 3333797 = 625087) (by norm_num)
theorem B3170117 : Blo 658307 3170117 := bbase (se 4 (by rfl) ⟨297198, by rfl⟩ : syracuseStep 3170117 = 594397) (by norm_num)
theorem B1072981 : Blo 658307 1072981 := bbase (se 9 (by rfl) ⟨3143, by rfl⟩ : syracuseStep 1072981 = 6287) (by norm_num)
theorem B1269605 : Blo 658307 1269605 := bbase (se 4 (by rfl) ⟨119025, by rfl⟩ : syracuseStep 1269605 = 238051) (by norm_num)
theorem B1335221 : Blo 658307 1335221 := bbase (se 5 (by rfl) ⟨62588, by rfl⟩ : syracuseStep 1335221 = 125177) (by norm_num)
theorem B2121653 : Blo 658307 2121653 := bbase (se 5 (by rfl) ⟨99452, by rfl⟩ : syracuseStep 2121653 = 198905) (by norm_num)
theorem B712697 : Blo 658307 712697 := bbase (se 2 (by rfl) ⟨267261, by rfl⟩ : syracuseStep 712697 = 534523) (by norm_num)
theorem B712837 : Blo 658307 712837 := bbase (se 4 (by rfl) ⟨66828, by rfl⟩ : syracuseStep 712837 = 133657) (by norm_num)
theorem B942301 : Blo 658307 942301 := bbase (se 3 (by rfl) ⟨176681, by rfl⟩ : syracuseStep 942301 = 353363) (by norm_num)
theorem B2253349 : Blo 658307 2253349 := bbase (se 4 (by rfl) ⟨211251, by rfl⟩ : syracuseStep 2253349 = 422503) (by norm_num)
theorem B1335869 : Blo 658307 1335869 := bbase (se 3 (by rfl) ⟨250475, by rfl⟩ : syracuseStep 1335869 = 500951) (by norm_num)
theorem B2253653 : Blo 658307 2253653 := bbase (se 9 (by rfl) ⟨6602, by rfl⟩ : syracuseStep 2253653 = 13205) (by norm_num)
theorem B1696621 : Blo 658307 1696621 := bbase (se 3 (by rfl) ⟨318116, by rfl⟩ : syracuseStep 1696621 = 636233) (by norm_num)
theorem B3335093 : Blo 658307 3335093 := bbase (se 5 (by rfl) ⟨156332, by rfl⟩ : syracuseStep 3335093 = 312665) (by norm_num)
theorem B1205453 : Blo 658307 1205453 := bbase (se 3 (by rfl) ⟨226022, by rfl⟩ : syracuseStep 1205453 = 452045) (by norm_num)
theorem B714169 : Blo 658307 714169 := bbase (se 2 (by rfl) ⟨267813, by rfl⟩ : syracuseStep 714169 = 535627) (by norm_num)
theorem B845273 : Blo 658307 845273 := bbase (se 2 (by rfl) ⟨316977, by rfl⟩ : syracuseStep 845273 = 633955) (by norm_num)
theorem B845417 : Blo 658307 845417 := bbase (se 2 (by rfl) ⟨317031, by rfl⟩ : syracuseStep 845417 = 634063) (by norm_num)
theorem B1926805 : Blo 658307 1926805 := bbase (se 6 (by rfl) ⟨45159, by rfl⟩ : syracuseStep 1926805 = 90319) (by norm_num)
theorem B2221829 : Blo 658307 2221829 := bbase (se 4 (by rfl) ⟨208296, by rfl⟩ : syracuseStep 2221829 = 416593) (by norm_num)
theorem B1271621 : Blo 658307 1271621 := bbase (se 4 (by rfl) ⟨119214, by rfl⟩ : syracuseStep 1271621 = 238429) (by norm_num)
theorem B714629 : Blo 658307 714629 := bbase (se 4 (by rfl) ⟨66996, by rfl⟩ : syracuseStep 714629 = 133993) (by norm_num)
theorem B1697813 : Blo 658307 1697813 := bbase (se 6 (by rfl) ⟨39792, by rfl⟩ : syracuseStep 1697813 = 79585) (by norm_num)
theorem B2222261 : Blo 658307 2222261 := bbase (se 5 (by rfl) ⟨104168, by rfl⟩ : syracuseStep 2222261 = 208337) (by norm_num)
theorem B3336389 : Blo 658307 3336389 := bbase (se 4 (by rfl) ⟨312786, by rfl⟩ : syracuseStep 3336389 = 625573) (by norm_num)
theorem B1337573 : Blo 658307 1337573 := bbase (se 4 (by rfl) ⟨125397, by rfl⟩ : syracuseStep 1337573 = 250795) (by norm_num)
theorem B715105 : Blo 658307 715105 := bbase (se 2 (by rfl) ⟨268164, by rfl⟩ : syracuseStep 715105 = 536329) (by norm_num)
theorem B846217 : Blo 658307 846217 := bbase (se 2 (by rfl) ⟨317331, by rfl⟩ : syracuseStep 846217 = 634663) (by norm_num)
theorem B2222693 : Blo 658307 2222693 := bbase (se 4 (by rfl) ⟨208377, by rfl⟩ : syracuseStep 2222693 = 416755) (by norm_num)
theorem B1338133 : Blo 658307 1338133 := bbase (se 6 (by rfl) ⟨31362, by rfl⟩ : syracuseStep 1338133 = 62725) (by norm_num)
theorem B4516661 : Blo 658307 4516661 := bbase (se 5 (by rfl) ⟨211718, by rfl⟩ : syracuseStep 4516661 = 423437) (by norm_num)
theorem B3173269 : Blo 658307 3173269 := bbase (se 6 (by rfl) ⟨74373, by rfl⟩ : syracuseStep 3173269 = 148747) (by norm_num)
theorem B2223125 : Blo 658307 2223125 := bbase (se 6 (by rfl) ⟨52104, by rfl⟩ : syracuseStep 2223125 = 104209) (by norm_num)
theorem B1502381 : Blo 658307 1502381 := bbase (se 3 (by rfl) ⟨281696, by rfl⟩ : syracuseStep 1502381 = 563393) (by norm_num)
theorem B1142069 : Blo 658307 1142069 := bbase (se 5 (by rfl) ⟨53534, by rfl⟩ : syracuseStep 1142069 = 107069) (by norm_num)
theorem B1666453 : Blo 658307 1666453 := bbase (se 6 (by rfl) ⟨39057, by rfl⟩ : syracuseStep 1666453 = 78115) (by norm_num)
theorem B2223557 : Blo 658307 2223557 := bbase (se 4 (by rfl) ⟨208458, by rfl⟩ : syracuseStep 2223557 = 416917) (by norm_num)
theorem B3337685 : Blo 658307 3337685 := bbase (se 7 (by rfl) ⟨39113, by rfl⟩ : syracuseStep 3337685 = 78227) (by norm_num)
theorem B847325 : Blo 658307 847325 := bbase (se 3 (by rfl) ⟨158873, by rfl⟩ : syracuseStep 847325 = 317747) (by norm_num)
theorem B1338853 : Blo 658307 1338853 := bbase (se 4 (by rfl) ⟨125517, by rfl⟩ : syracuseStep 1338853 = 251035) (by norm_num)
theorem B1666565 : Blo 658307 1666565 := bbase (se 4 (by rfl) ⟨156240, by rfl⟩ : syracuseStep 1666565 = 312481) (by norm_num)
theorem B1273421 : Blo 658307 1273421 := bbase (se 3 (by rfl) ⟨238766, by rfl⟩ : syracuseStep 1273421 = 477533) (by norm_num)
theorem B1666757 : Blo 658307 1666757 := bbase (se 4 (by rfl) ⟨156258, by rfl⟩ : syracuseStep 1666757 = 312517) (by norm_num)
theorem B2223989 : Blo 658307 2223989 := bbase (se 5 (by rfl) ⟨104249, by rfl⟩ : syracuseStep 2223989 = 208499) (by norm_num)
theorem B1339325 : Blo 658307 1339325 := bbase (se 3 (by rfl) ⟨251123, by rfl⟩ : syracuseStep 1339325 = 502247) (by norm_num)
theorem B1667101 : Blo 658307 1667101 := bbase (se 3 (by rfl) ⟨312581, by rfl⟩ : syracuseStep 1667101 = 625163) (by norm_num)
theorem B716845 : Blo 658307 716845 := bbase (se 3 (by rfl) ⟨134408, by rfl⟩ : syracuseStep 716845 = 268817) (by norm_num)
theorem B4223029 : Blo 658307 4223029 := bbase (se 5 (by rfl) ⟨197954, by rfl⟩ : syracuseStep 4223029 = 395909) (by norm_num)
theorem B1667213 : Blo 658307 1667213 := bbase (se 3 (by rfl) ⟨312602, by rfl⟩ : syracuseStep 1667213 = 625205) (by norm_num)
theorem B2224421 : Blo 658307 2224421 := bbase (se 4 (by rfl) ⟨208539, by rfl⟩ : syracuseStep 2224421 = 417079) (by norm_num)
theorem B1667405 : Blo 658307 1667405 := bbase (se 3 (by rfl) ⟨312638, by rfl⟩ : syracuseStep 1667405 = 625277) (by norm_num)
theorem B2814533 : Blo 658307 2814533 := bbase (se 4 (by rfl) ⟨263862, by rfl⟩ : syracuseStep 2814533 = 527725) (by norm_num)
theorem B1667749 : Blo 658307 1667749 := bbase (se 4 (by rfl) ⟨156351, by rfl⟩ : syracuseStep 1667749 = 312703) (by norm_num)
theorem B2224853 : Blo 658307 2224853 := bbase (se 7 (by rfl) ⟨26072, by rfl⟩ : syracuseStep 2224853 = 52145) (by norm_num)
theorem B1241813 : Blo 658307 1241813 := bbase (se 7 (by rfl) ⟨14552, by rfl⟩ : syracuseStep 1241813 = 29105) (by norm_num)
theorem B3338981 : Blo 658307 3338981 := bbase (se 4 (by rfl) ⟨313029, by rfl⟩ : syracuseStep 3338981 = 626059) (by norm_num)
theorem B1667861 : Blo 658307 1667861 := bbase (se 6 (by rfl) ⟨39090, by rfl⟩ : syracuseStep 1667861 = 78181) (by norm_num)
theorem B1110901 : Blo 658307 1110901 := bbase (se 5 (by rfl) ⟨52073, by rfl⟩ : syracuseStep 1110901 = 104147) (by norm_num)
theorem B1504133 : Blo 658307 1504133 := bbase (se 4 (by rfl) ⟨141012, by rfl⟩ : syracuseStep 1504133 = 282025) (by norm_num)
theorem B1110989 : Blo 658307 1110989 := bbase (se 3 (by rfl) ⟨208310, by rfl⟩ : syracuseStep 1110989 = 416621) (by norm_num)
theorem B1668053 : Blo 658307 1668053 := bbase (se 7 (by rfl) ⟨19547, by rfl⟩ : syracuseStep 1668053 = 39095) (by norm_num)
theorem B1111117 : Blo 658307 1111117 := bbase (se 3 (by rfl) ⟨208334, by rfl⟩ : syracuseStep 1111117 = 416669) (by norm_num)
theorem B2225285 : Blo 658307 2225285 := bbase (se 4 (by rfl) ⟨208620, by rfl⟩ : syracuseStep 2225285 = 417241) (by norm_num)
theorem B1111205 : Blo 658307 1111205 := bbase (se 4 (by rfl) ⟨104175, by rfl⟩ : syracuseStep 1111205 = 208351) (by norm_num)
theorem B1406173 : Blo 658307 1406173 := bbase (se 3 (by rfl) ⟨263657, by rfl⟩ : syracuseStep 1406173 = 527315) (by norm_num)
theorem B849133 : Blo 658307 849133 := bbase (se 3 (by rfl) ⟨159212, by rfl⟩ : syracuseStep 849133 = 318425) (by norm_num)
theorem B1111333 : Blo 658307 1111333 := bbase (se 4 (by rfl) ⟨104187, by rfl⟩ : syracuseStep 1111333 = 208375) (by norm_num)
theorem B1668397 : Blo 658307 1668397 := bbase (se 3 (by rfl) ⟨312824, by rfl⟩ : syracuseStep 1668397 = 625649) (by norm_num)
theorem B1504597 : Blo 658307 1504597 := bbase (se 13 (by rfl) ⟨275, by rfl⟩ : syracuseStep 1504597 = 551) (by norm_num)
theorem B1111421 : Blo 658307 1111421 := bbase (se 3 (by rfl) ⟨208391, by rfl⟩ : syracuseStep 1111421 = 416783) (by norm_num)
theorem B1668509 : Blo 658307 1668509 := bbase (se 3 (by rfl) ⟨312845, by rfl⟩ : syracuseStep 1668509 = 625691) (by norm_num)
theorem B751021 : Blo 658307 751021 := bbase (se 3 (by rfl) ⟨140816, by rfl⟩ : syracuseStep 751021 = 281633) (by norm_num)
theorem B751025 : Blo 658307 751025 := bbase (se 2 (by rfl) ⟨281634, by rfl⟩ : syracuseStep 751025 = 563269) (by norm_num)
theorem B751081 : Blo 658307 751081 := bbase (se 2 (by rfl) ⟨281655, by rfl⟩ : syracuseStep 751081 = 563311) (by norm_num)
theorem B1111549 : Blo 658307 1111549 := bbase (se 3 (by rfl) ⟨208415, by rfl⟩ : syracuseStep 1111549 = 416831) (by norm_num)
theorem B2225717 : Blo 658307 2225717 := bbase (se 5 (by rfl) ⟨104330, by rfl⟩ : syracuseStep 2225717 = 208661) (by norm_num)
theorem B1111637 : Blo 658307 1111637 := bbase (se 8 (by rfl) ⟨6513, by rfl⟩ : syracuseStep 1111637 = 13027) (by norm_num)
theorem B1668701 : Blo 658307 1668701 := bbase (se 3 (by rfl) ⟨312881, by rfl⟩ : syracuseStep 1668701 = 625763) (by norm_num)
theorem B1341053 : Blo 658307 1341053 := bbase (se 3 (by rfl) ⟨251447, by rfl⟩ : syracuseStep 1341053 = 502895) (by norm_num)
theorem B3176117 : Blo 658307 3176117 := bbase (se 5 (by rfl) ⟨148880, by rfl⟩ : syracuseStep 3176117 = 297761) (by norm_num)
theorem B1111765 : Blo 658307 1111765 := bbase (se 7 (by rfl) ⟨13028, by rfl⟩ : syracuseStep 1111765 = 26057) (by norm_num)
theorem B1111853 : Blo 658307 1111853 := bbase (se 3 (by rfl) ⟨208472, by rfl⟩ : syracuseStep 1111853 = 416945) (by norm_num)
theorem B1111981 : Blo 658307 1111981 := bbase (se 3 (by rfl) ⟨208496, by rfl⟩ : syracuseStep 1111981 = 416993) (by norm_num)
theorem B1669045 : Blo 658307 1669045 := bbase (se 5 (by rfl) ⟨78236, by rfl⟩ : syracuseStep 1669045 = 156473) (by norm_num)
theorem B2226149 : Blo 658307 2226149 := bbase (se 4 (by rfl) ⟨208701, by rfl⟩ : syracuseStep 2226149 = 417403) (by norm_num)
theorem B3340277 : Blo 658307 3340277 := bbase (se 5 (by rfl) ⟨156575, by rfl⟩ : syracuseStep 3340277 = 313151) (by norm_num)
theorem B1112069 : Blo 658307 1112069 := bbase (se 4 (by rfl) ⟨104256, by rfl⟩ : syracuseStep 1112069 = 208513) (by norm_num)
theorem B1669157 : Blo 658307 1669157 := bbase (se 4 (by rfl) ⟨156483, by rfl⟩ : syracuseStep 1669157 = 312967) (by norm_num)
theorem B1407061 : Blo 658307 1407061 := bbase (se 8 (by rfl) ⟨8244, by rfl⟩ : syracuseStep 1407061 = 16489) (by norm_num)
theorem B1112197 : Blo 658307 1112197 := bbase (se 4 (by rfl) ⟨104268, by rfl⟩ : syracuseStep 1112197 = 208537) (by norm_num)
theorem B9664661 : Blo 658307 9664661 := bbase (se 6 (by rfl) ⟨226515, by rfl⟩ : syracuseStep 9664661 = 453031) (by norm_num)
theorem B8485013 : Blo 658307 8485013 := bbase (se 6 (by rfl) ⟨198867, by rfl⟩ : syracuseStep 8485013 = 397735) (by norm_num)
theorem B1112285 : Blo 658307 1112285 := bbase (se 3 (by rfl) ⟨208553, by rfl⟩ : syracuseStep 1112285 = 417107) (by norm_num)
theorem B1669349 : Blo 658307 1669349 := bbase (se 4 (by rfl) ⟨156501, by rfl⟩ : syracuseStep 1669349 = 313003) (by norm_num)
theorem B751901 : Blo 658307 751901 := bbase (se 3 (by rfl) ⟨140981, by rfl⟩ : syracuseStep 751901 = 281963) (by norm_num)
theorem B2816309 : Blo 658307 2816309 := bbase (se 5 (by rfl) ⟨132014, by rfl⟩ : syracuseStep 2816309 = 264029) (by norm_num)
theorem B1112413 : Blo 658307 1112413 := bbase (se 3 (by rfl) ⟨208577, by rfl⟩ : syracuseStep 1112413 = 417155) (by norm_num)
theorem B2226581 : Blo 658307 2226581 := bbase (se 6 (by rfl) ⟨52185, by rfl⟩ : syracuseStep 2226581 = 104371) (by norm_num)
theorem B1112501 : Blo 658307 1112501 := bbase (se 5 (by rfl) ⟨52148, by rfl⟩ : syracuseStep 1112501 = 104297) (by norm_num)
theorem B1505837 : Blo 658307 1505837 := bbase (se 3 (by rfl) ⟨282344, by rfl⟩ : syracuseStep 1505837 = 564689) (by norm_num)
theorem B1112629 : Blo 658307 1112629 := bbase (se 5 (by rfl) ⟨52154, by rfl⟩ : syracuseStep 1112629 = 104309) (by norm_num)
theorem B1669693 : Blo 658307 1669693 := bbase (se 3 (by rfl) ⟨313067, by rfl⟩ : syracuseStep 1669693 = 626135) (by norm_num)
theorem B1407557 : Blo 658307 1407557 := bbase (se 4 (by rfl) ⟨131958, by rfl⟩ : syracuseStep 1407557 = 263917) (by norm_num)
theorem B1112717 : Blo 658307 1112717 := bbase (se 3 (by rfl) ⟨208634, by rfl⟩ : syracuseStep 1112717 = 417269) (by norm_num)
theorem B5012117 : Blo 658307 5012117 := bbase (se 6 (by rfl) ⟨117471, by rfl⟩ : syracuseStep 5012117 = 234943) (by norm_num)
theorem B1669805 : Blo 658307 1669805 := bbase (se 3 (by rfl) ⟨313088, by rfl⟩ : syracuseStep 1669805 = 626177) (by norm_num)
theorem B5634805 : Blo 658307 5634805 := bbase (se 5 (by rfl) ⟨264131, by rfl⟩ : syracuseStep 5634805 = 528263) (by norm_num)
theorem B1112845 : Blo 658307 1112845 := bbase (se 3 (by rfl) ⟨208658, by rfl⟩ : syracuseStep 1112845 = 417317) (by norm_num)
theorem B2227013 : Blo 658307 2227013 := bbase (se 4 (by rfl) ⟨208782, by rfl⟩ : syracuseStep 2227013 = 417565) (by norm_num)
theorem B4225877 : Blo 658307 4225877 := bbase (se 9 (by rfl) ⟨12380, by rfl⟩ : syracuseStep 4225877 = 24761) (by norm_num)
theorem B1112933 : Blo 658307 1112933 := bbase (se 4 (by rfl) ⟨104337, by rfl⟩ : syracuseStep 1112933 = 208675) (by norm_num)
theorem B752485 : Blo 658307 752485 := bbase (se 4 (by rfl) ⟨70545, by rfl⟩ : syracuseStep 752485 = 141091) (by norm_num)
theorem B1669997 : Blo 658307 1669997 := bbase (se 3 (by rfl) ⟨313124, by rfl⟩ : syracuseStep 1669997 = 626249) (by norm_num)
theorem B1342325 : Blo 658307 1342325 := bbase (se 5 (by rfl) ⟨62921, by rfl⟩ : syracuseStep 1342325 = 125843) (by norm_num)
theorem B1113061 : Blo 658307 1113061 := bbase (se 4 (by rfl) ⟨104349, by rfl⟩ : syracuseStep 1113061 = 208699) (by norm_num)
theorem B3177461 : Blo 658307 3177461 := bbase (se 5 (by rfl) ⟨148943, by rfl⟩ : syracuseStep 3177461 = 297887) (by norm_num)
theorem B1113149 : Blo 658307 1113149 := bbase (se 3 (by rfl) ⟨208715, by rfl⟩ : syracuseStep 1113149 = 417431) (by norm_num)
theorem B3767381 : Blo 658307 3767381 := bbase (se 8 (by rfl) ⟨22074, by rfl⟩ : syracuseStep 3767381 = 44149) (by norm_num)
theorem B1113277 : Blo 658307 1113277 := bbase (se 3 (by rfl) ⟨208739, by rfl⟩ : syracuseStep 1113277 = 417479) (by norm_num)
theorem B1670341 : Blo 658307 1670341 := bbase (se 4 (by rfl) ⟨156594, by rfl⟩ : syracuseStep 1670341 = 313189) (by norm_num)
theorem B2227445 : Blo 658307 2227445 := bbase (se 5 (by rfl) ⟨104411, by rfl⟩ : syracuseStep 2227445 = 208823) (by norm_num)
theorem B3341573 : Blo 658307 3341573 := bbase (se 4 (by rfl) ⟨313272, by rfl⟩ : syracuseStep 3341573 = 626545) (by norm_num)
theorem B2817301 : Blo 658307 2817301 := bbase (se 6 (by rfl) ⟨66030, by rfl⟩ : syracuseStep 2817301 = 132061) (by norm_num)
theorem B1113365 : Blo 658307 1113365 := bbase (se 6 (by rfl) ⟨26094, by rfl⟩ : syracuseStep 1113365 = 52189) (by norm_num)
theorem B1670453 : Blo 658307 1670453 := bbase (se 5 (by rfl) ⟨78302, by rfl⟩ : syracuseStep 1670453 = 156605) (by norm_num)
theorem B752969 : Blo 658307 752969 := bbase (se 2 (by rfl) ⟨282363, by rfl⟩ : syracuseStep 752969 = 564727) (by norm_num)
theorem B1113493 : Blo 658307 1113493 := bbase (se 6 (by rfl) ⟨26097, by rfl⟩ : syracuseStep 1113493 = 52195) (by norm_num)
theorem B1408421 : Blo 658307 1408421 := bbase (se 4 (by rfl) ⟨132039, by rfl⟩ : syracuseStep 1408421 = 264079) (by norm_num)
theorem B16940501 : Blo 658307 16940501 := bbase (se 7 (by rfl) ⟨198521, by rfl⟩ : syracuseStep 16940501 = 397043) (by norm_num)
theorem B1113581 : Blo 658307 1113581 := bbase (se 3 (by rfl) ⟨208796, by rfl⟩ : syracuseStep 1113581 = 417593) (by norm_num)
theorem B1670645 : Blo 658307 1670645 := bbase (se 5 (by rfl) ⟨78311, by rfl⟩ : syracuseStep 1670645 = 156623) (by norm_num)
theorem B1408565 : Blo 658307 1408565 := bbase (se 5 (by rfl) ⟨66026, by rfl⟩ : syracuseStep 1408565 = 132053) (by norm_num)
theorem B1113709 : Blo 658307 1113709 := bbase (se 3 (by rfl) ⟨208820, by rfl⟩ : syracuseStep 1113709 = 417641) (by norm_num)
theorem B2227877 : Blo 658307 2227877 := bbase (se 4 (by rfl) ⟨208863, by rfl⟩ : syracuseStep 2227877 = 417727) (by norm_num)
theorem B1113797 : Blo 658307 1113797 := bbase (se 4 (by rfl) ⟨104418, by rfl⟩ : syracuseStep 1113797 = 208837) (by norm_num)
theorem B1113925 : Blo 658307 1113925 := bbase (se 4 (by rfl) ⟨104430, by rfl⟩ : syracuseStep 1113925 = 208861) (by norm_num)
theorem B1670989 : Blo 658307 1670989 := bbase (se 3 (by rfl) ⟨313310, by rfl⟩ : syracuseStep 1670989 = 626621) (by norm_num)
theorem B3211093 : Blo 658307 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B1114013 : Blo 658307 1114013 := bbase (se 3 (by rfl) ⟨208877, by rfl⟩ : syracuseStep 1114013 = 417755) (by norm_num)
theorem B1671101 : Blo 658307 1671101 := bbase (se 3 (by rfl) ⟨313331, by rfl⟩ : syracuseStep 1671101 = 626663) (by norm_num)
theorem B1114195 : Blo 658307 1114195 := bstep (se 1 (by rfl) ⟨835646, by rfl⟩ : syracuseStep 1114195 = 1671293) B1671293
theorem B1671313 : Blo 658307 1671313 := bstep (se 2 (by rfl) ⟨626742, by rfl⟩ : syracuseStep 1671313 = 1253485) B1253485
theorem B950449 : Blo 658307 950449 := bstep (se 2 (by rfl) ⟨356418, by rfl⟩ : syracuseStep 950449 = 712837) B712837
theorem B1114337 : Blo 658307 1114337 := bstep (se 2 (by rfl) ⟨417876, by rfl⟩ : syracuseStep 1114337 = 835753) B835753
theorem B2228525 : Blo 658307 2228525 := bstep (se 3 (by rfl) ⟨417848, by rfl⟩ : syracuseStep 2228525 = 835697) B835697
theorem B1114465 : Blo 658307 1114465 := bstep (se 2 (by rfl) ⟨417924, by rfl⟩ : syracuseStep 1114465 = 835849) B835849
theorem B2228579 : Blo 658307 2228579 := bstep (se 1 (by rfl) ⟨1671434, by rfl⟩ : syracuseStep 2228579 = 3342869) B3342869
theorem B1114499 : Blo 658307 1114499 := bstep (se 1 (by rfl) ⟨835874, by rfl⟩ : syracuseStep 1114499 = 1671749) B1671749
theorem B1671587 : Blo 658307 1671587 := bstep (se 1 (by rfl) ⟨1253690, by rfl⟩ : syracuseStep 1671587 = 2507381) B2507381
theorem B7504325 : Blo 658307 7504325 := bstep (se 4 (by rfl) ⟨703530, by rfl⟩ : syracuseStep 7504325 = 1407061) B1407061
theorem B1114627 : Blo 658307 1114627 := bstep (se 1 (by rfl) ⟨835970, by rfl⟩ : syracuseStep 1114627 = 1671941) B1671941
theorem B1507889 : Blo 658307 1507889 := bstep (se 2 (by rfl) ⟨565458, by rfl⟩ : syracuseStep 1507889 = 1130917) B1130917
theorem B1671779 : Blo 658307 1671779 := bstep (se 1 (by rfl) ⟨1253834, by rfl⟩ : syracuseStep 1671779 = 2507669) B2507669
theorem B2228849 : Blo 658307 2228849 := bstep (se 2 (by rfl) ⟨835818, by rfl⟩ : syracuseStep 2228849 = 1671637) B1671637
theorem B1114769 : Blo 658307 1114769 := bstep (se 2 (by rfl) ⟨418038, by rfl⟩ : syracuseStep 1114769 = 836077) B836077
theorem B1114897 : Blo 658307 1114897 := bstep (se 2 (by rfl) ⟨418086, by rfl⟩ : syracuseStep 1114897 = 836173) B836173
theorem B1114931 : Blo 658307 1114931 := bstep (se 1 (by rfl) ⟨836198, by rfl⟩ : syracuseStep 1114931 = 1672397) B1672397
theorem B4752269 : Blo 658307 4752269 := bstep (se 3 (by rfl) ⟨891050, by rfl⟩ : syracuseStep 4752269 = 1782101) B1782101
theorem B1115059 : Blo 658307 1115059 := bstep (se 1 (by rfl) ⟨836294, by rfl⟩ : syracuseStep 1115059 = 1672589) B1672589
theorem B1115201 : Blo 658307 1115201 := bstep (se 2 (by rfl) ⟨418200, by rfl⟩ : syracuseStep 1115201 = 836401) B836401
theorem B2229389 : Blo 658307 2229389 := bstep (se 3 (by rfl) ⟨418010, by rfl⟩ : syracuseStep 2229389 = 836021) B836021
theorem B2262161 : Blo 658307 2262161 := bstep (se 2 (by rfl) ⟨848310, by rfl⟩ : syracuseStep 2262161 = 1696621) B1696621
theorem B2819249 : Blo 658307 2819249 := bstep (se 2 (by rfl) ⟨1057218, by rfl⟩ : syracuseStep 2819249 = 2114437) B2114437
theorem B1115329 : Blo 658307 1115329 := bstep (se 2 (by rfl) ⟨418248, by rfl⟩ : syracuseStep 1115329 = 836497) B836497
theorem B2229443 : Blo 658307 2229443 := bstep (se 1 (by rfl) ⟨1672082, by rfl⟩ : syracuseStep 2229443 = 3344165) B3344165
theorem B1115363 : Blo 658307 1115363 := bstep (se 1 (by rfl) ⟨836522, by rfl⟩ : syracuseStep 1115363 = 1673045) B1673045
theorem B1115491 : Blo 658307 1115491 := bstep (se 1 (by rfl) ⟨836618, by rfl⟩ : syracuseStep 1115491 = 1673237) B1673237
theorem B13731185 : Blo 658307 13731185 := bstep (se 2 (by rfl) ⟨5149194, by rfl⟩ : syracuseStep 13731185 = 10298389) B10298389
theorem B2229713 : Blo 658307 2229713 := bstep (se 2 (by rfl) ⟨836142, by rfl⟩ : syracuseStep 2229713 = 1672285) B1672285
theorem B6358499 : Blo 658307 6358499 := bstep (se 1 (by rfl) ⟨4768874, by rfl⟩ : syracuseStep 6358499 = 9537749) B9537749
theorem B1115633 : Blo 658307 1115633 := bstep (se 2 (by rfl) ⟨418362, by rfl⟩ : syracuseStep 1115633 = 836725) B836725
theorem B3769841 : Blo 658307 3769841 := bstep (se 2 (by rfl) ⟨1413690, by rfl⟩ : syracuseStep 3769841 = 2827381) B2827381
theorem B1672721 : Blo 658307 1672721 := bstep (se 2 (by rfl) ⟨627270, by rfl⟩ : syracuseStep 1672721 = 1254541) B1254541
theorem B1672771 : Blo 658307 1672771 := bstep (se 1 (by rfl) ⟨1254578, by rfl⟩ : syracuseStep 1672771 = 2509157) B2509157
theorem B1115761 : Blo 658307 1115761 := bstep (se 2 (by rfl) ⟨418410, by rfl⟩ : syracuseStep 1115761 = 836821) B836821
theorem B1115795 : Blo 658307 1115795 := bstep (se 1 (by rfl) ⟨836846, by rfl⟩ : syracuseStep 1115795 = 1673693) B1673693
theorem B1672913 : Blo 658307 1672913 := bstep (se 2 (by rfl) ⟨627342, by rfl⟩ : syracuseStep 1672913 = 1254685) B1254685
theorem B1115923 : Blo 658307 1115923 := bstep (se 1 (by rfl) ⟨836942, by rfl⟩ : syracuseStep 1115923 = 1673885) B1673885
theorem B952225 : Blo 658307 952225 := bstep (se 2 (by rfl) ⟨357084, by rfl⟩ : syracuseStep 952225 = 714169) B714169
theorem B1116065 : Blo 658307 1116065 := bstep (se 2 (by rfl) ⟨418524, by rfl⟩ : syracuseStep 1116065 = 837049) B837049
theorem B1411025 : Blo 658307 1411025 := bstep (se 2 (by rfl) ⟨529134, by rfl⟩ : syracuseStep 1411025 = 1058269) B1058269
theorem B2230253 : Blo 658307 2230253 := bstep (se 3 (by rfl) ⟨418172, by rfl⟩ : syracuseStep 2230253 = 836345) B836345
theorem B1116193 : Blo 658307 1116193 := bstep (se 2 (by rfl) ⟨418572, by rfl⟩ : syracuseStep 1116193 = 837145) B837145
theorem B2230307 : Blo 658307 2230307 := bstep (se 1 (by rfl) ⟨1672730, by rfl⟩ : syracuseStep 2230307 = 3345461) B3345461
theorem B1116227 : Blo 658307 1116227 := bstep (se 1 (by rfl) ⟨837170, by rfl⟩ : syracuseStep 1116227 = 1674341) B1674341
theorem B1116355 : Blo 658307 1116355 := bstep (se 1 (by rfl) ⟨837266, by rfl⟩ : syracuseStep 1116355 = 1674533) B1674533
theorem B2230577 : Blo 658307 2230577 := bstep (se 2 (by rfl) ⟨836466, by rfl⟩ : syracuseStep 2230577 = 1672933) B1672933
theorem B1116497 : Blo 658307 1116497 := bstep (se 2 (by rfl) ⟨418686, by rfl⟩ : syracuseStep 1116497 = 837373) B837373
theorem B1509713 : Blo 658307 1509713 := bstep (se 2 (by rfl) ⟨566142, by rfl⟩ : syracuseStep 1509713 = 1132285) B1132285
theorem B723395 : Blo 658307 723395 := bstep (se 1 (by rfl) ⟨542546, by rfl⟩ : syracuseStep 723395 = 1085093) B1085093
theorem B5016005 : Blo 658307 5016005 := bstep (se 4 (by rfl) ⟨470250, by rfl⟩ : syracuseStep 5016005 = 940501) B940501
theorem B1116625 : Blo 658307 1116625 := bstep (se 2 (by rfl) ⟨418734, by rfl⟩ : syracuseStep 1116625 = 837469) B837469
theorem B4524515 : Blo 658307 4524515 := bstep (se 1 (by rfl) ⟨3393386, by rfl⟩ : syracuseStep 4524515 = 6786773) B6786773
theorem B1116659 : Blo 658307 1116659 := bstep (se 1 (by rfl) ⟨837494, by rfl⟩ : syracuseStep 1116659 = 1674989) B1674989
theorem B7146083 : Blo 658307 7146083 := bstep (se 1 (by rfl) ⟨5359562, by rfl⟩ : syracuseStep 7146083 = 10719125) B10719125
theorem B1116787 : Blo 658307 1116787 := bstep (se 1 (by rfl) ⟨837590, by rfl⟩ : syracuseStep 1116787 = 1675181) B1675181
theorem B4229795 : Blo 658307 4229795 := bstep (se 1 (by rfl) ⟨3172346, by rfl⟩ : syracuseStep 4229795 = 6344693) B6344693
theorem B1673905 : Blo 658307 1673905 := bstep (se 2 (by rfl) ⟨627714, by rfl⟩ : syracuseStep 1673905 = 1255429) B1255429
theorem B3345137 : Blo 658307 3345137 := bstep (se 2 (by rfl) ⟨1254426, by rfl⟩ : syracuseStep 3345137 = 2508853) B2508853
theorem B1116929 : Blo 658307 1116929 := bstep (se 2 (by rfl) ⟨418848, by rfl⟩ : syracuseStep 1116929 = 837697) B837697
theorem B2231117 : Blo 658307 2231117 := bstep (se 3 (by rfl) ⟨418334, by rfl⟩ : syracuseStep 2231117 = 836669) B836669
theorem B1117057 : Blo 658307 1117057 := bstep (se 2 (by rfl) ⟨418896, by rfl⟩ : syracuseStep 1117057 = 837793) B837793
theorem B658307 : Blo 658307 658307 := bstep (se 1 (by rfl) ⟨493730, by rfl⟩ : syracuseStep 658307 = 987461) B987461
theorem B2231171 : Blo 658307 2231171 := bstep (se 1 (by rfl) ⟨1673378, by rfl⟩ : syracuseStep 2231171 = 3346757) B3346757
theorem B658323 : Blo 658307 658323 := bstep (se 1 (by rfl) ⟨493742, by rfl⟩ : syracuseStep 658323 = 987485) B987485
theorem B658339 : Blo 658307 658339 := bstep (se 1 (by rfl) ⟨493754, by rfl⟩ : syracuseStep 658339 = 987509) B987509
theorem B1117091 : Blo 658307 1117091 := bstep (se 1 (by rfl) ⟨837818, by rfl⟩ : syracuseStep 1117091 = 1675637) B1675637
theorem B3771299 : Blo 658307 3771299 := bstep (se 1 (by rfl) ⟨2828474, by rfl⟩ : syracuseStep 3771299 = 5656949) B5656949
theorem B658355 : Blo 658307 658355 := bstep (se 1 (by rfl) ⟨493766, by rfl⟩ : syracuseStep 658355 = 987533) B987533
theorem B658371 : Blo 658307 658371 := bstep (se 1 (by rfl) ⟨493778, by rfl⟩ : syracuseStep 658371 = 987557) B987557
theorem B1674179 : Blo 658307 1674179 := bstep (se 1 (by rfl) ⟨1255634, by rfl⟩ : syracuseStep 1674179 = 2511269) B2511269
theorem B658387 : Blo 658307 658387 := bstep (se 1 (by rfl) ⟨493790, by rfl⟩ : syracuseStep 658387 = 987581) B987581
theorem B658403 : Blo 658307 658403 := bstep (se 1 (by rfl) ⟨493802, by rfl⟩ : syracuseStep 658403 = 987605) B987605
theorem B658419 : Blo 658307 658419 := bstep (se 1 (by rfl) ⟨493814, by rfl⟩ : syracuseStep 658419 = 987629) B987629
theorem B658435 : Blo 658307 658435 := bstep (se 1 (by rfl) ⟨493826, by rfl⟩ : syracuseStep 658435 = 987653) B987653
theorem B658451 : Blo 658307 658451 := bstep (se 1 (by rfl) ⟨493838, by rfl⟩ : syracuseStep 658451 = 987677) B987677
theorem B658467 : Blo 658307 658467 := bstep (se 1 (by rfl) ⟨493850, by rfl⟩ : syracuseStep 658467 = 987701) B987701
theorem B1117219 : Blo 658307 1117219 := bstep (se 1 (by rfl) ⟨837914, by rfl⟩ : syracuseStep 1117219 = 1675829) B1675829
theorem B658483 : Blo 658307 658483 := bstep (se 1 (by rfl) ⟨493862, by rfl⟩ : syracuseStep 658483 = 987725) B987725
theorem B658499 : Blo 658307 658499 := bstep (se 1 (by rfl) ⟨493874, by rfl⟩ : syracuseStep 658499 = 987749) B987749
theorem B658515 : Blo 658307 658515 := bstep (se 1 (by rfl) ⟨493886, by rfl⟩ : syracuseStep 658515 = 987773) B987773
theorem B658531 : Blo 658307 658531 := bstep (se 1 (by rfl) ⟨493898, by rfl⟩ : syracuseStep 658531 = 987797) B987797
theorem B658547 : Blo 658307 658547 := bstep (se 1 (by rfl) ⟨493910, by rfl⟩ : syracuseStep 658547 = 987821) B987821
theorem B953473 : Blo 658307 953473 := bstep (se 2 (by rfl) ⟨357552, by rfl⟩ : syracuseStep 953473 = 715105) B715105
theorem B658563 : Blo 658307 658563 := bstep (se 1 (by rfl) ⟨493922, by rfl⟩ : syracuseStep 658563 = 987845) B987845
theorem B1674371 : Blo 658307 1674371 := bstep (se 1 (by rfl) ⟨1255778, by rfl⟩ : syracuseStep 1674371 = 2511557) B2511557
theorem B2231441 : Blo 658307 2231441 := bstep (se 2 (by rfl) ⟨836790, by rfl⟩ : syracuseStep 2231441 = 1673581) B1673581
theorem B658579 : Blo 658307 658579 := bstep (se 1 (by rfl) ⟨493934, by rfl⟩ : syracuseStep 658579 = 987869) B987869
theorem B658595 : Blo 658307 658595 := bstep (se 1 (by rfl) ⟨493946, by rfl⟩ : syracuseStep 658595 = 987893) B987893
theorem B1117361 : Blo 658307 1117361 := bstep (se 2 (by rfl) ⟨419010, by rfl⟩ : syracuseStep 1117361 = 838021) B838021
theorem B658611 : Blo 658307 658611 := bstep (se 1 (by rfl) ⟨493958, by rfl⟩ : syracuseStep 658611 = 987917) B987917
theorem B658627 : Blo 658307 658627 := bstep (se 1 (by rfl) ⟨493970, by rfl⟩ : syracuseStep 658627 = 987941) B987941
theorem B3214541 : Blo 658307 3214541 := bstep (se 3 (by rfl) ⟨602726, by rfl⟩ : syracuseStep 3214541 = 1205453) B1205453
theorem B658643 : Blo 658307 658643 := bstep (se 1 (by rfl) ⟨493982, by rfl⟩ : syracuseStep 658643 = 987965) B987965
theorem B658659 : Blo 658307 658659 := bstep (se 1 (by rfl) ⟨493994, by rfl⟩ : syracuseStep 658659 = 987989) B987989
theorem B4754659 : Blo 658307 4754659 := bstep (se 1 (by rfl) ⟨3565994, by rfl⟩ : syracuseStep 4754659 = 7131989) B7131989
theorem B3017969 : Blo 658307 3017969 := bstep (se 2 (by rfl) ⟨1131738, by rfl⟩ : syracuseStep 3017969 = 2263477) B2263477
theorem B658675 : Blo 658307 658675 := bstep (se 1 (by rfl) ⟨494006, by rfl⟩ : syracuseStep 658675 = 988013) B988013
theorem B658691 : Blo 658307 658691 := bstep (se 1 (by rfl) ⟨494018, by rfl⟩ : syracuseStep 658691 = 988037) B988037
theorem B658707 : Blo 658307 658707 := bstep (se 1 (by rfl) ⟨494030, by rfl⟩ : syracuseStep 658707 = 988061) B988061
theorem B658723 : Blo 658307 658723 := bstep (se 1 (by rfl) ⟨494042, by rfl⟩ : syracuseStep 658723 = 988085) B988085
theorem B1117489 : Blo 658307 1117489 := bstep (se 2 (by rfl) ⟨419058, by rfl⟩ : syracuseStep 1117489 = 838117) B838117
theorem B658739 : Blo 658307 658739 := bstep (se 1 (by rfl) ⟨494054, by rfl⟩ : syracuseStep 658739 = 988109) B988109
theorem B658755 : Blo 658307 658755 := bstep (se 1 (by rfl) ⟨494066, by rfl⟩ : syracuseStep 658755 = 988133) B988133
theorem B658771 : Blo 658307 658771 := bstep (se 1 (by rfl) ⟨494078, by rfl⟩ : syracuseStep 658771 = 988157) B988157
theorem B1117523 : Blo 658307 1117523 := bstep (se 1 (by rfl) ⟨838142, by rfl⟩ : syracuseStep 1117523 = 1676285) B1676285
theorem B658787 : Blo 658307 658787 := bstep (se 1 (by rfl) ⟨494090, by rfl⟩ : syracuseStep 658787 = 988181) B988181
theorem B658803 : Blo 658307 658803 := bstep (se 1 (by rfl) ⟨494102, by rfl⟩ : syracuseStep 658803 = 988205) B988205
theorem B658819 : Blo 658307 658819 := bstep (se 1 (by rfl) ⟨494114, by rfl⟩ : syracuseStep 658819 = 988229) B988229
theorem B658835 : Blo 658307 658835 := bstep (se 1 (by rfl) ⟨494126, by rfl⟩ : syracuseStep 658835 = 988253) B988253
theorem B658851 : Blo 658307 658851 := bstep (se 1 (by rfl) ⟨494138, by rfl⟩ : syracuseStep 658851 = 988277) B988277
theorem B658867 : Blo 658307 658867 := bstep (se 1 (by rfl) ⟨494150, by rfl⟩ : syracuseStep 658867 = 988301) B988301
theorem B658883 : Blo 658307 658883 := bstep (se 1 (by rfl) ⟨494162, by rfl⟩ : syracuseStep 658883 = 988325) B988325
theorem B658899 : Blo 658307 658899 := bstep (se 1 (by rfl) ⟨494174, by rfl⟩ : syracuseStep 658899 = 988349) B988349
theorem B658915 : Blo 658307 658915 := bstep (se 1 (by rfl) ⟨494186, by rfl⟩ : syracuseStep 658915 = 988373) B988373
theorem B658931 : Blo 658307 658931 := bstep (se 1 (by rfl) ⟨494198, by rfl⟩ : syracuseStep 658931 = 988397) B988397
theorem B658947 : Blo 658307 658947 := bstep (se 1 (by rfl) ⟨494210, by rfl⟩ : syracuseStep 658947 = 988421) B988421
theorem B658963 : Blo 658307 658963 := bstep (se 1 (by rfl) ⟨494222, by rfl⟩ : syracuseStep 658963 = 988445) B988445
theorem B658979 : Blo 658307 658979 := bstep (se 1 (by rfl) ⟨494234, by rfl⟩ : syracuseStep 658979 = 988469) B988469
theorem B658995 : Blo 658307 658995 := bstep (se 1 (by rfl) ⟨494246, by rfl⟩ : syracuseStep 658995 = 988493) B988493
theorem B659011 : Blo 658307 659011 := bstep (se 1 (by rfl) ⟨494258, by rfl⟩ : syracuseStep 659011 = 988517) B988517
theorem B2821709 : Blo 658307 2821709 := bstep (se 3 (by rfl) ⟨529070, by rfl⟩ : syracuseStep 2821709 = 1058141) B1058141
theorem B659027 : Blo 658307 659027 := bstep (se 1 (by rfl) ⟨494270, by rfl⟩ : syracuseStep 659027 = 988541) B988541
theorem B659043 : Blo 658307 659043 := bstep (se 1 (by rfl) ⟨494282, by rfl⟩ : syracuseStep 659043 = 988565) B988565
theorem B659059 : Blo 658307 659059 := bstep (se 1 (by rfl) ⟨494294, by rfl⟩ : syracuseStep 659059 = 988589) B988589
theorem B659075 : Blo 658307 659075 := bstep (se 1 (by rfl) ⟨494306, by rfl⟩ : syracuseStep 659075 = 988613) B988613
theorem B659091 : Blo 658307 659091 := bstep (se 1 (by rfl) ⟨494318, by rfl⟩ : syracuseStep 659091 = 988637) B988637
theorem B659107 : Blo 658307 659107 := bstep (se 1 (by rfl) ⟨494330, by rfl⟩ : syracuseStep 659107 = 988661) B988661
theorem B2231981 : Blo 658307 2231981 := bstep (se 3 (by rfl) ⟨418496, by rfl⟩ : syracuseStep 2231981 = 836993) B836993
theorem B659123 : Blo 658307 659123 := bstep (se 1 (by rfl) ⟨494342, by rfl⟩ : syracuseStep 659123 = 988685) B988685
theorem B659139 : Blo 658307 659139 := bstep (se 1 (by rfl) ⟨494354, by rfl⟩ : syracuseStep 659139 = 988709) B988709
theorem B659155 : Blo 658307 659155 := bstep (se 1 (by rfl) ⟨494366, by rfl⟩ : syracuseStep 659155 = 988733) B988733
theorem B32640725 : Blo 658307 32640725 := bstep (se 7 (by rfl) ⟨382508, by rfl⟩ : syracuseStep 32640725 = 765017) B765017
theorem B659171 : Blo 658307 659171 := bstep (se 1 (by rfl) ⟨494378, by rfl⟩ : syracuseStep 659171 = 988757) B988757
theorem B2232035 : Blo 658307 2232035 := bstep (se 1 (by rfl) ⟨1674026, by rfl⟩ : syracuseStep 2232035 = 3348053) B3348053
theorem B659187 : Blo 658307 659187 := bstep (se 1 (by rfl) ⟨494390, by rfl⟩ : syracuseStep 659187 = 988781) B988781
theorem B659203 : Blo 658307 659203 := bstep (se 1 (by rfl) ⟨494402, by rfl⟩ : syracuseStep 659203 = 988805) B988805
theorem B659219 : Blo 658307 659219 := bstep (se 1 (by rfl) ⟨494414, by rfl⟩ : syracuseStep 659219 = 988829) B988829
theorem B659235 : Blo 658307 659235 := bstep (se 1 (by rfl) ⟨494426, by rfl⟩ : syracuseStep 659235 = 988853) B988853
theorem B2002733 : Blo 658307 2002733 := bstep (se 3 (by rfl) ⟨375512, by rfl⟩ : syracuseStep 2002733 = 751025) B751025
theorem B659251 : Blo 658307 659251 := bstep (se 1 (by rfl) ⟨494438, by rfl⟩ : syracuseStep 659251 = 988877) B988877
theorem B659267 : Blo 658307 659267 := bstep (se 1 (by rfl) ⟨494450, by rfl⟩ : syracuseStep 659267 = 988901) B988901
theorem B659283 : Blo 658307 659283 := bstep (se 1 (by rfl) ⟨494462, by rfl⟩ : syracuseStep 659283 = 988925) B988925
theorem B659299 : Blo 658307 659299 := bstep (se 1 (by rfl) ⟨494474, by rfl⟩ : syracuseStep 659299 = 988949) B988949
theorem B4231025 : Blo 658307 4231025 := bstep (se 2 (by rfl) ⟨1586634, by rfl⟩ : syracuseStep 4231025 = 3173269) B3173269
theorem B659315 : Blo 658307 659315 := bstep (se 1 (by rfl) ⟨494486, by rfl⟩ : syracuseStep 659315 = 988973) B988973
theorem B659331 : Blo 658307 659331 := bstep (se 1 (by rfl) ⟨494498, by rfl⟩ : syracuseStep 659331 = 988997) B988997
theorem B5345165 : Blo 658307 5345165 := bstep (se 3 (by rfl) ⟨1002218, by rfl⟩ : syracuseStep 5345165 = 2004437) B2004437
theorem B659347 : Blo 658307 659347 := bstep (se 1 (by rfl) ⟨494510, by rfl⟩ : syracuseStep 659347 = 989021) B989021
theorem B659363 : Blo 658307 659363 := bstep (se 1 (by rfl) ⟨494522, by rfl⟩ : syracuseStep 659363 = 989045) B989045
theorem B659379 : Blo 658307 659379 := bstep (se 1 (by rfl) ⟨494534, by rfl⟩ : syracuseStep 659379 = 989069) B989069
theorem B659395 : Blo 658307 659395 := bstep (se 1 (by rfl) ⟨494546, by rfl⟩ : syracuseStep 659395 = 989093) B989093
theorem B659411 : Blo 658307 659411 := bstep (se 1 (by rfl) ⟨494558, by rfl⟩ : syracuseStep 659411 = 989117) B989117
theorem B659427 : Blo 658307 659427 := bstep (se 1 (by rfl) ⟨494570, by rfl⟩ : syracuseStep 659427 = 989141) B989141
theorem B6033379 : Blo 658307 6033379 := bstep (se 1 (by rfl) ⟨4525034, by rfl⟩ : syracuseStep 6033379 = 9050069) B9050069
theorem B2232305 : Blo 658307 2232305 := bstep (se 2 (by rfl) ⟨837114, by rfl⟩ : syracuseStep 2232305 = 1674229) B1674229
theorem B659443 : Blo 658307 659443 := bstep (se 1 (by rfl) ⟨494582, by rfl⟩ : syracuseStep 659443 = 989165) B989165
theorem B659459 : Blo 658307 659459 := bstep (se 1 (by rfl) ⟨494594, by rfl⟩ : syracuseStep 659459 = 989189) B989189
theorem B659475 : Blo 658307 659475 := bstep (se 1 (by rfl) ⟨494606, by rfl⟩ : syracuseStep 659475 = 989213) B989213
theorem B659491 : Blo 658307 659491 := bstep (se 1 (by rfl) ⟨494618, by rfl⟩ : syracuseStep 659491 = 989237) B989237
theorem B1675313 : Blo 658307 1675313 := bstep (se 2 (by rfl) ⟨628242, by rfl⟩ : syracuseStep 1675313 = 1256485) B1256485
theorem B659507 : Blo 658307 659507 := bstep (se 1 (by rfl) ⟨494630, by rfl⟩ : syracuseStep 659507 = 989261) B989261
theorem B659523 : Blo 658307 659523 := bstep (se 1 (by rfl) ⟨494642, by rfl⟩ : syracuseStep 659523 = 989285) B989285
theorem B659539 : Blo 658307 659539 := bstep (se 1 (by rfl) ⟨494654, by rfl⟩ : syracuseStep 659539 = 989309) B989309
theorem B659555 : Blo 658307 659555 := bstep (se 1 (by rfl) ⟨494666, by rfl⟩ : syracuseStep 659555 = 989333) B989333
theorem B1675363 : Blo 658307 1675363 := bstep (se 1 (by rfl) ⟨1256522, by rfl⟩ : syracuseStep 1675363 = 2513045) B2513045
theorem B659571 : Blo 658307 659571 := bstep (se 1 (by rfl) ⟨494678, by rfl⟩ : syracuseStep 659571 = 989357) B989357
theorem B659587 : Blo 658307 659587 := bstep (se 1 (by rfl) ⟨494690, by rfl⟩ : syracuseStep 659587 = 989381) B989381
theorem B659603 : Blo 658307 659603 := bstep (se 1 (by rfl) ⟨494702, by rfl⟩ : syracuseStep 659603 = 989405) B989405
theorem B659619 : Blo 658307 659619 := bstep (se 1 (by rfl) ⟨494714, by rfl⟩ : syracuseStep 659619 = 989429) B989429
theorem B3346595 : Blo 658307 3346595 := bstep (se 1 (by rfl) ⟨2509946, by rfl⟩ : syracuseStep 3346595 = 5019893) B5019893
theorem B659635 : Blo 658307 659635 := bstep (se 1 (by rfl) ⟨494726, by rfl⟩ : syracuseStep 659635 = 989453) B989453
theorem B659651 : Blo 658307 659651 := bstep (se 1 (by rfl) ⟨494738, by rfl⟩ : syracuseStep 659651 = 989477) B989477
theorem B659667 : Blo 658307 659667 := bstep (se 1 (by rfl) ⟨494750, by rfl⟩ : syracuseStep 659667 = 989501) B989501
theorem B659683 : Blo 658307 659683 := bstep (se 1 (by rfl) ⟨494762, by rfl⟩ : syracuseStep 659683 = 989525) B989525
theorem B1675505 : Blo 658307 1675505 := bstep (se 2 (by rfl) ⟨628314, by rfl⟩ : syracuseStep 1675505 = 1256629) B1256629
theorem B659699 : Blo 658307 659699 := bstep (se 1 (by rfl) ⟨494774, by rfl⟩ : syracuseStep 659699 = 989549) B989549
theorem B659715 : Blo 658307 659715 := bstep (se 1 (by rfl) ⟨494786, by rfl⟩ : syracuseStep 659715 = 989573) B989573
theorem B659731 : Blo 658307 659731 := bstep (se 1 (by rfl) ⟨494798, by rfl⟩ : syracuseStep 659731 = 989597) B989597
theorem B659747 : Blo 658307 659747 := bstep (se 1 (by rfl) ⟨494810, by rfl⟩ : syracuseStep 659747 = 989621) B989621
theorem B659763 : Blo 658307 659763 := bstep (se 1 (by rfl) ⟨494822, by rfl⟩ : syracuseStep 659763 = 989645) B989645
theorem B659779 : Blo 658307 659779 := bstep (se 1 (by rfl) ⟨494834, by rfl⟩ : syracuseStep 659779 = 989669) B989669
theorem B987473 : Blo 658307 987473 := bstep (se 2 (by rfl) ⟨370302, by rfl⟩ : syracuseStep 987473 = 740605) B740605
theorem B659795 : Blo 658307 659795 := bstep (se 1 (by rfl) ⟨494846, by rfl⟩ : syracuseStep 659795 = 989693) B989693
theorem B987491 : Blo 658307 987491 := bstep (se 1 (by rfl) ⟨740618, by rfl⟩ : syracuseStep 987491 = 1481237) B1481237
theorem B659811 : Blo 658307 659811 := bstep (se 1 (by rfl) ⟨494858, by rfl⟩ : syracuseStep 659811 = 989717) B989717
theorem B659827 : Blo 658307 659827 := bstep (se 1 (by rfl) ⟨494870, by rfl⟩ : syracuseStep 659827 = 989741) B989741
theorem B987521 : Blo 658307 987521 := bstep (se 2 (by rfl) ⟨370320, by rfl⟩ : syracuseStep 987521 = 740641) B740641
theorem B659843 : Blo 658307 659843 := bstep (se 1 (by rfl) ⟨494882, by rfl⟩ : syracuseStep 659843 = 989765) B989765
theorem B987539 : Blo 658307 987539 := bstep (se 1 (by rfl) ⟨740654, by rfl⟩ : syracuseStep 987539 = 1481309) B1481309
theorem B659859 : Blo 658307 659859 := bstep (se 1 (by rfl) ⟨494894, by rfl⟩ : syracuseStep 659859 = 989789) B989789
theorem B659875 : Blo 658307 659875 := bstep (se 1 (by rfl) ⟨494906, by rfl⟩ : syracuseStep 659875 = 989813) B989813
theorem B987569 : Blo 658307 987569 := bstep (se 2 (by rfl) ⟨370338, by rfl⟩ : syracuseStep 987569 = 740677) B740677
theorem B659891 : Blo 658307 659891 := bstep (se 1 (by rfl) ⟨494918, by rfl⟩ : syracuseStep 659891 = 989837) B989837
theorem B987587 : Blo 658307 987587 := bstep (se 1 (by rfl) ⟨740690, by rfl⟩ : syracuseStep 987587 = 1481381) B1481381
theorem B659907 : Blo 658307 659907 := bstep (se 1 (by rfl) ⟨494930, by rfl⟩ : syracuseStep 659907 = 989861) B989861
theorem B659923 : Blo 658307 659923 := bstep (se 1 (by rfl) ⟨494942, by rfl⟩ : syracuseStep 659923 = 989885) B989885
theorem B987617 : Blo 658307 987617 := bstep (se 2 (by rfl) ⟨370356, by rfl⟩ : syracuseStep 987617 = 740713) B740713
theorem B659939 : Blo 658307 659939 := bstep (se 1 (by rfl) ⟨494954, by rfl⟩ : syracuseStep 659939 = 989909) B989909
theorem B987635 : Blo 658307 987635 := bstep (se 1 (by rfl) ⟨740726, by rfl⟩ : syracuseStep 987635 = 1481453) B1481453
theorem B659955 : Blo 658307 659955 := bstep (se 1 (by rfl) ⟨494966, by rfl⟩ : syracuseStep 659955 = 989933) B989933
theorem B659971 : Blo 658307 659971 := bstep (se 1 (by rfl) ⟨494978, by rfl⟩ : syracuseStep 659971 = 989957) B989957
theorem B2232845 : Blo 658307 2232845 := bstep (se 3 (by rfl) ⟨418658, by rfl⟩ : syracuseStep 2232845 = 837317) B837317
theorem B987665 : Blo 658307 987665 := bstep (se 2 (by rfl) ⟨370374, by rfl⟩ : syracuseStep 987665 = 740749) B740749
theorem B659987 : Blo 658307 659987 := bstep (se 1 (by rfl) ⟨494990, by rfl⟩ : syracuseStep 659987 = 989981) B989981
theorem B14291477 : Blo 658307 14291477 := bstep (se 6 (by rfl) ⟨334956, by rfl⟩ : syracuseStep 14291477 = 669913) B669913
theorem B987683 : Blo 658307 987683 := bstep (se 1 (by rfl) ⟨740762, by rfl⟩ : syracuseStep 987683 = 1481525) B1481525
theorem B660003 : Blo 658307 660003 := bstep (se 1 (by rfl) ⟨495002, by rfl⟩ : syracuseStep 660003 = 990005) B990005
theorem B660019 : Blo 658307 660019 := bstep (se 1 (by rfl) ⟨495014, by rfl⟩ : syracuseStep 660019 = 990029) B990029
theorem B987713 : Blo 658307 987713 := bstep (se 2 (by rfl) ⟨370392, by rfl⟩ : syracuseStep 987713 = 740785) B740785
theorem B2232899 : Blo 658307 2232899 := bstep (se 1 (by rfl) ⟨1674674, by rfl⟩ : syracuseStep 2232899 = 3349349) B3349349
theorem B660035 : Blo 658307 660035 := bstep (se 1 (by rfl) ⟨495026, by rfl⟩ : syracuseStep 660035 = 990053) B990053
theorem B987731 : Blo 658307 987731 := bstep (se 1 (by rfl) ⟨740798, by rfl⟩ : syracuseStep 987731 = 1481597) B1481597
theorem B660051 : Blo 658307 660051 := bstep (se 1 (by rfl) ⟨495038, by rfl⟩ : syracuseStep 660051 = 990077) B990077
theorem B660067 : Blo 658307 660067 := bstep (se 1 (by rfl) ⟨495050, by rfl⟩ : syracuseStep 660067 = 990101) B990101
theorem B3576419 : Blo 658307 3576419 := bstep (se 1 (by rfl) ⟨2682314, by rfl⟩ : syracuseStep 3576419 = 5364629) B5364629
theorem B987761 : Blo 658307 987761 := bstep (se 2 (by rfl) ⟨370410, by rfl⟩ : syracuseStep 987761 = 740821) B740821
theorem B660083 : Blo 658307 660083 := bstep (se 1 (by rfl) ⟨495062, by rfl⟩ : syracuseStep 660083 = 990125) B990125
theorem B987779 : Blo 658307 987779 := bstep (se 1 (by rfl) ⟨740834, by rfl⟩ : syracuseStep 987779 = 1481669) B1481669
theorem B660099 : Blo 658307 660099 := bstep (se 1 (by rfl) ⟨495074, by rfl⟩ : syracuseStep 660099 = 990149) B990149
theorem B660115 : Blo 658307 660115 := bstep (se 1 (by rfl) ⟨495086, by rfl⟩ : syracuseStep 660115 = 990173) B990173
theorem B987809 : Blo 658307 987809 := bstep (se 2 (by rfl) ⟨370428, by rfl⟩ : syracuseStep 987809 = 740857) B740857
theorem B660131 : Blo 658307 660131 := bstep (se 1 (by rfl) ⟨495098, by rfl⟩ : syracuseStep 660131 = 990197) B990197
theorem B987827 : Blo 658307 987827 := bstep (se 1 (by rfl) ⟨740870, by rfl⟩ : syracuseStep 987827 = 1481741) B1481741
theorem B660147 : Blo 658307 660147 := bstep (se 1 (by rfl) ⟨495110, by rfl⟩ : syracuseStep 660147 = 990221) B990221
theorem B660163 : Blo 658307 660163 := bstep (se 1 (by rfl) ⟨495122, by rfl⟩ : syracuseStep 660163 = 990245) B990245
theorem B987857 : Blo 658307 987857 := bstep (se 2 (by rfl) ⟨370446, by rfl⟩ : syracuseStep 987857 = 740893) B740893
theorem B660179 : Blo 658307 660179 := bstep (se 1 (by rfl) ⟨495134, by rfl⟩ : syracuseStep 660179 = 990269) B990269
theorem B987875 : Blo 658307 987875 := bstep (se 1 (by rfl) ⟨740906, by rfl⟩ : syracuseStep 987875 = 1481813) B1481813
theorem B660195 : Blo 658307 660195 := bstep (se 1 (by rfl) ⟨495146, by rfl⟩ : syracuseStep 660195 = 990293) B990293
theorem B660211 : Blo 658307 660211 := bstep (se 1 (by rfl) ⟨495158, by rfl⟩ : syracuseStep 660211 = 990317) B990317
theorem B987905 : Blo 658307 987905 := bstep (se 2 (by rfl) ⟨370464, by rfl⟩ : syracuseStep 987905 = 740929) B740929
theorem B660227 : Blo 658307 660227 := bstep (se 1 (by rfl) ⟨495170, by rfl⟩ : syracuseStep 660227 = 990341) B990341
theorem B987923 : Blo 658307 987923 := bstep (se 1 (by rfl) ⟨740942, by rfl⟩ : syracuseStep 987923 = 1481885) B1481885
theorem B660243 : Blo 658307 660243 := bstep (se 1 (by rfl) ⟨495182, by rfl⟩ : syracuseStep 660243 = 990365) B990365
theorem B1250083 : Blo 658307 1250083 := bstep (se 1 (by rfl) ⟨937562, by rfl⟩ : syracuseStep 1250083 = 1875125) B1875125
theorem B660259 : Blo 658307 660259 := bstep (se 1 (by rfl) ⟨495194, by rfl⟩ : syracuseStep 660259 = 990389) B990389
theorem B987953 : Blo 658307 987953 := bstep (se 2 (by rfl) ⟨370482, by rfl⟩ : syracuseStep 987953 = 740965) B740965
theorem B660275 : Blo 658307 660275 := bstep (se 1 (by rfl) ⟨495206, by rfl⟩ : syracuseStep 660275 = 990413) B990413
theorem B987971 : Blo 658307 987971 := bstep (se 1 (by rfl) ⟨740978, by rfl⟩ : syracuseStep 987971 = 1481957) B1481957
theorem B660291 : Blo 658307 660291 := bstep (se 1 (by rfl) ⟨495218, by rfl⟩ : syracuseStep 660291 = 990437) B990437
theorem B1250129 : Blo 658307 1250129 := bstep (se 2 (by rfl) ⟨468798, by rfl⟩ : syracuseStep 1250129 = 937597) B937597
theorem B2233169 : Blo 658307 2233169 := bstep (se 2 (by rfl) ⟨837438, by rfl⟩ : syracuseStep 2233169 = 1674877) B1674877
theorem B660307 : Blo 658307 660307 := bstep (se 1 (by rfl) ⟨495230, by rfl⟩ : syracuseStep 660307 = 990461) B990461
theorem B988001 : Blo 658307 988001 := bstep (se 2 (by rfl) ⟨370500, by rfl⟩ : syracuseStep 988001 = 741001) B741001
theorem B660323 : Blo 658307 660323 := bstep (se 1 (by rfl) ⟨495242, by rfl⟩ : syracuseStep 660323 = 990485) B990485
theorem B988019 : Blo 658307 988019 := bstep (se 1 (by rfl) ⟨741014, by rfl⟩ : syracuseStep 988019 = 1482029) B1482029
theorem B660339 : Blo 658307 660339 := bstep (se 1 (by rfl) ⟨495254, by rfl⟩ : syracuseStep 660339 = 990509) B990509
theorem B660355 : Blo 658307 660355 := bstep (se 1 (by rfl) ⟨495266, by rfl⟩ : syracuseStep 660355 = 990533) B990533
theorem B988049 : Blo 658307 988049 := bstep (se 2 (by rfl) ⟨370518, by rfl⟩ : syracuseStep 988049 = 741037) B741037
theorem B660371 : Blo 658307 660371 := bstep (se 1 (by rfl) ⟨495278, by rfl⟩ : syracuseStep 660371 = 990557) B990557
theorem B988067 : Blo 658307 988067 := bstep (se 1 (by rfl) ⟨741050, by rfl⟩ : syracuseStep 988067 = 1482101) B1482101
theorem B660387 : Blo 658307 660387 := bstep (se 1 (by rfl) ⟨495290, by rfl⟩ : syracuseStep 660387 = 990581) B990581
theorem B660403 : Blo 658307 660403 := bstep (se 1 (by rfl) ⟨495302, by rfl⟩ : syracuseStep 660403 = 990605) B990605
theorem B988097 : Blo 658307 988097 := bstep (se 2 (by rfl) ⟨370536, by rfl⟩ : syracuseStep 988097 = 741073) B741073
theorem B660419 : Blo 658307 660419 := bstep (se 1 (by rfl) ⟨495314, by rfl⟩ : syracuseStep 660419 = 990629) B990629
theorem B3347405 : Blo 658307 3347405 := bstep (se 3 (by rfl) ⟨627638, by rfl⟩ : syracuseStep 3347405 = 1255277) B1255277
theorem B988115 : Blo 658307 988115 := bstep (se 1 (by rfl) ⟨741086, by rfl⟩ : syracuseStep 988115 = 1482173) B1482173
theorem B660435 : Blo 658307 660435 := bstep (se 1 (by rfl) ⟨495326, by rfl⟩ : syracuseStep 660435 = 990653) B990653
theorem B6329315 : Blo 658307 6329315 := bstep (se 1 (by rfl) ⟨4746986, by rfl⟩ : syracuseStep 6329315 = 9493973) B9493973
theorem B660451 : Blo 658307 660451 := bstep (se 1 (by rfl) ⟨495338, by rfl⟩ : syracuseStep 660451 = 990677) B990677
theorem B988145 : Blo 658307 988145 := bstep (se 2 (by rfl) ⟨370554, by rfl⟩ : syracuseStep 988145 = 741109) B741109
theorem B660467 : Blo 658307 660467 := bstep (se 1 (by rfl) ⟨495350, by rfl⟩ : syracuseStep 660467 = 990701) B990701
theorem B988163 : Blo 658307 988163 := bstep (se 1 (by rfl) ⟨741122, by rfl⟩ : syracuseStep 988163 = 1482245) B1482245
theorem B660483 : Blo 658307 660483 := bstep (se 1 (by rfl) ⟨495362, by rfl⟩ : syracuseStep 660483 = 990725) B990725
theorem B1905677 : Blo 658307 1905677 := bstep (se 3 (by rfl) ⟨357314, by rfl⟩ : syracuseStep 1905677 = 714629) B714629
theorem B660499 : Blo 658307 660499 := bstep (se 1 (by rfl) ⟨495374, by rfl⟩ : syracuseStep 660499 = 990749) B990749
theorem B988193 : Blo 658307 988193 := bstep (se 2 (by rfl) ⟨370572, by rfl⟩ : syracuseStep 988193 = 741145) B741145
theorem B660515 : Blo 658307 660515 := bstep (se 1 (by rfl) ⟨495386, by rfl⟩ : syracuseStep 660515 = 990773) B990773
theorem B988211 : Blo 658307 988211 := bstep (se 1 (by rfl) ⟨741158, by rfl⟩ : syracuseStep 988211 = 1482317) B1482317
theorem B660531 : Blo 658307 660531 := bstep (se 1 (by rfl) ⟨495398, by rfl⟩ : syracuseStep 660531 = 990797) B990797
theorem B660547 : Blo 658307 660547 := bstep (se 1 (by rfl) ⟨495410, by rfl⟩ : syracuseStep 660547 = 990821) B990821
theorem B988241 : Blo 658307 988241 := bstep (se 2 (by rfl) ⟨370590, by rfl⟩ : syracuseStep 988241 = 741181) B741181
theorem B660563 : Blo 658307 660563 := bstep (se 1 (by rfl) ⟨495422, by rfl⟩ : syracuseStep 660563 = 990845) B990845
theorem B988259 : Blo 658307 988259 := bstep (se 1 (by rfl) ⟨741194, by rfl⟩ : syracuseStep 988259 = 1482389) B1482389
theorem B660579 : Blo 658307 660579 := bstep (se 1 (by rfl) ⟨495434, by rfl⟩ : syracuseStep 660579 = 990869) B990869
theorem B1250417 : Blo 658307 1250417 := bstep (se 2 (by rfl) ⟨468906, by rfl⟩ : syracuseStep 1250417 = 937813) B937813
theorem B660595 : Blo 658307 660595 := bstep (se 1 (by rfl) ⟨495446, by rfl⟩ : syracuseStep 660595 = 990893) B990893
theorem B2823281 : Blo 658307 2823281 := bstep (se 2 (by rfl) ⟨1058730, by rfl⟩ : syracuseStep 2823281 = 2117461) B2117461
theorem B6362225 : Blo 658307 6362225 := bstep (se 2 (by rfl) ⟨2385834, by rfl⟩ : syracuseStep 6362225 = 4771669) B4771669
theorem B988289 : Blo 658307 988289 := bstep (se 2 (by rfl) ⟨370608, by rfl⟩ : syracuseStep 988289 = 741217) B741217
theorem B660611 : Blo 658307 660611 := bstep (se 1 (by rfl) ⟨495458, by rfl⟩ : syracuseStep 660611 = 990917) B990917
theorem B988307 : Blo 658307 988307 := bstep (se 1 (by rfl) ⟨741230, by rfl⟩ : syracuseStep 988307 = 1482461) B1482461
theorem B660627 : Blo 658307 660627 := bstep (se 1 (by rfl) ⟨495470, by rfl⟩ : syracuseStep 660627 = 990941) B990941
theorem B660643 : Blo 658307 660643 := bstep (se 1 (by rfl) ⟨495482, by rfl⟩ : syracuseStep 660643 = 990965) B990965
theorem B988337 : Blo 658307 988337 := bstep (se 2 (by rfl) ⟨370626, by rfl⟩ : syracuseStep 988337 = 741253) B741253
theorem B660659 : Blo 658307 660659 := bstep (se 1 (by rfl) ⟨495494, by rfl⟩ : syracuseStep 660659 = 990989) B990989
theorem B988355 : Blo 658307 988355 := bstep (se 1 (by rfl) ⟨741266, by rfl⟩ : syracuseStep 988355 = 1482533) B1482533
theorem B660675 : Blo 658307 660675 := bstep (se 1 (by rfl) ⟨495506, by rfl⟩ : syracuseStep 660675 = 991013) B991013
theorem B660691 : Blo 658307 660691 := bstep (se 1 (by rfl) ⟨495518, by rfl⟩ : syracuseStep 660691 = 991037) B991037
theorem B988385 : Blo 658307 988385 := bstep (se 2 (by rfl) ⟨370644, by rfl⟩ : syracuseStep 988385 = 741289) B741289
theorem B660707 : Blo 658307 660707 := bstep (se 1 (by rfl) ⟨495530, by rfl⟩ : syracuseStep 660707 = 991061) B991061
theorem B988403 : Blo 658307 988403 := bstep (se 1 (by rfl) ⟨741302, by rfl⟩ : syracuseStep 988403 = 1482605) B1482605
theorem B660723 : Blo 658307 660723 := bstep (se 1 (by rfl) ⟨495542, by rfl⟩ : syracuseStep 660723 = 991085) B991085
theorem B660739 : Blo 658307 660739 := bstep (se 1 (by rfl) ⟨495554, by rfl⟩ : syracuseStep 660739 = 991109) B991109
theorem B988433 : Blo 658307 988433 := bstep (se 2 (by rfl) ⟨370662, by rfl⟩ : syracuseStep 988433 = 741325) B741325
theorem B660755 : Blo 658307 660755 := bstep (se 1 (by rfl) ⟨495566, by rfl⟩ : syracuseStep 660755 = 991133) B991133
theorem B890147 : Blo 658307 890147 := bstep (se 1 (by rfl) ⟨667610, by rfl⟩ : syracuseStep 890147 = 1335221) B1335221
theorem B988451 : Blo 658307 988451 := bstep (se 1 (by rfl) ⟨741338, by rfl⟩ : syracuseStep 988451 = 1482677) B1482677
theorem B660771 : Blo 658307 660771 := bstep (se 1 (by rfl) ⟨495578, by rfl⟩ : syracuseStep 660771 = 991157) B991157
theorem B1414435 : Blo 658307 1414435 := bstep (se 1 (by rfl) ⟨1060826, by rfl⟩ : syracuseStep 1414435 = 2121653) B2121653
theorem B660787 : Blo 658307 660787 := bstep (se 1 (by rfl) ⟨495590, by rfl⟩ : syracuseStep 660787 = 991181) B991181
theorem B988481 : Blo 658307 988481 := bstep (se 2 (by rfl) ⟨370680, by rfl⟩ : syracuseStep 988481 = 741361) B741361
theorem B660803 : Blo 658307 660803 := bstep (se 1 (by rfl) ⟨495602, by rfl⟩ : syracuseStep 660803 = 991205) B991205
theorem B988499 : Blo 658307 988499 := bstep (se 1 (by rfl) ⟨741374, by rfl⟩ : syracuseStep 988499 = 1482749) B1482749
theorem B660819 : Blo 658307 660819 := bstep (se 1 (by rfl) ⟨495614, by rfl⟩ : syracuseStep 660819 = 991229) B991229
theorem B660835 : Blo 658307 660835 := bstep (se 1 (by rfl) ⟨495626, by rfl⟩ : syracuseStep 660835 = 991253) B991253
theorem B2233709 : Blo 658307 2233709 := bstep (se 3 (by rfl) ⟨418820, by rfl⟩ : syracuseStep 2233709 = 837641) B837641
theorem B988529 : Blo 658307 988529 := bstep (se 2 (by rfl) ⟨370698, by rfl⟩ : syracuseStep 988529 = 741397) B741397
theorem B660851 : Blo 658307 660851 := bstep (se 1 (by rfl) ⟨495638, by rfl⟩ : syracuseStep 660851 = 991277) B991277
theorem B988547 : Blo 658307 988547 := bstep (se 1 (by rfl) ⟨741410, by rfl⟩ : syracuseStep 988547 = 1482821) B1482821
theorem B660867 : Blo 658307 660867 := bstep (se 1 (by rfl) ⟨495650, by rfl⟩ : syracuseStep 660867 = 991301) B991301
theorem B955793 : Blo 658307 955793 := bstep (se 2 (by rfl) ⟨358422, by rfl⟩ : syracuseStep 955793 = 716845) B716845
theorem B660883 : Blo 658307 660883 := bstep (se 1 (by rfl) ⟨495662, by rfl⟩ : syracuseStep 660883 = 991325) B991325
theorem B988577 : Blo 658307 988577 := bstep (se 2 (by rfl) ⟨370716, by rfl⟩ : syracuseStep 988577 = 741433) B741433
theorem B660899 : Blo 658307 660899 := bstep (se 1 (by rfl) ⟨495674, by rfl⟩ : syracuseStep 660899 = 991349) B991349
theorem B2233763 : Blo 658307 2233763 := bstep (se 1 (by rfl) ⟨1675322, by rfl⟩ : syracuseStep 2233763 = 3350645) B3350645
theorem B988595 : Blo 658307 988595 := bstep (se 1 (by rfl) ⟨741446, by rfl⟩ : syracuseStep 988595 = 1482893) B1482893
theorem B660915 : Blo 658307 660915 := bstep (se 1 (by rfl) ⟨495686, by rfl⟩ : syracuseStep 660915 = 991373) B991373
theorem B660931 : Blo 658307 660931 := bstep (se 1 (by rfl) ⟨495698, by rfl⟩ : syracuseStep 660931 = 991397) B991397
theorem B988625 : Blo 658307 988625 := bstep (se 2 (by rfl) ⟨370734, by rfl⟩ : syracuseStep 988625 = 741469) B741469
theorem B660947 : Blo 658307 660947 := bstep (se 1 (by rfl) ⟨495710, by rfl⟩ : syracuseStep 660947 = 991421) B991421
theorem B988643 : Blo 658307 988643 := bstep (se 1 (by rfl) ⟨741482, by rfl⟩ : syracuseStep 988643 = 1482965) B1482965
theorem B660963 : Blo 658307 660963 := bstep (se 1 (by rfl) ⟨495722, by rfl⟩ : syracuseStep 660963 = 991445) B991445
theorem B660979 : Blo 658307 660979 := bstep (se 1 (by rfl) ⟨495734, by rfl⟩ : syracuseStep 660979 = 991469) B991469
theorem B988673 : Blo 658307 988673 := bstep (se 2 (by rfl) ⟨370752, by rfl⟩ : syracuseStep 988673 = 741505) B741505
theorem B660995 : Blo 658307 660995 := bstep (se 1 (by rfl) ⟨495746, by rfl⟩ : syracuseStep 660995 = 991493) B991493
theorem B988691 : Blo 658307 988691 := bstep (se 1 (by rfl) ⟨741518, by rfl⟩ : syracuseStep 988691 = 1483037) B1483037
theorem B661011 : Blo 658307 661011 := bstep (se 1 (by rfl) ⟨495758, by rfl⟩ : syracuseStep 661011 = 991517) B991517
theorem B661027 : Blo 658307 661027 := bstep (se 1 (by rfl) ⟨495770, by rfl⟩ : syracuseStep 661027 = 991541) B991541
theorem B988721 : Blo 658307 988721 := bstep (se 2 (by rfl) ⟨370770, by rfl⟩ : syracuseStep 988721 = 741541) B741541
theorem B661043 : Blo 658307 661043 := bstep (se 1 (by rfl) ⟨495782, by rfl⟩ : syracuseStep 661043 = 991565) B991565
theorem B988739 : Blo 658307 988739 := bstep (se 1 (by rfl) ⟨741554, by rfl⟩ : syracuseStep 988739 = 1483109) B1483109
theorem B661059 : Blo 658307 661059 := bstep (se 1 (by rfl) ⟨495794, by rfl⟩ : syracuseStep 661059 = 991589) B991589
theorem B661075 : Blo 658307 661075 := bstep (se 1 (by rfl) ⟨495806, by rfl⟩ : syracuseStep 661075 = 991613) B991613
theorem B988769 : Blo 658307 988769 := bstep (se 2 (by rfl) ⟨370788, by rfl⟩ : syracuseStep 988769 = 741577) B741577
theorem B661091 : Blo 658307 661091 := bstep (se 1 (by rfl) ⟨495818, by rfl⟩ : syracuseStep 661091 = 991637) B991637
theorem B988787 : Blo 658307 988787 := bstep (se 1 (by rfl) ⟨741590, by rfl⟩ : syracuseStep 988787 = 1483181) B1483181
theorem B661107 : Blo 658307 661107 := bstep (se 1 (by rfl) ⟨495830, by rfl⟩ : syracuseStep 661107 = 991661) B991661
theorem B661123 : Blo 658307 661123 := bstep (se 1 (by rfl) ⟨495842, by rfl⟩ : syracuseStep 661123 = 991685) B991685
theorem B988817 : Blo 658307 988817 := bstep (se 2 (by rfl) ⟨370806, by rfl⟩ : syracuseStep 988817 = 741613) B741613
theorem B661139 : Blo 658307 661139 := bstep (se 1 (by rfl) ⟨495854, by rfl⟩ : syracuseStep 661139 = 991709) B991709
theorem B988835 : Blo 658307 988835 := bstep (se 1 (by rfl) ⟨741626, by rfl⟩ : syracuseStep 988835 = 1483253) B1483253
theorem B661155 : Blo 658307 661155 := bstep (se 1 (by rfl) ⟨495866, by rfl⟩ : syracuseStep 661155 = 991733) B991733
theorem B2234033 : Blo 658307 2234033 := bstep (se 2 (by rfl) ⟨837762, by rfl⟩ : syracuseStep 2234033 = 1675525) B1675525
theorem B661171 : Blo 658307 661171 := bstep (se 1 (by rfl) ⟨495878, by rfl⟩ : syracuseStep 661171 = 991757) B991757
theorem B988865 : Blo 658307 988865 := bstep (se 2 (by rfl) ⟨370824, by rfl⟩ : syracuseStep 988865 = 741649) B741649
theorem B661187 : Blo 658307 661187 := bstep (se 1 (by rfl) ⟨495890, by rfl⟩ : syracuseStep 661187 = 991781) B991781
theorem B890579 : Blo 658307 890579 := bstep (se 1 (by rfl) ⟨667934, by rfl⟩ : syracuseStep 890579 = 1335869) B1335869
theorem B988883 : Blo 658307 988883 := bstep (se 1 (by rfl) ⟨741662, by rfl⟩ : syracuseStep 988883 = 1483325) B1483325
theorem B792275 : Blo 658307 792275 := bstep (se 1 (by rfl) ⟨594206, by rfl⟩ : syracuseStep 792275 = 1188413) B1188413
theorem B661203 : Blo 658307 661203 := bstep (se 1 (by rfl) ⟨495902, by rfl⟩ : syracuseStep 661203 = 991805) B991805
theorem B661219 : Blo 658307 661219 := bstep (se 1 (by rfl) ⟨495914, by rfl⟩ : syracuseStep 661219 = 991829) B991829
theorem B988913 : Blo 658307 988913 := bstep (se 2 (by rfl) ⟨370842, by rfl⟩ : syracuseStep 988913 = 741685) B741685
theorem B661235 : Blo 658307 661235 := bstep (se 1 (by rfl) ⟨495926, by rfl⟩ : syracuseStep 661235 = 991853) B991853
theorem B988931 : Blo 658307 988931 := bstep (se 1 (by rfl) ⟨741698, by rfl⟩ : syracuseStep 988931 = 1483397) B1483397
theorem B661251 : Blo 658307 661251 := bstep (se 1 (by rfl) ⟨495938, by rfl⟩ : syracuseStep 661251 = 991877) B991877
theorem B661267 : Blo 658307 661267 := bstep (se 1 (by rfl) ⟨495950, by rfl⟩ : syracuseStep 661267 = 991901) B991901
theorem B988961 : Blo 658307 988961 := bstep (se 2 (by rfl) ⟨370860, by rfl⟩ : syracuseStep 988961 = 741721) B741721
theorem B661283 : Blo 658307 661283 := bstep (se 1 (by rfl) ⟨495962, by rfl⟩ : syracuseStep 661283 = 991925) B991925
theorem B988979 : Blo 658307 988979 := bstep (se 1 (by rfl) ⟨741734, by rfl⟩ : syracuseStep 988979 = 1483469) B1483469
theorem B661299 : Blo 658307 661299 := bstep (se 1 (by rfl) ⟨495974, by rfl⟩ : syracuseStep 661299 = 991949) B991949
theorem B1251139 : Blo 658307 1251139 := bstep (se 1 (by rfl) ⟨938354, by rfl⟩ : syracuseStep 1251139 = 1876709) B1876709
theorem B661315 : Blo 658307 661315 := bstep (se 1 (by rfl) ⟨495986, by rfl⟩ : syracuseStep 661315 = 991973) B991973
theorem B989009 : Blo 658307 989009 := bstep (se 2 (by rfl) ⟨370878, by rfl⟩ : syracuseStep 989009 = 741757) B741757
theorem B661331 : Blo 658307 661331 := bstep (se 1 (by rfl) ⟨495998, by rfl⟩ : syracuseStep 661331 = 991997) B991997
theorem B989027 : Blo 658307 989027 := bstep (se 1 (by rfl) ⟨741770, by rfl⟩ : syracuseStep 989027 = 1483541) B1483541
theorem B661347 : Blo 658307 661347 := bstep (se 1 (by rfl) ⟨496010, by rfl⟩ : syracuseStep 661347 = 992021) B992021
theorem B661363 : Blo 658307 661363 := bstep (se 1 (by rfl) ⟨496022, by rfl⟩ : syracuseStep 661363 = 992045) B992045
theorem B989057 : Blo 658307 989057 := bstep (se 2 (by rfl) ⟨370896, by rfl⟩ : syracuseStep 989057 = 741793) B741793
theorem B661379 : Blo 658307 661379 := bstep (se 1 (by rfl) ⟨496034, by rfl⟩ : syracuseStep 661379 = 992069) B992069
theorem B989075 : Blo 658307 989075 := bstep (se 1 (by rfl) ⟨741806, by rfl⟩ : syracuseStep 989075 = 1483613) B1483613
theorem B661395 : Blo 658307 661395 := bstep (se 1 (by rfl) ⟨496046, by rfl⟩ : syracuseStep 661395 = 992093) B992093
theorem B661411 : Blo 658307 661411 := bstep (se 1 (by rfl) ⟨496058, by rfl⟩ : syracuseStep 661411 = 992117) B992117
theorem B989105 : Blo 658307 989105 := bstep (se 2 (by rfl) ⟨370914, by rfl⟩ : syracuseStep 989105 = 741829) B741829
theorem B661427 : Blo 658307 661427 := bstep (se 1 (by rfl) ⟨496070, by rfl⟩ : syracuseStep 661427 = 992141) B992141
theorem B989123 : Blo 658307 989123 := bstep (se 1 (by rfl) ⟨741842, by rfl⟩ : syracuseStep 989123 = 1483685) B1483685
theorem B661443 : Blo 658307 661443 := bstep (se 1 (by rfl) ⟨496082, by rfl⟩ : syracuseStep 661443 = 992165) B992165
theorem B661459 : Blo 658307 661459 := bstep (se 1 (by rfl) ⟨496094, by rfl⟩ : syracuseStep 661459 = 992189) B992189
theorem B989153 : Blo 658307 989153 := bstep (se 2 (by rfl) ⟨370932, by rfl⟩ : syracuseStep 989153 = 741865) B741865
theorem B661475 : Blo 658307 661475 := bstep (se 1 (by rfl) ⟨496106, by rfl⟩ : syracuseStep 661475 = 992213) B992213
theorem B989171 : Blo 658307 989171 := bstep (se 1 (by rfl) ⟨741878, by rfl⟩ : syracuseStep 989171 = 1483757) B1483757
theorem B661491 : Blo 658307 661491 := bstep (se 1 (by rfl) ⟨496118, by rfl⟩ : syracuseStep 661491 = 992237) B992237
theorem B661507 : Blo 658307 661507 := bstep (se 1 (by rfl) ⟨496130, by rfl⟩ : syracuseStep 661507 = 992261) B992261
theorem B989201 : Blo 658307 989201 := bstep (se 2 (by rfl) ⟨370950, by rfl⟩ : syracuseStep 989201 = 741901) B741901
theorem B661523 : Blo 658307 661523 := bstep (se 1 (by rfl) ⟨496142, by rfl⟩ : syracuseStep 661523 = 992285) B992285
theorem B989219 : Blo 658307 989219 := bstep (se 1 (by rfl) ⟨741914, by rfl⟩ : syracuseStep 989219 = 1483829) B1483829
theorem B661539 : Blo 658307 661539 := bstep (se 1 (by rfl) ⟨496154, by rfl⟩ : syracuseStep 661539 = 992309) B992309
theorem B661555 : Blo 658307 661555 := bstep (se 1 (by rfl) ⟨496166, by rfl⟩ : syracuseStep 661555 = 992333) B992333
theorem B989249 : Blo 658307 989249 := bstep (se 2 (by rfl) ⟨370968, by rfl⟩ : syracuseStep 989249 = 741937) B741937
theorem B661571 : Blo 658307 661571 := bstep (se 1 (by rfl) ⟨496178, by rfl⟩ : syracuseStep 661571 = 992357) B992357
theorem B2005069 : Blo 658307 2005069 := bstep (se 3 (by rfl) ⟨375950, by rfl⟩ : syracuseStep 2005069 = 751901) B751901
theorem B989267 : Blo 658307 989267 := bstep (se 1 (by rfl) ⟨741950, by rfl⟩ : syracuseStep 989267 = 1483901) B1483901
theorem B661587 : Blo 658307 661587 := bstep (se 1 (by rfl) ⟨496190, by rfl⟩ : syracuseStep 661587 = 992381) B992381
theorem B661603 : Blo 658307 661603 := bstep (se 1 (by rfl) ⟨496202, by rfl⟩ : syracuseStep 661603 = 992405) B992405
theorem B989297 : Blo 658307 989297 := bstep (se 2 (by rfl) ⟨370986, by rfl⟩ : syracuseStep 989297 = 741973) B741973
theorem B661619 : Blo 658307 661619 := bstep (se 1 (by rfl) ⟨496214, by rfl⟩ : syracuseStep 661619 = 992429) B992429
theorem B989315 : Blo 658307 989315 := bstep (se 1 (by rfl) ⟨741986, by rfl⟩ : syracuseStep 989315 = 1483973) B1483973
theorem B661635 : Blo 658307 661635 := bstep (se 1 (by rfl) ⟨496226, by rfl⟩ : syracuseStep 661635 = 992453) B992453
theorem B7510157 : Blo 658307 7510157 := bstep (se 3 (by rfl) ⟨1408154, by rfl⟩ : syracuseStep 7510157 = 2816309) B2816309
theorem B661651 : Blo 658307 661651 := bstep (se 1 (by rfl) ⟨496238, by rfl⟩ : syracuseStep 661651 = 992477) B992477
theorem B989345 : Blo 658307 989345 := bstep (se 2 (by rfl) ⟨371004, by rfl⟩ : syracuseStep 989345 = 742009) B742009
theorem B661667 : Blo 658307 661667 := bstep (se 1 (by rfl) ⟨496250, by rfl⟩ : syracuseStep 661667 = 992501) B992501
theorem B989363 : Blo 658307 989363 := bstep (se 1 (by rfl) ⟨742022, by rfl⟩ : syracuseStep 989363 = 1484045) B1484045
theorem B661683 : Blo 658307 661683 := bstep (se 1 (by rfl) ⟨496262, by rfl⟩ : syracuseStep 661683 = 992525) B992525
theorem B661699 : Blo 658307 661699 := bstep (se 1 (by rfl) ⟨496274, by rfl⟩ : syracuseStep 661699 = 992549) B992549
theorem B2234573 : Blo 658307 2234573 := bstep (se 3 (by rfl) ⟨418982, by rfl⟩ : syracuseStep 2234573 = 837965) B837965
theorem B989393 : Blo 658307 989393 := bstep (se 2 (by rfl) ⟨371022, by rfl⟩ : syracuseStep 989393 = 742045) B742045
theorem B661715 : Blo 658307 661715 := bstep (se 1 (by rfl) ⟨496286, by rfl⟩ : syracuseStep 661715 = 992573) B992573
theorem B989411 : Blo 658307 989411 := bstep (se 1 (by rfl) ⟨742058, by rfl⟩ : syracuseStep 989411 = 1484117) B1484117
theorem B661731 : Blo 658307 661731 := bstep (se 1 (by rfl) ⟨496298, by rfl⟩ : syracuseStep 661731 = 992597) B992597
theorem B661747 : Blo 658307 661747 := bstep (se 1 (by rfl) ⟨496310, by rfl⟩ : syracuseStep 661747 = 992621) B992621
theorem B989441 : Blo 658307 989441 := bstep (se 2 (by rfl) ⟨371040, by rfl⟩ : syracuseStep 989441 = 742081) B742081
theorem B1251587 : Blo 658307 1251587 := bstep (se 1 (by rfl) ⟨938690, by rfl⟩ : syracuseStep 1251587 = 1877381) B1877381
theorem B661763 : Blo 658307 661763 := bstep (se 1 (by rfl) ⟨496322, by rfl⟩ : syracuseStep 661763 = 992645) B992645
theorem B2234627 : Blo 658307 2234627 := bstep (se 1 (by rfl) ⟨1675970, by rfl⟩ : syracuseStep 2234627 = 3351941) B3351941
theorem B4233485 : Blo 658307 4233485 := bstep (se 3 (by rfl) ⟨793778, by rfl⟩ : syracuseStep 4233485 = 1587557) B1587557
theorem B989459 : Blo 658307 989459 := bstep (se 1 (by rfl) ⟨742094, by rfl⟩ : syracuseStep 989459 = 1484189) B1484189
theorem B661779 : Blo 658307 661779 := bstep (se 1 (by rfl) ⟨496334, by rfl⟩ : syracuseStep 661779 = 992669) B992669
theorem B661795 : Blo 658307 661795 := bstep (se 1 (by rfl) ⟨496346, by rfl⟩ : syracuseStep 661795 = 992693) B992693
theorem B989489 : Blo 658307 989489 := bstep (se 2 (by rfl) ⟨371058, by rfl⟩ : syracuseStep 989489 = 742117) B742117
theorem B661811 : Blo 658307 661811 := bstep (se 1 (by rfl) ⟨496358, by rfl⟩ : syracuseStep 661811 = 992717) B992717
theorem B989507 : Blo 658307 989507 := bstep (se 1 (by rfl) ⟨742130, by rfl⟩ : syracuseStep 989507 = 1484261) B1484261
theorem B661827 : Blo 658307 661827 := bstep (se 1 (by rfl) ⟨496370, by rfl⟩ : syracuseStep 661827 = 992741) B992741
theorem B661843 : Blo 658307 661843 := bstep (se 1 (by rfl) ⟨496382, by rfl⟩ : syracuseStep 661843 = 992765) B992765
theorem B989537 : Blo 658307 989537 := bstep (se 2 (by rfl) ⟨371076, by rfl⟩ : syracuseStep 989537 = 742153) B742153
theorem B661859 : Blo 658307 661859 := bstep (se 1 (by rfl) ⟨496394, by rfl⟩ : syracuseStep 661859 = 992789) B992789
theorem B989555 : Blo 658307 989555 := bstep (se 1 (by rfl) ⟨742166, by rfl⟩ : syracuseStep 989555 = 1484333) B1484333
theorem B661875 : Blo 658307 661875 := bstep (se 1 (by rfl) ⟨496406, by rfl⟩ : syracuseStep 661875 = 992813) B992813
theorem B661891 : Blo 658307 661891 := bstep (se 1 (by rfl) ⟨496418, by rfl⟩ : syracuseStep 661891 = 992837) B992837
theorem B989585 : Blo 658307 989585 := bstep (se 2 (by rfl) ⟨371094, by rfl⟩ : syracuseStep 989585 = 742189) B742189
theorem B661907 : Blo 658307 661907 := bstep (se 1 (by rfl) ⟨496430, by rfl⟩ : syracuseStep 661907 = 992861) B992861
theorem B989603 : Blo 658307 989603 := bstep (se 1 (by rfl) ⟨742202, by rfl⟩ : syracuseStep 989603 = 1484405) B1484405
theorem B661923 : Blo 658307 661923 := bstep (se 1 (by rfl) ⟨496442, by rfl⟩ : syracuseStep 661923 = 992885) B992885
theorem B661939 : Blo 658307 661939 := bstep (se 1 (by rfl) ⟨496454, by rfl⟩ : syracuseStep 661939 = 992909) B992909
theorem B989633 : Blo 658307 989633 := bstep (se 2 (by rfl) ⟨371112, by rfl⟩ : syracuseStep 989633 = 742225) B742225
theorem B661955 : Blo 658307 661955 := bstep (se 1 (by rfl) ⟨496466, by rfl⟩ : syracuseStep 661955 = 992933) B992933
theorem B989651 : Blo 658307 989651 := bstep (se 1 (by rfl) ⟨742238, by rfl⟩ : syracuseStep 989651 = 1484477) B1484477
theorem B661971 : Blo 658307 661971 := bstep (se 1 (by rfl) ⟨496478, by rfl⟩ : syracuseStep 661971 = 992957) B992957
theorem B661987 : Blo 658307 661987 := bstep (se 1 (by rfl) ⟨496490, by rfl⟩ : syracuseStep 661987 = 992981) B992981
theorem B1481201 : Blo 658307 1481201 := bstep (se 2 (by rfl) ⟨555450, by rfl⟩ : syracuseStep 1481201 = 1110901) B1110901
theorem B989681 : Blo 658307 989681 := bstep (se 2 (by rfl) ⟨371130, by rfl⟩ : syracuseStep 989681 = 742261) B742261
theorem B662003 : Blo 658307 662003 := bstep (se 1 (by rfl) ⟨496502, by rfl⟩ : syracuseStep 662003 = 993005) B993005
theorem B1481219 : Blo 658307 1481219 := bstep (se 1 (by rfl) ⟨1110914, by rfl⟩ : syracuseStep 1481219 = 2221829) B2221829
theorem B989699 : Blo 658307 989699 := bstep (se 1 (by rfl) ⟨742274, by rfl⟩ : syracuseStep 989699 = 1484549) B1484549
theorem B662019 : Blo 658307 662019 := bstep (se 1 (by rfl) ⟨496514, by rfl⟩ : syracuseStep 662019 = 993029) B993029
theorem B2234897 : Blo 658307 2234897 := bstep (se 2 (by rfl) ⟨838086, by rfl⟩ : syracuseStep 2234897 = 1676173) B1676173
theorem B662035 : Blo 658307 662035 := bstep (se 1 (by rfl) ⟨496526, by rfl⟩ : syracuseStep 662035 = 993053) B993053
theorem B989729 : Blo 658307 989729 := bstep (se 2 (by rfl) ⟨371148, by rfl⟩ : syracuseStep 989729 = 742297) B742297
theorem B1251875 : Blo 658307 1251875 := bstep (se 1 (by rfl) ⟨938906, by rfl⟩ : syracuseStep 1251875 = 1877813) B1877813
theorem B662051 : Blo 658307 662051 := bstep (se 1 (by rfl) ⟨496538, by rfl⟩ : syracuseStep 662051 = 993077) B993077
theorem B989747 : Blo 658307 989747 := bstep (se 1 (by rfl) ⟨742310, by rfl⟩ : syracuseStep 989747 = 1484621) B1484621
theorem B662067 : Blo 658307 662067 := bstep (se 1 (by rfl) ⟨496550, by rfl⟩ : syracuseStep 662067 = 993101) B993101
theorem B662083 : Blo 658307 662083 := bstep (se 1 (by rfl) ⟨496562, by rfl⟩ : syracuseStep 662083 = 993125) B993125
theorem B4528709 : Blo 658307 4528709 := bstep (se 4 (by rfl) ⟨424566, by rfl⟩ : syracuseStep 4528709 = 849133) B849133
theorem B989777 : Blo 658307 989777 := bstep (se 2 (by rfl) ⟨371166, by rfl⟩ : syracuseStep 989777 = 742333) B742333
theorem B662099 : Blo 658307 662099 := bstep (se 1 (by rfl) ⟨496574, by rfl⟩ : syracuseStep 662099 = 993149) B993149
theorem B989795 : Blo 658307 989795 := bstep (se 1 (by rfl) ⟨742346, by rfl⟩ : syracuseStep 989795 = 1484693) B1484693
theorem B662115 : Blo 658307 662115 := bstep (se 1 (by rfl) ⟨496586, by rfl⟩ : syracuseStep 662115 = 993173) B993173
theorem B662131 : Blo 658307 662131 := bstep (se 1 (by rfl) ⟨496598, by rfl⟩ : syracuseStep 662131 = 993197) B993197
theorem B989825 : Blo 658307 989825 := bstep (se 2 (by rfl) ⟨371184, by rfl⟩ : syracuseStep 989825 = 742369) B742369
theorem B662147 : Blo 658307 662147 := bstep (se 1 (by rfl) ⟨496610, by rfl⟩ : syracuseStep 662147 = 993221) B993221
theorem B989843 : Blo 658307 989843 := bstep (se 1 (by rfl) ⟨742382, by rfl⟩ : syracuseStep 989843 = 1484765) B1484765
theorem B662163 : Blo 658307 662163 := bstep (se 1 (by rfl) ⟨496622, by rfl⟩ : syracuseStep 662163 = 993245) B993245
theorem B662179 : Blo 658307 662179 := bstep (se 1 (by rfl) ⟨496634, by rfl⟩ : syracuseStep 662179 = 993269) B993269
theorem B989873 : Blo 658307 989873 := bstep (se 2 (by rfl) ⟨371202, by rfl⟩ : syracuseStep 989873 = 742405) B742405
theorem B662195 : Blo 658307 662195 := bstep (se 1 (by rfl) ⟨496646, by rfl⟩ : syracuseStep 662195 = 993293) B993293
theorem B1055425 : Blo 658307 1055425 := bstep (se 2 (by rfl) ⟨395784, by rfl⟩ : syracuseStep 1055425 = 791569) B791569
theorem B989891 : Blo 658307 989891 := bstep (se 1 (by rfl) ⟨742418, by rfl⟩ : syracuseStep 989891 = 1484837) B1484837
theorem B662211 : Blo 658307 662211 := bstep (se 1 (by rfl) ⟨496658, by rfl⟩ : syracuseStep 662211 = 993317) B993317
theorem B662227 : Blo 658307 662227 := bstep (se 1 (by rfl) ⟨496670, by rfl⟩ : syracuseStep 662227 = 993341) B993341
theorem B989921 : Blo 658307 989921 := bstep (se 2 (by rfl) ⟨371220, by rfl⟩ : syracuseStep 989921 = 742441) B742441
theorem B662243 : Blo 658307 662243 := bstep (se 1 (by rfl) ⟨496682, by rfl⟩ : syracuseStep 662243 = 993365) B993365
theorem B989939 : Blo 658307 989939 := bstep (se 1 (by rfl) ⟨742454, by rfl⟩ : syracuseStep 989939 = 1484909) B1484909
theorem B662259 : Blo 658307 662259 := bstep (se 1 (by rfl) ⟨496694, by rfl⟩ : syracuseStep 662259 = 993389) B993389
theorem B662275 : Blo 658307 662275 := bstep (se 1 (by rfl) ⟨496706, by rfl⟩ : syracuseStep 662275 = 993413) B993413
theorem B1481489 : Blo 658307 1481489 := bstep (se 2 (by rfl) ⟨555558, by rfl⟩ : syracuseStep 1481489 = 1111117) B1111117
theorem B989969 : Blo 658307 989969 := bstep (se 2 (by rfl) ⟨371238, by rfl⟩ : syracuseStep 989969 = 742477) B742477
theorem B662291 : Blo 658307 662291 := bstep (se 1 (by rfl) ⟨496718, by rfl⟩ : syracuseStep 662291 = 993437) B993437
theorem B1481507 : Blo 658307 1481507 := bstep (se 1 (by rfl) ⟨1111130, by rfl⟩ : syracuseStep 1481507 = 2222261) B2222261
theorem B989987 : Blo 658307 989987 := bstep (se 1 (by rfl) ⟨742490, by rfl⟩ : syracuseStep 989987 = 1484981) B1484981
theorem B662307 : Blo 658307 662307 := bstep (se 1 (by rfl) ⟨496730, by rfl⟩ : syracuseStep 662307 = 993461) B993461
theorem B990017 : Blo 658307 990017 := bstep (se 2 (by rfl) ⟨371256, by rfl⟩ : syracuseStep 990017 = 742513) B742513
theorem B990035 : Blo 658307 990035 := bstep (se 1 (by rfl) ⟨742526, by rfl⟩ : syracuseStep 990035 = 1485053) B1485053
theorem B990065 : Blo 658307 990065 := bstep (se 2 (by rfl) ⟨371274, by rfl⟩ : syracuseStep 990065 = 742549) B742549
theorem B990083 : Blo 658307 990083 := bstep (se 1 (by rfl) ⟨742562, by rfl⟩ : syracuseStep 990083 = 1485125) B1485125
theorem B990113 : Blo 658307 990113 := bstep (se 2 (by rfl) ⟨371292, by rfl⟩ : syracuseStep 990113 = 742585) B742585
theorem B990131 : Blo 658307 990131 := bstep (se 1 (by rfl) ⟨742598, by rfl⟩ : syracuseStep 990131 = 1485197) B1485197
theorem B1055681 : Blo 658307 1055681 := bstep (se 2 (by rfl) ⟨395880, by rfl⟩ : syracuseStep 1055681 = 791761) B791761
theorem B1874897 : Blo 658307 1874897 := bstep (se 2 (by rfl) ⟨703086, by rfl⟩ : syracuseStep 1874897 = 1406173) B1406173
theorem B990161 : Blo 658307 990161 := bstep (se 2 (by rfl) ⟨371310, by rfl⟩ : syracuseStep 990161 = 742621) B742621
theorem B990179 : Blo 658307 990179 := bstep (se 1 (by rfl) ⟨742634, by rfl⟩ : syracuseStep 990179 = 1485269) B1485269
theorem B990209 : Blo 658307 990209 := bstep (se 2 (by rfl) ⟨371328, by rfl⟩ : syracuseStep 990209 = 742657) B742657
theorem B990227 : Blo 658307 990227 := bstep (se 1 (by rfl) ⟨742670, by rfl⟩ : syracuseStep 990227 = 1485341) B1485341
theorem B1481777 : Blo 658307 1481777 := bstep (se 2 (by rfl) ⟨555666, by rfl⟩ : syracuseStep 1481777 = 1111333) B1111333
theorem B990257 : Blo 658307 990257 := bstep (se 2 (by rfl) ⟨371346, by rfl⟩ : syracuseStep 990257 = 742693) B742693
theorem B1481795 : Blo 658307 1481795 := bstep (se 1 (by rfl) ⟨1111346, by rfl⟩ : syracuseStep 1481795 = 2222693) B2222693
theorem B990275 : Blo 658307 990275 := bstep (se 1 (by rfl) ⟨742706, by rfl⟩ : syracuseStep 990275 = 1485413) B1485413
theorem B990305 : Blo 658307 990305 := bstep (se 2 (by rfl) ⟨371364, by rfl⟩ : syracuseStep 990305 = 742729) B742729
theorem B2006129 : Blo 658307 2006129 := bstep (se 2 (by rfl) ⟨752298, by rfl⟩ : syracuseStep 2006129 = 1504597) B1504597
theorem B990323 : Blo 658307 990323 := bstep (se 1 (by rfl) ⟨742742, by rfl⟩ : syracuseStep 990323 = 1485485) B1485485
theorem B1055873 : Blo 658307 1055873 := bstep (se 2 (by rfl) ⟨395952, by rfl⟩ : syracuseStep 1055873 = 791905) B791905
theorem B990353 : Blo 658307 990353 := bstep (se 2 (by rfl) ⟨371382, by rfl⟩ : syracuseStep 990353 = 742765) B742765
theorem B990371 : Blo 658307 990371 := bstep (se 1 (by rfl) ⟨742778, by rfl⟩ : syracuseStep 990371 = 1485557) B1485557
theorem B990401 : Blo 658307 990401 := bstep (se 2 (by rfl) ⟨371400, by rfl⟩ : syracuseStep 990401 = 742801) B742801
theorem B990419 : Blo 658307 990419 := bstep (se 1 (by rfl) ⟨742814, by rfl⟩ : syracuseStep 990419 = 1485629) B1485629
theorem B990449 : Blo 658307 990449 := bstep (se 2 (by rfl) ⟨371418, by rfl⟩ : syracuseStep 990449 = 742837) B742837
theorem B990467 : Blo 658307 990467 := bstep (se 1 (by rfl) ⟨742850, by rfl⟩ : syracuseStep 990467 = 1485701) B1485701
theorem B990497 : Blo 658307 990497 := bstep (se 2 (by rfl) ⟨371436, by rfl⟩ : syracuseStep 990497 = 742873) B742873
theorem B990515 : Blo 658307 990515 := bstep (se 1 (by rfl) ⟨742886, by rfl⟩ : syracuseStep 990515 = 1485773) B1485773
theorem B1482065 : Blo 658307 1482065 := bstep (se 2 (by rfl) ⟨555774, by rfl⟩ : syracuseStep 1482065 = 1111549) B1111549
theorem B990545 : Blo 658307 990545 := bstep (se 2 (by rfl) ⟨371454, by rfl⟩ : syracuseStep 990545 = 742909) B742909
theorem B1482083 : Blo 658307 1482083 := bstep (se 1 (by rfl) ⟨1111562, by rfl⟩ : syracuseStep 1482083 = 2223125) B2223125
theorem B990563 : Blo 658307 990563 := bstep (se 1 (by rfl) ⟨742922, by rfl⟩ : syracuseStep 990563 = 1485845) B1485845
theorem B990593 : Blo 658307 990593 := bstep (se 2 (by rfl) ⟨371472, by rfl⟩ : syracuseStep 990593 = 742945) B742945
theorem B990611 : Blo 658307 990611 := bstep (se 1 (by rfl) ⟨742958, by rfl⟩ : syracuseStep 990611 = 1485917) B1485917
theorem B990641 : Blo 658307 990641 := bstep (se 2 (by rfl) ⟨371490, by rfl⟩ : syracuseStep 990641 = 742981) B742981
theorem B990659 : Blo 658307 990659 := bstep (se 1 (by rfl) ⟨742994, by rfl⟩ : syracuseStep 990659 = 1485989) B1485989
theorem B1252817 : Blo 658307 1252817 := bstep (se 2 (by rfl) ⟨469806, by rfl⟩ : syracuseStep 1252817 = 939613) B939613
theorem B990689 : Blo 658307 990689 := bstep (se 2 (by rfl) ⟨371508, by rfl⟩ : syracuseStep 990689 = 743017) B743017
theorem B990707 : Blo 658307 990707 := bstep (se 1 (by rfl) ⟨743030, by rfl⟩ : syracuseStep 990707 = 1486061) B1486061
theorem B2825741 : Blo 658307 2825741 := bstep (se 3 (by rfl) ⟨529826, by rfl⟩ : syracuseStep 2825741 = 1059653) B1059653
theorem B990737 : Blo 658307 990737 := bstep (se 2 (by rfl) ⟨371526, by rfl⟩ : syracuseStep 990737 = 743053) B743053
theorem B990755 : Blo 658307 990755 := bstep (se 1 (by rfl) ⟨743066, by rfl⟩ : syracuseStep 990755 = 1486133) B1486133
theorem B990785 : Blo 658307 990785 := bstep (se 2 (by rfl) ⟨371544, by rfl⟩ : syracuseStep 990785 = 743089) B743089
theorem B7118405 : Blo 658307 7118405 := bstep (se 4 (by rfl) ⟨667350, by rfl⟩ : syracuseStep 7118405 = 1334701) B1334701
theorem B4005445 : Blo 658307 4005445 := bstep (se 4 (by rfl) ⟨375510, by rfl⟩ : syracuseStep 4005445 = 751021) B751021
theorem B990803 : Blo 658307 990803 := bstep (se 1 (by rfl) ⟨743102, by rfl⟩ : syracuseStep 990803 = 1486205) B1486205
theorem B1482353 : Blo 658307 1482353 := bstep (se 2 (by rfl) ⟨555882, by rfl⟩ : syracuseStep 1482353 = 1111765) B1111765
theorem B990833 : Blo 658307 990833 := bstep (se 2 (by rfl) ⟨371562, by rfl⟩ : syracuseStep 990833 = 743125) B743125
theorem B1482371 : Blo 658307 1482371 := bstep (se 1 (by rfl) ⟨1111778, by rfl⟩ : syracuseStep 1482371 = 2223557) B2223557
theorem B990851 : Blo 658307 990851 := bstep (se 1 (by rfl) ⟨743138, by rfl⟩ : syracuseStep 990851 = 1486277) B1486277
theorem B990881 : Blo 658307 990881 := bstep (se 2 (by rfl) ⟨371580, by rfl⟩ : syracuseStep 990881 = 743161) B743161
theorem B990899 : Blo 658307 990899 := bstep (se 1 (by rfl) ⟨743174, by rfl⟩ : syracuseStep 990899 = 1486349) B1486349
theorem B990929 : Blo 658307 990929 := bstep (se 2 (by rfl) ⟨371598, by rfl⟩ : syracuseStep 990929 = 743197) B743197
theorem B990947 : Blo 658307 990947 := bstep (se 1 (by rfl) ⟨743210, by rfl⟩ : syracuseStep 990947 = 1486421) B1486421
theorem B990977 : Blo 658307 990977 := bstep (se 2 (by rfl) ⟨371616, by rfl⟩ : syracuseStep 990977 = 743233) B743233
theorem B2039555 : Blo 658307 2039555 := bstep (se 1 (by rfl) ⟨1529666, by rfl⟩ : syracuseStep 2039555 = 3059333) B3059333
theorem B990995 : Blo 658307 990995 := bstep (se 1 (by rfl) ⟨743246, by rfl⟩ : syracuseStep 990995 = 1486493) B1486493
theorem B892721 : Blo 658307 892721 := bstep (se 2 (by rfl) ⟨334770, by rfl⟩ : syracuseStep 892721 = 669541) B669541
theorem B991025 : Blo 658307 991025 := bstep (se 2 (by rfl) ⟨371634, by rfl⟩ : syracuseStep 991025 = 743269) B743269
theorem B3350321 : Blo 658307 3350321 := bstep (se 2 (by rfl) ⟨1256370, by rfl⟩ : syracuseStep 3350321 = 2512741) B2512741
theorem B991043 : Blo 658307 991043 := bstep (se 1 (by rfl) ⟨743282, by rfl⟩ : syracuseStep 991043 = 1486565) B1486565
theorem B991073 : Blo 658307 991073 := bstep (se 2 (by rfl) ⟨371652, by rfl⟩ : syracuseStep 991073 = 743305) B743305
theorem B2826083 : Blo 658307 2826083 := bstep (se 1 (by rfl) ⟨2119562, by rfl⟩ : syracuseStep 2826083 = 4239125) B4239125
theorem B991091 : Blo 658307 991091 := bstep (se 1 (by rfl) ⟨743318, by rfl⟩ : syracuseStep 991091 = 1486637) B1486637
theorem B1482641 : Blo 658307 1482641 := bstep (se 2 (by rfl) ⟨555990, by rfl⟩ : syracuseStep 1482641 = 1111981) B1111981
theorem B991121 : Blo 658307 991121 := bstep (se 2 (by rfl) ⟨371670, by rfl⟩ : syracuseStep 991121 = 743341) B743341
theorem B1482659 : Blo 658307 1482659 := bstep (se 1 (by rfl) ⟨1111994, by rfl⟩ : syracuseStep 1482659 = 2223989) B2223989
theorem B991139 : Blo 658307 991139 := bstep (se 1 (by rfl) ⟨743354, by rfl⟩ : syracuseStep 991139 = 1486709) B1486709
theorem B991169 : Blo 658307 991169 := bstep (se 2 (by rfl) ⟨371688, by rfl⟩ : syracuseStep 991169 = 743377) B743377
theorem B892883 : Blo 658307 892883 := bstep (se 1 (by rfl) ⟨669662, by rfl⟩ : syracuseStep 892883 = 1339325) B1339325
theorem B991187 : Blo 658307 991187 := bstep (se 1 (by rfl) ⟨743390, by rfl⟩ : syracuseStep 991187 = 1486781) B1486781
theorem B991217 : Blo 658307 991217 := bstep (se 2 (by rfl) ⟨371706, by rfl⟩ : syracuseStep 991217 = 743413) B743413
theorem B9052145 : Blo 658307 9052145 := bstep (se 2 (by rfl) ⟨3394554, by rfl⟩ : syracuseStep 9052145 = 6789109) B6789109
theorem B991235 : Blo 658307 991235 := bstep (se 1 (by rfl) ⟨743426, by rfl⟩ : syracuseStep 991235 = 1486853) B1486853
theorem B991265 : Blo 658307 991265 := bstep (se 2 (by rfl) ⟨371724, by rfl⟩ : syracuseStep 991265 = 743449) B743449
theorem B991283 : Blo 658307 991283 := bstep (se 1 (by rfl) ⟨743462, by rfl⟩ : syracuseStep 991283 = 1486925) B1486925
theorem B991313 : Blo 658307 991313 := bstep (se 2 (by rfl) ⟨371742, by rfl⟩ : syracuseStep 991313 = 743485) B743485
theorem B991331 : Blo 658307 991331 := bstep (se 1 (by rfl) ⟨743498, by rfl⟩ : syracuseStep 991331 = 1486997) B1486997
theorem B991361 : Blo 658307 991361 := bstep (se 2 (by rfl) ⟨371760, by rfl⟩ : syracuseStep 991361 = 743521) B743521
theorem B5021837 : Blo 658307 5021837 := bstep (se 3 (by rfl) ⟨941594, by rfl⟩ : syracuseStep 5021837 = 1883189) B1883189
theorem B991379 : Blo 658307 991379 := bstep (se 1 (by rfl) ⟨743534, by rfl⟩ : syracuseStep 991379 = 1487069) B1487069
theorem B1482929 : Blo 658307 1482929 := bstep (se 2 (by rfl) ⟨556098, by rfl⟩ : syracuseStep 1482929 = 1112197) B1112197
theorem B991409 : Blo 658307 991409 := bstep (se 2 (by rfl) ⟨371778, by rfl⟩ : syracuseStep 991409 = 743557) B743557
theorem B1482947 : Blo 658307 1482947 := bstep (se 1 (by rfl) ⟨1112210, by rfl⟩ : syracuseStep 1482947 = 2224421) B2224421
theorem B991427 : Blo 658307 991427 := bstep (se 1 (by rfl) ⟨743570, by rfl⟩ : syracuseStep 991427 = 1487141) B1487141
theorem B991457 : Blo 658307 991457 := bstep (se 2 (by rfl) ⟨371796, by rfl⟩ : syracuseStep 991457 = 743593) B743593
theorem B991475 : Blo 658307 991475 := bstep (se 1 (by rfl) ⟨743606, by rfl⟩ : syracuseStep 991475 = 1487213) B1487213
theorem B991505 : Blo 658307 991505 := bstep (se 2 (by rfl) ⟨371814, by rfl⟩ : syracuseStep 991505 = 743629) B743629
theorem B991523 : Blo 658307 991523 := bstep (se 1 (by rfl) ⟨743642, by rfl⟩ : syracuseStep 991523 = 1487285) B1487285
theorem B991553 : Blo 658307 991553 := bstep (se 2 (by rfl) ⟨371832, by rfl⟩ : syracuseStep 991553 = 743665) B743665
theorem B1253713 : Blo 658307 1253713 := bstep (se 2 (by rfl) ⟨470142, by rfl⟩ : syracuseStep 1253713 = 940285) B940285
theorem B991571 : Blo 658307 991571 := bstep (se 1 (by rfl) ⟨743678, by rfl⟩ : syracuseStep 991571 = 1487357) B1487357
theorem B991601 : Blo 658307 991601 := bstep (se 2 (by rfl) ⟨371850, by rfl⟩ : syracuseStep 991601 = 743701) B743701
theorem B1876355 : Blo 658307 1876355 := bstep (se 1 (by rfl) ⟨1407266, by rfl⟩ : syracuseStep 1876355 = 2814533) B2814533
theorem B991619 : Blo 658307 991619 := bstep (se 1 (by rfl) ⟨743714, by rfl⟩ : syracuseStep 991619 = 1487429) B1487429
theorem B991649 : Blo 658307 991649 := bstep (se 2 (by rfl) ⟨371868, by rfl⟩ : syracuseStep 991649 = 743737) B743737
theorem B1057187 : Blo 658307 1057187 := bstep (se 1 (by rfl) ⟨792890, by rfl⟩ : syracuseStep 1057187 = 1585781) B1585781
theorem B795043 : Blo 658307 795043 := bstep (se 1 (by rfl) ⟨596282, by rfl⟩ : syracuseStep 795043 = 1192565) B1192565
theorem B991667 : Blo 658307 991667 := bstep (se 1 (by rfl) ⟨743750, by rfl⟩ : syracuseStep 991667 = 1487501) B1487501
theorem B1483217 : Blo 658307 1483217 := bstep (se 2 (by rfl) ⟨556206, by rfl⟩ : syracuseStep 1483217 = 1112413) B1112413
theorem B991697 : Blo 658307 991697 := bstep (se 2 (by rfl) ⟨371886, by rfl⟩ : syracuseStep 991697 = 743773) B743773
theorem B1483235 : Blo 658307 1483235 := bstep (se 1 (by rfl) ⟨1112426, by rfl⟩ : syracuseStep 1483235 = 2224853) B2224853
theorem B991715 : Blo 658307 991715 := bstep (se 1 (by rfl) ⟨743786, by rfl⟩ : syracuseStep 991715 = 1487573) B1487573
theorem B827875 : Blo 658307 827875 := bstep (se 1 (by rfl) ⟨620906, by rfl⟩ : syracuseStep 827875 = 1241813) B1241813
theorem B1253873 : Blo 658307 1253873 := bstep (se 2 (by rfl) ⟨470202, by rfl⟩ : syracuseStep 1253873 = 940405) B940405
theorem B991745 : Blo 658307 991745 := bstep (se 2 (by rfl) ⟨371904, by rfl⟩ : syracuseStep 991745 = 743809) B743809
theorem B991763 : Blo 658307 991763 := bstep (se 1 (by rfl) ⟨743822, by rfl⟩ : syracuseStep 991763 = 1487645) B1487645
theorem B991793 : Blo 658307 991793 := bstep (se 2 (by rfl) ⟨371922, by rfl⟩ : syracuseStep 991793 = 743845) B743845
theorem B991811 : Blo 658307 991811 := bstep (se 1 (by rfl) ⟨743858, by rfl⟩ : syracuseStep 991811 = 1487717) B1487717
theorem B991841 : Blo 658307 991841 := bstep (se 2 (by rfl) ⟨371940, by rfl⟩ : syracuseStep 991841 = 743881) B743881
theorem B991859 : Blo 658307 991859 := bstep (se 1 (by rfl) ⟨743894, by rfl⟩ : syracuseStep 991859 = 1487789) B1487789
theorem B1057411 : Blo 658307 1057411 := bstep (se 1 (by rfl) ⟨793058, by rfl⟩ : syracuseStep 1057411 = 1586117) B1586117
theorem B991889 : Blo 658307 991889 := bstep (se 2 (by rfl) ⟨371958, by rfl⟩ : syracuseStep 991889 = 743917) B743917
theorem B991907 : Blo 658307 991907 := bstep (se 1 (by rfl) ⟨743930, by rfl⟩ : syracuseStep 991907 = 1487861) B1487861
theorem B991937 : Blo 658307 991937 := bstep (se 2 (by rfl) ⟨371976, by rfl⟩ : syracuseStep 991937 = 743953) B743953
theorem B1057475 : Blo 658307 1057475 := bstep (se 1 (by rfl) ⟨793106, by rfl⟩ : syracuseStep 1057475 = 1586213) B1586213
theorem B991955 : Blo 658307 991955 := bstep (se 1 (by rfl) ⟨743966, by rfl⟩ : syracuseStep 991955 = 1487933) B1487933
theorem B1483505 : Blo 658307 1483505 := bstep (se 2 (by rfl) ⟨556314, by rfl⟩ : syracuseStep 1483505 = 1112629) B1112629
theorem B991985 : Blo 658307 991985 := bstep (se 2 (by rfl) ⟨371994, by rfl⟩ : syracuseStep 991985 = 743989) B743989
theorem B1483523 : Blo 658307 1483523 := bstep (se 1 (by rfl) ⟨1112642, by rfl⟩ : syracuseStep 1483523 = 2225285) B2225285
theorem B992003 : Blo 658307 992003 := bstep (se 1 (by rfl) ⟨744002, by rfl⟩ : syracuseStep 992003 = 1488005) B1488005
theorem B992033 : Blo 658307 992033 := bstep (se 2 (by rfl) ⟨372012, by rfl⟩ : syracuseStep 992033 = 744025) B744025
theorem B992051 : Blo 658307 992051 := bstep (se 1 (by rfl) ⟨744038, by rfl⟩ : syracuseStep 992051 = 1488077) B1488077
theorem B1057603 : Blo 658307 1057603 := bstep (se 1 (by rfl) ⟨793202, by rfl⟩ : syracuseStep 1057603 = 1586405) B1586405
theorem B992081 : Blo 658307 992081 := bstep (se 2 (by rfl) ⟨372030, by rfl⟩ : syracuseStep 992081 = 744061) B744061
theorem B992099 : Blo 658307 992099 := bstep (se 1 (by rfl) ⟨744074, by rfl⟩ : syracuseStep 992099 = 1488149) B1488149
theorem B2007917 : Blo 658307 2007917 := bstep (se 3 (by rfl) ⟨376484, by rfl⟩ : syracuseStep 2007917 = 752969) B752969
theorem B992129 : Blo 658307 992129 := bstep (se 2 (by rfl) ⟨372048, by rfl⟩ : syracuseStep 992129 = 744097) B744097
theorem B1254275 : Blo 658307 1254275 := bstep (se 1 (by rfl) ⟨940706, by rfl⟩ : syracuseStep 1254275 = 1881413) B1881413
theorem B992147 : Blo 658307 992147 := bstep (se 1 (by rfl) ⟨744110, by rfl⟩ : syracuseStep 992147 = 1488221) B1488221
theorem B992177 : Blo 658307 992177 := bstep (se 2 (by rfl) ⟨372066, by rfl⟩ : syracuseStep 992177 = 744133) B744133
theorem B992195 : Blo 658307 992195 := bstep (se 1 (by rfl) ⟨744146, by rfl⟩ : syracuseStep 992195 = 1488293) B1488293
theorem B893921 : Blo 658307 893921 := bstep (se 2 (by rfl) ⟨335220, by rfl⟩ : syracuseStep 893921 = 670441) B670441
theorem B992225 : Blo 658307 992225 := bstep (se 2 (by rfl) ⟨372084, by rfl⟩ : syracuseStep 992225 = 744169) B744169
theorem B7513073 : Blo 658307 7513073 := bstep (se 2 (by rfl) ⟨2817402, by rfl⟩ : syracuseStep 7513073 = 5634805) B5634805
theorem B992243 : Blo 658307 992243 := bstep (se 1 (by rfl) ⟨744182, by rfl⟩ : syracuseStep 992243 = 1488365) B1488365
theorem B893953 : Blo 658307 893953 := bstep (se 2 (by rfl) ⟨335232, by rfl⟩ : syracuseStep 893953 = 670465) B670465
theorem B1483793 : Blo 658307 1483793 := bstep (se 2 (by rfl) ⟨556422, by rfl⟩ : syracuseStep 1483793 = 1112845) B1112845
theorem B992273 : Blo 658307 992273 := bstep (se 2 (by rfl) ⟨372102, by rfl⟩ : syracuseStep 992273 = 744205) B744205
theorem B2499619 : Blo 658307 2499619 := bstep (se 1 (by rfl) ⟨1874714, by rfl⟩ : syracuseStep 2499619 = 3749429) B3749429
theorem B1483811 : Blo 658307 1483811 := bstep (se 1 (by rfl) ⟨1112858, by rfl⟩ : syracuseStep 1483811 = 2225717) B2225717
theorem B992291 : Blo 658307 992291 := bstep (se 1 (by rfl) ⟨744218, by rfl⟩ : syracuseStep 992291 = 1488437) B1488437
theorem B992321 : Blo 658307 992321 := bstep (se 2 (by rfl) ⟨372120, by rfl⟩ : syracuseStep 992321 = 744241) B744241
theorem B894035 : Blo 658307 894035 := bstep (se 1 (by rfl) ⟨670526, by rfl⟩ : syracuseStep 894035 = 1341053) B1341053
theorem B992339 : Blo 658307 992339 := bstep (se 1 (by rfl) ⟨744254, by rfl⟩ : syracuseStep 992339 = 1488509) B1488509
theorem B992369 : Blo 658307 992369 := bstep (se 2 (by rfl) ⟨372138, by rfl⟩ : syracuseStep 992369 = 744277) B744277
theorem B992387 : Blo 658307 992387 := bstep (se 1 (by rfl) ⟨744290, by rfl⟩ : syracuseStep 992387 = 1488581) B1488581
theorem B992417 : Blo 658307 992417 := bstep (se 2 (by rfl) ⟨372156, by rfl⟩ : syracuseStep 992417 = 744313) B744313
theorem B1877165 : Blo 658307 1877165 := bstep (se 3 (by rfl) ⟨351968, by rfl⟩ : syracuseStep 1877165 = 703937) B703937
theorem B992435 : Blo 658307 992435 := bstep (se 1 (by rfl) ⟨744326, by rfl⟩ : syracuseStep 992435 = 1488653) B1488653
theorem B992465 : Blo 658307 992465 := bstep (se 2 (by rfl) ⟨372174, by rfl⟩ : syracuseStep 992465 = 744349) B744349
theorem B992483 : Blo 658307 992483 := bstep (se 1 (by rfl) ⟨744362, by rfl⟩ : syracuseStep 992483 = 1488725) B1488725
theorem B3351779 : Blo 658307 3351779 := bstep (se 1 (by rfl) ⟨2513834, by rfl⟩ : syracuseStep 3351779 = 5027669) B5027669
theorem B992513 : Blo 658307 992513 := bstep (se 2 (by rfl) ⟨372192, by rfl⟩ : syracuseStep 992513 = 744385) B744385
theorem B992531 : Blo 658307 992531 := bstep (se 1 (by rfl) ⟨744398, by rfl⟩ : syracuseStep 992531 = 1488797) B1488797
theorem B1484081 : Blo 658307 1484081 := bstep (se 2 (by rfl) ⟨556530, by rfl⟩ : syracuseStep 1484081 = 1113061) B1113061
theorem B1189169 : Blo 658307 1189169 := bstep (se 2 (by rfl) ⟨445938, by rfl⟩ : syracuseStep 1189169 = 891877) B891877
theorem B992561 : Blo 658307 992561 := bstep (se 2 (by rfl) ⟨372210, by rfl⟩ : syracuseStep 992561 = 744421) B744421
theorem B1484099 : Blo 658307 1484099 := bstep (se 1 (by rfl) ⟨1113074, by rfl⟩ : syracuseStep 1484099 = 2226149) B2226149
theorem B992579 : Blo 658307 992579 := bstep (se 1 (by rfl) ⟨744434, by rfl⟩ : syracuseStep 992579 = 1488869) B1488869
theorem B992609 : Blo 658307 992609 := bstep (se 2 (by rfl) ⟨372228, by rfl⟩ : syracuseStep 992609 = 744457) B744457
theorem B1877357 : Blo 658307 1877357 := bstep (se 3 (by rfl) ⟨352004, by rfl⟩ : syracuseStep 1877357 = 704009) B704009
theorem B992627 : Blo 658307 992627 := bstep (se 1 (by rfl) ⟨744470, by rfl⟩ : syracuseStep 992627 = 1488941) B1488941
theorem B992657 : Blo 658307 992657 := bstep (se 2 (by rfl) ⟨372246, by rfl⟩ : syracuseStep 992657 = 744493) B744493
theorem B992675 : Blo 658307 992675 := bstep (se 1 (by rfl) ⟨744506, by rfl⟩ : syracuseStep 992675 = 1489013) B1489013
theorem B894385 : Blo 658307 894385 := bstep (se 2 (by rfl) ⟨335394, by rfl⟩ : syracuseStep 894385 = 670789) B670789
theorem B992705 : Blo 658307 992705 := bstep (se 2 (by rfl) ⟨372264, by rfl⟩ : syracuseStep 992705 = 744529) B744529
theorem B992723 : Blo 658307 992723 := bstep (se 1 (by rfl) ⟨744542, by rfl⟩ : syracuseStep 992723 = 1489085) B1489085
theorem B992753 : Blo 658307 992753 := bstep (se 2 (by rfl) ⟨372282, by rfl⟩ : syracuseStep 992753 = 744565) B744565
theorem B992771 : Blo 658307 992771 := bstep (se 1 (by rfl) ⟨744578, by rfl⟩ : syracuseStep 992771 = 1489157) B1489157
theorem B1058321 : Blo 658307 1058321 := bstep (se 2 (by rfl) ⟨396870, by rfl⟩ : syracuseStep 1058321 = 793741) B793741
theorem B992801 : Blo 658307 992801 := bstep (se 2 (by rfl) ⟨372300, by rfl⟩ : syracuseStep 992801 = 744601) B744601
theorem B992819 : Blo 658307 992819 := bstep (se 1 (by rfl) ⟨744614, by rfl⟩ : syracuseStep 992819 = 1489229) B1489229
theorem B1484369 : Blo 658307 1484369 := bstep (se 2 (by rfl) ⟨556638, by rfl⟩ : syracuseStep 1484369 = 1113277) B1113277
theorem B992849 : Blo 658307 992849 := bstep (se 2 (by rfl) ⟨372318, by rfl⟩ : syracuseStep 992849 = 744637) B744637
theorem B1484387 : Blo 658307 1484387 := bstep (se 1 (by rfl) ⟨1113290, by rfl⟩ : syracuseStep 1484387 = 2226581) B2226581
theorem B992867 : Blo 658307 992867 := bstep (se 1 (by rfl) ⟨744650, by rfl⟩ : syracuseStep 992867 = 1489301) B1489301
theorem B992897 : Blo 658307 992897 := bstep (se 2 (by rfl) ⟨372336, by rfl⟩ : syracuseStep 992897 = 744673) B744673
theorem B1058449 : Blo 658307 1058449 := bstep (se 2 (by rfl) ⟨396918, by rfl⟩ : syracuseStep 1058449 = 793837) B793837
theorem B992915 : Blo 658307 992915 := bstep (se 1 (by rfl) ⟨744686, by rfl⟩ : syracuseStep 992915 = 1489373) B1489373
theorem B992945 : Blo 658307 992945 := bstep (se 2 (by rfl) ⟨372354, by rfl⟩ : syracuseStep 992945 = 744709) B744709
theorem B992963 : Blo 658307 992963 := bstep (se 1 (by rfl) ⟨744722, by rfl⟩ : syracuseStep 992963 = 1489445) B1489445
theorem B992993 : Blo 658307 992993 := bstep (se 2 (by rfl) ⟨372372, by rfl⟩ : syracuseStep 992993 = 744745) B744745
theorem B993011 : Blo 658307 993011 := bstep (se 1 (by rfl) ⟨744758, by rfl⟩ : syracuseStep 993011 = 1489517) B1489517
theorem B1255171 : Blo 658307 1255171 := bstep (se 1 (by rfl) ⟨941378, by rfl⟩ : syracuseStep 1255171 = 1882757) B1882757
theorem B993041 : Blo 658307 993041 := bstep (se 2 (by rfl) ⟨372390, by rfl⟩ : syracuseStep 993041 = 744781) B744781
theorem B993059 : Blo 658307 993059 := bstep (se 1 (by rfl) ⟨744794, by rfl⟩ : syracuseStep 993059 = 1489589) B1489589
theorem B993089 : Blo 658307 993089 := bstep (se 2 (by rfl) ⟨372408, by rfl⟩ : syracuseStep 993089 = 744817) B744817
theorem B993107 : Blo 658307 993107 := bstep (se 1 (by rfl) ⟨744830, by rfl⟩ : syracuseStep 993107 = 1489661) B1489661
theorem B1484657 : Blo 658307 1484657 := bstep (se 2 (by rfl) ⟨556746, by rfl⟩ : syracuseStep 1484657 = 1113493) B1113493
theorem B993137 : Blo 658307 993137 := bstep (se 2 (by rfl) ⟨372426, by rfl⟩ : syracuseStep 993137 = 744853) B744853
theorem B1484675 : Blo 658307 1484675 := bstep (se 1 (by rfl) ⟨1113506, by rfl⟩ : syracuseStep 1484675 = 2227013) B2227013
theorem B993155 : Blo 658307 993155 := bstep (se 1 (by rfl) ⟨744866, by rfl⟩ : syracuseStep 993155 = 1489733) B1489733
theorem B993185 : Blo 658307 993185 := bstep (se 2 (by rfl) ⟨372444, by rfl⟩ : syracuseStep 993185 = 744889) B744889
theorem B1255331 : Blo 658307 1255331 := bstep (se 1 (by rfl) ⟨941498, by rfl⟩ : syracuseStep 1255331 = 1882997) B1882997
theorem B894883 : Blo 658307 894883 := bstep (se 1 (by rfl) ⟨671162, by rfl⟩ : syracuseStep 894883 = 1342325) B1342325
theorem B993203 : Blo 658307 993203 := bstep (se 1 (by rfl) ⟨744902, by rfl⟩ : syracuseStep 993203 = 1489805) B1489805
theorem B993233 : Blo 658307 993233 := bstep (se 2 (by rfl) ⟨372462, by rfl⟩ : syracuseStep 993233 = 744925) B744925
theorem B993251 : Blo 658307 993251 := bstep (se 1 (by rfl) ⟨744938, by rfl⟩ : syracuseStep 993251 = 1489877) B1489877
theorem B993281 : Blo 658307 993281 := bstep (se 2 (by rfl) ⟨372480, by rfl⟩ : syracuseStep 993281 = 744961) B744961
theorem B3352589 : Blo 658307 3352589 := bstep (se 3 (by rfl) ⟨628610, by rfl⟩ : syracuseStep 3352589 = 1257221) B1257221
theorem B1058833 : Blo 658307 1058833 := bstep (se 2 (by rfl) ⟨397062, by rfl⟩ : syracuseStep 1058833 = 794125) B794125
theorem B993299 : Blo 658307 993299 := bstep (se 1 (by rfl) ⟨744974, by rfl⟩ : syracuseStep 993299 = 1489949) B1489949
theorem B993329 : Blo 658307 993329 := bstep (se 2 (by rfl) ⟨372498, by rfl⟩ : syracuseStep 993329 = 744997) B744997
theorem B993347 : Blo 658307 993347 := bstep (se 1 (by rfl) ⟨745010, by rfl⟩ : syracuseStep 993347 = 1490021) B1490021
theorem B993377 : Blo 658307 993377 := bstep (se 2 (by rfl) ⟨372516, by rfl⟩ : syracuseStep 993377 = 745033) B745033
theorem B993395 : Blo 658307 993395 := bstep (se 1 (by rfl) ⟨745046, by rfl⟩ : syracuseStep 993395 = 1490093) B1490093
theorem B1484945 : Blo 658307 1484945 := bstep (se 2 (by rfl) ⟨556854, by rfl⟩ : syracuseStep 1484945 = 1113709) B1113709
theorem B993425 : Blo 658307 993425 := bstep (se 2 (by rfl) ⟨372534, by rfl⟩ : syracuseStep 993425 = 745069) B745069
theorem B1484963 : Blo 658307 1484963 := bstep (se 1 (by rfl) ⟨1113722, by rfl⟩ : syracuseStep 1484963 = 2227445) B2227445
theorem B993443 : Blo 658307 993443 := bstep (se 1 (by rfl) ⟨745082, by rfl⟩ : syracuseStep 993443 = 1490165) B1490165
theorem B1714403 : Blo 658307 1714403 := bstep (se 1 (by rfl) ⟨1285802, by rfl⟩ : syracuseStep 1714403 = 2571605) B2571605
theorem B3385613 : Blo 658307 3385613 := bstep (se 3 (by rfl) ⟨634802, by rfl⟩ : syracuseStep 3385613 = 1269605) B1269605
theorem B1059089 : Blo 658307 1059089 := bstep (se 2 (by rfl) ⟨397158, by rfl⟩ : syracuseStep 1059089 = 794317) B794317
theorem B1878349 : Blo 658307 1878349 := bstep (se 3 (by rfl) ⟨352190, by rfl⟩ : syracuseStep 1878349 = 704381) B704381
theorem B1485233 : Blo 658307 1485233 := bstep (se 2 (by rfl) ⟨556962, by rfl⟩ : syracuseStep 1485233 = 1113925) B1113925
theorem B1485251 : Blo 658307 1485251 := bstep (se 1 (by rfl) ⟨1113938, by rfl⟩ : syracuseStep 1485251 = 2227877) B2227877
theorem B2534093 : Blo 658307 2534093 := bstep (se 3 (by rfl) ⟨475142, by rfl⟩ : syracuseStep 2534093 = 950285) B950285
theorem B1485521 : Blo 658307 1485521 := bstep (se 2 (by rfl) ⟨557070, by rfl⟩ : syracuseStep 1485521 = 1114141) B1114141
theorem B1485539 : Blo 658307 1485539 := bstep (se 1 (by rfl) ⟨1114154, by rfl⟩ : syracuseStep 1485539 = 2228309) B2228309
theorem B2141005 : Blo 658307 2141005 := bstep (se 3 (by rfl) ⟨401438, by rfl⟩ : syracuseStep 2141005 = 802877) B802877
theorem B1256401 : Blo 658307 1256401 := bstep (se 2 (by rfl) ⟨471150, by rfl⟩ : syracuseStep 1256401 = 942301) B942301
theorem B1485809 : Blo 658307 1485809 := bstep (se 2 (by rfl) ⟨557178, by rfl⟩ : syracuseStep 1485809 = 1114357) B1114357
theorem B5024753 : Blo 658307 5024753 := bstep (se 2 (by rfl) ⟨1884282, by rfl⟩ : syracuseStep 5024753 = 3768565) B3768565
theorem B1485827 : Blo 658307 1485827 := bstep (se 1 (by rfl) ⟨1114370, by rfl⟩ : syracuseStep 1485827 = 2228741) B2228741
theorem B2501837 : Blo 658307 2501837 := bstep (se 3 (by rfl) ⟨469094, by rfl⟩ : syracuseStep 2501837 = 938189) B938189
theorem B2010349 : Blo 658307 2010349 := bstep (se 3 (by rfl) ⟨376940, by rfl⟩ : syracuseStep 2010349 = 753881) B753881
theorem B1486097 : Blo 658307 1486097 := bstep (se 2 (by rfl) ⟨557286, by rfl⟩ : syracuseStep 1486097 = 1114573) B1114573
theorem B1486115 : Blo 658307 1486115 := bstep (se 1 (by rfl) ⟨1114586, by rfl⟩ : syracuseStep 1486115 = 2229173) B2229173
theorem B6040973 : Blo 658307 6040973 := bstep (se 3 (by rfl) ⟨1132682, by rfl⟩ : syracuseStep 6040973 = 2265365) B2265365
theorem B1486385 : Blo 658307 1486385 := bstep (se 2 (by rfl) ⟨557394, by rfl⟩ : syracuseStep 1486385 = 1114789) B1114789
theorem B1486403 : Blo 658307 1486403 := bstep (se 1 (by rfl) ⟨1114802, by rfl⟩ : syracuseStep 1486403 = 2229605) B2229605
theorem B1191505 : Blo 658307 1191505 := bstep (se 2 (by rfl) ⟨446814, by rfl⟩ : syracuseStep 1191505 = 893629) B893629
theorem B1060499 : Blo 658307 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B1486673 : Blo 658307 1486673 := bstep (se 2 (by rfl) ⟨557502, by rfl⟩ : syracuseStep 1486673 = 1115005) B1115005
theorem B1486691 : Blo 658307 1486691 := bstep (se 1 (by rfl) ⟨1115018, by rfl⟩ : syracuseStep 1486691 = 2230037) B2230037
theorem B1880081 : Blo 658307 1880081 := bstep (se 2 (by rfl) ⟨705030, by rfl⟩ : syracuseStep 1880081 = 1410061) B1410061
theorem B1486961 : Blo 658307 1486961 := bstep (se 2 (by rfl) ⟨557610, by rfl⟩ : syracuseStep 1486961 = 1115221) B1115221
theorem B1486979 : Blo 658307 1486979 := bstep (se 1 (by rfl) ⟨1115234, by rfl⟩ : syracuseStep 1486979 = 2230469) B2230469
theorem B1880273 : Blo 658307 1880273 := bstep (se 2 (by rfl) ⟨705102, by rfl⟩ : syracuseStep 1880273 = 1410205) B1410205
theorem B1487249 : Blo 658307 1487249 := bstep (se 2 (by rfl) ⟨557718, by rfl⟩ : syracuseStep 1487249 = 1115437) B1115437
theorem B1487267 : Blo 658307 1487267 := bstep (se 1 (by rfl) ⟨1115450, by rfl⟩ : syracuseStep 1487267 = 2230901) B2230901
theorem B2109901 : Blo 658307 2109901 := bstep (se 3 (by rfl) ⟨395606, by rfl⟩ : syracuseStep 2109901 = 791213) B791213
theorem B1028675 : Blo 658307 1028675 := bstep (se 1 (by rfl) ⟨771506, by rfl⟩ : syracuseStep 1028675 = 1543013) B1543013
theorem B1487537 : Blo 658307 1487537 := bstep (se 2 (by rfl) ⟨557826, by rfl⟩ : syracuseStep 1487537 = 1115653) B1115653
theorem B1487555 : Blo 658307 1487555 := bstep (se 1 (by rfl) ⟨1115666, by rfl⟩ : syracuseStep 1487555 = 2231333) B2231333
theorem B2569073 : Blo 658307 2569073 := bstep (se 2 (by rfl) ⟨963402, by rfl⟩ : syracuseStep 2569073 = 1926805) B1926805
theorem B1487825 : Blo 658307 1487825 := bstep (se 2 (by rfl) ⟨557934, by rfl⟩ : syracuseStep 1487825 = 1115869) B1115869
theorem B734179 : Blo 658307 734179 := bstep (se 1 (by rfl) ⟨550634, by rfl⟩ : syracuseStep 734179 = 1101269) B1101269
theorem B1487843 : Blo 658307 1487843 := bstep (se 1 (by rfl) ⟨1115882, by rfl⟩ : syracuseStep 1487843 = 2231765) B2231765
theorem B2012273 : Blo 658307 2012273 := bstep (se 2 (by rfl) ⟨754602, by rfl⟩ : syracuseStep 2012273 = 1509205) B1509205
theorem B11416717 : Blo 658307 11416717 := bstep (se 3 (by rfl) ⟨2140634, by rfl⟩ : syracuseStep 11416717 = 4281269) B4281269
theorem B1881265 : Blo 658307 1881265 := bstep (se 2 (by rfl) ⟨705474, by rfl⟩ : syracuseStep 1881265 = 1410949) B1410949
theorem B1488113 : Blo 658307 1488113 := bstep (se 2 (by rfl) ⟨558042, by rfl⟩ : syracuseStep 1488113 = 1116085) B1116085
theorem B1488131 : Blo 658307 1488131 := bstep (se 1 (by rfl) ⟨1116098, by rfl⟩ : syracuseStep 1488131 = 2232197) B2232197
theorem B5715299 : Blo 658307 5715299 := bstep (se 1 (by rfl) ⟨4286474, by rfl⟩ : syracuseStep 5715299 = 8572949) B8572949
theorem B1783235 : Blo 658307 1783235 := bstep (se 1 (by rfl) ⟨1337426, by rfl⟩ : syracuseStep 1783235 = 2674853) B2674853
theorem B1881539 : Blo 658307 1881539 := bstep (se 1 (by rfl) ⟨1411154, by rfl⟩ : syracuseStep 1881539 = 2822309) B2822309
theorem B1488401 : Blo 658307 1488401 := bstep (se 2 (by rfl) ⟨558150, by rfl⟩ : syracuseStep 1488401 = 1116301) B1116301
theorem B1488419 : Blo 658307 1488419 := bstep (se 1 (by rfl) ⟨1116314, by rfl⟩ : syracuseStep 1488419 = 2232629) B2232629
theorem B1881731 : Blo 658307 1881731 := bstep (se 1 (by rfl) ⟨1411298, by rfl⟩ : syracuseStep 1881731 = 2822597) B2822597
theorem B833267 : Blo 658307 833267 := bstep (se 1 (by rfl) ⟨624950, by rfl⟩ : syracuseStep 833267 = 1249901) B1249901
theorem B1488689 : Blo 658307 1488689 := bstep (se 2 (by rfl) ⟨558258, by rfl⟩ : syracuseStep 1488689 = 1116517) B1116517
theorem B1488707 : Blo 658307 1488707 := bstep (se 1 (by rfl) ⟨1116530, by rfl⟩ : syracuseStep 1488707 = 2233061) B2233061
theorem B2504753 : Blo 658307 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B1488977 : Blo 658307 1488977 := bstep (se 2 (by rfl) ⟨558366, by rfl⟩ : syracuseStep 1488977 = 1116733) B1116733
theorem B1488995 : Blo 658307 1488995 := bstep (se 1 (by rfl) ⟨1116746, by rfl⟩ : syracuseStep 1488995 = 2233493) B2233493
theorem B4241585 : Blo 658307 4241585 := bstep (se 2 (by rfl) ⟨1590594, by rfl⟩ : syracuseStep 4241585 = 3181189) B3181189
theorem B1718513 : Blo 658307 1718513 := bstep (se 2 (by rfl) ⟨644442, by rfl⟩ : syracuseStep 1718513 = 1288885) B1288885
theorem B1784177 : Blo 658307 1784177 := bstep (se 2 (by rfl) ⟨669066, by rfl⟩ : syracuseStep 1784177 = 1338133) B1338133
theorem B1489265 : Blo 658307 1489265 := bstep (se 2 (by rfl) ⟨558474, by rfl⟩ : syracuseStep 1489265 = 1116949) B1116949
theorem B1489283 : Blo 658307 1489283 := bstep (se 1 (by rfl) ⟨1116962, by rfl⟩ : syracuseStep 1489283 = 2233925) B2233925
theorem B1882541 : Blo 658307 1882541 := bstep (se 3 (by rfl) ⟨352976, by rfl⟩ : syracuseStep 1882541 = 705953) B705953
theorem B833971 : Blo 658307 833971 := bstep (se 1 (by rfl) ⟨625478, by rfl⟩ : syracuseStep 833971 = 1250957) B1250957
theorem B834067 : Blo 658307 834067 := bstep (se 1 (by rfl) ⟨625550, by rfl⟩ : syracuseStep 834067 = 1251101) B1251101
theorem B2013731 : Blo 658307 2013731 := bstep (se 1 (by rfl) ⟨1510298, by rfl⟩ : syracuseStep 2013731 = 3020597) B3020597
theorem B703027 : Blo 658307 703027 := bstep (se 1 (by rfl) ⟨527270, by rfl⟩ : syracuseStep 703027 = 1054541) B1054541
theorem B1882723 : Blo 658307 1882723 := bstep (se 1 (by rfl) ⟨1412042, by rfl⟩ : syracuseStep 1882723 = 2824085) B2824085
theorem B1489553 : Blo 658307 1489553 := bstep (se 2 (by rfl) ⟨558582, by rfl⟩ : syracuseStep 1489553 = 1117165) B1117165
theorem B1489571 : Blo 658307 1489571 := bstep (se 1 (by rfl) ⟨1117178, by rfl⟩ : syracuseStep 1489571 = 2234357) B2234357
theorem B2538161 : Blo 658307 2538161 := bstep (se 2 (by rfl) ⟨951810, by rfl⟩ : syracuseStep 2538161 = 1903621) B1903621
theorem B2538317 : Blo 658307 2538317 := bstep (se 3 (by rfl) ⟨475934, by rfl⟩ : syracuseStep 2538317 = 951869) B951869
theorem B1489841 : Blo 658307 1489841 := bstep (se 2 (by rfl) ⟨558690, by rfl⟩ : syracuseStep 1489841 = 1117381) B1117381
theorem B1489859 : Blo 658307 1489859 := bstep (se 1 (by rfl) ⟨1117394, by rfl⟩ : syracuseStep 1489859 = 2234789) B2234789
theorem B2538467 : Blo 658307 2538467 := bstep (se 1 (by rfl) ⟨1903850, by rfl⟩ : syracuseStep 2538467 = 3807701) B3807701
theorem B834563 : Blo 658307 834563 := bstep (se 1 (by rfl) ⟨625922, by rfl⟩ : syracuseStep 834563 = 1251845) B1251845
theorem B1588241 : Blo 658307 1588241 := bstep (se 2 (by rfl) ⟨595590, by rfl⟩ : syracuseStep 1588241 = 1191181) B1191181
theorem B1883213 : Blo 658307 1883213 := bstep (se 3 (by rfl) ⟨353102, by rfl⟩ : syracuseStep 1883213 = 706205) B706205
theorem B1490129 : Blo 658307 1490129 := bstep (se 2 (by rfl) ⟨558798, by rfl⟩ : syracuseStep 1490129 = 1117597) B1117597
theorem B1490147 : Blo 658307 1490147 := bstep (se 1 (by rfl) ⟨1117610, by rfl⟩ : syracuseStep 1490147 = 2235221) B2235221
theorem B2145571 : Blo 658307 2145571 := bstep (se 1 (by rfl) ⟨1609178, by rfl⟩ : syracuseStep 2145571 = 3218357) B3218357
theorem B1785137 : Blo 658307 1785137 := bstep (se 2 (by rfl) ⟨669426, by rfl⟩ : syracuseStep 1785137 = 1338853) B1338853
theorem B7126325 : Blo 658307 7126325 := bstep (se 5 (by rfl) ⟨334046, by rfl⟩ : syracuseStep 7126325 = 668093) B668093
theorem B4767173 : Blo 658307 4767173 := bstep (se 4 (by rfl) ⟨446922, by rfl⟩ : syracuseStep 4767173 = 893845) B893845
theorem B2506211 : Blo 658307 2506211 := bstep (se 1 (by rfl) ⟨1879658, by rfl⟩ : syracuseStep 2506211 = 3759317) B3759317
theorem B835267 : Blo 658307 835267 := bstep (se 1 (by rfl) ⟨626450, by rfl⟩ : syracuseStep 835267 = 1252901) B1252901
theorem B835363 : Blo 658307 835363 := bstep (se 1 (by rfl) ⟨626522, by rfl⟩ : syracuseStep 835363 = 1253045) B1253045
theorem B2113361 : Blo 658307 2113361 := bstep (se 2 (by rfl) ⟨792510, by rfl⟩ : syracuseStep 2113361 = 1585021) B1585021
theorem B704419 : Blo 658307 704419 := bstep (se 1 (by rfl) ⟨528314, by rfl⟩ : syracuseStep 704419 = 1056629) B1056629
theorem B2113553 : Blo 658307 2113553 := bstep (se 2 (by rfl) ⟨792582, by rfl⟩ : syracuseStep 2113553 = 1585165) B1585165
theorem B1884397 : Blo 658307 1884397 := bstep (se 3 (by rfl) ⟨353324, by rfl⟩ : syracuseStep 1884397 = 706649) B706649
theorem B835859 : Blo 658307 835859 := bstep (se 1 (by rfl) ⟨626894, by rfl⟩ : syracuseStep 835859 = 1253789) B1253789
theorem B2507213 : Blo 658307 2507213 := bstep (se 3 (by rfl) ⟨470102, by rfl⟩ : syracuseStep 2507213 = 940205) B940205
theorem B1786349 : Blo 658307 1786349 := bstep (se 3 (by rfl) ⟨334940, by rfl⟩ : syracuseStep 1786349 = 669881) B669881
theorem B836563 : Blo 658307 836563 := bstep (se 1 (by rfl) ⟨627422, by rfl⟩ : syracuseStep 836563 = 1254845) B1254845
theorem B836659 : Blo 658307 836659 := bstep (se 1 (by rfl) ⟨627494, by rfl⟩ : syracuseStep 836659 = 1254989) B1254989
theorem B1885457 : Blo 658307 1885457 := bstep (se 2 (by rfl) ⟨707046, by rfl⟩ : syracuseStep 1885457 = 1414093) B1414093
theorem B1131875 : Blo 658307 1131875 := bstep (se 1 (by rfl) ⟨848906, by rfl⟩ : syracuseStep 1131875 = 1697813) B1697813
theorem B4015565 : Blo 658307 4015565 := bstep (se 3 (by rfl) ⟨752918, by rfl⟩ : syracuseStep 4015565 = 1505837) B1505837
theorem B3753485 : Blo 658307 3753485 := bstep (se 3 (by rfl) ⟨703778, by rfl⟩ : syracuseStep 3753485 = 1407557) B1407557
theorem B837155 : Blo 658307 837155 := bstep (se 1 (by rfl) ⟨627866, by rfl⟩ : syracuseStep 837155 = 1255733) B1255733
theorem B5654285 : Blo 658307 5654285 := bstep (se 3 (by rfl) ⟨1060178, by rfl⟩ : syracuseStep 5654285 = 2120357) B2120357
theorem B1001441 : Blo 658307 1001441 := bstep (se 2 (by rfl) ⟨375540, by rfl⟩ : syracuseStep 1001441 = 751081) B751081
theorem B1001587 : Blo 658307 1001587 := bstep (se 1 (by rfl) ⟨751190, by rfl⟩ : syracuseStep 1001587 = 1502381) B1502381
theorem B837859 : Blo 658307 837859 := bstep (se 1 (by rfl) ⟨628394, by rfl⟩ : syracuseStep 837859 = 1256789) B1256789
theorem B2115821 : Blo 658307 2115821 := bstep (se 3 (by rfl) ⟨396716, by rfl⟩ : syracuseStep 2115821 = 793433) B793433
theorem B2672909 : Blo 658307 2672909 := bstep (se 3 (by rfl) ⟨501170, by rfl⟩ : syracuseStep 2672909 = 1002341) B1002341
theorem B837955 : Blo 658307 837955 := bstep (se 1 (by rfl) ⟨628466, by rfl⟩ : syracuseStep 837955 = 1256933) B1256933
theorem B707059 : Blo 658307 707059 := bstep (se 1 (by rfl) ⟨530294, by rfl⟩ : syracuseStep 707059 = 1060589) B1060589
theorem B2411021 : Blo 658307 2411021 := bstep (se 3 (by rfl) ⟨452066, by rfl⟩ : syracuseStep 2411021 = 904133) B904133
theorem B2509325 : Blo 658307 2509325 := bstep (se 3 (by rfl) ⟨470498, by rfl⟩ : syracuseStep 2509325 = 940997) B940997
theorem B1002755 : Blo 658307 1002755 := bstep (se 1 (by rfl) ⟨752066, by rfl⟩ : syracuseStep 1002755 = 1504133) B1504133
theorem B2510129 : Blo 658307 2510129 := bstep (se 2 (by rfl) ⟨941298, by rfl⟩ : syracuseStep 2510129 = 1882597) B1882597
theorem B740659 : Blo 658307 740659 := bstep (se 1 (by rfl) ⟨555494, by rfl⟩ : syracuseStep 740659 = 1110989) B1110989
theorem B3165581 : Blo 658307 3165581 := bstep (se 3 (by rfl) ⟨593546, by rfl⟩ : syracuseStep 3165581 = 1187093) B1187093
theorem B6344077 : Blo 658307 6344077 := bstep (se 3 (by rfl) ⟨1189514, by rfl⟩ : syracuseStep 6344077 = 2379029) B2379029
theorem B740803 : Blo 658307 740803 := bstep (se 1 (by rfl) ⟨555602, by rfl⟩ : syracuseStep 740803 = 1111205) B1111205
theorem B937489 : Blo 658307 937489 := bstep (se 2 (by rfl) ⟨351558, by rfl⟩ : syracuseStep 937489 = 703117) B703117
theorem B740947 : Blo 658307 740947 := bstep (se 1 (by rfl) ⟨555710, by rfl⟩ : syracuseStep 740947 = 1111421) B1111421
theorem B937585 : Blo 658307 937585 := bstep (se 2 (by rfl) ⟨351594, by rfl⟩ : syracuseStep 937585 = 703189) B703189
theorem B3755717 : Blo 658307 3755717 := bstep (se 4 (by rfl) ⟨352098, by rfl⟩ : syracuseStep 3755717 = 704197) B704197
theorem B741091 : Blo 658307 741091 := bstep (se 1 (by rfl) ⟨555818, by rfl⟩ : syracuseStep 741091 = 1111637) B1111637
theorem B3264241 : Blo 658307 3264241 := bstep (se 2 (by rfl) ⟨1224090, by rfl⟩ : syracuseStep 3264241 = 2448181) B2448181
theorem B2117411 : Blo 658307 2117411 := bstep (se 1 (by rfl) ⟨1588058, by rfl⟩ : syracuseStep 2117411 = 3176117) B3176117
theorem B1003313 : Blo 658307 1003313 := bstep (se 2 (by rfl) ⟨376242, by rfl⟩ : syracuseStep 1003313 = 752485) B752485
theorem B741235 : Blo 658307 741235 := bstep (se 1 (by rfl) ⟨555926, by rfl⟩ : syracuseStep 741235 = 1111853) B1111853
theorem B2510797 : Blo 658307 2510797 := bstep (se 3 (by rfl) ⟨470774, by rfl⟩ : syracuseStep 2510797 = 941549) B941549
theorem B741379 : Blo 658307 741379 := bstep (se 1 (by rfl) ⟨556034, by rfl⟩ : syracuseStep 741379 = 1112069) B1112069
theorem B938081 : Blo 658307 938081 := bstep (se 2 (by rfl) ⟨351780, by rfl⟩ : syracuseStep 938081 = 703561) B703561
theorem B6443107 : Blo 658307 6443107 := bstep (se 1 (by rfl) ⟨4832330, by rfl⟩ : syracuseStep 6443107 = 9664661) B9664661
theorem B5656675 : Blo 658307 5656675 := bstep (se 1 (by rfl) ⟨4242506, by rfl⟩ : syracuseStep 5656675 = 8485013) B8485013
theorem B2478221 : Blo 658307 2478221 := bstep (se 3 (by rfl) ⟨464666, by rfl⟩ : syracuseStep 2478221 = 929333) B929333
theorem B741523 : Blo 658307 741523 := bstep (se 1 (by rfl) ⟨556142, by rfl⟩ : syracuseStep 741523 = 1112285) B1112285
theorem B3395789 : Blo 658307 3395789 := bstep (se 3 (by rfl) ⟨636710, by rfl⟩ : syracuseStep 3395789 = 1273421) B1273421
theorem B741667 : Blo 658307 741667 := bstep (se 1 (by rfl) ⟨556250, by rfl⟩ : syracuseStep 741667 = 1112501) B1112501
theorem B2150705 : Blo 658307 2150705 := bstep (se 2 (by rfl) ⟨806514, by rfl⟩ : syracuseStep 2150705 = 1613029) B1613029
theorem B3756401 : Blo 658307 3756401 := bstep (se 2 (by rfl) ⟨1408650, by rfl⟩ : syracuseStep 3756401 = 2817301) B2817301
theorem B20304269 : Blo 658307 20304269 := bstep (se 3 (by rfl) ⟨3807050, by rfl⟩ : syracuseStep 20304269 = 7614101) B7614101
theorem B741811 : Blo 658307 741811 := bstep (se 1 (by rfl) ⟨556358, by rfl⟩ : syracuseStep 741811 = 1112717) B1112717
theorem B17125829 : Blo 658307 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B741955 : Blo 658307 741955 := bstep (se 1 (by rfl) ⟨556466, by rfl⟩ : syracuseStep 741955 = 1112933) B1112933
theorem B2118307 : Blo 658307 2118307 := bstep (se 1 (by rfl) ⟨1588730, by rfl⟩ : syracuseStep 2118307 = 3177461) B3177461
theorem B742099 : Blo 658307 742099 := bstep (se 1 (by rfl) ⟨556574, by rfl⟩ : syracuseStep 742099 = 1113149) B1113149
theorem B2511587 : Blo 658307 2511587 := bstep (se 1 (by rfl) ⟨1883690, by rfl⟩ : syracuseStep 2511587 = 3767381) B3767381
theorem B2380529 : Blo 658307 2380529 := bstep (se 2 (by rfl) ⟨892698, by rfl⟩ : syracuseStep 2380529 = 1785397) B1785397
theorem B742243 : Blo 658307 742243 := bstep (se 1 (by rfl) ⟨556682, by rfl⟩ : syracuseStep 742243 = 1113365) B1113365
theorem B938947 : Blo 658307 938947 := bstep (se 1 (by rfl) ⟨704210, by rfl⟩ : syracuseStep 938947 = 1408421) B1408421
theorem B11293667 : Blo 658307 11293667 := bstep (se 1 (by rfl) ⟨8470250, by rfl⟩ : syracuseStep 11293667 = 16940501) B16940501
theorem B742387 : Blo 658307 742387 := bstep (se 1 (by rfl) ⟨556790, by rfl⟩ : syracuseStep 742387 = 1113581) B1113581
theorem B939043 : Blo 658307 939043 := bstep (se 1 (by rfl) ⟨704282, by rfl⟩ : syracuseStep 939043 = 1408565) B1408565
theorem B1070177 : Blo 658307 1070177 := bstep (se 2 (by rfl) ⟨401316, by rfl⟩ : syracuseStep 1070177 = 802633) B802633
theorem B1430641 : Blo 658307 1430641 := bstep (se 2 (by rfl) ⟨536490, by rfl⟩ : syracuseStep 1430641 = 1072981) B1072981
theorem B742531 : Blo 658307 742531 := bstep (se 1 (by rfl) ⟨556898, by rfl⟩ : syracuseStep 742531 = 1113797) B1113797
theorem B2413745 : Blo 658307 2413745 := bstep (se 2 (by rfl) ⟨905154, by rfl⟩ : syracuseStep 2413745 = 1810309) B1810309
theorem B742675 : Blo 658307 742675 := bstep (se 1 (by rfl) ⟨557006, by rfl⟩ : syracuseStep 742675 = 1114013) B1114013
theorem B2512241 : Blo 658307 2512241 := bstep (se 2 (by rfl) ⟨942090, by rfl⟩ : syracuseStep 2512241 = 1884181) B1884181
theorem B742819 : Blo 658307 742819 := bstep (se 1 (by rfl) ⟨557114, by rfl⟩ : syracuseStep 742819 = 1114229) B1114229
theorem B939539 : Blo 658307 939539 := bstep (se 1 (by rfl) ⟨704654, by rfl⟩ : syracuseStep 939539 = 1409309) B1409309
theorem B1005089 : Blo 658307 1005089 := bstep (se 2 (by rfl) ⟨376908, by rfl⟩ : syracuseStep 1005089 = 753817) B753817
theorem B742963 : Blo 658307 742963 := bstep (se 1 (by rfl) ⟨557222, by rfl⟩ : syracuseStep 742963 = 1114445) B1114445
theorem B6346309 : Blo 658307 6346309 := bstep (se 4 (by rfl) ⟨594966, by rfl⟩ : syracuseStep 6346309 = 1189933) B1189933
theorem B743107 : Blo 658307 743107 := bstep (se 1 (by rfl) ⟨557330, by rfl⟩ : syracuseStep 743107 = 1114661) B1114661
theorem B2119409 : Blo 658307 2119409 := bstep (se 2 (by rfl) ⟨794778, by rfl⟩ : syracuseStep 2119409 = 1589557) B1589557
theorem B3757859 : Blo 658307 3757859 := bstep (se 1 (by rfl) ⟨2818394, by rfl⟩ : syracuseStep 3757859 = 5636789) B5636789
theorem B743251 : Blo 658307 743251 := bstep (se 1 (by rfl) ⟨557438, by rfl⟩ : syracuseStep 743251 = 1114877) B1114877
theorem B2119537 : Blo 658307 2119537 := bstep (se 2 (by rfl) ⟨794826, by rfl⟩ : syracuseStep 2119537 = 1589653) B1589653
theorem B743395 : Blo 658307 743395 := bstep (se 1 (by rfl) ⟨557546, by rfl⟩ : syracuseStep 743395 = 1115093) B1115093
theorem B3004465 : Blo 658307 3004465 := bstep (se 2 (by rfl) ⟨1126674, by rfl⟩ : syracuseStep 3004465 = 2253349) B2253349
theorem B743539 : Blo 658307 743539 := bstep (se 1 (by rfl) ⟨557654, by rfl⟩ : syracuseStep 743539 = 1115309) B1115309
theorem B940177 : Blo 658307 940177 := bstep (se 2 (by rfl) ⟨352566, by rfl⟩ : syracuseStep 940177 = 705133) B705133
theorem B743683 : Blo 658307 743683 := bstep (se 1 (by rfl) ⟨557762, by rfl⟩ : syracuseStep 743683 = 1115525) B1115525
theorem B5363981 : Blo 658307 5363981 := bstep (se 3 (by rfl) ⟨1005746, by rfl⟩ : syracuseStep 5363981 = 2011493) B2011493
theorem B6773105 : Blo 658307 6773105 := bstep (se 2 (by rfl) ⟨2539914, by rfl⟩ : syracuseStep 6773105 = 5079829) B5079829
theorem B743827 : Blo 658307 743827 := bstep (se 1 (by rfl) ⟨557870, by rfl⟩ : syracuseStep 743827 = 1115741) B1115741
theorem B940513 : Blo 658307 940513 := bstep (se 2 (by rfl) ⟨352692, by rfl⟩ : syracuseStep 940513 = 705385) B705385
theorem B743971 : Blo 658307 743971 := bstep (se 1 (by rfl) ⟨557978, by rfl⟩ : syracuseStep 743971 = 1115957) B1115957
theorem B744115 : Blo 658307 744115 := bstep (se 1 (by rfl) ⟨558086, by rfl⟩ : syracuseStep 744115 = 1116173) B1116173
theorem B2513699 : Blo 658307 2513699 := bstep (se 1 (by rfl) ⟨1885274, by rfl⟩ : syracuseStep 2513699 = 3770549) B3770549
theorem B2513713 : Blo 658307 2513713 := bstep (se 2 (by rfl) ⟨942642, by rfl⟩ : syracuseStep 2513713 = 1885285) B1885285
theorem B744259 : Blo 658307 744259 := bstep (se 1 (by rfl) ⟨558194, by rfl⟩ : syracuseStep 744259 = 1116389) B1116389
theorem B2120525 : Blo 658307 2120525 := bstep (se 3 (by rfl) ⟨397598, by rfl⟩ : syracuseStep 2120525 = 795197) B795197
theorem B744403 : Blo 658307 744403 := bstep (se 1 (by rfl) ⟨558302, by rfl⟩ : syracuseStep 744403 = 1116605) B1116605
theorem B1694723 : Blo 658307 1694723 := bstep (se 1 (by rfl) ⟨1271042, by rfl⟩ : syracuseStep 1694723 = 2542085) B2542085
theorem B941105 : Blo 658307 941105 := bstep (se 2 (by rfl) ⟨352914, by rfl⟩ : syracuseStep 941105 = 705829) B705829
theorem B744547 : Blo 658307 744547 := bstep (se 1 (by rfl) ⟨558410, by rfl⟩ : syracuseStep 744547 = 1116821) B1116821
theorem B744691 : Blo 658307 744691 := bstep (se 1 (by rfl) ⟨558518, by rfl⟩ : syracuseStep 744691 = 1117037) B1117037
theorem B744835 : Blo 658307 744835 := bstep (se 1 (by rfl) ⟨558626, by rfl⟩ : syracuseStep 744835 = 1117253) B1117253
theorem B4513157 : Blo 658307 4513157 := bstep (se 4 (by rfl) ⟨423108, by rfl⟩ : syracuseStep 4513157 = 846217) B846217
theorem B1007011 : Blo 658307 1007011 := bstep (se 1 (by rfl) ⟨755258, by rfl⟩ : syracuseStep 1007011 = 1510517) B1510517
theorem B744979 : Blo 658307 744979 := bstep (se 1 (by rfl) ⟨558734, by rfl⟩ : syracuseStep 744979 = 1117469) B1117469
theorem B941635 : Blo 658307 941635 := bstep (se 1 (by rfl) ⟨706226, by rfl⟩ : syracuseStep 941635 = 1412453) B1412453
theorem B941971 : Blo 658307 941971 := bstep (se 1 (by rfl) ⟨706478, by rfl⟩ : syracuseStep 941971 = 1412957) B1412957
theorem B4218929 : Blo 658307 4218929 := bstep (se 2 (by rfl) ⟨1582098, by rfl⟩ : syracuseStep 4218929 = 3164197) B3164197
theorem B942529 : Blo 658307 942529 := bstep (se 2 (by rfl) ⟨353448, by rfl⟩ : syracuseStep 942529 = 706897) B706897
theorem B942563 : Blo 658307 942563 := bstep (se 1 (by rfl) ⟨706922, by rfl⟩ : syracuseStep 942563 = 1413845) B1413845
theorem B680419 : Blo 658307 680419 := bstep (se 1 (by rfl) ⟨510314, by rfl⟩ : syracuseStep 680419 = 1020629) B1020629
theorem B12182069 : Blo 658307 12182069 := bstep (se 5 (by rfl) ⟨571034, by rfl⟩ : syracuseStep 12182069 = 1142069) B1142069
theorem B3334769 : Blo 658307 3334769 := bstep (se 2 (by rfl) ⟨1250538, by rfl⟩ : syracuseStep 3334769 = 2501077) B2501077
theorem B2548493 : Blo 658307 2548493 := bstep (se 3 (by rfl) ⟨477842, by rfl⟩ : syracuseStep 2548493 = 955685) B955685
theorem B1336259 : Blo 658307 1336259 := bstep (se 1 (by rfl) ⟨1002194, by rfl⟩ : syracuseStep 1336259 = 2004389) B2004389
theorem B3761093 : Blo 658307 3761093 := bstep (se 4 (by rfl) ⟨352602, by rfl⟩ : syracuseStep 3761093 = 705205) B705205
theorem B2254061 : Blo 658307 2254061 := bstep (se 3 (by rfl) ⟨422636, by rfl⟩ : syracuseStep 2254061 = 845273) B845273
theorem B3761549 : Blo 658307 3761549 := bstep (se 3 (by rfl) ⟨705290, by rfl⟩ : syracuseStep 3761549 = 1410581) B1410581
theorem B2254225 : Blo 658307 2254225 := bstep (se 2 (by rfl) ⟨845334, by rfl⟩ : syracuseStep 2254225 = 1690669) B1690669
theorem B11888099 : Blo 658307 11888099 := bstep (se 1 (by rfl) ⟨8916074, by rfl⟩ : syracuseStep 11888099 = 17832149) B17832149
theorem B2254445 : Blo 658307 2254445 := bstep (se 3 (by rfl) ⟨422708, by rfl⟩ : syracuseStep 2254445 = 845417) B845417
theorem B2221937 : Blo 658307 2221937 := bstep (se 2 (by rfl) ⟨833226, by rfl⟩ : syracuseStep 2221937 = 1666453) B1666453
theorem B14444401 : Blo 658307 14444401 := bstep (se 2 (by rfl) ⟨5416650, by rfl⟩ : syracuseStep 14444401 = 10833301) B10833301
theorem B3336227 : Blo 658307 3336227 := bstep (se 1 (by rfl) ⟨2502170, by rfl⟩ : syracuseStep 3336227 = 5004341) B5004341
theorem B2222477 : Blo 658307 2222477 := bstep (se 3 (by rfl) ⟨416714, by rfl⟩ : syracuseStep 2222477 = 833429) B833429
theorem B2222531 : Blo 658307 2222531 := bstep (se 1 (by rfl) ⟨1666898, by rfl⟩ : syracuseStep 2222531 = 3333797) B3333797
theorem B4221389 : Blo 658307 4221389 := bstep (se 3 (by rfl) ⟨791510, by rfl⟩ : syracuseStep 4221389 = 1583021) B1583021
theorem B4516337 : Blo 658307 4516337 := bstep (se 2 (by rfl) ⟨1693626, by rfl⟩ : syracuseStep 4516337 = 3387253) B3387253
theorem B3566213 : Blo 658307 3566213 := bstep (se 4 (by rfl) ⟨334332, by rfl⟩ : syracuseStep 3566213 = 668665) B668665
theorem B2222801 : Blo 658307 2222801 := bstep (se 2 (by rfl) ⟨833550, by rfl⟩ : syracuseStep 2222801 = 1667101) B1667101
theorem B5630705 : Blo 658307 5630705 := bstep (se 2 (by rfl) ⟨2111514, by rfl⟩ : syracuseStep 5630705 = 4223029) B4223029
theorem B4025123 : Blo 658307 4025123 := bstep (se 1 (by rfl) ⟨3018842, by rfl⟩ : syracuseStep 4025123 = 6037685) B6037685
theorem B3337037 : Blo 658307 3337037 := bstep (se 3 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 3337037 = 1251389) B1251389
theorem B2812877 : Blo 658307 2812877 := bstep (se 3 (by rfl) ⟨527414, by rfl⟩ : syracuseStep 2812877 = 1054829) B1054829
theorem B2583587 : Blo 658307 2583587 := bstep (se 1 (by rfl) ⟨1937690, by rfl⟩ : syracuseStep 2583587 = 3875381) B3875381
theorem B1502435 : Blo 658307 1502435 := bstep (se 1 (by rfl) ⟨1126826, by rfl⟩ : syracuseStep 1502435 = 2253653) B2253653
theorem B2223341 : Blo 658307 2223341 := bstep (se 3 (by rfl) ⟨416876, by rfl⟩ : syracuseStep 2223341 = 833753) B833753
theorem B3566861 : Blo 658307 3566861 := bstep (se 3 (by rfl) ⟨668786, by rfl⟩ : syracuseStep 3566861 = 1337573) B1337573
theorem B2223395 : Blo 658307 2223395 := bstep (se 1 (by rfl) ⟨1667546, by rfl⟩ : syracuseStep 2223395 = 3335093) B3335093
theorem B1666403 : Blo 658307 1666403 := bstep (se 1 (by rfl) ⟨1249802, by rfl⟩ : syracuseStep 1666403 = 2499605) B2499605
theorem B1666595 : Blo 658307 1666595 := bstep (se 1 (by rfl) ⟨1249946, by rfl⟩ : syracuseStep 1666595 = 2499893) B2499893
theorem B2223665 : Blo 658307 2223665 := bstep (se 2 (by rfl) ⟨833874, by rfl⟩ : syracuseStep 2223665 = 1667749) B1667749
theorem B847747 : Blo 658307 847747 := bstep (se 1 (by rfl) ⟨635810, by rfl⟩ : syracuseStep 847747 = 1271621) B1271621
theorem B4026289 : Blo 658307 4026289 := bstep (se 2 (by rfl) ⟨1509858, by rfl⟩ : syracuseStep 4026289 = 3019717) B3019717
theorem B3174385 : Blo 658307 3174385 := bstep (se 2 (by rfl) ⟨1190394, by rfl⟩ : syracuseStep 3174385 = 2380789) B2380789
theorem B1208369 : Blo 658307 1208369 := bstep (se 2 (by rfl) ⟨453138, by rfl⟩ : syracuseStep 1208369 = 906277) B906277
theorem B2224205 : Blo 658307 2224205 := bstep (se 3 (by rfl) ⟨417038, by rfl⟩ : syracuseStep 2224205 = 834077) B834077
theorem B3174499 : Blo 658307 3174499 := bstep (se 1 (by rfl) ⟨2380874, by rfl⟩ : syracuseStep 3174499 = 4761749) B4761749
theorem B2224259 : Blo 658307 2224259 := bstep (se 1 (by rfl) ⟨1668194, by rfl⟩ : syracuseStep 2224259 = 3336389) B3336389
theorem B4878563 : Blo 658307 4878563 := bstep (se 1 (by rfl) ⟨3658922, by rfl⟩ : syracuseStep 4878563 = 7317845) B7317845
theorem B3764465 : Blo 658307 3764465 := bstep (se 2 (by rfl) ⟨1411674, by rfl⟩ : syracuseStep 3764465 = 2823349) B2823349
theorem B22868365 : Blo 658307 22868365 := bstep (se 3 (by rfl) ⟨4287818, by rfl⟩ : syracuseStep 22868365 = 8575637) B8575637
theorem B2224529 : Blo 658307 2224529 := bstep (se 2 (by rfl) ⟨834198, by rfl⟩ : syracuseStep 2224529 = 1668397) B1668397
theorem B1667537 : Blo 658307 1667537 := bstep (se 2 (by rfl) ⟨625326, by rfl⟩ : syracuseStep 1667537 = 1250653) B1250653
theorem B1667587 : Blo 658307 1667587 := bstep (se 1 (by rfl) ⟨1250690, by rfl⟩ : syracuseStep 1667587 = 2501381) B2501381
theorem B3011107 : Blo 658307 3011107 := bstep (se 1 (by rfl) ⟨2258330, by rfl⟩ : syracuseStep 3011107 = 4516661) B4516661
theorem B1667729 : Blo 658307 1667729 := bstep (se 2 (by rfl) ⟨625398, by rfl⟩ : syracuseStep 1667729 = 1250797) B1250797
theorem B1864433 : Blo 658307 1864433 := bstep (se 2 (by rfl) ⟨699162, by rfl⟩ : syracuseStep 1864433 = 1398325) B1398325
theorem B2225069 : Blo 658307 2225069 := bstep (se 3 (by rfl) ⟨417200, by rfl⟩ : syracuseStep 2225069 = 834401) B834401
theorem B1111009 : Blo 658307 1111009 := bstep (se 2 (by rfl) ⟨416628, by rfl⟩ : syracuseStep 1111009 = 833257) B833257
theorem B2225123 : Blo 658307 2225123 := bstep (se 1 (by rfl) ⟨1668842, by rfl⟩ : syracuseStep 2225123 = 3337685) B3337685
theorem B1111043 : Blo 658307 1111043 := bstep (se 1 (by rfl) ⟨833282, by rfl⟩ : syracuseStep 1111043 = 1666565) B1666565
theorem B1111171 : Blo 658307 1111171 := bstep (se 1 (by rfl) ⟨833378, by rfl⟩ : syracuseStep 1111171 = 1666757) B1666757
theorem B5633165 : Blo 658307 5633165 := bstep (se 3 (by rfl) ⟨1056218, by rfl⟩ : syracuseStep 5633165 = 2112437) B2112437
theorem B5010659 : Blo 658307 5010659 := bstep (se 1 (by rfl) ⟨3757994, by rfl⟩ : syracuseStep 5010659 = 7515989) B7515989
theorem B2225393 : Blo 658307 2225393 := bstep (se 2 (by rfl) ⟨834522, by rfl⟩ : syracuseStep 2225393 = 1669045) B1669045
theorem B1111313 : Blo 658307 1111313 := bstep (se 2 (by rfl) ⟨416742, by rfl⟩ : syracuseStep 1111313 = 833485) B833485
theorem B1111441 : Blo 658307 1111441 := bstep (se 2 (by rfl) ⟨416790, by rfl⟩ : syracuseStep 1111441 = 833581) B833581
theorem B1111475 : Blo 658307 1111475 := bstep (se 1 (by rfl) ⟨833606, by rfl⟩ : syracuseStep 1111475 = 1667213) B1667213
theorem B1111603 : Blo 658307 1111603 := bstep (se 1 (by rfl) ⟨833702, by rfl⟩ : syracuseStep 1111603 = 1667405) B1667405
theorem B1668721 : Blo 658307 1668721 := bstep (se 2 (by rfl) ⟨625770, by rfl⟩ : syracuseStep 1668721 = 1251541) B1251541
theorem B3765923 : Blo 658307 3765923 := bstep (se 1 (by rfl) ⟨2824442, by rfl⟩ : syracuseStep 3765923 = 5648885) B5648885
theorem B3339953 : Blo 658307 3339953 := bstep (se 2 (by rfl) ⟨1252482, by rfl⟩ : syracuseStep 3339953 = 2504965) B2504965
theorem B1111745 : Blo 658307 1111745 := bstep (se 2 (by rfl) ⟨416904, by rfl⟩ : syracuseStep 1111745 = 833809) B833809
theorem B2225933 : Blo 658307 2225933 := bstep (se 3 (by rfl) ⟨417362, by rfl⟩ : syracuseStep 2225933 = 834725) B834725
theorem B1406737 : Blo 658307 1406737 := bstep (se 2 (by rfl) ⟨527526, by rfl⟩ : syracuseStep 1406737 = 1055053) B1055053
theorem B1111873 : Blo 658307 1111873 := bstep (se 2 (by rfl) ⟨416952, by rfl⟩ : syracuseStep 1111873 = 833905) B833905
theorem B2225987 : Blo 658307 2225987 := bstep (se 1 (by rfl) ⟨1669490, by rfl⟩ : syracuseStep 2225987 = 3338981) B3338981
theorem B1111907 : Blo 658307 1111907 := bstep (se 1 (by rfl) ⟨833930, by rfl⟩ : syracuseStep 1111907 = 1667861) B1667861
theorem B1668995 : Blo 658307 1668995 := bstep (se 1 (by rfl) ⟨1251746, by rfl⟩ : syracuseStep 1668995 = 2503493) B2503493
theorem B1112035 : Blo 658307 1112035 := bstep (se 1 (by rfl) ⟨834026, by rfl⟩ : syracuseStep 1112035 = 1668053) B1668053
theorem B1669187 : Blo 658307 1669187 := bstep (se 1 (by rfl) ⟨1251890, by rfl⟩ : syracuseStep 1669187 = 2503781) B2503781
theorem B2226257 : Blo 658307 2226257 := bstep (se 2 (by rfl) ⟨834846, by rfl⟩ : syracuseStep 2226257 = 1669693) B1669693
theorem B1112177 : Blo 658307 1112177 := bstep (se 2 (by rfl) ⟨417066, by rfl⟩ : syracuseStep 1112177 = 834133) B834133
theorem B1341571 : Blo 658307 1341571 := bstep (se 1 (by rfl) ⟨1006178, by rfl⟩ : syracuseStep 1341571 = 2012357) B2012357
theorem B3045539 : Blo 658307 3045539 := bstep (se 1 (by rfl) ⟨2284154, by rfl⟩ : syracuseStep 3045539 = 4568309) B4568309
theorem B1112305 : Blo 658307 1112305 := bstep (se 2 (by rfl) ⟨417114, by rfl⟩ : syracuseStep 1112305 = 834229) B834229
theorem B1112339 : Blo 658307 1112339 := bstep (se 1 (by rfl) ⟨834254, by rfl⟩ : syracuseStep 1112339 = 1668509) B1668509
theorem B1112467 : Blo 658307 1112467 := bstep (se 1 (by rfl) ⟨834350, by rfl⟩ : syracuseStep 1112467 = 1668701) B1668701
theorem B1407395 : Blo 658307 1407395 := bstep (se 1 (by rfl) ⟨1055546, by rfl⟩ : syracuseStep 1407395 = 2111093) B2111093
theorem B1112609 : Blo 658307 1112609 := bstep (se 2 (by rfl) ⟨417228, by rfl⟩ : syracuseStep 1112609 = 834457) B834457
theorem B2259533 : Blo 658307 2259533 := bstep (se 3 (by rfl) ⟨423662, by rfl⟩ : syracuseStep 2259533 = 847325) B847325
theorem B2226797 : Blo 658307 2226797 := bstep (se 3 (by rfl) ⟨417524, by rfl⟩ : syracuseStep 2226797 = 835049) B835049
theorem B3766925 : Blo 658307 3766925 := bstep (se 3 (by rfl) ⟨706298, by rfl⟩ : syracuseStep 3766925 = 1412597) B1412597
theorem B1112737 : Blo 658307 1112737 := bstep (se 2 (by rfl) ⟨417276, by rfl⟩ : syracuseStep 1112737 = 834553) B834553
theorem B2226851 : Blo 658307 2226851 := bstep (se 1 (by rfl) ⟨1670138, by rfl⟩ : syracuseStep 2226851 = 3340277) B3340277
theorem B1112771 : Blo 658307 1112771 := bstep (se 1 (by rfl) ⟨834578, by rfl⟩ : syracuseStep 1112771 = 1669157) B1669157
theorem B1112899 : Blo 658307 1112899 := bstep (se 1 (by rfl) ⟨834674, by rfl⟩ : syracuseStep 1112899 = 1669349) B1669349
theorem B1604483 : Blo 658307 1604483 := bstep (se 1 (by rfl) ⟨1203362, by rfl⟩ : syracuseStep 1604483 = 2406725) B2406725
theorem B2227121 : Blo 658307 2227121 := bstep (se 2 (by rfl) ⟨835170, by rfl⟩ : syracuseStep 2227121 = 1670341) B1670341
theorem B1113041 : Blo 658307 1113041 := bstep (se 2 (by rfl) ⟨417390, by rfl⟩ : syracuseStep 1113041 = 834781) B834781
theorem B1670129 : Blo 658307 1670129 := bstep (se 2 (by rfl) ⟨626298, by rfl⟩ : syracuseStep 1670129 = 1252597) B1252597
theorem B1670179 : Blo 658307 1670179 := bstep (se 1 (by rfl) ⟨1252634, by rfl⟩ : syracuseStep 1670179 = 2505269) B2505269
theorem B1113169 : Blo 658307 1113169 := bstep (se 2 (by rfl) ⟨417438, by rfl⟩ : syracuseStep 1113169 = 834877) B834877
theorem B3341411 : Blo 658307 3341411 := bstep (se 1 (by rfl) ⟨2506058, by rfl⟩ : syracuseStep 3341411 = 5012117) B5012117
theorem B1113203 : Blo 658307 1113203 := bstep (se 1 (by rfl) ⟨834902, by rfl⟩ : syracuseStep 1113203 = 1669805) B1669805
theorem B1670321 : Blo 658307 1670321 := bstep (se 2 (by rfl) ⟨626370, by rfl⟩ : syracuseStep 1670321 = 1252741) B1252741
theorem B2817251 : Blo 658307 2817251 := bstep (se 1 (by rfl) ⟨2112938, by rfl⟩ : syracuseStep 2817251 = 4225877) B4225877
theorem B1408241 : Blo 658307 1408241 := bstep (se 2 (by rfl) ⟨528090, by rfl⟩ : syracuseStep 1408241 = 1056181) B1056181
theorem B1113331 : Blo 658307 1113331 := bstep (se 1 (by rfl) ⟨834998, by rfl⟩ : syracuseStep 1113331 = 1669997) B1669997
theorem B1113473 : Blo 658307 1113473 := bstep (se 2 (by rfl) ⟨417552, by rfl⟩ : syracuseStep 1113473 = 835105) B835105
theorem B3571121 : Blo 658307 3571121 := bstep (se 2 (by rfl) ⟨1339170, by rfl⟩ : syracuseStep 3571121 = 2678341) B2678341
theorem B2227661 : Blo 658307 2227661 := bstep (se 3 (by rfl) ⟨417686, by rfl⟩ : syracuseStep 2227661 = 835373) B835373
theorem B1113601 : Blo 658307 1113601 := bstep (se 2 (by rfl) ⟨417600, by rfl⟩ : syracuseStep 1113601 = 835201) B835201
theorem B2227715 : Blo 658307 2227715 := bstep (se 1 (by rfl) ⟨1670786, by rfl⟩ : syracuseStep 2227715 = 3341573) B3341573
theorem B8453645 : Blo 658307 8453645 := bstep (se 3 (by rfl) ⟨1585058, by rfl⟩ : syracuseStep 8453645 = 3170117) B3170117
theorem B1113635 : Blo 658307 1113635 := bstep (se 1 (by rfl) ⟨835226, by rfl⟩ : syracuseStep 1113635 = 1670453) B1670453
theorem B1113763 : Blo 658307 1113763 := bstep (se 1 (by rfl) ⟨835322, by rfl⟩ : syracuseStep 1113763 = 1670645) B1670645
theorem B2227985 : Blo 658307 2227985 := bstep (se 2 (by rfl) ⟨835494, by rfl⟩ : syracuseStep 2227985 = 1670989) B1670989
theorem B1113905 : Blo 658307 1113905 := bstep (se 2 (by rfl) ⟨417714, by rfl⟩ : syracuseStep 1113905 = 835429) B835429
theorem B3342221 : Blo 658307 3342221 := bstep (se 3 (by rfl) ⟨626666, by rfl⟩ : syracuseStep 3342221 = 1253333) B1253333
theorem B1114033 : Blo 658307 1114033 := bstep (se 2 (by rfl) ⟨417762, by rfl⟩ : syracuseStep 1114033 = 835525) B835525
theorem B1114067 : Blo 658307 1114067 := bstep (se 1 (by rfl) ⟨835550, by rfl⟩ : syracuseStep 1114067 = 1671101) B1671101
theorem B1900525 : Blo 658307 1900525 := bstep (se 3 (by rfl) ⟨356348, by rfl⟩ : syracuseStep 1900525 = 712697) B712697
theorem B5636141 : Blo 658307 5636141 := bstep (se 3 (by rfl) ⟨1056776, by rfl⟩ : syracuseStep 5636141 = 2113553) B2113553
theorem B2228417 : Blo 658307 2228417 := bstep (se 2 (by rfl) ⟨835656, by rfl⟩ : syracuseStep 2228417 = 1671313) B1671313
theorem B1114391 : Blo 658307 1114391 := bstep (se 1 (by rfl) ⟨835793, by rfl⟩ : syracuseStep 1114391 = 1671587) B1671587
theorem B1671475 : Blo 658307 1671475 := bstep (se 1 (by rfl) ⟨1253606, by rfl⟩ : syracuseStep 1671475 = 2507213) B2507213
theorem B1114519 : Blo 658307 1114519 := bstep (se 1 (by rfl) ⟨835889, by rfl⟩ : syracuseStep 1114519 = 1671779) B1671779
theorem B1671617 : Blo 658307 1671617 := bstep (se 2 (by rfl) ⟨626856, by rfl⟩ : syracuseStep 1671617 = 1253713) B1253713
theorem B5014061 : Blo 658307 5014061 := bstep (se 3 (by rfl) ⟨940136, by rfl⟩ : syracuseStep 5014061 = 1880273) B1880273
theorem B13009501 : Blo 658307 13009501 := bstep (se 3 (by rfl) ⟨2439281, by rfl⟩ : syracuseStep 13009501 = 4878563) B4878563
theorem B2228957 : Blo 658307 2228957 := bstep (se 3 (by rfl) ⟨417929, by rfl⟩ : syracuseStep 2228957 = 835859) B835859
theorem B1508107 : Blo 658307 1508107 := bstep (se 1 (by rfl) ⟨1131080, by rfl⟩ : syracuseStep 1508107 = 2262161) B2262161
theorem B1409881 : Blo 658307 1409881 := bstep (se 2 (by rfl) ⟨528705, by rfl⟩ : syracuseStep 1409881 = 1057411) B1057411
theorem B1115147 : Blo 658307 1115147 := bstep (se 1 (by rfl) ⟨836360, by rfl⟩ : syracuseStep 1115147 = 1672721) B1672721
theorem B1410137 : Blo 658307 1410137 := bstep (se 2 (by rfl) ⟨528801, by rfl⟩ : syracuseStep 1410137 = 1057603) B1057603
theorem B1115275 : Blo 658307 1115275 := bstep (se 1 (by rfl) ⟨836456, by rfl⟩ : syracuseStep 1115275 = 1672913) B1672913
theorem B3769523 : Blo 658307 3769523 := bstep (se 1 (by rfl) ⟨2827142, by rfl⟩ : syracuseStep 3769523 = 5654285) B5654285
theorem B1115417 : Blo 658307 1115417 := bstep (se 2 (by rfl) ⟨418281, by rfl⟩ : syracuseStep 1115417 = 836563) B836563
theorem B1115545 : Blo 658307 1115545 := bstep (se 2 (by rfl) ⟨418329, by rfl⟩ : syracuseStep 1115545 = 836659) B836659
theorem B1410547 : Blo 658307 1410547 := bstep (se 1 (by rfl) ⟨1057910, by rfl⟩ : syracuseStep 1410547 = 2115821) B2115821
theorem B3344003 : Blo 658307 3344003 := bstep (se 1 (by rfl) ⟨2508002, by rfl⟩ : syracuseStep 3344003 = 5016005) B5016005
theorem B3016343 : Blo 658307 3016343 := bstep (se 1 (by rfl) ⟨2262257, by rfl⟩ : syracuseStep 3016343 = 4524515) B4524515
theorem B1607347 : Blo 658307 1607347 := bstep (se 1 (by rfl) ⟨1205510, by rfl⟩ : syracuseStep 1607347 = 2411021) B2411021
theorem B1672883 : Blo 658307 1672883 := bstep (se 1 (by rfl) ⟨1254662, by rfl⟩ : syracuseStep 1672883 = 2509325) B2509325
theorem B2819863 : Blo 658307 2819863 := bstep (se 1 (by rfl) ⟨2114897, by rfl⟩ : syracuseStep 2819863 = 4229795) B4229795
theorem B2230091 : Blo 658307 2230091 := bstep (se 1 (by rfl) ⟨1672568, by rfl⟩ : syracuseStep 2230091 = 3345137) B3345137
theorem B2819933 : Blo 658307 2819933 := bstep (se 3 (by rfl) ⟨528737, by rfl⟩ : syracuseStep 2819933 = 1057475) B1057475
theorem B1116119 : Blo 658307 1116119 := bstep (se 1 (by rfl) ⟨837089, by rfl⟩ : syracuseStep 1116119 = 1674179) B1674179
theorem B1116247 : Blo 658307 1116247 := bstep (se 1 (by rfl) ⟨837185, by rfl⟩ : syracuseStep 1116247 = 1674371) B1674371
theorem B2230361 : Blo 658307 2230361 := bstep (se 2 (by rfl) ⟨836385, by rfl⟩ : syracuseStep 2230361 = 1672771) B1672771
theorem B1411265 : Blo 658307 1411265 := bstep (se 2 (by rfl) ⟨529224, by rfl⟩ : syracuseStep 1411265 = 1058449) B1058449
theorem B1673419 : Blo 658307 1673419 := bstep (se 1 (by rfl) ⟨1255064, by rfl⟩ : syracuseStep 1673419 = 2510129) B2510129
theorem B6850861 : Blo 658307 6850861 := bstep (se 3 (by rfl) ⟨1284536, by rfl⟩ : syracuseStep 6850861 = 2569073) B2569073
theorem B1673561 : Blo 658307 1673561 := bstep (se 2 (by rfl) ⟨627585, by rfl⟩ : syracuseStep 1673561 = 1255171) B1255171
theorem B21760483 : Blo 658307 21760483 := bstep (se 1 (by rfl) ⟨16320362, by rfl⟩ : syracuseStep 21760483 = 32640725) B32640725
theorem B1411607 : Blo 658307 1411607 := bstep (se 1 (by rfl) ⟨1058705, by rfl⟩ : syracuseStep 1411607 = 2117411) B2117411
theorem B2820683 : Blo 658307 2820683 := bstep (se 1 (by rfl) ⟨2115512, by rfl⟩ : syracuseStep 2820683 = 4231025) B4231025
theorem B3770981 : Blo 658307 3770981 := bstep (se 4 (by rfl) ⟨353529, by rfl⟩ : syracuseStep 3770981 = 707059) B707059
theorem B1411777 : Blo 658307 1411777 := bstep (se 2 (by rfl) ⟨529416, by rfl⟩ : syracuseStep 1411777 = 1058833) B1058833
theorem B1116875 : Blo 658307 1116875 := bstep (se 1 (by rfl) ⟨837656, by rfl⟩ : syracuseStep 1116875 = 1675313) B1675313
theorem B2231063 : Blo 658307 2231063 := bstep (se 1 (by rfl) ⟨1673297, by rfl⟩ : syracuseStep 2231063 = 3346595) B3346595
theorem B2263859 : Blo 658307 2263859 := bstep (se 1 (by rfl) ⟨1697894, by rfl⟩ : syracuseStep 2263859 = 3395789) B3395789
theorem B1117003 : Blo 658307 1117003 := bstep (se 1 (by rfl) ⟨837752, by rfl⟩ : syracuseStep 1117003 = 1675505) B1675505
theorem B658315 : Blo 658307 658315 := bstep (se 1 (by rfl) ⟨493736, by rfl⟩ : syracuseStep 658315 = 987473) B987473
theorem B658327 : Blo 658307 658327 := bstep (se 1 (by rfl) ⟨493745, by rfl⟩ : syracuseStep 658327 = 987491) B987491
theorem B658347 : Blo 658307 658347 := bstep (se 1 (by rfl) ⟨493760, by rfl⟩ : syracuseStep 658347 = 987521) B987521
theorem B2853805 : Blo 658307 2853805 := bstep (se 3 (by rfl) ⟨535088, by rfl⟩ : syracuseStep 2853805 = 1070177) B1070177
theorem B13536179 : Blo 658307 13536179 := bstep (se 1 (by rfl) ⟨10152134, by rfl⟩ : syracuseStep 13536179 = 20304269) B20304269
theorem B658359 : Blo 658307 658359 := bstep (se 1 (by rfl) ⟨493769, by rfl⟩ : syracuseStep 658359 = 987539) B987539
theorem B658379 : Blo 658307 658379 := bstep (se 1 (by rfl) ⟨493784, by rfl⟩ : syracuseStep 658379 = 987569) B987569
theorem B658391 : Blo 658307 658391 := bstep (se 1 (by rfl) ⟨493793, by rfl⟩ : syracuseStep 658391 = 987587) B987587
theorem B1117145 : Blo 658307 1117145 := bstep (se 2 (by rfl) ⟨418929, by rfl⟩ : syracuseStep 1117145 = 837859) B837859
theorem B658411 : Blo 658307 658411 := bstep (se 1 (by rfl) ⟨493808, by rfl⟩ : syracuseStep 658411 = 987617) B987617
theorem B658423 : Blo 658307 658423 := bstep (se 1 (by rfl) ⟨493817, by rfl⟩ : syracuseStep 658423 = 987635) B987635
theorem B658443 : Blo 658307 658443 := bstep (se 1 (by rfl) ⟨493832, by rfl⟩ : syracuseStep 658443 = 987665) B987665
theorem B658455 : Blo 658307 658455 := bstep (se 1 (by rfl) ⟨493841, by rfl⟩ : syracuseStep 658455 = 987683) B987683
theorem B658475 : Blo 658307 658475 := bstep (se 1 (by rfl) ⟨493856, by rfl⟩ : syracuseStep 658475 = 987713) B987713
theorem B658487 : Blo 658307 658487 := bstep (se 1 (by rfl) ⟨493865, by rfl⟩ : syracuseStep 658487 = 987731) B987731
theorem B658507 : Blo 658307 658507 := bstep (se 1 (by rfl) ⟨493880, by rfl⟩ : syracuseStep 658507 = 987761) B987761
theorem B658519 : Blo 658307 658519 := bstep (se 1 (by rfl) ⟨493889, by rfl⟩ : syracuseStep 658519 = 987779) B987779
theorem B1117273 : Blo 658307 1117273 := bstep (se 2 (by rfl) ⟨418977, by rfl⟩ : syracuseStep 1117273 = 837955) B837955
theorem B658539 : Blo 658307 658539 := bstep (se 1 (by rfl) ⟨493904, by rfl⟩ : syracuseStep 658539 = 987809) B987809
theorem B658551 : Blo 658307 658551 := bstep (se 1 (by rfl) ⟨493913, by rfl⟩ : syracuseStep 658551 = 987827) B987827
theorem B658571 : Blo 658307 658571 := bstep (se 1 (by rfl) ⟨493928, by rfl⟩ : syracuseStep 658571 = 987857) B987857
theorem B658583 : Blo 658307 658583 := bstep (se 1 (by rfl) ⟨493937, by rfl⟩ : syracuseStep 658583 = 987875) B987875
theorem B1674391 : Blo 658307 1674391 := bstep (se 1 (by rfl) ⟨1255793, by rfl⟩ : syracuseStep 1674391 = 2511587) B2511587
theorem B658603 : Blo 658307 658603 := bstep (se 1 (by rfl) ⟨493952, by rfl⟩ : syracuseStep 658603 = 987905) B987905
theorem B658615 : Blo 658307 658615 := bstep (se 1 (by rfl) ⟨493961, by rfl⟩ : syracuseStep 658615 = 987923) B987923
theorem B658635 : Blo 658307 658635 := bstep (se 1 (by rfl) ⟨493976, by rfl⟩ : syracuseStep 658635 = 987953) B987953
theorem B658647 : Blo 658307 658647 := bstep (se 1 (by rfl) ⟨493985, by rfl⟩ : syracuseStep 658647 = 987971) B987971
theorem B658667 : Blo 658307 658667 := bstep (se 1 (by rfl) ⟨494000, by rfl⟩ : syracuseStep 658667 = 988001) B988001
theorem B658679 : Blo 658307 658679 := bstep (se 1 (by rfl) ⟨494009, by rfl⟩ : syracuseStep 658679 = 988019) B988019
theorem B658699 : Blo 658307 658699 := bstep (se 1 (by rfl) ⟨494024, by rfl⟩ : syracuseStep 658699 = 988049) B988049
theorem B658711 : Blo 658307 658711 := bstep (se 1 (by rfl) ⟨494033, by rfl⟩ : syracuseStep 658711 = 988067) B988067
theorem B658731 : Blo 658307 658731 := bstep (se 1 (by rfl) ⟨494048, by rfl⟩ : syracuseStep 658731 = 988097) B988097
theorem B2231603 : Blo 658307 2231603 := bstep (se 1 (by rfl) ⟨1673702, by rfl⟩ : syracuseStep 2231603 = 3347405) B3347405
theorem B658743 : Blo 658307 658743 := bstep (se 1 (by rfl) ⟨494057, by rfl⟩ : syracuseStep 658743 = 988115) B988115
theorem B658763 : Blo 658307 658763 := bstep (se 1 (by rfl) ⟨494072, by rfl⟩ : syracuseStep 658763 = 988145) B988145
theorem B658775 : Blo 658307 658775 := bstep (se 1 (by rfl) ⟨494081, by rfl⟩ : syracuseStep 658775 = 988163) B988163
theorem B658795 : Blo 658307 658795 := bstep (se 1 (by rfl) ⟨494096, by rfl⟩ : syracuseStep 658795 = 988193) B988193
theorem B658807 : Blo 658307 658807 := bstep (se 1 (by rfl) ⟨494105, by rfl⟩ : syracuseStep 658807 = 988211) B988211
theorem B658827 : Blo 658307 658827 := bstep (se 1 (by rfl) ⟨494120, by rfl⟩ : syracuseStep 658827 = 988241) B988241
theorem B658839 : Blo 658307 658839 := bstep (se 1 (by rfl) ⟨494129, by rfl⟩ : syracuseStep 658839 = 988259) B988259
theorem B658859 : Blo 658307 658859 := bstep (se 1 (by rfl) ⟨494144, by rfl⟩ : syracuseStep 658859 = 988289) B988289
theorem B658871 : Blo 658307 658871 := bstep (se 1 (by rfl) ⟨494153, by rfl⟩ : syracuseStep 658871 = 988307) B988307
theorem B658891 : Blo 658307 658891 := bstep (se 1 (by rfl) ⟨494168, by rfl⟩ : syracuseStep 658891 = 988337) B988337
theorem B1609163 : Blo 658307 1609163 := bstep (se 1 (by rfl) ⟨1206872, by rfl⟩ : syracuseStep 1609163 = 2413745) B2413745
theorem B658903 : Blo 658307 658903 := bstep (se 1 (by rfl) ⟨494177, by rfl⟩ : syracuseStep 658903 = 988355) B988355
theorem B658923 : Blo 658307 658923 := bstep (se 1 (by rfl) ⟨494192, by rfl⟩ : syracuseStep 658923 = 988385) B988385
theorem B658935 : Blo 658307 658935 := bstep (se 1 (by rfl) ⟨494201, by rfl⟩ : syracuseStep 658935 = 988403) B988403
theorem B658955 : Blo 658307 658955 := bstep (se 1 (by rfl) ⟨494216, by rfl⟩ : syracuseStep 658955 = 988433) B988433
theorem B658967 : Blo 658307 658967 := bstep (se 1 (by rfl) ⟨494225, by rfl⟩ : syracuseStep 658967 = 988451) B988451
theorem B658987 : Blo 658307 658987 := bstep (se 1 (by rfl) ⟨494240, by rfl⟩ : syracuseStep 658987 = 988481) B988481
theorem B658999 : Blo 658307 658999 := bstep (se 1 (by rfl) ⟨494249, by rfl⟩ : syracuseStep 658999 = 988499) B988499
theorem B2231873 : Blo 658307 2231873 := bstep (se 2 (by rfl) ⟨836952, by rfl⟩ : syracuseStep 2231873 = 1673905) B1673905
theorem B659019 : Blo 658307 659019 := bstep (se 1 (by rfl) ⟨494264, by rfl⟩ : syracuseStep 659019 = 988529) B988529
theorem B1674827 : Blo 658307 1674827 := bstep (se 1 (by rfl) ⟨1256120, by rfl⟩ : syracuseStep 1674827 = 2512241) B2512241
theorem B659031 : Blo 658307 659031 := bstep (se 1 (by rfl) ⟨494273, by rfl⟩ : syracuseStep 659031 = 988547) B988547
theorem B659051 : Blo 658307 659051 := bstep (se 1 (by rfl) ⟨494288, by rfl⟩ : syracuseStep 659051 = 988577) B988577
theorem B659063 : Blo 658307 659063 := bstep (se 1 (by rfl) ⟨494297, by rfl⟩ : syracuseStep 659063 = 988595) B988595
theorem B659083 : Blo 658307 659083 := bstep (se 1 (by rfl) ⟨494312, by rfl⟩ : syracuseStep 659083 = 988625) B988625
theorem B659095 : Blo 658307 659095 := bstep (se 1 (by rfl) ⟨494321, by rfl⟩ : syracuseStep 659095 = 988643) B988643
theorem B659115 : Blo 658307 659115 := bstep (se 1 (by rfl) ⟨494336, by rfl⟩ : syracuseStep 659115 = 988673) B988673
theorem B659127 : Blo 658307 659127 := bstep (se 1 (by rfl) ⟨494345, by rfl⟩ : syracuseStep 659127 = 988691) B988691
theorem B659147 : Blo 658307 659147 := bstep (se 1 (by rfl) ⟨494360, by rfl⟩ : syracuseStep 659147 = 988721) B988721
theorem B659159 : Blo 658307 659159 := bstep (se 1 (by rfl) ⟨494369, by rfl⟩ : syracuseStep 659159 = 988739) B988739
theorem B659179 : Blo 658307 659179 := bstep (se 1 (by rfl) ⟨494384, by rfl⟩ : syracuseStep 659179 = 988769) B988769
theorem B659191 : Blo 658307 659191 := bstep (se 1 (by rfl) ⟨494393, by rfl⟩ : syracuseStep 659191 = 988787) B988787
theorem B659211 : Blo 658307 659211 := bstep (se 1 (by rfl) ⟨494408, by rfl⟩ : syracuseStep 659211 = 988817) B988817
theorem B2854673 : Blo 658307 2854673 := bstep (se 2 (by rfl) ⟨1070502, by rfl⟩ : syracuseStep 2854673 = 2141005) B2141005
theorem B659223 : Blo 658307 659223 := bstep (se 1 (by rfl) ⟨494417, by rfl⟩ : syracuseStep 659223 = 988835) B988835
theorem B659243 : Blo 658307 659243 := bstep (se 1 (by rfl) ⟨494432, by rfl⟩ : syracuseStep 659243 = 988865) B988865
theorem B659255 : Blo 658307 659255 := bstep (se 1 (by rfl) ⟨494441, by rfl⟩ : syracuseStep 659255 = 988883) B988883
theorem B659275 : Blo 658307 659275 := bstep (se 1 (by rfl) ⟨494456, by rfl⟩ : syracuseStep 659275 = 988913) B988913
theorem B1412939 : Blo 658307 1412939 := bstep (se 1 (by rfl) ⟨1059704, by rfl⟩ : syracuseStep 1412939 = 2119409) B2119409
theorem B659287 : Blo 658307 659287 := bstep (se 1 (by rfl) ⟨494465, by rfl⟩ : syracuseStep 659287 = 988931) B988931
theorem B659307 : Blo 658307 659307 := bstep (se 1 (by rfl) ⟨494480, by rfl⟩ : syracuseStep 659307 = 988961) B988961
theorem B659319 : Blo 658307 659319 := bstep (se 1 (by rfl) ⟨494489, by rfl⟩ : syracuseStep 659319 = 988979) B988979
theorem B659339 : Blo 658307 659339 := bstep (se 1 (by rfl) ⟨494504, by rfl⟩ : syracuseStep 659339 = 989009) B989009
theorem B659351 : Blo 658307 659351 := bstep (se 1 (by rfl) ⟨494513, by rfl⟩ : syracuseStep 659351 = 989027) B989027
theorem B659371 : Blo 658307 659371 := bstep (se 1 (by rfl) ⟨494528, by rfl⟩ : syracuseStep 659371 = 989057) B989057
theorem B659383 : Blo 658307 659383 := bstep (se 1 (by rfl) ⟨494537, by rfl⟩ : syracuseStep 659383 = 989075) B989075
theorem B1675201 : Blo 658307 1675201 := bstep (se 2 (by rfl) ⟨628200, by rfl⟩ : syracuseStep 1675201 = 1256401) B1256401
theorem B659403 : Blo 658307 659403 := bstep (se 1 (by rfl) ⟨494552, by rfl⟩ : syracuseStep 659403 = 989105) B989105
theorem B659415 : Blo 658307 659415 := bstep (se 1 (by rfl) ⟨494561, by rfl⟩ : syracuseStep 659415 = 989123) B989123
theorem B659435 : Blo 658307 659435 := bstep (se 1 (by rfl) ⟨494576, by rfl⟩ : syracuseStep 659435 = 989153) B989153
theorem B659447 : Blo 658307 659447 := bstep (se 1 (by rfl) ⟨494585, by rfl⟩ : syracuseStep 659447 = 989171) B989171
theorem B659467 : Blo 658307 659467 := bstep (se 1 (by rfl) ⟨494600, by rfl⟩ : syracuseStep 659467 = 989201) B989201
theorem B659479 : Blo 658307 659479 := bstep (se 1 (by rfl) ⟨494609, by rfl⟩ : syracuseStep 659479 = 989219) B989219
theorem B659499 : Blo 658307 659499 := bstep (se 1 (by rfl) ⟨494624, by rfl⟩ : syracuseStep 659499 = 989249) B989249
theorem B659511 : Blo 658307 659511 := bstep (se 1 (by rfl) ⟨494633, by rfl⟩ : syracuseStep 659511 = 989267) B989267
theorem B659531 : Blo 658307 659531 := bstep (se 1 (by rfl) ⟨494648, by rfl⟩ : syracuseStep 659531 = 989297) B989297
theorem B659543 : Blo 658307 659543 := bstep (se 1 (by rfl) ⟨494657, by rfl⟩ : syracuseStep 659543 = 989315) B989315
theorem B2232413 : Blo 658307 2232413 := bstep (se 3 (by rfl) ⟨418577, by rfl⟩ : syracuseStep 2232413 = 837155) B837155
theorem B659563 : Blo 658307 659563 := bstep (se 1 (by rfl) ⟨494672, by rfl⟩ : syracuseStep 659563 = 989345) B989345
theorem B659575 : Blo 658307 659575 := bstep (se 1 (by rfl) ⟨494681, by rfl⟩ : syracuseStep 659575 = 989363) B989363
theorem B659595 : Blo 658307 659595 := bstep (se 1 (by rfl) ⟨494696, by rfl⟩ : syracuseStep 659595 = 989393) B989393
theorem B659607 : Blo 658307 659607 := bstep (se 1 (by rfl) ⟨494705, by rfl⟩ : syracuseStep 659607 = 989411) B989411
theorem B659627 : Blo 658307 659627 := bstep (se 1 (by rfl) ⟨494720, by rfl⟩ : syracuseStep 659627 = 989441) B989441
theorem B3575987 : Blo 658307 3575987 := bstep (se 1 (by rfl) ⟨2681990, by rfl⟩ : syracuseStep 3575987 = 5363981) B5363981
theorem B659639 : Blo 658307 659639 := bstep (se 1 (by rfl) ⟨494729, by rfl⟩ : syracuseStep 659639 = 989459) B989459
theorem B659659 : Blo 658307 659659 := bstep (se 1 (by rfl) ⟨494744, by rfl⟩ : syracuseStep 659659 = 989489) B989489
theorem B659671 : Blo 658307 659671 := bstep (se 1 (by rfl) ⟨494753, by rfl⟩ : syracuseStep 659671 = 989507) B989507
theorem B659691 : Blo 658307 659691 := bstep (se 1 (by rfl) ⟨494768, by rfl⟩ : syracuseStep 659691 = 989537) B989537
theorem B659703 : Blo 658307 659703 := bstep (se 1 (by rfl) ⟨494777, by rfl⟩ : syracuseStep 659703 = 989555) B989555
theorem B659723 : Blo 658307 659723 := bstep (se 1 (by rfl) ⟨494792, by rfl⟩ : syracuseStep 659723 = 989585) B989585
theorem B659735 : Blo 658307 659735 := bstep (se 1 (by rfl) ⟨494801, by rfl⟩ : syracuseStep 659735 = 989603) B989603
theorem B659755 : Blo 658307 659755 := bstep (se 1 (by rfl) ⟨494816, by rfl⟩ : syracuseStep 659755 = 989633) B989633
theorem B659767 : Blo 658307 659767 := bstep (se 1 (by rfl) ⟨494825, by rfl⟩ : syracuseStep 659767 = 989651) B989651
theorem B987467 : Blo 658307 987467 := bstep (se 1 (by rfl) ⟨740600, by rfl⟩ : syracuseStep 987467 = 1481201) B1481201
theorem B659787 : Blo 658307 659787 := bstep (se 1 (by rfl) ⟨494840, by rfl⟩ : syracuseStep 659787 = 989681) B989681
theorem B987479 : Blo 658307 987479 := bstep (se 1 (by rfl) ⟨740609, by rfl⟩ : syracuseStep 987479 = 1481219) B1481219
theorem B659799 : Blo 658307 659799 := bstep (se 1 (by rfl) ⟨494849, by rfl⟩ : syracuseStep 659799 = 989699) B989699
theorem B5017949 : Blo 658307 5017949 := bstep (se 3 (by rfl) ⟨940865, by rfl⟩ : syracuseStep 5017949 = 1881731) B1881731
theorem B659819 : Blo 658307 659819 := bstep (se 1 (by rfl) ⟨494864, by rfl⟩ : syracuseStep 659819 = 989729) B989729
theorem B659831 : Blo 658307 659831 := bstep (se 1 (by rfl) ⟨494873, by rfl⟩ : syracuseStep 659831 = 989747) B989747
theorem B3019139 : Blo 658307 3019139 := bstep (se 1 (by rfl) ⟨2264354, by rfl⟩ : syracuseStep 3019139 = 4528709) B4528709
theorem B659851 : Blo 658307 659851 := bstep (se 1 (by rfl) ⟨494888, by rfl⟩ : syracuseStep 659851 = 989777) B989777
theorem B659863 : Blo 658307 659863 := bstep (se 1 (by rfl) ⟨494897, by rfl⟩ : syracuseStep 659863 = 989795) B989795
theorem B987545 : Blo 658307 987545 := bstep (se 2 (by rfl) ⟨370329, by rfl⟩ : syracuseStep 987545 = 740659) B740659
theorem B659883 : Blo 658307 659883 := bstep (se 1 (by rfl) ⟨494912, by rfl⟩ : syracuseStep 659883 = 989825) B989825
theorem B659895 : Blo 658307 659895 := bstep (se 1 (by rfl) ⟨494921, by rfl⟩ : syracuseStep 659895 = 989843) B989843
theorem B659915 : Blo 658307 659915 := bstep (se 1 (by rfl) ⟨494936, by rfl⟩ : syracuseStep 659915 = 989873) B989873
theorem B659927 : Blo 658307 659927 := bstep (se 1 (by rfl) ⟨494945, by rfl⟩ : syracuseStep 659927 = 989891) B989891
theorem B659947 : Blo 658307 659947 := bstep (se 1 (by rfl) ⟨494960, by rfl⟩ : syracuseStep 659947 = 989921) B989921
theorem B659959 : Blo 658307 659959 := bstep (se 1 (by rfl) ⟨494969, by rfl⟩ : syracuseStep 659959 = 989939) B989939
theorem B987659 : Blo 658307 987659 := bstep (se 1 (by rfl) ⟨740744, by rfl⟩ : syracuseStep 987659 = 1481489) B1481489
theorem B659979 : Blo 658307 659979 := bstep (se 1 (by rfl) ⟨494984, by rfl⟩ : syracuseStep 659979 = 989969) B989969
theorem B8458769 : Blo 658307 8458769 := bstep (se 2 (by rfl) ⟨3172038, by rfl⟩ : syracuseStep 8458769 = 6344077) B6344077
theorem B987671 : Blo 658307 987671 := bstep (se 1 (by rfl) ⟨740753, by rfl⟩ : syracuseStep 987671 = 1481507) B1481507
theorem B659991 : Blo 658307 659991 := bstep (se 1 (by rfl) ⟨494993, by rfl⟩ : syracuseStep 659991 = 989987) B989987
theorem B1675799 : Blo 658307 1675799 := bstep (se 1 (by rfl) ⟨1256849, by rfl⟩ : syracuseStep 1675799 = 2513699) B2513699
theorem B660011 : Blo 658307 660011 := bstep (se 1 (by rfl) ⟨495008, by rfl⟩ : syracuseStep 660011 = 990017) B990017
theorem B1413683 : Blo 658307 1413683 := bstep (se 1 (by rfl) ⟨1060262, by rfl⟩ : syracuseStep 1413683 = 2120525) B2120525
theorem B660023 : Blo 658307 660023 := bstep (se 1 (by rfl) ⟨495017, by rfl⟩ : syracuseStep 660023 = 990035) B990035
theorem B660043 : Blo 658307 660043 := bstep (se 1 (by rfl) ⟨495032, by rfl⟩ : syracuseStep 660043 = 990065) B990065
theorem B660055 : Blo 658307 660055 := bstep (se 1 (by rfl) ⟨495041, by rfl⟩ : syracuseStep 660055 = 990083) B990083
theorem B987737 : Blo 658307 987737 := bstep (se 2 (by rfl) ⟨370401, by rfl⟩ : syracuseStep 987737 = 740803) B740803
theorem B660075 : Blo 658307 660075 := bstep (se 1 (by rfl) ⟨495056, by rfl⟩ : syracuseStep 660075 = 990113) B990113
theorem B660087 : Blo 658307 660087 := bstep (se 1 (by rfl) ⟨495065, by rfl⟩ : syracuseStep 660087 = 990131) B990131
theorem B1249931 : Blo 658307 1249931 := bstep (se 1 (by rfl) ⟨937448, by rfl⟩ : syracuseStep 1249931 = 1874897) B1874897
theorem B660107 : Blo 658307 660107 := bstep (se 1 (by rfl) ⟨495080, by rfl⟩ : syracuseStep 660107 = 990161) B990161
theorem B660119 : Blo 658307 660119 := bstep (se 1 (by rfl) ⟨495089, by rfl⟩ : syracuseStep 660119 = 990179) B990179
theorem B660139 : Blo 658307 660139 := bstep (se 1 (by rfl) ⟨495104, by rfl⟩ : syracuseStep 660139 = 990209) B990209
theorem B660151 : Blo 658307 660151 := bstep (se 1 (by rfl) ⟨495113, by rfl⟩ : syracuseStep 660151 = 990227) B990227
theorem B1249985 : Blo 658307 1249985 := bstep (se 2 (by rfl) ⟨468744, by rfl⟩ : syracuseStep 1249985 = 937489) B937489
theorem B987851 : Blo 658307 987851 := bstep (se 1 (by rfl) ⟨740888, by rfl⟩ : syracuseStep 987851 = 1481777) B1481777
theorem B660171 : Blo 658307 660171 := bstep (se 1 (by rfl) ⟨495128, by rfl⟩ : syracuseStep 660171 = 990257) B990257
theorem B987863 : Blo 658307 987863 := bstep (se 1 (by rfl) ⟨740897, by rfl⟩ : syracuseStep 987863 = 1481795) B1481795
theorem B660183 : Blo 658307 660183 := bstep (se 1 (by rfl) ⟨495137, by rfl⟩ : syracuseStep 660183 = 990275) B990275
theorem B660203 : Blo 658307 660203 := bstep (se 1 (by rfl) ⟨495152, by rfl⟩ : syracuseStep 660203 = 990305) B990305
theorem B660215 : Blo 658307 660215 := bstep (se 1 (by rfl) ⟨495161, by rfl⟩ : syracuseStep 660215 = 990323) B990323
theorem B660235 : Blo 658307 660235 := bstep (se 1 (by rfl) ⟨495176, by rfl⟩ : syracuseStep 660235 = 990353) B990353
theorem B660247 : Blo 658307 660247 := bstep (se 1 (by rfl) ⟨495185, by rfl⟩ : syracuseStep 660247 = 990371) B990371
theorem B987929 : Blo 658307 987929 := bstep (se 2 (by rfl) ⟨370473, by rfl⟩ : syracuseStep 987929 = 740947) B740947
theorem B660267 : Blo 658307 660267 := bstep (se 1 (by rfl) ⟨495200, by rfl⟩ : syracuseStep 660267 = 990401) B990401
theorem B660279 : Blo 658307 660279 := bstep (se 1 (by rfl) ⟨495209, by rfl⟩ : syracuseStep 660279 = 990419) B990419
theorem B660299 : Blo 658307 660299 := bstep (se 1 (by rfl) ⟨495224, by rfl⟩ : syracuseStep 660299 = 990449) B990449
theorem B660311 : Blo 658307 660311 := bstep (se 1 (by rfl) ⟨495233, by rfl⟩ : syracuseStep 660311 = 990467) B990467
theorem B660331 : Blo 658307 660331 := bstep (se 1 (by rfl) ⟨495248, by rfl⟩ : syracuseStep 660331 = 990497) B990497
theorem B660343 : Blo 658307 660343 := bstep (se 1 (by rfl) ⟨495257, by rfl⟩ : syracuseStep 660343 = 990515) B990515
theorem B988043 : Blo 658307 988043 := bstep (se 1 (by rfl) ⟨741032, by rfl⟩ : syracuseStep 988043 = 1482065) B1482065
theorem B660363 : Blo 658307 660363 := bstep (se 1 (by rfl) ⟨495272, by rfl⟩ : syracuseStep 660363 = 990545) B990545
theorem B988055 : Blo 658307 988055 := bstep (se 1 (by rfl) ⟨741041, by rfl⟩ : syracuseStep 988055 = 1482083) B1482083
theorem B660375 : Blo 658307 660375 := bstep (se 1 (by rfl) ⟨495281, by rfl⟩ : syracuseStep 660375 = 990563) B990563
theorem B660395 : Blo 658307 660395 := bstep (se 1 (by rfl) ⟨495296, by rfl⟩ : syracuseStep 660395 = 990593) B990593
theorem B660407 : Blo 658307 660407 := bstep (se 1 (by rfl) ⟨495305, by rfl⟩ : syracuseStep 660407 = 990611) B990611
theorem B660427 : Blo 658307 660427 := bstep (se 1 (by rfl) ⟨495320, by rfl⟩ : syracuseStep 660427 = 990641) B990641
theorem B660439 : Blo 658307 660439 := bstep (se 1 (by rfl) ⟨495329, by rfl⟩ : syracuseStep 660439 = 990659) B990659
theorem B988121 : Blo 658307 988121 := bstep (se 2 (by rfl) ⟨370545, by rfl⟩ : syracuseStep 988121 = 741091) B741091
theorem B660459 : Blo 658307 660459 := bstep (se 1 (by rfl) ⟨495344, by rfl⟩ : syracuseStep 660459 = 990689) B990689
theorem B660471 : Blo 658307 660471 := bstep (se 1 (by rfl) ⟨495353, by rfl⟩ : syracuseStep 660471 = 990707) B990707
theorem B660491 : Blo 658307 660491 := bstep (se 1 (by rfl) ⟨495368, by rfl⟩ : syracuseStep 660491 = 990737) B990737
theorem B660503 : Blo 658307 660503 := bstep (se 1 (by rfl) ⟨495377, by rfl⟩ : syracuseStep 660503 = 990755) B990755
theorem B660523 : Blo 658307 660523 := bstep (se 1 (by rfl) ⟨495392, by rfl⟩ : syracuseStep 660523 = 990785) B990785
theorem B660535 : Blo 658307 660535 := bstep (se 1 (by rfl) ⟨495401, by rfl⟩ : syracuseStep 660535 = 990803) B990803
theorem B988235 : Blo 658307 988235 := bstep (se 1 (by rfl) ⟨741176, by rfl⟩ : syracuseStep 988235 = 1482353) B1482353
theorem B660555 : Blo 658307 660555 := bstep (se 1 (by rfl) ⟨495416, by rfl⟩ : syracuseStep 660555 = 990833) B990833
theorem B988247 : Blo 658307 988247 := bstep (se 1 (by rfl) ⟨741185, by rfl⟩ : syracuseStep 988247 = 1482371) B1482371
theorem B660567 : Blo 658307 660567 := bstep (se 1 (by rfl) ⟨495425, by rfl⟩ : syracuseStep 660567 = 990851) B990851
theorem B660587 : Blo 658307 660587 := bstep (se 1 (by rfl) ⟨495440, by rfl⟩ : syracuseStep 660587 = 990881) B990881
theorem B660599 : Blo 658307 660599 := bstep (se 1 (by rfl) ⟨495449, by rfl⟩ : syracuseStep 660599 = 990899) B990899
theorem B660619 : Blo 658307 660619 := bstep (se 1 (by rfl) ⟨495464, by rfl⟩ : syracuseStep 660619 = 990929) B990929
theorem B660631 : Blo 658307 660631 := bstep (se 1 (by rfl) ⟨495473, by rfl⟩ : syracuseStep 660631 = 990947) B990947
theorem B988313 : Blo 658307 988313 := bstep (se 2 (by rfl) ⟨370617, by rfl⟩ : syracuseStep 988313 = 741235) B741235
theorem B660651 : Blo 658307 660651 := bstep (se 1 (by rfl) ⟨495488, by rfl⟩ : syracuseStep 660651 = 990977) B990977
theorem B660663 : Blo 658307 660663 := bstep (se 1 (by rfl) ⟨495497, by rfl⟩ : syracuseStep 660663 = 990995) B990995
theorem B660683 : Blo 658307 660683 := bstep (se 1 (by rfl) ⟨495512, by rfl⟩ : syracuseStep 660683 = 991025) B991025
theorem B2233547 : Blo 658307 2233547 := bstep (se 1 (by rfl) ⟨1675160, by rfl⟩ : syracuseStep 2233547 = 3350321) B3350321
theorem B660695 : Blo 658307 660695 := bstep (se 1 (by rfl) ⟨495521, by rfl⟩ : syracuseStep 660695 = 991043) B991043
theorem B660715 : Blo 658307 660715 := bstep (se 1 (by rfl) ⟨495536, by rfl⟩ : syracuseStep 660715 = 991073) B991073
theorem B660727 : Blo 658307 660727 := bstep (se 1 (by rfl) ⟨495545, by rfl⟩ : syracuseStep 660727 = 991091) B991091
theorem B988427 : Blo 658307 988427 := bstep (se 1 (by rfl) ⟨741320, by rfl⟩ : syracuseStep 988427 = 1482641) B1482641
theorem B660747 : Blo 658307 660747 := bstep (se 1 (by rfl) ⟨495560, by rfl⟩ : syracuseStep 660747 = 991121) B991121
theorem B3347729 : Blo 658307 3347729 := bstep (se 2 (by rfl) ⟨1255398, by rfl⟩ : syracuseStep 3347729 = 2510797) B2510797
theorem B988439 : Blo 658307 988439 := bstep (se 1 (by rfl) ⟨741329, by rfl⟩ : syracuseStep 988439 = 1482659) B1482659
theorem B660759 : Blo 658307 660759 := bstep (se 1 (by rfl) ⟨495569, by rfl⟩ : syracuseStep 660759 = 991139) B991139
theorem B660779 : Blo 658307 660779 := bstep (se 1 (by rfl) ⟨495584, by rfl⟩ : syracuseStep 660779 = 991169) B991169
theorem B660791 : Blo 658307 660791 := bstep (se 1 (by rfl) ⟨495593, by rfl⟩ : syracuseStep 660791 = 991187) B991187
theorem B4232513 : Blo 658307 4232513 := bstep (se 2 (by rfl) ⟨1587192, by rfl⟩ : syracuseStep 4232513 = 3174385) B3174385
theorem B660811 : Blo 658307 660811 := bstep (se 1 (by rfl) ⟨495608, by rfl⟩ : syracuseStep 660811 = 991217) B991217
theorem B6034763 : Blo 658307 6034763 := bstep (se 1 (by rfl) ⟨4526072, by rfl⟩ : syracuseStep 6034763 = 9052145) B9052145
theorem B660823 : Blo 658307 660823 := bstep (se 1 (by rfl) ⟨495617, by rfl⟩ : syracuseStep 660823 = 991235) B991235
theorem B988505 : Blo 658307 988505 := bstep (se 2 (by rfl) ⟨370689, by rfl⟩ : syracuseStep 988505 = 741379) B741379
theorem B660843 : Blo 658307 660843 := bstep (se 1 (by rfl) ⟨495632, by rfl⟩ : syracuseStep 660843 = 991265) B991265
theorem B660855 : Blo 658307 660855 := bstep (se 1 (by rfl) ⟨495641, by rfl⟩ : syracuseStep 660855 = 991283) B991283
theorem B660875 : Blo 658307 660875 := bstep (se 1 (by rfl) ⟨495656, by rfl⟩ : syracuseStep 660875 = 991313) B991313
theorem B660887 : Blo 658307 660887 := bstep (se 1 (by rfl) ⟨495665, by rfl⟩ : syracuseStep 660887 = 991331) B991331
theorem B660907 : Blo 658307 660907 := bstep (se 1 (by rfl) ⟨495680, by rfl⟩ : syracuseStep 660907 = 991361) B991361
theorem B3347891 : Blo 658307 3347891 := bstep (se 1 (by rfl) ⟨2510918, by rfl⟩ : syracuseStep 3347891 = 5021837) B5021837
theorem B660919 : Blo 658307 660919 := bstep (se 1 (by rfl) ⟨495689, by rfl⟩ : syracuseStep 660919 = 991379) B991379
theorem B988619 : Blo 658307 988619 := bstep (se 1 (by rfl) ⟨741464, by rfl⟩ : syracuseStep 988619 = 1482929) B1482929
theorem B660939 : Blo 658307 660939 := bstep (se 1 (by rfl) ⟨495704, by rfl⟩ : syracuseStep 660939 = 991409) B991409
theorem B988631 : Blo 658307 988631 := bstep (se 1 (by rfl) ⟨741473, by rfl⟩ : syracuseStep 988631 = 1482947) B1482947
theorem B660951 : Blo 658307 660951 := bstep (se 1 (by rfl) ⟨495713, by rfl⟩ : syracuseStep 660951 = 991427) B991427
theorem B4232665 : Blo 658307 4232665 := bstep (se 2 (by rfl) ⟨1587249, by rfl⟩ : syracuseStep 4232665 = 3174499) B3174499
theorem B2233817 : Blo 658307 2233817 := bstep (se 2 (by rfl) ⟨837681, by rfl⟩ : syracuseStep 2233817 = 1675363) B1675363
theorem B7542233 : Blo 658307 7542233 := bstep (se 2 (by rfl) ⟨2828337, by rfl⟩ : syracuseStep 7542233 = 5656675) B5656675
theorem B660971 : Blo 658307 660971 := bstep (se 1 (by rfl) ⟨495728, by rfl⟩ : syracuseStep 660971 = 991457) B991457
theorem B660983 : Blo 658307 660983 := bstep (se 1 (by rfl) ⟨495737, by rfl⟩ : syracuseStep 660983 = 991475) B991475
theorem B661003 : Blo 658307 661003 := bstep (se 1 (by rfl) ⟨495752, by rfl⟩ : syracuseStep 661003 = 991505) B991505
theorem B661015 : Blo 658307 661015 := bstep (se 1 (by rfl) ⟨495761, by rfl⟩ : syracuseStep 661015 = 991523) B991523
theorem B988697 : Blo 658307 988697 := bstep (se 2 (by rfl) ⟨370761, by rfl⟩ : syracuseStep 988697 = 741523) B741523
theorem B661035 : Blo 658307 661035 := bstep (se 1 (by rfl) ⟨495776, by rfl⟩ : syracuseStep 661035 = 991553) B991553
theorem B661047 : Blo 658307 661047 := bstep (se 1 (by rfl) ⟨495785, by rfl⟩ : syracuseStep 661047 = 991571) B991571
theorem B661067 : Blo 658307 661067 := bstep (se 1 (by rfl) ⟨495800, by rfl⟩ : syracuseStep 661067 = 991601) B991601
theorem B1250903 : Blo 658307 1250903 := bstep (se 1 (by rfl) ⟨938177, by rfl⟩ : syracuseStep 1250903 = 1876355) B1876355
theorem B661079 : Blo 658307 661079 := bstep (se 1 (by rfl) ⟨495809, by rfl⟩ : syracuseStep 661079 = 991619) B991619
theorem B661099 : Blo 658307 661099 := bstep (se 1 (by rfl) ⟨495824, by rfl⟩ : syracuseStep 661099 = 991649) B991649
theorem B661111 : Blo 658307 661111 := bstep (se 1 (by rfl) ⟨495833, by rfl⟩ : syracuseStep 661111 = 991667) B991667
theorem B988811 : Blo 658307 988811 := bstep (se 1 (by rfl) ⟨741608, by rfl⟩ : syracuseStep 988811 = 1483217) B1483217
theorem B661131 : Blo 658307 661131 := bstep (se 1 (by rfl) ⟨495848, by rfl⟩ : syracuseStep 661131 = 991697) B991697
theorem B988823 : Blo 658307 988823 := bstep (se 1 (by rfl) ⟨741617, by rfl⟩ : syracuseStep 988823 = 1483235) B1483235
theorem B661143 : Blo 658307 661143 := bstep (se 1 (by rfl) ⟨495857, by rfl⟩ : syracuseStep 661143 = 991715) B991715
theorem B661163 : Blo 658307 661163 := bstep (se 1 (by rfl) ⟨495872, by rfl⟩ : syracuseStep 661163 = 991745) B991745
theorem B661175 : Blo 658307 661175 := bstep (se 1 (by rfl) ⟨495881, by rfl⟩ : syracuseStep 661175 = 991763) B991763
theorem B661195 : Blo 658307 661195 := bstep (se 1 (by rfl) ⟨495896, by rfl⟩ : syracuseStep 661195 = 991793) B991793
theorem B661207 : Blo 658307 661207 := bstep (se 1 (by rfl) ⟨495905, by rfl⟩ : syracuseStep 661207 = 991811) B991811
theorem B988889 : Blo 658307 988889 := bstep (se 2 (by rfl) ⟨370833, by rfl⟩ : syracuseStep 988889 = 741667) B741667
theorem B661227 : Blo 658307 661227 := bstep (se 1 (by rfl) ⟨495920, by rfl⟩ : syracuseStep 661227 = 991841) B991841
theorem B661239 : Blo 658307 661239 := bstep (se 1 (by rfl) ⟨495929, by rfl⟩ : syracuseStep 661239 = 991859) B991859
theorem B661259 : Blo 658307 661259 := bstep (se 1 (by rfl) ⟨495944, by rfl⟩ : syracuseStep 661259 = 991889) B991889
theorem B661271 : Blo 658307 661271 := bstep (se 1 (by rfl) ⟨495953, by rfl⟩ : syracuseStep 661271 = 991907) B991907
theorem B661291 : Blo 658307 661291 := bstep (se 1 (by rfl) ⟨495968, by rfl⟩ : syracuseStep 661291 = 991937) B991937
theorem B661303 : Blo 658307 661303 := bstep (se 1 (by rfl) ⟨495977, by rfl⟩ : syracuseStep 661303 = 991955) B991955
theorem B989003 : Blo 658307 989003 := bstep (se 1 (by rfl) ⟨741752, by rfl⟩ : syracuseStep 989003 = 1483505) B1483505
theorem B661323 : Blo 658307 661323 := bstep (se 1 (by rfl) ⟨495992, by rfl⟩ : syracuseStep 661323 = 991985) B991985
theorem B989015 : Blo 658307 989015 := bstep (se 1 (by rfl) ⟨741761, by rfl⟩ : syracuseStep 989015 = 1483523) B1483523
theorem B661335 : Blo 658307 661335 := bstep (se 1 (by rfl) ⟨496001, by rfl⟩ : syracuseStep 661335 = 992003) B992003
theorem B661355 : Blo 658307 661355 := bstep (se 1 (by rfl) ⟨496016, by rfl⟩ : syracuseStep 661355 = 992033) B992033
theorem B661367 : Blo 658307 661367 := bstep (se 1 (by rfl) ⟨496025, by rfl⟩ : syracuseStep 661367 = 992051) B992051
theorem B661387 : Blo 658307 661387 := bstep (se 1 (by rfl) ⟨496040, by rfl⟩ : syracuseStep 661387 = 992081) B992081
theorem B661399 : Blo 658307 661399 := bstep (se 1 (by rfl) ⟨496049, by rfl⟩ : syracuseStep 661399 = 992099) B992099
theorem B989081 : Blo 658307 989081 := bstep (se 2 (by rfl) ⟨370905, by rfl⟩ : syracuseStep 989081 = 741811) B741811
theorem B661419 : Blo 658307 661419 := bstep (se 1 (by rfl) ⟨496064, by rfl⟩ : syracuseStep 661419 = 992129) B992129
theorem B661431 : Blo 658307 661431 := bstep (se 1 (by rfl) ⟨496073, by rfl⟩ : syracuseStep 661431 = 992147) B992147
theorem B661451 : Blo 658307 661451 := bstep (se 1 (by rfl) ⟨496088, by rfl⟩ : syracuseStep 661451 = 992177) B992177
theorem B890839 : Blo 658307 890839 := bstep (se 1 (by rfl) ⟨668129, by rfl⟩ : syracuseStep 890839 = 1336259) B1336259
theorem B661463 : Blo 658307 661463 := bstep (se 1 (by rfl) ⟨496097, by rfl⟩ : syracuseStep 661463 = 992195) B992195
theorem B661483 : Blo 658307 661483 := bstep (se 1 (by rfl) ⟨496112, by rfl⟩ : syracuseStep 661483 = 992225) B992225
theorem B661495 : Blo 658307 661495 := bstep (se 1 (by rfl) ⟨496121, by rfl⟩ : syracuseStep 661495 = 992243) B992243
theorem B989195 : Blo 658307 989195 := bstep (se 1 (by rfl) ⟨741896, by rfl⟩ : syracuseStep 989195 = 1483793) B1483793
theorem B661515 : Blo 658307 661515 := bstep (se 1 (by rfl) ⟨496136, by rfl⟩ : syracuseStep 661515 = 992273) B992273
theorem B989207 : Blo 658307 989207 := bstep (se 1 (by rfl) ⟨741905, by rfl⟩ : syracuseStep 989207 = 1483811) B1483811
theorem B661527 : Blo 658307 661527 := bstep (se 1 (by rfl) ⟨496145, by rfl⟩ : syracuseStep 661527 = 992291) B992291
theorem B661547 : Blo 658307 661547 := bstep (se 1 (by rfl) ⟨496160, by rfl⟩ : syracuseStep 661547 = 992321) B992321
theorem B2824237 : Blo 658307 2824237 := bstep (se 3 (by rfl) ⟨529544, by rfl⟩ : syracuseStep 2824237 = 1059089) B1059089
theorem B661559 : Blo 658307 661559 := bstep (se 1 (by rfl) ⟨496169, by rfl⟩ : syracuseStep 661559 = 992339) B992339
theorem B60889157 : Blo 658307 60889157 := bstep (se 4 (by rfl) ⟨5708358, by rfl⟩ : syracuseStep 60889157 = 11416717) B11416717
theorem B661579 : Blo 658307 661579 := bstep (se 1 (by rfl) ⟨496184, by rfl⟩ : syracuseStep 661579 = 992369) B992369
theorem B661591 : Blo 658307 661591 := bstep (se 1 (by rfl) ⟨496193, by rfl⟩ : syracuseStep 661591 = 992387) B992387
theorem B989273 : Blo 658307 989273 := bstep (se 2 (by rfl) ⟨370977, by rfl⟩ : syracuseStep 989273 = 741955) B741955
theorem B661611 : Blo 658307 661611 := bstep (se 1 (by rfl) ⟨496208, by rfl⟩ : syracuseStep 661611 = 992417) B992417
theorem B1251443 : Blo 658307 1251443 := bstep (se 1 (by rfl) ⟨938582, by rfl⟩ : syracuseStep 1251443 = 1877165) B1877165
theorem B661623 : Blo 658307 661623 := bstep (se 1 (by rfl) ⟨496217, by rfl⟩ : syracuseStep 661623 = 992435) B992435
theorem B661643 : Blo 658307 661643 := bstep (se 1 (by rfl) ⟨496232, by rfl⟩ : syracuseStep 661643 = 992465) B992465
theorem B661655 : Blo 658307 661655 := bstep (se 1 (by rfl) ⟨496241, by rfl⟩ : syracuseStep 661655 = 992483) B992483
theorem B2234519 : Blo 658307 2234519 := bstep (se 1 (by rfl) ⟨1675889, by rfl⟩ : syracuseStep 2234519 = 3351779) B3351779
theorem B661675 : Blo 658307 661675 := bstep (se 1 (by rfl) ⟨496256, by rfl⟩ : syracuseStep 661675 = 992513) B992513
theorem B661687 : Blo 658307 661687 := bstep (se 1 (by rfl) ⟨496265, by rfl⟩ : syracuseStep 661687 = 992531) B992531
theorem B989387 : Blo 658307 989387 := bstep (se 1 (by rfl) ⟨742040, by rfl⟩ : syracuseStep 989387 = 1484081) B1484081
theorem B792779 : Blo 658307 792779 := bstep (se 1 (by rfl) ⟨594584, by rfl⟩ : syracuseStep 792779 = 1189169) B1189169
theorem B661707 : Blo 658307 661707 := bstep (se 1 (by rfl) ⟨496280, by rfl⟩ : syracuseStep 661707 = 992561) B992561
theorem B989399 : Blo 658307 989399 := bstep (se 1 (by rfl) ⟨742049, by rfl⟩ : syracuseStep 989399 = 1484099) B1484099
theorem B661719 : Blo 658307 661719 := bstep (se 1 (by rfl) ⟨496289, by rfl⟩ : syracuseStep 661719 = 992579) B992579
theorem B2824409 : Blo 658307 2824409 := bstep (se 2 (by rfl) ⟨1059153, by rfl⟩ : syracuseStep 2824409 = 2118307) B2118307
theorem B661739 : Blo 658307 661739 := bstep (se 1 (by rfl) ⟨496304, by rfl⟩ : syracuseStep 661739 = 992609) B992609
theorem B661751 : Blo 658307 661751 := bstep (se 1 (by rfl) ⟨496313, by rfl⟩ : syracuseStep 661751 = 992627) B992627
theorem B661771 : Blo 658307 661771 := bstep (se 1 (by rfl) ⟨496328, by rfl⟩ : syracuseStep 661771 = 992657) B992657
theorem B661783 : Blo 658307 661783 := bstep (se 1 (by rfl) ⟨496337, by rfl⟩ : syracuseStep 661783 = 992675) B992675
theorem B989465 : Blo 658307 989465 := bstep (se 2 (by rfl) ⟨371049, by rfl⟩ : syracuseStep 989465 = 742099) B742099
theorem B661803 : Blo 658307 661803 := bstep (se 1 (by rfl) ⟨496352, by rfl⟩ : syracuseStep 661803 = 992705) B992705
theorem B18061613 : Blo 658307 18061613 := bstep (se 3 (by rfl) ⟨3386552, by rfl⟩ : syracuseStep 18061613 = 6773105) B6773105
theorem B661815 : Blo 658307 661815 := bstep (se 1 (by rfl) ⟨496361, by rfl⟩ : syracuseStep 661815 = 992723) B992723
theorem B661835 : Blo 658307 661835 := bstep (se 1 (by rfl) ⟨496376, by rfl⟩ : syracuseStep 661835 = 992753) B992753
theorem B661847 : Blo 658307 661847 := bstep (se 1 (by rfl) ⟨496385, by rfl⟩ : syracuseStep 661847 = 992771) B992771
theorem B661867 : Blo 658307 661867 := bstep (se 1 (by rfl) ⟨496400, by rfl⟩ : syracuseStep 661867 = 992801) B992801
theorem B661879 : Blo 658307 661879 := bstep (se 1 (by rfl) ⟨496409, by rfl⟩ : syracuseStep 661879 = 992819) B992819
theorem B989579 : Blo 658307 989579 := bstep (se 1 (by rfl) ⟨742184, by rfl⟩ : syracuseStep 989579 = 1484369) B1484369
theorem B661899 : Blo 658307 661899 := bstep (se 1 (by rfl) ⟨496424, by rfl⟩ : syracuseStep 661899 = 992849) B992849
theorem B989591 : Blo 658307 989591 := bstep (se 1 (by rfl) ⟨742193, by rfl⟩ : syracuseStep 989591 = 1484387) B1484387
theorem B661911 : Blo 658307 661911 := bstep (se 1 (by rfl) ⟨496433, by rfl⟩ : syracuseStep 661911 = 992867) B992867
theorem B661931 : Blo 658307 661931 := bstep (se 1 (by rfl) ⟨496448, by rfl⟩ : syracuseStep 661931 = 992897) B992897
theorem B661943 : Blo 658307 661943 := bstep (se 1 (by rfl) ⟨496457, by rfl⟩ : syracuseStep 661943 = 992915) B992915
theorem B661963 : Blo 658307 661963 := bstep (se 1 (by rfl) ⟨496472, by rfl⟩ : syracuseStep 661963 = 992945) B992945
theorem B661975 : Blo 658307 661975 := bstep (se 1 (by rfl) ⟨496481, by rfl⟩ : syracuseStep 661975 = 992963) B992963
theorem B989657 : Blo 658307 989657 := bstep (se 2 (by rfl) ⟨371121, by rfl⟩ : syracuseStep 989657 = 742243) B742243
theorem B661995 : Blo 658307 661995 := bstep (se 1 (by rfl) ⟨496496, by rfl⟩ : syracuseStep 661995 = 992993) B992993
theorem B662007 : Blo 658307 662007 := bstep (se 1 (by rfl) ⟨496505, by rfl⟩ : syracuseStep 662007 = 993011) B993011
theorem B662027 : Blo 658307 662027 := bstep (se 1 (by rfl) ⟨496520, by rfl⟩ : syracuseStep 662027 = 993041) B993041
theorem B662039 : Blo 658307 662039 := bstep (se 1 (by rfl) ⟨496529, by rfl⟩ : syracuseStep 662039 = 993059) B993059
theorem B662059 : Blo 658307 662059 := bstep (se 1 (by rfl) ⟨496544, by rfl⟩ : syracuseStep 662059 = 993089) B993089
theorem B662071 : Blo 658307 662071 := bstep (se 1 (by rfl) ⟨496553, by rfl⟩ : syracuseStep 662071 = 993107) B993107
theorem B1481291 : Blo 658307 1481291 := bstep (se 1 (by rfl) ⟨1110968, by rfl⟩ : syracuseStep 1481291 = 2221937) B2221937
theorem B989771 : Blo 658307 989771 := bstep (se 1 (by rfl) ⟨742328, by rfl⟩ : syracuseStep 989771 = 1484657) B1484657
theorem B662091 : Blo 658307 662091 := bstep (se 1 (by rfl) ⟨496568, by rfl⟩ : syracuseStep 662091 = 993137) B993137
theorem B989783 : Blo 658307 989783 := bstep (se 1 (by rfl) ⟨742337, by rfl⟩ : syracuseStep 989783 = 1484675) B1484675
theorem B662103 : Blo 658307 662103 := bstep (se 1 (by rfl) ⟨496577, by rfl⟩ : syracuseStep 662103 = 993155) B993155
theorem B1251929 : Blo 658307 1251929 := bstep (se 2 (by rfl) ⟨469473, by rfl⟩ : syracuseStep 1251929 = 938947) B938947
theorem B662123 : Blo 658307 662123 := bstep (se 1 (by rfl) ⟨496592, by rfl⟩ : syracuseStep 662123 = 993185) B993185
theorem B662135 : Blo 658307 662135 := bstep (se 1 (by rfl) ⟨496601, by rfl⟩ : syracuseStep 662135 = 993203) B993203
theorem B1481345 : Blo 658307 1481345 := bstep (se 2 (by rfl) ⟨555504, by rfl⟩ : syracuseStep 1481345 = 1111009) B1111009
theorem B662155 : Blo 658307 662155 := bstep (se 1 (by rfl) ⟨496616, by rfl⟩ : syracuseStep 662155 = 993233) B993233
theorem B662167 : Blo 658307 662167 := bstep (se 1 (by rfl) ⟨496625, by rfl⟩ : syracuseStep 662167 = 993251) B993251
theorem B989849 : Blo 658307 989849 := bstep (se 2 (by rfl) ⟨371193, by rfl⟩ : syracuseStep 989849 = 742387) B742387
theorem B662187 : Blo 658307 662187 := bstep (se 1 (by rfl) ⟨496640, by rfl⟩ : syracuseStep 662187 = 993281) B993281
theorem B2235059 : Blo 658307 2235059 := bstep (se 1 (by rfl) ⟨1676294, by rfl⟩ : syracuseStep 2235059 = 3352589) B3352589
theorem B662199 : Blo 658307 662199 := bstep (se 1 (by rfl) ⟨496649, by rfl⟩ : syracuseStep 662199 = 993299) B993299
theorem B662219 : Blo 658307 662219 := bstep (se 1 (by rfl) ⟨496664, by rfl⟩ : syracuseStep 662219 = 993329) B993329
theorem B662231 : Blo 658307 662231 := bstep (se 1 (by rfl) ⟨496673, by rfl⟩ : syracuseStep 662231 = 993347) B993347
theorem B662251 : Blo 658307 662251 := bstep (se 1 (by rfl) ⟨496688, by rfl⟩ : syracuseStep 662251 = 993377) B993377
theorem B662263 : Blo 658307 662263 := bstep (se 1 (by rfl) ⟨496697, by rfl⟩ : syracuseStep 662263 = 993395) B993395
theorem B989963 : Blo 658307 989963 := bstep (se 1 (by rfl) ⟨742472, by rfl⟩ : syracuseStep 989963 = 1484945) B1484945
theorem B662283 : Blo 658307 662283 := bstep (se 1 (by rfl) ⟨496712, by rfl⟩ : syracuseStep 662283 = 993425) B993425
theorem B989975 : Blo 658307 989975 := bstep (se 1 (by rfl) ⟨742481, by rfl⟩ : syracuseStep 989975 = 1484963) B1484963
theorem B662295 : Blo 658307 662295 := bstep (se 1 (by rfl) ⟨496721, by rfl⟩ : syracuseStep 662295 = 993443) B993443
theorem B1481561 : Blo 658307 1481561 := bstep (se 2 (by rfl) ⟨555585, by rfl⟩ : syracuseStep 1481561 = 1111171) B1111171
theorem B990041 : Blo 658307 990041 := bstep (se 2 (by rfl) ⟨371265, by rfl⟩ : syracuseStep 990041 = 742531) B742531
theorem B11443045 : Blo 658307 11443045 := bstep (se 4 (by rfl) ⟨1072785, by rfl⟩ : syracuseStep 11443045 = 2145571) B2145571
theorem B1481651 : Blo 658307 1481651 := bstep (se 1 (by rfl) ⟨1111238, by rfl⟩ : syracuseStep 1481651 = 2222477) B2222477
theorem B990155 : Blo 658307 990155 := bstep (se 1 (by rfl) ⟨742616, by rfl⟩ : syracuseStep 990155 = 1485233) B1485233
theorem B1481687 : Blo 658307 1481687 := bstep (se 1 (by rfl) ⟨1111265, by rfl⟩ : syracuseStep 1481687 = 2222531) B2222531
theorem B990167 : Blo 658307 990167 := bstep (se 1 (by rfl) ⟨742625, by rfl⟩ : syracuseStep 990167 = 1485251) B1485251
theorem B990233 : Blo 658307 990233 := bstep (se 2 (by rfl) ⟨371337, by rfl⟩ : syracuseStep 990233 = 742675) B742675
theorem B1481867 : Blo 658307 1481867 := bstep (se 1 (by rfl) ⟨1111400, by rfl⟩ : syracuseStep 1481867 = 2222801) B2222801
theorem B990347 : Blo 658307 990347 := bstep (se 1 (by rfl) ⟨742760, by rfl⟩ : syracuseStep 990347 = 1485521) B1485521
theorem B990359 : Blo 658307 990359 := bstep (se 1 (by rfl) ⟨742769, by rfl⟩ : syracuseStep 990359 = 1485539) B1485539
theorem B1481921 : Blo 658307 1481921 := bstep (se 2 (by rfl) ⟨555720, by rfl⟩ : syracuseStep 1481921 = 1111441) B1111441
theorem B990425 : Blo 658307 990425 := bstep (se 2 (by rfl) ⟨371409, by rfl⟩ : syracuseStep 990425 = 742819) B742819
theorem B1875251 : Blo 658307 1875251 := bstep (se 1 (by rfl) ⟨1406438, by rfl⟩ : syracuseStep 1875251 = 2812877) B2812877
theorem B990539 : Blo 658307 990539 := bstep (se 1 (by rfl) ⟨742904, by rfl⟩ : syracuseStep 990539 = 1485809) B1485809
theorem B3349835 : Blo 658307 3349835 := bstep (se 1 (by rfl) ⟨2512376, by rfl⟩ : syracuseStep 3349835 = 5024753) B5024753
theorem B990551 : Blo 658307 990551 := bstep (se 1 (by rfl) ⟨742913, by rfl⟩ : syracuseStep 990551 = 1485827) B1485827
theorem B1482137 : Blo 658307 1482137 := bstep (se 2 (by rfl) ⟨555801, by rfl⟩ : syracuseStep 1482137 = 1111603) B1111603
theorem B990617 : Blo 658307 990617 := bstep (se 2 (by rfl) ⟨371481, by rfl⟩ : syracuseStep 990617 = 742963) B742963
theorem B8461745 : Blo 658307 8461745 := bstep (se 2 (by rfl) ⟨3173154, by rfl⟩ : syracuseStep 8461745 = 6346309) B6346309
theorem B1482227 : Blo 658307 1482227 := bstep (se 1 (by rfl) ⟨1111670, by rfl⟩ : syracuseStep 1482227 = 2223341) B2223341
theorem B990731 : Blo 658307 990731 := bstep (se 1 (by rfl) ⟨743048, by rfl⟩ : syracuseStep 990731 = 1486097) B1486097
theorem B1482263 : Blo 658307 1482263 := bstep (se 1 (by rfl) ⟨1111697, by rfl⟩ : syracuseStep 1482263 = 2223395) B2223395
theorem B990743 : Blo 658307 990743 := bstep (se 1 (by rfl) ⟨743057, by rfl⟩ : syracuseStep 990743 = 1486115) B1486115
theorem B990809 : Blo 658307 990809 := bstep (se 2 (by rfl) ⟨371553, by rfl⟩ : syracuseStep 990809 = 743107) B743107
theorem B1875649 : Blo 658307 1875649 := bstep (se 2 (by rfl) ⟨703368, by rfl⟩ : syracuseStep 1875649 = 1406737) B1406737
theorem B1482443 : Blo 658307 1482443 := bstep (se 1 (by rfl) ⟨1111832, by rfl⟩ : syracuseStep 1482443 = 2223665) B2223665
theorem B990923 : Blo 658307 990923 := bstep (se 1 (by rfl) ⟨743192, by rfl⟩ : syracuseStep 990923 = 1486385) B1486385
theorem B990935 : Blo 658307 990935 := bstep (se 1 (by rfl) ⟨743201, by rfl⟩ : syracuseStep 990935 = 1486403) B1486403
theorem B1482497 : Blo 658307 1482497 := bstep (se 2 (by rfl) ⟨555936, by rfl⟩ : syracuseStep 1482497 = 1111873) B1111873
theorem B991001 : Blo 658307 991001 := bstep (se 2 (by rfl) ⟨371625, by rfl⟩ : syracuseStep 991001 = 743251) B743251
theorem B2826049 : Blo 658307 2826049 := bstep (se 2 (by rfl) ⟨1059768, by rfl⟩ : syracuseStep 2826049 = 2119537) B2119537
theorem B991115 : Blo 658307 991115 := bstep (se 1 (by rfl) ⟨743336, by rfl⟩ : syracuseStep 991115 = 1486673) B1486673
theorem B991127 : Blo 658307 991127 := bstep (se 1 (by rfl) ⟨743345, by rfl⟩ : syracuseStep 991127 = 1486691) B1486691
theorem B1482713 : Blo 658307 1482713 := bstep (se 2 (by rfl) ⟨556017, by rfl⟩ : syracuseStep 1482713 = 1112035) B1112035
theorem B991193 : Blo 658307 991193 := bstep (se 2 (by rfl) ⟨371697, by rfl⟩ : syracuseStep 991193 = 743395) B743395
theorem B1253387 : Blo 658307 1253387 := bstep (se 1 (by rfl) ⟨940040, by rfl⟩ : syracuseStep 1253387 = 1880081) B1880081
theorem B1482803 : Blo 658307 1482803 := bstep (se 1 (by rfl) ⟨1112102, by rfl⟩ : syracuseStep 1482803 = 2224205) B2224205
theorem B4005953 : Blo 658307 4005953 := bstep (se 2 (by rfl) ⟨1502232, by rfl⟩ : syracuseStep 4005953 = 3004465) B3004465
theorem B991307 : Blo 658307 991307 := bstep (se 1 (by rfl) ⟨743480, by rfl⟩ : syracuseStep 991307 = 1486961) B1486961
theorem B1482839 : Blo 658307 1482839 := bstep (se 1 (by rfl) ⟨1112129, by rfl⟩ : syracuseStep 1482839 = 2224259) B2224259
theorem B991319 : Blo 658307 991319 := bstep (se 1 (by rfl) ⟨743489, by rfl⟩ : syracuseStep 991319 = 1486979) B1486979
theorem B991385 : Blo 658307 991385 := bstep (se 2 (by rfl) ⟨371769, by rfl⟩ : syracuseStep 991385 = 743539) B743539
theorem B1253569 : Blo 658307 1253569 := bstep (se 2 (by rfl) ⟨470088, by rfl⟩ : syracuseStep 1253569 = 940177) B940177
theorem B1483019 : Blo 658307 1483019 := bstep (se 1 (by rfl) ⟨1112264, by rfl⟩ : syracuseStep 1483019 = 2224529) B2224529
theorem B991499 : Blo 658307 991499 := bstep (se 1 (by rfl) ⟨743624, by rfl⟩ : syracuseStep 991499 = 1487249) B1487249
theorem B991511 : Blo 658307 991511 := bstep (se 1 (by rfl) ⟨743633, by rfl⟩ : syracuseStep 991511 = 1487267) B1487267
theorem B1483073 : Blo 658307 1483073 := bstep (se 2 (by rfl) ⟨556152, by rfl⟩ : syracuseStep 1483073 = 1112305) B1112305
theorem B991577 : Blo 658307 991577 := bstep (se 2 (by rfl) ⟨371841, by rfl⟩ : syracuseStep 991577 = 743683) B743683
theorem B991691 : Blo 658307 991691 := bstep (se 1 (by rfl) ⟨743768, by rfl⟩ : syracuseStep 991691 = 1487537) B1487537
theorem B991703 : Blo 658307 991703 := bstep (se 1 (by rfl) ⟨743777, by rfl⟩ : syracuseStep 991703 = 1487555) B1487555
theorem B1483289 : Blo 658307 1483289 := bstep (se 2 (by rfl) ⟨556233, by rfl⟩ : syracuseStep 1483289 = 1112467) B1112467
theorem B991769 : Blo 658307 991769 := bstep (se 2 (by rfl) ⟨371913, by rfl⟩ : syracuseStep 991769 = 743827) B743827
theorem B4006493 : Blo 658307 4006493 := bstep (se 3 (by rfl) ⟨751217, by rfl⟩ : syracuseStep 4006493 = 1502435) B1502435
theorem B1483379 : Blo 658307 1483379 := bstep (se 1 (by rfl) ⟨1112534, by rfl⟩ : syracuseStep 1483379 = 2225069) B2225069
theorem B1254017 : Blo 658307 1254017 := bstep (se 2 (by rfl) ⟨470256, by rfl⟩ : syracuseStep 1254017 = 940513) B940513
theorem B991883 : Blo 658307 991883 := bstep (se 1 (by rfl) ⟨743912, by rfl⟩ : syracuseStep 991883 = 1487825) B1487825
theorem B1483415 : Blo 658307 1483415 := bstep (se 1 (by rfl) ⟨1112561, by rfl⟩ : syracuseStep 1483415 = 2225123) B2225123
theorem B991895 : Blo 658307 991895 := bstep (se 1 (by rfl) ⟨743921, by rfl⟩ : syracuseStep 991895 = 1487843) B1487843
theorem B991961 : Blo 658307 991961 := bstep (se 2 (by rfl) ⟨371985, by rfl⟩ : syracuseStep 991961 = 743971) B743971
theorem B4760365 : Blo 658307 4760365 := bstep (se 3 (by rfl) ⟨892568, by rfl⟩ : syracuseStep 4760365 = 1785137) B1785137
theorem B1483595 : Blo 658307 1483595 := bstep (se 1 (by rfl) ⟨1112696, by rfl⟩ : syracuseStep 1483595 = 2225393) B2225393
theorem B992075 : Blo 658307 992075 := bstep (se 1 (by rfl) ⟨744056, by rfl⟩ : syracuseStep 992075 = 1488113) B1488113
theorem B992087 : Blo 658307 992087 := bstep (se 1 (by rfl) ⟨744065, by rfl⟩ : syracuseStep 992087 = 1488131) B1488131
theorem B1483649 : Blo 658307 1483649 := bstep (se 2 (by rfl) ⟨556368, by rfl⟩ : syracuseStep 1483649 = 1112737) B1112737
theorem B3810199 : Blo 658307 3810199 := bstep (se 1 (by rfl) ⟨2857649, by rfl⟩ : syracuseStep 3810199 = 5715299) B5715299
theorem B992153 : Blo 658307 992153 := bstep (se 2 (by rfl) ⟨372057, by rfl⟩ : syracuseStep 992153 = 744115) B744115
theorem B1188823 : Blo 658307 1188823 := bstep (se 1 (by rfl) ⟨891617, by rfl⟩ : syracuseStep 1188823 = 1783235) B1783235
theorem B1254359 : Blo 658307 1254359 := bstep (se 1 (by rfl) ⟨940769, by rfl⟩ : syracuseStep 1254359 = 1881539) B1881539
theorem B992267 : Blo 658307 992267 := bstep (se 1 (by rfl) ⟨744200, by rfl⟩ : syracuseStep 992267 = 1488401) B1488401
theorem B992279 : Blo 658307 992279 := bstep (se 1 (by rfl) ⟨744209, by rfl⟩ : syracuseStep 992279 = 1488419) B1488419
theorem B3351617 : Blo 658307 3351617 := bstep (se 2 (by rfl) ⟨1256856, by rfl⟩ : syracuseStep 3351617 = 2513713) B2513713
theorem B1483865 : Blo 658307 1483865 := bstep (se 2 (by rfl) ⟨556449, by rfl⟩ : syracuseStep 1483865 = 1112899) B1112899
theorem B992345 : Blo 658307 992345 := bstep (se 2 (by rfl) ⟨372129, by rfl⟩ : syracuseStep 992345 = 744259) B744259
theorem B1483955 : Blo 658307 1483955 := bstep (se 1 (by rfl) ⟨1112966, by rfl⟩ : syracuseStep 1483955 = 2225933) B2225933
theorem B992459 : Blo 658307 992459 := bstep (se 1 (by rfl) ⟨744344, by rfl⟩ : syracuseStep 992459 = 1488689) B1488689
theorem B1483991 : Blo 658307 1483991 := bstep (se 1 (by rfl) ⟨1112993, by rfl⟩ : syracuseStep 1483991 = 2225987) B2225987
theorem B992471 : Blo 658307 992471 := bstep (se 1 (by rfl) ⟨744353, by rfl⟩ : syracuseStep 992471 = 1488707) B1488707
theorem B992537 : Blo 658307 992537 := bstep (se 2 (by rfl) ⟨372201, by rfl⟩ : syracuseStep 992537 = 744403) B744403
theorem B17114485 : Blo 658307 17114485 := bstep (se 5 (by rfl) ⟨802241, by rfl⟩ : syracuseStep 17114485 = 1604483) B1604483
theorem B1484171 : Blo 658307 1484171 := bstep (se 1 (by rfl) ⟨1113128, by rfl⟩ : syracuseStep 1484171 = 2226257) B2226257
theorem B992651 : Blo 658307 992651 := bstep (se 1 (by rfl) ⟨744488, by rfl⟩ : syracuseStep 992651 = 1488977) B1488977
theorem B992663 : Blo 658307 992663 := bstep (se 1 (by rfl) ⟨744497, by rfl⟩ : syracuseStep 992663 = 1488995) B1488995
theorem B1484225 : Blo 658307 1484225 := bstep (se 2 (by rfl) ⟨556584, by rfl⟩ : syracuseStep 1484225 = 1113169) B1113169
theorem B2827723 : Blo 658307 2827723 := bstep (se 1 (by rfl) ⟨2120792, by rfl⟩ : syracuseStep 2827723 = 4241585) B4241585
theorem B992729 : Blo 658307 992729 := bstep (se 2 (by rfl) ⟨372273, by rfl⟩ : syracuseStep 992729 = 744547) B744547
theorem B1189451 : Blo 658307 1189451 := bstep (se 1 (by rfl) ⟨892088, by rfl⟩ : syracuseStep 1189451 = 1784177) B1784177
theorem B992843 : Blo 658307 992843 := bstep (se 1 (by rfl) ⟨744632, by rfl⟩ : syracuseStep 992843 = 1489265) B1489265
theorem B992855 : Blo 658307 992855 := bstep (se 1 (by rfl) ⟨744641, by rfl⟩ : syracuseStep 992855 = 1489283) B1489283
theorem B1255027 : Blo 658307 1255027 := bstep (se 1 (by rfl) ⟨941270, by rfl⟩ : syracuseStep 1255027 = 1882541) B1882541
theorem B1484441 : Blo 658307 1484441 := bstep (se 2 (by rfl) ⟨556665, by rfl⟩ : syracuseStep 1484441 = 1113331) B1113331
theorem B992921 : Blo 658307 992921 := bstep (se 2 (by rfl) ⟨372345, by rfl⟩ : syracuseStep 992921 = 744691) B744691
theorem B2827997 : Blo 658307 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B1484531 : Blo 658307 1484531 := bstep (se 1 (by rfl) ⟨1113398, by rfl⟩ : syracuseStep 1484531 = 2226797) B2226797
theorem B993035 : Blo 658307 993035 := bstep (se 1 (by rfl) ⟨744776, by rfl⟩ : syracuseStep 993035 = 1489553) B1489553
theorem B1484567 : Blo 658307 1484567 := bstep (se 1 (by rfl) ⟨1113425, by rfl⟩ : syracuseStep 1484567 = 2226851) B2226851
theorem B993047 : Blo 658307 993047 := bstep (se 1 (by rfl) ⟨744785, by rfl⟩ : syracuseStep 993047 = 1489571) B1489571
theorem B993113 : Blo 658307 993113 := bstep (se 2 (by rfl) ⟨372417, by rfl⟩ : syracuseStep 993113 = 744835) B744835
theorem B1484747 : Blo 658307 1484747 := bstep (se 1 (by rfl) ⟨1113560, by rfl⟩ : syracuseStep 1484747 = 2227121) B2227121
theorem B993227 : Blo 658307 993227 := bstep (se 1 (by rfl) ⟨744920, by rfl⟩ : syracuseStep 993227 = 1489841) B1489841
theorem B993239 : Blo 658307 993239 := bstep (se 1 (by rfl) ⟨744929, by rfl⟩ : syracuseStep 993239 = 1489859) B1489859
theorem B1484801 : Blo 658307 1484801 := bstep (se 2 (by rfl) ⟨556800, by rfl⟩ : syracuseStep 1484801 = 1113601) B1113601
theorem B1058827 : Blo 658307 1058827 := bstep (se 1 (by rfl) ⟨794120, by rfl⟩ : syracuseStep 1058827 = 1588241) B1588241
theorem B993305 : Blo 658307 993305 := bstep (se 2 (by rfl) ⟨372489, by rfl⟩ : syracuseStep 993305 = 744979) B744979
theorem B1255475 : Blo 658307 1255475 := bstep (se 1 (by rfl) ⟨941606, by rfl⟩ : syracuseStep 1255475 = 1883213) B1883213
theorem B1255513 : Blo 658307 1255513 := bstep (se 2 (by rfl) ⟨470817, by rfl⟩ : syracuseStep 1255513 = 941635) B941635
theorem B993419 : Blo 658307 993419 := bstep (se 1 (by rfl) ⟨745064, by rfl⟩ : syracuseStep 993419 = 1490129) B1490129
theorem B1878167 : Blo 658307 1878167 := bstep (se 1 (by rfl) ⟨1408625, by rfl⟩ : syracuseStep 1878167 = 2817251) B2817251
theorem B993431 : Blo 658307 993431 := bstep (se 1 (by rfl) ⟨745073, by rfl⟩ : syracuseStep 993431 = 1490147) B1490147
theorem B1485017 : Blo 658307 1485017 := bstep (se 2 (by rfl) ⟨556881, by rfl⟩ : syracuseStep 1485017 = 1113763) B1113763
theorem B1485107 : Blo 658307 1485107 := bstep (se 1 (by rfl) ⟨1113830, by rfl⟩ : syracuseStep 1485107 = 2227661) B2227661
theorem B1485143 : Blo 658307 1485143 := bstep (se 1 (by rfl) ⟨1113857, by rfl⟩ : syracuseStep 1485143 = 2227715) B2227715
theorem B1485323 : Blo 658307 1485323 := bstep (se 1 (by rfl) ⟨1113992, by rfl⟩ : syracuseStep 1485323 = 2227985) B2227985
theorem B1255961 : Blo 658307 1255961 := bstep (se 2 (by rfl) ⟨470985, by rfl⟩ : syracuseStep 1255961 = 941971) B941971
theorem B1485377 : Blo 658307 1485377 := bstep (se 2 (by rfl) ⟨557016, by rfl⟩ : syracuseStep 1485377 = 1114033) B1114033
theorem B2534033 : Blo 658307 2534033 := bstep (se 2 (by rfl) ⟨950262, by rfl⟩ : syracuseStep 2534033 = 1900525) B1900525
theorem B1485593 : Blo 658307 1485593 := bstep (se 2 (by rfl) ⟨557097, by rfl⟩ : syracuseStep 1485593 = 1114195) B1114195
theorem B3222317 : Blo 658307 3222317 := bstep (se 3 (by rfl) ⟨604184, by rfl⟩ : syracuseStep 3222317 = 1208369) B1208369
theorem B1485683 : Blo 658307 1485683 := bstep (se 1 (by rfl) ⟨1114262, by rfl⟩ : syracuseStep 1485683 = 2228525) B2228525
theorem B1485719 : Blo 658307 1485719 := bstep (se 1 (by rfl) ⟨1114289, by rfl⟩ : syracuseStep 1485719 = 2228579) B2228579
theorem B2501549 : Blo 658307 2501549 := bstep (se 3 (by rfl) ⟨469040, by rfl⟩ : syracuseStep 2501549 = 938081) B938081
theorem B1190899 : Blo 658307 1190899 := bstep (se 1 (by rfl) ⟨893174, by rfl⟩ : syracuseStep 1190899 = 1786349) B1786349
theorem B1485899 : Blo 658307 1485899 := bstep (se 1 (by rfl) ⟨1114424, by rfl⟩ : syracuseStep 1485899 = 2228849) B2228849
theorem B1485953 : Blo 658307 1485953 := bstep (se 2 (by rfl) ⟨557232, by rfl⟩ : syracuseStep 1485953 = 1114465) B1114465
theorem B1060057 : Blo 658307 1060057 := bstep (se 2 (by rfl) ⟨397521, by rfl⟩ : syracuseStep 1060057 = 795043) B795043
theorem B1256705 : Blo 658307 1256705 := bstep (se 2 (by rfl) ⟨471264, by rfl⟩ : syracuseStep 1256705 = 942529) B942529
theorem B1486169 : Blo 658307 1486169 := bstep (se 2 (by rfl) ⟨557313, by rfl⟩ : syracuseStep 1486169 = 1114627) B1114627
theorem B1486259 : Blo 658307 1486259 := bstep (se 1 (by rfl) ⟨1114694, by rfl⟩ : syracuseStep 1486259 = 2229389) B2229389
theorem B1879499 : Blo 658307 1879499 := bstep (se 1 (by rfl) ⟨1409624, by rfl⟩ : syracuseStep 1879499 = 2819249) B2819249
theorem B1486295 : Blo 658307 1486295 := bstep (se 1 (by rfl) ⟨1114721, by rfl⟩ : syracuseStep 1486295 = 2229443) B2229443
theorem B1256971 : Blo 658307 1256971 := bstep (se 1 (by rfl) ⟨942728, by rfl⟩ : syracuseStep 1256971 = 1885457) B1885457
theorem B1486475 : Blo 658307 1486475 := bstep (se 1 (by rfl) ⟨1114856, by rfl⟩ : syracuseStep 1486475 = 2229713) B2229713
theorem B4238999 : Blo 658307 4238999 := bstep (se 1 (by rfl) ⟨3179249, by rfl⟩ : syracuseStep 4238999 = 6358499) B6358499
theorem B2502323 : Blo 658307 2502323 := bstep (se 1 (by rfl) ⟨1876742, by rfl⟩ : syracuseStep 2502323 = 3753485) B3753485
theorem B1486529 : Blo 658307 1486529 := bstep (se 2 (by rfl) ⟨557448, by rfl⟩ : syracuseStep 1486529 = 1114897) B1114897
theorem B1486745 : Blo 658307 1486745 := bstep (se 2 (by rfl) ⟨557529, by rfl⟩ : syracuseStep 1486745 = 1115059) B1115059
theorem B1486835 : Blo 658307 1486835 := bstep (se 1 (by rfl) ⟨1115126, by rfl⟩ : syracuseStep 1486835 = 2230253) B2230253
theorem B1191937 : Blo 658307 1191937 := bstep (se 2 (by rfl) ⟨446976, by rfl⟩ : syracuseStep 1191937 = 893953) B893953
theorem B1486871 : Blo 658307 1486871 := bstep (se 1 (by rfl) ⟨1115153, by rfl⟩ : syracuseStep 1486871 = 2230307) B2230307
theorem B1781939 : Blo 658307 1781939 := bstep (se 1 (by rfl) ⟨1336454, by rfl⟩ : syracuseStep 1781939 = 2672909) B2672909
theorem B1487051 : Blo 658307 1487051 := bstep (se 1 (by rfl) ⟨1115288, by rfl⟩ : syracuseStep 1487051 = 2230577) B2230577
theorem B1487105 : Blo 658307 1487105 := bstep (se 2 (by rfl) ⟨557664, by rfl⟩ : syracuseStep 1487105 = 1115329) B1115329
theorem B1487321 : Blo 658307 1487321 := bstep (se 2 (by rfl) ⟨557745, by rfl⟩ : syracuseStep 1487321 = 1115491) B1115491
theorem B1487411 : Blo 658307 1487411 := bstep (se 1 (by rfl) ⟨1115558, by rfl⟩ : syracuseStep 1487411 = 2231117) B2231117
theorem B1487447 : Blo 658307 1487447 := bstep (se 1 (by rfl) ⟨1115585, by rfl⟩ : syracuseStep 1487447 = 2231171) B2231171
theorem B1487627 : Blo 658307 1487627 := bstep (se 1 (by rfl) ⟨1115720, by rfl⟩ : syracuseStep 1487627 = 2231441) B2231441
theorem B2143027 : Blo 658307 2143027 := bstep (se 1 (by rfl) ⟨1607270, by rfl⟩ : syracuseStep 2143027 = 3214541) B3214541
theorem B1487681 : Blo 658307 1487681 := bstep (se 2 (by rfl) ⟨557880, by rfl⟩ : syracuseStep 1487681 = 1115761) B1115761
theorem B2011979 : Blo 658307 2011979 := bstep (se 1 (by rfl) ⟨1508984, by rfl⟩ : syracuseStep 2011979 = 3017969) B3017969
theorem B668503 : Blo 658307 668503 := bstep (se 1 (by rfl) ⟨501377, by rfl⟩ : syracuseStep 668503 = 1002755) B1002755
theorem B2110387 : Blo 658307 2110387 := bstep (se 1 (by rfl) ⟨1582790, by rfl⟩ : syracuseStep 2110387 = 3165581) B3165581
theorem B1487897 : Blo 658307 1487897 := bstep (se 2 (by rfl) ⟨557961, by rfl⟩ : syracuseStep 1487897 = 1115923) B1115923
theorem B1881139 : Blo 658307 1881139 := bstep (se 1 (by rfl) ⟨1410854, by rfl⟩ : syracuseStep 1881139 = 2821709) B2821709
theorem B1487987 : Blo 658307 1487987 := bstep (se 1 (by rfl) ⟨1115990, by rfl⟩ : syracuseStep 1487987 = 2231981) B2231981
theorem B2503811 : Blo 658307 2503811 := bstep (se 1 (by rfl) ⟨1877858, by rfl⟩ : syracuseStep 2503811 = 3755717) B3755717
theorem B1488023 : Blo 658307 1488023 := bstep (se 1 (by rfl) ⟨1116017, by rfl⟩ : syracuseStep 1488023 = 2232035) B2232035
theorem B1193177 : Blo 658307 1193177 := bstep (se 2 (by rfl) ⟨447441, by rfl⟩ : syracuseStep 1193177 = 894883) B894883
theorem B1488203 : Blo 658307 1488203 := bstep (se 1 (by rfl) ⟨1116152, by rfl⟩ : syracuseStep 1488203 = 2232305) B2232305
theorem B1488257 : Blo 658307 1488257 := bstep (se 2 (by rfl) ⟨558096, by rfl⟩ : syracuseStep 1488257 = 1116193) B1116193
theorem B1652147 : Blo 658307 1652147 := bstep (se 1 (by rfl) ⟨1239110, by rfl⟩ : syracuseStep 1652147 = 2478221) B2478221
theorem B2504267 : Blo 658307 2504267 := bstep (se 1 (by rfl) ⟨1878200, by rfl⟩ : syracuseStep 2504267 = 3756401) B3756401
theorem B1488473 : Blo 658307 1488473 := bstep (se 2 (by rfl) ⟨558177, by rfl⟩ : syracuseStep 1488473 = 1116355) B1116355
theorem B11417219 : Blo 658307 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B1488563 : Blo 658307 1488563 := bstep (se 1 (by rfl) ⟨1116422, by rfl⟩ : syracuseStep 1488563 = 2232845) B2232845
theorem B1488599 : Blo 658307 1488599 := bstep (se 1 (by rfl) ⟨1116449, by rfl⟩ : syracuseStep 1488599 = 2232899) B2232899
theorem B2504465 : Blo 658307 2504465 := bstep (se 2 (by rfl) ⟨939174, by rfl⟩ : syracuseStep 2504465 = 1878349) B1878349
theorem B833419 : Blo 658307 833419 := bstep (se 1 (by rfl) ⟨625064, by rfl⟩ : syracuseStep 833419 = 1250129) B1250129
theorem B1488779 : Blo 658307 1488779 := bstep (se 1 (by rfl) ⟨1116584, by rfl⟩ : syracuseStep 1488779 = 2233169) B2233169
theorem B1488833 : Blo 658307 1488833 := bstep (se 2 (by rfl) ⟨558312, by rfl⟩ : syracuseStep 1488833 = 1116625) B1116625
theorem B1882187 : Blo 658307 1882187 := bstep (se 1 (by rfl) ⟨1411640, by rfl⟩ : syracuseStep 1882187 = 2823281) B2823281
theorem B4241483 : Blo 658307 4241483 := bstep (se 1 (by rfl) ⟨3181112, by rfl⟩ : syracuseStep 4241483 = 6362225) B6362225
theorem B2373725 : Blo 658307 2373725 := bstep (se 3 (by rfl) ⟨445073, by rfl⟩ : syracuseStep 2373725 = 890147) B890147
theorem B1489049 : Blo 658307 1489049 := bstep (se 2 (by rfl) ⟨558393, by rfl⟩ : syracuseStep 1489049 = 1116787) B1116787
theorem B1489139 : Blo 658307 1489139 := bstep (se 1 (by rfl) ⟨1116854, by rfl⟩ : syracuseStep 1489139 = 2233709) B2233709
theorem B1489175 : Blo 658307 1489175 := bstep (se 1 (by rfl) ⟨1116881, by rfl⟩ : syracuseStep 1489175 = 2233763) B2233763
theorem B36616493 : Blo 658307 36616493 := bstep (se 3 (by rfl) ⟨6865592, by rfl⟩ : syracuseStep 36616493 = 13731185) B13731185
theorem B12073333 : Blo 658307 12073333 := bstep (se 5 (by rfl) ⟨565937, by rfl⟩ : syracuseStep 12073333 = 1131875) B1131875
theorem B1489355 : Blo 658307 1489355 := bstep (se 1 (by rfl) ⟨1117016, by rfl⟩ : syracuseStep 1489355 = 2234033) B2234033
theorem B1489409 : Blo 658307 1489409 := bstep (se 2 (by rfl) ⟨558528, by rfl⟩ : syracuseStep 1489409 = 1117057) B1117057
theorem B2505239 : Blo 658307 2505239 := bstep (se 1 (by rfl) ⟨1878929, by rfl⟩ : syracuseStep 2505239 = 3757859) B3757859
theorem B1489625 : Blo 658307 1489625 := bstep (se 2 (by rfl) ⟨558609, by rfl⟩ : syracuseStep 1489625 = 1117219) B1117219
theorem B2505437 : Blo 658307 2505437 := bstep (se 3 (by rfl) ⟨469769, by rfl⟩ : syracuseStep 2505437 = 939539) B939539
theorem B1489715 : Blo 658307 1489715 := bstep (se 1 (by rfl) ⟨1117286, by rfl⟩ : syracuseStep 1489715 = 2234573) B2234573
theorem B834391 : Blo 658307 834391 := bstep (se 1 (by rfl) ⟨625793, by rfl⟩ : syracuseStep 834391 = 1251587) B1251587
theorem B1489751 : Blo 658307 1489751 := bstep (se 1 (by rfl) ⟨1117313, by rfl⟩ : syracuseStep 1489751 = 2234627) B2234627
theorem B6339545 : Blo 658307 6339545 := bstep (se 2 (by rfl) ⟨2377329, by rfl⟩ : syracuseStep 6339545 = 4754659) B4754659
theorem B1489931 : Blo 658307 1489931 := bstep (se 1 (by rfl) ⟨1117448, by rfl⟩ : syracuseStep 1489931 = 2234897) B2234897
theorem B1489985 : Blo 658307 1489985 := bstep (se 2 (by rfl) ⟨558744, by rfl⟩ : syracuseStep 1489985 = 1117489) B1117489
theorem B2374877 : Blo 658307 2374877 := bstep (se 3 (by rfl) ⟨445289, by rfl⟩ : syracuseStep 2374877 = 890579) B890579
theorem B2112733 : Blo 658307 2112733 := bstep (se 3 (by rfl) ⟨396137, by rfl⟩ : syracuseStep 2112733 = 792275) B792275
theorem B703787 : Blo 658307 703787 := bstep (se 1 (by rfl) ⟨527840, by rfl⟩ : syracuseStep 703787 = 1055681) B1055681
theorem B1588673 : Blo 658307 1588673 := bstep (se 2 (by rfl) ⟨595752, by rfl⟩ : syracuseStep 1588673 = 1191505) B1191505
theorem B835211 : Blo 658307 835211 := bstep (se 1 (by rfl) ⟨626408, by rfl⟩ : syracuseStep 835211 = 1252817) B1252817
theorem B1883827 : Blo 658307 1883827 := bstep (se 1 (by rfl) ⟨1412870, by rfl⟩ : syracuseStep 1883827 = 2825741) B2825741
theorem B1359703 : Blo 658307 1359703 := bstep (se 1 (by rfl) ⟨1019777, by rfl⟩ : syracuseStep 1359703 = 2039555) B2039555
theorem B1130329 : Blo 658307 1130329 := bstep (se 2 (by rfl) ⟨423873, by rfl⟩ : syracuseStep 1130329 = 847747) B847747
theorem B1884055 : Blo 658307 1884055 := bstep (se 1 (by rfl) ⟨1413041, by rfl⟩ : syracuseStep 1884055 = 2826083) B2826083
theorem B2670509 : Blo 658307 2670509 := bstep (se 3 (by rfl) ⟨500720, by rfl⟩ : syracuseStep 2670509 = 1001441) B1001441
theorem B8044505 : Blo 658307 8044505 := bstep (se 2 (by rfl) ⟨3016689, by rfl⟩ : syracuseStep 8044505 = 6033379) B6033379
theorem B704791 : Blo 658307 704791 := bstep (se 1 (by rfl) ⟨528593, by rfl⟩ : syracuseStep 704791 = 1057187) B1057187
theorem B835915 : Blo 658307 835915 := bstep (se 1 (by rfl) ⟨626936, by rfl⟩ : syracuseStep 835915 = 1253873) B1253873
theorem B30491153 : Blo 658307 30491153 := bstep (se 2 (by rfl) ⟨11434182, by rfl⟩ : syracuseStep 30491153 = 22868365) B22868365
theorem B836183 : Blo 658307 836183 := bstep (se 1 (by rfl) ⟨627137, by rfl⟩ : syracuseStep 836183 = 1254275) B1254275
theorem B4571741 : Blo 658307 4571741 := bstep (se 3 (by rfl) ⟨857201, by rfl⟩ : syracuseStep 4571741 = 1714403) B1714403
theorem B2507395 : Blo 658307 2507395 := bstep (se 1 (by rfl) ⟨1880546, by rfl⟩ : syracuseStep 2507395 = 3761093) B3761093
theorem B11289293 : Blo 658307 11289293 := bstep (se 3 (by rfl) ⟨2116742, by rfl⟩ : syracuseStep 11289293 = 4233485) B4233485
theorem B4014809 : Blo 658307 4014809 := bstep (se 2 (by rfl) ⟨1505553, by rfl⟩ : syracuseStep 4014809 = 3011107) B3011107
theorem B2507699 : Blo 658307 2507699 := bstep (se 1 (by rfl) ⟨1880774, by rfl⟩ : syracuseStep 2507699 = 3761549) B3761549
theorem B705547 : Blo 658307 705547 := bstep (se 1 (by rfl) ⟨529160, by rfl⟩ : syracuseStep 705547 = 1058321) B1058321
theorem B3753053 : Blo 658307 3753053 := bstep (se 3 (by rfl) ⟨703697, by rfl⟩ : syracuseStep 3753053 = 1407395) B1407395
theorem B836887 : Blo 658307 836887 := bstep (se 1 (by rfl) ⟨627665, by rfl⟩ : syracuseStep 836887 = 1255331) B1255331
theorem B2508353 : Blo 658307 2508353 := bstep (se 2 (by rfl) ⟨940632, by rfl⟩ : syracuseStep 2508353 = 1881265) B1881265
theorem B19056221 : Blo 658307 19056221 := bstep (se 3 (by rfl) ⟨3573041, by rfl⟩ : syracuseStep 19056221 = 7146083) B7146083
theorem B1885913 : Blo 658307 1885913 := bstep (se 2 (by rfl) ⟨707217, by rfl⟩ : syracuseStep 1885913 = 1414435) B1414435
theorem B2377475 : Blo 658307 2377475 := bstep (se 1 (by rfl) ⟨1783106, by rfl⟩ : syracuseStep 2377475 = 3566213) B3566213
theorem B1689395 : Blo 658307 1689395 := bstep (se 1 (by rfl) ⟨1267046, by rfl⟩ : syracuseStep 1689395 = 2534093) B2534093
theorem B3753803 : Blo 658307 3753803 := bstep (se 1 (by rfl) ⟨2815352, by rfl⟩ : syracuseStep 3753803 = 5630705) B5630705
theorem B1722391 : Blo 658307 1722391 := bstep (se 1 (by rfl) ⟨1291793, by rfl⟩ : syracuseStep 1722391 = 2583587) B2583587
theorem B2377907 : Blo 658307 2377907 := bstep (se 1 (by rfl) ⟨1783430, by rfl⟩ : syracuseStep 2377907 = 3566861) B3566861
theorem B4770053 : Blo 658307 4770053 := bstep (se 4 (by rfl) ⟨447192, by rfl⟩ : syracuseStep 4770053 = 894385) B894385
theorem B2673425 : Blo 658307 2673425 := bstep (se 2 (by rfl) ⟨1002534, by rfl⟩ : syracuseStep 2673425 = 2005069) B2005069
theorem B2509613 : Blo 658307 2509613 := bstep (se 3 (by rfl) ⟨470552, by rfl⟩ : syracuseStep 2509613 = 941105) B941105
theorem B2509643 : Blo 658307 2509643 := bstep (se 1 (by rfl) ⟨1882232, by rfl⟩ : syracuseStep 2509643 = 3764465) B3764465
theorem B1788761 : Blo 658307 1788761 := bstep (se 2 (by rfl) ⟨670785, by rfl⟩ : syracuseStep 1788761 = 1341571) B1341571
theorem B5000453 : Blo 658307 5000453 := bstep (se 4 (by rfl) ⟨468792, by rfl⟩ : syracuseStep 5000453 = 937585) B937585
theorem B740695 : Blo 658307 740695 := bstep (se 1 (by rfl) ⟨555521, by rfl⟩ : syracuseStep 740695 = 1111043) B1111043
theorem B937369 : Blo 658307 937369 := bstep (se 2 (by rfl) ⟨351513, by rfl⟩ : syracuseStep 937369 = 703027) B703027
theorem B3755443 : Blo 658307 3755443 := bstep (se 1 (by rfl) ⟨2816582, by rfl⟩ : syracuseStep 3755443 = 5633165) B5633165
theorem B2510297 : Blo 658307 2510297 := bstep (se 2 (by rfl) ⟨941361, by rfl⟩ : syracuseStep 2510297 = 1882723) B1882723
theorem B740875 : Blo 658307 740875 := bstep (se 1 (by rfl) ⟨555656, by rfl⟩ : syracuseStep 740875 = 1111313) B1111313
theorem B740983 : Blo 658307 740983 := bstep (se 1 (by rfl) ⟨555737, by rfl⟩ : syracuseStep 740983 = 1111475) B1111475
theorem B2510615 : Blo 658307 2510615 := bstep (se 1 (by rfl) ⟨1882961, by rfl⟩ : syracuseStep 2510615 = 3765923) B3765923
theorem B741163 : Blo 658307 741163 := bstep (se 1 (by rfl) ⟨555872, by rfl⟩ : syracuseStep 741163 = 1111745) B1111745
theorem B741271 : Blo 658307 741271 := bstep (se 1 (by rfl) ⟨555953, by rfl⟩ : syracuseStep 741271 = 1111907) B1111907
theorem B741451 : Blo 658307 741451 := bstep (se 1 (by rfl) ⟨556088, by rfl⟩ : syracuseStep 741451 = 1112177) B1112177
theorem B741559 : Blo 658307 741559 := bstep (se 1 (by rfl) ⟨556169, by rfl⟩ : syracuseStep 741559 = 1112339) B1112339
theorem B741739 : Blo 658307 741739 := bstep (se 1 (by rfl) ⟨556304, by rfl⟩ : syracuseStep 741739 = 1112609) B1112609
theorem B2511283 : Blo 658307 2511283 := bstep (se 1 (by rfl) ⟨1883462, by rfl⟩ : syracuseStep 2511283 = 3766925) B3766925
theorem B1692107 : Blo 658307 1692107 := bstep (se 1 (by rfl) ⟨1269080, by rfl⟩ : syracuseStep 1692107 = 2538161) B2538161
theorem B741847 : Blo 658307 741847 := bstep (se 1 (by rfl) ⟨556385, by rfl⟩ : syracuseStep 741847 = 1112771) B1112771
theorem B1692211 : Blo 658307 1692211 := bstep (se 1 (by rfl) ⟨1269158, by rfl⟩ : syracuseStep 1692211 = 2538317) B2538317
theorem B742027 : Blo 658307 742027 := bstep (se 1 (by rfl) ⟨556520, by rfl⟩ : syracuseStep 742027 = 1113041) B1113041
theorem B1692311 : Blo 658307 1692311 := bstep (se 1 (by rfl) ⟨1269233, by rfl⟩ : syracuseStep 1692311 = 2538467) B2538467
theorem B742135 : Blo 658307 742135 := bstep (se 1 (by rfl) ⟨556601, by rfl⟩ : syracuseStep 742135 = 1113203) B1113203
theorem B2675501 : Blo 658307 2675501 := bstep (se 3 (by rfl) ⟨501656, by rfl⟩ : syracuseStep 2675501 = 1003313) B1003313
theorem B2380589 : Blo 658307 2380589 := bstep (se 3 (by rfl) ⟨446360, by rfl⟩ : syracuseStep 2380589 = 892721) B892721
theorem B938827 : Blo 658307 938827 := bstep (se 1 (by rfl) ⟨704120, by rfl⟩ : syracuseStep 938827 = 1408241) B1408241
theorem B3756901 : Blo 658307 3756901 := bstep (se 4 (by rfl) ⟨352209, by rfl⟩ : syracuseStep 3756901 = 704419) B704419
theorem B742315 : Blo 658307 742315 := bstep (se 1 (by rfl) ⟨556736, by rfl⟩ : syracuseStep 742315 = 1113473) B1113473
theorem B2380747 : Blo 658307 2380747 := bstep (se 1 (by rfl) ⟨1785560, by rfl⟩ : syracuseStep 2380747 = 3571121) B3571121
theorem B742423 : Blo 658307 742423 := bstep (se 1 (by rfl) ⟨556817, by rfl⟩ : syracuseStep 742423 = 1113635) B1113635
theorem B742603 : Blo 658307 742603 := bstep (se 1 (by rfl) ⟨556952, by rfl⟩ : syracuseStep 742603 = 1113905) B1113905
theorem B2381021 : Blo 658307 2381021 := bstep (se 3 (by rfl) ⟨446441, by rfl⟩ : syracuseStep 2381021 = 892883) B892883
theorem B742711 : Blo 658307 742711 := bstep (se 1 (by rfl) ⟨557033, by rfl⟩ : syracuseStep 742711 = 1114067) B1114067
theorem B742891 : Blo 658307 742891 := bstep (se 1 (by rfl) ⟨557168, by rfl⟩ : syracuseStep 742891 = 1114337) B1114337
theorem B1267265 : Blo 658307 1267265 := bstep (se 2 (by rfl) ⟨475224, by rfl⟩ : syracuseStep 1267265 = 950449) B950449
theorem B742999 : Blo 658307 742999 := bstep (se 1 (by rfl) ⟨557249, by rfl⟩ : syracuseStep 742999 = 1114499) B1114499
theorem B5002883 : Blo 658307 5002883 := bstep (se 1 (by rfl) ⟨3752162, by rfl⟩ : syracuseStep 5002883 = 7504325) B7504325
theorem B2512529 : Blo 658307 2512529 := bstep (se 2 (by rfl) ⟨942198, by rfl⟩ : syracuseStep 2512529 = 1884397) B1884397
theorem B1005259 : Blo 658307 1005259 := bstep (se 1 (by rfl) ⟨753944, by rfl⟩ : syracuseStep 1005259 = 1507889) B1507889
theorem B743179 : Blo 658307 743179 := bstep (se 1 (by rfl) ⟨557384, by rfl⟩ : syracuseStep 743179 = 1114769) B1114769
theorem B34363237 : Blo 658307 34363237 := bstep (se 4 (by rfl) ⟨3221553, by rfl⟩ : syracuseStep 34363237 = 6443107) B6443107
theorem B743287 : Blo 658307 743287 := bstep (se 1 (by rfl) ⟨557465, by rfl⟩ : syracuseStep 743287 = 1114931) B1114931
theorem B3168179 : Blo 658307 3168179 := bstep (se 1 (by rfl) ⟨2376134, by rfl⟩ : syracuseStep 3168179 = 4752269) B4752269
theorem B1103833 : Blo 658307 1103833 := bstep (se 2 (by rfl) ⟨413937, by rfl⟩ : syracuseStep 1103833 = 827875) B827875
theorem B743467 : Blo 658307 743467 := bstep (se 1 (by rfl) ⟨557600, by rfl⟩ : syracuseStep 743467 = 1115201) B1115201
theorem B743575 : Blo 658307 743575 := bstep (se 1 (by rfl) ⟨557681, by rfl⟩ : syracuseStep 743575 = 1115363) B1115363
theorem B2677043 : Blo 658307 2677043 := bstep (se 1 (by rfl) ⟨2007782, by rfl⟩ : syracuseStep 2677043 = 4015565) B4015565
theorem B743755 : Blo 658307 743755 := bstep (se 1 (by rfl) ⟨557816, by rfl⟩ : syracuseStep 743755 = 1115633) B1115633
theorem B2513227 : Blo 658307 2513227 := bstep (se 1 (by rfl) ⟨1884920, by rfl⟩ : syracuseStep 2513227 = 3769841) B3769841
theorem B743863 : Blo 658307 743863 := bstep (se 1 (by rfl) ⟨557897, by rfl⟩ : syracuseStep 743863 = 1115795) B1115795
theorem B2513501 : Blo 658307 2513501 := bstep (se 3 (by rfl) ⟨471281, by rfl⟩ : syracuseStep 2513501 = 942563) B942563
theorem B744043 : Blo 658307 744043 := bstep (se 1 (by rfl) ⟨558032, by rfl⟩ : syracuseStep 744043 = 1116065) B1116065
theorem B744151 : Blo 658307 744151 := bstep (se 1 (by rfl) ⟨558113, by rfl⟩ : syracuseStep 744151 = 1116227) B1116227
theorem B3332825 : Blo 658307 3332825 := bstep (se 2 (by rfl) ⟨1249809, by rfl⟩ : syracuseStep 3332825 = 2499619) B2499619
theorem B744331 : Blo 658307 744331 := bstep (se 1 (by rfl) ⟨558248, by rfl⟩ : syracuseStep 744331 = 1116497) B1116497
theorem B1006475 : Blo 658307 1006475 := bstep (se 1 (by rfl) ⟨754856, by rfl⟩ : syracuseStep 1006475 = 1509713) B1509713
theorem B744439 : Blo 658307 744439 := bstep (se 1 (by rfl) ⟨558329, by rfl⟩ : syracuseStep 744439 = 1116659) B1116659
theorem B744619 : Blo 658307 744619 := bstep (se 1 (by rfl) ⟨558464, by rfl⟩ : syracuseStep 744619 = 1116929) B1116929
theorem B3005633 : Blo 658307 3005633 := bstep (se 2 (by rfl) ⟨1127112, by rfl⟩ : syracuseStep 3005633 = 2254225) B2254225
theorem B744727 : Blo 658307 744727 := bstep (se 1 (by rfl) ⟨558545, by rfl⟩ : syracuseStep 744727 = 1117091) B1117091
theorem B2514199 : Blo 658307 2514199 := bstep (se 1 (by rfl) ⟨1885649, by rfl⟩ : syracuseStep 2514199 = 3771299) B3771299
theorem B6348077 : Blo 658307 6348077 := bstep (se 3 (by rfl) ⟨1190264, by rfl⟩ : syracuseStep 6348077 = 2380529) B2380529
theorem B744907 : Blo 658307 744907 := bstep (se 1 (by rfl) ⟨558680, by rfl⟩ : syracuseStep 744907 = 1117361) B1117361
theorem B745015 : Blo 658307 745015 := bstep (se 1 (by rfl) ⟨558761, by rfl⟩ : syracuseStep 745015 = 1117523) B1117523
theorem B19259201 : Blo 658307 19259201 := bstep (se 2 (by rfl) ⟨7222200, by rfl⟩ : syracuseStep 19259201 = 14444401) B14444401
theorem B3628901 : Blo 658307 3628901 := bstep (se 4 (by rfl) ⟨340209, by rfl⟩ : syracuseStep 3628901 = 680419) B680419
theorem B1335155 : Blo 658307 1335155 := bstep (se 1 (by rfl) ⟨1001366, by rfl⟩ : syracuseStep 1335155 = 2002733) B2002733
theorem B2383789 : Blo 658307 2383789 := bstep (se 3 (by rfl) ⟨446960, by rfl⟩ : syracuseStep 2383789 = 893921) B893921
theorem B3563443 : Blo 658307 3563443 := bstep (se 1 (by rfl) ⟨2672582, by rfl⟩ : syracuseStep 3563443 = 5345165) B5345165
theorem B1335449 : Blo 658307 1335449 := bstep (se 2 (by rfl) ⟨500793, by rfl⟩ : syracuseStep 1335449 = 1001587) B1001587
theorem B1433803 : Blo 658307 1433803 := bstep (se 1 (by rfl) ⟨1075352, by rfl⟩ : syracuseStep 1433803 = 2150705) B2150705
theorem B2384093 : Blo 658307 2384093 := bstep (se 3 (by rfl) ⟨447017, by rfl⟩ : syracuseStep 2384093 = 894035) B894035
theorem B3334445 : Blo 658307 3334445 := bstep (se 3 (by rfl) ⟨625208, by rfl⟩ : syracuseStep 3334445 = 1250417) B1250417
theorem B9527651 : Blo 658307 9527651 := bstep (se 1 (by rfl) ⟨7145738, by rfl⟩ : syracuseStep 9527651 = 14291477) B14291477
theorem B2384279 : Blo 658307 2384279 := bstep (se 1 (by rfl) ⟨1788209, by rfl⟩ : syracuseStep 2384279 = 3576419) B3576419
theorem B4219543 : Blo 658307 4219543 := bstep (se 1 (by rfl) ⟨3164657, by rfl⟩ : syracuseStep 4219543 = 6329315) B6329315
theorem B7529111 : Blo 658307 7529111 := bstep (se 1 (by rfl) ⟨5646833, by rfl⟩ : syracuseStep 7529111 = 11293667) B11293667
theorem B1270451 : Blo 658307 1270451 := bstep (se 1 (by rfl) ⟨952838, by rfl⟩ : syracuseStep 1270451 = 1905677) B1905677
theorem B5006285 : Blo 658307 5006285 := bstep (se 3 (by rfl) ⟨938678, by rfl⟩ : syracuseStep 5006285 = 1877357) B1877357
theorem B2548781 : Blo 658307 2548781 := bstep (se 3 (by rfl) ⟨477896, by rfl⟩ : syracuseStep 2548781 = 955793) B955793
theorem B2680237 : Blo 658307 2680237 := bstep (se 3 (by rfl) ⟨502544, by rfl⟩ : syracuseStep 2680237 = 1005089) B1005089
theorem B5006771 : Blo 658307 5006771 := bstep (se 1 (by rfl) ⟨3755078, by rfl⟩ : syracuseStep 5006771 = 7510157) B7510157
theorem B1271297 : Blo 658307 1271297 := bstep (se 2 (by rfl) ⟨476736, by rfl⟩ : syracuseStep 1271297 = 953473) B953473
theorem B2680465 : Blo 658307 2680465 := bstep (se 2 (by rfl) ⟨1005174, by rfl⟩ : syracuseStep 2680465 = 2010349) B2010349
theorem B2222045 : Blo 658307 2222045 := bstep (se 3 (by rfl) ⟨416633, by rfl⟩ : syracuseStep 2222045 = 833267) B833267
theorem B1337419 : Blo 658307 1337419 := bstep (se 1 (by rfl) ⟨1003064, by rfl⟩ : syracuseStep 1337419 = 2006129) B2006129
theorem B3008771 : Blo 658307 3008771 := bstep (se 1 (by rfl) ⟨2256578, by rfl⟩ : syracuseStep 3008771 = 4513157) B4513157
theorem B4352321 : Blo 658307 4352321 := bstep (se 2 (by rfl) ⟨1632120, by rfl⟩ : syracuseStep 4352321 = 3264241) B3264241
theorem B4745603 : Blo 658307 4745603 := bstep (se 1 (by rfl) ⟨3559202, by rfl⟩ : syracuseStep 4745603 = 7118405) B7118405
theorem B3762733 : Blo 658307 3762733 := bstep (se 3 (by rfl) ⟨705512, by rfl⟩ : syracuseStep 3762733 = 1411025) B1411025
theorem B5368385 : Blo 658307 5368385 := bstep (se 2 (by rfl) ⟨2013144, by rfl⟩ : syracuseStep 5368385 = 4026289) B4026289
theorem B2812619 : Blo 658307 2812619 := bstep (se 1 (by rfl) ⟨2109464, by rfl⟩ : syracuseStep 2812619 = 4218929) B4218929
theorem B5008229 : Blo 658307 5008229 := bstep (se 4 (by rfl) ⟨469521, by rfl⟩ : syracuseStep 5008229 = 939043) B939043
theorem B8121379 : Blo 658307 8121379 := bstep (se 1 (by rfl) ⟨6091034, by rfl⟩ : syracuseStep 8121379 = 12182069) B12182069
theorem B2223179 : Blo 658307 2223179 := bstep (se 1 (by rfl) ⟨1667384, by rfl⟩ : syracuseStep 2223179 = 3334769) B3334769
theorem B1698995 : Blo 658307 1698995 := bstep (se 1 (by rfl) ⟨1274246, by rfl⟩ : syracuseStep 1698995 = 2548493) B2548493
theorem B1338611 : Blo 658307 1338611 := bstep (se 1 (by rfl) ⟨1003958, by rfl⟩ : syracuseStep 1338611 = 2007917) B2007917
theorem B7630085 : Blo 658307 7630085 := bstep (se 4 (by rfl) ⟨715320, by rfl⟩ : syracuseStep 7630085 = 1430641) B1430641
theorem B2813201 : Blo 658307 2813201 := bstep (se 2 (by rfl) ⟨1054950, by rfl⟩ : syracuseStep 2813201 = 2109901) B2109901
theorem B5008715 : Blo 658307 5008715 := bstep (se 1 (by rfl) ⟨3756536, by rfl⟩ : syracuseStep 5008715 = 7513073) B7513073
theorem B2223449 : Blo 658307 2223449 := bstep (se 2 (by rfl) ⟨833793, by rfl⟩ : syracuseStep 2223449 = 1667587) B1667587
theorem B1502707 : Blo 658307 1502707 := bstep (se 1 (by rfl) ⟨1127030, by rfl⟩ : syracuseStep 1502707 = 2254061) B2254061
theorem B7925399 : Blo 658307 7925399 := bstep (se 1 (by rfl) ⟨5944049, by rfl⟩ : syracuseStep 7925399 = 11888099) B11888099
theorem B1666777 : Blo 658307 1666777 := bstep (se 2 (by rfl) ⟨625041, by rfl⟩ : syracuseStep 1666777 = 1250083) B1250083
theorem B1502963 : Blo 658307 1502963 := bstep (se 1 (by rfl) ⟨1127222, by rfl⟩ : syracuseStep 1502963 = 2254445) B2254445
theorem B1929053 : Blo 658307 1929053 := bstep (se 3 (by rfl) ⟨361697, by rfl⟩ : syracuseStep 1929053 = 723395) B723395
theorem B978905 : Blo 658307 978905 := bstep (se 2 (by rfl) ⟨367089, by rfl⟩ : syracuseStep 978905 = 734179) B734179
theorem B2224151 : Blo 658307 2224151 := bstep (se 1 (by rfl) ⟨1668113, by rfl⟩ : syracuseStep 2224151 = 3336227) B3336227
theorem B3338333 : Blo 658307 3338333 := bstep (se 3 (by rfl) ⟨625937, by rfl⟩ : syracuseStep 3338333 = 1251875) B1251875
theorem B2257075 : Blo 658307 2257075 := bstep (se 1 (by rfl) ⟨1692806, by rfl⟩ : syracuseStep 2257075 = 3385613) B3385613
theorem B6025421 : Blo 658307 6025421 := bstep (se 3 (by rfl) ⟨1129766, by rfl⟩ : syracuseStep 6025421 = 2259533) B2259533
theorem B2814259 : Blo 658307 2814259 := bstep (se 1 (by rfl) ⟨2110694, by rfl⟩ : syracuseStep 2814259 = 4221389) B4221389
theorem B3010891 : Blo 658307 3010891 := bstep (se 1 (by rfl) ⟨2258168, by rfl⟩ : syracuseStep 3010891 = 4516337) B4516337
theorem B2683415 : Blo 658307 2683415 := bstep (se 1 (by rfl) ⟨2012561, by rfl⟩ : syracuseStep 2683415 = 4025123) B4025123
theorem B2224691 : Blo 658307 2224691 := bstep (se 1 (by rfl) ⟨1668518, by rfl⟩ : syracuseStep 2224691 = 3337037) B3337037
theorem B1667891 : Blo 658307 1667891 := bstep (se 1 (by rfl) ⟨1250918, by rfl⟩ : syracuseStep 1667891 = 2501837) B2501837
theorem B2224961 : Blo 658307 2224961 := bstep (se 2 (by rfl) ⟨834360, by rfl⟩ : syracuseStep 2224961 = 1668721) B1668721
theorem B5370725 : Blo 658307 5370725 := bstep (se 4 (by rfl) ⟨503505, by rfl⟩ : syracuseStep 5370725 = 1007011) B1007011
theorem B1110935 : Blo 658307 1110935 := bstep (se 1 (by rfl) ⟨833201, by rfl⟩ : syracuseStep 1110935 = 1666403) B1666403
theorem B4027315 : Blo 658307 4027315 := bstep (se 1 (by rfl) ⟨3020486, by rfl⟩ : syracuseStep 4027315 = 6040973) B6040973
theorem B1111063 : Blo 658307 1111063 := bstep (se 1 (by rfl) ⟨833297, by rfl⟩ : syracuseStep 1111063 = 1666595) B1666595
theorem B1668185 : Blo 658307 1668185 := bstep (se 2 (by rfl) ⟨625569, by rfl⟩ : syracuseStep 1668185 = 1251139) B1251139
theorem B2225501 : Blo 658307 2225501 := bstep (se 3 (by rfl) ⟨417281, by rfl⟩ : syracuseStep 2225501 = 834563) B834563
theorem B4519261 : Blo 658307 4519261 := bstep (se 3 (by rfl) ⟨847361, by rfl⟩ : syracuseStep 4519261 = 1694723) B1694723
theorem B1111691 : Blo 658307 1111691 := bstep (se 1 (by rfl) ⟨833768, by rfl⟩ : syracuseStep 1111691 = 1667537) B1667537
theorem B2815661 : Blo 658307 2815661 := bstep (se 3 (by rfl) ⟨527936, by rfl⟩ : syracuseStep 2815661 = 1055873) B1055873
theorem B685783 : Blo 658307 685783 := bstep (se 1 (by rfl) ⟨514337, by rfl⟩ : syracuseStep 685783 = 1028675) B1028675
theorem B1111819 : Blo 658307 1111819 := bstep (se 1 (by rfl) ⟨833864, by rfl⟩ : syracuseStep 1111819 = 1667729) B1667729
theorem B1242955 : Blo 658307 1242955 := bstep (se 1 (by rfl) ⟨932216, by rfl⟩ : syracuseStep 1242955 = 1864433) B1864433
theorem B1111961 : Blo 658307 1111961 := bstep (se 2 (by rfl) ⟨416985, by rfl⟩ : syracuseStep 1111961 = 833971) B833971
theorem B1112089 : Blo 658307 1112089 := bstep (se 2 (by rfl) ⟨417033, by rfl⟩ : syracuseStep 1112089 = 834067) B834067
theorem B1341515 : Blo 658307 1341515 := bstep (se 1 (by rfl) ⟨1006136, by rfl⟩ : syracuseStep 1341515 = 2012273) B2012273
theorem B3340439 : Blo 658307 3340439 := bstep (se 1 (by rfl) ⟨2505329, by rfl⟩ : syracuseStep 3340439 = 5010659) B5010659
theorem B1407233 : Blo 658307 1407233 := bstep (se 2 (by rfl) ⟨527712, by rfl⟩ : syracuseStep 1407233 = 1055425) B1055425
theorem B2226635 : Blo 658307 2226635 := bstep (se 1 (by rfl) ⟨1669976, by rfl⟩ : syracuseStep 2226635 = 3339953) B3339953
theorem B1112663 : Blo 658307 1112663 := bstep (se 1 (by rfl) ⟨834497, by rfl⟩ : syracuseStep 1112663 = 1668995) B1668995
theorem B1669835 : Blo 658307 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B1112791 : Blo 658307 1112791 := bstep (se 1 (by rfl) ⟨834593, by rfl⟩ : syracuseStep 1112791 = 1669187) B1669187
theorem B2226905 : Blo 658307 2226905 := bstep (se 2 (by rfl) ⟨835089, by rfl⟩ : syracuseStep 2226905 = 1670179) B1670179
theorem B2030359 : Blo 658307 2030359 := bstep (se 1 (by rfl) ⟨1522769, by rfl⟩ : syracuseStep 2030359 = 3045539) B3045539
theorem B1145675 : Blo 658307 1145675 := bstep (se 1 (by rfl) ⟨859256, by rfl⟩ : syracuseStep 1145675 = 1718513) B1718513
theorem B1342487 : Blo 658307 1342487 := bstep (se 1 (by rfl) ⟨1006865, by rfl⟩ : syracuseStep 1342487 = 2013731) B2013731
theorem B1113419 : Blo 658307 1113419 := bstep (se 1 (by rfl) ⟨835064, by rfl⟩ : syracuseStep 1113419 = 1670129) B1670129
theorem B2227607 : Blo 658307 2227607 := bstep (se 1 (by rfl) ⟨1670705, by rfl⟩ : syracuseStep 2227607 = 3341411) B3341411
theorem B5340593 : Blo 658307 5340593 := bstep (se 2 (by rfl) ⟨2002722, by rfl⟩ : syracuseStep 5340593 = 4005445) B4005445
theorem B1113547 : Blo 658307 1113547 := bstep (se 1 (by rfl) ⟨835160, by rfl⟩ : syracuseStep 1113547 = 1670321) B1670321
theorem B5078533 : Blo 658307 5078533 := bstep (se 4 (by rfl) ⟨476112, by rfl⟩ : syracuseStep 5078533 = 952225) B952225
theorem B4750883 : Blo 658307 4750883 := bstep (se 1 (by rfl) ⟨3563162, by rfl⟩ : syracuseStep 4750883 = 7126325) B7126325
theorem B1113689 : Blo 658307 1113689 := bstep (se 2 (by rfl) ⟨417633, by rfl⟩ : syracuseStep 1113689 = 835267) B835267
theorem B3178115 : Blo 658307 3178115 := bstep (se 1 (by rfl) ⟨2383586, by rfl⟩ : syracuseStep 3178115 = 4767173) B4767173
theorem B1670807 : Blo 658307 1670807 := bstep (se 1 (by rfl) ⟨1253105, by rfl⟩ : syracuseStep 1670807 = 2506211) B2506211
theorem B5635763 : Blo 658307 5635763 := bstep (se 1 (by rfl) ⟨4226822, by rfl⟩ : syracuseStep 5635763 = 8453645) B8453645
theorem B1113817 : Blo 658307 1113817 := bstep (se 2 (by rfl) ⟨417681, by rfl⟩ : syracuseStep 1113817 = 835363) B835363
theorem B1408907 : Blo 658307 1408907 := bstep (se 1 (by rfl) ⟨1056680, by rfl⟩ : syracuseStep 1408907 = 2113361) B2113361
theorem B2228147 : Blo 658307 2228147 := bstep (se 1 (by rfl) ⟨1671110, by rfl⟩ : syracuseStep 2228147 = 3342221) B3342221
theorem B1671425 : Blo 658307 1671425 := bstep (se 2 (by rfl) ⟨626784, by rfl⟩ : syracuseStep 1671425 = 1253569) B1253569
theorem B1114411 : Blo 658307 1114411 := bstep (se 1 (by rfl) ⟨835808, by rfl⟩ : syracuseStep 1114411 = 1671617) B1671617
theorem B3342707 : Blo 658307 3342707 := bstep (se 1 (by rfl) ⟨2507030, by rfl⟩ : syracuseStep 3342707 = 5014061) B5014061
theorem B3047827 : Blo 658307 3047827 := bstep (se 1 (by rfl) ⟨2285870, by rfl⟩ : syracuseStep 3047827 = 4571741) B4571741
theorem B2228633 : Blo 658307 2228633 := bstep (se 2 (by rfl) ⟨835737, by rfl⟩ : syracuseStep 2228633 = 1671475) B1671475
theorem B1114553 : Blo 658307 1114553 := bstep (se 2 (by rfl) ⟨417957, by rfl⟩ : syracuseStep 1114553 = 835915) B835915
theorem B1671799 : Blo 658307 1671799 := bstep (se 1 (by rfl) ⟨1253849, by rfl⟩ : syracuseStep 1671799 = 2507699) B2507699
theorem B3343193 : Blo 658307 3343193 := bstep (se 2 (by rfl) ⟨1253697, by rfl⟩ : syracuseStep 3343193 = 2507395) B2507395
theorem B1672235 : Blo 658307 1672235 := bstep (se 1 (by rfl) ⟨1254176, by rfl⟩ : syracuseStep 1672235 = 2508353) B2508353
theorem B2229335 : Blo 658307 2229335 := bstep (se 1 (by rfl) ⟨1672001, by rfl⟩ : syracuseStep 2229335 = 3344003) B3344003
theorem B1115255 : Blo 658307 1115255 := bstep (se 1 (by rfl) ⟨836441, by rfl⟩ : syracuseStep 1115255 = 1672883) B1672883
theorem B5080265 : Blo 658307 5080265 := bstep (se 2 (by rfl) ⟨1905099, by rfl⟩ : syracuseStep 5080265 = 3810199) B3810199
theorem B3180035 : Blo 658307 3180035 := bstep (se 1 (by rfl) ⟨2385026, by rfl⟩ : syracuseStep 3180035 = 4770053) B4770053
theorem B1115707 : Blo 658307 1115707 := bstep (se 1 (by rfl) ⟨836780, by rfl⟩ : syracuseStep 1115707 = 1673561) B1673561
theorem B2229821 : Blo 658307 2229821 := bstep (se 3 (by rfl) ⟨418091, by rfl⟩ : syracuseStep 2229821 = 836183) B836183
theorem B36537925 : Blo 658307 36537925 := bstep (se 4 (by rfl) ⟨3425430, by rfl⟩ : syracuseStep 36537925 = 6850861) B6850861
theorem B1115849 : Blo 658307 1115849 := bstep (se 2 (by rfl) ⟨418443, by rfl⟩ : syracuseStep 1115849 = 836887) B836887
theorem B1673075 : Blo 658307 1673075 := bstep (se 1 (by rfl) ⟨1254806, by rfl⟩ : syracuseStep 1673075 = 2509613) B2509613
theorem B1509239 : Blo 658307 1509239 := bstep (se 1 (by rfl) ⟨1131929, by rfl⟩ : syracuseStep 1509239 = 2263859) B2263859
theorem B1673095 : Blo 658307 1673095 := bstep (se 1 (by rfl) ⟨1254821, by rfl⟩ : syracuseStep 1673095 = 2509643) B2509643
theorem B3573649 : Blo 658307 3573649 := bstep (se 2 (by rfl) ⟨1340118, by rfl⟩ : syracuseStep 3573649 = 2680237) B2680237
theorem B3770297 : Blo 658307 3770297 := bstep (se 2 (by rfl) ⟨1413861, by rfl⟩ : syracuseStep 3770297 = 2827723) B2827723
theorem B8456309 : Blo 658307 8456309 := bstep (se 5 (by rfl) ⟨396389, by rfl⟩ : syracuseStep 8456309 = 792779) B792779
theorem B1673369 : Blo 658307 1673369 := bstep (se 2 (by rfl) ⟨627513, by rfl⟩ : syracuseStep 1673369 = 1255027) B1255027
theorem B3573953 : Blo 658307 3573953 := bstep (se 2 (by rfl) ⟨1340232, by rfl⟩ : syracuseStep 3573953 = 2680465) B2680465
theorem B1673531 : Blo 658307 1673531 := bstep (se 1 (by rfl) ⟨1255148, by rfl⟩ : syracuseStep 1673531 = 2510297) B2510297
theorem B1116551 : Blo 658307 1116551 := bstep (se 1 (by rfl) ⟨837413, by rfl⟩ : syracuseStep 1116551 = 1674827) B1674827
theorem B1903115 : Blo 658307 1903115 := bstep (se 1 (by rfl) ⟨1427336, by rfl⟩ : syracuseStep 1903115 = 2854673) B2854673
theorem B1673743 : Blo 658307 1673743 := bstep (se 1 (by rfl) ⟨1255307, by rfl⟩ : syracuseStep 1673743 = 2510615) B2510615
theorem B1411769 : Blo 658307 1411769 := bstep (se 2 (by rfl) ⟨529413, by rfl⟩ : syracuseStep 1411769 = 1058827) B1058827
theorem B1674017 : Blo 658307 1674017 := bstep (se 2 (by rfl) ⟨627756, by rfl⟩ : syracuseStep 1674017 = 1255513) B1255513
theorem B658311 : Blo 658307 658311 := bstep (se 1 (by rfl) ⟨493733, by rfl⟩ : syracuseStep 658311 = 987467) B987467
theorem B658319 : Blo 658307 658319 := bstep (se 1 (by rfl) ⟨493739, by rfl⟩ : syracuseStep 658319 = 987479) B987479
theorem B3345299 : Blo 658307 3345299 := bstep (se 1 (by rfl) ⟨2508974, by rfl⟩ : syracuseStep 3345299 = 5017949) B5017949
theorem B2231225 : Blo 658307 2231225 := bstep (se 2 (by rfl) ⟨836709, by rfl⟩ : syracuseStep 2231225 = 1673419) B1673419
theorem B658363 : Blo 658307 658363 := bstep (se 1 (by rfl) ⟨493772, by rfl⟩ : syracuseStep 658363 = 987545) B987545
theorem B658439 : Blo 658307 658439 := bstep (se 1 (by rfl) ⟨493829, by rfl⟩ : syracuseStep 658439 = 987659) B987659
theorem B5639179 : Blo 658307 5639179 := bstep (se 1 (by rfl) ⟨4229384, by rfl⟩ : syracuseStep 5639179 = 8458769) B8458769
theorem B658447 : Blo 658307 658447 := bstep (se 1 (by rfl) ⟨493835, by rfl⟩ : syracuseStep 658447 = 987671) B987671
theorem B1117199 : Blo 658307 1117199 := bstep (se 1 (by rfl) ⟨837899, by rfl⟩ : syracuseStep 1117199 = 1675799) B1675799
theorem B658491 : Blo 658307 658491 := bstep (se 1 (by rfl) ⟨493868, by rfl⟩ : syracuseStep 658491 = 987737) B987737
theorem B658567 : Blo 658307 658567 := bstep (se 1 (by rfl) ⟨493925, by rfl⟩ : syracuseStep 658567 = 987851) B987851
theorem B658575 : Blo 658307 658575 := bstep (se 1 (by rfl) ⟨493931, by rfl⟩ : syracuseStep 658575 = 987863) B987863
theorem B658619 : Blo 658307 658619 := bstep (se 1 (by rfl) ⟨493964, by rfl⟩ : syracuseStep 658619 = 987929) B987929
theorem B3181805 : Blo 658307 3181805 := bstep (se 3 (by rfl) ⟨596588, by rfl⟩ : syracuseStep 3181805 = 1193177) B1193177
theorem B658695 : Blo 658307 658695 := bstep (se 1 (by rfl) ⟨494021, by rfl⟩ : syracuseStep 658695 = 988043) B988043
theorem B658703 : Blo 658307 658703 := bstep (se 1 (by rfl) ⟨494027, by rfl⟩ : syracuseStep 658703 = 988055) B988055
theorem B658747 : Blo 658307 658747 := bstep (se 1 (by rfl) ⟨494060, by rfl⟩ : syracuseStep 658747 = 988121) B988121
theorem B658823 : Blo 658307 658823 := bstep (se 1 (by rfl) ⟨494117, by rfl⟩ : syracuseStep 658823 = 988235) B988235
theorem B658831 : Blo 658307 658831 := bstep (se 1 (by rfl) ⟨494123, by rfl⟩ : syracuseStep 658831 = 988247) B988247
theorem B5016977 : Blo 658307 5016977 := bstep (se 2 (by rfl) ⟨1881366, by rfl⟩ : syracuseStep 5016977 = 3762733) B3762733
theorem B658875 : Blo 658307 658875 := bstep (se 1 (by rfl) ⟨494156, by rfl⟩ : syracuseStep 658875 = 988313) B988313
theorem B658951 : Blo 658307 658951 := bstep (se 1 (by rfl) ⟨494213, by rfl⟩ : syracuseStep 658951 = 988427) B988427
theorem B2231819 : Blo 658307 2231819 := bstep (se 1 (by rfl) ⟨1673864, by rfl⟩ : syracuseStep 2231819 = 3347729) B3347729
theorem B658959 : Blo 658307 658959 := bstep (se 1 (by rfl) ⟨494219, by rfl⟩ : syracuseStep 658959 = 988439) B988439
theorem B2821675 : Blo 658307 2821675 := bstep (se 1 (by rfl) ⟨2116256, by rfl⟩ : syracuseStep 2821675 = 4232513) B4232513
theorem B659003 : Blo 658307 659003 := bstep (se 1 (by rfl) ⟨494252, by rfl⟩ : syracuseStep 659003 = 988505) B988505
theorem B2231927 : Blo 658307 2231927 := bstep (se 1 (by rfl) ⟨1673945, by rfl⟩ : syracuseStep 2231927 = 3347891) B3347891
theorem B659079 : Blo 658307 659079 := bstep (se 1 (by rfl) ⟨494309, by rfl⟩ : syracuseStep 659079 = 988619) B988619
theorem B659087 : Blo 658307 659087 := bstep (se 1 (by rfl) ⟨494315, by rfl⟩ : syracuseStep 659087 = 988631) B988631
theorem B659131 : Blo 658307 659131 := bstep (se 1 (by rfl) ⟨494348, by rfl⟩ : syracuseStep 659131 = 988697) B988697
theorem B659207 : Blo 658307 659207 := bstep (se 1 (by rfl) ⟨494405, by rfl⟩ : syracuseStep 659207 = 988811) B988811
theorem B1675019 : Blo 658307 1675019 := bstep (se 1 (by rfl) ⟨1256264, by rfl⟩ : syracuseStep 1675019 = 2512529) B2512529
theorem B659215 : Blo 658307 659215 := bstep (se 1 (by rfl) ⟨494411, by rfl⟩ : syracuseStep 659215 = 988823) B988823
theorem B659259 : Blo 658307 659259 := bstep (se 1 (by rfl) ⟨494444, by rfl⟩ : syracuseStep 659259 = 988889) B988889
theorem B659335 : Blo 658307 659335 := bstep (se 1 (by rfl) ⟨494501, by rfl⟩ : syracuseStep 659335 = 989003) B989003
theorem B659343 : Blo 658307 659343 := bstep (se 1 (by rfl) ⟨494507, by rfl⟩ : syracuseStep 659343 = 989015) B989015
theorem B3805073 : Blo 658307 3805073 := bstep (se 2 (by rfl) ⟨1426902, by rfl⟩ : syracuseStep 3805073 = 2853805) B2853805
theorem B659387 : Blo 658307 659387 := bstep (se 1 (by rfl) ⟨494540, by rfl⟩ : syracuseStep 659387 = 989081) B989081
theorem B659463 : Blo 658307 659463 := bstep (se 1 (by rfl) ⟨494597, by rfl⟩ : syracuseStep 659463 = 989195) B989195
theorem B659471 : Blo 658307 659471 := bstep (se 1 (by rfl) ⟨494603, by rfl⟩ : syracuseStep 659471 = 989207) B989207
theorem B659515 : Blo 658307 659515 := bstep (se 1 (by rfl) ⟨494636, by rfl⟩ : syracuseStep 659515 = 989273) B989273
theorem B659591 : Blo 658307 659591 := bstep (se 1 (by rfl) ⟨494693, by rfl⟩ : syracuseStep 659591 = 989387) B989387
theorem B659599 : Blo 658307 659599 := bstep (se 1 (by rfl) ⟨494699, by rfl⟩ : syracuseStep 659599 = 989399) B989399
theorem B659643 : Blo 658307 659643 := bstep (se 1 (by rfl) ⟨494732, by rfl⟩ : syracuseStep 659643 = 989465) B989465
theorem B2232521 : Blo 658307 2232521 := bstep (se 2 (by rfl) ⟨837195, by rfl⟩ : syracuseStep 2232521 = 1674391) B1674391
theorem B659719 : Blo 658307 659719 := bstep (se 1 (by rfl) ⟨494789, by rfl⟩ : syracuseStep 659719 = 989579) B989579
theorem B659727 : Blo 658307 659727 := bstep (se 1 (by rfl) ⟨494795, by rfl⟩ : syracuseStep 659727 = 989591) B989591
theorem B659771 : Blo 658307 659771 := bstep (se 1 (by rfl) ⟨494828, by rfl⟩ : syracuseStep 659771 = 989657) B989657
theorem B987527 : Blo 658307 987527 := bstep (se 1 (by rfl) ⟨740645, by rfl⟩ : syracuseStep 987527 = 1481291) B1481291
theorem B659847 : Blo 658307 659847 := bstep (se 1 (by rfl) ⟨494885, by rfl⟩ : syracuseStep 659847 = 989771) B989771
theorem B659855 : Blo 658307 659855 := bstep (se 1 (by rfl) ⟨494891, by rfl⟩ : syracuseStep 659855 = 989783) B989783
theorem B1675667 : Blo 658307 1675667 := bstep (se 1 (by rfl) ⟨1256750, by rfl⟩ : syracuseStep 1675667 = 2513501) B2513501
theorem B987563 : Blo 658307 987563 := bstep (se 1 (by rfl) ⟨740672, by rfl⟩ : syracuseStep 987563 = 1481345) B1481345
theorem B659899 : Blo 658307 659899 := bstep (se 1 (by rfl) ⟨494924, by rfl⟩ : syracuseStep 659899 = 989849) B989849
theorem B987593 : Blo 658307 987593 := bstep (se 2 (by rfl) ⟨370347, by rfl⟩ : syracuseStep 987593 = 740695) B740695
theorem B659975 : Blo 658307 659975 := bstep (se 1 (by rfl) ⟨494981, by rfl⟩ : syracuseStep 659975 = 989963) B989963
theorem B659983 : Blo 658307 659983 := bstep (se 1 (by rfl) ⟨494987, by rfl⟩ : syracuseStep 659983 = 989975) B989975
theorem B1249825 : Blo 658307 1249825 := bstep (se 2 (by rfl) ⟨468684, by rfl⟩ : syracuseStep 1249825 = 937369) B937369
theorem B987707 : Blo 658307 987707 := bstep (se 1 (by rfl) ⟨740780, by rfl⟩ : syracuseStep 987707 = 1481561) B1481561
theorem B660027 : Blo 658307 660027 := bstep (se 1 (by rfl) ⟨495020, by rfl⟩ : syracuseStep 660027 = 990041) B990041
theorem B987767 : Blo 658307 987767 := bstep (se 1 (by rfl) ⟨740825, by rfl⟩ : syracuseStep 987767 = 1481651) B1481651
theorem B660103 : Blo 658307 660103 := bstep (se 1 (by rfl) ⟨495077, by rfl⟩ : syracuseStep 660103 = 990155) B990155
theorem B987791 : Blo 658307 987791 := bstep (se 1 (by rfl) ⟨740843, by rfl⟩ : syracuseStep 987791 = 1481687) B1481687
theorem B660111 : Blo 658307 660111 := bstep (se 1 (by rfl) ⟨495083, by rfl⟩ : syracuseStep 660111 = 990167) B990167
theorem B2003609 : Blo 658307 2003609 := bstep (se 2 (by rfl) ⟨751353, by rfl⟩ : syracuseStep 2003609 = 1502707) B1502707
theorem B987833 : Blo 658307 987833 := bstep (se 2 (by rfl) ⟨370437, by rfl⟩ : syracuseStep 987833 = 740875) B740875
theorem B1675961 : Blo 658307 1675961 := bstep (se 2 (by rfl) ⟨628485, by rfl⟩ : syracuseStep 1675961 = 1256971) B1256971
theorem B660155 : Blo 658307 660155 := bstep (se 1 (by rfl) ⟨495116, by rfl⟩ : syracuseStep 660155 = 990233) B990233
theorem B987911 : Blo 658307 987911 := bstep (se 1 (by rfl) ⟨740933, by rfl⟩ : syracuseStep 987911 = 1481867) B1481867
theorem B660231 : Blo 658307 660231 := bstep (se 1 (by rfl) ⟨495173, by rfl⟩ : syracuseStep 660231 = 990347) B990347
theorem B660239 : Blo 658307 660239 := bstep (se 1 (by rfl) ⟨495179, by rfl⟩ : syracuseStep 660239 = 990359) B990359
theorem B987947 : Blo 658307 987947 := bstep (se 1 (by rfl) ⟨740960, by rfl⟩ : syracuseStep 987947 = 1481921) B1481921
theorem B660283 : Blo 658307 660283 := bstep (se 1 (by rfl) ⟨495212, by rfl⟩ : syracuseStep 660283 = 990425) B990425
theorem B987977 : Blo 658307 987977 := bstep (se 2 (by rfl) ⟨370491, by rfl⟩ : syracuseStep 987977 = 740983) B740983
theorem B4232051 : Blo 658307 4232051 := bstep (se 1 (by rfl) ⟨3174038, by rfl⟩ : syracuseStep 4232051 = 6348077) B6348077
theorem B1250167 : Blo 658307 1250167 := bstep (se 1 (by rfl) ⟨937625, by rfl⟩ : syracuseStep 1250167 = 1875251) B1875251
theorem B660359 : Blo 658307 660359 := bstep (se 1 (by rfl) ⟨495269, by rfl⟩ : syracuseStep 660359 = 990539) B990539
theorem B2233223 : Blo 658307 2233223 := bstep (se 1 (by rfl) ⟨1674917, by rfl⟩ : syracuseStep 2233223 = 3349835) B3349835
theorem B660367 : Blo 658307 660367 := bstep (se 1 (by rfl) ⟨495275, by rfl⟩ : syracuseStep 660367 = 990551) B990551
theorem B988091 : Blo 658307 988091 := bstep (se 1 (by rfl) ⟨741068, by rfl⟩ : syracuseStep 988091 = 1482137) B1482137
theorem B660411 : Blo 658307 660411 := bstep (se 1 (by rfl) ⟨495308, by rfl⟩ : syracuseStep 660411 = 990617) B990617
theorem B5641163 : Blo 658307 5641163 := bstep (se 1 (by rfl) ⟨4230872, by rfl⟩ : syracuseStep 5641163 = 8461745) B8461745
theorem B988151 : Blo 658307 988151 := bstep (se 1 (by rfl) ⟨741113, by rfl⟩ : syracuseStep 988151 = 1482227) B1482227
theorem B660487 : Blo 658307 660487 := bstep (se 1 (by rfl) ⟨495365, by rfl⟩ : syracuseStep 660487 = 990731) B990731
theorem B988175 : Blo 658307 988175 := bstep (se 1 (by rfl) ⟨741131, by rfl⟩ : syracuseStep 988175 = 1482263) B1482263
theorem B660495 : Blo 658307 660495 := bstep (se 1 (by rfl) ⟨495371, by rfl⟩ : syracuseStep 660495 = 990743) B990743
theorem B988217 : Blo 658307 988217 := bstep (se 2 (by rfl) ⟨370581, by rfl⟩ : syracuseStep 988217 = 741163) B741163
theorem B660539 : Blo 658307 660539 := bstep (se 1 (by rfl) ⟨495404, by rfl⟩ : syracuseStep 660539 = 990809) B990809
theorem B988295 : Blo 658307 988295 := bstep (se 1 (by rfl) ⟨741221, by rfl⟩ : syracuseStep 988295 = 1482443) B1482443
theorem B660615 : Blo 658307 660615 := bstep (se 1 (by rfl) ⟨495461, by rfl⟩ : syracuseStep 660615 = 990923) B990923
theorem B660623 : Blo 658307 660623 := bstep (se 1 (by rfl) ⟨495467, by rfl⟩ : syracuseStep 660623 = 990935) B990935
theorem B988331 : Blo 658307 988331 := bstep (se 1 (by rfl) ⟨741248, by rfl⟩ : syracuseStep 988331 = 1482497) B1482497
theorem B660667 : Blo 658307 660667 := bstep (se 1 (by rfl) ⟨495500, by rfl⟩ : syracuseStep 660667 = 991001) B991001
theorem B988361 : Blo 658307 988361 := bstep (se 2 (by rfl) ⟨370635, by rfl⟩ : syracuseStep 988361 = 741271) B741271
theorem B2233601 : Blo 658307 2233601 := bstep (se 2 (by rfl) ⟨837600, by rfl⟩ : syracuseStep 2233601 = 1675201) B1675201
theorem B660743 : Blo 658307 660743 := bstep (se 1 (by rfl) ⟨495557, by rfl⟩ : syracuseStep 660743 = 991115) B991115
theorem B660751 : Blo 658307 660751 := bstep (se 1 (by rfl) ⟨495563, by rfl⟩ : syracuseStep 660751 = 991127) B991127
theorem B988475 : Blo 658307 988475 := bstep (se 1 (by rfl) ⟨741356, by rfl⟩ : syracuseStep 988475 = 1482713) B1482713
theorem B660795 : Blo 658307 660795 := bstep (se 1 (by rfl) ⟨495596, by rfl⟩ : syracuseStep 660795 = 991193) B991193
theorem B988535 : Blo 658307 988535 := bstep (se 1 (by rfl) ⟨741401, by rfl⟩ : syracuseStep 988535 = 1482803) B1482803
theorem B660871 : Blo 658307 660871 := bstep (se 1 (by rfl) ⟨495653, by rfl⟩ : syracuseStep 660871 = 991307) B991307
theorem B988559 : Blo 658307 988559 := bstep (se 1 (by rfl) ⟨741419, by rfl⟩ : syracuseStep 988559 = 1482839) B1482839
theorem B660879 : Blo 658307 660879 := bstep (se 1 (by rfl) ⟨495659, by rfl⟩ : syracuseStep 660879 = 991319) B991319
theorem B988601 : Blo 658307 988601 := bstep (se 2 (by rfl) ⟨370725, by rfl⟩ : syracuseStep 988601 = 741451) B741451
theorem B890299 : Blo 658307 890299 := bstep (se 1 (by rfl) ⟨667724, by rfl⟩ : syracuseStep 890299 = 1335449) B1335449
theorem B660923 : Blo 658307 660923 := bstep (se 1 (by rfl) ⟨495692, by rfl⟩ : syracuseStep 660923 = 991385) B991385
theorem B988679 : Blo 658307 988679 := bstep (se 1 (by rfl) ⟨741509, by rfl⟩ : syracuseStep 988679 = 1483019) B1483019
theorem B660999 : Blo 658307 660999 := bstep (se 1 (by rfl) ⟨495749, by rfl⟩ : syracuseStep 660999 = 991499) B991499
theorem B661007 : Blo 658307 661007 := bstep (se 1 (by rfl) ⟨495755, by rfl⟩ : syracuseStep 661007 = 991511) B991511
theorem B988715 : Blo 658307 988715 := bstep (se 1 (by rfl) ⟨741536, by rfl⟩ : syracuseStep 988715 = 1483073) B1483073
theorem B661051 : Blo 658307 661051 := bstep (se 1 (by rfl) ⟨495788, by rfl⟩ : syracuseStep 661051 = 991577) B991577
theorem B988745 : Blo 658307 988745 := bstep (se 2 (by rfl) ⟨370779, by rfl⟩ : syracuseStep 988745 = 741559) B741559
theorem B661127 : Blo 658307 661127 := bstep (se 1 (by rfl) ⟨495845, by rfl⟩ : syracuseStep 661127 = 991691) B991691
theorem B661135 : Blo 658307 661135 := bstep (se 1 (by rfl) ⟨495851, by rfl⟩ : syracuseStep 661135 = 991703) B991703
theorem B988859 : Blo 658307 988859 := bstep (se 1 (by rfl) ⟨741644, by rfl⟩ : syracuseStep 988859 = 1483289) B1483289
theorem B661179 : Blo 658307 661179 := bstep (se 1 (by rfl) ⟨495884, by rfl⟩ : syracuseStep 661179 = 991769) B991769
theorem B988919 : Blo 658307 988919 := bstep (se 1 (by rfl) ⟨741689, by rfl⟩ : syracuseStep 988919 = 1483379) B1483379
theorem B661255 : Blo 658307 661255 := bstep (se 1 (by rfl) ⟨495941, by rfl⟩ : syracuseStep 661255 = 991883) B991883
theorem B988943 : Blo 658307 988943 := bstep (se 1 (by rfl) ⟨741707, by rfl⟩ : syracuseStep 988943 = 1483415) B1483415
theorem B5019407 : Blo 658307 5019407 := bstep (se 1 (by rfl) ⟨3764555, by rfl⟩ : syracuseStep 5019407 = 7529111) B7529111
theorem B661263 : Blo 658307 661263 := bstep (se 1 (by rfl) ⟨495947, by rfl⟩ : syracuseStep 661263 = 991895) B991895
theorem B988985 : Blo 658307 988985 := bstep (se 2 (by rfl) ⟨370869, by rfl⟩ : syracuseStep 988985 = 741739) B741739
theorem B661307 : Blo 658307 661307 := bstep (se 1 (by rfl) ⟨495980, by rfl⟩ : syracuseStep 661307 = 991961) B991961
theorem B989063 : Blo 658307 989063 := bstep (se 1 (by rfl) ⟨741797, by rfl⟩ : syracuseStep 989063 = 1483595) B1483595
theorem B661383 : Blo 658307 661383 := bstep (se 1 (by rfl) ⟨496037, by rfl⟩ : syracuseStep 661383 = 992075) B992075
theorem B661391 : Blo 658307 661391 := bstep (se 1 (by rfl) ⟨496043, by rfl⟩ : syracuseStep 661391 = 992087) B992087
theorem B3348377 : Blo 658307 3348377 := bstep (se 2 (by rfl) ⟨1255641, by rfl⟩ : syracuseStep 3348377 = 2511283) B2511283
theorem B989099 : Blo 658307 989099 := bstep (se 1 (by rfl) ⟨741824, by rfl⟩ : syracuseStep 989099 = 1483649) B1483649
theorem B661435 : Blo 658307 661435 := bstep (se 1 (by rfl) ⟨496076, by rfl⟩ : syracuseStep 661435 = 992153) B992153
theorem B989129 : Blo 658307 989129 := bstep (se 2 (by rfl) ⟨370923, by rfl⟩ : syracuseStep 989129 = 741847) B741847
theorem B661511 : Blo 658307 661511 := bstep (se 1 (by rfl) ⟨496133, by rfl⟩ : syracuseStep 661511 = 992267) B992267
theorem B661519 : Blo 658307 661519 := bstep (se 1 (by rfl) ⟨496139, by rfl⟩ : syracuseStep 661519 = 992279) B992279
theorem B2234411 : Blo 658307 2234411 := bstep (se 1 (by rfl) ⟨1675808, by rfl⟩ : syracuseStep 2234411 = 3351617) B3351617
theorem B989243 : Blo 658307 989243 := bstep (se 1 (by rfl) ⟨741932, by rfl⟩ : syracuseStep 989243 = 1483865) B1483865
theorem B661563 : Blo 658307 661563 := bstep (se 1 (by rfl) ⟨496172, by rfl⟩ : syracuseStep 661563 = 992345) B992345
theorem B989303 : Blo 658307 989303 := bstep (se 1 (by rfl) ⟨741977, by rfl⟩ : syracuseStep 989303 = 1483955) B1483955
theorem B661639 : Blo 658307 661639 := bstep (se 1 (by rfl) ⟨496229, by rfl⟩ : syracuseStep 661639 = 992459) B992459
theorem B989327 : Blo 658307 989327 := bstep (se 1 (by rfl) ⟨741995, by rfl⟩ : syracuseStep 989327 = 1483991) B1483991
theorem B661647 : Blo 658307 661647 := bstep (se 1 (by rfl) ⟨496235, by rfl⟩ : syracuseStep 661647 = 992471) B992471
theorem B989369 : Blo 658307 989369 := bstep (se 2 (by rfl) ⟨371013, by rfl⟩ : syracuseStep 989369 = 742027) B742027
theorem B661691 : Blo 658307 661691 := bstep (se 1 (by rfl) ⟨496268, by rfl⟩ : syracuseStep 661691 = 992537) B992537
theorem B989447 : Blo 658307 989447 := bstep (se 1 (by rfl) ⟨742085, by rfl⟩ : syracuseStep 989447 = 1484171) B1484171
theorem B661767 : Blo 658307 661767 := bstep (se 1 (by rfl) ⟨496325, by rfl⟩ : syracuseStep 661767 = 992651) B992651
theorem B661775 : Blo 658307 661775 := bstep (se 1 (by rfl) ⟨496331, by rfl⟩ : syracuseStep 661775 = 992663) B992663
theorem B989483 : Blo 658307 989483 := bstep (se 1 (by rfl) ⟨742112, by rfl⟩ : syracuseStep 989483 = 1484225) B1484225
theorem B661819 : Blo 658307 661819 := bstep (se 1 (by rfl) ⟨496364, by rfl⟩ : syracuseStep 661819 = 992729) B992729
theorem B989513 : Blo 658307 989513 := bstep (se 2 (by rfl) ⟨371067, by rfl⟩ : syracuseStep 989513 = 742135) B742135
theorem B661895 : Blo 658307 661895 := bstep (se 1 (by rfl) ⟨496421, by rfl⟩ : syracuseStep 661895 = 992843) B992843
theorem B661903 : Blo 658307 661903 := bstep (se 1 (by rfl) ⟨496427, by rfl⟩ : syracuseStep 661903 = 992855) B992855
theorem B2857369 : Blo 658307 2857369 := bstep (se 2 (by rfl) ⟨1071513, by rfl⟩ : syracuseStep 2857369 = 2143027) B2143027
theorem B1251769 : Blo 658307 1251769 := bstep (se 2 (by rfl) ⟨469413, by rfl⟩ : syracuseStep 1251769 = 938827) B938827
theorem B989627 : Blo 658307 989627 := bstep (se 1 (by rfl) ⟨742220, by rfl⟩ : syracuseStep 989627 = 1484441) B1484441
theorem B661947 : Blo 658307 661947 := bstep (se 1 (by rfl) ⟨496460, by rfl⟩ : syracuseStep 661947 = 992921) B992921
theorem B891337 : Blo 658307 891337 := bstep (se 2 (by rfl) ⟨334251, by rfl⟩ : syracuseStep 891337 = 668503) B668503
theorem B989687 : Blo 658307 989687 := bstep (se 1 (by rfl) ⟨742265, by rfl⟩ : syracuseStep 989687 = 1484531) B1484531
theorem B662023 : Blo 658307 662023 := bstep (se 1 (by rfl) ⟨496517, by rfl⟩ : syracuseStep 662023 = 993035) B993035
theorem B989711 : Blo 658307 989711 := bstep (se 1 (by rfl) ⟨742283, by rfl⟩ : syracuseStep 989711 = 1484567) B1484567
theorem B662031 : Blo 658307 662031 := bstep (se 1 (by rfl) ⟨496523, by rfl⟩ : syracuseStep 662031 = 993047) B993047
theorem B989753 : Blo 658307 989753 := bstep (se 2 (by rfl) ⟨371157, by rfl⟩ : syracuseStep 989753 = 742315) B742315
theorem B662075 : Blo 658307 662075 := bstep (se 1 (by rfl) ⟨496556, by rfl⟩ : syracuseStep 662075 = 993113) B993113
theorem B989831 : Blo 658307 989831 := bstep (se 1 (by rfl) ⟨742373, by rfl⟩ : syracuseStep 989831 = 1484747) B1484747
theorem B662151 : Blo 658307 662151 := bstep (se 1 (by rfl) ⟨496613, by rfl⟩ : syracuseStep 662151 = 993227) B993227
theorem B662159 : Blo 658307 662159 := bstep (se 1 (by rfl) ⟨496619, by rfl⟩ : syracuseStep 662159 = 993239) B993239
theorem B1481363 : Blo 658307 1481363 := bstep (se 1 (by rfl) ⟨1111022, by rfl⟩ : syracuseStep 1481363 = 2222045) B2222045
theorem B989867 : Blo 658307 989867 := bstep (se 1 (by rfl) ⟨742400, by rfl⟩ : syracuseStep 989867 = 1484801) B1484801
theorem B662203 : Blo 658307 662203 := bstep (se 1 (by rfl) ⟨496652, by rfl⟩ : syracuseStep 662203 = 993305) B993305
theorem B1481417 : Blo 658307 1481417 := bstep (se 2 (by rfl) ⟨555531, by rfl⟩ : syracuseStep 1481417 = 1111063) B1111063
theorem B989897 : Blo 658307 989897 := bstep (se 2 (by rfl) ⟨371211, by rfl⟩ : syracuseStep 989897 = 742423) B742423
theorem B662279 : Blo 658307 662279 := bstep (se 1 (by rfl) ⟨496709, by rfl⟩ : syracuseStep 662279 = 993419) B993419
theorem B1252111 : Blo 658307 1252111 := bstep (se 1 (by rfl) ⟨939083, by rfl⟩ : syracuseStep 1252111 = 1878167) B1878167
theorem B662287 : Blo 658307 662287 := bstep (se 1 (by rfl) ⟨496715, by rfl⟩ : syracuseStep 662287 = 993431) B993431
theorem B990011 : Blo 658307 990011 := bstep (se 1 (by rfl) ⟨742508, by rfl⟩ : syracuseStep 990011 = 1485017) B1485017
theorem B2005847 : Blo 658307 2005847 := bstep (se 1 (by rfl) ⟨1504385, by rfl⟩ : syracuseStep 2005847 = 3008771) B3008771
theorem B990071 : Blo 658307 990071 := bstep (se 1 (by rfl) ⟨742553, by rfl⟩ : syracuseStep 990071 = 1485107) B1485107
theorem B990095 : Blo 658307 990095 := bstep (se 1 (by rfl) ⟨742571, by rfl⟩ : syracuseStep 990095 = 1485143) B1485143
theorem B990137 : Blo 658307 990137 := bstep (se 2 (by rfl) ⟨371301, by rfl⟩ : syracuseStep 990137 = 742603) B742603
theorem B990215 : Blo 658307 990215 := bstep (se 1 (by rfl) ⟨742661, by rfl⟩ : syracuseStep 990215 = 1485323) B1485323
theorem B990251 : Blo 658307 990251 := bstep (se 1 (by rfl) ⟨742688, by rfl⟩ : syracuseStep 990251 = 1485377) B1485377
theorem B3578923 : Blo 658307 3578923 := bstep (se 1 (by rfl) ⟨2684192, by rfl⟩ : syracuseStep 3578923 = 5368385) B5368385
theorem B990281 : Blo 658307 990281 := bstep (se 2 (by rfl) ⟨371355, by rfl⟩ : syracuseStep 990281 = 742711) B742711
theorem B1875079 : Blo 658307 1875079 := bstep (se 1 (by rfl) ⟨1406309, by rfl⟩ : syracuseStep 1875079 = 2812619) B2812619
theorem B990395 : Blo 658307 990395 := bstep (se 1 (by rfl) ⟨742796, by rfl⟩ : syracuseStep 990395 = 1485593) B1485593
theorem B990455 : Blo 658307 990455 := bstep (se 1 (by rfl) ⟨742841, by rfl⟩ : syracuseStep 990455 = 1485683) B1485683
theorem B990479 : Blo 658307 990479 := bstep (se 1 (by rfl) ⟨742859, by rfl⟩ : syracuseStep 990479 = 1485719) B1485719
theorem B5643553 : Blo 658307 5643553 := bstep (se 2 (by rfl) ⟨2116332, by rfl⟩ : syracuseStep 5643553 = 4232665) B4232665
theorem B990521 : Blo 658307 990521 := bstep (se 2 (by rfl) ⟨371445, by rfl⟩ : syracuseStep 990521 = 742891) B742891
theorem B1482119 : Blo 658307 1482119 := bstep (se 1 (by rfl) ⟨1111589, by rfl⟩ : syracuseStep 1482119 = 2223179) B2223179
theorem B990599 : Blo 658307 990599 := bstep (se 1 (by rfl) ⟨742949, by rfl⟩ : syracuseStep 990599 = 1485899) B1485899
theorem B990635 : Blo 658307 990635 := bstep (se 1 (by rfl) ⟨742976, by rfl⟩ : syracuseStep 990635 = 1485953) B1485953
theorem B990665 : Blo 658307 990665 := bstep (se 2 (by rfl) ⟨371499, by rfl⟩ : syracuseStep 990665 = 742999) B742999
theorem B5086723 : Blo 658307 5086723 := bstep (se 1 (by rfl) ⟨3815042, by rfl⟩ : syracuseStep 5086723 = 7630085) B7630085
theorem B1875467 : Blo 658307 1875467 := bstep (se 1 (by rfl) ⟨1406600, by rfl⟩ : syracuseStep 1875467 = 2813201) B2813201
theorem B3055133 : Blo 658307 3055133 := bstep (se 3 (by rfl) ⟨572837, by rfl⟩ : syracuseStep 3055133 = 1145675) B1145675
theorem B1482299 : Blo 658307 1482299 := bstep (se 1 (by rfl) ⟨1111724, by rfl⟩ : syracuseStep 1482299 = 2223449) B2223449
theorem B990779 : Blo 658307 990779 := bstep (se 1 (by rfl) ⟨743084, by rfl⟩ : syracuseStep 990779 = 1486169) B1486169
theorem B990839 : Blo 658307 990839 := bstep (se 1 (by rfl) ⟨743129, by rfl⟩ : syracuseStep 990839 = 1486259) B1486259
theorem B1252999 : Blo 658307 1252999 := bstep (se 1 (by rfl) ⟨939749, by rfl⟩ : syracuseStep 1252999 = 1879499) B1879499
theorem B990863 : Blo 658307 990863 := bstep (se 1 (by rfl) ⟨743147, by rfl⟩ : syracuseStep 990863 = 1486295) B1486295
theorem B1482425 : Blo 658307 1482425 := bstep (se 2 (by rfl) ⟨555909, by rfl⟩ : syracuseStep 1482425 = 1111819) B1111819
theorem B990905 : Blo 658307 990905 := bstep (se 2 (by rfl) ⟨371589, by rfl⟩ : syracuseStep 990905 = 743179) B743179
theorem B990983 : Blo 658307 990983 := bstep (se 1 (by rfl) ⟨743237, by rfl⟩ : syracuseStep 990983 = 1486475) B1486475
theorem B2825999 : Blo 658307 2825999 := bstep (se 1 (by rfl) ⟨2119499, by rfl⟩ : syracuseStep 2825999 = 4238999) B4238999
theorem B991019 : Blo 658307 991019 := bstep (se 1 (by rfl) ⟨743264, by rfl⟩ : syracuseStep 991019 = 1486529) B1486529
theorem B45817649 : Blo 658307 45817649 := bstep (se 2 (by rfl) ⟨17181618, by rfl⟩ : syracuseStep 45817649 = 34363237) B34363237
theorem B991049 : Blo 658307 991049 := bstep (se 2 (by rfl) ⟨371643, by rfl⟩ : syracuseStep 991049 = 743287) B743287
theorem B991163 : Blo 658307 991163 := bstep (se 1 (by rfl) ⟨743372, by rfl⟩ : syracuseStep 991163 = 1486745) B1486745
theorem B1187785 : Blo 658307 1187785 := bstep (se 2 (by rfl) ⟨445419, by rfl⟩ : syracuseStep 1187785 = 890839) B890839
theorem B991223 : Blo 658307 991223 := bstep (se 1 (by rfl) ⟨743417, by rfl⟩ : syracuseStep 991223 = 1486835) B1486835
theorem B1482767 : Blo 658307 1482767 := bstep (se 1 (by rfl) ⟨1112075, by rfl⟩ : syracuseStep 1482767 = 2224151) B2224151
theorem B991247 : Blo 658307 991247 := bstep (se 1 (by rfl) ⟨743435, by rfl⟩ : syracuseStep 991247 = 1486871) B1486871
theorem B1482785 : Blo 658307 1482785 := bstep (se 2 (by rfl) ⟨556044, by rfl⟩ : syracuseStep 1482785 = 1112089) B1112089
theorem B991289 : Blo 658307 991289 := bstep (se 2 (by rfl) ⟨371733, by rfl⟩ : syracuseStep 991289 = 743467) B743467
theorem B1187959 : Blo 658307 1187959 := bstep (se 1 (by rfl) ⟨890969, by rfl⟩ : syracuseStep 1187959 = 1781939) B1781939
theorem B991367 : Blo 658307 991367 := bstep (se 1 (by rfl) ⟨743525, by rfl⟩ : syracuseStep 991367 = 1487051) B1487051
theorem B991403 : Blo 658307 991403 := bstep (se 1 (by rfl) ⟨743552, by rfl⟩ : syracuseStep 991403 = 1487105) B1487105
theorem B991433 : Blo 658307 991433 := bstep (se 2 (by rfl) ⟨371787, by rfl⟩ : syracuseStep 991433 = 743575) B743575
theorem B991547 : Blo 658307 991547 := bstep (se 1 (by rfl) ⟨743660, by rfl⟩ : syracuseStep 991547 = 1487321) B1487321
theorem B1483127 : Blo 658307 1483127 := bstep (se 1 (by rfl) ⟨1112345, by rfl⟩ : syracuseStep 1483127 = 2224691) B2224691
theorem B991607 : Blo 658307 991607 := bstep (se 1 (by rfl) ⟨743705, by rfl⟩ : syracuseStep 991607 = 1487411) B1487411
theorem B991631 : Blo 658307 991631 := bstep (se 1 (by rfl) ⟨743723, by rfl⟩ : syracuseStep 991631 = 1487447) B1487447
theorem B991673 : Blo 658307 991673 := bstep (se 2 (by rfl) ⟨371877, by rfl⟩ : syracuseStep 991673 = 743755) B743755
theorem B3350969 : Blo 658307 3350969 := bstep (se 2 (by rfl) ⟨1256613, by rfl⟩ : syracuseStep 3350969 = 2513227) B2513227
theorem B16097777 : Blo 658307 16097777 := bstep (se 2 (by rfl) ⟨6036666, by rfl⟩ : syracuseStep 16097777 = 12073333) B12073333
theorem B991751 : Blo 658307 991751 := bstep (se 1 (by rfl) ⟨743813, by rfl⟩ : syracuseStep 991751 = 1487627) B1487627
theorem B1483307 : Blo 658307 1483307 := bstep (se 1 (by rfl) ⟨1112480, by rfl⟩ : syracuseStep 1483307 = 2224961) B2224961
theorem B991787 : Blo 658307 991787 := bstep (se 1 (by rfl) ⟨743840, by rfl⟩ : syracuseStep 991787 = 1487681) B1487681
theorem B3580483 : Blo 658307 3580483 := bstep (se 1 (by rfl) ⟨2685362, by rfl⟩ : syracuseStep 3580483 = 5370725) B5370725
theorem B991817 : Blo 658307 991817 := bstep (se 2 (by rfl) ⟨371931, by rfl⟩ : syracuseStep 991817 = 743863) B743863
theorem B6333005 : Blo 658307 6333005 := bstep (se 3 (by rfl) ⟨1187438, by rfl⟩ : syracuseStep 6333005 = 2374877) B2374877
theorem B991931 : Blo 658307 991931 := bstep (se 1 (by rfl) ⟨743948, by rfl⟩ : syracuseStep 991931 = 1487897) B1487897
theorem B991991 : Blo 658307 991991 := bstep (se 1 (by rfl) ⟨743993, by rfl⟩ : syracuseStep 991991 = 1487987) B1487987
theorem B992015 : Blo 658307 992015 := bstep (se 1 (by rfl) ⟨744011, by rfl⟩ : syracuseStep 992015 = 1488023) B1488023
theorem B1876765 : Blo 658307 1876765 := bstep (se 3 (by rfl) ⟨351893, by rfl⟩ : syracuseStep 1876765 = 703787) B703787
theorem B992057 : Blo 658307 992057 := bstep (se 2 (by rfl) ⟨372021, by rfl⟩ : syracuseStep 992057 = 744043) B744043
theorem B992135 : Blo 658307 992135 := bstep (se 1 (by rfl) ⟨744101, by rfl⟩ : syracuseStep 992135 = 1488203) B1488203
theorem B1483667 : Blo 658307 1483667 := bstep (se 1 (by rfl) ⟨1112750, by rfl⟩ : syracuseStep 1483667 = 2225501) B2225501
theorem B992171 : Blo 658307 992171 := bstep (se 1 (by rfl) ⟨744128, by rfl⟩ : syracuseStep 992171 = 1488257) B1488257
theorem B1483721 : Blo 658307 1483721 := bstep (se 2 (by rfl) ⟨556395, by rfl⟩ : syracuseStep 1483721 = 1112791) B1112791
theorem B992201 : Blo 658307 992201 := bstep (se 2 (by rfl) ⟨372075, by rfl⟩ : syracuseStep 992201 = 744151) B744151
theorem B992315 : Blo 658307 992315 := bstep (se 1 (by rfl) ⟨744236, by rfl⟩ : syracuseStep 992315 = 1488473) B1488473
theorem B7611479 : Blo 658307 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B1877107 : Blo 658307 1877107 := bstep (se 1 (by rfl) ⟨1407830, by rfl⟩ : syracuseStep 1877107 = 2815661) B2815661
theorem B992375 : Blo 658307 992375 := bstep (se 1 (by rfl) ⟨744281, by rfl⟩ : syracuseStep 992375 = 1488563) B1488563
theorem B992399 : Blo 658307 992399 := bstep (se 1 (by rfl) ⟨744299, by rfl⟩ : syracuseStep 992399 = 1488599) B1488599
theorem B4236461 : Blo 658307 4236461 := bstep (se 3 (by rfl) ⟨794336, by rfl⟩ : syracuseStep 4236461 = 1588673) B1588673
theorem B992441 : Blo 658307 992441 := bstep (se 2 (by rfl) ⟨372165, by rfl⟩ : syracuseStep 992441 = 744331) B744331
theorem B992519 : Blo 658307 992519 := bstep (se 1 (by rfl) ⟨744389, by rfl⟩ : syracuseStep 992519 = 1488779) B1488779
theorem B992555 : Blo 658307 992555 := bstep (se 1 (by rfl) ⟨744416, by rfl⟩ : syracuseStep 992555 = 1488833) B1488833
theorem B992585 : Blo 658307 992585 := bstep (se 2 (by rfl) ⟨372219, by rfl⟩ : syracuseStep 992585 = 744439) B744439
theorem B1254791 : Blo 658307 1254791 := bstep (se 1 (by rfl) ⟨941093, by rfl⟩ : syracuseStep 1254791 = 1882187) B1882187
theorem B894343 : Blo 658307 894343 := bstep (se 1 (by rfl) ⟨670757, by rfl⟩ : syracuseStep 894343 = 1341515) B1341515
theorem B2827655 : Blo 658307 2827655 := bstep (se 1 (by rfl) ⟨2120741, by rfl⟩ : syracuseStep 2827655 = 4241483) B4241483
theorem B1582483 : Blo 658307 1582483 := bstep (se 1 (by rfl) ⟨1186862, by rfl⟩ : syracuseStep 1582483 = 2373725) B2373725
theorem B992699 : Blo 658307 992699 := bstep (se 1 (by rfl) ⟨744524, by rfl⟩ : syracuseStep 992699 = 1489049) B1489049
theorem B992759 : Blo 658307 992759 := bstep (se 1 (by rfl) ⟨744569, by rfl⟩ : syracuseStep 992759 = 1489139) B1489139
theorem B992783 : Blo 658307 992783 := bstep (se 1 (by rfl) ⟨744587, by rfl⟩ : syracuseStep 992783 = 1489175) B1489175
theorem B992825 : Blo 658307 992825 := bstep (se 2 (by rfl) ⟨372309, by rfl⟩ : syracuseStep 992825 = 744619) B744619
theorem B1484423 : Blo 658307 1484423 := bstep (se 1 (by rfl) ⟨1113317, by rfl⟩ : syracuseStep 1484423 = 2226635) B2226635
theorem B992903 : Blo 658307 992903 := bstep (se 1 (by rfl) ⟨744677, by rfl⟩ : syracuseStep 992903 = 1489355) B1489355
theorem B992939 : Blo 658307 992939 := bstep (se 1 (by rfl) ⟨744704, by rfl⟩ : syracuseStep 992939 = 1489409) B1489409
theorem B992969 : Blo 658307 992969 := bstep (se 2 (by rfl) ⟨372363, by rfl⟩ : syracuseStep 992969 = 744727) B744727
theorem B3352265 : Blo 658307 3352265 := bstep (se 2 (by rfl) ⟨1257099, by rfl⟩ : syracuseStep 3352265 = 2514199) B2514199
theorem B1484603 : Blo 658307 1484603 := bstep (se 1 (by rfl) ⟨1113452, by rfl⟩ : syracuseStep 1484603 = 2226905) B2226905
theorem B993083 : Blo 658307 993083 := bstep (se 1 (by rfl) ⟨744812, by rfl⟩ : syracuseStep 993083 = 1489625) B1489625
theorem B993143 : Blo 658307 993143 := bstep (se 1 (by rfl) ⟨744857, by rfl⟩ : syracuseStep 993143 = 1489715) B1489715
theorem B993167 : Blo 658307 993167 := bstep (se 1 (by rfl) ⟨744875, by rfl⟩ : syracuseStep 993167 = 1489751) B1489751
theorem B1484729 : Blo 658307 1484729 := bstep (se 2 (by rfl) ⟨556773, by rfl⟩ : syracuseStep 1484729 = 1113547) B1113547
theorem B993209 : Blo 658307 993209 := bstep (se 2 (by rfl) ⟨372453, by rfl⟩ : syracuseStep 993209 = 744907) B744907
theorem B993287 : Blo 658307 993287 := bstep (se 1 (by rfl) ⟨744965, by rfl⟩ : syracuseStep 993287 = 1489931) B1489931
theorem B894991 : Blo 658307 894991 := bstep (se 1 (by rfl) ⟨671243, by rfl⟩ : syracuseStep 894991 = 1342487) B1342487
theorem B993323 : Blo 658307 993323 := bstep (se 1 (by rfl) ⟨744992, by rfl⟩ : syracuseStep 993323 = 1489985) B1489985
theorem B993353 : Blo 658307 993353 := bstep (se 2 (by rfl) ⟨372507, by rfl⟩ : syracuseStep 993353 = 745015) B745015
theorem B2500865 : Blo 658307 2500865 := bstep (se 2 (by rfl) ⟨937824, by rfl⟩ : syracuseStep 2500865 = 1875649) B1875649
theorem B1485071 : Blo 658307 1485071 := bstep (se 1 (by rfl) ⟨1113803, by rfl⟩ : syracuseStep 1485071 = 2227607) B2227607
theorem B1485089 : Blo 658307 1485089 := bstep (se 2 (by rfl) ⟨556908, by rfl⟩ : syracuseStep 1485089 = 1113817) B1113817
theorem B1812937 : Blo 658307 1812937 := bstep (se 2 (by rfl) ⟨679851, by rfl⟩ : syracuseStep 1812937 = 1359703) B1359703
theorem B1780339 : Blo 658307 1780339 := bstep (se 1 (by rfl) ⟨1335254, by rfl⟩ : syracuseStep 1780339 = 2670509) B2670509
theorem B1485431 : Blo 658307 1485431 := bstep (se 1 (by rfl) ⟨1114073, by rfl⟩ : syracuseStep 1485431 = 2228147) B2228147
theorem B9186085 : Blo 658307 9186085 := bstep (se 4 (by rfl) ⟨861195, by rfl⟩ : syracuseStep 9186085 = 1722391) B1722391
theorem B1485611 : Blo 658307 1485611 := bstep (se 1 (by rfl) ⟨1114208, by rfl⟩ : syracuseStep 1485611 = 2228417) B2228417
theorem B1911737 : Blo 658307 1911737 := bstep (se 2 (by rfl) ⟨716901, by rfl⟩ : syracuseStep 1911737 = 1433803) B1433803
theorem B20327435 : Blo 658307 20327435 := bstep (se 1 (by rfl) ⟨15245576, by rfl⟩ : syracuseStep 20327435 = 30491153) B30491153
theorem B1485971 : Blo 658307 1485971 := bstep (se 1 (by rfl) ⟨1114478, by rfl⟩ : syracuseStep 1485971 = 2228957) B2228957
theorem B1486025 : Blo 658307 1486025 := bstep (se 2 (by rfl) ⟨557259, by rfl⟩ : syracuseStep 1486025 = 1114519) B1114519
theorem B2502035 : Blo 658307 2502035 := bstep (se 1 (by rfl) ⟨1876526, by rfl⟩ : syracuseStep 2502035 = 3753053) B3753053
theorem B17346001 : Blo 658307 17346001 := bstep (se 2 (by rfl) ⟨6504750, by rfl⟩ : syracuseStep 17346001 = 13009501) B13009501
theorem B2010809 : Blo 658307 2010809 := bstep (se 2 (by rfl) ⟨754053, by rfl⟩ : syracuseStep 2010809 = 1508107) B1508107
theorem B1879841 : Blo 658307 1879841 := bstep (se 2 (by rfl) ⟨704940, by rfl⟩ : syracuseStep 1879841 = 1409881) B1409881
theorem B1257275 : Blo 658307 1257275 := bstep (se 1 (by rfl) ⟨942956, by rfl⟩ : syracuseStep 1257275 = 1885913) B1885913
theorem B1584983 : Blo 658307 1584983 := bstep (se 1 (by rfl) ⟨1188737, by rfl⟩ : syracuseStep 1584983 = 2377475) B2377475
theorem B2502535 : Blo 658307 2502535 := bstep (se 1 (by rfl) ⟨1876901, by rfl⟩ : syracuseStep 2502535 = 3753803) B3753803
theorem B1486727 : Blo 658307 1486727 := bstep (se 1 (by rfl) ⟨1115045, by rfl⟩ : syracuseStep 1486727 = 2230091) B2230091
theorem B1879955 : Blo 658307 1879955 := bstep (se 1 (by rfl) ⟨1409966, by rfl⟩ : syracuseStep 1879955 = 2819933) B2819933
theorem B1585097 : Blo 658307 1585097 := bstep (se 2 (by rfl) ⟨594411, by rfl⟩ : syracuseStep 1585097 = 1188823) B1188823
theorem B1486907 : Blo 658307 1486907 := bstep (se 1 (by rfl) ⟨1115180, by rfl⟩ : syracuseStep 1486907 = 2230361) B2230361
theorem B7155773 : Blo 658307 7155773 := bstep (se 3 (by rfl) ⟨1341707, by rfl⟩ : syracuseStep 7155773 = 2683415) B2683415
theorem B1585271 : Blo 658307 1585271 := bstep (se 1 (by rfl) ⟨1188953, by rfl⟩ : syracuseStep 1585271 = 2377907) B2377907
theorem B1487033 : Blo 658307 1487033 := bstep (se 2 (by rfl) ⟨557637, by rfl⟩ : syracuseStep 1487033 = 1115275) B1115275
theorem B3387869 : Blo 658307 3387869 := bstep (se 3 (by rfl) ⟨635225, by rfl⟩ : syracuseStep 3387869 = 1270451) B1270451
theorem B22819313 : Blo 658307 22819313 := bstep (se 2 (by rfl) ⟨8557242, by rfl⟩ : syracuseStep 22819313 = 17114485) B17114485
theorem B1487375 : Blo 658307 1487375 := bstep (se 1 (by rfl) ⟨1115531, by rfl⟩ : syracuseStep 1487375 = 2231063) B2231063
theorem B1487393 : Blo 658307 1487393 := bstep (se 2 (by rfl) ⟨557772, by rfl⟩ : syracuseStep 1487393 = 1115545) B1115545
theorem B9024119 : Blo 658307 9024119 := bstep (se 1 (by rfl) ⟨6768089, by rfl⟩ : syracuseStep 9024119 = 13536179) B13536179
theorem B1880729 : Blo 658307 1880729 := bstep (se 2 (by rfl) ⟨705273, by rfl⟩ : syracuseStep 1880729 = 1410547) B1410547
theorem B1487735 : Blo 658307 1487735 := bstep (se 1 (by rfl) ⟨1115801, by rfl⟩ : syracuseStep 1487735 = 2231603) B2231603
theorem B1487915 : Blo 658307 1487915 := bstep (se 1 (by rfl) ⟨1115936, by rfl⟩ : syracuseStep 1487915 = 2231873) B2231873
theorem B1488275 : Blo 658307 1488275 := bstep (se 1 (by rfl) ⟨1116206, by rfl⟩ : syracuseStep 1488275 = 2232413) B2232413
theorem B1783225 : Blo 658307 1783225 := bstep (se 2 (by rfl) ⟨668709, by rfl⟩ : syracuseStep 1783225 = 1337419) B1337419
theorem B1488329 : Blo 658307 1488329 := bstep (se 2 (by rfl) ⟨558123, by rfl⟩ : syracuseStep 1488329 = 1116247) B1116247
theorem B2012759 : Blo 658307 2012759 := bstep (se 1 (by rfl) ⟨1509569, by rfl⟩ : syracuseStep 2012759 = 3019139) B3019139
theorem B1128071 : Blo 658307 1128071 := bstep (se 1 (by rfl) ⟨846053, by rfl⟩ : syracuseStep 1128071 = 1692107) B1692107
theorem B833323 : Blo 658307 833323 := bstep (se 1 (by rfl) ⟨624992, by rfl⟩ : syracuseStep 833323 = 1249985) B1249985
theorem B1783667 : Blo 658307 1783667 := bstep (se 1 (by rfl) ⟨1337750, by rfl⟩ : syracuseStep 1783667 = 2675501) B2675501
theorem B1587059 : Blo 658307 1587059 := bstep (se 1 (by rfl) ⟨1190294, by rfl⟩ : syracuseStep 1587059 = 2380589) B2380589
theorem B29013977 : Blo 658307 29013977 := bstep (se 2 (by rfl) ⟨10880241, by rfl⟩ : syracuseStep 29013977 = 21760483) B21760483
theorem B1489031 : Blo 658307 1489031 := bstep (se 1 (by rfl) ⟨1116773, by rfl⟩ : syracuseStep 1489031 = 2233547) B2233547
theorem B1587347 : Blo 658307 1587347 := bstep (se 1 (by rfl) ⟨1190510, by rfl⟩ : syracuseStep 1587347 = 2381021) B2381021
theorem B1882369 : Blo 658307 1882369 := bstep (se 2 (by rfl) ⟨705888, by rfl⟩ : syracuseStep 1882369 = 1411777) B1411777
theorem B1489211 : Blo 658307 1489211 := bstep (se 1 (by rfl) ⟨1116908, by rfl⟩ : syracuseStep 1489211 = 2233817) B2233817
theorem B5028155 : Blo 658307 5028155 := bstep (se 1 (by rfl) ⟨3771116, by rfl⟩ : syracuseStep 5028155 = 7542233) B7542233
theorem B1489337 : Blo 658307 1489337 := bstep (se 2 (by rfl) ⟨558501, by rfl⟩ : syracuseStep 1489337 = 1117003) B1117003
theorem B2112119 : Blo 658307 2112119 := bstep (se 1 (by rfl) ⟨1584089, by rfl⟩ : syracuseStep 2112119 = 3168179) B3168179
theorem B1587865 : Blo 658307 1587865 := bstep (se 2 (by rfl) ⟨595449, by rfl⟩ : syracuseStep 1587865 = 1190899) B1190899
theorem B10828505 : Blo 658307 10828505 := bstep (se 2 (by rfl) ⟨4060689, by rfl⟩ : syracuseStep 10828505 = 8121379) B8121379
theorem B834295 : Blo 658307 834295 := bstep (se 1 (by rfl) ⟨625721, by rfl⟩ : syracuseStep 834295 = 1251443) B1251443
theorem B1489679 : Blo 658307 1489679 := bstep (se 1 (by rfl) ⟨1117259, by rfl⟩ : syracuseStep 1489679 = 2234519) B2234519
theorem B1489697 : Blo 658307 1489697 := bstep (se 2 (by rfl) ⟨558636, by rfl⟩ : syracuseStep 1489697 = 1117273) B1117273
theorem B1882939 : Blo 658307 1882939 := bstep (se 1 (by rfl) ⟨1412204, by rfl⟩ : syracuseStep 1882939 = 2824409) B2824409
theorem B12041075 : Blo 658307 12041075 := bstep (se 1 (by rfl) ⟨9030806, by rfl⟩ : syracuseStep 12041075 = 18061613) B18061613
theorem B1784695 : Blo 658307 1784695 := bstep (se 1 (by rfl) ⟨1338521, by rfl⟩ : syracuseStep 1784695 = 2677043) B2677043
theorem B834619 : Blo 658307 834619 := bstep (se 1 (by rfl) ⟨625964, by rfl⟩ : syracuseStep 834619 = 1251929) B1251929
theorem B8043581 : Blo 658307 8043581 := bstep (se 3 (by rfl) ⟨1508171, by rfl⟩ : syracuseStep 8043581 = 3016343) B3016343
theorem B1490039 : Blo 658307 1490039 := bstep (se 1 (by rfl) ⟨1117529, by rfl⟩ : syracuseStep 1490039 = 2235059) B2235059
theorem B4505053 : Blo 658307 4505053 := bstep (se 3 (by rfl) ⟨844697, by rfl⟩ : syracuseStep 4505053 = 1689395) B1689395
theorem B1589249 : Blo 658307 1589249 := bstep (se 2 (by rfl) ⟨595968, by rfl⟩ : syracuseStep 1589249 = 1191937) B1191937
theorem B835591 : Blo 658307 835591 := bstep (se 1 (by rfl) ⟨626693, by rfl⟩ : syracuseStep 835591 = 1253387) B1253387
theorem B2670635 : Blo 658307 2670635 := bstep (se 1 (by rfl) ⟨2002976, by rfl⟩ : syracuseStep 2670635 = 4005953) B4005953
theorem B1589395 : Blo 658307 1589395 := bstep (se 1 (by rfl) ⟨1192046, by rfl⟩ : syracuseStep 1589395 = 2384093) B2384093
theorem B1589519 : Blo 658307 1589519 := bstep (se 1 (by rfl) ⟨1192139, by rfl⟩ : syracuseStep 1589519 = 2384279) B2384279
theorem B2670995 : Blo 658307 2670995 := bstep (se 1 (by rfl) ⟨2003246, by rfl⟩ : syracuseStep 2670995 = 4006493) B4006493
theorem B3752345 : Blo 658307 3752345 := bstep (se 2 (by rfl) ⟨1407129, by rfl⟩ : syracuseStep 3752345 = 2814259) B2814259
theorem B836011 : Blo 658307 836011 := bstep (se 1 (by rfl) ⟨627008, by rfl⟩ : syracuseStep 836011 = 1254017) B1254017
theorem B4014521 : Blo 658307 4014521 := bstep (se 2 (by rfl) ⟨1505445, by rfl⟩ : syracuseStep 4014521 = 3010891) B3010891
theorem B836239 : Blo 658307 836239 := bstep (se 1 (by rfl) ⟨627179, by rfl⟩ : syracuseStep 836239 = 1254359) B1254359
theorem B5653637 : Blo 658307 5653637 := bstep (se 4 (by rfl) ⟨530028, by rfl⟩ : syracuseStep 5653637 = 1060057) B1060057
theorem B1885331 : Blo 658307 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B836983 : Blo 658307 836983 := bstep (se 1 (by rfl) ⟨627737, by rfl⟩ : syracuseStep 836983 = 1255475) B1255475
theorem B2508185 : Blo 658307 2508185 := bstep (se 2 (by rfl) ⟨940569, by rfl⟩ : syracuseStep 2508185 = 1881139) B1881139
theorem B7521821 : Blo 658307 7521821 := bstep (se 3 (by rfl) ⟨1410341, by rfl⟩ : syracuseStep 7521821 = 2820683) B2820683
theorem B2901547 : Blo 658307 2901547 := bstep (se 1 (by rfl) ⟨2176160, by rfl⟩ : syracuseStep 2901547 = 4352321) B4352321
theorem B3163735 : Blo 658307 3163735 := bstep (se 1 (by rfl) ⟨2372801, by rfl⟩ : syracuseStep 3163735 = 4745603) B4745603
theorem B837307 : Blo 658307 837307 := bstep (se 1 (by rfl) ⟨627980, by rfl⟩ : syracuseStep 837307 = 1255961) B1255961
theorem B1689355 : Blo 658307 1689355 := bstep (se 1 (by rfl) ⟨1267016, by rfl⟩ : syracuseStep 1689355 = 2534033) B2534033
theorem B2148211 : Blo 658307 2148211 := bstep (se 1 (by rfl) ⟨1611158, by rfl⟩ : syracuseStep 2148211 = 3222317) B3222317
theorem B7129133 : Blo 658307 7129133 := bstep (se 3 (by rfl) ⟨1336712, by rfl⟩ : syracuseStep 7129133 = 2673425) B2673425
theorem B1132663 : Blo 658307 1132663 := bstep (se 1 (by rfl) ⟨849497, by rfl⟩ : syracuseStep 1132663 = 1698995) B1698995
theorem B837803 : Blo 658307 837803 := bstep (se 1 (by rfl) ⟨628352, by rfl⟩ : syracuseStep 837803 = 1256705) B1256705
theorem B4770029 : Blo 658307 4770029 := bstep (se 3 (by rfl) ⟨894380, by rfl⟩ : syracuseStep 4770029 = 1788761) B1788761
theorem B1657273 : Blo 658307 1657273 := bstep (se 2 (by rfl) ⟨621477, by rfl⟩ : syracuseStep 1657273 = 1242955) B1242955
theorem B1001975 : Blo 658307 1001975 := bstep (se 1 (by rfl) ⟨751481, by rfl⟩ : syracuseStep 1001975 = 1502963) B1502963
theorem B4016947 : Blo 658307 4016947 := bstep (se 1 (by rfl) ⟨3012710, by rfl⟩ : syracuseStep 4016947 = 6025421) B6025421
theorem B8015021 : Blo 658307 8015021 := bstep (se 3 (by rfl) ⟨1502816, by rfl⟩ : syracuseStep 8015021 = 3005633) B3005633
theorem B740623 : Blo 658307 740623 := bstep (se 1 (by rfl) ⟨555467, by rfl⟩ : syracuseStep 740623 = 1110935) B1110935
theorem B8572517 : Blo 658307 8572517 := bstep (se 4 (by rfl) ⟨803673, by rfl⟩ : syracuseStep 8572517 = 1607347) B1607347
theorem B1101431 : Blo 658307 1101431 := bstep (se 1 (by rfl) ⟨826073, by rfl⟩ : syracuseStep 1101431 = 1652147) B1652147
theorem B2707145 : Blo 658307 2707145 := bstep (se 2 (by rfl) ⟨1015179, by rfl⟩ : syracuseStep 2707145 = 2030359) B2030359
theorem B741127 : Blo 658307 741127 := bstep (se 1 (by rfl) ⟨555845, by rfl⟩ : syracuseStep 741127 = 1111691) B1111691
theorem B15257393 : Blo 658307 15257393 := bstep (se 2 (by rfl) ⟨5721522, by rfl⟩ : syracuseStep 15257393 = 11443045) B11443045
theorem B14241653 : Blo 658307 14241653 := bstep (se 5 (by rfl) ⟨667577, by rfl⟩ : syracuseStep 14241653 = 1335155) B1335155
theorem B741307 : Blo 658307 741307 := bstep (se 1 (by rfl) ⟨555980, by rfl⟩ : syracuseStep 741307 = 1111961) B1111961
theorem B10735733 : Blo 658307 10735733 := bstep (se 5 (by rfl) ⟨503237, by rfl⟩ : syracuseStep 10735733 = 1006475) B1006475
theorem B938155 : Blo 658307 938155 := bstep (se 1 (by rfl) ⟨703616, by rfl⟩ : syracuseStep 938155 = 1407233) B1407233
theorem B741775 : Blo 658307 741775 := bstep (se 1 (by rfl) ⟨556331, by rfl⟩ : syracuseStep 741775 = 1112663) B1112663
theorem B6771377 : Blo 658307 6771377 := bstep (se 2 (by rfl) ⟨2539266, by rfl⟩ : syracuseStep 6771377 = 5078533) B5078533
theorem B742279 : Blo 658307 742279 := bstep (se 1 (by rfl) ⟨556709, by rfl⟩ : syracuseStep 742279 = 1113419) B1113419
theorem B2511769 : Blo 658307 2511769 := bstep (se 2 (by rfl) ⟨941913, by rfl⟩ : syracuseStep 2511769 = 1883827) B1883827
theorem B3560395 : Blo 658307 3560395 := bstep (se 1 (by rfl) ⟨2670296, by rfl⟩ : syracuseStep 3560395 = 5340593) B5340593
theorem B3167255 : Blo 658307 3167255 := bstep (se 1 (by rfl) ⟨2375441, by rfl⟩ : syracuseStep 3167255 = 4750883) B4750883
theorem B742459 : Blo 658307 742459 := bstep (se 1 (by rfl) ⟨556844, by rfl⟩ : syracuseStep 742459 = 1113689) B1113689
theorem B2118743 : Blo 658307 2118743 := bstep (se 1 (by rfl) ⟨1589057, by rfl⟩ : syracuseStep 2118743 = 3178115) B3178115
theorem B3757175 : Blo 658307 3757175 := bstep (se 1 (by rfl) ⟨2817881, by rfl⟩ : syracuseStep 3757175 = 5635763) B5635763
theorem B2512073 : Blo 658307 2512073 := bstep (se 2 (by rfl) ⟨942027, by rfl⟩ : syracuseStep 2512073 = 1884055) B1884055
theorem B2610413 : Blo 658307 2610413 := bstep (se 3 (by rfl) ⟨489452, by rfl⟩ : syracuseStep 2610413 = 978905) B978905
theorem B939271 : Blo 658307 939271 := bstep (se 1 (by rfl) ⟨704453, by rfl⟩ : syracuseStep 939271 = 1408907) B1408907
theorem B5363003 : Blo 658307 5363003 := bstep (se 1 (by rfl) ⟨4022252, by rfl⟩ : syracuseStep 5363003 = 8044505) B8044505
theorem B3757427 : Blo 658307 3757427 := bstep (se 1 (by rfl) ⟨2818070, by rfl⟩ : syracuseStep 3757427 = 5636141) B5636141
theorem B742927 : Blo 658307 742927 := bstep (se 1 (by rfl) ⟨557195, by rfl⟩ : syracuseStep 742927 = 1114391) B1114391
theorem B7526195 : Blo 658307 7526195 := bstep (se 1 (by rfl) ⟨5644646, by rfl⟩ : syracuseStep 7526195 = 11289293) B11289293
theorem B2676539 : Blo 658307 2676539 := bstep (se 1 (by rfl) ⟨2007404, by rfl⟩ : syracuseStep 2676539 = 4014809) B4014809
theorem B743431 : Blo 658307 743431 := bstep (se 1 (by rfl) ⟨557573, by rfl⟩ : syracuseStep 743431 = 1115147) B1115147
theorem B940091 : Blo 658307 940091 := bstep (se 1 (by rfl) ⟨705068, by rfl⟩ : syracuseStep 940091 = 1410137) B1410137
theorem B2513015 : Blo 658307 2513015 := bstep (se 1 (by rfl) ⟨1884761, by rfl⟩ : syracuseStep 2513015 = 3769523) B3769523
theorem B743611 : Blo 658307 743611 := bstep (se 1 (by rfl) ⟨557708, by rfl⟩ : syracuseStep 743611 = 1115417) B1115417
theorem B5626057 : Blo 658307 5626057 := bstep (se 2 (by rfl) ⟨2109771, by rfl⟩ : syracuseStep 5626057 = 4219543) B4219543
theorem B6347153 : Blo 658307 6347153 := bstep (se 2 (by rfl) ⟨2380182, by rfl⟩ : syracuseStep 6347153 = 4760365) B4760365
theorem B12704147 : Blo 658307 12704147 := bstep (se 1 (by rfl) ⟨9528110, by rfl⟩ : syracuseStep 12704147 = 19056221) B19056221
theorem B744079 : Blo 658307 744079 := bstep (se 1 (by rfl) ⟨558059, by rfl⟩ : syracuseStep 744079 = 1116119) B1116119
theorem B940729 : Blo 658307 940729 := bstep (se 2 (by rfl) ⟨352773, by rfl⟩ : syracuseStep 940729 = 705547) B705547
theorem B3758885 : Blo 658307 3758885 := bstep (se 4 (by rfl) ⟨352395, by rfl⟩ : syracuseStep 3758885 = 704791) B704791
theorem B940843 : Blo 658307 940843 := bstep (se 1 (by rfl) ⟨705632, by rfl⟩ : syracuseStep 940843 = 1411265) B1411265
theorem B941071 : Blo 658307 941071 := bstep (se 1 (by rfl) ⟨705803, by rfl⟩ : syracuseStep 941071 = 1411607) B1411607
theorem B3333149 : Blo 658307 3333149 := bstep (se 3 (by rfl) ⟨624965, by rfl⟩ : syracuseStep 3333149 = 1249931) B1249931
theorem B4512829 : Blo 658307 4512829 := bstep (se 3 (by rfl) ⟨846155, by rfl⟩ : syracuseStep 4512829 = 1692311) B1692311
theorem B2513987 : Blo 658307 2513987 := bstep (se 1 (by rfl) ⟨1885490, by rfl⟩ : syracuseStep 2513987 = 3770981) B3770981
theorem B744583 : Blo 658307 744583 := bstep (se 1 (by rfl) ⟨558437, by rfl⟩ : syracuseStep 744583 = 1116875) B1116875
theorem B744763 : Blo 658307 744763 := bstep (se 1 (by rfl) ⟨558572, by rfl⟩ : syracuseStep 744763 = 1117145) B1117145
theorem B3333635 : Blo 658307 3333635 := bstep (se 1 (by rfl) ⟨2500226, by rfl⟩ : syracuseStep 3333635 = 5000453) B5000453
theorem B1072775 : Blo 658307 1072775 := bstep (se 1 (by rfl) ⟨804581, by rfl⟩ : syracuseStep 1072775 = 1609163) B1609163
theorem B3759817 : Blo 658307 3759817 := bstep (se 2 (by rfl) ⟨1409931, by rfl⟩ : syracuseStep 3759817 = 2819863) B2819863
theorem B941959 : Blo 658307 941959 := bstep (se 1 (by rfl) ⟨706469, by rfl⟩ : syracuseStep 941959 = 1412939) B1412939
theorem B2383991 : Blo 658307 2383991 := bstep (se 1 (by rfl) ⟨1787993, by rfl⟩ : syracuseStep 2383991 = 3575987) B3575987
theorem B942455 : Blo 658307 942455 := bstep (se 1 (by rfl) ⟨706841, by rfl⟩ : syracuseStep 942455 = 1413683) B1413683
theorem B4023175 : Blo 658307 4023175 := bstep (se 1 (by rfl) ⟨3017381, by rfl⟩ : syracuseStep 4023175 = 6034763) B6034763
theorem B844843 : Blo 658307 844843 := bstep (se 1 (by rfl) ⟨633632, by rfl⟩ : syracuseStep 844843 = 1267265) B1267265
theorem B3335255 : Blo 658307 3335255 := bstep (se 1 (by rfl) ⟨2501441, by rfl⟩ : syracuseStep 3335255 = 5002883) B5002883
theorem B40592771 : Blo 658307 40592771 := bstep (se 1 (by rfl) ⟨30444578, by rfl⟩ : syracuseStep 40592771 = 60889157) B60889157
theorem B3171869 : Blo 658307 3171869 := bstep (se 3 (by rfl) ⟨594725, by rfl⟩ : syracuseStep 3171869 = 1189451) B1189451
theorem B3335741 : Blo 658307 3335741 := bstep (se 3 (by rfl) ⟨625451, by rfl⟩ : syracuseStep 3335741 = 1250903) B1250903
theorem B2221883 : Blo 658307 2221883 := bstep (se 1 (by rfl) ⟨1666412, by rfl⟩ : syracuseStep 2221883 = 3332825) B3332825
theorem B5007257 : Blo 658307 5007257 := bstep (se 2 (by rfl) ⟨1877721, by rfl⟩ : syracuseStep 5007257 = 3755443) B3755443
theorem B2222369 : Blo 658307 2222369 := bstep (se 2 (by rfl) ⟨833388, by rfl⟩ : syracuseStep 2222369 = 1666777) B1666777
theorem B12839467 : Blo 658307 12839467 := bstep (se 1 (by rfl) ⟨9629600, by rfl⟩ : syracuseStep 12839467 = 19259201) B19259201
theorem B2419267 : Blo 658307 2419267 := bstep (se 1 (by rfl) ⟨1814450, by rfl⟩ : syracuseStep 2419267 = 3628901) B3628901
theorem B2222963 : Blo 658307 2222963 := bstep (se 1 (by rfl) ⟨1667222, by rfl⟩ : syracuseStep 2222963 = 3334445) B3334445
theorem B6351767 : Blo 658307 6351767 := bstep (se 1 (by rfl) ⟨4763825, by rfl⟩ : syracuseStep 6351767 = 9527651) B9527651
theorem B3009433 : Blo 658307 3009433 := bstep (se 2 (by rfl) ⟨1128537, by rfl⟩ : syracuseStep 3009433 = 2257075) B2257075
theorem B3337523 : Blo 658307 3337523 := bstep (se 1 (by rfl) ⟨2503142, by rfl⟩ : syracuseStep 3337523 = 5006285) B5006285
theorem B1699187 : Blo 658307 1699187 := bstep (se 1 (by rfl) ⟨1274390, by rfl⟩ : syracuseStep 1699187 = 2548781) B2548781
theorem B2256281 : Blo 658307 2256281 := bstep (se 2 (by rfl) ⟨846105, by rfl⟩ : syracuseStep 2256281 = 1692211) B1692211
theorem B97643981 : Blo 658307 97643981 := bstep (se 3 (by rfl) ⟨18308246, by rfl⟩ : syracuseStep 97643981 = 36616493) B36616493
theorem B3337847 : Blo 658307 3337847 := bstep (se 1 (by rfl) ⟨2503385, by rfl⟩ : syracuseStep 3337847 = 5006771) B5006771
theorem B847531 : Blo 658307 847531 := bstep (se 1 (by rfl) ⟨635648, by rfl⟩ : syracuseStep 847531 = 1271297) B1271297
theorem B5009201 : Blo 658307 5009201 := bstep (se 2 (by rfl) ⟨1878450, by rfl⟩ : syracuseStep 5009201 = 3756901) B3756901
theorem B2813849 : Blo 658307 2813849 := bstep (se 2 (by rfl) ⟨1055193, by rfl⟩ : syracuseStep 2813849 = 2110387) B2110387
theorem B5369753 : Blo 658307 5369753 := bstep (se 2 (by rfl) ⟨2013657, by rfl⟩ : syracuseStep 5369753 = 4027315) B4027315
theorem B3174329 : Blo 658307 3174329 := bstep (se 2 (by rfl) ⟨1190373, by rfl⟩ : syracuseStep 3174329 = 2380747) B2380747
theorem B84537589 : Blo 658307 84537589 := bstep (se 5 (by rfl) ⟨3962699, by rfl⟩ : syracuseStep 84537589 = 7925399) B7925399
theorem B6025681 : Blo 658307 6025681 := bstep (se 2 (by rfl) ⟨2259630, by rfl⟩ : syracuseStep 6025681 = 4519261) B4519261
theorem B3338819 : Blo 658307 3338819 := bstep (se 1 (by rfl) ⟨2504114, by rfl⟩ : syracuseStep 3338819 = 5008229) B5008229
theorem B1667699 : Blo 658307 1667699 := bstep (se 1 (by rfl) ⟨1250774, by rfl⟩ : syracuseStep 1667699 = 2501549) B2501549
theorem B3339143 : Blo 658307 3339143 := bstep (se 1 (by rfl) ⟨2504357, by rfl⟩ : syracuseStep 3339143 = 5008715) B5008715
theorem B1340345 : Blo 658307 1340345 := bstep (se 2 (by rfl) ⟨502629, by rfl⟩ : syracuseStep 1340345 = 1005259) B1005259
theorem B914377 : Blo 658307 914377 := bstep (se 2 (by rfl) ⟨342891, by rfl⟩ : syracuseStep 914377 = 685783) B685783
theorem B1668215 : Blo 658307 1668215 := bstep (se 1 (by rfl) ⟨1251161, by rfl⟩ : syracuseStep 1668215 = 2502323) B2502323
theorem B1111225 : Blo 658307 1111225 := bstep (se 2 (by rfl) ⟨416709, by rfl⟩ : syracuseStep 1111225 = 833419) B833419
theorem B1471777 : Blo 658307 1471777 := bstep (se 2 (by rfl) ⟨551916, by rfl⟩ : syracuseStep 1471777 = 1103833) B1103833
theorem B3765649 : Blo 658307 3765649 := bstep (se 2 (by rfl) ⟨1412118, by rfl⟩ : syracuseStep 3765649 = 2824237) B2824237
theorem B2225555 : Blo 658307 2225555 := bstep (se 1 (by rfl) ⟨1669166, by rfl⟩ : syracuseStep 2225555 = 3338333) B3338333
theorem B1111927 : Blo 658307 1111927 := bstep (se 1 (by rfl) ⟨833945, by rfl⟩ : syracuseStep 1111927 = 1667891) B1667891
theorem B1341319 : Blo 658307 1341319 := bstep (se 1 (by rfl) ⟨1005989, by rfl⟩ : syracuseStep 1341319 = 2011979) B2011979
theorem B3569629 : Blo 658307 3569629 := bstep (se 3 (by rfl) ⟨669305, by rfl⟩ : syracuseStep 3569629 = 1338611) B1338611
theorem B1112123 : Blo 658307 1112123 := bstep (se 1 (by rfl) ⟨834092, by rfl⟩ : syracuseStep 1112123 = 1668185) B1668185
theorem B1669207 : Blo 658307 1669207 := bstep (se 1 (by rfl) ⟨1251905, by rfl⟩ : syracuseStep 1669207 = 2503811) B2503811
theorem B1669511 : Blo 658307 1669511 := bstep (se 1 (by rfl) ⟨1252133, by rfl⟩ : syracuseStep 1669511 = 2504267) B2504267
theorem B1112521 : Blo 658307 1112521 := bstep (se 2 (by rfl) ⟨417195, by rfl⟩ : syracuseStep 1112521 = 834391) B834391
theorem B1669643 : Blo 658307 1669643 := bstep (se 1 (by rfl) ⟨1252232, by rfl⟩ : syracuseStep 1669643 = 2504465) B2504465
theorem B2226959 : Blo 658307 2226959 := bstep (se 1 (by rfl) ⟨1670219, by rfl⟩ : syracuseStep 2226959 = 3340439) B3340439
theorem B2816977 : Blo 658307 2816977 := bstep (se 2 (by rfl) ⟨1056366, by rfl⟩ : syracuseStep 2816977 = 2112733) B2112733
theorem B1670159 : Blo 658307 1670159 := bstep (se 1 (by rfl) ⟨1252619, by rfl⟩ : syracuseStep 1670159 = 2505239) B2505239
theorem B2227229 : Blo 658307 2227229 := bstep (se 3 (by rfl) ⟨417605, by rfl⟩ : syracuseStep 2227229 = 835211) B835211
theorem B1113223 : Blo 658307 1113223 := bstep (se 1 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 1113223 = 1669835) B1669835
theorem B1670291 : Blo 658307 1670291 := bstep (se 1 (by rfl) ⟨1252718, by rfl⟩ : syracuseStep 1670291 = 2505437) B2505437
theorem B4226363 : Blo 658307 4226363 := bstep (se 1 (by rfl) ⟨3169772, by rfl⟩ : syracuseStep 4226363 = 6339545) B6339545
theorem B5144141 : Blo 658307 5144141 := bstep (se 3 (by rfl) ⟨964526, by rfl⟩ : syracuseStep 5144141 = 1929053) B1929053
theorem B3768065 : Blo 658307 3768065 := bstep (se 2 (by rfl) ⟨1413024, by rfl⟩ : syracuseStep 3768065 = 2826049) B2826049
theorem B1113871 : Blo 658307 1113871 := bstep (se 1 (by rfl) ⟨835403, by rfl⟩ : syracuseStep 1113871 = 1670807) B1670807
theorem B1507105 : Blo 658307 1507105 := bstep (se 2 (by rfl) ⟨565164, by rfl⟩ : syracuseStep 1507105 = 1130329) B1130329
theorem B3178385 : Blo 658307 3178385 := bstep (se 2 (by rfl) ⟨1191894, by rfl⟩ : syracuseStep 3178385 = 2383789) B2383789
theorem B4751257 : Blo 658307 4751257 := bstep (se 2 (by rfl) ⟨1781721, by rfl⟩ : syracuseStep 4751257 = 3563443) B3563443
theorem B1114121 : Blo 658307 1114121 := bstep (se 2 (by rfl) ⟨417795, by rfl⟩ : syracuseStep 1114121 = 835591) B835591
theorem B1114283 : Blo 658307 1114283 := bstep (se 1 (by rfl) ⟨835712, by rfl⟩ : syracuseStep 1114283 = 1671425) B1671425
theorem B2228471 : Blo 658307 2228471 := bstep (se 1 (by rfl) ⟨1671353, by rfl⟩ : syracuseStep 2228471 = 3342707) B3342707
theorem B4227389 : Blo 658307 4227389 := bstep (se 3 (by rfl) ⟨792635, by rfl⟩ : syracuseStep 4227389 = 1585271) B1585271
theorem B4063769 : Blo 658307 4063769 := bstep (se 2 (by rfl) ⟨1523913, by rfl⟩ : syracuseStep 4063769 = 3047827) B3047827
theorem B1114681 : Blo 658307 1114681 := bstep (se 2 (by rfl) ⟨418005, by rfl⟩ : syracuseStep 1114681 = 836011) B836011
theorem B2228795 : Blo 658307 2228795 := bstep (se 1 (by rfl) ⟨1671596, by rfl⟩ : syracuseStep 2228795 = 3343193) B3343193
theorem B1114823 : Blo 658307 1114823 := bstep (se 1 (by rfl) ⟨836117, by rfl⟩ : syracuseStep 1114823 = 1672235) B1672235
theorem B3769091 : Blo 658307 3769091 := bstep (se 1 (by rfl) ⟨2826818, by rfl⟩ : syracuseStep 3769091 = 5653637) B5653637
theorem B2229065 : Blo 658307 2229065 := bstep (se 2 (by rfl) ⟨835899, by rfl⟩ : syracuseStep 2229065 = 1671799) B1671799
theorem B1114985 : Blo 658307 1114985 := bstep (se 2 (by rfl) ⟨418119, by rfl⟩ : syracuseStep 1114985 = 836239) B836239
theorem B1672123 : Blo 658307 1672123 := bstep (se 1 (by rfl) ⟨1254092, by rfl⟩ : syracuseStep 1672123 = 2508185) B2508185
theorem B5014547 : Blo 658307 5014547 := bstep (se 1 (by rfl) ⟨3760910, by rfl⟩ : syracuseStep 5014547 = 7521821) B7521821
theorem B1115383 : Blo 658307 1115383 := bstep (se 1 (by rfl) ⟨836537, by rfl⟩ : syracuseStep 1115383 = 1673075) B1673075
theorem B4752755 : Blo 658307 4752755 := bstep (se 1 (by rfl) ⟨3564566, by rfl⟩ : syracuseStep 4752755 = 7129133) B7129133
theorem B5637539 : Blo 658307 5637539 := bstep (se 1 (by rfl) ⟨4228154, by rfl⟩ : syracuseStep 5637539 = 8456309) B8456309
theorem B1115579 : Blo 658307 1115579 := bstep (se 1 (by rfl) ⟨836684, by rfl⟩ : syracuseStep 1115579 = 1673369) B1673369
theorem B3180019 : Blo 658307 3180019 := bstep (se 1 (by rfl) ⟨2385014, by rfl⟩ : syracuseStep 3180019 = 4770029) B4770029
theorem B1115687 : Blo 658307 1115687 := bstep (se 1 (by rfl) ⟨836765, by rfl⟩ : syracuseStep 1115687 = 1673531) B1673531
theorem B1115977 : Blo 658307 1115977 := bstep (se 2 (by rfl) ⟨418491, by rfl⟩ : syracuseStep 1115977 = 836983) B836983
theorem B1116011 : Blo 658307 1116011 := bstep (se 1 (by rfl) ⟨837008, by rfl⟩ : syracuseStep 1116011 = 1674017) B1674017
theorem B2230199 : Blo 658307 2230199 := bstep (se 1 (by rfl) ⟨1672649, by rfl⟩ : syracuseStep 2230199 = 3345299) B3345299
theorem B3868729 : Blo 658307 3868729 := bstep (se 2 (by rfl) ⟨1450773, by rfl⟩ : syracuseStep 3868729 = 2901547) B2901547
theorem B5343347 : Blo 658307 5343347 := bstep (se 1 (by rfl) ⟨4007510, by rfl⟩ : syracuseStep 5343347 = 8015021) B8015021
theorem B1116409 : Blo 658307 1116409 := bstep (se 2 (by rfl) ⟨418653, by rfl⟩ : syracuseStep 1116409 = 837307) B837307
theorem B3344651 : Blo 658307 3344651 := bstep (se 1 (by rfl) ⟨2508488, by rfl⟩ : syracuseStep 3344651 = 5016977) B5016977
theorem B1804763 : Blo 658307 1804763 := bstep (se 1 (by rfl) ⟨1353572, by rfl⟩ : syracuseStep 1804763 = 2707145) B2707145
theorem B3574253 : Blo 658307 3574253 := bstep (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) B1340345
theorem B1116679 : Blo 658307 1116679 := bstep (se 1 (by rfl) ⟨837509, by rfl⟩ : syracuseStep 1116679 = 1675019) B1675019
theorem B2230793 : Blo 658307 2230793 := bstep (se 2 (by rfl) ⟨836547, by rfl⟩ : syracuseStep 2230793 = 1673095) B1673095
theorem B1510217 : Blo 658307 1510217 := bstep (se 2 (by rfl) ⟨566331, by rfl⟩ : syracuseStep 1510217 = 1132663) B1132663
theorem B658351 : Blo 658307 658351 := bstep (se 1 (by rfl) ⟨493763, by rfl⟩ : syracuseStep 658351 = 987527) B987527
theorem B1117111 : Blo 658307 1117111 := bstep (se 1 (by rfl) ⟨837833, by rfl⟩ : syracuseStep 1117111 = 1675667) B1675667
theorem B658375 : Blo 658307 658375 := bstep (se 1 (by rfl) ⟨493781, by rfl⟩ : syracuseStep 658375 = 987563) B987563
theorem B658395 : Blo 658307 658395 := bstep (se 1 (by rfl) ⟨493796, by rfl⟩ : syracuseStep 658395 = 987593) B987593
theorem B658471 : Blo 658307 658471 := bstep (se 1 (by rfl) ⟨493853, by rfl⟩ : syracuseStep 658471 = 987707) B987707
theorem B658511 : Blo 658307 658511 := bstep (se 1 (by rfl) ⟨493883, by rfl⟩ : syracuseStep 658511 = 987767) B987767
theorem B658527 : Blo 658307 658527 := bstep (se 1 (by rfl) ⟨493895, by rfl⟩ : syracuseStep 658527 = 987791) B987791
theorem B658555 : Blo 658307 658555 := bstep (se 1 (by rfl) ⟨493916, by rfl⟩ : syracuseStep 658555 = 987833) B987833
theorem B1117307 : Blo 658307 1117307 := bstep (se 1 (by rfl) ⟨837980, by rfl⟩ : syracuseStep 1117307 = 1675961) B1675961
theorem B658607 : Blo 658307 658607 := bstep (se 1 (by rfl) ⟨493955, by rfl⟩ : syracuseStep 658607 = 987911) B987911
theorem B658631 : Blo 658307 658631 := bstep (se 1 (by rfl) ⟨493973, by rfl⟩ : syracuseStep 658631 = 987947) B987947
theorem B658651 : Blo 658307 658651 := bstep (se 1 (by rfl) ⟨493988, by rfl⟩ : syracuseStep 658651 = 987977) B987977
theorem B2821367 : Blo 658307 2821367 := bstep (se 1 (by rfl) ⟨2116025, by rfl⟩ : syracuseStep 2821367 = 4232051) B4232051
theorem B658727 : Blo 658307 658727 := bstep (se 1 (by rfl) ⟨494045, by rfl⟩ : syracuseStep 658727 = 988091) B988091
theorem B658767 : Blo 658307 658767 := bstep (se 1 (by rfl) ⟨494075, by rfl⟩ : syracuseStep 658767 = 988151) B988151
theorem B658783 : Blo 658307 658783 := bstep (se 1 (by rfl) ⟨494087, by rfl⟩ : syracuseStep 658783 = 988175) B988175
theorem B2231657 : Blo 658307 2231657 := bstep (se 2 (by rfl) ⟨836871, by rfl⟩ : syracuseStep 2231657 = 1673743) B1673743
theorem B658811 : Blo 658307 658811 := bstep (se 1 (by rfl) ⟨494108, by rfl⟩ : syracuseStep 658811 = 988217) B988217
theorem B1412495 : Blo 658307 1412495 := bstep (se 1 (by rfl) ⟨1059371, by rfl⟩ : syracuseStep 1412495 = 2118743) B2118743
theorem B658863 : Blo 658307 658863 := bstep (se 1 (by rfl) ⟨494147, by rfl⟩ : syracuseStep 658863 = 988295) B988295
theorem B658887 : Blo 658307 658887 := bstep (se 1 (by rfl) ⟨494165, by rfl⟩ : syracuseStep 658887 = 988331) B988331
theorem B658907 : Blo 658307 658907 := bstep (se 1 (by rfl) ⟨494180, by rfl⟩ : syracuseStep 658907 = 988361) B988361
theorem B1674715 : Blo 658307 1674715 := bstep (se 1 (by rfl) ⟨1256036, by rfl⟩ : syracuseStep 1674715 = 2512073) B2512073
theorem B1740275 : Blo 658307 1740275 := bstep (se 1 (by rfl) ⟨1305206, by rfl⟩ : syracuseStep 1740275 = 2610413) B2610413
theorem B658983 : Blo 658307 658983 := bstep (se 1 (by rfl) ⟨494237, by rfl⟩ : syracuseStep 658983 = 988475) B988475
theorem B3575335 : Blo 658307 3575335 := bstep (se 1 (by rfl) ⟨2681501, by rfl⟩ : syracuseStep 3575335 = 5363003) B5363003
theorem B659023 : Blo 658307 659023 := bstep (se 1 (by rfl) ⟨494267, by rfl⟩ : syracuseStep 659023 = 988535) B988535
theorem B659039 : Blo 658307 659039 := bstep (se 1 (by rfl) ⟨494279, by rfl⟩ : syracuseStep 659039 = 988559) B988559
theorem B659067 : Blo 658307 659067 := bstep (se 1 (by rfl) ⟨494300, by rfl⟩ : syracuseStep 659067 = 988601) B988601
theorem B659119 : Blo 658307 659119 := bstep (se 1 (by rfl) ⟨494339, by rfl⟩ : syracuseStep 659119 = 988679) B988679
theorem B3346109 : Blo 658307 3346109 := bstep (se 3 (by rfl) ⟨627395, by rfl⟩ : syracuseStep 3346109 = 1254791) B1254791
theorem B659143 : Blo 658307 659143 := bstep (se 1 (by rfl) ⟨494357, by rfl⟩ : syracuseStep 659143 = 988715) B988715
theorem B659163 : Blo 658307 659163 := bstep (se 1 (by rfl) ⟨494372, by rfl⟩ : syracuseStep 659163 = 988745) B988745
theorem B659239 : Blo 658307 659239 := bstep (se 1 (by rfl) ⟨494429, by rfl⟩ : syracuseStep 659239 = 988859) B988859
theorem B659279 : Blo 658307 659279 := bstep (se 1 (by rfl) ⟨494459, by rfl⟩ : syracuseStep 659279 = 988919) B988919
theorem B659295 : Blo 658307 659295 := bstep (se 1 (by rfl) ⟨494471, by rfl⟩ : syracuseStep 659295 = 988943) B988943
theorem B3346271 : Blo 658307 3346271 := bstep (se 1 (by rfl) ⟨2509703, by rfl⟩ : syracuseStep 3346271 = 5019407) B5019407
theorem B18124661 : Blo 658307 18124661 := bstep (se 5 (by rfl) ⟨849593, by rfl⟩ : syracuseStep 18124661 = 1699187) B1699187
theorem B5017463 : Blo 658307 5017463 := bstep (se 1 (by rfl) ⟨3763097, by rfl⟩ : syracuseStep 5017463 = 7526195) B7526195
theorem B659323 : Blo 658307 659323 := bstep (se 1 (by rfl) ⟨494492, by rfl⟩ : syracuseStep 659323 = 988985) B988985
theorem B659375 : Blo 658307 659375 := bstep (se 1 (by rfl) ⟨494531, by rfl⟩ : syracuseStep 659375 = 989063) B989063
theorem B2232251 : Blo 658307 2232251 := bstep (se 1 (by rfl) ⟨1674188, by rfl⟩ : syracuseStep 2232251 = 3348377) B3348377
theorem B659399 : Blo 658307 659399 := bstep (se 1 (by rfl) ⟨494549, by rfl⟩ : syracuseStep 659399 = 989099) B989099
theorem B659419 : Blo 658307 659419 := bstep (se 1 (by rfl) ⟨494564, by rfl⟩ : syracuseStep 659419 = 989129) B989129
theorem B659495 : Blo 658307 659495 := bstep (se 1 (by rfl) ⟨494621, by rfl⟩ : syracuseStep 659495 = 989243) B989243
theorem B659535 : Blo 658307 659535 := bstep (se 1 (by rfl) ⟨494651, by rfl⟩ : syracuseStep 659535 = 989303) B989303
theorem B1675343 : Blo 658307 1675343 := bstep (se 1 (by rfl) ⟨1256507, by rfl⟩ : syracuseStep 1675343 = 2513015) B2513015
theorem B659551 : Blo 658307 659551 := bstep (se 1 (by rfl) ⟨494663, by rfl⟩ : syracuseStep 659551 = 989327) B989327
theorem B659579 : Blo 658307 659579 := bstep (se 1 (by rfl) ⟨494684, by rfl⟩ : syracuseStep 659579 = 989369) B989369
theorem B659631 : Blo 658307 659631 := bstep (se 1 (by rfl) ⟨494723, by rfl⟩ : syracuseStep 659631 = 989447) B989447
theorem B659655 : Blo 658307 659655 := bstep (se 1 (by rfl) ⟨494741, by rfl⟩ : syracuseStep 659655 = 989483) B989483
theorem B659675 : Blo 658307 659675 := bstep (se 1 (by rfl) ⟨494756, by rfl⟩ : syracuseStep 659675 = 989513) B989513
theorem B4231435 : Blo 658307 4231435 := bstep (se 1 (by rfl) ⟨3173576, by rfl⟩ : syracuseStep 4231435 = 6347153) B6347153
theorem B659751 : Blo 658307 659751 := bstep (se 1 (by rfl) ⟨494813, by rfl⟩ : syracuseStep 659751 = 989627) B989627
theorem B659791 : Blo 658307 659791 := bstep (se 1 (by rfl) ⟨494843, by rfl⟩ : syracuseStep 659791 = 989687) B989687
theorem B659807 : Blo 658307 659807 := bstep (se 1 (by rfl) ⟨494855, by rfl⟩ : syracuseStep 659807 = 989711) B989711
theorem B987497 : Blo 658307 987497 := bstep (se 2 (by rfl) ⟨370311, by rfl⟩ : syracuseStep 987497 = 740623) B740623
theorem B659835 : Blo 658307 659835 := bstep (se 1 (by rfl) ⟨494876, by rfl⟩ : syracuseStep 659835 = 989753) B989753
theorem B659887 : Blo 658307 659887 := bstep (se 1 (by rfl) ⟨494915, by rfl⟩ : syracuseStep 659887 = 989831) B989831
theorem B987575 : Blo 658307 987575 := bstep (se 1 (by rfl) ⟨740681, by rfl⟩ : syracuseStep 987575 = 1481363) B1481363
theorem B659911 : Blo 658307 659911 := bstep (se 1 (by rfl) ⟨494933, by rfl⟩ : syracuseStep 659911 = 989867) B989867
theorem B987611 : Blo 658307 987611 := bstep (se 1 (by rfl) ⟨740708, by rfl⟩ : syracuseStep 987611 = 1481417) B1481417
theorem B659931 : Blo 658307 659931 := bstep (se 1 (by rfl) ⟨494948, by rfl⟩ : syracuseStep 659931 = 989897) B989897
theorem B660007 : Blo 658307 660007 := bstep (se 1 (by rfl) ⟨495005, by rfl⟩ : syracuseStep 660007 = 990011) B990011
theorem B660047 : Blo 658307 660047 := bstep (se 1 (by rfl) ⟨495035, by rfl⟩ : syracuseStep 660047 = 990071) B990071
theorem B660063 : Blo 658307 660063 := bstep (se 1 (by rfl) ⟨495047, by rfl⟩ : syracuseStep 660063 = 990095) B990095
theorem B660091 : Blo 658307 660091 := bstep (se 1 (by rfl) ⟨495068, by rfl⟩ : syracuseStep 660091 = 990137) B990137
theorem B660143 : Blo 658307 660143 := bstep (se 1 (by rfl) ⟨495107, by rfl⟩ : syracuseStep 660143 = 990215) B990215
theorem B660167 : Blo 658307 660167 := bstep (se 1 (by rfl) ⟨495125, by rfl⟩ : syracuseStep 660167 = 990251) B990251
theorem B1675991 : Blo 658307 1675991 := bstep (se 1 (by rfl) ⟨1256993, by rfl⟩ : syracuseStep 1675991 = 2513987) B2513987
theorem B660187 : Blo 658307 660187 := bstep (se 1 (by rfl) ⟨495140, by rfl⟩ : syracuseStep 660187 = 990281) B990281
theorem B660263 : Blo 658307 660263 := bstep (se 1 (by rfl) ⟨495197, by rfl⟩ : syracuseStep 660263 = 990395) B990395
theorem B660303 : Blo 658307 660303 := bstep (se 1 (by rfl) ⟨495227, by rfl⟩ : syracuseStep 660303 = 990455) B990455
theorem B660319 : Blo 658307 660319 := bstep (se 1 (by rfl) ⟨495239, by rfl⟩ : syracuseStep 660319 = 990479) B990479
theorem B660347 : Blo 658307 660347 := bstep (se 1 (by rfl) ⟨495260, by rfl⟩ : syracuseStep 660347 = 990521) B990521
theorem B988079 : Blo 658307 988079 := bstep (se 1 (by rfl) ⟨741059, by rfl⟩ : syracuseStep 988079 = 1482119) B1482119
theorem B660399 : Blo 658307 660399 := bstep (se 1 (by rfl) ⟨495299, by rfl⟩ : syracuseStep 660399 = 990599) B990599
theorem B660423 : Blo 658307 660423 := bstep (se 1 (by rfl) ⟨495317, by rfl⟩ : syracuseStep 660423 = 990635) B990635
theorem B660443 : Blo 658307 660443 := bstep (se 1 (by rfl) ⟨495332, by rfl⟩ : syracuseStep 660443 = 990665) B990665
theorem B4756445 : Blo 658307 4756445 := bstep (se 3 (by rfl) ⟨891833, by rfl⟩ : syracuseStep 4756445 = 1783667) B1783667
theorem B1250311 : Blo 658307 1250311 := bstep (se 1 (by rfl) ⟨937733, by rfl⟩ : syracuseStep 1250311 = 1875467) B1875467
theorem B988169 : Blo 658307 988169 := bstep (se 2 (by rfl) ⟨370563, by rfl⟩ : syracuseStep 988169 = 741127) B741127
theorem B2036755 : Blo 658307 2036755 := bstep (se 1 (by rfl) ⟨1527566, by rfl⟩ : syracuseStep 2036755 = 3055133) B3055133
theorem B988199 : Blo 658307 988199 := bstep (se 1 (by rfl) ⟨741149, by rfl⟩ : syracuseStep 988199 = 1482299) B1482299
theorem B660519 : Blo 658307 660519 := bstep (se 1 (by rfl) ⟨495389, by rfl⟩ : syracuseStep 660519 = 990779) B990779
theorem B660559 : Blo 658307 660559 := bstep (se 1 (by rfl) ⟨495419, by rfl⟩ : syracuseStep 660559 = 990839) B990839
theorem B660575 : Blo 658307 660575 := bstep (se 1 (by rfl) ⟨495431, by rfl⟩ : syracuseStep 660575 = 990863) B990863
theorem B988283 : Blo 658307 988283 := bstep (se 1 (by rfl) ⟨741212, by rfl⟩ : syracuseStep 988283 = 1482425) B1482425
theorem B660603 : Blo 658307 660603 := bstep (se 1 (by rfl) ⟨495452, by rfl⟩ : syracuseStep 660603 = 990905) B990905
theorem B660655 : Blo 658307 660655 := bstep (se 1 (by rfl) ⟨495491, by rfl⟩ : syracuseStep 660655 = 990983) B990983
theorem B660679 : Blo 658307 660679 := bstep (se 1 (by rfl) ⟨495509, by rfl⟩ : syracuseStep 660679 = 991019) B991019
theorem B30545099 : Blo 658307 30545099 := bstep (se 1 (by rfl) ⟨22908824, by rfl⟩ : syracuseStep 30545099 = 45817649) B45817649
theorem B660699 : Blo 658307 660699 := bstep (se 1 (by rfl) ⟨495524, by rfl⟩ : syracuseStep 660699 = 991049) B991049
theorem B10687733 : Blo 658307 10687733 := bstep (se 5 (by rfl) ⟨500987, by rfl⟩ : syracuseStep 10687733 = 1001975) B1001975
theorem B988409 : Blo 658307 988409 := bstep (se 2 (by rfl) ⟨370653, by rfl⟩ : syracuseStep 988409 = 741307) B741307
theorem B660775 : Blo 658307 660775 := bstep (se 1 (by rfl) ⟨495581, by rfl⟩ : syracuseStep 660775 = 991163) B991163
theorem B660815 : Blo 658307 660815 := bstep (se 1 (by rfl) ⟨495611, by rfl⟩ : syracuseStep 660815 = 991223) B991223
theorem B988511 : Blo 658307 988511 := bstep (se 1 (by rfl) ⟨741383, by rfl⟩ : syracuseStep 988511 = 1482767) B1482767
theorem B660831 : Blo 658307 660831 := bstep (se 1 (by rfl) ⟨495623, by rfl⟩ : syracuseStep 660831 = 991247) B991247
theorem B988523 : Blo 658307 988523 := bstep (se 1 (by rfl) ⟨741392, by rfl⟩ : syracuseStep 988523 = 1482785) B1482785
theorem B660859 : Blo 658307 660859 := bstep (se 1 (by rfl) ⟨495644, by rfl⟩ : syracuseStep 660859 = 991289) B991289
theorem B660911 : Blo 658307 660911 := bstep (se 1 (by rfl) ⟨495683, by rfl⟩ : syracuseStep 660911 = 991367) B991367
theorem B660935 : Blo 658307 660935 := bstep (se 1 (by rfl) ⟨495701, by rfl⟩ : syracuseStep 660935 = 991403) B991403
theorem B660955 : Blo 658307 660955 := bstep (se 1 (by rfl) ⟨495716, by rfl⟩ : syracuseStep 660955 = 991433) B991433
theorem B661031 : Blo 658307 661031 := bstep (se 1 (by rfl) ⟨495773, by rfl⟩ : syracuseStep 661031 = 991547) B991547
theorem B1250873 : Blo 658307 1250873 := bstep (se 2 (by rfl) ⟨469077, by rfl⟩ : syracuseStep 1250873 = 938155) B938155
theorem B988751 : Blo 658307 988751 := bstep (se 1 (by rfl) ⟨741563, by rfl⟩ : syracuseStep 988751 = 1483127) B1483127
theorem B661071 : Blo 658307 661071 := bstep (se 1 (by rfl) ⟨495803, by rfl⟩ : syracuseStep 661071 = 991607) B991607
theorem B661087 : Blo 658307 661087 := bstep (se 1 (by rfl) ⟨495815, by rfl⟩ : syracuseStep 661087 = 991631) B991631
theorem B661115 : Blo 658307 661115 := bstep (se 1 (by rfl) ⟨495836, by rfl⟩ : syracuseStep 661115 = 991673) B991673
theorem B2233979 : Blo 658307 2233979 := bstep (se 1 (by rfl) ⟨1675484, by rfl⟩ : syracuseStep 2233979 = 3350969) B3350969
theorem B661167 : Blo 658307 661167 := bstep (se 1 (by rfl) ⟨495875, by rfl⟩ : syracuseStep 661167 = 991751) B991751
theorem B988871 : Blo 658307 988871 := bstep (se 1 (by rfl) ⟨741653, by rfl⟩ : syracuseStep 988871 = 1483307) B1483307
theorem B661191 : Blo 658307 661191 := bstep (se 1 (by rfl) ⟨495893, by rfl⟩ : syracuseStep 661191 = 991787) B991787
theorem B661211 : Blo 658307 661211 := bstep (se 1 (by rfl) ⟨495908, by rfl⟩ : syracuseStep 661211 = 991817) B991817
theorem B2234141 : Blo 658307 2234141 := bstep (se 3 (by rfl) ⟨418901, by rfl⟩ : syracuseStep 2234141 = 837803) B837803
theorem B661287 : Blo 658307 661287 := bstep (se 1 (by rfl) ⟨495965, by rfl⟩ : syracuseStep 661287 = 991931) B991931
theorem B661327 : Blo 658307 661327 := bstep (se 1 (by rfl) ⟨495995, by rfl⟩ : syracuseStep 661327 = 991991) B991991
theorem B661343 : Blo 658307 661343 := bstep (se 1 (by rfl) ⟨496007, by rfl⟩ : syracuseStep 661343 = 992015) B992015
theorem B989033 : Blo 658307 989033 := bstep (se 2 (by rfl) ⟨370887, by rfl⟩ : syracuseStep 989033 = 741775) B741775
theorem B661371 : Blo 658307 661371 := bstep (se 1 (by rfl) ⟨496028, by rfl⟩ : syracuseStep 661371 = 992057) B992057
theorem B661423 : Blo 658307 661423 := bstep (se 1 (by rfl) ⟨496067, by rfl⟩ : syracuseStep 661423 = 992135) B992135
theorem B989111 : Blo 658307 989111 := bstep (se 1 (by rfl) ⟨741833, by rfl⟩ : syracuseStep 989111 = 1483667) B1483667
theorem B8034241 : Blo 658307 8034241 := bstep (se 2 (by rfl) ⟨3012840, by rfl⟩ : syracuseStep 8034241 = 6025681) B6025681
theorem B661447 : Blo 658307 661447 := bstep (se 1 (by rfl) ⟨496085, by rfl⟩ : syracuseStep 661447 = 992171) B992171
theorem B989147 : Blo 658307 989147 := bstep (se 1 (by rfl) ⟨741860, by rfl⟩ : syracuseStep 989147 = 1483721) B1483721
theorem B661467 : Blo 658307 661467 := bstep (se 1 (by rfl) ⟨496100, by rfl⟩ : syracuseStep 661467 = 992201) B992201
theorem B661543 : Blo 658307 661543 := bstep (se 1 (by rfl) ⟨496157, by rfl⟩ : syracuseStep 661543 = 992315) B992315
theorem B661583 : Blo 658307 661583 := bstep (se 1 (by rfl) ⟨496187, by rfl⟩ : syracuseStep 661583 = 992375) B992375
theorem B661599 : Blo 658307 661599 := bstep (se 1 (by rfl) ⟨496199, by rfl⟩ : syracuseStep 661599 = 992399) B992399
theorem B2824307 : Blo 658307 2824307 := bstep (se 1 (by rfl) ⟨2118230, by rfl⟩ : syracuseStep 2824307 = 4236461) B4236461
theorem B661627 : Blo 658307 661627 := bstep (se 1 (by rfl) ⟨496220, by rfl⟩ : syracuseStep 661627 = 992441) B992441
theorem B661679 : Blo 658307 661679 := bstep (se 1 (by rfl) ⟨496259, by rfl⟩ : syracuseStep 661679 = 992519) B992519
theorem B661703 : Blo 658307 661703 := bstep (se 1 (by rfl) ⟨496277, by rfl⟩ : syracuseStep 661703 = 992555) B992555
theorem B661723 : Blo 658307 661723 := bstep (se 1 (by rfl) ⟨496292, by rfl⟩ : syracuseStep 661723 = 992585) B992585
theorem B661799 : Blo 658307 661799 := bstep (se 1 (by rfl) ⟨496349, by rfl⟩ : syracuseStep 661799 = 992699) B992699
theorem B661839 : Blo 658307 661839 := bstep (se 1 (by rfl) ⟨496379, by rfl⟩ : syracuseStep 661839 = 992759) B992759
theorem B661855 : Blo 658307 661855 := bstep (se 1 (by rfl) ⟨496391, by rfl⟩ : syracuseStep 661855 = 992783) B992783
theorem B661883 : Blo 658307 661883 := bstep (se 1 (by rfl) ⟨496412, by rfl⟩ : syracuseStep 661883 = 992825) B992825
theorem B989615 : Blo 658307 989615 := bstep (se 1 (by rfl) ⟨742211, by rfl⟩ : syracuseStep 989615 = 1484423) B1484423
theorem B661935 : Blo 658307 661935 := bstep (se 1 (by rfl) ⟨496451, by rfl⟩ : syracuseStep 661935 = 992903) B992903
theorem B661959 : Blo 658307 661959 := bstep (se 1 (by rfl) ⟨496469, by rfl⟩ : syracuseStep 661959 = 992939) B992939
theorem B661979 : Blo 658307 661979 := bstep (se 1 (by rfl) ⟨496484, by rfl⟩ : syracuseStep 661979 = 992969) B992969
theorem B2234843 : Blo 658307 2234843 := bstep (se 1 (by rfl) ⟨1676132, by rfl⟩ : syracuseStep 2234843 = 3352265) B3352265
theorem B989705 : Blo 658307 989705 := bstep (se 2 (by rfl) ⟨371139, by rfl⟩ : syracuseStep 989705 = 742279) B742279
theorem B3349025 : Blo 658307 3349025 := bstep (se 2 (by rfl) ⟨1255884, by rfl⟩ : syracuseStep 3349025 = 2511769) B2511769
theorem B1481255 : Blo 658307 1481255 := bstep (se 1 (by rfl) ⟨1110941, by rfl⟩ : syracuseStep 1481255 = 2221883) B2221883
theorem B989735 : Blo 658307 989735 := bstep (se 1 (by rfl) ⟨742301, by rfl⟩ : syracuseStep 989735 = 1484603) B1484603
theorem B662055 : Blo 658307 662055 := bstep (se 1 (by rfl) ⟨496541, by rfl⟩ : syracuseStep 662055 = 993083) B993083
theorem B662095 : Blo 658307 662095 := bstep (se 1 (by rfl) ⟨496571, by rfl⟩ : syracuseStep 662095 = 993143) B993143
theorem B662111 : Blo 658307 662111 := bstep (se 1 (by rfl) ⟨496583, by rfl⟩ : syracuseStep 662111 = 993167) B993167
theorem B1219169 : Blo 658307 1219169 := bstep (se 2 (by rfl) ⟨457188, by rfl⟩ : syracuseStep 1219169 = 914377) B914377
theorem B989819 : Blo 658307 989819 := bstep (se 1 (by rfl) ⟨742364, by rfl⟩ : syracuseStep 989819 = 1484729) B1484729
theorem B662139 : Blo 658307 662139 := bstep (se 1 (by rfl) ⟨496604, by rfl⟩ : syracuseStep 662139 = 993209) B993209
theorem B662191 : Blo 658307 662191 := bstep (se 1 (by rfl) ⟨496643, by rfl⟩ : syracuseStep 662191 = 993287) B993287
theorem B662215 : Blo 658307 662215 := bstep (se 1 (by rfl) ⟨496661, by rfl⟩ : syracuseStep 662215 = 993323) B993323
theorem B662235 : Blo 658307 662235 := bstep (se 1 (by rfl) ⟨496676, by rfl⟩ : syracuseStep 662235 = 993353) B993353
theorem B989945 : Blo 658307 989945 := bstep (se 2 (by rfl) ⟨371229, by rfl⟩ : syracuseStep 989945 = 742459) B742459
theorem B990047 : Blo 658307 990047 := bstep (se 1 (by rfl) ⟨742535, by rfl⟩ : syracuseStep 990047 = 1485071) B1485071
theorem B1481579 : Blo 658307 1481579 := bstep (se 1 (by rfl) ⟨1111184, by rfl⟩ : syracuseStep 1481579 = 2222369) B2222369
theorem B990059 : Blo 658307 990059 := bstep (se 1 (by rfl) ⟨742544, by rfl⟩ : syracuseStep 990059 = 1485089) B1485089
theorem B1481633 : Blo 658307 1481633 := bstep (se 2 (by rfl) ⟨555612, by rfl⟩ : syracuseStep 1481633 = 1111225) B1111225
theorem B1252361 : Blo 658307 1252361 := bstep (se 2 (by rfl) ⟨469635, by rfl⟩ : syracuseStep 1252361 = 939271) B939271
theorem B990287 : Blo 658307 990287 := bstep (se 1 (by rfl) ⟨742715, by rfl⟩ : syracuseStep 990287 = 1485431) B1485431
theorem B5020865 : Blo 658307 5020865 := bstep (se 2 (by rfl) ⟨1882824, by rfl⟩ : syracuseStep 5020865 = 3765649) B3765649
theorem B990407 : Blo 658307 990407 := bstep (se 1 (by rfl) ⟨742805, by rfl⟩ : syracuseStep 990407 = 1485611) B1485611
theorem B1481975 : Blo 658307 1481975 := bstep (se 1 (by rfl) ⟨1111481, by rfl⟩ : syracuseStep 1481975 = 2222963) B2222963
theorem B1187065 : Blo 658307 1187065 := bstep (se 2 (by rfl) ⟨445149, by rfl⟩ : syracuseStep 1187065 = 890299) B890299
theorem B4234511 : Blo 658307 4234511 := bstep (se 1 (by rfl) ⟨3175883, by rfl⟩ : syracuseStep 4234511 = 6351767) B6351767
theorem B990569 : Blo 658307 990569 := bstep (se 2 (by rfl) ⟨371463, by rfl⟩ : syracuseStep 990569 = 742927) B742927
theorem B990647 : Blo 658307 990647 := bstep (se 1 (by rfl) ⟨742985, by rfl⟩ : syracuseStep 990647 = 1485971) B1485971
theorem B990683 : Blo 658307 990683 := bstep (se 1 (by rfl) ⟨743012, by rfl⟩ : syracuseStep 990683 = 1486025) B1486025
theorem B9510533 : Blo 658307 9510533 := bstep (se 4 (by rfl) ⟨891612, by rfl⟩ : syracuseStep 9510533 = 1783225) B1783225
theorem B1482569 : Blo 658307 1482569 := bstep (se 2 (by rfl) ⟨555963, by rfl⟩ : syracuseStep 1482569 = 1111927) B1111927
theorem B1253227 : Blo 658307 1253227 := bstep (se 1 (by rfl) ⟨939920, by rfl⟩ : syracuseStep 1253227 = 1879841) B1879841
theorem B1056655 : Blo 658307 1056655 := bstep (se 1 (by rfl) ⟨792491, by rfl⟩ : syracuseStep 1056655 = 1584983) B1584983
theorem B991151 : Blo 658307 991151 := bstep (se 1 (by rfl) ⟨743363, by rfl⟩ : syracuseStep 991151 = 1486727) B1486727
theorem B1253303 : Blo 658307 1253303 := bstep (se 1 (by rfl) ⟨939977, by rfl⟩ : syracuseStep 1253303 = 1879955) B1879955
theorem B1875899 : Blo 658307 1875899 := bstep (se 1 (by rfl) ⟨1406924, by rfl⟩ : syracuseStep 1875899 = 2813849) B2813849
theorem B3579835 : Blo 658307 3579835 := bstep (se 1 (by rfl) ⟨2684876, by rfl⟩ : syracuseStep 3579835 = 5369753) B5369753
theorem B4759505 : Blo 658307 4759505 := bstep (se 2 (by rfl) ⟨1784814, by rfl⟩ : syracuseStep 4759505 = 3569629) B3569629
theorem B1056731 : Blo 658307 1056731 := bstep (se 1 (by rfl) ⟨792548, by rfl⟩ : syracuseStep 1056731 = 1585097) B1585097
theorem B991241 : Blo 658307 991241 := bstep (se 2 (by rfl) ⟨371715, by rfl⟩ : syracuseStep 991241 = 743431) B743431
theorem B991271 : Blo 658307 991271 := bstep (se 1 (by rfl) ⟨743453, by rfl⟩ : syracuseStep 991271 = 1486907) B1486907
theorem B991355 : Blo 658307 991355 := bstep (se 1 (by rfl) ⟨743516, by rfl⟩ : syracuseStep 991355 = 1487033) B1487033
theorem B991481 : Blo 658307 991481 := bstep (se 2 (by rfl) ⟨371805, by rfl⟩ : syracuseStep 991481 = 743611) B743611
theorem B15212875 : Blo 658307 15212875 := bstep (se 1 (by rfl) ⟨11409656, by rfl⟩ : syracuseStep 15212875 = 22819313) B22819313
theorem B991583 : Blo 658307 991583 := bstep (se 1 (by rfl) ⟨743687, by rfl⟩ : syracuseStep 991583 = 1487375) B1487375
theorem B991595 : Blo 658307 991595 := bstep (se 1 (by rfl) ⟨743696, by rfl⟩ : syracuseStep 991595 = 1487393) B1487393
theorem B1253819 : Blo 658307 1253819 := bstep (se 1 (by rfl) ⟨940364, by rfl⟩ : syracuseStep 1253819 = 1880729) B1880729
theorem B3809825 : Blo 658307 3809825 := bstep (se 2 (by rfl) ⟨1428684, by rfl⟩ : syracuseStep 3809825 = 2857369) B2857369
theorem B991823 : Blo 658307 991823 := bstep (se 1 (by rfl) ⟨743867, by rfl⟩ : syracuseStep 991823 = 1487735) B1487735
theorem B1483361 : Blo 658307 1483361 := bstep (se 2 (by rfl) ⟨556260, by rfl⟩ : syracuseStep 1483361 = 1112521) B1112521
theorem B1188449 : Blo 658307 1188449 := bstep (se 2 (by rfl) ⟨445668, by rfl⟩ : syracuseStep 1188449 = 891337) B891337
theorem B991943 : Blo 658307 991943 := bstep (se 1 (by rfl) ⟨743957, by rfl⟩ : syracuseStep 991943 = 1487915) B1487915
theorem B992105 : Blo 658307 992105 := bstep (se 2 (by rfl) ⟨372039, by rfl⟩ : syracuseStep 992105 = 744079) B744079
theorem B1254305 : Blo 658307 1254305 := bstep (se 2 (by rfl) ⟨470364, by rfl⟩ : syracuseStep 1254305 = 940729) B940729
theorem B1483703 : Blo 658307 1483703 := bstep (se 1 (by rfl) ⟨1112777, by rfl⟩ : syracuseStep 1483703 = 2225555) B2225555
theorem B992183 : Blo 658307 992183 := bstep (se 1 (by rfl) ⟨744137, by rfl⟩ : syracuseStep 992183 = 1488275) B1488275
theorem B992219 : Blo 658307 992219 := bstep (se 1 (by rfl) ⟨744164, by rfl⟩ : syracuseStep 992219 = 1488329) B1488329
theorem B1254457 : Blo 658307 1254457 := bstep (se 2 (by rfl) ⟨470421, by rfl⟩ : syracuseStep 1254457 = 940843) B940843
theorem B1058039 : Blo 658307 1058039 := bstep (se 1 (by rfl) ⟨793529, by rfl⟩ : syracuseStep 1058039 = 1587059) B1587059
theorem B19342651 : Blo 658307 19342651 := bstep (se 1 (by rfl) ⟨14506988, by rfl⟩ : syracuseStep 19342651 = 29013977) B29013977
theorem B1254761 : Blo 658307 1254761 := bstep (se 2 (by rfl) ⟨470535, by rfl⟩ : syracuseStep 1254761 = 941071) B941071
theorem B992687 : Blo 658307 992687 := bstep (se 1 (by rfl) ⟨744515, by rfl⟩ : syracuseStep 992687 = 1489031) B1489031
theorem B1058231 : Blo 658307 1058231 := bstep (se 1 (by rfl) ⟨793673, by rfl⟩ : syracuseStep 1058231 = 1587347) B1587347
theorem B8037893 : Blo 658307 8037893 := bstep (se 4 (by rfl) ⟨753552, by rfl⟩ : syracuseStep 8037893 = 1507105) B1507105
theorem B2500105 : Blo 658307 2500105 := bstep (se 2 (by rfl) ⟨937539, by rfl⟩ : syracuseStep 2500105 = 1875079) B1875079
theorem B1484297 : Blo 658307 1484297 := bstep (se 2 (by rfl) ⟨556611, by rfl⟩ : syracuseStep 1484297 = 1113223) B1113223
theorem B992777 : Blo 658307 992777 := bstep (se 2 (by rfl) ⟨372291, by rfl⟩ : syracuseStep 992777 = 744583) B744583
theorem B992807 : Blo 658307 992807 := bstep (se 1 (by rfl) ⟨744605, by rfl⟩ : syracuseStep 992807 = 1489211) B1489211
theorem B3352103 : Blo 658307 3352103 := bstep (se 1 (by rfl) ⟨2514077, by rfl⟩ : syracuseStep 3352103 = 5028155) B5028155
theorem B992891 : Blo 658307 992891 := bstep (se 1 (by rfl) ⟨744668, by rfl⟩ : syracuseStep 992891 = 1489337) B1489337
theorem B2860733 : Blo 658307 2860733 := bstep (se 3 (by rfl) ⟨536387, by rfl⟩ : syracuseStep 2860733 = 1072775) B1072775
theorem B993017 : Blo 658307 993017 := bstep (se 2 (by rfl) ⟨372381, by rfl⟩ : syracuseStep 993017 = 744763) B744763
theorem B7219003 : Blo 658307 7219003 := bstep (se 1 (by rfl) ⟨5414252, by rfl⟩ : syracuseStep 7219003 = 10828505) B10828505
theorem B1484639 : Blo 658307 1484639 := bstep (se 1 (by rfl) ⟨1113479, by rfl⟩ : syracuseStep 1484639 = 2226959) B2226959
theorem B993119 : Blo 658307 993119 := bstep (se 1 (by rfl) ⟨744839, by rfl⟩ : syracuseStep 993119 = 1489679) B1489679
theorem B993131 : Blo 658307 993131 := bstep (se 1 (by rfl) ⟨744848, by rfl⟩ : syracuseStep 993131 = 1489697) B1489697
theorem B6006737 : Blo 658307 6006737 := bstep (se 2 (by rfl) ⟨2252526, by rfl⟩ : syracuseStep 6006737 = 4505053) B4505053
theorem B1484819 : Blo 658307 1484819 := bstep (se 1 (by rfl) ⟨1113614, by rfl⟩ : syracuseStep 1484819 = 2227229) B2227229
theorem B5023781 : Blo 658307 5023781 := bstep (se 4 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 5023781 = 941959) B941959
theorem B993359 : Blo 658307 993359 := bstep (se 1 (by rfl) ⟨745019, by rfl⟩ : syracuseStep 993359 = 1490039) B1490039
theorem B1485161 : Blo 658307 1485161 := bstep (se 2 (by rfl) ⟨556935, by rfl⟩ : syracuseStep 1485161 = 1113871) B1113871
theorem B6335009 : Blo 658307 6335009 := bstep (se 2 (by rfl) ⟨2375628, by rfl⟩ : syracuseStep 6335009 = 4751257) B4751257
theorem B1583713 : Blo 658307 1583713 := bstep (se 2 (by rfl) ⟨593892, by rfl⟩ : syracuseStep 1583713 = 1187785) B1187785
theorem B1059499 : Blo 658307 1059499 := bstep (se 1 (by rfl) ⟨794624, by rfl⟩ : syracuseStep 1059499 = 1589249) B1589249
theorem B1780423 : Blo 658307 1780423 := bstep (se 1 (by rfl) ⟨1335317, by rfl⟩ : syracuseStep 1780423 = 2670635) B2670635
theorem B1583945 : Blo 658307 1583945 := bstep (se 2 (by rfl) ⟨593979, by rfl⟩ : syracuseStep 1583945 = 1187959) B1187959
theorem B1059679 : Blo 658307 1059679 := bstep (se 1 (by rfl) ⟨794759, by rfl⟩ : syracuseStep 1059679 = 1589519) B1589519
theorem B1780663 : Blo 658307 1780663 := bstep (se 1 (by rfl) ⟨1335497, by rfl⟩ : syracuseStep 1780663 = 2670995) B2670995
theorem B2501563 : Blo 658307 2501563 := bstep (se 1 (by rfl) ⟨1876172, by rfl⟩ : syracuseStep 2501563 = 3752345) B3752345
theorem B1485755 : Blo 658307 1485755 := bstep (se 1 (by rfl) ⟨1114316, by rfl⟩ : syracuseStep 1485755 = 2228633) B2228633
theorem B1485881 : Blo 658307 1485881 := bstep (se 2 (by rfl) ⟨557205, by rfl⟩ : syracuseStep 1485881 = 1114411) B1114411
theorem B1486223 : Blo 658307 1486223 := bstep (se 1 (by rfl) ⟨1114667, by rfl⟩ : syracuseStep 1486223 = 2229335) B2229335
theorem B1256887 : Blo 658307 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B3386843 : Blo 658307 3386843 := bstep (se 1 (by rfl) ⟨2540132, by rfl⟩ : syracuseStep 3386843 = 5080265) B5080265
theorem B2502353 : Blo 658307 2502353 := bstep (se 2 (by rfl) ⟨938382, by rfl⟩ : syracuseStep 2502353 = 1876765) B1876765
theorem B1486547 : Blo 658307 1486547 := bstep (se 1 (by rfl) ⟨1114910, by rfl⟩ : syracuseStep 1486547 = 2229821) B2229821
theorem B1126457 : Blo 658307 1126457 := bstep (se 2 (by rfl) ⟨422421, by rfl⟩ : syracuseStep 1126457 = 844843) B844843
theorem B2502809 : Blo 658307 2502809 := bstep (se 2 (by rfl) ⟨938553, by rfl⟩ : syracuseStep 2502809 = 1877107) B1877107
theorem B16888013 : Blo 658307 16888013 := bstep (se 3 (by rfl) ⟨3166502, by rfl⟩ : syracuseStep 16888013 = 6333005) B6333005
theorem B1192457 : Blo 658307 1192457 := bstep (se 2 (by rfl) ⟨447171, by rfl⟩ : syracuseStep 1192457 = 894343) B894343
theorem B2109977 : Blo 658307 2109977 := bstep (se 2 (by rfl) ⟨791241, by rfl⟩ : syracuseStep 2109977 = 1582483) B1582483
theorem B1487483 : Blo 658307 1487483 := bstep (se 1 (by rfl) ⟨1115612, by rfl⟩ : syracuseStep 1487483 = 2231225) B2231225
theorem B1487609 : Blo 658307 1487609 := bstep (se 2 (by rfl) ⟨557853, by rfl⟩ : syracuseStep 1487609 = 1115707) B1115707
theorem B1487879 : Blo 658307 1487879 := bstep (se 1 (by rfl) ⟨1115909, by rfl⟩ : syracuseStep 1487879 = 2231819) B2231819
theorem B5715011 : Blo 658307 5715011 := bstep (se 1 (by rfl) ⟨4286258, by rfl⟩ : syracuseStep 5715011 = 8572517) B8572517
theorem B1487951 : Blo 658307 1487951 := bstep (se 1 (by rfl) ⟨1115963, by rfl⟩ : syracuseStep 1487951 = 2231927) B2231927
theorem B4764865 : Blo 658307 4764865 := bstep (se 2 (by rfl) ⟨1786824, by rfl⟩ : syracuseStep 4764865 = 3573649) B3573649
theorem B10171595 : Blo 658307 10171595 := bstep (se 1 (by rfl) ⟨7628696, by rfl⟩ : syracuseStep 10171595 = 15257393) B15257393
theorem B2536715 : Blo 658307 2536715 := bstep (se 1 (by rfl) ⟨1902536, by rfl⟩ : syracuseStep 2536715 = 3805073) B3805073
theorem B1193321 : Blo 658307 1193321 := bstep (se 2 (by rfl) ⟨447495, by rfl⟩ : syracuseStep 1193321 = 894991) B894991
theorem B7157155 : Blo 658307 7157155 := bstep (se 1 (by rfl) ⟨5367866, by rfl⟩ : syracuseStep 7157155 = 10735733) B10735733
theorem B1488347 : Blo 658307 1488347 := bstep (se 1 (by rfl) ⟨1116260, by rfl⟩ : syracuseStep 1488347 = 2232521) B2232521
theorem B2209697 : Blo 658307 2209697 := bstep (se 2 (by rfl) ⟨828636, by rfl⟩ : syracuseStep 2209697 = 1657273) B1657273
theorem B1488815 : Blo 658307 1488815 := bstep (se 1 (by rfl) ⟨1116611, by rfl⟩ : syracuseStep 1488815 = 2233223) B2233223
theorem B2111503 : Blo 658307 2111503 := bstep (se 1 (by rfl) ⟨1583627, by rfl⟩ : syracuseStep 2111503 = 3167255) B3167255
theorem B17119289 : Blo 658307 17119289 := bstep (se 2 (by rfl) ⟨6419733, by rfl⟩ : syracuseStep 17119289 = 12839467) B12839467
theorem B2504783 : Blo 658307 2504783 := bstep (se 1 (by rfl) ⟨1878587, by rfl⟩ : syracuseStep 2504783 = 3757175) B3757175
theorem B3225689 : Blo 658307 3225689 := bstep (se 2 (by rfl) ⟨1209633, by rfl⟩ : syracuseStep 3225689 = 2419267) B2419267
theorem B2373785 : Blo 658307 2373785 := bstep (se 2 (by rfl) ⟨890169, by rfl⟩ : syracuseStep 2373785 = 1780339) B1780339
theorem B1489067 : Blo 658307 1489067 := bstep (se 1 (by rfl) ⟨1116800, by rfl⟩ : syracuseStep 1489067 = 2233601) B2233601
theorem B2504951 : Blo 658307 2504951 := bstep (se 1 (by rfl) ⟨1878713, by rfl⟩ : syracuseStep 2504951 = 3757427) B3757427
theorem B5355929 : Blo 658307 5355929 := bstep (se 2 (by rfl) ⟨2008473, by rfl⟩ : syracuseStep 5355929 = 4016947) B4016947
theorem B4012577 : Blo 658307 4012577 := bstep (se 2 (by rfl) ⟨1504716, by rfl⟩ : syracuseStep 4012577 = 3009433) B3009433
theorem B1784359 : Blo 658307 1784359 := bstep (se 1 (by rfl) ⟨1338269, by rfl⟩ : syracuseStep 1784359 = 2676539) B2676539
theorem B7518905 : Blo 658307 7518905 := bstep (se 2 (by rfl) ⟨2819589, by rfl⟩ : syracuseStep 7518905 = 5639179) B5639179
theorem B1489607 : Blo 658307 1489607 := bstep (se 1 (by rfl) ⟨1117205, by rfl⟩ : syracuseStep 1489607 = 2234411) B2234411
theorem B8469431 : Blo 658307 8469431 := bstep (se 1 (by rfl) ⟨6352073, by rfl⟩ : syracuseStep 8469431 = 12704147) B12704147
theorem B2505923 : Blo 658307 2505923 := bstep (se 1 (by rfl) ⟨1879442, by rfl⟩ : syracuseStep 2505923 = 3758885) B3758885
theorem B1130041 : Blo 658307 1130041 := bstep (se 2 (by rfl) ⟨423765, by rfl⟩ : syracuseStep 1130041 = 847531) B847531
theorem B1883999 : Blo 658307 1883999 := bstep (se 1 (by rfl) ⟨1412999, by rfl⟩ : syracuseStep 1883999 = 2825999) B2825999
theorem B1589327 : Blo 658307 1589327 := bstep (se 1 (by rfl) ⟨1191995, by rfl⟩ : syracuseStep 1589327 = 2383991) B2383991
theorem B2506909 : Blo 658307 2506909 := bstep (se 3 (by rfl) ⟨470045, by rfl⟩ : syracuseStep 2506909 = 940091) B940091
theorem B19087589 : Blo 658307 19087589 := bstep (se 4 (by rfl) ⟨1789461, by rfl⟩ : syracuseStep 19087589 = 3578923) B3578923
theorem B10731851 : Blo 658307 10731851 := bstep (se 1 (by rfl) ⟨8048888, by rfl⟩ : syracuseStep 10731851 = 16097777) B16097777
theorem B1885103 : Blo 658307 1885103 := bstep (se 1 (by rfl) ⟨1413827, by rfl⟩ : syracuseStep 1885103 = 2827655) B2827655
theorem B2114579 : Blo 658307 2114579 := bstep (se 1 (by rfl) ⟨1585934, by rfl⟩ : syracuseStep 2114579 = 3171869) B3171869
theorem B7849477 : Blo 658307 7849477 := bstep (se 4 (by rfl) ⟨735888, by rfl⟩ : syracuseStep 7849477 = 1471777) B1471777
theorem B13551623 : Blo 658307 13551623 := bstep (se 1 (by rfl) ⟨10163717, by rfl⟩ : syracuseStep 13551623 = 20327435) B20327435
theorem B65095987 : Blo 658307 65095987 := bstep (se 1 (by rfl) ⟨48821990, by rfl⟩ : syracuseStep 65095987 = 97643981) B97643981
theorem B1788425 : Blo 658307 1788425 := bstep (se 2 (by rfl) ⟨670659, by rfl⟩ : syracuseStep 1788425 = 1341319) B1341319
theorem B838183 : Blo 658307 838183 := bstep (se 1 (by rfl) ⟨628637, by rfl⟩ : syracuseStep 838183 = 1257275) B1257275
theorem B2116219 : Blo 658307 2116219 := bstep (se 1 (by rfl) ⟨1587164, by rfl⟩ : syracuseStep 2116219 = 3174329) B3174329
theorem B4770515 : Blo 658307 4770515 := bstep (se 1 (by rfl) ⟨3577886, by rfl⟩ : syracuseStep 4770515 = 7155773) B7155773
theorem B21449549 : Blo 658307 21449549 := bstep (se 3 (by rfl) ⟨4021790, by rfl⟩ : syracuseStep 21449549 = 8043581) B8043581
theorem B2509825 : Blo 658307 2509825 := bstep (se 2 (by rfl) ⟨941184, by rfl⟩ : syracuseStep 2509825 = 1882369) B1882369
theorem B6016079 : Blo 658307 6016079 := bstep (se 1 (by rfl) ⟨4512059, by rfl⟩ : syracuseStep 6016079 = 9024119) B9024119
theorem B2117153 : Blo 658307 2117153 := bstep (se 2 (by rfl) ⟨793932, by rfl⟩ : syracuseStep 2117153 = 1587865) B1587865
theorem B2510585 : Blo 658307 2510585 := bstep (se 2 (by rfl) ⟨941469, by rfl⟩ : syracuseStep 2510585 = 1882939) B1882939
theorem B2379593 : Blo 658307 2379593 := bstep (se 2 (by rfl) ⟨892347, by rfl⟩ : syracuseStep 2379593 = 1784695) B1784695
theorem B3755969 : Blo 658307 3755969 := bstep (se 2 (by rfl) ⟨1408488, by rfl⟩ : syracuseStep 3755969 = 2816977) B2816977
theorem B741415 : Blo 658307 741415 := bstep (se 1 (by rfl) ⟨556061, by rfl⟩ : syracuseStep 741415 = 1112123) B1112123
theorem B6017105 : Blo 658307 6017105 := bstep (se 2 (by rfl) ⟨2256414, by rfl⟩ : syracuseStep 6017105 = 4512829) B4512829
theorem B2937149 : Blo 658307 2937149 := bstep (se 3 (by rfl) ⟨550715, by rfl⟩ : syracuseStep 2937149 = 1101431) B1101431
theorem B7524737 : Blo 658307 7524737 := bstep (se 2 (by rfl) ⟨2821776, by rfl⟩ : syracuseStep 7524737 = 5643553) B5643553
theorem B5362157 : Blo 658307 5362157 := bstep (se 3 (by rfl) ⟨1005404, by rfl⟩ : syracuseStep 5362157 = 2010809) B2010809
theorem B11457125 : Blo 658307 11457125 := bstep (se 4 (by rfl) ⟨1074105, by rfl⟩ : syracuseStep 11457125 = 2148211) B2148211
theorem B3429427 : Blo 658307 3429427 := bstep (se 1 (by rfl) ⟨2572070, by rfl⟩ : syracuseStep 3429427 = 5144141) B5144141
theorem B2512043 : Blo 658307 2512043 := bstep (se 1 (by rfl) ⟨1884032, by rfl⟩ : syracuseStep 2512043 = 3768065) B3768065
theorem B2118923 : Blo 658307 2118923 := bstep (se 1 (by rfl) ⟨1589192, by rfl⟩ : syracuseStep 2118923 = 3178385) B3178385
theorem B2119193 : Blo 658307 2119193 := bstep (se 2 (by rfl) ⟨794697, by rfl⟩ : syracuseStep 2119193 = 1589395) B1589395
theorem B2676347 : Blo 658307 2676347 := bstep (se 1 (by rfl) ⟨2007260, by rfl⟩ : syracuseStep 2676347 = 4014521) B4014521
theorem B743035 : Blo 658307 743035 := bstep (se 1 (by rfl) ⟨557276, by rfl⟩ : syracuseStep 743035 = 1114553) B1114553
theorem B743503 : Blo 658307 743503 := bstep (se 1 (by rfl) ⟨557627, by rfl⟩ : syracuseStep 743503 = 1115255) B1115255
theorem B4773977 : Blo 658307 4773977 := bstep (se 2 (by rfl) ⟨1790241, by rfl⟩ : syracuseStep 4773977 = 3580483) B3580483
theorem B2513213 : Blo 658307 2513213 := bstep (se 3 (by rfl) ⟨471227, by rfl⟩ : syracuseStep 2513213 = 942455) B942455
theorem B2120023 : Blo 658307 2120023 := bstep (se 1 (by rfl) ⟨1590017, by rfl⟩ : syracuseStep 2120023 = 3180035) B3180035
theorem B743899 : Blo 658307 743899 := bstep (se 1 (by rfl) ⟨557924, by rfl⟩ : syracuseStep 743899 = 1115849) B1115849
theorem B5364233 : Blo 658307 5364233 := bstep (se 2 (by rfl) ⟨2011587, by rfl⟩ : syracuseStep 5364233 = 4023175) B4023175
theorem B2513531 : Blo 658307 2513531 := bstep (se 1 (by rfl) ⟨1885148, by rfl⟩ : syracuseStep 2513531 = 3770297) B3770297
theorem B2382635 : Blo 658307 2382635 := bstep (se 1 (by rfl) ⟨1786976, by rfl⟩ : syracuseStep 2382635 = 3573953) B3573953
theorem B744367 : Blo 658307 744367 := bstep (se 1 (by rfl) ⟨558275, by rfl⟩ : syracuseStep 744367 = 1116551) B1116551
theorem B1268743 : Blo 658307 1268743 := bstep (se 1 (by rfl) ⟨951557, by rfl⟩ : syracuseStep 1268743 = 1903115) B1903115
theorem B744799 : Blo 658307 744799 := bstep (se 1 (by rfl) ⟨558599, by rfl⟩ : syracuseStep 744799 = 1117199) B1117199
theorem B48717233 : Blo 658307 48717233 := bstep (se 2 (by rfl) ⟨18268962, by rfl⟩ : syracuseStep 48717233 = 36537925) B36537925
theorem B4218313 : Blo 658307 4218313 := bstep (se 2 (by rfl) ⟨1581867, by rfl⟩ : syracuseStep 4218313 = 3163735) B3163735
theorem B2121203 : Blo 658307 2121203 := bstep (se 1 (by rfl) ⟨1590902, by rfl⟩ : syracuseStep 2121203 = 3181805) B3181805
theorem B9494435 : Blo 658307 9494435 := bstep (se 1 (by rfl) ⟨7120826, by rfl⟩ : syracuseStep 9494435 = 14241653) B14241653
theorem B1335739 : Blo 658307 1335739 := bstep (se 1 (by rfl) ⟨1001804, by rfl⟩ : syracuseStep 1335739 = 2003609) B2003609
theorem B4514251 : Blo 658307 4514251 := bstep (se 1 (by rfl) ⟨3385688, by rfl⟩ : syracuseStep 4514251 = 6771377) B6771377
theorem B2417249 : Blo 658307 2417249 := bstep (se 2 (by rfl) ⟨906468, by rfl⟩ : syracuseStep 2417249 = 1812937) B1812937
theorem B3760775 : Blo 658307 3760775 := bstep (se 1 (by rfl) ⟨2820581, by rfl⟩ : syracuseStep 3760775 = 5641163) B5641163
theorem B12248113 : Blo 658307 12248113 := bstep (se 2 (by rfl) ⟨4593042, by rfl⟩ : syracuseStep 12248113 = 9186085) B9186085
theorem B1337231 : Blo 658307 1337231 := bstep (se 1 (by rfl) ⟨1002923, by rfl⟩ : syracuseStep 1337231 = 2005847) B2005847
theorem B23128001 : Blo 658307 23128001 := bstep (se 2 (by rfl) ⟨8673000, by rfl⟩ : syracuseStep 23128001 = 17346001) B17346001
theorem B2222099 : Blo 658307 2222099 := bstep (se 1 (by rfl) ⟨1666574, by rfl⟩ : syracuseStep 2222099 = 3333149) B3333149
theorem B3762233 : Blo 658307 3762233 := bstep (se 2 (by rfl) ⟨1410837, by rfl⟩ : syracuseStep 3762233 = 2821675) B2821675
theorem B4024637 : Blo 658307 4024637 := bstep (se 3 (by rfl) ⟨754619, by rfl⟩ : syracuseStep 4024637 = 1509239) B1509239
theorem B2222423 : Blo 658307 2222423 := bstep (se 1 (by rfl) ⟨1666817, by rfl⟩ : syracuseStep 2222423 = 3333635) B3333635
theorem B3336713 : Blo 658307 3336713 := bstep (se 2 (by rfl) ⟨1251267, by rfl⟩ : syracuseStep 3336713 = 2502535) B2502535
theorem B112716785 : Blo 658307 112716785 := bstep (se 2 (by rfl) ⟨42268794, by rfl⟩ : syracuseStep 112716785 = 84537589) B84537589
theorem B1666433 : Blo 658307 1666433 := bstep (se 2 (by rfl) ⟨624912, by rfl⟩ : syracuseStep 1666433 = 1249825) B1249825
theorem B2223503 : Blo 658307 2223503 := bstep (se 1 (by rfl) ⟨1667627, by rfl⟩ : syracuseStep 2223503 = 3335255) B3335255
theorem B5074319 : Blo 658307 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B27061847 : Blo 658307 27061847 := bstep (se 1 (by rfl) ⟨20296385, by rfl⟩ : syracuseStep 27061847 = 40592771) B40592771
theorem B2223827 : Blo 658307 2223827 := bstep (se 1 (by rfl) ⟨1667870, by rfl⟩ : syracuseStep 2223827 = 3335741) B3335741
theorem B1666889 : Blo 658307 1666889 := bstep (se 2 (by rfl) ⟨625083, by rfl⟩ : syracuseStep 1666889 = 1250167) B1250167
theorem B4747193 : Blo 658307 4747193 := bstep (se 2 (by rfl) ⟨1780197, by rfl⟩ : syracuseStep 4747193 = 3560395) B3560395
theorem B3338171 : Blo 658307 3338171 := bstep (se 1 (by rfl) ⟨2503628, by rfl⟩ : syracuseStep 3338171 = 5007257) B5007257
theorem B1667243 : Blo 658307 1667243 := bstep (se 1 (by rfl) ⟨1250432, by rfl⟩ : syracuseStep 1667243 = 2500865) B2500865
theorem B3764717 : Blo 658307 3764717 := bstep (se 3 (by rfl) ⟨705884, by rfl⟩ : syracuseStep 3764717 = 1411769) B1411769
theorem B1274491 : Blo 658307 1274491 := bstep (se 1 (by rfl) ⟨955868, by rfl⟩ : syracuseStep 1274491 = 1911737) B1911737
theorem B2225015 : Blo 658307 2225015 := bstep (se 1 (by rfl) ⟨1668761, by rfl⟩ : syracuseStep 2225015 = 3337523) B3337523
theorem B1668023 : Blo 658307 1668023 := bstep (se 1 (by rfl) ⟨1251017, by rfl⟩ : syracuseStep 1668023 = 2502035) B2502035
theorem B1504187 : Blo 658307 1504187 := bstep (se 1 (by rfl) ⟨1128140, by rfl⟩ : syracuseStep 1504187 = 2256281) B2256281
theorem B1111097 : Blo 658307 1111097 := bstep (se 2 (by rfl) ⟨416661, by rfl⟩ : syracuseStep 1111097 = 833323) B833323
theorem B2225231 : Blo 658307 2225231 := bstep (se 1 (by rfl) ⟨1668923, by rfl⟩ : syracuseStep 2225231 = 3337847) B3337847
theorem B3339467 : Blo 658307 3339467 := bstep (se 1 (by rfl) ⟨2504600, by rfl⟩ : syracuseStep 3339467 = 5009201) B5009201
theorem B2225609 : Blo 658307 2225609 := bstep (se 2 (by rfl) ⟨834603, by rfl⟩ : syracuseStep 2225609 = 1669207) B1669207
theorem B7501409 : Blo 658307 7501409 := bstep (se 2 (by rfl) ⟨2813028, by rfl⟩ : syracuseStep 7501409 = 5626057) B5626057
theorem B2258579 : Blo 658307 2258579 := bstep (se 1 (by rfl) ⟨1693934, by rfl⟩ : syracuseStep 2258579 = 3387869) B3387869
theorem B2225879 : Blo 658307 2225879 := bstep (se 1 (by rfl) ⟨1669409, by rfl⟩ : syracuseStep 2225879 = 3338819) B3338819
theorem B1111799 : Blo 658307 1111799 := bstep (se 1 (by rfl) ⟨833849, by rfl⟩ : syracuseStep 1111799 = 1667699) B1667699
theorem B1669025 : Blo 658307 1669025 := bstep (se 2 (by rfl) ⟨625884, by rfl⟩ : syracuseStep 1669025 = 1251769) B1251769
theorem B2226095 : Blo 658307 2226095 := bstep (se 1 (by rfl) ⟨1669571, by rfl⟩ : syracuseStep 2226095 = 3339143) B3339143
theorem B1112143 : Blo 658307 1112143 := bstep (se 1 (by rfl) ⟨834107, by rfl⟩ : syracuseStep 1112143 = 1668215) B1668215
theorem B1112393 : Blo 658307 1112393 := bstep (se 2 (by rfl) ⟨417147, by rfl⟩ : syracuseStep 1112393 = 834295) B834295
theorem B1669481 : Blo 658307 1669481 := bstep (se 2 (by rfl) ⟨626055, by rfl⟩ : syracuseStep 1669481 = 1252111) B1252111
theorem B1341839 : Blo 658307 1341839 := bstep (se 1 (by rfl) ⟨1006379, by rfl⟩ : syracuseStep 1341839 = 2012759) B2012759
theorem B752047 : Blo 658307 752047 := bstep (se 1 (by rfl) ⟨564035, by rfl⟩ : syracuseStep 752047 = 1128071) B1128071
theorem B9009893 : Blo 658307 9009893 := bstep (se 4 (by rfl) ⟨844677, by rfl⟩ : syracuseStep 9009893 = 1689355) B1689355
theorem B1112825 : Blo 658307 1112825 := bstep (se 2 (by rfl) ⟨417309, by rfl⟩ : syracuseStep 1112825 = 834619) B834619
theorem B1113007 : Blo 658307 1113007 := bstep (se 1 (by rfl) ⟨834755, by rfl⟩ : syracuseStep 1113007 = 1669511) B1669511
theorem B1113095 : Blo 658307 1113095 := bstep (se 1 (by rfl) ⟨834821, by rfl⟩ : syracuseStep 1113095 = 1669643) B1669643
theorem B1408079 : Blo 658307 1408079 := bstep (se 1 (by rfl) ⟨1056059, by rfl⟩ : syracuseStep 1408079 = 2112119) B2112119
theorem B8027383 : Blo 658307 8027383 := bstep (se 1 (by rfl) ⟨6020537, by rfl⟩ : syracuseStep 8027383 = 12041075) B12041075
theorem B6782297 : Blo 658307 6782297 := bstep (se 2 (by rfl) ⟨2543361, by rfl⟩ : syracuseStep 6782297 = 5086723) B5086723
theorem B1113439 : Blo 658307 1113439 := bstep (se 1 (by rfl) ⟨835079, by rfl⟩ : syracuseStep 1113439 = 1670159) B1670159
theorem B1113527 : Blo 658307 1113527 := bstep (se 1 (by rfl) ⟨835145, by rfl⟩ : syracuseStep 1113527 = 1670291) B1670291
theorem B1670665 : Blo 658307 1670665 := bstep (se 2 (by rfl) ⟨626499, by rfl⟩ : syracuseStep 1670665 = 1252999) B1252999
theorem B2817575 : Blo 658307 2817575 := bstep (se 1 (by rfl) ⟨2113181, by rfl⟩ : syracuseStep 2817575 = 4226363) B4226363
theorem B5013089 : Blo 658307 5013089 := bstep (se 2 (by rfl) ⟨1879908, by rfl⟩ : syracuseStep 5013089 = 3759817) B3759817
theorem B3342545 : Blo 658307 3342545 := bstep (se 2 (by rfl) ⟨1253454, by rfl⟩ : syracuseStep 3342545 = 2506909) B2506909
theorem B2818259 : Blo 658307 2818259 := bstep (se 1 (by rfl) ⟨2113694, by rfl⟩ : syracuseStep 2818259 = 4227389) B4227389
theorem B20283833 : Blo 658307 20283833 := bstep (se 2 (by rfl) ⟨7606437, by rfl⟩ : syracuseStep 20283833 = 15212875) B15212875
theorem B1409719 : Blo 658307 1409719 := bstep (se 1 (by rfl) ⟨1057289, by rfl⟩ : syracuseStep 1409719 = 2114579) B2114579
theorem B3343031 : Blo 658307 3343031 := bstep (se 1 (by rfl) ⟨2507273, by rfl⟩ : syracuseStep 3343031 = 5014547) B5014547
theorem B3343517 : Blo 658307 3343517 := bstep (se 3 (by rfl) ⟨626909, by rfl⟩ : syracuseStep 3343517 = 1253819) B1253819
theorem B2229497 : Blo 658307 2229497 := bstep (se 2 (by rfl) ⟨836061, by rfl⟩ : syracuseStep 2229497 = 1672123) B1672123
theorem B1672609 : Blo 658307 1672609 := bstep (se 2 (by rfl) ⟨627228, by rfl⟩ : syracuseStep 1672609 = 1254457) B1254457
theorem B2229767 : Blo 658307 2229767 := bstep (se 1 (by rfl) ⟨1672325, by rfl⟩ : syracuseStep 2229767 = 3344651) B3344651
theorem B25790201 : Blo 658307 25790201 := bstep (se 2 (by rfl) ⟨9671325, by rfl⟩ : syracuseStep 25790201 = 19342651) B19342651
theorem B11306789 : Blo 658307 11306789 := bstep (se 4 (by rfl) ⟨1060011, by rfl⟩ : syracuseStep 11306789 = 2120023) B2120023
theorem B3180343 : Blo 658307 3180343 := bstep (se 1 (by rfl) ⟨2385257, by rfl⟩ : syracuseStep 3180343 = 4770515) B4770515
theorem B1411435 : Blo 658307 1411435 := bstep (se 1 (by rfl) ⟨1058576, by rfl⟩ : syracuseStep 1411435 = 2117153) B2117153
theorem B3344813 : Blo 658307 3344813 := bstep (se 3 (by rfl) ⟨627152, by rfl⟩ : syracuseStep 3344813 = 1254305) B1254305
theorem B2230739 : Blo 658307 2230739 := bstep (se 1 (by rfl) ⟨1673054, by rfl⟩ : syracuseStep 2230739 = 3346109) B3346109
theorem B1673723 : Blo 658307 1673723 := bstep (se 1 (by rfl) ⟨1255292, by rfl⟩ : syracuseStep 1673723 = 2510585) B2510585
theorem B2230847 : Blo 658307 2230847 := bstep (se 1 (by rfl) ⟨1673135, by rfl⟩ : syracuseStep 2230847 = 3346271) B3346271
theorem B3344975 : Blo 658307 3344975 := bstep (se 1 (by rfl) ⟨2508731, by rfl⟩ : syracuseStep 3344975 = 5017463) B5017463
theorem B1116895 : Blo 658307 1116895 := bstep (se 1 (by rfl) ⟨837671, by rfl⟩ : syracuseStep 1116895 = 1675343) B1675343
theorem B658331 : Blo 658307 658331 := bstep (se 1 (by rfl) ⟨493748, by rfl⟩ : syracuseStep 658331 = 987497) B987497
theorem B5016491 : Blo 658307 5016491 := bstep (se 1 (by rfl) ⟨3762368, by rfl⟩ : syracuseStep 5016491 = 7524737) B7524737
theorem B658383 : Blo 658307 658383 := bstep (se 1 (by rfl) ⟨493787, by rfl⟩ : syracuseStep 658383 = 987575) B987575
theorem B658407 : Blo 658307 658407 := bstep (se 1 (by rfl) ⟨493805, by rfl⟩ : syracuseStep 658407 = 987611) B987611
theorem B7638083 : Blo 658307 7638083 := bstep (se 1 (by rfl) ⟨5728562, by rfl⟩ : syracuseStep 7638083 = 11457125) B11457125
theorem B1117327 : Blo 658307 1117327 := bstep (se 1 (by rfl) ⟨837995, by rfl⟩ : syracuseStep 1117327 = 1675991) B1675991
theorem B658719 : Blo 658307 658719 := bstep (se 1 (by rfl) ⟨494039, by rfl⟩ : syracuseStep 658719 = 988079) B988079
theorem B658779 : Blo 658307 658779 := bstep (se 1 (by rfl) ⟨494084, by rfl⟩ : syracuseStep 658779 = 988169) B988169
theorem B658799 : Blo 658307 658799 := bstep (se 1 (by rfl) ⟨494099, by rfl⟩ : syracuseStep 658799 = 988199) B988199
theorem B1117577 : Blo 658307 1117577 := bstep (se 2 (by rfl) ⟨419091, by rfl⟩ : syracuseStep 1117577 = 838183) B838183
theorem B658855 : Blo 658307 658855 := bstep (se 1 (by rfl) ⟨494141, by rfl⟩ : syracuseStep 658855 = 988283) B988283
theorem B1674695 : Blo 658307 1674695 := bstep (se 1 (by rfl) ⟨1256021, by rfl⟩ : syracuseStep 1674695 = 2512043) B2512043
theorem B2821625 : Blo 658307 2821625 := bstep (se 2 (by rfl) ⟨1058109, by rfl⟩ : syracuseStep 2821625 = 2116219) B2116219
theorem B658939 : Blo 658307 658939 := bstep (se 1 (by rfl) ⟨494204, by rfl⟩ : syracuseStep 658939 = 988409) B988409
theorem B1412615 : Blo 658307 1412615 := bstep (se 1 (by rfl) ⟨1059461, by rfl⟩ : syracuseStep 1412615 = 2118923) B2118923
theorem B659007 : Blo 658307 659007 := bstep (se 1 (by rfl) ⟨494255, by rfl⟩ : syracuseStep 659007 = 988511) B988511
theorem B659015 : Blo 658307 659015 := bstep (se 1 (by rfl) ⟨494261, by rfl⟩ : syracuseStep 659015 = 988523) B988523
theorem B1412795 : Blo 658307 1412795 := bstep (se 1 (by rfl) ⟨1059596, by rfl⟩ : syracuseStep 1412795 = 2119193) B2119193
theorem B659167 : Blo 658307 659167 := bstep (se 1 (by rfl) ⟨494375, by rfl⟩ : syracuseStep 659167 = 988751) B988751
theorem B1412905 : Blo 658307 1412905 := bstep (se 2 (by rfl) ⟨529839, by rfl⟩ : syracuseStep 1412905 = 1059679) B1059679
theorem B659247 : Blo 658307 659247 := bstep (se 1 (by rfl) ⟨494435, by rfl⟩ : syracuseStep 659247 = 988871) B988871
theorem B2821949 : Blo 658307 2821949 := bstep (se 3 (by rfl) ⟨529115, by rfl⟩ : syracuseStep 2821949 = 1058231) B1058231
theorem B659355 : Blo 658307 659355 := bstep (se 1 (by rfl) ⟨494516, by rfl⟩ : syracuseStep 659355 = 989033) B989033
theorem B659407 : Blo 658307 659407 := bstep (se 1 (by rfl) ⟨494555, by rfl⟩ : syracuseStep 659407 = 989111) B989111
theorem B659431 : Blo 658307 659431 := bstep (se 1 (by rfl) ⟨494573, by rfl⟩ : syracuseStep 659431 = 989147) B989147
theorem B3346433 : Blo 658307 3346433 := bstep (se 2 (by rfl) ⟨1254912, by rfl⟩ : syracuseStep 3346433 = 2509825) B2509825
theorem B3182651 : Blo 658307 3182651 := bstep (se 1 (by rfl) ⟨2386988, by rfl⟩ : syracuseStep 3182651 = 4773977) B4773977
theorem B1675475 : Blo 658307 1675475 := bstep (se 1 (by rfl) ⟨1256606, by rfl⟩ : syracuseStep 1675475 = 2513213) B2513213
theorem B659743 : Blo 658307 659743 := bstep (se 1 (by rfl) ⟨494807, by rfl⟩ : syracuseStep 659743 = 989615) B989615
theorem B3576155 : Blo 658307 3576155 := bstep (se 1 (by rfl) ⟨2682116, by rfl⟩ : syracuseStep 3576155 = 5364233) B5364233
theorem B659803 : Blo 658307 659803 := bstep (se 1 (by rfl) ⟨494852, by rfl⟩ : syracuseStep 659803 = 989705) B989705
theorem B2232683 : Blo 658307 2232683 := bstep (se 1 (by rfl) ⟨1674512, by rfl⟩ : syracuseStep 2232683 = 3349025) B3349025
theorem B987503 : Blo 658307 987503 := bstep (se 1 (by rfl) ⟨740627, by rfl⟩ : syracuseStep 987503 = 1481255) B1481255
theorem B659823 : Blo 658307 659823 := bstep (se 1 (by rfl) ⟨494867, by rfl⟩ : syracuseStep 659823 = 989735) B989735
theorem B659879 : Blo 658307 659879 := bstep (se 1 (by rfl) ⟨494909, by rfl⟩ : syracuseStep 659879 = 989819) B989819
theorem B1675687 : Blo 658307 1675687 := bstep (se 1 (by rfl) ⟨1256765, by rfl⟩ : syracuseStep 1675687 = 2513531) B2513531
theorem B659963 : Blo 658307 659963 := bstep (se 1 (by rfl) ⟨494972, by rfl⟩ : syracuseStep 659963 = 989945) B989945
theorem B660031 : Blo 658307 660031 := bstep (se 1 (by rfl) ⟨495023, by rfl⟩ : syracuseStep 660031 = 990047) B990047
theorem B987719 : Blo 658307 987719 := bstep (se 1 (by rfl) ⟨740789, by rfl⟩ : syracuseStep 987719 = 1481579) B1481579
theorem B660039 : Blo 658307 660039 := bstep (se 1 (by rfl) ⟨495029, by rfl⟩ : syracuseStep 660039 = 990059) B990059
theorem B1675849 : Blo 658307 1675849 := bstep (se 2 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 1675849 = 1256887) B1256887
theorem B987755 : Blo 658307 987755 := bstep (se 1 (by rfl) ⟨740816, by rfl⟩ : syracuseStep 987755 = 1481633) B1481633
theorem B2232953 : Blo 658307 2232953 := bstep (se 2 (by rfl) ⟨837357, by rfl⟩ : syracuseStep 2232953 = 1674715) B1674715
theorem B660191 : Blo 658307 660191 := bstep (se 1 (by rfl) ⟨495143, by rfl⟩ : syracuseStep 660191 = 990287) B990287
theorem B3347243 : Blo 658307 3347243 := bstep (se 1 (by rfl) ⟨2510432, by rfl⟩ : syracuseStep 3347243 = 5020865) B5020865
theorem B660271 : Blo 658307 660271 := bstep (se 1 (by rfl) ⟨495203, by rfl⟩ : syracuseStep 660271 = 990407) B990407
theorem B987983 : Blo 658307 987983 := bstep (se 1 (by rfl) ⟨740987, by rfl⟩ : syracuseStep 987983 = 1481975) B1481975
theorem B2823007 : Blo 658307 2823007 := bstep (se 1 (by rfl) ⟨2117255, by rfl⟩ : syracuseStep 2823007 = 4234511) B4234511
theorem B660379 : Blo 658307 660379 := bstep (se 1 (by rfl) ⟨495284, by rfl⟩ : syracuseStep 660379 = 990569) B990569
theorem B32478155 : Blo 658307 32478155 := bstep (se 1 (by rfl) ⟨24358616, by rfl⟩ : syracuseStep 32478155 = 48717233) B48717233
theorem B660431 : Blo 658307 660431 := bstep (se 1 (by rfl) ⟨495323, by rfl⟩ : syracuseStep 660431 = 990647) B990647
theorem B660455 : Blo 658307 660455 := bstep (se 1 (by rfl) ⟨495341, by rfl⟩ : syracuseStep 660455 = 990683) B990683
theorem B1414135 : Blo 658307 1414135 := bstep (se 1 (by rfl) ⟨1060601, by rfl⟩ : syracuseStep 1414135 = 2121203) B2121203
theorem B988379 : Blo 658307 988379 := bstep (se 1 (by rfl) ⟨741284, by rfl⟩ : syracuseStep 988379 = 1482569) B1482569
theorem B6329623 : Blo 658307 6329623 := bstep (se 1 (by rfl) ⟨4747217, by rfl⟩ : syracuseStep 6329623 = 9494435) B9494435
theorem B660767 : Blo 658307 660767 := bstep (se 1 (by rfl) ⟨495575, by rfl⟩ : syracuseStep 660767 = 991151) B991151
theorem B660827 : Blo 658307 660827 := bstep (se 1 (by rfl) ⟨495620, by rfl⟩ : syracuseStep 660827 = 991241) B991241
theorem B660847 : Blo 658307 660847 := bstep (se 1 (by rfl) ⟨495635, by rfl⟩ : syracuseStep 660847 = 991271) B991271
theorem B988553 : Blo 658307 988553 := bstep (se 2 (by rfl) ⟨370707, by rfl⟩ : syracuseStep 988553 = 741415) B741415
theorem B660903 : Blo 658307 660903 := bstep (se 1 (by rfl) ⟨495677, by rfl⟩ : syracuseStep 660903 = 991355) B991355
theorem B660987 : Blo 658307 660987 := bstep (se 1 (by rfl) ⟨495740, by rfl⟩ : syracuseStep 660987 = 991481) B991481
theorem B661055 : Blo 658307 661055 := bstep (se 1 (by rfl) ⟨495791, by rfl⟩ : syracuseStep 661055 = 991583) B991583
theorem B661063 : Blo 658307 661063 := bstep (se 1 (by rfl) ⟨495797, by rfl⟩ : syracuseStep 661063 = 991595) B991595
theorem B5641913 : Blo 658307 5641913 := bstep (se 2 (by rfl) ⟨2115717, by rfl⟩ : syracuseStep 5641913 = 4231435) B4231435
theorem B661215 : Blo 658307 661215 := bstep (se 1 (by rfl) ⟨495911, by rfl⟩ : syracuseStep 661215 = 991823) B991823
theorem B988907 : Blo 658307 988907 := bstep (se 1 (by rfl) ⟨741680, by rfl⟩ : syracuseStep 988907 = 1483361) B1483361
theorem B792299 : Blo 658307 792299 := bstep (se 1 (by rfl) ⟨594224, by rfl⟩ : syracuseStep 792299 = 1188449) B1188449
theorem B1611499 : Blo 658307 1611499 := bstep (se 1 (by rfl) ⟨1208624, by rfl⟩ : syracuseStep 1611499 = 2417249) B2417249
theorem B661295 : Blo 658307 661295 := bstep (se 1 (by rfl) ⟨495971, by rfl⟩ : syracuseStep 661295 = 991943) B991943
theorem B661403 : Blo 658307 661403 := bstep (se 1 (by rfl) ⟨496052, by rfl⟩ : syracuseStep 661403 = 992105) B992105
theorem B989135 : Blo 658307 989135 := bstep (se 1 (by rfl) ⟨741851, by rfl⟩ : syracuseStep 989135 = 1483703) B1483703
theorem B661455 : Blo 658307 661455 := bstep (se 1 (by rfl) ⟨496091, by rfl⟩ : syracuseStep 661455 = 992183) B992183
theorem B661479 : Blo 658307 661479 := bstep (se 1 (by rfl) ⟨496109, by rfl⟩ : syracuseStep 661479 = 992219) B992219
theorem B661791 : Blo 658307 661791 := bstep (se 1 (by rfl) ⟨496343, by rfl⟩ : syracuseStep 661791 = 992687) B992687
theorem B989531 : Blo 658307 989531 := bstep (se 1 (by rfl) ⟨742148, by rfl⟩ : syracuseStep 989531 = 1484297) B1484297
theorem B661851 : Blo 658307 661851 := bstep (se 1 (by rfl) ⟨496388, by rfl⟩ : syracuseStep 661851 = 992777) B992777
theorem B661871 : Blo 658307 661871 := bstep (se 1 (by rfl) ⟨496403, by rfl⟩ : syracuseStep 661871 = 992807) B992807
theorem B2234735 : Blo 658307 2234735 := bstep (se 1 (by rfl) ⟨1676051, by rfl⟩ : syracuseStep 2234735 = 3352103) B3352103
theorem B661927 : Blo 658307 661927 := bstep (se 1 (by rfl) ⟨496445, by rfl⟩ : syracuseStep 661927 = 992891) B992891
theorem B1907155 : Blo 658307 1907155 := bstep (se 1 (by rfl) ⟨1430366, by rfl⟩ : syracuseStep 1907155 = 2860733) B2860733
theorem B662011 : Blo 658307 662011 := bstep (se 1 (by rfl) ⟨496508, by rfl⟩ : syracuseStep 662011 = 993017) B993017
theorem B989759 : Blo 658307 989759 := bstep (se 1 (by rfl) ⟨742319, by rfl⟩ : syracuseStep 989759 = 1484639) B1484639
theorem B662079 : Blo 658307 662079 := bstep (se 1 (by rfl) ⟨496559, by rfl⟩ : syracuseStep 662079 = 993119) B993119
theorem B662087 : Blo 658307 662087 := bstep (se 1 (by rfl) ⟨496565, by rfl⟩ : syracuseStep 662087 = 993131) B993131
theorem B1481399 : Blo 658307 1481399 := bstep (se 1 (by rfl) ⟨1111049, by rfl⟩ : syracuseStep 1481399 = 2222099) B2222099
theorem B989879 : Blo 658307 989879 := bstep (se 1 (by rfl) ⟨742409, by rfl⟩ : syracuseStep 989879 = 1484819) B1484819
theorem B3349187 : Blo 658307 3349187 := bstep (se 1 (by rfl) ⟨2511890, by rfl⟩ : syracuseStep 3349187 = 5023781) B5023781
theorem B662239 : Blo 658307 662239 := bstep (se 1 (by rfl) ⟨496679, by rfl⟩ : syracuseStep 662239 = 993359) B993359
theorem B1481615 : Blo 658307 1481615 := bstep (se 1 (by rfl) ⟨1111211, by rfl⟩ : syracuseStep 1481615 = 2222423) B2222423
theorem B990107 : Blo 658307 990107 := bstep (se 1 (by rfl) ⟨742580, by rfl⟩ : syracuseStep 990107 = 1485161) B1485161
theorem B3251117 : Blo 658307 3251117 := bstep (se 3 (by rfl) ⟨609584, by rfl⟩ : syracuseStep 3251117 = 1219169) B1219169
theorem B9542873 : Blo 658307 9542873 := bstep (se 2 (by rfl) ⟨3578577, by rfl⟩ : syracuseStep 9542873 = 7157155) B7157155
theorem B1055963 : Blo 658307 1055963 := bstep (se 1 (by rfl) ⟨791972, by rfl⟩ : syracuseStep 1055963 = 1583945) B1583945
theorem B24026381 : Blo 658307 24026381 := bstep (se 3 (by rfl) ⟨4504946, by rfl⟩ : syracuseStep 24026381 = 9009893) B9009893
theorem B990503 : Blo 658307 990503 := bstep (se 1 (by rfl) ⟨742877, by rfl⟩ : syracuseStep 990503 = 1485755) B1485755
theorem B75144523 : Blo 658307 75144523 := bstep (se 1 (by rfl) ⟨56358392, by rfl⟩ : syracuseStep 75144523 = 112716785) B112716785
theorem B990587 : Blo 658307 990587 := bstep (se 1 (by rfl) ⟨742940, by rfl⟩ : syracuseStep 990587 = 1485881) B1485881
theorem B990713 : Blo 658307 990713 := bstep (se 2 (by rfl) ⟨371517, by rfl⟩ : syracuseStep 990713 = 743035) B743035
theorem B1482335 : Blo 658307 1482335 := bstep (se 1 (by rfl) ⟨1111751, by rfl⟩ : syracuseStep 1482335 = 2223503) B2223503
theorem B3382879 : Blo 658307 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B990815 : Blo 658307 990815 := bstep (se 1 (by rfl) ⟨743111, by rfl⟩ : syracuseStep 990815 = 1486223) B1486223
theorem B1482551 : Blo 658307 1482551 := bstep (se 1 (by rfl) ⟨1111913, by rfl⟩ : syracuseStep 1482551 = 2223827) B2223827
theorem B991031 : Blo 658307 991031 := bstep (se 1 (by rfl) ⟨743273, by rfl⟩ : syracuseStep 991031 = 1486547) B1486547
theorem B1482857 : Blo 658307 1482857 := bstep (se 2 (by rfl) ⟨556071, by rfl⟩ : syracuseStep 1482857 = 1112143) B1112143
theorem B991337 : Blo 658307 991337 := bstep (se 2 (by rfl) ⟨371751, by rfl⟩ : syracuseStep 991337 = 743503) B743503
theorem B794971 : Blo 658307 794971 := bstep (se 1 (by rfl) ⟨596228, by rfl⟩ : syracuseStep 794971 = 1192457) B1192457
theorem B991655 : Blo 658307 991655 := bstep (se 1 (by rfl) ⟨743741, by rfl⟩ : syracuseStep 991655 = 1487483) B1487483
theorem B991739 : Blo 658307 991739 := bstep (se 1 (by rfl) ⟨743804, by rfl⟩ : syracuseStep 991739 = 1487609) B1487609
theorem B1483343 : Blo 658307 1483343 := bstep (se 1 (by rfl) ⟨1112507, by rfl⟩ : syracuseStep 1483343 = 2225015) B2225015
theorem B991865 : Blo 658307 991865 := bstep (se 2 (by rfl) ⟨371949, by rfl⟩ : syracuseStep 991865 = 743899) B743899
theorem B991919 : Blo 658307 991919 := bstep (se 1 (by rfl) ⟨743939, by rfl⟩ : syracuseStep 991919 = 1487879) B1487879
theorem B3810007 : Blo 658307 3810007 := bstep (se 1 (by rfl) ⟨2857505, by rfl⟩ : syracuseStep 3810007 = 5715011) B5715011
theorem B1483487 : Blo 658307 1483487 := bstep (se 1 (by rfl) ⟨1112615, by rfl⟩ : syracuseStep 1483487 = 2225231) B2225231
theorem B991967 : Blo 658307 991967 := bstep (se 1 (by rfl) ⟨743975, by rfl⟩ : syracuseStep 991967 = 1487951) B1487951
theorem B795547 : Blo 658307 795547 := bstep (se 1 (by rfl) ⟨596660, by rfl⟩ : syracuseStep 795547 = 1193321) B1193321
theorem B1483739 : Blo 658307 1483739 := bstep (se 1 (by rfl) ⟨1112804, by rfl⟩ : syracuseStep 1483739 = 2225609) B2225609
theorem B992231 : Blo 658307 992231 := bstep (se 1 (by rfl) ⟨744173, by rfl⟩ : syracuseStep 992231 = 1488347) B1488347
theorem B1483919 : Blo 658307 1483919 := bstep (se 1 (by rfl) ⟨1112939, by rfl⟩ : syracuseStep 1483919 = 2225879) B2225879
theorem B1484009 : Blo 658307 1484009 := bstep (se 2 (by rfl) ⟨556503, by rfl⟩ : syracuseStep 1484009 = 1113007) B1113007
theorem B992489 : Blo 658307 992489 := bstep (se 2 (by rfl) ⟨372183, by rfl⟩ : syracuseStep 992489 = 744367) B744367
theorem B1484063 : Blo 658307 1484063 := bstep (se 1 (by rfl) ⟨1113047, by rfl⟩ : syracuseStep 1484063 = 2226095) B2226095
theorem B992543 : Blo 658307 992543 := bstep (se 1 (by rfl) ⟨744407, by rfl⟩ : syracuseStep 992543 = 1488815) B1488815
theorem B11412859 : Blo 658307 11412859 := bstep (se 1 (by rfl) ⟨8559644, by rfl⟩ : syracuseStep 11412859 = 17119289) B17119289
theorem B1582523 : Blo 658307 1582523 := bstep (se 1 (by rfl) ⟨1186892, by rfl⟩ : syracuseStep 1582523 = 2373785) B2373785
theorem B992711 : Blo 658307 992711 := bstep (se 1 (by rfl) ⟨744533, by rfl⟩ : syracuseStep 992711 = 1489067) B1489067
theorem B894559 : Blo 658307 894559 := bstep (se 1 (by rfl) ⟨670919, by rfl⟩ : syracuseStep 894559 = 1341839) B1341839
theorem B1582753 : Blo 658307 1582753 := bstep (se 2 (by rfl) ⟨593532, by rfl⟩ : syracuseStep 1582753 = 1187065) B1187065
theorem B1484585 : Blo 658307 1484585 := bstep (se 2 (by rfl) ⟨556719, by rfl⟩ : syracuseStep 1484585 = 1113439) B1113439
theorem B993065 : Blo 658307 993065 := bstep (se 2 (by rfl) ⟨372399, by rfl⟩ : syracuseStep 993065 = 744799) B744799
theorem B993071 : Blo 658307 993071 := bstep (se 1 (by rfl) ⟨744803, by rfl⟩ : syracuseStep 993071 = 1489607) B1489607
theorem B5646287 : Blo 658307 5646287 := bstep (se 1 (by rfl) ⟨4234715, by rfl⟩ : syracuseStep 5646287 = 8469431) B8469431
theorem B1878383 : Blo 658307 1878383 := bstep (se 1 (by rfl) ⟨1408787, by rfl⟩ : syracuseStep 1878383 = 2817575) B2817575
theorem B1255999 : Blo 658307 1255999 := bstep (se 1 (by rfl) ⟨941999, by rfl⟩ : syracuseStep 1255999 = 1883999) B1883999
theorem B1059551 : Blo 658307 1059551 := bstep (se 1 (by rfl) ⟨794663, by rfl⟩ : syracuseStep 1059551 = 1589327) B1589327
theorem B12725059 : Blo 658307 12725059 := bstep (se 1 (by rfl) ⟨9543794, by rfl⟩ : syracuseStep 12725059 = 19087589) B19087589
theorem B1485647 : Blo 658307 1485647 := bstep (se 1 (by rfl) ⟨1114235, by rfl⟩ : syracuseStep 1485647 = 2228471) B2228471
theorem B7154567 : Blo 658307 7154567 := bstep (se 1 (by rfl) ⟨5365925, by rfl⟩ : syracuseStep 7154567 = 10731851) B10731851
theorem B1485863 : Blo 658307 1485863 := bstep (se 1 (by rfl) ⟨1114397, by rfl⟩ : syracuseStep 1485863 = 2228795) B2228795
theorem B1486043 : Blo 658307 1486043 := bstep (se 1 (by rfl) ⟨1114532, by rfl⟩ : syracuseStep 1486043 = 2229065) B2229065
theorem B1780985 : Blo 658307 1780985 := bstep (se 2 (by rfl) ⟨667869, by rfl⟩ : syracuseStep 1780985 = 1335739) B1335739
theorem B1256735 : Blo 658307 1256735 := bstep (se 1 (by rfl) ⟨942551, by rfl⟩ : syracuseStep 1256735 = 1885103) B1885103
theorem B1486241 : Blo 658307 1486241 := bstep (se 2 (by rfl) ⟨557340, by rfl⟩ : syracuseStep 1486241 = 1114681) B1114681
theorem B14299085 : Blo 658307 14299085 := bstep (se 3 (by rfl) ⟨2681078, by rfl⟩ : syracuseStep 14299085 = 5362157) B5362157
theorem B1486799 : Blo 658307 1486799 := bstep (se 1 (by rfl) ⟨1115099, by rfl⟩ : syracuseStep 1486799 = 2230199) B2230199
theorem B16330817 : Blo 658307 16330817 := bstep (se 2 (by rfl) ⟨6124056, by rfl⟩ : syracuseStep 16330817 = 12248113) B12248113
theorem B1487177 : Blo 658307 1487177 := bstep (se 2 (by rfl) ⟨557691, by rfl⟩ : syracuseStep 1487177 = 1115383) B1115383
theorem B1192283 : Blo 658307 1192283 := bstep (se 1 (by rfl) ⟨894212, by rfl⟩ : syracuseStep 1192283 = 1788425) B1788425
theorem B1487195 : Blo 658307 1487195 := bstep (se 1 (by rfl) ⟨1115396, by rfl⟩ : syracuseStep 1487195 = 2230793) B2230793
theorem B14299699 : Blo 658307 14299699 := bstep (se 1 (by rfl) ⟨10724774, by rfl⟩ : syracuseStep 14299699 = 21449549) B21449549
theorem B4240025 : Blo 658307 4240025 := bstep (se 2 (by rfl) ⟨1590009, by rfl⟩ : syracuseStep 4240025 = 3180019) B3180019
theorem B4010719 : Blo 658307 4010719 := bstep (se 1 (by rfl) ⟨3008039, by rfl⟩ : syracuseStep 4010719 = 6016079) B6016079
theorem B1880911 : Blo 658307 1880911 := bstep (se 1 (by rfl) ⟨1410683, by rfl⟩ : syracuseStep 1880911 = 2821367) B2821367
theorem B1487771 : Blo 658307 1487771 := bstep (se 1 (by rfl) ⟨1115828, by rfl⟩ : syracuseStep 1487771 = 2231657) B2231657
theorem B4010917 : Blo 658307 4010917 := bstep (se 4 (by rfl) ⟨376023, by rfl⟩ : syracuseStep 4010917 = 752047) B752047
theorem B1160183 : Blo 658307 1160183 := bstep (se 1 (by rfl) ⟨870137, by rfl⟩ : syracuseStep 1160183 = 1740275) B1740275
theorem B1487969 : Blo 658307 1487969 := bstep (se 2 (by rfl) ⟨557988, by rfl⟩ : syracuseStep 1487969 = 1115977) B1115977
theorem B1586395 : Blo 658307 1586395 := bstep (se 1 (by rfl) ⟨1189796, by rfl⟩ : syracuseStep 1586395 = 2379593) B2379593
theorem B1488167 : Blo 658307 1488167 := bstep (se 1 (by rfl) ⟨1116125, by rfl⟩ : syracuseStep 1488167 = 2232251) B2232251
theorem B2503979 : Blo 658307 2503979 := bstep (se 1 (by rfl) ⟨1877984, by rfl⟩ : syracuseStep 2503979 = 3755969) B3755969
theorem B4011403 : Blo 658307 4011403 := bstep (se 1 (by rfl) ⟨3008552, by rfl⟩ : syracuseStep 4011403 = 6017105) B6017105
theorem B1488545 : Blo 658307 1488545 := bstep (se 2 (by rfl) ⟨558204, by rfl⟩ : syracuseStep 1488545 = 1116409) B1116409
theorem B1488905 : Blo 658307 1488905 := bstep (se 2 (by rfl) ⟨558339, by rfl⟩ : syracuseStep 1488905 = 1116679) B1116679
theorem B6764573 : Blo 658307 6764573 := bstep (se 3 (by rfl) ⟨1268357, by rfl⟩ : syracuseStep 6764573 = 2536715) B2536715
theorem B2111617 : Blo 658307 2111617 := bstep (se 2 (by rfl) ⟨791856, by rfl⟩ : syracuseStep 2111617 = 1583713) B1583713
theorem B20363399 : Blo 658307 20363399 := bstep (se 1 (by rfl) ⟨15272549, by rfl⟩ : syracuseStep 20363399 = 30545099) B30545099
theorem B7125155 : Blo 658307 7125155 := bstep (se 1 (by rfl) ⟨5343866, by rfl⟩ : syracuseStep 7125155 = 10687733) B10687733
theorem B5650661 : Blo 658307 5650661 := bstep (se 4 (by rfl) ⟨529749, by rfl⟩ : syracuseStep 5650661 = 1059499) B1059499
theorem B833915 : Blo 658307 833915 := bstep (se 1 (by rfl) ⟨625436, by rfl⟩ : syracuseStep 833915 = 1250873) B1250873
theorem B1784231 : Blo 658307 1784231 := bstep (se 1 (by rfl) ⟨1338173, by rfl⟩ : syracuseStep 1784231 = 2676347) B2676347
theorem B1489319 : Blo 658307 1489319 := bstep (se 1 (by rfl) ⟨1116989, by rfl⟩ : syracuseStep 1489319 = 2233979) B2233979
theorem B1489427 : Blo 658307 1489427 := bstep (se 1 (by rfl) ⟨1117070, by rfl⟩ : syracuseStep 1489427 = 2234141) B2234141
theorem B2374217 : Blo 658307 2374217 := bstep (se 2 (by rfl) ⟨890331, by rfl⟩ : syracuseStep 2374217 = 1780663) B1780663
theorem B1489481 : Blo 658307 1489481 := bstep (se 2 (by rfl) ⟨558555, by rfl⟩ : syracuseStep 1489481 = 1117111) B1117111
theorem B1882871 : Blo 658307 1882871 := bstep (se 1 (by rfl) ⟨1412153, by rfl⟩ : syracuseStep 1882871 = 2824307) B2824307
theorem B1489895 : Blo 658307 1489895 := bstep (se 1 (by rfl) ⟨1117421, by rfl⟩ : syracuseStep 1489895 = 2234843) B2234843
theorem B1588423 : Blo 658307 1588423 := bstep (se 1 (by rfl) ⟨1191317, by rfl⟩ : syracuseStep 1588423 = 2382635) B2382635
theorem B4767113 : Blo 658307 4767113 := bstep (se 2 (by rfl) ⟨1787667, by rfl⟩ : syracuseStep 4767113 = 3575335) B3575335
theorem B6340355 : Blo 658307 6340355 := bstep (se 1 (by rfl) ⟨4755266, by rfl⟩ : syracuseStep 6340355 = 9510533) B9510533
theorem B835535 : Blo 658307 835535 := bstep (se 1 (by rfl) ⟨626651, by rfl⟩ : syracuseStep 835535 = 1253303) B1253303
theorem B10862693 : Blo 658307 10862693 := bstep (se 4 (by rfl) ⟨1018377, by rfl⟩ : syracuseStep 10862693 = 2036755) B2036755
theorem B2539883 : Blo 658307 2539883 := bstep (se 1 (by rfl) ⟨1904912, by rfl⟩ : syracuseStep 2539883 = 3809825) B3809825
theorem B2507183 : Blo 658307 2507183 := bstep (se 1 (by rfl) ⟨1880387, by rfl⟩ : syracuseStep 2507183 = 3760775) B3760775
theorem B705359 : Blo 658307 705359 := bstep (se 1 (by rfl) ⟨529019, by rfl⟩ : syracuseStep 705359 = 1058039) B1058039
theorem B836507 : Blo 658307 836507 := bstep (se 1 (by rfl) ⟨627380, by rfl⟩ : syracuseStep 836507 = 1254761) B1254761
theorem B5358595 : Blo 658307 5358595 := bstep (se 1 (by rfl) ⟨4018946, by rfl⟩ : syracuseStep 5358595 = 8037893) B8037893
theorem B15418667 : Blo 658307 15418667 := bstep (se 1 (by rfl) ⟨11564000, by rfl⟩ : syracuseStep 15418667 = 23128001) B23128001
theorem B2508155 : Blo 658307 2508155 := bstep (se 1 (by rfl) ⟨1881116, by rfl⟩ : syracuseStep 2508155 = 3762233) B3762233
theorem B4572569 : Blo 658307 4572569 := bstep (se 2 (by rfl) ⟨1714713, by rfl⟩ : syracuseStep 4572569 = 3429427) B3429427
theorem B18041231 : Blo 658307 18041231 := bstep (se 1 (by rfl) ⟨13530923, by rfl⟩ : syracuseStep 18041231 = 27061847) B27061847
theorem B3164795 : Blo 658307 3164795 := bstep (se 1 (by rfl) ⟨2373596, by rfl⟩ : syracuseStep 3164795 = 4747193) B4747193
theorem B41863877 : Blo 658307 41863877 := bstep (se 4 (by rfl) ⟨3924738, by rfl⟩ : syracuseStep 41863877 = 7849477) B7849477
theorem B11258675 : Blo 658307 11258675 := bstep (se 1 (by rfl) ⟨8444006, by rfl⟩ : syracuseStep 11258675 = 16888013) B16888013
theorem B2509811 : Blo 658307 2509811 := bstep (se 1 (by rfl) ⟨1882358, by rfl⟩ : syracuseStep 2509811 = 3764717) B3764717
theorem B1002791 : Blo 658307 1002791 := bstep (se 1 (by rfl) ⟨752093, by rfl⟩ : syracuseStep 1002791 = 1504187) B1504187
theorem B740731 : Blo 658307 740731 := bstep (se 1 (by rfl) ⟨555548, by rfl⟩ : syracuseStep 740731 = 1111097) B1111097
theorem B2379145 : Blo 658307 2379145 := bstep (se 2 (by rfl) ⟨892179, by rfl⟩ : syracuseStep 2379145 = 1784359) B1784359
theorem B5000939 : Blo 658307 5000939 := bstep (se 1 (by rfl) ⟨3750704, by rfl⟩ : syracuseStep 5000939 = 7501409) B7501409
theorem B741199 : Blo 658307 741199 := bstep (se 1 (by rfl) ⟨555899, by rfl⟩ : syracuseStep 741199 = 1111799) B1111799
theorem B1691657 : Blo 658307 1691657 := bstep (se 2 (by rfl) ⟨634371, by rfl⟩ : syracuseStep 1691657 = 1268743) B1268743
theorem B2150459 : Blo 658307 2150459 := bstep (se 1 (by rfl) ⟨1612844, by rfl⟩ : syracuseStep 2150459 = 3225689) B3225689
theorem B741595 : Blo 658307 741595 := bstep (se 1 (by rfl) ⟨556196, by rfl⟩ : syracuseStep 741595 = 1112393) B1112393
theorem B10703177 : Blo 658307 10703177 := bstep (se 2 (by rfl) ⟨4013691, by rfl⟩ : syracuseStep 10703177 = 8027383) B8027383
theorem B2675051 : Blo 658307 2675051 := bstep (se 1 (by rfl) ⟨2006288, by rfl⟩ : syracuseStep 2675051 = 4012577) B4012577
theorem B741883 : Blo 658307 741883 := bstep (se 1 (by rfl) ⟨556412, by rfl⟩ : syracuseStep 741883 = 1112825) B1112825
theorem B5624417 : Blo 658307 5624417 := bstep (se 2 (by rfl) ⟨2109156, by rfl⟩ : syracuseStep 5624417 = 4218313) B4218313
theorem B742063 : Blo 658307 742063 := bstep (se 1 (by rfl) ⟨556547, by rfl⟩ : syracuseStep 742063 = 1113095) B1113095
theorem B938719 : Blo 658307 938719 := bstep (se 1 (by rfl) ⟨704039, by rfl⟩ : syracuseStep 938719 = 1408079) B1408079
theorem B742351 : Blo 658307 742351 := bstep (se 1 (by rfl) ⟨556763, by rfl⟩ : syracuseStep 742351 = 1113527) B1113527
theorem B5002397 : Blo 658307 5002397 := bstep (se 3 (by rfl) ⟨937949, by rfl⟩ : syracuseStep 5002397 = 1875899) B1875899
theorem B4773113 : Blo 658307 4773113 := bstep (se 2 (by rfl) ⟨1789917, by rfl⟩ : syracuseStep 4773113 = 3579835) B3579835
theorem B742747 : Blo 658307 742747 := bstep (se 1 (by rfl) ⟨557060, by rfl⟩ : syracuseStep 742747 = 1114121) B1114121
theorem B742855 : Blo 658307 742855 := bstep (se 1 (by rfl) ⟨557141, by rfl⟩ : syracuseStep 742855 = 1114283) B1114283
theorem B20633221 : Blo 658307 20633221 := bstep (se 4 (by rfl) ⟨1934364, by rfl⟩ : syracuseStep 20633221 = 3868729) B3868729
theorem B2709179 : Blo 658307 2709179 := bstep (se 1 (by rfl) ⟨2031884, by rfl⟩ : syracuseStep 2709179 = 4063769) B4063769
theorem B743215 : Blo 658307 743215 := bstep (se 1 (by rfl) ⟨557411, by rfl⟩ : syracuseStep 743215 = 1114823) B1114823
theorem B2512727 : Blo 658307 2512727 := bstep (se 1 (by rfl) ⟨1884545, by rfl⟩ : syracuseStep 2512727 = 3769091) B3769091
theorem B743323 : Blo 658307 743323 := bstep (se 1 (by rfl) ⟨557492, by rfl⟩ : syracuseStep 743323 = 1114985) B1114985
theorem B6019001 : Blo 658307 6019001 := bstep (se 2 (by rfl) ⟨2257125, by rfl⟩ : syracuseStep 6019001 = 4514251) B4514251
theorem B3168503 : Blo 658307 3168503 := bstep (se 1 (by rfl) ⟨2376377, by rfl⟩ : syracuseStep 3168503 = 4752755) B4752755
theorem B3758359 : Blo 658307 3758359 := bstep (se 1 (by rfl) ⟨2818769, by rfl⟩ : syracuseStep 3758359 = 5637539) B5637539
theorem B743719 : Blo 658307 743719 := bstep (se 1 (by rfl) ⟨557789, by rfl⟩ : syracuseStep 743719 = 1115579) B1115579
theorem B743791 : Blo 658307 743791 := bstep (se 1 (by rfl) ⟨557843, by rfl⟩ : syracuseStep 743791 = 1115687) B1115687
theorem B744007 : Blo 658307 744007 := bstep (se 1 (by rfl) ⟨558005, by rfl⟩ : syracuseStep 744007 = 1116011) B1116011
theorem B9034415 : Blo 658307 9034415 := bstep (se 1 (by rfl) ⟨6775811, by rfl⟩ : syracuseStep 9034415 = 13551623) B13551623
theorem B3562231 : Blo 658307 3562231 := bstep (se 1 (by rfl) ⟨2671673, by rfl⟩ : syracuseStep 3562231 = 5343347) B5343347
theorem B1203175 : Blo 658307 1203175 := bstep (se 1 (by rfl) ⟨902381, by rfl⟩ : syracuseStep 1203175 = 1804763) B1804763
theorem B1006811 : Blo 658307 1006811 := bstep (se 1 (by rfl) ⟨755108, by rfl⟩ : syracuseStep 1006811 = 1510217) B1510217
theorem B3333473 : Blo 658307 3333473 := bstep (se 2 (by rfl) ⟨1250052, by rfl⟩ : syracuseStep 3333473 = 2500105) B2500105
theorem B744871 : Blo 658307 744871 := bstep (se 1 (by rfl) ⟨558653, by rfl⟩ : syracuseStep 744871 = 1117307) B1117307
theorem B941663 : Blo 658307 941663 := bstep (se 1 (by rfl) ⟨706247, by rfl⟩ : syracuseStep 941663 = 1412495) B1412495
theorem B9625337 : Blo 658307 9625337 := bstep (se 2 (by rfl) ⟨3609501, by rfl⟩ : syracuseStep 9625337 = 7219003) B7219003
theorem B12083107 : Blo 658307 12083107 := bstep (se 1 (by rfl) ⟨9062330, by rfl⟩ : syracuseStep 12083107 = 18124661) B18124661
theorem B1958099 : Blo 658307 1958099 := bstep (se 1 (by rfl) ⟨1468574, by rfl⟩ : syracuseStep 1958099 = 2937149) B2937149
theorem B86794649 : Blo 658307 86794649 := bstep (se 2 (by rfl) ⟨32547993, by rfl⟩ : syracuseStep 86794649 = 65095987) B65095987
theorem B27124253 : Blo 658307 27124253 := bstep (se 3 (by rfl) ⟨5085797, by rfl⟩ : syracuseStep 27124253 = 10171595) B10171595
theorem B3170963 : Blo 658307 3170963 := bstep (se 1 (by rfl) ⟨2378222, by rfl⟩ : syracuseStep 3170963 = 4756445) B4756445
theorem B9495589 : Blo 658307 9495589 := bstep (se 4 (by rfl) ⟨890211, by rfl⟩ : syracuseStep 9495589 = 1780423) B1780423
theorem B3335417 : Blo 658307 3335417 := bstep (se 2 (by rfl) ⟨1250781, by rfl⟩ : syracuseStep 3335417 = 2501563) B2501563
theorem B3565949 : Blo 658307 3565949 := bstep (se 3 (by rfl) ⟨668615, by rfl⟩ : syracuseStep 3565949 = 1337231) B1337231
theorem B16017965 : Blo 658307 16017965 := bstep (se 3 (by rfl) ⟨3003368, by rfl⟩ : syracuseStep 16017965 = 6006737) B6006737
theorem B3173003 : Blo 658307 3173003 := bstep (se 1 (by rfl) ⟨2379752, by rfl⟩ : syracuseStep 3173003 = 4759505) B4759505
theorem B1699321 : Blo 658307 1699321 := bstep (se 2 (by rfl) ⟨637245, by rfl⟩ : syracuseStep 1699321 = 1274491) B1274491
theorem B14282477 : Blo 658307 14282477 := bstep (se 3 (by rfl) ⟨2677964, by rfl⟩ : syracuseStep 14282477 = 5355929) B5355929
theorem B9531341 : Blo 658307 9531341 := bstep (se 3 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 9531341 = 3574253) B3574253
theorem B1667081 : Blo 658307 1667081 := bstep (se 2 (by rfl) ⟨625155, by rfl⟩ : syracuseStep 1667081 = 1250311) B1250311
theorem B2683091 : Blo 658307 2683091 := bstep (se 1 (by rfl) ⟨2012318, by rfl⟩ : syracuseStep 2683091 = 4024637) B4024637
theorem B6353153 : Blo 658307 6353153 := bstep (se 2 (by rfl) ⟨2382432, by rfl⟩ : syracuseStep 6353153 = 4764865) B4764865
theorem B2224475 : Blo 658307 2224475 := bstep (se 1 (by rfl) ⟨1668356, by rfl⟩ : syracuseStep 2224475 = 3336713) B3336713
theorem B4223339 : Blo 658307 4223339 := bstep (se 1 (by rfl) ⟨3167504, by rfl⟩ : syracuseStep 4223339 = 6335009) B6335009
theorem B1110955 : Blo 658307 1110955 := bstep (se 1 (by rfl) ⟨833216, by rfl⟩ : syracuseStep 1110955 = 1666433) B1666433
theorem B2257895 : Blo 658307 2257895 := bstep (se 1 (by rfl) ⟨1693421, by rfl⟩ : syracuseStep 2257895 = 3386843) B3386843
theorem B1668235 : Blo 658307 1668235 := bstep (se 1 (by rfl) ⟨1251176, by rfl⟩ : syracuseStep 1668235 = 2502353) B2502353
theorem B1111259 : Blo 658307 1111259 := bstep (se 1 (by rfl) ⟨833444, by rfl⟩ : syracuseStep 1111259 = 1666889) B1666889
theorem B10712321 : Blo 658307 10712321 := bstep (se 2 (by rfl) ⟨4017120, by rfl⟩ : syracuseStep 10712321 = 8034241) B8034241
theorem B2225447 : Blo 658307 2225447 := bstep (se 1 (by rfl) ⟨1669085, by rfl⟩ : syracuseStep 2225447 = 3338171) B3338171
theorem B2815337 : Blo 658307 2815337 := bstep (se 2 (by rfl) ⟨1055751, by rfl⟩ : syracuseStep 2815337 = 2111503) B2111503
theorem B3339629 : Blo 658307 3339629 := bstep (se 3 (by rfl) ⟨626180, by rfl⟩ : syracuseStep 3339629 = 1252361) B1252361
theorem B750971 : Blo 658307 750971 := bstep (se 1 (by rfl) ⟨563228, by rfl⟩ : syracuseStep 750971 = 1126457) B1126457
theorem B1668539 : Blo 658307 1668539 := bstep (se 1 (by rfl) ⟨1251404, by rfl⟩ : syracuseStep 1668539 = 2502809) B2502809
theorem B1111495 : Blo 658307 1111495 := bstep (se 1 (by rfl) ⟨833621, by rfl⟩ : syracuseStep 1111495 = 1667243) B1667243
theorem B6026885 : Blo 658307 6026885 := bstep (se 4 (by rfl) ⟨565020, by rfl⟩ : syracuseStep 6026885 = 1130041) B1130041
theorem B1406651 : Blo 658307 1406651 := bstep (se 1 (by rfl) ⟨1054988, by rfl⟩ : syracuseStep 1406651 = 2109977) B2109977
theorem B1112015 : Blo 658307 1112015 := bstep (se 1 (by rfl) ⟨834011, by rfl⟩ : syracuseStep 1112015 = 1668023) B1668023
theorem B2226311 : Blo 658307 2226311 := bstep (se 1 (by rfl) ⟨1669733, by rfl⟩ : syracuseStep 2226311 = 3339467) B3339467
theorem B18086125 : Blo 658307 18086125 := bstep (se 3 (by rfl) ⟨3391148, by rfl⟩ : syracuseStep 18086125 = 6782297) B6782297
theorem B1505719 : Blo 658307 1505719 := bstep (se 1 (by rfl) ⟨1129289, by rfl⟩ : syracuseStep 1505719 = 2258579) B2258579
theorem B1112683 : Blo 658307 1112683 := bstep (se 1 (by rfl) ⟨834512, by rfl⟩ : syracuseStep 1112683 = 1669025) B1669025
theorem B1473131 : Blo 658307 1473131 := bstep (se 1 (by rfl) ⟨1104848, by rfl⟩ : syracuseStep 1473131 = 2209697) B2209697
theorem B1669855 : Blo 658307 1669855 := bstep (se 1 (by rfl) ⟨1252391, by rfl⟩ : syracuseStep 1669855 = 2504783) B2504783
theorem B1669967 : Blo 658307 1669967 := bstep (se 1 (by rfl) ⟨1252475, by rfl⟩ : syracuseStep 1669967 = 2504951) B2504951
theorem B1112987 : Blo 658307 1112987 := bstep (se 1 (by rfl) ⟨834740, by rfl⟩ : syracuseStep 1112987 = 1669481) B1669481
theorem B5012603 : Blo 658307 5012603 := bstep (se 1 (by rfl) ⟨3759452, by rfl⟩ : syracuseStep 5012603 = 7518905) B7518905
theorem B2227553 : Blo 658307 2227553 := bstep (se 2 (by rfl) ⟨835332, by rfl⟩ : syracuseStep 2227553 = 1670665) B1670665
theorem B1670615 : Blo 658307 1670615 := bstep (se 1 (by rfl) ⟨1252961, by rfl⟩ : syracuseStep 1670615 = 2505923) B2505923
theorem B11271797 : Blo 658307 11271797 := bstep (se 5 (by rfl) ⟨528365, by rfl⟩ : syracuseStep 11271797 = 1056731) B1056731
theorem B3342059 : Blo 658307 3342059 := bstep (se 1 (by rfl) ⟨2506544, by rfl⟩ : syracuseStep 3342059 = 5013089) B5013089
theorem B1670969 : Blo 658307 1670969 := bstep (se 2 (by rfl) ⟨626613, by rfl⟩ : syracuseStep 1670969 = 1253227) B1253227
theorem B1408873 : Blo 658307 1408873 := bstep (se 2 (by rfl) ⟨528327, by rfl⟩ : syracuseStep 1408873 = 1056655) B1056655
theorem B7241795 : Blo 658307 7241795 := bstep (se 1 (by rfl) ⟨5431346, by rfl⟩ : syracuseStep 7241795 = 10862693) B10862693
theorem B2228363 : Blo 658307 2228363 := bstep (se 1 (by rfl) ⟨1671272, by rfl⟩ : syracuseStep 2228363 = 3342545) B3342545
theorem B1671455 : Blo 658307 1671455 := bstep (se 1 (by rfl) ⟨1253591, by rfl⟩ : syracuseStep 1671455 = 2507183) B2507183
theorem B2228687 : Blo 658307 2228687 := bstep (se 1 (by rfl) ⟨1671515, by rfl⟩ : syracuseStep 2228687 = 3343031) B3343031
theorem B2229011 : Blo 658307 2229011 := bstep (se 1 (by rfl) ⟨1671758, by rfl⟩ : syracuseStep 2229011 = 3343517) B3343517
theorem B1672103 : Blo 658307 1672103 := bstep (se 1 (by rfl) ⟨1254077, by rfl⟩ : syracuseStep 1672103 = 2508155) B2508155
theorem B5080009 : Blo 658307 5080009 := bstep (se 2 (by rfl) ⟨1905003, by rfl⟩ : syracuseStep 5080009 = 3810007) B3810007
theorem B7537859 : Blo 658307 7537859 := bstep (se 1 (by rfl) ⟨5653394, by rfl⟩ : syracuseStep 7537859 = 11306789) B11306789
theorem B7144793 : Blo 658307 7144793 := bstep (se 2 (by rfl) ⟨2679297, by rfl⟩ : syracuseStep 7144793 = 5358595) B5358595
theorem B12027487 : Blo 658307 12027487 := bstep (se 1 (by rfl) ⟨9020615, by rfl⟩ : syracuseStep 12027487 = 18041231) B18041231
theorem B2229875 : Blo 658307 2229875 := bstep (se 1 (by rfl) ⟨1672406, by rfl⟩ : syracuseStep 2229875 = 3344813) B3344813
theorem B1115815 : Blo 658307 1115815 := bstep (se 1 (by rfl) ⟨836861, by rfl⟩ : syracuseStep 1115815 = 1673723) B1673723
theorem B2229983 : Blo 658307 2229983 := bstep (se 1 (by rfl) ⟨1672487, by rfl⟩ : syracuseStep 2229983 = 3344975) B3344975
theorem B7505783 : Blo 658307 7505783 := bstep (se 1 (by rfl) ⟨5629337, by rfl⟩ : syracuseStep 7505783 = 11258675) B11258675
theorem B2230145 : Blo 658307 2230145 := bstep (se 2 (by rfl) ⟨836304, by rfl⟩ : syracuseStep 2230145 = 1672609) B1672609
theorem B3344327 : Blo 658307 3344327 := bstep (se 1 (by rfl) ⟨2508245, by rfl⟩ : syracuseStep 3344327 = 5016491) B5016491
theorem B1673207 : Blo 658307 1673207 := bstep (se 1 (by rfl) ⟨1254905, by rfl⟩ : syracuseStep 1673207 = 2509811) B2509811
theorem B1116463 : Blo 658307 1116463 := bstep (se 1 (by rfl) ⟨837347, by rfl⟩ : syracuseStep 1116463 = 1674695) B1674695
theorem B2230685 : Blo 658307 2230685 := bstep (se 3 (by rfl) ⟨418253, by rfl⟩ : syracuseStep 2230685 = 836507) B836507
theorem B2230955 : Blo 658307 2230955 := bstep (se 1 (by rfl) ⟨1673216, by rfl⟩ : syracuseStep 2230955 = 3346433) B3346433
theorem B1116983 : Blo 658307 1116983 := bstep (se 1 (by rfl) ⟨837737, by rfl⟩ : syracuseStep 1116983 = 1675475) B1675475
theorem B658335 : Blo 658307 658335 := bstep (se 1 (by rfl) ⟨493751, by rfl⟩ : syracuseStep 658335 = 987503) B987503
theorem B658479 : Blo 658307 658479 := bstep (se 1 (by rfl) ⟨493859, by rfl⟩ : syracuseStep 658479 = 987719) B987719
theorem B658503 : Blo 658307 658503 := bstep (se 1 (by rfl) ⟨493877, by rfl⟩ : syracuseStep 658503 = 987755) B987755
theorem B2231495 : Blo 658307 2231495 := bstep (se 1 (by rfl) ⟨1673621, by rfl⟩ : syracuseStep 2231495 = 3347243) B3347243
theorem B658655 : Blo 658307 658655 := bstep (se 1 (by rfl) ⟨493991, by rfl⟩ : syracuseStep 658655 = 987983) B987983
theorem B1674665 : Blo 658307 1674665 := bstep (se 2 (by rfl) ⟨627999, by rfl⟩ : syracuseStep 1674665 = 1255999) B1255999
theorem B658919 : Blo 658307 658919 := bstep (se 1 (by rfl) ⟨494189, by rfl⟩ : syracuseStep 658919 = 988379) B988379
theorem B3182075 : Blo 658307 3182075 := bstep (se 1 (by rfl) ⟨2386556, by rfl⟩ : syracuseStep 3182075 = 4773113) B4773113
theorem B659035 : Blo 658307 659035 := bstep (se 1 (by rfl) ⟨494276, by rfl⟩ : syracuseStep 659035 = 988553) B988553
theorem B38145653 : Blo 658307 38145653 := bstep (se 5 (by rfl) ⟨1788077, by rfl⟩ : syracuseStep 38145653 = 3576155) B3576155
theorem B2002589 : Blo 658307 2002589 := bstep (se 3 (by rfl) ⟨375485, by rfl⟩ : syracuseStep 2002589 = 750971) B750971
theorem B12193517 : Blo 658307 12193517 := bstep (se 3 (by rfl) ⟨2286284, by rfl⟩ : syracuseStep 12193517 = 4572569) B4572569
theorem B1806119 : Blo 658307 1806119 := bstep (se 1 (by rfl) ⟨1354589, by rfl⟩ : syracuseStep 1806119 = 2709179) B2709179
theorem B659271 : Blo 658307 659271 := bstep (se 1 (by rfl) ⟨494453, by rfl⟩ : syracuseStep 659271 = 988907) B988907
theorem B1675151 : Blo 658307 1675151 := bstep (se 1 (by rfl) ⟨1256363, by rfl⟩ : syracuseStep 1675151 = 2512727) B2512727
theorem B659423 : Blo 658307 659423 := bstep (se 1 (by rfl) ⟨494567, by rfl⟩ : syracuseStep 659423 = 989135) B989135
theorem B659687 : Blo 658307 659687 := bstep (se 1 (by rfl) ⟨494765, by rfl⟩ : syracuseStep 659687 = 989531) B989531
theorem B659839 : Blo 658307 659839 := bstep (se 1 (by rfl) ⟨494879, by rfl⟩ : syracuseStep 659839 = 989759) B989759
theorem B987599 : Blo 658307 987599 := bstep (se 1 (by rfl) ⟨740699, by rfl⟩ : syracuseStep 987599 = 1481399) B1481399
theorem B659919 : Blo 658307 659919 := bstep (se 1 (by rfl) ⟨494939, by rfl⟩ : syracuseStep 659919 = 989879) B989879
theorem B2232791 : Blo 658307 2232791 := bstep (se 1 (by rfl) ⟨1674593, by rfl⟩ : syracuseStep 2232791 = 3349187) B3349187
theorem B987641 : Blo 658307 987641 := bstep (se 2 (by rfl) ⟨370365, by rfl⟩ : syracuseStep 987641 = 740731) B740731
theorem B987743 : Blo 658307 987743 := bstep (se 1 (by rfl) ⟨740807, by rfl⟩ : syracuseStep 987743 = 1481615) B1481615
theorem B660071 : Blo 658307 660071 := bstep (se 1 (by rfl) ⟨495053, by rfl⟩ : syracuseStep 660071 = 990107) B990107
theorem B2265761 : Blo 658307 2265761 := bstep (se 2 (by rfl) ⟨849660, by rfl⟩ : syracuseStep 2265761 = 1699321) B1699321
theorem B6361915 : Blo 658307 6361915 := bstep (se 1 (by rfl) ⟨4771436, by rfl⟩ : syracuseStep 6361915 = 9542873) B9542873
theorem B660335 : Blo 658307 660335 := bstep (se 1 (by rfl) ⟨495251, by rfl⟩ : syracuseStep 660335 = 990503) B990503
theorem B660391 : Blo 658307 660391 := bstep (se 1 (by rfl) ⟨495293, by rfl⟩ : syracuseStep 660391 = 990587) B990587
theorem B660475 : Blo 658307 660475 := bstep (se 1 (by rfl) ⟨495356, by rfl⟩ : syracuseStep 660475 = 990713) B990713
theorem B988223 : Blo 658307 988223 := bstep (se 1 (by rfl) ⟨741167, by rfl⟩ : syracuseStep 988223 = 1482335) B1482335
theorem B660543 : Blo 658307 660543 := bstep (se 1 (by rfl) ⟨495407, by rfl⟩ : syracuseStep 660543 = 990815) B990815
theorem B988265 : Blo 658307 988265 := bstep (se 2 (by rfl) ⟨370599, by rfl⟩ : syracuseStep 988265 = 741199) B741199
theorem B988367 : Blo 658307 988367 := bstep (se 1 (by rfl) ⟨741275, by rfl⟩ : syracuseStep 988367 = 1482551) B1482551
theorem B660687 : Blo 658307 660687 := bstep (se 1 (by rfl) ⟨495515, by rfl⟩ : syracuseStep 660687 = 991031) B991031
theorem B988571 : Blo 658307 988571 := bstep (se 1 (by rfl) ⟨741428, by rfl⟩ : syracuseStep 988571 = 1482857) B1482857
theorem B660891 : Blo 658307 660891 := bstep (se 1 (by rfl) ⟨495668, by rfl⟩ : syracuseStep 660891 = 991337) B991337
theorem B661103 : Blo 658307 661103 := bstep (se 1 (by rfl) ⟨495827, by rfl⟩ : syracuseStep 661103 = 991655) B991655
theorem B988793 : Blo 658307 988793 := bstep (se 2 (by rfl) ⟨370797, by rfl⟩ : syracuseStep 988793 = 741595) B741595
theorem B661159 : Blo 658307 661159 := bstep (se 1 (by rfl) ⟨495869, by rfl⟩ : syracuseStep 661159 = 991739) B991739
theorem B988895 : Blo 658307 988895 := bstep (se 1 (by rfl) ⟨741671, by rfl⟩ : syracuseStep 988895 = 1483343) B1483343
theorem B661243 : Blo 658307 661243 := bstep (se 1 (by rfl) ⟨495932, by rfl⟩ : syracuseStep 661243 = 991865) B991865
theorem B661279 : Blo 658307 661279 := bstep (se 1 (by rfl) ⟨495959, by rfl⟩ : syracuseStep 661279 = 991919) B991919
theorem B988991 : Blo 658307 988991 := bstep (se 1 (by rfl) ⟨741743, by rfl⟩ : syracuseStep 988991 = 1483487) B1483487
theorem B661311 : Blo 658307 661311 := bstep (se 1 (by rfl) ⟨495983, by rfl⟩ : syracuseStep 661311 = 991967) B991967
theorem B2234249 : Blo 658307 2234249 := bstep (se 2 (by rfl) ⟨837843, by rfl⟩ : syracuseStep 2234249 = 1675687) B1675687
theorem B989159 : Blo 658307 989159 := bstep (se 1 (by rfl) ⟨741869, by rfl⟩ : syracuseStep 989159 = 1483739) B1483739
theorem B661487 : Blo 658307 661487 := bstep (se 1 (by rfl) ⟨496115, by rfl⟩ : syracuseStep 661487 = 992231) B992231
theorem B989177 : Blo 658307 989177 := bstep (se 2 (by rfl) ⟨370941, by rfl⟩ : syracuseStep 989177 = 741883) B741883
theorem B989279 : Blo 658307 989279 := bstep (se 1 (by rfl) ⟨741959, by rfl⟩ : syracuseStep 989279 = 1483919) B1483919
theorem B2234465 : Blo 658307 2234465 := bstep (se 2 (by rfl) ⟨837924, by rfl⟩ : syracuseStep 2234465 = 1675849) B1675849
theorem B989339 : Blo 658307 989339 := bstep (se 1 (by rfl) ⟨742004, by rfl⟩ : syracuseStep 989339 = 1484009) B1484009
theorem B661659 : Blo 658307 661659 := bstep (se 1 (by rfl) ⟨496244, by rfl⟩ : syracuseStep 661659 = 992489) B992489
theorem B989375 : Blo 658307 989375 := bstep (se 1 (by rfl) ⟨742031, by rfl⟩ : syracuseStep 989375 = 1484063) B1484063
theorem B661695 : Blo 658307 661695 := bstep (se 1 (by rfl) ⟨496271, by rfl⟩ : syracuseStep 661695 = 992543) B992543
theorem B989417 : Blo 658307 989417 := bstep (se 2 (by rfl) ⟨371031, by rfl⟩ : syracuseStep 989417 = 742063) B742063
theorem B1055015 : Blo 658307 1055015 := bstep (se 1 (by rfl) ⟨791261, by rfl⟩ : syracuseStep 1055015 = 1582523) B1582523
theorem B1251625 : Blo 658307 1251625 := bstep (se 2 (by rfl) ⟨469359, by rfl⟩ : syracuseStep 1251625 = 938719) B938719
theorem B5347625 : Blo 658307 5347625 := bstep (se 2 (by rfl) ⟨2005359, by rfl⟩ : syracuseStep 5347625 = 4010719) B4010719
theorem B661807 : Blo 658307 661807 := bstep (se 1 (by rfl) ⟨496355, by rfl⟩ : syracuseStep 661807 = 992711) B992711
theorem B9509197 : Blo 658307 9509197 := bstep (se 3 (by rfl) ⟨1782974, by rfl⟩ : syracuseStep 9509197 = 3565949) B3565949
theorem B8460773 : Blo 658307 8460773 := bstep (se 4 (by rfl) ⟨793197, by rfl⟩ : syracuseStep 8460773 = 1586395) B1586395
theorem B989723 : Blo 658307 989723 := bstep (se 1 (by rfl) ⟨742292, by rfl⟩ : syracuseStep 989723 = 1484585) B1484585
theorem B662043 : Blo 658307 662043 := bstep (se 1 (by rfl) ⟨496532, by rfl⟩ : syracuseStep 662043 = 993065) B993065
theorem B662047 : Blo 658307 662047 := bstep (se 1 (by rfl) ⟨496535, by rfl⟩ : syracuseStep 662047 = 993071) B993071
theorem B5347889 : Blo 658307 5347889 := bstep (se 2 (by rfl) ⟨2005458, by rfl⟩ : syracuseStep 5347889 = 4010917) B4010917
theorem B1481273 : Blo 658307 1481273 := bstep (se 2 (by rfl) ⟨555477, by rfl⟩ : syracuseStep 1481273 = 1110955) B1110955
theorem B989801 : Blo 658307 989801 := bstep (se 2 (by rfl) ⟨371175, by rfl⟩ : syracuseStep 989801 = 742351) B742351
theorem B1252255 : Blo 658307 1252255 := bstep (se 1 (by rfl) ⟨939191, by rfl⟩ : syracuseStep 1252255 = 1878383) B1878383
theorem B990329 : Blo 658307 990329 := bstep (se 2 (by rfl) ⟨371373, by rfl⟩ : syracuseStep 990329 = 742747) B742747
theorem B5348537 : Blo 658307 5348537 := bstep (se 2 (by rfl) ⟨2005701, by rfl⟩ : syracuseStep 5348537 = 4011403) B4011403
theorem B990431 : Blo 658307 990431 := bstep (se 1 (by rfl) ⟨742823, by rfl⟩ : syracuseStep 990431 = 1485647) B1485647
theorem B1481993 : Blo 658307 1481993 := bstep (se 2 (by rfl) ⟨555747, by rfl⟩ : syracuseStep 1481993 = 1111495) B1111495
theorem B990473 : Blo 658307 990473 := bstep (se 2 (by rfl) ⟨371427, by rfl⟩ : syracuseStep 990473 = 742855) B742855
theorem B990575 : Blo 658307 990575 := bstep (se 1 (by rfl) ⟨742931, by rfl⟩ : syracuseStep 990575 = 1485863) B1485863
theorem B990695 : Blo 658307 990695 := bstep (se 1 (by rfl) ⟨743021, by rfl⟩ : syracuseStep 990695 = 1486043) B1486043
theorem B990827 : Blo 658307 990827 := bstep (se 1 (by rfl) ⟨743120, by rfl⟩ : syracuseStep 990827 = 1486241) B1486241
theorem B990953 : Blo 658307 990953 := bstep (se 2 (by rfl) ⟨371607, by rfl⟩ : syracuseStep 990953 = 743215) B743215
theorem B991097 : Blo 658307 991097 := bstep (se 2 (by rfl) ⟨371661, by rfl⟩ : syracuseStep 991097 = 743323) B743323
theorem B991199 : Blo 658307 991199 := bstep (se 1 (by rfl) ⟨743399, by rfl⟩ : syracuseStep 991199 = 1486799) B1486799
theorem B10887211 : Blo 658307 10887211 := bstep (se 1 (by rfl) ⟨8165408, by rfl⟩ : syracuseStep 10887211 = 16330817) B16330817
theorem B4235435 : Blo 658307 4235435 := bstep (se 1 (by rfl) ⟨3176576, by rfl⟩ : syracuseStep 4235435 = 6353153) B6353153
theorem B991451 : Blo 658307 991451 := bstep (se 1 (by rfl) ⟨743588, by rfl⟩ : syracuseStep 991451 = 1487177) B1487177
theorem B1482983 : Blo 658307 1482983 := bstep (se 1 (by rfl) ⟨1112237, by rfl⟩ : syracuseStep 1482983 = 2224475) B2224475
theorem B991463 : Blo 658307 991463 := bstep (se 1 (by rfl) ⟨743597, by rfl⟩ : syracuseStep 991463 = 1487195) B1487195
theorem B794855 : Blo 658307 794855 := bstep (se 1 (by rfl) ⟨596141, by rfl⟩ : syracuseStep 794855 = 1192283) B1192283
theorem B991625 : Blo 658307 991625 := bstep (se 2 (by rfl) ⟨371859, by rfl⟩ : syracuseStep 991625 = 743719) B743719
theorem B2826683 : Blo 658307 2826683 := bstep (se 1 (by rfl) ⟨2120012, by rfl⟩ : syracuseStep 2826683 = 4240025) B4240025
theorem B991721 : Blo 658307 991721 := bstep (se 2 (by rfl) ⟨371895, by rfl⟩ : syracuseStep 991721 = 743791) B743791
theorem B2007625 : Blo 658307 2007625 := bstep (se 2 (by rfl) ⟨752859, by rfl⟩ : syracuseStep 2007625 = 1505719) B1505719
theorem B991847 : Blo 658307 991847 := bstep (se 1 (by rfl) ⟨743885, by rfl⟩ : syracuseStep 991847 = 1487771) B1487771
theorem B991979 : Blo 658307 991979 := bstep (se 1 (by rfl) ⟨743984, by rfl⟩ : syracuseStep 991979 = 1487969) B1487969
theorem B3351293 : Blo 658307 3351293 := bstep (se 3 (by rfl) ⟨628367, by rfl⟩ : syracuseStep 3351293 = 1256735) B1256735
theorem B992009 : Blo 658307 992009 := bstep (se 2 (by rfl) ⟨372003, by rfl⟩ : syracuseStep 992009 = 744007) B744007
theorem B1483577 : Blo 658307 1483577 := bstep (se 2 (by rfl) ⟨556341, by rfl⟩ : syracuseStep 1483577 = 1112683) B1112683
theorem B1483631 : Blo 658307 1483631 := bstep (se 1 (by rfl) ⟨1112723, by rfl⟩ : syracuseStep 1483631 = 2225447) B2225447
theorem B992111 : Blo 658307 992111 := bstep (se 1 (by rfl) ⟨744083, by rfl⟩ : syracuseStep 992111 = 1488167) B1488167
theorem B1876891 : Blo 658307 1876891 := bstep (se 1 (by rfl) ⟨1407668, by rfl⟩ : syracuseStep 1876891 = 2815337) B2815337
theorem B992363 : Blo 658307 992363 := bstep (se 1 (by rfl) ⟨744272, by rfl⟩ : syracuseStep 992363 = 1488545) B1488545
theorem B992603 : Blo 658307 992603 := bstep (se 1 (by rfl) ⟨744452, by rfl⟩ : syracuseStep 992603 = 1488905) B1488905
theorem B1484207 : Blo 658307 1484207 := bstep (se 1 (by rfl) ⟨1113155, by rfl⟩ : syracuseStep 1484207 = 2226311) B2226311
theorem B13575599 : Blo 658307 13575599 := bstep (se 1 (by rfl) ⟨10181699, by rfl⟩ : syracuseStep 13575599 = 20363399) B20363399
theorem B1189487 : Blo 658307 1189487 := bstep (se 1 (by rfl) ⟨892115, by rfl⟩ : syracuseStep 1189487 = 1784231) B1784231
theorem B992879 : Blo 658307 992879 := bstep (se 1 (by rfl) ⟨744659, by rfl⟩ : syracuseStep 992879 = 1489319) B1489319
theorem B992951 : Blo 658307 992951 := bstep (se 1 (by rfl) ⟨744713, by rfl⟩ : syracuseStep 992951 = 1489427) B1489427
theorem B1582811 : Blo 658307 1582811 := bstep (se 1 (by rfl) ⟨1187108, by rfl⟩ : syracuseStep 1582811 = 2374217) B2374217
theorem B992987 : Blo 658307 992987 := bstep (se 1 (by rfl) ⟨744740, by rfl⟩ : syracuseStep 992987 = 1489481) B1489481
theorem B1255247 : Blo 658307 1255247 := bstep (se 1 (by rfl) ⟨941435, by rfl⟩ : syracuseStep 1255247 = 1882871) B1882871
theorem B993161 : Blo 658307 993161 := bstep (se 2 (by rfl) ⟨372435, by rfl⟩ : syracuseStep 993161 = 744871) B744871
theorem B993263 : Blo 658307 993263 := bstep (se 1 (by rfl) ⟨744947, by rfl⟩ : syracuseStep 993263 = 1489895) B1489895
theorem B1485035 : Blo 658307 1485035 := bstep (se 1 (by rfl) ⟨1113776, by rfl⟩ : syracuseStep 1485035 = 2227553) B2227553
theorem B7514531 : Blo 658307 7514531 := bstep (se 1 (by rfl) ⟨5635898, by rfl⟩ : syracuseStep 7514531 = 11271797) B11271797
theorem B1878497 : Blo 658307 1878497 := bstep (se 2 (by rfl) ⟨704436, by rfl⟩ : syracuseStep 1878497 = 1408873) B1408873
theorem B1878839 : Blo 658307 1878839 := bstep (se 1 (by rfl) ⟨1409129, by rfl⟩ : syracuseStep 1878839 = 2818259) B2818259
theorem B1059961 : Blo 658307 1059961 := bstep (se 2 (by rfl) ⟨397485, by rfl⟩ : syracuseStep 1059961 = 794971) B794971
theorem B5221597 : Blo 658307 5221597 := bstep (se 3 (by rfl) ⟨979049, by rfl⟩ : syracuseStep 5221597 = 1958099) B1958099
theorem B1486331 : Blo 658307 1486331 := bstep (se 1 (by rfl) ⟨1114748, by rfl⟩ : syracuseStep 1486331 = 2229497) B2229497
theorem B1879625 : Blo 658307 1879625 := bstep (se 2 (by rfl) ⟨704859, by rfl⟩ : syracuseStep 1879625 = 1409719) B1409719
theorem B1486511 : Blo 658307 1486511 := bstep (se 1 (by rfl) ⟨1114883, by rfl⟩ : syracuseStep 1486511 = 2229767) B2229767
theorem B12660785 : Blo 658307 12660785 := bstep (se 2 (by rfl) ⟨4747794, by rfl⟩ : syracuseStep 12660785 = 9495589) B9495589
theorem B1487159 : Blo 658307 1487159 := bstep (se 1 (by rfl) ⟨1115369, by rfl⟩ : syracuseStep 1487159 = 2230739) B2230739
theorem B1487231 : Blo 658307 1487231 := bstep (se 1 (by rfl) ⟨1115423, by rfl⟩ : syracuseStep 1487231 = 2230847) B2230847
theorem B2109863 : Blo 658307 2109863 := bstep (se 1 (by rfl) ⟨1582397, by rfl⟩ : syracuseStep 2109863 = 3164795) B3164795
theorem B15217145 : Blo 658307 15217145 := bstep (se 2 (by rfl) ⟨5706429, by rfl⟩ : syracuseStep 15217145 = 11412859) B11412859
theorem B5092055 : Blo 658307 5092055 := bstep (se 1 (by rfl) ⟨3819041, by rfl⟩ : syracuseStep 5092055 = 7638083) B7638083
theorem B1192745 : Blo 658307 1192745 := bstep (se 2 (by rfl) ⟨447279, by rfl⟩ : syracuseStep 1192745 = 894559) B894559
theorem B1880957 : Blo 658307 1880957 := bstep (se 3 (by rfl) ⟨352679, by rfl⟩ : syracuseStep 1880957 = 705359) B705359
theorem B2110337 : Blo 658307 2110337 := bstep (se 2 (by rfl) ⟨791376, by rfl⟩ : syracuseStep 2110337 = 1582753) B1582753
theorem B1881083 : Blo 658307 1881083 := bstep (se 1 (by rfl) ⟨1410812, by rfl⟩ : syracuseStep 1881083 = 2821625) B2821625
theorem B4240457 : Blo 658307 4240457 := bstep (se 2 (by rfl) ⟨1590171, by rfl⟩ : syracuseStep 4240457 = 3180343) B3180343
theorem B1881299 : Blo 658307 1881299 := bstep (se 1 (by rfl) ⟨1410974, by rfl⟩ : syracuseStep 1881299 = 2821949) B2821949
theorem B3093821 : Blo 658307 3093821 := bstep (se 3 (by rfl) ⟨580091, by rfl⟩ : syracuseStep 3093821 = 1160183) B1160183
theorem B1127771 : Blo 658307 1127771 := bstep (se 1 (by rfl) ⟨845828, by rfl⟩ : syracuseStep 1127771 = 1691657) B1691657
theorem B1783367 : Blo 658307 1783367 := bstep (se 1 (by rfl) ⟨1337525, by rfl⟩ : syracuseStep 1783367 = 2675051) B2675051
theorem B1488455 : Blo 658307 1488455 := bstep (se 1 (by rfl) ⟨1116341, by rfl⟩ : syracuseStep 1488455 = 2232683) B2232683
theorem B3749611 : Blo 658307 3749611 := bstep (se 1 (by rfl) ⟨2812208, by rfl⟩ : syracuseStep 3749611 = 5624417) B5624417
theorem B1488635 : Blo 658307 1488635 := bstep (se 1 (by rfl) ⟨1116476, by rfl⟩ : syracuseStep 1488635 = 2232953) B2232953
theorem B1489193 : Blo 658307 1489193 := bstep (se 2 (by rfl) ⟨558447, by rfl⟩ : syracuseStep 1489193 = 1116895) B1116895
theorem B4012667 : Blo 658307 4012667 := bstep (se 1 (by rfl) ⟨3009500, by rfl⟩ : syracuseStep 4012667 = 6019001) B6019001
theorem B2112335 : Blo 658307 2112335 := bstep (se 1 (by rfl) ⟨1584251, by rfl⟩ : syracuseStep 2112335 = 3168503) B3168503
theorem B1489769 : Blo 658307 1489769 := bstep (se 2 (by rfl) ⟨558663, by rfl⟩ : syracuseStep 1489769 = 1117327) B1117327
theorem B1489823 : Blo 658307 1489823 := bstep (se 1 (by rfl) ⟨1117367, by rfl⟩ : syracuseStep 1489823 = 2234735) B2234735
theorem B3751069 : Blo 658307 3751069 := bstep (se 3 (by rfl) ⟨703325, by rfl⟩ : syracuseStep 3751069 = 1406651) B1406651
theorem B2112797 : Blo 658307 2112797 := bstep (se 3 (by rfl) ⟨396149, by rfl⟩ : syracuseStep 2112797 = 792299) B792299
theorem B4242917 : Blo 658307 4242917 := bstep (se 4 (by rfl) ⟨397773, by rfl⟩ : syracuseStep 4242917 = 795547) B795547
theorem B703975 : Blo 658307 703975 := bstep (se 1 (by rfl) ⟨527981, by rfl⟩ : syracuseStep 703975 = 1055963) B1055963
theorem B671207 : Blo 658307 671207 := bstep (se 1 (by rfl) ⟨503405, by rfl⟩ : syracuseStep 671207 = 1006811) B1006811
theorem B1883873 : Blo 658307 1883873 := bstep (se 2 (by rfl) ⟨706452, by rfl⟩ : syracuseStep 1883873 = 1412905) B1412905
theorem B2113975 : Blo 658307 2113975 := bstep (se 1 (by rfl) ⟨1585481, by rfl⟩ : syracuseStep 2113975 = 3170963) B3170963
theorem B2507881 : Blo 658307 2507881 := bstep (se 2 (by rfl) ⟨940455, by rfl⟩ : syracuseStep 2507881 = 1880911) B1880911
theorem B1885513 : Blo 658307 1885513 := bstep (se 2 (by rfl) ⟨707067, by rfl⟩ : syracuseStep 1885513 = 1414135) B1414135
theorem B8439497 : Blo 658307 8439497 := bstep (se 2 (by rfl) ⟨3164811, by rfl⟩ : syracuseStep 8439497 = 6329623) B6329623
theorem B2115335 : Blo 658307 2115335 := bstep (se 1 (by rfl) ⟨1586501, by rfl⟩ : syracuseStep 2115335 = 3173003) B3173003
theorem B706367 : Blo 658307 706367 := bstep (se 1 (by rfl) ⟨529775, by rfl⟩ : syracuseStep 706367 = 1059551) B1059551
theorem B4769711 : Blo 658307 4769711 := bstep (se 1 (by rfl) ⟨3577283, by rfl⟩ : syracuseStep 4769711 = 7154567) B7154567
theorem B27510961 : Blo 658307 27510961 := bstep (se 2 (by rfl) ⟨10316610, by rfl⟩ : syracuseStep 27510961 = 20633221) B20633221
theorem B2148665 : Blo 658307 2148665 := bstep (se 2 (by rfl) ⟨805749, by rfl⟩ : syracuseStep 2148665 = 1611499) B1611499
theorem B8669645 : Blo 658307 8669645 := bstep (se 3 (by rfl) ⟨1625558, by rfl⟩ : syracuseStep 8669645 = 3251117) B3251117
theorem B9521651 : Blo 658307 9521651 := bstep (se 1 (by rfl) ⟨7141238, by rfl⟩ : syracuseStep 9521651 = 14282477) B14282477
theorem B1788727 : Blo 658307 1788727 := bstep (se 1 (by rfl) ⟨1341545, by rfl⟩ : syracuseStep 1788727 = 2683091) B2683091
theorem B2542873 : Blo 658307 2542873 := bstep (se 2 (by rfl) ⟨953577, by rfl⟩ : syracuseStep 2542873 = 1907155) B1907155
theorem B2674109 : Blo 658307 2674109 := bstep (se 3 (by rfl) ⟨501395, by rfl⟩ : syracuseStep 2674109 = 1002791) B1002791
theorem B740839 : Blo 658307 740839 := bstep (se 1 (by rfl) ⟨555629, by rfl⟩ : syracuseStep 740839 = 1111259) B1111259
theorem B4017923 : Blo 658307 4017923 := bstep (se 1 (by rfl) ⟨3013442, by rfl⟩ : syracuseStep 4017923 = 6026885) B6026885
theorem B741343 : Blo 658307 741343 := bstep (se 1 (by rfl) ⟨556007, by rfl⟩ : syracuseStep 741343 = 1112015) B1112015
theorem B4509715 : Blo 658307 4509715 := bstep (se 1 (by rfl) ⟨3382286, by rfl⟩ : syracuseStep 4509715 = 6764573) B6764573
theorem B2511101 : Blo 658307 2511101 := bstep (se 3 (by rfl) ⟨470831, by rfl⟩ : syracuseStep 2511101 = 941663) B941663
theorem B2117897 : Blo 658307 2117897 := bstep (se 2 (by rfl) ⟨794211, by rfl⟩ : syracuseStep 2117897 = 1588423) B1588423
theorem B100192697 : Blo 658307 100192697 := bstep (se 2 (by rfl) ⟨37572261, by rfl⟩ : syracuseStep 100192697 = 75144523) B75144523
theorem B741991 : Blo 658307 741991 := bstep (se 1 (by rfl) ⟨556493, by rfl⟩ : syracuseStep 741991 = 1112987) B1112987
theorem B4510505 : Blo 658307 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B16110809 : Blo 658307 16110809 := bstep (se 2 (by rfl) ⟨6041553, by rfl⟩ : syracuseStep 16110809 = 12083107) B12083107
theorem B13522555 : Blo 658307 13522555 := bstep (se 1 (by rfl) ⟨10141916, by rfl⟩ : syracuseStep 13522555 = 20283833) B20283833
theorem B10279111 : Blo 658307 10279111 := bstep (se 1 (by rfl) ⟨7709333, by rfl⟩ : syracuseStep 10279111 = 15418667) B15418667
theorem B6773021 : Blo 658307 6773021 := bstep (se 3 (by rfl) ⟨1269941, by rfl⟩ : syracuseStep 6773021 = 2539883) B2539883
theorem B17193467 : Blo 658307 17193467 := bstep (se 1 (by rfl) ⟨12895100, by rfl⟩ : syracuseStep 17193467 = 25790201) B25790201
theorem B27909251 : Blo 658307 27909251 := bstep (se 1 (by rfl) ⟨20931938, by rfl⟩ : syracuseStep 27909251 = 41863877) B41863877
theorem B7527653 : Blo 658307 7527653 := bstep (se 4 (by rfl) ⟨705717, by rfl⟩ : syracuseStep 7527653 = 1411435) B1411435
theorem B745051 : Blo 658307 745051 := bstep (se 1 (by rfl) ⟨558788, by rfl⟩ : syracuseStep 745051 = 1117577) B1117577
theorem B941743 : Blo 658307 941743 := bstep (se 1 (by rfl) ⟨706307, by rfl⟩ : syracuseStep 941743 = 1412615) B1412615
theorem B941863 : Blo 658307 941863 := bstep (se 1 (by rfl) ⟨706397, by rfl⟩ : syracuseStep 941863 = 1412795) B1412795
theorem B3333959 : Blo 658307 3333959 := bstep (se 1 (by rfl) ⟨2500469, by rfl⟩ : syracuseStep 3333959 = 5000939) B5000939
theorem B6021053 : Blo 658307 6021053 := bstep (se 3 (by rfl) ⟨1128947, by rfl⟩ : syracuseStep 6021053 = 2257895) B2257895
theorem B1433639 : Blo 658307 1433639 := bstep (se 1 (by rfl) ⟨1075229, by rfl⟩ : syracuseStep 1433639 = 2150459) B2150459
theorem B2121767 : Blo 658307 2121767 := bstep (se 1 (by rfl) ⟨1591325, by rfl⟩ : syracuseStep 2121767 = 3182651) B3182651
theorem B7135451 : Blo 658307 7135451 := bstep (se 1 (by rfl) ⟨5351588, by rfl⟩ : syracuseStep 7135451 = 10703177) B10703177
theorem B21652103 : Blo 658307 21652103 := bstep (se 1 (by rfl) ⟨16239077, by rfl⟩ : syracuseStep 21652103 = 32478155) B32478155
theorem B3334931 : Blo 658307 3334931 := bstep (se 1 (by rfl) ⟨2501198, by rfl⟩ : syracuseStep 3334931 = 5002397) B5002397
theorem B16966745 : Blo 658307 16966745 := bstep (se 2 (by rfl) ⟨6362529, by rfl⟩ : syracuseStep 16966745 = 12725059) B12725059
theorem B3761275 : Blo 658307 3761275 := bstep (se 1 (by rfl) ⟨2820956, by rfl⟩ : syracuseStep 3761275 = 5641913) B5641913
theorem B6022943 : Blo 658307 6022943 := bstep (se 1 (by rfl) ⟨4517207, by rfl⟩ : syracuseStep 6022943 = 9034415) B9034415
theorem B3172193 : Blo 658307 3172193 := bstep (se 2 (by rfl) ⟨1189572, by rfl⟩ : syracuseStep 3172193 = 2379145) B2379145
theorem B16017587 : Blo 658307 16017587 := bstep (se 1 (by rfl) ⟨12013190, by rfl⟩ : syracuseStep 16017587 = 24026381) B24026381
theorem B2222315 : Blo 658307 2222315 := bstep (se 1 (by rfl) ⟨1666736, by rfl⟩ : syracuseStep 2222315 = 3333473) B3333473
theorem B6416891 : Blo 658307 6416891 := bstep (se 1 (by rfl) ⟨4812668, by rfl⟩ : syracuseStep 6416891 = 9625337) B9625337
theorem B57863099 : Blo 658307 57863099 := bstep (se 1 (by rfl) ⟨43397324, by rfl⟩ : syracuseStep 57863099 = 86794649) B86794649
theorem B18082835 : Blo 658307 18082835 := bstep (se 1 (by rfl) ⟨13562126, by rfl⟩ : syracuseStep 18082835 = 27124253) B27124253
theorem B19066265 : Blo 658307 19066265 := bstep (se 2 (by rfl) ⟨7149849, by rfl⟩ : syracuseStep 19066265 = 14299699) B14299699
theorem B2223611 : Blo 658307 2223611 := bstep (se 1 (by rfl) ⟨1667708, by rfl⟩ : syracuseStep 2223611 = 3335417) B3335417
theorem B2223773 : Blo 658307 2223773 := bstep (se 3 (by rfl) ⟨416957, by rfl⟩ : syracuseStep 2223773 = 833915) B833915
theorem B3764009 : Blo 658307 3764009 := bstep (se 2 (by rfl) ⟨1411503, by rfl⟩ : syracuseStep 3764009 = 2823007) B2823007
theorem B3764191 : Blo 658307 3764191 := bstep (se 1 (by rfl) ⟨2823143, by rfl⟩ : syracuseStep 3764191 = 5646287) B5646287
theorem B2224313 : Blo 658307 2224313 := bstep (se 2 (by rfl) ⟨834117, by rfl⟩ : syracuseStep 2224313 = 1668235) B1668235
theorem B10678643 : Blo 658307 10678643 := bstep (se 1 (by rfl) ⟨8008982, by rfl⟩ : syracuseStep 10678643 = 16017965) B16017965
theorem B6354227 : Blo 658307 6354227 := bstep (se 1 (by rfl) ⟨4765670, by rfl⟩ : syracuseStep 6354227 = 9531341) B9531341
theorem B9532723 : Blo 658307 9532723 := bstep (se 1 (by rfl) ⟨7149542, by rfl⟩ : syracuseStep 9532723 = 14299085) B14299085
theorem B1111387 : Blo 658307 1111387 := bstep (se 1 (by rfl) ⟨833540, by rfl⟩ : syracuseStep 1111387 = 1667081) B1667081
theorem B2815489 : Blo 658307 2815489 := bstep (se 2 (by rfl) ⟨1055808, by rfl⟩ : syracuseStep 2815489 = 2111617) B2111617
theorem B2815559 : Blo 658307 2815559 := bstep (se 1 (by rfl) ⟨2111669, by rfl⟩ : syracuseStep 2815559 = 4223339) B4223339
theorem B24114833 : Blo 658307 24114833 := bstep (se 2 (by rfl) ⟨9043062, by rfl⟩ : syracuseStep 24114833 = 18086125) B18086125
theorem B5011145 : Blo 658307 5011145 := bstep (se 2 (by rfl) ⟨1879179, by rfl⟩ : syracuseStep 5011145 = 3758359) B3758359
theorem B4749293 : Blo 658307 4749293 := bstep (se 3 (by rfl) ⟨890492, by rfl⟩ : syracuseStep 4749293 = 1780985) B1780985
theorem B7141547 : Blo 658307 7141547 := bstep (se 1 (by rfl) ⟨5356160, by rfl⟩ : syracuseStep 7141547 = 10712321) B10712321
theorem B1669319 : Blo 658307 1669319 := bstep (se 1 (by rfl) ⟨1251989, by rfl⟩ : syracuseStep 1669319 = 2503979) B2503979
theorem B2226419 : Blo 658307 2226419 := bstep (se 1 (by rfl) ⟨1669814, by rfl⟩ : syracuseStep 2226419 = 3339629) B3339629
theorem B1112359 : Blo 658307 1112359 := bstep (se 1 (by rfl) ⟨834269, by rfl⟩ : syracuseStep 1112359 = 1668539) B1668539
theorem B2226473 : Blo 658307 2226473 := bstep (se 2 (by rfl) ⟨834927, by rfl⟩ : syracuseStep 2226473 = 1669855) B1669855
theorem B4749641 : Blo 658307 4749641 := bstep (se 2 (by rfl) ⟨1781115, by rfl⟩ : syracuseStep 4749641 = 3562231) B3562231
theorem B12712301 : Blo 658307 12712301 := bstep (se 3 (by rfl) ⟨2383556, by rfl⟩ : syracuseStep 12712301 = 4767113) B4767113
theorem B1604233 : Blo 658307 1604233 := bstep (se 2 (by rfl) ⟨601587, by rfl⟩ : syracuseStep 1604233 = 1203175) B1203175
theorem B4750103 : Blo 658307 4750103 := bstep (se 1 (by rfl) ⟨3562577, by rfl⟩ : syracuseStep 4750103 = 7125155) B7125155
theorem B3767107 : Blo 658307 3767107 := bstep (se 1 (by rfl) ⟨2825330, by rfl⟩ : syracuseStep 3767107 = 5650661) B5650661
theorem B982087 : Blo 658307 982087 := bstep (se 1 (by rfl) ⟨736565, by rfl⟩ : syracuseStep 982087 = 1473131) B1473131
theorem B1113311 : Blo 658307 1113311 := bstep (se 1 (by rfl) ⟨834983, by rfl⟩ : syracuseStep 1113311 = 1669967) B1669967
theorem B3341735 : Blo 658307 3341735 := bstep (se 1 (by rfl) ⟨2506301, by rfl⟩ : syracuseStep 3341735 = 5012603) B5012603
theorem B1113743 : Blo 658307 1113743 := bstep (se 1 (by rfl) ⟨835307, by rfl⟩ : syracuseStep 1113743 = 1670615) B1670615
theorem B2228039 : Blo 658307 2228039 := bstep (se 1 (by rfl) ⟨1671029, by rfl⟩ : syracuseStep 2228039 = 3342059) B3342059
theorem B4226903 : Blo 658307 4226903 := bstep (se 1 (by rfl) ⟨3170177, by rfl⟩ : syracuseStep 4226903 = 6340355) B6340355
theorem B1113979 : Blo 658307 1113979 := bstep (se 1 (by rfl) ⟨835484, by rfl⟩ : syracuseStep 1113979 = 1670969) B1670969
theorem B2228093 : Blo 658307 2228093 := bstep (se 3 (by rfl) ⟨417767, by rfl⟩ : syracuseStep 2228093 = 835535) B835535
theorem B14516281 : Blo 658307 14516281 := bstep (se 2 (by rfl) ⟨5443605, by rfl⟩ : syracuseStep 14516281 = 10887211) B10887211
theorem B1114303 : Blo 658307 1114303 := bstep (se 1 (by rfl) ⟨835727, by rfl⟩ : syracuseStep 1114303 = 1671455) B1671455
theorem B2818633 : Blo 658307 2818633 := bstep (se 2 (by rfl) ⟨1056987, by rfl⟩ : syracuseStep 2818633 = 2113975) B2113975
theorem B1114735 : Blo 658307 1114735 := bstep (se 1 (by rfl) ⟨836051, by rfl⟩ : syracuseStep 1114735 = 1672103) B1672103
theorem B1410223 : Blo 658307 1410223 := bstep (se 1 (by rfl) ⟨1057667, by rfl⟩ : syracuseStep 1410223 = 2115335) B2115335
theorem B3179807 : Blo 658307 3179807 := bstep (se 1 (by rfl) ⟨2384855, by rfl⟩ : syracuseStep 3179807 = 4769711) B4769711
theorem B2229551 : Blo 658307 2229551 := bstep (se 1 (by rfl) ⟨1672163, by rfl⟩ : syracuseStep 2229551 = 3344327) B3344327
theorem B1115471 : Blo 658307 1115471 := bstep (se 1 (by rfl) ⟨836603, by rfl⟩ : syracuseStep 1115471 = 1673207) B1673207
theorem B3343841 : Blo 658307 3343841 := bstep (se 2 (by rfl) ⟨1253940, by rfl⟩ : syracuseStep 3343841 = 2507881) B2507881
theorem B5015033 : Blo 658307 5015033 := bstep (se 2 (by rfl) ⟨1880637, by rfl⟩ : syracuseStep 5015033 = 3761275) B3761275
theorem B1116443 : Blo 658307 1116443 := bstep (se 1 (by rfl) ⟨837332, by rfl⟩ : syracuseStep 1116443 = 1674665) B1674665
theorem B25430435 : Blo 658307 25430435 := bstep (se 1 (by rfl) ⟨19072826, by rfl⟩ : syracuseStep 25430435 = 38145653) B38145653
theorem B8129011 : Blo 658307 8129011 := bstep (se 1 (by rfl) ⟨6096758, by rfl⟩ : syracuseStep 8129011 = 12193517) B12193517
theorem B1116767 : Blo 658307 1116767 := bstep (se 1 (by rfl) ⟨837575, by rfl⟩ : syracuseStep 1116767 = 1675151) B1675151
theorem B1674067 : Blo 658307 1674067 := bstep (se 1 (by rfl) ⟨1255550, by rfl⟩ : syracuseStep 1674067 = 2511101) B2511101
theorem B1411931 : Blo 658307 1411931 := bstep (se 1 (by rfl) ⟨1058948, by rfl⟩ : syracuseStep 1411931 = 2117897) B2117897
theorem B658399 : Blo 658307 658399 := bstep (se 1 (by rfl) ⟨493799, by rfl⟩ : syracuseStep 658399 = 987599) B987599
theorem B658427 : Blo 658307 658427 := bstep (se 1 (by rfl) ⟨493820, by rfl⟩ : syracuseStep 658427 = 987641) B987641
theorem B658495 : Blo 658307 658495 := bstep (se 1 (by rfl) ⟨493871, by rfl⟩ : syracuseStep 658495 = 987743) B987743
theorem B1510507 : Blo 658307 1510507 := bstep (se 1 (by rfl) ⟨1132880, by rfl⟩ : syracuseStep 1510507 = 2265761) B2265761
theorem B658815 : Blo 658307 658815 := bstep (se 1 (by rfl) ⟨494111, by rfl⟩ : syracuseStep 658815 = 988223) B988223
theorem B658843 : Blo 658307 658843 := bstep (se 1 (by rfl) ⟨494132, by rfl⟩ : syracuseStep 658843 = 988265) B988265
theorem B658911 : Blo 658307 658911 := bstep (se 1 (by rfl) ⟨494183, by rfl⟩ : syracuseStep 658911 = 988367) B988367
theorem B659047 : Blo 658307 659047 := bstep (se 1 (by rfl) ⟨494285, by rfl⟩ : syracuseStep 659047 = 988571) B988571
theorem B659195 : Blo 658307 659195 := bstep (se 1 (by rfl) ⟨494396, by rfl⟩ : syracuseStep 659195 = 988793) B988793
theorem B659263 : Blo 658307 659263 := bstep (se 1 (by rfl) ⟨494447, by rfl⟩ : syracuseStep 659263 = 988895) B988895
theorem B659327 : Blo 658307 659327 := bstep (se 1 (by rfl) ⟨494495, by rfl⟩ : syracuseStep 659327 = 988991) B988991
theorem B659439 : Blo 658307 659439 := bstep (se 1 (by rfl) ⟨494579, by rfl⟩ : syracuseStep 659439 = 989159) B989159
theorem B659451 : Blo 658307 659451 := bstep (se 1 (by rfl) ⟨494588, by rfl⟩ : syracuseStep 659451 = 989177) B989177
theorem B659519 : Blo 658307 659519 := bstep (se 1 (by rfl) ⟨494639, by rfl⟩ : syracuseStep 659519 = 989279) B989279
theorem B659559 : Blo 658307 659559 := bstep (se 1 (by rfl) ⟨494669, by rfl⟩ : syracuseStep 659559 = 989339) B989339
theorem B659583 : Blo 658307 659583 := bstep (se 1 (by rfl) ⟨494687, by rfl⟩ : syracuseStep 659583 = 989375) B989375
theorem B659611 : Blo 658307 659611 := bstep (se 1 (by rfl) ⟨494708, by rfl⟩ : syracuseStep 659611 = 989417) B989417
theorem B1413281 : Blo 658307 1413281 := bstep (se 2 (by rfl) ⟨529980, by rfl⟩ : syracuseStep 1413281 = 1059961) B1059961
theorem B5640515 : Blo 658307 5640515 := bstep (se 1 (by rfl) ⟨4230386, by rfl⟩ : syracuseStep 5640515 = 8460773) B8460773
theorem B659815 : Blo 658307 659815 := bstep (se 1 (by rfl) ⟨494861, by rfl⟩ : syracuseStep 659815 = 989723) B989723
theorem B987515 : Blo 658307 987515 := bstep (se 1 (by rfl) ⟨740636, by rfl⟩ : syracuseStep 987515 = 1481273) B1481273
theorem B659867 : Blo 658307 659867 := bstep (se 1 (by rfl) ⟨494900, by rfl⟩ : syracuseStep 659867 = 989801) B989801
theorem B987785 : Blo 658307 987785 := bstep (se 2 (by rfl) ⟨370419, by rfl⟩ : syracuseStep 987785 = 740839) B740839
theorem B660219 : Blo 658307 660219 := bstep (se 1 (by rfl) ⟨495164, by rfl⟩ : syracuseStep 660219 = 990329) B990329
theorem B660287 : Blo 658307 660287 := bstep (se 1 (by rfl) ⟨495215, by rfl⟩ : syracuseStep 660287 = 990431) B990431
theorem B5018435 : Blo 658307 5018435 := bstep (se 1 (by rfl) ⟨3763826, by rfl⟩ : syracuseStep 5018435 = 7527653) B7527653
theorem B987995 : Blo 658307 987995 := bstep (se 1 (by rfl) ⟨740996, by rfl⟩ : syracuseStep 987995 = 1481993) B1481993
theorem B660315 : Blo 658307 660315 := bstep (se 1 (by rfl) ⟨495236, by rfl⟩ : syracuseStep 660315 = 990473) B990473
theorem B660383 : Blo 658307 660383 := bstep (se 1 (by rfl) ⟨495287, by rfl⟩ : syracuseStep 660383 = 990575) B990575
theorem B660463 : Blo 658307 660463 := bstep (se 1 (by rfl) ⟨495347, by rfl⟩ : syracuseStep 660463 = 990695) B990695
theorem B660551 : Blo 658307 660551 := bstep (se 1 (by rfl) ⟨495413, by rfl⟩ : syracuseStep 660551 = 990827) B990827
theorem B660635 : Blo 658307 660635 := bstep (se 1 (by rfl) ⟨495476, by rfl⟩ : syracuseStep 660635 = 990953) B990953
theorem B660731 : Blo 658307 660731 := bstep (se 1 (by rfl) ⟨495548, by rfl⟩ : syracuseStep 660731 = 991097) B991097
theorem B988457 : Blo 658307 988457 := bstep (se 2 (by rfl) ⟨370671, by rfl⟩ : syracuseStep 988457 = 741343) B741343
theorem B5018921 : Blo 658307 5018921 := bstep (se 2 (by rfl) ⟨1882095, by rfl⟩ : syracuseStep 5018921 = 3764191) B3764191
theorem B660799 : Blo 658307 660799 := bstep (se 1 (by rfl) ⟨495599, by rfl⟩ : syracuseStep 660799 = 991199) B991199
theorem B1414511 : Blo 658307 1414511 := bstep (se 1 (by rfl) ⟨1060883, by rfl⟩ : syracuseStep 1414511 = 2121767) B2121767
theorem B2823623 : Blo 658307 2823623 := bstep (se 1 (by rfl) ⟨2117717, by rfl⟩ : syracuseStep 2823623 = 4235435) B4235435
theorem B4756967 : Blo 658307 4756967 := bstep (se 1 (by rfl) ⟨3567725, by rfl⟩ : syracuseStep 4756967 = 7135451) B7135451
theorem B660967 : Blo 658307 660967 := bstep (se 1 (by rfl) ⟨495725, by rfl⟩ : syracuseStep 660967 = 991451) B991451
theorem B988655 : Blo 658307 988655 := bstep (se 1 (by rfl) ⟨741491, by rfl⟩ : syracuseStep 988655 = 1482983) B1482983
theorem B660975 : Blo 658307 660975 := bstep (se 1 (by rfl) ⟨495731, by rfl⟩ : syracuseStep 660975 = 991463) B991463
theorem B661083 : Blo 658307 661083 := bstep (se 1 (by rfl) ⟨495812, by rfl⟩ : syracuseStep 661083 = 991625) B991625
theorem B661147 : Blo 658307 661147 := bstep (se 1 (by rfl) ⟨495860, by rfl⟩ : syracuseStep 661147 = 991721) B991721
theorem B661231 : Blo 658307 661231 := bstep (se 1 (by rfl) ⟨495923, by rfl⟩ : syracuseStep 661231 = 991847) B991847
theorem B661319 : Blo 658307 661319 := bstep (se 1 (by rfl) ⟨495989, by rfl⟩ : syracuseStep 661319 = 991979) B991979
theorem B2234195 : Blo 658307 2234195 := bstep (se 1 (by rfl) ⟨1675646, by rfl⟩ : syracuseStep 2234195 = 3351293) B3351293
theorem B661339 : Blo 658307 661339 := bstep (se 1 (by rfl) ⟨496004, by rfl⟩ : syracuseStep 661339 = 992009) B992009
theorem B989051 : Blo 658307 989051 := bstep (se 1 (by rfl) ⟨741788, by rfl⟩ : syracuseStep 989051 = 1483577) B1483577
theorem B989087 : Blo 658307 989087 := bstep (se 1 (by rfl) ⟨741815, by rfl⟩ : syracuseStep 989087 = 1483631) B1483631
theorem B661407 : Blo 658307 661407 := bstep (se 1 (by rfl) ⟨496055, by rfl⟩ : syracuseStep 661407 = 992111) B992111
theorem B11311163 : Blo 658307 11311163 := bstep (se 1 (by rfl) ⟨8483372, by rfl⟩ : syracuseStep 11311163 = 16966745) B16966745
theorem B661575 : Blo 658307 661575 := bstep (se 1 (by rfl) ⟨496181, by rfl⟩ : syracuseStep 661575 = 992363) B992363
theorem B989321 : Blo 658307 989321 := bstep (se 2 (by rfl) ⟨370995, by rfl⟩ : syracuseStep 989321 = 741991) B741991
theorem B661735 : Blo 658307 661735 := bstep (se 1 (by rfl) ⟨496301, by rfl⟩ : syracuseStep 661735 = 992603) B992603
theorem B989471 : Blo 658307 989471 := bstep (se 1 (by rfl) ⟨742103, by rfl⟩ : syracuseStep 989471 = 1484207) B1484207
theorem B9050399 : Blo 658307 9050399 := bstep (se 1 (by rfl) ⟨6787799, by rfl⟩ : syracuseStep 9050399 = 13575599) B13575599
theorem B792991 : Blo 658307 792991 := bstep (se 1 (by rfl) ⟨594743, by rfl⟩ : syracuseStep 792991 = 1189487) B1189487
theorem B661919 : Blo 658307 661919 := bstep (se 1 (by rfl) ⟨496439, by rfl⟩ : syracuseStep 661919 = 992879) B992879
theorem B661967 : Blo 658307 661967 := bstep (se 1 (by rfl) ⟨496475, by rfl⟩ : syracuseStep 661967 = 992951) B992951
theorem B1055207 : Blo 658307 1055207 := bstep (se 1 (by rfl) ⟨791405, by rfl⟩ : syracuseStep 1055207 = 1582811) B1582811
theorem B661991 : Blo 658307 661991 := bstep (se 1 (by rfl) ⟨496493, by rfl⟩ : syracuseStep 661991 = 992987) B992987
theorem B662107 : Blo 658307 662107 := bstep (se 1 (by rfl) ⟨496580, by rfl⟩ : syracuseStep 662107 = 993161) B993161
theorem B662175 : Blo 658307 662175 := bstep (se 1 (by rfl) ⟨496631, by rfl⟩ : syracuseStep 662175 = 993263) B993263
theorem B1481543 : Blo 658307 1481543 := bstep (se 1 (by rfl) ⟨1111157, by rfl⟩ : syracuseStep 1481543 = 2222315) B2222315
theorem B990023 : Blo 658307 990023 := bstep (se 1 (by rfl) ⟨742517, by rfl⟩ : syracuseStep 990023 = 1485035) B1485035
theorem B1252331 : Blo 658307 1252331 := bstep (se 1 (by rfl) ⟨939248, by rfl⟩ : syracuseStep 1252331 = 1878497) B1878497
theorem B1481849 : Blo 658307 1481849 := bstep (se 2 (by rfl) ⟨555693, by rfl⟩ : syracuseStep 1481849 = 1111387) B1111387
theorem B1252559 : Blo 658307 1252559 := bstep (se 1 (by rfl) ⟨939419, by rfl⟩ : syracuseStep 1252559 = 1878839) B1878839
theorem B38575399 : Blo 658307 38575399 := bstep (se 1 (by rfl) ⟨28931549, by rfl⟩ : syracuseStep 38575399 = 57863099) B57863099
theorem B18030073 : Blo 658307 18030073 := bstep (se 2 (by rfl) ⟨6761277, by rfl⟩ : syracuseStep 18030073 = 13522555) B13522555
theorem B1482407 : Blo 658307 1482407 := bstep (se 1 (by rfl) ⟨1111805, by rfl⟩ : syracuseStep 1482407 = 2223611) B2223611
theorem B990887 : Blo 658307 990887 := bstep (se 1 (by rfl) ⟨743165, by rfl⟩ : syracuseStep 990887 = 1486331) B1486331
theorem B1253083 : Blo 658307 1253083 := bstep (se 1 (by rfl) ⟨939812, by rfl⟩ : syracuseStep 1253083 = 1879625) B1879625
theorem B1482515 : Blo 658307 1482515 := bstep (se 1 (by rfl) ⟨1111886, by rfl⟩ : syracuseStep 1482515 = 2223773) B2223773
theorem B991007 : Blo 658307 991007 := bstep (se 1 (by rfl) ⟨743255, by rfl⟩ : syracuseStep 991007 = 1486511) B1486511
theorem B1482875 : Blo 658307 1482875 := bstep (se 1 (by rfl) ⟨1112156, by rfl⟩ : syracuseStep 1482875 = 2224313) B2224313
theorem B991439 : Blo 658307 991439 := bstep (se 1 (by rfl) ⟨743579, by rfl⟩ : syracuseStep 991439 = 1487159) B1487159
theorem B7119095 : Blo 658307 7119095 := bstep (se 1 (by rfl) ⟨5339321, by rfl⟩ : syracuseStep 7119095 = 10678643) B10678643
theorem B991487 : Blo 658307 991487 := bstep (se 1 (by rfl) ⟨743615, by rfl⟩ : syracuseStep 991487 = 1487231) B1487231
theorem B13705481 : Blo 658307 13705481 := bstep (se 2 (by rfl) ⟨5139555, by rfl⟩ : syracuseStep 13705481 = 10279111) B10279111
theorem B1483145 : Blo 658307 1483145 := bstep (se 2 (by rfl) ⟨556179, by rfl⟩ : syracuseStep 1483145 = 1112359) B1112359
theorem B795163 : Blo 658307 795163 := bstep (se 1 (by rfl) ⟨596372, by rfl⟩ : syracuseStep 795163 = 1192745) B1192745
theorem B1253971 : Blo 658307 1253971 := bstep (se 1 (by rfl) ⟨940478, by rfl⟩ : syracuseStep 1253971 = 1880957) B1880957
theorem B1254055 : Blo 658307 1254055 := bstep (se 1 (by rfl) ⟨940541, by rfl⟩ : syracuseStep 1254055 = 1881083) B1881083
theorem B2826971 : Blo 658307 2826971 := bstep (se 1 (by rfl) ⟨2120228, by rfl⟩ : syracuseStep 2826971 = 4240457) B4240457
theorem B1254199 : Blo 658307 1254199 := bstep (se 1 (by rfl) ⟨940649, by rfl⟩ : syracuseStep 1254199 = 1881299) B1881299
theorem B2138977 : Blo 658307 2138977 := bstep (se 2 (by rfl) ⟨802116, by rfl⟩ : syracuseStep 2138977 = 1604233) B1604233
theorem B4236151 : Blo 658307 4236151 := bstep (se 1 (by rfl) ⟨3177113, by rfl⟩ : syracuseStep 4236151 = 6354227) B6354227
theorem B1877039 : Blo 658307 1877039 := bstep (se 1 (by rfl) ⟨1407779, by rfl⟩ : syracuseStep 1877039 = 2815559) B2815559
theorem B1188911 : Blo 658307 1188911 := bstep (se 1 (by rfl) ⟨891683, by rfl⟩ : syracuseStep 1188911 = 1783367) B1783367
theorem B992303 : Blo 658307 992303 := bstep (se 1 (by rfl) ⟨744227, by rfl⟩ : syracuseStep 992303 = 1488455) B1488455
theorem B5022809 : Blo 658307 5022809 := bstep (se 2 (by rfl) ⟨1883553, by rfl⟩ : syracuseStep 5022809 = 3767107) B3767107
theorem B992423 : Blo 658307 992423 := bstep (se 1 (by rfl) ⟨744317, by rfl⟩ : syracuseStep 992423 = 1488635) B1488635
theorem B4761031 : Blo 658307 4761031 := bstep (se 1 (by rfl) ⟨3570773, by rfl⟩ : syracuseStep 4761031 = 7141547) B7141547
theorem B1484279 : Blo 658307 1484279 := bstep (se 1 (by rfl) ⟨1113209, by rfl⟩ : syracuseStep 1484279 = 2226419) B2226419
theorem B1484315 : Blo 658307 1484315 := bstep (se 1 (by rfl) ⟨1113236, by rfl⟩ : syracuseStep 1484315 = 2226473) B2226473
theorem B992795 : Blo 658307 992795 := bstep (se 1 (by rfl) ⟨744596, by rfl⟩ : syracuseStep 992795 = 1489193) B1489193
theorem B993179 : Blo 658307 993179 := bstep (se 1 (by rfl) ⟨744884, by rfl⟩ : syracuseStep 993179 = 1489769) B1489769
theorem B993215 : Blo 658307 993215 := bstep (se 1 (by rfl) ⟨744911, by rfl⟩ : syracuseStep 993215 = 1489823) B1489823
theorem B993401 : Blo 658307 993401 := bstep (se 2 (by rfl) ⟨372525, by rfl⟩ : syracuseStep 993401 = 745051) B745051
theorem B1255657 : Blo 658307 1255657 := bstep (se 2 (by rfl) ⟨470871, by rfl⟩ : syracuseStep 1255657 = 941743) B941743
theorem B2828611 : Blo 658307 2828611 := bstep (se 1 (by rfl) ⟨2121458, by rfl⟩ : syracuseStep 2828611 = 4242917) B4242917
theorem B1255817 : Blo 658307 1255817 := bstep (se 2 (by rfl) ⟨470931, by rfl⟩ : syracuseStep 1255817 = 941863) B941863
theorem B1255915 : Blo 658307 1255915 := bstep (se 1 (by rfl) ⟨941936, by rfl⟩ : syracuseStep 1255915 = 1883873) B1883873
theorem B1485305 : Blo 658307 1485305 := bstep (se 2 (by rfl) ⟨556989, by rfl⟩ : syracuseStep 1485305 = 1113979) B1113979
theorem B1485359 : Blo 658307 1485359 := bstep (se 1 (by rfl) ⟨1114019, by rfl⟩ : syracuseStep 1485359 = 2228039) B2228039
theorem B1485395 : Blo 658307 1485395 := bstep (se 1 (by rfl) ⟨1114046, by rfl⟩ : syracuseStep 1485395 = 2228093) B2228093
theorem B4827863 : Blo 658307 4827863 := bstep (se 1 (by rfl) ⟨3620897, by rfl⟩ : syracuseStep 4827863 = 7241795) B7241795
theorem B1485575 : Blo 658307 1485575 := bstep (se 1 (by rfl) ⟨1114181, by rfl⟩ : syracuseStep 1485575 = 2228363) B2228363
theorem B1485791 : Blo 658307 1485791 := bstep (se 1 (by rfl) ⟨1114343, by rfl⟩ : syracuseStep 1485791 = 2228687) B2228687
theorem B1486007 : Blo 658307 1486007 := bstep (se 1 (by rfl) ⟨1114505, by rfl⟩ : syracuseStep 1486007 = 2229011) B2229011
theorem B5025239 : Blo 658307 5025239 := bstep (se 1 (by rfl) ⟨3768929, by rfl⟩ : syracuseStep 5025239 = 7537859) B7537859
theorem B4763195 : Blo 658307 4763195 := bstep (se 1 (by rfl) ⟨3572396, by rfl⟩ : syracuseStep 4763195 = 7144793) B7144793
theorem B1486583 : Blo 658307 1486583 := bstep (se 1 (by rfl) ⟨1114937, by rfl⟩ : syracuseStep 1486583 = 2229875) B2229875
theorem B1486655 : Blo 658307 1486655 := bstep (se 1 (by rfl) ⟨1114991, by rfl⟩ : syracuseStep 1486655 = 2229983) B2229983
theorem B2502521 : Blo 658307 2502521 := bstep (se 2 (by rfl) ⟨938445, by rfl⟩ : syracuseStep 2502521 = 1876891) B1876891
theorem B1486763 : Blo 658307 1486763 := bstep (se 1 (by rfl) ⟨1115072, by rfl⟩ : syracuseStep 1486763 = 2230145) B2230145
theorem B1487123 : Blo 658307 1487123 := bstep (se 1 (by rfl) ⟨1115342, by rfl⟩ : syracuseStep 1487123 = 2230685) B2230685
theorem B5779763 : Blo 658307 5779763 := bstep (se 1 (by rfl) ⟨4334822, by rfl⟩ : syracuseStep 5779763 = 8669645) B8669645
theorem B1487303 : Blo 658307 1487303 := bstep (se 1 (by rfl) ⟨1115477, by rfl⟩ : syracuseStep 1487303 = 2230955) B2230955
theorem B16036649 : Blo 658307 16036649 := bstep (se 2 (by rfl) ⟨6013743, by rfl⟩ : syracuseStep 16036649 = 12027487) B12027487
theorem B1487663 : Blo 658307 1487663 := bstep (se 1 (by rfl) ⟨1115747, by rfl⟩ : syracuseStep 1487663 = 2231495) B2231495
theorem B1487753 : Blo 658307 1487753 := bstep (se 2 (by rfl) ⟨557907, by rfl⟩ : syracuseStep 1487753 = 1115815) B1115815
theorem B1782739 : Blo 658307 1782739 := bstep (se 1 (by rfl) ⟨1337054, by rfl⟩ : syracuseStep 1782739 = 2674109) B2674109
theorem B36681281 : Blo 658307 36681281 := bstep (se 2 (by rfl) ⟨13755480, by rfl⟩ : syracuseStep 36681281 = 27510961) B27510961
theorem B66795131 : Blo 658307 66795131 := bstep (se 1 (by rfl) ⟨50096348, by rfl⟩ : syracuseStep 66795131 = 100192697) B100192697
theorem B1488527 : Blo 658307 1488527 := bstep (se 1 (by rfl) ⟨1116395, by rfl⟩ : syracuseStep 1488527 = 2232791) B2232791
theorem B1488617 : Blo 658307 1488617 := bstep (se 2 (by rfl) ⟨558231, by rfl⟩ : syracuseStep 1488617 = 1116463) B1116463
theorem B1489499 : Blo 658307 1489499 := bstep (se 1 (by rfl) ⟨1117124, by rfl⟩ : syracuseStep 1489499 = 2234249) B2234249
theorem B1489643 : Blo 658307 1489643 := bstep (se 1 (by rfl) ⟨1117232, by rfl⟩ : syracuseStep 1489643 = 2234465) B2234465
theorem B703343 : Blo 658307 703343 := bstep (se 1 (by rfl) ⟨527507, by rfl⟩ : syracuseStep 703343 = 1055015) B1055015
theorem B6962129 : Blo 658307 6962129 := bstep (se 2 (by rfl) ⟨2610798, by rfl⟩ : syracuseStep 6962129 = 5221597) B5221597
theorem B3390497 : Blo 658307 3390497 := bstep (se 2 (by rfl) ⟨1271436, by rfl⟩ : syracuseStep 3390497 = 2542873) B2542873
theorem B1883645 : Blo 658307 1883645 := bstep (se 3 (by rfl) ⟨353183, by rfl⟩ : syracuseStep 1883645 = 706367) B706367
theorem B12664781 : Blo 658307 12664781 := bstep (se 3 (by rfl) ⟨2374646, by rfl⟩ : syracuseStep 12664781 = 4749293) B4749293
theorem B4014035 : Blo 658307 4014035 := bstep (se 1 (by rfl) ⟨3010526, by rfl⟩ : syracuseStep 4014035 = 6021053) B6021053
theorem B6012953 : Blo 658307 6012953 := bstep (se 2 (by rfl) ⟨2254857, by rfl⟩ : syracuseStep 6012953 = 4509715) B4509715
theorem B1884455 : Blo 658307 1884455 := bstep (se 1 (by rfl) ⟨1413341, by rfl⟩ : syracuseStep 1884455 = 2826683) B2826683
theorem B14434735 : Blo 658307 14434735 := bstep (se 1 (by rfl) ⟨10826051, by rfl⟩ : syracuseStep 14434735 = 21652103) B21652103
theorem B4015295 : Blo 658307 4015295 := bstep (se 1 (by rfl) ⟨3011471, by rfl⟩ : syracuseStep 4015295 = 6022943) B6022943
theorem B836831 : Blo 658307 836831 := bstep (se 1 (by rfl) ⟨627623, by rfl⟩ : syracuseStep 836831 = 1255247) B1255247
theorem B2114795 : Blo 658307 2114795 := bstep (se 1 (by rfl) ⟨1586096, by rfl⟩ : syracuseStep 2114795 = 3172193) B3172193
theorem B4277927 : Blo 658307 4277927 := bstep (se 1 (by rfl) ⟨3208445, by rfl⟩ : syracuseStep 4277927 = 6416891) B6416891
theorem B3753985 : Blo 658307 3753985 := bstep (se 2 (by rfl) ⟨1407744, by rfl⟩ : syracuseStep 3753985 = 2815489) B2815489
theorem B4999481 : Blo 658307 4999481 := bstep (se 2 (by rfl) ⟨1874805, by rfl⟩ : syracuseStep 4999481 = 3749611) B3749611
theorem B2509339 : Blo 658307 2509339 := bstep (se 1 (by rfl) ⟨1882004, by rfl⟩ : syracuseStep 2509339 = 3764009) B3764009
theorem B8440523 : Blo 658307 8440523 := bstep (se 1 (by rfl) ⟨6330392, by rfl⟩ : syracuseStep 8440523 = 12660785) B12660785
theorem B10144763 : Blo 658307 10144763 := bstep (se 1 (by rfl) ⟨7608572, by rfl⟩ : syracuseStep 10144763 = 15217145) B15217145
theorem B3394703 : Blo 658307 3394703 := bstep (se 1 (by rfl) ⟨2546027, by rfl⟩ : syracuseStep 3394703 = 5092055) B5092055
theorem B16076555 : Blo 658307 16076555 := bstep (se 1 (by rfl) ⟨12057416, by rfl⟩ : syracuseStep 16076555 = 24114833) B24114833
theorem B1789885 : Blo 658307 1789885 := bstep (se 3 (by rfl) ⟨335603, by rfl⟩ : syracuseStep 1789885 = 671207) B671207
theorem B5001425 : Blo 658307 5001425 := bstep (se 2 (by rfl) ⟨1875534, by rfl⟩ : syracuseStep 5001425 = 3751069) B3751069
theorem B3166427 : Blo 658307 3166427 := bstep (se 1 (by rfl) ⟨2374820, by rfl⟩ : syracuseStep 3166427 = 4749641) B4749641
theorem B8474867 : Blo 658307 8474867 := bstep (se 1 (by rfl) ⟨6356150, by rfl⟩ : syracuseStep 8474867 = 12712301) B12712301
theorem B2675111 : Blo 658307 2675111 := bstep (se 1 (by rfl) ⟨2006333, by rfl⟩ : syracuseStep 2675111 = 4012667) B4012667
theorem B3166735 : Blo 658307 3166735 := bstep (se 1 (by rfl) ⟨2375051, by rfl⟩ : syracuseStep 3166735 = 4750103) B4750103
theorem B938633 : Blo 658307 938633 := bstep (se 2 (by rfl) ⟨351987, by rfl⟩ : syracuseStep 938633 = 703975) B703975
theorem B742207 : Blo 658307 742207 := bstep (se 1 (by rfl) ⟨556655, by rfl⟩ : syracuseStep 742207 = 1113311) B1113311
theorem B742495 : Blo 658307 742495 := bstep (se 1 (by rfl) ⟨556871, by rfl⟩ : syracuseStep 742495 = 1113743) B1113743
theorem B3823037 : Blo 658307 3823037 := bstep (se 3 (by rfl) ⟨716819, by rfl⟩ : syracuseStep 3823037 = 1433639) B1433639
theorem B2119613 : Blo 658307 2119613 := bstep (se 3 (by rfl) ⟨397427, by rfl⟩ : syracuseStep 2119613 = 794855) B794855
theorem B2676833 : Blo 658307 2676833 := bstep (se 2 (by rfl) ⟨1003812, by rfl⟩ : syracuseStep 2676833 = 2007625) B2007625
theorem B5626331 : Blo 658307 5626331 := bstep (se 1 (by rfl) ⟨4219748, by rfl⟩ : syracuseStep 5626331 = 8439497) B8439497
theorem B5003855 : Blo 658307 5003855 := bstep (se 1 (by rfl) ⟨3752891, by rfl⟩ : syracuseStep 5003855 = 7505783) B7505783
theorem B6773345 : Blo 658307 6773345 := bstep (se 2 (by rfl) ⟨2540004, by rfl⟩ : syracuseStep 6773345 = 5080009) B5080009
theorem B2514017 : Blo 658307 2514017 := bstep (se 2 (by rfl) ⟨942756, by rfl⟩ : syracuseStep 2514017 = 1885513) B1885513
theorem B744655 : Blo 658307 744655 := bstep (se 1 (by rfl) ⟨558491, by rfl⟩ : syracuseStep 744655 = 1116983) B1116983
theorem B2121383 : Blo 658307 2121383 := bstep (se 1 (by rfl) ⟨1591037, by rfl⟩ : syracuseStep 2121383 = 3182075) B3182075
theorem B1335059 : Blo 658307 1335059 := bstep (se 1 (by rfl) ⟨1001294, by rfl⟩ : syracuseStep 1335059 = 2002589) B2002589
theorem B2678615 : Blo 658307 2678615 := bstep (se 1 (by rfl) ⟨2008961, by rfl⟩ : syracuseStep 2678615 = 4017923) B4017923
theorem B1204079 : Blo 658307 1204079 := bstep (se 1 (by rfl) ⟨903059, by rfl⟩ : syracuseStep 1204079 = 1806119) B1806119
theorem B57041333 : Blo 658307 57041333 := bstep (se 5 (by rfl) ⟨2673812, by rfl⟩ : syracuseStep 57041333 = 5347625) B5347625
theorem B3007003 : Blo 658307 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B10740539 : Blo 658307 10740539 := bstep (se 1 (by rfl) ⟨8055404, by rfl⟩ : syracuseStep 10740539 = 16110809) B16110809
theorem B2384969 : Blo 658307 2384969 := bstep (se 2 (by rfl) ⟨894363, by rfl⟩ : syracuseStep 2384969 = 1788727) B1788727
theorem B4515347 : Blo 658307 4515347 := bstep (se 1 (by rfl) ⟨3386510, by rfl⟩ : syracuseStep 4515347 = 6773021) B6773021
theorem B11462311 : Blo 658307 11462311 := bstep (se 1 (by rfl) ⟨8596733, by rfl⟩ : syracuseStep 11462311 = 17193467) B17193467
theorem B3565259 : Blo 658307 3565259 := bstep (se 1 (by rfl) ⟨2673944, by rfl⟩ : syracuseStep 3565259 = 5347889) B5347889
theorem B18606167 : Blo 658307 18606167 := bstep (se 1 (by rfl) ⟨13954625, by rfl⟩ : syracuseStep 18606167 = 27909251) B27909251
theorem B3565691 : Blo 658307 3565691 := bstep (se 1 (by rfl) ⟨2674268, by rfl⟩ : syracuseStep 3565691 = 5348537) B5348537
theorem B2222639 : Blo 658307 2222639 := bstep (se 1 (by rfl) ⟨1666979, by rfl⟩ : syracuseStep 2222639 = 3333959) B3333959
theorem B5237797 : Blo 658307 5237797 := bstep (se 4 (by rfl) ⟨491043, by rfl⟩ : syracuseStep 5237797 = 982087) B982087
theorem B2223287 : Blo 658307 2223287 := bstep (se 1 (by rfl) ⟨1667465, by rfl⟩ : syracuseStep 2223287 = 3334931) B3334931
theorem B5729773 : Blo 658307 5729773 := bstep (se 3 (by rfl) ⟨1074332, by rfl⟩ : syracuseStep 5729773 = 2148665) B2148665
theorem B8482553 : Blo 658307 8482553 := bstep (se 2 (by rfl) ⟨3180957, by rfl⟩ : syracuseStep 8482553 = 6361915) B6361915
theorem B25391069 : Blo 658307 25391069 := bstep (se 3 (by rfl) ⟨4760825, by rfl⟩ : syracuseStep 25391069 = 9521651) B9521651
theorem B10678391 : Blo 658307 10678391 := bstep (se 1 (by rfl) ⟨8008793, by rfl⟩ : syracuseStep 10678391 = 16017587) B16017587
theorem B5009687 : Blo 658307 5009687 := bstep (se 1 (by rfl) ⟨3757265, by rfl⟩ : syracuseStep 5009687 = 7514531) B7514531
theorem B12710297 : Blo 658307 12710297 := bstep (se 2 (by rfl) ⟨4766361, by rfl⟩ : syracuseStep 12710297 = 9532723) B9532723
theorem B12055223 : Blo 658307 12055223 := bstep (se 1 (by rfl) ⟨9041417, by rfl⟩ : syracuseStep 12055223 = 18082835) B18082835
theorem B12710843 : Blo 658307 12710843 := bstep (se 1 (by rfl) ⟨9533132, by rfl⟩ : syracuseStep 12710843 = 19066265) B19066265
theorem B1406575 : Blo 658307 1406575 := bstep (se 1 (by rfl) ⟨1054931, by rfl⟩ : syracuseStep 1406575 = 2109863) B2109863
theorem B1668833 : Blo 658307 1668833 := bstep (se 2 (by rfl) ⟨625812, by rfl⟩ : syracuseStep 1668833 = 1251625) B1251625
theorem B12678929 : Blo 658307 12678929 := bstep (se 2 (by rfl) ⟨4754598, by rfl⟩ : syracuseStep 12678929 = 9509197) B9509197
theorem B1406891 : Blo 658307 1406891 := bstep (se 1 (by rfl) ⟨1055168, by rfl⟩ : syracuseStep 1406891 = 2110337) B2110337
theorem B2062547 : Blo 658307 2062547 := bstep (se 1 (by rfl) ⟨1546910, by rfl⟩ : syracuseStep 2062547 = 3093821) B3093821
theorem B751847 : Blo 658307 751847 := bstep (se 1 (by rfl) ⟨563885, by rfl⟩ : syracuseStep 751847 = 1127771) B1127771
theorem B3340763 : Blo 658307 3340763 := bstep (se 1 (by rfl) ⟨2505572, by rfl⟩ : syracuseStep 3340763 = 5011145) B5011145
theorem B1669673 : Blo 658307 1669673 := bstep (se 2 (by rfl) ⟨626127, by rfl⟩ : syracuseStep 1669673 = 1252255) B1252255
theorem B1112879 : Blo 658307 1112879 := bstep (se 1 (by rfl) ⟨834659, by rfl⟩ : syracuseStep 1112879 = 1669319) B1669319
theorem B1408223 : Blo 658307 1408223 := bstep (se 1 (by rfl) ⟨1056167, by rfl⟩ : syracuseStep 1408223 = 2112335) B2112335
theorem B1408531 : Blo 658307 1408531 := bstep (se 1 (by rfl) ⟨1056398, by rfl⟩ : syracuseStep 1408531 = 2112797) B2112797
theorem B2227823 : Blo 658307 2227823 := bstep (se 1 (by rfl) ⟨1670867, by rfl⟩ : syracuseStep 2227823 = 3341735) B3341735
theorem B2817935 : Blo 658307 2817935 := bstep (se 1 (by rfl) ⟨2113451, by rfl⟩ : syracuseStep 2817935 = 4226903) B4226903
theorem B1671961 : Blo 658307 1671961 := bstep (se 2 (by rfl) ⟨626985, by rfl⟩ : syracuseStep 1671961 = 1253971) B1253971
theorem B1672073 : Blo 658307 1672073 := bstep (se 2 (by rfl) ⟨627027, by rfl⟩ : syracuseStep 1672073 = 1254055) B1254055
theorem B2229227 : Blo 658307 2229227 := bstep (se 1 (by rfl) ⟨1671920, by rfl⟩ : syracuseStep 2229227 = 3343841) B3343841
theorem B3343355 : Blo 658307 3343355 := bstep (se 1 (by rfl) ⟨2507516, by rfl⟩ : syracuseStep 3343355 = 5015033) B5015033
theorem B1672265 : Blo 658307 1672265 := bstep (se 2 (by rfl) ⟨627099, by rfl⟩ : syracuseStep 1672265 = 1254199) B1254199
theorem B2851951 : Blo 658307 2851951 := bstep (se 1 (by rfl) ⟨2138963, by rfl⟩ : syracuseStep 2851951 = 4277927) B4277927
theorem B2851969 : Blo 658307 2851969 := bstep (se 2 (by rfl) ⟨1069488, by rfl⟩ : syracuseStep 2851969 = 2138977) B2138977
theorem B2263135 : Blo 658307 2263135 := bstep (se 1 (by rfl) ⟨1697351, by rfl⟩ : syracuseStep 2263135 = 3394703) B3394703
theorem B10717703 : Blo 658307 10717703 := bstep (se 1 (by rfl) ⟨8038277, by rfl⟩ : syracuseStep 10717703 = 16076555) B16076555
theorem B6359917 : Blo 658307 6359917 := bstep (se 3 (by rfl) ⟨1192484, by rfl⟩ : syracuseStep 6359917 = 2384969) B2384969
theorem B658343 : Blo 658307 658343 := bstep (se 1 (by rfl) ⟨493757, by rfl⟩ : syracuseStep 658343 = 987515) B987515
theorem B1674209 : Blo 658307 1674209 := bstep (se 2 (by rfl) ⟨627828, by rfl⟩ : syracuseStep 1674209 = 1255657) B1255657
theorem B3771481 : Blo 658307 3771481 := bstep (se 2 (by rfl) ⟨1414305, by rfl⟩ : syracuseStep 3771481 = 2828611) B2828611
theorem B658523 : Blo 658307 658523 := bstep (se 1 (by rfl) ⟨493892, by rfl⟩ : syracuseStep 658523 = 987785) B987785
theorem B3345623 : Blo 658307 3345623 := bstep (se 1 (by rfl) ⟨2509217, by rfl⟩ : syracuseStep 3345623 = 5018435) B5018435
theorem B658663 : Blo 658307 658663 := bstep (se 1 (by rfl) ⟨493997, by rfl⟩ : syracuseStep 658663 = 987995) B987995
theorem B2231549 : Blo 658307 2231549 := bstep (se 3 (by rfl) ⟨418415, by rfl⟩ : syracuseStep 2231549 = 836831) B836831
theorem B5639453 : Blo 658307 5639453 := bstep (se 3 (by rfl) ⟨1057397, by rfl⟩ : syracuseStep 5639453 = 2114795) B2114795
theorem B1674553 : Blo 658307 1674553 := bstep (se 2 (by rfl) ⟨627957, by rfl⟩ : syracuseStep 1674553 = 1255915) B1255915
theorem B3345785 : Blo 658307 3345785 := bstep (se 2 (by rfl) ⟨1254669, by rfl⟩ : syracuseStep 3345785 = 2509339) B2509339
theorem B658971 : Blo 658307 658971 := bstep (se 1 (by rfl) ⟨494228, by rfl⟩ : syracuseStep 658971 = 988457) B988457
theorem B3345947 : Blo 658307 3345947 := bstep (se 1 (by rfl) ⟨2509460, by rfl⟩ : syracuseStep 3345947 = 5018921) B5018921
theorem B659103 : Blo 658307 659103 := bstep (se 1 (by rfl) ⟨494327, by rfl⟩ : syracuseStep 659103 = 988655) B988655
theorem B2232089 : Blo 658307 2232089 := bstep (se 2 (by rfl) ⟨837033, by rfl⟩ : syracuseStep 2232089 = 1674067) B1674067
theorem B659367 : Blo 658307 659367 := bstep (se 1 (by rfl) ⟨494525, by rfl⟩ : syracuseStep 659367 = 989051) B989051
theorem B659391 : Blo 658307 659391 := bstep (se 1 (by rfl) ⟨494543, by rfl⟩ : syracuseStep 659391 = 989087) B989087
theorem B7540775 : Blo 658307 7540775 := bstep (se 1 (by rfl) ⟨5655581, by rfl⟩ : syracuseStep 7540775 = 11311163) B11311163
theorem B6983729 : Blo 658307 6983729 := bstep (se 2 (by rfl) ⟨2618898, by rfl⟩ : syracuseStep 6983729 = 5237797) B5237797
theorem B659547 : Blo 658307 659547 := bstep (se 1 (by rfl) ⟨494660, by rfl⟩ : syracuseStep 659547 = 989321) B989321
theorem B659647 : Blo 658307 659647 := bstep (se 1 (by rfl) ⟨494735, by rfl⟩ : syracuseStep 659647 = 989471) B989471
theorem B6033599 : Blo 658307 6033599 := bstep (se 1 (by rfl) ⟨4525199, by rfl⟩ : syracuseStep 6033599 = 9050399) B9050399
theorem B987695 : Blo 658307 987695 := bstep (se 1 (by rfl) ⟨740771, by rfl⟩ : syracuseStep 987695 = 1481543) B1481543
theorem B660015 : Blo 658307 660015 := bstep (se 1 (by rfl) ⟨495011, by rfl⟩ : syracuseStep 660015 = 990023) B990023
theorem B7639697 : Blo 658307 7639697 := bstep (se 2 (by rfl) ⟨2864886, by rfl⟩ : syracuseStep 7639697 = 5729773) B5729773
theorem B1676011 : Blo 658307 1676011 := bstep (se 1 (by rfl) ⟨1257008, by rfl⟩ : syracuseStep 1676011 = 2514017) B2514017
theorem B987899 : Blo 658307 987899 := bstep (se 1 (by rfl) ⟨740924, by rfl⟩ : syracuseStep 987899 = 1481849) B1481849
theorem B988271 : Blo 658307 988271 := bstep (se 1 (by rfl) ⟨741203, by rfl⟩ : syracuseStep 988271 = 1482407) B1482407
theorem B660591 : Blo 658307 660591 := bstep (se 1 (by rfl) ⟨495443, by rfl⟩ : syracuseStep 660591 = 990887) B990887
theorem B1414255 : Blo 658307 1414255 := bstep (se 1 (by rfl) ⟨1060691, by rfl⟩ : syracuseStep 1414255 = 2121383) B2121383
theorem B890039 : Blo 658307 890039 := bstep (se 1 (by rfl) ⟨667529, by rfl⟩ : syracuseStep 890039 = 1335059) B1335059
theorem B988343 : Blo 658307 988343 := bstep (se 1 (by rfl) ⟨741257, by rfl⟩ : syracuseStep 988343 = 1482515) B1482515
theorem B660671 : Blo 658307 660671 := bstep (se 1 (by rfl) ⟨495503, by rfl⟩ : syracuseStep 660671 = 991007) B991007
theorem B988583 : Blo 658307 988583 := bstep (se 1 (by rfl) ⟨741437, by rfl⟩ : syracuseStep 988583 = 1482875) B1482875
theorem B660959 : Blo 658307 660959 := bstep (se 1 (by rfl) ⟨495719, by rfl⟩ : syracuseStep 660959 = 991439) B991439
theorem B660991 : Blo 658307 660991 := bstep (se 1 (by rfl) ⟨495743, by rfl⟩ : syracuseStep 660991 = 991487) B991487
theorem B988763 : Blo 658307 988763 := bstep (se 1 (by rfl) ⟨741572, by rfl⟩ : syracuseStep 988763 = 1483145) B1483145
theorem B2004925 : Blo 658307 2004925 := bstep (se 3 (by rfl) ⟨375923, by rfl⟩ : syracuseStep 2004925 = 751847) B751847
theorem B1251359 : Blo 658307 1251359 := bstep (se 1 (by rfl) ⟨938519, by rfl⟩ : syracuseStep 1251359 = 1877039) B1877039
theorem B792607 : Blo 658307 792607 := bstep (se 1 (by rfl) ⟨594455, by rfl⟩ : syracuseStep 792607 = 1188911) B1188911
theorem B661535 : Blo 658307 661535 := bstep (se 1 (by rfl) ⟨496151, by rfl⟩ : syracuseStep 661535 = 992303) B992303
theorem B3348539 : Blo 658307 3348539 := bstep (se 1 (by rfl) ⟨2511404, by rfl⟩ : syracuseStep 3348539 = 5022809) B5022809
theorem B661615 : Blo 658307 661615 := bstep (se 1 (by rfl) ⟨496211, by rfl⟩ : syracuseStep 661615 = 992423) B992423
theorem B989519 : Blo 658307 989519 := bstep (se 1 (by rfl) ⟨742139, by rfl⟩ : syracuseStep 989519 = 1484279) B1484279
theorem B989543 : Blo 658307 989543 := bstep (se 1 (by rfl) ⟨742157, by rfl⟩ : syracuseStep 989543 = 1484315) B1484315
theorem B661863 : Blo 658307 661863 := bstep (se 1 (by rfl) ⟨496397, by rfl⟩ : syracuseStep 661863 = 992795) B992795
theorem B989609 : Blo 658307 989609 := bstep (se 2 (by rfl) ⟨371103, by rfl⟩ : syracuseStep 989609 = 742207) B742207
theorem B662119 : Blo 658307 662119 := bstep (se 1 (by rfl) ⟨496589, by rfl⟩ : syracuseStep 662119 = 993179) B993179
theorem B662143 : Blo 658307 662143 := bstep (se 1 (by rfl) ⟨496607, by rfl⟩ : syracuseStep 662143 = 993215) B993215
theorem B662267 : Blo 658307 662267 := bstep (se 1 (by rfl) ⟨496700, by rfl⟩ : syracuseStep 662267 = 993401) B993401
theorem B989993 : Blo 658307 989993 := bstep (se 2 (by rfl) ⟨371247, by rfl⟩ : syracuseStep 989993 = 742495) B742495
theorem B990203 : Blo 658307 990203 := bstep (se 1 (by rfl) ⟨742652, by rfl⟩ : syracuseStep 990203 = 1485305) B1485305
theorem B1481759 : Blo 658307 1481759 := bstep (se 1 (by rfl) ⟨1111319, by rfl⟩ : syracuseStep 1481759 = 2222639) B2222639
theorem B990239 : Blo 658307 990239 := bstep (se 1 (by rfl) ⟨742679, by rfl⟩ : syracuseStep 990239 = 1485359) B1485359
theorem B990263 : Blo 658307 990263 := bstep (se 1 (by rfl) ⟨742697, by rfl⟩ : syracuseStep 990263 = 1485395) B1485395
theorem B990383 : Blo 658307 990383 := bstep (se 1 (by rfl) ⟨742787, by rfl⟩ : syracuseStep 990383 = 1485575) B1485575
theorem B990527 : Blo 658307 990527 := bstep (se 1 (by rfl) ⟨742895, by rfl⟩ : syracuseStep 990527 = 1485791) B1485791
theorem B1482191 : Blo 658307 1482191 := bstep (se 1 (by rfl) ⟨1111643, by rfl⟩ : syracuseStep 1482191 = 2223287) B2223287
theorem B990671 : Blo 658307 990671 := bstep (se 1 (by rfl) ⟨743003, by rfl⟩ : syracuseStep 990671 = 1486007) B1486007
theorem B1875433 : Blo 658307 1875433 := bstep (se 2 (by rfl) ⟨703287, by rfl⟩ : syracuseStep 1875433 = 1406575) B1406575
theorem B1875581 : Blo 658307 1875581 := bstep (se 3 (by rfl) ⟨351671, by rfl⟩ : syracuseStep 1875581 = 703343) B703343
theorem B3350159 : Blo 658307 3350159 := bstep (se 1 (by rfl) ⟨2512619, by rfl⟩ : syracuseStep 3350159 = 5025239) B5025239
theorem B991055 : Blo 658307 991055 := bstep (se 1 (by rfl) ⟨743291, by rfl⟩ : syracuseStep 991055 = 1486583) B1486583
theorem B991103 : Blo 658307 991103 := bstep (se 1 (by rfl) ⟨743327, by rfl⟩ : syracuseStep 991103 = 1486655) B1486655
theorem B991175 : Blo 658307 991175 := bstep (se 1 (by rfl) ⟨743381, by rfl⟩ : syracuseStep 991175 = 1486763) B1486763
theorem B7118927 : Blo 658307 7118927 := bstep (se 1 (by rfl) ⟨5339195, by rfl⟩ : syracuseStep 7118927 = 10678391) B10678391
theorem B991415 : Blo 658307 991415 := bstep (se 1 (by rfl) ⟨743561, by rfl⟩ : syracuseStep 991415 = 1487123) B1487123
theorem B991535 : Blo 658307 991535 := bstep (se 1 (by rfl) ⟨743651, by rfl⟩ : syracuseStep 991535 = 1487303) B1487303
theorem B8036815 : Blo 658307 8036815 := bstep (se 1 (by rfl) ⟨6027611, by rfl⟩ : syracuseStep 8036815 = 12055223) B12055223
theorem B10691099 : Blo 658307 10691099 := bstep (se 1 (by rfl) ⟨8018324, by rfl⟩ : syracuseStep 10691099 = 16036649) B16036649
theorem B991775 : Blo 658307 991775 := bstep (se 1 (by rfl) ⟨743831, by rfl⟩ : syracuseStep 991775 = 1487663) B1487663
theorem B1057321 : Blo 658307 1057321 := bstep (se 2 (by rfl) ⟨396495, by rfl⟩ : syracuseStep 1057321 = 792991) B792991
theorem B991835 : Blo 658307 991835 := bstep (se 1 (by rfl) ⟨743876, by rfl⟩ : syracuseStep 991835 = 1487753) B1487753
theorem B24454187 : Blo 658307 24454187 := bstep (se 1 (by rfl) ⟨18340640, by rfl⟩ : syracuseStep 24454187 = 36681281) B36681281
theorem B992351 : Blo 658307 992351 := bstep (se 1 (by rfl) ⟨744263, by rfl⟩ : syracuseStep 992351 = 1488527) B1488527
theorem B992411 : Blo 658307 992411 := bstep (se 1 (by rfl) ⟨744308, by rfl⟩ : syracuseStep 992411 = 1488617) B1488617
theorem B992873 : Blo 658307 992873 := bstep (se 2 (by rfl) ⟨372327, by rfl⟩ : syracuseStep 992873 = 744655) B744655
theorem B992999 : Blo 658307 992999 := bstep (se 1 (by rfl) ⟨744749, by rfl⟩ : syracuseStep 992999 = 1489499) B1489499
theorem B993095 : Blo 658307 993095 := bstep (se 1 (by rfl) ⟨744821, by rfl⟩ : syracuseStep 993095 = 1489643) B1489643
theorem B1878041 : Blo 658307 1878041 := bstep (se 2 (by rfl) ⟨704265, by rfl⟩ : syracuseStep 1878041 = 1408531) B1408531
theorem B1255763 : Blo 658307 1255763 := bstep (se 1 (by rfl) ⟨941822, by rfl⟩ : syracuseStep 1255763 = 1883645) B1883645
theorem B1485215 : Blo 658307 1485215 := bstep (se 1 (by rfl) ⟨1113911, by rfl⟩ : syracuseStep 1485215 = 2227823) B2227823
theorem B1878623 : Blo 658307 1878623 := bstep (se 1 (by rfl) ⟨1408967, by rfl⟩ : syracuseStep 1878623 = 2817935) B2817935
theorem B4008635 : Blo 658307 4008635 := bstep (se 1 (by rfl) ⟨3006476, by rfl⟩ : syracuseStep 4008635 = 6012953) B6012953
theorem B1256303 : Blo 658307 1256303 := bstep (se 1 (by rfl) ⟨942227, by rfl⟩ : syracuseStep 1256303 = 1884455) B1884455
theorem B1485737 : Blo 658307 1485737 := bstep (se 2 (by rfl) ⟨557151, by rfl⟩ : syracuseStep 1485737 = 1114303) B1114303
theorem B19246313 : Blo 658307 19246313 := bstep (se 2 (by rfl) ⟨7217367, by rfl⟩ : syracuseStep 19246313 = 14434735) B14434735
theorem B18984253 : Blo 658307 18984253 := bstep (se 3 (by rfl) ⟨3559547, by rfl⟩ : syracuseStep 18984253 = 7119095) B7119095
theorem B36547949 : Blo 658307 36547949 := bstep (se 3 (by rfl) ⟨6852740, by rfl⟩ : syracuseStep 36547949 = 13705481) B13705481
theorem B4009337 : Blo 658307 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B1060217 : Blo 658307 1060217 := bstep (se 2 (by rfl) ⟨397581, by rfl⟩ : syracuseStep 1060217 = 795163) B795163
theorem B1486313 : Blo 658307 1486313 := bstep (se 2 (by rfl) ⟨557367, by rfl⟩ : syracuseStep 1486313 = 1114735) B1114735
theorem B1486367 : Blo 658307 1486367 := bstep (se 1 (by rfl) ⟨1114775, by rfl⟩ : syracuseStep 1486367 = 2229551) B2229551
theorem B5648201 : Blo 658307 5648201 := bstep (se 2 (by rfl) ⟨2118075, by rfl⟩ : syracuseStep 5648201 = 4236151) B4236151
theorem B1880297 : Blo 658307 1880297 := bstep (se 2 (by rfl) ⟨705111, by rfl⟩ : syracuseStep 1880297 = 1410223) B1410223
theorem B16953623 : Blo 658307 16953623 := bstep (se 1 (by rfl) ⟨12715217, by rfl⟩ : syracuseStep 16953623 = 25430435) B25430435
theorem B2503021 : Blo 658307 2503021 := bstep (se 3 (by rfl) ⟨469316, by rfl⟩ : syracuseStep 2503021 = 938633) B938633
theorem B6763175 : Blo 658307 6763175 := bstep (se 1 (by rfl) ⟨5072381, by rfl⟩ : syracuseStep 6763175 = 10144763) B10144763
theorem B15283081 : Blo 658307 15283081 := bstep (se 2 (by rfl) ⟨5731155, by rfl⟩ : syracuseStep 15283081 = 11462311) B11462311
theorem B2110951 : Blo 658307 2110951 := bstep (se 1 (by rfl) ⟨1583213, by rfl⟩ : syracuseStep 2110951 = 3166427) B3166427
theorem B5649911 : Blo 658307 5649911 := bstep (se 1 (by rfl) ⟨4237433, by rfl⟩ : syracuseStep 5649911 = 8474867) B8474867
theorem B1882415 : Blo 658307 1882415 := bstep (se 1 (by rfl) ⟨1411811, by rfl⟩ : syracuseStep 1882415 = 2823623) B2823623
theorem B1489463 : Blo 658307 1489463 := bstep (se 1 (by rfl) ⟨1117097, by rfl⟩ : syracuseStep 1489463 = 2234195) B2234195
theorem B1784555 : Blo 658307 1784555 := bstep (se 1 (by rfl) ⟨1338416, by rfl⟩ : syracuseStep 1784555 = 2676833) B2676833
theorem B3750887 : Blo 658307 3750887 := bstep (se 1 (by rfl) ⟨2813165, by rfl⟩ : syracuseStep 3750887 = 5626331) B5626331
theorem B834887 : Blo 658307 834887 := bstep (se 1 (by rfl) ⟨626165, by rfl⟩ : syracuseStep 834887 = 1252331) B1252331
theorem B835039 : Blo 658307 835039 := bstep (se 1 (by rfl) ⟨626279, by rfl⟩ : syracuseStep 835039 = 1252559) B1252559
theorem B5652301 : Blo 658307 5652301 := bstep (se 3 (by rfl) ⟨1059806, by rfl⟩ : syracuseStep 5652301 = 2119613) B2119613
theorem B1785743 : Blo 658307 1785743 := bstep (se 1 (by rfl) ⟨1339307, by rfl⟩ : syracuseStep 1785743 = 2678615) B2678615
theorem B38027555 : Blo 658307 38027555 := bstep (se 1 (by rfl) ⟨28520666, by rfl⟩ : syracuseStep 38027555 = 57041333) B57041333
theorem B1884647 : Blo 658307 1884647 := bstep (se 1 (by rfl) ⟨1413485, by rfl⟩ : syracuseStep 1884647 = 2826971) B2826971
theorem B7160359 : Blo 658307 7160359 := bstep (se 1 (by rfl) ⟨5370269, by rfl⟩ : syracuseStep 7160359 = 10740539) B10740539
theorem B2376839 : Blo 658307 2376839 := bstep (se 1 (by rfl) ⟨1782629, by rfl⟩ : syracuseStep 2376839 = 3565259) B3565259
theorem B2376985 : Blo 658307 2376985 := bstep (se 2 (by rfl) ⟨891369, by rfl⟩ : syracuseStep 2376985 = 1782739) B1782739
theorem B12404111 : Blo 658307 12404111 := bstep (se 1 (by rfl) ⟨9303083, by rfl⟩ : syracuseStep 12404111 = 18606167) B18606167
theorem B2377127 : Blo 658307 2377127 := bstep (se 1 (by rfl) ⟨1782845, by rfl⟩ : syracuseStep 2377127 = 3565691) B3565691
theorem B837211 : Blo 658307 837211 := bstep (se 1 (by rfl) ⟨627908, by rfl⟩ : syracuseStep 837211 = 1255817) B1255817
theorem B5655035 : Blo 658307 5655035 := bstep (se 1 (by rfl) ⟨4241276, by rfl⟩ : syracuseStep 5655035 = 8482553) B8482553
theorem B16927379 : Blo 658307 16927379 := bstep (se 1 (by rfl) ⟨12695534, by rfl⟩ : syracuseStep 16927379 = 25391069) B25391069
theorem B3853175 : Blo 658307 3853175 := bstep (se 1 (by rfl) ⟨2889881, by rfl⟩ : syracuseStep 3853175 = 5779763) B5779763
theorem B8473531 : Blo 658307 8473531 := bstep (se 1 (by rfl) ⟨6355148, by rfl⟩ : syracuseStep 8473531 = 12710297) B12710297
theorem B3755261 : Blo 658307 3755261 := bstep (se 3 (by rfl) ⟨704111, by rfl⟩ : syracuseStep 3755261 = 1408223) B1408223
theorem B8473895 : Blo 658307 8473895 := bstep (se 1 (by rfl) ⟨6355421, by rfl⟩ : syracuseStep 8473895 = 12710843) B12710843
theorem B937927 : Blo 658307 937927 := bstep (se 1 (by rfl) ⟨703445, by rfl⟩ : syracuseStep 937927 = 1406891) B1406891
theorem B51433865 : Blo 658307 51433865 := bstep (se 2 (by rfl) ⟨19287699, by rfl⟩ : syracuseStep 51433865 = 38575399) B38575399
theorem B741919 : Blo 658307 741919 := bstep (se 1 (by rfl) ⟨556439, by rfl⟩ : syracuseStep 741919 = 1112879) B1112879
theorem B4641419 : Blo 658307 4641419 := bstep (se 1 (by rfl) ⟨3481064, by rfl⟩ : syracuseStep 4641419 = 6962129) B6962129
theorem B24040097 : Blo 658307 24040097 := bstep (se 2 (by rfl) ⟨9015036, by rfl⟩ : syracuseStep 24040097 = 18030073) B18030073
theorem B8443187 : Blo 658307 8443187 := bstep (se 1 (by rfl) ⟨6332390, by rfl⟩ : syracuseStep 8443187 = 12664781) B12664781
theorem B2676023 : Blo 658307 2676023 := bstep (se 1 (by rfl) ⟨2007017, by rfl⟩ : syracuseStep 2676023 = 4014035) B4014035
theorem B19355041 : Blo 658307 19355041 := bstep (se 2 (by rfl) ⟨7258140, by rfl⟩ : syracuseStep 19355041 = 14516281) B14516281
theorem B3758177 : Blo 658307 3758177 := bstep (se 2 (by rfl) ⟨1409316, by rfl⟩ : syracuseStep 3758177 = 2818633) B2818633
theorem B2676863 : Blo 658307 2676863 := bstep (se 1 (by rfl) ⟨2007647, by rfl⟩ : syracuseStep 2676863 = 4015295) B4015295
theorem B2119871 : Blo 658307 2119871 := bstep (se 1 (by rfl) ⟨1589903, by rfl⟩ : syracuseStep 2119871 = 3179807) B3179807
theorem B743647 : Blo 658307 743647 := bstep (se 1 (by rfl) ⟨557735, by rfl⟩ : syracuseStep 743647 = 1115471) B1115471
theorem B7133629 : Blo 658307 7133629 := bstep (se 3 (by rfl) ⟨1337555, by rfl⟩ : syracuseStep 7133629 = 2675111) B2675111
theorem B744295 : Blo 658307 744295 := bstep (se 1 (by rfl) ⟨558221, by rfl⟩ : syracuseStep 744295 = 1116443) B1116443
theorem B3332987 : Blo 658307 3332987 := bstep (se 1 (by rfl) ⟨2499740, by rfl⟩ : syracuseStep 3332987 = 4999481) B4999481
theorem B744511 : Blo 658307 744511 := bstep (se 1 (by rfl) ⟨558383, by rfl⟩ : syracuseStep 744511 = 1116767) B1116767
theorem B5627015 : Blo 658307 5627015 := bstep (se 1 (by rfl) ⟨4220261, by rfl⟩ : syracuseStep 5627015 = 8440523) B8440523
theorem B6348041 : Blo 658307 6348041 := bstep (se 2 (by rfl) ⟨2380515, by rfl⟩ : syracuseStep 6348041 = 4761031) B4761031
theorem B5005313 : Blo 658307 5005313 := bstep (se 2 (by rfl) ⟨1876992, by rfl⟩ : syracuseStep 5005313 = 3753985) B3753985
theorem B942187 : Blo 658307 942187 := bstep (se 1 (by rfl) ⟨706640, by rfl⟩ : syracuseStep 942187 = 1413281) B1413281
theorem B3334283 : Blo 658307 3334283 := bstep (se 1 (by rfl) ⟨2500712, by rfl⟩ : syracuseStep 3334283 = 5001425) B5001425
theorem B3760343 : Blo 658307 3760343 := bstep (se 1 (by rfl) ⟨2820257, by rfl⟩ : syracuseStep 3760343 = 5640515) B5640515
theorem B10838681 : Blo 658307 10838681 := bstep (se 2 (by rfl) ⟨4064505, by rfl⟩ : syracuseStep 10838681 = 8129011) B8129011
theorem B943007 : Blo 658307 943007 := bstep (se 1 (by rfl) ⟨707255, by rfl⟩ : syracuseStep 943007 = 1414511) B1414511
theorem B2548691 : Blo 658307 2548691 := bstep (se 1 (by rfl) ⟨1911518, by rfl⟩ : syracuseStep 2548691 = 3823037) B3823037
theorem B3171311 : Blo 658307 3171311 := bstep (se 1 (by rfl) ⟨2378483, by rfl⟩ : syracuseStep 3171311 = 4756967) B4756967
theorem B178120349 : Blo 658307 178120349 := bstep (se 3 (by rfl) ⟨33397565, by rfl⟩ : syracuseStep 178120349 = 66795131) B66795131
theorem B3335903 : Blo 658307 3335903 := bstep (se 1 (by rfl) ⟨2501927, by rfl⟩ : syracuseStep 3335903 = 5003855) B5003855
theorem B4515563 : Blo 658307 4515563 := bstep (se 1 (by rfl) ⟨3386672, by rfl⟩ : syracuseStep 4515563 = 6773345) B6773345
theorem B2386513 : Blo 658307 2386513 := bstep (se 2 (by rfl) ⟨894942, by rfl⟩ : syracuseStep 2386513 = 1789885) B1789885
theorem B8056037 : Blo 658307 8056037 := bstep (se 4 (by rfl) ⟨755253, by rfl⟩ : syracuseStep 8056037 = 1510507) B1510507
theorem B4222313 : Blo 658307 4222313 := bstep (se 2 (by rfl) ⟨1583367, by rfl⟩ : syracuseStep 4222313 = 3166735) B3166735
theorem B3010231 : Blo 658307 3010231 := bstep (se 1 (by rfl) ⟨2257673, by rfl⟩ : syracuseStep 3010231 = 4515347) B4515347
theorem B2813885 : Blo 658307 2813885 := bstep (se 3 (by rfl) ⟨527603, by rfl⟩ : syracuseStep 2813885 = 1055207) B1055207
theorem B12874301 : Blo 658307 12874301 := bstep (se 3 (by rfl) ⟨2413931, by rfl⟩ : syracuseStep 12874301 = 4827863) B4827863
theorem B3765149 : Blo 658307 3765149 := bstep (se 3 (by rfl) ⟨705965, by rfl⟩ : syracuseStep 3765149 = 1411931) B1411931
theorem B3175463 : Blo 658307 3175463 := bstep (se 1 (by rfl) ⟨2381597, by rfl⟩ : syracuseStep 3175463 = 4763195) B4763195
theorem B1668347 : Blo 658307 1668347 := bstep (se 1 (by rfl) ⟨1251260, by rfl⟩ : syracuseStep 1668347 = 2502521) B2502521
theorem B3339791 : Blo 658307 3339791 := bstep (se 1 (by rfl) ⟨2504843, by rfl⟩ : syracuseStep 3339791 = 5009687) B5009687
theorem B1112555 : Blo 658307 1112555 := bstep (se 1 (by rfl) ⟨834416, by rfl⟩ : syracuseStep 1112555 = 1668833) B1668833
theorem B8452619 : Blo 658307 8452619 := bstep (se 1 (by rfl) ⟨6339464, by rfl⟩ : syracuseStep 8452619 = 12678929) B12678929
theorem B1375031 : Blo 658307 1375031 := bstep (se 1 (by rfl) ⟨1031273, by rfl⟩ : syracuseStep 1375031 = 2062547) B2062547
theorem B2227175 : Blo 658307 2227175 := bstep (se 1 (by rfl) ⟨1670381, by rfl⟩ : syracuseStep 2227175 = 3340763) B3340763
theorem B1113115 : Blo 658307 1113115 := bstep (se 1 (by rfl) ⟨834836, by rfl⟩ : syracuseStep 1113115 = 1669673) B1669673
theorem B2260331 : Blo 658307 2260331 := bstep (se 1 (by rfl) ⟨1695248, by rfl⟩ : syracuseStep 2260331 = 3390497) B3390497
theorem B1670777 : Blo 658307 1670777 := bstep (se 2 (by rfl) ⟨626541, by rfl⟩ : syracuseStep 1670777 = 1253083) B1253083
theorem B3210877 : Blo 658307 3210877 := bstep (se 3 (by rfl) ⟨602039, by rfl⟩ : syracuseStep 3210877 = 1204079) B1204079
theorem B1114715 : Blo 658307 1114715 := bstep (se 1 (by rfl) ⟨836036, by rfl⟩ : syracuseStep 1114715 = 1672073) B1672073
theorem B10715753 : Blo 658307 10715753 := bstep (se 2 (by rfl) ⟨4018407, by rfl⟩ : syracuseStep 10715753 = 8036815) B8036815
theorem B2228903 : Blo 658307 2228903 := bstep (se 1 (by rfl) ⟨1671677, by rfl⟩ : syracuseStep 2228903 = 3343355) B3343355
theorem B1114843 : Blo 658307 1114843 := bstep (se 1 (by rfl) ⟨836132, by rfl⟩ : syracuseStep 1114843 = 1672265) B1672265
theorem B1409761 : Blo 658307 1409761 := bstep (se 2 (by rfl) ⟨528660, by rfl⟩ : syracuseStep 1409761 = 1057321) B1057321
theorem B2229281 : Blo 658307 2229281 := bstep (se 2 (by rfl) ⟨835980, by rfl⟩ : syracuseStep 2229281 = 1671961) B1671961
theorem B3802601 : Blo 658307 3802601 := bstep (se 2 (by rfl) ⟨1425975, by rfl⟩ : syracuseStep 3802601 = 2851951) B2851951
theorem B3802625 : Blo 658307 3802625 := bstep (se 2 (by rfl) ⟨1425984, by rfl⟩ : syracuseStep 3802625 = 2851969) B2851969
theorem B3770023 : Blo 658307 3770023 := bstep (se 1 (by rfl) ⟨2827517, by rfl⟩ : syracuseStep 3770023 = 5655035) B5655035
theorem B7145135 : Blo 658307 7145135 := bstep (se 1 (by rfl) ⟨5358851, by rfl⟩ : syracuseStep 7145135 = 10717703) B10717703
theorem B1116139 : Blo 658307 1116139 := bstep (se 1 (by rfl) ⟨837104, by rfl⟩ : syracuseStep 1116139 = 1674209) B1674209
theorem B1116281 : Blo 658307 1116281 := bstep (se 2 (by rfl) ⟨418605, by rfl⟩ : syracuseStep 1116281 = 837211) B837211
theorem B2230415 : Blo 658307 2230415 := bstep (se 1 (by rfl) ⟨1672811, by rfl⟩ : syracuseStep 2230415 = 3345623) B3345623
theorem B2230523 : Blo 658307 2230523 := bstep (se 1 (by rfl) ⟨1672892, by rfl⟩ : syracuseStep 2230523 = 3345785) B3345785
theorem B2230631 : Blo 658307 2230631 := bstep (se 1 (by rfl) ⟨1672973, by rfl⟩ : syracuseStep 2230631 = 3345947) B3345947
theorem B4655819 : Blo 658307 4655819 := bstep (se 1 (by rfl) ⟨3491864, by rfl⟩ : syracuseStep 4655819 = 6983729) B6983729
theorem B3017513 : Blo 658307 3017513 := bstep (se 2 (by rfl) ⟨1131567, by rfl⟩ : syracuseStep 3017513 = 2263135) B2263135
theorem B658463 : Blo 658307 658463 := bstep (se 1 (by rfl) ⟨493847, by rfl⟩ : syracuseStep 658463 = 987695) B987695
theorem B16026731 : Blo 658307 16026731 := bstep (se 1 (by rfl) ⟨12020048, by rfl⟩ : syracuseStep 16026731 = 24040097) B24040097
theorem B658599 : Blo 658307 658599 := bstep (se 1 (by rfl) ⟨493949, by rfl⟩ : syracuseStep 658599 = 987899) B987899
theorem B658847 : Blo 658307 658847 := bstep (se 1 (by rfl) ⟨494135, by rfl⟩ : syracuseStep 658847 = 988271) B988271
theorem B3182017 : Blo 658307 3182017 := bstep (se 2 (by rfl) ⟨1193256, by rfl⟩ : syracuseStep 3182017 = 2386513) B2386513
theorem B658895 : Blo 658307 658895 := bstep (se 1 (by rfl) ⟨494171, by rfl⟩ : syracuseStep 658895 = 988343) B988343
theorem B659055 : Blo 658307 659055 := bstep (se 1 (by rfl) ⟨494291, by rfl⟩ : syracuseStep 659055 = 988583) B988583
theorem B659175 : Blo 658307 659175 := bstep (se 1 (by rfl) ⟨494381, by rfl⟩ : syracuseStep 659175 = 988763) B988763
theorem B2232359 : Blo 658307 2232359 := bstep (se 1 (by rfl) ⟨1674269, by rfl⟩ : syracuseStep 2232359 = 3348539) B3348539
theorem B1413247 : Blo 658307 1413247 := bstep (se 1 (by rfl) ⟨1059935, by rfl⟩ : syracuseStep 1413247 = 2119871) B2119871
theorem B659679 : Blo 658307 659679 := bstep (se 1 (by rfl) ⟨494759, by rfl⟩ : syracuseStep 659679 = 989519) B989519
theorem B659695 : Blo 658307 659695 := bstep (se 1 (by rfl) ⟨494771, by rfl⟩ : syracuseStep 659695 = 989543) B989543
theorem B659739 : Blo 658307 659739 := bstep (se 1 (by rfl) ⟨494804, by rfl⟩ : syracuseStep 659739 = 989609) B989609
theorem B2232737 : Blo 658307 2232737 := bstep (se 2 (by rfl) ⟨837276, by rfl⟩ : syracuseStep 2232737 = 1674553) B1674553
theorem B659995 : Blo 658307 659995 := bstep (se 1 (by rfl) ⟨494996, by rfl⟩ : syracuseStep 659995 = 989993) B989993
theorem B660135 : Blo 658307 660135 := bstep (se 1 (by rfl) ⟨495101, by rfl⟩ : syracuseStep 660135 = 990203) B990203
theorem B987839 : Blo 658307 987839 := bstep (se 1 (by rfl) ⟨740879, by rfl⟩ : syracuseStep 987839 = 1481759) B1481759
theorem B660159 : Blo 658307 660159 := bstep (se 1 (by rfl) ⟨495119, by rfl⟩ : syracuseStep 660159 = 990239) B990239
theorem B660175 : Blo 658307 660175 := bstep (se 1 (by rfl) ⟨495131, by rfl⟩ : syracuseStep 660175 = 990263) B990263
theorem B660255 : Blo 658307 660255 := bstep (se 1 (by rfl) ⟨495191, by rfl⟩ : syracuseStep 660255 = 990383) B990383
theorem B4232027 : Blo 658307 4232027 := bstep (se 1 (by rfl) ⟨3174020, by rfl⟩ : syracuseStep 4232027 = 6348041) B6348041
theorem B660351 : Blo 658307 660351 := bstep (se 1 (by rfl) ⟨495263, by rfl⟩ : syracuseStep 660351 = 990527) B990527
theorem B988127 : Blo 658307 988127 := bstep (se 1 (by rfl) ⟨741095, by rfl⟩ : syracuseStep 988127 = 1482191) B1482191
theorem B660447 : Blo 658307 660447 := bstep (se 1 (by rfl) ⟨495335, by rfl⟩ : syracuseStep 660447 = 990671) B990671
theorem B1250387 : Blo 658307 1250387 := bstep (se 1 (by rfl) ⟨937790, by rfl⟩ : syracuseStep 1250387 = 1875581) B1875581
theorem B2233439 : Blo 658307 2233439 := bstep (se 1 (by rfl) ⟨1675079, by rfl⟩ : syracuseStep 2233439 = 3350159) B3350159
theorem B660703 : Blo 658307 660703 := bstep (se 1 (by rfl) ⟨495527, by rfl⟩ : syracuseStep 660703 = 991055) B991055
theorem B660735 : Blo 658307 660735 := bstep (se 1 (by rfl) ⟨495551, by rfl⟩ : syracuseStep 660735 = 991103) B991103
theorem B1250569 : Blo 658307 1250569 := bstep (se 2 (by rfl) ⟨468963, by rfl⟩ : syracuseStep 1250569 = 937927) B937927
theorem B660783 : Blo 658307 660783 := bstep (se 1 (by rfl) ⟨495587, by rfl⟩ : syracuseStep 660783 = 991175) B991175
theorem B660943 : Blo 658307 660943 := bstep (se 1 (by rfl) ⟨495707, by rfl⟩ : syracuseStep 660943 = 991415) B991415
theorem B661023 : Blo 658307 661023 := bstep (se 1 (by rfl) ⟨495767, by rfl⟩ : syracuseStep 661023 = 991535) B991535
theorem B661183 : Blo 658307 661183 := bstep (se 1 (by rfl) ⟨495887, by rfl⟩ : syracuseStep 661183 = 991775) B991775
theorem B661223 : Blo 658307 661223 := bstep (se 1 (by rfl) ⟨495917, by rfl⟩ : syracuseStep 661223 = 991835) B991835
theorem B989225 : Blo 658307 989225 := bstep (se 2 (by rfl) ⟨370959, by rfl⟩ : syracuseStep 989225 = 741919) B741919
theorem B661567 : Blo 658307 661567 := bstep (se 1 (by rfl) ⟨496175, by rfl⟩ : syracuseStep 661567 = 992351) B992351
theorem B661607 : Blo 658307 661607 := bstep (se 1 (by rfl) ⟨496205, by rfl⟩ : syracuseStep 661607 = 992411) B992411
theorem B3348701 : Blo 658307 3348701 := bstep (se 3 (by rfl) ⟨627881, by rfl⟩ : syracuseStep 3348701 = 1255763) B1255763
theorem B2234681 : Blo 658307 2234681 := bstep (se 2 (by rfl) ⟨838005, by rfl⟩ : syracuseStep 2234681 = 1676011) B1676011
theorem B661915 : Blo 658307 661915 := bstep (se 1 (by rfl) ⟨496436, by rfl⟩ : syracuseStep 661915 = 992873) B992873
theorem B661999 : Blo 658307 661999 := bstep (se 1 (by rfl) ⟨496499, by rfl⟩ : syracuseStep 661999 = 992999) B992999
theorem B662063 : Blo 658307 662063 := bstep (se 1 (by rfl) ⟨496547, by rfl⟩ : syracuseStep 662063 = 993095) B993095
theorem B1252027 : Blo 658307 1252027 := bstep (se 1 (by rfl) ⟨939020, by rfl⟩ : syracuseStep 1252027 = 1878041) B1878041
theorem B990143 : Blo 658307 990143 := bstep (se 1 (by rfl) ⟨742607, by rfl⟩ : syracuseStep 990143 = 1485215) B1485215
theorem B1252415 : Blo 658307 1252415 := bstep (se 1 (by rfl) ⟨939311, by rfl⟩ : syracuseStep 1252415 = 1878623) B1878623
theorem B990491 : Blo 658307 990491 := bstep (se 1 (by rfl) ⟨742868, by rfl⟩ : syracuseStep 990491 = 1485737) B1485737
theorem B990875 : Blo 658307 990875 := bstep (se 1 (by rfl) ⟨743156, by rfl⟩ : syracuseStep 990875 = 1486313) B1486313
theorem B990911 : Blo 658307 990911 := bstep (se 1 (by rfl) ⟨743183, by rfl⟩ : syracuseStep 990911 = 1486367) B1486367
theorem B1875923 : Blo 658307 1875923 := bstep (se 1 (by rfl) ⟨1406942, by rfl⟩ : syracuseStep 1875923 = 2813885) B2813885
theorem B1056809 : Blo 658307 1056809 := bstep (se 2 (by rfl) ⟨396303, by rfl⟩ : syracuseStep 1056809 = 792607) B792607
theorem B1253531 : Blo 658307 1253531 := bstep (se 1 (by rfl) ⟨940148, by rfl⟩ : syracuseStep 1253531 = 1880297) B1880297
theorem B991529 : Blo 658307 991529 := bstep (se 2 (by rfl) ⟨371823, by rfl⟩ : syracuseStep 991529 = 743647) B743647
theorem B9511505 : Blo 658307 9511505 := bstep (se 2 (by rfl) ⟨3566814, by rfl⟩ : syracuseStep 9511505 = 7133629) B7133629
theorem B992393 : Blo 658307 992393 := bstep (se 2 (by rfl) ⟨372147, by rfl⟩ : syracuseStep 992393 = 744295) B744295
theorem B41100533 : Blo 658307 41100533 := bstep (se 5 (by rfl) ⟨1926587, by rfl⟩ : syracuseStep 41100533 = 3853175) B3853175
theorem B1484153 : Blo 658307 1484153 := bstep (se 2 (by rfl) ⟨556557, by rfl⟩ : syracuseStep 1484153 = 1113115) B1113115
theorem B992681 : Blo 658307 992681 := bstep (se 2 (by rfl) ⟨372255, by rfl⟩ : syracuseStep 992681 = 744511) B744511
theorem B1254943 : Blo 658307 1254943 := bstep (se 1 (by rfl) ⟨941207, by rfl⟩ : syracuseStep 1254943 = 1882415) B1882415
theorem B992975 : Blo 658307 992975 := bstep (se 1 (by rfl) ⟨744731, by rfl⟩ : syracuseStep 992975 = 1489463) B1489463
theorem B1189703 : Blo 658307 1189703 := bstep (se 1 (by rfl) ⟨892277, by rfl⟩ : syracuseStep 1189703 = 1784555) B1784555
theorem B2500577 : Blo 658307 2500577 := bstep (se 2 (by rfl) ⟨937716, by rfl⟩ : syracuseStep 2500577 = 1875433) B1875433
theorem B2500591 : Blo 658307 2500591 := bstep (se 1 (by rfl) ⟨1875443, by rfl⟩ : syracuseStep 2500591 = 3750887) B3750887
theorem B1484783 : Blo 658307 1484783 := bstep (se 1 (by rfl) ⟨1113587, by rfl⟩ : syracuseStep 1484783 = 2227175) B2227175
theorem B1190495 : Blo 658307 1190495 := bstep (se 1 (by rfl) ⟨892871, by rfl⟩ : syracuseStep 1190495 = 1785743) B1785743
theorem B1256249 : Blo 658307 1256249 := bstep (se 2 (by rfl) ⟨471093, by rfl⟩ : syracuseStep 1256249 = 942187) B942187
theorem B1486151 : Blo 658307 1486151 := bstep (se 1 (by rfl) ⟨1114613, by rfl⟩ : syracuseStep 1486151 = 2229227) B2229227
theorem B9547145 : Blo 658307 9547145 := bstep (se 2 (by rfl) ⟨3580179, by rfl⟩ : syracuseStep 9547145 = 7160359) B7160359
theorem B1584559 : Blo 658307 1584559 := bstep (se 1 (by rfl) ⟨1188419, by rfl⟩ : syracuseStep 1584559 = 2376839) B2376839
theorem B5025725 : Blo 658307 5025725 := bstep (se 3 (by rfl) ⟨942323, by rfl⟩ : syracuseStep 5025725 = 1884647) B1884647
theorem B11284919 : Blo 658307 11284919 := bstep (se 1 (by rfl) ⟨8463689, by rfl⟩ : syracuseStep 11284919 = 16927379) B16927379
theorem B2503507 : Blo 658307 2503507 := bstep (se 1 (by rfl) ⟨1877630, by rfl⟩ : syracuseStep 2503507 = 3755261) B3755261
theorem B1487699 : Blo 658307 1487699 := bstep (se 1 (by rfl) ⟨1115774, by rfl⟩ : syracuseStep 1487699 = 2231549) B2231549
theorem B5649263 : Blo 658307 5649263 := bstep (se 1 (by rfl) ⟨4236947, by rfl⟩ : syracuseStep 5649263 = 8473895) B8473895
theorem B1488059 : Blo 658307 1488059 := bstep (se 1 (by rfl) ⟨1116044, by rfl⟩ : syracuseStep 1488059 = 2232089) B2232089
theorem B5027183 : Blo 658307 5027183 := bstep (se 1 (by rfl) ⟨3770387, by rfl⟩ : syracuseStep 5027183 = 7540775) B7540775
theorem B34289243 : Blo 658307 34289243 := bstep (se 1 (by rfl) ⟨25716932, by rfl⟩ : syracuseStep 34289243 = 51433865) B51433865
theorem B5093131 : Blo 658307 5093131 := bstep (se 1 (by rfl) ⟨3819848, by rfl⟩ : syracuseStep 5093131 = 7639697) B7639697
theorem B2373437 : Blo 658307 2373437 := bstep (se 3 (by rfl) ⟨445019, by rfl⟩ : syracuseStep 2373437 = 890039) B890039
theorem B1784015 : Blo 658307 1784015 := bstep (se 1 (by rfl) ⟨1338011, by rfl⟩ : syracuseStep 1784015 = 2676023) B2676023
theorem B33077629 : Blo 658307 33077629 := bstep (se 3 (by rfl) ⟨6202055, by rfl⟩ : syracuseStep 33077629 = 12404111) B12404111
theorem B6339005 : Blo 658307 6339005 := bstep (se 3 (by rfl) ⟨1188563, by rfl⟩ : syracuseStep 6339005 = 2377127) B2377127
theorem B834239 : Blo 658307 834239 := bstep (se 1 (by rfl) ⟨625679, by rfl⟩ : syracuseStep 834239 = 1251359) B1251359
theorem B2505451 : Blo 658307 2505451 := bstep (se 1 (by rfl) ⟨1879088, by rfl⟩ : syracuseStep 2505451 = 3758177) B3758177
theorem B1784575 : Blo 658307 1784575 := bstep (se 1 (by rfl) ⟨1338431, by rfl⟩ : syracuseStep 1784575 = 2676863) B2676863
theorem B5028641 : Blo 658307 5028641 := bstep (se 2 (by rfl) ⟨1885740, by rfl⟩ : syracuseStep 5028641 = 3771481) B3771481
theorem B25312337 : Blo 658307 25312337 := bstep (se 2 (by rfl) ⟨9492126, by rfl⟩ : syracuseStep 25312337 = 18984253) B18984253
theorem B3751343 : Blo 658307 3751343 := bstep (se 1 (by rfl) ⟨2813507, by rfl⟩ : syracuseStep 3751343 = 5627015) B5627015
theorem B4013641 : Blo 658307 4013641 := bstep (se 2 (by rfl) ⟨1505115, by rfl⟩ : syracuseStep 4013641 = 3010231) B3010231
theorem B2506895 : Blo 658307 2506895 := bstep (se 1 (by rfl) ⟨1880171, by rfl⟩ : syracuseStep 2506895 = 3760343) B3760343
theorem B7127399 : Blo 658307 7127399 := bstep (se 1 (by rfl) ⟨5345549, by rfl⟩ : syracuseStep 7127399 = 10691099) B10691099
theorem B7225787 : Blo 658307 7225787 := bstep (se 1 (by rfl) ⟨5419340, by rfl⟩ : syracuseStep 7225787 = 10838681) B10838681
theorem B2114207 : Blo 658307 2114207 := bstep (se 1 (by rfl) ⟨1585655, by rfl⟩ : syracuseStep 2114207 = 3171311) B3171311
theorem B16302791 : Blo 658307 16302791 := bstep (se 1 (by rfl) ⟨12227093, by rfl⟩ : syracuseStep 16302791 = 24454187) B24454187
theorem B1885673 : Blo 658307 1885673 := bstep (se 2 (by rfl) ⟨707127, by rfl⟩ : syracuseStep 1885673 = 1414255) B1414255
theorem B2672423 : Blo 658307 2672423 := bstep (se 1 (by rfl) ⟨2004317, by rfl⟩ : syracuseStep 2672423 = 4008635) B4008635
theorem B25806721 : Blo 658307 25806721 := bstep (se 2 (by rfl) ⟨9677520, by rfl⟩ : syracuseStep 25806721 = 19355041) B19355041
theorem B837535 : Blo 658307 837535 := bstep (se 1 (by rfl) ⟨628151, by rfl⟩ : syracuseStep 837535 = 1256303) B1256303
theorem B12830875 : Blo 658307 12830875 := bstep (se 1 (by rfl) ⟨9623156, by rfl⟩ : syracuseStep 12830875 = 19246313) B19246313
theorem B24365299 : Blo 658307 24365299 := bstep (se 1 (by rfl) ⟨18273974, by rfl⟩ : syracuseStep 24365299 = 36547949) B36547949
theorem B2672891 : Blo 658307 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B706811 : Blo 658307 706811 := bstep (se 1 (by rfl) ⟨530108, by rfl⟩ : syracuseStep 706811 = 1060217) B1060217
theorem B2673233 : Blo 658307 2673233 := bstep (se 2 (by rfl) ⟨1002462, by rfl⟩ : syracuseStep 2673233 = 2004925) B2004925
theorem B4508783 : Blo 658307 4508783 := bstep (se 1 (by rfl) ⟨3381587, by rfl⟩ : syracuseStep 4508783 = 6763175) B6763175
theorem B21482765 : Blo 658307 21482765 := bstep (se 3 (by rfl) ⟨4028018, by rfl⟩ : syracuseStep 21482765 = 8056037) B8056037
theorem B2510099 : Blo 658307 2510099 := bstep (se 1 (by rfl) ⟨1882574, by rfl⟩ : syracuseStep 2510099 = 3765149) B3765149
theorem B2116975 : Blo 658307 2116975 := bstep (se 1 (by rfl) ⟨1587731, by rfl⟩ : syracuseStep 2116975 = 3175463) B3175463
theorem B741703 : Blo 658307 741703 := bstep (se 1 (by rfl) ⟨556277, by rfl⟩ : syracuseStep 741703 = 1112555) B1112555
theorem B4281169 : Blo 658307 4281169 := bstep (se 2 (by rfl) ⟨1605438, by rfl⟩ : syracuseStep 4281169 = 3210877) B3210877
theorem B25351703 : Blo 658307 25351703 := bstep (se 1 (by rfl) ⟨19013777, by rfl⟩ : syracuseStep 25351703 = 38027555) B38027555
theorem B12377117 : Blo 658307 12377117 := bstep (se 3 (by rfl) ⟨2320709, by rfl⟩ : syracuseStep 12377117 = 4641419) B4641419
theorem B3169313 : Blo 658307 3169313 := bstep (se 2 (by rfl) ⟨1188492, by rfl⟩ : syracuseStep 3169313 = 2376985) B2376985
theorem B3759635 : Blo 658307 3759635 := bstep (se 1 (by rfl) ⟨2819726, by rfl⟩ : syracuseStep 3759635 = 5639453) B5639453
theorem B2514685 : Blo 658307 2514685 := bstep (se 3 (by rfl) ⟨471503, by rfl⟩ : syracuseStep 2514685 = 943007) B943007
theorem B4022399 : Blo 658307 4022399 := bstep (se 1 (by rfl) ⟨3016799, by rfl⟩ : syracuseStep 4022399 = 6033599) B6033599
theorem B5628791 : Blo 658307 5628791 := bstep (se 1 (by rfl) ⟨4221593, by rfl⟩ : syracuseStep 5628791 = 8443187) B8443187
theorem B8479889 : Blo 658307 8479889 := bstep (se 2 (by rfl) ⟨3179958, by rfl⟩ : syracuseStep 8479889 = 6359917) B6359917
theorem B11298041 : Blo 658307 11298041 := bstep (se 2 (by rfl) ⟨4236765, by rfl⟩ : syracuseStep 11298041 = 8473531) B8473531
theorem B2221991 : Blo 658307 2221991 := bstep (se 1 (by rfl) ⟨1666493, by rfl⟩ : syracuseStep 2221991 = 3332987) B3332987
theorem B3336875 : Blo 658307 3336875 := bstep (se 1 (by rfl) ⟨2502656, by rfl⟩ : syracuseStep 3336875 = 5005313) B5005313
theorem B4745951 : Blo 658307 4745951 := bstep (se 1 (by rfl) ⟨3559463, by rfl⟩ : syracuseStep 4745951 = 7118927) B7118927
theorem B2222855 : Blo 658307 2222855 := bstep (se 1 (by rfl) ⟨1667141, by rfl⟩ : syracuseStep 2222855 = 3334283) B3334283
theorem B3337361 : Blo 658307 3337361 := bstep (se 2 (by rfl) ⟨1251510, by rfl⟩ : syracuseStep 3337361 = 2503021) B2503021
theorem B1699127 : Blo 658307 1699127 := bstep (se 1 (by rfl) ⟨1274345, by rfl⟩ : syracuseStep 1699127 = 2548691) B2548691
theorem B118746899 : Blo 658307 118746899 := bstep (se 1 (by rfl) ⟨89060174, by rfl⟩ : syracuseStep 118746899 = 178120349) B178120349
theorem B2223935 : Blo 658307 2223935 := bstep (se 1 (by rfl) ⟨1667951, by rfl⟩ : syracuseStep 2223935 = 3335903) B3335903
theorem B3010375 : Blo 658307 3010375 := bstep (se 1 (by rfl) ⟨2257781, by rfl⟩ : syracuseStep 3010375 = 4515563) B4515563
theorem B20377441 : Blo 658307 20377441 := bstep (se 2 (by rfl) ⟨7641540, by rfl⟩ : syracuseStep 20377441 = 15283081) B15283081
theorem B2814601 : Blo 658307 2814601 := bstep (se 2 (by rfl) ⟨1055475, by rfl⟩ : syracuseStep 2814601 = 2110951) B2110951
theorem B2814875 : Blo 658307 2814875 := bstep (se 1 (by rfl) ⟨2111156, by rfl⟩ : syracuseStep 2814875 = 4222313) B4222313
theorem B3765467 : Blo 658307 3765467 := bstep (se 1 (by rfl) ⟨2824100, by rfl⟩ : syracuseStep 3765467 = 5648201) B5648201
theorem B11302415 : Blo 658307 11302415 := bstep (se 1 (by rfl) ⟨8476811, by rfl⟩ : syracuseStep 11302415 = 16953623) B16953623
theorem B8582867 : Blo 658307 8582867 := bstep (se 1 (by rfl) ⟨6437150, by rfl⟩ : syracuseStep 8582867 = 12874301) B12874301
theorem B1112231 : Blo 658307 1112231 := bstep (se 1 (by rfl) ⟨834173, by rfl⟩ : syracuseStep 1112231 = 1668347) B1668347
theorem B2226365 : Blo 658307 2226365 := bstep (se 3 (by rfl) ⟨417443, by rfl⟩ : syracuseStep 2226365 = 834887) B834887
theorem B3766607 : Blo 658307 3766607 := bstep (se 1 (by rfl) ⟨2824955, by rfl⟩ : syracuseStep 3766607 = 5649911) B5649911
theorem B2226527 : Blo 658307 2226527 := bstep (se 1 (by rfl) ⟨1669895, by rfl⟩ : syracuseStep 2226527 = 3339791) B3339791
theorem B5635079 : Blo 658307 5635079 := bstep (se 1 (by rfl) ⟨4226309, by rfl⟩ : syracuseStep 5635079 = 8452619) B8452619
theorem B916687 : Blo 658307 916687 := bstep (se 1 (by rfl) ⟨687515, by rfl⟩ : syracuseStep 916687 = 1375031) B1375031
theorem B1113385 : Blo 658307 1113385 := bstep (se 2 (by rfl) ⟨417519, by rfl⟩ : syracuseStep 1113385 = 835039) B835039
theorem B1506887 : Blo 658307 1506887 := bstep (se 1 (by rfl) ⟨1130165, by rfl⟩ : syracuseStep 1506887 = 2260331) B2260331
theorem B1113851 : Blo 658307 1113851 := bstep (se 1 (by rfl) ⟨835388, by rfl⟩ : syracuseStep 1113851 = 1670777) B1670777
theorem B7536401 : Blo 658307 7536401 := bstep (se 2 (by rfl) ⟨2826150, by rfl⟩ : syracuseStep 7536401 = 5652301) B5652301
theorem B1671263 : Blo 658307 1671263 := bstep (se 1 (by rfl) ⟨1253447, by rfl⟩ : syracuseStep 1671263 = 2506895) B2506895
theorem B4817191 : Blo 658307 4817191 := bstep (se 1 (by rfl) ⟨3612893, by rfl⟩ : syracuseStep 4817191 = 7225787) B7225787
theorem B1409471 : Blo 658307 1409471 := bstep (se 1 (by rfl) ⟨1057103, by rfl⟩ : syracuseStep 1409471 = 2114207) B2114207
theorem B19006397 : Blo 658307 19006397 := bstep (se 3 (by rfl) ⟨3563699, by rfl⟩ : syracuseStep 19006397 = 7127399) B7127399
theorem B28575341 : Blo 658307 28575341 := bstep (se 3 (by rfl) ⟨5357876, by rfl⟩ : syracuseStep 28575341 = 10715753) B10715753
theorem B1673257 : Blo 658307 1673257 := bstep (se 2 (by rfl) ⟨627471, by rfl⟩ : syracuseStep 1673257 = 1254943) B1254943
theorem B10684487 : Blo 658307 10684487 := bstep (se 1 (by rfl) ⟨8013365, by rfl⟩ : syracuseStep 10684487 = 16026731) B16026731
theorem B14321843 : Blo 658307 14321843 := bstep (se 1 (by rfl) ⟨10741382, by rfl⟩ : syracuseStep 14321843 = 21482765) B21482765
theorem B1673399 : Blo 658307 1673399 := bstep (se 1 (by rfl) ⟨1255049, by rfl⟩ : syracuseStep 1673399 = 2510099) B2510099
theorem B34408961 : Blo 658307 34408961 := bstep (se 2 (by rfl) ⟨12903360, by rfl⟩ : syracuseStep 34408961 = 25806721) B25806721
theorem B1116713 : Blo 658307 1116713 := bstep (se 2 (by rfl) ⟨418767, by rfl⟩ : syracuseStep 1116713 = 837535) B837535
theorem B7539317 : Blo 658307 7539317 := bstep (se 5 (by rfl) ⟨353405, by rfl⟩ : syracuseStep 7539317 = 706811) B706811
theorem B658559 : Blo 658307 658559 := bstep (se 1 (by rfl) ⟨493919, by rfl⟩ : syracuseStep 658559 = 987839) B987839
theorem B2821351 : Blo 658307 2821351 := bstep (se 1 (by rfl) ⟨2116013, by rfl⟩ : syracuseStep 2821351 = 4232027) B4232027
theorem B658751 : Blo 658307 658751 := bstep (se 1 (by rfl) ⟨494063, by rfl⟩ : syracuseStep 658751 = 988127) B988127
theorem B659483 : Blo 658307 659483 := bstep (se 1 (by rfl) ⟨494612, by rfl⟩ : syracuseStep 659483 = 989225) B989225
theorem B2232467 : Blo 658307 2232467 := bstep (se 1 (by rfl) ⟨1674350, by rfl⟩ : syracuseStep 2232467 = 3348701) B3348701
theorem B2822633 : Blo 658307 2822633 := bstep (se 2 (by rfl) ⟨1058487, by rfl⟩ : syracuseStep 2822633 = 2116975) B2116975
theorem B660095 : Blo 658307 660095 := bstep (se 1 (by rfl) ⟨495071, by rfl⟩ : syracuseStep 660095 = 990143) B990143
theorem B660327 : Blo 658307 660327 := bstep (se 1 (by rfl) ⟨495245, by rfl⟩ : syracuseStep 660327 = 990491) B990491
theorem B660583 : Blo 658307 660583 := bstep (se 1 (by rfl) ⟨495437, by rfl⟩ : syracuseStep 660583 = 990875) B990875
theorem B660607 : Blo 658307 660607 := bstep (se 1 (by rfl) ⟨495455, by rfl⟩ : syracuseStep 660607 = 990911) B990911
theorem B27169921 : Blo 658307 27169921 := bstep (se 2 (by rfl) ⟨10188720, by rfl⟩ : syracuseStep 27169921 = 20377441) B20377441
theorem B1250615 : Blo 658307 1250615 := bstep (se 1 (by rfl) ⟨937961, by rfl⟩ : syracuseStep 1250615 = 1875923) B1875923
theorem B661019 : Blo 658307 661019 := bstep (se 1 (by rfl) ⟨495764, by rfl⟩ : syracuseStep 661019 = 991529) B991529
theorem B988937 : Blo 658307 988937 := bstep (se 2 (by rfl) ⟨370851, by rfl⟩ : syracuseStep 988937 = 741703) B741703
theorem B661595 : Blo 658307 661595 := bstep (se 1 (by rfl) ⟨496196, by rfl⟩ : syracuseStep 661595 = 992393) B992393
theorem B27400355 : Blo 658307 27400355 := bstep (se 1 (by rfl) ⟨20550266, by rfl⟩ : syracuseStep 27400355 = 41100533) B41100533
theorem B989435 : Blo 658307 989435 := bstep (se 1 (by rfl) ⟨742076, by rfl⟩ : syracuseStep 989435 = 1484153) B1484153
theorem B661787 : Blo 658307 661787 := bstep (se 1 (by rfl) ⟨496340, by rfl⟩ : syracuseStep 661787 = 992681) B992681
theorem B5708225 : Blo 658307 5708225 := bstep (se 2 (by rfl) ⟨2140584, by rfl⟩ : syracuseStep 5708225 = 4281169) B4281169
theorem B661983 : Blo 658307 661983 := bstep (se 1 (by rfl) ⟨496487, by rfl⟩ : syracuseStep 661983 = 992975) B992975
theorem B793135 : Blo 658307 793135 := bstep (se 1 (by rfl) ⟨594851, by rfl⟩ : syracuseStep 793135 = 1189703) B1189703
theorem B1481327 : Blo 658307 1481327 := bstep (se 1 (by rfl) ⟨1110995, by rfl⟩ : syracuseStep 1481327 = 2221991) B2221991
theorem B989855 : Blo 658307 989855 := bstep (se 1 (by rfl) ⟨742391, by rfl⟩ : syracuseStep 989855 = 1484783) B1484783
theorem B1481903 : Blo 658307 1481903 := bstep (se 1 (by rfl) ⟨1111427, by rfl⟩ : syracuseStep 1481903 = 2222855) B2222855
theorem B3349997 : Blo 658307 3349997 := bstep (se 3 (by rfl) ⟨628124, by rfl⟩ : syracuseStep 3349997 = 1256249) B1256249
theorem B990767 : Blo 658307 990767 := bstep (se 1 (by rfl) ⟨743075, by rfl⟩ : syracuseStep 990767 = 1486151) B1486151
theorem B6364763 : Blo 658307 6364763 := bstep (se 1 (by rfl) ⟨4773572, by rfl⟩ : syracuseStep 6364763 = 9547145) B9547145
theorem B6790841 : Blo 658307 6790841 := bstep (se 2 (by rfl) ⟨2546565, by rfl⟩ : syracuseStep 6790841 = 5093131) B5093131
theorem B1482623 : Blo 658307 1482623 := bstep (se 1 (by rfl) ⟨1111967, by rfl⟩ : syracuseStep 1482623 = 2223935) B2223935
theorem B3350483 : Blo 658307 3350483 := bstep (se 1 (by rfl) ⟨2512862, by rfl⟩ : syracuseStep 3350483 = 5025725) B5025725
theorem B991799 : Blo 658307 991799 := bstep (se 1 (by rfl) ⟨743849, by rfl⟩ : syracuseStep 991799 = 1487699) B1487699
theorem B1876583 : Blo 658307 1876583 := bstep (se 1 (by rfl) ⟨1407437, by rfl⟩ : syracuseStep 1876583 = 2814875) B2814875
theorem B992039 : Blo 658307 992039 := bstep (se 1 (by rfl) ⟨744029, by rfl⟩ : syracuseStep 992039 = 1488059) B1488059
theorem B3351455 : Blo 658307 3351455 := bstep (se 1 (by rfl) ⟨2513591, by rfl⟩ : syracuseStep 3351455 = 5027183) B5027183
theorem B1582291 : Blo 658307 1582291 := bstep (se 1 (by rfl) ⟨1186718, by rfl⟩ : syracuseStep 1582291 = 2373437) B2373437
theorem B1484243 : Blo 658307 1484243 := bstep (se 1 (by rfl) ⟨1113182, by rfl⟩ : syracuseStep 1484243 = 2226365) B2226365
theorem B1189343 : Blo 658307 1189343 := bstep (se 1 (by rfl) ⟨892007, by rfl⟩ : syracuseStep 1189343 = 1784015) B1784015
theorem B1484351 : Blo 658307 1484351 := bstep (se 1 (by rfl) ⟨1113263, by rfl⟩ : syracuseStep 1484351 = 2226527) B2226527
theorem B1222249 : Blo 658307 1222249 := bstep (se 2 (by rfl) ⟨458343, by rfl⟩ : syracuseStep 1222249 = 916687) B916687
theorem B1484513 : Blo 658307 1484513 := bstep (se 2 (by rfl) ⟨556692, by rfl⟩ : syracuseStep 1484513 = 1113385) B1113385
theorem B3352427 : Blo 658307 3352427 := bstep (se 1 (by rfl) ⟨2514320, by rfl⟩ : syracuseStep 3352427 = 5028641) B5028641
theorem B5351521 : Blo 658307 5351521 := bstep (se 2 (by rfl) ⟨2006820, by rfl⟩ : syracuseStep 5351521 = 4013641) B4013641
theorem B2500895 : Blo 658307 2500895 := bstep (se 1 (by rfl) ⟨1875671, by rfl⟩ : syracuseStep 2500895 = 3751343) B3751343
theorem B3352913 : Blo 658307 3352913 := bstep (se 2 (by rfl) ⟨1257342, by rfl⟩ : syracuseStep 3352913 = 2514685) B2514685
theorem B5024267 : Blo 658307 5024267 := bstep (se 1 (by rfl) ⟨3768200, by rfl⟩ : syracuseStep 5024267 = 7536401) B7536401
theorem B1485935 : Blo 658307 1485935 := bstep (se 1 (by rfl) ⟨1114451, by rfl⟩ : syracuseStep 1485935 = 2228903) B2228903
theorem B1486187 : Blo 658307 1486187 := bstep (se 1 (by rfl) ⟨1114640, by rfl⟩ : syracuseStep 1486187 = 2229281) B2229281
theorem B68431333 : Blo 658307 68431333 := bstep (se 4 (by rfl) ⟨6415437, by rfl⟩ : syracuseStep 68431333 = 12830875) B12830875
theorem B1486457 : Blo 658307 1486457 := bstep (se 2 (by rfl) ⟨557421, by rfl⟩ : syracuseStep 1486457 = 1114843) B1114843
theorem B1879681 : Blo 658307 1879681 := bstep (se 2 (by rfl) ⟨704880, by rfl⟩ : syracuseStep 1879681 = 1409761) B1409761
theorem B2535067 : Blo 658307 2535067 := bstep (se 1 (by rfl) ⟨1901300, by rfl⟩ : syracuseStep 2535067 = 3802601) B3802601
theorem B1257115 : Blo 658307 1257115 := bstep (se 1 (by rfl) ⟨942836, by rfl⟩ : syracuseStep 1257115 = 1885673) B1885673
theorem B2535083 : Blo 658307 2535083 := bstep (se 1 (by rfl) ⟨1901312, by rfl⟩ : syracuseStep 2535083 = 3802625) B3802625
theorem B4763423 : Blo 658307 4763423 := bstep (se 1 (by rfl) ⟨3572567, by rfl⟩ : syracuseStep 4763423 = 7145135) B7145135
theorem B1781615 : Blo 658307 1781615 := bstep (se 1 (by rfl) ⟨1336211, by rfl⟩ : syracuseStep 1781615 = 2672423) B2672423
theorem B1486943 : Blo 658307 1486943 := bstep (se 1 (by rfl) ⟨1115207, by rfl⟩ : syracuseStep 1486943 = 2230415) B2230415
theorem B1781927 : Blo 658307 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B1487015 : Blo 658307 1487015 := bstep (se 1 (by rfl) ⟨1115261, by rfl⟩ : syracuseStep 1487015 = 2230523) B2230523
theorem B1487087 : Blo 658307 1487087 := bstep (se 1 (by rfl) ⟨1115315, by rfl⟩ : syracuseStep 1487087 = 2230631) B2230631
theorem B1782155 : Blo 658307 1782155 := bstep (se 1 (by rfl) ⟨1336616, by rfl⟩ : syracuseStep 1782155 = 2673233) B2673233
theorem B5026697 : Blo 658307 5026697 := bstep (se 2 (by rfl) ⟨1885011, by rfl⟩ : syracuseStep 5026697 = 3770023) B3770023
theorem B1488185 : Blo 658307 1488185 := bstep (se 2 (by rfl) ⟨558069, by rfl⟩ : syracuseStep 1488185 = 1116139) B1116139
theorem B1488239 : Blo 658307 1488239 := bstep (se 1 (by rfl) ⟨1116179, by rfl⟩ : syracuseStep 1488239 = 2232359) B2232359
theorem B1488491 : Blo 658307 1488491 := bstep (se 1 (by rfl) ⟨1116368, by rfl⟩ : syracuseStep 1488491 = 2232737) B2232737
theorem B32487065 : Blo 658307 32487065 := bstep (se 2 (by rfl) ⟨12182649, by rfl⟩ : syracuseStep 32487065 = 24365299) B24365299
theorem B833591 : Blo 658307 833591 := bstep (se 1 (by rfl) ⟨625193, by rfl⟩ : syracuseStep 833591 = 1250387) B1250387
theorem B1488959 : Blo 658307 1488959 := bstep (se 1 (by rfl) ⟨1116719, by rfl⟩ : syracuseStep 1488959 = 2233439) B2233439
theorem B9517733 : Blo 658307 9517733 := bstep (se 4 (by rfl) ⟨892287, by rfl⟩ : syracuseStep 9517733 = 1784575) B1784575
theorem B1489787 : Blo 658307 1489787 := bstep (se 1 (by rfl) ⟨1117340, by rfl⟩ : syracuseStep 1489787 = 2234681) B2234681
theorem B2112745 : Blo 658307 2112745 := bstep (se 2 (by rfl) ⟨792279, by rfl⟩ : syracuseStep 2112745 = 1584559) B1584559
theorem B4242689 : Blo 658307 4242689 := bstep (se 2 (by rfl) ⟨1591008, by rfl⟩ : syracuseStep 4242689 = 3182017) B3182017
theorem B2112875 : Blo 658307 2112875 := bstep (se 1 (by rfl) ⟨1584656, by rfl⟩ : syracuseStep 2112875 = 3169313) B3169313
theorem B834943 : Blo 658307 834943 := bstep (se 1 (by rfl) ⟨626207, by rfl⟩ : syracuseStep 834943 = 1252415) B1252415
theorem B2506423 : Blo 658307 2506423 := bstep (se 1 (by rfl) ⟨1879817, by rfl⟩ : syracuseStep 2506423 = 3759635) B3759635
theorem B704539 : Blo 658307 704539 := bstep (se 1 (by rfl) ⟨528404, by rfl⟩ : syracuseStep 704539 = 1056809) B1056809
theorem B835687 : Blo 658307 835687 := bstep (se 1 (by rfl) ⟨626765, by rfl⟩ : syracuseStep 835687 = 1253531) B1253531
theorem B1884329 : Blo 658307 1884329 := bstep (se 2 (by rfl) ⟨706623, by rfl⟩ : syracuseStep 1884329 = 1413247) B1413247
theorem B6341003 : Blo 658307 6341003 := bstep (se 1 (by rfl) ⟨4755752, by rfl⟩ : syracuseStep 6341003 = 9511505) B9511505
theorem B3752527 : Blo 658307 3752527 := bstep (se 1 (by rfl) ⟨2814395, by rfl⟩ : syracuseStep 3752527 = 5628791) B5628791
theorem B5653259 : Blo 658307 5653259 := bstep (se 1 (by rfl) ⟨4239944, by rfl⟩ : syracuseStep 5653259 = 8479889) B8479889
theorem B3752801 : Blo 658307 3752801 := bstep (se 2 (by rfl) ⟨1407300, by rfl⟩ : syracuseStep 3752801 = 2814601) B2814601
theorem B3163967 : Blo 658307 3163967 := bstep (se 1 (by rfl) ⟨2372975, by rfl⟩ : syracuseStep 3163967 = 4745951) B4745951
theorem B8046701 : Blo 658307 8046701 := bstep (se 3 (by rfl) ⟨1508756, by rfl⟩ : syracuseStep 8046701 = 3017513) B3017513
theorem B1132751 : Blo 658307 1132751 := bstep (se 1 (by rfl) ⟨849563, by rfl⟩ : syracuseStep 1132751 = 1699127) B1699127
theorem B7523279 : Blo 658307 7523279 := bstep (se 1 (by rfl) ⟨5642459, by rfl⟩ : syracuseStep 7523279 = 11284919) B11284919
theorem B2510311 : Blo 658307 2510311 := bstep (se 1 (by rfl) ⟨1882733, by rfl⟩ : syracuseStep 2510311 = 3765467) B3765467
theorem B22859495 : Blo 658307 22859495 := bstep (se 1 (by rfl) ⟨17144621, by rfl⟩ : syracuseStep 22859495 = 34289243) B34289243
theorem B5721911 : Blo 658307 5721911 := bstep (se 1 (by rfl) ⟨4291433, by rfl⟩ : syracuseStep 5721911 = 8582867) B8582867
theorem B741487 : Blo 658307 741487 := bstep (se 1 (by rfl) ⟨556115, by rfl⟩ : syracuseStep 741487 = 1112231) B1112231
theorem B2511071 : Blo 658307 2511071 := bstep (se 1 (by rfl) ⟨1883303, by rfl⟩ : syracuseStep 2511071 = 3766607) B3766607
theorem B3756719 : Blo 658307 3756719 := bstep (se 1 (by rfl) ⟨2817539, by rfl⟩ : syracuseStep 3756719 = 5635079) B5635079
theorem B1004591 : Blo 658307 1004591 := bstep (se 1 (by rfl) ⟨753443, by rfl⟩ : syracuseStep 1004591 = 1506887) B1506887
theorem B742567 : Blo 658307 742567 := bstep (se 1 (by rfl) ⟨556925, by rfl⟩ : syracuseStep 742567 = 1113851) B1113851
theorem B743143 : Blo 658307 743143 := bstep (se 1 (by rfl) ⟨557357, by rfl⟩ : syracuseStep 743143 = 1114715) B1114715
theorem B10868527 : Blo 658307 10868527 := bstep (se 1 (by rfl) ⟨8151395, by rfl⟩ : syracuseStep 10868527 = 16302791) B16302791
theorem B744187 : Blo 658307 744187 := bstep (se 1 (by rfl) ⟨558140, by rfl⟩ : syracuseStep 744187 = 1116281) B1116281
theorem B3103879 : Blo 658307 3103879 := bstep (se 1 (by rfl) ⟨2327909, by rfl⟩ : syracuseStep 3103879 = 4655819) B4655819
theorem B176414021 : Blo 658307 176414021 := bstep (se 4 (by rfl) ⟨16538814, by rfl⟩ : syracuseStep 176414021 = 33077629) B33077629
theorem B3005855 : Blo 658307 3005855 := bstep (se 1 (by rfl) ⟨2254391, by rfl⟩ : syracuseStep 3005855 = 4508783) B4508783
theorem B3334121 : Blo 658307 3334121 := bstep (se 2 (by rfl) ⟨1250295, by rfl⟩ : syracuseStep 3334121 = 2500591) B2500591
theorem B16901135 : Blo 658307 16901135 := bstep (se 1 (by rfl) ⟨12675851, by rfl⟩ : syracuseStep 16901135 = 25351703) B25351703
theorem B8251411 : Blo 658307 8251411 := bstep (se 1 (by rfl) ⟨6188558, by rfl⟩ : syracuseStep 8251411 = 12377117) B12377117
theorem B2681599 : Blo 658307 2681599 := bstep (se 1 (by rfl) ⟨2011199, by rfl⟩ : syracuseStep 2681599 = 4022399) B4022399
theorem B7532027 : Blo 658307 7532027 := bstep (se 1 (by rfl) ⟨5649020, by rfl⟩ : syracuseStep 7532027 = 11298041) B11298041
theorem B3338009 : Blo 658307 3338009 := bstep (se 2 (by rfl) ⟨1251753, by rfl⟩ : syracuseStep 3338009 = 2503507) B2503507
theorem B1667051 : Blo 658307 1667051 := bstep (se 1 (by rfl) ⟨1250288, by rfl⟩ : syracuseStep 1667051 = 2500577) B2500577
theorem B3174653 : Blo 658307 3174653 := bstep (se 3 (by rfl) ⟨595247, by rfl⟩ : syracuseStep 3174653 = 1190495) B1190495
theorem B1667425 : Blo 658307 1667425 := bstep (se 2 (by rfl) ⟨625284, by rfl⟩ : syracuseStep 1667425 = 1250569) B1250569
theorem B2224583 : Blo 658307 2224583 := bstep (se 1 (by rfl) ⟨1668437, by rfl⟩ : syracuseStep 2224583 = 3336875) B3336875
theorem B2224637 : Blo 658307 2224637 := bstep (se 3 (by rfl) ⟨417119, by rfl⟩ : syracuseStep 2224637 = 834239) B834239
theorem B2224907 : Blo 658307 2224907 := bstep (se 1 (by rfl) ⟨1668680, by rfl⟩ : syracuseStep 2224907 = 3337361) B3337361
theorem B79164599 : Blo 658307 79164599 := bstep (se 1 (by rfl) ⟨59373449, by rfl⟩ : syracuseStep 79164599 = 118746899) B118746899
theorem B3766175 : Blo 658307 3766175 := bstep (se 1 (by rfl) ⟨2824631, by rfl⟩ : syracuseStep 3766175 = 5649263) B5649263
theorem B1669369 : Blo 658307 1669369 := bstep (se 2 (by rfl) ⟨626013, by rfl⟩ : syracuseStep 1669369 = 1252027) B1252027
theorem B3340601 : Blo 658307 3340601 := bstep (se 2 (by rfl) ⟨1252725, by rfl⟩ : syracuseStep 3340601 = 2505451) B2505451
theorem B7534943 : Blo 658307 7534943 := bstep (se 1 (by rfl) ⟨5651207, by rfl⟩ : syracuseStep 7534943 = 11302415) B11302415
theorem B4226003 : Blo 658307 4226003 := bstep (se 1 (by rfl) ⟨3169502, by rfl⟩ : syracuseStep 4226003 = 6339005) B6339005
theorem B16055333 : Blo 658307 16055333 := bstep (se 4 (by rfl) ⟨1505187, by rfl⟩ : syracuseStep 16055333 = 3010375) B3010375
theorem B16874891 : Blo 658307 16874891 := bstep (se 1 (by rfl) ⟨12656168, by rfl⟩ : syracuseStep 16874891 = 25312337) B25312337
theorem B1114175 : Blo 658307 1114175 := bstep (se 1 (by rfl) ⟨835631, by rfl⟩ : syracuseStep 1114175 = 1671263) B1671263
theorem B1114249 : Blo 658307 1114249 := bstep (se 2 (by rfl) ⟨417843, by rfl⟩ : syracuseStep 1114249 = 835687) B835687
theorem B4227335 : Blo 658307 4227335 := bstep (se 1 (by rfl) ⟨3170501, by rfl⟩ : syracuseStep 4227335 = 6341003) B6341003
theorem B6422921 : Blo 658307 6422921 := bstep (se 2 (by rfl) ⟨2408595, by rfl⟩ : syracuseStep 6422921 = 4817191) B4817191
theorem B3768839 : Blo 658307 3768839 := bstep (se 1 (by rfl) ⟨2826629, by rfl⟩ : syracuseStep 3768839 = 5653259) B5653259
theorem B1115599 : Blo 658307 1115599 := bstep (se 1 (by rfl) ⟨836699, by rfl⟩ : syracuseStep 1115599 = 1673399) B1673399
theorem B22939307 : Blo 658307 22939307 := bstep (se 1 (by rfl) ⟨17204480, by rfl⟩ : syracuseStep 22939307 = 34408961) B34408961
theorem B5015519 : Blo 658307 5015519 := bstep (se 1 (by rfl) ⟨3761639, by rfl⟩ : syracuseStep 5015519 = 7523279) B7523279
theorem B15239663 : Blo 658307 15239663 := bstep (se 1 (by rfl) ⟨11429747, by rfl⟩ : syracuseStep 15239663 = 22859495) B22859495
theorem B2231009 : Blo 658307 2231009 := bstep (se 2 (by rfl) ⟨836628, by rfl⟩ : syracuseStep 2231009 = 1673257) B1673257
theorem B1674047 : Blo 658307 1674047 := bstep (se 1 (by rfl) ⟨1255535, by rfl⟩ : syracuseStep 1674047 = 2511071) B2511071
theorem B4230053 : Blo 658307 4230053 := bstep (se 4 (by rfl) ⟨396567, by rfl⟩ : syracuseStep 4230053 = 793135) B793135
theorem B3575465 : Blo 658307 3575465 := bstep (se 2 (by rfl) ⟨1340799, by rfl⟩ : syracuseStep 3575465 = 2681599) B2681599
theorem B659291 : Blo 658307 659291 := bstep (se 1 (by rfl) ⟨494468, by rfl⟩ : syracuseStep 659291 = 988937) B988937
theorem B659623 : Blo 658307 659623 := bstep (se 1 (by rfl) ⟨494717, by rfl⟩ : syracuseStep 659623 = 989435) B989435
theorem B3805483 : Blo 658307 3805483 := bstep (se 1 (by rfl) ⟨2854112, by rfl⟩ : syracuseStep 3805483 = 5708225) B5708225
theorem B987551 : Blo 658307 987551 := bstep (se 1 (by rfl) ⟨740663, by rfl⟩ : syracuseStep 987551 = 1481327) B1481327
theorem B659903 : Blo 658307 659903 := bstep (se 1 (by rfl) ⟨494927, by rfl⟩ : syracuseStep 659903 = 989855) B989855
theorem B3347081 : Blo 658307 3347081 := bstep (se 2 (by rfl) ⟨1255155, by rfl⟩ : syracuseStep 3347081 = 2510311) B2510311
theorem B987935 : Blo 658307 987935 := bstep (se 1 (by rfl) ⟨740951, by rfl⟩ : syracuseStep 987935 = 1481903) B1481903
theorem B3380089 : Blo 658307 3380089 := bstep (se 2 (by rfl) ⟨1267533, by rfl⟩ : syracuseStep 3380089 = 2535067) B2535067
theorem B1676153 : Blo 658307 1676153 := bstep (se 2 (by rfl) ⟨628557, by rfl⟩ : syracuseStep 1676153 = 1257115) B1257115
theorem B117609347 : Blo 658307 117609347 := bstep (se 1 (by rfl) ⟨88207010, by rfl⟩ : syracuseStep 117609347 = 176414021) B176414021
theorem B2003903 : Blo 658307 2003903 := bstep (se 1 (by rfl) ⟨1502927, by rfl⟩ : syracuseStep 2003903 = 3005855) B3005855
theorem B2233331 : Blo 658307 2233331 := bstep (se 1 (by rfl) ⟨1674998, by rfl⟩ : syracuseStep 2233331 = 3349997) B3349997
theorem B660511 : Blo 658307 660511 := bstep (se 1 (by rfl) ⟨495383, by rfl⟩ : syracuseStep 660511 = 990767) B990767
theorem B4527227 : Blo 658307 4527227 := bstep (se 1 (by rfl) ⟨3395420, by rfl⟩ : syracuseStep 4527227 = 6790841) B6790841
theorem B988415 : Blo 658307 988415 := bstep (se 1 (by rfl) ⟨741311, by rfl⟩ : syracuseStep 988415 = 1482623) B1482623
theorem B2233655 : Blo 658307 2233655 := bstep (se 1 (by rfl) ⟨1675241, by rfl⟩ : syracuseStep 2233655 = 3350483) B3350483
theorem B988649 : Blo 658307 988649 := bstep (se 2 (by rfl) ⟨370743, by rfl⟩ : syracuseStep 988649 = 741487) B741487
theorem B661199 : Blo 658307 661199 := bstep (se 1 (by rfl) ⟨495899, by rfl⟩ : syracuseStep 661199 = 991799) B991799
theorem B1251055 : Blo 658307 1251055 := bstep (se 1 (by rfl) ⟨938291, by rfl⟩ : syracuseStep 1251055 = 1876583) B1876583
theorem B661359 : Blo 658307 661359 := bstep (se 1 (by rfl) ⟨496019, by rfl⟩ : syracuseStep 661359 = 992039) B992039
theorem B3020669 : Blo 658307 3020669 := bstep (se 3 (by rfl) ⟨566375, by rfl⟩ : syracuseStep 3020669 = 1132751) B1132751
theorem B2234303 : Blo 658307 2234303 := bstep (se 1 (by rfl) ⟨1675727, by rfl⟩ : syracuseStep 2234303 = 3351455) B3351455
theorem B989495 : Blo 658307 989495 := bstep (se 1 (by rfl) ⟨742121, by rfl⟩ : syracuseStep 989495 = 1484243) B1484243
theorem B792895 : Blo 658307 792895 := bstep (se 1 (by rfl) ⟨594671, by rfl⟩ : syracuseStep 792895 = 1189343) B1189343
theorem B989567 : Blo 658307 989567 := bstep (se 1 (by rfl) ⟨742175, by rfl⟩ : syracuseStep 989567 = 1484351) B1484351
theorem B989675 : Blo 658307 989675 := bstep (se 1 (by rfl) ⟨742256, by rfl⟩ : syracuseStep 989675 = 1484513) B1484513
theorem B2234951 : Blo 658307 2234951 := bstep (se 1 (by rfl) ⟨1676213, by rfl⟩ : syracuseStep 2234951 = 3352427) B3352427
theorem B990089 : Blo 658307 990089 := bstep (se 2 (by rfl) ⟨371283, by rfl⟩ : syracuseStep 990089 = 742567) B742567
theorem B2235275 : Blo 658307 2235275 := bstep (se 1 (by rfl) ⟨1676456, by rfl⟩ : syracuseStep 2235275 = 3352913) B3352913
theorem B3349511 : Blo 658307 3349511 := bstep (se 1 (by rfl) ⟨2512133, by rfl⟩ : syracuseStep 3349511 = 5024267) B5024267
theorem B990623 : Blo 658307 990623 := bstep (se 1 (by rfl) ⟨742967, by rfl⟩ : syracuseStep 990623 = 1485935) B1485935
theorem B990791 : Blo 658307 990791 := bstep (se 1 (by rfl) ⟨743093, by rfl⟩ : syracuseStep 990791 = 1486187) B1486187
theorem B990857 : Blo 658307 990857 := bstep (se 2 (by rfl) ⟨371571, by rfl⟩ : syracuseStep 990857 = 743143) B743143
theorem B5021351 : Blo 658307 5021351 := bstep (se 1 (by rfl) ⟨3766013, by rfl⟩ : syracuseStep 5021351 = 7532027) B7532027
theorem B14491369 : Blo 658307 14491369 := bstep (se 2 (by rfl) ⟨5434263, by rfl⟩ : syracuseStep 14491369 = 10868527) B10868527
theorem B990971 : Blo 658307 990971 := bstep (se 1 (by rfl) ⟨743228, by rfl⟩ : syracuseStep 990971 = 1486457) B1486457
theorem B1187743 : Blo 658307 1187743 := bstep (se 1 (by rfl) ⟨890807, by rfl⟩ : syracuseStep 1187743 = 1781615) B1781615
theorem B991295 : Blo 658307 991295 := bstep (se 1 (by rfl) ⟨743471, by rfl⟩ : syracuseStep 991295 = 1486943) B1486943
theorem B1187951 : Blo 658307 1187951 := bstep (se 1 (by rfl) ⟨890963, by rfl⟩ : syracuseStep 1187951 = 1781927) B1781927
theorem B991343 : Blo 658307 991343 := bstep (se 1 (by rfl) ⟨743507, by rfl⟩ : syracuseStep 991343 = 1487015) B1487015
theorem B991391 : Blo 658307 991391 := bstep (se 1 (by rfl) ⟨743543, by rfl⟩ : syracuseStep 991391 = 1487087) B1487087
theorem B1188103 : Blo 658307 1188103 := bstep (se 1 (by rfl) ⟨891077, by rfl⟩ : syracuseStep 1188103 = 1782155) B1782155
theorem B1483055 : Blo 658307 1483055 := bstep (se 1 (by rfl) ⟨1112291, by rfl⟩ : syracuseStep 1483055 = 2224583) B2224583
theorem B1483091 : Blo 658307 1483091 := bstep (se 1 (by rfl) ⟨1112318, by rfl⟩ : syracuseStep 1483091 = 2224637) B2224637
theorem B1483271 : Blo 658307 1483271 := bstep (se 1 (by rfl) ⟨1112453, by rfl⟩ : syracuseStep 1483271 = 2224907) B2224907
theorem B3351131 : Blo 658307 3351131 := bstep (se 1 (by rfl) ⟨2513348, by rfl⟩ : syracuseStep 3351131 = 5026697) B5026697
theorem B992123 : Blo 658307 992123 := bstep (se 1 (by rfl) ⟨744092, by rfl⟩ : syracuseStep 992123 = 1488185) B1488185
theorem B992159 : Blo 658307 992159 := bstep (se 1 (by rfl) ⟨744119, by rfl⟩ : syracuseStep 992159 = 1488239) B1488239
theorem B992249 : Blo 658307 992249 := bstep (se 2 (by rfl) ⟨372093, by rfl⟩ : syracuseStep 992249 = 744187) B744187
theorem B992327 : Blo 658307 992327 := bstep (se 1 (by rfl) ⟨744245, by rfl⟩ : syracuseStep 992327 = 1488491) B1488491
theorem B992639 : Blo 658307 992639 := bstep (se 1 (by rfl) ⟨744479, by rfl⟩ : syracuseStep 992639 = 1488959) B1488959
theorem B4138505 : Blo 658307 4138505 := bstep (se 2 (by rfl) ⟨1551939, by rfl⟩ : syracuseStep 4138505 = 3103879) B3103879
theorem B5023295 : Blo 658307 5023295 := bstep (se 1 (by rfl) ⟨3767471, by rfl⟩ : syracuseStep 5023295 = 7534943) B7534943
theorem B993191 : Blo 658307 993191 := bstep (se 1 (by rfl) ⟨744893, by rfl⟩ : syracuseStep 993191 = 1489787) B1489787
theorem B2828459 : Blo 658307 2828459 := bstep (se 1 (by rfl) ⟨2121344, by rfl⟩ : syracuseStep 2828459 = 4242689) B4242689
theorem B11249927 : Blo 658307 11249927 := bstep (se 1 (by rfl) ⟨8437445, by rfl⟩ : syracuseStep 11249927 = 16874891) B16874891
theorem B1256219 : Blo 658307 1256219 := bstep (se 1 (by rfl) ⟨942164, by rfl⟩ : syracuseStep 1256219 = 1884329) B1884329
theorem B2501867 : Blo 658307 2501867 := bstep (se 1 (by rfl) ⟨1876400, by rfl⟩ : syracuseStep 2501867 = 3752801) B3752801
theorem B8465741 : Blo 658307 8465741 := bstep (se 3 (by rfl) ⟨1587326, by rfl⟩ : syracuseStep 8465741 = 3174653) B3174653
theorem B19050227 : Blo 658307 19050227 := bstep (se 1 (by rfl) ⟨14287670, by rfl⟩ : syracuseStep 19050227 = 28575341) B28575341
theorem B2109311 : Blo 658307 2109311 := bstep (se 1 (by rfl) ⟨1581983, by rfl⟩ : syracuseStep 2109311 = 3163967) B3163967
theorem B7122991 : Blo 658307 7122991 := bstep (se 1 (by rfl) ⟨5342243, by rfl⟩ : syracuseStep 7122991 = 10684487) B10684487
theorem B9547895 : Blo 658307 9547895 := bstep (se 1 (by rfl) ⟨7160921, by rfl⟩ : syracuseStep 9547895 = 14321843) B14321843
theorem B2109721 : Blo 658307 2109721 := bstep (se 2 (by rfl) ⟨791145, by rfl⟩ : syracuseStep 2109721 = 1582291) B1582291
theorem B5026211 : Blo 658307 5026211 := bstep (se 1 (by rfl) ⟨3769658, by rfl⟩ : syracuseStep 5026211 = 7539317) B7539317
theorem B3814607 : Blo 658307 3814607 := bstep (se 1 (by rfl) ⟨2860955, by rfl⟩ : syracuseStep 3814607 = 5721911) B5721911
theorem B1488311 : Blo 658307 1488311 := bstep (se 1 (by rfl) ⟨1116233, by rfl⟩ : syracuseStep 1488311 = 2232467) B2232467
theorem B1881755 : Blo 658307 1881755 := bstep (se 1 (by rfl) ⟨1411316, by rfl⟩ : syracuseStep 1881755 = 2822633) B2822633
theorem B2504479 : Blo 658307 2504479 := bstep (se 1 (by rfl) ⟨1878359, by rfl⟩ : syracuseStep 2504479 = 3756719) B3756719
theorem B211105597 : Blo 658307 211105597 := bstep (se 3 (by rfl) ⟨39582299, by rfl⟩ : syracuseStep 211105597 = 79164599) B79164599
theorem B669727 : Blo 658307 669727 := bstep (se 1 (by rfl) ⟨502295, by rfl⟩ : syracuseStep 669727 = 1004591) B1004591
theorem B833743 : Blo 658307 833743 := bstep (se 1 (by rfl) ⟨625307, by rfl⟩ : syracuseStep 833743 = 1250615) B1250615
theorem B18266903 : Blo 658307 18266903 := bstep (se 1 (by rfl) ⟨13700177, by rfl⟩ : syracuseStep 18266903 = 27400355) B27400355
theorem B91241777 : Blo 658307 91241777 := bstep (se 2 (by rfl) ⟨34215666, by rfl⟩ : syracuseStep 91241777 = 68431333) B68431333
theorem B2506241 : Blo 658307 2506241 := bstep (se 2 (by rfl) ⟨939840, by rfl⟩ : syracuseStep 2506241 = 1879681) B1879681
theorem B4243175 : Blo 658307 4243175 := bstep (se 1 (by rfl) ⟨3182381, by rfl⟩ : syracuseStep 4243175 = 6364763) B6364763
theorem B36226561 : Blo 658307 36226561 := bstep (se 2 (by rfl) ⟨13584960, by rfl⟩ : syracuseStep 36226561 = 27169921) B27169921
theorem B1690055 : Blo 658307 1690055 := bstep (se 1 (by rfl) ⟨1267541, by rfl⟩ : syracuseStep 1690055 = 2535083) B2535083
theorem B2510783 : Blo 658307 2510783 := bstep (se 1 (by rfl) ⟨1883087, by rfl⟩ : syracuseStep 2510783 = 3766175) B3766175
theorem B6345155 : Blo 658307 6345155 := bstep (se 1 (by rfl) ⟨4758866, by rfl⟩ : syracuseStep 6345155 = 9517733) B9517733
theorem B10703555 : Blo 658307 10703555 := bstep (se 1 (by rfl) ⟨8027666, by rfl⟩ : syracuseStep 10703555 = 16055333) B16055333
theorem B939385 : Blo 658307 939385 := bstep (se 2 (by rfl) ⟨352269, by rfl⟩ : syracuseStep 939385 = 704539) B704539
theorem B939647 : Blo 658307 939647 := bstep (se 1 (by rfl) ⟨704735, by rfl⟩ : syracuseStep 939647 = 1409471) B1409471
theorem B12670931 : Blo 658307 12670931 := bstep (se 1 (by rfl) ⟨9503198, by rfl⟩ : syracuseStep 12670931 = 19006397) B19006397
theorem B5003369 : Blo 658307 5003369 := bstep (se 2 (by rfl) ⟨1876263, by rfl⟩ : syracuseStep 5003369 = 3752527) B3752527
theorem B5364467 : Blo 658307 5364467 := bstep (se 1 (by rfl) ⟨4023350, by rfl⟩ : syracuseStep 5364467 = 8046701) B8046701
theorem B744475 : Blo 658307 744475 := bstep (se 1 (by rfl) ⟨558356, by rfl⟩ : syracuseStep 744475 = 1116713) B1116713
theorem B1629665 : Blo 658307 1629665 := bstep (se 2 (by rfl) ⟨611124, by rfl⟩ : syracuseStep 1629665 = 1222249) B1222249
theorem B11001881 : Blo 658307 11001881 := bstep (se 2 (by rfl) ⟨4125705, by rfl⟩ : syracuseStep 11001881 = 8251411) B8251411
theorem B7135361 : Blo 658307 7135361 := bstep (se 2 (by rfl) ⟨2675760, by rfl⟩ : syracuseStep 7135361 = 5351521) B5351521
theorem B3761801 : Blo 658307 3761801 := bstep (se 2 (by rfl) ⟨1410675, by rfl⟩ : syracuseStep 3761801 = 2821351) B2821351
theorem B2222747 : Blo 658307 2222747 := bstep (se 1 (by rfl) ⟨1667060, by rfl⟩ : syracuseStep 2222747 = 3334121) B3334121
theorem B2222909 : Blo 658307 2222909 := bstep (se 3 (by rfl) ⟨416795, by rfl⟩ : syracuseStep 2222909 = 833591) B833591
theorem B2223233 : Blo 658307 2223233 := bstep (se 2 (by rfl) ⟨833712, by rfl⟩ : syracuseStep 2223233 = 1667425) B1667425
theorem B11267423 : Blo 658307 11267423 := bstep (se 1 (by rfl) ⟨8450567, by rfl⟩ : syracuseStep 11267423 = 16901135) B16901135
theorem B1667263 : Blo 658307 1667263 := bstep (se 1 (by rfl) ⟨1250447, by rfl⟩ : syracuseStep 1667263 = 2500895) B2500895
theorem B2225339 : Blo 658307 2225339 := bstep (se 1 (by rfl) ⟨1669004, by rfl⟩ : syracuseStep 2225339 = 3338009) B3338009
theorem B3175615 : Blo 658307 3175615 := bstep (se 1 (by rfl) ⟨2381711, by rfl⟩ : syracuseStep 3175615 = 4763423) B4763423
theorem B1111367 : Blo 658307 1111367 := bstep (se 1 (by rfl) ⟨833525, by rfl⟩ : syracuseStep 1111367 = 1667051) B1667051
theorem B2225825 : Blo 658307 2225825 := bstep (se 2 (by rfl) ⟨834684, by rfl⟩ : syracuseStep 2225825 = 1669369) B1669369
theorem B21658043 : Blo 658307 21658043 := bstep (se 1 (by rfl) ⟨16243532, by rfl⟩ : syracuseStep 21658043 = 32487065) B32487065
theorem B2227067 : Blo 658307 2227067 := bstep (se 1 (by rfl) ⟨1670300, by rfl⟩ : syracuseStep 2227067 = 3340601) B3340601
theorem B2816993 : Blo 658307 2816993 := bstep (se 2 (by rfl) ⟨1056372, by rfl⟩ : syracuseStep 2816993 = 2112745) B2112745
theorem B1113257 : Blo 658307 1113257 := bstep (se 2 (by rfl) ⟨417471, by rfl⟩ : syracuseStep 1113257 = 834943) B834943
theorem B2817335 : Blo 658307 2817335 := bstep (se 1 (by rfl) ⟨2113001, by rfl⟩ : syracuseStep 2817335 = 4226003) B4226003
theorem B1408583 : Blo 658307 1408583 := bstep (se 1 (by rfl) ⟨1056437, by rfl⟩ : syracuseStep 1408583 = 2112875) B2112875
theorem B3341897 : Blo 658307 3341897 := bstep (se 2 (by rfl) ⟨1253211, by rfl⟩ : syracuseStep 3341897 = 2506423) B2506423
theorem B3571877 : Blo 658307 3571877 := bstep (se 4 (by rfl) ⟨334863, by rfl⟩ : syracuseStep 3571877 = 669727) B669727
theorem B2818223 : Blo 658307 2818223 := bstep (se 1 (by rfl) ⟨2113667, by rfl⟩ : syracuseStep 2818223 = 4227335) B4227335
theorem B3343679 : Blo 658307 3343679 := bstep (se 1 (by rfl) ⟨2507759, by rfl⟩ : syracuseStep 3343679 = 5015519) B5015519
theorem B10159775 : Blo 658307 10159775 := bstep (se 1 (by rfl) ⟨7619831, by rfl⟩ : syracuseStep 10159775 = 15239663) B15239663
theorem B1116031 : Blo 658307 1116031 := bstep (se 1 (by rfl) ⟨837023, by rfl⟩ : syracuseStep 1116031 = 1674047) B1674047
theorem B2820035 : Blo 658307 2820035 := bstep (se 1 (by rfl) ⟨2115026, by rfl⟩ : syracuseStep 2820035 = 4230053) B4230053
theorem B48302081 : Blo 658307 48302081 := bstep (se 2 (by rfl) ⟨18113280, by rfl⟩ : syracuseStep 48302081 = 36226561) B36226561
theorem B313624925 : Blo 658307 313624925 := bstep (se 3 (by rfl) ⟨58804673, by rfl⟩ : syracuseStep 313624925 = 117609347) B117609347
theorem B1673855 : Blo 658307 1673855 := bstep (se 1 (by rfl) ⟨1255391, by rfl⟩ : syracuseStep 1673855 = 2510783) B2510783
theorem B658367 : Blo 658307 658367 := bstep (se 1 (by rfl) ⟨493775, by rfl⟩ : syracuseStep 658367 = 987551) B987551
theorem B4230103 : Blo 658307 4230103 := bstep (se 1 (by rfl) ⟨3172577, by rfl⟩ : syracuseStep 4230103 = 6345155) B6345155
theorem B2231387 : Blo 658307 2231387 := bstep (se 1 (by rfl) ⟨1673540, by rfl⟩ : syracuseStep 2231387 = 3347081) B3347081
theorem B658623 : Blo 658307 658623 := bstep (se 1 (by rfl) ⟨493967, by rfl⟩ : syracuseStep 658623 = 987935) B987935
theorem B1117435 : Blo 658307 1117435 := bstep (se 1 (by rfl) ⟨838076, by rfl⟩ : syracuseStep 1117435 = 1676153) B1676153
theorem B3018151 : Blo 658307 3018151 := bstep (se 1 (by rfl) ⟨2263613, by rfl⟩ : syracuseStep 3018151 = 4527227) B4527227
theorem B658943 : Blo 658307 658943 := bstep (se 1 (by rfl) ⟨494207, by rfl⟩ : syracuseStep 658943 = 988415) B988415
theorem B659099 : Blo 658307 659099 := bstep (se 1 (by rfl) ⟨494324, by rfl⟩ : syracuseStep 659099 = 988649) B988649
theorem B659663 : Blo 658307 659663 := bstep (se 1 (by rfl) ⟨494747, by rfl⟩ : syracuseStep 659663 = 989495) B989495
theorem B659711 : Blo 658307 659711 := bstep (se 1 (by rfl) ⟨494783, by rfl⟩ : syracuseStep 659711 = 989567) B989567
theorem B659783 : Blo 658307 659783 := bstep (se 1 (by rfl) ⟨494837, by rfl⟩ : syracuseStep 659783 = 989675) B989675
theorem B3576311 : Blo 658307 3576311 := bstep (se 1 (by rfl) ⟨2682233, by rfl⟩ : syracuseStep 3576311 = 5364467) B5364467
theorem B660059 : Blo 658307 660059 := bstep (se 1 (by rfl) ⟨495044, by rfl⟩ : syracuseStep 660059 = 990089) B990089
theorem B2233007 : Blo 658307 2233007 := bstep (se 1 (by rfl) ⟨1674755, by rfl⟩ : syracuseStep 2233007 = 3349511) B3349511
theorem B660415 : Blo 658307 660415 := bstep (se 1 (by rfl) ⟨495311, by rfl⟩ : syracuseStep 660415 = 990623) B990623
theorem B1086443 : Blo 658307 1086443 := bstep (se 1 (by rfl) ⟨814832, by rfl⟩ : syracuseStep 1086443 = 1629665) B1629665
theorem B660527 : Blo 658307 660527 := bstep (se 1 (by rfl) ⟨495395, by rfl⟩ : syracuseStep 660527 = 990791) B990791
theorem B660571 : Blo 658307 660571 := bstep (se 1 (by rfl) ⟨495428, by rfl⟩ : syracuseStep 660571 = 990857) B990857
theorem B3347567 : Blo 658307 3347567 := bstep (se 1 (by rfl) ⟨2510675, by rfl⟩ : syracuseStep 3347567 = 5021351) B5021351
theorem B660647 : Blo 658307 660647 := bstep (se 1 (by rfl) ⟨495485, by rfl⟩ : syracuseStep 660647 = 990971) B990971
theorem B660863 : Blo 658307 660863 := bstep (se 1 (by rfl) ⟨495647, by rfl⟩ : syracuseStep 660863 = 991295) B991295
theorem B660895 : Blo 658307 660895 := bstep (se 1 (by rfl) ⟨495671, by rfl⟩ : syracuseStep 660895 = 991343) B991343
theorem B4756907 : Blo 658307 4756907 := bstep (se 1 (by rfl) ⟨3567680, by rfl⟩ : syracuseStep 4756907 = 7135361) B7135361
theorem B660927 : Blo 658307 660927 := bstep (se 1 (by rfl) ⟨495695, by rfl⟩ : syracuseStep 660927 = 991391) B991391
theorem B988703 : Blo 658307 988703 := bstep (se 1 (by rfl) ⟨741527, by rfl⟩ : syracuseStep 988703 = 1483055) B1483055
theorem B988727 : Blo 658307 988727 := bstep (se 1 (by rfl) ⟨741545, by rfl⟩ : syracuseStep 988727 = 1483091) B1483091
theorem B988847 : Blo 658307 988847 := bstep (se 1 (by rfl) ⟨741635, by rfl⟩ : syracuseStep 988847 = 1483271) B1483271
theorem B2234087 : Blo 658307 2234087 := bstep (se 1 (by rfl) ⟨1675565, by rfl⟩ : syracuseStep 2234087 = 3351131) B3351131
theorem B661415 : Blo 658307 661415 := bstep (se 1 (by rfl) ⟨496061, by rfl⟩ : syracuseStep 661415 = 992123) B992123
theorem B661439 : Blo 658307 661439 := bstep (se 1 (by rfl) ⟨496079, by rfl⟩ : syracuseStep 661439 = 992159) B992159
theorem B661499 : Blo 658307 661499 := bstep (se 1 (by rfl) ⟨496124, by rfl⟩ : syracuseStep 661499 = 992249) B992249
theorem B661551 : Blo 658307 661551 := bstep (se 1 (by rfl) ⟨496163, by rfl⟩ : syracuseStep 661551 = 992327) B992327
theorem B661759 : Blo 658307 661759 := bstep (se 1 (by rfl) ⟨496319, by rfl⟩ : syracuseStep 661759 = 992639) B992639
theorem B2759003 : Blo 658307 2759003 := bstep (se 1 (by rfl) ⟨2069252, by rfl⟩ : syracuseStep 2759003 = 4138505) B4138505
theorem B3348863 : Blo 658307 3348863 := bstep (se 1 (by rfl) ⟨2511647, by rfl⟩ : syracuseStep 3348863 = 5023295) B5023295
theorem B662127 : Blo 658307 662127 := bstep (se 1 (by rfl) ⟨496595, by rfl⟩ : syracuseStep 662127 = 993191) B993191
theorem B4234153 : Blo 658307 4234153 := bstep (se 2 (by rfl) ⟨1587807, by rfl⟩ : syracuseStep 4234153 = 3175615) B3175615
theorem B1481831 : Blo 658307 1481831 := bstep (se 1 (by rfl) ⟨1111373, by rfl⟩ : syracuseStep 1481831 = 2222747) B2222747
theorem B1252513 : Blo 658307 1252513 := bstep (se 2 (by rfl) ⟨469692, by rfl⟩ : syracuseStep 1252513 = 939385) B939385
theorem B1481939 : Blo 658307 1481939 := bstep (se 1 (by rfl) ⟨1111454, by rfl⟩ : syracuseStep 1481939 = 2222909) B2222909
theorem B1482155 : Blo 658307 1482155 := bstep (se 1 (by rfl) ⟨1111616, by rfl⟩ : syracuseStep 1482155 = 2223233) B2223233
theorem B5643827 : Blo 658307 5643827 := bstep (se 1 (by rfl) ⟨4232870, by rfl⟩ : syracuseStep 5643827 = 8465741) B8465741
theorem B7511615 : Blo 658307 7511615 := bstep (se 1 (by rfl) ⟨5633711, by rfl⟩ : syracuseStep 7511615 = 11267423) B11267423
theorem B6365263 : Blo 658307 6365263 := bstep (se 1 (by rfl) ⟨4773947, by rfl⟩ : syracuseStep 6365263 = 9547895) B9547895
theorem B3350807 : Blo 658307 3350807 := bstep (se 1 (by rfl) ⟨2513105, by rfl⟩ : syracuseStep 3350807 = 5026211) B5026211
theorem B1057193 : Blo 658307 1057193 := bstep (se 2 (by rfl) ⟨396447, by rfl⟩ : syracuseStep 1057193 = 792895) B792895
theorem B1483559 : Blo 658307 1483559 := bstep (se 1 (by rfl) ⟨1112669, by rfl⟩ : syracuseStep 1483559 = 2225339) B2225339
theorem B992207 : Blo 658307 992207 := bstep (se 1 (by rfl) ⟨744155, by rfl⟩ : syracuseStep 992207 = 1488311) B1488311
theorem B1254503 : Blo 658307 1254503 := bstep (se 1 (by rfl) ⟨940877, by rfl⟩ : syracuseStep 1254503 = 1881755) B1881755
theorem B1483883 : Blo 658307 1483883 := bstep (se 1 (by rfl) ⟨1112912, by rfl⟩ : syracuseStep 1483883 = 2225825) B2225825
theorem B992633 : Blo 658307 992633 := bstep (se 2 (by rfl) ⟨372237, by rfl⟩ : syracuseStep 992633 = 744475) B744475
theorem B1484711 : Blo 658307 1484711 := bstep (se 1 (by rfl) ⟨1113533, by rfl⟩ : syracuseStep 1484711 = 2227067) B2227067
theorem B1877995 : Blo 658307 1877995 := bstep (se 1 (by rfl) ⟨1408496, by rfl⟩ : syracuseStep 1877995 = 2816993) B2816993
theorem B60827851 : Blo 658307 60827851 := bstep (se 1 (by rfl) ⟨45620888, by rfl⟩ : syracuseStep 60827851 = 91241777) B91241777
theorem B1878223 : Blo 658307 1878223 := bstep (se 1 (by rfl) ⟨1408667, by rfl⟩ : syracuseStep 1878223 = 2817335) B2817335
theorem B2828783 : Blo 658307 2828783 := bstep (se 1 (by rfl) ⟨2121587, by rfl⟩ : syracuseStep 2828783 = 4243175) B4243175
theorem B1583657 : Blo 658307 1583657 := bstep (se 2 (by rfl) ⟨593871, by rfl⟩ : syracuseStep 1583657 = 1187743) B1187743
theorem B1485665 : Blo 658307 1485665 := bstep (se 2 (by rfl) ⟨557124, by rfl⟩ : syracuseStep 1485665 = 1114249) B1114249
theorem B1584137 : Blo 658307 1584137 := bstep (se 2 (by rfl) ⟨594051, by rfl⟩ : syracuseStep 1584137 = 1188103) B1188103
theorem B1126703 : Blo 658307 1126703 := bstep (se 1 (by rfl) ⟨845027, by rfl⟩ : syracuseStep 1126703 = 1690055) B1690055
theorem B1487339 : Blo 658307 1487339 := bstep (se 1 (by rfl) ⟨1115504, by rfl⟩ : syracuseStep 1487339 = 2231009) B2231009
theorem B1487465 : Blo 658307 1487465 := bstep (se 2 (by rfl) ⟨557799, by rfl⟩ : syracuseStep 1487465 = 1115599) B1115599
theorem B1488887 : Blo 658307 1488887 := bstep (se 1 (by rfl) ⟨1116665, by rfl⟩ : syracuseStep 1488887 = 2233331) B2233331
theorem B1489103 : Blo 658307 1489103 := bstep (se 1 (by rfl) ⟨1116827, by rfl⟩ : syracuseStep 1489103 = 2233655) B2233655
theorem B2013779 : Blo 658307 2013779 := bstep (se 1 (by rfl) ⟨1510334, by rfl⟩ : syracuseStep 2013779 = 3020669) B3020669
theorem B1489535 : Blo 658307 1489535 := bstep (se 1 (by rfl) ⟨1117151, by rfl⟩ : syracuseStep 1489535 = 2234303) B2234303
theorem B2505725 : Blo 658307 2505725 := bstep (se 3 (by rfl) ⟨469823, by rfl⟩ : syracuseStep 2505725 = 939647) B939647
theorem B1489967 : Blo 658307 1489967 := bstep (se 1 (by rfl) ⟨1117475, by rfl⟩ : syracuseStep 1489967 = 2234951) B2234951
theorem B1490183 : Blo 658307 1490183 := bstep (se 1 (by rfl) ⟨1117637, by rfl⟩ : syracuseStep 1490183 = 2235275) B2235275
theorem B2507867 : Blo 658307 2507867 := bstep (se 1 (by rfl) ⟨1880900, by rfl⟩ : syracuseStep 2507867 = 3761801) B3761801
theorem B4506785 : Blo 658307 4506785 := bstep (se 2 (by rfl) ⟨1690044, by rfl⟩ : syracuseStep 4506785 = 3380089) B3380089
theorem B1885639 : Blo 658307 1885639 := bstep (se 1 (by rfl) ⟨1414229, by rfl⟩ : syracuseStep 1885639 = 2828459) B2828459
theorem B837479 : Blo 658307 837479 := bstep (se 1 (by rfl) ⟨628109, by rfl⟩ : syracuseStep 837479 = 1256219) B1256219
theorem B12700151 : Blo 658307 12700151 := bstep (se 1 (by rfl) ⟨9525113, by rfl⟩ : syracuseStep 12700151 = 19050227) B19050227
theorem B2543071 : Blo 658307 2543071 := bstep (se 1 (by rfl) ⟨1907303, by rfl⟩ : syracuseStep 2543071 = 3814607) B3814607
theorem B740911 : Blo 658307 740911 := bstep (se 1 (by rfl) ⟨555683, by rfl⟩ : syracuseStep 740911 = 1111367) B1111367
theorem B14438695 : Blo 658307 14438695 := bstep (se 1 (by rfl) ⟨10829021, by rfl⟩ : syracuseStep 14438695 = 21658043) B21658043
theorem B12177935 : Blo 658307 12177935 := bstep (se 1 (by rfl) ⟨9133451, by rfl⟩ : syracuseStep 12177935 = 18266903) B18266903
theorem B742171 : Blo 658307 742171 := bstep (se 1 (by rfl) ⟨556628, by rfl⟩ : syracuseStep 742171 = 1113257) B1113257
theorem B19321825 : Blo 658307 19321825 := bstep (se 2 (by rfl) ⟨7245684, by rfl⟩ : syracuseStep 19321825 = 14491369) B14491369
theorem B939055 : Blo 658307 939055 := bstep (se 1 (by rfl) ⟨704291, by rfl⟩ : syracuseStep 939055 = 1408583) B1408583
theorem B742783 : Blo 658307 742783 := bstep (se 1 (by rfl) ⟨557087, by rfl⟩ : syracuseStep 742783 = 1114175) B1114175
theorem B4281947 : Blo 658307 4281947 := bstep (se 1 (by rfl) ⟨3211460, by rfl⟩ : syracuseStep 4281947 = 6422921) B6422921
theorem B2512559 : Blo 658307 2512559 := bstep (se 1 (by rfl) ⟨1884419, by rfl⟩ : syracuseStep 2512559 = 3768839) B3768839
theorem B15292871 : Blo 658307 15292871 := bstep (se 1 (by rfl) ⟨11469653, by rfl⟩ : syracuseStep 15292871 = 22939307) B22939307
theorem B12671477 : Blo 658307 12671477 := bstep (se 5 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 12671477 = 1187951) B1187951
theorem B2383643 : Blo 658307 2383643 := bstep (se 1 (by rfl) ⟨1787732, by rfl⟩ : syracuseStep 2383643 = 3575465) B3575465
theorem B7135703 : Blo 658307 7135703 := bstep (se 1 (by rfl) ⟨5351777, by rfl⟩ : syracuseStep 7135703 = 10703555) B10703555
theorem B1335935 : Blo 658307 1335935 := bstep (se 1 (by rfl) ⟨1001951, by rfl⟩ : syracuseStep 1335935 = 2003903) B2003903
theorem B8447287 : Blo 658307 8447287 := bstep (se 1 (by rfl) ⟨6335465, by rfl⟩ : syracuseStep 8447287 = 12670931) B12670931
theorem B3335579 : Blo 658307 3335579 := bstep (se 1 (by rfl) ⟨2501684, by rfl⟩ : syracuseStep 3335579 = 5003369) B5003369
theorem B7334587 : Blo 658307 7334587 := bstep (se 1 (by rfl) ⟨5500940, by rfl⟩ : syracuseStep 7334587 = 11001881) B11001881
theorem B9497321 : Blo 658307 9497321 := bstep (se 2 (by rfl) ⟨3561495, by rfl⟩ : syracuseStep 9497321 = 7122991) B7122991
theorem B2223017 : Blo 658307 2223017 := bstep (se 2 (by rfl) ⟨833631, by rfl⟩ : syracuseStep 2223017 = 1667263) B1667263
theorem B2812961 : Blo 658307 2812961 := bstep (se 2 (by rfl) ⟨1054860, by rfl⟩ : syracuseStep 2812961 = 2109721) B2109721
theorem B5073977 : Blo 658307 5073977 := bstep (se 2 (by rfl) ⟨1902741, by rfl⟩ : syracuseStep 5073977 = 3805483) B3805483
theorem B7499951 : Blo 658307 7499951 := bstep (se 1 (by rfl) ⟨5624963, by rfl⟩ : syracuseStep 7499951 = 11249927) B11249927
theorem B1667911 : Blo 658307 1667911 := bstep (se 1 (by rfl) ⟨1250933, by rfl⟩ : syracuseStep 1667911 = 2501867) B2501867
theorem B1668073 : Blo 658307 1668073 := bstep (se 2 (by rfl) ⟨625527, by rfl⟩ : syracuseStep 1668073 = 1251055) B1251055
theorem B3339305 : Blo 658307 3339305 := bstep (se 2 (by rfl) ⟨1252239, by rfl⟩ : syracuseStep 3339305 = 2504479) B2504479
theorem B281474129 : Blo 658307 281474129 := bstep (se 2 (by rfl) ⟨105552798, by rfl⟩ : syracuseStep 281474129 = 211105597) B211105597
theorem B1406207 : Blo 658307 1406207 := bstep (se 1 (by rfl) ⟨1054655, by rfl⟩ : syracuseStep 1406207 = 2109311) B2109311
theorem B1111657 : Blo 658307 1111657 := bstep (se 2 (by rfl) ⟨416871, by rfl⟩ : syracuseStep 1111657 = 833743) B833743
theorem B1670827 : Blo 658307 1670827 := bstep (se 1 (by rfl) ⟨1253120, by rfl⟩ : syracuseStep 1670827 = 2506241) B2506241
theorem B2227931 : Blo 658307 2227931 := bstep (se 1 (by rfl) ⟨1670948, by rfl⟩ : syracuseStep 2227931 = 3341897) B3341897
theorem B8487017 : Blo 658307 8487017 := bstep (se 2 (by rfl) ⟨3182631, by rfl⟩ : syracuseStep 8487017 = 6365263) B6365263
theorem B1671911 : Blo 658307 1671911 := bstep (se 1 (by rfl) ⟨1253933, by rfl⟩ : syracuseStep 1671911 = 2507867) B2507867
theorem B2229119 : Blo 658307 2229119 := bstep (se 1 (by rfl) ⟨1671839, by rfl⟩ : syracuseStep 2229119 = 3343679) B3343679
theorem B1115903 : Blo 658307 1115903 := bstep (se 1 (by rfl) ⟨836927, by rfl⟩ : syracuseStep 1115903 = 1673855) B1673855
theorem B81103801 : Blo 658307 81103801 := bstep (se 2 (by rfl) ⟨30413925, by rfl⟩ : syracuseStep 81103801 = 60827851) B60827851
theorem B724295 : Blo 658307 724295 := bstep (se 1 (by rfl) ⟨543221, by rfl⟩ : syracuseStep 724295 = 1086443) B1086443
theorem B2231711 : Blo 658307 2231711 := bstep (se 1 (by rfl) ⟨1673783, by rfl⟩ : syracuseStep 2231711 = 3347567) B3347567
theorem B29429365 : Blo 658307 29429365 := bstep (se 5 (by rfl) ⟨1379501, by rfl⟩ : syracuseStep 29429365 = 2759003) B2759003
theorem B659135 : Blo 658307 659135 := bstep (se 1 (by rfl) ⟨494351, by rfl⟩ : syracuseStep 659135 = 988703) B988703
theorem B659151 : Blo 658307 659151 := bstep (se 1 (by rfl) ⟨494363, by rfl⟩ : syracuseStep 659151 = 988727) B988727
theorem B2854631 : Blo 658307 2854631 := bstep (se 1 (by rfl) ⟨2140973, by rfl⟩ : syracuseStep 2854631 = 4281947) B4281947
theorem B659231 : Blo 658307 659231 := bstep (se 1 (by rfl) ⟨494423, by rfl⟩ : syracuseStep 659231 = 988847) B988847
theorem B1675039 : Blo 658307 1675039 := bstep (se 1 (by rfl) ⟨1256279, by rfl⟩ : syracuseStep 1675039 = 2512559) B2512559
theorem B5640137 : Blo 658307 5640137 := bstep (se 2 (by rfl) ⟨2115051, by rfl⟩ : syracuseStep 5640137 = 4230103) B4230103
theorem B2232575 : Blo 658307 2232575 := bstep (se 1 (by rfl) ⟨1674431, by rfl⟩ : syracuseStep 2232575 = 3348863) B3348863
theorem B10195247 : Blo 658307 10195247 := bstep (se 1 (by rfl) ⟨7646435, by rfl⟩ : syracuseStep 10195247 = 15292871) B15292871
theorem B987881 : Blo 658307 987881 := bstep (se 2 (by rfl) ⟨370455, by rfl⟩ : syracuseStep 987881 = 740911) B740911
theorem B987887 : Blo 658307 987887 := bstep (se 1 (by rfl) ⟨740915, by rfl⟩ : syracuseStep 987887 = 1481831) B1481831
theorem B987959 : Blo 658307 987959 := bstep (se 1 (by rfl) ⟨740969, by rfl⟩ : syracuseStep 987959 = 1481939) B1481939
theorem B2233277 : Blo 658307 2233277 := bstep (se 3 (by rfl) ⟨418739, by rfl⟩ : syracuseStep 2233277 = 837479) B837479
theorem B988103 : Blo 658307 988103 := bstep (se 1 (by rfl) ⟨741077, by rfl⟩ : syracuseStep 988103 = 1482155) B1482155
theorem B2233871 : Blo 658307 2233871 := bstep (se 1 (by rfl) ⟨1675403, by rfl⟩ : syracuseStep 2233871 = 3350807) B3350807
theorem B4757135 : Blo 658307 4757135 := bstep (se 1 (by rfl) ⟨3567851, by rfl⟩ : syracuseStep 4757135 = 7135703) B7135703
theorem B890623 : Blo 658307 890623 := bstep (se 1 (by rfl) ⟨667967, by rfl⟩ : syracuseStep 890623 = 1335935) B1335935
theorem B989039 : Blo 658307 989039 := bstep (se 1 (by rfl) ⟨741779, by rfl⟩ : syracuseStep 989039 = 1483559) B1483559
theorem B661471 : Blo 658307 661471 := bstep (se 1 (by rfl) ⟨496103, by rfl⟩ : syracuseStep 661471 = 992207) B992207
theorem B989255 : Blo 658307 989255 := bstep (se 1 (by rfl) ⟨741941, by rfl⟩ : syracuseStep 989255 = 1483883) B1483883
theorem B661755 : Blo 658307 661755 := bstep (se 1 (by rfl) ⟨496316, by rfl⟩ : syracuseStep 661755 = 992633) B992633
theorem B989561 : Blo 658307 989561 := bstep (se 2 (by rfl) ⟨371085, by rfl⟩ : syracuseStep 989561 = 742171) B742171
theorem B989807 : Blo 658307 989807 := bstep (se 1 (by rfl) ⟨742355, by rfl⟩ : syracuseStep 989807 = 1484711) B1484711
theorem B25762433 : Blo 658307 25762433 := bstep (se 2 (by rfl) ⟨9660912, by rfl⟩ : syracuseStep 25762433 = 19321825) B19321825
theorem B1252073 : Blo 658307 1252073 := bstep (se 2 (by rfl) ⟨469527, by rfl⟩ : syracuseStep 1252073 = 939055) B939055
theorem B1055771 : Blo 658307 1055771 := bstep (se 1 (by rfl) ⟨791828, by rfl⟩ : syracuseStep 1055771 = 1583657) B1583657
theorem B6331547 : Blo 658307 6331547 := bstep (se 1 (by rfl) ⟨4748660, by rfl⟩ : syracuseStep 6331547 = 9497321) B9497321
theorem B990377 : Blo 658307 990377 := bstep (se 2 (by rfl) ⟨371391, by rfl⟩ : syracuseStep 990377 = 742783) B742783
theorem B990443 : Blo 658307 990443 := bstep (se 1 (by rfl) ⟨742832, by rfl⟩ : syracuseStep 990443 = 1485665) B1485665
theorem B1482011 : Blo 658307 1482011 := bstep (se 1 (by rfl) ⟨1111508, by rfl⟩ : syracuseStep 1482011 = 2223017) B2223017
theorem B1056091 : Blo 658307 1056091 := bstep (se 1 (by rfl) ⟨792068, by rfl⟩ : syracuseStep 1056091 = 1584137) B1584137
theorem B1875307 : Blo 658307 1875307 := bstep (se 1 (by rfl) ⟨1406480, by rfl⟩ : syracuseStep 1875307 = 2812961) B2812961
theorem B3382651 : Blo 658307 3382651 := bstep (se 1 (by rfl) ⟨2536988, by rfl⟩ : syracuseStep 3382651 = 5073977) B5073977
theorem B1482209 : Blo 658307 1482209 := bstep (se 2 (by rfl) ⟨555828, by rfl⟩ : syracuseStep 1482209 = 1111657) B1111657
theorem B991559 : Blo 658307 991559 := bstep (se 1 (by rfl) ⟨743669, by rfl⟩ : syracuseStep 991559 = 1487339) B1487339
theorem B991643 : Blo 658307 991643 := bstep (se 1 (by rfl) ⟨743732, by rfl⟩ : syracuseStep 991643 = 1487465) B1487465
theorem B5645537 : Blo 658307 5645537 := bstep (se 2 (by rfl) ⟨2117076, by rfl⟩ : syracuseStep 5645537 = 4234153) B4234153
theorem B992591 : Blo 658307 992591 := bstep (se 1 (by rfl) ⟨744443, by rfl⟩ : syracuseStep 992591 = 1488887) B1488887
theorem B992735 : Blo 658307 992735 := bstep (se 1 (by rfl) ⟨744551, by rfl⟩ : syracuseStep 992735 = 1489103) B1489103
theorem B993023 : Blo 658307 993023 := bstep (se 1 (by rfl) ⟨744767, by rfl⟩ : syracuseStep 993023 = 1489535) B1489535
theorem B993311 : Blo 658307 993311 := bstep (se 1 (by rfl) ⟨744983, by rfl⟩ : syracuseStep 993311 = 1489967) B1489967
theorem B993455 : Blo 658307 993455 := bstep (se 1 (by rfl) ⟨745091, by rfl⟩ : syracuseStep 993455 = 1490183) B1490183
theorem B1485287 : Blo 658307 1485287 := bstep (se 1 (by rfl) ⟨1113965, by rfl⟩ : syracuseStep 1485287 = 2227931) B2227931
theorem B1878815 : Blo 658307 1878815 := bstep (se 1 (by rfl) ⟨1409111, by rfl⟩ : syracuseStep 1878815 = 2818223) B2818223
theorem B1880023 : Blo 658307 1880023 := bstep (se 1 (by rfl) ⟨1410017, by rfl⟩ : syracuseStep 1880023 = 2820035) B2820035
theorem B8466767 : Blo 658307 8466767 := bstep (se 1 (by rfl) ⟨6350075, by rfl⟩ : syracuseStep 8466767 = 12700151) B12700151
theorem B1487591 : Blo 658307 1487591 := bstep (se 1 (by rfl) ⟨1115693, by rfl⟩ : syracuseStep 1487591 = 2231387) B2231387
theorem B1488041 : Blo 658307 1488041 := bstep (se 2 (by rfl) ⟨558015, by rfl⟩ : syracuseStep 1488041 = 1116031) B1116031
theorem B2503993 : Blo 658307 2503993 := bstep (se 2 (by rfl) ⟨938997, by rfl⟩ : syracuseStep 2503993 = 1877995) B1877995
theorem B2504297 : Blo 658307 2504297 := bstep (se 2 (by rfl) ⟨939111, by rfl⟩ : syracuseStep 2504297 = 1878223) B1878223
theorem B1488671 : Blo 658307 1488671 := bstep (se 1 (by rfl) ⟨1116503, by rfl⟩ : syracuseStep 1488671 = 2233007) B2233007
theorem B3749885 : Blo 658307 3749885 := bstep (se 3 (by rfl) ⟨703103, by rfl⟩ : syracuseStep 3749885 = 1406207) B1406207
theorem B9779449 : Blo 658307 9779449 := bstep (se 2 (by rfl) ⟨3667293, by rfl⟩ : syracuseStep 9779449 = 7334587) B7334587
theorem B1489391 : Blo 658307 1489391 := bstep (se 1 (by rfl) ⟨1117043, by rfl⟩ : syracuseStep 1489391 = 2234087) B2234087
theorem B1489913 : Blo 658307 1489913 := bstep (se 2 (by rfl) ⟨558717, by rfl⟩ : syracuseStep 1489913 = 1117435) B1117435
theorem B3390761 : Blo 658307 3390761 := bstep (se 2 (by rfl) ⟨1271535, by rfl⟩ : syracuseStep 3390761 = 2543071) B2543071
theorem B1589095 : Blo 658307 1589095 := bstep (se 1 (by rfl) ⟨1191821, by rfl⟩ : syracuseStep 1589095 = 2383643) B2383643
theorem B704795 : Blo 658307 704795 := bstep (se 1 (by rfl) ⟨528596, by rfl⟩ : syracuseStep 704795 = 1057193) B1057193
theorem B19251593 : Blo 658307 19251593 := bstep (se 2 (by rfl) ⟨7219347, by rfl⟩ : syracuseStep 19251593 = 14438695) B14438695
theorem B836335 : Blo 658307 836335 := bstep (se 1 (by rfl) ⟨627251, by rfl⟩ : syracuseStep 836335 = 1254503) B1254503
theorem B1885855 : Blo 658307 1885855 := bstep (se 1 (by rfl) ⟨1414391, by rfl⟩ : syracuseStep 1885855 = 2828783) B2828783
theorem B4999967 : Blo 658307 4999967 := bstep (se 1 (by rfl) ⟨3749975, by rfl⟩ : syracuseStep 4999967 = 7499951) B7499951
theorem B187649419 : Blo 658307 187649419 := bstep (se 1 (by rfl) ⟨140737064, by rfl⟩ : syracuseStep 187649419 = 281474129) B281474129
theorem B2381251 : Blo 658307 2381251 := bstep (se 1 (by rfl) ⟨1785938, by rfl⟩ : syracuseStep 2381251 = 3571877) B3571877
theorem B3004523 : Blo 658307 3004523 := bstep (se 1 (by rfl) ⟨2253392, by rfl⟩ : syracuseStep 3004523 = 4506785) B4506785
theorem B6773183 : Blo 658307 6773183 := bstep (se 1 (by rfl) ⟨5079887, by rfl⟩ : syracuseStep 6773183 = 10159775) B10159775
theorem B32201387 : Blo 658307 32201387 := bstep (se 1 (by rfl) ⟨24151040, by rfl⟩ : syracuseStep 32201387 = 48302081) B48302081
theorem B209083283 : Blo 658307 209083283 := bstep (se 1 (by rfl) ⟨156812462, by rfl⟩ : syracuseStep 209083283 = 313624925) B313624925
theorem B11263049 : Blo 658307 11263049 := bstep (se 2 (by rfl) ⟨4223643, by rfl⟩ : syracuseStep 11263049 = 8447287) B8447287
theorem B2514185 : Blo 658307 2514185 := bstep (se 2 (by rfl) ⟨942819, by rfl⟩ : syracuseStep 2514185 = 1885639) B1885639
theorem B2384207 : Blo 658307 2384207 := bstep (se 1 (by rfl) ⟨1788155, by rfl⟩ : syracuseStep 2384207 = 3576311) B3576311
theorem B8118623 : Blo 658307 8118623 := bstep (se 1 (by rfl) ⟨6088967, by rfl⟩ : syracuseStep 8118623 = 12177935) B12177935
theorem B3171271 : Blo 658307 3171271 := bstep (se 1 (by rfl) ⟨2378453, by rfl⟩ : syracuseStep 3171271 = 4756907) B4756907
theorem B8447651 : Blo 658307 8447651 := bstep (se 1 (by rfl) ⟨6335738, by rfl⟩ : syracuseStep 8447651 = 12671477) B12671477
theorem B4024201 : Blo 658307 4024201 := bstep (se 2 (by rfl) ⟨1509075, by rfl⟩ : syracuseStep 4024201 = 3018151) B3018151
theorem B3762551 : Blo 658307 3762551 := bstep (se 1 (by rfl) ⟨2821913, by rfl⟩ : syracuseStep 3762551 = 5643827) B5643827
theorem B5007743 : Blo 658307 5007743 := bstep (se 1 (by rfl) ⟨3755807, by rfl⟩ : syracuseStep 5007743 = 7511615) B7511615
theorem B2223719 : Blo 658307 2223719 := bstep (se 1 (by rfl) ⟨1667789, by rfl⟩ : syracuseStep 2223719 = 3335579) B3335579
theorem B2223881 : Blo 658307 2223881 := bstep (se 2 (by rfl) ⟨833955, by rfl⟩ : syracuseStep 2223881 = 1667911) B1667911
theorem B2224097 : Blo 658307 2224097 := bstep (se 2 (by rfl) ⟨834036, by rfl⟩ : syracuseStep 2224097 = 1668073) B1668073
theorem B5370077 : Blo 658307 5370077 := bstep (se 3 (by rfl) ⟨1006889, by rfl⟩ : syracuseStep 5370077 = 2013779) B2013779
theorem B751135 : Blo 658307 751135 := bstep (se 1 (by rfl) ⟨563351, by rfl⟩ : syracuseStep 751135 = 1126703) B1126703
theorem B2226203 : Blo 658307 2226203 := bstep (se 1 (by rfl) ⟨1669652, by rfl⟩ : syracuseStep 2226203 = 3339305) B3339305
theorem B1670017 : Blo 658307 1670017 := bstep (se 2 (by rfl) ⟨626256, by rfl⟩ : syracuseStep 1670017 = 1252513) B1252513
theorem B1670483 : Blo 658307 1670483 := bstep (se 1 (by rfl) ⟨1252862, by rfl⟩ : syracuseStep 1670483 = 2505725) B2505725
theorem B2227769 : Blo 658307 2227769 := bstep (se 2 (by rfl) ⟨835413, by rfl⟩ : syracuseStep 2227769 = 1670827) B1670827
theorem B1114607 : Blo 658307 1114607 := bstep (se 1 (by rfl) ⟨835955, by rfl⟩ : syracuseStep 1114607 = 1671911) B1671911
theorem B1115113 : Blo 658307 1115113 := bstep (se 2 (by rfl) ⟨418167, by rfl⟩ : syracuseStep 1115113 = 836335) B836335
theorem B4228361 : Blo 658307 4228361 := bstep (se 2 (by rfl) ⟨1585635, by rfl⟩ : syracuseStep 4228361 = 3171271) B3171271
theorem B1903087 : Blo 658307 1903087 := bstep (se 1 (by rfl) ⟨1427315, by rfl⟩ : syracuseStep 1903087 = 2854631) B2854631
theorem B658587 : Blo 658307 658587 := bstep (se 1 (by rfl) ⟨493940, by rfl⟩ : syracuseStep 658587 = 987881) B987881
theorem B658591 : Blo 658307 658591 := bstep (se 1 (by rfl) ⟨493943, by rfl⟩ : syracuseStep 658591 = 987887) B987887
theorem B658639 : Blo 658307 658639 := bstep (se 1 (by rfl) ⟨493979, by rfl⟩ : syracuseStep 658639 = 987959) B987959
theorem B658735 : Blo 658307 658735 := bstep (se 1 (by rfl) ⟨494051, by rfl⟩ : syracuseStep 658735 = 988103) B988103
theorem B659359 : Blo 658307 659359 := bstep (se 1 (by rfl) ⟨494519, by rfl⟩ : syracuseStep 659359 = 989039) B989039
theorem B108138401 : Blo 658307 108138401 := bstep (se 2 (by rfl) ⟨40551900, by rfl⟩ : syracuseStep 108138401 = 81103801) B81103801
theorem B659503 : Blo 658307 659503 := bstep (se 1 (by rfl) ⟨494627, by rfl⟩ : syracuseStep 659503 = 989255) B989255
theorem B2003015 : Blo 658307 2003015 := bstep (se 1 (by rfl) ⟨1502261, by rfl⟩ : syracuseStep 2003015 = 3004523) B3004523
theorem B659707 : Blo 658307 659707 := bstep (se 1 (by rfl) ⟨494780, by rfl⟩ : syracuseStep 659707 = 989561) B989561
theorem B12685693 : Blo 658307 12685693 := bstep (se 3 (by rfl) ⟨2378567, by rfl⟩ : syracuseStep 12685693 = 4757135) B4757135
theorem B659871 : Blo 658307 659871 := bstep (se 1 (by rfl) ⟨494903, by rfl⟩ : syracuseStep 659871 = 989807) B989807
theorem B21467591 : Blo 658307 21467591 := bstep (se 1 (by rfl) ⟨16100693, by rfl⟩ : syracuseStep 21467591 = 32201387) B32201387
theorem B7508699 : Blo 658307 7508699 := bstep (se 1 (by rfl) ⟨5631524, by rfl⟩ : syracuseStep 7508699 = 11263049) B11263049
theorem B660251 : Blo 658307 660251 := bstep (se 1 (by rfl) ⟨495188, by rfl⟩ : syracuseStep 660251 = 990377) B990377
theorem B660295 : Blo 658307 660295 := bstep (se 1 (by rfl) ⟨495221, by rfl⟩ : syracuseStep 660295 = 990443) B990443
theorem B1676123 : Blo 658307 1676123 := bstep (se 1 (by rfl) ⟨1257092, by rfl⟩ : syracuseStep 1676123 = 2514185) B2514185
theorem B988007 : Blo 658307 988007 := bstep (se 1 (by rfl) ⟨741005, by rfl⟩ : syracuseStep 988007 = 1482011) B1482011
theorem B988139 : Blo 658307 988139 := bstep (se 1 (by rfl) ⟨741104, by rfl⟩ : syracuseStep 988139 = 1482209) B1482209
theorem B2233385 : Blo 658307 2233385 := bstep (se 2 (by rfl) ⟨837519, by rfl⟩ : syracuseStep 2233385 = 1675039) B1675039
theorem B661039 : Blo 658307 661039 := bstep (se 1 (by rfl) ⟨495779, by rfl⟩ : syracuseStep 661039 = 991559) B991559
theorem B5412415 : Blo 658307 5412415 := bstep (se 1 (by rfl) ⟨4059311, by rfl⟩ : syracuseStep 5412415 = 8118623) B8118623
theorem B661095 : Blo 658307 661095 := bstep (se 1 (by rfl) ⟨495821, by rfl⟩ : syracuseStep 661095 = 991643) B991643
theorem B661727 : Blo 658307 661727 := bstep (se 1 (by rfl) ⟨496295, by rfl⟩ : syracuseStep 661727 = 992591) B992591
theorem B661823 : Blo 658307 661823 := bstep (se 1 (by rfl) ⟨496367, by rfl⟩ : syracuseStep 661823 = 992735) B992735
theorem B662015 : Blo 658307 662015 := bstep (se 1 (by rfl) ⟨496511, by rfl⟩ : syracuseStep 662015 = 993023) B993023
theorem B662207 : Blo 658307 662207 := bstep (se 1 (by rfl) ⟨496655, by rfl⟩ : syracuseStep 662207 = 993311) B993311
theorem B662303 : Blo 658307 662303 := bstep (se 1 (by rfl) ⟨496727, by rfl⟩ : syracuseStep 662303 = 993455) B993455
theorem B990191 : Blo 658307 990191 := bstep (se 1 (by rfl) ⟨742643, by rfl⟩ : syracuseStep 990191 = 1485287) B1485287
theorem B1187497 : Blo 658307 1187497 := bstep (se 2 (by rfl) ⟨445311, by rfl⟩ : syracuseStep 1187497 = 890623) B890623
theorem B1482479 : Blo 658307 1482479 := bstep (se 1 (by rfl) ⟨1111859, by rfl⟩ : syracuseStep 1482479 = 2223719) B2223719
theorem B1482587 : Blo 658307 1482587 := bstep (se 1 (by rfl) ⟨1111940, by rfl⟩ : syracuseStep 1482587 = 2223881) B2223881
theorem B1482731 : Blo 658307 1482731 := bstep (se 1 (by rfl) ⟨1112048, by rfl⟩ : syracuseStep 1482731 = 2224097) B2224097
theorem B3580051 : Blo 658307 3580051 := bstep (se 1 (by rfl) ⟨2685038, by rfl⟩ : syracuseStep 3580051 = 5370077) B5370077
theorem B5644511 : Blo 658307 5644511 := bstep (se 1 (by rfl) ⟨4233383, by rfl⟩ : syracuseStep 5644511 = 8466767) B8466767
theorem B991727 : Blo 658307 991727 := bstep (se 1 (by rfl) ⟨743795, by rfl⟩ : syracuseStep 991727 = 1487591) B1487591
theorem B992027 : Blo 658307 992027 := bstep (se 1 (by rfl) ⟨744020, by rfl⟩ : syracuseStep 992027 = 1488041) B1488041
theorem B992447 : Blo 658307 992447 := bstep (se 1 (by rfl) ⟨744335, by rfl⟩ : syracuseStep 992447 = 1488671) B1488671
theorem B2499923 : Blo 658307 2499923 := bstep (se 1 (by rfl) ⟨1874942, by rfl⟩ : syracuseStep 2499923 = 3749885) B3749885
theorem B1484135 : Blo 658307 1484135 := bstep (se 1 (by rfl) ⟨1113101, by rfl⟩ : syracuseStep 1484135 = 2226203) B2226203
theorem B992927 : Blo 658307 992927 := bstep (se 1 (by rfl) ⟨744695, by rfl⟩ : syracuseStep 992927 = 1489391) B1489391
theorem B2500409 : Blo 658307 2500409 := bstep (se 2 (by rfl) ⟨937653, by rfl⟩ : syracuseStep 2500409 = 1875307) B1875307
theorem B993275 : Blo 658307 993275 := bstep (se 1 (by rfl) ⟨744956, by rfl⟩ : syracuseStep 993275 = 1489913) B1489913
theorem B1485179 : Blo 658307 1485179 := bstep (se 1 (by rfl) ⟨1113884, by rfl⟩ : syracuseStep 1485179 = 2227769) B2227769
theorem B1486079 : Blo 658307 1486079 := bstep (se 1 (by rfl) ⟨1114559, by rfl⟩ : syracuseStep 1486079 = 2229119) B2229119
theorem B1879453 : Blo 658307 1879453 := bstep (se 3 (by rfl) ⟨352397, by rfl⟩ : syracuseStep 1879453 = 704795) B704795
theorem B1487807 : Blo 658307 1487807 := bstep (se 1 (by rfl) ⟨1115855, by rfl⟩ : syracuseStep 1487807 = 2231711) B2231711
theorem B1488383 : Blo 658307 1488383 := bstep (se 1 (by rfl) ⟨1116287, by rfl⟩ : syracuseStep 1488383 = 2232575) B2232575
theorem B6796831 : Blo 658307 6796831 := bstep (se 1 (by rfl) ⟨5097623, by rfl⟩ : syracuseStep 6796831 = 10195247) B10195247
theorem B1488851 : Blo 658307 1488851 := bstep (se 1 (by rfl) ⟨1116638, by rfl⟩ : syracuseStep 1488851 = 2233277) B2233277
theorem B1489247 : Blo 658307 1489247 := bstep (se 1 (by rfl) ⟨1116935, by rfl⟩ : syracuseStep 1489247 = 2233871) B2233871
theorem B834715 : Blo 658307 834715 := bstep (se 1 (by rfl) ⟨626036, by rfl⟩ : syracuseStep 834715 = 1252073) B1252073
theorem B250199225 : Blo 658307 250199225 := bstep (se 2 (by rfl) ⟨93824709, by rfl⟩ : syracuseStep 250199225 = 187649419) B187649419
theorem B703847 : Blo 658307 703847 := bstep (se 1 (by rfl) ⟨527885, by rfl⟩ : syracuseStep 703847 = 1055771) B1055771
theorem B39239153 : Blo 658307 39239153 := bstep (se 2 (by rfl) ⟨14714682, by rfl⟩ : syracuseStep 39239153 = 29429365) B29429365
theorem B2506697 : Blo 658307 2506697 := bstep (se 2 (by rfl) ⟨940011, by rfl⟩ : syracuseStep 2506697 = 1880023) B1880023
theorem B1589471 : Blo 658307 1589471 := bstep (se 1 (by rfl) ⟨1192103, by rfl⟩ : syracuseStep 1589471 = 2384207) B2384207
theorem B2508367 : Blo 658307 2508367 := bstep (se 1 (by rfl) ⟨1881275, by rfl⟩ : syracuseStep 2508367 = 3762551) B3762551
theorem B68699821 : Blo 658307 68699821 := bstep (se 3 (by rfl) ⟨12881216, by rfl⟩ : syracuseStep 68699821 = 25762433) B25762433
theorem B18040805 : Blo 658307 18040805 := bstep (se 4 (by rfl) ⟨1691325, by rfl⟩ : syracuseStep 18040805 = 3382651) B3382651
theorem B1001513 : Blo 658307 1001513 := bstep (se 2 (by rfl) ⟨375567, by rfl⟩ : syracuseStep 1001513 = 751135) B751135
theorem B2118793 : Blo 658307 2118793 := bstep (se 2 (by rfl) ⟨794547, by rfl⟩ : syracuseStep 2118793 = 1589095) B1589095
theorem B5658011 : Blo 658307 5658011 := bstep (se 1 (by rfl) ⟨4243508, by rfl⟩ : syracuseStep 5658011 = 8487017) B8487017
theorem B12834395 : Blo 658307 12834395 := bstep (se 1 (by rfl) ⟨9625796, by rfl⟩ : syracuseStep 12834395 = 19251593) B19251593
theorem B743935 : Blo 658307 743935 := bstep (se 1 (by rfl) ⟨557951, by rfl⟩ : syracuseStep 743935 = 1115903) B1115903
theorem B3333311 : Blo 658307 3333311 := bstep (se 1 (by rfl) ⟨2499983, by rfl⟩ : syracuseStep 3333311 = 4999967) B4999967
theorem B2514473 : Blo 658307 2514473 := bstep (se 2 (by rfl) ⟨942927, by rfl⟩ : syracuseStep 2514473 = 1885855) B1885855
theorem B5365601 : Blo 658307 5365601 := bstep (se 2 (by rfl) ⟨2012100, by rfl⟩ : syracuseStep 5365601 = 4024201) B4024201
theorem B3760091 : Blo 658307 3760091 := bstep (se 1 (by rfl) ⟨2820068, by rfl⟩ : syracuseStep 3760091 = 5640137) B5640137
theorem B4515455 : Blo 658307 4515455 := bstep (se 1 (by rfl) ⟨3386591, by rfl⟩ : syracuseStep 4515455 = 6773183) B6773183
theorem B139388855 : Blo 658307 139388855 := bstep (se 1 (by rfl) ⟨104541641, by rfl⟩ : syracuseStep 139388855 = 209083283) B209083283
theorem B4221031 : Blo 658307 4221031 := bstep (se 1 (by rfl) ⟨3165773, by rfl⟩ : syracuseStep 4221031 = 6331547) B6331547
theorem B3763691 : Blo 658307 3763691 := bstep (se 1 (by rfl) ⟨2822768, by rfl⟩ : syracuseStep 3763691 = 5645537) B5645537
theorem B5631767 : Blo 658307 5631767 := bstep (se 1 (by rfl) ⟨4223825, by rfl⟩ : syracuseStep 5631767 = 8447651) B8447651
theorem B3338495 : Blo 658307 3338495 := bstep (se 1 (by rfl) ⟨2503871, by rfl⟩ : syracuseStep 3338495 = 5007743) B5007743
theorem B3338657 : Blo 658307 3338657 := bstep (se 2 (by rfl) ⟨1251996, by rfl⟩ : syracuseStep 3338657 = 2503993) B2503993
theorem B3175001 : Blo 658307 3175001 := bstep (se 2 (by rfl) ⟨1190625, by rfl⟩ : syracuseStep 3175001 = 2381251) B2381251
theorem B5010173 : Blo 658307 5010173 := bstep (se 3 (by rfl) ⟨939407, by rfl⟩ : syracuseStep 5010173 = 1878815) B1878815
theorem B13039265 : Blo 658307 13039265 := bstep (se 2 (by rfl) ⟨4889724, by rfl⟩ : syracuseStep 13039265 = 9779449) B9779449
theorem B9042029 : Blo 658307 9042029 := bstep (se 3 (by rfl) ⟨1695380, by rfl⟩ : syracuseStep 9042029 = 3390761) B3390761
theorem B1931453 : Blo 658307 1931453 := bstep (se 3 (by rfl) ⟨362147, by rfl⟩ : syracuseStep 1931453 = 724295) B724295
theorem B1669531 : Blo 658307 1669531 := bstep (se 1 (by rfl) ⟨1252148, by rfl⟩ : syracuseStep 1669531 = 2504297) B2504297
theorem B2226689 : Blo 658307 2226689 := bstep (se 2 (by rfl) ⟨835008, by rfl⟩ : syracuseStep 2226689 = 1670017) B1670017
theorem B1408121 : Blo 658307 1408121 := bstep (se 2 (by rfl) ⟨528045, by rfl⟩ : syracuseStep 1408121 = 1056091) B1056091
theorem B1113655 : Blo 658307 1113655 := bstep (se 1 (by rfl) ⟨835241, by rfl⟩ : syracuseStep 1113655 = 1670483) B1670483
theorem B5341373 : Blo 658307 5341373 := bstep (se 3 (by rfl) ⟨1001507, by rfl⟩ : syracuseStep 5341373 = 2003015) B2003015
theorem B2818907 : Blo 658307 2818907 := bstep (se 1 (by rfl) ⟨2114180, by rfl⟩ : syracuseStep 2818907 = 4228361) B4228361
theorem B12027203 : Blo 658307 12027203 := bstep (se 1 (by rfl) ⟨9020402, by rfl⟩ : syracuseStep 12027203 = 18040805) B18040805
theorem B3344489 : Blo 658307 3344489 := bstep (se 2 (by rfl) ⟨1254183, by rfl⟩ : syracuseStep 3344489 = 2508367) B2508367
theorem B72092267 : Blo 658307 72092267 := bstep (se 1 (by rfl) ⟨54069200, by rfl⟩ : syracuseStep 72092267 = 108138401) B108138401
theorem B1117415 : Blo 658307 1117415 := bstep (se 1 (by rfl) ⟨838061, by rfl⟩ : syracuseStep 1117415 = 1676123) B1676123
theorem B658671 : Blo 658307 658671 := bstep (se 1 (by rfl) ⟨494003, by rfl⟩ : syracuseStep 658671 = 988007) B988007
theorem B658759 : Blo 658307 658759 := bstep (se 1 (by rfl) ⟨494069, by rfl⟩ : syracuseStep 658759 = 988139) B988139
theorem B3772007 : Blo 658307 3772007 := bstep (se 1 (by rfl) ⟨2829005, by rfl⟩ : syracuseStep 3772007 = 5658011) B5658011
theorem B8556263 : Blo 658307 8556263 := bstep (se 1 (by rfl) ⟨6417197, by rfl⟩ : syracuseStep 8556263 = 12834395) B12834395
theorem B660127 : Blo 658307 660127 := bstep (se 1 (by rfl) ⟨495095, by rfl⟩ : syracuseStep 660127 = 990191) B990191
theorem B1676315 : Blo 658307 1676315 := bstep (se 1 (by rfl) ⟨1257236, by rfl⟩ : syracuseStep 1676315 = 2514473) B2514473
theorem B988319 : Blo 658307 988319 := bstep (se 1 (by rfl) ⟨741239, by rfl⟩ : syracuseStep 988319 = 1482479) B1482479
theorem B988391 : Blo 658307 988391 := bstep (se 1 (by rfl) ⟨741293, by rfl⟩ : syracuseStep 988391 = 1482587) B1482587
theorem B3577067 : Blo 658307 3577067 := bstep (se 1 (by rfl) ⟨2682800, by rfl⟩ : syracuseStep 3577067 = 5365601) B5365601
theorem B988487 : Blo 658307 988487 := bstep (se 1 (by rfl) ⟨741365, by rfl⟩ : syracuseStep 988487 = 1482731) B1482731
theorem B661151 : Blo 658307 661151 := bstep (se 1 (by rfl) ⟨495863, by rfl⟩ : syracuseStep 661151 = 991727) B991727
theorem B16914257 : Blo 658307 16914257 := bstep (se 2 (by rfl) ⟨6342846, by rfl⟩ : syracuseStep 16914257 = 12685693) B12685693
theorem B661351 : Blo 658307 661351 := bstep (se 1 (by rfl) ⟨496013, by rfl⟩ : syracuseStep 661351 = 992027) B992027
theorem B661631 : Blo 658307 661631 := bstep (se 1 (by rfl) ⟨496223, by rfl⟩ : syracuseStep 661631 = 992447) B992447
theorem B989423 : Blo 658307 989423 := bstep (se 1 (by rfl) ⟨742067, by rfl⟩ : syracuseStep 989423 = 1484135) B1484135
theorem B661951 : Blo 658307 661951 := bstep (se 1 (by rfl) ⟨496463, by rfl⟩ : syracuseStep 661951 = 992927) B992927
theorem B662183 : Blo 658307 662183 := bstep (se 1 (by rfl) ⟨496637, by rfl⟩ : syracuseStep 662183 = 993275) B993275
theorem B2825057 : Blo 658307 2825057 := bstep (se 2 (by rfl) ⟨1059396, by rfl⟩ : syracuseStep 2825057 = 2118793) B2118793
theorem B990119 : Blo 658307 990119 := bstep (se 1 (by rfl) ⟨742589, by rfl⟩ : syracuseStep 990119 = 1485179) B1485179
theorem B7216553 : Blo 658307 7216553 := bstep (se 2 (by rfl) ⟨2706207, by rfl⟩ : syracuseStep 7216553 = 5412415) B5412415
theorem B990719 : Blo 658307 990719 := bstep (se 1 (by rfl) ⟨743039, by rfl⟩ : syracuseStep 990719 = 1486079) B1486079
theorem B991871 : Blo 658307 991871 := bstep (se 1 (by rfl) ⟨743903, by rfl⟩ : syracuseStep 991871 = 1487807) B1487807
theorem B991913 : Blo 658307 991913 := bstep (se 2 (by rfl) ⟨371967, by rfl⟩ : syracuseStep 991913 = 743935) B743935
theorem B1876925 : Blo 658307 1876925 := bstep (se 3 (by rfl) ⟨351923, by rfl⟩ : syracuseStep 1876925 = 703847) B703847
theorem B992255 : Blo 658307 992255 := bstep (se 1 (by rfl) ⟨744191, by rfl⟩ : syracuseStep 992255 = 1488383) B1488383
theorem B8692843 : Blo 658307 8692843 := bstep (se 1 (by rfl) ⟨6519632, by rfl⟩ : syracuseStep 8692843 = 13039265) B13039265
theorem B992567 : Blo 658307 992567 := bstep (se 1 (by rfl) ⟨744425, by rfl⟩ : syracuseStep 992567 = 1488851) B1488851
theorem B1287635 : Blo 658307 1287635 := bstep (se 1 (by rfl) ⟨965726, by rfl⟩ : syracuseStep 1287635 = 1931453) B1931453
theorem B992831 : Blo 658307 992831 := bstep (se 1 (by rfl) ⟨744623, by rfl⟩ : syracuseStep 992831 = 1489247) B1489247
theorem B1484459 : Blo 658307 1484459 := bstep (se 1 (by rfl) ⟨1113344, by rfl⟩ : syracuseStep 1484459 = 2226689) B2226689
theorem B1484873 : Blo 658307 1484873 := bstep (se 2 (by rfl) ⟨556827, by rfl⟩ : syracuseStep 1484873 = 1113655) B1113655
theorem B166799483 : Blo 658307 166799483 := bstep (se 1 (by rfl) ⟨125099612, by rfl⟩ : syracuseStep 166799483 = 250199225) B250199225
theorem B1583329 : Blo 658307 1583329 := bstep (se 2 (by rfl) ⟨593748, by rfl⟩ : syracuseStep 1583329 = 1187497) B1187497
theorem B26159435 : Blo 658307 26159435 := bstep (se 1 (by rfl) ⟨19619576, by rfl⟩ : syracuseStep 26159435 = 39239153) B39239153
theorem B1059647 : Blo 658307 1059647 := bstep (se 1 (by rfl) ⟨794735, by rfl⟩ : syracuseStep 1059647 = 1589471) B1589471
theorem B1486817 : Blo 658307 1486817 := bstep (se 2 (by rfl) ⟨557556, by rfl⟩ : syracuseStep 1486817 = 1115113) B1115113
theorem B667675 : Blo 658307 667675 := bstep (se 1 (by rfl) ⟨500756, by rfl⟩ : syracuseStep 667675 = 1001513) B1001513
theorem B91599761 : Blo 658307 91599761 := bstep (se 2 (by rfl) ⟨34349910, by rfl⟩ : syracuseStep 91599761 = 68699821) B68699821
theorem B1488923 : Blo 658307 1488923 := bstep (se 1 (by rfl) ⟨1116692, by rfl⟩ : syracuseStep 1488923 = 2233385) B2233385
theorem B2505937 : Blo 658307 2505937 := bstep (se 2 (by rfl) ⟨939726, by rfl⟩ : syracuseStep 2505937 = 1879453) B1879453
theorem B371703613 : Blo 658307 371703613 := bstep (se 3 (by rfl) ⟨69694427, by rfl⟩ : syracuseStep 371703613 = 139388855) B139388855
theorem B2506727 : Blo 658307 2506727 := bstep (se 1 (by rfl) ⟨1880045, by rfl⟩ : syracuseStep 2506727 = 3760091) B3760091
theorem B9062441 : Blo 658307 9062441 := bstep (se 2 (by rfl) ⟨3398415, by rfl⟩ : syracuseStep 9062441 = 6796831) B6796831
theorem B2509127 : Blo 658307 2509127 := bstep (se 1 (by rfl) ⟨1881845, by rfl⟩ : syracuseStep 2509127 = 3763691) B3763691
theorem B3754511 : Blo 658307 3754511 := bstep (se 1 (by rfl) ⟨2815883, by rfl⟩ : syracuseStep 3754511 = 5631767) B5631767
theorem B2116667 : Blo 658307 2116667 := bstep (se 1 (by rfl) ⟨1587500, by rfl⟩ : syracuseStep 2116667 = 3175001) B3175001
theorem B938747 : Blo 658307 938747 := bstep (se 1 (by rfl) ⟨704060, by rfl⟩ : syracuseStep 938747 = 1408121) B1408121
theorem B4773401 : Blo 658307 4773401 := bstep (se 2 (by rfl) ⟨1790025, by rfl⟩ : syracuseStep 4773401 = 3580051) B3580051
theorem B743071 : Blo 658307 743071 := bstep (se 1 (by rfl) ⟨557303, by rfl⟩ : syracuseStep 743071 = 1114607) B1114607
theorem B10149797 : Blo 658307 10149797 := bstep (se 4 (by rfl) ⟨951543, by rfl⟩ : syracuseStep 10149797 = 1903087) B1903087
theorem B5628041 : Blo 658307 5628041 := bstep (se 2 (by rfl) ⟨2110515, by rfl⟩ : syracuseStep 5628041 = 4221031) B4221031
theorem B14311727 : Blo 658307 14311727 := bstep (se 1 (by rfl) ⟨10733795, by rfl⟩ : syracuseStep 14311727 = 21467591) B21467591
theorem B5005799 : Blo 658307 5005799 := bstep (se 1 (by rfl) ⟨3754349, by rfl⟩ : syracuseStep 5005799 = 7508699) B7508699
theorem B2222207 : Blo 658307 2222207 := bstep (se 1 (by rfl) ⟨1666655, by rfl⟩ : syracuseStep 2222207 = 3333311) B3333311
theorem B3763007 : Blo 658307 3763007 := bstep (se 1 (by rfl) ⟨2822255, by rfl⟩ : syracuseStep 3763007 = 5644511) B5644511
theorem B1666615 : Blo 658307 1666615 := bstep (se 1 (by rfl) ⟨1249961, by rfl⟩ : syracuseStep 1666615 = 2499923) B2499923
theorem B3010303 : Blo 658307 3010303 := bstep (se 1 (by rfl) ⟨2257727, by rfl⟩ : syracuseStep 3010303 = 4515455) B4515455
theorem B1666939 : Blo 658307 1666939 := bstep (se 1 (by rfl) ⟨1250204, by rfl⟩ : syracuseStep 1666939 = 2500409) B2500409
theorem B2225663 : Blo 658307 2225663 := bstep (se 1 (by rfl) ⟨1669247, by rfl⟩ : syracuseStep 2225663 = 3338495) B3338495
theorem B2225771 : Blo 658307 2225771 := bstep (se 1 (by rfl) ⟨1669328, by rfl⟩ : syracuseStep 2225771 = 3338657) B3338657
theorem B3340115 : Blo 658307 3340115 := bstep (se 1 (by rfl) ⟨2505086, by rfl⟩ : syracuseStep 3340115 = 5010173) B5010173
theorem B2226041 : Blo 658307 2226041 := bstep (se 2 (by rfl) ⟨834765, by rfl⟩ : syracuseStep 2226041 = 1669531) B1669531
theorem B6028019 : Blo 658307 6028019 := bstep (se 1 (by rfl) ⟨4521014, by rfl⟩ : syracuseStep 6028019 = 9042029) B9042029
theorem B1112953 : Blo 658307 1112953 := bstep (se 2 (by rfl) ⟨417357, by rfl⟩ : syracuseStep 1112953 = 834715) B834715
theorem B1671131 : Blo 658307 1671131 := bstep (se 1 (by rfl) ⟨1253348, by rfl⟩ : syracuseStep 1671131 = 2506697) B2506697
theorem B2229659 : Blo 658307 2229659 := bstep (se 1 (by rfl) ⟨1672244, by rfl⟩ : syracuseStep 2229659 = 3344489) B3344489
theorem B1672751 : Blo 658307 1672751 := bstep (se 1 (by rfl) ⟨1254563, by rfl⟩ : syracuseStep 1672751 = 2509127) B2509127
theorem B1411111 : Blo 658307 1411111 := bstep (se 1 (by rfl) ⟨1058333, by rfl⟩ : syracuseStep 1411111 = 2116667) B2116667
theorem B5704175 : Blo 658307 5704175 := bstep (se 1 (by rfl) ⟨4278131, by rfl⟩ : syracuseStep 5704175 = 8556263) B8556263
theorem B1117543 : Blo 658307 1117543 := bstep (se 1 (by rfl) ⟨838157, by rfl⟩ : syracuseStep 1117543 = 1676315) B1676315
theorem B658879 : Blo 658307 658879 := bstep (se 1 (by rfl) ⟨494159, by rfl⟩ : syracuseStep 658879 = 988319) B988319
theorem B658927 : Blo 658307 658927 := bstep (se 1 (by rfl) ⟨494195, by rfl⟩ : syracuseStep 658927 = 988391) B988391
theorem B658991 : Blo 658307 658991 := bstep (se 1 (by rfl) ⟨494243, by rfl⟩ : syracuseStep 658991 = 988487) B988487
theorem B3182267 : Blo 658307 3182267 := bstep (se 1 (by rfl) ⟨2386700, by rfl⟩ : syracuseStep 3182267 = 4773401) B4773401
theorem B11276171 : Blo 658307 11276171 := bstep (se 1 (by rfl) ⟨8457128, by rfl⟩ : syracuseStep 11276171 = 16914257) B16914257
theorem B659615 : Blo 658307 659615 := bstep (se 1 (by rfl) ⟨494711, by rfl⟩ : syracuseStep 659615 = 989423) B989423
theorem B660079 : Blo 658307 660079 := bstep (se 1 (by rfl) ⟨495059, by rfl⟩ : syracuseStep 660079 = 990119) B990119
theorem B660479 : Blo 658307 660479 := bstep (se 1 (by rfl) ⟨495359, by rfl⟩ : syracuseStep 660479 = 990719) B990719
theorem B890233 : Blo 658307 890233 := bstep (se 2 (by rfl) ⟨333837, by rfl⟩ : syracuseStep 890233 = 667675) B667675
theorem B9541151 : Blo 658307 9541151 := bstep (se 1 (by rfl) ⟨7155863, by rfl⟩ : syracuseStep 9541151 = 14311727) B14311727
theorem B661247 : Blo 658307 661247 := bstep (se 1 (by rfl) ⟨495935, by rfl⟩ : syracuseStep 661247 = 991871) B991871
theorem B661275 : Blo 658307 661275 := bstep (se 1 (by rfl) ⟨495956, by rfl⟩ : syracuseStep 661275 = 991913) B991913
theorem B1251283 : Blo 658307 1251283 := bstep (se 1 (by rfl) ⟨938462, by rfl⟩ : syracuseStep 1251283 = 1876925) B1876925
theorem B661503 : Blo 658307 661503 := bstep (se 1 (by rfl) ⟨496127, by rfl⟩ : syracuseStep 661503 = 992255) B992255
theorem B661711 : Blo 658307 661711 := bstep (se 1 (by rfl) ⟨496283, by rfl⟩ : syracuseStep 661711 = 992567) B992567
theorem B661887 : Blo 658307 661887 := bstep (se 1 (by rfl) ⟨496415, by rfl⟩ : syracuseStep 661887 = 992831) B992831
theorem B989639 : Blo 658307 989639 := bstep (se 1 (by rfl) ⟨742229, by rfl⟩ : syracuseStep 989639 = 1484459) B1484459
theorem B989915 : Blo 658307 989915 := bstep (se 1 (by rfl) ⟨742436, by rfl⟩ : syracuseStep 989915 = 1484873) B1484873
theorem B1481471 : Blo 658307 1481471 := bstep (se 1 (by rfl) ⟨1111103, by rfl⟩ : syracuseStep 1481471 = 2222207) B2222207
theorem B17439623 : Blo 658307 17439623 := bstep (se 1 (by rfl) ⟨13079717, by rfl⟩ : syracuseStep 17439623 = 26159435) B26159435
theorem B2825725 : Blo 658307 2825725 := bstep (se 3 (by rfl) ⟨529823, by rfl⟩ : syracuseStep 2825725 = 1059647) B1059647
theorem B990761 : Blo 658307 990761 := bstep (se 2 (by rfl) ⟨371535, by rfl⟩ : syracuseStep 990761 = 743071) B743071
theorem B991211 : Blo 658307 991211 := bstep (se 1 (by rfl) ⟨743408, by rfl⟩ : syracuseStep 991211 = 1486817) B1486817
theorem B1483775 : Blo 658307 1483775 := bstep (se 1 (by rfl) ⟨1112831, by rfl⟩ : syracuseStep 1483775 = 2225663) B2225663
theorem B1483847 : Blo 658307 1483847 := bstep (se 1 (by rfl) ⟨1112885, by rfl⟩ : syracuseStep 1483847 = 2225771) B2225771
theorem B1483937 : Blo 658307 1483937 := bstep (se 2 (by rfl) ⟨556476, by rfl⟩ : syracuseStep 1483937 = 1112953) B1112953
theorem B1484027 : Blo 658307 1484027 := bstep (se 1 (by rfl) ⟨1113020, by rfl⟩ : syracuseStep 1484027 = 2226041) B2226041
theorem B992615 : Blo 658307 992615 := bstep (se 1 (by rfl) ⟨744461, by rfl⟩ : syracuseStep 992615 = 1488923) B1488923
theorem B1879271 : Blo 658307 1879271 := bstep (se 1 (by rfl) ⟨1409453, by rfl⟩ : syracuseStep 1879271 = 2818907) B2818907
theorem B6041627 : Blo 658307 6041627 := bstep (se 1 (by rfl) ⟨4531220, by rfl⟩ : syracuseStep 6041627 = 9062441) B9062441
theorem B2503007 : Blo 658307 2503007 := bstep (se 1 (by rfl) ⟨1877255, by rfl⟩ : syracuseStep 2503007 = 3754511) B3754511
theorem B2503325 : Blo 658307 2503325 := bstep (se 3 (by rfl) ⟨469373, by rfl⟩ : syracuseStep 2503325 = 938747) B938747
theorem B2111105 : Blo 658307 2111105 := bstep (se 2 (by rfl) ⟨791664, by rfl⟩ : syracuseStep 2111105 = 1583329) B1583329
theorem B3752027 : Blo 658307 3752027 := bstep (se 1 (by rfl) ⟨2814020, by rfl⟩ : syracuseStep 3752027 = 5628041) B5628041
theorem B111199655 : Blo 658307 111199655 := bstep (se 1 (by rfl) ⟨83399741, by rfl⟩ : syracuseStep 111199655 = 166799483) B166799483
theorem B2508671 : Blo 658307 2508671 := bstep (se 1 (by rfl) ⟨1881503, by rfl⟩ : syracuseStep 2508671 = 3763007) B3763007
theorem B61066507 : Blo 658307 61066507 := bstep (se 1 (by rfl) ⟨45799880, by rfl⟩ : syracuseStep 61066507 = 91599761) B91599761
theorem B4018679 : Blo 658307 4018679 := bstep (se 1 (by rfl) ⟨3014009, by rfl⟩ : syracuseStep 4018679 = 6028019) B6028019
theorem B495604817 : Blo 658307 495604817 := bstep (se 2 (by rfl) ⟨185851806, by rfl⟩ : syracuseStep 495604817 = 371703613) B371703613
theorem B3560915 : Blo 658307 3560915 := bstep (se 1 (by rfl) ⟨2670686, by rfl⟩ : syracuseStep 3560915 = 5341373) B5341373
theorem B8018135 : Blo 658307 8018135 := bstep (se 1 (by rfl) ⟨6013601, by rfl⟩ : syracuseStep 8018135 = 12027203) B12027203
theorem B11590457 : Blo 658307 11590457 := bstep (se 2 (by rfl) ⟨4346421, by rfl⟩ : syracuseStep 11590457 = 8692843) B8692843
theorem B48061511 : Blo 658307 48061511 := bstep (se 1 (by rfl) ⟨36046133, by rfl⟩ : syracuseStep 48061511 = 72092267) B72092267
theorem B744943 : Blo 658307 744943 := bstep (se 1 (by rfl) ⟨558707, by rfl⟩ : syracuseStep 744943 = 1117415) B1117415
theorem B2514671 : Blo 658307 2514671 := bstep (se 1 (by rfl) ⟨1886003, by rfl⟩ : syracuseStep 2514671 = 3772007) B3772007
theorem B2384711 : Blo 658307 2384711 := bstep (se 1 (by rfl) ⟨1788533, by rfl⟩ : syracuseStep 2384711 = 3577067) B3577067
theorem B3433693 : Blo 658307 3433693 := bstep (se 3 (by rfl) ⟨643817, by rfl⟩ : syracuseStep 3433693 = 1287635) B1287635
theorem B2222153 : Blo 658307 2222153 := bstep (se 2 (by rfl) ⟨833307, by rfl⟩ : syracuseStep 2222153 = 1666615) B1666615
theorem B4811035 : Blo 658307 4811035 := bstep (se 1 (by rfl) ⟨3608276, by rfl⟩ : syracuseStep 4811035 = 7216553) B7216553
theorem B2222585 : Blo 658307 2222585 := bstep (se 2 (by rfl) ⟨833469, by rfl⟩ : syracuseStep 2222585 = 1666939) B1666939
theorem B3337199 : Blo 658307 3337199 := bstep (se 1 (by rfl) ⟨2502899, by rfl⟩ : syracuseStep 3337199 = 5005799) B5005799
theorem B7533485 : Blo 658307 7533485 := bstep (se 3 (by rfl) ⟨1412528, by rfl⟩ : syracuseStep 7533485 = 2825057) B2825057
theorem B2226743 : Blo 658307 2226743 := bstep (se 1 (by rfl) ⟨1670057, by rfl⟩ : syracuseStep 2226743 = 3340115) B3340115
theorem B16054949 : Blo 658307 16054949 := bstep (se 4 (by rfl) ⟨1505151, by rfl⟩ : syracuseStep 16054949 = 3010303) B3010303
theorem B3341249 : Blo 658307 3341249 := bstep (se 2 (by rfl) ⟨1252968, by rfl⟩ : syracuseStep 3341249 = 2505937) B2505937
theorem B27066125 : Blo 658307 27066125 := bstep (se 3 (by rfl) ⟨5074898, by rfl⟩ : syracuseStep 27066125 = 10149797) B10149797
theorem B1114087 : Blo 658307 1114087 := bstep (se 1 (by rfl) ⟨835565, by rfl⟩ : syracuseStep 1114087 = 1671131) B1671131
theorem B1671151 : Blo 658307 1671151 := bstep (se 1 (by rfl) ⟨1253363, by rfl⟩ : syracuseStep 1671151 = 2506727) B2506727
theorem B1115167 : Blo 658307 1115167 := bstep (se 1 (by rfl) ⟨836375, by rfl⟩ : syracuseStep 1115167 = 1672751) B1672751
theorem B1672447 : Blo 658307 1672447 := bstep (se 1 (by rfl) ⟨1254335, by rfl⟩ : syracuseStep 1672447 = 2508671) B2508671
theorem B3802783 : Blo 658307 3802783 := bstep (se 1 (by rfl) ⟨2852087, by rfl⟩ : syracuseStep 3802783 = 5704175) B5704175
theorem B330403211 : Blo 658307 330403211 := bstep (se 1 (by rfl) ⟨247802408, by rfl⟩ : syracuseStep 330403211 = 495604817) B495604817
theorem B6360767 : Blo 658307 6360767 := bstep (se 1 (by rfl) ⟨4770575, by rfl⟩ : syracuseStep 6360767 = 9541151) B9541151
theorem B5345423 : Blo 658307 5345423 := bstep (se 1 (by rfl) ⟨4009067, by rfl⟩ : syracuseStep 5345423 = 8018135) B8018135
theorem B659759 : Blo 658307 659759 := bstep (se 1 (by rfl) ⟨494819, by rfl⟩ : syracuseStep 659759 = 989639) B989639
theorem B659943 : Blo 658307 659943 := bstep (se 1 (by rfl) ⟨494957, by rfl⟩ : syracuseStep 659943 = 989915) B989915
theorem B987647 : Blo 658307 987647 := bstep (se 1 (by rfl) ⟨740735, by rfl⟩ : syracuseStep 987647 = 1481471) B1481471
theorem B660507 : Blo 658307 660507 := bstep (se 1 (by rfl) ⟨495380, by rfl⟩ : syracuseStep 660507 = 990761) B990761
theorem B1676447 : Blo 658307 1676447 := bstep (se 1 (by rfl) ⟨1257335, by rfl⟩ : syracuseStep 1676447 = 2514671) B2514671
theorem B660807 : Blo 658307 660807 := bstep (se 1 (by rfl) ⟨495605, by rfl⟩ : syracuseStep 660807 = 991211) B991211
theorem B989183 : Blo 658307 989183 := bstep (se 1 (by rfl) ⟨741887, by rfl⟩ : syracuseStep 989183 = 1483775) B1483775
theorem B989231 : Blo 658307 989231 := bstep (se 1 (by rfl) ⟨741923, by rfl⟩ : syracuseStep 989231 = 1483847) B1483847
theorem B989291 : Blo 658307 989291 := bstep (se 1 (by rfl) ⟨741968, by rfl⟩ : syracuseStep 989291 = 1483937) B1483937
theorem B989351 : Blo 658307 989351 := bstep (se 1 (by rfl) ⟨742013, by rfl⟩ : syracuseStep 989351 = 1484027) B1484027
theorem B661743 : Blo 658307 661743 := bstep (se 1 (by rfl) ⟨496307, by rfl⟩ : syracuseStep 661743 = 992615) B992615
theorem B1481435 : Blo 658307 1481435 := bstep (se 1 (by rfl) ⟨1111076, by rfl⟩ : syracuseStep 1481435 = 2222153) B2222153
theorem B1481723 : Blo 658307 1481723 := bstep (se 1 (by rfl) ⟨1111292, by rfl⟩ : syracuseStep 1481723 = 2222585) B2222585
theorem B30907885 : Blo 658307 30907885 := bstep (se 3 (by rfl) ⟨5795228, by rfl⟩ : syracuseStep 30907885 = 11590457) B11590457
theorem B1252847 : Blo 658307 1252847 := bstep (se 1 (by rfl) ⟨939635, by rfl⟩ : syracuseStep 1252847 = 1879271) B1879271
theorem B5022323 : Blo 658307 5022323 := bstep (se 1 (by rfl) ⟨3766742, by rfl⟩ : syracuseStep 5022323 = 7533485) B7533485
theorem B1484495 : Blo 658307 1484495 := bstep (se 1 (by rfl) ⟨1113371, by rfl⟩ : syracuseStep 1484495 = 2226743) B2226743
theorem B993257 : Blo 658307 993257 := bstep (se 2 (by rfl) ⟨372471, by rfl⟩ : syracuseStep 993257 = 744943) B744943
theorem B1485449 : Blo 658307 1485449 := bstep (se 2 (by rfl) ⟨557043, by rfl⟩ : syracuseStep 1485449 = 1114087) B1114087
theorem B2501351 : Blo 658307 2501351 := bstep (se 1 (by rfl) ⟨1876013, by rfl⟩ : syracuseStep 2501351 = 3752027) B3752027
theorem B1486439 : Blo 658307 1486439 := bstep (se 1 (by rfl) ⟨1114829, by rfl⟩ : syracuseStep 1486439 = 2229659) B2229659
theorem B7517447 : Blo 658307 7517447 := bstep (se 1 (by rfl) ⟨5638085, by rfl⟩ : syracuseStep 7517447 = 11276171) B11276171
theorem B1881481 : Blo 658307 1881481 := bstep (se 2 (by rfl) ⟨705555, by rfl⟩ : syracuseStep 1881481 = 1411111) B1411111
theorem B2373943 : Blo 658307 2373943 := bstep (se 1 (by rfl) ⟨1780457, by rfl⟩ : syracuseStep 2373943 = 3560915) B3560915
theorem B296532413 : Blo 658307 296532413 := bstep (se 3 (by rfl) ⟨55599827, by rfl⟩ : syracuseStep 296532413 = 111199655) B111199655
theorem B1490057 : Blo 658307 1490057 := bstep (se 2 (by rfl) ⟨558771, by rfl⟩ : syracuseStep 1490057 = 1117543) B1117543
theorem B1589807 : Blo 658307 1589807 := bstep (se 1 (by rfl) ⟨1192355, by rfl⟩ : syracuseStep 1589807 = 2384711) B2384711
theorem B10703299 : Blo 658307 10703299 := bstep (se 1 (by rfl) ⟨8027474, by rfl⟩ : syracuseStep 10703299 = 16054949) B16054949
theorem B18044083 : Blo 658307 18044083 := bstep (se 1 (by rfl) ⟨13533062, by rfl⟩ : syracuseStep 18044083 = 27066125) B27066125
theorem B4578257 : Blo 658307 4578257 := bstep (se 2 (by rfl) ⟨1716846, by rfl⟩ : syracuseStep 4578257 = 3433693) B3433693
theorem B2121511 : Blo 658307 2121511 := bstep (se 1 (by rfl) ⟨1591133, by rfl⟩ : syracuseStep 2121511 = 3182267) B3182267
theorem B2679119 : Blo 658307 2679119 := bstep (se 1 (by rfl) ⟨2009339, by rfl⟩ : syracuseStep 2679119 = 4018679) B4018679
theorem B6414713 : Blo 658307 6414713 := bstep (se 2 (by rfl) ⟨2405517, by rfl⟩ : syracuseStep 6414713 = 4811035) B4811035
theorem B81422009 : Blo 658307 81422009 := bstep (se 2 (by rfl) ⟨30533253, by rfl⟩ : syracuseStep 81422009 = 61066507) B61066507
theorem B11626415 : Blo 658307 11626415 := bstep (se 1 (by rfl) ⟨8719811, by rfl⟩ : syracuseStep 11626415 = 17439623) B17439623
theorem B32041007 : Blo 658307 32041007 := bstep (se 1 (by rfl) ⟨24030755, by rfl⟩ : syracuseStep 32041007 = 48061511) B48061511
theorem B4747909 : Blo 658307 4747909 := bstep (se 4 (by rfl) ⟨445116, by rfl⟩ : syracuseStep 4747909 = 890233) B890233
theorem B2224799 : Blo 658307 2224799 := bstep (se 1 (by rfl) ⟨1668599, by rfl⟩ : syracuseStep 2224799 = 3337199) B3337199
theorem B1668377 : Blo 658307 1668377 := bstep (se 2 (by rfl) ⟨625641, by rfl⟩ : syracuseStep 1668377 = 1251283) B1251283
theorem B4027751 : Blo 658307 4027751 := bstep (se 1 (by rfl) ⟨3020813, by rfl⟩ : syracuseStep 4027751 = 6041627) B6041627
theorem B1668671 : Blo 658307 1668671 := bstep (se 1 (by rfl) ⟨1251503, by rfl⟩ : syracuseStep 1668671 = 2503007) B2503007
theorem B1668883 : Blo 658307 1668883 := bstep (se 1 (by rfl) ⟨1251662, by rfl⟩ : syracuseStep 1668883 = 2503325) B2503325
theorem B1407403 : Blo 658307 1407403 := bstep (se 1 (by rfl) ⟨1055552, by rfl⟩ : syracuseStep 1407403 = 2111105) B2111105
theorem B2227499 : Blo 658307 2227499 := bstep (se 1 (by rfl) ⟨1670624, by rfl⟩ : syracuseStep 2227499 = 3341249) B3341249
theorem B3767633 : Blo 658307 3767633 := bstep (se 2 (by rfl) ⟨1412862, by rfl⟩ : syracuseStep 3767633 = 2825725) B2825725
theorem B2228201 : Blo 658307 2228201 := bstep (se 2 (by rfl) ⟨835575, by rfl⟩ : syracuseStep 2228201 = 1671151) B1671151
theorem B2229929 : Blo 658307 2229929 := bstep (se 2 (by rfl) ⟨836223, by rfl⟩ : syracuseStep 2229929 = 1672447) B1672447
theorem B220268807 : Blo 658307 220268807 := bstep (se 1 (by rfl) ⟨165201605, by rfl⟩ : syracuseStep 220268807 = 330403211) B330403211
theorem B658431 : Blo 658307 658431 := bstep (se 1 (by rfl) ⟨493823, by rfl⟩ : syracuseStep 658431 = 987647) B987647
theorem B1117631 : Blo 658307 1117631 := bstep (se 1 (by rfl) ⟨838223, by rfl⟩ : syracuseStep 1117631 = 1676447) B1676447
theorem B659455 : Blo 658307 659455 := bstep (se 1 (by rfl) ⟨494591, by rfl⟩ : syracuseStep 659455 = 989183) B989183
theorem B659487 : Blo 658307 659487 := bstep (se 1 (by rfl) ⟨494615, by rfl⟩ : syracuseStep 659487 = 989231) B989231
theorem B659527 : Blo 658307 659527 := bstep (se 1 (by rfl) ⟨494645, by rfl⟩ : syracuseStep 659527 = 989291) B989291
theorem B659567 : Blo 658307 659567 := bstep (se 1 (by rfl) ⟨494675, by rfl⟩ : syracuseStep 659567 = 989351) B989351
theorem B987623 : Blo 658307 987623 := bstep (se 1 (by rfl) ⟨740717, by rfl⟩ : syracuseStep 987623 = 1481435) B1481435
theorem B3052171 : Blo 658307 3052171 := bstep (se 1 (by rfl) ⟨2289128, by rfl⟩ : syracuseStep 3052171 = 4578257) B4578257
theorem B987815 : Blo 658307 987815 := bstep (se 1 (by rfl) ⟨740861, by rfl⟩ : syracuseStep 987815 = 1481723) B1481723
theorem B3348215 : Blo 658307 3348215 := bstep (se 1 (by rfl) ⟨2511161, by rfl⟩ : syracuseStep 3348215 = 5022323) B5022323
theorem B6330545 : Blo 658307 6330545 := bstep (se 2 (by rfl) ⟨2373954, by rfl⟩ : syracuseStep 6330545 = 4747909) B4747909
theorem B989663 : Blo 658307 989663 := bstep (se 1 (by rfl) ⟨742247, by rfl⟩ : syracuseStep 989663 = 1484495) B1484495
theorem B662171 : Blo 658307 662171 := bstep (se 1 (by rfl) ⟨496628, by rfl⟩ : syracuseStep 662171 = 993257) B993257
theorem B24058777 : Blo 658307 24058777 := bstep (se 2 (by rfl) ⟨9022041, by rfl⟩ : syracuseStep 24058777 = 18044083) B18044083
theorem B990299 : Blo 658307 990299 := bstep (se 1 (by rfl) ⟨742724, by rfl⟩ : syracuseStep 990299 = 1485449) B1485449
theorem B990959 : Blo 658307 990959 := bstep (se 1 (by rfl) ⟨743219, by rfl⟩ : syracuseStep 990959 = 1486439) B1486439
theorem B1483199 : Blo 658307 1483199 := bstep (se 1 (by rfl) ⟨1112399, by rfl⟩ : syracuseStep 1483199 = 2224799) B2224799
theorem B1876537 : Blo 658307 1876537 := bstep (se 2 (by rfl) ⟨703701, by rfl⟩ : syracuseStep 1876537 = 1407403) B1407403
theorem B993371 : Blo 658307 993371 := bstep (se 1 (by rfl) ⟨745028, by rfl⟩ : syracuseStep 993371 = 1490057) B1490057
theorem B1484999 : Blo 658307 1484999 := bstep (se 1 (by rfl) ⟨1113749, by rfl⟩ : syracuseStep 1484999 = 2227499) B2227499
theorem B2828681 : Blo 658307 2828681 := bstep (se 2 (by rfl) ⟨1060755, by rfl⟩ : syracuseStep 2828681 = 2121511) B2121511
theorem B1485467 : Blo 658307 1485467 := bstep (se 1 (by rfl) ⟨1114100, by rfl⟩ : syracuseStep 1485467 = 2228201) B2228201
theorem B1486889 : Blo 658307 1486889 := bstep (se 2 (by rfl) ⟨557583, by rfl⟩ : syracuseStep 1486889 = 1115167) B1115167
theorem B4239485 : Blo 658307 4239485 := bstep (se 3 (by rfl) ⟨794903, by rfl⟩ : syracuseStep 4239485 = 1589807) B1589807
theorem B4240511 : Blo 658307 4240511 := bstep (se 1 (by rfl) ⟨3180383, by rfl⟩ : syracuseStep 4240511 = 6360767) B6360767
theorem B1786079 : Blo 658307 1786079 := bstep (se 1 (by rfl) ⟨1339559, by rfl⟩ : syracuseStep 1786079 = 2679119) B2679119
theorem B4276475 : Blo 658307 4276475 := bstep (se 1 (by rfl) ⟨3207356, by rfl⟩ : syracuseStep 4276475 = 6414713) B6414713
theorem B14271065 : Blo 658307 14271065 := bstep (se 2 (by rfl) ⟨5351649, by rfl⟩ : syracuseStep 14271065 = 10703299) B10703299
theorem B54281339 : Blo 658307 54281339 := bstep (se 1 (by rfl) ⟨40711004, by rfl⟩ : syracuseStep 54281339 = 81422009) B81422009
theorem B7750943 : Blo 658307 7750943 := bstep (se 1 (by rfl) ⟨5813207, by rfl⟩ : syracuseStep 7750943 = 11626415) B11626415
theorem B2508641 : Blo 658307 2508641 := bstep (se 2 (by rfl) ⟨940740, by rfl⟩ : syracuseStep 2508641 = 1881481) B1881481
theorem B3165257 : Blo 658307 3165257 := bstep (se 2 (by rfl) ⟨1186971, by rfl⟩ : syracuseStep 3165257 = 2373943) B2373943
theorem B41210513 : Blo 658307 41210513 := bstep (se 2 (by rfl) ⟨15453942, by rfl⟩ : syracuseStep 41210513 = 30907885) B30907885
theorem B2511755 : Blo 658307 2511755 := bstep (se 1 (by rfl) ⟨1883816, by rfl⟩ : syracuseStep 2511755 = 3767633) B3767633
theorem B5070377 : Blo 658307 5070377 := bstep (se 2 (by rfl) ⟨1901391, by rfl⟩ : syracuseStep 5070377 = 3802783) B3802783
theorem B3563615 : Blo 658307 3563615 := bstep (se 1 (by rfl) ⟨2672711, by rfl⟩ : syracuseStep 3563615 = 5345423) B5345423
theorem B21360671 : Blo 658307 21360671 := bstep (se 1 (by rfl) ⟨16020503, by rfl⟩ : syracuseStep 21360671 = 32041007) B32041007
theorem B1667567 : Blo 658307 1667567 := bstep (se 1 (by rfl) ⟨1250675, by rfl⟩ : syracuseStep 1667567 = 2501351) B2501351
theorem B2225177 : Blo 658307 2225177 := bstep (se 2 (by rfl) ⟨834441, by rfl⟩ : syracuseStep 2225177 = 1668883) B1668883
theorem B5011631 : Blo 658307 5011631 := bstep (se 1 (by rfl) ⟨3758723, by rfl⟩ : syracuseStep 5011631 = 7517447) B7517447
theorem B1112251 : Blo 658307 1112251 := bstep (se 1 (by rfl) ⟨834188, by rfl⟩ : syracuseStep 1112251 = 1668377) B1668377
theorem B2685167 : Blo 658307 2685167 := bstep (se 1 (by rfl) ⟨2013875, by rfl⟩ : syracuseStep 2685167 = 4027751) B4027751
theorem B1112447 : Blo 658307 1112447 := bstep (se 1 (by rfl) ⟨834335, by rfl⟩ : syracuseStep 1112447 = 1668671) B1668671
theorem B3340925 : Blo 658307 3340925 := bstep (se 3 (by rfl) ⟨626423, by rfl⟩ : syracuseStep 3340925 = 1252847) B1252847
theorem B197688275 : Blo 658307 197688275 := bstep (se 1 (by rfl) ⟨148266206, by rfl⟩ : syracuseStep 197688275 = 296532413) B296532413
theorem B2850983 : Blo 658307 2850983 := bstep (se 1 (by rfl) ⟨2138237, by rfl⟩ : syracuseStep 2850983 = 4276475) B4276475
theorem B1672427 : Blo 658307 1672427 := bstep (se 1 (by rfl) ⟨1254320, by rfl⟩ : syracuseStep 1672427 = 2508641) B2508641
theorem B658415 : Blo 658307 658415 := bstep (se 1 (by rfl) ⟨493811, by rfl⟩ : syracuseStep 658415 = 987623) B987623
theorem B658543 : Blo 658307 658543 := bstep (se 1 (by rfl) ⟨493907, by rfl⟩ : syracuseStep 658543 = 987815) B987815
theorem B1674503 : Blo 658307 1674503 := bstep (se 1 (by rfl) ⟨1255877, by rfl⟩ : syracuseStep 1674503 = 2511755) B2511755
theorem B2232143 : Blo 658307 2232143 := bstep (se 1 (by rfl) ⟨1674107, by rfl⟩ : syracuseStep 2232143 = 3348215) B3348215
theorem B659775 : Blo 658307 659775 := bstep (se 1 (by rfl) ⟨494831, by rfl⟩ : syracuseStep 659775 = 989663) B989663
theorem B660199 : Blo 658307 660199 := bstep (se 1 (by rfl) ⟨495149, by rfl⟩ : syracuseStep 660199 = 990299) B990299
theorem B660639 : Blo 658307 660639 := bstep (se 1 (by rfl) ⟨495479, by rfl⟩ : syracuseStep 660639 = 990959) B990959
theorem B988799 : Blo 658307 988799 := bstep (se 1 (by rfl) ⟨741599, by rfl⟩ : syracuseStep 988799 = 1483199) B1483199
theorem B662247 : Blo 658307 662247 := bstep (se 1 (by rfl) ⟨496685, by rfl⟩ : syracuseStep 662247 = 993371) B993371
theorem B989999 : Blo 658307 989999 := bstep (se 1 (by rfl) ⟨742499, by rfl⟩ : syracuseStep 989999 = 1484999) B1484999
theorem B990311 : Blo 658307 990311 := bstep (se 1 (by rfl) ⟨742733, by rfl⟩ : syracuseStep 990311 = 1485467) B1485467
theorem B991259 : Blo 658307 991259 := bstep (se 1 (by rfl) ⟨743444, by rfl⟩ : syracuseStep 991259 = 1486889) B1486889
theorem B2826323 : Blo 658307 2826323 := bstep (se 1 (by rfl) ⟨2119742, by rfl⟩ : syracuseStep 2826323 = 4239485) B4239485
theorem B1483001 : Blo 658307 1483001 := bstep (se 2 (by rfl) ⟨556125, by rfl⟩ : syracuseStep 1483001 = 1112251) B1112251
theorem B1483451 : Blo 658307 1483451 := bstep (se 1 (by rfl) ⟨1112588, by rfl⟩ : syracuseStep 1483451 = 2225177) B2225177
theorem B2827007 : Blo 658307 2827007 := bstep (se 1 (by rfl) ⟨2120255, by rfl⟩ : syracuseStep 2827007 = 4240511) B4240511
theorem B1190719 : Blo 658307 1190719 := bstep (se 1 (by rfl) ⟨893039, by rfl⟩ : syracuseStep 1190719 = 1786079) B1786079
theorem B9514043 : Blo 658307 9514043 := bstep (se 1 (by rfl) ⟨7135532, by rfl⟩ : syracuseStep 9514043 = 14271065) B14271065
theorem B2502049 : Blo 658307 2502049 := bstep (se 2 (by rfl) ⟨938268, by rfl⟩ : syracuseStep 2502049 = 1876537) B1876537
theorem B36187559 : Blo 658307 36187559 := bstep (se 1 (by rfl) ⟨27140669, by rfl⟩ : syracuseStep 36187559 = 54281339) B54281339
theorem B1486619 : Blo 658307 1486619 := bstep (se 1 (by rfl) ⟨1114964, by rfl⟩ : syracuseStep 1486619 = 2229929) B2229929
theorem B146845871 : Blo 658307 146845871 := bstep (se 1 (by rfl) ⟨110134403, by rfl⟩ : syracuseStep 146845871 = 220268807) B220268807
theorem B2110171 : Blo 658307 2110171 := bstep (se 1 (by rfl) ⟨1582628, by rfl⟩ : syracuseStep 2110171 = 3165257) B3165257
theorem B27473675 : Blo 658307 27473675 := bstep (se 1 (by rfl) ⟨20605256, by rfl⟩ : syracuseStep 27473675 = 41210513) B41210513
theorem B2375743 : Blo 658307 2375743 := bstep (se 1 (by rfl) ⟨1781807, by rfl⟩ : syracuseStep 2375743 = 3563615) B3563615
theorem B1885787 : Blo 658307 1885787 := bstep (se 1 (by rfl) ⟨1414340, by rfl⟩ : syracuseStep 1885787 = 2828681) B2828681
theorem B14240447 : Blo 658307 14240447 := bstep (se 1 (by rfl) ⟨10680335, by rfl⟩ : syracuseStep 14240447 = 21360671) B21360671
theorem B13521005 : Blo 658307 13521005 := bstep (se 3 (by rfl) ⟨2535188, by rfl⟩ : syracuseStep 13521005 = 5070377) B5070377
theorem B1790111 : Blo 658307 1790111 := bstep (se 1 (by rfl) ⟨1342583, by rfl⟩ : syracuseStep 1790111 = 2685167) B2685167
theorem B741631 : Blo 658307 741631 := bstep (se 1 (by rfl) ⟨556223, by rfl⟩ : syracuseStep 741631 = 1112447) B1112447
theorem B5167295 : Blo 658307 5167295 := bstep (se 1 (by rfl) ⟨3875471, by rfl⟩ : syracuseStep 5167295 = 7750943) B7750943
theorem B745087 : Blo 658307 745087 := bstep (se 1 (by rfl) ⟨558815, by rfl⟩ : syracuseStep 745087 = 1117631) B1117631
theorem B16278245 : Blo 658307 16278245 := bstep (se 4 (by rfl) ⟨1526085, by rfl⟩ : syracuseStep 16278245 = 3052171) B3052171
theorem B4220363 : Blo 658307 4220363 := bstep (se 1 (by rfl) ⟨3165272, by rfl⟩ : syracuseStep 4220363 = 6330545) B6330545
theorem B1111711 : Blo 658307 1111711 := bstep (se 1 (by rfl) ⟨833783, by rfl⟩ : syracuseStep 1111711 = 1667567) B1667567
theorem B32078369 : Blo 658307 32078369 := bstep (se 2 (by rfl) ⟨12029388, by rfl⟩ : syracuseStep 32078369 = 24058777) B24058777
theorem B3341087 : Blo 658307 3341087 := bstep (se 1 (by rfl) ⟨2505815, by rfl⟩ : syracuseStep 3341087 = 5011631) B5011631
theorem B2227283 : Blo 658307 2227283 := bstep (se 1 (by rfl) ⟨1670462, by rfl⟩ : syracuseStep 2227283 = 3340925) B3340925
theorem B131792183 : Blo 658307 131792183 := bstep (se 1 (by rfl) ⟨98844137, by rfl⟩ : syracuseStep 131792183 = 197688275) B197688275
theorem B1900655 : Blo 658307 1900655 := bstep (se 1 (by rfl) ⟨1425491, by rfl⟩ : syracuseStep 1900655 = 2850983) B2850983
theorem B1114951 : Blo 658307 1114951 := bstep (se 1 (by rfl) ⟨836213, by rfl⟩ : syracuseStep 1114951 = 1672427) B1672427
theorem B1116335 : Blo 658307 1116335 := bstep (se 1 (by rfl) ⟨837251, by rfl⟩ : syracuseStep 1116335 = 1674503) B1674503
theorem B9014003 : Blo 658307 9014003 := bstep (se 1 (by rfl) ⟨6760502, by rfl⟩ : syracuseStep 9014003 = 13521005) B13521005
theorem B659199 : Blo 658307 659199 := bstep (se 1 (by rfl) ⟨494399, by rfl⟩ : syracuseStep 659199 = 988799) B988799
theorem B3444863 : Blo 658307 3444863 := bstep (se 1 (by rfl) ⟨2583647, by rfl⟩ : syracuseStep 3444863 = 5167295) B5167295
theorem B659999 : Blo 658307 659999 := bstep (se 1 (by rfl) ⟨494999, by rfl⟩ : syracuseStep 659999 = 989999) B989999
theorem B660207 : Blo 658307 660207 := bstep (se 1 (by rfl) ⟨495155, by rfl⟩ : syracuseStep 660207 = 990311) B990311
theorem B660839 : Blo 658307 660839 := bstep (se 1 (by rfl) ⟨495629, by rfl⟩ : syracuseStep 660839 = 991259) B991259
theorem B988667 : Blo 658307 988667 := bstep (se 1 (by rfl) ⟨741500, by rfl⟩ : syracuseStep 988667 = 1483001) B1483001
theorem B988841 : Blo 658307 988841 := bstep (se 2 (by rfl) ⟨370815, by rfl⟩ : syracuseStep 988841 = 741631) B741631
theorem B988967 : Blo 658307 988967 := bstep (se 1 (by rfl) ⟨741725, by rfl⟩ : syracuseStep 988967 = 1483451) B1483451
theorem B10852163 : Blo 658307 10852163 := bstep (se 1 (by rfl) ⟨8139122, by rfl⟩ : syracuseStep 10852163 = 16278245) B16278245
theorem B1482281 : Blo 658307 1482281 := bstep (se 2 (by rfl) ⟨555855, by rfl⟩ : syracuseStep 1482281 = 1111711) B1111711
theorem B24125039 : Blo 658307 24125039 := bstep (se 1 (by rfl) ⟨18093779, by rfl⟩ : syracuseStep 24125039 = 36187559) B36187559
theorem B991079 : Blo 658307 991079 := bstep (se 1 (by rfl) ⟨743309, by rfl⟩ : syracuseStep 991079 = 1486619) B1486619
theorem B1484855 : Blo 658307 1484855 := bstep (se 1 (by rfl) ⟨1113641, by rfl⟩ : syracuseStep 1484855 = 2227283) B2227283
theorem B993449 : Blo 658307 993449 := bstep (se 2 (by rfl) ⟨372543, by rfl⟩ : syracuseStep 993449 = 745087) B745087
theorem B87861455 : Blo 658307 87861455 := bstep (se 1 (by rfl) ⟨65896091, by rfl⟩ : syracuseStep 87861455 = 131792183) B131792183
theorem B1257191 : Blo 658307 1257191 := bstep (se 1 (by rfl) ⟨942893, by rfl⟩ : syracuseStep 1257191 = 1885787) B1885787
theorem B1488095 : Blo 658307 1488095 := bstep (se 1 (by rfl) ⟨1116071, by rfl⟩ : syracuseStep 1488095 = 2232143) B2232143
theorem B11254301 : Blo 658307 11254301 := bstep (se 3 (by rfl) ⟨2110181, by rfl⟩ : syracuseStep 11254301 = 4220363) B4220363
theorem B1884215 : Blo 658307 1884215 := bstep (se 1 (by rfl) ⟨1413161, by rfl⟩ : syracuseStep 1884215 = 2826323) B2826323
theorem B1884671 : Blo 658307 1884671 := bstep (se 1 (by rfl) ⟨1413503, by rfl⟩ : syracuseStep 1884671 = 2827007) B2827007
theorem B6342695 : Blo 658307 6342695 := bstep (se 1 (by rfl) ⟨4757021, by rfl⟩ : syracuseStep 6342695 = 9514043) B9514043
theorem B97897247 : Blo 658307 97897247 := bstep (se 1 (by rfl) ⟨73422935, by rfl⟩ : syracuseStep 97897247 = 146845871) B146845871
theorem B21385579 : Blo 658307 21385579 := bstep (se 1 (by rfl) ⟨16039184, by rfl⟩ : syracuseStep 21385579 = 32078369) B32078369
theorem B3167657 : Blo 658307 3167657 := bstep (se 2 (by rfl) ⟨1187871, by rfl⟩ : syracuseStep 3167657 = 2375743) B2375743
theorem B4773629 : Blo 658307 4773629 := bstep (se 3 (by rfl) ⟨895055, by rfl⟩ : syracuseStep 4773629 = 1790111) B1790111
theorem B9493631 : Blo 658307 9493631 := bstep (se 1 (by rfl) ⟨7120223, by rfl⟩ : syracuseStep 9493631 = 14240447) B14240447
theorem B6350501 : Blo 658307 6350501 := bstep (se 4 (by rfl) ⟨595359, by rfl⟩ : syracuseStep 6350501 = 1190719) B1190719
theorem B3336065 : Blo 658307 3336065 := bstep (se 2 (by rfl) ⟨1251024, by rfl⟩ : syracuseStep 3336065 = 2502049) B2502049
theorem B73263133 : Blo 658307 73263133 := bstep (se 3 (by rfl) ⟨13736837, by rfl⟩ : syracuseStep 73263133 = 27473675) B27473675
theorem B2813561 : Blo 658307 2813561 := bstep (se 2 (by rfl) ⟨1055085, by rfl⟩ : syracuseStep 2813561 = 2110171) B2110171
theorem B2227391 : Blo 658307 2227391 := bstep (se 1 (by rfl) ⟨1670543, by rfl⟩ : syracuseStep 2227391 = 3341087) B3341087
theorem B4228463 : Blo 658307 4228463 := bstep (se 1 (by rfl) ⟨3171347, by rfl⟩ : syracuseStep 4228463 = 6342695) B6342695
theorem B97684177 : Blo 658307 97684177 := bstep (se 2 (by rfl) ⟨36631566, by rfl⟩ : syracuseStep 97684177 = 73263133) B73263133
theorem B659111 : Blo 658307 659111 := bstep (se 1 (by rfl) ⟨494333, by rfl⟩ : syracuseStep 659111 = 988667) B988667
theorem B659227 : Blo 658307 659227 := bstep (se 1 (by rfl) ⟨494420, by rfl⟩ : syracuseStep 659227 = 988841) B988841
theorem B3182419 : Blo 658307 3182419 := bstep (se 1 (by rfl) ⟨2386814, by rfl⟩ : syracuseStep 3182419 = 4773629) B4773629
theorem B659311 : Blo 658307 659311 := bstep (se 1 (by rfl) ⟨494483, by rfl⟩ : syracuseStep 659311 = 988967) B988967
theorem B6329087 : Blo 658307 6329087 := bstep (se 1 (by rfl) ⟨4746815, by rfl⟩ : syracuseStep 6329087 = 9493631) B9493631
theorem B988187 : Blo 658307 988187 := bstep (se 1 (by rfl) ⟨741140, by rfl⟩ : syracuseStep 988187 = 1482281) B1482281
theorem B660719 : Blo 658307 660719 := bstep (se 1 (by rfl) ⟨495539, by rfl⟩ : syracuseStep 660719 = 991079) B991079
theorem B28514105 : Blo 658307 28514105 := bstep (se 2 (by rfl) ⟨10692789, by rfl⟩ : syracuseStep 28514105 = 21385579) B21385579
theorem B4233667 : Blo 658307 4233667 := bstep (se 1 (by rfl) ⟨3175250, by rfl⟩ : syracuseStep 4233667 = 6350501) B6350501
theorem B989903 : Blo 658307 989903 := bstep (se 1 (by rfl) ⟨742427, by rfl⟩ : syracuseStep 989903 = 1484855) B1484855
theorem B662299 : Blo 658307 662299 := bstep (se 1 (by rfl) ⟨496724, by rfl⟩ : syracuseStep 662299 = 993449) B993449
theorem B1875707 : Blo 658307 1875707 := bstep (se 1 (by rfl) ⟨1406780, by rfl⟩ : syracuseStep 1875707 = 2813561) B2813561
theorem B992063 : Blo 658307 992063 := bstep (se 1 (by rfl) ⟨744047, by rfl⟩ : syracuseStep 992063 = 1488095) B1488095
theorem B1484927 : Blo 658307 1484927 := bstep (se 1 (by rfl) ⟨1113695, by rfl⟩ : syracuseStep 1484927 = 2227391) B2227391
theorem B1256143 : Blo 658307 1256143 := bstep (se 1 (by rfl) ⟨942107, by rfl⟩ : syracuseStep 1256143 = 1884215) B1884215
theorem B9186301 : Blo 658307 9186301 := bstep (se 3 (by rfl) ⟨1722431, by rfl⟩ : syracuseStep 9186301 = 3444863) B3444863
theorem B1256447 : Blo 658307 1256447 := bstep (se 1 (by rfl) ⟨942335, by rfl⟩ : syracuseStep 1256447 = 1884671) B1884671
theorem B1486601 : Blo 658307 1486601 := bstep (se 2 (by rfl) ⟨557475, by rfl⟩ : syracuseStep 1486601 = 1114951) B1114951
theorem B6009335 : Blo 658307 6009335 := bstep (se 1 (by rfl) ⟨4507001, by rfl⟩ : syracuseStep 6009335 = 9014003) B9014003
theorem B2111771 : Blo 658307 2111771 := bstep (se 1 (by rfl) ⟨1583828, by rfl⟩ : syracuseStep 2111771 = 3167657) B3167657
theorem B58574303 : Blo 658307 58574303 := bstep (se 1 (by rfl) ⟨43930727, by rfl⟩ : syracuseStep 58574303 = 87861455) B87861455
theorem B838127 : Blo 658307 838127 := bstep (se 1 (by rfl) ⟨628595, by rfl⟩ : syracuseStep 838127 = 1257191) B1257191
theorem B1267103 : Blo 658307 1267103 := bstep (se 1 (by rfl) ⟨950327, by rfl⟩ : syracuseStep 1267103 = 1900655) B1900655
theorem B744223 : Blo 658307 744223 := bstep (se 1 (by rfl) ⟨558167, by rfl⟩ : syracuseStep 744223 = 1116335) B1116335
theorem B65264831 : Blo 658307 65264831 := bstep (se 1 (by rfl) ⟨48948623, by rfl⟩ : syracuseStep 65264831 = 97897247) B97897247
theorem B7234775 : Blo 658307 7234775 := bstep (se 1 (by rfl) ⟨5426081, by rfl⟩ : syracuseStep 7234775 = 10852163) B10852163
theorem B16083359 : Blo 658307 16083359 := bstep (se 1 (by rfl) ⟨12062519, by rfl⟩ : syracuseStep 16083359 = 24125039) B24125039
theorem B2224043 : Blo 658307 2224043 := bstep (se 1 (by rfl) ⟨1668032, by rfl⟩ : syracuseStep 2224043 = 3336065) B3336065
theorem B7502867 : Blo 658307 7502867 := bstep (se 1 (by rfl) ⟨5627150, by rfl⟩ : syracuseStep 7502867 = 11254301) B11254301
theorem B2818975 : Blo 658307 2818975 := bstep (se 1 (by rfl) ⟨2114231, by rfl⟩ : syracuseStep 2818975 = 4228463) B4228463
theorem B658791 : Blo 658307 658791 := bstep (se 1 (by rfl) ⟨494093, by rfl⟩ : syracuseStep 658791 = 988187) B988187
theorem B1674857 : Blo 658307 1674857 := bstep (se 2 (by rfl) ⟨628071, by rfl⟩ : syracuseStep 1674857 = 1256143) B1256143
theorem B19009403 : Blo 658307 19009403 := bstep (se 1 (by rfl) ⟨14257052, by rfl⟩ : syracuseStep 19009403 = 28514105) B28514105
theorem B659935 : Blo 658307 659935 := bstep (se 1 (by rfl) ⟨494951, by rfl⟩ : syracuseStep 659935 = 989903) B989903
theorem B1250471 : Blo 658307 1250471 := bstep (se 1 (by rfl) ⟨937853, by rfl⟩ : syracuseStep 1250471 = 1875707) B1875707
theorem B661375 : Blo 658307 661375 := bstep (se 1 (by rfl) ⟨496031, by rfl⟩ : syracuseStep 661375 = 992063) B992063
theorem B4823183 : Blo 658307 4823183 := bstep (se 1 (by rfl) ⟨3617387, by rfl⟩ : syracuseStep 4823183 = 7234775) B7234775
theorem B2235005 : Blo 658307 2235005 := bstep (se 3 (by rfl) ⟨419063, by rfl⟩ : syracuseStep 2235005 = 838127) B838127
theorem B989951 : Blo 658307 989951 := bstep (se 1 (by rfl) ⟨742463, by rfl⟩ : syracuseStep 989951 = 1484927) B1484927
theorem B10722239 : Blo 658307 10722239 := bstep (se 1 (by rfl) ⟨8041679, by rfl⟩ : syracuseStep 10722239 = 16083359) B16083359
theorem B991067 : Blo 658307 991067 := bstep (se 1 (by rfl) ⟨743300, by rfl⟩ : syracuseStep 991067 = 1486601) B1486601
theorem B1482695 : Blo 658307 1482695 := bstep (se 1 (by rfl) ⟨1112021, by rfl⟩ : syracuseStep 1482695 = 2224043) B2224043
theorem B4006223 : Blo 658307 4006223 := bstep (se 1 (by rfl) ⟨3004667, by rfl⟩ : syracuseStep 4006223 = 6009335) B6009335
theorem B5644889 : Blo 658307 5644889 := bstep (se 2 (by rfl) ⟨2116833, by rfl⟩ : syracuseStep 5644889 = 4233667) B4233667
theorem B992297 : Blo 658307 992297 := bstep (se 2 (by rfl) ⟨372111, by rfl⟩ : syracuseStep 992297 = 744223) B744223
theorem B4243225 : Blo 658307 4243225 := bstep (se 2 (by rfl) ⟨1591209, by rfl⟩ : syracuseStep 4243225 = 3182419) B3182419
theorem B837631 : Blo 658307 837631 := bstep (se 1 (by rfl) ⟨628223, by rfl⟩ : syracuseStep 837631 = 1256447) B1256447
theorem B5001911 : Blo 658307 5001911 := bstep (se 1 (by rfl) ⟨3751433, by rfl⟩ : syracuseStep 5001911 = 7502867) B7502867
theorem B39049535 : Blo 658307 39049535 := bstep (se 1 (by rfl) ⟨29287151, by rfl⟩ : syracuseStep 39049535 = 58574303) B58574303
theorem B4219391 : Blo 658307 4219391 := bstep (se 1 (by rfl) ⟨3164543, by rfl⟩ : syracuseStep 4219391 = 6329087) B6329087
theorem B844735 : Blo 658307 844735 := bstep (se 1 (by rfl) ⟨633551, by rfl⟩ : syracuseStep 844735 = 1267103) B1267103
theorem B130245569 : Blo 658307 130245569 := bstep (se 2 (by rfl) ⟨48842088, by rfl⟩ : syracuseStep 130245569 = 97684177) B97684177
theorem B12248401 : Blo 658307 12248401 := bstep (se 2 (by rfl) ⟨4593150, by rfl⟩ : syracuseStep 12248401 = 9186301) B9186301
theorem B43509887 : Blo 658307 43509887 := bstep (se 1 (by rfl) ⟨32632415, by rfl⟩ : syracuseStep 43509887 = 65264831) B65264831
theorem B5631389 : Blo 658307 5631389 := bstep (se 3 (by rfl) ⟨1055885, by rfl⟩ : syracuseStep 5631389 = 2111771) B2111771
theorem B1116571 : Blo 658307 1116571 := bstep (se 1 (by rfl) ⟨837428, by rfl⟩ : syracuseStep 1116571 = 1674857) B1674857
theorem B1116841 : Blo 658307 1116841 := bstep (se 2 (by rfl) ⟨418815, by rfl⟩ : syracuseStep 1116841 = 837631) B837631
theorem B659967 : Blo 658307 659967 := bstep (se 1 (by rfl) ⟨494975, by rfl⟩ : syracuseStep 659967 = 989951) B989951
theorem B7148159 : Blo 658307 7148159 := bstep (se 1 (by rfl) ⟨5361119, by rfl⟩ : syracuseStep 7148159 = 10722239) B10722239
theorem B660711 : Blo 658307 660711 := bstep (se 1 (by rfl) ⟨495533, by rfl⟩ : syracuseStep 660711 = 991067) B991067
theorem B988463 : Blo 658307 988463 := bstep (se 1 (by rfl) ⟨741347, by rfl⟩ : syracuseStep 988463 = 1482695) B1482695
theorem B661531 : Blo 658307 661531 := bstep (se 1 (by rfl) ⟨496148, by rfl⟩ : syracuseStep 661531 = 992297) B992297
theorem B29006591 : Blo 658307 29006591 := bstep (se 1 (by rfl) ⟨21754943, by rfl⟩ : syracuseStep 29006591 = 43509887) B43509887
theorem B1126313 : Blo 658307 1126313 := bstep (se 2 (by rfl) ⟨422367, by rfl⟩ : syracuseStep 1126313 = 844735) B844735
theorem B16331201 : Blo 658307 16331201 := bstep (se 2 (by rfl) ⟨6124200, by rfl⟩ : syracuseStep 16331201 = 12248401) B12248401
theorem B833647 : Blo 658307 833647 := bstep (se 1 (by rfl) ⟨625235, by rfl⟩ : syracuseStep 833647 = 1250471) B1250471
theorem B26033023 : Blo 658307 26033023 := bstep (se 1 (by rfl) ⟨19524767, by rfl⟩ : syracuseStep 26033023 = 39049535) B39049535
theorem B1490003 : Blo 658307 1490003 := bstep (se 1 (by rfl) ⟨1117502, by rfl⟩ : syracuseStep 1490003 = 2235005) B2235005
theorem B2670815 : Blo 658307 2670815 := bstep (se 1 (by rfl) ⟨2003111, by rfl⟩ : syracuseStep 2670815 = 4006223) B4006223
theorem B12861821 : Blo 658307 12861821 := bstep (se 3 (by rfl) ⟨2411591, by rfl⟩ : syracuseStep 12861821 = 4823183) B4823183
theorem B3754259 : Blo 658307 3754259 := bstep (se 1 (by rfl) ⟨2815694, by rfl⟩ : syracuseStep 3754259 = 5631389) B5631389
theorem B5657633 : Blo 658307 5657633 := bstep (se 2 (by rfl) ⟨2121612, by rfl⟩ : syracuseStep 5657633 = 4243225) B4243225
theorem B3758633 : Blo 658307 3758633 := bstep (se 2 (by rfl) ⟨1409487, by rfl⟩ : syracuseStep 3758633 = 2818975) B2818975
theorem B12672935 : Blo 658307 12672935 := bstep (se 1 (by rfl) ⟨9504701, by rfl⟩ : syracuseStep 12672935 = 19009403) B19009403
theorem B3334607 : Blo 658307 3334607 := bstep (se 1 (by rfl) ⟨2500955, by rfl⟩ : syracuseStep 3334607 = 5001911) B5001911
theorem B2812927 : Blo 658307 2812927 := bstep (se 1 (by rfl) ⟨2109695, by rfl⟩ : syracuseStep 2812927 = 4219391) B4219391
theorem B3763259 : Blo 658307 3763259 := bstep (se 1 (by rfl) ⟨2822444, by rfl⟩ : syracuseStep 3763259 = 5644889) B5644889
theorem B86830379 : Blo 658307 86830379 := bstep (se 1 (by rfl) ⟨65122784, by rfl⟩ : syracuseStep 86830379 = 130245569) B130245569
theorem B3771755 : Blo 658307 3771755 := bstep (se 1 (by rfl) ⟨2828816, by rfl⟩ : syracuseStep 3771755 = 5657633) B5657633
theorem B658975 : Blo 658307 658975 := bstep (se 1 (by rfl) ⟨494231, by rfl⟩ : syracuseStep 658975 = 988463) B988463
theorem B10887467 : Blo 658307 10887467 := bstep (se 1 (by rfl) ⟨8165600, by rfl⟩ : syracuseStep 10887467 = 16331201) B16331201
theorem B34710697 : Blo 658307 34710697 := bstep (se 2 (by rfl) ⟨13016511, by rfl⟩ : syracuseStep 34710697 = 26033023) B26033023
theorem B993335 : Blo 658307 993335 := bstep (se 1 (by rfl) ⟨745001, by rfl⟩ : syracuseStep 993335 = 1490003) B1490003
theorem B1780543 : Blo 658307 1780543 := bstep (se 1 (by rfl) ⟨1335407, by rfl⟩ : syracuseStep 1780543 = 2670815) B2670815
theorem B2502839 : Blo 658307 2502839 := bstep (se 1 (by rfl) ⟨1877129, by rfl⟩ : syracuseStep 2502839 = 3754259) B3754259
theorem B4765439 : Blo 658307 4765439 := bstep (se 1 (by rfl) ⟨3574079, by rfl⟩ : syracuseStep 4765439 = 7148159) B7148159
theorem B1488761 : Blo 658307 1488761 := bstep (se 2 (by rfl) ⟨558285, by rfl⟩ : syracuseStep 1488761 = 1116571) B1116571
theorem B1489121 : Blo 658307 1489121 := bstep (se 2 (by rfl) ⟨558420, by rfl⟩ : syracuseStep 1489121 = 1116841) B1116841
theorem B3750569 : Blo 658307 3750569 := bstep (se 2 (by rfl) ⟨1406463, by rfl⟩ : syracuseStep 3750569 = 2812927) B2812927
theorem B2505755 : Blo 658307 2505755 := bstep (se 1 (by rfl) ⟨1879316, by rfl⟩ : syracuseStep 2505755 = 3758633) B3758633
theorem B77350909 : Blo 658307 77350909 := bstep (se 3 (by rfl) ⟨14503295, by rfl⟩ : syracuseStep 77350909 = 29006591) B29006591
theorem B2508839 : Blo 658307 2508839 := bstep (se 1 (by rfl) ⟨1881629, by rfl⟩ : syracuseStep 2508839 = 3763259) B3763259
theorem B57886919 : Blo 658307 57886919 := bstep (se 1 (by rfl) ⟨43415189, by rfl⟩ : syracuseStep 57886919 = 86830379) B86830379
theorem B8574547 : Blo 658307 8574547 := bstep (se 1 (by rfl) ⟨6430910, by rfl⟩ : syracuseStep 8574547 = 12861821) B12861821
theorem B8448623 : Blo 658307 8448623 := bstep (se 1 (by rfl) ⟨6336467, by rfl⟩ : syracuseStep 8448623 = 12672935) B12672935
theorem B2223071 : Blo 658307 2223071 := bstep (se 1 (by rfl) ⟨1667303, by rfl⟩ : syracuseStep 2223071 = 3334607) B3334607
theorem B750875 : Blo 658307 750875 := bstep (se 1 (by rfl) ⟨563156, by rfl⟩ : syracuseStep 750875 = 1126313) B1126313
theorem B1111529 : Blo 658307 1111529 := bstep (se 2 (by rfl) ⟨416823, by rfl⟩ : syracuseStep 1111529 = 833647) B833647
theorem B29033245 : Blo 658307 29033245 := bstep (se 3 (by rfl) ⟨5443733, by rfl⟩ : syracuseStep 29033245 = 10887467) B10887467
theorem B1672559 : Blo 658307 1672559 := bstep (se 1 (by rfl) ⟨1254419, by rfl⟩ : syracuseStep 1672559 = 2508839) B2508839
theorem B2002333 : Blo 658307 2002333 := bstep (se 3 (by rfl) ⟨375437, by rfl⟩ : syracuseStep 2002333 = 750875) B750875
theorem B662223 : Blo 658307 662223 := bstep (se 1 (by rfl) ⟨496667, by rfl⟩ : syracuseStep 662223 = 993335) B993335
theorem B1482047 : Blo 658307 1482047 := bstep (se 1 (by rfl) ⟨1111535, by rfl⟩ : syracuseStep 1482047 = 2223071) B2223071
theorem B992507 : Blo 658307 992507 := bstep (se 1 (by rfl) ⟨744380, by rfl⟩ : syracuseStep 992507 = 1488761) B1488761
theorem B992747 : Blo 658307 992747 := bstep (se 1 (by rfl) ⟨744560, by rfl⟩ : syracuseStep 992747 = 1489121) B1489121
theorem B2500379 : Blo 658307 2500379 := bstep (se 1 (by rfl) ⟨1875284, by rfl⟩ : syracuseStep 2500379 = 3750569) B3750569
theorem B46280929 : Blo 658307 46280929 := bstep (se 2 (by rfl) ⟨17355348, by rfl⟩ : syracuseStep 46280929 = 34710697) B34710697
theorem B103134545 : Blo 658307 103134545 := bstep (se 2 (by rfl) ⟨38675454, by rfl⟩ : syracuseStep 103134545 = 77350909) B77350909
theorem B2374057 : Blo 658307 2374057 := bstep (se 2 (by rfl) ⟨890271, by rfl⟩ : syracuseStep 2374057 = 1780543) B1780543
theorem B741019 : Blo 658307 741019 := bstep (se 1 (by rfl) ⟨555764, by rfl⟩ : syracuseStep 741019 = 1111529) B1111529
theorem B38591279 : Blo 658307 38591279 := bstep (se 1 (by rfl) ⟨28943459, by rfl⟩ : syracuseStep 38591279 = 57886919) B57886919
theorem B2514503 : Blo 658307 2514503 := bstep (se 1 (by rfl) ⟨1885877, by rfl⟩ : syracuseStep 2514503 = 3771755) B3771755
theorem B12707837 : Blo 658307 12707837 := bstep (se 3 (by rfl) ⟨2382719, by rfl⟩ : syracuseStep 12707837 = 4765439) B4765439
theorem B5632415 : Blo 658307 5632415 := bstep (se 1 (by rfl) ⟨4224311, by rfl⟩ : syracuseStep 5632415 = 8448623) B8448623
theorem B11432729 : Blo 658307 11432729 := bstep (se 2 (by rfl) ⟨4287273, by rfl⟩ : syracuseStep 11432729 = 8574547) B8574547
theorem B1668559 : Blo 658307 1668559 := bstep (se 1 (by rfl) ⟨1251419, by rfl⟩ : syracuseStep 1668559 = 2502839) B2502839
theorem B1670503 : Blo 658307 1670503 := bstep (se 1 (by rfl) ⟨1252877, by rfl⟩ : syracuseStep 1670503 = 2505755) B2505755
theorem B1115039 : Blo 658307 1115039 := bstep (se 1 (by rfl) ⟨836279, by rfl⟩ : syracuseStep 1115039 = 1672559) B1672559
theorem B25727519 : Blo 658307 25727519 := bstep (se 1 (by rfl) ⟨19295639, by rfl⟩ : syracuseStep 25727519 = 38591279) B38591279
theorem B988025 : Blo 658307 988025 := bstep (se 2 (by rfl) ⟨370509, by rfl⟩ : syracuseStep 988025 = 741019) B741019
theorem B988031 : Blo 658307 988031 := bstep (se 1 (by rfl) ⟨741023, by rfl⟩ : syracuseStep 988031 = 1482047) B1482047
theorem B1676335 : Blo 658307 1676335 := bstep (se 1 (by rfl) ⟨1257251, by rfl⟩ : syracuseStep 1676335 = 2514503) B2514503
theorem B61707905 : Blo 658307 61707905 := bstep (se 2 (by rfl) ⟨23140464, by rfl⟩ : syracuseStep 61707905 = 46280929) B46280929
theorem B661671 : Blo 658307 661671 := bstep (se 1 (by rfl) ⟨496253, by rfl⟩ : syracuseStep 661671 = 992507) B992507
theorem B661831 : Blo 658307 661831 := bstep (se 1 (by rfl) ⟨496373, by rfl⟩ : syracuseStep 661831 = 992747) B992747
theorem B68756363 : Blo 658307 68756363 := bstep (se 1 (by rfl) ⟨51567272, by rfl⟩ : syracuseStep 68756363 = 103134545) B103134545
theorem B38710993 : Blo 658307 38710993 := bstep (se 2 (by rfl) ⟨14516622, by rfl⟩ : syracuseStep 38710993 = 29033245) B29033245
theorem B2669777 : Blo 658307 2669777 := bstep (se 2 (by rfl) ⟨1001166, by rfl⟩ : syracuseStep 2669777 = 2002333) B2002333
theorem B8471891 : Blo 658307 8471891 := bstep (se 1 (by rfl) ⟨6353918, by rfl⟩ : syracuseStep 8471891 = 12707837) B12707837
theorem B3754943 : Blo 658307 3754943 := bstep (se 1 (by rfl) ⟨2816207, by rfl⟩ : syracuseStep 3754943 = 5632415) B5632415
theorem B7621819 : Blo 658307 7621819 := bstep (se 1 (by rfl) ⟨5716364, by rfl⟩ : syracuseStep 7621819 = 11432729) B11432729
theorem B3165409 : Blo 658307 3165409 := bstep (se 2 (by rfl) ⟨1187028, by rfl⟩ : syracuseStep 3165409 = 2374057) B2374057
theorem B1666919 : Blo 658307 1666919 := bstep (se 1 (by rfl) ⟨1250189, by rfl⟩ : syracuseStep 1666919 = 2500379) B2500379
theorem B2224745 : Blo 658307 2224745 := bstep (se 2 (by rfl) ⟨834279, by rfl⟩ : syracuseStep 2224745 = 1668559) B1668559
theorem B2227337 : Blo 658307 2227337 := bstep (se 2 (by rfl) ⟨835251, by rfl⟩ : syracuseStep 2227337 = 1670503) B1670503
theorem B658683 : Blo 658307 658683 := bstep (se 1 (by rfl) ⟨494012, by rfl⟩ : syracuseStep 658683 = 988025) B988025
theorem B658687 : Blo 658307 658687 := bstep (se 1 (by rfl) ⟨494015, by rfl⟩ : syracuseStep 658687 = 988031) B988031
theorem B51614657 : Blo 658307 51614657 := bstep (se 2 (by rfl) ⟨19355496, by rfl⟩ : syracuseStep 51614657 = 38710993) B38710993
theorem B2235113 : Blo 658307 2235113 := bstep (se 2 (by rfl) ⟨838167, by rfl⟩ : syracuseStep 2235113 = 1676335) B1676335
theorem B1483163 : Blo 658307 1483163 := bstep (se 1 (by rfl) ⟨1112372, by rfl⟩ : syracuseStep 1483163 = 2224745) B2224745
theorem B1484891 : Blo 658307 1484891 := bstep (se 1 (by rfl) ⟨1113668, by rfl⟩ : syracuseStep 1484891 = 2227337) B2227337
theorem B1779851 : Blo 658307 1779851 := bstep (se 1 (by rfl) ⟨1334888, by rfl⟩ : syracuseStep 1779851 = 2669777) B2669777
theorem B5647927 : Blo 658307 5647927 := bstep (se 1 (by rfl) ⟨4235945, by rfl⟩ : syracuseStep 5647927 = 8471891) B8471891
theorem B2503295 : Blo 658307 2503295 := bstep (se 1 (by rfl) ⟨1877471, by rfl⟩ : syracuseStep 2503295 = 3754943) B3754943
theorem B17151679 : Blo 658307 17151679 := bstep (se 1 (by rfl) ⟨12863759, by rfl⟩ : syracuseStep 17151679 = 25727519) B25727519
theorem B41138603 : Blo 658307 41138603 := bstep (se 1 (by rfl) ⟨30853952, by rfl⟩ : syracuseStep 41138603 = 61707905) B61707905
theorem B40649701 : Blo 658307 40649701 := bstep (se 4 (by rfl) ⟨3810909, by rfl⟩ : syracuseStep 40649701 = 7621819) B7621819
theorem B743359 : Blo 658307 743359 := bstep (se 1 (by rfl) ⟨557519, by rfl⟩ : syracuseStep 743359 = 1115039) B1115039
theorem B4220545 : Blo 658307 4220545 := bstep (se 2 (by rfl) ⟨1582704, by rfl⟩ : syracuseStep 4220545 = 3165409) B3165409
theorem B45837575 : Blo 658307 45837575 := bstep (se 1 (by rfl) ⟨34378181, by rfl⟩ : syracuseStep 45837575 = 68756363) B68756363
theorem B1111279 : Blo 658307 1111279 := bstep (se 1 (by rfl) ⟨833459, by rfl⟩ : syracuseStep 1111279 = 1666919) B1666919
theorem B54199601 : Blo 658307 54199601 := bstep (se 2 (by rfl) ⟨20324850, by rfl⟩ : syracuseStep 54199601 = 40649701) B40649701
theorem B34409771 : Blo 658307 34409771 := bstep (se 1 (by rfl) ⟨25807328, by rfl⟩ : syracuseStep 34409771 = 51614657) B51614657
theorem B988775 : Blo 658307 988775 := bstep (se 1 (by rfl) ⟨741581, by rfl⟩ : syracuseStep 988775 = 1483163) B1483163
theorem B989927 : Blo 658307 989927 := bstep (se 1 (by rfl) ⟨742445, by rfl⟩ : syracuseStep 989927 = 1484891) B1484891
theorem B1481705 : Blo 658307 1481705 := bstep (se 2 (by rfl) ⟨555639, by rfl⟩ : syracuseStep 1481705 = 1111279) B1111279
theorem B991145 : Blo 658307 991145 := bstep (se 2 (by rfl) ⟨371679, by rfl⟩ : syracuseStep 991145 = 743359) B743359
theorem B1490075 : Blo 658307 1490075 := bstep (se 1 (by rfl) ⟨1117556, by rfl⟩ : syracuseStep 1490075 = 2235113) B2235113
theorem B30558383 : Blo 658307 30558383 := bstep (se 1 (by rfl) ⟨22918787, by rfl⟩ : syracuseStep 30558383 = 45837575) B45837575
theorem B5627393 : Blo 658307 5627393 := bstep (se 2 (by rfl) ⟨2110272, by rfl⟩ : syracuseStep 5627393 = 4220545) B4220545
theorem B7530569 : Blo 658307 7530569 := bstep (se 2 (by rfl) ⟨2823963, by rfl⟩ : syracuseStep 7530569 = 5647927) B5647927
theorem B4746269 : Blo 658307 4746269 := bstep (se 3 (by rfl) ⟨889925, by rfl⟩ : syracuseStep 4746269 = 1779851) B1779851
theorem B22868905 : Blo 658307 22868905 := bstep (se 2 (by rfl) ⟨8575839, by rfl⟩ : syracuseStep 22868905 = 17151679) B17151679
theorem B1668863 : Blo 658307 1668863 := bstep (se 1 (by rfl) ⟨1251647, by rfl⟩ : syracuseStep 1668863 = 2503295) B2503295
theorem B27425735 : Blo 658307 27425735 := bstep (se 1 (by rfl) ⟨20569301, by rfl⟩ : syracuseStep 27425735 = 41138603) B41138603
theorem B22939847 : Blo 658307 22939847 := bstep (se 1 (by rfl) ⟨17204885, by rfl⟩ : syracuseStep 22939847 = 34409771) B34409771
theorem B659183 : Blo 658307 659183 := bstep (se 1 (by rfl) ⟨494387, by rfl⟩ : syracuseStep 659183 = 988775) B988775
theorem B659951 : Blo 658307 659951 := bstep (se 1 (by rfl) ⟨494963, by rfl⟩ : syracuseStep 659951 = 989927) B989927
theorem B987803 : Blo 658307 987803 := bstep (se 1 (by rfl) ⟨740852, by rfl⟩ : syracuseStep 987803 = 1481705) B1481705
theorem B660763 : Blo 658307 660763 := bstep (se 1 (by rfl) ⟨495572, by rfl⟩ : syracuseStep 660763 = 991145) B991145
theorem B5020379 : Blo 658307 5020379 := bstep (se 1 (by rfl) ⟨3765284, by rfl⟩ : syracuseStep 5020379 = 7530569) B7530569
theorem B993383 : Blo 658307 993383 := bstep (se 1 (by rfl) ⟨745037, by rfl⟩ : syracuseStep 993383 = 1490075) B1490075
theorem B3751595 : Blo 658307 3751595 := bstep (se 1 (by rfl) ⟨2813696, by rfl⟩ : syracuseStep 3751595 = 5627393) B5627393
theorem B30491873 : Blo 658307 30491873 := bstep (se 2 (by rfl) ⟨11434452, by rfl⟩ : syracuseStep 30491873 = 22868905) B22868905
theorem B3164179 : Blo 658307 3164179 := bstep (se 1 (by rfl) ⟨2373134, by rfl⟩ : syracuseStep 3164179 = 4746269) B4746269
theorem B36133067 : Blo 658307 36133067 := bstep (se 1 (by rfl) ⟨27099800, by rfl⟩ : syracuseStep 36133067 = 54199601) B54199601
theorem B20372255 : Blo 658307 20372255 := bstep (se 1 (by rfl) ⟨15279191, by rfl⟩ : syracuseStep 20372255 = 30558383) B30558383
theorem B1112575 : Blo 658307 1112575 := bstep (se 1 (by rfl) ⟨834431, by rfl⟩ : syracuseStep 1112575 = 1668863) B1668863
theorem B18283823 : Blo 658307 18283823 := bstep (se 1 (by rfl) ⟨13712867, by rfl⟩ : syracuseStep 18283823 = 27425735) B27425735
theorem B658535 : Blo 658307 658535 := bstep (se 1 (by rfl) ⟨493901, by rfl⟩ : syracuseStep 658535 = 987803) B987803
theorem B24088711 : Blo 658307 24088711 := bstep (se 1 (by rfl) ⟨18066533, by rfl⟩ : syracuseStep 24088711 = 36133067) B36133067
theorem B3346919 : Blo 658307 3346919 := bstep (se 1 (by rfl) ⟨2510189, by rfl⟩ : syracuseStep 3346919 = 5020379) B5020379
theorem B662255 : Blo 658307 662255 := bstep (se 1 (by rfl) ⟨496691, by rfl⟩ : syracuseStep 662255 = 993383) B993383
theorem B1483433 : Blo 658307 1483433 := bstep (se 2 (by rfl) ⟨556287, by rfl⟩ : syracuseStep 1483433 = 1112575) B1112575
theorem B2501063 : Blo 658307 2501063 := bstep (se 1 (by rfl) ⟨1875797, by rfl⟩ : syracuseStep 2501063 = 3751595) B3751595
theorem B20327915 : Blo 658307 20327915 := bstep (se 1 (by rfl) ⟨15245936, by rfl⟩ : syracuseStep 20327915 = 30491873) B30491873
theorem B13581503 : Blo 658307 13581503 := bstep (se 1 (by rfl) ⟨10186127, by rfl⟩ : syracuseStep 13581503 = 20372255) B20372255
theorem B15293231 : Blo 658307 15293231 := bstep (se 1 (by rfl) ⟨11469923, by rfl⟩ : syracuseStep 15293231 = 22939847) B22939847
theorem B4218905 : Blo 658307 4218905 := bstep (se 2 (by rfl) ⟨1582089, by rfl⟩ : syracuseStep 4218905 = 3164179) B3164179
theorem B12189215 : Blo 658307 12189215 := bstep (se 1 (by rfl) ⟨9141911, by rfl⟩ : syracuseStep 12189215 = 18283823) B18283823
theorem B2231279 : Blo 658307 2231279 := bstep (se 1 (by rfl) ⟨1673459, by rfl⟩ : syracuseStep 2231279 = 3346919) B3346919
theorem B10195487 : Blo 658307 10195487 := bstep (se 1 (by rfl) ⟨7646615, by rfl⟩ : syracuseStep 10195487 = 15293231) B15293231
theorem B32118281 : Blo 658307 32118281 := bstep (se 2 (by rfl) ⟨12044355, by rfl⟩ : syracuseStep 32118281 = 24088711) B24088711
theorem B988955 : Blo 658307 988955 := bstep (se 1 (by rfl) ⟨741716, by rfl⟩ : syracuseStep 988955 = 1483433) B1483433
theorem B9054335 : Blo 658307 9054335 := bstep (se 1 (by rfl) ⟨6790751, by rfl⟩ : syracuseStep 9054335 = 13581503) B13581503
theorem B13551943 : Blo 658307 13551943 := bstep (se 1 (by rfl) ⟨10163957, by rfl⟩ : syracuseStep 13551943 = 20327915) B20327915
theorem B2812603 : Blo 658307 2812603 := bstep (se 1 (by rfl) ⟨2109452, by rfl⟩ : syracuseStep 2812603 = 4218905) B4218905
theorem B1667375 : Blo 658307 1667375 := bstep (se 1 (by rfl) ⟨1250531, by rfl⟩ : syracuseStep 1667375 = 2501063) B2501063
theorem B8126143 : Blo 658307 8126143 := bstep (se 1 (by rfl) ⟨6094607, by rfl⟩ : syracuseStep 8126143 = 12189215) B12189215
theorem B659303 : Blo 658307 659303 := bstep (se 1 (by rfl) ⟨494477, by rfl⟩ : syracuseStep 659303 = 988955) B988955
theorem B6036223 : Blo 658307 6036223 := bstep (se 1 (by rfl) ⟨4527167, by rfl⟩ : syracuseStep 6036223 = 9054335) B9054335
theorem B1487519 : Blo 658307 1487519 := bstep (se 1 (by rfl) ⟨1115639, by rfl⟩ : syracuseStep 1487519 = 2231279) B2231279
theorem B6796991 : Blo 658307 6796991 := bstep (se 1 (by rfl) ⟨5097743, by rfl⟩ : syracuseStep 6796991 = 10195487) B10195487
theorem B18069257 : Blo 658307 18069257 := bstep (se 2 (by rfl) ⟨6775971, by rfl⟩ : syracuseStep 18069257 = 13551943) B13551943
theorem B3750137 : Blo 658307 3750137 := bstep (se 2 (by rfl) ⟨1406301, by rfl⟩ : syracuseStep 3750137 = 2812603) B2812603
theorem B21412187 : Blo 658307 21412187 := bstep (se 1 (by rfl) ⟨16059140, by rfl⟩ : syracuseStep 21412187 = 32118281) B32118281
theorem B43339429 : Blo 658307 43339429 := bstep (se 4 (by rfl) ⟨4063071, by rfl⟩ : syracuseStep 43339429 = 8126143) B8126143
theorem B1111583 : Blo 658307 1111583 := bstep (se 1 (by rfl) ⟨833687, by rfl⟩ : syracuseStep 1111583 = 1667375) B1667375
theorem B18125309 : Blo 658307 18125309 := bstep (se 3 (by rfl) ⟨3398495, by rfl⟩ : syracuseStep 18125309 = 6796991) B6796991
theorem B991679 : Blo 658307 991679 := bstep (se 1 (by rfl) ⟨743759, by rfl⟩ : syracuseStep 991679 = 1487519) B1487519
theorem B2500091 : Blo 658307 2500091 := bstep (se 1 (by rfl) ⟨1875068, by rfl⟩ : syracuseStep 2500091 = 3750137) B3750137
theorem B57785905 : Blo 658307 57785905 := bstep (se 2 (by rfl) ⟨21669714, by rfl⟩ : syracuseStep 57785905 = 43339429) B43339429
theorem B8048297 : Blo 658307 8048297 := bstep (se 2 (by rfl) ⟨3018111, by rfl⟩ : syracuseStep 8048297 = 6036223) B6036223
theorem B741055 : Blo 658307 741055 := bstep (se 1 (by rfl) ⟨555791, by rfl⟩ : syracuseStep 741055 = 1111583) B1111583
theorem B12046171 : Blo 658307 12046171 := bstep (se 1 (by rfl) ⟨9034628, by rfl⟩ : syracuseStep 12046171 = 18069257) B18069257
theorem B14274791 : Blo 658307 14274791 := bstep (se 1 (by rfl) ⟨10706093, by rfl⟩ : syracuseStep 14274791 = 21412187) B21412187
theorem B988073 : Blo 658307 988073 := bstep (se 2 (by rfl) ⟨370527, by rfl⟩ : syracuseStep 988073 = 741055) B741055
theorem B16061561 : Blo 658307 16061561 := bstep (se 2 (by rfl) ⟨6023085, by rfl⟩ : syracuseStep 16061561 = 12046171) B12046171
theorem B661119 : Blo 658307 661119 := bstep (se 1 (by rfl) ⟨495839, by rfl⟩ : syracuseStep 661119 = 991679) B991679
theorem B308191493 : Blo 658307 308191493 := bstep (se 4 (by rfl) ⟨28892952, by rfl⟩ : syracuseStep 308191493 = 57785905) B57785905
theorem B9516527 : Blo 658307 9516527 := bstep (se 1 (by rfl) ⟨7137395, by rfl⟩ : syracuseStep 9516527 = 14274791) B14274791
theorem B5365531 : Blo 658307 5365531 := bstep (se 1 (by rfl) ⟨4024148, by rfl⟩ : syracuseStep 5365531 = 8048297) B8048297
theorem B12083539 : Blo 658307 12083539 := bstep (se 1 (by rfl) ⟨9062654, by rfl⟩ : syracuseStep 12083539 = 18125309) B18125309
theorem B1666727 : Blo 658307 1666727 := bstep (se 1 (by rfl) ⟨1250045, by rfl⟩ : syracuseStep 1666727 = 2500091) B2500091
theorem B658715 : Blo 658307 658715 := bstep (se 1 (by rfl) ⟨494036, by rfl⟩ : syracuseStep 658715 = 988073) B988073
theorem B205460995 : Blo 658307 205460995 := bstep (se 1 (by rfl) ⟨154095746, by rfl⟩ : syracuseStep 205460995 = 308191493) B308191493
theorem B28616165 : Blo 658307 28616165 := bstep (se 4 (by rfl) ⟨2682765, by rfl⟩ : syracuseStep 28616165 = 5365531) B5365531
theorem B6344351 : Blo 658307 6344351 := bstep (se 1 (by rfl) ⟨4758263, by rfl⟩ : syracuseStep 6344351 = 9516527) B9516527
theorem B16111385 : Blo 658307 16111385 := bstep (se 2 (by rfl) ⟨6041769, by rfl⟩ : syracuseStep 16111385 = 12083539) B12083539
theorem B10707707 : Blo 658307 10707707 := bstep (se 1 (by rfl) ⟨8030780, by rfl⟩ : syracuseStep 10707707 = 16061561) B16061561
theorem B1111151 : Blo 658307 1111151 := bstep (se 1 (by rfl) ⟨833363, by rfl⟩ : syracuseStep 1111151 = 1666727) B1666727
theorem B4229567 : Blo 658307 4229567 := bstep (se 1 (by rfl) ⟨3172175, by rfl⟩ : syracuseStep 4229567 = 6344351) B6344351
theorem B19077443 : Blo 658307 19077443 := bstep (se 1 (by rfl) ⟨14308082, by rfl⟩ : syracuseStep 19077443 = 28616165) B28616165
theorem B273947993 : Blo 658307 273947993 := bstep (se 2 (by rfl) ⟨102730497, by rfl⟩ : syracuseStep 273947993 = 205460995) B205460995
theorem B740767 : Blo 658307 740767 := bstep (se 1 (by rfl) ⟨555575, by rfl⟩ : syracuseStep 740767 = 1111151) B1111151
theorem B10740923 : Blo 658307 10740923 := bstep (se 1 (by rfl) ⟨8055692, by rfl⟩ : syracuseStep 10740923 = 16111385) B16111385
theorem B7138471 : Blo 658307 7138471 := bstep (se 1 (by rfl) ⟨5353853, by rfl⟩ : syracuseStep 7138471 = 10707707) B10707707
theorem B2819711 : Blo 658307 2819711 := bstep (se 1 (by rfl) ⟨2114783, by rfl⟩ : syracuseStep 2819711 = 4229567) B4229567
theorem B12718295 : Blo 658307 12718295 := bstep (se 1 (by rfl) ⟨9538721, by rfl⟩ : syracuseStep 12718295 = 19077443) B19077443
theorem B987689 : Blo 658307 987689 := bstep (se 2 (by rfl) ⟨370383, by rfl⟩ : syracuseStep 987689 = 740767) B740767
theorem B9517961 : Blo 658307 9517961 := bstep (se 2 (by rfl) ⟨3569235, by rfl⟩ : syracuseStep 9517961 = 7138471) B7138471
theorem B182631995 : Blo 658307 182631995 := bstep (se 1 (by rfl) ⟨136973996, by rfl⟩ : syracuseStep 182631995 = 273947993) B273947993
theorem B7160615 : Blo 658307 7160615 := bstep (se 1 (by rfl) ⟨5370461, by rfl⟩ : syracuseStep 7160615 = 10740923) B10740923
theorem B658459 : Blo 658307 658459 := bstep (se 1 (by rfl) ⟨493844, by rfl⟩ : syracuseStep 658459 = 987689) B987689
theorem B1879807 : Blo 658307 1879807 := bstep (se 1 (by rfl) ⟨1409855, by rfl⟩ : syracuseStep 1879807 = 2819711) B2819711
theorem B6345307 : Blo 658307 6345307 := bstep (se 1 (by rfl) ⟨4758980, by rfl⟩ : syracuseStep 6345307 = 9517961) B9517961
theorem B121754663 : Blo 658307 121754663 := bstep (se 1 (by rfl) ⟨91315997, by rfl⟩ : syracuseStep 121754663 = 182631995) B182631995
theorem B4773743 : Blo 658307 4773743 := bstep (se 1 (by rfl) ⟨3580307, by rfl⟩ : syracuseStep 4773743 = 7160615) B7160615
theorem B8478863 : Blo 658307 8478863 := bstep (se 1 (by rfl) ⟨6359147, by rfl⟩ : syracuseStep 8478863 = 12718295) B12718295
theorem B81169775 : Blo 658307 81169775 := bstep (se 1 (by rfl) ⟨60877331, by rfl⟩ : syracuseStep 81169775 = 121754663) B121754663
theorem B3182495 : Blo 658307 3182495 := bstep (se 1 (by rfl) ⟨2386871, by rfl⟩ : syracuseStep 3182495 = 4773743) B4773743
theorem B8460409 : Blo 658307 8460409 := bstep (se 2 (by rfl) ⟨3172653, by rfl⟩ : syracuseStep 8460409 = 6345307) B6345307
theorem B2506409 : Blo 658307 2506409 := bstep (se 2 (by rfl) ⟨939903, by rfl⟩ : syracuseStep 2506409 = 1879807) B1879807
theorem B5652575 : Blo 658307 5652575 := bstep (se 1 (by rfl) ⟨4239431, by rfl⟩ : syracuseStep 5652575 = 8478863) B8478863
theorem B3768383 : Blo 658307 3768383 := bstep (se 1 (by rfl) ⟨2826287, by rfl⟩ : syracuseStep 3768383 = 5652575) B5652575
theorem B11280545 : Blo 658307 11280545 := bstep (se 2 (by rfl) ⟨4230204, by rfl⟩ : syracuseStep 11280545 = 8460409) B8460409
theorem B54113183 : Blo 658307 54113183 := bstep (se 1 (by rfl) ⟨40584887, by rfl⟩ : syracuseStep 54113183 = 81169775) B81169775
theorem B8486653 : Blo 658307 8486653 := bstep (se 3 (by rfl) ⟨1591247, by rfl⟩ : syracuseStep 8486653 = 3182495) B3182495
theorem B1670939 : Blo 658307 1670939 := bstep (se 1 (by rfl) ⟨1253204, by rfl⟩ : syracuseStep 1670939 = 2506409) B2506409
theorem B11315537 : Blo 658307 11315537 := bstep (se 2 (by rfl) ⟨4243326, by rfl⟩ : syracuseStep 11315537 = 8486653) B8486653
theorem B7520363 : Blo 658307 7520363 := bstep (se 1 (by rfl) ⟨5640272, by rfl⟩ : syracuseStep 7520363 = 11280545) B11280545
theorem B2512255 : Blo 658307 2512255 := bstep (se 1 (by rfl) ⟨1884191, by rfl⟩ : syracuseStep 2512255 = 3768383) B3768383
theorem B36075455 : Blo 658307 36075455 := bstep (se 1 (by rfl) ⟨27056591, by rfl⟩ : syracuseStep 36075455 = 54113183) B54113183
theorem B1113959 : Blo 658307 1113959 := bstep (se 1 (by rfl) ⟨835469, by rfl⟩ : syracuseStep 1113959 = 1670939) B1670939
theorem B5013575 : Blo 658307 5013575 := bstep (se 1 (by rfl) ⟨3760181, by rfl⟩ : syracuseStep 5013575 = 7520363) B7520363
theorem B7543691 : Blo 658307 7543691 := bstep (se 1 (by rfl) ⟨5657768, by rfl⟩ : syracuseStep 7543691 = 11315537) B11315537
theorem B3349673 : Blo 658307 3349673 := bstep (se 2 (by rfl) ⟨1256127, by rfl⟩ : syracuseStep 3349673 = 2512255) B2512255
theorem B742639 : Blo 658307 742639 := bstep (se 1 (by rfl) ⟨556979, by rfl⟩ : syracuseStep 742639 = 1113959) B1113959
theorem B24050303 : Blo 658307 24050303 := bstep (se 1 (by rfl) ⟨18037727, by rfl⟩ : syracuseStep 24050303 = 36075455) B36075455
theorem B3342383 : Blo 658307 3342383 := bstep (se 1 (by rfl) ⟨2506787, by rfl⟩ : syracuseStep 3342383 = 5013575) B5013575
theorem B2233115 : Blo 658307 2233115 := bstep (se 1 (by rfl) ⟨1674836, by rfl⟩ : syracuseStep 2233115 = 3349673) B3349673
theorem B990185 : Blo 658307 990185 := bstep (se 2 (by rfl) ⟨371319, by rfl⟩ : syracuseStep 990185 = 742639) B742639
theorem B16033535 : Blo 658307 16033535 := bstep (se 1 (by rfl) ⟨12025151, by rfl⟩ : syracuseStep 16033535 = 24050303) B24050303
theorem B5029127 : Blo 658307 5029127 := bstep (se 1 (by rfl) ⟨3771845, by rfl⟩ : syracuseStep 5029127 = 7543691) B7543691
theorem B2228255 : Blo 658307 2228255 := bstep (se 1 (by rfl) ⟨1671191, by rfl⟩ : syracuseStep 2228255 = 3342383) B3342383
theorem B660123 : Blo 658307 660123 := bstep (se 1 (by rfl) ⟨495092, by rfl⟩ : syracuseStep 660123 = 990185) B990185
theorem B10689023 : Blo 658307 10689023 := bstep (se 1 (by rfl) ⟨8016767, by rfl⟩ : syracuseStep 10689023 = 16033535) B16033535
theorem B3352751 : Blo 658307 3352751 := bstep (se 1 (by rfl) ⟨2514563, by rfl⟩ : syracuseStep 3352751 = 5029127) B5029127
theorem B1488743 : Blo 658307 1488743 := bstep (se 1 (by rfl) ⟨1116557, by rfl⟩ : syracuseStep 1488743 = 2233115) B2233115
theorem B2235167 : Blo 658307 2235167 := bstep (se 1 (by rfl) ⟨1676375, by rfl⟩ : syracuseStep 2235167 = 3352751) B3352751
theorem B992495 : Blo 658307 992495 := bstep (se 1 (by rfl) ⟨744371, by rfl⟩ : syracuseStep 992495 = 1488743) B1488743
theorem B1485503 : Blo 658307 1485503 := bstep (se 1 (by rfl) ⟨1114127, by rfl⟩ : syracuseStep 1485503 = 2228255) B2228255
theorem B28504061 : Blo 658307 28504061 := bstep (se 3 (by rfl) ⟨5344511, by rfl⟩ : syracuseStep 28504061 = 10689023) B10689023
theorem B661663 : Blo 658307 661663 := bstep (se 1 (by rfl) ⟨496247, by rfl⟩ : syracuseStep 661663 = 992495) B992495
theorem B990335 : Blo 658307 990335 := bstep (se 1 (by rfl) ⟨742751, by rfl⟩ : syracuseStep 990335 = 1485503) B1485503
theorem B1490111 : Blo 658307 1490111 := bstep (se 1 (by rfl) ⟨1117583, by rfl⟩ : syracuseStep 1490111 = 2235167) B2235167
theorem B19002707 : Blo 658307 19002707 := bstep (se 1 (by rfl) ⟨14252030, by rfl⟩ : syracuseStep 19002707 = 28504061) B28504061
theorem B660223 : Blo 658307 660223 := bstep (se 1 (by rfl) ⟨495167, by rfl⟩ : syracuseStep 660223 = 990335) B990335
theorem B993407 : Blo 658307 993407 := bstep (se 1 (by rfl) ⟨745055, by rfl⟩ : syracuseStep 993407 = 1490111) B1490111
theorem B12668471 : Blo 658307 12668471 := bstep (se 1 (by rfl) ⟨9501353, by rfl⟩ : syracuseStep 12668471 = 19002707) B19002707
theorem B662271 : Blo 658307 662271 := bstep (se 1 (by rfl) ⟨496703, by rfl⟩ : syracuseStep 662271 = 993407) B993407
theorem B8445647 : Blo 658307 8445647 := bstep (se 1 (by rfl) ⟨6334235, by rfl⟩ : syracuseStep 8445647 = 12668471) B12668471
theorem B5630431 : Blo 658307 5630431 := bstep (se 1 (by rfl) ⟨4222823, by rfl⟩ : syracuseStep 5630431 = 8445647) B8445647
theorem B7507241 : Blo 658307 7507241 := bstep (se 2 (by rfl) ⟨2815215, by rfl⟩ : syracuseStep 7507241 = 5630431) B5630431
theorem B5004827 : Blo 658307 5004827 := bstep (se 1 (by rfl) ⟨3753620, by rfl⟩ : syracuseStep 5004827 = 7507241) B7507241
theorem B3336551 : Blo 658307 3336551 := bstep (se 1 (by rfl) ⟨2502413, by rfl⟩ : syracuseStep 3336551 = 5004827) B5004827
theorem B2224367 : Blo 658307 2224367 := bstep (se 1 (by rfl) ⟨1668275, by rfl⟩ : syracuseStep 2224367 = 3336551) B3336551
theorem B1482911 : Blo 658307 1482911 := bstep (se 1 (by rfl) ⟨1112183, by rfl⟩ : syracuseStep 1482911 = 2224367) B2224367
theorem B988607 : Blo 658307 988607 := bstep (se 1 (by rfl) ⟨741455, by rfl⟩ : syracuseStep 988607 = 1482911) B1482911
theorem B659071 : Blo 658307 659071 := bstep (se 1 (by rfl) ⟨494303, by rfl⟩ : syracuseStep 659071 = 988607) B988607

theorem C0 (j : ℕ) (h1 : 164576 ≤ j) (h2 : j ≤ 165275) : Blo 658307 (4 * j + 3) := by
  interval_cases j
  · exact B658307
  · exact B658311
  · exact B658315
  · exact B658319
  · exact B658323
  · exact B658327
  · exact B658331
  · exact B658335
  · exact B658339
  · exact B658343
  · exact B658347
  · exact B658351
  · exact B658355
  · exact B658359
  · exact B658363
  · exact B658367
  · exact B658371
  · exact B658375
  · exact B658379
  · exact B658383
  · exact B658387
  · exact B658391
  · exact B658395
  · exact B658399
  · exact B658403
  · exact B658407
  · exact B658411
  · exact B658415
  · exact B658419
  · exact B658423
  · exact B658427
  · exact B658431
  · exact B658435
  · exact B658439
  · exact B658443
  · exact B658447
  · exact B658451
  · exact B658455
  · exact B658459
  · exact B658463
  · exact B658467
  · exact B658471
  · exact B658475
  · exact B658479
  · exact B658483
  · exact B658487
  · exact B658491
  · exact B658495
  · exact B658499
  · exact B658503
  · exact B658507
  · exact B658511
  · exact B658515
  · exact B658519
  · exact B658523
  · exact B658527
  · exact B658531
  · exact B658535
  · exact B658539
  · exact B658543
  · exact B658547
  · exact B658551
  · exact B658555
  · exact B658559
  · exact B658563
  · exact B658567
  · exact B658571
  · exact B658575
  · exact B658579
  · exact B658583
  · exact B658587
  · exact B658591
  · exact B658595
  · exact B658599
  · exact B658603
  · exact B658607
  · exact B658611
  · exact B658615
  · exact B658619
  · exact B658623
  · exact B658627
  · exact B658631
  · exact B658635
  · exact B658639
  · exact B658643
  · exact B658647
  · exact B658651
  · exact B658655
  · exact B658659
  · exact B658663
  · exact B658667
  · exact B658671
  · exact B658675
  · exact B658679
  · exact B658683
  · exact B658687
  · exact B658691
  · exact B658695
  · exact B658699
  · exact B658703
  · exact B658707
  · exact B658711
  · exact B658715
  · exact B658719
  · exact B658723
  · exact B658727
  · exact B658731
  · exact B658735
  · exact B658739
  · exact B658743
  · exact B658747
  · exact B658751
  · exact B658755
  · exact B658759
  · exact B658763
  · exact B658767
  · exact B658771
  · exact B658775
  · exact B658779
  · exact B658783
  · exact B658787
  · exact B658791
  · exact B658795
  · exact B658799
  · exact B658803
  · exact B658807
  · exact B658811
  · exact B658815
  · exact B658819
  · exact B658823
  · exact B658827
  · exact B658831
  · exact B658835
  · exact B658839
  · exact B658843
  · exact B658847
  · exact B658851
  · exact B658855
  · exact B658859
  · exact B658863
  · exact B658867
  · exact B658871
  · exact B658875
  · exact B658879
  · exact B658883
  · exact B658887
  · exact B658891
  · exact B658895
  · exact B658899
  · exact B658903
  · exact B658907
  · exact B658911
  · exact B658915
  · exact B658919
  · exact B658923
  · exact B658927
  · exact B658931
  · exact B658935
  · exact B658939
  · exact B658943
  · exact B658947
  · exact B658951
  · exact B658955
  · exact B658959
  · exact B658963
  · exact B658967
  · exact B658971
  · exact B658975
  · exact B658979
  · exact B658983
  · exact B658987
  · exact B658991
  · exact B658995
  · exact B658999
  · exact B659003
  · exact B659007
  · exact B659011
  · exact B659015
  · exact B659019
  · exact B659023
  · exact B659027
  · exact B659031
  · exact B659035
  · exact B659039
  · exact B659043
  · exact B659047
  · exact B659051
  · exact B659055
  · exact B659059
  · exact B659063
  · exact B659067
  · exact B659071
  · exact B659075
  · exact B659079
  · exact B659083
  · exact B659087
  · exact B659091
  · exact B659095
  · exact B659099
  · exact B659103
  · exact B659107
  · exact B659111
  · exact B659115
  · exact B659119
  · exact B659123
  · exact B659127
  · exact B659131
  · exact B659135
  · exact B659139
  · exact B659143
  · exact B659147
  · exact B659151
  · exact B659155
  · exact B659159
  · exact B659163
  · exact B659167
  · exact B659171
  · exact B659175
  · exact B659179
  · exact B659183
  · exact B659187
  · exact B659191
  · exact B659195
  · exact B659199
  · exact B659203
  · exact B659207
  · exact B659211
  · exact B659215
  · exact B659219
  · exact B659223
  · exact B659227
  · exact B659231
  · exact B659235
  · exact B659239
  · exact B659243
  · exact B659247
  · exact B659251
  · exact B659255
  · exact B659259
  · exact B659263
  · exact B659267
  · exact B659271
  · exact B659275
  · exact B659279
  · exact B659283
  · exact B659287
  · exact B659291
  · exact B659295
  · exact B659299
  · exact B659303
  · exact B659307
  · exact B659311
  · exact B659315
  · exact B659319
  · exact B659323
  · exact B659327
  · exact B659331
  · exact B659335
  · exact B659339
  · exact B659343
  · exact B659347
  · exact B659351
  · exact B659355
  · exact B659359
  · exact B659363
  · exact B659367
  · exact B659371
  · exact B659375
  · exact B659379
  · exact B659383
  · exact B659387
  · exact B659391
  · exact B659395
  · exact B659399
  · exact B659403
  · exact B659407
  · exact B659411
  · exact B659415
  · exact B659419
  · exact B659423
  · exact B659427
  · exact B659431
  · exact B659435
  · exact B659439
  · exact B659443
  · exact B659447
  · exact B659451
  · exact B659455
  · exact B659459
  · exact B659463
  · exact B659467
  · exact B659471
  · exact B659475
  · exact B659479
  · exact B659483
  · exact B659487
  · exact B659491
  · exact B659495
  · exact B659499
  · exact B659503
  · exact B659507
  · exact B659511
  · exact B659515
  · exact B659519
  · exact B659523
  · exact B659527
  · exact B659531
  · exact B659535
  · exact B659539
  · exact B659543
  · exact B659547
  · exact B659551
  · exact B659555
  · exact B659559
  · exact B659563
  · exact B659567
  · exact B659571
  · exact B659575
  · exact B659579
  · exact B659583
  · exact B659587
  · exact B659591
  · exact B659595
  · exact B659599
  · exact B659603
  · exact B659607
  · exact B659611
  · exact B659615
  · exact B659619
  · exact B659623
  · exact B659627
  · exact B659631
  · exact B659635
  · exact B659639
  · exact B659643
  · exact B659647
  · exact B659651
  · exact B659655
  · exact B659659
  · exact B659663
  · exact B659667
  · exact B659671
  · exact B659675
  · exact B659679
  · exact B659683
  · exact B659687
  · exact B659691
  · exact B659695
  · exact B659699
  · exact B659703
  · exact B659707
  · exact B659711
  · exact B659715
  · exact B659719
  · exact B659723
  · exact B659727
  · exact B659731
  · exact B659735
  · exact B659739
  · exact B659743
  · exact B659747
  · exact B659751
  · exact B659755
  · exact B659759
  · exact B659763
  · exact B659767
  · exact B659771
  · exact B659775
  · exact B659779
  · exact B659783
  · exact B659787
  · exact B659791
  · exact B659795
  · exact B659799
  · exact B659803
  · exact B659807
  · exact B659811
  · exact B659815
  · exact B659819
  · exact B659823
  · exact B659827
  · exact B659831
  · exact B659835
  · exact B659839
  · exact B659843
  · exact B659847
  · exact B659851
  · exact B659855
  · exact B659859
  · exact B659863
  · exact B659867
  · exact B659871
  · exact B659875
  · exact B659879
  · exact B659883
  · exact B659887
  · exact B659891
  · exact B659895
  · exact B659899
  · exact B659903
  · exact B659907
  · exact B659911
  · exact B659915
  · exact B659919
  · exact B659923
  · exact B659927
  · exact B659931
  · exact B659935
  · exact B659939
  · exact B659943
  · exact B659947
  · exact B659951
  · exact B659955
  · exact B659959
  · exact B659963
  · exact B659967
  · exact B659971
  · exact B659975
  · exact B659979
  · exact B659983
  · exact B659987
  · exact B659991
  · exact B659995
  · exact B659999
  · exact B660003
  · exact B660007
  · exact B660011
  · exact B660015
  · exact B660019
  · exact B660023
  · exact B660027
  · exact B660031
  · exact B660035
  · exact B660039
  · exact B660043
  · exact B660047
  · exact B660051
  · exact B660055
  · exact B660059
  · exact B660063
  · exact B660067
  · exact B660071
  · exact B660075
  · exact B660079
  · exact B660083
  · exact B660087
  · exact B660091
  · exact B660095
  · exact B660099
  · exact B660103
  · exact B660107
  · exact B660111
  · exact B660115
  · exact B660119
  · exact B660123
  · exact B660127
  · exact B660131
  · exact B660135
  · exact B660139
  · exact B660143
  · exact B660147
  · exact B660151
  · exact B660155
  · exact B660159
  · exact B660163
  · exact B660167
  · exact B660171
  · exact B660175
  · exact B660179
  · exact B660183
  · exact B660187
  · exact B660191
  · exact B660195
  · exact B660199
  · exact B660203
  · exact B660207
  · exact B660211
  · exact B660215
  · exact B660219
  · exact B660223
  · exact B660227
  · exact B660231
  · exact B660235
  · exact B660239
  · exact B660243
  · exact B660247
  · exact B660251
  · exact B660255
  · exact B660259
  · exact B660263
  · exact B660267
  · exact B660271
  · exact B660275
  · exact B660279
  · exact B660283
  · exact B660287
  · exact B660291
  · exact B660295
  · exact B660299
  · exact B660303
  · exact B660307
  · exact B660311
  · exact B660315
  · exact B660319
  · exact B660323
  · exact B660327
  · exact B660331
  · exact B660335
  · exact B660339
  · exact B660343
  · exact B660347
  · exact B660351
  · exact B660355
  · exact B660359
  · exact B660363
  · exact B660367
  · exact B660371
  · exact B660375
  · exact B660379
  · exact B660383
  · exact B660387
  · exact B660391
  · exact B660395
  · exact B660399
  · exact B660403
  · exact B660407
  · exact B660411
  · exact B660415
  · exact B660419
  · exact B660423
  · exact B660427
  · exact B660431
  · exact B660435
  · exact B660439
  · exact B660443
  · exact B660447
  · exact B660451
  · exact B660455
  · exact B660459
  · exact B660463
  · exact B660467
  · exact B660471
  · exact B660475
  · exact B660479
  · exact B660483
  · exact B660487
  · exact B660491
  · exact B660495
  · exact B660499
  · exact B660503
  · exact B660507
  · exact B660511
  · exact B660515
  · exact B660519
  · exact B660523
  · exact B660527
  · exact B660531
  · exact B660535
  · exact B660539
  · exact B660543
  · exact B660547
  · exact B660551
  · exact B660555
  · exact B660559
  · exact B660563
  · exact B660567
  · exact B660571
  · exact B660575
  · exact B660579
  · exact B660583
  · exact B660587
  · exact B660591
  · exact B660595
  · exact B660599
  · exact B660603
  · exact B660607
  · exact B660611
  · exact B660615
  · exact B660619
  · exact B660623
  · exact B660627
  · exact B660631
  · exact B660635
  · exact B660639
  · exact B660643
  · exact B660647
  · exact B660651
  · exact B660655
  · exact B660659
  · exact B660663
  · exact B660667
  · exact B660671
  · exact B660675
  · exact B660679
  · exact B660683
  · exact B660687
  · exact B660691
  · exact B660695
  · exact B660699
  · exact B660703
  · exact B660707
  · exact B660711
  · exact B660715
  · exact B660719
  · exact B660723
  · exact B660727
  · exact B660731
  · exact B660735
  · exact B660739
  · exact B660743
  · exact B660747
  · exact B660751
  · exact B660755
  · exact B660759
  · exact B660763
  · exact B660767
  · exact B660771
  · exact B660775
  · exact B660779
  · exact B660783
  · exact B660787
  · exact B660791
  · exact B660795
  · exact B660799
  · exact B660803
  · exact B660807
  · exact B660811
  · exact B660815
  · exact B660819
  · exact B660823
  · exact B660827
  · exact B660831
  · exact B660835
  · exact B660839
  · exact B660843
  · exact B660847
  · exact B660851
  · exact B660855
  · exact B660859
  · exact B660863
  · exact B660867
  · exact B660871
  · exact B660875
  · exact B660879
  · exact B660883
  · exact B660887
  · exact B660891
  · exact B660895
  · exact B660899
  · exact B660903
  · exact B660907
  · exact B660911
  · exact B660915
  · exact B660919
  · exact B660923
  · exact B660927
  · exact B660931
  · exact B660935
  · exact B660939
  · exact B660943
  · exact B660947
  · exact B660951
  · exact B660955
  · exact B660959
  · exact B660963
  · exact B660967
  · exact B660971
  · exact B660975
  · exact B660979
  · exact B660983
  · exact B660987
  · exact B660991
  · exact B660995
  · exact B660999
  · exact B661003
  · exact B661007
  · exact B661011
  · exact B661015
  · exact B661019
  · exact B661023
  · exact B661027
  · exact B661031
  · exact B661035
  · exact B661039
  · exact B661043
  · exact B661047
  · exact B661051
  · exact B661055
  · exact B661059
  · exact B661063
  · exact B661067
  · exact B661071
  · exact B661075
  · exact B661079
  · exact B661083
  · exact B661087
  · exact B661091
  · exact B661095
  · exact B661099
  · exact B661103

theorem C1 (j : ℕ) (h1 : 165276 ≤ j) (h2 : j ≤ 165576) : Blo 658307 (4 * j + 3) := by
  interval_cases j
  · exact B661107
  · exact B661111
  · exact B661115
  · exact B661119
  · exact B661123
  · exact B661127
  · exact B661131
  · exact B661135
  · exact B661139
  · exact B661143
  · exact B661147
  · exact B661151
  · exact B661155
  · exact B661159
  · exact B661163
  · exact B661167
  · exact B661171
  · exact B661175
  · exact B661179
  · exact B661183
  · exact B661187
  · exact B661191
  · exact B661195
  · exact B661199
  · exact B661203
  · exact B661207
  · exact B661211
  · exact B661215
  · exact B661219
  · exact B661223
  · exact B661227
  · exact B661231
  · exact B661235
  · exact B661239
  · exact B661243
  · exact B661247
  · exact B661251
  · exact B661255
  · exact B661259
  · exact B661263
  · exact B661267
  · exact B661271
  · exact B661275
  · exact B661279
  · exact B661283
  · exact B661287
  · exact B661291
  · exact B661295
  · exact B661299
  · exact B661303
  · exact B661307
  · exact B661311
  · exact B661315
  · exact B661319
  · exact B661323
  · exact B661327
  · exact B661331
  · exact B661335
  · exact B661339
  · exact B661343
  · exact B661347
  · exact B661351
  · exact B661355
  · exact B661359
  · exact B661363
  · exact B661367
  · exact B661371
  · exact B661375
  · exact B661379
  · exact B661383
  · exact B661387
  · exact B661391
  · exact B661395
  · exact B661399
  · exact B661403
  · exact B661407
  · exact B661411
  · exact B661415
  · exact B661419
  · exact B661423
  · exact B661427
  · exact B661431
  · exact B661435
  · exact B661439
  · exact B661443
  · exact B661447
  · exact B661451
  · exact B661455
  · exact B661459
  · exact B661463
  · exact B661467
  · exact B661471
  · exact B661475
  · exact B661479
  · exact B661483
  · exact B661487
  · exact B661491
  · exact B661495
  · exact B661499
  · exact B661503
  · exact B661507
  · exact B661511
  · exact B661515
  · exact B661519
  · exact B661523
  · exact B661527
  · exact B661531
  · exact B661535
  · exact B661539
  · exact B661543
  · exact B661547
  · exact B661551
  · exact B661555
  · exact B661559
  · exact B661563
  · exact B661567
  · exact B661571
  · exact B661575
  · exact B661579
  · exact B661583
  · exact B661587
  · exact B661591
  · exact B661595
  · exact B661599
  · exact B661603
  · exact B661607
  · exact B661611
  · exact B661615
  · exact B661619
  · exact B661623
  · exact B661627
  · exact B661631
  · exact B661635
  · exact B661639
  · exact B661643
  · exact B661647
  · exact B661651
  · exact B661655
  · exact B661659
  · exact B661663
  · exact B661667
  · exact B661671
  · exact B661675
  · exact B661679
  · exact B661683
  · exact B661687
  · exact B661691
  · exact B661695
  · exact B661699
  · exact B661703
  · exact B661707
  · exact B661711
  · exact B661715
  · exact B661719
  · exact B661723
  · exact B661727
  · exact B661731
  · exact B661735
  · exact B661739
  · exact B661743
  · exact B661747
  · exact B661751
  · exact B661755
  · exact B661759
  · exact B661763
  · exact B661767
  · exact B661771
  · exact B661775
  · exact B661779
  · exact B661783
  · exact B661787
  · exact B661791
  · exact B661795
  · exact B661799
  · exact B661803
  · exact B661807
  · exact B661811
  · exact B661815
  · exact B661819
  · exact B661823
  · exact B661827
  · exact B661831
  · exact B661835
  · exact B661839
  · exact B661843
  · exact B661847
  · exact B661851
  · exact B661855
  · exact B661859
  · exact B661863
  · exact B661867
  · exact B661871
  · exact B661875
  · exact B661879
  · exact B661883
  · exact B661887
  · exact B661891
  · exact B661895
  · exact B661899
  · exact B661903
  · exact B661907
  · exact B661911
  · exact B661915
  · exact B661919
  · exact B661923
  · exact B661927
  · exact B661931
  · exact B661935
  · exact B661939
  · exact B661943
  · exact B661947
  · exact B661951
  · exact B661955
  · exact B661959
  · exact B661963
  · exact B661967
  · exact B661971
  · exact B661975
  · exact B661979
  · exact B661983
  · exact B661987
  · exact B661991
  · exact B661995
  · exact B661999
  · exact B662003
  · exact B662007
  · exact B662011
  · exact B662015
  · exact B662019
  · exact B662023
  · exact B662027
  · exact B662031
  · exact B662035
  · exact B662039
  · exact B662043
  · exact B662047
  · exact B662051
  · exact B662055
  · exact B662059
  · exact B662063
  · exact B662067
  · exact B662071
  · exact B662075
  · exact B662079
  · exact B662083
  · exact B662087
  · exact B662091
  · exact B662095
  · exact B662099
  · exact B662103
  · exact B662107
  · exact B662111
  · exact B662115
  · exact B662119
  · exact B662123
  · exact B662127
  · exact B662131
  · exact B662135
  · exact B662139
  · exact B662143
  · exact B662147
  · exact B662151
  · exact B662155
  · exact B662159
  · exact B662163
  · exact B662167
  · exact B662171
  · exact B662175
  · exact B662179
  · exact B662183
  · exact B662187
  · exact B662191
  · exact B662195
  · exact B662199
  · exact B662203
  · exact B662207
  · exact B662211
  · exact B662215
  · exact B662219
  · exact B662223
  · exact B662227
  · exact B662231
  · exact B662235
  · exact B662239
  · exact B662243
  · exact B662247
  · exact B662251
  · exact B662255
  · exact B662259
  · exact B662263
  · exact B662267
  · exact B662271
  · exact B662275
  · exact B662279
  · exact B662283
  · exact B662287
  · exact B662291
  · exact B662295
  · exact B662299
  · exact B662303
  · exact B662307

theorem solution (m : ℕ) (hlo : 658307 ≤ m) (hhi : m ≤ 662307) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 164576 ≤ j := by omega
    have hj2 : j ≤ 165576 := by omega
    have hb : Blo 658307 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 165276 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
