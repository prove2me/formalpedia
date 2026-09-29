-- Prove2me | solution 1 for syracuse_descends_range_1319478_1321478
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:34.569912+00:00
-- url     : https://prove2.me/submissions/2aee48ff-1137-43c3-9e34-c750cf9874db

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


theorem B2506781 : Blo 1319478 2506781 := bbase (se 3 (by rfl) ⟨470021, by rfl⟩ : syracuseStep 2506781 = 940043) (by norm_num)
theorem B2228269 : Blo 1319478 2228269 := bbase (se 3 (by rfl) ⟨417800, by rfl⟩ : syracuseStep 2228269 = 835601) (by norm_num)
theorem B8036405 : Blo 1319478 8036405 := bbase (se 5 (by rfl) ⟨376706, by rfl⟩ : syracuseStep 8036405 = 753413) (by norm_num)
theorem B4456565 : Blo 1319478 4456565 := bbase (se 5 (by rfl) ⟨208901, by rfl⟩ : syracuseStep 4456565 = 417803) (by norm_num)
theorem B1671293 : Blo 1319478 1671293 := bbase (se 3 (by rfl) ⟨313367, by rfl⟩ : syracuseStep 1671293 = 626735) (by norm_num)
theorem B2228357 : Blo 1319478 2228357 := bbase (se 4 (by rfl) ⟨208908, by rfl⟩ : syracuseStep 2228357 = 417817) (by norm_num)
theorem B2818189 : Blo 1319478 2818189 := bbase (se 3 (by rfl) ⟨528410, by rfl⟩ : syracuseStep 2818189 = 1056821) (by norm_num)
theorem B4227221 : Blo 1319478 4227221 := bbase (se 6 (by rfl) ⟨99075, by rfl⟩ : syracuseStep 4227221 = 198151) (by norm_num)
theorem B3342485 : Blo 1319478 3342485 := bbase (se 6 (by rfl) ⟨78339, by rfl⟩ : syracuseStep 3342485 = 156679) (by norm_num)
theorem B3571877 : Blo 1319478 3571877 := bbase (se 4 (by rfl) ⟨334863, by rfl⟩ : syracuseStep 3571877 = 669727) (by norm_num)
theorem B2506925 : Blo 1319478 2506925 := bbase (se 3 (by rfl) ⟨470048, by rfl⟩ : syracuseStep 2506925 = 940097) (by norm_num)
theorem B1671349 : Blo 1319478 1671349 := bbase (se 5 (by rfl) ⟨78344, by rfl⟩ : syracuseStep 1671349 = 156689) (by norm_num)
theorem B2859229 : Blo 1319478 2859229 := bbase (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) (by norm_num)
theorem B2818309 : Blo 1319478 2818309 := bbase (se 4 (by rfl) ⟨264216, by rfl⟩ : syracuseStep 2818309 = 528433) (by norm_num)
theorem B2228485 : Blo 1319478 2228485 := bbase (se 4 (by rfl) ⟨208920, by rfl⟩ : syracuseStep 2228485 = 417841) (by norm_num)
theorem B1671445 : Blo 1319478 1671445 := bbase (se 6 (by rfl) ⟨39174, by rfl⟩ : syracuseStep 1671445 = 78349) (by norm_num)
theorem B2007349 : Blo 1319478 2007349 := bbase (se 5 (by rfl) ⟨94094, by rfl⟩ : syracuseStep 2007349 = 188189) (by norm_num)
theorem B2228573 : Blo 1319478 2228573 := bbase (se 3 (by rfl) ⟨417857, by rfl⟩ : syracuseStep 2228573 = 835715) (by norm_num)
theorem B3760501 : Blo 1319478 3760501 := bbase (se 5 (by rfl) ⟨176273, by rfl⟩ : syracuseStep 3760501 = 352547) (by norm_num)
theorem B1671617 : Blo 1319478 1671617 := bbase (se 2 (by rfl) ⟨626856, by rfl⟩ : syracuseStep 1671617 = 1253713) (by norm_num)
theorem B2507213 : Blo 1319478 2507213 := bbase (se 3 (by rfl) ⟨470102, by rfl⟩ : syracuseStep 2507213 = 940205) (by norm_num)
theorem B2228701 : Blo 1319478 2228701 := bbase (se 3 (by rfl) ⟨417881, by rfl⟩ : syracuseStep 2228701 = 835763) (by norm_num)
theorem B2114021 : Blo 1319478 2114021 := bbase (se 4 (by rfl) ⟨198189, by rfl⟩ : syracuseStep 2114021 = 396379) (by norm_num)
theorem B3342829 : Blo 1319478 3342829 := bbase (se 3 (by rfl) ⟨626780, by rfl⟩ : syracuseStep 3342829 = 1253561) (by norm_num)
theorem B1671673 : Blo 1319478 1671673 := bbase (se 2 (by rfl) ⟨626877, by rfl⟩ : syracuseStep 1671673 = 1253755) (by norm_num)
theorem B2818565 : Blo 1319478 2818565 := bbase (se 4 (by rfl) ⟨264240, by rfl⟩ : syracuseStep 2818565 = 528481) (by norm_num)
theorem B3760661 : Blo 1319478 3760661 := bbase (se 6 (by rfl) ⟨88140, by rfl⟩ : syracuseStep 3760661 = 176281) (by norm_num)
theorem B1409573 : Blo 1319478 1409573 := bbase (se 4 (by rfl) ⟨132147, by rfl⟩ : syracuseStep 1409573 = 264295) (by norm_num)
theorem B4456997 : Blo 1319478 4456997 := bbase (se 4 (by rfl) ⟨417843, by rfl⟩ : syracuseStep 4456997 = 835687) (by norm_num)
theorem B2228789 : Blo 1319478 2228789 := bbase (se 5 (by rfl) ⟨104474, by rfl⟩ : syracuseStep 2228789 = 208949) (by norm_num)
theorem B6685253 : Blo 1319478 6685253 := bbase (se 4 (by rfl) ⟨626742, by rfl⟩ : syracuseStep 6685253 = 1253485) (by norm_num)
theorem B1884749 : Blo 1319478 1884749 := bbase (se 3 (by rfl) ⟨353390, by rfl⟩ : syracuseStep 1884749 = 706781) (by norm_num)
theorem B1671769 : Blo 1319478 1671769 := bbase (se 2 (by rfl) ⟨626913, by rfl⟩ : syracuseStep 1671769 = 1253827) (by norm_num)
theorem B3342941 : Blo 1319478 3342941 := bbase (se 3 (by rfl) ⟨626801, by rfl⟩ : syracuseStep 3342941 = 1253603) (by norm_num)
theorem B2507365 : Blo 1319478 2507365 := bbase (se 4 (by rfl) ⟨235065, by rfl⟩ : syracuseStep 2507365 = 470131) (by norm_num)
theorem B2007661 : Blo 1319478 2007661 := bbase (se 3 (by rfl) ⟨376436, by rfl⟩ : syracuseStep 2007661 = 752873) (by norm_num)
theorem B10027637 : Blo 1319478 10027637 := bbase (se 5 (by rfl) ⟨470045, by rfl⟩ : syracuseStep 10027637 = 940091) (by norm_num)
theorem B5636789 : Blo 1319478 5636789 := bbase (se 5 (by rfl) ⟨264224, by rfl⟩ : syracuseStep 5636789 = 528449) (by norm_num)
theorem B2228917 : Blo 1319478 2228917 := bbase (se 5 (by rfl) ⟨104480, by rfl⟩ : syracuseStep 2228917 = 208961) (by norm_num)
theorem B1409761 : Blo 1319478 1409761 := bbase (se 2 (by rfl) ⟨528660, by rfl⟩ : syracuseStep 1409761 = 1057321) (by norm_num)
theorem B4760309 : Blo 1319478 4760309 := bbase (se 5 (by rfl) ⟨223139, by rfl⟩ : syracuseStep 4760309 = 446279) (by norm_num)
theorem B3760901 : Blo 1319478 3760901 := bbase (se 4 (by rfl) ⟨352584, by rfl⟩ : syracuseStep 3760901 = 705169) (by norm_num)
theorem B1671941 : Blo 1319478 1671941 := bbase (se 4 (by rfl) ⟨156744, by rfl⟩ : syracuseStep 1671941 = 313489) (by norm_num)
theorem B2229005 : Blo 1319478 2229005 := bbase (se 3 (by rfl) ⟨417938, by rfl⟩ : syracuseStep 2229005 = 835877) (by norm_num)
theorem B3343133 : Blo 1319478 3343133 := bbase (se 3 (by rfl) ⟨626837, by rfl⟩ : syracuseStep 3343133 = 1253675) (by norm_num)
theorem B1671997 : Blo 1319478 1671997 := bbase (se 3 (by rfl) ⟨313499, by rfl⟩ : syracuseStep 1671997 = 626999) (by norm_num)
theorem B2229133 : Blo 1319478 2229133 := bbase (se 3 (by rfl) ⟨417962, by rfl⟩ : syracuseStep 2229133 = 835925) (by norm_num)
theorem B2507669 : Blo 1319478 2507669 := bbase (se 6 (by rfl) ⟨58773, by rfl⟩ : syracuseStep 2507669 = 117547) (by norm_num)
theorem B1672093 : Blo 1319478 1672093 := bbase (se 3 (by rfl) ⟨313517, by rfl⟩ : syracuseStep 1672093 = 627035) (by norm_num)
theorem B3761093 : Blo 1319478 3761093 := bbase (se 4 (by rfl) ⟨352602, by rfl⟩ : syracuseStep 3761093 = 705205) (by norm_num)
theorem B4457429 : Blo 1319478 4457429 := bbase (se 7 (by rfl) ⟨52235, by rfl⟩ : syracuseStep 4457429 = 104471) (by norm_num)
theorem B2114533 : Blo 1319478 2114533 := bbase (se 4 (by rfl) ⟨198237, by rfl⟩ : syracuseStep 2114533 = 396475) (by norm_num)
theorem B2229221 : Blo 1319478 2229221 := bbase (se 4 (by rfl) ⟨208989, by rfl⟩ : syracuseStep 2229221 = 417979) (by norm_num)
theorem B10019861 : Blo 1319478 10019861 := bbase (se 6 (by rfl) ⟨234840, by rfl⟩ : syracuseStep 10019861 = 469681) (by norm_num)
theorem B10298389 : Blo 1319478 10298389 := bbase (se 6 (by rfl) ⟨241368, by rfl⟩ : syracuseStep 10298389 = 482737) (by norm_num)
theorem B1672265 : Blo 1319478 1672265 := bbase (se 2 (by rfl) ⟨627099, by rfl⟩ : syracuseStep 1672265 = 1254199) (by norm_num)
theorem B2229349 : Blo 1319478 2229349 := bbase (se 4 (by rfl) ⟨209001, by rfl⟩ : syracuseStep 2229349 = 418003) (by norm_num)
theorem B3343477 : Blo 1319478 3343477 := bbase (se 5 (by rfl) ⟨156725, by rfl⟩ : syracuseStep 3343477 = 313451) (by norm_num)
theorem B1672321 : Blo 1319478 1672321 := bbase (se 2 (by rfl) ⟨627120, by rfl⟩ : syracuseStep 1672321 = 1254241) (by norm_num)
theorem B2229437 : Blo 1319478 2229437 := bbase (se 3 (by rfl) ⟨418019, by rfl⟩ : syracuseStep 2229437 = 836039) (by norm_num)
theorem B1672417 : Blo 1319478 1672417 := bbase (se 2 (by rfl) ⟨627156, by rfl⟩ : syracuseStep 1672417 = 1254313) (by norm_num)
theorem B3343589 : Blo 1319478 3343589 := bbase (se 4 (by rfl) ⟨313461, by rfl⟩ : syracuseStep 3343589 = 626923) (by norm_num)
theorem B2229565 : Blo 1319478 2229565 := bbase (se 3 (by rfl) ⟨418043, by rfl⟩ : syracuseStep 2229565 = 836087) (by norm_num)
theorem B2819453 : Blo 1319478 2819453 := bbase (se 3 (by rfl) ⟨528647, by rfl⟩ : syracuseStep 2819453 = 1057295) (by norm_num)
theorem B4457861 : Blo 1319478 4457861 := bbase (se 4 (by rfl) ⟨417924, by rfl⟩ : syracuseStep 4457861 = 835849) (by norm_num)
theorem B2229653 : Blo 1319478 2229653 := bbase (se 6 (by rfl) ⟨52257, by rfl⟩ : syracuseStep 2229653 = 104515) (by norm_num)
theorem B3343781 : Blo 1319478 3343781 := bbase (se 4 (by rfl) ⟨313479, by rfl⟩ : syracuseStep 3343781 = 626959) (by norm_num)
theorem B2115077 : Blo 1319478 2115077 := bbase (se 4 (by rfl) ⟨198288, by rfl⟩ : syracuseStep 2115077 = 396577) (by norm_num)
theorem B1410581 : Blo 1319478 1410581 := bbase (se 6 (by rfl) ⟨33060, by rfl⟩ : syracuseStep 1410581 = 66121) (by norm_num)
theorem B2229781 : Blo 1319478 2229781 := bbase (se 6 (by rfl) ⟨52260, by rfl⟩ : syracuseStep 2229781 = 104521) (by norm_num)
theorem B5015141 : Blo 1319478 5015141 := bbase (se 4 (by rfl) ⟨470169, by rfl⟩ : syracuseStep 5015141 = 940339) (by norm_num)
theorem B2819693 : Blo 1319478 2819693 := bbase (se 3 (by rfl) ⟨528692, by rfl⟩ : syracuseStep 2819693 = 1057385) (by norm_num)
theorem B2229869 : Blo 1319478 2229869 := bbase (se 3 (by rfl) ⟨418100, by rfl⟩ : syracuseStep 2229869 = 836201) (by norm_num)
theorem B2508421 : Blo 1319478 2508421 := bbase (se 4 (by rfl) ⟨235164, by rfl⟩ : syracuseStep 2508421 = 470329) (by norm_num)
theorem B1484437 : Blo 1319478 1484437 := bbase (se 6 (by rfl) ⟨34791, by rfl⟩ : syracuseStep 1484437 = 69583) (by norm_num)
theorem B1484473 : Blo 1319478 1484473 := bbase (se 2 (by rfl) ⟨556677, by rfl⟩ : syracuseStep 1484473 = 1113355) (by norm_num)
theorem B1484509 : Blo 1319478 1484509 := bbase (se 3 (by rfl) ⟨278345, by rfl⟩ : syracuseStep 1484509 = 556691) (by norm_num)
theorem B3344125 : Blo 1319478 3344125 := bbase (se 3 (by rfl) ⟨627023, by rfl⟩ : syracuseStep 3344125 = 1254047) (by norm_num)
theorem B1484545 : Blo 1319478 1484545 := bbase (se 2 (by rfl) ⟨556704, by rfl⟩ : syracuseStep 1484545 = 1113409) (by norm_num)
theorem B4015877 : Blo 1319478 4015877 := bbase (se 4 (by rfl) ⟨376488, by rfl⟩ : syracuseStep 4015877 = 752977) (by norm_num)
theorem B2508565 : Blo 1319478 2508565 := bbase (se 6 (by rfl) ⟨58794, by rfl⟩ : syracuseStep 2508565 = 117589) (by norm_num)
theorem B1484581 : Blo 1319478 1484581 := bbase (se 4 (by rfl) ⟨139179, by rfl⟩ : syracuseStep 1484581 = 278359) (by norm_num)
theorem B4458293 : Blo 1319478 4458293 := bbase (se 5 (by rfl) ⟨208982, by rfl⟩ : syracuseStep 4458293 = 417965) (by norm_num)
theorem B1484617 : Blo 1319478 1484617 := bbase (se 2 (by rfl) ⟨556731, by rfl⟩ : syracuseStep 1484617 = 1113463) (by norm_num)
theorem B6686549 : Blo 1319478 6686549 := bbase (se 9 (by rfl) ⟨19589, by rfl⟩ : syracuseStep 6686549 = 39179) (by norm_num)
theorem B1484653 : Blo 1319478 1484653 := bbase (se 3 (by rfl) ⟨278372, by rfl⟩ : syracuseStep 1484653 = 556745) (by norm_num)
theorem B3344237 : Blo 1319478 3344237 := bbase (se 3 (by rfl) ⟨627044, by rfl⟩ : syracuseStep 3344237 = 1254089) (by norm_num)
theorem B3172213 : Blo 1319478 3172213 := bbase (se 5 (by rfl) ⟨148697, by rfl⟩ : syracuseStep 3172213 = 297395) (by norm_num)
theorem B6104965 : Blo 1319478 6104965 := bbase (se 4 (by rfl) ⟨572340, by rfl⟩ : syracuseStep 6104965 = 1144681) (by norm_num)
theorem B5015429 : Blo 1319478 5015429 := bbase (se 4 (by rfl) ⟨470196, by rfl⟩ : syracuseStep 5015429 = 940393) (by norm_num)
theorem B1484689 : Blo 1319478 1484689 := bbase (se 2 (by rfl) ⟨556758, by rfl⟩ : syracuseStep 1484689 = 1113517) (by norm_num)
theorem B3762085 : Blo 1319478 3762085 := bbase (se 4 (by rfl) ⟨352695, by rfl⟩ : syracuseStep 3762085 = 705391) (by norm_num)
theorem B1484725 : Blo 1319478 1484725 := bbase (se 5 (by rfl) ⟨69596, by rfl⟩ : syracuseStep 1484725 = 139193) (by norm_num)
theorem B2508725 : Blo 1319478 2508725 := bbase (se 5 (by rfl) ⟨117596, by rfl⟩ : syracuseStep 2508725 = 235193) (by norm_num)
theorem B1411025 : Blo 1319478 1411025 := bbase (se 2 (by rfl) ⟨529134, by rfl⟩ : syracuseStep 1411025 = 1058269) (by norm_num)
theorem B1484761 : Blo 1319478 1484761 := bbase (se 2 (by rfl) ⟨556785, by rfl⟩ : syracuseStep 1484761 = 1113571) (by norm_num)
theorem B1484797 : Blo 1319478 1484797 := bbase (se 3 (by rfl) ⟨278399, by rfl⟩ : syracuseStep 1484797 = 556799) (by norm_num)
theorem B1484833 : Blo 1319478 1484833 := bbase (se 2 (by rfl) ⟨556812, by rfl⟩ : syracuseStep 1484833 = 1113625) (by norm_num)
theorem B2115629 : Blo 1319478 2115629 := bbase (se 3 (by rfl) ⟨396680, by rfl⟩ : syracuseStep 2115629 = 793361) (by norm_num)
theorem B3344429 : Blo 1319478 3344429 := bbase (se 3 (by rfl) ⟨627080, by rfl⟩ : syracuseStep 3344429 = 1254161) (by norm_num)
theorem B1484869 : Blo 1319478 1484869 := bbase (se 4 (by rfl) ⟨139206, by rfl⟩ : syracuseStep 1484869 = 278413) (by norm_num)
theorem B2115661 : Blo 1319478 2115661 := bbase (se 3 (by rfl) ⟨396686, by rfl⟩ : syracuseStep 2115661 = 793373) (by norm_num)
theorem B2820197 : Blo 1319478 2820197 := bbase (se 4 (by rfl) ⟨264393, by rfl⟩ : syracuseStep 2820197 = 528787) (by norm_num)
theorem B1484905 : Blo 1319478 1484905 := bbase (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) (by norm_num)
theorem B2820205 : Blo 1319478 2820205 := bbase (se 3 (by rfl) ⟨528788, by rfl⟩ : syracuseStep 2820205 = 1057577) (by norm_num)
theorem B8456309 : Blo 1319478 8456309 := bbase (se 5 (by rfl) ⟨396389, by rfl⟩ : syracuseStep 8456309 = 792779) (by norm_num)
theorem B1484941 : Blo 1319478 1484941 := bbase (se 3 (by rfl) ⟨278426, by rfl⟩ : syracuseStep 1484941 = 556853) (by norm_num)
theorem B4761749 : Blo 1319478 4761749 := bbase (se 6 (by rfl) ⟨111603, by rfl⟩ : syracuseStep 4761749 = 223207) (by norm_num)
theorem B1484977 : Blo 1319478 1484977 := bbase (se 2 (by rfl) ⟨556866, by rfl⟩ : syracuseStep 1484977 = 1113733) (by norm_num)
theorem B1485013 : Blo 1319478 1485013 := bbase (se 7 (by rfl) ⟨17402, by rfl⟩ : syracuseStep 1485013 = 34805) (by norm_num)
theorem B4458725 : Blo 1319478 4458725 := bbase (se 4 (by rfl) ⟨418005, by rfl⟩ : syracuseStep 4458725 = 836011) (by norm_num)
theorem B1485049 : Blo 1319478 1485049 := bbase (se 2 (by rfl) ⟨556893, by rfl⟩ : syracuseStep 1485049 = 1113787) (by norm_num)
theorem B1485085 : Blo 1319478 1485085 := bbase (se 3 (by rfl) ⟨278453, by rfl⟩ : syracuseStep 1485085 = 556907) (by norm_num)
theorem B1485121 : Blo 1319478 1485121 := bbase (se 2 (by rfl) ⟨556920, by rfl⟩ : syracuseStep 1485121 = 1113841) (by norm_num)
theorem B1485157 : Blo 1319478 1485157 := bbase (se 4 (by rfl) ⟨139233, by rfl⟩ : syracuseStep 1485157 = 278467) (by norm_num)
theorem B2378101 : Blo 1319478 2378101 := bbase (se 5 (by rfl) ⟨111473, by rfl⟩ : syracuseStep 2378101 = 222947) (by norm_num)
theorem B3344773 : Blo 1319478 3344773 := bbase (se 4 (by rfl) ⟨313572, by rfl⟩ : syracuseStep 3344773 = 627145) (by norm_num)
theorem B1485193 : Blo 1319478 1485193 := bbase (se 2 (by rfl) ⟨556947, by rfl⟩ : syracuseStep 1485193 = 1113895) (by norm_num)
theorem B5638565 : Blo 1319478 5638565 := bbase (se 4 (by rfl) ⟨528615, by rfl⟩ : syracuseStep 5638565 = 1057231) (by norm_num)
theorem B1485229 : Blo 1319478 1485229 := bbase (se 3 (by rfl) ⟨278480, by rfl⟩ : syracuseStep 1485229 = 556961) (by norm_num)
theorem B1485265 : Blo 1319478 1485265 := bbase (se 2 (by rfl) ⟨556974, by rfl⟩ : syracuseStep 1485265 = 1113949) (by norm_num)
theorem B2288101 : Blo 1319478 2288101 := bbase (se 4 (by rfl) ⟨214509, by rfl⟩ : syracuseStep 2288101 = 429019) (by norm_num)
theorem B1485301 : Blo 1319478 1485301 := bbase (se 5 (by rfl) ⟨69623, by rfl⟩ : syracuseStep 1485301 = 139247) (by norm_num)
theorem B3344885 : Blo 1319478 3344885 := bbase (se 5 (by rfl) ⟨156791, by rfl⟩ : syracuseStep 3344885 = 313583) (by norm_num)
theorem B2411021 : Blo 1319478 2411021 := bbase (se 3 (by rfl) ⟨452066, by rfl⟩ : syracuseStep 2411021 = 904133) (by norm_num)
theorem B3172877 : Blo 1319478 3172877 := bbase (se 3 (by rfl) ⟨594914, by rfl⟩ : syracuseStep 3172877 = 1189829) (by norm_num)
theorem B1485337 : Blo 1319478 1485337 := bbase (se 2 (by rfl) ⟨557001, by rfl⟩ : syracuseStep 1485337 = 1114003) (by norm_num)
theorem B2542117 : Blo 1319478 2542117 := bbase (se 4 (by rfl) ⟨238323, by rfl⟩ : syracuseStep 2542117 = 476647) (by norm_num)
theorem B1485373 : Blo 1319478 1485373 := bbase (se 3 (by rfl) ⟨278507, by rfl⟩ : syracuseStep 1485373 = 557015) (by norm_num)
theorem B1485409 : Blo 1319478 1485409 := bbase (se 2 (by rfl) ⟨557028, by rfl⟩ : syracuseStep 1485409 = 1114057) (by norm_num)
theorem B1337977 : Blo 1319478 1337977 := bbase (se 2 (by rfl) ⟨501741, by rfl⟩ : syracuseStep 1337977 = 1003483) (by norm_num)
theorem B1485445 : Blo 1319478 1485445 := bbase (se 4 (by rfl) ⟨139260, by rfl⟩ : syracuseStep 1485445 = 278521) (by norm_num)
theorem B5638805 : Blo 1319478 5638805 := bbase (se 6 (by rfl) ⟨132159, by rfl⟩ : syracuseStep 5638805 = 264319) (by norm_num)
theorem B4459157 : Blo 1319478 4459157 := bbase (se 6 (by rfl) ⟨104511, by rfl⟩ : syracuseStep 4459157 = 209023) (by norm_num)
theorem B1485481 : Blo 1319478 1485481 := bbase (se 2 (by rfl) ⟨557055, by rfl⟩ : syracuseStep 1485481 = 1114111) (by norm_num)
theorem B1485517 : Blo 1319478 1485517 := bbase (se 3 (by rfl) ⟨278534, by rfl⟩ : syracuseStep 1485517 = 557069) (by norm_num)
theorem B1485553 : Blo 1319478 1485553 := bbase (se 2 (by rfl) ⟨557082, by rfl⟩ : syracuseStep 1485553 = 1114165) (by norm_num)
theorem B1485589 : Blo 1319478 1485589 := bbase (se 6 (by rfl) ⟨34818, by rfl⟩ : syracuseStep 1485589 = 69637) (by norm_num)
theorem B4516661 : Blo 1319478 4516661 := bbase (se 5 (by rfl) ⟨211718, by rfl⟩ : syracuseStep 4516661 = 423437) (by norm_num)
theorem B1485625 : Blo 1319478 1485625 := bbase (se 2 (by rfl) ⟨557109, by rfl⟩ : syracuseStep 1485625 = 1114219) (by norm_num)
theorem B1485661 : Blo 1319478 1485661 := bbase (se 3 (by rfl) ⟨278561, by rfl⟩ : syracuseStep 1485661 = 557123) (by norm_num)
theorem B1428337 : Blo 1319478 1428337 := bbase (se 2 (by rfl) ⟨535626, by rfl⟩ : syracuseStep 1428337 = 1071253) (by norm_num)
theorem B7523189 : Blo 1319478 7523189 := bbase (se 5 (by rfl) ⟨352649, by rfl⟩ : syracuseStep 7523189 = 705299) (by norm_num)
theorem B1485697 : Blo 1319478 1485697 := bbase (se 2 (by rfl) ⟨557136, by rfl⟩ : syracuseStep 1485697 = 1114273) (by norm_num)
theorem B4230053 : Blo 1319478 4230053 := bbase (se 4 (by rfl) ⟨396567, by rfl⟩ : syracuseStep 4230053 = 793135) (by norm_num)
theorem B1485733 : Blo 1319478 1485733 := bbase (se 4 (by rfl) ⟨139287, by rfl⟩ : syracuseStep 1485733 = 278575) (by norm_num)
theorem B1485769 : Blo 1319478 1485769 := bbase (se 2 (by rfl) ⟨557163, by rfl⟩ : syracuseStep 1485769 = 1114327) (by norm_num)
theorem B12856277 : Blo 1319478 12856277 := bbase (se 7 (by rfl) ⟨150659, by rfl⟩ : syracuseStep 12856277 = 301319) (by norm_num)
theorem B1485805 : Blo 1319478 1485805 := bbase (se 3 (by rfl) ⟨278588, by rfl⟩ : syracuseStep 1485805 = 557177) (by norm_num)
theorem B2116589 : Blo 1319478 2116589 := bbase (se 3 (by rfl) ⟨396860, by rfl⟩ : syracuseStep 2116589 = 793721) (by norm_num)
theorem B7515125 : Blo 1319478 7515125 := bbase (se 5 (by rfl) ⟨352271, by rfl⟩ : syracuseStep 7515125 = 704543) (by norm_num)
theorem B1485841 : Blo 1319478 1485841 := bbase (se 2 (by rfl) ⟨557190, by rfl⟩ : syracuseStep 1485841 = 1114381) (by norm_num)
theorem B3009565 : Blo 1319478 3009565 := bbase (se 3 (by rfl) ⟨564293, by rfl⟩ : syracuseStep 3009565 = 1128587) (by norm_num)
theorem B5016613 : Blo 1319478 5016613 := bbase (se 4 (by rfl) ⟨470307, by rfl⟩ : syracuseStep 5016613 = 940615) (by norm_num)
theorem B1485877 : Blo 1319478 1485877 := bbase (se 5 (by rfl) ⟨69650, by rfl⟩ : syracuseStep 1485877 = 139301) (by norm_num)
theorem B4459589 : Blo 1319478 4459589 := bbase (se 4 (by rfl) ⟨418086, by rfl⟩ : syracuseStep 4459589 = 836173) (by norm_num)
theorem B1485913 : Blo 1319478 1485913 := bbase (se 2 (by rfl) ⟨557217, by rfl⟩ : syracuseStep 1485913 = 1114435) (by norm_num)
theorem B6687845 : Blo 1319478 6687845 := bbase (se 4 (by rfl) ⟨626985, by rfl⟩ : syracuseStep 6687845 = 1253971) (by norm_num)
theorem B1879157 : Blo 1319478 1879157 := bbase (se 5 (by rfl) ⟨88085, by rfl⟩ : syracuseStep 1879157 = 176171) (by norm_num)
theorem B1485949 : Blo 1319478 1485949 := bbase (se 3 (by rfl) ⟨278615, by rfl⟩ : syracuseStep 1485949 = 557231) (by norm_num)
theorem B1485985 : Blo 1319478 1485985 := bbase (se 2 (by rfl) ⟨557244, by rfl⟩ : syracuseStep 1485985 = 1114489) (by norm_num)
theorem B1879237 : Blo 1319478 1879237 := bbase (se 4 (by rfl) ⟨176178, by rfl⟩ : syracuseStep 1879237 = 352357) (by norm_num)
theorem B1486021 : Blo 1319478 1486021 := bbase (se 4 (by rfl) ⟨139314, by rfl⟩ : syracuseStep 1486021 = 278629) (by norm_num)
theorem B2821333 : Blo 1319478 2821333 := bbase (se 7 (by rfl) ⟨33062, by rfl⟩ : syracuseStep 2821333 = 66125) (by norm_num)
theorem B1486057 : Blo 1319478 1486057 := bbase (se 2 (by rfl) ⟨557271, by rfl⟩ : syracuseStep 1486057 = 1114543) (by norm_num)
theorem B2968829 : Blo 1319478 2968829 := bbase (se 3 (by rfl) ⟨556655, by rfl⟩ : syracuseStep 2968829 = 1113311) (by norm_num)
theorem B1486093 : Blo 1319478 1486093 := bbase (se 3 (by rfl) ⟨278642, by rfl⟩ : syracuseStep 1486093 = 557285) (by norm_num)
theorem B2379029 : Blo 1319478 2379029 := bbase (se 6 (by rfl) ⟨55758, by rfl⟩ : syracuseStep 2379029 = 111517) (by norm_num)
theorem B1486129 : Blo 1319478 1486129 := bbase (se 2 (by rfl) ⟨557298, by rfl⟩ : syracuseStep 1486129 = 1114597) (by norm_num)
theorem B1879357 : Blo 1319478 1879357 := bbase (se 3 (by rfl) ⟨352379, by rfl⟩ : syracuseStep 1879357 = 704759) (by norm_num)
theorem B2968901 : Blo 1319478 2968901 := bbase (se 4 (by rfl) ⟨278334, by rfl⟩ : syracuseStep 2968901 = 556669) (by norm_num)
theorem B1609033 : Blo 1319478 1609033 := bbase (se 2 (by rfl) ⟨603387, by rfl⟩ : syracuseStep 1609033 = 1206775) (by norm_num)
theorem B1486165 : Blo 1319478 1486165 := bbase (se 11 (by rfl) ⟨1088, by rfl⟩ : syracuseStep 1486165 = 2177) (by norm_num)
theorem B5016917 : Blo 1319478 5016917 := bbase (se 11 (by rfl) ⟨3674, by rfl⟩ : syracuseStep 5016917 = 7349) (by norm_num)
theorem B1486201 : Blo 1319478 1486201 := bbase (se 2 (by rfl) ⟨557325, by rfl⟩ : syracuseStep 1486201 = 1114651) (by norm_num)
theorem B2968973 : Blo 1319478 2968973 := bbase (se 3 (by rfl) ⟨556682, by rfl⟩ : syracuseStep 2968973 = 1113365) (by norm_num)
theorem B1879453 : Blo 1319478 1879453 := bbase (se 3 (by rfl) ⟨352397, by rfl⟩ : syracuseStep 1879453 = 704795) (by norm_num)
theorem B1486237 : Blo 1319478 1486237 := bbase (se 3 (by rfl) ⟨278669, by rfl⟩ : syracuseStep 1486237 = 557339) (by norm_num)
theorem B1486273 : Blo 1319478 1486273 := bbase (se 2 (by rfl) ⟨557352, by rfl⟩ : syracuseStep 1486273 = 1114705) (by norm_num)
theorem B2969045 : Blo 1319478 2969045 := bbase (se 7 (by rfl) ⟨34793, by rfl⟩ : syracuseStep 2969045 = 69587) (by norm_num)
theorem B1338853 : Blo 1319478 1338853 := bbase (se 4 (by rfl) ⟨125517, by rfl⟩ : syracuseStep 1338853 = 251035) (by norm_num)
theorem B1486309 : Blo 1319478 1486309 := bbase (se 4 (by rfl) ⟨139341, by rfl⟩ : syracuseStep 1486309 = 278683) (by norm_num)
theorem B6680069 : Blo 1319478 6680069 := bbase (se 4 (by rfl) ⟨626256, by rfl⟩ : syracuseStep 6680069 = 1252513) (by norm_num)
theorem B1486345 : Blo 1319478 1486345 := bbase (se 2 (by rfl) ⟨557379, by rfl⟩ : syracuseStep 1486345 = 1114759) (by norm_num)
theorem B2969117 : Blo 1319478 2969117 := bbase (se 3 (by rfl) ⟨556709, by rfl⟩ : syracuseStep 2969117 = 1113419) (by norm_num)
theorem B1486381 : Blo 1319478 1486381 := bbase (se 3 (by rfl) ⟨278696, by rfl⟩ : syracuseStep 1486381 = 557393) (by norm_num)
theorem B2821709 : Blo 1319478 2821709 := bbase (se 3 (by rfl) ⟨529070, by rfl⟩ : syracuseStep 2821709 = 1058141) (by norm_num)
theorem B1486417 : Blo 1319478 1486417 := bbase (se 2 (by rfl) ⟨557406, by rfl⟩ : syracuseStep 1486417 = 1114813) (by norm_num)
theorem B2969189 : Blo 1319478 2969189 := bbase (se 4 (by rfl) ⟨278361, by rfl⟩ : syracuseStep 2969189 = 556723) (by norm_num)
theorem B1486453 : Blo 1319478 1486453 := bbase (se 5 (by rfl) ⟨69677, by rfl⟩ : syracuseStep 1486453 = 139355) (by norm_num)
theorem B1486489 : Blo 1319478 1486489 := bbase (se 2 (by rfl) ⟨557433, by rfl⟩ : syracuseStep 1486489 = 1114867) (by norm_num)
theorem B2969261 : Blo 1319478 2969261 := bbase (se 3 (by rfl) ⟨556736, by rfl⟩ : syracuseStep 2969261 = 1113473) (by norm_num)
theorem B1486525 : Blo 1319478 1486525 := bbase (se 3 (by rfl) ⟨278723, by rfl⟩ : syracuseStep 1486525 = 557447) (by norm_num)
theorem B1486561 : Blo 1319478 1486561 := bbase (se 2 (by rfl) ⟨557460, by rfl⟩ : syracuseStep 1486561 = 1114921) (by norm_num)
theorem B2969333 : Blo 1319478 2969333 := bbase (se 5 (by rfl) ⟨139187, by rfl⟩ : syracuseStep 2969333 = 278375) (by norm_num)
theorem B1486597 : Blo 1319478 1486597 := bbase (se 4 (by rfl) ⟨139368, by rfl⟩ : syracuseStep 1486597 = 278737) (by norm_num)
theorem B4230949 : Blo 1319478 4230949 := bbase (se 4 (by rfl) ⟨396651, by rfl⟩ : syracuseStep 4230949 = 793303) (by norm_num)
theorem B1486633 : Blo 1319478 1486633 := bbase (se 2 (by rfl) ⟨557487, by rfl⟩ : syracuseStep 1486633 = 1114975) (by norm_num)
theorem B2969405 : Blo 1319478 2969405 := bbase (se 3 (by rfl) ⟨556763, by rfl⟩ : syracuseStep 2969405 = 1113527) (by norm_num)
theorem B28946261 : Blo 1319478 28946261 := bbase (se 9 (by rfl) ⟨84803, by rfl⟩ : syracuseStep 28946261 = 169607) (by norm_num)
theorem B5082965 : Blo 1319478 5082965 := bbase (se 9 (by rfl) ⟨14891, by rfl⟩ : syracuseStep 5082965 = 29783) (by norm_num)
theorem B2969477 : Blo 1319478 2969477 := bbase (se 4 (by rfl) ⟨278388, by rfl⟩ : syracuseStep 2969477 = 556777) (by norm_num)
theorem B1879949 : Blo 1319478 1879949 := bbase (se 3 (by rfl) ⟨352490, by rfl⟩ : syracuseStep 1879949 = 704981) (by norm_num)
theorem B11284373 : Blo 1319478 11284373 := bbase (se 6 (by rfl) ⟨264477, by rfl⟩ : syracuseStep 11284373 = 528955) (by norm_num)
theorem B2969549 : Blo 1319478 2969549 := bbase (se 3 (by rfl) ⟨556790, by rfl⟩ : syracuseStep 2969549 = 1113581) (by norm_num)
theorem B6344693 : Blo 1319478 6344693 := bbase (se 5 (by rfl) ⟨297407, by rfl⟩ : syracuseStep 6344693 = 594815) (by norm_num)
theorem B2379773 : Blo 1319478 2379773 := bbase (se 3 (by rfl) ⟨446207, by rfl⟩ : syracuseStep 2379773 = 892415) (by norm_num)
theorem B2969621 : Blo 1319478 2969621 := bbase (se 6 (by rfl) ⟨69600, by rfl⟩ : syracuseStep 2969621 = 139201) (by norm_num)
theorem B7524373 : Blo 1319478 7524373 := bbase (se 6 (by rfl) ⟨176352, by rfl⟩ : syracuseStep 7524373 = 352705) (by norm_num)
theorem B10850357 : Blo 1319478 10850357 := bbase (se 5 (by rfl) ⟨508610, by rfl⟩ : syracuseStep 10850357 = 1017221) (by norm_num)
theorem B2412613 : Blo 1319478 2412613 := bbase (se 4 (by rfl) ⟨226182, by rfl⟩ : syracuseStep 2412613 = 452365) (by norm_num)
theorem B2969693 : Blo 1319478 2969693 := bbase (se 3 (by rfl) ⟨556817, by rfl⟩ : syracuseStep 2969693 = 1113635) (by norm_num)
theorem B1585289 : Blo 1319478 1585289 := bbase (se 2 (by rfl) ⟨594483, by rfl⟩ : syracuseStep 1585289 = 1188967) (by norm_num)
theorem B2969765 : Blo 1319478 2969765 := bbase (se 4 (by rfl) ⟨278415, by rfl⟩ : syracuseStep 2969765 = 556831) (by norm_num)
theorem B2969837 : Blo 1319478 2969837 := bbase (se 3 (by rfl) ⟨556844, by rfl⟩ : syracuseStep 2969837 = 1113689) (by norm_num)
theorem B3174653 : Blo 1319478 3174653 := bbase (se 3 (by rfl) ⟨595247, by rfl⟩ : syracuseStep 3174653 = 1190495) (by norm_num)
theorem B2969909 : Blo 1319478 2969909 := bbase (se 5 (by rfl) ⟨139214, by rfl⟩ : syracuseStep 2969909 = 278429) (by norm_num)
theorem B2937149 : Blo 1319478 2937149 := bbase (se 3 (by rfl) ⟨550715, by rfl⟩ : syracuseStep 2937149 = 1101431) (by norm_num)
theorem B6689141 : Blo 1319478 6689141 := bbase (se 5 (by rfl) ⟨313553, by rfl⟩ : syracuseStep 6689141 = 627107) (by norm_num)
theorem B2969981 : Blo 1319478 2969981 := bbase (se 3 (by rfl) ⟨556871, by rfl⟩ : syracuseStep 2969981 = 1113743) (by norm_num)
theorem B3617189 : Blo 1319478 3617189 := bbase (se 4 (by rfl) ⟨339111, by rfl⟩ : syracuseStep 3617189 = 678223) (by norm_num)
theorem B12038581 : Blo 1319478 12038581 := bbase (se 5 (by rfl) ⟨564308, by rfl⟩ : syracuseStep 12038581 = 1128617) (by norm_num)
theorem B1880501 : Blo 1319478 1880501 := bbase (se 5 (by rfl) ⟨88148, by rfl⟩ : syracuseStep 1880501 = 176297) (by norm_num)
theorem B8466869 : Blo 1319478 8466869 := bbase (se 5 (by rfl) ⟨396884, by rfl⟩ : syracuseStep 8466869 = 793769) (by norm_num)
theorem B1585597 : Blo 1319478 1585597 := bbase (se 3 (by rfl) ⟨297299, by rfl⟩ : syracuseStep 1585597 = 594599) (by norm_num)
theorem B2970053 : Blo 1319478 2970053 := bbase (se 4 (by rfl) ⟨278442, by rfl⟩ : syracuseStep 2970053 = 556885) (by norm_num)
theorem B2413061 : Blo 1319478 2413061 := bbase (se 4 (by rfl) ⟨226224, by rfl⟩ : syracuseStep 2413061 = 452449) (by norm_num)
theorem B2970125 : Blo 1319478 2970125 := bbase (se 3 (by rfl) ⟨556898, by rfl⟩ : syracuseStep 2970125 = 1113797) (by norm_num)
theorem B1585693 : Blo 1319478 1585693 := bbase (se 3 (by rfl) ⟨297317, by rfl⟩ : syracuseStep 1585693 = 594635) (by norm_num)
theorem B2970197 : Blo 1319478 2970197 := bbase (se 8 (by rfl) ⟨17403, by rfl⟩ : syracuseStep 2970197 = 34807) (by norm_num)
theorem B2970269 : Blo 1319478 2970269 := bbase (se 3 (by rfl) ⟨556925, by rfl⟩ : syracuseStep 2970269 = 1113851) (by norm_num)
theorem B1585837 : Blo 1319478 1585837 := bbase (se 3 (by rfl) ⟨297344, by rfl⟩ : syracuseStep 1585837 = 594689) (by norm_num)
theorem B2970341 : Blo 1319478 2970341 := bbase (se 4 (by rfl) ⟨278469, by rfl⟩ : syracuseStep 2970341 = 556939) (by norm_num)
theorem B2577125 : Blo 1319478 2577125 := bbase (se 4 (by rfl) ⟨241605, by rfl⟩ : syracuseStep 2577125 = 483211) (by norm_num)
theorem B6681365 : Blo 1319478 6681365 := bbase (se 6 (by rfl) ⟨156594, by rfl⟩ : syracuseStep 6681365 = 313189) (by norm_num)
theorem B6026005 : Blo 1319478 6026005 := bbase (se 6 (by rfl) ⟨141234, by rfl⟩ : syracuseStep 6026005 = 282469) (by norm_num)
theorem B2675501 : Blo 1319478 2675501 := bbase (se 3 (by rfl) ⟨501656, by rfl⟩ : syracuseStep 2675501 = 1003313) (by norm_num)
theorem B2970413 : Blo 1319478 2970413 := bbase (se 3 (by rfl) ⟨556952, by rfl⟩ : syracuseStep 2970413 = 1113905) (by norm_num)
theorem B1979237 : Blo 1319478 1979237 := bbase (se 4 (by rfl) ⟨185553, by rfl⟩ : syracuseStep 1979237 = 371107) (by norm_num)
theorem B2970485 : Blo 1319478 2970485 := bbase (se 5 (by rfl) ⟨139241, by rfl⟩ : syracuseStep 2970485 = 278483) (by norm_num)
theorem B1979261 : Blo 1319478 1979261 := bbase (se 3 (by rfl) ⟨371111, by rfl⟩ : syracuseStep 1979261 = 742223) (by norm_num)
theorem B2675581 : Blo 1319478 2675581 := bbase (se 3 (by rfl) ⟨501671, by rfl⟩ : syracuseStep 2675581 = 1003343) (by norm_num)
theorem B5641093 : Blo 1319478 5641093 := bbase (se 4 (by rfl) ⟨528852, by rfl⟩ : syracuseStep 5641093 = 1057705) (by norm_num)
theorem B1979285 : Blo 1319478 1979285 := bbase (se 6 (by rfl) ⟨46389, by rfl⟩ : syracuseStep 1979285 = 92779) (by norm_num)
theorem B1979309 : Blo 1319478 1979309 := bbase (se 3 (by rfl) ⟨371120, by rfl⟩ : syracuseStep 1979309 = 742241) (by norm_num)
theorem B2970557 : Blo 1319478 2970557 := bbase (se 3 (by rfl) ⟨556979, by rfl⟩ : syracuseStep 2970557 = 1113959) (by norm_num)
theorem B1979333 : Blo 1319478 1979333 := bbase (se 4 (by rfl) ⟨185562, by rfl⟩ : syracuseStep 1979333 = 371125) (by norm_num)
theorem B1979357 : Blo 1319478 1979357 := bbase (se 3 (by rfl) ⟨371129, by rfl⟩ : syracuseStep 1979357 = 742259) (by norm_num)
theorem B1979381 : Blo 1319478 1979381 := bbase (se 5 (by rfl) ⟨92783, by rfl⟩ : syracuseStep 1979381 = 185567) (by norm_num)
theorem B2380789 : Blo 1319478 2380789 := bbase (se 5 (by rfl) ⟨111599, by rfl⟩ : syracuseStep 2380789 = 223199) (by norm_num)
theorem B2970629 : Blo 1319478 2970629 := bbase (se 4 (by rfl) ⟨278496, by rfl⟩ : syracuseStep 2970629 = 556993) (by norm_num)
theorem B1979405 : Blo 1319478 1979405 := bbase (se 3 (by rfl) ⟨371138, by rfl⟩ : syracuseStep 1979405 = 742277) (by norm_num)
theorem B1979429 : Blo 1319478 1979429 := bbase (se 4 (by rfl) ⟨185571, by rfl⟩ : syracuseStep 1979429 = 371143) (by norm_num)
theorem B1979453 : Blo 1319478 1979453 := bbase (se 3 (by rfl) ⟨371147, by rfl⟩ : syracuseStep 1979453 = 742295) (by norm_num)
theorem B3011653 : Blo 1319478 3011653 := bbase (se 4 (by rfl) ⟨282342, by rfl⟩ : syracuseStep 3011653 = 564685) (by norm_num)
theorem B2970701 : Blo 1319478 2970701 := bbase (se 3 (by rfl) ⟨557006, by rfl⟩ : syracuseStep 2970701 = 1114013) (by norm_num)
theorem B1979477 : Blo 1319478 1979477 := bbase (se 8 (by rfl) ⟨11598, by rfl⟩ : syracuseStep 1979477 = 23197) (by norm_num)
theorem B1979501 : Blo 1319478 1979501 := bbase (se 3 (by rfl) ⟨371156, by rfl⟩ : syracuseStep 1979501 = 742313) (by norm_num)
theorem B1979525 : Blo 1319478 1979525 := bbase (se 4 (by rfl) ⟨185580, by rfl⟩ : syracuseStep 1979525 = 371161) (by norm_num)
theorem B2970773 : Blo 1319478 2970773 := bbase (se 6 (by rfl) ⟨69627, by rfl⟩ : syracuseStep 2970773 = 139255) (by norm_num)
theorem B1979549 : Blo 1319478 1979549 := bbase (se 3 (by rfl) ⟨371165, by rfl⟩ : syracuseStep 1979549 = 742331) (by norm_num)
theorem B4453541 : Blo 1319478 4453541 := bbase (se 4 (by rfl) ⟨417519, by rfl⟩ : syracuseStep 4453541 = 835039) (by norm_num)
theorem B1881253 : Blo 1319478 1881253 := bbase (se 4 (by rfl) ⟨176367, by rfl⟩ : syracuseStep 1881253 = 352735) (by norm_num)
theorem B1979573 : Blo 1319478 1979573 := bbase (se 5 (by rfl) ⟨92792, by rfl⟩ : syracuseStep 1979573 = 185585) (by norm_num)
theorem B1979597 : Blo 1319478 1979597 := bbase (se 3 (by rfl) ⟨371174, by rfl⟩ : syracuseStep 1979597 = 742349) (by norm_num)
theorem B2381005 : Blo 1319478 2381005 := bbase (se 3 (by rfl) ⟨446438, by rfl⟩ : syracuseStep 2381005 = 892877) (by norm_num)
theorem B2970845 : Blo 1319478 2970845 := bbase (se 3 (by rfl) ⟨557033, by rfl⟩ : syracuseStep 2970845 = 1114067) (by norm_num)
theorem B1979621 : Blo 1319478 1979621 := bbase (se 4 (by rfl) ⟨185589, by rfl⟩ : syracuseStep 1979621 = 371179) (by norm_num)
theorem B1979645 : Blo 1319478 1979645 := bbase (se 3 (by rfl) ⟨371183, by rfl⟩ : syracuseStep 1979645 = 742367) (by norm_num)
theorem B1979669 : Blo 1319478 1979669 := bbase (se 6 (by rfl) ⟨46398, by rfl⟩ : syracuseStep 1979669 = 92797) (by norm_num)
theorem B10704149 : Blo 1319478 10704149 := bbase (se 6 (by rfl) ⟨250878, by rfl⟩ : syracuseStep 10704149 = 501757) (by norm_num)
theorem B2970917 : Blo 1319478 2970917 := bbase (se 4 (by rfl) ⟨278523, by rfl⟩ : syracuseStep 2970917 = 557047) (by norm_num)
theorem B1979693 : Blo 1319478 1979693 := bbase (se 3 (by rfl) ⟨371192, by rfl⟩ : syracuseStep 1979693 = 742385) (by norm_num)
theorem B1979717 : Blo 1319478 1979717 := bbase (se 4 (by rfl) ⟨185598, by rfl⟩ : syracuseStep 1979717 = 371197) (by norm_num)
theorem B1979741 : Blo 1319478 1979741 := bbase (se 3 (by rfl) ⟨371201, by rfl⟩ : syracuseStep 1979741 = 742403) (by norm_num)
theorem B2970989 : Blo 1319478 2970989 := bbase (se 3 (by rfl) ⟨557060, by rfl⟩ : syracuseStep 2970989 = 1114121) (by norm_num)
theorem B1979765 : Blo 1319478 1979765 := bbase (se 5 (by rfl) ⟨92801, by rfl⟩ : syracuseStep 1979765 = 185603) (by norm_num)
theorem B1979789 : Blo 1319478 1979789 := bbase (se 3 (by rfl) ⟨371210, by rfl⟩ : syracuseStep 1979789 = 742421) (by norm_num)
theorem B1979813 : Blo 1319478 1979813 := bbase (se 4 (by rfl) ⟨185607, by rfl⟩ : syracuseStep 1979813 = 371215) (by norm_num)
theorem B2676149 : Blo 1319478 2676149 := bbase (se 5 (by rfl) ⟨125444, by rfl⟩ : syracuseStep 2676149 = 250889) (by norm_num)
theorem B2971061 : Blo 1319478 2971061 := bbase (se 5 (by rfl) ⟨139268, by rfl⟩ : syracuseStep 2971061 = 278537) (by norm_num)
theorem B1979837 : Blo 1319478 1979837 := bbase (se 3 (by rfl) ⟨371219, by rfl⟩ : syracuseStep 1979837 = 742439) (by norm_num)
theorem B1979861 : Blo 1319478 1979861 := bbase (se 7 (by rfl) ⟨23201, by rfl⟩ : syracuseStep 1979861 = 46403) (by norm_num)
theorem B1979885 : Blo 1319478 1979885 := bbase (se 3 (by rfl) ⟨371228, by rfl⟩ : syracuseStep 1979885 = 742457) (by norm_num)
theorem B2971133 : Blo 1319478 2971133 := bbase (se 3 (by rfl) ⟨557087, by rfl⟩ : syracuseStep 2971133 = 1114175) (by norm_num)
theorem B1979909 : Blo 1319478 1979909 := bbase (se 4 (by rfl) ⟨185616, by rfl⟩ : syracuseStep 1979909 = 371233) (by norm_num)
theorem B1979933 : Blo 1319478 1979933 := bbase (se 3 (by rfl) ⟨371237, by rfl⟩ : syracuseStep 1979933 = 742475) (by norm_num)
theorem B1979957 : Blo 1319478 1979957 := bbase (se 5 (by rfl) ⟨92810, by rfl⟩ : syracuseStep 1979957 = 185621) (by norm_num)
theorem B2143805 : Blo 1319478 2143805 := bbase (se 3 (by rfl) ⟨401963, by rfl⟩ : syracuseStep 2143805 = 803927) (by norm_num)
theorem B2971205 : Blo 1319478 2971205 := bbase (se 4 (by rfl) ⟨278550, by rfl⟩ : syracuseStep 2971205 = 557101) (by norm_num)
theorem B6346309 : Blo 1319478 6346309 := bbase (se 4 (by rfl) ⟨594966, by rfl⟩ : syracuseStep 6346309 = 1189933) (by norm_num)
theorem B1979981 : Blo 1319478 1979981 := bbase (se 3 (by rfl) ⟨371246, by rfl⟩ : syracuseStep 1979981 = 742493) (by norm_num)
theorem B4453973 : Blo 1319478 4453973 := bbase (se 8 (by rfl) ⟨26097, by rfl⟩ : syracuseStep 4453973 = 52195) (by norm_num)
theorem B1980005 : Blo 1319478 1980005 := bbase (se 4 (by rfl) ⟨185625, by rfl⟩ : syracuseStep 1980005 = 371251) (by norm_num)
theorem B1980029 : Blo 1319478 1980029 := bbase (se 3 (by rfl) ⟨371255, by rfl⟩ : syracuseStep 1980029 = 742511) (by norm_num)
theorem B3053189 : Blo 1319478 3053189 := bbase (se 4 (by rfl) ⟨286236, by rfl⟩ : syracuseStep 3053189 = 572473) (by norm_num)
theorem B2971277 : Blo 1319478 2971277 := bbase (se 3 (by rfl) ⟨557114, by rfl⟩ : syracuseStep 2971277 = 1114229) (by norm_num)
theorem B1980053 : Blo 1319478 1980053 := bbase (se 6 (by rfl) ⟨46407, by rfl⟩ : syracuseStep 1980053 = 92815) (by norm_num)
theorem B1586837 : Blo 1319478 1586837 := bbase (se 6 (by rfl) ⟨37191, by rfl⟩ : syracuseStep 1586837 = 74383) (by norm_num)
theorem B1980077 : Blo 1319478 1980077 := bbase (se 3 (by rfl) ⟨371264, by rfl⟩ : syracuseStep 1980077 = 742529) (by norm_num)
theorem B6772405 : Blo 1319478 6772405 := bbase (se 5 (by rfl) ⟨317456, by rfl⟩ : syracuseStep 6772405 = 634913) (by norm_num)
theorem B1980101 : Blo 1319478 1980101 := bbase (se 4 (by rfl) ⟨185634, by rfl⟩ : syracuseStep 1980101 = 371269) (by norm_num)
theorem B2971349 : Blo 1319478 2971349 := bbase (se 7 (by rfl) ⟨34820, by rfl⟩ : syracuseStep 2971349 = 69641) (by norm_num)
theorem B1980125 : Blo 1319478 1980125 := bbase (se 3 (by rfl) ⟨371273, by rfl⟩ : syracuseStep 1980125 = 742547) (by norm_num)
theorem B1980149 : Blo 1319478 1980149 := bbase (se 5 (by rfl) ⟨92819, by rfl⟩ : syracuseStep 1980149 = 185639) (by norm_num)
theorem B1980173 : Blo 1319478 1980173 := bbase (se 3 (by rfl) ⟨371282, by rfl⟩ : syracuseStep 1980173 = 742565) (by norm_num)
theorem B2971421 : Blo 1319478 2971421 := bbase (se 3 (by rfl) ⟨557141, by rfl⟩ : syracuseStep 2971421 = 1114283) (by norm_num)
theorem B1980197 : Blo 1319478 1980197 := bbase (se 4 (by rfl) ⟨185643, by rfl⟩ : syracuseStep 1980197 = 371287) (by norm_num)
theorem B5011253 : Blo 1319478 5011253 := bbase (se 5 (by rfl) ⟨234902, by rfl⟩ : syracuseStep 5011253 = 469805) (by norm_num)
theorem B1980221 : Blo 1319478 1980221 := bbase (se 3 (by rfl) ⟨371291, by rfl⟩ : syracuseStep 1980221 = 742583) (by norm_num)
theorem B1980245 : Blo 1319478 1980245 := bbase (se 9 (by rfl) ⟨5801, by rfl⟩ : syracuseStep 1980245 = 11603) (by norm_num)
theorem B1718101 : Blo 1319478 1718101 := bbase (se 9 (by rfl) ⟨5033, by rfl⟩ : syracuseStep 1718101 = 10067) (by norm_num)
theorem B2971493 : Blo 1319478 2971493 := bbase (se 4 (by rfl) ⟨278577, by rfl⟩ : syracuseStep 2971493 = 557155) (by norm_num)
theorem B1980269 : Blo 1319478 1980269 := bbase (se 3 (by rfl) ⟨371300, by rfl⟩ : syracuseStep 1980269 = 742601) (by norm_num)
theorem B1980293 : Blo 1319478 1980293 := bbase (se 4 (by rfl) ⟨185652, by rfl⟩ : syracuseStep 1980293 = 371305) (by norm_num)
theorem B2258837 : Blo 1319478 2258837 := bbase (se 6 (by rfl) ⟨52941, by rfl⟩ : syracuseStep 2258837 = 105883) (by norm_num)
theorem B1980317 : Blo 1319478 1980317 := bbase (se 3 (by rfl) ⟨371309, by rfl⟩ : syracuseStep 1980317 = 742619) (by norm_num)
theorem B2971565 : Blo 1319478 2971565 := bbase (se 3 (by rfl) ⟨557168, by rfl⟩ : syracuseStep 2971565 = 1114337) (by norm_num)
theorem B1980341 : Blo 1319478 1980341 := bbase (se 5 (by rfl) ⟨92828, by rfl⟩ : syracuseStep 1980341 = 185657) (by norm_num)
theorem B3340237 : Blo 1319478 3340237 := bbase (se 3 (by rfl) ⟨626294, by rfl⟩ : syracuseStep 3340237 = 1252589) (by norm_num)
theorem B1980365 : Blo 1319478 1980365 := bbase (se 3 (by rfl) ⟨371318, by rfl⟩ : syracuseStep 1980365 = 742637) (by norm_num)
theorem B1357777 : Blo 1319478 1357777 := bbase (se 2 (by rfl) ⟨509166, by rfl⟩ : syracuseStep 1357777 = 1018333) (by norm_num)
theorem B2856917 : Blo 1319478 2856917 := bbase (se 7 (by rfl) ⟨33479, by rfl⟩ : syracuseStep 2856917 = 66959) (by norm_num)
theorem B1980389 : Blo 1319478 1980389 := bbase (se 4 (by rfl) ⟨185661, by rfl⟩ : syracuseStep 1980389 = 371323) (by norm_num)
theorem B2971637 : Blo 1319478 2971637 := bbase (se 5 (by rfl) ⟨139295, by rfl⟩ : syracuseStep 2971637 = 278591) (by norm_num)
theorem B1980413 : Blo 1319478 1980413 := bbase (se 3 (by rfl) ⟨371327, by rfl⟩ : syracuseStep 1980413 = 742655) (by norm_num)
theorem B4454405 : Blo 1319478 4454405 := bbase (se 4 (by rfl) ⟨417600, by rfl⟩ : syracuseStep 4454405 = 835201) (by norm_num)
theorem B1980437 : Blo 1319478 1980437 := bbase (se 6 (by rfl) ⟨46416, by rfl⟩ : syracuseStep 1980437 = 92833) (by norm_num)
theorem B6682661 : Blo 1319478 6682661 := bbase (se 4 (by rfl) ⟨626499, by rfl⟩ : syracuseStep 6682661 = 1252999) (by norm_num)
theorem B1980461 : Blo 1319478 1980461 := bbase (se 3 (by rfl) ⟨371336, by rfl⟩ : syracuseStep 1980461 = 742673) (by norm_num)
theorem B2857013 : Blo 1319478 2857013 := bbase (se 5 (by rfl) ⟨133922, by rfl⟩ : syracuseStep 2857013 = 267845) (by norm_num)
theorem B5716021 : Blo 1319478 5716021 := bbase (se 5 (by rfl) ⟨267938, by rfl⟩ : syracuseStep 5716021 = 535877) (by norm_num)
theorem B3340349 : Blo 1319478 3340349 := bbase (se 3 (by rfl) ⟨626315, by rfl⟩ : syracuseStep 3340349 = 1252631) (by norm_num)
theorem B2971709 : Blo 1319478 2971709 := bbase (se 3 (by rfl) ⟨557195, by rfl⟩ : syracuseStep 2971709 = 1114391) (by norm_num)
theorem B1980485 : Blo 1319478 1980485 := bbase (se 4 (by rfl) ⟨185670, by rfl⟩ : syracuseStep 1980485 = 371341) (by norm_num)
theorem B5011541 : Blo 1319478 5011541 := bbase (se 8 (by rfl) ⟨29364, by rfl⟩ : syracuseStep 5011541 = 58729) (by norm_num)
theorem B5797973 : Blo 1319478 5797973 := bbase (se 8 (by rfl) ⟨33972, by rfl⟩ : syracuseStep 5797973 = 67945) (by norm_num)
theorem B1980509 : Blo 1319478 1980509 := bbase (se 3 (by rfl) ⟨371345, by rfl⟩ : syracuseStep 1980509 = 742691) (by norm_num)
theorem B1980533 : Blo 1319478 1980533 := bbase (se 5 (by rfl) ⟨92837, by rfl⟩ : syracuseStep 1980533 = 185675) (by norm_num)
theorem B2971781 : Blo 1319478 2971781 := bbase (se 4 (by rfl) ⟨278604, by rfl⟩ : syracuseStep 2971781 = 557209) (by norm_num)
theorem B1980557 : Blo 1319478 1980557 := bbase (se 3 (by rfl) ⟨371354, by rfl⟩ : syracuseStep 1980557 = 742709) (by norm_num)
theorem B1980581 : Blo 1319478 1980581 := bbase (se 4 (by rfl) ⟨185679, by rfl⟩ : syracuseStep 1980581 = 371359) (by norm_num)
theorem B1980605 : Blo 1319478 1980605 := bbase (se 3 (by rfl) ⟨371363, by rfl⟩ : syracuseStep 1980605 = 742727) (by norm_num)
theorem B2971853 : Blo 1319478 2971853 := bbase (se 3 (by rfl) ⟨557222, by rfl⟩ : syracuseStep 2971853 = 1114445) (by norm_num)
theorem B1980629 : Blo 1319478 1980629 := bbase (se 7 (by rfl) ⟨23210, by rfl⟩ : syracuseStep 1980629 = 46421) (by norm_num)
theorem B1980653 : Blo 1319478 1980653 := bbase (se 3 (by rfl) ⟨371372, by rfl⟩ : syracuseStep 1980653 = 742745) (by norm_num)
theorem B3340541 : Blo 1319478 3340541 := bbase (se 3 (by rfl) ⟨626351, by rfl⟩ : syracuseStep 3340541 = 1252703) (by norm_num)
theorem B1980677 : Blo 1319478 1980677 := bbase (se 4 (by rfl) ⟨185688, by rfl⟩ : syracuseStep 1980677 = 371377) (by norm_num)
theorem B2504981 : Blo 1319478 2504981 := bbase (se 6 (by rfl) ⟨58710, by rfl⟩ : syracuseStep 2504981 = 117421) (by norm_num)
theorem B2971925 : Blo 1319478 2971925 := bbase (se 6 (by rfl) ⟨69654, by rfl⟩ : syracuseStep 2971925 = 139309) (by norm_num)
theorem B1980701 : Blo 1319478 1980701 := bbase (se 3 (by rfl) ⟨371381, by rfl⟩ : syracuseStep 1980701 = 742763) (by norm_num)
theorem B1980725 : Blo 1319478 1980725 := bbase (se 5 (by rfl) ⟨92846, by rfl⟩ : syracuseStep 1980725 = 185693) (by norm_num)
theorem B1587529 : Blo 1319478 1587529 := bbase (se 2 (by rfl) ⟨595323, by rfl⟩ : syracuseStep 1587529 = 1190647) (by norm_num)
theorem B1980749 : Blo 1319478 1980749 := bbase (se 3 (by rfl) ⟨371390, by rfl⟩ : syracuseStep 1980749 = 742781) (by norm_num)
theorem B5642581 : Blo 1319478 5642581 := bbase (se 10 (by rfl) ⟨8265, by rfl⟩ : syracuseStep 5642581 = 16531) (by norm_num)
theorem B2971997 : Blo 1319478 2971997 := bbase (se 3 (by rfl) ⟨557249, by rfl⟩ : syracuseStep 2971997 = 1114499) (by norm_num)
theorem B1980773 : Blo 1319478 1980773 := bbase (se 4 (by rfl) ⟨185697, by rfl⟩ : syracuseStep 1980773 = 371395) (by norm_num)
theorem B5642597 : Blo 1319478 5642597 := bbase (se 4 (by rfl) ⟨528993, by rfl⟩ : syracuseStep 5642597 = 1057987) (by norm_num)
theorem B1980797 : Blo 1319478 1980797 := bbase (se 3 (by rfl) ⟨371399, by rfl⟩ : syracuseStep 1980797 = 742799) (by norm_num)
theorem B6429077 : Blo 1319478 6429077 := bbase (se 6 (by rfl) ⟨150681, by rfl⟩ : syracuseStep 6429077 = 301363) (by norm_num)
theorem B1980821 : Blo 1319478 1980821 := bbase (se 6 (by rfl) ⟨46425, by rfl⟩ : syracuseStep 1980821 = 92851) (by norm_num)
theorem B2972069 : Blo 1319478 2972069 := bbase (se 4 (by rfl) ⟨278631, by rfl⟩ : syracuseStep 2972069 = 557263) (by norm_num)
theorem B1980845 : Blo 1319478 1980845 := bbase (se 3 (by rfl) ⟨371408, by rfl⟩ : syracuseStep 1980845 = 742817) (by norm_num)
theorem B4454837 : Blo 1319478 4454837 := bbase (se 5 (by rfl) ⟨208820, by rfl⟩ : syracuseStep 4454837 = 417641) (by norm_num)
theorem B2226629 : Blo 1319478 2226629 := bbase (se 4 (by rfl) ⟨208746, by rfl⟩ : syracuseStep 2226629 = 417493) (by norm_num)
theorem B1980869 : Blo 1319478 1980869 := bbase (se 4 (by rfl) ⟨185706, by rfl⟩ : syracuseStep 1980869 = 371413) (by norm_num)
theorem B38091221 : Blo 1319478 38091221 := bbase (se 7 (by rfl) ⟨446381, by rfl⟩ : syracuseStep 38091221 = 892763) (by norm_num)
theorem B1980893 : Blo 1319478 1980893 := bbase (se 3 (by rfl) ⟨371417, by rfl⟩ : syracuseStep 1980893 = 742835) (by norm_num)
theorem B2972141 : Blo 1319478 2972141 := bbase (se 3 (by rfl) ⟨557276, by rfl⟩ : syracuseStep 2972141 = 1114553) (by norm_num)
theorem B1980917 : Blo 1319478 1980917 := bbase (se 5 (by rfl) ⟨92855, by rfl⟩ : syracuseStep 1980917 = 185711) (by norm_num)
theorem B1980941 : Blo 1319478 1980941 := bbase (se 3 (by rfl) ⟨371426, by rfl⟩ : syracuseStep 1980941 = 742853) (by norm_num)
theorem B1980965 : Blo 1319478 1980965 := bbase (se 4 (by rfl) ⟨185715, by rfl⟩ : syracuseStep 1980965 = 371431) (by norm_num)
theorem B2505269 : Blo 1319478 2505269 := bbase (se 5 (by rfl) ⟨117434, by rfl⟩ : syracuseStep 2505269 = 234869) (by norm_num)
theorem B2972213 : Blo 1319478 2972213 := bbase (se 5 (by rfl) ⟨139322, by rfl⟩ : syracuseStep 2972213 = 278645) (by norm_num)
theorem B1980989 : Blo 1319478 1980989 := bbase (se 3 (by rfl) ⟨371435, by rfl⟩ : syracuseStep 1980989 = 742871) (by norm_num)
theorem B2226757 : Blo 1319478 2226757 := bbase (se 4 (by rfl) ⟨208758, by rfl⟩ : syracuseStep 2226757 = 417517) (by norm_num)
theorem B2259533 : Blo 1319478 2259533 := bbase (se 3 (by rfl) ⟨423662, by rfl⟩ : syracuseStep 2259533 = 847325) (by norm_num)
theorem B3340885 : Blo 1319478 3340885 := bbase (se 8 (by rfl) ⟨19575, by rfl⟩ : syracuseStep 3340885 = 39151) (by norm_num)
theorem B1981013 : Blo 1319478 1981013 := bbase (se 8 (by rfl) ⟨11607, by rfl⟩ : syracuseStep 1981013 = 23215) (by norm_num)
theorem B1784413 : Blo 1319478 1784413 := bbase (se 3 (by rfl) ⟨334577, by rfl⟩ : syracuseStep 1784413 = 669155) (by norm_num)
theorem B1981037 : Blo 1319478 1981037 := bbase (se 3 (by rfl) ⟨371444, by rfl⟩ : syracuseStep 1981037 = 742889) (by norm_num)
theorem B2972285 : Blo 1319478 2972285 := bbase (se 3 (by rfl) ⟨557303, by rfl⟩ : syracuseStep 2972285 = 1114607) (by norm_num)
theorem B1981061 : Blo 1319478 1981061 := bbase (se 4 (by rfl) ⟨185724, by rfl⟩ : syracuseStep 1981061 = 371449) (by norm_num)
theorem B8575637 : Blo 1319478 8575637 := bbase (se 6 (by rfl) ⟨200991, by rfl⟩ : syracuseStep 8575637 = 401983) (by norm_num)
theorem B2226845 : Blo 1319478 2226845 := bbase (se 3 (by rfl) ⟨417533, by rfl⟩ : syracuseStep 2226845 = 835067) (by norm_num)
theorem B1981085 : Blo 1319478 1981085 := bbase (se 3 (by rfl) ⟨371453, by rfl⟩ : syracuseStep 1981085 = 742907) (by norm_num)
theorem B1981109 : Blo 1319478 1981109 := bbase (se 5 (by rfl) ⟨92864, by rfl⟩ : syracuseStep 1981109 = 185729) (by norm_num)
theorem B3340997 : Blo 1319478 3340997 := bbase (se 4 (by rfl) ⟨313218, by rfl⟩ : syracuseStep 3340997 = 626437) (by norm_num)
theorem B2972357 : Blo 1319478 2972357 := bbase (se 4 (by rfl) ⟨278658, by rfl⟩ : syracuseStep 2972357 = 557317) (by norm_num)
theorem B2505421 : Blo 1319478 2505421 := bbase (se 3 (by rfl) ⟨469766, by rfl⟩ : syracuseStep 2505421 = 939533) (by norm_num)
theorem B1981133 : Blo 1319478 1981133 := bbase (se 3 (by rfl) ⟨371462, by rfl⟩ : syracuseStep 1981133 = 742925) (by norm_num)
theorem B1981157 : Blo 1319478 1981157 := bbase (se 4 (by rfl) ⟨185733, by rfl⟩ : syracuseStep 1981157 = 371467) (by norm_num)
theorem B1981181 : Blo 1319478 1981181 := bbase (se 3 (by rfl) ⟨371471, by rfl⟩ : syracuseStep 1981181 = 742943) (by norm_num)
theorem B2972429 : Blo 1319478 2972429 := bbase (se 3 (by rfl) ⟨557330, by rfl⟩ : syracuseStep 2972429 = 1114661) (by norm_num)
theorem B1981205 : Blo 1319478 1981205 := bbase (se 6 (by rfl) ⟨46434, by rfl⟩ : syracuseStep 1981205 = 92869) (by norm_num)
theorem B2226973 : Blo 1319478 2226973 := bbase (se 3 (by rfl) ⟨417557, by rfl⟩ : syracuseStep 2226973 = 835115) (by norm_num)
theorem B1981229 : Blo 1319478 1981229 := bbase (se 3 (by rfl) ⟨371480, by rfl⟩ : syracuseStep 1981229 = 742961) (by norm_num)
theorem B11287349 : Blo 1319478 11287349 := bbase (se 5 (by rfl) ⟨529094, by rfl⟩ : syracuseStep 11287349 = 1058189) (by norm_num)
theorem B1981253 : Blo 1319478 1981253 := bbase (se 4 (by rfl) ⟨185742, by rfl⟩ : syracuseStep 1981253 = 371485) (by norm_num)
theorem B2972501 : Blo 1319478 2972501 := bbase (se 9 (by rfl) ⟨8708, by rfl⟩ : syracuseStep 2972501 = 17417) (by norm_num)
theorem B1981277 : Blo 1319478 1981277 := bbase (se 3 (by rfl) ⟨371489, by rfl⟩ : syracuseStep 1981277 = 742979) (by norm_num)
theorem B4455269 : Blo 1319478 4455269 := bbase (se 4 (by rfl) ⟨417681, by rfl⟩ : syracuseStep 4455269 = 835363) (by norm_num)
theorem B1669997 : Blo 1319478 1669997 := bbase (se 3 (by rfl) ⟨313124, by rfl⟩ : syracuseStep 1669997 = 626249) (by norm_num)
theorem B2227061 : Blo 1319478 2227061 := bbase (se 5 (by rfl) ⟨104393, by rfl⟩ : syracuseStep 2227061 = 208787) (by norm_num)
theorem B1981301 : Blo 1319478 1981301 := bbase (se 5 (by rfl) ⟨92873, by rfl⟩ : syracuseStep 1981301 = 185747) (by norm_num)
theorem B3341189 : Blo 1319478 3341189 := bbase (se 4 (by rfl) ⟨313236, by rfl⟩ : syracuseStep 3341189 = 626473) (by norm_num)
theorem B1981325 : Blo 1319478 1981325 := bbase (se 3 (by rfl) ⟨371498, by rfl⟩ : syracuseStep 1981325 = 742997) (by norm_num)
theorem B2972573 : Blo 1319478 2972573 := bbase (se 3 (by rfl) ⟨557357, by rfl⟩ : syracuseStep 2972573 = 1114715) (by norm_num)
theorem B1670053 : Blo 1319478 1670053 := bbase (se 4 (by rfl) ⟨156567, by rfl⟩ : syracuseStep 1670053 = 313135) (by norm_num)
theorem B1981349 : Blo 1319478 1981349 := bbase (se 4 (by rfl) ⟨185751, by rfl⟩ : syracuseStep 1981349 = 371503) (by norm_num)
theorem B3218357 : Blo 1319478 3218357 := bbase (se 5 (by rfl) ⟨150860, by rfl⟩ : syracuseStep 3218357 = 301721) (by norm_num)
theorem B1981373 : Blo 1319478 1981373 := bbase (se 3 (by rfl) ⟨371507, by rfl⟩ : syracuseStep 1981373 = 743015) (by norm_num)
theorem B1981397 : Blo 1319478 1981397 := bbase (se 7 (by rfl) ⟨23219, by rfl⟩ : syracuseStep 1981397 = 46439) (by norm_num)
theorem B2972645 : Blo 1319478 2972645 := bbase (se 4 (by rfl) ⟨278685, by rfl⟩ : syracuseStep 2972645 = 557371) (by norm_num)
theorem B1981421 : Blo 1319478 1981421 := bbase (se 3 (by rfl) ⟨371516, by rfl⟩ : syracuseStep 1981421 = 743033) (by norm_num)
theorem B2227189 : Blo 1319478 2227189 := bbase (se 5 (by rfl) ⟨104399, by rfl⟩ : syracuseStep 2227189 = 208799) (by norm_num)
theorem B2505725 : Blo 1319478 2505725 := bbase (se 3 (by rfl) ⟨469823, by rfl⟩ : syracuseStep 2505725 = 939647) (by norm_num)
theorem B1670149 : Blo 1319478 1670149 := bbase (se 4 (by rfl) ⟨156576, by rfl⟩ : syracuseStep 1670149 = 313153) (by norm_num)
theorem B1981445 : Blo 1319478 1981445 := bbase (se 4 (by rfl) ⟨185760, by rfl⟩ : syracuseStep 1981445 = 371521) (by norm_num)
theorem B1981469 : Blo 1319478 1981469 := bbase (se 3 (by rfl) ⟨371525, by rfl⟩ : syracuseStep 1981469 = 743051) (by norm_num)
theorem B2972717 : Blo 1319478 2972717 := bbase (se 3 (by rfl) ⟨557384, by rfl⟩ : syracuseStep 2972717 = 1114769) (by norm_num)
theorem B1981493 : Blo 1319478 1981493 := bbase (se 5 (by rfl) ⟨92882, by rfl⟩ : syracuseStep 1981493 = 185765) (by norm_num)
theorem B1694785 : Blo 1319478 1694785 := bbase (se 2 (by rfl) ⟨635544, by rfl⟩ : syracuseStep 1694785 = 1271089) (by norm_num)
theorem B2858053 : Blo 1319478 2858053 := bbase (se 4 (by rfl) ⟨267942, by rfl⟩ : syracuseStep 2858053 = 535885) (by norm_num)
theorem B5356613 : Blo 1319478 5356613 := bbase (se 4 (by rfl) ⟨502182, by rfl⟩ : syracuseStep 5356613 = 1004365) (by norm_num)
theorem B2227277 : Blo 1319478 2227277 := bbase (se 3 (by rfl) ⟨417614, by rfl⟩ : syracuseStep 2227277 = 835229) (by norm_num)
theorem B1981517 : Blo 1319478 1981517 := bbase (se 3 (by rfl) ⟨371534, by rfl⟩ : syracuseStep 1981517 = 743069) (by norm_num)
theorem B1981541 : Blo 1319478 1981541 := bbase (se 4 (by rfl) ⟨185769, by rfl⟩ : syracuseStep 1981541 = 371539) (by norm_num)
theorem B3013733 : Blo 1319478 3013733 := bbase (se 4 (by rfl) ⟨282537, by rfl⟩ : syracuseStep 3013733 = 565075) (by norm_num)
theorem B2972789 : Blo 1319478 2972789 := bbase (se 5 (by rfl) ⟨139349, by rfl⟩ : syracuseStep 2972789 = 278699) (by norm_num)
theorem B1981565 : Blo 1319478 1981565 := bbase (se 3 (by rfl) ⟨371543, by rfl⟩ : syracuseStep 1981565 = 743087) (by norm_num)
theorem B1981589 : Blo 1319478 1981589 := bbase (se 6 (by rfl) ⟨46443, by rfl⟩ : syracuseStep 1981589 = 92887) (by norm_num)
theorem B1981613 : Blo 1319478 1981613 := bbase (se 3 (by rfl) ⟨371552, by rfl⟩ : syracuseStep 1981613 = 743105) (by norm_num)
theorem B1670321 : Blo 1319478 1670321 := bbase (se 2 (by rfl) ⟨626370, by rfl⟩ : syracuseStep 1670321 = 1252741) (by norm_num)
theorem B2972861 : Blo 1319478 2972861 := bbase (se 3 (by rfl) ⟨557411, by rfl⟩ : syracuseStep 2972861 = 1114823) (by norm_num)
theorem B1981637 : Blo 1319478 1981637 := bbase (se 4 (by rfl) ⟨185778, by rfl⟩ : syracuseStep 1981637 = 371557) (by norm_num)
theorem B2227405 : Blo 1319478 2227405 := bbase (se 3 (by rfl) ⟨417638, by rfl⟩ : syracuseStep 2227405 = 835277) (by norm_num)
theorem B3759317 : Blo 1319478 3759317 := bbase (se 7 (by rfl) ⟨44054, by rfl⟩ : syracuseStep 3759317 = 88109) (by norm_num)
theorem B3341533 : Blo 1319478 3341533 := bbase (se 3 (by rfl) ⟨626537, by rfl⟩ : syracuseStep 3341533 = 1253075) (by norm_num)
theorem B1981661 : Blo 1319478 1981661 := bbase (se 3 (by rfl) ⟨371561, by rfl⟩ : syracuseStep 1981661 = 743123) (by norm_num)
theorem B1670377 : Blo 1319478 1670377 := bbase (se 2 (by rfl) ⟨626391, by rfl⟩ : syracuseStep 1670377 = 1252783) (by norm_num)
theorem B5012725 : Blo 1319478 5012725 := bbase (se 5 (by rfl) ⟨234971, by rfl⟩ : syracuseStep 5012725 = 469943) (by norm_num)
theorem B1981685 : Blo 1319478 1981685 := bbase (se 5 (by rfl) ⟨92891, by rfl⟩ : syracuseStep 1981685 = 185783) (by norm_num)
theorem B5160197 : Blo 1319478 5160197 := bbase (se 4 (by rfl) ⟨483768, by rfl⟩ : syracuseStep 5160197 = 967537) (by norm_num)
theorem B2972933 : Blo 1319478 2972933 := bbase (se 4 (by rfl) ⟨278712, by rfl⟩ : syracuseStep 2972933 = 557425) (by norm_num)
theorem B1981709 : Blo 1319478 1981709 := bbase (se 3 (by rfl) ⟨371570, by rfl⟩ : syracuseStep 1981709 = 743141) (by norm_num)
theorem B4455701 : Blo 1319478 4455701 := bbase (se 6 (by rfl) ⟨104430, by rfl⟩ : syracuseStep 4455701 = 208861) (by norm_num)
theorem B2227493 : Blo 1319478 2227493 := bbase (se 4 (by rfl) ⟨208827, by rfl⟩ : syracuseStep 2227493 = 417655) (by norm_num)
theorem B1981733 : Blo 1319478 1981733 := bbase (se 4 (by rfl) ⟨185787, by rfl⟩ : syracuseStep 1981733 = 371575) (by norm_num)
theorem B6683957 : Blo 1319478 6683957 := bbase (se 5 (by rfl) ⟨313310, by rfl⟩ : syracuseStep 6683957 = 626621) (by norm_num)
theorem B1981757 : Blo 1319478 1981757 := bbase (se 3 (by rfl) ⟨371579, by rfl⟩ : syracuseStep 1981757 = 743159) (by norm_num)
theorem B1670473 : Blo 1319478 1670473 := bbase (se 2 (by rfl) ⟨626427, by rfl⟩ : syracuseStep 1670473 = 1252855) (by norm_num)
theorem B3341645 : Blo 1319478 3341645 := bbase (se 3 (by rfl) ⟨626558, by rfl⟩ : syracuseStep 3341645 = 1253117) (by norm_num)
theorem B2973005 : Blo 1319478 2973005 := bbase (se 3 (by rfl) ⟨557438, by rfl⟩ : syracuseStep 2973005 = 1114877) (by norm_num)
theorem B1981781 : Blo 1319478 1981781 := bbase (se 11 (by rfl) ⟨1451, by rfl⟩ : syracuseStep 1981781 = 2903) (by norm_num)
theorem B1785181 : Blo 1319478 1785181 := bbase (se 3 (by rfl) ⟨334721, by rfl⟩ : syracuseStep 1785181 = 669443) (by norm_num)
theorem B1981805 : Blo 1319478 1981805 := bbase (se 3 (by rfl) ⟨371588, by rfl⟩ : syracuseStep 1981805 = 743177) (by norm_num)
theorem B1981829 : Blo 1319478 1981829 := bbase (se 4 (by rfl) ⟨185796, by rfl⟩ : syracuseStep 1981829 = 371593) (by norm_num)
theorem B2973077 : Blo 1319478 2973077 := bbase (se 6 (by rfl) ⟨69681, by rfl⟩ : syracuseStep 2973077 = 139363) (by norm_num)
theorem B1981853 : Blo 1319478 1981853 := bbase (se 3 (by rfl) ⟨371597, by rfl⟩ : syracuseStep 1981853 = 743195) (by norm_num)
theorem B2227621 : Blo 1319478 2227621 := bbase (se 4 (by rfl) ⟨208839, by rfl⟩ : syracuseStep 2227621 = 417679) (by norm_num)
theorem B1981877 : Blo 1319478 1981877 := bbase (se 5 (by rfl) ⟨92900, by rfl⟩ : syracuseStep 1981877 = 185801) (by norm_num)
theorem B1981901 : Blo 1319478 1981901 := bbase (se 3 (by rfl) ⟨371606, by rfl⟩ : syracuseStep 1981901 = 743213) (by norm_num)
theorem B2973149 : Blo 1319478 2973149 := bbase (se 3 (by rfl) ⟨557465, by rfl⟩ : syracuseStep 2973149 = 1114931) (by norm_num)
theorem B1981925 : Blo 1319478 1981925 := bbase (se 4 (by rfl) ⟨185805, by rfl⟩ : syracuseStep 1981925 = 371611) (by norm_num)
theorem B1670645 : Blo 1319478 1670645 := bbase (se 5 (by rfl) ⟨78311, by rfl⟩ : syracuseStep 1670645 = 156623) (by norm_num)
theorem B2227709 : Blo 1319478 2227709 := bbase (se 3 (by rfl) ⟨417695, by rfl⟩ : syracuseStep 2227709 = 835391) (by norm_num)
theorem B1981949 : Blo 1319478 1981949 := bbase (se 3 (by rfl) ⟨371615, by rfl⟩ : syracuseStep 1981949 = 743231) (by norm_num)
theorem B3341837 : Blo 1319478 3341837 := bbase (se 3 (by rfl) ⟨626594, by rfl⟩ : syracuseStep 3341837 = 1253189) (by norm_num)
theorem B1981973 : Blo 1319478 1981973 := bbase (se 6 (by rfl) ⟨46452, by rfl⟩ : syracuseStep 1981973 = 92905) (by norm_num)
theorem B5013029 : Blo 1319478 5013029 := bbase (se 4 (by rfl) ⟨469971, by rfl⟩ : syracuseStep 5013029 = 939943) (by norm_num)
theorem B2973221 : Blo 1319478 2973221 := bbase (se 4 (by rfl) ⟨278739, by rfl⟩ : syracuseStep 2973221 = 557479) (by norm_num)
theorem B1670701 : Blo 1319478 1670701 := bbase (se 3 (by rfl) ⟨313256, by rfl⟩ : syracuseStep 1670701 = 626513) (by norm_num)
theorem B1981997 : Blo 1319478 1981997 := bbase (se 3 (by rfl) ⟨371624, by rfl⟩ : syracuseStep 1981997 = 743249) (by norm_num)
theorem B1785397 : Blo 1319478 1785397 := bbase (se 5 (by rfl) ⟨83690, by rfl⟩ : syracuseStep 1785397 = 167381) (by norm_num)
theorem B1982021 : Blo 1319478 1982021 := bbase (se 4 (by rfl) ⟨185814, by rfl⟩ : syracuseStep 1982021 = 371629) (by norm_num)
theorem B1982045 : Blo 1319478 1982045 := bbase (se 3 (by rfl) ⟨371633, by rfl⟩ : syracuseStep 1982045 = 743267) (by norm_num)
theorem B2973293 : Blo 1319478 2973293 := bbase (se 3 (by rfl) ⟨557492, by rfl⟩ : syracuseStep 2973293 = 1114985) (by norm_num)
theorem B1982069 : Blo 1319478 1982069 := bbase (se 5 (by rfl) ⟨92909, by rfl⟩ : syracuseStep 1982069 = 185819) (by norm_num)
theorem B2227837 : Blo 1319478 2227837 := bbase (se 3 (by rfl) ⟨417719, by rfl⟩ : syracuseStep 2227837 = 835439) (by norm_num)
theorem B1670797 : Blo 1319478 1670797 := bbase (se 3 (by rfl) ⟨313274, by rfl⟩ : syracuseStep 1670797 = 626549) (by norm_num)
theorem B1982093 : Blo 1319478 1982093 := bbase (se 3 (by rfl) ⟨371642, by rfl⟩ : syracuseStep 1982093 = 743285) (by norm_num)
theorem B2678437 : Blo 1319478 2678437 := bbase (se 4 (by rfl) ⟨251103, by rfl⟩ : syracuseStep 2678437 = 502207) (by norm_num)
theorem B1982117 : Blo 1319478 1982117 := bbase (se 4 (by rfl) ⟨185823, by rfl⟩ : syracuseStep 1982117 = 371647) (by norm_num)
theorem B1982141 : Blo 1319478 1982141 := bbase (se 3 (by rfl) ⟨371651, by rfl⟩ : syracuseStep 1982141 = 743303) (by norm_num)
theorem B4456133 : Blo 1319478 4456133 := bbase (se 4 (by rfl) ⟨417762, by rfl⟩ : syracuseStep 4456133 = 835525) (by norm_num)
theorem B2227925 : Blo 1319478 2227925 := bbase (se 7 (by rfl) ⟨26108, by rfl⟩ : syracuseStep 2227925 = 52217) (by norm_num)
theorem B1982165 : Blo 1319478 1982165 := bbase (se 7 (by rfl) ⟨23228, by rfl⟩ : syracuseStep 1982165 = 46457) (by norm_num)
theorem B2506477 : Blo 1319478 2506477 := bbase (se 3 (by rfl) ⟨469964, by rfl⟩ : syracuseStep 2506477 = 939929) (by norm_num)
theorem B1982189 : Blo 1319478 1982189 := bbase (se 3 (by rfl) ⟨371660, by rfl⟩ : syracuseStep 1982189 = 743321) (by norm_num)
theorem B1982213 : Blo 1319478 1982213 := bbase (se 4 (by rfl) ⟨185832, by rfl⟩ : syracuseStep 1982213 = 371665) (by norm_num)
theorem B1670969 : Blo 1319478 1670969 := bbase (se 2 (by rfl) ⟨626613, by rfl⟩ : syracuseStep 1670969 = 1253227) (by norm_num)
theorem B16916309 : Blo 1319478 16916309 := bbase (se 9 (by rfl) ⟨49559, by rfl⟩ : syracuseStep 16916309 = 99119) (by norm_num)
theorem B2228053 : Blo 1319478 2228053 := bbase (se 9 (by rfl) ⟨6527, by rfl⟩ : syracuseStep 2228053 = 13055) (by norm_num)
theorem B3342181 : Blo 1319478 3342181 := bbase (se 4 (by rfl) ⟨313329, by rfl⟩ : syracuseStep 3342181 = 626659) (by norm_num)
theorem B1671025 : Blo 1319478 1671025 := bbase (se 2 (by rfl) ⟨626634, by rfl⟩ : syracuseStep 1671025 = 1253269) (by norm_num)
theorem B2506621 : Blo 1319478 2506621 := bbase (se 3 (by rfl) ⟨469991, by rfl⟩ : syracuseStep 2506621 = 939983) (by norm_num)
theorem B2228141 : Blo 1319478 2228141 := bbase (se 3 (by rfl) ⟨417776, by rfl⟩ : syracuseStep 2228141 = 835553) (by norm_num)
theorem B1671121 : Blo 1319478 1671121 := bbase (se 2 (by rfl) ⟨626670, by rfl⟩ : syracuseStep 1671121 = 1253341) (by norm_num)
theorem B3342293 : Blo 1319478 3342293 := bbase (se 7 (by rfl) ⟨39167, by rfl⟩ : syracuseStep 3342293 = 78335) (by norm_num)
theorem B1671187 : Blo 1319478 1671187 := bstep (se 1 (by rfl) ⟨1253390, by rfl⟩ : syracuseStep 1671187 = 2506781) B2506781
theorem B7233571 : Blo 1319478 7233571 := bstep (se 1 (by rfl) ⟨5425178, by rfl⟩ : syracuseStep 7233571 = 10850357) B10850357
theorem B5357603 : Blo 1319478 5357603 := bstep (se 1 (by rfl) ⟨4018202, by rfl⟩ : syracuseStep 5357603 = 8036405) B8036405
theorem B2818147 : Blo 1319478 2818147 := bstep (se 1 (by rfl) ⟨2113610, by rfl⟩ : syracuseStep 2818147 = 4227221) B4227221
theorem B2228323 : Blo 1319478 2228323 := bstep (se 1 (by rfl) ⟨1671242, by rfl⟩ : syracuseStep 2228323 = 3342485) B3342485
theorem B1671283 : Blo 1319478 1671283 := bstep (se 1 (by rfl) ⟨1253462, by rfl⟩ : syracuseStep 1671283 = 2506925) B2506925
theorem B3760273 : Blo 1319478 3760273 := bstep (se 2 (by rfl) ⟨1410102, by rfl⟩ : syracuseStep 3760273 = 2820205) B2820205
theorem B1958099 : Blo 1319478 1958099 := bstep (se 1 (by rfl) ⟨1468574, by rfl⟩ : syracuseStep 1958099 = 2937149) B2937149
theorem B2228465 : Blo 1319478 2228465 := bstep (se 2 (by rfl) ⟨835674, by rfl⟩ : syracuseStep 2228465 = 1671349) B1671349
theorem B7520525 : Blo 1319478 7520525 := bstep (se 3 (by rfl) ⟨1410098, by rfl⟩ : syracuseStep 7520525 = 2820197) B2820197
theorem B5644579 : Blo 1319478 5644579 := bstep (se 1 (by rfl) ⟨4233434, by rfl⟩ : syracuseStep 5644579 = 8466869) B8466869
theorem B1409347 : Blo 1319478 1409347 := bstep (se 1 (by rfl) ⟨1057010, by rfl⟩ : syracuseStep 1409347 = 2114021) B2114021
theorem B4456781 : Blo 1319478 4456781 := bstep (se 3 (by rfl) ⟨835646, by rfl⟩ : syracuseStep 4456781 = 1671293) B1671293
theorem B2507107 : Blo 1319478 2507107 := bstep (se 1 (by rfl) ⟨1880330, by rfl⟩ : syracuseStep 2507107 = 3760661) B3760661
theorem B4227437 : Blo 1319478 4227437 := bstep (se 3 (by rfl) ⟨792644, by rfl⟩ : syracuseStep 4227437 = 1585289) B1585289
theorem B2228593 : Blo 1319478 2228593 := bstep (se 2 (by rfl) ⟨835722, by rfl⟩ : syracuseStep 2228593 = 1671445) B1671445
theorem B4456835 : Blo 1319478 4456835 := bstep (se 1 (by rfl) ⟨3342626, by rfl⟩ : syracuseStep 4456835 = 6685253) B6685253
theorem B2228627 : Blo 1319478 2228627 := bstep (se 1 (by rfl) ⟨1671470, by rfl⟩ : syracuseStep 2228627 = 3342941) B3342941
theorem B6685091 : Blo 1319478 6685091 := bstep (se 1 (by rfl) ⟨5013818, by rfl⟩ : syracuseStep 6685091 = 10027637) B10027637
theorem B3170801 : Blo 1319478 3170801 := bstep (se 2 (by rfl) ⟨1189050, by rfl⟩ : syracuseStep 3170801 = 2378101) B2378101
theorem B5014001 : Blo 1319478 5014001 := bstep (se 2 (by rfl) ⟨1880250, by rfl⟩ : syracuseStep 5014001 = 3760501) B3760501
theorem B2507267 : Blo 1319478 2507267 := bstep (se 1 (by rfl) ⟨1880450, by rfl⟩ : syracuseStep 2507267 = 3760901) B3760901
theorem B2228755 : Blo 1319478 2228755 := bstep (se 1 (by rfl) ⟨1671566, by rfl⟩ : syracuseStep 2228755 = 3343133) B3343133
theorem B1319491 : Blo 1319478 1319491 := bstep (se 1 (by rfl) ⟨989618, by rfl⟩ : syracuseStep 1319491 = 1979237) B1979237
theorem B2114129 : Blo 1319478 2114129 := bstep (se 2 (by rfl) ⟨792798, by rfl⟩ : syracuseStep 2114129 = 1585597) B1585597
theorem B1319507 : Blo 1319478 1319507 := bstep (se 1 (by rfl) ⟨989630, by rfl⟩ : syracuseStep 1319507 = 1979261) B1979261
theorem B1319523 : Blo 1319478 1319523 := bstep (se 1 (by rfl) ⟨989642, by rfl⟩ : syracuseStep 1319523 = 1979285) B1979285
theorem B1671779 : Blo 1319478 1671779 := bstep (se 1 (by rfl) ⟨1253834, by rfl⟩ : syracuseStep 1671779 = 2507669) B2507669
theorem B1319539 : Blo 1319478 1319539 := bstep (se 1 (by rfl) ⟨989654, by rfl⟩ : syracuseStep 1319539 = 1979309) B1979309
theorem B1319555 : Blo 1319478 1319555 := bstep (se 1 (by rfl) ⟨989666, by rfl⟩ : syracuseStep 1319555 = 1979333) B1979333
theorem B7135877 : Blo 1319478 7135877 := bstep (se 4 (by rfl) ⟨668988, by rfl⟩ : syracuseStep 7135877 = 1337977) B1337977
theorem B4457105 : Blo 1319478 4457105 := bstep (se 2 (by rfl) ⟨1671414, by rfl⟩ : syracuseStep 4457105 = 3342829) B3342829
theorem B1319571 : Blo 1319478 1319571 := bstep (se 1 (by rfl) ⟨989678, by rfl⟩ : syracuseStep 1319571 = 1979357) B1979357
theorem B2228897 : Blo 1319478 2228897 := bstep (se 2 (by rfl) ⟨835836, by rfl⟩ : syracuseStep 2228897 = 1671673) B1671673
theorem B1319587 : Blo 1319478 1319587 := bstep (se 1 (by rfl) ⟨989690, by rfl⟩ : syracuseStep 1319587 = 1979381) B1979381
theorem B1319603 : Blo 1319478 1319603 := bstep (se 1 (by rfl) ⟨989702, by rfl⟩ : syracuseStep 1319603 = 1979405) B1979405
theorem B1319619 : Blo 1319478 1319619 := bstep (se 1 (by rfl) ⟨989714, by rfl⟩ : syracuseStep 1319619 = 1979429) B1979429
theorem B2114257 : Blo 1319478 2114257 := bstep (se 2 (by rfl) ⟨792846, by rfl⟩ : syracuseStep 2114257 = 1585693) B1585693
theorem B1319635 : Blo 1319478 1319635 := bstep (se 1 (by rfl) ⟨989726, by rfl⟩ : syracuseStep 1319635 = 1979453) B1979453
theorem B1319651 : Blo 1319478 1319651 := bstep (se 1 (by rfl) ⟨989738, by rfl⟩ : syracuseStep 1319651 = 1979477) B1979477
theorem B1319667 : Blo 1319478 1319667 := bstep (se 1 (by rfl) ⟨989750, by rfl⟩ : syracuseStep 1319667 = 1979501) B1979501
theorem B1319683 : Blo 1319478 1319683 := bstep (se 1 (by rfl) ⟨989762, by rfl⟩ : syracuseStep 1319683 = 1979525) B1979525
theorem B1319699 : Blo 1319478 1319699 := bstep (se 1 (by rfl) ⟨989774, by rfl⟩ : syracuseStep 1319699 = 1979549) B1979549
theorem B2229025 : Blo 1319478 2229025 := bstep (se 2 (by rfl) ⟨835884, by rfl⟩ : syracuseStep 2229025 = 1671769) B1671769
theorem B1319715 : Blo 1319478 1319715 := bstep (se 1 (by rfl) ⟨989786, by rfl⟩ : syracuseStep 1319715 = 1979573) B1979573
theorem B3343153 : Blo 1319478 3343153 := bstep (se 2 (by rfl) ⟨1253682, by rfl⟩ : syracuseStep 3343153 = 2507365) B2507365
theorem B1319731 : Blo 1319478 1319731 := bstep (se 1 (by rfl) ⟨989798, by rfl⟩ : syracuseStep 1319731 = 1979597) B1979597
theorem B1319747 : Blo 1319478 1319747 := bstep (se 1 (by rfl) ⟨989810, by rfl⟩ : syracuseStep 1319747 = 1979621) B1979621
theorem B2229059 : Blo 1319478 2229059 := bstep (se 1 (by rfl) ⟨1671794, by rfl⟩ : syracuseStep 2229059 = 3343589) B3343589
theorem B1319763 : Blo 1319478 1319763 := bstep (se 1 (by rfl) ⟨989822, by rfl⟩ : syracuseStep 1319763 = 1979645) B1979645
theorem B1319779 : Blo 1319478 1319779 := bstep (se 1 (by rfl) ⟨989834, by rfl⟩ : syracuseStep 1319779 = 1979669) B1979669
theorem B7136099 : Blo 1319478 7136099 := bstep (se 1 (by rfl) ⟨5352074, by rfl⟩ : syracuseStep 7136099 = 10704149) B10704149
theorem B1319795 : Blo 1319478 1319795 := bstep (se 1 (by rfl) ⟨989846, by rfl⟩ : syracuseStep 1319795 = 1979693) B1979693
theorem B1319811 : Blo 1319478 1319811 := bstep (se 1 (by rfl) ⟨989858, by rfl⟩ : syracuseStep 1319811 = 1979717) B1979717
theorem B1319827 : Blo 1319478 1319827 := bstep (se 1 (by rfl) ⟨989870, by rfl⟩ : syracuseStep 1319827 = 1979741) B1979741
theorem B1319843 : Blo 1319478 1319843 := bstep (se 1 (by rfl) ⟨989882, by rfl⟩ : syracuseStep 1319843 = 1979765) B1979765
theorem B1319859 : Blo 1319478 1319859 := bstep (se 1 (by rfl) ⟨989894, by rfl⟩ : syracuseStep 1319859 = 1979789) B1979789
theorem B1319875 : Blo 1319478 1319875 := bstep (se 1 (by rfl) ⟨989906, by rfl⟩ : syracuseStep 1319875 = 1979813) B1979813
theorem B2229187 : Blo 1319478 2229187 := bstep (se 1 (by rfl) ⟨1671890, by rfl⟩ : syracuseStep 2229187 = 3343781) B3343781
theorem B1319891 : Blo 1319478 1319891 := bstep (se 1 (by rfl) ⟨989918, by rfl⟩ : syracuseStep 1319891 = 1979837) B1979837
theorem B1319907 : Blo 1319478 1319907 := bstep (se 1 (by rfl) ⟨989930, by rfl⟩ : syracuseStep 1319907 = 1979861) B1979861
theorem B1319923 : Blo 1319478 1319923 := bstep (se 1 (by rfl) ⟨989942, by rfl⟩ : syracuseStep 1319923 = 1979885) B1979885
theorem B1319939 : Blo 1319478 1319939 := bstep (se 1 (by rfl) ⟨989954, by rfl⟩ : syracuseStep 1319939 = 1979909) B1979909
theorem B1319955 : Blo 1319478 1319955 := bstep (se 1 (by rfl) ⟨989966, by rfl⟩ : syracuseStep 1319955 = 1979933) B1979933
theorem B1319971 : Blo 1319478 1319971 := bstep (se 1 (by rfl) ⟨989978, by rfl⟩ : syracuseStep 1319971 = 1979957) B1979957
theorem B1319987 : Blo 1319478 1319987 := bstep (se 1 (by rfl) ⟨989990, by rfl⟩ : syracuseStep 1319987 = 1979981) B1979981
theorem B1320003 : Blo 1319478 1320003 := bstep (se 1 (by rfl) ⟨990002, by rfl⟩ : syracuseStep 1320003 = 1980005) B1980005
theorem B3343427 : Blo 1319478 3343427 := bstep (se 1 (by rfl) ⟨2507570, by rfl⟩ : syracuseStep 3343427 = 5015141) B5015141
theorem B12698693 : Blo 1319478 12698693 := bstep (se 4 (by rfl) ⟨1190502, by rfl⟩ : syracuseStep 12698693 = 2381005) B2381005
theorem B2229329 : Blo 1319478 2229329 := bstep (se 2 (by rfl) ⟨835998, by rfl⟩ : syracuseStep 2229329 = 1671997) B1671997
theorem B1320019 : Blo 1319478 1320019 := bstep (se 1 (by rfl) ⟨990014, by rfl⟩ : syracuseStep 1320019 = 1980029) B1980029
theorem B1320035 : Blo 1319478 1320035 := bstep (se 1 (by rfl) ⟨990026, by rfl⟩ : syracuseStep 1320035 = 1980053) B1980053
theorem B1320051 : Blo 1319478 1320051 := bstep (se 1 (by rfl) ⟨990038, by rfl⟩ : syracuseStep 1320051 = 1980077) B1980077
theorem B1320067 : Blo 1319478 1320067 := bstep (se 1 (by rfl) ⟨990050, by rfl⟩ : syracuseStep 1320067 = 1980101) B1980101
theorem B5014669 : Blo 1319478 5014669 := bstep (se 3 (by rfl) ⟨940250, by rfl⟩ : syracuseStep 5014669 = 1880501) B1880501
theorem B1320083 : Blo 1319478 1320083 := bstep (se 1 (by rfl) ⟨990062, by rfl⟩ : syracuseStep 1320083 = 1980125) B1980125
theorem B1320099 : Blo 1319478 1320099 := bstep (se 1 (by rfl) ⟨990074, by rfl⟩ : syracuseStep 1320099 = 1980149) B1980149
theorem B4457645 : Blo 1319478 4457645 := bstep (se 3 (by rfl) ⟨835808, by rfl⟩ : syracuseStep 4457645 = 1671617) B1671617
theorem B7521457 : Blo 1319478 7521457 := bstep (se 2 (by rfl) ⟨2820546, by rfl⟩ : syracuseStep 7521457 = 5641093) B5641093
theorem B1320115 : Blo 1319478 1320115 := bstep (se 1 (by rfl) ⟨990086, by rfl⟩ : syracuseStep 1320115 = 1980173) B1980173
theorem B1320131 : Blo 1319478 1320131 := bstep (se 1 (by rfl) ⟨990098, by rfl⟩ : syracuseStep 1320131 = 1980197) B1980197
theorem B6685901 : Blo 1319478 6685901 := bstep (se 3 (by rfl) ⟨1253606, by rfl⟩ : syracuseStep 6685901 = 2507213) B2507213
theorem B2229457 : Blo 1319478 2229457 := bstep (se 2 (by rfl) ⟨836046, by rfl⟩ : syracuseStep 2229457 = 1672093) B1672093
theorem B1320147 : Blo 1319478 1320147 := bstep (se 1 (by rfl) ⟨990110, by rfl⟩ : syracuseStep 1320147 = 1980221) B1980221
theorem B1320163 : Blo 1319478 1320163 := bstep (se 1 (by rfl) ⟨990122, by rfl⟩ : syracuseStep 1320163 = 1980245) B1980245
theorem B4457699 : Blo 1319478 4457699 := bstep (se 1 (by rfl) ⟨3343274, by rfl⟩ : syracuseStep 4457699 = 6686549) B6686549
theorem B1320179 : Blo 1319478 1320179 := bstep (se 1 (by rfl) ⟨990134, by rfl⟩ : syracuseStep 1320179 = 1980269) B1980269
theorem B2229491 : Blo 1319478 2229491 := bstep (se 1 (by rfl) ⟨1672118, by rfl⟩ : syracuseStep 2229491 = 3344237) B3344237
theorem B1320195 : Blo 1319478 1320195 := bstep (se 1 (by rfl) ⟨990146, by rfl⟩ : syracuseStep 1320195 = 1980293) B1980293
theorem B3343619 : Blo 1319478 3343619 := bstep (se 1 (by rfl) ⟨2507714, by rfl⟩ : syracuseStep 3343619 = 5015429) B5015429
theorem B1320211 : Blo 1319478 1320211 := bstep (se 1 (by rfl) ⟨990158, by rfl⟩ : syracuseStep 1320211 = 1980317) B1980317
theorem B1320227 : Blo 1319478 1320227 := bstep (se 1 (by rfl) ⟨990170, by rfl⟩ : syracuseStep 1320227 = 1980341) B1980341
theorem B1672483 : Blo 1319478 1672483 := bstep (se 1 (by rfl) ⟨1254362, by rfl⟩ : syracuseStep 1672483 = 2508725) B2508725
theorem B2819377 : Blo 1319478 2819377 := bstep (se 2 (by rfl) ⟨1057266, by rfl⟩ : syracuseStep 2819377 = 2114533) B2114533
theorem B1320243 : Blo 1319478 1320243 := bstep (se 1 (by rfl) ⟨990182, by rfl⟩ : syracuseStep 1320243 = 1980365) B1980365
theorem B1320259 : Blo 1319478 1320259 := bstep (se 1 (by rfl) ⟨990194, by rfl⟩ : syracuseStep 1320259 = 1980389) B1980389
theorem B1320275 : Blo 1319478 1320275 := bstep (se 1 (by rfl) ⟨990206, by rfl⟩ : syracuseStep 1320275 = 1980413) B1980413
theorem B1320291 : Blo 1319478 1320291 := bstep (se 1 (by rfl) ⟨990218, by rfl⟩ : syracuseStep 1320291 = 1980437) B1980437
theorem B13731185 : Blo 1319478 13731185 := bstep (se 2 (by rfl) ⟨5149194, by rfl⟩ : syracuseStep 13731185 = 10298389) B10298389
theorem B1320307 : Blo 1319478 1320307 := bstep (se 1 (by rfl) ⟨990230, by rfl⟩ : syracuseStep 1320307 = 1980461) B1980461
theorem B1410419 : Blo 1319478 1410419 := bstep (se 1 (by rfl) ⟨1057814, by rfl⟩ : syracuseStep 1410419 = 2115629) B2115629
theorem B2229619 : Blo 1319478 2229619 := bstep (se 1 (by rfl) ⟨1672214, by rfl⟩ : syracuseStep 2229619 = 3344429) B3344429
theorem B1320323 : Blo 1319478 1320323 := bstep (se 1 (by rfl) ⟨990242, by rfl⟩ : syracuseStep 1320323 = 1980485) B1980485
theorem B3761549 : Blo 1319478 3761549 := bstep (se 3 (by rfl) ⟨705290, by rfl⟩ : syracuseStep 3761549 = 1410581) B1410581
theorem B1320339 : Blo 1319478 1320339 := bstep (se 1 (by rfl) ⟨990254, by rfl⟩ : syracuseStep 1320339 = 1980509) B1980509
theorem B5637539 : Blo 1319478 5637539 := bstep (se 1 (by rfl) ⟨4228154, by rfl⟩ : syracuseStep 5637539 = 8456309) B8456309
theorem B1320355 : Blo 1319478 1320355 := bstep (se 1 (by rfl) ⟨990266, by rfl⟩ : syracuseStep 1320355 = 1980533) B1980533
theorem B3810737 : Blo 1319478 3810737 := bstep (se 2 (by rfl) ⟨1429026, by rfl⟩ : syracuseStep 3810737 = 2858053) B2858053
theorem B4015537 : Blo 1319478 4015537 := bstep (se 2 (by rfl) ⟨1505826, by rfl⟩ : syracuseStep 4015537 = 3011653) B3011653
theorem B1320371 : Blo 1319478 1320371 := bstep (se 1 (by rfl) ⟨990278, by rfl⟩ : syracuseStep 1320371 = 1980557) B1980557
theorem B1320387 : Blo 1319478 1320387 := bstep (se 1 (by rfl) ⟨990290, by rfl⟩ : syracuseStep 1320387 = 1980581) B1980581
theorem B32138693 : Blo 1319478 32138693 := bstep (se 4 (by rfl) ⟨3013002, by rfl⟩ : syracuseStep 32138693 = 6026005) B6026005
theorem B1320403 : Blo 1319478 1320403 := bstep (se 1 (by rfl) ⟨990302, by rfl⟩ : syracuseStep 1320403 = 1980605) B1980605
theorem B1320419 : Blo 1319478 1320419 := bstep (se 1 (by rfl) ⟨990314, by rfl⟩ : syracuseStep 1320419 = 1980629) B1980629
theorem B4457969 : Blo 1319478 4457969 := bstep (se 2 (by rfl) ⟨1671738, by rfl⟩ : syracuseStep 4457969 = 3343477) B3343477
theorem B1320435 : Blo 1319478 1320435 := bstep (se 1 (by rfl) ⟨990326, by rfl⟩ : syracuseStep 1320435 = 1980653) B1980653
theorem B2229761 : Blo 1319478 2229761 := bstep (se 2 (by rfl) ⟨836160, by rfl⟩ : syracuseStep 2229761 = 1672321) B1672321
theorem B1320451 : Blo 1319478 1320451 := bstep (se 1 (by rfl) ⟨990338, by rfl⟩ : syracuseStep 1320451 = 1980677) B1980677
theorem B1320467 : Blo 1319478 1320467 := bstep (se 1 (by rfl) ⟨990350, by rfl⟩ : syracuseStep 1320467 = 1980701) B1980701
theorem B1320483 : Blo 1319478 1320483 := bstep (se 1 (by rfl) ⟨990362, by rfl⟩ : syracuseStep 1320483 = 1980725) B1980725
theorem B2508337 : Blo 1319478 2508337 := bstep (se 2 (by rfl) ⟨940626, by rfl⟩ : syracuseStep 2508337 = 1881253) B1881253
theorem B1320499 : Blo 1319478 1320499 := bstep (se 1 (by rfl) ⟨990374, by rfl⟩ : syracuseStep 1320499 = 1980749) B1980749
theorem B1320515 : Blo 1319478 1320515 := bstep (se 1 (by rfl) ⟨990386, by rfl⟩ : syracuseStep 1320515 = 1980773) B1980773
theorem B3761731 : Blo 1319478 3761731 := bstep (se 1 (by rfl) ⟨2821298, by rfl⟩ : syracuseStep 3761731 = 5642597) B5642597
theorem B1320531 : Blo 1319478 1320531 := bstep (se 1 (by rfl) ⟨990398, by rfl⟩ : syracuseStep 1320531 = 1980797) B1980797
theorem B4286051 : Blo 1319478 4286051 := bstep (se 1 (by rfl) ⟨3214538, by rfl⟩ : syracuseStep 4286051 = 6429077) B6429077
theorem B1320547 : Blo 1319478 1320547 := bstep (se 1 (by rfl) ⟨990410, by rfl⟩ : syracuseStep 1320547 = 1980821) B1980821
theorem B3761777 : Blo 1319478 3761777 := bstep (se 2 (by rfl) ⟨1410666, by rfl⟩ : syracuseStep 3761777 = 2821333) B2821333
theorem B1320563 : Blo 1319478 1320563 := bstep (se 1 (by rfl) ⟨990422, by rfl⟩ : syracuseStep 1320563 = 1980845) B1980845
theorem B2229889 : Blo 1319478 2229889 := bstep (se 2 (by rfl) ⟨836208, by rfl⟩ : syracuseStep 2229889 = 1672417) B1672417
theorem B1484419 : Blo 1319478 1484419 := bstep (se 1 (by rfl) ⟨1113314, by rfl⟩ : syracuseStep 1484419 = 2226629) B2226629
theorem B1320579 : Blo 1319478 1320579 := bstep (se 1 (by rfl) ⟨990434, by rfl⟩ : syracuseStep 1320579 = 1980869) B1980869
theorem B1320595 : Blo 1319478 1320595 := bstep (se 1 (by rfl) ⟨990446, by rfl⟩ : syracuseStep 1320595 = 1980893) B1980893
theorem B1320611 : Blo 1319478 1320611 := bstep (se 1 (by rfl) ⟨990458, by rfl⟩ : syracuseStep 1320611 = 1980917) B1980917
theorem B2229923 : Blo 1319478 2229923 := bstep (se 1 (by rfl) ⟨1672442, by rfl⟩ : syracuseStep 2229923 = 3344885) B3344885
theorem B1607347 : Blo 1319478 1607347 := bstep (se 1 (by rfl) ⟨1205510, by rfl⟩ : syracuseStep 1607347 = 2411021) B2411021
theorem B2115251 : Blo 1319478 2115251 := bstep (se 1 (by rfl) ⟨1586438, by rfl⟩ : syracuseStep 2115251 = 3172877) B3172877
theorem B1320627 : Blo 1319478 1320627 := bstep (se 1 (by rfl) ⟨990470, by rfl⟩ : syracuseStep 1320627 = 1980941) B1980941
theorem B1320643 : Blo 1319478 1320643 := bstep (se 1 (by rfl) ⟨990482, by rfl⟩ : syracuseStep 1320643 = 1980965) B1980965
theorem B1320659 : Blo 1319478 1320659 := bstep (se 1 (by rfl) ⟨990494, by rfl⟩ : syracuseStep 1320659 = 1980989) B1980989
theorem B1320675 : Blo 1319478 1320675 := bstep (se 1 (by rfl) ⟨990506, by rfl⟩ : syracuseStep 1320675 = 1981013) B1981013
theorem B1320691 : Blo 1319478 1320691 := bstep (se 1 (by rfl) ⟨990518, by rfl⟩ : syracuseStep 1320691 = 1981037) B1981037
theorem B1320707 : Blo 1319478 1320707 := bstep (se 1 (by rfl) ⟨990530, by rfl⟩ : syracuseStep 1320707 = 1981061) B1981061
theorem B1484563 : Blo 1319478 1484563 := bstep (se 1 (by rfl) ⟨1113422, by rfl⟩ : syracuseStep 1484563 = 2226845) B2226845
theorem B1320723 : Blo 1319478 1320723 := bstep (se 1 (by rfl) ⟨990542, by rfl⟩ : syracuseStep 1320723 = 1981085) B1981085
theorem B1320739 : Blo 1319478 1320739 := bstep (se 1 (by rfl) ⟨990554, by rfl⟩ : syracuseStep 1320739 = 1981109) B1981109
theorem B1320755 : Blo 1319478 1320755 := bstep (se 1 (by rfl) ⟨990566, by rfl⟩ : syracuseStep 1320755 = 1981133) B1981133
theorem B1320771 : Blo 1319478 1320771 := bstep (se 1 (by rfl) ⟨990578, by rfl⟩ : syracuseStep 1320771 = 1981157) B1981157
theorem B1320787 : Blo 1319478 1320787 := bstep (se 1 (by rfl) ⟨990590, by rfl⟩ : syracuseStep 1320787 = 1981181) B1981181
theorem B1320803 : Blo 1319478 1320803 := bstep (se 1 (by rfl) ⟨990602, by rfl⟩ : syracuseStep 1320803 = 1981205) B1981205
theorem B1320819 : Blo 1319478 1320819 := bstep (se 1 (by rfl) ⟨990614, by rfl⟩ : syracuseStep 1320819 = 1981229) B1981229
theorem B1320835 : Blo 1319478 1320835 := bstep (se 1 (by rfl) ⟨990626, by rfl⟩ : syracuseStep 1320835 = 1981253) B1981253
theorem B1320851 : Blo 1319478 1320851 := bstep (se 1 (by rfl) ⟨990638, by rfl⟩ : syracuseStep 1320851 = 1981277) B1981277
theorem B1484707 : Blo 1319478 1484707 := bstep (se 1 (by rfl) ⟨1113530, by rfl⟩ : syracuseStep 1484707 = 2227061) B2227061
theorem B1320867 : Blo 1319478 1320867 := bstep (se 1 (by rfl) ⟨990650, by rfl⟩ : syracuseStep 1320867 = 1981301) B1981301
theorem B5015459 : Blo 1319478 5015459 := bstep (se 1 (by rfl) ⟨3761594, by rfl⟩ : syracuseStep 5015459 = 7523189) B7523189
theorem B1320883 : Blo 1319478 1320883 := bstep (se 1 (by rfl) ⟨990662, by rfl⟩ : syracuseStep 1320883 = 1981325) B1981325
theorem B2820035 : Blo 1319478 2820035 := bstep (se 1 (by rfl) ⟨2115026, by rfl⟩ : syracuseStep 2820035 = 4230053) B4230053
theorem B1320899 : Blo 1319478 1320899 := bstep (se 1 (by rfl) ⟨990674, by rfl⟩ : syracuseStep 1320899 = 1981349) B1981349
theorem B1320915 : Blo 1319478 1320915 := bstep (se 1 (by rfl) ⟨990686, by rfl⟩ : syracuseStep 1320915 = 1981373) B1981373
theorem B1320931 : Blo 1319478 1320931 := bstep (se 1 (by rfl) ⟨990698, by rfl⟩ : syracuseStep 1320931 = 1981397) B1981397
theorem B1320947 : Blo 1319478 1320947 := bstep (se 1 (by rfl) ⟨990710, by rfl⟩ : syracuseStep 1320947 = 1981421) B1981421
theorem B1320963 : Blo 1319478 1320963 := bstep (se 1 (by rfl) ⟨990722, by rfl⟩ : syracuseStep 1320963 = 1981445) B1981445
theorem B10709005 : Blo 1319478 10709005 := bstep (se 3 (by rfl) ⟨2007938, by rfl⟩ : syracuseStep 10709005 = 4015877) B4015877
theorem B4458509 : Blo 1319478 4458509 := bstep (se 3 (by rfl) ⟨835970, by rfl⟩ : syracuseStep 4458509 = 1671941) B1671941
theorem B1320979 : Blo 1319478 1320979 := bstep (se 1 (by rfl) ⟨990734, by rfl⟩ : syracuseStep 1320979 = 1981469) B1981469
theorem B1320995 : Blo 1319478 1320995 := bstep (se 1 (by rfl) ⟨990746, by rfl⟩ : syracuseStep 1320995 = 1981493) B1981493
theorem B1484851 : Blo 1319478 1484851 := bstep (se 1 (by rfl) ⟨1113638, by rfl⟩ : syracuseStep 1484851 = 2227277) B2227277
theorem B1321011 : Blo 1319478 1321011 := bstep (se 1 (by rfl) ⟨990758, by rfl⟩ : syracuseStep 1321011 = 1981517) B1981517
theorem B1321027 : Blo 1319478 1321027 := bstep (se 1 (by rfl) ⟨990770, by rfl⟩ : syracuseStep 1321027 = 1981541) B1981541
theorem B4458563 : Blo 1319478 4458563 := bstep (se 1 (by rfl) ⟨3343922, by rfl⟩ : syracuseStep 4458563 = 6687845) B6687845
theorem B2009155 : Blo 1319478 2009155 := bstep (se 1 (by rfl) ⟨1506866, by rfl⟩ : syracuseStep 2009155 = 3013733) B3013733
theorem B1321043 : Blo 1319478 1321043 := bstep (se 1 (by rfl) ⟨990782, by rfl⟩ : syracuseStep 1321043 = 1981565) B1981565
theorem B1321059 : Blo 1319478 1321059 := bstep (se 1 (by rfl) ⟨990794, by rfl⟩ : syracuseStep 1321059 = 1981589) B1981589
theorem B1321075 : Blo 1319478 1321075 := bstep (se 1 (by rfl) ⟨990806, by rfl⟩ : syracuseStep 1321075 = 1981613) B1981613
theorem B1321091 : Blo 1319478 1321091 := bstep (se 1 (by rfl) ⟨990818, by rfl⟩ : syracuseStep 1321091 = 1981637) B1981637
theorem B1321107 : Blo 1319478 1321107 := bstep (se 1 (by rfl) ⟨990830, by rfl⟩ : syracuseStep 1321107 = 1981661) B1981661
theorem B1321123 : Blo 1319478 1321123 := bstep (se 1 (by rfl) ⟨990842, by rfl⟩ : syracuseStep 1321123 = 1981685) B1981685
theorem B3344561 : Blo 1319478 3344561 := bstep (se 2 (by rfl) ⟨1254210, by rfl⟩ : syracuseStep 3344561 = 2508421) B2508421
theorem B1321139 : Blo 1319478 1321139 := bstep (se 1 (by rfl) ⟨990854, by rfl⟩ : syracuseStep 1321139 = 1981709) B1981709
theorem B15050933 : Blo 1319478 15050933 := bstep (se 5 (by rfl) ⟨705512, by rfl⟩ : syracuseStep 15050933 = 1411025) B1411025
theorem B1484995 : Blo 1319478 1484995 := bstep (se 1 (by rfl) ⟨1113746, by rfl⟩ : syracuseStep 1484995 = 2227493) B2227493
theorem B1321155 : Blo 1319478 1321155 := bstep (se 1 (by rfl) ⟨990866, by rfl⟩ : syracuseStep 1321155 = 1981733) B1981733
theorem B1321171 : Blo 1319478 1321171 := bstep (se 1 (by rfl) ⟨990878, by rfl⟩ : syracuseStep 1321171 = 1981757) B1981757
theorem B1321187 : Blo 1319478 1321187 := bstep (se 1 (by rfl) ⟨990890, by rfl⟩ : syracuseStep 1321187 = 1981781) B1981781
theorem B3344611 : Blo 1319478 3344611 := bstep (se 1 (by rfl) ⟨2508458, by rfl⟩ : syracuseStep 3344611 = 5016917) B5016917
theorem B9029873 : Blo 1319478 9029873 := bstep (se 2 (by rfl) ⟨3386202, by rfl⟩ : syracuseStep 9029873 = 6772405) B6772405
theorem B1321203 : Blo 1319478 1321203 := bstep (se 1 (by rfl) ⟨990902, by rfl⟩ : syracuseStep 1321203 = 1981805) B1981805
theorem B1321219 : Blo 1319478 1321219 := bstep (se 1 (by rfl) ⟨990914, by rfl⟩ : syracuseStep 1321219 = 1981829) B1981829
theorem B1321235 : Blo 1319478 1321235 := bstep (se 1 (by rfl) ⟨990926, by rfl⟩ : syracuseStep 1321235 = 1981853) B1981853
theorem B1321251 : Blo 1319478 1321251 := bstep (se 1 (by rfl) ⟨990938, by rfl⟩ : syracuseStep 1321251 = 1981877) B1981877
theorem B1321267 : Blo 1319478 1321267 := bstep (se 1 (by rfl) ⟨990950, by rfl⟩ : syracuseStep 1321267 = 1981901) B1981901
theorem B1321283 : Blo 1319478 1321283 := bstep (se 1 (by rfl) ⟨990962, by rfl⟩ : syracuseStep 1321283 = 1981925) B1981925
theorem B4458833 : Blo 1319478 4458833 := bstep (se 2 (by rfl) ⟨1672062, by rfl⟩ : syracuseStep 4458833 = 3344125) B3344125
theorem B1485139 : Blo 1319478 1485139 := bstep (se 1 (by rfl) ⟨1113854, by rfl⟩ : syracuseStep 1485139 = 2227709) B2227709
theorem B1321299 : Blo 1319478 1321299 := bstep (se 1 (by rfl) ⟨990974, by rfl⟩ : syracuseStep 1321299 = 1981949) B1981949
theorem B1321315 : Blo 1319478 1321315 := bstep (se 1 (by rfl) ⟨990986, by rfl⟩ : syracuseStep 1321315 = 1981973) B1981973
theorem B3344753 : Blo 1319478 3344753 := bstep (se 2 (by rfl) ⟨1254282, by rfl⟩ : syracuseStep 3344753 = 2508565) B2508565
theorem B1321331 : Blo 1319478 1321331 := bstep (se 1 (by rfl) ⟨990998, by rfl⟩ : syracuseStep 1321331 = 1981997) B1981997
theorem B1321347 : Blo 1319478 1321347 := bstep (se 1 (by rfl) ⟨991010, by rfl⟩ : syracuseStep 1321347 = 1982021) B1982021
theorem B1321363 : Blo 1319478 1321363 := bstep (se 1 (by rfl) ⟨991022, by rfl⟩ : syracuseStep 1321363 = 1982045) B1982045
theorem B1321379 : Blo 1319478 1321379 := bstep (se 1 (by rfl) ⟨991034, by rfl⟩ : syracuseStep 1321379 = 1982069) B1982069
theorem B1321395 : Blo 1319478 1321395 := bstep (se 1 (by rfl) ⟨991046, by rfl⟩ : syracuseStep 1321395 = 1982093) B1982093
theorem B1321411 : Blo 1319478 1321411 := bstep (se 1 (by rfl) ⟨991058, by rfl⟩ : syracuseStep 1321411 = 1982117) B1982117
theorem B1321427 : Blo 1319478 1321427 := bstep (se 1 (by rfl) ⟨991070, by rfl⟩ : syracuseStep 1321427 = 1982141) B1982141
theorem B1485283 : Blo 1319478 1485283 := bstep (se 1 (by rfl) ⟨1113962, by rfl⟩ : syracuseStep 1485283 = 2227925) B2227925
theorem B1321443 : Blo 1319478 1321443 := bstep (se 1 (by rfl) ⟨991082, by rfl⟩ : syracuseStep 1321443 = 1982165) B1982165
theorem B4229617 : Blo 1319478 4229617 := bstep (se 2 (by rfl) ⟨1586106, by rfl⟩ : syracuseStep 4229617 = 3172213) B3172213
theorem B1321459 : Blo 1319478 1321459 := bstep (se 1 (by rfl) ⟨991094, by rfl⟩ : syracuseStep 1321459 = 1982189) B1982189
theorem B1321475 : Blo 1319478 1321475 := bstep (se 1 (by rfl) ⟨991106, by rfl⟩ : syracuseStep 1321475 = 1982213) B1982213
theorem B10029581 : Blo 1319478 10029581 := bstep (se 3 (by rfl) ⟨1880546, by rfl⟩ : syracuseStep 10029581 = 3761093) B3761093
theorem B5016113 : Blo 1319478 5016113 := bstep (se 2 (by rfl) ⟨1881042, by rfl⟩ : syracuseStep 5016113 = 3762085) B3762085
theorem B7522915 : Blo 1319478 7522915 := bstep (se 1 (by rfl) ⟨5642186, by rfl⟩ : syracuseStep 7522915 = 11284373) B11284373
theorem B1485427 : Blo 1319478 1485427 := bstep (se 1 (by rfl) ⟨1114070, by rfl⟩ : syracuseStep 1485427 = 2228141) B2228141
theorem B4229795 : Blo 1319478 4229795 := bstep (se 1 (by rfl) ⟨3172346, by rfl⟩ : syracuseStep 4229795 = 6344693) B6344693
theorem B7621361 : Blo 1319478 7621361 := bstep (se 2 (by rfl) ⟨2858010, by rfl⟩ : syracuseStep 7621361 = 5716021) B5716021
theorem B1485571 : Blo 1319478 1485571 := bstep (se 1 (by rfl) ⟨1114178, by rfl⟩ : syracuseStep 1485571 = 2228357) B2228357
theorem B2820881 : Blo 1319478 2820881 := bstep (se 2 (by rfl) ⟨1057830, by rfl⟩ : syracuseStep 2820881 = 2115661) B2115661
theorem B4459373 : Blo 1319478 4459373 := bstep (se 3 (by rfl) ⟨836132, by rfl⟩ : syracuseStep 4459373 = 1672265) B1672265
theorem B1485715 : Blo 1319478 1485715 := bstep (se 1 (by rfl) ⟨1114286, by rfl⟩ : syracuseStep 1485715 = 2228573) B2228573
theorem B4459427 : Blo 1319478 4459427 := bstep (se 1 (by rfl) ⟨3344570, by rfl⟩ : syracuseStep 4459427 = 6689141) B6689141
theorem B2411459 : Blo 1319478 2411459 := bstep (se 1 (by rfl) ⟨1808594, by rfl⟩ : syracuseStep 2411459 = 3617189) B3617189
theorem B1879043 : Blo 1319478 1879043 := bstep (se 1 (by rfl) ⟨1409282, by rfl⟩ : syracuseStep 1879043 = 2818565) B2818565
theorem B1608707 : Blo 1319478 1608707 := bstep (se 1 (by rfl) ⟨1206530, by rfl⟩ : syracuseStep 1608707 = 2413061) B2413061
theorem B1485859 : Blo 1319478 1485859 := bstep (se 1 (by rfl) ⟨1114394, by rfl⟩ : syracuseStep 1485859 = 2228789) B2228789
theorem B2116705 : Blo 1319478 2116705 := bstep (se 2 (by rfl) ⟨793764, by rfl⟩ : syracuseStep 2116705 = 1587529) B1587529
theorem B7523441 : Blo 1319478 7523441 := bstep (se 2 (by rfl) ⟨2821290, by rfl⟩ : syracuseStep 7523441 = 5642581) B5642581
theorem B3173539 : Blo 1319478 3173539 := bstep (se 1 (by rfl) ⟨2380154, by rfl⟩ : syracuseStep 3173539 = 4760309) B4760309
theorem B4459697 : Blo 1319478 4459697 := bstep (se 2 (by rfl) ⟨1672386, by rfl⟩ : syracuseStep 4459697 = 3344773) B3344773
theorem B1486003 : Blo 1319478 1486003 := bstep (se 1 (by rfl) ⟨1114502, by rfl⟩ : syracuseStep 1486003 = 2229005) B2229005
theorem B16051441 : Blo 1319478 16051441 := bstep (se 2 (by rfl) ⟨6019290, by rfl⟩ : syracuseStep 16051441 = 12038581) B12038581
theorem B3050801 : Blo 1319478 3050801 := bstep (se 2 (by rfl) ⟨1144050, by rfl⟩ : syracuseStep 3050801 = 2288101) B2288101
theorem B1486147 : Blo 1319478 1486147 := bstep (se 1 (by rfl) ⟨1114610, by rfl⟩ : syracuseStep 1486147 = 2229221) B2229221
theorem B8465741 : Blo 1319478 8465741 := bstep (se 3 (by rfl) ⟨1587326, by rfl⟩ : syracuseStep 8465741 = 3174653) B3174653
theorem B6679907 : Blo 1319478 6679907 := bstep (se 1 (by rfl) ⟨5009930, by rfl⟩ : syracuseStep 6679907 = 10019861) B10019861
theorem B6344077 : Blo 1319478 6344077 := bstep (se 3 (by rfl) ⟨1189514, by rfl⟩ : syracuseStep 6344077 = 2379029) B2379029
theorem B2969009 : Blo 1319478 2969009 := bstep (se 2 (by rfl) ⟨1113378, by rfl⟩ : syracuseStep 2969009 = 2226757) B2226757
theorem B2969027 : Blo 1319478 2969027 := bstep (se 1 (by rfl) ⟨2226770, by rfl⟩ : syracuseStep 2969027 = 4453541) B4453541
theorem B2379217 : Blo 1319478 2379217 := bstep (se 2 (by rfl) ⟨892206, by rfl⟩ : syracuseStep 2379217 = 1784413) B1784413
theorem B1486291 : Blo 1319478 1486291 := bstep (se 1 (by rfl) ⟨1114718, by rfl⟩ : syracuseStep 1486291 = 2229437) B2229437
theorem B8457797 : Blo 1319478 8457797 := bstep (se 4 (by rfl) ⟨792918, by rfl⟩ : syracuseStep 8457797 = 1585837) B1585837
theorem B1486435 : Blo 1319478 1486435 := bstep (se 1 (by rfl) ⟨1114826, by rfl⟩ : syracuseStep 1486435 = 2229653) B2229653
theorem B1879681 : Blo 1319478 1879681 := bstep (se 2 (by rfl) ⟨704880, by rfl⟩ : syracuseStep 1879681 = 1409761) B1409761
theorem B2969297 : Blo 1319478 2969297 := bstep (se 2 (by rfl) ⟨1113486, by rfl⟩ : syracuseStep 2969297 = 2226973) B2226973
theorem B2969315 : Blo 1319478 2969315 := bstep (se 1 (by rfl) ⟨2226986, by rfl⟩ : syracuseStep 2969315 = 4453973) B4453973
theorem B1879795 : Blo 1319478 1879795 := bstep (se 1 (by rfl) ⟨1409846, by rfl⟩ : syracuseStep 1879795 = 2819693) B2819693
theorem B1486579 : Blo 1319478 1486579 := bstep (se 1 (by rfl) ⟨1114934, by rfl⟩ : syracuseStep 1486579 = 2229869) B2229869
theorem B2035459 : Blo 1319478 2035459 := bstep (se 1 (by rfl) ⟨1526594, by rfl⟩ : syracuseStep 2035459 = 3053189) B3053189
theorem B15249221 : Blo 1319478 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B2969585 : Blo 1319478 2969585 := bstep (se 2 (by rfl) ⟨1113594, by rfl⟩ : syracuseStep 2969585 = 2227189) B2227189
theorem B3174385 : Blo 1319478 3174385 := bstep (se 2 (by rfl) ⟨1190394, by rfl⟩ : syracuseStep 3174385 = 2380789) B2380789
theorem B2969603 : Blo 1319478 2969603 := bstep (se 1 (by rfl) ⟨2227202, by rfl⟩ : syracuseStep 2969603 = 4454405) B4454405
theorem B5640205 : Blo 1319478 5640205 := bstep (se 3 (by rfl) ⟨1057538, by rfl⟩ : syracuseStep 5640205 = 2115077) B2115077
theorem B1904675 : Blo 1319478 1904675 := bstep (se 1 (by rfl) ⟨1428506, by rfl⟩ : syracuseStep 1904675 = 2857013) B2857013
theorem B6688817 : Blo 1319478 6688817 := bstep (se 2 (by rfl) ⟨2508306, by rfl⟩ : syracuseStep 6688817 = 5016613) B5016613
theorem B3174499 : Blo 1319478 3174499 := bstep (se 1 (by rfl) ⟨2380874, by rfl⟩ : syracuseStep 3174499 = 4761749) B4761749
theorem B6680717 : Blo 1319478 6680717 := bstep (se 3 (by rfl) ⟨1252634, by rfl⟩ : syracuseStep 6680717 = 2505269) B2505269
theorem B5025997 : Blo 1319478 5025997 := bstep (se 3 (by rfl) ⟨942374, by rfl⟩ : syracuseStep 5025997 = 1884749) B1884749
theorem B2969873 : Blo 1319478 2969873 := bstep (se 2 (by rfl) ⟨1113702, by rfl⟩ : syracuseStep 2969873 = 2227405) B2227405
theorem B2969891 : Blo 1319478 2969891 := bstep (se 1 (by rfl) ⟨2227418, by rfl⟩ : syracuseStep 2969891 = 4454837) B4454837
theorem B22868365 : Blo 1319478 22868365 := bstep (se 3 (by rfl) ⟨4287818, by rfl⟩ : syracuseStep 22868365 = 8575637) B8575637
theorem B4231565 : Blo 1319478 4231565 := bstep (se 3 (by rfl) ⟨793418, by rfl⟩ : syracuseStep 4231565 = 1586837) B1586837
theorem B2380241 : Blo 1319478 2380241 := bstep (se 2 (by rfl) ⟨892590, by rfl⟩ : syracuseStep 2380241 = 1785181) B1785181
theorem B3011107 : Blo 1319478 3011107 := bstep (se 1 (by rfl) ⟨2258330, by rfl⟩ : syracuseStep 3011107 = 4516661) B4516661
theorem B7524899 : Blo 1319478 7524899 := bstep (se 1 (by rfl) ⟨5643674, by rfl⟩ : syracuseStep 7524899 = 11287349) B11287349
theorem B2970161 : Blo 1319478 2970161 := bstep (se 2 (by rfl) ⟨1113810, by rfl⟩ : syracuseStep 2970161 = 2227621) B2227621
theorem B2970179 : Blo 1319478 2970179 := bstep (se 1 (by rfl) ⟨2227634, by rfl⟩ : syracuseStep 2970179 = 4455269) B4455269
theorem B5010083 : Blo 1319478 5010083 := bstep (se 1 (by rfl) ⟨3757562, by rfl⟩ : syracuseStep 5010083 = 7515125) B7515125
theorem B2380529 : Blo 1319478 2380529 := bstep (se 2 (by rfl) ⟨892698, by rfl⟩ : syracuseStep 2380529 = 1785397) B1785397
theorem B10023749 : Blo 1319478 10023749 := bstep (se 4 (by rfl) ⟨939726, by rfl⟩ : syracuseStep 10023749 = 1879453) B1879453
theorem B2970449 : Blo 1319478 2970449 := bstep (se 2 (by rfl) ⟨1113918, by rfl⟩ : syracuseStep 2970449 = 2227837) B2227837
theorem B1979219 : Blo 1319478 1979219 := bstep (se 1 (by rfl) ⟨1484414, by rfl⟩ : syracuseStep 1979219 = 2968829) B2968829
theorem B2970467 : Blo 1319478 2970467 := bstep (se 1 (by rfl) ⟨2227850, by rfl⟩ : syracuseStep 2970467 = 4455701) B4455701
theorem B1979249 : Blo 1319478 1979249 := bstep (se 2 (by rfl) ⟨742218, by rfl⟩ : syracuseStep 1979249 = 1484437) B1484437
theorem B1979267 : Blo 1319478 1979267 := bstep (se 1 (by rfl) ⟨1484450, by rfl⟩ : syracuseStep 1979267 = 2968901) B2968901
theorem B77190029 : Blo 1319478 77190029 := bstep (se 3 (by rfl) ⟨14473130, by rfl⟩ : syracuseStep 77190029 = 28946261) B28946261
theorem B1979297 : Blo 1319478 1979297 := bstep (se 2 (by rfl) ⟨742236, by rfl⟩ : syracuseStep 1979297 = 1484473) B1484473
theorem B1979315 : Blo 1319478 1979315 := bstep (se 1 (by rfl) ⟨1484486, by rfl⟩ : syracuseStep 1979315 = 2968973) B2968973
theorem B4453325 : Blo 1319478 4453325 := bstep (se 3 (by rfl) ⟨834998, by rfl⟩ : syracuseStep 4453325 = 1669997) B1669997
theorem B1979345 : Blo 1319478 1979345 := bstep (se 2 (by rfl) ⟨742254, by rfl⟩ : syracuseStep 1979345 = 1484509) B1484509
theorem B1979363 : Blo 1319478 1979363 := bstep (se 1 (by rfl) ⟨1484522, by rfl⟩ : syracuseStep 1979363 = 2969045) B2969045
theorem B1979393 : Blo 1319478 1979393 := bstep (se 2 (by rfl) ⟨742272, by rfl⟩ : syracuseStep 1979393 = 1484545) B1484545
theorem B4453379 : Blo 1319478 4453379 := bstep (se 1 (by rfl) ⟨3340034, by rfl⟩ : syracuseStep 4453379 = 6680069) B6680069
theorem B1979411 : Blo 1319478 1979411 := bstep (se 1 (by rfl) ⟨1484558, by rfl⟩ : syracuseStep 1979411 = 2969117) B2969117
theorem B1979441 : Blo 1319478 1979441 := bstep (se 2 (by rfl) ⟨742290, by rfl⟩ : syracuseStep 1979441 = 1484581) B1484581
theorem B5641265 : Blo 1319478 5641265 := bstep (se 2 (by rfl) ⟨2115474, by rfl⟩ : syracuseStep 5641265 = 4230949) B4230949
theorem B1881139 : Blo 1319478 1881139 := bstep (se 1 (by rfl) ⟨1410854, by rfl⟩ : syracuseStep 1881139 = 2821709) B2821709
theorem B1979459 : Blo 1319478 1979459 := bstep (se 1 (by rfl) ⟨1484594, by rfl⟩ : syracuseStep 1979459 = 2969189) B2969189
theorem B1979489 : Blo 1319478 1979489 := bstep (se 2 (by rfl) ⟨742308, by rfl⟩ : syracuseStep 1979489 = 1484617) B1484617
theorem B2970737 : Blo 1319478 2970737 := bstep (se 2 (by rfl) ⟨1114026, by rfl⟩ : syracuseStep 2970737 = 2228053) B2228053
theorem B2290801 : Blo 1319478 2290801 := bstep (se 2 (by rfl) ⟨859050, by rfl⟩ : syracuseStep 2290801 = 1718101) B1718101
theorem B1979507 : Blo 1319478 1979507 := bstep (se 1 (by rfl) ⟨1484630, by rfl⟩ : syracuseStep 1979507 = 2969261) B2969261
theorem B2970755 : Blo 1319478 2970755 := bstep (se 1 (by rfl) ⟨2228066, by rfl⟩ : syracuseStep 2970755 = 4456133) B4456133
theorem B1979537 : Blo 1319478 1979537 := bstep (se 2 (by rfl) ⟨742326, by rfl⟩ : syracuseStep 1979537 = 1484653) B1484653
theorem B1979555 : Blo 1319478 1979555 := bstep (se 1 (by rfl) ⟨1484666, by rfl⟩ : syracuseStep 1979555 = 2969333) B2969333
theorem B8139953 : Blo 1319478 8139953 := bstep (se 2 (by rfl) ⟨3052482, by rfl⟩ : syracuseStep 8139953 = 6104965) B6104965
theorem B1979585 : Blo 1319478 1979585 := bstep (se 2 (by rfl) ⟨742344, by rfl⟩ : syracuseStep 1979585 = 1484689) B1484689
theorem B1979603 : Blo 1319478 1979603 := bstep (se 1 (by rfl) ⟨1484702, by rfl⟩ : syracuseStep 1979603 = 2969405) B2969405
theorem B11277539 : Blo 1319478 11277539 := bstep (se 1 (by rfl) ⟨8458154, by rfl⟩ : syracuseStep 11277539 = 16916309) B16916309
theorem B3388643 : Blo 1319478 3388643 := bstep (se 1 (by rfl) ⟨2541482, by rfl⟩ : syracuseStep 3388643 = 5082965) B5082965
theorem B1979633 : Blo 1319478 1979633 := bstep (se 2 (by rfl) ⟨742362, by rfl⟩ : syracuseStep 1979633 = 1484725) B1484725
theorem B1979651 : Blo 1319478 1979651 := bstep (se 1 (by rfl) ⟨1484738, by rfl⟩ : syracuseStep 1979651 = 2969477) B2969477
theorem B4453649 : Blo 1319478 4453649 := bstep (se 2 (by rfl) ⟨1670118, by rfl⟩ : syracuseStep 4453649 = 3340237) B3340237
theorem B1979681 : Blo 1319478 1979681 := bstep (se 2 (by rfl) ⟨742380, by rfl⟩ : syracuseStep 1979681 = 1484761) B1484761
theorem B1979699 : Blo 1319478 1979699 := bstep (se 1 (by rfl) ⟨1484774, by rfl⟩ : syracuseStep 1979699 = 2969549) B2969549
theorem B1979729 : Blo 1319478 1979729 := bstep (se 2 (by rfl) ⟨742398, by rfl⟩ : syracuseStep 1979729 = 1484797) B1484797
theorem B1586515 : Blo 1319478 1586515 := bstep (se 1 (by rfl) ⟨1189886, by rfl⟩ : syracuseStep 1586515 = 2379773) B2379773
theorem B1979747 : Blo 1319478 1979747 := bstep (se 1 (by rfl) ⟨1484810, by rfl⟩ : syracuseStep 1979747 = 2969621) B2969621
theorem B10032497 : Blo 1319478 10032497 := bstep (se 2 (by rfl) ⟨3762186, by rfl⟩ : syracuseStep 10032497 = 7524373) B7524373
theorem B1979777 : Blo 1319478 1979777 := bstep (se 2 (by rfl) ⟨742416, by rfl⟩ : syracuseStep 1979777 = 1484833) B1484833
theorem B2971025 : Blo 1319478 2971025 := bstep (se 2 (by rfl) ⟨1114134, by rfl⟩ : syracuseStep 2971025 = 2228269) B2228269
theorem B1979795 : Blo 1319478 1979795 := bstep (se 1 (by rfl) ⟨1484846, by rfl⟩ : syracuseStep 1979795 = 2969693) B2969693
theorem B2971043 : Blo 1319478 2971043 := bstep (se 1 (by rfl) ⟨2228282, by rfl⟩ : syracuseStep 2971043 = 4456565) B4456565
theorem B1979825 : Blo 1319478 1979825 := bstep (se 2 (by rfl) ⟨742434, by rfl⟩ : syracuseStep 1979825 = 1484869) B1484869
theorem B3216817 : Blo 1319478 3216817 := bstep (se 2 (by rfl) ⟨1206306, by rfl⟩ : syracuseStep 3216817 = 2412613) B2412613
theorem B1979843 : Blo 1319478 1979843 := bstep (se 1 (by rfl) ⟨1484882, by rfl⟩ : syracuseStep 1979843 = 2969765) B2969765
theorem B2381251 : Blo 1319478 2381251 := bstep (se 1 (by rfl) ⟨1785938, by rfl⟩ : syracuseStep 2381251 = 3571877) B3571877
theorem B1979873 : Blo 1319478 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B1979891 : Blo 1319478 1979891 := bstep (se 1 (by rfl) ⟨1484918, by rfl⟩ : syracuseStep 1979891 = 2969837) B2969837
theorem B3757585 : Blo 1319478 3757585 := bstep (se 2 (by rfl) ⟨1409094, by rfl⟩ : syracuseStep 3757585 = 2818189) B2818189
theorem B1979921 : Blo 1319478 1979921 := bstep (se 2 (by rfl) ⟨742470, by rfl⟩ : syracuseStep 1979921 = 1484941) B1484941
theorem B1979939 : Blo 1319478 1979939 := bstep (se 1 (by rfl) ⟨1484954, by rfl⟩ : syracuseStep 1979939 = 2969909) B2969909
theorem B1979969 : Blo 1319478 1979969 := bstep (se 2 (by rfl) ⟨742488, by rfl⟩ : syracuseStep 1979969 = 1484977) B1484977
theorem B1979987 : Blo 1319478 1979987 := bstep (se 1 (by rfl) ⟨1484990, by rfl⟩ : syracuseStep 1979987 = 2969981) B2969981
theorem B1980017 : Blo 1319478 1980017 := bstep (se 2 (by rfl) ⟨742506, by rfl⟩ : syracuseStep 1980017 = 1485013) B1485013
theorem B1980035 : Blo 1319478 1980035 := bstep (se 1 (by rfl) ⟨1485026, by rfl⟩ : syracuseStep 1980035 = 2970053) B2970053
theorem B5011085 : Blo 1319478 5011085 := bstep (se 3 (by rfl) ⟨939578, by rfl⟩ : syracuseStep 5011085 = 1879157) B1879157
theorem B1980065 : Blo 1319478 1980065 := bstep (se 2 (by rfl) ⟨742524, by rfl⟩ : syracuseStep 1980065 = 1485049) B1485049
theorem B3757745 : Blo 1319478 3757745 := bstep (se 2 (by rfl) ⟨1409154, by rfl⟩ : syracuseStep 3757745 = 2818309) B2818309
theorem B1980083 : Blo 1319478 1980083 := bstep (se 1 (by rfl) ⟨1485062, by rfl⟩ : syracuseStep 1980083 = 2970125) B2970125
theorem B2971313 : Blo 1319478 2971313 := bstep (se 2 (by rfl) ⟨1114242, by rfl⟩ : syracuseStep 2971313 = 2228485) B2228485
theorem B2971331 : Blo 1319478 2971331 := bstep (se 1 (by rfl) ⟨2228498, by rfl⟩ : syracuseStep 2971331 = 4456997) B4456997
theorem B1980113 : Blo 1319478 1980113 := bstep (se 2 (by rfl) ⟨742542, by rfl⟩ : syracuseStep 1980113 = 1485085) B1485085
theorem B1980131 : Blo 1319478 1980131 := bstep (se 1 (by rfl) ⟨1485098, by rfl⟩ : syracuseStep 1980131 = 2970197) B2970197
theorem B1980161 : Blo 1319478 1980161 := bstep (se 2 (by rfl) ⟨742560, by rfl⟩ : syracuseStep 1980161 = 1485121) B1485121
theorem B1980179 : Blo 1319478 1980179 := bstep (se 1 (by rfl) ⟨1485134, by rfl⟩ : syracuseStep 1980179 = 2970269) B2970269
theorem B3757859 : Blo 1319478 3757859 := bstep (se 1 (by rfl) ⟨2818394, by rfl⟩ : syracuseStep 3757859 = 5636789) B5636789
theorem B4454189 : Blo 1319478 4454189 := bstep (se 3 (by rfl) ⟨835160, by rfl⟩ : syracuseStep 4454189 = 1670321) B1670321
theorem B1980209 : Blo 1319478 1980209 := bstep (se 2 (by rfl) ⟨742578, by rfl⟩ : syracuseStep 1980209 = 1485157) B1485157
theorem B1980227 : Blo 1319478 1980227 := bstep (se 1 (by rfl) ⟨1485170, by rfl⟩ : syracuseStep 1980227 = 2970341) B2970341
theorem B1718083 : Blo 1319478 1718083 := bstep (se 1 (by rfl) ⟨1288562, by rfl⟩ : syracuseStep 1718083 = 2577125) B2577125
theorem B1980257 : Blo 1319478 1980257 := bstep (se 2 (by rfl) ⟨742596, by rfl⟩ : syracuseStep 1980257 = 1485193) B1485193
theorem B4454243 : Blo 1319478 4454243 := bstep (se 1 (by rfl) ⟨3340682, by rfl⟩ : syracuseStep 4454243 = 6681365) B6681365
theorem B1783667 : Blo 1319478 1783667 := bstep (se 1 (by rfl) ⟨1337750, by rfl⟩ : syracuseStep 1783667 = 2675501) B2675501
theorem B1980275 : Blo 1319478 1980275 := bstep (se 1 (by rfl) ⟨1485206, by rfl⟩ : syracuseStep 1980275 = 2970413) B2970413
theorem B1980305 : Blo 1319478 1980305 := bstep (se 2 (by rfl) ⟨742614, by rfl⟩ : syracuseStep 1980305 = 1485229) B1485229
theorem B1980323 : Blo 1319478 1980323 := bstep (se 1 (by rfl) ⟨1485242, by rfl⟩ : syracuseStep 1980323 = 2970485) B2970485
theorem B1980353 : Blo 1319478 1980353 := bstep (se 2 (by rfl) ⟨742632, by rfl⟩ : syracuseStep 1980353 = 1485265) B1485265
theorem B2971601 : Blo 1319478 2971601 := bstep (se 2 (by rfl) ⟨1114350, by rfl⟩ : syracuseStep 2971601 = 2228701) B2228701
theorem B1980371 : Blo 1319478 1980371 := bstep (se 1 (by rfl) ⟨1485278, by rfl⟩ : syracuseStep 1980371 = 2970557) B2970557
theorem B2971619 : Blo 1319478 2971619 := bstep (se 1 (by rfl) ⟨2228714, by rfl⟩ : syracuseStep 2971619 = 4457429) B4457429
theorem B1980401 : Blo 1319478 1980401 := bstep (se 2 (by rfl) ⟨742650, by rfl⟩ : syracuseStep 1980401 = 1485301) B1485301
theorem B1980419 : Blo 1319478 1980419 := bstep (se 1 (by rfl) ⟨1485314, by rfl⟩ : syracuseStep 1980419 = 2970629) B2970629
theorem B13760525 : Blo 1319478 13760525 := bstep (se 3 (by rfl) ⟨2580098, by rfl⟩ : syracuseStep 13760525 = 5160197) B5160197
theorem B1980449 : Blo 1319478 1980449 := bstep (se 2 (by rfl) ⟨742668, by rfl⟩ : syracuseStep 1980449 = 1485337) B1485337
theorem B3389489 : Blo 1319478 3389489 := bstep (se 2 (by rfl) ⟨1271058, by rfl⟩ : syracuseStep 3389489 = 2542117) B2542117
theorem B1980467 : Blo 1319478 1980467 := bstep (se 1 (by rfl) ⟨1485350, by rfl⟩ : syracuseStep 1980467 = 2970701) B2970701
theorem B1980497 : Blo 1319478 1980497 := bstep (se 2 (by rfl) ⟨742686, by rfl⟩ : syracuseStep 1980497 = 1485373) B1485373
theorem B1980515 : Blo 1319478 1980515 := bstep (se 1 (by rfl) ⟨1485386, by rfl⟩ : syracuseStep 1980515 = 2970773) B2970773
theorem B4454513 : Blo 1319478 4454513 := bstep (se 2 (by rfl) ⟨1670442, by rfl⟩ : syracuseStep 4454513 = 3340885) B3340885
theorem B1980545 : Blo 1319478 1980545 := bstep (se 2 (by rfl) ⟨742704, by rfl⟩ : syracuseStep 1980545 = 1485409) B1485409
theorem B2676881 : Blo 1319478 2676881 := bstep (se 2 (by rfl) ⟨1003830, by rfl⟩ : syracuseStep 2676881 = 2007661) B2007661
theorem B1980563 : Blo 1319478 1980563 := bstep (se 1 (by rfl) ⟨1485422, by rfl⟩ : syracuseStep 1980563 = 2970845) B2970845
theorem B1980593 : Blo 1319478 1980593 := bstep (se 2 (by rfl) ⟨742722, by rfl⟩ : syracuseStep 1980593 = 1485445) B1485445
theorem B1980611 : Blo 1319478 1980611 := bstep (se 1 (by rfl) ⟨1485458, by rfl⟩ : syracuseStep 1980611 = 2970917) B2970917
theorem B1980641 : Blo 1319478 1980641 := bstep (se 2 (by rfl) ⟨742740, by rfl⟩ : syracuseStep 1980641 = 1485481) B1485481
theorem B2971889 : Blo 1319478 2971889 := bstep (se 2 (by rfl) ⟨1114458, by rfl⟩ : syracuseStep 2971889 = 2228917) B2228917
theorem B1980659 : Blo 1319478 1980659 := bstep (se 1 (by rfl) ⟨1485494, by rfl⟩ : syracuseStep 1980659 = 2970989) B2970989
theorem B2971907 : Blo 1319478 2971907 := bstep (se 1 (by rfl) ⟨2228930, by rfl⟩ : syracuseStep 2971907 = 4457861) B4457861
theorem B3340561 : Blo 1319478 3340561 := bstep (se 2 (by rfl) ⟨1252710, by rfl⟩ : syracuseStep 3340561 = 2505421) B2505421
theorem B1980689 : Blo 1319478 1980689 := bstep (se 2 (by rfl) ⟨742758, by rfl⟩ : syracuseStep 1980689 = 1485517) B1485517
theorem B1784099 : Blo 1319478 1784099 := bstep (se 1 (by rfl) ⟨1338074, by rfl⟩ : syracuseStep 1784099 = 2676149) B2676149
theorem B1980707 : Blo 1319478 1980707 := bstep (se 1 (by rfl) ⟨1485530, by rfl⟩ : syracuseStep 1980707 = 2971061) B2971061
theorem B1980737 : Blo 1319478 1980737 := bstep (se 2 (by rfl) ⟨742776, by rfl⟩ : syracuseStep 1980737 = 1485553) B1485553
theorem B7518541 : Blo 1319478 7518541 := bstep (se 3 (by rfl) ⟨1409726, by rfl⟩ : syracuseStep 7518541 = 2819453) B2819453
theorem B1980755 : Blo 1319478 1980755 := bstep (se 1 (by rfl) ⟨1485566, by rfl⟩ : syracuseStep 1980755 = 2971133) B2971133
theorem B1980785 : Blo 1319478 1980785 := bstep (se 2 (by rfl) ⟨742794, by rfl⟩ : syracuseStep 1980785 = 1485589) B1485589
theorem B1980803 : Blo 1319478 1980803 := bstep (se 1 (by rfl) ⟨1485602, by rfl⟩ : syracuseStep 1980803 = 2971205) B2971205
theorem B1980833 : Blo 1319478 1980833 := bstep (se 2 (by rfl) ⟨742812, by rfl⟩ : syracuseStep 1980833 = 1485625) B1485625
theorem B1980851 : Blo 1319478 1980851 := bstep (se 1 (by rfl) ⟨1485638, by rfl⟩ : syracuseStep 1980851 = 2971277) B2971277
theorem B1980881 : Blo 1319478 1980881 := bstep (se 2 (by rfl) ⟨742830, by rfl⟩ : syracuseStep 1980881 = 1485661) B1485661
theorem B1980899 : Blo 1319478 1980899 := bstep (se 1 (by rfl) ⟨1485674, by rfl⟩ : syracuseStep 1980899 = 2971349) B2971349
theorem B1980929 : Blo 1319478 1980929 := bstep (se 2 (by rfl) ⟨742848, by rfl⟩ : syracuseStep 1980929 = 1485697) B1485697
theorem B2972177 : Blo 1319478 2972177 := bstep (se 2 (by rfl) ⟨1114566, by rfl⟩ : syracuseStep 2972177 = 2229133) B2229133
theorem B1980947 : Blo 1319478 1980947 := bstep (se 1 (by rfl) ⟨1485710, by rfl⟩ : syracuseStep 1980947 = 2971421) B2971421
theorem B3340835 : Blo 1319478 3340835 := bstep (se 1 (by rfl) ⟨2505626, by rfl⟩ : syracuseStep 3340835 = 5011253) B5011253
theorem B2972195 : Blo 1319478 2972195 := bstep (se 1 (by rfl) ⟨2229146, by rfl⟩ : syracuseStep 2972195 = 4458293) B4458293
theorem B2226737 : Blo 1319478 2226737 := bstep (se 2 (by rfl) ⟨835026, by rfl⟩ : syracuseStep 2226737 = 1670053) B1670053
theorem B1980977 : Blo 1319478 1980977 := bstep (se 2 (by rfl) ⟨742866, by rfl⟩ : syracuseStep 1980977 = 1485733) B1485733
theorem B1980995 : Blo 1319478 1980995 := bstep (se 1 (by rfl) ⟨1485746, by rfl⟩ : syracuseStep 1980995 = 2971493) B2971493
theorem B1981025 : Blo 1319478 1981025 := bstep (se 2 (by rfl) ⟨742884, by rfl⟩ : syracuseStep 1981025 = 1485769) B1485769
theorem B1505891 : Blo 1319478 1505891 := bstep (se 1 (by rfl) ⟨1129418, by rfl⟩ : syracuseStep 1505891 = 2258837) B2258837
theorem B1981043 : Blo 1319478 1981043 := bstep (se 1 (by rfl) ⟨1485782, by rfl⟩ : syracuseStep 1981043 = 2971565) B2971565
theorem B4455053 : Blo 1319478 4455053 := bstep (se 3 (by rfl) ⟨835322, by rfl⟩ : syracuseStep 4455053 = 1670645) B1670645
theorem B1981073 : Blo 1319478 1981073 := bstep (se 2 (by rfl) ⟨742902, by rfl⟩ : syracuseStep 1981073 = 1485805) B1485805
theorem B1981091 : Blo 1319478 1981091 := bstep (se 1 (by rfl) ⟨1485818, by rfl⟩ : syracuseStep 1981091 = 2971637) B2971637
theorem B2226865 : Blo 1319478 2226865 := bstep (se 2 (by rfl) ⟨835074, by rfl⟩ : syracuseStep 2226865 = 1670149) B1670149
theorem B1981121 : Blo 1319478 1981121 := bstep (se 2 (by rfl) ⟨742920, by rfl⟩ : syracuseStep 1981121 = 1485841) B1485841
theorem B4455107 : Blo 1319478 4455107 := bstep (se 1 (by rfl) ⟨3341330, by rfl⟩ : syracuseStep 4455107 = 6682661) B6682661
theorem B4012753 : Blo 1319478 4012753 := bstep (se 2 (by rfl) ⟨1504782, by rfl⟩ : syracuseStep 4012753 = 3009565) B3009565
theorem B2226899 : Blo 1319478 2226899 := bstep (se 1 (by rfl) ⟨1670174, by rfl⟩ : syracuseStep 2226899 = 3340349) B3340349
theorem B1981139 : Blo 1319478 1981139 := bstep (se 1 (by rfl) ⟨1485854, by rfl⟩ : syracuseStep 1981139 = 2971709) B2971709
theorem B3341027 : Blo 1319478 3341027 := bstep (se 1 (by rfl) ⟨2505770, by rfl⟩ : syracuseStep 3341027 = 5011541) B5011541
theorem B3865315 : Blo 1319478 3865315 := bstep (se 1 (by rfl) ⟨2898986, by rfl⟩ : syracuseStep 3865315 = 5797973) B5797973
theorem B1981169 : Blo 1319478 1981169 := bstep (se 2 (by rfl) ⟨742938, by rfl⟩ : syracuseStep 1981169 = 1485877) B1485877
theorem B2259713 : Blo 1319478 2259713 := bstep (se 2 (by rfl) ⟨847392, by rfl⟩ : syracuseStep 2259713 = 1694785) B1694785
theorem B1981187 : Blo 1319478 1981187 := bstep (se 1 (by rfl) ⟨1485890, by rfl⟩ : syracuseStep 1981187 = 2971781) B2971781
theorem B3758861 : Blo 1319478 3758861 := bstep (se 3 (by rfl) ⟨704786, by rfl⟩ : syracuseStep 3758861 = 1409573) B1409573
theorem B1981217 : Blo 1319478 1981217 := bstep (se 2 (by rfl) ⟨742956, by rfl⟩ : syracuseStep 1981217 = 1485913) B1485913
theorem B2972465 : Blo 1319478 2972465 := bstep (se 2 (by rfl) ⟨1114674, by rfl⟩ : syracuseStep 2972465 = 2229349) B2229349
theorem B1981235 : Blo 1319478 1981235 := bstep (se 1 (by rfl) ⟨1485926, by rfl⟩ : syracuseStep 1981235 = 2971853) B2971853
theorem B2972483 : Blo 1319478 2972483 := bstep (se 1 (by rfl) ⟨2229362, by rfl⟩ : syracuseStep 2972483 = 4458725) B4458725
theorem B5716813 : Blo 1319478 5716813 := bstep (se 3 (by rfl) ⟨1071902, by rfl⟩ : syracuseStep 5716813 = 2143805) B2143805
theorem B1981265 : Blo 1319478 1981265 := bstep (se 2 (by rfl) ⟨742974, by rfl⟩ : syracuseStep 1981265 = 1485949) B1485949
theorem B2227027 : Blo 1319478 2227027 := bstep (se 1 (by rfl) ⟨1670270, by rfl⟩ : syracuseStep 2227027 = 3340541) B3340541
theorem B1669987 : Blo 1319478 1669987 := bstep (se 1 (by rfl) ⟨1252490, by rfl⟩ : syracuseStep 1669987 = 2504981) B2504981
theorem B1981283 : Blo 1319478 1981283 := bstep (se 1 (by rfl) ⟨1485962, by rfl⟩ : syracuseStep 1981283 = 2971925) B2971925
theorem B1981313 : Blo 1319478 1981313 := bstep (se 2 (by rfl) ⟨742992, by rfl⟩ : syracuseStep 1981313 = 1485985) B1485985
theorem B1981331 : Blo 1319478 1981331 := bstep (se 1 (by rfl) ⟨1485998, by rfl⟩ : syracuseStep 1981331 = 2971997) B2971997
theorem B2505649 : Blo 1319478 2505649 := bstep (se 2 (by rfl) ⟨939618, by rfl⟩ : syracuseStep 2505649 = 1879237) B1879237
theorem B1981361 : Blo 1319478 1981361 := bstep (se 2 (by rfl) ⟨743010, by rfl⟩ : syracuseStep 1981361 = 1486021) B1486021
theorem B3759043 : Blo 1319478 3759043 := bstep (se 1 (by rfl) ⟨2819282, by rfl⟩ : syracuseStep 3759043 = 5638565) B5638565
theorem B1981379 : Blo 1319478 1981379 := bstep (se 1 (by rfl) ⟨1486034, by rfl⟩ : syracuseStep 1981379 = 2972069) B2972069
theorem B10705861 : Blo 1319478 10705861 := bstep (se 4 (by rfl) ⟨1003674, by rfl⟩ : syracuseStep 10705861 = 2007349) B2007349
theorem B4455377 : Blo 1319478 4455377 := bstep (se 2 (by rfl) ⟨1670766, by rfl⟩ : syracuseStep 4455377 = 3341533) B3341533
theorem B2227169 : Blo 1319478 2227169 := bstep (se 2 (by rfl) ⟨835188, by rfl⟩ : syracuseStep 2227169 = 1670377) B1670377
theorem B1981409 : Blo 1319478 1981409 := bstep (se 2 (by rfl) ⟨743028, by rfl⟩ : syracuseStep 1981409 = 1486057) B1486057
theorem B25394147 : Blo 1319478 25394147 := bstep (se 1 (by rfl) ⟨19045610, by rfl⟩ : syracuseStep 25394147 = 38091221) B38091221
theorem B6683633 : Blo 1319478 6683633 := bstep (se 2 (by rfl) ⟨2506362, by rfl⟩ : syracuseStep 6683633 = 5012725) B5012725
theorem B1981427 : Blo 1319478 1981427 := bstep (se 1 (by rfl) ⟨1486070, by rfl⟩ : syracuseStep 1981427 = 2972141) B2972141
theorem B1981457 : Blo 1319478 1981457 := bstep (se 2 (by rfl) ⟨743046, by rfl⟩ : syracuseStep 1981457 = 1486093) B1486093
theorem B1981475 : Blo 1319478 1981475 := bstep (se 1 (by rfl) ⟨1486106, by rfl⟩ : syracuseStep 1981475 = 2972213) B2972213
theorem B1506355 : Blo 1319478 1506355 := bstep (se 1 (by rfl) ⟨1129766, by rfl⟩ : syracuseStep 1506355 = 2259533) B2259533
theorem B1981505 : Blo 1319478 1981505 := bstep (se 2 (by rfl) ⟨743064, by rfl⟩ : syracuseStep 1981505 = 1486129) B1486129
theorem B2505809 : Blo 1319478 2505809 := bstep (se 2 (by rfl) ⟨939678, by rfl⟩ : syracuseStep 2505809 = 1879357) B1879357
theorem B2972753 : Blo 1319478 2972753 := bstep (se 2 (by rfl) ⟨1114782, by rfl⟩ : syracuseStep 2972753 = 2229565) B2229565
theorem B1981523 : Blo 1319478 1981523 := bstep (se 1 (by rfl) ⟨1486142, by rfl⟩ : syracuseStep 1981523 = 2972285) B2972285
theorem B2227297 : Blo 1319478 2227297 := bstep (se 2 (by rfl) ⟨835236, by rfl⟩ : syracuseStep 2227297 = 1670473) B1670473
theorem B2145377 : Blo 1319478 2145377 := bstep (se 2 (by rfl) ⟨804516, by rfl⟩ : syracuseStep 2145377 = 1609033) B1609033
theorem B3759203 : Blo 1319478 3759203 := bstep (se 1 (by rfl) ⟨2819402, by rfl⟩ : syracuseStep 3759203 = 5638805) B5638805
theorem B2972771 : Blo 1319478 2972771 := bstep (se 1 (by rfl) ⟨2229578, by rfl⟩ : syracuseStep 2972771 = 4459157) B4459157
theorem B1981553 : Blo 1319478 1981553 := bstep (se 2 (by rfl) ⟨743082, by rfl⟩ : syracuseStep 1981553 = 1486165) B1486165
theorem B2227331 : Blo 1319478 2227331 := bstep (se 1 (by rfl) ⟨1670498, by rfl⟩ : syracuseStep 2227331 = 3340997) B3340997
theorem B1981571 : Blo 1319478 1981571 := bstep (se 1 (by rfl) ⟨1486178, by rfl⟩ : syracuseStep 1981571 = 2972357) B2972357
theorem B1981601 : Blo 1319478 1981601 := bstep (se 2 (by rfl) ⟨743100, by rfl⟩ : syracuseStep 1981601 = 1486201) B1486201
theorem B1981619 : Blo 1319478 1981619 := bstep (se 1 (by rfl) ⟨1486214, by rfl⟩ : syracuseStep 1981619 = 2972429) B2972429
theorem B1981649 : Blo 1319478 1981649 := bstep (se 2 (by rfl) ⟨743118, by rfl⟩ : syracuseStep 1981649 = 1486237) B1486237
theorem B1981667 : Blo 1319478 1981667 := bstep (se 1 (by rfl) ⟨1486250, by rfl⟩ : syracuseStep 1981667 = 2972501) B2972501
theorem B1981697 : Blo 1319478 1981697 := bstep (se 2 (by rfl) ⟨743136, by rfl⟩ : syracuseStep 1981697 = 1486273) B1486273
theorem B2227459 : Blo 1319478 2227459 := bstep (se 1 (by rfl) ⟨1670594, by rfl⟩ : syracuseStep 2227459 = 3341189) B3341189
theorem B7617797 : Blo 1319478 7617797 := bstep (se 4 (by rfl) ⟨714168, by rfl⟩ : syracuseStep 7617797 = 1428337) B1428337
theorem B1981715 : Blo 1319478 1981715 := bstep (se 1 (by rfl) ⟨1486286, by rfl⟩ : syracuseStep 1981715 = 2972573) B2972573
theorem B2145571 : Blo 1319478 2145571 := bstep (se 1 (by rfl) ⟨1609178, by rfl⟩ : syracuseStep 2145571 = 3218357) B3218357
theorem B1785137 : Blo 1319478 1785137 := bstep (se 2 (by rfl) ⟨669426, by rfl⟩ : syracuseStep 1785137 = 1338853) B1338853
theorem B1981745 : Blo 1319478 1981745 := bstep (se 2 (by rfl) ⟨743154, by rfl⟩ : syracuseStep 1981745 = 1486309) B1486309
theorem B1981763 : Blo 1319478 1981763 := bstep (se 1 (by rfl) ⟨1486322, by rfl⟩ : syracuseStep 1981763 = 2972645) B2972645
theorem B14269765 : Blo 1319478 14269765 := bstep (se 4 (by rfl) ⟨1337790, by rfl⟩ : syracuseStep 14269765 = 2675581) B2675581
theorem B1670483 : Blo 1319478 1670483 := bstep (se 1 (by rfl) ⟨1252862, by rfl⟩ : syracuseStep 1670483 = 2505725) B2505725
theorem B1981793 : Blo 1319478 1981793 := bstep (se 2 (by rfl) ⟨743172, by rfl⟩ : syracuseStep 1981793 = 1486345) B1486345
theorem B2973041 : Blo 1319478 2973041 := bstep (se 2 (by rfl) ⟨1114890, by rfl⟩ : syracuseStep 2973041 = 2229781) B2229781
theorem B1981811 : Blo 1319478 1981811 := bstep (se 1 (by rfl) ⟨1486358, by rfl⟩ : syracuseStep 1981811 = 2972717) B2972717
theorem B3571075 : Blo 1319478 3571075 := bstep (se 1 (by rfl) ⟨2678306, by rfl⟩ : syracuseStep 3571075 = 5356613) B5356613
theorem B2973059 : Blo 1319478 2973059 := bstep (se 1 (by rfl) ⟨2229794, by rfl⟩ : syracuseStep 2973059 = 4459589) B4459589
theorem B2227601 : Blo 1319478 2227601 := bstep (se 2 (by rfl) ⟨835350, by rfl⟩ : syracuseStep 2227601 = 1670701) B1670701
theorem B1981841 : Blo 1319478 1981841 := bstep (se 2 (by rfl) ⟨743190, by rfl⟩ : syracuseStep 1981841 = 1486381) B1486381
theorem B1981859 : Blo 1319478 1981859 := bstep (se 1 (by rfl) ⟨1486394, by rfl⟩ : syracuseStep 1981859 = 2972789) B2972789
theorem B8461745 : Blo 1319478 8461745 := bstep (se 2 (by rfl) ⟨3173154, by rfl⟩ : syracuseStep 8461745 = 6346309) B6346309
theorem B1981889 : Blo 1319478 1981889 := bstep (se 2 (by rfl) ⟨743208, by rfl⟩ : syracuseStep 1981889 = 1486417) B1486417
theorem B1981907 : Blo 1319478 1981907 := bstep (se 1 (by rfl) ⟨1486430, by rfl⟩ : syracuseStep 1981907 = 2972861) B2972861
theorem B2506211 : Blo 1319478 2506211 := bstep (se 1 (by rfl) ⟨1879658, by rfl⟩ : syracuseStep 2506211 = 3759317) B3759317
theorem B4455917 : Blo 1319478 4455917 := bstep (se 3 (by rfl) ⟨835484, by rfl⟩ : syracuseStep 4455917 = 1670969) B1670969
theorem B1981937 : Blo 1319478 1981937 := bstep (se 2 (by rfl) ⟨743226, by rfl⟩ : syracuseStep 1981937 = 1486453) B1486453
theorem B1981955 : Blo 1319478 1981955 := bstep (se 1 (by rfl) ⟨1486466, by rfl⟩ : syracuseStep 1981955 = 2972933) B2972933
theorem B2227729 : Blo 1319478 2227729 := bstep (se 2 (by rfl) ⟨835398, by rfl⟩ : syracuseStep 2227729 = 1670797) B1670797
theorem B1981985 : Blo 1319478 1981985 := bstep (se 2 (by rfl) ⟨743244, by rfl⟩ : syracuseStep 1981985 = 1486489) B1486489
theorem B4455971 : Blo 1319478 4455971 := bstep (se 1 (by rfl) ⟨3341978, by rfl⟩ : syracuseStep 4455971 = 6683957) B6683957
theorem B3571249 : Blo 1319478 3571249 := bstep (se 2 (by rfl) ⟨1339218, by rfl⟩ : syracuseStep 3571249 = 2678437) B2678437
theorem B2227763 : Blo 1319478 2227763 := bstep (se 1 (by rfl) ⟨1670822, by rfl⟩ : syracuseStep 2227763 = 3341645) B3341645
theorem B1982003 : Blo 1319478 1982003 := bstep (se 1 (by rfl) ⟨1486502, by rfl⟩ : syracuseStep 1982003 = 2973005) B2973005
theorem B1982033 : Blo 1319478 1982033 := bstep (se 2 (by rfl) ⟨743262, by rfl⟩ : syracuseStep 1982033 = 1486525) B1486525
theorem B1982051 : Blo 1319478 1982051 := bstep (se 1 (by rfl) ⟨1486538, by rfl⟩ : syracuseStep 1982051 = 2973077) B2973077
theorem B1982081 : Blo 1319478 1982081 := bstep (se 2 (by rfl) ⟨743280, by rfl⟩ : syracuseStep 1982081 = 1486561) B1486561
theorem B3341969 : Blo 1319478 3341969 := bstep (se 2 (by rfl) ⟨1253238, by rfl⟩ : syracuseStep 3341969 = 2506477) B2506477
theorem B1982099 : Blo 1319478 1982099 := bstep (se 1 (by rfl) ⟨1486574, by rfl⟩ : syracuseStep 1982099 = 2973149) B2973149
theorem B1982129 : Blo 1319478 1982129 := bstep (se 2 (by rfl) ⟨743298, by rfl⟩ : syracuseStep 1982129 = 1486597) B1486597
theorem B2227891 : Blo 1319478 2227891 := bstep (se 1 (by rfl) ⟨1670918, by rfl⟩ : syracuseStep 2227891 = 3341837) B3341837
theorem B3342019 : Blo 1319478 3342019 := bstep (se 1 (by rfl) ⟨2506514, by rfl⟩ : syracuseStep 3342019 = 5013029) B5013029
theorem B1982147 : Blo 1319478 1982147 := bstep (se 1 (by rfl) ⟨1486610, by rfl⟩ : syracuseStep 1982147 = 2973221) B2973221
theorem B5013197 : Blo 1319478 5013197 := bstep (se 3 (by rfl) ⟨939974, by rfl⟩ : syracuseStep 5013197 = 1879949) B1879949
theorem B1982177 : Blo 1319478 1982177 := bstep (se 2 (by rfl) ⟨743316, by rfl⟩ : syracuseStep 1982177 = 1486633) B1486633
theorem B1982195 : Blo 1319478 1982195 := bstep (se 1 (by rfl) ⟨1486646, by rfl⟩ : syracuseStep 1982195 = 2973293) B2973293
theorem B4456241 : Blo 1319478 4456241 := bstep (se 2 (by rfl) ⟨1671090, by rfl⟩ : syracuseStep 4456241 = 3342181) B3342181
theorem B2228033 : Blo 1319478 2228033 := bstep (se 2 (by rfl) ⟨835512, by rfl⟩ : syracuseStep 2228033 = 1671025) B1671025
theorem B3342161 : Blo 1319478 3342161 := bstep (se 2 (by rfl) ⟨1253310, by rfl⟩ : syracuseStep 3342161 = 2506621) B2506621
theorem B7618445 : Blo 1319478 7618445 := bstep (se 3 (by rfl) ⟨1428458, by rfl⟩ : syracuseStep 7618445 = 2856917) B2856917
theorem B34283405 : Blo 1319478 34283405 := bstep (se 3 (by rfl) ⟨6428138, by rfl⟩ : syracuseStep 34283405 = 12856277) B12856277
theorem B2228161 : Blo 1319478 2228161 := bstep (se 2 (by rfl) ⟨835560, by rfl⟩ : syracuseStep 2228161 = 1671121) B1671121
theorem B1810369 : Blo 1319478 1810369 := bstep (se 2 (by rfl) ⟨678888, by rfl⟩ : syracuseStep 1810369 = 1357777) B1357777
theorem B5644237 : Blo 1319478 5644237 := bstep (se 3 (by rfl) ⟨1058294, by rfl⟩ : syracuseStep 5644237 = 2116589) B2116589
theorem B2228195 : Blo 1319478 2228195 := bstep (se 1 (by rfl) ⟨1671146, by rfl⟩ : syracuseStep 2228195 = 3342293) B3342293
theorem B7520273 : Blo 1319478 7520273 := bstep (se 2 (by rfl) ⟨2820102, by rfl⟩ : syracuseStep 7520273 = 5640205) B5640205
theorem B14278673 : Blo 1319478 14278673 := bstep (se 2 (by rfl) ⟨5354502, by rfl⟩ : syracuseStep 14278673 = 10709005) B10709005
theorem B2228249 : Blo 1319478 2228249 := bstep (se 2 (by rfl) ⟨835593, by rfl⟩ : syracuseStep 2228249 = 1671187) B1671187
theorem B2678873 : Blo 1319478 2678873 := bstep (se 2 (by rfl) ⟨1004577, by rfl⟩ : syracuseStep 2678873 = 2009155) B2009155
theorem B5079133 : Blo 1319478 5079133 := bstep (se 3 (by rfl) ⟨952337, by rfl⟩ : syracuseStep 5079133 = 1904675) B1904675
theorem B14286941 : Blo 1319478 14286941 := bstep (se 3 (by rfl) ⟨2678801, by rfl⟩ : syracuseStep 14286941 = 5357603) B5357603
theorem B2228377 : Blo 1319478 2228377 := bstep (se 2 (by rfl) ⟨835641, by rfl⟩ : syracuseStep 2228377 = 1671283) B1671283
theorem B5013683 : Blo 1319478 5013683 := bstep (se 1 (by rfl) ⟨3760262, by rfl⟩ : syracuseStep 5013683 = 7520525) B7520525
theorem B5013697 : Blo 1319478 5013697 := bstep (se 2 (by rfl) ⟨1880136, by rfl⟩ : syracuseStep 5013697 = 3760273) B3760273
theorem B6701329 : Blo 1319478 6701329 := bstep (se 2 (by rfl) ⟨2512998, by rfl⟩ : syracuseStep 6701329 = 5025997) B5025997
theorem B4456727 : Blo 1319478 4456727 := bstep (se 1 (by rfl) ⟨3342545, by rfl⟩ : syracuseStep 4456727 = 6685091) B6685091
theorem B2113867 : Blo 1319478 2113867 := bstep (se 1 (by rfl) ⟨1585400, by rfl⟩ : syracuseStep 2113867 = 3170801) B3170801
theorem B3342667 : Blo 1319478 3342667 := bstep (se 1 (by rfl) ⟨2507000, by rfl⟩ : syracuseStep 3342667 = 5014001) B5014001
theorem B1671511 : Blo 1319478 1671511 := bstep (se 1 (by rfl) ⟨1253633, by rfl⟩ : syracuseStep 1671511 = 2507267) B2507267
theorem B1409419 : Blo 1319478 1409419 := bstep (se 1 (by rfl) ⟨1057064, by rfl⟩ : syracuseStep 1409419 = 2114129) B2114129
theorem B3342809 : Blo 1319478 3342809 := bstep (se 2 (by rfl) ⟨1253553, by rfl⟩ : syracuseStep 3342809 = 2507107) B2507107
theorem B30491153 : Blo 1319478 30491153 := bstep (se 2 (by rfl) ⟨11434182, by rfl⟩ : syracuseStep 30491153 = 22868365) B22868365
theorem B1319479 : Blo 1319478 1319479 := bstep (se 1 (by rfl) ⟨989609, by rfl⟩ : syracuseStep 1319479 = 1979219) B1979219
theorem B1319499 : Blo 1319478 1319499 := bstep (se 1 (by rfl) ⟨989624, by rfl⟩ : syracuseStep 1319499 = 1979249) B1979249
theorem B1319511 : Blo 1319478 1319511 := bstep (se 1 (by rfl) ⟨989633, by rfl⟩ : syracuseStep 1319511 = 1979267) B1979267
theorem B1319531 : Blo 1319478 1319531 := bstep (se 1 (by rfl) ⟨989648, by rfl⟩ : syracuseStep 1319531 = 1979297) B1979297
theorem B1319543 : Blo 1319478 1319543 := bstep (se 1 (by rfl) ⟨989657, by rfl⟩ : syracuseStep 1319543 = 1979315) B1979315
theorem B1319563 : Blo 1319478 1319563 := bstep (se 1 (by rfl) ⟨989672, by rfl⟩ : syracuseStep 1319563 = 1979345) B1979345
theorem B1319575 : Blo 1319478 1319575 := bstep (se 1 (by rfl) ⟨989681, by rfl⟩ : syracuseStep 1319575 = 1979363) B1979363
theorem B1319595 : Blo 1319478 1319595 := bstep (se 1 (by rfl) ⟨989696, by rfl⟩ : syracuseStep 1319595 = 1979393) B1979393
theorem B1319607 : Blo 1319478 1319607 := bstep (se 1 (by rfl) ⟨989705, by rfl⟩ : syracuseStep 1319607 = 1979411) B1979411
theorem B1319627 : Blo 1319478 1319627 := bstep (se 1 (by rfl) ⟨989720, by rfl⟩ : syracuseStep 1319627 = 1979441) B1979441
theorem B3760843 : Blo 1319478 3760843 := bstep (se 1 (by rfl) ⟨2820632, by rfl⟩ : syracuseStep 3760843 = 5641265) B5641265
theorem B1319639 : Blo 1319478 1319639 := bstep (se 1 (by rfl) ⟨989729, by rfl⟩ : syracuseStep 1319639 = 1979459) B1979459
theorem B4014809 : Blo 1319478 4014809 := bstep (se 2 (by rfl) ⟨1505553, by rfl⟩ : syracuseStep 4014809 = 3011107) B3011107
theorem B2228951 : Blo 1319478 2228951 := bstep (se 1 (by rfl) ⟨1671713, by rfl⟩ : syracuseStep 2228951 = 3343427) B3343427
theorem B1319659 : Blo 1319478 1319659 := bstep (se 1 (by rfl) ⟨989744, by rfl⟩ : syracuseStep 1319659 = 1979489) B1979489
theorem B1319671 : Blo 1319478 1319671 := bstep (se 1 (by rfl) ⟨989753, by rfl⟩ : syracuseStep 1319671 = 1979507) B1979507
theorem B1319691 : Blo 1319478 1319691 := bstep (se 1 (by rfl) ⟨989768, by rfl⟩ : syracuseStep 1319691 = 1979537) B1979537
theorem B1319703 : Blo 1319478 1319703 := bstep (se 1 (by rfl) ⟨989777, by rfl⟩ : syracuseStep 1319703 = 1979555) B1979555
theorem B1319723 : Blo 1319478 1319723 := bstep (se 1 (by rfl) ⟨989792, by rfl⟩ : syracuseStep 1319723 = 1979585) B1979585
theorem B4760365 : Blo 1319478 4760365 := bstep (se 3 (by rfl) ⟨892568, by rfl⟩ : syracuseStep 4760365 = 1785137) B1785137
theorem B4457267 : Blo 1319478 4457267 := bstep (se 1 (by rfl) ⟨3342950, by rfl⟩ : syracuseStep 4457267 = 6685901) B6685901
theorem B1319735 : Blo 1319478 1319735 := bstep (se 1 (by rfl) ⟨989801, by rfl⟩ : syracuseStep 1319735 = 1979603) B1979603
theorem B1319755 : Blo 1319478 1319755 := bstep (se 1 (by rfl) ⟨989816, by rfl⟩ : syracuseStep 1319755 = 1979633) B1979633
theorem B1319767 : Blo 1319478 1319767 := bstep (se 1 (by rfl) ⟨989825, by rfl⟩ : syracuseStep 1319767 = 1979651) B1979651
theorem B2229079 : Blo 1319478 2229079 := bstep (se 1 (by rfl) ⟨1671809, by rfl⟩ : syracuseStep 2229079 = 3343619) B3343619
theorem B1319787 : Blo 1319478 1319787 := bstep (se 1 (by rfl) ⟨989840, by rfl⟩ : syracuseStep 1319787 = 1979681) B1979681
theorem B1319799 : Blo 1319478 1319799 := bstep (se 1 (by rfl) ⟨989849, by rfl⟩ : syracuseStep 1319799 = 1979699) B1979699
theorem B1319819 : Blo 1319478 1319819 := bstep (se 1 (by rfl) ⟨989864, by rfl⟩ : syracuseStep 1319819 = 1979729) B1979729
theorem B1319831 : Blo 1319478 1319831 := bstep (se 1 (by rfl) ⟨989873, by rfl⟩ : syracuseStep 1319831 = 1979747) B1979747
theorem B1319851 : Blo 1319478 1319851 := bstep (se 1 (by rfl) ⟨989888, by rfl⟩ : syracuseStep 1319851 = 1979777) B1979777
theorem B2507699 : Blo 1319478 2507699 := bstep (se 1 (by rfl) ⟨1880774, by rfl⟩ : syracuseStep 2507699 = 3761549) B3761549
theorem B1319863 : Blo 1319478 1319863 := bstep (se 1 (by rfl) ⟨989897, by rfl⟩ : syracuseStep 1319863 = 1979795) B1979795
theorem B5350337 : Blo 1319478 5350337 := bstep (se 2 (by rfl) ⟨2006376, by rfl⟩ : syracuseStep 5350337 = 4012753) B4012753
theorem B2819009 : Blo 1319478 2819009 := bstep (se 2 (by rfl) ⟨1057128, by rfl⟩ : syracuseStep 2819009 = 2114257) B2114257
theorem B2540491 : Blo 1319478 2540491 := bstep (se 1 (by rfl) ⟨1905368, by rfl⟩ : syracuseStep 2540491 = 3810737) B3810737
theorem B1319883 : Blo 1319478 1319883 := bstep (se 1 (by rfl) ⟨989912, by rfl⟩ : syracuseStep 1319883 = 1979825) B1979825
theorem B11273165 : Blo 1319478 11273165 := bstep (se 3 (by rfl) ⟨2113718, by rfl⟩ : syracuseStep 11273165 = 4227437) B4227437
theorem B1319895 : Blo 1319478 1319895 := bstep (se 1 (by rfl) ⟨989921, by rfl⟩ : syracuseStep 1319895 = 1979843) B1979843
theorem B5153753 : Blo 1319478 5153753 := bstep (se 2 (by rfl) ⟨1932657, by rfl⟩ : syracuseStep 5153753 = 3865315) B3865315
theorem B3761117 : Blo 1319478 3761117 := bstep (se 3 (by rfl) ⟨705209, by rfl⟩ : syracuseStep 3761117 = 1410419) B1410419
theorem B1319915 : Blo 1319478 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B1319927 : Blo 1319478 1319927 := bstep (se 1 (by rfl) ⟨989945, by rfl⟩ : syracuseStep 1319927 = 1979891) B1979891
theorem B1319947 : Blo 1319478 1319947 := bstep (se 1 (by rfl) ⟨989960, by rfl⟩ : syracuseStep 1319947 = 1979921) B1979921
theorem B1319959 : Blo 1319478 1319959 := bstep (se 1 (by rfl) ⟨989969, by rfl⟩ : syracuseStep 1319959 = 1979939) B1979939
theorem B1319979 : Blo 1319478 1319979 := bstep (se 1 (by rfl) ⟨989984, by rfl⟩ : syracuseStep 1319979 = 1979969) B1979969
theorem B1319991 : Blo 1319478 1319991 := bstep (se 1 (by rfl) ⟨989993, by rfl⟩ : syracuseStep 1319991 = 1979987) B1979987
theorem B4457537 : Blo 1319478 4457537 := bstep (se 2 (by rfl) ⟨1671576, by rfl⟩ : syracuseStep 4457537 = 3343153) B3343153
theorem B1320011 : Blo 1319478 1320011 := bstep (se 1 (by rfl) ⟨990008, by rfl⟩ : syracuseStep 1320011 = 1980017) B1980017
theorem B2507851 : Blo 1319478 2507851 := bstep (se 1 (by rfl) ⟨1880888, by rfl⟩ : syracuseStep 2507851 = 3761777) B3761777
theorem B1320023 : Blo 1319478 1320023 := bstep (se 1 (by rfl) ⟨990017, by rfl⟩ : syracuseStep 1320023 = 1980035) B1980035
theorem B15033437 : Blo 1319478 15033437 := bstep (se 3 (by rfl) ⟨2818769, by rfl⟩ : syracuseStep 15033437 = 5637539) B5637539
theorem B1320043 : Blo 1319478 1320043 := bstep (se 1 (by rfl) ⟨990032, by rfl⟩ : syracuseStep 1320043 = 1980065) B1980065
theorem B1320055 : Blo 1319478 1320055 := bstep (se 1 (by rfl) ⟨990041, by rfl⟩ : syracuseStep 1320055 = 1980083) B1980083
theorem B1410167 : Blo 1319478 1410167 := bstep (se 1 (by rfl) ⟨1057625, by rfl⟩ : syracuseStep 1410167 = 2115251) B2115251
theorem B1320075 : Blo 1319478 1320075 := bstep (se 1 (by rfl) ⟨990056, by rfl⟩ : syracuseStep 1320075 = 1980113) B1980113
theorem B1320087 : Blo 1319478 1320087 := bstep (se 1 (by rfl) ⟨990065, by rfl⟩ : syracuseStep 1320087 = 1980131) B1980131
theorem B1320107 : Blo 1319478 1320107 := bstep (se 1 (by rfl) ⟨990080, by rfl⟩ : syracuseStep 1320107 = 1980161) B1980161
theorem B1320119 : Blo 1319478 1320119 := bstep (se 1 (by rfl) ⟨990089, by rfl⟩ : syracuseStep 1320119 = 1980179) B1980179
theorem B1320139 : Blo 1319478 1320139 := bstep (se 1 (by rfl) ⟨990104, by rfl⟩ : syracuseStep 1320139 = 1980209) B1980209
theorem B1320151 : Blo 1319478 1320151 := bstep (se 1 (by rfl) ⟨990113, by rfl⟩ : syracuseStep 1320151 = 1980227) B1980227
theorem B1320171 : Blo 1319478 1320171 := bstep (se 1 (by rfl) ⟨990128, by rfl⟩ : syracuseStep 1320171 = 1980257) B1980257
theorem B1320183 : Blo 1319478 1320183 := bstep (se 1 (by rfl) ⟨990137, by rfl⟩ : syracuseStep 1320183 = 1980275) B1980275
theorem B1320203 : Blo 1319478 1320203 := bstep (se 1 (by rfl) ⟨990152, by rfl⟩ : syracuseStep 1320203 = 1980305) B1980305
theorem B1320215 : Blo 1319478 1320215 := bstep (se 1 (by rfl) ⟨990161, by rfl⟩ : syracuseStep 1320215 = 1980323) B1980323
theorem B3343639 : Blo 1319478 3343639 := bstep (se 1 (by rfl) ⟨2507729, by rfl⟩ : syracuseStep 3343639 = 5015459) B5015459
theorem B1320235 : Blo 1319478 1320235 := bstep (se 1 (by rfl) ⟨990176, by rfl⟩ : syracuseStep 1320235 = 1980353) B1980353
theorem B1320247 : Blo 1319478 1320247 := bstep (se 1 (by rfl) ⟨990185, by rfl⟩ : syracuseStep 1320247 = 1980371) B1980371
theorem B1320267 : Blo 1319478 1320267 := bstep (se 1 (by rfl) ⟨990200, by rfl⟩ : syracuseStep 1320267 = 1980401) B1980401
theorem B1320279 : Blo 1319478 1320279 := bstep (se 1 (by rfl) ⟨990209, by rfl⟩ : syracuseStep 1320279 = 1980419) B1980419
theorem B10855781 : Blo 1319478 10855781 := bstep (se 4 (by rfl) ⟨1017729, by rfl⟩ : syracuseStep 10855781 = 2035459) B2035459
theorem B1320299 : Blo 1319478 1320299 := bstep (se 1 (by rfl) ⟨990224, by rfl⟩ : syracuseStep 1320299 = 1980449) B1980449
theorem B1320311 : Blo 1319478 1320311 := bstep (se 1 (by rfl) ⟨990233, by rfl⟩ : syracuseStep 1320311 = 1980467) B1980467
theorem B1320331 : Blo 1319478 1320331 := bstep (se 1 (by rfl) ⟨990248, by rfl⟩ : syracuseStep 1320331 = 1980497) B1980497
theorem B1320343 : Blo 1319478 1320343 := bstep (se 1 (by rfl) ⟨990257, by rfl⟩ : syracuseStep 1320343 = 1980515) B1980515
theorem B2508185 : Blo 1319478 2508185 := bstep (se 2 (by rfl) ⟨940569, by rfl⟩ : syracuseStep 2508185 = 1881139) B1881139
theorem B1320363 : Blo 1319478 1320363 := bstep (se 1 (by rfl) ⟨990272, by rfl⟩ : syracuseStep 1320363 = 1980545) B1980545
theorem B1320375 : Blo 1319478 1320375 := bstep (se 1 (by rfl) ⟨990281, by rfl⟩ : syracuseStep 1320375 = 1980563) B1980563
theorem B1320395 : Blo 1319478 1320395 := bstep (se 1 (by rfl) ⟨990296, by rfl⟩ : syracuseStep 1320395 = 1980593) B1980593
theorem B2229707 : Blo 1319478 2229707 := bstep (se 1 (by rfl) ⟨1672280, by rfl⟩ : syracuseStep 2229707 = 3344561) B3344561
theorem B1320407 : Blo 1319478 1320407 := bstep (se 1 (by rfl) ⟨990305, by rfl⟩ : syracuseStep 1320407 = 1980611) B1980611
theorem B1320427 : Blo 1319478 1320427 := bstep (se 1 (by rfl) ⟨990320, by rfl⟩ : syracuseStep 1320427 = 1980641) B1980641
theorem B1320439 : Blo 1319478 1320439 := bstep (se 1 (by rfl) ⟨990329, by rfl⟩ : syracuseStep 1320439 = 1980659) B1980659
theorem B1320459 : Blo 1319478 1320459 := bstep (se 1 (by rfl) ⟨990344, by rfl⟩ : syracuseStep 1320459 = 1980689) B1980689
theorem B6686225 : Blo 1319478 6686225 := bstep (se 2 (by rfl) ⟨2507334, by rfl⟩ : syracuseStep 6686225 = 5014669) B5014669
theorem B1320471 : Blo 1319478 1320471 := bstep (se 1 (by rfl) ⟨990353, by rfl⟩ : syracuseStep 1320471 = 1980707) B1980707
theorem B1320491 : Blo 1319478 1320491 := bstep (se 1 (by rfl) ⟨990368, by rfl⟩ : syracuseStep 1320491 = 1980737) B1980737
theorem B1320503 : Blo 1319478 1320503 := bstep (se 1 (by rfl) ⟨990377, by rfl⟩ : syracuseStep 1320503 = 1980755) B1980755
theorem B10028609 : Blo 1319478 10028609 := bstep (se 2 (by rfl) ⟨3760728, by rfl⟩ : syracuseStep 10028609 = 7521457) B7521457
theorem B1320523 : Blo 1319478 1320523 := bstep (se 1 (by rfl) ⟨990392, by rfl⟩ : syracuseStep 1320523 = 1980785) B1980785
theorem B2229835 : Blo 1319478 2229835 := bstep (se 1 (by rfl) ⟨1672376, by rfl⟩ : syracuseStep 2229835 = 3344753) B3344753
theorem B1320535 : Blo 1319478 1320535 := bstep (se 1 (by rfl) ⟨990401, by rfl⟩ : syracuseStep 1320535 = 1980803) B1980803
theorem B4015709 : Blo 1319478 4015709 := bstep (se 3 (by rfl) ⟨752945, by rfl⟩ : syracuseStep 4015709 = 1505891) B1505891
theorem B4458077 : Blo 1319478 4458077 := bstep (se 3 (by rfl) ⟨835889, by rfl⟩ : syracuseStep 4458077 = 1671779) B1671779
theorem B1320555 : Blo 1319478 1320555 := bstep (se 1 (by rfl) ⟨990416, by rfl⟩ : syracuseStep 1320555 = 1980833) B1980833
theorem B1320567 : Blo 1319478 1320567 := bstep (se 1 (by rfl) ⟨990425, by rfl⟩ : syracuseStep 1320567 = 1980851) B1980851
theorem B1320587 : Blo 1319478 1320587 := bstep (se 1 (by rfl) ⟨990440, by rfl⟩ : syracuseStep 1320587 = 1980881) B1980881
theorem B1320599 : Blo 1319478 1320599 := bstep (se 1 (by rfl) ⟨990449, by rfl⟩ : syracuseStep 1320599 = 1980899) B1980899
theorem B1320619 : Blo 1319478 1320619 := bstep (se 1 (by rfl) ⟨990464, by rfl⟩ : syracuseStep 1320619 = 1980929) B1980929
theorem B6686387 : Blo 1319478 6686387 := bstep (se 1 (by rfl) ⟨5014790, by rfl⟩ : syracuseStep 6686387 = 10029581) B10029581
theorem B1320631 : Blo 1319478 1320631 := bstep (se 1 (by rfl) ⟨990473, by rfl⟩ : syracuseStep 1320631 = 1980947) B1980947
theorem B1484491 : Blo 1319478 1484491 := bstep (se 1 (by rfl) ⟨1113368, by rfl⟩ : syracuseStep 1484491 = 2226737) B2226737
theorem B1320651 : Blo 1319478 1320651 := bstep (se 1 (by rfl) ⟨990488, by rfl⟩ : syracuseStep 1320651 = 1980977) B1980977
theorem B3344075 : Blo 1319478 3344075 := bstep (se 1 (by rfl) ⟨2508056, by rfl⟩ : syracuseStep 3344075 = 5016113) B5016113
theorem B1320663 : Blo 1319478 1320663 := bstep (se 1 (by rfl) ⟨990497, by rfl⟩ : syracuseStep 1320663 = 1980995) B1980995
theorem B2229977 : Blo 1319478 2229977 := bstep (se 2 (by rfl) ⟨836241, by rfl⟩ : syracuseStep 2229977 = 1672483) B1672483
theorem B1320683 : Blo 1319478 1320683 := bstep (se 1 (by rfl) ⟨990512, by rfl⟩ : syracuseStep 1320683 = 1981025) B1981025
theorem B1320695 : Blo 1319478 1320695 := bstep (se 1 (by rfl) ⟨990521, by rfl⟩ : syracuseStep 1320695 = 1981043) B1981043
theorem B1320715 : Blo 1319478 1320715 := bstep (se 1 (by rfl) ⟨990536, by rfl⟩ : syracuseStep 1320715 = 1981073) B1981073
theorem B2819863 : Blo 1319478 2819863 := bstep (se 1 (by rfl) ⟨2114897, by rfl⟩ : syracuseStep 2819863 = 4229795) B4229795
theorem B1320727 : Blo 1319478 1320727 := bstep (se 1 (by rfl) ⟨990545, by rfl⟩ : syracuseStep 1320727 = 1981091) B1981091
theorem B2115353 : Blo 1319478 2115353 := bstep (se 2 (by rfl) ⟨793257, by rfl⟩ : syracuseStep 2115353 = 1586515) B1586515
theorem B1320747 : Blo 1319478 1320747 := bstep (se 1 (by rfl) ⟨990560, by rfl⟩ : syracuseStep 1320747 = 1981121) B1981121
theorem B1484599 : Blo 1319478 1484599 := bstep (se 1 (by rfl) ⟨1113449, by rfl⟩ : syracuseStep 1484599 = 2226899) B2226899
theorem B1320759 : Blo 1319478 1320759 := bstep (se 1 (by rfl) ⟨990569, by rfl⟩ : syracuseStep 1320759 = 1981139) B1981139
theorem B5080907 : Blo 1319478 5080907 := bstep (se 1 (by rfl) ⟨3810680, by rfl⟩ : syracuseStep 5080907 = 7621361) B7621361
theorem B1320779 : Blo 1319478 1320779 := bstep (se 1 (by rfl) ⟨990584, by rfl⟩ : syracuseStep 1320779 = 1981169) B1981169
theorem B1320791 : Blo 1319478 1320791 := bstep (se 1 (by rfl) ⟨990593, by rfl⟩ : syracuseStep 1320791 = 1981187) B1981187
theorem B4761433 : Blo 1319478 4761433 := bstep (se 2 (by rfl) ⟨1785537, by rfl⟩ : syracuseStep 4761433 = 3571075) B3571075
theorem B1320811 : Blo 1319478 1320811 := bstep (se 1 (by rfl) ⟨990608, by rfl⟩ : syracuseStep 1320811 = 1981217) B1981217
theorem B1320823 : Blo 1319478 1320823 := bstep (se 1 (by rfl) ⟨990617, by rfl⟩ : syracuseStep 1320823 = 1981235) B1981235
theorem B1320843 : Blo 1319478 1320843 := bstep (se 1 (by rfl) ⟨990632, by rfl⟩ : syracuseStep 1320843 = 1981265) B1981265
theorem B1320855 : Blo 1319478 1320855 := bstep (se 1 (by rfl) ⟨990641, by rfl⟩ : syracuseStep 1320855 = 1981283) B1981283
theorem B1320875 : Blo 1319478 1320875 := bstep (se 1 (by rfl) ⟨990656, by rfl⟩ : syracuseStep 1320875 = 1981313) B1981313
theorem B1320887 : Blo 1319478 1320887 := bstep (se 1 (by rfl) ⟨990665, by rfl⟩ : syracuseStep 1320887 = 1981331) B1981331
theorem B3172289 : Blo 1319478 3172289 := bstep (se 2 (by rfl) ⟨1189608, by rfl⟩ : syracuseStep 3172289 = 2379217) B2379217
theorem B1320907 : Blo 1319478 1320907 := bstep (se 1 (by rfl) ⟨990680, by rfl⟩ : syracuseStep 1320907 = 1981361) B1981361
theorem B1607639 : Blo 1319478 1607639 := bstep (se 1 (by rfl) ⟨1205729, by rfl⟩ : syracuseStep 1607639 = 2411459) B2411459
theorem B1320919 : Blo 1319478 1320919 := bstep (se 1 (by rfl) ⟨990689, by rfl⟩ : syracuseStep 1320919 = 1981379) B1981379
theorem B1484779 : Blo 1319478 1484779 := bstep (se 1 (by rfl) ⟨1113584, by rfl⟩ : syracuseStep 1484779 = 2227169) B2227169
theorem B1320939 : Blo 1319478 1320939 := bstep (se 1 (by rfl) ⟨990704, by rfl⟩ : syracuseStep 1320939 = 1981409) B1981409
theorem B1320951 : Blo 1319478 1320951 := bstep (se 1 (by rfl) ⟨990713, by rfl⟩ : syracuseStep 1320951 = 1981427) B1981427
theorem B1320971 : Blo 1319478 1320971 := bstep (se 1 (by rfl) ⟨990728, by rfl⟩ : syracuseStep 1320971 = 1981457) B1981457
theorem B1320983 : Blo 1319478 1320983 := bstep (se 1 (by rfl) ⟨990737, by rfl⟩ : syracuseStep 1320983 = 1981475) B1981475
theorem B1321003 : Blo 1319478 1321003 := bstep (se 1 (by rfl) ⟨990752, by rfl⟩ : syracuseStep 1321003 = 1981505) B1981505
theorem B1321015 : Blo 1319478 1321015 := bstep (se 1 (by rfl) ⟨990761, by rfl⟩ : syracuseStep 1321015 = 1981523) B1981523
theorem B4761665 : Blo 1319478 4761665 := bstep (se 2 (by rfl) ⟨1785624, by rfl⟩ : syracuseStep 4761665 = 3571249) B3571249
theorem B3344449 : Blo 1319478 3344449 := bstep (se 2 (by rfl) ⟨1254168, by rfl⟩ : syracuseStep 3344449 = 2508337) B2508337
theorem B5015627 : Blo 1319478 5015627 := bstep (se 1 (by rfl) ⟨3761720, by rfl⟩ : syracuseStep 5015627 = 7523441) B7523441
theorem B1321035 : Blo 1319478 1321035 := bstep (se 1 (by rfl) ⟨990776, by rfl⟩ : syracuseStep 1321035 = 1981553) B1981553
theorem B1484887 : Blo 1319478 1484887 := bstep (se 1 (by rfl) ⟨1113665, by rfl⟩ : syracuseStep 1484887 = 2227331) B2227331
theorem B1321047 : Blo 1319478 1321047 := bstep (se 1 (by rfl) ⟨990785, by rfl⟩ : syracuseStep 1321047 = 1981571) B1981571
theorem B5015641 : Blo 1319478 5015641 := bstep (se 2 (by rfl) ⟨1880865, by rfl⟩ : syracuseStep 5015641 = 3761731) B3761731
theorem B1321067 : Blo 1319478 1321067 := bstep (se 1 (by rfl) ⟨990800, by rfl⟩ : syracuseStep 1321067 = 1981601) B1981601
theorem B1321079 : Blo 1319478 1321079 := bstep (se 1 (by rfl) ⟨990809, by rfl⟩ : syracuseStep 1321079 = 1981619) B1981619
theorem B1321099 : Blo 1319478 1321099 := bstep (se 1 (by rfl) ⟨990824, by rfl⟩ : syracuseStep 1321099 = 1981649) B1981649
theorem B1321111 : Blo 1319478 1321111 := bstep (se 1 (by rfl) ⟨990833, by rfl⟩ : syracuseStep 1321111 = 1981667) B1981667
theorem B1321131 : Blo 1319478 1321131 := bstep (se 1 (by rfl) ⟨990848, by rfl⟩ : syracuseStep 1321131 = 1981697) B1981697
theorem B1321143 : Blo 1319478 1321143 := bstep (se 1 (by rfl) ⟨990857, by rfl⟩ : syracuseStep 1321143 = 1981715) B1981715
theorem B2033867 : Blo 1319478 2033867 := bstep (se 1 (by rfl) ⟨1525400, by rfl⟩ : syracuseStep 2033867 = 3050801) B3050801
theorem B1321163 : Blo 1319478 1321163 := bstep (se 1 (by rfl) ⟨990872, by rfl⟩ : syracuseStep 1321163 = 1981745) B1981745
theorem B1321175 : Blo 1319478 1321175 := bstep (se 1 (by rfl) ⟨990881, by rfl⟩ : syracuseStep 1321175 = 1981763) B1981763
theorem B1321195 : Blo 1319478 1321195 := bstep (se 1 (by rfl) ⟨990896, by rfl⟩ : syracuseStep 1321195 = 1981793) B1981793
theorem B1321207 : Blo 1319478 1321207 := bstep (se 1 (by rfl) ⟨990905, by rfl⟩ : syracuseStep 1321207 = 1981811) B1981811
theorem B21416197 : Blo 1319478 21416197 := bstep (se 4 (by rfl) ⟨2007768, by rfl⟩ : syracuseStep 21416197 = 4015537) B4015537
theorem B17156357 : Blo 1319478 17156357 := bstep (se 4 (by rfl) ⟨1608408, by rfl⟩ : syracuseStep 17156357 = 3216817) B3216817
theorem B1485067 : Blo 1319478 1485067 := bstep (se 1 (by rfl) ⟨1113800, by rfl⟩ : syracuseStep 1485067 = 2227601) B2227601
theorem B1321227 : Blo 1319478 1321227 := bstep (se 1 (by rfl) ⟨990920, by rfl⟩ : syracuseStep 1321227 = 1981841) B1981841
theorem B1321239 : Blo 1319478 1321239 := bstep (se 1 (by rfl) ⟨990929, by rfl⟩ : syracuseStep 1321239 = 1981859) B1981859
theorem B1321259 : Blo 1319478 1321259 := bstep (se 1 (by rfl) ⟨990944, by rfl⟩ : syracuseStep 1321259 = 1981889) B1981889
theorem B1321271 : Blo 1319478 1321271 := bstep (se 1 (by rfl) ⟨990953, by rfl⟩ : syracuseStep 1321271 = 1981907) B1981907
theorem B1321291 : Blo 1319478 1321291 := bstep (se 1 (by rfl) ⟨990968, by rfl⟩ : syracuseStep 1321291 = 1981937) B1981937
theorem B1321303 : Blo 1319478 1321303 := bstep (se 1 (by rfl) ⟨990977, by rfl⟩ : syracuseStep 1321303 = 1981955) B1981955
theorem B1321323 : Blo 1319478 1321323 := bstep (se 1 (by rfl) ⟨990992, by rfl⟩ : syracuseStep 1321323 = 1981985) B1981985
theorem B1485175 : Blo 1319478 1485175 := bstep (se 1 (by rfl) ⟨1113881, by rfl⟩ : syracuseStep 1485175 = 2227763) B2227763
theorem B1321335 : Blo 1319478 1321335 := bstep (se 1 (by rfl) ⟨991001, by rfl⟩ : syracuseStep 1321335 = 1982003) B1982003
theorem B5638531 : Blo 1319478 5638531 := bstep (se 1 (by rfl) ⟨4228898, by rfl⟩ : syracuseStep 5638531 = 8457797) B8457797
theorem B1321355 : Blo 1319478 1321355 := bstep (se 1 (by rfl) ⟨991016, by rfl⟩ : syracuseStep 1321355 = 1982033) B1982033
theorem B1321367 : Blo 1319478 1321367 := bstep (se 1 (by rfl) ⟨991025, by rfl⟩ : syracuseStep 1321367 = 1982051) B1982051
theorem B1321387 : Blo 1319478 1321387 := bstep (se 1 (by rfl) ⟨991040, by rfl⟩ : syracuseStep 1321387 = 1982081) B1982081
theorem B1321399 : Blo 1319478 1321399 := bstep (se 1 (by rfl) ⟨991049, by rfl⟩ : syracuseStep 1321399 = 1982099) B1982099
theorem B1321419 : Blo 1319478 1321419 := bstep (se 1 (by rfl) ⟨991064, by rfl⟩ : syracuseStep 1321419 = 1982129) B1982129
theorem B1321431 : Blo 1319478 1321431 := bstep (se 1 (by rfl) ⟨991073, by rfl⟩ : syracuseStep 1321431 = 1982147) B1982147
theorem B1321451 : Blo 1319478 1321451 := bstep (se 1 (by rfl) ⟨991088, by rfl⟩ : syracuseStep 1321451 = 1982177) B1982177
theorem B1321463 : Blo 1319478 1321463 := bstep (se 1 (by rfl) ⟨991097, by rfl⟩ : syracuseStep 1321463 = 1982195) B1982195
theorem B1485355 : Blo 1319478 1485355 := bstep (se 1 (by rfl) ⟨1114016, by rfl⟩ : syracuseStep 1485355 = 2228033) B2228033
theorem B1485463 : Blo 1319478 1485463 := bstep (se 1 (by rfl) ⟨1114097, by rfl⟩ : syracuseStep 1485463 = 2228195) B2228195
theorem B4459211 : Blo 1319478 4459211 := bstep (se 1 (by rfl) ⟨3344408, by rfl⟩ : syracuseStep 4459211 = 6688817) B6688817
theorem B9644761 : Blo 1319478 9644761 := bstep (se 2 (by rfl) ⟨3616785, by rfl⟩ : syracuseStep 9644761 = 7233571) B7233571
theorem B1485643 : Blo 1319478 1485643 := bstep (se 1 (by rfl) ⟨1114232, by rfl⟩ : syracuseStep 1485643 = 2228465) B2228465
theorem B5721005 : Blo 1319478 5721005 := bstep (se 3 (by rfl) ⟨1072688, by rfl⟩ : syracuseStep 5721005 = 2145377) B2145377
theorem B2821043 : Blo 1319478 2821043 := bstep (se 1 (by rfl) ⟨2115782, by rfl⟩ : syracuseStep 2821043 = 4231565) B4231565
theorem B1485751 : Blo 1319478 1485751 := bstep (se 1 (by rfl) ⟨1114313, by rfl⟩ : syracuseStep 1485751 = 2228627) B2228627
theorem B4459481 : Blo 1319478 4459481 := bstep (se 2 (by rfl) ⟨1672305, by rfl⟩ : syracuseStep 4459481 = 3344611) B3344611
theorem B5016599 : Blo 1319478 5016599 := bstep (se 1 (by rfl) ⟨3762449, by rfl⟩ : syracuseStep 5016599 = 7524899) B7524899
theorem B1879129 : Blo 1319478 1879129 := bstep (se 2 (by rfl) ⟨704673, by rfl⟩ : syracuseStep 1879129 = 1409347) B1409347
theorem B1485931 : Blo 1319478 1485931 := bstep (se 1 (by rfl) ⟨1114448, by rfl⟩ : syracuseStep 1485931 = 2228897) B2228897
theorem B1486039 : Blo 1319478 1486039 := bstep (se 1 (by rfl) ⟨1114529, by rfl⟩ : syracuseStep 1486039 = 2229059) B2229059
theorem B5221597 : Blo 1319478 5221597 := bstep (se 3 (by rfl) ⟨979049, by rfl⟩ : syracuseStep 5221597 = 1958099) B1958099
theorem B2968883 : Blo 1319478 2968883 := bstep (se 1 (by rfl) ⟨2226662, by rfl⟩ : syracuseStep 2968883 = 4453325) B4453325
theorem B5639489 : Blo 1319478 5639489 := bstep (se 2 (by rfl) ⟨2114808, by rfl⟩ : syracuseStep 5639489 = 4229617) B4229617
theorem B2968919 : Blo 1319478 2968919 := bstep (se 1 (by rfl) ⟨2226689, by rfl⟩ : syracuseStep 2968919 = 4453379) B4453379
theorem B8465795 : Blo 1319478 8465795 := bstep (se 1 (by rfl) ⟨6349346, by rfl⟩ : syracuseStep 8465795 = 12698693) B12698693
theorem B1486219 : Blo 1319478 1486219 := bstep (se 1 (by rfl) ⟨1114664, by rfl⟩ : syracuseStep 1486219 = 2229329) B2229329
theorem B5426635 : Blo 1319478 5426635 := bstep (se 1 (by rfl) ⟨4069976, by rfl⟩ : syracuseStep 5426635 = 8139953) B8139953
theorem B10030553 : Blo 1319478 10030553 := bstep (se 2 (by rfl) ⟨3761457, by rfl⟩ : syracuseStep 10030553 = 7522915) B7522915
theorem B1486327 : Blo 1319478 1486327 := bstep (se 1 (by rfl) ⟨1114745, by rfl⟩ : syracuseStep 1486327 = 2229491) B2229491
theorem B2969099 : Blo 1319478 2969099 := bstep (se 1 (by rfl) ⟨2226824, by rfl⟩ : syracuseStep 2969099 = 4453649) B4453649
theorem B2969153 : Blo 1319478 2969153 := bstep (se 2 (by rfl) ⟨1113432, by rfl⟩ : syracuseStep 2969153 = 2226865) B2226865
theorem B6688331 : Blo 1319478 6688331 := bstep (se 1 (by rfl) ⟨5016248, by rfl⟩ : syracuseStep 6688331 = 10032497) B10032497
theorem B8572517 : Blo 1319478 8572517 := bstep (se 4 (by rfl) ⟨803673, by rfl⟩ : syracuseStep 8572517 = 1607347) B1607347
theorem B21425795 : Blo 1319478 21425795 := bstep (se 1 (by rfl) ⟨16069346, by rfl⟩ : syracuseStep 21425795 = 32138693) B32138693
theorem B1486507 : Blo 1319478 1486507 := bstep (se 1 (by rfl) ⟨1114880, by rfl⟩ : syracuseStep 1486507 = 2229761) B2229761
theorem B7622417 : Blo 1319478 7622417 := bstep (se 2 (by rfl) ⟨2858406, by rfl⟩ : syracuseStep 7622417 = 5716813) B5716813
theorem B1486615 : Blo 1319478 1486615 := bstep (se 1 (by rfl) ⟨1114961, by rfl⟩ : syracuseStep 1486615 = 2229923) B2229923
theorem B2969369 : Blo 1319478 2969369 := bstep (se 2 (by rfl) ⟨1113513, by rfl⟩ : syracuseStep 2969369 = 2227027) B2227027
theorem B2969459 : Blo 1319478 2969459 := bstep (se 1 (by rfl) ⟨2227094, by rfl⟩ : syracuseStep 2969459 = 4454189) B4454189
theorem B2969495 : Blo 1319478 2969495 := bstep (se 1 (by rfl) ⟨2227121, by rfl⟩ : syracuseStep 2969495 = 4454243) B4454243
theorem B14274481 : Blo 1319478 14274481 := bstep (se 2 (by rfl) ⟨5352930, by rfl⟩ : syracuseStep 14274481 = 10705861) B10705861
theorem B1880023 : Blo 1319478 1880023 := bstep (se 1 (by rfl) ⟨1410017, by rfl⟩ : syracuseStep 1880023 = 2820035) B2820035
theorem B2969675 : Blo 1319478 2969675 := bstep (se 1 (by rfl) ⟨2227256, by rfl⟩ : syracuseStep 2969675 = 4454513) B4454513
theorem B2969729 : Blo 1319478 2969729 := bstep (se 2 (by rfl) ⟨1113648, by rfl⟩ : syracuseStep 2969729 = 2227297) B2227297
theorem B2822273 : Blo 1319478 2822273 := bstep (se 2 (by rfl) ⟨1058352, by rfl⟩ : syracuseStep 2822273 = 2116705) B2116705
theorem B4231385 : Blo 1319478 4231385 := bstep (se 2 (by rfl) ⟨1586769, by rfl⟩ : syracuseStep 4231385 = 3173539) B3173539
theorem B21401921 : Blo 1319478 21401921 := bstep (se 2 (by rfl) ⟨8025720, by rfl⟩ : syracuseStep 21401921 = 16051441) B16051441
theorem B2969945 : Blo 1319478 2969945 := bstep (se 2 (by rfl) ⟨1113729, by rfl⟩ : syracuseStep 2969945 = 2227459) B2227459
theorem B9163109 : Blo 1319478 9163109 := bstep (se 4 (by rfl) ⟨859041, by rfl⟩ : syracuseStep 9163109 = 1718083) B1718083
theorem B19026353 : Blo 1319478 19026353 := bstep (se 2 (by rfl) ⟨7134882, by rfl⟩ : syracuseStep 19026353 = 14269765) B14269765
theorem B2970035 : Blo 1319478 2970035 := bstep (se 1 (by rfl) ⟨2227526, by rfl⟩ : syracuseStep 2970035 = 4455053) B4455053
theorem B2970071 : Blo 1319478 2970071 := bstep (se 1 (by rfl) ⟨2227553, by rfl⟩ : syracuseStep 2970071 = 4455107) B4455107
theorem B1880587 : Blo 1319478 1880587 := bstep (se 1 (by rfl) ⟨1410440, by rfl⟩ : syracuseStep 1880587 = 2820881) B2820881
theorem B8458769 : Blo 1319478 8458769 := bstep (se 2 (by rfl) ⟨3172038, by rfl⟩ : syracuseStep 8458769 = 6344077) B6344077
theorem B3175001 : Blo 1319478 3175001 := bstep (se 2 (by rfl) ⟨1190625, by rfl⟩ : syracuseStep 3175001 = 2381251) B2381251
theorem B2970251 : Blo 1319478 2970251 := bstep (se 1 (by rfl) ⟨2227688, by rfl⟩ : syracuseStep 2970251 = 4455377) B4455377
theorem B16929431 : Blo 1319478 16929431 := bstep (se 1 (by rfl) ⟨12697073, by rfl⟩ : syracuseStep 16929431 = 25394147) B25394147
theorem B5010113 : Blo 1319478 5010113 := bstep (se 2 (by rfl) ⟨1878792, by rfl⟩ : syracuseStep 5010113 = 3757585) B3757585
theorem B2970305 : Blo 1319478 2970305 := bstep (se 2 (by rfl) ⟨1113864, by rfl⟩ : syracuseStep 2970305 = 2227729) B2227729
theorem B1979225 : Blo 1319478 1979225 := bstep (se 2 (by rfl) ⟨742209, by rfl⟩ : syracuseStep 1979225 = 1484419) B1484419
theorem B4453271 : Blo 1319478 4453271 := bstep (se 1 (by rfl) ⟨3339953, by rfl⟩ : syracuseStep 4453271 = 6679907) B6679907
theorem B2970521 : Blo 1319478 2970521 := bstep (se 2 (by rfl) ⟨1113945, by rfl⟩ : syracuseStep 2970521 = 2227891) B2227891
theorem B1979339 : Blo 1319478 1979339 := bstep (se 1 (by rfl) ⟨1484504, by rfl⟩ : syracuseStep 1979339 = 2969009) B2969009
theorem B5641163 : Blo 1319478 5641163 := bstep (se 1 (by rfl) ⟨4230872, by rfl⟩ : syracuseStep 5641163 = 8461745) B8461745
theorem B1979351 : Blo 1319478 1979351 := bstep (se 1 (by rfl) ⟨1484513, by rfl⟩ : syracuseStep 1979351 = 2969027) B2969027
theorem B4756445 : Blo 1319478 4756445 := bstep (se 3 (by rfl) ⟨891833, by rfl⟩ : syracuseStep 4756445 = 1783667) B1783667
theorem B2970611 : Blo 1319478 2970611 := bstep (se 1 (by rfl) ⟨2227958, by rfl⟩ : syracuseStep 2970611 = 4455917) B4455917
theorem B9655301 : Blo 1319478 9655301 := bstep (se 4 (by rfl) ⟨905184, by rfl⟩ : syracuseStep 9655301 = 1810369) B1810369
theorem B2970647 : Blo 1319478 2970647 := bstep (se 1 (by rfl) ⟨2227985, by rfl⟩ : syracuseStep 2970647 = 4455971) B4455971
theorem B1979417 : Blo 1319478 1979417 := bstep (se 2 (by rfl) ⟨742281, by rfl⟩ : syracuseStep 1979417 = 1484563) B1484563
theorem B1979531 : Blo 1319478 1979531 := bstep (se 1 (by rfl) ⟨1484648, by rfl⟩ : syracuseStep 1979531 = 2969297) B2969297
theorem B1979543 : Blo 1319478 1979543 := bstep (se 1 (by rfl) ⟨1484657, by rfl⟩ : syracuseStep 1979543 = 2969315) B2969315
theorem B2970827 : Blo 1319478 2970827 := bstep (se 1 (by rfl) ⟨2228120, by rfl⟩ : syracuseStep 2970827 = 4456241) B4456241
theorem B1979609 : Blo 1319478 1979609 := bstep (se 2 (by rfl) ⟨742353, by rfl⟩ : syracuseStep 1979609 = 1484707) B1484707
theorem B2970881 : Blo 1319478 2970881 := bstep (se 2 (by rfl) ⟨1114080, by rfl⟩ : syracuseStep 2970881 = 2228161) B2228161
theorem B7525649 : Blo 1319478 7525649 := bstep (se 2 (by rfl) ⟨2822118, by rfl⟩ : syracuseStep 7525649 = 5644237) B5644237
theorem B4232513 : Blo 1319478 4232513 := bstep (se 2 (by rfl) ⟨1587192, by rfl⟩ : syracuseStep 4232513 = 3174385) B3174385
theorem B1979723 : Blo 1319478 1979723 := bstep (se 1 (by rfl) ⟨1484792, by rfl⟩ : syracuseStep 1979723 = 2969585) B2969585
theorem B1979735 : Blo 1319478 1979735 := bstep (se 1 (by rfl) ⟨1484801, by rfl⟩ : syracuseStep 1979735 = 2969603) B2969603
theorem B5010781 : Blo 1319478 5010781 := bstep (se 3 (by rfl) ⟨939521, by rfl⟩ : syracuseStep 5010781 = 1879043) B1879043
theorem B4289885 : Blo 1319478 4289885 := bstep (se 3 (by rfl) ⟨804353, by rfl⟩ : syracuseStep 4289885 = 1608707) B1608707
theorem B1979801 : Blo 1319478 1979801 := bstep (se 2 (by rfl) ⟨742425, by rfl⟩ : syracuseStep 1979801 = 1484851) B1484851
theorem B4453811 : Blo 1319478 4453811 := bstep (se 1 (by rfl) ⟨3340358, by rfl⟩ : syracuseStep 4453811 = 6680717) B6680717
theorem B3757529 : Blo 1319478 3757529 := bstep (se 2 (by rfl) ⟨1409073, by rfl⟩ : syracuseStep 3757529 = 2818147) B2818147
theorem B2971097 : Blo 1319478 2971097 := bstep (se 2 (by rfl) ⟨1114161, by rfl⟩ : syracuseStep 2971097 = 2228323) B2228323
theorem B4232665 : Blo 1319478 4232665 := bstep (se 2 (by rfl) ⟨1587249, by rfl⟩ : syracuseStep 4232665 = 3174499) B3174499
theorem B1979915 : Blo 1319478 1979915 := bstep (se 1 (by rfl) ⟨1484936, by rfl⟩ : syracuseStep 1979915 = 2969873) B2969873
theorem B1979927 : Blo 1319478 1979927 := bstep (se 1 (by rfl) ⟨1484945, by rfl⟩ : syracuseStep 1979927 = 2969891) B2969891
theorem B2971187 : Blo 1319478 2971187 := bstep (se 1 (by rfl) ⟨2228390, by rfl⟩ : syracuseStep 2971187 = 4456781) B4456781
theorem B2971223 : Blo 1319478 2971223 := bstep (se 1 (by rfl) ⟨2228417, by rfl⟩ : syracuseStep 2971223 = 4456835) B4456835
theorem B1979993 : Blo 1319478 1979993 := bstep (se 2 (by rfl) ⟨742497, by rfl⟩ : syracuseStep 1979993 = 1484995) B1484995
theorem B1586827 : Blo 1319478 1586827 := bstep (se 1 (by rfl) ⟨1190120, by rfl⟩ : syracuseStep 1586827 = 2380241) B2380241
theorem B4454081 : Blo 1319478 4454081 := bstep (se 2 (by rfl) ⟨1670280, by rfl⟩ : syracuseStep 4454081 = 3340561) B3340561
theorem B1980107 : Blo 1319478 1980107 := bstep (se 1 (by rfl) ⟨1485080, by rfl⟩ : syracuseStep 1980107 = 2970161) B2970161
theorem B1980119 : Blo 1319478 1980119 := bstep (se 1 (by rfl) ⟨1485089, by rfl⟩ : syracuseStep 1980119 = 2970179) B2970179
theorem B7526105 : Blo 1319478 7526105 := bstep (se 2 (by rfl) ⟨2822289, by rfl⟩ : syracuseStep 7526105 = 5644579) B5644579
theorem B2971403 : Blo 1319478 2971403 := bstep (se 1 (by rfl) ⟨2228552, by rfl⟩ : syracuseStep 2971403 = 4457105) B4457105
theorem B10024721 : Blo 1319478 10024721 := bstep (se 2 (by rfl) ⟨3759270, by rfl⟩ : syracuseStep 10024721 = 7518541) B7518541
theorem B3340055 : Blo 1319478 3340055 := bstep (se 1 (by rfl) ⟨2505041, by rfl⟩ : syracuseStep 3340055 = 5010083) B5010083
theorem B1980185 : Blo 1319478 1980185 := bstep (se 2 (by rfl) ⟨742569, by rfl⟩ : syracuseStep 1980185 = 1485139) B1485139
theorem B2971457 : Blo 1319478 2971457 := bstep (se 2 (by rfl) ⟨1114296, by rfl⟩ : syracuseStep 2971457 = 2228593) B2228593
theorem B6682499 : Blo 1319478 6682499 := bstep (se 1 (by rfl) ⟨5011874, by rfl⟩ : syracuseStep 6682499 = 10023749) B10023749
theorem B1980299 : Blo 1319478 1980299 := bstep (se 1 (by rfl) ⟨1485224, by rfl⟩ : syracuseStep 1980299 = 2970449) B2970449
theorem B4757399 : Blo 1319478 4757399 := bstep (se 1 (by rfl) ⟨3568049, by rfl⟩ : syracuseStep 4757399 = 7136099) B7136099
theorem B1980311 : Blo 1319478 1980311 := bstep (se 1 (by rfl) ⟨1485233, by rfl⟩ : syracuseStep 1980311 = 2970467) B2970467
theorem B51460019 : Blo 1319478 51460019 := bstep (se 1 (by rfl) ⟨38595014, by rfl⟩ : syracuseStep 51460019 = 77190029) B77190029
theorem B1980377 : Blo 1319478 1980377 := bstep (se 2 (by rfl) ⟨742641, by rfl⟩ : syracuseStep 1980377 = 1485283) B1485283
theorem B2971673 : Blo 1319478 2971673 := bstep (se 2 (by rfl) ⟨1114377, by rfl⟩ : syracuseStep 2971673 = 2228755) B2228755
theorem B1980491 : Blo 1319478 1980491 := bstep (se 1 (by rfl) ⟨1485368, by rfl⟩ : syracuseStep 1980491 = 2970737) B2970737
theorem B1980503 : Blo 1319478 1980503 := bstep (se 1 (by rfl) ⟨1485377, by rfl⟩ : syracuseStep 1980503 = 2970755) B2970755
theorem B4757597 : Blo 1319478 4757597 := bstep (se 3 (by rfl) ⟨892049, by rfl⟩ : syracuseStep 4757597 = 1784099) B1784099
theorem B2971763 : Blo 1319478 2971763 := bstep (se 1 (by rfl) ⟨2228822, by rfl⟩ : syracuseStep 2971763 = 4457645) B4457645
theorem B7518359 : Blo 1319478 7518359 := bstep (se 1 (by rfl) ⟨5638769, by rfl⟩ : syracuseStep 7518359 = 11277539) B11277539
theorem B2259095 : Blo 1319478 2259095 := bstep (se 1 (by rfl) ⟨1694321, by rfl⟩ : syracuseStep 2259095 = 3388643) B3388643
theorem B1980569 : Blo 1319478 1980569 := bstep (se 2 (by rfl) ⟨742713, by rfl⟩ : syracuseStep 1980569 = 1485427) B1485427
theorem B2971799 : Blo 1319478 2971799 := bstep (se 1 (by rfl) ⟨2228849, by rfl⟩ : syracuseStep 2971799 = 4457699) B4457699
theorem B4454621 : Blo 1319478 4454621 := bstep (se 3 (by rfl) ⟨835241, by rfl⟩ : syracuseStep 4454621 = 1670483) B1670483
theorem B1980683 : Blo 1319478 1980683 := bstep (se 1 (by rfl) ⟨1485512, by rfl⟩ : syracuseStep 1980683 = 2971025) B2971025
theorem B1980695 : Blo 1319478 1980695 := bstep (se 1 (by rfl) ⟨1485521, by rfl⟩ : syracuseStep 1980695 = 2971043) B2971043
theorem B36616493 : Blo 1319478 36616493 := bstep (se 3 (by rfl) ⟨6865592, by rfl⟩ : syracuseStep 36616493 = 13731185) B13731185
theorem B2971979 : Blo 1319478 2971979 := bstep (se 1 (by rfl) ⟨2228984, by rfl⟩ : syracuseStep 2971979 = 4457969) B4457969
theorem B1980761 : Blo 1319478 1980761 := bstep (se 2 (by rfl) ⟨742785, by rfl⟩ : syracuseStep 1980761 = 1485571) B1485571
theorem B2972033 : Blo 1319478 2972033 := bstep (se 2 (by rfl) ⟨1114512, by rfl⟩ : syracuseStep 2972033 = 2229025) B2229025
theorem B2857367 : Blo 1319478 2857367 := bstep (se 1 (by rfl) ⟨2143025, by rfl⟩ : syracuseStep 2857367 = 4286051) B4286051
theorem B32135573 : Blo 1319478 32135573 := bstep (se 6 (by rfl) ⟨753177, by rfl⟩ : syracuseStep 32135573 = 1506355) B1506355
theorem B3340723 : Blo 1319478 3340723 := bstep (se 1 (by rfl) ⟨2505542, by rfl⟩ : syracuseStep 3340723 = 5011085) B5011085
theorem B2505163 : Blo 1319478 2505163 := bstep (se 1 (by rfl) ⟨1878872, by rfl⟩ : syracuseStep 2505163 = 3757745) B3757745
theorem B1980875 : Blo 1319478 1980875 := bstep (se 1 (by rfl) ⟨1485656, by rfl⟩ : syracuseStep 1980875 = 2971313) B2971313
theorem B1980887 : Blo 1319478 1980887 := bstep (se 1 (by rfl) ⟨1485665, by rfl⟩ : syracuseStep 1980887 = 2971331) B2971331
theorem B2226649 : Blo 1319478 2226649 := bstep (se 2 (by rfl) ⟨834993, by rfl⟩ : syracuseStep 2226649 = 1669987) B1669987
theorem B2505239 : Blo 1319478 2505239 := bstep (se 1 (by rfl) ⟨1878929, by rfl⟩ : syracuseStep 2505239 = 3757859) B3757859
theorem B1980953 : Blo 1319478 1980953 := bstep (se 2 (by rfl) ⟨742857, by rfl⟩ : syracuseStep 1980953 = 1485715) B1485715
theorem B3340865 : Blo 1319478 3340865 := bstep (se 2 (by rfl) ⟨1252824, by rfl⟩ : syracuseStep 3340865 = 2505649) B2505649
theorem B5012057 : Blo 1319478 5012057 := bstep (se 2 (by rfl) ⟨1879521, by rfl⟩ : syracuseStep 5012057 = 3759043) B3759043
theorem B2972249 : Blo 1319478 2972249 := bstep (se 2 (by rfl) ⟨1114593, by rfl⟩ : syracuseStep 2972249 = 2229187) B2229187
theorem B1981067 : Blo 1319478 1981067 := bstep (se 1 (by rfl) ⟨1485800, by rfl⟩ : syracuseStep 1981067 = 2971601) B2971601
theorem B1981079 : Blo 1319478 1981079 := bstep (se 1 (by rfl) ⟨1485809, by rfl⟩ : syracuseStep 1981079 = 2971619) B2971619
theorem B9173683 : Blo 1319478 9173683 := bstep (se 1 (by rfl) ⟨6880262, by rfl⟩ : syracuseStep 9173683 = 13760525) B13760525
theorem B2972339 : Blo 1319478 2972339 := bstep (se 1 (by rfl) ⟨2229254, by rfl⟩ : syracuseStep 2972339 = 4458509) B4458509
theorem B2259659 : Blo 1319478 2259659 := bstep (se 1 (by rfl) ⟨1694744, by rfl⟩ : syracuseStep 2259659 = 3389489) B3389489
theorem B2972375 : Blo 1319478 2972375 := bstep (se 1 (by rfl) ⟨2229281, by rfl⟩ : syracuseStep 2972375 = 4458563) B4458563
theorem B1981145 : Blo 1319478 1981145 := bstep (se 2 (by rfl) ⟨742929, by rfl⟩ : syracuseStep 1981145 = 1485859) B1485859
theorem B1784587 : Blo 1319478 1784587 := bstep (se 1 (by rfl) ⟨1338440, by rfl⟩ : syracuseStep 1784587 = 2676881) B2676881
theorem B10033955 : Blo 1319478 10033955 := bstep (se 1 (by rfl) ⟨7525466, by rfl⟩ : syracuseStep 10033955 = 15050933) B15050933
theorem B3054401 : Blo 1319478 3054401 := bstep (se 2 (by rfl) ⟨1145400, by rfl⟩ : syracuseStep 3054401 = 2290801) B2290801
theorem B6019915 : Blo 1319478 6019915 := bstep (se 1 (by rfl) ⟨4514936, by rfl⟩ : syracuseStep 6019915 = 9029873) B9029873
theorem B1981259 : Blo 1319478 1981259 := bstep (se 1 (by rfl) ⟨1485944, by rfl⟩ : syracuseStep 1981259 = 2971889) B2971889
theorem B1981271 : Blo 1319478 1981271 := bstep (se 1 (by rfl) ⟨1485953, by rfl⟩ : syracuseStep 1981271 = 2971907) B2971907
theorem B11443045 : Blo 1319478 11443045 := bstep (se 4 (by rfl) ⟨1072785, by rfl⟩ : syracuseStep 11443045 = 2145571) B2145571
theorem B2972555 : Blo 1319478 2972555 := bstep (se 1 (by rfl) ⟨2229416, by rfl⟩ : syracuseStep 2972555 = 4458833) B4458833
theorem B1981337 : Blo 1319478 1981337 := bstep (se 2 (by rfl) ⟨743001, by rfl⟩ : syracuseStep 1981337 = 1486003) B1486003
theorem B2972609 : Blo 1319478 2972609 := bstep (se 2 (by rfl) ⟨1114728, by rfl⟩ : syracuseStep 2972609 = 2229457) B2229457
theorem B1981451 : Blo 1319478 1981451 := bstep (se 1 (by rfl) ⟨1486088, by rfl⟩ : syracuseStep 1981451 = 2972177) B2972177
theorem B19029005 : Blo 1319478 19029005 := bstep (se 3 (by rfl) ⟨3567938, by rfl⟩ : syracuseStep 19029005 = 7135877) B7135877
theorem B2227223 : Blo 1319478 2227223 := bstep (se 1 (by rfl) ⟨1670417, by rfl⟩ : syracuseStep 2227223 = 3340835) B3340835
theorem B1981463 : Blo 1319478 1981463 := bstep (se 1 (by rfl) ⟨1486097, by rfl⟩ : syracuseStep 1981463 = 2972195) B2972195
theorem B3759169 : Blo 1319478 3759169 := bstep (se 2 (by rfl) ⟨1409688, by rfl⟩ : syracuseStep 3759169 = 2819377) B2819377
theorem B1981529 : Blo 1319478 1981529 := bstep (se 2 (by rfl) ⟨743073, by rfl⟩ : syracuseStep 1981529 = 1486147) B1486147
theorem B2227351 : Blo 1319478 2227351 := bstep (se 1 (by rfl) ⟨1670513, by rfl⟩ : syracuseStep 2227351 = 3341027) B3341027
theorem B2972825 : Blo 1319478 2972825 := bstep (se 2 (by rfl) ⟨1114809, by rfl⟩ : syracuseStep 2972825 = 2229619) B2229619
theorem B1506475 : Blo 1319478 1506475 := bstep (se 1 (by rfl) ⟨1129856, by rfl⟩ : syracuseStep 1506475 = 2259713) B2259713
theorem B2505907 : Blo 1319478 2505907 := bstep (se 1 (by rfl) ⟨1879430, by rfl⟩ : syracuseStep 2505907 = 3758861) B3758861
theorem B1981643 : Blo 1319478 1981643 := bstep (se 1 (by rfl) ⟨1486232, by rfl⟩ : syracuseStep 1981643 = 2972465) B2972465
theorem B1981655 : Blo 1319478 1981655 := bstep (se 1 (by rfl) ⟨1486241, by rfl⟩ : syracuseStep 1981655 = 2972483) B2972483
theorem B2972915 : Blo 1319478 2972915 := bstep (se 1 (by rfl) ⟨2229686, by rfl⟩ : syracuseStep 2972915 = 4459373) B4459373
theorem B2972951 : Blo 1319478 2972951 := bstep (se 1 (by rfl) ⟨2229713, by rfl⟩ : syracuseStep 2972951 = 4459427) B4459427
theorem B1981721 : Blo 1319478 1981721 := bstep (se 2 (by rfl) ⟨743145, by rfl⟩ : syracuseStep 1981721 = 1486291) B1486291
theorem B6348077 : Blo 1319478 6348077 := bstep (se 3 (by rfl) ⟨1190264, by rfl⟩ : syracuseStep 6348077 = 2380529) B2380529
theorem B4455755 : Blo 1319478 4455755 := bstep (se 1 (by rfl) ⟨3341816, by rfl⟩ : syracuseStep 4455755 = 6683633) B6683633
theorem B1670539 : Blo 1319478 1670539 := bstep (se 1 (by rfl) ⟨1252904, by rfl⟩ : syracuseStep 1670539 = 2505809) B2505809
theorem B1981835 : Blo 1319478 1981835 := bstep (se 1 (by rfl) ⟨1486376, by rfl⟩ : syracuseStep 1981835 = 2972753) B2972753
theorem B2506135 : Blo 1319478 2506135 := bstep (se 1 (by rfl) ⟨1879601, by rfl⟩ : syracuseStep 2506135 = 3759203) B3759203
theorem B1981847 : Blo 1319478 1981847 := bstep (se 1 (by rfl) ⟨1486385, by rfl⟩ : syracuseStep 1981847 = 2972771) B2972771
theorem B2973131 : Blo 1319478 2973131 := bstep (se 1 (by rfl) ⟨2229848, by rfl⟩ : syracuseStep 2973131 = 4459697) B4459697
theorem B1981913 : Blo 1319478 1981913 := bstep (se 2 (by rfl) ⟨743217, by rfl⟩ : syracuseStep 1981913 = 1486435) B1486435
theorem B2506241 : Blo 1319478 2506241 := bstep (se 2 (by rfl) ⟨939840, by rfl⟩ : syracuseStep 2506241 = 1879681) B1879681
theorem B2973185 : Blo 1319478 2973185 := bstep (se 2 (by rfl) ⟨1114944, by rfl⟩ : syracuseStep 2973185 = 2229889) B2229889
theorem B5078531 : Blo 1319478 5078531 := bstep (se 1 (by rfl) ⟨3808898, by rfl⟩ : syracuseStep 5078531 = 7617797) B7617797
theorem B5643827 : Blo 1319478 5643827 := bstep (se 1 (by rfl) ⟨4232870, by rfl⟩ : syracuseStep 5643827 = 8465741) B8465741
theorem B1982027 : Blo 1319478 1982027 := bstep (se 1 (by rfl) ⟨1486520, by rfl⟩ : syracuseStep 1982027 = 2973041) B2973041
theorem B1982039 : Blo 1319478 1982039 := bstep (se 1 (by rfl) ⟨1486529, by rfl⟩ : syracuseStep 1982039 = 2973059) B2973059
theorem B4456025 : Blo 1319478 4456025 := bstep (se 2 (by rfl) ⟨1671009, by rfl⟩ : syracuseStep 4456025 = 3342019) B3342019
theorem B1670807 : Blo 1319478 1670807 := bstep (se 1 (by rfl) ⟨1253105, by rfl⟩ : syracuseStep 1670807 = 2506211) B2506211
theorem B2506393 : Blo 1319478 2506393 := bstep (se 2 (by rfl) ⟨939897, by rfl⟩ : syracuseStep 2506393 = 1879795) B1879795
theorem B1982105 : Blo 1319478 1982105 := bstep (se 2 (by rfl) ⟨743289, by rfl⟩ : syracuseStep 1982105 = 1486579) B1486579
theorem B2227979 : Blo 1319478 2227979 := bstep (se 1 (by rfl) ⟨1670984, by rfl⟩ : syracuseStep 2227979 = 3341969) B3341969
theorem B3342131 : Blo 1319478 3342131 := bstep (se 1 (by rfl) ⟨2506598, by rfl⟩ : syracuseStep 3342131 = 5013197) B5013197
theorem B10166147 : Blo 1319478 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B2228107 : Blo 1319478 2228107 := bstep (se 1 (by rfl) ⟨1671080, by rfl⟩ : syracuseStep 2228107 = 3342161) B3342161
theorem B5078963 : Blo 1319478 5078963 := bstep (se 1 (by rfl) ⟨3809222, by rfl⟩ : syracuseStep 5078963 = 7618445) B7618445
theorem B22855603 : Blo 1319478 22855603 := bstep (se 1 (by rfl) ⟨17141702, by rfl⟩ : syracuseStep 22855603 = 34283405) B34283405
theorem B5013515 : Blo 1319478 5013515 := bstep (se 1 (by rfl) ⟨3760136, by rfl⟩ : syracuseStep 5013515 = 7520273) B7520273
theorem B9519115 : Blo 1319478 9519115 := bstep (se 1 (by rfl) ⟨7139336, by rfl⟩ : syracuseStep 9519115 = 14278673) B14278673
theorem B25747469 : Blo 1319478 25747469 := bstep (se 3 (by rfl) ⟨4827650, by rfl⟩ : syracuseStep 25747469 = 9655301) B9655301
theorem B3342455 : Blo 1319478 3342455 := bstep (se 1 (by rfl) ⟨2506841, by rfl⟩ : syracuseStep 3342455 = 5013683) B5013683
theorem B7143661 : Blo 1319478 7143661 := bstep (se 3 (by rfl) ⟨1339436, by rfl⟩ : syracuseStep 7143661 = 2678873) B2678873
theorem B6684929 : Blo 1319478 6684929 := bstep (se 2 (by rfl) ⟨2506848, by rfl⟩ : syracuseStep 6684929 = 5013697) B5013697
theorem B2228539 : Blo 1319478 2228539 := bstep (se 1 (by rfl) ⟨1671404, by rfl⟩ : syracuseStep 2228539 = 3342809) B3342809
theorem B3760445 : Blo 1319478 3760445 := bstep (se 3 (by rfl) ⟨705083, by rfl⟩ : syracuseStep 3760445 = 1410167) B1410167
theorem B2818489 : Blo 1319478 2818489 := bstep (se 2 (by rfl) ⟨1056933, by rfl⟩ : syracuseStep 2818489 = 2113867) B2113867
theorem B4456889 : Blo 1319478 4456889 := bstep (se 2 (by rfl) ⟨1671333, by rfl⟩ : syracuseStep 4456889 = 3342667) B3342667
theorem B2228681 : Blo 1319478 2228681 := bstep (se 2 (by rfl) ⟨835755, by rfl⟩ : syracuseStep 2228681 = 1671511) B1671511
theorem B5423645 : Blo 1319478 5423645 := bstep (se 3 (by rfl) ⟨1016933, by rfl⟩ : syracuseStep 5423645 = 2033867) B2033867
theorem B1319483 : Blo 1319478 1319483 := bstep (se 1 (by rfl) ⟨989612, by rfl⟩ : syracuseStep 1319483 = 1979225) B1979225
theorem B1319559 : Blo 1319478 1319559 := bstep (se 1 (by rfl) ⟨989669, by rfl⟩ : syracuseStep 1319559 = 1979339) B1979339
theorem B3760775 : Blo 1319478 3760775 := bstep (se 1 (by rfl) ⟨2820581, by rfl⟩ : syracuseStep 3760775 = 5641163) B5641163
theorem B1319567 : Blo 1319478 1319567 := bstep (se 1 (by rfl) ⟨989675, by rfl⟩ : syracuseStep 1319567 = 1979351) B1979351
theorem B3170963 : Blo 1319478 3170963 := bstep (se 1 (by rfl) ⟨2378222, by rfl⟩ : syracuseStep 3170963 = 4756445) B4756445
theorem B2507411 : Blo 1319478 2507411 := bstep (se 1 (by rfl) ⟨1880558, by rfl⟩ : syracuseStep 2507411 = 3761117) B3761117
theorem B2507449 : Blo 1319478 2507449 := bstep (se 2 (by rfl) ⟨940293, by rfl⟩ : syracuseStep 2507449 = 1880587) B1880587
theorem B1319611 : Blo 1319478 1319611 := bstep (se 1 (by rfl) ⟨989708, by rfl⟩ : syracuseStep 1319611 = 1979417) B1979417
theorem B1319687 : Blo 1319478 1319687 := bstep (se 1 (by rfl) ⟨989765, by rfl⟩ : syracuseStep 1319687 = 1979531) B1979531
theorem B1319695 : Blo 1319478 1319695 := bstep (se 1 (by rfl) ⟨989771, by rfl⟩ : syracuseStep 1319695 = 1979543) B1979543
theorem B1319739 : Blo 1319478 1319739 := bstep (se 1 (by rfl) ⟨989804, by rfl⟩ : syracuseStep 1319739 = 1979609) B1979609
theorem B1319815 : Blo 1319478 1319815 := bstep (se 1 (by rfl) ⟨989861, by rfl⟩ : syracuseStep 1319815 = 1979723) B1979723
theorem B1319823 : Blo 1319478 1319823 := bstep (se 1 (by rfl) ⟨989867, by rfl⟩ : syracuseStep 1319823 = 1979735) B1979735
theorem B2859923 : Blo 1319478 2859923 := bstep (se 1 (by rfl) ⟨2144942, by rfl⟩ : syracuseStep 2859923 = 4289885) B4289885
theorem B12231577 : Blo 1319478 12231577 := bstep (se 2 (by rfl) ⟨4586841, by rfl⟩ : syracuseStep 12231577 = 9173683) B9173683
theorem B5014457 : Blo 1319478 5014457 := bstep (se 2 (by rfl) ⟨1880421, by rfl⟩ : syracuseStep 5014457 = 3760843) B3760843
theorem B1319867 : Blo 1319478 1319867 := bstep (se 1 (by rfl) ⟨989900, by rfl⟩ : syracuseStep 1319867 = 1979801) B1979801
theorem B1319943 : Blo 1319478 1319943 := bstep (se 1 (by rfl) ⟨989957, by rfl⟩ : syracuseStep 1319943 = 1979915) B1979915
theorem B4457483 : Blo 1319478 4457483 := bstep (se 1 (by rfl) ⟨3343112, by rfl⟩ : syracuseStep 4457483 = 6686225) B6686225
theorem B1319951 : Blo 1319478 1319951 := bstep (se 1 (by rfl) ⟨989963, by rfl⟩ : syracuseStep 1319951 = 1979927) B1979927
theorem B6685739 : Blo 1319478 6685739 := bstep (se 1 (by rfl) ⟨5014304, by rfl⟩ : syracuseStep 6685739 = 10028609) B10028609
theorem B1319995 : Blo 1319478 1319995 := bstep (se 1 (by rfl) ⟨989996, by rfl⟩ : syracuseStep 1319995 = 1979993) B1979993
theorem B7619645 : Blo 1319478 7619645 := bstep (se 3 (by rfl) ⟨1428683, by rfl⟩ : syracuseStep 7619645 = 2857367) B2857367
theorem B4457591 : Blo 1319478 4457591 := bstep (se 1 (by rfl) ⟨3343193, by rfl⟩ : syracuseStep 4457591 = 6686387) B6686387
theorem B1320071 : Blo 1319478 1320071 := bstep (se 1 (by rfl) ⟨990053, by rfl⟩ : syracuseStep 1320071 = 1980107) B1980107
theorem B2229383 : Blo 1319478 2229383 := bstep (se 1 (by rfl) ⟨1672037, by rfl⟩ : syracuseStep 2229383 = 3344075) B3344075
theorem B1320079 : Blo 1319478 1320079 := bstep (se 1 (by rfl) ⟨990059, by rfl⟩ : syracuseStep 1320079 = 1980119) B1980119
theorem B1320123 : Blo 1319478 1320123 := bstep (se 1 (by rfl) ⟨990092, by rfl⟩ : syracuseStep 1320123 = 1980185) B1980185
theorem B1320199 : Blo 1319478 1320199 := bstep (se 1 (by rfl) ⟨990149, by rfl⟩ : syracuseStep 1320199 = 1980299) B1980299
theorem B3171599 : Blo 1319478 3171599 := bstep (se 1 (by rfl) ⟨2378699, by rfl⟩ : syracuseStep 3171599 = 4757399) B4757399
theorem B1320207 : Blo 1319478 1320207 := bstep (se 1 (by rfl) ⟨990155, by rfl⟩ : syracuseStep 1320207 = 1980311) B1980311
theorem B1320251 : Blo 1319478 1320251 := bstep (se 1 (by rfl) ⟨990188, by rfl⟩ : syracuseStep 1320251 = 1980377) B1980377
theorem B1320327 : Blo 1319478 1320327 := bstep (se 1 (by rfl) ⟨990245, by rfl⟩ : syracuseStep 1320327 = 1980491) B1980491
theorem B3343751 : Blo 1319478 3343751 := bstep (se 1 (by rfl) ⟨2507813, by rfl⟩ : syracuseStep 3343751 = 5015627) B5015627
theorem B1320335 : Blo 1319478 1320335 := bstep (se 1 (by rfl) ⟨990251, by rfl⟩ : syracuseStep 1320335 = 1980503) B1980503
theorem B3171731 : Blo 1319478 3171731 := bstep (se 1 (by rfl) ⟨2378798, by rfl⟩ : syracuseStep 3171731 = 4757597) B4757597
theorem B3343801 : Blo 1319478 3343801 := bstep (se 2 (by rfl) ⟨1253925, by rfl⟩ : syracuseStep 3343801 = 2507851) B2507851
theorem B1320379 : Blo 1319478 1320379 := bstep (se 1 (by rfl) ⟨990284, by rfl⟩ : syracuseStep 1320379 = 1980569) B1980569
theorem B11437571 : Blo 1319478 11437571 := bstep (se 1 (by rfl) ⟨8578178, by rfl⟩ : syracuseStep 11437571 = 17156357) B17156357
theorem B1320455 : Blo 1319478 1320455 := bstep (se 1 (by rfl) ⟨990341, by rfl⟩ : syracuseStep 1320455 = 1980683) B1980683
theorem B1320463 : Blo 1319478 1320463 := bstep (se 1 (by rfl) ⟨990347, by rfl⟩ : syracuseStep 1320463 = 1980695) B1980695
theorem B2008633 : Blo 1319478 2008633 := bstep (se 2 (by rfl) ⟨753237, by rfl⟩ : syracuseStep 2008633 = 1506475) B1506475
theorem B1320507 : Blo 1319478 1320507 := bstep (se 1 (by rfl) ⟨990380, by rfl⟩ : syracuseStep 1320507 = 1980761) B1980761
theorem B1320583 : Blo 1319478 1320583 := bstep (se 1 (by rfl) ⟨990437, by rfl⟩ : syracuseStep 1320583 = 1980875) B1980875
theorem B1320591 : Blo 1319478 1320591 := bstep (se 1 (by rfl) ⟨990443, by rfl⟩ : syracuseStep 1320591 = 1980887) B1980887
theorem B1320635 : Blo 1319478 1320635 := bstep (se 1 (by rfl) ⟨990476, by rfl⟩ : syracuseStep 1320635 = 1980953) B1980953
theorem B4458185 : Blo 1319478 4458185 := bstep (se 2 (by rfl) ⟨1671819, by rfl⟩ : syracuseStep 4458185 = 3343639) B3343639
theorem B1320711 : Blo 1319478 1320711 := bstep (se 1 (by rfl) ⟨990533, by rfl⟩ : syracuseStep 1320711 = 1981067) B1981067
theorem B1320719 : Blo 1319478 1320719 := bstep (se 1 (by rfl) ⟨990539, by rfl⟩ : syracuseStep 1320719 = 1981079) B1981079
theorem B1320763 : Blo 1319478 1320763 := bstep (se 1 (by rfl) ⟨990572, by rfl⟩ : syracuseStep 1320763 = 1981145) B1981145
theorem B1320839 : Blo 1319478 1320839 := bstep (se 1 (by rfl) ⟨990629, by rfl⟩ : syracuseStep 1320839 = 1981259) B1981259
theorem B1320847 : Blo 1319478 1320847 := bstep (se 1 (by rfl) ⟨990635, by rfl⟩ : syracuseStep 1320847 = 1981271) B1981271
theorem B7235513 : Blo 1319478 7235513 := bstep (se 2 (by rfl) ⟨2713317, by rfl⟩ : syracuseStep 7235513 = 5426635) B5426635
theorem B1320891 : Blo 1319478 1320891 := bstep (se 1 (by rfl) ⟨990668, by rfl⟩ : syracuseStep 1320891 = 1981337) B1981337
theorem B1320967 : Blo 1319478 1320967 := bstep (se 1 (by rfl) ⟨990725, by rfl⟩ : syracuseStep 1320967 = 1981451) B1981451
theorem B1484815 : Blo 1319478 1484815 := bstep (se 1 (by rfl) ⟨1113611, by rfl⟩ : syracuseStep 1484815 = 2227223) B2227223
theorem B1320975 : Blo 1319478 1320975 := bstep (se 1 (by rfl) ⟨990731, by rfl⟩ : syracuseStep 1320975 = 1981463) B1981463
theorem B3344399 : Blo 1319478 3344399 := bstep (se 1 (by rfl) ⟨2508299, by rfl⟩ : syracuseStep 3344399 = 5016599) B5016599
theorem B1321019 : Blo 1319478 1321019 := bstep (se 1 (by rfl) ⟨990764, by rfl⟩ : syracuseStep 1321019 = 1981529) B1981529
theorem B1321095 : Blo 1319478 1321095 := bstep (se 1 (by rfl) ⟨990821, by rfl⟩ : syracuseStep 1321095 = 1981643) B1981643
theorem B1321103 : Blo 1319478 1321103 := bstep (se 1 (by rfl) ⟨990827, by rfl⟩ : syracuseStep 1321103 = 1981655) B1981655
theorem B2115769 : Blo 1319478 2115769 := bstep (se 2 (by rfl) ⟨793413, by rfl⟩ : syracuseStep 2115769 = 1586827) B1586827
theorem B1321147 : Blo 1319478 1321147 := bstep (se 1 (by rfl) ⟨990860, by rfl⟩ : syracuseStep 1321147 = 1981721) B1981721
theorem B17148149 : Blo 1319478 17148149 := bstep (se 5 (by rfl) ⟨803819, by rfl⟩ : syracuseStep 17148149 = 1607639) B1607639
theorem B1321223 : Blo 1319478 1321223 := bstep (se 1 (by rfl) ⟨990917, by rfl⟩ : syracuseStep 1321223 = 1981835) B1981835
theorem B1321231 : Blo 1319478 1321231 := bstep (se 1 (by rfl) ⟨990923, by rfl⟩ : syracuseStep 1321231 = 1981847) B1981847
theorem B6687035 : Blo 1319478 6687035 := bstep (se 1 (by rfl) ⟨5015276, by rfl⟩ : syracuseStep 6687035 = 10030553) B10030553
theorem B1321275 : Blo 1319478 1321275 := bstep (se 1 (by rfl) ⟨990956, by rfl⟩ : syracuseStep 1321275 = 1981913) B1981913
theorem B3385687 : Blo 1319478 3385687 := bstep (se 1 (by rfl) ⟨2539265, by rfl⟩ : syracuseStep 3385687 = 5078531) B5078531
theorem B3762551 : Blo 1319478 3762551 := bstep (se 1 (by rfl) ⟨2821913, by rfl⟩ : syracuseStep 3762551 = 5643827) B5643827
theorem B4458887 : Blo 1319478 4458887 := bstep (se 1 (by rfl) ⟨3344165, by rfl⟩ : syracuseStep 4458887 = 6688331) B6688331
theorem B1321351 : Blo 1319478 1321351 := bstep (se 1 (by rfl) ⟨991013, by rfl⟩ : syracuseStep 1321351 = 1982027) B1982027
theorem B1321359 : Blo 1319478 1321359 := bstep (se 1 (by rfl) ⟨991019, by rfl⟩ : syracuseStep 1321359 = 1982039) B1982039
theorem B1321403 : Blo 1319478 1321403 := bstep (se 1 (by rfl) ⟨991052, by rfl⟩ : syracuseStep 1321403 = 1982105) B1982105
theorem B6687197 : Blo 1319478 6687197 := bstep (se 3 (by rfl) ⟨1253849, by rfl⟩ : syracuseStep 6687197 = 2507699) B2507699
theorem B1485319 : Blo 1319478 1485319 := bstep (se 1 (by rfl) ⟨1113989, by rfl⟩ : syracuseStep 1485319 = 2227979) B2227979
theorem B5081611 : Blo 1319478 5081611 := bstep (se 1 (by rfl) ⟨3811208, by rfl⟩ : syracuseStep 5081611 = 7622417) B7622417
theorem B19032641 : Blo 1319478 19032641 := bstep (se 2 (by rfl) ⟨7137240, by rfl⟩ : syracuseStep 19032641 = 14274481) B14274481
theorem B6777431 : Blo 1319478 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B3385975 : Blo 1319478 3385975 := bstep (se 1 (by rfl) ⟨2539481, by rfl⟩ : syracuseStep 3385975 = 5078963) B5078963
theorem B1485499 : Blo 1319478 1485499 := bstep (se 1 (by rfl) ⟨1114124, by rfl⟩ : syracuseStep 1485499 = 2228249) B2228249
theorem B4459265 : Blo 1319478 4459265 := bstep (se 2 (by rfl) ⟨1672224, by rfl⟩ : syracuseStep 4459265 = 3344449) B3344449
theorem B6687521 : Blo 1319478 6687521 := bstep (se 2 (by rfl) ⟨2507820, by rfl⟩ : syracuseStep 6687521 = 5015641) B5015641
theorem B2820923 : Blo 1319478 2820923 := bstep (se 1 (by rfl) ⟨2115692, by rfl⟩ : syracuseStep 2820923 = 4231385) B4231385
theorem B12684235 : Blo 1319478 12684235 := bstep (se 1 (by rfl) ⟨9513176, by rfl⟩ : syracuseStep 12684235 = 19026353) B19026353
theorem B20327435 : Blo 1319478 20327435 := bstep (se 1 (by rfl) ⟨15245576, by rfl⟩ : syracuseStep 20327435 = 30491153) B30491153
theorem B2116667 : Blo 1319478 2116667 := bstep (se 1 (by rfl) ⟨1587500, by rfl⟩ : syracuseStep 2116667 = 3175001) B3175001
theorem B1485967 : Blo 1319478 1485967 := bstep (se 1 (by rfl) ⟨1114475, by rfl⟩ : syracuseStep 1485967 = 2228951) B2228951
theorem B2968847 : Blo 1319478 2968847 := bstep (se 1 (by rfl) ⟨2226635, by rfl⟩ : syracuseStep 2968847 = 4453271) B4453271
theorem B2968865 : Blo 1319478 2968865 := bstep (se 2 (by rfl) ⟨1113324, by rfl⟩ : syracuseStep 2968865 = 2226649) B2226649
theorem B3566891 : Blo 1319478 3566891 := bstep (se 1 (by rfl) ⟨2675168, by rfl⟩ : syracuseStep 3566891 = 5350337) B5350337
theorem B7515443 : Blo 1319478 7515443 := bstep (se 1 (by rfl) ⟨5636582, by rfl⟩ : syracuseStep 7515443 = 11273165) B11273165
theorem B10022291 : Blo 1319478 10022291 := bstep (se 1 (by rfl) ⟨7516718, by rfl⟩ : syracuseStep 10022291 = 15033437) B15033437
theorem B97643981 : Blo 1319478 97643981 := bstep (se 3 (by rfl) ⟨18308246, by rfl⟩ : syracuseStep 97643981 = 36616493) B36616493
theorem B5017099 : Blo 1319478 5017099 := bstep (se 1 (by rfl) ⟨3762824, by rfl⟩ : syracuseStep 5017099 = 7525649) B7525649
theorem B2821675 : Blo 1319478 2821675 := bstep (se 1 (by rfl) ⟨2116256, by rfl⟩ : syracuseStep 2821675 = 4232513) B4232513
theorem B7237187 : Blo 1319478 7237187 := bstep (se 1 (by rfl) ⟨5427890, by rfl⟩ : syracuseStep 7237187 = 10855781) B10855781
theorem B2969207 : Blo 1319478 2969207 := bstep (se 1 (by rfl) ⟨2226905, by rfl⟩ : syracuseStep 2969207 = 4453811) B4453811
theorem B1486471 : Blo 1319478 1486471 := bstep (se 1 (by rfl) ⟨1114853, by rfl⟩ : syracuseStep 1486471 = 2229707) B2229707
theorem B2379449 : Blo 1319478 2379449 := bstep (se 2 (by rfl) ⟨892293, by rfl⟩ : syracuseStep 2379449 = 1784587) B1784587
theorem B6688493 : Blo 1319478 6688493 := bstep (se 3 (by rfl) ⟨1254092, by rfl⟩ : syracuseStep 6688493 = 2508185) B2508185
theorem B2969387 : Blo 1319478 2969387 := bstep (se 1 (by rfl) ⟨2227040, by rfl⟩ : syracuseStep 2969387 = 4454081) B4454081
theorem B15257393 : Blo 1319478 15257393 := bstep (se 2 (by rfl) ⟨5721522, by rfl⟩ : syracuseStep 15257393 = 11443045) B11443045
theorem B5017403 : Blo 1319478 5017403 := bstep (se 1 (by rfl) ⟨3763052, by rfl⟩ : syracuseStep 5017403 = 7526105) B7526105
theorem B1486651 : Blo 1319478 1486651 := bstep (se 1 (by rfl) ⟨1114988, by rfl⟩ : syracuseStep 1486651 = 2229977) B2229977
theorem B3387271 : Blo 1319478 3387271 := bstep (se 1 (by rfl) ⟨2540453, by rfl⟩ : syracuseStep 3387271 = 5080907) B5080907
theorem B3174443 : Blo 1319478 3174443 := bstep (se 1 (by rfl) ⟨2380832, by rfl⟩ : syracuseStep 3174443 = 4761665) B4761665
theorem B22556717 : Blo 1319478 22556717 := bstep (se 3 (by rfl) ⟨4229384, by rfl⟩ : syracuseStep 22556717 = 8458769) B8458769
theorem B2969747 : Blo 1319478 2969747 := bstep (se 1 (by rfl) ⟨2227310, by rfl⟩ : syracuseStep 2969747 = 4454621) B4454621
theorem B2969801 : Blo 1319478 2969801 := bstep (se 2 (by rfl) ⟨1113675, by rfl⟩ : syracuseStep 2969801 = 2227351) B2227351
theorem B24097013 : Blo 1319478 24097013 := bstep (se 5 (by rfl) ⟨1129547, by rfl⟩ : syracuseStep 24097013 = 2259095) B2259095
theorem B6681041 : Blo 1319478 6681041 := bstep (se 2 (by rfl) ⟨2505390, by rfl⟩ : syracuseStep 6681041 = 5010781) B5010781
theorem B6689303 : Blo 1319478 6689303 := bstep (se 1 (by rfl) ⟨5016977, by rfl⟩ : syracuseStep 6689303 = 10033955) B10033955
theorem B2036267 : Blo 1319478 2036267 := bstep (se 1 (by rfl) ⟨1527200, by rfl⟩ : syracuseStep 2036267 = 3054401) B3054401
theorem B3814003 : Blo 1319478 3814003 := bstep (se 1 (by rfl) ⟨2860502, by rfl⟩ : syracuseStep 3814003 = 5721005) B5721005
theorem B1880695 : Blo 1319478 1880695 := bstep (se 1 (by rfl) ⟨1410521, by rfl⟩ : syracuseStep 1880695 = 2821043) B2821043
theorem B12686003 : Blo 1319478 12686003 := bstep (se 1 (by rfl) ⟨9514502, by rfl⟩ : syracuseStep 12686003 = 19029005) B19029005
theorem B7516901 : Blo 1319478 7516901 := bstep (se 4 (by rfl) ⟨704709, by rfl⟩ : syracuseStep 7516901 = 1409419) B1409419
theorem B5640941 : Blo 1319478 5640941 := bstep (se 3 (by rfl) ⟨1057676, by rfl⟩ : syracuseStep 5640941 = 2115353) B2115353
theorem B4232051 : Blo 1319478 4232051 := bstep (se 1 (by rfl) ⟨3174038, by rfl⟩ : syracuseStep 4232051 = 6348077) B6348077
theorem B1979255 : Blo 1319478 1979255 := bstep (se 1 (by rfl) ⟨1484441, by rfl⟩ : syracuseStep 1979255 = 2968883) B2968883
theorem B2970503 : Blo 1319478 2970503 := bstep (se 1 (by rfl) ⟨2227877, by rfl⟩ : syracuseStep 2970503 = 4455755) B4455755
theorem B1979279 : Blo 1319478 1979279 := bstep (se 1 (by rfl) ⟨1484459, by rfl⟩ : syracuseStep 1979279 = 2968919) B2968919
theorem B1979321 : Blo 1319478 1979321 := bstep (se 2 (by rfl) ⟨742245, by rfl⟩ : syracuseStep 1979321 = 1484491) B1484491
theorem B1979399 : Blo 1319478 1979399 := bstep (se 1 (by rfl) ⟨1484549, by rfl⟩ : syracuseStep 1979399 = 2969099) B2969099
theorem B1979435 : Blo 1319478 1979435 := bstep (se 1 (by rfl) ⟨1484576, by rfl⟩ : syracuseStep 1979435 = 2969153) B2969153
theorem B2970683 : Blo 1319478 2970683 := bstep (se 1 (by rfl) ⟨2228012, by rfl⟩ : syracuseStep 2970683 = 4456025) B4456025
theorem B5715011 : Blo 1319478 5715011 := bstep (se 1 (by rfl) ⟨4286258, by rfl⟩ : syracuseStep 5715011 = 8572517) B8572517
theorem B1979465 : Blo 1319478 1979465 := bstep (se 2 (by rfl) ⟨742299, by rfl⟩ : syracuseStep 1979465 = 1484599) B1484599
theorem B14283863 : Blo 1319478 14283863 := bstep (se 1 (by rfl) ⟨10712897, by rfl⟩ : syracuseStep 14283863 = 21425795) B21425795
theorem B22574213 : Blo 1319478 22574213 := bstep (se 4 (by rfl) ⟨2116332, by rfl⟩ : syracuseStep 22574213 = 4232665) B4232665
theorem B7517357 : Blo 1319478 7517357 := bstep (se 3 (by rfl) ⟨1409504, by rfl⟩ : syracuseStep 7517357 = 2819009) B2819009
theorem B8459437 : Blo 1319478 8459437 := bstep (se 3 (by rfl) ⟨1586144, by rfl⟩ : syracuseStep 8459437 = 3172289) B3172289
theorem B2970809 : Blo 1319478 2970809 := bstep (se 2 (by rfl) ⟨1114053, by rfl⟩ : syracuseStep 2970809 = 2228107) B2228107
theorem B1979579 : Blo 1319478 1979579 := bstep (se 1 (by rfl) ⟨1484684, by rfl⟩ : syracuseStep 1979579 = 2969369) B2969369
theorem B13743341 : Blo 1319478 13743341 := bstep (se 3 (by rfl) ⟨2576876, by rfl⟩ : syracuseStep 13743341 = 5153753) B5153753
theorem B1979639 : Blo 1319478 1979639 := bstep (se 1 (by rfl) ⟨1484729, by rfl⟩ : syracuseStep 1979639 = 2969459) B2969459
theorem B1979663 : Blo 1319478 1979663 := bstep (se 1 (by rfl) ⟨1484747, by rfl⟩ : syracuseStep 1979663 = 2969495) B2969495
theorem B1979705 : Blo 1319478 1979705 := bstep (se 2 (by rfl) ⟨742389, by rfl⟩ : syracuseStep 1979705 = 1484779) B1484779
theorem B1979783 : Blo 1319478 1979783 := bstep (se 1 (by rfl) ⟨1484837, by rfl⟩ : syracuseStep 1979783 = 2969675) B2969675
theorem B9524627 : Blo 1319478 9524627 := bstep (se 1 (by rfl) ⟨7143470, by rfl⟩ : syracuseStep 9524627 = 14286941) B14286941
theorem B1979819 : Blo 1319478 1979819 := bstep (se 1 (by rfl) ⟨1484864, by rfl⟩ : syracuseStep 1979819 = 2969729) B2969729
theorem B1881515 : Blo 1319478 1881515 := bstep (se 1 (by rfl) ⟨1411136, by rfl⟩ : syracuseStep 1881515 = 2822273) B2822273
theorem B1979849 : Blo 1319478 1979849 := bstep (se 2 (by rfl) ⟨742443, by rfl⟩ : syracuseStep 1979849 = 1484887) B1484887
theorem B6772177 : Blo 1319478 6772177 := bstep (se 2 (by rfl) ⟨2539566, by rfl⟩ : syracuseStep 6772177 = 5079133) B5079133
theorem B2971151 : Blo 1319478 2971151 := bstep (se 1 (by rfl) ⟨2228363, by rfl⟩ : syracuseStep 2971151 = 4456727) B4456727
theorem B2971169 : Blo 1319478 2971169 := bstep (se 2 (by rfl) ⟨1114188, by rfl⟩ : syracuseStep 2971169 = 2228377) B2228377
theorem B14267947 : Blo 1319478 14267947 := bstep (se 1 (by rfl) ⟨10700960, by rfl⟩ : syracuseStep 14267947 = 21401921) B21401921
theorem B1979963 : Blo 1319478 1979963 := bstep (se 1 (by rfl) ⟨1484972, by rfl⟩ : syracuseStep 1979963 = 2969945) B2969945
theorem B6108739 : Blo 1319478 6108739 := bstep (se 1 (by rfl) ⟨4581554, by rfl⟩ : syracuseStep 6108739 = 9163109) B9163109
theorem B1980023 : Blo 1319478 1980023 := bstep (se 1 (by rfl) ⟨1485017, by rfl⟩ : syracuseStep 1980023 = 2970035) B2970035
theorem B1980047 : Blo 1319478 1980047 := bstep (se 1 (by rfl) ⟨1485035, by rfl⟩ : syracuseStep 1980047 = 2970071) B2970071
theorem B28554929 : Blo 1319478 28554929 := bstep (se 2 (by rfl) ⟨10708098, by rfl⟩ : syracuseStep 28554929 = 21416197) B21416197
theorem B1980089 : Blo 1319478 1980089 := bstep (se 2 (by rfl) ⟨742533, by rfl⟩ : syracuseStep 1980089 = 1485067) B1485067
theorem B8935105 : Blo 1319478 8935105 := bstep (se 2 (by rfl) ⟨3350664, by rfl⟩ : syracuseStep 8935105 = 6701329) B6701329
theorem B1980167 : Blo 1319478 1980167 := bstep (se 1 (by rfl) ⟨1485125, by rfl⟩ : syracuseStep 1980167 = 2970251) B2970251
theorem B11286287 : Blo 1319478 11286287 := bstep (se 1 (by rfl) ⟨8464715, by rfl⟩ : syracuseStep 11286287 = 16929431) B16929431
theorem B3340075 : Blo 1319478 3340075 := bstep (se 1 (by rfl) ⟨2505056, by rfl⟩ : syracuseStep 3340075 = 5010113) B5010113
theorem B1980203 : Blo 1319478 1980203 := bstep (se 1 (by rfl) ⟨1485152, by rfl⟩ : syracuseStep 1980203 = 2970305) B2970305
theorem B2676539 : Blo 1319478 2676539 := bstep (se 1 (by rfl) ⟨2007404, by rfl⟩ : syracuseStep 2676539 = 4014809) B4014809
theorem B1980233 : Blo 1319478 1980233 := bstep (se 2 (by rfl) ⟨742587, by rfl⟩ : syracuseStep 1980233 = 1485175) B1485175
theorem B7518041 : Blo 1319478 7518041 := bstep (se 2 (by rfl) ⟨2819265, by rfl⟩ : syracuseStep 7518041 = 5638531) B5638531
theorem B2971511 : Blo 1319478 2971511 := bstep (se 1 (by rfl) ⟨2228633, by rfl⟩ : syracuseStep 2971511 = 4457267) B4457267
theorem B4454297 : Blo 1319478 4454297 := bstep (se 2 (by rfl) ⟨1670361, by rfl⟩ : syracuseStep 4454297 = 3340723) B3340723
theorem B3340217 : Blo 1319478 3340217 := bstep (se 2 (by rfl) ⟨1252581, by rfl⟩ : syracuseStep 3340217 = 2505163) B2505163
theorem B1980347 : Blo 1319478 1980347 := bstep (se 1 (by rfl) ⟨1485260, by rfl⟩ : syracuseStep 1980347 = 2970521) B2970521
theorem B1980407 : Blo 1319478 1980407 := bstep (se 1 (by rfl) ⟨1485305, by rfl⟩ : syracuseStep 1980407 = 2970611) B2970611
theorem B1980431 : Blo 1319478 1980431 := bstep (se 1 (by rfl) ⟨1485323, by rfl⟩ : syracuseStep 1980431 = 2970647) B2970647
theorem B2971691 : Blo 1319478 2971691 := bstep (se 1 (by rfl) ⟨2228768, by rfl⟩ : syracuseStep 2971691 = 4457537) B4457537
theorem B1980473 : Blo 1319478 1980473 := bstep (se 2 (by rfl) ⟨742677, by rfl⟩ : syracuseStep 1980473 = 1485355) B1485355
theorem B1980551 : Blo 1319478 1980551 := bstep (se 1 (by rfl) ⟨1485413, by rfl⟩ : syracuseStep 1980551 = 2970827) B2970827
theorem B1980587 : Blo 1319478 1980587 := bstep (se 1 (by rfl) ⟨1485440, by rfl⟩ : syracuseStep 1980587 = 2970881) B2970881
theorem B1980617 : Blo 1319478 1980617 := bstep (se 2 (by rfl) ⟨742731, by rfl⟩ : syracuseStep 1980617 = 1485463) B1485463
theorem B12859681 : Blo 1319478 12859681 := bstep (se 2 (by rfl) ⟨4822380, by rfl⟩ : syracuseStep 12859681 = 9644761) B9644761
theorem B2505019 : Blo 1319478 2505019 := bstep (se 1 (by rfl) ⟨1878764, by rfl⟩ : syracuseStep 2505019 = 3757529) B3757529
theorem B1980731 : Blo 1319478 1980731 := bstep (se 1 (by rfl) ⟨1485548, by rfl⟩ : syracuseStep 1980731 = 2971097) B2971097
theorem B1980791 : Blo 1319478 1980791 := bstep (se 1 (by rfl) ⟨1485593, by rfl⟩ : syracuseStep 1980791 = 2971187) B2971187
theorem B85694861 : Blo 1319478 85694861 := bstep (se 3 (by rfl) ⟨16067786, by rfl⟩ : syracuseStep 85694861 = 32135573) B32135573
theorem B1980815 : Blo 1319478 1980815 := bstep (se 1 (by rfl) ⟨1485611, by rfl⟩ : syracuseStep 1980815 = 2971223) B2971223
theorem B6347153 : Blo 1319478 6347153 := bstep (se 2 (by rfl) ⟨2380182, by rfl⟩ : syracuseStep 6347153 = 4760365) B4760365
theorem B2677139 : Blo 1319478 2677139 := bstep (se 1 (by rfl) ⟨2007854, by rfl⟩ : syracuseStep 2677139 = 4015709) B4015709
theorem B2972051 : Blo 1319478 2972051 := bstep (se 1 (by rfl) ⟨2229038, by rfl⟩ : syracuseStep 2972051 = 4458077) B4458077
theorem B8026553 : Blo 1319478 8026553 := bstep (se 2 (by rfl) ⟨3009957, by rfl⟩ : syracuseStep 8026553 = 6019915) B6019915
theorem B1980857 : Blo 1319478 1980857 := bstep (se 2 (by rfl) ⟨742821, by rfl⟩ : syracuseStep 1980857 = 1485643) B1485643
theorem B2972105 : Blo 1319478 2972105 := bstep (se 2 (by rfl) ⟨1114539, by rfl⟩ : syracuseStep 2972105 = 2229079) B2229079
theorem B1980935 : Blo 1319478 1980935 := bstep (se 1 (by rfl) ⟨1485701, by rfl⟩ : syracuseStep 1980935 = 2971403) B2971403
theorem B6683147 : Blo 1319478 6683147 := bstep (se 1 (by rfl) ⟨5012360, by rfl⟩ : syracuseStep 6683147 = 10024721) B10024721
theorem B2226703 : Blo 1319478 2226703 := bstep (se 1 (by rfl) ⟨1670027, by rfl⟩ : syracuseStep 2226703 = 3340055) B3340055
theorem B1980971 : Blo 1319478 1980971 := bstep (se 1 (by rfl) ⟨1485728, by rfl⟩ : syracuseStep 1980971 = 2971457) B2971457
theorem B1981001 : Blo 1319478 1981001 := bstep (se 2 (by rfl) ⟨742875, by rfl⟩ : syracuseStep 1981001 = 1485751) B1485751
theorem B4454999 : Blo 1319478 4454999 := bstep (se 1 (by rfl) ⟨3341249, by rfl⟩ : syracuseStep 4454999 = 6682499) B6682499
theorem B34306679 : Blo 1319478 34306679 := bstep (se 1 (by rfl) ⟨25730009, by rfl⟩ : syracuseStep 34306679 = 51460019) B51460019
theorem B6683309 : Blo 1319478 6683309 := bstep (se 3 (by rfl) ⟨1253120, by rfl⟩ : syracuseStep 6683309 = 2506241) B2506241
theorem B1981115 : Blo 1319478 1981115 := bstep (se 1 (by rfl) ⟨1485836, by rfl⟩ : syracuseStep 1981115 = 2971673) B2971673
theorem B1981175 : Blo 1319478 1981175 := bstep (se 1 (by rfl) ⟨1485881, by rfl⟩ : syracuseStep 1981175 = 2971763) B2971763
theorem B5012225 : Blo 1319478 5012225 := bstep (se 2 (by rfl) ⟨1879584, by rfl⟩ : syracuseStep 5012225 = 3759169) B3759169
theorem B5012239 : Blo 1319478 5012239 := bstep (se 1 (by rfl) ⟨3759179, by rfl⟩ : syracuseStep 5012239 = 7518359) B7518359
theorem B1981199 : Blo 1319478 1981199 := bstep (se 1 (by rfl) ⟨1485899, by rfl⟩ : syracuseStep 1981199 = 2971799) B2971799
theorem B2505505 : Blo 1319478 2505505 := bstep (se 2 (by rfl) ⟨939564, by rfl⟩ : syracuseStep 2505505 = 1879129) B1879129
theorem B15039269 : Blo 1319478 15039269 := bstep (se 4 (by rfl) ⟨1409931, by rfl⟩ : syracuseStep 15039269 = 2819863) B2819863
theorem B1981241 : Blo 1319478 1981241 := bstep (se 2 (by rfl) ⟨742965, by rfl⟩ : syracuseStep 1981241 = 1485931) B1485931
theorem B1981319 : Blo 1319478 1981319 := bstep (se 1 (by rfl) ⟨1485989, by rfl⟩ : syracuseStep 1981319 = 2971979) B2971979
theorem B3341209 : Blo 1319478 3341209 := bstep (se 2 (by rfl) ⟨1252953, by rfl⟩ : syracuseStep 3341209 = 2505907) B2505907
theorem B1981355 : Blo 1319478 1981355 := bstep (se 1 (by rfl) ⟨1486016, by rfl⟩ : syracuseStep 1981355 = 2972033) B2972033
theorem B1981385 : Blo 1319478 1981385 := bstep (se 2 (by rfl) ⟨743019, by rfl⟩ : syracuseStep 1981385 = 1486039) B1486039
theorem B6962129 : Blo 1319478 6962129 := bstep (se 2 (by rfl) ⟨2610798, by rfl⟩ : syracuseStep 6962129 = 5221597) B5221597
theorem B1670159 : Blo 1319478 1670159 := bstep (se 1 (by rfl) ⟨1252619, by rfl⟩ : syracuseStep 1670159 = 2505239) B2505239
theorem B2227243 : Blo 1319478 2227243 := bstep (se 1 (by rfl) ⟨1670432, by rfl⟩ : syracuseStep 2227243 = 3340865) B3340865
theorem B3341371 : Blo 1319478 3341371 := bstep (se 1 (by rfl) ⟨2506028, by rfl⟩ : syracuseStep 3341371 = 5012057) B5012057
theorem B1981499 : Blo 1319478 1981499 := bstep (se 1 (by rfl) ⟨1486124, by rfl⟩ : syracuseStep 1981499 = 2972249) B2972249
theorem B4455485 : Blo 1319478 4455485 := bstep (se 3 (by rfl) ⟨835403, by rfl⟩ : syracuseStep 4455485 = 1670807) B1670807
theorem B1981559 : Blo 1319478 1981559 := bstep (se 1 (by rfl) ⟨1486169, by rfl⟩ : syracuseStep 1981559 = 2972339) B2972339
theorem B1506439 : Blo 1319478 1506439 := bstep (se 1 (by rfl) ⟨1129829, by rfl⟩ : syracuseStep 1506439 = 2259659) B2259659
theorem B2972807 : Blo 1319478 2972807 := bstep (se 1 (by rfl) ⟨2229605, by rfl⟩ : syracuseStep 2972807 = 4459211) B4459211
theorem B1981583 : Blo 1319478 1981583 := bstep (se 1 (by rfl) ⟨1486187, by rfl⟩ : syracuseStep 1981583 = 2972375) B2972375
theorem B2227385 : Blo 1319478 2227385 := bstep (se 2 (by rfl) ⟨835269, by rfl⟩ : syracuseStep 2227385 = 1670539) B1670539
theorem B1981625 : Blo 1319478 1981625 := bstep (se 2 (by rfl) ⟨743109, by rfl⟩ : syracuseStep 1981625 = 1486219) B1486219
theorem B3341513 : Blo 1319478 3341513 := bstep (se 2 (by rfl) ⟨1253067, by rfl⟩ : syracuseStep 3341513 = 2506135) B2506135
theorem B1981703 : Blo 1319478 1981703 := bstep (se 1 (by rfl) ⟨1486277, by rfl⟩ : syracuseStep 1981703 = 2972555) B2972555
theorem B1981739 : Blo 1319478 1981739 := bstep (se 1 (by rfl) ⟨1486304, by rfl⟩ : syracuseStep 1981739 = 2972609) B2972609
theorem B2972987 : Blo 1319478 2972987 := bstep (se 1 (by rfl) ⟨2229740, by rfl⟩ : syracuseStep 2972987 = 4459481) B4459481
theorem B1981769 : Blo 1319478 1981769 := bstep (se 2 (by rfl) ⟨743163, by rfl⟩ : syracuseStep 1981769 = 1486327) B1486327
theorem B2973113 : Blo 1319478 2973113 := bstep (se 2 (by rfl) ⟨1114917, by rfl⟩ : syracuseStep 2973113 = 2229835) B2229835
theorem B1981883 : Blo 1319478 1981883 := bstep (se 1 (by rfl) ⟨1486412, by rfl⟩ : syracuseStep 1981883 = 2972825) B2972825
theorem B1981943 : Blo 1319478 1981943 := bstep (se 1 (by rfl) ⟨1486457, by rfl⟩ : syracuseStep 1981943 = 2972915) B2972915
theorem B1981967 : Blo 1319478 1981967 := bstep (se 1 (by rfl) ⟨1486475, by rfl⟩ : syracuseStep 1981967 = 2972951) B2972951
theorem B3341857 : Blo 1319478 3341857 := bstep (se 2 (by rfl) ⟨1253196, by rfl⟩ : syracuseStep 3341857 = 2506393) B2506393
theorem B3759659 : Blo 1319478 3759659 := bstep (se 1 (by rfl) ⟨2819744, by rfl⟩ : syracuseStep 3759659 = 5639489) B5639489
theorem B1982009 : Blo 1319478 1982009 := bstep (se 2 (by rfl) ⟨743253, by rfl⟩ : syracuseStep 1982009 = 1486507) B1486507
theorem B5643863 : Blo 1319478 5643863 := bstep (se 1 (by rfl) ⟨4232897, by rfl⟩ : syracuseStep 5643863 = 8465795) B8465795
theorem B1982087 : Blo 1319478 1982087 := bstep (se 1 (by rfl) ⟨1486565, by rfl⟩ : syracuseStep 1982087 = 2973131) B2973131
theorem B1982123 : Blo 1319478 1982123 := bstep (se 1 (by rfl) ⟨1486592, by rfl⟩ : syracuseStep 1982123 = 2973185) B2973185
theorem B1982153 : Blo 1319478 1982153 := bstep (se 2 (by rfl) ⟨743307, by rfl⟩ : syracuseStep 1982153 = 1486615) B1486615
theorem B13549285 : Blo 1319478 13549285 := bstep (se 4 (by rfl) ⟨1270245, by rfl⟩ : syracuseStep 13549285 = 2540491) B2540491
theorem B6348577 : Blo 1319478 6348577 := bstep (se 2 (by rfl) ⟨2380716, by rfl⟩ : syracuseStep 6348577 = 4761433) B4761433
theorem B2228087 : Blo 1319478 2228087 := bstep (se 1 (by rfl) ⟨1671065, by rfl⟩ : syracuseStep 2228087 = 3342131) B3342131
theorem B30474137 : Blo 1319478 30474137 := bstep (se 2 (by rfl) ⟨11427801, by rfl⟩ : syracuseStep 30474137 = 22855603) B22855603
theorem B2506697 : Blo 1319478 2506697 := bstep (se 2 (by rfl) ⟨940011, by rfl⟩ : syracuseStep 2506697 = 1880023) B1880023
theorem B3342343 : Blo 1319478 3342343 := bstep (se 1 (by rfl) ⟨2506757, by rfl⟩ : syracuseStep 3342343 = 5013515) B5013515
theorem B2228303 : Blo 1319478 2228303 := bstep (se 1 (by rfl) ⟨1671227, by rfl⟩ : syracuseStep 2228303 = 3342455) B3342455
theorem B16064675 : Blo 1319478 16064675 := bstep (se 1 (by rfl) ⟨12048506, by rfl⟩ : syracuseStep 16064675 = 24097013) B24097013
theorem B4456619 : Blo 1319478 4456619 := bstep (se 1 (by rfl) ⟨3342464, by rfl⟩ : syracuseStep 4456619 = 6684929) B6684929
theorem B2506963 : Blo 1319478 2506963 := bstep (se 1 (by rfl) ⟨1880222, by rfl⟩ : syracuseStep 2506963 = 3760445) B3760445
theorem B32579941 : Blo 1319478 32579941 := bstep (se 4 (by rfl) ⟨3054369, by rfl⟩ : syracuseStep 32579941 = 6108739) B6108739
theorem B17146241 : Blo 1319478 17146241 := bstep (se 2 (by rfl) ⟨6429840, by rfl⟩ : syracuseStep 17146241 = 12859681) B12859681
theorem B2507183 : Blo 1319478 2507183 := bstep (se 1 (by rfl) ⟨1880387, by rfl⟩ : syracuseStep 2507183 = 3760775) B3760775
theorem B2113975 : Blo 1319478 2113975 := bstep (se 1 (by rfl) ⟨1585481, by rfl⟩ : syracuseStep 2113975 = 3170963) B3170963
theorem B1671607 : Blo 1319478 1671607 := bstep (se 1 (by rfl) ⟨1253705, by rfl⟩ : syracuseStep 1671607 = 2507411) B2507411
theorem B4514249 : Blo 1319478 4514249 := bstep (se 2 (by rfl) ⟨1692843, by rfl⟩ : syracuseStep 4514249 = 3385687) B3385687
theorem B3760627 : Blo 1319478 3760627 := bstep (se 1 (by rfl) ⟨2820470, by rfl⟩ : syracuseStep 3760627 = 5640941) B5640941
theorem B1319503 : Blo 1319478 1319503 := bstep (se 1 (by rfl) ⟨989627, by rfl⟩ : syracuseStep 1319503 = 1979255) B1979255
theorem B1319519 : Blo 1319478 1319519 := bstep (se 1 (by rfl) ⟨989639, by rfl⟩ : syracuseStep 1319519 = 1979279) B1979279
theorem B1319547 : Blo 1319478 1319547 := bstep (se 1 (by rfl) ⟨989660, by rfl⟩ : syracuseStep 1319547 = 1979321) B1979321
theorem B3342971 : Blo 1319478 3342971 := bstep (se 1 (by rfl) ⟨2507228, by rfl⟩ : syracuseStep 3342971 = 5014457) B5014457
theorem B1319599 : Blo 1319478 1319599 := bstep (se 1 (by rfl) ⟨989699, by rfl⟩ : syracuseStep 1319599 = 1979399) B1979399
theorem B6775481 : Blo 1319478 6775481 := bstep (se 2 (by rfl) ⟨2540805, by rfl⟩ : syracuseStep 6775481 = 5081611) B5081611
theorem B1319623 : Blo 1319478 1319623 := bstep (se 1 (by rfl) ⟨989717, by rfl⟩ : syracuseStep 1319623 = 1979435) B1979435
theorem B4457159 : Blo 1319478 4457159 := bstep (se 1 (by rfl) ⟨3342869, by rfl⟩ : syracuseStep 4457159 = 6685739) B6685739
theorem B5079763 : Blo 1319478 5079763 := bstep (se 1 (by rfl) ⟨3809822, by rfl⟩ : syracuseStep 5079763 = 7619645) B7619645
theorem B3810007 : Blo 1319478 3810007 := bstep (se 1 (by rfl) ⟨2857505, by rfl⟩ : syracuseStep 3810007 = 5715011) B5715011
theorem B1319643 : Blo 1319478 1319643 := bstep (se 1 (by rfl) ⟨989732, by rfl⟩ : syracuseStep 1319643 = 1979465) B1979465
theorem B15049475 : Blo 1319478 15049475 := bstep (se 1 (by rfl) ⟨11287106, by rfl⟩ : syracuseStep 15049475 = 22574213) B22574213
theorem B1319719 : Blo 1319478 1319719 := bstep (se 1 (by rfl) ⟨989789, by rfl⟩ : syracuseStep 1319719 = 1979579) B1979579
theorem B4514633 : Blo 1319478 4514633 := bstep (se 2 (by rfl) ⟨1692987, by rfl⟩ : syracuseStep 4514633 = 3385975) B3385975
theorem B2507593 : Blo 1319478 2507593 := bstep (se 2 (by rfl) ⟨940347, by rfl⟩ : syracuseStep 2507593 = 1880695) B1880695
theorem B1319759 : Blo 1319478 1319759 := bstep (se 1 (by rfl) ⟨989819, by rfl⟩ : syracuseStep 1319759 = 1979639) B1979639
theorem B1319775 : Blo 1319478 1319775 := bstep (se 1 (by rfl) ⟨989831, by rfl⟩ : syracuseStep 1319775 = 1979663) B1979663
theorem B2114399 : Blo 1319478 2114399 := bstep (se 1 (by rfl) ⟨1585799, by rfl⟩ : syracuseStep 2114399 = 3171599) B3171599
theorem B1319803 : Blo 1319478 1319803 := bstep (se 1 (by rfl) ⟨989852, by rfl⟩ : syracuseStep 1319803 = 1979705) B1979705
theorem B3343265 : Blo 1319478 3343265 := bstep (se 2 (by rfl) ⟨1253724, by rfl⟩ : syracuseStep 3343265 = 2507449) B2507449
theorem B1319855 : Blo 1319478 1319855 := bstep (se 1 (by rfl) ⟨989891, by rfl⟩ : syracuseStep 1319855 = 1979783) B1979783
theorem B2229167 : Blo 1319478 2229167 := bstep (se 1 (by rfl) ⟨1671875, by rfl⟩ : syracuseStep 2229167 = 3343751) B3343751
theorem B6349751 : Blo 1319478 6349751 := bstep (se 1 (by rfl) ⟨4762313, by rfl⟩ : syracuseStep 6349751 = 9524627) B9524627
theorem B1319879 : Blo 1319478 1319879 := bstep (se 1 (by rfl) ⟨989909, by rfl⟩ : syracuseStep 1319879 = 1979819) B1979819
theorem B1319899 : Blo 1319478 1319899 := bstep (se 1 (by rfl) ⟨989924, by rfl⟩ : syracuseStep 1319899 = 1979849) B1979849
theorem B1319975 : Blo 1319478 1319975 := bstep (se 1 (by rfl) ⟨989981, by rfl⟩ : syracuseStep 1319975 = 1979963) B1979963
theorem B1320015 : Blo 1319478 1320015 := bstep (se 1 (by rfl) ⟨990011, by rfl⟩ : syracuseStep 1320015 = 1980023) B1980023
theorem B1320031 : Blo 1319478 1320031 := bstep (se 1 (by rfl) ⟨990023, by rfl⟩ : syracuseStep 1320031 = 1980047) B1980047
theorem B1320059 : Blo 1319478 1320059 := bstep (se 1 (by rfl) ⟨990044, by rfl⟩ : syracuseStep 1320059 = 1980089) B1980089
theorem B1320111 : Blo 1319478 1320111 := bstep (se 1 (by rfl) ⟨990083, by rfl⟩ : syracuseStep 1320111 = 1980167) B1980167
theorem B1320135 : Blo 1319478 1320135 := bstep (se 1 (by rfl) ⟨990101, by rfl⟩ : syracuseStep 1320135 = 1980203) B1980203
theorem B1320155 : Blo 1319478 1320155 := bstep (se 1 (by rfl) ⟨990116, by rfl⟩ : syracuseStep 1320155 = 1980233) B1980233
theorem B1320231 : Blo 1319478 1320231 := bstep (se 1 (by rfl) ⟨990173, by rfl⟩ : syracuseStep 1320231 = 1980347) B1980347
theorem B1320271 : Blo 1319478 1320271 := bstep (se 1 (by rfl) ⟨990203, by rfl⟩ : syracuseStep 1320271 = 1980407) B1980407
theorem B1320287 : Blo 1319478 1320287 := bstep (se 1 (by rfl) ⟨990215, by rfl⟩ : syracuseStep 1320287 = 1980431) B1980431
theorem B2229599 : Blo 1319478 2229599 := bstep (se 1 (by rfl) ⟨1672199, by rfl⟩ : syracuseStep 2229599 = 3344399) B3344399
theorem B1320315 : Blo 1319478 1320315 := bstep (se 1 (by rfl) ⟨990236, by rfl⟩ : syracuseStep 1320315 = 1980473) B1980473
theorem B1320367 : Blo 1319478 1320367 := bstep (se 1 (by rfl) ⟨990275, by rfl⟩ : syracuseStep 1320367 = 1980551) B1980551
theorem B1320391 : Blo 1319478 1320391 := bstep (se 1 (by rfl) ⟨990293, by rfl⟩ : syracuseStep 1320391 = 1980587) B1980587
theorem B1320411 : Blo 1319478 1320411 := bstep (se 1 (by rfl) ⟨990308, by rfl⟩ : syracuseStep 1320411 = 1980617) B1980617
theorem B2008585 : Blo 1319478 2008585 := bstep (se 2 (by rfl) ⟨753219, by rfl⟩ : syracuseStep 2008585 = 1506439) B1506439
theorem B1320487 : Blo 1319478 1320487 := bstep (se 1 (by rfl) ⟨990365, by rfl⟩ : syracuseStep 1320487 = 1980731) B1980731
theorem B4458023 : Blo 1319478 4458023 := bstep (se 1 (by rfl) ⟨3343517, by rfl⟩ : syracuseStep 4458023 = 6687035) B6687035
theorem B1320527 : Blo 1319478 1320527 := bstep (se 1 (by rfl) ⟨990395, by rfl⟩ : syracuseStep 1320527 = 1980791) B1980791
theorem B1320543 : Blo 1319478 1320543 := bstep (se 1 (by rfl) ⟨990407, by rfl⟩ : syracuseStep 1320543 = 1980815) B1980815
theorem B5351035 : Blo 1319478 5351035 := bstep (se 1 (by rfl) ⟨4013276, by rfl⟩ : syracuseStep 5351035 = 8026553) B8026553
theorem B1320571 : Blo 1319478 1320571 := bstep (se 1 (by rfl) ⟨990428, by rfl⟩ : syracuseStep 1320571 = 1980857) B1980857
theorem B4458131 : Blo 1319478 4458131 := bstep (se 1 (by rfl) ⟨3343598, by rfl⟩ : syracuseStep 4458131 = 6687197) B6687197
theorem B1320623 : Blo 1319478 1320623 := bstep (se 1 (by rfl) ⟨990467, by rfl⟩ : syracuseStep 1320623 = 1980935) B1980935
theorem B1320647 : Blo 1319478 1320647 := bstep (se 1 (by rfl) ⟨990485, by rfl⟩ : syracuseStep 1320647 = 1980971) B1980971
theorem B1320667 : Blo 1319478 1320667 := bstep (se 1 (by rfl) ⟨990500, by rfl⟩ : syracuseStep 1320667 = 1981001) B1981001
theorem B1320743 : Blo 1319478 1320743 := bstep (se 1 (by rfl) ⟨990557, by rfl⟩ : syracuseStep 1320743 = 1981115) B1981115
theorem B1320783 : Blo 1319478 1320783 := bstep (se 1 (by rfl) ⟨990587, by rfl⟩ : syracuseStep 1320783 = 1981175) B1981175
theorem B1320799 : Blo 1319478 1320799 := bstep (se 1 (by rfl) ⟨990599, by rfl⟩ : syracuseStep 1320799 = 1981199) B1981199
theorem B4458347 : Blo 1319478 4458347 := bstep (se 1 (by rfl) ⟨3343760, by rfl⟩ : syracuseStep 4458347 = 6687521) B6687521
theorem B1320827 : Blo 1319478 1320827 := bstep (se 1 (by rfl) ⟨990620, by rfl⟩ : syracuseStep 1320827 = 1981241) B1981241
theorem B4458401 : Blo 1319478 4458401 := bstep (se 2 (by rfl) ⟨1671900, by rfl⟩ : syracuseStep 4458401 = 3343801) B3343801
theorem B1320879 : Blo 1319478 1320879 := bstep (se 1 (by rfl) ⟨990659, by rfl⟩ : syracuseStep 1320879 = 1981319) B1981319
theorem B9029569 : Blo 1319478 9029569 := bstep (se 2 (by rfl) ⟨3386088, by rfl⟩ : syracuseStep 9029569 = 6772177) B6772177
theorem B1320903 : Blo 1319478 1320903 := bstep (se 1 (by rfl) ⟨990677, by rfl⟩ : syracuseStep 1320903 = 1981355) B1981355
theorem B1320923 : Blo 1319478 1320923 := bstep (se 1 (by rfl) ⟨990692, by rfl⟩ : syracuseStep 1320923 = 1981385) B1981385
theorem B13551623 : Blo 1319478 13551623 := bstep (se 1 (by rfl) ⟨10163717, by rfl⟩ : syracuseStep 13551623 = 20327435) B20327435
theorem B1320999 : Blo 1319478 1320999 := bstep (se 1 (by rfl) ⟨990749, by rfl⟩ : syracuseStep 1320999 = 1981499) B1981499
theorem B1411111 : Blo 1319478 1411111 := bstep (se 1 (by rfl) ⟨1058333, by rfl⟩ : syracuseStep 1411111 = 2116667) B2116667
theorem B19023929 : Blo 1319478 19023929 := bstep (se 2 (by rfl) ⟨7133973, by rfl⟩ : syracuseStep 19023929 = 14267947) B14267947
theorem B3762233 : Blo 1319478 3762233 := bstep (se 2 (by rfl) ⟨1410837, by rfl⟩ : syracuseStep 3762233 = 2821675) B2821675
theorem B1321039 : Blo 1319478 1321039 := bstep (se 1 (by rfl) ⟨990779, by rfl⟩ : syracuseStep 1321039 = 1981559) B1981559
theorem B1321055 : Blo 1319478 1321055 := bstep (se 1 (by rfl) ⟨990791, by rfl⟩ : syracuseStep 1321055 = 1981583) B1981583
theorem B1484923 : Blo 1319478 1484923 := bstep (se 1 (by rfl) ⟨1113692, by rfl⟩ : syracuseStep 1484923 = 2227385) B2227385
theorem B1321083 : Blo 1319478 1321083 := bstep (se 1 (by rfl) ⟨990812, by rfl⟩ : syracuseStep 1321083 = 1981625) B1981625
theorem B1321135 : Blo 1319478 1321135 := bstep (se 1 (by rfl) ⟨990851, by rfl⟩ : syracuseStep 1321135 = 1981703) B1981703
theorem B2377927 : Blo 1319478 2377927 := bstep (se 1 (by rfl) ⟨1783445, by rfl⟩ : syracuseStep 2377927 = 3566891) B3566891
theorem B1321159 : Blo 1319478 1321159 := bstep (se 1 (by rfl) ⟨990869, by rfl⟩ : syracuseStep 1321159 = 1981739) B1981739
theorem B1321179 : Blo 1319478 1321179 := bstep (se 1 (by rfl) ⟨990884, by rfl⟩ : syracuseStep 1321179 = 1981769) B1981769
theorem B11913473 : Blo 1319478 11913473 := bstep (se 2 (by rfl) ⟨4467552, by rfl⟩ : syracuseStep 11913473 = 8935105) B8935105
theorem B1321255 : Blo 1319478 1321255 := bstep (se 1 (by rfl) ⟨990941, by rfl⟩ : syracuseStep 1321255 = 1981883) B1981883
theorem B18065713 : Blo 1319478 18065713 := bstep (se 2 (by rfl) ⟨6774642, by rfl⟩ : syracuseStep 18065713 = 13549285) B13549285
theorem B65095987 : Blo 1319478 65095987 := bstep (se 1 (by rfl) ⟨48821990, by rfl⟩ : syracuseStep 65095987 = 97643981) B97643981
theorem B1321295 : Blo 1319478 1321295 := bstep (se 1 (by rfl) ⟨990971, by rfl⟩ : syracuseStep 1321295 = 1981943) B1981943
theorem B1321311 : Blo 1319478 1321311 := bstep (se 1 (by rfl) ⟨990983, by rfl⟩ : syracuseStep 1321311 = 1981967) B1981967
theorem B1321339 : Blo 1319478 1321339 := bstep (se 1 (by rfl) ⟨991004, by rfl⟩ : syracuseStep 1321339 = 1982009) B1982009
theorem B8464769 : Blo 1319478 8464769 := bstep (se 2 (by rfl) ⟨3174288, by rfl⟩ : syracuseStep 8464769 = 6348577) B6348577
theorem B3762575 : Blo 1319478 3762575 := bstep (se 1 (by rfl) ⟨2821931, by rfl⟩ : syracuseStep 3762575 = 5643863) B5643863
theorem B1321391 : Blo 1319478 1321391 := bstep (se 1 (by rfl) ⟨991043, by rfl⟩ : syracuseStep 1321391 = 1982087) B1982087
theorem B1321415 : Blo 1319478 1321415 := bstep (se 1 (by rfl) ⟨991061, by rfl⟩ : syracuseStep 1321415 = 1982123) B1982123
theorem B1321435 : Blo 1319478 1321435 := bstep (se 1 (by rfl) ⟨991076, by rfl⟩ : syracuseStep 1321435 = 1982153) B1982153
theorem B4458995 : Blo 1319478 4458995 := bstep (se 1 (by rfl) ⟨3344246, by rfl⟩ : syracuseStep 4458995 = 6688493) B6688493
theorem B4516361 : Blo 1319478 4516361 := bstep (se 2 (by rfl) ⟨1693635, by rfl⟩ : syracuseStep 4516361 = 3387271) B3387271
theorem B3344935 : Blo 1319478 3344935 := bstep (se 1 (by rfl) ⟨2508701, by rfl⟩ : syracuseStep 3344935 = 5017403) B5017403
theorem B1485391 : Blo 1319478 1485391 := bstep (se 1 (by rfl) ⟨1114043, by rfl⟩ : syracuseStep 1485391 = 2228087) B2228087
theorem B17164979 : Blo 1319478 17164979 := bstep (se 1 (by rfl) ⟨12873734, by rfl⟩ : syracuseStep 17164979 = 25747469) B25747469
theorem B12692153 : Blo 1319478 12692153 := bstep (se 2 (by rfl) ⟨4759557, by rfl⟩ : syracuseStep 12692153 = 9519115) B9519115
theorem B2116295 : Blo 1319478 2116295 := bstep (se 1 (by rfl) ⟨1587221, by rfl⟩ : syracuseStep 2116295 = 3174443) B3174443
theorem B2821025 : Blo 1319478 2821025 := bstep (se 2 (by rfl) ⟨1057884, by rfl⟩ : syracuseStep 2821025 = 2115769) B2115769
theorem B1485787 : Blo 1319478 1485787 := bstep (se 1 (by rfl) ⟨1114340, by rfl⟩ : syracuseStep 1485787 = 2228681) B2228681
theorem B4459535 : Blo 1319478 4459535 := bstep (se 1 (by rfl) ⟨3344651, by rfl⟩ : syracuseStep 4459535 = 6689303) B6689303
theorem B8457335 : Blo 1319478 8457335 := bstep (se 1 (by rfl) ⟨6343001, by rfl⟩ : syracuseStep 8457335 = 12686003) B12686003
theorem B2821367 : Blo 1319478 2821367 := bstep (se 1 (by rfl) ⟨2116025, by rfl⟩ : syracuseStep 2821367 = 4232051) B4232051
theorem B2968937 : Blo 1319478 2968937 := bstep (se 2 (by rfl) ⟨1113351, by rfl⟩ : syracuseStep 2968937 = 2226703) B2226703
theorem B9522575 : Blo 1319478 9522575 := bstep (se 1 (by rfl) ⟨7141931, by rfl⟩ : syracuseStep 9522575 = 14283863) B14283863
theorem B1486255 : Blo 1319478 1486255 := bstep (se 1 (by rfl) ⟨1114691, by rfl⟩ : syracuseStep 1486255 = 2229383) B2229383
theorem B9162227 : Blo 1319478 9162227 := bstep (se 1 (by rfl) ⟨6871670, by rfl⟩ : syracuseStep 9162227 = 13743341) B13743341
theorem B8457949 : Blo 1319478 8457949 := bstep (se 3 (by rfl) ⟨1585865, by rfl⟩ : syracuseStep 8457949 = 3171731) B3171731
theorem B5017373 : Blo 1319478 5017373 := bstep (se 3 (by rfl) ⟨940757, by rfl⟩ : syracuseStep 5017373 = 1881515) B1881515
theorem B7524191 : Blo 1319478 7524191 := bstep (se 1 (by rfl) ⟨5643143, by rfl⟩ : syracuseStep 7524191 = 11286287) B11286287
theorem B16912313 : Blo 1319478 16912313 := bstep (se 2 (by rfl) ⟨6342117, by rfl⟩ : syracuseStep 16912313 = 12684235) B12684235
theorem B2969531 : Blo 1319478 2969531 := bstep (se 1 (by rfl) ⟨2227148, by rfl⟩ : syracuseStep 2969531 = 4454297) B4454297
theorem B2969657 : Blo 1319478 2969657 := bstep (se 2 (by rfl) ⟨1113621, by rfl⟩ : syracuseStep 2969657 = 2227243) B2227243
theorem B14463053 : Blo 1319478 14463053 := bstep (se 3 (by rfl) ⟨2711822, by rfl⟩ : syracuseStep 14463053 = 5423645) B5423645
theorem B11432099 : Blo 1319478 11432099 := bstep (se 1 (by rfl) ⟨8574074, by rfl⟩ : syracuseStep 11432099 = 17148149) B17148149
theorem B4231435 : Blo 1319478 4231435 := bstep (se 1 (by rfl) ⟨3173576, by rfl⟩ : syracuseStep 4231435 = 6347153) B6347153
theorem B2969999 : Blo 1319478 2969999 := bstep (se 1 (by rfl) ⟨2227499, by rfl⟩ : syracuseStep 2969999 = 4454999) B4454999
theorem B4518287 : Blo 1319478 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B1880615 : Blo 1319478 1880615 := bstep (se 1 (by rfl) ⟨1410461, by rfl⟩ : syracuseStep 1880615 = 2820923) B2820923
theorem B4641419 : Blo 1319478 4641419 := bstep (se 1 (by rfl) ⟨3481064, by rfl⟩ : syracuseStep 4641419 = 6962129) B6962129
theorem B6689465 : Blo 1319478 6689465 := bstep (se 2 (by rfl) ⟨2508549, by rfl⟩ : syracuseStep 6689465 = 5017099) B5017099
theorem B2970323 : Blo 1319478 2970323 := bstep (se 1 (by rfl) ⟨2227742, by rfl⟩ : syracuseStep 2970323 = 4455485) B4455485
theorem B1979231 : Blo 1319478 1979231 := bstep (se 1 (by rfl) ⟨1484423, by rfl⟩ : syracuseStep 1979231 = 2968847) B2968847
theorem B1979243 : Blo 1319478 1979243 := bstep (se 1 (by rfl) ⟨1484432, by rfl⟩ : syracuseStep 1979243 = 2968865) B2968865
theorem B5010295 : Blo 1319478 5010295 := bstep (se 1 (by rfl) ⟨3757721, by rfl⟩ : syracuseStep 5010295 = 7515443) B7515443
theorem B6681527 : Blo 1319478 6681527 := bstep (se 1 (by rfl) ⟨5011145, by rfl⟩ : syracuseStep 6681527 = 10022291) B10022291
theorem B4453433 : Blo 1319478 4453433 := bstep (se 2 (by rfl) ⟨1670037, by rfl⟩ : syracuseStep 4453433 = 3340075) B3340075
theorem B1979471 : Blo 1319478 1979471 := bstep (se 1 (by rfl) ⟨1484603, by rfl⟩ : syracuseStep 1979471 = 2969207) B2969207
theorem B1586299 : Blo 1319478 1586299 := bstep (se 1 (by rfl) ⟨1189724, by rfl⟩ : syracuseStep 1586299 = 2379449) B2379449
theorem B1979591 : Blo 1319478 1979591 := bstep (se 1 (by rfl) ⟨1484693, by rfl⟩ : syracuseStep 1979591 = 2969387) B2969387
theorem B10171595 : Blo 1319478 10171595 := bstep (se 1 (by rfl) ⟨7628696, by rfl⟩ : syracuseStep 10171595 = 15257393) B15257393
theorem B1979753 : Blo 1319478 1979753 := bstep (se 2 (by rfl) ⟨742407, by rfl⟩ : syracuseStep 1979753 = 1484815) B1484815
theorem B15037811 : Blo 1319478 15037811 := bstep (se 1 (by rfl) ⟨11278358, by rfl⟩ : syracuseStep 15037811 = 22556717) B22556717
theorem B4453757 : Blo 1319478 4453757 := bstep (se 3 (by rfl) ⟨835079, by rfl⟩ : syracuseStep 4453757 = 1670159) B1670159
theorem B1979831 : Blo 1319478 1979831 := bstep (se 1 (by rfl) ⟨1484873, by rfl⟩ : syracuseStep 1979831 = 2969747) B2969747
theorem B1979867 : Blo 1319478 1979867 := bstep (se 1 (by rfl) ⟨1484900, by rfl⟩ : syracuseStep 1979867 = 2969801) B2969801
theorem B2971259 : Blo 1319478 2971259 := bstep (se 1 (by rfl) ⟨2228444, by rfl⟩ : syracuseStep 2971259 = 4456889) B4456889
theorem B4454027 : Blo 1319478 4454027 := bstep (se 1 (by rfl) ⟨3340520, by rfl⟩ : syracuseStep 4454027 = 6681041) B6681041
theorem B9524881 : Blo 1319478 9524881 := bstep (se 2 (by rfl) ⟨3571830, by rfl⟩ : syracuseStep 9524881 = 7143661) B7143661
theorem B1357511 : Blo 1319478 1357511 := bstep (se 1 (by rfl) ⟨1018133, by rfl⟩ : syracuseStep 1357511 = 2036267) B2036267
theorem B3340025 : Blo 1319478 3340025 := bstep (se 2 (by rfl) ⟨1252509, by rfl⟩ : syracuseStep 3340025 = 2505019) B2505019
theorem B2971385 : Blo 1319478 2971385 := bstep (se 2 (by rfl) ⟨1114269, by rfl⟩ : syracuseStep 2971385 = 2228539) B2228539
theorem B5011267 : Blo 1319478 5011267 := bstep (se 1 (by rfl) ⟨3758450, by rfl⟩ : syracuseStep 5011267 = 7516901) B7516901
theorem B3757985 : Blo 1319478 3757985 := bstep (se 2 (by rfl) ⟨1409244, by rfl⟩ : syracuseStep 3757985 = 2818489) B2818489
theorem B1980335 : Blo 1319478 1980335 := bstep (se 1 (by rfl) ⟨1485251, by rfl⟩ : syracuseStep 1980335 = 2970503) B2970503
theorem B1906615 : Blo 1319478 1906615 := bstep (se 1 (by rfl) ⟨1429961, by rfl⟩ : syracuseStep 1906615 = 2859923) B2859923
theorem B2971655 : Blo 1319478 2971655 := bstep (se 1 (by rfl) ⟨2228741, by rfl⟩ : syracuseStep 2971655 = 4457483) B4457483
theorem B1980425 : Blo 1319478 1980425 := bstep (se 2 (by rfl) ⟨742659, by rfl⟩ : syracuseStep 1980425 = 1485319) B1485319
theorem B1980455 : Blo 1319478 1980455 := bstep (se 1 (by rfl) ⟨1485341, by rfl⟩ : syracuseStep 1980455 = 2970683) B2970683
theorem B2971727 : Blo 1319478 2971727 := bstep (se 1 (by rfl) ⟨2228795, by rfl⟩ : syracuseStep 2971727 = 4457591) B4457591
theorem B5011571 : Blo 1319478 5011571 := bstep (se 1 (by rfl) ⟨3758678, by rfl⟩ : syracuseStep 5011571 = 7517357) B7517357
theorem B1980539 : Blo 1319478 1980539 := bstep (se 1 (by rfl) ⟨1485404, by rfl⟩ : syracuseStep 1980539 = 2970809) B2970809
theorem B5085337 : Blo 1319478 5085337 := bstep (se 2 (by rfl) ⟨1907001, by rfl⟩ : syracuseStep 5085337 = 3814003) B3814003
theorem B1980665 : Blo 1319478 1980665 := bstep (se 2 (by rfl) ⟨742749, by rfl⟩ : syracuseStep 1980665 = 1485499) B1485499
theorem B10033469 : Blo 1319478 10033469 := bstep (se 3 (by rfl) ⟨1881275, by rfl⟩ : syracuseStep 10033469 = 3762551) B3762551
theorem B7625047 : Blo 1319478 7625047 := bstep (se 1 (by rfl) ⟨5718785, by rfl⟩ : syracuseStep 7625047 = 11437571) B11437571
theorem B1980767 : Blo 1319478 1980767 := bstep (se 1 (by rfl) ⟨1485575, by rfl⟩ : syracuseStep 1980767 = 2971151) B2971151
theorem B6682985 : Blo 1319478 6682985 := bstep (se 2 (by rfl) ⟨2506119, by rfl⟩ : syracuseStep 6682985 = 5012239) B5012239
theorem B1980779 : Blo 1319478 1980779 := bstep (se 1 (by rfl) ⟨1485584, by rfl⟩ : syracuseStep 1980779 = 2971169) B2971169
theorem B3340673 : Blo 1319478 3340673 := bstep (se 2 (by rfl) ⟨1252752, by rfl⟩ : syracuseStep 3340673 = 2505505) B2505505
theorem B19036619 : Blo 1319478 19036619 := bstep (se 1 (by rfl) ⟨14277464, by rfl⟩ : syracuseStep 19036619 = 28554929) B28554929
theorem B2972123 : Blo 1319478 2972123 := bstep (se 1 (by rfl) ⟨2229092, by rfl⟩ : syracuseStep 2972123 = 4458185) B4458185
theorem B16308769 : Blo 1319478 16308769 := bstep (se 2 (by rfl) ⟨6115788, by rfl⟩ : syracuseStep 16308769 = 12231577) B12231577
theorem B4454945 : Blo 1319478 4454945 := bstep (se 2 (by rfl) ⟨1670604, by rfl⟩ : syracuseStep 4454945 = 3341209) B3341209
theorem B1784359 : Blo 1319478 1784359 := bstep (se 1 (by rfl) ⟨1338269, by rfl⟩ : syracuseStep 1784359 = 2676539) B2676539
theorem B5012027 : Blo 1319478 5012027 := bstep (se 1 (by rfl) ⟨3759020, by rfl⟩ : syracuseStep 5012027 = 7518041) B7518041
theorem B1981007 : Blo 1319478 1981007 := bstep (se 1 (by rfl) ⟨1485755, by rfl⟩ : syracuseStep 1981007 = 2971511) B2971511
theorem B2226811 : Blo 1319478 2226811 := bstep (se 1 (by rfl) ⟨1670108, by rfl⟩ : syracuseStep 2226811 = 3340217) B3340217
theorem B4823675 : Blo 1319478 4823675 := bstep (se 1 (by rfl) ⟨3617756, by rfl⟩ : syracuseStep 4823675 = 7235513) B7235513
theorem B1981127 : Blo 1319478 1981127 := bstep (se 1 (by rfl) ⟨1485845, by rfl⟩ : syracuseStep 1981127 = 2971691) B2971691
theorem B4455161 : Blo 1319478 4455161 := bstep (se 2 (by rfl) ⟨1670685, by rfl⟩ : syracuseStep 4455161 = 3341371) B3341371
theorem B1981289 : Blo 1319478 1981289 := bstep (se 2 (by rfl) ⟨742983, by rfl⟩ : syracuseStep 1981289 = 1485967) B1485967
theorem B11279249 : Blo 1319478 11279249 := bstep (se 2 (by rfl) ⟨4229718, by rfl⟩ : syracuseStep 11279249 = 8459437) B8459437
theorem B2972591 : Blo 1319478 2972591 := bstep (se 1 (by rfl) ⟨2229443, by rfl⟩ : syracuseStep 2972591 = 4458887) B4458887
theorem B57129907 : Blo 1319478 57129907 := bstep (se 1 (by rfl) ⟨42847430, by rfl⟩ : syracuseStep 57129907 = 85694861) B85694861
theorem B1784759 : Blo 1319478 1784759 := bstep (se 1 (by rfl) ⟨1338569, by rfl⟩ : syracuseStep 1784759 = 2677139) B2677139
theorem B1981367 : Blo 1319478 1981367 := bstep (se 1 (by rfl) ⟨1486025, by rfl⟩ : syracuseStep 1981367 = 2972051) B2972051
theorem B1981403 : Blo 1319478 1981403 := bstep (se 1 (by rfl) ⟨1486052, by rfl⟩ : syracuseStep 1981403 = 2972105) B2972105
theorem B4455431 : Blo 1319478 4455431 := bstep (se 1 (by rfl) ⟨3341573, by rfl⟩ : syracuseStep 4455431 = 6683147) B6683147
theorem B12688427 : Blo 1319478 12688427 := bstep (se 1 (by rfl) ⟨9516320, by rfl⟩ : syracuseStep 12688427 = 19032641) B19032641
theorem B22871119 : Blo 1319478 22871119 := bstep (se 1 (by rfl) ⟨17153339, by rfl⟩ : syracuseStep 22871119 = 34306679) B34306679
theorem B4455539 : Blo 1319478 4455539 := bstep (se 1 (by rfl) ⟨3341654, by rfl⟩ : syracuseStep 4455539 = 6683309) B6683309
theorem B3341483 : Blo 1319478 3341483 := bstep (se 1 (by rfl) ⟨2506112, by rfl⟩ : syracuseStep 3341483 = 5012225) B5012225
theorem B2972843 : Blo 1319478 2972843 := bstep (se 1 (by rfl) ⟨2229632, by rfl⟩ : syracuseStep 2972843 = 4459265) B4459265
theorem B10026179 : Blo 1319478 10026179 := bstep (se 1 (by rfl) ⟨7519634, by rfl⟩ : syracuseStep 10026179 = 15039269) B15039269
theorem B4455809 : Blo 1319478 4455809 := bstep (se 2 (by rfl) ⟨1670928, by rfl⟩ : syracuseStep 4455809 = 3341857) B3341857
theorem B2678177 : Blo 1319478 2678177 := bstep (se 2 (by rfl) ⟨1004316, by rfl⟩ : syracuseStep 2678177 = 2008633) B2008633
theorem B1981871 : Blo 1319478 1981871 := bstep (se 1 (by rfl) ⟨1486403, by rfl⟩ : syracuseStep 1981871 = 2972807) B2972807
theorem B2227675 : Blo 1319478 2227675 := bstep (se 1 (by rfl) ⟨1670756, by rfl⟩ : syracuseStep 2227675 = 3341513) B3341513
theorem B1981961 : Blo 1319478 1981961 := bstep (se 2 (by rfl) ⟨743235, by rfl⟩ : syracuseStep 1981961 = 1486471) B1486471
theorem B1981991 : Blo 1319478 1981991 := bstep (se 1 (by rfl) ⟨1486493, by rfl⟩ : syracuseStep 1981991 = 2972987) B2972987
theorem B1982075 : Blo 1319478 1982075 := bstep (se 1 (by rfl) ⟨1486556, by rfl⟩ : syracuseStep 1982075 = 2973113) B2973113
theorem B2506439 : Blo 1319478 2506439 := bstep (se 1 (by rfl) ⟨1879829, by rfl⟩ : syracuseStep 2506439 = 3759659) B3759659
theorem B4824791 : Blo 1319478 4824791 := bstep (se 1 (by rfl) ⟨3618593, by rfl⟩ : syracuseStep 4824791 = 7237187) B7237187
theorem B1982201 : Blo 1319478 1982201 := bstep (se 2 (by rfl) ⟨743325, by rfl⟩ : syracuseStep 1982201 = 1486651) B1486651
theorem B20316091 : Blo 1319478 20316091 := bstep (se 1 (by rfl) ⟨15237068, by rfl⟩ : syracuseStep 20316091 = 30474137) B30474137
theorem B1671131 : Blo 1319478 1671131 := bstep (se 1 (by rfl) ⟨1253348, by rfl⟩ : syracuseStep 1671131 = 2506697) B2506697
theorem B4456457 : Blo 1319478 4456457 := bstep (se 2 (by rfl) ⟨1671171, by rfl⟩ : syracuseStep 4456457 = 3342343) B3342343
theorem B9642035 : Blo 1319478 9642035 := bstep (se 1 (by rfl) ⟨7231526, by rfl⟩ : syracuseStep 9642035 = 14463053) B14463053
theorem B3342617 : Blo 1319478 3342617 := bstep (se 2 (by rfl) ⟨1253481, by rfl⟩ : syracuseStep 3342617 = 2506963) B2506963
theorem B1671455 : Blo 1319478 1671455 := bstep (se 1 (by rfl) ⟨1253591, by rfl⟩ : syracuseStep 1671455 = 2507183) B2507183
theorem B86794649 : Blo 1319478 86794649 := bstep (se 2 (by rfl) ⟨32547993, by rfl⟩ : syracuseStep 86794649 = 65095987) B65095987
theorem B2228647 : Blo 1319478 2228647 := bstep (se 1 (by rfl) ⟨1671485, by rfl⟩ : syracuseStep 2228647 = 3342971) B3342971
theorem B10166729 : Blo 1319478 10166729 := bstep (se 2 (by rfl) ⟨3812523, by rfl⟩ : syracuseStep 10166729 = 7625047) B7625047
theorem B27124253 : Blo 1319478 27124253 := bstep (se 3 (by rfl) ⟨5085797, by rfl⟩ : syracuseStep 27124253 = 10171595) B10171595
theorem B1319487 : Blo 1319478 1319487 := bstep (se 1 (by rfl) ⟨989615, by rfl⟩ : syracuseStep 1319487 = 1979231) B1979231
theorem B1409599 : Blo 1319478 1409599 := bstep (se 1 (by rfl) ⟨1057199, by rfl⟩ : syracuseStep 1409599 = 2114399) B2114399
theorem B1319495 : Blo 1319478 1319495 := bstep (se 1 (by rfl) ⟨989621, by rfl⟩ : syracuseStep 1319495 = 1979243) B1979243
theorem B2818633 : Blo 1319478 2818633 := bstep (se 2 (by rfl) ⟨1056987, by rfl⟩ : syracuseStep 2818633 = 2113975) B2113975
theorem B2228809 : Blo 1319478 2228809 := bstep (se 2 (by rfl) ⟨835803, by rfl⟩ : syracuseStep 2228809 = 1671607) B1671607
theorem B2228843 : Blo 1319478 2228843 := bstep (se 1 (by rfl) ⟨1671632, by rfl⟩ : syracuseStep 2228843 = 3343265) B3343265
theorem B5014169 : Blo 1319478 5014169 := bstep (se 2 (by rfl) ⟨1880313, by rfl⟩ : syracuseStep 5014169 = 3760627) B3760627
theorem B1319647 : Blo 1319478 1319647 := bstep (se 1 (by rfl) ⟨989735, by rfl⟩ : syracuseStep 1319647 = 1979471) B1979471
theorem B1319727 : Blo 1319478 1319727 := bstep (se 1 (by rfl) ⟨989795, by rfl⟩ : syracuseStep 1319727 = 1979591) B1979591
theorem B1319835 : Blo 1319478 1319835 := bstep (se 1 (by rfl) ⟨989876, by rfl⟩ : syracuseStep 1319835 = 1979753) B1979753
theorem B5080009 : Blo 1319478 5080009 := bstep (se 2 (by rfl) ⟨1905003, by rfl⟩ : syracuseStep 5080009 = 3810007) B3810007
theorem B1319887 : Blo 1319478 1319887 := bstep (se 1 (by rfl) ⟨989915, by rfl⟩ : syracuseStep 1319887 = 1979831) B1979831
theorem B1319911 : Blo 1319478 1319911 := bstep (se 1 (by rfl) ⟨989933, by rfl⟩ : syracuseStep 1319911 = 1979867) B1979867
theorem B12682277 : Blo 1319478 12682277 := bstep (se 4 (by rfl) ⟨1188963, by rfl⟩ : syracuseStep 12682277 = 2377927) B2377927
theorem B3343457 : Blo 1319478 3343457 := bstep (se 2 (by rfl) ⟨1253796, by rfl⟩ : syracuseStep 3343457 = 2507593) B2507593
theorem B1320223 : Blo 1319478 1320223 := bstep (se 1 (by rfl) ⟨990167, by rfl⟩ : syracuseStep 1320223 = 1980335) B1980335
theorem B1320283 : Blo 1319478 1320283 := bstep (se 1 (by rfl) ⟨990212, by rfl⟩ : syracuseStep 1320283 = 1980425) B1980425
theorem B1320303 : Blo 1319478 1320303 := bstep (se 1 (by rfl) ⟨990227, by rfl⟩ : syracuseStep 1320303 = 1980455) B1980455
theorem B12682619 : Blo 1319478 12682619 := bstep (se 1 (by rfl) ⟨9511964, by rfl⟩ : syracuseStep 12682619 = 19023929) B19023929
theorem B2508155 : Blo 1319478 2508155 := bstep (se 1 (by rfl) ⟨1881116, by rfl⟩ : syracuseStep 2508155 = 3762233) B3762233
theorem B1320359 : Blo 1319478 1320359 := bstep (se 1 (by rfl) ⟨990269, by rfl⟩ : syracuseStep 1320359 = 1980539) B1980539
theorem B5014973 : Blo 1319478 5014973 := bstep (se 3 (by rfl) ⟨940307, by rfl⟩ : syracuseStep 5014973 = 1880615) B1880615
theorem B2115065 : Blo 1319478 2115065 := bstep (se 2 (by rfl) ⟨793149, by rfl⟩ : syracuseStep 2115065 = 1586299) B1586299
theorem B1320443 : Blo 1319478 1320443 := bstep (se 1 (by rfl) ⟨990332, by rfl⟩ : syracuseStep 1320443 = 1980665) B1980665
theorem B1320511 : Blo 1319478 1320511 := bstep (se 1 (by rfl) ⟨990383, by rfl⟩ : syracuseStep 1320511 = 1980767) B1980767
theorem B1320519 : Blo 1319478 1320519 := bstep (se 1 (by rfl) ⟨990389, by rfl⟩ : syracuseStep 1320519 = 1980779) B1980779
theorem B2508383 : Blo 1319478 2508383 := bstep (se 1 (by rfl) ⟨1881287, by rfl⟩ : syracuseStep 2508383 = 3762575) B3762575
theorem B12691079 : Blo 1319478 12691079 := bstep (se 1 (by rfl) ⟨9518309, by rfl⟩ : syracuseStep 12691079 = 19036619) B19036619
theorem B1320671 : Blo 1319478 1320671 := bstep (se 1 (by rfl) ⟨990503, by rfl⟩ : syracuseStep 1320671 = 1981007) B1981007
theorem B1320751 : Blo 1319478 1320751 := bstep (se 1 (by rfl) ⟨990563, by rfl⟩ : syracuseStep 1320751 = 1981127) B1981127
theorem B1410863 : Blo 1319478 1410863 := bstep (se 1 (by rfl) ⟨1058147, by rfl⟩ : syracuseStep 1410863 = 2116295) B2116295
theorem B1320859 : Blo 1319478 1320859 := bstep (se 1 (by rfl) ⟨990644, by rfl⟩ : syracuseStep 1320859 = 1981289) B1981289
theorem B1320911 : Blo 1319478 1320911 := bstep (se 1 (by rfl) ⟨990683, by rfl⟩ : syracuseStep 1320911 = 1981367) B1981367
theorem B1320935 : Blo 1319478 1320935 := bstep (se 1 (by rfl) ⟨990701, by rfl⟩ : syracuseStep 1320935 = 1981403) B1981403
theorem B5638223 : Blo 1319478 5638223 := bstep (se 1 (by rfl) ⟨4228667, by rfl⟩ : syracuseStep 5638223 = 8457335) B8457335
theorem B12699841 : Blo 1319478 12699841 := bstep (se 2 (by rfl) ⟨4762440, by rfl⟩ : syracuseStep 12699841 = 9524881) B9524881
theorem B1321247 : Blo 1319478 1321247 := bstep (se 1 (by rfl) ⟨990935, by rfl⟩ : syracuseStep 1321247 = 1981871) B1981871
theorem B1321307 : Blo 1319478 1321307 := bstep (se 1 (by rfl) ⟨990980, by rfl⟩ : syracuseStep 1321307 = 1981961) B1981961
theorem B1321327 : Blo 1319478 1321327 := bstep (se 1 (by rfl) ⟨990995, by rfl⟩ : syracuseStep 1321327 = 1981991) B1981991
theorem B1321383 : Blo 1319478 1321383 := bstep (se 1 (by rfl) ⟨991037, by rfl⟩ : syracuseStep 1321383 = 1982075) B1982075
theorem B7522733 : Blo 1319478 7522733 := bstep (se 3 (by rfl) ⟨1410512, by rfl⟩ : syracuseStep 7522733 = 2821025) B2821025
theorem B1321467 : Blo 1319478 1321467 := bstep (se 1 (by rfl) ⟨991100, by rfl⟩ : syracuseStep 1321467 = 1982201) B1982201
theorem B3344915 : Blo 1319478 3344915 := bstep (se 1 (by rfl) ⟨2508686, by rfl⟩ : syracuseStep 3344915 = 5017373) B5017373
theorem B5016127 : Blo 1319478 5016127 := bstep (se 1 (by rfl) ⟨3762095, by rfl⟩ : syracuseStep 5016127 = 7524191) B7524191
theorem B2542153 : Blo 1319478 2542153 := bstep (se 2 (by rfl) ⟨953307, by rfl⟩ : syracuseStep 2542153 = 1906615) B1906615
theorem B11274875 : Blo 1319478 11274875 := bstep (se 1 (by rfl) ⟨8456156, by rfl⟩ : syracuseStep 11274875 = 16912313) B16912313
theorem B1485535 : Blo 1319478 1485535 := bstep (se 1 (by rfl) ⟨1114151, by rfl⟩ : syracuseStep 1485535 = 2228303) B2228303
theorem B7621399 : Blo 1319478 7621399 := bstep (se 1 (by rfl) ⟨5716049, by rfl⟩ : syracuseStep 7621399 = 11432099) B11432099
theorem B10709783 : Blo 1319478 10709783 := bstep (se 1 (by rfl) ⟨8032337, by rfl⟩ : syracuseStep 10709783 = 16064675) B16064675
theorem B11430827 : Blo 1319478 11430827 := bstep (se 1 (by rfl) ⟨8573120, by rfl⟩ : syracuseStep 11430827 = 17146241) B17146241
theorem B24087617 : Blo 1319478 24087617 := bstep (se 2 (by rfl) ⟨9032856, by rfl⟩ : syracuseStep 24087617 = 18065713) B18065713
theorem B4516987 : Blo 1319478 4516987 := bstep (se 1 (by rfl) ⟨3387740, by rfl⟩ : syracuseStep 4516987 = 6775481) B6775481
theorem B4459643 : Blo 1319478 4459643 := bstep (se 1 (by rfl) ⟨3344732, by rfl⟩ : syracuseStep 4459643 = 6689465) B6689465
theorem B3009755 : Blo 1319478 3009755 := bstep (se 1 (by rfl) ⟨2257316, by rfl⟩ : syracuseStep 3009755 = 4514633) B4514633
theorem B1486111 : Blo 1319478 1486111 := bstep (se 1 (by rfl) ⟨1114583, by rfl⟩ : syracuseStep 1486111 = 2229167) B2229167
theorem B2968955 : Blo 1319478 2968955 := bstep (se 1 (by rfl) ⟨2226716, by rfl⟩ : syracuseStep 2968955 = 4453433) B4453433
theorem B21745025 : Blo 1319478 21745025 := bstep (se 2 (by rfl) ⟨8154384, by rfl⟩ : syracuseStep 21745025 = 16308769) B16308769
theorem B2379145 : Blo 1319478 2379145 := bstep (se 2 (by rfl) ⟨892179, by rfl⟩ : syracuseStep 2379145 = 1784359) B1784359
theorem B4459913 : Blo 1319478 4459913 := bstep (se 2 (by rfl) ⟨1672467, by rfl⟩ : syracuseStep 4459913 = 3344935) B3344935
theorem B2969081 : Blo 1319478 2969081 := bstep (se 2 (by rfl) ⟨1113405, by rfl⟩ : syracuseStep 2969081 = 2226811) B2226811
theorem B1486399 : Blo 1319478 1486399 := bstep (se 1 (by rfl) ⟨1114799, by rfl⟩ : syracuseStep 1486399 = 2229599) B2229599
theorem B2969171 : Blo 1319478 2969171 := bstep (se 1 (by rfl) ⟨2226878, by rfl⟩ : syracuseStep 2969171 = 4453757) B4453757
theorem B2969351 : Blo 1319478 2969351 := bstep (se 1 (by rfl) ⟨2227013, by rfl⟩ : syracuseStep 2969351 = 4454027) B4454027
theorem B6680393 : Blo 1319478 6680393 := bstep (se 2 (by rfl) ⟨2505147, by rfl⟩ : syracuseStep 6680393 = 5010295) B5010295
theorem B12037997 : Blo 1319478 12037997 := bstep (se 3 (by rfl) ⟨2257124, by rfl⟩ : syracuseStep 12037997 = 4514249) B4514249
theorem B76173209 : Blo 1319478 76173209 := bstep (se 2 (by rfl) ⟨28564953, by rfl⟩ : syracuseStep 76173209 = 57129907) B57129907
theorem B30494825 : Blo 1319478 30494825 := bstep (se 2 (by rfl) ⟨11435559, by rfl⟩ : syracuseStep 30494825 = 22871119) B22871119
theorem B7942315 : Blo 1319478 7942315 := bstep (se 1 (by rfl) ⟨5956736, by rfl⟩ : syracuseStep 7942315 = 11913473) B11913473
theorem B6688979 : Blo 1319478 6688979 := bstep (se 1 (by rfl) ⟨5016734, by rfl⟩ : syracuseStep 6688979 = 10033469) B10033469
theorem B3010907 : Blo 1319478 3010907 := bstep (se 1 (by rfl) ⟨2258180, by rfl⟩ : syracuseStep 3010907 = 4516361) B4516361
theorem B2969963 : Blo 1319478 2969963 := bstep (se 1 (by rfl) ⟨2227472, by rfl⟩ : syracuseStep 2969963 = 4454945) B4454945
theorem B2970107 : Blo 1319478 2970107 := bstep (se 1 (by rfl) ⟨2227580, by rfl⟩ : syracuseStep 2970107 = 4455161) B4455161
theorem B2970233 : Blo 1319478 2970233 := bstep (se 2 (by rfl) ⟨1113837, by rfl⟩ : syracuseStep 2970233 = 2227675) B2227675
theorem B2970287 : Blo 1319478 2970287 := bstep (se 1 (by rfl) ⟨2227715, by rfl⟩ : syracuseStep 2970287 = 4455431) B4455431
theorem B8458951 : Blo 1319478 8458951 := bstep (se 1 (by rfl) ⟨6344213, by rfl⟩ : syracuseStep 8458951 = 12688427) B12688427
theorem B14480117 : Blo 1319478 14480117 := bstep (se 5 (by rfl) ⟨678755, by rfl⟩ : syracuseStep 14480117 = 1357511) B1357511
theorem B2970359 : Blo 1319478 2970359 := bstep (se 1 (by rfl) ⟨2227769, by rfl⟩ : syracuseStep 2970359 = 4455539) B4455539
theorem B1880911 : Blo 1319478 1880911 := bstep (se 1 (by rfl) ⟨1410683, by rfl⟩ : syracuseStep 1880911 = 2821367) B2821367
theorem B1979291 : Blo 1319478 1979291 := bstep (se 1 (by rfl) ⟨1484468, by rfl⟩ : syracuseStep 1979291 = 2968937) B2968937
theorem B2970539 : Blo 1319478 2970539 := bstep (se 1 (by rfl) ⟨2227904, by rfl⟩ : syracuseStep 2970539 = 4455809) B4455809
theorem B11277265 : Blo 1319478 11277265 := bstep (se 2 (by rfl) ⟨4228974, by rfl⟩ : syracuseStep 11277265 = 8457949) B8457949
theorem B6108151 : Blo 1319478 6108151 := bstep (se 1 (by rfl) ⟨4581113, by rfl⟩ : syracuseStep 6108151 = 9162227) B9162227
theorem B6681689 : Blo 1319478 6681689 := bstep (se 2 (by rfl) ⟨2505633, by rfl⟩ : syracuseStep 6681689 = 5011267) B5011267
theorem B3216527 : Blo 1319478 3216527 := bstep (se 1 (by rfl) ⟨2412395, by rfl⟩ : syracuseStep 3216527 = 4824791) B4824791
theorem B27088121 : Blo 1319478 27088121 := bstep (se 2 (by rfl) ⟨10158045, by rfl⟩ : syracuseStep 27088121 = 20316091) B20316091
theorem B12039425 : Blo 1319478 12039425 := bstep (se 2 (by rfl) ⟨4514784, by rfl⟩ : syracuseStep 12039425 = 9029569) B9029569
theorem B1979687 : Blo 1319478 1979687 := bstep (se 1 (by rfl) ⟨1484765, by rfl⟩ : syracuseStep 1979687 = 2969531) B2969531
theorem B1979771 : Blo 1319478 1979771 := bstep (se 1 (by rfl) ⟨1484828, by rfl⟩ : syracuseStep 1979771 = 2969657) B2969657
theorem B1881481 : Blo 1319478 1881481 := bstep (se 2 (by rfl) ⟨705555, by rfl⟩ : syracuseStep 1881481 = 1411111) B1411111
theorem B2971079 : Blo 1319478 2971079 := bstep (se 1 (by rfl) ⟨2228309, by rfl⟩ : syracuseStep 2971079 = 4456619) B4456619
theorem B1979897 : Blo 1319478 1979897 := bstep (se 2 (by rfl) ⟨742461, by rfl⟩ : syracuseStep 1979897 = 1484923) B1484923
theorem B6780449 : Blo 1319478 6780449 := bstep (se 2 (by rfl) ⟨2542668, by rfl⟩ : syracuseStep 6780449 = 5085337) B5085337
theorem B1979999 : Blo 1319478 1979999 := bstep (se 1 (by rfl) ⟨1484999, by rfl⟩ : syracuseStep 1979999 = 2969999) B2969999
theorem B3012191 : Blo 1319478 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B5641913 : Blo 1319478 5641913 := bstep (se 2 (by rfl) ⟨2115717, by rfl⟩ : syracuseStep 5641913 = 4231435) B4231435
theorem B2971439 : Blo 1319478 2971439 := bstep (se 1 (by rfl) ⟨2228579, by rfl⟩ : syracuseStep 2971439 = 4457159) B4457159
theorem B43439921 : Blo 1319478 43439921 := bstep (se 2 (by rfl) ⟨16289970, by rfl⟩ : syracuseStep 43439921 = 32579941) B32579941
theorem B1980215 : Blo 1319478 1980215 := bstep (se 1 (by rfl) ⟨1485161, by rfl⟩ : syracuseStep 1980215 = 2970323) B2970323
theorem B10032983 : Blo 1319478 10032983 := bstep (se 1 (by rfl) ⟨7524737, by rfl⟩ : syracuseStep 10032983 = 15049475) B15049475
theorem B4454351 : Blo 1319478 4454351 := bstep (se 1 (by rfl) ⟨3340763, by rfl⟩ : syracuseStep 4454351 = 6681527) B6681527
theorem B4233167 : Blo 1319478 4233167 := bstep (se 1 (by rfl) ⟨3174875, by rfl⟩ : syracuseStep 4233167 = 6349751) B6349751
theorem B1980521 : Blo 1319478 1980521 := bstep (se 2 (by rfl) ⟨742695, by rfl⟩ : syracuseStep 1980521 = 1485391) B1485391
theorem B10025207 : Blo 1319478 10025207 := bstep (se 1 (by rfl) ⟨7518905, by rfl⟩ : syracuseStep 10025207 = 15037811) B15037811
theorem B6773017 : Blo 1319478 6773017 := bstep (se 2 (by rfl) ⟨2539881, by rfl⟩ : syracuseStep 6773017 = 5079763) B5079763
theorem B2972015 : Blo 1319478 2972015 := bstep (se 1 (by rfl) ⟨2229011, by rfl⟩ : syracuseStep 2972015 = 4458023) B4458023
theorem B1980839 : Blo 1319478 1980839 := bstep (se 1 (by rfl) ⟨1485629, by rfl⟩ : syracuseStep 1980839 = 2971259) B2971259
theorem B2972087 : Blo 1319478 2972087 := bstep (se 1 (by rfl) ⟨2229065, by rfl⟩ : syracuseStep 2972087 = 4458131) B4458131
theorem B2226683 : Blo 1319478 2226683 := bstep (se 1 (by rfl) ⟨1670012, by rfl⟩ : syracuseStep 2226683 = 3340025) B3340025
theorem B1980923 : Blo 1319478 1980923 := bstep (se 1 (by rfl) ⟨1485692, by rfl⟩ : syracuseStep 1980923 = 2971385) B2971385
theorem B2972231 : Blo 1319478 2972231 := bstep (se 1 (by rfl) ⟨2229173, by rfl⟩ : syracuseStep 2972231 = 4458347) B4458347
theorem B2505323 : Blo 1319478 2505323 := bstep (se 1 (by rfl) ⟨1878992, by rfl⟩ : syracuseStep 2505323 = 3757985) B3757985
theorem B2972267 : Blo 1319478 2972267 := bstep (se 1 (by rfl) ⟨2229200, by rfl⟩ : syracuseStep 2972267 = 4458401) B4458401
theorem B51452533 : Blo 1319478 51452533 := bstep (se 5 (by rfl) ⟨2411837, by rfl⟩ : syracuseStep 51452533 = 4823675) B4823675
theorem B1981049 : Blo 1319478 1981049 := bstep (se 2 (by rfl) ⟨742893, by rfl⟩ : syracuseStep 1981049 = 1485787) B1485787
theorem B9034415 : Blo 1319478 9034415 := bstep (se 1 (by rfl) ⟨6775811, by rfl⟩ : syracuseStep 9034415 = 13551623) B13551623
theorem B1981103 : Blo 1319478 1981103 := bstep (se 1 (by rfl) ⟨1485827, by rfl⟩ : syracuseStep 1981103 = 2971655) B2971655
theorem B1981151 : Blo 1319478 1981151 := bstep (se 1 (by rfl) ⟨1485863, by rfl⟩ : syracuseStep 1981151 = 2971727) B2971727
theorem B3341047 : Blo 1319478 3341047 := bstep (se 1 (by rfl) ⟨2505785, by rfl⟩ : syracuseStep 3341047 = 5011571) B5011571
theorem B4455323 : Blo 1319478 4455323 := bstep (se 1 (by rfl) ⟨3341492, by rfl⟩ : syracuseStep 4455323 = 6682985) B6682985
theorem B2227115 : Blo 1319478 2227115 := bstep (se 1 (by rfl) ⟨1670336, by rfl⟩ : syracuseStep 2227115 = 3340673) B3340673
theorem B5643179 : Blo 1319478 5643179 := bstep (se 1 (by rfl) ⟨4232384, by rfl⟩ : syracuseStep 5643179 = 8464769) B8464769
theorem B1981415 : Blo 1319478 1981415 := bstep (se 1 (by rfl) ⟨1486061, by rfl⟩ : syracuseStep 1981415 = 2972123) B2972123
theorem B2972663 : Blo 1319478 2972663 := bstep (se 1 (by rfl) ⟨2229497, by rfl⟩ : syracuseStep 2972663 = 4458995) B4458995
theorem B12377117 : Blo 1319478 12377117 := bstep (se 3 (by rfl) ⟨2320709, by rfl⟩ : syracuseStep 12377117 = 4641419) B4641419
theorem B3341351 : Blo 1319478 3341351 := bstep (se 1 (by rfl) ⟨2506013, by rfl⟩ : syracuseStep 3341351 = 5012027) B5012027
theorem B11443319 : Blo 1319478 11443319 := bstep (se 1 (by rfl) ⟨8582489, by rfl⟩ : syracuseStep 11443319 = 17164979) B17164979
theorem B8461435 : Blo 1319478 8461435 := bstep (se 1 (by rfl) ⟨6346076, by rfl⟩ : syracuseStep 8461435 = 12692153) B12692153
theorem B1981673 : Blo 1319478 1981673 := bstep (se 2 (by rfl) ⟨743127, by rfl⟩ : syracuseStep 1981673 = 1486255) B1486255
theorem B7519499 : Blo 1319478 7519499 := bstep (se 1 (by rfl) ⟨5639624, by rfl⟩ : syracuseStep 7519499 = 11279249) B11279249
theorem B1981727 : Blo 1319478 1981727 := bstep (se 1 (by rfl) ⟨1486295, by rfl⟩ : syracuseStep 1981727 = 2972591) B2972591
theorem B2973023 : Blo 1319478 2973023 := bstep (se 1 (by rfl) ⟨2229767, by rfl⟩ : syracuseStep 2973023 = 4459535) B4459535
theorem B2678113 : Blo 1319478 2678113 := bstep (se 2 (by rfl) ⟨1004292, by rfl⟩ : syracuseStep 2678113 = 2008585) B2008585
theorem B2227655 : Blo 1319478 2227655 := bstep (se 1 (by rfl) ⟨1670741, by rfl⟩ : syracuseStep 2227655 = 3341483) B3341483
theorem B1981895 : Blo 1319478 1981895 := bstep (se 1 (by rfl) ⟨1486421, by rfl⟩ : syracuseStep 1981895 = 2972843) B2972843
theorem B6684119 : Blo 1319478 6684119 := bstep (se 1 (by rfl) ⟨5013089, by rfl⟩ : syracuseStep 6684119 = 10026179) B10026179
theorem B7134713 : Blo 1319478 7134713 := bstep (se 2 (by rfl) ⟨2675517, by rfl⟩ : syracuseStep 7134713 = 5351035) B5351035
theorem B6348383 : Blo 1319478 6348383 := bstep (se 1 (by rfl) ⟨4761287, by rfl⟩ : syracuseStep 6348383 = 9522575) B9522575
theorem B1785451 : Blo 1319478 1785451 := bstep (se 1 (by rfl) ⟨1339088, by rfl⟩ : syracuseStep 1785451 = 2678177) B2678177
theorem B1670959 : Blo 1319478 1670959 := bstep (se 1 (by rfl) ⟨1253219, by rfl⟩ : syracuseStep 1670959 = 2506439) B2506439
theorem B4759357 : Blo 1319478 4759357 := bstep (se 3 (by rfl) ⟨892379, by rfl⟩ : syracuseStep 4759357 = 1784759) B1784759
theorem B4456349 : Blo 1319478 4456349 := bstep (se 3 (by rfl) ⟨835565, by rfl⟩ : syracuseStep 4456349 = 1671131) B1671131
theorem B2228411 : Blo 1319478 2228411 := bstep (se 1 (by rfl) ⟨1671308, by rfl⟩ : syracuseStep 2228411 = 3342617) B3342617
theorem B2007271 : Blo 1319478 2007271 := bstep (se 1 (by rfl) ⟨1505453, by rfl⟩ : syracuseStep 2007271 = 3010907) B3010907
theorem B16933121 : Blo 1319478 16933121 := bstep (se 2 (by rfl) ⟨6349920, by rfl⟩ : syracuseStep 16933121 = 12699841) B12699841
theorem B3342779 : Blo 1319478 3342779 := bstep (se 1 (by rfl) ⟨2507084, by rfl⟩ : syracuseStep 3342779 = 5014169) B5014169
theorem B1319527 : Blo 1319478 1319527 := bstep (se 1 (by rfl) ⟨989645, by rfl⟩ : syracuseStep 1319527 = 1979291) B1979291
theorem B8454851 : Blo 1319478 8454851 := bstep (se 1 (by rfl) ⟨6341138, by rfl⟩ : syracuseStep 8454851 = 12682277) B12682277
theorem B2228971 : Blo 1319478 2228971 := bstep (se 1 (by rfl) ⟨1671728, by rfl⟩ : syracuseStep 2228971 = 3343457) B3343457
theorem B4457213 : Blo 1319478 4457213 := bstep (se 3 (by rfl) ⟨835727, by rfl⟩ : syracuseStep 4457213 = 1671455) B1671455
theorem B1319791 : Blo 1319478 1319791 := bstep (se 1 (by rfl) ⟨989843, by rfl⟩ : syracuseStep 1319791 = 1979687) B1979687
theorem B8455079 : Blo 1319478 8455079 := bstep (se 1 (by rfl) ⟨6341309, by rfl⟩ : syracuseStep 8455079 = 12682619) B12682619
theorem B1319847 : Blo 1319478 1319847 := bstep (se 1 (by rfl) ⟨989885, by rfl⟩ : syracuseStep 1319847 = 1979771) B1979771
theorem B1672103 : Blo 1319478 1672103 := bstep (se 1 (by rfl) ⟨1254077, by rfl⟩ : syracuseStep 1672103 = 2508155) B2508155
theorem B3343315 : Blo 1319478 3343315 := bstep (se 1 (by rfl) ⟨2507486, by rfl⟩ : syracuseStep 3343315 = 5014973) B5014973
theorem B32130037 : Blo 1319478 32130037 := bstep (se 5 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 32130037 = 3012191) B3012191
theorem B1319931 : Blo 1319478 1319931 := bstep (se 1 (by rfl) ⟨989948, by rfl⟩ : syracuseStep 1319931 = 1979897) B1979897
theorem B1410043 : Blo 1319478 1410043 := bstep (se 1 (by rfl) ⟨1057532, by rfl⟩ : syracuseStep 1410043 = 2115065) B2115065
theorem B1319999 : Blo 1319478 1319999 := bstep (se 1 (by rfl) ⟨989999, by rfl⟩ : syracuseStep 1319999 = 1979999) B1979999
theorem B1672255 : Blo 1319478 1672255 := bstep (se 1 (by rfl) ⟨1254191, by rfl⟩ : syracuseStep 1672255 = 2508383) B2508383
theorem B28959947 : Blo 1319478 28959947 := bstep (se 1 (by rfl) ⟨21719960, by rfl⟩ : syracuseStep 28959947 = 43439921) B43439921
theorem B1320143 : Blo 1319478 1320143 := bstep (se 1 (by rfl) ⟨990107, by rfl⟩ : syracuseStep 1320143 = 1980215) B1980215
theorem B8144201 : Blo 1319478 8144201 := bstep (se 2 (by rfl) ⟨3054075, by rfl⟩ : syracuseStep 8144201 = 6108151) B6108151
theorem B1320347 : Blo 1319478 1320347 := bstep (se 1 (by rfl) ⟨990260, by rfl⟩ : syracuseStep 1320347 = 1980521) B1980521
theorem B6022649 : Blo 1319478 6022649 := bstep (se 2 (by rfl) ⟨2258493, by rfl⟩ : syracuseStep 6022649 = 4516987) B4516987
theorem B11281913 : Blo 1319478 11281913 := bstep (se 2 (by rfl) ⟨4230717, by rfl⟩ : syracuseStep 11281913 = 8461435) B8461435
theorem B1320559 : Blo 1319478 1320559 := bstep (se 1 (by rfl) ⟨990419, by rfl⟩ : syracuseStep 1320559 = 1980839) B1980839
theorem B5015155 : Blo 1319478 5015155 := bstep (se 1 (by rfl) ⟨3761366, by rfl⟩ : syracuseStep 5015155 = 7522733) B7522733
theorem B1484455 : Blo 1319478 1484455 := bstep (se 1 (by rfl) ⟨1113341, by rfl⟩ : syracuseStep 1484455 = 2226683) B2226683
theorem B1320615 : Blo 1319478 1320615 := bstep (se 1 (by rfl) ⟨990461, by rfl⟩ : syracuseStep 1320615 = 1980923) B1980923
theorem B2229943 : Blo 1319478 2229943 := bstep (se 1 (by rfl) ⟨1672457, by rfl⟩ : syracuseStep 2229943 = 3344915) B3344915
theorem B1320699 : Blo 1319478 1320699 := bstep (se 1 (by rfl) ⟨990524, by rfl⟩ : syracuseStep 1320699 = 1981049) B1981049
theorem B6022943 : Blo 1319478 6022943 := bstep (se 1 (by rfl) ⟨4517207, by rfl⟩ : syracuseStep 6022943 = 9034415) B9034415
theorem B1320735 : Blo 1319478 1320735 := bstep (se 1 (by rfl) ⟨990551, by rfl⟩ : syracuseStep 1320735 = 1981103) B1981103
theorem B1320767 : Blo 1319478 1320767 := bstep (se 1 (by rfl) ⟨990575, by rfl⟩ : syracuseStep 1320767 = 1981151) B1981151
theorem B3172193 : Blo 1319478 3172193 := bstep (se 2 (by rfl) ⟨1189572, by rfl⟩ : syracuseStep 3172193 = 2379145) B2379145
theorem B2508641 : Blo 1319478 2508641 := bstep (se 2 (by rfl) ⟨940740, by rfl⟩ : syracuseStep 2508641 = 1881481) B1881481
theorem B1484743 : Blo 1319478 1484743 := bstep (se 1 (by rfl) ⟨1113557, by rfl⟩ : syracuseStep 1484743 = 2227115) B2227115
theorem B7620551 : Blo 1319478 7620551 := bstep (se 1 (by rfl) ⟨5715413, by rfl⟩ : syracuseStep 7620551 = 11430827) B11430827
theorem B3762119 : Blo 1319478 3762119 := bstep (se 1 (by rfl) ⟨2821589, by rfl⟩ : syracuseStep 3762119 = 5643179) B5643179
theorem B1320943 : Blo 1319478 1320943 := bstep (se 1 (by rfl) ⟨990707, by rfl⟩ : syracuseStep 1320943 = 1981415) B1981415
theorem B8251411 : Blo 1319478 8251411 := bstep (se 1 (by rfl) ⟨6188558, by rfl⟩ : syracuseStep 8251411 = 12377117) B12377117
theorem B16058411 : Blo 1319478 16058411 := bstep (se 1 (by rfl) ⟨12043808, by rfl⟩ : syracuseStep 16058411 = 24087617) B24087617
theorem B7628879 : Blo 1319478 7628879 := bstep (se 1 (by rfl) ⟨5721659, by rfl⟩ : syracuseStep 7628879 = 11443319) B11443319
theorem B3762301 : Blo 1319478 3762301 := bstep (se 3 (by rfl) ⟨705431, by rfl⟩ : syracuseStep 3762301 = 1410863) B1410863
theorem B1321115 : Blo 1319478 1321115 := bstep (se 1 (by rfl) ⟨990836, by rfl⟩ : syracuseStep 1321115 = 1981673) B1981673
theorem B1321151 : Blo 1319478 1321151 := bstep (se 1 (by rfl) ⟨990863, by rfl⟩ : syracuseStep 1321151 = 1981727) B1981727
theorem B1485103 : Blo 1319478 1485103 := bstep (se 1 (by rfl) ⟨1113827, by rfl⟩ : syracuseStep 1485103 = 2227655) B2227655
theorem B1321263 : Blo 1319478 1321263 := bstep (se 1 (by rfl) ⟨990947, by rfl⟩ : syracuseStep 1321263 = 1981895) B1981895
theorem B4459319 : Blo 1319478 4459319 := bstep (se 1 (by rfl) ⟨3344489, by rfl⟩ : syracuseStep 4459319 = 6688979) B6688979
theorem B57863099 : Blo 1319478 57863099 := bstep (se 1 (by rfl) ⟨43397324, by rfl⟩ : syracuseStep 57863099 = 86794649) B86794649
theorem B18082835 : Blo 1319478 18082835 := bstep (se 1 (by rfl) ⟨13562126, by rfl⟩ : syracuseStep 18082835 = 27124253) B27124253
theorem B9030689 : Blo 1319478 9030689 := bstep (se 2 (by rfl) ⟨3386508, by rfl⟩ : syracuseStep 9030689 = 6773017) B6773017
theorem B1485895 : Blo 1319478 1485895 := bstep (se 1 (by rfl) ⟨1114421, by rfl⟩ : syracuseStep 1485895 = 2228843) B2228843
theorem B9653411 : Blo 1319478 9653411 := bstep (se 1 (by rfl) ⟨7240058, by rfl⟩ : syracuseStep 9653411 = 14480117) B14480117
theorem B1879465 : Blo 1319478 1879465 := bstep (se 2 (by rfl) ⟨704799, by rfl⟩ : syracuseStep 1879465 = 1409599) B1409599
theorem B6688169 : Blo 1319478 6688169 := bstep (se 2 (by rfl) ⟨2508063, by rfl⟩ : syracuseStep 6688169 = 5016127) B5016127
theorem B68603377 : Blo 1319478 68603377 := bstep (se 2 (by rfl) ⟨25726266, by rfl⟩ : syracuseStep 68603377 = 51452533) B51452533
theorem B18058747 : Blo 1319478 18058747 := bstep (se 1 (by rfl) ⟨13544060, by rfl⟩ : syracuseStep 18058747 = 27088121) B27088121
theorem B10161865 : Blo 1319478 10161865 := bstep (se 2 (by rfl) ⟨3810699, by rfl⟩ : syracuseStep 10161865 = 7621399) B7621399
theorem B27111277 : Blo 1319478 27111277 := bstep (se 3 (by rfl) ⟨5083364, by rfl⟩ : syracuseStep 27111277 = 10166729) B10166729
theorem B6688655 : Blo 1319478 6688655 := bstep (se 1 (by rfl) ⟨5016491, by rfl⟩ : syracuseStep 6688655 = 10032983) B10032983
theorem B15036353 : Blo 1319478 15036353 := bstep (se 2 (by rfl) ⟨5638632, by rfl⟩ : syracuseStep 15036353 = 11277265) B11277265
theorem B2969567 : Blo 1319478 2969567 := bstep (se 1 (by rfl) ⟨2227175, by rfl⟩ : syracuseStep 2969567 = 4454351) B4454351
theorem B2822111 : Blo 1319478 2822111 := bstep (se 1 (by rfl) ⟨2116583, by rfl⟩ : syracuseStep 2822111 = 4233167) B4233167
theorem B10031525 : Blo 1319478 10031525 := bstep (se 4 (by rfl) ⟨940455, by rfl⟩ : syracuseStep 10031525 = 1880911) B1880911
theorem B7516583 : Blo 1319478 7516583 := bstep (se 1 (by rfl) ⟨5637437, by rfl⟩ : syracuseStep 7516583 = 11274875) B11274875
theorem B15045101 : Blo 1319478 15045101 := bstep (se 3 (by rfl) ⟨2820956, by rfl⟩ : syracuseStep 15045101 = 5641913) B5641913
theorem B7139855 : Blo 1319478 7139855 := bstep (se 1 (by rfl) ⟨5354891, by rfl⟩ : syracuseStep 7139855 = 10709783) B10709783
theorem B2970215 : Blo 1319478 2970215 := bstep (se 1 (by rfl) ⟨2227661, by rfl⟩ : syracuseStep 2970215 = 4455323) B4455323
theorem B2380601 : Blo 1319478 2380601 := bstep (se 2 (by rfl) ⟨892725, by rfl⟩ : syracuseStep 2380601 = 1785451) B1785451
theorem B1979303 : Blo 1319478 1979303 := bstep (se 1 (by rfl) ⟨1484477, by rfl⟩ : syracuseStep 1979303 = 2968955) B2968955
theorem B14496683 : Blo 1319478 14496683 := bstep (se 1 (by rfl) ⟨10872512, by rfl⟩ : syracuseStep 14496683 = 21745025) B21745025
theorem B1979387 : Blo 1319478 1979387 := bstep (se 1 (by rfl) ⟨1484540, by rfl⟩ : syracuseStep 1979387 = 2969081) B2969081
theorem B4756475 : Blo 1319478 4756475 := bstep (se 1 (by rfl) ⟨3567356, by rfl⟩ : syracuseStep 4756475 = 7134713) B7134713
theorem B1979447 : Blo 1319478 1979447 := bstep (se 1 (by rfl) ⟨1484585, by rfl⟩ : syracuseStep 1979447 = 2969171) B2969171
theorem B4232255 : Blo 1319478 4232255 := bstep (se 1 (by rfl) ⟨3174191, by rfl⟩ : syracuseStep 4232255 = 6348383) B6348383
theorem B6345809 : Blo 1319478 6345809 := bstep (se 2 (by rfl) ⟨2379678, by rfl⟩ : syracuseStep 6345809 = 4759357) B4759357
theorem B1979567 : Blo 1319478 1979567 := bstep (se 1 (by rfl) ⟨1484675, by rfl⟩ : syracuseStep 1979567 = 2969351) B2969351
theorem B4453595 : Blo 1319478 4453595 := bstep (se 1 (by rfl) ⟨3340196, by rfl⟩ : syracuseStep 4453595 = 6680393) B6680393
theorem B8025331 : Blo 1319478 8025331 := bstep (se 1 (by rfl) ⟨6018998, by rfl⟩ : syracuseStep 8025331 = 12037997) B12037997
theorem B2970899 : Blo 1319478 2970899 := bstep (se 1 (by rfl) ⟨2228174, by rfl⟩ : syracuseStep 2970899 = 4456349) B4456349
theorem B2970971 : Blo 1319478 2970971 := bstep (se 1 (by rfl) ⟨2228228, by rfl⟩ : syracuseStep 2970971 = 4456457) B4456457
theorem B20329883 : Blo 1319478 20329883 := bstep (se 1 (by rfl) ⟨15247412, by rfl⟩ : syracuseStep 20329883 = 30494825) B30494825
theorem B25712093 : Blo 1319478 25712093 := bstep (se 3 (by rfl) ⟨4821017, by rfl⟩ : syracuseStep 25712093 = 9642035) B9642035
theorem B10589753 : Blo 1319478 10589753 := bstep (se 2 (by rfl) ⟨3971157, by rfl⟩ : syracuseStep 10589753 = 7942315) B7942315
theorem B1979975 : Blo 1319478 1979975 := bstep (se 1 (by rfl) ⟨1484981, by rfl⟩ : syracuseStep 1979975 = 2969963) B2969963
theorem B1980071 : Blo 1319478 1980071 := bstep (se 1 (by rfl) ⟨1485053, by rfl⟩ : syracuseStep 1980071 = 2970107) B2970107
theorem B1980155 : Blo 1319478 1980155 := bstep (se 1 (by rfl) ⟨1485116, by rfl⟩ : syracuseStep 1980155 = 2970233) B2970233
theorem B1980191 : Blo 1319478 1980191 := bstep (se 1 (by rfl) ⟨1485143, by rfl⟩ : syracuseStep 1980191 = 2970287) B2970287
theorem B1980239 : Blo 1319478 1980239 := bstep (se 1 (by rfl) ⟨1485179, by rfl⟩ : syracuseStep 1980239 = 2970359) B2970359
theorem B2971529 : Blo 1319478 2971529 := bstep (se 2 (by rfl) ⟨1114323, by rfl⟩ : syracuseStep 2971529 = 2228647) B2228647
theorem B8026013 : Blo 1319478 8026013 := bstep (se 3 (by rfl) ⟨1504877, by rfl⟩ : syracuseStep 8026013 = 3009755) B3009755
theorem B1980359 : Blo 1319478 1980359 := bstep (se 1 (by rfl) ⟨1485269, by rfl⟩ : syracuseStep 1980359 = 2970539) B2970539
theorem B4454459 : Blo 1319478 4454459 := bstep (se 1 (by rfl) ⟨3340844, by rfl⟩ : syracuseStep 4454459 = 6681689) B6681689
theorem B2144351 : Blo 1319478 2144351 := bstep (se 1 (by rfl) ⟨1608263, by rfl⟩ : syracuseStep 2144351 = 3216527) B3216527
theorem B3758177 : Blo 1319478 3758177 := bstep (se 2 (by rfl) ⟨1409316, by rfl⟩ : syracuseStep 3758177 = 2818633) B2818633
theorem B2971745 : Blo 1319478 2971745 := bstep (se 2 (by rfl) ⟨1114404, by rfl⟩ : syracuseStep 2971745 = 2228809) B2228809
theorem B3389537 : Blo 1319478 3389537 := bstep (se 2 (by rfl) ⟨1271076, by rfl⟩ : syracuseStep 3389537 = 2542153) B2542153
theorem B8026283 : Blo 1319478 8026283 := bstep (se 1 (by rfl) ⟨6019712, by rfl⟩ : syracuseStep 8026283 = 12039425) B12039425
theorem B11278601 : Blo 1319478 11278601 := bstep (se 2 (by rfl) ⟨4229475, by rfl⟩ : syracuseStep 11278601 = 8458951) B8458951
theorem B1980713 : Blo 1319478 1980713 := bstep (se 2 (by rfl) ⟨742767, by rfl⟩ : syracuseStep 1980713 = 1485535) B1485535
theorem B1980719 : Blo 1319478 1980719 := bstep (se 1 (by rfl) ⟨1485539, by rfl⟩ : syracuseStep 1980719 = 2971079) B2971079
theorem B4454729 : Blo 1319478 4454729 := bstep (se 2 (by rfl) ⟨1670523, by rfl⟩ : syracuseStep 4454729 = 3341047) B3341047
theorem B4520299 : Blo 1319478 4520299 := bstep (se 1 (by rfl) ⟨3390224, by rfl⟩ : syracuseStep 4520299 = 6780449) B6780449
theorem B8460719 : Blo 1319478 8460719 := bstep (se 1 (by rfl) ⟨6345539, by rfl⟩ : syracuseStep 8460719 = 12691079) B12691079
theorem B1980959 : Blo 1319478 1980959 := bstep (se 1 (by rfl) ⟨1485719, by rfl⟩ : syracuseStep 1980959 = 2971439) B2971439
theorem B6773345 : Blo 1319478 6773345 := bstep (se 2 (by rfl) ⟨2540004, by rfl⟩ : syracuseStep 6773345 = 5080009) B5080009
theorem B3758815 : Blo 1319478 3758815 := bstep (se 1 (by rfl) ⟨2819111, by rfl⟩ : syracuseStep 3758815 = 5638223) B5638223
theorem B6683471 : Blo 1319478 6683471 := bstep (se 1 (by rfl) ⟨5012603, by rfl⟩ : syracuseStep 6683471 = 10025207) B10025207
theorem B1981343 : Blo 1319478 1981343 := bstep (se 1 (by rfl) ⟨1486007, by rfl⟩ : syracuseStep 1981343 = 2972015) B2972015
theorem B1981391 : Blo 1319478 1981391 := bstep (se 1 (by rfl) ⟨1486043, by rfl⟩ : syracuseStep 1981391 = 2972087) B2972087
theorem B1981481 : Blo 1319478 1981481 := bstep (se 2 (by rfl) ⟨743055, by rfl⟩ : syracuseStep 1981481 = 1486111) B1486111
theorem B1981487 : Blo 1319478 1981487 := bstep (se 1 (by rfl) ⟨1486115, by rfl⟩ : syracuseStep 1981487 = 2972231) B2972231
theorem B1670215 : Blo 1319478 1670215 := bstep (se 1 (by rfl) ⟨1252661, by rfl⟩ : syracuseStep 1670215 = 2505323) B2505323
theorem B1981511 : Blo 1319478 1981511 := bstep (se 1 (by rfl) ⟨1486133, by rfl⟩ : syracuseStep 1981511 = 2972267) B2972267
theorem B3570817 : Blo 1319478 3570817 := bstep (se 2 (by rfl) ⟨1339056, by rfl⟩ : syracuseStep 3570817 = 2678113) B2678113
theorem B1981775 : Blo 1319478 1981775 := bstep (se 1 (by rfl) ⟨1486331, by rfl⟩ : syracuseStep 1981775 = 2972663) B2972663
theorem B2227567 : Blo 1319478 2227567 := bstep (se 1 (by rfl) ⟨1670675, by rfl⟩ : syracuseStep 2227567 = 3341351) B3341351
theorem B2973095 : Blo 1319478 2973095 := bstep (se 1 (by rfl) ⟨2229821, by rfl⟩ : syracuseStep 2973095 = 4459643) B4459643
theorem B1981865 : Blo 1319478 1981865 := bstep (se 2 (by rfl) ⟨743199, by rfl⟩ : syracuseStep 1981865 = 1486399) B1486399
theorem B5012999 : Blo 1319478 5012999 := bstep (se 1 (by rfl) ⟨3759749, by rfl⟩ : syracuseStep 5012999 = 7519499) B7519499
theorem B1982015 : Blo 1319478 1982015 := bstep (se 1 (by rfl) ⟨1486511, by rfl⟩ : syracuseStep 1982015 = 2973023) B2973023
theorem B2973275 : Blo 1319478 2973275 := bstep (se 1 (by rfl) ⟨2229956, by rfl⟩ : syracuseStep 2973275 = 4459913) B4459913
theorem B4456079 : Blo 1319478 4456079 := bstep (se 1 (by rfl) ⟨3342059, by rfl⟩ : syracuseStep 4456079 = 6684119) B6684119
theorem B2227945 : Blo 1319478 2227945 := bstep (se 2 (by rfl) ⟨835479, by rfl⟩ : syracuseStep 2227945 = 1670959) B1670959
theorem B50782139 : Blo 1319478 50782139 := bstep (se 1 (by rfl) ⟨38086604, by rfl⟩ : syracuseStep 50782139 = 76173209) B76173209
theorem B11001881 : Blo 1319478 11001881 := bstep (se 2 (by rfl) ⟨4125705, by rfl⟩ : syracuseStep 11001881 = 8251411) B8251411
theorem B11288747 : Blo 1319478 11288747 := bstep (se 1 (by rfl) ⟨8466560, by rfl⟩ : syracuseStep 11288747 = 16933121) B16933121
theorem B5718269 : Blo 1319478 5718269 := bstep (se 3 (by rfl) ⟨1072175, by rfl⟩ : syracuseStep 5718269 = 2144351) B2144351
theorem B2228519 : Blo 1319478 2228519 := bstep (se 1 (by rfl) ⟨1671389, by rfl⟩ : syracuseStep 2228519 = 3342779) B3342779
theorem B4759903 : Blo 1319478 4759903 := bstep (se 1 (by rfl) ⟨3569927, by rfl⟩ : syracuseStep 4759903 = 7139855) B7139855
theorem B5636567 : Blo 1319478 5636567 := bstep (se 1 (by rfl) ⟨4227425, by rfl⟩ : syracuseStep 5636567 = 8454851) B8454851
theorem B1319535 : Blo 1319478 1319535 := bstep (se 1 (by rfl) ⟨989651, by rfl⟩ : syracuseStep 1319535 = 1979303) B1979303
theorem B5636719 : Blo 1319478 5636719 := bstep (se 1 (by rfl) ⟨4227539, by rfl⟩ : syracuseStep 5636719 = 8455079) B8455079
theorem B1319591 : Blo 1319478 1319591 := bstep (se 1 (by rfl) ⟨989693, by rfl⟩ : syracuseStep 1319591 = 1979387) B1979387
theorem B3170983 : Blo 1319478 3170983 := bstep (se 1 (by rfl) ⟨2378237, by rfl⟩ : syracuseStep 3170983 = 4756475) B4756475
theorem B1319631 : Blo 1319478 1319631 := bstep (se 1 (by rfl) ⟨989723, by rfl⟩ : syracuseStep 1319631 = 1979447) B1979447
theorem B1319711 : Blo 1319478 1319711 := bstep (se 1 (by rfl) ⟨989783, by rfl⟩ : syracuseStep 1319711 = 1979567) B1979567
theorem B4015099 : Blo 1319478 4015099 := bstep (se 1 (by rfl) ⟨3011324, by rfl⟩ : syracuseStep 4015099 = 6022649) B6022649
theorem B7521275 : Blo 1319478 7521275 := bstep (se 1 (by rfl) ⟨5640956, by rfl⟩ : syracuseStep 7521275 = 11281913) B11281913
theorem B1319983 : Blo 1319478 1319983 := bstep (se 1 (by rfl) ⟨989987, by rfl⟩ : syracuseStep 1319983 = 1979975) B1979975
theorem B1320047 : Blo 1319478 1320047 := bstep (se 1 (by rfl) ⟨990035, by rfl⟩ : syracuseStep 1320047 = 1980071) B1980071
theorem B1320103 : Blo 1319478 1320103 := bstep (se 1 (by rfl) ⟨990077, by rfl⟩ : syracuseStep 1320103 = 1980155) B1980155
theorem B1320127 : Blo 1319478 1320127 := bstep (se 1 (by rfl) ⟨990095, by rfl⟩ : syracuseStep 1320127 = 1980191) B1980191
theorem B4015295 : Blo 1319478 4015295 := bstep (se 1 (by rfl) ⟨3011471, by rfl⟩ : syracuseStep 4015295 = 6022943) B6022943
theorem B1320159 : Blo 1319478 1320159 := bstep (se 1 (by rfl) ⟨990119, by rfl⟩ : syracuseStep 1320159 = 1980239) B1980239
theorem B2114795 : Blo 1319478 2114795 := bstep (se 1 (by rfl) ⟨1586096, by rfl⟩ : syracuseStep 2114795 = 3172193) B3172193
theorem B1672427 : Blo 1319478 1672427 := bstep (se 1 (by rfl) ⟨1254320, by rfl⟩ : syracuseStep 1672427 = 2508641) B2508641
theorem B4457753 : Blo 1319478 4457753 := bstep (se 2 (by rfl) ⟨1671657, by rfl⟩ : syracuseStep 4457753 = 3343315) B3343315
theorem B5080367 : Blo 1319478 5080367 := bstep (se 1 (by rfl) ⟨3810275, by rfl⟩ : syracuseStep 5080367 = 7620551) B7620551
theorem B1320239 : Blo 1319478 1320239 := bstep (se 1 (by rfl) ⟨990179, by rfl⟩ : syracuseStep 1320239 = 1980359) B1980359
theorem B2508079 : Blo 1319478 2508079 := bstep (se 1 (by rfl) ⟨1881059, by rfl⟩ : syracuseStep 2508079 = 3762119) B3762119
theorem B2229673 : Blo 1319478 2229673 := bstep (se 2 (by rfl) ⟨836127, by rfl⟩ : syracuseStep 2229673 = 1672255) B1672255
theorem B5350855 : Blo 1319478 5350855 := bstep (se 1 (by rfl) ⟨4013141, by rfl⟩ : syracuseStep 5350855 = 8026283) B8026283
theorem B4761089 : Blo 1319478 4761089 := bstep (se 2 (by rfl) ⟨1785408, by rfl⟩ : syracuseStep 4761089 = 3570817) B3570817
theorem B1320475 : Blo 1319478 1320475 := bstep (se 1 (by rfl) ⟨990356, by rfl⟩ : syracuseStep 1320475 = 1980713) B1980713
theorem B1320479 : Blo 1319478 1320479 := bstep (se 1 (by rfl) ⟨990359, by rfl⟩ : syracuseStep 1320479 = 1980719) B1980719
theorem B10700441 : Blo 1319478 10700441 := bstep (se 2 (by rfl) ⟨4012665, by rfl⟩ : syracuseStep 10700441 = 8025331) B8025331
theorem B1320639 : Blo 1319478 1320639 := bstep (se 1 (by rfl) ⟨990479, by rfl⟩ : syracuseStep 1320639 = 1980959) B1980959
theorem B4515563 : Blo 1319478 4515563 := bstep (se 1 (by rfl) ⟨3386672, by rfl⟩ : syracuseStep 4515563 = 6773345) B6773345
theorem B1320895 : Blo 1319478 1320895 := bstep (se 1 (by rfl) ⟨990671, by rfl⟩ : syracuseStep 1320895 = 1981343) B1981343
theorem B1320927 : Blo 1319478 1320927 := bstep (se 1 (by rfl) ⟨990695, by rfl⟩ : syracuseStep 1320927 = 1981391) B1981391
theorem B24078329 : Blo 1319478 24078329 := bstep (se 2 (by rfl) ⟨9029373, by rfl⟩ : syracuseStep 24078329 = 18058747) B18058747
theorem B1320987 : Blo 1319478 1320987 := bstep (se 1 (by rfl) ⟨990740, by rfl⟩ : syracuseStep 1320987 = 1981481) B1981481
theorem B1320991 : Blo 1319478 1320991 := bstep (se 1 (by rfl) ⟨990743, by rfl⟩ : syracuseStep 1320991 = 1981487) B1981487
theorem B1321007 : Blo 1319478 1321007 := bstep (se 1 (by rfl) ⟨990755, by rfl⟩ : syracuseStep 1321007 = 1981511) B1981511
theorem B6686873 : Blo 1319478 6686873 := bstep (se 2 (by rfl) ⟨2507577, by rfl⟩ : syracuseStep 6686873 = 5015155) B5015155
theorem B1321183 : Blo 1319478 1321183 := bstep (se 1 (by rfl) ⟨990887, by rfl⟩ : syracuseStep 1321183 = 1981775) B1981775
theorem B4458779 : Blo 1319478 4458779 := bstep (se 1 (by rfl) ⟨3344084, by rfl⟩ : syracuseStep 4458779 = 6688169) B6688169
theorem B1321243 : Blo 1319478 1321243 := bstep (se 1 (by rfl) ⟨990932, by rfl⟩ : syracuseStep 1321243 = 1981865) B1981865
theorem B1321343 : Blo 1319478 1321343 := bstep (se 1 (by rfl) ⟨991007, by rfl⟩ : syracuseStep 1321343 = 1982015) B1982015
theorem B4458941 : Blo 1319478 4458941 := bstep (se 3 (by rfl) ⟨836051, by rfl⟩ : syracuseStep 4458941 = 1672103) B1672103
theorem B4459103 : Blo 1319478 4459103 := bstep (se 1 (by rfl) ⟨3344327, by rfl⟩ : syracuseStep 4459103 = 6688655) B6688655
theorem B1485607 : Blo 1319478 1485607 := bstep (se 1 (by rfl) ⟨1114205, by rfl⟩ : syracuseStep 1485607 = 2228411) B2228411
theorem B5016401 : Blo 1319478 5016401 := bstep (se 2 (by rfl) ⟨1881150, by rfl⟩ : syracuseStep 5016401 = 3762301) B3762301
theorem B10021805 : Blo 1319478 10021805 := bstep (se 3 (by rfl) ⟨1879088, by rfl⟩ : syracuseStep 10021805 = 3758177) B3758177
theorem B9038765 : Blo 1319478 9038765 := bstep (se 3 (by rfl) ⟨1694768, by rfl⟩ : syracuseStep 9038765 = 3389537) B3389537
theorem B6687683 : Blo 1319478 6687683 := bstep (se 1 (by rfl) ⟨5015762, by rfl⟩ : syracuseStep 6687683 = 10031525) B10031525
theorem B10030067 : Blo 1319478 10030067 := bstep (se 1 (by rfl) ⟨7522550, by rfl⟩ : syracuseStep 10030067 = 15045101) B15045101
theorem B4230539 : Blo 1319478 4230539 := bstep (se 1 (by rfl) ⟨3172904, by rfl⟩ : syracuseStep 4230539 = 6345809) B6345809
theorem B2969063 : Blo 1319478 2969063 := bstep (se 1 (by rfl) ⟨2226797, by rfl⟩ : syracuseStep 2969063 = 4453595) B4453595
theorem B13553255 : Blo 1319478 13553255 := bstep (se 1 (by rfl) ⟨10164941, by rfl⟩ : syracuseStep 13553255 = 20329883) B20329883
theorem B17141395 : Blo 1319478 17141395 := bstep (se 1 (by rfl) ⟨12856046, by rfl⟩ : syracuseStep 17141395 = 25712093) B25712093
theorem B42840049 : Blo 1319478 42840049 := bstep (se 2 (by rfl) ⟨16065018, by rfl⟩ : syracuseStep 42840049 = 32130037) B32130037
theorem B1880057 : Blo 1319478 1880057 := bstep (se 2 (by rfl) ⟨705021, by rfl⟩ : syracuseStep 1880057 = 1410043) B1410043
theorem B2969639 : Blo 1319478 2969639 := bstep (se 1 (by rfl) ⟨2227229, by rfl⟩ : syracuseStep 2969639 = 4454459) B4454459
theorem B2969819 : Blo 1319478 2969819 := bstep (se 1 (by rfl) ⟨2227364, by rfl⟩ : syracuseStep 2969819 = 4454729) B4454729
theorem B5640479 : Blo 1319478 5640479 := bstep (se 1 (by rfl) ⟨4230359, by rfl⟩ : syracuseStep 5640479 = 8460719) B8460719
theorem B2970089 : Blo 1319478 2970089 := bstep (se 2 (by rfl) ⟨1113783, by rfl⟩ : syracuseStep 2970089 = 2227567) B2227567
theorem B12055223 : Blo 1319478 12055223 := bstep (se 1 (by rfl) ⟨9041417, by rfl⟩ : syracuseStep 12055223 = 18082835) B18082835
theorem B6435607 : Blo 1319478 6435607 := bstep (se 1 (by rfl) ⟨4826705, by rfl⟩ : syracuseStep 6435607 = 9653411) B9653411
theorem B1979273 : Blo 1319478 1979273 := bstep (se 2 (by rfl) ⟨742227, by rfl⟩ : syracuseStep 1979273 = 1484455) B1484455
theorem B2970593 : Blo 1319478 2970593 := bstep (se 2 (by rfl) ⟨1113972, by rfl⟩ : syracuseStep 2970593 = 2227945) B2227945
theorem B21402701 : Blo 1319478 21402701 := bstep (se 3 (by rfl) ⟨4013006, by rfl⟩ : syracuseStep 21402701 = 8026013) B8026013
theorem B2970719 : Blo 1319478 2970719 := bstep (se 1 (by rfl) ⟨2228039, by rfl⟩ : syracuseStep 2970719 = 4456079) B4456079
theorem B36148369 : Blo 1319478 36148369 := bstep (se 2 (by rfl) ⟨13555638, by rfl⟩ : syracuseStep 36148369 = 27111277) B27111277
theorem B1979657 : Blo 1319478 1979657 := bstep (se 2 (by rfl) ⟨742371, by rfl⟩ : syracuseStep 1979657 = 1484743) B1484743
theorem B33854759 : Blo 1319478 33854759 := bstep (se 1 (by rfl) ⟨25391069, by rfl⟩ : syracuseStep 33854759 = 50782139) B50782139
theorem B10024235 : Blo 1319478 10024235 := bstep (se 1 (by rfl) ⟨7518176, by rfl⟩ : syracuseStep 10024235 = 15036353) B15036353
theorem B1979711 : Blo 1319478 1979711 := bstep (se 1 (by rfl) ⟨1484783, by rfl⟩ : syracuseStep 1979711 = 2969567) B2969567
theorem B1881407 : Blo 1319478 1881407 := bstep (se 1 (by rfl) ⟨1411055, by rfl⟩ : syracuseStep 1881407 = 2822111) B2822111
theorem B11286013 : Blo 1319478 11286013 := bstep (se 3 (by rfl) ⟨2116127, by rfl⟩ : syracuseStep 11286013 = 4232255) B4232255
theorem B5011055 : Blo 1319478 5011055 := bstep (se 1 (by rfl) ⟨3758291, by rfl⟩ : syracuseStep 5011055 = 7516583) B7516583
theorem B2676361 : Blo 1319478 2676361 := bstep (se 2 (by rfl) ⟨1003635, by rfl⟩ : syracuseStep 2676361 = 2007271) B2007271
theorem B1980137 : Blo 1319478 1980137 := bstep (se 2 (by rfl) ⟨742551, by rfl⟩ : syracuseStep 1980137 = 1485103) B1485103
theorem B1980143 : Blo 1319478 1980143 := bstep (se 1 (by rfl) ⟨1485107, by rfl⟩ : syracuseStep 1980143 = 2970215) B2970215
theorem B6027065 : Blo 1319478 6027065 := bstep (se 2 (by rfl) ⟨2260149, by rfl⟩ : syracuseStep 6027065 = 4520299) B4520299
theorem B2971475 : Blo 1319478 2971475 := bstep (se 1 (by rfl) ⟨2228606, by rfl⟩ : syracuseStep 2971475 = 4457213) B4457213
theorem B19306631 : Blo 1319478 19306631 := bstep (se 1 (by rfl) ⟨14479973, by rfl⟩ : syracuseStep 19306631 = 28959947) B28959947
theorem B1980599 : Blo 1319478 1980599 := bstep (se 1 (by rfl) ⟨1485449, by rfl⟩ : syracuseStep 1980599 = 2970899) B2970899
theorem B5429467 : Blo 1319478 5429467 := bstep (se 1 (by rfl) ⟨4072100, by rfl⟩ : syracuseStep 5429467 = 8144201) B8144201
theorem B1980647 : Blo 1319478 1980647 := bstep (se 1 (by rfl) ⟨1485485, by rfl⟩ : syracuseStep 1980647 = 2970971) B2970971
theorem B5011753 : Blo 1319478 5011753 := bstep (se 2 (by rfl) ⟨1879407, by rfl⟩ : syracuseStep 5011753 = 3758815) B3758815
theorem B2971961 : Blo 1319478 2971961 := bstep (se 2 (by rfl) ⟨1114485, by rfl⟩ : syracuseStep 2971961 = 2228971) B2228971
theorem B7059835 : Blo 1319478 7059835 := bstep (se 1 (by rfl) ⟨5294876, by rfl⟩ : syracuseStep 7059835 = 10589753) B10589753
theorem B1981019 : Blo 1319478 1981019 := bstep (se 1 (by rfl) ⟨1485764, by rfl⟩ : syracuseStep 1981019 = 2971529) B2971529
theorem B10705607 : Blo 1319478 10705607 := bstep (se 1 (by rfl) ⟨8029205, by rfl⟩ : syracuseStep 10705607 = 16058411) B16058411
theorem B5085919 : Blo 1319478 5085919 := bstep (se 1 (by rfl) ⟨3814439, by rfl⟩ : syracuseStep 5085919 = 7628879) B7628879
theorem B1981163 : Blo 1319478 1981163 := bstep (se 1 (by rfl) ⟨1485872, by rfl⟩ : syracuseStep 1981163 = 2971745) B2971745
theorem B2226953 : Blo 1319478 2226953 := bstep (se 2 (by rfl) ⟨835107, by rfl⟩ : syracuseStep 2226953 = 1670215) B1670215
theorem B1981193 : Blo 1319478 1981193 := bstep (se 2 (by rfl) ⟨742947, by rfl⟩ : syracuseStep 1981193 = 1485895) B1485895
theorem B7519067 : Blo 1319478 7519067 := bstep (se 1 (by rfl) ⟨5639300, by rfl⟩ : syracuseStep 7519067 = 11278601) B11278601
theorem B2972879 : Blo 1319478 2972879 := bstep (se 1 (by rfl) ⟨2229659, by rfl⟩ : syracuseStep 2972879 = 4459319) B4459319
theorem B4455647 : Blo 1319478 4455647 := bstep (se 1 (by rfl) ⟨3341735, by rfl⟩ : syracuseStep 4455647 = 6683471) B6683471
theorem B2505953 : Blo 1319478 2505953 := bstep (se 2 (by rfl) ⟨939732, by rfl⟩ : syracuseStep 2505953 = 1879465) B1879465
theorem B38575399 : Blo 1319478 38575399 := bstep (se 1 (by rfl) ⟨28931549, by rfl⟩ : syracuseStep 38575399 = 57863099) B57863099
theorem B91471169 : Blo 1319478 91471169 := bstep (se 2 (by rfl) ⟨34301688, by rfl⟩ : syracuseStep 91471169 = 68603377) B68603377
theorem B6020459 : Blo 1319478 6020459 := bstep (se 1 (by rfl) ⟨4515344, by rfl⟩ : syracuseStep 6020459 = 9030689) B9030689
theorem B6348269 : Blo 1319478 6348269 := bstep (se 3 (by rfl) ⟨1190300, by rfl⟩ : syracuseStep 6348269 = 2380601) B2380601
theorem B2973257 : Blo 1319478 2973257 := bstep (se 2 (by rfl) ⟨1114971, by rfl⟩ : syracuseStep 2973257 = 2229943) B2229943
theorem B13549153 : Blo 1319478 13549153 := bstep (se 2 (by rfl) ⟨5080932, by rfl⟩ : syracuseStep 13549153 = 10161865) B10161865
theorem B1982063 : Blo 1319478 1982063 := bstep (se 1 (by rfl) ⟨1486547, by rfl⟩ : syracuseStep 1982063 = 2973095) B2973095
theorem B3341999 : Blo 1319478 3341999 := bstep (se 1 (by rfl) ⟨2506499, by rfl⟩ : syracuseStep 3341999 = 5012999) B5012999
theorem B1982183 : Blo 1319478 1982183 := bstep (se 1 (by rfl) ⟨1486637, by rfl⟩ : syracuseStep 1982183 = 2973275) B2973275
theorem B38657821 : Blo 1319478 38657821 := bstep (se 3 (by rfl) ⟨7248341, by rfl⟩ : syracuseStep 38657821 = 14496683) B14496683
theorem B3760319 : Blo 1319478 3760319 := bstep (se 1 (by rfl) ⟨2820239, by rfl⟩ : syracuseStep 3760319 = 5640479) B5640479
theorem B8036815 : Blo 1319478 8036815 := bstep (se 1 (by rfl) ⟨6027611, by rfl⟩ : syracuseStep 8036815 = 12055223) B12055223
theorem B1319515 : Blo 1319478 1319515 := bstep (se 1 (by rfl) ⟨989636, by rfl⟩ : syracuseStep 1319515 = 1979273) B1979273
theorem B5014183 : Blo 1319478 5014183 := bstep (se 1 (by rfl) ⟨3760637, by rfl⟩ : syracuseStep 5014183 = 7521275) B7521275
theorem B1319771 : Blo 1319478 1319771 := bstep (se 1 (by rfl) ⟨989828, by rfl⟩ : syracuseStep 1319771 = 1979657) B1979657
theorem B22569839 : Blo 1319478 22569839 := bstep (se 1 (by rfl) ⟨16927379, by rfl⟩ : syracuseStep 22569839 = 33854759) B33854759
theorem B1319807 : Blo 1319478 1319807 := bstep (se 1 (by rfl) ⟨989855, by rfl⟩ : syracuseStep 1319807 = 1979711) B1979711
theorem B4227977 : Blo 1319478 4227977 := bstep (se 2 (by rfl) ⟨1585491, by rfl⟩ : syracuseStep 4227977 = 3170983) B3170983
theorem B1320091 : Blo 1319478 1320091 := bstep (se 1 (by rfl) ⟨990068, by rfl⟩ : syracuseStep 1320091 = 1980137) B1980137
theorem B1320095 : Blo 1319478 1320095 := bstep (se 1 (by rfl) ⟨990071, by rfl⟩ : syracuseStep 1320095 = 1980143) B1980143
theorem B27124901 : Blo 1319478 27124901 := bstep (se 4 (by rfl) ⟨2542959, by rfl⟩ : syracuseStep 27124901 = 5085919) B5085919
theorem B4457915 : Blo 1319478 4457915 := bstep (se 1 (by rfl) ⟨3343436, by rfl⟩ : syracuseStep 4457915 = 6686873) B6686873
theorem B1320399 : Blo 1319478 1320399 := bstep (se 1 (by rfl) ⟨990299, by rfl⟩ : syracuseStep 1320399 = 1980599) B1980599
theorem B1320431 : Blo 1319478 1320431 := bstep (se 1 (by rfl) ⟨990323, by rfl⟩ : syracuseStep 1320431 = 1980647) B1980647
theorem B1320679 : Blo 1319478 1320679 := bstep (se 1 (by rfl) ⟨990509, by rfl⟩ : syracuseStep 1320679 = 1981019) B1981019
theorem B3344105 : Blo 1319478 3344105 := bstep (se 2 (by rfl) ⟨1254039, by rfl⟩ : syracuseStep 3344105 = 2508079) B2508079
theorem B7137071 : Blo 1319478 7137071 := bstep (se 1 (by rfl) ⟨5352803, by rfl⟩ : syracuseStep 7137071 = 10705607) B10705607
theorem B1320775 : Blo 1319478 1320775 := bstep (se 1 (by rfl) ⟨990581, by rfl⟩ : syracuseStep 1320775 = 1981163) B1981163
theorem B1484635 : Blo 1319478 1484635 := bstep (se 1 (by rfl) ⟨1113476, by rfl⟩ : syracuseStep 1484635 = 2226953) B2226953
theorem B1320795 : Blo 1319478 1320795 := bstep (se 1 (by rfl) ⟨990596, by rfl⟩ : syracuseStep 1320795 = 1981193) B1981193
theorem B3344267 : Blo 1319478 3344267 := bstep (se 1 (by rfl) ⟨2508200, by rfl⟩ : syracuseStep 3344267 = 5016401) B5016401
theorem B4458455 : Blo 1319478 4458455 := bstep (se 1 (by rfl) ⟨3343841, by rfl⟩ : syracuseStep 4458455 = 6687683) B6687683
theorem B37652453 : Blo 1319478 37652453 := bstep (se 4 (by rfl) ⟨3529917, by rfl⟩ : syracuseStep 37652453 = 7059835) B7059835
theorem B6686711 : Blo 1319478 6686711 := bstep (se 1 (by rfl) ⟨5015033, by rfl⟩ : syracuseStep 6686711 = 10030067) B10030067
theorem B18065537 : Blo 1319478 18065537 := bstep (se 2 (by rfl) ⟨6774576, by rfl⟩ : syracuseStep 18065537 = 13549153) B13549153
theorem B2820359 : Blo 1319478 2820359 := bstep (se 1 (by rfl) ⟨2115269, by rfl⟩ : syracuseStep 2820359 = 4230539) B4230539
theorem B1321375 : Blo 1319478 1321375 := bstep (se 1 (by rfl) ⟨991031, by rfl⟩ : syracuseStep 1321375 = 1982063) B1982063
theorem B1321455 : Blo 1319478 1321455 := bstep (se 1 (by rfl) ⟨991091, by rfl⟩ : syracuseStep 1321455 = 1982183) B1982183
theorem B7334587 : Blo 1319478 7334587 := bstep (se 1 (by rfl) ⟨5500940, by rfl⟩ : syracuseStep 7334587 = 11001881) B11001881
theorem B3812179 : Blo 1319478 3812179 := bstep (se 1 (by rfl) ⟨2859134, by rfl⟩ : syracuseStep 3812179 = 5718269) B5718269
theorem B1485679 : Blo 1319478 1485679 := bstep (se 1 (by rfl) ⟨1114259, by rfl⟩ : syracuseStep 1485679 = 2228519) B2228519
theorem B5639453 : Blo 1319478 5639453 := bstep (se 3 (by rfl) ⟨1057397, by rfl⟩ : syracuseStep 5639453 = 2114795) B2114795
theorem B4459805 : Blo 1319478 4459805 := bstep (se 3 (by rfl) ⟨836213, by rfl⟩ : syracuseStep 4459805 = 1672427) B1672427
theorem B7515625 : Blo 1319478 7515625 := bstep (se 2 (by rfl) ⟨2818359, by rfl⟩ : syracuseStep 7515625 = 5636719) B5636719
theorem B5017085 : Blo 1319478 5017085 := bstep (se 3 (by rfl) ⟨940703, by rfl⟩ : syracuseStep 5017085 = 1881407) B1881407
theorem B3174059 : Blo 1319478 3174059 := bstep (se 1 (by rfl) ⟨2380544, by rfl⟩ : syracuseStep 3174059 = 4761089) B4761089
theorem B8580809 : Blo 1319478 8580809 := bstep (se 2 (by rfl) ⟨3217803, by rfl⟩ : syracuseStep 8580809 = 6435607) B6435607
theorem B3010375 : Blo 1319478 3010375 := bstep (se 1 (by rfl) ⟨2257781, by rfl⟩ : syracuseStep 3010375 = 4515563) B4515563
theorem B4018043 : Blo 1319478 4018043 := bstep (se 1 (by rfl) ⟨3013532, by rfl⟩ : syracuseStep 4018043 = 6027065) B6027065
theorem B5353465 : Blo 1319478 5353465 := bstep (se 2 (by rfl) ⟨2007549, by rfl⟩ : syracuseStep 5353465 = 4015099) B4015099
theorem B16052219 : Blo 1319478 16052219 := bstep (se 1 (by rfl) ⟨12039164, by rfl⟩ : syracuseStep 16052219 = 24078329) B24078329
theorem B48197825 : Blo 1319478 48197825 := bstep (se 2 (by rfl) ⟨18074184, by rfl⟩ : syracuseStep 48197825 = 36148369) B36148369
theorem B51433865 : Blo 1319478 51433865 := bstep (se 2 (by rfl) ⟨19287699, by rfl⟩ : syracuseStep 51433865 = 38575399) B38575399
theorem B6681203 : Blo 1319478 6681203 := bstep (se 1 (by rfl) ⟨5010902, by rfl⟩ : syracuseStep 6681203 = 10021805) B10021805
theorem B6025843 : Blo 1319478 6025843 := bstep (se 1 (by rfl) ⟨4519382, by rfl⟩ : syracuseStep 6025843 = 9038765) B9038765
theorem B2970431 : Blo 1319478 2970431 := bstep (se 1 (by rfl) ⟨2227823, by rfl⟩ : syracuseStep 2970431 = 4455647) B4455647
theorem B3568481 : Blo 1319478 3568481 := bstep (se 2 (by rfl) ⟨1338180, by rfl⟩ : syracuseStep 3568481 = 2676361) B2676361
theorem B1979375 : Blo 1319478 1979375 := bstep (se 1 (by rfl) ⟨1484531, by rfl⟩ : syracuseStep 1979375 = 2969063) B2969063
theorem B4232179 : Blo 1319478 4232179 := bstep (se 1 (by rfl) ⟨3174134, by rfl⟩ : syracuseStep 4232179 = 6348269) B6348269
theorem B57120065 : Blo 1319478 57120065 := bstep (se 2 (by rfl) ⟨21420024, by rfl⟩ : syracuseStep 57120065 = 42840049) B42840049
theorem B1979759 : Blo 1319478 1979759 := bstep (se 1 (by rfl) ⟨1484819, by rfl⟩ : syracuseStep 1979759 = 2969639) B2969639
theorem B7525831 : Blo 1319478 7525831 := bstep (se 1 (by rfl) ⟨5644373, by rfl⟩ : syracuseStep 7525831 = 11288747) B11288747
theorem B1979879 : Blo 1319478 1979879 := bstep (se 1 (by rfl) ⟨1484909, by rfl⟩ : syracuseStep 1979879 = 2969819) B2969819
theorem B7239289 : Blo 1319478 7239289 := bstep (se 2 (by rfl) ⟨2714733, by rfl⟩ : syracuseStep 7239289 = 5429467) B5429467
theorem B3757711 : Blo 1319478 3757711 := bstep (se 1 (by rfl) ⟨2818283, by rfl⟩ : syracuseStep 3757711 = 5636567) B5636567
theorem B1980059 : Blo 1319478 1980059 := bstep (se 1 (by rfl) ⟨1485044, by rfl⟩ : syracuseStep 1980059 = 2970089) B2970089
theorem B51484349 : Blo 1319478 51484349 := bstep (se 3 (by rfl) ⟨9653315, by rfl⟩ : syracuseStep 51484349 = 19306631) B19306631
theorem B6682337 : Blo 1319478 6682337 := bstep (se 2 (by rfl) ⟨2505876, by rfl⟩ : syracuseStep 6682337 = 5011753) B5011753
theorem B1980395 : Blo 1319478 1980395 := bstep (se 1 (by rfl) ⟨1485296, by rfl⟩ : syracuseStep 1980395 = 2970593) B2970593
theorem B14268467 : Blo 1319478 14268467 := bstep (se 1 (by rfl) ⟨10701350, by rfl⟩ : syracuseStep 14268467 = 21402701) B21402701
theorem B1980479 : Blo 1319478 1980479 := bstep (se 1 (by rfl) ⟨1485359, by rfl⟩ : syracuseStep 1980479 = 2970719) B2970719
theorem B13547645 : Blo 1319478 13547645 := bstep (se 3 (by rfl) ⟨2540183, by rfl⟩ : syracuseStep 13547645 = 5080367) B5080367
theorem B2676863 : Blo 1319478 2676863 := bstep (se 1 (by rfl) ⟨2007647, by rfl⟩ : syracuseStep 2676863 = 4015295) B4015295
theorem B2971835 : Blo 1319478 2971835 := bstep (se 1 (by rfl) ⟨2228876, by rfl⟩ : syracuseStep 2971835 = 4457753) B4457753
theorem B6682823 : Blo 1319478 6682823 := bstep (se 1 (by rfl) ⟨5012117, by rfl⟩ : syracuseStep 6682823 = 10024235) B10024235
theorem B1980809 : Blo 1319478 1980809 := bstep (se 2 (by rfl) ⟨742803, by rfl⟩ : syracuseStep 1980809 = 1485607) B1485607
theorem B3340703 : Blo 1319478 3340703 := bstep (se 1 (by rfl) ⟨2505527, by rfl⟩ : syracuseStep 3340703 = 5011055) B5011055
theorem B7133627 : Blo 1319478 7133627 := bstep (se 1 (by rfl) ⟨5350220, by rfl⟩ : syracuseStep 7133627 = 10700441) B10700441
theorem B1980983 : Blo 1319478 1980983 := bstep (se 1 (by rfl) ⟨1485737, by rfl⟩ : syracuseStep 1980983 = 2971475) B2971475
theorem B2972519 : Blo 1319478 2972519 := bstep (se 1 (by rfl) ⟨2229389, by rfl⟩ : syracuseStep 2972519 = 4458779) B4458779
theorem B1981307 : Blo 1319478 1981307 := bstep (se 1 (by rfl) ⟨1485980, by rfl⟩ : syracuseStep 1981307 = 2971961) B2971961
theorem B36142013 : Blo 1319478 36142013 := bstep (se 3 (by rfl) ⟨6776627, by rfl⟩ : syracuseStep 36142013 = 13553255) B13553255
theorem B2972627 : Blo 1319478 2972627 := bstep (se 1 (by rfl) ⟨2229470, by rfl⟩ : syracuseStep 2972627 = 4458941) B4458941
theorem B2972735 : Blo 1319478 2972735 := bstep (se 1 (by rfl) ⟨2229551, by rfl⟩ : syracuseStep 2972735 = 4459103) B4459103
theorem B25386149 : Blo 1319478 25386149 := bstep (se 4 (by rfl) ⟨2379951, by rfl⟩ : syracuseStep 25386149 = 4759903) B4759903
theorem B2972897 : Blo 1319478 2972897 := bstep (se 2 (by rfl) ⟨1114836, by rfl⟩ : syracuseStep 2972897 = 2229673) B2229673
theorem B5012711 : Blo 1319478 5012711 := bstep (se 1 (by rfl) ⟨3759533, by rfl⟩ : syracuseStep 5012711 = 7519067) B7519067
theorem B7134473 : Blo 1319478 7134473 := bstep (se 2 (by rfl) ⟨2675427, by rfl⟩ : syracuseStep 7134473 = 5350855) B5350855
theorem B15048017 : Blo 1319478 15048017 := bstep (se 2 (by rfl) ⟨5643006, by rfl⟩ : syracuseStep 15048017 = 11286013) B11286013
theorem B1981919 : Blo 1319478 1981919 := bstep (se 1 (by rfl) ⟨1486439, by rfl⟩ : syracuseStep 1981919 = 2972879) B2972879
theorem B1670635 : Blo 1319478 1670635 := bstep (se 1 (by rfl) ⟨1252976, by rfl⟩ : syracuseStep 1670635 = 2505953) B2505953
theorem B22855193 : Blo 1319478 22855193 := bstep (se 2 (by rfl) ⟨8570697, by rfl⟩ : syracuseStep 22855193 = 17141395) B17141395
theorem B60980779 : Blo 1319478 60980779 := bstep (se 1 (by rfl) ⟨45735584, by rfl⟩ : syracuseStep 60980779 = 91471169) B91471169
theorem B4013639 : Blo 1319478 4013639 := bstep (se 1 (by rfl) ⟨3010229, by rfl⟩ : syracuseStep 4013639 = 6020459) B6020459
theorem B51543761 : Blo 1319478 51543761 := bstep (se 2 (by rfl) ⟨19328910, by rfl⟩ : syracuseStep 51543761 = 38657821) B38657821
theorem B1982171 : Blo 1319478 1982171 := bstep (se 1 (by rfl) ⟨1486628, by rfl⟩ : syracuseStep 1982171 = 2973257) B2973257
theorem B2227999 : Blo 1319478 2227999 := bstep (se 1 (by rfl) ⟨1670999, by rfl⟩ : syracuseStep 2227999 = 3341999) B3341999
theorem B5013485 : Blo 1319478 5013485 := bstep (se 3 (by rfl) ⟨940028, by rfl⟩ : syracuseStep 5013485 = 1880057) B1880057
theorem B2506879 : Blo 1319478 2506879 := bstep (se 1 (by rfl) ⟨1880159, by rfl⟩ : syracuseStep 2506879 = 3760319) B3760319
theorem B325230821 : Blo 1319478 325230821 := bstep (se 4 (by rfl) ⟨30490389, by rfl⟩ : syracuseStep 325230821 = 60980779) B60980779
theorem B2818651 : Blo 1319478 2818651 := bstep (se 1 (by rfl) ⟨2113988, by rfl⟩ : syracuseStep 2818651 = 4227977) B4227977
theorem B32137829 : Blo 1319478 32137829 := bstep (se 4 (by rfl) ⟨3012921, by rfl⟩ : syracuseStep 32137829 = 6025843) B6025843
theorem B10715753 : Blo 1319478 10715753 := bstep (se 2 (by rfl) ⟨4018407, by rfl⟩ : syracuseStep 10715753 = 8036815) B8036815
theorem B1319583 : Blo 1319478 1319583 := bstep (se 1 (by rfl) ⟨989687, by rfl⟩ : syracuseStep 1319583 = 1979375) B1979375
theorem B7520957 : Blo 1319478 7520957 := bstep (se 3 (by rfl) ⟨1410179, by rfl⟩ : syracuseStep 7520957 = 2820359) B2820359
theorem B6685577 : Blo 1319478 6685577 := bstep (se 2 (by rfl) ⟨2507091, by rfl⟩ : syracuseStep 6685577 = 5014183) B5014183
theorem B1319839 : Blo 1319478 1319839 := bstep (se 1 (by rfl) ⟨989879, by rfl⟩ : syracuseStep 1319839 = 1979759) B1979759
theorem B1319919 : Blo 1319478 1319919 := bstep (se 1 (by rfl) ⟨989939, by rfl⟩ : syracuseStep 1319919 = 1979879) B1979879
theorem B1320039 : Blo 1319478 1320039 := bstep (se 1 (by rfl) ⟨990029, by rfl⟩ : syracuseStep 1320039 = 1980059) B1980059
theorem B2229403 : Blo 1319478 2229403 := bstep (se 1 (by rfl) ⟨1672052, by rfl⟩ : syracuseStep 2229403 = 3344105) B3344105
theorem B19023005 : Blo 1319478 19023005 := bstep (se 3 (by rfl) ⟨3566813, by rfl⟩ : syracuseStep 19023005 = 7133627) B7133627
theorem B2229511 : Blo 1319478 2229511 := bstep (se 1 (by rfl) ⟨1672133, by rfl⟩ : syracuseStep 2229511 = 3344267) B3344267
theorem B25101635 : Blo 1319478 25101635 := bstep (se 1 (by rfl) ⟨18826226, by rfl⟩ : syracuseStep 25101635 = 37652453) B37652453
theorem B1320263 : Blo 1319478 1320263 := bstep (se 1 (by rfl) ⟨990197, by rfl⟩ : syracuseStep 1320263 = 1980395) B1980395
theorem B4457807 : Blo 1319478 4457807 := bstep (se 1 (by rfl) ⟨3343355, by rfl⟩ : syracuseStep 4457807 = 6686711) B6686711
theorem B9512311 : Blo 1319478 9512311 := bstep (se 1 (by rfl) ⟨7134233, by rfl⟩ : syracuseStep 9512311 = 14268467) B14268467
theorem B1320319 : Blo 1319478 1320319 := bstep (se 1 (by rfl) ⟨990239, by rfl⟩ : syracuseStep 1320319 = 1980479) B1980479
theorem B12043691 : Blo 1319478 12043691 := bstep (se 1 (by rfl) ⟨9032768, by rfl⟩ : syracuseStep 12043691 = 18065537) B18065537
theorem B1320539 : Blo 1319478 1320539 := bstep (se 1 (by rfl) ⟨990404, by rfl⟩ : syracuseStep 1320539 = 1980809) B1980809
theorem B1320655 : Blo 1319478 1320655 := bstep (se 1 (by rfl) ⟨990491, by rfl⟩ : syracuseStep 1320655 = 1980983) B1980983
theorem B1320871 : Blo 1319478 1320871 := bstep (se 1 (by rfl) ⟨990653, by rfl⟩ : syracuseStep 1320871 = 1981307) B1981307
theorem B24094675 : Blo 1319478 24094675 := bstep (se 1 (by rfl) ⟨18071006, by rfl⟩ : syracuseStep 24094675 = 36142013) B36142013
theorem B10020833 : Blo 1319478 10020833 := bstep (se 2 (by rfl) ⟨3757812, by rfl⟩ : syracuseStep 10020833 = 7515625) B7515625
theorem B9652385 : Blo 1319478 9652385 := bstep (se 2 (by rfl) ⟨3619644, by rfl⟩ : syracuseStep 9652385 = 7239289) B7239289
theorem B1321279 : Blo 1319478 1321279 := bstep (se 1 (by rfl) ⟨990959, by rfl⟩ : syracuseStep 1321279 = 1981919) B1981919
theorem B3344723 : Blo 1319478 3344723 := bstep (se 1 (by rfl) ⟨2508542, by rfl⟩ : syracuseStep 3344723 = 5017085) B5017085
theorem B2116039 : Blo 1319478 2116039 := bstep (se 1 (by rfl) ⟨1587029, by rfl⟩ : syracuseStep 2116039 = 3174059) B3174059
theorem B5720539 : Blo 1319478 5720539 := bstep (se 1 (by rfl) ⟨4290404, by rfl⟩ : syracuseStep 5720539 = 8580809) B8580809
theorem B1321447 : Blo 1319478 1321447 := bstep (se 1 (by rfl) ⟨991085, by rfl⟩ : syracuseStep 1321447 = 1982171) B1982171
theorem B7137953 : Blo 1319478 7137953 := bstep (se 2 (by rfl) ⟨2676732, by rfl⟩ : syracuseStep 7137953 = 5353465) B5353465
theorem B10701479 : Blo 1319478 10701479 := bstep (se 1 (by rfl) ⟨8026109, by rfl⟩ : syracuseStep 10701479 = 16052219) B16052219
theorem B32131883 : Blo 1319478 32131883 := bstep (se 1 (by rfl) ⟨24098912, by rfl⟩ : syracuseStep 32131883 = 48197825) B48197825
theorem B2378987 : Blo 1319478 2378987 := bstep (se 1 (by rfl) ⟨1784240, by rfl⟩ : syracuseStep 2378987 = 3568481) B3568481
theorem B18083267 : Blo 1319478 18083267 := bstep (se 1 (by rfl) ⟨13562450, by rfl⟩ : syracuseStep 18083267 = 27124901) B27124901
theorem B38080043 : Blo 1319478 38080043 := bstep (se 1 (by rfl) ⟨28560032, by rfl⟩ : syracuseStep 38080043 = 57120065) B57120065
theorem B5082905 : Blo 1319478 5082905 := bstep (se 2 (by rfl) ⟨1906089, by rfl⟩ : syracuseStep 5082905 = 3812179) B3812179
theorem B9031763 : Blo 1319478 9031763 := bstep (se 1 (by rfl) ⟨6773822, by rfl⟩ : syracuseStep 9031763 = 13547645) B13547645
theorem B137450029 : Blo 1319478 137450029 := bstep (se 3 (by rfl) ⟨25771880, by rfl⟩ : syracuseStep 137450029 = 51543761) B51543761
theorem B4756315 : Blo 1319478 4756315 := bstep (se 1 (by rfl) ⟨3567236, by rfl⟩ : syracuseStep 4756315 = 7134473) B7134473
theorem B5010281 : Blo 1319478 5010281 := bstep (se 2 (by rfl) ⟨1878855, by rfl⟩ : syracuseStep 5010281 = 3757711) B3757711
theorem B10032011 : Blo 1319478 10032011 := bstep (se 1 (by rfl) ⟨7524008, by rfl⟩ : syracuseStep 10032011 = 15048017) B15048017
theorem B2970665 : Blo 1319478 2970665 := bstep (se 2 (by rfl) ⟨1113999, by rfl⟩ : syracuseStep 2970665 = 2227999) B2227999
theorem B2675759 : Blo 1319478 2675759 := bstep (se 1 (by rfl) ⟨2006819, by rfl⟩ : syracuseStep 2675759 = 4013639) B4013639
theorem B1979513 : Blo 1319478 1979513 := bstep (se 2 (by rfl) ⟨742317, by rfl⟩ : syracuseStep 1979513 = 1484635) B1484635
theorem B34289243 : Blo 1319478 34289243 := bstep (se 1 (by rfl) ⟨25716932, by rfl⟩ : syracuseStep 34289243 = 51433865) B51433865
theorem B4454135 : Blo 1319478 4454135 := bstep (se 1 (by rfl) ⟨3340601, by rfl⟩ : syracuseStep 4454135 = 6681203) B6681203
theorem B1980287 : Blo 1319478 1980287 := bstep (se 1 (by rfl) ⟨1485215, by rfl⟩ : syracuseStep 1980287 = 2970431) B2970431
theorem B15046559 : Blo 1319478 15046559 := bstep (se 1 (by rfl) ⟨11284919, by rfl⟩ : syracuseStep 15046559 = 22569839) B22569839
theorem B9779449 : Blo 1319478 9779449 := bstep (se 2 (by rfl) ⟨3667293, by rfl⟩ : syracuseStep 9779449 = 7334587) B7334587
theorem B2971943 : Blo 1319478 2971943 := bstep (se 1 (by rfl) ⟨2228957, by rfl⟩ : syracuseStep 2971943 = 4457915) B4457915
theorem B34322899 : Blo 1319478 34322899 := bstep (se 1 (by rfl) ⟨25742174, by rfl⟩ : syracuseStep 34322899 = 51484349) B51484349
theorem B1980905 : Blo 1319478 1980905 := bstep (se 2 (by rfl) ⟨742839, by rfl⟩ : syracuseStep 1980905 = 1485679) B1485679
theorem B4454891 : Blo 1319478 4454891 := bstep (se 1 (by rfl) ⟨3341168, by rfl⟩ : syracuseStep 4454891 = 6682337) B6682337
theorem B4758047 : Blo 1319478 4758047 := bstep (se 1 (by rfl) ⟨3568535, by rfl⟩ : syracuseStep 4758047 = 7137071) B7137071
theorem B2972303 : Blo 1319478 2972303 := bstep (se 1 (by rfl) ⟨2229227, by rfl⟩ : syracuseStep 2972303 = 4458455) B4458455
theorem B5642905 : Blo 1319478 5642905 := bstep (se 2 (by rfl) ⟨2116089, by rfl⟩ : syracuseStep 5642905 = 4232179) B4232179
theorem B1784575 : Blo 1319478 1784575 := bstep (se 1 (by rfl) ⟨1338431, by rfl⟩ : syracuseStep 1784575 = 2676863) B2676863
theorem B1981223 : Blo 1319478 1981223 := bstep (se 1 (by rfl) ⟨1485917, by rfl⟩ : syracuseStep 1981223 = 2971835) B2971835
theorem B4455215 : Blo 1319478 4455215 := bstep (se 1 (by rfl) ⟨3341411, by rfl⟩ : syracuseStep 4455215 = 6682823) B6682823
theorem B2227135 : Blo 1319478 2227135 := bstep (se 1 (by rfl) ⟨1670351, by rfl⟩ : syracuseStep 2227135 = 3340703) B3340703
theorem B16055333 : Blo 1319478 16055333 := bstep (se 4 (by rfl) ⟨1505187, by rfl⟩ : syracuseStep 16055333 = 3010375) B3010375
theorem B1981679 : Blo 1319478 1981679 := bstep (se 1 (by rfl) ⟨1486259, by rfl⟩ : syracuseStep 1981679 = 2972519) B2972519
theorem B10034441 : Blo 1319478 10034441 := bstep (se 2 (by rfl) ⟨3762915, by rfl⟩ : syracuseStep 10034441 = 7525831) B7525831
theorem B1981751 : Blo 1319478 1981751 := bstep (se 1 (by rfl) ⟨1486313, by rfl⟩ : syracuseStep 1981751 = 2972627) B2972627
theorem B2227513 : Blo 1319478 2227513 := bstep (se 2 (by rfl) ⟨835317, by rfl⟩ : syracuseStep 2227513 = 1670635) B1670635
theorem B1981823 : Blo 1319478 1981823 := bstep (se 1 (by rfl) ⟨1486367, by rfl⟩ : syracuseStep 1981823 = 2972735) B2972735
theorem B16924099 : Blo 1319478 16924099 := bstep (se 1 (by rfl) ⟨12693074, by rfl⟩ : syracuseStep 16924099 = 25386149) B25386149
theorem B1981931 : Blo 1319478 1981931 := bstep (se 1 (by rfl) ⟨1486448, by rfl⟩ : syracuseStep 1981931 = 2972897) B2972897
theorem B3341807 : Blo 1319478 3341807 := bstep (se 1 (by rfl) ⟨2506355, by rfl⟩ : syracuseStep 3341807 = 5012711) B5012711
theorem B3759635 : Blo 1319478 3759635 := bstep (se 1 (by rfl) ⟨2819726, by rfl⟩ : syracuseStep 3759635 = 5639453) B5639453
theorem B2973203 : Blo 1319478 2973203 := bstep (se 1 (by rfl) ⟨2229902, by rfl⟩ : syracuseStep 2973203 = 4459805) B4459805
theorem B10714781 : Blo 1319478 10714781 := bstep (se 3 (by rfl) ⟨2009021, by rfl⟩ : syracuseStep 10714781 = 4018043) B4018043
theorem B15236795 : Blo 1319478 15236795 := bstep (se 1 (by rfl) ⟨11427596, by rfl⟩ : syracuseStep 15236795 = 22855193) B22855193
theorem B3342323 : Blo 1319478 3342323 := bstep (se 1 (by rfl) ⟨2506742, by rfl⟩ : syracuseStep 3342323 = 5013485) B5013485
theorem B6021175 : Blo 1319478 6021175 := bstep (se 1 (by rfl) ⟨4515881, by rfl⟩ : syracuseStep 6021175 = 9031763) B9031763
theorem B3342505 : Blo 1319478 3342505 := bstep (se 2 (by rfl) ⟨1253439, by rfl⟩ : syracuseStep 3342505 = 2506879) B2506879
theorem B25739693 : Blo 1319478 25739693 := bstep (se 3 (by rfl) ⟨4826192, by rfl⟩ : syracuseStep 25739693 = 9652385) B9652385
theorem B5013971 : Blo 1319478 5013971 := bstep (se 1 (by rfl) ⟨3760478, by rfl⟩ : syracuseStep 5013971 = 7520957) B7520957
theorem B28541429 : Blo 1319478 28541429 := bstep (se 5 (by rfl) ⟨1337879, by rfl⟩ : syracuseStep 28541429 = 2675759) B2675759
theorem B4457051 : Blo 1319478 4457051 := bstep (se 1 (by rfl) ⟨3342788, by rfl⟩ : syracuseStep 4457051 = 6685577) B6685577
theorem B7627385 : Blo 1319478 7627385 := bstep (se 2 (by rfl) ⟨2860269, by rfl⟩ : syracuseStep 7627385 = 5720539) B5720539
theorem B1319675 : Blo 1319478 1319675 := bstep (se 1 (by rfl) ⟨989756, by rfl⟩ : syracuseStep 1319675 = 1979513) B1979513
theorem B12682003 : Blo 1319478 12682003 := bstep (se 1 (by rfl) ⟨9511502, by rfl⟩ : syracuseStep 12682003 = 19023005) B19023005
theorem B66937693 : Blo 1319478 66937693 := bstep (se 3 (by rfl) ⟨12550817, by rfl⟩ : syracuseStep 66937693 = 25101635) B25101635
theorem B8029127 : Blo 1319478 8029127 := bstep (se 1 (by rfl) ⟨6021845, by rfl⟩ : syracuseStep 8029127 = 12043691) B12043691
theorem B6341753 : Blo 1319478 6341753 := bstep (se 2 (by rfl) ⟨2378157, by rfl⟩ : syracuseStep 6341753 = 4756315) B4756315
theorem B1320191 : Blo 1319478 1320191 := bstep (se 1 (by rfl) ⟨990143, by rfl⟩ : syracuseStep 1320191 = 1980287) B1980287
theorem B2229815 : Blo 1319478 2229815 := bstep (se 1 (by rfl) ⟨1672361, by rfl⟩ : syracuseStep 2229815 = 3344723) B3344723
theorem B28575341 : Blo 1319478 28575341 := bstep (se 3 (by rfl) ⟨5357876, by rfl⟩ : syracuseStep 28575341 = 10715753) B10715753
theorem B1320603 : Blo 1319478 1320603 := bstep (se 1 (by rfl) ⟨990452, by rfl⟩ : syracuseStep 1320603 = 1980905) B1980905
theorem B3172031 : Blo 1319478 3172031 := bstep (se 1 (by rfl) ⟨2379023, by rfl⟩ : syracuseStep 3172031 = 4758047) B4758047
theorem B12683081 : Blo 1319478 12683081 := bstep (se 2 (by rfl) ⟨4756155, by rfl⟩ : syracuseStep 12683081 = 9512311) B9512311
theorem B1320815 : Blo 1319478 1320815 := bstep (se 1 (by rfl) ⟨990611, by rfl⟩ : syracuseStep 1320815 = 1981223) B1981223
theorem B1321119 : Blo 1319478 1321119 := bstep (se 1 (by rfl) ⟨990839, by rfl⟩ : syracuseStep 1321119 = 1981679) B1981679
theorem B1321167 : Blo 1319478 1321167 := bstep (se 1 (by rfl) ⟨990875, by rfl⟩ : syracuseStep 1321167 = 1981751) B1981751
theorem B1321215 : Blo 1319478 1321215 := bstep (se 1 (by rfl) ⟨990911, by rfl⟩ : syracuseStep 1321215 = 1981823) B1981823
theorem B1321287 : Blo 1319478 1321287 := bstep (se 1 (by rfl) ⟨990965, by rfl⟩ : syracuseStep 1321287 = 1981931) B1981931
theorem B216820547 : Blo 1319478 216820547 := bstep (se 1 (by rfl) ⟨162615410, by rfl⟩ : syracuseStep 216820547 = 325230821) B325230821
theorem B21425219 : Blo 1319478 21425219 := bstep (se 1 (by rfl) ⟨16068914, by rfl⟩ : syracuseStep 21425219 = 32137829) B32137829
theorem B6688007 : Blo 1319478 6688007 := bstep (se 1 (by rfl) ⟨5016005, by rfl⟩ : syracuseStep 6688007 = 10032011) B10032011
theorem B2821385 : Blo 1319478 2821385 := bstep (se 2 (by rfl) ⟨1058019, by rfl⟩ : syracuseStep 2821385 = 2116039) B2116039
theorem B45763865 : Blo 1319478 45763865 := bstep (se 2 (by rfl) ⟨17161449, by rfl⟩ : syracuseStep 45763865 = 34322899) B34322899
theorem B183266705 : Blo 1319478 183266705 := bstep (se 2 (by rfl) ⟨68725014, by rfl⟩ : syracuseStep 183266705 = 137450029) B137450029
theorem B7523873 : Blo 1319478 7523873 := bstep (se 2 (by rfl) ⟨2821452, by rfl⟩ : syracuseStep 7523873 = 5642905) B5642905
theorem B22859495 : Blo 1319478 22859495 := bstep (se 1 (by rfl) ⟨17144621, by rfl⟩ : syracuseStep 22859495 = 34289243) B34289243
theorem B2969423 : Blo 1319478 2969423 := bstep (se 1 (by rfl) ⟨2227067, by rfl⟩ : syracuseStep 2969423 = 4454135) B4454135
theorem B2969513 : Blo 1319478 2969513 := bstep (se 2 (by rfl) ⟨1113567, by rfl⟩ : syracuseStep 2969513 = 2227135) B2227135
theorem B10031039 : Blo 1319478 10031039 := bstep (se 1 (by rfl) ⟨7523279, by rfl⟩ : syracuseStep 10031039 = 15046559) B15046559
theorem B6680555 : Blo 1319478 6680555 := bstep (se 1 (by rfl) ⟨5010416, by rfl⟩ : syracuseStep 6680555 = 10020833) B10020833
theorem B2969927 : Blo 1319478 2969927 := bstep (se 1 (by rfl) ⟨2227445, by rfl⟩ : syracuseStep 2969927 = 4454891) B4454891
theorem B2970017 : Blo 1319478 2970017 := bstep (se 2 (by rfl) ⟨1113756, by rfl⟩ : syracuseStep 2970017 = 2227513) B2227513
theorem B2970143 : Blo 1319478 2970143 := bstep (se 1 (by rfl) ⟨2227607, by rfl⟩ : syracuseStep 2970143 = 4455215) B4455215
theorem B22565465 : Blo 1319478 22565465 := bstep (se 2 (by rfl) ⟨8462049, by rfl⟩ : syracuseStep 22565465 = 16924099) B16924099
theorem B10703555 : Blo 1319478 10703555 := bstep (se 1 (by rfl) ⟨8027666, by rfl⟩ : syracuseStep 10703555 = 16055333) B16055333
theorem B1585991 : Blo 1319478 1585991 := bstep (se 1 (by rfl) ⟨1189493, by rfl⟩ : syracuseStep 1585991 = 2378987) B2378987
theorem B6689627 : Blo 1319478 6689627 := bstep (se 1 (by rfl) ⟨5017220, by rfl⟩ : syracuseStep 6689627 = 10034441) B10034441
theorem B12055511 : Blo 1319478 12055511 := bstep (se 1 (by rfl) ⟨9041633, by rfl⟩ : syracuseStep 12055511 = 18083267) B18083267
theorem B3388603 : Blo 1319478 3388603 := bstep (se 1 (by rfl) ⟨2541452, by rfl⟩ : syracuseStep 3388603 = 5082905) B5082905
theorem B32126233 : Blo 1319478 32126233 := bstep (se 2 (by rfl) ⟨12047337, by rfl⟩ : syracuseStep 32126233 = 24094675) B24094675
theorem B13039265 : Blo 1319478 13039265 := bstep (se 2 (by rfl) ⟨4889724, by rfl⟩ : syracuseStep 13039265 = 9779449) B9779449
theorem B3340187 : Blo 1319478 3340187 := bstep (se 1 (by rfl) ⟨2505140, by rfl⟩ : syracuseStep 3340187 = 5010281) B5010281
theorem B1980443 : Blo 1319478 1980443 := bstep (se 1 (by rfl) ⟨1485332, by rfl⟩ : syracuseStep 1980443 = 2970665) B2970665
theorem B3758201 : Blo 1319478 3758201 := bstep (se 2 (by rfl) ⟨1409325, by rfl⟩ : syracuseStep 3758201 = 2818651) B2818651
theorem B2971871 : Blo 1319478 2971871 := bstep (se 1 (by rfl) ⟨2228903, by rfl⟩ : syracuseStep 2971871 = 4457807) B4457807
theorem B9517733 : Blo 1319478 9517733 := bstep (se 4 (by rfl) ⟨892287, by rfl⟩ : syracuseStep 9517733 = 1784575) B1784575
theorem B10025693 : Blo 1319478 10025693 := bstep (se 3 (by rfl) ⟨1879817, by rfl⟩ : syracuseStep 10025693 = 3759635) B3759635
theorem B1981295 : Blo 1319478 1981295 := bstep (se 1 (by rfl) ⟨1485971, by rfl⟩ : syracuseStep 1981295 = 2971943) B2971943
theorem B2972537 : Blo 1319478 2972537 := bstep (se 2 (by rfl) ⟨1114701, by rfl⟩ : syracuseStep 2972537 = 2229403) B2229403
theorem B2972681 : Blo 1319478 2972681 := bstep (se 2 (by rfl) ⟨1114755, by rfl⟩ : syracuseStep 2972681 = 2229511) B2229511
theorem B1981535 : Blo 1319478 1981535 := bstep (se 1 (by rfl) ⟨1486151, by rfl⟩ : syracuseStep 1981535 = 2972303) B2972303
theorem B4758635 : Blo 1319478 4758635 := bstep (se 1 (by rfl) ⟨3568976, by rfl⟩ : syracuseStep 4758635 = 7137953) B7137953
theorem B7134319 : Blo 1319478 7134319 := bstep (se 1 (by rfl) ⟨5350739, by rfl⟩ : syracuseStep 7134319 = 10701479) B10701479
theorem B40631453 : Blo 1319478 40631453 := bstep (se 3 (by rfl) ⟨7618397, by rfl⟩ : syracuseStep 40631453 = 15236795) B15236795
theorem B21421255 : Blo 1319478 21421255 := bstep (se 1 (by rfl) ⟨16065941, by rfl⟩ : syracuseStep 21421255 = 32131883) B32131883
theorem B2227871 : Blo 1319478 2227871 := bstep (se 1 (by rfl) ⟨1670903, by rfl⟩ : syracuseStep 2227871 = 3341807) B3341807
theorem B1982135 : Blo 1319478 1982135 := bstep (se 1 (by rfl) ⟨1486601, by rfl⟩ : syracuseStep 1982135 = 2973203) B2973203
theorem B25386695 : Blo 1319478 25386695 := bstep (se 1 (by rfl) ⟨19040021, by rfl⟩ : syracuseStep 25386695 = 38080043) B38080043
theorem B7143187 : Blo 1319478 7143187 := bstep (se 1 (by rfl) ⟨5357390, by rfl⟩ : syracuseStep 7143187 = 10714781) B10714781
theorem B2228215 : Blo 1319478 2228215 := bstep (se 1 (by rfl) ⟨1671161, by rfl⟩ : syracuseStep 2228215 = 3342323) B3342323
theorem B8028233 : Blo 1319478 8028233 := bstep (se 2 (by rfl) ⟨3010587, by rfl⟩ : syracuseStep 8028233 = 6021175) B6021175
theorem B4456673 : Blo 1319478 4456673 := bstep (se 2 (by rfl) ⟨1671252, by rfl⟩ : syracuseStep 4456673 = 3342505) B3342505
theorem B12689693 : Blo 1319478 12689693 := bstep (se 3 (by rfl) ⟨2379317, by rfl⟩ : syracuseStep 12689693 = 4758635) B4758635
theorem B3342647 : Blo 1319478 3342647 := bstep (se 1 (by rfl) ⟨2506985, by rfl⟩ : syracuseStep 3342647 = 5013971) B5013971
theorem B7135703 : Blo 1319478 7135703 := bstep (se 1 (by rfl) ⟨5351777, by rfl⟩ : syracuseStep 7135703 = 10703555) B10703555
theorem B16909337 : Blo 1319478 16909337 := bstep (se 2 (by rfl) ⟨6341001, by rfl⟩ : syracuseStep 16909337 = 12682003) B12682003
theorem B8692843 : Blo 1319478 8692843 := bstep (se 1 (by rfl) ⟨6519632, by rfl⟩ : syracuseStep 8692843 = 13039265) B13039265
theorem B2114687 : Blo 1319478 2114687 := bstep (se 1 (by rfl) ⟨1586015, by rfl⟩ : syracuseStep 2114687 = 3172031) B3172031
theorem B8455387 : Blo 1319478 8455387 := bstep (se 1 (by rfl) ⟨6341540, by rfl⟩ : syracuseStep 8455387 = 12683081) B12683081
theorem B1320295 : Blo 1319478 1320295 := bstep (se 1 (by rfl) ⟨990221, by rfl⟩ : syracuseStep 1320295 = 1980443) B1980443
theorem B9512425 : Blo 1319478 9512425 := bstep (se 2 (by rfl) ⟨3567159, by rfl⟩ : syracuseStep 9512425 = 7134319) B7134319
theorem B1320863 : Blo 1319478 1320863 := bstep (se 1 (by rfl) ⟨990647, by rfl⟩ : syracuseStep 1320863 = 1981295) B1981295
theorem B1321023 : Blo 1319478 1321023 := bstep (se 1 (by rfl) ⟨990767, by rfl⟩ : syracuseStep 1321023 = 1981535) B1981535
theorem B4458671 : Blo 1319478 4458671 := bstep (se 1 (by rfl) ⟨3344003, by rfl⟩ : syracuseStep 4458671 = 6688007) B6688007
theorem B30509243 : Blo 1319478 30509243 := bstep (se 1 (by rfl) ⟨22881932, by rfl⟩ : syracuseStep 30509243 = 45763865) B45763865
theorem B4229309 : Blo 1319478 4229309 := bstep (se 3 (by rfl) ⟨792995, by rfl⟩ : syracuseStep 4229309 = 1585991) B1585991
theorem B122177803 : Blo 1319478 122177803 := bstep (se 1 (by rfl) ⟨91633352, by rfl⟩ : syracuseStep 122177803 = 183266705) B183266705
theorem B5015915 : Blo 1319478 5015915 := bstep (se 1 (by rfl) ⟨3761936, by rfl⟩ : syracuseStep 5015915 = 7523873) B7523873
theorem B1485247 : Blo 1319478 1485247 := bstep (se 1 (by rfl) ⟨1113935, by rfl⟩ : syracuseStep 1485247 = 2227871) B2227871
theorem B1321423 : Blo 1319478 1321423 := bstep (se 1 (by rfl) ⟨991067, by rfl⟩ : syracuseStep 1321423 = 1982135) B1982135
theorem B15239663 : Blo 1319478 15239663 := bstep (se 1 (by rfl) ⟨11429747, by rfl⟩ : syracuseStep 15239663 = 22859495) B22859495
theorem B32148029 : Blo 1319478 32148029 := bstep (se 3 (by rfl) ⟨6027755, by rfl⟩ : syracuseStep 32148029 = 12055511) B12055511
theorem B6687359 : Blo 1319478 6687359 := bstep (se 1 (by rfl) ⟨5015519, by rfl⟩ : syracuseStep 6687359 = 10031039) B10031039
theorem B16911341 : Blo 1319478 16911341 := bstep (se 3 (by rfl) ⟨3170876, by rfl⟩ : syracuseStep 16911341 = 6341753) B6341753
theorem B15043643 : Blo 1319478 15043643 := bstep (se 1 (by rfl) ⟨11282732, by rfl⟩ : syracuseStep 15043643 = 22565465) B22565465
theorem B4459751 : Blo 1319478 4459751 := bstep (se 1 (by rfl) ⟨3344813, by rfl⟩ : syracuseStep 4459751 = 6689627) B6689627
theorem B5352751 : Blo 1319478 5352751 := bstep (se 1 (by rfl) ⟨4014563, by rfl⟩ : syracuseStep 5352751 = 8029127) B8029127
theorem B1486543 : Blo 1319478 1486543 := bstep (se 1 (by rfl) ⟨1114907, by rfl⟩ : syracuseStep 1486543 = 2229815) B2229815
theorem B19050227 : Blo 1319478 19050227 := bstep (se 1 (by rfl) ⟨14287670, by rfl⟩ : syracuseStep 19050227 = 28575341) B28575341
theorem B4518137 : Blo 1319478 4518137 := bstep (se 2 (by rfl) ⟨1694301, by rfl⟩ : syracuseStep 4518137 = 3388603) B3388603
theorem B28561673 : Blo 1319478 28561673 := bstep (se 2 (by rfl) ⟨10710627, by rfl⟩ : syracuseStep 28561673 = 21421255) B21421255
theorem B6345155 : Blo 1319478 6345155 := bstep (se 1 (by rfl) ⟨4758866, by rfl⟩ : syracuseStep 6345155 = 9517733) B9517733
theorem B14283479 : Blo 1319478 14283479 := bstep (se 1 (by rfl) ⟨10712609, by rfl⟩ : syracuseStep 14283479 = 21425219) B21425219
theorem B27087635 : Blo 1319478 27087635 := bstep (se 1 (by rfl) ⟨20315726, by rfl⟩ : syracuseStep 27087635 = 40631453) B40631453
theorem B1880923 : Blo 1319478 1880923 := bstep (se 1 (by rfl) ⟨1410692, by rfl⟩ : syracuseStep 1880923 = 2821385) B2821385
theorem B9524249 : Blo 1319478 9524249 := bstep (se 2 (by rfl) ⟨3571593, by rfl⟩ : syracuseStep 9524249 = 7143187) B7143187
theorem B1979615 : Blo 1319478 1979615 := bstep (se 1 (by rfl) ⟨1484711, by rfl⟩ : syracuseStep 1979615 = 2969423) B2969423
theorem B1979675 : Blo 1319478 1979675 := bstep (se 1 (by rfl) ⟨1484756, by rfl⟩ : syracuseStep 1979675 = 2969513) B2969513
theorem B4453703 : Blo 1319478 4453703 := bstep (se 1 (by rfl) ⟨3340277, by rfl⟩ : syracuseStep 4453703 = 6680555) B6680555
theorem B2970953 : Blo 1319478 2970953 := bstep (se 2 (by rfl) ⟨1114107, by rfl⟩ : syracuseStep 2970953 = 2228215) B2228215
theorem B1979951 : Blo 1319478 1979951 := bstep (se 1 (by rfl) ⟨1484963, by rfl⟩ : syracuseStep 1979951 = 2969927) B2969927
theorem B1980011 : Blo 1319478 1980011 := bstep (se 1 (by rfl) ⟨1485008, by rfl⟩ : syracuseStep 1980011 = 2970017) B2970017
theorem B17159795 : Blo 1319478 17159795 := bstep (se 1 (by rfl) ⟨12869846, by rfl⟩ : syracuseStep 17159795 = 25739693) B25739693
theorem B19027619 : Blo 1319478 19027619 := bstep (se 1 (by rfl) ⟨14270714, by rfl⟩ : syracuseStep 19027619 = 28541429) B28541429
theorem B1980095 : Blo 1319478 1980095 := bstep (se 1 (by rfl) ⟨1485071, by rfl⟩ : syracuseStep 1980095 = 2970143) B2970143
theorem B2971367 : Blo 1319478 2971367 := bstep (se 1 (by rfl) ⟨2228525, by rfl⟩ : syracuseStep 2971367 = 4457051) B4457051
theorem B89250257 : Blo 1319478 89250257 := bstep (se 2 (by rfl) ⟨33468846, by rfl⟩ : syracuseStep 89250257 = 66937693) B66937693
theorem B2226791 : Blo 1319478 2226791 := bstep (se 1 (by rfl) ⟨1670093, by rfl⟩ : syracuseStep 2226791 = 3340187) B3340187
theorem B2505467 : Blo 1319478 2505467 := bstep (se 1 (by rfl) ⟨1879100, by rfl⟩ : syracuseStep 2505467 = 3758201) B3758201
theorem B1981247 : Blo 1319478 1981247 := bstep (se 1 (by rfl) ⟨1485935, by rfl⟩ : syracuseStep 1981247 = 2971871) B2971871
theorem B20339693 : Blo 1319478 20339693 := bstep (se 3 (by rfl) ⟨3813692, by rfl⟩ : syracuseStep 20339693 = 7627385) B7627385
theorem B42834977 : Blo 1319478 42834977 := bstep (se 2 (by rfl) ⟨16063116, by rfl⟩ : syracuseStep 42834977 = 32126233) B32126233
theorem B6683795 : Blo 1319478 6683795 := bstep (se 1 (by rfl) ⟨5012846, by rfl⟩ : syracuseStep 6683795 = 10025693) B10025693
theorem B144547031 : Blo 1319478 144547031 := bstep (se 1 (by rfl) ⟨108410273, by rfl⟩ : syracuseStep 144547031 = 216820547) B216820547
theorem B1981691 : Blo 1319478 1981691 := bstep (se 1 (by rfl) ⟨1486268, by rfl⟩ : syracuseStep 1981691 = 2972537) B2972537
theorem B1981787 : Blo 1319478 1981787 := bstep (se 1 (by rfl) ⟨1486340, by rfl⟩ : syracuseStep 1981787 = 2972681) B2972681
theorem B16924463 : Blo 1319478 16924463 := bstep (se 1 (by rfl) ⟨12693347, by rfl⟩ : syracuseStep 16924463 = 25386695) B25386695
theorem B2228431 : Blo 1319478 2228431 := bstep (se 1 (by rfl) ⟨1671323, by rfl⟩ : syracuseStep 2228431 = 3342647) B3342647
theorem B11272891 : Blo 1319478 11272891 := bstep (se 1 (by rfl) ⟨8454668, by rfl⟩ : syracuseStep 11272891 = 16909337) B16909337
theorem B6349499 : Blo 1319478 6349499 := bstep (se 1 (by rfl) ⟨4762124, by rfl⟩ : syracuseStep 6349499 = 9524249) B9524249
theorem B1319743 : Blo 1319478 1319743 := bstep (se 1 (by rfl) ⟨989807, by rfl⟩ : syracuseStep 1319743 = 1979615) B1979615
theorem B1319783 : Blo 1319478 1319783 := bstep (se 1 (by rfl) ⟨989837, by rfl⟩ : syracuseStep 1319783 = 1979675) B1979675
theorem B1319967 : Blo 1319478 1319967 := bstep (se 1 (by rfl) ⟨989975, by rfl⟩ : syracuseStep 1319967 = 1979951) B1979951
theorem B1320007 : Blo 1319478 1320007 := bstep (se 1 (by rfl) ⟨990005, by rfl⟩ : syracuseStep 1320007 = 1980011) B1980011
theorem B2507897 : Blo 1319478 2507897 := bstep (se 2 (by rfl) ⟨940461, by rfl⟩ : syracuseStep 2507897 = 1880923) B1880923
theorem B1320063 : Blo 1319478 1320063 := bstep (se 1 (by rfl) ⟨990047, by rfl⟩ : syracuseStep 1320063 = 1980095) B1980095
theorem B2819539 : Blo 1319478 2819539 := bstep (se 1 (by rfl) ⟨2114654, by rfl⟩ : syracuseStep 2819539 = 4229309) B4229309
theorem B3343943 : Blo 1319478 3343943 := bstep (se 1 (by rfl) ⟨2507957, by rfl⟩ : syracuseStep 3343943 = 5015915) B5015915
theorem B11273849 : Blo 1319478 11273849 := bstep (se 2 (by rfl) ⟨4227693, by rfl⟩ : syracuseStep 11273849 = 8455387) B8455387
theorem B59500171 : Blo 1319478 59500171 := bstep (se 1 (by rfl) ⟨44625128, by rfl⟩ : syracuseStep 59500171 = 89250257) B89250257
theorem B10159775 : Blo 1319478 10159775 := bstep (se 1 (by rfl) ⟨7619831, by rfl⟩ : syracuseStep 10159775 = 15239663) B15239663
theorem B7137001 : Blo 1319478 7137001 := bstep (se 2 (by rfl) ⟨2676375, by rfl⟩ : syracuseStep 7137001 = 5352751) B5352751
theorem B1484527 : Blo 1319478 1484527 := bstep (se 1 (by rfl) ⟨1113395, by rfl⟩ : syracuseStep 1484527 = 2226791) B2226791
theorem B4458239 : Blo 1319478 4458239 := bstep (se 1 (by rfl) ⟨3343679, by rfl⟩ : syracuseStep 4458239 = 6687359) B6687359
theorem B1320831 : Blo 1319478 1320831 := bstep (se 1 (by rfl) ⟨990623, by rfl⟩ : syracuseStep 1320831 = 1981247) B1981247
theorem B12683233 : Blo 1319478 12683233 := bstep (se 2 (by rfl) ⟨4756212, by rfl⟩ : syracuseStep 12683233 = 9512425) B9512425
theorem B11274227 : Blo 1319478 11274227 := bstep (se 1 (by rfl) ⟨8455670, by rfl⟩ : syracuseStep 11274227 = 16911341) B16911341
theorem B13559795 : Blo 1319478 13559795 := bstep (se 1 (by rfl) ⟨10169846, by rfl⟩ : syracuseStep 13559795 = 20339693) B20339693
theorem B10029095 : Blo 1319478 10029095 := bstep (se 1 (by rfl) ⟨7521821, by rfl⟩ : syracuseStep 10029095 = 15043643) B15043643
theorem B96364687 : Blo 1319478 96364687 := bstep (se 1 (by rfl) ⟨72273515, by rfl⟩ : syracuseStep 96364687 = 144547031) B144547031
theorem B1321127 : Blo 1319478 1321127 := bstep (se 1 (by rfl) ⟨990845, by rfl⟩ : syracuseStep 1321127 = 1981691) B1981691
theorem B1321191 : Blo 1319478 1321191 := bstep (se 1 (by rfl) ⟨990893, by rfl⟩ : syracuseStep 1321191 = 1981787) B1981787
theorem B12700151 : Blo 1319478 12700151 := bstep (se 1 (by rfl) ⟨9525113, by rfl⟩ : syracuseStep 12700151 = 19050227) B19050227
theorem B11282975 : Blo 1319478 11282975 := bstep (se 1 (by rfl) ⟨8462231, by rfl⟩ : syracuseStep 11282975 = 16924463) B16924463
theorem B5352155 : Blo 1319478 5352155 := bstep (se 1 (by rfl) ⟨4014116, by rfl⟩ : syracuseStep 5352155 = 8028233) B8028233
theorem B19041115 : Blo 1319478 19041115 := bstep (se 1 (by rfl) ⟨14280836, by rfl⟩ : syracuseStep 19041115 = 28561673) B28561673
theorem B4230103 : Blo 1319478 4230103 := bstep (se 1 (by rfl) ⟨3172577, by rfl⟩ : syracuseStep 4230103 = 6345155) B6345155
theorem B5639165 : Blo 1319478 5639165 := bstep (se 3 (by rfl) ⟨1057343, by rfl⟩ : syracuseStep 5639165 = 2114687) B2114687
theorem B9522319 : Blo 1319478 9522319 := bstep (se 1 (by rfl) ⟨7141739, by rfl⟩ : syracuseStep 9522319 = 14283479) B14283479
theorem B2969135 : Blo 1319478 2969135 := bstep (se 1 (by rfl) ⟨2226851, by rfl⟩ : syracuseStep 2969135 = 4453703) B4453703
theorem B11439863 : Blo 1319478 11439863 := bstep (se 1 (by rfl) ⟨8579897, by rfl⟩ : syracuseStep 11439863 = 17159795) B17159795
theorem B12685079 : Blo 1319478 12685079 := bstep (se 1 (by rfl) ⟨9513809, by rfl⟩ : syracuseStep 12685079 = 19027619) B19027619
theorem B72233693 : Blo 1319478 72233693 := bstep (se 3 (by rfl) ⟨13543817, by rfl⟩ : syracuseStep 72233693 = 27087635) B27087635
theorem B2971115 : Blo 1319478 2971115 := bstep (se 1 (by rfl) ⟨2228336, by rfl⟩ : syracuseStep 2971115 = 4456673) B4456673
theorem B8459795 : Blo 1319478 8459795 := bstep (se 1 (by rfl) ⟨6344846, by rfl⟩ : syracuseStep 8459795 = 12689693) B12689693
theorem B4757135 : Blo 1319478 4757135 := bstep (se 1 (by rfl) ⟨3567851, by rfl⟩ : syracuseStep 4757135 = 7135703) B7135703
theorem B162903737 : Blo 1319478 162903737 := bstep (se 2 (by rfl) ⟨61088901, by rfl⟩ : syracuseStep 162903737 = 122177803) B122177803
theorem B1980329 : Blo 1319478 1980329 := bstep (se 2 (by rfl) ⟨742623, by rfl⟩ : syracuseStep 1980329 = 1485247) B1485247
theorem B12048365 : Blo 1319478 12048365 := bstep (se 3 (by rfl) ⟨2259068, by rfl⟩ : syracuseStep 12048365 = 4518137) B4518137
theorem B1980635 : Blo 1319478 1980635 := bstep (se 1 (by rfl) ⟨1485476, by rfl⟩ : syracuseStep 1980635 = 2970953) B2970953
theorem B1980911 : Blo 1319478 1980911 := bstep (se 1 (by rfl) ⟨1485683, by rfl⟩ : syracuseStep 1980911 = 2971367) B2971367
theorem B2972447 : Blo 1319478 2972447 := bstep (se 1 (by rfl) ⟨2229335, by rfl⟩ : syracuseStep 2972447 = 4458671) B4458671
theorem B20339495 : Blo 1319478 20339495 := bstep (se 1 (by rfl) ⟨15254621, by rfl⟩ : syracuseStep 20339495 = 30509243) B30509243
theorem B11590457 : Blo 1319478 11590457 := bstep (se 2 (by rfl) ⟨4346421, by rfl⟩ : syracuseStep 11590457 = 8692843) B8692843
theorem B85728077 : Blo 1319478 85728077 := bstep (se 3 (by rfl) ⟨16074014, by rfl⟩ : syracuseStep 85728077 = 32148029) B32148029
theorem B1670311 : Blo 1319478 1670311 := bstep (se 1 (by rfl) ⟨1252733, by rfl⟩ : syracuseStep 1670311 = 2505467) B2505467
theorem B28556651 : Blo 1319478 28556651 := bstep (se 1 (by rfl) ⟨21417488, by rfl⟩ : syracuseStep 28556651 = 42834977) B42834977
theorem B4455863 : Blo 1319478 4455863 := bstep (se 1 (by rfl) ⟨3341897, by rfl⟩ : syracuseStep 4455863 = 6683795) B6683795
theorem B2973167 : Blo 1319478 2973167 := bstep (se 1 (by rfl) ⟨2229875, by rfl⟩ : syracuseStep 2973167 = 4459751) B4459751
theorem B1982057 : Blo 1319478 1982057 := bstep (se 2 (by rfl) ⟨743271, by rfl⟩ : syracuseStep 1982057 = 1486543) B1486543
theorem B1671931 : Blo 1319478 1671931 := bstep (se 1 (by rfl) ⟨1253948, by rfl⟩ : syracuseStep 1671931 = 2507897) B2507897
theorem B2229295 : Blo 1319478 2229295 := bstep (se 1 (by rfl) ⟨1671971, by rfl⟩ : syracuseStep 2229295 = 3343943) B3343943
theorem B108602491 : Blo 1319478 108602491 := bstep (se 1 (by rfl) ⟨81451868, by rfl⟩ : syracuseStep 108602491 = 162903737) B162903737
theorem B25388153 : Blo 1319478 25388153 := bstep (se 2 (by rfl) ⟨9520557, by rfl⟩ : syracuseStep 25388153 = 19041115) B19041115
theorem B1320219 : Blo 1319478 1320219 := bstep (se 1 (by rfl) ⟨990164, by rfl⟩ : syracuseStep 1320219 = 1980329) B1980329
theorem B6686063 : Blo 1319478 6686063 := bstep (se 1 (by rfl) ⟨5014547, by rfl⟩ : syracuseStep 6686063 = 10029095) B10029095
theorem B1320423 : Blo 1319478 1320423 := bstep (se 1 (by rfl) ⟨990317, by rfl⟩ : syracuseStep 1320423 = 1980635) B1980635
theorem B50742773 : Blo 1319478 50742773 := bstep (se 5 (by rfl) ⟨2378567, by rfl⟩ : syracuseStep 50742773 = 4757135) B4757135
theorem B1320607 : Blo 1319478 1320607 := bstep (se 1 (by rfl) ⟨990455, by rfl⟩ : syracuseStep 1320607 = 1980911) B1980911
theorem B7521983 : Blo 1319478 7521983 := bstep (se 1 (by rfl) ⟨5641487, by rfl⟩ : syracuseStep 7521983 = 11282975) B11282975
theorem B13559663 : Blo 1319478 13559663 := bstep (se 1 (by rfl) ⟨10169747, by rfl⟩ : syracuseStep 13559663 = 20339495) B20339495
theorem B79333561 : Blo 1319478 79333561 := bstep (se 2 (by rfl) ⟨29750085, by rfl⟩ : syracuseStep 79333561 = 59500171) B59500171
theorem B1321371 : Blo 1319478 1321371 := bstep (se 1 (by rfl) ⟨991028, by rfl⟩ : syracuseStep 1321371 = 1982057) B1982057
theorem B8456719 : Blo 1319478 8456719 := bstep (se 1 (by rfl) ⟨6342539, by rfl⟩ : syracuseStep 8456719 = 12685079) B12685079
theorem B16910977 : Blo 1319478 16910977 := bstep (se 2 (by rfl) ⟨6341616, by rfl⟩ : syracuseStep 16910977 = 12683233) B12683233
theorem B128486249 : Blo 1319478 128486249 := bstep (se 2 (by rfl) ⟨48182343, by rfl⟩ : syracuseStep 128486249 = 96364687) B96364687
theorem B48155795 : Blo 1319478 48155795 := bstep (se 1 (by rfl) ⟨36116846, by rfl⟩ : syracuseStep 48155795 = 72233693) B72233693
theorem B5639863 : Blo 1319478 5639863 := bstep (se 1 (by rfl) ⟨4229897, by rfl⟩ : syracuseStep 5639863 = 8459795) B8459795
theorem B7515899 : Blo 1319478 7515899 := bstep (se 1 (by rfl) ⟨5636924, by rfl⟩ : syracuseStep 7515899 = 11273849) B11273849
theorem B38064005 : Blo 1319478 38064005 := bstep (se 4 (by rfl) ⟨3568500, by rfl⟩ : syracuseStep 38064005 = 7137001) B7137001
theorem B5640137 : Blo 1319478 5640137 := bstep (se 2 (by rfl) ⟨2115051, by rfl⟩ : syracuseStep 5640137 = 4230103) B4230103
theorem B8032243 : Blo 1319478 8032243 := bstep (se 1 (by rfl) ⟨6024182, by rfl⟩ : syracuseStep 8032243 = 12048365) B12048365
theorem B7516151 : Blo 1319478 7516151 := bstep (se 1 (by rfl) ⟨5637113, by rfl⟩ : syracuseStep 7516151 = 11274227) B11274227
theorem B9039863 : Blo 1319478 9039863 := bstep (se 1 (by rfl) ⟨6779897, by rfl⟩ : syracuseStep 9039863 = 13559795) B13559795
theorem B8466767 : Blo 1319478 8466767 := bstep (se 1 (by rfl) ⟨6350075, by rfl⟩ : syracuseStep 8466767 = 12700151) B12700151
theorem B3568103 : Blo 1319478 3568103 := bstep (se 1 (by rfl) ⟨2676077, by rfl⟩ : syracuseStep 3568103 = 5352155) B5352155
theorem B57152051 : Blo 1319478 57152051 := bstep (se 1 (by rfl) ⟨42864038, by rfl⟩ : syracuseStep 57152051 = 85728077) B85728077
theorem B2970575 : Blo 1319478 2970575 := bstep (se 1 (by rfl) ⟨2227931, by rfl⟩ : syracuseStep 2970575 = 4455863) B4455863
theorem B1979369 : Blo 1319478 1979369 := bstep (se 2 (by rfl) ⟨742263, by rfl⟩ : syracuseStep 1979369 = 1484527) B1484527
theorem B1979423 : Blo 1319478 1979423 := bstep (se 1 (by rfl) ⟨1484567, by rfl⟩ : syracuseStep 1979423 = 2969135) B2969135
theorem B2971241 : Blo 1319478 2971241 := bstep (se 2 (by rfl) ⟨1114215, by rfl⟩ : syracuseStep 2971241 = 2228431) B2228431
theorem B4232999 : Blo 1319478 4232999 := bstep (se 1 (by rfl) ⟨3174749, by rfl⟩ : syracuseStep 4232999 = 6349499) B6349499
theorem B15030521 : Blo 1319478 15030521 := bstep (se 2 (by rfl) ⟨5636445, by rfl⟩ : syracuseStep 15030521 = 11272891) B11272891
theorem B1980743 : Blo 1319478 1980743 := bstep (se 1 (by rfl) ⟨1485557, by rfl⟩ : syracuseStep 1980743 = 2971115) B2971115
theorem B6773183 : Blo 1319478 6773183 := bstep (se 1 (by rfl) ⟨5079887, by rfl⟩ : syracuseStep 6773183 = 10159775) B10159775
theorem B2972159 : Blo 1319478 2972159 := bstep (se 1 (by rfl) ⟨2229119, by rfl⟩ : syracuseStep 2972159 = 4458239) B4458239
theorem B12696425 : Blo 1319478 12696425 := bstep (se 2 (by rfl) ⟨4761159, by rfl⟩ : syracuseStep 12696425 = 9522319) B9522319
theorem B2227081 : Blo 1319478 2227081 := bstep (se 2 (by rfl) ⟨835155, by rfl⟩ : syracuseStep 2227081 = 1670311) B1670311
theorem B1981631 : Blo 1319478 1981631 := bstep (se 1 (by rfl) ⟨1486223, by rfl⟩ : syracuseStep 1981631 = 2972447) B2972447
theorem B3759385 : Blo 1319478 3759385 := bstep (se 2 (by rfl) ⟨1409769, by rfl⟩ : syracuseStep 3759385 = 2819539) B2819539
theorem B3759443 : Blo 1319478 3759443 := bstep (se 1 (by rfl) ⟨2819582, by rfl⟩ : syracuseStep 3759443 = 5639165) B5639165
theorem B30907885 : Blo 1319478 30907885 := bstep (se 3 (by rfl) ⟨5795228, by rfl⟩ : syracuseStep 30907885 = 11590457) B11590457
theorem B19037767 : Blo 1319478 19037767 := bstep (se 1 (by rfl) ⟨14278325, by rfl⟩ : syracuseStep 19037767 = 28556651) B28556651
theorem B1982111 : Blo 1319478 1982111 := bstep (se 1 (by rfl) ⟨1486583, by rfl⟩ : syracuseStep 1982111 = 2973167) B2973167
theorem B7626575 : Blo 1319478 7626575 := bstep (se 1 (by rfl) ⟨5719931, by rfl⟩ : syracuseStep 7626575 = 11439863) B11439863
theorem B5644511 : Blo 1319478 5644511 := bstep (se 1 (by rfl) ⟨4233383, by rfl⟩ : syracuseStep 5644511 = 8466767) B8466767
theorem B38101367 : Blo 1319478 38101367 := bstep (se 1 (by rfl) ⟨28576025, by rfl⟩ : syracuseStep 38101367 = 57152051) B57152051
theorem B1319579 : Blo 1319478 1319579 := bstep (se 1 (by rfl) ⟨989684, by rfl⟩ : syracuseStep 1319579 = 1979369) B1979369
theorem B1319615 : Blo 1319478 1319615 := bstep (se 1 (by rfl) ⟨989711, by rfl⟩ : syracuseStep 1319615 = 1979423) B1979423
theorem B16925435 : Blo 1319478 16925435 := bstep (se 1 (by rfl) ⟨12694076, by rfl⟩ : syracuseStep 16925435 = 25388153) B25388153
theorem B4457375 : Blo 1319478 4457375 := bstep (se 1 (by rfl) ⟨3343031, by rfl⟩ : syracuseStep 4457375 = 6686063) B6686063
theorem B2229241 : Blo 1319478 2229241 := bstep (se 2 (by rfl) ⟨835965, by rfl⟩ : syracuseStep 2229241 = 1671931) B1671931
theorem B5014655 : Blo 1319478 5014655 := bstep (se 1 (by rfl) ⟨3760991, by rfl⟩ : syracuseStep 5014655 = 7521983) B7521983
theorem B144803321 : Blo 1319478 144803321 := bstep (se 2 (by rfl) ⟨54301245, by rfl⟩ : syracuseStep 144803321 = 108602491) B108602491
theorem B10020347 : Blo 1319478 10020347 := bstep (se 1 (by rfl) ⟨7515260, by rfl⟩ : syracuseStep 10020347 = 15030521) B15030521
theorem B1320495 : Blo 1319478 1320495 := bstep (se 1 (by rfl) ⟨990371, by rfl⟩ : syracuseStep 1320495 = 1980743) B1980743
theorem B4515455 : Blo 1319478 4515455 := bstep (se 1 (by rfl) ⟨3386591, by rfl⟩ : syracuseStep 4515455 = 6773183) B6773183
theorem B85657499 : Blo 1319478 85657499 := bstep (se 1 (by rfl) ⟨64243124, by rfl⟩ : syracuseStep 85657499 = 128486249) B128486249
theorem B8464283 : Blo 1319478 8464283 := bstep (se 1 (by rfl) ⟨6348212, by rfl⟩ : syracuseStep 8464283 = 12696425) B12696425
theorem B1321087 : Blo 1319478 1321087 := bstep (se 1 (by rfl) ⟨990815, by rfl⟩ : syracuseStep 1321087 = 1981631) B1981631
theorem B1321407 : Blo 1319478 1321407 := bstep (se 1 (by rfl) ⟨991055, by rfl⟩ : syracuseStep 1321407 = 1982111) B1982111
theorem B10709657 : Blo 1319478 10709657 := bstep (se 2 (by rfl) ⟨4016121, by rfl⟩ : syracuseStep 10709657 = 8032243) B8032243
theorem B105778081 : Blo 1319478 105778081 := bstep (se 2 (by rfl) ⟨39666780, by rfl⟩ : syracuseStep 105778081 = 79333561) B79333561
theorem B2378735 : Blo 1319478 2378735 := bstep (se 1 (by rfl) ⟨1784051, by rfl⟩ : syracuseStep 2378735 = 3568103) B3568103
theorem B11275625 : Blo 1319478 11275625 := bstep (se 2 (by rfl) ⟨4228359, by rfl⟩ : syracuseStep 11275625 = 8456719) B8456719
theorem B22547969 : Blo 1319478 22547969 := bstep (se 2 (by rfl) ⟨8455488, by rfl⟩ : syracuseStep 22547969 = 16910977) B16910977
theorem B33828515 : Blo 1319478 33828515 := bstep (se 1 (by rfl) ⟨25371386, by rfl⟩ : syracuseStep 33828515 = 50742773) B50742773
theorem B2969441 : Blo 1319478 2969441 := bstep (se 2 (by rfl) ⟨1113540, by rfl⟩ : syracuseStep 2969441 = 2227081) B2227081
theorem B9039775 : Blo 1319478 9039775 := bstep (se 1 (by rfl) ⟨6779831, by rfl⟩ : syracuseStep 9039775 = 13559663) B13559663
theorem B41210513 : Blo 1319478 41210513 := bstep (se 2 (by rfl) ⟨15453942, by rfl⟩ : syracuseStep 41210513 = 30907885) B30907885
theorem B25383689 : Blo 1319478 25383689 := bstep (se 2 (by rfl) ⟨9518883, by rfl⟩ : syracuseStep 25383689 = 19037767) B19037767
theorem B5010599 : Blo 1319478 5010599 := bstep (se 1 (by rfl) ⟨3757949, by rfl⟩ : syracuseStep 5010599 = 7515899) B7515899
theorem B5084383 : Blo 1319478 5084383 := bstep (se 1 (by rfl) ⟨3813287, by rfl⟩ : syracuseStep 5084383 = 7626575) B7626575
theorem B25376003 : Blo 1319478 25376003 := bstep (se 1 (by rfl) ⟨19032002, by rfl⟩ : syracuseStep 25376003 = 38064005) B38064005
theorem B5010767 : Blo 1319478 5010767 := bstep (se 1 (by rfl) ⟨3758075, by rfl⟩ : syracuseStep 5010767 = 7516151) B7516151
theorem B6026575 : Blo 1319478 6026575 := bstep (se 1 (by rfl) ⟨4519931, by rfl⟩ : syracuseStep 6026575 = 9039863) B9039863
theorem B1980383 : Blo 1319478 1980383 := bstep (se 1 (by rfl) ⟨1485287, by rfl⟩ : syracuseStep 1980383 = 2970575) B2970575
theorem B1980827 : Blo 1319478 1980827 := bstep (se 1 (by rfl) ⟨1485620, by rfl⟩ : syracuseStep 1980827 = 2971241) B2971241
theorem B2972393 : Blo 1319478 2972393 := bstep (se 2 (by rfl) ⟨1114647, by rfl⟩ : syracuseStep 2972393 = 2229295) B2229295
theorem B1981439 : Blo 1319478 1981439 := bstep (se 1 (by rfl) ⟨1486079, by rfl⟩ : syracuseStep 1981439 = 2972159) B2972159
theorem B5012513 : Blo 1319478 5012513 := bstep (se 2 (by rfl) ⟨1879692, by rfl⟩ : syracuseStep 5012513 = 3759385) B3759385
theorem B32103863 : Blo 1319478 32103863 := bstep (se 1 (by rfl) ⟨24077897, by rfl⟩ : syracuseStep 32103863 = 48155795) B48155795
theorem B11287997 : Blo 1319478 11287997 := bstep (se 3 (by rfl) ⟨2116499, by rfl⟩ : syracuseStep 11287997 = 4232999) B4232999
theorem B2506295 : Blo 1319478 2506295 := bstep (se 1 (by rfl) ⟨1879721, by rfl⟩ : syracuseStep 2506295 = 3759443) B3759443
theorem B7519817 : Blo 1319478 7519817 := bstep (se 2 (by rfl) ⟨2819931, by rfl⟩ : syracuseStep 7519817 = 5639863) B5639863
theorem B3760091 : Blo 1319478 3760091 := bstep (se 1 (by rfl) ⟨2820068, by rfl⟩ : syracuseStep 3760091 = 5640137) B5640137
theorem B3343103 : Blo 1319478 3343103 := bstep (se 1 (by rfl) ⟨2507327, by rfl⟩ : syracuseStep 3343103 = 5014655) B5014655
theorem B16917335 : Blo 1319478 16917335 := bstep (se 1 (by rfl) ⟨12688001, by rfl⟩ : syracuseStep 16917335 = 25376003) B25376003
theorem B96535547 : Blo 1319478 96535547 := bstep (se 1 (by rfl) ⟨72401660, by rfl⟩ : syracuseStep 96535547 = 144803321) B144803321
theorem B1320255 : Blo 1319478 1320255 := bstep (se 1 (by rfl) ⟨990191, by rfl⟩ : syracuseStep 1320255 = 1980383) B1980383
theorem B1320551 : Blo 1319478 1320551 := bstep (se 1 (by rfl) ⟨990413, by rfl⟩ : syracuseStep 1320551 = 1980827) B1980827
theorem B1320959 : Blo 1319478 1320959 := bstep (se 1 (by rfl) ⟨990719, by rfl⟩ : syracuseStep 1320959 = 1981439) B1981439
theorem B12053033 : Blo 1319478 12053033 := bstep (se 2 (by rfl) ⟨4519887, by rfl⟩ : syracuseStep 12053033 = 9039775) B9039775
theorem B3763007 : Blo 1319478 3763007 := bstep (se 1 (by rfl) ⟨2822255, by rfl⟩ : syracuseStep 3763007 = 5644511) B5644511
theorem B11283623 : Blo 1319478 11283623 := bstep (se 1 (by rfl) ⟨8462717, by rfl⟩ : syracuseStep 11283623 = 16925435) B16925435
theorem B6680231 : Blo 1319478 6680231 := bstep (se 1 (by rfl) ⟨5010173, by rfl⟩ : syracuseStep 6680231 = 10020347) B10020347
theorem B3010303 : Blo 1319478 3010303 := bstep (se 1 (by rfl) ⟨2257727, by rfl⟩ : syracuseStep 3010303 = 4515455) B4515455
theorem B6779177 : Blo 1319478 6779177 := bstep (se 2 (by rfl) ⟨2542191, by rfl⟩ : syracuseStep 6779177 = 5084383) B5084383
theorem B7139771 : Blo 1319478 7139771 := bstep (se 1 (by rfl) ⟨5354828, by rfl⟩ : syracuseStep 7139771 = 10709657) B10709657
theorem B1585823 : Blo 1319478 1585823 := bstep (se 1 (by rfl) ⟨1189367, by rfl⟩ : syracuseStep 1585823 = 2378735) B2378735
theorem B7517083 : Blo 1319478 7517083 := bstep (se 1 (by rfl) ⟨5637812, by rfl⟩ : syracuseStep 7517083 = 11275625) B11275625
theorem B21402575 : Blo 1319478 21402575 := bstep (se 1 (by rfl) ⟨16051931, by rfl⟩ : syracuseStep 21402575 = 32103863) B32103863
theorem B7525331 : Blo 1319478 7525331 := bstep (se 1 (by rfl) ⟨5643998, by rfl⟩ : syracuseStep 7525331 = 11287997) B11287997
theorem B1979627 : Blo 1319478 1979627 := bstep (se 1 (by rfl) ⟨1484720, by rfl⟩ : syracuseStep 1979627 = 2969441) B2969441
theorem B25400911 : Blo 1319478 25400911 := bstep (se 1 (by rfl) ⟨19050683, by rfl⟩ : syracuseStep 25400911 = 38101367) B38101367
theorem B27473675 : Blo 1319478 27473675 := bstep (se 1 (by rfl) ⟨20605256, by rfl⟩ : syracuseStep 27473675 = 41210513) B41210513
theorem B16922459 : Blo 1319478 16922459 := bstep (se 1 (by rfl) ⟨12691844, by rfl⟩ : syracuseStep 16922459 = 25383689) B25383689
theorem B2971583 : Blo 1319478 2971583 := bstep (se 1 (by rfl) ⟨2228687, by rfl⟩ : syracuseStep 2971583 = 4457375) B4457375
theorem B3340399 : Blo 1319478 3340399 := bstep (se 1 (by rfl) ⟨2505299, by rfl⟩ : syracuseStep 3340399 = 5010599) B5010599
theorem B3340511 : Blo 1319478 3340511 := bstep (se 1 (by rfl) ⟨2505383, by rfl⟩ : syracuseStep 3340511 = 5010767) B5010767
theorem B57104999 : Blo 1319478 57104999 := bstep (se 1 (by rfl) ⟨42828749, by rfl⟩ : syracuseStep 57104999 = 85657499) B85657499
theorem B5642855 : Blo 1319478 5642855 := bstep (se 1 (by rfl) ⟨4232141, by rfl⟩ : syracuseStep 5642855 = 8464283) B8464283
theorem B2972321 : Blo 1319478 2972321 := bstep (se 2 (by rfl) ⟨1114620, by rfl⟩ : syracuseStep 2972321 = 2229241) B2229241
theorem B8035433 : Blo 1319478 8035433 := bstep (se 2 (by rfl) ⟨3013287, by rfl⟩ : syracuseStep 8035433 = 6026575) B6026575
theorem B1981595 : Blo 1319478 1981595 := bstep (se 1 (by rfl) ⟨1486196, by rfl⟩ : syracuseStep 1981595 = 2972393) B2972393
theorem B3341675 : Blo 1319478 3341675 := bstep (se 1 (by rfl) ⟨2506256, by rfl⟩ : syracuseStep 3341675 = 5012513) B5012513
theorem B564149765 : Blo 1319478 564149765 := bstep (se 4 (by rfl) ⟨52889040, by rfl⟩ : syracuseStep 564149765 = 105778081) B105778081
theorem B15031979 : Blo 1319478 15031979 := bstep (se 1 (by rfl) ⟨11273984, by rfl⟩ : syracuseStep 15031979 = 22547969) B22547969
theorem B1670863 : Blo 1319478 1670863 := bstep (se 1 (by rfl) ⟨1253147, by rfl⟩ : syracuseStep 1670863 = 2506295) B2506295
theorem B5013211 : Blo 1319478 5013211 := bstep (se 1 (by rfl) ⟨3759908, by rfl⟩ : syracuseStep 5013211 = 7519817) B7519817
theorem B22552343 : Blo 1319478 22552343 := bstep (se 1 (by rfl) ⟨16914257, by rfl⟩ : syracuseStep 22552343 = 33828515) B33828515
theorem B2506727 : Blo 1319478 2506727 := bstep (se 1 (by rfl) ⟨1880045, by rfl⟩ : syracuseStep 2506727 = 3760091) B3760091
theorem B4759847 : Blo 1319478 4759847 := bstep (se 1 (by rfl) ⟨3569885, by rfl⟩ : syracuseStep 4759847 = 7139771) B7139771
theorem B2228735 : Blo 1319478 2228735 := bstep (se 1 (by rfl) ⟨1671551, by rfl⟩ : syracuseStep 2228735 = 3343103) B3343103
theorem B64357031 : Blo 1319478 64357031 := bstep (se 1 (by rfl) ⟨48267773, by rfl⟩ : syracuseStep 64357031 = 96535547) B96535547
theorem B1319751 : Blo 1319478 1319751 := bstep (se 1 (by rfl) ⟨989813, by rfl⟩ : syracuseStep 1319751 = 1979627) B1979627
theorem B11281639 : Blo 1319478 11281639 := bstep (se 1 (by rfl) ⟨8461229, by rfl⟩ : syracuseStep 11281639 = 16922459) B16922459
theorem B38069999 : Blo 1319478 38069999 := bstep (se 1 (by rfl) ⟨28552499, by rfl⟩ : syracuseStep 38069999 = 57104999) B57104999
theorem B3761903 : Blo 1319478 3761903 := bstep (se 1 (by rfl) ⟨2821427, by rfl⟩ : syracuseStep 3761903 = 5642855) B5642855
theorem B4228861 : Blo 1319478 4228861 := bstep (se 3 (by rfl) ⟨792911, by rfl⟩ : syracuseStep 4228861 = 1585823) B1585823
theorem B2508671 : Blo 1319478 2508671 := bstep (se 1 (by rfl) ⟨1881503, by rfl⟩ : syracuseStep 2508671 = 3763007) B3763007
theorem B73263133 : Blo 1319478 73263133 := bstep (se 3 (by rfl) ⟨13736837, by rfl⟩ : syracuseStep 73263133 = 27473675) B27473675
theorem B1321063 : Blo 1319478 1321063 := bstep (se 1 (by rfl) ⟨990797, by rfl⟩ : syracuseStep 1321063 = 1981595) B1981595
theorem B33867881 : Blo 1319478 33867881 := bstep (se 2 (by rfl) ⟨12700455, by rfl⟩ : syracuseStep 33867881 = 25400911) B25400911
theorem B7522415 : Blo 1319478 7522415 := bstep (se 1 (by rfl) ⟨5641811, by rfl⟩ : syracuseStep 7522415 = 11283623) B11283623
theorem B10021319 : Blo 1319478 10021319 := bstep (se 1 (by rfl) ⟨7515989, by rfl⟩ : syracuseStep 10021319 = 15031979) B15031979
theorem B15034895 : Blo 1319478 15034895 := bstep (se 1 (by rfl) ⟨11276171, by rfl⟩ : syracuseStep 15034895 = 22552343) B22552343
theorem B5016887 : Blo 1319478 5016887 := bstep (se 1 (by rfl) ⟨3762665, by rfl⟩ : syracuseStep 5016887 = 7525331) B7525331
theorem B10022777 : Blo 1319478 10022777 := bstep (se 2 (by rfl) ⟨3758541, by rfl⟩ : syracuseStep 10022777 = 7517083) B7517083
theorem B376099843 : Blo 1319478 376099843 := bstep (se 1 (by rfl) ⟨282074882, by rfl⟩ : syracuseStep 376099843 = 564149765) B564149765
theorem B4453487 : Blo 1319478 4453487 := bstep (se 1 (by rfl) ⟨3340115, by rfl⟩ : syracuseStep 4453487 = 6680231) B6680231
theorem B4453865 : Blo 1319478 4453865 := bstep (se 2 (by rfl) ⟨1670199, by rfl⟩ : syracuseStep 4453865 = 3340399) B3340399
theorem B4519451 : Blo 1319478 4519451 := bstep (se 1 (by rfl) ⟨3389588, by rfl⟩ : syracuseStep 4519451 = 6779177) B6779177
theorem B11278223 : Blo 1319478 11278223 := bstep (se 1 (by rfl) ⟨8458667, by rfl⟩ : syracuseStep 11278223 = 16917335) B16917335
theorem B14268383 : Blo 1319478 14268383 := bstep (se 1 (by rfl) ⟨10701287, by rfl⟩ : syracuseStep 14268383 = 21402575) B21402575
theorem B1981055 : Blo 1319478 1981055 := bstep (se 1 (by rfl) ⟨1485791, by rfl⟩ : syracuseStep 1981055 = 2971583) B2971583
theorem B16054949 : Blo 1319478 16054949 := bstep (se 4 (by rfl) ⟨1505151, by rfl⟩ : syracuseStep 16054949 = 3010303) B3010303
theorem B2227007 : Blo 1319478 2227007 := bstep (se 1 (by rfl) ⟨1670255, by rfl⟩ : syracuseStep 2227007 = 3340511) B3340511
theorem B8035355 : Blo 1319478 8035355 := bstep (se 1 (by rfl) ⟨6026516, by rfl⟩ : syracuseStep 8035355 = 12053033) B12053033
theorem B1981547 : Blo 1319478 1981547 := bstep (se 1 (by rfl) ⟨1486160, by rfl⟩ : syracuseStep 1981547 = 2972321) B2972321
theorem B5356955 : Blo 1319478 5356955 := bstep (se 1 (by rfl) ⟨4017716, by rfl⟩ : syracuseStep 5356955 = 8035433) B8035433
theorem B2227783 : Blo 1319478 2227783 := bstep (se 1 (by rfl) ⟨1670837, by rfl⟩ : syracuseStep 2227783 = 3341675) B3341675
theorem B2227817 : Blo 1319478 2227817 := bstep (se 2 (by rfl) ⟨835431, by rfl⟩ : syracuseStep 2227817 = 1670863) B1670863
theorem B6684281 : Blo 1319478 6684281 := bstep (se 2 (by rfl) ⟨2506605, by rfl⟩ : syracuseStep 6684281 = 5013211) B5013211
theorem B6684605 : Blo 1319478 6684605 := bstep (se 3 (by rfl) ⟨1253363, by rfl⟩ : syracuseStep 6684605 = 2506727) B2506727
theorem B25379999 : Blo 1319478 25379999 := bstep (se 1 (by rfl) ⟨19034999, by rfl⟩ : syracuseStep 25379999 = 38069999) B38069999
theorem B2507935 : Blo 1319478 2507935 := bstep (se 1 (by rfl) ⟨1880951, by rfl⟩ : syracuseStep 2507935 = 3761903) B3761903
theorem B9512255 : Blo 1319478 9512255 := bstep (se 1 (by rfl) ⟨7134191, by rfl⟩ : syracuseStep 9512255 = 14268383) B14268383
theorem B501466457 : Blo 1319478 501466457 := bstep (se 2 (by rfl) ⟨188049921, by rfl⟩ : syracuseStep 501466457 = 376099843) B376099843
theorem B22578587 : Blo 1319478 22578587 := bstep (se 1 (by rfl) ⟨16933940, by rfl⟩ : syracuseStep 22578587 = 33867881) B33867881
theorem B5014943 : Blo 1319478 5014943 := bstep (se 1 (by rfl) ⟨3761207, by rfl⟩ : syracuseStep 5014943 = 7522415) B7522415
theorem B15042185 : Blo 1319478 15042185 := bstep (se 2 (by rfl) ⟨5640819, by rfl⟩ : syracuseStep 15042185 = 11281639) B11281639
theorem B1320703 : Blo 1319478 1320703 := bstep (se 1 (by rfl) ⟨990527, by rfl⟩ : syracuseStep 1320703 = 1981055) B1981055
theorem B1484671 : Blo 1319478 1484671 := bstep (se 1 (by rfl) ⟨1113503, by rfl⟩ : syracuseStep 1484671 = 2227007) B2227007
theorem B1321031 : Blo 1319478 1321031 := bstep (se 1 (by rfl) ⟨990773, by rfl⟩ : syracuseStep 1321031 = 1981547) B1981547
theorem B3344591 : Blo 1319478 3344591 := bstep (se 1 (by rfl) ⟨2508443, by rfl⟩ : syracuseStep 3344591 = 5016887) B5016887
theorem B5638481 : Blo 1319478 5638481 := bstep (se 2 (by rfl) ⟨2114430, by rfl⟩ : syracuseStep 5638481 = 4228861) B4228861
theorem B1485211 : Blo 1319478 1485211 := bstep (se 1 (by rfl) ⟨1113908, by rfl⟩ : syracuseStep 1485211 = 2227817) B2227817
theorem B97684177 : Blo 1319478 97684177 := bstep (se 2 (by rfl) ⟨36631566, by rfl⟩ : syracuseStep 97684177 = 73263133) B73263133
theorem B3173231 : Blo 1319478 3173231 := bstep (se 1 (by rfl) ⟨2379923, by rfl⟩ : syracuseStep 3173231 = 4759847) B4759847
theorem B1485823 : Blo 1319478 1485823 := bstep (se 1 (by rfl) ⟨1114367, by rfl⟩ : syracuseStep 1485823 = 2228735) B2228735
theorem B42904687 : Blo 1319478 42904687 := bstep (se 1 (by rfl) ⟨32178515, by rfl⟩ : syracuseStep 42904687 = 64357031) B64357031
theorem B2968991 : Blo 1319478 2968991 := bstep (se 1 (by rfl) ⟨2226743, by rfl⟩ : syracuseStep 2968991 = 4453487) B4453487
theorem B2969243 : Blo 1319478 2969243 := bstep (se 1 (by rfl) ⟨2226932, by rfl⟩ : syracuseStep 2969243 = 4453865) B4453865
theorem B6680879 : Blo 1319478 6680879 := bstep (se 1 (by rfl) ⟨5010659, by rfl⟩ : syracuseStep 6680879 = 10021319) B10021319
theorem B10023263 : Blo 1319478 10023263 := bstep (se 1 (by rfl) ⟨7517447, by rfl⟩ : syracuseStep 10023263 = 15034895) B15034895
theorem B10703299 : Blo 1319478 10703299 := bstep (se 1 (by rfl) ⟨8027474, by rfl⟩ : syracuseStep 10703299 = 16054949) B16054949
theorem B2970377 : Blo 1319478 2970377 := bstep (se 2 (by rfl) ⟨1113891, by rfl⟩ : syracuseStep 2970377 = 2227783) B2227783
theorem B6689789 : Blo 1319478 6689789 := bstep (se 3 (by rfl) ⟨1254335, by rfl⟩ : syracuseStep 6689789 = 2508671) B2508671
theorem B6681851 : Blo 1319478 6681851 := bstep (se 1 (by rfl) ⟨5011388, by rfl⟩ : syracuseStep 6681851 = 10022777) B10022777
theorem B3012967 : Blo 1319478 3012967 := bstep (se 1 (by rfl) ⟨2259725, by rfl⟩ : syracuseStep 3012967 = 4519451) B4519451
theorem B7518815 : Blo 1319478 7518815 := bstep (se 1 (by rfl) ⟨5639111, by rfl⟩ : syracuseStep 7518815 = 11278223) B11278223
theorem B5356903 : Blo 1319478 5356903 := bstep (se 1 (by rfl) ⟨4017677, by rfl⟩ : syracuseStep 5356903 = 8035355) B8035355
theorem B3571303 : Blo 1319478 3571303 := bstep (se 1 (by rfl) ⟨2678477, by rfl⟩ : syracuseStep 3571303 = 5356955) B5356955
theorem B4456187 : Blo 1319478 4456187 := bstep (se 1 (by rfl) ⟨3342140, by rfl⟩ : syracuseStep 4456187 = 6684281) B6684281
theorem B4456403 : Blo 1319478 4456403 := bstep (se 1 (by rfl) ⟨3342302, by rfl⟩ : syracuseStep 4456403 = 6684605) B6684605
theorem B14271065 : Blo 1319478 14271065 := bstep (se 2 (by rfl) ⟨5351649, by rfl⟩ : syracuseStep 14271065 = 10703299) B10703299
theorem B6341503 : Blo 1319478 6341503 := bstep (se 1 (by rfl) ⟨4756127, by rfl⟩ : syracuseStep 6341503 = 9512255) B9512255
theorem B3343295 : Blo 1319478 3343295 := bstep (se 1 (by rfl) ⟨2507471, by rfl⟩ : syracuseStep 3343295 = 5014943) B5014943
theorem B130245569 : Blo 1319478 130245569 := bstep (se 2 (by rfl) ⟨48842088, by rfl⟩ : syracuseStep 130245569 = 97684177) B97684177
theorem B10028123 : Blo 1319478 10028123 := bstep (se 1 (by rfl) ⟨7521092, by rfl⟩ : syracuseStep 10028123 = 15042185) B15042185
theorem B2229727 : Blo 1319478 2229727 := bstep (se 1 (by rfl) ⟨1672295, by rfl⟩ : syracuseStep 2229727 = 3344591) B3344591
theorem B57206249 : Blo 1319478 57206249 := bstep (se 2 (by rfl) ⟨21452343, by rfl⟩ : syracuseStep 57206249 = 42904687) B42904687
theorem B3343913 : Blo 1319478 3343913 := bstep (se 2 (by rfl) ⟨1253967, by rfl⟩ : syracuseStep 3343913 = 2507935) B2507935
theorem B2115487 : Blo 1319478 2115487 := bstep (se 1 (by rfl) ⟨1586615, by rfl⟩ : syracuseStep 2115487 = 3173231) B3173231
theorem B4761737 : Blo 1319478 4761737 := bstep (se 2 (by rfl) ⟨1785651, by rfl⟩ : syracuseStep 4761737 = 3571303) B3571303
theorem B4017289 : Blo 1319478 4017289 := bstep (se 2 (by rfl) ⟨1506483, by rfl⟩ : syracuseStep 4017289 = 3012967) B3012967
theorem B4459859 : Blo 1319478 4459859 := bstep (se 1 (by rfl) ⟨3344894, by rfl⟩ : syracuseStep 4459859 = 6689789) B6689789
theorem B16919999 : Blo 1319478 16919999 := bstep (se 1 (by rfl) ⟨12689999, by rfl⟩ : syracuseStep 16919999 = 25379999) B25379999
theorem B334310971 : Blo 1319478 334310971 := bstep (se 1 (by rfl) ⟨250733228, by rfl⟩ : syracuseStep 334310971 = 501466457) B501466457
theorem B15052391 : Blo 1319478 15052391 := bstep (se 1 (by rfl) ⟨11289293, by rfl⟩ : syracuseStep 15052391 = 22578587) B22578587
theorem B1979327 : Blo 1319478 1979327 := bstep (se 1 (by rfl) ⟨1484495, by rfl⟩ : syracuseStep 1979327 = 2968991) B2968991
theorem B1979495 : Blo 1319478 1979495 := bstep (se 1 (by rfl) ⟨1484621, by rfl⟩ : syracuseStep 1979495 = 2969243) B2969243
theorem B2970791 : Blo 1319478 2970791 := bstep (se 1 (by rfl) ⟨2228093, by rfl⟩ : syracuseStep 2970791 = 4456187) B4456187
theorem B1979561 : Blo 1319478 1979561 := bstep (se 2 (by rfl) ⟨742335, by rfl⟩ : syracuseStep 1979561 = 1484671) B1484671
theorem B2970935 : Blo 1319478 2970935 := bstep (se 1 (by rfl) ⟨2228201, by rfl⟩ : syracuseStep 2970935 = 4456403) B4456403
theorem B4453919 : Blo 1319478 4453919 := bstep (se 1 (by rfl) ⟨3340439, by rfl⟩ : syracuseStep 4453919 = 6680879) B6680879
theorem B6682175 : Blo 1319478 6682175 := bstep (se 1 (by rfl) ⟨5011631, by rfl⟩ : syracuseStep 6682175 = 10023263) B10023263
theorem B1980251 : Blo 1319478 1980251 := bstep (se 1 (by rfl) ⟨1485188, by rfl⟩ : syracuseStep 1980251 = 2970377) B2970377
theorem B1980281 : Blo 1319478 1980281 := bstep (se 2 (by rfl) ⟨742605, by rfl⟩ : syracuseStep 1980281 = 1485211) B1485211
theorem B4454567 : Blo 1319478 4454567 := bstep (se 1 (by rfl) ⟨3340925, by rfl⟩ : syracuseStep 4454567 = 6681851) B6681851
theorem B1981097 : Blo 1319478 1981097 := bstep (se 2 (by rfl) ⟨742911, by rfl⟩ : syracuseStep 1981097 = 1485823) B1485823
theorem B3758987 : Blo 1319478 3758987 := bstep (se 1 (by rfl) ⟨2819240, by rfl⟩ : syracuseStep 3758987 = 5638481) B5638481
theorem B5012543 : Blo 1319478 5012543 := bstep (se 1 (by rfl) ⟨3759407, by rfl⟩ : syracuseStep 5012543 = 7518815) B7518815
theorem B7142537 : Blo 1319478 7142537 := bstep (se 2 (by rfl) ⟨2678451, by rfl⟩ : syracuseStep 7142537 = 5356903) B5356903
theorem B19046765 : Blo 1319478 19046765 := bstep (se 3 (by rfl) ⟨3571268, by rfl⟩ : syracuseStep 19046765 = 7142537) B7142537
theorem B1319551 : Blo 1319478 1319551 := bstep (se 1 (by rfl) ⟨989663, by rfl⟩ : syracuseStep 1319551 = 1979327) B1979327
theorem B2228863 : Blo 1319478 2228863 := bstep (se 1 (by rfl) ⟨1671647, by rfl⟩ : syracuseStep 2228863 = 3343295) B3343295
theorem B6685415 : Blo 1319478 6685415 := bstep (se 1 (by rfl) ⟨5014061, by rfl⟩ : syracuseStep 6685415 = 10028123) B10028123
theorem B1319663 : Blo 1319478 1319663 := bstep (se 1 (by rfl) ⟨989747, by rfl⟩ : syracuseStep 1319663 = 1979495) B1979495
theorem B1319707 : Blo 1319478 1319707 := bstep (se 1 (by rfl) ⟨989780, by rfl⟩ : syracuseStep 1319707 = 1979561) B1979561
theorem B2229275 : Blo 1319478 2229275 := bstep (se 1 (by rfl) ⟨1671956, by rfl⟩ : syracuseStep 2229275 = 3343913) B3343913
theorem B8455337 : Blo 1319478 8455337 := bstep (se 2 (by rfl) ⟨3170751, by rfl⟩ : syracuseStep 8455337 = 6341503) B6341503
theorem B1320167 : Blo 1319478 1320167 := bstep (se 1 (by rfl) ⟨990125, by rfl⟩ : syracuseStep 1320167 = 1980251) B1980251
theorem B1320187 : Blo 1319478 1320187 := bstep (se 1 (by rfl) ⟨990140, by rfl⟩ : syracuseStep 1320187 = 1980281) B1980281
theorem B1320731 : Blo 1319478 1320731 := bstep (se 1 (by rfl) ⟨990548, by rfl⟩ : syracuseStep 1320731 = 1981097) B1981097
theorem B11282597 : Blo 1319478 11282597 := bstep (se 4 (by rfl) ⟨1057743, by rfl⟩ : syracuseStep 11282597 = 2115487) B2115487
theorem B9514043 : Blo 1319478 9514043 := bstep (se 1 (by rfl) ⟨7135532, by rfl⟩ : syracuseStep 9514043 = 14271065) B14271065
theorem B86830379 : Blo 1319478 86830379 := bstep (se 1 (by rfl) ⟨65122784, by rfl⟩ : syracuseStep 86830379 = 130245569) B130245569
theorem B38137499 : Blo 1319478 38137499 := bstep (se 1 (by rfl) ⟨28603124, by rfl⟩ : syracuseStep 38137499 = 57206249) B57206249
theorem B2969279 : Blo 1319478 2969279 := bstep (se 1 (by rfl) ⟨2226959, by rfl⟩ : syracuseStep 2969279 = 4453919) B4453919
theorem B3174491 : Blo 1319478 3174491 := bstep (se 1 (by rfl) ⟨2380868, by rfl⟩ : syracuseStep 3174491 = 4761737) B4761737
theorem B2969711 : Blo 1319478 2969711 := bstep (se 1 (by rfl) ⟨2227283, by rfl⟩ : syracuseStep 2969711 = 4454567) B4454567
theorem B445747961 : Blo 1319478 445747961 := bstep (se 2 (by rfl) ⟨167155485, by rfl⟩ : syracuseStep 445747961 = 334310971) B334310971
theorem B1980527 : Blo 1319478 1980527 := bstep (se 1 (by rfl) ⟨1485395, by rfl⟩ : syracuseStep 1980527 = 2970791) B2970791
theorem B1980623 : Blo 1319478 1980623 := bstep (se 1 (by rfl) ⟨1485467, by rfl⟩ : syracuseStep 1980623 = 2970935) B2970935
theorem B4454783 : Blo 1319478 4454783 := bstep (se 1 (by rfl) ⟨3341087, by rfl⟩ : syracuseStep 4454783 = 6682175) B6682175
theorem B5356385 : Blo 1319478 5356385 := bstep (se 2 (by rfl) ⟨2008644, by rfl⟩ : syracuseStep 5356385 = 4017289) B4017289
theorem B2505991 : Blo 1319478 2505991 := bstep (se 1 (by rfl) ⟨1879493, by rfl⟩ : syracuseStep 2505991 = 3758987) B3758987
theorem B2972969 : Blo 1319478 2972969 := bstep (se 2 (by rfl) ⟨1114863, by rfl⟩ : syracuseStep 2972969 = 2229727) B2229727
theorem B3341695 : Blo 1319478 3341695 := bstep (se 1 (by rfl) ⟨2506271, by rfl⟩ : syracuseStep 3341695 = 5012543) B5012543
theorem B2973239 : Blo 1319478 2973239 := bstep (se 1 (by rfl) ⟨2229929, by rfl⟩ : syracuseStep 2973239 = 4459859) B4459859
theorem B11279999 : Blo 1319478 11279999 := bstep (se 1 (by rfl) ⟨8459999, by rfl⟩ : syracuseStep 11279999 = 16919999) B16919999
theorem B10034927 : Blo 1319478 10034927 := bstep (se 1 (by rfl) ⟨7526195, by rfl⟩ : syracuseStep 10034927 = 15052391) B15052391
theorem B12697843 : Blo 1319478 12697843 := bstep (se 1 (by rfl) ⟨9523382, by rfl⟩ : syracuseStep 12697843 = 19046765) B19046765
theorem B4456943 : Blo 1319478 4456943 := bstep (se 1 (by rfl) ⟨3342707, by rfl⟩ : syracuseStep 4456943 = 6685415) B6685415
theorem B297165307 : Blo 1319478 297165307 := bstep (se 1 (by rfl) ⟨222873980, by rfl⟩ : syracuseStep 297165307 = 445747961) B445747961
theorem B5636891 : Blo 1319478 5636891 := bstep (se 1 (by rfl) ⟨4227668, by rfl⟩ : syracuseStep 5636891 = 8455337) B8455337
theorem B1320351 : Blo 1319478 1320351 := bstep (se 1 (by rfl) ⟨990263, by rfl⟩ : syracuseStep 1320351 = 1980527) B1980527
theorem B7521731 : Blo 1319478 7521731 := bstep (se 1 (by rfl) ⟨5641298, by rfl⟩ : syracuseStep 7521731 = 11282597) B11282597
theorem B1320415 : Blo 1319478 1320415 := bstep (se 1 (by rfl) ⟨990311, by rfl⟩ : syracuseStep 1320415 = 1980623) B1980623
theorem B6342695 : Blo 1319478 6342695 := bstep (se 1 (by rfl) ⟨4757021, by rfl⟩ : syracuseStep 6342695 = 9514043) B9514043
theorem B57886919 : Blo 1319478 57886919 := bstep (se 1 (by rfl) ⟨43415189, by rfl⟩ : syracuseStep 57886919 = 86830379) B86830379
theorem B8465309 : Blo 1319478 8465309 := bstep (se 3 (by rfl) ⟨1587245, by rfl⟩ : syracuseStep 8465309 = 3174491) B3174491
theorem B1486183 : Blo 1319478 1486183 := bstep (se 1 (by rfl) ⟨1114637, by rfl⟩ : syracuseStep 1486183 = 2229275) B2229275
theorem B2969855 : Blo 1319478 2969855 := bstep (se 1 (by rfl) ⟨2227391, by rfl⟩ : syracuseStep 2969855 = 4454783) B4454783
theorem B25424999 : Blo 1319478 25424999 := bstep (se 1 (by rfl) ⟨19068749, by rfl⟩ : syracuseStep 25424999 = 38137499) B38137499
theorem B1979519 : Blo 1319478 1979519 := bstep (se 1 (by rfl) ⟨1484639, by rfl⟩ : syracuseStep 1979519 = 2969279) B2969279
theorem B6689951 : Blo 1319478 6689951 := bstep (se 1 (by rfl) ⟨5017463, by rfl⟩ : syracuseStep 6689951 = 10034927) B10034927
theorem B1979807 : Blo 1319478 1979807 := bstep (se 1 (by rfl) ⟨1484855, by rfl⟩ : syracuseStep 1979807 = 2969711) B2969711
theorem B2971817 : Blo 1319478 2971817 := bstep (se 2 (by rfl) ⟨1114431, by rfl⟩ : syracuseStep 2971817 = 2228863) B2228863
theorem B3341321 : Blo 1319478 3341321 := bstep (se 2 (by rfl) ⟨1252995, by rfl⟩ : syracuseStep 3341321 = 2505991) B2505991
theorem B4455593 : Blo 1319478 4455593 := bstep (se 2 (by rfl) ⟨1670847, by rfl⟩ : syracuseStep 4455593 = 3341695) B3341695
theorem B3570923 : Blo 1319478 3570923 := bstep (se 1 (by rfl) ⟨2678192, by rfl⟩ : syracuseStep 3570923 = 5356385) B5356385
theorem B1981979 : Blo 1319478 1981979 := bstep (se 1 (by rfl) ⟨1486484, by rfl⟩ : syracuseStep 1981979 = 2972969) B2972969
theorem B1982159 : Blo 1319478 1982159 := bstep (se 1 (by rfl) ⟨1486619, by rfl⟩ : syracuseStep 1982159 = 2973239) B2973239
theorem B7519999 : Blo 1319478 7519999 := bstep (se 1 (by rfl) ⟨5639999, by rfl⟩ : syracuseStep 7519999 = 11279999) B11279999
theorem B16949999 : Blo 1319478 16949999 := bstep (se 1 (by rfl) ⟨12712499, by rfl⟩ : syracuseStep 16949999 = 25424999) B25424999
theorem B1319679 : Blo 1319478 1319679 := bstep (se 1 (by rfl) ⟨989759, by rfl⟩ : syracuseStep 1319679 = 1979519) B1979519
theorem B1319871 : Blo 1319478 1319871 := bstep (se 1 (by rfl) ⟨989903, by rfl⟩ : syracuseStep 1319871 = 1979807) B1979807
theorem B5014487 : Blo 1319478 5014487 := bstep (se 1 (by rfl) ⟨3760865, by rfl⟩ : syracuseStep 5014487 = 7521731) B7521731
theorem B4228463 : Blo 1319478 4228463 := bstep (se 1 (by rfl) ⟨3171347, by rfl⟩ : syracuseStep 4228463 = 6342695) B6342695
theorem B1321319 : Blo 1319478 1321319 := bstep (se 1 (by rfl) ⟨990989, by rfl⟩ : syracuseStep 1321319 = 1981979) B1981979
theorem B1321439 : Blo 1319478 1321439 := bstep (se 1 (by rfl) ⟨991079, by rfl⟩ : syracuseStep 1321439 = 1982159) B1982159
theorem B9522461 : Blo 1319478 9522461 := bstep (se 3 (by rfl) ⟨1785461, by rfl⟩ : syracuseStep 9522461 = 3570923) B3570923
theorem B4459967 : Blo 1319478 4459967 := bstep (se 1 (by rfl) ⟨3344975, by rfl⟩ : syracuseStep 4459967 = 6689951) B6689951
theorem B2970395 : Blo 1319478 2970395 := bstep (se 1 (by rfl) ⟨2227796, by rfl⟩ : syracuseStep 2970395 = 4455593) B4455593
theorem B1979903 : Blo 1319478 1979903 := bstep (se 1 (by rfl) ⟨1484927, by rfl⟩ : syracuseStep 1979903 = 2969855) B2969855
theorem B16930457 : Blo 1319478 16930457 := bstep (se 2 (by rfl) ⟨6348921, by rfl⟩ : syracuseStep 16930457 = 12697843) B12697843
theorem B2971295 : Blo 1319478 2971295 := bstep (se 1 (by rfl) ⟨2228471, by rfl⟩ : syracuseStep 2971295 = 4456943) B4456943
theorem B3757927 : Blo 1319478 3757927 := bstep (se 1 (by rfl) ⟨2818445, by rfl⟩ : syracuseStep 3757927 = 5636891) B5636891
theorem B396220409 : Blo 1319478 396220409 := bstep (se 2 (by rfl) ⟨148582653, by rfl⟩ : syracuseStep 396220409 = 297165307) B297165307
theorem B1981211 : Blo 1319478 1981211 := bstep (se 1 (by rfl) ⟨1485908, by rfl⟩ : syracuseStep 1981211 = 2971817) B2971817
theorem B38591279 : Blo 1319478 38591279 := bstep (se 1 (by rfl) ⟨28943459, by rfl⟩ : syracuseStep 38591279 = 57886919) B57886919
theorem B1981577 : Blo 1319478 1981577 := bstep (se 2 (by rfl) ⟨743091, by rfl⟩ : syracuseStep 1981577 = 1486183) B1486183
theorem B5643539 : Blo 1319478 5643539 := bstep (se 1 (by rfl) ⟨4232654, by rfl⟩ : syracuseStep 5643539 = 8465309) B8465309
theorem B2227547 : Blo 1319478 2227547 := bstep (se 1 (by rfl) ⟨1670660, by rfl⟩ : syracuseStep 2227547 = 3341321) B3341321
theorem B10026665 : Blo 1319478 10026665 := bstep (se 2 (by rfl) ⟨3759999, by rfl⟩ : syracuseStep 10026665 = 7519999) B7519999
theorem B3342991 : Blo 1319478 3342991 := bstep (se 1 (by rfl) ⟨2507243, by rfl⟩ : syracuseStep 3342991 = 5014487) B5014487
theorem B2818975 : Blo 1319478 2818975 := bstep (se 1 (by rfl) ⟨2114231, by rfl⟩ : syracuseStep 2818975 = 4228463) B4228463
theorem B1319935 : Blo 1319478 1319935 := bstep (se 1 (by rfl) ⟨989951, by rfl⟩ : syracuseStep 1319935 = 1979903) B1979903
theorem B1320807 : Blo 1319478 1320807 := bstep (se 1 (by rfl) ⟨990605, by rfl⟩ : syracuseStep 1320807 = 1981211) B1981211
theorem B1321051 : Blo 1319478 1321051 := bstep (se 1 (by rfl) ⟨990788, by rfl⟩ : syracuseStep 1321051 = 1981577) B1981577
theorem B3762359 : Blo 1319478 3762359 := bstep (se 1 (by rfl) ⟨2821769, by rfl⟩ : syracuseStep 3762359 = 5643539) B5643539
theorem B1485031 : Blo 1319478 1485031 := bstep (se 1 (by rfl) ⟨1113773, by rfl⟩ : syracuseStep 1485031 = 2227547) B2227547
theorem B11299999 : Blo 1319478 11299999 := bstep (se 1 (by rfl) ⟨8474999, by rfl⟩ : syracuseStep 11299999 = 16949999) B16949999
theorem B264146939 : Blo 1319478 264146939 := bstep (se 1 (by rfl) ⟨198110204, by rfl⟩ : syracuseStep 264146939 = 396220409) B396220409
theorem B25727519 : Blo 1319478 25727519 := bstep (se 1 (by rfl) ⟨19295639, by rfl⟩ : syracuseStep 25727519 = 38591279) B38591279
theorem B5010569 : Blo 1319478 5010569 := bstep (se 2 (by rfl) ⟨1878963, by rfl⟩ : syracuseStep 5010569 = 3757927) B3757927
theorem B1980263 : Blo 1319478 1980263 := bstep (se 1 (by rfl) ⟨1485197, by rfl⟩ : syracuseStep 1980263 = 2970395) B2970395
theorem B11286971 : Blo 1319478 11286971 := bstep (se 1 (by rfl) ⟨8465228, by rfl⟩ : syracuseStep 11286971 = 16930457) B16930457
theorem B1980863 : Blo 1319478 1980863 := bstep (se 1 (by rfl) ⟨1485647, by rfl⟩ : syracuseStep 1980863 = 2971295) B2971295
theorem B6348307 : Blo 1319478 6348307 := bstep (se 1 (by rfl) ⟨4761230, by rfl⟩ : syracuseStep 6348307 = 9522461) B9522461
theorem B2973311 : Blo 1319478 2973311 := bstep (se 1 (by rfl) ⟨2229983, by rfl⟩ : syracuseStep 2973311 = 4459967) B4459967
theorem B6684443 : Blo 1319478 6684443 := bstep (se 1 (by rfl) ⟨5013332, by rfl⟩ : syracuseStep 6684443 = 10026665) B10026665
theorem B4457321 : Blo 1319478 4457321 := bstep (se 2 (by rfl) ⟨1671495, by rfl⟩ : syracuseStep 4457321 = 3342991) B3342991
theorem B1320175 : Blo 1319478 1320175 := bstep (se 1 (by rfl) ⟨990131, by rfl⟩ : syracuseStep 1320175 = 1980263) B1980263
theorem B2508239 : Blo 1319478 2508239 := bstep (se 1 (by rfl) ⟨1881179, by rfl⟩ : syracuseStep 2508239 = 3762359) B3762359
theorem B15066665 : Blo 1319478 15066665 := bstep (se 2 (by rfl) ⟨5649999, by rfl⟩ : syracuseStep 15066665 = 11299999) B11299999
theorem B1320575 : Blo 1319478 1320575 := bstep (se 1 (by rfl) ⟨990431, by rfl⟩ : syracuseStep 1320575 = 1980863) B1980863
theorem B8464409 : Blo 1319478 8464409 := bstep (se 2 (by rfl) ⟨3174153, by rfl⟩ : syracuseStep 8464409 = 6348307) B6348307
theorem B176097959 : Blo 1319478 176097959 := bstep (se 1 (by rfl) ⟨132073469, by rfl⟩ : syracuseStep 176097959 = 264146939) B264146939
theorem B7524647 : Blo 1319478 7524647 := bstep (se 1 (by rfl) ⟨5643485, by rfl⟩ : syracuseStep 7524647 = 11286971) B11286971
theorem B1980041 : Blo 1319478 1980041 := bstep (se 2 (by rfl) ⟨742515, by rfl⟩ : syracuseStep 1980041 = 1485031) B1485031
theorem B17151679 : Blo 1319478 17151679 := bstep (se 1 (by rfl) ⟨12863759, by rfl⟩ : syracuseStep 17151679 = 25727519) B25727519
theorem B3340379 : Blo 1319478 3340379 := bstep (se 1 (by rfl) ⟨2505284, by rfl⟩ : syracuseStep 3340379 = 5010569) B5010569
theorem B3758633 : Blo 1319478 3758633 := bstep (se 2 (by rfl) ⟨1409487, by rfl⟩ : syracuseStep 3758633 = 2818975) B2818975
theorem B1982207 : Blo 1319478 1982207 := bstep (se 1 (by rfl) ⟨1486655, by rfl⟩ : syracuseStep 1982207 = 2973311) B2973311
theorem B4456295 : Blo 1319478 4456295 := bstep (se 1 (by rfl) ⟨3342221, by rfl⟩ : syracuseStep 4456295 = 6684443) B6684443
theorem B1672159 : Blo 1319478 1672159 := bstep (se 1 (by rfl) ⟨1254119, by rfl⟩ : syracuseStep 1672159 = 2508239) B2508239
theorem B10044443 : Blo 1319478 10044443 := bstep (se 1 (by rfl) ⟨7533332, by rfl⟩ : syracuseStep 10044443 = 15066665) B15066665
theorem B1320027 : Blo 1319478 1320027 := bstep (se 1 (by rfl) ⟨990020, by rfl⟩ : syracuseStep 1320027 = 1980041) B1980041
theorem B1321471 : Blo 1319478 1321471 := bstep (se 1 (by rfl) ⟨991103, by rfl⟩ : syracuseStep 1321471 = 1982207) B1982207
theorem B5016431 : Blo 1319478 5016431 := bstep (se 1 (by rfl) ⟨3762323, by rfl⟩ : syracuseStep 5016431 = 7524647) B7524647
theorem B22868905 : Blo 1319478 22868905 := bstep (se 2 (by rfl) ⟨8575839, by rfl⟩ : syracuseStep 22868905 = 17151679) B17151679
theorem B2970863 : Blo 1319478 2970863 := bstep (se 1 (by rfl) ⟨2228147, by rfl⟩ : syracuseStep 2970863 = 4456295) B4456295
theorem B2971547 : Blo 1319478 2971547 := bstep (se 1 (by rfl) ⟨2228660, by rfl⟩ : syracuseStep 2971547 = 4457321) B4457321
theorem B5642939 : Blo 1319478 5642939 := bstep (se 1 (by rfl) ⟨4232204, by rfl⟩ : syracuseStep 5642939 = 8464409) B8464409
theorem B2226919 : Blo 1319478 2226919 := bstep (se 1 (by rfl) ⟨1670189, by rfl⟩ : syracuseStep 2226919 = 3340379) B3340379
theorem B2505755 : Blo 1319478 2505755 := bstep (se 1 (by rfl) ⟨1879316, by rfl⟩ : syracuseStep 2505755 = 3758633) B3758633
theorem B117398639 : Blo 1319478 117398639 := bstep (se 1 (by rfl) ⟨88048979, by rfl⟩ : syracuseStep 117398639 = 176097959) B176097959
theorem B30491873 : Blo 1319478 30491873 := bstep (se 2 (by rfl) ⟨11434452, by rfl⟩ : syracuseStep 30491873 = 22868905) B22868905
theorem B2229545 : Blo 1319478 2229545 := bstep (se 2 (by rfl) ⟨836079, by rfl⟩ : syracuseStep 2229545 = 1672159) B1672159
theorem B3761959 : Blo 1319478 3761959 := bstep (se 1 (by rfl) ⟨2821469, by rfl⟩ : syracuseStep 3761959 = 5642939) B5642939
theorem B3344287 : Blo 1319478 3344287 := bstep (se 1 (by rfl) ⟨2508215, by rfl⟩ : syracuseStep 3344287 = 5016431) B5016431
theorem B2969225 : Blo 1319478 2969225 := bstep (se 2 (by rfl) ⟨1113459, by rfl⟩ : syracuseStep 2969225 = 2226919) B2226919
theorem B6682013 : Blo 1319478 6682013 := bstep (se 3 (by rfl) ⟨1252877, by rfl⟩ : syracuseStep 6682013 = 2505755) B2505755
theorem B26785181 : Blo 1319478 26785181 := bstep (se 3 (by rfl) ⟨5022221, by rfl⟩ : syracuseStep 26785181 = 10044443) B10044443
theorem B1980575 : Blo 1319478 1980575 := bstep (se 1 (by rfl) ⟨1485431, by rfl⟩ : syracuseStep 1980575 = 2970863) B2970863
theorem B1981031 : Blo 1319478 1981031 := bstep (se 1 (by rfl) ⟨1485773, by rfl⟩ : syracuseStep 1981031 = 2971547) B2971547
theorem B78265759 : Blo 1319478 78265759 := bstep (se 1 (by rfl) ⟨58699319, by rfl⟩ : syracuseStep 78265759 = 117398639) B117398639
theorem B1320383 : Blo 1319478 1320383 := bstep (se 1 (by rfl) ⟨990287, by rfl⟩ : syracuseStep 1320383 = 1980575) B1980575
theorem B1320687 : Blo 1319478 1320687 := bstep (se 1 (by rfl) ⟨990515, by rfl⟩ : syracuseStep 1320687 = 1981031) B1981031
theorem B5015945 : Blo 1319478 5015945 := bstep (se 2 (by rfl) ⟨1880979, by rfl⟩ : syracuseStep 5015945 = 3761959) B3761959
theorem B4459049 : Blo 1319478 4459049 := bstep (se 2 (by rfl) ⟨1672143, by rfl⟩ : syracuseStep 4459049 = 3344287) B3344287
theorem B20327915 : Blo 1319478 20327915 := bstep (se 1 (by rfl) ⟨15245936, by rfl⟩ : syracuseStep 20327915 = 30491873) B30491873
theorem B1486363 : Blo 1319478 1486363 := bstep (se 1 (by rfl) ⟨1114772, by rfl⟩ : syracuseStep 1486363 = 2229545) B2229545
theorem B104354345 : Blo 1319478 104354345 := bstep (se 2 (by rfl) ⟨39132879, by rfl⟩ : syracuseStep 104354345 = 78265759) B78265759
theorem B1979483 : Blo 1319478 1979483 := bstep (se 1 (by rfl) ⟨1484612, by rfl⟩ : syracuseStep 1979483 = 2969225) B2969225
theorem B4454675 : Blo 1319478 4454675 := bstep (se 1 (by rfl) ⟨3341006, by rfl⟩ : syracuseStep 4454675 = 6682013) B6682013
theorem B17856787 : Blo 1319478 17856787 := bstep (se 1 (by rfl) ⟨13392590, by rfl⟩ : syracuseStep 17856787 = 26785181) B26785181
theorem B1319655 : Blo 1319478 1319655 := bstep (se 1 (by rfl) ⟨989741, by rfl⟩ : syracuseStep 1319655 = 1979483) B1979483
theorem B3343963 : Blo 1319478 3343963 := bstep (se 1 (by rfl) ⟨2507972, by rfl⟩ : syracuseStep 3343963 = 5015945) B5015945
theorem B13551943 : Blo 1319478 13551943 := bstep (se 1 (by rfl) ⟨10163957, by rfl⟩ : syracuseStep 13551943 = 20327915) B20327915
theorem B23809049 : Blo 1319478 23809049 := bstep (se 2 (by rfl) ⟨8928393, by rfl⟩ : syracuseStep 23809049 = 17856787) B17856787
theorem B69569563 : Blo 1319478 69569563 := bstep (se 1 (by rfl) ⟨52177172, by rfl⟩ : syracuseStep 69569563 = 104354345) B104354345
theorem B2969783 : Blo 1319478 2969783 := bstep (se 1 (by rfl) ⟨2227337, by rfl⟩ : syracuseStep 2969783 = 4454675) B4454675
theorem B2972699 : Blo 1319478 2972699 := bstep (se 1 (by rfl) ⟨2229524, by rfl⟩ : syracuseStep 2972699 = 4459049) B4459049
theorem B1981817 : Blo 1319478 1981817 := bstep (se 2 (by rfl) ⟨743181, by rfl⟩ : syracuseStep 1981817 = 1486363) B1486363
theorem B92759417 : Blo 1319478 92759417 := bstep (se 2 (by rfl) ⟨34784781, by rfl⟩ : syracuseStep 92759417 = 69569563) B69569563
theorem B4458617 : Blo 1319478 4458617 := bstep (se 2 (by rfl) ⟨1671981, by rfl⟩ : syracuseStep 4458617 = 3343963) B3343963
theorem B1321211 : Blo 1319478 1321211 := bstep (se 1 (by rfl) ⟨990908, by rfl⟩ : syracuseStep 1321211 = 1981817) B1981817
theorem B15872699 : Blo 1319478 15872699 := bstep (se 1 (by rfl) ⟨11904524, by rfl⟩ : syracuseStep 15872699 = 23809049) B23809049
theorem B1979855 : Blo 1319478 1979855 := bstep (se 1 (by rfl) ⟨1484891, by rfl⟩ : syracuseStep 1979855 = 2969783) B2969783
theorem B18069257 : Blo 1319478 18069257 := bstep (se 2 (by rfl) ⟨6775971, by rfl⟩ : syracuseStep 18069257 = 13551943) B13551943
theorem B1981799 : Blo 1319478 1981799 := bstep (se 1 (by rfl) ⟨1486349, by rfl⟩ : syracuseStep 1981799 = 2972699) B2972699
theorem B1319903 : Blo 1319478 1319903 := bstep (se 1 (by rfl) ⟨989927, by rfl⟩ : syracuseStep 1319903 = 1979855) B1979855
theorem B1321199 : Blo 1319478 1321199 := bstep (se 1 (by rfl) ⟨990899, by rfl⟩ : syracuseStep 1321199 = 1981799) B1981799
theorem B12046171 : Blo 1319478 12046171 := bstep (se 1 (by rfl) ⟨9034628, by rfl⟩ : syracuseStep 12046171 = 18069257) B18069257
theorem B61839611 : Blo 1319478 61839611 := bstep (se 1 (by rfl) ⟨46379708, by rfl⟩ : syracuseStep 61839611 = 92759417) B92759417
theorem B2972411 : Blo 1319478 2972411 := bstep (se 1 (by rfl) ⟨2229308, by rfl⟩ : syracuseStep 2972411 = 4458617) B4458617
theorem B42327197 : Blo 1319478 42327197 := bstep (se 3 (by rfl) ⟨7936349, by rfl⟩ : syracuseStep 42327197 = 15872699) B15872699
theorem B41226407 : Blo 1319478 41226407 := bstep (se 1 (by rfl) ⟨30919805, by rfl⟩ : syracuseStep 41226407 = 61839611) B61839611
theorem B28218131 : Blo 1319478 28218131 := bstep (se 1 (by rfl) ⟨21163598, by rfl⟩ : syracuseStep 28218131 = 42327197) B42327197
theorem B16061561 : Blo 1319478 16061561 := bstep (se 2 (by rfl) ⟨6023085, by rfl⟩ : syracuseStep 16061561 = 12046171) B12046171
theorem B1981607 : Blo 1319478 1981607 := bstep (se 1 (by rfl) ⟨1486205, by rfl⟩ : syracuseStep 1981607 = 2972411) B2972411
theorem B27484271 : Blo 1319478 27484271 := bstep (se 1 (by rfl) ⟨20613203, by rfl⟩ : syracuseStep 27484271 = 41226407) B41226407
theorem B10707707 : Blo 1319478 10707707 := bstep (se 1 (by rfl) ⟨8030780, by rfl⟩ : syracuseStep 10707707 = 16061561) B16061561
theorem B1321071 : Blo 1319478 1321071 := bstep (se 1 (by rfl) ⟨990803, by rfl⟩ : syracuseStep 1321071 = 1981607) B1981607
theorem B18812087 : Blo 1319478 18812087 := bstep (se 1 (by rfl) ⟨14109065, by rfl⟩ : syracuseStep 18812087 = 28218131) B28218131
theorem B7138471 : Blo 1319478 7138471 := bstep (se 1 (by rfl) ⟨5353853, by rfl⟩ : syracuseStep 7138471 = 10707707) B10707707
theorem B18322847 : Blo 1319478 18322847 := bstep (se 1 (by rfl) ⟨13742135, by rfl⟩ : syracuseStep 18322847 = 27484271) B27484271
theorem B12541391 : Blo 1319478 12541391 := bstep (se 1 (by rfl) ⟨9406043, by rfl⟩ : syracuseStep 12541391 = 18812087) B18812087
theorem B12215231 : Blo 1319478 12215231 := bstep (se 1 (by rfl) ⟨9161423, by rfl⟩ : syracuseStep 12215231 = 18322847) B18322847
theorem B8360927 : Blo 1319478 8360927 := bstep (se 1 (by rfl) ⟨6270695, by rfl⟩ : syracuseStep 8360927 = 12541391) B12541391
theorem B9517961 : Blo 1319478 9517961 := bstep (se 2 (by rfl) ⟨3569235, by rfl⟩ : syracuseStep 9517961 = 7138471) B7138471
theorem B8143487 : Blo 1319478 8143487 := bstep (se 1 (by rfl) ⟨6107615, by rfl⟩ : syracuseStep 8143487 = 12215231) B12215231
theorem B5573951 : Blo 1319478 5573951 := bstep (se 1 (by rfl) ⟨4180463, by rfl⟩ : syracuseStep 5573951 = 8360927) B8360927
theorem B6345307 : Blo 1319478 6345307 := bstep (se 1 (by rfl) ⟨4758980, by rfl⟩ : syracuseStep 6345307 = 9517961) B9517961
theorem B33841637 : Blo 1319478 33841637 := bstep (se 4 (by rfl) ⟨3172653, by rfl⟩ : syracuseStep 33841637 = 6345307) B6345307
theorem B3715967 : Blo 1319478 3715967 := bstep (se 1 (by rfl) ⟨2786975, by rfl⟩ : syracuseStep 3715967 = 5573951) B5573951
theorem B5428991 : Blo 1319478 5428991 := bstep (se 1 (by rfl) ⟨4071743, by rfl⟩ : syracuseStep 5428991 = 8143487) B8143487
theorem B22561091 : Blo 1319478 22561091 := bstep (se 1 (by rfl) ⟨16920818, by rfl⟩ : syracuseStep 22561091 = 33841637) B33841637
theorem B14477309 : Blo 1319478 14477309 := bstep (se 3 (by rfl) ⟨2714495, by rfl⟩ : syracuseStep 14477309 = 5428991) B5428991
theorem B2477311 : Blo 1319478 2477311 := bstep (se 1 (by rfl) ⟨1857983, by rfl⟩ : syracuseStep 2477311 = 3715967) B3715967
theorem B15040727 : Blo 1319478 15040727 := bstep (se 1 (by rfl) ⟨11280545, by rfl⟩ : syracuseStep 15040727 = 22561091) B22561091
theorem B9651539 : Blo 1319478 9651539 := bstep (se 1 (by rfl) ⟨7238654, by rfl⟩ : syracuseStep 9651539 = 14477309) B14477309
theorem B13212325 : Blo 1319478 13212325 := bstep (se 4 (by rfl) ⟨1238655, by rfl⟩ : syracuseStep 13212325 = 2477311) B2477311
theorem B10027151 : Blo 1319478 10027151 := bstep (se 1 (by rfl) ⟨7520363, by rfl⟩ : syracuseStep 10027151 = 15040727) B15040727
theorem B6434359 : Blo 1319478 6434359 := bstep (se 1 (by rfl) ⟨4825769, by rfl⟩ : syracuseStep 6434359 = 9651539) B9651539
theorem B70465733 : Blo 1319478 70465733 := bstep (se 4 (by rfl) ⟨6606162, by rfl⟩ : syracuseStep 70465733 = 13212325) B13212325
theorem B6684767 : Blo 1319478 6684767 := bstep (se 1 (by rfl) ⟨5013575, by rfl⟩ : syracuseStep 6684767 = 10027151) B10027151
theorem B137266325 : Blo 1319478 137266325 := bstep (se 6 (by rfl) ⟨3217179, by rfl⟩ : syracuseStep 137266325 = 6434359) B6434359
theorem B46977155 : Blo 1319478 46977155 := bstep (se 1 (by rfl) ⟨35232866, by rfl⟩ : syracuseStep 46977155 = 70465733) B70465733
theorem B4456511 : Blo 1319478 4456511 := bstep (se 1 (by rfl) ⟨3342383, by rfl⟩ : syracuseStep 4456511 = 6684767) B6684767
theorem B31318103 : Blo 1319478 31318103 := bstep (se 1 (by rfl) ⟨23488577, by rfl⟩ : syracuseStep 31318103 = 46977155) B46977155
theorem B91510883 : Blo 1319478 91510883 := bstep (se 1 (by rfl) ⟨68633162, by rfl⟩ : syracuseStep 91510883 = 137266325) B137266325
theorem B61007255 : Blo 1319478 61007255 := bstep (se 1 (by rfl) ⟨45755441, by rfl⟩ : syracuseStep 61007255 = 91510883) B91510883
theorem B2971007 : Blo 1319478 2971007 := bstep (se 1 (by rfl) ⟨2228255, by rfl⟩ : syracuseStep 2971007 = 4456511) B4456511
theorem B20878735 : Blo 1319478 20878735 := bstep (se 1 (by rfl) ⟨15659051, by rfl⟩ : syracuseStep 20878735 = 31318103) B31318103
theorem B27838313 : Blo 1319478 27838313 := bstep (se 2 (by rfl) ⟨10439367, by rfl⟩ : syracuseStep 27838313 = 20878735) B20878735
theorem B1980671 : Blo 1319478 1980671 := bstep (se 1 (by rfl) ⟨1485503, by rfl⟩ : syracuseStep 1980671 = 2971007) B2971007
theorem B40671503 : Blo 1319478 40671503 := bstep (se 1 (by rfl) ⟨30503627, by rfl⟩ : syracuseStep 40671503 = 61007255) B61007255
theorem B1320447 : Blo 1319478 1320447 := bstep (se 1 (by rfl) ⟨990335, by rfl⟩ : syracuseStep 1320447 = 1980671) B1980671
theorem B18558875 : Blo 1319478 18558875 := bstep (se 1 (by rfl) ⟨13919156, by rfl⟩ : syracuseStep 18558875 = 27838313) B27838313
theorem B27114335 : Blo 1319478 27114335 := bstep (se 1 (by rfl) ⟨20335751, by rfl⟩ : syracuseStep 27114335 = 40671503) B40671503
theorem B12372583 : Blo 1319478 12372583 := bstep (se 1 (by rfl) ⟨9279437, by rfl⟩ : syracuseStep 12372583 = 18558875) B18558875
theorem B18076223 : Blo 1319478 18076223 := bstep (se 1 (by rfl) ⟨13557167, by rfl⟩ : syracuseStep 18076223 = 27114335) B27114335
theorem B12050815 : Blo 1319478 12050815 := bstep (se 1 (by rfl) ⟨9038111, by rfl⟩ : syracuseStep 12050815 = 18076223) B18076223
theorem B16496777 : Blo 1319478 16496777 := bstep (se 2 (by rfl) ⟨6186291, by rfl⟩ : syracuseStep 16496777 = 12372583) B12372583
theorem B16067753 : Blo 1319478 16067753 := bstep (se 2 (by rfl) ⟨6025407, by rfl⟩ : syracuseStep 16067753 = 12050815) B12050815
theorem B10997851 : Blo 1319478 10997851 := bstep (se 1 (by rfl) ⟨8248388, by rfl⟩ : syracuseStep 10997851 = 16496777) B16496777
theorem B14663801 : Blo 1319478 14663801 := bstep (se 2 (by rfl) ⟨5498925, by rfl⟩ : syracuseStep 14663801 = 10997851) B10997851
theorem B10711835 : Blo 1319478 10711835 := bstep (se 1 (by rfl) ⟨8033876, by rfl⟩ : syracuseStep 10711835 = 16067753) B16067753
theorem B39103469 : Blo 1319478 39103469 := bstep (se 3 (by rfl) ⟨7331900, by rfl⟩ : syracuseStep 39103469 = 14663801) B14663801
theorem B7141223 : Blo 1319478 7141223 := bstep (se 1 (by rfl) ⟨5355917, by rfl⟩ : syracuseStep 7141223 = 10711835) B10711835
theorem B4760815 : Blo 1319478 4760815 := bstep (se 1 (by rfl) ⟨3570611, by rfl⟩ : syracuseStep 4760815 = 7141223) B7141223
theorem B26068979 : Blo 1319478 26068979 := bstep (se 1 (by rfl) ⟨19551734, by rfl⟩ : syracuseStep 26068979 = 39103469) B39103469
theorem B17379319 : Blo 1319478 17379319 := bstep (se 1 (by rfl) ⟨13034489, by rfl⟩ : syracuseStep 17379319 = 26068979) B26068979
theorem B6347753 : Blo 1319478 6347753 := bstep (se 2 (by rfl) ⟨2380407, by rfl⟩ : syracuseStep 6347753 = 4760815) B4760815
theorem B4231835 : Blo 1319478 4231835 := bstep (se 1 (by rfl) ⟨3173876, by rfl⟩ : syracuseStep 4231835 = 6347753) B6347753
theorem B23172425 : Blo 1319478 23172425 := bstep (se 2 (by rfl) ⟨8689659, by rfl⟩ : syracuseStep 23172425 = 17379319) B17379319
theorem B2821223 : Blo 1319478 2821223 := bstep (se 1 (by rfl) ⟨2115917, by rfl⟩ : syracuseStep 2821223 = 4231835) B4231835
theorem B15448283 : Blo 1319478 15448283 := bstep (se 1 (by rfl) ⟨11586212, by rfl⟩ : syracuseStep 15448283 = 23172425) B23172425
theorem B10298855 : Blo 1319478 10298855 := bstep (se 1 (by rfl) ⟨7724141, by rfl⟩ : syracuseStep 10298855 = 15448283) B15448283
theorem B1880815 : Blo 1319478 1880815 := bstep (se 1 (by rfl) ⟨1410611, by rfl⟩ : syracuseStep 1880815 = 2821223) B2821223
theorem B2507753 : Blo 1319478 2507753 := bstep (se 2 (by rfl) ⟨940407, by rfl⟩ : syracuseStep 2507753 = 1880815) B1880815
theorem B6865903 : Blo 1319478 6865903 := bstep (se 1 (by rfl) ⟨5149427, by rfl⟩ : syracuseStep 6865903 = 10298855) B10298855
theorem B1671835 : Blo 1319478 1671835 := bstep (se 1 (by rfl) ⟨1253876, by rfl⟩ : syracuseStep 1671835 = 2507753) B2507753
theorem B36618149 : Blo 1319478 36618149 := bstep (se 4 (by rfl) ⟨3432951, by rfl⟩ : syracuseStep 36618149 = 6865903) B6865903
theorem B2229113 : Blo 1319478 2229113 := bstep (se 2 (by rfl) ⟨835917, by rfl⟩ : syracuseStep 2229113 = 1671835) B1671835
theorem B24412099 : Blo 1319478 24412099 := bstep (se 1 (by rfl) ⟨18309074, by rfl⟩ : syracuseStep 24412099 = 36618149) B36618149
theorem B32549465 : Blo 1319478 32549465 := bstep (se 2 (by rfl) ⟨12206049, by rfl⟩ : syracuseStep 32549465 = 24412099) B24412099
theorem B1486075 : Blo 1319478 1486075 := bstep (se 1 (by rfl) ⟨1114556, by rfl⟩ : syracuseStep 1486075 = 2229113) B2229113
theorem B86798573 : Blo 1319478 86798573 := bstep (se 3 (by rfl) ⟨16274732, by rfl⟩ : syracuseStep 86798573 = 32549465) B32549465
theorem B1981433 : Blo 1319478 1981433 := bstep (se 2 (by rfl) ⟨743037, by rfl⟩ : syracuseStep 1981433 = 1486075) B1486075
theorem B1320955 : Blo 1319478 1320955 := bstep (se 1 (by rfl) ⟨990716, by rfl⟩ : syracuseStep 1320955 = 1981433) B1981433
theorem B57865715 : Blo 1319478 57865715 := bstep (se 1 (by rfl) ⟨43399286, by rfl⟩ : syracuseStep 57865715 = 86798573) B86798573
theorem B38577143 : Blo 1319478 38577143 := bstep (se 1 (by rfl) ⟨28932857, by rfl⟩ : syracuseStep 38577143 = 57865715) B57865715
theorem B25718095 : Blo 1319478 25718095 := bstep (se 1 (by rfl) ⟨19288571, by rfl⟩ : syracuseStep 25718095 = 38577143) B38577143
theorem B34290793 : Blo 1319478 34290793 := bstep (se 2 (by rfl) ⟨12859047, by rfl⟩ : syracuseStep 34290793 = 25718095) B25718095
theorem B45721057 : Blo 1319478 45721057 := bstep (se 2 (by rfl) ⟨17145396, by rfl⟩ : syracuseStep 45721057 = 34290793) B34290793
theorem B60961409 : Blo 1319478 60961409 := bstep (se 2 (by rfl) ⟨22860528, by rfl⟩ : syracuseStep 60961409 = 45721057) B45721057
theorem B40640939 : Blo 1319478 40640939 := bstep (se 1 (by rfl) ⟨30480704, by rfl⟩ : syracuseStep 40640939 = 60961409) B60961409
theorem B27093959 : Blo 1319478 27093959 := bstep (se 1 (by rfl) ⟨20320469, by rfl⟩ : syracuseStep 27093959 = 40640939) B40640939
theorem B18062639 : Blo 1319478 18062639 := bstep (se 1 (by rfl) ⟨13546979, by rfl⟩ : syracuseStep 18062639 = 27093959) B27093959
theorem B12041759 : Blo 1319478 12041759 := bstep (se 1 (by rfl) ⟨9031319, by rfl⟩ : syracuseStep 12041759 = 18062639) B18062639
theorem B8027839 : Blo 1319478 8027839 := bstep (se 1 (by rfl) ⟨6020879, by rfl⟩ : syracuseStep 8027839 = 12041759) B12041759
theorem B42815141 : Blo 1319478 42815141 := bstep (se 4 (by rfl) ⟨4013919, by rfl⟩ : syracuseStep 42815141 = 8027839) B8027839
theorem B28543427 : Blo 1319478 28543427 := bstep (se 1 (by rfl) ⟨21407570, by rfl⟩ : syracuseStep 28543427 = 42815141) B42815141
theorem B19028951 : Blo 1319478 19028951 := bstep (se 1 (by rfl) ⟨14271713, by rfl⟩ : syracuseStep 19028951 = 28543427) B28543427
theorem B12685967 : Blo 1319478 12685967 := bstep (se 1 (by rfl) ⟨9514475, by rfl⟩ : syracuseStep 12685967 = 19028951) B19028951
theorem B8457311 : Blo 1319478 8457311 := bstep (se 1 (by rfl) ⟨6342983, by rfl⟩ : syracuseStep 8457311 = 12685967) B12685967
theorem B5638207 : Blo 1319478 5638207 := bstep (se 1 (by rfl) ⟨4228655, by rfl⟩ : syracuseStep 5638207 = 8457311) B8457311
theorem B7517609 : Blo 1319478 7517609 := bstep (se 2 (by rfl) ⟨2819103, by rfl⟩ : syracuseStep 7517609 = 5638207) B5638207
theorem B5011739 : Blo 1319478 5011739 := bstep (se 1 (by rfl) ⟨3758804, by rfl⟩ : syracuseStep 5011739 = 7517609) B7517609
theorem B3341159 : Blo 1319478 3341159 := bstep (se 1 (by rfl) ⟨2505869, by rfl⟩ : syracuseStep 3341159 = 5011739) B5011739
theorem B2227439 : Blo 1319478 2227439 := bstep (se 1 (by rfl) ⟨1670579, by rfl⟩ : syracuseStep 2227439 = 3341159) B3341159
theorem B1484959 : Blo 1319478 1484959 := bstep (se 1 (by rfl) ⟨1113719, by rfl⟩ : syracuseStep 1484959 = 2227439) B2227439
theorem B1979945 : Blo 1319478 1979945 := bstep (se 2 (by rfl) ⟨742479, by rfl⟩ : syracuseStep 1979945 = 1484959) B1484959
theorem B1319963 : Blo 1319478 1319963 := bstep (se 1 (by rfl) ⟨989972, by rfl⟩ : syracuseStep 1319963 = 1979945) B1979945

theorem C0 (j : ℕ) (h1 : 329869 ≤ j) (h2 : j ≤ 330368) : Blo 1319478 (4 * j + 3) := by
  interval_cases j
  · exact B1319479
  · exact B1319483
  · exact B1319487
  · exact B1319491
  · exact B1319495
  · exact B1319499
  · exact B1319503
  · exact B1319507
  · exact B1319511
  · exact B1319515
  · exact B1319519
  · exact B1319523
  · exact B1319527
  · exact B1319531
  · exact B1319535
  · exact B1319539
  · exact B1319543
  · exact B1319547
  · exact B1319551
  · exact B1319555
  · exact B1319559
  · exact B1319563
  · exact B1319567
  · exact B1319571
  · exact B1319575
  · exact B1319579
  · exact B1319583
  · exact B1319587
  · exact B1319591
  · exact B1319595
  · exact B1319599
  · exact B1319603
  · exact B1319607
  · exact B1319611
  · exact B1319615
  · exact B1319619
  · exact B1319623
  · exact B1319627
  · exact B1319631
  · exact B1319635
  · exact B1319639
  · exact B1319643
  · exact B1319647
  · exact B1319651
  · exact B1319655
  · exact B1319659
  · exact B1319663
  · exact B1319667
  · exact B1319671
  · exact B1319675
  · exact B1319679
  · exact B1319683
  · exact B1319687
  · exact B1319691
  · exact B1319695
  · exact B1319699
  · exact B1319703
  · exact B1319707
  · exact B1319711
  · exact B1319715
  · exact B1319719
  · exact B1319723
  · exact B1319727
  · exact B1319731
  · exact B1319735
  · exact B1319739
  · exact B1319743
  · exact B1319747
  · exact B1319751
  · exact B1319755
  · exact B1319759
  · exact B1319763
  · exact B1319767
  · exact B1319771
  · exact B1319775
  · exact B1319779
  · exact B1319783
  · exact B1319787
  · exact B1319791
  · exact B1319795
  · exact B1319799
  · exact B1319803
  · exact B1319807
  · exact B1319811
  · exact B1319815
  · exact B1319819
  · exact B1319823
  · exact B1319827
  · exact B1319831
  · exact B1319835
  · exact B1319839
  · exact B1319843
  · exact B1319847
  · exact B1319851
  · exact B1319855
  · exact B1319859
  · exact B1319863
  · exact B1319867
  · exact B1319871
  · exact B1319875
  · exact B1319879
  · exact B1319883
  · exact B1319887
  · exact B1319891
  · exact B1319895
  · exact B1319899
  · exact B1319903
  · exact B1319907
  · exact B1319911
  · exact B1319915
  · exact B1319919
  · exact B1319923
  · exact B1319927
  · exact B1319931
  · exact B1319935
  · exact B1319939
  · exact B1319943
  · exact B1319947
  · exact B1319951
  · exact B1319955
  · exact B1319959
  · exact B1319963
  · exact B1319967
  · exact B1319971
  · exact B1319975
  · exact B1319979
  · exact B1319983
  · exact B1319987
  · exact B1319991
  · exact B1319995
  · exact B1319999
  · exact B1320003
  · exact B1320007
  · exact B1320011
  · exact B1320015
  · exact B1320019
  · exact B1320023
  · exact B1320027
  · exact B1320031
  · exact B1320035
  · exact B1320039
  · exact B1320043
  · exact B1320047
  · exact B1320051
  · exact B1320055
  · exact B1320059
  · exact B1320063
  · exact B1320067
  · exact B1320071
  · exact B1320075
  · exact B1320079
  · exact B1320083
  · exact B1320087
  · exact B1320091
  · exact B1320095
  · exact B1320099
  · exact B1320103
  · exact B1320107
  · exact B1320111
  · exact B1320115
  · exact B1320119
  · exact B1320123
  · exact B1320127
  · exact B1320131
  · exact B1320135
  · exact B1320139
  · exact B1320143
  · exact B1320147
  · exact B1320151
  · exact B1320155
  · exact B1320159
  · exact B1320163
  · exact B1320167
  · exact B1320171
  · exact B1320175
  · exact B1320179
  · exact B1320183
  · exact B1320187
  · exact B1320191
  · exact B1320195
  · exact B1320199
  · exact B1320203
  · exact B1320207
  · exact B1320211
  · exact B1320215
  · exact B1320219
  · exact B1320223
  · exact B1320227
  · exact B1320231
  · exact B1320235
  · exact B1320239
  · exact B1320243
  · exact B1320247
  · exact B1320251
  · exact B1320255
  · exact B1320259
  · exact B1320263
  · exact B1320267
  · exact B1320271
  · exact B1320275
  · exact B1320279
  · exact B1320283
  · exact B1320287
  · exact B1320291
  · exact B1320295
  · exact B1320299
  · exact B1320303
  · exact B1320307
  · exact B1320311
  · exact B1320315
  · exact B1320319
  · exact B1320323
  · exact B1320327
  · exact B1320331
  · exact B1320335
  · exact B1320339
  · exact B1320343
  · exact B1320347
  · exact B1320351
  · exact B1320355
  · exact B1320359
  · exact B1320363
  · exact B1320367
  · exact B1320371
  · exact B1320375
  · exact B1320379
  · exact B1320383
  · exact B1320387
  · exact B1320391
  · exact B1320395
  · exact B1320399
  · exact B1320403
  · exact B1320407
  · exact B1320411
  · exact B1320415
  · exact B1320419
  · exact B1320423
  · exact B1320427
  · exact B1320431
  · exact B1320435
  · exact B1320439
  · exact B1320443
  · exact B1320447
  · exact B1320451
  · exact B1320455
  · exact B1320459
  · exact B1320463
  · exact B1320467
  · exact B1320471
  · exact B1320475
  · exact B1320479
  · exact B1320483
  · exact B1320487
  · exact B1320491
  · exact B1320495
  · exact B1320499
  · exact B1320503
  · exact B1320507
  · exact B1320511
  · exact B1320515
  · exact B1320519
  · exact B1320523
  · exact B1320527
  · exact B1320531
  · exact B1320535
  · exact B1320539
  · exact B1320543
  · exact B1320547
  · exact B1320551
  · exact B1320555
  · exact B1320559
  · exact B1320563
  · exact B1320567
  · exact B1320571
  · exact B1320575
  · exact B1320579
  · exact B1320583
  · exact B1320587
  · exact B1320591
  · exact B1320595
  · exact B1320599
  · exact B1320603
  · exact B1320607
  · exact B1320611
  · exact B1320615
  · exact B1320619
  · exact B1320623
  · exact B1320627
  · exact B1320631
  · exact B1320635
  · exact B1320639
  · exact B1320643
  · exact B1320647
  · exact B1320651
  · exact B1320655
  · exact B1320659
  · exact B1320663
  · exact B1320667
  · exact B1320671
  · exact B1320675
  · exact B1320679
  · exact B1320683
  · exact B1320687
  · exact B1320691
  · exact B1320695
  · exact B1320699
  · exact B1320703
  · exact B1320707
  · exact B1320711
  · exact B1320715
  · exact B1320719
  · exact B1320723
  · exact B1320727
  · exact B1320731
  · exact B1320735
  · exact B1320739
  · exact B1320743
  · exact B1320747
  · exact B1320751
  · exact B1320755
  · exact B1320759
  · exact B1320763
  · exact B1320767
  · exact B1320771
  · exact B1320775
  · exact B1320779
  · exact B1320783
  · exact B1320787
  · exact B1320791
  · exact B1320795
  · exact B1320799
  · exact B1320803
  · exact B1320807
  · exact B1320811
  · exact B1320815
  · exact B1320819
  · exact B1320823
  · exact B1320827
  · exact B1320831
  · exact B1320835
  · exact B1320839
  · exact B1320843
  · exact B1320847
  · exact B1320851
  · exact B1320855
  · exact B1320859
  · exact B1320863
  · exact B1320867
  · exact B1320871
  · exact B1320875
  · exact B1320879
  · exact B1320883
  · exact B1320887
  · exact B1320891
  · exact B1320895
  · exact B1320899
  · exact B1320903
  · exact B1320907
  · exact B1320911
  · exact B1320915
  · exact B1320919
  · exact B1320923
  · exact B1320927
  · exact B1320931
  · exact B1320935
  · exact B1320939
  · exact B1320943
  · exact B1320947
  · exact B1320951
  · exact B1320955
  · exact B1320959
  · exact B1320963
  · exact B1320967
  · exact B1320971
  · exact B1320975
  · exact B1320979
  · exact B1320983
  · exact B1320987
  · exact B1320991
  · exact B1320995
  · exact B1320999
  · exact B1321003
  · exact B1321007
  · exact B1321011
  · exact B1321015
  · exact B1321019
  · exact B1321023
  · exact B1321027
  · exact B1321031
  · exact B1321035
  · exact B1321039
  · exact B1321043
  · exact B1321047
  · exact B1321051
  · exact B1321055
  · exact B1321059
  · exact B1321063
  · exact B1321067
  · exact B1321071
  · exact B1321075
  · exact B1321079
  · exact B1321083
  · exact B1321087
  · exact B1321091
  · exact B1321095
  · exact B1321099
  · exact B1321103
  · exact B1321107
  · exact B1321111
  · exact B1321115
  · exact B1321119
  · exact B1321123
  · exact B1321127
  · exact B1321131
  · exact B1321135
  · exact B1321139
  · exact B1321143
  · exact B1321147
  · exact B1321151
  · exact B1321155
  · exact B1321159
  · exact B1321163
  · exact B1321167
  · exact B1321171
  · exact B1321175
  · exact B1321179
  · exact B1321183
  · exact B1321187
  · exact B1321191
  · exact B1321195
  · exact B1321199
  · exact B1321203
  · exact B1321207
  · exact B1321211
  · exact B1321215
  · exact B1321219
  · exact B1321223
  · exact B1321227
  · exact B1321231
  · exact B1321235
  · exact B1321239
  · exact B1321243
  · exact B1321247
  · exact B1321251
  · exact B1321255
  · exact B1321259
  · exact B1321263
  · exact B1321267
  · exact B1321271
  · exact B1321275
  · exact B1321279
  · exact B1321283
  · exact B1321287
  · exact B1321291
  · exact B1321295
  · exact B1321299
  · exact B1321303
  · exact B1321307
  · exact B1321311
  · exact B1321315
  · exact B1321319
  · exact B1321323
  · exact B1321327
  · exact B1321331
  · exact B1321335
  · exact B1321339
  · exact B1321343
  · exact B1321347
  · exact B1321351
  · exact B1321355
  · exact B1321359
  · exact B1321363
  · exact B1321367
  · exact B1321371
  · exact B1321375
  · exact B1321379
  · exact B1321383
  · exact B1321387
  · exact B1321391
  · exact B1321395
  · exact B1321399
  · exact B1321403
  · exact B1321407
  · exact B1321411
  · exact B1321415
  · exact B1321419
  · exact B1321423
  · exact B1321427
  · exact B1321431
  · exact B1321435
  · exact B1321439
  · exact B1321443
  · exact B1321447
  · exact B1321451
  · exact B1321455
  · exact B1321459
  · exact B1321463
  · exact B1321467
  · exact B1321471
  · exact B1321475

theorem solution (m : ℕ) (hlo : 1319478 ≤ m) (hhi : m ≤ 1321478) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 329869 ≤ j := by omega
    have hj2 : j ≤ 330368 := by omega
    have hb : Blo 1319478 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
