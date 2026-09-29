-- Prove2me | solution 1 for syracuse_descends_range_988596_992596
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:10.188483+00:00
-- url     : https://prove2.me/submissions/eba3ad01-de9b-4dd0-ac02-6920344af97e

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


theorem B2228237 : Blo 988596 2228237 := bbase (se 3 (by rfl) ⟨417794, by rfl⟩ : syracuseStep 2228237 = 835589) (by norm_num)
theorem B1114141 : Blo 988596 1114141 := bbase (se 3 (by rfl) ⟨208901, by rfl⟩ : syracuseStep 1114141 = 417803) (by norm_num)
theorem B1671205 : Blo 988596 1671205 := bbase (se 4 (by rfl) ⟨156675, by rfl⟩ : syracuseStep 1671205 = 313351) (by norm_num)
theorem B1114177 : Blo 988596 1114177 := bbase (se 2 (by rfl) ⟨417816, by rfl⟩ : syracuseStep 1114177 = 835633) (by norm_num)
theorem B2228309 : Blo 988596 2228309 := bbase (se 8 (by rfl) ⟨13056, by rfl⟩ : syracuseStep 2228309 = 26113) (by norm_num)
theorem B3342437 : Blo 988596 3342437 := bbase (se 4 (by rfl) ⟨313353, by rfl⟩ : syracuseStep 3342437 = 626707) (by norm_num)
theorem B1114213 : Blo 988596 1114213 := bbase (se 4 (by rfl) ⟨104457, by rfl⟩ : syracuseStep 1114213 = 208915) (by norm_num)
theorem B1671293 : Blo 988596 1671293 := bbase (se 3 (by rfl) ⟨313367, by rfl⟩ : syracuseStep 1671293 = 626735) (by norm_num)
theorem B1114249 : Blo 988596 1114249 := bbase (se 2 (by rfl) ⟨417843, by rfl⟩ : syracuseStep 1114249 = 835687) (by norm_num)
theorem B2228381 : Blo 988596 2228381 := bbase (se 3 (by rfl) ⟨417821, by rfl⟩ : syracuseStep 2228381 = 835643) (by norm_num)
theorem B3571877 : Blo 988596 3571877 := bbase (se 4 (by rfl) ⟨334863, by rfl⟩ : syracuseStep 3571877 = 669727) (by norm_num)
theorem B1114285 : Blo 988596 1114285 := bbase (se 3 (by rfl) ⟨208928, by rfl⟩ : syracuseStep 1114285 = 417857) (by norm_num)
theorem B1114321 : Blo 988596 1114321 := bbase (se 2 (by rfl) ⟨417870, by rfl⟩ : syracuseStep 1114321 = 835741) (by norm_num)
theorem B2228453 : Blo 988596 2228453 := bbase (se 4 (by rfl) ⟨208917, by rfl⟩ : syracuseStep 2228453 = 417835) (by norm_num)
theorem B1114357 : Blo 988596 1114357 := bbase (se 5 (by rfl) ⟨52235, by rfl⟩ : syracuseStep 1114357 = 104471) (by norm_num)
theorem B3768565 : Blo 988596 3768565 := bbase (se 5 (by rfl) ⟨176651, by rfl⟩ : syracuseStep 3768565 = 353303) (by norm_num)
theorem B1671421 : Blo 988596 1671421 := bbase (se 3 (by rfl) ⟨313391, by rfl⟩ : syracuseStep 1671421 = 626783) (by norm_num)
theorem B1114393 : Blo 988596 1114393 := bbase (se 2 (by rfl) ⟨417897, by rfl⟩ : syracuseStep 1114393 = 835795) (by norm_num)
theorem B1507621 : Blo 988596 1507621 := bbase (se 4 (by rfl) ⟨141339, by rfl⟩ : syracuseStep 1507621 = 282679) (by norm_num)
theorem B2228525 : Blo 988596 2228525 := bbase (se 3 (by rfl) ⟨417848, by rfl⟩ : syracuseStep 2228525 = 835697) (by norm_num)
theorem B1114429 : Blo 988596 1114429 := bbase (se 3 (by rfl) ⟨208955, by rfl⟩ : syracuseStep 1114429 = 417911) (by norm_num)
theorem B1671509 : Blo 988596 1671509 := bbase (se 10 (by rfl) ⟨2448, by rfl⟩ : syracuseStep 1671509 = 4897) (by norm_num)
theorem B1114465 : Blo 988596 1114465 := bbase (se 2 (by rfl) ⟨417924, by rfl⟩ : syracuseStep 1114465 = 835849) (by norm_num)
theorem B2818405 : Blo 988596 2818405 := bbase (se 4 (by rfl) ⟨264225, by rfl⟩ : syracuseStep 2818405 = 528451) (by norm_num)
theorem B2228597 : Blo 988596 2228597 := bbase (se 5 (by rfl) ⟨104465, by rfl⟩ : syracuseStep 2228597 = 208931) (by norm_num)
theorem B1114501 : Blo 988596 1114501 := bbase (se 4 (by rfl) ⟨104484, by rfl⟩ : syracuseStep 1114501 = 208969) (by norm_num)
theorem B1114537 : Blo 988596 1114537 := bbase (se 2 (by rfl) ⟨417951, by rfl⟩ : syracuseStep 1114537 = 835903) (by norm_num)
theorem B2228669 : Blo 988596 2228669 := bbase (se 3 (by rfl) ⟨417875, by rfl⟩ : syracuseStep 2228669 = 835751) (by norm_num)
theorem B1114573 : Blo 988596 1114573 := bbase (se 3 (by rfl) ⟨208982, by rfl⟩ : syracuseStep 1114573 = 417965) (by norm_num)
theorem B1671637 : Blo 988596 1671637 := bbase (se 7 (by rfl) ⟨19589, by rfl⟩ : syracuseStep 1671637 = 39179) (by norm_num)
theorem B1114609 : Blo 988596 1114609 := bbase (se 2 (by rfl) ⟨417978, by rfl⟩ : syracuseStep 1114609 = 835957) (by norm_num)
theorem B2228741 : Blo 988596 2228741 := bbase (se 4 (by rfl) ⟨208944, by rfl⟩ : syracuseStep 2228741 = 417889) (by norm_num)
theorem B3342869 : Blo 988596 3342869 := bbase (se 6 (by rfl) ⟨78348, by rfl⟩ : syracuseStep 3342869 = 156697) (by norm_num)
theorem B1114645 : Blo 988596 1114645 := bbase (se 6 (by rfl) ⟨26124, by rfl⟩ : syracuseStep 1114645 = 52249) (by norm_num)
theorem B3867173 : Blo 988596 3867173 := bbase (se 4 (by rfl) ⟨362547, by rfl⟩ : syracuseStep 3867173 = 725095) (by norm_num)
theorem B1671725 : Blo 988596 1671725 := bbase (se 3 (by rfl) ⟨313448, by rfl⟩ : syracuseStep 1671725 = 626897) (by norm_num)
theorem B1114681 : Blo 988596 1114681 := bbase (se 2 (by rfl) ⟨418005, by rfl⟩ : syracuseStep 1114681 = 836011) (by norm_num)
theorem B2228813 : Blo 988596 2228813 := bbase (se 3 (by rfl) ⟨417902, by rfl⟩ : syracuseStep 2228813 = 835805) (by norm_num)
theorem B1114717 : Blo 988596 1114717 := bbase (se 3 (by rfl) ⟨209009, by rfl⟩ : syracuseStep 1114717 = 418019) (by norm_num)
theorem B1409653 : Blo 988596 1409653 := bbase (se 5 (by rfl) ⟨66077, by rfl⟩ : syracuseStep 1409653 = 132155) (by norm_num)
theorem B1114753 : Blo 988596 1114753 := bbase (se 2 (by rfl) ⟨418032, by rfl⟩ : syracuseStep 1114753 = 836065) (by norm_num)
theorem B2228885 : Blo 988596 2228885 := bbase (se 6 (by rfl) ⟨52239, by rfl⟩ : syracuseStep 2228885 = 104479) (by norm_num)
theorem B1114789 : Blo 988596 1114789 := bbase (se 4 (by rfl) ⟨104511, by rfl⟩ : syracuseStep 1114789 = 209023) (by norm_num)
theorem B1671853 : Blo 988596 1671853 := bbase (se 3 (by rfl) ⟨313472, by rfl⟩ : syracuseStep 1671853 = 626945) (by norm_num)
theorem B5636789 : Blo 988596 5636789 := bbase (se 5 (by rfl) ⟨264224, by rfl⟩ : syracuseStep 5636789 = 528449) (by norm_num)
theorem B1114825 : Blo 988596 1114825 := bbase (se 2 (by rfl) ⟨418059, by rfl⟩ : syracuseStep 1114825 = 836119) (by norm_num)
theorem B2228957 : Blo 988596 2228957 := bbase (se 3 (by rfl) ⟨417929, by rfl⟩ : syracuseStep 2228957 = 835859) (by norm_num)
theorem B4752101 : Blo 988596 4752101 := bbase (se 4 (by rfl) ⟨445509, by rfl⟩ : syracuseStep 4752101 = 891019) (by norm_num)
theorem B1114861 : Blo 988596 1114861 := bbase (se 3 (by rfl) ⟨209036, by rfl⟩ : syracuseStep 1114861 = 418073) (by norm_num)
theorem B1671941 : Blo 988596 1671941 := bbase (se 4 (by rfl) ⟨156744, by rfl⟩ : syracuseStep 1671941 = 313489) (by norm_num)
theorem B1114897 : Blo 988596 1114897 := bbase (se 2 (by rfl) ⟨418086, by rfl⟩ : syracuseStep 1114897 = 836173) (by norm_num)
theorem B2229029 : Blo 988596 2229029 := bbase (se 4 (by rfl) ⟨208971, by rfl⟩ : syracuseStep 2229029 = 417943) (by norm_num)
theorem B1114933 : Blo 988596 1114933 := bbase (se 5 (by rfl) ⟨52262, by rfl⟩ : syracuseStep 1114933 = 104525) (by norm_num)
theorem B1114969 : Blo 988596 1114969 := bbase (se 2 (by rfl) ⟨418113, by rfl⟩ : syracuseStep 1114969 = 836227) (by norm_num)
theorem B3572581 : Blo 988596 3572581 := bbase (se 4 (by rfl) ⟨334929, by rfl⟩ : syracuseStep 3572581 = 669859) (by norm_num)
theorem B2229101 : Blo 988596 2229101 := bbase (se 3 (by rfl) ⟨417956, by rfl⟩ : syracuseStep 2229101 = 835913) (by norm_num)
theorem B1115005 : Blo 988596 1115005 := bbase (se 3 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 1115005 = 418127) (by norm_num)
theorem B1672069 : Blo 988596 1672069 := bbase (se 4 (by rfl) ⟨156756, by rfl⟩ : syracuseStep 1672069 = 313513) (by norm_num)
theorem B1115041 : Blo 988596 1115041 := bbase (se 2 (by rfl) ⟨418140, by rfl⟩ : syracuseStep 1115041 = 836281) (by norm_num)
theorem B2229173 : Blo 988596 2229173 := bbase (se 5 (by rfl) ⟨104492, by rfl⟩ : syracuseStep 2229173 = 208985) (by norm_num)
theorem B1409989 : Blo 988596 1409989 := bbase (se 4 (by rfl) ⟨132186, by rfl⟩ : syracuseStep 1409989 = 264373) (by norm_num)
theorem B3343301 : Blo 988596 3343301 := bbase (se 4 (by rfl) ⟨313434, by rfl⟩ : syracuseStep 3343301 = 626869) (by norm_num)
theorem B1115077 : Blo 988596 1115077 := bbase (se 4 (by rfl) ⟨104538, by rfl⟩ : syracuseStep 1115077 = 209077) (by norm_num)
theorem B1672157 : Blo 988596 1672157 := bbase (se 3 (by rfl) ⟨313529, by rfl⟩ : syracuseStep 1672157 = 627059) (by norm_num)
theorem B1115113 : Blo 988596 1115113 := bbase (se 2 (by rfl) ⟨418167, by rfl⟩ : syracuseStep 1115113 = 836335) (by norm_num)
theorem B2229245 : Blo 988596 2229245 := bbase (se 3 (by rfl) ⟨417983, by rfl⟩ : syracuseStep 2229245 = 835967) (by norm_num)
theorem B1115149 : Blo 988596 1115149 := bbase (se 3 (by rfl) ⟨209090, by rfl⟩ : syracuseStep 1115149 = 418181) (by norm_num)
theorem B7144469 : Blo 988596 7144469 := bbase (se 6 (by rfl) ⟨167448, by rfl⟩ : syracuseStep 7144469 = 334897) (by norm_num)
theorem B1115185 : Blo 988596 1115185 := bbase (se 2 (by rfl) ⟨418194, by rfl⟩ : syracuseStep 1115185 = 836389) (by norm_num)
theorem B2229317 : Blo 988596 2229317 := bbase (se 4 (by rfl) ⟨208998, by rfl⟩ : syracuseStep 2229317 = 417997) (by norm_num)
theorem B1115221 : Blo 988596 1115221 := bbase (se 8 (by rfl) ⟨6534, by rfl⟩ : syracuseStep 1115221 = 13069) (by norm_num)
theorem B1672285 : Blo 988596 1672285 := bbase (se 3 (by rfl) ⟨313553, by rfl⟩ : syracuseStep 1672285 = 627107) (by norm_num)
theorem B1115257 : Blo 988596 1115257 := bbase (se 2 (by rfl) ⟨418221, by rfl⟩ : syracuseStep 1115257 = 836443) (by norm_num)
theorem B2229389 : Blo 988596 2229389 := bbase (se 3 (by rfl) ⟨418010, by rfl⟩ : syracuseStep 2229389 = 836021) (by norm_num)
theorem B1410205 : Blo 988596 1410205 := bbase (se 3 (by rfl) ⟨264413, by rfl⟩ : syracuseStep 1410205 = 528827) (by norm_num)
theorem B1115293 : Blo 988596 1115293 := bbase (se 3 (by rfl) ⟨209117, by rfl⟩ : syracuseStep 1115293 = 418235) (by norm_num)
theorem B5014709 : Blo 988596 5014709 := bbase (se 5 (by rfl) ⟨235064, by rfl⟩ : syracuseStep 5014709 = 470129) (by norm_num)
theorem B1672373 : Blo 988596 1672373 := bbase (se 5 (by rfl) ⟨78392, by rfl⟩ : syracuseStep 1672373 = 156785) (by norm_num)
theorem B1115329 : Blo 988596 1115329 := bbase (se 2 (by rfl) ⟨418248, by rfl⟩ : syracuseStep 1115329 = 836497) (by norm_num)
theorem B2229461 : Blo 988596 2229461 := bbase (se 7 (by rfl) ⟨26126, by rfl⟩ : syracuseStep 2229461 = 52253) (by norm_num)
theorem B1115365 : Blo 988596 1115365 := bbase (se 4 (by rfl) ⟨104565, by rfl⟩ : syracuseStep 1115365 = 209131) (by norm_num)
theorem B1115401 : Blo 988596 1115401 := bbase (se 2 (by rfl) ⟨418275, by rfl⟩ : syracuseStep 1115401 = 836551) (by norm_num)
theorem B2229533 : Blo 988596 2229533 := bbase (se 3 (by rfl) ⟨418037, by rfl⟩ : syracuseStep 2229533 = 836075) (by norm_num)
theorem B1115437 : Blo 988596 1115437 := bbase (se 3 (by rfl) ⟨209144, by rfl⟩ : syracuseStep 1115437 = 418289) (by norm_num)
theorem B1672501 : Blo 988596 1672501 := bbase (se 5 (by rfl) ⟨78398, by rfl⟩ : syracuseStep 1672501 = 156797) (by norm_num)
theorem B1115473 : Blo 988596 1115473 := bbase (se 2 (by rfl) ⟨418302, by rfl⟩ : syracuseStep 1115473 = 836605) (by norm_num)
theorem B2229605 : Blo 988596 2229605 := bbase (se 4 (by rfl) ⟨209025, by rfl⟩ : syracuseStep 2229605 = 418051) (by norm_num)
theorem B3343733 : Blo 988596 3343733 := bbase (se 5 (by rfl) ⟨156737, by rfl⟩ : syracuseStep 3343733 = 313475) (by norm_num)
theorem B1115509 : Blo 988596 1115509 := bbase (se 5 (by rfl) ⟨52289, by rfl⟩ : syracuseStep 1115509 = 104579) (by norm_num)
theorem B1672589 : Blo 988596 1672589 := bbase (se 3 (by rfl) ⟨313610, by rfl⟩ : syracuseStep 1672589 = 627221) (by norm_num)
theorem B1115545 : Blo 988596 1115545 := bbase (se 2 (by rfl) ⟨418329, by rfl⟩ : syracuseStep 1115545 = 836659) (by norm_num)
theorem B2229677 : Blo 988596 2229677 := bbase (se 3 (by rfl) ⟨418064, by rfl⟩ : syracuseStep 2229677 = 836129) (by norm_num)
theorem B1115581 : Blo 988596 1115581 := bbase (se 3 (by rfl) ⟨209171, by rfl⟩ : syracuseStep 1115581 = 418343) (by norm_num)
theorem B1115617 : Blo 988596 1115617 := bbase (se 2 (by rfl) ⟨418356, by rfl⟩ : syracuseStep 1115617 = 836713) (by norm_num)
theorem B2229749 : Blo 988596 2229749 := bbase (se 5 (by rfl) ⟨104519, by rfl⟩ : syracuseStep 2229749 = 209039) (by norm_num)
theorem B1115653 : Blo 988596 1115653 := bbase (se 4 (by rfl) ⟨104592, by rfl⟩ : syracuseStep 1115653 = 209185) (by norm_num)
theorem B1672717 : Blo 988596 1672717 := bbase (se 3 (by rfl) ⟨313634, by rfl⟩ : syracuseStep 1672717 = 627269) (by norm_num)
theorem B1410581 : Blo 988596 1410581 := bbase (se 6 (by rfl) ⟨33060, by rfl⟩ : syracuseStep 1410581 = 66121) (by norm_num)
theorem B1115689 : Blo 988596 1115689 := bbase (se 2 (by rfl) ⟨418383, by rfl⟩ : syracuseStep 1115689 = 836767) (by norm_num)
theorem B2229821 : Blo 988596 2229821 := bbase (se 3 (by rfl) ⟨418091, by rfl⟩ : syracuseStep 2229821 = 836183) (by norm_num)
theorem B1115725 : Blo 988596 1115725 := bbase (se 3 (by rfl) ⟨209198, by rfl⟩ : syracuseStep 1115725 = 418397) (by norm_num)
theorem B1672805 : Blo 988596 1672805 := bbase (se 4 (by rfl) ⟨156825, by rfl⟩ : syracuseStep 1672805 = 313651) (by norm_num)
theorem B1115761 : Blo 988596 1115761 := bbase (se 2 (by rfl) ⟨418410, by rfl⟩ : syracuseStep 1115761 = 836821) (by norm_num)
theorem B2229893 : Blo 988596 2229893 := bbase (se 4 (by rfl) ⟨209052, by rfl⟩ : syracuseStep 2229893 = 418105) (by norm_num)
theorem B1115797 : Blo 988596 1115797 := bbase (se 6 (by rfl) ⟨26151, by rfl⟩ : syracuseStep 1115797 = 52303) (by norm_num)
theorem B1115833 : Blo 988596 1115833 := bbase (se 2 (by rfl) ⟨418437, by rfl⟩ : syracuseStep 1115833 = 836875) (by norm_num)
theorem B2229965 : Blo 988596 2229965 := bbase (se 3 (by rfl) ⟨418118, by rfl⟩ : syracuseStep 2229965 = 836237) (by norm_num)
theorem B1115869 : Blo 988596 1115869 := bbase (se 3 (by rfl) ⟨209225, by rfl⟩ : syracuseStep 1115869 = 418451) (by norm_num)
theorem B1672933 : Blo 988596 1672933 := bbase (se 4 (by rfl) ⟨156837, by rfl⟩ : syracuseStep 1672933 = 313675) (by norm_num)
theorem B1115905 : Blo 988596 1115905 := bbase (se 2 (by rfl) ⟨418464, by rfl⟩ : syracuseStep 1115905 = 836929) (by norm_num)
theorem B2230037 : Blo 988596 2230037 := bbase (se 6 (by rfl) ⟨52266, by rfl⟩ : syracuseStep 2230037 = 104533) (by norm_num)
theorem B3344165 : Blo 988596 3344165 := bbase (se 4 (by rfl) ⟨313515, by rfl⟩ : syracuseStep 3344165 = 627031) (by norm_num)
theorem B1115941 : Blo 988596 1115941 := bbase (se 4 (by rfl) ⟨104619, by rfl⟩ : syracuseStep 1115941 = 209239) (by norm_num)
theorem B1673021 : Blo 988596 1673021 := bbase (se 3 (by rfl) ⟨313691, by rfl⟩ : syracuseStep 1673021 = 627383) (by norm_num)
theorem B2819909 : Blo 988596 2819909 := bbase (se 4 (by rfl) ⟨264366, by rfl⟩ : syracuseStep 2819909 = 528733) (by norm_num)
theorem B1115977 : Blo 988596 1115977 := bbase (se 2 (by rfl) ⟨418491, by rfl⟩ : syracuseStep 1115977 = 836983) (by norm_num)
theorem B2230109 : Blo 988596 2230109 := bbase (se 3 (by rfl) ⟨418145, by rfl⟩ : syracuseStep 2230109 = 836291) (by norm_num)
theorem B1116013 : Blo 988596 1116013 := bbase (se 3 (by rfl) ⟨209252, by rfl⟩ : syracuseStep 1116013 = 418505) (by norm_num)
theorem B1116049 : Blo 988596 1116049 := bbase (se 2 (by rfl) ⟨418518, by rfl⟩ : syracuseStep 1116049 = 837037) (by norm_num)
theorem B2230181 : Blo 988596 2230181 := bbase (se 4 (by rfl) ⟨209079, by rfl⟩ : syracuseStep 2230181 = 418159) (by norm_num)
theorem B1116085 : Blo 988596 1116085 := bbase (se 5 (by rfl) ⟨52316, by rfl⟩ : syracuseStep 1116085 = 104633) (by norm_num)
theorem B1673149 : Blo 988596 1673149 := bbase (se 3 (by rfl) ⟨313715, by rfl⟩ : syracuseStep 1673149 = 627431) (by norm_num)
theorem B1116121 : Blo 988596 1116121 := bbase (se 2 (by rfl) ⟨418545, by rfl⟩ : syracuseStep 1116121 = 837091) (by norm_num)
theorem B1114105 : Blo 988596 1114105 := bbase (se 2 (by rfl) ⟨417789, by rfl⟩ : syracuseStep 1114105 = 835579) (by norm_num)
theorem B2230253 : Blo 988596 2230253 := bbase (se 3 (by rfl) ⟨418172, by rfl⟩ : syracuseStep 2230253 = 836345) (by norm_num)
theorem B1116157 : Blo 988596 1116157 := bbase (se 3 (by rfl) ⟨209279, by rfl⟩ : syracuseStep 1116157 = 418559) (by norm_num)
theorem B1673237 : Blo 988596 1673237 := bbase (se 6 (by rfl) ⟨39216, by rfl⟩ : syracuseStep 1673237 = 78433) (by norm_num)
theorem B1116193 : Blo 988596 1116193 := bbase (se 2 (by rfl) ⟨418572, by rfl⟩ : syracuseStep 1116193 = 837145) (by norm_num)
theorem B2230325 : Blo 988596 2230325 := bbase (se 5 (by rfl) ⟨104546, by rfl⟩ : syracuseStep 2230325 = 209093) (by norm_num)
theorem B1116229 : Blo 988596 1116229 := bbase (se 4 (by rfl) ⟨104646, by rfl⟩ : syracuseStep 1116229 = 209293) (by norm_num)
theorem B1116265 : Blo 988596 1116265 := bbase (se 2 (by rfl) ⟨418599, by rfl⟩ : syracuseStep 1116265 = 837199) (by norm_num)
theorem B8456309 : Blo 988596 8456309 := bbase (se 5 (by rfl) ⟨396389, by rfl⟩ : syracuseStep 8456309 = 792779) (by norm_num)
theorem B2230397 : Blo 988596 2230397 := bbase (se 3 (by rfl) ⟨418199, by rfl⟩ : syracuseStep 2230397 = 836399) (by norm_num)
theorem B1116301 : Blo 988596 1116301 := bbase (se 3 (by rfl) ⟨209306, by rfl⟩ : syracuseStep 1116301 = 418613) (by norm_num)
theorem B1673365 : Blo 988596 1673365 := bbase (se 6 (by rfl) ⟨39219, by rfl⟩ : syracuseStep 1673365 = 78439) (by norm_num)
theorem B1116337 : Blo 988596 1116337 := bbase (se 2 (by rfl) ⟨418626, by rfl⟩ : syracuseStep 1116337 = 837253) (by norm_num)
theorem B2230469 : Blo 988596 2230469 := bbase (se 4 (by rfl) ⟨209106, by rfl⟩ : syracuseStep 2230469 = 418213) (by norm_num)
theorem B3344597 : Blo 988596 3344597 := bbase (se 7 (by rfl) ⟨39194, by rfl⟩ : syracuseStep 3344597 = 78389) (by norm_num)
theorem B1116373 : Blo 988596 1116373 := bbase (se 7 (by rfl) ⟨13082, by rfl⟩ : syracuseStep 1116373 = 26165) (by norm_num)
theorem B4950245 : Blo 988596 4950245 := bbase (se 4 (by rfl) ⟨464085, by rfl⟩ : syracuseStep 4950245 = 928171) (by norm_num)
theorem B1673453 : Blo 988596 1673453 := bbase (se 3 (by rfl) ⟨313772, by rfl⟩ : syracuseStep 1673453 = 627545) (by norm_num)
theorem B1116409 : Blo 988596 1116409 := bbase (se 2 (by rfl) ⟨418653, by rfl⟩ : syracuseStep 1116409 = 837307) (by norm_num)
theorem B2230541 : Blo 988596 2230541 := bbase (se 3 (by rfl) ⟨418226, by rfl⟩ : syracuseStep 2230541 = 836453) (by norm_num)
theorem B1116445 : Blo 988596 1116445 := bbase (se 3 (by rfl) ⟨209333, by rfl⟩ : syracuseStep 1116445 = 418667) (by norm_num)
theorem B1116481 : Blo 988596 1116481 := bbase (se 2 (by rfl) ⟨418680, by rfl⟩ : syracuseStep 1116481 = 837361) (by norm_num)
theorem B2230613 : Blo 988596 2230613 := bbase (se 10 (by rfl) ⟨3267, by rfl⟩ : syracuseStep 2230613 = 6535) (by norm_num)
theorem B1116517 : Blo 988596 1116517 := bbase (se 4 (by rfl) ⟨104673, by rfl⟩ : syracuseStep 1116517 = 209347) (by norm_num)
theorem B1673581 : Blo 988596 1673581 := bbase (se 3 (by rfl) ⟨313796, by rfl⟩ : syracuseStep 1673581 = 627593) (by norm_num)
theorem B1116553 : Blo 988596 1116553 := bbase (se 2 (by rfl) ⟨418707, by rfl⟩ : syracuseStep 1116553 = 837415) (by norm_num)
theorem B2230685 : Blo 988596 2230685 := bbase (se 3 (by rfl) ⟨418253, by rfl⟩ : syracuseStep 2230685 = 836507) (by norm_num)
theorem B1116589 : Blo 988596 1116589 := bbase (se 3 (by rfl) ⟨209360, by rfl⟩ : syracuseStep 1116589 = 418721) (by norm_num)
theorem B5016005 : Blo 988596 5016005 := bbase (se 4 (by rfl) ⟨470250, by rfl⟩ : syracuseStep 5016005 = 940501) (by norm_num)
theorem B1673669 : Blo 988596 1673669 := bbase (se 4 (by rfl) ⟨156906, by rfl⟩ : syracuseStep 1673669 = 313813) (by norm_num)
theorem B1116625 : Blo 988596 1116625 := bbase (se 2 (by rfl) ⟨418734, by rfl⟩ : syracuseStep 1116625 = 837469) (by norm_num)
theorem B2230757 : Blo 988596 2230757 := bbase (se 4 (by rfl) ⟨209133, by rfl⟩ : syracuseStep 2230757 = 418267) (by norm_num)
theorem B1116661 : Blo 988596 1116661 := bbase (se 5 (by rfl) ⟨52343, by rfl⟩ : syracuseStep 1116661 = 104687) (by norm_num)
theorem B2230829 : Blo 988596 2230829 := bbase (se 3 (by rfl) ⟨418280, by rfl⟩ : syracuseStep 2230829 = 836561) (by norm_num)
theorem B1673797 : Blo 988596 1673797 := bbase (se 4 (by rfl) ⟨156918, by rfl⟩ : syracuseStep 1673797 = 313837) (by norm_num)
theorem B2263621 : Blo 988596 2263621 := bbase (se 4 (by rfl) ⟨212214, by rfl⟩ : syracuseStep 2263621 = 424429) (by norm_num)
theorem B2230901 : Blo 988596 2230901 := bbase (se 5 (by rfl) ⟨104573, by rfl⟩ : syracuseStep 2230901 = 209147) (by norm_num)
theorem B3345029 : Blo 988596 3345029 := bbase (se 4 (by rfl) ⟨313596, by rfl⟩ : syracuseStep 3345029 = 627193) (by norm_num)
theorem B1673885 : Blo 988596 1673885 := bbase (se 3 (by rfl) ⟨313853, by rfl⟩ : syracuseStep 1673885 = 627707) (by norm_num)
theorem B2230973 : Blo 988596 2230973 := bbase (se 3 (by rfl) ⟨418307, by rfl⟩ : syracuseStep 2230973 = 836615) (by norm_num)
theorem B2231045 : Blo 988596 2231045 := bbase (se 4 (by rfl) ⟨209160, by rfl⟩ : syracuseStep 2231045 = 418321) (by norm_num)
theorem B12684053 : Blo 988596 12684053 := bbase (se 6 (by rfl) ⟨297282, by rfl⟩ : syracuseStep 12684053 = 594565) (by norm_num)
theorem B1674013 : Blo 988596 1674013 := bbase (se 3 (by rfl) ⟨313877, by rfl⟩ : syracuseStep 1674013 = 627755) (by norm_num)
theorem B2231117 : Blo 988596 2231117 := bbase (se 3 (by rfl) ⟨418334, by rfl⟩ : syracuseStep 2231117 = 836669) (by norm_num)
theorem B5638997 : Blo 988596 5638997 := bbase (se 9 (by rfl) ⟨16520, by rfl⟩ : syracuseStep 5638997 = 33041) (by norm_num)
theorem B1674101 : Blo 988596 1674101 := bbase (se 5 (by rfl) ⟨78473, by rfl⟩ : syracuseStep 1674101 = 156947) (by norm_num)
theorem B2231189 : Blo 988596 2231189 := bbase (se 6 (by rfl) ⟨52293, by rfl⟩ : syracuseStep 2231189 = 104587) (by norm_num)
theorem B4230053 : Blo 988596 4230053 := bbase (se 4 (by rfl) ⟨396567, by rfl⟩ : syracuseStep 4230053 = 793135) (by norm_num)
theorem B1412005 : Blo 988596 1412005 := bbase (se 4 (by rfl) ⟨132375, by rfl⟩ : syracuseStep 1412005 = 264751) (by norm_num)
theorem B2231261 : Blo 988596 2231261 := bbase (se 3 (by rfl) ⟨418361, by rfl⟩ : syracuseStep 2231261 = 836723) (by norm_num)
theorem B1674229 : Blo 988596 1674229 := bbase (se 5 (by rfl) ⟨78479, by rfl⟩ : syracuseStep 1674229 = 156959) (by norm_num)
theorem B2231333 : Blo 988596 2231333 := bbase (se 4 (by rfl) ⟨209187, by rfl⟩ : syracuseStep 2231333 = 418375) (by norm_num)
theorem B3345461 : Blo 988596 3345461 := bbase (se 5 (by rfl) ⟨156818, by rfl⟩ : syracuseStep 3345461 = 313637) (by norm_num)
theorem B1674317 : Blo 988596 1674317 := bbase (se 3 (by rfl) ⟨313934, by rfl⟩ : syracuseStep 1674317 = 627869) (by norm_num)
theorem B2231405 : Blo 988596 2231405 := bbase (se 3 (by rfl) ⟨418388, by rfl⟩ : syracuseStep 2231405 = 836777) (by norm_num)
theorem B2231477 : Blo 988596 2231477 := bbase (se 5 (by rfl) ⟨104600, by rfl⟩ : syracuseStep 2231477 = 209201) (by norm_num)
theorem B4525237 : Blo 988596 4525237 := bbase (se 5 (by rfl) ⟨212120, by rfl⟩ : syracuseStep 4525237 = 424241) (by norm_num)
theorem B1674445 : Blo 988596 1674445 := bbase (se 3 (by rfl) ⟨313958, by rfl⟩ : syracuseStep 1674445 = 627917) (by norm_num)
theorem B12717269 : Blo 988596 12717269 := bbase (se 7 (by rfl) ⟨149030, by rfl⟩ : syracuseStep 12717269 = 298061) (by norm_num)
theorem B2231549 : Blo 988596 2231549 := bbase (se 3 (by rfl) ⟨418415, by rfl⟩ : syracuseStep 2231549 = 836831) (by norm_num)
theorem B1674533 : Blo 988596 1674533 := bbase (se 4 (by rfl) ⟨156987, by rfl⟩ : syracuseStep 1674533 = 313975) (by norm_num)
theorem B2231621 : Blo 988596 2231621 := bbase (se 4 (by rfl) ⟨209214, by rfl⟩ : syracuseStep 2231621 = 418429) (by norm_num)
theorem B2821493 : Blo 988596 2821493 := bbase (se 5 (by rfl) ⟨132257, by rfl⟩ : syracuseStep 2821493 = 264515) (by norm_num)
theorem B2231693 : Blo 988596 2231693 := bbase (se 3 (by rfl) ⟨418442, by rfl⟩ : syracuseStep 2231693 = 836885) (by norm_num)
theorem B1674661 : Blo 988596 1674661 := bbase (se 4 (by rfl) ⟨156999, by rfl⟩ : syracuseStep 1674661 = 313999) (by norm_num)
theorem B2231765 : Blo 988596 2231765 := bbase (se 7 (by rfl) ⟨26153, by rfl⟩ : syracuseStep 2231765 = 52307) (by norm_num)
theorem B3345893 : Blo 988596 3345893 := bbase (se 4 (by rfl) ⟨313677, by rfl⟩ : syracuseStep 3345893 = 627355) (by norm_num)
theorem B1412597 : Blo 988596 1412597 := bbase (se 5 (by rfl) ⟨66215, by rfl⟩ : syracuseStep 1412597 = 132431) (by norm_num)
theorem B1674749 : Blo 988596 1674749 := bbase (se 3 (by rfl) ⟨314015, by rfl⟩ : syracuseStep 1674749 = 628031) (by norm_num)
theorem B2231837 : Blo 988596 2231837 := bbase (se 3 (by rfl) ⟨418469, by rfl⟩ : syracuseStep 2231837 = 836939) (by norm_num)
theorem B1412677 : Blo 988596 1412677 := bbase (se 4 (by rfl) ⟨132438, by rfl⟩ : syracuseStep 1412677 = 264877) (by norm_num)
theorem B2231909 : Blo 988596 2231909 := bbase (se 4 (by rfl) ⟨209241, by rfl⟩ : syracuseStep 2231909 = 418483) (by norm_num)
theorem B1674877 : Blo 988596 1674877 := bbase (se 3 (by rfl) ⟨314039, by rfl⟩ : syracuseStep 1674877 = 628079) (by norm_num)
theorem B1805981 : Blo 988596 1805981 := bbase (se 3 (by rfl) ⟨338621, by rfl⟩ : syracuseStep 1805981 = 677243) (by norm_num)
theorem B2231981 : Blo 988596 2231981 := bbase (se 3 (by rfl) ⟨418496, by rfl⟩ : syracuseStep 2231981 = 836993) (by norm_num)
theorem B1412797 : Blo 988596 1412797 := bbase (se 3 (by rfl) ⟨264899, by rfl⟩ : syracuseStep 1412797 = 529799) (by norm_num)
theorem B5017301 : Blo 988596 5017301 := bbase (se 7 (by rfl) ⟨58796, by rfl⟩ : syracuseStep 5017301 = 117593) (by norm_num)
theorem B1674965 : Blo 988596 1674965 := bbase (se 7 (by rfl) ⟨19628, by rfl⟩ : syracuseStep 1674965 = 39257) (by norm_num)
theorem B2232053 : Blo 988596 2232053 := bbase (se 5 (by rfl) ⟨104627, by rfl⟩ : syracuseStep 2232053 = 209255) (by norm_num)
theorem B1412893 : Blo 988596 1412893 := bbase (se 3 (by rfl) ⟨264917, by rfl⟩ : syracuseStep 1412893 = 529835) (by norm_num)
theorem B2232125 : Blo 988596 2232125 := bbase (se 3 (by rfl) ⟨418523, by rfl⟩ : syracuseStep 2232125 = 837047) (by norm_num)
theorem B2232197 : Blo 988596 2232197 := bbase (se 4 (by rfl) ⟨209268, by rfl⟩ : syracuseStep 2232197 = 418537) (by norm_num)
theorem B1806221 : Blo 988596 1806221 := bbase (se 3 (by rfl) ⟨338666, by rfl⟩ : syracuseStep 1806221 = 677333) (by norm_num)
theorem B4231061 : Blo 988596 4231061 := bbase (se 6 (by rfl) ⟨99165, by rfl⟩ : syracuseStep 4231061 = 198331) (by norm_num)
theorem B10719125 : Blo 988596 10719125 := bbase (se 6 (by rfl) ⟨251229, by rfl⟩ : syracuseStep 10719125 = 502459) (by norm_num)
theorem B3346325 : Blo 988596 3346325 := bbase (se 6 (by rfl) ⟨78429, by rfl⟩ : syracuseStep 3346325 = 156859) (by norm_num)
theorem B2232269 : Blo 988596 2232269 := bbase (se 3 (by rfl) ⟨418550, by rfl⟩ : syracuseStep 2232269 = 837101) (by norm_num)
theorem B2822165 : Blo 988596 2822165 := bbase (se 6 (by rfl) ⟨66144, by rfl⟩ : syracuseStep 2822165 = 132289) (by norm_num)
theorem B2232341 : Blo 988596 2232341 := bbase (se 6 (by rfl) ⟨52320, by rfl⟩ : syracuseStep 2232341 = 104641) (by norm_num)
theorem B2232413 : Blo 988596 2232413 := bbase (se 3 (by rfl) ⟨418577, by rfl⟩ : syracuseStep 2232413 = 837155) (by norm_num)
theorem B2232485 : Blo 988596 2232485 := bbase (se 4 (by rfl) ⟨209295, by rfl⟩ : syracuseStep 2232485 = 418591) (by norm_num)
theorem B2232557 : Blo 988596 2232557 := bbase (se 3 (by rfl) ⟨418604, by rfl⟩ : syracuseStep 2232557 = 837209) (by norm_num)
theorem B7508213 : Blo 988596 7508213 := bbase (se 5 (by rfl) ⟨351947, by rfl⟩ : syracuseStep 7508213 = 703895) (by norm_num)
theorem B2232629 : Blo 988596 2232629 := bbase (se 5 (by rfl) ⟨104654, by rfl⟩ : syracuseStep 2232629 = 209309) (by norm_num)
theorem B3346757 : Blo 988596 3346757 := bbase (se 4 (by rfl) ⟨313758, by rfl⟩ : syracuseStep 3346757 = 627517) (by norm_num)
theorem B4755829 : Blo 988596 4755829 := bbase (se 5 (by rfl) ⟨222929, by rfl⟩ : syracuseStep 4755829 = 445859) (by norm_num)
theorem B2232701 : Blo 988596 2232701 := bbase (se 3 (by rfl) ⟨418631, by rfl⟩ : syracuseStep 2232701 = 837263) (by norm_num)
theorem B2822597 : Blo 988596 2822597 := bbase (se 4 (by rfl) ⟨264618, by rfl⟩ : syracuseStep 2822597 = 529237) (by norm_num)
theorem B2232773 : Blo 988596 2232773 := bbase (se 4 (by rfl) ⟨209322, by rfl⟩ : syracuseStep 2232773 = 418645) (by norm_num)
theorem B2232845 : Blo 988596 2232845 := bbase (se 3 (by rfl) ⟨418658, by rfl⟩ : syracuseStep 2232845 = 837317) (by norm_num)
theorem B14291477 : Blo 988596 14291477 := bbase (se 6 (by rfl) ⟨334956, by rfl⟩ : syracuseStep 14291477 = 669913) (by norm_num)
theorem B2232917 : Blo 988596 2232917 := bbase (se 8 (by rfl) ⟨13083, by rfl⟩ : syracuseStep 2232917 = 26167) (by norm_num)
theorem B2232989 : Blo 988596 2232989 := bbase (se 3 (by rfl) ⟨418685, by rfl⟩ : syracuseStep 2232989 = 837371) (by norm_num)
theorem B2233061 : Blo 988596 2233061 := bbase (se 4 (by rfl) ⟨209349, by rfl⟩ : syracuseStep 2233061 = 418699) (by norm_num)
theorem B3347189 : Blo 988596 3347189 := bbase (se 5 (by rfl) ⟨156899, by rfl⟩ : syracuseStep 3347189 = 313799) (by norm_num)
theorem B2233133 : Blo 988596 2233133 := bbase (se 3 (by rfl) ⟨418712, by rfl⟩ : syracuseStep 2233133 = 837425) (by norm_num)
theorem B2233205 : Blo 988596 2233205 := bbase (se 5 (by rfl) ⟨104681, by rfl⟩ : syracuseStep 2233205 = 209363) (by norm_num)
theorem B2233277 : Blo 988596 2233277 := bbase (se 3 (by rfl) ⟨418739, by rfl⟩ : syracuseStep 2233277 = 837479) (by norm_num)
theorem B5018597 : Blo 988596 5018597 := bbase (se 4 (by rfl) ⟨470493, by rfl⟩ : syracuseStep 5018597 = 940987) (by norm_num)
theorem B3347621 : Blo 988596 3347621 := bbase (se 4 (by rfl) ⟨313839, by rfl⟩ : syracuseStep 3347621 = 627679) (by norm_num)
theorem B2823349 : Blo 988596 2823349 := bbase (se 5 (by rfl) ⟨132344, by rfl⟩ : syracuseStep 2823349 = 264689) (by norm_num)
theorem B1611037 : Blo 988596 1611037 := bbase (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) (by norm_num)
theorem B5346805 : Blo 988596 5346805 := bbase (se 5 (by rfl) ⟨250631, by rfl⟩ : syracuseStep 5346805 = 501263) (by norm_num)
theorem B3348053 : Blo 988596 3348053 := bbase (se 8 (by rfl) ⟨19617, by rfl⟩ : syracuseStep 3348053 = 39235) (by norm_num)
theorem B4232837 : Blo 988596 4232837 := bbase (se 4 (by rfl) ⟨396828, by rfl⟩ : syracuseStep 4232837 = 793657) (by norm_num)
theorem B1251217 : Blo 988596 1251217 := bbase (se 2 (by rfl) ⟨469206, by rfl⟩ : syracuseStep 1251217 = 938413) (by norm_num)
theorem B9050069 : Blo 988596 9050069 := bbase (se 7 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 9050069 = 212111) (by norm_num)
theorem B6789109 : Blo 988596 6789109 := bbase (se 5 (by rfl) ⟨318239, by rfl⟩ : syracuseStep 6789109 = 636479) (by norm_num)
theorem B3348485 : Blo 988596 3348485 := bbase (se 4 (by rfl) ⟨313920, by rfl⟩ : syracuseStep 3348485 = 627841) (by norm_num)
theorem B1251389 : Blo 988596 1251389 := bbase (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) (by norm_num)
theorem B2005069 : Blo 988596 2005069 := bbase (se 3 (by rfl) ⟨375950, by rfl⟩ : syracuseStep 2005069 = 751901) (by norm_num)
theorem B1251445 : Blo 988596 1251445 := bbase (se 5 (by rfl) ⟨58661, by rfl⟩ : syracuseStep 1251445 = 117323) (by norm_num)
theorem B17832149 : Blo 988596 17832149 := bbase (se 7 (by rfl) ⟨208970, by rfl⟩ : syracuseStep 17832149 = 417941) (by norm_num)
theorem B1251541 : Blo 988596 1251541 := bbase (se 7 (by rfl) ⟨14666, by rfl⟩ : syracuseStep 1251541 = 29333) (by norm_num)
theorem B5019893 : Blo 988596 5019893 := bbase (se 5 (by rfl) ⟨235307, by rfl⟩ : syracuseStep 5019893 = 470615) (by norm_num)
theorem B2857253 : Blo 988596 2857253 := bbase (se 4 (by rfl) ⟨267867, by rfl⟩ : syracuseStep 2857253 = 535735) (by norm_num)
theorem B1251713 : Blo 988596 1251713 := bbase (se 2 (by rfl) ⟨469392, by rfl⟩ : syracuseStep 1251713 = 938785) (by norm_num)
theorem B3348917 : Blo 988596 3348917 := bbase (se 5 (by rfl) ⟨156980, by rfl⟩ : syracuseStep 3348917 = 313961) (by norm_num)
theorem B1251769 : Blo 988596 1251769 := bbase (se 2 (by rfl) ⟨469413, by rfl⟩ : syracuseStep 1251769 = 938827) (by norm_num)
theorem B3807701 : Blo 988596 3807701 := bbase (se 7 (by rfl) ⟨44621, by rfl⟩ : syracuseStep 3807701 = 89243) (by norm_num)
theorem B1251865 : Blo 988596 1251865 := bbase (se 2 (by rfl) ⟨469449, by rfl⟩ : syracuseStep 1251865 = 938899) (by norm_num)
theorem B1252037 : Blo 988596 1252037 := bbase (se 4 (by rfl) ⟨117378, by rfl⟩ : syracuseStep 1252037 = 234757) (by norm_num)
theorem B1252093 : Blo 988596 1252093 := bbase (se 3 (by rfl) ⟨234767, by rfl⟩ : syracuseStep 1252093 = 469535) (by norm_num)
theorem B1252189 : Blo 988596 1252189 := bbase (se 3 (by rfl) ⟨234785, by rfl⟩ : syracuseStep 1252189 = 469571) (by norm_num)
theorem B3349349 : Blo 988596 3349349 := bbase (se 4 (by rfl) ⟨314001, by rfl⟩ : syracuseStep 3349349 = 628003) (by norm_num)
theorem B3218357 : Blo 988596 3218357 := bbase (se 5 (by rfl) ⟨150860, by rfl⟩ : syracuseStep 3218357 = 301721) (by norm_num)
theorem B1907645 : Blo 988596 1907645 := bbase (se 3 (by rfl) ⟨357683, by rfl⟩ : syracuseStep 1907645 = 715367) (by norm_num)
theorem B1055749 : Blo 988596 1055749 := bbase (se 4 (by rfl) ⟨98976, by rfl⟩ : syracuseStep 1055749 = 197953) (by norm_num)
theorem B1252361 : Blo 988596 1252361 := bbase (se 2 (by rfl) ⟨469635, by rfl⟩ : syracuseStep 1252361 = 939271) (by norm_num)
theorem B1252417 : Blo 988596 1252417 := bbase (se 2 (by rfl) ⟨469656, by rfl⟩ : syracuseStep 1252417 = 939313) (by norm_num)
theorem B1055873 : Blo 988596 1055873 := bbase (se 2 (by rfl) ⟨395952, by rfl⟩ : syracuseStep 1055873 = 791905) (by norm_num)
theorem B1252513 : Blo 988596 1252513 := bbase (se 2 (by rfl) ⟨469692, by rfl⟩ : syracuseStep 1252513 = 939385) (by norm_num)
theorem B1088749 : Blo 988596 1088749 := bbase (se 3 (by rfl) ⟨204140, by rfl⟩ : syracuseStep 1088749 = 408281) (by norm_num)
theorem B3349781 : Blo 988596 3349781 := bbase (se 6 (by rfl) ⟨78510, by rfl⟩ : syracuseStep 3349781 = 157021) (by norm_num)
theorem B1252685 : Blo 988596 1252685 := bbase (se 3 (by rfl) ⟨234878, by rfl⟩ : syracuseStep 1252685 = 469757) (by norm_num)
theorem B1056125 : Blo 988596 1056125 := bbase (se 3 (by rfl) ⟨198023, by rfl⟩ : syracuseStep 1056125 = 396047) (by norm_num)
theorem B1252741 : Blo 988596 1252741 := bbase (se 4 (by rfl) ⟨117444, by rfl⟩ : syracuseStep 1252741 = 234889) (by norm_num)
theorem B1252837 : Blo 988596 1252837 := bbase (se 4 (by rfl) ⟨117453, by rfl⟩ : syracuseStep 1252837 = 234907) (by norm_num)
theorem B5021189 : Blo 988596 5021189 := bbase (se 4 (by rfl) ⟨470736, by rfl⟩ : syracuseStep 5021189 = 941473) (by norm_num)
theorem B1253009 : Blo 988596 1253009 := bbase (se 2 (by rfl) ⟨469878, by rfl⟩ : syracuseStep 1253009 = 939757) (by norm_num)
theorem B1253065 : Blo 988596 1253065 := bbase (se 2 (by rfl) ⟨469899, by rfl⟩ : syracuseStep 1253065 = 939799) (by norm_num)
theorem B1253161 : Blo 988596 1253161 := bbase (se 2 (by rfl) ⟨469935, by rfl⟩ : syracuseStep 1253161 = 939871) (by norm_num)
theorem B1056569 : Blo 988596 1056569 := bbase (se 2 (by rfl) ⟨396213, by rfl⟩ : syracuseStep 1056569 = 792427) (by norm_num)
theorem B2006885 : Blo 988596 2006885 := bbase (se 4 (by rfl) ⟨188145, by rfl⟩ : syracuseStep 2006885 = 376291) (by norm_num)
theorem B1187785 : Blo 988596 1187785 := bbase (se 2 (by rfl) ⟨445419, by rfl⟩ : syracuseStep 1187785 = 890839) (by norm_num)
theorem B1253333 : Blo 988596 1253333 := bbase (se 7 (by rfl) ⟨14687, by rfl⟩ : syracuseStep 1253333 = 29375) (by norm_num)
theorem B2826197 : Blo 988596 2826197 := bbase (se 7 (by rfl) ⟨33119, by rfl⟩ : syracuseStep 2826197 = 66239) (by norm_num)
theorem B1253389 : Blo 988596 1253389 := bbase (se 3 (by rfl) ⟨235010, by rfl⟩ : syracuseStep 1253389 = 470021) (by norm_num)
theorem B1056817 : Blo 988596 1056817 := bbase (se 2 (by rfl) ⟨396306, by rfl⟩ : syracuseStep 1056817 = 792613) (by norm_num)
theorem B1253485 : Blo 988596 1253485 := bbase (se 3 (by rfl) ⟨235028, by rfl⟩ : syracuseStep 1253485 = 470057) (by norm_num)
theorem B1187977 : Blo 988596 1187977 := bbase (se 2 (by rfl) ⟨445491, by rfl⟩ : syracuseStep 1187977 = 890983) (by norm_num)
theorem B1482917 : Blo 988596 1482917 := bbase (se 4 (by rfl) ⟨139023, by rfl⟩ : syracuseStep 1482917 = 278047) (by norm_num)
theorem B1482941 : Blo 988596 1482941 := bbase (se 3 (by rfl) ⟨278051, by rfl⟩ : syracuseStep 1482941 = 556103) (by norm_num)
theorem B1482965 : Blo 988596 1482965 := bbase (se 7 (by rfl) ⟨17378, by rfl⟩ : syracuseStep 1482965 = 34757) (by norm_num)
theorem B1482989 : Blo 988596 1482989 := bbase (se 3 (by rfl) ⟨278060, by rfl⟩ : syracuseStep 1482989 = 556121) (by norm_num)
theorem B1483013 : Blo 988596 1483013 := bbase (se 4 (by rfl) ⟨139032, by rfl⟩ : syracuseStep 1483013 = 278065) (by norm_num)
theorem B4759829 : Blo 988596 4759829 := bbase (se 6 (by rfl) ⟨111558, by rfl⟩ : syracuseStep 4759829 = 223117) (by norm_num)
theorem B1253657 : Blo 988596 1253657 := bbase (se 2 (by rfl) ⟨470121, by rfl⟩ : syracuseStep 1253657 = 940243) (by norm_num)
theorem B1483037 : Blo 988596 1483037 := bbase (se 3 (by rfl) ⟨278069, by rfl⟩ : syracuseStep 1483037 = 556139) (by norm_num)
theorem B1483061 : Blo 988596 1483061 := bbase (se 5 (by rfl) ⟨69518, by rfl⟩ : syracuseStep 1483061 = 139037) (by norm_num)
theorem B1483085 : Blo 988596 1483085 := bbase (se 3 (by rfl) ⟨278078, by rfl⟩ : syracuseStep 1483085 = 556157) (by norm_num)
theorem B1253713 : Blo 988596 1253713 := bbase (se 2 (by rfl) ⟨470142, by rfl⟩ : syracuseStep 1253713 = 940285) (by norm_num)
theorem B1483109 : Blo 988596 1483109 := bbase (se 4 (by rfl) ⟨139041, by rfl⟩ : syracuseStep 1483109 = 278083) (by norm_num)
theorem B1483133 : Blo 988596 1483133 := bbase (se 3 (by rfl) ⟨278087, by rfl⟩ : syracuseStep 1483133 = 556175) (by norm_num)
theorem B1483157 : Blo 988596 1483157 := bbase (se 6 (by rfl) ⟨34761, by rfl⟩ : syracuseStep 1483157 = 69523) (by norm_num)
theorem B1483181 : Blo 988596 1483181 := bbase (se 3 (by rfl) ⟨278096, by rfl⟩ : syracuseStep 1483181 = 556193) (by norm_num)
theorem B1253809 : Blo 988596 1253809 := bbase (se 2 (by rfl) ⟨470178, by rfl⟩ : syracuseStep 1253809 = 940357) (by norm_num)
theorem B1483205 : Blo 988596 1483205 := bbase (se 4 (by rfl) ⟨139050, by rfl⟩ : syracuseStep 1483205 = 278101) (by norm_num)
theorem B1483229 : Blo 988596 1483229 := bbase (se 3 (by rfl) ⟨278105, by rfl⟩ : syracuseStep 1483229 = 556211) (by norm_num)
theorem B1057261 : Blo 988596 1057261 := bbase (se 3 (by rfl) ⟨198236, by rfl⟩ : syracuseStep 1057261 = 396473) (by norm_num)
theorem B1483253 : Blo 988596 1483253 := bbase (se 5 (by rfl) ⟨69527, by rfl⟩ : syracuseStep 1483253 = 139055) (by norm_num)
theorem B1483277 : Blo 988596 1483277 := bbase (se 3 (by rfl) ⟨278114, by rfl⟩ : syracuseStep 1483277 = 556229) (by norm_num)
theorem B1483301 : Blo 988596 1483301 := bbase (se 4 (by rfl) ⟨139059, by rfl⟩ : syracuseStep 1483301 = 278119) (by norm_num)
theorem B1057321 : Blo 988596 1057321 := bbase (se 2 (by rfl) ⟨396495, by rfl⟩ : syracuseStep 1057321 = 792991) (by norm_num)
theorem B1483325 : Blo 988596 1483325 := bbase (se 3 (by rfl) ⟨278123, by rfl⟩ : syracuseStep 1483325 = 556247) (by norm_num)
theorem B1483349 : Blo 988596 1483349 := bbase (se 8 (by rfl) ⟨8691, by rfl⟩ : syracuseStep 1483349 = 17383) (by norm_num)
theorem B1253981 : Blo 988596 1253981 := bbase (se 3 (by rfl) ⟨235121, by rfl⟩ : syracuseStep 1253981 = 470243) (by norm_num)
theorem B1483373 : Blo 988596 1483373 := bbase (se 3 (by rfl) ⟨278132, by rfl⟩ : syracuseStep 1483373 = 556265) (by norm_num)
theorem B1483397 : Blo 988596 1483397 := bbase (se 4 (by rfl) ⟨139068, by rfl⟩ : syracuseStep 1483397 = 278137) (by norm_num)
theorem B1254037 : Blo 988596 1254037 := bbase (se 6 (by rfl) ⟨29391, by rfl⟩ : syracuseStep 1254037 = 58783) (by norm_num)
theorem B1483421 : Blo 988596 1483421 := bbase (se 3 (by rfl) ⟨278141, by rfl⟩ : syracuseStep 1483421 = 556283) (by norm_num)
theorem B1483445 : Blo 988596 1483445 := bbase (se 5 (by rfl) ⟨69536, by rfl⟩ : syracuseStep 1483445 = 139073) (by norm_num)
theorem B1483469 : Blo 988596 1483469 := bbase (se 3 (by rfl) ⟨278150, by rfl⟩ : syracuseStep 1483469 = 556301) (by norm_num)
theorem B25338581 : Blo 988596 25338581 := bbase (se 7 (by rfl) ⟨296936, by rfl⟩ : syracuseStep 25338581 = 593873) (by norm_num)
theorem B1483493 : Blo 988596 1483493 := bbase (se 4 (by rfl) ⟨139077, by rfl⟩ : syracuseStep 1483493 = 278155) (by norm_num)
theorem B1254133 : Blo 988596 1254133 := bbase (se 5 (by rfl) ⟨58787, by rfl⟩ : syracuseStep 1254133 = 117575) (by norm_num)
theorem B1483517 : Blo 988596 1483517 := bbase (se 3 (by rfl) ⟨278159, by rfl⟩ : syracuseStep 1483517 = 556319) (by norm_num)
theorem B1483541 : Blo 988596 1483541 := bbase (se 6 (by rfl) ⟨34770, by rfl⟩ : syracuseStep 1483541 = 69541) (by norm_num)
theorem B5022485 : Blo 988596 5022485 := bbase (se 6 (by rfl) ⟨117714, by rfl⟩ : syracuseStep 5022485 = 235429) (by norm_num)
theorem B1483565 : Blo 988596 1483565 := bbase (se 3 (by rfl) ⟨278168, by rfl⟩ : syracuseStep 1483565 = 556337) (by norm_num)
theorem B1483589 : Blo 988596 1483589 := bbase (se 4 (by rfl) ⟨139086, by rfl⟩ : syracuseStep 1483589 = 278173) (by norm_num)
theorem B1483613 : Blo 988596 1483613 := bbase (se 3 (by rfl) ⟨278177, by rfl⟩ : syracuseStep 1483613 = 556355) (by norm_num)
theorem B1057637 : Blo 988596 1057637 := bbase (se 4 (by rfl) ⟨99153, by rfl⟩ : syracuseStep 1057637 = 198307) (by norm_num)
theorem B1483637 : Blo 988596 1483637 := bbase (se 5 (by rfl) ⟨69545, by rfl⟩ : syracuseStep 1483637 = 139091) (by norm_num)
theorem B1483661 : Blo 988596 1483661 := bbase (se 3 (by rfl) ⟨278186, by rfl⟩ : syracuseStep 1483661 = 556373) (by norm_num)
theorem B2007949 : Blo 988596 2007949 := bbase (se 3 (by rfl) ⟨376490, by rfl⟩ : syracuseStep 2007949 = 752981) (by norm_num)
theorem B1254305 : Blo 988596 1254305 := bbase (se 2 (by rfl) ⟨470364, by rfl⟩ : syracuseStep 1254305 = 940729) (by norm_num)
theorem B1483685 : Blo 988596 1483685 := bbase (se 4 (by rfl) ⟨139095, by rfl⟩ : syracuseStep 1483685 = 278191) (by norm_num)
theorem B1876925 : Blo 988596 1876925 := bbase (se 3 (by rfl) ⟨351923, by rfl⟩ : syracuseStep 1876925 = 703847) (by norm_num)
theorem B1483709 : Blo 988596 1483709 := bbase (se 3 (by rfl) ⟨278195, by rfl⟩ : syracuseStep 1483709 = 556391) (by norm_num)
theorem B1483733 : Blo 988596 1483733 := bbase (se 7 (by rfl) ⟨17387, by rfl⟩ : syracuseStep 1483733 = 34775) (by norm_num)
theorem B1254361 : Blo 988596 1254361 := bbase (se 2 (by rfl) ⟨470385, by rfl⟩ : syracuseStep 1254361 = 940771) (by norm_num)
theorem B1483757 : Blo 988596 1483757 := bbase (se 3 (by rfl) ⟨278204, by rfl⟩ : syracuseStep 1483757 = 556409) (by norm_num)
theorem B1188857 : Blo 988596 1188857 := bbase (se 2 (by rfl) ⟨445821, by rfl⟩ : syracuseStep 1188857 = 891643) (by norm_num)
theorem B1483781 : Blo 988596 1483781 := bbase (se 4 (by rfl) ⟨139104, by rfl⟩ : syracuseStep 1483781 = 278209) (by norm_num)
theorem B10298389 : Blo 988596 10298389 := bbase (se 6 (by rfl) ⟨241368, by rfl⟩ : syracuseStep 10298389 = 482737) (by norm_num)
theorem B1483805 : Blo 988596 1483805 := bbase (se 3 (by rfl) ⟨278213, by rfl⟩ : syracuseStep 1483805 = 556427) (by norm_num)
theorem B1483829 : Blo 988596 1483829 := bbase (se 5 (by rfl) ⟨69554, by rfl⟩ : syracuseStep 1483829 = 139109) (by norm_num)
theorem B1254457 : Blo 988596 1254457 := bbase (se 2 (by rfl) ⟨470421, by rfl⟩ : syracuseStep 1254457 = 940843) (by norm_num)
theorem B1877069 : Blo 988596 1877069 := bbase (se 3 (by rfl) ⟨351950, by rfl⟩ : syracuseStep 1877069 = 703901) (by norm_num)
theorem B1483853 : Blo 988596 1483853 := bbase (se 3 (by rfl) ⟨278222, by rfl⟩ : syracuseStep 1483853 = 556445) (by norm_num)
theorem B1483877 : Blo 988596 1483877 := bbase (se 4 (by rfl) ⟨139113, by rfl⟩ : syracuseStep 1483877 = 278227) (by norm_num)
theorem B1483901 : Blo 988596 1483901 := bbase (se 3 (by rfl) ⟨278231, by rfl⟩ : syracuseStep 1483901 = 556463) (by norm_num)
theorem B1483925 : Blo 988596 1483925 := bbase (se 6 (by rfl) ⟨34779, by rfl⟩ : syracuseStep 1483925 = 69559) (by norm_num)
theorem B1483949 : Blo 988596 1483949 := bbase (se 3 (by rfl) ⟨278240, by rfl⟩ : syracuseStep 1483949 = 556481) (by norm_num)
theorem B1483973 : Blo 988596 1483973 := bbase (se 4 (by rfl) ⟨139122, by rfl⟩ : syracuseStep 1483973 = 278245) (by norm_num)
theorem B1483997 : Blo 988596 1483997 := bbase (se 3 (by rfl) ⟨278249, by rfl⟩ : syracuseStep 1483997 = 556499) (by norm_num)
theorem B1254629 : Blo 988596 1254629 := bbase (se 4 (by rfl) ⟨117621, by rfl⟩ : syracuseStep 1254629 = 235243) (by norm_num)
theorem B1484021 : Blo 988596 1484021 := bbase (se 5 (by rfl) ⟨69563, by rfl⟩ : syracuseStep 1484021 = 139127) (by norm_num)
theorem B1484045 : Blo 988596 1484045 := bbase (se 3 (by rfl) ⟨278258, by rfl⟩ : syracuseStep 1484045 = 556517) (by norm_num)
theorem B1254685 : Blo 988596 1254685 := bbase (se 3 (by rfl) ⟨235253, by rfl⟩ : syracuseStep 1254685 = 470507) (by norm_num)
theorem B1058081 : Blo 988596 1058081 := bbase (se 2 (by rfl) ⟨396780, by rfl⟩ : syracuseStep 1058081 = 793561) (by norm_num)
theorem B1484069 : Blo 988596 1484069 := bbase (se 4 (by rfl) ⟨139131, by rfl⟩ : syracuseStep 1484069 = 278263) (by norm_num)
theorem B1484093 : Blo 988596 1484093 := bbase (se 3 (by rfl) ⟨278267, by rfl⟩ : syracuseStep 1484093 = 556535) (by norm_num)
theorem B1484117 : Blo 988596 1484117 := bbase (se 12 (by rfl) ⟨543, by rfl⟩ : syracuseStep 1484117 = 1087) (by norm_num)
theorem B1058141 : Blo 988596 1058141 := bbase (se 3 (by rfl) ⟨198401, by rfl⟩ : syracuseStep 1058141 = 396803) (by norm_num)
theorem B1877357 : Blo 988596 1877357 := bbase (se 3 (by rfl) ⟨352004, by rfl⟩ : syracuseStep 1877357 = 704009) (by norm_num)
theorem B1484141 : Blo 988596 1484141 := bbase (se 3 (by rfl) ⟨278276, by rfl⟩ : syracuseStep 1484141 = 556553) (by norm_num)
theorem B1254781 : Blo 988596 1254781 := bbase (se 3 (by rfl) ⟨235271, by rfl⟩ : syracuseStep 1254781 = 470543) (by norm_num)
theorem B1484165 : Blo 988596 1484165 := bbase (se 4 (by rfl) ⟨139140, by rfl⟩ : syracuseStep 1484165 = 278281) (by norm_num)
theorem B6432149 : Blo 988596 6432149 := bbase (se 6 (by rfl) ⟨150753, by rfl⟩ : syracuseStep 6432149 = 301507) (by norm_num)
theorem B4760981 : Blo 988596 4760981 := bbase (se 6 (by rfl) ⟨111585, by rfl⟩ : syracuseStep 4760981 = 223171) (by norm_num)
theorem B1484189 : Blo 988596 1484189 := bbase (se 3 (by rfl) ⟨278285, by rfl⟩ : syracuseStep 1484189 = 556571) (by norm_num)
theorem B1484213 : Blo 988596 1484213 := bbase (se 5 (by rfl) ⟨69572, by rfl⟩ : syracuseStep 1484213 = 139145) (by norm_num)
theorem B1484237 : Blo 988596 1484237 := bbase (se 3 (by rfl) ⟨278294, by rfl⟩ : syracuseStep 1484237 = 556589) (by norm_num)
theorem B1058269 : Blo 988596 1058269 := bbase (se 3 (by rfl) ⟨198425, by rfl⟩ : syracuseStep 1058269 = 396851) (by norm_num)
theorem B1484261 : Blo 988596 1484261 := bbase (se 4 (by rfl) ⟨139149, by rfl⟩ : syracuseStep 1484261 = 278299) (by norm_num)
theorem B1189361 : Blo 988596 1189361 := bbase (se 2 (by rfl) ⟨446010, by rfl⟩ : syracuseStep 1189361 = 892021) (by norm_num)
theorem B1484285 : Blo 988596 1484285 := bbase (se 3 (by rfl) ⟨278303, by rfl⟩ : syracuseStep 1484285 = 556607) (by norm_num)
theorem B1877509 : Blo 988596 1877509 := bbase (se 4 (by rfl) ⟨176016, by rfl⟩ : syracuseStep 1877509 = 352033) (by norm_num)
theorem B1484309 : Blo 988596 1484309 := bbase (se 6 (by rfl) ⟨34788, by rfl⟩ : syracuseStep 1484309 = 69577) (by norm_num)
theorem B1189409 : Blo 988596 1189409 := bbase (se 2 (by rfl) ⟨446028, by rfl⟩ : syracuseStep 1189409 = 892057) (by norm_num)
theorem B1254953 : Blo 988596 1254953 := bbase (se 2 (by rfl) ⟨470607, by rfl⟩ : syracuseStep 1254953 = 941215) (by norm_num)
theorem B1484333 : Blo 988596 1484333 := bbase (se 3 (by rfl) ⟨278312, by rfl⟩ : syracuseStep 1484333 = 556625) (by norm_num)
theorem B10298933 : Blo 988596 10298933 := bbase (se 5 (by rfl) ⟨482762, by rfl⟩ : syracuseStep 10298933 = 965525) (by norm_num)
theorem B1484357 : Blo 988596 1484357 := bbase (se 4 (by rfl) ⟨139158, by rfl⟩ : syracuseStep 1484357 = 278317) (by norm_num)
theorem B1484381 : Blo 988596 1484381 := bbase (se 3 (by rfl) ⟨278321, by rfl⟩ : syracuseStep 1484381 = 556643) (by norm_num)
theorem B1255009 : Blo 988596 1255009 := bbase (se 2 (by rfl) ⟨470628, by rfl⟩ : syracuseStep 1255009 = 941257) (by norm_num)
theorem B1484405 : Blo 988596 1484405 := bbase (se 5 (by rfl) ⟨69581, by rfl⟩ : syracuseStep 1484405 = 139163) (by norm_num)
theorem B1484429 : Blo 988596 1484429 := bbase (se 3 (by rfl) ⟨278330, by rfl⟩ : syracuseStep 1484429 = 556661) (by norm_num)
theorem B2008733 : Blo 988596 2008733 := bbase (se 3 (by rfl) ⟨376637, by rfl⟩ : syracuseStep 2008733 = 753275) (by norm_num)
theorem B1484453 : Blo 988596 1484453 := bbase (se 4 (by rfl) ⟨139167, by rfl⟩ : syracuseStep 1484453 = 278335) (by norm_num)
theorem B1484477 : Blo 988596 1484477 := bbase (se 3 (by rfl) ⟨278339, by rfl⟩ : syracuseStep 1484477 = 556679) (by norm_num)
theorem B1255105 : Blo 988596 1255105 := bbase (se 2 (by rfl) ⟨470664, by rfl⟩ : syracuseStep 1255105 = 941329) (by norm_num)
theorem B1484501 : Blo 988596 1484501 := bbase (se 7 (by rfl) ⟨17396, by rfl⟩ : syracuseStep 1484501 = 34793) (by norm_num)
theorem B1484525 : Blo 988596 1484525 := bbase (se 3 (by rfl) ⟨278348, by rfl⟩ : syracuseStep 1484525 = 556697) (by norm_num)
theorem B1484549 : Blo 988596 1484549 := bbase (se 4 (by rfl) ⟨139176, by rfl⟩ : syracuseStep 1484549 = 278353) (by norm_num)
theorem B1484573 : Blo 988596 1484573 := bbase (se 3 (by rfl) ⟨278357, by rfl⟩ : syracuseStep 1484573 = 556715) (by norm_num)
theorem B1189669 : Blo 988596 1189669 := bbase (se 4 (by rfl) ⟨111531, by rfl⟩ : syracuseStep 1189669 = 223063) (by norm_num)
theorem B1877813 : Blo 988596 1877813 := bbase (se 5 (by rfl) ⟨88022, by rfl⟩ : syracuseStep 1877813 = 176045) (by norm_num)
theorem B1484597 : Blo 988596 1484597 := bbase (se 5 (by rfl) ⟨69590, by rfl⟩ : syracuseStep 1484597 = 139181) (by norm_num)
theorem B4237109 : Blo 988596 4237109 := bbase (se 5 (by rfl) ⟨198614, by rfl⟩ : syracuseStep 4237109 = 397229) (by norm_num)
theorem B1484621 : Blo 988596 1484621 := bbase (se 3 (by rfl) ⟨278366, by rfl⟩ : syracuseStep 1484621 = 556733) (by norm_num)
theorem B1484645 : Blo 988596 1484645 := bbase (se 4 (by rfl) ⟨139185, by rfl⟩ : syracuseStep 1484645 = 278371) (by norm_num)
theorem B1255277 : Blo 988596 1255277 := bbase (se 3 (by rfl) ⟨235364, by rfl⟩ : syracuseStep 1255277 = 470729) (by norm_num)
theorem B1484669 : Blo 988596 1484669 := bbase (se 3 (by rfl) ⟨278375, by rfl⟩ : syracuseStep 1484669 = 556751) (by norm_num)
theorem B1484693 : Blo 988596 1484693 := bbase (se 6 (by rfl) ⟨34797, by rfl⟩ : syracuseStep 1484693 = 69595) (by norm_num)
theorem B1058713 : Blo 988596 1058713 := bbase (se 2 (by rfl) ⟨397017, by rfl⟩ : syracuseStep 1058713 = 794035) (by norm_num)
theorem B1255333 : Blo 988596 1255333 := bbase (se 4 (by rfl) ⟨117687, by rfl⟩ : syracuseStep 1255333 = 235375) (by norm_num)
theorem B1484717 : Blo 988596 1484717 := bbase (se 3 (by rfl) ⟨278384, by rfl⟩ : syracuseStep 1484717 = 556769) (by norm_num)
theorem B1484741 : Blo 988596 1484741 := bbase (se 4 (by rfl) ⟨139194, by rfl⟩ : syracuseStep 1484741 = 278389) (by norm_num)
theorem B12036053 : Blo 988596 12036053 := bbase (se 7 (by rfl) ⟨141047, by rfl⟩ : syracuseStep 12036053 = 282095) (by norm_num)
theorem B1484765 : Blo 988596 1484765 := bbase (se 3 (by rfl) ⟨278393, by rfl⟩ : syracuseStep 1484765 = 556787) (by norm_num)
theorem B1484789 : Blo 988596 1484789 := bbase (se 5 (by rfl) ⟨69599, by rfl⟩ : syracuseStep 1484789 = 139199) (by norm_num)
theorem B1255429 : Blo 988596 1255429 := bbase (se 4 (by rfl) ⟨117696, by rfl⟩ : syracuseStep 1255429 = 235393) (by norm_num)
theorem B1484813 : Blo 988596 1484813 := bbase (se 3 (by rfl) ⟨278402, by rfl⟩ : syracuseStep 1484813 = 556805) (by norm_num)
theorem B1058833 : Blo 988596 1058833 := bbase (se 2 (by rfl) ⟨397062, by rfl⟩ : syracuseStep 1058833 = 794125) (by norm_num)
theorem B1484837 : Blo 988596 1484837 := bbase (se 4 (by rfl) ⟨139203, by rfl⟩ : syracuseStep 1484837 = 278407) (by norm_num)
theorem B5023781 : Blo 988596 5023781 := bbase (se 4 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 5023781 = 941959) (by norm_num)
theorem B1189933 : Blo 988596 1189933 := bbase (se 3 (by rfl) ⟨223112, by rfl⟩ : syracuseStep 1189933 = 446225) (by norm_num)
theorem B1484861 : Blo 988596 1484861 := bbase (se 3 (by rfl) ⟨278411, by rfl⟩ : syracuseStep 1484861 = 556823) (by norm_num)
theorem B1484885 : Blo 988596 1484885 := bbase (se 8 (by rfl) ⟨8700, by rfl⟩ : syracuseStep 1484885 = 17401) (by norm_num)
theorem B1484909 : Blo 988596 1484909 := bbase (se 3 (by rfl) ⟨278420, by rfl⟩ : syracuseStep 1484909 = 556841) (by norm_num)
theorem B1484933 : Blo 988596 1484933 := bbase (se 4 (by rfl) ⟨139212, by rfl⟩ : syracuseStep 1484933 = 278425) (by norm_num)
theorem B4761749 : Blo 988596 4761749 := bbase (se 6 (by rfl) ⟨111603, by rfl⟩ : syracuseStep 4761749 = 223207) (by norm_num)
theorem B1484957 : Blo 988596 1484957 := bbase (se 3 (by rfl) ⟨278429, by rfl⟩ : syracuseStep 1484957 = 556859) (by norm_num)
theorem B1190053 : Blo 988596 1190053 := bbase (se 4 (by rfl) ⟨111567, by rfl⟩ : syracuseStep 1190053 = 223135) (by norm_num)
theorem B1255601 : Blo 988596 1255601 := bbase (se 2 (by rfl) ⟨470850, by rfl⟩ : syracuseStep 1255601 = 941701) (by norm_num)
theorem B1484981 : Blo 988596 1484981 := bbase (se 5 (by rfl) ⟨69608, by rfl⟩ : syracuseStep 1484981 = 139217) (by norm_num)
theorem B1485005 : Blo 988596 1485005 := bbase (se 3 (by rfl) ⟨278438, by rfl⟩ : syracuseStep 1485005 = 556877) (by norm_num)
theorem B1485029 : Blo 988596 1485029 := bbase (se 4 (by rfl) ⟨139221, by rfl⟩ : syracuseStep 1485029 = 278443) (by norm_num)
theorem B1255657 : Blo 988596 1255657 := bbase (se 2 (by rfl) ⟨470871, by rfl⟩ : syracuseStep 1255657 = 941743) (by norm_num)
theorem B1485053 : Blo 988596 1485053 := bbase (se 3 (by rfl) ⟨278447, by rfl⟩ : syracuseStep 1485053 = 556895) (by norm_num)
theorem B1059085 : Blo 988596 1059085 := bbase (se 3 (by rfl) ⟨198578, by rfl⟩ : syracuseStep 1059085 = 397157) (by norm_num)
theorem B1059089 : Blo 988596 1059089 := bbase (se 2 (by rfl) ⟨397158, by rfl⟩ : syracuseStep 1059089 = 794317) (by norm_num)
theorem B1485077 : Blo 988596 1485077 := bbase (se 6 (by rfl) ⟨34806, by rfl⟩ : syracuseStep 1485077 = 69613) (by norm_num)
theorem B1485101 : Blo 988596 1485101 := bbase (se 3 (by rfl) ⟨278456, by rfl⟩ : syracuseStep 1485101 = 556913) (by norm_num)
theorem B1485125 : Blo 988596 1485125 := bbase (se 4 (by rfl) ⟨139230, by rfl⟩ : syracuseStep 1485125 = 278461) (by norm_num)
theorem B1255753 : Blo 988596 1255753 := bbase (se 2 (by rfl) ⟨470907, by rfl⟩ : syracuseStep 1255753 = 941815) (by norm_num)
theorem B1485149 : Blo 988596 1485149 := bbase (se 3 (by rfl) ⟨278465, by rfl⟩ : syracuseStep 1485149 = 556931) (by norm_num)
theorem B1485173 : Blo 988596 1485173 := bbase (se 5 (by rfl) ⟨69617, by rfl⟩ : syracuseStep 1485173 = 139235) (by norm_num)
theorem B1485197 : Blo 988596 1485197 := bbase (se 3 (by rfl) ⟨278474, by rfl⟩ : syracuseStep 1485197 = 556949) (by norm_num)
theorem B1485221 : Blo 988596 1485221 := bbase (se 4 (by rfl) ⟨139239, by rfl⟩ : syracuseStep 1485221 = 278479) (by norm_num)
theorem B1485245 : Blo 988596 1485245 := bbase (se 3 (by rfl) ⟨278483, by rfl⟩ : syracuseStep 1485245 = 556967) (by norm_num)
theorem B1485269 : Blo 988596 1485269 := bbase (se 7 (by rfl) ⟨17405, by rfl⟩ : syracuseStep 1485269 = 34811) (by norm_num)
theorem B11446741 : Blo 988596 11446741 := bbase (se 7 (by rfl) ⟨134141, by rfl⟩ : syracuseStep 11446741 = 268283) (by norm_num)
theorem B1485293 : Blo 988596 1485293 := bbase (se 3 (by rfl) ⟨278492, by rfl⟩ : syracuseStep 1485293 = 556985) (by norm_num)
theorem B1255925 : Blo 988596 1255925 := bbase (se 5 (by rfl) ⟨58871, by rfl⟩ : syracuseStep 1255925 = 117743) (by norm_num)
theorem B1485317 : Blo 988596 1485317 := bbase (se 4 (by rfl) ⟨139248, by rfl⟩ : syracuseStep 1485317 = 278497) (by norm_num)
theorem B1485341 : Blo 988596 1485341 := bbase (se 3 (by rfl) ⟨278501, by rfl⟩ : syracuseStep 1485341 = 557003) (by norm_num)
theorem B1878565 : Blo 988596 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B1255981 : Blo 988596 1255981 := bbase (se 3 (by rfl) ⟨235496, by rfl⟩ : syracuseStep 1255981 = 470993) (by norm_num)
theorem B1485365 : Blo 988596 1485365 := bbase (se 5 (by rfl) ⟨69626, by rfl⟩ : syracuseStep 1485365 = 139253) (by norm_num)
theorem B1485389 : Blo 988596 1485389 := bbase (se 3 (by rfl) ⟨278510, by rfl⟩ : syracuseStep 1485389 = 557021) (by norm_num)
theorem B1485413 : Blo 988596 1485413 := bbase (se 4 (by rfl) ⟨139257, by rfl⟩ : syracuseStep 1485413 = 278515) (by norm_num)
theorem B1485437 : Blo 988596 1485437 := bbase (se 3 (by rfl) ⟨278519, by rfl⟩ : syracuseStep 1485437 = 557039) (by norm_num)
theorem B1256077 : Blo 988596 1256077 := bbase (se 3 (by rfl) ⟨235514, by rfl⟩ : syracuseStep 1256077 = 471029) (by norm_num)
theorem B1485461 : Blo 988596 1485461 := bbase (se 6 (by rfl) ⟨34815, by rfl⟩ : syracuseStep 1485461 = 69631) (by norm_num)
theorem B1485485 : Blo 988596 1485485 := bbase (se 3 (by rfl) ⟨278528, by rfl⟩ : syracuseStep 1485485 = 557057) (by norm_num)
theorem B1878709 : Blo 988596 1878709 := bbase (se 5 (by rfl) ⟨88064, by rfl⟩ : syracuseStep 1878709 = 176129) (by norm_num)
theorem B1485509 : Blo 988596 1485509 := bbase (se 4 (by rfl) ⟨139266, by rfl⟩ : syracuseStep 1485509 = 278533) (by norm_num)
theorem B1485533 : Blo 988596 1485533 := bbase (se 3 (by rfl) ⟨278537, by rfl⟩ : syracuseStep 1485533 = 557075) (by norm_num)
theorem B1485557 : Blo 988596 1485557 := bbase (se 5 (by rfl) ⟨69635, by rfl⟩ : syracuseStep 1485557 = 139271) (by norm_num)
theorem B1485581 : Blo 988596 1485581 := bbase (se 3 (by rfl) ⟨278546, by rfl⟩ : syracuseStep 1485581 = 557093) (by norm_num)
theorem B1485605 : Blo 988596 1485605 := bbase (se 4 (by rfl) ⟨139275, by rfl⟩ : syracuseStep 1485605 = 278551) (by norm_num)
theorem B1256249 : Blo 988596 1256249 := bbase (se 2 (by rfl) ⟨471093, by rfl⟩ : syracuseStep 1256249 = 942187) (by norm_num)
theorem B1485629 : Blo 988596 1485629 := bbase (se 3 (by rfl) ⟨278555, by rfl⟩ : syracuseStep 1485629 = 557111) (by norm_num)
theorem B1059653 : Blo 988596 1059653 := bbase (se 4 (by rfl) ⟨99342, by rfl⟩ : syracuseStep 1059653 = 198685) (by norm_num)
theorem B1878869 : Blo 988596 1878869 := bbase (se 9 (by rfl) ⟨5504, by rfl⟩ : syracuseStep 1878869 = 11009) (by norm_num)
theorem B1485653 : Blo 988596 1485653 := bbase (se 9 (by rfl) ⟨4352, by rfl⟩ : syracuseStep 1485653 = 8705) (by norm_num)
theorem B1485677 : Blo 988596 1485677 := bbase (se 3 (by rfl) ⟨278564, by rfl⟩ : syracuseStep 1485677 = 557129) (by norm_num)
theorem B1485701 : Blo 988596 1485701 := bbase (se 4 (by rfl) ⟨139284, by rfl⟩ : syracuseStep 1485701 = 278569) (by norm_num)
theorem B1485725 : Blo 988596 1485725 := bbase (se 3 (by rfl) ⟨278573, by rfl⟩ : syracuseStep 1485725 = 557147) (by norm_num)
theorem B1485749 : Blo 988596 1485749 := bbase (se 5 (by rfl) ⟨69644, by rfl⟩ : syracuseStep 1485749 = 139289) (by norm_num)
theorem B1485773 : Blo 988596 1485773 := bbase (se 3 (by rfl) ⟨278582, by rfl⟩ : syracuseStep 1485773 = 557165) (by norm_num)
theorem B4303829 : Blo 988596 4303829 := bbase (se 7 (by rfl) ⟨50435, by rfl⟩ : syracuseStep 4303829 = 100871) (by norm_num)
theorem B1879013 : Blo 988596 1879013 := bbase (se 4 (by rfl) ⟨176157, by rfl⟩ : syracuseStep 1879013 = 352315) (by norm_num)
theorem B1485797 : Blo 988596 1485797 := bbase (se 4 (by rfl) ⟨139293, by rfl⟩ : syracuseStep 1485797 = 278587) (by norm_num)
theorem B1485821 : Blo 988596 1485821 := bbase (se 3 (by rfl) ⟨278591, by rfl⟩ : syracuseStep 1485821 = 557183) (by norm_num)
theorem B1190909 : Blo 988596 1190909 := bbase (se 3 (by rfl) ⟨223295, by rfl⟩ : syracuseStep 1190909 = 446591) (by norm_num)
theorem B1059841 : Blo 988596 1059841 := bbase (se 2 (by rfl) ⟨397440, by rfl⟩ : syracuseStep 1059841 = 794881) (by norm_num)
theorem B1485845 : Blo 988596 1485845 := bbase (se 6 (by rfl) ⟨34824, by rfl⟩ : syracuseStep 1485845 = 69649) (by norm_num)
theorem B1485869 : Blo 988596 1485869 := bbase (se 3 (by rfl) ⟨278600, by rfl⟩ : syracuseStep 1485869 = 557201) (by norm_num)
theorem B1485893 : Blo 988596 1485893 := bbase (se 4 (by rfl) ⟨139302, by rfl⟩ : syracuseStep 1485893 = 278605) (by norm_num)
theorem B1485917 : Blo 988596 1485917 := bbase (se 3 (by rfl) ⟨278609, by rfl⟩ : syracuseStep 1485917 = 557219) (by norm_num)
theorem B1485941 : Blo 988596 1485941 := bbase (se 5 (by rfl) ⟨69653, by rfl⟩ : syracuseStep 1485941 = 139307) (by norm_num)
theorem B1485965 : Blo 988596 1485965 := bbase (se 3 (by rfl) ⟨278618, by rfl⟩ : syracuseStep 1485965 = 557237) (by norm_num)
theorem B1485989 : Blo 988596 1485989 := bbase (se 4 (by rfl) ⟨139311, by rfl⟩ : syracuseStep 1485989 = 278623) (by norm_num)
theorem B1486013 : Blo 988596 1486013 := bbase (se 3 (by rfl) ⟨278627, by rfl⟩ : syracuseStep 1486013 = 557255) (by norm_num)
theorem B1486037 : Blo 988596 1486037 := bbase (se 7 (by rfl) ⟨17414, by rfl⟩ : syracuseStep 1486037 = 34829) (by norm_num)
theorem B1486061 : Blo 988596 1486061 := bbase (se 3 (by rfl) ⟨278636, by rfl⟩ : syracuseStep 1486061 = 557273) (by norm_num)
theorem B2010349 : Blo 988596 2010349 := bbase (se 3 (by rfl) ⟨376940, by rfl⟩ : syracuseStep 2010349 = 753881) (by norm_num)
theorem B1879301 : Blo 988596 1879301 := bbase (se 4 (by rfl) ⟨176184, by rfl⟩ : syracuseStep 1879301 = 352369) (by norm_num)
theorem B1486085 : Blo 988596 1486085 := bbase (se 4 (by rfl) ⟨139320, by rfl⟩ : syracuseStep 1486085 = 278641) (by norm_num)
theorem B1486109 : Blo 988596 1486109 := bbase (se 3 (by rfl) ⟨278645, by rfl⟩ : syracuseStep 1486109 = 557291) (by norm_num)
theorem B1486133 : Blo 988596 1486133 := bbase (se 5 (by rfl) ⟨69662, by rfl⟩ : syracuseStep 1486133 = 139325) (by norm_num)
theorem B1486157 : Blo 988596 1486157 := bbase (se 3 (by rfl) ⟨278654, by rfl⟩ : syracuseStep 1486157 = 557309) (by norm_num)
theorem B1486181 : Blo 988596 1486181 := bbase (se 4 (by rfl) ⟨139329, by rfl⟩ : syracuseStep 1486181 = 278659) (by norm_num)
theorem B1486205 : Blo 988596 1486205 := bbase (se 3 (by rfl) ⟨278663, by rfl⟩ : syracuseStep 1486205 = 557327) (by norm_num)
theorem B1584533 : Blo 988596 1584533 := bbase (se 6 (by rfl) ⟨37137, by rfl⟩ : syracuseStep 1584533 = 74275) (by norm_num)
theorem B1486229 : Blo 988596 1486229 := bbase (se 6 (by rfl) ⟨34833, by rfl⟩ : syracuseStep 1486229 = 69667) (by norm_num)
theorem B1879453 : Blo 988596 1879453 := bbase (se 3 (by rfl) ⟨352397, by rfl⟩ : syracuseStep 1879453 = 704795) (by norm_num)
theorem B1486253 : Blo 988596 1486253 := bbase (se 3 (by rfl) ⟨278672, by rfl⟩ : syracuseStep 1486253 = 557345) (by norm_num)
theorem B1486277 : Blo 988596 1486277 := bbase (se 4 (by rfl) ⟨139338, by rfl⟩ : syracuseStep 1486277 = 278677) (by norm_num)
theorem B1486301 : Blo 988596 1486301 := bbase (se 3 (by rfl) ⟨278681, by rfl⟩ : syracuseStep 1486301 = 557363) (by norm_num)
theorem B2207197 : Blo 988596 2207197 := bbase (se 3 (by rfl) ⟨413849, by rfl⟩ : syracuseStep 2207197 = 827699) (by norm_num)
theorem B1486325 : Blo 988596 1486325 := bbase (se 5 (by rfl) ⟨69671, by rfl⟩ : syracuseStep 1486325 = 139343) (by norm_num)
theorem B1486349 : Blo 988596 1486349 := bbase (se 3 (by rfl) ⟨278690, by rfl⟩ : syracuseStep 1486349 = 557381) (by norm_num)
theorem B1486373 : Blo 988596 1486373 := bbase (se 4 (by rfl) ⟨139347, by rfl⟩ : syracuseStep 1486373 = 278695) (by norm_num)
theorem B4238885 : Blo 988596 4238885 := bbase (se 4 (by rfl) ⟨397395, by rfl⟩ : syracuseStep 4238885 = 794791) (by norm_num)
theorem B1486397 : Blo 988596 1486397 := bbase (se 3 (by rfl) ⟨278699, by rfl⟩ : syracuseStep 1486397 = 557399) (by norm_num)
theorem B1486421 : Blo 988596 1486421 := bbase (se 8 (by rfl) ⟨8709, by rfl⟩ : syracuseStep 1486421 = 17419) (by norm_num)
theorem B1486445 : Blo 988596 1486445 := bbase (se 3 (by rfl) ⟨278708, by rfl⟩ : syracuseStep 1486445 = 557417) (by norm_num)
theorem B1486469 : Blo 988596 1486469 := bbase (se 4 (by rfl) ⟨139356, by rfl⟩ : syracuseStep 1486469 = 278713) (by norm_num)
theorem B3059333 : Blo 988596 3059333 := bbase (se 4 (by rfl) ⟨286812, by rfl⟩ : syracuseStep 3059333 = 573625) (by norm_num)
theorem B7614101 : Blo 988596 7614101 := bbase (se 6 (by rfl) ⟨178455, by rfl⟩ : syracuseStep 7614101 = 356911) (by norm_num)
theorem B1486493 : Blo 988596 1486493 := bbase (se 3 (by rfl) ⟨278717, by rfl⟩ : syracuseStep 1486493 = 557435) (by norm_num)
theorem B1715885 : Blo 988596 1715885 := bbase (se 3 (by rfl) ⟨321728, by rfl⟩ : syracuseStep 1715885 = 643457) (by norm_num)
theorem B1486517 : Blo 988596 1486517 := bbase (se 5 (by rfl) ⟨69680, by rfl⟩ : syracuseStep 1486517 = 139361) (by norm_num)
theorem B1879757 : Blo 988596 1879757 := bbase (se 3 (by rfl) ⟨352454, by rfl⟩ : syracuseStep 1879757 = 704909) (by norm_num)
theorem B1486541 : Blo 988596 1486541 := bbase (se 3 (by rfl) ⟨278726, by rfl⟩ : syracuseStep 1486541 = 557453) (by norm_num)
theorem B1191629 : Blo 988596 1191629 := bbase (se 3 (by rfl) ⟨223430, by rfl⟩ : syracuseStep 1191629 = 446861) (by norm_num)
theorem B1486565 : Blo 988596 1486565 := bbase (se 4 (by rfl) ⟨139365, by rfl⟩ : syracuseStep 1486565 = 278731) (by norm_num)
theorem B1486589 : Blo 988596 1486589 := bbase (se 3 (by rfl) ⟨278735, by rfl⟩ : syracuseStep 1486589 = 557471) (by norm_num)
theorem B1486613 : Blo 988596 1486613 := bbase (se 6 (by rfl) ⟨34842, by rfl⟩ : syracuseStep 1486613 = 69685) (by norm_num)
theorem B4239125 : Blo 988596 4239125 := bbase (se 6 (by rfl) ⟨99354, by rfl⟩ : syracuseStep 4239125 = 198709) (by norm_num)
theorem B1486637 : Blo 988596 1486637 := bbase (se 3 (by rfl) ⟨278744, by rfl⟩ : syracuseStep 1486637 = 557489) (by norm_num)
theorem B1486661 : Blo 988596 1486661 := bbase (se 4 (by rfl) ⟨139374, by rfl⟩ : syracuseStep 1486661 = 278749) (by norm_num)
theorem B2502485 : Blo 988596 2502485 := bbase (se 9 (by rfl) ⟨7331, by rfl⟩ : syracuseStep 2502485 = 14663) (by norm_num)
theorem B7515989 : Blo 988596 7515989 := bbase (se 9 (by rfl) ⟨22019, by rfl⟩ : syracuseStep 7515989 = 44039) (by norm_num)
theorem B1486685 : Blo 988596 1486685 := bbase (se 3 (by rfl) ⟨278753, by rfl⟩ : syracuseStep 1486685 = 557507) (by norm_num)
theorem B1486709 : Blo 988596 1486709 := bbase (se 5 (by rfl) ⟨69689, by rfl⟩ : syracuseStep 1486709 = 139379) (by norm_num)
theorem B1486733 : Blo 988596 1486733 := bbase (se 3 (by rfl) ⟨278762, by rfl⟩ : syracuseStep 1486733 = 557525) (by norm_num)
theorem B1486757 : Blo 988596 1486757 := bbase (se 4 (by rfl) ⟨139383, by rfl⟩ : syracuseStep 1486757 = 278767) (by norm_num)
theorem B1486781 : Blo 988596 1486781 := bbase (se 3 (by rfl) ⟨278771, by rfl⟩ : syracuseStep 1486781 = 557543) (by norm_num)
theorem B1486805 : Blo 988596 1486805 := bbase (se 7 (by rfl) ⟨17423, by rfl⟩ : syracuseStep 1486805 = 34847) (by norm_num)
theorem B1486829 : Blo 988596 1486829 := bbase (se 3 (by rfl) ⟨278780, by rfl⟩ : syracuseStep 1486829 = 557561) (by norm_num)
theorem B1191937 : Blo 988596 1191937 := bbase (se 2 (by rfl) ⟨446976, by rfl⟩ : syracuseStep 1191937 = 893953) (by norm_num)
theorem B1486853 : Blo 988596 1486853 := bbase (se 4 (by rfl) ⟨139392, by rfl⟩ : syracuseStep 1486853 = 278785) (by norm_num)
theorem B2502677 : Blo 988596 2502677 := bbase (se 6 (by rfl) ⟨58656, by rfl⟩ : syracuseStep 2502677 = 117313) (by norm_num)
theorem B1486877 : Blo 988596 1486877 := bbase (se 3 (by rfl) ⟨278789, by rfl⟩ : syracuseStep 1486877 = 557579) (by norm_num)
theorem B1486901 : Blo 988596 1486901 := bbase (se 5 (by rfl) ⟨69698, by rfl⟩ : syracuseStep 1486901 = 139397) (by norm_num)
theorem B1486925 : Blo 988596 1486925 := bbase (se 3 (by rfl) ⟨278798, by rfl⟩ : syracuseStep 1486925 = 557597) (by norm_num)
theorem B1192033 : Blo 988596 1192033 := bbase (se 2 (by rfl) ⟨447012, by rfl⟩ : syracuseStep 1192033 = 894025) (by norm_num)
theorem B1486949 : Blo 988596 1486949 := bbase (se 4 (by rfl) ⟨139401, by rfl⟩ : syracuseStep 1486949 = 278803) (by norm_num)
theorem B1486973 : Blo 988596 1486973 := bbase (se 3 (by rfl) ⟨278807, by rfl⟩ : syracuseStep 1486973 = 557615) (by norm_num)
theorem B1486997 : Blo 988596 1486997 := bbase (se 6 (by rfl) ⟨34851, by rfl⟩ : syracuseStep 1486997 = 69703) (by norm_num)
theorem B1487021 : Blo 988596 1487021 := bbase (se 3 (by rfl) ⟨278816, by rfl⟩ : syracuseStep 1487021 = 557633) (by norm_num)
theorem B1487045 : Blo 988596 1487045 := bbase (se 4 (by rfl) ⟨139410, by rfl⟩ : syracuseStep 1487045 = 278821) (by norm_num)
theorem B1487069 : Blo 988596 1487069 := bbase (se 3 (by rfl) ⟨278825, by rfl⟩ : syracuseStep 1487069 = 557651) (by norm_num)
theorem B1192177 : Blo 988596 1192177 := bbase (se 2 (by rfl) ⟨447066, by rfl⟩ : syracuseStep 1192177 = 894133) (by norm_num)
theorem B1487093 : Blo 988596 1487093 := bbase (se 5 (by rfl) ⟨69707, by rfl⟩ : syracuseStep 1487093 = 139415) (by norm_num)
theorem B1487117 : Blo 988596 1487117 := bbase (se 3 (by rfl) ⟨278834, by rfl⟩ : syracuseStep 1487117 = 557669) (by norm_num)
theorem B1487141 : Blo 988596 1487141 := bbase (se 4 (by rfl) ⟨139419, by rfl⟩ : syracuseStep 1487141 = 278839) (by norm_num)
theorem B1585469 : Blo 988596 1585469 := bbase (se 3 (by rfl) ⟨297275, by rfl⟩ : syracuseStep 1585469 = 594551) (by norm_num)
theorem B1487165 : Blo 988596 1487165 := bbase (se 3 (by rfl) ⟨278843, by rfl⟩ : syracuseStep 1487165 = 557687) (by norm_num)
theorem B1487189 : Blo 988596 1487189 := bbase (se 10 (by rfl) ⟨2178, by rfl⟩ : syracuseStep 1487189 = 4357) (by norm_num)
theorem B2503021 : Blo 988596 2503021 := bbase (se 3 (by rfl) ⟨469316, by rfl⟩ : syracuseStep 2503021 = 938633) (by norm_num)
theorem B1487213 : Blo 988596 1487213 := bbase (se 3 (by rfl) ⟨278852, by rfl⟩ : syracuseStep 1487213 = 557705) (by norm_num)
theorem B1487237 : Blo 988596 1487237 := bbase (se 4 (by rfl) ⟨139428, by rfl⟩ : syracuseStep 1487237 = 278857) (by norm_num)
theorem B1487261 : Blo 988596 1487261 := bbase (se 3 (by rfl) ⟨278861, by rfl⟩ : syracuseStep 1487261 = 557723) (by norm_num)
theorem B1487285 : Blo 988596 1487285 := bbase (se 5 (by rfl) ⟨69716, by rfl⟩ : syracuseStep 1487285 = 139433) (by norm_num)
theorem B1880509 : Blo 988596 1880509 := bbase (se 3 (by rfl) ⟨352595, by rfl⟩ : syracuseStep 1880509 = 705191) (by norm_num)
theorem B1487309 : Blo 988596 1487309 := bbase (se 3 (by rfl) ⟨278870, by rfl⟩ : syracuseStep 1487309 = 557741) (by norm_num)
theorem B2503133 : Blo 988596 2503133 := bbase (se 3 (by rfl) ⟨469337, by rfl⟩ : syracuseStep 2503133 = 938675) (by norm_num)
theorem B1487333 : Blo 988596 1487333 := bbase (se 4 (by rfl) ⟨139437, by rfl⟩ : syracuseStep 1487333 = 278875) (by norm_num)
theorem B5648885 : Blo 988596 5648885 := bbase (se 5 (by rfl) ⟨264791, by rfl⟩ : syracuseStep 5648885 = 529583) (by norm_num)
theorem B1487357 : Blo 988596 1487357 := bbase (se 3 (by rfl) ⟨278879, by rfl⟩ : syracuseStep 1487357 = 557759) (by norm_num)
theorem B1487381 : Blo 988596 1487381 := bbase (se 6 (by rfl) ⟨34860, by rfl⟩ : syracuseStep 1487381 = 69721) (by norm_num)
theorem B1487405 : Blo 988596 1487405 := bbase (se 3 (by rfl) ⟨278888, by rfl⟩ : syracuseStep 1487405 = 557777) (by norm_num)
theorem B1487429 : Blo 988596 1487429 := bbase (se 4 (by rfl) ⟨139446, by rfl⟩ : syracuseStep 1487429 = 278893) (by norm_num)
theorem B1880653 : Blo 988596 1880653 := bbase (se 3 (by rfl) ⟨352622, by rfl⟩ : syracuseStep 1880653 = 705245) (by norm_num)
theorem B1487453 : Blo 988596 1487453 := bbase (se 3 (by rfl) ⟨278897, by rfl⟩ : syracuseStep 1487453 = 557795) (by norm_num)
theorem B2863717 : Blo 988596 2863717 := bbase (se 4 (by rfl) ⟨268473, by rfl⟩ : syracuseStep 2863717 = 536947) (by norm_num)
theorem B1487477 : Blo 988596 1487477 := bbase (se 5 (by rfl) ⟨69725, by rfl⟩ : syracuseStep 1487477 = 139451) (by norm_num)
theorem B1487501 : Blo 988596 1487501 := bbase (se 3 (by rfl) ⟨278906, by rfl⟩ : syracuseStep 1487501 = 557813) (by norm_num)
theorem B2503325 : Blo 988596 2503325 := bbase (se 3 (by rfl) ⟨469373, by rfl⟩ : syracuseStep 2503325 = 938747) (by norm_num)
theorem B1487525 : Blo 988596 1487525 := bbase (se 4 (by rfl) ⟨139455, by rfl⟩ : syracuseStep 1487525 = 278911) (by norm_num)
theorem B3388085 : Blo 988596 3388085 := bbase (se 5 (by rfl) ⟨158816, by rfl⟩ : syracuseStep 3388085 = 317633) (by norm_num)
theorem B1487549 : Blo 988596 1487549 := bbase (se 3 (by rfl) ⟨278915, by rfl⟩ : syracuseStep 1487549 = 557831) (by norm_num)
theorem B1487573 : Blo 988596 1487573 := bbase (se 7 (by rfl) ⟨17432, by rfl⟩ : syracuseStep 1487573 = 34865) (by norm_num)
theorem B1880813 : Blo 988596 1880813 := bbase (se 3 (by rfl) ⟨352652, by rfl⟩ : syracuseStep 1880813 = 705305) (by norm_num)
theorem B1487597 : Blo 988596 1487597 := bbase (se 3 (by rfl) ⟨278924, by rfl⟩ : syracuseStep 1487597 = 557849) (by norm_num)
theorem B1487621 : Blo 988596 1487621 := bbase (se 4 (by rfl) ⟨139464, by rfl⟩ : syracuseStep 1487621 = 278929) (by norm_num)
theorem B1487645 : Blo 988596 1487645 := bbase (se 3 (by rfl) ⟨278933, by rfl⟩ : syracuseStep 1487645 = 557867) (by norm_num)
theorem B1487669 : Blo 988596 1487669 := bbase (se 5 (by rfl) ⟨69734, by rfl⟩ : syracuseStep 1487669 = 139469) (by norm_num)
theorem B1487693 : Blo 988596 1487693 := bbase (se 3 (by rfl) ⟨278942, by rfl⟩ : syracuseStep 1487693 = 557885) (by norm_num)
theorem B1487717 : Blo 988596 1487717 := bbase (se 4 (by rfl) ⟨139473, by rfl⟩ : syracuseStep 1487717 = 278947) (by norm_num)
theorem B1880957 : Blo 988596 1880957 := bbase (se 3 (by rfl) ⟨352679, by rfl⟩ : syracuseStep 1880957 = 705359) (by norm_num)
theorem B1487741 : Blo 988596 1487741 := bbase (se 3 (by rfl) ⟨278951, by rfl⟩ : syracuseStep 1487741 = 557903) (by norm_num)
theorem B1487765 : Blo 988596 1487765 := bbase (se 6 (by rfl) ⟨34869, by rfl⟩ : syracuseStep 1487765 = 69739) (by norm_num)
theorem B4010917 : Blo 988596 4010917 := bbase (se 4 (by rfl) ⟨376023, by rfl⟩ : syracuseStep 4010917 = 752047) (by norm_num)
theorem B1487789 : Blo 988596 1487789 := bbase (se 3 (by rfl) ⟨278960, by rfl⟩ : syracuseStep 1487789 = 557921) (by norm_num)
theorem B1586117 : Blo 988596 1586117 := bbase (se 4 (by rfl) ⟨148698, by rfl⟩ : syracuseStep 1586117 = 297397) (by norm_num)
theorem B1487813 : Blo 988596 1487813 := bbase (se 4 (by rfl) ⟨139482, by rfl⟩ : syracuseStep 1487813 = 278965) (by norm_num)
theorem B1487837 : Blo 988596 1487837 := bbase (se 3 (by rfl) ⟨278969, by rfl⟩ : syracuseStep 1487837 = 557939) (by norm_num)
theorem B2503669 : Blo 988596 2503669 := bbase (se 5 (by rfl) ⟨117359, by rfl⟩ : syracuseStep 2503669 = 234719) (by norm_num)
theorem B1782773 : Blo 988596 1782773 := bbase (se 5 (by rfl) ⟨83567, by rfl⟩ : syracuseStep 1782773 = 167135) (by norm_num)
theorem B1487861 : Blo 988596 1487861 := bbase (se 5 (by rfl) ⟨69743, by rfl⟩ : syracuseStep 1487861 = 139487) (by norm_num)
theorem B1487885 : Blo 988596 1487885 := bbase (se 3 (by rfl) ⟨278978, by rfl⟩ : syracuseStep 1487885 = 557957) (by norm_num)
theorem B1487909 : Blo 988596 1487909 := bbase (se 4 (by rfl) ⟨139491, by rfl⟩ : syracuseStep 1487909 = 278983) (by norm_num)
theorem B1487933 : Blo 988596 1487933 := bbase (se 3 (by rfl) ⟨278987, by rfl⟩ : syracuseStep 1487933 = 557975) (by norm_num)
theorem B1487957 : Blo 988596 1487957 := bbase (se 8 (by rfl) ⟨8718, by rfl⟩ : syracuseStep 1487957 = 17437) (by norm_num)
theorem B2503781 : Blo 988596 2503781 := bbase (se 4 (by rfl) ⟨234729, by rfl⟩ : syracuseStep 2503781 = 469459) (by norm_num)
theorem B1487981 : Blo 988596 1487981 := bbase (se 3 (by rfl) ⟨278996, by rfl⟩ : syracuseStep 1487981 = 557993) (by norm_num)
theorem B1488005 : Blo 988596 1488005 := bbase (se 4 (by rfl) ⟨139500, by rfl⟩ : syracuseStep 1488005 = 279001) (by norm_num)
theorem B1881245 : Blo 988596 1881245 := bbase (se 3 (by rfl) ⟨352733, by rfl⟩ : syracuseStep 1881245 = 705467) (by norm_num)
theorem B1488029 : Blo 988596 1488029 := bbase (se 3 (by rfl) ⟨279005, by rfl⟩ : syracuseStep 1488029 = 558011) (by norm_num)
theorem B1488053 : Blo 988596 1488053 := bbase (se 5 (by rfl) ⟨69752, by rfl⟩ : syracuseStep 1488053 = 139505) (by norm_num)
theorem B1488077 : Blo 988596 1488077 := bbase (se 3 (by rfl) ⟨279014, by rfl⟩ : syracuseStep 1488077 = 558029) (by norm_num)
theorem B1488101 : Blo 988596 1488101 := bbase (se 4 (by rfl) ⟨139509, by rfl⟩ : syracuseStep 1488101 = 279019) (by norm_num)
theorem B1488125 : Blo 988596 1488125 := bbase (se 3 (by rfl) ⟨279023, by rfl⟩ : syracuseStep 1488125 = 558047) (by norm_num)
theorem B1488149 : Blo 988596 1488149 := bbase (se 6 (by rfl) ⟨34878, by rfl⟩ : syracuseStep 1488149 = 69757) (by norm_num)
theorem B2503973 : Blo 988596 2503973 := bbase (se 4 (by rfl) ⟨234747, by rfl⟩ : syracuseStep 2503973 = 469495) (by norm_num)
theorem B1488173 : Blo 988596 1488173 := bbase (se 3 (by rfl) ⟨279032, by rfl⟩ : syracuseStep 1488173 = 558065) (by norm_num)
theorem B1881397 : Blo 988596 1881397 := bbase (se 5 (by rfl) ⟨88190, by rfl⟩ : syracuseStep 1881397 = 176381) (by norm_num)
theorem B1488197 : Blo 988596 1488197 := bbase (se 4 (by rfl) ⟨139518, by rfl⟩ : syracuseStep 1488197 = 279037) (by norm_num)
theorem B1488221 : Blo 988596 1488221 := bbase (se 3 (by rfl) ⟨279041, by rfl⟩ : syracuseStep 1488221 = 558083) (by norm_num)
theorem B1488245 : Blo 988596 1488245 := bbase (se 5 (by rfl) ⟨69761, by rfl⟩ : syracuseStep 1488245 = 139523) (by norm_num)
theorem B1488269 : Blo 988596 1488269 := bbase (se 3 (by rfl) ⟨279050, by rfl⟩ : syracuseStep 1488269 = 558101) (by norm_num)
theorem B1717661 : Blo 988596 1717661 := bbase (se 3 (by rfl) ⟨322061, by rfl⟩ : syracuseStep 1717661 = 644123) (by norm_num)
theorem B1488293 : Blo 988596 1488293 := bbase (se 4 (by rfl) ⟨139527, by rfl⟩ : syracuseStep 1488293 = 279055) (by norm_num)
theorem B1488317 : Blo 988596 1488317 := bbase (se 3 (by rfl) ⟨279059, by rfl⟩ : syracuseStep 1488317 = 558119) (by norm_num)
theorem B1488341 : Blo 988596 1488341 := bbase (se 7 (by rfl) ⟨17441, by rfl⟩ : syracuseStep 1488341 = 34883) (by norm_num)
theorem B1488365 : Blo 988596 1488365 := bbase (se 3 (by rfl) ⟨279068, by rfl⟩ : syracuseStep 1488365 = 558137) (by norm_num)
theorem B1488389 : Blo 988596 1488389 := bbase (se 4 (by rfl) ⟨139536, by rfl⟩ : syracuseStep 1488389 = 279073) (by norm_num)
theorem B1488413 : Blo 988596 1488413 := bbase (se 3 (by rfl) ⟨279077, by rfl⟩ : syracuseStep 1488413 = 558155) (by norm_num)
theorem B1488437 : Blo 988596 1488437 := bbase (se 5 (by rfl) ⟨69770, by rfl⟩ : syracuseStep 1488437 = 139541) (by norm_num)
theorem B1488461 : Blo 988596 1488461 := bbase (se 3 (by rfl) ⟨279086, by rfl⟩ : syracuseStep 1488461 = 558173) (by norm_num)
theorem B1881701 : Blo 988596 1881701 := bbase (se 4 (by rfl) ⟨176409, by rfl⟩ : syracuseStep 1881701 = 352819) (by norm_num)
theorem B1488485 : Blo 988596 1488485 := bbase (se 4 (by rfl) ⟨139545, by rfl⟩ : syracuseStep 1488485 = 279091) (by norm_num)
theorem B2504317 : Blo 988596 2504317 := bbase (se 3 (by rfl) ⟨469559, by rfl⟩ : syracuseStep 2504317 = 939119) (by norm_num)
theorem B1488509 : Blo 988596 1488509 := bbase (se 3 (by rfl) ⟨279095, by rfl⟩ : syracuseStep 1488509 = 558191) (by norm_num)
theorem B1488533 : Blo 988596 1488533 := bbase (se 6 (by rfl) ⟨34887, by rfl⟩ : syracuseStep 1488533 = 69775) (by norm_num)
theorem B1488557 : Blo 988596 1488557 := bbase (se 3 (by rfl) ⟨279104, by rfl⟩ : syracuseStep 1488557 = 558209) (by norm_num)
theorem B1488581 : Blo 988596 1488581 := bbase (se 4 (by rfl) ⟨139554, by rfl⟩ : syracuseStep 1488581 = 279109) (by norm_num)
theorem B1488605 : Blo 988596 1488605 := bbase (se 3 (by rfl) ⟨279113, by rfl⟩ : syracuseStep 1488605 = 558227) (by norm_num)
theorem B2504429 : Blo 988596 2504429 := bbase (se 3 (by rfl) ⟨469580, by rfl⟩ : syracuseStep 2504429 = 939161) (by norm_num)
theorem B1488629 : Blo 988596 1488629 := bbase (se 5 (by rfl) ⟨69779, by rfl⟩ : syracuseStep 1488629 = 139559) (by norm_num)
theorem B1488653 : Blo 988596 1488653 := bbase (se 3 (by rfl) ⟨279122, by rfl⟩ : syracuseStep 1488653 = 558245) (by norm_num)
theorem B1488677 : Blo 988596 1488677 := bbase (se 4 (by rfl) ⟨139563, by rfl⟩ : syracuseStep 1488677 = 279127) (by norm_num)
theorem B1128253 : Blo 988596 1128253 := bbase (se 3 (by rfl) ⟨211547, by rfl⟩ : syracuseStep 1128253 = 423095) (by norm_num)
theorem B1488701 : Blo 988596 1488701 := bbase (se 3 (by rfl) ⟨279131, by rfl⟩ : syracuseStep 1488701 = 558263) (by norm_num)
theorem B1488725 : Blo 988596 1488725 := bbase (se 9 (by rfl) ⟨4361, by rfl⟩ : syracuseStep 1488725 = 8723) (by norm_num)
theorem B1488749 : Blo 988596 1488749 := bbase (se 3 (by rfl) ⟨279140, by rfl⟩ : syracuseStep 1488749 = 558281) (by norm_num)
theorem B1488773 : Blo 988596 1488773 := bbase (se 4 (by rfl) ⟨139572, by rfl⟩ : syracuseStep 1488773 = 279145) (by norm_num)
theorem B16267157 : Blo 988596 16267157 := bbase (se 6 (by rfl) ⟨381261, by rfl⟩ : syracuseStep 16267157 = 762523) (by norm_num)
theorem B1488797 : Blo 988596 1488797 := bbase (se 3 (by rfl) ⟨279149, by rfl⟩ : syracuseStep 1488797 = 558299) (by norm_num)
theorem B1587109 : Blo 988596 1587109 := bbase (se 4 (by rfl) ⟨148791, by rfl⟩ : syracuseStep 1587109 = 297583) (by norm_num)
theorem B2504621 : Blo 988596 2504621 := bbase (se 3 (by rfl) ⟨469616, by rfl⟩ : syracuseStep 2504621 = 939233) (by norm_num)
theorem B1488821 : Blo 988596 1488821 := bbase (se 5 (by rfl) ⟨69788, by rfl⟩ : syracuseStep 1488821 = 139577) (by norm_num)
theorem B1488845 : Blo 988596 1488845 := bbase (se 3 (by rfl) ⟨279158, by rfl⟩ : syracuseStep 1488845 = 558317) (by norm_num)
theorem B1488869 : Blo 988596 1488869 := bbase (se 4 (by rfl) ⟨139581, by rfl⟩ : syracuseStep 1488869 = 279163) (by norm_num)
theorem B1488893 : Blo 988596 1488893 := bbase (se 3 (by rfl) ⟨279167, by rfl⟩ : syracuseStep 1488893 = 558335) (by norm_num)
theorem B6338645 : Blo 988596 6338645 := bbase (se 8 (by rfl) ⟨37140, by rfl⟩ : syracuseStep 6338645 = 74281) (by norm_num)
theorem B2504965 : Blo 988596 2504965 := bbase (se 4 (by rfl) ⟨234840, by rfl⟩ : syracuseStep 2504965 = 469681) (by norm_num)
theorem B2177285 : Blo 988596 2177285 := bbase (se 4 (by rfl) ⟨204120, by rfl⟩ : syracuseStep 2177285 = 408241) (by norm_num)
theorem B1882453 : Blo 988596 1882453 := bbase (se 10 (by rfl) ⟨2757, by rfl⟩ : syracuseStep 1882453 = 5515) (by norm_num)
theorem B1587557 : Blo 988596 1587557 := bbase (se 4 (by rfl) ⟨148833, by rfl⟩ : syracuseStep 1587557 = 297667) (by norm_num)
theorem B2505077 : Blo 988596 2505077 := bbase (se 5 (by rfl) ⟨117425, by rfl⟩ : syracuseStep 2505077 = 234851) (by norm_num)
theorem B1882597 : Blo 988596 1882597 := bbase (se 4 (by rfl) ⟨176493, by rfl⟩ : syracuseStep 1882597 = 352987) (by norm_num)
theorem B1587757 : Blo 988596 1587757 := bbase (se 3 (by rfl) ⟨297704, by rfl⟩ : syracuseStep 1587757 = 595409) (by norm_num)
theorem B2505269 : Blo 988596 2505269 := bbase (se 5 (by rfl) ⟨117434, by rfl⟩ : syracuseStep 2505269 = 234869) (by norm_num)
theorem B1129037 : Blo 988596 1129037 := bbase (se 3 (by rfl) ⟨211694, by rfl⟩ : syracuseStep 1129037 = 423389) (by norm_num)
theorem B1882757 : Blo 988596 1882757 := bbase (se 4 (by rfl) ⟨176508, by rfl⟩ : syracuseStep 1882757 = 353017) (by norm_num)
theorem B1882901 : Blo 988596 1882901 := bbase (se 6 (by rfl) ⟨44130, by rfl⟩ : syracuseStep 1882901 = 88261) (by norm_num)
theorem B2112293 : Blo 988596 2112293 := bbase (se 4 (by rfl) ⟨198027, by rfl⟩ : syracuseStep 2112293 = 396055) (by norm_num)
theorem B1588013 : Blo 988596 1588013 := bbase (se 3 (by rfl) ⟨297752, by rfl⟩ : syracuseStep 1588013 = 595505) (by norm_num)
theorem B24132437 : Blo 988596 24132437 := bbase (se 9 (by rfl) ⟨70700, by rfl⟩ : syracuseStep 24132437 = 141401) (by norm_num)
theorem B2505613 : Blo 988596 2505613 := bbase (se 3 (by rfl) ⟨469802, by rfl⟩ : syracuseStep 2505613 = 939605) (by norm_num)
theorem B2112437 : Blo 988596 2112437 := bbase (se 5 (by rfl) ⟨99020, by rfl⟩ : syracuseStep 2112437 = 198041) (by norm_num)
theorem B2505725 : Blo 988596 2505725 := bbase (se 3 (by rfl) ⟨469823, by rfl⟩ : syracuseStep 2505725 = 939647) (by norm_num)
theorem B1883189 : Blo 988596 1883189 := bbase (se 5 (by rfl) ⟨88274, by rfl⟩ : syracuseStep 1883189 = 176549) (by norm_num)
theorem B2505917 : Blo 988596 2505917 := bbase (se 3 (by rfl) ⟨469859, by rfl⟩ : syracuseStep 2505917 = 939719) (by norm_num)
theorem B1883341 : Blo 988596 1883341 := bbase (se 3 (by rfl) ⟨353126, by rfl⟩ : syracuseStep 1883341 = 706253) (by norm_num)
theorem B2112797 : Blo 988596 2112797 := bbase (se 3 (by rfl) ⟨396149, by rfl⟩ : syracuseStep 2112797 = 792299) (by norm_num)
theorem B2571605 : Blo 988596 2571605 := bbase (se 11 (by rfl) ⟨1883, by rfl⟩ : syracuseStep 2571605 = 3767) (by norm_num)
theorem B1785253 : Blo 988596 1785253 := bbase (se 4 (by rfl) ⟨167367, by rfl⟩ : syracuseStep 1785253 = 334735) (by norm_num)
theorem B1883645 : Blo 988596 1883645 := bbase (se 3 (by rfl) ⟨353183, by rfl⟩ : syracuseStep 1883645 = 706367) (by norm_num)
theorem B2506261 : Blo 988596 2506261 := bbase (se 6 (by rfl) ⟨58740, by rfl⟩ : syracuseStep 2506261 = 117481) (by norm_num)
theorem B1785397 : Blo 988596 1785397 := bbase (se 5 (by rfl) ⟨83690, by rfl⟩ : syracuseStep 1785397 = 167381) (by norm_num)
theorem B1130041 : Blo 988596 1130041 := bbase (se 2 (by rfl) ⟨423765, by rfl⟩ : syracuseStep 1130041 = 847531) (by norm_num)
theorem B2506373 : Blo 988596 2506373 := bbase (se 4 (by rfl) ⟨234972, by rfl⟩ : syracuseStep 2506373 = 469945) (by norm_num)
theorem B2506565 : Blo 988596 2506565 := bbase (se 4 (by rfl) ⟨234990, by rfl⟩ : syracuseStep 2506565 = 469981) (by norm_num)
theorem B1589141 : Blo 988596 1589141 := bbase (se 6 (by rfl) ⟨37245, by rfl⟩ : syracuseStep 1589141 = 74491) (by norm_num)
theorem B10731541 : Blo 988596 10731541 := bbase (se 6 (by rfl) ⟨251520, by rfl⟩ : syracuseStep 10731541 = 503041) (by norm_num)
theorem B2113685 : Blo 988596 2113685 := bbase (se 6 (by rfl) ⟨49539, by rfl⟩ : syracuseStep 2113685 = 99079) (by norm_num)
theorem B2506909 : Blo 988596 2506909 := bbase (se 3 (by rfl) ⟨470045, by rfl⟩ : syracuseStep 2506909 = 940091) (by norm_num)
theorem B2507021 : Blo 988596 2507021 := bbase (se 3 (by rfl) ⟨470066, by rfl⟩ : syracuseStep 2507021 = 940133) (by norm_num)
theorem B3621205 : Blo 988596 3621205 := bbase (se 10 (by rfl) ⟨5304, by rfl⟩ : syracuseStep 3621205 = 10609) (by norm_num)
theorem B1786205 : Blo 988596 1786205 := bbase (se 3 (by rfl) ⟨334913, by rfl⟩ : syracuseStep 1786205 = 669827) (by norm_num)
theorem B2113933 : Blo 988596 2113933 := bbase (se 3 (by rfl) ⟨396362, by rfl⟩ : syracuseStep 2113933 = 792725) (by norm_num)
theorem B1589653 : Blo 988596 1589653 := bbase (se 6 (by rfl) ⟨37257, by rfl⟩ : syracuseStep 1589653 = 74515) (by norm_num)
theorem B1130917 : Blo 988596 1130917 := bbase (se 4 (by rfl) ⟨106023, by rfl⟩ : syracuseStep 1130917 = 212047) (by norm_num)
theorem B2507213 : Blo 988596 2507213 := bbase (se 3 (by rfl) ⟨470102, by rfl⟩ : syracuseStep 2507213 = 940205) (by norm_num)
theorem B1786349 : Blo 988596 1786349 := bbase (se 3 (by rfl) ⟨334940, by rfl⟩ : syracuseStep 1786349 = 669881) (by norm_num)
theorem B1786421 : Blo 988596 1786421 := bbase (se 5 (by rfl) ⟨83738, by rfl⟩ : syracuseStep 1786421 = 167477) (by norm_num)
theorem B7717493 : Blo 988596 7717493 := bbase (se 5 (by rfl) ⟨361757, by rfl⟩ : syracuseStep 7717493 = 723515) (by norm_num)
theorem B1786637 : Blo 988596 1786637 := bbase (se 3 (by rfl) ⟨334994, by rfl⟩ : syracuseStep 1786637 = 669989) (by norm_num)
theorem B2507557 : Blo 988596 2507557 := bbase (se 4 (by rfl) ⟨235083, by rfl⟩ : syracuseStep 2507557 = 470167) (by norm_num)
theorem B2114437 : Blo 988596 2114437 := bbase (se 4 (by rfl) ⟨198228, by rfl⟩ : syracuseStep 2114437 = 396457) (by norm_num)
theorem B2507669 : Blo 988596 2507669 := bbase (se 6 (by rfl) ⟨58773, by rfl⟩ : syracuseStep 2507669 = 117547) (by norm_num)
theorem B2507861 : Blo 988596 2507861 := bbase (se 8 (by rfl) ⟨14694, by rfl⟩ : syracuseStep 2507861 = 29389) (by norm_num)
theorem B2376877 : Blo 988596 2376877 := bbase (se 3 (by rfl) ⟨445664, by rfl⟩ : syracuseStep 2376877 = 891329) (by norm_num)
theorem B3392725 : Blo 988596 3392725 := bbase (se 7 (by rfl) ⟨39758, by rfl⟩ : syracuseStep 3392725 = 79517) (by norm_num)
theorem B2376973 : Blo 988596 2376973 := bbase (se 3 (by rfl) ⟨445682, by rfl⟩ : syracuseStep 2376973 = 891365) (by norm_num)
theorem B2508205 : Blo 988596 2508205 := bbase (se 3 (by rfl) ⟨470288, by rfl⟩ : syracuseStep 2508205 = 940577) (by norm_num)
theorem B2508317 : Blo 988596 2508317 := bbase (se 3 (by rfl) ⟨470309, by rfl⟩ : syracuseStep 2508317 = 940619) (by norm_num)
theorem B1787437 : Blo 988596 1787437 := bbase (se 3 (by rfl) ⟨335144, by rfl⟩ : syracuseStep 1787437 = 670289) (by norm_num)
theorem B2541277 : Blo 988596 2541277 := bbase (se 3 (by rfl) ⟨476489, by rfl⟩ : syracuseStep 2541277 = 952979) (by norm_num)
theorem B2508509 : Blo 988596 2508509 := bbase (se 3 (by rfl) ⟨470345, by rfl⟩ : syracuseStep 2508509 = 940691) (by norm_num)
theorem B2115325 : Blo 988596 2115325 := bbase (se 3 (by rfl) ⟨396623, by rfl⟩ : syracuseStep 2115325 = 793247) (by norm_num)
theorem B4015909 : Blo 988596 4015909 := bbase (se 4 (by rfl) ⟨376491, by rfl⟩ : syracuseStep 4015909 = 752983) (by norm_num)
theorem B2508853 : Blo 988596 2508853 := bbase (se 5 (by rfl) ⟨117602, by rfl⟩ : syracuseStep 2508853 = 235205) (by norm_num)
theorem B2508965 : Blo 988596 2508965 := bbase (se 4 (by rfl) ⟨235215, by rfl⟩ : syracuseStep 2508965 = 470431) (by norm_num)
theorem B2115821 : Blo 988596 2115821 := bbase (se 3 (by rfl) ⟨396716, by rfl⟩ : syracuseStep 2115821 = 793433) (by norm_num)
theorem B2378069 : Blo 988596 2378069 := bbase (se 10 (by rfl) ⟨3483, by rfl⟩ : syracuseStep 2378069 = 6967) (by norm_num)
theorem B1788245 : Blo 988596 1788245 := bbase (se 10 (by rfl) ⟨2619, by rfl⟩ : syracuseStep 1788245 = 5239) (by norm_num)
theorem B2509157 : Blo 988596 2509157 := bbase (se 4 (by rfl) ⟨235233, by rfl⟩ : syracuseStep 2509157 = 470467) (by norm_num)
theorem B2411021 : Blo 988596 2411021 := bbase (se 3 (by rfl) ⟨452066, by rfl⟩ : syracuseStep 2411021 = 904133) (by norm_num)
theorem B1526293 : Blo 988596 1526293 := bbase (se 6 (by rfl) ⟨35772, by rfl⟩ : syracuseStep 1526293 = 71545) (by norm_num)
theorem B2509501 : Blo 988596 2509501 := bbase (se 3 (by rfl) ⟨470531, by rfl⟩ : syracuseStep 2509501 = 941063) (by norm_num)
theorem B2509613 : Blo 988596 2509613 := bbase (se 3 (by rfl) ⟨470552, by rfl⟩ : syracuseStep 2509613 = 941105) (by norm_num)
theorem B2509805 : Blo 988596 2509805 := bbase (se 3 (by rfl) ⟨470588, by rfl⟩ : syracuseStep 2509805 = 941177) (by norm_num)
theorem B2116709 : Blo 988596 2116709 := bbase (se 4 (by rfl) ⟨198441, by rfl⟩ : syracuseStep 2116709 = 396883) (by norm_num)
theorem B1002677 : Blo 988596 1002677 := bbase (se 5 (by rfl) ⟨47000, by rfl⟩ : syracuseStep 1002677 = 94001) (by norm_num)
theorem B1002709 : Blo 988596 1002709 := bbase (se 7 (by rfl) ⟨11750, by rfl⟩ : syracuseStep 1002709 = 23501) (by norm_num)
theorem B2116829 : Blo 988596 2116829 := bbase (se 3 (by rfl) ⟨396905, by rfl⟩ : syracuseStep 2116829 = 793811) (by norm_num)
theorem B2379029 : Blo 988596 2379029 := bbase (se 6 (by rfl) ⟨55758, by rfl⟩ : syracuseStep 2379029 = 111517) (by norm_num)
theorem B2510149 : Blo 988596 2510149 := bbase (se 4 (by rfl) ⟨235326, by rfl⟩ : syracuseStep 2510149 = 470653) (by norm_num)
theorem B3755429 : Blo 988596 3755429 := bbase (se 4 (by rfl) ⟨352071, by rfl⟩ : syracuseStep 3755429 = 704143) (by norm_num)
theorem B7523765 : Blo 988596 7523765 := bbase (se 5 (by rfl) ⟨352676, by rfl⟩ : syracuseStep 7523765 = 705353) (by norm_num)
theorem B2510261 : Blo 988596 2510261 := bbase (se 5 (by rfl) ⟨117668, by rfl⟩ : syracuseStep 2510261 = 235337) (by norm_num)
theorem B1527229 : Blo 988596 1527229 := bbase (se 3 (by rfl) ⟨286355, by rfl⟩ : syracuseStep 1527229 = 572711) (by norm_num)
theorem B2510453 : Blo 988596 2510453 := bbase (se 5 (by rfl) ⟨117677, by rfl⟩ : syracuseStep 2510453 = 235355) (by norm_num)
theorem B3755717 : Blo 988596 3755717 := bbase (se 4 (by rfl) ⟨352098, by rfl⟩ : syracuseStep 3755717 = 704197) (by norm_num)
theorem B2674421 : Blo 988596 2674421 := bbase (se 5 (by rfl) ⟨125363, by rfl⟩ : syracuseStep 2674421 = 250727) (by norm_num)
theorem B1003313 : Blo 988596 1003313 := bbase (se 2 (by rfl) ⟨376242, by rfl⟩ : syracuseStep 1003313 = 752485) (by norm_num)
theorem B2117461 : Blo 988596 2117461 := bbase (se 9 (by rfl) ⟨6203, by rfl⟩ : syracuseStep 2117461 = 12407) (by norm_num)
theorem B2510797 : Blo 988596 2510797 := bbase (se 3 (by rfl) ⟨470774, by rfl⟩ : syracuseStep 2510797 = 941549) (by norm_num)
theorem B6344693 : Blo 988596 6344693 := bbase (se 5 (by rfl) ⟨297407, by rfl⟩ : syracuseStep 6344693 = 594815) (by norm_num)
theorem B2510909 : Blo 988596 2510909 := bbase (se 3 (by rfl) ⟨470795, by rfl⟩ : syracuseStep 2510909 = 941591) (by norm_num)
theorem B2478221 : Blo 988596 2478221 := bbase (se 3 (by rfl) ⟨464666, by rfl⟩ : syracuseStep 2478221 = 929333) (by norm_num)
theorem B2674853 : Blo 988596 2674853 := bbase (se 4 (by rfl) ⟨250767, by rfl⟩ : syracuseStep 2674853 = 501535) (by norm_num)
theorem B2511101 : Blo 988596 2511101 := bbase (se 3 (by rfl) ⟨470831, by rfl⟩ : syracuseStep 2511101 = 941663) (by norm_num)
theorem B1692181 : Blo 988596 1692181 := bbase (se 6 (by rfl) ⟨39660, by rfl⟩ : syracuseStep 1692181 = 79321) (by norm_num)
theorem B2511445 : Blo 988596 2511445 := bbase (se 8 (by rfl) ⟨14715, by rfl⟩ : syracuseStep 2511445 = 29431) (by norm_num)
theorem B1004221 : Blo 988596 1004221 := bbase (se 3 (by rfl) ⟨188291, by rfl⟩ : syracuseStep 1004221 = 376583) (by norm_num)
theorem B2511557 : Blo 988596 2511557 := bbase (se 4 (by rfl) ⟨235458, by rfl⟩ : syracuseStep 2511557 = 470917) (by norm_num)
theorem B2118349 : Blo 988596 2118349 := bbase (se 3 (by rfl) ⟨397190, by rfl⟩ : syracuseStep 2118349 = 794381) (by norm_num)
theorem B4575989 : Blo 988596 4575989 := bbase (se 5 (by rfl) ⟨214499, by rfl⟩ : syracuseStep 4575989 = 428999) (by norm_num)
theorem B6017813 : Blo 988596 6017813 := bbase (se 6 (by rfl) ⟨141042, by rfl⟩ : syracuseStep 6017813 = 282085) (by norm_num)
theorem B1692461 : Blo 988596 1692461 := bbase (se 3 (by rfl) ⟨317336, by rfl⟩ : syracuseStep 1692461 = 634673) (by norm_num)
theorem B2118469 : Blo 988596 2118469 := bbase (se 4 (by rfl) ⟨198606, by rfl⟩ : syracuseStep 2118469 = 397213) (by norm_num)
theorem B7131989 : Blo 988596 7131989 := bbase (se 9 (by rfl) ⟨20894, by rfl⟩ : syracuseStep 7131989 = 41789) (by norm_num)
theorem B3756901 : Blo 988596 3756901 := bbase (se 4 (by rfl) ⟨352209, by rfl⟩ : syracuseStep 3756901 = 704419) (by norm_num)
theorem B2511749 : Blo 988596 2511749 := bbase (se 4 (by rfl) ⟨235476, by rfl⟩ : syracuseStep 2511749 = 470953) (by norm_num)
theorem B4281269 : Blo 988596 4281269 := bbase (se 5 (by rfl) ⟨200684, by rfl⟩ : syracuseStep 4281269 = 401369) (by norm_num)
theorem B1004525 : Blo 988596 1004525 := bbase (se 3 (by rfl) ⟨188348, by rfl⟩ : syracuseStep 1004525 = 376697) (by norm_num)
theorem B3167221 : Blo 988596 3167221 := bbase (se 5 (by rfl) ⟨148463, by rfl⟩ : syracuseStep 3167221 = 296927) (by norm_num)
theorem B2380789 : Blo 988596 2380789 := bbase (se 5 (by rfl) ⟨111599, by rfl⟩ : syracuseStep 2380789 = 223199) (by norm_num)
theorem B2675717 : Blo 988596 2675717 := bbase (se 4 (by rfl) ⟨250848, by rfl⟩ : syracuseStep 2675717 = 501697) (by norm_num)
theorem B2118725 : Blo 988596 2118725 := bbase (se 4 (by rfl) ⟨198630, by rfl⟩ : syracuseStep 2118725 = 397261) (by norm_num)
theorem B3757205 : Blo 988596 3757205 := bbase (se 6 (by rfl) ⟨88059, by rfl⟩ : syracuseStep 3757205 = 176119) (by norm_num)
theorem B2381021 : Blo 988596 2381021 := bbase (se 3 (by rfl) ⟨446441, by rfl⟩ : syracuseStep 2381021 = 892883) (by norm_num)
theorem B2512093 : Blo 988596 2512093 := bbase (se 3 (by rfl) ⟨471017, by rfl⟩ : syracuseStep 2512093 = 942035) (by norm_num)
theorem B2512205 : Blo 988596 2512205 := bbase (se 3 (by rfl) ⟨471038, by rfl⟩ : syracuseStep 2512205 = 942077) (by norm_num)
theorem B2512397 : Blo 988596 2512397 := bbase (se 3 (by rfl) ⟨471074, by rfl⟩ : syracuseStep 2512397 = 942149) (by norm_num)
theorem B1005089 : Blo 988596 1005089 := bbase (se 2 (by rfl) ⟨376908, by rfl⟩ : syracuseStep 1005089 = 753817) (by norm_num)
theorem B2381413 : Blo 988596 2381413 := bbase (se 4 (by rfl) ⟨223257, by rfl⟩ : syracuseStep 2381413 = 446515) (by norm_num)
theorem B2545253 : Blo 988596 2545253 := bbase (se 4 (by rfl) ⟨238617, by rfl⟩ : syracuseStep 2545253 = 477235) (by norm_num)
theorem B4511477 : Blo 988596 4511477 := bbase (se 5 (by rfl) ⟨211475, by rfl⟩ : syracuseStep 4511477 = 422951) (by norm_num)
theorem B2119613 : Blo 988596 2119613 := bbase (se 3 (by rfl) ⟨397427, by rfl⟩ : syracuseStep 2119613 = 794855) (by norm_num)
theorem B1103833 : Blo 988596 1103833 := bbase (se 2 (by rfl) ⟨413937, by rfl⟩ : syracuseStep 1103833 = 827875) (by norm_num)
theorem B2119853 : Blo 988596 2119853 := bbase (se 3 (by rfl) ⟨397472, by rfl⟩ : syracuseStep 2119853 = 794945) (by norm_num)
theorem B2578645 : Blo 988596 2578645 := bbase (se 7 (by rfl) ⟨30218, by rfl⟩ : syracuseStep 2578645 = 60437) (by norm_num)
theorem B11295125 : Blo 988596 11295125 := bbase (se 6 (by rfl) ⟨264729, by rfl⟩ : syracuseStep 11295125 = 529459) (by norm_num)
theorem B2546245 : Blo 988596 2546245 := bbase (se 4 (by rfl) ⟨238710, by rfl⟩ : syracuseStep 2546245 = 477421) (by norm_num)
theorem B8575637 : Blo 988596 8575637 := bbase (se 6 (by rfl) ⟨200991, by rfl⟩ : syracuseStep 8575637 = 401983) (by norm_num)
theorem B2382509 : Blo 988596 2382509 := bbase (se 3 (by rfl) ⟨446720, by rfl⟩ : syracuseStep 2382509 = 893441) (by norm_num)
theorem B2448181 : Blo 988596 2448181 := bbase (se 5 (by rfl) ⟨114758, by rfl⟩ : syracuseStep 2448181 = 229517) (by norm_num)
theorem B32168789 : Blo 988596 32168789 := bbase (se 9 (by rfl) ⟨94244, by rfl⟩ : syracuseStep 32168789 = 188489) (by norm_num)
theorem B5364629 : Blo 988596 5364629 := bbase (se 6 (by rfl) ⟨125733, by rfl⟩ : syracuseStep 5364629 = 251467) (by norm_num)
theorem B2382797 : Blo 988596 2382797 := bbase (se 3 (by rfl) ⟨446774, by rfl⟩ : syracuseStep 2382797 = 893549) (by norm_num)
theorem B1268689 : Blo 988596 1268689 := bbase (se 2 (by rfl) ⟨475758, by rfl⟩ : syracuseStep 1268689 = 951517) (by norm_num)
theorem B3759317 : Blo 988596 3759317 := bbase (se 7 (by rfl) ⟨44054, by rfl⟩ : syracuseStep 3759317 = 88109) (by norm_num)
theorem B41278805 : Blo 988596 41278805 := bbase (se 11 (by rfl) ⟨30233, by rfl⟩ : syracuseStep 41278805 = 60467) (by norm_num)
theorem B4513157 : Blo 988596 4513157 := bbase (se 4 (by rfl) ⟨423108, by rfl⟩ : syracuseStep 4513157 = 846217) (by norm_num)
theorem B12705173 : Blo 988596 12705173 := bbase (se 6 (by rfl) ⟨297777, by rfl⟩ : syracuseStep 12705173 = 595555) (by norm_num)
theorem B3759605 : Blo 988596 3759605 := bbase (se 5 (by rfl) ⟨176231, by rfl⟩ : syracuseStep 3759605 = 352463) (by norm_num)
theorem B3170117 : Blo 988596 3170117 := bbase (se 4 (by rfl) ⟨297198, by rfl⟩ : syracuseStep 3170117 = 594397) (by norm_num)
theorem B1072981 : Blo 988596 1072981 := bbase (se 9 (by rfl) ⟨3143, by rfl⟩ : syracuseStep 1072981 = 6287) (by norm_num)
theorem B1073089 : Blo 988596 1073089 := bbase (se 2 (by rfl) ⟨402408, by rfl⟩ : syracuseStep 1073089 = 804817) (by norm_num)
theorem B5005637 : Blo 988596 5005637 := bbase (se 4 (by rfl) ⟨469278, by rfl⟩ : syracuseStep 5005637 = 938557) (by norm_num)
theorem B3760789 : Blo 988596 3760789 := bbase (se 6 (by rfl) ⟨88143, by rfl⟩ : syracuseStep 3760789 = 176287) (by norm_num)
theorem B2417413 : Blo 988596 2417413 := bbase (se 4 (by rfl) ⟨226632, by rfl⟩ : syracuseStep 2417413 = 453265) (by norm_num)
theorem B1631069 : Blo 988596 1631069 := bbase (se 3 (by rfl) ⟨305825, by rfl⟩ : syracuseStep 1631069 = 611651) (by norm_num)
theorem B1696621 : Blo 988596 1696621 := bbase (se 3 (by rfl) ⟨318116, by rfl⟩ : syracuseStep 1696621 = 636233) (by norm_num)
theorem B3761093 : Blo 988596 3761093 := bbase (se 4 (by rfl) ⟨352602, by rfl⟩ : syracuseStep 3761093 = 705205) (by norm_num)
theorem B2384893 : Blo 988596 2384893 := bbase (se 3 (by rfl) ⟨447167, by rfl⟩ : syracuseStep 2384893 = 894335) (by norm_num)
theorem B42787925 : Blo 988596 42787925 := bbase (se 8 (by rfl) ⟨250710, by rfl⟩ : syracuseStep 42787925 = 501421) (by norm_num)
theorem B3171413 : Blo 988596 3171413 := bbase (se 8 (by rfl) ⟨18582, by rfl⟩ : syracuseStep 3171413 = 37165) (by norm_num)
theorem B1205453 : Blo 988596 1205453 := bbase (se 3 (by rfl) ⟨226022, by rfl⟩ : syracuseStep 1205453 = 452045) (by norm_num)
theorem B27059669 : Blo 988596 27059669 := bbase (se 7 (by rfl) ⟨317105, by rfl⟩ : syracuseStep 27059669 = 634211) (by norm_num)
theorem B5006933 : Blo 988596 5006933 := bbase (se 8 (by rfl) ⟨29337, by rfl⟩ : syracuseStep 5006933 = 58675) (by norm_num)
theorem B9168821 : Blo 988596 9168821 := bbase (se 5 (by rfl) ⟨429788, by rfl⟩ : syracuseStep 9168821 = 859577) (by norm_num)
theorem B8448245 : Blo 988596 8448245 := bbase (se 5 (by rfl) ⟨396011, by rfl⟩ : syracuseStep 8448245 = 792023) (by norm_num)
theorem B6023477 : Blo 988596 6023477 := bbase (se 5 (by rfl) ⟨282350, by rfl⟩ : syracuseStep 6023477 = 564701) (by norm_num)
theorem B1206757 : Blo 988596 1206757 := bbase (se 4 (by rfl) ⟨113133, by rfl⟩ : syracuseStep 1206757 = 226267) (by norm_num)
theorem B3336821 : Blo 988596 3336821 := bbase (se 5 (by rfl) ⟨156413, by rfl⟩ : syracuseStep 3336821 = 312827) (by norm_num)
theorem B4516661 : Blo 988596 4516661 := bbase (se 5 (by rfl) ⟨211718, by rfl⟩ : syracuseStep 4516661 = 423437) (by norm_num)
theorem B5008229 : Blo 988596 5008229 := bbase (se 4 (by rfl) ⟨469521, by rfl⟩ : syracuseStep 5008229 = 939043) (by norm_num)
theorem B4287365 : Blo 988596 4287365 := bbase (se 4 (by rfl) ⟨401940, by rfl⟩ : syracuseStep 4287365 = 803881) (by norm_num)
theorem B3173269 : Blo 988596 3173269 := bbase (se 6 (by rfl) ⟨74373, by rfl⟩ : syracuseStep 3173269 = 148747) (by norm_num)
theorem B3763205 : Blo 988596 3763205 := bbase (se 4 (by rfl) ⟨352800, by rfl⟩ : syracuseStep 3763205 = 705601) (by norm_num)
theorem B7531541 : Blo 988596 7531541 := bbase (se 6 (by rfl) ⟨176520, by rfl⟩ : syracuseStep 7531541 = 353041) (by norm_num)
theorem B3337253 : Blo 988596 3337253 := bbase (se 4 (by rfl) ⟨312867, by rfl⟩ : syracuseStep 3337253 = 625735) (by norm_num)
theorem B3763493 : Blo 988596 3763493 := bbase (se 4 (by rfl) ⟨352827, by rfl⟩ : syracuseStep 3763493 = 705655) (by norm_num)
theorem B3337685 : Blo 988596 3337685 := bbase (se 7 (by rfl) ⟨39113, by rfl⟩ : syracuseStep 3337685 = 78227) (by norm_num)
theorem B1338853 : Blo 988596 1338853 := bbase (se 4 (by rfl) ⟨125517, by rfl⟩ : syracuseStep 1338853 = 251035) (by norm_num)
theorem B4517461 : Blo 988596 4517461 := bbase (se 8 (by rfl) ⟨26469, by rfl⟩ : syracuseStep 4517461 = 52939) (by norm_num)
theorem B1339021 : Blo 988596 1339021 := bbase (se 3 (by rfl) ⟨251066, by rfl⟩ : syracuseStep 1339021 = 502133) (by norm_num)
theorem B1929053 : Blo 988596 1929053 := bbase (se 3 (by rfl) ⟨361697, by rfl⟩ : syracuseStep 1929053 = 723395) (by norm_num)
theorem B3338117 : Blo 988596 3338117 := bbase (se 4 (by rfl) ⟨312948, by rfl⟩ : syracuseStep 3338117 = 625897) (by norm_num)
theorem B3567493 : Blo 988596 3567493 := bbase (se 4 (by rfl) ⟨334452, by rfl⟩ : syracuseStep 3567493 = 668905) (by norm_num)
theorem B4223029 : Blo 988596 4223029 := bbase (se 5 (by rfl) ⟨197954, by rfl⟩ : syracuseStep 4223029 = 395909) (by norm_num)
theorem B5009525 : Blo 988596 5009525 := bbase (se 5 (by rfl) ⟨234821, by rfl⟩ : syracuseStep 5009525 = 469643) (by norm_num)
theorem B2224349 : Blo 988596 2224349 := bbase (se 3 (by rfl) ⟨417065, by rfl⟩ : syracuseStep 2224349 = 834131) (by norm_num)
theorem B2224421 : Blo 988596 2224421 := bbase (se 4 (by rfl) ⟨208539, by rfl⟩ : syracuseStep 2224421 = 417079) (by norm_num)
theorem B3338549 : Blo 988596 3338549 := bbase (se 5 (by rfl) ⟨156494, by rfl⟩ : syracuseStep 3338549 = 312989) (by norm_num)
theorem B2224493 : Blo 988596 2224493 := bbase (se 3 (by rfl) ⟨417092, by rfl⟩ : syracuseStep 2224493 = 834185) (by norm_num)
theorem B2224565 : Blo 988596 2224565 := bbase (se 5 (by rfl) ⟨104276, by rfl⟩ : syracuseStep 2224565 = 208553) (by norm_num)
theorem B3764677 : Blo 988596 3764677 := bbase (se 4 (by rfl) ⟨352938, by rfl⟩ : syracuseStep 3764677 = 705877) (by norm_num)
theorem B2224637 : Blo 988596 2224637 := bbase (se 3 (by rfl) ⟨417119, by rfl⟩ : syracuseStep 2224637 = 834239) (by norm_num)
theorem B2224709 : Blo 988596 2224709 := bbase (se 4 (by rfl) ⟨208566, by rfl⟩ : syracuseStep 2224709 = 417133) (by norm_num)
theorem B2224781 : Blo 988596 2224781 := bbase (se 3 (by rfl) ⟨417146, by rfl⟩ : syracuseStep 2224781 = 834293) (by norm_num)
theorem B2224853 : Blo 988596 2224853 := bbase (se 7 (by rfl) ⟨26072, by rfl⟩ : syracuseStep 2224853 = 52145) (by norm_num)
theorem B3338981 : Blo 988596 3338981 := bbase (se 4 (by rfl) ⟨313029, by rfl⟩ : syracuseStep 3338981 = 626059) (by norm_num)
theorem B3764981 : Blo 988596 3764981 := bbase (se 5 (by rfl) ⟨176483, by rfl⟩ : syracuseStep 3764981 = 352967) (by norm_num)
theorem B4223765 : Blo 988596 4223765 := bbase (se 6 (by rfl) ⟨98994, by rfl⟩ : syracuseStep 4223765 = 197989) (by norm_num)
theorem B2224925 : Blo 988596 2224925 := bbase (se 3 (by rfl) ⟨417173, by rfl⟩ : syracuseStep 2224925 = 834347) (by norm_num)
theorem B1340237 : Blo 988596 1340237 := bbase (se 3 (by rfl) ⟨251294, by rfl⟩ : syracuseStep 1340237 = 502589) (by norm_num)
theorem B2224997 : Blo 988596 2224997 := bbase (se 4 (by rfl) ⟨208593, by rfl⟩ : syracuseStep 2224997 = 417187) (by norm_num)
theorem B2225069 : Blo 988596 2225069 := bbase (se 3 (by rfl) ⟨417200, by rfl⟩ : syracuseStep 2225069 = 834401) (by norm_num)
theorem B5075909 : Blo 988596 5075909 := bbase (se 4 (by rfl) ⟨475866, by rfl⟩ : syracuseStep 5075909 = 951733) (by norm_num)
theorem B2225141 : Blo 988596 2225141 := bbase (se 5 (by rfl) ⟨104303, by rfl⟩ : syracuseStep 2225141 = 208607) (by norm_num)
theorem B3568661 : Blo 988596 3568661 := bbase (se 6 (by rfl) ⟨83640, by rfl⟩ : syracuseStep 3568661 = 167281) (by norm_num)
theorem B2290733 : Blo 988596 2290733 := bbase (se 3 (by rfl) ⟨429512, by rfl⟩ : syracuseStep 2290733 = 859025) (by norm_num)
theorem B2225213 : Blo 988596 2225213 := bbase (se 3 (by rfl) ⟨417227, by rfl⟩ : syracuseStep 2225213 = 834455) (by norm_num)
theorem B2225285 : Blo 988596 2225285 := bbase (se 4 (by rfl) ⟨208620, by rfl⟩ : syracuseStep 2225285 = 417241) (by norm_num)
theorem B3339413 : Blo 988596 3339413 := bbase (se 6 (by rfl) ⟨78267, by rfl⟩ : syracuseStep 3339413 = 156535) (by norm_num)
theorem B1668269 : Blo 988596 1668269 := bbase (se 3 (by rfl) ⟨312800, by rfl⟩ : syracuseStep 1668269 = 625601) (by norm_num)
theorem B2225357 : Blo 988596 2225357 := bbase (se 3 (by rfl) ⟨417254, by rfl⟩ : syracuseStep 2225357 = 834509) (by norm_num)
theorem B2225429 : Blo 988596 2225429 := bbase (se 6 (by rfl) ⟨52158, by rfl⟩ : syracuseStep 2225429 = 104317) (by norm_num)
theorem B1668397 : Blo 988596 1668397 := bbase (se 3 (by rfl) ⟨312824, by rfl⟩ : syracuseStep 1668397 = 625649) (by norm_num)
theorem B2225501 : Blo 988596 2225501 := bbase (se 3 (by rfl) ⟨417281, by rfl⟩ : syracuseStep 2225501 = 834563) (by norm_num)
theorem B1668485 : Blo 988596 1668485 := bbase (se 4 (by rfl) ⟨156420, by rfl⟩ : syracuseStep 1668485 = 312841) (by norm_num)
theorem B5010821 : Blo 988596 5010821 := bbase (se 4 (by rfl) ⟨469764, by rfl⟩ : syracuseStep 5010821 = 939529) (by norm_num)
theorem B2225573 : Blo 988596 2225573 := bbase (se 4 (by rfl) ⟨208647, by rfl⟩ : syracuseStep 2225573 = 417295) (by norm_num)
theorem B2225645 : Blo 988596 2225645 := bbase (se 3 (by rfl) ⟨417308, by rfl⟩ : syracuseStep 2225645 = 834617) (by norm_num)
theorem B1668613 : Blo 988596 1668613 := bbase (se 4 (by rfl) ⟨156432, by rfl⟩ : syracuseStep 1668613 = 312865) (by norm_num)
theorem B2225717 : Blo 988596 2225717 := bbase (se 5 (by rfl) ⟨104330, by rfl⟩ : syracuseStep 2225717 = 208661) (by norm_num)
theorem B3339845 : Blo 988596 3339845 := bbase (se 4 (by rfl) ⟨313110, by rfl⟩ : syracuseStep 3339845 = 626221) (by norm_num)
theorem B5633621 : Blo 988596 5633621 := bbase (se 8 (by rfl) ⟨33009, by rfl⟩ : syracuseStep 5633621 = 66019) (by norm_num)
theorem B1668701 : Blo 988596 1668701 := bbase (se 3 (by rfl) ⟨312881, by rfl⟩ : syracuseStep 1668701 = 625763) (by norm_num)
theorem B2225789 : Blo 988596 2225789 := bbase (se 3 (by rfl) ⟨417335, by rfl⟩ : syracuseStep 2225789 = 834671) (by norm_num)
theorem B2225861 : Blo 988596 2225861 := bbase (se 4 (by rfl) ⟨208674, by rfl⟩ : syracuseStep 2225861 = 417349) (by norm_num)
theorem B1668829 : Blo 988596 1668829 := bbase (se 3 (by rfl) ⟨312905, by rfl⟩ : syracuseStep 1668829 = 625811) (by norm_num)
theorem B2815717 : Blo 988596 2815717 := bbase (se 4 (by rfl) ⟨263973, by rfl⟩ : syracuseStep 2815717 = 527947) (by norm_num)
theorem B2225933 : Blo 988596 2225933 := bbase (se 3 (by rfl) ⟨417362, by rfl⟩ : syracuseStep 2225933 = 834725) (by norm_num)
theorem B1668917 : Blo 988596 1668917 := bbase (se 5 (by rfl) ⟨78230, by rfl⟩ : syracuseStep 1668917 = 156461) (by norm_num)
theorem B2226005 : Blo 988596 2226005 := bbase (se 9 (by rfl) ⟨6521, by rfl⟩ : syracuseStep 2226005 = 13043) (by norm_num)
theorem B2815877 : Blo 988596 2815877 := bbase (se 4 (by rfl) ⟨263988, by rfl⟩ : syracuseStep 2815877 = 527977) (by norm_num)
theorem B2226077 : Blo 988596 2226077 := bbase (se 3 (by rfl) ⟨417389, by rfl⟩ : syracuseStep 2226077 = 834779) (by norm_num)
theorem B1669045 : Blo 988596 1669045 := bbase (se 5 (by rfl) ⟨78236, by rfl⟩ : syracuseStep 1669045 = 156473) (by norm_num)
theorem B1341373 : Blo 988596 1341373 := bbase (se 3 (by rfl) ⟨251507, by rfl⟩ : syracuseStep 1341373 = 503015) (by norm_num)
theorem B1505237 : Blo 988596 1505237 := bbase (se 7 (by rfl) ⟨17639, by rfl⟩ : syracuseStep 1505237 = 35279) (by norm_num)
theorem B2226149 : Blo 988596 2226149 := bbase (se 4 (by rfl) ⟨208701, by rfl⟩ : syracuseStep 2226149 = 417403) (by norm_num)
theorem B3340277 : Blo 988596 3340277 := bbase (se 5 (by rfl) ⟨156575, by rfl⟩ : syracuseStep 3340277 = 313151) (by norm_num)
theorem B1669133 : Blo 988596 1669133 := bbase (se 3 (by rfl) ⟨312962, by rfl⟩ : syracuseStep 1669133 = 625925) (by norm_num)
theorem B2226221 : Blo 988596 2226221 := bbase (se 3 (by rfl) ⟨417416, by rfl⟩ : syracuseStep 2226221 = 834833) (by norm_num)
theorem B2816117 : Blo 988596 2816117 := bbase (se 5 (by rfl) ⟨132005, by rfl⟩ : syracuseStep 2816117 = 264011) (by norm_num)
theorem B2226293 : Blo 988596 2226293 := bbase (se 5 (by rfl) ⟨104357, by rfl⟩ : syracuseStep 2226293 = 208715) (by norm_num)
theorem B1112197 : Blo 988596 1112197 := bbase (se 4 (by rfl) ⟨104268, by rfl⟩ : syracuseStep 1112197 = 208537) (by norm_num)
theorem B1669261 : Blo 988596 1669261 := bbase (se 3 (by rfl) ⟨312986, by rfl⟩ : syracuseStep 1669261 = 625973) (by norm_num)
theorem B9664661 : Blo 988596 9664661 := bbase (se 6 (by rfl) ⟨226515, by rfl⟩ : syracuseStep 9664661 = 453031) (by norm_num)
theorem B1112233 : Blo 988596 1112233 := bbase (se 2 (by rfl) ⟨417087, by rfl⟩ : syracuseStep 1112233 = 834175) (by norm_num)
theorem B2226365 : Blo 988596 2226365 := bbase (se 3 (by rfl) ⟨417443, by rfl⟩ : syracuseStep 2226365 = 834887) (by norm_num)
theorem B1112269 : Blo 988596 1112269 := bbase (se 3 (by rfl) ⟨208550, by rfl⟩ : syracuseStep 1112269 = 417101) (by norm_num)
theorem B1669349 : Blo 988596 1669349 := bbase (se 4 (by rfl) ⟨156501, by rfl⟩ : syracuseStep 1669349 = 313003) (by norm_num)
theorem B1112305 : Blo 988596 1112305 := bbase (se 2 (by rfl) ⟨417114, by rfl⟩ : syracuseStep 1112305 = 834229) (by norm_num)
theorem B2226437 : Blo 988596 2226437 := bbase (se 4 (by rfl) ⟨208728, by rfl⟩ : syracuseStep 2226437 = 417457) (by norm_num)
theorem B1112341 : Blo 988596 1112341 := bbase (se 6 (by rfl) ⟨26070, by rfl⟩ : syracuseStep 1112341 = 52141) (by norm_num)
theorem B2816309 : Blo 988596 2816309 := bbase (se 5 (by rfl) ⟨132014, by rfl⟩ : syracuseStep 2816309 = 264029) (by norm_num)
theorem B1112377 : Blo 988596 1112377 := bbase (se 2 (by rfl) ⟨417141, by rfl⟩ : syracuseStep 1112377 = 834283) (by norm_num)
theorem B2226509 : Blo 988596 2226509 := bbase (se 3 (by rfl) ⟨417470, by rfl⟩ : syracuseStep 2226509 = 834941) (by norm_num)
theorem B1505621 : Blo 988596 1505621 := bbase (se 10 (by rfl) ⟨2205, by rfl⟩ : syracuseStep 1505621 = 4411) (by norm_num)
theorem B1112413 : Blo 988596 1112413 := bbase (se 3 (by rfl) ⟨208577, by rfl⟩ : syracuseStep 1112413 = 417155) (by norm_num)
theorem B1669477 : Blo 988596 1669477 := bbase (se 4 (by rfl) ⟨156513, by rfl⟩ : syracuseStep 1669477 = 313027) (by norm_num)
theorem B1112449 : Blo 988596 1112449 := bbase (se 2 (by rfl) ⟨417168, by rfl⟩ : syracuseStep 1112449 = 834337) (by norm_num)
theorem B2226581 : Blo 988596 2226581 := bbase (se 6 (by rfl) ⟨52185, by rfl⟩ : syracuseStep 2226581 = 104371) (by norm_num)
theorem B1112485 : Blo 988596 1112485 := bbase (se 4 (by rfl) ⟨104295, by rfl⟩ : syracuseStep 1112485 = 208591) (by norm_num)
theorem B3340709 : Blo 988596 3340709 := bbase (se 4 (by rfl) ⟨313191, by rfl⟩ : syracuseStep 3340709 = 626383) (by norm_num)
theorem B1669565 : Blo 988596 1669565 := bbase (se 3 (by rfl) ⟨313043, by rfl⟩ : syracuseStep 1669565 = 626087) (by norm_num)
theorem B1112521 : Blo 988596 1112521 := bbase (se 2 (by rfl) ⟨417195, by rfl⟩ : syracuseStep 1112521 = 834391) (by norm_num)
theorem B2226653 : Blo 988596 2226653 := bbase (se 3 (by rfl) ⟨417497, by rfl⟩ : syracuseStep 2226653 = 834995) (by norm_num)
theorem B1112557 : Blo 988596 1112557 := bbase (se 3 (by rfl) ⟨208604, by rfl⟩ : syracuseStep 1112557 = 417209) (by norm_num)
theorem B1112593 : Blo 988596 1112593 := bbase (se 2 (by rfl) ⟨417222, by rfl⟩ : syracuseStep 1112593 = 834445) (by norm_num)
theorem B2226725 : Blo 988596 2226725 := bbase (se 4 (by rfl) ⟨208755, by rfl⟩ : syracuseStep 2226725 = 417511) (by norm_num)
theorem B1112629 : Blo 988596 1112629 := bbase (se 5 (by rfl) ⟨52154, by rfl⟩ : syracuseStep 1112629 = 104309) (by norm_num)
theorem B1669693 : Blo 988596 1669693 := bbase (se 3 (by rfl) ⟨313067, by rfl⟩ : syracuseStep 1669693 = 626135) (by norm_num)
theorem B2259533 : Blo 988596 2259533 := bbase (se 3 (by rfl) ⟨423662, by rfl⟩ : syracuseStep 2259533 = 847325) (by norm_num)
theorem B1112665 : Blo 988596 1112665 := bbase (se 2 (by rfl) ⟨417249, by rfl⟩ : syracuseStep 1112665 = 834499) (by norm_num)
theorem B2226797 : Blo 988596 2226797 := bbase (se 3 (by rfl) ⟨417524, by rfl⟩ : syracuseStep 2226797 = 835049) (by norm_num)
theorem B1112701 : Blo 988596 1112701 := bbase (se 3 (by rfl) ⟨208631, by rfl⟩ : syracuseStep 1112701 = 417263) (by norm_num)
theorem B1669781 : Blo 988596 1669781 := bbase (se 6 (by rfl) ⟨39135, by rfl⟩ : syracuseStep 1669781 = 78271) (by norm_num)
theorem B5012117 : Blo 988596 5012117 := bbase (se 6 (by rfl) ⟨117471, by rfl⟩ : syracuseStep 5012117 = 234943) (by norm_num)
theorem B1112737 : Blo 988596 1112737 := bbase (se 2 (by rfl) ⟨417276, by rfl⟩ : syracuseStep 1112737 = 834553) (by norm_num)
theorem B2226869 : Blo 988596 2226869 := bbase (se 5 (by rfl) ⟨104384, by rfl⟩ : syracuseStep 2226869 = 208769) (by norm_num)
theorem B1112773 : Blo 988596 1112773 := bbase (se 4 (by rfl) ⟨104322, by rfl⟩ : syracuseStep 1112773 = 208645) (by norm_num)
theorem B1112809 : Blo 988596 1112809 := bbase (se 2 (by rfl) ⟨417303, by rfl⟩ : syracuseStep 1112809 = 834607) (by norm_num)
theorem B5634805 : Blo 988596 5634805 := bbase (se 5 (by rfl) ⟨264131, by rfl⟩ : syracuseStep 5634805 = 528263) (by norm_num)
theorem B2226941 : Blo 988596 2226941 := bbase (se 3 (by rfl) ⟨417551, by rfl⟩ : syracuseStep 2226941 = 835103) (by norm_num)
theorem B1112845 : Blo 988596 1112845 := bbase (se 3 (by rfl) ⟨208658, by rfl⟩ : syracuseStep 1112845 = 417317) (by norm_num)
theorem B1669909 : Blo 988596 1669909 := bbase (se 6 (by rfl) ⟨39138, by rfl⟩ : syracuseStep 1669909 = 78277) (by norm_num)
theorem B1112881 : Blo 988596 1112881 := bbase (se 2 (by rfl) ⟨417330, by rfl⟩ : syracuseStep 1112881 = 834661) (by norm_num)
theorem B3767093 : Blo 988596 3767093 := bbase (se 5 (by rfl) ⟨176582, by rfl⟩ : syracuseStep 3767093 = 353165) (by norm_num)
theorem B2227013 : Blo 988596 2227013 := bbase (se 4 (by rfl) ⟨208782, by rfl⟩ : syracuseStep 2227013 = 417565) (by norm_num)
theorem B1506125 : Blo 988596 1506125 := bbase (se 3 (by rfl) ⟨282398, by rfl⟩ : syracuseStep 1506125 = 564797) (by norm_num)
theorem B1112917 : Blo 988596 1112917 := bbase (se 9 (by rfl) ⟨3260, by rfl⟩ : syracuseStep 1112917 = 6521) (by norm_num)
theorem B3341141 : Blo 988596 3341141 := bbase (se 9 (by rfl) ⟨9788, by rfl⟩ : syracuseStep 3341141 = 19577) (by norm_num)
theorem B1669997 : Blo 988596 1669997 := bbase (se 3 (by rfl) ⟨313124, by rfl⟩ : syracuseStep 1669997 = 626249) (by norm_num)
theorem B1112953 : Blo 988596 1112953 := bbase (se 2 (by rfl) ⟨417357, by rfl⟩ : syracuseStep 1112953 = 834715) (by norm_num)
theorem B2227085 : Blo 988596 2227085 := bbase (se 3 (by rfl) ⟨417578, by rfl⟩ : syracuseStep 2227085 = 835157) (by norm_num)
theorem B1112989 : Blo 988596 1112989 := bbase (se 3 (by rfl) ⟨208685, by rfl⟩ : syracuseStep 1112989 = 417371) (by norm_num)
theorem B1506205 : Blo 988596 1506205 := bbase (se 3 (by rfl) ⟨282413, by rfl⟩ : syracuseStep 1506205 = 564827) (by norm_num)
theorem B1113025 : Blo 988596 1113025 := bbase (se 2 (by rfl) ⟨417384, by rfl⟩ : syracuseStep 1113025 = 834769) (by norm_num)
theorem B2227157 : Blo 988596 2227157 := bbase (se 7 (by rfl) ⟨26099, by rfl⟩ : syracuseStep 2227157 = 52199) (by norm_num)
theorem B1113061 : Blo 988596 1113061 := bbase (se 4 (by rfl) ⟨104349, by rfl⟩ : syracuseStep 1113061 = 208699) (by norm_num)
theorem B1670125 : Blo 988596 1670125 := bbase (se 3 (by rfl) ⟨313148, by rfl⟩ : syracuseStep 1670125 = 626297) (by norm_num)
theorem B3177461 : Blo 988596 3177461 := bbase (se 5 (by rfl) ⟨148943, by rfl⟩ : syracuseStep 3177461 = 297887) (by norm_num)
theorem B1113097 : Blo 988596 1113097 := bbase (se 2 (by rfl) ⟨417411, by rfl⟩ : syracuseStep 1113097 = 834823) (by norm_num)
theorem B2227229 : Blo 988596 2227229 := bbase (se 3 (by rfl) ⟨417605, by rfl⟩ : syracuseStep 2227229 = 835211) (by norm_num)
theorem B1113133 : Blo 988596 1113133 := bbase (se 3 (by rfl) ⟨208712, by rfl⟩ : syracuseStep 1113133 = 417425) (by norm_num)
theorem B1670213 : Blo 988596 1670213 := bbase (se 4 (by rfl) ⟨156582, by rfl⟩ : syracuseStep 1670213 = 313165) (by norm_num)
theorem B1113169 : Blo 988596 1113169 := bbase (se 2 (by rfl) ⟨417438, by rfl⟩ : syracuseStep 1113169 = 834877) (by norm_num)
theorem B3767381 : Blo 988596 3767381 := bbase (se 8 (by rfl) ⟨22074, by rfl⟩ : syracuseStep 3767381 = 44149) (by norm_num)
theorem B2227301 : Blo 988596 2227301 := bbase (se 4 (by rfl) ⟨208809, by rfl⟩ : syracuseStep 2227301 = 417619) (by norm_num)
theorem B1408109 : Blo 988596 1408109 := bbase (se 3 (by rfl) ⟨264020, by rfl⟩ : syracuseStep 1408109 = 528041) (by norm_num)
theorem B1113205 : Blo 988596 1113205 := bbase (se 5 (by rfl) ⟨52181, by rfl⟩ : syracuseStep 1113205 = 104363) (by norm_num)
theorem B4586645 : Blo 988596 4586645 := bbase (se 6 (by rfl) ⟨107499, by rfl⟩ : syracuseStep 4586645 = 214999) (by norm_num)
theorem B1113241 : Blo 988596 1113241 := bbase (se 2 (by rfl) ⟨417465, by rfl⟩ : syracuseStep 1113241 = 834931) (by norm_num)
theorem B2227373 : Blo 988596 2227373 := bbase (se 3 (by rfl) ⟨417632, by rfl⟩ : syracuseStep 2227373 = 835265) (by norm_num)
theorem B1113277 : Blo 988596 1113277 := bbase (se 3 (by rfl) ⟨208739, by rfl⟩ : syracuseStep 1113277 = 417479) (by norm_num)
theorem B1670341 : Blo 988596 1670341 := bbase (se 4 (by rfl) ⟨156594, by rfl⟩ : syracuseStep 1670341 = 313189) (by norm_num)
theorem B1113313 : Blo 988596 1113313 := bbase (se 2 (by rfl) ⟨417492, by rfl⟩ : syracuseStep 1113313 = 834985) (by norm_num)
theorem B2227445 : Blo 988596 2227445 := bbase (se 5 (by rfl) ⟨104411, by rfl⟩ : syracuseStep 2227445 = 208823) (by norm_num)
theorem B1113349 : Blo 988596 1113349 := bbase (se 4 (by rfl) ⟨104376, by rfl⟩ : syracuseStep 1113349 = 208753) (by norm_num)
theorem B3341573 : Blo 988596 3341573 := bbase (se 4 (by rfl) ⟨313272, by rfl⟩ : syracuseStep 3341573 = 626545) (by norm_num)
theorem B2817301 : Blo 988596 2817301 := bbase (se 6 (by rfl) ⟨66030, by rfl⟩ : syracuseStep 2817301 = 132061) (by norm_num)
theorem B1670429 : Blo 988596 1670429 := bbase (se 3 (by rfl) ⟨313205, by rfl⟩ : syracuseStep 1670429 = 626411) (by norm_num)
theorem B1113385 : Blo 988596 1113385 := bbase (se 2 (by rfl) ⟨417519, by rfl⟩ : syracuseStep 1113385 = 835039) (by norm_num)
theorem B2227517 : Blo 988596 2227517 := bbase (se 3 (by rfl) ⟨417659, by rfl⟩ : syracuseStep 2227517 = 835319) (by norm_num)
theorem B1113421 : Blo 988596 1113421 := bbase (se 3 (by rfl) ⟨208766, by rfl⟩ : syracuseStep 1113421 = 417533) (by norm_num)
theorem B1113457 : Blo 988596 1113457 := bbase (se 2 (by rfl) ⟨417546, by rfl⟩ : syracuseStep 1113457 = 835093) (by norm_num)
theorem B2227589 : Blo 988596 2227589 := bbase (se 4 (by rfl) ⟨208836, by rfl⟩ : syracuseStep 2227589 = 417673) (by norm_num)
theorem B1113493 : Blo 988596 1113493 := bbase (se 6 (by rfl) ⟨26097, by rfl⟩ : syracuseStep 1113493 = 52195) (by norm_num)
theorem B1670557 : Blo 988596 1670557 := bbase (se 3 (by rfl) ⟨313229, by rfl⟩ : syracuseStep 1670557 = 626459) (by norm_num)
theorem B4750757 : Blo 988596 4750757 := bbase (se 4 (by rfl) ⟨445383, by rfl⟩ : syracuseStep 4750757 = 890767) (by norm_num)
theorem B1113529 : Blo 988596 1113529 := bbase (se 2 (by rfl) ⟨417573, by rfl⟩ : syracuseStep 1113529 = 835147) (by norm_num)
theorem B2227661 : Blo 988596 2227661 := bbase (se 3 (by rfl) ⟨417686, by rfl⟩ : syracuseStep 2227661 = 835373) (by norm_num)
theorem B16940501 : Blo 988596 16940501 := bbase (se 7 (by rfl) ⟨198521, by rfl⟩ : syracuseStep 16940501 = 397043) (by norm_num)
theorem B1113565 : Blo 988596 1113565 := bbase (se 3 (by rfl) ⟨208793, by rfl⟩ : syracuseStep 1113565 = 417587) (by norm_num)
theorem B1670645 : Blo 988596 1670645 := bbase (se 5 (by rfl) ⟨78311, by rfl⟩ : syracuseStep 1670645 = 156623) (by norm_num)
theorem B1113601 : Blo 988596 1113601 := bbase (se 2 (by rfl) ⟨417600, by rfl⟩ : syracuseStep 1113601 = 835201) (by norm_num)
theorem B5078533 : Blo 988596 5078533 := bbase (se 4 (by rfl) ⟨476112, by rfl⟩ : syracuseStep 5078533 = 952225) (by norm_num)
theorem B2227733 : Blo 988596 2227733 := bbase (se 6 (by rfl) ⟨52212, by rfl⟩ : syracuseStep 2227733 = 104425) (by norm_num)
theorem B1113637 : Blo 988596 1113637 := bbase (se 4 (by rfl) ⟨104403, by rfl⟩ : syracuseStep 1113637 = 208807) (by norm_num)
theorem B1146421 : Blo 988596 1146421 := bbase (se 5 (by rfl) ⟨53738, by rfl⟩ : syracuseStep 1146421 = 107477) (by norm_num)
theorem B1113673 : Blo 988596 1113673 := bbase (se 2 (by rfl) ⟨417627, by rfl⟩ : syracuseStep 1113673 = 835255) (by norm_num)
theorem B2227805 : Blo 988596 2227805 := bbase (se 3 (by rfl) ⟨417713, by rfl⟩ : syracuseStep 2227805 = 835427) (by norm_num)
theorem B1113709 : Blo 988596 1113709 := bbase (se 3 (by rfl) ⟨208820, by rfl⟩ : syracuseStep 1113709 = 417641) (by norm_num)
theorem B1670773 : Blo 988596 1670773 := bbase (se 5 (by rfl) ⟨78317, by rfl⟩ : syracuseStep 1670773 = 156635) (by norm_num)
theorem B1113745 : Blo 988596 1113745 := bbase (se 2 (by rfl) ⟨417654, by rfl⟩ : syracuseStep 1113745 = 835309) (by norm_num)
theorem B2227877 : Blo 988596 2227877 := bbase (se 4 (by rfl) ⟨208863, by rfl⟩ : syracuseStep 2227877 = 417727) (by norm_num)
theorem B1113781 : Blo 988596 1113781 := bbase (se 5 (by rfl) ⟨52208, by rfl⟩ : syracuseStep 1113781 = 104417) (by norm_num)
theorem B3342005 : Blo 988596 3342005 := bbase (se 5 (by rfl) ⟨156656, by rfl⟩ : syracuseStep 3342005 = 313313) (by norm_num)
theorem B1670861 : Blo 988596 1670861 := bbase (se 3 (by rfl) ⟨313286, by rfl⟩ : syracuseStep 1670861 = 626573) (by norm_num)
theorem B1113817 : Blo 988596 1113817 := bbase (se 2 (by rfl) ⟨417681, by rfl⟩ : syracuseStep 1113817 = 835363) (by norm_num)
theorem B2227949 : Blo 988596 2227949 := bbase (se 3 (by rfl) ⟨417740, by rfl⟩ : syracuseStep 2227949 = 835481) (by norm_num)
theorem B1113853 : Blo 988596 1113853 := bbase (se 3 (by rfl) ⟨208847, by rfl⟩ : syracuseStep 1113853 = 417695) (by norm_num)
theorem B1113889 : Blo 988596 1113889 := bbase (se 2 (by rfl) ⟨417708, by rfl⟩ : syracuseStep 1113889 = 835417) (by norm_num)
theorem B2228021 : Blo 988596 2228021 := bbase (se 5 (by rfl) ⟨104438, by rfl⟩ : syracuseStep 2228021 = 208877) (by norm_num)
theorem B6356789 : Blo 988596 6356789 := bbase (se 5 (by rfl) ⟨297974, by rfl⟩ : syracuseStep 6356789 = 595949) (by norm_num)
theorem B1113925 : Blo 988596 1113925 := bbase (se 4 (by rfl) ⟨104430, by rfl⟩ : syracuseStep 1113925 = 208861) (by norm_num)
theorem B1670989 : Blo 988596 1670989 := bbase (se 3 (by rfl) ⟨313310, by rfl⟩ : syracuseStep 1670989 = 626621) (by norm_num)
theorem B1408861 : Blo 988596 1408861 := bbase (se 3 (by rfl) ⟨264161, by rfl⟩ : syracuseStep 1408861 = 528323) (by norm_num)
theorem B1113961 : Blo 988596 1113961 := bbase (se 2 (by rfl) ⟨417735, by rfl⟩ : syracuseStep 1113961 = 835471) (by norm_num)
theorem B9633653 : Blo 988596 9633653 := bbase (se 5 (by rfl) ⟨451577, by rfl⟩ : syracuseStep 9633653 = 903155) (by norm_num)
theorem B2228093 : Blo 988596 2228093 := bbase (se 3 (by rfl) ⟨417767, by rfl⟩ : syracuseStep 2228093 = 835535) (by norm_num)
theorem B1113997 : Blo 988596 1113997 := bbase (se 3 (by rfl) ⟨208874, by rfl⟩ : syracuseStep 1113997 = 417749) (by norm_num)
theorem B1671077 : Blo 988596 1671077 := bbase (se 4 (by rfl) ⟨156663, by rfl⟩ : syracuseStep 1671077 = 313327) (by norm_num)
theorem B5013413 : Blo 988596 5013413 := bbase (se 4 (by rfl) ⟨470007, by rfl⟩ : syracuseStep 5013413 = 940015) (by norm_num)
theorem B1114033 : Blo 988596 1114033 := bbase (se 2 (by rfl) ⟨417762, by rfl⟩ : syracuseStep 1114033 = 835525) (by norm_num)
theorem B2228165 : Blo 988596 2228165 := bbase (se 4 (by rfl) ⟨208890, by rfl⟩ : syracuseStep 2228165 = 417781) (by norm_num)
theorem B1114069 : Blo 988596 1114069 := bbase (se 7 (by rfl) ⟨13055, by rfl⟩ : syracuseStep 1114069 = 26111) (by norm_num)
theorem B4227061 : Blo 988596 4227061 := bbase (se 5 (by rfl) ⟨198143, by rfl⟩ : syracuseStep 4227061 = 396287) (by norm_num)
theorem B1671185 : Blo 988596 1671185 := bstep (se 2 (by rfl) ⟨626694, by rfl⟩ : syracuseStep 1671185 = 1253389) B1253389
theorem B2228273 : Blo 988596 2228273 := bstep (se 2 (by rfl) ⟨835602, by rfl⟩ : syracuseStep 2228273 = 1671205) B1671205
theorem B1409089 : Blo 988596 1409089 := bstep (se 2 (by rfl) ⟨528408, by rfl⟩ : syracuseStep 1409089 = 1056817) B1056817
theorem B2228291 : Blo 988596 2228291 := bstep (se 1 (by rfl) ⟨1671218, by rfl⟩ : syracuseStep 2228291 = 3342437) B3342437
theorem B1114195 : Blo 988596 1114195 := bstep (se 1 (by rfl) ⟨835646, by rfl⟩ : syracuseStep 1114195 = 1671293) B1671293
theorem B1409123 : Blo 988596 1409123 := bstep (se 1 (by rfl) ⟨1056842, by rfl⟩ : syracuseStep 1409123 = 2113685) B2113685
theorem B1671313 : Blo 988596 1671313 := bstep (se 2 (by rfl) ⟨626742, by rfl⟩ : syracuseStep 1671313 = 1253485) B1253485
theorem B1671347 : Blo 988596 1671347 := bstep (se 1 (by rfl) ⟨1253510, by rfl⟩ : syracuseStep 1671347 = 2507021) B2507021
theorem B3342545 : Blo 988596 3342545 := bstep (se 2 (by rfl) ⟨1253454, by rfl⟩ : syracuseStep 3342545 = 2506909) B2506909
theorem B1114339 : Blo 988596 1114339 := bstep (se 1 (by rfl) ⟨835754, by rfl⟩ : syracuseStep 1114339 = 1671509) B1671509
theorem B1671475 : Blo 988596 1671475 := bstep (se 1 (by rfl) ⟨1253606, by rfl⟩ : syracuseStep 1671475 = 2507213) B2507213
theorem B2228561 : Blo 988596 2228561 := bstep (se 2 (by rfl) ⟨835710, by rfl⟩ : syracuseStep 2228561 = 1671421) B1671421
theorem B2228579 : Blo 988596 2228579 := bstep (se 1 (by rfl) ⟨1671434, by rfl⟩ : syracuseStep 2228579 = 3342869) B3342869
theorem B1114483 : Blo 988596 1114483 := bstep (se 1 (by rfl) ⟨835862, by rfl⟩ : syracuseStep 1114483 = 1671725) B1671725
theorem B5144995 : Blo 988596 5144995 := bstep (se 1 (by rfl) ⟨3858746, by rfl⟩ : syracuseStep 5144995 = 7717493) B7717493
theorem B1671617 : Blo 988596 1671617 := bstep (se 2 (by rfl) ⟨626856, by rfl⟩ : syracuseStep 1671617 = 1253713) B1253713
theorem B1114627 : Blo 988596 1114627 := bstep (se 1 (by rfl) ⟨835970, by rfl⟩ : syracuseStep 1114627 = 1671941) B1671941
theorem B2818577 : Blo 988596 2818577 := bstep (se 2 (by rfl) ⟨1056966, by rfl⟩ : syracuseStep 2818577 = 2113933) B2113933
theorem B1507889 : Blo 988596 1507889 := bstep (se 2 (by rfl) ⟨565458, by rfl⟩ : syracuseStep 1507889 = 1130917) B1130917
theorem B1671745 : Blo 988596 1671745 := bstep (se 2 (by rfl) ⟨626904, by rfl⟩ : syracuseStep 1671745 = 1253809) B1253809
theorem B1671779 : Blo 988596 1671779 := bstep (se 1 (by rfl) ⟨1253834, by rfl⟩ : syracuseStep 1671779 = 2507669) B2507669
theorem B2228849 : Blo 988596 2228849 := bstep (se 2 (by rfl) ⟨835818, by rfl⟩ : syracuseStep 2228849 = 1671637) B1671637
theorem B2228867 : Blo 988596 2228867 := bstep (se 1 (by rfl) ⟨1671650, by rfl⟩ : syracuseStep 2228867 = 3343301) B3343301
theorem B1409681 : Blo 988596 1409681 := bstep (se 2 (by rfl) ⟨528630, by rfl⟩ : syracuseStep 1409681 = 1057261) B1057261
theorem B1114771 : Blo 988596 1114771 := bstep (se 1 (by rfl) ⟨836078, by rfl⟩ : syracuseStep 1114771 = 1672157) B1672157
theorem B1409761 : Blo 988596 1409761 := bstep (se 2 (by rfl) ⟨528660, by rfl⟩ : syracuseStep 1409761 = 1057321) B1057321
theorem B1671907 : Blo 988596 1671907 := bstep (se 1 (by rfl) ⟨1253930, by rfl⟩ : syracuseStep 1671907 = 2507861) B2507861
theorem B3343085 : Blo 988596 3343085 := bstep (se 3 (by rfl) ⟨626828, by rfl⟩ : syracuseStep 3343085 = 1253657) B1253657
theorem B3343139 : Blo 988596 3343139 := bstep (se 1 (by rfl) ⟨2507354, by rfl⟩ : syracuseStep 3343139 = 5014709) B5014709
theorem B1114915 : Blo 988596 1114915 := bstep (se 1 (by rfl) ⟨836186, by rfl⟩ : syracuseStep 1114915 = 1672373) B1672373
theorem B5014385 : Blo 988596 5014385 := bstep (se 2 (by rfl) ⟨1880394, by rfl⟩ : syracuseStep 5014385 = 3760789) B3760789
theorem B1672049 : Blo 988596 1672049 := bstep (se 2 (by rfl) ⟨627018, by rfl⟩ : syracuseStep 1672049 = 1254037) B1254037
theorem B2229137 : Blo 988596 2229137 := bstep (se 2 (by rfl) ⟨835926, by rfl⟩ : syracuseStep 2229137 = 1671853) B1671853
theorem B2229155 : Blo 988596 2229155 := bstep (se 1 (by rfl) ⟨1671866, by rfl⟩ : syracuseStep 2229155 = 3343733) B3343733
theorem B1115059 : Blo 988596 1115059 := bstep (se 1 (by rfl) ⟨836294, by rfl⟩ : syracuseStep 1115059 = 1672589) B1672589
theorem B1672177 : Blo 988596 1672177 := bstep (se 2 (by rfl) ⟨627066, by rfl⟩ : syracuseStep 1672177 = 1254133) B1254133
theorem B1672211 : Blo 988596 1672211 := bstep (se 1 (by rfl) ⟨1254158, by rfl⟩ : syracuseStep 1672211 = 2508317) B2508317
theorem B3343409 : Blo 988596 3343409 := bstep (se 2 (by rfl) ⟨1253778, by rfl⟩ : syracuseStep 3343409 = 2507557) B2507557
theorem B1115203 : Blo 988596 1115203 := bstep (se 1 (by rfl) ⟨836402, by rfl⟩ : syracuseStep 1115203 = 1672805) B1672805
theorem B2262161 : Blo 988596 2262161 := bstep (se 2 (by rfl) ⟨848310, by rfl⟩ : syracuseStep 2262161 = 1696621) B1696621
theorem B1672339 : Blo 988596 1672339 := bstep (se 1 (by rfl) ⟨1254254, by rfl⟩ : syracuseStep 1672339 = 2508509) B2508509
theorem B2819249 : Blo 988596 2819249 := bstep (se 2 (by rfl) ⟨1057218, by rfl⟩ : syracuseStep 2819249 = 2114437) B2114437
theorem B2229425 : Blo 988596 2229425 := bstep (se 2 (by rfl) ⟨836034, by rfl⟩ : syracuseStep 2229425 = 1672069) B1672069
theorem B2229443 : Blo 988596 2229443 := bstep (se 1 (by rfl) ⟨1672082, by rfl⟩ : syracuseStep 2229443 = 3344165) B3344165
theorem B1115347 : Blo 988596 1115347 := bstep (se 1 (by rfl) ⟨836510, by rfl⟩ : syracuseStep 1115347 = 1673021) B1673021
theorem B6358277 : Blo 988596 6358277 := bstep (se 4 (by rfl) ⟨596088, by rfl⟩ : syracuseStep 6358277 = 1192177) B1192177
theorem B1672481 : Blo 988596 1672481 := bstep (se 2 (by rfl) ⟨627180, by rfl⟩ : syracuseStep 1672481 = 1254361) B1254361
theorem B3179857 : Blo 988596 3179857 := bstep (se 2 (by rfl) ⟨1192446, by rfl⟩ : syracuseStep 3179857 = 2384893) B2384893
theorem B1115491 : Blo 988596 1115491 := bstep (se 1 (by rfl) ⟨836618, by rfl⟩ : syracuseStep 1115491 = 1673237) B1673237
theorem B13731185 : Blo 988596 13731185 := bstep (se 2 (by rfl) ⟨5149194, by rfl⟩ : syracuseStep 13731185 = 10298389) B10298389
theorem B1672609 : Blo 988596 1672609 := bstep (se 2 (by rfl) ⟨627228, by rfl⟩ : syracuseStep 1672609 = 1254457) B1254457
theorem B5637539 : Blo 988596 5637539 := bstep (se 1 (by rfl) ⟨4228154, by rfl⟩ : syracuseStep 5637539 = 8456309) B8456309
theorem B1672643 : Blo 988596 1672643 := bstep (se 1 (by rfl) ⟨1254482, by rfl⟩ : syracuseStep 1672643 = 2508965) B2508965
theorem B2229713 : Blo 988596 2229713 := bstep (se 2 (by rfl) ⟨836142, by rfl⟩ : syracuseStep 2229713 = 1672285) B1672285
theorem B2229731 : Blo 988596 2229731 := bstep (se 1 (by rfl) ⟨1672298, by rfl⟩ : syracuseStep 2229731 = 3344597) B3344597
theorem B1410547 : Blo 988596 1410547 := bstep (se 1 (by rfl) ⟨1057910, by rfl⟩ : syracuseStep 1410547 = 2115821) B2115821
theorem B1115635 : Blo 988596 1115635 := bstep (se 1 (by rfl) ⟨836726, by rfl⟩ : syracuseStep 1115635 = 1673453) B1673453
theorem B1672771 : Blo 988596 1672771 := bstep (se 1 (by rfl) ⟨1254578, by rfl⟩ : syracuseStep 1672771 = 2509157) B2509157
theorem B3343949 : Blo 988596 3343949 := bstep (se 3 (by rfl) ⟨626990, by rfl⟩ : syracuseStep 3343949 = 1253981) B1253981
theorem B4523633 : Blo 988596 4523633 := bstep (se 2 (by rfl) ⟨1696362, by rfl⟩ : syracuseStep 4523633 = 3392725) B3392725
theorem B3344003 : Blo 988596 3344003 := bstep (se 1 (by rfl) ⟨2508002, by rfl⟩ : syracuseStep 3344003 = 5016005) B5016005
theorem B1115779 : Blo 988596 1115779 := bstep (se 1 (by rfl) ⟨836834, by rfl⟩ : syracuseStep 1115779 = 1673669) B1673669
theorem B1607347 : Blo 988596 1607347 := bstep (se 1 (by rfl) ⟨1205510, by rfl⟩ : syracuseStep 1607347 = 2411021) B2411021
theorem B1672913 : Blo 988596 1672913 := bstep (se 2 (by rfl) ⟨627342, by rfl⟩ : syracuseStep 1672913 = 1254685) B1254685
theorem B2230001 : Blo 988596 2230001 := bstep (se 2 (by rfl) ⟨836250, by rfl⟩ : syracuseStep 2230001 = 1672501) B1672501
theorem B2230019 : Blo 988596 2230019 := bstep (se 1 (by rfl) ⟨1672514, by rfl⟩ : syracuseStep 2230019 = 3345029) B3345029
theorem B1115923 : Blo 988596 1115923 := bstep (se 1 (by rfl) ⟨836942, by rfl⟩ : syracuseStep 1115923 = 1673885) B1673885
theorem B1673041 : Blo 988596 1673041 := bstep (se 2 (by rfl) ⟨627390, by rfl⟩ : syracuseStep 1673041 = 1254781) B1254781
theorem B8456035 : Blo 988596 8456035 := bstep (se 1 (by rfl) ⟨6342026, by rfl⟩ : syracuseStep 8456035 = 12684053) B12684053
theorem B1673075 : Blo 988596 1673075 := bstep (se 1 (by rfl) ⟨1254806, by rfl⟩ : syracuseStep 1673075 = 2509613) B2509613
theorem B3344273 : Blo 988596 3344273 := bstep (se 2 (by rfl) ⟨1254102, by rfl⟩ : syracuseStep 3344273 = 2508205) B2508205
theorem B1116067 : Blo 988596 1116067 := bstep (se 1 (by rfl) ⟨837050, by rfl⟩ : syracuseStep 1116067 = 1674101) B1674101
theorem B2820035 : Blo 988596 2820035 := bstep (se 1 (by rfl) ⟨2115026, by rfl⟩ : syracuseStep 2820035 = 4230053) B4230053
theorem B1411025 : Blo 988596 1411025 := bstep (se 2 (by rfl) ⟨529134, by rfl⟩ : syracuseStep 1411025 = 1058269) B1058269
theorem B1673203 : Blo 988596 1673203 := bstep (se 1 (by rfl) ⟨1254902, by rfl⟩ : syracuseStep 1673203 = 2509805) B2509805
theorem B2230289 : Blo 988596 2230289 := bstep (se 2 (by rfl) ⟨836358, by rfl⟩ : syracuseStep 2230289 = 1672717) B1672717
theorem B2230307 : Blo 988596 2230307 := bstep (se 1 (by rfl) ⟨1672730, by rfl⟩ : syracuseStep 2230307 = 3345461) B3345461
theorem B1116211 : Blo 988596 1116211 := bstep (se 1 (by rfl) ⟨837158, by rfl⟩ : syracuseStep 1116211 = 1674317) B1674317
theorem B1411139 : Blo 988596 1411139 := bstep (se 1 (by rfl) ⟨1058354, by rfl⟩ : syracuseStep 1411139 = 2116709) B2116709
theorem B1673345 : Blo 988596 1673345 := bstep (se 2 (by rfl) ⟨627504, by rfl⟩ : syracuseStep 1673345 = 1255009) B1255009
theorem B1411219 : Blo 988596 1411219 := bstep (se 1 (by rfl) ⟨1058414, by rfl⟩ : syracuseStep 1411219 = 2116829) B2116829
theorem B1116355 : Blo 988596 1116355 := bstep (se 1 (by rfl) ⟨837266, by rfl⟩ : syracuseStep 1116355 = 1674533) B1674533
theorem B3573965 : Blo 988596 3573965 := bstep (se 3 (by rfl) ⟨670118, by rfl⟩ : syracuseStep 3573965 = 1340237) B1340237
theorem B1673473 : Blo 988596 1673473 := bstep (se 2 (by rfl) ⟨627552, by rfl⟩ : syracuseStep 1673473 = 1255105) B1255105
theorem B2820365 : Blo 988596 2820365 := bstep (se 3 (by rfl) ⟨528818, by rfl⟩ : syracuseStep 2820365 = 1057637) B1057637
theorem B5015843 : Blo 988596 5015843 := bstep (se 1 (by rfl) ⟨3761882, by rfl⟩ : syracuseStep 5015843 = 7523765) B7523765
theorem B1673507 : Blo 988596 1673507 := bstep (se 1 (by rfl) ⟨1255130, by rfl⟩ : syracuseStep 1673507 = 2510261) B2510261
theorem B2230577 : Blo 988596 2230577 := bstep (se 2 (by rfl) ⟨836466, by rfl⟩ : syracuseStep 2230577 = 1672933) B1672933
theorem B2230595 : Blo 988596 2230595 := bstep (se 1 (by rfl) ⟨1672946, by rfl⟩ : syracuseStep 2230595 = 3345893) B3345893
theorem B2820433 : Blo 988596 2820433 := bstep (se 2 (by rfl) ⟨1057662, by rfl⟩ : syracuseStep 2820433 = 2115325) B2115325
theorem B1116499 : Blo 988596 1116499 := bstep (se 1 (by rfl) ⟨837374, by rfl⟩ : syracuseStep 1116499 = 1674749) B1674749
theorem B1673635 : Blo 988596 1673635 := bstep (se 1 (by rfl) ⟨1255226, by rfl⟩ : syracuseStep 1673635 = 2510453) B2510453
theorem B3344813 : Blo 988596 3344813 := bstep (se 3 (by rfl) ⟨627152, by rfl⟩ : syracuseStep 3344813 = 1254305) B1254305
theorem B61049285 : Blo 988596 61049285 := bstep (se 4 (by rfl) ⟨5723370, by rfl⟩ : syracuseStep 61049285 = 11446741) B11446741
theorem B3344867 : Blo 988596 3344867 := bstep (se 1 (by rfl) ⟨2508650, by rfl⟩ : syracuseStep 3344867 = 5017301) B5017301
theorem B1116643 : Blo 988596 1116643 := bstep (se 1 (by rfl) ⟨837482, by rfl⟩ : syracuseStep 1116643 = 1674965) B1674965
theorem B1673777 : Blo 988596 1673777 := bstep (se 2 (by rfl) ⟨627666, by rfl⟩ : syracuseStep 1673777 = 1255333) B1255333
theorem B2230865 : Blo 988596 2230865 := bstep (se 2 (by rfl) ⟨836574, by rfl⟩ : syracuseStep 2230865 = 1673149) B1673149
theorem B2820707 : Blo 988596 2820707 := bstep (se 1 (by rfl) ⟨2115530, by rfl⟩ : syracuseStep 2820707 = 4231061) B4231061
theorem B7146083 : Blo 988596 7146083 := bstep (se 1 (by rfl) ⟨5359562, by rfl⟩ : syracuseStep 7146083 = 10719125) B10719125
theorem B2230883 : Blo 988596 2230883 := bstep (se 1 (by rfl) ⟨1673162, by rfl⟩ : syracuseStep 2230883 = 3346325) B3346325
theorem B4229795 : Blo 988596 4229795 := bstep (se 1 (by rfl) ⟨3172346, by rfl⟩ : syracuseStep 4229795 = 6344693) B6344693
theorem B1673905 : Blo 988596 1673905 := bstep (se 2 (by rfl) ⟨627714, by rfl⟩ : syracuseStep 1673905 = 1255429) B1255429
theorem B1411777 : Blo 988596 1411777 := bstep (se 2 (by rfl) ⟨529416, by rfl⟩ : syracuseStep 1411777 = 1058833) B1058833
theorem B1673939 : Blo 988596 1673939 := bstep (se 1 (by rfl) ⟨1255454, by rfl⟩ : syracuseStep 1673939 = 2510909) B2510909
theorem B3345137 : Blo 988596 3345137 := bstep (se 2 (by rfl) ⟨1254426, by rfl⟩ : syracuseStep 3345137 = 2508853) B2508853
theorem B1674067 : Blo 988596 1674067 := bstep (se 1 (by rfl) ⟨1255550, by rfl⟩ : syracuseStep 1674067 = 2511101) B2511101
theorem B2231153 : Blo 988596 2231153 := bstep (se 2 (by rfl) ⟨836682, by rfl⟩ : syracuseStep 2231153 = 1673365) B1673365
theorem B2231171 : Blo 988596 2231171 := bstep (se 1 (by rfl) ⟨1673378, by rfl⟩ : syracuseStep 2231171 = 3346757) B3346757
theorem B1674209 : Blo 988596 1674209 := bstep (se 2 (by rfl) ⟨627828, by rfl⟩ : syracuseStep 1674209 = 1255657) B1255657
theorem B5016653 : Blo 988596 5016653 := bstep (se 3 (by rfl) ⟨940622, by rfl⟩ : syracuseStep 5016653 = 1881245) B1881245
theorem B1674337 : Blo 988596 1674337 := bstep (se 2 (by rfl) ⟨627876, by rfl⟩ : syracuseStep 1674337 = 1255753) B1255753
theorem B1674371 : Blo 988596 1674371 := bstep (se 1 (by rfl) ⟨1255778, by rfl⟩ : syracuseStep 1674371 = 2511557) B2511557
theorem B2231441 : Blo 988596 2231441 := bstep (se 2 (by rfl) ⟨836790, by rfl⟩ : syracuseStep 2231441 = 1673581) B1673581
theorem B3050659 : Blo 988596 3050659 := bstep (se 1 (by rfl) ⟨2287994, by rfl⟩ : syracuseStep 3050659 = 4575989) B4575989
theorem B2231459 : Blo 988596 2231459 := bstep (se 1 (by rfl) ⟨1673594, by rfl⟩ : syracuseStep 2231459 = 3347189) B3347189
theorem B3214541 : Blo 988596 3214541 := bstep (se 3 (by rfl) ⟨602726, by rfl⟩ : syracuseStep 3214541 = 1205453) B1205453
theorem B4754659 : Blo 988596 4754659 := bstep (se 1 (by rfl) ⟨3565994, by rfl⟩ : syracuseStep 4754659 = 7131989) B7131989
theorem B1674499 : Blo 988596 1674499 := bstep (se 1 (by rfl) ⟨1255874, by rfl⟩ : syracuseStep 1674499 = 2511749) B2511749
theorem B3345677 : Blo 988596 3345677 := bstep (se 3 (by rfl) ⟨627314, by rfl⟩ : syracuseStep 3345677 = 1254629) B1254629
theorem B3345731 : Blo 988596 3345731 := bstep (se 1 (by rfl) ⟨2509298, by rfl⟩ : syracuseStep 3345731 = 5018597) B5018597
theorem B2035057 : Blo 988596 2035057 := bstep (se 2 (by rfl) ⟨763146, by rfl⟩ : syracuseStep 2035057 = 1526293) B1526293
theorem B1412483 : Blo 988596 1412483 := bstep (se 1 (by rfl) ⟨1059362, by rfl⟩ : syracuseStep 1412483 = 2118725) B2118725
theorem B1674641 : Blo 988596 1674641 := bstep (se 2 (by rfl) ⟨627990, by rfl⟩ : syracuseStep 1674641 = 1255981) B1255981
theorem B2821549 : Blo 988596 2821549 := bstep (se 3 (by rfl) ⟨529040, by rfl⟩ : syracuseStep 2821549 = 1058081) B1058081
theorem B2231729 : Blo 988596 2231729 := bstep (se 2 (by rfl) ⟨836898, by rfl⟩ : syracuseStep 2231729 = 1673797) B1673797
theorem B3018161 : Blo 988596 3018161 := bstep (se 2 (by rfl) ⟨1131810, by rfl⟩ : syracuseStep 3018161 = 2263621) B2263621
theorem B2231747 : Blo 988596 2231747 := bstep (se 1 (by rfl) ⟨1673810, by rfl⟩ : syracuseStep 2231747 = 3347621) B3347621
theorem B1674769 : Blo 988596 1674769 := bstep (se 2 (by rfl) ⟨628038, by rfl⟩ : syracuseStep 1674769 = 1256077) B1256077
theorem B1674803 : Blo 988596 1674803 := bstep (se 1 (by rfl) ⟨1256102, by rfl⟩ : syracuseStep 1674803 = 2512205) B2512205
theorem B2821709 : Blo 988596 2821709 := bstep (se 3 (by rfl) ⟨529070, by rfl⟩ : syracuseStep 2821709 = 1058141) B1058141
theorem B3346001 : Blo 988596 3346001 := bstep (se 2 (by rfl) ⟨1254750, by rfl⟩ : syracuseStep 3346001 = 2509501) B2509501
theorem B1674931 : Blo 988596 1674931 := bstep (se 1 (by rfl) ⟨1256198, by rfl⟩ : syracuseStep 1674931 = 2512397) B2512397
theorem B2232017 : Blo 988596 2232017 := bstep (se 2 (by rfl) ⟨837006, by rfl⟩ : syracuseStep 2232017 = 1674013) B1674013
theorem B2232035 : Blo 988596 2232035 := bstep (se 1 (by rfl) ⟨1674026, by rfl⟩ : syracuseStep 2232035 = 3348053) B3348053
theorem B2821891 : Blo 988596 2821891 := bstep (se 1 (by rfl) ⟨2116418, by rfl⟩ : syracuseStep 2821891 = 4232837) B4232837
theorem B4231025 : Blo 988596 4231025 := bstep (se 2 (by rfl) ⟨1586634, by rfl⟩ : syracuseStep 4231025 = 3173269) B3173269
theorem B6033379 : Blo 988596 6033379 := bstep (se 1 (by rfl) ⟨4525034, by rfl⟩ : syracuseStep 6033379 = 9050069) B9050069
theorem B2232305 : Blo 988596 2232305 := bstep (se 2 (by rfl) ⟨837114, by rfl⟩ : syracuseStep 2232305 = 1674229) B1674229
theorem B1413121 : Blo 988596 1413121 := bstep (se 2 (by rfl) ⟨529920, by rfl⟩ : syracuseStep 1413121 = 1059841) B1059841
theorem B2232323 : Blo 988596 2232323 := bstep (se 1 (by rfl) ⟨1674242, by rfl⟩ : syracuseStep 2232323 = 3348485) B3348485
theorem B3346541 : Blo 988596 3346541 := bstep (se 3 (by rfl) ⟨627476, by rfl⟩ : syracuseStep 3346541 = 1254953) B1254953
theorem B1413235 : Blo 988596 1413235 := bstep (se 1 (by rfl) ⟨1059926, by rfl⟩ : syracuseStep 1413235 = 2119853) B2119853
theorem B3346595 : Blo 988596 3346595 := bstep (se 1 (by rfl) ⟨2509946, by rfl⟩ : syracuseStep 3346595 = 5019893) B5019893
theorem B6033649 : Blo 988596 6033649 := bstep (se 2 (by rfl) ⟨2262618, by rfl⟩ : syracuseStep 6033649 = 4525237) B4525237
theorem B2232593 : Blo 988596 2232593 := bstep (se 2 (by rfl) ⟨837222, by rfl⟩ : syracuseStep 2232593 = 1674445) B1674445
theorem B2232611 : Blo 988596 2232611 := bstep (se 1 (by rfl) ⟨1674458, by rfl⟩ : syracuseStep 2232611 = 3348917) B3348917
theorem B3346865 : Blo 988596 3346865 := bstep (se 2 (by rfl) ⟨1255074, by rfl⟩ : syracuseStep 3346865 = 2510149) B2510149
theorem B2232881 : Blo 988596 2232881 := bstep (se 2 (by rfl) ⟨837330, by rfl⟩ : syracuseStep 2232881 = 1674661) B1674661
theorem B2232899 : Blo 988596 2232899 := bstep (se 1 (by rfl) ⟨1674674, by rfl⟩ : syracuseStep 2232899 = 3349349) B3349349
theorem B2036305 : Blo 988596 2036305 := bstep (se 2 (by rfl) ⟨763614, by rfl⟩ : syracuseStep 2036305 = 1527229) B1527229
theorem B3576419 : Blo 988596 3576419 := bstep (se 1 (by rfl) ⟨2682314, by rfl⟩ : syracuseStep 3576419 = 5364629) B5364629
theorem B12030605 : Blo 988596 12030605 := bstep (se 3 (by rfl) ⟨2255738, by rfl⟩ : syracuseStep 12030605 = 4511477) B4511477
theorem B8033093 : Blo 988596 8033093 := bstep (se 4 (by rfl) ⟨753102, by rfl⟩ : syracuseStep 8033093 = 1506205) B1506205
theorem B2233169 : Blo 988596 2233169 := bstep (se 2 (by rfl) ⟨837438, by rfl⟩ : syracuseStep 2233169 = 1674877) B1674877
theorem B2233187 : Blo 988596 2233187 := bstep (se 1 (by rfl) ⟨1674890, by rfl⟩ : syracuseStep 2233187 = 3349781) B3349781
theorem B3347405 : Blo 988596 3347405 := bstep (se 3 (by rfl) ⟨627638, by rfl⟩ : syracuseStep 3347405 = 1255277) B1255277
theorem B3347459 : Blo 988596 3347459 := bstep (se 1 (by rfl) ⟨2510594, by rfl⟩ : syracuseStep 3347459 = 5021189) B5021189
theorem B2823281 : Blo 988596 2823281 := bstep (se 2 (by rfl) ⟨1058730, by rfl⟩ : syracuseStep 2823281 = 2117461) B2117461
theorem B4756657 : Blo 988596 4756657 := bstep (se 2 (by rfl) ⟨1783746, by rfl⟩ : syracuseStep 4756657 = 3567493) B3567493
theorem B3347729 : Blo 988596 3347729 := bstep (se 2 (by rfl) ⟨1255398, by rfl⟩ : syracuseStep 3347729 = 2510797) B2510797
theorem B988611 : Blo 988596 988611 := bstep (se 1 (by rfl) ⟨741458, by rfl⟩ : syracuseStep 988611 = 1482917) B1482917
theorem B988627 : Blo 988596 988627 := bstep (se 1 (by rfl) ⟨741470, by rfl⟩ : syracuseStep 988627 = 1482941) B1482941
theorem B988643 : Blo 988596 988643 := bstep (se 1 (by rfl) ⟨741482, by rfl⟩ : syracuseStep 988643 = 1482965) B1482965
theorem B988659 : Blo 988596 988659 := bstep (se 1 (by rfl) ⟨741494, by rfl⟩ : syracuseStep 988659 = 1482989) B1482989
theorem B988675 : Blo 988596 988675 := bstep (se 1 (by rfl) ⟨741506, by rfl⟩ : syracuseStep 988675 = 1483013) B1483013
theorem B988691 : Blo 988596 988691 := bstep (se 1 (by rfl) ⟨741518, by rfl⟩ : syracuseStep 988691 = 1483037) B1483037
theorem B988707 : Blo 988596 988707 := bstep (se 1 (by rfl) ⟨741530, by rfl⟩ : syracuseStep 988707 = 1483061) B1483061
theorem B988723 : Blo 988596 988723 := bstep (se 1 (by rfl) ⟨741542, by rfl⟩ : syracuseStep 988723 = 1483085) B1483085
theorem B988739 : Blo 988596 988739 := bstep (se 1 (by rfl) ⟨741554, by rfl⟩ : syracuseStep 988739 = 1483109) B1483109
theorem B988755 : Blo 988596 988755 := bstep (se 1 (by rfl) ⟨741566, by rfl⟩ : syracuseStep 988755 = 1483133) B1483133
theorem B988771 : Blo 988596 988771 := bstep (se 1 (by rfl) ⟨741578, by rfl⟩ : syracuseStep 988771 = 1483157) B1483157
theorem B988787 : Blo 988596 988787 := bstep (se 1 (by rfl) ⟨741590, by rfl⟩ : syracuseStep 988787 = 1483181) B1483181
theorem B988803 : Blo 988596 988803 := bstep (se 1 (by rfl) ⟨741602, by rfl⟩ : syracuseStep 988803 = 1483205) B1483205
theorem B988819 : Blo 988596 988819 := bstep (se 1 (by rfl) ⟨741614, by rfl⟩ : syracuseStep 988819 = 1483229) B1483229
theorem B988835 : Blo 988596 988835 := bstep (se 1 (by rfl) ⟨741626, by rfl⟩ : syracuseStep 988835 = 1483253) B1483253
theorem B988851 : Blo 988596 988851 := bstep (se 1 (by rfl) ⟨741638, by rfl⟩ : syracuseStep 988851 = 1483277) B1483277
theorem B12687029 : Blo 988596 12687029 := bstep (se 5 (by rfl) ⟨594704, by rfl⟩ : syracuseStep 12687029 = 1189409) B1189409
theorem B988867 : Blo 988596 988867 := bstep (se 1 (by rfl) ⟨741650, by rfl⟩ : syracuseStep 988867 = 1483301) B1483301
theorem B988883 : Blo 988596 988883 := bstep (se 1 (by rfl) ⟨741662, by rfl⟩ : syracuseStep 988883 = 1483325) B1483325
theorem B988899 : Blo 988596 988899 := bstep (se 1 (by rfl) ⟨741674, by rfl⟩ : syracuseStep 988899 = 1483349) B1483349
theorem B988915 : Blo 988596 988915 := bstep (se 1 (by rfl) ⟨741686, by rfl⟩ : syracuseStep 988915 = 1483373) B1483373
theorem B988931 : Blo 988596 988931 := bstep (se 1 (by rfl) ⟨741698, by rfl⟩ : syracuseStep 988931 = 1483397) B1483397
theorem B988947 : Blo 988596 988947 := bstep (se 1 (by rfl) ⟨741710, by rfl⟩ : syracuseStep 988947 = 1483421) B1483421
theorem B988963 : Blo 988596 988963 := bstep (se 1 (by rfl) ⟨741722, by rfl⟩ : syracuseStep 988963 = 1483445) B1483445
theorem B3348269 : Blo 988596 3348269 := bstep (se 3 (by rfl) ⟨627800, by rfl⟩ : syracuseStep 3348269 = 1255601) B1255601
theorem B988979 : Blo 988596 988979 := bstep (se 1 (by rfl) ⟨741734, by rfl⟩ : syracuseStep 988979 = 1483469) B1483469
theorem B988995 : Blo 988596 988995 := bstep (se 1 (by rfl) ⟨741746, by rfl⟩ : syracuseStep 988995 = 1483493) B1483493
theorem B989011 : Blo 988596 989011 := bstep (se 1 (by rfl) ⟨741758, by rfl⟩ : syracuseStep 989011 = 1483517) B1483517
theorem B989027 : Blo 988596 989027 := bstep (se 1 (by rfl) ⟨741770, by rfl⟩ : syracuseStep 989027 = 1483541) B1483541
theorem B3348323 : Blo 988596 3348323 := bstep (se 1 (by rfl) ⟨2511242, by rfl⟩ : syracuseStep 3348323 = 5022485) B5022485
theorem B989043 : Blo 988596 989043 := bstep (se 1 (by rfl) ⟨741782, by rfl⟩ : syracuseStep 989043 = 1483565) B1483565
theorem B989059 : Blo 988596 989059 := bstep (se 1 (by rfl) ⟨741794, by rfl⟩ : syracuseStep 989059 = 1483589) B1483589
theorem B989075 : Blo 988596 989075 := bstep (se 1 (by rfl) ⟨741806, by rfl⟩ : syracuseStep 989075 = 1483613) B1483613
theorem B1087379 : Blo 988596 1087379 := bstep (se 1 (by rfl) ⟨815534, by rfl⟩ : syracuseStep 1087379 = 1631069) B1631069
theorem B989091 : Blo 988596 989091 := bstep (se 1 (by rfl) ⟨741818, by rfl⟩ : syracuseStep 989091 = 1483637) B1483637
theorem B5019569 : Blo 988596 5019569 := bstep (se 2 (by rfl) ⟨1882338, by rfl⟩ : syracuseStep 5019569 = 3764677) B3764677
theorem B989107 : Blo 988596 989107 := bstep (se 1 (by rfl) ⟨741830, by rfl⟩ : syracuseStep 989107 = 1483661) B1483661
theorem B989123 : Blo 988596 989123 := bstep (se 1 (by rfl) ⟨741842, by rfl⟩ : syracuseStep 989123 = 1483685) B1483685
theorem B1251283 : Blo 988596 1251283 := bstep (se 1 (by rfl) ⟨938462, by rfl⟩ : syracuseStep 1251283 = 1876925) B1876925
theorem B989139 : Blo 988596 989139 := bstep (se 1 (by rfl) ⟨741854, by rfl⟩ : syracuseStep 989139 = 1483709) B1483709
theorem B989155 : Blo 988596 989155 := bstep (se 1 (by rfl) ⟨741866, by rfl⟩ : syracuseStep 989155 = 1483733) B1483733
theorem B989171 : Blo 988596 989171 := bstep (se 1 (by rfl) ⟨741878, by rfl⟩ : syracuseStep 989171 = 1483757) B1483757
theorem B989187 : Blo 988596 989187 := bstep (se 1 (by rfl) ⟨741890, by rfl⟩ : syracuseStep 989187 = 1483781) B1483781
theorem B5806093 : Blo 988596 5806093 := bstep (se 3 (by rfl) ⟨1088642, by rfl⟩ : syracuseStep 5806093 = 2177285) B2177285
theorem B989203 : Blo 988596 989203 := bstep (se 1 (by rfl) ⟨741902, by rfl⟩ : syracuseStep 989203 = 1483805) B1483805
theorem B989219 : Blo 988596 989219 := bstep (se 1 (by rfl) ⟨741914, by rfl⟩ : syracuseStep 989219 = 1483829) B1483829
theorem B2824237 : Blo 988596 2824237 := bstep (se 3 (by rfl) ⟨529544, by rfl⟩ : syracuseStep 2824237 = 1059089) B1059089
theorem B1251379 : Blo 988596 1251379 := bstep (se 1 (by rfl) ⟨938534, by rfl⟩ : syracuseStep 1251379 = 1877069) B1877069
theorem B989235 : Blo 988596 989235 := bstep (se 1 (by rfl) ⟨741926, by rfl⟩ : syracuseStep 989235 = 1483853) B1483853
theorem B989251 : Blo 988596 989251 := bstep (se 1 (by rfl) ⟨741938, by rfl⟩ : syracuseStep 989251 = 1483877) B1483877
theorem B989267 : Blo 988596 989267 := bstep (se 1 (by rfl) ⟨741950, by rfl⟩ : syracuseStep 989267 = 1483901) B1483901
theorem B989283 : Blo 988596 989283 := bstep (se 1 (by rfl) ⟨741962, by rfl⟩ : syracuseStep 989283 = 1483925) B1483925
theorem B3348593 : Blo 988596 3348593 := bstep (se 2 (by rfl) ⟨1255722, by rfl⟩ : syracuseStep 3348593 = 2511445) B2511445
theorem B989299 : Blo 988596 989299 := bstep (se 1 (by rfl) ⟨741974, by rfl⟩ : syracuseStep 989299 = 1483949) B1483949
theorem B989315 : Blo 988596 989315 := bstep (se 1 (by rfl) ⟨741986, by rfl⟩ : syracuseStep 989315 = 1483973) B1483973
theorem B7510157 : Blo 988596 7510157 := bstep (se 3 (by rfl) ⟨1408154, by rfl⟩ : syracuseStep 7510157 = 2816309) B2816309
theorem B989331 : Blo 988596 989331 := bstep (se 1 (by rfl) ⟨741998, by rfl⟩ : syracuseStep 989331 = 1483997) B1483997
theorem B989347 : Blo 988596 989347 := bstep (se 1 (by rfl) ⟨742010, by rfl⟩ : syracuseStep 989347 = 1484021) B1484021
theorem B989363 : Blo 988596 989363 := bstep (se 1 (by rfl) ⟨742022, by rfl⟩ : syracuseStep 989363 = 1484045) B1484045
theorem B989379 : Blo 988596 989379 := bstep (se 1 (by rfl) ⟨742034, by rfl⟩ : syracuseStep 989379 = 1484069) B1484069
theorem B989395 : Blo 988596 989395 := bstep (se 1 (by rfl) ⟨742046, by rfl⟩ : syracuseStep 989395 = 1484093) B1484093
theorem B989411 : Blo 988596 989411 := bstep (se 1 (by rfl) ⟨742058, by rfl⟩ : syracuseStep 989411 = 1484117) B1484117
theorem B989427 : Blo 988596 989427 := bstep (se 1 (by rfl) ⟨742070, by rfl⟩ : syracuseStep 989427 = 1484141) B1484141
theorem B989443 : Blo 988596 989443 := bstep (se 1 (by rfl) ⟨742082, by rfl⟩ : syracuseStep 989443 = 1484165) B1484165
theorem B4233485 : Blo 988596 4233485 := bstep (se 3 (by rfl) ⟨793778, by rfl⟩ : syracuseStep 4233485 = 1587557) B1587557
theorem B2824465 : Blo 988596 2824465 := bstep (se 2 (by rfl) ⟨1059174, by rfl⟩ : syracuseStep 2824465 = 2118349) B2118349
theorem B989459 : Blo 988596 989459 := bstep (se 1 (by rfl) ⟨742094, by rfl⟩ : syracuseStep 989459 = 1484189) B1484189
theorem B989475 : Blo 988596 989475 := bstep (se 1 (by rfl) ⟨742106, by rfl⟩ : syracuseStep 989475 = 1484213) B1484213
theorem B989491 : Blo 988596 989491 := bstep (se 1 (by rfl) ⟨742118, by rfl⟩ : syracuseStep 989491 = 1484237) B1484237
theorem B989507 : Blo 988596 989507 := bstep (se 1 (by rfl) ⟨742130, by rfl⟩ : syracuseStep 989507 = 1484261) B1484261
theorem B989523 : Blo 988596 989523 := bstep (se 1 (by rfl) ⟨742142, by rfl⟩ : syracuseStep 989523 = 1484285) B1484285
theorem B989539 : Blo 988596 989539 := bstep (se 1 (by rfl) ⟨742154, by rfl⟩ : syracuseStep 989539 = 1484309) B1484309
theorem B989555 : Blo 988596 989555 := bstep (se 1 (by rfl) ⟨742166, by rfl⟩ : syracuseStep 989555 = 1484333) B1484333
theorem B989571 : Blo 988596 989571 := bstep (se 1 (by rfl) ⟨742178, by rfl⟩ : syracuseStep 989571 = 1484357) B1484357
theorem B989587 : Blo 988596 989587 := bstep (se 1 (by rfl) ⟨742190, by rfl⟩ : syracuseStep 989587 = 1484381) B1484381
theorem B989603 : Blo 988596 989603 := bstep (se 1 (by rfl) ⟨742202, by rfl⟩ : syracuseStep 989603 = 1484405) B1484405
theorem B2824625 : Blo 988596 2824625 := bstep (se 2 (by rfl) ⟨1059234, by rfl⟩ : syracuseStep 2824625 = 2118469) B2118469
theorem B989619 : Blo 988596 989619 := bstep (se 1 (by rfl) ⟨742214, by rfl⟩ : syracuseStep 989619 = 1484429) B1484429
theorem B989635 : Blo 988596 989635 := bstep (se 1 (by rfl) ⟨742226, by rfl⟩ : syracuseStep 989635 = 1484453) B1484453
theorem B5347781 : Blo 988596 5347781 := bstep (se 4 (by rfl) ⟨501354, by rfl⟩ : syracuseStep 5347781 = 1002709) B1002709
theorem B989651 : Blo 988596 989651 := bstep (se 1 (by rfl) ⟨742238, by rfl⟩ : syracuseStep 989651 = 1484477) B1484477
theorem B989667 : Blo 988596 989667 := bstep (se 1 (by rfl) ⟨742250, by rfl⟩ : syracuseStep 989667 = 1484501) B1484501
theorem B989683 : Blo 988596 989683 := bstep (se 1 (by rfl) ⟨742262, by rfl⟩ : syracuseStep 989683 = 1484525) B1484525
theorem B989699 : Blo 988596 989699 := bstep (se 1 (by rfl) ⟨742274, by rfl⟩ : syracuseStep 989699 = 1484549) B1484549
theorem B989715 : Blo 988596 989715 := bstep (se 1 (by rfl) ⟨742286, by rfl⟩ : syracuseStep 989715 = 1484573) B1484573
theorem B1251875 : Blo 988596 1251875 := bstep (se 1 (by rfl) ⟨938906, by rfl⟩ : syracuseStep 1251875 = 1877813) B1877813
theorem B989731 : Blo 988596 989731 := bstep (se 1 (by rfl) ⟨742298, by rfl⟩ : syracuseStep 989731 = 1484597) B1484597
theorem B2824739 : Blo 988596 2824739 := bstep (se 1 (by rfl) ⟨2118554, by rfl⟩ : syracuseStep 2824739 = 4237109) B4237109
theorem B5347889 : Blo 988596 5347889 := bstep (se 2 (by rfl) ⟨2005458, by rfl⟩ : syracuseStep 5347889 = 4010917) B4010917
theorem B989747 : Blo 988596 989747 := bstep (se 1 (by rfl) ⟨742310, by rfl⟩ : syracuseStep 989747 = 1484621) B1484621
theorem B989763 : Blo 988596 989763 := bstep (se 1 (by rfl) ⟨742322, by rfl⟩ : syracuseStep 989763 = 1484645) B1484645
theorem B989779 : Blo 988596 989779 := bstep (se 1 (by rfl) ⟨742334, by rfl⟩ : syracuseStep 989779 = 1484669) B1484669
theorem B989795 : Blo 988596 989795 := bstep (se 1 (by rfl) ⟨742346, by rfl⟩ : syracuseStep 989795 = 1484693) B1484693
theorem B989811 : Blo 988596 989811 := bstep (se 1 (by rfl) ⟨742358, by rfl⟩ : syracuseStep 989811 = 1484717) B1484717
theorem B989827 : Blo 988596 989827 := bstep (se 1 (by rfl) ⟨742370, by rfl⟩ : syracuseStep 989827 = 1484741) B1484741
theorem B3349133 : Blo 988596 3349133 := bstep (se 3 (by rfl) ⟨627962, by rfl⟩ : syracuseStep 3349133 = 1255925) B1255925
theorem B989843 : Blo 988596 989843 := bstep (se 1 (by rfl) ⟨742382, by rfl⟩ : syracuseStep 989843 = 1484765) B1484765
theorem B989859 : Blo 988596 989859 := bstep (se 1 (by rfl) ⟨742394, by rfl⟩ : syracuseStep 989859 = 1484789) B1484789
theorem B989875 : Blo 988596 989875 := bstep (se 1 (by rfl) ⟨742406, by rfl⟩ : syracuseStep 989875 = 1484813) B1484813
theorem B989891 : Blo 988596 989891 := bstep (se 1 (by rfl) ⟨742418, by rfl⟩ : syracuseStep 989891 = 1484837) B1484837
theorem B3349187 : Blo 988596 3349187 := bstep (se 1 (by rfl) ⟨2511890, by rfl⟩ : syracuseStep 3349187 = 5023781) B5023781
theorem B989907 : Blo 988596 989907 := bstep (se 1 (by rfl) ⟨742430, by rfl⟩ : syracuseStep 989907 = 1484861) B1484861
theorem B989923 : Blo 988596 989923 := bstep (se 1 (by rfl) ⟨742442, by rfl⟩ : syracuseStep 989923 = 1484885) B1484885
theorem B989939 : Blo 988596 989939 := bstep (se 1 (by rfl) ⟨742454, by rfl⟩ : syracuseStep 989939 = 1484909) B1484909
theorem B989955 : Blo 988596 989955 := bstep (se 1 (by rfl) ⟨742466, by rfl⟩ : syracuseStep 989955 = 1484933) B1484933
theorem B989971 : Blo 988596 989971 := bstep (se 1 (by rfl) ⟨742478, by rfl⟩ : syracuseStep 989971 = 1484957) B1484957
theorem B989987 : Blo 988596 989987 := bstep (se 1 (by rfl) ⟨742490, by rfl⟩ : syracuseStep 989987 = 1484981) B1484981
theorem B990003 : Blo 988596 990003 := bstep (se 1 (by rfl) ⟨742502, by rfl⟩ : syracuseStep 990003 = 1485005) B1485005
theorem B990019 : Blo 988596 990019 := bstep (se 1 (by rfl) ⟨742514, by rfl⟩ : syracuseStep 990019 = 1485029) B1485029
theorem B990035 : Blo 988596 990035 := bstep (se 1 (by rfl) ⟨742526, by rfl⟩ : syracuseStep 990035 = 1485053) B1485053
theorem B990051 : Blo 988596 990051 := bstep (se 1 (by rfl) ⟨742538, by rfl⟩ : syracuseStep 990051 = 1485077) B1485077
theorem B990067 : Blo 988596 990067 := bstep (se 1 (by rfl) ⟨742550, by rfl⟩ : syracuseStep 990067 = 1485101) B1485101
theorem B990083 : Blo 988596 990083 := bstep (se 1 (by rfl) ⟨742562, by rfl⟩ : syracuseStep 990083 = 1485125) B1485125
theorem B990099 : Blo 988596 990099 := bstep (se 1 (by rfl) ⟨742574, by rfl⟩ : syracuseStep 990099 = 1485149) B1485149
theorem B990115 : Blo 988596 990115 := bstep (se 1 (by rfl) ⟨742586, by rfl⟩ : syracuseStep 990115 = 1485173) B1485173
theorem B990131 : Blo 988596 990131 := bstep (se 1 (by rfl) ⟨742598, by rfl⟩ : syracuseStep 990131 = 1485197) B1485197
theorem B990147 : Blo 988596 990147 := bstep (se 1 (by rfl) ⟨742610, by rfl⟩ : syracuseStep 990147 = 1485221) B1485221
theorem B3349457 : Blo 988596 3349457 := bstep (se 2 (by rfl) ⟨1256046, by rfl⟩ : syracuseStep 3349457 = 2512093) B2512093
theorem B990163 : Blo 988596 990163 := bstep (se 1 (by rfl) ⟨742622, by rfl⟩ : syracuseStep 990163 = 1485245) B1485245
theorem B990179 : Blo 988596 990179 := bstep (se 1 (by rfl) ⟨742634, by rfl⟩ : syracuseStep 990179 = 1485269) B1485269
theorem B990195 : Blo 988596 990195 := bstep (se 1 (by rfl) ⟨742646, by rfl⟩ : syracuseStep 990195 = 1485293) B1485293
theorem B990211 : Blo 988596 990211 := bstep (se 1 (by rfl) ⟨742658, by rfl⟩ : syracuseStep 990211 = 1485317) B1485317
theorem B990227 : Blo 988596 990227 := bstep (se 1 (by rfl) ⟨742670, by rfl⟩ : syracuseStep 990227 = 1485341) B1485341
theorem B990243 : Blo 988596 990243 := bstep (se 1 (by rfl) ⟨742682, by rfl⟩ : syracuseStep 990243 = 1485365) B1485365
theorem B990259 : Blo 988596 990259 := bstep (se 1 (by rfl) ⟨742694, by rfl⟩ : syracuseStep 990259 = 1485389) B1485389
theorem B990275 : Blo 988596 990275 := bstep (se 1 (by rfl) ⟨742706, by rfl⟩ : syracuseStep 990275 = 1485413) B1485413
theorem B990291 : Blo 988596 990291 := bstep (se 1 (by rfl) ⟨742718, by rfl⟩ : syracuseStep 990291 = 1485437) B1485437
theorem B990307 : Blo 988596 990307 := bstep (se 1 (by rfl) ⟨742730, by rfl⟩ : syracuseStep 990307 = 1485461) B1485461
theorem B990323 : Blo 988596 990323 := bstep (se 1 (by rfl) ⟨742742, by rfl⟩ : syracuseStep 990323 = 1485485) B1485485
theorem B990339 : Blo 988596 990339 := bstep (se 1 (by rfl) ⟨742754, by rfl⟩ : syracuseStep 990339 = 1485509) B1485509
theorem B990355 : Blo 988596 990355 := bstep (se 1 (by rfl) ⟨742766, by rfl⟩ : syracuseStep 990355 = 1485533) B1485533
theorem B990371 : Blo 988596 990371 := bstep (se 1 (by rfl) ⟨742778, by rfl⟩ : syracuseStep 990371 = 1485557) B1485557
theorem B990387 : Blo 988596 990387 := bstep (se 1 (by rfl) ⟨742790, by rfl⟩ : syracuseStep 990387 = 1485581) B1485581
theorem B990403 : Blo 988596 990403 := bstep (se 1 (by rfl) ⟨742802, by rfl⟩ : syracuseStep 990403 = 1485605) B1485605
theorem B990419 : Blo 988596 990419 := bstep (se 1 (by rfl) ⟨742814, by rfl⟩ : syracuseStep 990419 = 1485629) B1485629
theorem B1252579 : Blo 988596 1252579 := bstep (se 1 (by rfl) ⟨939434, by rfl⟩ : syracuseStep 1252579 = 1878869) B1878869
theorem B990435 : Blo 988596 990435 := bstep (se 1 (by rfl) ⟨742826, by rfl⟩ : syracuseStep 990435 = 1485653) B1485653
theorem B990451 : Blo 988596 990451 := bstep (se 1 (by rfl) ⟨742838, by rfl⟩ : syracuseStep 990451 = 1485677) B1485677
theorem B2858243 : Blo 988596 2858243 := bstep (se 1 (by rfl) ⟨2143682, by rfl⟩ : syracuseStep 2858243 = 4287365) B4287365
theorem B990467 : Blo 988596 990467 := bstep (se 1 (by rfl) ⟨742850, by rfl⟩ : syracuseStep 990467 = 1485701) B1485701
theorem B990483 : Blo 988596 990483 := bstep (se 1 (by rfl) ⟨742862, by rfl⟩ : syracuseStep 990483 = 1485725) B1485725
theorem B990499 : Blo 988596 990499 := bstep (se 1 (by rfl) ⟨742874, by rfl⟩ : syracuseStep 990499 = 1485749) B1485749
theorem B990515 : Blo 988596 990515 := bstep (se 1 (by rfl) ⟨742886, by rfl⟩ : syracuseStep 990515 = 1485773) B1485773
theorem B1252675 : Blo 988596 1252675 := bstep (se 1 (by rfl) ⟨939506, by rfl⟩ : syracuseStep 1252675 = 1879013) B1879013
theorem B990531 : Blo 988596 990531 := bstep (se 1 (by rfl) ⟨742898, by rfl⟩ : syracuseStep 990531 = 1485797) B1485797
theorem B990547 : Blo 988596 990547 := bstep (se 1 (by rfl) ⟨742910, by rfl⟩ : syracuseStep 990547 = 1485821) B1485821
theorem B990563 : Blo 988596 990563 := bstep (se 1 (by rfl) ⟨742922, by rfl⟩ : syracuseStep 990563 = 1485845) B1485845
theorem B5021027 : Blo 988596 5021027 := bstep (se 1 (by rfl) ⟨3765770, by rfl⟩ : syracuseStep 5021027 = 7531541) B7531541
theorem B990579 : Blo 988596 990579 := bstep (se 1 (by rfl) ⟨742934, by rfl⟩ : syracuseStep 990579 = 1485869) B1485869
theorem B990595 : Blo 988596 990595 := bstep (se 1 (by rfl) ⟨742946, by rfl⟩ : syracuseStep 990595 = 1485893) B1485893
theorem B990611 : Blo 988596 990611 := bstep (se 1 (by rfl) ⟨742958, by rfl⟩ : syracuseStep 990611 = 1485917) B1485917
theorem B990627 : Blo 988596 990627 := bstep (se 1 (by rfl) ⟨742970, by rfl⟩ : syracuseStep 990627 = 1485941) B1485941
theorem B990643 : Blo 988596 990643 := bstep (se 1 (by rfl) ⟨742982, by rfl⟩ : syracuseStep 990643 = 1485965) B1485965
theorem B990659 : Blo 988596 990659 := bstep (se 1 (by rfl) ⟨742994, by rfl⟩ : syracuseStep 990659 = 1485989) B1485989
theorem B990675 : Blo 988596 990675 := bstep (se 1 (by rfl) ⟨743006, by rfl⟩ : syracuseStep 990675 = 1486013) B1486013
theorem B990691 : Blo 988596 990691 := bstep (se 1 (by rfl) ⟨743018, by rfl⟩ : syracuseStep 990691 = 1486037) B1486037
theorem B3349997 : Blo 988596 3349997 := bstep (se 3 (by rfl) ⟨628124, by rfl⟩ : syracuseStep 3349997 = 1256249) B1256249
theorem B990707 : Blo 988596 990707 := bstep (se 1 (by rfl) ⟨743030, by rfl⟩ : syracuseStep 990707 = 1486061) B1486061
theorem B990723 : Blo 988596 990723 := bstep (se 1 (by rfl) ⟨743042, by rfl⟩ : syracuseStep 990723 = 1486085) B1486085
theorem B2825741 : Blo 988596 2825741 := bstep (se 3 (by rfl) ⟨529826, by rfl⟩ : syracuseStep 2825741 = 1059653) B1059653
theorem B990739 : Blo 988596 990739 := bstep (se 1 (by rfl) ⟨743054, by rfl⟩ : syracuseStep 990739 = 1486109) B1486109
theorem B990755 : Blo 988596 990755 := bstep (se 1 (by rfl) ⟨743066, by rfl⟩ : syracuseStep 990755 = 1486133) B1486133
theorem B990771 : Blo 988596 990771 := bstep (se 1 (by rfl) ⟨743078, by rfl⟩ : syracuseStep 990771 = 1486157) B1486157
theorem B990787 : Blo 988596 990787 := bstep (se 1 (by rfl) ⟨743090, by rfl⟩ : syracuseStep 990787 = 1486181) B1486181
theorem B990803 : Blo 988596 990803 := bstep (se 1 (by rfl) ⟨743102, by rfl⟩ : syracuseStep 990803 = 1486205) B1486205
theorem B990819 : Blo 988596 990819 := bstep (se 1 (by rfl) ⟨743114, by rfl⟩ : syracuseStep 990819 = 1486229) B1486229
theorem B990835 : Blo 988596 990835 := bstep (se 1 (by rfl) ⟨743126, by rfl⟩ : syracuseStep 990835 = 1486253) B1486253
theorem B990851 : Blo 988596 990851 := bstep (se 1 (by rfl) ⟨743138, by rfl⟩ : syracuseStep 990851 = 1486277) B1486277
theorem B990867 : Blo 988596 990867 := bstep (se 1 (by rfl) ⟨743150, by rfl⟩ : syracuseStep 990867 = 1486301) B1486301
theorem B990883 : Blo 988596 990883 := bstep (se 1 (by rfl) ⟨743162, by rfl⟩ : syracuseStep 990883 = 1486325) B1486325
theorem B990899 : Blo 988596 990899 := bstep (se 1 (by rfl) ⟨743174, by rfl⟩ : syracuseStep 990899 = 1486349) B1486349
theorem B990915 : Blo 988596 990915 := bstep (se 1 (by rfl) ⟨743186, by rfl⟩ : syracuseStep 990915 = 1486373) B1486373
theorem B2825923 : Blo 988596 2825923 := bstep (se 1 (by rfl) ⟨2119442, by rfl⟩ : syracuseStep 2825923 = 4238885) B4238885
theorem B990931 : Blo 988596 990931 := bstep (se 1 (by rfl) ⟨743198, by rfl⟩ : syracuseStep 990931 = 1486397) B1486397
theorem B990947 : Blo 988596 990947 := bstep (se 1 (by rfl) ⟨743210, by rfl⟩ : syracuseStep 990947 = 1486421) B1486421
theorem B990963 : Blo 988596 990963 := bstep (se 1 (by rfl) ⟨743222, by rfl⟩ : syracuseStep 990963 = 1486445) B1486445
theorem B990979 : Blo 988596 990979 := bstep (se 1 (by rfl) ⟨743234, by rfl⟩ : syracuseStep 990979 = 1486469) B1486469
theorem B2039555 : Blo 988596 2039555 := bstep (se 1 (by rfl) ⟨1529666, by rfl⟩ : syracuseStep 2039555 = 3059333) B3059333
theorem B990995 : Blo 988596 990995 := bstep (se 1 (by rfl) ⟨743246, by rfl⟩ : syracuseStep 990995 = 1486493) B1486493
theorem B991011 : Blo 988596 991011 := bstep (se 1 (by rfl) ⟨743258, by rfl⟩ : syracuseStep 991011 = 1486517) B1486517
theorem B1253171 : Blo 988596 1253171 := bstep (se 1 (by rfl) ⟨939878, by rfl⟩ : syracuseStep 1253171 = 1879757) B1879757
theorem B991027 : Blo 988596 991027 := bstep (se 1 (by rfl) ⟨743270, by rfl⟩ : syracuseStep 991027 = 1486541) B1486541
theorem B991043 : Blo 988596 991043 := bstep (se 1 (by rfl) ⟨743282, by rfl⟩ : syracuseStep 991043 = 1486565) B1486565
theorem B5087053 : Blo 988596 5087053 := bstep (se 3 (by rfl) ⟨953822, by rfl⟩ : syracuseStep 5087053 = 1907645) B1907645
theorem B991059 : Blo 988596 991059 := bstep (se 1 (by rfl) ⟨743294, by rfl⟩ : syracuseStep 991059 = 1486589) B1486589
theorem B991075 : Blo 988596 991075 := bstep (se 1 (by rfl) ⟨743306, by rfl⟩ : syracuseStep 991075 = 1486613) B1486613
theorem B2826083 : Blo 988596 2826083 := bstep (se 1 (by rfl) ⟨2119562, by rfl⟩ : syracuseStep 2826083 = 4239125) B4239125
theorem B991091 : Blo 988596 991091 := bstep (se 1 (by rfl) ⟨743318, by rfl⟩ : syracuseStep 991091 = 1486637) B1486637
theorem B991107 : Blo 988596 991107 := bstep (se 1 (by rfl) ⟨743330, by rfl⟩ : syracuseStep 991107 = 1486661) B1486661
theorem B991123 : Blo 988596 991123 := bstep (se 1 (by rfl) ⟨743342, by rfl⟩ : syracuseStep 991123 = 1486685) B1486685
theorem B991139 : Blo 988596 991139 := bstep (se 1 (by rfl) ⟨743354, by rfl⟩ : syracuseStep 991139 = 1486709) B1486709
theorem B991155 : Blo 988596 991155 := bstep (se 1 (by rfl) ⟨743366, by rfl⟩ : syracuseStep 991155 = 1486733) B1486733
theorem B991171 : Blo 988596 991171 := bstep (se 1 (by rfl) ⟨743378, by rfl⟩ : syracuseStep 991171 = 1486757) B1486757
theorem B991187 : Blo 988596 991187 := bstep (se 1 (by rfl) ⟨743390, by rfl⟩ : syracuseStep 991187 = 1486781) B1486781
theorem B991203 : Blo 988596 991203 := bstep (se 1 (by rfl) ⟨743402, by rfl⟩ : syracuseStep 991203 = 1486805) B1486805
theorem B9052145 : Blo 988596 9052145 := bstep (se 2 (by rfl) ⟨3394554, by rfl⟩ : syracuseStep 9052145 = 6789109) B6789109
theorem B991219 : Blo 988596 991219 := bstep (se 1 (by rfl) ⟨743414, by rfl⟩ : syracuseStep 991219 = 1486829) B1486829
theorem B991235 : Blo 988596 991235 := bstep (se 1 (by rfl) ⟨743426, by rfl⟩ : syracuseStep 991235 = 1486853) B1486853
theorem B991251 : Blo 988596 991251 := bstep (se 1 (by rfl) ⟨743438, by rfl⟩ : syracuseStep 991251 = 1486877) B1486877
theorem B991267 : Blo 988596 991267 := bstep (se 1 (by rfl) ⟨743450, by rfl⟩ : syracuseStep 991267 = 1486901) B1486901
theorem B991283 : Blo 988596 991283 := bstep (se 1 (by rfl) ⟨743462, by rfl⟩ : syracuseStep 991283 = 1486925) B1486925
theorem B991299 : Blo 988596 991299 := bstep (se 1 (by rfl) ⟨743474, by rfl⟩ : syracuseStep 991299 = 1486949) B1486949
theorem B991315 : Blo 988596 991315 := bstep (se 1 (by rfl) ⟨743486, by rfl⟩ : syracuseStep 991315 = 1486973) B1486973
theorem B991331 : Blo 988596 991331 := bstep (se 1 (by rfl) ⟨743498, by rfl⟩ : syracuseStep 991331 = 1486997) B1486997
theorem B991347 : Blo 988596 991347 := bstep (se 1 (by rfl) ⟨743510, by rfl⟩ : syracuseStep 991347 = 1487021) B1487021
theorem B991363 : Blo 988596 991363 := bstep (se 1 (by rfl) ⟨743522, by rfl⟩ : syracuseStep 991363 = 1487045) B1487045
theorem B5021837 : Blo 988596 5021837 := bstep (se 3 (by rfl) ⟨941594, by rfl⟩ : syracuseStep 5021837 = 1883189) B1883189
theorem B1482899 : Blo 988596 1482899 := bstep (se 1 (by rfl) ⟨1112174, by rfl⟩ : syracuseStep 1482899 = 2224349) B2224349
theorem B991379 : Blo 988596 991379 := bstep (se 1 (by rfl) ⟨743534, by rfl⟩ : syracuseStep 991379 = 1487069) B1487069
theorem B991395 : Blo 988596 991395 := bstep (se 1 (by rfl) ⟨743546, by rfl⟩ : syracuseStep 991395 = 1487093) B1487093
theorem B1482929 : Blo 988596 1482929 := bstep (se 2 (by rfl) ⟨556098, by rfl⟩ : syracuseStep 1482929 = 1112197) B1112197
theorem B991411 : Blo 988596 991411 := bstep (se 1 (by rfl) ⟨743558, by rfl⟩ : syracuseStep 991411 = 1487117) B1487117
theorem B1482947 : Blo 988596 1482947 := bstep (se 1 (by rfl) ⟨1112210, by rfl⟩ : syracuseStep 1482947 = 2224421) B2224421
theorem B991427 : Blo 988596 991427 := bstep (se 1 (by rfl) ⟨743570, by rfl⟩ : syracuseStep 991427 = 1487141) B1487141
theorem B1056979 : Blo 988596 1056979 := bstep (se 1 (by rfl) ⟨792734, by rfl⟩ : syracuseStep 1056979 = 1585469) B1585469
theorem B991443 : Blo 988596 991443 := bstep (se 1 (by rfl) ⟨743582, by rfl⟩ : syracuseStep 991443 = 1487165) B1487165
theorem B1482977 : Blo 988596 1482977 := bstep (se 2 (by rfl) ⟨556116, by rfl⟩ : syracuseStep 1482977 = 1112233) B1112233
theorem B991459 : Blo 988596 991459 := bstep (se 1 (by rfl) ⟨743594, by rfl⟩ : syracuseStep 991459 = 1487189) B1487189
theorem B1482995 : Blo 988596 1482995 := bstep (se 1 (by rfl) ⟨1112246, by rfl⟩ : syracuseStep 1482995 = 2224493) B2224493
theorem B991475 : Blo 988596 991475 := bstep (se 1 (by rfl) ⟨743606, by rfl⟩ : syracuseStep 991475 = 1487213) B1487213
theorem B991491 : Blo 988596 991491 := bstep (se 1 (by rfl) ⟨743618, by rfl⟩ : syracuseStep 991491 = 1487237) B1487237
theorem B1483025 : Blo 988596 1483025 := bstep (se 2 (by rfl) ⟨556134, by rfl⟩ : syracuseStep 1483025 = 1112269) B1112269
theorem B991507 : Blo 988596 991507 := bstep (se 1 (by rfl) ⟨743630, by rfl⟩ : syracuseStep 991507 = 1487261) B1487261
theorem B1483043 : Blo 988596 1483043 := bstep (se 1 (by rfl) ⟨1112282, by rfl⟩ : syracuseStep 1483043 = 2224565) B2224565
theorem B991523 : Blo 988596 991523 := bstep (se 1 (by rfl) ⟨743642, by rfl⟩ : syracuseStep 991523 = 1487285) B1487285
theorem B991539 : Blo 988596 991539 := bstep (se 1 (by rfl) ⟨743654, by rfl⟩ : syracuseStep 991539 = 1487309) B1487309
theorem B1483073 : Blo 988596 1483073 := bstep (se 2 (by rfl) ⟨556152, by rfl⟩ : syracuseStep 1483073 = 1112305) B1112305
theorem B991555 : Blo 988596 991555 := bstep (se 1 (by rfl) ⟨743666, by rfl⟩ : syracuseStep 991555 = 1487333) B1487333
theorem B1483091 : Blo 988596 1483091 := bstep (se 1 (by rfl) ⟨1112318, by rfl⟩ : syracuseStep 1483091 = 2224637) B2224637
theorem B991571 : Blo 988596 991571 := bstep (se 1 (by rfl) ⟨743678, by rfl⟩ : syracuseStep 991571 = 1487357) B1487357
theorem B991587 : Blo 988596 991587 := bstep (se 1 (by rfl) ⟨743690, by rfl⟩ : syracuseStep 991587 = 1487381) B1487381
theorem B1483121 : Blo 988596 1483121 := bstep (se 2 (by rfl) ⟨556170, by rfl⟩ : syracuseStep 1483121 = 1112341) B1112341
theorem B991603 : Blo 988596 991603 := bstep (se 1 (by rfl) ⟨743702, by rfl⟩ : syracuseStep 991603 = 1487405) B1487405
theorem B1483139 : Blo 988596 1483139 := bstep (se 1 (by rfl) ⟨1112354, by rfl⟩ : syracuseStep 1483139 = 2224709) B2224709
theorem B991619 : Blo 988596 991619 := bstep (se 1 (by rfl) ⟨743714, by rfl⟩ : syracuseStep 991619 = 1487429) B1487429
theorem B991635 : Blo 988596 991635 := bstep (se 1 (by rfl) ⟨743726, by rfl⟩ : syracuseStep 991635 = 1487453) B1487453
theorem B1483169 : Blo 988596 1483169 := bstep (se 2 (by rfl) ⟨556188, by rfl⟩ : syracuseStep 1483169 = 1112377) B1112377
theorem B991651 : Blo 988596 991651 := bstep (se 1 (by rfl) ⟨743738, by rfl⟩ : syracuseStep 991651 = 1487477) B1487477
theorem B1483187 : Blo 988596 1483187 := bstep (se 1 (by rfl) ⟨1112390, by rfl⟩ : syracuseStep 1483187 = 2224781) B2224781
theorem B991667 : Blo 988596 991667 := bstep (se 1 (by rfl) ⟨743750, by rfl⟩ : syracuseStep 991667 = 1487501) B1487501
theorem B991683 : Blo 988596 991683 := bstep (se 1 (by rfl) ⟨743762, by rfl⟩ : syracuseStep 991683 = 1487525) B1487525
theorem B1483217 : Blo 988596 1483217 := bstep (se 2 (by rfl) ⟨556206, by rfl⟩ : syracuseStep 1483217 = 1112413) B1112413
theorem B991699 : Blo 988596 991699 := bstep (se 1 (by rfl) ⟨743774, by rfl⟩ : syracuseStep 991699 = 1487549) B1487549
theorem B1483235 : Blo 988596 1483235 := bstep (se 1 (by rfl) ⟨1112426, by rfl⟩ : syracuseStep 1483235 = 2224853) B2224853
theorem B991715 : Blo 988596 991715 := bstep (se 1 (by rfl) ⟨743786, by rfl⟩ : syracuseStep 991715 = 1487573) B1487573
theorem B1253875 : Blo 988596 1253875 := bstep (se 1 (by rfl) ⟨940406, by rfl⟩ : syracuseStep 1253875 = 1880813) B1880813
theorem B991731 : Blo 988596 991731 := bstep (se 1 (by rfl) ⟨743798, by rfl⟩ : syracuseStep 991731 = 1487597) B1487597
theorem B1483265 : Blo 988596 1483265 := bstep (se 2 (by rfl) ⟨556224, by rfl⟩ : syracuseStep 1483265 = 1112449) B1112449
theorem B991747 : Blo 988596 991747 := bstep (se 1 (by rfl) ⟨743810, by rfl⟩ : syracuseStep 991747 = 1487621) B1487621
theorem B1483283 : Blo 988596 1483283 := bstep (se 1 (by rfl) ⟨1112462, by rfl⟩ : syracuseStep 1483283 = 2224925) B2224925
theorem B991763 : Blo 988596 991763 := bstep (se 1 (by rfl) ⟨743822, by rfl⟩ : syracuseStep 991763 = 1487645) B1487645
theorem B991779 : Blo 988596 991779 := bstep (se 1 (by rfl) ⟨743834, by rfl⟩ : syracuseStep 991779 = 1487669) B1487669
theorem B1483313 : Blo 988596 1483313 := bstep (se 2 (by rfl) ⟨556242, by rfl⟩ : syracuseStep 1483313 = 1112485) B1112485
theorem B991795 : Blo 988596 991795 := bstep (se 1 (by rfl) ⟨743846, by rfl⟩ : syracuseStep 991795 = 1487693) B1487693
theorem B1483331 : Blo 988596 1483331 := bstep (se 1 (by rfl) ⟨1112498, by rfl⟩ : syracuseStep 1483331 = 2224997) B2224997
theorem B991811 : Blo 988596 991811 := bstep (se 1 (by rfl) ⟨743858, by rfl⟩ : syracuseStep 991811 = 1487717) B1487717
theorem B1253971 : Blo 988596 1253971 := bstep (se 1 (by rfl) ⟨940478, by rfl⟩ : syracuseStep 1253971 = 1880957) B1880957
theorem B991827 : Blo 988596 991827 := bstep (se 1 (by rfl) ⟨743870, by rfl⟩ : syracuseStep 991827 = 1487741) B1487741
theorem B1483361 : Blo 988596 1483361 := bstep (se 2 (by rfl) ⟨556260, by rfl⟩ : syracuseStep 1483361 = 1112521) B1112521
theorem B991843 : Blo 988596 991843 := bstep (se 1 (by rfl) ⟨743882, by rfl⟩ : syracuseStep 991843 = 1487765) B1487765
theorem B1483379 : Blo 988596 1483379 := bstep (se 1 (by rfl) ⟨1112534, by rfl⟩ : syracuseStep 1483379 = 2225069) B2225069
theorem B991859 : Blo 988596 991859 := bstep (se 1 (by rfl) ⟨743894, by rfl⟩ : syracuseStep 991859 = 1487789) B1487789
theorem B3383939 : Blo 988596 3383939 := bstep (se 1 (by rfl) ⟨2537954, by rfl⟩ : syracuseStep 3383939 = 5075909) B5075909
theorem B1057411 : Blo 988596 1057411 := bstep (se 1 (by rfl) ⟨793058, by rfl⟩ : syracuseStep 1057411 = 1586117) B1586117
theorem B991875 : Blo 988596 991875 := bstep (se 1 (by rfl) ⟨743906, by rfl⟩ : syracuseStep 991875 = 1487813) B1487813
theorem B1483409 : Blo 988596 1483409 := bstep (se 2 (by rfl) ⟨556278, by rfl⟩ : syracuseStep 1483409 = 1112557) B1112557
theorem B991891 : Blo 988596 991891 := bstep (se 1 (by rfl) ⟨743918, by rfl⟩ : syracuseStep 991891 = 1487837) B1487837
theorem B1483427 : Blo 988596 1483427 := bstep (se 1 (by rfl) ⟨1112570, by rfl⟩ : syracuseStep 1483427 = 2225141) B2225141
theorem B1188515 : Blo 988596 1188515 := bstep (se 1 (by rfl) ⟨891386, by rfl⟩ : syracuseStep 1188515 = 1782773) B1782773
theorem B991907 : Blo 988596 991907 := bstep (se 1 (by rfl) ⟨743930, by rfl⟩ : syracuseStep 991907 = 1487861) B1487861
theorem B991923 : Blo 988596 991923 := bstep (se 1 (by rfl) ⟨743942, by rfl⟩ : syracuseStep 991923 = 1487885) B1487885
theorem B1483457 : Blo 988596 1483457 := bstep (se 2 (by rfl) ⟨556296, by rfl⟩ : syracuseStep 1483457 = 1112593) B1112593
theorem B991939 : Blo 988596 991939 := bstep (se 1 (by rfl) ⟨743954, by rfl⟩ : syracuseStep 991939 = 1487909) B1487909
theorem B1483475 : Blo 988596 1483475 := bstep (se 1 (by rfl) ⟨1112606, by rfl⟩ : syracuseStep 1483475 = 2225213) B2225213
theorem B991955 : Blo 988596 991955 := bstep (se 1 (by rfl) ⟨743966, by rfl⟩ : syracuseStep 991955 = 1487933) B1487933
theorem B991971 : Blo 988596 991971 := bstep (se 1 (by rfl) ⟨743978, by rfl⟩ : syracuseStep 991971 = 1487957) B1487957
theorem B1483505 : Blo 988596 1483505 := bstep (se 2 (by rfl) ⟨556314, by rfl⟩ : syracuseStep 1483505 = 1112629) B1112629
theorem B991987 : Blo 988596 991987 := bstep (se 1 (by rfl) ⟨743990, by rfl⟩ : syracuseStep 991987 = 1487981) B1487981
theorem B1483523 : Blo 988596 1483523 := bstep (se 1 (by rfl) ⟨1112642, by rfl⟩ : syracuseStep 1483523 = 2225285) B2225285
theorem B992003 : Blo 988596 992003 := bstep (se 1 (by rfl) ⟨744002, by rfl⟩ : syracuseStep 992003 = 1488005) B1488005
theorem B992019 : Blo 988596 992019 := bstep (se 1 (by rfl) ⟨744014, by rfl⟩ : syracuseStep 992019 = 1488029) B1488029
theorem B1483553 : Blo 988596 1483553 := bstep (se 2 (by rfl) ⟨556332, by rfl⟩ : syracuseStep 1483553 = 1112665) B1112665
theorem B992035 : Blo 988596 992035 := bstep (se 1 (by rfl) ⟨744026, by rfl⟩ : syracuseStep 992035 = 1488053) B1488053
theorem B1483571 : Blo 988596 1483571 := bstep (se 1 (by rfl) ⟨1112678, by rfl⟩ : syracuseStep 1483571 = 2225357) B2225357
theorem B992051 : Blo 988596 992051 := bstep (se 1 (by rfl) ⟨744038, by rfl⟩ : syracuseStep 992051 = 1488077) B1488077
theorem B992067 : Blo 988596 992067 := bstep (se 1 (by rfl) ⟨744050, by rfl⟩ : syracuseStep 992067 = 1488101) B1488101
theorem B1483601 : Blo 988596 1483601 := bstep (se 2 (by rfl) ⟨556350, by rfl⟩ : syracuseStep 1483601 = 1112701) B1112701
theorem B992083 : Blo 988596 992083 := bstep (se 1 (by rfl) ⟨744062, by rfl⟩ : syracuseStep 992083 = 1488125) B1488125
theorem B1483619 : Blo 988596 1483619 := bstep (se 1 (by rfl) ⟨1112714, by rfl⟩ : syracuseStep 1483619 = 2225429) B2225429
theorem B992099 : Blo 988596 992099 := bstep (se 1 (by rfl) ⟨744074, by rfl⟩ : syracuseStep 992099 = 1488149) B1488149
theorem B992115 : Blo 988596 992115 := bstep (se 1 (by rfl) ⟨744086, by rfl⟩ : syracuseStep 992115 = 1488173) B1488173
theorem B1483649 : Blo 988596 1483649 := bstep (se 2 (by rfl) ⟨556368, by rfl⟩ : syracuseStep 1483649 = 1112737) B1112737
theorem B992131 : Blo 988596 992131 := bstep (se 1 (by rfl) ⟨744098, by rfl⟩ : syracuseStep 992131 = 1488197) B1488197
theorem B1483667 : Blo 988596 1483667 := bstep (se 1 (by rfl) ⟨1112750, by rfl⟩ : syracuseStep 1483667 = 2225501) B2225501
theorem B992147 : Blo 988596 992147 := bstep (se 1 (by rfl) ⟨744110, by rfl⟩ : syracuseStep 992147 = 1488221) B1488221
theorem B992163 : Blo 988596 992163 := bstep (se 1 (by rfl) ⟨744122, by rfl⟩ : syracuseStep 992163 = 1488245) B1488245
theorem B1483697 : Blo 988596 1483697 := bstep (se 2 (by rfl) ⟨556386, by rfl⟩ : syracuseStep 1483697 = 1112773) B1112773
theorem B992179 : Blo 988596 992179 := bstep (se 1 (by rfl) ⟨744134, by rfl⟩ : syracuseStep 992179 = 1488269) B1488269
theorem B1483715 : Blo 988596 1483715 := bstep (se 1 (by rfl) ⟨1112786, by rfl⟩ : syracuseStep 1483715 = 2225573) B2225573
theorem B992195 : Blo 988596 992195 := bstep (se 1 (by rfl) ⟨744146, by rfl⟩ : syracuseStep 992195 = 1488293) B1488293
theorem B992211 : Blo 988596 992211 := bstep (se 1 (by rfl) ⟨744158, by rfl⟩ : syracuseStep 992211 = 1488317) B1488317
theorem B1483745 : Blo 988596 1483745 := bstep (se 2 (by rfl) ⟨556404, by rfl⟩ : syracuseStep 1483745 = 1112809) B1112809
theorem B992227 : Blo 988596 992227 := bstep (se 1 (by rfl) ⟨744170, by rfl⟩ : syracuseStep 992227 = 1488341) B1488341
theorem B7513073 : Blo 988596 7513073 := bstep (se 2 (by rfl) ⟨2817402, by rfl⟩ : syracuseStep 7513073 = 5634805) B5634805
theorem B1483763 : Blo 988596 1483763 := bstep (se 1 (by rfl) ⟨1112822, by rfl⟩ : syracuseStep 1483763 = 2225645) B2225645
theorem B992243 : Blo 988596 992243 := bstep (se 1 (by rfl) ⟨744182, by rfl⟩ : syracuseStep 992243 = 1488365) B1488365
theorem B992259 : Blo 988596 992259 := bstep (se 1 (by rfl) ⟨744194, by rfl⟩ : syracuseStep 992259 = 1488389) B1488389
theorem B1483793 : Blo 988596 1483793 := bstep (se 2 (by rfl) ⟨556422, by rfl⟩ : syracuseStep 1483793 = 1112845) B1112845
theorem B992275 : Blo 988596 992275 := bstep (se 1 (by rfl) ⟨744206, by rfl⟩ : syracuseStep 992275 = 1488413) B1488413
theorem B1483811 : Blo 988596 1483811 := bstep (se 1 (by rfl) ⟨1112858, by rfl⟩ : syracuseStep 1483811 = 2225717) B2225717
theorem B992291 : Blo 988596 992291 := bstep (se 1 (by rfl) ⟨744218, by rfl⟩ : syracuseStep 992291 = 1488437) B1488437
theorem B992307 : Blo 988596 992307 := bstep (se 1 (by rfl) ⟨744230, by rfl⟩ : syracuseStep 992307 = 1488461) B1488461
theorem B1483841 : Blo 988596 1483841 := bstep (se 2 (by rfl) ⟨556440, by rfl⟩ : syracuseStep 1483841 = 1112881) B1112881
theorem B1254467 : Blo 988596 1254467 := bstep (se 1 (by rfl) ⟨940850, by rfl⟩ : syracuseStep 1254467 = 1881701) B1881701
theorem B992323 : Blo 988596 992323 := bstep (se 1 (by rfl) ⟨744242, by rfl⟩ : syracuseStep 992323 = 1488485) B1488485
theorem B1483859 : Blo 988596 1483859 := bstep (se 1 (by rfl) ⟨1112894, by rfl⟩ : syracuseStep 1483859 = 2225789) B2225789
theorem B992339 : Blo 988596 992339 := bstep (se 1 (by rfl) ⟨744254, by rfl⟩ : syracuseStep 992339 = 1488509) B1488509
theorem B992355 : Blo 988596 992355 := bstep (se 1 (by rfl) ⟨744266, by rfl⟩ : syracuseStep 992355 = 1488533) B1488533
theorem B1483889 : Blo 988596 1483889 := bstep (se 2 (by rfl) ⟨556458, by rfl⟩ : syracuseStep 1483889 = 1112917) B1112917
theorem B992371 : Blo 988596 992371 := bstep (se 1 (by rfl) ⟨744278, by rfl⟩ : syracuseStep 992371 = 1488557) B1488557
theorem B1483907 : Blo 988596 1483907 := bstep (se 1 (by rfl) ⟨1112930, by rfl⟩ : syracuseStep 1483907 = 2225861) B2225861
theorem B992387 : Blo 988596 992387 := bstep (se 1 (by rfl) ⟨744290, by rfl⟩ : syracuseStep 992387 = 1488581) B1488581
theorem B992403 : Blo 988596 992403 := bstep (se 1 (by rfl) ⟨744302, by rfl⟩ : syracuseStep 992403 = 1488605) B1488605
theorem B1483937 : Blo 988596 1483937 := bstep (se 2 (by rfl) ⟨556476, by rfl⟩ : syracuseStep 1483937 = 1112953) B1112953
theorem B992419 : Blo 988596 992419 := bstep (se 1 (by rfl) ⟨744314, by rfl⟩ : syracuseStep 992419 = 1488629) B1488629
theorem B1483955 : Blo 988596 1483955 := bstep (se 1 (by rfl) ⟨1112966, by rfl⟩ : syracuseStep 1483955 = 2225933) B2225933
theorem B992435 : Blo 988596 992435 := bstep (se 1 (by rfl) ⟨744326, by rfl⟩ : syracuseStep 992435 = 1488653) B1488653
theorem B992451 : Blo 988596 992451 := bstep (se 1 (by rfl) ⟨744338, by rfl⟩ : syracuseStep 992451 = 1488677) B1488677
theorem B1483985 : Blo 988596 1483985 := bstep (se 2 (by rfl) ⟨556494, by rfl⟩ : syracuseStep 1483985 = 1112989) B1112989
theorem B992467 : Blo 988596 992467 := bstep (se 1 (by rfl) ⟨744350, by rfl⟩ : syracuseStep 992467 = 1488701) B1488701
theorem B1484003 : Blo 988596 1484003 := bstep (se 1 (by rfl) ⟨1113002, by rfl⟩ : syracuseStep 1484003 = 2226005) B2226005
theorem B992483 : Blo 988596 992483 := bstep (se 1 (by rfl) ⟨744362, by rfl⟩ : syracuseStep 992483 = 1488725) B1488725
theorem B992499 : Blo 988596 992499 := bstep (se 1 (by rfl) ⟨744374, by rfl⟩ : syracuseStep 992499 = 1488749) B1488749
theorem B1484033 : Blo 988596 1484033 := bstep (se 2 (by rfl) ⟨556512, by rfl⟩ : syracuseStep 1484033 = 1113025) B1113025
theorem B1877251 : Blo 988596 1877251 := bstep (se 1 (by rfl) ⟨1407938, by rfl⟩ : syracuseStep 1877251 = 2815877) B2815877
theorem B992515 : Blo 988596 992515 := bstep (se 1 (by rfl) ⟨744386, by rfl⟩ : syracuseStep 992515 = 1488773) B1488773
theorem B1484051 : Blo 988596 1484051 := bstep (se 1 (by rfl) ⟨1113038, by rfl⟩ : syracuseStep 1484051 = 2226077) B2226077
theorem B992531 : Blo 988596 992531 := bstep (se 1 (by rfl) ⟨744398, by rfl⟩ : syracuseStep 992531 = 1488797) B1488797
theorem B992547 : Blo 988596 992547 := bstep (se 1 (by rfl) ⟨744410, by rfl⟩ : syracuseStep 992547 = 1488821) B1488821
theorem B1484081 : Blo 988596 1484081 := bstep (se 2 (by rfl) ⟨556530, by rfl⟩ : syracuseStep 1484081 = 1113061) B1113061
theorem B992563 : Blo 988596 992563 := bstep (se 1 (by rfl) ⟨744422, by rfl⟩ : syracuseStep 992563 = 1488845) B1488845
theorem B1484099 : Blo 988596 1484099 := bstep (se 1 (by rfl) ⟨1113074, by rfl⟩ : syracuseStep 1484099 = 2226149) B2226149
theorem B992579 : Blo 988596 992579 := bstep (se 1 (by rfl) ⟨744434, by rfl⟩ : syracuseStep 992579 = 1488869) B1488869
theorem B992595 : Blo 988596 992595 := bstep (se 1 (by rfl) ⟨744446, by rfl⟩ : syracuseStep 992595 = 1488893) B1488893
theorem B1484129 : Blo 988596 1484129 := bstep (se 2 (by rfl) ⟨556548, by rfl⟩ : syracuseStep 1484129 = 1113097) B1113097
theorem B1484147 : Blo 988596 1484147 := bstep (se 1 (by rfl) ⟨1113110, by rfl⟩ : syracuseStep 1484147 = 2226221) B2226221
theorem B1484177 : Blo 988596 1484177 := bstep (se 2 (by rfl) ⟨556566, by rfl⟩ : syracuseStep 1484177 = 1113133) B1113133
theorem B1877411 : Blo 988596 1877411 := bstep (se 1 (by rfl) ⟨1408058, by rfl⟩ : syracuseStep 1877411 = 2816117) B2816117
theorem B1484195 : Blo 988596 1484195 := bstep (se 1 (by rfl) ⟨1113146, by rfl⟩ : syracuseStep 1484195 = 2226293) B2226293
theorem B1484225 : Blo 988596 1484225 := bstep (se 2 (by rfl) ⟨556584, by rfl⟩ : syracuseStep 1484225 = 1113169) B1113169
theorem B1484243 : Blo 988596 1484243 := bstep (se 1 (by rfl) ⟨1113182, by rfl⟩ : syracuseStep 1484243 = 2226365) B2226365
theorem B1484273 : Blo 988596 1484273 := bstep (se 2 (by rfl) ⟨556602, by rfl⟩ : syracuseStep 1484273 = 1113205) B1113205
theorem B1484291 : Blo 988596 1484291 := bstep (se 1 (by rfl) ⟨1113218, by rfl⟩ : syracuseStep 1484291 = 2226437) B2226437
theorem B1484321 : Blo 988596 1484321 := bstep (se 2 (by rfl) ⟨556620, by rfl⟩ : syracuseStep 1484321 = 1113241) B1113241
theorem B1484339 : Blo 988596 1484339 := bstep (se 1 (by rfl) ⟨1113254, by rfl⟩ : syracuseStep 1484339 = 2226509) B2226509
theorem B1484369 : Blo 988596 1484369 := bstep (se 2 (by rfl) ⟨556638, by rfl⟩ : syracuseStep 1484369 = 1113277) B1113277
theorem B1484387 : Blo 988596 1484387 := bstep (se 1 (by rfl) ⟨1113290, by rfl⟩ : syracuseStep 1484387 = 2226581) B2226581
theorem B1484417 : Blo 988596 1484417 := bstep (se 2 (by rfl) ⟨556656, by rfl⟩ : syracuseStep 1484417 = 1113313) B1113313
theorem B1451665 : Blo 988596 1451665 := bstep (se 2 (by rfl) ⟨544374, by rfl⟩ : syracuseStep 1451665 = 1088749) B1088749
theorem B1484435 : Blo 988596 1484435 := bstep (se 1 (by rfl) ⟨1113326, by rfl⟩ : syracuseStep 1484435 = 2226653) B2226653
theorem B1484465 : Blo 988596 1484465 := bstep (se 2 (by rfl) ⟨556674, by rfl⟩ : syracuseStep 1484465 = 1113349) B1113349
theorem B1484483 : Blo 988596 1484483 := bstep (se 1 (by rfl) ⟨1113362, by rfl⟩ : syracuseStep 1484483 = 2226725) B2226725
theorem B1484513 : Blo 988596 1484513 := bstep (se 2 (by rfl) ⟨556692, by rfl⟩ : syracuseStep 1484513 = 1113385) B1113385
theorem B1484531 : Blo 988596 1484531 := bstep (se 1 (by rfl) ⟨1113398, by rfl⟩ : syracuseStep 1484531 = 2226797) B2226797
theorem B1255171 : Blo 988596 1255171 := bstep (se 1 (by rfl) ⟨941378, by rfl⟩ : syracuseStep 1255171 = 1882757) B1882757
theorem B1484561 : Blo 988596 1484561 := bstep (se 2 (by rfl) ⟨556710, by rfl⟩ : syracuseStep 1484561 = 1113421) B1113421
theorem B1484579 : Blo 988596 1484579 := bstep (se 1 (by rfl) ⟨1113434, by rfl⟩ : syracuseStep 1484579 = 2226869) B2226869
theorem B1484609 : Blo 988596 1484609 := bstep (se 2 (by rfl) ⟨556728, by rfl⟩ : syracuseStep 1484609 = 1113457) B1113457
theorem B1484627 : Blo 988596 1484627 := bstep (se 1 (by rfl) ⟨1113470, by rfl⟩ : syracuseStep 1484627 = 2226941) B2226941
theorem B1255267 : Blo 988596 1255267 := bstep (se 1 (by rfl) ⟨941450, by rfl⟩ : syracuseStep 1255267 = 1882901) B1882901
theorem B1484657 : Blo 988596 1484657 := bstep (se 2 (by rfl) ⟨556746, by rfl⟩ : syracuseStep 1484657 = 1113493) B1113493
theorem B1058675 : Blo 988596 1058675 := bstep (se 1 (by rfl) ⟨794006, by rfl⟩ : syracuseStep 1058675 = 1588013) B1588013
theorem B1484675 : Blo 988596 1484675 := bstep (se 1 (by rfl) ⟨1113506, by rfl⟩ : syracuseStep 1484675 = 2227013) B2227013
theorem B1484705 : Blo 988596 1484705 := bstep (se 2 (by rfl) ⟨556764, by rfl⟩ : syracuseStep 1484705 = 1113529) B1113529
theorem B1484723 : Blo 988596 1484723 := bstep (se 1 (by rfl) ⟨1113542, by rfl⟩ : syracuseStep 1484723 = 2227085) B2227085
theorem B1484753 : Blo 988596 1484753 := bstep (se 2 (by rfl) ⟨556782, by rfl⟩ : syracuseStep 1484753 = 1113565) B1113565
theorem B1484771 : Blo 988596 1484771 := bstep (se 1 (by rfl) ⟨1113578, by rfl⟩ : syracuseStep 1484771 = 2227157) B2227157
theorem B1484801 : Blo 988596 1484801 := bstep (se 2 (by rfl) ⟨556800, by rfl⟩ : syracuseStep 1484801 = 1113601) B1113601
theorem B1484819 : Blo 988596 1484819 := bstep (se 1 (by rfl) ⟨1113614, by rfl⟩ : syracuseStep 1484819 = 2227229) B2227229
theorem B1484849 : Blo 988596 1484849 := bstep (se 2 (by rfl) ⟨556818, by rfl⟩ : syracuseStep 1484849 = 1113637) B1113637
theorem B1484867 : Blo 988596 1484867 := bstep (se 1 (by rfl) ⟨1113650, by rfl⟩ : syracuseStep 1484867 = 2227301) B2227301
theorem B1484897 : Blo 988596 1484897 := bstep (se 2 (by rfl) ⟨556836, by rfl⟩ : syracuseStep 1484897 = 1113673) B1113673
theorem B3057763 : Blo 988596 3057763 := bstep (se 1 (by rfl) ⟨2293322, by rfl⟩ : syracuseStep 3057763 = 4586645) B4586645
theorem B1484915 : Blo 988596 1484915 := bstep (se 1 (by rfl) ⟨1113686, by rfl⟩ : syracuseStep 1484915 = 2227373) B2227373
theorem B5646469 : Blo 988596 5646469 := bstep (se 4 (by rfl) ⟨529356, by rfl⟩ : syracuseStep 5646469 = 1058713) B1058713
theorem B1484945 : Blo 988596 1484945 := bstep (se 2 (by rfl) ⟨556854, by rfl⟩ : syracuseStep 1484945 = 1113709) B1113709
theorem B1484963 : Blo 988596 1484963 := bstep (se 1 (by rfl) ⟨1113722, by rfl⟩ : syracuseStep 1484963 = 2227445) B2227445
theorem B1484993 : Blo 988596 1484993 := bstep (se 2 (by rfl) ⟨556872, by rfl⟩ : syracuseStep 1484993 = 1113745) B1113745
theorem B1485011 : Blo 988596 1485011 := bstep (se 1 (by rfl) ⟨1113758, by rfl⟩ : syracuseStep 1485011 = 2227517) B2227517
theorem B1714403 : Blo 988596 1714403 := bstep (se 1 (by rfl) ⟨1285802, by rfl⟩ : syracuseStep 1714403 = 2571605) B2571605
theorem B1485041 : Blo 988596 1485041 := bstep (se 2 (by rfl) ⟨556890, by rfl⟩ : syracuseStep 1485041 = 1113781) B1113781
theorem B1485059 : Blo 988596 1485059 := bstep (se 1 (by rfl) ⟨1113794, by rfl⟩ : syracuseStep 1485059 = 2227589) B2227589
theorem B1485089 : Blo 988596 1485089 := bstep (se 2 (by rfl) ⟨556908, by rfl⟩ : syracuseStep 1485089 = 1113817) B1113817
theorem B1485107 : Blo 988596 1485107 := bstep (se 1 (by rfl) ⟨1113830, by rfl⟩ : syracuseStep 1485107 = 2227661) B2227661
theorem B1485137 : Blo 988596 1485137 := bstep (se 2 (by rfl) ⟨556926, by rfl⟩ : syracuseStep 1485137 = 1113853) B1113853
theorem B1255763 : Blo 988596 1255763 := bstep (se 1 (by rfl) ⟨941822, by rfl⟩ : syracuseStep 1255763 = 1883645) B1883645
theorem B1485155 : Blo 988596 1485155 := bstep (se 1 (by rfl) ⟨1113866, by rfl⟩ : syracuseStep 1485155 = 2227733) B2227733
theorem B1485185 : Blo 988596 1485185 := bstep (se 2 (by rfl) ⟨556944, by rfl⟩ : syracuseStep 1485185 = 1113889) B1113889
theorem B1485203 : Blo 988596 1485203 := bstep (se 1 (by rfl) ⟨1113902, by rfl⟩ : syracuseStep 1485203 = 2227805) B2227805
theorem B1485233 : Blo 988596 1485233 := bstep (se 2 (by rfl) ⟨556962, by rfl⟩ : syracuseStep 1485233 = 1113925) B1113925
theorem B1485251 : Blo 988596 1485251 := bstep (se 1 (by rfl) ⟨1113938, by rfl⟩ : syracuseStep 1485251 = 2227877) B2227877
theorem B1878481 : Blo 988596 1878481 := bstep (se 2 (by rfl) ⟨704430, by rfl⟩ : syracuseStep 1878481 = 1408861) B1408861
theorem B1485281 : Blo 988596 1485281 := bstep (se 2 (by rfl) ⟨556980, by rfl⟩ : syracuseStep 1485281 = 1113961) B1113961
theorem B1485299 : Blo 988596 1485299 := bstep (se 1 (by rfl) ⟨1113974, by rfl⟩ : syracuseStep 1485299 = 2227949) B2227949
theorem B1485329 : Blo 988596 1485329 := bstep (se 2 (by rfl) ⟨556998, by rfl⟩ : syracuseStep 1485329 = 1113997) B1113997
theorem B1485347 : Blo 988596 1485347 := bstep (se 1 (by rfl) ⟨1114010, by rfl⟩ : syracuseStep 1485347 = 2228021) B2228021
theorem B4237859 : Blo 988596 4237859 := bstep (se 1 (by rfl) ⟨3178394, by rfl⟩ : syracuseStep 4237859 = 6356789) B6356789
theorem B1485377 : Blo 988596 1485377 := bstep (se 2 (by rfl) ⟨557016, by rfl⟩ : syracuseStep 1485377 = 1114033) B1114033
theorem B1485395 : Blo 988596 1485395 := bstep (se 1 (by rfl) ⟨1114046, by rfl⟩ : syracuseStep 1485395 = 2228093) B2228093
theorem B1583713 : Blo 988596 1583713 := bstep (se 2 (by rfl) ⟨593892, by rfl⟩ : syracuseStep 1583713 = 1187785) B1187785
theorem B1059427 : Blo 988596 1059427 := bstep (se 1 (by rfl) ⟨794570, by rfl⟩ : syracuseStep 1059427 = 1589141) B1589141
theorem B1485425 : Blo 988596 1485425 := bstep (se 2 (by rfl) ⟨557034, by rfl⟩ : syracuseStep 1485425 = 1114069) B1114069
theorem B1485443 : Blo 988596 1485443 := bstep (se 1 (by rfl) ⟨1114082, by rfl⟩ : syracuseStep 1485443 = 2228165) B2228165
theorem B1485473 : Blo 988596 1485473 := bstep (se 2 (by rfl) ⟨557052, by rfl⟩ : syracuseStep 1485473 = 1114105) B1114105
theorem B1485491 : Blo 988596 1485491 := bstep (se 1 (by rfl) ⟨1114118, by rfl⟩ : syracuseStep 1485491 = 2228237) B2228237
theorem B1485521 : Blo 988596 1485521 := bstep (se 2 (by rfl) ⟨557070, by rfl⟩ : syracuseStep 1485521 = 1114141) B1114141
theorem B1485539 : Blo 988596 1485539 := bstep (se 1 (by rfl) ⟨1114154, by rfl⟩ : syracuseStep 1485539 = 2228309) B2228309
theorem B1485569 : Blo 988596 1485569 := bstep (se 2 (by rfl) ⟨557088, by rfl⟩ : syracuseStep 1485569 = 1114177) B1114177
theorem B1485587 : Blo 988596 1485587 := bstep (se 1 (by rfl) ⟨1114190, by rfl⟩ : syracuseStep 1485587 = 2228381) B2228381
theorem B1485617 : Blo 988596 1485617 := bstep (se 2 (by rfl) ⟨557106, by rfl⟩ : syracuseStep 1485617 = 1114213) B1114213
theorem B1485635 : Blo 988596 1485635 := bstep (se 1 (by rfl) ⟨1114226, by rfl⟩ : syracuseStep 1485635 = 2228453) B2228453
theorem B1583969 : Blo 988596 1583969 := bstep (se 2 (by rfl) ⟨593988, by rfl⟩ : syracuseStep 1583969 = 1187977) B1187977
theorem B1485665 : Blo 988596 1485665 := bstep (se 2 (by rfl) ⟨557124, by rfl⟩ : syracuseStep 1485665 = 1114249) B1114249
theorem B1485683 : Blo 988596 1485683 := bstep (se 1 (by rfl) ⟨1114262, by rfl⟩ : syracuseStep 1485683 = 2228525) B2228525
theorem B1485713 : Blo 988596 1485713 := bstep (se 2 (by rfl) ⟨557142, by rfl⟩ : syracuseStep 1485713 = 1114285) B1114285
theorem B1190803 : Blo 988596 1190803 := bstep (se 1 (by rfl) ⟨893102, by rfl⟩ : syracuseStep 1190803 = 1786205) B1786205
theorem B1485731 : Blo 988596 1485731 := bstep (se 1 (by rfl) ⟨1114298, by rfl⟩ : syracuseStep 1485731 = 2228597) B2228597
theorem B1485761 : Blo 988596 1485761 := bstep (se 2 (by rfl) ⟨557160, by rfl⟩ : syracuseStep 1485761 = 1114321) B1114321
theorem B1485779 : Blo 988596 1485779 := bstep (se 1 (by rfl) ⟨1114334, by rfl⟩ : syracuseStep 1485779 = 2228669) B2228669
theorem B1485809 : Blo 988596 1485809 := bstep (se 2 (by rfl) ⟨557178, by rfl⟩ : syracuseStep 1485809 = 1114357) B1114357
theorem B5024753 : Blo 988596 5024753 := bstep (se 2 (by rfl) ⟨1884282, by rfl⟩ : syracuseStep 5024753 = 3768565) B3768565
theorem B1190899 : Blo 988596 1190899 := bstep (se 1 (by rfl) ⟨893174, by rfl⟩ : syracuseStep 1190899 = 1786349) B1786349
theorem B1485827 : Blo 988596 1485827 := bstep (se 1 (by rfl) ⟨1114370, by rfl⟩ : syracuseStep 1485827 = 2228741) B2228741
theorem B1485857 : Blo 988596 1485857 := bstep (se 2 (by rfl) ⟨557196, by rfl⟩ : syracuseStep 1485857 = 1114393) B1114393
theorem B1190947 : Blo 988596 1190947 := bstep (se 1 (by rfl) ⟨893210, by rfl⟩ : syracuseStep 1190947 = 1786421) B1786421
theorem B2010161 : Blo 988596 2010161 := bstep (se 2 (by rfl) ⟨753810, by rfl⟩ : syracuseStep 2010161 = 1507621) B1507621
theorem B1485875 : Blo 988596 1485875 := bstep (se 1 (by rfl) ⟨1114406, by rfl⟩ : syracuseStep 1485875 = 2228813) B2228813
theorem B1485905 : Blo 988596 1485905 := bstep (se 2 (by rfl) ⟨557214, by rfl⟩ : syracuseStep 1485905 = 1114429) B1114429
theorem B1485923 : Blo 988596 1485923 := bstep (se 1 (by rfl) ⟨1114442, by rfl⟩ : syracuseStep 1485923 = 2228885) B2228885
theorem B1485953 : Blo 988596 1485953 := bstep (se 2 (by rfl) ⟨557232, by rfl⟩ : syracuseStep 1485953 = 1114465) B1114465
theorem B1485971 : Blo 988596 1485971 := bstep (se 1 (by rfl) ⟨1114478, by rfl⟩ : syracuseStep 1485971 = 2228957) B2228957
theorem B1486001 : Blo 988596 1486001 := bstep (se 2 (by rfl) ⟨557250, by rfl⟩ : syracuseStep 1486001 = 1114501) B1114501
theorem B1486019 : Blo 988596 1486019 := bstep (se 1 (by rfl) ⟨1114514, by rfl⟩ : syracuseStep 1486019 = 2229029) B2229029
theorem B1486049 : Blo 988596 1486049 := bstep (se 2 (by rfl) ⟨557268, by rfl⟩ : syracuseStep 1486049 = 1114537) B1114537
theorem B1486067 : Blo 988596 1486067 := bstep (se 1 (by rfl) ⟨1114550, by rfl⟩ : syracuseStep 1486067 = 2229101) B2229101
theorem B1486097 : Blo 988596 1486097 := bstep (se 2 (by rfl) ⟨557286, by rfl⟩ : syracuseStep 1486097 = 1114573) B1114573
theorem B1486115 : Blo 988596 1486115 := bstep (se 1 (by rfl) ⟨1114586, by rfl⟩ : syracuseStep 1486115 = 2229173) B2229173
theorem B1486145 : Blo 988596 1486145 := bstep (se 2 (by rfl) ⟨557304, by rfl⟩ : syracuseStep 1486145 = 1114609) B1114609
theorem B1486163 : Blo 988596 1486163 := bstep (se 1 (by rfl) ⟨1114622, by rfl⟩ : syracuseStep 1486163 = 2229245) B2229245
theorem B4762979 : Blo 988596 4762979 := bstep (se 1 (by rfl) ⟨3572234, by rfl⟩ : syracuseStep 4762979 = 7144469) B7144469
theorem B1486193 : Blo 988596 1486193 := bstep (se 2 (by rfl) ⟨557322, by rfl⟩ : syracuseStep 1486193 = 1114645) B1114645
theorem B1486211 : Blo 988596 1486211 := bstep (se 1 (by rfl) ⟨1114658, by rfl⟩ : syracuseStep 1486211 = 2229317) B2229317
theorem B1486241 : Blo 988596 1486241 := bstep (se 2 (by rfl) ⟨557340, by rfl⟩ : syracuseStep 1486241 = 1114681) B1114681
theorem B1486259 : Blo 988596 1486259 := bstep (se 1 (by rfl) ⟨1114694, by rfl⟩ : syracuseStep 1486259 = 2229389) B2229389
theorem B1486289 : Blo 988596 1486289 := bstep (se 2 (by rfl) ⟨557358, by rfl⟩ : syracuseStep 1486289 = 1114717) B1114717
theorem B1486307 : Blo 988596 1486307 := bstep (se 1 (by rfl) ⟨1114730, by rfl⟩ : syracuseStep 1486307 = 2229461) B2229461
theorem B1879537 : Blo 988596 1879537 := bstep (se 2 (by rfl) ⟨704826, by rfl⟩ : syracuseStep 1879537 = 1409653) B1409653
theorem B1486337 : Blo 988596 1486337 := bstep (se 2 (by rfl) ⟨557376, by rfl⟩ : syracuseStep 1486337 = 1114753) B1114753
theorem B1486355 : Blo 988596 1486355 := bstep (se 1 (by rfl) ⟨1114766, by rfl⟩ : syracuseStep 1486355 = 2229533) B2229533
theorem B1486385 : Blo 988596 1486385 := bstep (se 2 (by rfl) ⟨557394, by rfl⟩ : syracuseStep 1486385 = 1114789) B1114789
theorem B1486403 : Blo 988596 1486403 := bstep (se 1 (by rfl) ⟨1114802, by rfl⟩ : syracuseStep 1486403 = 2229605) B2229605
theorem B1486433 : Blo 988596 1486433 := bstep (se 2 (by rfl) ⟨557412, by rfl⟩ : syracuseStep 1486433 = 1114825) B1114825
theorem B1486451 : Blo 988596 1486451 := bstep (se 1 (by rfl) ⟨1114838, by rfl⟩ : syracuseStep 1486451 = 2229677) B2229677
theorem B1486481 : Blo 988596 1486481 := bstep (se 2 (by rfl) ⟨557430, by rfl⟩ : syracuseStep 1486481 = 1114861) B1114861
theorem B1486499 : Blo 988596 1486499 := bstep (se 1 (by rfl) ⟨1114874, by rfl⟩ : syracuseStep 1486499 = 2229749) B2229749
theorem B3223217 : Blo 988596 3223217 := bstep (se 2 (by rfl) ⟨1208706, by rfl⟩ : syracuseStep 3223217 = 2417413) B2417413
theorem B1486529 : Blo 988596 1486529 := bstep (se 2 (by rfl) ⟨557448, by rfl⟩ : syracuseStep 1486529 = 1114897) B1114897
theorem B1486547 : Blo 988596 1486547 := bstep (se 1 (by rfl) ⟨1114910, by rfl⟩ : syracuseStep 1486547 = 2229821) B2229821
theorem B1486577 : Blo 988596 1486577 := bstep (se 2 (by rfl) ⟨557466, by rfl⟩ : syracuseStep 1486577 = 1114933) B1114933
theorem B1486595 : Blo 988596 1486595 := bstep (se 1 (by rfl) ⟨1114946, by rfl⟩ : syracuseStep 1486595 = 2229893) B2229893
theorem B1486625 : Blo 988596 1486625 := bstep (se 2 (by rfl) ⟨557484, by rfl⟩ : syracuseStep 1486625 = 1114969) B1114969
theorem B4763441 : Blo 988596 4763441 := bstep (se 2 (by rfl) ⟨1786290, by rfl⟩ : syracuseStep 4763441 = 3572581) B3572581
theorem B1486643 : Blo 988596 1486643 := bstep (se 1 (by rfl) ⟨1114982, by rfl⟩ : syracuseStep 1486643 = 2229965) B2229965
theorem B1486673 : Blo 988596 1486673 := bstep (se 2 (by rfl) ⟨557502, by rfl⟩ : syracuseStep 1486673 = 1115005) B1115005
theorem B1486691 : Blo 988596 1486691 := bstep (se 1 (by rfl) ⟨1115018, by rfl⟩ : syracuseStep 1486691 = 2230037) B2230037
theorem B1486721 : Blo 988596 1486721 := bstep (se 2 (by rfl) ⟨557520, by rfl⟩ : syracuseStep 1486721 = 1115041) B1115041
theorem B1879939 : Blo 988596 1879939 := bstep (se 1 (by rfl) ⟨1409954, by rfl⟩ : syracuseStep 1879939 = 2819909) B2819909
theorem B1486739 : Blo 988596 1486739 := bstep (se 1 (by rfl) ⟨1115054, by rfl⟩ : syracuseStep 1486739 = 2230109) B2230109
theorem B1879985 : Blo 988596 1879985 := bstep (se 2 (by rfl) ⟨704994, by rfl⟩ : syracuseStep 1879985 = 1409989) B1409989
theorem B1486769 : Blo 988596 1486769 := bstep (se 2 (by rfl) ⟨557538, by rfl⟩ : syracuseStep 1486769 = 1115077) B1115077
theorem B1486787 : Blo 988596 1486787 := bstep (se 1 (by rfl) ⟨1115090, by rfl⟩ : syracuseStep 1486787 = 2230181) B2230181
theorem B1486817 : Blo 988596 1486817 := bstep (se 2 (by rfl) ⟨557556, by rfl⟩ : syracuseStep 1486817 = 1115113) B1115113
theorem B1486835 : Blo 988596 1486835 := bstep (se 1 (by rfl) ⟨1115126, by rfl⟩ : syracuseStep 1486835 = 2230253) B2230253
theorem B1486865 : Blo 988596 1486865 := bstep (se 2 (by rfl) ⟨557574, by rfl⟩ : syracuseStep 1486865 = 1115149) B1115149
theorem B1486883 : Blo 988596 1486883 := bstep (se 1 (by rfl) ⟨1115162, by rfl⟩ : syracuseStep 1486883 = 2230325) B2230325
theorem B1486913 : Blo 988596 1486913 := bstep (se 2 (by rfl) ⟨557592, by rfl⟩ : syracuseStep 1486913 = 1115185) B1115185
theorem B5648453 : Blo 988596 5648453 := bstep (se 4 (by rfl) ⟨529542, by rfl⟩ : syracuseStep 5648453 = 1059085) B1059085
theorem B1486931 : Blo 988596 1486931 := bstep (se 1 (by rfl) ⟨1115198, by rfl⟩ : syracuseStep 1486931 = 2230397) B2230397
theorem B1486961 : Blo 988596 1486961 := bstep (se 2 (by rfl) ⟨557610, by rfl⟩ : syracuseStep 1486961 = 1115221) B1115221
theorem B1486979 : Blo 988596 1486979 := bstep (se 1 (by rfl) ⟨1115234, by rfl⟩ : syracuseStep 1486979 = 2230469) B2230469
theorem B1487009 : Blo 988596 1487009 := bstep (se 2 (by rfl) ⟨557628, by rfl⟩ : syracuseStep 1487009 = 1115257) B1115257
theorem B1487027 : Blo 988596 1487027 := bstep (se 1 (by rfl) ⟨1115270, by rfl⟩ : syracuseStep 1487027 = 2230541) B2230541
theorem B1880273 : Blo 988596 1880273 := bstep (se 2 (by rfl) ⟨705102, by rfl⟩ : syracuseStep 1880273 = 1410205) B1410205
theorem B1487057 : Blo 988596 1487057 := bstep (se 2 (by rfl) ⟨557646, by rfl⟩ : syracuseStep 1487057 = 1115293) B1115293
theorem B1585379 : Blo 988596 1585379 := bstep (se 1 (by rfl) ⟨1189034, by rfl⟩ : syracuseStep 1585379 = 2378069) B2378069
theorem B1487075 : Blo 988596 1487075 := bstep (se 1 (by rfl) ⟨1115306, by rfl⟩ : syracuseStep 1487075 = 2230613) B2230613
theorem B1192163 : Blo 988596 1192163 := bstep (se 1 (by rfl) ⟨894122, by rfl⟩ : syracuseStep 1192163 = 1788245) B1788245
theorem B1487105 : Blo 988596 1487105 := bstep (se 2 (by rfl) ⟨557664, by rfl⟩ : syracuseStep 1487105 = 1115329) B1115329
theorem B1487123 : Blo 988596 1487123 := bstep (se 1 (by rfl) ⟨1115342, by rfl⟩ : syracuseStep 1487123 = 2230685) B2230685
theorem B1487153 : Blo 988596 1487153 := bstep (se 2 (by rfl) ⟨557682, by rfl⟩ : syracuseStep 1487153 = 1115365) B1115365
theorem B1487171 : Blo 988596 1487171 := bstep (se 1 (by rfl) ⟨1115378, by rfl⟩ : syracuseStep 1487171 = 2230757) B2230757
theorem B1487201 : Blo 988596 1487201 := bstep (se 2 (by rfl) ⟨557700, by rfl⟩ : syracuseStep 1487201 = 1115401) B1115401
theorem B1487219 : Blo 988596 1487219 := bstep (se 1 (by rfl) ⟨1115414, by rfl⟩ : syracuseStep 1487219 = 2230829) B2230829
theorem B1487249 : Blo 988596 1487249 := bstep (se 2 (by rfl) ⟨557718, by rfl⟩ : syracuseStep 1487249 = 1115437) B1115437
theorem B1487267 : Blo 988596 1487267 := bstep (se 1 (by rfl) ⟨1115450, by rfl⟩ : syracuseStep 1487267 = 2230901) B2230901
theorem B1487297 : Blo 988596 1487297 := bstep (se 2 (by rfl) ⟨557736, by rfl⟩ : syracuseStep 1487297 = 1115473) B1115473
theorem B19313093 : Blo 988596 19313093 := bstep (se 4 (by rfl) ⟨1810602, by rfl⟩ : syracuseStep 19313093 = 3621205) B3621205
theorem B1487315 : Blo 988596 1487315 := bstep (se 1 (by rfl) ⟨1115486, by rfl⟩ : syracuseStep 1487315 = 2230973) B2230973
theorem B1487345 : Blo 988596 1487345 := bstep (se 2 (by rfl) ⟨557754, by rfl⟩ : syracuseStep 1487345 = 1115509) B1115509
theorem B1487363 : Blo 988596 1487363 := bstep (se 1 (by rfl) ⟨1115522, by rfl⟩ : syracuseStep 1487363 = 2231045) B2231045
theorem B1487393 : Blo 988596 1487393 := bstep (se 2 (by rfl) ⟨557772, by rfl⟩ : syracuseStep 1487393 = 1115545) B1115545
theorem B1487411 : Blo 988596 1487411 := bstep (se 1 (by rfl) ⟨1115558, by rfl⟩ : syracuseStep 1487411 = 2231117) B2231117
theorem B1487441 : Blo 988596 1487441 := bstep (se 2 (by rfl) ⟨557790, by rfl⟩ : syracuseStep 1487441 = 1115581) B1115581
theorem B1487459 : Blo 988596 1487459 := bstep (se 1 (by rfl) ⟨1115594, by rfl⟩ : syracuseStep 1487459 = 2231189) B2231189
theorem B1487489 : Blo 988596 1487489 := bstep (se 2 (by rfl) ⟨557808, by rfl⟩ : syracuseStep 1487489 = 1115617) B1115617
theorem B1487507 : Blo 988596 1487507 := bstep (se 1 (by rfl) ⟨1115630, by rfl⟩ : syracuseStep 1487507 = 2231261) B2231261
theorem B2503345 : Blo 988596 2503345 := bstep (se 2 (by rfl) ⟨938754, by rfl⟩ : syracuseStep 2503345 = 1877509) B1877509
theorem B1487537 : Blo 988596 1487537 := bstep (se 2 (by rfl) ⟨557826, by rfl⟩ : syracuseStep 1487537 = 1115653) B1115653
theorem B1487555 : Blo 988596 1487555 := bstep (se 1 (by rfl) ⟨1115666, by rfl⟩ : syracuseStep 1487555 = 2231333) B2231333
theorem B4764365 : Blo 988596 4764365 := bstep (se 3 (by rfl) ⟨893318, by rfl⟩ : syracuseStep 4764365 = 1786637) B1786637
theorem B1487585 : Blo 988596 1487585 := bstep (se 2 (by rfl) ⟨557844, by rfl⟩ : syracuseStep 1487585 = 1115689) B1115689
theorem B1487603 : Blo 988596 1487603 := bstep (se 1 (by rfl) ⟨1115702, by rfl⟩ : syracuseStep 1487603 = 2231405) B2231405
theorem B1487633 : Blo 988596 1487633 := bstep (se 2 (by rfl) ⟨557862, by rfl⟩ : syracuseStep 1487633 = 1115725) B1115725
theorem B61092629 : Blo 988596 61092629 := bstep (se 6 (by rfl) ⟨1431858, by rfl⟩ : syracuseStep 61092629 = 2863717) B2863717
theorem B1487651 : Blo 988596 1487651 := bstep (se 1 (by rfl) ⟨1115738, by rfl⟩ : syracuseStep 1487651 = 2231477) B2231477
theorem B1487681 : Blo 988596 1487681 := bstep (se 2 (by rfl) ⟨557880, by rfl⟩ : syracuseStep 1487681 = 1115761) B1115761
theorem B1487699 : Blo 988596 1487699 := bstep (se 1 (by rfl) ⟨1115774, by rfl⟩ : syracuseStep 1487699 = 2231549) B2231549
theorem B1487729 : Blo 988596 1487729 := bstep (se 2 (by rfl) ⟨557898, by rfl⟩ : syracuseStep 1487729 = 1115797) B1115797
theorem B1487747 : Blo 988596 1487747 := bstep (se 1 (by rfl) ⟨1115810, by rfl⟩ : syracuseStep 1487747 = 2231621) B2231621
theorem B1487777 : Blo 988596 1487777 := bstep (se 2 (by rfl) ⟨557916, by rfl⟩ : syracuseStep 1487777 = 1115833) B1115833
theorem B1880995 : Blo 988596 1880995 := bstep (se 1 (by rfl) ⟨1410746, by rfl⟩ : syracuseStep 1880995 = 2821493) B2821493
theorem B1487795 : Blo 988596 1487795 := bstep (se 1 (by rfl) ⟨1115846, by rfl⟩ : syracuseStep 1487795 = 2231693) B2231693
theorem B2503619 : Blo 988596 2503619 := bstep (se 1 (by rfl) ⟨1877714, by rfl⟩ : syracuseStep 2503619 = 3755429) B3755429
theorem B1487825 : Blo 988596 1487825 := bstep (se 2 (by rfl) ⟨557934, by rfl⟩ : syracuseStep 1487825 = 1115869) B1115869
theorem B1487843 : Blo 988596 1487843 := bstep (se 1 (by rfl) ⟨1115882, by rfl⟩ : syracuseStep 1487843 = 2231765) B2231765
theorem B1487873 : Blo 988596 1487873 := bstep (se 2 (by rfl) ⟨557952, by rfl⟩ : syracuseStep 1487873 = 1115905) B1115905
theorem B1487891 : Blo 988596 1487891 := bstep (se 1 (by rfl) ⟨1115918, by rfl⟩ : syracuseStep 1487891 = 2231837) B2231837
theorem B1586225 : Blo 988596 1586225 := bstep (se 2 (by rfl) ⟨594834, by rfl⟩ : syracuseStep 1586225 = 1189669) B1189669
theorem B1487921 : Blo 988596 1487921 := bstep (se 2 (by rfl) ⟨557970, by rfl⟩ : syracuseStep 1487921 = 1115941) B1115941
theorem B1487939 : Blo 988596 1487939 := bstep (se 1 (by rfl) ⟨1115954, by rfl⟩ : syracuseStep 1487939 = 2231909) B2231909
theorem B1487969 : Blo 988596 1487969 := bstep (se 2 (by rfl) ⟨557988, by rfl⟩ : syracuseStep 1487969 = 1115977) B1115977
theorem B1487987 : Blo 988596 1487987 := bstep (se 1 (by rfl) ⟨1115990, by rfl⟩ : syracuseStep 1487987 = 2231981) B2231981
theorem B2503811 : Blo 988596 2503811 := bstep (se 1 (by rfl) ⟨1877858, by rfl⟩ : syracuseStep 2503811 = 3755717) B3755717
theorem B11416717 : Blo 988596 11416717 := bstep (se 3 (by rfl) ⟨2140634, by rfl⟩ : syracuseStep 11416717 = 4281269) B4281269
theorem B1488017 : Blo 988596 1488017 := bstep (se 2 (by rfl) ⟨558006, by rfl⟩ : syracuseStep 1488017 = 1116013) B1116013
theorem B1782947 : Blo 988596 1782947 := bstep (se 1 (by rfl) ⟨1337210, by rfl⟩ : syracuseStep 1782947 = 2674421) B2674421
theorem B1488035 : Blo 988596 1488035 := bstep (se 1 (by rfl) ⟨1116026, by rfl⟩ : syracuseStep 1488035 = 2232053) B2232053
theorem B1488065 : Blo 988596 1488065 := bstep (se 2 (by rfl) ⟨558024, by rfl⟩ : syracuseStep 1488065 = 1116049) B1116049
theorem B6436037 : Blo 988596 6436037 := bstep (se 4 (by rfl) ⟨603378, by rfl⟩ : syracuseStep 6436037 = 1206757) B1206757
theorem B1488083 : Blo 988596 1488083 := bstep (se 1 (by rfl) ⟨1116062, by rfl⟩ : syracuseStep 1488083 = 2232125) B2232125
theorem B1488113 : Blo 988596 1488113 := bstep (se 2 (by rfl) ⟨558042, by rfl⟩ : syracuseStep 1488113 = 1116085) B1116085
theorem B1488131 : Blo 988596 1488131 := bstep (se 1 (by rfl) ⟨1116098, by rfl⟩ : syracuseStep 1488131 = 2232197) B2232197
theorem B1488161 : Blo 988596 1488161 := bstep (se 2 (by rfl) ⟨558060, by rfl⟩ : syracuseStep 1488161 = 1116121) B1116121
theorem B1488179 : Blo 988596 1488179 := bstep (se 1 (by rfl) ⟨1116134, by rfl⟩ : syracuseStep 1488179 = 2232269) B2232269
theorem B1488209 : Blo 988596 1488209 := bstep (se 2 (by rfl) ⟨558078, by rfl⟩ : syracuseStep 1488209 = 1116157) B1116157
theorem B1881443 : Blo 988596 1881443 := bstep (se 1 (by rfl) ⟨1411082, by rfl⟩ : syracuseStep 1881443 = 2822165) B2822165
theorem B1488227 : Blo 988596 1488227 := bstep (se 1 (by rfl) ⟨1116170, by rfl⟩ : syracuseStep 1488227 = 2232341) B2232341
theorem B1488257 : Blo 988596 1488257 := bstep (se 2 (by rfl) ⟨558096, by rfl⟩ : syracuseStep 1488257 = 1116193) B1116193
theorem B1488275 : Blo 988596 1488275 := bstep (se 1 (by rfl) ⟨1116206, by rfl⟩ : syracuseStep 1488275 = 2232413) B2232413
theorem B1488305 : Blo 988596 1488305 := bstep (se 2 (by rfl) ⟨558114, by rfl⟩ : syracuseStep 1488305 = 1116229) B1116229
theorem B1652147 : Blo 988596 1652147 := bstep (se 1 (by rfl) ⟨1239110, by rfl⟩ : syracuseStep 1652147 = 2478221) B2478221
theorem B1783235 : Blo 988596 1783235 := bstep (se 1 (by rfl) ⟨1337426, by rfl⟩ : syracuseStep 1783235 = 2674853) B2674853
theorem B1488323 : Blo 988596 1488323 := bstep (se 1 (by rfl) ⟨1116242, by rfl⟩ : syracuseStep 1488323 = 2232485) B2232485
theorem B9024965 : Blo 988596 9024965 := bstep (se 4 (by rfl) ⟨846090, by rfl⟩ : syracuseStep 9024965 = 1692181) B1692181
theorem B1488353 : Blo 988596 1488353 := bstep (se 2 (by rfl) ⟨558132, by rfl⟩ : syracuseStep 1488353 = 1116265) B1116265
theorem B1488371 : Blo 988596 1488371 := bstep (se 1 (by rfl) ⟨1116278, by rfl⟩ : syracuseStep 1488371 = 2232557) B2232557
theorem B1488401 : Blo 988596 1488401 := bstep (se 2 (by rfl) ⟨558150, by rfl⟩ : syracuseStep 1488401 = 1116301) B1116301
theorem B1488419 : Blo 988596 1488419 := bstep (se 1 (by rfl) ⟨1116314, by rfl⟩ : syracuseStep 1488419 = 2232629) B2232629
theorem B1586737 : Blo 988596 1586737 := bstep (se 2 (by rfl) ⟨595026, by rfl⟩ : syracuseStep 1586737 = 1190053) B1190053
theorem B1488449 : Blo 988596 1488449 := bstep (se 2 (by rfl) ⟨558168, by rfl⟩ : syracuseStep 1488449 = 1116337) B1116337
theorem B1488467 : Blo 988596 1488467 := bstep (se 1 (by rfl) ⟨1116350, by rfl⟩ : syracuseStep 1488467 = 2232701) B2232701
theorem B1488497 : Blo 988596 1488497 := bstep (se 2 (by rfl) ⟨558186, by rfl⟩ : syracuseStep 1488497 = 1116373) B1116373
theorem B1881731 : Blo 988596 1881731 := bstep (se 1 (by rfl) ⟨1411298, by rfl⟩ : syracuseStep 1881731 = 2822597) B2822597
theorem B1488515 : Blo 988596 1488515 := bstep (se 1 (by rfl) ⟨1116386, by rfl⟩ : syracuseStep 1488515 = 2232773) B2232773
theorem B1488545 : Blo 988596 1488545 := bstep (se 2 (by rfl) ⟨558204, by rfl⟩ : syracuseStep 1488545 = 1116409) B1116409
theorem B1488563 : Blo 988596 1488563 := bstep (se 1 (by rfl) ⟨1116422, by rfl⟩ : syracuseStep 1488563 = 2232845) B2232845
theorem B13579973 : Blo 988596 13579973 := bstep (se 4 (by rfl) ⟨1273122, by rfl⟩ : syracuseStep 13579973 = 2546245) B2546245
theorem B1488593 : Blo 988596 1488593 := bstep (se 2 (by rfl) ⟨558222, by rfl⟩ : syracuseStep 1488593 = 1116445) B1116445
theorem B1488611 : Blo 988596 1488611 := bstep (se 1 (by rfl) ⟨1116458, by rfl⟩ : syracuseStep 1488611 = 2232917) B2232917
theorem B1488641 : Blo 988596 1488641 := bstep (se 2 (by rfl) ⟨558240, by rfl⟩ : syracuseStep 1488641 = 1116481) B1116481
theorem B1488659 : Blo 988596 1488659 := bstep (se 1 (by rfl) ⟨1116494, by rfl⟩ : syracuseStep 1488659 = 2232989) B2232989
theorem B1488689 : Blo 988596 1488689 := bstep (se 2 (by rfl) ⟨558258, by rfl⟩ : syracuseStep 1488689 = 1116517) B1116517
theorem B1488707 : Blo 988596 1488707 := bstep (se 1 (by rfl) ⟨1116530, by rfl⟩ : syracuseStep 1488707 = 2233061) B2233061
theorem B1488737 : Blo 988596 1488737 := bstep (se 2 (by rfl) ⟨558276, by rfl⟩ : syracuseStep 1488737 = 1116553) B1116553
theorem B4011875 : Blo 988596 4011875 := bstep (se 1 (by rfl) ⟨3008906, by rfl⟩ : syracuseStep 4011875 = 6017813) B6017813
theorem B1488755 : Blo 988596 1488755 := bstep (se 1 (by rfl) ⟨1116566, by rfl⟩ : syracuseStep 1488755 = 2233133) B2233133
theorem B1488785 : Blo 988596 1488785 := bstep (se 2 (by rfl) ⟨558294, by rfl⟩ : syracuseStep 1488785 = 1116589) B1116589
theorem B1488803 : Blo 988596 1488803 := bstep (se 1 (by rfl) ⟨1116602, by rfl⟩ : syracuseStep 1488803 = 2233205) B2233205
theorem B1488833 : Blo 988596 1488833 := bstep (se 2 (by rfl) ⟨558312, by rfl⟩ : syracuseStep 1488833 = 1116625) B1116625
theorem B1488851 : Blo 988596 1488851 := bstep (se 1 (by rfl) ⟨1116638, by rfl⟩ : syracuseStep 1488851 = 2233277) B2233277
theorem B1488881 : Blo 988596 1488881 := bstep (se 2 (by rfl) ⟨558330, by rfl⟩ : syracuseStep 1488881 = 1116661) B1116661
theorem B1783811 : Blo 988596 1783811 := bstep (se 1 (by rfl) ⟨1337858, by rfl⟩ : syracuseStep 1783811 = 2675717) B2675717
theorem B2504753 : Blo 988596 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B2504803 : Blo 988596 2504803 := bstep (se 1 (by rfl) ⟨1878602, by rfl⟩ : syracuseStep 2504803 = 3757205) B3757205
theorem B1587347 : Blo 988596 1587347 := bstep (se 1 (by rfl) ⟨1190510, by rfl⟩ : syracuseStep 1587347 = 2381021) B2381021
theorem B2504945 : Blo 988596 2504945 := bstep (se 2 (by rfl) ⟨939354, by rfl⟩ : syracuseStep 2504945 = 1878709) B1878709
theorem B5355845 : Blo 988596 5355845 := bstep (se 4 (by rfl) ⟨502110, by rfl⟩ : syracuseStep 5355845 = 1004221) B1004221
theorem B1882673 : Blo 988596 1882673 := bstep (se 2 (by rfl) ⟨706002, by rfl⟩ : syracuseStep 1882673 = 1412005) B1412005
theorem B2538467 : Blo 988596 2538467 := bstep (se 1 (by rfl) ⟨1903850, by rfl⟩ : syracuseStep 2538467 = 3807701) B3807701
theorem B5356621 : Blo 988596 5356621 := bstep (se 3 (by rfl) ⟨1004366, by rfl⟩ : syracuseStep 5356621 = 2008733) B2008733
theorem B1588339 : Blo 988596 1588339 := bstep (se 1 (by rfl) ⟨1191254, by rfl⟩ : syracuseStep 1588339 = 2382509) B2382509
theorem B2505937 : Blo 988596 2505937 := bstep (se 2 (by rfl) ⟨939726, by rfl⟩ : syracuseStep 2505937 = 1879453) B1879453
theorem B21445859 : Blo 988596 21445859 := bstep (se 1 (by rfl) ⟨16084394, by rfl⟩ : syracuseStep 21445859 = 32168789) B32168789
theorem B2145571 : Blo 988596 2145571 := bstep (se 1 (by rfl) ⟨1609178, by rfl⟩ : syracuseStep 2145571 = 3218357) B3218357
theorem B1785137 : Blo 988596 1785137 := bstep (se 2 (by rfl) ⟨669426, by rfl⟩ : syracuseStep 1785137 = 1338853) B1338853
theorem B1883569 : Blo 988596 1883569 := bstep (se 2 (by rfl) ⟨706338, by rfl⟩ : syracuseStep 1883569 = 1412677) B1412677
theorem B2506211 : Blo 988596 2506211 := bstep (se 1 (by rfl) ⟨1879658, by rfl⟩ : syracuseStep 2506211 = 3759317) B3759317
theorem B1883729 : Blo 988596 1883729 := bstep (se 2 (by rfl) ⟨706398, by rfl⟩ : syracuseStep 1883729 = 1412797) B1412797
theorem B8470115 : Blo 988596 8470115 := bstep (se 1 (by rfl) ⟨6352586, by rfl⟩ : syracuseStep 8470115 = 12705173) B12705173
theorem B2506403 : Blo 988596 2506403 := bstep (se 1 (by rfl) ⟨1879802, by rfl⟩ : syracuseStep 2506403 = 3759605) B3759605
theorem B5652301 : Blo 988596 5652301 := bstep (se 3 (by rfl) ⟨1059806, by rfl⟩ : syracuseStep 5652301 = 2119613) B2119613
theorem B4013965 : Blo 988596 4013965 := bstep (se 3 (by rfl) ⟨752618, by rfl⟩ : syracuseStep 4013965 = 1505237) B1505237
theorem B1884131 : Blo 988596 1884131 := bstep (se 1 (by rfl) ⟨1413098, by rfl⟩ : syracuseStep 1884131 = 2826197) B2826197
theorem B1589249 : Blo 988596 1589249 := bstep (se 2 (by rfl) ⟨595968, by rfl⟩ : syracuseStep 1589249 = 1191937) B1191937
theorem B1589377 : Blo 988596 1589377 := bstep (se 2 (by rfl) ⟨596016, by rfl⟩ : syracuseStep 1589377 = 1192033) B1192033
theorem B16892387 : Blo 988596 16892387 := bstep (se 1 (by rfl) ⟨12669290, by rfl⟩ : syracuseStep 16892387 = 25338581) B25338581
theorem B6341105 : Blo 988596 6341105 := bstep (se 2 (by rfl) ⟨2377914, by rfl⟩ : syracuseStep 6341105 = 4755829) B4755829
theorem B2507345 : Blo 988596 2507345 := bstep (se 2 (by rfl) ⟨940254, by rfl⟩ : syracuseStep 2507345 = 1880509) B1880509
theorem B2507395 : Blo 988596 2507395 := bstep (se 1 (by rfl) ⟨1880546, by rfl⟩ : syracuseStep 2507395 = 3761093) B3761093
theorem B28525283 : Blo 988596 28525283 := bstep (se 1 (by rfl) ⟨21393962, by rfl⟩ : syracuseStep 28525283 = 42787925) B42787925
theorem B2114275 : Blo 988596 2114275 := bstep (se 1 (by rfl) ⟨1585706, by rfl⟩ : syracuseStep 2114275 = 3171413) B3171413
theorem B7619341 : Blo 988596 7619341 := bstep (se 3 (by rfl) ⟨1428626, by rfl⟩ : syracuseStep 7619341 = 2857253) B2857253
theorem B2507537 : Blo 988596 2507537 := bstep (se 2 (by rfl) ⟨940326, by rfl⟩ : syracuseStep 2507537 = 1880653) B1880653
theorem B18039779 : Blo 988596 18039779 := bstep (se 1 (by rfl) ⟨13529834, by rfl⟩ : syracuseStep 18039779 = 27059669) B27059669
theorem B6865955 : Blo 988596 6865955 := bstep (se 1 (by rfl) ⟨5149466, by rfl⟩ : syracuseStep 6865955 = 10298933) B10298933
theorem B6112547 : Blo 988596 6112547 := bstep (se 1 (by rfl) ⟨4584410, by rfl⟩ : syracuseStep 6112547 = 9168821) B9168821
theorem B4015651 : Blo 988596 4015651 := bstep (se 1 (by rfl) ⟨3011738, by rfl⟩ : syracuseStep 4015651 = 6023477) B6023477
theorem B2148049 : Blo 988596 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B2508529 : Blo 988596 2508529 := bstep (se 2 (by rfl) ⟨940698, by rfl⟩ : syracuseStep 2508529 = 1881397) B1881397
theorem B2869219 : Blo 988596 2869219 := bstep (se 1 (by rfl) ⟨2151914, by rfl⟩ : syracuseStep 2869219 = 4303829) B4303829
theorem B7129073 : Blo 988596 7129073 := bstep (se 2 (by rfl) ⟨2673402, by rfl⟩ : syracuseStep 7129073 = 5346805) B5346805
theorem B2508803 : Blo 988596 2508803 := bstep (se 1 (by rfl) ⟨1881602, by rfl⟩ : syracuseStep 2508803 = 3763205) B3763205
theorem B2508995 : Blo 988596 2508995 := bstep (se 1 (by rfl) ⟨1881746, by rfl⟩ : syracuseStep 2508995 = 3763493) B3763493
theorem B3754289 : Blo 988596 3754289 := bstep (se 2 (by rfl) ⟨1407858, by rfl⟩ : syracuseStep 3754289 = 2815717) B2815717
theorem B2116145 : Blo 988596 2116145 := bstep (se 2 (by rfl) ⟨793554, by rfl⟩ : syracuseStep 2116145 = 1587109) B1587109
theorem B1788497 : Blo 988596 1788497 := bstep (se 2 (by rfl) ⟨670686, by rfl⟩ : syracuseStep 1788497 = 1341373) B1341373
theorem B2673425 : Blo 988596 2673425 := bstep (se 2 (by rfl) ⟨1002534, by rfl⟩ : syracuseStep 2673425 = 2005069) B2005069
theorem B3754957 : Blo 988596 3754957 := bstep (se 3 (by rfl) ⟨704054, by rfl⟩ : syracuseStep 3754957 = 1408109) B1408109
theorem B2509937 : Blo 988596 2509937 := bstep (se 2 (by rfl) ⟨941226, by rfl⟩ : syracuseStep 2509937 = 1882453) B1882453
theorem B2673805 : Blo 988596 2673805 := bstep (se 3 (by rfl) ⟨501338, by rfl⟩ : syracuseStep 2673805 = 1002677) B1002677
theorem B2509987 : Blo 988596 2509987 := bstep (se 1 (by rfl) ⟨1882490, by rfl⟩ : syracuseStep 2509987 = 3764981) B3764981
theorem B2510129 : Blo 988596 2510129 := bstep (se 2 (by rfl) ⟨941298, by rfl⟩ : syracuseStep 2510129 = 1882597) B1882597
theorem B2379107 : Blo 988596 2379107 := bstep (se 1 (by rfl) ⟨1784330, by rfl⟩ : syracuseStep 2379107 = 3568661) B3568661
theorem B1527155 : Blo 988596 1527155 := bstep (se 1 (by rfl) ⟨1145366, by rfl⟩ : syracuseStep 1527155 = 2290733) B2290733
theorem B6344077 : Blo 988596 6344077 := bstep (se 3 (by rfl) ⟨1189514, by rfl⟩ : syracuseStep 6344077 = 2379029) B2379029
theorem B2117009 : Blo 988596 2117009 := bstep (se 2 (by rfl) ⟨793878, by rfl⟩ : syracuseStep 2117009 = 1587757) B1587757
theorem B3755747 : Blo 988596 3755747 := bstep (se 1 (by rfl) ⟨2816810, by rfl⟩ : syracuseStep 3755747 = 5633621) B5633621
theorem B3264241 : Blo 988596 3264241 := bstep (se 2 (by rfl) ⟨1224090, by rfl⟩ : syracuseStep 3264241 = 2448181) B2448181
theorem B13553477 : Blo 988596 13553477 := bstep (se 4 (by rfl) ⟨1270638, by rfl⟩ : syracuseStep 13553477 = 2541277) B2541277
theorem B1691585 : Blo 988596 1691585 := bstep (se 2 (by rfl) ⟨634344, by rfl⟩ : syracuseStep 1691585 = 1268689) B1268689
theorem B6443107 : Blo 988596 6443107 := bstep (se 1 (by rfl) ⟨4832330, by rfl⟩ : syracuseStep 6443107 = 9664661) B9664661
theorem B21418181 : Blo 988596 21418181 := bstep (se 4 (by rfl) ⟨2007954, by rfl⟩ : syracuseStep 21418181 = 4015909) B4015909
theorem B1003747 : Blo 988596 1003747 := bstep (se 1 (by rfl) ⟨752810, by rfl⟩ : syracuseStep 1003747 = 1505621) B1505621
theorem B2511121 : Blo 988596 2511121 := bstep (se 2 (by rfl) ⟨941670, by rfl⟩ : syracuseStep 2511121 = 1883341) B1883341
theorem B3756401 : Blo 988596 3756401 := bstep (se 2 (by rfl) ⟨1408650, by rfl⟩ : syracuseStep 3756401 = 2817301) B2817301
theorem B20304269 : Blo 988596 20304269 := bstep (se 3 (by rfl) ⟨3807050, by rfl⟩ : syracuseStep 20304269 = 7614101) B7614101
theorem B2511395 : Blo 988596 2511395 := bstep (se 1 (by rfl) ⟨1883546, by rfl⟩ : syracuseStep 2511395 = 3767093) B3767093
theorem B2380337 : Blo 988596 2380337 := bstep (se 2 (by rfl) ⟨892626, by rfl⟩ : syracuseStep 2380337 = 1785253) B1785253
theorem B1004083 : Blo 988596 1004083 := bstep (se 1 (by rfl) ⟨753062, by rfl⟩ : syracuseStep 1004083 = 1506125) B1506125
theorem B2118307 : Blo 988596 2118307 := bstep (se 1 (by rfl) ⟨1588730, by rfl⟩ : syracuseStep 2118307 = 3177461) B3177461
theorem B6771377 : Blo 988596 6771377 := bstep (se 2 (by rfl) ⟨2539266, by rfl⟩ : syracuseStep 6771377 = 5078533) B5078533
theorem B2511587 : Blo 988596 2511587 := bstep (se 1 (by rfl) ⟨1883690, by rfl⟩ : syracuseStep 2511587 = 3767381) B3767381
theorem B2380529 : Blo 988596 2380529 := bstep (se 2 (by rfl) ⟨892698, by rfl⟩ : syracuseStep 2380529 = 1785397) B1785397
theorem B1528561 : Blo 988596 1528561 := bstep (se 2 (by rfl) ⟨573210, by rfl⟩ : syracuseStep 1528561 = 1146421) B1146421
theorem B2675501 : Blo 988596 2675501 := bstep (se 3 (by rfl) ⟨501656, by rfl⟩ : syracuseStep 2675501 = 1003313) B1003313
theorem B3167171 : Blo 988596 3167171 := bstep (se 1 (by rfl) ⟨2375378, by rfl⟩ : syracuseStep 3167171 = 4750757) B4750757
theorem B11293667 : Blo 988596 11293667 := bstep (se 1 (by rfl) ⟨8470250, by rfl⟩ : syracuseStep 11293667 = 16940501) B16940501
theorem B1430641 : Blo 988596 1430641 := bstep (se 2 (by rfl) ⟨536490, by rfl⟩ : syracuseStep 1430641 = 1072981) B1072981
theorem B1430785 : Blo 988596 1430785 := bstep (se 2 (by rfl) ⟨536544, by rfl⟩ : syracuseStep 1430785 = 1073089) B1073089
theorem B14308721 : Blo 988596 14308721 := bstep (se 2 (by rfl) ⟨5365770, by rfl⟩ : syracuseStep 14308721 = 10731541) B10731541
theorem B2381251 : Blo 988596 2381251 := bstep (se 1 (by rfl) ⟨1785938, by rfl⟩ : syracuseStep 2381251 = 3571877) B3571877
theorem B6346309 : Blo 988596 6346309 := bstep (se 4 (by rfl) ⟨594966, by rfl⟩ : syracuseStep 6346309 = 1189933) B1189933
theorem B2578115 : Blo 988596 2578115 := bstep (se 1 (by rfl) ⟨1933586, by rfl⟩ : syracuseStep 2578115 = 3867173) B3867173
theorem B3757859 : Blo 988596 3757859 := bstep (se 1 (by rfl) ⟨2818394, by rfl⟩ : syracuseStep 3757859 = 5636789) B5636789
theorem B3757873 : Blo 988596 3757873 := bstep (se 2 (by rfl) ⟨1409202, by rfl⟩ : syracuseStep 3757873 = 2818405) B2818405
theorem B3168067 : Blo 988596 3168067 := bstep (se 1 (by rfl) ⟨2376050, by rfl⟩ : syracuseStep 3168067 = 4752101) B4752101
theorem B2119537 : Blo 988596 2119537 := bstep (se 2 (by rfl) ⟨794826, by rfl⟩ : syracuseStep 2119537 = 1589653) B1589653
theorem B13752773 : Blo 988596 13752773 := bstep (se 4 (by rfl) ⟨1289322, by rfl⟩ : syracuseStep 13752773 = 2578645) B2578645
theorem B2677265 : Blo 988596 2677265 := bstep (se 2 (by rfl) ⟨1003974, by rfl⟩ : syracuseStep 2677265 = 2007949) B2007949
theorem B3169169 : Blo 988596 3169169 := bstep (se 2 (by rfl) ⟨1188438, by rfl⟩ : syracuseStep 3169169 = 2376877) B2376877
theorem B3169297 : Blo 988596 3169297 := bstep (se 2 (by rfl) ⟨1188486, by rfl⟩ : syracuseStep 3169297 = 2376973) B2376973
theorem B3759331 : Blo 988596 3759331 := bstep (se 1 (by rfl) ⟨2819498, by rfl⟩ : syracuseStep 3759331 = 5638997) B5638997
theorem B4513229 : Blo 988596 4513229 := bstep (se 3 (by rfl) ⟨846230, by rfl⟩ : syracuseStep 4513229 = 1692461) B1692461
theorem B8478179 : Blo 988596 8478179 := bstep (se 1 (by rfl) ⟨6358634, by rfl⟩ : syracuseStep 8478179 = 12717269) B12717269
theorem B1204147 : Blo 988596 1204147 := bstep (se 1 (by rfl) ⟨903110, by rfl⟩ : syracuseStep 1204147 = 1806221) B1806221
theorem B3170285 : Blo 988596 3170285 := bstep (se 3 (by rfl) ⟨594428, by rfl⟩ : syracuseStep 3170285 = 1188857) B1188857
theorem B5005475 : Blo 988596 5005475 := bstep (se 1 (by rfl) ⟨3754106, by rfl⟩ : syracuseStep 5005475 = 7508213) B7508213
theorem B9527651 : Blo 988596 9527651 := bstep (se 1 (by rfl) ⟨7145738, by rfl⟩ : syracuseStep 9527651 = 14291477) B14291477
theorem B5006285 : Blo 988596 5006285 := bstep (se 3 (by rfl) ⟨938678, by rfl⟩ : syracuseStep 5006285 = 1877357) B1877357
theorem B1696835 : Blo 988596 1696835 := bstep (se 1 (by rfl) ⟨1272626, by rfl⟩ : syracuseStep 1696835 = 2545253) B2545253
theorem B3171629 : Blo 988596 3171629 := bstep (se 3 (by rfl) ⟨594680, by rfl⟩ : syracuseStep 3171629 = 1189361) B1189361
theorem B3761549 : Blo 988596 3761549 := bstep (se 3 (by rfl) ⟨705290, by rfl⟩ : syracuseStep 3761549 = 1410581) B1410581
theorem B2680237 : Blo 988596 2680237 := bstep (se 3 (by rfl) ⟨502544, by rfl⟩ : syracuseStep 2680237 = 1005089) B1005089
theorem B11888099 : Blo 988596 11888099 := bstep (se 1 (by rfl) ⟨8916074, by rfl⟩ : syracuseStep 11888099 = 17832149) B17832149
theorem B7530083 : Blo 988596 7530083 := bstep (se 1 (by rfl) ⟨5647562, by rfl⟩ : syracuseStep 7530083 = 11295125) B11295125
theorem B2680465 : Blo 988596 2680465 := bstep (se 2 (by rfl) ⟨1005174, by rfl⟩ : syracuseStep 2680465 = 2010349) B2010349
theorem B2942929 : Blo 988596 2942929 := bstep (se 2 (by rfl) ⟨1103598, by rfl⟩ : syracuseStep 2942929 = 2207197) B2207197
theorem B6023281 : Blo 988596 6023281 := bstep (se 2 (by rfl) ⟨2258730, by rfl⟩ : syracuseStep 6023281 = 4517461) B4517461
theorem B27519203 : Blo 988596 27519203 := bstep (se 1 (by rfl) ⟨20639402, by rfl⟩ : syracuseStep 27519203 = 41278805) B41278805
theorem B3008771 : Blo 988596 3008771 := bstep (se 1 (by rfl) ⟨2256578, by rfl⟩ : syracuseStep 3008771 = 4513157) B4513157
theorem B1337923 : Blo 988596 1337923 := bstep (se 1 (by rfl) ⟨1003442, by rfl⟩ : syracuseStep 1337923 = 2006885) B2006885
theorem B5630705 : Blo 988596 5630705 := bstep (se 2 (by rfl) ⟨2111514, by rfl⟩ : syracuseStep 5630705 = 4223029) B4223029
theorem B3337037 : Blo 988596 3337037 := bstep (se 3 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 3337037 = 1251389) B1251389
theorem B3173219 : Blo 988596 3173219 := bstep (se 1 (by rfl) ⟨2379914, by rfl⟩ : syracuseStep 3173219 = 4759829) B4759829
theorem B3337091 : Blo 988596 3337091 := bstep (se 1 (by rfl) ⟨2502818, by rfl⟩ : syracuseStep 3337091 = 5005637) B5005637
theorem B3337361 : Blo 988596 3337361 := bstep (se 2 (by rfl) ⟨1251510, by rfl⟩ : syracuseStep 3337361 = 2503021) B2503021
theorem B13200653 : Blo 988596 13200653 := bstep (se 3 (by rfl) ⟨2475122, by rfl⟩ : syracuseStep 13200653 = 4950245) B4950245
theorem B4288099 : Blo 988596 4288099 := bstep (se 1 (by rfl) ⟨3216074, by rfl⟩ : syracuseStep 4288099 = 6432149) B6432149
theorem B3173987 : Blo 988596 3173987 := bstep (se 1 (by rfl) ⟨2380490, by rfl⟩ : syracuseStep 3173987 = 4760981) B4760981
theorem B3337901 : Blo 988596 3337901 := bstep (se 3 (by rfl) ⟨625856, by rfl⟩ : syracuseStep 3337901 = 1251713) B1251713
theorem B3337955 : Blo 988596 3337955 := bstep (se 1 (by rfl) ⟨2503466, by rfl⟩ : syracuseStep 3337955 = 5006933) B5006933
theorem B5009201 : Blo 988596 5009201 := bstep (se 2 (by rfl) ⟨1878450, by rfl⟩ : syracuseStep 5009201 = 3756901) B3756901
theorem B8024035 : Blo 988596 8024035 := bstep (se 1 (by rfl) ⟨6018026, by rfl⟩ : syracuseStep 8024035 = 12036053) B12036053
theorem B4222961 : Blo 988596 4222961 := bstep (se 2 (by rfl) ⟨1583610, by rfl⟩ : syracuseStep 4222961 = 3167221) B3167221
theorem B3338225 : Blo 988596 3338225 := bstep (se 2 (by rfl) ⟨1251834, by rfl⟩ : syracuseStep 3338225 = 2503669) B2503669
theorem B3174385 : Blo 988596 3174385 := bstep (se 2 (by rfl) ⟨1190394, by rfl⟩ : syracuseStep 3174385 = 2380789) B2380789
theorem B3174499 : Blo 988596 3174499 := bstep (se 1 (by rfl) ⟨2380874, by rfl⟩ : syracuseStep 3174499 = 4761749) B4761749
theorem B5632163 : Blo 988596 5632163 := bstep (se 1 (by rfl) ⟨4224122, by rfl⟩ : syracuseStep 5632163 = 8448245) B8448245
theorem B3010765 : Blo 988596 3010765 := bstep (se 3 (by rfl) ⟨564518, by rfl⟩ : syracuseStep 3010765 = 1129037) B1129037
theorem B6025421 : Blo 988596 6025421 := bstep (se 3 (by rfl) ⟨1129766, by rfl⟩ : syracuseStep 6025421 = 2259533) B2259533
theorem B3764465 : Blo 988596 3764465 := bstep (se 2 (by rfl) ⟨1411674, by rfl⟩ : syracuseStep 3764465 = 2823349) B2823349
theorem B22868365 : Blo 988596 22868365 := bstep (se 3 (by rfl) ⟨4287818, by rfl⟩ : syracuseStep 22868365 = 8575637) B8575637
theorem B2224529 : Blo 988596 2224529 := bstep (se 2 (by rfl) ⟨834198, by rfl⟩ : syracuseStep 2224529 = 1668397) B1668397
theorem B2224547 : Blo 988596 2224547 := bstep (se 1 (by rfl) ⟨1668410, by rfl⟩ : syracuseStep 2224547 = 3336821) B3336821
theorem B3338765 : Blo 988596 3338765 := bstep (se 3 (by rfl) ⟨626018, by rfl⟩ : syracuseStep 3338765 = 1252037) B1252037
theorem B3011107 : Blo 988596 3011107 := bstep (se 1 (by rfl) ⟨2258330, by rfl⟩ : syracuseStep 3011107 = 4516661) B4516661
theorem B3338819 : Blo 988596 3338819 := bstep (se 1 (by rfl) ⟨2504114, by rfl⟩ : syracuseStep 3338819 = 5008229) B5008229
theorem B2224817 : Blo 988596 2224817 := bstep (se 2 (by rfl) ⟨834306, by rfl⟩ : syracuseStep 2224817 = 1668613) B1668613
theorem B2224835 : Blo 988596 2224835 := bstep (se 1 (by rfl) ⟨1668626, by rfl⟩ : syracuseStep 2224835 = 3337253) B3337253
theorem B3175217 : Blo 988596 3175217 := bstep (se 2 (by rfl) ⟨1190706, by rfl⟩ : syracuseStep 3175217 = 2381413) B2381413
theorem B3339089 : Blo 988596 3339089 := bstep (se 2 (by rfl) ⟨1252158, by rfl⟩ : syracuseStep 3339089 = 2504317) B2504317
theorem B2225105 : Blo 988596 2225105 := bstep (se 2 (by rfl) ⟨834414, by rfl⟩ : syracuseStep 2225105 = 1668829) B1668829
theorem B2225123 : Blo 988596 2225123 := bstep (se 1 (by rfl) ⟨1668842, by rfl⟩ : syracuseStep 2225123 = 3337685) B3337685
theorem B1504337 : Blo 988596 1504337 := bstep (se 2 (by rfl) ⟨564126, by rfl⟩ : syracuseStep 1504337 = 1128253) B1128253
theorem B1143923 : Blo 988596 1143923 := bstep (se 1 (by rfl) ⟨857942, by rfl⟩ : syracuseStep 1143923 = 1715885) B1715885
theorem B5633165 : Blo 988596 5633165 := bstep (se 3 (by rfl) ⟨1056218, by rfl⟩ : syracuseStep 5633165 = 2112437) B2112437
theorem B1668289 : Blo 988596 1668289 := bstep (se 2 (by rfl) ⟨625608, by rfl⟩ : syracuseStep 1668289 = 1251217) B1251217
theorem B6354125 : Blo 988596 6354125 := bstep (se 3 (by rfl) ⟨1191398, by rfl⟩ : syracuseStep 6354125 = 2382797) B2382797
theorem B1668323 : Blo 988596 1668323 := bstep (se 1 (by rfl) ⟨1251242, by rfl⟩ : syracuseStep 1668323 = 2502485) B2502485
theorem B5010659 : Blo 988596 5010659 := bstep (se 1 (by rfl) ⟨3757994, by rfl⟩ : syracuseStep 5010659 = 7515989) B7515989
theorem B2225393 : Blo 988596 2225393 := bstep (se 2 (by rfl) ⟨834522, by rfl⟩ : syracuseStep 2225393 = 1669045) B1669045
theorem B2225411 : Blo 988596 2225411 := bstep (se 1 (by rfl) ⟨1669058, by rfl⟩ : syracuseStep 2225411 = 3338117) B3338117
theorem B1471777 : Blo 988596 1471777 := bstep (se 2 (by rfl) ⟨551916, by rfl⟩ : syracuseStep 1471777 = 1103833) B1103833
theorem B3175757 : Blo 988596 3175757 := bstep (se 3 (by rfl) ⟨595454, by rfl⟩ : syracuseStep 3175757 = 1190909) B1190909
theorem B1668451 : Blo 988596 1668451 := bstep (se 1 (by rfl) ⟨1251338, by rfl⟩ : syracuseStep 1668451 = 2502677) B2502677
theorem B3339629 : Blo 988596 3339629 := bstep (se 3 (by rfl) ⟨626180, by rfl⟩ : syracuseStep 3339629 = 1252361) B1252361
theorem B3339683 : Blo 988596 3339683 := bstep (se 1 (by rfl) ⟨2504762, by rfl⟩ : syracuseStep 3339683 = 5009525) B5009525
theorem B1668593 : Blo 988596 1668593 := bstep (se 2 (by rfl) ⟨625722, by rfl⟩ : syracuseStep 1668593 = 1251445) B1251445
theorem B2225681 : Blo 988596 2225681 := bstep (se 2 (by rfl) ⟨834630, by rfl⟩ : syracuseStep 2225681 = 1669261) B1669261
theorem B2225699 : Blo 988596 2225699 := bstep (se 1 (by rfl) ⟨1669274, by rfl⟩ : syracuseStep 2225699 = 3338549) B3338549
theorem B9532997 : Blo 988596 9532997 := bstep (se 4 (by rfl) ⟨893718, by rfl⟩ : syracuseStep 9532997 = 1787437) B1787437
theorem B1668721 : Blo 988596 1668721 := bstep (se 2 (by rfl) ⟨625770, by rfl⟩ : syracuseStep 1668721 = 1251541) B1251541
theorem B6026885 : Blo 988596 6026885 := bstep (se 4 (by rfl) ⟨565020, by rfl⟩ : syracuseStep 6026885 = 1130041) B1130041
theorem B1668755 : Blo 988596 1668755 := bstep (se 1 (by rfl) ⟨1251566, by rfl⟩ : syracuseStep 1668755 = 2503133) B2503133
theorem B3765923 : Blo 988596 3765923 := bstep (se 1 (by rfl) ⟨2824442, by rfl⟩ : syracuseStep 3765923 = 5648885) B5648885
theorem B2815661 : Blo 988596 2815661 := bstep (se 3 (by rfl) ⟨527936, by rfl⟩ : syracuseStep 2815661 = 1055873) B1055873
theorem B3339953 : Blo 988596 3339953 := bstep (se 2 (by rfl) ⟨1252482, by rfl⟩ : syracuseStep 3339953 = 2504965) B2504965
theorem B1668883 : Blo 988596 1668883 := bstep (se 1 (by rfl) ⟨1251662, by rfl⟩ : syracuseStep 1668883 = 2503325) B2503325
theorem B2258723 : Blo 988596 2258723 := bstep (se 1 (by rfl) ⟨1694042, by rfl⟩ : syracuseStep 2258723 = 3388085) B3388085
theorem B2225969 : Blo 988596 2225969 := bstep (se 2 (by rfl) ⟨834738, by rfl⟩ : syracuseStep 2225969 = 1669477) B1669477
theorem B2225987 : Blo 988596 2225987 := bstep (se 1 (by rfl) ⟨1669490, by rfl⟩ : syracuseStep 2225987 = 3338981) B3338981
theorem B2815843 : Blo 988596 2815843 := bstep (se 1 (by rfl) ⟨2111882, by rfl⟩ : syracuseStep 2815843 = 4223765) B4223765
theorem B1669025 : Blo 988596 1669025 := bstep (se 2 (by rfl) ⟨625884, by rfl⟩ : syracuseStep 1669025 = 1251769) B1251769
theorem B5011469 : Blo 988596 5011469 := bstep (se 3 (by rfl) ⟨939650, by rfl⟩ : syracuseStep 5011469 = 1879301) B1879301
theorem B1669153 : Blo 988596 1669153 := bstep (se 2 (by rfl) ⟨625932, by rfl⟩ : syracuseStep 1669153 = 1251865) B1251865
theorem B1669187 : Blo 988596 1669187 := bstep (se 1 (by rfl) ⟨1251890, by rfl⟩ : syracuseStep 1669187 = 2503781) B2503781
theorem B7141445 : Blo 988596 7141445 := bstep (se 4 (by rfl) ⟨669510, by rfl⟩ : syracuseStep 7141445 = 1339021) B1339021
theorem B2226257 : Blo 988596 2226257 := bstep (se 2 (by rfl) ⟨834846, by rfl⟩ : syracuseStep 2226257 = 1669693) B1669693
theorem B2226275 : Blo 988596 2226275 := bstep (se 1 (by rfl) ⟨1669706, by rfl⟩ : syracuseStep 2226275 = 3339413) B3339413
theorem B1112179 : Blo 988596 1112179 := bstep (se 1 (by rfl) ⟨834134, by rfl⟩ : syracuseStep 1112179 = 1668269) B1668269
theorem B1669315 : Blo 988596 1669315 := bstep (se 1 (by rfl) ⟨1251986, by rfl⟩ : syracuseStep 1669315 = 2503973) B2503973
theorem B3340493 : Blo 988596 3340493 := bstep (se 3 (by rfl) ⟨626342, by rfl⟩ : syracuseStep 3340493 = 1252685) B1252685
theorem B1112323 : Blo 988596 1112323 := bstep (se 1 (by rfl) ⟨834242, by rfl⟩ : syracuseStep 1112323 = 1668485) B1668485
theorem B3340547 : Blo 988596 3340547 := bstep (se 1 (by rfl) ⟨2505410, by rfl⟩ : syracuseStep 3340547 = 5010821) B5010821
theorem B1145107 : Blo 988596 1145107 := bstep (se 1 (by rfl) ⟨858830, by rfl⟩ : syracuseStep 1145107 = 1717661) B1717661
theorem B2816333 : Blo 988596 2816333 := bstep (se 3 (by rfl) ⟨528062, by rfl⟩ : syracuseStep 2816333 = 1056125) B1056125
theorem B1669457 : Blo 988596 1669457 := bstep (se 2 (by rfl) ⟨626046, by rfl⟩ : syracuseStep 1669457 = 1252093) B1252093
theorem B2226545 : Blo 988596 2226545 := bstep (se 2 (by rfl) ⟨834954, by rfl⟩ : syracuseStep 2226545 = 1669909) B1669909
theorem B2226563 : Blo 988596 2226563 := bstep (se 1 (by rfl) ⟨1669922, by rfl⟩ : syracuseStep 2226563 = 3339845) B3339845
theorem B4225421 : Blo 988596 4225421 := bstep (se 3 (by rfl) ⟨792266, by rfl⟩ : syracuseStep 4225421 = 1584533) B1584533
theorem B1112467 : Blo 988596 1112467 := bstep (se 1 (by rfl) ⟨834350, by rfl⟩ : syracuseStep 1112467 = 1668701) B1668701
theorem B1669585 : Blo 988596 1669585 := bstep (se 2 (by rfl) ⟨626094, by rfl⟩ : syracuseStep 1669585 = 1252189) B1252189
theorem B1669619 : Blo 988596 1669619 := bstep (se 1 (by rfl) ⟨1252214, by rfl⟩ : syracuseStep 1669619 = 2504429) B2504429
theorem B3340817 : Blo 988596 3340817 := bstep (se 2 (by rfl) ⟨1252806, by rfl⟩ : syracuseStep 3340817 = 2505613) B2505613
theorem B1112611 : Blo 988596 1112611 := bstep (se 1 (by rfl) ⟨834458, by rfl⟩ : syracuseStep 1112611 = 1668917) B1668917
theorem B10844771 : Blo 988596 10844771 := bstep (se 1 (by rfl) ⟨8133578, by rfl⟩ : syracuseStep 10844771 = 16267157) B16267157
theorem B1669747 : Blo 988596 1669747 := bstep (se 1 (by rfl) ⟨1252310, by rfl⟩ : syracuseStep 1669747 = 2504621) B2504621
theorem B3766925 : Blo 988596 3766925 := bstep (se 3 (by rfl) ⟨706298, by rfl⟩ : syracuseStep 3766925 = 1412597) B1412597
theorem B2226833 : Blo 988596 2226833 := bstep (se 2 (by rfl) ⟨835062, by rfl⟩ : syracuseStep 2226833 = 1670125) B1670125
theorem B2226851 : Blo 988596 2226851 := bstep (se 1 (by rfl) ⟨1670138, by rfl⟩ : syracuseStep 2226851 = 3340277) B3340277
theorem B1407665 : Blo 988596 1407665 := bstep (se 2 (by rfl) ⟨527874, by rfl⟩ : syracuseStep 1407665 = 1055749) B1055749
theorem B1112755 : Blo 988596 1112755 := bstep (se 1 (by rfl) ⟨834566, by rfl⟩ : syracuseStep 1112755 = 1669133) B1669133
theorem B4225763 : Blo 988596 4225763 := bstep (se 1 (by rfl) ⟨3169322, by rfl⟩ : syracuseStep 4225763 = 6338645) B6338645
theorem B1669889 : Blo 988596 1669889 := bstep (se 2 (by rfl) ⟨626208, by rfl⟩ : syracuseStep 1669889 = 1252417) B1252417
theorem B1112899 : Blo 988596 1112899 := bstep (se 1 (by rfl) ⟨834674, by rfl⟩ : syracuseStep 1112899 = 1669349) B1669349
theorem B7535429 : Blo 988596 7535429 := bstep (se 4 (by rfl) ⟨706446, by rfl⟩ : syracuseStep 7535429 = 1412893) B1412893
theorem B1670017 : Blo 988596 1670017 := bstep (se 2 (by rfl) ⟨626256, by rfl⟩ : syracuseStep 1670017 = 1252513) B1252513
theorem B1670051 : Blo 988596 1670051 := bstep (se 1 (by rfl) ⟨1252538, by rfl⟩ : syracuseStep 1670051 = 2505077) B2505077
theorem B2227121 : Blo 988596 2227121 := bstep (se 2 (by rfl) ⟨835170, by rfl⟩ : syracuseStep 2227121 = 1670341) B1670341
theorem B2227139 : Blo 988596 2227139 := bstep (se 1 (by rfl) ⟨1670354, by rfl⟩ : syracuseStep 2227139 = 3340709) B3340709
theorem B1113043 : Blo 988596 1113043 := bstep (se 1 (by rfl) ⟨834782, by rfl⟩ : syracuseStep 1113043 = 1669565) B1669565
theorem B1670179 : Blo 988596 1670179 := bstep (se 1 (by rfl) ⟨1252634, by rfl⟩ : syracuseStep 1670179 = 2505269) B2505269
theorem B3341357 : Blo 988596 3341357 := bstep (se 3 (by rfl) ⟨626504, by rfl⟩ : syracuseStep 3341357 = 1253009) B1253009
theorem B4815949 : Blo 988596 4815949 := bstep (se 3 (by rfl) ⟨902990, by rfl⟩ : syracuseStep 4815949 = 1805981) B1805981
theorem B1113187 : Blo 988596 1113187 := bstep (se 1 (by rfl) ⟨834890, by rfl⟩ : syracuseStep 1113187 = 1669781) B1669781
theorem B3341411 : Blo 988596 3341411 := bstep (se 1 (by rfl) ⟨2506058, by rfl⟩ : syracuseStep 3341411 = 5012117) B5012117
theorem B1670321 : Blo 988596 1670321 := bstep (se 2 (by rfl) ⟨626370, by rfl⟩ : syracuseStep 1670321 = 1252741) B1252741
theorem B1408195 : Blo 988596 1408195 := bstep (se 1 (by rfl) ⟨1056146, by rfl⟩ : syracuseStep 1408195 = 2112293) B2112293
theorem B3177677 : Blo 988596 3177677 := bstep (se 3 (by rfl) ⟨595814, by rfl⟩ : syracuseStep 3177677 = 1191629) B1191629
theorem B2227409 : Blo 988596 2227409 := bstep (se 2 (by rfl) ⟨835278, by rfl⟩ : syracuseStep 2227409 = 1670557) B1670557
theorem B2227427 : Blo 988596 2227427 := bstep (se 1 (by rfl) ⟨1670570, by rfl⟩ : syracuseStep 2227427 = 3341141) B3341141
theorem B16088291 : Blo 988596 16088291 := bstep (se 1 (by rfl) ⟨12066218, by rfl⟩ : syracuseStep 16088291 = 24132437) B24132437
theorem B1113331 : Blo 988596 1113331 := bstep (se 1 (by rfl) ⟨834998, by rfl⟩ : syracuseStep 1113331 = 1669997) B1669997
theorem B1670449 : Blo 988596 1670449 := bstep (se 2 (by rfl) ⟨626418, by rfl⟩ : syracuseStep 1670449 = 1252837) B1252837
theorem B1670483 : Blo 988596 1670483 := bstep (se 1 (by rfl) ⟨1252862, by rfl⟩ : syracuseStep 1670483 = 2505725) B2505725
theorem B3341681 : Blo 988596 3341681 := bstep (se 2 (by rfl) ⟨1253130, by rfl⟩ : syracuseStep 3341681 = 2506261) B2506261
theorem B1113475 : Blo 988596 1113475 := bstep (se 1 (by rfl) ⟨835106, by rfl⟩ : syracuseStep 1113475 = 1670213) B1670213
theorem B1670611 : Blo 988596 1670611 := bstep (se 1 (by rfl) ⟨1252958, by rfl⟩ : syracuseStep 1670611 = 2505917) B2505917
theorem B2817517 : Blo 988596 2817517 := bstep (se 3 (by rfl) ⟨528284, by rfl⟩ : syracuseStep 2817517 = 1056569) B1056569
theorem B2227697 : Blo 988596 2227697 := bstep (se 2 (by rfl) ⟨835386, by rfl⟩ : syracuseStep 2227697 = 1670773) B1670773
theorem B2227715 : Blo 988596 2227715 := bstep (se 1 (by rfl) ⟨1670786, by rfl⟩ : syracuseStep 2227715 = 3341573) B3341573
theorem B8453645 : Blo 988596 8453645 := bstep (se 3 (by rfl) ⟨1585058, by rfl⟩ : syracuseStep 8453645 = 3170117) B3170117
theorem B1408531 : Blo 988596 1408531 := bstep (se 1 (by rfl) ⟨1056398, by rfl⟩ : syracuseStep 1408531 = 2112797) B2112797
theorem B1113619 : Blo 988596 1113619 := bstep (se 1 (by rfl) ⟨835214, by rfl⟩ : syracuseStep 1113619 = 1670429) B1670429
theorem B5144141 : Blo 988596 5144141 := bstep (se 3 (by rfl) ⟨964526, by rfl⟩ : syracuseStep 5144141 = 1929053) B1929053
theorem B1670753 : Blo 988596 1670753 := bstep (se 2 (by rfl) ⟨626532, by rfl⟩ : syracuseStep 1670753 = 1253065) B1253065
theorem B1113763 : Blo 988596 1113763 := bstep (se 1 (by rfl) ⟨835322, by rfl⟩ : syracuseStep 1113763 = 1670645) B1670645
theorem B1670881 : Blo 988596 1670881 := bstep (se 2 (by rfl) ⟨626580, by rfl⟩ : syracuseStep 1670881 = 1253161) B1253161
theorem B1670915 : Blo 988596 1670915 := bstep (se 1 (by rfl) ⟨1253186, by rfl⟩ : syracuseStep 1670915 = 2506373) B2506373
theorem B2227985 : Blo 988596 2227985 := bstep (se 2 (by rfl) ⟨835494, by rfl⟩ : syracuseStep 2227985 = 1670989) B1670989
theorem B2228003 : Blo 988596 2228003 := bstep (se 1 (by rfl) ⟨1671002, by rfl⟩ : syracuseStep 2228003 = 3342005) B3342005
theorem B1113907 : Blo 988596 1113907 := bstep (se 1 (by rfl) ⟨835430, by rfl⟩ : syracuseStep 1113907 = 1670861) B1670861
theorem B10714933 : Blo 988596 10714933 := bstep (se 5 (by rfl) ⟨502262, by rfl⟩ : syracuseStep 10714933 = 1004525) B1004525
theorem B1671043 : Blo 988596 1671043 := bstep (se 1 (by rfl) ⟨1253282, by rfl⟩ : syracuseStep 1671043 = 2506565) B2506565
theorem B3342221 : Blo 988596 3342221 := bstep (se 3 (by rfl) ⟨626666, by rfl⟩ : syracuseStep 3342221 = 1253333) B1253333
theorem B6422435 : Blo 988596 6422435 := bstep (se 1 (by rfl) ⟨4816826, by rfl⟩ : syracuseStep 6422435 = 9633653) B9633653
theorem B1114051 : Blo 988596 1114051 := bstep (se 1 (by rfl) ⟨835538, by rfl⟩ : syracuseStep 1114051 = 1671077) B1671077
theorem B3342275 : Blo 988596 3342275 := bstep (se 1 (by rfl) ⟨2506706, by rfl⟩ : syracuseStep 3342275 = 5013413) B5013413
theorem B5636081 : Blo 988596 5636081 := bstep (se 2 (by rfl) ⟨2113530, by rfl⟩ : syracuseStep 5636081 = 4227061) B4227061
theorem B1114123 : Blo 988596 1114123 := bstep (se 1 (by rfl) ⟨835592, by rfl⟩ : syracuseStep 1114123 = 1671185) B1671185
theorem B1114231 : Blo 988596 1114231 := bstep (se 1 (by rfl) ⟨835673, by rfl⟩ : syracuseStep 1114231 = 1671347) B1671347
theorem B2228363 : Blo 988596 2228363 := bstep (se 1 (by rfl) ⟨1671272, by rfl⟩ : syracuseStep 2228363 = 3342545) B3342545
theorem B2228417 : Blo 988596 2228417 := bstep (se 2 (by rfl) ⟨835656, by rfl⟩ : syracuseStep 2228417 = 1671313) B1671313
theorem B1114411 : Blo 988596 1114411 := bstep (se 1 (by rfl) ⟨835808, by rfl⟩ : syracuseStep 1114411 = 1671617) B1671617
theorem B4227403 : Blo 988596 4227403 := bstep (se 1 (by rfl) ⟨3170552, by rfl⟩ : syracuseStep 4227403 = 6341105) B6341105
theorem B1671563 : Blo 988596 1671563 := bstep (se 1 (by rfl) ⟨1253672, by rfl⟩ : syracuseStep 1671563 = 2507345) B2507345
theorem B1114519 : Blo 988596 1114519 := bstep (se 1 (by rfl) ⟨835889, by rfl⟩ : syracuseStep 1114519 = 1671779) B1671779
theorem B2228633 : Blo 988596 2228633 := bstep (se 2 (by rfl) ⟨835737, by rfl⟩ : syracuseStep 2228633 = 1671475) B1671475
theorem B2228723 : Blo 988596 2228723 := bstep (se 1 (by rfl) ⟨1671542, by rfl⟩ : syracuseStep 2228723 = 3343085) B3343085
theorem B1671691 : Blo 988596 1671691 := bstep (se 1 (by rfl) ⟨1253768, by rfl⟩ : syracuseStep 1671691 = 2507537) B2507537
theorem B2228759 : Blo 988596 2228759 := bstep (se 1 (by rfl) ⟨1671569, by rfl⟩ : syracuseStep 2228759 = 3343139) B3343139
theorem B5014061 : Blo 988596 5014061 := bstep (se 3 (by rfl) ⟨940136, by rfl⟩ : syracuseStep 5014061 = 1880273) B1880273
theorem B3342923 : Blo 988596 3342923 := bstep (se 1 (by rfl) ⟨2507192, by rfl⟩ : syracuseStep 3342923 = 5014385) B5014385
theorem B1114699 : Blo 988596 1114699 := bstep (se 1 (by rfl) ⟨836024, by rfl⟩ : syracuseStep 1114699 = 1672049) B1672049
theorem B4227677 : Blo 988596 4227677 := bstep (se 3 (by rfl) ⟨792689, by rfl⟩ : syracuseStep 4227677 = 1585379) B1585379
theorem B3179101 : Blo 988596 3179101 := bstep (se 3 (by rfl) ⟨596081, by rfl⟩ : syracuseStep 3179101 = 1192163) B1192163
theorem B12026519 : Blo 988596 12026519 := bstep (se 1 (by rfl) ⟨9019889, by rfl⟩ : syracuseStep 12026519 = 18039779) B18039779
theorem B1671833 : Blo 988596 1671833 := bstep (se 2 (by rfl) ⟨626937, by rfl⟩ : syracuseStep 1671833 = 1253875) B1253875
theorem B1114807 : Blo 988596 1114807 := bstep (se 1 (by rfl) ⟨836105, by rfl⟩ : syracuseStep 1114807 = 1672211) B1672211
theorem B2228939 : Blo 988596 2228939 := bstep (se 1 (by rfl) ⟨1671704, by rfl⟩ : syracuseStep 2228939 = 3343409) B3343409
theorem B2228993 : Blo 988596 2228993 := bstep (se 2 (by rfl) ⟨835872, by rfl⟩ : syracuseStep 2228993 = 1671745) B1671745
theorem B1508107 : Blo 988596 1508107 := bstep (se 1 (by rfl) ⟨1131080, by rfl⟩ : syracuseStep 1508107 = 2262161) B2262161
theorem B1671961 : Blo 988596 1671961 := bstep (se 2 (by rfl) ⟨626985, by rfl⟩ : syracuseStep 1671961 = 1253971) B1253971
theorem B1409881 : Blo 988596 1409881 := bstep (se 2 (by rfl) ⟨528705, by rfl⟩ : syracuseStep 1409881 = 1057411) B1057411
theorem B3343193 : Blo 988596 3343193 := bstep (se 2 (by rfl) ⟨1253697, by rfl⟩ : syracuseStep 3343193 = 2507395) B2507395
theorem B1114987 : Blo 988596 1114987 := bstep (se 1 (by rfl) ⟨836240, by rfl⟩ : syracuseStep 1114987 = 1672481) B1672481
theorem B1115095 : Blo 988596 1115095 := bstep (se 1 (by rfl) ⟨836321, by rfl⟩ : syracuseStep 1115095 = 1672643) B1672643
theorem B2819033 : Blo 988596 2819033 := bstep (se 2 (by rfl) ⟨1057137, by rfl⟩ : syracuseStep 2819033 = 2114275) B2114275
theorem B2229209 : Blo 988596 2229209 := bstep (se 2 (by rfl) ⟨835953, by rfl⟩ : syracuseStep 2229209 = 1671907) B1671907
theorem B10159121 : Blo 988596 10159121 := bstep (se 2 (by rfl) ⟨3809670, by rfl⟩ : syracuseStep 10159121 = 7619341) B7619341
theorem B2229299 : Blo 988596 2229299 := bstep (se 1 (by rfl) ⟨1671974, by rfl⟩ : syracuseStep 2229299 = 3343949) B3343949
theorem B3015755 : Blo 988596 3015755 := bstep (se 1 (by rfl) ⟨2261816, by rfl⟩ : syracuseStep 3015755 = 4523633) B4523633
theorem B2229335 : Blo 988596 2229335 := bstep (se 1 (by rfl) ⟨1672001, by rfl⟩ : syracuseStep 2229335 = 3344003) B3344003
theorem B5637221 : Blo 988596 5637221 := bstep (se 4 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 5637221 = 1056979) B1056979
theorem B1115275 : Blo 988596 1115275 := bstep (se 1 (by rfl) ⟨836456, by rfl⟩ : syracuseStep 1115275 = 1672913) B1672913
theorem B1115383 : Blo 988596 1115383 := bstep (se 1 (by rfl) ⟨836537, by rfl⟩ : syracuseStep 1115383 = 1673075) B1673075
theorem B2229515 : Blo 988596 2229515 := bstep (se 1 (by rfl) ⟨1672136, by rfl⟩ : syracuseStep 2229515 = 3344273) B3344273
theorem B2229569 : Blo 988596 2229569 := bstep (se 2 (by rfl) ⟨836088, by rfl⟩ : syracuseStep 2229569 = 1672177) B1672177
theorem B1672535 : Blo 988596 1672535 := bstep (se 1 (by rfl) ⟨1254401, by rfl⟩ : syracuseStep 1672535 = 2508803) B2508803
theorem B1115563 : Blo 988596 1115563 := bstep (se 1 (by rfl) ⟨836672, by rfl⟩ : syracuseStep 1115563 = 1673345) B1673345
theorem B1672663 : Blo 988596 1672663 := bstep (se 1 (by rfl) ⟨1254497, by rfl⟩ : syracuseStep 1672663 = 2508995) B2508995
theorem B3343895 : Blo 988596 3343895 := bstep (se 1 (by rfl) ⟨2507921, by rfl⟩ : syracuseStep 3343895 = 5015843) B5015843
theorem B1115671 : Blo 988596 1115671 := bstep (se 1 (by rfl) ⟨836753, by rfl⟩ : syracuseStep 1115671 = 1673507) B1673507
theorem B2229785 : Blo 988596 2229785 := bstep (se 2 (by rfl) ⟨836169, by rfl⟩ : syracuseStep 2229785 = 1672339) B1672339
theorem B2229875 : Blo 988596 2229875 := bstep (se 1 (by rfl) ⟨1672406, by rfl⟩ : syracuseStep 2229875 = 3344813) B3344813
theorem B40699523 : Blo 988596 40699523 := bstep (se 1 (by rfl) ⟨30524642, by rfl⟩ : syracuseStep 40699523 = 61049285) B61049285
theorem B2229911 : Blo 988596 2229911 := bstep (se 1 (by rfl) ⟨1672433, by rfl⟩ : syracuseStep 2229911 = 3344867) B3344867
theorem B1115851 : Blo 988596 1115851 := bstep (se 1 (by rfl) ⟨836888, by rfl⟩ : syracuseStep 1115851 = 1673777) B1673777
theorem B2819863 : Blo 988596 2819863 := bstep (se 1 (by rfl) ⟨2114897, by rfl⟩ : syracuseStep 2819863 = 4229795) B4229795
theorem B1115959 : Blo 988596 1115959 := bstep (se 1 (by rfl) ⟨836969, by rfl⟩ : syracuseStep 1115959 = 1673939) B1673939
theorem B2230091 : Blo 988596 2230091 := bstep (se 1 (by rfl) ⟨1672568, by rfl⟩ : syracuseStep 2230091 = 3345137) B3345137
theorem B2230145 : Blo 988596 2230145 := bstep (se 2 (by rfl) ⟨836304, by rfl⟩ : syracuseStep 2230145 = 1672609) B1672609
theorem B3573649 : Blo 988596 3573649 := bstep (se 2 (by rfl) ⟨1340118, by rfl⟩ : syracuseStep 3573649 = 2680237) B2680237
theorem B1116139 : Blo 988596 1116139 := bstep (se 1 (by rfl) ⟨837104, by rfl⟩ : syracuseStep 1116139 = 1674209) B1674209
theorem B3344435 : Blo 988596 3344435 := bstep (se 1 (by rfl) ⟨2508326, by rfl⟩ : syracuseStep 3344435 = 5016653) B5016653
theorem B1673291 : Blo 988596 1673291 := bstep (se 1 (by rfl) ⟨1254968, by rfl⟩ : syracuseStep 1673291 = 2509937) B2509937
theorem B1116247 : Blo 988596 1116247 := bstep (se 1 (by rfl) ⟨837185, by rfl⟩ : syracuseStep 1116247 = 1674371) B1674371
theorem B2230361 : Blo 988596 2230361 := bstep (se 2 (by rfl) ⟨836385, by rfl⟩ : syracuseStep 2230361 = 1672771) B1672771
theorem B2230451 : Blo 988596 2230451 := bstep (se 1 (by rfl) ⟨1672838, by rfl⟩ : syracuseStep 2230451 = 3345677) B3345677
theorem B3573953 : Blo 988596 3573953 := bstep (se 2 (by rfl) ⟨1340232, by rfl⟩ : syracuseStep 3573953 = 2680465) B2680465
theorem B1673419 : Blo 988596 1673419 := bstep (se 1 (by rfl) ⟨1255064, by rfl⟩ : syracuseStep 1673419 = 2510129) B2510129
theorem B2230487 : Blo 988596 2230487 := bstep (se 1 (by rfl) ⟨1672865, by rfl⟩ : syracuseStep 2230487 = 3345731) B3345731
theorem B1018103 : Blo 988596 1018103 := bstep (se 1 (by rfl) ⟨763577, by rfl⟩ : syracuseStep 1018103 = 1527155) B1527155
theorem B1411339 : Blo 988596 1411339 := bstep (se 1 (by rfl) ⟨1058504, by rfl⟩ : syracuseStep 1411339 = 2117009) B2117009
theorem B1116427 : Blo 988596 1116427 := bstep (se 1 (by rfl) ⟨837320, by rfl⟩ : syracuseStep 1116427 = 1674641) B1674641
theorem B3344705 : Blo 988596 3344705 := bstep (se 2 (by rfl) ⟨1254264, by rfl⟩ : syracuseStep 3344705 = 2508529) B2508529
theorem B1673561 : Blo 988596 1673561 := bstep (se 2 (by rfl) ⟨627585, by rfl⟩ : syracuseStep 1673561 = 1255171) B1255171
theorem B1116535 : Blo 988596 1116535 := bstep (se 1 (by rfl) ⟨837401, by rfl⟩ : syracuseStep 1116535 = 1674803) B1674803
theorem B2230667 : Blo 988596 2230667 := bstep (se 1 (by rfl) ⟨1673000, by rfl⟩ : syracuseStep 2230667 = 3346001) B3346001
theorem B2230721 : Blo 988596 2230721 := bstep (se 2 (by rfl) ⟨836520, by rfl⟩ : syracuseStep 2230721 = 1673041) B1673041
theorem B11274713 : Blo 988596 11274713 := bstep (se 2 (by rfl) ⟨4228017, by rfl⟩ : syracuseStep 11274713 = 8456035) B8456035
theorem B1673689 : Blo 988596 1673689 := bstep (se 2 (by rfl) ⟨627633, by rfl⟩ : syracuseStep 1673689 = 1255267) B1255267
theorem B2820683 : Blo 988596 2820683 := bstep (se 1 (by rfl) ⟨2115512, by rfl⟩ : syracuseStep 2820683 = 4231025) B4231025
theorem B2230937 : Blo 988596 2230937 := bstep (se 2 (by rfl) ⟨836601, by rfl⟩ : syracuseStep 2230937 = 1673203) B1673203
theorem B2231027 : Blo 988596 2231027 := bstep (se 1 (by rfl) ⟨1673270, by rfl⟩ : syracuseStep 2231027 = 3346541) B3346541
theorem B2231063 : Blo 988596 2231063 := bstep (se 1 (by rfl) ⟨1673297, by rfl⟩ : syracuseStep 2231063 = 3346595) B3346595
theorem B8031041 : Blo 988596 8031041 := bstep (se 2 (by rfl) ⟨3011640, by rfl⟩ : syracuseStep 8031041 = 6023281) B6023281
theorem B3345245 : Blo 988596 3345245 := bstep (se 3 (by rfl) ⟨627233, by rfl⟩ : syracuseStep 3345245 = 1254467) B1254467
theorem B4524893 : Blo 988596 4524893 := bstep (se 3 (by rfl) ⟨848417, by rfl⟩ : syracuseStep 4524893 = 1696835) B1696835
theorem B13536179 : Blo 988596 13536179 := bstep (se 1 (by rfl) ⟨10152134, by rfl⟩ : syracuseStep 13536179 = 20304269) B20304269
theorem B2231243 : Blo 988596 2231243 := bstep (se 1 (by rfl) ⟨1673432, by rfl⟩ : syracuseStep 2231243 = 3346865) B3346865
theorem B3050461 : Blo 988596 3050461 := bstep (se 3 (by rfl) ⟨571961, by rfl⟩ : syracuseStep 3050461 = 1143923) B1143923
theorem B2231297 : Blo 988596 2231297 := bstep (se 2 (by rfl) ⟨836736, by rfl⟩ : syracuseStep 2231297 = 1673473) B1673473
theorem B1674263 : Blo 988596 1674263 := bstep (se 1 (by rfl) ⟨1255697, by rfl⟩ : syracuseStep 1674263 = 2511395) B2511395
theorem B1674391 : Blo 988596 1674391 := bstep (se 1 (by rfl) ⟨1255793, by rfl⟩ : syracuseStep 1674391 = 2511587) B2511587
theorem B2231513 : Blo 988596 2231513 := bstep (se 2 (by rfl) ⟨836817, by rfl⟩ : syracuseStep 2231513 = 1673635) B1673635
theorem B2231603 : Blo 988596 2231603 := bstep (se 1 (by rfl) ⟨1673702, by rfl⟩ : syracuseStep 2231603 = 3347405) B3347405
theorem B2231639 : Blo 988596 2231639 := bstep (se 1 (by rfl) ⟨1673729, by rfl⟩ : syracuseStep 2231639 = 3347459) B3347459
theorem B1412569 : Blo 988596 1412569 := bstep (se 2 (by rfl) ⟨529713, by rfl⟩ : syracuseStep 1412569 = 1059427) B1059427
theorem B2231819 : Blo 988596 2231819 := bstep (se 1 (by rfl) ⟨1673864, by rfl⟩ : syracuseStep 2231819 = 3347729) B3347729
theorem B2231873 : Blo 988596 2231873 := bstep (se 2 (by rfl) ⟨836952, by rfl⟩ : syracuseStep 2231873 = 1673905) B1673905
theorem B9539147 : Blo 988596 9539147 := bstep (se 1 (by rfl) ⟨7154360, by rfl⟩ : syracuseStep 9539147 = 14308721) B14308721
theorem B2232089 : Blo 988596 2232089 := bstep (se 2 (by rfl) ⟨837033, by rfl⟩ : syracuseStep 2232089 = 1674067) B1674067
theorem B8458019 : Blo 988596 8458019 := bstep (se 1 (by rfl) ⟨6343514, by rfl⟩ : syracuseStep 8458019 = 12687029) B12687029
theorem B2232179 : Blo 988596 2232179 := bstep (se 1 (by rfl) ⟨1674134, by rfl⟩ : syracuseStep 2232179 = 3348269) B3348269
theorem B2232215 : Blo 988596 2232215 := bstep (se 1 (by rfl) ⟨1674161, by rfl⟩ : syracuseStep 2232215 = 3348323) B3348323
theorem B3346379 : Blo 988596 3346379 := bstep (se 1 (by rfl) ⟨2509784, by rfl⟩ : syracuseStep 3346379 = 5019569) B5019569
theorem B2232395 : Blo 988596 2232395 := bstep (se 1 (by rfl) ⟨1674296, by rfl⟩ : syracuseStep 2232395 = 3348593) B3348593
theorem B2232449 : Blo 988596 2232449 := bstep (se 2 (by rfl) ⟨837168, by rfl⟩ : syracuseStep 2232449 = 1674337) B1674337
theorem B4067545 : Blo 988596 4067545 := bstep (se 2 (by rfl) ⟨1525329, by rfl⟩ : syracuseStep 4067545 = 3050659) B3050659
theorem B3346649 : Blo 988596 3346649 := bstep (se 2 (by rfl) ⟨1254993, by rfl⟩ : syracuseStep 3346649 = 2509987) B2509987
theorem B2232665 : Blo 988596 2232665 := bstep (se 2 (by rfl) ⟨837249, by rfl⟩ : syracuseStep 2232665 = 1674499) B1674499
theorem B5017949 : Blo 988596 5017949 := bstep (se 3 (by rfl) ⟨940865, by rfl⟩ : syracuseStep 5017949 = 1881731) B1881731
theorem B2232755 : Blo 988596 2232755 := bstep (se 1 (by rfl) ⟨1674566, by rfl⟩ : syracuseStep 2232755 = 3349133) B3349133
theorem B2232791 : Blo 988596 2232791 := bstep (se 1 (by rfl) ⟨1674593, by rfl⟩ : syracuseStep 2232791 = 3349187) B3349187
theorem B8458769 : Blo 988596 8458769 := bstep (se 2 (by rfl) ⟨3172038, by rfl⟩ : syracuseStep 8458769 = 6344077) B6344077
theorem B2232971 : Blo 988596 2232971 := bstep (se 1 (by rfl) ⟨1674728, by rfl⟩ : syracuseStep 2232971 = 3349457) B3349457
theorem B2233025 : Blo 988596 2233025 := bstep (se 2 (by rfl) ⟨837384, by rfl⟩ : syracuseStep 2233025 = 1674769) B1674769
theorem B3347351 : Blo 988596 3347351 := bstep (se 1 (by rfl) ⟨2510513, by rfl⟩ : syracuseStep 3347351 = 5021027) B5021027
theorem B2233241 : Blo 988596 2233241 := bstep (se 2 (by rfl) ⟨837465, by rfl⟩ : syracuseStep 2233241 = 1674931) B1674931
theorem B2823133 : Blo 988596 2823133 := bstep (se 3 (by rfl) ⟨529337, by rfl⟩ : syracuseStep 2823133 = 1058675) B1058675
theorem B2233331 : Blo 988596 2233331 := bstep (se 1 (by rfl) ⟨1674998, by rfl⟩ : syracuseStep 2233331 = 3349997) B3349997
theorem B19010861 : Blo 988596 19010861 := bstep (se 3 (by rfl) ⟨3564536, by rfl⟩ : syracuseStep 19010861 = 7129073) B7129073
theorem B4232513 : Blo 988596 4232513 := bstep (se 2 (by rfl) ⟨1587192, by rfl⟩ : syracuseStep 4232513 = 3174385) B3174385
theorem B6034763 : Blo 988596 6034763 := bstep (se 1 (by rfl) ⟨4526072, by rfl⟩ : syracuseStep 6034763 = 9052145) B9052145
theorem B3347891 : Blo 988596 3347891 := bstep (se 1 (by rfl) ⟨2510918, by rfl⟩ : syracuseStep 3347891 = 5021837) B5021837
theorem B988599 : Blo 988596 988599 := bstep (se 1 (by rfl) ⟨741449, by rfl⟩ : syracuseStep 988599 = 1482899) B1482899
theorem B988619 : Blo 988596 988619 := bstep (se 1 (by rfl) ⟨741464, by rfl⟩ : syracuseStep 988619 = 1482929) B1482929
theorem B988631 : Blo 988596 988631 := bstep (se 1 (by rfl) ⟨741473, by rfl⟩ : syracuseStep 988631 = 1482947) B1482947
theorem B4232665 : Blo 988596 4232665 := bstep (se 2 (by rfl) ⟨1587249, by rfl⟩ : syracuseStep 4232665 = 3174499) B3174499
theorem B988651 : Blo 988596 988651 := bstep (se 1 (by rfl) ⟨741488, by rfl⟩ : syracuseStep 988651 = 1482977) B1482977
theorem B988663 : Blo 988596 988663 := bstep (se 1 (by rfl) ⟨741497, by rfl⟩ : syracuseStep 988663 = 1482995) B1482995
theorem B988683 : Blo 988596 988683 := bstep (se 1 (by rfl) ⟨741512, by rfl⟩ : syracuseStep 988683 = 1483025) B1483025
theorem B988695 : Blo 988596 988695 := bstep (se 1 (by rfl) ⟨741521, by rfl⟩ : syracuseStep 988695 = 1483043) B1483043
theorem B988715 : Blo 988596 988715 := bstep (se 1 (by rfl) ⟨741536, by rfl⟩ : syracuseStep 988715 = 1483073) B1483073
theorem B988727 : Blo 988596 988727 := bstep (se 1 (by rfl) ⟨741545, by rfl⟩ : syracuseStep 988727 = 1483091) B1483091
theorem B988747 : Blo 988596 988747 := bstep (se 1 (by rfl) ⟨741560, by rfl⟩ : syracuseStep 988747 = 1483121) B1483121
theorem B988759 : Blo 988596 988759 := bstep (se 1 (by rfl) ⟨741569, by rfl⟩ : syracuseStep 988759 = 1483139) B1483139
theorem B988779 : Blo 988596 988779 := bstep (se 1 (by rfl) ⟨741584, by rfl⟩ : syracuseStep 988779 = 1483169) B1483169
theorem B988791 : Blo 988596 988791 := bstep (se 1 (by rfl) ⟨741593, by rfl⟩ : syracuseStep 988791 = 1483187) B1483187
theorem B988811 : Blo 988596 988811 := bstep (se 1 (by rfl) ⟨741608, by rfl⟩ : syracuseStep 988811 = 1483217) B1483217
theorem B988823 : Blo 988596 988823 := bstep (se 1 (by rfl) ⟨741617, by rfl⟩ : syracuseStep 988823 = 1483235) B1483235
theorem B988843 : Blo 988596 988843 := bstep (se 1 (by rfl) ⟨741632, by rfl⟩ : syracuseStep 988843 = 1483265) B1483265
theorem B988855 : Blo 988596 988855 := bstep (se 1 (by rfl) ⟨741641, by rfl⟩ : syracuseStep 988855 = 1483283) B1483283
theorem B3348161 : Blo 988596 3348161 := bstep (se 2 (by rfl) ⟨1255560, by rfl⟩ : syracuseStep 3348161 = 2511121) B2511121
theorem B988875 : Blo 988596 988875 := bstep (se 1 (by rfl) ⟨741656, by rfl⟩ : syracuseStep 988875 = 1483313) B1483313
theorem B988887 : Blo 988596 988887 := bstep (se 1 (by rfl) ⟨741665, by rfl⟩ : syracuseStep 988887 = 1483331) B1483331
theorem B988907 : Blo 988596 988907 := bstep (se 1 (by rfl) ⟨741680, by rfl⟩ : syracuseStep 988907 = 1483361) B1483361
theorem B988919 : Blo 988596 988919 := bstep (se 1 (by rfl) ⟨741689, by rfl⟩ : syracuseStep 988919 = 1483379) B1483379
theorem B988939 : Blo 988596 988939 := bstep (se 1 (by rfl) ⟨741704, by rfl⟩ : syracuseStep 988939 = 1483409) B1483409
theorem B988951 : Blo 988596 988951 := bstep (se 1 (by rfl) ⟨741713, by rfl⟩ : syracuseStep 988951 = 1483427) B1483427
theorem B988971 : Blo 988596 988971 := bstep (se 1 (by rfl) ⟨741728, by rfl⟩ : syracuseStep 988971 = 1483457) B1483457
theorem B988983 : Blo 988596 988983 := bstep (se 1 (by rfl) ⟨741737, by rfl⟩ : syracuseStep 988983 = 1483475) B1483475
theorem B989003 : Blo 988596 989003 := bstep (se 1 (by rfl) ⟨741752, by rfl⟩ : syracuseStep 989003 = 1483505) B1483505
theorem B989015 : Blo 988596 989015 := bstep (se 1 (by rfl) ⟨741761, by rfl⟩ : syracuseStep 989015 = 1483523) B1483523
theorem B989035 : Blo 988596 989035 := bstep (se 1 (by rfl) ⟨741776, by rfl⟩ : syracuseStep 989035 = 1483553) B1483553
theorem B989047 : Blo 988596 989047 := bstep (se 1 (by rfl) ⟨741785, by rfl⟩ : syracuseStep 989047 = 1483571) B1483571
theorem B989067 : Blo 988596 989067 := bstep (se 1 (by rfl) ⟨741800, by rfl⟩ : syracuseStep 989067 = 1483601) B1483601
theorem B989079 : Blo 988596 989079 := bstep (se 1 (by rfl) ⟨741809, by rfl⟩ : syracuseStep 989079 = 1483619) B1483619
theorem B989099 : Blo 988596 989099 := bstep (se 1 (by rfl) ⟨741824, by rfl⟩ : syracuseStep 989099 = 1483649) B1483649
theorem B989111 : Blo 988596 989111 := bstep (se 1 (by rfl) ⟨741833, by rfl⟩ : syracuseStep 989111 = 1483667) B1483667
theorem B989131 : Blo 988596 989131 := bstep (se 1 (by rfl) ⟨741848, by rfl⟩ : syracuseStep 989131 = 1483697) B1483697
theorem B989143 : Blo 988596 989143 := bstep (se 1 (by rfl) ⟨741857, by rfl⟩ : syracuseStep 989143 = 1483715) B1483715
theorem B989163 : Blo 988596 989163 := bstep (se 1 (by rfl) ⟨741872, by rfl⟩ : syracuseStep 989163 = 1483745) B1483745
theorem B989175 : Blo 988596 989175 := bstep (se 1 (by rfl) ⟨741881, by rfl⟩ : syracuseStep 989175 = 1483763) B1483763
theorem B989195 : Blo 988596 989195 := bstep (se 1 (by rfl) ⟨741896, by rfl⟩ : syracuseStep 989195 = 1483793) B1483793
theorem B989207 : Blo 988596 989207 := bstep (se 1 (by rfl) ⟨741905, by rfl⟩ : syracuseStep 989207 = 1483811) B1483811
theorem B989227 : Blo 988596 989227 := bstep (se 1 (by rfl) ⟨741920, by rfl⟩ : syracuseStep 989227 = 1483841) B1483841
theorem B989239 : Blo 988596 989239 := bstep (se 1 (by rfl) ⟨741929, by rfl⟩ : syracuseStep 989239 = 1483859) B1483859
theorem B60889157 : Blo 988596 60889157 := bstep (se 4 (by rfl) ⟨5708358, by rfl⟩ : syracuseStep 60889157 = 11416717) B11416717
theorem B989259 : Blo 988596 989259 := bstep (se 1 (by rfl) ⟨741944, by rfl⟩ : syracuseStep 989259 = 1483889) B1483889
theorem B989271 : Blo 988596 989271 := bstep (se 1 (by rfl) ⟨741953, by rfl⟩ : syracuseStep 989271 = 1483907) B1483907
theorem B989291 : Blo 988596 989291 := bstep (se 1 (by rfl) ⟨741968, by rfl⟩ : syracuseStep 989291 = 1483937) B1483937
theorem B989303 : Blo 988596 989303 := bstep (se 1 (by rfl) ⟨741977, by rfl⟩ : syracuseStep 989303 = 1483955) B1483955
theorem B989323 : Blo 988596 989323 := bstep (se 1 (by rfl) ⟨741992, by rfl⟩ : syracuseStep 989323 = 1483985) B1483985
theorem B989335 : Blo 988596 989335 := bstep (se 1 (by rfl) ⟨742001, by rfl⟩ : syracuseStep 989335 = 1484003) B1484003
theorem B989355 : Blo 988596 989355 := bstep (se 1 (by rfl) ⟨742016, by rfl⟩ : syracuseStep 989355 = 1484033) B1484033
theorem B989367 : Blo 988596 989367 := bstep (se 1 (by rfl) ⟨742025, by rfl⟩ : syracuseStep 989367 = 1484051) B1484051
theorem B989387 : Blo 988596 989387 := bstep (se 1 (by rfl) ⟨742040, by rfl⟩ : syracuseStep 989387 = 1484081) B1484081
theorem B989399 : Blo 988596 989399 := bstep (se 1 (by rfl) ⟨742049, by rfl⟩ : syracuseStep 989399 = 1484099) B1484099
theorem B2824409 : Blo 988596 2824409 := bstep (se 2 (by rfl) ⟨1059153, by rfl⟩ : syracuseStep 2824409 = 2118307) B2118307
theorem B3348701 : Blo 988596 3348701 := bstep (se 3 (by rfl) ⟨627881, by rfl⟩ : syracuseStep 3348701 = 1255763) B1255763
theorem B989419 : Blo 988596 989419 := bstep (se 1 (by rfl) ⟨742064, by rfl⟩ : syracuseStep 989419 = 1484129) B1484129
theorem B989431 : Blo 988596 989431 := bstep (se 1 (by rfl) ⟨742073, by rfl⟩ : syracuseStep 989431 = 1484147) B1484147
theorem B989451 : Blo 988596 989451 := bstep (se 1 (by rfl) ⟨742088, by rfl⟩ : syracuseStep 989451 = 1484177) B1484177
theorem B1251607 : Blo 988596 1251607 := bstep (se 1 (by rfl) ⟨938705, by rfl⟩ : syracuseStep 1251607 = 1877411) B1877411
theorem B989463 : Blo 988596 989463 := bstep (se 1 (by rfl) ⟨742097, by rfl⟩ : syracuseStep 989463 = 1484195) B1484195
theorem B989483 : Blo 988596 989483 := bstep (se 1 (by rfl) ⟨742112, by rfl⟩ : syracuseStep 989483 = 1484225) B1484225
theorem B989495 : Blo 988596 989495 := bstep (se 1 (by rfl) ⟨742121, by rfl⟩ : syracuseStep 989495 = 1484243) B1484243
theorem B989515 : Blo 988596 989515 := bstep (se 1 (by rfl) ⟨742136, by rfl⟩ : syracuseStep 989515 = 1484273) B1484273
theorem B989527 : Blo 988596 989527 := bstep (se 1 (by rfl) ⟨742145, by rfl⟩ : syracuseStep 989527 = 1484291) B1484291
theorem B989547 : Blo 988596 989547 := bstep (se 1 (by rfl) ⟨742160, by rfl⟩ : syracuseStep 989547 = 1484321) B1484321
theorem B115677557 : Blo 988596 115677557 := bstep (se 5 (by rfl) ⟨5422385, by rfl⟩ : syracuseStep 115677557 = 10844771) B10844771
theorem B989559 : Blo 988596 989559 := bstep (se 1 (by rfl) ⟨742169, by rfl⟩ : syracuseStep 989559 = 1484339) B1484339
theorem B989579 : Blo 988596 989579 := bstep (se 1 (by rfl) ⟨742184, by rfl⟩ : syracuseStep 989579 = 1484369) B1484369
theorem B989591 : Blo 988596 989591 := bstep (se 1 (by rfl) ⟨742193, by rfl⟩ : syracuseStep 989591 = 1484387) B1484387
theorem B5020055 : Blo 988596 5020055 := bstep (se 1 (by rfl) ⟨3765041, by rfl⟩ : syracuseStep 5020055 = 7530083) B7530083
theorem B989611 : Blo 988596 989611 := bstep (se 1 (by rfl) ⟨742208, by rfl⟩ : syracuseStep 989611 = 1484417) B1484417
theorem B989623 : Blo 988596 989623 := bstep (se 1 (by rfl) ⟨742217, by rfl⟩ : syracuseStep 989623 = 1484435) B1484435
theorem B989643 : Blo 988596 989643 := bstep (se 1 (by rfl) ⟨742232, by rfl⟩ : syracuseStep 989643 = 1484465) B1484465
theorem B989655 : Blo 988596 989655 := bstep (se 1 (by rfl) ⟨742241, by rfl⟩ : syracuseStep 989655 = 1484483) B1484483
theorem B989675 : Blo 988596 989675 := bstep (se 1 (by rfl) ⟨742256, by rfl⟩ : syracuseStep 989675 = 1484513) B1484513
theorem B989687 : Blo 988596 989687 := bstep (se 1 (by rfl) ⟨742265, by rfl⟩ : syracuseStep 989687 = 1484531) B1484531
theorem B989707 : Blo 988596 989707 := bstep (se 1 (by rfl) ⟨742280, by rfl⟩ : syracuseStep 989707 = 1484561) B1484561
theorem B989719 : Blo 988596 989719 := bstep (se 1 (by rfl) ⟨742289, by rfl⟩ : syracuseStep 989719 = 1484579) B1484579
theorem B989739 : Blo 988596 989739 := bstep (se 1 (by rfl) ⟨742304, by rfl⟩ : syracuseStep 989739 = 1484609) B1484609
theorem B989751 : Blo 988596 989751 := bstep (se 1 (by rfl) ⟨742313, by rfl⟩ : syracuseStep 989751 = 1484627) B1484627
theorem B989771 : Blo 988596 989771 := bstep (se 1 (by rfl) ⟨742328, by rfl⟩ : syracuseStep 989771 = 1484657) B1484657
theorem B989783 : Blo 988596 989783 := bstep (se 1 (by rfl) ⟨742337, by rfl⟩ : syracuseStep 989783 = 1484675) B1484675
theorem B989803 : Blo 988596 989803 := bstep (se 1 (by rfl) ⟨742352, by rfl⟩ : syracuseStep 989803 = 1484705) B1484705
theorem B989815 : Blo 988596 989815 := bstep (se 1 (by rfl) ⟨742361, by rfl⟩ : syracuseStep 989815 = 1484723) B1484723
theorem B989835 : Blo 988596 989835 := bstep (se 1 (by rfl) ⟨742376, by rfl⟩ : syracuseStep 989835 = 1484753) B1484753
theorem B989847 : Blo 988596 989847 := bstep (se 1 (by rfl) ⟨742385, by rfl⟩ : syracuseStep 989847 = 1484771) B1484771
theorem B989867 : Blo 988596 989867 := bstep (se 1 (by rfl) ⟨742400, by rfl⟩ : syracuseStep 989867 = 1484801) B1484801
theorem B989879 : Blo 988596 989879 := bstep (se 1 (by rfl) ⟨742409, by rfl⟩ : syracuseStep 989879 = 1484819) B1484819
theorem B989899 : Blo 988596 989899 := bstep (se 1 (by rfl) ⟨742424, by rfl⟩ : syracuseStep 989899 = 1484849) B1484849
theorem B989911 : Blo 988596 989911 := bstep (se 1 (by rfl) ⟨742433, by rfl⟩ : syracuseStep 989911 = 1484867) B1484867
theorem B989931 : Blo 988596 989931 := bstep (se 1 (by rfl) ⟨742448, by rfl⟩ : syracuseStep 989931 = 1484897) B1484897
theorem B989943 : Blo 988596 989943 := bstep (se 1 (by rfl) ⟨742457, by rfl⟩ : syracuseStep 989943 = 1484915) B1484915
theorem B989963 : Blo 988596 989963 := bstep (se 1 (by rfl) ⟨742472, by rfl⟩ : syracuseStep 989963 = 1484945) B1484945
theorem B989975 : Blo 988596 989975 := bstep (se 1 (by rfl) ⟨742481, by rfl⟩ : syracuseStep 989975 = 1484963) B1484963
theorem B989995 : Blo 988596 989995 := bstep (se 1 (by rfl) ⟨742496, by rfl⟩ : syracuseStep 989995 = 1484993) B1484993
theorem B5643053 : Blo 988596 5643053 := bstep (se 3 (by rfl) ⟨1058072, by rfl⟩ : syracuseStep 5643053 = 2116145) B2116145
theorem B990007 : Blo 988596 990007 := bstep (se 1 (by rfl) ⟨742505, by rfl⟩ : syracuseStep 990007 = 1485011) B1485011
theorem B990027 : Blo 988596 990027 := bstep (se 1 (by rfl) ⟨742520, by rfl⟩ : syracuseStep 990027 = 1485041) B1485041
theorem B2005847 : Blo 988596 2005847 := bstep (se 1 (by rfl) ⟨1504385, by rfl⟩ : syracuseStep 2005847 = 3008771) B3008771
theorem B990039 : Blo 988596 990039 := bstep (se 1 (by rfl) ⟨742529, by rfl⟩ : syracuseStep 990039 = 1485059) B1485059
theorem B11443045 : Blo 988596 11443045 := bstep (se 4 (by rfl) ⟨1072785, by rfl⟩ : syracuseStep 11443045 = 2145571) B2145571
theorem B990059 : Blo 988596 990059 := bstep (se 1 (by rfl) ⟨742544, by rfl⟩ : syracuseStep 990059 = 1485089) B1485089
theorem B990071 : Blo 988596 990071 := bstep (se 1 (by rfl) ⟨742553, by rfl⟩ : syracuseStep 990071 = 1485107) B1485107
theorem B990091 : Blo 988596 990091 := bstep (se 1 (by rfl) ⟨742568, by rfl⟩ : syracuseStep 990091 = 1485137) B1485137
theorem B990103 : Blo 988596 990103 := bstep (se 1 (by rfl) ⟨742577, by rfl⟩ : syracuseStep 990103 = 1485155) B1485155
theorem B990123 : Blo 988596 990123 := bstep (se 1 (by rfl) ⟨742592, by rfl⟩ : syracuseStep 990123 = 1485185) B1485185
theorem B990135 : Blo 988596 990135 := bstep (se 1 (by rfl) ⟨742601, by rfl⟩ : syracuseStep 990135 = 1485203) B1485203
theorem B990155 : Blo 988596 990155 := bstep (se 1 (by rfl) ⟨742616, by rfl⟩ : syracuseStep 990155 = 1485233) B1485233
theorem B990167 : Blo 988596 990167 := bstep (se 1 (by rfl) ⟨742625, by rfl⟩ : syracuseStep 990167 = 1485251) B1485251
theorem B990187 : Blo 988596 990187 := bstep (se 1 (by rfl) ⟨742640, by rfl⟩ : syracuseStep 990187 = 1485281) B1485281
theorem B990199 : Blo 988596 990199 := bstep (se 1 (by rfl) ⟨742649, by rfl⟩ : syracuseStep 990199 = 1485299) B1485299
theorem B990219 : Blo 988596 990219 := bstep (se 1 (by rfl) ⟨742664, by rfl⟩ : syracuseStep 990219 = 1485329) B1485329
theorem B990231 : Blo 988596 990231 := bstep (se 1 (by rfl) ⟨742673, by rfl⟩ : syracuseStep 990231 = 1485347) B1485347
theorem B990251 : Blo 988596 990251 := bstep (se 1 (by rfl) ⟨742688, by rfl⟩ : syracuseStep 990251 = 1485377) B1485377
theorem B990263 : Blo 988596 990263 := bstep (se 1 (by rfl) ⟨742697, by rfl⟩ : syracuseStep 990263 = 1485395) B1485395
theorem B990283 : Blo 988596 990283 := bstep (se 1 (by rfl) ⟨742712, by rfl⟩ : syracuseStep 990283 = 1485425) B1485425
theorem B990295 : Blo 988596 990295 := bstep (se 1 (by rfl) ⟨742721, by rfl⟩ : syracuseStep 990295 = 1485443) B1485443
theorem B990315 : Blo 988596 990315 := bstep (se 1 (by rfl) ⟨742736, by rfl⟩ : syracuseStep 990315 = 1485473) B1485473
theorem B990327 : Blo 988596 990327 := bstep (se 1 (by rfl) ⟨742745, by rfl⟩ : syracuseStep 990327 = 1485491) B1485491
theorem B990347 : Blo 988596 990347 := bstep (se 1 (by rfl) ⟨742760, by rfl⟩ : syracuseStep 990347 = 1485521) B1485521
theorem B990359 : Blo 988596 990359 := bstep (se 1 (by rfl) ⟨742769, by rfl⟩ : syracuseStep 990359 = 1485539) B1485539
theorem B990379 : Blo 988596 990379 := bstep (se 1 (by rfl) ⟨742784, by rfl⟩ : syracuseStep 990379 = 1485569) B1485569
theorem B990391 : Blo 988596 990391 := bstep (se 1 (by rfl) ⟨742793, by rfl⟩ : syracuseStep 990391 = 1485587) B1485587
theorem B990411 : Blo 988596 990411 := bstep (se 1 (by rfl) ⟨742808, by rfl⟩ : syracuseStep 990411 = 1485617) B1485617
theorem B990423 : Blo 988596 990423 := bstep (se 1 (by rfl) ⟨742817, by rfl⟩ : syracuseStep 990423 = 1485635) B1485635
theorem B990443 : Blo 988596 990443 := bstep (se 1 (by rfl) ⟨742832, by rfl⟩ : syracuseStep 990443 = 1485665) B1485665
theorem B990455 : Blo 988596 990455 := bstep (se 1 (by rfl) ⟨742841, by rfl⟩ : syracuseStep 990455 = 1485683) B1485683
theorem B990475 : Blo 988596 990475 := bstep (se 1 (by rfl) ⟨742856, by rfl⟩ : syracuseStep 990475 = 1485713) B1485713
theorem B990487 : Blo 988596 990487 := bstep (se 1 (by rfl) ⟨742865, by rfl⟩ : syracuseStep 990487 = 1485731) B1485731
theorem B990507 : Blo 988596 990507 := bstep (se 1 (by rfl) ⟨742880, by rfl⟩ : syracuseStep 990507 = 1485761) B1485761
theorem B990519 : Blo 988596 990519 := bstep (se 1 (by rfl) ⟨742889, by rfl⟩ : syracuseStep 990519 = 1485779) B1485779
theorem B990539 : Blo 988596 990539 := bstep (se 1 (by rfl) ⟨742904, by rfl⟩ : syracuseStep 990539 = 1485809) B1485809
theorem B3349835 : Blo 988596 3349835 := bstep (se 1 (by rfl) ⟨2512376, by rfl⟩ : syracuseStep 3349835 = 5024753) B5024753
theorem B990551 : Blo 988596 990551 := bstep (se 1 (by rfl) ⟨742913, by rfl⟩ : syracuseStep 990551 = 1485827) B1485827
theorem B990571 : Blo 988596 990571 := bstep (se 1 (by rfl) ⟨742928, by rfl⟩ : syracuseStep 990571 = 1485857) B1485857
theorem B990583 : Blo 988596 990583 := bstep (se 1 (by rfl) ⟨742937, by rfl⟩ : syracuseStep 990583 = 1485875) B1485875
theorem B990603 : Blo 988596 990603 := bstep (se 1 (by rfl) ⟨742952, by rfl⟩ : syracuseStep 990603 = 1485905) B1485905
theorem B990615 : Blo 988596 990615 := bstep (se 1 (by rfl) ⟨742961, by rfl⟩ : syracuseStep 990615 = 1485923) B1485923
theorem B990635 : Blo 988596 990635 := bstep (se 1 (by rfl) ⟨742976, by rfl⟩ : syracuseStep 990635 = 1485953) B1485953
theorem B8461745 : Blo 988596 8461745 := bstep (se 2 (by rfl) ⟨3173154, by rfl⟩ : syracuseStep 8461745 = 6346309) B6346309
theorem B990647 : Blo 988596 990647 := bstep (se 1 (by rfl) ⟨742985, by rfl⟩ : syracuseStep 990647 = 1485971) B1485971
theorem B990667 : Blo 988596 990667 := bstep (se 1 (by rfl) ⟨743000, by rfl⟩ : syracuseStep 990667 = 1486001) B1486001
theorem B990679 : Blo 988596 990679 := bstep (se 1 (by rfl) ⟨743009, by rfl⟩ : syracuseStep 990679 = 1486019) B1486019
theorem B990699 : Blo 988596 990699 := bstep (se 1 (by rfl) ⟨743024, by rfl⟩ : syracuseStep 990699 = 1486049) B1486049
theorem B990711 : Blo 988596 990711 := bstep (se 1 (by rfl) ⟨743033, by rfl⟩ : syracuseStep 990711 = 1486067) B1486067
theorem B990731 : Blo 988596 990731 := bstep (se 1 (by rfl) ⟨743048, by rfl⟩ : syracuseStep 990731 = 1486097) B1486097
theorem B990743 : Blo 988596 990743 := bstep (se 1 (by rfl) ⟨743057, by rfl⟩ : syracuseStep 990743 = 1486115) B1486115
theorem B990763 : Blo 988596 990763 := bstep (se 1 (by rfl) ⟨743072, by rfl⟩ : syracuseStep 990763 = 1486145) B1486145
theorem B990775 : Blo 988596 990775 := bstep (se 1 (by rfl) ⟨743081, by rfl⟩ : syracuseStep 990775 = 1486163) B1486163
theorem B990795 : Blo 988596 990795 := bstep (se 1 (by rfl) ⟨743096, by rfl⟩ : syracuseStep 990795 = 1486193) B1486193
theorem B990807 : Blo 988596 990807 := bstep (se 1 (by rfl) ⟨743105, by rfl⟩ : syracuseStep 990807 = 1486211) B1486211
theorem B990827 : Blo 988596 990827 := bstep (se 1 (by rfl) ⟨743120, by rfl⟩ : syracuseStep 990827 = 1486241) B1486241
theorem B990839 : Blo 988596 990839 := bstep (se 1 (by rfl) ⟨743129, by rfl⟩ : syracuseStep 990839 = 1486259) B1486259
theorem B990859 : Blo 988596 990859 := bstep (se 1 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 990859 = 1486289) B1486289
theorem B990871 : Blo 988596 990871 := bstep (se 1 (by rfl) ⟨743153, by rfl⟩ : syracuseStep 990871 = 1486307) B1486307
theorem B990891 : Blo 988596 990891 := bstep (se 1 (by rfl) ⟨743168, by rfl⟩ : syracuseStep 990891 = 1486337) B1486337
theorem B990903 : Blo 988596 990903 := bstep (se 1 (by rfl) ⟨743177, by rfl⟩ : syracuseStep 990903 = 1486355) B1486355
theorem B990923 : Blo 988596 990923 := bstep (se 1 (by rfl) ⟨743192, by rfl⟩ : syracuseStep 990923 = 1486385) B1486385
theorem B990935 : Blo 988596 990935 := bstep (se 1 (by rfl) ⟨743201, by rfl⟩ : syracuseStep 990935 = 1486403) B1486403
theorem B990955 : Blo 988596 990955 := bstep (se 1 (by rfl) ⟨743216, by rfl⟩ : syracuseStep 990955 = 1486433) B1486433
theorem B990967 : Blo 988596 990967 := bstep (se 1 (by rfl) ⟨743225, by rfl⟩ : syracuseStep 990967 = 1486451) B1486451
theorem B990987 : Blo 988596 990987 := bstep (se 1 (by rfl) ⟨743240, by rfl⟩ : syracuseStep 990987 = 1486481) B1486481
theorem B990999 : Blo 988596 990999 := bstep (se 1 (by rfl) ⟨743249, by rfl⟩ : syracuseStep 990999 = 1486499) B1486499
theorem B991019 : Blo 988596 991019 := bstep (se 1 (by rfl) ⟨743264, by rfl⟩ : syracuseStep 991019 = 1486529) B1486529
theorem B991031 : Blo 988596 991031 := bstep (se 1 (by rfl) ⟨743273, by rfl⟩ : syracuseStep 991031 = 1486547) B1486547
theorem B2826049 : Blo 988596 2826049 := bstep (se 2 (by rfl) ⟨1059768, by rfl⟩ : syracuseStep 2826049 = 2119537) B2119537
theorem B991051 : Blo 988596 991051 := bstep (se 1 (by rfl) ⟨743288, by rfl⟩ : syracuseStep 991051 = 1486577) B1486577
theorem B991063 : Blo 988596 991063 := bstep (se 1 (by rfl) ⟨743297, by rfl⟩ : syracuseStep 991063 = 1486595) B1486595
theorem B991083 : Blo 988596 991083 := bstep (se 1 (by rfl) ⟨743312, by rfl⟩ : syracuseStep 991083 = 1486625) B1486625
theorem B991095 : Blo 988596 991095 := bstep (se 1 (by rfl) ⟨743321, by rfl⟩ : syracuseStep 991095 = 1486643) B1486643
theorem B991115 : Blo 988596 991115 := bstep (se 1 (by rfl) ⟨743336, by rfl⟩ : syracuseStep 991115 = 1486673) B1486673
theorem B991127 : Blo 988596 991127 := bstep (se 1 (by rfl) ⟨743345, by rfl⟩ : syracuseStep 991127 = 1486691) B1486691
theorem B991147 : Blo 988596 991147 := bstep (se 1 (by rfl) ⟨743360, by rfl⟩ : syracuseStep 991147 = 1486721) B1486721
theorem B991159 : Blo 988596 991159 := bstep (se 1 (by rfl) ⟨743369, by rfl⟩ : syracuseStep 991159 = 1486739) B1486739
theorem B1253323 : Blo 988596 1253323 := bstep (se 1 (by rfl) ⟨939992, by rfl⟩ : syracuseStep 1253323 = 1879985) B1879985
theorem B991179 : Blo 988596 991179 := bstep (se 1 (by rfl) ⟨743384, by rfl⟩ : syracuseStep 991179 = 1486769) B1486769
theorem B991191 : Blo 988596 991191 := bstep (se 1 (by rfl) ⟨743393, by rfl⟩ : syracuseStep 991191 = 1486787) B1486787
theorem B991211 : Blo 988596 991211 := bstep (se 1 (by rfl) ⟨743408, by rfl⟩ : syracuseStep 991211 = 1486817) B1486817
theorem B991223 : Blo 988596 991223 := bstep (se 1 (by rfl) ⟨743417, by rfl⟩ : syracuseStep 991223 = 1486835) B1486835
theorem B991243 : Blo 988596 991243 := bstep (se 1 (by rfl) ⟨743432, by rfl⟩ : syracuseStep 991243 = 1486865) B1486865
theorem B7741457 : Blo 988596 7741457 := bstep (se 2 (by rfl) ⟨2903046, by rfl⟩ : syracuseStep 7741457 = 5806093) B5806093
theorem B991255 : Blo 988596 991255 := bstep (se 1 (by rfl) ⟨743441, by rfl⟩ : syracuseStep 991255 = 1486883) B1486883
theorem B991275 : Blo 988596 991275 := bstep (se 1 (by rfl) ⟨743456, by rfl⟩ : syracuseStep 991275 = 1486913) B1486913
theorem B991287 : Blo 988596 991287 := bstep (se 1 (by rfl) ⟨743465, by rfl⟩ : syracuseStep 991287 = 1486931) B1486931
theorem B991307 : Blo 988596 991307 := bstep (se 1 (by rfl) ⟨743480, by rfl⟩ : syracuseStep 991307 = 1486961) B1486961
theorem B991319 : Blo 988596 991319 := bstep (se 1 (by rfl) ⟨743489, by rfl⟩ : syracuseStep 991319 = 1486979) B1486979
theorem B991339 : Blo 988596 991339 := bstep (se 1 (by rfl) ⟨743504, by rfl⟩ : syracuseStep 991339 = 1487009) B1487009
theorem B991351 : Blo 988596 991351 := bstep (se 1 (by rfl) ⟨743513, by rfl⟩ : syracuseStep 991351 = 1487027) B1487027
theorem B991371 : Blo 988596 991371 := bstep (se 1 (by rfl) ⟨743528, by rfl⟩ : syracuseStep 991371 = 1487057) B1487057
theorem B991383 : Blo 988596 991383 := bstep (se 1 (by rfl) ⟨743537, by rfl⟩ : syracuseStep 991383 = 1487075) B1487075
theorem B1482905 : Blo 988596 1482905 := bstep (se 2 (by rfl) ⟨556089, by rfl⟩ : syracuseStep 1482905 = 1112179) B1112179
theorem B991403 : Blo 988596 991403 := bstep (se 1 (by rfl) ⟨743552, by rfl⟩ : syracuseStep 991403 = 1487105) B1487105
theorem B991415 : Blo 988596 991415 := bstep (se 1 (by rfl) ⟨743561, by rfl⟩ : syracuseStep 991415 = 1487123) B1487123
theorem B991435 : Blo 988596 991435 := bstep (se 1 (by rfl) ⟨743576, by rfl⟩ : syracuseStep 991435 = 1487153) B1487153
theorem B991447 : Blo 988596 991447 := bstep (se 1 (by rfl) ⟨743585, by rfl⟩ : syracuseStep 991447 = 1487171) B1487171
theorem B991467 : Blo 988596 991467 := bstep (se 1 (by rfl) ⟨743600, by rfl⟩ : syracuseStep 991467 = 1487201) B1487201
theorem B991479 : Blo 988596 991479 := bstep (se 1 (by rfl) ⟨743609, by rfl⟩ : syracuseStep 991479 = 1487219) B1487219
theorem B1483019 : Blo 988596 1483019 := bstep (se 1 (by rfl) ⟨1112264, by rfl⟩ : syracuseStep 1483019 = 2224529) B2224529
theorem B991499 : Blo 988596 991499 := bstep (se 1 (by rfl) ⟨743624, by rfl⟩ : syracuseStep 991499 = 1487249) B1487249
theorem B1483031 : Blo 988596 1483031 := bstep (se 1 (by rfl) ⟨1112273, by rfl⟩ : syracuseStep 1483031 = 2224547) B2224547
theorem B991511 : Blo 988596 991511 := bstep (se 1 (by rfl) ⟨743633, by rfl⟩ : syracuseStep 991511 = 1487267) B1487267
theorem B991531 : Blo 988596 991531 := bstep (se 1 (by rfl) ⟨743648, by rfl⟩ : syracuseStep 991531 = 1487297) B1487297
theorem B991543 : Blo 988596 991543 := bstep (se 1 (by rfl) ⟨743657, by rfl⟩ : syracuseStep 991543 = 1487315) B1487315
theorem B991563 : Blo 988596 991563 := bstep (se 1 (by rfl) ⟨743672, by rfl⟩ : syracuseStep 991563 = 1487345) B1487345
theorem B991575 : Blo 988596 991575 := bstep (se 1 (by rfl) ⟨743681, by rfl⟩ : syracuseStep 991575 = 1487363) B1487363
theorem B1483097 : Blo 988596 1483097 := bstep (se 2 (by rfl) ⟨556161, by rfl⟩ : syracuseStep 1483097 = 1112323) B1112323
theorem B991595 : Blo 988596 991595 := bstep (se 1 (by rfl) ⟨743696, by rfl⟩ : syracuseStep 991595 = 1487393) B1487393
theorem B991607 : Blo 988596 991607 := bstep (se 1 (by rfl) ⟨743705, by rfl⟩ : syracuseStep 991607 = 1487411) B1487411
theorem B991627 : Blo 988596 991627 := bstep (se 1 (by rfl) ⟨743720, by rfl⟩ : syracuseStep 991627 = 1487441) B1487441
theorem B991639 : Blo 988596 991639 := bstep (se 1 (by rfl) ⟨743729, by rfl⟩ : syracuseStep 991639 = 1487459) B1487459
theorem B991659 : Blo 988596 991659 := bstep (se 1 (by rfl) ⟨743744, by rfl⟩ : syracuseStep 991659 = 1487489) B1487489
theorem B991671 : Blo 988596 991671 := bstep (se 1 (by rfl) ⟨743753, by rfl⟩ : syracuseStep 991671 = 1487507) B1487507
theorem B1483211 : Blo 988596 1483211 := bstep (se 1 (by rfl) ⟨1112408, by rfl⟩ : syracuseStep 1483211 = 2224817) B2224817
theorem B991691 : Blo 988596 991691 := bstep (se 1 (by rfl) ⟨743768, by rfl⟩ : syracuseStep 991691 = 1487537) B1487537
theorem B1483223 : Blo 988596 1483223 := bstep (se 1 (by rfl) ⟨1112417, by rfl⟩ : syracuseStep 1483223 = 2224835) B2224835
theorem B991703 : Blo 988596 991703 := bstep (se 1 (by rfl) ⟨743777, by rfl⟩ : syracuseStep 991703 = 1487555) B1487555
theorem B991723 : Blo 988596 991723 := bstep (se 1 (by rfl) ⟨743792, by rfl⟩ : syracuseStep 991723 = 1487585) B1487585
theorem B991735 : Blo 988596 991735 := bstep (se 1 (by rfl) ⟨743801, by rfl⟩ : syracuseStep 991735 = 1487603) B1487603
theorem B991755 : Blo 988596 991755 := bstep (se 1 (by rfl) ⟨743816, by rfl⟩ : syracuseStep 991755 = 1487633) B1487633
theorem B991767 : Blo 988596 991767 := bstep (se 1 (by rfl) ⟨743825, by rfl⟩ : syracuseStep 991767 = 1487651) B1487651
theorem B1483289 : Blo 988596 1483289 := bstep (se 2 (by rfl) ⟨556233, by rfl⟩ : syracuseStep 1483289 = 1112467) B1112467
theorem B991787 : Blo 988596 991787 := bstep (se 1 (by rfl) ⟨743840, by rfl⟩ : syracuseStep 991787 = 1487681) B1487681
theorem B991799 : Blo 988596 991799 := bstep (se 1 (by rfl) ⟨743849, by rfl⟩ : syracuseStep 991799 = 1487699) B1487699
theorem B991819 : Blo 988596 991819 := bstep (se 1 (by rfl) ⟨743864, by rfl⟩ : syracuseStep 991819 = 1487729) B1487729
theorem B991831 : Blo 988596 991831 := bstep (se 1 (by rfl) ⟨743873, by rfl⟩ : syracuseStep 991831 = 1487747) B1487747
theorem B991851 : Blo 988596 991851 := bstep (se 1 (by rfl) ⟨743888, by rfl⟩ : syracuseStep 991851 = 1487777) B1487777
theorem B991863 : Blo 988596 991863 := bstep (se 1 (by rfl) ⟨743897, by rfl⟩ : syracuseStep 991863 = 1487795) B1487795
theorem B1483403 : Blo 988596 1483403 := bstep (se 1 (by rfl) ⟨1112552, by rfl⟩ : syracuseStep 1483403 = 2225105) B2225105
theorem B991883 : Blo 988596 991883 := bstep (se 1 (by rfl) ⟨743912, by rfl⟩ : syracuseStep 991883 = 1487825) B1487825
theorem B1483415 : Blo 988596 1483415 := bstep (se 1 (by rfl) ⟨1112561, by rfl⟩ : syracuseStep 1483415 = 2225123) B2225123
theorem B991895 : Blo 988596 991895 := bstep (se 1 (by rfl) ⟨743921, by rfl⟩ : syracuseStep 991895 = 1487843) B1487843
theorem B991915 : Blo 988596 991915 := bstep (se 1 (by rfl) ⟨743936, by rfl⟩ : syracuseStep 991915 = 1487873) B1487873
theorem B991927 : Blo 988596 991927 := bstep (se 1 (by rfl) ⟨743945, by rfl⟩ : syracuseStep 991927 = 1487891) B1487891
theorem B1057483 : Blo 988596 1057483 := bstep (se 1 (by rfl) ⟨793112, by rfl⟩ : syracuseStep 1057483 = 1586225) B1586225
theorem B991947 : Blo 988596 991947 := bstep (se 1 (by rfl) ⟨743960, by rfl⟩ : syracuseStep 991947 = 1487921) B1487921
theorem B991959 : Blo 988596 991959 := bstep (se 1 (by rfl) ⟨743969, by rfl⟩ : syracuseStep 991959 = 1487939) B1487939
theorem B1483481 : Blo 988596 1483481 := bstep (se 2 (by rfl) ⟨556305, by rfl⟩ : syracuseStep 1483481 = 1112611) B1112611
theorem B991979 : Blo 988596 991979 := bstep (se 1 (by rfl) ⟨743984, by rfl⟩ : syracuseStep 991979 = 1487969) B1487969
theorem B991991 : Blo 988596 991991 := bstep (se 1 (by rfl) ⟨743993, by rfl⟩ : syracuseStep 991991 = 1487987) B1487987
theorem B7742213 : Blo 988596 7742213 := bstep (se 4 (by rfl) ⟨725832, by rfl⟩ : syracuseStep 7742213 = 1451665) B1451665
theorem B992011 : Blo 988596 992011 := bstep (se 1 (by rfl) ⟨744008, by rfl⟩ : syracuseStep 992011 = 1488017) B1488017
theorem B1188631 : Blo 988596 1188631 := bstep (se 1 (by rfl) ⟨891473, by rfl⟩ : syracuseStep 1188631 = 1782947) B1782947
theorem B992023 : Blo 988596 992023 := bstep (se 1 (by rfl) ⟨744017, by rfl⟩ : syracuseStep 992023 = 1488035) B1488035
theorem B992043 : Blo 988596 992043 := bstep (se 1 (by rfl) ⟨744032, by rfl⟩ : syracuseStep 992043 = 1488065) B1488065
theorem B4760365 : Blo 988596 4760365 := bstep (se 3 (by rfl) ⟨892568, by rfl⟩ : syracuseStep 4760365 = 1785137) B1785137
theorem B4236083 : Blo 988596 4236083 := bstep (se 1 (by rfl) ⟨3177062, by rfl⟩ : syracuseStep 4236083 = 6354125) B6354125
theorem B992055 : Blo 988596 992055 := bstep (se 1 (by rfl) ⟨744041, by rfl⟩ : syracuseStep 992055 = 1488083) B1488083
theorem B1483595 : Blo 988596 1483595 := bstep (se 1 (by rfl) ⟨1112696, by rfl⟩ : syracuseStep 1483595 = 2225393) B2225393
theorem B992075 : Blo 988596 992075 := bstep (se 1 (by rfl) ⟨744056, by rfl⟩ : syracuseStep 992075 = 1488113) B1488113
theorem B1483607 : Blo 988596 1483607 := bstep (se 1 (by rfl) ⟨1112705, by rfl⟩ : syracuseStep 1483607 = 2225411) B2225411
theorem B992087 : Blo 988596 992087 := bstep (se 1 (by rfl) ⟨744065, by rfl⟩ : syracuseStep 992087 = 1488131) B1488131
theorem B992107 : Blo 988596 992107 := bstep (se 1 (by rfl) ⟨744080, by rfl⟩ : syracuseStep 992107 = 1488161) B1488161
theorem B992119 : Blo 988596 992119 := bstep (se 1 (by rfl) ⟨744089, by rfl⟩ : syracuseStep 992119 = 1488179) B1488179
theorem B992139 : Blo 988596 992139 := bstep (se 1 (by rfl) ⟨744104, by rfl⟩ : syracuseStep 992139 = 1488209) B1488209
theorem B1254295 : Blo 988596 1254295 := bstep (se 1 (by rfl) ⟨940721, by rfl⟩ : syracuseStep 1254295 = 1881443) B1881443
theorem B992151 : Blo 988596 992151 := bstep (se 1 (by rfl) ⟨744113, by rfl⟩ : syracuseStep 992151 = 1488227) B1488227
theorem B1483673 : Blo 988596 1483673 := bstep (se 2 (by rfl) ⟨556377, by rfl⟩ : syracuseStep 1483673 = 1112755) B1112755
theorem B992171 : Blo 988596 992171 := bstep (se 1 (by rfl) ⟨744128, by rfl⟩ : syracuseStep 992171 = 1488257) B1488257
theorem B992183 : Blo 988596 992183 := bstep (se 1 (by rfl) ⟨744137, by rfl⟩ : syracuseStep 992183 = 1488275) B1488275
theorem B992203 : Blo 988596 992203 := bstep (se 1 (by rfl) ⟨744152, by rfl⟩ : syracuseStep 992203 = 1488305) B1488305
theorem B1188823 : Blo 988596 1188823 := bstep (se 1 (by rfl) ⟨891617, by rfl⟩ : syracuseStep 1188823 = 1783235) B1783235
theorem B992215 : Blo 988596 992215 := bstep (se 1 (by rfl) ⟨744161, by rfl⟩ : syracuseStep 992215 = 1488323) B1488323
theorem B992235 : Blo 988596 992235 := bstep (se 1 (by rfl) ⟨744176, by rfl⟩ : syracuseStep 992235 = 1488353) B1488353
theorem B992247 : Blo 988596 992247 := bstep (se 1 (by rfl) ⟨744185, by rfl⟩ : syracuseStep 992247 = 1488371) B1488371
theorem B1483787 : Blo 988596 1483787 := bstep (se 1 (by rfl) ⟨1112840, by rfl⟩ : syracuseStep 1483787 = 2225681) B2225681
theorem B992267 : Blo 988596 992267 := bstep (se 1 (by rfl) ⟨744200, by rfl⟩ : syracuseStep 992267 = 1488401) B1488401
theorem B1483799 : Blo 988596 1483799 := bstep (se 1 (by rfl) ⟨1112849, by rfl⟩ : syracuseStep 1483799 = 2225699) B2225699
theorem B992279 : Blo 988596 992279 := bstep (se 1 (by rfl) ⟨744209, by rfl⟩ : syracuseStep 992279 = 1488419) B1488419
theorem B992299 : Blo 988596 992299 := bstep (se 1 (by rfl) ⟨744224, by rfl⟩ : syracuseStep 992299 = 1488449) B1488449
theorem B992311 : Blo 988596 992311 := bstep (se 1 (by rfl) ⟨744233, by rfl⟩ : syracuseStep 992311 = 1488467) B1488467
theorem B992331 : Blo 988596 992331 := bstep (se 1 (by rfl) ⟨744248, by rfl⟩ : syracuseStep 992331 = 1488497) B1488497
theorem B992343 : Blo 988596 992343 := bstep (se 1 (by rfl) ⟨744257, by rfl⟩ : syracuseStep 992343 = 1488515) B1488515
theorem B1483865 : Blo 988596 1483865 := bstep (se 2 (by rfl) ⟨556449, by rfl⟩ : syracuseStep 1483865 = 1112899) B1112899
theorem B992363 : Blo 988596 992363 := bstep (se 1 (by rfl) ⟨744272, by rfl⟩ : syracuseStep 992363 = 1488545) B1488545
theorem B1877107 : Blo 988596 1877107 := bstep (se 1 (by rfl) ⟨1407830, by rfl⟩ : syracuseStep 1877107 = 2815661) B2815661
theorem B992375 : Blo 988596 992375 := bstep (se 1 (by rfl) ⟨744281, by rfl⟩ : syracuseStep 992375 = 1488563) B1488563
theorem B9053315 : Blo 988596 9053315 := bstep (se 1 (by rfl) ⟨6789986, by rfl⟩ : syracuseStep 9053315 = 13579973) B13579973
theorem B992395 : Blo 988596 992395 := bstep (se 1 (by rfl) ⟨744296, by rfl⟩ : syracuseStep 992395 = 1488593) B1488593
theorem B992407 : Blo 988596 992407 := bstep (se 1 (by rfl) ⟨744305, by rfl⟩ : syracuseStep 992407 = 1488611) B1488611
theorem B992427 : Blo 988596 992427 := bstep (se 1 (by rfl) ⟨744320, by rfl⟩ : syracuseStep 992427 = 1488641) B1488641
theorem B992439 : Blo 988596 992439 := bstep (se 1 (by rfl) ⟨744329, by rfl⟩ : syracuseStep 992439 = 1488659) B1488659
theorem B1483979 : Blo 988596 1483979 := bstep (se 1 (by rfl) ⟨1112984, by rfl⟩ : syracuseStep 1483979 = 2225969) B2225969
theorem B992459 : Blo 988596 992459 := bstep (se 1 (by rfl) ⟨744344, by rfl⟩ : syracuseStep 992459 = 1488689) B1488689
theorem B1483991 : Blo 988596 1483991 := bstep (se 1 (by rfl) ⟨1112993, by rfl⟩ : syracuseStep 1483991 = 2225987) B2225987
theorem B992471 : Blo 988596 992471 := bstep (se 1 (by rfl) ⟨744353, by rfl⟩ : syracuseStep 992471 = 1488707) B1488707
theorem B992491 : Blo 988596 992491 := bstep (se 1 (by rfl) ⟨744368, by rfl⟩ : syracuseStep 992491 = 1488737) B1488737
theorem B992503 : Blo 988596 992503 := bstep (se 1 (by rfl) ⟨744377, by rfl⟩ : syracuseStep 992503 = 1488755) B1488755
theorem B992523 : Blo 988596 992523 := bstep (se 1 (by rfl) ⟨744392, by rfl⟩ : syracuseStep 992523 = 1488785) B1488785
theorem B992535 : Blo 988596 992535 := bstep (se 1 (by rfl) ⟨744401, by rfl⟩ : syracuseStep 992535 = 1488803) B1488803
theorem B1484057 : Blo 988596 1484057 := bstep (se 2 (by rfl) ⟨556521, by rfl⟩ : syracuseStep 1484057 = 1113043) B1113043
theorem B992555 : Blo 988596 992555 := bstep (se 1 (by rfl) ⟨744416, by rfl⟩ : syracuseStep 992555 = 1488833) B1488833
theorem B992567 : Blo 988596 992567 := bstep (se 1 (by rfl) ⟨744425, by rfl⟩ : syracuseStep 992567 = 1488851) B1488851
theorem B992587 : Blo 988596 992587 := bstep (se 1 (by rfl) ⟨744440, by rfl⟩ : syracuseStep 992587 = 1488881) B1488881
theorem B1189207 : Blo 988596 1189207 := bstep (se 1 (by rfl) ⟨891905, by rfl⟩ : syracuseStep 1189207 = 1783811) B1783811
theorem B4760963 : Blo 988596 4760963 := bstep (se 1 (by rfl) ⟨3570722, by rfl⟩ : syracuseStep 4760963 = 7141445) B7141445
theorem B1484171 : Blo 988596 1484171 := bstep (se 1 (by rfl) ⟨1113128, by rfl⟩ : syracuseStep 1484171 = 2226257) B2226257
theorem B1484183 : Blo 988596 1484183 := bstep (se 1 (by rfl) ⟨1113137, by rfl⟩ : syracuseStep 1484183 = 2226275) B2226275
theorem B1058231 : Blo 988596 1058231 := bstep (se 1 (by rfl) ⟨793673, by rfl⟩ : syracuseStep 1058231 = 1587347) B1587347
theorem B1484249 : Blo 988596 1484249 := bstep (se 2 (by rfl) ⟨556593, by rfl⟩ : syracuseStep 1484249 = 1113187) B1113187
theorem B1877555 : Blo 988596 1877555 := bstep (se 1 (by rfl) ⟨1408166, by rfl⟩ : syracuseStep 1877555 = 2816333) B2816333
theorem B1484363 : Blo 988596 1484363 := bstep (se 1 (by rfl) ⟨1113272, by rfl⟩ : syracuseStep 1484363 = 2226545) B2226545
theorem B1484375 : Blo 988596 1484375 := bstep (se 1 (by rfl) ⟨1113281, by rfl⟩ : syracuseStep 1484375 = 2226563) B2226563
theorem B1877593 : Blo 988596 1877593 := bstep (se 2 (by rfl) ⟨704097, by rfl⟩ : syracuseStep 1877593 = 1408195) B1408195
theorem B1484441 : Blo 988596 1484441 := bstep (se 2 (by rfl) ⟨556665, by rfl⟩ : syracuseStep 1484441 = 1113331) B1113331
theorem B1255115 : Blo 988596 1255115 := bstep (se 1 (by rfl) ⟨941336, by rfl⟩ : syracuseStep 1255115 = 1882673) B1882673
theorem B1484555 : Blo 988596 1484555 := bstep (se 1 (by rfl) ⟨1113416, by rfl⟩ : syracuseStep 1484555 = 2226833) B2226833
theorem B1484567 : Blo 988596 1484567 := bstep (se 1 (by rfl) ⟨1113425, by rfl⟩ : syracuseStep 1484567 = 2226851) B2226851
theorem B1484633 : Blo 988596 1484633 := bstep (se 2 (by rfl) ⟨556737, by rfl⟩ : syracuseStep 1484633 = 1113475) B1113475
theorem B5023619 : Blo 988596 5023619 := bstep (se 1 (by rfl) ⟨3767714, by rfl⟩ : syracuseStep 5023619 = 7535429) B7535429
theorem B1484747 : Blo 988596 1484747 := bstep (se 1 (by rfl) ⟨1113560, by rfl⟩ : syracuseStep 1484747 = 2227121) B2227121
theorem B1484759 : Blo 988596 1484759 := bstep (se 1 (by rfl) ⟨1113569, by rfl⟩ : syracuseStep 1484759 = 2227139) B2227139
theorem B1878041 : Blo 988596 1878041 := bstep (se 2 (by rfl) ⟨704265, by rfl⟩ : syracuseStep 1878041 = 1408531) B1408531
theorem B1484825 : Blo 988596 1484825 := bstep (se 2 (by rfl) ⟨556809, by rfl⟩ : syracuseStep 1484825 = 1113619) B1113619
theorem B1484939 : Blo 988596 1484939 := bstep (se 1 (by rfl) ⟨1113704, by rfl⟩ : syracuseStep 1484939 = 2227409) B2227409
theorem B1484951 : Blo 988596 1484951 := bstep (se 1 (by rfl) ⟨1113713, by rfl⟩ : syracuseStep 1484951 = 2227427) B2227427
theorem B14297239 : Blo 988596 14297239 := bstep (se 1 (by rfl) ⟨10722929, by rfl⟩ : syracuseStep 14297239 = 21445859) B21445859
theorem B10725527 : Blo 988596 10725527 := bstep (se 1 (by rfl) ⟨8044145, by rfl⟩ : syracuseStep 10725527 = 16088291) B16088291
theorem B1485017 : Blo 988596 1485017 := bstep (se 2 (by rfl) ⟨556881, by rfl⟩ : syracuseStep 1485017 = 1113763) B1113763
theorem B1485131 : Blo 988596 1485131 := bstep (se 1 (by rfl) ⟨1113848, by rfl⟩ : syracuseStep 1485131 = 2227697) B2227697
theorem B1485143 : Blo 988596 1485143 := bstep (se 1 (by rfl) ⟨1113857, by rfl⟩ : syracuseStep 1485143 = 2227715) B2227715
theorem B1255819 : Blo 988596 1255819 := bstep (se 1 (by rfl) ⟨941864, by rfl⟩ : syracuseStep 1255819 = 1883729) B1883729
theorem B5646743 : Blo 988596 5646743 := bstep (se 1 (by rfl) ⟨4235057, by rfl⟩ : syracuseStep 5646743 = 8470115) B8470115
theorem B1485209 : Blo 988596 1485209 := bstep (se 2 (by rfl) ⟨556953, by rfl⟩ : syracuseStep 1485209 = 1113907) B1113907
theorem B1485323 : Blo 988596 1485323 := bstep (se 1 (by rfl) ⟨1113992, by rfl⟩ : syracuseStep 1485323 = 2227985) B2227985
theorem B5351953 : Blo 988596 5351953 := bstep (se 2 (by rfl) ⟨2006982, by rfl⟩ : syracuseStep 5351953 = 4013965) B4013965
theorem B1485335 : Blo 988596 1485335 := bstep (se 1 (by rfl) ⟨1114001, by rfl⟩ : syracuseStep 1485335 = 2228003) B2228003
theorem B1485401 : Blo 988596 1485401 := bstep (se 2 (by rfl) ⟨557025, by rfl⟩ : syracuseStep 1485401 = 1114051) B1114051
theorem B1256087 : Blo 988596 1256087 := bstep (se 1 (by rfl) ⟨942065, by rfl⟩ : syracuseStep 1256087 = 1884131) B1884131
theorem B1059499 : Blo 988596 1059499 := bstep (se 1 (by rfl) ⟨794624, by rfl⟩ : syracuseStep 1059499 = 1589249) B1589249
theorem B1485515 : Blo 988596 1485515 := bstep (se 1 (by rfl) ⟨1114136, by rfl⟩ : syracuseStep 1485515 = 2228273) B2228273
theorem B1485527 : Blo 988596 1485527 := bstep (se 1 (by rfl) ⟨1114145, by rfl⟩ : syracuseStep 1485527 = 2228291) B2228291
theorem B1878785 : Blo 988596 1878785 := bstep (se 2 (by rfl) ⟨704544, by rfl⟩ : syracuseStep 1878785 = 1409089) B1409089
theorem B1485593 : Blo 988596 1485593 := bstep (se 2 (by rfl) ⟨557097, by rfl⟩ : syracuseStep 1485593 = 1114195) B1114195
theorem B1485707 : Blo 988596 1485707 := bstep (se 1 (by rfl) ⟨1114280, by rfl⟩ : syracuseStep 1485707 = 2228561) B2228561
theorem B1485719 : Blo 988596 1485719 := bstep (se 1 (by rfl) ⟨1114289, by rfl⟩ : syracuseStep 1485719 = 2228579) B2228579
theorem B1485785 : Blo 988596 1485785 := bstep (se 2 (by rfl) ⟨557169, by rfl⟩ : syracuseStep 1485785 = 1114339) B1114339
theorem B1879051 : Blo 988596 1879051 := bstep (se 1 (by rfl) ⟨1409288, by rfl⟩ : syracuseStep 1879051 = 2818577) B2818577
theorem B1485899 : Blo 988596 1485899 := bstep (se 1 (by rfl) ⟨1114424, by rfl⟩ : syracuseStep 1485899 = 2228849) B2228849
theorem B1485911 : Blo 988596 1485911 := bstep (se 1 (by rfl) ⟨1114433, by rfl⟩ : syracuseStep 1485911 = 2228867) B2228867
theorem B19016855 : Blo 988596 19016855 := bstep (se 1 (by rfl) ⟨14262641, by rfl⟩ : syracuseStep 19016855 = 28525283) B28525283
theorem B1485977 : Blo 988596 1485977 := bstep (se 2 (by rfl) ⟨557241, by rfl⟩ : syracuseStep 1485977 = 1114483) B1114483
theorem B6859993 : Blo 988596 6859993 := bstep (se 2 (by rfl) ⟨2572497, by rfl⟩ : syracuseStep 6859993 = 5144995) B5144995
theorem B1486091 : Blo 988596 1486091 := bstep (se 1 (by rfl) ⟨1114568, by rfl⟩ : syracuseStep 1486091 = 2229137) B2229137
theorem B1486103 : Blo 988596 1486103 := bstep (se 1 (by rfl) ⟨1114577, by rfl⟩ : syracuseStep 1486103 = 2229155) B2229155
theorem B1486169 : Blo 988596 1486169 := bstep (se 2 (by rfl) ⟨557313, by rfl⟩ : syracuseStep 1486169 = 1114627) B1114627
theorem B1879499 : Blo 988596 1879499 := bstep (se 1 (by rfl) ⟨1409624, by rfl⟩ : syracuseStep 1879499 = 2819249) B2819249
theorem B1486283 : Blo 988596 1486283 := bstep (se 1 (by rfl) ⟨1114712, by rfl⟩ : syracuseStep 1486283 = 2229425) B2229425
theorem B1486295 : Blo 988596 1486295 := bstep (se 1 (by rfl) ⟨1114721, by rfl⟩ : syracuseStep 1486295 = 2229443) B2229443
theorem B4238851 : Blo 988596 4238851 := bstep (se 1 (by rfl) ⟨3179138, by rfl⟩ : syracuseStep 4238851 = 6358277) B6358277
theorem B4075031 : Blo 988596 4075031 := bstep (se 1 (by rfl) ⟨3056273, by rfl⟩ : syracuseStep 4075031 = 6112547) B6112547
theorem B1486361 : Blo 988596 1486361 := bstep (se 2 (by rfl) ⟨557385, by rfl⟩ : syracuseStep 1486361 = 1114771) B1114771
theorem B1879681 : Blo 988596 1879681 := bstep (se 2 (by rfl) ⟨704880, by rfl⟩ : syracuseStep 1879681 = 1409761) B1409761
theorem B1486475 : Blo 988596 1486475 := bstep (se 1 (by rfl) ⟨1114856, by rfl⟩ : syracuseStep 1486475 = 2229713) B2229713
theorem B1486487 : Blo 988596 1486487 := bstep (se 1 (by rfl) ⟨1114865, by rfl⟩ : syracuseStep 1486487 = 2229731) B2229731
theorem B1486553 : Blo 988596 1486553 := bstep (se 2 (by rfl) ⟨557457, by rfl⟩ : syracuseStep 1486553 = 1114915) B1114915
theorem B1486667 : Blo 988596 1486667 := bstep (se 1 (by rfl) ⟨1115000, by rfl⟩ : syracuseStep 1486667 = 2230001) B2230001
theorem B1486679 : Blo 988596 1486679 := bstep (se 1 (by rfl) ⟨1115009, by rfl⟩ : syracuseStep 1486679 = 2230019) B2230019
theorem B1486745 : Blo 988596 1486745 := bstep (se 2 (by rfl) ⟨557529, by rfl⟩ : syracuseStep 1486745 = 1115059) B1115059
theorem B1880023 : Blo 988596 1880023 := bstep (se 1 (by rfl) ⟨1410017, by rfl⟩ : syracuseStep 1880023 = 2820035) B2820035
theorem B1486859 : Blo 988596 1486859 := bstep (se 1 (by rfl) ⟨1115144, by rfl⟩ : syracuseStep 1486859 = 2230289) B2230289
theorem B1486871 : Blo 988596 1486871 := bstep (se 1 (by rfl) ⟨1115153, by rfl⟩ : syracuseStep 1486871 = 2230307) B2230307
theorem B1486937 : Blo 988596 1486937 := bstep (se 2 (by rfl) ⟨557601, by rfl⟩ : syracuseStep 1486937 = 1115203) B1115203
theorem B6107237 : Blo 988596 6107237 := bstep (se 4 (by rfl) ⟨572553, by rfl⟩ : syracuseStep 6107237 = 1145107) B1145107
theorem B1880243 : Blo 988596 1880243 := bstep (se 1 (by rfl) ⟨1410182, by rfl⟩ : syracuseStep 1880243 = 2820365) B2820365
theorem B2502859 : Blo 988596 2502859 := bstep (se 1 (by rfl) ⟨1877144, by rfl⟩ : syracuseStep 2502859 = 3754289) B3754289
theorem B1487051 : Blo 988596 1487051 := bstep (se 1 (by rfl) ⟨1115288, by rfl⟩ : syracuseStep 1487051 = 2230577) B2230577
theorem B1487063 : Blo 988596 1487063 := bstep (se 1 (by rfl) ⟨1115297, by rfl⟩ : syracuseStep 1487063 = 2230595) B2230595
theorem B1487129 : Blo 988596 1487129 := bstep (se 2 (by rfl) ⟨557673, by rfl⟩ : syracuseStep 1487129 = 1115347) B1115347
theorem B2503001 : Blo 988596 2503001 := bstep (se 2 (by rfl) ⟨938625, by rfl⟩ : syracuseStep 2503001 = 1877251) B1877251
theorem B1487243 : Blo 988596 1487243 := bstep (se 1 (by rfl) ⟨1115432, by rfl⟩ : syracuseStep 1487243 = 2230865) B2230865
theorem B1192331 : Blo 988596 1192331 := bstep (se 1 (by rfl) ⟨894248, by rfl⟩ : syracuseStep 1192331 = 1788497) B1788497
theorem B1880471 : Blo 988596 1880471 := bstep (se 1 (by rfl) ⟨1410353, by rfl⟩ : syracuseStep 1880471 = 2820707) B2820707
theorem B1487255 : Blo 988596 1487255 := bstep (se 1 (by rfl) ⟨1115441, by rfl⟩ : syracuseStep 1487255 = 2230883) B2230883
theorem B4239809 : Blo 988596 4239809 := bstep (se 2 (by rfl) ⟨1589928, by rfl⟩ : syracuseStep 4239809 = 3179857) B3179857
theorem B1487321 : Blo 988596 1487321 := bstep (se 2 (by rfl) ⟨557745, by rfl⟩ : syracuseStep 1487321 = 1115491) B1115491
theorem B1487435 : Blo 988596 1487435 := bstep (se 1 (by rfl) ⟨1115576, by rfl⟩ : syracuseStep 1487435 = 2231153) B2231153
theorem B1487447 : Blo 988596 1487447 := bstep (se 1 (by rfl) ⟨1115585, by rfl⟩ : syracuseStep 1487447 = 2231171) B2231171
theorem B1880729 : Blo 988596 1880729 := bstep (se 2 (by rfl) ⟨705273, by rfl⟩ : syracuseStep 1880729 = 1410547) B1410547
theorem B1487513 : Blo 988596 1487513 := bstep (se 2 (by rfl) ⟨557817, by rfl⟩ : syracuseStep 1487513 = 1115635) B1115635
theorem B5354201 : Blo 988596 5354201 := bstep (se 2 (by rfl) ⟨2007825, by rfl⟩ : syracuseStep 5354201 = 4015651) B4015651
theorem B1487627 : Blo 988596 1487627 := bstep (se 1 (by rfl) ⟨1115720, by rfl⟩ : syracuseStep 1487627 = 2231441) B2231441
theorem B1487639 : Blo 988596 1487639 := bstep (se 1 (by rfl) ⟨1115729, by rfl⟩ : syracuseStep 1487639 = 2231459) B2231459
theorem B2143027 : Blo 988596 2143027 := bstep (se 1 (by rfl) ⟨1607270, by rfl⟩ : syracuseStep 2143027 = 3214541) B3214541
theorem B1487705 : Blo 988596 1487705 := bstep (se 2 (by rfl) ⟨557889, by rfl⟩ : syracuseStep 1487705 = 1115779) B1115779
theorem B1586071 : Blo 988596 1586071 := bstep (se 1 (by rfl) ⟨1189553, by rfl⟩ : syracuseStep 1586071 = 2379107) B2379107
theorem B2864065 : Blo 988596 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B1487819 : Blo 988596 1487819 := bstep (se 1 (by rfl) ⟨1115864, by rfl⟩ : syracuseStep 1487819 = 2231729) B2231729
theorem B2012107 : Blo 988596 2012107 := bstep (se 1 (by rfl) ⟨1509080, by rfl⟩ : syracuseStep 2012107 = 3018161) B3018161
theorem B1487831 : Blo 988596 1487831 := bstep (se 1 (by rfl) ⟨1115873, by rfl⟩ : syracuseStep 1487831 = 2231747) B2231747
theorem B1487897 : Blo 988596 1487897 := bstep (se 2 (by rfl) ⟨557961, by rfl⟩ : syracuseStep 1487897 = 1115923) B1115923
theorem B1881139 : Blo 988596 1881139 := bstep (se 1 (by rfl) ⟨1410854, by rfl⟩ : syracuseStep 1881139 = 2821709) B2821709
theorem B1488011 : Blo 988596 1488011 := bstep (se 1 (by rfl) ⟨1116008, by rfl⟩ : syracuseStep 1488011 = 2232017) B2232017
theorem B2503831 : Blo 988596 2503831 := bstep (se 1 (by rfl) ⟨1877873, by rfl⟩ : syracuseStep 2503831 = 3755747) B3755747
theorem B1488023 : Blo 988596 1488023 := bstep (se 1 (by rfl) ⟨1116017, by rfl⟩ : syracuseStep 1488023 = 2232035) B2232035
theorem B1488089 : Blo 988596 1488089 := bstep (se 2 (by rfl) ⟨558033, by rfl⟩ : syracuseStep 1488089 = 1116067) B1116067
theorem B1127723 : Blo 988596 1127723 := bstep (se 1 (by rfl) ⟨845792, by rfl⟩ : syracuseStep 1127723 = 1691585) B1691585
theorem B1488203 : Blo 988596 1488203 := bstep (se 1 (by rfl) ⟨1116152, by rfl⟩ : syracuseStep 1488203 = 2232305) B2232305
theorem B1488215 : Blo 988596 1488215 := bstep (se 1 (by rfl) ⟨1116161, by rfl⟩ : syracuseStep 1488215 = 2232323) B2232323
theorem B30487925 : Blo 988596 30487925 := bstep (se 5 (by rfl) ⟨1429121, by rfl⟩ : syracuseStep 30487925 = 2858243) B2858243
theorem B1488281 : Blo 988596 1488281 := bstep (se 2 (by rfl) ⟨558105, by rfl⟩ : syracuseStep 1488281 = 1116211) B1116211
theorem B4077017 : Blo 988596 4077017 := bstep (se 2 (by rfl) ⟨1528881, by rfl⟩ : syracuseStep 4077017 = 3057763) B3057763
theorem B1488395 : Blo 988596 1488395 := bstep (se 1 (by rfl) ⟨1116296, by rfl⟩ : syracuseStep 1488395 = 2232593) B2232593
theorem B1488407 : Blo 988596 1488407 := bstep (se 1 (by rfl) ⟨1116305, by rfl⟩ : syracuseStep 1488407 = 2232611) B2232611
theorem B1881625 : Blo 988596 1881625 := bstep (se 2 (by rfl) ⟨705609, by rfl⟩ : syracuseStep 1881625 = 1411219) B1411219
theorem B2504267 : Blo 988596 2504267 := bstep (se 1 (by rfl) ⟨1878200, by rfl⟩ : syracuseStep 2504267 = 3756401) B3756401
theorem B1488473 : Blo 988596 1488473 := bstep (se 2 (by rfl) ⟨558177, by rfl⟩ : syracuseStep 1488473 = 1116355) B1116355
theorem B5355109 : Blo 988596 5355109 := bstep (se 4 (by rfl) ⟨502041, by rfl⟩ : syracuseStep 5355109 = 1004083) B1004083
theorem B1586891 : Blo 988596 1586891 := bstep (se 1 (by rfl) ⟨1190168, by rfl⟩ : syracuseStep 1586891 = 2380337) B2380337
theorem B1488587 : Blo 988596 1488587 := bstep (se 1 (by rfl) ⟨1116440, by rfl⟩ : syracuseStep 1488587 = 2232881) B2232881
theorem B1488599 : Blo 988596 1488599 := bstep (se 1 (by rfl) ⟨1116449, by rfl⟩ : syracuseStep 1488599 = 2232899) B2232899
theorem B10860293 : Blo 988596 10860293 := bstep (se 4 (by rfl) ⟨1018152, by rfl⟩ : syracuseStep 10860293 = 2036305) B2036305
theorem B1488665 : Blo 988596 1488665 := bstep (se 2 (by rfl) ⟨558249, by rfl⟩ : syracuseStep 1488665 = 1116499) B1116499
theorem B1783667 : Blo 988596 1783667 := bstep (se 1 (by rfl) ⟨1337750, by rfl⟩ : syracuseStep 1783667 = 2675501) B2675501
theorem B5355395 : Blo 988596 5355395 := bstep (se 1 (by rfl) ⟨4016546, by rfl⟩ : syracuseStep 5355395 = 8033093) B8033093
theorem B1488779 : Blo 988596 1488779 := bstep (se 1 (by rfl) ⟨1116584, by rfl⟩ : syracuseStep 1488779 = 2233169) B2233169
theorem B1488791 : Blo 988596 1488791 := bstep (se 1 (by rfl) ⟨1116593, by rfl⟩ : syracuseStep 1488791 = 2233187) B2233187
theorem B2504641 : Blo 988596 2504641 := bstep (se 2 (by rfl) ⟨939240, by rfl⟩ : syracuseStep 2504641 = 1878481) B1878481
theorem B2111447 : Blo 988596 2111447 := bstep (se 1 (by rfl) ⟨1583585, by rfl⟩ : syracuseStep 2111447 = 3167171) B3167171
theorem B1488857 : Blo 988596 1488857 := bstep (se 2 (by rfl) ⟨558321, by rfl⟩ : syracuseStep 1488857 = 1116643) B1116643
theorem B1882187 : Blo 988596 1882187 := bstep (se 1 (by rfl) ⟨1411640, by rfl⟩ : syracuseStep 1882187 = 2823281) B2823281
theorem B2111617 : Blo 988596 2111617 := bstep (se 2 (by rfl) ⟨791856, by rfl⟩ : syracuseStep 2111617 = 1583713) B1583713
theorem B1882369 : Blo 988596 1882369 := bstep (se 2 (by rfl) ⟨705888, by rfl⟩ : syracuseStep 1882369 = 1411777) B1411777
theorem B36616493 : Blo 988596 36616493 := bstep (se 3 (by rfl) ⟨6865592, by rfl⟩ : syracuseStep 36616493 = 13731185) B13731185
theorem B1718743 : Blo 988596 1718743 := bstep (se 1 (by rfl) ⟨1289057, by rfl⟩ : syracuseStep 1718743 = 2578115) B2578115
theorem B2505239 : Blo 988596 2505239 := bstep (se 1 (by rfl) ⟨1878929, by rfl⟩ : syracuseStep 2505239 = 3757859) B3757859
theorem B1587737 : Blo 988596 1587737 := bstep (se 2 (by rfl) ⟨595401, by rfl⟩ : syracuseStep 1587737 = 1190803) B1190803
theorem B1587865 : Blo 988596 1587865 := bstep (se 2 (by rfl) ⟨595449, by rfl⟩ : syracuseStep 1587865 = 1190899) B1190899
theorem B1587929 : Blo 988596 1587929 := bstep (se 2 (by rfl) ⟨595473, by rfl⟩ : syracuseStep 1587929 = 1190947) B1190947
theorem B1883083 : Blo 988596 1883083 := bstep (se 1 (by rfl) ⟨1412312, by rfl⟩ : syracuseStep 1883083 = 2824625) B2824625
theorem B6339545 : Blo 988596 6339545 := bstep (se 2 (by rfl) ⟨2377329, by rfl⟩ : syracuseStep 6339545 = 4754659) B4754659
theorem B1784843 : Blo 988596 1784843 := bstep (se 1 (by rfl) ⟨1338632, by rfl⟩ : syracuseStep 1784843 = 2677265) B2677265
theorem B1883159 : Blo 988596 1883159 := bstep (se 1 (by rfl) ⟨1412369, by rfl⟩ : syracuseStep 1883159 = 2824739) B2824739
theorem B2112779 : Blo 988596 2112779 := bstep (se 1 (by rfl) ⟨1584584, by rfl⟩ : syracuseStep 2112779 = 3169169) B3169169
theorem B2506049 : Blo 988596 2506049 := bstep (se 2 (by rfl) ⟨939768, by rfl⟩ : syracuseStep 2506049 = 1879537) B1879537
theorem B5717465 : Blo 988596 5717465 := bstep (se 2 (by rfl) ⟨2144049, by rfl⟩ : syracuseStep 5717465 = 4288099) B4288099
theorem B5652119 : Blo 988596 5652119 := bstep (se 1 (by rfl) ⟨4239089, by rfl⟩ : syracuseStep 5652119 = 8478179) B8478179
theorem B1883827 : Blo 988596 1883827 := bstep (se 1 (by rfl) ⟨1412870, by rfl⟩ : syracuseStep 1883827 = 2825741) B2825741
theorem B1359703 : Blo 988596 1359703 := bstep (se 1 (by rfl) ⟨1019777, by rfl⟩ : syracuseStep 1359703 = 2039555) B2039555
theorem B2506585 : Blo 988596 2506585 := bstep (se 2 (by rfl) ⟨939969, by rfl⟩ : syracuseStep 2506585 = 1879939) B1879939
theorem B1884055 : Blo 988596 1884055 := bstep (se 1 (by rfl) ⟨1413041, by rfl⟩ : syracuseStep 1884055 = 2826083) B2826083
theorem B10698713 : Blo 988596 10698713 := bstep (se 2 (by rfl) ⟨4012017, by rfl⟩ : syracuseStep 10698713 = 8024035) B8024035
theorem B8044505 : Blo 988596 8044505 := bstep (se 2 (by rfl) ⟨3016689, by rfl⟩ : syracuseStep 8044505 = 6033379) B6033379
theorem B2113523 : Blo 988596 2113523 := bstep (se 1 (by rfl) ⟨1585142, by rfl⟩ : syracuseStep 2113523 = 3170285) B3170285
theorem B1884161 : Blo 988596 1884161 := bstep (se 2 (by rfl) ⟨706560, by rfl⟩ : syracuseStep 1884161 = 1413121) B1413121
theorem B1884313 : Blo 988596 1884313 := bstep (se 2 (by rfl) ⟨706617, by rfl⟩ : syracuseStep 1884313 = 1413235) B1413235
theorem B4014353 : Blo 988596 4014353 := bstep (se 2 (by rfl) ⟨1505382, by rfl⟩ : syracuseStep 4014353 = 3010765) B3010765
theorem B8044865 : Blo 988596 8044865 := bstep (se 2 (by rfl) ⟨3016824, by rfl⟩ : syracuseStep 8044865 = 6033649) B6033649
theorem B30491153 : Blo 988596 30491153 := bstep (se 2 (by rfl) ⟨11434182, by rfl⟩ : syracuseStep 30491153 = 22868365) B22868365
theorem B4571741 : Blo 988596 4571741 := bstep (se 3 (by rfl) ⟨857201, by rfl⟩ : syracuseStep 4571741 = 1714403) B1714403
theorem B8471141 : Blo 988596 8471141 := bstep (se 4 (by rfl) ⟨794169, by rfl⟩ : syracuseStep 8471141 = 1588339) B1588339
theorem B11289293 : Blo 988596 11289293 := bstep (se 3 (by rfl) ⟨2116742, by rfl⟩ : syracuseStep 11289293 = 4233485) B4233485
theorem B4014809 : Blo 988596 4014809 := bstep (se 2 (by rfl) ⟨1505553, by rfl⟩ : syracuseStep 4014809 = 3011107) B3011107
theorem B2114419 : Blo 988596 2114419 := bstep (se 1 (by rfl) ⟨1585814, by rfl⟩ : syracuseStep 2114419 = 3171629) B3171629
theorem B2507699 : Blo 988596 2507699 := bstep (se 1 (by rfl) ⟨1880774, by rfl⟩ : syracuseStep 2507699 = 3761549) B3761549
theorem B2507993 : Blo 988596 2507993 := bstep (se 2 (by rfl) ⟨940497, by rfl⟩ : syracuseStep 2507993 = 1880995) B1880995
theorem B7849477 : Blo 988596 7849477 := bstep (se 4 (by rfl) ⟨735888, by rfl⟩ : syracuseStep 7849477 = 1471777) B1471777
theorem B6342209 : Blo 988596 6342209 := bstep (se 2 (by rfl) ⟨2378328, by rfl⟩ : syracuseStep 6342209 = 4756657) B4756657
theorem B19056221 : Blo 988596 19056221 := bstep (se 3 (by rfl) ⟨3573041, by rfl⟩ : syracuseStep 19056221 = 7146083) B7146083
theorem B3753773 : Blo 988596 3753773 := bstep (se 3 (by rfl) ⟨703832, by rfl⟩ : syracuseStep 3753773 = 1407665) B1407665
theorem B3753803 : Blo 988596 3753803 := bstep (se 1 (by rfl) ⟨2815352, by rfl⟩ : syracuseStep 3753803 = 5630705) B5630705
theorem B2115479 : Blo 988596 2115479 := bstep (se 1 (by rfl) ⟨1586609, by rfl⟩ : syracuseStep 2115479 = 3173219) B3173219
theorem B7129133 : Blo 988596 7129133 := bstep (se 3 (by rfl) ⟨1336712, by rfl⟩ : syracuseStep 7129133 = 2673425) B2673425
theorem B2115649 : Blo 988596 2115649 := bstep (se 2 (by rfl) ⟨793368, by rfl⟩ : syracuseStep 2115649 = 1586737) B1586737
theorem B8800435 : Blo 988596 8800435 := bstep (se 1 (by rfl) ⟨6600326, by rfl⟩ : syracuseStep 8800435 = 13200653) B13200653
theorem B2115991 : Blo 988596 2115991 := bstep (se 1 (by rfl) ⟨1586993, by rfl⟩ : syracuseStep 2115991 = 3173987) B3173987
theorem B2148811 : Blo 988596 2148811 := bstep (se 1 (by rfl) ⟨1611608, by rfl⟩ : syracuseStep 2148811 = 3223217) B3223217
theorem B3754457 : Blo 988596 3754457 := bstep (se 2 (by rfl) ⟨1407921, by rfl⟩ : syracuseStep 3754457 = 2815843) B2815843
theorem B3754775 : Blo 988596 3754775 := bstep (se 1 (by rfl) ⟨2816081, by rfl⟩ : syracuseStep 3754775 = 5632163) B5632163
theorem B4016947 : Blo 988596 4016947 := bstep (se 1 (by rfl) ⟨3012710, by rfl⟩ : syracuseStep 4016947 = 6025421) B6025421
theorem B2509643 : Blo 988596 2509643 := bstep (se 1 (by rfl) ⟨1882232, by rfl⟩ : syracuseStep 2509643 = 3764465) B3764465
theorem B2116811 : Blo 988596 2116811 := bstep (se 1 (by rfl) ⟨1587608, by rfl⟩ : syracuseStep 2116811 = 3175217) B3175217
theorem B8473805 : Blo 988596 8473805 := bstep (se 3 (by rfl) ⟨1588838, by rfl⟩ : syracuseStep 8473805 = 3177677) B3177677
theorem B3755443 : Blo 988596 3755443 := bstep (se 1 (by rfl) ⟨2816582, by rfl⟩ : syracuseStep 3755443 = 5633165) B5633165
theorem B2117171 : Blo 988596 2117171 := bstep (se 1 (by rfl) ⟨1587878, by rfl⟩ : syracuseStep 2117171 = 3175757) B3175757
theorem B8572517 : Blo 988596 8572517 := bstep (se 4 (by rfl) ⟨803673, by rfl⟩ : syracuseStep 8572517 = 1607347) B1607347
theorem B1101431 : Blo 988596 1101431 := bstep (se 1 (by rfl) ⟨826073, by rfl⟩ : syracuseStep 1101431 = 1652147) B1652147
theorem B6016643 : Blo 988596 6016643 := bstep (se 1 (by rfl) ⟨4512482, by rfl⟩ : syracuseStep 6016643 = 9024965) B9024965
theorem B4017923 : Blo 988596 4017923 := bstep (se 1 (by rfl) ⟨3013442, by rfl⟩ : syracuseStep 4017923 = 6026885) B6026885
theorem B2510615 : Blo 988596 2510615 := bstep (se 1 (by rfl) ⟨1882961, by rfl⟩ : syracuseStep 2510615 = 3765923) B3765923
theorem B2674583 : Blo 988596 2674583 := bstep (se 1 (by rfl) ⟨2005937, by rfl⟩ : syracuseStep 2674583 = 4011875) B4011875
theorem B2511283 : Blo 988596 2511283 := bstep (se 1 (by rfl) ⟨1883462, by rfl⟩ : syracuseStep 2511283 = 3766925) B3766925
theorem B2511425 : Blo 988596 2511425 := bstep (se 2 (by rfl) ⟨941784, by rfl⟩ : syracuseStep 2511425 = 1883569) B1883569
theorem B3756689 : Blo 988596 3756689 := bstep (se 2 (by rfl) ⟨1408758, by rfl⟩ : syracuseStep 3756689 = 2817517) B2817517
theorem B1692311 : Blo 988596 1692311 := bstep (se 1 (by rfl) ⟨1269233, by rfl⟩ : syracuseStep 1692311 = 2538467) B2538467
theorem B3429427 : Blo 988596 3429427 := bstep (se 1 (by rfl) ⟨2572070, by rfl⟩ : syracuseStep 3429427 = 5144141) B5144141
theorem B4281623 : Blo 988596 4281623 := bstep (se 1 (by rfl) ⟨3211217, by rfl⟩ : syracuseStep 4281623 = 6422435) B6422435
theorem B3757387 : Blo 988596 3757387 := bstep (se 1 (by rfl) ⟨2818040, by rfl⟩ : syracuseStep 3757387 = 5636081) B5636081
theorem B2119169 : Blo 988596 2119169 := bstep (se 2 (by rfl) ⟨794688, by rfl⟩ : syracuseStep 2119169 = 1589377) B1589377
theorem B3757661 : Blo 988596 3757661 := bstep (se 3 (by rfl) ⟨704561, by rfl⟩ : syracuseStep 3757661 = 1409123) B1409123
theorem B11261591 : Blo 988596 11261591 := bstep (se 1 (by rfl) ⟨8446193, by rfl⟩ : syracuseStep 11261591 = 16892387) B16892387
theorem B1005259 : Blo 988596 1005259 := bstep (se 1 (by rfl) ⟨753944, by rfl⟩ : syracuseStep 1005259 = 1507889) B1507889
theorem B34363237 : Blo 988596 34363237 := bstep (se 4 (by rfl) ⟨3221553, by rfl⟩ : syracuseStep 34363237 = 6443107) B6443107
theorem B4577303 : Blo 988596 4577303 := bstep (se 1 (by rfl) ⟨3432977, by rfl⟩ : syracuseStep 4577303 = 6865955) B6865955
theorem B16046261 : Blo 988596 16046261 := bstep (se 5 (by rfl) ⟨752168, by rfl⟩ : syracuseStep 16046261 = 1504337) B1504337
theorem B3758359 : Blo 988596 3758359 := bstep (se 1 (by rfl) ⟨2818769, by rfl⟩ : syracuseStep 3758359 = 5637539) B5637539
theorem B51501581 : Blo 988596 51501581 := bstep (se 3 (by rfl) ⟨9656546, by rfl⟩ : syracuseStep 51501581 = 19313093) B19313093
theorem B2382643 : Blo 988596 2382643 := bstep (se 1 (by rfl) ⟨1786982, by rfl⟩ : syracuseStep 2382643 = 3573965) B3573965
theorem B3759149 : Blo 988596 3759149 := bstep (se 3 (by rfl) ⟨704840, by rfl⟩ : syracuseStep 3759149 = 1409681) B1409681
theorem B3169373 : Blo 988596 3169373 := bstep (se 3 (by rfl) ⟨594257, by rfl⟩ : syracuseStep 3169373 = 1188515) B1188515
theorem B6348077 : Blo 988596 6348077 := bstep (se 3 (by rfl) ⟨1190264, by rfl⟩ : syracuseStep 6348077 = 2380529) B2380529
theorem B9035651 : Blo 988596 9035651 := bstep (se 1 (by rfl) ⟨6776738, by rfl⟩ : syracuseStep 9035651 = 13553477) B13553477
theorem B3923905 : Blo 988596 3923905 := bstep (se 2 (by rfl) ⟨1471464, by rfl⟩ : syracuseStep 3923905 = 2942929) B2942929
theorem B3825625 : Blo 988596 3825625 := bstep (se 2 (by rfl) ⟨1434609, by rfl⟩ : syracuseStep 3825625 = 2869219) B2869219
theorem B14278787 : Blo 988596 14278787 := bstep (se 1 (by rfl) ⟨10709090, by rfl⟩ : syracuseStep 14278787 = 21418181) B21418181
theorem B7528625 : Blo 988596 7528625 := bstep (se 2 (by rfl) ⟨2823234, by rfl⟩ : syracuseStep 7528625 = 5646469) B5646469
theorem B7135589 : Blo 988596 7135589 := bstep (se 4 (by rfl) ⟨668961, by rfl⟩ : syracuseStep 7135589 = 1337923) B1337923
theorem B2384279 : Blo 988596 2384279 := bstep (se 1 (by rfl) ⟨1788209, by rfl⟩ : syracuseStep 2384279 = 3576419) B3576419
theorem B8020403 : Blo 988596 8020403 := bstep (se 1 (by rfl) ⟨6015302, by rfl⟩ : syracuseStep 8020403 = 12030605) B12030605
theorem B3760577 : Blo 988596 3760577 := bstep (se 2 (by rfl) ⟨1410216, by rfl⟩ : syracuseStep 3760577 = 2820433) B2820433
theorem B4514251 : Blo 988596 4514251 := bstep (se 1 (by rfl) ⟨3385688, by rfl⟩ : syracuseStep 4514251 = 6771377) B6771377
theorem B7529111 : Blo 988596 7529111 := bstep (se 1 (by rfl) ⟨5646833, by rfl⟩ : syracuseStep 7529111 = 11293667) B11293667
theorem B8152325 : Blo 988596 8152325 := bstep (se 4 (by rfl) ⟨764280, by rfl⟩ : syracuseStep 8152325 = 1528561) B1528561
theorem B5006609 : Blo 988596 5006609 := bstep (se 2 (by rfl) ⟨1877478, by rfl⟩ : syracuseStep 5006609 = 3754957) B3754957
theorem B5006771 : Blo 988596 5006771 := bstep (se 1 (by rfl) ⟨3755078, by rfl⟩ : syracuseStep 5006771 = 7510157) B7510157
theorem B3565073 : Blo 988596 3565073 := bstep (se 2 (by rfl) ⟨1336902, by rfl⟩ : syracuseStep 3565073 = 2673805) B2673805
theorem B3565187 : Blo 988596 3565187 := bstep (se 1 (by rfl) ⟨2673890, by rfl⟩ : syracuseStep 3565187 = 5347781) B5347781
theorem B9168515 : Blo 988596 9168515 := bstep (se 1 (by rfl) ⟨6876386, by rfl⟩ : syracuseStep 9168515 = 13752773) B13752773
theorem B3565259 : Blo 988596 3565259 := bstep (se 1 (by rfl) ⟨2673944, by rfl⟩ : syracuseStep 3565259 = 5347889) B5347889
theorem B2713409 : Blo 988596 2713409 := bstep (se 2 (by rfl) ⟨1017528, by rfl⟩ : syracuseStep 2713409 = 2035057) B2035057
theorem B3762065 : Blo 988596 3762065 := bstep (se 2 (by rfl) ⟨1410774, by rfl⟩ : syracuseStep 3762065 = 2821549) B2821549
theorem B6023261 : Blo 988596 6023261 := bstep (se 3 (by rfl) ⟨1129361, by rfl⟩ : syracuseStep 6023261 = 2258723) B2258723
theorem B3008819 : Blo 988596 3008819 := bstep (se 1 (by rfl) ⟨2256614, by rfl⟩ : syracuseStep 3008819 = 4513229) B4513229
theorem B4352321 : Blo 988596 4352321 := bstep (se 2 (by rfl) ⟨1632120, by rfl⟩ : syracuseStep 4352321 = 3264241) B3264241
theorem B3762521 : Blo 988596 3762521 := bstep (se 2 (by rfl) ⟨1410945, by rfl⟩ : syracuseStep 3762521 = 2821891) B2821891
theorem B3762733 : Blo 988596 3762733 := bstep (se 3 (by rfl) ⟨705512, by rfl⟩ : syracuseStep 3762733 = 1411025) B1411025
theorem B3336983 : Blo 988596 3336983 := bstep (se 1 (by rfl) ⟨2502737, by rfl⟩ : syracuseStep 3336983 = 5005475) B5005475
theorem B3763037 : Blo 988596 3763037 := bstep (se 3 (by rfl) ⟨705569, by rfl⟩ : syracuseStep 3763037 = 1411139) B1411139
theorem B6351767 : Blo 988596 6351767 := bstep (se 1 (by rfl) ⟨4763825, by rfl⟩ : syracuseStep 6351767 = 9527651) B9527651
theorem B1338329 : Blo 988596 1338329 := bstep (se 2 (by rfl) ⟨501873, by rfl⟩ : syracuseStep 1338329 = 1003747) B1003747
theorem B28568645 : Blo 988596 28568645 := bstep (se 4 (by rfl) ⟨2678310, by rfl⟩ : syracuseStep 28568645 = 5356621) B5356621
theorem B2255959 : Blo 988596 2255959 := bstep (se 1 (by rfl) ⟨1691969, by rfl⟩ : syracuseStep 2255959 = 3383939) B3383939
theorem B7630085 : Blo 988596 7630085 := bstep (se 4 (by rfl) ⟨715320, by rfl⟩ : syracuseStep 7630085 = 1430641) B1430641
theorem B3337523 : Blo 988596 3337523 := bstep (se 1 (by rfl) ⟨2503142, by rfl⟩ : syracuseStep 3337523 = 5006285) B5006285
theorem B5008715 : Blo 988596 5008715 := bstep (se 1 (by rfl) ⟨3756536, by rfl⟩ : syracuseStep 5008715 = 7513073) B7513073
theorem B3337793 : Blo 988596 3337793 := bstep (se 2 (by rfl) ⟨1251672, by rfl⟩ : syracuseStep 3337793 = 2503345) B2503345
theorem B7925399 : Blo 988596 7925399 := bstep (se 1 (by rfl) ⟨5944049, by rfl⟩ : syracuseStep 7925399 = 11888099) B11888099
theorem B7630853 : Blo 988596 7630853 := bstep (se 4 (by rfl) ⟨715392, by rfl⟩ : syracuseStep 7630853 = 1430785) B1430785
theorem B3338333 : Blo 988596 3338333 := bstep (se 3 (by rfl) ⟨625937, by rfl⟩ : syracuseStep 3338333 = 1251875) B1251875
theorem B11300957 : Blo 988596 11300957 := bstep (se 3 (by rfl) ⟨2118929, by rfl⟩ : syracuseStep 11300957 = 4237859) B4237859
theorem B18346135 : Blo 988596 18346135 := bstep (se 1 (by rfl) ⟨13759601, by rfl⟩ : syracuseStep 18346135 = 27519203) B27519203
theorem B2224385 : Blo 988596 2224385 := bstep (se 2 (by rfl) ⟨834144, by rfl⟩ : syracuseStep 2224385 = 1668289) B1668289
theorem B2224601 : Blo 988596 2224601 := bstep (se 2 (by rfl) ⟨834225, by rfl⟩ : syracuseStep 2224601 = 1668451) B1668451
theorem B2224691 : Blo 988596 2224691 := bstep (se 1 (by rfl) ⟨1668518, by rfl⟩ : syracuseStep 2224691 = 3337037) B3337037
theorem B2224727 : Blo 988596 2224727 := bstep (se 1 (by rfl) ⟨1668545, by rfl⟩ : syracuseStep 2224727 = 3337091) B3337091
theorem B3175001 : Blo 988596 3175001 := bstep (se 2 (by rfl) ⟨1190625, by rfl⟩ : syracuseStep 3175001 = 2381251) B2381251
theorem B1340107 : Blo 988596 1340107 := bstep (se 1 (by rfl) ⟨1005080, by rfl⟩ : syracuseStep 1340107 = 2010161) B2010161
theorem B2224907 : Blo 988596 2224907 := bstep (se 1 (by rfl) ⟨1668680, by rfl⟩ : syracuseStep 2224907 = 3337361) B3337361
theorem B2224961 : Blo 988596 2224961 := bstep (se 2 (by rfl) ⟨834360, by rfl⟩ : syracuseStep 2224961 = 1668721) B1668721
theorem B3175319 : Blo 988596 3175319 := bstep (se 1 (by rfl) ⟨2381489, by rfl⟩ : syracuseStep 3175319 = 4762979) B4762979
theorem B4223917 : Blo 988596 4223917 := bstep (se 3 (by rfl) ⟨791984, by rfl⟩ : syracuseStep 4223917 = 1583969) B1583969
theorem B2225177 : Blo 988596 2225177 := bstep (se 2 (by rfl) ⟨834441, by rfl⟩ : syracuseStep 2225177 = 1668883) B1668883
theorem B5010497 : Blo 988596 5010497 := bstep (se 2 (by rfl) ⟨1878936, by rfl⟩ : syracuseStep 5010497 = 3757873) B3757873
theorem B4224089 : Blo 988596 4224089 := bstep (se 2 (by rfl) ⟨1584033, by rfl⟩ : syracuseStep 4224089 = 3168067) B3168067
theorem B2225267 : Blo 988596 2225267 := bstep (se 1 (by rfl) ⟨1668950, by rfl⟩ : syracuseStep 2225267 = 3337901) B3337901
theorem B2225303 : Blo 988596 2225303 := bstep (se 1 (by rfl) ⟨1668977, by rfl⟩ : syracuseStep 2225303 = 3337955) B3337955
theorem B3339467 : Blo 988596 3339467 := bstep (se 1 (by rfl) ⟨2504600, by rfl⟩ : syracuseStep 3339467 = 5009201) B5009201
theorem B3175627 : Blo 988596 3175627 := bstep (se 1 (by rfl) ⟨2381720, by rfl⟩ : syracuseStep 3175627 = 4763441) B4763441
theorem B1668377 : Blo 988596 1668377 := bstep (se 2 (by rfl) ⟨625641, by rfl⟩ : syracuseStep 1668377 = 1251283) B1251283
theorem B2815307 : Blo 988596 2815307 := bstep (se 1 (by rfl) ⟨2111480, by rfl⟩ : syracuseStep 2815307 = 4222961) B4222961
theorem B2225483 : Blo 988596 2225483 := bstep (se 1 (by rfl) ⟨1669112, by rfl⟩ : syracuseStep 2225483 = 3338225) B3338225
theorem B2225537 : Blo 988596 2225537 := bstep (se 2 (by rfl) ⟨834576, by rfl⟩ : syracuseStep 2225537 = 1669153) B1669153
theorem B3765635 : Blo 988596 3765635 := bstep (se 1 (by rfl) ⟨2824226, by rfl⟩ : syracuseStep 3765635 = 5648453) B5648453
theorem B3765649 : Blo 988596 3765649 := bstep (se 2 (by rfl) ⟨1412118, by rfl⟩ : syracuseStep 3765649 = 2824237) B2824237
theorem B1668505 : Blo 988596 1668505 := bstep (se 2 (by rfl) ⟨625689, by rfl⟩ : syracuseStep 1668505 = 1251379) B1251379
theorem B3339737 : Blo 988596 3339737 := bstep (se 2 (by rfl) ⟨1252401, by rfl⟩ : syracuseStep 3339737 = 2504803) B2504803
theorem B2225753 : Blo 988596 2225753 := bstep (se 2 (by rfl) ⟨834657, by rfl⟩ : syracuseStep 2225753 = 1669315) B1669315
theorem B2225843 : Blo 988596 2225843 := bstep (se 1 (by rfl) ⟨1669382, by rfl⟩ : syracuseStep 2225843 = 3338765) B3338765
theorem B3765953 : Blo 988596 3765953 := bstep (se 2 (by rfl) ⟨1412232, by rfl⟩ : syracuseStep 3765953 = 2824465) B2824465
theorem B2225879 : Blo 988596 2225879 := bstep (se 1 (by rfl) ⟨1669409, by rfl⟩ : syracuseStep 2225879 = 3338819) B3338819
theorem B3176243 : Blo 988596 3176243 := bstep (se 1 (by rfl) ⟨2382182, by rfl⟩ : syracuseStep 3176243 = 4764365) B4764365
theorem B40728419 : Blo 988596 40728419 := bstep (se 1 (by rfl) ⟨30546314, by rfl⟩ : syracuseStep 40728419 = 61092629) B61092629
theorem B2226059 : Blo 988596 2226059 := bstep (se 1 (by rfl) ⟨1669544, by rfl⟩ : syracuseStep 2226059 = 3339089) B3339089
theorem B2226113 : Blo 988596 2226113 := bstep (se 2 (by rfl) ⟨834792, by rfl⟩ : syracuseStep 2226113 = 1669585) B1669585
theorem B1669079 : Blo 988596 1669079 := bstep (se 1 (by rfl) ⟨1251809, by rfl⟩ : syracuseStep 1669079 = 2503619) B2503619
theorem B1669207 : Blo 988596 1669207 := bstep (se 1 (by rfl) ⟨1251905, by rfl⟩ : syracuseStep 1669207 = 2503811) B2503811
theorem B4290691 : Blo 988596 4290691 := bstep (se 1 (by rfl) ⟨3218018, by rfl⟩ : syracuseStep 4290691 = 6436037) B6436037
theorem B1112215 : Blo 988596 1112215 := bstep (se 1 (by rfl) ⟨834161, by rfl⟩ : syracuseStep 1112215 = 1668323) B1668323
theorem B3340439 : Blo 988596 3340439 := bstep (se 1 (by rfl) ⟨2505329, by rfl⟩ : syracuseStep 3340439 = 5010659) B5010659
theorem B2226329 : Blo 988596 2226329 := bstep (se 2 (by rfl) ⟨834873, by rfl⟩ : syracuseStep 2226329 = 1669747) B1669747
theorem B2226419 : Blo 988596 2226419 := bstep (se 1 (by rfl) ⟨1669814, by rfl⟩ : syracuseStep 2226419 = 3339629) B3339629
theorem B2226455 : Blo 988596 2226455 := bstep (se 1 (by rfl) ⟨1669841, by rfl⟩ : syracuseStep 2226455 = 3339683) B3339683
theorem B1112395 : Blo 988596 1112395 := bstep (se 1 (by rfl) ⟨834296, by rfl⟩ : syracuseStep 1112395 = 1668593) B1668593
theorem B3766621 : Blo 988596 3766621 := bstep (se 3 (by rfl) ⟨706241, by rfl⟩ : syracuseStep 3766621 = 1412483) B1412483
theorem B6355331 : Blo 988596 6355331 := bstep (se 1 (by rfl) ⟨4766498, by rfl⟩ : syracuseStep 6355331 = 9532997) B9532997
theorem B1112503 : Blo 988596 1112503 := bstep (se 1 (by rfl) ⟨834377, by rfl⟩ : syracuseStep 1112503 = 1668755) B1668755
theorem B2226635 : Blo 988596 2226635 := bstep (se 1 (by rfl) ⟨1669976, by rfl⟩ : syracuseStep 2226635 = 3339953) B3339953
theorem B2226689 : Blo 988596 2226689 := bstep (se 2 (by rfl) ⟨835008, by rfl⟩ : syracuseStep 2226689 = 1670017) B1670017
theorem B1112683 : Blo 988596 1112683 := bstep (se 1 (by rfl) ⟨834512, by rfl⟩ : syracuseStep 1112683 = 1669025) B1669025
theorem B3340979 : Blo 988596 3340979 := bstep (se 1 (by rfl) ⟨2505734, by rfl⟩ : syracuseStep 3340979 = 5011469) B5011469
theorem B4225729 : Blo 988596 4225729 := bstep (se 2 (by rfl) ⟨1584648, by rfl⟩ : syracuseStep 4225729 = 3169297) B3169297
theorem B1669835 : Blo 988596 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B1112791 : Blo 988596 1112791 := bstep (se 1 (by rfl) ⟨834593, by rfl⟩ : syracuseStep 1112791 = 1669187) B1669187
theorem B2226905 : Blo 988596 2226905 := bstep (se 2 (by rfl) ⟨835089, by rfl⟩ : syracuseStep 2226905 = 1670179) B1670179
theorem B6421265 : Blo 988596 6421265 := bstep (se 2 (by rfl) ⟨2407974, by rfl⟩ : syracuseStep 6421265 = 4815949) B4815949
theorem B2226995 : Blo 988596 2226995 := bstep (se 1 (by rfl) ⟨1670246, by rfl⟩ : syracuseStep 2226995 = 3340493) B3340493
theorem B1669963 : Blo 988596 1669963 := bstep (se 1 (by rfl) ⟨1252472, by rfl⟩ : syracuseStep 1669963 = 2504945) B2504945
theorem B2227031 : Blo 988596 2227031 := bstep (se 1 (by rfl) ⟨1670273, by rfl⟩ : syracuseStep 2227031 = 3340547) B3340547
theorem B11598709 : Blo 988596 11598709 := bstep (se 5 (by rfl) ⟨543689, by rfl⟩ : syracuseStep 11598709 = 1087379) B1087379
theorem B3570563 : Blo 988596 3570563 := bstep (se 1 (by rfl) ⟨2677922, by rfl⟩ : syracuseStep 3570563 = 5355845) B5355845
theorem B1112971 : Blo 988596 1112971 := bstep (se 1 (by rfl) ⟨834728, by rfl⟩ : syracuseStep 1112971 = 1669457) B1669457
theorem B2816947 : Blo 988596 2816947 := bstep (se 1 (by rfl) ⟨2112710, by rfl⟩ : syracuseStep 2816947 = 4225421) B4225421
theorem B3341249 : Blo 988596 3341249 := bstep (se 2 (by rfl) ⟨1252968, by rfl⟩ : syracuseStep 3341249 = 2505937) B2505937
theorem B1670105 : Blo 988596 1670105 := bstep (se 2 (by rfl) ⟨626289, by rfl⟩ : syracuseStep 1670105 = 1252579) B1252579
theorem B5012441 : Blo 988596 5012441 := bstep (se 2 (by rfl) ⟨1879665, by rfl⟩ : syracuseStep 5012441 = 3759331) B3759331
theorem B1113079 : Blo 988596 1113079 := bstep (se 1 (by rfl) ⟨834809, by rfl⟩ : syracuseStep 1113079 = 1669619) B1669619
theorem B2227211 : Blo 988596 2227211 := bstep (se 1 (by rfl) ⟨1670408, by rfl⟩ : syracuseStep 2227211 = 3340817) B3340817
theorem B2227265 : Blo 988596 2227265 := bstep (se 2 (by rfl) ⟨835224, by rfl⟩ : syracuseStep 2227265 = 1670449) B1670449
theorem B1670233 : Blo 988596 1670233 := bstep (se 2 (by rfl) ⟨626337, by rfl⟩ : syracuseStep 1670233 = 1252675) B1252675
theorem B2817175 : Blo 988596 2817175 := bstep (se 1 (by rfl) ⟨2112881, by rfl⟩ : syracuseStep 2817175 = 4225763) B4225763
theorem B1113259 : Blo 988596 1113259 := bstep (se 1 (by rfl) ⟨834944, by rfl⟩ : syracuseStep 1113259 = 1669889) B1669889
theorem B1113367 : Blo 988596 1113367 := bstep (se 1 (by rfl) ⟨835025, by rfl⟩ : syracuseStep 1113367 = 1670051) B1670051
theorem B2227481 : Blo 988596 2227481 := bstep (se 2 (by rfl) ⟨835305, by rfl⟩ : syracuseStep 2227481 = 1670611) B1670611
theorem B2227571 : Blo 988596 2227571 := bstep (se 1 (by rfl) ⟨1670678, by rfl⟩ : syracuseStep 2227571 = 3341357) B3341357
theorem B2227607 : Blo 988596 2227607 := bstep (se 1 (by rfl) ⟨1670705, by rfl⟩ : syracuseStep 2227607 = 3341411) B3341411
theorem B1113547 : Blo 988596 1113547 := bstep (se 1 (by rfl) ⟨835160, by rfl⟩ : syracuseStep 1113547 = 1670321) B1670321
theorem B3341789 : Blo 988596 3341789 := bstep (se 3 (by rfl) ⟨626585, by rfl⟩ : syracuseStep 3341789 = 1253171) B1253171
theorem B1113655 : Blo 988596 1113655 := bstep (se 1 (by rfl) ⟨835241, by rfl⟩ : syracuseStep 1113655 = 1670483) B1670483
theorem B2227787 : Blo 988596 2227787 := bstep (se 1 (by rfl) ⟨1670840, by rfl⟩ : syracuseStep 2227787 = 3341681) B3341681
theorem B3767897 : Blo 988596 3767897 := bstep (se 2 (by rfl) ⟨1412961, by rfl⟩ : syracuseStep 3767897 = 2825923) B2825923
theorem B2227841 : Blo 988596 2227841 := bstep (se 2 (by rfl) ⟨835440, by rfl⟩ : syracuseStep 2227841 = 1670881) B1670881
theorem B1670807 : Blo 988596 1670807 := bstep (se 1 (by rfl) ⟨1253105, by rfl⟩ : syracuseStep 1670807 = 2506211) B2506211
theorem B5635763 : Blo 988596 5635763 := bstep (se 1 (by rfl) ⟨4226822, by rfl⟩ : syracuseStep 5635763 = 8453645) B8453645
theorem B1113835 : Blo 988596 1113835 := bstep (se 1 (by rfl) ⟨835376, by rfl⟩ : syracuseStep 1113835 = 1670753) B1670753
theorem B14286577 : Blo 988596 14286577 := bstep (se 2 (by rfl) ⟨5357466, by rfl⟩ : syracuseStep 14286577 = 10714933) B10714933
theorem B6782737 : Blo 988596 6782737 := bstep (se 2 (by rfl) ⟨2543526, by rfl⟩ : syracuseStep 6782737 = 5087053) B5087053
theorem B7536401 : Blo 988596 7536401 := bstep (se 2 (by rfl) ⟨2826150, by rfl⟩ : syracuseStep 7536401 = 5652301) B5652301
theorem B1670935 : Blo 988596 1670935 := bstep (se 1 (by rfl) ⟨1253201, by rfl⟩ : syracuseStep 1670935 = 2506403) B2506403
theorem B1113943 : Blo 988596 1113943 := bstep (se 1 (by rfl) ⟨835457, by rfl⟩ : syracuseStep 1113943 = 1670915) B1670915
theorem B2228057 : Blo 988596 2228057 := bstep (se 2 (by rfl) ⟨835521, by rfl⟩ : syracuseStep 2228057 = 1671043) B1671043
theorem B1605529 : Blo 988596 1605529 := bstep (se 2 (by rfl) ⟨602073, by rfl⟩ : syracuseStep 1605529 = 1204147) B1204147
theorem B2228147 : Blo 988596 2228147 := bstep (se 1 (by rfl) ⟨1671110, by rfl⟩ : syracuseStep 2228147 = 3342221) B3342221
theorem B2228183 : Blo 988596 2228183 := bstep (se 1 (by rfl) ⟨1671137, by rfl⟩ : syracuseStep 2228183 = 3342275) B3342275
theorem B20348941 : Blo 988596 20348941 := bstep (se 3 (by rfl) ⟨3815426, by rfl⟩ : syracuseStep 20348941 = 7630853) B7630853
theorem B1114375 : Blo 988596 1114375 := bstep (se 1 (by rfl) ⟨835781, by rfl⟩ : syracuseStep 1114375 = 1671563) B1671563
theorem B3342707 : Blo 988596 3342707 := bstep (se 1 (by rfl) ⟨2507030, by rfl⟩ : syracuseStep 3342707 = 5014061) B5014061
theorem B2228615 : Blo 988596 2228615 := bstep (se 1 (by rfl) ⟨1671461, by rfl⟩ : syracuseStep 2228615 = 3342923) B3342923
theorem B3047827 : Blo 988596 3047827 := bstep (se 1 (by rfl) ⟨2285870, by rfl⟩ : syracuseStep 3047827 = 4571741) B4571741
theorem B2818451 : Blo 988596 2818451 := bstep (se 1 (by rfl) ⟨2113838, by rfl⟩ : syracuseStep 2818451 = 4227677) B4227677
theorem B5636537 : Blo 988596 5636537 := bstep (se 2 (by rfl) ⟨2113701, by rfl⟩ : syracuseStep 5636537 = 4227403) B4227403
theorem B1114555 : Blo 988596 1114555 := bstep (se 1 (by rfl) ⟨835916, by rfl⟩ : syracuseStep 1114555 = 1671833) B1671833
theorem B2228795 : Blo 988596 2228795 := bstep (se 1 (by rfl) ⟨1671596, by rfl⟩ : syracuseStep 2228795 = 3343193) B3343193
theorem B1671799 : Blo 988596 1671799 := bstep (se 1 (by rfl) ⟨1253849, by rfl⟩ : syracuseStep 1671799 = 2507699) B2507699
theorem B2228921 : Blo 988596 2228921 := bstep (se 2 (by rfl) ⟨835845, by rfl⟩ : syracuseStep 2228921 = 1671691) B1671691
theorem B1671995 : Blo 988596 1671995 := bstep (se 1 (by rfl) ⟨1253996, by rfl⟩ : syracuseStep 1671995 = 2507993) B2507993
theorem B1115023 : Blo 988596 1115023 := bstep (se 1 (by rfl) ⟨836267, by rfl⟩ : syracuseStep 1115023 = 1672535) B1672535
theorem B1409977 : Blo 988596 1409977 := bstep (se 2 (by rfl) ⟨528741, by rfl⟩ : syracuseStep 1409977 = 1057483) B1057483
theorem B2229263 : Blo 988596 2229263 := bstep (se 1 (by rfl) ⟨1671947, by rfl⟩ : syracuseStep 2229263 = 3343895) B3343895
theorem B3179549 : Blo 988596 3179549 := bstep (se 3 (by rfl) ⟨596165, by rfl⟩ : syracuseStep 3179549 = 1192331) B1192331
theorem B2229281 : Blo 988596 2229281 := bstep (se 2 (by rfl) ⟨835980, by rfl⟩ : syracuseStep 2229281 = 1671961) B1671961
theorem B4228139 : Blo 988596 4228139 := bstep (se 1 (by rfl) ⟨3171104, by rfl⟩ : syracuseStep 4228139 = 6342209) B6342209
theorem B2819225 : Blo 988596 2819225 := bstep (se 2 (by rfl) ⟨1057209, by rfl⟩ : syracuseStep 2819225 = 2114419) B2114419
theorem B1672393 : Blo 988596 1672393 := bstep (se 2 (by rfl) ⟨627147, by rfl⟩ : syracuseStep 1672393 = 1254295) B1254295
theorem B1410319 : Blo 988596 1410319 := bstep (se 1 (by rfl) ⟨1057739, by rfl⟩ : syracuseStep 1410319 = 2115479) B2115479
theorem B4752755 : Blo 988596 4752755 := bstep (se 1 (by rfl) ⟨3564566, by rfl⟩ : syracuseStep 4752755 = 7129133) B7129133
theorem B2229623 : Blo 988596 2229623 := bstep (se 1 (by rfl) ⟨1672217, by rfl⟩ : syracuseStep 2229623 = 3344435) B3344435
theorem B1115527 : Blo 988596 1115527 := bstep (se 1 (by rfl) ⟨836645, by rfl⟩ : syracuseStep 1115527 = 1673291) B1673291
theorem B2229803 : Blo 988596 2229803 := bstep (se 1 (by rfl) ⟨1672352, by rfl⟩ : syracuseStep 2229803 = 3344705) B3344705
theorem B1115707 : Blo 988596 1115707 := bstep (se 1 (by rfl) ⟨836780, by rfl⟩ : syracuseStep 1115707 = 1673561) B1673561
theorem B1673095 : Blo 988596 1673095 := bstep (se 1 (by rfl) ⟨1254821, by rfl⟩ : syracuseStep 1673095 = 2509643) B2509643
theorem B2230163 : Blo 988596 2230163 := bstep (se 1 (by rfl) ⟨1672622, by rfl⟩ : syracuseStep 2230163 = 3345245) B3345245
theorem B3016595 : Blo 988596 3016595 := bstep (se 1 (by rfl) ⟨2262446, by rfl⟩ : syracuseStep 3016595 = 4524893) B4524893
theorem B2230217 : Blo 988596 2230217 := bstep (se 2 (by rfl) ⟨836331, by rfl⟩ : syracuseStep 2230217 = 1672663) B1672663
theorem B1116175 : Blo 988596 1116175 := bstep (se 1 (by rfl) ⟨837131, by rfl⟩ : syracuseStep 1116175 = 1674263) B1674263
theorem B1411447 : Blo 988596 1411447 := bstep (se 1 (by rfl) ⟨1058585, by rfl⟩ : syracuseStep 1411447 = 2117171) B2117171
theorem B6359431 : Blo 988596 6359431 := bstep (se 1 (by rfl) ⟨4769573, by rfl⟩ : syracuseStep 6359431 = 9539147) B9539147
theorem B1673743 : Blo 988596 1673743 := bstep (se 1 (by rfl) ⟨1255307, by rfl⟩ : syracuseStep 1673743 = 2510615) B2510615
theorem B5638679 : Blo 988596 5638679 := bstep (se 1 (by rfl) ⟨4229009, by rfl⟩ : syracuseStep 5638679 = 8458019) B8458019
theorem B2230919 : Blo 988596 2230919 := bstep (se 1 (by rfl) ⟨1673189, by rfl⟩ : syracuseStep 2230919 = 3346379) B3346379
theorem B2231099 : Blo 988596 2231099 := bstep (se 1 (by rfl) ⟨1673324, by rfl⟩ : syracuseStep 2231099 = 3346649) B3346649
theorem B3345299 : Blo 988596 3345299 := bstep (se 1 (by rfl) ⟨2508974, by rfl⟩ : syracuseStep 3345299 = 5017949) B5017949
theorem B11733913 : Blo 988596 11733913 := bstep (se 2 (by rfl) ⟨4400217, by rfl⟩ : syracuseStep 11733913 = 8800435) B8800435
theorem B2231225 : Blo 988596 2231225 := bstep (se 2 (by rfl) ⟨836709, by rfl⟩ : syracuseStep 2231225 = 1673419) B1673419
theorem B5639179 : Blo 988596 5639179 := bstep (se 1 (by rfl) ⟨4229384, by rfl⟩ : syracuseStep 5639179 = 8458769) B8458769
theorem B1674283 : Blo 988596 1674283 := bstep (se 1 (by rfl) ⟨1255712, by rfl⟩ : syracuseStep 1674283 = 2511425) B2511425
theorem B1674425 : Blo 988596 1674425 := bstep (se 2 (by rfl) ⟨627909, by rfl⟩ : syracuseStep 1674425 = 1255819) B1255819
theorem B2821321 : Blo 988596 2821321 := bstep (se 2 (by rfl) ⟨1057995, by rfl⟩ : syracuseStep 2821321 = 2115991) B2115991
theorem B2231567 : Blo 988596 2231567 := bstep (se 1 (by rfl) ⟨1673675, by rfl⟩ : syracuseStep 2231567 = 3347351) B3347351
theorem B2231585 : Blo 988596 2231585 := bstep (se 2 (by rfl) ⟨836844, by rfl⟩ : syracuseStep 2231585 = 1673689) B1673689
theorem B5016977 : Blo 988596 5016977 := bstep (se 2 (by rfl) ⟨1881366, by rfl⟩ : syracuseStep 5016977 = 3762733) B3762733
theorem B2854415 : Blo 988596 2854415 := bstep (se 1 (by rfl) ⟨2140811, by rfl⟩ : syracuseStep 2854415 = 4281623) B4281623
theorem B2821675 : Blo 988596 2821675 := bstep (se 1 (by rfl) ⟨2116256, by rfl⟩ : syracuseStep 2821675 = 4232513) B4232513
theorem B2231927 : Blo 988596 2231927 := bstep (se 1 (by rfl) ⟨1673945, by rfl⟩ : syracuseStep 2231927 = 3347891) B3347891
theorem B81301133 : Blo 988596 81301133 := bstep (se 3 (by rfl) ⟨15243962, by rfl⟩ : syracuseStep 81301133 = 30487925) B30487925
theorem B7147237 : Blo 988596 7147237 := bstep (se 4 (by rfl) ⟨670053, by rfl⟩ : syracuseStep 7147237 = 1340107) B1340107
theorem B7507727 : Blo 988596 7507727 := bstep (se 1 (by rfl) ⟨5630795, by rfl⟩ : syracuseStep 7507727 = 11261591) B11261591
theorem B2232107 : Blo 988596 2232107 := bstep (se 1 (by rfl) ⟨1674080, by rfl⟩ : syracuseStep 2232107 = 3348161) B3348161
theorem B2821949 : Blo 988596 2821949 := bstep (se 3 (by rfl) ⟨529115, by rfl⟩ : syracuseStep 2821949 = 1058231) B1058231
theorem B4067281 : Blo 988596 4067281 := bstep (se 2 (by rfl) ⟨1525230, by rfl⟩ : syracuseStep 4067281 = 3050461) B3050461
theorem B3051535 : Blo 988596 3051535 := bstep (se 1 (by rfl) ⟨2288651, by rfl⟩ : syracuseStep 3051535 = 4577303) B4577303
theorem B2232467 : Blo 988596 2232467 := bstep (se 1 (by rfl) ⟨1674350, by rfl⟩ : syracuseStep 2232467 = 3348701) B3348701
theorem B2232521 : Blo 988596 2232521 := bstep (se 2 (by rfl) ⟨837195, by rfl⟩ : syracuseStep 2232521 = 1674391) B1674391
theorem B3346703 : Blo 988596 3346703 := bstep (se 1 (by rfl) ⟨2510027, by rfl⟩ : syracuseStep 3346703 = 5020055) B5020055
theorem B9146657 : Blo 988596 9146657 := bstep (se 2 (by rfl) ⟨3429996, by rfl⟩ : syracuseStep 9146657 = 6859993) B6859993
theorem B108532061 : Blo 988596 108532061 := bstep (se 3 (by rfl) ⟨20349761, by rfl⟩ : syracuseStep 108532061 = 40699523) B40699523
theorem B4231709 : Blo 988596 4231709 := bstep (se 3 (by rfl) ⟨793445, by rfl⟩ : syracuseStep 4231709 = 1586891) B1586891
theorem B3346973 : Blo 988596 3346973 := bstep (se 3 (by rfl) ⟨627557, by rfl⟩ : syracuseStep 3346973 = 1255115) B1255115
theorem B4232051 : Blo 988596 4232051 := bstep (se 1 (by rfl) ⟨3174038, by rfl⟩ : syracuseStep 4232051 = 6348077) B6348077
theorem B2233223 : Blo 988596 2233223 := bstep (se 1 (by rfl) ⟨1674917, by rfl⟩ : syracuseStep 2233223 = 3349835) B3349835
theorem B5641163 : Blo 988596 5641163 := bstep (se 1 (by rfl) ⟨4230872, by rfl⟩ : syracuseStep 5641163 = 8461745) B8461745
theorem B4756445 : Blo 988596 4756445 := bstep (se 3 (by rfl) ⟨891833, by rfl⟩ : syracuseStep 4756445 = 1783667) B1783667
theorem B988603 : Blo 988596 988603 := bstep (se 1 (by rfl) ⟨741452, by rfl⟩ : syracuseStep 988603 = 1482905) B1482905
theorem B5019083 : Blo 988596 5019083 := bstep (se 1 (by rfl) ⟨3764312, by rfl⟩ : syracuseStep 5019083 = 7528625) B7528625
theorem B988679 : Blo 988596 988679 := bstep (se 1 (by rfl) ⟨741509, by rfl⟩ : syracuseStep 988679 = 1483019) B1483019
theorem B988687 : Blo 988596 988687 := bstep (se 1 (by rfl) ⟨741515, by rfl⟩ : syracuseStep 988687 = 1483031) B1483031
theorem B988731 : Blo 988596 988731 := bstep (se 1 (by rfl) ⟨741548, by rfl⟩ : syracuseStep 988731 = 1483097) B1483097
theorem B4757059 : Blo 988596 4757059 := bstep (se 1 (by rfl) ⟨3567794, by rfl⟩ : syracuseStep 4757059 = 7135589) B7135589
theorem B5346935 : Blo 988596 5346935 := bstep (se 1 (by rfl) ⟨4010201, by rfl⟩ : syracuseStep 5346935 = 8020403) B8020403
theorem B988807 : Blo 988596 988807 := bstep (se 1 (by rfl) ⟨741605, by rfl⟩ : syracuseStep 988807 = 1483211) B1483211
theorem B988815 : Blo 988596 988815 := bstep (se 1 (by rfl) ⟨741611, by rfl⟩ : syracuseStep 988815 = 1483223) B1483223
theorem B988859 : Blo 988596 988859 := bstep (se 1 (by rfl) ⟨741644, by rfl⟩ : syracuseStep 988859 = 1483289) B1483289
theorem B988935 : Blo 988596 988935 := bstep (se 1 (by rfl) ⟨741701, by rfl⟩ : syracuseStep 988935 = 1483403) B1483403
theorem B988943 : Blo 988596 988943 := bstep (se 1 (by rfl) ⟨741707, by rfl⟩ : syracuseStep 988943 = 1483415) B1483415
theorem B5019407 : Blo 988596 5019407 := bstep (se 1 (by rfl) ⟨3764555, by rfl⟩ : syracuseStep 5019407 = 7529111) B7529111
theorem B988987 : Blo 988596 988987 := bstep (se 1 (by rfl) ⟨741740, by rfl⟩ : syracuseStep 988987 = 1483481) B1483481
theorem B2824055 : Blo 988596 2824055 := bstep (se 1 (by rfl) ⟨2118041, by rfl⟩ : syracuseStep 2824055 = 4236083) B4236083
theorem B989063 : Blo 988596 989063 := bstep (se 1 (by rfl) ⟨741797, by rfl⟩ : syracuseStep 989063 = 1483595) B1483595
theorem B989071 : Blo 988596 989071 := bstep (se 1 (by rfl) ⟨741803, by rfl⟩ : syracuseStep 989071 = 1483607) B1483607
theorem B3348377 : Blo 988596 3348377 := bstep (se 2 (by rfl) ⟨1255641, by rfl⟩ : syracuseStep 3348377 = 2511283) B2511283
theorem B989115 : Blo 988596 989115 := bstep (se 1 (by rfl) ⟨741836, by rfl⟩ : syracuseStep 989115 = 1483673) B1483673
theorem B989191 : Blo 988596 989191 := bstep (se 1 (by rfl) ⟨741893, by rfl⟩ : syracuseStep 989191 = 1483787) B1483787
theorem B989199 : Blo 988596 989199 := bstep (se 1 (by rfl) ⟨741899, by rfl⟩ : syracuseStep 989199 = 1483799) B1483799
theorem B989243 : Blo 988596 989243 := bstep (se 1 (by rfl) ⟨741932, by rfl⟩ : syracuseStep 989243 = 1483865) B1483865
theorem B6035543 : Blo 988596 6035543 := bstep (se 1 (by rfl) ⟨4526657, by rfl⟩ : syracuseStep 6035543 = 9053315) B9053315
theorem B989319 : Blo 988596 989319 := bstep (se 1 (by rfl) ⟨741989, by rfl⟩ : syracuseStep 989319 = 1483979) B1483979
theorem B989327 : Blo 988596 989327 := bstep (se 1 (by rfl) ⟨741995, by rfl⟩ : syracuseStep 989327 = 1483991) B1483991
theorem B989371 : Blo 988596 989371 := bstep (se 1 (by rfl) ⟨742028, by rfl⟩ : syracuseStep 989371 = 1484057) B1484057
theorem B989447 : Blo 988596 989447 := bstep (se 1 (by rfl) ⟨742085, by rfl⟩ : syracuseStep 989447 = 1484171) B1484171
theorem B989455 : Blo 988596 989455 := bstep (se 1 (by rfl) ⟨742091, by rfl⟩ : syracuseStep 989455 = 1484183) B1484183
theorem B989499 : Blo 988596 989499 := bstep (se 1 (by rfl) ⟨742124, by rfl⟩ : syracuseStep 989499 = 1484249) B1484249
theorem B1251703 : Blo 988596 1251703 := bstep (se 1 (by rfl) ⟨938777, by rfl⟩ : syracuseStep 1251703 = 1877555) B1877555
theorem B989575 : Blo 988596 989575 := bstep (se 1 (by rfl) ⟨742181, by rfl⟩ : syracuseStep 989575 = 1484363) B1484363
theorem B989583 : Blo 988596 989583 := bstep (se 1 (by rfl) ⟨742187, by rfl⟩ : syracuseStep 989583 = 1484375) B1484375
theorem B2857369 : Blo 988596 2857369 := bstep (se 2 (by rfl) ⟨1071513, by rfl⟩ : syracuseStep 2857369 = 2143027) B2143027
theorem B989627 : Blo 988596 989627 := bstep (se 1 (by rfl) ⟨742220, by rfl⟩ : syracuseStep 989627 = 1484441) B1484441
theorem B989703 : Blo 988596 989703 := bstep (se 1 (by rfl) ⟨742277, by rfl⟩ : syracuseStep 989703 = 1484555) B1484555
theorem B989711 : Blo 988596 989711 := bstep (se 1 (by rfl) ⟨742283, by rfl⟩ : syracuseStep 989711 = 1484567) B1484567
theorem B1808939 : Blo 988596 1808939 := bstep (se 1 (by rfl) ⟨1356704, by rfl⟩ : syracuseStep 1808939 = 2713409) B2713409
theorem B989755 : Blo 988596 989755 := bstep (se 1 (by rfl) ⟨742316, by rfl⟩ : syracuseStep 989755 = 1484633) B1484633
theorem B3349079 : Blo 988596 3349079 := bstep (se 1 (by rfl) ⟨2511809, by rfl⟩ : syracuseStep 3349079 = 5023619) B5023619
theorem B989831 : Blo 988596 989831 := bstep (se 1 (by rfl) ⟨742373, by rfl⟩ : syracuseStep 989831 = 1484747) B1484747
theorem B989839 : Blo 988596 989839 := bstep (se 1 (by rfl) ⟨742379, by rfl⟩ : syracuseStep 989839 = 1484759) B1484759
theorem B1252027 : Blo 988596 1252027 := bstep (se 1 (by rfl) ⟨939020, by rfl⟩ : syracuseStep 1252027 = 1878041) B1878041
theorem B989883 : Blo 988596 989883 := bstep (se 1 (by rfl) ⟨742412, by rfl⟩ : syracuseStep 989883 = 1484825) B1484825
theorem B989959 : Blo 988596 989959 := bstep (se 1 (by rfl) ⟨742469, by rfl⟩ : syracuseStep 989959 = 1484939) B1484939
theorem B989967 : Blo 988596 989967 := bstep (se 1 (by rfl) ⟨742475, by rfl⟩ : syracuseStep 989967 = 1484951) B1484951
theorem B7150351 : Blo 988596 7150351 := bstep (se 1 (by rfl) ⟨5362763, by rfl⟩ : syracuseStep 7150351 = 10725527) B10725527
theorem B990011 : Blo 988596 990011 := bstep (se 1 (by rfl) ⟨742508, by rfl⟩ : syracuseStep 990011 = 1485017) B1485017
theorem B2005879 : Blo 988596 2005879 := bstep (se 1 (by rfl) ⟨1504409, by rfl⟩ : syracuseStep 2005879 = 3008819) B3008819
theorem B990087 : Blo 988596 990087 := bstep (se 1 (by rfl) ⟨742565, by rfl⟩ : syracuseStep 990087 = 1485131) B1485131
theorem B990095 : Blo 988596 990095 := bstep (se 1 (by rfl) ⟨742571, by rfl⟩ : syracuseStep 990095 = 1485143) B1485143
theorem B4234169 : Blo 988596 4234169 := bstep (se 2 (by rfl) ⟨1587813, by rfl⟩ : syracuseStep 4234169 = 3175627) B3175627
theorem B990139 : Blo 988596 990139 := bstep (se 1 (by rfl) ⟨742604, by rfl⟩ : syracuseStep 990139 = 1485209) B1485209
theorem B990215 : Blo 988596 990215 := bstep (se 1 (by rfl) ⟨742661, by rfl⟩ : syracuseStep 990215 = 1485323) B1485323
theorem B990223 : Blo 988596 990223 := bstep (se 1 (by rfl) ⟨742667, by rfl⟩ : syracuseStep 990223 = 1485335) B1485335
theorem B990267 : Blo 988596 990267 := bstep (se 1 (by rfl) ⟨742700, by rfl⟩ : syracuseStep 990267 = 1485401) B1485401
theorem B3349565 : Blo 988596 3349565 := bstep (se 3 (by rfl) ⟨628043, by rfl⟩ : syracuseStep 3349565 = 1256087) B1256087
theorem B990343 : Blo 988596 990343 := bstep (se 1 (by rfl) ⟨742757, by rfl⟩ : syracuseStep 990343 = 1485515) B1485515
theorem B990351 : Blo 988596 990351 := bstep (se 1 (by rfl) ⟨742763, by rfl⟩ : syracuseStep 990351 = 1485527) B1485527
theorem B1252523 : Blo 988596 1252523 := bstep (se 1 (by rfl) ⟨939392, by rfl⟩ : syracuseStep 1252523 = 1878785) B1878785
theorem B990395 : Blo 988596 990395 := bstep (se 1 (by rfl) ⟨742796, by rfl⟩ : syracuseStep 990395 = 1485593) B1485593
theorem B5020865 : Blo 988596 5020865 := bstep (se 2 (by rfl) ⟨1882824, by rfl⟩ : syracuseStep 5020865 = 3765649) B3765649
theorem B4234477 : Blo 988596 4234477 := bstep (se 3 (by rfl) ⟨793964, by rfl⟩ : syracuseStep 4234477 = 1587929) B1587929
theorem B990471 : Blo 988596 990471 := bstep (se 1 (by rfl) ⟨742853, by rfl⟩ : syracuseStep 990471 = 1485707) B1485707
theorem B990479 : Blo 988596 990479 := bstep (se 1 (by rfl) ⟨742859, by rfl⟩ : syracuseStep 990479 = 1485719) B1485719
theorem B4234511 : Blo 988596 4234511 := bstep (se 1 (by rfl) ⟨3175883, by rfl⟩ : syracuseStep 4234511 = 6351767) B6351767
theorem B5643553 : Blo 988596 5643553 := bstep (se 2 (by rfl) ⟨2116332, by rfl⟩ : syracuseStep 5643553 = 4232665) B4232665
theorem B990523 : Blo 988596 990523 := bstep (se 1 (by rfl) ⟨742892, by rfl⟩ : syracuseStep 990523 = 1485785) B1485785
theorem B19045763 : Blo 988596 19045763 := bstep (se 1 (by rfl) ⟨14284322, by rfl⟩ : syracuseStep 19045763 = 28568645) B28568645
theorem B990599 : Blo 988596 990599 := bstep (se 1 (by rfl) ⟨742949, by rfl⟩ : syracuseStep 990599 = 1485899) B1485899
theorem B990607 : Blo 988596 990607 := bstep (se 1 (by rfl) ⟨742955, by rfl⟩ : syracuseStep 990607 = 1485911) B1485911
theorem B990651 : Blo 988596 990651 := bstep (se 1 (by rfl) ⟨742988, by rfl⟩ : syracuseStep 990651 = 1485977) B1485977
theorem B5086723 : Blo 988596 5086723 := bstep (se 1 (by rfl) ⟨3815042, by rfl⟩ : syracuseStep 5086723 = 7630085) B7630085
theorem B990727 : Blo 988596 990727 := bstep (se 1 (by rfl) ⟨743045, by rfl⟩ : syracuseStep 990727 = 1486091) B1486091
theorem B990735 : Blo 988596 990735 := bstep (se 1 (by rfl) ⟨743051, by rfl⟩ : syracuseStep 990735 = 1486103) B1486103
theorem B990779 : Blo 988596 990779 := bstep (se 1 (by rfl) ⟨743084, by rfl⟩ : syracuseStep 990779 = 1486169) B1486169
theorem B1252999 : Blo 988596 1252999 := bstep (se 1 (by rfl) ⟨939749, by rfl⟩ : syracuseStep 1252999 = 1879499) B1879499
theorem B990855 : Blo 988596 990855 := bstep (se 1 (by rfl) ⟨743141, by rfl⟩ : syracuseStep 990855 = 1486283) B1486283
theorem B990863 : Blo 988596 990863 := bstep (se 1 (by rfl) ⟨743147, by rfl⟩ : syracuseStep 990863 = 1486295) B1486295
theorem B990907 : Blo 988596 990907 := bstep (se 1 (by rfl) ⟨743180, by rfl⟩ : syracuseStep 990907 = 1486361) B1486361
theorem B990983 : Blo 988596 990983 := bstep (se 1 (by rfl) ⟨743237, by rfl⟩ : syracuseStep 990983 = 1486475) B1486475
theorem B990991 : Blo 988596 990991 := bstep (se 1 (by rfl) ⟨743243, by rfl⟩ : syracuseStep 990991 = 1486487) B1486487
theorem B45817649 : Blo 988596 45817649 := bstep (se 2 (by rfl) ⟨17181618, by rfl⟩ : syracuseStep 45817649 = 34363237) B34363237
theorem B991035 : Blo 988596 991035 := bstep (se 1 (by rfl) ⟨743276, by rfl⟩ : syracuseStep 991035 = 1486553) B1486553
theorem B991111 : Blo 988596 991111 := bstep (se 1 (by rfl) ⟨743333, by rfl⟩ : syracuseStep 991111 = 1486667) B1486667
theorem B991119 : Blo 988596 991119 := bstep (se 1 (by rfl) ⟨743339, by rfl⟩ : syracuseStep 991119 = 1486679) B1486679
theorem B991163 : Blo 988596 991163 := bstep (se 1 (by rfl) ⟨743372, by rfl⟩ : syracuseStep 991163 = 1486745) B1486745
theorem B991239 : Blo 988596 991239 := bstep (se 1 (by rfl) ⟨743429, by rfl⟩ : syracuseStep 991239 = 1486859) B1486859
theorem B991247 : Blo 988596 991247 := bstep (se 1 (by rfl) ⟨743435, by rfl⟩ : syracuseStep 991247 = 1486871) B1486871
theorem B991291 : Blo 988596 991291 := bstep (se 1 (by rfl) ⟨743468, by rfl⟩ : syracuseStep 991291 = 1486937) B1486937
theorem B4071491 : Blo 988596 4071491 := bstep (se 1 (by rfl) ⟨3053618, by rfl⟩ : syracuseStep 4071491 = 6107237) B6107237
theorem B1253495 : Blo 988596 1253495 := bstep (se 1 (by rfl) ⟨940121, by rfl⟩ : syracuseStep 1253495 = 1880243) B1880243
theorem B991367 : Blo 988596 991367 := bstep (se 1 (by rfl) ⟨743525, by rfl⟩ : syracuseStep 991367 = 1487051) B1487051
theorem B991375 : Blo 988596 991375 := bstep (se 1 (by rfl) ⟨743531, by rfl⟩ : syracuseStep 991375 = 1487063) B1487063
theorem B1482923 : Blo 988596 1482923 := bstep (se 1 (by rfl) ⟨1112192, by rfl⟩ : syracuseStep 1482923 = 2224385) B2224385
theorem B991419 : Blo 988596 991419 := bstep (se 1 (by rfl) ⟨743564, by rfl⟩ : syracuseStep 991419 = 1487129) B1487129
theorem B1482953 : Blo 988596 1482953 := bstep (se 2 (by rfl) ⟨556107, by rfl⟩ : syracuseStep 1482953 = 1112215) B1112215
theorem B991495 : Blo 988596 991495 := bstep (se 1 (by rfl) ⟨743621, by rfl⟩ : syracuseStep 991495 = 1487243) B1487243
theorem B1253647 : Blo 988596 1253647 := bstep (se 1 (by rfl) ⟨940235, by rfl⟩ : syracuseStep 1253647 = 1880471) B1880471
theorem B991503 : Blo 988596 991503 := bstep (se 1 (by rfl) ⟨743627, by rfl⟩ : syracuseStep 991503 = 1487255) B1487255
theorem B2826539 : Blo 988596 2826539 := bstep (se 1 (by rfl) ⟨2119904, by rfl⟩ : syracuseStep 2826539 = 4239809) B4239809
theorem B1483067 : Blo 988596 1483067 := bstep (se 1 (by rfl) ⟨1112300, by rfl⟩ : syracuseStep 1483067 = 2224601) B2224601
theorem B991547 : Blo 988596 991547 := bstep (se 1 (by rfl) ⟨743660, by rfl⟩ : syracuseStep 991547 = 1487321) B1487321
theorem B1483127 : Blo 988596 1483127 := bstep (se 1 (by rfl) ⟨1112345, by rfl⟩ : syracuseStep 1483127 = 2224691) B2224691
theorem B991623 : Blo 988596 991623 := bstep (se 1 (by rfl) ⟨743717, by rfl⟩ : syracuseStep 991623 = 1487435) B1487435
theorem B1483151 : Blo 988596 1483151 := bstep (se 1 (by rfl) ⟨1112363, by rfl⟩ : syracuseStep 1483151 = 2224727) B2224727
theorem B991631 : Blo 988596 991631 := bstep (se 1 (by rfl) ⟨743723, by rfl⟩ : syracuseStep 991631 = 1487447) B1487447
theorem B1483193 : Blo 988596 1483193 := bstep (se 2 (by rfl) ⟨556197, by rfl⟩ : syracuseStep 1483193 = 1112395) B1112395
theorem B1253819 : Blo 988596 1253819 := bstep (se 1 (by rfl) ⟨940364, by rfl⟩ : syracuseStep 1253819 = 1880729) B1880729
theorem B991675 : Blo 988596 991675 := bstep (se 1 (by rfl) ⟨743756, by rfl⟩ : syracuseStep 991675 = 1487513) B1487513
theorem B5022161 : Blo 988596 5022161 := bstep (se 2 (by rfl) ⟨1883310, by rfl⟩ : syracuseStep 5022161 = 3766621) B3766621
theorem B1483271 : Blo 988596 1483271 := bstep (se 1 (by rfl) ⟨1112453, by rfl⟩ : syracuseStep 1483271 = 2224907) B2224907
theorem B991751 : Blo 988596 991751 := bstep (se 1 (by rfl) ⟨743813, by rfl⟩ : syracuseStep 991751 = 1487627) B1487627
theorem B991759 : Blo 988596 991759 := bstep (se 1 (by rfl) ⟨743819, by rfl⟩ : syracuseStep 991759 = 1487639) B1487639
theorem B5644829 : Blo 988596 5644829 := bstep (se 3 (by rfl) ⟨1058405, by rfl⟩ : syracuseStep 5644829 = 2116811) B2116811
theorem B1483307 : Blo 988596 1483307 := bstep (se 1 (by rfl) ⟨1112480, by rfl⟩ : syracuseStep 1483307 = 2224961) B2224961
theorem B991803 : Blo 988596 991803 := bstep (se 1 (by rfl) ⟨743852, by rfl⟩ : syracuseStep 991803 = 1487705) B1487705
theorem B1483337 : Blo 988596 1483337 := bstep (se 2 (by rfl) ⟨556251, by rfl⟩ : syracuseStep 1483337 = 1112503) B1112503
theorem B991879 : Blo 988596 991879 := bstep (se 1 (by rfl) ⟨743909, by rfl⟩ : syracuseStep 991879 = 1487819) B1487819
theorem B991887 : Blo 988596 991887 := bstep (se 1 (by rfl) ⟨743915, by rfl⟩ : syracuseStep 991887 = 1487831) B1487831
theorem B1483451 : Blo 988596 1483451 := bstep (se 1 (by rfl) ⟨1112588, by rfl⟩ : syracuseStep 1483451 = 2225177) B2225177
theorem B991931 : Blo 988596 991931 := bstep (se 1 (by rfl) ⟨743948, by rfl⟩ : syracuseStep 991931 = 1487897) B1487897
theorem B1483511 : Blo 988596 1483511 := bstep (se 1 (by rfl) ⟨1112633, by rfl⟩ : syracuseStep 1483511 = 2225267) B2225267
theorem B992007 : Blo 988596 992007 := bstep (se 1 (by rfl) ⟨744005, by rfl⟩ : syracuseStep 992007 = 1488011) B1488011
theorem B1483535 : Blo 988596 1483535 := bstep (se 1 (by rfl) ⟨1112651, by rfl⟩ : syracuseStep 1483535 = 2225303) B2225303
theorem B992015 : Blo 988596 992015 := bstep (se 1 (by rfl) ⟨744011, by rfl⟩ : syracuseStep 992015 = 1488023) B1488023
theorem B1483577 : Blo 988596 1483577 := bstep (se 2 (by rfl) ⟨556341, by rfl⟩ : syracuseStep 1483577 = 1112683) B1112683
theorem B992059 : Blo 988596 992059 := bstep (se 1 (by rfl) ⟨744044, by rfl⟩ : syracuseStep 992059 = 1488089) B1488089
theorem B1876871 : Blo 988596 1876871 := bstep (se 1 (by rfl) ⟨1407653, by rfl⟩ : syracuseStep 1876871 = 2815307) B2815307
theorem B1483655 : Blo 988596 1483655 := bstep (se 1 (by rfl) ⟨1112741, by rfl⟩ : syracuseStep 1483655 = 2225483) B2225483
theorem B992135 : Blo 988596 992135 := bstep (se 1 (by rfl) ⟨744101, by rfl⟩ : syracuseStep 992135 = 1488203) B1488203
theorem B992143 : Blo 988596 992143 := bstep (se 1 (by rfl) ⟨744107, by rfl⟩ : syracuseStep 992143 = 1488215) B1488215
theorem B1483691 : Blo 988596 1483691 := bstep (se 1 (by rfl) ⟨1112768, by rfl⟩ : syracuseStep 1483691 = 2225537) B2225537
theorem B992187 : Blo 988596 992187 := bstep (se 1 (by rfl) ⟨744140, by rfl⟩ : syracuseStep 992187 = 1488281) B1488281
theorem B1483721 : Blo 988596 1483721 := bstep (se 2 (by rfl) ⟨556395, by rfl⟩ : syracuseStep 1483721 = 1112791) B1112791
theorem B992263 : Blo 988596 992263 := bstep (se 1 (by rfl) ⟨744197, by rfl⟩ : syracuseStep 992263 = 1488395) B1488395
theorem B992271 : Blo 988596 992271 := bstep (se 1 (by rfl) ⟨744203, by rfl⟩ : syracuseStep 992271 = 1488407) B1488407
theorem B1483835 : Blo 988596 1483835 := bstep (se 1 (by rfl) ⟨1112876, by rfl⟩ : syracuseStep 1483835 = 2225753) B2225753
theorem B992315 : Blo 988596 992315 := bstep (se 1 (by rfl) ⟨744236, by rfl⟩ : syracuseStep 992315 = 1488473) B1488473
theorem B1483895 : Blo 988596 1483895 := bstep (se 1 (by rfl) ⟨1112921, by rfl⟩ : syracuseStep 1483895 = 2225843) B2225843
theorem B992391 : Blo 988596 992391 := bstep (se 1 (by rfl) ⟨744293, by rfl⟩ : syracuseStep 992391 = 1488587) B1488587
theorem B1483919 : Blo 988596 1483919 := bstep (se 1 (by rfl) ⟨1112939, by rfl⟩ : syracuseStep 1483919 = 2225879) B2225879
theorem B992399 : Blo 988596 992399 := bstep (se 1 (by rfl) ⟨744299, by rfl⟩ : syracuseStep 992399 = 1488599) B1488599
theorem B1483961 : Blo 988596 1483961 := bstep (se 2 (by rfl) ⟨556485, by rfl⟩ : syracuseStep 1483961 = 1112971) B1112971
theorem B992443 : Blo 988596 992443 := bstep (se 1 (by rfl) ⟨744332, by rfl⟩ : syracuseStep 992443 = 1488665) B1488665
theorem B1484039 : Blo 988596 1484039 := bstep (se 1 (by rfl) ⟨1113029, by rfl⟩ : syracuseStep 1484039 = 2226059) B2226059
theorem B992519 : Blo 988596 992519 := bstep (se 1 (by rfl) ⟨744389, by rfl⟩ : syracuseStep 992519 = 1488779) B1488779
theorem B992527 : Blo 988596 992527 := bstep (se 1 (by rfl) ⟨744395, by rfl⟩ : syracuseStep 992527 = 1488791) B1488791
theorem B1484075 : Blo 988596 1484075 := bstep (se 1 (by rfl) ⟨1113056, by rfl⟩ : syracuseStep 1484075 = 2226113) B2226113
theorem B992571 : Blo 988596 992571 := bstep (se 1 (by rfl) ⟨744428, by rfl⟩ : syracuseStep 992571 = 1488857) B1488857
theorem B1484105 : Blo 988596 1484105 := bstep (se 2 (by rfl) ⟨556539, by rfl⟩ : syracuseStep 1484105 = 1113079) B1113079
theorem B1254791 : Blo 988596 1254791 := bstep (se 1 (by rfl) ⟨941093, by rfl⟩ : syracuseStep 1254791 = 1882187) B1882187
theorem B1484219 : Blo 988596 1484219 := bstep (se 1 (by rfl) ⟨1113164, by rfl⟩ : syracuseStep 1484219 = 2226329) B2226329
theorem B1484279 : Blo 988596 1484279 := bstep (se 1 (by rfl) ⟨1113209, by rfl⟩ : syracuseStep 1484279 = 2226419) B2226419
theorem B1484303 : Blo 988596 1484303 := bstep (se 1 (by rfl) ⟨1113227, by rfl⟩ : syracuseStep 1484303 = 2226455) B2226455
theorem B1484345 : Blo 988596 1484345 := bstep (se 2 (by rfl) ⟨556629, by rfl⟩ : syracuseStep 1484345 = 1113259) B1113259
theorem B4236887 : Blo 988596 4236887 := bstep (se 1 (by rfl) ⟨3177665, by rfl⟩ : syracuseStep 4236887 = 6355331) B6355331
theorem B1484423 : Blo 988596 1484423 := bstep (se 1 (by rfl) ⟨1113317, by rfl⟩ : syracuseStep 1484423 = 2226635) B2226635
theorem B1484459 : Blo 988596 1484459 := bstep (se 1 (by rfl) ⟨1113344, by rfl⟩ : syracuseStep 1484459 = 2226689) B2226689
theorem B1058491 : Blo 988596 1058491 := bstep (se 1 (by rfl) ⟨793868, by rfl⟩ : syracuseStep 1058491 = 1587737) B1587737
theorem B1484489 : Blo 988596 1484489 := bstep (se 2 (by rfl) ⟨556683, by rfl⟩ : syracuseStep 1484489 = 1113367) B1113367
theorem B1484603 : Blo 988596 1484603 := bstep (se 1 (by rfl) ⟨1113452, by rfl⟩ : syracuseStep 1484603 = 2226905) B2226905
theorem B1484663 : Blo 988596 1484663 := bstep (se 1 (by rfl) ⟨1113497, by rfl⟩ : syracuseStep 1484663 = 2226995) B2226995
theorem B1484687 : Blo 988596 1484687 := bstep (se 1 (by rfl) ⟨1113515, by rfl⟩ : syracuseStep 1484687 = 2227031) B2227031
theorem B1484729 : Blo 988596 1484729 := bstep (se 2 (by rfl) ⟨556773, by rfl⟩ : syracuseStep 1484729 = 1113547) B1113547
theorem B1484807 : Blo 988596 1484807 := bstep (se 1 (by rfl) ⟨1113605, by rfl⟩ : syracuseStep 1484807 = 2227211) B2227211
theorem B1189895 : Blo 988596 1189895 := bstep (se 1 (by rfl) ⟨892421, by rfl⟩ : syracuseStep 1189895 = 1784843) B1784843
theorem B1255439 : Blo 988596 1255439 := bstep (se 1 (by rfl) ⟨941579, by rfl⟩ : syracuseStep 1255439 = 1883159) B1883159
theorem B1484843 : Blo 988596 1484843 := bstep (se 1 (by rfl) ⟨1113632, by rfl⟩ : syracuseStep 1484843 = 2227265) B2227265
theorem B1484873 : Blo 988596 1484873 := bstep (se 2 (by rfl) ⟨556827, by rfl⟩ : syracuseStep 1484873 = 1113655) B1113655
theorem B1484987 : Blo 988596 1484987 := bstep (se 1 (by rfl) ⟨1113740, by rfl⟩ : syracuseStep 1484987 = 2227481) B2227481
theorem B1485047 : Blo 988596 1485047 := bstep (se 1 (by rfl) ⟨1113785, by rfl⟩ : syracuseStep 1485047 = 2227571) B2227571
theorem B1485071 : Blo 988596 1485071 := bstep (se 1 (by rfl) ⟨1113803, by rfl⟩ : syracuseStep 1485071 = 2227607) B2227607
theorem B1485113 : Blo 988596 1485113 := bstep (se 2 (by rfl) ⟨556917, by rfl⟩ : syracuseStep 1485113 = 1113835) B1113835
theorem B3811643 : Blo 988596 3811643 := bstep (se 1 (by rfl) ⟨2858732, by rfl⟩ : syracuseStep 3811643 = 5717465) B5717465
theorem B19048769 : Blo 988596 19048769 := bstep (se 2 (by rfl) ⟨7143288, by rfl⟩ : syracuseStep 19048769 = 14286577) B14286577
theorem B24095069 : Blo 988596 24095069 := bstep (se 3 (by rfl) ⟨4517825, by rfl⟩ : syracuseStep 24095069 = 9035651) B9035651
theorem B1485191 : Blo 988596 1485191 := bstep (se 1 (by rfl) ⟨1113893, by rfl⟩ : syracuseStep 1485191 = 2227787) B2227787
theorem B1485227 : Blo 988596 1485227 := bstep (se 1 (by rfl) ⟨1113920, by rfl⟩ : syracuseStep 1485227 = 2227841) B2227841
theorem B1485257 : Blo 988596 1485257 := bstep (se 2 (by rfl) ⟨556971, by rfl⟩ : syracuseStep 1485257 = 1113943) B1113943
theorem B1812937 : Blo 988596 1812937 := bstep (se 2 (by rfl) ⟨679851, by rfl⟩ : syracuseStep 1812937 = 1359703) B1359703
theorem B5024267 : Blo 988596 5024267 := bstep (se 1 (by rfl) ⟨3768200, by rfl⟩ : syracuseStep 5024267 = 7536401) B7536401
theorem B2140705 : Blo 988596 2140705 := bstep (se 2 (by rfl) ⟨802764, by rfl⟩ : syracuseStep 2140705 = 1605529) B1605529
theorem B1485371 : Blo 988596 1485371 := bstep (se 1 (by rfl) ⟨1114028, by rfl⟩ : syracuseStep 1485371 = 2228057) B2228057
theorem B1485431 : Blo 988596 1485431 := bstep (se 1 (by rfl) ⟨1114073, by rfl⟩ : syracuseStep 1485431 = 2228147) B2228147
theorem B1485455 : Blo 988596 1485455 := bstep (se 1 (by rfl) ⟨1114091, by rfl⟩ : syracuseStep 1485455 = 2228183) B2228183
theorem B5024429 : Blo 988596 5024429 := bstep (se 3 (by rfl) ⟨942080, by rfl⟩ : syracuseStep 5024429 = 1884161) B1884161
theorem B1485497 : Blo 988596 1485497 := bstep (se 2 (by rfl) ⟨557061, by rfl⟩ : syracuseStep 1485497 = 1114123) B1114123
theorem B1485575 : Blo 988596 1485575 := bstep (se 1 (by rfl) ⟨1114181, by rfl⟩ : syracuseStep 1485575 = 2228363) B2228363
theorem B1485611 : Blo 988596 1485611 := bstep (se 1 (by rfl) ⟨1114208, by rfl⟩ : syracuseStep 1485611 = 2228417) B2228417
theorem B1485641 : Blo 988596 1485641 := bstep (se 2 (by rfl) ⟨557115, by rfl⟩ : syracuseStep 1485641 = 1114231) B1114231
theorem B1485755 : Blo 988596 1485755 := bstep (se 1 (by rfl) ⟨1114316, by rfl⟩ : syracuseStep 1485755 = 2228633) B2228633
theorem B1485815 : Blo 988596 1485815 := bstep (se 1 (by rfl) ⟨1114361, by rfl⟩ : syracuseStep 1485815 = 2228723) B2228723
theorem B11283461 : Blo 988596 11283461 := bstep (se 4 (by rfl) ⟨1057824, by rfl⟩ : syracuseStep 11283461 = 2115649) B2115649
theorem B20327435 : Blo 988596 20327435 := bstep (se 1 (by rfl) ⟨15245576, by rfl⟩ : syracuseStep 20327435 = 30491153) B30491153
theorem B1485839 : Blo 988596 1485839 := bstep (se 1 (by rfl) ⟨1114379, by rfl⟩ : syracuseStep 1485839 = 2228759) B2228759
theorem B1485881 : Blo 988596 1485881 := bstep (se 2 (by rfl) ⟨557205, by rfl⟩ : syracuseStep 1485881 = 1114411) B1114411
theorem B5647427 : Blo 988596 5647427 := bstep (se 1 (by rfl) ⟨4235570, by rfl⟩ : syracuseStep 5647427 = 8471141) B8471141
theorem B1485959 : Blo 988596 1485959 := bstep (se 1 (by rfl) ⟨1114469, by rfl⟩ : syracuseStep 1485959 = 2228939) B2228939
theorem B1485995 : Blo 988596 1485995 := bstep (se 1 (by rfl) ⟨1114496, by rfl⟩ : syracuseStep 1485995 = 2228993) B2228993
theorem B1486025 : Blo 988596 1486025 := bstep (se 2 (by rfl) ⟨557259, by rfl⟩ : syracuseStep 1486025 = 1114519) B1114519
theorem B1879355 : Blo 988596 1879355 := bstep (se 1 (by rfl) ⟨1409516, by rfl⟩ : syracuseStep 1879355 = 2819033) B2819033
theorem B1486139 : Blo 988596 1486139 := bstep (se 1 (by rfl) ⟨1114604, by rfl⟩ : syracuseStep 1486139 = 2229209) B2229209
theorem B1486199 : Blo 988596 1486199 := bstep (se 1 (by rfl) ⟨1114649, by rfl⟩ : syracuseStep 1486199 = 2229299) B2229299
theorem B2010503 : Blo 988596 2010503 := bstep (se 1 (by rfl) ⟨1507877, by rfl⟩ : syracuseStep 2010503 = 3015755) B3015755
theorem B1486223 : Blo 988596 1486223 := bstep (se 1 (by rfl) ⟨1114667, by rfl⟩ : syracuseStep 1486223 = 2229335) B2229335
theorem B1486265 : Blo 988596 1486265 := bstep (se 2 (by rfl) ⟨557349, by rfl⟩ : syracuseStep 1486265 = 1114699) B1114699
theorem B4238801 : Blo 988596 4238801 := bstep (se 2 (by rfl) ⟨1589550, by rfl⟩ : syracuseStep 4238801 = 3179101) B3179101
theorem B1486343 : Blo 988596 1486343 := bstep (se 1 (by rfl) ⟨1114757, by rfl⟩ : syracuseStep 1486343 = 2229515) B2229515
theorem B1486379 : Blo 988596 1486379 := bstep (se 1 (by rfl) ⟨1114784, by rfl⟩ : syracuseStep 1486379 = 2229569) B2229569
theorem B1486409 : Blo 988596 1486409 := bstep (se 2 (by rfl) ⟨557403, by rfl⟩ : syracuseStep 1486409 = 1114807) B1114807
theorem B2010809 : Blo 988596 2010809 := bstep (se 2 (by rfl) ⟨754053, by rfl⟩ : syracuseStep 2010809 = 1508107) B1508107
theorem B1486523 : Blo 988596 1486523 := bstep (se 1 (by rfl) ⟨1114892, by rfl⟩ : syracuseStep 1486523 = 2229785) B2229785
theorem B1584841 : Blo 988596 1584841 := bstep (se 2 (by rfl) ⟨594315, by rfl⟩ : syracuseStep 1584841 = 1188631) B1188631
theorem B1486583 : Blo 988596 1486583 := bstep (se 1 (by rfl) ⟨1114937, by rfl⟩ : syracuseStep 1486583 = 2229875) B2229875
theorem B1486607 : Blo 988596 1486607 := bstep (se 1 (by rfl) ⟨1114955, by rfl⟩ : syracuseStep 1486607 = 2229911) B2229911
theorem B1879841 : Blo 988596 1879841 := bstep (se 2 (by rfl) ⟨704940, by rfl⟩ : syracuseStep 1879841 = 1409881) B1409881
theorem B1486649 : Blo 988596 1486649 := bstep (se 2 (by rfl) ⟨557493, by rfl⟩ : syracuseStep 1486649 = 1114987) B1114987
theorem B2502515 : Blo 988596 2502515 := bstep (se 1 (by rfl) ⟨1876886, by rfl⟩ : syracuseStep 2502515 = 3753773) B3753773
theorem B2502535 : Blo 988596 2502535 := bstep (se 1 (by rfl) ⟨1876901, by rfl⟩ : syracuseStep 2502535 = 3753803) B3753803
theorem B1486727 : Blo 988596 1486727 := bstep (se 1 (by rfl) ⟨1115045, by rfl⟩ : syracuseStep 1486727 = 2230091) B2230091
theorem B1486763 : Blo 988596 1486763 := bstep (se 1 (by rfl) ⟨1115072, by rfl⟩ : syracuseStep 1486763 = 2230145) B2230145
theorem B1585097 : Blo 988596 1585097 := bstep (se 2 (by rfl) ⟨594411, by rfl⟩ : syracuseStep 1585097 = 1188823) B1188823
theorem B1486793 : Blo 988596 1486793 := bstep (se 2 (by rfl) ⟨557547, by rfl⟩ : syracuseStep 1486793 = 1115095) B1115095
theorem B1486907 : Blo 988596 1486907 := bstep (se 1 (by rfl) ⟨1115180, by rfl⟩ : syracuseStep 1486907 = 2230361) B2230361
theorem B1486967 : Blo 988596 1486967 := bstep (se 1 (by rfl) ⟨1115225, by rfl⟩ : syracuseStep 1486967 = 2230451) B2230451
theorem B1486991 : Blo 988596 1486991 := bstep (se 1 (by rfl) ⟨1115243, by rfl⟩ : syracuseStep 1486991 = 2230487) B2230487
theorem B2502809 : Blo 988596 2502809 := bstep (se 2 (by rfl) ⟨938553, by rfl⟩ : syracuseStep 2502809 = 1877107) B1877107
theorem B1487033 : Blo 988596 1487033 := bstep (se 2 (by rfl) ⟨557637, by rfl⟩ : syracuseStep 1487033 = 1115275) B1115275
theorem B1487111 : Blo 988596 1487111 := bstep (se 1 (by rfl) ⟨1115333, by rfl⟩ : syracuseStep 1487111 = 2230667) B2230667
theorem B1487147 : Blo 988596 1487147 := bstep (se 1 (by rfl) ⟨1115360, by rfl⟩ : syracuseStep 1487147 = 2230721) B2230721
theorem B2502971 : Blo 988596 2502971 := bstep (se 1 (by rfl) ⟨1877228, by rfl⟩ : syracuseStep 2502971 = 3754457) B3754457
theorem B7516475 : Blo 988596 7516475 := bstep (se 1 (by rfl) ⟨5637356, by rfl⟩ : syracuseStep 7516475 = 11274713) B11274713
theorem B1487177 : Blo 988596 1487177 := bstep (se 2 (by rfl) ⟨557691, by rfl⟩ : syracuseStep 1487177 = 1115383) B1115383
theorem B1487291 : Blo 988596 1487291 := bstep (se 1 (by rfl) ⟨1115468, by rfl⟩ : syracuseStep 1487291 = 2230937) B2230937
theorem B1487351 : Blo 988596 1487351 := bstep (se 1 (by rfl) ⟨1115513, by rfl⟩ : syracuseStep 1487351 = 2231027) B2231027
theorem B2503183 : Blo 988596 2503183 := bstep (se 1 (by rfl) ⟨1877387, by rfl⟩ : syracuseStep 2503183 = 3754775) B3754775
theorem B1487375 : Blo 988596 1487375 := bstep (se 1 (by rfl) ⟨1115531, by rfl⟩ : syracuseStep 1487375 = 2231063) B2231063
theorem B5354027 : Blo 988596 5354027 := bstep (se 1 (by rfl) ⟨4015520, by rfl⟩ : syracuseStep 5354027 = 8031041) B8031041
theorem B1487417 : Blo 988596 1487417 := bstep (se 2 (by rfl) ⟨557781, by rfl⟩ : syracuseStep 1487417 = 1115563) B1115563
theorem B9024119 : Blo 988596 9024119 := bstep (se 1 (by rfl) ⟨6768089, by rfl⟩ : syracuseStep 9024119 = 13536179) B13536179
theorem B1487495 : Blo 988596 1487495 := bstep (se 1 (by rfl) ⟨1115621, by rfl⟩ : syracuseStep 1487495 = 2231243) B2231243
theorem B1487531 : Blo 988596 1487531 := bstep (se 1 (by rfl) ⟨1115648, by rfl⟩ : syracuseStep 1487531 = 2231297) B2231297
theorem B1487561 : Blo 988596 1487561 := bstep (se 2 (by rfl) ⟨557835, by rfl⟩ : syracuseStep 1487561 = 1115671) B1115671
theorem B2503457 : Blo 988596 2503457 := bstep (se 2 (by rfl) ⟨938796, by rfl⟩ : syracuseStep 2503457 = 1877593) B1877593
theorem B5649203 : Blo 988596 5649203 := bstep (se 1 (by rfl) ⟨4236902, by rfl⟩ : syracuseStep 5649203 = 8473805) B8473805
theorem B1487675 : Blo 988596 1487675 := bstep (se 1 (by rfl) ⟨1115756, by rfl⟩ : syracuseStep 1487675 = 2231513) B2231513
theorem B1487735 : Blo 988596 1487735 := bstep (se 1 (by rfl) ⟨1115801, by rfl⟩ : syracuseStep 1487735 = 2231603) B2231603
theorem B1487759 : Blo 988596 1487759 := bstep (se 1 (by rfl) ⟨1115819, by rfl⟩ : syracuseStep 1487759 = 2231639) B2231639
theorem B1487801 : Blo 988596 1487801 := bstep (se 2 (by rfl) ⟨557925, by rfl⟩ : syracuseStep 1487801 = 1115851) B1115851
theorem B1487879 : Blo 988596 1487879 := bstep (se 1 (by rfl) ⟨1115909, by rfl⟩ : syracuseStep 1487879 = 2231819) B2231819
theorem B1487915 : Blo 988596 1487915 := bstep (se 1 (by rfl) ⟨1115936, by rfl⟩ : syracuseStep 1487915 = 2231873) B2231873
theorem B8467517 : Blo 988596 8467517 := bstep (se 3 (by rfl) ⟨1587659, by rfl⟩ : syracuseStep 8467517 = 3175319) B3175319
theorem B5715011 : Blo 988596 5715011 := bstep (se 1 (by rfl) ⟨4286258, by rfl⟩ : syracuseStep 5715011 = 8572517) B8572517
theorem B1487945 : Blo 988596 1487945 := bstep (se 2 (by rfl) ⟨557979, by rfl⟩ : syracuseStep 1487945 = 1115959) B1115959
theorem B4011095 : Blo 988596 4011095 := bstep (se 1 (by rfl) ⟨3008321, by rfl⟩ : syracuseStep 4011095 = 6016643) B6016643
theorem B1488059 : Blo 988596 1488059 := bstep (se 1 (by rfl) ⟨1116044, by rfl⟩ : syracuseStep 1488059 = 2232089) B2232089
theorem B4764865 : Blo 988596 4764865 := bstep (se 2 (by rfl) ⟨1786824, by rfl⟩ : syracuseStep 4764865 = 3573649) B3573649
theorem B1488119 : Blo 988596 1488119 := bstep (se 1 (by rfl) ⟨1116089, by rfl⟩ : syracuseStep 1488119 = 2232179) B2232179
theorem B1783055 : Blo 988596 1783055 := bstep (se 1 (by rfl) ⟨1337291, by rfl⟩ : syracuseStep 1783055 = 2674583) B2674583
theorem B1488143 : Blo 988596 1488143 := bstep (se 1 (by rfl) ⟨1116107, by rfl⟩ : syracuseStep 1488143 = 2232215) B2232215
theorem B1488185 : Blo 988596 1488185 := bstep (se 2 (by rfl) ⟨558069, by rfl⟩ : syracuseStep 1488185 = 1116139) B1116139
theorem B1488263 : Blo 988596 1488263 := bstep (se 1 (by rfl) ⟨1116197, by rfl⟩ : syracuseStep 1488263 = 2232395) B2232395
theorem B1488299 : Blo 988596 1488299 := bstep (se 1 (by rfl) ⟨1116224, by rfl⟩ : syracuseStep 1488299 = 2232449) B2232449
theorem B1488329 : Blo 988596 1488329 := bstep (se 2 (by rfl) ⟨558123, by rfl⟩ : syracuseStep 1488329 = 1116247) B1116247
theorem B1488443 : Blo 988596 1488443 := bstep (se 1 (by rfl) ⟨1116332, by rfl⟩ : syracuseStep 1488443 = 2232665) B2232665
theorem B1488503 : Blo 988596 1488503 := bstep (se 1 (by rfl) ⟨1116377, by rfl⟩ : syracuseStep 1488503 = 2232755) B2232755
theorem B1488527 : Blo 988596 1488527 := bstep (se 1 (by rfl) ⟨1116395, by rfl⟩ : syracuseStep 1488527 = 2232791) B2232791
theorem B1881785 : Blo 988596 1881785 := bstep (se 2 (by rfl) ⟨705669, by rfl⟩ : syracuseStep 1881785 = 1411339) B1411339
theorem B1488569 : Blo 988596 1488569 := bstep (se 2 (by rfl) ⟨558213, by rfl⟩ : syracuseStep 1488569 = 1116427) B1116427
theorem B1488647 : Blo 988596 1488647 := bstep (se 1 (by rfl) ⟨1116485, by rfl⟩ : syracuseStep 1488647 = 2232971) B2232971
theorem B2504459 : Blo 988596 2504459 := bstep (se 1 (by rfl) ⟨1878344, by rfl⟩ : syracuseStep 2504459 = 3756689) B3756689
theorem B1488683 : Blo 988596 1488683 := bstep (se 1 (by rfl) ⟨1116512, by rfl⟩ : syracuseStep 1488683 = 2233025) B2233025
theorem B1488713 : Blo 988596 1488713 := bstep (se 2 (by rfl) ⟨558267, by rfl⟩ : syracuseStep 1488713 = 1116535) B1116535
theorem B1488827 : Blo 988596 1488827 := bstep (se 1 (by rfl) ⟨1116620, by rfl⟩ : syracuseStep 1488827 = 2233241) B2233241
theorem B1488887 : Blo 988596 1488887 := bstep (se 1 (by rfl) ⟨1116665, by rfl⟩ : syracuseStep 1488887 = 2233331) B2233331
theorem B5650661 : Blo 988596 5650661 := bstep (se 4 (by rfl) ⟨529749, by rfl⟩ : syracuseStep 5650661 = 1059499) B1059499
theorem B2505107 : Blo 988596 2505107 := bstep (se 1 (by rfl) ⟨1878830, by rfl⟩ : syracuseStep 2505107 = 3757661) B3757661
theorem B5355929 : Blo 988596 5355929 := bstep (se 2 (by rfl) ⟨2008473, by rfl⟩ : syracuseStep 5355929 = 4016947) B4016947
theorem B5651117 : Blo 988596 5651117 := bstep (se 3 (by rfl) ⟨1059584, by rfl⟩ : syracuseStep 5651117 = 2119169) B2119169
theorem B2505401 : Blo 988596 2505401 := bstep (se 2 (by rfl) ⟨939525, by rfl⟩ : syracuseStep 2505401 = 1879051) B1879051
theorem B10697507 : Blo 988596 10697507 := bstep (se 1 (by rfl) ⟨8023130, by rfl⟩ : syracuseStep 10697507 = 16046261) B16046261
theorem B1882939 : Blo 988596 1882939 := bstep (se 1 (by rfl) ⟨1412204, by rfl⟩ : syracuseStep 1882939 = 2824409) B2824409
theorem B77118371 : Blo 988596 77118371 := bstep (se 1 (by rfl) ⟨57838778, by rfl⟩ : syracuseStep 77118371 = 115677557) B115677557
theorem B1883425 : Blo 988596 1883425 := bstep (se 2 (by rfl) ⟨706284, by rfl⟩ : syracuseStep 1883425 = 1412569) B1412569
theorem B5651801 : Blo 988596 5651801 := bstep (se 2 (by rfl) ⟨2119425, by rfl⟩ : syracuseStep 5651801 = 4238851) B4238851
theorem B2506099 : Blo 988596 2506099 := bstep (se 1 (by rfl) ⟨1879574, by rfl⟩ : syracuseStep 2506099 = 3759149) B3759149
theorem B2506241 : Blo 988596 2506241 := bstep (se 2 (by rfl) ⟨939840, by rfl⟩ : syracuseStep 2506241 = 1879681) B1879681
theorem B2506697 : Blo 988596 2506697 := bstep (se 2 (by rfl) ⟨940011, by rfl⟩ : syracuseStep 2506697 = 1880023) B1880023
theorem B5160971 : Blo 988596 5160971 := bstep (se 1 (by rfl) ⟨3870728, by rfl⟩ : syracuseStep 5160971 = 7741457) B7741457
theorem B9519191 : Blo 988596 9519191 := bstep (se 1 (by rfl) ⟨7139393, by rfl⟩ : syracuseStep 9519191 = 14278787) B14278787
theorem B24461513 : Blo 988596 24461513 := bstep (se 2 (by rfl) ⟨9173067, by rfl⟩ : syracuseStep 24461513 = 18346135) B18346135
theorem B1589519 : Blo 988596 1589519 := bstep (se 1 (by rfl) ⟨1192139, by rfl⟩ : syracuseStep 1589519 = 2384279) B2384279
theorem B5423393 : Blo 988596 5423393 := bstep (se 2 (by rfl) ⟨2033772, by rfl⟩ : syracuseStep 5423393 = 4067545) B4067545
theorem B2507051 : Blo 988596 2507051 := bstep (se 1 (by rfl) ⟨1880288, by rfl⟩ : syracuseStep 2507051 = 3760577) B3760577
theorem B5161475 : Blo 988596 5161475 := bstep (se 1 (by rfl) ⟨3871106, by rfl⟩ : syracuseStep 5161475 = 7742213) B7742213
theorem B2376715 : Blo 988596 2376715 := bstep (se 1 (by rfl) ⟨1782536, by rfl⟩ : syracuseStep 2376715 = 3565073) B3565073
theorem B2376791 : Blo 988596 2376791 := bstep (se 1 (by rfl) ⟨1782593, by rfl⟩ : syracuseStep 2376791 = 3565187) B3565187
theorem B6112343 : Blo 988596 6112343 := bstep (se 1 (by rfl) ⟨4584257, by rfl⟩ : syracuseStep 6112343 = 9168515) B9168515
theorem B2376839 : Blo 988596 2376839 := bstep (se 1 (by rfl) ⟨1782629, by rfl⟩ : syracuseStep 2376839 = 3565259) B3565259
theorem B2114761 : Blo 988596 2114761 := bstep (se 2 (by rfl) ⟨793035, by rfl⟩ : syracuseStep 2114761 = 1586071) B1586071
theorem B3818753 : Blo 988596 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B2508043 : Blo 988596 2508043 := bstep (se 1 (by rfl) ⟨1881032, by rfl⟩ : syracuseStep 2508043 = 3762065) B3762065
theorem B4015507 : Blo 988596 4015507 := bstep (se 1 (by rfl) ⟨3011630, by rfl⟩ : syracuseStep 4015507 = 6023261) B6023261
theorem B4572569 : Blo 988596 4572569 := bstep (se 2 (by rfl) ⟨1714713, by rfl⟩ : syracuseStep 4572569 = 3429427) B3429427
theorem B2508185 : Blo 988596 2508185 := bstep (se 2 (by rfl) ⟨940569, by rfl⟩ : syracuseStep 2508185 = 1881139) B1881139
theorem B7521821 : Blo 988596 7521821 := bstep (se 3 (by rfl) ⟨1410341, by rfl⟩ : syracuseStep 7521821 = 2820683) B2820683
theorem B2901547 : Blo 988596 2901547 := bstep (se 1 (by rfl) ⟨2176160, by rfl⟩ : syracuseStep 2901547 = 4352321) B4352321
theorem B2508347 : Blo 988596 2508347 := bstep (se 1 (by rfl) ⟨1881260, by rfl⟩ : syracuseStep 2508347 = 3762521) B3762521
theorem B6342437 : Blo 988596 6342437 := bstep (se 4 (by rfl) ⟨594603, by rfl⟩ : syracuseStep 6342437 = 1189207) B1189207
theorem B2508691 : Blo 988596 2508691 := bstep (se 1 (by rfl) ⟨1881518, by rfl⟩ : syracuseStep 2508691 = 3763037) B3763037
theorem B2508833 : Blo 988596 2508833 := bstep (se 2 (by rfl) ⟨940812, by rfl⟩ : syracuseStep 2508833 = 1881625) B1881625
theorem B41863877 : Blo 988596 41863877 := bstep (se 4 (by rfl) ⟨3924738, by rfl⟩ : syracuseStep 41863877 = 7849477) B7849477
theorem B5720921 : Blo 988596 5720921 := bstep (se 2 (by rfl) ⟨2145345, by rfl⟩ : syracuseStep 5720921 = 4290691) B4290691
theorem B2509825 : Blo 988596 2509825 := bstep (se 2 (by rfl) ⟨941184, by rfl⟩ : syracuseStep 2509825 = 1882369) B1882369
theorem B2116667 : Blo 988596 2116667 := bstep (se 1 (by rfl) ⟨1587500, by rfl⟩ : syracuseStep 2116667 = 3175001) B3175001
theorem B2117153 : Blo 988596 2117153 := bstep (se 2 (by rfl) ⟨793932, by rfl⟩ : syracuseStep 2117153 = 1587865) B1587865
theorem B2510423 : Blo 988596 2510423 := bstep (se 1 (by rfl) ⟨1882817, by rfl⟩ : syracuseStep 2510423 = 3765635) B3765635
theorem B2510635 : Blo 988596 2510635 := bstep (se 1 (by rfl) ⟨1882976, by rfl⟩ : syracuseStep 2510635 = 3765953) B3765953
theorem B15257393 : Blo 988596 15257393 := bstep (se 2 (by rfl) ⟨5721522, by rfl⟩ : syracuseStep 15257393 = 11443045) B11443045
theorem B2117495 : Blo 988596 2117495 := bstep (se 1 (by rfl) ⟨1588121, by rfl⟩ : syracuseStep 2117495 = 3176243) B3176243
theorem B27152279 : Blo 988596 27152279 := bstep (se 1 (by rfl) ⟨20364209, by rfl⟩ : syracuseStep 27152279 = 40728419) B40728419
theorem B3755929 : Blo 988596 3755929 := bstep (se 2 (by rfl) ⟨1408473, by rfl⟩ : syracuseStep 3755929 = 2816947) B2816947
theorem B2510777 : Blo 988596 2510777 := bstep (se 2 (by rfl) ⟨941541, by rfl⟩ : syracuseStep 2510777 = 1883083) B1883083
theorem B3756233 : Blo 988596 3756233 := bstep (se 2 (by rfl) ⟨1408587, by rfl⟩ : syracuseStep 3756233 = 2817175) B2817175
theorem B2937149 : Blo 988596 2937149 := bstep (se 3 (by rfl) ⟨550715, by rfl⟩ : syracuseStep 2937149 = 1101431) B1101431
theorem B4280843 : Blo 988596 4280843 := bstep (se 1 (by rfl) ⟨3210632, by rfl⟩ : syracuseStep 4280843 = 6421265) B6421265
theorem B2380375 : Blo 988596 2380375 := bstep (se 1 (by rfl) ⟨1785281, by rfl⟩ : syracuseStep 2380375 = 3570563) B3570563
theorem B2511769 : Blo 988596 2511769 := bstep (se 2 (by rfl) ⟨941913, by rfl⟩ : syracuseStep 2511769 = 1883827) B1883827
theorem B2511931 : Blo 988596 2511931 := bstep (se 1 (by rfl) ⟨1883948, by rfl⟩ : syracuseStep 2511931 = 3767897) B3767897
theorem B3757175 : Blo 988596 3757175 := bstep (se 1 (by rfl) ⟨2817881, by rfl⟩ : syracuseStep 3757175 = 5635763) B5635763
theorem B2512073 : Blo 988596 2512073 := bstep (se 2 (by rfl) ⟨942027, by rfl⟩ : syracuseStep 2512073 = 1884055) B1884055
theorem B5231873 : Blo 988596 5231873 := bstep (se 2 (by rfl) ⟨1961952, by rfl⟩ : syracuseStep 5231873 = 3923905) B3923905
theorem B5100833 : Blo 988596 5100833 := bstep (se 2 (by rfl) ⟨1912812, by rfl⟩ : syracuseStep 5100833 = 3825625) B3825625
theorem B7132475 : Blo 988596 7132475 := bstep (se 1 (by rfl) ⟨5349356, by rfl⟩ : syracuseStep 7132475 = 10698713) B10698713
theorem B5363003 : Blo 988596 5363003 := bstep (se 1 (by rfl) ⟨4022252, by rfl⟩ : syracuseStep 5363003 = 8044505) B8044505
theorem B2676235 : Blo 988596 2676235 := bstep (se 1 (by rfl) ⟨2007176, by rfl⟩ : syracuseStep 2676235 = 4014353) B4014353
theorem B2512417 : Blo 988596 2512417 := bstep (se 2 (by rfl) ⟨942156, by rfl⟩ : syracuseStep 2512417 = 1884313) B1884313
theorem B5363243 : Blo 988596 5363243 := bstep (se 1 (by rfl) ⟨4022432, by rfl⟩ : syracuseStep 5363243 = 8044865) B8044865
theorem B8017679 : Blo 988596 8017679 := bstep (se 1 (by rfl) ⟨6013259, by rfl⟩ : syracuseStep 8017679 = 12026519) B12026519
theorem B7526195 : Blo 988596 7526195 := bstep (se 1 (by rfl) ⟨5644646, by rfl⟩ : syracuseStep 7526195 = 11289293) B11289293
theorem B2676539 : Blo 988596 2676539 := bstep (se 1 (by rfl) ⟨2007404, by rfl⟩ : syracuseStep 2676539 = 4014809) B4014809
theorem B6019001 : Blo 988596 6019001 := bstep (se 2 (by rfl) ⟨2257125, by rfl⟩ : syracuseStep 6019001 = 4514251) B4514251
theorem B6772747 : Blo 988596 6772747 := bstep (se 1 (by rfl) ⟨5079560, by rfl⟩ : syracuseStep 6772747 = 10159121) B10159121
theorem B3758147 : Blo 988596 3758147 := bstep (se 1 (by rfl) ⟨2818610, by rfl⟩ : syracuseStep 3758147 = 5637221) B5637221
theorem B6347153 : Blo 988596 6347153 := bstep (se 2 (by rfl) ⟨2380182, by rfl⟩ : syracuseStep 6347153 = 4760365) B4760365
theorem B12704147 : Blo 988596 12704147 := bstep (se 1 (by rfl) ⟨9528110, by rfl⟩ : syracuseStep 12704147 = 19056221) B19056221
theorem B2382635 : Blo 988596 2382635 := bstep (se 1 (by rfl) ⟨1786976, by rfl⟩ : syracuseStep 2382635 = 3573953) B3573953
theorem B4512829 : Blo 988596 4512829 := bstep (se 3 (by rfl) ⟨846155, by rfl⟩ : syracuseStep 4512829 = 1692311) B1692311
theorem B3759817 : Blo 988596 3759817 := bstep (se 2 (by rfl) ⟨1409931, by rfl⟩ : syracuseStep 3759817 = 2819863) B2819863
theorem B11460325 : Blo 988596 11460325 := bstep (se 4 (by rfl) ⟨1074405, by rfl⟩ : syracuseStep 11460325 = 2148811) B2148811
theorem B2678615 : Blo 988596 2678615 := bstep (se 1 (by rfl) ⟨2008961, by rfl⟩ : syracuseStep 2678615 = 4017923) B4017923
theorem B19062985 : Blo 988596 19062985 := bstep (se 2 (by rfl) ⟨7148619, by rfl⟩ : syracuseStep 19062985 = 14297239) B14297239
theorem B7135937 : Blo 988596 7135937 := bstep (se 2 (by rfl) ⟨2675976, by rfl⟩ : syracuseStep 7135937 = 5351953) B5351953
theorem B3007261 : Blo 988596 3007261 := bstep (se 3 (by rfl) ⟨563861, by rfl⟩ : syracuseStep 3007261 = 1127723) B1127723
theorem B12673907 : Blo 988596 12673907 := bstep (se 1 (by rfl) ⟨9505430, by rfl⟩ : syracuseStep 12673907 = 19010861) B19010861
theorem B4023175 : Blo 988596 4023175 := bstep (se 1 (by rfl) ⟨3017381, by rfl⟩ : syracuseStep 4023175 = 6034763) B6034763
theorem B40592771 : Blo 988596 40592771 := bstep (se 1 (by rfl) ⟨30444578, by rfl⟩ : syracuseStep 40592771 = 60889157) B60889157
theorem B3007945 : Blo 988596 3007945 := bstep (se 2 (by rfl) ⟨1127979, by rfl⟩ : syracuseStep 3007945 = 2255959) B2255959
theorem B34334387 : Blo 988596 34334387 := bstep (se 1 (by rfl) ⟨25750790, by rfl⟩ : syracuseStep 34334387 = 51501581) B51501581
theorem B3762035 : Blo 988596 3762035 := bstep (se 1 (by rfl) ⟨2821526, by rfl⟩ : syracuseStep 3762035 = 5643053) B5643053
theorem B1337231 : Blo 988596 1337231 := bstep (se 1 (by rfl) ⟨1002923, by rfl⟩ : syracuseStep 1337231 = 2005847) B2005847
theorem B5007257 : Blo 988596 5007257 := bstep (se 2 (by rfl) ⟨1877721, by rfl⟩ : syracuseStep 5007257 = 3755443) B3755443
theorem B3337145 : Blo 988596 3337145 := bstep (se 2 (by rfl) ⟨1251429, by rfl⟩ : syracuseStep 3337145 = 2502859) B2502859
theorem B2714941 : Blo 988596 2714941 := bstep (se 3 (by rfl) ⟨509051, by rfl⟩ : syracuseStep 2714941 = 1018103) B1018103
theorem B97643981 : Blo 988596 97643981 := bstep (se 3 (by rfl) ⟨18308246, by rfl⟩ : syracuseStep 97643981 = 36616493) B36616493
theorem B5434883 : Blo 988596 5434883 := bstep (se 1 (by rfl) ⟨4076162, by rfl⟩ : syracuseStep 5434883 = 8152325) B8152325
theorem B3337739 : Blo 988596 3337739 := bstep (se 1 (by rfl) ⟨2503304, by rfl⟩ : syracuseStep 3337739 = 5006609) B5006609
theorem B3173975 : Blo 988596 3173975 := bstep (se 1 (by rfl) ⟨2380481, by rfl⟩ : syracuseStep 3173975 = 4760963) B4760963
theorem B3337847 : Blo 988596 3337847 := bstep (se 1 (by rfl) ⟨2503385, by rfl⟩ : syracuseStep 3337847 = 5006771) B5006771
theorem B5631889 : Blo 988596 5631889 := bstep (se 2 (by rfl) ⟨2111958, by rfl⟩ : syracuseStep 5631889 = 4223917) B4223917
theorem B2682809 : Blo 988596 2682809 := bstep (se 2 (by rfl) ⟨1006053, by rfl⟩ : syracuseStep 2682809 = 2012107) B2012107
theorem B3764177 : Blo 988596 3764177 := bstep (se 2 (by rfl) ⟨1411566, by rfl⟩ : syracuseStep 3764177 = 2823133) B2823133
theorem B3338441 : Blo 988596 3338441 := bstep (se 2 (by rfl) ⟨1251915, by rfl⟩ : syracuseStep 3338441 = 2503831) B2503831
theorem B84537589 : Blo 988596 84537589 := bstep (se 5 (by rfl) ⟨3962699, by rfl⟩ : syracuseStep 84537589 = 7925399) B7925399
theorem B3764495 : Blo 988596 3764495 := bstep (se 1 (by rfl) ⟨2823371, by rfl⟩ : syracuseStep 3764495 = 5646743) B5646743
theorem B5009849 : Blo 988596 5009849 := bstep (se 2 (by rfl) ⟨1878693, by rfl⟩ : syracuseStep 5009849 = 3757387) B3757387
theorem B2224655 : Blo 988596 2224655 := bstep (se 1 (by rfl) ⟨1668491, by rfl⟩ : syracuseStep 2224655 = 3336983) B3336983
theorem B2224673 : Blo 988596 2224673 := bstep (se 2 (by rfl) ⟨834252, by rfl⟩ : syracuseStep 2224673 = 1668505) B1668505
theorem B12677903 : Blo 988596 12677903 := bstep (se 1 (by rfl) ⟨9508427, by rfl⟩ : syracuseStep 12677903 = 19016855) B19016855
theorem B7140145 : Blo 988596 7140145 := bstep (se 2 (by rfl) ⟨2677554, by rfl⟩ : syracuseStep 7140145 = 5355109) B5355109
theorem B2225015 : Blo 988596 2225015 := bstep (se 1 (by rfl) ⟨1668761, by rfl⟩ : syracuseStep 2225015 = 3337523) B3337523
theorem B3339143 : Blo 988596 3339143 := bstep (se 1 (by rfl) ⟨2504357, by rfl⟩ : syracuseStep 3339143 = 5008715) B5008715
theorem B1340345 : Blo 988596 1340345 := bstep (se 2 (by rfl) ⟨502629, by rfl⟩ : syracuseStep 1340345 = 1005259) B1005259
theorem B2716687 : Blo 988596 2716687 := bstep (se 1 (by rfl) ⟨2037515, by rfl⟩ : syracuseStep 2716687 = 4075031) B4075031
theorem B2225195 : Blo 988596 2225195 := bstep (se 1 (by rfl) ⟨1668896, by rfl⟩ : syracuseStep 2225195 = 3337793) B3337793
theorem B3568877 : Blo 988596 3568877 := bstep (se 3 (by rfl) ⟨669164, by rfl⟩ : syracuseStep 3568877 = 1338329) B1338329
theorem B3339521 : Blo 988596 3339521 := bstep (se 2 (by rfl) ⟨1252320, by rfl⟩ : syracuseStep 3339521 = 2504641) B2504641
theorem B2225555 : Blo 988596 2225555 := bstep (se 1 (by rfl) ⟨1669166, by rfl⟩ : syracuseStep 2225555 = 3338333) B3338333
theorem B7533971 : Blo 988596 7533971 := bstep (se 1 (by rfl) ⟨5650478, by rfl⟩ : syracuseStep 7533971 = 11300957) B11300957
theorem B2225609 : Blo 988596 2225609 := bstep (se 2 (by rfl) ⟨834603, by rfl⟩ : syracuseStep 2225609 = 1669207) B1669207
theorem B2815489 : Blo 988596 2815489 := bstep (se 2 (by rfl) ⟨1055808, by rfl⟩ : syracuseStep 2815489 = 2111617) B2111617
theorem B1668667 : Blo 988596 1668667 := bstep (se 1 (by rfl) ⟨1251500, by rfl⟩ : syracuseStep 1668667 = 2503001) B2503001
theorem B8451661 : Blo 988596 8451661 := bstep (se 3 (by rfl) ⟨1584686, by rfl⟩ : syracuseStep 8451661 = 3169373) B3169373
theorem B1668809 : Blo 988596 1668809 := bstep (se 2 (by rfl) ⟨625803, by rfl⟩ : syracuseStep 1668809 = 1251607) B1251607
theorem B5011145 : Blo 988596 5011145 := bstep (se 2 (by rfl) ⟨1879179, by rfl⟩ : syracuseStep 5011145 = 3758359) B3758359
theorem B3569467 : Blo 988596 3569467 := bstep (se 1 (by rfl) ⟨2677100, by rfl⟩ : syracuseStep 3569467 = 5354201) B5354201
theorem B2291657 : Blo 988596 2291657 := bstep (se 2 (by rfl) ⟨859371, by rfl⟩ : syracuseStep 2291657 = 1718743) B1718743
theorem B3340331 : Blo 988596 3340331 := bstep (se 1 (by rfl) ⟨2505248, by rfl⟩ : syracuseStep 3340331 = 5010497) B5010497
theorem B2816059 : Blo 988596 2816059 := bstep (se 1 (by rfl) ⟨2112044, by rfl⟩ : syracuseStep 2816059 = 4224089) B4224089
theorem B2226311 : Blo 988596 2226311 := bstep (se 1 (by rfl) ⟨1669733, by rfl⟩ : syracuseStep 2226311 = 3339467) B3339467
theorem B1112251 : Blo 988596 1112251 := bstep (se 1 (by rfl) ⟨834188, by rfl⟩ : syracuseStep 1112251 = 1668377) B1668377
theorem B5634305 : Blo 988596 5634305 := bstep (se 2 (by rfl) ⟨2112864, by rfl⟩ : syracuseStep 5634305 = 4225729) B4225729
theorem B2226491 : Blo 988596 2226491 := bstep (se 1 (by rfl) ⟨1669868, by rfl⟩ : syracuseStep 2226491 = 3339737) B3339737
theorem B2718011 : Blo 988596 2718011 := bstep (se 1 (by rfl) ⟨2038508, by rfl⟩ : syracuseStep 2718011 = 4077017) B4077017
theorem B1669511 : Blo 988596 1669511 := bstep (se 1 (by rfl) ⟨1252133, by rfl⟩ : syracuseStep 1669511 = 2504267) B2504267
theorem B3176857 : Blo 988596 3176857 := bstep (se 2 (by rfl) ⟨1191321, by rfl⟩ : syracuseStep 3176857 = 2382643) B2382643
theorem B2226617 : Blo 988596 2226617 := bstep (se 2 (by rfl) ⟨834981, by rfl⟩ : syracuseStep 2226617 = 1669963) B1669963
theorem B15464945 : Blo 988596 15464945 := bstep (se 2 (by rfl) ⟨5799354, by rfl⟩ : syracuseStep 15464945 = 11598709) B11598709
theorem B7240195 : Blo 988596 7240195 := bstep (se 1 (by rfl) ⟨5430146, by rfl⟩ : syracuseStep 7240195 = 10860293) B10860293
theorem B3570263 : Blo 988596 3570263 := bstep (se 1 (by rfl) ⟨2677697, by rfl⟩ : syracuseStep 3570263 = 5355395) B5355395
theorem B1407631 : Blo 988596 1407631 := bstep (se 1 (by rfl) ⟨1055723, by rfl⟩ : syracuseStep 1407631 = 2111447) B2111447
theorem B1112719 : Blo 988596 1112719 := bstep (se 1 (by rfl) ⟨834539, by rfl⟩ : syracuseStep 1112719 = 1669079) B1669079
theorem B2226959 : Blo 988596 2226959 := bstep (se 1 (by rfl) ⟨1670219, by rfl⟩ : syracuseStep 2226959 = 3340439) B3340439
theorem B2226977 : Blo 988596 2226977 := bstep (se 2 (by rfl) ⟨835116, by rfl⟩ : syracuseStep 2226977 = 1670233) B1670233
theorem B1670159 : Blo 988596 1670159 := bstep (se 1 (by rfl) ⟨1252619, by rfl⟩ : syracuseStep 1670159 = 2505239) B2505239
theorem B2227319 : Blo 988596 2227319 := bstep (se 1 (by rfl) ⟨1670489, by rfl⟩ : syracuseStep 2227319 = 3340979) B3340979
theorem B1113223 : Blo 988596 1113223 := bstep (se 1 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 1113223 = 1669835) B1669835
theorem B2227499 : Blo 988596 2227499 := bstep (se 1 (by rfl) ⟨1670624, by rfl⟩ : syracuseStep 2227499 = 3341249) B3341249
theorem B4226363 : Blo 988596 4226363 := bstep (se 1 (by rfl) ⟨3169772, by rfl⟩ : syracuseStep 4226363 = 6339545) B6339545
theorem B1113403 : Blo 988596 1113403 := bstep (se 1 (by rfl) ⟨835052, by rfl⟩ : syracuseStep 1113403 = 1670105) B1670105
theorem B3341627 : Blo 988596 3341627 := bstep (se 1 (by rfl) ⟨2506220, by rfl⟩ : syracuseStep 3341627 = 5012441) B5012441
theorem B1408519 : Blo 988596 1408519 := bstep (se 1 (by rfl) ⟨1056389, by rfl⟩ : syracuseStep 1408519 = 2112779) B2112779
theorem B1670699 : Blo 988596 1670699 := bstep (se 1 (by rfl) ⟨1253024, by rfl⟩ : syracuseStep 1670699 = 2506049) B2506049
theorem B2227859 : Blo 988596 2227859 := bstep (se 1 (by rfl) ⟨1670894, by rfl⟩ : syracuseStep 2227859 = 3341789) B3341789
theorem B9043649 : Blo 988596 9043649 := bstep (se 2 (by rfl) ⟨3391368, by rfl⟩ : syracuseStep 9043649 = 6782737) B6782737
theorem B2227913 : Blo 988596 2227913 := bstep (se 2 (by rfl) ⟨835467, by rfl⟩ : syracuseStep 2227913 = 1670935) B1670935
theorem B3768065 : Blo 988596 3768065 := bstep (se 2 (by rfl) ⟨1413024, by rfl⟩ : syracuseStep 3768065 = 2826049) B2826049
theorem B1113871 : Blo 988596 1113871 := bstep (se 1 (by rfl) ⟨835403, by rfl⟩ : syracuseStep 1113871 = 1670807) B1670807
theorem B3768079 : Blo 988596 3768079 := bstep (se 1 (by rfl) ⟨2826059, by rfl⟩ : syracuseStep 3768079 = 5652119) B5652119
theorem B3342113 : Blo 988596 3342113 := bstep (se 2 (by rfl) ⟨1253292, by rfl⟩ : syracuseStep 3342113 = 2506585) B2506585
theorem B1671097 : Blo 988596 1671097 := bstep (se 2 (by rfl) ⟨626661, by rfl⟩ : syracuseStep 1671097 = 1253323) B1253323
theorem B1409015 : Blo 988596 1409015 := bstep (se 1 (by rfl) ⟨1056761, by rfl⟩ : syracuseStep 1409015 = 2113523) B2113523
theorem B3440647 : Blo 988596 3440647 := bstep (se 1 (by rfl) ⟨2580485, by rfl⟩ : syracuseStep 3440647 = 5160971) B5160971
theorem B27131921 : Blo 988596 27131921 := bstep (se 2 (by rfl) ⟨10174470, by rfl⟩ : syracuseStep 27131921 = 20348941) B20348941
theorem B1671367 : Blo 988596 1671367 := bstep (se 1 (by rfl) ⟨1253525, by rfl⟩ : syracuseStep 1671367 = 2507051) B2507051
theorem B2228471 : Blo 988596 2228471 := bstep (se 1 (by rfl) ⟨1671353, by rfl⟩ : syracuseStep 2228471 = 3342707) B3342707
theorem B3342653 : Blo 988596 3342653 := bstep (se 3 (by rfl) ⟨626747, by rfl⟩ : syracuseStep 3342653 = 1253495) B1253495
theorem B3440983 : Blo 988596 3440983 := bstep (se 1 (by rfl) ⟨2580737, by rfl⟩ : syracuseStep 3440983 = 5161475) B5161475
theorem B1671529 : Blo 988596 1671529 := bstep (se 2 (by rfl) ⟨626823, by rfl⟩ : syracuseStep 1671529 = 1253647) B1253647
theorem B4063769 : Blo 988596 4063769 := bstep (se 2 (by rfl) ⟨1523913, by rfl⟩ : syracuseStep 4063769 = 3047827) B3047827
theorem B1114663 : Blo 988596 1114663 := bstep (se 1 (by rfl) ⟨835997, by rfl⟩ : syracuseStep 1114663 = 1671995) B1671995
theorem B2818759 : Blo 988596 2818759 := bstep (se 1 (by rfl) ⟨2114069, by rfl⟩ : syracuseStep 2818759 = 4228139) B4228139
theorem B2229065 : Blo 988596 2229065 := bstep (se 2 (by rfl) ⟨835899, by rfl⟩ : syracuseStep 2229065 = 1671799) B1671799
theorem B1672123 : Blo 988596 1672123 := bstep (se 1 (by rfl) ⟨1254092, by rfl⟩ : syracuseStep 1672123 = 2508185) B2508185
theorem B5014547 : Blo 988596 5014547 := bstep (se 1 (by rfl) ⟨3760910, by rfl⟩ : syracuseStep 5014547 = 7521821) B7521821
theorem B1672231 : Blo 988596 1672231 := bstep (se 1 (by rfl) ⟨1254173, by rfl⟩ : syracuseStep 1672231 = 2508347) B2508347
theorem B3343517 : Blo 988596 3343517 := bstep (se 3 (by rfl) ⟨626909, by rfl⟩ : syracuseStep 3343517 = 1253819) B1253819
theorem B4228291 : Blo 988596 4228291 := bstep (se 1 (by rfl) ⟨3171218, by rfl⟩ : syracuseStep 4228291 = 6342437) B6342437
theorem B1672555 : Blo 988596 1672555 := bstep (se 1 (by rfl) ⟨1254416, by rfl⟩ : syracuseStep 1672555 = 2508833) B2508833
theorem B2819681 : Blo 988596 2819681 := bstep (se 2 (by rfl) ⟨1057380, by rfl⟩ : syracuseStep 2819681 = 2114761) B2114761
theorem B2229857 : Blo 988596 2229857 := bstep (se 2 (by rfl) ⟨836196, by rfl⟩ : syracuseStep 2229857 = 1672393) B1672393
theorem B3344057 : Blo 988596 3344057 := bstep (se 2 (by rfl) ⟨1254021, by rfl⟩ : syracuseStep 3344057 = 2508043) B2508043
theorem B2230199 : Blo 988596 2230199 := bstep (se 1 (by rfl) ⟨1672649, by rfl⟩ : syracuseStep 2230199 = 3345299) B3345299
theorem B1411111 : Blo 988596 1411111 := bstep (se 1 (by rfl) ⟨1058333, by rfl⟩ : syracuseStep 1411111 = 2116667) B2116667
theorem B3868729 : Blo 988596 3868729 := bstep (se 2 (by rfl) ⟨1450773, by rfl⟩ : syracuseStep 3868729 = 2901547) B2901547
theorem B1116283 : Blo 988596 1116283 := bstep (se 1 (by rfl) ⟨837212, by rfl⟩ : syracuseStep 1116283 = 1674425) B1674425
theorem B3344651 : Blo 988596 3344651 := bstep (se 1 (by rfl) ⟨2508488, by rfl⟩ : syracuseStep 3344651 = 5016977) B5016977
theorem B1902943 : Blo 988596 1902943 := bstep (se 1 (by rfl) ⟨1427207, by rfl⟩ : syracuseStep 1902943 = 2854415) B2854415
theorem B1411435 : Blo 988596 1411435 := bstep (se 1 (by rfl) ⟨1058576, by rfl⟩ : syracuseStep 1411435 = 2117153) B2117153
theorem B1673615 : Blo 988596 1673615 := bstep (se 1 (by rfl) ⟨1255211, by rfl⟩ : syracuseStep 1673615 = 2510423) B2510423
theorem B54200755 : Blo 988596 54200755 := bstep (se 1 (by rfl) ⟨40650566, by rfl⟩ : syracuseStep 54200755 = 81301133) B81301133
theorem B3574253 : Blo 988596 3574253 := bstep (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) B1340345
theorem B2230793 : Blo 988596 2230793 := bstep (se 2 (by rfl) ⟨836547, by rfl⟩ : syracuseStep 2230793 = 1673095) B1673095
theorem B3344921 : Blo 988596 3344921 := bstep (se 2 (by rfl) ⟨1254345, by rfl⟩ : syracuseStep 3344921 = 2508691) B2508691
theorem B1411663 : Blo 988596 1411663 := bstep (se 1 (by rfl) ⟨1058747, by rfl⟩ : syracuseStep 1411663 = 2117495) B2117495
theorem B1673851 : Blo 988596 1673851 := bstep (se 1 (by rfl) ⟨1255388, by rfl⟩ : syracuseStep 1673851 = 2510777) B2510777
theorem B2231135 : Blo 988596 2231135 := bstep (se 1 (by rfl) ⟨1673351, by rfl⟩ : syracuseStep 2231135 = 3346703) B3346703
theorem B6097771 : Blo 988596 6097771 := bstep (se 1 (by rfl) ⟨4573328, by rfl⟩ : syracuseStep 6097771 = 9146657) B9146657
theorem B72354707 : Blo 988596 72354707 := bstep (se 1 (by rfl) ⟨54266030, by rfl⟩ : syracuseStep 72354707 = 108532061) B108532061
theorem B2853895 : Blo 988596 2853895 := bstep (se 1 (by rfl) ⟨2140421, by rfl⟩ : syracuseStep 2853895 = 4280843) B4280843
theorem B2821139 : Blo 988596 2821139 := bstep (se 1 (by rfl) ⟨2115854, by rfl⟩ : syracuseStep 2821139 = 4231709) B4231709
theorem B2231315 : Blo 988596 2231315 := bstep (se 1 (by rfl) ⟨1673486, by rfl⟩ : syracuseStep 2231315 = 3346973) B3346973
theorem B2821367 : Blo 988596 2821367 := bstep (se 1 (by rfl) ⟨2116025, by rfl⟩ : syracuseStep 2821367 = 4232051) B4232051
theorem B2231657 : Blo 988596 2231657 := bstep (se 2 (by rfl) ⟨836871, by rfl⟩ : syracuseStep 2231657 = 1673743) B1673743
theorem B2854273 : Blo 988596 2854273 := bstep (se 2 (by rfl) ⟨1070352, by rfl⟩ : syracuseStep 2854273 = 2140705) B2140705
theorem B1674715 : Blo 988596 1674715 := bstep (se 1 (by rfl) ⟨1256036, by rfl⟩ : syracuseStep 1674715 = 2512073) B2512073
theorem B4754983 : Blo 988596 4754983 := bstep (se 1 (by rfl) ⟨3566237, by rfl⟩ : syracuseStep 4754983 = 7132475) B7132475
theorem B3575335 : Blo 988596 3575335 := bstep (se 1 (by rfl) ⟨2681501, by rfl⟩ : syracuseStep 3575335 = 5363003) B5363003
theorem B3346055 : Blo 988596 3346055 := bstep (se 1 (by rfl) ⟨2509541, by rfl⟩ : syracuseStep 3346055 = 5019083) B5019083
theorem B3346109 : Blo 988596 3346109 := bstep (se 3 (by rfl) ⟨627395, by rfl⟩ : syracuseStep 3346109 = 1254791) B1254791
theorem B3575495 : Blo 988596 3575495 := bstep (se 1 (by rfl) ⟨2681621, by rfl⟩ : syracuseStep 3575495 = 5363243) B5363243
theorem B12193517 : Blo 988596 12193517 := bstep (se 3 (by rfl) ⟨2286284, by rfl⟩ : syracuseStep 12193517 = 4572569) B4572569
theorem B5345119 : Blo 988596 5345119 := bstep (se 1 (by rfl) ⟨4008839, by rfl⟩ : syracuseStep 5345119 = 8017679) B8017679
theorem B3346271 : Blo 988596 3346271 := bstep (se 1 (by rfl) ⟨2509703, by rfl⟩ : syracuseStep 3346271 = 5019407) B5019407
theorem B5017463 : Blo 988596 5017463 := bstep (se 1 (by rfl) ⟨3763097, by rfl⟩ : syracuseStep 5017463 = 7526195) B7526195
theorem B2232251 : Blo 988596 2232251 := bstep (se 1 (by rfl) ⟨1674188, by rfl⟩ : syracuseStep 2232251 = 3348377) B3348377
theorem B3346433 : Blo 988596 3346433 := bstep (se 2 (by rfl) ⟨1254912, by rfl⟩ : syracuseStep 3346433 = 2509825) B2509825
theorem B2232377 : Blo 988596 2232377 := bstep (se 2 (by rfl) ⟨837141, by rfl⟩ : syracuseStep 2232377 = 1674283) B1674283
theorem B4231435 : Blo 988596 4231435 := bstep (se 1 (by rfl) ⟨3173576, by rfl⟩ : syracuseStep 4231435 = 6347153) B6347153
theorem B2232719 : Blo 988596 2232719 := bstep (se 1 (by rfl) ⟨1674539, by rfl⟩ : syracuseStep 2232719 = 3349079) B3349079
theorem B2822779 : Blo 988596 2822779 := bstep (se 1 (by rfl) ⟨2117084, by rfl⟩ : syracuseStep 2822779 = 4234169) B4234169
theorem B2233043 : Blo 988596 2233043 := bstep (se 1 (by rfl) ⟨1674782, by rfl⟩ : syracuseStep 2233043 = 3349565) B3349565
theorem B3347243 : Blo 988596 3347243 := bstep (se 1 (by rfl) ⟨2510432, by rfl⟩ : syracuseStep 3347243 = 5020865) B5020865
theorem B2823007 : Blo 988596 2823007 := bstep (se 1 (by rfl) ⟨2117255, by rfl⟩ : syracuseStep 2823007 = 4234511) B4234511
theorem B3347513 : Blo 988596 3347513 := bstep (se 2 (by rfl) ⟨1255317, by rfl⟩ : syracuseStep 3347513 = 2510635) B2510635
theorem B7509185 : Blo 988596 7509185 := bstep (se 2 (by rfl) ⟨2815944, by rfl⟩ : syracuseStep 7509185 = 5631889) B5631889
theorem B30545099 : Blo 988596 30545099 := bstep (se 1 (by rfl) ⟨22908824, by rfl⟩ : syracuseStep 30545099 = 45817649) B45817649
theorem B4068713 : Blo 988596 4068713 := bstep (se 2 (by rfl) ⟨1525767, by rfl⟩ : syracuseStep 4068713 = 3051535) B3051535
theorem B3347837 : Blo 988596 3347837 := bstep (se 3 (by rfl) ⟨627719, by rfl⟩ : syracuseStep 3347837 = 1255439) B1255439
theorem B988615 : Blo 988596 988615 := bstep (se 1 (by rfl) ⟨741461, by rfl⟩ : syracuseStep 988615 = 1482923) B1482923
theorem B988635 : Blo 988596 988635 := bstep (se 1 (by rfl) ⟨741476, by rfl⟩ : syracuseStep 988635 = 1482953) B1482953
theorem B988711 : Blo 988596 988711 := bstep (se 1 (by rfl) ⟨741533, by rfl⟩ : syracuseStep 988711 = 1483067) B1483067
theorem B988751 : Blo 988596 988751 := bstep (se 1 (by rfl) ⟨741563, by rfl⟩ : syracuseStep 988751 = 1483127) B1483127
theorem B988767 : Blo 988596 988767 := bstep (se 1 (by rfl) ⟨741575, by rfl⟩ : syracuseStep 988767 = 1483151) B1483151
theorem B988795 : Blo 988596 988795 := bstep (se 1 (by rfl) ⟨741596, by rfl⟩ : syracuseStep 988795 = 1483193) B1483193
theorem B3348107 : Blo 988596 3348107 := bstep (se 1 (by rfl) ⟨2511080, by rfl⟩ : syracuseStep 3348107 = 5022161) B5022161
theorem B988847 : Blo 988596 988847 := bstep (se 1 (by rfl) ⟨741635, by rfl⟩ : syracuseStep 988847 = 1483271) B1483271
theorem B988871 : Blo 988596 988871 := bstep (se 1 (by rfl) ⟨741653, by rfl⟩ : syracuseStep 988871 = 1483307) B1483307
theorem B988891 : Blo 988596 988891 := bstep (se 1 (by rfl) ⟨741668, by rfl⟩ : syracuseStep 988891 = 1483337) B1483337
theorem B988967 : Blo 988596 988967 := bstep (se 1 (by rfl) ⟨741725, by rfl⟩ : syracuseStep 988967 = 1483451) B1483451
theorem B4757291 : Blo 988596 4757291 := bstep (se 1 (by rfl) ⟨3567968, by rfl⟩ : syracuseStep 4757291 = 7135937) B7135937
theorem B989007 : Blo 988596 989007 := bstep (se 1 (by rfl) ⟨741755, by rfl⟩ : syracuseStep 989007 = 1483511) B1483511
theorem B989023 : Blo 988596 989023 := bstep (se 1 (by rfl) ⟨741767, by rfl⟩ : syracuseStep 989023 = 1483535) B1483535
theorem B989051 : Blo 988596 989051 := bstep (se 1 (by rfl) ⟨741788, by rfl⟩ : syracuseStep 989051 = 1483577) B1483577
theorem B989103 : Blo 988596 989103 := bstep (se 1 (by rfl) ⟨741827, by rfl⟩ : syracuseStep 989103 = 1483655) B1483655
theorem B989127 : Blo 988596 989127 := bstep (se 1 (by rfl) ⟨741845, by rfl⟩ : syracuseStep 989127 = 1483691) B1483691
theorem B989147 : Blo 988596 989147 := bstep (se 1 (by rfl) ⟨741860, by rfl⟩ : syracuseStep 989147 = 1483721) B1483721
theorem B989223 : Blo 988596 989223 := bstep (se 1 (by rfl) ⟨741917, by rfl⟩ : syracuseStep 989223 = 1483835) B1483835
theorem B989263 : Blo 988596 989263 := bstep (se 1 (by rfl) ⟨741947, by rfl⟩ : syracuseStep 989263 = 1483895) B1483895
theorem B989279 : Blo 988596 989279 := bstep (se 1 (by rfl) ⟨741959, by rfl⟩ : syracuseStep 989279 = 1483919) B1483919
theorem B989307 : Blo 988596 989307 := bstep (se 1 (by rfl) ⟨741980, by rfl⟩ : syracuseStep 989307 = 1483961) B1483961
theorem B989359 : Blo 988596 989359 := bstep (se 1 (by rfl) ⟨742019, by rfl⟩ : syracuseStep 989359 = 1484039) B1484039
theorem B989383 : Blo 988596 989383 := bstep (se 1 (by rfl) ⟨742037, by rfl⟩ : syracuseStep 989383 = 1484075) B1484075
theorem B989403 : Blo 988596 989403 := bstep (se 1 (by rfl) ⟨742052, by rfl⟩ : syracuseStep 989403 = 1484105) B1484105
theorem B989479 : Blo 988596 989479 := bstep (se 1 (by rfl) ⟨742109, by rfl⟩ : syracuseStep 989479 = 1484219) B1484219
theorem B989519 : Blo 988596 989519 := bstep (se 1 (by rfl) ⟨742139, by rfl⟩ : syracuseStep 989519 = 1484279) B1484279
theorem B989535 : Blo 988596 989535 := bstep (se 1 (by rfl) ⟨742151, by rfl⟩ : syracuseStep 989535 = 1484303) B1484303
theorem B989563 : Blo 988596 989563 := bstep (se 1 (by rfl) ⟨742172, by rfl⟩ : syracuseStep 989563 = 1484345) B1484345
theorem B2824591 : Blo 988596 2824591 := bstep (se 1 (by rfl) ⟨2118443, by rfl⟩ : syracuseStep 2824591 = 4236887) B4236887
theorem B989615 : Blo 988596 989615 := bstep (se 1 (by rfl) ⟨742211, by rfl⟩ : syracuseStep 989615 = 1484423) B1484423
theorem B989639 : Blo 988596 989639 := bstep (se 1 (by rfl) ⟨742229, by rfl⟩ : syracuseStep 989639 = 1484459) B1484459
theorem B989659 : Blo 988596 989659 := bstep (se 1 (by rfl) ⟨742244, by rfl⟩ : syracuseStep 989659 = 1484489) B1484489
theorem B3349025 : Blo 988596 3349025 := bstep (se 2 (by rfl) ⟨1255884, by rfl⟩ : syracuseStep 3349025 = 2511769) B2511769
theorem B989735 : Blo 988596 989735 := bstep (se 1 (by rfl) ⟨742301, by rfl⟩ : syracuseStep 989735 = 1484603) B1484603
theorem B989775 : Blo 988596 989775 := bstep (se 1 (by rfl) ⟨742331, by rfl⟩ : syracuseStep 989775 = 1484663) B1484663
theorem B989791 : Blo 988596 989791 := bstep (se 1 (by rfl) ⟨742343, by rfl⟩ : syracuseStep 989791 = 1484687) B1484687
theorem B989819 : Blo 988596 989819 := bstep (se 1 (by rfl) ⟨742364, by rfl⟩ : syracuseStep 989819 = 1484729) B1484729
theorem B989871 : Blo 988596 989871 := bstep (se 1 (by rfl) ⟨742403, by rfl⟩ : syracuseStep 989871 = 1484807) B1484807
theorem B989895 : Blo 988596 989895 := bstep (se 1 (by rfl) ⟨742421, by rfl⟩ : syracuseStep 989895 = 1484843) B1484843
theorem B989915 : Blo 988596 989915 := bstep (se 1 (by rfl) ⟨742436, by rfl⟩ : syracuseStep 989915 = 1484873) B1484873
theorem B3349241 : Blo 988596 3349241 := bstep (se 2 (by rfl) ⟨1255965, by rfl⟩ : syracuseStep 3349241 = 2511931) B2511931
theorem B989991 : Blo 988596 989991 := bstep (se 1 (by rfl) ⟨742493, by rfl⟩ : syracuseStep 989991 = 1484987) B1484987
theorem B990031 : Blo 988596 990031 := bstep (se 1 (by rfl) ⟨742523, by rfl⟩ : syracuseStep 990031 = 1485047) B1485047
theorem B990047 : Blo 988596 990047 := bstep (se 1 (by rfl) ⟨742535, by rfl⟩ : syracuseStep 990047 = 1485071) B1485071
theorem B990075 : Blo 988596 990075 := bstep (se 1 (by rfl) ⟨742556, by rfl⟩ : syracuseStep 990075 = 1485113) B1485113
theorem B16063379 : Blo 988596 16063379 := bstep (se 1 (by rfl) ⟨12047534, by rfl⟩ : syracuseStep 16063379 = 24095069) B24095069
theorem B990127 : Blo 988596 990127 := bstep (se 1 (by rfl) ⟨742595, by rfl⟩ : syracuseStep 990127 = 1485191) B1485191
theorem B990151 : Blo 988596 990151 := bstep (se 1 (by rfl) ⟨742613, by rfl⟩ : syracuseStep 990151 = 1485227) B1485227
theorem B990171 : Blo 988596 990171 := bstep (se 1 (by rfl) ⟨742628, by rfl⟩ : syracuseStep 990171 = 1485257) B1485257
theorem B3349511 : Blo 988596 3349511 := bstep (se 1 (by rfl) ⟨2512133, by rfl⟩ : syracuseStep 3349511 = 5024267) B5024267
theorem B990247 : Blo 988596 990247 := bstep (se 1 (by rfl) ⟨742685, by rfl⟩ : syracuseStep 990247 = 1485371) B1485371
theorem B990287 : Blo 988596 990287 := bstep (se 1 (by rfl) ⟨742715, by rfl⟩ : syracuseStep 990287 = 1485431) B1485431
theorem B990303 : Blo 988596 990303 := bstep (se 1 (by rfl) ⟨742727, by rfl⟩ : syracuseStep 990303 = 1485455) B1485455
theorem B3349619 : Blo 988596 3349619 := bstep (se 1 (by rfl) ⟨2512214, by rfl⟩ : syracuseStep 3349619 = 5024429) B5024429
theorem B990331 : Blo 988596 990331 := bstep (se 1 (by rfl) ⟨742748, by rfl⟩ : syracuseStep 990331 = 1485497) B1485497
theorem B990383 : Blo 988596 990383 := bstep (se 1 (by rfl) ⟨742787, by rfl⟩ : syracuseStep 990383 = 1485575) B1485575
theorem B990407 : Blo 988596 990407 := bstep (se 1 (by rfl) ⟨742805, by rfl⟩ : syracuseStep 990407 = 1485611) B1485611
theorem B990427 : Blo 988596 990427 := bstep (se 1 (by rfl) ⟨742820, by rfl⟩ : syracuseStep 990427 = 1485641) B1485641
theorem B990503 : Blo 988596 990503 := bstep (se 1 (by rfl) ⟨742877, by rfl⟩ : syracuseStep 990503 = 1485755) B1485755
theorem B990543 : Blo 988596 990543 := bstep (se 1 (by rfl) ⟨742907, by rfl⟩ : syracuseStep 990543 = 1485815) B1485815
theorem B990559 : Blo 988596 990559 := bstep (se 1 (by rfl) ⟨742919, by rfl⟩ : syracuseStep 990559 = 1485839) B1485839
theorem B990587 : Blo 988596 990587 := bstep (se 1 (by rfl) ⟨742940, by rfl⟩ : syracuseStep 990587 = 1485881) B1485881
theorem B3349889 : Blo 988596 3349889 := bstep (se 2 (by rfl) ⟨1256208, by rfl⟩ : syracuseStep 3349889 = 2512417) B2512417
theorem B990639 : Blo 988596 990639 := bstep (se 1 (by rfl) ⟨742979, by rfl⟩ : syracuseStep 990639 = 1485959) B1485959
theorem B990663 : Blo 988596 990663 := bstep (se 1 (by rfl) ⟨742997, by rfl⟩ : syracuseStep 990663 = 1485995) B1485995
theorem B990683 : Blo 988596 990683 := bstep (se 1 (by rfl) ⟨743012, by rfl⟩ : syracuseStep 990683 = 1486025) B1486025
theorem B1252903 : Blo 988596 1252903 := bstep (se 1 (by rfl) ⟨939677, by rfl⟩ : syracuseStep 1252903 = 1879355) B1879355
theorem B990759 : Blo 988596 990759 := bstep (se 1 (by rfl) ⟨743069, by rfl⟩ : syracuseStep 990759 = 1486139) B1486139
theorem B990799 : Blo 988596 990799 := bstep (se 1 (by rfl) ⟨743099, by rfl⟩ : syracuseStep 990799 = 1486199) B1486199
theorem B990815 : Blo 988596 990815 := bstep (se 1 (by rfl) ⟨743111, by rfl⟩ : syracuseStep 990815 = 1486223) B1486223
theorem B990843 : Blo 988596 990843 := bstep (se 1 (by rfl) ⟨743132, by rfl⟩ : syracuseStep 990843 = 1486265) B1486265
theorem B2825867 : Blo 988596 2825867 := bstep (se 1 (by rfl) ⟨2119400, by rfl⟩ : syracuseStep 2825867 = 4238801) B4238801
theorem B990895 : Blo 988596 990895 := bstep (se 1 (by rfl) ⟨743171, by rfl⟩ : syracuseStep 990895 = 1486343) B1486343
theorem B990919 : Blo 988596 990919 := bstep (se 1 (by rfl) ⟨743189, by rfl⟩ : syracuseStep 990919 = 1486379) B1486379
theorem B990939 : Blo 988596 990939 := bstep (se 1 (by rfl) ⟨743204, by rfl⟩ : syracuseStep 990939 = 1486409) B1486409
theorem B4759289 : Blo 988596 4759289 := bstep (se 2 (by rfl) ⟨1784733, by rfl⟩ : syracuseStep 4759289 = 3569467) B3569467
theorem B991015 : Blo 988596 991015 := bstep (se 1 (by rfl) ⟨743261, by rfl⟩ : syracuseStep 991015 = 1486523) B1486523
theorem B991055 : Blo 988596 991055 := bstep (se 1 (by rfl) ⟨743291, by rfl⟩ : syracuseStep 991055 = 1486583) B1486583
theorem B991071 : Blo 988596 991071 := bstep (se 1 (by rfl) ⟨743303, by rfl⟩ : syracuseStep 991071 = 1486607) B1486607
theorem B1253227 : Blo 988596 1253227 := bstep (se 1 (by rfl) ⟨939920, by rfl⟩ : syracuseStep 1253227 = 1879841) B1879841
theorem B991099 : Blo 988596 991099 := bstep (se 1 (by rfl) ⟨743324, by rfl⟩ : syracuseStep 991099 = 1486649) B1486649
theorem B991151 : Blo 988596 991151 := bstep (se 1 (by rfl) ⟨743363, by rfl⟩ : syracuseStep 991151 = 1486727) B1486727
theorem B991175 : Blo 988596 991175 := bstep (se 1 (by rfl) ⟨743381, by rfl⟩ : syracuseStep 991175 = 1486763) B1486763
theorem B1056731 : Blo 988596 1056731 := bstep (se 1 (by rfl) ⟨792548, by rfl⟩ : syracuseStep 1056731 = 1585097) B1585097
theorem B991195 : Blo 988596 991195 := bstep (se 1 (by rfl) ⟨743396, by rfl⟩ : syracuseStep 991195 = 1486793) B1486793
theorem B7512101 : Blo 988596 7512101 := bstep (se 4 (by rfl) ⟨704259, by rfl⟩ : syracuseStep 7512101 = 1408519) B1408519
theorem B991271 : Blo 988596 991271 := bstep (se 1 (by rfl) ⟨743453, by rfl⟩ : syracuseStep 991271 = 1486907) B1486907
theorem B991311 : Blo 988596 991311 := bstep (se 1 (by rfl) ⟨743483, by rfl⟩ : syracuseStep 991311 = 1486967) B1486967
theorem B991327 : Blo 988596 991327 := bstep (se 1 (by rfl) ⟨743495, by rfl⟩ : syracuseStep 991327 = 1486991) B1486991
theorem B991355 : Blo 988596 991355 := bstep (se 1 (by rfl) ⟨743516, by rfl⟩ : syracuseStep 991355 = 1487033) B1487033
theorem B991407 : Blo 988596 991407 := bstep (se 1 (by rfl) ⟨743555, by rfl⟩ : syracuseStep 991407 = 1487111) B1487111
theorem B991431 : Blo 988596 991431 := bstep (se 1 (by rfl) ⟨743573, by rfl⟩ : syracuseStep 991431 = 1487147) B1487147
theorem B991451 : Blo 988596 991451 := bstep (se 1 (by rfl) ⟨743588, by rfl⟩ : syracuseStep 991451 = 1487177) B1487177
theorem B1483001 : Blo 988596 1483001 := bstep (se 2 (by rfl) ⟨556125, by rfl⟩ : syracuseStep 1483001 = 1112251) B1112251
theorem B991527 : Blo 988596 991527 := bstep (se 1 (by rfl) ⟨743645, by rfl⟩ : syracuseStep 991527 = 1487291) B1487291
theorem B991567 : Blo 988596 991567 := bstep (se 1 (by rfl) ⟨743675, by rfl⟩ : syracuseStep 991567 = 1487351) B1487351
theorem B1483103 : Blo 988596 1483103 := bstep (se 1 (by rfl) ⟨1112327, by rfl⟩ : syracuseStep 1483103 = 2224655) B2224655
theorem B991583 : Blo 988596 991583 := bstep (se 1 (by rfl) ⟨743687, by rfl⟩ : syracuseStep 991583 = 1487375) B1487375
theorem B1483115 : Blo 988596 1483115 := bstep (se 1 (by rfl) ⟨1112336, by rfl⟩ : syracuseStep 1483115 = 2224673) B2224673
theorem B991611 : Blo 988596 991611 := bstep (se 1 (by rfl) ⟨743708, by rfl⟩ : syracuseStep 991611 = 1487417) B1487417
theorem B991663 : Blo 988596 991663 := bstep (se 1 (by rfl) ⟨743747, by rfl⟩ : syracuseStep 991663 = 1487495) B1487495
theorem B991687 : Blo 988596 991687 := bstep (se 1 (by rfl) ⟨743765, by rfl⟩ : syracuseStep 991687 = 1487531) B1487531
theorem B991707 : Blo 988596 991707 := bstep (se 1 (by rfl) ⟨743780, by rfl⟩ : syracuseStep 991707 = 1487561) B1487561
theorem B3809825 : Blo 988596 3809825 := bstep (se 2 (by rfl) ⟨1428684, by rfl⟩ : syracuseStep 3809825 = 2857369) B2857369
theorem B4235809 : Blo 988596 4235809 := bstep (se 2 (by rfl) ⟨1588428, by rfl⟩ : syracuseStep 4235809 = 3176857) B3176857
theorem B991783 : Blo 988596 991783 := bstep (se 1 (by rfl) ⟨743837, by rfl⟩ : syracuseStep 991783 = 1487675) B1487675
theorem B1483343 : Blo 988596 1483343 := bstep (se 1 (by rfl) ⟨1112507, by rfl⟩ : syracuseStep 1483343 = 2225015) B2225015
theorem B991823 : Blo 988596 991823 := bstep (se 1 (by rfl) ⟨743867, by rfl⟩ : syracuseStep 991823 = 1487735) B1487735
theorem B991839 : Blo 988596 991839 := bstep (se 1 (by rfl) ⟨743879, by rfl⟩ : syracuseStep 991839 = 1487759) B1487759
theorem B991867 : Blo 988596 991867 := bstep (se 1 (by rfl) ⟨743900, by rfl⟩ : syracuseStep 991867 = 1487801) B1487801
theorem B991919 : Blo 988596 991919 := bstep (se 1 (by rfl) ⟨743939, by rfl⟩ : syracuseStep 991919 = 1487879) B1487879
theorem B1483463 : Blo 988596 1483463 := bstep (se 1 (by rfl) ⟨1112597, by rfl⟩ : syracuseStep 1483463 = 2225195) B2225195
theorem B991943 : Blo 988596 991943 := bstep (se 1 (by rfl) ⟨743957, by rfl⟩ : syracuseStep 991943 = 1487915) B1487915
theorem B5645011 : Blo 988596 5645011 := bstep (se 1 (by rfl) ⟨4233758, by rfl⟩ : syracuseStep 5645011 = 8467517) B8467517
theorem B3810007 : Blo 988596 3810007 := bstep (se 1 (by rfl) ⟨2857505, by rfl⟩ : syracuseStep 3810007 = 5715011) B5715011
theorem B991963 : Blo 988596 991963 := bstep (se 1 (by rfl) ⟨743972, by rfl⟩ : syracuseStep 991963 = 1487945) B1487945
theorem B992039 : Blo 988596 992039 := bstep (se 1 (by rfl) ⟨744029, by rfl⟩ : syracuseStep 992039 = 1488059) B1488059
theorem B992079 : Blo 988596 992079 := bstep (se 1 (by rfl) ⟨744059, by rfl⟩ : syracuseStep 992079 = 1488119) B1488119
theorem B1188703 : Blo 988596 1188703 := bstep (se 1 (by rfl) ⟨891527, by rfl⟩ : syracuseStep 1188703 = 1783055) B1783055
theorem B992095 : Blo 988596 992095 := bstep (se 1 (by rfl) ⟨744071, by rfl⟩ : syracuseStep 992095 = 1488143) B1488143
theorem B1876841 : Blo 988596 1876841 := bstep (se 2 (by rfl) ⟨703815, by rfl⟩ : syracuseStep 1876841 = 1407631) B1407631
theorem B1483625 : Blo 988596 1483625 := bstep (se 2 (by rfl) ⟨556359, by rfl⟩ : syracuseStep 1483625 = 1112719) B1112719
theorem B992123 : Blo 988596 992123 := bstep (se 1 (by rfl) ⟨744092, by rfl⟩ : syracuseStep 992123 = 1488185) B1488185
theorem B992175 : Blo 988596 992175 := bstep (se 1 (by rfl) ⟨744131, by rfl⟩ : syracuseStep 992175 = 1488263) B1488263
theorem B1483703 : Blo 988596 1483703 := bstep (se 1 (by rfl) ⟨1112777, by rfl⟩ : syracuseStep 1483703 = 2225555) B2225555
theorem B5022647 : Blo 988596 5022647 := bstep (se 1 (by rfl) ⟨3766985, by rfl⟩ : syracuseStep 5022647 = 7533971) B7533971
theorem B992199 : Blo 988596 992199 := bstep (se 1 (by rfl) ⟨744149, by rfl⟩ : syracuseStep 992199 = 1488299) B1488299
theorem B1483739 : Blo 988596 1483739 := bstep (se 1 (by rfl) ⟨1112804, by rfl⟩ : syracuseStep 1483739 = 2225609) B2225609
theorem B992219 : Blo 988596 992219 := bstep (se 1 (by rfl) ⟨744164, by rfl⟩ : syracuseStep 992219 = 1488329) B1488329
theorem B5645285 : Blo 988596 5645285 := bstep (se 4 (by rfl) ⟨529245, by rfl⟩ : syracuseStep 5645285 = 1058491) B1058491
theorem B992295 : Blo 988596 992295 := bstep (se 1 (by rfl) ⟨744221, by rfl⟩ : syracuseStep 992295 = 1488443) B1488443
theorem B992335 : Blo 988596 992335 := bstep (se 1 (by rfl) ⟨744251, by rfl⟩ : syracuseStep 992335 = 1488503) B1488503
theorem B992351 : Blo 988596 992351 := bstep (se 1 (by rfl) ⟨744263, by rfl⟩ : syracuseStep 992351 = 1488527) B1488527
theorem B1254523 : Blo 988596 1254523 := bstep (se 1 (by rfl) ⟨940892, by rfl⟩ : syracuseStep 1254523 = 1881785) B1881785
theorem B992379 : Blo 988596 992379 := bstep (se 1 (by rfl) ⟨744284, by rfl⟩ : syracuseStep 992379 = 1488569) B1488569
theorem B992431 : Blo 988596 992431 := bstep (se 1 (by rfl) ⟨744323, by rfl⟩ : syracuseStep 992431 = 1488647) B1488647
theorem B992455 : Blo 988596 992455 := bstep (se 1 (by rfl) ⟨744341, by rfl⟩ : syracuseStep 992455 = 1488683) B1488683
theorem B992475 : Blo 988596 992475 := bstep (se 1 (by rfl) ⟨744356, by rfl⟩ : syracuseStep 992475 = 1488713) B1488713
theorem B992551 : Blo 988596 992551 := bstep (se 1 (by rfl) ⟨744413, by rfl⟩ : syracuseStep 992551 = 1488827) B1488827
theorem B992591 : Blo 988596 992591 := bstep (se 1 (by rfl) ⟨744443, by rfl⟩ : syracuseStep 992591 = 1488887) B1488887
theorem B1484207 : Blo 988596 1484207 := bstep (se 1 (by rfl) ⟨1113155, by rfl⟩ : syracuseStep 1484207 = 2226311) B2226311
theorem B1484297 : Blo 988596 1484297 := bstep (se 2 (by rfl) ⟨556611, by rfl⟩ : syracuseStep 1484297 = 1113223) B1113223
theorem B1484327 : Blo 988596 1484327 := bstep (se 1 (by rfl) ⟨1113245, by rfl⟩ : syracuseStep 1484327 = 2226491) B2226491
theorem B1812007 : Blo 988596 1812007 := bstep (se 1 (by rfl) ⟨1359005, by rfl⟩ : syracuseStep 1812007 = 2718011) B2718011
theorem B1484411 : Blo 988596 1484411 := bstep (se 1 (by rfl) ⟨1113308, by rfl⟩ : syracuseStep 1484411 = 2226617) B2226617
theorem B5645969 : Blo 988596 5645969 := bstep (se 2 (by rfl) ⟨2117238, by rfl⟩ : syracuseStep 5645969 = 4234477) B4234477
theorem B1484537 : Blo 988596 1484537 := bstep (se 2 (by rfl) ⟨556701, by rfl⟩ : syracuseStep 1484537 = 1113403) B1113403
theorem B1484639 : Blo 988596 1484639 := bstep (se 1 (by rfl) ⟨1113479, by rfl⟩ : syracuseStep 1484639 = 2226959) B2226959
theorem B1484651 : Blo 988596 1484651 := bstep (se 1 (by rfl) ⟨1113488, by rfl⟩ : syracuseStep 1484651 = 2226977) B2226977
theorem B1484879 : Blo 988596 1484879 := bstep (se 1 (by rfl) ⟨1113659, by rfl⟩ : syracuseStep 1484879 = 2227319) B2227319
theorem B1484999 : Blo 988596 1484999 := bstep (se 1 (by rfl) ⟨1113749, by rfl⟩ : syracuseStep 1484999 = 2227499) B2227499
theorem B15280433 : Blo 988596 15280433 := bstep (se 2 (by rfl) ⟨5730162, by rfl⟩ : syracuseStep 15280433 = 11460325) B11460325
theorem B1485161 : Blo 988596 1485161 := bstep (se 2 (by rfl) ⟨556935, by rfl⟩ : syracuseStep 1485161 = 1113871) B1113871
theorem B5024105 : Blo 988596 5024105 := bstep (se 2 (by rfl) ⟨1884039, by rfl⟩ : syracuseStep 5024105 = 3768079) B3768079
theorem B1485239 : Blo 988596 1485239 := bstep (se 1 (by rfl) ⟨1113929, by rfl⟩ : syracuseStep 1485239 = 2227859) B2227859
theorem B1485275 : Blo 988596 1485275 := bstep (se 1 (by rfl) ⟨1113956, by rfl⟩ : syracuseStep 1485275 = 2227913) B2227913
theorem B1059679 : Blo 988596 1059679 := bstep (se 1 (by rfl) ⟨794759, by rfl⟩ : syracuseStep 1059679 = 1589519) B1589519
theorem B1485743 : Blo 988596 1485743 := bstep (se 1 (by rfl) ⟨1114307, by rfl⟩ : syracuseStep 1485743 = 2228615) B2228615
theorem B1878967 : Blo 988596 1878967 := bstep (se 1 (by rfl) ⟨1409225, by rfl⟩ : syracuseStep 1878967 = 2818451) B2818451
theorem B1485833 : Blo 988596 1485833 := bstep (se 2 (by rfl) ⟨557187, by rfl⟩ : syracuseStep 1485833 = 1114375) B1114375
theorem B1485863 : Blo 988596 1485863 := bstep (se 1 (by rfl) ⟨1114397, by rfl⟩ : syracuseStep 1485863 = 2228795) B2228795
theorem B1485947 : Blo 988596 1485947 := bstep (se 1 (by rfl) ⟨1114460, by rfl⟩ : syracuseStep 1485947 = 2228921) B2228921
theorem B1486073 : Blo 988596 1486073 := bstep (se 2 (by rfl) ⟨557277, by rfl⟩ : syracuseStep 1486073 = 1114555) B1114555
theorem B1486175 : Blo 988596 1486175 := bstep (se 1 (by rfl) ⟨1114631, by rfl⟩ : syracuseStep 1486175 = 2229263) B2229263
theorem B1486187 : Blo 988596 1486187 := bstep (se 1 (by rfl) ⟨1114640, by rfl⟩ : syracuseStep 1486187 = 2229281) B2229281
theorem B1584527 : Blo 988596 1584527 := bstep (se 1 (by rfl) ⟨1188395, by rfl⟩ : syracuseStep 1584527 = 2376791) B2376791
theorem B4074895 : Blo 988596 4074895 := bstep (se 1 (by rfl) ⟨3056171, by rfl⟩ : syracuseStep 4074895 = 6112343) B6112343
theorem B14462381 : Blo 988596 14462381 := bstep (se 3 (by rfl) ⟨2711696, by rfl⟩ : syracuseStep 14462381 = 5423393) B5423393
theorem B1584559 : Blo 988596 1584559 := bstep (se 1 (by rfl) ⟨1188419, by rfl⟩ : syracuseStep 1584559 = 2376839) B2376839
theorem B1486415 : Blo 988596 1486415 := bstep (se 1 (by rfl) ⟨1114811, by rfl⟩ : syracuseStep 1486415 = 2229623) B2229623
theorem B1486535 : Blo 988596 1486535 := bstep (se 1 (by rfl) ⟨1114901, by rfl⟩ : syracuseStep 1486535 = 2229803) B2229803
theorem B4009681 : Blo 988596 4009681 := bstep (se 2 (by rfl) ⟨1503630, by rfl⟩ : syracuseStep 4009681 = 3007261) B3007261
theorem B1486697 : Blo 988596 1486697 := bstep (se 2 (by rfl) ⟨557511, by rfl⟩ : syracuseStep 1486697 = 1115023) B1115023
theorem B1486775 : Blo 988596 1486775 := bstep (se 1 (by rfl) ⟨1115081, by rfl⟩ : syracuseStep 1486775 = 2230163) B2230163
theorem B2011063 : Blo 988596 2011063 := bstep (se 1 (by rfl) ⟨1508297, by rfl⟩ : syracuseStep 2011063 = 3016595) B3016595
theorem B1486811 : Blo 988596 1486811 := bstep (se 1 (by rfl) ⟨1115108, by rfl⟩ : syracuseStep 1486811 = 2230217) B2230217
theorem B1880425 : Blo 988596 1880425 := bstep (se 2 (by rfl) ⟨705159, by rfl⟩ : syracuseStep 1880425 = 1410319) B1410319
theorem B1487279 : Blo 988596 1487279 := bstep (se 1 (by rfl) ⟨1115459, by rfl⟩ : syracuseStep 1487279 = 2230919) B2230919
theorem B1487369 : Blo 988596 1487369 := bstep (se 2 (by rfl) ⟨557763, by rfl⟩ : syracuseStep 1487369 = 1115527) B1115527
theorem B5354009 : Blo 988596 5354009 := bstep (se 2 (by rfl) ⟨2007753, by rfl⟩ : syracuseStep 5354009 = 4015507) B4015507
theorem B1487399 : Blo 988596 1487399 := bstep (se 1 (by rfl) ⟨1115549, by rfl⟩ : syracuseStep 1487399 = 2231099) B2231099
theorem B3813947 : Blo 988596 3813947 := bstep (se 1 (by rfl) ⟨2860460, by rfl⟩ : syracuseStep 3813947 = 5720921) B5720921
theorem B4010593 : Blo 988596 4010593 := bstep (se 2 (by rfl) ⟨1503972, by rfl⟩ : syracuseStep 4010593 = 3007945) B3007945
theorem B1487483 : Blo 988596 1487483 := bstep (se 1 (by rfl) ⟨1115612, by rfl⟩ : syracuseStep 1487483 = 2231225) B2231225
theorem B1487609 : Blo 988596 1487609 := bstep (se 2 (by rfl) ⟨557853, by rfl⟩ : syracuseStep 1487609 = 1115707) B1115707
theorem B1487711 : Blo 988596 1487711 := bstep (se 1 (by rfl) ⟨1115783, by rfl⟩ : syracuseStep 1487711 = 2231567) B2231567
theorem B1487723 : Blo 988596 1487723 := bstep (se 1 (by rfl) ⟨1115792, by rfl⟩ : syracuseStep 1487723 = 2231585) B2231585
theorem B1487951 : Blo 988596 1487951 := bstep (se 1 (by rfl) ⟨1115963, by rfl⟩ : syracuseStep 1487951 = 2231927) B2231927
theorem B1488071 : Blo 988596 1488071 := bstep (se 1 (by rfl) ⟨1116053, by rfl⟩ : syracuseStep 1488071 = 2232107) B2232107
theorem B10171595 : Blo 988596 10171595 := bstep (se 1 (by rfl) ⟨7628696, by rfl⟩ : syracuseStep 10171595 = 15257393) B15257393
theorem B1881299 : Blo 988596 1881299 := bstep (se 1 (by rfl) ⟨1410974, by rfl⟩ : syracuseStep 1881299 = 2821949) B2821949
theorem B18101519 : Blo 988596 18101519 := bstep (se 1 (by rfl) ⟨13576139, by rfl⟩ : syracuseStep 18101519 = 27152279) B27152279
theorem B1488233 : Blo 988596 1488233 := bstep (se 2 (by rfl) ⟨558087, by rfl⟩ : syracuseStep 1488233 = 1116175) B1116175
theorem B1488311 : Blo 988596 1488311 := bstep (se 1 (by rfl) ⟨1116233, by rfl⟩ : syracuseStep 1488311 = 2232467) B2232467
theorem B2504155 : Blo 988596 2504155 := bstep (se 1 (by rfl) ⟨1878116, by rfl⟩ : syracuseStep 2504155 = 3756233) B3756233
theorem B1488347 : Blo 988596 1488347 := bstep (se 1 (by rfl) ⟨1116260, by rfl⟩ : syracuseStep 1488347 = 2232521) B2232521
theorem B7517933 : Blo 988596 7517933 := bstep (se 3 (by rfl) ⟨1409612, by rfl⟩ : syracuseStep 7517933 = 2819225) B2819225
theorem B1881929 : Blo 988596 1881929 := bstep (se 2 (by rfl) ⟨705723, by rfl⟩ : syracuseStep 1881929 = 1411447) B1411447
theorem B1488815 : Blo 988596 1488815 := bstep (se 1 (by rfl) ⟨1116611, by rfl⟩ : syracuseStep 1488815 = 2233223) B2233223
theorem B2504783 : Blo 988596 2504783 := bstep (se 1 (by rfl) ⟨1878587, by rfl⟩ : syracuseStep 2504783 = 3757175) B3757175
theorem B3487915 : Blo 988596 3487915 := bstep (se 1 (by rfl) ⟨2615936, by rfl⟩ : syracuseStep 3487915 = 5231873) B5231873
theorem B1784359 : Blo 988596 1784359 := bstep (se 1 (by rfl) ⟨1338269, by rfl⟩ : syracuseStep 1784359 = 2676539) B2676539
theorem B1882703 : Blo 988596 1882703 := bstep (se 1 (by rfl) ⟨1412027, by rfl⟩ : syracuseStep 1882703 = 2824055) B2824055
theorem B4012667 : Blo 988596 4012667 := bstep (se 1 (by rfl) ⟨3009500, by rfl⟩ : syracuseStep 4012667 = 6019001) B6019001
theorem B7518905 : Blo 988596 7518905 := bstep (se 2 (by rfl) ⟨2819589, by rfl⟩ : syracuseStep 7518905 = 5639179) B5639179
theorem B2505431 : Blo 988596 2505431 := bstep (se 1 (by rfl) ⟨1879073, by rfl⟩ : syracuseStep 2505431 = 3758147) B3758147
theorem B8469431 : Blo 988596 8469431 := bstep (se 1 (by rfl) ⟨6352073, by rfl⟩ : syracuseStep 8469431 = 12704147) B12704147
theorem B3619921 : Blo 988596 3619921 := bstep (se 2 (by rfl) ⟨1357470, by rfl⟩ : syracuseStep 3619921 = 2714941) B2714941
theorem B1588423 : Blo 988596 1588423 := bstep (se 1 (by rfl) ⟨1191317, by rfl⟩ : syracuseStep 1588423 = 2382635) B2382635
theorem B12697175 : Blo 988596 12697175 := bstep (se 1 (by rfl) ⟨9522881, by rfl⟩ : syracuseStep 12697175 = 19045763) B19045763
theorem B2113121 : Blo 988596 2113121 := bstep (se 2 (by rfl) ⟨792420, by rfl⟩ : syracuseStep 2113121 = 1584841) B1584841
theorem B7519877 : Blo 988596 7519877 := bstep (se 4 (by rfl) ⟨704988, by rfl⟩ : syracuseStep 7519877 = 1409977) B1409977
theorem B1785743 : Blo 988596 1785743 := bstep (se 1 (by rfl) ⟨1339307, by rfl⟩ : syracuseStep 1785743 = 2678615) B2678615
theorem B5423041 : Blo 988596 5423041 := bstep (se 2 (by rfl) ⟨2033640, by rfl⟩ : syracuseStep 5423041 = 4067281) B4067281
theorem B1884359 : Blo 988596 1884359 := bstep (se 1 (by rfl) ⟨1413269, by rfl⟩ : syracuseStep 1884359 = 2826539) B2826539
theorem B9520193 : Blo 988596 9520193 := bstep (se 2 (by rfl) ⟨3570072, by rfl⟩ : syracuseStep 9520193 = 7140145) B7140145
theorem B22889591 : Blo 988596 22889591 := bstep (se 1 (by rfl) ⟨17167193, by rfl⟩ : syracuseStep 22889591 = 34334387) B34334387
theorem B2508023 : Blo 988596 2508023 := bstep (se 1 (by rfl) ⟨1881017, by rfl⟩ : syracuseStep 2508023 = 3762035) B3762035
theorem B3622249 : Blo 988596 3622249 := bstep (se 2 (by rfl) ⟨1358343, by rfl⟩ : syracuseStep 3622249 = 2716687) B2716687
theorem B2541095 : Blo 988596 2541095 := bstep (se 1 (by rfl) ⟨1905821, by rfl⟩ : syracuseStep 2541095 = 3811643) B3811643
theorem B12699179 : Blo 988596 12699179 := bstep (se 1 (by rfl) ⟨9524384, by rfl⟩ : syracuseStep 12699179 = 19048769) B19048769
theorem B3753985 : Blo 988596 3753985 := bstep (se 2 (by rfl) ⟨1407744, by rfl⟩ : syracuseStep 3753985 = 2815489) B2815489
theorem B7522307 : Blo 988596 7522307 := bstep (se 1 (by rfl) ⟨5641730, by rfl⟩ : syracuseStep 7522307 = 11283461) B11283461
theorem B13551623 : Blo 988596 13551623 := bstep (se 1 (by rfl) ⟨10163717, by rfl⟩ : syracuseStep 13551623 = 20327435) B20327435
theorem B6342745 : Blo 988596 6342745 := bstep (se 2 (by rfl) ⟨2378529, by rfl⟩ : syracuseStep 6342745 = 4757059) B4757059
theorem B65095987 : Blo 988596 65095987 := bstep (se 1 (by rfl) ⟨48821990, by rfl⟩ : syracuseStep 65095987 = 97643981) B97643981
theorem B3623255 : Blo 988596 3623255 := bstep (se 1 (by rfl) ⟨2717441, by rfl⟩ : syracuseStep 3623255 = 5434883) B5434883
theorem B2115983 : Blo 988596 2115983 := bstep (se 1 (by rfl) ⟨1586987, by rfl⟩ : syracuseStep 2115983 = 3173975) B3173975
theorem B1788539 : Blo 988596 1788539 := bstep (se 1 (by rfl) ⟨1341404, by rfl⟩ : syracuseStep 1788539 = 2682809) B2682809
theorem B2509451 : Blo 988596 2509451 := bstep (se 1 (by rfl) ⟨1882088, by rfl⟩ : syracuseStep 2509451 = 3764177) B3764177
theorem B9030329 : Blo 988596 9030329 := bstep (se 2 (by rfl) ⟨3386373, by rfl⟩ : syracuseStep 9030329 = 6772747) B6772747
theorem B3754745 : Blo 988596 3754745 := bstep (se 2 (by rfl) ⟨1408029, by rfl⟩ : syracuseStep 3754745 = 2816059) B2816059
theorem B2509663 : Blo 988596 2509663 := bstep (se 1 (by rfl) ⟨1882247, by rfl⟩ : syracuseStep 2509663 = 3764495) B3764495
theorem B6016079 : Blo 988596 6016079 := bstep (se 1 (by rfl) ⟨4512059, by rfl⟩ : syracuseStep 6016079 = 9024119) B9024119
theorem B9653593 : Blo 988596 9653593 := bstep (se 2 (by rfl) ⟨3620097, by rfl⟩ : syracuseStep 9653593 = 7240195) B7240195
theorem B2674063 : Blo 988596 2674063 := bstep (se 1 (by rfl) ⟨2005547, by rfl⟩ : syracuseStep 2674063 = 4011095) B4011095
theorem B2379251 : Blo 988596 2379251 := bstep (se 1 (by rfl) ⟨1784438, by rfl⟩ : syracuseStep 2379251 = 3568877) B3568877
theorem B2510585 : Blo 988596 2510585 := bstep (se 2 (by rfl) ⟨941469, by rfl⟩ : syracuseStep 2510585 = 1882939) B1882939
theorem B2674505 : Blo 988596 2674505 := bstep (se 2 (by rfl) ⟨1002939, by rfl⟩ : syracuseStep 2674505 = 2005879) B2005879
theorem B6017105 : Blo 988596 6017105 := bstep (se 2 (by rfl) ⟨2256414, by rfl⟩ : syracuseStep 6017105 = 4512829) B4512829
theorem B3756203 : Blo 988596 3756203 := bstep (se 1 (by rfl) ⟨2817152, by rfl⟩ : syracuseStep 3756203 = 5634305) B5634305
theorem B10309963 : Blo 988596 10309963 := bstep (se 1 (by rfl) ⟨7732472, by rfl⟩ : syracuseStep 10309963 = 15464945) B15464945
theorem B7524737 : Blo 988596 7524737 := bstep (se 2 (by rfl) ⟨2821776, by rfl⟩ : syracuseStep 7524737 = 5643553) B5643553
theorem B2511233 : Blo 988596 2511233 := bstep (se 2 (by rfl) ⟨941712, by rfl⟩ : syracuseStep 2511233 = 1883425) B1883425
theorem B2380175 : Blo 988596 2380175 := bstep (se 1 (by rfl) ⟨1785131, by rfl⟩ : syracuseStep 2380175 = 3570263) B3570263
theorem B5362157 : Blo 988596 5362157 := bstep (se 3 (by rfl) ⟨1005404, by rfl⟩ : syracuseStep 5362157 = 2010809) B2010809
theorem B7131671 : Blo 988596 7131671 := bstep (se 1 (by rfl) ⟨5348753, by rfl⟩ : syracuseStep 7131671 = 10697507) B10697507
theorem B2512043 : Blo 988596 2512043 := bstep (se 1 (by rfl) ⟨1884032, by rfl⟩ : syracuseStep 2512043 = 3768065) B3768065
theorem B3757373 : Blo 988596 3757373 := bstep (se 3 (by rfl) ⟨704507, by rfl⟩ : syracuseStep 3757373 = 1409015) B1409015
theorem B6346127 : Blo 988596 6346127 := bstep (se 1 (by rfl) ⟨4759595, by rfl⟩ : syracuseStep 6346127 = 9519191) B9519191
theorem B16307675 : Blo 988596 16307675 := bstep (se 1 (by rfl) ⟨12230756, by rfl⟩ : syracuseStep 16307675 = 24461513) B24461513
theorem B25417313 : Blo 988596 25417313 := bstep (se 2 (by rfl) ⟨9531492, by rfl⟩ : syracuseStep 25417313 = 19062985) B19062985
theorem B3757691 : Blo 988596 3757691 := bstep (se 1 (by rfl) ⟨2818268, by rfl⟩ : syracuseStep 3757691 = 5636537) B5636537
theorem B2119699 : Blo 988596 2119699 := bstep (se 1 (by rfl) ⟨1589774, by rfl⟩ : syracuseStep 2119699 = 3179549) B3179549
theorem B2545835 : Blo 988596 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B3168503 : Blo 988596 3168503 := bstep (se 1 (by rfl) ⟨2376377, by rfl⟩ : syracuseStep 3168503 = 4752755) B4752755
theorem B5364233 : Blo 988596 5364233 := bstep (se 2 (by rfl) ⟨2011587, by rfl⟩ : syracuseStep 5364233 = 4023175) B4023175
theorem B3168953 : Blo 988596 3168953 := bstep (se 2 (by rfl) ⟨1188357, by rfl⟩ : syracuseStep 3168953 = 2376715) B2376715
theorem B3759119 : Blo 988596 3759119 := bstep (se 1 (by rfl) ⟨2819339, by rfl⟩ : syracuseStep 3759119 = 5638679) B5638679
theorem B27909251 : Blo 988596 27909251 := bstep (se 1 (by rfl) ⟨20931938, by rfl⟩ : syracuseStep 27909251 = 41863877) B41863877
theorem B5004989 : Blo 988596 5004989 := bstep (se 3 (by rfl) ⟨938435, by rfl⟩ : syracuseStep 5004989 = 1876871) B1876871
theorem B5005151 : Blo 988596 5005151 := bstep (se 1 (by rfl) ⟨3753863, by rfl⟩ : syracuseStep 5005151 = 7507727) B7507727
theorem B1958099 : Blo 988596 1958099 := bstep (se 1 (by rfl) ⟨1468574, by rfl⟩ : syracuseStep 1958099 = 2937149) B2937149
theorem B8479241 : Blo 988596 8479241 := bstep (se 2 (by rfl) ⟨3179715, by rfl⟩ : syracuseStep 8479241 = 6359431) B6359431
theorem B2417249 : Blo 988596 2417249 := bstep (se 2 (by rfl) ⟨906468, by rfl⟩ : syracuseStep 2417249 = 1812937) B1812937
theorem B3760775 : Blo 988596 3760775 := bstep (se 1 (by rfl) ⟨2820581, by rfl⟩ : syracuseStep 3760775 = 5641163) B5641163
theorem B3170963 : Blo 988596 3170963 := bstep (se 1 (by rfl) ⟨2378222, by rfl⟩ : syracuseStep 3170963 = 4756445) B4756445
theorem B3400555 : Blo 988596 3400555 := bstep (se 1 (by rfl) ⟨2550416, by rfl⟩ : syracuseStep 3400555 = 5100833) B5100833
theorem B3564623 : Blo 988596 3564623 := bstep (se 1 (by rfl) ⟨2673467, by rfl⟩ : syracuseStep 3564623 = 5346935) B5346935
theorem B4023695 : Blo 988596 4023695 := bstep (se 1 (by rfl) ⟨3017771, by rfl⟩ : syracuseStep 4023695 = 6035543) B6035543
theorem B3761761 : Blo 988596 3761761 := bstep (se 2 (by rfl) ⟨1410660, by rfl⟩ : syracuseStep 3761761 = 2821321) B2821321
theorem B1205959 : Blo 988596 1205959 := bstep (se 1 (by rfl) ⟨904469, by rfl⟩ : syracuseStep 1205959 = 1808939) B1808939
theorem B3762233 : Blo 988596 3762233 := bstep (se 2 (by rfl) ⟨1410837, by rfl⟩ : syracuseStep 3762233 = 2821675) B2821675
theorem B62580869 : Blo 988596 62580869 := bstep (se 4 (by rfl) ⟨5866956, by rfl⟩ : syracuseStep 62580869 = 11733913) B11733913
theorem B9529649 : Blo 988596 9529649 := bstep (se 2 (by rfl) ⟨3573618, by rfl⟩ : syracuseStep 9529649 = 7147237) B7147237
theorem B3565949 : Blo 988596 3565949 := bstep (se 3 (by rfl) ⟨668615, by rfl⟩ : syracuseStep 3565949 = 1337231) B1337231
theorem B3336713 : Blo 988596 3336713 := bstep (se 2 (by rfl) ⟨1251267, by rfl⟩ : syracuseStep 3336713 = 2502535) B2502535
theorem B5007905 : Blo 988596 5007905 := bstep (se 2 (by rfl) ⟨1877964, by rfl⟩ : syracuseStep 5007905 = 3755929) B3755929
theorem B3173053 : Blo 988596 3173053 := bstep (se 3 (by rfl) ⟨594947, by rfl⟩ : syracuseStep 3173053 = 1189895) B1189895
theorem B2714327 : Blo 988596 2714327 := bstep (se 1 (by rfl) ⟨2035745, by rfl⟩ : syracuseStep 2714327 = 4071491) B4071491
theorem B112716785 : Blo 988596 112716785 := bstep (se 2 (by rfl) ⟨42268794, by rfl⟩ : syracuseStep 112716785 = 84537589) B84537589
theorem B3763219 : Blo 988596 3763219 := bstep (se 1 (by rfl) ⟨2822414, by rfl⟩ : syracuseStep 3763219 = 5644829) B5644829
theorem B8449271 : Blo 988596 8449271 := bstep (se 1 (by rfl) ⟨6336953, by rfl⟩ : syracuseStep 8449271 = 12673907) B12673907
theorem B3337577 : Blo 988596 3337577 := bstep (se 2 (by rfl) ⟨1251591, by rfl⟩ : syracuseStep 3337577 = 2503183) B2503183
theorem B3173833 : Blo 988596 3173833 := bstep (se 2 (by rfl) ⟨1190187, by rfl⟩ : syracuseStep 3173833 = 2380375) B2380375
theorem B27061847 : Blo 988596 27061847 := bstep (se 1 (by rfl) ⟨20296385, by rfl⟩ : syracuseStep 27061847 = 40592771) B40592771
theorem B14282477 : Blo 988596 14282477 := bstep (se 3 (by rfl) ⟨2677964, by rfl⟩ : syracuseStep 14282477 = 5355929) B5355929
theorem B3338171 : Blo 988596 3338171 := bstep (se 1 (by rfl) ⟨2503628, by rfl⟩ : syracuseStep 3338171 = 5007257) B5007257
theorem B6353153 : Blo 988596 6353153 := bstep (se 2 (by rfl) ⟨2382432, by rfl⟩ : syracuseStep 6353153 = 4764865) B4764865
theorem B2224763 : Blo 988596 2224763 := bstep (se 1 (by rfl) ⟨1668572, by rfl⟩ : syracuseStep 2224763 = 3337145) B3337145
theorem B3568313 : Blo 988596 3568313 := bstep (se 2 (by rfl) ⟨1338117, by rfl⟩ : syracuseStep 3568313 = 2676235) B2676235
theorem B3764951 : Blo 988596 3764951 := bstep (se 1 (by rfl) ⟨2823713, by rfl⟩ : syracuseStep 3764951 = 5647427) B5647427
theorem B2224889 : Blo 988596 2224889 := bstep (se 2 (by rfl) ⟨834333, by rfl⟩ : syracuseStep 2224889 = 1668667) B1668667
theorem B11268881 : Blo 988596 11268881 := bstep (se 2 (by rfl) ⟨4225830, by rfl⟩ : syracuseStep 11268881 = 8451661) B8451661
theorem B1340335 : Blo 988596 1340335 := bstep (se 1 (by rfl) ⟨1005251, by rfl⟩ : syracuseStep 1340335 = 2010503) B2010503
theorem B2225159 : Blo 988596 2225159 := bstep (se 1 (by rfl) ⟨1668869, by rfl⟩ : syracuseStep 2225159 = 3337739) B3337739
theorem B2225231 : Blo 988596 2225231 := bstep (se 1 (by rfl) ⟨1668923, by rfl⟩ : syracuseStep 2225231 = 3337847) B3337847
theorem B1668343 : Blo 988596 1668343 := bstep (se 1 (by rfl) ⟨1251257, by rfl⟩ : syracuseStep 1668343 = 2502515) B2502515
theorem B1668539 : Blo 988596 1668539 := bstep (se 1 (by rfl) ⟨1251404, by rfl⟩ : syracuseStep 1668539 = 2502809) B2502809
theorem B2225627 : Blo 988596 2225627 := bstep (se 1 (by rfl) ⟨1669220, by rfl⟩ : syracuseStep 2225627 = 3338441) B3338441
theorem B1668647 : Blo 988596 1668647 := bstep (se 1 (by rfl) ⟨1251485, by rfl⟩ : syracuseStep 1668647 = 2502971) B2502971
theorem B5010983 : Blo 988596 5010983 := bstep (se 1 (by rfl) ⟨3758237, by rfl⟩ : syracuseStep 5010983 = 7516475) B7516475
theorem B3339899 : Blo 988596 3339899 := bstep (se 1 (by rfl) ⟨2504924, by rfl⟩ : syracuseStep 3339899 = 5009849) B5009849
theorem B3569351 : Blo 988596 3569351 := bstep (se 1 (by rfl) ⟨2677013, by rfl⟩ : syracuseStep 3569351 = 5354027) B5354027
theorem B3340061 : Blo 988596 3340061 := bstep (se 3 (by rfl) ⟨626261, by rfl⟩ : syracuseStep 3340061 = 1252523) B1252523
theorem B1668937 : Blo 988596 1668937 := bstep (se 2 (by rfl) ⟨625851, by rfl⟩ : syracuseStep 1668937 = 1251703) B1251703
theorem B8451935 : Blo 988596 8451935 := bstep (se 1 (by rfl) ⟨6338951, by rfl⟩ : syracuseStep 8451935 = 12677903) B12677903
theorem B1668971 : Blo 988596 1668971 := bstep (se 1 (by rfl) ⟨1251728, by rfl⟩ : syracuseStep 1668971 = 2503457) B2503457
theorem B3766135 : Blo 988596 3766135 := bstep (se 1 (by rfl) ⟨2824601, by rfl⟩ : syracuseStep 3766135 = 5649203) B5649203
theorem B2226095 : Blo 988596 2226095 := bstep (se 1 (by rfl) ⟨1669571, by rfl⟩ : syracuseStep 2226095 = 3339143) B3339143
theorem B2226347 : Blo 988596 2226347 := bstep (se 1 (by rfl) ⟨1669760, by rfl⟩ : syracuseStep 2226347 = 3339521) B3339521
theorem B1669369 : Blo 988596 1669369 := bstep (se 2 (by rfl) ⟨626013, by rfl⟩ : syracuseStep 1669369 = 1252027) B1252027
theorem B9533801 : Blo 988596 9533801 := bstep (se 2 (by rfl) ⟨3575175, by rfl⟩ : syracuseStep 9533801 = 7150351) B7150351
theorem B1112539 : Blo 988596 1112539 := bstep (se 1 (by rfl) ⟨834404, by rfl⟩ : syracuseStep 1112539 = 1668809) B1668809
theorem B3340763 : Blo 988596 3340763 := bstep (se 1 (by rfl) ⟨2505572, by rfl⟩ : syracuseStep 3340763 = 5011145) B5011145
theorem B1669639 : Blo 988596 1669639 := bstep (se 1 (by rfl) ⟨1252229, by rfl⟩ : syracuseStep 1669639 = 2504459) B2504459
theorem B2226887 : Blo 988596 2226887 := bstep (se 1 (by rfl) ⟨1670165, by rfl⟩ : syracuseStep 2226887 = 3340331) B3340331
theorem B3767107 : Blo 988596 3767107 := bstep (se 1 (by rfl) ⟨2825330, by rfl⟩ : syracuseStep 3767107 = 5650661) B5650661
theorem B1113007 : Blo 988596 1113007 := bstep (se 1 (by rfl) ⟨834755, by rfl⟩ : syracuseStep 1113007 = 1669511) B1669511
theorem B1670071 : Blo 988596 1670071 := bstep (se 1 (by rfl) ⟨1252553, by rfl⟩ : syracuseStep 1670071 = 2505107) B2505107
theorem B3767411 : Blo 988596 3767411 := bstep (se 1 (by rfl) ⟨2825558, by rfl⟩ : syracuseStep 3767411 = 5651117) B5651117
theorem B1670267 : Blo 988596 1670267 := bstep (se 1 (by rfl) ⟨1252700, by rfl⟩ : syracuseStep 1670267 = 2505401) B2505401
theorem B3341465 : Blo 988596 3341465 := bstep (se 2 (by rfl) ⟨1253049, by rfl⟩ : syracuseStep 3341465 = 2506099) B2506099
theorem B51412247 : Blo 988596 51412247 := bstep (se 1 (by rfl) ⟨38559185, by rfl⟩ : syracuseStep 51412247 = 77118371) B77118371
theorem B6782297 : Blo 988596 6782297 := bstep (se 2 (by rfl) ⟨2543361, by rfl⟩ : syracuseStep 6782297 = 5086723) B5086723
theorem B1113439 : Blo 988596 1113439 := bstep (se 1 (by rfl) ⟨835079, by rfl⟩ : syracuseStep 1113439 = 1670159) B1670159
theorem B24444341 : Blo 988596 24444341 := bstep (se 5 (by rfl) ⟨1145828, by rfl⟩ : syracuseStep 24444341 = 2291657) B2291657
theorem B1670665 : Blo 988596 1670665 := bstep (se 2 (by rfl) ⟨626499, by rfl⟩ : syracuseStep 1670665 = 1252999) B1252999
theorem B2817575 : Blo 988596 2817575 := bstep (se 1 (by rfl) ⟨2113181, by rfl⟩ : syracuseStep 2817575 = 4226363) B4226363
theorem B2227751 : Blo 988596 2227751 := bstep (se 1 (by rfl) ⟨1670813, by rfl⟩ : syracuseStep 2227751 = 3341627) B3341627
theorem B3767867 : Blo 988596 3767867 := bstep (se 1 (by rfl) ⟨2825900, by rfl⟩ : syracuseStep 3767867 = 5651801) B5651801
theorem B5013089 : Blo 988596 5013089 := bstep (se 2 (by rfl) ⟨1879908, by rfl⟩ : syracuseStep 5013089 = 3759817) B3759817
theorem B1670827 : Blo 988596 1670827 := bstep (se 1 (by rfl) ⟨1253120, by rfl⟩ : syracuseStep 1670827 = 2506241) B2506241
theorem B1113799 : Blo 988596 1113799 := bstep (se 1 (by rfl) ⟨835349, by rfl⟩ : syracuseStep 1113799 = 1670699) B1670699
theorem B6029099 : Blo 988596 6029099 := bstep (se 1 (by rfl) ⟨4521824, by rfl⟩ : syracuseStep 6029099 = 9043649) B9043649
theorem B2228075 : Blo 988596 2228075 := bstep (se 1 (by rfl) ⟨1671056, by rfl⟩ : syracuseStep 2228075 = 3342113) B3342113
theorem B2228129 : Blo 988596 2228129 := bstep (se 2 (by rfl) ⟨835548, by rfl⟩ : syracuseStep 2228129 = 1671097) B1671097
theorem B1671131 : Blo 988596 1671131 := bstep (se 1 (by rfl) ⟨1253348, by rfl⟩ : syracuseStep 1671131 = 2506697) B2506697
theorem B4587529 : Blo 988596 4587529 := bstep (se 2 (by rfl) ⟨1720323, by rfl⟩ : syracuseStep 4587529 = 3440647) B3440647
theorem B18087947 : Blo 988596 18087947 := bstep (se 1 (by rfl) ⟨13565960, by rfl⟩ : syracuseStep 18087947 = 27131921) B27131921
theorem B2228435 : Blo 988596 2228435 := bstep (se 1 (by rfl) ⟨1671326, by rfl⟩ : syracuseStep 2228435 = 3342653) B3342653
theorem B2228489 : Blo 988596 2228489 := bstep (se 2 (by rfl) ⟨835683, by rfl⟩ : syracuseStep 2228489 = 1671367) B1671367
theorem B4587977 : Blo 988596 4587977 := bstep (se 2 (by rfl) ⟨1720491, by rfl⟩ : syracuseStep 4587977 = 3440983) B3440983
theorem B2228705 : Blo 988596 2228705 := bstep (se 2 (by rfl) ⟨835764, by rfl⟩ : syracuseStep 2228705 = 1671529) B1671529
theorem B3343031 : Blo 988596 3343031 := bstep (se 1 (by rfl) ⟨2507273, by rfl⟩ : syracuseStep 3343031 = 5014547) B5014547
theorem B2229011 : Blo 988596 2229011 := bstep (se 1 (by rfl) ⟨1671758, by rfl⟩ : syracuseStep 2229011 = 3343517) B3343517
theorem B1672015 : Blo 988596 1672015 := bstep (se 1 (by rfl) ⟨1254011, by rfl⟩ : syracuseStep 1672015 = 2508023) B2508023
theorem B5080009 : Blo 988596 5080009 := bstep (se 2 (by rfl) ⟨1905003, by rfl⟩ : syracuseStep 5080009 = 3810007) B3810007
theorem B2229371 : Blo 988596 2229371 := bstep (se 1 (by rfl) ⟨1672028, by rfl⟩ : syracuseStep 2229371 = 3344057) B3344057
theorem B2229497 : Blo 988596 2229497 := bstep (se 2 (by rfl) ⟨836061, by rfl⟩ : syracuseStep 2229497 = 1672123) B1672123
theorem B5014871 : Blo 988596 5014871 := bstep (se 1 (by rfl) ⟨3761153, by rfl⟩ : syracuseStep 5014871 = 7522307) B7522307
theorem B2229641 : Blo 988596 2229641 := bstep (se 2 (by rfl) ⟨836115, by rfl⟩ : syracuseStep 2229641 = 1672231) B1672231
theorem B1672697 : Blo 988596 1672697 := bstep (se 2 (by rfl) ⟨627261, by rfl⟩ : syracuseStep 1672697 = 1254523) B1254523
theorem B2229767 : Blo 988596 2229767 := bstep (se 1 (by rfl) ⟨1672325, by rfl⟩ : syracuseStep 2229767 = 3344651) B3344651
theorem B5637721 : Blo 988596 5637721 := bstep (se 2 (by rfl) ⟨2114145, by rfl⟩ : syracuseStep 5637721 = 4228291) B4228291
theorem B1115743 : Blo 988596 1115743 := bstep (se 1 (by rfl) ⟨836807, by rfl⟩ : syracuseStep 1115743 = 1673615) B1673615
theorem B2229947 : Blo 988596 2229947 := bstep (se 1 (by rfl) ⟨1672460, by rfl⟩ : syracuseStep 2229947 = 3344921) B3344921
theorem B1672967 : Blo 988596 1672967 := bstep (se 1 (by rfl) ⟨1254725, by rfl⟩ : syracuseStep 1672967 = 2509451) B2509451
theorem B2230073 : Blo 988596 2230073 := bstep (se 2 (by rfl) ⟨836277, by rfl⟩ : syracuseStep 2230073 = 1672555) B1672555
theorem B48236471 : Blo 988596 48236471 := bstep (se 1 (by rfl) ⟨36177353, by rfl⟩ : syracuseStep 48236471 = 72354707) B72354707
theorem B5015681 : Blo 988596 5015681 := bstep (se 2 (by rfl) ⟨1880880, by rfl⟩ : syracuseStep 5015681 = 3761761) B3761761
theorem B1607945 : Blo 988596 1607945 := bstep (se 2 (by rfl) ⟨602979, by rfl⟩ : syracuseStep 1607945 = 1205959) B1205959
theorem B2230703 : Blo 988596 2230703 := bstep (se 1 (by rfl) ⟨1673027, by rfl⟩ : syracuseStep 2230703 = 3346055) B3346055
theorem B2230739 : Blo 988596 2230739 := bstep (se 1 (by rfl) ⟨1673054, by rfl⟩ : syracuseStep 2230739 = 3346109) B3346109
theorem B8129011 : Blo 988596 8129011 := bstep (se 1 (by rfl) ⟨6096758, by rfl⟩ : syracuseStep 8129011 = 12193517) B12193517
theorem B1673723 : Blo 988596 1673723 := bstep (se 1 (by rfl) ⟨1255292, by rfl⟩ : syracuseStep 1673723 = 2510585) B2510585
theorem B2230847 : Blo 988596 2230847 := bstep (se 1 (by rfl) ⟨1673135, by rfl⟩ : syracuseStep 2230847 = 3346271) B3346271
theorem B3344975 : Blo 988596 3344975 := bstep (se 1 (by rfl) ⟨2508731, by rfl⟩ : syracuseStep 3344975 = 5017463) B5017463
theorem B2230955 : Blo 988596 2230955 := bstep (se 1 (by rfl) ⟨1673216, by rfl⟩ : syracuseStep 2230955 = 3346433) B3346433
theorem B8456993 : Blo 988596 8456993 := bstep (se 2 (by rfl) ⟨3171372, by rfl⟩ : syracuseStep 8456993 = 6342745) B6342745
theorem B5016491 : Blo 988596 5016491 := bstep (se 1 (by rfl) ⟨3762368, by rfl⟩ : syracuseStep 5016491 = 7524737) B7524737
theorem B1674155 : Blo 988596 1674155 := bstep (se 1 (by rfl) ⟨1255616, by rfl⟩ : syracuseStep 1674155 = 2511233) B2511233
theorem B4754447 : Blo 988596 4754447 := bstep (se 1 (by rfl) ⟨3565835, by rfl⟩ : syracuseStep 4754447 = 7131671) B7131671
theorem B2231495 : Blo 988596 2231495 := bstep (se 1 (by rfl) ⟨1673621, by rfl⟩ : syracuseStep 2231495 = 3347243) B3347243
theorem B2231675 : Blo 988596 2231675 := bstep (se 1 (by rfl) ⟨1673756, by rfl⟩ : syracuseStep 2231675 = 3347513) B3347513
theorem B1674695 : Blo 988596 1674695 := bstep (se 1 (by rfl) ⟨1256021, by rfl⟩ : syracuseStep 1674695 = 2512043) B2512043
theorem B2231801 : Blo 988596 2231801 := bstep (se 2 (by rfl) ⟨836925, by rfl⟩ : syracuseStep 2231801 = 1673851) B1673851
theorem B4230737 : Blo 988596 4230737 := bstep (se 2 (by rfl) ⟨1586526, by rfl⟩ : syracuseStep 4230737 = 3173053) B3173053
theorem B2231891 : Blo 988596 2231891 := bstep (se 1 (by rfl) ⟨1673918, by rfl⟩ : syracuseStep 2231891 = 3347837) B3347837
theorem B16944875 : Blo 988596 16944875 := bstep (se 1 (by rfl) ⟨12708656, by rfl⟩ : syracuseStep 16944875 = 25417313) B25417313
theorem B2232071 : Blo 988596 2232071 := bstep (se 1 (by rfl) ⟨1674053, by rfl⟩ : syracuseStep 2232071 = 3348107) B3348107
theorem B3346217 : Blo 988596 3346217 := bstep (se 2 (by rfl) ⟨1254831, by rfl⟩ : syracuseStep 3346217 = 2509663) B2509663
theorem B1412905 : Blo 988596 1412905 := bstep (se 2 (by rfl) ⟨529839, by rfl⟩ : syracuseStep 1412905 = 1059679) B1059679
theorem B8130361 : Blo 988596 8130361 := bstep (se 2 (by rfl) ⟨3048885, by rfl⟩ : syracuseStep 8130361 = 6097771) B6097771
theorem B3805193 : Blo 988596 3805193 := bstep (se 2 (by rfl) ⟨1426947, by rfl⟩ : syracuseStep 3805193 = 2853895) B2853895
theorem B5017625 : Blo 988596 5017625 := bstep (se 2 (by rfl) ⟨1881609, by rfl⟩ : syracuseStep 5017625 = 3763219) B3763219
theorem B3576155 : Blo 988596 3576155 := bstep (se 1 (by rfl) ⟨2682116, by rfl⟩ : syracuseStep 3576155 = 5364233) B5364233
theorem B2232683 : Blo 988596 2232683 := bstep (se 1 (by rfl) ⟨1674512, by rfl⟩ : syracuseStep 2232683 = 3349025) B3349025
theorem B2232827 : Blo 988596 2232827 := bstep (se 1 (by rfl) ⟨1674620, by rfl⟩ : syracuseStep 2232827 = 3349241) B3349241
theorem B3805697 : Blo 988596 3805697 := bstep (se 2 (by rfl) ⟨1427136, by rfl⟩ : syracuseStep 3805697 = 2854273) B2854273
theorem B4231777 : Blo 988596 4231777 := bstep (se 2 (by rfl) ⟨1586916, by rfl⟩ : syracuseStep 4231777 = 3173833) B3173833
theorem B2232953 : Blo 988596 2232953 := bstep (se 2 (by rfl) ⟨837357, by rfl⟩ : syracuseStep 2232953 = 1674715) B1674715
theorem B2233007 : Blo 988596 2233007 := bstep (se 1 (by rfl) ⟨1674755, by rfl⟩ : syracuseStep 2233007 = 3349511) B3349511
theorem B2233079 : Blo 988596 2233079 := bstep (se 1 (by rfl) ⟨1674809, by rfl⟩ : syracuseStep 2233079 = 3349619) B3349619
theorem B2233259 : Blo 988596 2233259 := bstep (se 1 (by rfl) ⟨1674944, by rfl⟩ : syracuseStep 2233259 = 3349889) B3349889
theorem B988667 : Blo 988596 988667 := bstep (se 1 (by rfl) ⟨741500, by rfl⟩ : syracuseStep 988667 = 1483001) B1483001
theorem B988735 : Blo 988596 988735 := bstep (se 1 (by rfl) ⟨741551, by rfl⟩ : syracuseStep 988735 = 1483103) B1483103
theorem B988743 : Blo 988596 988743 := bstep (se 1 (by rfl) ⟨741557, by rfl⟩ : syracuseStep 988743 = 1483115) B1483115
theorem B5641913 : Blo 988596 5641913 := bstep (se 2 (by rfl) ⟨2115717, by rfl⟩ : syracuseStep 5641913 = 4231435) B4231435
theorem B988895 : Blo 988596 988895 := bstep (se 1 (by rfl) ⟨741671, by rfl⟩ : syracuseStep 988895 = 1483343) B1483343
theorem B1611499 : Blo 988596 1611499 := bstep (se 1 (by rfl) ⟨1208624, by rfl⟩ : syracuseStep 1611499 = 2417249) B2417249
theorem B6788893 : Blo 988596 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B988975 : Blo 988596 988975 := bstep (se 1 (by rfl) ⟨741731, by rfl⟩ : syracuseStep 988975 = 1483463) B1483463
theorem B1251227 : Blo 988596 1251227 := bstep (se 1 (by rfl) ⟨938420, by rfl⟩ : syracuseStep 1251227 = 1876841) B1876841
theorem B989083 : Blo 988596 989083 := bstep (se 1 (by rfl) ⟨741812, by rfl⟩ : syracuseStep 989083 = 1483625) B1483625
theorem B989135 : Blo 988596 989135 := bstep (se 1 (by rfl) ⟨741851, by rfl⟩ : syracuseStep 989135 = 1483703) B1483703
theorem B3348431 : Blo 988596 3348431 := bstep (se 1 (by rfl) ⟨2511323, by rfl⟩ : syracuseStep 3348431 = 5022647) B5022647
theorem B989159 : Blo 988596 989159 := bstep (se 1 (by rfl) ⟨741869, by rfl⟩ : syracuseStep 989159 = 1483739) B1483739
theorem B5347457 : Blo 988596 5347457 := bstep (se 2 (by rfl) ⟨2005296, by rfl⟩ : syracuseStep 5347457 = 4010593) B4010593
theorem B989471 : Blo 988596 989471 := bstep (se 1 (by rfl) ⟨742103, by rfl⟩ : syracuseStep 989471 = 1484207) B1484207
theorem B9509197 : Blo 988596 9509197 := bstep (se 3 (by rfl) ⟨1782974, by rfl⟩ : syracuseStep 9509197 = 3565949) B3565949
theorem B989531 : Blo 988596 989531 := bstep (se 1 (by rfl) ⟨742148, by rfl⟩ : syracuseStep 989531 = 1484297) B1484297
theorem B989551 : Blo 988596 989551 := bstep (se 1 (by rfl) ⟨742163, by rfl⟩ : syracuseStep 989551 = 1484327) B1484327
theorem B5642621 : Blo 988596 5642621 := bstep (se 3 (by rfl) ⟨1057991, by rfl⟩ : syracuseStep 5642621 = 2115983) B2115983
theorem B989607 : Blo 988596 989607 := bstep (se 1 (by rfl) ⟨742205, by rfl⟩ : syracuseStep 989607 = 1484411) B1484411
theorem B989691 : Blo 988596 989691 := bstep (se 1 (by rfl) ⟨742268, by rfl⟩ : syracuseStep 989691 = 1484537) B1484537
theorem B989759 : Blo 988596 989759 := bstep (se 1 (by rfl) ⟨742319, by rfl⟩ : syracuseStep 989759 = 1484639) B1484639
theorem B989767 : Blo 988596 989767 := bstep (se 1 (by rfl) ⟨742325, by rfl⟩ : syracuseStep 989767 = 1484651) B1484651
theorem B989919 : Blo 988596 989919 := bstep (se 1 (by rfl) ⟨742439, by rfl⟩ : syracuseStep 989919 = 1484879) B1484879
theorem B41720579 : Blo 988596 41720579 := bstep (se 1 (by rfl) ⟨31290434, by rfl⟩ : syracuseStep 41720579 = 62580869) B62580869
theorem B989999 : Blo 988596 989999 := bstep (se 1 (by rfl) ⟨742499, by rfl⟩ : syracuseStep 989999 = 1484999) B1484999
theorem B5020541 : Blo 988596 5020541 := bstep (se 3 (by rfl) ⟨941351, by rfl⟩ : syracuseStep 5020541 = 1882703) B1882703
theorem B990107 : Blo 988596 990107 := bstep (se 1 (by rfl) ⟨742580, by rfl⟩ : syracuseStep 990107 = 1485161) B1485161
theorem B3349403 : Blo 988596 3349403 := bstep (se 1 (by rfl) ⟨2512052, by rfl⟩ : syracuseStep 3349403 = 5024105) B5024105
theorem B990159 : Blo 988596 990159 := bstep (se 1 (by rfl) ⟨742619, by rfl⟩ : syracuseStep 990159 = 1485239) B1485239
theorem B990183 : Blo 988596 990183 := bstep (se 1 (by rfl) ⟨742637, by rfl⟩ : syracuseStep 990183 = 1485275) B1485275
theorem B1809551 : Blo 988596 1809551 := bstep (se 1 (by rfl) ⟨1357163, by rfl⟩ : syracuseStep 1809551 = 2714327) B2714327
theorem B990495 : Blo 988596 990495 := bstep (se 1 (by rfl) ⟨742871, by rfl⟩ : syracuseStep 990495 = 1485743) B1485743
theorem B75144523 : Blo 988596 75144523 := bstep (se 1 (by rfl) ⟨56358392, by rfl⟩ : syracuseStep 75144523 = 112716785) B112716785
theorem B990555 : Blo 988596 990555 := bstep (se 1 (by rfl) ⟨742916, by rfl⟩ : syracuseStep 990555 = 1485833) B1485833
theorem B990575 : Blo 988596 990575 := bstep (se 1 (by rfl) ⟨742931, by rfl⟩ : syracuseStep 990575 = 1485863) B1485863
theorem B14261669 : Blo 988596 14261669 := bstep (se 4 (by rfl) ⟨1337031, by rfl⟩ : syracuseStep 14261669 = 2674063) B2674063
theorem B990631 : Blo 988596 990631 := bstep (se 1 (by rfl) ⟨742973, by rfl⟩ : syracuseStep 990631 = 1485947) B1485947
theorem B990715 : Blo 988596 990715 := bstep (se 1 (by rfl) ⟨743036, by rfl⟩ : syracuseStep 990715 = 1486073) B1486073
theorem B990783 : Blo 988596 990783 := bstep (se 1 (by rfl) ⟨743087, by rfl⟩ : syracuseStep 990783 = 1486175) B1486175
theorem B990791 : Blo 988596 990791 := bstep (se 1 (by rfl) ⟨743093, by rfl⟩ : syracuseStep 990791 = 1486187) B1486187
theorem B9641587 : Blo 988596 9641587 := bstep (se 1 (by rfl) ⟨7231190, by rfl⟩ : syracuseStep 9641587 = 14462381) B14462381
theorem B990943 : Blo 988596 990943 := bstep (se 1 (by rfl) ⟨743207, by rfl⟩ : syracuseStep 990943 = 1486415) B1486415
theorem B991023 : Blo 988596 991023 := bstep (se 1 (by rfl) ⟨743267, by rfl⟩ : syracuseStep 991023 = 1486535) B1486535
theorem B5021513 : Blo 988596 5021513 := bstep (se 2 (by rfl) ⟨1883067, by rfl⟩ : syracuseStep 5021513 = 3766135) B3766135
theorem B991131 : Blo 988596 991131 := bstep (se 1 (by rfl) ⟨743348, by rfl⟩ : syracuseStep 991131 = 1486697) B1486697
theorem B991183 : Blo 988596 991183 := bstep (se 1 (by rfl) ⟨743387, by rfl⟩ : syracuseStep 991183 = 1486775) B1486775
theorem B991207 : Blo 988596 991207 := bstep (se 1 (by rfl) ⟨743405, by rfl⟩ : syracuseStep 991207 = 1486811) B1486811
theorem B2826265 : Blo 988596 2826265 := bstep (se 2 (by rfl) ⟨1059849, by rfl⟩ : syracuseStep 2826265 = 2119699) B2119699
theorem B4235435 : Blo 988596 4235435 := bstep (se 1 (by rfl) ⟨3176576, by rfl⟩ : syracuseStep 4235435 = 6353153) B6353153
theorem B991519 : Blo 988596 991519 := bstep (se 1 (by rfl) ⟨743639, by rfl⟩ : syracuseStep 991519 = 1487279) B1487279
theorem B991579 : Blo 988596 991579 := bstep (se 1 (by rfl) ⟨743684, by rfl⟩ : syracuseStep 991579 = 1487369) B1487369
theorem B991599 : Blo 988596 991599 := bstep (se 1 (by rfl) ⟨743699, by rfl⟩ : syracuseStep 991599 = 1487399) B1487399
theorem B1483175 : Blo 988596 1483175 := bstep (se 1 (by rfl) ⟨1112381, by rfl⟩ : syracuseStep 1483175 = 2224763) B2224763
theorem B991655 : Blo 988596 991655 := bstep (se 1 (by rfl) ⟨743741, by rfl⟩ : syracuseStep 991655 = 1487483) B1487483
theorem B1483259 : Blo 988596 1483259 := bstep (se 1 (by rfl) ⟨1112444, by rfl⟩ : syracuseStep 1483259 = 2224889) B2224889
theorem B991739 : Blo 988596 991739 := bstep (se 1 (by rfl) ⟨743804, by rfl⟩ : syracuseStep 991739 = 1487609) B1487609
theorem B7512587 : Blo 988596 7512587 := bstep (se 1 (by rfl) ⟨5634440, by rfl⟩ : syracuseStep 7512587 = 11268881) B11268881
theorem B991807 : Blo 988596 991807 := bstep (se 1 (by rfl) ⟨743855, by rfl⟩ : syracuseStep 991807 = 1487711) B1487711
theorem B991815 : Blo 988596 991815 := bstep (se 1 (by rfl) ⟨743861, by rfl⟩ : syracuseStep 991815 = 1487723) B1487723
theorem B1483385 : Blo 988596 1483385 := bstep (se 2 (by rfl) ⟨556269, by rfl⟩ : syracuseStep 1483385 = 1112539) B1112539
theorem B1483439 : Blo 988596 1483439 := bstep (se 1 (by rfl) ⟨1112579, by rfl⟩ : syracuseStep 1483439 = 2225159) B2225159
theorem B1483487 : Blo 988596 1483487 := bstep (se 1 (by rfl) ⟨1112615, by rfl⟩ : syracuseStep 1483487 = 2225231) B2225231
theorem B991967 : Blo 988596 991967 := bstep (se 1 (by rfl) ⟨743975, by rfl⟩ : syracuseStep 991967 = 1487951) B1487951
theorem B992047 : Blo 988596 992047 := bstep (se 1 (by rfl) ⟨744035, by rfl⟩ : syracuseStep 992047 = 1488071) B1488071
theorem B1254199 : Blo 988596 1254199 := bstep (se 1 (by rfl) ⟨940649, by rfl⟩ : syracuseStep 1254199 = 1881299) B1881299
theorem B12067679 : Blo 988596 12067679 := bstep (se 1 (by rfl) ⟨9050759, by rfl⟩ : syracuseStep 12067679 = 18101519) B18101519
theorem B992155 : Blo 988596 992155 := bstep (se 1 (by rfl) ⟨744116, by rfl⟩ : syracuseStep 992155 = 1488233) B1488233
theorem B992207 : Blo 988596 992207 := bstep (se 1 (by rfl) ⟨744155, by rfl⟩ : syracuseStep 992207 = 1488311) B1488311
theorem B1483751 : Blo 988596 1483751 := bstep (se 1 (by rfl) ⟨1112813, by rfl⟩ : syracuseStep 1483751 = 2225627) B2225627
theorem B992231 : Blo 988596 992231 := bstep (se 1 (by rfl) ⟨744173, by rfl⟩ : syracuseStep 992231 = 1488347) B1488347
theorem B5022809 : Blo 988596 5022809 := bstep (se 2 (by rfl) ⟨1883553, by rfl⟩ : syracuseStep 5022809 = 3767107) B3767107
theorem B1254619 : Blo 988596 1254619 := bstep (se 1 (by rfl) ⟨940964, by rfl⟩ : syracuseStep 1254619 = 1881929) B1881929
theorem B1484009 : Blo 988596 1484009 := bstep (se 2 (by rfl) ⟨556503, by rfl⟩ : syracuseStep 1484009 = 1113007) B1113007
theorem B1484063 : Blo 988596 1484063 := bstep (se 1 (by rfl) ⟨1113047, by rfl⟩ : syracuseStep 1484063 = 2226095) B2226095
theorem B992543 : Blo 988596 992543 := bstep (se 1 (by rfl) ⟨744407, by rfl⟩ : syracuseStep 992543 = 1488815) B1488815
theorem B4826561 : Blo 988596 4826561 := bstep (se 2 (by rfl) ⟨1809960, by rfl⟩ : syracuseStep 4826561 = 3619921) B3619921
theorem B1484231 : Blo 988596 1484231 := bstep (se 1 (by rfl) ⟨1113173, by rfl⟩ : syracuseStep 1484231 = 2226347) B2226347
theorem B1484585 : Blo 988596 1484585 := bstep (se 2 (by rfl) ⟨556719, by rfl⟩ : syracuseStep 1484585 = 1113439) B1113439
theorem B1484591 : Blo 988596 1484591 := bstep (se 1 (by rfl) ⟨1113443, by rfl⟩ : syracuseStep 1484591 = 2226887) B2226887
theorem B5646287 : Blo 988596 5646287 := bstep (se 1 (by rfl) ⟨4234715, by rfl⟩ : syracuseStep 5646287 = 8469431) B8469431
theorem B1485065 : Blo 988596 1485065 := bstep (se 2 (by rfl) ⟨556899, by rfl⟩ : syracuseStep 1485065 = 1113799) B1113799
theorem B16296227 : Blo 988596 16296227 := bstep (se 1 (by rfl) ⟨12222170, by rfl⟩ : syracuseStep 16296227 = 24444341) B24444341
theorem B1878383 : Blo 988596 1878383 := bstep (se 1 (by rfl) ⟨1408787, by rfl⟩ : syracuseStep 1878383 = 2817575) B2817575
theorem B1485167 : Blo 988596 1485167 := bstep (se 1 (by rfl) ⟨1113875, by rfl⟩ : syracuseStep 1485167 = 2227751) B2227751
theorem B8464783 : Blo 988596 8464783 := bstep (se 1 (by rfl) ⟨6348587, by rfl⟩ : syracuseStep 8464783 = 12697175) B12697175
theorem B1485383 : Blo 988596 1485383 := bstep (se 1 (by rfl) ⟨1114037, by rfl⟩ : syracuseStep 1485383 = 2228075) B2228075
theorem B1190495 : Blo 988596 1190495 := bstep (se 1 (by rfl) ⟨892871, by rfl⟩ : syracuseStep 1190495 = 1785743) B1785743
theorem B1485419 : Blo 988596 1485419 := bstep (se 1 (by rfl) ⟨1114064, by rfl⟩ : syracuseStep 1485419 = 2228129) B2228129
theorem B1256239 : Blo 988596 1256239 := bstep (se 1 (by rfl) ⟨942179, by rfl⟩ : syracuseStep 1256239 = 1884359) B1884359
theorem B1485647 : Blo 988596 1485647 := bstep (se 1 (by rfl) ⟨1114235, by rfl⟩ : syracuseStep 1485647 = 2228471) B2228471
theorem B1486043 : Blo 988596 1486043 := bstep (se 1 (by rfl) ⟨1114532, by rfl⟩ : syracuseStep 1486043 = 2229065) B2229065
theorem B5221597 : Blo 988596 5221597 := bstep (se 3 (by rfl) ⟨979049, by rfl⟩ : syracuseStep 5221597 = 1958099) B1958099
theorem B5647745 : Blo 988596 5647745 := bstep (se 2 (by rfl) ⟨2117904, by rfl⟩ : syracuseStep 5647745 = 4235809) B4235809
theorem B1486217 : Blo 988596 1486217 := bstep (se 2 (by rfl) ⟨557331, by rfl⟩ : syracuseStep 1486217 = 1114663) B1114663
theorem B8466119 : Blo 988596 8466119 := bstep (se 1 (by rfl) ⟨6349589, by rfl⟩ : syracuseStep 8466119 = 12699179) B12699179
theorem B1879787 : Blo 988596 1879787 := bstep (se 1 (by rfl) ⟨1409840, by rfl⟩ : syracuseStep 1879787 = 2819681) B2819681
theorem B1486571 : Blo 988596 1486571 := bstep (se 1 (by rfl) ⟨1114928, by rfl⟩ : syracuseStep 1486571 = 2229857) B2229857
theorem B1584937 : Blo 988596 1584937 := bstep (se 2 (by rfl) ⟨594351, by rfl⟩ : syracuseStep 1584937 = 1188703) B1188703
theorem B4534073 : Blo 988596 4534073 := bstep (se 2 (by rfl) ⟨1700277, by rfl⟩ : syracuseStep 4534073 = 3400555) B3400555
theorem B14299085 : Blo 988596 14299085 := bstep (se 3 (by rfl) ⟨2681078, by rfl⟩ : syracuseStep 14299085 = 5362157) B5362157
theorem B1486799 : Blo 988596 1486799 := bstep (se 1 (by rfl) ⟨1115099, by rfl⟩ : syracuseStep 1486799 = 2230199) B2230199
theorem B1487195 : Blo 988596 1487195 := bstep (se 1 (by rfl) ⟨1115396, by rfl⟩ : syracuseStep 1487195 = 2230793) B2230793
theorem B9515501 : Blo 988596 9515501 := bstep (se 3 (by rfl) ⟨1784156, by rfl⟩ : syracuseStep 9515501 = 3568313) B3568313
theorem B2503163 : Blo 988596 2503163 := bstep (se 1 (by rfl) ⟨1877372, by rfl⟩ : syracuseStep 2503163 = 3754745) B3754745
theorem B1487423 : Blo 988596 1487423 := bstep (se 1 (by rfl) ⟨1115567, by rfl⟩ : syracuseStep 1487423 = 2231135) B2231135
theorem B1880759 : Blo 988596 1880759 := bstep (se 1 (by rfl) ⟨1410569, by rfl⟩ : syracuseStep 1880759 = 2821139) B2821139
theorem B1487543 : Blo 988596 1487543 := bstep (se 1 (by rfl) ⟨1115657, by rfl⟩ : syracuseStep 1487543 = 2231315) B2231315
theorem B4010719 : Blo 988596 4010719 := bstep (se 1 (by rfl) ⟨3008039, by rfl⟩ : syracuseStep 4010719 = 6016079) B6016079
theorem B1880911 : Blo 988596 1880911 := bstep (se 1 (by rfl) ⟨1410683, by rfl⟩ : syracuseStep 1880911 = 2821367) B2821367
theorem B1487771 : Blo 988596 1487771 := bstep (se 1 (by rfl) ⟨1115828, by rfl⟩ : syracuseStep 1487771 = 2231657) B2231657
theorem B1488167 : Blo 988596 1488167 := bstep (se 1 (by rfl) ⟨1116125, by rfl⟩ : syracuseStep 1488167 = 2232251) B2232251
theorem B1488251 : Blo 988596 1488251 := bstep (se 1 (by rfl) ⟨1116188, by rfl⟩ : syracuseStep 1488251 = 2232377) B2232377
theorem B1881481 : Blo 988596 1881481 := bstep (se 2 (by rfl) ⟨705555, by rfl⟩ : syracuseStep 1881481 = 1411111) B1411111
theorem B4011403 : Blo 988596 4011403 := bstep (se 1 (by rfl) ⟨3008552, by rfl⟩ : syracuseStep 4011403 = 6017105) B6017105
theorem B2504135 : Blo 988596 2504135 := bstep (se 1 (by rfl) ⟨1878101, by rfl⟩ : syracuseStep 2504135 = 3756203) B3756203
theorem B1488377 : Blo 988596 1488377 := bstep (se 2 (by rfl) ⟨558141, by rfl⟩ : syracuseStep 1488377 = 1116283) B1116283
theorem B1586783 : Blo 988596 1586783 := bstep (se 1 (by rfl) ⟨1190087, by rfl⟩ : syracuseStep 1586783 = 2380175) B2380175
theorem B1488479 : Blo 988596 1488479 := bstep (se 1 (by rfl) ⟨1116359, by rfl⟩ : syracuseStep 1488479 = 2232719) B2232719
theorem B2537257 : Blo 988596 2537257 := bstep (se 2 (by rfl) ⟨951471, by rfl⟩ : syracuseStep 2537257 = 1902943) B1902943
theorem B1488695 : Blo 988596 1488695 := bstep (se 1 (by rfl) ⟨1116521, by rfl⟩ : syracuseStep 1488695 = 2233043) B2233043
theorem B72267673 : Blo 988596 72267673 := bstep (se 2 (by rfl) ⟨27100377, by rfl⟩ : syracuseStep 72267673 = 54200755) B54200755
theorem B1882217 : Blo 988596 1882217 := bstep (se 2 (by rfl) ⟨705831, by rfl⟩ : syracuseStep 1882217 = 1411663) B1411663
theorem B20363399 : Blo 988596 20363399 := bstep (se 1 (by rfl) ⟨15272549, by rfl⟩ : syracuseStep 20363399 = 30545099) B30545099
theorem B2504915 : Blo 988596 2504915 := bstep (se 1 (by rfl) ⟨1878686, by rfl⟩ : syracuseStep 2504915 = 3757373) B3757373
theorem B16923005 : Blo 988596 16923005 := bstep (se 3 (by rfl) ⟨3173063, by rfl⟩ : syracuseStep 16923005 = 6346127) B6346127
theorem B2505127 : Blo 988596 2505127 := bstep (se 1 (by rfl) ⟨1878845, by rfl⟩ : syracuseStep 2505127 = 3757691) B3757691
theorem B2505289 : Blo 988596 2505289 := bstep (se 2 (by rfl) ⟨939483, by rfl⟩ : syracuseStep 2505289 = 1878967) B1878967
theorem B2112335 : Blo 988596 2112335 := bstep (se 1 (by rfl) ⟨1584251, by rfl⟩ : syracuseStep 2112335 = 3168503) B3168503
theorem B2112635 : Blo 988596 2112635 := bstep (se 1 (by rfl) ⟨1584476, by rfl⟩ : syracuseStep 2112635 = 3168953) B3168953
theorem B9518269 : Blo 988596 9518269 := bstep (se 3 (by rfl) ⟨1784675, by rfl⟩ : syracuseStep 9518269 = 3569351) B3569351
theorem B2112745 : Blo 988596 2112745 := bstep (se 2 (by rfl) ⟨792279, by rfl⟩ : syracuseStep 2112745 = 1584559) B1584559
theorem B2506079 : Blo 988596 2506079 := bstep (se 1 (by rfl) ⟨1879559, by rfl⟩ : syracuseStep 2506079 = 3759119) B3759119
theorem B6339977 : Blo 988596 6339977 := bstep (se 2 (by rfl) ⟨2377491, by rfl⟩ : syracuseStep 6339977 = 4754983) B4754983
theorem B4767113 : Blo 988596 4767113 := bstep (se 2 (by rfl) ⟨1787667, by rfl⟩ : syracuseStep 4767113 = 3575335) B3575335
theorem B1883911 : Blo 988596 1883911 := bstep (se 1 (by rfl) ⟨1412933, by rfl⟩ : syracuseStep 1883911 = 2825867) B2825867
theorem B7126825 : Blo 988596 7126825 := bstep (se 2 (by rfl) ⟨2672559, by rfl⟩ : syracuseStep 7126825 = 5345119) B5345119
theorem B5652827 : Blo 988596 5652827 := bstep (se 1 (by rfl) ⟨4239620, by rfl⟩ : syracuseStep 5652827 = 8479241) B8479241
theorem B2539883 : Blo 988596 2539883 := bstep (se 1 (by rfl) ⟨1904912, by rfl⟩ : syracuseStep 2539883 = 3809825) B3809825
theorem B2507183 : Blo 988596 2507183 := bstep (se 1 (by rfl) ⟨1880387, by rfl⟩ : syracuseStep 2507183 = 3760775) B3760775
theorem B2113975 : Blo 988596 2113975 := bstep (se 1 (by rfl) ⟨1585481, by rfl⟩ : syracuseStep 2113975 = 3170963) B3170963
theorem B13746617 : Blo 988596 13746617 := bstep (se 2 (by rfl) ⟨5154981, by rfl⟩ : syracuseStep 13746617 = 10309963) B10309963
theorem B2507233 : Blo 988596 2507233 := bstep (se 2 (by rfl) ⟨940212, by rfl⟩ : syracuseStep 2507233 = 1880425) B1880425
theorem B2376415 : Blo 988596 2376415 := bstep (se 1 (by rfl) ⟨1782311, by rfl⟩ : syracuseStep 2376415 = 3564623) B3564623
theorem B1787113 : Blo 988596 1787113 := bstep (se 2 (by rfl) ⟨670167, by rfl⟩ : syracuseStep 1787113 = 1340335) B1340335
theorem B2508155 : Blo 988596 2508155 := bstep (se 1 (by rfl) ⟨1881116, by rfl⟩ : syracuseStep 2508155 = 3762233) B3762233
theorem B4769437 : Blo 988596 4769437 := bstep (se 3 (by rfl) ⟨894269, by rfl⟩ : syracuseStep 4769437 = 1788539) B1788539
theorem B19318661 : Blo 988596 19318661 := bstep (se 4 (by rfl) ⟨1811124, by rfl⟩ : syracuseStep 19318661 = 3622249) B3622249
theorem B18041231 : Blo 988596 18041231 := bstep (se 1 (by rfl) ⟨13530923, by rfl⟩ : syracuseStep 18041231 = 27061847) B27061847
theorem B9521651 : Blo 988596 9521651 := bstep (se 1 (by rfl) ⟨7141238, by rfl⟩ : syracuseStep 9521651 = 14282477) B14282477
theorem B2542631 : Blo 988596 2542631 := bstep (se 1 (by rfl) ⟨1906973, by rfl⟩ : syracuseStep 2542631 = 3813947) B3813947
theorem B2509967 : Blo 988596 2509967 := bstep (se 1 (by rfl) ⟨1882475, by rfl⟩ : syracuseStep 2509967 = 3764951) B3764951
theorem B2379145 : Blo 988596 2379145 := bstep (se 2 (by rfl) ⟨892179, by rfl⟩ : syracuseStep 2379145 = 1784359) B1784359
theorem B21384965 : Blo 988596 21384965 := bstep (se 4 (by rfl) ⟨2004840, by rfl⟩ : syracuseStep 21384965 = 4009681) B4009681
theorem B6344669 : Blo 988596 6344669 := bstep (se 3 (by rfl) ⟨1189625, by rfl⟩ : syracuseStep 6344669 = 2379251) B2379251
theorem B2117897 : Blo 988596 2117897 := bstep (se 2 (by rfl) ⟨794211, by rfl⟩ : syracuseStep 2117897 = 1588423) B1588423
theorem B2675111 : Blo 988596 2675111 := bstep (se 1 (by rfl) ⟨2006333, by rfl⟩ : syracuseStep 2675111 = 4012667) B4012667
theorem B2511607 : Blo 988596 2511607 := bstep (se 1 (by rfl) ⟨1883705, by rfl⟩ : syracuseStep 2511607 = 3767411) B3767411
theorem B7132013 : Blo 988596 7132013 := bstep (se 3 (by rfl) ⟨1337252, by rfl⟩ : syracuseStep 7132013 = 2674505) B2674505
theorem B2511911 : Blo 988596 2511911 := bstep (se 1 (by rfl) ⟨1883933, by rfl⟩ : syracuseStep 2511911 = 3767867) B3767867
theorem B4019399 : Blo 988596 4019399 := bstep (se 1 (by rfl) ⟨3014549, by rfl⟩ : syracuseStep 4019399 = 6029099) B6029099
theorem B7230721 : Blo 988596 7230721 := bstep (se 2 (by rfl) ⟨2711520, by rfl⟩ : syracuseStep 7230721 = 5423041) B5423041
theorem B20633221 : Blo 988596 20633221 := bstep (se 4 (by rfl) ⟨1934364, by rfl⟩ : syracuseStep 20633221 = 3868729) B3868729
theorem B2709179 : Blo 988596 2709179 := bstep (se 1 (by rfl) ⟨2031884, by rfl⟩ : syracuseStep 2709179 = 4063769) B4063769
theorem B6346795 : Blo 988596 6346795 := bstep (se 1 (by rfl) ⟨4760096, by rfl⟩ : syracuseStep 6346795 = 9520193) B9520193
theorem B15259727 : Blo 988596 15259727 := bstep (se 1 (by rfl) ⟨11444795, by rfl⟩ : syracuseStep 15259727 = 22889591) B22889591
theorem B3758345 : Blo 988596 3758345 := bstep (se 2 (by rfl) ⟨1409379, by rfl⟩ : syracuseStep 3758345 = 2818759) B2818759
theorem B7526681 : Blo 988596 7526681 := bstep (se 2 (by rfl) ⟨2822505, by rfl⟩ : syracuseStep 7526681 = 5645011) B5645011
theorem B1694063 : Blo 988596 1694063 := bstep (se 1 (by rfl) ⟨1270547, by rfl⟩ : syracuseStep 1694063 = 2541095) B2541095
theorem B9034415 : Blo 988596 9034415 := bstep (se 1 (by rfl) ⟨6775811, by rfl⟩ : syracuseStep 9034415 = 13551623) B13551623
theorem B2415503 : Blo 988596 2415503 := bstep (se 1 (by rfl) ⟨1811627, by rfl⟩ : syracuseStep 2415503 = 3623255) B3623255
theorem B6020219 : Blo 988596 6020219 := bstep (se 1 (by rfl) ⟨4515164, by rfl⟩ : syracuseStep 6020219 = 9030329) B9030329
theorem B7527653 : Blo 988596 7527653 := bstep (se 4 (by rfl) ⟨705717, by rfl⟩ : syracuseStep 7527653 = 1411435) B1411435
theorem B2416009 : Blo 988596 2416009 := bstep (se 2 (by rfl) ⟨906003, by rfl⟩ : syracuseStep 2416009 = 1812007) B1812007
theorem B2383663 : Blo 988596 2383663 := bstep (se 1 (by rfl) ⟨1787747, by rfl⟩ : syracuseStep 2383663 = 3575495) B3575495
theorem B5005313 : Blo 988596 5005313 := bstep (se 2 (by rfl) ⟨1876992, by rfl⟩ : syracuseStep 5005313 = 3753985) B3753985
theorem B86794649 : Blo 988596 86794649 := bstep (se 2 (by rfl) ⟨32547993, by rfl⟩ : syracuseStep 86794649 = 65095987) B65095987
theorem B27124253 : Blo 988596 27124253 := bstep (se 3 (by rfl) ⟨5085797, by rfl⟩ : syracuseStep 27124253 = 10171595) B10171595
theorem B5006123 : Blo 988596 5006123 := bstep (se 1 (by rfl) ⟨3754592, by rfl⟩ : syracuseStep 5006123 = 7509185) B7509185
theorem B2712475 : Blo 988596 2712475 := bstep (se 1 (by rfl) ⟨2034356, by rfl⟩ : syracuseStep 2712475 = 4068713) B4068713
theorem B10871783 : Blo 988596 10871783 := bstep (se 1 (by rfl) ⟨8153837, by rfl⟩ : syracuseStep 10871783 = 16307675) B16307675
theorem B3171527 : Blo 988596 3171527 := bstep (se 1 (by rfl) ⟨2378645, by rfl⟩ : syracuseStep 3171527 = 4757291) B4757291
theorem B12871457 : Blo 988596 12871457 := bstep (se 2 (by rfl) ⟨4826796, by rfl⟩ : syracuseStep 12871457 = 9653593) B9653593
theorem B5433193 : Blo 988596 5433193 := bstep (se 2 (by rfl) ⟨2037447, by rfl⟩ : syracuseStep 5433193 = 4074895) B4074895
theorem B10708919 : Blo 988596 10708919 := bstep (se 1 (by rfl) ⟨8031689, by rfl⟩ : syracuseStep 10708919 = 16063379) B16063379
theorem B18606167 : Blo 988596 18606167 := bstep (se 1 (by rfl) ⟨13954625, by rfl⟩ : syracuseStep 18606167 = 27909251) B27909251
theorem B3336659 : Blo 988596 3336659 := bstep (se 1 (by rfl) ⟨2502494, by rfl⟩ : syracuseStep 3336659 = 5004989) B5004989
theorem B3172859 : Blo 988596 3172859 := bstep (se 1 (by rfl) ⟨2379644, by rfl⟩ : syracuseStep 3172859 = 4759289) B4759289
theorem B3336767 : Blo 988596 3336767 := bstep (se 1 (by rfl) ⟨2502575, by rfl⟩ : syracuseStep 3336767 = 5005151) B5005151
theorem B2681417 : Blo 988596 2681417 := bstep (se 2 (by rfl) ⟨1005531, by rfl⟩ : syracuseStep 2681417 = 2011063) B2011063
theorem B5008067 : Blo 988596 5008067 := bstep (se 1 (by rfl) ⟨3756050, by rfl⟩ : syracuseStep 5008067 = 7512101) B7512101
theorem B3763523 : Blo 988596 3763523 := bstep (se 1 (by rfl) ⟨2822642, by rfl⟩ : syracuseStep 3763523 = 5645285) B5645285
theorem B3763705 : Blo 988596 3763705 := bstep (se 2 (by rfl) ⟨1411389, by rfl⟩ : syracuseStep 3763705 = 2822779) B2822779
theorem B2682463 : Blo 988596 2682463 := bstep (se 1 (by rfl) ⟨2011847, by rfl⟩ : syracuseStep 2682463 = 4023695) B4023695
theorem B3763979 : Blo 988596 3763979 := bstep (se 1 (by rfl) ⟨2822984, by rfl⟩ : syracuseStep 3763979 = 5645969) B5645969
theorem B3764009 : Blo 988596 3764009 := bstep (se 2 (by rfl) ⟨1411503, by rfl⟩ : syracuseStep 3764009 = 2823007) B2823007
theorem B9531341 : Blo 988596 9531341 := bstep (se 3 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 9531341 = 3574253) B3574253
theorem B6353099 : Blo 988596 6353099 := bstep (se 1 (by rfl) ⟨4764824, by rfl⟩ : syracuseStep 6353099 = 9529649) B9529649
theorem B10186955 : Blo 988596 10186955 := bstep (se 1 (by rfl) ⟨7640216, by rfl⟩ : syracuseStep 10186955 = 15280433) B15280433
theorem B2224457 : Blo 988596 2224457 := bstep (se 2 (by rfl) ⟨834171, by rfl⟩ : syracuseStep 2224457 = 1668343) B1668343
theorem B2224475 : Blo 988596 2224475 := bstep (se 1 (by rfl) ⟨1668356, by rfl⟩ : syracuseStep 2224475 = 3336713) B3336713
theorem B3338603 : Blo 988596 3338603 := bstep (se 1 (by rfl) ⟨2503952, by rfl⟩ : syracuseStep 3338603 = 5007905) B5007905
theorem B3338873 : Blo 988596 3338873 := bstep (se 2 (by rfl) ⟨1252077, by rfl⟩ : syracuseStep 3338873 = 2504155) B2504155
theorem B5632847 : Blo 988596 5632847 := bstep (se 1 (by rfl) ⟨4224635, by rfl⟩ : syracuseStep 5632847 = 8449271) B8449271
theorem B2225051 : Blo 988596 2225051 := bstep (se 1 (by rfl) ⟨1668788, by rfl⟩ : syracuseStep 2225051 = 3337577) B3337577
theorem B2225249 : Blo 988596 2225249 := bstep (se 2 (by rfl) ⟨834468, by rfl⟩ : syracuseStep 2225249 = 1668937) B1668937
theorem B2225447 : Blo 988596 2225447 := bstep (se 1 (by rfl) ⟨1669085, by rfl⟩ : syracuseStep 2225447 = 3338171) B3338171
theorem B4650553 : Blo 988596 4650553 := bstep (se 2 (by rfl) ⟨1743957, by rfl⟩ : syracuseStep 4650553 = 3487915) B3487915
theorem B2225825 : Blo 988596 2225825 := bstep (se 2 (by rfl) ⟨834684, by rfl⟩ : syracuseStep 2225825 = 1669369) B1669369
theorem B3569339 : Blo 988596 3569339 := bstep (se 1 (by rfl) ⟨2677004, by rfl⟩ : syracuseStep 3569339 = 5354009) B5354009
theorem B3766121 : Blo 988596 3766121 := bstep (se 2 (by rfl) ⟨1412295, by rfl⟩ : syracuseStep 3766121 = 2824591) B2824591
theorem B2226185 : Blo 988596 2226185 := bstep (se 2 (by rfl) ⟨834819, by rfl⟩ : syracuseStep 2226185 = 1669639) B1669639
theorem B18086125 : Blo 988596 18086125 := bstep (se 3 (by rfl) ⟨3391148, by rfl⟩ : syracuseStep 18086125 = 6782297) B6782297
theorem B1112359 : Blo 988596 1112359 := bstep (se 1 (by rfl) ⟨834269, by rfl⟩ : syracuseStep 1112359 = 1668539) B1668539
theorem B1112431 : Blo 988596 1112431 := bstep (se 1 (by rfl) ⟨834323, by rfl⟩ : syracuseStep 1112431 = 1668647) B1668647
theorem B3340655 : Blo 988596 3340655 := bstep (se 1 (by rfl) ⟨2505491, by rfl⟩ : syracuseStep 3340655 = 5010983) B5010983
theorem B4225405 : Blo 988596 4225405 := bstep (se 3 (by rfl) ⟨792263, by rfl⟩ : syracuseStep 4225405 = 1584527) B1584527
theorem B2226599 : Blo 988596 2226599 := bstep (se 1 (by rfl) ⟨1669949, by rfl⟩ : syracuseStep 2226599 = 3339899) B3339899
theorem B5011955 : Blo 988596 5011955 := bstep (se 1 (by rfl) ⟨3758966, by rfl⟩ : syracuseStep 5011955 = 7517933) B7517933
theorem B2226707 : Blo 988596 2226707 := bstep (se 1 (by rfl) ⟨1670030, by rfl⟩ : syracuseStep 2226707 = 3340061) B3340061
theorem B5634623 : Blo 988596 5634623 := bstep (se 1 (by rfl) ⟨4225967, by rfl⟩ : syracuseStep 5634623 = 8451935) B8451935
theorem B1112647 : Blo 988596 1112647 := bstep (se 1 (by rfl) ⟨834485, by rfl⟩ : syracuseStep 1112647 = 1668971) B1668971
theorem B2226761 : Blo 988596 2226761 := bstep (se 2 (by rfl) ⟨835035, by rfl⟩ : syracuseStep 2226761 = 1670071) B1670071
theorem B1669855 : Blo 988596 1669855 := bstep (se 1 (by rfl) ⟨1252391, by rfl⟩ : syracuseStep 1669855 = 2504783) B2504783
theorem B6355867 : Blo 988596 6355867 := bstep (se 1 (by rfl) ⟨4766900, by rfl⟩ : syracuseStep 6355867 = 9533801) B9533801
theorem B2227175 : Blo 988596 2227175 := bstep (se 1 (by rfl) ⟨1670381, by rfl⟩ : syracuseStep 2227175 = 3340763) B3340763
theorem B5012603 : Blo 988596 5012603 := bstep (se 1 (by rfl) ⟨3759452, by rfl⟩ : syracuseStep 5012603 = 7518905) B7518905
theorem B1670287 : Blo 988596 1670287 := bstep (se 1 (by rfl) ⟨1252715, by rfl⟩ : syracuseStep 1670287 = 2505431) B2505431
theorem B2227553 : Blo 988596 2227553 := bstep (se 2 (by rfl) ⟨835332, by rfl⟩ : syracuseStep 2227553 = 1670665) B1670665
theorem B1670537 : Blo 988596 1670537 := bstep (se 2 (by rfl) ⟨626451, by rfl⟩ : syracuseStep 1670537 = 1252903) B1252903
theorem B1113511 : Blo 988596 1113511 := bstep (se 1 (by rfl) ⟨835133, by rfl⟩ : syracuseStep 1113511 = 1670267) B1670267
theorem B2227643 : Blo 988596 2227643 := bstep (se 1 (by rfl) ⟨1670732, by rfl⟩ : syracuseStep 2227643 = 3341465) B3341465
theorem B34274831 : Blo 988596 34274831 := bstep (se 1 (by rfl) ⟨25706123, by rfl⟩ : syracuseStep 34274831 = 51412247) B51412247
theorem B2227769 : Blo 988596 2227769 := bstep (se 2 (by rfl) ⟨835413, by rfl⟩ : syracuseStep 2227769 = 1670827) B1670827
theorem B11271797 : Blo 988596 11271797 := bstep (se 5 (by rfl) ⟨528365, by rfl⟩ : syracuseStep 11271797 = 1056731) B1056731
theorem B1408747 : Blo 988596 1408747 := bstep (se 1 (by rfl) ⟨1056560, by rfl⟩ : syracuseStep 1408747 = 2113121) B2113121
theorem B3342059 : Blo 988596 3342059 := bstep (se 1 (by rfl) ⟨2506544, by rfl⟩ : syracuseStep 3342059 = 5013089) B5013089
theorem B5013251 : Blo 988596 5013251 := bstep (se 1 (by rfl) ⟨3759938, by rfl⟩ : syracuseStep 5013251 = 7519877) B7519877
theorem B1670969 : Blo 988596 1670969 := bstep (se 2 (by rfl) ⟨626613, by rfl⟩ : syracuseStep 1670969 = 1253227) B1253227
theorem B1114087 : Blo 988596 1114087 := bstep (se 1 (by rfl) ⟨835565, by rfl⟩ : syracuseStep 1114087 = 1671131) B1671131
theorem B12058631 : Blo 988596 12058631 := bstep (se 1 (by rfl) ⟨9043973, by rfl⟩ : syracuseStep 12058631 = 18087947) B18087947
theorem B3768353 : Blo 988596 3768353 := bstep (se 2 (by rfl) ⟨1413132, by rfl⟩ : syracuseStep 3768353 = 2826265) B2826265
theorem B3768551 : Blo 988596 3768551 := bstep (se 1 (by rfl) ⟨2826413, by rfl⟩ : syracuseStep 3768551 = 5652827) B5652827
theorem B1671455 : Blo 988596 1671455 := bstep (se 1 (by rfl) ⟨1253591, by rfl⟩ : syracuseStep 1671455 = 2507183) B2507183
theorem B2228687 : Blo 988596 2228687 := bstep (se 1 (by rfl) ⟨1671515, by rfl⟩ : syracuseStep 2228687 = 3343031) B3343031
theorem B2818633 : Blo 988596 2818633 := bstep (se 2 (by rfl) ⟨1056987, by rfl⟩ : syracuseStep 2818633 = 2113975) B2113975
theorem B3342977 : Blo 988596 3342977 := bstep (se 2 (by rfl) ⟨1253616, by rfl⟩ : syracuseStep 3342977 = 2507233) B2507233
theorem B3343247 : Blo 988596 3343247 := bstep (se 1 (by rfl) ⟨2507435, by rfl⟩ : syracuseStep 3343247 = 5014871) B5014871
theorem B1672103 : Blo 988596 1672103 := bstep (se 1 (by rfl) ⟨1254077, by rfl⟩ : syracuseStep 1672103 = 2508155) B2508155
theorem B1115131 : Blo 988596 1115131 := bstep (se 1 (by rfl) ⟨836348, by rfl⟩ : syracuseStep 1115131 = 1672697) B1672697
theorem B1672265 : Blo 988596 1672265 := bstep (se 2 (by rfl) ⟨627099, by rfl⟩ : syracuseStep 1672265 = 1254199) B1254199
theorem B2229353 : Blo 988596 2229353 := bstep (se 2 (by rfl) ⟨836007, by rfl⟩ : syracuseStep 2229353 = 1672015) B1672015
theorem B1115311 : Blo 988596 1115311 := bstep (se 1 (by rfl) ⟨836483, by rfl⟩ : syracuseStep 1115311 = 1672967) B1672967
theorem B12879107 : Blo 988596 12879107 := bstep (se 1 (by rfl) ⟨9659330, by rfl⟩ : syracuseStep 12879107 = 19318661) B19318661
theorem B3343787 : Blo 988596 3343787 := bstep (se 1 (by rfl) ⟨2507840, by rfl⟩ : syracuseStep 3343787 = 5015681) B5015681
theorem B12027487 : Blo 988596 12027487 := bstep (se 1 (by rfl) ⟨9020615, by rfl⟩ : syracuseStep 12027487 = 18041231) B18041231
theorem B1672825 : Blo 988596 1672825 := bstep (se 2 (by rfl) ⟨627309, by rfl⟩ : syracuseStep 1672825 = 1254619) B1254619
theorem B1115815 : Blo 988596 1115815 := bstep (se 1 (by rfl) ⟨836861, by rfl⟩ : syracuseStep 1115815 = 1673723) B1673723
theorem B2229983 : Blo 988596 2229983 := bstep (se 1 (by rfl) ⟨1672487, by rfl⟩ : syracuseStep 2229983 = 3344975) B3344975
theorem B5015357 : Blo 988596 5015357 := bstep (se 3 (by rfl) ⟨940379, by rfl⟩ : syracuseStep 5015357 = 1880759) B1880759
theorem B5637995 : Blo 988596 5637995 := bstep (se 1 (by rfl) ⟨4228496, by rfl⟩ : syracuseStep 5637995 = 8456993) B8456993
theorem B3344327 : Blo 988596 3344327 := bstep (se 1 (by rfl) ⟨2508245, by rfl⟩ : syracuseStep 3344327 = 5016491) B5016491
theorem B1116103 : Blo 988596 1116103 := bstep (se 1 (by rfl) ⟨837077, by rfl⟩ : syracuseStep 1116103 = 1674155) B1674155
theorem B1673311 : Blo 988596 1673311 := bstep (se 1 (by rfl) ⟨1254983, by rfl⟩ : syracuseStep 1673311 = 2509967) B2509967
theorem B6359249 : Blo 988596 6359249 := bstep (se 2 (by rfl) ⟨2384718, by rfl⟩ : syracuseStep 6359249 = 4769437) B4769437
theorem B1116463 : Blo 988596 1116463 := bstep (se 1 (by rfl) ⟨837347, by rfl⟩ : syracuseStep 1116463 = 1674695) B1674695
theorem B2820491 : Blo 988596 2820491 := bstep (se 1 (by rfl) ⟨2115368, by rfl⟩ : syracuseStep 2820491 = 4230737) B4230737
theorem B14256643 : Blo 988596 14256643 := bstep (se 1 (by rfl) ⟨10692482, by rfl⟩ : syracuseStep 14256643 = 21384965) B21384965
theorem B2230811 : Blo 988596 2230811 := bstep (se 1 (by rfl) ⟨1673108, by rfl⟩ : syracuseStep 2230811 = 3346217) B3346217
theorem B4229779 : Blo 988596 4229779 := bstep (se 1 (by rfl) ⟨3172334, by rfl⟩ : syracuseStep 4229779 = 6344669) B6344669
theorem B3345083 : Blo 988596 3345083 := bstep (se 1 (by rfl) ⟨2508812, by rfl⟩ : syracuseStep 3345083 = 5017625) B5017625
theorem B1411931 : Blo 988596 1411931 := bstep (se 1 (by rfl) ⟨1058948, by rfl⟩ : syracuseStep 1411931 = 2117897) B2117897
theorem B4754675 : Blo 988596 4754675 := bstep (se 1 (by rfl) ⟨3566006, by rfl⟩ : syracuseStep 4754675 = 7132013) B7132013
theorem B1674607 : Blo 988596 1674607 := bstep (se 1 (by rfl) ⟨1255955, by rfl⟩ : syracuseStep 1674607 = 2511911) B2511911
theorem B38145653 : Blo 988596 38145653 := bstep (se 5 (by rfl) ⟨1788077, by rfl⟩ : syracuseStep 38145653 = 3576155) B3576155
theorem B1674985 : Blo 988596 1674985 := bstep (se 2 (by rfl) ⟨628119, by rfl⟩ : syracuseStep 1674985 = 1256239) B1256239
theorem B1806119 : Blo 988596 1806119 := bstep (se 1 (by rfl) ⟨1354589, by rfl⟩ : syracuseStep 1806119 = 2709179) B2709179
theorem B2232287 : Blo 988596 2232287 := bstep (se 1 (by rfl) ⟨1674215, by rfl⟩ : syracuseStep 2232287 = 3348431) B3348431
theorem B5017787 : Blo 988596 5017787 := bstep (se 1 (by rfl) ⟨3763340, by rfl⟩ : syracuseStep 5017787 = 7526681) B7526681
theorem B3347027 : Blo 988596 3347027 := bstep (se 1 (by rfl) ⟨2510270, by rfl⟩ : syracuseStep 3347027 = 5020541) B5020541
theorem B1610335 : Blo 988596 1610335 := bstep (se 1 (by rfl) ⟨1207751, by rfl⟩ : syracuseStep 1610335 = 2415503) B2415503
theorem B2232935 : Blo 988596 2232935 := bstep (se 1 (by rfl) ⟨1674701, by rfl⟩ : syracuseStep 2232935 = 3349403) B3349403
theorem B5018273 : Blo 988596 5018273 := bstep (se 2 (by rfl) ⟨1881852, by rfl⟩ : syracuseStep 5018273 = 3763705) B3763705
theorem B3576617 : Blo 988596 3576617 := bstep (se 2 (by rfl) ⟨1341231, by rfl⟩ : syracuseStep 3576617 = 2682463) B2682463
theorem B5018435 : Blo 988596 5018435 := bstep (se 1 (by rfl) ⟨3763826, by rfl⟩ : syracuseStep 5018435 = 7527653) B7527653
theorem B9507779 : Blo 988596 9507779 := bstep (se 1 (by rfl) ⟨7130834, by rfl⟩ : syracuseStep 9507779 = 14261669) B14261669
theorem B3347675 : Blo 988596 3347675 := bstep (se 1 (by rfl) ⟨2510756, by rfl⟩ : syracuseStep 3347675 = 5021513) B5021513
theorem B2823623 : Blo 988596 2823623 := bstep (se 1 (by rfl) ⟨2117717, by rfl⟩ : syracuseStep 2823623 = 4235435) B4235435
theorem B5019245 : Blo 988596 5019245 := bstep (se 3 (by rfl) ⟨941108, by rfl⟩ : syracuseStep 5019245 = 1882217) B1882217
theorem B988783 : Blo 988596 988783 := bstep (se 1 (by rfl) ⟨741587, by rfl⟩ : syracuseStep 988783 = 1483175) B1483175
theorem B988839 : Blo 988596 988839 := bstep (se 1 (by rfl) ⟨741629, by rfl⟩ : syracuseStep 988839 = 1483259) B1483259
theorem B988923 : Blo 988596 988923 := bstep (se 1 (by rfl) ⟨741692, by rfl⟩ : syracuseStep 988923 = 1483385) B1483385
theorem B988959 : Blo 988596 988959 := bstep (se 1 (by rfl) ⟨741719, by rfl⟩ : syracuseStep 988959 = 1483439) B1483439
theorem B988991 : Blo 988596 988991 := bstep (se 1 (by rfl) ⟨741743, by rfl⟩ : syracuseStep 988991 = 1483487) B1483487
theorem B989167 : Blo 988596 989167 := bstep (se 1 (by rfl) ⟨741875, by rfl⟩ : syracuseStep 989167 = 1483751) B1483751
theorem B7247855 : Blo 988596 7247855 := bstep (se 1 (by rfl) ⟨5435891, by rfl⟩ : syracuseStep 7247855 = 10871783) B10871783
theorem B3348539 : Blo 988596 3348539 := bstep (se 1 (by rfl) ⟨2511404, by rfl⟩ : syracuseStep 3348539 = 5022809) B5022809
theorem B5642369 : Blo 988596 5642369 := bstep (se 2 (by rfl) ⟨2115888, by rfl⟩ : syracuseStep 5642369 = 4231777) B4231777
theorem B989339 : Blo 988596 989339 := bstep (se 1 (by rfl) ⟨742004, by rfl⟩ : syracuseStep 989339 = 1484009) B1484009
theorem B989375 : Blo 988596 989375 := bstep (se 1 (by rfl) ⟨742031, by rfl⟩ : syracuseStep 989375 = 1484063) B1484063
theorem B5347625 : Blo 988596 5347625 := bstep (se 2 (by rfl) ⟨2005359, by rfl⟩ : syracuseStep 5347625 = 4010719) B4010719
theorem B989487 : Blo 988596 989487 := bstep (se 1 (by rfl) ⟨742115, by rfl⟩ : syracuseStep 989487 = 1484231) B1484231
theorem B3348809 : Blo 988596 3348809 := bstep (se 2 (by rfl) ⟨1255803, by rfl⟩ : syracuseStep 3348809 = 2511607) B2511607
theorem B989723 : Blo 988596 989723 := bstep (se 1 (by rfl) ⟨742292, by rfl⟩ : syracuseStep 989723 = 1484585) B1484585
theorem B989727 : Blo 988596 989727 := bstep (se 1 (by rfl) ⟨742295, by rfl⟩ : syracuseStep 989727 = 1484591) B1484591
theorem B990043 : Blo 988596 990043 := bstep (se 1 (by rfl) ⟨742532, by rfl⟩ : syracuseStep 990043 = 1485065) B1485065
theorem B1252255 : Blo 988596 1252255 := bstep (se 1 (by rfl) ⟨939191, by rfl⟩ : syracuseStep 1252255 = 1878383) B1878383
theorem B990111 : Blo 988596 990111 := bstep (se 1 (by rfl) ⟨742583, by rfl⟩ : syracuseStep 990111 = 1485167) B1485167
theorem B9640961 : Blo 988596 9640961 := bstep (se 2 (by rfl) ⟨3615360, by rfl⟩ : syracuseStep 9640961 = 7230721) B7230721
theorem B990255 : Blo 988596 990255 := bstep (se 1 (by rfl) ⟨742691, by rfl⟩ : syracuseStep 990255 = 1485383) B1485383
theorem B990279 : Blo 988596 990279 := bstep (se 1 (by rfl) ⟨742709, by rfl⟩ : syracuseStep 990279 = 1485419) B1485419
theorem B5348537 : Blo 988596 5348537 := bstep (se 2 (by rfl) ⟨2005701, by rfl⟩ : syracuseStep 5348537 = 4011403) B4011403
theorem B990431 : Blo 988596 990431 := bstep (se 1 (by rfl) ⟨742823, by rfl⟩ : syracuseStep 990431 = 1485647) B1485647
theorem B990695 : Blo 988596 990695 := bstep (se 1 (by rfl) ⟨743021, by rfl⟩ : syracuseStep 990695 = 1486043) B1486043
theorem B990811 : Blo 988596 990811 := bstep (se 1 (by rfl) ⟨743108, by rfl⟩ : syracuseStep 990811 = 1486217) B1486217
theorem B9051857 : Blo 988596 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B3383009 : Blo 988596 3383009 := bstep (se 2 (by rfl) ⟨1268628, by rfl⟩ : syracuseStep 3383009 = 2537257) B2537257
theorem B5644079 : Blo 988596 5644079 := bstep (se 1 (by rfl) ⟨4233059, by rfl⟩ : syracuseStep 5644079 = 8466119) B8466119
theorem B991047 : Blo 988596 991047 := bstep (se 1 (by rfl) ⟨743285, by rfl⟩ : syracuseStep 991047 = 1486571) B1486571
theorem B3022715 : Blo 988596 3022715 := bstep (se 1 (by rfl) ⟨2267036, by rfl⟩ : syracuseStep 3022715 = 4534073) B4534073
theorem B991199 : Blo 988596 991199 := bstep (se 1 (by rfl) ⟨743399, by rfl⟩ : syracuseStep 991199 = 1486799) B1486799
theorem B8462393 : Blo 988596 8462393 := bstep (se 2 (by rfl) ⟨3173397, by rfl⟩ : syracuseStep 8462393 = 6346795) B6346795
theorem B4235399 : Blo 988596 4235399 := bstep (se 1 (by rfl) ⟨3176549, by rfl⟩ : syracuseStep 4235399 = 6353099) B6353099
theorem B6791303 : Blo 988596 6791303 := bstep (se 1 (by rfl) ⟨5093477, by rfl⟩ : syracuseStep 6791303 = 10186955) B10186955
theorem B1482971 : Blo 988596 1482971 := bstep (se 1 (by rfl) ⟨1112228, by rfl⟩ : syracuseStep 1482971 = 2224457) B2224457
theorem B1482983 : Blo 988596 1482983 := bstep (se 1 (by rfl) ⟨1112237, by rfl⟩ : syracuseStep 1482983 = 2224475) B2224475
theorem B991463 : Blo 988596 991463 := bstep (se 1 (by rfl) ⟨743597, by rfl⟩ : syracuseStep 991463 = 1487195) B1487195
theorem B4825469 : Blo 988596 4825469 := bstep (se 3 (by rfl) ⟨904775, by rfl⟩ : syracuseStep 4825469 = 1809551) B1809551
theorem B991615 : Blo 988596 991615 := bstep (se 1 (by rfl) ⟨743711, by rfl⟩ : syracuseStep 991615 = 1487423) B1487423
theorem B1483145 : Blo 988596 1483145 := bstep (se 2 (by rfl) ⟨556179, by rfl⟩ : syracuseStep 1483145 = 1112359) B1112359
theorem B991695 : Blo 988596 991695 := bstep (se 1 (by rfl) ⟨743771, by rfl⟩ : syracuseStep 991695 = 1487543) B1487543
theorem B1483241 : Blo 988596 1483241 := bstep (se 2 (by rfl) ⟨556215, by rfl⟩ : syracuseStep 1483241 = 1112431) B1112431
theorem B1483367 : Blo 988596 1483367 := bstep (se 1 (by rfl) ⟨1112525, by rfl⟩ : syracuseStep 1483367 = 2225051) B2225051
theorem B991847 : Blo 988596 991847 := bstep (se 1 (by rfl) ⟨743885, by rfl⟩ : syracuseStep 991847 = 1487771) B1487771
theorem B1483499 : Blo 988596 1483499 := bstep (se 1 (by rfl) ⟨1112624, by rfl⟩ : syracuseStep 1483499 = 2225249) B2225249
theorem B1483529 : Blo 988596 1483529 := bstep (se 2 (by rfl) ⟨556323, by rfl⟩ : syracuseStep 1483529 = 1112647) B1112647
theorem B1483631 : Blo 988596 1483631 := bstep (se 1 (by rfl) ⟨1112723, by rfl⟩ : syracuseStep 1483631 = 2225447) B2225447
theorem B992111 : Blo 988596 992111 := bstep (se 1 (by rfl) ⟨744083, by rfl⟩ : syracuseStep 992111 = 1488167) B1488167
theorem B992167 : Blo 988596 992167 := bstep (se 1 (by rfl) ⟨744125, by rfl⟩ : syracuseStep 992167 = 1488251) B1488251
theorem B992251 : Blo 988596 992251 := bstep (se 1 (by rfl) ⟨744188, by rfl⟩ : syracuseStep 992251 = 1488377) B1488377
theorem B1057855 : Blo 988596 1057855 := bstep (se 1 (by rfl) ⟨793391, by rfl⟩ : syracuseStep 1057855 = 1586783) B1586783
theorem B992319 : Blo 988596 992319 := bstep (se 1 (by rfl) ⟨744239, by rfl⟩ : syracuseStep 992319 = 1488479) B1488479
theorem B1483883 : Blo 988596 1483883 := bstep (se 1 (by rfl) ⟨1112912, by rfl⟩ : syracuseStep 1483883 = 2225825) B2225825
theorem B992463 : Blo 988596 992463 := bstep (se 1 (by rfl) ⟨744347, by rfl⟩ : syracuseStep 992463 = 1488695) B1488695
theorem B1484123 : Blo 988596 1484123 := bstep (se 1 (by rfl) ⟨1113092, by rfl⟩ : syracuseStep 1484123 = 2226185) B2226185
theorem B91399549 : Blo 988596 91399549 := bstep (se 3 (by rfl) ⟨17137415, by rfl⟩ : syracuseStep 91399549 = 34274831) B34274831
theorem B13575599 : Blo 988596 13575599 := bstep (se 1 (by rfl) ⟨10181699, by rfl⟩ : syracuseStep 13575599 = 20363399) B20363399
theorem B12691025 : Blo 988596 12691025 := bstep (se 2 (by rfl) ⟨4759134, by rfl⟩ : syracuseStep 12691025 = 9518269) B9518269
theorem B11282003 : Blo 988596 11282003 := bstep (se 1 (by rfl) ⟨8461502, by rfl⟩ : syracuseStep 11282003 = 16923005) B16923005
theorem B1484399 : Blo 988596 1484399 := bstep (se 1 (by rfl) ⟨1113299, by rfl⟩ : syracuseStep 1484399 = 2226599) B2226599
theorem B1484471 : Blo 988596 1484471 := bstep (se 1 (by rfl) ⟨1113353, by rfl⟩ : syracuseStep 1484471 = 2226707) B2226707
theorem B1484507 : Blo 988596 1484507 := bstep (se 1 (by rfl) ⟨1113380, by rfl⟩ : syracuseStep 1484507 = 2226761) B2226761
theorem B3221345 : Blo 988596 3221345 := bstep (se 2 (by rfl) ⟨1208004, by rfl⟩ : syracuseStep 3221345 = 2416009) B2416009
theorem B28977029 : Blo 988596 28977029 := bstep (se 4 (by rfl) ⟨2716596, by rfl⟩ : syracuseStep 28977029 = 5433193) B5433193
theorem B1484681 : Blo 988596 1484681 := bstep (se 2 (by rfl) ⟨556755, by rfl⟩ : syracuseStep 1484681 = 1113511) B1113511
theorem B1484783 : Blo 988596 1484783 := bstep (se 1 (by rfl) ⟨1113587, by rfl⟩ : syracuseStep 1484783 = 2227175) B2227175
theorem B12855449 : Blo 988596 12855449 := bstep (se 2 (by rfl) ⟨4820793, by rfl⟩ : syracuseStep 12855449 = 9641587) B9641587
theorem B1485035 : Blo 988596 1485035 := bstep (se 1 (by rfl) ⟨1113776, by rfl⟩ : syracuseStep 1485035 = 2227553) B2227553
theorem B1485095 : Blo 988596 1485095 := bstep (se 1 (by rfl) ⟨1113821, by rfl⟩ : syracuseStep 1485095 = 2227643) B2227643
theorem B1878329 : Blo 988596 1878329 := bstep (se 2 (by rfl) ⟨704373, by rfl⟩ : syracuseStep 1878329 = 1408747) B1408747
theorem B1485179 : Blo 988596 1485179 := bstep (se 1 (by rfl) ⟨1113884, by rfl⟩ : syracuseStep 1485179 = 2227769) B2227769
theorem B7514531 : Blo 988596 7514531 := bstep (se 1 (by rfl) ⟨5635898, by rfl⟩ : syracuseStep 7514531 = 11271797) B11271797
theorem B1485449 : Blo 988596 1485449 := bstep (se 2 (by rfl) ⟨557043, by rfl⟩ : syracuseStep 1485449 = 1114087) B1114087
theorem B1485623 : Blo 988596 1485623 := bstep (se 1 (by rfl) ⟨1114217, by rfl⟩ : syracuseStep 1485623 = 2228435) B2228435
theorem B1485659 : Blo 988596 1485659 := bstep (se 1 (by rfl) ⟨1114244, by rfl⟩ : syracuseStep 1485659 = 2228489) B2228489
theorem B3058651 : Blo 988596 3058651 := bstep (se 1 (by rfl) ⟨2293988, by rfl⟩ : syracuseStep 3058651 = 4587977) B4587977
theorem B1485803 : Blo 988596 1485803 := bstep (se 1 (by rfl) ⟨1114352, by rfl⟩ : syracuseStep 1485803 = 2228705) B2228705
theorem B1486007 : Blo 988596 1486007 := bstep (se 1 (by rfl) ⟨1114505, by rfl⟩ : syracuseStep 1486007 = 2229011) B2229011
theorem B1486247 : Blo 988596 1486247 := bstep (se 1 (by rfl) ⟨1114685, by rfl⟩ : syracuseStep 1486247 = 2229371) B2229371
theorem B1486331 : Blo 988596 1486331 := bstep (se 1 (by rfl) ⟨1114748, by rfl⟩ : syracuseStep 1486331 = 2229497) B2229497
theorem B1486427 : Blo 988596 1486427 := bstep (se 1 (by rfl) ⟨1114820, by rfl⟩ : syracuseStep 1486427 = 2229641) B2229641
theorem B1486511 : Blo 988596 1486511 := bstep (se 1 (by rfl) ⟨1114883, by rfl⟩ : syracuseStep 1486511 = 2229767) B2229767
theorem B1486631 : Blo 988596 1486631 := bstep (se 1 (by rfl) ⟨1114973, by rfl⟩ : syracuseStep 1486631 = 2229947) B2229947
theorem B3616633 : Blo 988596 3616633 := bstep (se 2 (by rfl) ⟨1356237, by rfl⟩ : syracuseStep 3616633 = 2712475) B2712475
theorem B1486715 : Blo 988596 1486715 := bstep (se 1 (by rfl) ⟨1115036, by rfl⟩ : syracuseStep 1486715 = 2230073) B2230073
theorem B32157647 : Blo 988596 32157647 := bstep (se 1 (by rfl) ⟨24118235, by rfl⟩ : syracuseStep 32157647 = 48236471) B48236471
theorem B1487135 : Blo 988596 1487135 := bstep (se 1 (by rfl) ⟨1115351, by rfl⟩ : syracuseStep 1487135 = 2230703) B2230703
theorem B1487159 : Blo 988596 1487159 := bstep (se 1 (by rfl) ⟨1115369, by rfl⟩ : syracuseStep 1487159 = 2230739) B2230739
theorem B1487231 : Blo 988596 1487231 := bstep (se 1 (by rfl) ⟨1115423, by rfl⟩ : syracuseStep 1487231 = 2230847) B2230847
theorem B1487303 : Blo 988596 1487303 := bstep (se 1 (by rfl) ⟨1115477, by rfl⟩ : syracuseStep 1487303 = 2230955) B2230955
theorem B7516961 : Blo 988596 7516961 := bstep (se 2 (by rfl) ⟨2818860, by rfl⟩ : syracuseStep 7516961 = 5637721) B5637721
theorem B1487657 : Blo 988596 1487657 := bstep (se 2 (by rfl) ⟨557871, by rfl⟩ : syracuseStep 1487657 = 1115743) B1115743
theorem B1487663 : Blo 988596 1487663 := bstep (se 1 (by rfl) ⟨1115747, by rfl⟩ : syracuseStep 1487663 = 2231495) B2231495
theorem B1487783 : Blo 988596 1487783 := bstep (se 1 (by rfl) ⟨1115837, by rfl⟩ : syracuseStep 1487783 = 2231675) B2231675
theorem B1487867 : Blo 988596 1487867 := bstep (se 1 (by rfl) ⟨1115900, by rfl⟩ : syracuseStep 1487867 = 2231801) B2231801
theorem B1487927 : Blo 988596 1487927 := bstep (se 1 (by rfl) ⟨1115945, by rfl⟩ : syracuseStep 1487927 = 2231891) B2231891
theorem B1488047 : Blo 988596 1488047 := bstep (se 1 (by rfl) ⟨1116035, by rfl⟩ : syracuseStep 1488047 = 2232071) B2232071
theorem B2536795 : Blo 988596 2536795 := bstep (se 1 (by rfl) ⟨1902596, by rfl⟩ : syracuseStep 2536795 = 3805193) B3805193
theorem B1488455 : Blo 988596 1488455 := bstep (se 1 (by rfl) ⟨1116341, by rfl⟩ : syracuseStep 1488455 = 2232683) B2232683
theorem B1488551 : Blo 988596 1488551 := bstep (se 1 (by rfl) ⟨1116413, by rfl⟩ : syracuseStep 1488551 = 2232827) B2232827
theorem B2537131 : Blo 988596 2537131 := bstep (se 1 (by rfl) ⟨1902848, by rfl⟩ : syracuseStep 2537131 = 3805697) B3805697
theorem B1488635 : Blo 988596 1488635 := bstep (se 1 (by rfl) ⟨1116476, by rfl⟩ : syracuseStep 1488635 = 2232953) B2232953
theorem B1488671 : Blo 988596 1488671 := bstep (se 1 (by rfl) ⟨1116503, by rfl⟩ : syracuseStep 1488671 = 2233007) B2233007
theorem B1488719 : Blo 988596 1488719 := bstep (se 1 (by rfl) ⟨1116539, by rfl⟩ : syracuseStep 1488719 = 2233079) B2233079
theorem B11286377 : Blo 988596 11286377 := bstep (se 2 (by rfl) ⟨4232391, by rfl⟩ : syracuseStep 11286377 = 8464783) B8464783
theorem B1488839 : Blo 988596 1488839 := bstep (se 1 (by rfl) ⟨1116629, by rfl⟩ : syracuseStep 1488839 = 2233259) B2233259
theorem B10173151 : Blo 988596 10173151 := bstep (se 1 (by rfl) ⟨7629863, by rfl⟩ : syracuseStep 10173151 = 15259727) B15259727
theorem B2505563 : Blo 988596 2505563 := bstep (se 1 (by rfl) ⟨1879172, by rfl⟩ : syracuseStep 2505563 = 3758345) B3758345
theorem B1129375 : Blo 988596 1129375 := bstep (se 1 (by rfl) ⟨847031, by rfl⟩ : syracuseStep 1129375 = 1694063) B1694063
theorem B6962129 : Blo 988596 6962129 := bstep (se 2 (by rfl) ⟨2610798, by rfl⟩ : syracuseStep 6962129 = 5221597) B5221597
theorem B4013479 : Blo 988596 4013479 := bstep (se 1 (by rfl) ⟨3010109, by rfl⟩ : syracuseStep 4013479 = 6020219) B6020219
theorem B1883873 : Blo 988596 1883873 := bstep (se 2 (by rfl) ⟨706452, by rfl⟩ : syracuseStep 1883873 = 1412905) B1412905
theorem B8045119 : Blo 988596 8045119 := bstep (se 1 (by rfl) ⟨6033839, by rfl⟩ : syracuseStep 8045119 = 12067679) B12067679
theorem B2114351 : Blo 988596 2114351 := bstep (se 1 (by rfl) ⟨1585763, by rfl⟩ : syracuseStep 2114351 = 3171527) B3171527
theorem B2507881 : Blo 988596 2507881 := bstep (se 2 (by rfl) ⟨940455, by rfl⟩ : syracuseStep 2507881 = 1880911) B1880911
theorem B12404111 : Blo 988596 12404111 := bstep (se 1 (by rfl) ⟨9303083, by rfl⟩ : syracuseStep 12404111 = 18606167) B18606167
theorem B10864151 : Blo 988596 10864151 := bstep (se 1 (by rfl) ⟨8148113, by rfl⟩ : syracuseStep 10864151 = 16296227) B16296227
theorem B2115239 : Blo 988596 2115239 := bstep (se 1 (by rfl) ⟨1586429, by rfl⟩ : syracuseStep 2115239 = 3172859) B3172859
theorem B1787611 : Blo 988596 1787611 := bstep (se 1 (by rfl) ⟨1340708, by rfl⟩ : syracuseStep 1787611 = 2681417) B2681417
theorem B2508641 : Blo 988596 2508641 := bstep (se 2 (by rfl) ⟨940740, by rfl⟩ : syracuseStep 2508641 = 1881481) B1881481
theorem B27510961 : Blo 988596 27510961 := bstep (se 2 (by rfl) ⟨10316610, by rfl⟩ : syracuseStep 27510961 = 20633221) B20633221
theorem B2509015 : Blo 988596 2509015 := bstep (se 1 (by rfl) ⟨1881761, by rfl⟩ : syracuseStep 2509015 = 3763523) B3763523
theorem B2148665 : Blo 988596 2148665 := bstep (se 2 (by rfl) ⟨805749, by rfl⟩ : syracuseStep 2148665 = 1611499) B1611499
theorem B2509319 : Blo 988596 2509319 := bstep (se 1 (by rfl) ⟨1881989, by rfl⟩ : syracuseStep 2509319 = 3763979) B3763979
theorem B2509339 : Blo 988596 2509339 := bstep (se 1 (by rfl) ⟨1882004, by rfl⟩ : syracuseStep 2509339 = 3764009) B3764009
theorem B96356897 : Blo 988596 96356897 := bstep (se 2 (by rfl) ⟨36133836, by rfl⟩ : syracuseStep 96356897 = 72267673) B72267673
theorem B6343667 : Blo 988596 6343667 := bstep (se 1 (by rfl) ⟨4757750, by rfl⟩ : syracuseStep 6343667 = 9515501) B9515501
theorem B3755231 : Blo 988596 3755231 := bstep (se 1 (by rfl) ⟨2816423, by rfl⟩ : syracuseStep 3755231 = 5632847) B5632847
theorem B2379559 : Blo 988596 2379559 := bstep (se 1 (by rfl) ⟨1784669, by rfl⟩ : syracuseStep 2379559 = 3569339) B3569339
theorem B8474489 : Blo 988596 8474489 := bstep (se 2 (by rfl) ⟨3177933, by rfl⟩ : syracuseStep 8474489 = 6355867) B6355867
theorem B2510747 : Blo 988596 2510747 := bstep (se 1 (by rfl) ⟨1883060, by rfl⟩ : syracuseStep 2510747 = 3766121) B3766121
theorem B3756415 : Blo 988596 3756415 := bstep (se 1 (by rfl) ⟨2817311, by rfl⟩ : syracuseStep 3756415 = 5634623) B5634623
theorem B100192697 : Blo 988596 100192697 := bstep (se 2 (by rfl) ⟨37572261, by rfl⟩ : syracuseStep 100192697 = 75144523) B75144523
theorem B2511881 : Blo 988596 2511881 := bstep (se 2 (by rfl) ⟨941955, by rfl⟩ : syracuseStep 2511881 = 1883911) B1883911
theorem B6116705 : Blo 988596 6116705 := bstep (se 2 (by rfl) ⟨2293764, by rfl⟩ : syracuseStep 6116705 = 4587529) B4587529
theorem B9164411 : Blo 988596 9164411 := bstep (se 1 (by rfl) ⟨6873308, by rfl⟩ : syracuseStep 9164411 = 13746617) B13746617
theorem B27121397 : Blo 988596 27121397 := bstep (se 5 (by rfl) ⟨1271315, by rfl⟩ : syracuseStep 27121397 = 2542631) B2542631
theorem B6773021 : Blo 988596 6773021 := bstep (se 3 (by rfl) ⟨1269941, by rfl⟩ : syracuseStep 6773021 = 2539883) B2539883
theorem B3168553 : Blo 988596 3168553 := bstep (se 2 (by rfl) ⟨1188207, by rfl⟩ : syracuseStep 3168553 = 2376415) B2376415
theorem B7133629 : Blo 988596 7133629 := bstep (se 3 (by rfl) ⟨1337555, by rfl⟩ : syracuseStep 7133629 = 2675111) B2675111
theorem B6773345 : Blo 988596 6773345 := bstep (se 2 (by rfl) ⟨2540004, by rfl⟩ : syracuseStep 6773345 = 5080009) B5080009
theorem B2382817 : Blo 988596 2382817 := bstep (se 2 (by rfl) ⟨893556, by rfl⟩ : syracuseStep 2382817 = 1787113) B1787113
theorem B3169631 : Blo 988596 3169631 := bstep (se 1 (by rfl) ⟨2377223, by rfl⟩ : syracuseStep 3169631 = 4754447) B4754447
theorem B11296583 : Blo 988596 11296583 := bstep (se 1 (by rfl) ⟨8472437, by rfl⟩ : syracuseStep 11296583 = 16944875) B16944875
theorem B10838681 : Blo 988596 10838681 := bstep (se 2 (by rfl) ⟨4064505, by rfl⟩ : syracuseStep 10838681 = 8129011) B8129011
theorem B2679599 : Blo 988596 2679599 := bstep (se 1 (by rfl) ⟨2009699, by rfl⟩ : syracuseStep 2679599 = 4019399) B4019399
theorem B3761275 : Blo 988596 3761275 := bstep (se 1 (by rfl) ⟨2820956, by rfl⟩ : syracuseStep 3761275 = 5641913) B5641913
theorem B12870829 : Blo 988596 12870829 := bstep (se 3 (by rfl) ⟨2413280, by rfl⟩ : syracuseStep 12870829 = 4826561) B4826561
theorem B3564971 : Blo 988596 3564971 := bstep (se 1 (by rfl) ⟨2673728, by rfl⟩ : syracuseStep 3564971 = 5347457) B5347457
theorem B3761747 : Blo 988596 3761747 := bstep (se 1 (by rfl) ⟨2821310, by rfl⟩ : syracuseStep 3761747 = 5642621) B5642621
theorem B6022943 : Blo 988596 6022943 := bstep (se 1 (by rfl) ⟨4517207, by rfl⟩ : syracuseStep 6022943 = 9034415) B9034415
theorem B27813719 : Blo 988596 27813719 := bstep (se 1 (by rfl) ⟨20860289, by rfl⟩ : syracuseStep 27813719 = 41720579) B41720579
theorem B3172193 : Blo 988596 3172193 := bstep (se 2 (by rfl) ⟨1189572, by rfl⟩ : syracuseStep 3172193 = 2379145) B2379145
theorem B3336605 : Blo 988596 3336605 := bstep (se 3 (by rfl) ⟨625613, by rfl⟩ : syracuseStep 3336605 = 1251227) B1251227
theorem B10840481 : Blo 988596 10840481 := bstep (se 2 (by rfl) ⟨4065180, by rfl⟩ : syracuseStep 10840481 = 8130361) B8130361
theorem B3336875 : Blo 988596 3336875 := bstep (se 1 (by rfl) ⟨2502656, by rfl⟩ : syracuseStep 3336875 = 5005313) B5005313
theorem B57863099 : Blo 988596 57863099 := bstep (se 1 (by rfl) ⟨43397324, by rfl⟩ : syracuseStep 57863099 = 86794649) B86794649
theorem B5008391 : Blo 988596 5008391 := bstep (se 1 (by rfl) ⟨3756293, by rfl⟩ : syracuseStep 5008391 = 7512587) B7512587
theorem B18082835 : Blo 988596 18082835 := bstep (se 1 (by rfl) ⟨13562126, by rfl⟩ : syracuseStep 18082835 = 27124253) B27124253
theorem B3337415 : Blo 988596 3337415 := bstep (se 1 (by rfl) ⟨2503061, by rfl⟩ : syracuseStep 3337415 = 5006123) B5006123
theorem B4287853 : Blo 988596 4287853 := bstep (se 3 (by rfl) ⟨803972, by rfl⟩ : syracuseStep 4287853 = 1607945) B1607945
theorem B8580971 : Blo 988596 8580971 := bstep (se 1 (by rfl) ⟨6435728, by rfl⟩ : syracuseStep 8580971 = 12871457) B12871457
theorem B7139279 : Blo 988596 7139279 := bstep (se 1 (by rfl) ⟨5354459, by rfl⟩ : syracuseStep 7139279 = 10708919) B10708919
theorem B25391069 : Blo 988596 25391069 := bstep (se 3 (by rfl) ⟨4760825, by rfl⟩ : syracuseStep 25391069 = 9521651) B9521651
theorem B3764191 : Blo 988596 3764191 := bstep (se 1 (by rfl) ⟨2823143, by rfl⟩ : syracuseStep 3764191 = 5646287) B5646287
theorem B3174653 : Blo 988596 3174653 := bstep (se 3 (by rfl) ⟨595247, by rfl⟩ : syracuseStep 3174653 = 1190495) B1190495
theorem B2224439 : Blo 988596 2224439 := bstep (se 1 (by rfl) ⟨1668329, by rfl⟩ : syracuseStep 2224439 = 3336659) B3336659
theorem B2224511 : Blo 988596 2224511 := bstep (se 1 (by rfl) ⟨1668383, by rfl⟩ : syracuseStep 2224511 = 3336767) B3336767
theorem B3338711 : Blo 988596 3338711 := bstep (se 1 (by rfl) ⟨2504033, by rfl⟩ : syracuseStep 3338711 = 5008067) B5008067
theorem B3765163 : Blo 988596 3765163 := bstep (se 1 (by rfl) ⟨2823872, by rfl⟩ : syracuseStep 3765163 = 5647745) B5647745
theorem B6354227 : Blo 988596 6354227 := bstep (se 1 (by rfl) ⟨4765670, by rfl⟩ : syracuseStep 6354227 = 9531341) B9531341
theorem B9532723 : Blo 988596 9532723 := bstep (se 1 (by rfl) ⟨7149542, by rfl⟩ : syracuseStep 9532723 = 14299085) B14299085
theorem B2225735 : Blo 988596 2225735 := bstep (se 1 (by rfl) ⟨1669301, by rfl⟩ : syracuseStep 2225735 = 3338603) B3338603
theorem B24802949 : Blo 988596 24802949 := bstep (se 4 (by rfl) ⟨2325276, by rfl⟩ : syracuseStep 24802949 = 4650553) B4650553
theorem B24114833 : Blo 988596 24114833 := bstep (se 2 (by rfl) ⟨9043062, by rfl⟩ : syracuseStep 24114833 = 18086125) B18086125
theorem B1668775 : Blo 988596 1668775 := bstep (se 1 (by rfl) ⟨1251581, by rfl⟩ : syracuseStep 1668775 = 2503163) B2503163
theorem B2225915 : Blo 988596 2225915 := bstep (se 1 (by rfl) ⟨1669436, by rfl⟩ : syracuseStep 2225915 = 3338873) B3338873
theorem B12678929 : Blo 988596 12678929 := bstep (se 2 (by rfl) ⟨4754598, by rfl⟩ : syracuseStep 12678929 = 9509197) B9509197
theorem B5633873 : Blo 988596 5633873 := bstep (se 2 (by rfl) ⟨2112702, by rfl⟩ : syracuseStep 5633873 = 4225405) B4225405
theorem B3340169 : Blo 988596 3340169 := bstep (se 2 (by rfl) ⟨1252563, by rfl⟩ : syracuseStep 3340169 = 2505127) B2505127
theorem B3340385 : Blo 988596 3340385 := bstep (se 2 (by rfl) ⟨1252644, by rfl⟩ : syracuseStep 3340385 = 2505289) B2505289
theorem B2226473 : Blo 988596 2226473 := bstep (se 2 (by rfl) ⟨834927, by rfl⟩ : syracuseStep 2226473 = 1669855) B1669855
theorem B1669423 : Blo 988596 1669423 := bstep (se 1 (by rfl) ⟨1252067, by rfl⟩ : syracuseStep 1669423 = 2504135) B2504135
theorem B12712301 : Blo 988596 12712301 := bstep (se 3 (by rfl) ⟨2383556, by rfl⟩ : syracuseStep 12712301 = 4767113) B4767113
theorem B1669943 : Blo 988596 1669943 := bstep (se 1 (by rfl) ⟨1252457, by rfl⟩ : syracuseStep 1669943 = 2504915) B2504915
theorem B2227049 : Blo 988596 2227049 := bstep (se 2 (by rfl) ⟨835143, by rfl⟩ : syracuseStep 2227049 = 1670287) B1670287
theorem B8452997 : Blo 988596 8452997 := bstep (se 4 (by rfl) ⟨792468, by rfl⟩ : syracuseStep 8452997 = 1584937) B1584937
theorem B2227103 : Blo 988596 2227103 := bstep (se 1 (by rfl) ⟨1670327, by rfl⟩ : syracuseStep 2227103 = 3340655) B3340655
theorem B2816993 : Blo 988596 2816993 := bstep (se 2 (by rfl) ⟨1056372, by rfl⟩ : syracuseStep 2816993 = 2112745) B2112745
theorem B3341303 : Blo 988596 3341303 := bstep (se 1 (by rfl) ⟨2505977, by rfl⟩ : syracuseStep 3341303 = 5011955) B5011955
theorem B1408223 : Blo 988596 1408223 := bstep (se 1 (by rfl) ⟨1056167, by rfl⟩ : syracuseStep 1408223 = 2112335) B2112335
theorem B5012765 : Blo 988596 5012765 := bstep (se 3 (by rfl) ⟨939893, by rfl⟩ : syracuseStep 5012765 = 1879787) B1879787
theorem B1408423 : Blo 988596 1408423 := bstep (se 1 (by rfl) ⟨1056317, by rfl⟩ : syracuseStep 1408423 = 2112635) B2112635
theorem B3341735 : Blo 988596 3341735 := bstep (se 1 (by rfl) ⟨2506301, by rfl⟩ : syracuseStep 3341735 = 5012603) B5012603
theorem B1670719 : Blo 988596 1670719 := bstep (se 1 (by rfl) ⟨1253039, by rfl⟩ : syracuseStep 1670719 = 2506079) B2506079
theorem B4226651 : Blo 988596 4226651 := bstep (se 1 (by rfl) ⟨3169988, by rfl⟩ : syracuseStep 4226651 = 6339977) B6339977
theorem B1113691 : Blo 988596 1113691 := bstep (se 1 (by rfl) ⟨835268, by rfl⟩ : syracuseStep 1113691 = 1670537) B1670537
theorem B9502433 : Blo 988596 9502433 := bstep (se 2 (by rfl) ⟨3563412, by rfl⟩ : syracuseStep 9502433 = 7126825) B7126825
theorem B3178217 : Blo 988596 3178217 := bstep (se 2 (by rfl) ⟨1191831, by rfl⟩ : syracuseStep 3178217 = 2383663) B2383663
theorem B2228039 : Blo 988596 2228039 := bstep (se 1 (by rfl) ⟨1671029, by rfl⟩ : syracuseStep 2228039 = 3342059) B3342059
theorem B3342167 : Blo 988596 3342167 := bstep (se 1 (by rfl) ⟨2506625, by rfl⟩ : syracuseStep 3342167 = 5013251) B5013251
theorem B1113979 : Blo 988596 1113979 := bstep (se 1 (by rfl) ⟨835484, by rfl⟩ : syracuseStep 1113979 = 1670969) B1670969
theorem B1114303 : Blo 988596 1114303 := bstep (se 1 (by rfl) ⟨835727, by rfl⟩ : syracuseStep 1114303 = 1671455) B1671455
theorem B2228651 : Blo 988596 2228651 := bstep (se 1 (by rfl) ⟨1671488, by rfl⟩ : syracuseStep 2228651 = 3342977) B3342977
theorem B1409567 : Blo 988596 1409567 := bstep (se 1 (by rfl) ⟨1057175, by rfl⟩ : syracuseStep 1409567 = 2114351) B2114351
theorem B2228831 : Blo 988596 2228831 := bstep (se 1 (by rfl) ⟨1671623, by rfl⟩ : syracuseStep 2228831 = 3343247) B3343247
theorem B1114735 : Blo 988596 1114735 := bstep (se 1 (by rfl) ⟨836051, by rfl⟩ : syracuseStep 1114735 = 1672103) B1672103
theorem B1114843 : Blo 988596 1114843 := bstep (se 1 (by rfl) ⟨836132, by rfl⟩ : syracuseStep 1114843 = 1672265) B1672265
theorem B8586071 : Blo 988596 8586071 := bstep (se 1 (by rfl) ⟨6439553, by rfl⟩ : syracuseStep 8586071 = 12879107) B12879107
theorem B2229191 : Blo 988596 2229191 := bstep (se 1 (by rfl) ⟨1671893, by rfl⟩ : syracuseStep 2229191 = 3343787) B3343787
theorem B7242767 : Blo 988596 7242767 := bstep (se 1 (by rfl) ⟨5432075, by rfl⟩ : syracuseStep 7242767 = 10864151) B10864151
theorem B3343571 : Blo 988596 3343571 := bstep (se 1 (by rfl) ⟨2507678, by rfl⟩ : syracuseStep 3343571 = 5015357) B5015357
theorem B1672427 : Blo 988596 1672427 := bstep (se 1 (by rfl) ⟨1254320, by rfl⟩ : syracuseStep 1672427 = 2508641) B2508641
theorem B2229551 : Blo 988596 2229551 := bstep (se 1 (by rfl) ⟨1672163, by rfl⟩ : syracuseStep 2229551 = 3344327) B3344327
theorem B1410473 : Blo 988596 1410473 := bstep (se 2 (by rfl) ⟨528927, by rfl⟩ : syracuseStep 1410473 = 1057855) B1057855
theorem B3343841 : Blo 988596 3343841 := bstep (se 2 (by rfl) ⟨1253940, by rfl⟩ : syracuseStep 3343841 = 2507881) B2507881
theorem B5015033 : Blo 988596 5015033 := bstep (se 2 (by rfl) ⟨1880637, by rfl⟩ : syracuseStep 5015033 = 3761275) B3761275
theorem B1672879 : Blo 988596 1672879 := bstep (se 1 (by rfl) ⟨1254659, by rfl⟩ : syracuseStep 1672879 = 2509319) B2509319
theorem B2230055 : Blo 988596 2230055 := bstep (se 1 (by rfl) ⟨1672541, by rfl⟩ : syracuseStep 2230055 = 3345083) B3345083
theorem B121866065 : Blo 988596 121866065 := bstep (se 2 (by rfl) ⟨45699774, by rfl⟩ : syracuseStep 121866065 = 91399549) B91399549
theorem B4229111 : Blo 988596 4229111 := bstep (se 1 (by rfl) ⟨3171833, by rfl⟩ : syracuseStep 4229111 = 6343667) B6343667
theorem B7145597 : Blo 988596 7145597 := bstep (se 3 (by rfl) ⟨1339799, by rfl⟩ : syracuseStep 7145597 = 2679599) B2679599
theorem B2230433 : Blo 988596 2230433 := bstep (se 2 (by rfl) ⟨836412, by rfl⟩ : syracuseStep 2230433 = 1672825) B1672825
theorem B25430435 : Blo 988596 25430435 := bstep (se 1 (by rfl) ⟨19072826, by rfl⟩ : syracuseStep 25430435 = 38145653) B38145653
theorem B1673831 : Blo 988596 1673831 := bstep (se 1 (by rfl) ⟨1255373, by rfl⟩ : syracuseStep 1673831 = 2510747) B2510747
theorem B3345191 : Blo 988596 3345191 := bstep (se 1 (by rfl) ⟨2508893, by rfl⟩ : syracuseStep 3345191 = 5017787) B5017787
theorem B2231081 : Blo 988596 2231081 := bstep (se 2 (by rfl) ⟨836655, by rfl⟩ : syracuseStep 2231081 = 1673311) B1673311
theorem B3345353 : Blo 988596 3345353 := bstep (se 2 (by rfl) ⟨1254507, by rfl⟩ : syracuseStep 3345353 = 2509015) B2509015
theorem B2231351 : Blo 988596 2231351 := bstep (se 1 (by rfl) ⟨1673513, by rfl⟩ : syracuseStep 2231351 = 3347027) B3347027
theorem B3345515 : Blo 988596 3345515 := bstep (se 1 (by rfl) ⟨2509136, by rfl⟩ : syracuseStep 3345515 = 5018273) B5018273
theorem B3345623 : Blo 988596 3345623 := bstep (se 1 (by rfl) ⟨2509217, by rfl⟩ : syracuseStep 3345623 = 5018435) B5018435
theorem B19008857 : Blo 988596 19008857 := bstep (se 2 (by rfl) ⟨7128321, by rfl⟩ : syracuseStep 19008857 = 14256643) B14256643
theorem B1674587 : Blo 988596 1674587 := bstep (se 1 (by rfl) ⟨1255940, by rfl⟩ : syracuseStep 1674587 = 2511881) B2511881
theorem B3345785 : Blo 988596 3345785 := bstep (se 2 (by rfl) ⟨1254669, by rfl⟩ : syracuseStep 3345785 = 2509339) B2509339
theorem B2231783 : Blo 988596 2231783 := bstep (se 1 (by rfl) ⟨1673837, by rfl⟩ : syracuseStep 2231783 = 3347675) B3347675
theorem B5639705 : Blo 988596 5639705 := bstep (se 2 (by rfl) ⟨2114889, by rfl⟩ : syracuseStep 5639705 = 4229779) B4229779
theorem B3346163 : Blo 988596 3346163 := bstep (se 1 (by rfl) ⟨2509622, by rfl⟩ : syracuseStep 3346163 = 5019245) B5019245
theorem B2232359 : Blo 988596 2232359 := bstep (se 1 (by rfl) ⟨1674269, by rfl⟩ : syracuseStep 2232359 = 3348539) B3348539
theorem B2232539 : Blo 988596 2232539 := bstep (se 1 (by rfl) ⟨1674404, by rfl⟩ : syracuseStep 2232539 = 3348809) B3348809
theorem B5640637 : Blo 988596 5640637 := bstep (se 3 (by rfl) ⟨1057619, by rfl⟩ : syracuseStep 5640637 = 2115239) B2115239
theorem B2232809 : Blo 988596 2232809 := bstep (se 2 (by rfl) ⟨837303, by rfl⟩ : syracuseStep 2232809 = 1674607) B1674607
theorem B72323725 : Blo 988596 72323725 := bstep (se 3 (by rfl) ⟨13560698, by rfl⟩ : syracuseStep 72323725 = 27121397) B27121397
theorem B6427307 : Blo 988596 6427307 := bstep (se 1 (by rfl) ⟨4820480, by rfl⟩ : syracuseStep 6427307 = 9640961) B9640961
theorem B2233313 : Blo 988596 2233313 := bstep (se 2 (by rfl) ⟨837492, by rfl⟩ : syracuseStep 2233313 = 1674985) B1674985
theorem B6034571 : Blo 988596 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B5018921 : Blo 988596 5018921 := bstep (se 2 (by rfl) ⟨1882095, by rfl⟩ : syracuseStep 5018921 = 3764191) B3764191
theorem B5641595 : Blo 988596 5641595 := bstep (se 1 (by rfl) ⟨4231196, by rfl⟩ : syracuseStep 5641595 = 8462393) B8462393
theorem B2823599 : Blo 988596 2823599 := bstep (se 1 (by rfl) ⟨2117699, by rfl⟩ : syracuseStep 2823599 = 4235399) B4235399
theorem B4527535 : Blo 988596 4527535 := bstep (se 1 (by rfl) ⟨3395651, by rfl⟩ : syracuseStep 4527535 = 6791303) B6791303
theorem B988647 : Blo 988596 988647 := bstep (se 1 (by rfl) ⟨741485, by rfl⟩ : syracuseStep 988647 = 1482971) B1482971
theorem B988655 : Blo 988596 988655 := bstep (se 1 (by rfl) ⟨741491, by rfl⟩ : syracuseStep 988655 = 1482983) B1482983
theorem B3216979 : Blo 988596 3216979 := bstep (se 1 (by rfl) ⟨2412734, by rfl⟩ : syracuseStep 3216979 = 4825469) B4825469
theorem B988763 : Blo 988596 988763 := bstep (se 1 (by rfl) ⟨741572, by rfl⟩ : syracuseStep 988763 = 1483145) B1483145
theorem B988827 : Blo 988596 988827 := bstep (se 1 (by rfl) ⟨741620, by rfl⟩ : syracuseStep 988827 = 1483241) B1483241
theorem B988911 : Blo 988596 988911 := bstep (se 1 (by rfl) ⟨741683, by rfl⟩ : syracuseStep 988911 = 1483367) B1483367
theorem B988999 : Blo 988596 988999 := bstep (se 1 (by rfl) ⟨741749, by rfl⟩ : syracuseStep 988999 = 1483499) B1483499
theorem B989019 : Blo 988596 989019 := bstep (se 1 (by rfl) ⟨741764, by rfl⟩ : syracuseStep 989019 = 1483529) B1483529
theorem B989087 : Blo 988596 989087 := bstep (se 1 (by rfl) ⟨741815, by rfl⟩ : syracuseStep 989087 = 1483631) B1483631
theorem B989255 : Blo 988596 989255 := bstep (se 1 (by rfl) ⟨741941, by rfl⟩ : syracuseStep 989255 = 1483883) B1483883
theorem B989415 : Blo 988596 989415 := bstep (se 1 (by rfl) ⟨742061, by rfl⟩ : syracuseStep 989415 = 1484123) B1484123
theorem B9050399 : Blo 988596 9050399 := bstep (se 1 (by rfl) ⟨6787799, by rfl⟩ : syracuseStep 9050399 = 13575599) B13575599
theorem B8460683 : Blo 988596 8460683 := bstep (se 1 (by rfl) ⟨6345512, by rfl⟩ : syracuseStep 8460683 = 12691025) B12691025
theorem B989599 : Blo 988596 989599 := bstep (se 1 (by rfl) ⟨742199, by rfl⟩ : syracuseStep 989599 = 1484399) B1484399
theorem B989647 : Blo 988596 989647 := bstep (se 1 (by rfl) ⟨742235, by rfl⟩ : syracuseStep 989647 = 1484471) B1484471
theorem B989671 : Blo 988596 989671 := bstep (se 1 (by rfl) ⟨742253, by rfl⟩ : syracuseStep 989671 = 1484507) B1484507
theorem B5020217 : Blo 988596 5020217 := bstep (se 2 (by rfl) ⟨1882581, by rfl⟩ : syracuseStep 5020217 = 3765163) B3765163
theorem B989787 : Blo 988596 989787 := bstep (se 1 (by rfl) ⟨742340, by rfl⟩ : syracuseStep 989787 = 1484681) B1484681
theorem B989855 : Blo 988596 989855 := bstep (se 1 (by rfl) ⟨742391, by rfl⟩ : syracuseStep 989855 = 1484783) B1484783
theorem B990023 : Blo 988596 990023 := bstep (se 1 (by rfl) ⟨742517, by rfl⟩ : syracuseStep 990023 = 1485035) B1485035
theorem B990063 : Blo 988596 990063 := bstep (se 1 (by rfl) ⟨742547, by rfl⟩ : syracuseStep 990063 = 1485095) B1485095
theorem B990119 : Blo 988596 990119 := bstep (se 1 (by rfl) ⟨742589, by rfl⟩ : syracuseStep 990119 = 1485179) B1485179
theorem B990299 : Blo 988596 990299 := bstep (se 1 (by rfl) ⟨742724, by rfl⟩ : syracuseStep 990299 = 1485449) B1485449
theorem B3382393 : Blo 988596 3382393 := bstep (se 2 (by rfl) ⟨1268397, by rfl⟩ : syracuseStep 3382393 = 2536795) B2536795
theorem B990415 : Blo 988596 990415 := bstep (se 1 (by rfl) ⟨742811, by rfl⟩ : syracuseStep 990415 = 1485623) B1485623
theorem B990439 : Blo 988596 990439 := bstep (se 1 (by rfl) ⟨742829, by rfl⟩ : syracuseStep 990439 = 1485659) B1485659
theorem B38575399 : Blo 988596 38575399 := bstep (se 1 (by rfl) ⟨28931549, by rfl⟩ : syracuseStep 38575399 = 57863099) B57863099
theorem B990535 : Blo 988596 990535 := bstep (se 1 (by rfl) ⟨742901, by rfl⟩ : syracuseStep 990535 = 1485803) B1485803
theorem B990671 : Blo 988596 990671 := bstep (se 1 (by rfl) ⟨743003, by rfl⟩ : syracuseStep 990671 = 1486007) B1486007
theorem B3382841 : Blo 988596 3382841 := bstep (se 2 (by rfl) ⟨1268565, by rfl⟩ : syracuseStep 3382841 = 2537131) B2537131
theorem B990831 : Blo 988596 990831 := bstep (se 1 (by rfl) ⟨743123, by rfl⟩ : syracuseStep 990831 = 1486247) B1486247
theorem B990887 : Blo 988596 990887 := bstep (se 1 (by rfl) ⟨743165, by rfl⟩ : syracuseStep 990887 = 1486331) B1486331
theorem B990951 : Blo 988596 990951 := bstep (se 1 (by rfl) ⟨743213, by rfl⟩ : syracuseStep 990951 = 1486427) B1486427
theorem B991007 : Blo 988596 991007 := bstep (se 1 (by rfl) ⟨743255, by rfl⟩ : syracuseStep 991007 = 1486511) B1486511
theorem B991087 : Blo 988596 991087 := bstep (se 1 (by rfl) ⟨743315, by rfl⟩ : syracuseStep 991087 = 1486631) B1486631
theorem B991143 : Blo 988596 991143 := bstep (se 1 (by rfl) ⟨743357, by rfl⟩ : syracuseStep 991143 = 1486715) B1486715
theorem B21438431 : Blo 988596 21438431 := bstep (se 1 (by rfl) ⟨16078823, by rfl⟩ : syracuseStep 21438431 = 32157647) B32157647
theorem B991423 : Blo 988596 991423 := bstep (se 1 (by rfl) ⟨743567, by rfl⟩ : syracuseStep 991423 = 1487135) B1487135
theorem B1482959 : Blo 988596 1482959 := bstep (se 1 (by rfl) ⟨1112219, by rfl⟩ : syracuseStep 1482959 = 2224439) B2224439
theorem B991439 : Blo 988596 991439 := bstep (se 1 (by rfl) ⟨743579, by rfl⟩ : syracuseStep 991439 = 1487159) B1487159
theorem B1483007 : Blo 988596 1483007 := bstep (se 1 (by rfl) ⟨1112255, by rfl⟩ : syracuseStep 1483007 = 2224511) B2224511
theorem B991487 : Blo 988596 991487 := bstep (se 1 (by rfl) ⟨743615, by rfl⟩ : syracuseStep 991487 = 1487231) B1487231
theorem B991535 : Blo 988596 991535 := bstep (se 1 (by rfl) ⟨743651, by rfl⟩ : syracuseStep 991535 = 1487303) B1487303
theorem B991771 : Blo 988596 991771 := bstep (se 1 (by rfl) ⟨743828, by rfl⟩ : syracuseStep 991771 = 1487657) B1487657
theorem B991775 : Blo 988596 991775 := bstep (se 1 (by rfl) ⟨743831, by rfl⟩ : syracuseStep 991775 = 1487663) B1487663
theorem B9511505 : Blo 988596 9511505 := bstep (se 2 (by rfl) ⟨3566814, by rfl⟩ : syracuseStep 9511505 = 7133629) B7133629
theorem B991855 : Blo 988596 991855 := bstep (se 1 (by rfl) ⟨743891, by rfl⟩ : syracuseStep 991855 = 1487783) B1487783
theorem B991911 : Blo 988596 991911 := bstep (se 1 (by rfl) ⟨743933, by rfl⟩ : syracuseStep 991911 = 1487867) B1487867
theorem B991951 : Blo 988596 991951 := bstep (se 1 (by rfl) ⟨743963, by rfl⟩ : syracuseStep 991951 = 1487927) B1487927
theorem B992031 : Blo 988596 992031 := bstep (se 1 (by rfl) ⟨744023, by rfl⟩ : syracuseStep 992031 = 1488047) B1488047
theorem B4236151 : Blo 988596 4236151 := bstep (se 1 (by rfl) ⟨3177113, by rfl⟩ : syracuseStep 4236151 = 6354227) B6354227
theorem B1483823 : Blo 988596 1483823 := bstep (se 1 (by rfl) ⟨1112867, by rfl⟩ : syracuseStep 1483823 = 2225735) B2225735
theorem B992303 : Blo 988596 992303 := bstep (se 1 (by rfl) ⟨744227, by rfl⟩ : syracuseStep 992303 = 1488455) B1488455
theorem B992367 : Blo 988596 992367 := bstep (se 1 (by rfl) ⟨744275, by rfl⟩ : syracuseStep 992367 = 1488551) B1488551
theorem B1483943 : Blo 988596 1483943 := bstep (se 1 (by rfl) ⟨1112957, by rfl⟩ : syracuseStep 1483943 = 2225915) B2225915
theorem B992423 : Blo 988596 992423 := bstep (se 1 (by rfl) ⟨744317, by rfl⟩ : syracuseStep 992423 = 1488635) B1488635
theorem B992447 : Blo 988596 992447 := bstep (se 1 (by rfl) ⟨744335, by rfl⟩ : syracuseStep 992447 = 1488671) B1488671
theorem B992479 : Blo 988596 992479 := bstep (se 1 (by rfl) ⟨744359, by rfl⟩ : syracuseStep 992479 = 1488719) B1488719
theorem B992559 : Blo 988596 992559 := bstep (se 1 (by rfl) ⟨744419, by rfl⟩ : syracuseStep 992559 = 1488839) B1488839
theorem B1484315 : Blo 988596 1484315 := bstep (se 1 (by rfl) ⟨1113236, by rfl⟩ : syracuseStep 1484315 = 2226473) B2226473
theorem B1877897 : Blo 988596 1877897 := bstep (se 2 (by rfl) ⟨704211, by rfl⟩ : syracuseStep 1877897 = 1408423) B1408423
theorem B5351305 : Blo 988596 5351305 := bstep (se 2 (by rfl) ⟨2006739, by rfl⟩ : syracuseStep 5351305 = 4013479) B4013479
theorem B1484699 : Blo 988596 1484699 := bstep (se 1 (by rfl) ⟨1113524, by rfl⟩ : syracuseStep 1484699 = 2227049) B2227049
theorem B1484735 : Blo 988596 1484735 := bstep (se 1 (by rfl) ⟨1113551, by rfl⟩ : syracuseStep 1484735 = 2227103) B2227103
theorem B1877995 : Blo 988596 1877995 := bstep (se 1 (by rfl) ⟨1408496, by rfl⟩ : syracuseStep 1877995 = 2816993) B2816993
theorem B1484921 : Blo 988596 1484921 := bstep (se 2 (by rfl) ⟨556845, by rfl⟩ : syracuseStep 1484921 = 1113691) B1113691
theorem B6334955 : Blo 988596 6334955 := bstep (se 1 (by rfl) ⟨4751216, by rfl⟩ : syracuseStep 6334955 = 9502433) B9502433
theorem B1255915 : Blo 988596 1255915 := bstep (se 1 (by rfl) ⟨941936, by rfl⟩ : syracuseStep 1255915 = 1883873) B1883873
theorem B1485305 : Blo 988596 1485305 := bstep (se 2 (by rfl) ⟨556989, by rfl⟩ : syracuseStep 1485305 = 1113979) B1113979
theorem B1485359 : Blo 988596 1485359 := bstep (se 1 (by rfl) ⟨1114019, by rfl⟩ : syracuseStep 1485359 = 2228039) B2228039
theorem B8039087 : Blo 988596 8039087 := bstep (se 1 (by rfl) ⟨6029315, by rfl⟩ : syracuseStep 8039087 = 12058631) B12058631
theorem B1485791 : Blo 988596 1485791 := bstep (se 1 (by rfl) ⟨1114343, by rfl⟩ : syracuseStep 1485791 = 2228687) B2228687
theorem B8465741 : Blo 988596 8465741 := bstep (se 3 (by rfl) ⟨1587326, by rfl⟩ : syracuseStep 8465741 = 3174653) B3174653
theorem B1486235 : Blo 988596 1486235 := bstep (se 1 (by rfl) ⟨1114676, by rfl⟩ : syracuseStep 1486235 = 2229353) B2229353
theorem B10726825 : Blo 988596 10726825 := bstep (se 2 (by rfl) ⟨4022559, by rfl⟩ : syracuseStep 10726825 = 8045119) B8045119
theorem B1486655 : Blo 988596 1486655 := bstep (se 1 (by rfl) ⟨1114991, by rfl⟩ : syracuseStep 1486655 = 2229983) B2229983
theorem B1486841 : Blo 988596 1486841 := bstep (se 2 (by rfl) ⟨557565, by rfl⟩ : syracuseStep 1486841 = 1115131) B1115131
theorem B1487081 : Blo 988596 1487081 := bstep (se 2 (by rfl) ⟨557655, by rfl⟩ : syracuseStep 1487081 = 1115311) B1115311
theorem B1880327 : Blo 988596 1880327 := bstep (se 1 (by rfl) ⟨1410245, by rfl⟩ : syracuseStep 1880327 = 2820491) B2820491
theorem B1487207 : Blo 988596 1487207 := bstep (se 1 (by rfl) ⟨1115405, by rfl⟩ : syracuseStep 1487207 = 2230811) B2230811
theorem B64237931 : Blo 988596 64237931 := bstep (se 1 (by rfl) ⟨48178448, by rfl⟩ : syracuseStep 64237931 = 96356897) B96356897
theorem B16036649 : Blo 988596 16036649 := bstep (se 2 (by rfl) ⟨6013743, by rfl⟩ : syracuseStep 16036649 = 12027487) B12027487
theorem B2503487 : Blo 988596 2503487 := bstep (se 1 (by rfl) ⟨1877615, by rfl⟩ : syracuseStep 2503487 = 3755231) B3755231
theorem B1487753 : Blo 988596 1487753 := bstep (se 2 (by rfl) ⟨557907, by rfl⟩ : syracuseStep 1487753 = 1115815) B1115815
theorem B5649659 : Blo 988596 5649659 := bstep (se 1 (by rfl) ⟨4237244, by rfl⟩ : syracuseStep 5649659 = 8474489) B8474489
theorem B1488137 : Blo 988596 1488137 := bstep (se 2 (by rfl) ⟨558051, by rfl⟩ : syracuseStep 1488137 = 1116103) B1116103
theorem B1488191 : Blo 988596 1488191 := bstep (se 1 (by rfl) ⟨1116143, by rfl⟩ : syracuseStep 1488191 = 2232287) B2232287
theorem B36681281 : Blo 988596 36681281 := bstep (se 2 (by rfl) ⟨13755480, by rfl⟩ : syracuseStep 36681281 = 27510961) B27510961
theorem B66795131 : Blo 988596 66795131 := bstep (se 1 (by rfl) ⟨50096348, by rfl⟩ : syracuseStep 66795131 = 100192697) B100192697
theorem B1488617 : Blo 988596 1488617 := bstep (se 2 (by rfl) ⟨558231, by rfl⟩ : syracuseStep 1488617 = 1116463) B1116463
theorem B1488623 : Blo 988596 1488623 := bstep (se 1 (by rfl) ⟨1116467, by rfl⟩ : syracuseStep 1488623 = 2232935) B2232935
theorem B6338519 : Blo 988596 6338519 := bstep (se 1 (by rfl) ⟨4753889, by rfl⟩ : syracuseStep 6338519 = 9507779) B9507779
theorem B4077803 : Blo 988596 4077803 := bstep (se 1 (by rfl) ⟨3058352, by rfl⟩ : syracuseStep 4077803 = 6116705) B6116705
theorem B1882415 : Blo 988596 1882415 := bstep (se 1 (by rfl) ⟨1411811, by rfl⟩ : syracuseStep 1882415 = 2823623) B2823623
theorem B33077629 : Blo 988596 33077629 := bstep (se 3 (by rfl) ⟨6202055, by rfl⟩ : syracuseStep 33077629 = 12404111) B12404111
theorem B6109607 : Blo 988596 6109607 := bstep (se 1 (by rfl) ⟨4582205, by rfl⟩ : syracuseStep 6109607 = 9164411) B9164411
theorem B4078201 : Blo 988596 4078201 := bstep (se 2 (by rfl) ⟨1529325, by rfl⟩ : syracuseStep 4078201 = 3058651) B3058651
theorem B4831903 : Blo 988596 4831903 := bstep (se 1 (by rfl) ⟨3623927, by rfl⟩ : syracuseStep 4831903 = 7247855) B7247855
theorem B5717137 : Blo 988596 5717137 := bstep (se 2 (by rfl) ⟨2143926, by rfl⟩ : syracuseStep 5717137 = 4287853) B4287853
theorem B2113087 : Blo 988596 2113087 := bstep (se 1 (by rfl) ⟨1584815, by rfl⟩ : syracuseStep 2113087 = 3169631) B3169631
theorem B2015143 : Blo 988596 2015143 := bstep (se 1 (by rfl) ⟨1511357, by rfl⟩ : syracuseStep 2015143 = 3022715) B3022715
theorem B7225787 : Blo 988596 7225787 := bstep (se 1 (by rfl) ⟨5419340, by rfl⟩ : syracuseStep 7225787 = 10838681) B10838681
theorem B16957997 : Blo 988596 16957997 := bstep (se 3 (by rfl) ⟨3179624, by rfl⟩ : syracuseStep 16957997 = 6359249) B6359249
theorem B2147113 : Blo 988596 2147113 := bstep (se 2 (by rfl) ⟨805167, by rfl⟩ : syracuseStep 2147113 = 1610335) B1610335
theorem B2376647 : Blo 988596 2376647 := bstep (se 1 (by rfl) ⟨1782485, by rfl⟩ : syracuseStep 2376647 = 3564971) B3564971
theorem B7521335 : Blo 988596 7521335 := bstep (se 1 (by rfl) ⟨5641001, by rfl⟩ : syracuseStep 7521335 = 11282003) B11282003
theorem B2507831 : Blo 988596 2507831 := bstep (se 1 (by rfl) ⟨1880873, by rfl⟩ : syracuseStep 2507831 = 3761747) B3761747
theorem B4015295 : Blo 988596 4015295 := bstep (se 1 (by rfl) ⟨3011471, by rfl⟩ : syracuseStep 4015295 = 6022943) B6022943
theorem B2114795 : Blo 988596 2114795 := bstep (se 1 (by rfl) ⟨1586096, by rfl⟩ : syracuseStep 2114795 = 3172193) B3172193
theorem B2147563 : Blo 988596 2147563 := bstep (se 1 (by rfl) ⟨1610672, by rfl⟩ : syracuseStep 2147563 = 3221345) B3221345
theorem B19318019 : Blo 988596 19318019 := bstep (se 1 (by rfl) ⟨14488514, by rfl⟩ : syracuseStep 19318019 = 28977029) B28977029
theorem B8570299 : Blo 988596 8570299 := bstep (se 1 (by rfl) ⟨6427724, by rfl⟩ : syracuseStep 8570299 = 12855449) B12855449
theorem B7226987 : Blo 988596 7226987 := bstep (se 1 (by rfl) ⟨5420240, by rfl⟩ : syracuseStep 7226987 = 10840481) B10840481
theorem B5720647 : Blo 988596 5720647 := bstep (se 1 (by rfl) ⟨4290485, by rfl⟩ : syracuseStep 5720647 = 8580971) B8580971
theorem B16927379 : Blo 988596 16927379 := bstep (se 1 (by rfl) ⟨12695534, by rfl⟩ : syracuseStep 16927379 = 25391069) B25391069
theorem B3755261 : Blo 988596 3755261 := bstep (se 3 (by rfl) ⟨704111, by rfl⟩ : syracuseStep 3755261 = 1408223) B1408223
theorem B16535299 : Blo 988596 16535299 := bstep (se 1 (by rfl) ⟨12401474, by rfl⟩ : syracuseStep 16535299 = 24802949) B24802949
theorem B16076555 : Blo 988596 16076555 := bstep (se 1 (by rfl) ⟨12057416, by rfl⟩ : syracuseStep 16076555 = 24114833) B24114833
theorem B3755915 : Blo 988596 3755915 := bstep (se 1 (by rfl) ⟨2816936, by rfl⟩ : syracuseStep 3755915 = 5633873) B5633873
theorem B7524251 : Blo 988596 7524251 := bstep (se 1 (by rfl) ⟨5643188, by rfl⟩ : syracuseStep 7524251 = 11286377) B11286377
theorem B8474867 : Blo 988596 8474867 := bstep (se 1 (by rfl) ⟨6356150, by rfl⟩ : syracuseStep 8474867 = 12712301) B12712301
theorem B19288709 : Blo 988596 19288709 := bstep (se 4 (by rfl) ⟨1808316, by rfl⟩ : syracuseStep 19288709 = 3616633) B3616633
theorem B4641419 : Blo 988596 4641419 := bstep (se 1 (by rfl) ⟨3481064, by rfl⟩ : syracuseStep 4641419 = 6962129) B6962129
theorem B2118811 : Blo 988596 2118811 := bstep (se 1 (by rfl) ⟨1589108, by rfl⟩ : syracuseStep 2118811 = 3178217) B3178217
theorem B2512235 : Blo 988596 2512235 := bstep (se 1 (by rfl) ⟨1884176, by rfl⟩ : syracuseStep 2512235 = 3768353) B3768353
theorem B2512367 : Blo 988596 2512367 := bstep (se 1 (by rfl) ⟨1884275, by rfl⟩ : syracuseStep 2512367 = 3768551) B3768551
theorem B3758177 : Blo 988596 3758177 := bstep (se 2 (by rfl) ⟨1409316, by rfl⟩ : syracuseStep 3758177 = 2818633) B2818633
theorem B3758663 : Blo 988596 3758663 := bstep (se 1 (by rfl) ⟨2818997, by rfl⟩ : syracuseStep 3758663 = 5637995) B5637995
theorem B17161105 : Blo 988596 17161105 := bstep (se 2 (by rfl) ⟨6435414, by rfl⟩ : syracuseStep 17161105 = 12870829) B12870829
theorem B3169783 : Blo 988596 3169783 := bstep (se 1 (by rfl) ⟨2377337, by rfl⟩ : syracuseStep 3169783 = 4754675) B4754675
theorem B2383481 : Blo 988596 2383481 := bstep (se 2 (by rfl) ⟨893805, by rfl⟩ : syracuseStep 2383481 = 1787611) B1787611
theorem B1204079 : Blo 988596 1204079 := bstep (se 1 (by rfl) ⟨903059, by rfl⟩ : syracuseStep 1204079 = 1806119) B1806119
theorem B57041333 : Blo 988596 57041333 := bstep (se 5 (by rfl) ⟨2673812, by rfl⟩ : syracuseStep 57041333 = 5347625) B5347625
theorem B2384411 : Blo 988596 2384411 := bstep (se 1 (by rfl) ⟨1788308, by rfl⟩ : syracuseStep 2384411 = 3576617) B3576617
theorem B54256805 : Blo 988596 54256805 := bstep (se 4 (by rfl) ⟨5086575, by rfl⟩ : syracuseStep 54256805 = 10173151) B10173151
theorem B3761579 : Blo 988596 3761579 := bstep (se 1 (by rfl) ⟨2821184, by rfl⟩ : syracuseStep 3761579 = 5642369) B5642369
theorem B4515347 : Blo 988596 4515347 := bstep (se 1 (by rfl) ⟨3386510, by rfl⟩ : syracuseStep 4515347 = 6773021) B6773021
theorem B4515563 : Blo 988596 4515563 := bstep (se 1 (by rfl) ⟨3386672, by rfl⟩ : syracuseStep 4515563 = 6773345) B6773345
theorem B3565691 : Blo 988596 3565691 := bstep (se 1 (by rfl) ⟨2674268, by rfl⟩ : syracuseStep 3565691 = 5348537) B5348537
theorem B3172745 : Blo 988596 3172745 := bstep (se 2 (by rfl) ⟨1189779, by rfl⟩ : syracuseStep 3172745 = 2379559) B2379559
theorem B2255339 : Blo 988596 2255339 := bstep (se 1 (by rfl) ⟨1691504, by rfl⟩ : syracuseStep 2255339 = 3383009) B3383009
theorem B3762719 : Blo 988596 3762719 := bstep (se 1 (by rfl) ⟨2822039, by rfl⟩ : syracuseStep 3762719 = 5644079) B5644079
theorem B7531055 : Blo 988596 7531055 := bstep (se 1 (by rfl) ⟨5648291, by rfl⟩ : syracuseStep 7531055 = 11296583) B11296583
theorem B5008553 : Blo 988596 5008553 := bstep (se 2 (by rfl) ⟨1878207, by rfl⟩ : syracuseStep 5008553 = 3756415) B3756415
theorem B5008877 : Blo 988596 5008877 := bstep (se 3 (by rfl) ⟨939164, by rfl⟩ : syracuseStep 5008877 = 1878329) B1878329
theorem B5729773 : Blo 988596 5729773 := bstep (se 3 (by rfl) ⟨1074332, by rfl⟩ : syracuseStep 5729773 = 2148665) B2148665
theorem B18542479 : Blo 988596 18542479 := bstep (se 1 (by rfl) ⟨13906859, by rfl⟩ : syracuseStep 18542479 = 27813719) B27813719
theorem B2224403 : Blo 988596 2224403 := bstep (se 1 (by rfl) ⟨1668302, by rfl⟩ : syracuseStep 2224403 = 3336605) B3336605
theorem B5009687 : Blo 988596 5009687 := bstep (se 1 (by rfl) ⟨3757265, by rfl⟩ : syracuseStep 5009687 = 7514531) B7514531
theorem B12710297 : Blo 988596 12710297 := bstep (se 2 (by rfl) ⟨4766361, by rfl⟩ : syracuseStep 12710297 = 9532723) B9532723
theorem B2224583 : Blo 988596 2224583 := bstep (se 1 (by rfl) ⟨1668437, by rfl⟩ : syracuseStep 2224583 = 3336875) B3336875
theorem B3338927 : Blo 988596 3338927 := bstep (se 1 (by rfl) ⟨2504195, by rfl⟩ : syracuseStep 3338927 = 5008391) B5008391
theorem B12055223 : Blo 988596 12055223 := bstep (se 1 (by rfl) ⟨9041417, by rfl⟩ : syracuseStep 12055223 = 18082835) B18082835
theorem B2224943 : Blo 988596 2224943 := bstep (se 1 (by rfl) ⟨1668707, by rfl⟩ : syracuseStep 2224943 = 3337415) B3337415
theorem B2225033 : Blo 988596 2225033 := bstep (se 2 (by rfl) ⟨834387, by rfl⟩ : syracuseStep 2225033 = 1668775) B1668775
theorem B3765149 : Blo 988596 3765149 := bstep (se 3 (by rfl) ⟨705965, by rfl⟩ : syracuseStep 3765149 = 1411931) B1411931
theorem B2225807 : Blo 988596 2225807 := bstep (se 1 (by rfl) ⟨1669355, by rfl⟩ : syracuseStep 2225807 = 3338711) B3338711
theorem B4224737 : Blo 988596 4224737 := bstep (se 2 (by rfl) ⟨1584276, by rfl⟩ : syracuseStep 4224737 = 3168553) B3168553
theorem B2225897 : Blo 988596 2225897 := bstep (se 2 (by rfl) ⟨834711, by rfl⟩ : syracuseStep 2225897 = 1669423) B1669423
theorem B5011307 : Blo 988596 5011307 := bstep (se 1 (by rfl) ⟨3758480, by rfl⟩ : syracuseStep 5011307 = 7516961) B7516961
theorem B8452619 : Blo 988596 8452619 := bstep (se 1 (by rfl) ⟨6339464, by rfl⟩ : syracuseStep 8452619 = 12678929) B12678929
theorem B1669673 : Blo 988596 1669673 := bstep (se 2 (by rfl) ⟨626127, by rfl⟩ : syracuseStep 1669673 = 1252255) B1252255
theorem B1505833 : Blo 988596 1505833 := bstep (se 2 (by rfl) ⟨564687, by rfl⟩ : syracuseStep 1505833 = 1129375) B1129375
theorem B2226779 : Blo 988596 2226779 := bstep (se 1 (by rfl) ⟨1670084, by rfl⟩ : syracuseStep 2226779 = 3340169) B3340169
theorem B3177089 : Blo 988596 3177089 := bstep (se 2 (by rfl) ⟨1191408, by rfl⟩ : syracuseStep 3177089 = 2382817) B2382817
theorem B2226923 : Blo 988596 2226923 := bstep (se 1 (by rfl) ⟨1670192, by rfl⟩ : syracuseStep 2226923 = 3340385) B3340385
theorem B1113295 : Blo 988596 1113295 := bstep (se 1 (by rfl) ⟨834971, by rfl⟩ : syracuseStep 1113295 = 1669943) B1669943
theorem B1670375 : Blo 988596 1670375 := bstep (se 1 (by rfl) ⟨1252781, by rfl⟩ : syracuseStep 1670375 = 2505563) B2505563
theorem B5635331 : Blo 988596 5635331 := bstep (se 1 (by rfl) ⟨4226498, by rfl⟩ : syracuseStep 5635331 = 8452997) B8452997
theorem B2227535 : Blo 988596 2227535 := bstep (se 1 (by rfl) ⟨1670651, by rfl⟩ : syracuseStep 2227535 = 3341303) B3341303
theorem B2227625 : Blo 988596 2227625 := bstep (se 2 (by rfl) ⟨835359, by rfl⟩ : syracuseStep 2227625 = 1670719) B1670719
theorem B3341843 : Blo 988596 3341843 := bstep (se 1 (by rfl) ⟨2506382, by rfl⟩ : syracuseStep 3341843 = 5012765) B5012765
theorem B2227823 : Blo 988596 2227823 := bstep (se 1 (by rfl) ⟨1670867, by rfl⟩ : syracuseStep 2227823 = 3341735) B3341735
theorem B2817767 : Blo 988596 2817767 := bstep (se 1 (by rfl) ⟨2113325, by rfl⟩ : syracuseStep 2817767 = 4226651) B4226651
theorem B19038077 : Blo 988596 19038077 := bstep (se 3 (by rfl) ⟨3569639, by rfl⟩ : syracuseStep 19038077 = 7139279) B7139279
theorem B2228111 : Blo 988596 2228111 := bstep (se 1 (by rfl) ⟨1671083, by rfl⟩ : syracuseStep 2228111 = 3342167) B3342167
theorem B4817191 : Blo 988596 4817191 := bstep (se 1 (by rfl) ⟨3612893, by rfl⟩ : syracuseStep 4817191 = 7225787) B7225787
theorem B11305331 : Blo 988596 11305331 := bstep (se 1 (by rfl) ⟨8478998, by rfl⟩ : syracuseStep 11305331 = 16957997) B16957997
theorem B5014223 : Blo 988596 5014223 := bstep (se 1 (by rfl) ⟨3760667, by rfl⟩ : syracuseStep 5014223 = 7521335) B7521335
theorem B1671887 : Blo 988596 1671887 := bstep (se 1 (by rfl) ⟨1253915, by rfl⟩ : syracuseStep 1671887 = 2507831) B2507831
theorem B2229047 : Blo 988596 2229047 := bstep (se 1 (by rfl) ⟨1671785, by rfl⟩ : syracuseStep 2229047 = 3343571) B3343571
theorem B1114951 : Blo 988596 1114951 := bstep (se 1 (by rfl) ⟨836213, by rfl⟩ : syracuseStep 1114951 = 1672427) B1672427
theorem B2229227 : Blo 988596 2229227 := bstep (se 1 (by rfl) ⟨1671920, by rfl⟩ : syracuseStep 2229227 = 3343841) B3343841
theorem B3343355 : Blo 988596 3343355 := bstep (se 1 (by rfl) ⟨2507516, by rfl⟩ : syracuseStep 3343355 = 5015033) B5015033
theorem B6358429 : Blo 988596 6358429 := bstep (se 3 (by rfl) ⟨1192205, by rfl⟩ : syracuseStep 6358429 = 2384411) B2384411
theorem B1115887 : Blo 988596 1115887 := bstep (se 1 (by rfl) ⟨836915, by rfl⟩ : syracuseStep 1115887 = 1673831) B1673831
theorem B17139485 : Blo 988596 17139485 := bstep (se 3 (by rfl) ⟨3213653, by rfl⟩ : syracuseStep 17139485 = 6427307) B6427307
theorem B2230127 : Blo 988596 2230127 := bstep (se 1 (by rfl) ⟨1672595, by rfl⟩ : syracuseStep 2230127 = 3345191) B3345191
theorem B2230235 : Blo 988596 2230235 := bstep (se 1 (by rfl) ⟨1672676, by rfl⟩ : syracuseStep 2230235 = 3345353) B3345353
theorem B2230343 : Blo 988596 2230343 := bstep (se 1 (by rfl) ⟨1672757, by rfl⟩ : syracuseStep 2230343 = 3345515) B3345515
theorem B2230415 : Blo 988596 2230415 := bstep (se 1 (by rfl) ⟨1672811, by rfl⟩ : syracuseStep 2230415 = 3345623) B3345623
theorem B1116391 : Blo 988596 1116391 := bstep (se 1 (by rfl) ⟨837293, by rfl⟩ : syracuseStep 1116391 = 1674587) B1674587
theorem B2230505 : Blo 988596 2230505 := bstep (se 2 (by rfl) ⟨836439, by rfl⟩ : syracuseStep 2230505 = 1672879) B1672879
theorem B2230523 : Blo 988596 2230523 := bstep (se 1 (by rfl) ⟨1672892, by rfl⟩ : syracuseStep 2230523 = 3345785) B3345785
theorem B2230775 : Blo 988596 2230775 := bstep (se 1 (by rfl) ⟨1673081, by rfl⟩ : syracuseStep 2230775 = 3346163) B3346163
theorem B10717703 : Blo 988596 10717703 := bstep (se 1 (by rfl) ⟨8038277, by rfl⟩ : syracuseStep 10717703 = 16076555) B16076555
theorem B5016167 : Blo 988596 5016167 := bstep (se 1 (by rfl) ⟨3762125, by rfl⟩ : syracuseStep 5016167 = 7524251) B7524251
theorem B8031109 : Blo 988596 8031109 := bstep (se 4 (by rfl) ⟨752916, by rfl⟩ : syracuseStep 8031109 = 1505833) B1505833
theorem B5639453 : Blo 988596 5639453 := bstep (se 3 (by rfl) ⟨1057397, by rfl⟩ : syracuseStep 5639453 = 2114795) B2114795
theorem B1674553 : Blo 988596 1674553 := bstep (se 2 (by rfl) ⟨627957, by rfl⟩ : syracuseStep 1674553 = 1255915) B1255915
theorem B51514717 : Blo 988596 51514717 := bstep (se 3 (by rfl) ⟨9659009, by rfl⟩ : syracuseStep 51514717 = 19318019) B19318019
theorem B3345947 : Blo 988596 3345947 := bstep (se 1 (by rfl) ⟨2509460, by rfl⟩ : syracuseStep 3345947 = 5018921) B5018921
theorem B1674823 : Blo 988596 1674823 := bstep (se 1 (by rfl) ⟨1256117, by rfl⟩ : syracuseStep 1674823 = 2512235) B2512235
theorem B1674911 : Blo 988596 1674911 := bstep (se 1 (by rfl) ⟨1256183, by rfl⟩ : syracuseStep 1674911 = 2512367) B2512367
theorem B6033599 : Blo 988596 6033599 := bstep (se 1 (by rfl) ⟨4525199, by rfl⟩ : syracuseStep 6033599 = 9050399) B9050399
theorem B5640455 : Blo 988596 5640455 := bstep (se 1 (by rfl) ⟨4230341, by rfl⟩ : syracuseStep 5640455 = 8460683) B8460683
theorem B19271965 : Blo 988596 19271965 := bstep (se 3 (by rfl) ⟨3613493, by rfl⟩ : syracuseStep 19271965 = 7226987) B7226987
theorem B3346811 : Blo 988596 3346811 := bstep (se 1 (by rfl) ⟨2510108, by rfl⟩ : syracuseStep 3346811 = 5020217) B5020217
theorem B7639697 : Blo 988596 7639697 := bstep (se 2 (by rfl) ⟨2864886, by rfl⟩ : syracuseStep 7639697 = 5729773) B5729773
theorem B11277629 : Blo 988596 11277629 := bstep (se 3 (by rfl) ⟨2114555, by rfl⟩ : syracuseStep 11277629 = 4229111) B4229111
theorem B14292287 : Blo 988596 14292287 := bstep (se 1 (by rfl) ⟨10719215, by rfl⟩ : syracuseStep 14292287 = 21438431) B21438431
theorem B988639 : Blo 988596 988639 := bstep (se 1 (by rfl) ⟨741479, by rfl⟩ : syracuseStep 988639 = 1482959) B1482959
theorem B988671 : Blo 988596 988671 := bstep (se 1 (by rfl) ⟨741503, by rfl⟩ : syracuseStep 988671 = 1483007) B1483007
theorem B989215 : Blo 988596 989215 := bstep (se 1 (by rfl) ⟨741911, by rfl⟩ : syracuseStep 989215 = 1483823) B1483823
theorem B989295 : Blo 988596 989295 := bstep (se 1 (by rfl) ⟨741971, by rfl⟩ : syracuseStep 989295 = 1483943) B1483943
theorem B989543 : Blo 988596 989543 := bstep (se 1 (by rfl) ⟨742157, by rfl⟩ : syracuseStep 989543 = 1484315) B1484315
theorem B16292285 : Blo 988596 16292285 := bstep (se 3 (by rfl) ⟨3054803, by rfl⟩ : syracuseStep 16292285 = 6109607) B6109607
theorem B1251931 : Blo 988596 1251931 := bstep (se 1 (by rfl) ⟨938948, by rfl⟩ : syracuseStep 1251931 = 1877897) B1877897
theorem B989799 : Blo 988596 989799 := bstep (se 1 (by rfl) ⟨742349, by rfl⟩ : syracuseStep 989799 = 1484699) B1484699
theorem B989823 : Blo 988596 989823 := bstep (se 1 (by rfl) ⟨742367, by rfl⟩ : syracuseStep 989823 = 1484735) B1484735
theorem B989947 : Blo 988596 989947 := bstep (se 1 (by rfl) ⟨742460, by rfl⟩ : syracuseStep 989947 = 1484921) B1484921
theorem B2825081 : Blo 988596 2825081 := bstep (se 2 (by rfl) ⟨1059405, by rfl⟩ : syracuseStep 2825081 = 2118811) B2118811
theorem B990203 : Blo 988596 990203 := bstep (se 1 (by rfl) ⟨742652, by rfl⟩ : syracuseStep 990203 = 1485305) B1485305
theorem B990239 : Blo 988596 990239 := bstep (se 1 (by rfl) ⟨742679, by rfl⟩ : syracuseStep 990239 = 1485359) B1485359
theorem B5020703 : Blo 988596 5020703 := bstep (se 1 (by rfl) ⟨3765527, by rfl⟩ : syracuseStep 5020703 = 7531055) B7531055
theorem B6036713 : Blo 988596 6036713 := bstep (se 2 (by rfl) ⟨2263767, by rfl⟩ : syracuseStep 6036713 = 4527535) B4527535
theorem B990527 : Blo 988596 990527 := bstep (se 1 (by rfl) ⟨742895, by rfl⟩ : syracuseStep 990527 = 1485791) B1485791
theorem B5643827 : Blo 988596 5643827 := bstep (se 1 (by rfl) ⟨4232870, by rfl⟩ : syracuseStep 5643827 = 8465741) B8465741
theorem B990823 : Blo 988596 990823 := bstep (se 1 (by rfl) ⟨743117, by rfl⟩ : syracuseStep 990823 = 1486235) B1486235
theorem B991103 : Blo 988596 991103 := bstep (se 1 (by rfl) ⟨743327, by rfl⟩ : syracuseStep 991103 = 1486655) B1486655
theorem B991227 : Blo 988596 991227 := bstep (se 1 (by rfl) ⟨743420, by rfl⟩ : syracuseStep 991227 = 1486841) B1486841
theorem B991387 : Blo 988596 991387 := bstep (se 1 (by rfl) ⟨743540, by rfl⟩ : syracuseStep 991387 = 1487081) B1487081
theorem B1253551 : Blo 988596 1253551 := bstep (se 1 (by rfl) ⟨940163, by rfl⟩ : syracuseStep 1253551 = 1880327) B1880327
theorem B1482935 : Blo 988596 1482935 := bstep (se 1 (by rfl) ⟨1112201, by rfl⟩ : syracuseStep 1482935 = 2224403) B2224403
theorem B991471 : Blo 988596 991471 := bstep (se 1 (by rfl) ⟨743603, by rfl⟩ : syracuseStep 991471 = 1487207) B1487207
theorem B1483055 : Blo 988596 1483055 := bstep (se 1 (by rfl) ⟨1112291, by rfl⟩ : syracuseStep 1483055 = 2224583) B2224583
theorem B8036815 : Blo 988596 8036815 := bstep (se 1 (by rfl) ⟨6027611, by rfl⟩ : syracuseStep 8036815 = 12055223) B12055223
theorem B10691099 : Blo 988596 10691099 := bstep (se 1 (by rfl) ⟨8018324, by rfl⟩ : syracuseStep 10691099 = 16036649) B16036649
theorem B1483295 : Blo 988596 1483295 := bstep (se 1 (by rfl) ⟨1112471, by rfl⟩ : syracuseStep 1483295 = 2224943) B2224943
theorem B1483355 : Blo 988596 1483355 := bstep (se 1 (by rfl) ⟨1112516, by rfl⟩ : syracuseStep 1483355 = 2225033) B2225033
theorem B991835 : Blo 988596 991835 := bstep (se 1 (by rfl) ⟨743876, by rfl⟩ : syracuseStep 991835 = 1487753) B1487753
theorem B992091 : Blo 988596 992091 := bstep (se 1 (by rfl) ⟨744068, by rfl⟩ : syracuseStep 992091 = 1488137) B1488137
theorem B992127 : Blo 988596 992127 := bstep (se 1 (by rfl) ⟨744095, by rfl⟩ : syracuseStep 992127 = 1488191) B1488191
theorem B24454187 : Blo 988596 24454187 := bstep (se 1 (by rfl) ⟨18340640, by rfl⟩ : syracuseStep 24454187 = 36681281) B36681281
theorem B1483871 : Blo 988596 1483871 := bstep (se 1 (by rfl) ⟨1112903, by rfl⟩ : syracuseStep 1483871 = 2225807) B2225807
theorem B1483931 : Blo 988596 1483931 := bstep (se 1 (by rfl) ⟨1112948, by rfl⟩ : syracuseStep 1483931 = 2225897) B2225897
theorem B992411 : Blo 988596 992411 := bstep (se 1 (by rfl) ⟨744308, by rfl⟩ : syracuseStep 992411 = 1488617) B1488617
theorem B992415 : Blo 988596 992415 := bstep (se 1 (by rfl) ⟨744311, by rfl⟩ : syracuseStep 992415 = 1488623) B1488623
theorem B22881473 : Blo 988596 22881473 := bstep (se 2 (by rfl) ⟨8580552, by rfl⟩ : syracuseStep 22881473 = 17161105) B17161105
theorem B9020909 : Blo 988596 9020909 := bstep (se 3 (by rfl) ⟨1691420, by rfl⟩ : syracuseStep 9020909 = 3382841) B3382841
theorem B1254943 : Blo 988596 1254943 := bstep (se 1 (by rfl) ⟨941207, by rfl⟩ : syracuseStep 1254943 = 1882415) B1882415
theorem B1484393 : Blo 988596 1484393 := bstep (se 2 (by rfl) ⟨556647, by rfl⟩ : syracuseStep 1484393 = 1113295) B1113295
theorem B1484519 : Blo 988596 1484519 := bstep (se 1 (by rfl) ⟨1113389, by rfl⟩ : syracuseStep 1484519 = 2226779) B2226779
theorem B1484615 : Blo 988596 1484615 := bstep (se 1 (by rfl) ⟨1113461, by rfl⟩ : syracuseStep 1484615 = 2226923) B2226923
theorem B7514045 : Blo 988596 7514045 := bstep (se 3 (by rfl) ⟨1408883, by rfl⟩ : syracuseStep 7514045 = 2817767) B2817767
theorem B1485023 : Blo 988596 1485023 := bstep (se 1 (by rfl) ⟨1113767, by rfl⟩ : syracuseStep 1485023 = 2227535) B2227535
theorem B1485083 : Blo 988596 1485083 := bstep (se 1 (by rfl) ⟨1113812, by rfl⟩ : syracuseStep 1485083 = 2227625) B2227625
theorem B1485215 : Blo 988596 1485215 := bstep (se 1 (by rfl) ⟨1113911, by rfl⟩ : syracuseStep 1485215 = 2227823) B2227823
theorem B12692051 : Blo 988596 12692051 := bstep (se 1 (by rfl) ⟨9519038, by rfl⟩ : syracuseStep 12692051 = 19038077) B19038077
theorem B1485407 : Blo 988596 1485407 := bstep (se 1 (by rfl) ⟨1114055, by rfl⟩ : syracuseStep 1485407 = 2228111) B2228111
theorem B1485737 : Blo 988596 1485737 := bstep (se 2 (by rfl) ⟨557151, by rfl⟩ : syracuseStep 1485737 = 1114303) B1114303
theorem B1485767 : Blo 988596 1485767 := bstep (se 1 (by rfl) ⟨1114325, by rfl⟩ : syracuseStep 1485767 = 2228651) B2228651
theorem B1485887 : Blo 988596 1485887 := bstep (se 1 (by rfl) ⟨1114415, by rfl⟩ : syracuseStep 1485887 = 2228831) B2228831
theorem B1584431 : Blo 988596 1584431 := bstep (se 1 (by rfl) ⟨1188323, by rfl⟩ : syracuseStep 1584431 = 2376647) B2376647
theorem B1486127 : Blo 988596 1486127 := bstep (se 1 (by rfl) ⟨1114595, by rfl⟩ : syracuseStep 1486127 = 2229191) B2229191
theorem B4828511 : Blo 988596 4828511 := bstep (se 1 (by rfl) ⟨3621383, by rfl⟩ : syracuseStep 4828511 = 7242767) B7242767
theorem B1486313 : Blo 988596 1486313 := bstep (se 2 (by rfl) ⟨557367, by rfl⟩ : syracuseStep 1486313 = 1114735) B1114735
theorem B1486367 : Blo 988596 1486367 := bstep (se 1 (by rfl) ⟨1114775, by rfl⟩ : syracuseStep 1486367 = 2229551) B2229551
theorem B1486457 : Blo 988596 1486457 := bstep (se 2 (by rfl) ⟨557421, by rfl⟩ : syracuseStep 1486457 = 1114843) B1114843
theorem B5648201 : Blo 988596 5648201 := bstep (se 2 (by rfl) ⟨2118075, by rfl⟩ : syracuseStep 5648201 = 4236151) B4236151
theorem B1486703 : Blo 988596 1486703 := bstep (se 1 (by rfl) ⟨1115027, by rfl⟩ : syracuseStep 1486703 = 2230055) B2230055
theorem B81244043 : Blo 988596 81244043 := bstep (se 1 (by rfl) ⟨60933032, by rfl⟩ : syracuseStep 81244043 = 121866065) B121866065
theorem B4763731 : Blo 988596 4763731 := bstep (se 1 (by rfl) ⟨3572798, by rfl⟩ : syracuseStep 4763731 = 7145597) B7145597
theorem B1486955 : Blo 988596 1486955 := bstep (se 1 (by rfl) ⟨1115216, by rfl⟩ : syracuseStep 1486955 = 2230433) B2230433
theorem B16953623 : Blo 988596 16953623 := bstep (se 1 (by rfl) ⟨12715217, by rfl⟩ : syracuseStep 16953623 = 25430435) B25430435
theorem B11284919 : Blo 988596 11284919 := bstep (se 1 (by rfl) ⟨8463689, by rfl⟩ : syracuseStep 11284919 = 16927379) B16927379
theorem B1487387 : Blo 988596 1487387 := bstep (se 1 (by rfl) ⟨1115540, by rfl⟩ : syracuseStep 1487387 = 2231081) B2231081
theorem B1487567 : Blo 988596 1487567 := bstep (se 1 (by rfl) ⟨1115675, by rfl⟩ : syracuseStep 1487567 = 2231351) B2231351
theorem B2503507 : Blo 988596 2503507 := bstep (se 1 (by rfl) ⟨1877630, by rfl⟩ : syracuseStep 2503507 = 3755261) B3755261
theorem B1487855 : Blo 988596 1487855 := bstep (se 1 (by rfl) ⟨1115891, by rfl⟩ : syracuseStep 1487855 = 2231783) B2231783
theorem B2503943 : Blo 988596 2503943 := bstep (se 1 (by rfl) ⟨1877957, by rfl⟩ : syracuseStep 2503943 = 3755915) B3755915
theorem B2503993 : Blo 988596 2503993 := bstep (se 2 (by rfl) ⟨938997, by rfl⟩ : syracuseStep 2503993 = 1877995) B1877995
theorem B1488239 : Blo 988596 1488239 := bstep (se 1 (by rfl) ⟨1116179, by rfl⟩ : syracuseStep 1488239 = 2232359) B2232359
theorem B1488359 : Blo 988596 1488359 := bstep (se 1 (by rfl) ⟨1116269, by rfl⟩ : syracuseStep 1488359 = 2232539) B2232539
theorem B5649911 : Blo 988596 5649911 := bstep (se 1 (by rfl) ⟨4237433, by rfl⟩ : syracuseStep 5649911 = 8474867) B8474867
theorem B1488539 : Blo 988596 1488539 := bstep (se 1 (by rfl) ⟨1116404, by rfl⟩ : syracuseStep 1488539 = 2232809) B2232809
theorem B12859139 : Blo 988596 12859139 := bstep (se 1 (by rfl) ⟨9644354, by rfl⟩ : syracuseStep 12859139 = 19288709) B19288709
theorem B1488875 : Blo 988596 1488875 := bstep (se 1 (by rfl) ⟨1116656, by rfl⟩ : syracuseStep 1488875 = 2233313) B2233313
theorem B2505451 : Blo 988596 2505451 := bstep (se 1 (by rfl) ⟨1879088, by rfl⟩ : syracuseStep 2505451 = 3758177) B3758177
theorem B11451269 : Blo 988596 11451269 := bstep (se 4 (by rfl) ⟨1073556, by rfl⟩ : syracuseStep 11451269 = 2147113) B2147113
theorem B2505775 : Blo 988596 2505775 := bstep (se 1 (by rfl) ⟨1879331, by rfl⟩ : syracuseStep 2505775 = 3758663) B3758663
theorem B14302433 : Blo 988596 14302433 := bstep (se 2 (by rfl) ⟨5363412, by rfl⟩ : syracuseStep 14302433 = 10726825) B10726825
theorem B1588987 : Blo 988596 1588987 := bstep (se 1 (by rfl) ⟨1191740, by rfl⟩ : syracuseStep 1588987 = 2383481) B2383481
theorem B24723305 : Blo 988596 24723305 := bstep (se 2 (by rfl) ⟨9271239, by rfl⟩ : syracuseStep 24723305 = 18542479) B18542479
theorem B38027555 : Blo 988596 38027555 := bstep (se 1 (by rfl) ⟨28520666, by rfl⟩ : syracuseStep 38027555 = 57041333) B57041333
theorem B6341003 : Blo 988596 6341003 := bstep (se 1 (by rfl) ⟨4755752, by rfl⟩ : syracuseStep 6341003 = 9511505) B9511505
theorem B7520849 : Blo 988596 7520849 := bstep (se 2 (by rfl) ⟨2820318, by rfl⟩ : syracuseStep 7520849 = 5640637) B5640637
theorem B2507719 : Blo 988596 2507719 := bstep (se 1 (by rfl) ⟨1880789, by rfl⟩ : syracuseStep 2507719 = 3761579) B3761579
theorem B11453669 : Blo 988596 11453669 := bstep (se 4 (by rfl) ⟨1073781, by rfl⟩ : syracuseStep 11453669 = 2147563) B2147563
theorem B2377127 : Blo 988596 2377127 := bstep (se 1 (by rfl) ⟨1782845, by rfl⟩ : syracuseStep 2377127 = 3565691) B3565691
theorem B2115163 : Blo 988596 2115163 := bstep (se 1 (by rfl) ⟨1586372, by rfl⟩ : syracuseStep 2115163 = 3172745) B3172745
theorem B2508479 : Blo 988596 2508479 := bstep (se 1 (by rfl) ⟨1881359, by rfl⟩ : syracuseStep 2508479 = 3762719) B3762719
theorem B5359391 : Blo 988596 5359391 := bstep (se 1 (by rfl) ⟨4019543, by rfl⟩ : syracuseStep 5359391 = 8039087) B8039087
theorem B8473531 : Blo 988596 8473531 := bstep (se 1 (by rfl) ⟨6355148, by rfl⟩ : syracuseStep 8473531 = 12710297) B12710297
theorem B17157221 : Blo 988596 17157221 := bstep (se 4 (by rfl) ⟨1608489, by rfl⟩ : syracuseStep 17157221 = 3216979) B3216979
theorem B2510099 : Blo 988596 2510099 := bstep (se 1 (by rfl) ⟨1882574, by rfl⟩ : syracuseStep 2510099 = 3765149) B3765149
theorem B6442537 : Blo 988596 6442537 := bstep (se 2 (by rfl) ⟨2415951, by rfl⟩ : syracuseStep 6442537 = 4831903) B4831903
theorem B4509857 : Blo 988596 4509857 := bstep (se 2 (by rfl) ⟨1691196, by rfl⟩ : syracuseStep 4509857 = 3382393) B3382393
theorem B7622849 : Blo 988596 7622849 := bstep (se 2 (by rfl) ⟨2858568, by rfl⟩ : syracuseStep 7622849 = 5717137) B5717137
theorem B51433865 : Blo 988596 51433865 := bstep (se 2 (by rfl) ⟨19287699, by rfl⟩ : syracuseStep 51433865 = 38575399) B38575399
theorem B2118059 : Blo 988596 2118059 := bstep (se 1 (by rfl) ⟨1588544, by rfl⟩ : syracuseStep 2118059 = 3177089) B3177089
theorem B3756887 : Blo 988596 3756887 := bstep (se 1 (by rfl) ⟨2817665, by rfl⟩ : syracuseStep 3756887 = 5635331) B5635331
theorem B5724047 : Blo 988596 5724047 := bstep (se 1 (by rfl) ⟨4293035, by rfl⟩ : syracuseStep 5724047 = 8586071) B8586071
theorem B2676863 : Blo 988596 2676863 := bstep (se 1 (by rfl) ⟨2007647, by rfl⟩ : syracuseStep 2676863 = 4015295) B4015295
theorem B3758845 : Blo 988596 3758845 := bstep (se 3 (by rfl) ⟨704783, by rfl⟩ : syracuseStep 3758845 = 1409567) B1409567
theorem B12377117 : Blo 988596 12377117 := bstep (se 3 (by rfl) ⟨2320709, by rfl⟩ : syracuseStep 12377117 = 4641419) B4641419
theorem B11427065 : Blo 988596 11427065 := bstep (se 2 (by rfl) ⟨4285149, by rfl⟩ : syracuseStep 11427065 = 8570299) B8570299
theorem B176414021 : Blo 988596 176414021 := bstep (se 4 (by rfl) ⟨16538814, by rfl⟩ : syracuseStep 176414021 = 33077629) B33077629
theorem B12672571 : Blo 988596 12672571 := bstep (se 1 (by rfl) ⟨9504428, by rfl⟩ : syracuseStep 12672571 = 19008857) B19008857
theorem B3759803 : Blo 988596 3759803 := bstep (se 1 (by rfl) ⟨2819852, by rfl⟩ : syracuseStep 3759803 = 5639705) B5639705
theorem B7135073 : Blo 988596 7135073 := bstep (se 2 (by rfl) ⟨2675652, by rfl⟩ : syracuseStep 7135073 = 5351305) B5351305
theorem B4023047 : Blo 988596 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B7627529 : Blo 988596 7627529 := bstep (se 2 (by rfl) ⟨2860323, by rfl⟩ : syracuseStep 7627529 = 5720647) B5720647
theorem B3761063 : Blo 988596 3761063 := bstep (se 1 (by rfl) ⟨2820797, by rfl⟩ : syracuseStep 3761063 = 5641595) B5641595
theorem B3761261 : Blo 988596 3761261 := bstep (se 3 (by rfl) ⟨705236, by rfl⟩ : syracuseStep 3761261 = 1410473) B1410473
theorem B7529597 : Blo 988596 7529597 := bstep (se 3 (by rfl) ⟨1411799, by rfl⟩ : syracuseStep 7529597 = 2823599) B2823599
theorem B178120349 : Blo 988596 178120349 := bstep (se 3 (by rfl) ⟨33397565, by rfl⟩ : syracuseStep 178120349 = 66795131) B66795131
theorem B11265965 : Blo 988596 11265965 := bstep (se 3 (by rfl) ⟨2112368, by rfl⟩ : syracuseStep 11265965 = 4224737) B4224737
theorem B22047065 : Blo 988596 22047065 := bstep (se 2 (by rfl) ⟨8267649, by rfl⟩ : syracuseStep 22047065 = 16535299) B16535299
theorem B10874141 : Blo 988596 10874141 := bstep (se 3 (by rfl) ⟨2038901, by rfl⟩ : syracuseStep 10874141 = 4077803) B4077803
theorem B36171203 : Blo 988596 36171203 := bstep (se 1 (by rfl) ⟨27128402, by rfl⟩ : syracuseStep 36171203 = 54256805) B54256805
theorem B96431633 : Blo 988596 96431633 := bstep (se 2 (by rfl) ⟨36161862, by rfl⟩ : syracuseStep 96431633 = 72323725) B72323725
theorem B3010231 : Blo 988596 3010231 := bstep (se 1 (by rfl) ⟨2257673, by rfl⟩ : syracuseStep 3010231 = 4515347) B4515347
theorem B3010375 : Blo 988596 3010375 := bstep (se 1 (by rfl) ⟨2257781, by rfl⟩ : syracuseStep 3010375 = 4515563) B4515563
theorem B4223303 : Blo 988596 4223303 := bstep (se 1 (by rfl) ⟨3167477, by rfl⟩ : syracuseStep 4223303 = 6334955) B6334955
theorem B1503559 : Blo 988596 1503559 := bstep (se 1 (by rfl) ⟨1127669, by rfl⟩ : syracuseStep 1503559 = 2255339) B2255339
theorem B3339035 : Blo 988596 3339035 := bstep (se 1 (by rfl) ⟨2504276, by rfl⟩ : syracuseStep 3339035 = 5008553) B5008553
theorem B3339251 : Blo 988596 3339251 := bstep (se 1 (by rfl) ⟨2504438, by rfl⟩ : syracuseStep 3339251 = 5008877) B5008877
theorem B16905509 : Blo 988596 16905509 := bstep (se 4 (by rfl) ⟨1584891, by rfl⟩ : syracuseStep 16905509 = 3169783) B3169783
theorem B3339791 : Blo 988596 3339791 := bstep (se 1 (by rfl) ⟨2504843, by rfl⟩ : syracuseStep 3339791 = 5009687) B5009687
theorem B42825287 : Blo 988596 42825287 := bstep (se 1 (by rfl) ⟨32118965, by rfl⟩ : syracuseStep 42825287 = 64237931) B64237931
theorem B2225951 : Blo 988596 2225951 := bstep (se 1 (by rfl) ⟨1669463, by rfl⟩ : syracuseStep 2225951 = 3338927) B3338927
theorem B1668991 : Blo 988596 1668991 := bstep (se 1 (by rfl) ⟨1251743, by rfl⟩ : syracuseStep 1668991 = 2503487) B2503487
theorem B5437601 : Blo 988596 5437601 := bstep (se 2 (by rfl) ⟨2039100, by rfl⟩ : syracuseStep 5437601 = 4078201) B4078201
theorem B3766439 : Blo 988596 3766439 := bstep (se 1 (by rfl) ⟨2824829, by rfl⟩ : syracuseStep 3766439 = 5649659) B5649659
theorem B3340871 : Blo 988596 3340871 := bstep (se 1 (by rfl) ⟨2505653, by rfl⟩ : syracuseStep 3340871 = 5011307) B5011307
theorem B4225679 : Blo 988596 4225679 := bstep (se 1 (by rfl) ⟨3169259, by rfl⟩ : syracuseStep 4225679 = 6338519) B6338519
theorem B5635079 : Blo 988596 5635079 := bstep (se 1 (by rfl) ⟨4226309, by rfl⟩ : syracuseStep 5635079 = 8452619) B8452619
theorem B1113115 : Blo 988596 1113115 := bstep (se 1 (by rfl) ⟨834836, by rfl⟩ : syracuseStep 1113115 = 1669673) B1669673
theorem B2817449 : Blo 988596 2817449 := bstep (se 2 (by rfl) ⟨1056543, by rfl⟩ : syracuseStep 2817449 = 2113087) B2113087
theorem B1113583 : Blo 988596 1113583 := bstep (se 1 (by rfl) ⟨835187, by rfl⟩ : syracuseStep 1113583 = 1670375) B1670375
theorem B10747429 : Blo 988596 10747429 := bstep (se 4 (by rfl) ⟨1007571, by rfl⟩ : syracuseStep 10747429 = 2015143) B2015143
theorem B3210877 : Blo 988596 3210877 := bstep (se 3 (by rfl) ⟨602039, by rfl⟩ : syracuseStep 3210877 = 1204079) B1204079
theorem B2227895 : Blo 988596 2227895 := bstep (se 1 (by rfl) ⟨1670921, by rfl⟩ : syracuseStep 2227895 = 3341843) B3341843
theorem B1671401 : Blo 988596 1671401 := bstep (se 2 (by rfl) ⟨626775, by rfl⟩ : syracuseStep 1671401 = 1253551) B1253551
theorem B7536887 : Blo 988596 7536887 := bstep (se 1 (by rfl) ⟨5652665, by rfl⟩ : syracuseStep 7536887 = 11305331) B11305331
theorem B4227335 : Blo 988596 4227335 := bstep (se 1 (by rfl) ⟨3170501, by rfl⟩ : syracuseStep 4227335 = 6341003) B6341003
theorem B6422921 : Blo 988596 6422921 := bstep (se 2 (by rfl) ⟨2408595, by rfl⟩ : syracuseStep 6422921 = 4817191) B4817191
theorem B5013899 : Blo 988596 5013899 := bstep (se 1 (by rfl) ⟨3760424, by rfl⟩ : syracuseStep 5013899 = 7520849) B7520849
theorem B3342815 : Blo 988596 3342815 := bstep (se 1 (by rfl) ⟨2507111, by rfl⟩ : syracuseStep 3342815 = 5014223) B5014223
theorem B1114591 : Blo 988596 1114591 := bstep (se 1 (by rfl) ⟨835943, by rfl⟩ : syracuseStep 1114591 = 1671887) B1671887
theorem B10715753 : Blo 988596 10715753 := bstep (se 2 (by rfl) ⟨4018407, by rfl⟩ : syracuseStep 10715753 = 8036815) B8036815
theorem B2228903 : Blo 988596 2228903 := bstep (se 1 (by rfl) ⟨1671677, by rfl⟩ : syracuseStep 2228903 = 3343355) B3343355
theorem B229278485 : Blo 988596 229278485 := bstep (se 6 (by rfl) ⟨5373714, by rfl⟩ : syracuseStep 229278485 = 10747429) B10747429
theorem B7635779 : Blo 988596 7635779 := bstep (se 1 (by rfl) ⟨5726834, by rfl⟩ : syracuseStep 7635779 = 11453669) B11453669
theorem B1672319 : Blo 988596 1672319 := bstep (se 1 (by rfl) ⟨1254239, by rfl⟩ : syracuseStep 1672319 = 2508479) B2508479
theorem B3572927 : Blo 988596 3572927 := bstep (se 1 (by rfl) ⟨2679695, by rfl⟩ : syracuseStep 3572927 = 5359391) B5359391
theorem B3343625 : Blo 988596 3343625 := bstep (se 2 (by rfl) ⟨1253859, by rfl⟩ : syracuseStep 3343625 = 2507719) B2507719
theorem B7145135 : Blo 988596 7145135 := bstep (se 1 (by rfl) ⟨5358851, by rfl⟩ : syracuseStep 7145135 = 10717703) B10717703
theorem B3344111 : Blo 988596 3344111 := bstep (se 1 (by rfl) ⟨2508083, by rfl⟩ : syracuseStep 3344111 = 5016167) B5016167
theorem B1673257 : Blo 988596 1673257 := bstep (se 2 (by rfl) ⟨627471, by rfl⟩ : syracuseStep 1673257 = 1254943) B1254943
theorem B11438147 : Blo 988596 11438147 := bstep (se 1 (by rfl) ⟨8578610, by rfl⟩ : syracuseStep 11438147 = 17157221) B17157221
theorem B2820217 : Blo 988596 2820217 := bstep (se 2 (by rfl) ⟨1057581, by rfl⟩ : syracuseStep 2820217 = 2115163) B2115163
theorem B1673399 : Blo 988596 1673399 := bstep (se 1 (by rfl) ⟨1255049, by rfl⟩ : syracuseStep 1673399 = 2510099) B2510099
theorem B2230631 : Blo 988596 2230631 := bstep (se 1 (by rfl) ⟨1672973, by rfl⟩ : syracuseStep 2230631 = 3345947) B3345947
theorem B1116607 : Blo 988596 1116607 := bstep (se 1 (by rfl) ⟨837455, by rfl⟩ : syracuseStep 1116607 = 1674911) B1674911
theorem B2231207 : Blo 988596 2231207 := bstep (se 1 (by rfl) ⟨1673405, by rfl⟩ : syracuseStep 2231207 = 3346811) B3346811
theorem B1412039 : Blo 988596 1412039 := bstep (se 1 (by rfl) ⟨1059029, by rfl⟩ : syracuseStep 1412039 = 2118059) B2118059
theorem B2232737 : Blo 988596 2232737 := bstep (se 2 (by rfl) ⟨837276, by rfl⟩ : syracuseStep 2232737 = 1674553) B1674553
theorem B68686289 : Blo 988596 68686289 := bstep (se 2 (by rfl) ⟨25757358, by rfl⟩ : syracuseStep 68686289 = 51514717) B51514717
theorem B3347135 : Blo 988596 3347135 := bstep (se 1 (by rfl) ⟨2510351, by rfl⟩ : syracuseStep 3347135 = 5020703) B5020703
theorem B8590049 : Blo 988596 8590049 := bstep (se 2 (by rfl) ⟨3221268, by rfl⟩ : syracuseStep 8590049 = 6442537) B6442537
theorem B2233097 : Blo 988596 2233097 := bstep (se 2 (by rfl) ⟨837411, by rfl⟩ : syracuseStep 2233097 = 1674823) B1674823
theorem B117609347 : Blo 988596 117609347 := bstep (se 1 (by rfl) ⟨88207010, by rfl⟩ : syracuseStep 117609347 = 176414021) B176414021
theorem B4756715 : Blo 988596 4756715 := bstep (se 1 (by rfl) ⟨3567536, by rfl⟩ : syracuseStep 4756715 = 7135073) B7135073
theorem B988623 : Blo 988596 988623 := bstep (se 1 (by rfl) ⟨741467, by rfl⟩ : syracuseStep 988623 = 1482935) B1482935
theorem B988703 : Blo 988596 988703 := bstep (se 1 (by rfl) ⟨741527, by rfl⟩ : syracuseStep 988703 = 1483055) B1483055
theorem B988863 : Blo 988596 988863 := bstep (se 1 (by rfl) ⟨741647, by rfl⟩ : syracuseStep 988863 = 1483295) B1483295
theorem B25695953 : Blo 988596 25695953 := bstep (se 2 (by rfl) ⟨9635982, by rfl⟩ : syracuseStep 25695953 = 19271965) B19271965
theorem B988903 : Blo 988596 988903 := bstep (se 1 (by rfl) ⟨741677, by rfl⟩ : syracuseStep 988903 = 1483355) B1483355
theorem B2004745 : Blo 988596 2004745 := bstep (se 2 (by rfl) ⟨751779, by rfl⟩ : syracuseStep 2004745 = 1503559) B1503559
theorem B5085019 : Blo 988596 5085019 := bstep (se 1 (by rfl) ⟨3813764, by rfl⟩ : syracuseStep 5085019 = 7627529) B7627529
theorem B989247 : Blo 988596 989247 := bstep (se 1 (by rfl) ⟨741935, by rfl⟩ : syracuseStep 989247 = 1483871) B1483871
theorem B5019731 : Blo 988596 5019731 := bstep (se 1 (by rfl) ⟨3764798, by rfl⟩ : syracuseStep 5019731 = 7529597) B7529597
theorem B989287 : Blo 988596 989287 := bstep (se 1 (by rfl) ⟨741965, by rfl⟩ : syracuseStep 989287 = 1483931) B1483931
theorem B989595 : Blo 988596 989595 := bstep (se 1 (by rfl) ⟨742196, by rfl⟩ : syracuseStep 989595 = 1484393) B1484393
theorem B989679 : Blo 988596 989679 := bstep (se 1 (by rfl) ⟨742259, by rfl⟩ : syracuseStep 989679 = 1484519) B1484519
theorem B989743 : Blo 988596 989743 := bstep (se 1 (by rfl) ⟨742307, by rfl⟩ : syracuseStep 989743 = 1484615) B1484615
theorem B7510643 : Blo 988596 7510643 := bstep (se 1 (by rfl) ⟨5632982, by rfl⟩ : syracuseStep 7510643 = 11265965) B11265965
theorem B990015 : Blo 988596 990015 := bstep (se 1 (by rfl) ⟨742511, by rfl⟩ : syracuseStep 990015 = 1485023) B1485023
theorem B990055 : Blo 988596 990055 := bstep (se 1 (by rfl) ⟨742541, by rfl⟩ : syracuseStep 990055 = 1485083) B1485083
theorem B990143 : Blo 988596 990143 := bstep (se 1 (by rfl) ⟨742607, by rfl⟩ : syracuseStep 990143 = 1485215) B1485215
theorem B8461367 : Blo 988596 8461367 := bstep (se 1 (by rfl) ⟨6346025, by rfl⟩ : syracuseStep 8461367 = 12692051) B12692051
theorem B990271 : Blo 988596 990271 := bstep (se 1 (by rfl) ⟨742703, by rfl⟩ : syracuseStep 990271 = 1485407) B1485407
theorem B990491 : Blo 988596 990491 := bstep (se 1 (by rfl) ⟨742868, by rfl⟩ : syracuseStep 990491 = 1485737) B1485737
theorem B990511 : Blo 988596 990511 := bstep (se 1 (by rfl) ⟨742883, by rfl⟩ : syracuseStep 990511 = 1485767) B1485767
theorem B990591 : Blo 988596 990591 := bstep (se 1 (by rfl) ⟨742943, by rfl⟩ : syracuseStep 990591 = 1485887) B1485887
theorem B7249427 : Blo 988596 7249427 := bstep (se 1 (by rfl) ⟨5437070, by rfl⟩ : syracuseStep 7249427 = 10874141) B10874141
theorem B1056287 : Blo 988596 1056287 := bstep (se 1 (by rfl) ⟨792215, by rfl⟩ : syracuseStep 1056287 = 1584431) B1584431
theorem B990751 : Blo 988596 990751 := bstep (se 1 (by rfl) ⟨743063, by rfl⟩ : syracuseStep 990751 = 1486127) B1486127
theorem B990875 : Blo 988596 990875 := bstep (se 1 (by rfl) ⟨743156, by rfl⟩ : syracuseStep 990875 = 1486313) B1486313
theorem B990911 : Blo 988596 990911 := bstep (se 1 (by rfl) ⟨743183, by rfl⟩ : syracuseStep 990911 = 1486367) B1486367
theorem B990971 : Blo 988596 990971 := bstep (se 1 (by rfl) ⟨743228, by rfl⟩ : syracuseStep 990971 = 1486457) B1486457
theorem B991135 : Blo 988596 991135 := bstep (se 1 (by rfl) ⟨743351, by rfl⟩ : syracuseStep 991135 = 1486703) B1486703
theorem B991303 : Blo 988596 991303 := bstep (se 1 (by rfl) ⟨743477, by rfl⟩ : syracuseStep 991303 = 1486955) B1486955
theorem B991591 : Blo 988596 991591 := bstep (se 1 (by rfl) ⟨743693, by rfl⟩ : syracuseStep 991591 = 1487387) B1487387
theorem B991711 : Blo 988596 991711 := bstep (se 1 (by rfl) ⟨743783, by rfl⟩ : syracuseStep 991711 = 1487567) B1487567
theorem B991903 : Blo 988596 991903 := bstep (se 1 (by rfl) ⟨743927, by rfl⟩ : syracuseStep 991903 = 1487855) B1487855
theorem B992159 : Blo 988596 992159 := bstep (se 1 (by rfl) ⟨744119, by rfl⟩ : syracuseStep 992159 = 1488239) B1488239
theorem B992239 : Blo 988596 992239 := bstep (se 1 (by rfl) ⟨744179, by rfl⟩ : syracuseStep 992239 = 1488359) B1488359
theorem B28550191 : Blo 988596 28550191 := bstep (se 1 (by rfl) ⟨21412643, by rfl⟩ : syracuseStep 28550191 = 42825287) B42825287
theorem B992359 : Blo 988596 992359 := bstep (se 1 (by rfl) ⟨744269, by rfl⟩ : syracuseStep 992359 = 1488539) B1488539
theorem B1483967 : Blo 988596 1483967 := bstep (se 1 (by rfl) ⟨1112975, by rfl⟩ : syracuseStep 1483967 = 2225951) B2225951
theorem B992583 : Blo 988596 992583 := bstep (se 1 (by rfl) ⟨744437, by rfl⟩ : syracuseStep 992583 = 1488875) B1488875
theorem B1484153 : Blo 988596 1484153 := bstep (se 2 (by rfl) ⟨556557, by rfl⟩ : syracuseStep 1484153 = 1113115) B1113115
theorem B1484777 : Blo 988596 1484777 := bstep (se 2 (by rfl) ⟨556791, by rfl⟩ : syracuseStep 1484777 = 1113583) B1113583
theorem B1878299 : Blo 988596 1878299 := bstep (se 1 (by rfl) ⟨1408724, by rfl⟩ : syracuseStep 1878299 = 2817449) B2817449
theorem B1485263 : Blo 988596 1485263 := bstep (se 1 (by rfl) ⟨1113947, by rfl⟩ : syracuseStep 1485263 = 2227895) B2227895
theorem B20327597 : Blo 988596 20327597 := bstep (se 3 (by rfl) ⟨3811424, by rfl⟩ : syracuseStep 20327597 = 7622849) B7622849
theorem B1486031 : Blo 988596 1486031 := bstep (se 1 (by rfl) ⟨1114523, by rfl⟩ : syracuseStep 1486031 = 2229047) B2229047
theorem B1486151 : Blo 988596 1486151 := bstep (se 1 (by rfl) ⟨1114613, by rfl⟩ : syracuseStep 1486151 = 2229227) B2229227
theorem B1486601 : Blo 988596 1486601 := bstep (se 2 (by rfl) ⟨557475, by rfl⟩ : syracuseStep 1486601 = 1114951) B1114951
theorem B1486751 : Blo 988596 1486751 := bstep (se 1 (by rfl) ⟨1115063, by rfl⟩ : syracuseStep 1486751 = 2230127) B2230127
theorem B1486823 : Blo 988596 1486823 := bstep (se 1 (by rfl) ⟨1115117, by rfl⟩ : syracuseStep 1486823 = 2230235) B2230235
theorem B1486895 : Blo 988596 1486895 := bstep (se 1 (by rfl) ⟨1115171, by rfl⟩ : syracuseStep 1486895 = 2230343) B2230343
theorem B1486943 : Blo 988596 1486943 := bstep (se 1 (by rfl) ⟨1115207, by rfl⟩ : syracuseStep 1486943 = 2230415) B2230415
theorem B1487003 : Blo 988596 1487003 := bstep (se 1 (by rfl) ⟨1115252, by rfl⟩ : syracuseStep 1487003 = 2230505) B2230505
theorem B1487015 : Blo 988596 1487015 := bstep (se 1 (by rfl) ⟨1115261, by rfl⟩ : syracuseStep 1487015 = 2230523) B2230523
theorem B1487183 : Blo 988596 1487183 := bstep (se 1 (by rfl) ⟨1115387, by rfl⟩ : syracuseStep 1487183 = 2230775) B2230775
theorem B10728125 : Blo 988596 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B1487849 : Blo 988596 1487849 := bstep (se 2 (by rfl) ⟨557943, by rfl⟩ : syracuseStep 1487849 = 1115887) B1115887
theorem B34289243 : Blo 988596 34289243 := bstep (se 1 (by rfl) ⟨25716932, by rfl⟩ : syracuseStep 34289243 = 51433865) B51433865
theorem B1488521 : Blo 988596 1488521 := bstep (se 2 (by rfl) ⟨558195, by rfl⟩ : syracuseStep 1488521 = 1116391) B1116391
theorem B5093131 : Blo 988596 5093131 := bstep (se 1 (by rfl) ⟨3819848, by rfl⟩ : syracuseStep 5093131 = 7639697) B7639697
theorem B2504591 : Blo 988596 2504591 := bstep (se 1 (by rfl) ⟨1878443, by rfl⟩ : syracuseStep 2504591 = 3756887) B3756887
theorem B7518419 : Blo 988596 7518419 := bstep (se 1 (by rfl) ⟨5638814, by rfl⟩ : syracuseStep 7518419 = 11277629) B11277629
theorem B6339005 : Blo 988596 6339005 := bstep (se 3 (by rfl) ⟨1188563, by rfl⟩ : syracuseStep 6339005 = 2377127) B2377127
theorem B3816031 : Blo 988596 3816031 := bstep (se 1 (by rfl) ⟨2862023, by rfl⟩ : syracuseStep 3816031 = 5724047) B5724047
theorem B1784575 : Blo 988596 1784575 := bstep (se 1 (by rfl) ⟨1338431, by rfl⟩ : syracuseStep 1784575 = 2676863) B2676863
theorem B10861523 : Blo 988596 10861523 := bstep (se 1 (by rfl) ⟨8146142, by rfl⟩ : syracuseStep 10861523 = 16292285) B16292285
theorem B1883387 : Blo 988596 1883387 := bstep (se 1 (by rfl) ⟨1412540, by rfl⟩ : syracuseStep 1883387 = 2825081) B2825081
theorem B7618043 : Blo 988596 7618043 := bstep (se 1 (by rfl) ⟨5713532, by rfl⟩ : syracuseStep 7618043 = 11427065) B11427065
theorem B4013641 : Blo 988596 4013641 := bstep (se 2 (by rfl) ⟨1505115, by rfl⟩ : syracuseStep 4013641 = 3010231) B3010231
theorem B2506535 : Blo 988596 2506535 := bstep (se 1 (by rfl) ⟨1879901, by rfl⟩ : syracuseStep 2506535 = 3759803) B3759803
theorem B7127399 : Blo 988596 7127399 := bstep (se 1 (by rfl) ⟨5345549, by rfl⟩ : syracuseStep 7127399 = 10691099) B10691099
theorem B2507375 : Blo 988596 2507375 := bstep (se 1 (by rfl) ⟨1880531, by rfl⟩ : syracuseStep 2507375 = 3761063) B3761063
theorem B16302791 : Blo 988596 16302791 := bstep (se 1 (by rfl) ⟨12227093, by rfl⟩ : syracuseStep 16302791 = 24454187) B24454187
theorem B2507507 : Blo 988596 2507507 := bstep (se 1 (by rfl) ⟨1880630, by rfl⟩ : syracuseStep 2507507 = 3761261) B3761261
theorem B15254315 : Blo 988596 15254315 := bstep (se 1 (by rfl) ⟨11440736, by rfl⟩ : syracuseStep 15254315 = 22881473) B22881473
theorem B6013939 : Blo 988596 6013939 := bstep (se 1 (by rfl) ⟨4510454, by rfl⟩ : syracuseStep 6013939 = 9020909) B9020909
theorem B14698043 : Blo 988596 14698043 := bstep (se 1 (by rfl) ⟨11023532, by rfl⟩ : syracuseStep 14698043 = 22047065) B22047065
theorem B7523279 : Blo 988596 7523279 := bstep (se 1 (by rfl) ⟨5642459, by rfl⟩ : syracuseStep 7523279 = 11284919) B11284919
theorem B8572759 : Blo 988596 8572759 := bstep (se 1 (by rfl) ⟨6429569, by rfl⟩ : syracuseStep 8572759 = 12859139) B12859139
theorem B96456541 : Blo 988596 96456541 := bstep (se 3 (by rfl) ⟨18085601, by rfl⟩ : syracuseStep 96456541 = 36171203) B36171203
theorem B3625067 : Blo 988596 3625067 := bstep (se 1 (by rfl) ⟨2718800, by rfl⟩ : syracuseStep 3625067 = 5437601) B5437601
theorem B2510959 : Blo 988596 2510959 := bstep (se 1 (by rfl) ⟨1883219, by rfl⟩ : syracuseStep 2510959 = 3766439) B3766439
theorem B3756719 : Blo 988596 3756719 := bstep (se 1 (by rfl) ⟨2817539, by rfl⟩ : syracuseStep 3756719 = 5635079) B5635079
theorem B16896761 : Blo 988596 16896761 := bstep (se 2 (by rfl) ⟨6336285, by rfl⟩ : syracuseStep 16896761 = 12672571) B12672571
theorem B4281169 : Blo 988596 4281169 := bstep (se 2 (by rfl) ⟨1605438, by rfl⟩ : syracuseStep 4281169 = 3210877) B3210877
theorem B2118649 : Blo 988596 2118649 := bstep (se 2 (by rfl) ⟨794493, by rfl⟩ : syracuseStep 2118649 = 1588987) B1588987
theorem B25351703 : Blo 988596 25351703 := bstep (se 1 (by rfl) ⟨19013777, by rfl⟩ : syracuseStep 25351703 = 38027555) B38027555
theorem B8477905 : Blo 988596 8477905 := bstep (se 2 (by rfl) ⟨3179214, by rfl⟩ : syracuseStep 8477905 = 6358429) B6358429
theorem B3759635 : Blo 988596 3759635 := bstep (se 1 (by rfl) ⟨2819726, by rfl⟩ : syracuseStep 3759635 = 5639453) B5639453
theorem B3006571 : Blo 988596 3006571 := bstep (se 1 (by rfl) ⟨2254928, by rfl⟩ : syracuseStep 3006571 = 4509857) B4509857
theorem B4022399 : Blo 988596 4022399 := bstep (se 1 (by rfl) ⟨3016799, by rfl⟩ : syracuseStep 4022399 = 6033599) B6033599
theorem B3760303 : Blo 988596 3760303 := bstep (se 1 (by rfl) ⟨2820227, by rfl⟩ : syracuseStep 3760303 = 5640455) B5640455
theorem B9528191 : Blo 988596 9528191 := bstep (se 1 (by rfl) ⟨7146143, by rfl⟩ : syracuseStep 9528191 = 14292287) B14292287
theorem B10708145 : Blo 988596 10708145 := bstep (se 2 (by rfl) ⟨4015554, by rfl⟩ : syracuseStep 10708145 = 8031109) B8031109
theorem B11298041 : Blo 988596 11298041 := bstep (se 2 (by rfl) ⟨4236765, by rfl⟩ : syracuseStep 11298041 = 8473531) B8473531
theorem B8251411 : Blo 988596 8251411 := bstep (se 1 (by rfl) ⟨6188558, by rfl⟩ : syracuseStep 8251411 = 12377117) B12377117
theorem B45705293 : Blo 988596 45705293 := bstep (se 3 (by rfl) ⟨8569742, by rfl⟩ : syracuseStep 45705293 = 17139485) B17139485
theorem B4024475 : Blo 988596 4024475 := bstep (se 1 (by rfl) ⟨3018356, by rfl⟩ : syracuseStep 4024475 = 6036713) B6036713
theorem B3762551 : Blo 988596 3762551 := bstep (se 1 (by rfl) ⟨2821913, by rfl⟩ : syracuseStep 3762551 = 5643827) B5643827
theorem B6351641 : Blo 988596 6351641 := bstep (se 2 (by rfl) ⟨2381865, by rfl⟩ : syracuseStep 6351641 = 4763731) B4763731
theorem B118746899 : Blo 988596 118746899 := bstep (se 1 (by rfl) ⟨89060174, by rfl⟩ : syracuseStep 118746899 = 178120349) B178120349
theorem B3338009 : Blo 988596 3338009 := bstep (se 2 (by rfl) ⟨1251753, by rfl⟩ : syracuseStep 3338009 = 2503507) B2503507
theorem B5009363 : Blo 988596 5009363 := bstep (se 1 (by rfl) ⟨3757022, by rfl⟩ : syracuseStep 5009363 = 7514045) B7514045
theorem B3338657 : Blo 988596 3338657 := bstep (se 2 (by rfl) ⟨1251996, by rfl⟩ : syracuseStep 3338657 = 2503993) B2503993
theorem B64287755 : Blo 988596 64287755 := bstep (se 1 (by rfl) ⟨48215816, by rfl⟩ : syracuseStep 64287755 = 96431633) B96431633
theorem B2225321 : Blo 988596 2225321 := bstep (se 2 (by rfl) ⟨834495, by rfl⟩ : syracuseStep 2225321 = 1668991) B1668991
theorem B3765467 : Blo 988596 3765467 := bstep (se 1 (by rfl) ⟨2824100, by rfl⟩ : syracuseStep 3765467 = 5648201) B5648201
theorem B54162695 : Blo 988596 54162695 := bstep (se 1 (by rfl) ⟨40622021, by rfl⟩ : syracuseStep 54162695 = 81244043) B81244043
theorem B11302415 : Blo 988596 11302415 := bstep (se 1 (by rfl) ⟨8476811, by rfl⟩ : syracuseStep 11302415 = 16953623) B16953623
theorem B2815535 : Blo 988596 2815535 := bstep (se 1 (by rfl) ⟨2111651, by rfl⟩ : syracuseStep 2815535 = 4223303) B4223303
theorem B2226023 : Blo 988596 2226023 := bstep (se 1 (by rfl) ⟨1669517, by rfl⟩ : syracuseStep 2226023 = 3339035) B3339035
theorem B2226167 : Blo 988596 2226167 := bstep (se 1 (by rfl) ⟨1669625, by rfl⟩ : syracuseStep 2226167 = 3339251) B3339251
theorem B1669241 : Blo 988596 1669241 := bstep (se 2 (by rfl) ⟨625965, by rfl⟩ : syracuseStep 1669241 = 1251931) B1251931
theorem B1669295 : Blo 988596 1669295 := bstep (se 1 (by rfl) ⟨1251971, by rfl⟩ : syracuseStep 1669295 = 2503943) B2503943
theorem B11270339 : Blo 988596 11270339 := bstep (se 1 (by rfl) ⟨8452754, by rfl⟩ : syracuseStep 11270339 = 16905509) B16905509
theorem B12876029 : Blo 988596 12876029 := bstep (se 3 (by rfl) ⟨2414255, by rfl⟩ : syracuseStep 12876029 = 4828511) B4828511
theorem B3340601 : Blo 988596 3340601 := bstep (se 2 (by rfl) ⟨1252725, by rfl⟩ : syracuseStep 3340601 = 2505451) B2505451
theorem B3766607 : Blo 988596 3766607 := bstep (se 1 (by rfl) ⟨2824955, by rfl⟩ : syracuseStep 3766607 = 5649911) B5649911
theorem B5011793 : Blo 988596 5011793 := bstep (se 2 (by rfl) ⟨1879422, by rfl⟩ : syracuseStep 5011793 = 3758845) B3758845
theorem B2226527 : Blo 988596 2226527 := bstep (se 1 (by rfl) ⟨1669895, by rfl⟩ : syracuseStep 2226527 = 3339791) B3339791
theorem B3341033 : Blo 988596 3341033 := bstep (se 2 (by rfl) ⟨1252887, by rfl⟩ : syracuseStep 3341033 = 2505775) B2505775
theorem B16055333 : Blo 988596 16055333 := bstep (se 4 (by rfl) ⟨1505187, by rfl⟩ : syracuseStep 16055333 = 3010375) B3010375
theorem B2227247 : Blo 988596 2227247 := bstep (se 1 (by rfl) ⟨1670435, by rfl⟩ : syracuseStep 2227247 = 3340871) B3340871
theorem B2817119 : Blo 988596 2817119 := bstep (se 1 (by rfl) ⟨2112839, by rfl⟩ : syracuseStep 2817119 = 4225679) B4225679
theorem B7634179 : Blo 988596 7634179 := bstep (se 1 (by rfl) ⟨5725634, by rfl⟩ : syracuseStep 7634179 = 11451269) B11451269
theorem B9534955 : Blo 988596 9534955 := bstep (se 1 (by rfl) ⟨7151216, by rfl⟩ : syracuseStep 9534955 = 14302433) B14302433
theorem B16482203 : Blo 988596 16482203 := bstep (se 1 (by rfl) ⟨12361652, by rfl⟩ : syracuseStep 16482203 = 24723305) B24723305
theorem B1114267 : Blo 988596 1114267 := bstep (se 1 (by rfl) ⟨835700, by rfl⟩ : syracuseStep 1114267 = 1671401) B1671401
theorem B2818223 : Blo 988596 2818223 := bstep (se 1 (by rfl) ⟨2113667, by rfl⟩ : syracuseStep 2818223 = 4227335) B4227335
theorem B5013737 : Blo 988596 5013737 := bstep (se 2 (by rfl) ⟨1880151, by rfl⟩ : syracuseStep 5013737 = 3760303) B3760303
theorem B3342599 : Blo 988596 3342599 := bstep (se 1 (by rfl) ⟨2506949, by rfl⟩ : syracuseStep 3342599 = 5013899) B5013899
theorem B2228543 : Blo 988596 2228543 := bstep (se 1 (by rfl) ⟨1671407, by rfl⟩ : syracuseStep 2228543 = 3342815) B3342815
theorem B1671583 : Blo 988596 1671583 := bstep (se 1 (by rfl) ⟨1253687, by rfl⟩ : syracuseStep 1671583 = 2507375) B2507375
theorem B1671671 : Blo 988596 1671671 := bstep (se 1 (by rfl) ⟨1253753, by rfl⟩ : syracuseStep 1671671 = 2507507) B2507507
theorem B1114879 : Blo 988596 1114879 := bstep (se 1 (by rfl) ⟨836159, by rfl⟩ : syracuseStep 1114879 = 1672319) B1672319
theorem B2229083 : Blo 988596 2229083 := bstep (se 1 (by rfl) ⟨1671812, by rfl⟩ : syracuseStep 2229083 = 3343625) B3343625
theorem B19006397 : Blo 988596 19006397 := bstep (se 3 (by rfl) ⟨3563699, by rfl⟩ : syracuseStep 19006397 = 7127399) B7127399
theorem B9798695 : Blo 988596 9798695 := bstep (se 1 (by rfl) ⟨7349021, by rfl⟩ : syracuseStep 9798695 = 14698043) B14698043
theorem B2229407 : Blo 988596 2229407 := bstep (se 1 (by rfl) ⟨1672055, by rfl⟩ : syracuseStep 2229407 = 3344111) B3344111
theorem B1115599 : Blo 988596 1115599 := bstep (se 1 (by rfl) ⟨836699, by rfl⟩ : syracuseStep 1115599 = 1673399) B1673399
theorem B28575341 : Blo 988596 28575341 := bstep (se 3 (by rfl) ⟨5357876, by rfl⟩ : syracuseStep 28575341 = 10715753) B10715753
theorem B5015519 : Blo 988596 5015519 := bstep (se 1 (by rfl) ⟨3761639, by rfl⟩ : syracuseStep 5015519 = 7523279) B7523279
theorem B313624925 : Blo 988596 313624925 := bstep (se 3 (by rfl) ⟨58804673, by rfl⟩ : syracuseStep 313624925 = 117609347) B117609347
theorem B2231009 : Blo 988596 2231009 := bstep (se 2 (by rfl) ⟨836628, by rfl⟩ : syracuseStep 2231009 = 1673257) B1673257
theorem B2231423 : Blo 988596 2231423 := bstep (se 1 (by rfl) ⟨1673567, by rfl⟩ : syracuseStep 2231423 = 3347135) B3347135
theorem B3346487 : Blo 988596 3346487 := bstep (se 1 (by rfl) ⟨2509865, by rfl⟩ : syracuseStep 3346487 = 5019731) B5019731
theorem B5640911 : Blo 988596 5640911 := bstep (se 1 (by rfl) ⟨4230683, by rfl⟩ : syracuseStep 5640911 = 8461367) B8461367
theorem B3347945 : Blo 988596 3347945 := bstep (se 2 (by rfl) ⟨1255479, by rfl⟩ : syracuseStep 3347945 = 2510959) B2510959
theorem B989311 : Blo 988596 989311 := bstep (se 1 (by rfl) ⟨741983, by rfl⟩ : syracuseStep 989311 = 1483967) B1483967
theorem B989435 : Blo 988596 989435 := bstep (se 1 (by rfl) ⟨742076, by rfl⟩ : syracuseStep 989435 = 1484153) B1484153
theorem B5708225 : Blo 988596 5708225 := bstep (se 2 (by rfl) ⟨2140584, by rfl⟩ : syracuseStep 5708225 = 4281169) B4281169
theorem B989851 : Blo 988596 989851 := bstep (se 1 (by rfl) ⟨742388, by rfl⟩ : syracuseStep 989851 = 1484777) B1484777
theorem B2824865 : Blo 988596 2824865 := bstep (se 2 (by rfl) ⟨1059324, by rfl⟩ : syracuseStep 2824865 = 2118649) B2118649
theorem B1252199 : Blo 988596 1252199 := bstep (se 1 (by rfl) ⟨939149, by rfl⟩ : syracuseStep 1252199 = 1878299) B1878299
theorem B990175 : Blo 988596 990175 := bstep (se 1 (by rfl) ⟨742631, by rfl⟩ : syracuseStep 990175 = 1485263) B1485263
theorem B4234427 : Blo 988596 4234427 := bstep (se 1 (by rfl) ⟨3175820, by rfl⟩ : syracuseStep 4234427 = 6351641) B6351641
theorem B990687 : Blo 988596 990687 := bstep (se 1 (by rfl) ⟨743015, by rfl⟩ : syracuseStep 990687 = 1486031) B1486031
theorem B990767 : Blo 988596 990767 := bstep (se 1 (by rfl) ⟨743075, by rfl⟩ : syracuseStep 990767 = 1486151) B1486151
theorem B6790841 : Blo 988596 6790841 := bstep (se 2 (by rfl) ⟨2546565, by rfl⟩ : syracuseStep 6790841 = 5093131) B5093131
theorem B991067 : Blo 988596 991067 := bstep (se 1 (by rfl) ⟨743300, by rfl⟩ : syracuseStep 991067 = 1486601) B1486601
theorem B991167 : Blo 988596 991167 := bstep (se 1 (by rfl) ⟨743375, by rfl⟩ : syracuseStep 991167 = 1486751) B1486751
theorem B991215 : Blo 988596 991215 := bstep (se 1 (by rfl) ⟨743411, by rfl⟩ : syracuseStep 991215 = 1486823) B1486823
theorem B991263 : Blo 988596 991263 := bstep (se 1 (by rfl) ⟨743447, by rfl⟩ : syracuseStep 991263 = 1486895) B1486895
theorem B991295 : Blo 988596 991295 := bstep (se 1 (by rfl) ⟨743471, by rfl⟩ : syracuseStep 991295 = 1486943) B1486943
theorem B991335 : Blo 988596 991335 := bstep (se 1 (by rfl) ⟨743501, by rfl⟩ : syracuseStep 991335 = 1487003) B1487003
theorem B991343 : Blo 988596 991343 := bstep (se 1 (by rfl) ⟨743507, by rfl⟩ : syracuseStep 991343 = 1487015) B1487015
theorem B991455 : Blo 988596 991455 := bstep (se 1 (by rfl) ⟨743591, by rfl⟩ : syracuseStep 991455 = 1487183) B1487183
theorem B7152083 : Blo 988596 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B991899 : Blo 988596 991899 := bstep (se 1 (by rfl) ⟨743924, by rfl⟩ : syracuseStep 991899 = 1487849) B1487849
theorem B1483547 : Blo 988596 1483547 := bstep (se 1 (by rfl) ⟨1112660, by rfl⟩ : syracuseStep 1483547 = 2225321) B2225321
theorem B5088041 : Blo 988596 5088041 := bstep (se 2 (by rfl) ⟨1908015, by rfl⟩ : syracuseStep 5088041 = 3816031) B3816031
theorem B1877023 : Blo 988596 1877023 := bstep (se 1 (by rfl) ⟨1407767, by rfl⟩ : syracuseStep 1877023 = 2815535) B2815535
theorem B992347 : Blo 988596 992347 := bstep (se 1 (by rfl) ⟨744260, by rfl⟩ : syracuseStep 992347 = 1488521) B1488521
theorem B1484015 : Blo 988596 1484015 := bstep (se 1 (by rfl) ⟨1113011, by rfl⟩ : syracuseStep 1484015 = 2226023) B2226023
theorem B1484111 : Blo 988596 1484111 := bstep (se 1 (by rfl) ⟨1113083, by rfl⟩ : syracuseStep 1484111 = 2226167) B2226167
theorem B7513559 : Blo 988596 7513559 := bstep (se 1 (by rfl) ⟨5635169, by rfl⟩ : syracuseStep 7513559 = 11270339) B11270339
theorem B1484351 : Blo 988596 1484351 := bstep (se 1 (by rfl) ⟨1113263, by rfl⟩ : syracuseStep 1484351 = 2226527) B2226527
theorem B45721381 : Blo 988596 45721381 := bstep (se 4 (by rfl) ⟨4286379, by rfl⟩ : syracuseStep 45721381 = 8572759) B8572759
theorem B1484831 : Blo 988596 1484831 := bstep (se 1 (by rfl) ⟨1113623, by rfl⟩ : syracuseStep 1484831 = 2227247) B2227247
theorem B1878079 : Blo 988596 1878079 := bstep (se 1 (by rfl) ⟨1408559, by rfl⟩ : syracuseStep 1878079 = 2817119) B2817119
theorem B5351521 : Blo 988596 5351521 := bstep (se 2 (by rfl) ⟨2006820, by rfl⟩ : syracuseStep 5351521 = 4013641) B4013641
theorem B1255591 : Blo 988596 1255591 := bstep (se 1 (by rfl) ⟨941693, by rfl⟩ : syracuseStep 1255591 = 1883387) B1883387
theorem B10988135 : Blo 988596 10988135 := bstep (se 1 (by rfl) ⟨8241101, by rfl⟩ : syracuseStep 10988135 = 16482203) B16482203
theorem B4008761 : Blo 988596 4008761 := bstep (se 2 (by rfl) ⟨1503285, by rfl⟩ : syracuseStep 4008761 = 3006571) B3006571
theorem B5024591 : Blo 988596 5024591 := bstep (se 1 (by rfl) ⟨3768443, by rfl⟩ : syracuseStep 5024591 = 7536887) B7536887
theorem B1485935 : Blo 988596 1485935 := bstep (se 1 (by rfl) ⟨1114451, by rfl⟩ : syracuseStep 1485935 = 2228903) B2228903
theorem B10169543 : Blo 988596 10169543 := bstep (se 1 (by rfl) ⟨7627157, by rfl⟩ : syracuseStep 10169543 = 15254315) B15254315
theorem B5090519 : Blo 988596 5090519 := bstep (se 1 (by rfl) ⟨3817889, by rfl⟩ : syracuseStep 5090519 = 7635779) B7635779
theorem B1486121 : Blo 988596 1486121 := bstep (se 2 (by rfl) ⟨557295, by rfl⟩ : syracuseStep 1486121 = 1114591) B1114591
theorem B4763423 : Blo 988596 4763423 := bstep (se 1 (by rfl) ⟨3572567, by rfl⟩ : syracuseStep 4763423 = 7145135) B7145135
theorem B1487087 : Blo 988596 1487087 := bstep (se 1 (by rfl) ⟨1115315, by rfl⟩ : syracuseStep 1487087 = 2230631) B2230631
theorem B1487471 : Blo 988596 1487471 := bstep (se 1 (by rfl) ⟨1115603, by rfl⟩ : syracuseStep 1487471 = 2231207) B2231207
theorem B1488491 : Blo 988596 1488491 := bstep (se 1 (by rfl) ⟨1116368, by rfl⟩ : syracuseStep 1488491 = 2232737) B2232737
theorem B45790859 : Blo 988596 45790859 := bstep (se 1 (by rfl) ⟨34343144, by rfl⟩ : syracuseStep 45790859 = 68686289) B68686289
theorem B2504479 : Blo 988596 2504479 := bstep (se 1 (by rfl) ⟨1878359, by rfl⟩ : syracuseStep 2504479 = 3756719) B3756719
theorem B1488731 : Blo 988596 1488731 := bstep (se 1 (by rfl) ⟨1116548, by rfl⟩ : syracuseStep 1488731 = 2233097) B2233097
theorem B1488809 : Blo 988596 1488809 := bstep (se 2 (by rfl) ⟨558303, by rfl⟩ : syracuseStep 1488809 = 1116607) B1116607
theorem B9517733 : Blo 988596 9517733 := bstep (se 4 (by rfl) ⟨892287, by rfl⟩ : syracuseStep 9517733 = 1784575) B1784575
theorem B2506423 : Blo 988596 2506423 := bstep (se 1 (by rfl) ⟨1879817, by rfl⟩ : syracuseStep 2506423 = 3759635) B3759635
theorem B4832951 : Blo 988596 4832951 := bstep (se 1 (by rfl) ⟨3624713, by rfl⟩ : syracuseStep 4832951 = 7249427) B7249427
theorem B40715621 : Blo 988596 40715621 := bstep (se 4 (by rfl) ⟨3817089, by rfl⟩ : syracuseStep 40715621 = 7634179) B7634179
theorem B2508367 : Blo 988596 2508367 := bstep (se 1 (by rfl) ⟨1881275, by rfl⟩ : syracuseStep 2508367 = 3762551) B3762551
theorem B13551731 : Blo 988596 13551731 := bstep (se 1 (by rfl) ⟨10163798, by rfl⟩ : syracuseStep 13551731 = 20327597) B20327597
theorem B2672993 : Blo 988596 2672993 := bstep (se 2 (by rfl) ⟨1002372, by rfl⟩ : syracuseStep 2672993 = 2004745) B2004745
theorem B2510311 : Blo 988596 2510311 := bstep (se 1 (by rfl) ⟨1882733, by rfl⟩ : syracuseStep 2510311 = 3765467) B3765467
theorem B22859495 : Blo 988596 22859495 := bstep (se 1 (by rfl) ⟨17144621, by rfl⟩ : syracuseStep 22859495 = 34289243) B34289243
theorem B2511071 : Blo 988596 2511071 := bstep (se 1 (by rfl) ⟨1883303, by rfl⟩ : syracuseStep 2511071 = 3766607) B3766607
theorem B10703555 : Blo 988596 10703555 := bstep (se 1 (by rfl) ⟨8027666, by rfl⟩ : syracuseStep 10703555 = 16055333) B16055333
theorem B4281947 : Blo 988596 4281947 := bstep (se 1 (by rfl) ⟨3211460, by rfl⟩ : syracuseStep 4281947 = 6422921) B6422921
theorem B10868527 : Blo 988596 10868527 := bstep (se 1 (by rfl) ⟨8151395, by rfl⟩ : syracuseStep 10868527 = 16302791) B16302791
theorem B2381951 : Blo 988596 2381951 := bstep (se 1 (by rfl) ⟨1786463, by rfl⟩ : syracuseStep 2381951 = 3572927) B3572927
theorem B8018585 : Blo 988596 8018585 := bstep (se 2 (by rfl) ⟨3006969, by rfl⟩ : syracuseStep 8018585 = 6013939) B6013939
theorem B7625431 : Blo 988596 7625431 := bstep (se 1 (by rfl) ⟨5719073, by rfl⟩ : syracuseStep 7625431 = 11438147) B11438147
theorem B38066921 : Blo 988596 38066921 := bstep (se 2 (by rfl) ⟨14275095, by rfl⟩ : syracuseStep 38066921 = 28550191) B28550191
theorem B611409293 : Blo 988596 611409293 := bstep (se 3 (by rfl) ⟨114639242, by rfl⟩ : syracuseStep 611409293 = 229278485) B229278485
theorem B11001881 : Blo 988596 11001881 := bstep (se 2 (by rfl) ⟨4125705, by rfl⟩ : syracuseStep 11001881 = 8251411) B8251411
theorem B2416711 : Blo 988596 2416711 := bstep (se 1 (by rfl) ⟨1812533, by rfl⟩ : syracuseStep 2416711 = 3625067) B3625067
theorem B3760289 : Blo 988596 3760289 := bstep (se 2 (by rfl) ⟨1410108, by rfl⟩ : syracuseStep 3760289 = 2820217) B2820217
theorem B5726699 : Blo 988596 5726699 := bstep (se 1 (by rfl) ⟨4295024, by rfl⟩ : syracuseStep 5726699 = 8590049) B8590049
theorem B11264507 : Blo 988596 11264507 := bstep (se 1 (by rfl) ⟨8448380, by rfl⟩ : syracuseStep 11264507 = 16896761) B16896761
theorem B3171143 : Blo 988596 3171143 := bstep (se 1 (by rfl) ⟨2378357, by rfl⟩ : syracuseStep 3171143 = 4756715) B4756715
theorem B16901135 : Blo 988596 16901135 := bstep (se 1 (by rfl) ⟨12675851, by rfl⟩ : syracuseStep 16901135 = 25351703) B25351703
theorem B17130635 : Blo 988596 17130635 := bstep (se 1 (by rfl) ⟨12847976, by rfl⟩ : syracuseStep 17130635 = 25695953) B25695953
theorem B5007095 : Blo 988596 5007095 := bstep (se 1 (by rfl) ⟨3755321, by rfl⟩ : syracuseStep 5007095 = 7510643) B7510643
theorem B128608721 : Blo 988596 128608721 := bstep (se 2 (by rfl) ⟨48228270, by rfl⟩ : syracuseStep 128608721 = 96456541) B96456541
theorem B2681599 : Blo 988596 2681599 := bstep (se 1 (by rfl) ⟨2011199, by rfl⟩ : syracuseStep 2681599 = 4022399) B4022399
theorem B6352127 : Blo 988596 6352127 := bstep (se 1 (by rfl) ⟨4764095, by rfl⟩ : syracuseStep 6352127 = 9528191) B9528191
theorem B7138763 : Blo 988596 7138763 := bstep (se 1 (by rfl) ⟨5354072, by rfl⟩ : syracuseStep 7138763 = 10708145) B10708145
theorem B7532027 : Blo 988596 7532027 := bstep (se 1 (by rfl) ⟨5649020, by rfl⟩ : syracuseStep 7532027 = 11298041) B11298041
theorem B30470195 : Blo 988596 30470195 := bstep (se 1 (by rfl) ⟨22852646, by rfl⟩ : syracuseStep 30470195 = 45705293) B45705293
theorem B2682983 : Blo 988596 2682983 := bstep (se 1 (by rfl) ⟨2012237, by rfl⟩ : syracuseStep 2682983 = 4024475) B4024475
theorem B6780025 : Blo 988596 6780025 := bstep (se 2 (by rfl) ⟨2542509, by rfl⟩ : syracuseStep 6780025 = 5085019) B5085019
theorem B79164599 : Blo 988596 79164599 := bstep (se 1 (by rfl) ⟨59373449, by rfl⟩ : syracuseStep 79164599 = 118746899) B118746899
theorem B2225339 : Blo 988596 2225339 := bstep (se 1 (by rfl) ⟨1669004, by rfl⟩ : syracuseStep 2225339 = 3338009) B3338009
theorem B3765437 : Blo 988596 3765437 := bstep (se 3 (by rfl) ⟨706019, by rfl⟩ : syracuseStep 3765437 = 1412039) B1412039
theorem B3339575 : Blo 988596 3339575 := bstep (se 1 (by rfl) ⟨2504681, by rfl⟩ : syracuseStep 3339575 = 5009363) B5009363
theorem B2225771 : Blo 988596 2225771 := bstep (se 1 (by rfl) ⟨1669328, by rfl⟩ : syracuseStep 2225771 = 3338657) B3338657
theorem B42858503 : Blo 988596 42858503 := bstep (se 1 (by rfl) ⟨32143877, by rfl⟩ : syracuseStep 42858503 = 64287755) B64287755
theorem B36108463 : Blo 988596 36108463 := bstep (se 1 (by rfl) ⟨27081347, by rfl⟩ : syracuseStep 36108463 = 54162695) B54162695
theorem B7534943 : Blo 988596 7534943 := bstep (se 1 (by rfl) ⟨5651207, by rfl⟩ : syracuseStep 7534943 = 11302415) B11302415
theorem B1669727 : Blo 988596 1669727 := bstep (se 1 (by rfl) ⟨1252295, by rfl⟩ : syracuseStep 1669727 = 2504591) B2504591
theorem B1112827 : Blo 988596 1112827 := bstep (se 1 (by rfl) ⟨834620, by rfl⟩ : syracuseStep 1112827 = 1669241) B1669241
theorem B2816765 : Blo 988596 2816765 := bstep (se 3 (by rfl) ⟨528143, by rfl⟩ : syracuseStep 2816765 = 1056287) B1056287
theorem B1112863 : Blo 988596 1112863 := bstep (se 1 (by rfl) ⟨834647, by rfl⟩ : syracuseStep 1112863 = 1669295) B1669295
theorem B5012279 : Blo 988596 5012279 := bstep (se 1 (by rfl) ⟨3759209, by rfl⟩ : syracuseStep 5012279 = 7518419) B7518419
theorem B8584019 : Blo 988596 8584019 := bstep (se 1 (by rfl) ⟨6438014, by rfl⟩ : syracuseStep 8584019 = 12876029) B12876029
theorem B2227067 : Blo 988596 2227067 := bstep (se 1 (by rfl) ⟨1670300, by rfl⟩ : syracuseStep 2227067 = 3340601) B3340601
theorem B3341195 : Blo 988596 3341195 := bstep (se 1 (by rfl) ⟨2505896, by rfl⟩ : syracuseStep 3341195 = 5011793) B5011793
theorem B11303873 : Blo 988596 11303873 := bstep (se 2 (by rfl) ⟨4238952, by rfl⟩ : syracuseStep 11303873 = 8477905) B8477905
theorem B4226003 : Blo 988596 4226003 := bstep (se 1 (by rfl) ⟨3169502, by rfl⟩ : syracuseStep 4226003 = 6339005) B6339005
theorem B2227355 : Blo 988596 2227355 := bstep (se 1 (by rfl) ⟨1670516, by rfl⟩ : syracuseStep 2227355 = 3341033) B3341033
theorem B7241015 : Blo 988596 7241015 := bstep (se 1 (by rfl) ⟨5430761, by rfl⟩ : syracuseStep 7241015 = 10861523) B10861523
theorem B12713273 : Blo 988596 12713273 := bstep (se 2 (by rfl) ⟨4767477, by rfl⟩ : syracuseStep 12713273 = 9534955) B9534955
theorem B5078695 : Blo 988596 5078695 := bstep (se 1 (by rfl) ⟨3809021, by rfl⟩ : syracuseStep 5078695 = 7618043) B7618043
theorem B1671023 : Blo 988596 1671023 := bstep (se 1 (by rfl) ⟨1253267, by rfl⟩ : syracuseStep 1671023 = 2506535) B2506535
theorem B3342491 : Blo 988596 3342491 := bstep (se 1 (by rfl) ⟨2506868, by rfl⟩ : syracuseStep 3342491 = 5013737) B5013737
theorem B2228399 : Blo 988596 2228399 := bstep (se 1 (by rfl) ⟨1671299, by rfl⟩ : syracuseStep 2228399 = 3342599) B3342599
theorem B1114447 : Blo 988596 1114447 := bstep (se 1 (by rfl) ⟨835835, by rfl⟩ : syracuseStep 1114447 = 1671671) B1671671
theorem B2228777 : Blo 988596 2228777 := bstep (se 2 (by rfl) ⟨835791, by rfl⟩ : syracuseStep 2228777 = 1671583) B1671583
theorem B3343679 : Blo 988596 3343679 := bstep (se 1 (by rfl) ⟨2507759, by rfl⟩ : syracuseStep 3343679 = 5015519) B5015519
theorem B3344489 : Blo 988596 3344489 := bstep (se 2 (by rfl) ⟨1254183, by rfl⟩ : syracuseStep 3344489 = 2508367) B2508367
theorem B15239663 : Blo 988596 15239663 := bstep (se 1 (by rfl) ⟨11429747, by rfl⟩ : syracuseStep 15239663 = 22859495) B22859495
theorem B2230991 : Blo 988596 2230991 := bstep (se 1 (by rfl) ⟨1673243, by rfl⟩ : syracuseStep 2230991 = 3346487) B3346487
theorem B1674047 : Blo 988596 1674047 := bstep (se 1 (by rfl) ⟨1255535, by rfl⟩ : syracuseStep 1674047 = 2511071) B2511071
theorem B1674121 : Blo 988596 1674121 := bstep (se 2 (by rfl) ⟨627795, by rfl⟩ : syracuseStep 1674121 = 1255591) B1255591
theorem B2231963 : Blo 988596 2231963 := bstep (se 1 (by rfl) ⟨1673972, by rfl⟩ : syracuseStep 2231963 = 3347945) B3347945
theorem B3575465 : Blo 988596 3575465 := bstep (se 2 (by rfl) ⟨1340799, by rfl⟩ : syracuseStep 3575465 = 2681599) B2681599
theorem B2854631 : Blo 988596 2854631 := bstep (se 1 (by rfl) ⟨2140973, by rfl⟩ : syracuseStep 2854631 = 4281947) B4281947
theorem B40668965 : Blo 988596 40668965 := bstep (se 4 (by rfl) ⟨3812715, by rfl⟩ : syracuseStep 40668965 = 7625431) B7625431
theorem B3805483 : Blo 988596 3805483 := bstep (se 1 (by rfl) ⟨2854112, by rfl⟩ : syracuseStep 3805483 = 5708225) B5708225
theorem B5345723 : Blo 988596 5345723 := bstep (se 1 (by rfl) ⟨4009292, by rfl⟩ : syracuseStep 5345723 = 8018585) B8018585
theorem B3347081 : Blo 988596 3347081 := bstep (se 2 (by rfl) ⟨1255155, by rfl⟩ : syracuseStep 3347081 = 2510311) B2510311
theorem B2822951 : Blo 988596 2822951 := bstep (se 1 (by rfl) ⟨2117213, by rfl⟩ : syracuseStep 2822951 = 4234427) B4234427
theorem B407606195 : Blo 988596 407606195 := bstep (se 1 (by rfl) ⟨305704646, by rfl⟩ : syracuseStep 407606195 = 611409293) B611409293
theorem B4527227 : Blo 988596 4527227 := bstep (se 1 (by rfl) ⟨3395420, by rfl⟩ : syracuseStep 4527227 = 6790841) B6790841
theorem B7509671 : Blo 988596 7509671 := bstep (se 1 (by rfl) ⟨5632253, by rfl⟩ : syracuseStep 7509671 = 11264507) B11264507
theorem B989031 : Blo 988596 989031 := bstep (se 1 (by rfl) ⟨741773, by rfl⟩ : syracuseStep 989031 = 1483547) B1483547
theorem B989343 : Blo 988596 989343 := bstep (se 1 (by rfl) ⟨742007, by rfl⟩ : syracuseStep 989343 = 1484015) B1484015
theorem B989407 : Blo 988596 989407 := bstep (se 1 (by rfl) ⟨742055, by rfl⟩ : syracuseStep 989407 = 1484111) B1484111
theorem B989567 : Blo 988596 989567 := bstep (se 1 (by rfl) ⟨742175, by rfl⟩ : syracuseStep 989567 = 1484351) B1484351
theorem B989887 : Blo 988596 989887 := bstep (se 1 (by rfl) ⟨742415, by rfl⟩ : syracuseStep 989887 = 1484831) B1484831
theorem B3349727 : Blo 988596 3349727 := bstep (se 1 (by rfl) ⟨2512295, by rfl⟩ : syracuseStep 3349727 = 5024591) B5024591
theorem B990623 : Blo 988596 990623 := bstep (se 1 (by rfl) ⟨742967, by rfl⟩ : syracuseStep 990623 = 1485935) B1485935
theorem B4234751 : Blo 988596 4234751 := bstep (se 1 (by rfl) ⟨3176063, by rfl⟩ : syracuseStep 4234751 = 6352127) B6352127
theorem B990747 : Blo 988596 990747 := bstep (se 1 (by rfl) ⟨743060, by rfl⟩ : syracuseStep 990747 = 1486121) B1486121
theorem B4759175 : Blo 988596 4759175 := bstep (se 1 (by rfl) ⟨3569381, by rfl⟩ : syracuseStep 4759175 = 7138763) B7138763
theorem B5021351 : Blo 988596 5021351 := bstep (se 1 (by rfl) ⟨3766013, by rfl⟩ : syracuseStep 5021351 = 7532027) B7532027
theorem B14491369 : Blo 988596 14491369 := bstep (se 2 (by rfl) ⟨5434263, by rfl⟩ : syracuseStep 14491369 = 10868527) B10868527
theorem B991391 : Blo 988596 991391 := bstep (se 1 (by rfl) ⟨743543, by rfl⟩ : syracuseStep 991391 = 1487087) B1487087
theorem B48144617 : Blo 988596 48144617 := bstep (se 2 (by rfl) ⟨18054231, by rfl⟩ : syracuseStep 48144617 = 36108463) B36108463
theorem B991647 : Blo 988596 991647 := bstep (se 1 (by rfl) ⟨743735, by rfl⟩ : syracuseStep 991647 = 1487471) B1487471
theorem B1483559 : Blo 988596 1483559 := bstep (se 1 (by rfl) ⟨1112669, by rfl⟩ : syracuseStep 1483559 = 2225339) B2225339
theorem B19309373 : Blo 988596 19309373 := bstep (se 3 (by rfl) ⟨3620507, by rfl⟩ : syracuseStep 19309373 = 7241015) B7241015
theorem B1483769 : Blo 988596 1483769 := bstep (se 2 (by rfl) ⟨556413, by rfl⟩ : syracuseStep 1483769 = 1112827) B1112827
theorem B1483817 : Blo 988596 1483817 := bstep (se 2 (by rfl) ⟨556431, by rfl⟩ : syracuseStep 1483817 = 1112863) B1112863
theorem B1483847 : Blo 988596 1483847 := bstep (se 1 (by rfl) ⟨1112885, by rfl⟩ : syracuseStep 1483847 = 2225771) B2225771
theorem B992327 : Blo 988596 992327 := bstep (se 1 (by rfl) ⟨744245, by rfl⟩ : syracuseStep 992327 = 1488491) B1488491
theorem B992487 : Blo 988596 992487 := bstep (se 1 (by rfl) ⟨744365, by rfl⟩ : syracuseStep 992487 = 1488731) B1488731
theorem B992539 : Blo 988596 992539 := bstep (se 1 (by rfl) ⟨744404, by rfl⟩ : syracuseStep 992539 = 1488809) B1488809
theorem B5023295 : Blo 988596 5023295 := bstep (se 1 (by rfl) ⟨3767471, by rfl⟩ : syracuseStep 5023295 = 7534943) B7534943
theorem B12887869 : Blo 988596 12887869 := bstep (se 3 (by rfl) ⟨2416475, by rfl⟩ : syracuseStep 12887869 = 4832951) B4832951
theorem B1877843 : Blo 988596 1877843 := bstep (se 1 (by rfl) ⟨1408382, by rfl⟩ : syracuseStep 1877843 = 2816765) B2816765
theorem B1484711 : Blo 988596 1484711 := bstep (se 1 (by rfl) ⟨1113533, by rfl⟩ : syracuseStep 1484711 = 2227067) B2227067
theorem B1484903 : Blo 988596 1484903 := bstep (se 1 (by rfl) ⟨1113677, by rfl⟩ : syracuseStep 1484903 = 2227355) B2227355
theorem B3222281 : Blo 988596 3222281 := bstep (se 2 (by rfl) ⟨1208355, by rfl⟩ : syracuseStep 3222281 = 2416711) B2416711
theorem B1878815 : Blo 988596 1878815 := bstep (se 1 (by rfl) ⟨1409111, by rfl⟩ : syracuseStep 1878815 = 2818223) B2818223
theorem B1485689 : Blo 988596 1485689 := bstep (se 2 (by rfl) ⟨557133, by rfl⟩ : syracuseStep 1485689 = 1114267) B1114267
theorem B1485695 : Blo 988596 1485695 := bstep (se 1 (by rfl) ⟨1114271, by rfl⟩ : syracuseStep 1485695 = 2228543) B2228543
theorem B1486055 : Blo 988596 1486055 := bstep (se 1 (by rfl) ⟨1114541, by rfl⟩ : syracuseStep 1486055 = 2229083) B2229083
theorem B6532463 : Blo 988596 6532463 := bstep (se 1 (by rfl) ⟨4899347, by rfl⟩ : syracuseStep 6532463 = 9798695) B9798695
theorem B1486271 : Blo 988596 1486271 := bstep (se 1 (by rfl) ⟨1114703, by rfl⟩ : syracuseStep 1486271 = 2229407) B2229407
theorem B27143747 : Blo 988596 27143747 := bstep (se 1 (by rfl) ⟨20357810, by rfl⟩ : syracuseStep 27143747 = 40715621) B40715621
theorem B1486505 : Blo 988596 1486505 := bstep (se 2 (by rfl) ⟨557439, by rfl⟩ : syracuseStep 1486505 = 1114879) B1114879
theorem B19050227 : Blo 988596 19050227 := bstep (se 1 (by rfl) ⟨14287670, by rfl⟩ : syracuseStep 19050227 = 28575341) B28575341
theorem B2502697 : Blo 988596 2502697 := bstep (se 2 (by rfl) ⟨938511, by rfl⟩ : syracuseStep 2502697 = 1877023) B1877023
theorem B1781995 : Blo 988596 1781995 := bstep (se 1 (by rfl) ⟨1336496, by rfl⟩ : syracuseStep 1781995 = 2672993) B2672993
theorem B1487339 : Blo 988596 1487339 := bstep (se 1 (by rfl) ⟨1115504, by rfl⟩ : syracuseStep 1487339 = 2231009) B2231009
theorem B1487465 : Blo 988596 1487465 := bstep (se 2 (by rfl) ⟨557799, by rfl⟩ : syracuseStep 1487465 = 1115599) B1115599
theorem B1487615 : Blo 988596 1487615 := bstep (se 1 (by rfl) ⟨1115711, by rfl⟩ : syracuseStep 1487615 = 2231423) B2231423
theorem B60961841 : Blo 988596 60961841 := bstep (se 2 (by rfl) ⟨22860690, by rfl⟩ : syracuseStep 60961841 = 45721381) B45721381
theorem B2504105 : Blo 988596 2504105 := bstep (se 2 (by rfl) ⟨939039, by rfl⟩ : syracuseStep 2504105 = 1878079) B1878079
theorem B211105597 : Blo 988596 211105597 := bstep (se 3 (by rfl) ⟨39582299, by rfl⟩ : syracuseStep 211105597 = 79164599) B79164599
theorem B1587967 : Blo 988596 1587967 := bstep (se 1 (by rfl) ⟨1190975, by rfl⟩ : syracuseStep 1587967 = 2381951) B2381951
theorem B122108957 : Blo 988596 122108957 := bstep (se 3 (by rfl) ⟨22895429, by rfl⟩ : syracuseStep 122108957 = 45790859) B45790859
theorem B1883243 : Blo 988596 1883243 := bstep (se 1 (by rfl) ⟨1412432, by rfl⟩ : syracuseStep 1883243 = 2824865) B2824865
theorem B25377947 : Blo 988596 25377947 := bstep (se 1 (by rfl) ⟨19033460, by rfl⟩ : syracuseStep 25377947 = 38066921) B38066921
theorem B2506859 : Blo 988596 2506859 := bstep (se 1 (by rfl) ⟨1880144, by rfl⟩ : syracuseStep 2506859 = 3760289) B3760289
theorem B4768055 : Blo 988596 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B3817799 : Blo 988596 3817799 := bstep (se 1 (by rfl) ⟨2863349, by rfl⟩ : syracuseStep 3817799 = 5726699) B5726699
theorem B3392027 : Blo 988596 3392027 := bstep (se 1 (by rfl) ⟨2544020, by rfl⟩ : syracuseStep 3392027 = 5088041) B5088041
theorem B2114095 : Blo 988596 2114095 := bstep (se 1 (by rfl) ⟨1585571, by rfl⟩ : syracuseStep 2114095 = 3171143) B3171143
theorem B11420423 : Blo 988596 11420423 := bstep (se 1 (by rfl) ⟨8565317, by rfl⟩ : syracuseStep 11420423 = 17130635) B17130635
theorem B85739147 : Blo 988596 85739147 := bstep (se 1 (by rfl) ⟨64304360, by rfl⟩ : syracuseStep 85739147 = 128608721) B128608721
theorem B7325423 : Blo 988596 7325423 := bstep (se 1 (by rfl) ⟨5494067, by rfl⟩ : syracuseStep 7325423 = 10988135) B10988135
theorem B2672507 : Blo 988596 2672507 := bstep (se 1 (by rfl) ⟨2004380, by rfl⟩ : syracuseStep 2672507 = 4008761) B4008761
theorem B3393679 : Blo 988596 3393679 := bstep (se 1 (by rfl) ⟨2545259, by rfl⟩ : syracuseStep 3393679 = 5090519) B5090519
theorem B1788655 : Blo 988596 1788655 := bstep (se 1 (by rfl) ⟨1341491, by rfl⟩ : syracuseStep 1788655 = 2682983) B2682983
theorem B2510291 : Blo 988596 2510291 := bstep (se 1 (by rfl) ⟨1882718, by rfl⟩ : syracuseStep 2510291 = 3765437) B3765437
theorem B6345155 : Blo 988596 6345155 := bstep (se 1 (by rfl) ⟨4758866, by rfl⟩ : syracuseStep 6345155 = 9517733) B9517733
theorem B5722679 : Blo 988596 5722679 := bstep (se 1 (by rfl) ⟨4292009, by rfl⟩ : syracuseStep 5722679 = 8584019) B8584019
theorem B8475515 : Blo 988596 8475515 := bstep (se 1 (by rfl) ⟨6356636, by rfl⟩ : syracuseStep 8475515 = 12713273) B12713273
theorem B6771593 : Blo 988596 6771593 := bstep (se 2 (by rfl) ⟨2539347, by rfl⟩ : syracuseStep 6771593 = 5078695) B5078695
theorem B81253853 : Blo 988596 81253853 := bstep (se 3 (by rfl) ⟨15235097, by rfl⟩ : syracuseStep 81253853 = 30470195) B30470195
theorem B12670931 : Blo 988596 12670931 := bstep (se 1 (by rfl) ⟨9503198, by rfl⟩ : syracuseStep 12670931 = 19006397) B19006397
theorem B9034487 : Blo 988596 9034487 := bstep (se 1 (by rfl) ⟨6775865, by rfl⟩ : syracuseStep 9034487 = 13551731) B13551731
theorem B209083283 : Blo 988596 209083283 := bstep (se 1 (by rfl) ⟨156812462, by rfl⟩ : syracuseStep 209083283 = 313624925) B313624925
theorem B7135361 : Blo 988596 7135361 := bstep (se 2 (by rfl) ⟨2675760, by rfl⟩ : syracuseStep 7135361 = 5351521) B5351521
theorem B7135703 : Blo 988596 7135703 := bstep (se 1 (by rfl) ⟨5351777, by rfl⟩ : syracuseStep 7135703 = 10703555) B10703555
theorem B3760607 : Blo 988596 3760607 := bstep (se 1 (by rfl) ⟨2820455, by rfl⟩ : syracuseStep 3760607 = 5640911) B5640911
theorem B7334587 : Blo 988596 7334587 := bstep (se 1 (by rfl) ⟨5500940, by rfl⟩ : syracuseStep 7334587 = 11001881) B11001881
theorem B11267423 : Blo 988596 11267423 := bstep (se 1 (by rfl) ⟨8450567, by rfl⟩ : syracuseStep 11267423 = 16901135) B16901135
theorem B5009039 : Blo 988596 5009039 := bstep (se 1 (by rfl) ⟨3756779, by rfl⟩ : syracuseStep 5009039 = 7513559) B7513559
theorem B3338063 : Blo 988596 3338063 := bstep (se 1 (by rfl) ⟨2503547, by rfl⟩ : syracuseStep 3338063 = 5007095) B5007095
theorem B9040033 : Blo 988596 9040033 := bstep (se 2 (by rfl) ⟨3390012, by rfl⟩ : syracuseStep 9040033 = 6780025) B6780025
theorem B6779695 : Blo 988596 6779695 := bstep (se 1 (by rfl) ⟨5084771, by rfl⟩ : syracuseStep 6779695 = 10169543) B10169543
theorem B3339197 : Blo 988596 3339197 := bstep (se 3 (by rfl) ⟨626099, by rfl⟩ : syracuseStep 3339197 = 1252199) B1252199
theorem B3339305 : Blo 988596 3339305 := bstep (se 2 (by rfl) ⟨1252239, by rfl⟩ : syracuseStep 3339305 = 2504479) B2504479
theorem B3175615 : Blo 988596 3175615 := bstep (se 1 (by rfl) ⟨2381711, by rfl⟩ : syracuseStep 3175615 = 4763423) B4763423
theorem B2226383 : Blo 988596 2226383 := bstep (se 1 (by rfl) ⟨1669787, by rfl⟩ : syracuseStep 2226383 = 3339575) B3339575
theorem B28572335 : Blo 988596 28572335 := bstep (se 1 (by rfl) ⟨21429251, by rfl⟩ : syracuseStep 28572335 = 42858503) B42858503
theorem B1113151 : Blo 988596 1113151 := bstep (se 1 (by rfl) ⟨834863, by rfl⟩ : syracuseStep 1113151 = 1669727) B1669727
theorem B3341519 : Blo 988596 3341519 := bstep (se 1 (by rfl) ⟨2506139, by rfl⟩ : syracuseStep 3341519 = 5012279) B5012279
theorem B2227463 : Blo 988596 2227463 := bstep (se 1 (by rfl) ⟨1670597, by rfl⟩ : syracuseStep 2227463 = 3341195) B3341195
theorem B7535915 : Blo 988596 7535915 := bstep (se 1 (by rfl) ⟨5651936, by rfl⟩ : syracuseStep 7535915 = 11303873) B11303873
theorem B2817335 : Blo 988596 2817335 := bstep (se 1 (by rfl) ⟨2113001, by rfl⟩ : syracuseStep 2817335 = 4226003) B4226003
theorem B3341897 : Blo 988596 3341897 := bstep (se 2 (by rfl) ⟨1253211, by rfl⟩ : syracuseStep 3341897 = 2506423) B2506423
theorem B1114015 : Blo 988596 1114015 := bstep (se 1 (by rfl) ⟨835511, by rfl⟩ : syracuseStep 1114015 = 1671023) B1671023
theorem B1671239 : Blo 988596 1671239 := bstep (se 1 (by rfl) ⟨1253429, by rfl⟩ : syracuseStep 1671239 = 2506859) B2506859
theorem B2228327 : Blo 988596 2228327 := bstep (se 1 (by rfl) ⟨1671245, by rfl⟩ : syracuseStep 2228327 = 3342491) B3342491
theorem B3178703 : Blo 988596 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B2261351 : Blo 988596 2261351 := bstep (se 1 (by rfl) ⟨1696013, by rfl⟩ : syracuseStep 2261351 = 3392027) B3392027
theorem B2818793 : Blo 988596 2818793 := bstep (se 2 (by rfl) ⟨1057047, by rfl⟩ : syracuseStep 2818793 = 2114095) B2114095
theorem B2229119 : Blo 988596 2229119 := bstep (se 1 (by rfl) ⟨1671839, by rfl⟩ : syracuseStep 2229119 = 3343679) B3343679
theorem B14255261 : Blo 988596 14255261 := bstep (se 3 (by rfl) ⟨2672861, by rfl⟩ : syracuseStep 14255261 = 5345723) B5345723
theorem B4883615 : Blo 988596 4883615 := bstep (se 1 (by rfl) ⟨3662711, by rfl⟩ : syracuseStep 4883615 = 7325423) B7325423
theorem B2229659 : Blo 988596 2229659 := bstep (se 1 (by rfl) ⟨1672244, by rfl⟩ : syracuseStep 2229659 = 3344489) B3344489
theorem B10159775 : Blo 988596 10159775 := bstep (se 1 (by rfl) ⟨7619831, by rfl⟩ : syracuseStep 10159775 = 15239663) B15239663
theorem B1116031 : Blo 988596 1116031 := bstep (se 1 (by rfl) ⟨837023, by rfl⟩ : syracuseStep 1116031 = 1674047) B1674047
theorem B1673527 : Blo 988596 1673527 := bstep (se 1 (by rfl) ⟨1255145, by rfl⟩ : syracuseStep 1673527 = 2510291) B2510291
theorem B1086949853 : Blo 988596 1086949853 := bstep (se 3 (by rfl) ⟨203803097, by rfl⟩ : syracuseStep 1086949853 = 407606195) B407606195
theorem B1903087 : Blo 988596 1903087 := bstep (se 1 (by rfl) ⟨1427315, by rfl⟩ : syracuseStep 1903087 = 2854631) B2854631
theorem B4524905 : Blo 988596 4524905 := bstep (se 2 (by rfl) ⟨1696839, by rfl⟩ : syracuseStep 4524905 = 3393679) B3393679
theorem B4230103 : Blo 988596 4230103 := bstep (se 1 (by rfl) ⟨3172577, by rfl⟩ : syracuseStep 4230103 = 6345155) B6345155
theorem B2231387 : Blo 988596 2231387 := bstep (se 1 (by rfl) ⟨1673540, by rfl⟩ : syracuseStep 2231387 = 3347081) B3347081
theorem B3018151 : Blo 988596 3018151 := bstep (se 1 (by rfl) ⟨2263613, by rfl⟩ : syracuseStep 3018151 = 4527227) B4527227
theorem B54169235 : Blo 988596 54169235 := bstep (se 1 (by rfl) ⟨40626926, by rfl⟩ : syracuseStep 54169235 = 81253853) B81253853
theorem B2232161 : Blo 988596 2232161 := bstep (se 2 (by rfl) ⟨837060, by rfl⟩ : syracuseStep 2232161 = 1674121) B1674121
theorem B2233151 : Blo 988596 2233151 := bstep (se 1 (by rfl) ⟨1674863, by rfl⟩ : syracuseStep 2233151 = 3349727) B3349727
theorem B2823167 : Blo 988596 2823167 := bstep (se 1 (by rfl) ⟨2117375, by rfl⟩ : syracuseStep 2823167 = 4234751) B4234751
theorem B3347567 : Blo 988596 3347567 := bstep (se 1 (by rfl) ⟨2510675, by rfl⟩ : syracuseStep 3347567 = 5021351) B5021351
theorem B4756907 : Blo 988596 4756907 := bstep (se 1 (by rfl) ⟨3567680, by rfl⟩ : syracuseStep 4756907 = 7135361) B7135361
theorem B4757135 : Blo 988596 4757135 := bstep (se 1 (by rfl) ⟨3567851, by rfl⟩ : syracuseStep 4757135 = 7135703) B7135703
theorem B989039 : Blo 988596 989039 := bstep (se 1 (by rfl) ⟨741779, by rfl⟩ : syracuseStep 989039 = 1483559) B1483559
theorem B989179 : Blo 988596 989179 := bstep (se 1 (by rfl) ⟨741884, by rfl⟩ : syracuseStep 989179 = 1483769) B1483769
theorem B989211 : Blo 988596 989211 := bstep (se 1 (by rfl) ⟨741908, by rfl⟩ : syracuseStep 989211 = 1483817) B1483817
theorem B989231 : Blo 988596 989231 := bstep (se 1 (by rfl) ⟨741923, by rfl⟩ : syracuseStep 989231 = 1483847) B1483847
theorem B3348863 : Blo 988596 3348863 := bstep (se 1 (by rfl) ⟨2511647, by rfl⟩ : syracuseStep 3348863 = 5023295) B5023295
theorem B989807 : Blo 988596 989807 := bstep (se 1 (by rfl) ⟨742355, by rfl⟩ : syracuseStep 989807 = 1484711) B1484711
theorem B989935 : Blo 988596 989935 := bstep (se 1 (by rfl) ⟨742451, by rfl⟩ : syracuseStep 989935 = 1484903) B1484903
theorem B4234153 : Blo 988596 4234153 := bstep (se 2 (by rfl) ⟨1587807, by rfl⟩ : syracuseStep 4234153 = 3175615) B3175615
theorem B990459 : Blo 988596 990459 := bstep (se 1 (by rfl) ⟨742844, by rfl⟩ : syracuseStep 990459 = 1485689) B1485689
theorem B990463 : Blo 988596 990463 := bstep (se 1 (by rfl) ⟨742847, by rfl⟩ : syracuseStep 990463 = 1485695) B1485695
theorem B990703 : Blo 988596 990703 := bstep (se 1 (by rfl) ⟨743027, by rfl⟩ : syracuseStep 990703 = 1486055) B1486055
theorem B7511615 : Blo 988596 7511615 := bstep (se 1 (by rfl) ⟨5633711, by rfl⟩ : syracuseStep 7511615 = 11267423) B11267423
theorem B990847 : Blo 988596 990847 := bstep (se 1 (by rfl) ⟨743135, by rfl⟩ : syracuseStep 990847 = 1486271) B1486271
theorem B18095831 : Blo 988596 18095831 := bstep (se 1 (by rfl) ⟨13571873, by rfl⟩ : syracuseStep 18095831 = 27143747) B27143747
theorem B991003 : Blo 988596 991003 := bstep (se 1 (by rfl) ⟨743252, by rfl⟩ : syracuseStep 991003 = 1486505) B1486505
theorem B991559 : Blo 988596 991559 := bstep (se 1 (by rfl) ⟨743669, by rfl⟩ : syracuseStep 991559 = 1487339) B1487339
theorem B991643 : Blo 988596 991643 := bstep (se 1 (by rfl) ⟨743732, by rfl⟩ : syracuseStep 991643 = 1487465) B1487465
theorem B991743 : Blo 988596 991743 := bstep (se 1 (by rfl) ⟨743807, by rfl⟩ : syracuseStep 991743 = 1487615) B1487615
theorem B40641227 : Blo 988596 40641227 := bstep (se 1 (by rfl) ⟨30480920, by rfl⟩ : syracuseStep 40641227 = 60961841) B60961841
theorem B1484201 : Blo 988596 1484201 := bstep (se 2 (by rfl) ⟨556575, by rfl⟩ : syracuseStep 1484201 = 1113151) B1113151
theorem B1484255 : Blo 988596 1484255 := bstep (se 1 (by rfl) ⟨1113191, by rfl⟩ : syracuseStep 1484255 = 2226383) B2226383
theorem B19048223 : Blo 988596 19048223 := bstep (se 1 (by rfl) ⟨14286167, by rfl⟩ : syracuseStep 19048223 = 28572335) B28572335
theorem B81405971 : Blo 988596 81405971 := bstep (se 1 (by rfl) ⟨61054478, by rfl⟩ : syracuseStep 81405971 = 122108957) B122108957
theorem B1255495 : Blo 988596 1255495 := bstep (se 1 (by rfl) ⟨941621, by rfl⟩ : syracuseStep 1255495 = 1883243) B1883243
theorem B16918631 : Blo 988596 16918631 := bstep (se 1 (by rfl) ⟨12688973, by rfl⟩ : syracuseStep 16918631 = 25377947) B25377947
theorem B1484975 : Blo 988596 1484975 := bstep (se 1 (by rfl) ⟨1113731, by rfl⟩ : syracuseStep 1484975 = 2227463) B2227463
theorem B5023943 : Blo 988596 5023943 := bstep (se 1 (by rfl) ⟨3767957, by rfl⟩ : syracuseStep 5023943 = 7535915) B7535915
theorem B1878223 : Blo 988596 1878223 := bstep (se 1 (by rfl) ⟨1408667, by rfl⟩ : syracuseStep 1878223 = 2817335) B2817335
theorem B1485353 : Blo 988596 1485353 := bstep (se 2 (by rfl) ⟨557007, by rfl⟩ : syracuseStep 1485353 = 1114015) B1114015
theorem B1485599 : Blo 988596 1485599 := bstep (se 1 (by rfl) ⟨1114199, by rfl⟩ : syracuseStep 1485599 = 2228399) B2228399
theorem B1485851 : Blo 988596 1485851 := bstep (se 1 (by rfl) ⟨1114388, by rfl⟩ : syracuseStep 1485851 = 2228777) B2228777
theorem B1485929 : Blo 988596 1485929 := bstep (se 2 (by rfl) ⟨557223, by rfl⟩ : syracuseStep 1485929 = 1114447) B1114447
theorem B7613615 : Blo 988596 7613615 := bstep (se 1 (by rfl) ⟨5710211, by rfl⟩ : syracuseStep 7613615 = 11420423) B11420423
theorem B57159431 : Blo 988596 57159431 := bstep (se 1 (by rfl) ⟨42869573, by rfl⟩ : syracuseStep 57159431 = 85739147) B85739147
theorem B1781671 : Blo 988596 1781671 := bstep (se 1 (by rfl) ⟨1336253, by rfl⟩ : syracuseStep 1781671 = 2672507) B2672507
theorem B1487327 : Blo 988596 1487327 := bstep (se 1 (by rfl) ⟨1115495, by rfl⟩ : syracuseStep 1487327 = 2230991) B2230991
theorem B17183825 : Blo 988596 17183825 := bstep (se 2 (by rfl) ⟨6443934, by rfl⟩ : syracuseStep 17183825 = 12887869) B12887869
theorem B1487975 : Blo 988596 1487975 := bstep (se 1 (by rfl) ⟨1115981, by rfl⟩ : syracuseStep 1487975 = 2231963) B2231963
theorem B27112643 : Blo 988596 27112643 := bstep (se 1 (by rfl) ⟨20334482, by rfl⟩ : syracuseStep 27112643 = 40668965) B40668965
theorem B3815119 : Blo 988596 3815119 := bstep (se 1 (by rfl) ⟨2861339, by rfl⟩ : syracuseStep 3815119 = 5722679) B5722679
theorem B1881967 : Blo 988596 1881967 := bstep (se 1 (by rfl) ⟨1411475, by rfl⟩ : syracuseStep 1881967 = 2822951) B2822951
theorem B5650343 : Blo 988596 5650343 := bstep (se 1 (by rfl) ⟨4237757, by rfl⟩ : syracuseStep 5650343 = 8475515) B8475515
theorem B9779449 : Blo 988596 9779449 := bstep (se 2 (by rfl) ⟨3667293, by rfl⟩ : syracuseStep 9779449 = 7334587) B7334587
theorem B8469157 : Blo 988596 8469157 := bstep (se 4 (by rfl) ⟨793983, by rfl⟩ : syracuseStep 8469157 = 1587967) B1587967
theorem B32096411 : Blo 988596 32096411 := bstep (se 1 (by rfl) ⟨24072308, by rfl⟩ : syracuseStep 32096411 = 48144617) B48144617
theorem B2375993 : Blo 988596 2375993 := bstep (se 2 (by rfl) ⟨890997, by rfl⟩ : syracuseStep 2375993 = 1781995) B1781995
theorem B2507071 : Blo 988596 2507071 := bstep (se 1 (by rfl) ⟨1880303, by rfl⟩ : syracuseStep 2507071 = 3760607) B3760607
theorem B2148187 : Blo 988596 2148187 := bstep (se 1 (by rfl) ⟨1611140, by rfl⟩ : syracuseStep 2148187 = 3222281) B3222281
theorem B12700151 : Blo 988596 12700151 := bstep (se 1 (by rfl) ⟨9525113, by rfl⟩ : syracuseStep 12700151 = 19050227) B19050227
theorem B19321825 : Blo 988596 19321825 := bstep (se 2 (by rfl) ⟨7245684, by rfl⟩ : syracuseStep 19321825 = 14491369) B14491369
theorem B2545199 : Blo 988596 2545199 := bstep (se 1 (by rfl) ⟨1908899, by rfl⟩ : syracuseStep 2545199 = 3817799) B3817799
theorem B2383643 : Blo 988596 2383643 := bstep (se 1 (by rfl) ⟨1787732, by rfl⟩ : syracuseStep 2383643 = 3575465) B3575465
theorem B4514395 : Blo 988596 4514395 := bstep (se 1 (by rfl) ⟨3385796, by rfl⟩ : syracuseStep 4514395 = 6771593) B6771593
theorem B2384873 : Blo 988596 2384873 := bstep (se 2 (by rfl) ⟨894327, by rfl⟩ : syracuseStep 2384873 = 1788655) B1788655
theorem B5006447 : Blo 988596 5006447 := bstep (se 1 (by rfl) ⟨3754835, by rfl⟩ : syracuseStep 5006447 = 7509671) B7509671
theorem B8447287 : Blo 988596 8447287 := bstep (se 1 (by rfl) ⟨6335465, by rfl⟩ : syracuseStep 8447287 = 12670931) B12670931
theorem B6022991 : Blo 988596 6022991 := bstep (se 1 (by rfl) ⟨4517243, by rfl⟩ : syracuseStep 6022991 = 9034487) B9034487
theorem B139388855 : Blo 988596 139388855 := bstep (se 1 (by rfl) ⟨104541641, by rfl⟩ : syracuseStep 139388855 = 209083283) B209083283
theorem B5007581 : Blo 988596 5007581 := bstep (se 3 (by rfl) ⟨938921, by rfl⟩ : syracuseStep 5007581 = 1877843) B1877843
theorem B3172783 : Blo 988596 3172783 := bstep (se 1 (by rfl) ⟨2379587, by rfl⟩ : syracuseStep 3172783 = 4759175) B4759175
theorem B3336929 : Blo 988596 3336929 := bstep (se 2 (by rfl) ⟨1251348, by rfl⟩ : syracuseStep 3336929 = 2502697) B2502697
theorem B12053377 : Blo 988596 12053377 := bstep (se 2 (by rfl) ⟨4520016, by rfl⟩ : syracuseStep 12053377 = 9040033) B9040033
theorem B5073977 : Blo 988596 5073977 := bstep (se 2 (by rfl) ⟨1902741, by rfl⟩ : syracuseStep 5073977 = 3805483) B3805483
theorem B12872915 : Blo 988596 12872915 := bstep (se 1 (by rfl) ⟨9654686, by rfl⟩ : syracuseStep 12872915 = 19309373) B19309373
theorem B9039593 : Blo 988596 9039593 := bstep (se 2 (by rfl) ⟨3389847, by rfl⟩ : syracuseStep 9039593 = 6779695) B6779695
theorem B5010173 : Blo 988596 5010173 := bstep (se 3 (by rfl) ⟨939407, by rfl⟩ : syracuseStep 5010173 = 1878815) B1878815
theorem B4354975 : Blo 988596 4354975 := bstep (se 1 (by rfl) ⟨3266231, by rfl⟩ : syracuseStep 4354975 = 6532463) B6532463
theorem B281474129 : Blo 988596 281474129 := bstep (se 2 (by rfl) ⟨105552798, by rfl⟩ : syracuseStep 281474129 = 211105597) B211105597
theorem B3339359 : Blo 988596 3339359 := bstep (se 1 (by rfl) ⟨2504519, by rfl⟩ : syracuseStep 3339359 = 5009039) B5009039
theorem B2225375 : Blo 988596 2225375 := bstep (se 1 (by rfl) ⟨1669031, by rfl⟩ : syracuseStep 2225375 = 3338063) B3338063
theorem B2226131 : Blo 988596 2226131 := bstep (se 1 (by rfl) ⟨1669598, by rfl⟩ : syracuseStep 2226131 = 3339197) B3339197
theorem B2226203 : Blo 988596 2226203 := bstep (se 1 (by rfl) ⟨1669652, by rfl⟩ : syracuseStep 2226203 = 3339305) B3339305
theorem B1669403 : Blo 988596 1669403 := bstep (se 1 (by rfl) ⟨1252052, by rfl⟩ : syracuseStep 1669403 = 2504105) B2504105
theorem B2227679 : Blo 988596 2227679 := bstep (se 1 (by rfl) ⟨1670759, by rfl⟩ : syracuseStep 2227679 = 3341519) B3341519
theorem B2227931 : Blo 988596 2227931 := bstep (se 1 (by rfl) ⟨1670948, by rfl⟩ : syracuseStep 2227931 = 3341897) B3341897
theorem B1114159 : Blo 988596 1114159 := bstep (se 1 (by rfl) ⟨835619, by rfl⟩ : syracuseStep 1114159 = 1671239) B1671239
theorem B21397607 : Blo 988596 21397607 := bstep (se 1 (by rfl) ⟨16048205, by rfl⟩ : syracuseStep 21397607 = 32096411) B32096411
theorem B1507567 : Blo 988596 1507567 := bstep (se 1 (by rfl) ⟨1130675, by rfl⟩ : syracuseStep 1507567 = 2261351) B2261351
theorem B3342761 : Blo 988596 3342761 := bstep (se 2 (by rfl) ⟨1253535, by rfl⟩ : syracuseStep 3342761 = 2507071) B2507071
theorem B9503507 : Blo 988596 9503507 := bstep (se 1 (by rfl) ⟨7127630, by rfl⟩ : syracuseStep 9503507 = 14255261) B14255261
theorem B724633235 : Blo 988596 724633235 := bstep (se 1 (by rfl) ⟨543474926, by rfl⟩ : syracuseStep 724633235 = 1086949853) B1086949853
theorem B3016603 : Blo 988596 3016603 := bstep (se 1 (by rfl) ⟨2262452, by rfl⟩ : syracuseStep 3016603 = 4524905) B4524905
theorem B36112823 : Blo 988596 36112823 := bstep (se 1 (by rfl) ⟨27084617, by rfl⟩ : syracuseStep 36112823 = 54169235) B54169235
theorem B1673993 : Blo 988596 1673993 := bstep (se 2 (by rfl) ⟨627747, by rfl⟩ : syracuseStep 1673993 = 1255495) B1255495
theorem B2231369 : Blo 988596 2231369 := bstep (se 2 (by rfl) ⟨836763, by rfl⟩ : syracuseStep 2231369 = 1673527) B1673527
theorem B4230377 : Blo 988596 4230377 := bstep (se 2 (by rfl) ⟨1586391, by rfl⟩ : syracuseStep 4230377 = 3172783) B3172783
theorem B2231711 : Blo 988596 2231711 := bstep (se 1 (by rfl) ⟨1673783, by rfl⟩ : syracuseStep 2231711 = 3347567) B3347567
theorem B5640137 : Blo 988596 5640137 := bstep (se 2 (by rfl) ⟨2115051, by rfl⟩ : syracuseStep 5640137 = 4230103) B4230103
theorem B2232575 : Blo 988596 2232575 := bstep (se 1 (by rfl) ⟨1674431, by rfl⟩ : syracuseStep 2232575 = 3348863) B3348863
theorem B12685693 : Blo 988596 12685693 := bstep (se 3 (by rfl) ⟨2378567, by rfl⟩ : syracuseStep 12685693 = 4757135) B4757135
theorem B12063887 : Blo 988596 12063887 := bstep (se 1 (by rfl) ⟨9047915, by rfl⟩ : syracuseStep 12063887 = 18095831) B18095831
theorem B989467 : Blo 988596 989467 := bstep (se 1 (by rfl) ⟨742100, by rfl⟩ : syracuseStep 989467 = 1484201) B1484201
theorem B989503 : Blo 988596 989503 := bstep (se 1 (by rfl) ⟨742127, by rfl⟩ : syracuseStep 989503 = 1484255) B1484255
theorem B25762433 : Blo 988596 25762433 := bstep (se 2 (by rfl) ⟨9660912, by rfl⟩ : syracuseStep 25762433 = 19321825) B19321825
theorem B54270647 : Blo 988596 54270647 := bstep (se 1 (by rfl) ⟨40702985, by rfl⟩ : syracuseStep 54270647 = 81405971) B81405971
theorem B11279087 : Blo 988596 11279087 := bstep (se 1 (by rfl) ⟨8459315, by rfl⟩ : syracuseStep 11279087 = 16918631) B16918631
theorem B989983 : Blo 988596 989983 := bstep (se 1 (by rfl) ⟨742487, by rfl⟩ : syracuseStep 989983 = 1484975) B1484975
theorem B3349295 : Blo 988596 3349295 := bstep (se 1 (by rfl) ⟨2511971, by rfl⟩ : syracuseStep 3349295 = 5023943) B5023943
theorem B990235 : Blo 988596 990235 := bstep (se 1 (by rfl) ⟨742676, by rfl⟩ : syracuseStep 990235 = 1485353) B1485353
theorem B990399 : Blo 988596 990399 := bstep (se 1 (by rfl) ⟨742799, by rfl⟩ : syracuseStep 990399 = 1485599) B1485599
theorem B990567 : Blo 988596 990567 := bstep (se 1 (by rfl) ⟨742925, by rfl⟩ : syracuseStep 990567 = 1485851) B1485851
theorem B3382651 : Blo 988596 3382651 := bstep (se 1 (by rfl) ⟨2536988, by rfl⟩ : syracuseStep 3382651 = 5073977) B5073977
theorem B990619 : Blo 988596 990619 := bstep (se 1 (by rfl) ⟨742964, by rfl⟩ : syracuseStep 990619 = 1485929) B1485929
theorem B991551 : Blo 988596 991551 := bstep (se 1 (by rfl) ⟨743663, by rfl⟩ : syracuseStep 991551 = 1487327) B1487327
theorem B991983 : Blo 988596 991983 := bstep (se 1 (by rfl) ⟨743987, by rfl⟩ : syracuseStep 991983 = 1487975) B1487975
theorem B1483583 : Blo 988596 1483583 := bstep (se 1 (by rfl) ⟨1112687, by rfl⟩ : syracuseStep 1483583 = 2225375) B2225375
theorem B5645537 : Blo 988596 5645537 := bstep (se 2 (by rfl) ⟨2117076, by rfl⟩ : syracuseStep 5645537 = 4234153) B4234153
theorem B1484087 : Blo 988596 1484087 := bstep (se 1 (by rfl) ⟨1113065, by rfl⟩ : syracuseStep 1484087 = 2226131) B2226131
theorem B1484135 : Blo 988596 1484135 := bstep (se 1 (by rfl) ⟨1113101, by rfl⟩ : syracuseStep 1484135 = 2226203) B2226203
theorem B1485119 : Blo 988596 1485119 := bstep (se 1 (by rfl) ⟨1113839, by rfl⟩ : syracuseStep 1485119 = 2227679) B2227679
theorem B1485287 : Blo 988596 1485287 := bstep (se 1 (by rfl) ⟨1113965, by rfl⟩ : syracuseStep 1485287 = 2227931) B2227931
theorem B1485551 : Blo 988596 1485551 := bstep (se 1 (by rfl) ⟨1114163, by rfl⟩ : syracuseStep 1485551 = 2228327) B2228327
theorem B1879195 : Blo 988596 1879195 := bstep (se 1 (by rfl) ⟨1409396, by rfl⟩ : syracuseStep 1879195 = 2818793) B2818793
theorem B1486079 : Blo 988596 1486079 := bstep (se 1 (by rfl) ⟨1114559, by rfl⟩ : syracuseStep 1486079 = 2229119) B2229119
theorem B3255743 : Blo 988596 3255743 := bstep (se 1 (by rfl) ⟨2441807, by rfl⟩ : syracuseStep 3255743 = 4883615) B4883615
theorem B6335981 : Blo 988596 6335981 := bstep (se 3 (by rfl) ⟨1187996, by rfl⟩ : syracuseStep 6335981 = 2375993) B2375993
theorem B1486439 : Blo 988596 1486439 := bstep (se 1 (by rfl) ⟨1114829, by rfl⟩ : syracuseStep 1486439 = 2229659) B2229659
theorem B8466767 : Blo 988596 8466767 := bstep (se 1 (by rfl) ⟨6350075, by rfl⟩ : syracuseStep 8466767 = 12700151) B12700151
theorem B1487591 : Blo 988596 1487591 := bstep (se 1 (by rfl) ⟨1115693, by rfl⟩ : syracuseStep 1487591 = 2231387) B2231387
theorem B2864249 : Blo 988596 2864249 := bstep (se 2 (by rfl) ⟨1074093, by rfl⟩ : syracuseStep 2864249 = 2148187) B2148187
theorem B1488041 : Blo 988596 1488041 := bstep (se 2 (by rfl) ⟨558015, by rfl⟩ : syracuseStep 1488041 = 1116031) B1116031
theorem B1488107 : Blo 988596 1488107 := bstep (se 1 (by rfl) ⟨1116080, by rfl⟩ : syracuseStep 1488107 = 2232161) B2232161
theorem B2504297 : Blo 988596 2504297 := bstep (se 2 (by rfl) ⟨939111, by rfl⟩ : syracuseStep 2504297 = 1878223) B1878223
theorem B1488767 : Blo 988596 1488767 := bstep (se 1 (by rfl) ⟨1116575, by rfl⟩ : syracuseStep 1488767 = 2233151) B2233151
theorem B1882111 : Blo 988596 1882111 := bstep (se 1 (by rfl) ⟨1411583, by rfl⟩ : syracuseStep 1882111 = 2823167) B2823167
theorem B16071169 : Blo 988596 16071169 := bstep (se 2 (by rfl) ⟨6026688, by rfl⟩ : syracuseStep 16071169 = 12053377) B12053377
theorem B371703613 : Blo 988596 371703613 := bstep (se 3 (by rfl) ⟨69694427, by rfl⟩ : syracuseStep 371703613 = 139388855) B139388855
theorem B1589095 : Blo 988596 1589095 := bstep (se 1 (by rfl) ⟨1191821, by rfl⟩ : syracuseStep 1589095 = 2383643) B2383643
theorem B2375561 : Blo 988596 2375561 := bstep (se 2 (by rfl) ⟨890835, by rfl⟩ : syracuseStep 2375561 = 1781671) B1781671
theorem B1589915 : Blo 988596 1589915 := bstep (se 1 (by rfl) ⟨1192436, by rfl⟩ : syracuseStep 1589915 = 2384873) B2384873
theorem B12698815 : Blo 988596 12698815 := bstep (se 1 (by rfl) ⟨9524111, by rfl⟩ : syracuseStep 12698815 = 19048223) B19048223
theorem B4015327 : Blo 988596 4015327 := bstep (se 1 (by rfl) ⟨3011495, by rfl⟩ : syracuseStep 4015327 = 6022991) B6022991
theorem B2509289 : Blo 988596 2509289 := bstep (se 2 (by rfl) ⟨940983, by rfl⟩ : syracuseStep 2509289 = 1881967) B1881967
theorem B187649419 : Blo 988596 187649419 := bstep (se 1 (by rfl) ⟨140737064, by rfl⟩ : syracuseStep 187649419 = 281474129) B281474129
theorem B11455883 : Blo 988596 11455883 := bstep (se 1 (by rfl) ⟨8591912, by rfl⟩ : syracuseStep 11455883 = 17183825) B17183825
theorem B18075095 : Blo 988596 18075095 := bstep (se 1 (by rfl) ⟨13556321, by rfl⟩ : syracuseStep 18075095 = 27112643) B27112643
theorem B11292209 : Blo 988596 11292209 := bstep (se 2 (by rfl) ⟨4234578, by rfl⟩ : syracuseStep 11292209 = 8469157) B8469157
theorem B2119135 : Blo 988596 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B6019193 : Blo 988596 6019193 := bstep (se 2 (by rfl) ⟨2257197, by rfl⟩ : syracuseStep 6019193 = 4514395) B4514395
theorem B6773183 : Blo 988596 6773183 := bstep (se 1 (by rfl) ⟨5079887, by rfl⟩ : syracuseStep 6773183 = 10159775) B10159775
theorem B11263049 : Blo 988596 11263049 := bstep (se 2 (by rfl) ⟨4223643, by rfl⟩ : syracuseStep 11263049 = 8447287) B8447287
theorem B10149797 : Blo 988596 10149797 := bstep (se 4 (by rfl) ⟨951543, by rfl⟩ : syracuseStep 10149797 = 1903087) B1903087
theorem B3171271 : Blo 988596 3171271 := bstep (se 1 (by rfl) ⟨2378453, by rfl⟩ : syracuseStep 3171271 = 4756907) B4756907
theorem B1696799 : Blo 988596 1696799 := bstep (se 1 (by rfl) ⟨1272599, by rfl⟩ : syracuseStep 1696799 = 2545199) B2545199
theorem B4024201 : Blo 988596 4024201 := bstep (se 2 (by rfl) ⟨1509075, by rfl⟩ : syracuseStep 4024201 = 3018151) B3018151
theorem B23226533 : Blo 988596 23226533 := bstep (se 4 (by rfl) ⟨2177487, by rfl⟩ : syracuseStep 23226533 = 4354975) B4354975
theorem B5007743 : Blo 988596 5007743 := bstep (se 1 (by rfl) ⟨3755807, by rfl⟩ : syracuseStep 5007743 = 7511615) B7511615
theorem B27094151 : Blo 988596 27094151 := bstep (se 1 (by rfl) ⟨20320613, by rfl⟩ : syracuseStep 27094151 = 40641227) B40641227
theorem B3337631 : Blo 988596 3337631 := bstep (se 1 (by rfl) ⟨2503223, by rfl⟩ : syracuseStep 3337631 = 5006447) B5006447
theorem B3338387 : Blo 988596 3338387 := bstep (se 1 (by rfl) ⟨2503790, by rfl⟩ : syracuseStep 3338387 = 5007581) B5007581
theorem B2224619 : Blo 988596 2224619 := bstep (se 1 (by rfl) ⟨1668464, by rfl⟩ : syracuseStep 2224619 = 3336929) B3336929
theorem B5075743 : Blo 988596 5075743 := bstep (se 1 (by rfl) ⟨3806807, by rfl⟩ : syracuseStep 5075743 = 7613615) B7613615
theorem B8581943 : Blo 988596 8581943 := bstep (se 1 (by rfl) ⟨6436457, by rfl⟩ : syracuseStep 8581943 = 12872915) B12872915
theorem B6026395 : Blo 988596 6026395 := bstep (se 1 (by rfl) ⟨4519796, by rfl⟩ : syracuseStep 6026395 = 9039593) B9039593
theorem B38106287 : Blo 988596 38106287 := bstep (se 1 (by rfl) ⟨28579715, by rfl⟩ : syracuseStep 38106287 = 57159431) B57159431
theorem B13039265 : Blo 988596 13039265 := bstep (se 2 (by rfl) ⟨4889724, by rfl⟩ : syracuseStep 13039265 = 9779449) B9779449
theorem B3340115 : Blo 988596 3340115 := bstep (se 1 (by rfl) ⟨2505086, by rfl⟩ : syracuseStep 3340115 = 5010173) B5010173
theorem B2226239 : Blo 988596 2226239 := bstep (se 1 (by rfl) ⟨1669679, by rfl⟩ : syracuseStep 2226239 = 3339359) B3339359
theorem B20347301 : Blo 988596 20347301 := bstep (se 4 (by rfl) ⟨1907559, by rfl⟩ : syracuseStep 20347301 = 3815119) B3815119
theorem B3766895 : Blo 988596 3766895 := bstep (se 1 (by rfl) ⟨2825171, by rfl⟩ : syracuseStep 3766895 = 5650343) B5650343
theorem B1112935 : Blo 988596 1112935 := bstep (se 1 (by rfl) ⟨834701, by rfl⟩ : syracuseStep 1112935 = 1669403) B1669403
theorem B2228507 : Blo 988596 2228507 := bstep (se 1 (by rfl) ⟨1671380, by rfl⟩ : syracuseStep 2228507 = 3342761) B3342761
theorem B4228361 : Blo 988596 4228361 := bstep (se 2 (by rfl) ⟨1585635, by rfl⟩ : syracuseStep 4228361 = 3171271) B3171271
theorem B1672859 : Blo 988596 1672859 := bstep (se 1 (by rfl) ⟨1254644, by rfl⟩ : syracuseStep 1672859 = 2509289) B2509289
theorem B1115995 : Blo 988596 1115995 := bstep (se 1 (by rfl) ⟨836996, by rfl⟩ : syracuseStep 1115995 = 1673993) B1673993
theorem B2820251 : Blo 988596 2820251 := bstep (se 1 (by rfl) ⟨2115188, by rfl⟩ : syracuseStep 2820251 = 4230377) B4230377
theorem B7637255 : Blo 988596 7637255 := bstep (se 1 (by rfl) ⟨5727941, by rfl⟩ : syracuseStep 7637255 = 11455883) B11455883
theorem B4524797 : Blo 988596 4524797 := bstep (se 3 (by rfl) ⟨848399, by rfl⟩ : syracuseStep 4524797 = 1696799) B1696799
theorem B36180431 : Blo 988596 36180431 := bstep (se 1 (by rfl) ⟨27135323, by rfl⟩ : syracuseStep 36180431 = 54270647) B54270647
theorem B2232863 : Blo 988596 2232863 := bstep (se 1 (by rfl) ⟨1674647, by rfl⟩ : syracuseStep 2232863 = 3349295) B3349295
theorem B7508699 : Blo 988596 7508699 := bstep (se 1 (by rfl) ⟨5631524, by rfl⟩ : syracuseStep 7508699 = 11263049) B11263049
theorem B16914257 : Blo 988596 16914257 := bstep (se 2 (by rfl) ⟨6342846, by rfl⟩ : syracuseStep 16914257 = 12685693) B12685693
theorem B989055 : Blo 988596 989055 := bstep (se 1 (by rfl) ⟨741791, by rfl⟩ : syracuseStep 989055 = 1483583) B1483583
theorem B989391 : Blo 988596 989391 := bstep (se 1 (by rfl) ⟨742043, by rfl⟩ : syracuseStep 989391 = 1484087) B1484087
theorem B989423 : Blo 988596 989423 := bstep (se 1 (by rfl) ⟨742067, by rfl⟩ : syracuseStep 989423 = 1484135) B1484135
theorem B8035193 : Blo 988596 8035193 := bstep (se 2 (by rfl) ⟨3013197, by rfl⟩ : syracuseStep 8035193 = 6026395) B6026395
theorem B990079 : Blo 988596 990079 := bstep (se 1 (by rfl) ⟨742559, by rfl⟩ : syracuseStep 990079 = 1485119) B1485119
theorem B990191 : Blo 988596 990191 := bstep (se 1 (by rfl) ⟨742643, by rfl⟩ : syracuseStep 990191 = 1485287) B1485287
theorem B990367 : Blo 988596 990367 := bstep (se 1 (by rfl) ⟨742775, by rfl⟩ : syracuseStep 990367 = 1485551) B1485551
theorem B2825513 : Blo 988596 2825513 := bstep (se 2 (by rfl) ⟨1059567, by rfl⟩ : syracuseStep 2825513 = 2119135) B2119135
theorem B18062767 : Blo 988596 18062767 := bstep (se 1 (by rfl) ⟨13547075, by rfl⟩ : syracuseStep 18062767 = 27094151) B27094151
theorem B990719 : Blo 988596 990719 := bstep (se 1 (by rfl) ⟨743039, by rfl⟩ : syracuseStep 990719 = 1486079) B1486079
theorem B2170495 : Blo 988596 2170495 := bstep (se 1 (by rfl) ⟨1627871, by rfl⟩ : syracuseStep 2170495 = 3255743) B3255743
theorem B990959 : Blo 988596 990959 := bstep (se 1 (by rfl) ⟨743219, by rfl⟩ : syracuseStep 990959 = 1486439) B1486439
theorem B5644511 : Blo 988596 5644511 := bstep (se 1 (by rfl) ⟨4233383, by rfl⟩ : syracuseStep 5644511 = 8466767) B8466767
theorem B1483079 : Blo 988596 1483079 := bstep (se 1 (by rfl) ⟨1112309, by rfl⟩ : syracuseStep 1483079 = 2224619) B2224619
theorem B991727 : Blo 988596 991727 := bstep (se 1 (by rfl) ⟨743795, by rfl⟩ : syracuseStep 991727 = 1487591) B1487591
theorem B1909499 : Blo 988596 1909499 := bstep (se 1 (by rfl) ⟨1432124, by rfl⟩ : syracuseStep 1909499 = 2864249) B2864249
theorem B992027 : Blo 988596 992027 := bstep (se 1 (by rfl) ⟨744020, by rfl⟩ : syracuseStep 992027 = 1488041) B1488041
theorem B25404191 : Blo 988596 25404191 := bstep (se 1 (by rfl) ⟨19053143, by rfl⟩ : syracuseStep 25404191 = 38106287) B38106287
theorem B992071 : Blo 988596 992071 := bstep (se 1 (by rfl) ⟨744053, by rfl⟩ : syracuseStep 992071 = 1488107) B1488107
theorem B8692843 : Blo 988596 8692843 := bstep (se 1 (by rfl) ⟨6519632, by rfl⟩ : syracuseStep 8692843 = 13039265) B13039265
theorem B1483913 : Blo 988596 1483913 := bstep (se 2 (by rfl) ⟨556467, by rfl⟩ : syracuseStep 1483913 = 1112935) B1112935
theorem B992511 : Blo 988596 992511 := bstep (se 1 (by rfl) ⟨744383, by rfl⟩ : syracuseStep 992511 = 1488767) B1488767
theorem B1484159 : Blo 988596 1484159 := bstep (se 1 (by rfl) ⟨1113119, by rfl⟩ : syracuseStep 1484159 = 2226239) B2226239
theorem B1583707 : Blo 988596 1583707 := bstep (se 1 (by rfl) ⟨1187780, by rfl⟩ : syracuseStep 1583707 = 2375561) B2375561
theorem B1485545 : Blo 988596 1485545 := bstep (se 2 (by rfl) ⟨557079, by rfl⟩ : syracuseStep 1485545 = 1114159) B1114159
theorem B14265071 : Blo 988596 14265071 := bstep (se 1 (by rfl) ⟨10698803, by rfl⟩ : syracuseStep 14265071 = 21397607) B21397607
theorem B2010089 : Blo 988596 2010089 := bstep (se 2 (by rfl) ⟨753783, by rfl⟩ : syracuseStep 2010089 = 1507567) B1507567
theorem B6335671 : Blo 988596 6335671 := bstep (se 1 (by rfl) ⟨4751753, by rfl⟩ : syracuseStep 6335671 = 9503507) B9503507
theorem B5353769 : Blo 988596 5353769 := bstep (se 2 (by rfl) ⟨2007663, by rfl⟩ : syracuseStep 5353769 = 4015327) B4015327
theorem B4239773 : Blo 988596 4239773 := bstep (se 3 (by rfl) ⟨794957, by rfl⟩ : syracuseStep 4239773 = 1589915) B1589915
theorem B1487579 : Blo 988596 1487579 := bstep (se 1 (by rfl) ⟨1115684, by rfl⟩ : syracuseStep 1487579 = 2231369) B2231369
theorem B1487807 : Blo 988596 1487807 := bstep (se 1 (by rfl) ⟨1115855, by rfl⟩ : syracuseStep 1487807 = 2231711) B2231711
theorem B1488383 : Blo 988596 1488383 := bstep (se 1 (by rfl) ⟨1116287, by rfl⟩ : syracuseStep 1488383 = 2232575) B2232575
theorem B8042591 : Blo 988596 8042591 := bstep (se 1 (by rfl) ⟨6031943, by rfl⟩ : syracuseStep 8042591 = 12063887) B12063887
theorem B4012795 : Blo 988596 4012795 := bstep (se 1 (by rfl) ⟨3009596, by rfl⟩ : syracuseStep 4012795 = 6019193) B6019193
theorem B2505593 : Blo 988596 2505593 := bstep (se 2 (by rfl) ⟨939597, by rfl⟩ : syracuseStep 2505593 = 1879195) B1879195
theorem B7519391 : Blo 988596 7519391 := bstep (se 1 (by rfl) ⟨5639543, by rfl⟩ : syracuseStep 7519391 = 11279087) B11279087
theorem B250199225 : Blo 988596 250199225 := bstep (se 2 (by rfl) ⟨93824709, by rfl⟩ : syracuseStep 250199225 = 187649419) B187649419
theorem B6767657 : Blo 988596 6767657 := bstep (se 2 (by rfl) ⟨2537871, by rfl⟩ : syracuseStep 6767657 = 5075743) B5075743
theorem B15484355 : Blo 988596 15484355 := bstep (se 1 (by rfl) ⟨11613266, by rfl⟩ : syracuseStep 15484355 = 23226533) B23226533
theorem B68699821 : Blo 988596 68699821 := bstep (se 3 (by rfl) ⟨12881216, by rfl⟩ : syracuseStep 68699821 = 25762433) B25762433
theorem B18040805 : Blo 988596 18040805 := bstep (se 4 (by rfl) ⟨1691325, by rfl⟩ : syracuseStep 18040805 = 3382651) B3382651
theorem B2509481 : Blo 988596 2509481 := bstep (se 2 (by rfl) ⟨941055, by rfl⟩ : syracuseStep 2509481 = 1882111) B1882111
theorem B5721295 : Blo 988596 5721295 := bstep (se 1 (by rfl) ⟨4290971, by rfl⟩ : syracuseStep 5721295 = 8581943) B8581943
theorem B2511263 : Blo 988596 2511263 := bstep (se 1 (by rfl) ⟨1883447, by rfl⟩ : syracuseStep 2511263 = 3766895) B3766895
theorem B495604817 : Blo 988596 495604817 := bstep (se 2 (by rfl) ⟨185851806, by rfl⟩ : syracuseStep 495604817 = 371703613) B371703613
theorem B2118793 : Blo 988596 2118793 := bstep (se 2 (by rfl) ⟨794547, by rfl⟩ : syracuseStep 2118793 = 1589095) B1589095
theorem B483088823 : Blo 988596 483088823 := bstep (se 1 (by rfl) ⟨362316617, by rfl⟩ : syracuseStep 483088823 = 724633235) B724633235
theorem B16931753 : Blo 988596 16931753 := bstep (se 2 (by rfl) ⟨6349407, by rfl⟩ : syracuseStep 16931753 = 12698815) B12698815
theorem B24075215 : Blo 988596 24075215 := bstep (se 1 (by rfl) ⟨18056411, by rfl⟩ : syracuseStep 24075215 = 36112823) B36112823
theorem B12050063 : Blo 988596 12050063 := bstep (se 1 (by rfl) ⟨9037547, by rfl⟩ : syracuseStep 12050063 = 18075095) B18075095
theorem B7528139 : Blo 988596 7528139 := bstep (se 1 (by rfl) ⟨5646104, by rfl⟩ : syracuseStep 7528139 = 11292209) B11292209
theorem B5365601 : Blo 988596 5365601 := bstep (se 2 (by rfl) ⟨2012100, by rfl⟩ : syracuseStep 5365601 = 4024201) B4024201
theorem B4022137 : Blo 988596 4022137 := bstep (se 2 (by rfl) ⟨1508301, by rfl⟩ : syracuseStep 4022137 = 3016603) B3016603
theorem B3760091 : Blo 988596 3760091 := bstep (se 1 (by rfl) ⟨2820068, by rfl⟩ : syracuseStep 3760091 = 5640137) B5640137
theorem B4515455 : Blo 988596 4515455 := bstep (se 1 (by rfl) ⟨3386591, by rfl⟩ : syracuseStep 4515455 = 6773183) B6773183
theorem B3763691 : Blo 988596 3763691 := bstep (se 1 (by rfl) ⟨2822768, by rfl⟩ : syracuseStep 3763691 = 5645537) B5645537
theorem B54259469 : Blo 988596 54259469 := bstep (se 3 (by rfl) ⟨10173650, by rfl⟩ : syracuseStep 54259469 = 20347301) B20347301
theorem B3338495 : Blo 988596 3338495 := bstep (se 1 (by rfl) ⟨2503871, by rfl⟩ : syracuseStep 3338495 = 5007743) B5007743
theorem B2225087 : Blo 988596 2225087 := bstep (se 1 (by rfl) ⟨1668815, by rfl⟩ : syracuseStep 2225087 = 3337631) B3337631
theorem B4223987 : Blo 988596 4223987 := bstep (se 1 (by rfl) ⟨3167990, by rfl⟩ : syracuseStep 4223987 = 6335981) B6335981
theorem B2225591 : Blo 988596 2225591 := bstep (se 1 (by rfl) ⟨1669193, by rfl⟩ : syracuseStep 2225591 = 3338387) B3338387
theorem B21428225 : Blo 988596 21428225 := bstep (se 2 (by rfl) ⟨8035584, by rfl⟩ : syracuseStep 21428225 = 16071169) B16071169
theorem B1669531 : Blo 988596 1669531 := bstep (se 1 (by rfl) ⟨1252148, by rfl⟩ : syracuseStep 1669531 = 2504297) B2504297
theorem B2226743 : Blo 988596 2226743 := bstep (se 1 (by rfl) ⟨1670057, by rfl⟩ : syracuseStep 2226743 = 3340115) B3340115
theorem B27066125 : Blo 988596 27066125 := bstep (se 3 (by rfl) ⟨5074898, by rfl⟩ : syracuseStep 27066125 = 10149797) B10149797
theorem B2818907 : Blo 988596 2818907 := bstep (se 1 (by rfl) ⟨2114180, by rfl⟩ : syracuseStep 2818907 = 4228361) B4228361
theorem B10322903 : Blo 988596 10322903 := bstep (se 1 (by rfl) ⟨7742177, by rfl⟩ : syracuseStep 10322903 = 15484355) B15484355
theorem B1115239 : Blo 988596 1115239 := bstep (se 1 (by rfl) ⟨836429, by rfl⟩ : syracuseStep 1115239 = 1672859) B1672859
theorem B12027203 : Blo 988596 12027203 := bstep (se 1 (by rfl) ⟨9020402, by rfl⟩ : syracuseStep 12027203 = 18040805) B18040805
theorem B1672987 : Blo 988596 1672987 := bstep (se 1 (by rfl) ⟨1254740, by rfl⟩ : syracuseStep 1672987 = 2509481) B2509481
theorem B3016531 : Blo 988596 3016531 := bstep (se 1 (by rfl) ⟨2262398, by rfl⟩ : syracuseStep 3016531 = 4524797) B4524797
theorem B1674175 : Blo 988596 1674175 := bstep (se 1 (by rfl) ⟨1255631, by rfl⟩ : syracuseStep 1674175 = 2511263) B2511263
theorem B24120287 : Blo 988596 24120287 := bstep (se 1 (by rfl) ⟨18090215, by rfl⟩ : syracuseStep 24120287 = 36180431) B36180431
theorem B330403211 : Blo 988596 330403211 := bstep (se 1 (by rfl) ⟨247802408, by rfl⟩ : syracuseStep 330403211 = 495604817) B495604817
theorem B11276171 : Blo 988596 11276171 := bstep (se 1 (by rfl) ⟨8457128, by rfl⟩ : syracuseStep 11276171 = 16914257) B16914257
theorem B8033375 : Blo 988596 8033375 := bstep (se 1 (by rfl) ⟨6025031, by rfl⟩ : syracuseStep 8033375 = 12050063) B12050063
theorem B5018759 : Blo 988596 5018759 := bstep (se 1 (by rfl) ⟨3764069, by rfl⟩ : syracuseStep 5018759 = 7528139) B7528139
theorem B3577067 : Blo 988596 3577067 := bstep (se 1 (by rfl) ⟨2682800, by rfl⟩ : syracuseStep 3577067 = 5365601) B5365601
theorem B988719 : Blo 988596 988719 := bstep (se 1 (by rfl) ⟨741539, by rfl⟩ : syracuseStep 988719 = 1483079) B1483079
theorem B989275 : Blo 988596 989275 := bstep (se 1 (by rfl) ⟨741956, by rfl⟩ : syracuseStep 989275 = 1483913) B1483913
theorem B989439 : Blo 988596 989439 := bstep (se 1 (by rfl) ⟨742079, by rfl⟩ : syracuseStep 989439 = 1484159) B1484159
theorem B2825057 : Blo 988596 2825057 := bstep (se 2 (by rfl) ⟨1059396, by rfl⟩ : syracuseStep 2825057 = 2118793) B2118793
theorem B990363 : Blo 988596 990363 := bstep (se 1 (by rfl) ⟨742772, by rfl⟩ : syracuseStep 990363 = 1485545) B1485545
theorem B9510047 : Blo 988596 9510047 := bstep (se 1 (by rfl) ⟨7132535, by rfl⟩ : syracuseStep 9510047 = 14265071) B14265071
theorem B2826515 : Blo 988596 2826515 := bstep (se 1 (by rfl) ⟨2119886, by rfl⟩ : syracuseStep 2826515 = 4239773) B4239773
theorem B991719 : Blo 988596 991719 := bstep (se 1 (by rfl) ⟨743789, by rfl⟩ : syracuseStep 991719 = 1487579) B1487579
theorem B1483391 : Blo 988596 1483391 := bstep (se 1 (by rfl) ⟨1112543, by rfl⟩ : syracuseStep 1483391 = 2225087) B2225087
theorem B991871 : Blo 988596 991871 := bstep (se 1 (by rfl) ⟨743903, by rfl⟩ : syracuseStep 991871 = 1487807) B1487807
theorem B11575973 : Blo 988596 11575973 := bstep (se 4 (by rfl) ⟨1085247, by rfl⟩ : syracuseStep 11575973 = 2170495) B2170495
theorem B1483727 : Blo 988596 1483727 := bstep (se 1 (by rfl) ⟨1112795, by rfl⟩ : syracuseStep 1483727 = 2225591) B2225591
theorem B5350393 : Blo 988596 5350393 := bstep (se 2 (by rfl) ⟨2006397, by rfl⟩ : syracuseStep 5350393 = 4012795) B4012795
theorem B992255 : Blo 988596 992255 := bstep (se 1 (by rfl) ⟨744191, by rfl⟩ : syracuseStep 992255 = 1488383) B1488383
theorem B1484495 : Blo 988596 1484495 := bstep (se 1 (by rfl) ⟨1113371, by rfl⟩ : syracuseStep 1484495 = 2226743) B2226743
theorem B166799483 : Blo 988596 166799483 := bstep (se 1 (by rfl) ⟨125099612, by rfl⟩ : syracuseStep 166799483 = 250199225) B250199225
theorem B1485671 : Blo 988596 1485671 := bstep (se 1 (by rfl) ⟨1114253, by rfl⟩ : syracuseStep 1485671 = 2228507) B2228507
theorem B1880167 : Blo 988596 1880167 := bstep (se 1 (by rfl) ⟨1410125, by rfl⟩ : syracuseStep 1880167 = 2820251) B2820251
theorem B5091503 : Blo 988596 5091503 := bstep (se 1 (by rfl) ⟨3818627, by rfl⟩ : syracuseStep 5091503 = 7637255) B7637255
theorem B5091997 : Blo 988596 5091997 := bstep (se 3 (by rfl) ⟨954749, by rfl⟩ : syracuseStep 5091997 = 1909499) B1909499
theorem B91599761 : Blo 988596 91599761 := bstep (se 2 (by rfl) ⟨34349910, by rfl⟩ : syracuseStep 91599761 = 68699821) B68699821
theorem B1487993 : Blo 988596 1487993 := bstep (se 2 (by rfl) ⟨557997, by rfl⟩ : syracuseStep 1487993 = 1115995) B1115995
theorem B1488575 : Blo 988596 1488575 := bstep (se 1 (by rfl) ⟨1116431, by rfl⟩ : syracuseStep 1488575 = 2232863) B2232863
theorem B2111609 : Blo 988596 2111609 := bstep (se 2 (by rfl) ⟨791853, by rfl⟩ : syracuseStep 2111609 = 1583707) B1583707
theorem B322059215 : Blo 988596 322059215 := bstep (se 1 (by rfl) ⟨241544411, by rfl⟩ : syracuseStep 322059215 = 483088823) B483088823
theorem B5356795 : Blo 988596 5356795 := bstep (se 1 (by rfl) ⟨4017596, by rfl⟩ : syracuseStep 5356795 = 8035193) B8035193
theorem B11287835 : Blo 988596 11287835 := bstep (se 1 (by rfl) ⟨8465876, by rfl⟩ : syracuseStep 11287835 = 16931753) B16931753
theorem B1883675 : Blo 988596 1883675 := bstep (se 1 (by rfl) ⟨1412756, by rfl⟩ : syracuseStep 1883675 = 2825513) B2825513
theorem B2506727 : Blo 988596 2506727 := bstep (se 1 (by rfl) ⟨1880045, by rfl⟩ : syracuseStep 2506727 = 3760091) B3760091
theorem B2509127 : Blo 988596 2509127 := bstep (se 1 (by rfl) ⟨1881845, by rfl⟩ : syracuseStep 2509127 = 3763691) B3763691
theorem B5361727 : Blo 988596 5361727 := bstep (se 1 (by rfl) ⟨4021295, by rfl⟩ : syracuseStep 5361727 = 8042591) B8042591
theorem B5362849 : Blo 988596 5362849 := bstep (se 2 (by rfl) ⟨2011068, by rfl⟩ : syracuseStep 5362849 = 4022137) B4022137
theorem B18044083 : Blo 988596 18044083 := bstep (se 1 (by rfl) ⟨13533062, by rfl⟩ : syracuseStep 18044083 = 27066125) B27066125
theorem B4511771 : Blo 988596 4511771 := bstep (se 1 (by rfl) ⟨3383828, by rfl⟩ : syracuseStep 4511771 = 6767657) B6767657
theorem B11590457 : Blo 988596 11590457 := bstep (se 2 (by rfl) ⟨4346421, by rfl⟩ : syracuseStep 11590457 = 8692843) B8692843
theorem B5005799 : Blo 988596 5005799 := bstep (se 1 (by rfl) ⟨3754349, by rfl⟩ : syracuseStep 5005799 = 7508699) B7508699
theorem B8447561 : Blo 988596 8447561 := bstep (se 2 (by rfl) ⟨3167835, by rfl⟩ : syracuseStep 8447561 = 6335671) B6335671
theorem B7628393 : Blo 988596 7628393 := bstep (se 2 (by rfl) ⟨2860647, by rfl⟩ : syracuseStep 7628393 = 5721295) B5721295
theorem B16050143 : Blo 988596 16050143 := bstep (se 1 (by rfl) ⟨12037607, by rfl⟩ : syracuseStep 16050143 = 24075215) B24075215
theorem B3763007 : Blo 988596 3763007 := bstep (se 1 (by rfl) ⟨2822255, by rfl⟩ : syracuseStep 3763007 = 5644511) B5644511
theorem B16936127 : Blo 988596 16936127 := bstep (se 1 (by rfl) ⟨12702095, by rfl⟩ : syracuseStep 16936127 = 25404191) B25404191
theorem B3010303 : Blo 988596 3010303 := bstep (se 1 (by rfl) ⟨2257727, by rfl⟩ : syracuseStep 3010303 = 4515455) B4515455
theorem B1340059 : Blo 988596 1340059 := bstep (se 1 (by rfl) ⟨1005044, by rfl⟩ : syracuseStep 1340059 = 2010089) B2010089
theorem B36172979 : Blo 988596 36172979 := bstep (se 1 (by rfl) ⟨27129734, by rfl⟩ : syracuseStep 36172979 = 54259469) B54259469
theorem B2225663 : Blo 988596 2225663 := bstep (se 1 (by rfl) ⟨1669247, by rfl⟩ : syracuseStep 2225663 = 3338495) B3338495
theorem B3569179 : Blo 988596 3569179 := bstep (se 1 (by rfl) ⟨2676884, by rfl⟩ : syracuseStep 3569179 = 5353769) B5353769
theorem B2226041 : Blo 988596 2226041 := bstep (se 2 (by rfl) ⟨834765, by rfl⟩ : syracuseStep 2226041 = 1669531) B1669531
theorem B2815991 : Blo 988596 2815991 := bstep (se 1 (by rfl) ⟨2111993, by rfl⟩ : syracuseStep 2815991 = 4223987) B4223987
theorem B14285483 : Blo 988596 14285483 := bstep (se 1 (by rfl) ⟨10714112, by rfl⟩ : syracuseStep 14285483 = 21428225) B21428225
theorem B24083689 : Blo 988596 24083689 := bstep (se 2 (by rfl) ⟨9031383, by rfl⟩ : syracuseStep 24083689 = 18062767) B18062767
theorem B1670395 : Blo 988596 1670395 := bstep (se 1 (by rfl) ⟨1252796, by rfl⟩ : syracuseStep 1670395 = 2505593) B2505593
theorem B5012927 : Blo 988596 5012927 := bstep (se 1 (by rfl) ⟨3759695, by rfl⟩ : syracuseStep 5012927 = 7519391) B7519391
theorem B6881935 : Blo 988596 6881935 := bstep (se 1 (by rfl) ⟨5161451, by rfl⟩ : syracuseStep 6881935 = 10322903) B10322903
theorem B7537373 : Blo 988596 7537373 := bstep (se 3 (by rfl) ⟨1413257, by rfl⟩ : syracuseStep 7537373 = 2826515) B2826515
theorem B1672751 : Blo 988596 1672751 := bstep (se 1 (by rfl) ⟨1254563, by rfl⟩ : syracuseStep 1672751 = 2509127) B2509127
theorem B220268807 : Blo 988596 220268807 := bstep (se 1 (by rfl) ⟨165201605, by rfl⟩ : syracuseStep 220268807 = 330403211) B330403211
theorem B2230649 : Blo 988596 2230649 := bstep (se 2 (by rfl) ⟨836493, by rfl⟩ : syracuseStep 2230649 = 1672987) B1672987
theorem B3345839 : Blo 988596 3345839 := bstep (se 1 (by rfl) ⟨2509379, by rfl⟩ : syracuseStep 3345839 = 5018759) B5018759
theorem B2232233 : Blo 988596 2232233 := bstep (se 2 (by rfl) ⟨837087, by rfl⟩ : syracuseStep 2232233 = 1674175) B1674175
theorem B7148969 : Blo 988596 7148969 := bstep (se 2 (by rfl) ⟨2680863, by rfl⟩ : syracuseStep 7148969 = 5361727) B5361727
theorem B988927 : Blo 988596 988927 := bstep (se 1 (by rfl) ⟨741695, by rfl⟩ : syracuseStep 988927 = 1483391) B1483391
theorem B989151 : Blo 988596 989151 := bstep (se 1 (by rfl) ⟨741863, by rfl⟩ : syracuseStep 989151 = 1483727) B1483727
theorem B6789329 : Blo 988596 6789329 := bstep (se 2 (by rfl) ⟨2545998, by rfl⟩ : syracuseStep 6789329 = 5091997) B5091997
theorem B5085595 : Blo 988596 5085595 := bstep (se 1 (by rfl) ⟨3814196, by rfl⟩ : syracuseStep 5085595 = 7628393) B7628393
theorem B989663 : Blo 988596 989663 := bstep (se 1 (by rfl) ⟨742247, by rfl⟩ : syracuseStep 989663 = 1484495) B1484495
theorem B7150465 : Blo 988596 7150465 := bstep (se 2 (by rfl) ⟨2681424, by rfl⟩ : syracuseStep 7150465 = 5362849) B5362849
theorem B24058777 : Blo 988596 24058777 := bstep (se 2 (by rfl) ⟨9022041, by rfl⟩ : syracuseStep 24058777 = 18044083) B18044083
theorem B990447 : Blo 988596 990447 := bstep (se 1 (by rfl) ⟨742835, by rfl⟩ : syracuseStep 990447 = 1485671) B1485671
theorem B4758905 : Blo 988596 4758905 := bstep (se 2 (by rfl) ⟨1784589, by rfl⟩ : syracuseStep 4758905 = 3569179) B3569179
theorem B30907885 : Blo 988596 30907885 := bstep (se 3 (by rfl) ⟨5795228, by rfl⟩ : syracuseStep 30907885 = 11590457) B11590457
theorem B991995 : Blo 988596 991995 := bstep (se 1 (by rfl) ⟨743996, by rfl⟩ : syracuseStep 991995 = 1487993) B1487993
theorem B1483775 : Blo 988596 1483775 := bstep (se 1 (by rfl) ⟨1112831, by rfl⟩ : syracuseStep 1483775 = 2225663) B2225663
theorem B992383 : Blo 988596 992383 := bstep (se 1 (by rfl) ⟨744287, by rfl⟩ : syracuseStep 992383 = 1488575) B1488575
theorem B1484027 : Blo 988596 1484027 := bstep (se 1 (by rfl) ⟨1113020, by rfl⟩ : syracuseStep 1484027 = 2226041) B2226041
theorem B1877327 : Blo 988596 1877327 := bstep (se 1 (by rfl) ⟨1407995, by rfl⟩ : syracuseStep 1877327 = 2815991) B2815991
theorem B5023133 : Blo 988596 5023133 := bstep (se 3 (by rfl) ⟨941837, by rfl⟩ : syracuseStep 5023133 = 1883675) B1883675
theorem B214706143 : Blo 988596 214706143 := bstep (se 1 (by rfl) ⟨161029607, by rfl⟩ : syracuseStep 214706143 = 322059215) B322059215
theorem B13577341 : Blo 988596 13577341 := bstep (se 3 (by rfl) ⟨2545751, by rfl⟩ : syracuseStep 13577341 = 5091503) B5091503
theorem B1879271 : Blo 988596 1879271 := bstep (se 1 (by rfl) ⟨1409453, by rfl⟩ : syracuseStep 1879271 = 2818907) B2818907
theorem B1486985 : Blo 988596 1486985 := bstep (se 2 (by rfl) ⟨557619, by rfl⟩ : syracuseStep 1486985 = 1115239) B1115239
theorem B7517447 : Blo 988596 7517447 := bstep (se 1 (by rfl) ⟨5638085, by rfl⟩ : syracuseStep 7517447 = 11276171) B11276171
theorem B6340031 : Blo 988596 6340031 := bstep (se 1 (by rfl) ⟨4755023, by rfl⟩ : syracuseStep 6340031 = 9510047) B9510047
theorem B2506889 : Blo 988596 2506889 := bstep (se 2 (by rfl) ⟨940083, by rfl⟩ : syracuseStep 2506889 = 1880167) B1880167
theorem B7717315 : Blo 988596 7717315 := bstep (se 1 (by rfl) ⟨5787986, by rfl⟩ : syracuseStep 7717315 = 11575973) B11575973
theorem B1786745 : Blo 988596 1786745 := bstep (se 2 (by rfl) ⟨670029, by rfl⟩ : syracuseStep 1786745 = 1340059) B1340059
theorem B10700095 : Blo 988596 10700095 := bstep (se 1 (by rfl) ⟨8025071, by rfl⟩ : syracuseStep 10700095 = 16050143) B16050143
theorem B111199655 : Blo 988596 111199655 := bstep (se 1 (by rfl) ⟨83399741, by rfl⟩ : syracuseStep 111199655 = 166799483) B166799483
theorem B2508671 : Blo 988596 2508671 := bstep (se 1 (by rfl) ⟨1881503, by rfl⟩ : syracuseStep 2508671 = 3763007) B3763007
theorem B11290751 : Blo 988596 11290751 := bstep (se 1 (by rfl) ⟨8468063, by rfl⟩ : syracuseStep 11290751 = 16936127) B16936127
theorem B61066507 : Blo 988596 61066507 := bstep (se 1 (by rfl) ⟨45799880, by rfl⟩ : syracuseStep 61066507 = 91599761) B91599761
theorem B9523655 : Blo 988596 9523655 := bstep (se 1 (by rfl) ⟨7142741, by rfl⟩ : syracuseStep 9523655 = 14285483) B14285483
theorem B7525223 : Blo 988596 7525223 := bstep (se 1 (by rfl) ⟨5643917, by rfl⟩ : syracuseStep 7525223 = 11287835) B11287835
theorem B8018135 : Blo 988596 8018135 := bstep (se 1 (by rfl) ⟨6013601, by rfl⟩ : syracuseStep 8018135 = 12027203) B12027203
theorem B16080191 : Blo 988596 16080191 := bstep (se 1 (by rfl) ⟨12060143, by rfl⟩ : syracuseStep 16080191 = 24120287) B24120287
theorem B21422333 : Blo 988596 21422333 := bstep (se 3 (by rfl) ⟨4016687, by rfl⟩ : syracuseStep 21422333 = 8033375) B8033375
theorem B2384711 : Blo 988596 2384711 := bstep (se 1 (by rfl) ⟨1788533, by rfl⟩ : syracuseStep 2384711 = 3577067) B3577067
theorem B3007847 : Blo 988596 3007847 := bstep (se 1 (by rfl) ⟨2255885, by rfl⟩ : syracuseStep 3007847 = 4511771) B4511771
theorem B28535429 : Blo 988596 28535429 := bstep (se 4 (by rfl) ⟨2675196, by rfl⟩ : syracuseStep 28535429 = 5350393) B5350393
theorem B5630957 : Blo 988596 5630957 := bstep (se 3 (by rfl) ⟨1055804, by rfl⟩ : syracuseStep 5630957 = 2111609) B2111609
theorem B3337199 : Blo 988596 3337199 := bstep (se 1 (by rfl) ⟨2502899, by rfl⟩ : syracuseStep 3337199 = 5005799) B5005799
theorem B5631707 : Blo 988596 5631707 := bstep (se 1 (by rfl) ⟨4223780, by rfl⟩ : syracuseStep 5631707 = 8447561) B8447561
theorem B7533485 : Blo 988596 7533485 := bstep (se 3 (by rfl) ⟨1412528, by rfl⟩ : syracuseStep 7533485 = 2825057) B2825057
theorem B24115319 : Blo 988596 24115319 := bstep (se 1 (by rfl) ⟨18086489, by rfl⟩ : syracuseStep 24115319 = 36172979) B36172979
theorem B16054949 : Blo 988596 16054949 := bstep (se 4 (by rfl) ⟨1505151, by rfl⟩ : syracuseStep 16054949 = 3010303) B3010303
theorem B32111585 : Blo 988596 32111585 := bstep (se 2 (by rfl) ⟨12041844, by rfl⟩ : syracuseStep 32111585 = 24083689) B24083689
theorem B2227193 : Blo 988596 2227193 := bstep (se 2 (by rfl) ⟨835197, by rfl⟩ : syracuseStep 2227193 = 1670395) B1670395
theorem B7142393 : Blo 988596 7142393 := bstep (se 2 (by rfl) ⟨2678397, by rfl⟩ : syracuseStep 7142393 = 5356795) B5356795
theorem B16088165 : Blo 988596 16088165 := bstep (se 4 (by rfl) ⟨1508265, by rfl⟩ : syracuseStep 16088165 = 3016531) B3016531
theorem B3341951 : Blo 988596 3341951 := bstep (se 1 (by rfl) ⟨2506463, by rfl⟩ : syracuseStep 3341951 = 5012927) B5012927
theorem B1671151 : Blo 988596 1671151 := bstep (se 1 (by rfl) ⟨1253363, by rfl⟩ : syracuseStep 1671151 = 2506727) B2506727
theorem B1671259 : Blo 988596 1671259 := bstep (se 1 (by rfl) ⟨1253444, by rfl⟩ : syracuseStep 1671259 = 2506889) B2506889
theorem B10289753 : Blo 988596 10289753 := bstep (se 2 (by rfl) ⟨3858657, by rfl⟩ : syracuseStep 10289753 = 7717315) B7717315
theorem B9175913 : Blo 988596 9175913 := bstep (se 2 (by rfl) ⟨3440967, by rfl⟩ : syracuseStep 9175913 = 6881935) B6881935
theorem B1115167 : Blo 988596 1115167 := bstep (se 1 (by rfl) ⟨836375, by rfl⟩ : syracuseStep 1115167 = 1672751) B1672751
theorem B1672447 : Blo 988596 1672447 := bstep (se 1 (by rfl) ⟨1254335, by rfl⟩ : syracuseStep 1672447 = 2508671) B2508671
theorem B2230559 : Blo 988596 2230559 := bstep (se 1 (by rfl) ⟨1672919, by rfl⟩ : syracuseStep 2230559 = 3345839) B3345839
theorem B5016815 : Blo 988596 5016815 := bstep (se 1 (by rfl) ⟨3762611, by rfl⟩ : syracuseStep 5016815 = 7525223) B7525223
theorem B4526219 : Blo 988596 4526219 := bstep (se 1 (by rfl) ⟨3394664, by rfl⟩ : syracuseStep 4526219 = 6789329) B6789329
theorem B5345423 : Blo 988596 5345423 := bstep (se 1 (by rfl) ⟨4009067, by rfl⟩ : syracuseStep 5345423 = 8018135) B8018135
theorem B10720127 : Blo 988596 10720127 := bstep (se 1 (by rfl) ⟨8040095, by rfl⟩ : syracuseStep 10720127 = 16080191) B16080191
theorem B989183 : Blo 988596 989183 := bstep (se 1 (by rfl) ⟨741887, by rfl⟩ : syracuseStep 989183 = 1483775) B1483775
theorem B989351 : Blo 988596 989351 := bstep (se 1 (by rfl) ⟨742013, by rfl⟩ : syracuseStep 989351 = 1484027) B1484027
theorem B1251551 : Blo 988596 1251551 := bstep (se 1 (by rfl) ⟨938663, by rfl⟩ : syracuseStep 1251551 = 1877327) B1877327
theorem B2005231 : Blo 988596 2005231 := bstep (se 1 (by rfl) ⟨1503923, by rfl⟩ : syracuseStep 2005231 = 3007847) B3007847
theorem B3348755 : Blo 988596 3348755 := bstep (se 1 (by rfl) ⟨2511566, by rfl⟩ : syracuseStep 3348755 = 5023133) B5023133
theorem B1252847 : Blo 988596 1252847 := bstep (se 1 (by rfl) ⟨939635, by rfl⟩ : syracuseStep 1252847 = 1879271) B1879271
theorem B991323 : Blo 988596 991323 := bstep (se 1 (by rfl) ⟨743492, by rfl⟩ : syracuseStep 991323 = 1486985) B1486985
theorem B5022323 : Blo 988596 5022323 := bstep (se 1 (by rfl) ⟨3766742, by rfl⟩ : syracuseStep 5022323 = 7533485) B7533485
theorem B21407723 : Blo 988596 21407723 := bstep (se 1 (by rfl) ⟨16055792, by rfl⟩ : syracuseStep 21407723 = 32111585) B32111585
theorem B1484795 : Blo 988596 1484795 := bstep (se 1 (by rfl) ⟨1113596, by rfl⟩ : syracuseStep 1484795 = 2227193) B2227193
theorem B4761595 : Blo 988596 4761595 := bstep (se 1 (by rfl) ⟨3571196, by rfl⟩ : syracuseStep 4761595 = 7142393) B7142393
theorem B10725443 : Blo 988596 10725443 := bstep (se 1 (by rfl) ⟨8044082, by rfl⟩ : syracuseStep 10725443 = 16088165) B16088165
theorem B5024915 : Blo 988596 5024915 := bstep (se 1 (by rfl) ⟨3768686, by rfl⟩ : syracuseStep 5024915 = 7537373) B7537373
theorem B146845871 : Blo 988596 146845871 := bstep (se 1 (by rfl) ⟨110134403, by rfl⟩ : syracuseStep 146845871 = 220268807) B220268807
theorem B1487099 : Blo 988596 1487099 := bstep (se 1 (by rfl) ⟨1115324, by rfl⟩ : syracuseStep 1487099 = 2230649) B2230649
theorem B14266793 : Blo 988596 14266793 := bstep (se 2 (by rfl) ⟨5350047, by rfl⟩ : syracuseStep 14266793 = 10700095) B10700095
theorem B4764653 : Blo 988596 4764653 := bstep (se 3 (by rfl) ⟨893372, by rfl⟩ : syracuseStep 4764653 = 1786745) B1786745
theorem B1488155 : Blo 988596 1488155 := bstep (se 1 (by rfl) ⟨1116116, by rfl⟩ : syracuseStep 1488155 = 2232233) B2232233
theorem B286274857 : Blo 988596 286274857 := bstep (se 2 (by rfl) ⟨107353071, by rfl⟩ : syracuseStep 286274857 = 214706143) B214706143
theorem B4765979 : Blo 988596 4765979 := bstep (se 1 (by rfl) ⟨3574484, by rfl⟩ : syracuseStep 4765979 = 7148969) B7148969
theorem B296532413 : Blo 988596 296532413 := bstep (se 3 (by rfl) ⟨55599827, by rfl⟩ : syracuseStep 296532413 = 111199655) B111199655
theorem B18103121 : Blo 988596 18103121 := bstep (se 2 (by rfl) ⟨6788670, by rfl⟩ : syracuseStep 18103121 = 13577341) B13577341
theorem B1589807 : Blo 988596 1589807 := bstep (se 1 (by rfl) ⟨1192355, by rfl⟩ : syracuseStep 1589807 = 2384711) B2384711
theorem B19023619 : Blo 988596 19023619 := bstep (se 1 (by rfl) ⟨14267714, by rfl⟩ : syracuseStep 19023619 = 28535429) B28535429
theorem B3753971 : Blo 988596 3753971 := bstep (se 1 (by rfl) ⟨2815478, by rfl⟩ : syracuseStep 3753971 = 5630957) B5630957
theorem B3754471 : Blo 988596 3754471 := bstep (se 1 (by rfl) ⟨2815853, by rfl⟩ : syracuseStep 3754471 = 5631707) B5631707
theorem B16076879 : Blo 988596 16076879 := bstep (se 1 (by rfl) ⟨12057659, by rfl⟩ : syracuseStep 16076879 = 24115319) B24115319
theorem B10703299 : Blo 988596 10703299 := bstep (se 1 (by rfl) ⟨8027474, by rfl⟩ : syracuseStep 10703299 = 16054949) B16054949
theorem B41210513 : Blo 988596 41210513 := bstep (se 2 (by rfl) ⟨15453942, by rfl⟩ : syracuseStep 41210513 = 30907885) B30907885
theorem B7527167 : Blo 988596 7527167 := bstep (se 1 (by rfl) ⟨5645375, by rfl⟩ : syracuseStep 7527167 = 11290751) B11290751
theorem B27123173 : Blo 988596 27123173 := bstep (se 4 (by rfl) ⟨2542797, by rfl⟩ : syracuseStep 27123173 = 5085595) B5085595
theorem B6349103 : Blo 988596 6349103 := bstep (se 1 (by rfl) ⟨4761827, by rfl⟩ : syracuseStep 6349103 = 9523655) B9523655
theorem B81422009 : Blo 988596 81422009 := bstep (se 2 (by rfl) ⟨30533253, by rfl⟩ : syracuseStep 81422009 = 61066507) B61066507
theorem B3172603 : Blo 988596 3172603 := bstep (se 1 (by rfl) ⟨2379452, by rfl⟩ : syracuseStep 3172603 = 4758905) B4758905
theorem B14281555 : Blo 988596 14281555 := bstep (se 1 (by rfl) ⟨10711166, by rfl⟩ : syracuseStep 14281555 = 21422333) B21422333
theorem B2224799 : Blo 988596 2224799 := bstep (se 1 (by rfl) ⟨1668599, by rfl⟩ : syracuseStep 2224799 = 3337199) B3337199
theorem B5011631 : Blo 988596 5011631 := bstep (se 1 (by rfl) ⟨3758723, by rfl⟩ : syracuseStep 5011631 = 7517447) B7517447
theorem B9533953 : Blo 988596 9533953 := bstep (se 2 (by rfl) ⟨3575232, by rfl⟩ : syracuseStep 9533953 = 7150465) B7150465
theorem B32078369 : Blo 988596 32078369 := bstep (se 2 (by rfl) ⟨12029388, by rfl⟩ : syracuseStep 32078369 = 24058777) B24058777
theorem B4226687 : Blo 988596 4226687 := bstep (se 1 (by rfl) ⟨3170015, by rfl⟩ : syracuseStep 4226687 = 6340031) B6340031
theorem B2227967 : Blo 988596 2227967 := bstep (se 1 (by rfl) ⟨1670975, by rfl⟩ : syracuseStep 2227967 = 3341951) B3341951
theorem B2228201 : Blo 988596 2228201 := bstep (se 2 (by rfl) ⟨835575, by rfl⟩ : syracuseStep 2228201 = 1671151) B1671151
theorem B2228345 : Blo 988596 2228345 := bstep (se 2 (by rfl) ⟨835629, by rfl⟩ : syracuseStep 2228345 = 1671259) B1671259
theorem B2229929 : Blo 988596 2229929 := bstep (se 2 (by rfl) ⟨836223, by rfl⟩ : syracuseStep 2229929 = 1672447) B1672447
theorem B3344543 : Blo 988596 3344543 := bstep (se 1 (by rfl) ⟨2508407, by rfl⟩ : syracuseStep 3344543 = 5016815) B5016815
theorem B25364825 : Blo 988596 25364825 := bstep (se 2 (by rfl) ⟨9511809, by rfl⟩ : syracuseStep 25364825 = 19023619) B19023619
theorem B10717919 : Blo 988596 10717919 := bstep (se 1 (by rfl) ⟨8038439, by rfl⟩ : syracuseStep 10717919 = 16076879) B16076879
theorem B4230137 : Blo 988596 4230137 := bstep (se 2 (by rfl) ⟨1586301, by rfl⟩ : syracuseStep 4230137 = 3172603) B3172603
theorem B7146751 : Blo 988596 7146751 := bstep (se 1 (by rfl) ⟨5360063, by rfl⟩ : syracuseStep 7146751 = 10720127) B10720127
theorem B19042073 : Blo 988596 19042073 := bstep (se 2 (by rfl) ⟨7140777, by rfl⟩ : syracuseStep 19042073 = 14281555) B14281555
theorem B2232503 : Blo 988596 2232503 := bstep (se 1 (by rfl) ⟨1674377, by rfl⟩ : syracuseStep 2232503 = 3348755) B3348755
theorem B5018111 : Blo 988596 5018111 := bstep (se 1 (by rfl) ⟨3763583, by rfl⟩ : syracuseStep 5018111 = 7527167) B7527167
theorem B4232735 : Blo 988596 4232735 := bstep (se 1 (by rfl) ⟨3174551, by rfl⟩ : syracuseStep 4232735 = 6349103) B6349103
theorem B3348215 : Blo 988596 3348215 := bstep (se 1 (by rfl) ⟨2511161, by rfl⟩ : syracuseStep 3348215 = 5022323) B5022323
theorem B989863 : Blo 988596 989863 := bstep (se 1 (by rfl) ⟨742397, by rfl⟩ : syracuseStep 989863 = 1484795) B1484795
theorem B7150295 : Blo 988596 7150295 := bstep (se 1 (by rfl) ⟨5362721, by rfl⟩ : syracuseStep 7150295 = 10725443) B10725443
theorem B3349943 : Blo 988596 3349943 := bstep (se 1 (by rfl) ⟨2512457, by rfl⟩ : syracuseStep 3349943 = 5024915) B5024915
theorem B991399 : Blo 988596 991399 := bstep (se 1 (by rfl) ⟨743549, by rfl⟩ : syracuseStep 991399 = 1487099) B1487099
theorem B9511195 : Blo 988596 9511195 := bstep (se 1 (by rfl) ⟨7133396, by rfl⟩ : syracuseStep 9511195 = 14266793) B14266793
theorem B1483199 : Blo 988596 1483199 := bstep (se 1 (by rfl) ⟨1112399, by rfl⟩ : syracuseStep 1483199 = 2224799) B2224799
theorem B992103 : Blo 988596 992103 := bstep (se 1 (by rfl) ⟨744077, by rfl⟩ : syracuseStep 992103 = 1488155) B1488155
theorem B12068747 : Blo 988596 12068747 := bstep (se 1 (by rfl) ⟨9051560, by rfl⟩ : syracuseStep 12068747 = 18103121) B18103121
theorem B1485311 : Blo 988596 1485311 := bstep (se 1 (by rfl) ⟨1113983, by rfl⟩ : syracuseStep 1485311 = 2227967) B2227967
theorem B1485467 : Blo 988596 1485467 := bstep (se 1 (by rfl) ⟨1114100, by rfl⟩ : syracuseStep 1485467 = 2228201) B2228201
theorem B12069917 : Blo 988596 12069917 := bstep (se 3 (by rfl) ⟨2263109, by rfl⟩ : syracuseStep 12069917 = 4526219) B4526219
theorem B6859835 : Blo 988596 6859835 := bstep (se 1 (by rfl) ⟨5144876, by rfl⟩ : syracuseStep 6859835 = 10289753) B10289753
theorem B2502647 : Blo 988596 2502647 := bstep (se 1 (by rfl) ⟨1876985, by rfl⟩ : syracuseStep 2502647 = 3753971) B3753971
theorem B1486889 : Blo 988596 1486889 := bstep (se 2 (by rfl) ⟨557583, by rfl⟩ : syracuseStep 1486889 = 1115167) B1115167
theorem B4239485 : Blo 988596 4239485 := bstep (se 3 (by rfl) ⟨794903, by rfl⟩ : syracuseStep 4239485 = 1589807) B1589807
theorem B1487039 : Blo 988596 1487039 := bstep (se 1 (by rfl) ⟨1115279, by rfl⟩ : syracuseStep 1487039 = 2230559) B2230559
theorem B27473675 : Blo 988596 27473675 := bstep (se 1 (by rfl) ⟨20605256, by rfl⟩ : syracuseStep 27473675 = 41210513) B41210513
theorem B14271065 : Blo 988596 14271065 := bstep (se 2 (by rfl) ⟨5351649, by rfl⟩ : syracuseStep 14271065 = 10703299) B10703299
theorem B54281339 : Blo 988596 54281339 := bstep (se 1 (by rfl) ⟨40711004, by rfl⟩ : syracuseStep 54281339 = 81422009) B81422009
theorem B14271815 : Blo 988596 14271815 := bstep (se 1 (by rfl) ⟨10703861, by rfl⟩ : syracuseStep 14271815 = 21407723) B21407723
theorem B381699809 : Blo 988596 381699809 := bstep (se 2 (by rfl) ⟨143137428, by rfl⟩ : syracuseStep 381699809 = 286274857) B286274857
theorem B97897247 : Blo 988596 97897247 := bstep (se 1 (by rfl) ⟨73422935, by rfl⟩ : syracuseStep 97897247 = 146845871) B146845871
theorem B2673641 : Blo 988596 2673641 := bstep (se 2 (by rfl) ⟨1002615, by rfl⟩ : syracuseStep 2673641 = 2005231) B2005231
theorem B21385579 : Blo 988596 21385579 := bstep (se 1 (by rfl) ⟨16039184, by rfl⟩ : syracuseStep 21385579 = 32078369) B32078369
theorem B6117275 : Blo 988596 6117275 := bstep (se 1 (by rfl) ⟨4587956, by rfl⟩ : syracuseStep 6117275 = 9175913) B9175913
theorem B6348793 : Blo 988596 6348793 := bstep (se 2 (by rfl) ⟨2380797, by rfl⟩ : syracuseStep 6348793 = 4761595) B4761595
theorem B3563615 : Blo 988596 3563615 := bstep (se 1 (by rfl) ⟨2672711, by rfl⟩ : syracuseStep 3563615 = 5345423) B5345423
theorem B5005961 : Blo 988596 5005961 := bstep (se 2 (by rfl) ⟨1877235, by rfl⟩ : syracuseStep 5005961 = 3754471) B3754471
theorem B18082115 : Blo 988596 18082115 := bstep (se 1 (by rfl) ⟨13561586, by rfl⟩ : syracuseStep 18082115 = 27123173) B27123173
theorem B3337469 : Blo 988596 3337469 := bstep (se 3 (by rfl) ⟨625775, by rfl⟩ : syracuseStep 3337469 = 1251551) B1251551
theorem B3176435 : Blo 988596 3176435 := bstep (se 1 (by rfl) ⟨2382326, by rfl⟩ : syracuseStep 3176435 = 4764653) B4764653
theorem B12711937 : Blo 988596 12711937 := bstep (se 2 (by rfl) ⟨4766976, by rfl⟩ : syracuseStep 12711937 = 9533953) B9533953
theorem B3340925 : Blo 988596 3340925 := bstep (se 3 (by rfl) ⟨626423, by rfl⟩ : syracuseStep 3340925 = 1252847) B1252847
theorem B3341087 : Blo 988596 3341087 := bstep (se 1 (by rfl) ⟨2505815, by rfl⟩ : syracuseStep 3341087 = 5011631) B5011631
theorem B3177319 : Blo 988596 3177319 := bstep (se 1 (by rfl) ⟨2382989, by rfl⟩ : syracuseStep 3177319 = 4765979) B4765979
theorem B197688275 : Blo 988596 197688275 := bstep (se 1 (by rfl) ⟨148266206, by rfl⟩ : syracuseStep 197688275 = 296532413) B296532413
theorem B2817791 : Blo 988596 2817791 := bstep (se 1 (by rfl) ⟨2113343, by rfl⟩ : syracuseStep 2817791 = 4226687) B4226687
theorem B12681593 : Blo 988596 12681593 := bstep (se 2 (by rfl) ⟨4755597, by rfl⟩ : syracuseStep 12681593 = 9511195) B9511195
theorem B2229695 : Blo 988596 2229695 := bstep (se 1 (by rfl) ⟨1672271, by rfl⟩ : syracuseStep 2229695 = 3344543) B3344543
theorem B16909883 : Blo 988596 16909883 := bstep (se 1 (by rfl) ⟨12682412, by rfl⟩ : syracuseStep 16909883 = 25364825) B25364825
theorem B7145279 : Blo 988596 7145279 := bstep (se 1 (by rfl) ⟨5358959, by rfl⟩ : syracuseStep 7145279 = 10717919) B10717919
theorem B2820091 : Blo 988596 2820091 := bstep (se 1 (by rfl) ⟨2115068, by rfl⟩ : syracuseStep 2820091 = 4230137) B4230137
theorem B3345407 : Blo 988596 3345407 := bstep (se 1 (by rfl) ⟨2509055, by rfl⟩ : syracuseStep 3345407 = 5018111) B5018111
theorem B2821823 : Blo 988596 2821823 := bstep (se 1 (by rfl) ⟨2116367, by rfl⟩ : syracuseStep 2821823 = 4232735) B4232735
theorem B2232143 : Blo 988596 2232143 := bstep (se 1 (by rfl) ⟨1674107, by rfl⟩ : syracuseStep 2232143 = 3348215) B3348215
theorem B2233295 : Blo 988596 2233295 := bstep (se 1 (by rfl) ⟨1674971, by rfl⟩ : syracuseStep 2233295 = 3349943) B3349943
theorem B988799 : Blo 988596 988799 := bstep (se 1 (by rfl) ⟨741599, by rfl⟩ : syracuseStep 988799 = 1483199) B1483199
theorem B28514105 : Blo 988596 28514105 := bstep (se 2 (by rfl) ⟨10692789, by rfl⟩ : syracuseStep 28514105 = 21385579) B21385579
theorem B990207 : Blo 988596 990207 := bstep (se 1 (by rfl) ⟨742655, by rfl⟩ : syracuseStep 990207 = 1485311) B1485311
theorem B990311 : Blo 988596 990311 := bstep (se 1 (by rfl) ⟨742733, by rfl⟩ : syracuseStep 990311 = 1485467) B1485467
theorem B16949249 : Blo 988596 16949249 := bstep (se 2 (by rfl) ⟨6355968, by rfl⟩ : syracuseStep 16949249 = 12711937) B12711937
theorem B991259 : Blo 988596 991259 := bstep (se 1 (by rfl) ⟨743444, by rfl⟩ : syracuseStep 991259 = 1486889) B1486889
theorem B2826323 : Blo 988596 2826323 := bstep (se 1 (by rfl) ⟨2119742, by rfl⟩ : syracuseStep 2826323 = 4239485) B4239485
theorem B991359 : Blo 988596 991359 := bstep (se 1 (by rfl) ⟨743519, by rfl⟩ : syracuseStep 991359 = 1487039) B1487039
theorem B4236425 : Blo 988596 4236425 := bstep (se 2 (by rfl) ⟨1588659, by rfl⟩ : syracuseStep 4236425 = 3177319) B3177319
theorem B1878527 : Blo 988596 1878527 := bstep (se 1 (by rfl) ⟨1408895, by rfl⟩ : syracuseStep 1878527 = 2817791) B2817791
theorem B8465057 : Blo 988596 8465057 := bstep (se 2 (by rfl) ⟨3174396, by rfl⟩ : syracuseStep 8465057 = 6348793) B6348793
theorem B1485563 : Blo 988596 1485563 := bstep (se 1 (by rfl) ⟨1114172, by rfl⟩ : syracuseStep 1485563 = 2228345) B2228345
theorem B9514043 : Blo 988596 9514043 := bstep (se 1 (by rfl) ⟨7135532, by rfl⟩ : syracuseStep 9514043 = 14271065) B14271065
theorem B36187559 : Blo 988596 36187559 := bstep (se 1 (by rfl) ⟨27140669, by rfl⟩ : syracuseStep 36187559 = 54281339) B54281339
theorem B9514543 : Blo 988596 9514543 := bstep (se 1 (by rfl) ⟨7135907, by rfl⟩ : syracuseStep 9514543 = 14271815) B14271815
theorem B1486619 : Blo 988596 1486619 := bstep (se 1 (by rfl) ⟨1114964, by rfl⟩ : syracuseStep 1486619 = 2229929) B2229929
theorem B1782427 : Blo 988596 1782427 := bstep (se 1 (by rfl) ⟨1336820, by rfl⟩ : syracuseStep 1782427 = 2673641) B2673641
theorem B12694715 : Blo 988596 12694715 := bstep (se 1 (by rfl) ⟨9521036, by rfl⟩ : syracuseStep 12694715 = 19042073) B19042073
theorem B1488335 : Blo 988596 1488335 := bstep (se 1 (by rfl) ⟨1116251, by rfl⟩ : syracuseStep 1488335 = 2232503) B2232503
theorem B4078183 : Blo 988596 4078183 := bstep (se 1 (by rfl) ⟨3058637, by rfl⟩ : syracuseStep 4078183 = 6117275) B6117275
theorem B4766863 : Blo 988596 4766863 := bstep (se 1 (by rfl) ⟨3575147, by rfl⟩ : syracuseStep 4766863 = 7150295) B7150295
theorem B8470493 : Blo 988596 8470493 := bstep (se 3 (by rfl) ⟨1588217, by rfl⟩ : syracuseStep 8470493 = 3176435) B3176435
theorem B2375743 : Blo 988596 2375743 := bstep (se 1 (by rfl) ⟨1781807, by rfl⟩ : syracuseStep 2375743 = 3563615) B3563615
theorem B8045831 : Blo 988596 8045831 := bstep (se 1 (by rfl) ⟨6034373, by rfl⟩ : syracuseStep 8045831 = 12068747) B12068747
theorem B8046611 : Blo 988596 8046611 := bstep (se 1 (by rfl) ⟨6034958, by rfl⟩ : syracuseStep 8046611 = 12069917) B12069917
theorem B4573223 : Blo 988596 4573223 := bstep (se 1 (by rfl) ⟨3429917, by rfl⟩ : syracuseStep 4573223 = 6859835) B6859835
theorem B254466539 : Blo 988596 254466539 := bstep (se 1 (by rfl) ⟨190849904, by rfl⟩ : syracuseStep 254466539 = 381699809) B381699809
theorem B65264831 : Blo 988596 65264831 := bstep (se 1 (by rfl) ⟨48948623, by rfl⟩ : syracuseStep 65264831 = 97897247) B97897247
theorem B9529001 : Blo 988596 9529001 := bstep (se 2 (by rfl) ⟨3573375, by rfl⟩ : syracuseStep 9529001 = 7146751) B7146751
theorem B73263133 : Blo 988596 73263133 := bstep (se 3 (by rfl) ⟨13736837, by rfl⟩ : syracuseStep 73263133 = 27473675) B27473675
theorem B3337307 : Blo 988596 3337307 := bstep (se 1 (by rfl) ⟨2502980, by rfl⟩ : syracuseStep 3337307 = 5005961) B5005961
theorem B12054743 : Blo 988596 12054743 := bstep (se 1 (by rfl) ⟨9041057, by rfl⟩ : syracuseStep 12054743 = 18082115) B18082115
theorem B2224979 : Blo 988596 2224979 := bstep (se 1 (by rfl) ⟨1668734, by rfl⟩ : syracuseStep 2224979 = 3337469) B3337469
theorem B1668431 : Blo 988596 1668431 := bstep (se 1 (by rfl) ⟨1251323, by rfl⟩ : syracuseStep 1668431 = 2502647) B2502647
theorem B2227283 : Blo 988596 2227283 := bstep (se 1 (by rfl) ⟨1670462, by rfl⟩ : syracuseStep 2227283 = 3340925) B3340925
theorem B2227391 : Blo 988596 2227391 := bstep (se 1 (by rfl) ⟨1670543, by rfl⟩ : syracuseStep 2227391 = 3341087) B3341087
theorem B131792183 : Blo 988596 131792183 := bstep (se 1 (by rfl) ⟨98844137, by rfl⟩ : syracuseStep 131792183 = 197688275) B197688275
theorem B8454395 : Blo 988596 8454395 := bstep (se 1 (by rfl) ⟨6340796, by rfl⟩ : syracuseStep 8454395 = 12681593) B12681593
theorem B11273255 : Blo 988596 11273255 := bstep (se 1 (by rfl) ⟨8454941, by rfl⟩ : syracuseStep 11273255 = 16909883) B16909883
theorem B3048815 : Blo 988596 3048815 := bstep (se 1 (by rfl) ⟨2286611, by rfl⟩ : syracuseStep 3048815 = 4573223) B4573223
theorem B2230271 : Blo 988596 2230271 := bstep (se 1 (by rfl) ⟨1672703, by rfl⟩ : syracuseStep 2230271 = 3345407) B3345407
theorem B97684177 : Blo 988596 97684177 := bstep (se 2 (by rfl) ⟨36631566, by rfl⟩ : syracuseStep 97684177 = 73263133) B73263133
theorem B19009403 : Blo 988596 19009403 := bstep (se 1 (by rfl) ⟨14257052, by rfl⟩ : syracuseStep 19009403 = 28514105) B28514105
theorem B169644359 : Blo 988596 169644359 := bstep (se 1 (by rfl) ⟨127233269, by rfl⟩ : syracuseStep 169644359 = 254466539) B254466539
theorem B12686057 : Blo 988596 12686057 := bstep (se 2 (by rfl) ⟨4757271, by rfl⟩ : syracuseStep 12686057 = 9514543) B9514543
theorem B2824283 : Blo 988596 2824283 := bstep (se 1 (by rfl) ⟨2118212, by rfl⟩ : syracuseStep 2824283 = 4236425) B4236425
theorem B1252351 : Blo 988596 1252351 := bstep (se 1 (by rfl) ⟨939263, by rfl⟩ : syracuseStep 1252351 = 1878527) B1878527
theorem B5643371 : Blo 988596 5643371 := bstep (se 1 (by rfl) ⟨4232528, by rfl⟩ : syracuseStep 5643371 = 8465057) B8465057
theorem B990375 : Blo 988596 990375 := bstep (se 1 (by rfl) ⟨742781, by rfl⟩ : syracuseStep 990375 = 1485563) B1485563
theorem B24125039 : Blo 988596 24125039 := bstep (se 1 (by rfl) ⟨18093779, by rfl⟩ : syracuseStep 24125039 = 36187559) B36187559
theorem B991079 : Blo 988596 991079 := bstep (se 1 (by rfl) ⟨743309, by rfl⟩ : syracuseStep 991079 = 1486619) B1486619
theorem B8036495 : Blo 988596 8036495 := bstep (se 1 (by rfl) ⟨6027371, by rfl⟩ : syracuseStep 8036495 = 12054743) B12054743
theorem B1483319 : Blo 988596 1483319 := bstep (se 1 (by rfl) ⟨1112489, by rfl⟩ : syracuseStep 1483319 = 2224979) B2224979
theorem B8463143 : Blo 988596 8463143 := bstep (se 1 (by rfl) ⟨6347357, by rfl⟩ : syracuseStep 8463143 = 12694715) B12694715
theorem B992223 : Blo 988596 992223 := bstep (se 1 (by rfl) ⟨744167, by rfl⟩ : syracuseStep 992223 = 1488335) B1488335
theorem B1484855 : Blo 988596 1484855 := bstep (se 1 (by rfl) ⟨1113641, by rfl⟩ : syracuseStep 1484855 = 2227283) B2227283
theorem B1484927 : Blo 988596 1484927 := bstep (se 1 (by rfl) ⟨1113695, by rfl⟩ : syracuseStep 1484927 = 2227391) B2227391
theorem B87861455 : Blo 988596 87861455 := bstep (se 1 (by rfl) ⟨65896091, by rfl⟩ : syracuseStep 87861455 = 131792183) B131792183
theorem B5646995 : Blo 988596 5646995 := bstep (se 1 (by rfl) ⟨4235246, by rfl⟩ : syracuseStep 5646995 = 8470493) B8470493
theorem B1486463 : Blo 988596 1486463 := bstep (se 1 (by rfl) ⟨1114847, by rfl⟩ : syracuseStep 1486463 = 2229695) B2229695
theorem B4763519 : Blo 988596 4763519 := bstep (se 1 (by rfl) ⟨3572639, by rfl⟩ : syracuseStep 4763519 = 7145279) B7145279
theorem B1881215 : Blo 988596 1881215 := bstep (se 1 (by rfl) ⟨1410911, by rfl⟩ : syracuseStep 1881215 = 2821823) B2821823
theorem B1488095 : Blo 988596 1488095 := bstep (se 1 (by rfl) ⟨1116071, by rfl⟩ : syracuseStep 1488095 = 2232143) B2232143
theorem B1488863 : Blo 988596 1488863 := bstep (se 1 (by rfl) ⟨1116647, by rfl⟩ : syracuseStep 1488863 = 2233295) B2233295
theorem B1884215 : Blo 988596 1884215 := bstep (se 1 (by rfl) ⟨1413161, by rfl⟩ : syracuseStep 1884215 = 2826323) B2826323
theorem B2376569 : Blo 988596 2376569 := bstep (se 2 (by rfl) ⟨891213, by rfl⟩ : syracuseStep 2376569 = 1782427) B1782427
theorem B6342695 : Blo 988596 6342695 := bstep (se 1 (by rfl) ⟨4757021, by rfl⟩ : syracuseStep 6342695 = 9514043) B9514043
theorem B3167657 : Blo 988596 3167657 := bstep (se 2 (by rfl) ⟨1187871, by rfl⟩ : syracuseStep 3167657 = 2375743) B2375743
theorem B5364407 : Blo 988596 5364407 := bstep (se 1 (by rfl) ⟨4023305, by rfl⟩ : syracuseStep 5364407 = 8046611) B8046611
theorem B3760121 : Blo 988596 3760121 := bstep (se 2 (by rfl) ⟨1410045, by rfl⟩ : syracuseStep 3760121 = 2820091) B2820091
theorem B21455549 : Blo 988596 21455549 := bstep (se 3 (by rfl) ⟨4022915, by rfl⟩ : syracuseStep 21455549 = 8045831) B8045831
theorem B43509887 : Blo 988596 43509887 := bstep (se 1 (by rfl) ⟨32632415, by rfl⟩ : syracuseStep 43509887 = 65264831) B65264831
theorem B11299499 : Blo 988596 11299499 := bstep (se 1 (by rfl) ⟨8474624, by rfl⟩ : syracuseStep 11299499 = 16949249) B16949249
theorem B6352667 : Blo 988596 6352667 := bstep (se 1 (by rfl) ⟨4764500, by rfl⟩ : syracuseStep 6352667 = 9529001) B9529001
theorem B2224871 : Blo 988596 2224871 := bstep (se 1 (by rfl) ⟨1668653, by rfl⟩ : syracuseStep 2224871 = 3337307) B3337307
theorem B5437577 : Blo 988596 5437577 := bstep (se 2 (by rfl) ⟨2039091, by rfl⟩ : syracuseStep 5437577 = 4078183) B4078183
theorem B1112287 : Blo 988596 1112287 := bstep (se 1 (by rfl) ⟨834215, by rfl⟩ : syracuseStep 1112287 = 1668431) B1668431
theorem B6355817 : Blo 988596 6355817 := bstep (se 2 (by rfl) ⟨2383431, by rfl⟩ : syracuseStep 6355817 = 4766863) B4766863
theorem B5636263 : Blo 988596 5636263 := bstep (se 1 (by rfl) ⟨4227197, by rfl⟩ : syracuseStep 5636263 = 8454395) B8454395
theorem B2032543 : Blo 988596 2032543 := bstep (se 1 (by rfl) ⟨1524407, by rfl⟩ : syracuseStep 2032543 = 3048815) B3048815
theorem B4228463 : Blo 988596 4228463 := bstep (se 1 (by rfl) ⟨3171347, by rfl⟩ : syracuseStep 4228463 = 6342695) B6342695
theorem B8457371 : Blo 988596 8457371 := bstep (se 1 (by rfl) ⟨6343028, by rfl⟩ : syracuseStep 8457371 = 12686057) B12686057
theorem B988879 : Blo 988596 988879 := bstep (se 1 (by rfl) ⟨741659, by rfl⟩ : syracuseStep 988879 = 1483319) B1483319
theorem B5642095 : Blo 988596 5642095 := bstep (se 1 (by rfl) ⟨4231571, by rfl⟩ : syracuseStep 5642095 = 8463143) B8463143
theorem B989903 : Blo 988596 989903 := bstep (se 1 (by rfl) ⟨742427, by rfl⟩ : syracuseStep 989903 = 1484855) B1484855
theorem B989951 : Blo 988596 989951 := bstep (se 1 (by rfl) ⟨742463, by rfl⟩ : syracuseStep 989951 = 1484927) B1484927
theorem B29006591 : Blo 988596 29006591 := bstep (se 1 (by rfl) ⟨21754943, by rfl⟩ : syracuseStep 29006591 = 43509887) B43509887
theorem B990975 : Blo 988596 990975 := bstep (se 1 (by rfl) ⟨743231, by rfl⟩ : syracuseStep 990975 = 1486463) B1486463
theorem B4235111 : Blo 988596 4235111 := bstep (se 1 (by rfl) ⟨3176333, by rfl⟩ : syracuseStep 4235111 = 6352667) B6352667
theorem B1483049 : Blo 988596 1483049 := bstep (se 2 (by rfl) ⟨556143, by rfl⟩ : syracuseStep 1483049 = 1112287) B1112287
theorem B1483247 : Blo 988596 1483247 := bstep (se 1 (by rfl) ⟨1112435, by rfl⟩ : syracuseStep 1483247 = 2224871) B2224871
theorem B1254143 : Blo 988596 1254143 := bstep (se 1 (by rfl) ⟨940607, by rfl⟩ : syracuseStep 1254143 = 1881215) B1881215
theorem B992063 : Blo 988596 992063 := bstep (se 1 (by rfl) ⟨744047, by rfl⟩ : syracuseStep 992063 = 1488095) B1488095
theorem B992575 : Blo 988596 992575 := bstep (se 1 (by rfl) ⟨744431, by rfl⟩ : syracuseStep 992575 = 1488863) B1488863
theorem B4237211 : Blo 988596 4237211 := bstep (se 1 (by rfl) ⟨3177908, by rfl⟩ : syracuseStep 4237211 = 6355817) B6355817
theorem B1256143 : Blo 988596 1256143 := bstep (se 1 (by rfl) ⟨942107, by rfl⟩ : syracuseStep 1256143 = 1884215) B1884215
theorem B1584379 : Blo 988596 1584379 := bstep (se 1 (by rfl) ⟨1188284, by rfl⟩ : syracuseStep 1584379 = 2376569) B2376569
theorem B7515503 : Blo 988596 7515503 := bstep (se 1 (by rfl) ⟨5636627, by rfl⟩ : syracuseStep 7515503 = 11273255) B11273255
theorem B1486847 : Blo 988596 1486847 := bstep (se 1 (by rfl) ⟨1115135, by rfl⟩ : syracuseStep 1486847 = 2230271) B2230271
theorem B2111771 : Blo 988596 2111771 := bstep (se 1 (by rfl) ⟨1583828, by rfl⟩ : syracuseStep 2111771 = 3167657) B3167657
theorem B1882855 : Blo 988596 1882855 := bstep (se 1 (by rfl) ⟨1412141, by rfl⟩ : syracuseStep 1882855 = 2824283) B2824283
theorem B2506747 : Blo 988596 2506747 := bstep (se 1 (by rfl) ⟨1880060, by rfl⟩ : syracuseStep 2506747 = 3760121) B3760121
theorem B5357663 : Blo 988596 5357663 := bstep (se 1 (by rfl) ⟨4018247, by rfl⟩ : syracuseStep 5357663 = 8036495) B8036495
theorem B14500205 : Blo 988596 14500205 := bstep (se 3 (by rfl) ⟨2718788, by rfl⟩ : syracuseStep 14500205 = 5437577) B5437577
theorem B14303699 : Blo 988596 14303699 := bstep (se 1 (by rfl) ⟨10727774, by rfl⟩ : syracuseStep 14303699 = 21455549) B21455549
theorem B58574303 : Blo 988596 58574303 := bstep (se 1 (by rfl) ⟨43930727, by rfl⟩ : syracuseStep 58574303 = 87861455) B87861455
theorem B14305085 : Blo 988596 14305085 := bstep (se 3 (by rfl) ⟨2682203, by rfl⟩ : syracuseStep 14305085 = 5364407) B5364407
theorem B452384957 : Blo 988596 452384957 := bstep (se 3 (by rfl) ⟨84822179, by rfl⟩ : syracuseStep 452384957 = 169644359) B169644359
theorem B12672935 : Blo 988596 12672935 := bstep (se 1 (by rfl) ⟨9504701, by rfl⟩ : syracuseStep 12672935 = 19009403) B19009403
theorem B130245569 : Blo 988596 130245569 := bstep (se 2 (by rfl) ⟨48842088, by rfl⟩ : syracuseStep 130245569 = 97684177) B97684177
theorem B3762247 : Blo 988596 3762247 := bstep (se 1 (by rfl) ⟨2821685, by rfl⟩ : syracuseStep 3762247 = 5643371) B5643371
theorem B16083359 : Blo 988596 16083359 := bstep (se 1 (by rfl) ⟨12062519, by rfl⟩ : syracuseStep 16083359 = 24125039) B24125039
theorem B3764663 : Blo 988596 3764663 := bstep (se 1 (by rfl) ⟨2823497, by rfl⟩ : syracuseStep 3764663 = 5646995) B5646995
theorem B7532999 : Blo 988596 7532999 := bstep (se 1 (by rfl) ⟨5649749, by rfl⟩ : syracuseStep 7532999 = 11299499) B11299499
theorem B3175679 : Blo 988596 3175679 := bstep (se 1 (by rfl) ⟨2381759, by rfl⟩ : syracuseStep 3175679 = 4763519) B4763519
theorem B1669801 : Blo 988596 1669801 := bstep (se 2 (by rfl) ⟨626175, by rfl⟩ : syracuseStep 1669801 = 1252351) B1252351
theorem B3571775 : Blo 988596 3571775 := bstep (se 1 (by rfl) ⟨2678831, by rfl⟩ : syracuseStep 3571775 = 5357663) B5357663
theorem B9666803 : Blo 988596 9666803 := bstep (se 1 (by rfl) ⟨7250102, by rfl⟩ : syracuseStep 9666803 = 14500205) B14500205
theorem B9535799 : Blo 988596 9535799 := bstep (se 1 (by rfl) ⟨7151849, by rfl⟩ : syracuseStep 9535799 = 14303699) B14303699
theorem B2818975 : Blo 988596 2818975 := bstep (se 1 (by rfl) ⟨2114231, by rfl⟩ : syracuseStep 2818975 = 4228463) B4228463
theorem B9536723 : Blo 988596 9536723 := bstep (se 1 (by rfl) ⟨7152542, by rfl⟩ : syracuseStep 9536723 = 14305085) B14305085
theorem B3344381 : Blo 988596 3344381 := bstep (se 3 (by rfl) ⟨627071, by rfl⟩ : syracuseStep 3344381 = 1254143) B1254143
theorem B5638247 : Blo 988596 5638247 := bstep (se 1 (by rfl) ⟨4228685, by rfl⟩ : syracuseStep 5638247 = 8457371) B8457371
theorem B5016329 : Blo 988596 5016329 := bstep (se 2 (by rfl) ⟨1881123, by rfl⟩ : syracuseStep 5016329 = 3762247) B3762247
theorem B1674857 : Blo 988596 1674857 := bstep (se 2 (by rfl) ⟨628071, by rfl⟩ : syracuseStep 1674857 = 1256143) B1256143
theorem B2823407 : Blo 988596 2823407 := bstep (se 1 (by rfl) ⟨2117555, by rfl⟩ : syracuseStep 2823407 = 4235111) B4235111
theorem B988699 : Blo 988596 988699 := bstep (se 1 (by rfl) ⟨741524, by rfl⟩ : syracuseStep 988699 = 1483049) B1483049
theorem B988831 : Blo 988596 988831 := bstep (se 1 (by rfl) ⟨741623, by rfl⟩ : syracuseStep 988831 = 1483247) B1483247
theorem B1206359885 : Blo 988596 1206359885 := bstep (se 3 (by rfl) ⟨226192478, by rfl⟩ : syracuseStep 1206359885 = 452384957) B452384957
theorem B2824807 : Blo 988596 2824807 := bstep (se 1 (by rfl) ⟨2118605, by rfl⟩ : syracuseStep 2824807 = 4237211) B4237211
theorem B10722239 : Blo 988596 10722239 := bstep (se 1 (by rfl) ⟨8041679, by rfl⟩ : syracuseStep 10722239 = 16083359) B16083359
theorem B991231 : Blo 988596 991231 := bstep (se 1 (by rfl) ⟨743423, by rfl⟩ : syracuseStep 991231 = 1486847) B1486847
theorem B5021999 : Blo 988596 5021999 := bstep (se 1 (by rfl) ⟨3766499, by rfl⟩ : syracuseStep 5021999 = 7532999) B7532999
theorem B7515017 : Blo 988596 7515017 := bstep (se 2 (by rfl) ⟨2818131, by rfl⟩ : syracuseStep 7515017 = 5636263) B5636263
theorem B77350909 : Blo 988596 77350909 := bstep (se 3 (by rfl) ⟨14503295, by rfl⟩ : syracuseStep 77350909 = 29006591) B29006591
theorem B7522793 : Blo 988596 7522793 := bstep (se 2 (by rfl) ⟨2821047, by rfl⟩ : syracuseStep 7522793 = 5642095) B5642095
theorem B2509775 : Blo 988596 2509775 := bstep (se 1 (by rfl) ⟨1882331, by rfl⟩ : syracuseStep 2509775 = 3764663) B3764663
theorem B2117119 : Blo 988596 2117119 := bstep (se 1 (by rfl) ⟨1587839, by rfl⟩ : syracuseStep 2117119 = 3175679) B3175679
theorem B2510473 : Blo 988596 2510473 := bstep (se 2 (by rfl) ⟨941427, by rfl⟩ : syracuseStep 2510473 = 1882855) B1882855
theorem B39049535 : Blo 988596 39049535 := bstep (se 1 (by rfl) ⟨29287151, by rfl⟩ : syracuseStep 39049535 = 58574303) B58574303
theorem B2710057 : Blo 988596 2710057 := bstep (se 2 (by rfl) ⟨1016271, by rfl⟩ : syracuseStep 2710057 = 2032543) B2032543
theorem B8448623 : Blo 988596 8448623 := bstep (se 1 (by rfl) ⟨6336467, by rfl⟩ : syracuseStep 8448623 = 12672935) B12672935
theorem B86830379 : Blo 988596 86830379 := bstep (se 1 (by rfl) ⟨65122784, by rfl⟩ : syracuseStep 86830379 = 130245569) B130245569
theorem B5631389 : Blo 988596 5631389 := bstep (se 3 (by rfl) ⟨1055885, by rfl⟩ : syracuseStep 5631389 = 2111771) B2111771
theorem B8450021 : Blo 988596 8450021 := bstep (se 4 (by rfl) ⟨792189, by rfl⟩ : syracuseStep 8450021 = 1584379) B1584379
theorem B5010335 : Blo 988596 5010335 := bstep (se 1 (by rfl) ⟨3757751, by rfl⟩ : syracuseStep 5010335 = 7515503) B7515503
theorem B2226401 : Blo 988596 2226401 := bstep (se 2 (by rfl) ⟨834900, by rfl⟩ : syracuseStep 2226401 = 1669801) B1669801
theorem B3342329 : Blo 988596 3342329 := bstep (se 2 (by rfl) ⟨1253373, by rfl⟩ : syracuseStep 3342329 = 2506747) B2506747
theorem B6357199 : Blo 988596 6357199 := bstep (se 1 (by rfl) ⟨4767899, by rfl⟩ : syracuseStep 6357199 = 9535799) B9535799
theorem B6357815 : Blo 988596 6357815 := bstep (se 1 (by rfl) ⟨4768361, by rfl⟩ : syracuseStep 6357815 = 9536723) B9536723
theorem B2229587 : Blo 988596 2229587 := bstep (se 1 (by rfl) ⟨1672190, by rfl⟩ : syracuseStep 2229587 = 3344381) B3344381
theorem B5015195 : Blo 988596 5015195 := bstep (se 1 (by rfl) ⟨3761396, by rfl⟩ : syracuseStep 5015195 = 7522793) B7522793
theorem B3344219 : Blo 988596 3344219 := bstep (se 1 (by rfl) ⟨2508164, by rfl⟩ : syracuseStep 3344219 = 5016329) B5016329
theorem B1673183 : Blo 988596 1673183 := bstep (se 1 (by rfl) ⟨1254887, by rfl⟩ : syracuseStep 1673183 = 2509775) B2509775
theorem B1116571 : Blo 988596 1116571 := bstep (se 1 (by rfl) ⟨837428, by rfl⟩ : syracuseStep 1116571 = 1674857) B1674857
theorem B7148159 : Blo 988596 7148159 := bstep (se 1 (by rfl) ⟨5361119, by rfl⟩ : syracuseStep 7148159 = 10722239) B10722239
theorem B2822825 : Blo 988596 2822825 := bstep (se 2 (by rfl) ⟨1058559, by rfl⟩ : syracuseStep 2822825 = 2117119) B2117119
theorem B3347297 : Blo 988596 3347297 := bstep (se 2 (by rfl) ⟨1255236, by rfl⟩ : syracuseStep 3347297 = 2510473) B2510473
theorem B3347999 : Blo 988596 3347999 := bstep (se 1 (by rfl) ⟨2510999, by rfl⟩ : syracuseStep 3347999 = 5021999) B5021999
theorem B3613409 : Blo 988596 3613409 := bstep (se 2 (by rfl) ⟨1355028, by rfl⟩ : syracuseStep 3613409 = 2710057) B2710057
theorem B1484267 : Blo 988596 1484267 := bstep (se 1 (by rfl) ⟨1113200, by rfl⟩ : syracuseStep 1484267 = 2226401) B2226401
theorem B103134545 : Blo 988596 103134545 := bstep (se 2 (by rfl) ⟨38675454, by rfl⟩ : syracuseStep 103134545 = 77350909) B77350909
theorem B1882271 : Blo 988596 1882271 := bstep (se 1 (by rfl) ⟨1411703, by rfl⟩ : syracuseStep 1882271 = 2823407) B2823407
theorem B804239923 : Blo 988596 804239923 := bstep (se 1 (by rfl) ⟨603179942, by rfl⟩ : syracuseStep 804239923 = 1206359885) B1206359885
theorem B26033023 : Blo 988596 26033023 := bstep (se 1 (by rfl) ⟨19524767, by rfl⟩ : syracuseStep 26033023 = 39049535) B39049535
theorem B57886919 : Blo 988596 57886919 := bstep (se 1 (by rfl) ⟨43415189, by rfl⟩ : syracuseStep 57886919 = 86830379) B86830379
theorem B3754259 : Blo 988596 3754259 := bstep (se 1 (by rfl) ⟨2815694, by rfl⟩ : syracuseStep 3754259 = 5631389) B5631389
theorem B2381183 : Blo 988596 2381183 := bstep (se 1 (by rfl) ⟨1785887, by rfl⟩ : syracuseStep 2381183 = 3571775) B3571775
theorem B6444535 : Blo 988596 6444535 := bstep (se 1 (by rfl) ⟨4833401, by rfl⟩ : syracuseStep 6444535 = 9666803) B9666803
theorem B3758633 : Blo 988596 3758633 := bstep (se 2 (by rfl) ⟨1409487, by rfl⟩ : syracuseStep 3758633 = 2818975) B2818975
theorem B3758831 : Blo 988596 3758831 := bstep (se 1 (by rfl) ⟨2819123, by rfl⟩ : syracuseStep 3758831 = 5638247) B5638247
theorem B5632415 : Blo 988596 5632415 := bstep (se 1 (by rfl) ⟨4224311, by rfl⟩ : syracuseStep 5632415 = 8448623) B8448623
theorem B5010011 : Blo 988596 5010011 := bstep (se 1 (by rfl) ⟨3757508, by rfl⟩ : syracuseStep 5010011 = 7515017) B7515017
theorem B5633347 : Blo 988596 5633347 := bstep (se 1 (by rfl) ⟨4225010, by rfl⟩ : syracuseStep 5633347 = 8450021) B8450021
theorem B3340223 : Blo 988596 3340223 := bstep (se 1 (by rfl) ⟨2505167, by rfl⟩ : syracuseStep 3340223 = 5010335) B5010335
theorem B3766409 : Blo 988596 3766409 := bstep (se 2 (by rfl) ⟨1412403, by rfl⟩ : syracuseStep 3766409 = 2824807) B2824807
theorem B2228219 : Blo 988596 2228219 := bstep (se 1 (by rfl) ⟨1671164, by rfl⟩ : syracuseStep 2228219 = 3342329) B3342329
theorem B3343463 : Blo 988596 3343463 := bstep (se 1 (by rfl) ⟨2507597, by rfl⟩ : syracuseStep 3343463 = 5015195) B5015195
theorem B2229479 : Blo 988596 2229479 := bstep (se 1 (by rfl) ⟨1672109, by rfl⟩ : syracuseStep 2229479 = 3344219) B3344219
theorem B1115455 : Blo 988596 1115455 := bstep (se 1 (by rfl) ⟨836591, by rfl⟩ : syracuseStep 1115455 = 1673183) B1673183
theorem B2231531 : Blo 988596 2231531 := bstep (se 1 (by rfl) ⟨1673648, by rfl⟩ : syracuseStep 2231531 = 3347297) B3347297
theorem B2231999 : Blo 988596 2231999 := bstep (se 1 (by rfl) ⟨1673999, by rfl⟩ : syracuseStep 2231999 = 3347999) B3347999
theorem B989511 : Blo 988596 989511 := bstep (se 1 (by rfl) ⟨742133, by rfl⟩ : syracuseStep 989511 = 1484267) B1484267
theorem B7511129 : Blo 988596 7511129 := bstep (se 2 (by rfl) ⟨2816673, by rfl⟩ : syracuseStep 7511129 = 5633347) B5633347
theorem B8592713 : Blo 988596 8592713 := bstep (se 2 (by rfl) ⟨3222267, by rfl⟩ : syracuseStep 8592713 = 6444535) B6444535
theorem B68756363 : Blo 988596 68756363 := bstep (se 1 (by rfl) ⟨51567272, by rfl⟩ : syracuseStep 68756363 = 103134545) B103134545
theorem B34710697 : Blo 988596 34710697 := bstep (se 2 (by rfl) ⟨13016511, by rfl⟩ : syracuseStep 34710697 = 26033023) B26033023
theorem B1254847 : Blo 988596 1254847 := bstep (se 1 (by rfl) ⟨941135, by rfl⟩ : syracuseStep 1254847 = 1882271) B1882271
theorem B1485479 : Blo 988596 1485479 := bstep (se 1 (by rfl) ⟨1114109, by rfl⟩ : syracuseStep 1485479 = 2228219) B2228219
theorem B4238543 : Blo 988596 4238543 := bstep (se 1 (by rfl) ⟨3178907, by rfl⟩ : syracuseStep 4238543 = 6357815) B6357815
theorem B1486391 : Blo 988596 1486391 := bstep (se 1 (by rfl) ⟨1114793, by rfl⟩ : syracuseStep 1486391 = 2229587) B2229587
theorem B2502839 : Blo 988596 2502839 := bstep (se 1 (by rfl) ⟨1877129, by rfl⟩ : syracuseStep 2502839 = 3754259) B3754259
theorem B4765439 : Blo 988596 4765439 := bstep (se 1 (by rfl) ⟨3574079, by rfl⟩ : syracuseStep 4765439 = 7148159) B7148159
theorem B1881883 : Blo 988596 1881883 := bstep (se 1 (by rfl) ⟨1411412, by rfl⟩ : syracuseStep 1881883 = 2822825) B2822825
theorem B1488761 : Blo 988596 1488761 := bstep (se 2 (by rfl) ⟨558285, by rfl⟩ : syracuseStep 1488761 = 1116571) B1116571
theorem B1587455 : Blo 988596 1587455 := bstep (se 1 (by rfl) ⟨1190591, by rfl⟩ : syracuseStep 1587455 = 2381183) B2381183
theorem B2505755 : Blo 988596 2505755 := bstep (se 1 (by rfl) ⟨1879316, by rfl⟩ : syracuseStep 2505755 = 3758633) B3758633
theorem B2505887 : Blo 988596 2505887 := bstep (se 1 (by rfl) ⟨1879415, by rfl⟩ : syracuseStep 2505887 = 3758831) B3758831
theorem B2408939 : Blo 988596 2408939 := bstep (se 1 (by rfl) ⟨1806704, by rfl⟩ : syracuseStep 2408939 = 3613409) B3613409
theorem B3754943 : Blo 988596 3754943 := bstep (se 1 (by rfl) ⟨2816207, by rfl⟩ : syracuseStep 3754943 = 5632415) B5632415
theorem B1072319897 : Blo 988596 1072319897 := bstep (se 2 (by rfl) ⟨402119961, by rfl⟩ : syracuseStep 1072319897 = 804239923) B804239923
theorem B2510939 : Blo 988596 2510939 := bstep (se 1 (by rfl) ⟨1883204, by rfl⟩ : syracuseStep 2510939 = 3766409) B3766409
theorem B8476265 : Blo 988596 8476265 := bstep (se 2 (by rfl) ⟨3178599, by rfl⟩ : syracuseStep 8476265 = 6357199) B6357199
theorem B38591279 : Blo 988596 38591279 := bstep (se 1 (by rfl) ⟨28943459, by rfl⟩ : syracuseStep 38591279 = 57886919) B57886919
theorem B3340007 : Blo 988596 3340007 := bstep (se 1 (by rfl) ⟨2505005, by rfl⟩ : syracuseStep 3340007 = 5010011) B5010011
theorem B2226815 : Blo 988596 2226815 := bstep (se 1 (by rfl) ⟨1670111, by rfl⟩ : syracuseStep 2226815 = 3340223) B3340223
theorem B1605959 : Blo 988596 1605959 := bstep (se 1 (by rfl) ⟨1204469, by rfl⟩ : syracuseStep 1605959 = 2408939) B2408939
theorem B2228975 : Blo 988596 2228975 := bstep (se 1 (by rfl) ⟨1671731, by rfl⟩ : syracuseStep 2228975 = 3343463) B3343463
theorem B1673129 : Blo 988596 1673129 := bstep (se 2 (by rfl) ⟨627423, by rfl⟩ : syracuseStep 1673129 = 1254847) B1254847
theorem B1673959 : Blo 988596 1673959 := bstep (se 1 (by rfl) ⟨1255469, by rfl⟩ : syracuseStep 1673959 = 2510939) B2510939
theorem B25727519 : Blo 988596 25727519 := bstep (se 1 (by rfl) ⟨19295639, by rfl⟩ : syracuseStep 25727519 = 38591279) B38591279
theorem B990319 : Blo 988596 990319 := bstep (se 1 (by rfl) ⟨742739, by rfl⟩ : syracuseStep 990319 = 1485479) B1485479
theorem B2825695 : Blo 988596 2825695 := bstep (se 1 (by rfl) ⟨2119271, by rfl⟩ : syracuseStep 2825695 = 4238543) B4238543
theorem B990927 : Blo 988596 990927 := bstep (se 1 (by rfl) ⟨743195, by rfl⟩ : syracuseStep 990927 = 1486391) B1486391
theorem B992507 : Blo 988596 992507 := bstep (se 1 (by rfl) ⟨744380, by rfl⟩ : syracuseStep 992507 = 1488761) B1488761
theorem B1058303 : Blo 988596 1058303 := bstep (se 1 (by rfl) ⟨793727, by rfl⟩ : syracuseStep 1058303 = 1587455) B1587455
theorem B1484543 : Blo 988596 1484543 := bstep (se 1 (by rfl) ⟨1113407, by rfl⟩ : syracuseStep 1484543 = 2226815) B2226815
theorem B1486319 : Blo 988596 1486319 := bstep (se 1 (by rfl) ⟨1114739, by rfl⟩ : syracuseStep 1486319 = 2229479) B2229479
theorem B46280929 : Blo 988596 46280929 := bstep (se 2 (by rfl) ⟨17355348, by rfl⟩ : syracuseStep 46280929 = 34710697) B34710697
theorem B1487273 : Blo 988596 1487273 := bstep (se 2 (by rfl) ⟨557727, by rfl⟩ : syracuseStep 1487273 = 1115455) B1115455
theorem B2503295 : Blo 988596 2503295 := bstep (se 1 (by rfl) ⟨1877471, by rfl⟩ : syracuseStep 2503295 = 3754943) B3754943
theorem B1487687 : Blo 988596 1487687 := bstep (se 1 (by rfl) ⟨1115765, by rfl⟩ : syracuseStep 1487687 = 2231531) B2231531
theorem B714879931 : Blo 988596 714879931 := bstep (se 1 (by rfl) ⟨536159948, by rfl⟩ : syracuseStep 714879931 = 1072319897) B1072319897
theorem B1487999 : Blo 988596 1487999 := bstep (se 1 (by rfl) ⟨1115999, by rfl⟩ : syracuseStep 1487999 = 2231999) B2231999
theorem B5650843 : Blo 988596 5650843 := bstep (se 1 (by rfl) ⟨4238132, by rfl⟩ : syracuseStep 5650843 = 8476265) B8476265
theorem B2509177 : Blo 988596 2509177 := bstep (se 2 (by rfl) ⟨940941, by rfl⟩ : syracuseStep 2509177 = 1881883) B1881883
theorem B12707837 : Blo 988596 12707837 := bstep (se 3 (by rfl) ⟨2382719, by rfl⟩ : syracuseStep 12707837 = 4765439) B4765439
theorem B5007419 : Blo 988596 5007419 := bstep (se 1 (by rfl) ⟨3755564, by rfl⟩ : syracuseStep 5007419 = 7511129) B7511129
theorem B5728475 : Blo 988596 5728475 := bstep (se 1 (by rfl) ⟨4296356, by rfl⟩ : syracuseStep 5728475 = 8592713) B8592713
theorem B45837575 : Blo 988596 45837575 := bstep (se 1 (by rfl) ⟨34378181, by rfl⟩ : syracuseStep 45837575 = 68756363) B68756363
theorem B1668559 : Blo 988596 1668559 := bstep (se 1 (by rfl) ⟨1251419, by rfl⟩ : syracuseStep 1668559 = 2502839) B2502839
theorem B2226671 : Blo 988596 2226671 := bstep (se 1 (by rfl) ⟨1670003, by rfl⟩ : syracuseStep 2226671 = 3340007) B3340007
theorem B1670503 : Blo 988596 1670503 := bstep (se 1 (by rfl) ⟨1252877, by rfl⟩ : syracuseStep 1670503 = 2505755) B2505755
theorem B1670591 : Blo 988596 1670591 := bstep (se 1 (by rfl) ⟨1252943, by rfl⟩ : syracuseStep 1670591 = 2505887) B2505887
theorem B1115419 : Blo 988596 1115419 := bstep (se 1 (by rfl) ⟨836564, by rfl⟩ : syracuseStep 1115419 = 1673129) B1673129
theorem B3345569 : Blo 988596 3345569 := bstep (se 2 (by rfl) ⟨1254588, by rfl⟩ : syracuseStep 3345569 = 2509177) B2509177
theorem B2231945 : Blo 988596 2231945 := bstep (se 2 (by rfl) ⟨836979, by rfl⟩ : syracuseStep 2231945 = 1673959) B1673959
theorem B2822141 : Blo 988596 2822141 := bstep (se 3 (by rfl) ⟨529151, by rfl⟩ : syracuseStep 2822141 = 1058303) B1058303
theorem B61707905 : Blo 988596 61707905 := bstep (se 2 (by rfl) ⟨23140464, by rfl⟩ : syracuseStep 61707905 = 46280929) B46280929
theorem B989695 : Blo 988596 989695 := bstep (se 1 (by rfl) ⟨742271, by rfl⟩ : syracuseStep 989695 = 1484543) B1484543
theorem B990879 : Blo 988596 990879 := bstep (se 1 (by rfl) ⟨743159, by rfl⟩ : syracuseStep 990879 = 1486319) B1486319
theorem B991515 : Blo 988596 991515 := bstep (se 1 (by rfl) ⟨743636, by rfl⟩ : syracuseStep 991515 = 1487273) B1487273
theorem B991791 : Blo 988596 991791 := bstep (se 1 (by rfl) ⟨743843, by rfl⟩ : syracuseStep 991791 = 1487687) B1487687
theorem B991999 : Blo 988596 991999 := bstep (se 1 (by rfl) ⟨743999, by rfl⟩ : syracuseStep 991999 = 1487999) B1487999
theorem B1484447 : Blo 988596 1484447 := bstep (se 1 (by rfl) ⟨1113335, by rfl⟩ : syracuseStep 1484447 = 2226671) B2226671
theorem B1485983 : Blo 988596 1485983 := bstep (se 1 (by rfl) ⟨1114487, by rfl⟩ : syracuseStep 1485983 = 2228975) B2228975
theorem B17151679 : Blo 988596 17151679 := bstep (se 1 (by rfl) ⟨12863759, by rfl⟩ : syracuseStep 17151679 = 25727519) B25727519
theorem B953173241 : Blo 988596 953173241 := bstep (se 2 (by rfl) ⟨357439965, by rfl⟩ : syracuseStep 953173241 = 714879931) B714879931
theorem B8471891 : Blo 988596 8471891 := bstep (se 1 (by rfl) ⟨6353918, by rfl⟩ : syracuseStep 8471891 = 12707837) B12707837
theorem B3818983 : Blo 988596 3818983 := bstep (se 1 (by rfl) ⟨2864237, by rfl⟩ : syracuseStep 3818983 = 5728475) B5728475
theorem B30558383 : Blo 988596 30558383 := bstep (se 1 (by rfl) ⟨22918787, by rfl⟩ : syracuseStep 30558383 = 45837575) B45837575
theorem B1070639 : Blo 988596 1070639 := bstep (se 1 (by rfl) ⟨802979, by rfl⟩ : syracuseStep 1070639 = 1605959) B1605959
theorem B3338279 : Blo 988596 3338279 := bstep (se 1 (by rfl) ⟨2503709, by rfl⟩ : syracuseStep 3338279 = 5007419) B5007419
theorem B2224745 : Blo 988596 2224745 := bstep (se 2 (by rfl) ⟨834279, by rfl⟩ : syracuseStep 2224745 = 1668559) B1668559
theorem B1668863 : Blo 988596 1668863 := bstep (se 1 (by rfl) ⟨1251647, by rfl⟩ : syracuseStep 1668863 = 2503295) B2503295
theorem B7534457 : Blo 988596 7534457 := bstep (se 2 (by rfl) ⟨2825421, by rfl⟩ : syracuseStep 7534457 = 5650843) B5650843
theorem B2227337 : Blo 988596 2227337 := bstep (se 2 (by rfl) ⟨835251, by rfl⟩ : syracuseStep 2227337 = 1670503) B1670503
theorem B3767593 : Blo 988596 3767593 := bstep (se 2 (by rfl) ⟨1412847, by rfl⟩ : syracuseStep 3767593 = 2825695) B2825695
theorem B1113727 : Blo 988596 1113727 := bstep (se 1 (by rfl) ⟨835295, by rfl⟩ : syracuseStep 1113727 = 1670591) B1670591
theorem B2230379 : Blo 988596 2230379 := bstep (se 1 (by rfl) ⟨1672784, by rfl⟩ : syracuseStep 2230379 = 3345569) B3345569
theorem B989631 : Blo 988596 989631 := bstep (se 1 (by rfl) ⟨742223, by rfl⟩ : syracuseStep 989631 = 1484447) B1484447
theorem B990655 : Blo 988596 990655 := bstep (se 1 (by rfl) ⟨742991, by rfl⟩ : syracuseStep 990655 = 1485983) B1485983
theorem B1483163 : Blo 988596 1483163 := bstep (se 1 (by rfl) ⟨1112372, by rfl⟩ : syracuseStep 1483163 = 2224745) B2224745
theorem B5022971 : Blo 988596 5022971 := bstep (se 1 (by rfl) ⟨3767228, by rfl⟩ : syracuseStep 5022971 = 7534457) B7534457
theorem B5023457 : Blo 988596 5023457 := bstep (se 2 (by rfl) ⟨1883796, by rfl⟩ : syracuseStep 5023457 = 3767593) B3767593
theorem B1484891 : Blo 988596 1484891 := bstep (se 1 (by rfl) ⟨1113668, by rfl⟩ : syracuseStep 1484891 = 2227337) B2227337
theorem B1484969 : Blo 988596 1484969 := bstep (se 2 (by rfl) ⟨556863, by rfl⟩ : syracuseStep 1484969 = 1113727) B1113727
theorem B635448827 : Blo 988596 635448827 := bstep (se 1 (by rfl) ⟨476586620, by rfl⟩ : syracuseStep 635448827 = 953173241) B953173241
theorem B5647927 : Blo 988596 5647927 := bstep (se 1 (by rfl) ⟨4235945, by rfl⟩ : syracuseStep 5647927 = 8471891) B8471891
theorem B1487225 : Blo 988596 1487225 := bstep (se 2 (by rfl) ⟨557709, by rfl⟩ : syracuseStep 1487225 = 1115419) B1115419
theorem B5091977 : Blo 988596 5091977 := bstep (se 2 (by rfl) ⟨1909491, by rfl⟩ : syracuseStep 5091977 = 3818983) B3818983
theorem B1487963 : Blo 988596 1487963 := bstep (se 1 (by rfl) ⟨1115972, by rfl⟩ : syracuseStep 1487963 = 2231945) B2231945
theorem B41138603 : Blo 988596 41138603 := bstep (se 1 (by rfl) ⟨30853952, by rfl⟩ : syracuseStep 41138603 = 61707905) B61707905
theorem B11420149 : Blo 988596 11420149 := bstep (se 5 (by rfl) ⟨535319, by rfl⟩ : syracuseStep 11420149 = 1070639) B1070639
theorem B7525709 : Blo 988596 7525709 := bstep (se 3 (by rfl) ⟨1411070, by rfl⟩ : syracuseStep 7525709 = 2822141) B2822141
theorem B20372255 : Blo 988596 20372255 := bstep (se 1 (by rfl) ⟨15279191, by rfl⟩ : syracuseStep 20372255 = 30558383) B30558383
theorem B22868905 : Blo 988596 22868905 := bstep (se 2 (by rfl) ⟨8575839, by rfl⟩ : syracuseStep 22868905 = 17151679) B17151679
theorem B2225519 : Blo 988596 2225519 := bstep (se 1 (by rfl) ⟨1669139, by rfl⟩ : syracuseStep 2225519 = 3338279) B3338279
theorem B1112575 : Blo 988596 1112575 := bstep (se 1 (by rfl) ⟨834431, by rfl⟩ : syracuseStep 1112575 = 1668863) B1668863
theorem B5017139 : Blo 988596 5017139 := bstep (se 1 (by rfl) ⟨3762854, by rfl⟩ : syracuseStep 5017139 = 7525709) B7525709
theorem B988775 : Blo 988596 988775 := bstep (se 1 (by rfl) ⟨741581, by rfl⟩ : syracuseStep 988775 = 1483163) B1483163
theorem B3348647 : Blo 988596 3348647 := bstep (se 1 (by rfl) ⟨2511485, by rfl⟩ : syracuseStep 3348647 = 5022971) B5022971
theorem B3348971 : Blo 988596 3348971 := bstep (se 1 (by rfl) ⟨2511728, by rfl⟩ : syracuseStep 3348971 = 5023457) B5023457
theorem B989927 : Blo 988596 989927 := bstep (se 1 (by rfl) ⟨742445, by rfl⟩ : syracuseStep 989927 = 1484891) B1484891
theorem B989979 : Blo 988596 989979 := bstep (se 1 (by rfl) ⟨742484, by rfl⟩ : syracuseStep 989979 = 1484969) B1484969
theorem B423632551 : Blo 988596 423632551 := bstep (se 1 (by rfl) ⟨317724413, by rfl⟩ : syracuseStep 423632551 = 635448827) B635448827
theorem B991483 : Blo 988596 991483 := bstep (se 1 (by rfl) ⟨743612, by rfl⟩ : syracuseStep 991483 = 1487225) B1487225
theorem B1483433 : Blo 988596 1483433 := bstep (se 2 (by rfl) ⟨556287, by rfl⟩ : syracuseStep 1483433 = 1112575) B1112575
theorem B991975 : Blo 988596 991975 := bstep (se 1 (by rfl) ⟨743981, by rfl⟩ : syracuseStep 991975 = 1487963) B1487963
theorem B1483679 : Blo 988596 1483679 := bstep (se 1 (by rfl) ⟨1112759, by rfl⟩ : syracuseStep 1483679 = 2225519) B2225519
theorem B1486919 : Blo 988596 1486919 := bstep (se 1 (by rfl) ⟨1115189, by rfl⟩ : syracuseStep 1486919 = 2230379) B2230379
theorem B13578605 : Blo 988596 13578605 := bstep (se 3 (by rfl) ⟨2545988, by rfl⟩ : syracuseStep 13578605 = 5091977) B5091977
theorem B13581503 : Blo 988596 13581503 := bstep (se 1 (by rfl) ⟨10186127, by rfl⟩ : syracuseStep 13581503 = 20372255) B20372255
theorem B30491873 : Blo 988596 30491873 := bstep (se 2 (by rfl) ⟨11434452, by rfl⟩ : syracuseStep 30491873 = 22868905) B22868905
theorem B15226865 : Blo 988596 15226865 := bstep (se 2 (by rfl) ⟨5710074, by rfl⟩ : syracuseStep 15226865 = 11420149) B11420149
theorem B7530569 : Blo 988596 7530569 := bstep (se 2 (by rfl) ⟨2823963, by rfl⟩ : syracuseStep 7530569 = 5647927) B5647927
theorem B27425735 : Blo 988596 27425735 := bstep (se 1 (by rfl) ⟨20569301, by rfl⟩ : syracuseStep 27425735 = 41138603) B41138603
theorem B3344759 : Blo 988596 3344759 := bstep (se 1 (by rfl) ⟨2508569, by rfl⟩ : syracuseStep 3344759 = 5017139) B5017139
theorem B2232431 : Blo 988596 2232431 := bstep (se 1 (by rfl) ⟨1674323, by rfl⟩ : syracuseStep 2232431 = 3348647) B3348647
theorem B2232647 : Blo 988596 2232647 := bstep (se 1 (by rfl) ⟨1674485, by rfl⟩ : syracuseStep 2232647 = 3348971) B3348971
theorem B988955 : Blo 988596 988955 := bstep (se 1 (by rfl) ⟨741716, by rfl⟩ : syracuseStep 988955 = 1483433) B1483433
theorem B989119 : Blo 988596 989119 := bstep (se 1 (by rfl) ⟨741839, by rfl⟩ : syracuseStep 989119 = 1483679) B1483679
theorem B5020379 : Blo 988596 5020379 := bstep (se 1 (by rfl) ⟨3765284, by rfl⟩ : syracuseStep 5020379 = 7530569) B7530569
theorem B991279 : Blo 988596 991279 := bstep (se 1 (by rfl) ⟨743459, by rfl⟩ : syracuseStep 991279 = 1486919) B1486919
theorem B9052403 : Blo 988596 9052403 := bstep (se 1 (by rfl) ⟨6789302, by rfl⟩ : syracuseStep 9052403 = 13578605) B13578605
theorem B9054335 : Blo 988596 9054335 := bstep (se 1 (by rfl) ⟨6790751, by rfl⟩ : syracuseStep 9054335 = 13581503) B13581503
theorem B20327915 : Blo 988596 20327915 := bstep (se 1 (by rfl) ⟨15245936, by rfl⟩ : syracuseStep 20327915 = 30491873) B30491873
theorem B564843401 : Blo 988596 564843401 := bstep (se 2 (by rfl) ⟨211816275, by rfl⟩ : syracuseStep 564843401 = 423632551) B423632551
theorem B10151243 : Blo 988596 10151243 := bstep (se 1 (by rfl) ⟨7613432, by rfl⟩ : syracuseStep 10151243 = 15226865) B15226865
theorem B18283823 : Blo 988596 18283823 := bstep (se 1 (by rfl) ⟨13712867, by rfl⟩ : syracuseStep 18283823 = 27425735) B27425735
theorem B2229839 : Blo 988596 2229839 := bstep (se 1 (by rfl) ⟨1672379, by rfl⟩ : syracuseStep 2229839 = 3344759) B3344759
theorem B3346919 : Blo 988596 3346919 := bstep (se 1 (by rfl) ⟨2510189, by rfl⟩ : syracuseStep 3346919 = 5020379) B5020379
theorem B6036223 : Blo 988596 6036223 := bstep (se 1 (by rfl) ⟨4527167, by rfl⟩ : syracuseStep 6036223 = 9054335) B9054335
theorem B1488287 : Blo 988596 1488287 := bstep (se 1 (by rfl) ⟨1116215, by rfl⟩ : syracuseStep 1488287 = 2232431) B2232431
theorem B1488431 : Blo 988596 1488431 := bstep (se 1 (by rfl) ⟨1116323, by rfl⟩ : syracuseStep 1488431 = 2232647) B2232647
theorem B6767495 : Blo 988596 6767495 := bstep (se 1 (by rfl) ⟨5075621, by rfl⟩ : syracuseStep 6767495 = 10151243) B10151243
theorem B13551943 : Blo 988596 13551943 := bstep (se 1 (by rfl) ⟨10163957, by rfl⟩ : syracuseStep 13551943 = 20327915) B20327915
theorem B24139741 : Blo 988596 24139741 := bstep (se 3 (by rfl) ⟨4526201, by rfl⟩ : syracuseStep 24139741 = 9052403) B9052403
theorem B376562267 : Blo 988596 376562267 := bstep (se 1 (by rfl) ⟨282421700, by rfl⟩ : syracuseStep 376562267 = 564843401) B564843401
theorem B12189215 : Blo 988596 12189215 := bstep (se 1 (by rfl) ⟨9141911, by rfl⟩ : syracuseStep 12189215 = 18283823) B18283823
theorem B2231279 : Blo 988596 2231279 := bstep (se 1 (by rfl) ⟨1673459, by rfl⟩ : syracuseStep 2231279 = 3346919) B3346919
theorem B251041511 : Blo 988596 251041511 := bstep (se 1 (by rfl) ⟨188281133, by rfl⟩ : syracuseStep 251041511 = 376562267) B376562267
theorem B32186321 : Blo 988596 32186321 := bstep (se 2 (by rfl) ⟨12069870, by rfl⟩ : syracuseStep 32186321 = 24139741) B24139741
theorem B992191 : Blo 988596 992191 := bstep (se 1 (by rfl) ⟨744143, by rfl⟩ : syracuseStep 992191 = 1488287) B1488287
theorem B992287 : Blo 988596 992287 := bstep (se 1 (by rfl) ⟨744215, by rfl⟩ : syracuseStep 992287 = 1488431) B1488431
theorem B1486559 : Blo 988596 1486559 := bstep (se 1 (by rfl) ⟨1114919, by rfl⟩ : syracuseStep 1486559 = 2229839) B2229839
theorem B18069257 : Blo 988596 18069257 := bstep (se 2 (by rfl) ⟨6775971, by rfl⟩ : syracuseStep 18069257 = 13551943) B13551943
theorem B8048297 : Blo 988596 8048297 := bstep (se 2 (by rfl) ⟨3018111, by rfl⟩ : syracuseStep 8048297 = 6036223) B6036223
theorem B4511663 : Blo 988596 4511663 := bstep (se 1 (by rfl) ⟨3383747, by rfl⟩ : syracuseStep 4511663 = 6767495) B6767495
theorem B8126143 : Blo 988596 8126143 := bstep (se 1 (by rfl) ⟨6094607, by rfl⟩ : syracuseStep 8126143 = 12189215) B12189215
theorem B991039 : Blo 988596 991039 := bstep (se 1 (by rfl) ⟨743279, by rfl⟩ : syracuseStep 991039 = 1486559) B1486559
theorem B1487519 : Blo 988596 1487519 := bstep (se 1 (by rfl) ⟨1115639, by rfl⟩ : syracuseStep 1487519 = 2231279) B2231279
theorem B167361007 : Blo 988596 167361007 := bstep (se 1 (by rfl) ⟨125520755, by rfl⟩ : syracuseStep 167361007 = 251041511) B251041511
theorem B43339429 : Blo 988596 43339429 := bstep (se 4 (by rfl) ⟨4063071, by rfl⟩ : syracuseStep 43339429 = 8126143) B8126143
theorem B12046171 : Blo 988596 12046171 := bstep (se 1 (by rfl) ⟨9034628, by rfl⟩ : syracuseStep 12046171 = 18069257) B18069257
theorem B5365531 : Blo 988596 5365531 := bstep (se 1 (by rfl) ⟨4024148, by rfl⟩ : syracuseStep 5365531 = 8048297) B8048297
theorem B3007775 : Blo 988596 3007775 := bstep (se 1 (by rfl) ⟨2255831, by rfl⟩ : syracuseStep 3007775 = 4511663) B4511663
theorem B21457547 : Blo 988596 21457547 := bstep (se 1 (by rfl) ⟨16093160, by rfl⟩ : syracuseStep 21457547 = 32186321) B32186321
theorem B16061561 : Blo 988596 16061561 := bstep (se 2 (by rfl) ⟨6023085, by rfl⟩ : syracuseStep 16061561 = 12046171) B12046171
theorem B2005183 : Blo 988596 2005183 := bstep (se 1 (by rfl) ⟨1503887, by rfl⟩ : syracuseStep 2005183 = 3007775) B3007775
theorem B991679 : Blo 988596 991679 := bstep (se 1 (by rfl) ⟨743759, by rfl⟩ : syracuseStep 991679 = 1487519) B1487519
theorem B28616165 : Blo 988596 28616165 := bstep (se 4 (by rfl) ⟨2682765, by rfl⟩ : syracuseStep 28616165 = 5365531) B5365531
theorem B57785905 : Blo 988596 57785905 := bstep (se 2 (by rfl) ⟨21669714, by rfl⟩ : syracuseStep 57785905 = 43339429) B43339429
theorem B14305031 : Blo 988596 14305031 := bstep (se 1 (by rfl) ⟨10728773, by rfl⟩ : syracuseStep 14305031 = 21457547) B21457547
theorem B223148009 : Blo 988596 223148009 := bstep (se 2 (by rfl) ⟨83680503, by rfl⟩ : syracuseStep 223148009 = 167361007) B167361007
theorem B9536687 : Blo 988596 9536687 := bstep (se 1 (by rfl) ⟨7152515, by rfl⟩ : syracuseStep 9536687 = 14305031) B14305031
theorem B19077443 : Blo 988596 19077443 := bstep (se 1 (by rfl) ⟨14308082, by rfl⟩ : syracuseStep 19077443 = 28616165) B28616165
theorem B308191493 : Blo 988596 308191493 := bstep (se 4 (by rfl) ⟨28892952, by rfl⟩ : syracuseStep 308191493 = 57785905) B57785905
theorem B2673577 : Blo 988596 2673577 := bstep (se 2 (by rfl) ⟨1002591, by rfl⟩ : syracuseStep 2673577 = 2005183) B2005183
theorem B10707707 : Blo 988596 10707707 := bstep (se 1 (by rfl) ⟨8030780, by rfl⟩ : syracuseStep 10707707 = 16061561) B16061561
theorem B148765339 : Blo 988596 148765339 := bstep (se 1 (by rfl) ⟨111574004, by rfl⟩ : syracuseStep 148765339 = 223148009) B223148009
theorem B6357791 : Blo 988596 6357791 := bstep (se 1 (by rfl) ⟨4768343, by rfl⟩ : syracuseStep 6357791 = 9536687) B9536687
theorem B12718295 : Blo 988596 12718295 := bstep (se 1 (by rfl) ⟨9538721, by rfl⟩ : syracuseStep 12718295 = 19077443) B19077443
theorem B205460995 : Blo 988596 205460995 := bstep (se 1 (by rfl) ⟨154095746, by rfl⟩ : syracuseStep 205460995 = 308191493) B308191493
theorem B198353785 : Blo 988596 198353785 := bstep (se 2 (by rfl) ⟨74382669, by rfl⟩ : syracuseStep 198353785 = 148765339) B148765339
theorem B3564769 : Blo 988596 3564769 := bstep (se 2 (by rfl) ⟨1336788, by rfl⟩ : syracuseStep 3564769 = 2673577) B2673577
theorem B7138471 : Blo 988596 7138471 := bstep (se 1 (by rfl) ⟨5353853, by rfl⟩ : syracuseStep 7138471 = 10707707) B10707707
theorem B264471713 : Blo 988596 264471713 := bstep (se 2 (by rfl) ⟨99176892, by rfl⟩ : syracuseStep 264471713 = 198353785) B198353785
theorem B4753025 : Blo 988596 4753025 := bstep (se 2 (by rfl) ⟨1782384, by rfl⟩ : syracuseStep 4753025 = 3564769) B3564769
theorem B273947993 : Blo 988596 273947993 := bstep (se 2 (by rfl) ⟨102730497, by rfl⟩ : syracuseStep 273947993 = 205460995) B205460995
theorem B4238527 : Blo 988596 4238527 := bstep (se 1 (by rfl) ⟨3178895, by rfl⟩ : syracuseStep 4238527 = 6357791) B6357791
theorem B9517961 : Blo 988596 9517961 := bstep (se 2 (by rfl) ⟨3569235, by rfl⟩ : syracuseStep 9517961 = 7138471) B7138471
theorem B8478863 : Blo 988596 8478863 := bstep (se 1 (by rfl) ⟨6359147, by rfl⟩ : syracuseStep 8478863 = 12718295) B12718295
theorem B5651369 : Blo 988596 5651369 := bstep (se 2 (by rfl) ⟨2119263, by rfl⟩ : syracuseStep 5651369 = 4238527) B4238527
theorem B182631995 : Blo 988596 182631995 := bstep (se 1 (by rfl) ⟨136973996, by rfl⟩ : syracuseStep 182631995 = 273947993) B273947993
theorem B5652575 : Blo 988596 5652575 := bstep (se 1 (by rfl) ⟨4239431, by rfl⟩ : syracuseStep 5652575 = 8478863) B8478863
theorem B6345307 : Blo 988596 6345307 := bstep (se 1 (by rfl) ⟨4758980, by rfl⟩ : syracuseStep 6345307 = 9517961) B9517961
theorem B176314475 : Blo 988596 176314475 := bstep (se 1 (by rfl) ⟨132235856, by rfl⟩ : syracuseStep 176314475 = 264471713) B264471713
theorem B3168683 : Blo 988596 3168683 := bstep (se 1 (by rfl) ⟨2376512, by rfl⟩ : syracuseStep 3168683 = 4753025) B4753025
theorem B3768383 : Blo 988596 3768383 := bstep (se 1 (by rfl) ⟨2826287, by rfl⟩ : syracuseStep 3768383 = 5652575) B5652575
theorem B117542983 : Blo 988596 117542983 := bstep (se 1 (by rfl) ⟨88157237, by rfl⟩ : syracuseStep 117542983 = 176314475) B176314475
theorem B8460409 : Blo 988596 8460409 := bstep (se 2 (by rfl) ⟨3172653, by rfl⟩ : syracuseStep 8460409 = 6345307) B6345307
theorem B2112455 : Blo 988596 2112455 := bstep (se 1 (by rfl) ⟨1584341, by rfl⟩ : syracuseStep 2112455 = 3168683) B3168683
theorem B121754663 : Blo 988596 121754663 := bstep (se 1 (by rfl) ⟨91315997, by rfl⟩ : syracuseStep 121754663 = 182631995) B182631995
theorem B3767579 : Blo 988596 3767579 := bstep (se 1 (by rfl) ⟨2825684, by rfl⟩ : syracuseStep 3767579 = 5651369) B5651369
theorem B81169775 : Blo 988596 81169775 := bstep (se 1 (by rfl) ⟨60877331, by rfl⟩ : syracuseStep 81169775 = 121754663) B121754663
theorem B11280545 : Blo 988596 11280545 := bstep (se 2 (by rfl) ⟨4230204, by rfl⟩ : syracuseStep 11280545 = 8460409) B8460409
theorem B2511719 : Blo 988596 2511719 := bstep (se 1 (by rfl) ⟨1883789, by rfl⟩ : syracuseStep 2511719 = 3767579) B3767579
theorem B2512255 : Blo 988596 2512255 := bstep (se 1 (by rfl) ⟨1884191, by rfl⟩ : syracuseStep 2512255 = 3768383) B3768383
theorem B156723977 : Blo 988596 156723977 := bstep (se 2 (by rfl) ⟨58771491, by rfl⟩ : syracuseStep 156723977 = 117542983) B117542983
theorem B1408303 : Blo 988596 1408303 := bstep (se 1 (by rfl) ⟨1056227, by rfl⟩ : syracuseStep 1408303 = 2112455) B2112455
theorem B1674479 : Blo 988596 1674479 := bstep (se 1 (by rfl) ⟨1255859, by rfl⟩ : syracuseStep 1674479 = 2511719) B2511719
theorem B3349673 : Blo 988596 3349673 := bstep (se 2 (by rfl) ⟨1256127, by rfl⟩ : syracuseStep 3349673 = 2512255) B2512255
theorem B1877737 : Blo 988596 1877737 := bstep (se 2 (by rfl) ⟨704151, by rfl⟩ : syracuseStep 1877737 = 1408303) B1408303
theorem B54113183 : Blo 988596 54113183 := bstep (se 1 (by rfl) ⟨40584887, by rfl⟩ : syracuseStep 54113183 = 81169775) B81169775
theorem B7520363 : Blo 988596 7520363 := bstep (se 1 (by rfl) ⟨5640272, by rfl⟩ : syracuseStep 7520363 = 11280545) B11280545
theorem B104482651 : Blo 988596 104482651 := bstep (se 1 (by rfl) ⟨78361988, by rfl⟩ : syracuseStep 104482651 = 156723977) B156723977
theorem B5013575 : Blo 988596 5013575 := bstep (se 1 (by rfl) ⟨3760181, by rfl⟩ : syracuseStep 5013575 = 7520363) B7520363
theorem B1116319 : Blo 988596 1116319 := bstep (se 1 (by rfl) ⟨837239, by rfl⟩ : syracuseStep 1116319 = 1674479) B1674479
theorem B2233115 : Blo 988596 2233115 := bstep (se 1 (by rfl) ⟨1674836, by rfl⟩ : syracuseStep 2233115 = 3349673) B3349673
theorem B2503649 : Blo 988596 2503649 := bstep (se 2 (by rfl) ⟨938868, by rfl⟩ : syracuseStep 2503649 = 1877737) B1877737
theorem B139310201 : Blo 988596 139310201 := bstep (se 2 (by rfl) ⟨52241325, by rfl⟩ : syracuseStep 139310201 = 104482651) B104482651
theorem B36075455 : Blo 988596 36075455 := bstep (se 1 (by rfl) ⟨27056591, by rfl⟩ : syracuseStep 36075455 = 54113183) B54113183
theorem B3342383 : Blo 988596 3342383 := bstep (se 1 (by rfl) ⟨2506787, by rfl⟩ : syracuseStep 3342383 = 5013575) B5013575
theorem B92873467 : Blo 988596 92873467 := bstep (se 1 (by rfl) ⟨69655100, by rfl⟩ : syracuseStep 92873467 = 139310201) B139310201
theorem B1488425 : Blo 988596 1488425 := bstep (se 2 (by rfl) ⟨558159, by rfl⟩ : syracuseStep 1488425 = 1116319) B1116319
theorem B1488743 : Blo 988596 1488743 := bstep (se 1 (by rfl) ⟨1116557, by rfl⟩ : syracuseStep 1488743 = 2233115) B2233115
theorem B1669099 : Blo 988596 1669099 := bstep (se 1 (by rfl) ⟨1251824, by rfl⟩ : syracuseStep 1669099 = 2503649) B2503649
theorem B24050303 : Blo 988596 24050303 := bstep (se 1 (by rfl) ⟨18037727, by rfl⟩ : syracuseStep 24050303 = 36075455) B36075455
theorem B2228255 : Blo 988596 2228255 := bstep (se 1 (by rfl) ⟨1671191, by rfl⟩ : syracuseStep 2228255 = 3342383) B3342383
theorem B123831289 : Blo 988596 123831289 := bstep (se 2 (by rfl) ⟨46436733, by rfl⟩ : syracuseStep 123831289 = 92873467) B92873467
theorem B992283 : Blo 988596 992283 := bstep (se 1 (by rfl) ⟨744212, by rfl⟩ : syracuseStep 992283 = 1488425) B1488425
theorem B992495 : Blo 988596 992495 := bstep (se 1 (by rfl) ⟨744371, by rfl⟩ : syracuseStep 992495 = 1488743) B1488743
theorem B16033535 : Blo 988596 16033535 := bstep (se 1 (by rfl) ⟨12025151, by rfl⟩ : syracuseStep 16033535 = 24050303) B24050303
theorem B2225465 : Blo 988596 2225465 := bstep (se 2 (by rfl) ⟨834549, by rfl⟩ : syracuseStep 2225465 = 1669099) B1669099
theorem B10689023 : Blo 988596 10689023 := bstep (se 1 (by rfl) ⟨8016767, by rfl⟩ : syracuseStep 10689023 = 16033535) B16033535
theorem B1483643 : Blo 988596 1483643 := bstep (se 1 (by rfl) ⟨1112732, by rfl⟩ : syracuseStep 1483643 = 2225465) B2225465
theorem B1485503 : Blo 988596 1485503 := bstep (se 1 (by rfl) ⟨1114127, by rfl⟩ : syracuseStep 1485503 = 2228255) B2228255
theorem B165108385 : Blo 988596 165108385 := bstep (se 2 (by rfl) ⟨61915644, by rfl⟩ : syracuseStep 165108385 = 123831289) B123831289
theorem B989095 : Blo 988596 989095 := bstep (se 1 (by rfl) ⟨741821, by rfl⟩ : syracuseStep 989095 = 1483643) B1483643
theorem B990335 : Blo 988596 990335 := bstep (se 1 (by rfl) ⟨742751, by rfl⟩ : syracuseStep 990335 = 1485503) B1485503
theorem B220144513 : Blo 988596 220144513 := bstep (se 2 (by rfl) ⟨82554192, by rfl⟩ : syracuseStep 220144513 = 165108385) B165108385
theorem B28504061 : Blo 988596 28504061 := bstep (se 3 (by rfl) ⟨5344511, by rfl⟩ : syracuseStep 28504061 = 10689023) B10689023
theorem B293526017 : Blo 988596 293526017 := bstep (se 2 (by rfl) ⟨110072256, by rfl⟩ : syracuseStep 293526017 = 220144513) B220144513
theorem B19002707 : Blo 988596 19002707 := bstep (se 1 (by rfl) ⟨14252030, by rfl⟩ : syracuseStep 19002707 = 28504061) B28504061
theorem B12668471 : Blo 988596 12668471 := bstep (se 1 (by rfl) ⟨9501353, by rfl⟩ : syracuseStep 12668471 = 19002707) B19002707
theorem B195684011 : Blo 988596 195684011 := bstep (se 1 (by rfl) ⟨146763008, by rfl⟩ : syracuseStep 195684011 = 293526017) B293526017
theorem B130456007 : Blo 988596 130456007 := bstep (se 1 (by rfl) ⟨97842005, by rfl⟩ : syracuseStep 130456007 = 195684011) B195684011
theorem B8445647 : Blo 988596 8445647 := bstep (se 1 (by rfl) ⟨6334235, by rfl⟩ : syracuseStep 8445647 = 12668471) B12668471
theorem B86970671 : Blo 988596 86970671 := bstep (se 1 (by rfl) ⟨65228003, by rfl⟩ : syracuseStep 86970671 = 130456007) B130456007
theorem B5630431 : Blo 988596 5630431 := bstep (se 1 (by rfl) ⟨4222823, by rfl⟩ : syracuseStep 5630431 = 8445647) B8445647
theorem B7507241 : Blo 988596 7507241 := bstep (se 2 (by rfl) ⟨2815215, by rfl⟩ : syracuseStep 7507241 = 5630431) B5630431
theorem B57980447 : Blo 988596 57980447 := bstep (se 1 (by rfl) ⟨43485335, by rfl⟩ : syracuseStep 57980447 = 86970671) B86970671
theorem B38653631 : Blo 988596 38653631 := bstep (se 1 (by rfl) ⟨28990223, by rfl⟩ : syracuseStep 38653631 = 57980447) B57980447
theorem B5004827 : Blo 988596 5004827 := bstep (se 1 (by rfl) ⟨3753620, by rfl⟩ : syracuseStep 5004827 = 7507241) B7507241
theorem B25769087 : Blo 988596 25769087 := bstep (se 1 (by rfl) ⟨19326815, by rfl⟩ : syracuseStep 25769087 = 38653631) B38653631
theorem B3336551 : Blo 988596 3336551 := bstep (se 1 (by rfl) ⟨2502413, by rfl⟩ : syracuseStep 3336551 = 5004827) B5004827
theorem B17179391 : Blo 988596 17179391 := bstep (se 1 (by rfl) ⟨12884543, by rfl⟩ : syracuseStep 17179391 = 25769087) B25769087
theorem B2224367 : Blo 988596 2224367 := bstep (se 1 (by rfl) ⟨1668275, by rfl⟩ : syracuseStep 2224367 = 3336551) B3336551
theorem B1482911 : Blo 988596 1482911 := bstep (se 1 (by rfl) ⟨1112183, by rfl⟩ : syracuseStep 1482911 = 2224367) B2224367
theorem B11452927 : Blo 988596 11452927 := bstep (se 1 (by rfl) ⟨8589695, by rfl⟩ : syracuseStep 11452927 = 17179391) B17179391
theorem B15270569 : Blo 988596 15270569 := bstep (se 2 (by rfl) ⟨5726463, by rfl⟩ : syracuseStep 15270569 = 11452927) B11452927
theorem B988607 : Blo 988596 988607 := bstep (se 1 (by rfl) ⟨741455, by rfl⟩ : syracuseStep 988607 = 1482911) B1482911
theorem B10180379 : Blo 988596 10180379 := bstep (se 1 (by rfl) ⟨7635284, by rfl⟩ : syracuseStep 10180379 = 15270569) B15270569
theorem B6786919 : Blo 988596 6786919 := bstep (se 1 (by rfl) ⟨5090189, by rfl⟩ : syracuseStep 6786919 = 10180379) B10180379
theorem B36196901 : Blo 988596 36196901 := bstep (se 4 (by rfl) ⟨3393459, by rfl⟩ : syracuseStep 36196901 = 6786919) B6786919
theorem B24131267 : Blo 988596 24131267 := bstep (se 1 (by rfl) ⟨18098450, by rfl⟩ : syracuseStep 24131267 = 36196901) B36196901
theorem B16087511 : Blo 988596 16087511 := bstep (se 1 (by rfl) ⟨12065633, by rfl⟩ : syracuseStep 16087511 = 24131267) B24131267
theorem B10725007 : Blo 988596 10725007 := bstep (se 1 (by rfl) ⟨8043755, by rfl⟩ : syracuseStep 10725007 = 16087511) B16087511
theorem B14300009 : Blo 988596 14300009 := bstep (se 2 (by rfl) ⟨5362503, by rfl⟩ : syracuseStep 14300009 = 10725007) B10725007
theorem B9533339 : Blo 988596 9533339 := bstep (se 1 (by rfl) ⟨7150004, by rfl⟩ : syracuseStep 9533339 = 14300009) B14300009
theorem B6355559 : Blo 988596 6355559 := bstep (se 1 (by rfl) ⟨4766669, by rfl⟩ : syracuseStep 6355559 = 9533339) B9533339
theorem B4237039 : Blo 988596 4237039 := bstep (se 1 (by rfl) ⟨3177779, by rfl⟩ : syracuseStep 4237039 = 6355559) B6355559
theorem B5649385 : Blo 988596 5649385 := bstep (se 2 (by rfl) ⟨2118519, by rfl⟩ : syracuseStep 5649385 = 4237039) B4237039
theorem B7532513 : Blo 988596 7532513 := bstep (se 2 (by rfl) ⟨2824692, by rfl⟩ : syracuseStep 7532513 = 5649385) B5649385
theorem B5021675 : Blo 988596 5021675 := bstep (se 1 (by rfl) ⟨3766256, by rfl⟩ : syracuseStep 5021675 = 7532513) B7532513
theorem B3347783 : Blo 988596 3347783 := bstep (se 1 (by rfl) ⟨2510837, by rfl⟩ : syracuseStep 3347783 = 5021675) B5021675
theorem B2231855 : Blo 988596 2231855 := bstep (se 1 (by rfl) ⟨1673891, by rfl⟩ : syracuseStep 2231855 = 3347783) B3347783
theorem B1487903 : Blo 988596 1487903 := bstep (se 1 (by rfl) ⟨1115927, by rfl⟩ : syracuseStep 1487903 = 2231855) B2231855
theorem B991935 : Blo 988596 991935 := bstep (se 1 (by rfl) ⟨743951, by rfl⟩ : syracuseStep 991935 = 1487903) B1487903

theorem C0 (j : ℕ) (h1 : 247149 ≤ j) (h2 : j ≤ 247848) : Blo 988596 (4 * j + 3) := by
  interval_cases j
  · exact B988599
  · exact B988603
  · exact B988607
  · exact B988611
  · exact B988615
  · exact B988619
  · exact B988623
  · exact B988627
  · exact B988631
  · exact B988635
  · exact B988639
  · exact B988643
  · exact B988647
  · exact B988651
  · exact B988655
  · exact B988659
  · exact B988663
  · exact B988667
  · exact B988671
  · exact B988675
  · exact B988679
  · exact B988683
  · exact B988687
  · exact B988691
  · exact B988695
  · exact B988699
  · exact B988703
  · exact B988707
  · exact B988711
  · exact B988715
  · exact B988719
  · exact B988723
  · exact B988727
  · exact B988731
  · exact B988735
  · exact B988739
  · exact B988743
  · exact B988747
  · exact B988751
  · exact B988755
  · exact B988759
  · exact B988763
  · exact B988767
  · exact B988771
  · exact B988775
  · exact B988779
  · exact B988783
  · exact B988787
  · exact B988791
  · exact B988795
  · exact B988799
  · exact B988803
  · exact B988807
  · exact B988811
  · exact B988815
  · exact B988819
  · exact B988823
  · exact B988827
  · exact B988831
  · exact B988835
  · exact B988839
  · exact B988843
  · exact B988847
  · exact B988851
  · exact B988855
  · exact B988859
  · exact B988863
  · exact B988867
  · exact B988871
  · exact B988875
  · exact B988879
  · exact B988883
  · exact B988887
  · exact B988891
  · exact B988895
  · exact B988899
  · exact B988903
  · exact B988907
  · exact B988911
  · exact B988915
  · exact B988919
  · exact B988923
  · exact B988927
  · exact B988931
  · exact B988935
  · exact B988939
  · exact B988943
  · exact B988947
  · exact B988951
  · exact B988955
  · exact B988959
  · exact B988963
  · exact B988967
  · exact B988971
  · exact B988975
  · exact B988979
  · exact B988983
  · exact B988987
  · exact B988991
  · exact B988995
  · exact B988999
  · exact B989003
  · exact B989007
  · exact B989011
  · exact B989015
  · exact B989019
  · exact B989023
  · exact B989027
  · exact B989031
  · exact B989035
  · exact B989039
  · exact B989043
  · exact B989047
  · exact B989051
  · exact B989055
  · exact B989059
  · exact B989063
  · exact B989067
  · exact B989071
  · exact B989075
  · exact B989079
  · exact B989083
  · exact B989087
  · exact B989091
  · exact B989095
  · exact B989099
  · exact B989103
  · exact B989107
  · exact B989111
  · exact B989115
  · exact B989119
  · exact B989123
  · exact B989127
  · exact B989131
  · exact B989135
  · exact B989139
  · exact B989143
  · exact B989147
  · exact B989151
  · exact B989155
  · exact B989159
  · exact B989163
  · exact B989167
  · exact B989171
  · exact B989175
  · exact B989179
  · exact B989183
  · exact B989187
  · exact B989191
  · exact B989195
  · exact B989199
  · exact B989203
  · exact B989207
  · exact B989211
  · exact B989215
  · exact B989219
  · exact B989223
  · exact B989227
  · exact B989231
  · exact B989235
  · exact B989239
  · exact B989243
  · exact B989247
  · exact B989251
  · exact B989255
  · exact B989259
  · exact B989263
  · exact B989267
  · exact B989271
  · exact B989275
  · exact B989279
  · exact B989283
  · exact B989287
  · exact B989291
  · exact B989295
  · exact B989299
  · exact B989303
  · exact B989307
  · exact B989311
  · exact B989315
  · exact B989319
  · exact B989323
  · exact B989327
  · exact B989331
  · exact B989335
  · exact B989339
  · exact B989343
  · exact B989347
  · exact B989351
  · exact B989355
  · exact B989359
  · exact B989363
  · exact B989367
  · exact B989371
  · exact B989375
  · exact B989379
  · exact B989383
  · exact B989387
  · exact B989391
  · exact B989395
  · exact B989399
  · exact B989403
  · exact B989407
  · exact B989411
  · exact B989415
  · exact B989419
  · exact B989423
  · exact B989427
  · exact B989431
  · exact B989435
  · exact B989439
  · exact B989443
  · exact B989447
  · exact B989451
  · exact B989455
  · exact B989459
  · exact B989463
  · exact B989467
  · exact B989471
  · exact B989475
  · exact B989479
  · exact B989483
  · exact B989487
  · exact B989491
  · exact B989495
  · exact B989499
  · exact B989503
  · exact B989507
  · exact B989511
  · exact B989515
  · exact B989519
  · exact B989523
  · exact B989527
  · exact B989531
  · exact B989535
  · exact B989539
  · exact B989543
  · exact B989547
  · exact B989551
  · exact B989555
  · exact B989559
  · exact B989563
  · exact B989567
  · exact B989571
  · exact B989575
  · exact B989579
  · exact B989583
  · exact B989587
  · exact B989591
  · exact B989595
  · exact B989599
  · exact B989603
  · exact B989607
  · exact B989611
  · exact B989615
  · exact B989619
  · exact B989623
  · exact B989627
  · exact B989631
  · exact B989635
  · exact B989639
  · exact B989643
  · exact B989647
  · exact B989651
  · exact B989655
  · exact B989659
  · exact B989663
  · exact B989667
  · exact B989671
  · exact B989675
  · exact B989679
  · exact B989683
  · exact B989687
  · exact B989691
  · exact B989695
  · exact B989699
  · exact B989703
  · exact B989707
  · exact B989711
  · exact B989715
  · exact B989719
  · exact B989723
  · exact B989727
  · exact B989731
  · exact B989735
  · exact B989739
  · exact B989743
  · exact B989747
  · exact B989751
  · exact B989755
  · exact B989759
  · exact B989763
  · exact B989767
  · exact B989771
  · exact B989775
  · exact B989779
  · exact B989783
  · exact B989787
  · exact B989791
  · exact B989795
  · exact B989799
  · exact B989803
  · exact B989807
  · exact B989811
  · exact B989815
  · exact B989819
  · exact B989823
  · exact B989827
  · exact B989831
  · exact B989835
  · exact B989839
  · exact B989843
  · exact B989847
  · exact B989851
  · exact B989855
  · exact B989859
  · exact B989863
  · exact B989867
  · exact B989871
  · exact B989875
  · exact B989879
  · exact B989883
  · exact B989887
  · exact B989891
  · exact B989895
  · exact B989899
  · exact B989903
  · exact B989907
  · exact B989911
  · exact B989915
  · exact B989919
  · exact B989923
  · exact B989927
  · exact B989931
  · exact B989935
  · exact B989939
  · exact B989943
  · exact B989947
  · exact B989951
  · exact B989955
  · exact B989959
  · exact B989963
  · exact B989967
  · exact B989971
  · exact B989975
  · exact B989979
  · exact B989983
  · exact B989987
  · exact B989991
  · exact B989995
  · exact B989999
  · exact B990003
  · exact B990007
  · exact B990011
  · exact B990015
  · exact B990019
  · exact B990023
  · exact B990027
  · exact B990031
  · exact B990035
  · exact B990039
  · exact B990043
  · exact B990047
  · exact B990051
  · exact B990055
  · exact B990059
  · exact B990063
  · exact B990067
  · exact B990071
  · exact B990075
  · exact B990079
  · exact B990083
  · exact B990087
  · exact B990091
  · exact B990095
  · exact B990099
  · exact B990103
  · exact B990107
  · exact B990111
  · exact B990115
  · exact B990119
  · exact B990123
  · exact B990127
  · exact B990131
  · exact B990135
  · exact B990139
  · exact B990143
  · exact B990147
  · exact B990151
  · exact B990155
  · exact B990159
  · exact B990163
  · exact B990167
  · exact B990171
  · exact B990175
  · exact B990179
  · exact B990183
  · exact B990187
  · exact B990191
  · exact B990195
  · exact B990199
  · exact B990203
  · exact B990207
  · exact B990211
  · exact B990215
  · exact B990219
  · exact B990223
  · exact B990227
  · exact B990231
  · exact B990235
  · exact B990239
  · exact B990243
  · exact B990247
  · exact B990251
  · exact B990255
  · exact B990259
  · exact B990263
  · exact B990267
  · exact B990271
  · exact B990275
  · exact B990279
  · exact B990283
  · exact B990287
  · exact B990291
  · exact B990295
  · exact B990299
  · exact B990303
  · exact B990307
  · exact B990311
  · exact B990315
  · exact B990319
  · exact B990323
  · exact B990327
  · exact B990331
  · exact B990335
  · exact B990339
  · exact B990343
  · exact B990347
  · exact B990351
  · exact B990355
  · exact B990359
  · exact B990363
  · exact B990367
  · exact B990371
  · exact B990375
  · exact B990379
  · exact B990383
  · exact B990387
  · exact B990391
  · exact B990395
  · exact B990399
  · exact B990403
  · exact B990407
  · exact B990411
  · exact B990415
  · exact B990419
  · exact B990423
  · exact B990427
  · exact B990431
  · exact B990435
  · exact B990439
  · exact B990443
  · exact B990447
  · exact B990451
  · exact B990455
  · exact B990459
  · exact B990463
  · exact B990467
  · exact B990471
  · exact B990475
  · exact B990479
  · exact B990483
  · exact B990487
  · exact B990491
  · exact B990495
  · exact B990499
  · exact B990503
  · exact B990507
  · exact B990511
  · exact B990515
  · exact B990519
  · exact B990523
  · exact B990527
  · exact B990531
  · exact B990535
  · exact B990539
  · exact B990543
  · exact B990547
  · exact B990551
  · exact B990555
  · exact B990559
  · exact B990563
  · exact B990567
  · exact B990571
  · exact B990575
  · exact B990579
  · exact B990583
  · exact B990587
  · exact B990591
  · exact B990595
  · exact B990599
  · exact B990603
  · exact B990607
  · exact B990611
  · exact B990615
  · exact B990619
  · exact B990623
  · exact B990627
  · exact B990631
  · exact B990635
  · exact B990639
  · exact B990643
  · exact B990647
  · exact B990651
  · exact B990655
  · exact B990659
  · exact B990663
  · exact B990667
  · exact B990671
  · exact B990675
  · exact B990679
  · exact B990683
  · exact B990687
  · exact B990691
  · exact B990695
  · exact B990699
  · exact B990703
  · exact B990707
  · exact B990711
  · exact B990715
  · exact B990719
  · exact B990723
  · exact B990727
  · exact B990731
  · exact B990735
  · exact B990739
  · exact B990743
  · exact B990747
  · exact B990751
  · exact B990755
  · exact B990759
  · exact B990763
  · exact B990767
  · exact B990771
  · exact B990775
  · exact B990779
  · exact B990783
  · exact B990787
  · exact B990791
  · exact B990795
  · exact B990799
  · exact B990803
  · exact B990807
  · exact B990811
  · exact B990815
  · exact B990819
  · exact B990823
  · exact B990827
  · exact B990831
  · exact B990835
  · exact B990839
  · exact B990843
  · exact B990847
  · exact B990851
  · exact B990855
  · exact B990859
  · exact B990863
  · exact B990867
  · exact B990871
  · exact B990875
  · exact B990879
  · exact B990883
  · exact B990887
  · exact B990891
  · exact B990895
  · exact B990899
  · exact B990903
  · exact B990907
  · exact B990911
  · exact B990915
  · exact B990919
  · exact B990923
  · exact B990927
  · exact B990931
  · exact B990935
  · exact B990939
  · exact B990943
  · exact B990947
  · exact B990951
  · exact B990955
  · exact B990959
  · exact B990963
  · exact B990967
  · exact B990971
  · exact B990975
  · exact B990979
  · exact B990983
  · exact B990987
  · exact B990991
  · exact B990995
  · exact B990999
  · exact B991003
  · exact B991007
  · exact B991011
  · exact B991015
  · exact B991019
  · exact B991023
  · exact B991027
  · exact B991031
  · exact B991035
  · exact B991039
  · exact B991043
  · exact B991047
  · exact B991051
  · exact B991055
  · exact B991059
  · exact B991063
  · exact B991067
  · exact B991071
  · exact B991075
  · exact B991079
  · exact B991083
  · exact B991087
  · exact B991091
  · exact B991095
  · exact B991099
  · exact B991103
  · exact B991107
  · exact B991111
  · exact B991115
  · exact B991119
  · exact B991123
  · exact B991127
  · exact B991131
  · exact B991135
  · exact B991139
  · exact B991143
  · exact B991147
  · exact B991151
  · exact B991155
  · exact B991159
  · exact B991163
  · exact B991167
  · exact B991171
  · exact B991175
  · exact B991179
  · exact B991183
  · exact B991187
  · exact B991191
  · exact B991195
  · exact B991199
  · exact B991203
  · exact B991207
  · exact B991211
  · exact B991215
  · exact B991219
  · exact B991223
  · exact B991227
  · exact B991231
  · exact B991235
  · exact B991239
  · exact B991243
  · exact B991247
  · exact B991251
  · exact B991255
  · exact B991259
  · exact B991263
  · exact B991267
  · exact B991271
  · exact B991275
  · exact B991279
  · exact B991283
  · exact B991287
  · exact B991291
  · exact B991295
  · exact B991299
  · exact B991303
  · exact B991307
  · exact B991311
  · exact B991315
  · exact B991319
  · exact B991323
  · exact B991327
  · exact B991331
  · exact B991335
  · exact B991339
  · exact B991343
  · exact B991347
  · exact B991351
  · exact B991355
  · exact B991359
  · exact B991363
  · exact B991367
  · exact B991371
  · exact B991375
  · exact B991379
  · exact B991383
  · exact B991387
  · exact B991391
  · exact B991395

theorem C1 (j : ℕ) (h1 : 247849 ≤ j) (h2 : j ≤ 248148) : Blo 988596 (4 * j + 3) := by
  interval_cases j
  · exact B991399
  · exact B991403
  · exact B991407
  · exact B991411
  · exact B991415
  · exact B991419
  · exact B991423
  · exact B991427
  · exact B991431
  · exact B991435
  · exact B991439
  · exact B991443
  · exact B991447
  · exact B991451
  · exact B991455
  · exact B991459
  · exact B991463
  · exact B991467
  · exact B991471
  · exact B991475
  · exact B991479
  · exact B991483
  · exact B991487
  · exact B991491
  · exact B991495
  · exact B991499
  · exact B991503
  · exact B991507
  · exact B991511
  · exact B991515
  · exact B991519
  · exact B991523
  · exact B991527
  · exact B991531
  · exact B991535
  · exact B991539
  · exact B991543
  · exact B991547
  · exact B991551
  · exact B991555
  · exact B991559
  · exact B991563
  · exact B991567
  · exact B991571
  · exact B991575
  · exact B991579
  · exact B991583
  · exact B991587
  · exact B991591
  · exact B991595
  · exact B991599
  · exact B991603
  · exact B991607
  · exact B991611
  · exact B991615
  · exact B991619
  · exact B991623
  · exact B991627
  · exact B991631
  · exact B991635
  · exact B991639
  · exact B991643
  · exact B991647
  · exact B991651
  · exact B991655
  · exact B991659
  · exact B991663
  · exact B991667
  · exact B991671
  · exact B991675
  · exact B991679
  · exact B991683
  · exact B991687
  · exact B991691
  · exact B991695
  · exact B991699
  · exact B991703
  · exact B991707
  · exact B991711
  · exact B991715
  · exact B991719
  · exact B991723
  · exact B991727
  · exact B991731
  · exact B991735
  · exact B991739
  · exact B991743
  · exact B991747
  · exact B991751
  · exact B991755
  · exact B991759
  · exact B991763
  · exact B991767
  · exact B991771
  · exact B991775
  · exact B991779
  · exact B991783
  · exact B991787
  · exact B991791
  · exact B991795
  · exact B991799
  · exact B991803
  · exact B991807
  · exact B991811
  · exact B991815
  · exact B991819
  · exact B991823
  · exact B991827
  · exact B991831
  · exact B991835
  · exact B991839
  · exact B991843
  · exact B991847
  · exact B991851
  · exact B991855
  · exact B991859
  · exact B991863
  · exact B991867
  · exact B991871
  · exact B991875
  · exact B991879
  · exact B991883
  · exact B991887
  · exact B991891
  · exact B991895
  · exact B991899
  · exact B991903
  · exact B991907
  · exact B991911
  · exact B991915
  · exact B991919
  · exact B991923
  · exact B991927
  · exact B991931
  · exact B991935
  · exact B991939
  · exact B991943
  · exact B991947
  · exact B991951
  · exact B991955
  · exact B991959
  · exact B991963
  · exact B991967
  · exact B991971
  · exact B991975
  · exact B991979
  · exact B991983
  · exact B991987
  · exact B991991
  · exact B991995
  · exact B991999
  · exact B992003
  · exact B992007
  · exact B992011
  · exact B992015
  · exact B992019
  · exact B992023
  · exact B992027
  · exact B992031
  · exact B992035
  · exact B992039
  · exact B992043
  · exact B992047
  · exact B992051
  · exact B992055
  · exact B992059
  · exact B992063
  · exact B992067
  · exact B992071
  · exact B992075
  · exact B992079
  · exact B992083
  · exact B992087
  · exact B992091
  · exact B992095
  · exact B992099
  · exact B992103
  · exact B992107
  · exact B992111
  · exact B992115
  · exact B992119
  · exact B992123
  · exact B992127
  · exact B992131
  · exact B992135
  · exact B992139
  · exact B992143
  · exact B992147
  · exact B992151
  · exact B992155
  · exact B992159
  · exact B992163
  · exact B992167
  · exact B992171
  · exact B992175
  · exact B992179
  · exact B992183
  · exact B992187
  · exact B992191
  · exact B992195
  · exact B992199
  · exact B992203
  · exact B992207
  · exact B992211
  · exact B992215
  · exact B992219
  · exact B992223
  · exact B992227
  · exact B992231
  · exact B992235
  · exact B992239
  · exact B992243
  · exact B992247
  · exact B992251
  · exact B992255
  · exact B992259
  · exact B992263
  · exact B992267
  · exact B992271
  · exact B992275
  · exact B992279
  · exact B992283
  · exact B992287
  · exact B992291
  · exact B992295
  · exact B992299
  · exact B992303
  · exact B992307
  · exact B992311
  · exact B992315
  · exact B992319
  · exact B992323
  · exact B992327
  · exact B992331
  · exact B992335
  · exact B992339
  · exact B992343
  · exact B992347
  · exact B992351
  · exact B992355
  · exact B992359
  · exact B992363
  · exact B992367
  · exact B992371
  · exact B992375
  · exact B992379
  · exact B992383
  · exact B992387
  · exact B992391
  · exact B992395
  · exact B992399
  · exact B992403
  · exact B992407
  · exact B992411
  · exact B992415
  · exact B992419
  · exact B992423
  · exact B992427
  · exact B992431
  · exact B992435
  · exact B992439
  · exact B992443
  · exact B992447
  · exact B992451
  · exact B992455
  · exact B992459
  · exact B992463
  · exact B992467
  · exact B992471
  · exact B992475
  · exact B992479
  · exact B992483
  · exact B992487
  · exact B992491
  · exact B992495
  · exact B992499
  · exact B992503
  · exact B992507
  · exact B992511
  · exact B992515
  · exact B992519
  · exact B992523
  · exact B992527
  · exact B992531
  · exact B992535
  · exact B992539
  · exact B992543
  · exact B992547
  · exact B992551
  · exact B992555
  · exact B992559
  · exact B992563
  · exact B992567
  · exact B992571
  · exact B992575
  · exact B992579
  · exact B992583
  · exact B992587
  · exact B992591
  · exact B992595

theorem solution (m : ℕ) (hlo : 988596 ≤ m) (hhi : m ≤ 992596) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 247149 ≤ j := by omega
    have hj2 : j ≤ 248148 := by omega
    have hb : Blo 988596 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 247849 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
