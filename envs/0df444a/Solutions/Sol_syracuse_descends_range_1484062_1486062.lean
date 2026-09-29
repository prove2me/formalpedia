-- Prove2me | solution 1 for syracuse_descends_range_1484062_1486062
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:46:10.805562+00:00
-- url     : https://prove2.me/submissions/b03f3bfe-bd09-4c8b-a106-e5a248dfe430

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


theorem B1671169 : Blo 1484062 1671169 := bbase (se 2 (by rfl) ⟨626688, by rfl⟩ : syracuseStep 1671169 = 1253377) (by norm_num)
theorem B3760141 : Blo 1484062 3760141 := bbase (se 3 (by rfl) ⟨705026, by rfl⟩ : syracuseStep 3760141 = 1410053) (by norm_num)
theorem B2228237 : Blo 1484062 2228237 := bbase (se 3 (by rfl) ⟨417794, by rfl⟩ : syracuseStep 2228237 = 835589) (by norm_num)
theorem B3342365 : Blo 1484062 3342365 := bbase (se 3 (by rfl) ⟨626693, by rfl⟩ : syracuseStep 3342365 = 1253387) (by norm_num)
theorem B2506781 : Blo 1484062 2506781 := bbase (se 3 (by rfl) ⟨470021, by rfl⟩ : syracuseStep 2506781 = 940043) (by norm_num)
theorem B2228261 : Blo 1484062 2228261 := bbase (se 4 (by rfl) ⟨208899, by rfl⟩ : syracuseStep 2228261 = 417799) (by norm_num)
theorem B1671205 : Blo 1484062 1671205 := bbase (se 4 (by rfl) ⟨156675, by rfl⟩ : syracuseStep 1671205 = 313351) (by norm_num)
theorem B2228285 : Blo 1484062 2228285 := bbase (se 3 (by rfl) ⟨417803, by rfl⟩ : syracuseStep 2228285 = 835607) (by norm_num)
theorem B1671241 : Blo 1484062 1671241 := bbase (se 2 (by rfl) ⟨626715, by rfl⟩ : syracuseStep 1671241 = 1253431) (by norm_num)
theorem B2228309 : Blo 1484062 2228309 := bbase (se 8 (by rfl) ⟨13056, by rfl⟩ : syracuseStep 2228309 = 26113) (by norm_num)
theorem B3342437 : Blo 1484062 3342437 := bbase (se 4 (by rfl) ⟨313353, by rfl⟩ : syracuseStep 3342437 = 626707) (by norm_num)
theorem B2228333 : Blo 1484062 2228333 := bbase (se 3 (by rfl) ⟨417812, by rfl⟩ : syracuseStep 2228333 = 835625) (by norm_num)
theorem B1671277 : Blo 1484062 1671277 := bbase (se 3 (by rfl) ⟨313364, by rfl⟩ : syracuseStep 1671277 = 626729) (by norm_num)
theorem B3760253 : Blo 1484062 3760253 := bbase (se 3 (by rfl) ⟨705047, by rfl⟩ : syracuseStep 3760253 = 1410095) (by norm_num)
theorem B2228357 : Blo 1484062 2228357 := bbase (se 4 (by rfl) ⟨208908, by rfl⟩ : syracuseStep 2228357 = 417817) (by norm_num)
theorem B1671313 : Blo 1484062 1671313 := bbase (se 2 (by rfl) ⟨626742, by rfl⟩ : syracuseStep 1671313 = 1253485) (by norm_num)
theorem B4227221 : Blo 1484062 4227221 := bbase (se 6 (by rfl) ⟨99075, by rfl⟩ : syracuseStep 4227221 = 198151) (by norm_num)
theorem B2506909 : Blo 1484062 2506909 := bbase (se 3 (by rfl) ⟨470045, by rfl⟩ : syracuseStep 2506909 = 940091) (by norm_num)
theorem B2228381 : Blo 1484062 2228381 := bbase (se 3 (by rfl) ⟨417821, by rfl⟩ : syracuseStep 2228381 = 835643) (by norm_num)
theorem B7135397 : Blo 1484062 7135397 := bbase (se 4 (by rfl) ⟨668943, by rfl⟩ : syracuseStep 7135397 = 1337887) (by norm_num)
theorem B3342509 : Blo 1484062 3342509 := bbase (se 3 (by rfl) ⟨626720, by rfl⟩ : syracuseStep 3342509 = 1253441) (by norm_num)
theorem B8028341 : Blo 1484062 8028341 := bbase (se 5 (by rfl) ⟨376328, by rfl⟩ : syracuseStep 8028341 = 752657) (by norm_num)
theorem B2228405 : Blo 1484062 2228405 := bbase (se 5 (by rfl) ⟨104456, by rfl⟩ : syracuseStep 2228405 = 208913) (by norm_num)
theorem B1671349 : Blo 1484062 1671349 := bbase (se 5 (by rfl) ⟨78344, by rfl⟩ : syracuseStep 1671349 = 156689) (by norm_num)
theorem B2818253 : Blo 1484062 2818253 := bbase (se 3 (by rfl) ⟨528422, by rfl⟩ : syracuseStep 2818253 = 1056845) (by norm_num)
theorem B2228429 : Blo 1484062 2228429 := bbase (se 3 (by rfl) ⟨417830, by rfl⟩ : syracuseStep 2228429 = 835661) (by norm_num)
theorem B1671385 : Blo 1484062 1671385 := bbase (se 2 (by rfl) ⟨626769, by rfl⟩ : syracuseStep 1671385 = 1253539) (by norm_num)
theorem B2859229 : Blo 1484062 2859229 := bbase (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) (by norm_num)
theorem B2228453 : Blo 1484062 2228453 := bbase (se 4 (by rfl) ⟨208917, by rfl⟩ : syracuseStep 2228453 = 417835) (by norm_num)
theorem B2113781 : Blo 1484062 2113781 := bbase (se 5 (by rfl) ⟨99083, by rfl⟩ : syracuseStep 2113781 = 198167) (by norm_num)
theorem B3342581 : Blo 1484062 3342581 := bbase (se 5 (by rfl) ⟨156683, by rfl⟩ : syracuseStep 3342581 = 313367) (by norm_num)
theorem B2506997 : Blo 1484062 2506997 := bbase (se 5 (by rfl) ⟨117515, by rfl⟩ : syracuseStep 2506997 = 235031) (by norm_num)
theorem B2228477 : Blo 1484062 2228477 := bbase (se 3 (by rfl) ⟨417839, by rfl⟩ : syracuseStep 2228477 = 835679) (by norm_num)
theorem B1671421 : Blo 1484062 1671421 := bbase (se 3 (by rfl) ⟨313391, by rfl⟩ : syracuseStep 1671421 = 626783) (by norm_num)
theorem B2228501 : Blo 1484062 2228501 := bbase (se 6 (by rfl) ⟨52230, by rfl⟩ : syracuseStep 2228501 = 104461) (by norm_num)
theorem B2859293 : Blo 1484062 2859293 := bbase (se 3 (by rfl) ⟨536117, by rfl⟩ : syracuseStep 2859293 = 1072235) (by norm_num)
theorem B1671457 : Blo 1484062 1671457 := bbase (se 2 (by rfl) ⟨626796, by rfl⟩ : syracuseStep 1671457 = 1253593) (by norm_num)
theorem B2228525 : Blo 1484062 2228525 := bbase (se 3 (by rfl) ⟨417848, by rfl⟩ : syracuseStep 2228525 = 835697) (by norm_num)
theorem B2007349 : Blo 1484062 2007349 := bbase (se 5 (by rfl) ⟨94094, by rfl⟩ : syracuseStep 2007349 = 188189) (by norm_num)
theorem B3760445 : Blo 1484062 3760445 := bbase (se 3 (by rfl) ⟨705083, by rfl⟩ : syracuseStep 3760445 = 1410167) (by norm_num)
theorem B3342653 : Blo 1484062 3342653 := bbase (se 3 (by rfl) ⟨626747, by rfl⟩ : syracuseStep 3342653 = 1253495) (by norm_num)
theorem B6340933 : Blo 1484062 6340933 := bbase (se 4 (by rfl) ⟨594462, by rfl⟩ : syracuseStep 6340933 = 1188925) (by norm_num)
theorem B2228549 : Blo 1484062 2228549 := bbase (se 4 (by rfl) ⟨208926, by rfl⟩ : syracuseStep 2228549 = 417853) (by norm_num)
theorem B1671493 : Blo 1484062 1671493 := bbase (se 4 (by rfl) ⟨156702, by rfl⟩ : syracuseStep 1671493 = 313405) (by norm_num)
theorem B5013845 : Blo 1484062 5013845 := bbase (se 10 (by rfl) ⟨7344, by rfl⟩ : syracuseStep 5013845 = 14689) (by norm_num)
theorem B2228573 : Blo 1484062 2228573 := bbase (se 3 (by rfl) ⟨417857, by rfl⟩ : syracuseStep 2228573 = 835715) (by norm_num)
theorem B2818405 : Blo 1484062 2818405 := bbase (se 4 (by rfl) ⟨264225, by rfl⟩ : syracuseStep 2818405 = 528451) (by norm_num)
theorem B7135589 : Blo 1484062 7135589 := bbase (se 4 (by rfl) ⟨668961, by rfl⟩ : syracuseStep 7135589 = 1337923) (by norm_num)
theorem B1671529 : Blo 1484062 1671529 := bbase (se 2 (by rfl) ⟨626823, by rfl⟩ : syracuseStep 1671529 = 1253647) (by norm_num)
theorem B2507125 : Blo 1484062 2507125 := bbase (se 5 (by rfl) ⟨117521, by rfl⟩ : syracuseStep 2507125 = 235043) (by norm_num)
theorem B2228597 : Blo 1484062 2228597 := bbase (se 5 (by rfl) ⟨104465, by rfl⟩ : syracuseStep 2228597 = 208931) (by norm_num)
theorem B4227461 : Blo 1484062 4227461 := bbase (se 4 (by rfl) ⟨396324, by rfl⟩ : syracuseStep 4227461 = 792649) (by norm_num)
theorem B3342725 : Blo 1484062 3342725 := bbase (se 4 (by rfl) ⟨313380, by rfl⟩ : syracuseStep 3342725 = 626761) (by norm_num)
theorem B2228621 : Blo 1484062 2228621 := bbase (se 3 (by rfl) ⟨417866, by rfl⟩ : syracuseStep 2228621 = 835733) (by norm_num)
theorem B1671565 : Blo 1484062 1671565 := bbase (se 3 (by rfl) ⟨313418, by rfl⟩ : syracuseStep 1671565 = 626837) (by norm_num)
theorem B2228645 : Blo 1484062 2228645 := bbase (se 4 (by rfl) ⟨208935, by rfl⟩ : syracuseStep 2228645 = 417871) (by norm_num)
theorem B1671601 : Blo 1484062 1671601 := bbase (se 2 (by rfl) ⟨626850, by rfl⟩ : syracuseStep 1671601 = 1253701) (by norm_num)
theorem B2228669 : Blo 1484062 2228669 := bbase (se 3 (by rfl) ⟨417875, by rfl⟩ : syracuseStep 2228669 = 835751) (by norm_num)
theorem B3342797 : Blo 1484062 3342797 := bbase (se 3 (by rfl) ⟨626774, by rfl⟩ : syracuseStep 3342797 = 1253549) (by norm_num)
theorem B2507213 : Blo 1484062 2507213 := bbase (se 3 (by rfl) ⟨470102, by rfl⟩ : syracuseStep 2507213 = 940205) (by norm_num)
theorem B2228693 : Blo 1484062 2228693 := bbase (se 7 (by rfl) ⟨26117, by rfl⟩ : syracuseStep 2228693 = 52235) (by norm_num)
theorem B1671637 : Blo 1484062 1671637 := bbase (se 7 (by rfl) ⟨19589, by rfl⟩ : syracuseStep 1671637 = 39179) (by norm_num)
theorem B2228717 : Blo 1484062 2228717 := bbase (se 3 (by rfl) ⟨417884, by rfl⟩ : syracuseStep 2228717 = 835769) (by norm_num)
theorem B1671673 : Blo 1484062 1671673 := bbase (se 2 (by rfl) ⟨626877, by rfl⟩ : syracuseStep 1671673 = 1253755) (by norm_num)
theorem B2228741 : Blo 1484062 2228741 := bbase (se 4 (by rfl) ⟨208944, by rfl⟩ : syracuseStep 2228741 = 417889) (by norm_num)
theorem B3342869 : Blo 1484062 3342869 := bbase (se 6 (by rfl) ⟨78348, by rfl⟩ : syracuseStep 3342869 = 156697) (by norm_num)
theorem B2228765 : Blo 1484062 2228765 := bbase (se 3 (by rfl) ⟨417893, by rfl⟩ : syracuseStep 2228765 = 835787) (by norm_num)
theorem B1671709 : Blo 1484062 1671709 := bbase (se 3 (by rfl) ⟨313445, by rfl⟩ : syracuseStep 1671709 = 626891) (by norm_num)
theorem B2228789 : Blo 1484062 2228789 := bbase (se 5 (by rfl) ⟨104474, by rfl⟩ : syracuseStep 2228789 = 208949) (by norm_num)
theorem B1671745 : Blo 1484062 1671745 := bbase (se 2 (by rfl) ⟨626904, by rfl⟩ : syracuseStep 1671745 = 1253809) (by norm_num)
theorem B4227653 : Blo 1484062 4227653 := bbase (se 4 (by rfl) ⟨396342, by rfl⟩ : syracuseStep 4227653 = 792685) (by norm_num)
theorem B2507341 : Blo 1484062 2507341 := bbase (se 3 (by rfl) ⟨470126, by rfl⟩ : syracuseStep 2507341 = 940253) (by norm_num)
theorem B2228813 : Blo 1484062 2228813 := bbase (se 3 (by rfl) ⟨417902, by rfl⟩ : syracuseStep 2228813 = 835805) (by norm_num)
theorem B3342941 : Blo 1484062 3342941 := bbase (se 3 (by rfl) ⟨626801, by rfl⟩ : syracuseStep 3342941 = 1253603) (by norm_num)
theorem B2228837 : Blo 1484062 2228837 := bbase (se 4 (by rfl) ⟨208953, by rfl⟩ : syracuseStep 2228837 = 417907) (by norm_num)
theorem B1671781 : Blo 1484062 1671781 := bbase (se 4 (by rfl) ⟨156729, by rfl⟩ : syracuseStep 1671781 = 313459) (by norm_num)
theorem B2228861 : Blo 1484062 2228861 := bbase (se 3 (by rfl) ⟨417911, by rfl⟩ : syracuseStep 2228861 = 835823) (by norm_num)
theorem B1671817 : Blo 1484062 1671817 := bbase (se 2 (by rfl) ⟨626931, by rfl⟩ : syracuseStep 1671817 = 1253863) (by norm_num)
theorem B2818709 : Blo 1484062 2818709 := bbase (se 6 (by rfl) ⟨66063, by rfl⟩ : syracuseStep 2818709 = 132127) (by norm_num)
theorem B3760789 : Blo 1484062 3760789 := bbase (se 6 (by rfl) ⟨88143, by rfl⟩ : syracuseStep 3760789 = 176287) (by norm_num)
theorem B2228885 : Blo 1484062 2228885 := bbase (se 6 (by rfl) ⟨52239, by rfl⟩ : syracuseStep 2228885 = 104479) (by norm_num)
theorem B3343013 : Blo 1484062 3343013 := bbase (se 4 (by rfl) ⟨313407, by rfl⟩ : syracuseStep 3343013 = 626815) (by norm_num)
theorem B2507429 : Blo 1484062 2507429 := bbase (se 4 (by rfl) ⟨235071, by rfl⟩ : syracuseStep 2507429 = 470143) (by norm_num)
theorem B2228909 : Blo 1484062 2228909 := bbase (se 3 (by rfl) ⟨417920, by rfl⟩ : syracuseStep 2228909 = 835841) (by norm_num)
theorem B2228933 : Blo 1484062 2228933 := bbase (se 4 (by rfl) ⟨208962, by rfl⟩ : syracuseStep 2228933 = 417925) (by norm_num)
theorem B2228957 : Blo 1484062 2228957 := bbase (se 3 (by rfl) ⟨417929, by rfl⟩ : syracuseStep 2228957 = 835859) (by norm_num)
theorem B3343085 : Blo 1484062 3343085 := bbase (se 3 (by rfl) ⟨626828, by rfl⟩ : syracuseStep 3343085 = 1253657) (by norm_num)
theorem B2228981 : Blo 1484062 2228981 := bbase (se 5 (by rfl) ⟨104483, by rfl⟩ : syracuseStep 2228981 = 208967) (by norm_num)
theorem B5014277 : Blo 1484062 5014277 := bbase (se 4 (by rfl) ⟨470088, by rfl⟩ : syracuseStep 5014277 = 940177) (by norm_num)
theorem B3760901 : Blo 1484062 3760901 := bbase (se 4 (by rfl) ⟨352584, by rfl⟩ : syracuseStep 3760901 = 705169) (by norm_num)
theorem B2229005 : Blo 1484062 2229005 := bbase (se 3 (by rfl) ⟨417938, by rfl⟩ : syracuseStep 2229005 = 835877) (by norm_num)
theorem B2507557 : Blo 1484062 2507557 := bbase (se 4 (by rfl) ⟨235083, by rfl⟩ : syracuseStep 2507557 = 470167) (by norm_num)
theorem B2229029 : Blo 1484062 2229029 := bbase (se 4 (by rfl) ⟨208971, by rfl⟩ : syracuseStep 2229029 = 417943) (by norm_num)
theorem B3343157 : Blo 1484062 3343157 := bbase (se 5 (by rfl) ⟨156710, by rfl⟩ : syracuseStep 3343157 = 313421) (by norm_num)
theorem B2229053 : Blo 1484062 2229053 := bbase (se 3 (by rfl) ⟨417947, by rfl⟩ : syracuseStep 2229053 = 835895) (by norm_num)
theorem B2229077 : Blo 1484062 2229077 := bbase (se 9 (by rfl) ⟨6530, by rfl⟩ : syracuseStep 2229077 = 13061) (by norm_num)
theorem B3343229 : Blo 1484062 3343229 := bbase (se 3 (by rfl) ⟨626855, by rfl⟩ : syracuseStep 3343229 = 1253711) (by norm_num)
theorem B2507645 : Blo 1484062 2507645 := bbase (se 3 (by rfl) ⟨470183, by rfl⟩ : syracuseStep 2507645 = 940367) (by norm_num)
theorem B7521173 : Blo 1484062 7521173 := bbase (se 6 (by rfl) ⟨176277, by rfl⟩ : syracuseStep 7521173 = 352555) (by norm_num)
theorem B3171253 : Blo 1484062 3171253 := bbase (se 5 (by rfl) ⟨148652, by rfl⟩ : syracuseStep 3171253 = 297305) (by norm_num)
theorem B3761093 : Blo 1484062 3761093 := bbase (se 4 (by rfl) ⟨352602, by rfl⟩ : syracuseStep 3761093 = 705205) (by norm_num)
theorem B3343301 : Blo 1484062 3343301 := bbase (se 4 (by rfl) ⟨313434, by rfl⟩ : syracuseStep 3343301 = 626869) (by norm_num)
theorem B2114533 : Blo 1484062 2114533 := bbase (se 4 (by rfl) ⟨198237, by rfl⟩ : syracuseStep 2114533 = 396475) (by norm_num)
theorem B3343373 : Blo 1484062 3343373 := bbase (se 3 (by rfl) ⟨626882, by rfl⟩ : syracuseStep 3343373 = 1253765) (by norm_num)
theorem B2090005 : Blo 1484062 2090005 := bbase (se 6 (by rfl) ⟨48984, by rfl⟩ : syracuseStep 2090005 = 97969) (by norm_num)
theorem B10298389 : Blo 1484062 10298389 := bbase (se 6 (by rfl) ⟨241368, by rfl⟩ : syracuseStep 10298389 = 482737) (by norm_num)
theorem B3343445 : Blo 1484062 3343445 := bbase (se 8 (by rfl) ⟨19590, by rfl⟩ : syracuseStep 3343445 = 39181) (by norm_num)
theorem B5637221 : Blo 1484062 5637221 := bbase (se 4 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 5637221 = 1056979) (by norm_num)
theorem B3343517 : Blo 1484062 3343517 := bbase (se 3 (by rfl) ⟨626909, by rfl⟩ : syracuseStep 3343517 = 1253819) (by norm_num)
theorem B5014709 : Blo 1484062 5014709 := bbase (se 5 (by rfl) ⟨235064, by rfl⟩ : syracuseStep 5014709 = 470129) (by norm_num)
theorem B2008253 : Blo 1484062 2008253 := bbase (se 3 (by rfl) ⟨376547, by rfl⟩ : syracuseStep 2008253 = 753095) (by norm_num)
theorem B3433693 : Blo 1484062 3433693 := bbase (se 3 (by rfl) ⟨643817, by rfl⟩ : syracuseStep 3433693 = 1287635) (by norm_num)
theorem B3343589 : Blo 1484062 3343589 := bbase (se 4 (by rfl) ⟨313461, by rfl⟩ : syracuseStep 3343589 = 626923) (by norm_num)
theorem B3761437 : Blo 1484062 3761437 := bbase (se 3 (by rfl) ⟨705269, by rfl⟩ : syracuseStep 3761437 = 1410539) (by norm_num)
theorem B3171629 : Blo 1484062 3171629 := bbase (se 3 (by rfl) ⟨594680, by rfl⟩ : syracuseStep 3171629 = 1189361) (by norm_num)
theorem B7513397 : Blo 1484062 7513397 := bbase (se 5 (by rfl) ⟨352190, by rfl⟩ : syracuseStep 7513397 = 704381) (by norm_num)
theorem B5637509 : Blo 1484062 5637509 := bbase (se 4 (by rfl) ⟨528516, by rfl⟩ : syracuseStep 5637509 = 1057033) (by norm_num)
theorem B2819461 : Blo 1484062 2819461 := bbase (se 4 (by rfl) ⟨264324, by rfl⟩ : syracuseStep 2819461 = 528649) (by norm_num)
theorem B3761549 : Blo 1484062 3761549 := bbase (se 3 (by rfl) ⟨705290, by rfl⟩ : syracuseStep 3761549 = 1410581) (by norm_num)
theorem B2819605 : Blo 1484062 2819605 := bbase (se 6 (by rfl) ⟨66084, by rfl⟩ : syracuseStep 2819605 = 132169) (by norm_num)
theorem B4228645 : Blo 1484062 4228645 := bbase (se 4 (by rfl) ⟨396435, by rfl⟩ : syracuseStep 4228645 = 792871) (by norm_num)
theorem B5015141 : Blo 1484062 5015141 := bbase (se 4 (by rfl) ⟨470169, by rfl⟩ : syracuseStep 5015141 = 940339) (by norm_num)
theorem B2033333 : Blo 1484062 2033333 := bbase (se 5 (by rfl) ⟨95312, by rfl⟩ : syracuseStep 2033333 = 190625) (by norm_num)
theorem B2819765 : Blo 1484062 2819765 := bbase (se 5 (by rfl) ⟨132176, by rfl⟩ : syracuseStep 2819765 = 264353) (by norm_num)
theorem B24094421 : Blo 1484062 24094421 := bbase (se 7 (by rfl) ⟨282356, by rfl⟩ : syracuseStep 24094421 = 564713) (by norm_num)
theorem B2541277 : Blo 1484062 2541277 := bbase (se 3 (by rfl) ⟨476489, by rfl⟩ : syracuseStep 2541277 = 952979) (by norm_num)
theorem B5080805 : Blo 1484062 5080805 := bbase (se 4 (by rfl) ⟨476325, by rfl⟩ : syracuseStep 5080805 = 952651) (by norm_num)
theorem B2115325 : Blo 1484062 2115325 := bbase (se 3 (by rfl) ⟨396623, by rfl⟩ : syracuseStep 2115325 = 793247) (by norm_num)
theorem B4286213 : Blo 1484062 4286213 := bbase (se 4 (by rfl) ⟨401832, by rfl⟩ : syracuseStep 4286213 = 803665) (by norm_num)
theorem B6342421 : Blo 1484062 6342421 := bbase (se 6 (by rfl) ⟨148650, by rfl⟩ : syracuseStep 6342421 = 297301) (by norm_num)
theorem B6342437 : Blo 1484062 6342437 := bbase (se 4 (by rfl) ⟨594603, by rfl⟩ : syracuseStep 6342437 = 1189207) (by norm_num)
theorem B4015909 : Blo 1484062 4015909 := bbase (se 4 (by rfl) ⟨376491, by rfl⟩ : syracuseStep 4015909 = 752983) (by norm_num)
theorem B2377517 : Blo 1484062 2377517 := bbase (se 3 (by rfl) ⟨445784, by rfl⟩ : syracuseStep 2377517 = 891569) (by norm_num)
theorem B2819909 : Blo 1484062 2819909 := bbase (se 4 (by rfl) ⟨264366, by rfl⟩ : syracuseStep 2819909 = 528733) (by norm_num)
theorem B12036053 : Blo 1484062 12036053 := bbase (se 7 (by rfl) ⟨141047, by rfl⟩ : syracuseStep 12036053 = 282095) (by norm_num)
theorem B2115661 : Blo 1484062 2115661 := bbase (se 3 (by rfl) ⟨396686, by rfl⟩ : syracuseStep 2115661 = 793373) (by norm_num)
theorem B4016213 : Blo 1484062 4016213 := bbase (se 8 (by rfl) ⟨23532, by rfl⟩ : syracuseStep 4016213 = 47065) (by norm_num)
theorem B2820197 : Blo 1484062 2820197 := bbase (se 4 (by rfl) ⟨264393, by rfl⟩ : syracuseStep 2820197 = 528787) (by norm_num)
theorem B8456309 : Blo 1484062 8456309 := bbase (se 5 (by rfl) ⟨396389, by rfl⟩ : syracuseStep 8456309 = 792779) (by norm_num)
theorem B7522469 : Blo 1484062 7522469 := bbase (se 4 (by rfl) ⟨705231, by rfl⟩ : syracuseStep 7522469 = 1410463) (by norm_num)
theorem B2820349 : Blo 1484062 2820349 := bbase (se 3 (by rfl) ⟨528815, by rfl⟩ : syracuseStep 2820349 = 1057631) (by norm_num)
theorem B3811589 : Blo 1484062 3811589 := bbase (se 4 (by rfl) ⟨357336, by rfl⟩ : syracuseStep 3811589 = 714673) (by norm_num)
theorem B1607945 : Blo 1484062 1607945 := bbase (se 2 (by rfl) ⟨602979, by rfl⟩ : syracuseStep 1607945 = 1205959) (by norm_num)
theorem B3565853 : Blo 1484062 3565853 := bbase (se 3 (by rfl) ⟨668597, by rfl⟩ : syracuseStep 3565853 = 1337195) (by norm_num)
theorem B2115877 : Blo 1484062 2115877 := bbase (se 4 (by rfl) ⟨198363, by rfl⟩ : syracuseStep 2115877 = 396727) (by norm_num)
theorem B6023477 : Blo 1484062 6023477 := bbase (se 5 (by rfl) ⟨282350, by rfl⟩ : syracuseStep 6023477 = 564701) (by norm_num)
theorem B1878329 : Blo 1484062 1878329 := bbase (se 2 (by rfl) ⟨704373, by rfl⟩ : syracuseStep 1878329 = 1408747) (by norm_num)
theorem B2378069 : Blo 1484062 2378069 := bbase (se 10 (by rfl) ⟨3483, by rfl⟩ : syracuseStep 2378069 = 6967) (by norm_num)
theorem B1878385 : Blo 1484062 1878385 := bbase (se 2 (by rfl) ⟨704394, by rfl⟩ : syracuseStep 1878385 = 1408789) (by norm_num)
theorem B2378101 : Blo 1484062 2378101 := bbase (se 5 (by rfl) ⟨111473, by rfl⟩ : syracuseStep 2378101 = 222947) (by norm_num)
theorem B3565949 : Blo 1484062 3565949 := bbase (se 3 (by rfl) ⟨668615, by rfl⟩ : syracuseStep 3565949 = 1337231) (by norm_num)
theorem B1878481 : Blo 1484062 1878481 := bbase (se 2 (by rfl) ⟨704430, by rfl⟩ : syracuseStep 1878481 = 1408861) (by norm_num)
theorem B2411021 : Blo 1484062 2411021 := bbase (se 3 (by rfl) ⟨452066, by rfl⟩ : syracuseStep 2411021 = 904133) (by norm_num)
theorem B5638693 : Blo 1484062 5638693 := bbase (se 4 (by rfl) ⟨528627, by rfl⟩ : syracuseStep 5638693 = 1057255) (by norm_num)
theorem B2820653 : Blo 1484062 2820653 := bbase (se 3 (by rfl) ⟨528872, by rfl⟩ : syracuseStep 2820653 = 1057745) (by norm_num)
theorem B7514693 : Blo 1484062 7514693 := bbase (se 4 (by rfl) ⟨704502, by rfl⟩ : syracuseStep 7514693 = 1409005) (by norm_num)
theorem B4229749 : Blo 1484062 4229749 := bbase (se 5 (by rfl) ⟨198269, by rfl⟩ : syracuseStep 4229749 = 396539) (by norm_num)
theorem B1878653 : Blo 1484062 1878653 := bbase (se 3 (by rfl) ⟨352247, by rfl⟩ : syracuseStep 1878653 = 704495) (by norm_num)
theorem B2714269 : Blo 1484062 2714269 := bbase (se 3 (by rfl) ⟨508925, by rfl⟩ : syracuseStep 2714269 = 1017851) (by norm_num)
theorem B1739441 : Blo 1484062 1739441 := bbase (se 2 (by rfl) ⟨652290, by rfl⟩ : syracuseStep 1739441 = 1304581) (by norm_num)
theorem B1878709 : Blo 1484062 1878709 := bbase (se 5 (by rfl) ⟨88064, by rfl⟩ : syracuseStep 1878709 = 176129) (by norm_num)
theorem B3386053 : Blo 1484062 3386053 := bbase (se 4 (by rfl) ⟨317442, by rfl⟩ : syracuseStep 3386053 = 634885) (by norm_num)
theorem B1878805 : Blo 1484062 1878805 := bbase (se 6 (by rfl) ⟨44034, by rfl⟩ : syracuseStep 1878805 = 88069) (by norm_num)
theorem B12684053 : Blo 1484062 12684053 := bbase (se 6 (by rfl) ⟨297282, by rfl⟩ : syracuseStep 12684053 = 594565) (by norm_num)
theorem B14273333 : Blo 1484062 14273333 := bbase (se 5 (by rfl) ⟨669062, by rfl⟩ : syracuseStep 14273333 = 1338125) (by norm_num)
theorem B4516661 : Blo 1484062 4516661 := bbase (se 5 (by rfl) ⟨211718, by rfl⟩ : syracuseStep 4516661 = 423437) (by norm_num)
theorem B5638997 : Blo 1484062 5638997 := bbase (se 9 (by rfl) ⟨16520, by rfl⟩ : syracuseStep 5638997 = 33041) (by norm_num)
theorem B4287365 : Blo 1484062 4287365 := bbase (se 4 (by rfl) ⟨401940, by rfl⟩ : syracuseStep 4287365 = 803881) (by norm_num)
theorem B3173269 : Blo 1484062 3173269 := bbase (se 6 (by rfl) ⟨74373, by rfl⟩ : syracuseStep 3173269 = 148747) (by norm_num)
theorem B1878977 : Blo 1484062 1878977 := bbase (se 2 (by rfl) ⟨704616, by rfl⟩ : syracuseStep 1878977 = 1409233) (by norm_num)
theorem B21408725 : Blo 1484062 21408725 := bbase (se 7 (by rfl) ⟨250883, by rfl⟩ : syracuseStep 21408725 = 501767) (by norm_num)
theorem B3050461 : Blo 1484062 3050461 := bbase (se 3 (by rfl) ⟨571961, by rfl⟩ : syracuseStep 3050461 = 1143923) (by norm_num)
theorem B1879033 : Blo 1484062 1879033 := bbase (se 2 (by rfl) ⟨704637, by rfl⟩ : syracuseStep 1879033 = 1409275) (by norm_num)
theorem B3009565 : Blo 1484062 3009565 := bbase (se 3 (by rfl) ⟨564293, by rfl⟩ : syracuseStep 3009565 = 1128587) (by norm_num)
theorem B1879129 : Blo 1484062 1879129 := bbase (se 2 (by rfl) ⟨704673, by rfl⟩ : syracuseStep 1879129 = 1409347) (by norm_num)
theorem B1879301 : Blo 1484062 1879301 := bbase (se 4 (by rfl) ⟨176184, by rfl⟩ : syracuseStep 1879301 = 352369) (by norm_num)
theorem B8457493 : Blo 1484062 8457493 := bbase (se 6 (by rfl) ⟨198222, by rfl⟩ : syracuseStep 8457493 = 396445) (by norm_num)
theorem B4640021 : Blo 1484062 4640021 := bbase (se 6 (by rfl) ⟨108750, by rfl⟩ : syracuseStep 4640021 = 217501) (by norm_num)
theorem B2379029 : Blo 1484062 2379029 := bbase (se 6 (by rfl) ⟨55758, by rfl⟩ : syracuseStep 2379029 = 111517) (by norm_num)
theorem B1879357 : Blo 1484062 1879357 := bbase (se 3 (by rfl) ⟨352379, by rfl⟩ : syracuseStep 1879357 = 704759) (by norm_num)
theorem B3386765 : Blo 1484062 3386765 := bbase (se 3 (by rfl) ⟨635018, by rfl⟩ : syracuseStep 3386765 = 1270037) (by norm_num)
theorem B1879453 : Blo 1484062 1879453 := bbase (se 3 (by rfl) ⟨352397, by rfl⟩ : syracuseStep 1879453 = 704795) (by norm_num)
theorem B4754933 : Blo 1484062 4754933 := bbase (se 5 (by rfl) ⟨222887, by rfl⟩ : syracuseStep 4754933 = 445775) (by norm_num)
theorem B4517365 : Blo 1484062 4517365 := bbase (se 5 (by rfl) ⟨211751, by rfl⟩ : syracuseStep 4517365 = 423503) (by norm_num)
theorem B1879625 : Blo 1484062 1879625 := bbase (se 2 (by rfl) ⟨704859, by rfl⟩ : syracuseStep 1879625 = 1409719) (by norm_num)
theorem B4517461 : Blo 1484062 4517461 := bbase (se 8 (by rfl) ⟨26469, by rfl⟩ : syracuseStep 4517461 = 52939) (by norm_num)
theorem B1879681 : Blo 1484062 1879681 := bbase (se 2 (by rfl) ⟨704880, by rfl⟩ : syracuseStep 1879681 = 1409761) (by norm_num)
theorem B3616397 : Blo 1484062 3616397 := bbase (se 3 (by rfl) ⟨678074, by rfl⟩ : syracuseStep 3616397 = 1356149) (by norm_num)
theorem B5009093 : Blo 1484062 5009093 := bbase (se 4 (by rfl) ⟨469602, by rfl⟩ : syracuseStep 5009093 = 939205) (by norm_num)
theorem B1879777 : Blo 1484062 1879777 := bbase (se 2 (by rfl) ⟨704916, by rfl⟩ : syracuseStep 1879777 = 1409833) (by norm_num)
theorem B2674405 : Blo 1484062 2674405 := bbase (se 4 (by rfl) ⟨250725, by rfl⟩ : syracuseStep 2674405 = 501451) (by norm_num)
theorem B7515989 : Blo 1484062 7515989 := bbase (se 9 (by rfl) ⟨22019, by rfl⟩ : syracuseStep 7515989 = 44039) (by norm_num)
theorem B1879949 : Blo 1484062 1879949 := bbase (se 3 (by rfl) ⟨352490, by rfl⟩ : syracuseStep 1879949 = 704981) (by norm_num)
theorem B2379709 : Blo 1484062 2379709 := bbase (se 3 (by rfl) ⟨446195, by rfl⟩ : syracuseStep 2379709 = 892391) (by norm_num)
theorem B1880005 : Blo 1484062 1880005 := bbase (se 4 (by rfl) ⟨176250, by rfl⟩ : syracuseStep 1880005 = 352501) (by norm_num)
theorem B6770645 : Blo 1484062 6770645 := bbase (se 7 (by rfl) ⟨79343, by rfl⟩ : syracuseStep 6770645 = 158687) (by norm_num)
theorem B6344693 : Blo 1484062 6344693 := bbase (se 5 (by rfl) ⟨297407, by rfl⟩ : syracuseStep 6344693 = 594815) (by norm_num)
theorem B2379773 : Blo 1484062 2379773 := bbase (se 3 (by rfl) ⟨446207, by rfl⟩ : syracuseStep 2379773 = 892415) (by norm_num)
theorem B1880101 : Blo 1484062 1880101 := bbase (se 4 (by rfl) ⟨176259, by rfl⟩ : syracuseStep 1880101 = 352519) (by norm_num)
theorem B10850357 : Blo 1484062 10850357 := bbase (se 5 (by rfl) ⟨508610, by rfl⟩ : syracuseStep 10850357 = 1017221) (by norm_num)
theorem B4231253 : Blo 1484062 4231253 := bbase (se 8 (by rfl) ⟨24792, by rfl⟩ : syracuseStep 4231253 = 49585) (by norm_num)
theorem B6107237 : Blo 1484062 6107237 := bbase (se 4 (by rfl) ⟨572553, by rfl⟩ : syracuseStep 6107237 = 1145107) (by norm_num)
theorem B5009525 : Blo 1484062 5009525 := bbase (se 5 (by rfl) ⟨234821, by rfl⟩ : syracuseStep 5009525 = 469643) (by norm_num)
theorem B3010765 : Blo 1484062 3010765 := bbase (se 3 (by rfl) ⟨564518, by rfl⟩ : syracuseStep 3010765 = 1129037) (by norm_num)
theorem B1880273 : Blo 1484062 1880273 := bbase (se 2 (by rfl) ⟨705102, by rfl⟩ : syracuseStep 1880273 = 1410205) (by norm_num)
theorem B1880329 : Blo 1484062 1880329 := bbase (se 2 (by rfl) ⟨705123, by rfl⟩ : syracuseStep 1880329 = 1410247) (by norm_num)
theorem B2937149 : Blo 1484062 2937149 := bbase (se 3 (by rfl) ⟨550715, by rfl⟩ : syracuseStep 2937149 = 1101431) (by norm_num)
theorem B1880425 : Blo 1484062 1880425 := bbase (se 2 (by rfl) ⟨705159, by rfl⟩ : syracuseStep 1880425 = 1410319) (by norm_num)
theorem B4755829 : Blo 1484062 4755829 := bbase (se 5 (by rfl) ⟨222929, by rfl⟩ : syracuseStep 4755829 = 445859) (by norm_num)
theorem B7139701 : Blo 1484062 7139701 := bbase (se 5 (by rfl) ⟨334673, by rfl⟩ : syracuseStep 7139701 = 669347) (by norm_num)
theorem B1585541 : Blo 1484062 1585541 := bbase (se 4 (by rfl) ⟨148644, by rfl⟩ : syracuseStep 1585541 = 297289) (by norm_num)
theorem B3568045 : Blo 1484062 3568045 := bbase (se 3 (by rfl) ⟨669008, by rfl⟩ : syracuseStep 3568045 = 1338017) (by norm_num)
theorem B3756557 : Blo 1484062 3756557 := bbase (se 3 (by rfl) ⟨704354, by rfl⟩ : syracuseStep 3756557 = 1408709) (by norm_num)
theorem B1880597 : Blo 1484062 1880597 := bbase (se 6 (by rfl) ⟨44076, by rfl⟩ : syracuseStep 1880597 = 88153) (by norm_num)
theorem B5009957 : Blo 1484062 5009957 := bbase (se 4 (by rfl) ⟨469683, by rfl⟩ : syracuseStep 5009957 = 939367) (by norm_num)
theorem B1880653 : Blo 1484062 1880653 := bbase (se 3 (by rfl) ⟨352622, by rfl⟩ : syracuseStep 1880653 = 705245) (by norm_num)
theorem B1880749 : Blo 1484062 1880749 := bbase (se 3 (by rfl) ⟨352640, by rfl⟩ : syracuseStep 1880749 = 705281) (by norm_num)
theorem B4575989 : Blo 1484062 4575989 := bbase (se 5 (by rfl) ⟨214499, by rfl⟩ : syracuseStep 4575989 = 428999) (by norm_num)
theorem B1692461 : Blo 1484062 1692461 := bbase (se 3 (by rfl) ⟨317336, by rfl⟩ : syracuseStep 1692461 = 634673) (by norm_num)
theorem B2675501 : Blo 1484062 2675501 := bbase (se 3 (by rfl) ⟨501656, by rfl⟩ : syracuseStep 2675501 = 1003313) (by norm_num)
theorem B2544437 : Blo 1484062 2544437 := bbase (se 5 (by rfl) ⟨119270, by rfl⟩ : syracuseStep 2544437 = 238541) (by norm_num)
theorem B1585985 : Blo 1484062 1585985 := bbase (se 2 (by rfl) ⟨594744, by rfl⟩ : syracuseStep 1585985 = 1189489) (by norm_num)
theorem B3011413 : Blo 1484062 3011413 := bbase (se 9 (by rfl) ⟨8822, by rfl⟩ : syracuseStep 3011413 = 17645) (by norm_num)
theorem B3756901 : Blo 1484062 3756901 := bbase (se 4 (by rfl) ⟨352209, by rfl⟩ : syracuseStep 3756901 = 704419) (by norm_num)
theorem B5641109 : Blo 1484062 5641109 := bbase (se 6 (by rfl) ⟨132213, by rfl⟩ : syracuseStep 5641109 = 264427) (by norm_num)
theorem B3339197 : Blo 1484062 3339197 := bbase (se 3 (by rfl) ⟨626099, by rfl⟩ : syracuseStep 3339197 = 1252199) (by norm_num)
theorem B3757013 : Blo 1484062 3757013 := bbase (se 7 (by rfl) ⟨44027, by rfl⟩ : syracuseStep 3757013 = 88055) (by norm_num)
theorem B5010389 : Blo 1484062 5010389 := bbase (se 7 (by rfl) ⟨58715, by rfl⟩ : syracuseStep 5010389 = 117431) (by norm_num)
theorem B3339269 : Blo 1484062 3339269 := bbase (se 4 (by rfl) ⟨313056, by rfl⟩ : syracuseStep 3339269 = 626113) (by norm_num)
theorem B3568661 : Blo 1484062 3568661 := bbase (se 6 (by rfl) ⟨83640, by rfl⟩ : syracuseStep 3568661 = 167281) (by norm_num)
theorem B1586233 : Blo 1484062 1586233 := bbase (se 2 (by rfl) ⟨594837, by rfl⟩ : syracuseStep 1586233 = 1189675) (by norm_num)
theorem B3339341 : Blo 1484062 3339341 := bbase (se 3 (by rfl) ⟨626126, by rfl⟩ : syracuseStep 3339341 = 1252253) (by norm_num)
theorem B7517285 : Blo 1484062 7517285 := bbase (se 4 (by rfl) ⟨704745, by rfl⟩ : syracuseStep 7517285 = 1409491) (by norm_num)
theorem B3339413 : Blo 1484062 3339413 := bbase (se 6 (by rfl) ⟨78267, by rfl⟩ : syracuseStep 3339413 = 156535) (by norm_num)
theorem B3757205 : Blo 1484062 3757205 := bbase (se 6 (by rfl) ⟨88059, by rfl⟩ : syracuseStep 3757205 = 176119) (by norm_num)
theorem B5641397 : Blo 1484062 5641397 := bbase (se 5 (by rfl) ⟨264440, by rfl⟩ : syracuseStep 5641397 = 528881) (by norm_num)
theorem B5354693 : Blo 1484062 5354693 := bbase (se 4 (by rfl) ⟨502002, by rfl⟩ : syracuseStep 5354693 = 1004005) (by norm_num)
theorem B8459477 : Blo 1484062 8459477 := bbase (se 7 (by rfl) ⟨99134, by rfl⟩ : syracuseStep 8459477 = 198269) (by norm_num)
theorem B3339485 : Blo 1484062 3339485 := bbase (se 3 (by rfl) ⟨626153, by rfl⟩ : syracuseStep 3339485 = 1252307) (by norm_num)
theorem B3339557 : Blo 1484062 3339557 := bbase (se 4 (by rfl) ⟨313083, by rfl⟩ : syracuseStep 3339557 = 626167) (by norm_num)
theorem B1783129 : Blo 1484062 1783129 := bbase (se 2 (by rfl) ⟨668673, by rfl⟩ : syracuseStep 1783129 = 1337347) (by norm_num)
theorem B3568997 : Blo 1484062 3568997 := bbase (se 4 (by rfl) ⟨334593, by rfl⟩ : syracuseStep 3568997 = 669187) (by norm_num)
theorem B3339629 : Blo 1484062 3339629 := bbase (se 3 (by rfl) ⟨626180, by rfl⟩ : syracuseStep 3339629 = 1252361) (by norm_num)
theorem B5010821 : Blo 1484062 5010821 := bbase (se 4 (by rfl) ⟨469764, by rfl⟩ : syracuseStep 5010821 = 939529) (by norm_num)
theorem B3339701 : Blo 1484062 3339701 := bbase (se 5 (by rfl) ⟨156548, by rfl⟩ : syracuseStep 3339701 = 313097) (by norm_num)
theorem B6018533 : Blo 1484062 6018533 := bbase (se 4 (by rfl) ⟨564237, by rfl⟩ : syracuseStep 6018533 = 1128475) (by norm_num)
theorem B1586665 : Blo 1484062 1586665 := bbase (se 2 (by rfl) ⟨594999, by rfl⟩ : syracuseStep 1586665 = 1189999) (by norm_num)
theorem B3757549 : Blo 1484062 3757549 := bbase (se 3 (by rfl) ⟨704540, by rfl⟩ : syracuseStep 3757549 = 1409081) (by norm_num)
theorem B3339773 : Blo 1484062 3339773 := bbase (se 3 (by rfl) ⟨626207, by rfl⟩ : syracuseStep 3339773 = 1252415) (by norm_num)
theorem B1783345 : Blo 1484062 1783345 := bbase (se 2 (by rfl) ⟨668754, by rfl⟩ : syracuseStep 1783345 = 1337509) (by norm_num)
theorem B1586737 : Blo 1484062 1586737 := bbase (se 2 (by rfl) ⟨595026, by rfl⟩ : syracuseStep 1586737 = 1190053) (by norm_num)
theorem B3339845 : Blo 1484062 3339845 := bbase (se 4 (by rfl) ⟨313110, by rfl⟩ : syracuseStep 3339845 = 626221) (by norm_num)
theorem B9516629 : Blo 1484062 9516629 := bbase (se 8 (by rfl) ⟨55761, by rfl⟩ : syracuseStep 9516629 = 111523) (by norm_num)
theorem B3757661 : Blo 1484062 3757661 := bbase (se 3 (by rfl) ⟨704561, by rfl⟩ : syracuseStep 3757661 = 1409123) (by norm_num)
theorem B5355109 : Blo 1484062 5355109 := bbase (se 4 (by rfl) ⟨502041, by rfl⟩ : syracuseStep 5355109 = 1004083) (by norm_num)
theorem B3339917 : Blo 1484062 3339917 := bbase (se 3 (by rfl) ⟨626234, by rfl⟩ : syracuseStep 3339917 = 1252469) (by norm_num)
theorem B12687029 : Blo 1484062 12687029 := bbase (se 5 (by rfl) ⟨594704, by rfl⟩ : syracuseStep 12687029 = 1189409) (by norm_num)
theorem B2504405 : Blo 1484062 2504405 := bbase (se 7 (by rfl) ⟨29348, by rfl⟩ : syracuseStep 2504405 = 58697) (by norm_num)
theorem B3339989 : Blo 1484062 3339989 := bbase (se 7 (by rfl) ⟨39140, by rfl⟩ : syracuseStep 3339989 = 78281) (by norm_num)
theorem B3569389 : Blo 1484062 3569389 := bbase (se 3 (by rfl) ⟨669260, by rfl⟩ : syracuseStep 3569389 = 1338521) (by norm_num)
theorem B3340061 : Blo 1484062 3340061 := bbase (se 3 (by rfl) ⟨626261, by rfl⟩ : syracuseStep 3340061 = 1252523) (by norm_num)
theorem B3757853 : Blo 1484062 3757853 := bbase (se 3 (by rfl) ⟨704597, by rfl⟩ : syracuseStep 3757853 = 1409195) (by norm_num)
theorem B5011253 : Blo 1484062 5011253 := bbase (se 5 (by rfl) ⟨234902, by rfl⟩ : syracuseStep 5011253 = 469805) (by norm_num)
theorem B2504533 : Blo 1484062 2504533 := bbase (se 9 (by rfl) ⟨7337, by rfl⟩ : syracuseStep 2504533 = 14675) (by norm_num)
theorem B3340133 : Blo 1484062 3340133 := bbase (se 4 (by rfl) ⟨313137, by rfl⟩ : syracuseStep 3340133 = 626275) (by norm_num)
theorem B1783657 : Blo 1484062 1783657 := bbase (se 2 (by rfl) ⟨668871, by rfl⟩ : syracuseStep 1783657 = 1337743) (by norm_num)
theorem B3012509 : Blo 1484062 3012509 := bbase (se 3 (by rfl) ⟨564845, by rfl⟩ : syracuseStep 3012509 = 1129691) (by norm_num)
theorem B2504621 : Blo 1484062 2504621 := bbase (se 3 (by rfl) ⟨469616, by rfl⟩ : syracuseStep 2504621 = 939233) (by norm_num)
theorem B3340205 : Blo 1484062 3340205 := bbase (se 3 (by rfl) ⟨626288, by rfl⟩ : syracuseStep 3340205 = 1252577) (by norm_num)
theorem B2226101 : Blo 1484062 2226101 := bbase (se 5 (by rfl) ⟨104348, by rfl⟩ : syracuseStep 2226101 = 208697) (by norm_num)
theorem B2226125 : Blo 1484062 2226125 := bbase (se 3 (by rfl) ⟨417398, by rfl⟩ : syracuseStep 2226125 = 834797) (by norm_num)
theorem B2226149 : Blo 1484062 2226149 := bbase (se 4 (by rfl) ⟨208701, by rfl⟩ : syracuseStep 2226149 = 417403) (by norm_num)
theorem B3340277 : Blo 1484062 3340277 := bbase (se 5 (by rfl) ⟨156575, by rfl⟩ : syracuseStep 3340277 = 313151) (by norm_num)
theorem B2226173 : Blo 1484062 2226173 := bbase (se 3 (by rfl) ⟨417407, by rfl⟩ : syracuseStep 2226173 = 834815) (by norm_num)
theorem B2226197 : Blo 1484062 2226197 := bbase (se 6 (by rfl) ⟨52176, by rfl⟩ : syracuseStep 2226197 = 104353) (by norm_num)
theorem B2226221 : Blo 1484062 2226221 := bbase (se 3 (by rfl) ⟨417416, by rfl⟩ : syracuseStep 2226221 = 834833) (by norm_num)
theorem B2504749 : Blo 1484062 2504749 := bbase (se 3 (by rfl) ⟨469640, by rfl⟩ : syracuseStep 2504749 = 939281) (by norm_num)
theorem B2857013 : Blo 1484062 2857013 := bbase (se 5 (by rfl) ⟨133922, by rfl⟩ : syracuseStep 2857013 = 267845) (by norm_num)
theorem B3340349 : Blo 1484062 3340349 := bbase (se 3 (by rfl) ⟨626315, by rfl⟩ : syracuseStep 3340349 = 1252631) (by norm_num)
theorem B2226245 : Blo 1484062 2226245 := bbase (se 4 (by rfl) ⟨208710, by rfl⟩ : syracuseStep 2226245 = 417421) (by norm_num)
theorem B2226269 : Blo 1484062 2226269 := bbase (se 3 (by rfl) ⟨417425, by rfl⟩ : syracuseStep 2226269 = 834851) (by norm_num)
theorem B2226293 : Blo 1484062 2226293 := bbase (se 5 (by rfl) ⟨104357, by rfl⟩ : syracuseStep 2226293 = 208715) (by norm_num)
theorem B3758197 : Blo 1484062 3758197 := bbase (se 5 (by rfl) ⟨176165, by rfl⟩ : syracuseStep 3758197 = 352331) (by norm_num)
theorem B2504837 : Blo 1484062 2504837 := bbase (se 4 (by rfl) ⟨234828, by rfl⟩ : syracuseStep 2504837 = 469657) (by norm_num)
theorem B3340421 : Blo 1484062 3340421 := bbase (se 4 (by rfl) ⟨313164, by rfl⟩ : syracuseStep 3340421 = 626329) (by norm_num)
theorem B2226317 : Blo 1484062 2226317 := bbase (se 3 (by rfl) ⟨417434, by rfl⟩ : syracuseStep 2226317 = 834869) (by norm_num)
theorem B2226341 : Blo 1484062 2226341 := bbase (se 4 (by rfl) ⟨208719, by rfl⟩ : syracuseStep 2226341 = 417439) (by norm_num)
theorem B2226365 : Blo 1484062 2226365 := bbase (se 3 (by rfl) ⟨417443, by rfl⟩ : syracuseStep 2226365 = 834887) (by norm_num)
theorem B3340493 : Blo 1484062 3340493 := bbase (se 3 (by rfl) ⟨626342, by rfl⟩ : syracuseStep 3340493 = 1252685) (by norm_num)
theorem B2226389 : Blo 1484062 2226389 := bbase (se 7 (by rfl) ⟨26090, by rfl⟩ : syracuseStep 2226389 = 52181) (by norm_num)
theorem B3758309 : Blo 1484062 3758309 := bbase (se 4 (by rfl) ⟨352341, by rfl⟩ : syracuseStep 3758309 = 704683) (by norm_num)
theorem B5011685 : Blo 1484062 5011685 := bbase (se 4 (by rfl) ⟨469845, by rfl⟩ : syracuseStep 5011685 = 939691) (by norm_num)
theorem B2226413 : Blo 1484062 2226413 := bbase (se 3 (by rfl) ⟨417452, by rfl⟩ : syracuseStep 2226413 = 834905) (by norm_num)
theorem B2226437 : Blo 1484062 2226437 := bbase (se 4 (by rfl) ⟨208728, by rfl⟩ : syracuseStep 2226437 = 417457) (by norm_num)
theorem B2504965 : Blo 1484062 2504965 := bbase (se 4 (by rfl) ⟨234840, by rfl⟩ : syracuseStep 2504965 = 469681) (by norm_num)
theorem B1693957 : Blo 1484062 1693957 := bbase (se 4 (by rfl) ⟨158808, by rfl⟩ : syracuseStep 1693957 = 317617) (by norm_num)
theorem B3340565 : Blo 1484062 3340565 := bbase (se 6 (by rfl) ⟨78294, by rfl⟩ : syracuseStep 3340565 = 156589) (by norm_num)
theorem B2226461 : Blo 1484062 2226461 := bbase (se 3 (by rfl) ⟨417461, by rfl⟩ : syracuseStep 2226461 = 834923) (by norm_num)
theorem B2857253 : Blo 1484062 2857253 := bbase (se 4 (by rfl) ⟨267867, by rfl⟩ : syracuseStep 2857253 = 535735) (by norm_num)
theorem B2226485 : Blo 1484062 2226485 := bbase (se 5 (by rfl) ⟨104366, by rfl⟩ : syracuseStep 2226485 = 208733) (by norm_num)
theorem B5355845 : Blo 1484062 5355845 := bbase (se 4 (by rfl) ⟨502110, by rfl⟩ : syracuseStep 5355845 = 1004221) (by norm_num)
theorem B2226509 : Blo 1484062 2226509 := bbase (se 3 (by rfl) ⟨417470, by rfl⟩ : syracuseStep 2226509 = 834941) (by norm_num)
theorem B13031765 : Blo 1484062 13031765 := bbase (se 10 (by rfl) ⟨19089, by rfl⟩ : syracuseStep 13031765 = 38179) (by norm_num)
theorem B2505053 : Blo 1484062 2505053 := bbase (se 3 (by rfl) ⟨469697, by rfl⟩ : syracuseStep 2505053 = 939395) (by norm_num)
theorem B3340637 : Blo 1484062 3340637 := bbase (se 3 (by rfl) ⟨626369, by rfl⟩ : syracuseStep 3340637 = 1252739) (by norm_num)
theorem B2226533 : Blo 1484062 2226533 := bbase (se 4 (by rfl) ⟨208737, by rfl⟩ : syracuseStep 2226533 = 417475) (by norm_num)
theorem B2677093 : Blo 1484062 2677093 := bbase (se 4 (by rfl) ⟨250977, by rfl⟩ : syracuseStep 2677093 = 501955) (by norm_num)
theorem B7518581 : Blo 1484062 7518581 := bbase (se 5 (by rfl) ⟨352433, by rfl⟩ : syracuseStep 7518581 = 704867) (by norm_num)
theorem B2226557 : Blo 1484062 2226557 := bbase (se 3 (by rfl) ⟨417479, by rfl⟩ : syracuseStep 2226557 = 834959) (by norm_num)
theorem B2226581 : Blo 1484062 2226581 := bbase (se 6 (by rfl) ⟨52185, by rfl⟩ : syracuseStep 2226581 = 104371) (by norm_num)
theorem B24099221 : Blo 1484062 24099221 := bbase (se 6 (by rfl) ⟨564825, by rfl⟩ : syracuseStep 24099221 = 1129651) (by norm_num)
theorem B3340709 : Blo 1484062 3340709 := bbase (se 4 (by rfl) ⟨313191, by rfl⟩ : syracuseStep 3340709 = 626383) (by norm_num)
theorem B3758501 : Blo 1484062 3758501 := bbase (se 4 (by rfl) ⟨352359, by rfl⟩ : syracuseStep 3758501 = 704719) (by norm_num)
theorem B2226605 : Blo 1484062 2226605 := bbase (se 3 (by rfl) ⟨417488, by rfl⟩ : syracuseStep 2226605 = 834977) (by norm_num)
theorem B6863285 : Blo 1484062 6863285 := bbase (se 5 (by rfl) ⟨321716, by rfl⟩ : syracuseStep 6863285 = 643433) (by norm_num)
theorem B2226629 : Blo 1484062 2226629 := bbase (se 4 (by rfl) ⟨208746, by rfl⟩ : syracuseStep 2226629 = 417493) (by norm_num)
theorem B1669585 : Blo 1484062 1669585 := bbase (se 2 (by rfl) ⟨626094, by rfl⟩ : syracuseStep 1669585 = 1252189) (by norm_num)
theorem B2226653 : Blo 1484062 2226653 := bbase (se 3 (by rfl) ⟨417497, by rfl⟩ : syracuseStep 2226653 = 834995) (by norm_num)
theorem B2505181 : Blo 1484062 2505181 := bbase (se 3 (by rfl) ⟨469721, by rfl⟩ : syracuseStep 2505181 = 939443) (by norm_num)
theorem B3340781 : Blo 1484062 3340781 := bbase (se 3 (by rfl) ⟨626396, by rfl⟩ : syracuseStep 3340781 = 1252793) (by norm_num)
theorem B1669621 : Blo 1484062 1669621 := bbase (se 5 (by rfl) ⟨78263, by rfl⟩ : syracuseStep 1669621 = 156527) (by norm_num)
theorem B2226677 : Blo 1484062 2226677 := bbase (se 5 (by rfl) ⟨104375, by rfl⟩ : syracuseStep 2226677 = 208751) (by norm_num)
theorem B2226701 : Blo 1484062 2226701 := bbase (se 3 (by rfl) ⟨417506, by rfl⟩ : syracuseStep 2226701 = 835013) (by norm_num)
theorem B1669657 : Blo 1484062 1669657 := bbase (se 2 (by rfl) ⟨626121, by rfl⟩ : syracuseStep 1669657 = 1252243) (by norm_num)
theorem B2226725 : Blo 1484062 2226725 := bbase (se 4 (by rfl) ⟨208755, by rfl⟩ : syracuseStep 2226725 = 417511) (by norm_num)
theorem B1505833 : Blo 1484062 1505833 := bbase (se 2 (by rfl) ⟨564687, by rfl⟩ : syracuseStep 1505833 = 1129375) (by norm_num)
theorem B2505269 : Blo 1484062 2505269 := bbase (se 5 (by rfl) ⟨117434, by rfl⟩ : syracuseStep 2505269 = 234869) (by norm_num)
theorem B3340853 : Blo 1484062 3340853 := bbase (se 5 (by rfl) ⟨156602, by rfl⟩ : syracuseStep 3340853 = 313205) (by norm_num)
theorem B1669693 : Blo 1484062 1669693 := bbase (se 3 (by rfl) ⟨313067, by rfl⟩ : syracuseStep 1669693 = 626135) (by norm_num)
theorem B2226749 : Blo 1484062 2226749 := bbase (se 3 (by rfl) ⟨417515, by rfl⟩ : syracuseStep 2226749 = 835031) (by norm_num)
theorem B2226773 : Blo 1484062 2226773 := bbase (se 8 (by rfl) ⟨13047, by rfl⟩ : syracuseStep 2226773 = 26095) (by norm_num)
theorem B1669729 : Blo 1484062 1669729 := bbase (se 2 (by rfl) ⟨626148, by rfl⟩ : syracuseStep 1669729 = 1252297) (by norm_num)
theorem B2226797 : Blo 1484062 2226797 := bbase (se 3 (by rfl) ⟨417524, by rfl⟩ : syracuseStep 2226797 = 835049) (by norm_num)
theorem B3340925 : Blo 1484062 3340925 := bbase (se 3 (by rfl) ⟨626423, by rfl⟩ : syracuseStep 3340925 = 1252847) (by norm_num)
theorem B1669765 : Blo 1484062 1669765 := bbase (se 4 (by rfl) ⟨156540, by rfl⟩ : syracuseStep 1669765 = 313081) (by norm_num)
theorem B2226821 : Blo 1484062 2226821 := bbase (se 4 (by rfl) ⟨208764, by rfl⟩ : syracuseStep 2226821 = 417529) (by norm_num)
theorem B5012117 : Blo 1484062 5012117 := bbase (se 6 (by rfl) ⟨117471, by rfl⟩ : syracuseStep 5012117 = 234943) (by norm_num)
theorem B8575637 : Blo 1484062 8575637 := bbase (se 6 (by rfl) ⟨200991, by rfl⟩ : syracuseStep 8575637 = 401983) (by norm_num)
theorem B2226845 : Blo 1484062 2226845 := bbase (se 3 (by rfl) ⟨417533, by rfl⟩ : syracuseStep 2226845 = 835067) (by norm_num)
theorem B1669801 : Blo 1484062 1669801 := bbase (se 2 (by rfl) ⟨626175, by rfl⟩ : syracuseStep 1669801 = 1252351) (by norm_num)
theorem B2226869 : Blo 1484062 2226869 := bbase (se 5 (by rfl) ⟨104384, by rfl⟩ : syracuseStep 2226869 = 208769) (by norm_num)
theorem B2505397 : Blo 1484062 2505397 := bbase (se 5 (by rfl) ⟨117440, by rfl⟩ : syracuseStep 2505397 = 234881) (by norm_num)
theorem B3340997 : Blo 1484062 3340997 := bbase (se 4 (by rfl) ⟨313218, by rfl⟩ : syracuseStep 3340997 = 626437) (by norm_num)
theorem B1669837 : Blo 1484062 1669837 := bbase (se 3 (by rfl) ⟨313094, by rfl⟩ : syracuseStep 1669837 = 626189) (by norm_num)
theorem B2226893 : Blo 1484062 2226893 := bbase (se 3 (by rfl) ⟨417542, by rfl⟩ : syracuseStep 2226893 = 835085) (by norm_num)
theorem B2226917 : Blo 1484062 2226917 := bbase (se 4 (by rfl) ⟨208773, by rfl⟩ : syracuseStep 2226917 = 417547) (by norm_num)
theorem B1669873 : Blo 1484062 1669873 := bbase (se 2 (by rfl) ⟨626202, by rfl⟩ : syracuseStep 1669873 = 1252405) (by norm_num)
theorem B5634805 : Blo 1484062 5634805 := bbase (se 5 (by rfl) ⟨264131, by rfl⟩ : syracuseStep 5634805 = 528263) (by norm_num)
theorem B2226941 : Blo 1484062 2226941 := bbase (se 3 (by rfl) ⟨417551, by rfl⟩ : syracuseStep 2226941 = 835103) (by norm_num)
theorem B3758845 : Blo 1484062 3758845 := bbase (se 3 (by rfl) ⟨704783, by rfl⟩ : syracuseStep 3758845 = 1409567) (by norm_num)
theorem B7625477 : Blo 1484062 7625477 := bbase (se 4 (by rfl) ⟨714888, by rfl⟩ : syracuseStep 7625477 = 1429777) (by norm_num)
theorem B2505485 : Blo 1484062 2505485 := bbase (se 3 (by rfl) ⟨469778, by rfl⟩ : syracuseStep 2505485 = 939557) (by norm_num)
theorem B3341069 : Blo 1484062 3341069 := bbase (se 3 (by rfl) ⟨626450, by rfl⟩ : syracuseStep 3341069 = 1252901) (by norm_num)
theorem B1669909 : Blo 1484062 1669909 := bbase (se 6 (by rfl) ⟨39138, by rfl⟩ : syracuseStep 1669909 = 78277) (by norm_num)
theorem B2226965 : Blo 1484062 2226965 := bbase (se 6 (by rfl) ⟨52194, by rfl⟩ : syracuseStep 2226965 = 104389) (by norm_num)
theorem B2226989 : Blo 1484062 2226989 := bbase (se 3 (by rfl) ⟨417560, by rfl⟩ : syracuseStep 2226989 = 835121) (by norm_num)
theorem B1669945 : Blo 1484062 1669945 := bbase (se 2 (by rfl) ⟨626229, by rfl⟩ : syracuseStep 1669945 = 1252459) (by norm_num)
theorem B2227013 : Blo 1484062 2227013 := bbase (se 4 (by rfl) ⟨208782, by rfl⟩ : syracuseStep 2227013 = 417565) (by norm_num)
theorem B3341141 : Blo 1484062 3341141 := bbase (se 9 (by rfl) ⟨9788, by rfl⟩ : syracuseStep 3341141 = 19577) (by norm_num)
theorem B1669981 : Blo 1484062 1669981 := bbase (se 3 (by rfl) ⟨313121, by rfl⟩ : syracuseStep 1669981 = 626243) (by norm_num)
theorem B2227037 : Blo 1484062 2227037 := bbase (se 3 (by rfl) ⟨417569, by rfl⟩ : syracuseStep 2227037 = 835139) (by norm_num)
theorem B3758957 : Blo 1484062 3758957 := bbase (se 3 (by rfl) ⟨704804, by rfl⟩ : syracuseStep 3758957 = 1409609) (by norm_num)
theorem B2227061 : Blo 1484062 2227061 := bbase (se 5 (by rfl) ⟨104393, by rfl⟩ : syracuseStep 2227061 = 208787) (by norm_num)
theorem B1670017 : Blo 1484062 1670017 := bbase (se 2 (by rfl) ⟨626256, by rfl⟩ : syracuseStep 1670017 = 1252513) (by norm_num)
theorem B2227085 : Blo 1484062 2227085 := bbase (se 3 (by rfl) ⟨417578, by rfl⟩ : syracuseStep 2227085 = 835157) (by norm_num)
theorem B2505613 : Blo 1484062 2505613 := bbase (se 3 (by rfl) ⟨469802, by rfl⟩ : syracuseStep 2505613 = 939605) (by norm_num)
theorem B3341213 : Blo 1484062 3341213 := bbase (se 3 (by rfl) ⟨626477, by rfl⟩ : syracuseStep 3341213 = 1252955) (by norm_num)
theorem B1670053 : Blo 1484062 1670053 := bbase (se 4 (by rfl) ⟨156567, by rfl⟩ : syracuseStep 1670053 = 313135) (by norm_num)
theorem B2227109 : Blo 1484062 2227109 := bbase (se 4 (by rfl) ⟨208791, by rfl⟩ : syracuseStep 2227109 = 417583) (by norm_num)
theorem B2227133 : Blo 1484062 2227133 := bbase (se 3 (by rfl) ⟨417587, by rfl⟩ : syracuseStep 2227133 = 835175) (by norm_num)
theorem B1670089 : Blo 1484062 1670089 := bbase (se 2 (by rfl) ⟨626283, by rfl⟩ : syracuseStep 1670089 = 1252567) (by norm_num)
theorem B2227157 : Blo 1484062 2227157 := bbase (se 7 (by rfl) ⟨26099, by rfl⟩ : syracuseStep 2227157 = 52199) (by norm_num)
theorem B2505701 : Blo 1484062 2505701 := bbase (se 4 (by rfl) ⟨234909, by rfl⟩ : syracuseStep 2505701 = 469819) (by norm_num)
theorem B3341285 : Blo 1484062 3341285 := bbase (se 4 (by rfl) ⟨313245, by rfl⟩ : syracuseStep 3341285 = 626491) (by norm_num)
theorem B1670125 : Blo 1484062 1670125 := bbase (se 3 (by rfl) ⟨313148, by rfl⟩ : syracuseStep 1670125 = 626297) (by norm_num)
theorem B2227181 : Blo 1484062 2227181 := bbase (se 3 (by rfl) ⟨417596, by rfl⟩ : syracuseStep 2227181 = 835193) (by norm_num)
theorem B2227205 : Blo 1484062 2227205 := bbase (se 4 (by rfl) ⟨208800, by rfl⟩ : syracuseStep 2227205 = 417601) (by norm_num)
theorem B1670161 : Blo 1484062 1670161 := bbase (se 2 (by rfl) ⟨626310, by rfl⟩ : syracuseStep 1670161 = 1252621) (by norm_num)
theorem B2227229 : Blo 1484062 2227229 := bbase (se 3 (by rfl) ⟨417605, by rfl⟩ : syracuseStep 2227229 = 835211) (by norm_num)
theorem B5635109 : Blo 1484062 5635109 := bbase (se 4 (by rfl) ⟨528291, by rfl⟩ : syracuseStep 5635109 = 1056583) (by norm_num)
theorem B3341357 : Blo 1484062 3341357 := bbase (se 3 (by rfl) ⟨626504, by rfl⟩ : syracuseStep 3341357 = 1253009) (by norm_num)
theorem B3759149 : Blo 1484062 3759149 := bbase (se 3 (by rfl) ⟨704840, by rfl⟩ : syracuseStep 3759149 = 1409681) (by norm_num)
theorem B1670197 : Blo 1484062 1670197 := bbase (se 5 (by rfl) ⟨78290, by rfl⟩ : syracuseStep 1670197 = 156581) (by norm_num)
theorem B2227253 : Blo 1484062 2227253 := bbase (se 5 (by rfl) ⟨104402, by rfl⟩ : syracuseStep 2227253 = 208805) (by norm_num)
theorem B5012549 : Blo 1484062 5012549 := bbase (se 4 (by rfl) ⟨469926, by rfl⟩ : syracuseStep 5012549 = 939853) (by norm_num)
theorem B2858053 : Blo 1484062 2858053 := bbase (se 4 (by rfl) ⟨267942, by rfl⟩ : syracuseStep 2858053 = 535885) (by norm_num)
theorem B2227277 : Blo 1484062 2227277 := bbase (se 3 (by rfl) ⟨417614, by rfl⟩ : syracuseStep 2227277 = 835229) (by norm_num)
theorem B1670233 : Blo 1484062 1670233 := bbase (se 2 (by rfl) ⟨626337, by rfl⟩ : syracuseStep 1670233 = 1252675) (by norm_num)
theorem B2227301 : Blo 1484062 2227301 := bbase (se 4 (by rfl) ⟨208809, by rfl⟩ : syracuseStep 2227301 = 417619) (by norm_num)
theorem B2505829 : Blo 1484062 2505829 := bbase (se 4 (by rfl) ⟨234921, by rfl⟩ : syracuseStep 2505829 = 469843) (by norm_num)
theorem B3341429 : Blo 1484062 3341429 := bbase (se 5 (by rfl) ⟨156629, by rfl⟩ : syracuseStep 3341429 = 313259) (by norm_num)
theorem B1670269 : Blo 1484062 1670269 := bbase (se 3 (by rfl) ⟨313175, by rfl⟩ : syracuseStep 1670269 = 626351) (by norm_num)
theorem B2227325 : Blo 1484062 2227325 := bbase (se 3 (by rfl) ⟨417623, by rfl⟩ : syracuseStep 2227325 = 835247) (by norm_num)
theorem B2227349 : Blo 1484062 2227349 := bbase (se 6 (by rfl) ⟨52203, by rfl⟩ : syracuseStep 2227349 = 104407) (by norm_num)
theorem B1670305 : Blo 1484062 1670305 := bbase (se 2 (by rfl) ⟨626364, by rfl⟩ : syracuseStep 1670305 = 1252729) (by norm_num)
theorem B2227373 : Blo 1484062 2227373 := bbase (se 3 (by rfl) ⟨417632, by rfl⟩ : syracuseStep 2227373 = 835265) (by norm_num)
theorem B2505917 : Blo 1484062 2505917 := bbase (se 3 (by rfl) ⟨469859, by rfl⟩ : syracuseStep 2505917 = 939719) (by norm_num)
theorem B3341501 : Blo 1484062 3341501 := bbase (se 3 (by rfl) ⟨626531, by rfl⟩ : syracuseStep 3341501 = 1253063) (by norm_num)
theorem B1670341 : Blo 1484062 1670341 := bbase (se 4 (by rfl) ⟨156594, by rfl⟩ : syracuseStep 1670341 = 313189) (by norm_num)
theorem B2227397 : Blo 1484062 2227397 := bbase (se 4 (by rfl) ⟨208818, by rfl⟩ : syracuseStep 2227397 = 417637) (by norm_num)
theorem B4758725 : Blo 1484062 4758725 := bbase (se 4 (by rfl) ⟨446130, by rfl⟩ : syracuseStep 4758725 = 892261) (by norm_num)
theorem B11279573 : Blo 1484062 11279573 := bbase (se 7 (by rfl) ⟨132182, by rfl⟩ : syracuseStep 11279573 = 264365) (by norm_num)
theorem B2227421 : Blo 1484062 2227421 := bbase (se 3 (by rfl) ⟨417641, by rfl⟩ : syracuseStep 2227421 = 835283) (by norm_num)
theorem B1670377 : Blo 1484062 1670377 := bbase (se 2 (by rfl) ⟨626391, by rfl⟩ : syracuseStep 1670377 = 1252783) (by norm_num)
theorem B2227445 : Blo 1484062 2227445 := bbase (se 5 (by rfl) ⟨104411, by rfl⟩ : syracuseStep 2227445 = 208823) (by norm_num)
theorem B5160197 : Blo 1484062 5160197 := bbase (se 4 (by rfl) ⟨483768, by rfl⟩ : syracuseStep 5160197 = 967537) (by norm_num)
theorem B3341573 : Blo 1484062 3341573 := bbase (se 4 (by rfl) ⟨313272, by rfl⟩ : syracuseStep 3341573 = 626545) (by norm_num)
theorem B1670413 : Blo 1484062 1670413 := bbase (se 3 (by rfl) ⟨313202, by rfl⟩ : syracuseStep 1670413 = 626405) (by norm_num)
theorem B2227469 : Blo 1484062 2227469 := bbase (se 3 (by rfl) ⟨417650, by rfl⟩ : syracuseStep 2227469 = 835301) (by norm_num)
theorem B2227493 : Blo 1484062 2227493 := bbase (se 4 (by rfl) ⟨208827, by rfl⟩ : syracuseStep 2227493 = 417655) (by norm_num)
theorem B1670449 : Blo 1484062 1670449 := bbase (se 2 (by rfl) ⟨626418, by rfl⟩ : syracuseStep 1670449 = 1252837) (by norm_num)
theorem B1785137 : Blo 1484062 1785137 := bbase (se 2 (by rfl) ⟨669426, by rfl⟩ : syracuseStep 1785137 = 1338853) (by norm_num)
theorem B2227517 : Blo 1484062 2227517 := bbase (se 3 (by rfl) ⟨417659, by rfl⟩ : syracuseStep 2227517 = 835319) (by norm_num)
theorem B2506045 : Blo 1484062 2506045 := bbase (se 3 (by rfl) ⟨469883, by rfl⟩ : syracuseStep 2506045 = 939767) (by norm_num)
theorem B3169613 : Blo 1484062 3169613 := bbase (se 3 (by rfl) ⟨594302, by rfl⟩ : syracuseStep 3169613 = 1188605) (by norm_num)
theorem B3341645 : Blo 1484062 3341645 := bbase (se 3 (by rfl) ⟨626558, by rfl⟩ : syracuseStep 3341645 = 1253117) (by norm_num)
theorem B1670485 : Blo 1484062 1670485 := bbase (se 11 (by rfl) ⟨1223, by rfl⟩ : syracuseStep 1670485 = 2447) (by norm_num)
theorem B2227541 : Blo 1484062 2227541 := bbase (se 11 (by rfl) ⟨1631, by rfl⟩ : syracuseStep 2227541 = 3263) (by norm_num)
theorem B2227565 : Blo 1484062 2227565 := bbase (se 3 (by rfl) ⟨417668, by rfl⟩ : syracuseStep 2227565 = 835337) (by norm_num)
theorem B8461685 : Blo 1484062 8461685 := bbase (se 5 (by rfl) ⟨396641, by rfl⟩ : syracuseStep 8461685 = 793283) (by norm_num)
theorem B1670521 : Blo 1484062 1670521 := bbase (se 2 (by rfl) ⟨626445, by rfl⟩ : syracuseStep 1670521 = 1252891) (by norm_num)
theorem B2227589 : Blo 1484062 2227589 := bbase (se 4 (by rfl) ⟨208836, by rfl⟩ : syracuseStep 2227589 = 417673) (by norm_num)
theorem B3759493 : Blo 1484062 3759493 := bbase (se 4 (by rfl) ⟨352452, by rfl⟩ : syracuseStep 3759493 = 704905) (by norm_num)
theorem B1785233 : Blo 1484062 1785233 := bbase (se 2 (by rfl) ⟨669462, by rfl⟩ : syracuseStep 1785233 = 1338925) (by norm_num)
theorem B2506133 : Blo 1484062 2506133 := bbase (se 6 (by rfl) ⟨58737, by rfl⟩ : syracuseStep 2506133 = 117475) (by norm_num)
theorem B3341717 : Blo 1484062 3341717 := bbase (se 6 (by rfl) ⟨78321, by rfl⟩ : syracuseStep 3341717 = 156643) (by norm_num)
theorem B1670557 : Blo 1484062 1670557 := bbase (se 3 (by rfl) ⟨313229, by rfl⟩ : syracuseStep 1670557 = 626459) (by norm_num)
theorem B2227613 : Blo 1484062 2227613 := bbase (se 3 (by rfl) ⟨417677, by rfl⟩ : syracuseStep 2227613 = 835355) (by norm_num)
theorem B1785253 : Blo 1484062 1785253 := bbase (se 4 (by rfl) ⟨167367, by rfl⟩ : syracuseStep 1785253 = 334735) (by norm_num)
theorem B2227637 : Blo 1484062 2227637 := bbase (se 5 (by rfl) ⟨104420, by rfl⟩ : syracuseStep 2227637 = 208841) (by norm_num)
theorem B1670593 : Blo 1484062 1670593 := bbase (se 2 (by rfl) ⟨626472, by rfl⟩ : syracuseStep 1670593 = 1252945) (by norm_num)
theorem B2227661 : Blo 1484062 2227661 := bbase (se 3 (by rfl) ⟨417686, by rfl⟩ : syracuseStep 2227661 = 835373) (by norm_num)
theorem B3341789 : Blo 1484062 3341789 := bbase (se 3 (by rfl) ⟨626585, by rfl⟩ : syracuseStep 3341789 = 1253171) (by norm_num)
theorem B1670629 : Blo 1484062 1670629 := bbase (se 4 (by rfl) ⟨156621, by rfl⟩ : syracuseStep 1670629 = 313243) (by norm_num)
theorem B2227685 : Blo 1484062 2227685 := bbase (se 4 (by rfl) ⟨208845, by rfl⟩ : syracuseStep 2227685 = 417691) (by norm_num)
theorem B2817517 : Blo 1484062 2817517 := bbase (se 3 (by rfl) ⟨528284, by rfl⟩ : syracuseStep 2817517 = 1056569) (by norm_num)
theorem B3759605 : Blo 1484062 3759605 := bbase (se 5 (by rfl) ⟨176231, by rfl⟩ : syracuseStep 3759605 = 352463) (by norm_num)
theorem B5012981 : Blo 1484062 5012981 := bbase (se 5 (by rfl) ⟨234983, by rfl⟩ : syracuseStep 5012981 = 469967) (by norm_num)
theorem B2227709 : Blo 1484062 2227709 := bbase (se 3 (by rfl) ⟨417695, by rfl⟩ : syracuseStep 2227709 = 835391) (by norm_num)
theorem B5078533 : Blo 1484062 5078533 := bbase (se 4 (by rfl) ⟨476112, by rfl⟩ : syracuseStep 5078533 = 952225) (by norm_num)
theorem B1670665 : Blo 1484062 1670665 := bbase (se 2 (by rfl) ⟨626499, by rfl⟩ : syracuseStep 1670665 = 1252999) (by norm_num)
theorem B2227733 : Blo 1484062 2227733 := bbase (se 6 (by rfl) ⟨52212, by rfl⟩ : syracuseStep 2227733 = 104425) (by norm_num)
theorem B2506261 : Blo 1484062 2506261 := bbase (se 6 (by rfl) ⟨58740, by rfl⟩ : syracuseStep 2506261 = 117481) (by norm_num)
theorem B3341861 : Blo 1484062 3341861 := bbase (se 4 (by rfl) ⟨313299, by rfl⟩ : syracuseStep 3341861 = 626599) (by norm_num)
theorem B1670701 : Blo 1484062 1670701 := bbase (se 3 (by rfl) ⟨313256, by rfl⟩ : syracuseStep 1670701 = 626513) (by norm_num)
theorem B2227757 : Blo 1484062 2227757 := bbase (se 3 (by rfl) ⟨417704, by rfl⟩ : syracuseStep 2227757 = 835409) (by norm_num)
theorem B2227781 : Blo 1484062 2227781 := bbase (se 4 (by rfl) ⟨208854, by rfl⟩ : syracuseStep 2227781 = 417709) (by norm_num)
theorem B1670737 : Blo 1484062 1670737 := bbase (se 2 (by rfl) ⟨626526, by rfl⟩ : syracuseStep 1670737 = 1253053) (by norm_num)
theorem B2227805 : Blo 1484062 2227805 := bbase (se 3 (by rfl) ⟨417713, by rfl⟩ : syracuseStep 2227805 = 835427) (by norm_num)
theorem B2506349 : Blo 1484062 2506349 := bbase (se 3 (by rfl) ⟨469940, by rfl⟩ : syracuseStep 2506349 = 939881) (by norm_num)
theorem B3341933 : Blo 1484062 3341933 := bbase (se 3 (by rfl) ⟨626612, by rfl⟩ : syracuseStep 3341933 = 1253225) (by norm_num)
theorem B11271797 : Blo 1484062 11271797 := bbase (se 5 (by rfl) ⟨528365, by rfl⟩ : syracuseStep 11271797 = 1056731) (by norm_num)
theorem B1670773 : Blo 1484062 1670773 := bbase (se 5 (by rfl) ⟨78317, by rfl⟩ : syracuseStep 1670773 = 156635) (by norm_num)
theorem B2227829 : Blo 1484062 2227829 := bbase (se 5 (by rfl) ⟨104429, by rfl⟩ : syracuseStep 2227829 = 208859) (by norm_num)
theorem B2817661 : Blo 1484062 2817661 := bbase (se 3 (by rfl) ⟨528311, by rfl⟩ : syracuseStep 2817661 = 1056623) (by norm_num)
theorem B7519877 : Blo 1484062 7519877 := bbase (se 4 (by rfl) ⟨704988, by rfl⟩ : syracuseStep 7519877 = 1409977) (by norm_num)
theorem B2227853 : Blo 1484062 2227853 := bbase (se 3 (by rfl) ⟨417722, by rfl⟩ : syracuseStep 2227853 = 835445) (by norm_num)
theorem B1670809 : Blo 1484062 1670809 := bbase (se 2 (by rfl) ⟨626553, by rfl⟩ : syracuseStep 1670809 = 1253107) (by norm_num)
theorem B2227877 : Blo 1484062 2227877 := bbase (se 4 (by rfl) ⟨208863, by rfl⟩ : syracuseStep 2227877 = 417727) (by norm_num)
theorem B3342005 : Blo 1484062 3342005 := bbase (se 5 (by rfl) ⟨156656, by rfl⟩ : syracuseStep 3342005 = 313313) (by norm_num)
theorem B3759797 : Blo 1484062 3759797 := bbase (se 5 (by rfl) ⟨176240, by rfl⟩ : syracuseStep 3759797 = 352481) (by norm_num)
theorem B1670845 : Blo 1484062 1670845 := bbase (se 3 (by rfl) ⟨313283, by rfl⟩ : syracuseStep 1670845 = 626567) (by norm_num)
theorem B2227901 : Blo 1484062 2227901 := bbase (se 3 (by rfl) ⟨417731, by rfl⟩ : syracuseStep 2227901 = 835463) (by norm_num)
theorem B2113229 : Blo 1484062 2113229 := bbase (se 3 (by rfl) ⟨396230, by rfl⟩ : syracuseStep 2113229 = 792461) (by norm_num)
theorem B2227925 : Blo 1484062 2227925 := bbase (se 7 (by rfl) ⟨26108, by rfl⟩ : syracuseStep 2227925 = 52217) (by norm_num)
theorem B1670881 : Blo 1484062 1670881 := bbase (se 2 (by rfl) ⟨626580, by rfl⟩ : syracuseStep 1670881 = 1253161) (by norm_num)
theorem B2227949 : Blo 1484062 2227949 := bbase (se 3 (by rfl) ⟨417740, by rfl⟩ : syracuseStep 2227949 = 835481) (by norm_num)
theorem B2506477 : Blo 1484062 2506477 := bbase (se 3 (by rfl) ⟨469964, by rfl⟩ : syracuseStep 2506477 = 939929) (by norm_num)
theorem B3342077 : Blo 1484062 3342077 := bbase (se 3 (by rfl) ⟨626639, by rfl⟩ : syracuseStep 3342077 = 1253279) (by norm_num)
theorem B5349125 : Blo 1484062 5349125 := bbase (se 4 (by rfl) ⟨501480, by rfl⟩ : syracuseStep 5349125 = 1002961) (by norm_num)
theorem B1670917 : Blo 1484062 1670917 := bbase (se 4 (by rfl) ⟨156648, by rfl⟩ : syracuseStep 1670917 = 313297) (by norm_num)
theorem B2227973 : Blo 1484062 2227973 := bbase (se 4 (by rfl) ⟨208872, by rfl⟩ : syracuseStep 2227973 = 417745) (by norm_num)
theorem B2817821 : Blo 1484062 2817821 := bbase (se 3 (by rfl) ⟨528341, by rfl⟩ : syracuseStep 2817821 = 1056683) (by norm_num)
theorem B2227997 : Blo 1484062 2227997 := bbase (se 3 (by rfl) ⟨417749, by rfl⟩ : syracuseStep 2227997 = 835499) (by norm_num)
theorem B1670953 : Blo 1484062 1670953 := bbase (se 2 (by rfl) ⟨626607, by rfl⟩ : syracuseStep 1670953 = 1253215) (by norm_num)
theorem B2228021 : Blo 1484062 2228021 := bbase (se 5 (by rfl) ⟨104438, by rfl⟩ : syracuseStep 2228021 = 208877) (by norm_num)
theorem B3170117 : Blo 1484062 3170117 := bbase (se 4 (by rfl) ⟨297198, by rfl⟩ : syracuseStep 3170117 = 594397) (by norm_num)
theorem B2506565 : Blo 1484062 2506565 := bbase (se 4 (by rfl) ⟨234990, by rfl⟩ : syracuseStep 2506565 = 469981) (by norm_num)
theorem B3342149 : Blo 1484062 3342149 := bbase (se 4 (by rfl) ⟨313326, by rfl⟩ : syracuseStep 3342149 = 626653) (by norm_num)
theorem B3170125 : Blo 1484062 3170125 := bbase (se 3 (by rfl) ⟨594398, by rfl⟩ : syracuseStep 3170125 = 1188797) (by norm_num)
theorem B1670989 : Blo 1484062 1670989 := bbase (se 3 (by rfl) ⟨313310, by rfl⟩ : syracuseStep 1670989 = 626621) (by norm_num)
theorem B2228045 : Blo 1484062 2228045 := bbase (se 3 (by rfl) ⟨417758, by rfl⟩ : syracuseStep 2228045 = 835517) (by norm_num)
theorem B2228069 : Blo 1484062 2228069 := bbase (se 4 (by rfl) ⟨208881, by rfl⟩ : syracuseStep 2228069 = 417763) (by norm_num)
theorem B1671025 : Blo 1484062 1671025 := bbase (se 2 (by rfl) ⟨626634, by rfl⟩ : syracuseStep 1671025 = 1253269) (by norm_num)
theorem B2228093 : Blo 1484062 2228093 := bbase (se 3 (by rfl) ⟨417767, by rfl⟩ : syracuseStep 2228093 = 835535) (by norm_num)
theorem B3342221 : Blo 1484062 3342221 := bbase (se 3 (by rfl) ⟨626666, by rfl⟩ : syracuseStep 3342221 = 1253333) (by norm_num)
theorem B1671061 : Blo 1484062 1671061 := bbase (se 6 (by rfl) ⟨39165, by rfl⟩ : syracuseStep 1671061 = 78331) (by norm_num)
theorem B2228117 : Blo 1484062 2228117 := bbase (se 6 (by rfl) ⟨52221, by rfl⟩ : syracuseStep 2228117 = 104443) (by norm_num)
theorem B5013413 : Blo 1484062 5013413 := bbase (se 4 (by rfl) ⟨470007, by rfl⟩ : syracuseStep 5013413 = 940015) (by norm_num)
theorem B2817965 : Blo 1484062 2817965 := bbase (se 3 (by rfl) ⟨528368, by rfl⟩ : syracuseStep 2817965 = 1056737) (by norm_num)
theorem B2228141 : Blo 1484062 2228141 := bbase (se 3 (by rfl) ⟨417776, by rfl⟩ : syracuseStep 2228141 = 835553) (by norm_num)
theorem B1671097 : Blo 1484062 1671097 := bbase (se 2 (by rfl) ⟨626661, by rfl⟩ : syracuseStep 1671097 = 1253323) (by norm_num)
theorem B2228165 : Blo 1484062 2228165 := bbase (se 4 (by rfl) ⟨208890, by rfl⟩ : syracuseStep 2228165 = 417781) (by norm_num)
theorem B2506693 : Blo 1484062 2506693 := bbase (se 4 (by rfl) ⟨235002, by rfl⟩ : syracuseStep 2506693 = 470005) (by norm_num)
theorem B3342293 : Blo 1484062 3342293 := bbase (se 7 (by rfl) ⟨39167, by rfl⟩ : syracuseStep 3342293 = 78335) (by norm_num)
theorem B1671133 : Blo 1484062 1671133 := bbase (se 3 (by rfl) ⟨313337, by rfl⟩ : syracuseStep 1671133 = 626675) (by norm_num)
theorem B2228189 : Blo 1484062 2228189 := bbase (se 3 (by rfl) ⟨417785, by rfl⟩ : syracuseStep 2228189 = 835571) (by norm_num)
theorem B8568821 : Blo 1484062 8568821 := bbase (se 5 (by rfl) ⟨401663, by rfl⟩ : syracuseStep 8568821 = 803327) (by norm_num)
theorem B4227061 : Blo 1484062 4227061 := bbase (se 5 (by rfl) ⟨198143, by rfl⟩ : syracuseStep 4227061 = 396287) (by norm_num)
theorem B2228213 : Blo 1484062 2228213 := bbase (se 5 (by rfl) ⟨104447, by rfl⟩ : syracuseStep 2228213 = 208895) (by norm_num)
theorem B2228225 : Blo 1484062 2228225 := bstep (se 2 (by rfl) ⟨835584, by rfl⟩ : syracuseStep 2228225 = 1671169) B1671169
theorem B5013521 : Blo 1484062 5013521 := bstep (se 2 (by rfl) ⟨1880070, by rfl⟩ : syracuseStep 5013521 = 3760141) B3760141
theorem B2228243 : Blo 1484062 2228243 := bstep (se 1 (by rfl) ⟨1671182, by rfl⟩ : syracuseStep 2228243 = 3342365) B3342365
theorem B1671187 : Blo 1484062 1671187 := bstep (se 1 (by rfl) ⟨1253390, by rfl⟩ : syracuseStep 1671187 = 2506781) B2506781
theorem B7233571 : Blo 1484062 7233571 := bstep (se 1 (by rfl) ⟨5425178, by rfl⟩ : syracuseStep 7233571 = 10850357) B10850357
theorem B2506801 : Blo 1484062 2506801 := bstep (se 2 (by rfl) ⟨940050, by rfl⟩ : syracuseStep 2506801 = 1880101) B1880101
theorem B2228273 : Blo 1484062 2228273 := bstep (se 2 (by rfl) ⟨835602, by rfl⟩ : syracuseStep 2228273 = 1671205) B1671205
theorem B2228291 : Blo 1484062 2228291 := bstep (se 1 (by rfl) ⟨1671218, by rfl⟩ : syracuseStep 2228291 = 3342437) B3342437
theorem B4071491 : Blo 1484062 4071491 := bstep (se 1 (by rfl) ⟨3053618, by rfl⟩ : syracuseStep 4071491 = 6107237) B6107237
theorem B2506835 : Blo 1484062 2506835 := bstep (se 1 (by rfl) ⟨1880126, by rfl⟩ : syracuseStep 2506835 = 3760253) B3760253
theorem B2228321 : Blo 1484062 2228321 := bstep (se 2 (by rfl) ⟨835620, by rfl⟩ : syracuseStep 2228321 = 1671241) B1671241
theorem B2818147 : Blo 1484062 2818147 := bstep (se 1 (by rfl) ⟨2113610, by rfl⟩ : syracuseStep 2818147 = 4227221) B4227221
theorem B2228339 : Blo 1484062 2228339 := bstep (se 1 (by rfl) ⟨1671254, by rfl⟩ : syracuseStep 2228339 = 3342509) B3342509
theorem B2228369 : Blo 1484062 2228369 := bstep (se 2 (by rfl) ⟨835638, by rfl⟩ : syracuseStep 2228369 = 1671277) B1671277
theorem B2228387 : Blo 1484062 2228387 := bstep (se 1 (by rfl) ⟨1671290, by rfl⟩ : syracuseStep 2228387 = 3342581) B3342581
theorem B1671331 : Blo 1484062 1671331 := bstep (se 1 (by rfl) ⟨1253498, by rfl⟩ : syracuseStep 1671331 = 2506997) B2506997
theorem B2228417 : Blo 1484062 2228417 := bstep (se 2 (by rfl) ⟨835656, by rfl⟩ : syracuseStep 2228417 = 1671313) B1671313
theorem B3342545 : Blo 1484062 3342545 := bstep (se 2 (by rfl) ⟨1253454, by rfl⟩ : syracuseStep 3342545 = 2506909) B2506909
theorem B1958099 : Blo 1484062 1958099 := bstep (se 1 (by rfl) ⟨1468574, by rfl⟩ : syracuseStep 1958099 = 2937149) B2937149
theorem B2506963 : Blo 1484062 2506963 := bstep (se 1 (by rfl) ⟨1880222, by rfl⟩ : syracuseStep 2506963 = 3760445) B3760445
theorem B2228435 : Blo 1484062 2228435 := bstep (se 1 (by rfl) ⟨1671326, by rfl⟩ : syracuseStep 2228435 = 3342653) B3342653
theorem B3342563 : Blo 1484062 3342563 := bstep (se 1 (by rfl) ⟨2506922, by rfl⟩ : syracuseStep 3342563 = 5013845) B5013845
theorem B2228465 : Blo 1484062 2228465 := bstep (se 2 (by rfl) ⟨835674, by rfl⟩ : syracuseStep 2228465 = 1671349) B1671349
theorem B2818307 : Blo 1484062 2818307 := bstep (se 1 (by rfl) ⟨2113730, by rfl⟩ : syracuseStep 2818307 = 4227461) B4227461
theorem B2228483 : Blo 1484062 2228483 := bstep (se 1 (by rfl) ⟨1671362, by rfl⟩ : syracuseStep 2228483 = 3342725) B3342725
theorem B7520525 : Blo 1484062 7520525 := bstep (se 3 (by rfl) ⟨1410098, by rfl⟩ : syracuseStep 7520525 = 2820197) B2820197
theorem B4014353 : Blo 1484062 4014353 := bstep (se 2 (by rfl) ⟨1505382, by rfl⟩ : syracuseStep 4014353 = 3010765) B3010765
theorem B2228513 : Blo 1484062 2228513 := bstep (se 2 (by rfl) ⟨835692, by rfl⟩ : syracuseStep 2228513 = 1671385) B1671385
theorem B2228531 : Blo 1484062 2228531 := bstep (se 1 (by rfl) ⟨1671398, by rfl⟩ : syracuseStep 2228531 = 3342797) B3342797
theorem B1671475 : Blo 1484062 1671475 := bstep (se 1 (by rfl) ⟨1253606, by rfl⟩ : syracuseStep 1671475 = 2507213) B2507213
theorem B3760465 : Blo 1484062 3760465 := bstep (se 2 (by rfl) ⟨1410174, by rfl⟩ : syracuseStep 3760465 = 2820349) B2820349
theorem B2228561 : Blo 1484062 2228561 := bstep (se 2 (by rfl) ⟨835710, by rfl⟩ : syracuseStep 2228561 = 1671421) B1671421
theorem B2507105 : Blo 1484062 2507105 := bstep (se 2 (by rfl) ⟨940164, by rfl⟩ : syracuseStep 2507105 = 1880329) B1880329
theorem B2228579 : Blo 1484062 2228579 := bstep (se 1 (by rfl) ⟨1671434, by rfl⟩ : syracuseStep 2228579 = 3342869) B3342869
theorem B2228609 : Blo 1484062 2228609 := bstep (se 2 (by rfl) ⟨835728, by rfl⟩ : syracuseStep 2228609 = 1671457) B1671457
theorem B2228627 : Blo 1484062 2228627 := bstep (se 1 (by rfl) ⟨1671470, by rfl⟩ : syracuseStep 2228627 = 3342941) B3342941
theorem B8454577 : Blo 1484062 8454577 := bstep (se 2 (by rfl) ⟨3170466, by rfl⟩ : syracuseStep 8454577 = 6340933) B6340933
theorem B2228657 : Blo 1484062 2228657 := bstep (se 2 (by rfl) ⟨835746, by rfl⟩ : syracuseStep 2228657 = 1671493) B1671493
theorem B2228675 : Blo 1484062 2228675 := bstep (se 1 (by rfl) ⟨1671506, by rfl⟩ : syracuseStep 2228675 = 3343013) B3343013
theorem B1671619 : Blo 1484062 1671619 := bstep (se 1 (by rfl) ⟨1253714, by rfl⟩ : syracuseStep 1671619 = 2507429) B2507429
theorem B2507233 : Blo 1484062 2507233 := bstep (se 2 (by rfl) ⟨940212, by rfl⟩ : syracuseStep 2507233 = 1880425) B1880425
theorem B2228705 : Blo 1484062 2228705 := bstep (se 2 (by rfl) ⟨835764, by rfl⟩ : syracuseStep 2228705 = 1671529) B1671529
theorem B6341105 : Blo 1484062 6341105 := bstep (se 2 (by rfl) ⟨2377914, by rfl⟩ : syracuseStep 6341105 = 4755829) B4755829
theorem B3170801 : Blo 1484062 3170801 := bstep (se 2 (by rfl) ⟨1189050, by rfl⟩ : syracuseStep 3170801 = 2378101) B2378101
theorem B3342833 : Blo 1484062 3342833 := bstep (se 2 (by rfl) ⟨1253562, by rfl⟩ : syracuseStep 3342833 = 2507125) B2507125
theorem B9519601 : Blo 1484062 9519601 := bstep (se 2 (by rfl) ⟨3569850, by rfl⟩ : syracuseStep 9519601 = 7139701) B7139701
theorem B2228723 : Blo 1484062 2228723 := bstep (se 1 (by rfl) ⟨1671542, by rfl⟩ : syracuseStep 2228723 = 3343085) B3343085
theorem B3342851 : Blo 1484062 3342851 := bstep (se 1 (by rfl) ⟨2507138, by rfl⟩ : syracuseStep 3342851 = 5014277) B5014277
theorem B2507267 : Blo 1484062 2507267 := bstep (se 1 (by rfl) ⟨1880450, by rfl⟩ : syracuseStep 2507267 = 3760901) B3760901
theorem B2228753 : Blo 1484062 2228753 := bstep (se 2 (by rfl) ⟨835782, by rfl⟩ : syracuseStep 2228753 = 1671565) B1671565
theorem B2228771 : Blo 1484062 2228771 := bstep (se 1 (by rfl) ⟨1671578, by rfl⟩ : syracuseStep 2228771 = 3343157) B3343157
theorem B5014061 : Blo 1484062 5014061 := bstep (se 3 (by rfl) ⟨940136, by rfl⟩ : syracuseStep 5014061 = 1880273) B1880273
theorem B2228801 : Blo 1484062 2228801 := bstep (se 2 (by rfl) ⟨835800, by rfl⟩ : syracuseStep 2228801 = 1671601) B1671601
theorem B2228819 : Blo 1484062 2228819 := bstep (se 1 (by rfl) ⟨1671614, by rfl⟩ : syracuseStep 2228819 = 3343229) B3343229
theorem B1671763 : Blo 1484062 1671763 := bstep (se 1 (by rfl) ⟨1253822, by rfl⟩ : syracuseStep 1671763 = 2507645) B2507645
theorem B5014115 : Blo 1484062 5014115 := bstep (se 1 (by rfl) ⟨3760586, by rfl⟩ : syracuseStep 5014115 = 7521173) B7521173
theorem B3760739 : Blo 1484062 3760739 := bstep (se 1 (by rfl) ⟨2820554, by rfl⟩ : syracuseStep 3760739 = 5641109) B5641109
theorem B2228849 : Blo 1484062 2228849 := bstep (se 2 (by rfl) ⟨835818, by rfl⟩ : syracuseStep 2228849 = 1671637) B1671637
theorem B2507395 : Blo 1484062 2507395 := bstep (se 1 (by rfl) ⟨1880546, by rfl⟩ : syracuseStep 2507395 = 3761093) B3761093
theorem B2228867 : Blo 1484062 2228867 := bstep (se 1 (by rfl) ⟨1671650, by rfl⟩ : syracuseStep 2228867 = 3343301) B3343301
theorem B5636749 : Blo 1484062 5636749 := bstep (se 3 (by rfl) ⟨1056890, by rfl⟩ : syracuseStep 5636749 = 2113781) B2113781
theorem B2228897 : Blo 1484062 2228897 := bstep (se 2 (by rfl) ⟨835836, by rfl⟩ : syracuseStep 2228897 = 1671673) B1671673
theorem B2228915 : Blo 1484062 2228915 := bstep (se 1 (by rfl) ⟨1671686, by rfl⟩ : syracuseStep 2228915 = 3343373) B3343373
theorem B16917173 : Blo 1484062 16917173 := bstep (se 5 (by rfl) ⟨792992, by rfl⟩ : syracuseStep 16917173 = 1585985) B1585985
theorem B2228945 : Blo 1484062 2228945 := bstep (se 2 (by rfl) ⟨835854, by rfl⟩ : syracuseStep 2228945 = 1671709) B1671709
theorem B2228963 : Blo 1484062 2228963 := bstep (se 1 (by rfl) ⟨1671722, by rfl⟩ : syracuseStep 2228963 = 3343445) B3343445
theorem B2228993 : Blo 1484062 2228993 := bstep (se 2 (by rfl) ⟨835872, by rfl⟩ : syracuseStep 2228993 = 1671745) B1671745
theorem B7619341 : Blo 1484062 7619341 := bstep (se 3 (by rfl) ⟨1428626, by rfl⟩ : syracuseStep 7619341 = 2857253) B2857253
theorem B3343121 : Blo 1484062 3343121 := bstep (se 2 (by rfl) ⟨1253670, by rfl⟩ : syracuseStep 3343121 = 2507341) B2507341
theorem B2507537 : Blo 1484062 2507537 := bstep (se 2 (by rfl) ⟨940326, by rfl⟩ : syracuseStep 2507537 = 1880653) B1880653
theorem B2229011 : Blo 1484062 2229011 := bstep (se 1 (by rfl) ⟨1671758, by rfl⟩ : syracuseStep 2229011 = 3343517) B3343517
theorem B3760931 : Blo 1484062 3760931 := bstep (se 1 (by rfl) ⟨2820698, by rfl⟩ : syracuseStep 3760931 = 5641397) B5641397
theorem B3343139 : Blo 1484062 3343139 := bstep (se 1 (by rfl) ⟨2507354, by rfl⟩ : syracuseStep 3343139 = 5014709) B5014709
theorem B4760365 : Blo 1484062 4760365 := bstep (se 3 (by rfl) ⟨892568, by rfl⟩ : syracuseStep 4760365 = 1785137) B1785137
theorem B2229041 : Blo 1484062 2229041 := bstep (se 2 (by rfl) ⟨835890, by rfl⟩ : syracuseStep 2229041 = 1671781) B1671781
theorem B2229059 : Blo 1484062 2229059 := bstep (se 1 (by rfl) ⟨1671794, by rfl⟩ : syracuseStep 2229059 = 3343589) B3343589
theorem B2229089 : Blo 1484062 2229089 := bstep (se 2 (by rfl) ⟨835908, by rfl⟩ : syracuseStep 2229089 = 1671817) B1671817
theorem B5014385 : Blo 1484062 5014385 := bstep (se 2 (by rfl) ⟨1880394, by rfl⟩ : syracuseStep 5014385 = 3760789) B3760789
theorem B2114419 : Blo 1484062 2114419 := bstep (se 1 (by rfl) ⟨1585814, by rfl⟩ : syracuseStep 2114419 = 3171629) B3171629
theorem B2507665 : Blo 1484062 2507665 := bstep (se 2 (by rfl) ⟨940374, by rfl⟩ : syracuseStep 2507665 = 1880749) B1880749
theorem B2507699 : Blo 1484062 2507699 := bstep (se 1 (by rfl) ⟨1880774, by rfl⟩ : syracuseStep 2507699 = 3761549) B3761549
theorem B7513073 : Blo 1484062 7513073 := bstep (se 2 (by rfl) ⟨2817402, by rfl⟩ : syracuseStep 7513073 = 5634805) B5634805
theorem B4228109 : Blo 1484062 4228109 := bstep (se 3 (by rfl) ⟨792770, by rfl⟩ : syracuseStep 4228109 = 1585541) B1585541
theorem B4760621 : Blo 1484062 4760621 := bstep (se 3 (by rfl) ⟨892616, by rfl⟩ : syracuseStep 4760621 = 1785233) B1785233
theorem B3343409 : Blo 1484062 3343409 := bstep (se 2 (by rfl) ⟨1253778, by rfl⟩ : syracuseStep 3343409 = 2507557) B2507557
theorem B3343427 : Blo 1484062 3343427 := bstep (se 1 (by rfl) ⟨2507570, by rfl⟩ : syracuseStep 3343427 = 5015141) B5015141
theorem B4015217 : Blo 1484062 4015217 := bstep (se 2 (by rfl) ⟨1505706, by rfl⟩ : syracuseStep 4015217 = 3011413) B3011413
theorem B4228291 : Blo 1484062 4228291 := bstep (se 1 (by rfl) ⟨3171218, by rfl⟩ : syracuseStep 4228291 = 6342437) B6342437
theorem B4228337 : Blo 1484062 4228337 := bstep (se 2 (by rfl) ⟨1585626, by rfl⟩ : syracuseStep 4228337 = 3171253) B3171253
theorem B1484067 : Blo 1484062 1484067 := bstep (se 1 (by rfl) ⟨1113050, by rfl⟩ : syracuseStep 1484067 = 2226101) B2226101
theorem B2819377 : Blo 1484062 2819377 := bstep (se 2 (by rfl) ⟨1057266, by rfl⟩ : syracuseStep 2819377 = 2114533) B2114533
theorem B1484083 : Blo 1484062 1484083 := bstep (se 1 (by rfl) ⟨1113062, by rfl⟩ : syracuseStep 1484083 = 2226125) B2226125
theorem B1484099 : Blo 1484062 1484099 := bstep (se 1 (by rfl) ⟨1113074, by rfl⟩ : syracuseStep 1484099 = 2226149) B2226149
theorem B1484115 : Blo 1484062 1484115 := bstep (se 1 (by rfl) ⟨1113086, by rfl⟩ : syracuseStep 1484115 = 2226173) B2226173
theorem B1484131 : Blo 1484062 1484131 := bstep (se 1 (by rfl) ⟨1113098, by rfl⟩ : syracuseStep 1484131 = 2226197) B2226197
theorem B13731185 : Blo 1484062 13731185 := bstep (se 2 (by rfl) ⟨5149194, by rfl⟩ : syracuseStep 13731185 = 10298389) B10298389
theorem B1484147 : Blo 1484062 1484147 := bstep (se 1 (by rfl) ⟨1113110, by rfl⟩ : syracuseStep 1484147 = 2226221) B2226221
theorem B1484163 : Blo 1484062 1484163 := bstep (se 1 (by rfl) ⟨1113122, by rfl⟩ : syracuseStep 1484163 = 2226245) B2226245
theorem B5014925 : Blo 1484062 5014925 := bstep (se 3 (by rfl) ⟨940298, by rfl⟩ : syracuseStep 5014925 = 1880597) B1880597
theorem B1484179 : Blo 1484062 1484179 := bstep (se 1 (by rfl) ⟨1113134, by rfl⟩ : syracuseStep 1484179 = 2226269) B2226269
theorem B1484195 : Blo 1484062 1484195 := bstep (se 1 (by rfl) ⟨1113146, by rfl⟩ : syracuseStep 1484195 = 2226293) B2226293
theorem B5637539 : Blo 1484062 5637539 := bstep (se 1 (by rfl) ⟨4228154, by rfl⟩ : syracuseStep 5637539 = 8456309) B8456309
theorem B3810737 : Blo 1484062 3810737 := bstep (se 2 (by rfl) ⟨1429026, by rfl⟩ : syracuseStep 3810737 = 2858053) B2858053
theorem B1484211 : Blo 1484062 1484211 := bstep (se 1 (by rfl) ⟨1113158, by rfl⟩ : syracuseStep 1484211 = 2226317) B2226317
theorem B1484227 : Blo 1484062 1484227 := bstep (se 1 (by rfl) ⟨1113170, by rfl⟩ : syracuseStep 1484227 = 2226341) B2226341
theorem B5014979 : Blo 1484062 5014979 := bstep (se 1 (by rfl) ⟨3761234, by rfl⟩ : syracuseStep 5014979 = 7522469) B7522469
theorem B1484243 : Blo 1484062 1484243 := bstep (se 1 (by rfl) ⟨1113182, by rfl⟩ : syracuseStep 1484243 = 2226365) B2226365
theorem B1484259 : Blo 1484062 1484259 := bstep (se 1 (by rfl) ⟨1113194, by rfl⟩ : syracuseStep 1484259 = 2226389) B2226389
theorem B1484275 : Blo 1484062 1484275 := bstep (se 1 (by rfl) ⟨1113206, by rfl⟩ : syracuseStep 1484275 = 2226413) B2226413
theorem B1484291 : Blo 1484062 1484291 := bstep (se 1 (by rfl) ⟨1113218, by rfl⟩ : syracuseStep 1484291 = 2226437) B2226437
theorem B2541059 : Blo 1484062 2541059 := bstep (se 1 (by rfl) ⟨1905794, by rfl⟩ : syracuseStep 2541059 = 3811589) B3811589
theorem B11273741 : Blo 1484062 11273741 := bstep (se 3 (by rfl) ⟨2113826, by rfl⟩ : syracuseStep 11273741 = 4227653) B4227653
theorem B2377235 : Blo 1484062 2377235 := bstep (se 1 (by rfl) ⟨1782926, by rfl⟩ : syracuseStep 2377235 = 3565853) B3565853
theorem B1484307 : Blo 1484062 1484307 := bstep (se 1 (by rfl) ⟨1113230, by rfl⟩ : syracuseStep 1484307 = 2226461) B2226461
theorem B1484323 : Blo 1484062 1484323 := bstep (se 1 (by rfl) ⟨1113242, by rfl⟩ : syracuseStep 1484323 = 2226485) B2226485
theorem B4015651 : Blo 1484062 4015651 := bstep (se 1 (by rfl) ⟨3011738, by rfl⟩ : syracuseStep 4015651 = 6023477) B6023477
theorem B1484339 : Blo 1484062 1484339 := bstep (se 1 (by rfl) ⟨1113254, by rfl⟩ : syracuseStep 1484339 = 2226509) B2226509
theorem B1484355 : Blo 1484062 1484355 := bstep (se 1 (by rfl) ⟨1113266, by rfl⟩ : syracuseStep 1484355 = 2226533) B2226533
theorem B1484371 : Blo 1484062 1484371 := bstep (se 1 (by rfl) ⟨1113278, by rfl⟩ : syracuseStep 1484371 = 2226557) B2226557
theorem B1484387 : Blo 1484062 1484387 := bstep (se 1 (by rfl) ⟨1113290, by rfl⟩ : syracuseStep 1484387 = 2226581) B2226581
theorem B16066147 : Blo 1484062 16066147 := bstep (se 1 (by rfl) ⟨12049610, by rfl⟩ : syracuseStep 16066147 = 24099221) B24099221
theorem B1484403 : Blo 1484062 1484403 := bstep (se 1 (by rfl) ⟨1113302, by rfl⟩ : syracuseStep 1484403 = 2226605) B2226605
theorem B1484419 : Blo 1484062 1484419 := bstep (se 1 (by rfl) ⟨1113314, by rfl⟩ : syracuseStep 1484419 = 2226629) B2226629
theorem B1484435 : Blo 1484062 1484435 := bstep (se 1 (by rfl) ⟨1113326, by rfl⟩ : syracuseStep 1484435 = 2226653) B2226653
theorem B1484451 : Blo 1484062 1484451 := bstep (se 1 (by rfl) ⟨1113338, by rfl⟩ : syracuseStep 1484451 = 2226677) B2226677
theorem B1484467 : Blo 1484062 1484467 := bstep (se 1 (by rfl) ⟨1113350, by rfl⟩ : syracuseStep 1484467 = 2226701) B2226701
theorem B1607347 : Blo 1484062 1607347 := bstep (se 1 (by rfl) ⟨1205510, by rfl⟩ : syracuseStep 1607347 = 2411021) B2411021
theorem B1484483 : Blo 1484062 1484483 := bstep (se 1 (by rfl) ⟨1113362, by rfl⟩ : syracuseStep 1484483 = 2226725) B2226725
theorem B5015249 : Blo 1484062 5015249 := bstep (se 2 (by rfl) ⟨1880718, by rfl⟩ : syracuseStep 5015249 = 3761437) B3761437
theorem B1484499 : Blo 1484062 1484499 := bstep (se 1 (by rfl) ⟨1113374, by rfl⟩ : syracuseStep 1484499 = 2226749) B2226749
theorem B1484515 : Blo 1484062 1484515 := bstep (se 1 (by rfl) ⟨1113386, by rfl⟩ : syracuseStep 1484515 = 2226773) B2226773
theorem B1484531 : Blo 1484062 1484531 := bstep (se 1 (by rfl) ⟨1113398, by rfl⟩ : syracuseStep 1484531 = 2226797) B2226797
theorem B1484547 : Blo 1484062 1484547 := bstep (se 1 (by rfl) ⟨1113410, by rfl⟩ : syracuseStep 1484547 = 2226821) B2226821
theorem B1484563 : Blo 1484062 1484563 := bstep (se 1 (by rfl) ⟨1113422, by rfl⟩ : syracuseStep 1484563 = 2226845) B2226845
theorem B2377505 : Blo 1484062 2377505 := bstep (se 2 (by rfl) ⟨891564, by rfl⟩ : syracuseStep 2377505 = 1783129) B1783129
theorem B1484579 : Blo 1484062 1484579 := bstep (se 1 (by rfl) ⟨1113434, by rfl⟩ : syracuseStep 1484579 = 2226869) B2226869
theorem B4638509 : Blo 1484062 4638509 := bstep (se 3 (by rfl) ⟨869720, by rfl⟩ : syracuseStep 4638509 = 1739441) B1739441
theorem B1484595 : Blo 1484062 1484595 := bstep (se 1 (by rfl) ⟨1113446, by rfl⟩ : syracuseStep 1484595 = 2226893) B2226893
theorem B1484611 : Blo 1484062 1484611 := bstep (se 1 (by rfl) ⟨1113458, by rfl⟩ : syracuseStep 1484611 = 2226917) B2226917
theorem B1484627 : Blo 1484062 1484627 := bstep (se 1 (by rfl) ⟨1113470, by rfl⟩ : syracuseStep 1484627 = 2226941) B2226941
theorem B1484643 : Blo 1484062 1484643 := bstep (se 1 (by rfl) ⟨1113482, by rfl⟩ : syracuseStep 1484643 = 2226965) B2226965
theorem B8456035 : Blo 1484062 8456035 := bstep (se 1 (by rfl) ⟨6342026, by rfl⟩ : syracuseStep 8456035 = 12684053) B12684053
theorem B1484659 : Blo 1484062 1484659 := bstep (se 1 (by rfl) ⟨1113494, by rfl⟩ : syracuseStep 1484659 = 2226989) B2226989
theorem B1484675 : Blo 1484062 1484675 := bstep (se 1 (by rfl) ⟨1113506, by rfl⟩ : syracuseStep 1484675 = 2227013) B2227013
theorem B1484691 : Blo 1484062 1484691 := bstep (se 1 (by rfl) ⟨1113518, by rfl⟩ : syracuseStep 1484691 = 2227037) B2227037
theorem B1484707 : Blo 1484062 1484707 := bstep (se 1 (by rfl) ⟨1113530, by rfl⟩ : syracuseStep 1484707 = 2227061) B2227061
theorem B1484723 : Blo 1484062 1484723 := bstep (se 1 (by rfl) ⟨1113542, by rfl⟩ : syracuseStep 1484723 = 2227085) B2227085
theorem B1484739 : Blo 1484062 1484739 := bstep (se 1 (by rfl) ⟨1113554, by rfl⟩ : syracuseStep 1484739 = 2227109) B2227109
theorem B1484755 : Blo 1484062 1484755 := bstep (se 1 (by rfl) ⟨1113566, by rfl⟩ : syracuseStep 1484755 = 2227133) B2227133
theorem B2115553 : Blo 1484062 2115553 := bstep (se 2 (by rfl) ⟨793332, by rfl⟩ : syracuseStep 2115553 = 1586665) B1586665
theorem B1484771 : Blo 1484062 1484771 := bstep (se 1 (by rfl) ⟨1113578, by rfl⟩ : syracuseStep 1484771 = 2227157) B2227157
theorem B14272483 : Blo 1484062 14272483 := bstep (se 1 (by rfl) ⟨10704362, by rfl⟩ : syracuseStep 14272483 = 21408725) B21408725
theorem B6023153 : Blo 1484062 6023153 := bstep (se 2 (by rfl) ⟨2258682, by rfl⟩ : syracuseStep 6023153 = 4517365) B4517365
theorem B1484787 : Blo 1484062 1484787 := bstep (se 1 (by rfl) ⟨1113590, by rfl⟩ : syracuseStep 1484787 = 2227181) B2227181
theorem B1484803 : Blo 1484062 1484803 := bstep (se 1 (by rfl) ⟨1113602, by rfl⟩ : syracuseStep 1484803 = 2227205) B2227205
theorem B14264333 : Blo 1484062 14264333 := bstep (se 3 (by rfl) ⟨2674562, by rfl⟩ : syracuseStep 14264333 = 5349125) B5349125
theorem B1484819 : Blo 1484062 1484819 := bstep (se 1 (by rfl) ⟨1113614, by rfl⟩ : syracuseStep 1484819 = 2227229) B2227229
theorem B1484835 : Blo 1484062 1484835 := bstep (se 1 (by rfl) ⟨1113626, by rfl⟩ : syracuseStep 1484835 = 2227253) B2227253
theorem B5638193 : Blo 1484062 5638193 := bstep (se 2 (by rfl) ⟨2114322, by rfl⟩ : syracuseStep 5638193 = 4228645) B4228645
theorem B1484851 : Blo 1484062 1484851 := bstep (se 1 (by rfl) ⟨1113638, by rfl⟩ : syracuseStep 1484851 = 2227277) B2227277
theorem B2377793 : Blo 1484062 2377793 := bstep (se 2 (by rfl) ⟨891672, by rfl⟩ : syracuseStep 2377793 = 1783345) B1783345
theorem B2115649 : Blo 1484062 2115649 := bstep (se 2 (by rfl) ⟨793368, by rfl⟩ : syracuseStep 2115649 = 1586737) B1586737
theorem B1484867 : Blo 1484062 1484867 := bstep (se 1 (by rfl) ⟨1113650, by rfl⟩ : syracuseStep 1484867 = 2227301) B2227301
theorem B1484883 : Blo 1484062 1484883 := bstep (se 1 (by rfl) ⟨1113662, by rfl⟩ : syracuseStep 1484883 = 2227325) B2227325
theorem B1484899 : Blo 1484062 1484899 := bstep (se 1 (by rfl) ⟨1113674, by rfl⟩ : syracuseStep 1484899 = 2227349) B2227349
theorem B6023281 : Blo 1484062 6023281 := bstep (se 2 (by rfl) ⟨2258730, by rfl⟩ : syracuseStep 6023281 = 4517461) B4517461
theorem B1484915 : Blo 1484062 1484915 := bstep (se 1 (by rfl) ⟨1113686, by rfl⟩ : syracuseStep 1484915 = 2227373) B2227373
theorem B1484931 : Blo 1484062 1484931 := bstep (se 1 (by rfl) ⟨1113698, by rfl⟩ : syracuseStep 1484931 = 2227397) B2227397
theorem B3172483 : Blo 1484062 3172483 := bstep (se 1 (by rfl) ⟨2379362, by rfl⟩ : syracuseStep 3172483 = 4758725) B4758725
theorem B6785165 : Blo 1484062 6785165 := bstep (se 3 (by rfl) ⟨1272218, by rfl⟩ : syracuseStep 6785165 = 2544437) B2544437
theorem B1484947 : Blo 1484062 1484947 := bstep (se 1 (by rfl) ⟨1113710, by rfl⟩ : syracuseStep 1484947 = 2227421) B2227421
theorem B1484963 : Blo 1484062 1484963 := bstep (se 1 (by rfl) ⟨1113722, by rfl⟩ : syracuseStep 1484963 = 2227445) B2227445
theorem B1484979 : Blo 1484062 1484979 := bstep (se 1 (by rfl) ⟨1113734, by rfl⟩ : syracuseStep 1484979 = 2227469) B2227469
theorem B1484995 : Blo 1484062 1484995 := bstep (se 1 (by rfl) ⟨1113746, by rfl⟩ : syracuseStep 1484995 = 2227493) B2227493
theorem B1485011 : Blo 1484062 1485011 := bstep (se 1 (by rfl) ⟨1113758, by rfl⟩ : syracuseStep 1485011 = 2227517) B2227517
theorem B1485027 : Blo 1484062 1485027 := bstep (se 1 (by rfl) ⟨1113770, by rfl⟩ : syracuseStep 1485027 = 2227541) B2227541
theorem B1485043 : Blo 1484062 1485043 := bstep (se 1 (by rfl) ⟨1113782, by rfl⟩ : syracuseStep 1485043 = 2227565) B2227565
theorem B1485059 : Blo 1484062 1485059 := bstep (se 1 (by rfl) ⟨1113794, by rfl⟩ : syracuseStep 1485059 = 2227589) B2227589
theorem B1485075 : Blo 1484062 1485075 := bstep (se 1 (by rfl) ⟨1113806, by rfl⟩ : syracuseStep 1485075 = 2227613) B2227613
theorem B1485091 : Blo 1484062 1485091 := bstep (se 1 (by rfl) ⟨1113818, by rfl⟩ : syracuseStep 1485091 = 2227637) B2227637
theorem B3565873 : Blo 1484062 3565873 := bstep (se 2 (by rfl) ⟨1337202, by rfl⟩ : syracuseStep 3565873 = 2674405) B2674405
theorem B1485107 : Blo 1484062 1485107 := bstep (se 1 (by rfl) ⟨1113830, by rfl⟩ : syracuseStep 1485107 = 2227661) B2227661
theorem B1485123 : Blo 1484062 1485123 := bstep (se 1 (by rfl) ⟨1113842, by rfl⟩ : syracuseStep 1485123 = 2227685) B2227685
theorem B2820433 : Blo 1484062 2820433 := bstep (se 2 (by rfl) ⟨1057662, by rfl⟩ : syracuseStep 2820433 = 2115325) B2115325
theorem B1485139 : Blo 1484062 1485139 := bstep (se 1 (by rfl) ⟨1113854, by rfl⟩ : syracuseStep 1485139 = 2227709) B2227709
theorem B1485155 : Blo 1484062 1485155 := bstep (se 1 (by rfl) ⟨1113866, by rfl⟩ : syracuseStep 1485155 = 2227733) B2227733
theorem B8456561 : Blo 1484062 8456561 := bstep (se 2 (by rfl) ⟨3171210, by rfl⟩ : syracuseStep 8456561 = 6342421) B6342421
theorem B1485171 : Blo 1484062 1485171 := bstep (se 1 (by rfl) ⟨1113878, by rfl⟩ : syracuseStep 1485171 = 2227757) B2227757
theorem B1485187 : Blo 1484062 1485187 := bstep (se 1 (by rfl) ⟨1113890, by rfl⟩ : syracuseStep 1485187 = 2227781) B2227781
theorem B1485203 : Blo 1484062 1485203 := bstep (se 1 (by rfl) ⟨1113902, by rfl⟩ : syracuseStep 1485203 = 2227805) B2227805
theorem B7514531 : Blo 1484062 7514531 := bstep (se 1 (by rfl) ⟨5635898, by rfl⟩ : syracuseStep 7514531 = 11271797) B11271797
theorem B1485219 : Blo 1484062 1485219 := bstep (se 1 (by rfl) ⟨1113914, by rfl⟩ : syracuseStep 1485219 = 2227829) B2227829
theorem B2410931 : Blo 1484062 2410931 := bstep (se 1 (by rfl) ⟨1808198, by rfl⟩ : syracuseStep 2410931 = 3616397) B3616397
theorem B1485235 : Blo 1484062 1485235 := bstep (se 1 (by rfl) ⟨1113926, by rfl⟩ : syracuseStep 1485235 = 2227853) B2227853
theorem B1485251 : Blo 1484062 1485251 := bstep (se 1 (by rfl) ⟨1113938, by rfl⟩ : syracuseStep 1485251 = 2227877) B2227877
theorem B1485267 : Blo 1484062 1485267 := bstep (se 1 (by rfl) ⟨1113950, by rfl⟩ : syracuseStep 1485267 = 2227901) B2227901
theorem B2378209 : Blo 1484062 2378209 := bstep (se 2 (by rfl) ⟨891828, by rfl⟩ : syracuseStep 2378209 = 1783657) B1783657
theorem B1485283 : Blo 1484062 1485283 := bstep (se 1 (by rfl) ⟨1113962, by rfl⟩ : syracuseStep 1485283 = 2227925) B2227925
theorem B1485299 : Blo 1484062 1485299 := bstep (se 1 (by rfl) ⟨1113974, by rfl⟩ : syracuseStep 1485299 = 2227949) B2227949
theorem B1485315 : Blo 1484062 1485315 := bstep (se 1 (by rfl) ⟨1113986, by rfl⟩ : syracuseStep 1485315 = 2227973) B2227973
theorem B1878547 : Blo 1484062 1878547 := bstep (se 1 (by rfl) ⟨1408910, by rfl⟩ : syracuseStep 1878547 = 2817821) B2817821
theorem B1485331 : Blo 1484062 1485331 := bstep (se 1 (by rfl) ⟨1113998, by rfl⟩ : syracuseStep 1485331 = 2227997) B2227997
theorem B1485347 : Blo 1484062 1485347 := bstep (se 1 (by rfl) ⟨1114010, by rfl⟩ : syracuseStep 1485347 = 2228021) B2228021
theorem B1485363 : Blo 1484062 1485363 := bstep (se 1 (by rfl) ⟨1114022, by rfl⟩ : syracuseStep 1485363 = 2228045) B2228045
theorem B1485379 : Blo 1484062 1485379 := bstep (se 1 (by rfl) ⟨1114034, by rfl⟩ : syracuseStep 1485379 = 2228069) B2228069
theorem B3172945 : Blo 1484062 3172945 := bstep (se 2 (by rfl) ⟨1189854, by rfl⟩ : syracuseStep 3172945 = 2379709) B2379709
theorem B1485395 : Blo 1484062 1485395 := bstep (se 1 (by rfl) ⟨1114046, by rfl⟩ : syracuseStep 1485395 = 2228093) B2228093
theorem B1485411 : Blo 1484062 1485411 := bstep (se 1 (by rfl) ⟨1114058, by rfl⟩ : syracuseStep 1485411 = 2228117) B2228117
theorem B1878643 : Blo 1484062 1878643 := bstep (se 1 (by rfl) ⟨1408982, by rfl⟩ : syracuseStep 1878643 = 2817965) B2817965
theorem B1485427 : Blo 1484062 1485427 := bstep (se 1 (by rfl) ⟨1114070, by rfl⟩ : syracuseStep 1485427 = 2228141) B2228141
theorem B1485443 : Blo 1484062 1485443 := bstep (se 1 (by rfl) ⟨1114082, by rfl⟩ : syracuseStep 1485443 = 2228165) B2228165
theorem B1485459 : Blo 1484062 1485459 := bstep (se 1 (by rfl) ⟨1114094, by rfl⟩ : syracuseStep 1485459 = 2228189) B2228189
theorem B5712547 : Blo 1484062 5712547 := bstep (se 1 (by rfl) ⟨4284410, by rfl⟩ : syracuseStep 5712547 = 8568821) B8568821
theorem B4229795 : Blo 1484062 4229795 := bstep (se 1 (by rfl) ⟨3172346, by rfl⟩ : syracuseStep 4229795 = 6344693) B6344693
theorem B1485475 : Blo 1484062 1485475 := bstep (se 1 (by rfl) ⟨1114106, by rfl⟩ : syracuseStep 1485475 = 2228213) B2228213
theorem B1485491 : Blo 1484062 1485491 := bstep (se 1 (by rfl) ⟨1114118, by rfl⟩ : syracuseStep 1485491 = 2228237) B2228237
theorem B1485507 : Blo 1484062 1485507 := bstep (se 1 (by rfl) ⟨1114130, by rfl⟩ : syracuseStep 1485507 = 2228261) B2228261
theorem B1485523 : Blo 1484062 1485523 := bstep (se 1 (by rfl) ⟨1114142, by rfl⟩ : syracuseStep 1485523 = 2228285) B2228285
theorem B1485539 : Blo 1484062 1485539 := bstep (se 1 (by rfl) ⟨1114154, by rfl⟩ : syracuseStep 1485539 = 2228309) B2228309
theorem B2820835 : Blo 1484062 2820835 := bstep (se 1 (by rfl) ⟨2115626, by rfl⟩ : syracuseStep 2820835 = 4231253) B4231253
theorem B1485555 : Blo 1484062 1485555 := bstep (se 1 (by rfl) ⟨1114166, by rfl⟩ : syracuseStep 1485555 = 2228333) B2228333
theorem B1485571 : Blo 1484062 1485571 := bstep (se 1 (by rfl) ⟨1114178, by rfl⟩ : syracuseStep 1485571 = 2228357) B2228357
theorem B2820881 : Blo 1484062 2820881 := bstep (se 2 (by rfl) ⟨1057830, by rfl⟩ : syracuseStep 2820881 = 2115661) B2115661
theorem B1485587 : Blo 1484062 1485587 := bstep (se 1 (by rfl) ⟨1114190, by rfl⟩ : syracuseStep 1485587 = 2228381) B2228381
theorem B5352227 : Blo 1484062 5352227 := bstep (se 1 (by rfl) ⟨4014170, by rfl⟩ : syracuseStep 5352227 = 8028341) B8028341
theorem B1485603 : Blo 1484062 1485603 := bstep (se 1 (by rfl) ⟨1114202, by rfl⟩ : syracuseStep 1485603 = 2228405) B2228405
theorem B1485619 : Blo 1484062 1485619 := bstep (se 1 (by rfl) ⟨1114214, by rfl⟩ : syracuseStep 1485619 = 2228429) B2228429
theorem B1485635 : Blo 1484062 1485635 := bstep (se 1 (by rfl) ⟨1114226, by rfl⟩ : syracuseStep 1485635 = 2228453) B2228453
theorem B1485651 : Blo 1484062 1485651 := bstep (se 1 (by rfl) ⟨1114238, by rfl⟩ : syracuseStep 1485651 = 2228477) B2228477
theorem B1485667 : Blo 1484062 1485667 := bstep (se 1 (by rfl) ⟨1114250, by rfl⟩ : syracuseStep 1485667 = 2228501) B2228501
theorem B1485683 : Blo 1484062 1485683 := bstep (se 1 (by rfl) ⟨1114262, by rfl⟩ : syracuseStep 1485683 = 2228525) B2228525
theorem B1485699 : Blo 1484062 1485699 := bstep (se 1 (by rfl) ⟨1114274, by rfl⟩ : syracuseStep 1485699 = 2228549) B2228549
theorem B8031109 : Blo 1484062 8031109 := bstep (se 4 (by rfl) ⟨752916, by rfl⟩ : syracuseStep 8031109 = 1505833) B1505833
theorem B1485715 : Blo 1484062 1485715 := bstep (se 1 (by rfl) ⟨1114286, by rfl⟩ : syracuseStep 1485715 = 2228573) B2228573
theorem B1485731 : Blo 1484062 1485731 := bstep (se 1 (by rfl) ⟨1114298, by rfl⟩ : syracuseStep 1485731 = 2228597) B2228597
theorem B1485747 : Blo 1484062 1485747 := bstep (se 1 (by rfl) ⟨1114310, by rfl⟩ : syracuseStep 1485747 = 2228621) B2228621
theorem B1485763 : Blo 1484062 1485763 := bstep (se 1 (by rfl) ⟨1114322, by rfl⟩ : syracuseStep 1485763 = 2228645) B2228645
theorem B1485779 : Blo 1484062 1485779 := bstep (se 1 (by rfl) ⟨1114334, by rfl⟩ : syracuseStep 1485779 = 2228669) B2228669
theorem B1485795 : Blo 1484062 1485795 := bstep (se 1 (by rfl) ⟨1114346, by rfl⟩ : syracuseStep 1485795 = 2228693) B2228693
theorem B1485811 : Blo 1484062 1485811 := bstep (se 1 (by rfl) ⟨1114358, by rfl⟩ : syracuseStep 1485811 = 2228717) B2228717
theorem B1485827 : Blo 1484062 1485827 := bstep (se 1 (by rfl) ⟨1114370, by rfl⟩ : syracuseStep 1485827 = 2228741) B2228741
theorem B1485843 : Blo 1484062 1485843 := bstep (se 1 (by rfl) ⟨1114382, by rfl⟩ : syracuseStep 1485843 = 2228765) B2228765
theorem B1485859 : Blo 1484062 1485859 := bstep (se 1 (by rfl) ⟨1114394, by rfl⟩ : syracuseStep 1485859 = 2228789) B2228789
theorem B2821169 : Blo 1484062 2821169 := bstep (se 2 (by rfl) ⟨1057938, by rfl⟩ : syracuseStep 2821169 = 2115877) B2115877
theorem B1485875 : Blo 1484062 1485875 := bstep (se 1 (by rfl) ⟨1114406, by rfl⟩ : syracuseStep 1485875 = 2228813) B2228813
theorem B1485891 : Blo 1484062 1485891 := bstep (se 1 (by rfl) ⟨1114418, by rfl⟩ : syracuseStep 1485891 = 2228837) B2228837
theorem B1485907 : Blo 1484062 1485907 := bstep (se 1 (by rfl) ⟨1114430, by rfl⟩ : syracuseStep 1485907 = 2228861) B2228861
theorem B1879139 : Blo 1484062 1879139 := bstep (se 1 (by rfl) ⟨1409354, by rfl⟩ : syracuseStep 1879139 = 2818709) B2818709
theorem B1485923 : Blo 1484062 1485923 := bstep (se 1 (by rfl) ⟨1114442, by rfl⟩ : syracuseStep 1485923 = 2228885) B2228885
theorem B1485939 : Blo 1484062 1485939 := bstep (se 1 (by rfl) ⟨1114454, by rfl⟩ : syracuseStep 1485939 = 2228909) B2228909
theorem B1485955 : Blo 1484062 1485955 := bstep (se 1 (by rfl) ⟨1114466, by rfl⟩ : syracuseStep 1485955 = 2228933) B2228933
theorem B1485971 : Blo 1484062 1485971 := bstep (se 1 (by rfl) ⟨1114478, by rfl⟩ : syracuseStep 1485971 = 2228957) B2228957
theorem B3050659 : Blo 1484062 3050659 := bstep (se 1 (by rfl) ⟨2287994, by rfl⟩ : syracuseStep 3050659 = 4575989) B4575989
theorem B1485987 : Blo 1484062 1485987 := bstep (se 1 (by rfl) ⟨1114490, by rfl⟩ : syracuseStep 1485987 = 2228981) B2228981
theorem B1486003 : Blo 1484062 1486003 := bstep (se 1 (by rfl) ⟨1114502, by rfl⟩ : syracuseStep 1486003 = 2229005) B2229005
theorem B1486019 : Blo 1484062 1486019 := bstep (se 1 (by rfl) ⟨1114514, by rfl⟩ : syracuseStep 1486019 = 2229029) B2229029
theorem B7515341 : Blo 1484062 7515341 := bstep (se 3 (by rfl) ⟨1409126, by rfl⟩ : syracuseStep 7515341 = 2818253) B2818253
theorem B1486035 : Blo 1484062 1486035 := bstep (se 1 (by rfl) ⟨1114526, by rfl⟩ : syracuseStep 1486035 = 2229053) B2229053
theorem B1486051 : Blo 1484062 1486051 := bstep (se 1 (by rfl) ⟨1114538, by rfl⟩ : syracuseStep 1486051 = 2229077) B2229077
theorem B2379107 : Blo 1484062 2379107 := bstep (se 1 (by rfl) ⟨1784330, by rfl⟩ : syracuseStep 2379107 = 3568661) B3568661
theorem B4287853 : Blo 1484062 4287853 := bstep (se 3 (by rfl) ⟨803972, by rfl⟩ : syracuseStep 4287853 = 1607945) B1607945
theorem B6344077 : Blo 1484062 6344077 := bstep (se 3 (by rfl) ⟨1189514, by rfl⟩ : syracuseStep 6344077 = 2379029) B2379029
theorem B5639651 : Blo 1484062 5639651 := bstep (se 1 (by rfl) ⟨4229738, by rfl⟩ : syracuseStep 5639651 = 8459477) B8459477
theorem B5008877 : Blo 1484062 5008877 := bstep (se 3 (by rfl) ⟨939164, by rfl⟩ : syracuseStep 5008877 = 1878329) B1878329
theorem B5639665 : Blo 1484062 5639665 := bstep (se 2 (by rfl) ⟨2114874, by rfl⟩ : syracuseStep 5639665 = 4229749) B4229749
theorem B5008931 : Blo 1484062 5008931 := bstep (se 1 (by rfl) ⟨3756698, by rfl⟩ : syracuseStep 5008931 = 7513397) B7513397
theorem B2379331 : Blo 1484062 2379331 := bstep (se 1 (by rfl) ⟨1784498, by rfl⟩ : syracuseStep 2379331 = 3568997) B3568997
theorem B18058949 : Blo 1484062 18058949 := bstep (se 4 (by rfl) ⟨1693026, by rfl⟩ : syracuseStep 18058949 = 3386053) B3386053
theorem B6344419 : Blo 1484062 6344419 := bstep (se 1 (by rfl) ⟨4758314, by rfl⟩ : syracuseStep 6344419 = 9516629) B9516629
theorem B8458019 : Blo 1484062 8458019 := bstep (se 1 (by rfl) ⟨6343514, by rfl⟩ : syracuseStep 8458019 = 12687029) B12687029
theorem B1879843 : Blo 1484062 1879843 := bstep (se 1 (by rfl) ⟨1409882, by rfl⟩ : syracuseStep 1879843 = 2819765) B2819765
theorem B5009201 : Blo 1484062 5009201 := bstep (se 2 (by rfl) ⟨1878450, by rfl⟩ : syracuseStep 5009201 = 3756901) B3756901
theorem B3387203 : Blo 1484062 3387203 := bstep (se 1 (by rfl) ⟨2540402, by rfl⟩ : syracuseStep 3387203 = 5080805) B5080805
theorem B13553477 : Blo 1484062 13553477 := bstep (se 4 (by rfl) ⟨1270638, by rfl⟩ : syracuseStep 13553477 = 2541277) B2541277
theorem B15249221 : Blo 1484062 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B4231025 : Blo 1484062 4231025 := bstep (se 2 (by rfl) ⟨1586634, by rfl⟩ : syracuseStep 4231025 = 3173269) B3173269
theorem B1879939 : Blo 1484062 1879939 := bstep (se 1 (by rfl) ⟨1409954, by rfl⟩ : syracuseStep 1879939 = 2819909) B2819909
theorem B4067281 : Blo 1484062 4067281 := bstep (se 2 (by rfl) ⟨1525230, by rfl⟩ : syracuseStep 4067281 = 3050461) B3050461
theorem B8024035 : Blo 1484062 8024035 := bstep (se 1 (by rfl) ⟨6018026, by rfl⟩ : syracuseStep 8024035 = 12036053) B12036053
theorem B1904675 : Blo 1484062 1904675 := bstep (se 1 (by rfl) ⟨1428506, by rfl⟩ : syracuseStep 1904675 = 2857013) B2857013
theorem B21418181 : Blo 1484062 21418181 := bstep (se 4 (by rfl) ⟨2007954, by rfl⟩ : syracuseStep 21418181 = 4015909) B4015909
theorem B1585379 : Blo 1484062 1585379 := bstep (se 1 (by rfl) ⟨1189034, by rfl⟩ : syracuseStep 1585379 = 2378069) B2378069
theorem B8687843 : Blo 1484062 8687843 := bstep (se 1 (by rfl) ⟨6515882, by rfl⟩ : syracuseStep 8687843 = 13031765) B13031765
theorem B4575523 : Blo 1484062 4575523 := bstep (se 1 (by rfl) ⟨3431642, by rfl⟩ : syracuseStep 4575523 = 6863285) B6863285
theorem B5009741 : Blo 1484062 5009741 := bstep (se 3 (by rfl) ⟨939326, by rfl⟩ : syracuseStep 5009741 = 1878653) B1878653
theorem B11276657 : Blo 1484062 11276657 := bstep (se 2 (by rfl) ⟨4228746, by rfl⟩ : syracuseStep 11276657 = 8457493) B8457493
theorem B1880435 : Blo 1484062 1880435 := bstep (se 1 (by rfl) ⟨1410326, by rfl⟩ : syracuseStep 1880435 = 2820653) B2820653
theorem B5009795 : Blo 1484062 5009795 := bstep (se 1 (by rfl) ⟨3757346, by rfl⟩ : syracuseStep 5009795 = 7514693) B7514693
theorem B22868365 : Blo 1484062 22868365 := bstep (se 3 (by rfl) ⟨4287818, by rfl⟩ : syracuseStep 22868365 = 8575637) B8575637
theorem B5083651 : Blo 1484062 5083651 := bstep (se 1 (by rfl) ⟨3812738, by rfl⟩ : syracuseStep 5083651 = 7625477) B7625477
theorem B9515555 : Blo 1484062 9515555 := bstep (se 1 (by rfl) ⟨7136666, by rfl⟩ : syracuseStep 9515555 = 14273333) B14273333
theorem B3011107 : Blo 1484062 3011107 := bstep (se 1 (by rfl) ⟨2258330, by rfl⟩ : syracuseStep 3011107 = 4516661) B4516661
theorem B2380337 : Blo 1484062 2380337 := bstep (se 2 (by rfl) ⟨892626, by rfl⟩ : syracuseStep 2380337 = 1785253) B1785253
theorem B21688885 : Blo 1484062 21688885 := bstep (se 5 (by rfl) ⟨1016666, by rfl⟩ : syracuseStep 21688885 = 2033333) B2033333
theorem B3756689 : Blo 1484062 3756689 := bstep (se 2 (by rfl) ⟨1408758, by rfl⟩ : syracuseStep 3756689 = 2817517) B2817517
theorem B5010065 : Blo 1484062 5010065 := bstep (se 2 (by rfl) ⟨1878774, by rfl⟩ : syracuseStep 5010065 = 3757549) B3757549
theorem B6771377 : Blo 1484062 6771377 := bstep (se 2 (by rfl) ⟨2539266, by rfl⟩ : syracuseStep 6771377 = 5078533) B5078533
theorem B3756739 : Blo 1484062 3756739 := bstep (se 1 (by rfl) ⟨2817554, by rfl⟩ : syracuseStep 3756739 = 5635109) B5635109
theorem B7140145 : Blo 1484062 7140145 := bstep (se 2 (by rfl) ⟨2677554, by rfl⟩ : syracuseStep 7140145 = 5355109) B5355109
theorem B3756881 : Blo 1484062 3756881 := bstep (se 2 (by rfl) ⟨1408830, by rfl⟩ : syracuseStep 3756881 = 2817661) B2817661
theorem B3093347 : Blo 1484062 3093347 := bstep (se 1 (by rfl) ⟨2320010, by rfl⟩ : syracuseStep 3093347 = 4640021) B4640021
theorem B5641123 : Blo 1484062 5641123 := bstep (se 1 (by rfl) ⟨4230842, by rfl⟩ : syracuseStep 5641123 = 8461685) B8461685
theorem B2257843 : Blo 1484062 2257843 := bstep (se 1 (by rfl) ⟨1693382, by rfl⟩ : syracuseStep 2257843 = 3386765) B3386765
theorem B8033357 : Blo 1484062 8033357 := bstep (se 3 (by rfl) ⟨1506254, by rfl⟩ : syracuseStep 8033357 = 3012509) B3012509
theorem B3339377 : Blo 1484062 3339377 := bstep (se 2 (by rfl) ⟨1252266, by rfl⟩ : syracuseStep 3339377 = 2504533) B2504533
theorem B3339395 : Blo 1484062 3339395 := bstep (se 1 (by rfl) ⟨2504546, by rfl⟩ : syracuseStep 3339395 = 5009093) B5009093
theorem B5010605 : Blo 1484062 5010605 := bstep (se 3 (by rfl) ⟨939488, by rfl⟩ : syracuseStep 5010605 = 1878977) B1878977
theorem B5010659 : Blo 1484062 5010659 := bstep (se 1 (by rfl) ⟨3757994, by rfl⟩ : syracuseStep 5010659 = 7515989) B7515989
theorem B1586515 : Blo 1484062 1586515 := bstep (se 1 (by rfl) ⟨1189886, by rfl⟩ : syracuseStep 1586515 = 2379773) B2379773
theorem B3339665 : Blo 1484062 3339665 := bstep (se 2 (by rfl) ⟨1252374, by rfl⟩ : syracuseStep 3339665 = 2504749) B2504749
theorem B3339683 : Blo 1484062 3339683 := bstep (se 1 (by rfl) ⟨2504762, by rfl⟩ : syracuseStep 3339683 = 5009525) B5009525
theorem B4756931 : Blo 1484062 4756931 := bstep (se 1 (by rfl) ⟨3567698, by rfl⟩ : syracuseStep 4756931 = 7135397) B7135397
theorem B5010929 : Blo 1484062 5010929 := bstep (se 2 (by rfl) ⟨1879098, by rfl⟩ : syracuseStep 5010929 = 3758197) B3758197
theorem B1906195 : Blo 1484062 1906195 := bstep (se 1 (by rfl) ⟨1429646, by rfl⟩ : syracuseStep 1906195 = 2859293) B2859293
theorem B4757059 : Blo 1484062 4757059 := bstep (se 1 (by rfl) ⟨3567794, by rfl⟩ : syracuseStep 4757059 = 7135589) B7135589
theorem B8459909 : Blo 1484062 8459909 := bstep (se 4 (by rfl) ⟨793116, by rfl⟩ : syracuseStep 8459909 = 1586233) B1586233
theorem B3339953 : Blo 1484062 3339953 := bstep (se 2 (by rfl) ⟨1252482, by rfl⟩ : syracuseStep 3339953 = 2504965) B2504965
theorem B2258609 : Blo 1484062 2258609 := bstep (se 2 (by rfl) ⟨846978, by rfl⟩ : syracuseStep 2258609 = 1693957) B1693957
theorem B2504371 : Blo 1484062 2504371 := bstep (se 1 (by rfl) ⟨1878278, by rfl⟩ : syracuseStep 2504371 = 3756557) B3756557
theorem B3339971 : Blo 1484062 3339971 := bstep (se 1 (by rfl) ⟨2504978, by rfl⟩ : syracuseStep 3339971 = 5009957) B5009957
theorem B44586773 : Blo 1484062 44586773 := bstep (se 6 (by rfl) ⟨1045002, by rfl⟩ : syracuseStep 44586773 = 2090005) B2090005
theorem B3757873 : Blo 1484062 3757873 := bstep (se 2 (by rfl) ⟨1409202, by rfl⟩ : syracuseStep 3757873 = 2818405) B2818405
theorem B2504513 : Blo 1484062 2504513 := bstep (se 2 (by rfl) ⟨939192, by rfl⟩ : syracuseStep 2504513 = 1878385) B1878385
theorem B5355341 : Blo 1484062 5355341 := bstep (se 3 (by rfl) ⟨1004126, by rfl⟩ : syracuseStep 5355341 = 2008253) B2008253
theorem B1783667 : Blo 1484062 1783667 := bstep (se 1 (by rfl) ⟨1337750, by rfl⟩ : syracuseStep 1783667 = 2675501) B2675501
theorem B4757393 : Blo 1484062 4757393 := bstep (se 2 (by rfl) ⟨1784022, by rfl⟩ : syracuseStep 4757393 = 3568045) B3568045
theorem B2226113 : Blo 1484062 2226113 := bstep (se 2 (by rfl) ⟨834792, by rfl⟩ : syracuseStep 2226113 = 1669585) B1669585
theorem B2504641 : Blo 1484062 2504641 := bstep (se 2 (by rfl) ⟨939240, by rfl⟩ : syracuseStep 2504641 = 1878481) B1878481
theorem B3340241 : Blo 1484062 3340241 := bstep (se 2 (by rfl) ⟨1252590, by rfl⟩ : syracuseStep 3340241 = 2505181) B2505181
theorem B2226131 : Blo 1484062 2226131 := bstep (se 1 (by rfl) ⟨1669598, by rfl⟩ : syracuseStep 2226131 = 3339197) B3339197
theorem B2504675 : Blo 1484062 2504675 := bstep (se 1 (by rfl) ⟨1878506, by rfl⟩ : syracuseStep 2504675 = 3757013) B3757013
theorem B3340259 : Blo 1484062 3340259 := bstep (se 1 (by rfl) ⟨2505194, by rfl⟩ : syracuseStep 3340259 = 5010389) B5010389
theorem B2226161 : Blo 1484062 2226161 := bstep (se 2 (by rfl) ⟨834810, by rfl⟩ : syracuseStep 2226161 = 1669621) B1669621
theorem B2226179 : Blo 1484062 2226179 := bstep (se 1 (by rfl) ⟨1669634, by rfl⟩ : syracuseStep 2226179 = 3339269) B3339269
theorem B5011469 : Blo 1484062 5011469 := bstep (se 3 (by rfl) ⟨939650, by rfl⟩ : syracuseStep 5011469 = 1879301) B1879301
theorem B13760525 : Blo 1484062 13760525 := bstep (se 3 (by rfl) ⟨2580098, by rfl⟩ : syracuseStep 13760525 = 5160197) B5160197
theorem B2226209 : Blo 1484062 2226209 := bstep (se 2 (by rfl) ⟨834828, by rfl⟩ : syracuseStep 2226209 = 1669657) B1669657
theorem B7518257 : Blo 1484062 7518257 := bstep (se 2 (by rfl) ⟨2819346, by rfl⟩ : syracuseStep 7518257 = 5638693) B5638693
theorem B2226227 : Blo 1484062 2226227 := bstep (se 1 (by rfl) ⟨1669670, by rfl⟩ : syracuseStep 2226227 = 3339341) B3339341
theorem B3758147 : Blo 1484062 3758147 := bstep (se 1 (by rfl) ⟨2818610, by rfl⟩ : syracuseStep 3758147 = 5637221) B5637221
theorem B5011523 : Blo 1484062 5011523 := bstep (se 1 (by rfl) ⟨3758642, by rfl⟩ : syracuseStep 5011523 = 7517285) B7517285
theorem B2226257 : Blo 1484062 2226257 := bstep (se 2 (by rfl) ⟨834846, by rfl⟩ : syracuseStep 2226257 = 1669693) B1669693
theorem B2226275 : Blo 1484062 2226275 := bstep (se 1 (by rfl) ⟨1669706, by rfl⟩ : syracuseStep 2226275 = 3339413) B3339413
theorem B2504803 : Blo 1484062 2504803 := bstep (se 1 (by rfl) ⟨1878602, by rfl⟩ : syracuseStep 2504803 = 3757205) B3757205
theorem B2226305 : Blo 1484062 2226305 := bstep (se 2 (by rfl) ⟨834864, by rfl⟩ : syracuseStep 2226305 = 1669729) B1669729
theorem B3569795 : Blo 1484062 3569795 := bstep (se 1 (by rfl) ⟨2677346, by rfl⟩ : syracuseStep 3569795 = 5354693) B5354693
theorem B2226323 : Blo 1484062 2226323 := bstep (se 1 (by rfl) ⟨1669742, by rfl⟩ : syracuseStep 2226323 = 3339485) B3339485
theorem B2226353 : Blo 1484062 2226353 := bstep (se 2 (by rfl) ⟨834882, by rfl⟩ : syracuseStep 2226353 = 1669765) B1669765
theorem B2226371 : Blo 1484062 2226371 := bstep (se 1 (by rfl) ⟨1669778, by rfl⟩ : syracuseStep 2226371 = 3339557) B3339557
theorem B3619025 : Blo 1484062 3619025 := bstep (se 2 (by rfl) ⟨1357134, by rfl⟩ : syracuseStep 3619025 = 2714269) B2714269
theorem B2226401 : Blo 1484062 2226401 := bstep (se 2 (by rfl) ⟨834900, by rfl⟩ : syracuseStep 2226401 = 1669801) B1669801
theorem B2504945 : Blo 1484062 2504945 := bstep (se 2 (by rfl) ⟨939354, by rfl⟩ : syracuseStep 2504945 = 1878709) B1878709
theorem B3340529 : Blo 1484062 3340529 := bstep (se 2 (by rfl) ⟨1252698, by rfl⟩ : syracuseStep 3340529 = 2505397) B2505397
theorem B2226419 : Blo 1484062 2226419 := bstep (se 1 (by rfl) ⟨1669814, by rfl⟩ : syracuseStep 2226419 = 3339629) B3339629
theorem B3340547 : Blo 1484062 3340547 := bstep (se 1 (by rfl) ⟨2505410, by rfl⟩ : syracuseStep 3340547 = 5010821) B5010821
theorem B3758339 : Blo 1484062 3758339 := bstep (se 1 (by rfl) ⟨2818754, by rfl⟩ : syracuseStep 3758339 = 5637509) B5637509
theorem B2226449 : Blo 1484062 2226449 := bstep (se 2 (by rfl) ⟨834918, by rfl⟩ : syracuseStep 2226449 = 1669837) B1669837
theorem B2226467 : Blo 1484062 2226467 := bstep (se 1 (by rfl) ⟨1669850, by rfl⟩ : syracuseStep 2226467 = 3339701) B3339701
theorem B2226497 : Blo 1484062 2226497 := bstep (se 2 (by rfl) ⟨834936, by rfl⟩ : syracuseStep 2226497 = 1669873) B1669873
theorem B4012355 : Blo 1484062 4012355 := bstep (se 1 (by rfl) ⟨3009266, by rfl⟩ : syracuseStep 4012355 = 6018533) B6018533
theorem B9509197 : Blo 1484062 9509197 := bstep (se 3 (by rfl) ⟨1782974, by rfl⟩ : syracuseStep 9509197 = 3565949) B3565949
theorem B5011793 : Blo 1484062 5011793 := bstep (se 2 (by rfl) ⟨1879422, by rfl⟩ : syracuseStep 5011793 = 3758845) B3758845
theorem B2226515 : Blo 1484062 2226515 := bstep (se 1 (by rfl) ⟨1669886, by rfl⟩ : syracuseStep 2226515 = 3339773) B3339773
theorem B2226545 : Blo 1484062 2226545 := bstep (se 2 (by rfl) ⟨834954, by rfl⟩ : syracuseStep 2226545 = 1669909) B1669909
theorem B2505073 : Blo 1484062 2505073 := bstep (se 2 (by rfl) ⟨939402, by rfl⟩ : syracuseStep 2505073 = 1878805) B1878805
theorem B2226563 : Blo 1484062 2226563 := bstep (se 1 (by rfl) ⟨1669922, by rfl⟩ : syracuseStep 2226563 = 3339845) B3339845
theorem B2505107 : Blo 1484062 2505107 := bstep (se 1 (by rfl) ⟨1878830, by rfl⟩ : syracuseStep 2505107 = 3757661) B3757661
theorem B2226593 : Blo 1484062 2226593 := bstep (se 2 (by rfl) ⟨834972, by rfl⟩ : syracuseStep 2226593 = 1669945) B1669945
theorem B2226611 : Blo 1484062 2226611 := bstep (se 1 (by rfl) ⟨1669958, by rfl⟩ : syracuseStep 2226611 = 3339917) B3339917
theorem B2226641 : Blo 1484062 2226641 := bstep (se 2 (by rfl) ⟨834990, by rfl⟩ : syracuseStep 2226641 = 1669981) B1669981
theorem B1669603 : Blo 1484062 1669603 := bstep (se 1 (by rfl) ⟨1252202, by rfl⟩ : syracuseStep 1669603 = 2504405) B2504405
theorem B2226659 : Blo 1484062 2226659 := bstep (se 1 (by rfl) ⟨1669994, by rfl⟩ : syracuseStep 2226659 = 3339989) B3339989
theorem B16062947 : Blo 1484062 16062947 := bstep (se 1 (by rfl) ⟨12047210, by rfl⟩ : syracuseStep 16062947 = 24094421) B24094421
theorem B2226689 : Blo 1484062 2226689 := bstep (se 2 (by rfl) ⟨835008, by rfl⟩ : syracuseStep 2226689 = 1670017) B1670017
theorem B2857475 : Blo 1484062 2857475 := bstep (se 1 (by rfl) ⟨2143106, by rfl⟩ : syracuseStep 2857475 = 4286213) B4286213
theorem B3340817 : Blo 1484062 3340817 := bstep (se 2 (by rfl) ⟨1252806, by rfl⟩ : syracuseStep 3340817 = 2505613) B2505613
theorem B2226707 : Blo 1484062 2226707 := bstep (se 1 (by rfl) ⟨1670030, by rfl⟩ : syracuseStep 2226707 = 3340061) B3340061
theorem B2505235 : Blo 1484062 2505235 := bstep (se 1 (by rfl) ⟨1878926, by rfl⟩ : syracuseStep 2505235 = 3757853) B3757853
theorem B3340835 : Blo 1484062 3340835 := bstep (se 1 (by rfl) ⟨2505626, by rfl⟩ : syracuseStep 3340835 = 5011253) B5011253
theorem B2226737 : Blo 1484062 2226737 := bstep (se 2 (by rfl) ⟨835026, by rfl⟩ : syracuseStep 2226737 = 1670053) B1670053
theorem B2226755 : Blo 1484062 2226755 := bstep (se 1 (by rfl) ⟨1670066, by rfl⟩ : syracuseStep 2226755 = 3340133) B3340133
theorem B19036741 : Blo 1484062 19036741 := bstep (se 4 (by rfl) ⟨1784694, by rfl⟩ : syracuseStep 19036741 = 3569389) B3569389
theorem B2226785 : Blo 1484062 2226785 := bstep (se 2 (by rfl) ⟨835044, by rfl⟩ : syracuseStep 2226785 = 1670089) B1670089
theorem B1669747 : Blo 1484062 1669747 := bstep (se 1 (by rfl) ⟨1252310, by rfl⟩ : syracuseStep 1669747 = 2504621) B2504621
theorem B2226803 : Blo 1484062 2226803 := bstep (se 1 (by rfl) ⟨1670102, by rfl⟩ : syracuseStep 2226803 = 3340205) B3340205
theorem B2226833 : Blo 1484062 2226833 := bstep (se 2 (by rfl) ⟨835062, by rfl⟩ : syracuseStep 2226833 = 1670125) B1670125
theorem B2505377 : Blo 1484062 2505377 := bstep (se 2 (by rfl) ⟨939516, by rfl⟩ : syracuseStep 2505377 = 1879033) B1879033
theorem B2226851 : Blo 1484062 2226851 := bstep (se 1 (by rfl) ⟨1670138, by rfl⟩ : syracuseStep 2226851 = 3340277) B3340277
theorem B2226881 : Blo 1484062 2226881 := bstep (se 2 (by rfl) ⟨835080, by rfl⟩ : syracuseStep 2226881 = 1670161) B1670161
theorem B4012753 : Blo 1484062 4012753 := bstep (se 2 (by rfl) ⟨1504782, by rfl⟩ : syracuseStep 4012753 = 3009565) B3009565
theorem B2226899 : Blo 1484062 2226899 := bstep (se 1 (by rfl) ⟨1670174, by rfl⟩ : syracuseStep 2226899 = 3340349) B3340349
theorem B2677475 : Blo 1484062 2677475 := bstep (se 1 (by rfl) ⟨2008106, by rfl⟩ : syracuseStep 2677475 = 4016213) B4016213
theorem B2226929 : Blo 1484062 2226929 := bstep (se 2 (by rfl) ⟨835098, by rfl⟩ : syracuseStep 2226929 = 1670197) B1670197
theorem B1669891 : Blo 1484062 1669891 := bstep (se 1 (by rfl) ⟨1252418, by rfl⟩ : syracuseStep 1669891 = 2504837) B2504837
theorem B2226947 : Blo 1484062 2226947 := bstep (se 1 (by rfl) ⟨1670210, by rfl⟩ : syracuseStep 2226947 = 3340421) B3340421
theorem B2226977 : Blo 1484062 2226977 := bstep (se 2 (by rfl) ⟨835116, by rfl⟩ : syracuseStep 2226977 = 1670233) B1670233
theorem B2505505 : Blo 1484062 2505505 := bstep (se 2 (by rfl) ⟨939564, by rfl⟩ : syracuseStep 2505505 = 1879129) B1879129
theorem B3341105 : Blo 1484062 3341105 := bstep (se 2 (by rfl) ⟨1252914, by rfl⟩ : syracuseStep 3341105 = 2505829) B2505829
theorem B2226995 : Blo 1484062 2226995 := bstep (se 1 (by rfl) ⟨1670246, by rfl⟩ : syracuseStep 2226995 = 3340493) B3340493
theorem B2505539 : Blo 1484062 2505539 := bstep (se 1 (by rfl) ⟨1879154, by rfl⟩ : syracuseStep 2505539 = 3758309) B3758309
theorem B3341123 : Blo 1484062 3341123 := bstep (se 1 (by rfl) ⟨2505842, by rfl⟩ : syracuseStep 3341123 = 5011685) B5011685
theorem B2227025 : Blo 1484062 2227025 := bstep (se 2 (by rfl) ⟨835134, by rfl⟩ : syracuseStep 2227025 = 1670269) B1670269
theorem B2227043 : Blo 1484062 2227043 := bstep (se 1 (by rfl) ⟨1670282, by rfl⟩ : syracuseStep 2227043 = 3340565) B3340565
theorem B5012333 : Blo 1484062 5012333 := bstep (se 3 (by rfl) ⟨939812, by rfl⟩ : syracuseStep 5012333 = 1879625) B1879625
theorem B2227073 : Blo 1484062 2227073 := bstep (se 2 (by rfl) ⟨835152, by rfl⟩ : syracuseStep 2227073 = 1670305) B1670305
theorem B3570563 : Blo 1484062 3570563 := bstep (se 1 (by rfl) ⟨2677922, by rfl⟩ : syracuseStep 3570563 = 5355845) B5355845
theorem B1670035 : Blo 1484062 1670035 := bstep (se 1 (by rfl) ⟨1252526, by rfl⟩ : syracuseStep 1670035 = 2505053) B2505053
theorem B2227091 : Blo 1484062 2227091 := bstep (se 1 (by rfl) ⟨1670318, by rfl⟩ : syracuseStep 2227091 = 3340637) B3340637
theorem B5012387 : Blo 1484062 5012387 := bstep (se 1 (by rfl) ⟨3759290, by rfl⟩ : syracuseStep 5012387 = 7518581) B7518581
theorem B2227121 : Blo 1484062 2227121 := bstep (se 2 (by rfl) ⟨835170, by rfl⟩ : syracuseStep 2227121 = 1670341) B1670341
theorem B2227139 : Blo 1484062 2227139 := bstep (se 1 (by rfl) ⟨1670354, by rfl⟩ : syracuseStep 2227139 = 3340709) B3340709
theorem B2505667 : Blo 1484062 2505667 := bstep (se 1 (by rfl) ⟨1879250, by rfl⟩ : syracuseStep 2505667 = 3758501) B3758501
theorem B10705861 : Blo 1484062 10705861 := bstep (se 4 (by rfl) ⟨1003674, by rfl⟩ : syracuseStep 10705861 = 2007349) B2007349
theorem B4578257 : Blo 1484062 4578257 := bstep (se 2 (by rfl) ⟨1716846, by rfl⟩ : syracuseStep 4578257 = 3433693) B3433693
theorem B2227169 : Blo 1484062 2227169 := bstep (se 2 (by rfl) ⟨835188, by rfl⟩ : syracuseStep 2227169 = 1670377) B1670377
theorem B2227187 : Blo 1484062 2227187 := bstep (se 1 (by rfl) ⟨1670390, by rfl⟩ : syracuseStep 2227187 = 3340781) B3340781
theorem B2227217 : Blo 1484062 2227217 := bstep (se 2 (by rfl) ⟨835206, by rfl⟩ : syracuseStep 2227217 = 1670413) B1670413
theorem B1670179 : Blo 1484062 1670179 := bstep (se 1 (by rfl) ⟨1252634, by rfl⟩ : syracuseStep 1670179 = 2505269) B2505269
theorem B2227235 : Blo 1484062 2227235 := bstep (se 1 (by rfl) ⟨1670426, by rfl⟩ : syracuseStep 2227235 = 3340853) B3340853
theorem B2227265 : Blo 1484062 2227265 := bstep (se 2 (by rfl) ⟨835224, by rfl⟩ : syracuseStep 2227265 = 1670449) B1670449
theorem B2505809 : Blo 1484062 2505809 := bstep (se 2 (by rfl) ⟨939678, by rfl⟩ : syracuseStep 2505809 = 1879357) B1879357
theorem B3341393 : Blo 1484062 3341393 := bstep (se 2 (by rfl) ⟨1253022, by rfl⟩ : syracuseStep 3341393 = 2506045) B2506045
theorem B2227283 : Blo 1484062 2227283 := bstep (se 1 (by rfl) ⟨1670462, by rfl⟩ : syracuseStep 2227283 = 3340925) B3340925
theorem B3341411 : Blo 1484062 3341411 := bstep (se 1 (by rfl) ⟨2506058, by rfl⟩ : syracuseStep 3341411 = 5012117) B5012117
theorem B2227313 : Blo 1484062 2227313 := bstep (se 2 (by rfl) ⟨835242, by rfl⟩ : syracuseStep 2227313 = 1670485) B1670485
theorem B2227331 : Blo 1484062 2227331 := bstep (se 1 (by rfl) ⟨1670498, by rfl⟩ : syracuseStep 2227331 = 3340997) B3340997
theorem B2227361 : Blo 1484062 2227361 := bstep (se 2 (by rfl) ⟨835260, by rfl⟩ : syracuseStep 2227361 = 1670521) B1670521
theorem B3759281 : Blo 1484062 3759281 := bstep (se 2 (by rfl) ⟨1409730, by rfl⟩ : syracuseStep 3759281 = 2819461) B2819461
theorem B5012657 : Blo 1484062 5012657 := bstep (se 2 (by rfl) ⟨1879746, by rfl⟩ : syracuseStep 5012657 = 3759493) B3759493
theorem B1670323 : Blo 1484062 1670323 := bstep (se 1 (by rfl) ⟨1252742, by rfl⟩ : syracuseStep 1670323 = 2505485) B2505485
theorem B2227379 : Blo 1484062 2227379 := bstep (se 1 (by rfl) ⟨1670534, by rfl⟩ : syracuseStep 2227379 = 3341069) B3341069
theorem B14277829 : Blo 1484062 14277829 := bstep (se 4 (by rfl) ⟨1338546, by rfl⟩ : syracuseStep 14277829 = 2677093) B2677093
theorem B5635277 : Blo 1484062 5635277 := bstep (se 3 (by rfl) ⟨1056614, by rfl⟩ : syracuseStep 5635277 = 2113229) B2113229
theorem B2227409 : Blo 1484062 2227409 := bstep (se 2 (by rfl) ⟨835278, by rfl⟩ : syracuseStep 2227409 = 1670557) B1670557
theorem B2505937 : Blo 1484062 2505937 := bstep (se 2 (by rfl) ⟨939726, by rfl⟩ : syracuseStep 2505937 = 1879453) B1879453
theorem B2227427 : Blo 1484062 2227427 := bstep (se 1 (by rfl) ⟨1670570, by rfl⟩ : syracuseStep 2227427 = 3341141) B3341141
theorem B3759331 : Blo 1484062 3759331 := bstep (se 1 (by rfl) ⟨2819498, by rfl⟩ : syracuseStep 3759331 = 5638997) B5638997
theorem B2505971 : Blo 1484062 2505971 := bstep (se 1 (by rfl) ⟨1879478, by rfl⟩ : syracuseStep 2505971 = 3758957) B3758957
theorem B2227457 : Blo 1484062 2227457 := bstep (se 2 (by rfl) ⟨835296, by rfl⟩ : syracuseStep 2227457 = 1670593) B1670593
theorem B2858243 : Blo 1484062 2858243 := bstep (se 1 (by rfl) ⟨2143682, by rfl⟩ : syracuseStep 2858243 = 4287365) B4287365
theorem B2227475 : Blo 1484062 2227475 := bstep (se 1 (by rfl) ⟨1670606, by rfl⟩ : syracuseStep 2227475 = 3341213) B3341213
theorem B2227505 : Blo 1484062 2227505 := bstep (se 2 (by rfl) ⟨835314, by rfl⟩ : syracuseStep 2227505 = 1670629) B1670629
theorem B1670467 : Blo 1484062 1670467 := bstep (se 1 (by rfl) ⟨1252850, by rfl⟩ : syracuseStep 1670467 = 2505701) B2505701
theorem B2227523 : Blo 1484062 2227523 := bstep (se 1 (by rfl) ⟨1670642, by rfl⟩ : syracuseStep 2227523 = 3341285) B3341285
theorem B2227553 : Blo 1484062 2227553 := bstep (se 2 (by rfl) ⟨835332, by rfl⟩ : syracuseStep 2227553 = 1670665) B1670665
theorem B3341681 : Blo 1484062 3341681 := bstep (se 2 (by rfl) ⟨1253130, by rfl⟩ : syracuseStep 3341681 = 2506261) B2506261
theorem B3759473 : Blo 1484062 3759473 := bstep (se 2 (by rfl) ⟨1409802, by rfl⟩ : syracuseStep 3759473 = 2819605) B2819605
theorem B2227571 : Blo 1484062 2227571 := bstep (se 1 (by rfl) ⟨1670678, by rfl⟩ : syracuseStep 2227571 = 3341357) B3341357
theorem B2506099 : Blo 1484062 2506099 := bstep (se 1 (by rfl) ⟨1879574, by rfl⟩ : syracuseStep 2506099 = 3759149) B3759149
theorem B3341699 : Blo 1484062 3341699 := bstep (se 1 (by rfl) ⟨2506274, by rfl⟩ : syracuseStep 3341699 = 5012549) B5012549
theorem B2227601 : Blo 1484062 2227601 := bstep (se 2 (by rfl) ⟨835350, by rfl⟩ : syracuseStep 2227601 = 1670701) B1670701
theorem B2227619 : Blo 1484062 2227619 := bstep (se 1 (by rfl) ⟨1670714, by rfl⟩ : syracuseStep 2227619 = 3341429) B3341429
theorem B2227649 : Blo 1484062 2227649 := bstep (se 2 (by rfl) ⟨835368, by rfl⟩ : syracuseStep 2227649 = 1670737) B1670737
theorem B6340045 : Blo 1484062 6340045 := bstep (se 3 (by rfl) ⟨1188758, by rfl⟩ : syracuseStep 6340045 = 2377517) B2377517
theorem B4513229 : Blo 1484062 4513229 := bstep (se 3 (by rfl) ⟨846230, by rfl⟩ : syracuseStep 4513229 = 1692461) B1692461
theorem B1670611 : Blo 1484062 1670611 := bstep (se 1 (by rfl) ⟨1252958, by rfl⟩ : syracuseStep 1670611 = 2505917) B2505917
theorem B2227667 : Blo 1484062 2227667 := bstep (se 1 (by rfl) ⟨1670750, by rfl⟩ : syracuseStep 2227667 = 3341501) B3341501
theorem B7519715 : Blo 1484062 7519715 := bstep (se 1 (by rfl) ⟨5639786, by rfl⟩ : syracuseStep 7519715 = 11279573) B11279573
theorem B2227697 : Blo 1484062 2227697 := bstep (se 2 (by rfl) ⟨835386, by rfl⟩ : syracuseStep 2227697 = 1670773) B1670773
theorem B2506241 : Blo 1484062 2506241 := bstep (se 2 (by rfl) ⟨939840, by rfl⟩ : syracuseStep 2506241 = 1879681) B1879681
theorem B2227715 : Blo 1484062 2227715 := bstep (se 1 (by rfl) ⟨1670786, by rfl⟩ : syracuseStep 2227715 = 3341573) B3341573
theorem B8453645 : Blo 1484062 8453645 := bstep (se 3 (by rfl) ⟨1585058, by rfl⟩ : syracuseStep 8453645 = 3170117) B3170117
theorem B2227745 : Blo 1484062 2227745 := bstep (se 2 (by rfl) ⟨835404, by rfl⟩ : syracuseStep 2227745 = 1670809) B1670809
theorem B2113075 : Blo 1484062 2113075 := bstep (se 1 (by rfl) ⟨1584806, by rfl⟩ : syracuseStep 2113075 = 3169613) B3169613
theorem B2227763 : Blo 1484062 2227763 := bstep (se 1 (by rfl) ⟨1670822, by rfl⟩ : syracuseStep 2227763 = 3341645) B3341645
theorem B2227793 : Blo 1484062 2227793 := bstep (se 2 (by rfl) ⟨835422, by rfl⟩ : syracuseStep 2227793 = 1670845) B1670845
theorem B1670755 : Blo 1484062 1670755 := bstep (se 1 (by rfl) ⟨1253066, by rfl⟩ : syracuseStep 1670755 = 2506133) B2506133
theorem B2227811 : Blo 1484062 2227811 := bstep (se 1 (by rfl) ⟨1670858, by rfl⟩ : syracuseStep 2227811 = 3341717) B3341717
theorem B2227841 : Blo 1484062 2227841 := bstep (se 2 (by rfl) ⟨835440, by rfl⟩ : syracuseStep 2227841 = 1670881) B1670881
theorem B2506369 : Blo 1484062 2506369 := bstep (se 2 (by rfl) ⟨939888, by rfl⟩ : syracuseStep 2506369 = 1879777) B1879777
theorem B3341969 : Blo 1484062 3341969 := bstep (se 2 (by rfl) ⟨1253238, by rfl⟩ : syracuseStep 3341969 = 2506477) B2506477
theorem B2227859 : Blo 1484062 2227859 := bstep (se 1 (by rfl) ⟨1670894, by rfl⟩ : syracuseStep 2227859 = 3341789) B3341789
theorem B3169955 : Blo 1484062 3169955 := bstep (se 1 (by rfl) ⟨2377466, by rfl⟩ : syracuseStep 3169955 = 4754933) B4754933
theorem B2506403 : Blo 1484062 2506403 := bstep (se 1 (by rfl) ⟨1879802, by rfl⟩ : syracuseStep 2506403 = 3759605) B3759605
theorem B3341987 : Blo 1484062 3341987 := bstep (se 1 (by rfl) ⟨2506490, by rfl⟩ : syracuseStep 3341987 = 5012981) B5012981
theorem B2227889 : Blo 1484062 2227889 := bstep (se 2 (by rfl) ⟨835458, by rfl⟩ : syracuseStep 2227889 = 1670917) B1670917
theorem B2227907 : Blo 1484062 2227907 := bstep (se 1 (by rfl) ⟨1670930, by rfl⟩ : syracuseStep 2227907 = 3341861) B3341861
theorem B5013197 : Blo 1484062 5013197 := bstep (se 3 (by rfl) ⟨939974, by rfl⟩ : syracuseStep 5013197 = 1879949) B1879949
theorem B2227937 : Blo 1484062 2227937 := bstep (se 2 (by rfl) ⟨835476, by rfl⟩ : syracuseStep 2227937 = 1670953) B1670953
theorem B1670899 : Blo 1484062 1670899 := bstep (se 1 (by rfl) ⟨1253174, by rfl⟩ : syracuseStep 1670899 = 2506349) B2506349
theorem B2227955 : Blo 1484062 2227955 := bstep (se 1 (by rfl) ⟨1670966, by rfl⟩ : syracuseStep 2227955 = 3341933) B3341933
theorem B5013251 : Blo 1484062 5013251 := bstep (se 1 (by rfl) ⟨3759938, by rfl⟩ : syracuseStep 5013251 = 7519877) B7519877
theorem B4226833 : Blo 1484062 4226833 := bstep (se 2 (by rfl) ⟨1585062, by rfl⟩ : syracuseStep 4226833 = 3170125) B3170125
theorem B2227985 : Blo 1484062 2227985 := bstep (se 2 (by rfl) ⟨835494, by rfl⟩ : syracuseStep 2227985 = 1670989) B1670989
theorem B2228003 : Blo 1484062 2228003 := bstep (se 1 (by rfl) ⟨1671002, by rfl⟩ : syracuseStep 2228003 = 3342005) B3342005
theorem B2506531 : Blo 1484062 2506531 := bstep (se 1 (by rfl) ⟨1879898, by rfl⟩ : syracuseStep 2506531 = 3759797) B3759797
theorem B2228033 : Blo 1484062 2228033 := bstep (se 2 (by rfl) ⟨835512, by rfl⟩ : syracuseStep 2228033 = 1671025) B1671025
theorem B2228051 : Blo 1484062 2228051 := bstep (se 1 (by rfl) ⟨1671038, by rfl⟩ : syracuseStep 2228051 = 3342077) B3342077
theorem B2228081 : Blo 1484062 2228081 := bstep (se 2 (by rfl) ⟨835530, by rfl⟩ : syracuseStep 2228081 = 1671061) B1671061
theorem B1671043 : Blo 1484062 1671043 := bstep (se 1 (by rfl) ⟨1253282, by rfl⟩ : syracuseStep 1671043 = 2506565) B2506565
theorem B2228099 : Blo 1484062 2228099 := bstep (se 1 (by rfl) ⟨1671074, by rfl⟩ : syracuseStep 2228099 = 3342149) B3342149
theorem B2228129 : Blo 1484062 2228129 := bstep (se 2 (by rfl) ⟨835548, by rfl⟩ : syracuseStep 2228129 = 1671097) B1671097
theorem B2506673 : Blo 1484062 2506673 := bstep (se 2 (by rfl) ⟨940002, by rfl⟩ : syracuseStep 2506673 = 1880005) B1880005
theorem B3342257 : Blo 1484062 3342257 := bstep (se 2 (by rfl) ⟨1253346, by rfl⟩ : syracuseStep 3342257 = 2506693) B2506693
theorem B2228147 : Blo 1484062 2228147 := bstep (se 1 (by rfl) ⟨1671110, by rfl⟩ : syracuseStep 2228147 = 3342221) B3342221
theorem B3342275 : Blo 1484062 3342275 := bstep (se 1 (by rfl) ⟨2506706, by rfl⟩ : syracuseStep 3342275 = 5013413) B5013413
theorem B2228177 : Blo 1484062 2228177 := bstep (se 2 (by rfl) ⟨835566, by rfl⟩ : syracuseStep 2228177 = 1671133) B1671133
theorem B4513763 : Blo 1484062 4513763 := bstep (se 1 (by rfl) ⟨3385322, by rfl⟩ : syracuseStep 4513763 = 6770645) B6770645
theorem B2228195 : Blo 1484062 2228195 := bstep (se 1 (by rfl) ⟨1671146, by rfl⟩ : syracuseStep 2228195 = 3342293) B3342293
theorem B5636081 : Blo 1484062 5636081 := bstep (se 2 (by rfl) ⟨2113530, by rfl⟩ : syracuseStep 5636081 = 4227061) B4227061
theorem B3342347 : Blo 1484062 3342347 := bstep (se 1 (by rfl) ⟨2506760, by rfl⟩ : syracuseStep 3342347 = 5013521) B5013521
theorem B2228249 : Blo 1484062 2228249 := bstep (se 2 (by rfl) ⟨835593, by rfl⟩ : syracuseStep 2228249 = 1671187) B1671187
theorem B1671223 : Blo 1484062 1671223 := bstep (se 1 (by rfl) ⟨1253417, by rfl⟩ : syracuseStep 1671223 = 2506835) B2506835
theorem B3342401 : Blo 1484062 3342401 := bstep (se 2 (by rfl) ⟨1253400, by rfl⟩ : syracuseStep 3342401 = 2506801) B2506801
theorem B5079133 : Blo 1484062 5079133 := bstep (se 3 (by rfl) ⟨952337, by rfl⟩ : syracuseStep 5079133 = 1904675) B1904675
theorem B14278787 : Blo 1484062 14278787 := bstep (se 1 (by rfl) ⟨10709090, by rfl⟩ : syracuseStep 14278787 = 21418181) B21418181
theorem B2228363 : Blo 1484062 2228363 := bstep (se 1 (by rfl) ⟨1671272, by rfl⟩ : syracuseStep 2228363 = 3342545) B3342545
theorem B5791895 : Blo 1484062 5791895 := bstep (se 1 (by rfl) ⟨4343921, by rfl⟩ : syracuseStep 5791895 = 8687843) B8687843
theorem B2228375 : Blo 1484062 2228375 := bstep (se 1 (by rfl) ⟨1671281, by rfl⟩ : syracuseStep 2228375 = 3342563) B3342563
theorem B6340781 : Blo 1484062 6340781 := bstep (se 3 (by rfl) ⟨1188896, by rfl⟩ : syracuseStep 6340781 = 2377793) B2377793
theorem B5013683 : Blo 1484062 5013683 := bstep (se 1 (by rfl) ⟨3760262, by rfl⟩ : syracuseStep 5013683 = 7520525) B7520525
theorem B2228441 : Blo 1484062 2228441 := bstep (se 2 (by rfl) ⟨835665, by rfl⟩ : syracuseStep 2228441 = 1671331) B1671331
theorem B1671403 : Blo 1484062 1671403 := bstep (se 1 (by rfl) ⟨1253552, by rfl⟩ : syracuseStep 1671403 = 2507105) B2507105
theorem B3342617 : Blo 1484062 3342617 := bstep (se 2 (by rfl) ⟨1253481, by rfl⟩ : syracuseStep 3342617 = 2506963) B2506963
theorem B10707245 : Blo 1484062 10707245 := bstep (se 3 (by rfl) ⟨2007608, by rfl⟩ : syracuseStep 10707245 = 4015217) B4015217
theorem B4227403 : Blo 1484062 4227403 := bstep (se 1 (by rfl) ⟨3170552, by rfl⟩ : syracuseStep 4227403 = 6341105) B6341105
theorem B2113867 : Blo 1484062 2113867 := bstep (se 1 (by rfl) ⟨1585400, by rfl⟩ : syracuseStep 2113867 = 3170801) B3170801
theorem B2228555 : Blo 1484062 2228555 := bstep (se 1 (by rfl) ⟨1671416, by rfl⟩ : syracuseStep 2228555 = 3342833) B3342833
theorem B2228567 : Blo 1484062 2228567 := bstep (se 1 (by rfl) ⟨1671425, by rfl⟩ : syracuseStep 2228567 = 3342851) B3342851
theorem B1671511 : Blo 1484062 1671511 := bstep (se 1 (by rfl) ⟨1253633, by rfl⟩ : syracuseStep 1671511 = 2507267) B2507267
theorem B3342707 : Blo 1484062 3342707 := bstep (se 1 (by rfl) ⟨2507030, by rfl⟩ : syracuseStep 3342707 = 5014061) B5014061
theorem B3342743 : Blo 1484062 3342743 := bstep (se 1 (by rfl) ⟨2507057, by rfl⟩ : syracuseStep 3342743 = 5014115) B5014115
theorem B2507159 : Blo 1484062 2507159 := bstep (se 1 (by rfl) ⟨1880369, by rfl⟩ : syracuseStep 2507159 = 3760739) B3760739
theorem B2228633 : Blo 1484062 2228633 := bstep (se 2 (by rfl) ⟨835737, by rfl⟩ : syracuseStep 2228633 = 1671475) B1671475
theorem B5013953 : Blo 1484062 5013953 := bstep (se 2 (by rfl) ⟨1880232, by rfl⟩ : syracuseStep 5013953 = 3760465) B3760465
theorem B3760577 : Blo 1484062 3760577 := bstep (se 2 (by rfl) ⟨1410216, by rfl⟩ : syracuseStep 3760577 = 2820433) B2820433
theorem B4514251 : Blo 1484062 4514251 := bstep (se 1 (by rfl) ⟨3385688, by rfl⟩ : syracuseStep 4514251 = 6771377) B6771377
theorem B2228747 : Blo 1484062 2228747 := bstep (se 1 (by rfl) ⟨1671560, by rfl⟩ : syracuseStep 2228747 = 3343121) B3343121
theorem B1671691 : Blo 1484062 1671691 := bstep (se 1 (by rfl) ⟨1253768, by rfl⟩ : syracuseStep 1671691 = 2507537) B2507537
theorem B30491153 : Blo 1484062 30491153 := bstep (se 2 (by rfl) ⟨11434182, by rfl⟩ : syracuseStep 30491153 = 22868365) B22868365
theorem B2507287 : Blo 1484062 2507287 := bstep (se 1 (by rfl) ⟨1880465, by rfl⟩ : syracuseStep 2507287 = 3760931) B3760931
theorem B2228759 : Blo 1484062 2228759 := bstep (se 1 (by rfl) ⟨1671569, by rfl⟩ : syracuseStep 2228759 = 3343139) B3343139
theorem B11272769 : Blo 1484062 11272769 := bstep (se 2 (by rfl) ⟨4227288, by rfl⟩ : syracuseStep 11272769 = 8454577) B8454577
theorem B3342923 : Blo 1484062 3342923 := bstep (se 1 (by rfl) ⟨2507192, by rfl⟩ : syracuseStep 3342923 = 5014385) B5014385
theorem B2228825 : Blo 1484062 2228825 := bstep (se 2 (by rfl) ⟨835809, by rfl⟩ : syracuseStep 2228825 = 1671619) B1671619
theorem B4227677 : Blo 1484062 4227677 := bstep (se 3 (by rfl) ⟨792689, by rfl⟩ : syracuseStep 4227677 = 1585379) B1585379
theorem B1671799 : Blo 1484062 1671799 := bstep (se 1 (by rfl) ⟨1253849, by rfl⟩ : syracuseStep 1671799 = 2507699) B2507699
theorem B3170945 : Blo 1484062 3170945 := bstep (se 2 (by rfl) ⟨1189104, by rfl⟩ : syracuseStep 3170945 = 2378209) B2378209
theorem B3342977 : Blo 1484062 3342977 := bstep (se 2 (by rfl) ⟨1253616, by rfl⟩ : syracuseStep 3342977 = 2507233) B2507233
theorem B2818739 : Blo 1484062 2818739 := bstep (se 1 (by rfl) ⟨2114054, by rfl⟩ : syracuseStep 2818739 = 4228109) B4228109
theorem B2228939 : Blo 1484062 2228939 := bstep (se 1 (by rfl) ⟨1671704, by rfl⟩ : syracuseStep 2228939 = 3343409) B3343409
theorem B2228951 : Blo 1484062 2228951 := bstep (se 1 (by rfl) ⟨1671713, by rfl⟩ : syracuseStep 2228951 = 3343427) B3343427
theorem B4014809 : Blo 1484062 4014809 := bstep (se 2 (by rfl) ⟨1505553, by rfl⟩ : syracuseStep 4014809 = 3011107) B3011107
theorem B28918513 : Blo 1484062 28918513 := bstep (se 2 (by rfl) ⟨10844442, by rfl⟩ : syracuseStep 28918513 = 21688885) B21688885
theorem B2229017 : Blo 1484062 2229017 := bstep (se 2 (by rfl) ⟨835881, by rfl⟩ : syracuseStep 2229017 = 1671763) B1671763
theorem B2818891 : Blo 1484062 2818891 := bstep (se 1 (by rfl) ⟨2114168, by rfl⟩ : syracuseStep 2818891 = 4228337) B4228337
theorem B3343193 : Blo 1484062 3343193 := bstep (se 2 (by rfl) ⟨1253697, by rfl⟩ : syracuseStep 3343193 = 2507395) B2507395
theorem B3343283 : Blo 1484062 3343283 := bstep (se 1 (by rfl) ⟨2507462, by rfl⟩ : syracuseStep 3343283 = 5014925) B5014925
theorem B5350337 : Blo 1484062 5350337 := bstep (se 2 (by rfl) ⟨2006376, by rfl⟩ : syracuseStep 5350337 = 4012753) B4012753
theorem B2540491 : Blo 1484062 2540491 := bstep (se 1 (by rfl) ⟨1905368, by rfl⟩ : syracuseStep 2540491 = 3810737) B3810737
theorem B3171287 : Blo 1484062 3171287 := bstep (se 1 (by rfl) ⟨2378465, by rfl⟩ : syracuseStep 3171287 = 4756931) B4756931
theorem B3343319 : Blo 1484062 3343319 := bstep (se 1 (by rfl) ⟨2507489, by rfl⟩ : syracuseStep 3343319 = 5014979) B5014979
theorem B3761113 : Blo 1484062 3761113 := bstep (se 2 (by rfl) ⟨1410417, by rfl⟩ : syracuseStep 3761113 = 2820835) B2820835
theorem B5014493 : Blo 1484062 5014493 := bstep (se 3 (by rfl) ⟨940217, by rfl⟩ : syracuseStep 5014493 = 1880435) B1880435
theorem B10159121 : Blo 1484062 10159121 := bstep (se 2 (by rfl) ⟨3809670, by rfl⟩ : syracuseStep 10159121 = 7619341) B7619341
theorem B9520193 : Blo 1484062 9520193 := bstep (se 2 (by rfl) ⟨3570072, by rfl⟩ : syracuseStep 9520193 = 7140145) B7140145
theorem B3343499 : Blo 1484062 3343499 := bstep (se 1 (by rfl) ⟨2507624, by rfl⟩ : syracuseStep 3343499 = 5015249) B5015249
theorem B2819225 : Blo 1484062 2819225 := bstep (se 2 (by rfl) ⟨1057209, by rfl⟩ : syracuseStep 2819225 = 2114419) B2114419
theorem B10708145 : Blo 1484062 10708145 := bstep (se 2 (by rfl) ⟨4015554, by rfl⟩ : syracuseStep 10708145 = 8031109) B8031109
theorem B3343553 : Blo 1484062 3343553 := bstep (se 2 (by rfl) ⟨1253832, by rfl⟩ : syracuseStep 3343553 = 2507665) B2507665
theorem B7521497 : Blo 1484062 7521497 := bstep (se 2 (by rfl) ⟨2820561, by rfl⟩ : syracuseStep 7521497 = 5641123) B5641123
theorem B3171595 : Blo 1484062 3171595 := bstep (se 1 (by rfl) ⟨2378696, by rfl⟩ : syracuseStep 3171595 = 4757393) B4757393
theorem B1484075 : Blo 1484062 1484075 := bstep (se 1 (by rfl) ⟨1113056, by rfl⟩ : syracuseStep 1484075 = 2226113) B2226113
theorem B1484087 : Blo 1484062 1484087 := bstep (se 1 (by rfl) ⟨1113065, by rfl⟩ : syracuseStep 1484087 = 2226131) B2226131
theorem B1484107 : Blo 1484062 1484107 := bstep (se 1 (by rfl) ⟨1113080, by rfl⟩ : syracuseStep 1484107 = 2226161) B2226161
theorem B4015435 : Blo 1484062 4015435 := bstep (se 1 (by rfl) ⟨3011576, by rfl⟩ : syracuseStep 4015435 = 6023153) B6023153
theorem B1484119 : Blo 1484062 1484119 := bstep (se 1 (by rfl) ⟨1113089, by rfl⟩ : syracuseStep 1484119 = 2226179) B2226179
theorem B7619933 : Blo 1484062 7619933 := bstep (se 3 (by rfl) ⟨1428737, by rfl⟩ : syracuseStep 7619933 = 2857475) B2857475
theorem B1484139 : Blo 1484062 1484139 := bstep (se 1 (by rfl) ⟨1113104, by rfl⟩ : syracuseStep 1484139 = 2226209) B2226209
theorem B1484151 : Blo 1484062 1484151 := bstep (se 1 (by rfl) ⟨1113113, by rfl⟩ : syracuseStep 1484151 = 2226227) B2226227
theorem B1484171 : Blo 1484062 1484171 := bstep (se 1 (by rfl) ⟨1113128, by rfl⟩ : syracuseStep 1484171 = 2226257) B2226257
theorem B1484183 : Blo 1484062 1484183 := bstep (se 1 (by rfl) ⟨1113137, by rfl⟩ : syracuseStep 1484183 = 2226275) B2226275
theorem B1484203 : Blo 1484062 1484203 := bstep (se 1 (by rfl) ⟨1113152, by rfl⟩ : syracuseStep 1484203 = 2226305) B2226305
theorem B1484215 : Blo 1484062 1484215 := bstep (se 1 (by rfl) ⟨1113161, by rfl⟩ : syracuseStep 1484215 = 2226323) B2226323
theorem B1484235 : Blo 1484062 1484235 := bstep (se 1 (by rfl) ⟨1113176, by rfl⟩ : syracuseStep 1484235 = 2226353) B2226353
theorem B1484247 : Blo 1484062 1484247 := bstep (se 1 (by rfl) ⟨1113185, by rfl⟩ : syracuseStep 1484247 = 2226371) B2226371
theorem B1484267 : Blo 1484062 1484267 := bstep (se 1 (by rfl) ⟨1113200, by rfl⟩ : syracuseStep 1484267 = 2226401) B2226401
theorem B1484279 : Blo 1484062 1484279 := bstep (se 1 (by rfl) ⟨1113209, by rfl⟩ : syracuseStep 1484279 = 2226419) B2226419
theorem B1484299 : Blo 1484062 1484299 := bstep (se 1 (by rfl) ⟨1113224, by rfl⟩ : syracuseStep 1484299 = 2226449) B2226449
theorem B1484311 : Blo 1484062 1484311 := bstep (se 1 (by rfl) ⟨1113233, by rfl⟩ : syracuseStep 1484311 = 2226467) B2226467
theorem B1484331 : Blo 1484062 1484331 := bstep (se 1 (by rfl) ⟨1113248, by rfl⟩ : syracuseStep 1484331 = 2226497) B2226497
theorem B1484343 : Blo 1484062 1484343 := bstep (se 1 (by rfl) ⟨1113257, by rfl⟩ : syracuseStep 1484343 = 2226515) B2226515
theorem B1484363 : Blo 1484062 1484363 := bstep (se 1 (by rfl) ⟨1113272, by rfl⟩ : syracuseStep 1484363 = 2226545) B2226545
theorem B5637707 : Blo 1484062 5637707 := bstep (se 1 (by rfl) ⟨4228280, by rfl⟩ : syracuseStep 5637707 = 8456561) B8456561
theorem B1484375 : Blo 1484062 1484375 := bstep (se 1 (by rfl) ⟨1113281, by rfl⟩ : syracuseStep 1484375 = 2226563) B2226563
theorem B5637721 : Blo 1484062 5637721 := bstep (se 2 (by rfl) ⟨2114145, by rfl⟩ : syracuseStep 5637721 = 4228291) B4228291
theorem B1484395 : Blo 1484062 1484395 := bstep (se 1 (by rfl) ⟨1113296, by rfl⟩ : syracuseStep 1484395 = 2226593) B2226593
theorem B1484407 : Blo 1484062 1484407 := bstep (se 1 (by rfl) ⟨1113305, by rfl⟩ : syracuseStep 1484407 = 2226611) B2226611
theorem B1484427 : Blo 1484062 1484427 := bstep (se 1 (by rfl) ⟨1113320, by rfl⟩ : syracuseStep 1484427 = 2226641) B2226641
theorem B1484439 : Blo 1484062 1484439 := bstep (se 1 (by rfl) ⟨1113329, by rfl⟩ : syracuseStep 1484439 = 2226659) B2226659
theorem B10708631 : Blo 1484062 10708631 := bstep (se 1 (by rfl) ⟨8031473, by rfl⟩ : syracuseStep 10708631 = 16062947) B16062947
theorem B1484459 : Blo 1484062 1484459 := bstep (se 1 (by rfl) ⟨1113344, by rfl⟩ : syracuseStep 1484459 = 2226689) B2226689
theorem B1484471 : Blo 1484062 1484471 := bstep (se 1 (by rfl) ⟨1113353, by rfl⟩ : syracuseStep 1484471 = 2226707) B2226707
theorem B1484491 : Blo 1484062 1484491 := bstep (se 1 (by rfl) ⟨1113368, by rfl⟩ : syracuseStep 1484491 = 2226737) B2226737
theorem B1484503 : Blo 1484062 1484503 := bstep (se 1 (by rfl) ⟨1113377, by rfl⟩ : syracuseStep 1484503 = 2226755) B2226755
theorem B1484523 : Blo 1484062 1484523 := bstep (se 1 (by rfl) ⟨1113392, by rfl⟩ : syracuseStep 1484523 = 2226785) B2226785
theorem B1484535 : Blo 1484062 1484535 := bstep (se 1 (by rfl) ⟨1113401, by rfl⟩ : syracuseStep 1484535 = 2226803) B2226803
theorem B1484555 : Blo 1484062 1484555 := bstep (se 1 (by rfl) ⟨1113416, by rfl⟩ : syracuseStep 1484555 = 2226833) B2226833
theorem B1484567 : Blo 1484062 1484567 := bstep (se 1 (by rfl) ⟨1113425, by rfl⟩ : syracuseStep 1484567 = 2226851) B2226851
theorem B2819863 : Blo 1484062 2819863 := bstep (se 1 (by rfl) ⟨2114897, by rfl⟩ : syracuseStep 2819863 = 4229795) B4229795
theorem B2115353 : Blo 1484062 2115353 := bstep (se 2 (by rfl) ⟨793257, by rfl⟩ : syracuseStep 2115353 = 1586515) B1586515
theorem B1484587 : Blo 1484062 1484587 := bstep (se 1 (by rfl) ⟨1113440, by rfl⟩ : syracuseStep 1484587 = 2226881) B2226881
theorem B6022957 : Blo 1484062 6022957 := bstep (se 3 (by rfl) ⟨1129304, by rfl⟩ : syracuseStep 6022957 = 2258609) B2258609
theorem B1484599 : Blo 1484062 1484599 := bstep (se 1 (by rfl) ⟨1113449, by rfl⟩ : syracuseStep 1484599 = 2226899) B2226899
theorem B1484619 : Blo 1484062 1484619 := bstep (se 1 (by rfl) ⟨1113464, by rfl⟩ : syracuseStep 1484619 = 2226929) B2226929
theorem B1484631 : Blo 1484062 1484631 := bstep (se 1 (by rfl) ⟨1113473, by rfl⟩ : syracuseStep 1484631 = 2226947) B2226947
theorem B1484651 : Blo 1484062 1484651 := bstep (se 1 (by rfl) ⟨1113488, by rfl⟩ : syracuseStep 1484651 = 2226977) B2226977
theorem B1484663 : Blo 1484062 1484663 := bstep (se 1 (by rfl) ⟨1113497, by rfl⟩ : syracuseStep 1484663 = 2226995) B2226995
theorem B1484683 : Blo 1484062 1484683 := bstep (se 1 (by rfl) ⟨1113512, by rfl⟩ : syracuseStep 1484683 = 2227025) B2227025
theorem B1484695 : Blo 1484062 1484695 := bstep (se 1 (by rfl) ⟨1113521, by rfl⟩ : syracuseStep 1484695 = 2227043) B2227043
theorem B1484715 : Blo 1484062 1484715 := bstep (se 1 (by rfl) ⟨1113536, by rfl⟩ : syracuseStep 1484715 = 2227073) B2227073
theorem B1484727 : Blo 1484062 1484727 := bstep (se 1 (by rfl) ⟨1113545, by rfl⟩ : syracuseStep 1484727 = 2227091) B2227091
theorem B1484747 : Blo 1484062 1484747 := bstep (se 1 (by rfl) ⟨1113560, by rfl⟩ : syracuseStep 1484747 = 2227121) B2227121
theorem B1484759 : Blo 1484062 1484759 := bstep (se 1 (by rfl) ⟨1113569, by rfl⟩ : syracuseStep 1484759 = 2227139) B2227139
theorem B1484779 : Blo 1484062 1484779 := bstep (se 1 (by rfl) ⟨1113584, by rfl⟩ : syracuseStep 1484779 = 2227169) B2227169
theorem B1484791 : Blo 1484062 1484791 := bstep (se 1 (by rfl) ⟨1113593, by rfl⟩ : syracuseStep 1484791 = 2227187) B2227187
theorem B1484811 : Blo 1484062 1484811 := bstep (se 1 (by rfl) ⟨1113608, by rfl⟩ : syracuseStep 1484811 = 2227217) B2227217
theorem B1484823 : Blo 1484062 1484823 := bstep (se 1 (by rfl) ⟨1113617, by rfl⟩ : syracuseStep 1484823 = 2227235) B2227235
theorem B2541593 : Blo 1484062 2541593 := bstep (se 2 (by rfl) ⟨953097, by rfl⟩ : syracuseStep 2541593 = 1906195) B1906195
theorem B1484843 : Blo 1484062 1484843 := bstep (se 1 (by rfl) ⟨1113632, by rfl⟩ : syracuseStep 1484843 = 2227265) B2227265
theorem B1484855 : Blo 1484062 1484855 := bstep (se 1 (by rfl) ⟨1113641, by rfl⟩ : syracuseStep 1484855 = 2227283) B2227283
theorem B1484875 : Blo 1484062 1484875 := bstep (se 1 (by rfl) ⟨1113656, by rfl⟩ : syracuseStep 1484875 = 2227313) B2227313
theorem B1484887 : Blo 1484062 1484887 := bstep (se 1 (by rfl) ⟨1113665, by rfl⟩ : syracuseStep 1484887 = 2227331) B2227331
theorem B6342745 : Blo 1484062 6342745 := bstep (se 2 (by rfl) ⟨2378529, by rfl⟩ : syracuseStep 6342745 = 4757059) B4757059
theorem B3172441 : Blo 1484062 3172441 := bstep (se 2 (by rfl) ⟨1189665, by rfl⟩ : syracuseStep 3172441 = 2379331) B2379331
theorem B1484907 : Blo 1484062 1484907 := bstep (se 1 (by rfl) ⟨1113680, by rfl⟩ : syracuseStep 1484907 = 2227361) B2227361
theorem B1484919 : Blo 1484062 1484919 := bstep (se 1 (by rfl) ⟨1113689, by rfl⟩ : syracuseStep 1484919 = 2227379) B2227379
theorem B1484939 : Blo 1484062 1484939 := bstep (se 1 (by rfl) ⟨1113704, by rfl⟩ : syracuseStep 1484939 = 2227409) B2227409
theorem B1484951 : Blo 1484062 1484951 := bstep (se 1 (by rfl) ⟨1113713, by rfl⟩ : syracuseStep 1484951 = 2227427) B2227427
theorem B1484971 : Blo 1484062 1484971 := bstep (se 1 (by rfl) ⟨1113728, by rfl⟩ : syracuseStep 1484971 = 2227457) B2227457
theorem B1484983 : Blo 1484062 1484983 := bstep (se 1 (by rfl) ⟨1113737, by rfl⟩ : syracuseStep 1484983 = 2227475) B2227475
theorem B1485003 : Blo 1484062 1485003 := bstep (se 1 (by rfl) ⟨1113752, by rfl⟩ : syracuseStep 1485003 = 2227505) B2227505
theorem B1485015 : Blo 1484062 1485015 := bstep (se 1 (by rfl) ⟨1113761, by rfl⟩ : syracuseStep 1485015 = 2227523) B2227523
theorem B1485035 : Blo 1484062 1485035 := bstep (se 1 (by rfl) ⟨1113776, by rfl⟩ : syracuseStep 1485035 = 2227553) B2227553
theorem B1485047 : Blo 1484062 1485047 := bstep (se 1 (by rfl) ⟨1113785, by rfl⟩ : syracuseStep 1485047 = 2227571) B2227571
theorem B1485067 : Blo 1484062 1485067 := bstep (se 1 (by rfl) ⟨1113800, by rfl⟩ : syracuseStep 1485067 = 2227601) B2227601
theorem B1485079 : Blo 1484062 1485079 := bstep (se 1 (by rfl) ⟨1113809, by rfl⟩ : syracuseStep 1485079 = 2227619) B2227619
theorem B1485099 : Blo 1484062 1485099 := bstep (se 1 (by rfl) ⟨1113824, by rfl⟩ : syracuseStep 1485099 = 2227649) B2227649
theorem B3008819 : Blo 1484062 3008819 := bstep (se 1 (by rfl) ⟨2256614, by rfl⟩ : syracuseStep 3008819 = 4513229) B4513229
theorem B1485111 : Blo 1484062 1485111 := bstep (se 1 (by rfl) ⟨1113833, by rfl⟩ : syracuseStep 1485111 = 2227667) B2227667
theorem B1485131 : Blo 1484062 1485131 := bstep (se 1 (by rfl) ⟨1113848, by rfl⟩ : syracuseStep 1485131 = 2227697) B2227697
theorem B1485143 : Blo 1484062 1485143 := bstep (se 1 (by rfl) ⟨1113857, by rfl⟩ : syracuseStep 1485143 = 2227715) B2227715
theorem B1485163 : Blo 1484062 1485163 := bstep (se 1 (by rfl) ⟨1113872, by rfl⟩ : syracuseStep 1485163 = 2227745) B2227745
theorem B1485175 : Blo 1484062 1485175 := bstep (se 1 (by rfl) ⟨1113881, by rfl⟩ : syracuseStep 1485175 = 2227763) B2227763
theorem B1485195 : Blo 1484062 1485195 := bstep (se 1 (by rfl) ⟨1113896, by rfl⟩ : syracuseStep 1485195 = 2227793) B2227793
theorem B1485207 : Blo 1484062 1485207 := bstep (se 1 (by rfl) ⟨1113905, by rfl⟩ : syracuseStep 1485207 = 2227811) B2227811
theorem B1485227 : Blo 1484062 1485227 := bstep (se 1 (by rfl) ⟨1113920, by rfl⟩ : syracuseStep 1485227 = 2227841) B2227841
theorem B1485239 : Blo 1484062 1485239 := bstep (se 1 (by rfl) ⟨1113929, by rfl⟩ : syracuseStep 1485239 = 2227859) B2227859
theorem B1485259 : Blo 1484062 1485259 := bstep (se 1 (by rfl) ⟨1113944, by rfl⟩ : syracuseStep 1485259 = 2227889) B2227889
theorem B1485271 : Blo 1484062 1485271 := bstep (se 1 (by rfl) ⟨1113953, by rfl⟩ : syracuseStep 1485271 = 2227907) B2227907
theorem B11274713 : Blo 1484062 11274713 := bstep (se 2 (by rfl) ⟨4228017, by rfl⟩ : syracuseStep 11274713 = 8456035) B8456035
theorem B1485291 : Blo 1484062 1485291 := bstep (se 1 (by rfl) ⟨1113968, by rfl⟩ : syracuseStep 1485291 = 2227937) B2227937
theorem B1485303 : Blo 1484062 1485303 := bstep (se 1 (by rfl) ⟨1113977, by rfl⟩ : syracuseStep 1485303 = 2227955) B2227955
theorem B1485323 : Blo 1484062 1485323 := bstep (se 1 (by rfl) ⟨1113992, by rfl⟩ : syracuseStep 1485323 = 2227985) B2227985
theorem B5638679 : Blo 1484062 5638679 := bstep (se 1 (by rfl) ⟨4229009, by rfl⟩ : syracuseStep 5638679 = 8458019) B8458019
theorem B1485335 : Blo 1484062 1485335 := bstep (se 1 (by rfl) ⟨1114001, by rfl⟩ : syracuseStep 1485335 = 2228003) B2228003
theorem B1485355 : Blo 1484062 1485355 := bstep (se 1 (by rfl) ⟨1114016, by rfl⟩ : syracuseStep 1485355 = 2228033) B2228033
theorem B1485367 : Blo 1484062 1485367 := bstep (se 1 (by rfl) ⟨1114025, by rfl⟩ : syracuseStep 1485367 = 2228051) B2228051
theorem B1485387 : Blo 1484062 1485387 := bstep (se 1 (by rfl) ⟨1114040, by rfl⟩ : syracuseStep 1485387 = 2228081) B2228081
theorem B2820683 : Blo 1484062 2820683 := bstep (se 1 (by rfl) ⟨2115512, by rfl⟩ : syracuseStep 2820683 = 4231025) B4231025
theorem B1485399 : Blo 1484062 1485399 := bstep (se 1 (by rfl) ⟨1114049, by rfl⟩ : syracuseStep 1485399 = 2228099) B2228099
theorem B12036701 : Blo 1484062 12036701 := bstep (se 3 (by rfl) ⟨2256881, by rfl⟩ : syracuseStep 12036701 = 4513763) B4513763
theorem B1485419 : Blo 1484062 1485419 := bstep (se 1 (by rfl) ⟨1114064, by rfl⟩ : syracuseStep 1485419 = 2228129) B2228129
theorem B1485431 : Blo 1484062 1485431 := bstep (se 1 (by rfl) ⟨1114073, by rfl⟩ : syracuseStep 1485431 = 2228147) B2228147
theorem B2820737 : Blo 1484062 2820737 := bstep (se 2 (by rfl) ⟨1057776, by rfl⟩ : syracuseStep 2820737 = 2115553) B2115553
theorem B1485451 : Blo 1484062 1485451 := bstep (se 1 (by rfl) ⟨1114088, by rfl⟩ : syracuseStep 1485451 = 2228177) B2228177
theorem B1485463 : Blo 1484062 1485463 := bstep (se 1 (by rfl) ⟨1114097, by rfl⟩ : syracuseStep 1485463 = 2228195) B2228195
theorem B1485483 : Blo 1484062 1485483 := bstep (se 1 (by rfl) ⟨1114112, by rfl⟩ : syracuseStep 1485483 = 2228225) B2228225
theorem B1485495 : Blo 1484062 1485495 := bstep (se 1 (by rfl) ⟨1114121, by rfl⟩ : syracuseStep 1485495 = 2228243) B2228243
theorem B1485515 : Blo 1484062 1485515 := bstep (se 1 (by rfl) ⟨1114136, by rfl⟩ : syracuseStep 1485515 = 2228273) B2228273
theorem B1485527 : Blo 1484062 1485527 := bstep (se 1 (by rfl) ⟨1114145, by rfl⟩ : syracuseStep 1485527 = 2228291) B2228291
theorem B2714327 : Blo 1484062 2714327 := bstep (se 1 (by rfl) ⟨2035745, by rfl⟩ : syracuseStep 2714327 = 4071491) B4071491
theorem B9644761 : Blo 1484062 9644761 := bstep (se 2 (by rfl) ⟨3616785, by rfl⟩ : syracuseStep 9644761 = 7233571) B7233571
theorem B1485547 : Blo 1484062 1485547 := bstep (se 1 (by rfl) ⟨1114160, by rfl⟩ : syracuseStep 1485547 = 2228321) B2228321
theorem B1485559 : Blo 1484062 1485559 := bstep (se 1 (by rfl) ⟨1114169, by rfl⟩ : syracuseStep 1485559 = 2228339) B2228339
theorem B1485579 : Blo 1484062 1485579 := bstep (se 1 (by rfl) ⟨1114184, by rfl⟩ : syracuseStep 1485579 = 2228369) B2228369
theorem B1485591 : Blo 1484062 1485591 := bstep (se 1 (by rfl) ⟨1114193, by rfl⟩ : syracuseStep 1485591 = 2228387) B2228387
theorem B1485611 : Blo 1484062 1485611 := bstep (se 1 (by rfl) ⟨1114208, by rfl⟩ : syracuseStep 1485611 = 2228417) B2228417
theorem B7523117 : Blo 1484062 7523117 := bstep (se 3 (by rfl) ⟨1410584, by rfl⟩ : syracuseStep 7523117 = 2821169) B2821169
theorem B1485623 : Blo 1484062 1485623 := bstep (se 1 (by rfl) ⟨1114217, by rfl⟩ : syracuseStep 1485623 = 2228435) B2228435
theorem B8031041 : Blo 1484062 8031041 := bstep (se 2 (by rfl) ⟨3011640, by rfl⟩ : syracuseStep 8031041 = 6023281) B6023281
theorem B1485643 : Blo 1484062 1485643 := bstep (se 1 (by rfl) ⟨1114232, by rfl⟩ : syracuseStep 1485643 = 2228465) B2228465
theorem B1878871 : Blo 1484062 1878871 := bstep (se 1 (by rfl) ⟨1409153, by rfl⟩ : syracuseStep 1878871 = 2818307) B2818307
theorem B1485655 : Blo 1484062 1485655 := bstep (se 1 (by rfl) ⟨1114241, by rfl⟩ : syracuseStep 1485655 = 2228483) B2228483
theorem B4229977 : Blo 1484062 4229977 := bstep (se 2 (by rfl) ⟨1586241, by rfl⟩ : syracuseStep 4229977 = 3172483) B3172483
theorem B1485675 : Blo 1484062 1485675 := bstep (se 1 (by rfl) ⟨1114256, by rfl⟩ : syracuseStep 1485675 = 2228513) B2228513
theorem B1485687 : Blo 1484062 1485687 := bstep (se 1 (by rfl) ⟨1114265, by rfl⟩ : syracuseStep 1485687 = 2228531) B2228531
theorem B1485707 : Blo 1484062 1485707 := bstep (se 1 (by rfl) ⟨1114280, by rfl⟩ : syracuseStep 1485707 = 2228561) B2228561
theorem B1485719 : Blo 1484062 1485719 := bstep (se 1 (by rfl) ⟨1114289, by rfl⟩ : syracuseStep 1485719 = 2228579) B2228579
theorem B1485739 : Blo 1484062 1485739 := bstep (se 1 (by rfl) ⟨1114304, by rfl⟩ : syracuseStep 1485739 = 2228609) B2228609
theorem B1485751 : Blo 1484062 1485751 := bstep (se 1 (by rfl) ⟨1114313, by rfl⟩ : syracuseStep 1485751 = 2228627) B2228627
theorem B1485771 : Blo 1484062 1485771 := bstep (se 1 (by rfl) ⟨1114328, by rfl⟩ : syracuseStep 1485771 = 2228657) B2228657
theorem B1485783 : Blo 1484062 1485783 := bstep (se 1 (by rfl) ⟨1114337, by rfl⟩ : syracuseStep 1485783 = 2228675) B2228675
theorem B1485803 : Blo 1484062 1485803 := bstep (se 1 (by rfl) ⟨1114352, by rfl⟩ : syracuseStep 1485803 = 2228705) B2228705
theorem B1485815 : Blo 1484062 1485815 := bstep (se 1 (by rfl) ⟨1114361, by rfl⟩ : syracuseStep 1485815 = 2228723) B2228723
theorem B11283461 : Blo 1484062 11283461 := bstep (se 4 (by rfl) ⟨1057824, by rfl⟩ : syracuseStep 11283461 = 2115649) B2115649
theorem B1485835 : Blo 1484062 1485835 := bstep (se 1 (by rfl) ⟨1114376, by rfl⟩ : syracuseStep 1485835 = 2228753) B2228753
theorem B6343703 : Blo 1484062 6343703 := bstep (se 1 (by rfl) ⟨4757777, by rfl⟩ : syracuseStep 6343703 = 9515555) B9515555
theorem B1485847 : Blo 1484062 1485847 := bstep (se 1 (by rfl) ⟨1114385, by rfl⟩ : syracuseStep 1485847 = 2228771) B2228771
theorem B1485867 : Blo 1484062 1485867 := bstep (se 1 (by rfl) ⟨1114400, by rfl⟩ : syracuseStep 1485867 = 2228801) B2228801
theorem B1485879 : Blo 1484062 1485879 := bstep (se 1 (by rfl) ⟨1114409, by rfl⟩ : syracuseStep 1485879 = 2228819) B2228819
theorem B4754497 : Blo 1484062 4754497 := bstep (se 2 (by rfl) ⟨1782936, by rfl⟩ : syracuseStep 4754497 = 3565873) B3565873
theorem B1485899 : Blo 1484062 1485899 := bstep (se 1 (by rfl) ⟨1114424, by rfl⟩ : syracuseStep 1485899 = 2228849) B2228849
theorem B1485911 : Blo 1484062 1485911 := bstep (se 1 (by rfl) ⟨1114433, by rfl⟩ : syracuseStep 1485911 = 2228867) B2228867
theorem B1485931 : Blo 1484062 1485931 := bstep (se 1 (by rfl) ⟨1114448, by rfl⟩ : syracuseStep 1485931 = 2228897) B2228897
theorem B1485943 : Blo 1484062 1485943 := bstep (se 1 (by rfl) ⟨1114457, by rfl⟩ : syracuseStep 1485943 = 2228915) B2228915
theorem B1485963 : Blo 1484062 1485963 := bstep (se 1 (by rfl) ⟨1114472, by rfl⟩ : syracuseStep 1485963 = 2228945) B2228945
theorem B1485975 : Blo 1484062 1485975 := bstep (se 1 (by rfl) ⟨1114481, by rfl⟩ : syracuseStep 1485975 = 2228963) B2228963
theorem B1485995 : Blo 1484062 1485995 := bstep (se 1 (by rfl) ⟨1114496, by rfl⟩ : syracuseStep 1485995 = 2228993) B2228993
theorem B1486007 : Blo 1484062 1486007 := bstep (se 1 (by rfl) ⟨1114505, by rfl⟩ : syracuseStep 1486007 = 2229011) B2229011
theorem B1486027 : Blo 1484062 1486027 := bstep (se 1 (by rfl) ⟨1114520, by rfl⟩ : syracuseStep 1486027 = 2229041) B2229041
theorem B1486039 : Blo 1484062 1486039 := bstep (se 1 (by rfl) ⟨1114529, by rfl⟩ : syracuseStep 1486039 = 2229059) B2229059
theorem B5221597 : Blo 1484062 5221597 := bstep (se 3 (by rfl) ⟨979049, by rfl⟩ : syracuseStep 5221597 = 1958099) B1958099
theorem B1486059 : Blo 1484062 1486059 := bstep (se 1 (by rfl) ⟨1114544, by rfl⟩ : syracuseStep 1486059 = 2229089) B2229089
theorem B12692801 : Blo 1484062 12692801 := bstep (se 2 (by rfl) ⟨4759800, by rfl⟩ : syracuseStep 12692801 = 9519601) B9519601
theorem B5008715 : Blo 1484062 5008715 := bstep (se 1 (by rfl) ⟨3756536, by rfl⟩ : syracuseStep 5008715 = 7513073) B7513073
theorem B6778201 : Blo 1484062 6778201 := bstep (se 2 (by rfl) ⟨2541825, by rfl⟩ : syracuseStep 6778201 = 5083651) B5083651
theorem B3173747 : Blo 1484062 3173747 := bstep (se 1 (by rfl) ⟨2380310, by rfl⟩ : syracuseStep 3173747 = 4760621) B4760621
theorem B25382321 : Blo 1484062 25382321 := bstep (se 2 (by rfl) ⟨9518370, by rfl⟩ : syracuseStep 25382321 = 19036741) B19036741
theorem B4230593 : Blo 1484062 4230593 := bstep (se 2 (by rfl) ⟨1586472, by rfl⟩ : syracuseStep 4230593 = 3172945) B3172945
theorem B7515665 : Blo 1484062 7515665 := bstep (se 2 (by rfl) ⟨2818374, by rfl⟩ : syracuseStep 7515665 = 5636749) B5636749
theorem B5008985 : Blo 1484062 5008985 := bstep (se 2 (by rfl) ⟨1878369, by rfl⟩ : syracuseStep 5008985 = 3756739) B3756739
theorem B8572517 : Blo 1484062 8572517 := bstep (se 4 (by rfl) ⟨803673, by rfl⟩ : syracuseStep 8572517 = 1607347) B1607347
theorem B7515827 : Blo 1484062 7515827 := bstep (se 1 (by rfl) ⟨5636870, by rfl⟩ : syracuseStep 7515827 = 11273741) B11273741
theorem B5639939 : Blo 1484062 5639939 := bstep (se 1 (by rfl) ⟨4229954, by rfl⟩ : syracuseStep 5639939 = 8459909) B8459909
theorem B29724515 : Blo 1484062 29724515 := bstep (se 1 (by rfl) ⟨22293386, by rfl⟩ : syracuseStep 29724515 = 44586773) B44586773
theorem B1585003 : Blo 1484062 1585003 := bstep (se 1 (by rfl) ⟨1188752, by rfl⟩ : syracuseStep 1585003 = 2377505) B2377505
theorem B3092339 : Blo 1484062 3092339 := bstep (se 1 (by rfl) ⟨2319254, by rfl⟩ : syracuseStep 3092339 = 4638509) B4638509
theorem B3010457 : Blo 1484062 3010457 := bstep (se 2 (by rfl) ⟨1128921, by rfl⟩ : syracuseStep 3010457 = 2257843) B2257843
theorem B14274481 : Blo 1484062 14274481 := bstep (se 2 (by rfl) ⟨5352930, by rfl⟩ : syracuseStep 14274481 = 10705861) B10705861
theorem B2379863 : Blo 1484062 2379863 := bstep (se 1 (by rfl) ⟨1784897, by rfl⟩ : syracuseStep 2379863 = 3569795) B3569795
theorem B2412683 : Blo 1484062 2412683 := bstep (se 1 (by rfl) ⟨1809512, by rfl⟩ : syracuseStep 2412683 = 3619025) B3619025
theorem B2674903 : Blo 1484062 2674903 := bstep (se 1 (by rfl) ⟨2006177, by rfl⟩ : syracuseStep 2674903 = 4012355) B4012355
theorem B4067545 : Blo 1484062 4067545 := bstep (se 2 (by rfl) ⟨1525329, by rfl⟩ : syracuseStep 4067545 = 3050659) B3050659
theorem B5009687 : Blo 1484062 5009687 := bstep (se 1 (by rfl) ⟨3757265, by rfl⟩ : syracuseStep 5009687 = 7514531) B7514531
theorem B1880587 : Blo 1484062 1880587 := bstep (se 1 (by rfl) ⟨1410440, by rfl⟩ : syracuseStep 1880587 = 2820881) B2820881
theorem B8458769 : Blo 1484062 8458769 := bstep (se 2 (by rfl) ⟨3172038, by rfl⟩ : syracuseStep 8458769 = 6344077) B6344077
theorem B3568151 : Blo 1484062 3568151 := bstep (se 1 (by rfl) ⟨2676113, by rfl⟩ : syracuseStep 3568151 = 5352227) B5352227
theorem B2380375 : Blo 1484062 2380375 := bstep (se 1 (by rfl) ⟨1785281, by rfl⟩ : syracuseStep 2380375 = 3570563) B3570563
theorem B7139933 : Blo 1484062 7139933 := bstep (se 3 (by rfl) ⟨1338737, by rfl⟩ : syracuseStep 7139933 = 2677475) B2677475
theorem B3052171 : Blo 1484062 3052171 := bstep (se 1 (by rfl) ⟨2289128, by rfl⟩ : syracuseStep 3052171 = 4578257) B4578257
theorem B5354201 : Blo 1484062 5354201 := bstep (se 2 (by rfl) ⟨2007825, by rfl⟩ : syracuseStep 5354201 = 4015651) B4015651
theorem B3756851 : Blo 1484062 3756851 := bstep (se 1 (by rfl) ⟨2817638, by rfl⟩ : syracuseStep 3756851 = 5635277) B5635277
theorem B5010227 : Blo 1484062 5010227 := bstep (se 1 (by rfl) ⟨3757670, by rfl⟩ : syracuseStep 5010227 = 7515341) B7515341
theorem B1586071 : Blo 1484062 1586071 := bstep (se 1 (by rfl) ⟨1189553, by rfl⟩ : syracuseStep 1586071 = 2379107) B2379107
theorem B3339161 : Blo 1484062 3339161 := bstep (se 2 (by rfl) ⟨1252185, by rfl⟩ : syracuseStep 3339161 = 2504371) B2504371
theorem B8459225 : Blo 1484062 8459225 := bstep (se 2 (by rfl) ⟨3172209, by rfl⟩ : syracuseStep 8459225 = 6344419) B6344419
theorem B4756445 : Blo 1484062 4756445 := bstep (se 3 (by rfl) ⟨891833, by rfl⟩ : syracuseStep 4756445 = 1783667) B1783667
theorem B3339251 : Blo 1484062 3339251 := bstep (se 1 (by rfl) ⟨2504438, by rfl⟩ : syracuseStep 3339251 = 5008877) B5008877
theorem B3339287 : Blo 1484062 3339287 := bstep (se 1 (by rfl) ⟨2504465, by rfl⟩ : syracuseStep 3339287 = 5008931) B5008931
theorem B5010497 : Blo 1484062 5010497 := bstep (se 2 (by rfl) ⟨1878936, by rfl⟩ : syracuseStep 5010497 = 3757873) B3757873
theorem B12039299 : Blo 1484062 12039299 := bstep (se 1 (by rfl) ⟨9029474, by rfl⟩ : syracuseStep 12039299 = 18058949) B18058949
theorem B3339467 : Blo 1484062 3339467 := bstep (se 1 (by rfl) ⟨2504600, by rfl⟩ : syracuseStep 3339467 = 5009201) B5009201
theorem B2258135 : Blo 1484062 2258135 := bstep (se 1 (by rfl) ⟨1693601, by rfl⟩ : syracuseStep 2258135 = 3387203) B3387203
theorem B3339521 : Blo 1484062 3339521 := bstep (se 2 (by rfl) ⟨1252320, by rfl⟩ : syracuseStep 3339521 = 2504641) B2504641
theorem B3757387 : Blo 1484062 3757387 := bstep (se 1 (by rfl) ⟨2818040, by rfl⟩ : syracuseStep 3757387 = 5636081) B5636081
theorem B30487925 : Blo 1484062 30487925 := bstep (se 5 (by rfl) ⟨1429121, by rfl⟩ : syracuseStep 30487925 = 2858243) B2858243
theorem B3339737 : Blo 1484062 3339737 := bstep (se 2 (by rfl) ⟨1252401, by rfl⟩ : syracuseStep 3339737 = 2504803) B2504803
theorem B3757529 : Blo 1484062 3757529 := bstep (se 2 (by rfl) ⟨1409073, by rfl⟩ : syracuseStep 3757529 = 2818147) B2818147
theorem B2676235 : Blo 1484062 2676235 := bstep (se 1 (by rfl) ⟨2007176, by rfl⟩ : syracuseStep 2676235 = 4014353) B4014353
theorem B3339827 : Blo 1484062 3339827 := bstep (se 1 (by rfl) ⟨2504870, by rfl⟩ : syracuseStep 3339827 = 5009741) B5009741
theorem B7517771 : Blo 1484062 7517771 := bstep (se 1 (by rfl) ⟨5638328, by rfl⟩ : syracuseStep 7517771 = 11276657) B11276657
theorem B3339863 : Blo 1484062 3339863 := bstep (se 1 (by rfl) ⟨2504897, by rfl⟩ : syracuseStep 3339863 = 5009795) B5009795
theorem B5011037 : Blo 1484062 5011037 := bstep (se 3 (by rfl) ⟨939569, by rfl⟩ : syracuseStep 5011037 = 1879139) B1879139
theorem B1586891 : Blo 1484062 1586891 := bstep (se 1 (by rfl) ⟨1190168, by rfl⟩ : syracuseStep 1586891 = 2380337) B2380337
theorem B18093773 : Blo 1484062 18093773 := bstep (se 3 (by rfl) ⟨3392582, by rfl⟩ : syracuseStep 18093773 = 6785165) B6785165
theorem B6100697 : Blo 1484062 6100697 := bstep (se 2 (by rfl) ⟨2287761, by rfl⟩ : syracuseStep 6100697 = 4575523) B4575523
theorem B2504459 : Blo 1484062 2504459 := bstep (se 1 (by rfl) ⟨1878344, by rfl⟩ : syracuseStep 2504459 = 3756689) B3756689
theorem B3340043 : Blo 1484062 3340043 := bstep (se 1 (by rfl) ⟨2505032, by rfl⟩ : syracuseStep 3340043 = 5010065) B5010065
theorem B12678929 : Blo 1484062 12678929 := bstep (se 2 (by rfl) ⟨4754598, by rfl⟩ : syracuseStep 12678929 = 9509197) B9509197
theorem B11278115 : Blo 1484062 11278115 := bstep (se 1 (by rfl) ⟨8458586, by rfl⟩ : syracuseStep 11278115 = 16917173) B16917173
theorem B3340097 : Blo 1484062 3340097 := bstep (se 2 (by rfl) ⟨1252536, by rfl⟩ : syracuseStep 3340097 = 2505073) B2505073
theorem B2504587 : Blo 1484062 2504587 := bstep (se 1 (by rfl) ⟨1878440, by rfl⟩ : syracuseStep 2504587 = 3756881) B3756881
theorem B2226137 : Blo 1484062 2226137 := bstep (se 2 (by rfl) ⟨834801, by rfl⟩ : syracuseStep 2226137 = 1669603) B1669603
theorem B2504729 : Blo 1484062 2504729 := bstep (se 2 (by rfl) ⟨939273, by rfl⟩ : syracuseStep 2504729 = 1878547) B1878547
theorem B3340313 : Blo 1484062 3340313 := bstep (se 2 (by rfl) ⟨1252617, by rfl⟩ : syracuseStep 3340313 = 2505235) B2505235
theorem B5355571 : Blo 1484062 5355571 := bstep (se 1 (by rfl) ⟨4016678, by rfl⟩ : syracuseStep 5355571 = 8033357) B8033357
theorem B2226251 : Blo 1484062 2226251 := bstep (se 1 (by rfl) ⟨1669688, by rfl⟩ : syracuseStep 2226251 = 3339377) B3339377
theorem B2226263 : Blo 1484062 2226263 := bstep (se 1 (by rfl) ⟨1669697, by rfl⟩ : syracuseStep 2226263 = 3339395) B3339395
theorem B3340403 : Blo 1484062 3340403 := bstep (se 1 (by rfl) ⟨2505302, by rfl⟩ : syracuseStep 3340403 = 5010605) B5010605
theorem B3340439 : Blo 1484062 3340439 := bstep (se 1 (by rfl) ⟨2505329, by rfl⟩ : syracuseStep 3340439 = 5010659) B5010659
theorem B2226329 : Blo 1484062 2226329 := bstep (se 2 (by rfl) ⟨834873, by rfl⟩ : syracuseStep 2226329 = 1669747) B1669747
theorem B2504857 : Blo 1484062 2504857 := bstep (se 2 (by rfl) ⟨939321, by rfl⟩ : syracuseStep 2504857 = 1878643) B1878643
theorem B7616729 : Blo 1484062 7616729 := bstep (se 2 (by rfl) ⟨2856273, by rfl⟩ : syracuseStep 7616729 = 5712547) B5712547
theorem B2226443 : Blo 1484062 2226443 := bstep (se 1 (by rfl) ⟨1669832, by rfl⟩ : syracuseStep 2226443 = 3339665) B3339665
theorem B2226455 : Blo 1484062 2226455 := bstep (se 1 (by rfl) ⟨1669841, by rfl⟩ : syracuseStep 2226455 = 3339683) B3339683
theorem B3758359 : Blo 1484062 3758359 := bstep (se 1 (by rfl) ⟨2818769, by rfl⟩ : syracuseStep 3758359 = 5637539) B5637539
theorem B36616493 : Blo 1484062 36616493 := bstep (se 3 (by rfl) ⟨6865592, by rfl⟩ : syracuseStep 36616493 = 13731185) B13731185
theorem B3340619 : Blo 1484062 3340619 := bstep (se 1 (by rfl) ⟨2505464, by rfl⟩ : syracuseStep 3340619 = 5010929) B5010929
theorem B1694039 : Blo 1484062 1694039 := bstep (se 1 (by rfl) ⟨1270529, by rfl⟩ : syracuseStep 1694039 = 2541059) B2541059
theorem B2226521 : Blo 1484062 2226521 := bstep (se 2 (by rfl) ⟨834945, by rfl⟩ : syracuseStep 2226521 = 1669891) B1669891
theorem B3340673 : Blo 1484062 3340673 := bstep (se 2 (by rfl) ⟨1252752, by rfl⟩ : syracuseStep 3340673 = 2505505) B2505505
theorem B6347153 : Blo 1484062 6347153 := bstep (se 2 (by rfl) ⟨2380182, by rfl⟩ : syracuseStep 6347153 = 4760365) B4760365
theorem B2226635 : Blo 1484062 2226635 := bstep (se 1 (by rfl) ⟨1669976, by rfl⟩ : syracuseStep 2226635 = 3339953) B3339953
theorem B2226647 : Blo 1484062 2226647 := bstep (se 1 (by rfl) ⟨1669985, by rfl⟩ : syracuseStep 2226647 = 3339971) B3339971
theorem B6429149 : Blo 1484062 6429149 := bstep (se 3 (by rfl) ⟨1205465, by rfl⟩ : syracuseStep 6429149 = 2410931) B2410931
theorem B2226713 : Blo 1484062 2226713 := bstep (se 2 (by rfl) ⟨835017, by rfl⟩ : syracuseStep 2226713 = 1670035) B1670035
theorem B1669675 : Blo 1484062 1669675 := bstep (se 1 (by rfl) ⟨1252256, by rfl⟩ : syracuseStep 1669675 = 2504513) B2504513
theorem B3570227 : Blo 1484062 3570227 := bstep (se 1 (by rfl) ⟨2677670, by rfl⟩ : syracuseStep 3570227 = 5355341) B5355341
theorem B3340889 : Blo 1484062 3340889 := bstep (se 2 (by rfl) ⟨1252833, by rfl⟩ : syracuseStep 3340889 = 2505667) B2505667
theorem B2226827 : Blo 1484062 2226827 := bstep (se 1 (by rfl) ⟨1670120, by rfl⟩ : syracuseStep 2226827 = 3340241) B3340241
theorem B1669783 : Blo 1484062 1669783 := bstep (se 1 (by rfl) ⟨1252337, by rfl⟩ : syracuseStep 1669783 = 2504675) B2504675
theorem B2226839 : Blo 1484062 2226839 := bstep (se 1 (by rfl) ⟨1670129, by rfl⟩ : syracuseStep 2226839 = 3340259) B3340259
theorem B9509555 : Blo 1484062 9509555 := bstep (se 1 (by rfl) ⟨7132166, by rfl⟩ : syracuseStep 9509555 = 14264333) B14264333
theorem B3340979 : Blo 1484062 3340979 := bstep (se 1 (by rfl) ⟨2505734, by rfl⟩ : syracuseStep 3340979 = 5011469) B5011469
theorem B9173683 : Blo 1484062 9173683 := bstep (se 1 (by rfl) ⟨6880262, by rfl⟩ : syracuseStep 9173683 = 13760525) B13760525
theorem B3758795 : Blo 1484062 3758795 := bstep (se 1 (by rfl) ⟨2819096, by rfl⟩ : syracuseStep 3758795 = 5638193) B5638193
theorem B5012171 : Blo 1484062 5012171 := bstep (se 1 (by rfl) ⟨3759128, by rfl⟩ : syracuseStep 5012171 = 7518257) B7518257
theorem B2505431 : Blo 1484062 2505431 := bstep (se 1 (by rfl) ⟨1879073, by rfl⟩ : syracuseStep 2505431 = 3758147) B3758147
theorem B2226905 : Blo 1484062 2226905 := bstep (se 2 (by rfl) ⟨835089, by rfl⟩ : syracuseStep 2226905 = 1670179) B1670179
theorem B3341015 : Blo 1484062 3341015 := bstep (se 1 (by rfl) ⟨2505761, by rfl⟩ : syracuseStep 3341015 = 5011523) B5011523
theorem B6339293 : Blo 1484062 6339293 := bstep (se 3 (by rfl) ⟨1188617, by rfl⟩ : syracuseStep 6339293 = 2377235) B2377235
theorem B1669963 : Blo 1484062 1669963 := bstep (se 1 (by rfl) ⟨1252472, by rfl⟩ : syracuseStep 1669963 = 2504945) B2504945
theorem B2227019 : Blo 1484062 2227019 := bstep (se 1 (by rfl) ⟨1670264, by rfl⟩ : syracuseStep 2227019 = 3340529) B3340529
theorem B2227031 : Blo 1484062 2227031 := bstep (se 1 (by rfl) ⟨1670273, by rfl⟩ : syracuseStep 2227031 = 3340547) B3340547
theorem B2505559 : Blo 1484062 2505559 := bstep (se 1 (by rfl) ⟨1879169, by rfl⟩ : syracuseStep 2505559 = 3758339) B3758339
theorem B3341195 : Blo 1484062 3341195 := bstep (se 1 (by rfl) ⟨2505896, by rfl⟩ : syracuseStep 3341195 = 5011793) B5011793
theorem B2227097 : Blo 1484062 2227097 := bstep (se 2 (by rfl) ⟨835161, by rfl⟩ : syracuseStep 2227097 = 1670323) B1670323
theorem B19037105 : Blo 1484062 19037105 := bstep (se 2 (by rfl) ⟨7138914, by rfl⟩ : syracuseStep 19037105 = 14277829) B14277829
theorem B1670071 : Blo 1484062 1670071 := bstep (se 1 (by rfl) ⟨1252553, by rfl⟩ : syracuseStep 1670071 = 2505107) B2505107
theorem B3341249 : Blo 1484062 3341249 := bstep (se 2 (by rfl) ⟨1252968, by rfl⟩ : syracuseStep 3341249 = 2505937) B2505937
theorem B5012441 : Blo 1484062 5012441 := bstep (se 2 (by rfl) ⟨1879665, by rfl⟩ : syracuseStep 5012441 = 3759331) B3759331
theorem B2227211 : Blo 1484062 2227211 := bstep (se 1 (by rfl) ⟨1670408, by rfl⟩ : syracuseStep 2227211 = 3340817) B3340817
theorem B2227223 : Blo 1484062 2227223 := bstep (se 1 (by rfl) ⟨1670417, by rfl⟩ : syracuseStep 2227223 = 3340835) B3340835
theorem B3759169 : Blo 1484062 3759169 := bstep (se 2 (by rfl) ⟨1409688, by rfl⟩ : syracuseStep 3759169 = 2819377) B2819377
theorem B2227289 : Blo 1484062 2227289 := bstep (se 2 (by rfl) ⟨835233, by rfl⟩ : syracuseStep 2227289 = 1670467) B1670467
theorem B1670251 : Blo 1484062 1670251 := bstep (se 1 (by rfl) ⟨1252688, by rfl⟩ : syracuseStep 1670251 = 2505377) B2505377
theorem B5717137 : Blo 1484062 5717137 := bstep (se 2 (by rfl) ⟨2143926, by rfl⟩ : syracuseStep 5717137 = 4287853) B4287853
theorem B3341465 : Blo 1484062 3341465 := bstep (se 2 (by rfl) ⟨1253049, by rfl⟩ : syracuseStep 3341465 = 2506099) B2506099
theorem B2227403 : Blo 1484062 2227403 := bstep (se 1 (by rfl) ⟨1670552, by rfl⟩ : syracuseStep 2227403 = 3341105) B3341105
theorem B1670359 : Blo 1484062 1670359 := bstep (se 1 (by rfl) ⟨1252769, by rfl⟩ : syracuseStep 1670359 = 2505539) B2505539
theorem B2227415 : Blo 1484062 2227415 := bstep (se 1 (by rfl) ⟨1670561, by rfl⟩ : syracuseStep 2227415 = 3341123) B3341123
theorem B3341555 : Blo 1484062 3341555 := bstep (se 1 (by rfl) ⟨2506166, by rfl⟩ : syracuseStep 3341555 = 5012333) B5012333
theorem B8453393 : Blo 1484062 8453393 := bstep (se 2 (by rfl) ⟨3170022, by rfl⟩ : syracuseStep 8453393 = 6340045) B6340045
theorem B3341591 : Blo 1484062 3341591 := bstep (se 1 (by rfl) ⟨2506193, by rfl⟩ : syracuseStep 3341591 = 5012387) B5012387
theorem B2227481 : Blo 1484062 2227481 := bstep (se 2 (by rfl) ⟨835305, by rfl⟩ : syracuseStep 2227481 = 1670611) B1670611
theorem B7519553 : Blo 1484062 7519553 := bstep (se 2 (by rfl) ⟨2819832, by rfl⟩ : syracuseStep 7519553 = 5639665) B5639665
theorem B1670539 : Blo 1484062 1670539 := bstep (se 1 (by rfl) ⟨1252904, by rfl⟩ : syracuseStep 1670539 = 2505809) B2505809
theorem B2227595 : Blo 1484062 2227595 := bstep (se 1 (by rfl) ⟨1670696, by rfl⟩ : syracuseStep 2227595 = 3341393) B3341393
theorem B2227607 : Blo 1484062 2227607 := bstep (se 1 (by rfl) ⟨1670705, by rfl⟩ : syracuseStep 2227607 = 3341411) B3341411
theorem B2817433 : Blo 1484062 2817433 := bstep (se 2 (by rfl) ⟨1056537, by rfl⟩ : syracuseStep 2817433 = 2113075) B2113075
theorem B2506187 : Blo 1484062 2506187 := bstep (se 1 (by rfl) ⟨1879640, by rfl⟩ : syracuseStep 2506187 = 3759281) B3759281
theorem B3341771 : Blo 1484062 3341771 := bstep (se 1 (by rfl) ⟨2506328, by rfl⟩ : syracuseStep 3341771 = 5012657) B5012657
theorem B2227673 : Blo 1484062 2227673 := bstep (se 2 (by rfl) ⟨835377, by rfl⟩ : syracuseStep 2227673 = 1670755) B1670755
theorem B21421529 : Blo 1484062 21421529 := bstep (se 2 (by rfl) ⟨8033073, by rfl⟩ : syracuseStep 21421529 = 16066147) B16066147
theorem B1670647 : Blo 1484062 1670647 := bstep (se 1 (by rfl) ⟨1252985, by rfl⟩ : syracuseStep 1670647 = 2505971) B2505971
theorem B3341825 : Blo 1484062 3341825 := bstep (se 2 (by rfl) ⟨1253184, by rfl⟩ : syracuseStep 3341825 = 2506369) B2506369
theorem B2227787 : Blo 1484062 2227787 := bstep (se 1 (by rfl) ⟨1670840, by rfl⟩ : syracuseStep 2227787 = 3341681) B3341681
theorem B2506315 : Blo 1484062 2506315 := bstep (se 1 (by rfl) ⟨1879736, by rfl⟩ : syracuseStep 2506315 = 3759473) B3759473
theorem B2227799 : Blo 1484062 2227799 := bstep (se 1 (by rfl) ⟨1670849, by rfl⟩ : syracuseStep 2227799 = 3341699) B3341699
theorem B8248925 : Blo 1484062 8248925 := bstep (se 3 (by rfl) ⟨1546673, by rfl⟩ : syracuseStep 8248925 = 3093347) B3093347
theorem B3759767 : Blo 1484062 3759767 := bstep (se 1 (by rfl) ⟨2819825, by rfl⟩ : syracuseStep 3759767 = 5639651) B5639651
theorem B5013143 : Blo 1484062 5013143 := bstep (se 1 (by rfl) ⟨3759857, by rfl⟩ : syracuseStep 5013143 = 7519715) B7519715
theorem B2227865 : Blo 1484062 2227865 := bstep (se 2 (by rfl) ⟨835449, by rfl⟩ : syracuseStep 2227865 = 1670899) B1670899
theorem B1670827 : Blo 1484062 1670827 := bstep (se 1 (by rfl) ⟨1253120, by rfl⟩ : syracuseStep 1670827 = 2506241) B2506241
theorem B5635763 : Blo 1484062 5635763 := bstep (se 1 (by rfl) ⟨4226822, by rfl⟩ : syracuseStep 5635763 = 8453645) B8453645
theorem B5635777 : Blo 1484062 5635777 := bstep (se 2 (by rfl) ⟨2113416, by rfl⟩ : syracuseStep 5635777 = 4226833) B4226833
theorem B2506457 : Blo 1484062 2506457 := bstep (se 2 (by rfl) ⟨939921, by rfl⟩ : syracuseStep 2506457 = 1879843) B1879843
theorem B3342041 : Blo 1484062 3342041 := bstep (se 2 (by rfl) ⟨1253265, by rfl⟩ : syracuseStep 3342041 = 2506531) B2506531
theorem B2227979 : Blo 1484062 2227979 := bstep (se 1 (by rfl) ⟨1670984, by rfl⟩ : syracuseStep 2227979 = 3341969) B3341969
theorem B2113303 : Blo 1484062 2113303 := bstep (se 1 (by rfl) ⟨1584977, by rfl⟩ : syracuseStep 2113303 = 3169955) B3169955
theorem B1670935 : Blo 1484062 1670935 := bstep (se 1 (by rfl) ⟨1253201, by rfl⟩ : syracuseStep 1670935 = 2506403) B2506403
theorem B2227991 : Blo 1484062 2227991 := bstep (se 1 (by rfl) ⟨1670993, by rfl⟩ : syracuseStep 2227991 = 3341987) B3341987
theorem B3342131 : Blo 1484062 3342131 := bstep (se 1 (by rfl) ⟨2506598, by rfl⟩ : syracuseStep 3342131 = 5013197) B5013197
theorem B3342167 : Blo 1484062 3342167 := bstep (se 1 (by rfl) ⟨2506625, by rfl⟩ : syracuseStep 3342167 = 5013251) B5013251
theorem B2228057 : Blo 1484062 2228057 := bstep (se 2 (by rfl) ⟨835521, by rfl⟩ : syracuseStep 2228057 = 1671043) B1671043
theorem B2506585 : Blo 1484062 2506585 := bstep (se 2 (by rfl) ⟨939969, by rfl⟩ : syracuseStep 2506585 = 1879939) B1879939
theorem B9035651 : Blo 1484062 9035651 := bstep (se 1 (by rfl) ⟨6776738, by rfl⟩ : syracuseStep 9035651 = 13553477) B13553477
theorem B10166147 : Blo 1484062 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B5423041 : Blo 1484062 5423041 := bstep (se 2 (by rfl) ⟨2033640, by rfl⟩ : syracuseStep 5423041 = 4067281) B4067281
theorem B1671115 : Blo 1484062 1671115 := bstep (se 1 (by rfl) ⟨1253336, by rfl⟩ : syracuseStep 1671115 = 2506673) B2506673
theorem B2228171 : Blo 1484062 2228171 := bstep (se 1 (by rfl) ⟨1671128, by rfl⟩ : syracuseStep 2228171 = 3342257) B3342257
theorem B2228183 : Blo 1484062 2228183 := bstep (se 1 (by rfl) ⟨1671137, by rfl⟩ : syracuseStep 2228183 = 3342275) B3342275
theorem B10698713 : Blo 1484062 10698713 := bstep (se 2 (by rfl) ⟨4012017, by rfl⟩ : syracuseStep 10698713 = 8024035) B8024035
theorem B19029977 : Blo 1484062 19029977 := bstep (se 2 (by rfl) ⟨7136241, by rfl⟩ : syracuseStep 19029977 = 14272483) B14272483
theorem B2228231 : Blo 1484062 2228231 := bstep (se 1 (by rfl) ⟨1671173, by rfl⟩ : syracuseStep 2228231 = 3342347) B3342347
theorem B2228267 : Blo 1484062 2228267 := bstep (se 1 (by rfl) ⟨1671200, by rfl⟩ : syracuseStep 2228267 = 3342401) B3342401
theorem B2228297 : Blo 1484062 2228297 := bstep (se 2 (by rfl) ⟨835611, by rfl⟩ : syracuseStep 2228297 = 1671223) B1671223
theorem B9519191 : Blo 1484062 9519191 := bstep (se 1 (by rfl) ⟨7139393, by rfl⟩ : syracuseStep 9519191 = 14278787) B14278787
theorem B4227187 : Blo 1484062 4227187 := bstep (se 1 (by rfl) ⟨3170390, by rfl⟩ : syracuseStep 4227187 = 6340781) B6340781
theorem B3342455 : Blo 1484062 3342455 := bstep (se 1 (by rfl) ⟨2506841, by rfl⟩ : syracuseStep 3342455 = 5013683) B5013683
theorem B2228411 : Blo 1484062 2228411 := bstep (se 1 (by rfl) ⟨1671308, by rfl⟩ : syracuseStep 2228411 = 3342617) B3342617
theorem B2228471 : Blo 1484062 2228471 := bstep (se 1 (by rfl) ⟨1671353, by rfl⟩ : syracuseStep 2228471 = 3342707) B3342707
theorem B2228495 : Blo 1484062 2228495 := bstep (se 1 (by rfl) ⟨1671371, by rfl⟩ : syracuseStep 2228495 = 3342743) B3342743
theorem B1671439 : Blo 1484062 1671439 := bstep (se 1 (by rfl) ⟨1253579, by rfl⟩ : syracuseStep 1671439 = 2507159) B2507159
theorem B5423393 : Blo 1484062 5423393 := bstep (se 2 (by rfl) ⟨2033772, by rfl⟩ : syracuseStep 5423393 = 4067545) B4067545
theorem B3342635 : Blo 1484062 3342635 := bstep (se 1 (by rfl) ⟨2506976, by rfl⟩ : syracuseStep 3342635 = 5013953) B5013953
theorem B2507051 : Blo 1484062 2507051 := bstep (se 1 (by rfl) ⟨1880288, by rfl⟩ : syracuseStep 2507051 = 3760577) B3760577
theorem B2228537 : Blo 1484062 2228537 := bstep (se 2 (by rfl) ⟨835701, by rfl⟩ : syracuseStep 2228537 = 1671403) B1671403
theorem B2228615 : Blo 1484062 2228615 := bstep (se 1 (by rfl) ⟨1671461, by rfl⟩ : syracuseStep 2228615 = 3342923) B3342923
theorem B2818451 : Blo 1484062 2818451 := bstep (se 1 (by rfl) ⟨2113838, by rfl⟩ : syracuseStep 2818451 = 4227677) B4227677
theorem B4759955 : Blo 1484062 4759955 := bstep (se 1 (by rfl) ⟨3569966, by rfl⟩ : syracuseStep 4759955 = 7139933) B7139933
theorem B2228651 : Blo 1484062 2228651 := bstep (se 1 (by rfl) ⟨1671488, by rfl⟩ : syracuseStep 2228651 = 3342977) B3342977
theorem B5636537 : Blo 1484062 5636537 := bstep (se 2 (by rfl) ⟨2113701, by rfl⟩ : syracuseStep 5636537 = 4227403) B4227403
theorem B2818489 : Blo 1484062 2818489 := bstep (se 2 (by rfl) ⟨1056933, by rfl⟩ : syracuseStep 2818489 = 2113867) B2113867
theorem B2228681 : Blo 1484062 2228681 := bstep (se 2 (by rfl) ⟨835755, by rfl⟩ : syracuseStep 2228681 = 1671511) B1671511
theorem B2228795 : Blo 1484062 2228795 := bstep (se 1 (by rfl) ⟨1671596, by rfl⟩ : syracuseStep 2228795 = 3343193) B3343193
theorem B2228855 : Blo 1484062 2228855 := bstep (se 1 (by rfl) ⟨1671641, by rfl⟩ : syracuseStep 2228855 = 3343283) B3343283
theorem B2114191 : Blo 1484062 2114191 := bstep (se 1 (by rfl) ⟨1585643, by rfl⟩ : syracuseStep 2114191 = 3171287) B3171287
theorem B2228879 : Blo 1484062 2228879 := bstep (se 1 (by rfl) ⟨1671659, by rfl⟩ : syracuseStep 2228879 = 3343319) B3343319
theorem B3170963 : Blo 1484062 3170963 := bstep (se 1 (by rfl) ⟨2378222, by rfl⟩ : syracuseStep 3170963 = 4756445) B4756445
theorem B3342995 : Blo 1484062 3342995 := bstep (se 1 (by rfl) ⟨2507246, by rfl⟩ : syracuseStep 3342995 = 5014493) B5014493
theorem B2507449 : Blo 1484062 2507449 := bstep (se 2 (by rfl) ⟨940293, by rfl⟩ : syracuseStep 2507449 = 1880587) B1880587
theorem B2228921 : Blo 1484062 2228921 := bstep (se 2 (by rfl) ⟨835845, by rfl⟩ : syracuseStep 2228921 = 1671691) B1671691
theorem B3343049 : Blo 1484062 3343049 := bstep (se 2 (by rfl) ⟨1253643, by rfl⟩ : syracuseStep 3343049 = 2507287) B2507287
theorem B16278245 : Blo 1484062 16278245 := bstep (se 4 (by rfl) ⟨1526085, by rfl⟩ : syracuseStep 16278245 = 3052171) B3052171
theorem B2228999 : Blo 1484062 2228999 := bstep (se 1 (by rfl) ⟨1671749, by rfl⟩ : syracuseStep 2228999 = 3343499) B3343499
theorem B2229035 : Blo 1484062 2229035 := bstep (se 1 (by rfl) ⟨1671776, by rfl⟩ : syracuseStep 2229035 = 3343553) B3343553
theorem B5014331 : Blo 1484062 5014331 := bstep (se 1 (by rfl) ⟨3760748, by rfl⟩ : syracuseStep 5014331 = 7521497) B7521497
theorem B2229065 : Blo 1484062 2229065 := bstep (se 2 (by rfl) ⟨835899, by rfl⟩ : syracuseStep 2229065 = 1671799) B1671799
theorem B5079955 : Blo 1484062 5079955 := bstep (se 1 (by rfl) ⟨3809966, by rfl⟩ : syracuseStep 5079955 = 7619933) B7619933
theorem B12231577 : Blo 1484062 12231577 := bstep (se 2 (by rfl) ⟨4586841, by rfl⟩ : syracuseStep 12231577 = 9173683) B9173683
theorem B8463325 : Blo 1484062 8463325 := bstep (se 3 (by rfl) ⟨1586873, by rfl⟩ : syracuseStep 8463325 = 3173747) B3173747
theorem B2114761 : Blo 1484062 2114761 := bstep (se 2 (by rfl) ⟨793035, by rfl⟩ : syracuseStep 2114761 = 1586071) B1586071
theorem B5014817 : Blo 1484062 5014817 := bstep (se 2 (by rfl) ⟨1880556, by rfl⟩ : syracuseStep 5014817 = 3761113) B3761113
theorem B1484091 : Blo 1484062 1484091 := bstep (se 1 (by rfl) ⟨1113068, by rfl⟩ : syracuseStep 1484091 = 2226137) B2226137
theorem B1484167 : Blo 1484062 1484167 := bstep (se 1 (by rfl) ⟨1113125, by rfl⟩ : syracuseStep 1484167 = 2226251) B2226251
theorem B1484175 : Blo 1484062 1484175 := bstep (se 1 (by rfl) ⟨1113131, by rfl⟩ : syracuseStep 1484175 = 2226263) B2226263
theorem B1484219 : Blo 1484062 1484219 := bstep (se 1 (by rfl) ⟨1113164, by rfl⟩ : syracuseStep 1484219 = 2226329) B2226329
theorem B1484295 : Blo 1484062 1484295 := bstep (se 1 (by rfl) ⟨1113221, by rfl⟩ : syracuseStep 1484295 = 2226443) B2226443
theorem B1484303 : Blo 1484062 1484303 := bstep (se 1 (by rfl) ⟨1113227, by rfl⟩ : syracuseStep 1484303 = 2226455) B2226455
theorem B7521821 : Blo 1484062 7521821 := bstep (se 3 (by rfl) ⟨1410341, by rfl⟩ : syracuseStep 7521821 = 2820683) B2820683
theorem B1484347 : Blo 1484062 1484347 := bstep (se 1 (by rfl) ⟨1113260, by rfl⟩ : syracuseStep 1484347 = 2226521) B2226521
theorem B32097869 : Blo 1484062 32097869 := bstep (se 3 (by rfl) ⟨6018350, by rfl⟩ : syracuseStep 32097869 = 12036701) B12036701
theorem B1484423 : Blo 1484062 1484423 := bstep (se 1 (by rfl) ⟨1113317, by rfl⟩ : syracuseStep 1484423 = 2226635) B2226635
theorem B1484431 : Blo 1484062 1484431 := bstep (se 1 (by rfl) ⟨1113323, by rfl⟩ : syracuseStep 1484431 = 2226647) B2226647
theorem B4286099 : Blo 1484062 4286099 := bstep (se 1 (by rfl) ⟨3214574, by rfl⟩ : syracuseStep 4286099 = 6429149) B6429149
theorem B8455853 : Blo 1484062 8455853 := bstep (se 3 (by rfl) ⟨1585472, by rfl⟩ : syracuseStep 8455853 = 3170945) B3170945
theorem B4228793 : Blo 1484062 4228793 := bstep (se 2 (by rfl) ⟨1585797, by rfl⟩ : syracuseStep 4228793 = 3171595) B3171595
theorem B1484475 : Blo 1484062 1484475 := bstep (se 1 (by rfl) ⟨1113356, by rfl⟩ : syracuseStep 1484475 = 2226713) B2226713
theorem B1484551 : Blo 1484062 1484551 := bstep (se 1 (by rfl) ⟨1113413, by rfl⟩ : syracuseStep 1484551 = 2226827) B2226827
theorem B1484559 : Blo 1484062 1484559 := bstep (se 1 (by rfl) ⟨1113419, by rfl⟩ : syracuseStep 1484559 = 2226839) B2226839
theorem B9037601 : Blo 1484062 9037601 := bstep (se 2 (by rfl) ⟨3389100, by rfl⟩ : syracuseStep 9037601 = 6778201) B6778201
theorem B1484603 : Blo 1484062 1484603 := bstep (se 1 (by rfl) ⟨1113452, by rfl⟩ : syracuseStep 1484603 = 2226905) B2226905
theorem B5015411 : Blo 1484062 5015411 := bstep (se 1 (by rfl) ⟨3761558, by rfl⟩ : syracuseStep 5015411 = 7523117) B7523117
theorem B1484679 : Blo 1484062 1484679 := bstep (se 1 (by rfl) ⟨1113509, by rfl⟩ : syracuseStep 1484679 = 2227019) B2227019
theorem B1484687 : Blo 1484062 1484687 := bstep (se 1 (by rfl) ⟨1113515, by rfl⟩ : syracuseStep 1484687 = 2227031) B2227031
theorem B1484731 : Blo 1484062 1484731 := bstep (se 1 (by rfl) ⟨1113548, by rfl⟩ : syracuseStep 1484731 = 2227097) B2227097
theorem B12691403 : Blo 1484062 12691403 := bstep (se 1 (by rfl) ⟨9518552, by rfl⟩ : syracuseStep 12691403 = 19037105) B19037105
theorem B7522307 : Blo 1484062 7522307 := bstep (se 1 (by rfl) ⟨5641730, by rfl⟩ : syracuseStep 7522307 = 11283461) B11283461
theorem B1484807 : Blo 1484062 1484807 := bstep (se 1 (by rfl) ⟨1113605, by rfl⟩ : syracuseStep 1484807 = 2227211) B2227211
theorem B1484815 : Blo 1484062 1484815 := bstep (se 1 (by rfl) ⟨1113611, by rfl⟩ : syracuseStep 1484815 = 2227223) B2227223
theorem B4229135 : Blo 1484062 4229135 := bstep (se 1 (by rfl) ⟨3171851, by rfl⟩ : syracuseStep 4229135 = 6343703) B6343703
theorem B1484859 : Blo 1484062 1484859 := bstep (se 1 (by rfl) ⟨1113644, by rfl⟩ : syracuseStep 1484859 = 2227289) B2227289
theorem B1484935 : Blo 1484062 1484935 := bstep (se 1 (by rfl) ⟨1113701, by rfl⟩ : syracuseStep 1484935 = 2227403) B2227403
theorem B1484943 : Blo 1484062 1484943 := bstep (se 1 (by rfl) ⟨1113707, by rfl⟩ : syracuseStep 1484943 = 2227415) B2227415
theorem B1484987 : Blo 1484062 1484987 := bstep (se 1 (by rfl) ⟨1113740, by rfl⟩ : syracuseStep 1484987 = 2227481) B2227481
theorem B7514369 : Blo 1484062 7514369 := bstep (se 2 (by rfl) ⟨2817888, by rfl⟩ : syracuseStep 7514369 = 5635777) B5635777
theorem B1485063 : Blo 1484062 1485063 := bstep (se 1 (by rfl) ⟨1113797, by rfl⟩ : syracuseStep 1485063 = 2227595) B2227595
theorem B1485071 : Blo 1484062 1485071 := bstep (se 1 (by rfl) ⟨1113803, by rfl⟩ : syracuseStep 1485071 = 2227607) B2227607
theorem B2820395 : Blo 1484062 2820395 := bstep (se 1 (by rfl) ⟨2115296, by rfl⟩ : syracuseStep 2820395 = 4230593) B4230593
theorem B1485115 : Blo 1484062 1485115 := bstep (se 1 (by rfl) ⟨1113836, by rfl⟩ : syracuseStep 1485115 = 2227673) B2227673
theorem B14281019 : Blo 1484062 14281019 := bstep (se 1 (by rfl) ⟨10710764, by rfl⟩ : syracuseStep 14281019 = 21421529) B21421529
theorem B24095069 : Blo 1484062 24095069 := bstep (se 3 (by rfl) ⟨4517825, by rfl⟩ : syracuseStep 24095069 = 9035651) B9035651
theorem B1485191 : Blo 1484062 1485191 := bstep (se 1 (by rfl) ⟨1113893, by rfl⟩ : syracuseStep 1485191 = 2227787) B2227787
theorem B1485199 : Blo 1484062 1485199 := bstep (se 1 (by rfl) ⟨1113899, by rfl⟩ : syracuseStep 1485199 = 2227799) B2227799
theorem B8030609 : Blo 1484062 8030609 := bstep (se 2 (by rfl) ⟨3011478, by rfl⟩ : syracuseStep 8030609 = 6022957) B6022957
theorem B5499283 : Blo 1484062 5499283 := bstep (se 1 (by rfl) ⟨4124462, by rfl⟩ : syracuseStep 5499283 = 8248925) B8248925
theorem B1485243 : Blo 1484062 1485243 := bstep (se 1 (by rfl) ⟨1113932, by rfl⟩ : syracuseStep 1485243 = 2227865) B2227865
theorem B1485319 : Blo 1484062 1485319 := bstep (se 1 (by rfl) ⟨1113989, by rfl⟩ : syracuseStep 1485319 = 2227979) B2227979
theorem B1485327 : Blo 1484062 1485327 := bstep (se 1 (by rfl) ⟨1113995, by rfl⟩ : syracuseStep 1485327 = 2227991) B2227991
theorem B1485371 : Blo 1484062 1485371 := bstep (se 1 (by rfl) ⟨1114028, by rfl⟩ : syracuseStep 1485371 = 2228057) B2228057
theorem B19032641 : Blo 1484062 19032641 := bstep (se 2 (by rfl) ⟨7137240, by rfl⟩ : syracuseStep 19032641 = 14274481) B14274481
theorem B6777431 : Blo 1484062 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B1485447 : Blo 1484062 1485447 := bstep (se 1 (by rfl) ⟨1114085, by rfl⟩ : syracuseStep 1485447 = 2228171) B2228171
theorem B1485455 : Blo 1484062 1485455 := bstep (se 1 (by rfl) ⟨1114091, by rfl⟩ : syracuseStep 1485455 = 2228183) B2228183
theorem B1485499 : Blo 1484062 1485499 := bstep (se 1 (by rfl) ⟨1114124, by rfl⟩ : syracuseStep 1485499 = 2228249) B2228249
theorem B1485575 : Blo 1484062 1485575 := bstep (se 1 (by rfl) ⟨1114181, by rfl⟩ : syracuseStep 1485575 = 2228363) B2228363
theorem B1608455 : Blo 1484062 1608455 := bstep (se 1 (by rfl) ⟨1206341, by rfl⟩ : syracuseStep 1608455 = 2412683) B2412683
theorem B3861263 : Blo 1484062 3861263 := bstep (se 1 (by rfl) ⟨2895947, by rfl⟩ : syracuseStep 3861263 = 5791895) B5791895
theorem B1485583 : Blo 1484062 1485583 := bstep (se 1 (by rfl) ⟨1114187, by rfl⟩ : syracuseStep 1485583 = 2228375) B2228375
theorem B8456993 : Blo 1484062 8456993 := bstep (se 2 (by rfl) ⟨3171372, by rfl⟩ : syracuseStep 8456993 = 6342745) B6342745
theorem B4229921 : Blo 1484062 4229921 := bstep (se 2 (by rfl) ⟨1586220, by rfl⟩ : syracuseStep 4229921 = 3172441) B3172441
theorem B1485627 : Blo 1484062 1485627 := bstep (se 1 (by rfl) ⟨1114220, by rfl⟩ : syracuseStep 1485627 = 2228441) B2228441
theorem B7138163 : Blo 1484062 7138163 := bstep (se 1 (by rfl) ⟨5353622, by rfl⟩ : syracuseStep 7138163 = 10707245) B10707245
theorem B1485703 : Blo 1484062 1485703 := bstep (se 1 (by rfl) ⟨1114277, by rfl⟩ : syracuseStep 1485703 = 2228555) B2228555
theorem B1485711 : Blo 1484062 1485711 := bstep (se 1 (by rfl) ⟨1114283, by rfl⟩ : syracuseStep 1485711 = 2228567) B2228567
theorem B1485755 : Blo 1484062 1485755 := bstep (se 1 (by rfl) ⟨1114316, by rfl⟩ : syracuseStep 1485755 = 2228633) B2228633
theorem B3566537 : Blo 1484062 3566537 := bstep (se 2 (by rfl) ⟨1337451, by rfl⟩ : syracuseStep 3566537 = 2674903) B2674903
theorem B1485831 : Blo 1484062 1485831 := bstep (se 1 (by rfl) ⟨1114373, by rfl⟩ : syracuseStep 1485831 = 2228747) B2228747
theorem B5639179 : Blo 1484062 5639179 := bstep (se 1 (by rfl) ⟨4229384, by rfl⟩ : syracuseStep 5639179 = 8458769) B8458769
theorem B20327435 : Blo 1484062 20327435 := bstep (se 1 (by rfl) ⟨15245576, by rfl⟩ : syracuseStep 20327435 = 30491153) B30491153
theorem B1485839 : Blo 1484062 1485839 := bstep (se 1 (by rfl) ⟨1114379, by rfl⟩ : syracuseStep 1485839 = 2228759) B2228759
theorem B7515179 : Blo 1484062 7515179 := bstep (se 1 (by rfl) ⟨5636384, by rfl⟩ : syracuseStep 7515179 = 11272769) B11272769
theorem B1485883 : Blo 1484062 1485883 := bstep (se 1 (by rfl) ⟨1114412, by rfl⟩ : syracuseStep 1485883 = 2228825) B2228825
theorem B1485959 : Blo 1484062 1485959 := bstep (se 1 (by rfl) ⟨1114469, by rfl⟩ : syracuseStep 1485959 = 2228939) B2228939
theorem B1485967 : Blo 1484062 1485967 := bstep (se 1 (by rfl) ⟨1114475, by rfl⟩ : syracuseStep 1485967 = 2228951) B2228951
theorem B1486011 : Blo 1484062 1486011 := bstep (se 1 (by rfl) ⟨1114508, by rfl⟩ : syracuseStep 1486011 = 2229017) B2229017
theorem B3566891 : Blo 1484062 3566891 := bstep (se 1 (by rfl) ⟨2675168, by rfl⟩ : syracuseStep 3566891 = 5350337) B5350337
theorem B5639483 : Blo 1484062 5639483 := bstep (se 1 (by rfl) ⟨4229612, by rfl⟩ : syracuseStep 5639483 = 8459225) B8459225
theorem B3173833 : Blo 1484062 3173833 := bstep (se 2 (by rfl) ⟨1190187, by rfl⟩ : syracuseStep 3173833 = 2380375) B2380375
theorem B7138763 : Blo 1484062 7138763 := bstep (se 1 (by rfl) ⟨5354072, by rfl⟩ : syracuseStep 7138763 = 10708145) B10708145
theorem B97643981 : Blo 1484062 97643981 := bstep (se 3 (by rfl) ⟨18308246, by rfl⟩ : syracuseStep 97643981 = 36616493) B36616493
theorem B4517437 : Blo 1484062 4517437 := bstep (se 3 (by rfl) ⟨847019, by rfl⟩ : syracuseStep 4517437 = 1694039) B1694039
theorem B81301133 : Blo 1484062 81301133 := bstep (se 3 (by rfl) ⟨15243962, by rfl⟩ : syracuseStep 81301133 = 30487925) B30487925
theorem B7139087 : Blo 1484062 7139087 := bstep (se 1 (by rfl) ⟨5354315, by rfl⟩ : syracuseStep 7139087 = 10708631) B10708631
theorem B5639969 : Blo 1484062 5639969 := bstep (se 2 (by rfl) ⟨2114988, by rfl⟩ : syracuseStep 5639969 = 4229977) B4229977
theorem B12062515 : Blo 1484062 12062515 := bstep (se 1 (by rfl) ⟨9046886, by rfl⟩ : syracuseStep 12062515 = 18093773) B18093773
theorem B9515069 : Blo 1484062 9515069 := bstep (se 3 (by rfl) ⟨1784075, by rfl⟩ : syracuseStep 9515069 = 3568151) B3568151
theorem B7622849 : Blo 1484062 7622849 := bstep (se 2 (by rfl) ⟨2858568, by rfl⟩ : syracuseStep 7622849 = 5717137) B5717137
theorem B4231435 : Blo 1484062 4231435 := bstep (se 1 (by rfl) ⟨3173576, by rfl⟩ : syracuseStep 4231435 = 6347153) B6347153
theorem B7516475 : Blo 1484062 7516475 := bstep (se 1 (by rfl) ⟨5637356, by rfl⟩ : syracuseStep 7516475 = 11274713) B11274713
theorem B2380151 : Blo 1484062 2380151 := bstep (se 1 (by rfl) ⟨1785113, by rfl⟩ : syracuseStep 2380151 = 3570227) B3570227
theorem B1880491 : Blo 1484062 1880491 := bstep (se 1 (by rfl) ⟨1410368, by rfl⟩ : syracuseStep 1880491 = 2820737) B2820737
theorem B5009849 : Blo 1484062 5009849 := bstep (se 2 (by rfl) ⟨1878693, by rfl⟩ : syracuseStep 5009849 = 3757387) B3757387
theorem B5353913 : Blo 1484062 5353913 := bstep (se 2 (by rfl) ⟨2007717, by rfl⟩ : syracuseStep 5353913 = 4015435) B4015435
theorem B7516637 : Blo 1484062 7516637 := bstep (se 3 (by rfl) ⟨1409369, by rfl⟩ : syracuseStep 7516637 = 2818739) B2818739
theorem B4231709 : Blo 1484062 4231709 := bstep (se 3 (by rfl) ⟨793445, by rfl⟩ : syracuseStep 4231709 = 1586891) B1586891
theorem B3756577 : Blo 1484062 3756577 := bstep (se 2 (by rfl) ⟨1408716, by rfl⟩ : syracuseStep 3756577 = 2817433) B2817433
theorem B5354027 : Blo 1484062 5354027 := bstep (se 1 (by rfl) ⟨4015520, by rfl⟩ : syracuseStep 5354027 = 8031041) B8031041
theorem B3568313 : Blo 1484062 3568313 := bstep (se 2 (by rfl) ⟨1338117, by rfl⟩ : syracuseStep 3568313 = 2676235) B2676235
theorem B5640941 : Blo 1484062 5640941 := bstep (se 3 (by rfl) ⟨1057676, by rfl⟩ : syracuseStep 5640941 = 2115353) B2115353
theorem B7516961 : Blo 1484062 7516961 := bstep (se 2 (by rfl) ⟨2818860, by rfl⟩ : syracuseStep 7516961 = 5637721) B5637721
theorem B3339143 : Blo 1484062 3339143 := bstep (se 1 (by rfl) ⟨2504357, by rfl⟩ : syracuseStep 3339143 = 5008715) B5008715
theorem B16921547 : Blo 1484062 16921547 := bstep (se 1 (by rfl) ⟨12691160, by rfl⟩ : syracuseStep 16921547 = 25382321) B25382321
theorem B5010443 : Blo 1484062 5010443 := bstep (se 1 (by rfl) ⟨3757832, by rfl⟩ : syracuseStep 5010443 = 7515665) B7515665
theorem B3339323 : Blo 1484062 3339323 := bstep (se 1 (by rfl) ⟨2504492, by rfl⟩ : syracuseStep 3339323 = 5008985) B5008985
theorem B5715011 : Blo 1484062 5715011 := bstep (se 1 (by rfl) ⟨4286258, by rfl⟩ : syracuseStep 5715011 = 8572517) B8572517
theorem B3757175 : Blo 1484062 3757175 := bstep (se 1 (by rfl) ⟨2817881, by rfl⟩ : syracuseStep 3757175 = 5635763) B5635763
theorem B5010551 : Blo 1484062 5010551 := bstep (se 1 (by rfl) ⟨3757913, by rfl⟩ : syracuseStep 5010551 = 7515827) B7515827
theorem B3339449 : Blo 1484062 3339449 := bstep (se 2 (by rfl) ⟨1252293, by rfl⟩ : syracuseStep 3339449 = 2504587) B2504587
theorem B2061559 : Blo 1484062 2061559 := bstep (se 1 (by rfl) ⟨1546169, by rfl⟩ : syracuseStep 2061559 = 3092339) B3092339
theorem B7230721 : Blo 1484062 7230721 := bstep (se 2 (by rfl) ⟨2711520, by rfl⟩ : syracuseStep 7230721 = 5423041) B5423041
theorem B7132475 : Blo 1484062 7132475 := bstep (se 1 (by rfl) ⟨5349356, by rfl⟩ : syracuseStep 7132475 = 10698713) B10698713
theorem B12686651 : Blo 1484062 12686651 := bstep (se 1 (by rfl) ⟨9514988, by rfl⟩ : syracuseStep 12686651 = 19029977) B19029977
theorem B1586575 : Blo 1484062 1586575 := bstep (se 1 (by rfl) ⟨1189931, by rfl⟩ : syracuseStep 1586575 = 2379863) B2379863
theorem B7140761 : Blo 1484062 7140761 := bstep (se 2 (by rfl) ⟨2677785, by rfl⟩ : syracuseStep 7140761 = 5355571) B5355571
theorem B6772177 : Blo 1484062 6772177 := bstep (se 2 (by rfl) ⟨2539566, by rfl⟩ : syracuseStep 6772177 = 5079133) B5079133
theorem B3339791 : Blo 1484062 3339791 := bstep (se 1 (by rfl) ⟨2504843, by rfl⟩ : syracuseStep 3339791 = 5009687) B5009687
theorem B3339809 : Blo 1484062 3339809 := bstep (se 2 (by rfl) ⟨1252428, by rfl⟩ : syracuseStep 3339809 = 2504857) B2504857
theorem B5011145 : Blo 1484062 5011145 := bstep (se 2 (by rfl) ⟨1879179, by rfl⟩ : syracuseStep 5011145 = 3758359) B3758359
theorem B7517933 : Blo 1484062 7517933 := bstep (se 3 (by rfl) ⟨1409612, by rfl⟩ : syracuseStep 7517933 = 2819225) B2819225
theorem B2676539 : Blo 1484062 2676539 := bstep (se 1 (by rfl) ⟨2007404, by rfl⟩ : syracuseStep 2676539 = 4014809) B4014809
theorem B3569467 : Blo 1484062 3569467 := bstep (se 1 (by rfl) ⟨2677100, by rfl⟩ : syracuseStep 3569467 = 5354201) B5354201
theorem B2504567 : Blo 1484062 2504567 := bstep (se 1 (by rfl) ⟨1878425, by rfl⟩ : syracuseStep 2504567 = 3756851) B3756851
theorem B3340151 : Blo 1484062 3340151 := bstep (se 1 (by rfl) ⟨2505113, by rfl⟩ : syracuseStep 3340151 = 5010227) B5010227
theorem B6019001 : Blo 1484062 6019001 := bstep (se 2 (by rfl) ⟨2257125, by rfl⟩ : syracuseStep 6019001 = 4514251) B4514251
theorem B2226107 : Blo 1484062 2226107 := bstep (se 1 (by rfl) ⟨1669580, by rfl⟩ : syracuseStep 2226107 = 3339161) B3339161
theorem B2226167 : Blo 1484062 2226167 := bstep (se 1 (by rfl) ⟨1669625, by rfl⟩ : syracuseStep 2226167 = 3339251) B3339251
theorem B6772747 : Blo 1484062 6772747 := bstep (se 1 (by rfl) ⟨5079560, by rfl⟩ : syracuseStep 6772747 = 10159121) B10159121
theorem B2226191 : Blo 1484062 2226191 := bstep (se 1 (by rfl) ⟨1669643, by rfl⟩ : syracuseStep 2226191 = 3339287) B3339287
theorem B3340331 : Blo 1484062 3340331 := bstep (se 1 (by rfl) ⟨2505248, by rfl⟩ : syracuseStep 3340331 = 5010497) B5010497
theorem B6346795 : Blo 1484062 6346795 := bstep (se 1 (by rfl) ⟨4760096, by rfl⟩ : syracuseStep 6346795 = 9520193) B9520193
theorem B2226233 : Blo 1484062 2226233 := bstep (se 2 (by rfl) ⟨834837, by rfl⟩ : syracuseStep 2226233 = 1669675) B1669675
theorem B8026199 : Blo 1484062 8026199 := bstep (se 1 (by rfl) ⟨6019649, by rfl⟩ : syracuseStep 8026199 = 12039299) B12039299
theorem B2226311 : Blo 1484062 2226311 := bstep (se 1 (by rfl) ⟨1669733, by rfl⟩ : syracuseStep 2226311 = 3339467) B3339467
theorem B1505423 : Blo 1484062 1505423 := bstep (se 1 (by rfl) ⟨1129067, by rfl⟩ : syracuseStep 1505423 = 2258135) B2258135
theorem B2226347 : Blo 1484062 2226347 := bstep (se 1 (by rfl) ⟨1669760, by rfl⟩ : syracuseStep 2226347 = 3339521) B3339521
theorem B2226377 : Blo 1484062 2226377 := bstep (se 2 (by rfl) ⟨834891, by rfl⟩ : syracuseStep 2226377 = 1669783) B1669783
theorem B12859681 : Blo 1484062 12859681 := bstep (se 2 (by rfl) ⟨4822380, by rfl⟩ : syracuseStep 12859681 = 9644761) B9644761
theorem B2226491 : Blo 1484062 2226491 := bstep (se 1 (by rfl) ⟨1669868, by rfl⟩ : syracuseStep 2226491 = 3339737) B3339737
theorem B2505019 : Blo 1484062 2505019 := bstep (se 1 (by rfl) ⟨1878764, by rfl⟩ : syracuseStep 2505019 = 3757529) B3757529
theorem B38558017 : Blo 1484062 38558017 := bstep (se 2 (by rfl) ⟨14459256, by rfl⟩ : syracuseStep 38558017 = 28918513) B28918513
theorem B2226551 : Blo 1484062 2226551 := bstep (se 1 (by rfl) ⟨1669913, by rfl⟩ : syracuseStep 2226551 = 3339827) B3339827
theorem B3758471 : Blo 1484062 3758471 := bstep (se 1 (by rfl) ⟨2818853, by rfl⟩ : syracuseStep 3758471 = 5637707) B5637707
theorem B5011847 : Blo 1484062 5011847 := bstep (se 1 (by rfl) ⟨3758885, by rfl⟩ : syracuseStep 5011847 = 7517771) B7517771
theorem B2226575 : Blo 1484062 2226575 := bstep (se 1 (by rfl) ⟨1669931, by rfl⟩ : syracuseStep 2226575 = 3339863) B3339863
theorem B3340691 : Blo 1484062 3340691 := bstep (se 1 (by rfl) ⟨2505518, by rfl⟩ : syracuseStep 3340691 = 5011037) B5011037
theorem B2226617 : Blo 1484062 2226617 := bstep (se 2 (by rfl) ⟨834981, by rfl⟩ : syracuseStep 2226617 = 1669963) B1669963
theorem B3758521 : Blo 1484062 3758521 := bstep (se 2 (by rfl) ⟨1409445, by rfl⟩ : syracuseStep 3758521 = 2818891) B2818891
theorem B2505161 : Blo 1484062 2505161 := bstep (se 2 (by rfl) ⟨939435, by rfl⟩ : syracuseStep 2505161 = 1878871) B1878871
theorem B3340745 : Blo 1484062 3340745 := bstep (se 2 (by rfl) ⟨1252779, by rfl⟩ : syracuseStep 3340745 = 2505559) B2505559
theorem B1669639 : Blo 1484062 1669639 := bstep (se 1 (by rfl) ⟨1252229, by rfl⟩ : syracuseStep 1669639 = 2504459) B2504459
theorem B2226695 : Blo 1484062 2226695 := bstep (se 1 (by rfl) ⟨1670021, by rfl⟩ : syracuseStep 2226695 = 3340043) B3340043
theorem B8452619 : Blo 1484062 8452619 := bstep (se 1 (by rfl) ⟨6339464, by rfl⟩ : syracuseStep 8452619 = 12678929) B12678929
theorem B7518743 : Blo 1484062 7518743 := bstep (se 1 (by rfl) ⟨5639057, by rfl⟩ : syracuseStep 7518743 = 11278115) B11278115
theorem B2226731 : Blo 1484062 2226731 := bstep (se 1 (by rfl) ⟨1670048, by rfl⟩ : syracuseStep 2226731 = 3340097) B3340097
theorem B2226761 : Blo 1484062 2226761 := bstep (se 2 (by rfl) ⟨835035, by rfl⟩ : syracuseStep 2226761 = 1670071) B1670071
theorem B1669819 : Blo 1484062 1669819 := bstep (se 1 (by rfl) ⟨1252364, by rfl⟩ : syracuseStep 1669819 = 2504729) B2504729
theorem B2226875 : Blo 1484062 2226875 := bstep (se 1 (by rfl) ⟨1670156, by rfl⟩ : syracuseStep 2226875 = 3340313) B3340313
theorem B1694395 : Blo 1484062 1694395 := bstep (se 1 (by rfl) ⟨1270796, by rfl⟩ : syracuseStep 1694395 = 2541593) B2541593
theorem B2226935 : Blo 1484062 2226935 := bstep (se 1 (by rfl) ⟨1670201, by rfl⟩ : syracuseStep 2226935 = 3340403) B3340403
theorem B6339329 : Blo 1484062 6339329 := bstep (se 2 (by rfl) ⟨2377248, by rfl⟩ : syracuseStep 6339329 = 4754497) B4754497
theorem B5012225 : Blo 1484062 5012225 := bstep (se 2 (by rfl) ⟨1879584, by rfl⟩ : syracuseStep 5012225 = 3759169) B3759169
theorem B2226959 : Blo 1484062 2226959 := bstep (se 1 (by rfl) ⟨1670219, by rfl⟩ : syracuseStep 2226959 = 3340439) B3340439
theorem B2227001 : Blo 1484062 2227001 := bstep (se 2 (by rfl) ⟨835125, by rfl⟩ : syracuseStep 2227001 = 1670251) B1670251
theorem B5077819 : Blo 1484062 5077819 := bstep (se 1 (by rfl) ⟨3808364, by rfl⟩ : syracuseStep 5077819 = 7616729) B7616729
theorem B2005879 : Blo 1484062 2005879 := bstep (se 1 (by rfl) ⟨1504409, by rfl⟩ : syracuseStep 2005879 = 3008819) B3008819
theorem B2227079 : Blo 1484062 2227079 := bstep (se 1 (by rfl) ⟨1670309, by rfl⟩ : syracuseStep 2227079 = 3340619) B3340619
theorem B2227115 : Blo 1484062 2227115 := bstep (se 1 (by rfl) ⟨1670336, by rfl⟩ : syracuseStep 2227115 = 3340673) B3340673
theorem B2227145 : Blo 1484062 2227145 := bstep (se 2 (by rfl) ⟨835179, by rfl⟩ : syracuseStep 2227145 = 1670359) B1670359
theorem B6962129 : Blo 1484062 6962129 := bstep (se 2 (by rfl) ⟨2610798, by rfl⟩ : syracuseStep 6962129 = 5221597) B5221597
theorem B3759119 : Blo 1484062 3759119 := bstep (se 1 (by rfl) ⟨2819339, by rfl⟩ : syracuseStep 3759119 = 5638679) B5638679
theorem B2227259 : Blo 1484062 2227259 := bstep (se 1 (by rfl) ⟨1670444, by rfl⟩ : syracuseStep 2227259 = 3340889) B3340889
theorem B6339703 : Blo 1484062 6339703 := bstep (se 1 (by rfl) ⟨4754777, by rfl⟩ : syracuseStep 6339703 = 9509555) B9509555
theorem B2227319 : Blo 1484062 2227319 := bstep (se 1 (by rfl) ⟨1670489, by rfl⟩ : syracuseStep 2227319 = 3340979) B3340979
theorem B2505863 : Blo 1484062 2505863 := bstep (se 1 (by rfl) ⟨1879397, by rfl⟩ : syracuseStep 2505863 = 3758795) B3758795
theorem B3341447 : Blo 1484062 3341447 := bstep (se 1 (by rfl) ⟨2506085, by rfl⟩ : syracuseStep 3341447 = 5012171) B5012171
theorem B1670287 : Blo 1484062 1670287 := bstep (se 1 (by rfl) ⟨1252715, by rfl⟩ : syracuseStep 1670287 = 2505431) B2505431
theorem B2227343 : Blo 1484062 2227343 := bstep (se 1 (by rfl) ⟨1670507, by rfl⟩ : syracuseStep 2227343 = 3341015) B3341015
theorem B4226195 : Blo 1484062 4226195 := bstep (se 1 (by rfl) ⟨3169646, by rfl⟩ : syracuseStep 4226195 = 6339293) B6339293
theorem B1809551 : Blo 1484062 1809551 := bstep (se 1 (by rfl) ⟨1357163, by rfl⟩ : syracuseStep 1809551 = 2714327) B2714327
theorem B2227385 : Blo 1484062 2227385 := bstep (se 2 (by rfl) ⟨835269, by rfl⟩ : syracuseStep 2227385 = 1670539) B1670539
theorem B16268525 : Blo 1484062 16268525 := bstep (se 3 (by rfl) ⟨3050348, by rfl⟩ : syracuseStep 16268525 = 6100697) B6100697
theorem B2227463 : Blo 1484062 2227463 := bstep (se 1 (by rfl) ⟨1670597, by rfl⟩ : syracuseStep 2227463 = 3341195) B3341195
theorem B2227499 : Blo 1484062 2227499 := bstep (se 1 (by rfl) ⟨1670624, by rfl⟩ : syracuseStep 2227499 = 3341249) B3341249
theorem B3341627 : Blo 1484062 3341627 := bstep (se 1 (by rfl) ⟨2506220, by rfl⟩ : syracuseStep 3341627 = 5012441) B5012441
theorem B2227529 : Blo 1484062 2227529 := bstep (se 2 (by rfl) ⟨835323, by rfl⟩ : syracuseStep 2227529 = 1670647) B1670647
theorem B3341753 : Blo 1484062 3341753 := bstep (se 2 (by rfl) ⟨1253157, by rfl⟩ : syracuseStep 3341753 = 2506315) B2506315
theorem B2227643 : Blo 1484062 2227643 := bstep (se 1 (by rfl) ⟨1670732, by rfl⟩ : syracuseStep 2227643 = 3341465) B3341465
theorem B2227703 : Blo 1484062 2227703 := bstep (se 1 (by rfl) ⟨1670777, by rfl⟩ : syracuseStep 2227703 = 3341555) B3341555
theorem B5635595 : Blo 1484062 5635595 := bstep (se 1 (by rfl) ⟨4226696, by rfl⟩ : syracuseStep 5635595 = 8453393) B8453393
theorem B2227727 : Blo 1484062 2227727 := bstep (se 1 (by rfl) ⟨1670795, by rfl⟩ : syracuseStep 2227727 = 3341591) B3341591
theorem B5013035 : Blo 1484062 5013035 := bstep (se 1 (by rfl) ⟨3759776, by rfl⟩ : syracuseStep 5013035 = 7519553) B7519553
theorem B8461867 : Blo 1484062 8461867 := bstep (se 1 (by rfl) ⟨6346400, by rfl⟩ : syracuseStep 8461867 = 12692801) B12692801
theorem B2227769 : Blo 1484062 2227769 := bstep (se 2 (by rfl) ⟨835413, by rfl⟩ : syracuseStep 2227769 = 1670827) B1670827
theorem B1670791 : Blo 1484062 1670791 := bstep (se 1 (by rfl) ⟨1253093, by rfl⟩ : syracuseStep 1670791 = 2506187) B2506187
theorem B2227847 : Blo 1484062 2227847 := bstep (se 1 (by rfl) ⟨1670885, by rfl⟩ : syracuseStep 2227847 = 3341771) B3341771
theorem B2227883 : Blo 1484062 2227883 := bstep (se 1 (by rfl) ⟨1670912, by rfl⟩ : syracuseStep 2227883 = 3341825) B3341825
theorem B2817737 : Blo 1484062 2817737 := bstep (se 2 (by rfl) ⟨1056651, by rfl⟩ : syracuseStep 2817737 = 2113303) B2113303
theorem B2227913 : Blo 1484062 2227913 := bstep (se 2 (by rfl) ⟨835467, by rfl⟩ : syracuseStep 2227913 = 1670935) B1670935
theorem B3759817 : Blo 1484062 3759817 := bstep (se 2 (by rfl) ⟨1409931, by rfl⟩ : syracuseStep 3759817 = 2819863) B2819863
theorem B13549285 : Blo 1484062 13549285 := bstep (se 4 (by rfl) ⟨1270245, by rfl⟩ : syracuseStep 13549285 = 2540491) B2540491
theorem B8027885 : Blo 1484062 8027885 := bstep (se 3 (by rfl) ⟨1505228, by rfl⟩ : syracuseStep 8027885 = 3010457) B3010457
theorem B2506511 : Blo 1484062 2506511 := bstep (se 1 (by rfl) ⟨1879883, by rfl⟩ : syracuseStep 2506511 = 3759767) B3759767
theorem B3342095 : Blo 1484062 3342095 := bstep (se 1 (by rfl) ⟨2506571, by rfl⟩ : syracuseStep 3342095 = 5013143) B5013143
theorem B3342113 : Blo 1484062 3342113 := bstep (se 2 (by rfl) ⟨1253292, by rfl⟩ : syracuseStep 3342113 = 2506585) B2506585
theorem B2113337 : Blo 1484062 2113337 := bstep (se 2 (by rfl) ⟨792501, by rfl⟩ : syracuseStep 2113337 = 1585003) B1585003
theorem B1670971 : Blo 1484062 1670971 := bstep (se 1 (by rfl) ⟨1253228, by rfl⟩ : syracuseStep 1670971 = 2506457) B2506457
theorem B2228027 : Blo 1484062 2228027 := bstep (se 1 (by rfl) ⟨1671020, by rfl⟩ : syracuseStep 2228027 = 3342041) B3342041
theorem B3759959 : Blo 1484062 3759959 := bstep (se 1 (by rfl) ⟨2819969, by rfl⟩ : syracuseStep 3759959 = 5639939) B5639939
theorem B2228087 : Blo 1484062 2228087 := bstep (se 1 (by rfl) ⟨1671065, by rfl⟩ : syracuseStep 2228087 = 3342131) B3342131
theorem B2228111 : Blo 1484062 2228111 := bstep (se 1 (by rfl) ⟨1671083, by rfl⟩ : syracuseStep 2228111 = 3342167) B3342167
theorem B19816343 : Blo 1484062 19816343 := bstep (se 1 (by rfl) ⟨14862257, by rfl⟩ : syracuseStep 19816343 = 29724515) B29724515
theorem B2228153 : Blo 1484062 2228153 := bstep (se 2 (by rfl) ⟨835557, by rfl⟩ : syracuseStep 2228153 = 1671115) B1671115
theorem B8462393 : Blo 1484062 8462393 := bstep (se 2 (by rfl) ⟨3173397, by rfl⟩ : syracuseStep 8462393 = 6346795) B6346795
theorem B2228303 : Blo 1484062 2228303 := bstep (se 1 (by rfl) ⟨1671227, by rfl⟩ : syracuseStep 2228303 = 3342455) B3342455
theorem B5636249 : Blo 1484062 5636249 := bstep (se 2 (by rfl) ⟨2113593, by rfl⟩ : syracuseStep 5636249 = 4227187) B4227187
theorem B2228423 : Blo 1484062 2228423 := bstep (se 1 (by rfl) ⟨1671317, by rfl⟩ : syracuseStep 2228423 = 3342635) B3342635
theorem B1671367 : Blo 1484062 1671367 := bstep (se 1 (by rfl) ⟨1253525, by rfl⟩ : syracuseStep 1671367 = 2507051) B2507051
theorem B2228585 : Blo 1484062 2228585 := bstep (se 2 (by rfl) ⟨835719, by rfl⟩ : syracuseStep 2228585 = 1671439) B1671439
theorem B4014461 : Blo 1484062 4014461 := bstep (se 3 (by rfl) ⟨752711, by rfl⟩ : syracuseStep 4014461 = 1505423) B1505423
theorem B4825469 : Blo 1484062 4825469 := bstep (se 3 (by rfl) ⟨904775, by rfl⟩ : syracuseStep 4825469 = 1809551) B1809551
theorem B17146241 : Blo 1484062 17146241 := bstep (se 2 (by rfl) ⟨6429840, by rfl⟩ : syracuseStep 17146241 = 12859681) B12859681
theorem B2113975 : Blo 1484062 2113975 := bstep (se 1 (by rfl) ⟨1585481, by rfl⟩ : syracuseStep 2113975 = 3170963) B3170963
theorem B2228663 : Blo 1484062 2228663 := bstep (se 1 (by rfl) ⟨1671497, by rfl⟩ : syracuseStep 2228663 = 3342995) B3342995
theorem B2228699 : Blo 1484062 2228699 := bstep (se 1 (by rfl) ⟨1671524, by rfl⟩ : syracuseStep 2228699 = 3343049) B3343049
theorem B3760627 : Blo 1484062 3760627 := bstep (se 1 (by rfl) ⟨2820470, by rfl⟩ : syracuseStep 3760627 = 5640941) B5640941
theorem B7332377 : Blo 1484062 7332377 := bstep (se 2 (by rfl) ⟨2749641, by rfl⟩ : syracuseStep 7332377 = 5499283) B5499283
theorem B3342887 : Blo 1484062 3342887 := bstep (se 1 (by rfl) ⟨2507165, by rfl⟩ : syracuseStep 3342887 = 5014331) B5014331
theorem B2507321 : Blo 1484062 2507321 := bstep (se 2 (by rfl) ⟨940245, by rfl⟩ : syracuseStep 2507321 = 1880491) B1880491
theorem B11281031 : Blo 1484062 11281031 := bstep (se 1 (by rfl) ⟨8460773, by rfl⟩ : syracuseStep 11281031 = 16921547) B16921547
theorem B3810007 : Blo 1484062 3810007 := bstep (se 1 (by rfl) ⟨2857505, by rfl⟩ : syracuseStep 3810007 = 5715011) B5715011
theorem B3343211 : Blo 1484062 3343211 := bstep (se 1 (by rfl) ⟨2507408, by rfl⟩ : syracuseStep 3343211 = 5014817) B5014817
theorem B3343265 : Blo 1484062 3343265 := bstep (se 2 (by rfl) ⟨1253724, by rfl⟩ : syracuseStep 3343265 = 2507449) B2507449
theorem B4760507 : Blo 1484062 4760507 := bstep (se 1 (by rfl) ⟨3570380, by rfl⟩ : syracuseStep 4760507 = 7140761) B7140761
theorem B5014547 : Blo 1484062 5014547 := bstep (se 1 (by rfl) ⟨3760910, by rfl⟩ : syracuseStep 5014547 = 7521821) B7521821
theorem B21398579 : Blo 1484062 21398579 := bstep (se 1 (by rfl) ⟨16048934, by rfl⟩ : syracuseStep 21398579 = 32097869) B32097869
theorem B5637235 : Blo 1484062 5637235 := bstep (se 1 (by rfl) ⟨4227926, by rfl⟩ : syracuseStep 5637235 = 8455853) B8455853
theorem B2819195 : Blo 1484062 2819195 := bstep (se 1 (by rfl) ⟨2114396, by rfl⟩ : syracuseStep 2819195 = 4228793) B4228793
theorem B3343607 : Blo 1484062 3343607 := bstep (se 1 (by rfl) ⟨2507705, by rfl⟩ : syracuseStep 3343607 = 5015411) B5015411
theorem B1484071 : Blo 1484062 1484071 := bstep (se 1 (by rfl) ⟨1113053, by rfl⟩ : syracuseStep 1484071 = 2226107) B2226107
theorem B1484111 : Blo 1484062 1484111 := bstep (se 1 (by rfl) ⟨1113083, by rfl⟩ : syracuseStep 1484111 = 2226167) B2226167
theorem B5014871 : Blo 1484062 5014871 := bstep (se 1 (by rfl) ⟨3761153, by rfl⟩ : syracuseStep 5014871 = 7522307) B7522307
theorem B1484127 : Blo 1484062 1484127 := bstep (se 1 (by rfl) ⟨1113095, by rfl⟩ : syracuseStep 1484127 = 2226191) B2226191
theorem B2819423 : Blo 1484062 2819423 := bstep (se 1 (by rfl) ⟨2114567, by rfl⟩ : syracuseStep 2819423 = 4229135) B4229135
theorem B1484155 : Blo 1484062 1484155 := bstep (se 1 (by rfl) ⟨1113116, by rfl⟩ : syracuseStep 1484155 = 2226233) B2226233
theorem B5350799 : Blo 1484062 5350799 := bstep (se 1 (by rfl) ⟨4013099, by rfl⟩ : syracuseStep 5350799 = 8026199) B8026199
theorem B1484207 : Blo 1484062 1484207 := bstep (se 1 (by rfl) ⟨1113155, by rfl⟩ : syracuseStep 1484207 = 2226311) B2226311
theorem B1484231 : Blo 1484062 1484231 := bstep (se 1 (by rfl) ⟨1113173, by rfl⟩ : syracuseStep 1484231 = 2226347) B2226347
theorem B1484251 : Blo 1484062 1484251 := bstep (se 1 (by rfl) ⟨1113188, by rfl⟩ : syracuseStep 1484251 = 2226377) B2226377
theorem B1484327 : Blo 1484062 1484327 := bstep (se 1 (by rfl) ⟨1113245, by rfl⟩ : syracuseStep 1484327 = 2226491) B2226491
theorem B9520679 : Blo 1484062 9520679 := bstep (se 1 (by rfl) ⟨7140509, by rfl⟩ : syracuseStep 9520679 = 14281019) B14281019
theorem B1484367 : Blo 1484062 1484367 := bstep (se 1 (by rfl) ⟨1113275, by rfl⟩ : syracuseStep 1484367 = 2226551) B2226551
theorem B1484383 : Blo 1484062 1484383 := bstep (se 1 (by rfl) ⟨1113287, by rfl⟩ : syracuseStep 1484383 = 2226575) B2226575
theorem B2819681 : Blo 1484062 2819681 := bstep (se 2 (by rfl) ⟨1057380, by rfl⟩ : syracuseStep 2819681 = 2114761) B2114761
theorem B1484411 : Blo 1484062 1484411 := bstep (se 1 (by rfl) ⟨1113308, by rfl⟩ : syracuseStep 1484411 = 2226617) B2226617
theorem B1484463 : Blo 1484062 1484463 := bstep (se 1 (by rfl) ⟨1113347, by rfl⟩ : syracuseStep 1484463 = 2226695) B2226695
theorem B1484487 : Blo 1484062 1484487 := bstep (se 1 (by rfl) ⟨1113365, by rfl⟩ : syracuseStep 1484487 = 2226731) B2226731
theorem B1484507 : Blo 1484062 1484507 := bstep (se 1 (by rfl) ⟨1113380, by rfl⟩ : syracuseStep 1484507 = 2226761) B2226761
theorem B1484583 : Blo 1484062 1484583 := bstep (se 1 (by rfl) ⟨1113437, by rfl⟩ : syracuseStep 1484583 = 2226875) B2226875
theorem B1484623 : Blo 1484062 1484623 := bstep (se 1 (by rfl) ⟨1113467, by rfl⟩ : syracuseStep 1484623 = 2226935) B2226935
theorem B1484639 : Blo 1484062 1484639 := bstep (se 1 (by rfl) ⟨1113479, by rfl⟩ : syracuseStep 1484639 = 2226959) B2226959
theorem B2574175 : Blo 1484062 2574175 := bstep (se 1 (by rfl) ⟨1930631, by rfl⟩ : syracuseStep 2574175 = 3861263) B3861263
theorem B2115433 : Blo 1484062 2115433 := bstep (se 2 (by rfl) ⟨793287, by rfl⟩ : syracuseStep 2115433 = 1586575) B1586575
theorem B5637995 : Blo 1484062 5637995 := bstep (se 1 (by rfl) ⟨4228496, by rfl⟩ : syracuseStep 5637995 = 8456993) B8456993
theorem B2819947 : Blo 1484062 2819947 := bstep (se 1 (by rfl) ⟨2114960, by rfl⟩ : syracuseStep 2819947 = 4229921) B4229921
theorem B1484667 : Blo 1484062 1484667 := bstep (se 1 (by rfl) ⟨1113500, by rfl⟩ : syracuseStep 1484667 = 2227001) B2227001
theorem B1484719 : Blo 1484062 1484719 := bstep (se 1 (by rfl) ⟨1113539, by rfl⟩ : syracuseStep 1484719 = 2227079) B2227079
theorem B9029569 : Blo 1484062 9029569 := bstep (se 2 (by rfl) ⟨3386088, by rfl⟩ : syracuseStep 9029569 = 6772177) B6772177
theorem B1484743 : Blo 1484062 1484743 := bstep (se 1 (by rfl) ⟨1113557, by rfl⟩ : syracuseStep 1484743 = 2227115) B2227115
theorem B2377691 : Blo 1484062 2377691 := bstep (se 1 (by rfl) ⟨1783268, by rfl⟩ : syracuseStep 2377691 = 3566537) B3566537
theorem B1484763 : Blo 1484062 1484763 := bstep (se 1 (by rfl) ⟨1113572, by rfl⟩ : syracuseStep 1484763 = 2227145) B2227145
theorem B13551623 : Blo 1484062 13551623 := bstep (se 1 (by rfl) ⟨10163717, by rfl⟩ : syracuseStep 13551623 = 20327435) B20327435
theorem B1484839 : Blo 1484062 1484839 := bstep (se 1 (by rfl) ⟨1113629, by rfl⟩ : syracuseStep 1484839 = 2227259) B2227259
theorem B11282489 : Blo 1484062 11282489 := bstep (se 2 (by rfl) ⟨4230933, by rfl⟩ : syracuseStep 11282489 = 8461867) B8461867
theorem B1484879 : Blo 1484062 1484879 := bstep (se 1 (by rfl) ⟨1113659, by rfl⟩ : syracuseStep 1484879 = 2227319) B2227319
theorem B6023249 : Blo 1484062 6023249 := bstep (se 2 (by rfl) ⟨2258718, by rfl⟩ : syracuseStep 6023249 = 4517437) B4517437
theorem B1484895 : Blo 1484062 1484895 := bstep (se 1 (by rfl) ⟨1113671, by rfl⟩ : syracuseStep 1484895 = 2227343) B2227343
theorem B1484923 : Blo 1484062 1484923 := bstep (se 1 (by rfl) ⟨1113692, by rfl⟩ : syracuseStep 1484923 = 2227385) B2227385
theorem B1484975 : Blo 1484062 1484975 := bstep (se 1 (by rfl) ⟨1113731, by rfl⟩ : syracuseStep 1484975 = 2227463) B2227463
theorem B2377927 : Blo 1484062 2377927 := bstep (se 1 (by rfl) ⟨1783445, by rfl⟩ : syracuseStep 2377927 = 3566891) B3566891
theorem B1484999 : Blo 1484062 1484999 := bstep (se 1 (by rfl) ⟨1113749, by rfl⟩ : syracuseStep 1484999 = 2227499) B2227499
theorem B1485019 : Blo 1484062 1485019 := bstep (se 1 (by rfl) ⟨1113764, by rfl⟩ : syracuseStep 1485019 = 2227529) B2227529
theorem B1485095 : Blo 1484062 1485095 := bstep (se 1 (by rfl) ⟨1113821, by rfl⟩ : syracuseStep 1485095 = 2227643) B2227643
theorem B18065713 : Blo 1484062 18065713 := bstep (se 2 (by rfl) ⟨6774642, by rfl⟩ : syracuseStep 18065713 = 13549285) B13549285
theorem B65095987 : Blo 1484062 65095987 := bstep (se 1 (by rfl) ⟨48821990, by rfl⟩ : syracuseStep 65095987 = 97643981) B97643981
theorem B1485135 : Blo 1484062 1485135 := bstep (se 1 (by rfl) ⟨1113851, by rfl⟩ : syracuseStep 1485135 = 2227703) B2227703
theorem B1485151 : Blo 1484062 1485151 := bstep (se 1 (by rfl) ⟨1113863, by rfl⟩ : syracuseStep 1485151 = 2227727) B2227727
theorem B1485179 : Blo 1484062 1485179 := bstep (se 1 (by rfl) ⟨1113884, by rfl⟩ : syracuseStep 1485179 = 2227769) B2227769
theorem B16083353 : Blo 1484062 16083353 := bstep (se 2 (by rfl) ⟨6031257, by rfl⟩ : syracuseStep 16083353 = 12062515) B12062515
theorem B1485231 : Blo 1484062 1485231 := bstep (se 1 (by rfl) ⟨1113923, by rfl⟩ : syracuseStep 1485231 = 2227847) B2227847
theorem B54200755 : Blo 1484062 54200755 := bstep (se 1 (by rfl) ⟨40650566, by rfl⟩ : syracuseStep 54200755 = 81301133) B81301133
theorem B1485255 : Blo 1484062 1485255 := bstep (se 1 (by rfl) ⟨1113941, by rfl⟩ : syracuseStep 1485255 = 2227883) B2227883
theorem B1878491 : Blo 1484062 1878491 := bstep (se 1 (by rfl) ⟨1408868, by rfl⟩ : syracuseStep 1878491 = 2817737) B2817737
theorem B1485275 : Blo 1484062 1485275 := bstep (se 1 (by rfl) ⟨1113956, by rfl⟩ : syracuseStep 1485275 = 2227913) B2227913
theorem B5351923 : Blo 1484062 5351923 := bstep (se 1 (by rfl) ⟨4013942, by rfl⟩ : syracuseStep 5351923 = 8027885) B8027885
theorem B1485351 : Blo 1484062 1485351 := bstep (se 1 (by rfl) ⟨1114013, by rfl⟩ : syracuseStep 1485351 = 2228027) B2228027
theorem B1485391 : Blo 1484062 1485391 := bstep (se 1 (by rfl) ⟨1114043, by rfl⟩ : syracuseStep 1485391 = 2228087) B2228087
theorem B1485407 : Blo 1484062 1485407 := bstep (se 1 (by rfl) ⟨1114055, by rfl⟩ : syracuseStep 1485407 = 2228111) B2228111
theorem B1485435 : Blo 1484062 1485435 := bstep (se 1 (by rfl) ⟨1114076, by rfl⟩ : syracuseStep 1485435 = 2228153) B2228153
theorem B1485487 : Blo 1484062 1485487 := bstep (se 1 (by rfl) ⟨1114115, by rfl⟩ : syracuseStep 1485487 = 2228231) B2228231
theorem B9030329 : Blo 1484062 9030329 := bstep (se 2 (by rfl) ⟨3386373, by rfl⟩ : syracuseStep 9030329 = 6772747) B6772747
theorem B1485511 : Blo 1484062 1485511 := bstep (se 1 (by rfl) ⟨1114133, by rfl⟩ : syracuseStep 1485511 = 2228267) B2228267
theorem B6343379 : Blo 1484062 6343379 := bstep (se 1 (by rfl) ⟨4757534, by rfl⟩ : syracuseStep 6343379 = 9515069) B9515069
theorem B1485531 : Blo 1484062 1485531 := bstep (se 1 (by rfl) ⟨1114148, by rfl⟩ : syracuseStep 1485531 = 2228297) B2228297
theorem B1485607 : Blo 1484062 1485607 := bstep (se 1 (by rfl) ⟨1114205, by rfl⟩ : syracuseStep 1485607 = 2228411) B2228411
theorem B1485647 : Blo 1484062 1485647 := bstep (se 1 (by rfl) ⟨1114235, by rfl⟩ : syracuseStep 1485647 = 2228471) B2228471
theorem B1485663 : Blo 1484062 1485663 := bstep (se 1 (by rfl) ⟨1114247, by rfl⟩ : syracuseStep 1485663 = 2228495) B2228495
theorem B1485691 : Blo 1484062 1485691 := bstep (se 1 (by rfl) ⟨1114268, by rfl⟩ : syracuseStep 1485691 = 2228537) B2228537
theorem B1485743 : Blo 1484062 1485743 := bstep (se 1 (by rfl) ⟨1114307, by rfl⟩ : syracuseStep 1485743 = 2228615) B2228615
theorem B1878967 : Blo 1484062 1878967 := bstep (se 1 (by rfl) ⟨1409225, by rfl⟩ : syracuseStep 1878967 = 2818451) B2818451
theorem B3173303 : Blo 1484062 3173303 := bstep (se 1 (by rfl) ⟨2379977, by rfl⟩ : syracuseStep 3173303 = 4759955) B4759955
theorem B1485767 : Blo 1484062 1485767 := bstep (se 1 (by rfl) ⟨1114325, by rfl⟩ : syracuseStep 1485767 = 2228651) B2228651
theorem B1485787 : Blo 1484062 1485787 := bstep (se 1 (by rfl) ⟨1114340, by rfl⟩ : syracuseStep 1485787 = 2228681) B2228681
theorem B2821139 : Blo 1484062 2821139 := bstep (se 1 (by rfl) ⟨2115854, by rfl⟩ : syracuseStep 2821139 = 4231709) B4231709
theorem B1485863 : Blo 1484062 1485863 := bstep (se 1 (by rfl) ⟨1114397, by rfl⟩ : syracuseStep 1485863 = 2228795) B2228795
theorem B1485903 : Blo 1484062 1485903 := bstep (se 1 (by rfl) ⟨1114427, by rfl⟩ : syracuseStep 1485903 = 2228855) B2228855
theorem B1485919 : Blo 1484062 1485919 := bstep (se 1 (by rfl) ⟨1114439, by rfl⟩ : syracuseStep 1485919 = 2228879) B2228879
theorem B1485947 : Blo 1484062 1485947 := bstep (se 1 (by rfl) ⟨1114460, by rfl⟩ : syracuseStep 1485947 = 2228921) B2228921
theorem B20327597 : Blo 1484062 20327597 := bstep (se 3 (by rfl) ⟨3811424, by rfl⟩ : syracuseStep 20327597 = 7622849) B7622849
theorem B1485999 : Blo 1484062 1485999 := bstep (se 1 (by rfl) ⟨1114499, by rfl⟩ : syracuseStep 1485999 = 2228999) B2228999
theorem B1486023 : Blo 1484062 1486023 := bstep (se 1 (by rfl) ⟨1114517, by rfl⟩ : syracuseStep 1486023 = 2229035) B2229035
theorem B1486043 : Blo 1484062 1486043 := bstep (se 1 (by rfl) ⟨1114532, by rfl⟩ : syracuseStep 1486043 = 2229065) B2229065
theorem B5008769 : Blo 1484062 5008769 := bstep (se 2 (by rfl) ⟨1878288, by rfl⟩ : syracuseStep 5008769 = 3756577) B3756577
theorem B11275685 : Blo 1484062 11275685 := bstep (se 4 (by rfl) ⟨1057095, by rfl⟩ : syracuseStep 11275685 = 2114191) B2114191
theorem B14462381 : Blo 1484062 14462381 := bstep (se 3 (by rfl) ⟨2711696, by rfl⟩ : syracuseStep 14462381 = 5423393) B5423393
theorem B4754983 : Blo 1484062 4754983 := bstep (se 1 (by rfl) ⟨3566237, by rfl⟩ : syracuseStep 4754983 = 7132475) B7132475
theorem B8457767 : Blo 1484062 8457767 := bstep (se 1 (by rfl) ⟨6343325, by rfl⟩ : syracuseStep 8457767 = 12686651) B12686651
theorem B6770425 : Blo 1484062 6770425 := bstep (se 2 (by rfl) ⟨2538909, by rfl⟩ : syracuseStep 6770425 = 5077819) B5077819
theorem B2674505 : Blo 1484062 2674505 := bstep (se 2 (by rfl) ⟨1002939, by rfl⟩ : syracuseStep 2674505 = 2005879) B2005879
theorem B6025067 : Blo 1484062 6025067 := bstep (se 1 (by rfl) ⟨4518800, by rfl⟩ : syracuseStep 6025067 = 9037601) B9037601
theorem B11284433 : Blo 1484062 11284433 := bstep (se 2 (by rfl) ⟨4231662, by rfl⟩ : syracuseStep 11284433 = 8463325) B8463325
theorem B5009579 : Blo 1484062 5009579 := bstep (se 1 (by rfl) ⟨3757184, by rfl⟩ : syracuseStep 5009579 = 7514369) B7514369
theorem B1880263 : Blo 1484062 1880263 := bstep (se 1 (by rfl) ⟨1410197, by rfl⟩ : syracuseStep 1880263 = 2820395) B2820395
theorem B5353739 : Blo 1484062 5353739 := bstep (se 1 (by rfl) ⟨4015304, by rfl⟩ : syracuseStep 5353739 = 8030609) B8030609
theorem B2748745 : Blo 1484062 2748745 := bstep (se 2 (by rfl) ⟨1030779, by rfl⟩ : syracuseStep 2748745 = 2061559) B2061559
theorem B4518287 : Blo 1484062 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B9515501 : Blo 1484062 9515501 := bstep (se 3 (by rfl) ⟨1784156, by rfl⟩ : syracuseStep 9515501 = 3568313) B3568313
theorem B4231777 : Blo 1484062 4231777 := bstep (se 2 (by rfl) ⟨1586916, by rfl⟩ : syracuseStep 4231777 = 3173833) B3173833
theorem B4641419 : Blo 1484062 4641419 := bstep (se 1 (by rfl) ⟨3481064, by rfl⟩ : syracuseStep 4641419 = 6962129) B6962129
theorem B4289213 : Blo 1484062 4289213 := bstep (se 3 (by rfl) ⟨804227, by rfl⟩ : syracuseStep 4289213 = 1608455) B1608455
theorem B5010119 : Blo 1484062 5010119 := bstep (se 1 (by rfl) ⟨3757589, by rfl⟩ : syracuseStep 5010119 = 7515179) B7515179
theorem B19035101 : Blo 1484062 19035101 := bstep (se 3 (by rfl) ⟨3569081, by rfl⟩ : syracuseStep 19035101 = 7138163) B7138163
theorem B3757063 : Blo 1484062 3757063 := bstep (se 1 (by rfl) ⟨2817797, by rfl⟩ : syracuseStep 3757063 = 5635595) B5635595
theorem B13210895 : Blo 1484062 13210895 := bstep (se 1 (by rfl) ⟨9908171, by rfl⟩ : syracuseStep 13210895 = 19816343) B19816343
theorem B6346127 : Blo 1484062 6346127 := bstep (se 1 (by rfl) ⟨4759595, by rfl⟩ : syracuseStep 6346127 = 9519191) B9519191
theorem B5010983 : Blo 1484062 5010983 := bstep (se 1 (by rfl) ⟨3758237, by rfl⟩ : syracuseStep 5010983 = 7516475) B7516475
theorem B3339899 : Blo 1484062 3339899 := bstep (se 1 (by rfl) ⟨2504924, by rfl⟩ : syracuseStep 3339899 = 5009849) B5009849
theorem B3757691 : Blo 1484062 3757691 := bstep (se 1 (by rfl) ⟨2818268, by rfl⟩ : syracuseStep 3757691 = 5636537) B5636537
theorem B3569275 : Blo 1484062 3569275 := bstep (se 1 (by rfl) ⟨2676956, by rfl⟩ : syracuseStep 3569275 = 5353913) B5353913
theorem B5011091 : Blo 1484062 5011091 := bstep (se 1 (by rfl) ⟨3758318, by rfl⟩ : syracuseStep 5011091 = 7516637) B7516637
theorem B5641913 : Blo 1484062 5641913 := bstep (se 2 (by rfl) ⟨2115717, by rfl⟩ : syracuseStep 5641913 = 4231435) B4231435
theorem B3569351 : Blo 1484062 3569351 := bstep (se 1 (by rfl) ⟨2677013, by rfl⟩ : syracuseStep 3569351 = 5354027) B5354027
theorem B11269853 : Blo 1484062 11269853 := bstep (se 3 (by rfl) ⟨2113097, by rfl⟩ : syracuseStep 11269853 = 4226195) B4226195
theorem B3340025 : Blo 1484062 3340025 := bstep (se 2 (by rfl) ⟨1252509, by rfl⟩ : syracuseStep 3340025 = 2505019) B2505019
theorem B51410689 : Blo 1484062 51410689 := bstep (se 2 (by rfl) ⟨19279008, by rfl⟩ : syracuseStep 51410689 = 38558017) B38558017
theorem B10852163 : Blo 1484062 10852163 := bstep (se 1 (by rfl) ⟨8139122, by rfl⟩ : syracuseStep 10852163 = 16278245) B16278245
theorem B5011307 : Blo 1484062 5011307 := bstep (se 1 (by rfl) ⟨3758480, by rfl⟩ : syracuseStep 5011307 = 7516961) B7516961
theorem B3757985 : Blo 1484062 3757985 := bstep (se 2 (by rfl) ⟨1409244, by rfl⟩ : syracuseStep 3757985 = 2818489) B2818489
theorem B5011361 : Blo 1484062 5011361 := bstep (se 2 (by rfl) ⟨1879260, by rfl⟩ : syracuseStep 5011361 = 3758521) B3758521
theorem B2226095 : Blo 1484062 2226095 := bstep (se 1 (by rfl) ⟨1669571, by rfl⟩ : syracuseStep 2226095 = 3339143) B3339143
theorem B3340295 : Blo 1484062 3340295 := bstep (se 1 (by rfl) ⟨2505221, by rfl⟩ : syracuseStep 3340295 = 5010443) B5010443
theorem B2226185 : Blo 1484062 2226185 := bstep (se 2 (by rfl) ⟨834819, by rfl⟩ : syracuseStep 2226185 = 1669639) B1669639
theorem B2226215 : Blo 1484062 2226215 := bstep (se 1 (by rfl) ⟨1669661, by rfl⟩ : syracuseStep 2226215 = 3339323) B3339323
theorem B2504783 : Blo 1484062 2504783 := bstep (se 1 (by rfl) ⟨1878587, by rfl⟩ : syracuseStep 2504783 = 3757175) B3757175
theorem B3340367 : Blo 1484062 3340367 := bstep (se 1 (by rfl) ⟨2505275, by rfl⟩ : syracuseStep 3340367 = 5010551) B5010551
theorem B2226299 : Blo 1484062 2226299 := bstep (se 1 (by rfl) ⟨1669724, by rfl⟩ : syracuseStep 2226299 = 3339449) B3339449
theorem B2226425 : Blo 1484062 2226425 := bstep (se 2 (by rfl) ⟨834909, by rfl⟩ : syracuseStep 2226425 = 1669819) B1669819
theorem B2259193 : Blo 1484062 2259193 := bstep (se 2 (by rfl) ⟨847197, by rfl⟩ : syracuseStep 2259193 = 1694395) B1694395
theorem B6347069 : Blo 1484062 6347069 := bstep (se 3 (by rfl) ⟨1190075, by rfl⟩ : syracuseStep 6347069 = 2380151) B2380151
theorem B2226527 : Blo 1484062 2226527 := bstep (se 1 (by rfl) ⟨1669895, by rfl⟩ : syracuseStep 2226527 = 3339791) B3339791
theorem B2226539 : Blo 1484062 2226539 := bstep (se 1 (by rfl) ⟨1669904, by rfl⟩ : syracuseStep 2226539 = 3339809) B3339809
theorem B2857399 : Blo 1484062 2857399 := bstep (se 1 (by rfl) ⟨2143049, by rfl⟩ : syracuseStep 2857399 = 4286099) B4286099
theorem B3340763 : Blo 1484062 3340763 := bstep (se 1 (by rfl) ⟨2505572, by rfl⟩ : syracuseStep 3340763 = 5011145) B5011145
theorem B5011955 : Blo 1484062 5011955 := bstep (se 1 (by rfl) ⟨3758966, by rfl⟩ : syracuseStep 5011955 = 7517933) B7517933
theorem B6773273 : Blo 1484062 6773273 := bstep (se 2 (by rfl) ⟨2539977, by rfl⟩ : syracuseStep 6773273 = 5079955) B5079955
theorem B16308769 : Blo 1484062 16308769 := bstep (se 2 (by rfl) ⟨6115788, by rfl⟩ : syracuseStep 16308769 = 12231577) B12231577
theorem B1784359 : Blo 1484062 1784359 := bstep (se 1 (by rfl) ⟨1338269, by rfl⟩ : syracuseStep 1784359 = 2676539) B2676539
theorem B1669711 : Blo 1484062 1669711 := bstep (se 1 (by rfl) ⟨1252283, by rfl⟩ : syracuseStep 1669711 = 2504567) B2504567
theorem B2226767 : Blo 1484062 2226767 := bstep (se 1 (by rfl) ⟨1670075, by rfl⟩ : syracuseStep 2226767 = 3340151) B3340151
theorem B4012667 : Blo 1484062 4012667 := bstep (se 1 (by rfl) ⟨3009500, by rfl⟩ : syracuseStep 4012667 = 6019001) B6019001
theorem B8460935 : Blo 1484062 8460935 := bstep (se 1 (by rfl) ⟨6345701, by rfl⟩ : syracuseStep 8460935 = 12691403) B12691403
theorem B7518905 : Blo 1484062 7518905 := bstep (se 2 (by rfl) ⟨2819589, by rfl⟩ : syracuseStep 7518905 = 5639179) B5639179
theorem B2226887 : Blo 1484062 2226887 := bstep (se 1 (by rfl) ⟨1670165, by rfl⟩ : syracuseStep 2226887 = 3340331) B3340331
theorem B8452937 : Blo 1484062 8452937 := bstep (se 2 (by rfl) ⟨3169851, by rfl⟩ : syracuseStep 8452937 = 6339703) B6339703
theorem B2227049 : Blo 1484062 2227049 := bstep (se 2 (by rfl) ⟨835143, by rfl⟩ : syracuseStep 2227049 = 1670287) B1670287
theorem B16063379 : Blo 1484062 16063379 := bstep (se 1 (by rfl) ⟨12047534, by rfl⟩ : syracuseStep 16063379 = 24095069) B24095069
theorem B2505647 : Blo 1484062 2505647 := bstep (se 1 (by rfl) ⟨1879235, by rfl⟩ : syracuseStep 2505647 = 3758471) B3758471
theorem B3341231 : Blo 1484062 3341231 := bstep (se 1 (by rfl) ⟨2505923, by rfl⟩ : syracuseStep 3341231 = 5011847) B5011847
theorem B2227127 : Blo 1484062 2227127 := bstep (se 1 (by rfl) ⟨1670345, by rfl⟩ : syracuseStep 2227127 = 3340691) B3340691
theorem B1670107 : Blo 1484062 1670107 := bstep (se 1 (by rfl) ⟨1252580, by rfl⟩ : syracuseStep 1670107 = 2505161) B2505161
theorem B2227163 : Blo 1484062 2227163 := bstep (se 1 (by rfl) ⟨1670372, by rfl⟩ : syracuseStep 2227163 = 3340745) B3340745
theorem B9640961 : Blo 1484062 9640961 := bstep (se 2 (by rfl) ⟨3615360, by rfl⟩ : syracuseStep 9640961 = 7230721) B7230721
theorem B5635079 : Blo 1484062 5635079 := bstep (se 1 (by rfl) ⟨4226309, by rfl⟩ : syracuseStep 5635079 = 8452619) B8452619
theorem B5012495 : Blo 1484062 5012495 := bstep (se 1 (by rfl) ⟨3759371, by rfl⟩ : syracuseStep 5012495 = 7518743) B7518743
theorem B12688427 : Blo 1484062 12688427 := bstep (se 1 (by rfl) ⟨9516320, by rfl⟩ : syracuseStep 12688427 = 19032641) B19032641
theorem B4226219 : Blo 1484062 4226219 := bstep (se 1 (by rfl) ⟨3169664, by rfl⟩ : syracuseStep 4226219 = 6339329) B6339329
theorem B3341483 : Blo 1484062 3341483 := bstep (se 1 (by rfl) ⟨2506112, by rfl⟩ : syracuseStep 3341483 = 5012225) B5012225
theorem B2506079 : Blo 1484062 2506079 := bstep (se 1 (by rfl) ⟨1879559, by rfl⟩ : syracuseStep 2506079 = 3759119) B3759119
theorem B1670575 : Blo 1484062 1670575 := bstep (se 1 (by rfl) ⟨1252931, by rfl⟩ : syracuseStep 1670575 = 2505863) B2505863
theorem B2227631 : Blo 1484062 2227631 := bstep (se 1 (by rfl) ⟨1670723, by rfl⟩ : syracuseStep 2227631 = 3341447) B3341447
theorem B5635565 : Blo 1484062 5635565 := bstep (se 3 (by rfl) ⟨1056668, by rfl⟩ : syracuseStep 5635565 = 2113337) B2113337
theorem B10845683 : Blo 1484062 10845683 := bstep (se 1 (by rfl) ⟨8134262, by rfl⟩ : syracuseStep 10845683 = 16268525) B16268525
theorem B2227721 : Blo 1484062 2227721 := bstep (se 2 (by rfl) ⟨835395, by rfl⟩ : syracuseStep 2227721 = 1670791) B1670791
theorem B2227751 : Blo 1484062 2227751 := bstep (se 1 (by rfl) ⟨1670813, by rfl⟩ : syracuseStep 2227751 = 3341627) B3341627
theorem B3759655 : Blo 1484062 3759655 := bstep (se 1 (by rfl) ⟨2819741, by rfl⟩ : syracuseStep 3759655 = 5639483) B5639483
theorem B5013089 : Blo 1484062 5013089 := bstep (se 2 (by rfl) ⟨1879908, by rfl⟩ : syracuseStep 5013089 = 3759817) B3759817
theorem B2227835 : Blo 1484062 2227835 := bstep (se 1 (by rfl) ⟨1670876, by rfl⟩ : syracuseStep 2227835 = 3341753) B3341753
theorem B4759175 : Blo 1484062 4759175 := bstep (se 1 (by rfl) ⟨3569381, by rfl⟩ : syracuseStep 4759175 = 7138763) B7138763
theorem B3342023 : Blo 1484062 3342023 := bstep (se 1 (by rfl) ⟨2506517, by rfl⟩ : syracuseStep 3342023 = 5013035) B5013035
theorem B2227961 : Blo 1484062 2227961 := bstep (se 2 (by rfl) ⟨835485, by rfl⟩ : syracuseStep 2227961 = 1670971) B1670971
theorem B4759289 : Blo 1484062 4759289 := bstep (se 2 (by rfl) ⟨1784733, by rfl⟩ : syracuseStep 4759289 = 3569467) B3569467
theorem B1671007 : Blo 1484062 1671007 := bstep (se 1 (by rfl) ⟨1253255, by rfl⟩ : syracuseStep 1671007 = 2506511) B2506511
theorem B2228063 : Blo 1484062 2228063 := bstep (se 1 (by rfl) ⟨1671047, by rfl⟩ : syracuseStep 2228063 = 3342095) B3342095
theorem B4759391 : Blo 1484062 4759391 := bstep (se 1 (by rfl) ⟨3569543, by rfl⟩ : syracuseStep 4759391 = 7139087) B7139087
theorem B2228075 : Blo 1484062 2228075 := bstep (se 1 (by rfl) ⟨1671056, by rfl⟩ : syracuseStep 2228075 = 3342113) B3342113
theorem B3759979 : Blo 1484062 3759979 := bstep (se 1 (by rfl) ⟨2819984, by rfl⟩ : syracuseStep 3759979 = 5639969) B5639969
theorem B2506639 : Blo 1484062 2506639 := bstep (se 1 (by rfl) ⟨1879979, by rfl⟩ : syracuseStep 2506639 = 3759959) B3759959
theorem B2507017 : Blo 1484062 2507017 := bstep (se 2 (by rfl) ⟨940131, by rfl⟩ : syracuseStep 2507017 = 1880263) B1880263
theorem B2228489 : Blo 1484062 2228489 := bstep (se 2 (by rfl) ⟨835683, by rfl⟩ : syracuseStep 2228489 = 1671367) B1671367
theorem B2228591 : Blo 1484062 2228591 := bstep (se 1 (by rfl) ⟨1671443, by rfl⟩ : syracuseStep 2228591 = 3342887) B3342887
theorem B1671547 : Blo 1484062 1671547 := bstep (se 1 (by rfl) ⟨1253660, by rfl⟩ : syracuseStep 1671547 = 2507321) B2507321
theorem B86794649 : Blo 1484062 86794649 := bstep (se 2 (by rfl) ⟨32547993, by rfl⟩ : syracuseStep 86794649 = 65095987) B65095987
theorem B7520687 : Blo 1484062 7520687 := bstep (se 1 (by rfl) ⟨5640515, by rfl⟩ : syracuseStep 7520687 = 11281031) B11281031
theorem B2859475 : Blo 1484062 2859475 := bstep (se 1 (by rfl) ⟨2144606, by rfl⟩ : syracuseStep 2859475 = 4289213) B4289213
theorem B2228807 : Blo 1484062 2228807 := bstep (se 1 (by rfl) ⟨1671605, by rfl⟩ : syracuseStep 2228807 = 3343211) B3343211
theorem B2818633 : Blo 1484062 2818633 := bstep (se 2 (by rfl) ⟨1056987, by rfl⟩ : syracuseStep 2818633 = 2113975) B2113975
theorem B2228843 : Blo 1484062 2228843 := bstep (se 1 (by rfl) ⟨1671632, by rfl⟩ : syracuseStep 2228843 = 3343265) B3343265
theorem B12690067 : Blo 1484062 12690067 := bstep (se 1 (by rfl) ⟨9517550, by rfl⟩ : syracuseStep 12690067 = 19035101) B19035101
theorem B7135897 : Blo 1484062 7135897 := bstep (se 2 (by rfl) ⟨2675961, by rfl⟩ : syracuseStep 7135897 = 5351923) B5351923
theorem B5014169 : Blo 1484062 5014169 := bstep (se 2 (by rfl) ⟨1880313, by rfl⟩ : syracuseStep 5014169 = 3760627) B3760627
theorem B3343031 : Blo 1484062 3343031 := bstep (se 1 (by rfl) ⟨2507273, by rfl⟩ : syracuseStep 3343031 = 5014547) B5014547
theorem B2229071 : Blo 1484062 2229071 := bstep (se 1 (by rfl) ⟨1671803, by rfl⟩ : syracuseStep 2229071 = 3343607) B3343607
theorem B8807263 : Blo 1484062 8807263 := bstep (se 1 (by rfl) ⟨6605447, by rfl⟩ : syracuseStep 8807263 = 13210895) B13210895
theorem B3343247 : Blo 1484062 3343247 := bstep (se 1 (by rfl) ⟨2507435, by rfl⟩ : syracuseStep 3343247 = 5014871) B5014871
theorem B5080009 : Blo 1484062 5080009 := bstep (se 2 (by rfl) ⟨1905003, by rfl⟩ : syracuseStep 5080009 = 3810007) B3810007
theorem B12682277 : Blo 1484062 12682277 := bstep (se 4 (by rfl) ⟨1188963, by rfl⟩ : syracuseStep 12682277 = 2377927) B2377927
theorem B3761275 : Blo 1484062 3761275 := bstep (se 1 (by rfl) ⟨2820956, by rfl⟩ : syracuseStep 3761275 = 5641913) B5641913
theorem B7513235 : Blo 1484062 7513235 := bstep (se 1 (by rfl) ⟨5634926, by rfl⟩ : syracuseStep 7513235 = 11269853) B11269853
theorem B7234775 : Blo 1484062 7234775 := bstep (se 1 (by rfl) ⟨5426081, by rfl⟩ : syracuseStep 7234775 = 10852163) B10852163
theorem B1484063 : Blo 1484062 1484063 := bstep (se 1 (by rfl) ⟨1113047, by rfl⟩ : syracuseStep 1484063 = 2226095) B2226095
theorem B1484123 : Blo 1484062 1484123 := bstep (se 1 (by rfl) ⟨1113092, by rfl⟩ : syracuseStep 1484123 = 2226185) B2226185
theorem B1484143 : Blo 1484062 1484143 := bstep (se 1 (by rfl) ⟨1113107, by rfl⟩ : syracuseStep 1484143 = 2226215) B2226215
theorem B7521659 : Blo 1484062 7521659 := bstep (se 1 (by rfl) ⟨5641244, by rfl⟩ : syracuseStep 7521659 = 11282489) B11282489
theorem B4015499 : Blo 1484062 4015499 := bstep (se 1 (by rfl) ⟨3011624, by rfl⟩ : syracuseStep 4015499 = 6023249) B6023249
theorem B1484199 : Blo 1484062 1484199 := bstep (se 1 (by rfl) ⟨1113149, by rfl⟩ : syracuseStep 1484199 = 2226299) B2226299
theorem B1484283 : Blo 1484062 1484283 := bstep (se 1 (by rfl) ⟨1113212, by rfl⟩ : syracuseStep 1484283 = 2226425) B2226425
theorem B1484351 : Blo 1484062 1484351 := bstep (se 1 (by rfl) ⟨1113263, by rfl⟩ : syracuseStep 1484351 = 2226527) B2226527
theorem B1484359 : Blo 1484062 1484359 := bstep (se 1 (by rfl) ⟨1113269, by rfl⟩ : syracuseStep 1484359 = 2226539) B2226539
theorem B4515515 : Blo 1484062 4515515 := bstep (se 1 (by rfl) ⟨3386636, by rfl⟩ : syracuseStep 4515515 = 6773273) B6773273
theorem B1484511 : Blo 1484062 1484511 := bstep (se 1 (by rfl) ⟨1113383, by rfl⟩ : syracuseStep 1484511 = 2226767) B2226767
theorem B1484591 : Blo 1484062 1484591 := bstep (se 1 (by rfl) ⟨1113443, by rfl⟩ : syracuseStep 1484591 = 2226887) B2226887
theorem B4228919 : Blo 1484062 4228919 := bstep (se 1 (by rfl) ⟨3171689, by rfl⟩ : syracuseStep 4228919 = 6343379) B6343379
theorem B1484699 : Blo 1484062 1484699 := bstep (se 1 (by rfl) ⟨1113524, by rfl⟩ : syracuseStep 1484699 = 2227049) B2227049
theorem B10708919 : Blo 1484062 10708919 := bstep (se 1 (by rfl) ⟨8031689, by rfl⟩ : syracuseStep 10708919 = 16063379) B16063379
theorem B1484751 : Blo 1484062 1484751 := bstep (se 1 (by rfl) ⟨1113563, by rfl⟩ : syracuseStep 1484751 = 2227127) B2227127
theorem B1484775 : Blo 1484062 1484775 := bstep (se 1 (by rfl) ⟨1113581, by rfl⟩ : syracuseStep 1484775 = 2227163) B2227163
theorem B13551731 : Blo 1484062 13551731 := bstep (se 1 (by rfl) ⟨10163798, by rfl⟩ : syracuseStep 13551731 = 20327597) B20327597
theorem B1485087 : Blo 1484062 1485087 := bstep (se 1 (by rfl) ⟨1113815, by rfl⟩ : syracuseStep 1485087 = 2227631) B2227631
theorem B15239461 : Blo 1484062 15239461 := bstep (se 4 (by rfl) ⟨1428699, by rfl⟩ : syracuseStep 15239461 = 2857399) B2857399
theorem B1485147 : Blo 1484062 1485147 := bstep (se 1 (by rfl) ⟨1113860, by rfl⟩ : syracuseStep 1485147 = 2227721) B2227721
theorem B5638511 : Blo 1484062 5638511 := bstep (se 1 (by rfl) ⟨4228883, by rfl⟩ : syracuseStep 5638511 = 8457767) B8457767
theorem B1485167 : Blo 1484062 1485167 := bstep (se 1 (by rfl) ⟨1113875, by rfl⟩ : syracuseStep 1485167 = 2227751) B2227751
theorem B1485223 : Blo 1484062 1485223 := bstep (se 1 (by rfl) ⟨1113917, by rfl⟩ : syracuseStep 1485223 = 2227835) B2227835
theorem B3172783 : Blo 1484062 3172783 := bstep (se 1 (by rfl) ⟨2379587, by rfl⟩ : syracuseStep 3172783 = 4759175) B4759175
theorem B2820577 : Blo 1484062 2820577 := bstep (se 2 (by rfl) ⟨1057716, by rfl⟩ : syracuseStep 2820577 = 2115433) B2115433
theorem B1485307 : Blo 1484062 1485307 := bstep (se 1 (by rfl) ⟨1113980, by rfl⟩ : syracuseStep 1485307 = 2227961) B2227961
theorem B3172859 : Blo 1484062 3172859 := bstep (se 1 (by rfl) ⟨2379644, by rfl⟩ : syracuseStep 3172859 = 4759289) B4759289
theorem B1485375 : Blo 1484062 1485375 := bstep (se 1 (by rfl) ⟨1114031, by rfl⟩ : syracuseStep 1485375 = 2228063) B2228063
theorem B3172927 : Blo 1484062 3172927 := bstep (se 1 (by rfl) ⟨2379695, by rfl⟩ : syracuseStep 3172927 = 4759391) B4759391
theorem B1485383 : Blo 1484062 1485383 := bstep (se 1 (by rfl) ⟨1114037, by rfl⟩ : syracuseStep 1485383 = 2228075) B2228075
theorem B4016711 : Blo 1484062 4016711 := bstep (se 1 (by rfl) ⟨3012533, by rfl⟩ : syracuseStep 4016711 = 6025067) B6025067
theorem B7522955 : Blo 1484062 7522955 := bstep (se 1 (by rfl) ⟨5642216, by rfl⟩ : syracuseStep 7522955 = 11284433) B11284433
theorem B1485535 : Blo 1484062 1485535 := bstep (se 1 (by rfl) ⟨1114151, by rfl⟩ : syracuseStep 1485535 = 2228303) B2228303
theorem B1485615 : Blo 1484062 1485615 := bstep (se 1 (by rfl) ⟨1114211, by rfl⟩ : syracuseStep 1485615 = 2228423) B2228423
theorem B1485723 : Blo 1484062 1485723 := bstep (se 1 (by rfl) ⟨1114292, by rfl⟩ : syracuseStep 1485723 = 2228585) B2228585
theorem B11430827 : Blo 1484062 11430827 := bstep (se 1 (by rfl) ⟨8573120, by rfl⟩ : syracuseStep 11430827 = 17146241) B17146241
theorem B1485775 : Blo 1484062 1485775 := bstep (se 1 (by rfl) ⟨1114331, by rfl⟩ : syracuseStep 1485775 = 2228663) B2228663
theorem B1485799 : Blo 1484062 1485799 := bstep (se 1 (by rfl) ⟨1114349, by rfl⟩ : syracuseStep 1485799 = 2228699) B2228699
theorem B6343667 : Blo 1484062 6343667 := bstep (se 1 (by rfl) ⟨4757750, by rfl⟩ : syracuseStep 6343667 = 9515501) B9515501
theorem B24087617 : Blo 1484062 24087617 := bstep (se 2 (by rfl) ⟨9032856, by rfl⟩ : syracuseStep 24087617 = 18065713) B18065713
theorem B3664993 : Blo 1484062 3664993 := bstep (se 2 (by rfl) ⟨1374372, by rfl⟩ : syracuseStep 3664993 = 2748745) B2748745
theorem B3173671 : Blo 1484062 3173671 := bstep (se 1 (by rfl) ⟨2380253, by rfl⟩ : syracuseStep 3173671 = 4760507) B4760507
theorem B14265719 : Blo 1484062 14265719 := bstep (se 1 (by rfl) ⟨10699289, by rfl⟩ : syracuseStep 14265719 = 21398579) B21398579
theorem B21745025 : Blo 1484062 21745025 := bstep (se 2 (by rfl) ⟨8154384, by rfl⟩ : syracuseStep 21745025 = 16308769) B16308769
theorem B2379145 : Blo 1484062 2379145 := bstep (se 2 (by rfl) ⟨892179, by rfl⟩ : syracuseStep 2379145 = 1784359) B1784359
theorem B1879463 : Blo 1484062 1879463 := bstep (se 1 (by rfl) ⟨1409597, by rfl⟩ : syracuseStep 1879463 = 2819195) B2819195
theorem B1879615 : Blo 1484062 1879615 := bstep (se 1 (by rfl) ⟨1409711, by rfl⟩ : syracuseStep 1879615 = 2819423) B2819423
theorem B3567199 : Blo 1484062 3567199 := bstep (se 1 (by rfl) ⟨2675399, by rfl⟩ : syracuseStep 3567199 = 5350799) B5350799
theorem B1879787 : Blo 1484062 1879787 := bstep (se 1 (by rfl) ⟨1409840, by rfl⟩ : syracuseStep 1879787 = 2819681) B2819681
theorem B5009309 : Blo 1484062 5009309 := bstep (se 3 (by rfl) ⟨939245, by rfl⟩ : syracuseStep 5009309 = 1878491) B1878491
theorem B1585127 : Blo 1484062 1585127 := bstep (se 1 (by rfl) ⟨1188845, by rfl⟩ : syracuseStep 1585127 = 2377691) B2377691
theorem B274190341 : Blo 1484062 274190341 := bstep (se 4 (by rfl) ⟨25705344, by rfl⟩ : syracuseStep 274190341 = 51410689) B51410689
theorem B5009417 : Blo 1484062 5009417 := bstep (se 2 (by rfl) ⟨1878531, by rfl⟩ : syracuseStep 5009417 = 3757063) B3757063
theorem B7516313 : Blo 1484062 7516313 := bstep (se 2 (by rfl) ⟨2818617, by rfl⟩ : syracuseStep 7516313 = 5637235) B5637235
theorem B4231379 : Blo 1484062 4231379 := bstep (se 1 (by rfl) ⟨3173534, by rfl⟩ : syracuseStep 4231379 = 6347069) B6347069
theorem B2675111 : Blo 1484062 2675111 := bstep (se 1 (by rfl) ⟨2006333, by rfl⟩ : syracuseStep 2675111 = 4012667) B4012667
theorem B5640623 : Blo 1484062 5640623 := bstep (se 1 (by rfl) ⟨4230467, by rfl⟩ : syracuseStep 5640623 = 8460935) B8460935
theorem B6427307 : Blo 1484062 6427307 := bstep (se 1 (by rfl) ⟨4820480, by rfl⟩ : syracuseStep 6427307 = 9640961) B9640961
theorem B3756719 : Blo 1484062 3756719 := bstep (se 1 (by rfl) ⟨2817539, by rfl⟩ : syracuseStep 3756719 = 5635079) B5635079
theorem B1880759 : Blo 1484062 1880759 := bstep (se 1 (by rfl) ⟨1410569, by rfl⟩ : syracuseStep 1880759 = 2821139) B2821139
theorem B8458951 : Blo 1484062 8458951 := bstep (se 1 (by rfl) ⟨6344213, by rfl⟩ : syracuseStep 8458951 = 12688427) B12688427
theorem B7132013 : Blo 1484062 7132013 := bstep (se 3 (by rfl) ⟨1337252, by rfl⟩ : syracuseStep 7132013 = 2674505) B2674505
theorem B3339179 : Blo 1484062 3339179 := bstep (se 1 (by rfl) ⟨2504384, by rfl⟩ : syracuseStep 3339179 = 5008769) B5008769
theorem B7517123 : Blo 1484062 7517123 := bstep (se 1 (by rfl) ⟨5637842, by rfl⟩ : syracuseStep 7517123 = 11275685) B11275685
theorem B3757043 : Blo 1484062 3757043 := bstep (se 1 (by rfl) ⟨2817782, by rfl⟩ : syracuseStep 3757043 = 5635565) B5635565
theorem B7230455 : Blo 1484062 7230455 := bstep (se 1 (by rfl) ⟨5422841, by rfl⟩ : syracuseStep 7230455 = 10845683) B10845683
theorem B12039425 : Blo 1484062 12039425 := bstep (se 2 (by rfl) ⟨4514784, by rfl⟩ : syracuseStep 12039425 = 9029569) B9029569
theorem B5641595 : Blo 1484062 5641595 := bstep (se 1 (by rfl) ⟨4231196, by rfl⟩ : syracuseStep 5641595 = 8462393) B8462393
theorem B3757499 : Blo 1484062 3757499 := bstep (se 1 (by rfl) ⟨2818124, by rfl⟩ : syracuseStep 3757499 = 5636249) B5636249
theorem B3339719 : Blo 1484062 3339719 := bstep (se 1 (by rfl) ⟨2504789, by rfl⟩ : syracuseStep 3339719 = 5009579) B5009579
theorem B3569159 : Blo 1484062 3569159 := bstep (se 1 (by rfl) ⟨2676869, by rfl⟩ : syracuseStep 3569159 = 5353739) B5353739
theorem B3216979 : Blo 1484062 3216979 := bstep (se 1 (by rfl) ⟨2412734, by rfl⟩ : syracuseStep 3216979 = 4825469) B4825469
theorem B3012191 : Blo 1484062 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B3012257 : Blo 1484062 3012257 := bstep (se 2 (by rfl) ⟨1129596, by rfl⟩ : syracuseStep 3012257 = 2259193) B2259193
theorem B3340079 : Blo 1484062 3340079 := bstep (se 1 (by rfl) ⟨2505059, by rfl⟩ : syracuseStep 3340079 = 5010119) B5010119
theorem B72267673 : Blo 1484062 72267673 := bstep (se 2 (by rfl) ⟨27100377, by rfl⟩ : syracuseStep 72267673 = 54200755) B54200755
theorem B2226281 : Blo 1484062 2226281 := bstep (se 2 (by rfl) ⟨834855, by rfl⟩ : syracuseStep 2226281 = 1669711) B1669711
theorem B5642369 : Blo 1484062 5642369 := bstep (se 2 (by rfl) ⟨2115888, by rfl⟩ : syracuseStep 5642369 = 4231777) B4231777
theorem B10705229 : Blo 1484062 10705229 := bstep (se 3 (by rfl) ⟨2007230, by rfl⟩ : syracuseStep 10705229 = 4014461) B4014461
theorem B3340655 : Blo 1484062 3340655 := bstep (se 1 (by rfl) ⟨2505491, by rfl⟩ : syracuseStep 3340655 = 5010983) B5010983
theorem B6347119 : Blo 1484062 6347119 := bstep (se 1 (by rfl) ⟨4760339, by rfl⟩ : syracuseStep 6347119 = 9520679) B9520679
theorem B16923005 : Blo 1484062 16923005 := bstep (se 3 (by rfl) ⟨3173063, by rfl⟩ : syracuseStep 16923005 = 6346127) B6346127
theorem B2226599 : Blo 1484062 2226599 := bstep (se 1 (by rfl) ⟨1669949, by rfl⟩ : syracuseStep 2226599 = 3339899) B3339899
theorem B2505127 : Blo 1484062 2505127 := bstep (se 1 (by rfl) ⟨1878845, by rfl⟩ : syracuseStep 2505127 = 3757691) B3757691
theorem B3340727 : Blo 1484062 3340727 := bstep (se 1 (by rfl) ⟨2505545, by rfl⟩ : syracuseStep 3340727 = 5011091) B5011091
theorem B2226683 : Blo 1484062 2226683 := bstep (se 1 (by rfl) ⟨1670012, by rfl⟩ : syracuseStep 2226683 = 3340025) B3340025
theorem B3340871 : Blo 1484062 3340871 := bstep (se 1 (by rfl) ⟨2505653, by rfl⟩ : syracuseStep 3340871 = 5011307) B5011307
theorem B3758663 : Blo 1484062 3758663 := bstep (se 1 (by rfl) ⟨2818997, by rfl⟩ : syracuseStep 3758663 = 5637995) B5637995
theorem B2505289 : Blo 1484062 2505289 := bstep (se 2 (by rfl) ⟨939483, by rfl⟩ : syracuseStep 2505289 = 1878967) B1878967
theorem B2505323 : Blo 1484062 2505323 := bstep (se 1 (by rfl) ⟨1878992, by rfl⟩ : syracuseStep 2505323 = 3757985) B3757985
theorem B3340907 : Blo 1484062 3340907 := bstep (se 1 (by rfl) ⟨2505680, by rfl⟩ : syracuseStep 3340907 = 5011361) B5011361
theorem B2226809 : Blo 1484062 2226809 := bstep (se 2 (by rfl) ⟨835053, by rfl⟩ : syracuseStep 2226809 = 1670107) B1670107
theorem B2226863 : Blo 1484062 2226863 := bstep (se 1 (by rfl) ⟨1670147, by rfl⟩ : syracuseStep 2226863 = 3340295) B3340295
theorem B9034415 : Blo 1484062 9034415 := bstep (se 1 (by rfl) ⟨6775811, by rfl⟩ : syracuseStep 9034415 = 13551623) B13551623
theorem B1669855 : Blo 1484062 1669855 := bstep (se 1 (by rfl) ⟨1252391, by rfl⟩ : syracuseStep 1669855 = 2504783) B2504783
theorem B2226911 : Blo 1484062 2226911 := bstep (se 1 (by rfl) ⟨1670183, by rfl⟩ : syracuseStep 2226911 = 3340367) B3340367
theorem B19553005 : Blo 1484062 19553005 := bstep (se 3 (by rfl) ⟨3666188, by rfl⟩ : syracuseStep 19553005 = 7332377) B7332377
theorem B10722235 : Blo 1484062 10722235 := bstep (se 1 (by rfl) ⟨8041676, by rfl⟩ : syracuseStep 10722235 = 16083353) B16083353
theorem B2227175 : Blo 1484062 2227175 := bstep (se 1 (by rfl) ⟨1670381, by rfl⟩ : syracuseStep 2227175 = 3340763) B3340763
theorem B3341303 : Blo 1484062 3341303 := bstep (se 1 (by rfl) ⟨2505977, by rfl⟩ : syracuseStep 3341303 = 5011955) B5011955
theorem B12377117 : Blo 1484062 12377117 := bstep (se 3 (by rfl) ⟨2320709, by rfl⟩ : syracuseStep 12377117 = 4641419) B4641419
theorem B6020219 : Blo 1484062 6020219 := bstep (se 1 (by rfl) ⟨4515164, by rfl⟩ : syracuseStep 6020219 = 9030329) B9030329
theorem B5012603 : Blo 1484062 5012603 := bstep (se 1 (by rfl) ⟨3759452, by rfl⟩ : syracuseStep 5012603 = 7518905) B7518905
theorem B9518269 : Blo 1484062 9518269 := bstep (se 3 (by rfl) ⟨1784675, by rfl⟩ : syracuseStep 9518269 = 3569351) B3569351
theorem B5635291 : Blo 1484062 5635291 := bstep (se 1 (by rfl) ⟨4226468, by rfl⟩ : syracuseStep 5635291 = 8452937) B8452937
theorem B2227433 : Blo 1484062 2227433 := bstep (se 2 (by rfl) ⟨835287, by rfl⟩ : syracuseStep 2227433 = 1670575) B1670575
theorem B1670431 : Blo 1484062 1670431 := bstep (se 1 (by rfl) ⟨1252823, by rfl⟩ : syracuseStep 1670431 = 2505647) B2505647
theorem B2227487 : Blo 1484062 2227487 := bstep (se 1 (by rfl) ⟨1670615, by rfl⟩ : syracuseStep 2227487 = 3341231) B3341231
theorem B3341663 : Blo 1484062 3341663 := bstep (se 1 (by rfl) ⟨2506247, by rfl⟩ : syracuseStep 3341663 = 5012495) B5012495
theorem B6339977 : Blo 1484062 6339977 := bstep (se 2 (by rfl) ⟨2377491, by rfl⟩ : syracuseStep 6339977 = 4754983) B4754983
theorem B5012873 : Blo 1484062 5012873 := bstep (se 2 (by rfl) ⟨1879827, by rfl⟩ : syracuseStep 5012873 = 3759655) B3759655
theorem B2817479 : Blo 1484062 2817479 := bstep (se 1 (by rfl) ⟨2113109, by rfl⟩ : syracuseStep 2817479 = 4226219) B4226219
theorem B2227655 : Blo 1484062 2227655 := bstep (se 1 (by rfl) ⟨1670741, by rfl⟩ : syracuseStep 2227655 = 3341483) B3341483
theorem B4759033 : Blo 1484062 4759033 := bstep (se 2 (by rfl) ⟨1784637, by rfl⟩ : syracuseStep 4759033 = 3569275) B3569275
theorem B1670719 : Blo 1484062 1670719 := bstep (se 1 (by rfl) ⟨1253039, by rfl⟩ : syracuseStep 1670719 = 2506079) B2506079
theorem B9641587 : Blo 1484062 9641587 := bstep (se 1 (by rfl) ⟨7231190, by rfl⟩ : syracuseStep 9641587 = 14462381) B14462381
theorem B9027233 : Blo 1484062 9027233 := bstep (se 2 (by rfl) ⟨3385212, by rfl⟩ : syracuseStep 9027233 = 6770425) B6770425
theorem B3342059 : Blo 1484062 3342059 := bstep (se 1 (by rfl) ⟨2506544, by rfl⟩ : syracuseStep 3342059 = 5013089) B5013089
theorem B3432233 : Blo 1484062 3432233 := bstep (se 2 (by rfl) ⟨1287087, by rfl⟩ : syracuseStep 3432233 = 2574175) B2574175
theorem B2228009 : Blo 1484062 2228009 := bstep (se 2 (by rfl) ⟨835503, by rfl⟩ : syracuseStep 2228009 = 1671007) B1671007
theorem B2228015 : Blo 1484062 2228015 := bstep (se 1 (by rfl) ⟨1671011, by rfl⟩ : syracuseStep 2228015 = 3342023) B3342023
theorem B3759929 : Blo 1484062 3759929 := bstep (se 2 (by rfl) ⟨1409973, by rfl⟩ : syracuseStep 3759929 = 2819947) B2819947
theorem B5013305 : Blo 1484062 5013305 := bstep (se 2 (by rfl) ⟨1879989, by rfl⟩ : syracuseStep 5013305 = 3759979) B3759979
theorem B8462141 : Blo 1484062 8462141 := bstep (se 3 (by rfl) ⟨1586651, by rfl⟩ : syracuseStep 8462141 = 3173303) B3173303
theorem B3342185 : Blo 1484062 3342185 := bstep (se 2 (by rfl) ⟨1253319, by rfl⟩ : syracuseStep 3342185 = 2506639) B2506639
theorem B5013791 : Blo 1484062 5013791 := bstep (se 1 (by rfl) ⟨3760343, by rfl⟩ : syracuseStep 5013791 = 7520687) B7520687
theorem B3760415 : Blo 1484062 3760415 := bstep (se 1 (by rfl) ⟨2820311, by rfl⟩ : syracuseStep 3760415 = 5640623) B5640623
theorem B3342689 : Blo 1484062 3342689 := bstep (se 2 (by rfl) ⟨1253508, by rfl⟩ : syracuseStep 3342689 = 2507017) B2507017
theorem B3342779 : Blo 1484062 3342779 := bstep (se 1 (by rfl) ⟨2507084, by rfl⟩ : syracuseStep 3342779 = 5014169) B5014169
theorem B2228687 : Blo 1484062 2228687 := bstep (se 1 (by rfl) ⟨1671515, by rfl⟩ : syracuseStep 2228687 = 3343031) B3343031
theorem B8462825 : Blo 1484062 8462825 := bstep (se 2 (by rfl) ⟨3173559, by rfl⟩ : syracuseStep 8462825 = 6347119) B6347119
theorem B2228729 : Blo 1484062 2228729 := bstep (se 2 (by rfl) ⟨835773, by rfl⟩ : syracuseStep 2228729 = 1671547) B1671547
theorem B2228831 : Blo 1484062 2228831 := bstep (se 1 (by rfl) ⟨1671623, by rfl⟩ : syracuseStep 2228831 = 3343247) B3343247
theorem B3760769 : Blo 1484062 3760769 := bstep (se 2 (by rfl) ⟨1410288, by rfl⟩ : syracuseStep 3760769 = 2820577) B2820577
theorem B8454851 : Blo 1484062 8454851 := bstep (se 1 (by rfl) ⟨6341138, by rfl⟩ : syracuseStep 8454851 = 12682277) B12682277
theorem B5014439 : Blo 1484062 5014439 := bstep (se 1 (by rfl) ⟨3760829, by rfl⟩ : syracuseStep 5014439 = 7521659) B7521659
theorem B3761063 : Blo 1484062 3761063 := bstep (se 1 (by rfl) ⟨2820797, by rfl⟩ : syracuseStep 3761063 = 5641595) B5641595
theorem B32130037 : Blo 1484062 32130037 := bstep (se 5 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 32130037 = 3012191) B3012191
theorem B10707997 : Blo 1484062 10707997 := bstep (se 3 (by rfl) ⟨2007749, by rfl⟩ : syracuseStep 10707997 = 4015499) B4015499
theorem B2008171 : Blo 1484062 2008171 := bstep (se 1 (by rfl) ⟨1506128, by rfl⟩ : syracuseStep 2008171 = 3012257) B3012257
theorem B2819279 : Blo 1484062 2819279 := bstep (se 1 (by rfl) ⟨2114459, by rfl⟩ : syracuseStep 2819279 = 4228919) B4228919
theorem B14296313 : Blo 1484062 14296313 := bstep (se 2 (by rfl) ⟨5361117, by rfl⟩ : syracuseStep 14296313 = 10722235) B10722235
theorem B1484187 : Blo 1484062 1484187 := bstep (se 1 (by rfl) ⟨1113140, by rfl⟩ : syracuseStep 1484187 = 2226281) B2226281
theorem B3761579 : Blo 1484062 3761579 := bstep (se 1 (by rfl) ⟨2821184, by rfl⟩ : syracuseStep 3761579 = 5642369) B5642369
theorem B5015033 : Blo 1484062 5015033 := bstep (se 2 (by rfl) ⟨1880637, by rfl⟩ : syracuseStep 5015033 = 3761275) B3761275
theorem B7136819 : Blo 1484062 7136819 := bstep (se 1 (by rfl) ⟨5352614, by rfl⟩ : syracuseStep 7136819 = 10705229) B10705229
theorem B12691025 : Blo 1484062 12691025 := bstep (se 2 (by rfl) ⟨4759134, by rfl⟩ : syracuseStep 12691025 = 9518269) B9518269
theorem B11282003 : Blo 1484062 11282003 := bstep (se 1 (by rfl) ⟨8461502, by rfl⟩ : syracuseStep 11282003 = 16923005) B16923005
theorem B1484399 : Blo 1484062 1484399 := bstep (se 1 (by rfl) ⟨1113299, by rfl⟩ : syracuseStep 1484399 = 2226599) B2226599
theorem B7513721 : Blo 1484062 7513721 := bstep (se 2 (by rfl) ⟨2817645, by rfl⟩ : syracuseStep 7513721 = 5635291) B5635291
theorem B1484455 : Blo 1484062 1484455 := bstep (se 1 (by rfl) ⟨1113341, by rfl⟩ : syracuseStep 1484455 = 2226683) B2226683
theorem B2115239 : Blo 1484062 2115239 := bstep (se 1 (by rfl) ⟨1586429, by rfl⟩ : syracuseStep 2115239 = 3172859) B3172859
theorem B1484539 : Blo 1484062 1484539 := bstep (se 1 (by rfl) ⟨1113404, by rfl⟩ : syracuseStep 1484539 = 2226809) B2226809
theorem B5015303 : Blo 1484062 5015303 := bstep (se 1 (by rfl) ⟨3761477, by rfl⟩ : syracuseStep 5015303 = 7522955) B7522955
theorem B17139485 : Blo 1484062 17139485 := bstep (se 3 (by rfl) ⟨3213653, by rfl⟩ : syracuseStep 17139485 = 6427307) B6427307
theorem B1484575 : Blo 1484062 1484575 := bstep (se 1 (by rfl) ⟨1113431, by rfl⟩ : syracuseStep 1484575 = 2226863) B2226863
theorem B6022943 : Blo 1484062 6022943 := bstep (se 1 (by rfl) ⟨4517207, by rfl⟩ : syracuseStep 6022943 = 9034415) B9034415
theorem B5015357 : Blo 1484062 5015357 := bstep (se 3 (by rfl) ⟨940379, by rfl⟩ : syracuseStep 5015357 = 1880759) B1880759
theorem B1484607 : Blo 1484062 1484607 := bstep (se 1 (by rfl) ⟨1113455, by rfl⟩ : syracuseStep 1484607 = 2226911) B2226911
theorem B3172193 : Blo 1484062 3172193 := bstep (se 2 (by rfl) ⟨1189572, by rfl⟩ : syracuseStep 3172193 = 2379145) B2379145
theorem B7620551 : Blo 1484062 7620551 := bstep (se 1 (by rfl) ⟨5715413, by rfl⟩ : syracuseStep 7620551 = 11430827) B11430827
theorem B1484783 : Blo 1484062 1484783 := bstep (se 1 (by rfl) ⟨1113587, by rfl⟩ : syracuseStep 1484783 = 2227175) B2227175
theorem B4229111 : Blo 1484062 4229111 := bstep (se 1 (by rfl) ⟨3171833, by rfl⟩ : syracuseStep 4229111 = 6343667) B6343667
theorem B8251411 : Blo 1484062 8251411 := bstep (se 1 (by rfl) ⟨6188558, by rfl⟩ : syracuseStep 8251411 = 12377117) B12377117
theorem B16058411 : Blo 1484062 16058411 := bstep (se 1 (by rfl) ⟨12043808, by rfl⟩ : syracuseStep 16058411 = 24087617) B24087617
theorem B12855449 : Blo 1484062 12855449 := bstep (se 2 (by rfl) ⟨4820793, by rfl⟩ : syracuseStep 12855449 = 9641587) B9641587
theorem B1484955 : Blo 1484062 1484955 := bstep (se 1 (by rfl) ⟨1113716, by rfl⟩ : syracuseStep 1484955 = 2227433) B2227433
theorem B1484991 : Blo 1484062 1484991 := bstep (se 1 (by rfl) ⟨1113743, by rfl⟩ : syracuseStep 1484991 = 2227487) B2227487
theorem B1878319 : Blo 1484062 1878319 := bstep (se 1 (by rfl) ⟨1408739, by rfl⟩ : syracuseStep 1878319 = 2817479) B2817479
theorem B1485103 : Blo 1484062 1485103 := bstep (se 1 (by rfl) ⟨1113827, by rfl⟩ : syracuseStep 1485103 = 2227655) B2227655
theorem B2288155 : Blo 1484062 2288155 := bstep (se 1 (by rfl) ⟨1716116, by rfl⟩ : syracuseStep 2288155 = 3432233) B3432233
theorem B1485339 : Blo 1484062 1485339 := bstep (se 1 (by rfl) ⟨1114004, by rfl⟩ : syracuseStep 1485339 = 2228009) B2228009
theorem B1485343 : Blo 1484062 1485343 := bstep (se 1 (by rfl) ⟨1114007, by rfl⟩ : syracuseStep 1485343 = 2228015) B2228015
theorem B96356897 : Blo 1484062 96356897 := bstep (se 2 (by rfl) ⟨36133836, by rfl⟩ : syracuseStep 96356897 = 72267673) B72267673
theorem B365587121 : Blo 1484062 365587121 := bstep (se 2 (by rfl) ⟨137095170, by rfl⟩ : syracuseStep 365587121 = 274190341) B274190341
theorem B2820919 : Blo 1484062 2820919 := bstep (se 1 (by rfl) ⟨2115689, by rfl⟩ : syracuseStep 2820919 = 4231379) B4231379
theorem B1485659 : Blo 1484062 1485659 := bstep (se 1 (by rfl) ⟨1114244, by rfl⟩ : syracuseStep 1485659 = 2228489) B2228489
theorem B1485727 : Blo 1484062 1485727 := bstep (se 1 (by rfl) ⟨1114295, by rfl⟩ : syracuseStep 1485727 = 2228591) B2228591
theorem B57863099 : Blo 1484062 57863099 := bstep (se 1 (by rfl) ⟨43397324, by rfl⟩ : syracuseStep 57863099 = 86794649) B86794649
theorem B1485871 : Blo 1484062 1485871 := bstep (se 1 (by rfl) ⟨1114403, by rfl⟩ : syracuseStep 1485871 = 2228807) B2228807
theorem B20319281 : Blo 1484062 20319281 := bstep (se 2 (by rfl) ⟨7619730, by rfl⟩ : syracuseStep 20319281 = 15239461) B15239461
theorem B1485895 : Blo 1484062 1485895 := bstep (se 1 (by rfl) ⟨1114421, by rfl⟩ : syracuseStep 1485895 = 2228843) B2228843
theorem B17157221 : Blo 1484062 17157221 := bstep (se 4 (by rfl) ⟨1608489, by rfl⟩ : syracuseStep 17157221 = 3216979) B3216979
theorem B1486047 : Blo 1484062 1486047 := bstep (se 1 (by rfl) ⟨1114535, by rfl⟩ : syracuseStep 1486047 = 2229071) B2229071
theorem B4230377 : Blo 1484062 4230377 := bstep (se 2 (by rfl) ⟨1586391, by rfl⟩ : syracuseStep 4230377 = 3172783) B3172783
theorem B4754675 : Blo 1484062 4754675 := bstep (se 1 (by rfl) ⟨3566006, by rfl⟩ : syracuseStep 4754675 = 7132013) B7132013
theorem B3812633 : Blo 1484062 3812633 := bstep (se 2 (by rfl) ⟨1429737, by rfl⟩ : syracuseStep 3812633 = 2859475) B2859475
theorem B4820303 : Blo 1484062 4820303 := bstep (se 1 (by rfl) ⟨3615227, by rfl⟩ : syracuseStep 4820303 = 7230455) B7230455
theorem B4230569 : Blo 1484062 4230569 := bstep (se 2 (by rfl) ⟨1586463, by rfl⟩ : syracuseStep 4230569 = 3172927) B3172927
theorem B5008823 : Blo 1484062 5008823 := bstep (se 1 (by rfl) ⟨3756617, by rfl⟩ : syracuseStep 5008823 = 7513235) B7513235
theorem B16920089 : Blo 1484062 16920089 := bstep (se 2 (by rfl) ⟨6345033, by rfl⟩ : syracuseStep 16920089 = 12690067) B12690067
theorem B9514529 : Blo 1484062 9514529 := bstep (se 2 (by rfl) ⟨3567948, by rfl⟩ : syracuseStep 9514529 = 7135897) B7135897
theorem B26070673 : Blo 1484062 26070673 := bstep (se 2 (by rfl) ⟨9776502, by rfl⟩ : syracuseStep 26070673 = 19553005) B19553005
theorem B2379439 : Blo 1484062 2379439 := bstep (se 1 (by rfl) ⟨1784579, by rfl⟩ : syracuseStep 2379439 = 3569159) B3569159
theorem B3010343 : Blo 1484062 3010343 := bstep (se 1 (by rfl) ⟨2257757, by rfl⟩ : syracuseStep 3010343 = 4515515) B4515515
theorem B7139279 : Blo 1484062 7139279 := bstep (se 1 (by rfl) ⟨5354459, by rfl⟩ : syracuseStep 7139279 = 10708919) B10708919
theorem B4886657 : Blo 1484062 4886657 := bstep (se 2 (by rfl) ⟨1832496, by rfl⟩ : syracuseStep 4886657 = 3664993) B3664993
theorem B4231561 : Blo 1484062 4231561 := bstep (se 2 (by rfl) ⟨1586835, by rfl⟩ : syracuseStep 4231561 = 3173671) B3173671
theorem B6345377 : Blo 1484062 6345377 := bstep (se 2 (by rfl) ⟨2379516, by rfl⟩ : syracuseStep 6345377 = 4759033) B4759033
theorem B4756265 : Blo 1484062 4756265 := bstep (se 2 (by rfl) ⟨1783599, by rfl⟩ : syracuseStep 4756265 = 3567199) B3567199
theorem B14496683 : Blo 1484062 14496683 := bstep (se 1 (by rfl) ⟨10872512, by rfl⟩ : syracuseStep 14496683 = 21745025) B21745025
theorem B6018155 : Blo 1484062 6018155 := bstep (se 1 (by rfl) ⟨4513616, by rfl⟩ : syracuseStep 6018155 = 9027233) B9027233
theorem B5641427 : Blo 1484062 5641427 := bstep (se 1 (by rfl) ⟨4231070, by rfl⟩ : syracuseStep 5641427 = 8462141) B8462141
theorem B3339539 : Blo 1484062 3339539 := bstep (se 1 (by rfl) ⟨2504654, by rfl⟩ : syracuseStep 3339539 = 5009309) B5009309
theorem B3339611 : Blo 1484062 3339611 := bstep (se 1 (by rfl) ⟨2504708, by rfl⟩ : syracuseStep 3339611 = 5009417) B5009417
theorem B5010875 : Blo 1484062 5010875 := bstep (se 1 (by rfl) ⟨3758156, by rfl⟩ : syracuseStep 5010875 = 7516313) B7516313
theorem B2504479 : Blo 1484062 2504479 := bstep (se 1 (by rfl) ⟨1878359, by rfl⟩ : syracuseStep 2504479 = 3756719) B3756719
theorem B3340169 : Blo 1484062 3340169 := bstep (se 2 (by rfl) ⟨1252563, by rfl⟩ : syracuseStep 3340169 = 2505127) B2505127
theorem B2226119 : Blo 1484062 2226119 := bstep (se 1 (by rfl) ⟨1669589, by rfl⟩ : syracuseStep 2226119 = 3339179) B3339179
theorem B5011415 : Blo 1484062 5011415 := bstep (se 1 (by rfl) ⟨3758561, by rfl⟩ : syracuseStep 5011415 = 7517123) B7517123
theorem B2504695 : Blo 1484062 2504695 := bstep (se 1 (by rfl) ⟨1878521, by rfl⟩ : syracuseStep 2504695 = 3757043) B3757043
theorem B3340385 : Blo 1484062 3340385 := bstep (se 2 (by rfl) ⟨1252644, by rfl⟩ : syracuseStep 3340385 = 2505289) B2505289
theorem B3758177 : Blo 1484062 3758177 := bstep (se 2 (by rfl) ⟨1409316, by rfl⟩ : syracuseStep 3758177 = 2818633) B2818633
theorem B4823183 : Blo 1484062 4823183 := bstep (se 1 (by rfl) ⟨3617387, by rfl⟩ : syracuseStep 4823183 = 7234775) B7234775
theorem B8026283 : Blo 1484062 8026283 := bstep (se 1 (by rfl) ⟨6019712, by rfl⟩ : syracuseStep 8026283 = 12039425) B12039425
theorem B11278601 : Blo 1484062 11278601 := bstep (se 2 (by rfl) ⟨4229475, by rfl⟩ : syracuseStep 11278601 = 8458951) B8458951
theorem B2504999 : Blo 1484062 2504999 := bstep (se 1 (by rfl) ⟨1878749, by rfl⟩ : syracuseStep 2504999 = 3757499) B3757499
theorem B2226473 : Blo 1484062 2226473 := bstep (se 2 (by rfl) ⟨834927, by rfl⟩ : syracuseStep 2226473 = 1669855) B1669855
theorem B2226479 : Blo 1484062 2226479 := bstep (se 1 (by rfl) ⟨1669859, by rfl⟩ : syracuseStep 2226479 = 3339719) B3339719
theorem B7133629 : Blo 1484062 7133629 := bstep (se 3 (by rfl) ⟨1337555, by rfl⟩ : syracuseStep 7133629 = 2675111) B2675111
theorem B5011901 : Blo 1484062 5011901 := bstep (se 3 (by rfl) ⟨939731, by rfl⟩ : syracuseStep 5011901 = 1879463) B1879463
theorem B2226719 : Blo 1484062 2226719 := bstep (se 1 (by rfl) ⟨1670039, by rfl⟩ : syracuseStep 2226719 = 3340079) B3340079
theorem B6773345 : Blo 1484062 6773345 := bstep (se 2 (by rfl) ⟨2540004, by rfl⟩ : syracuseStep 6773345 = 5080009) B5080009
theorem B9034487 : Blo 1484062 9034487 := bstep (se 1 (by rfl) ⟨6775865, by rfl⟩ : syracuseStep 9034487 = 13551731) B13551731
theorem B2227103 : Blo 1484062 2227103 := bstep (se 1 (by rfl) ⟨1670327, by rfl⟩ : syracuseStep 2227103 = 3340655) B3340655
theorem B3759007 : Blo 1484062 3759007 := bstep (se 1 (by rfl) ⟨2819255, by rfl⟩ : syracuseStep 3759007 = 5638511) B5638511
theorem B2227151 : Blo 1484062 2227151 := bstep (se 1 (by rfl) ⟨1670363, by rfl⟩ : syracuseStep 2227151 = 3340727) B3340727
theorem B2227241 : Blo 1484062 2227241 := bstep (se 2 (by rfl) ⟨835215, by rfl⟩ : syracuseStep 2227241 = 1670431) B1670431
theorem B2227247 : Blo 1484062 2227247 := bstep (se 1 (by rfl) ⟨1670435, by rfl⟩ : syracuseStep 2227247 = 3340871) B3340871
theorem B2505775 : Blo 1484062 2505775 := bstep (se 1 (by rfl) ⟨1879331, by rfl⟩ : syracuseStep 2505775 = 3758663) B3758663
theorem B2677807 : Blo 1484062 2677807 := bstep (se 1 (by rfl) ⟨2008355, by rfl⟩ : syracuseStep 2677807 = 4016711) B4016711
theorem B1670215 : Blo 1484062 1670215 := bstep (se 1 (by rfl) ⟨1252661, by rfl⟩ : syracuseStep 1670215 = 2505323) B2505323
theorem B2227271 : Blo 1484062 2227271 := bstep (se 1 (by rfl) ⟨1670453, by rfl⟩ : syracuseStep 2227271 = 3340907) B3340907
theorem B46972069 : Blo 1484062 46972069 := bstep (se 4 (by rfl) ⟨4403631, by rfl⟩ : syracuseStep 46972069 = 8807263) B8807263
theorem B5012765 : Blo 1484062 5012765 := bstep (se 3 (by rfl) ⟨939893, by rfl⟩ : syracuseStep 5012765 = 1879787) B1879787
theorem B2227535 : Blo 1484062 2227535 := bstep (se 1 (by rfl) ⟨1670651, by rfl⟩ : syracuseStep 2227535 = 3341303) B3341303
theorem B4013479 : Blo 1484062 4013479 := bstep (se 1 (by rfl) ⟨3010109, by rfl⟩ : syracuseStep 4013479 = 6020219) B6020219
theorem B3341735 : Blo 1484062 3341735 := bstep (se 1 (by rfl) ⟨2506301, by rfl⟩ : syracuseStep 3341735 = 5012603) B5012603
theorem B2227625 : Blo 1484062 2227625 := bstep (se 2 (by rfl) ⟨835359, by rfl⟩ : syracuseStep 2227625 = 1670719) B1670719
theorem B2506153 : Blo 1484062 2506153 := bstep (se 2 (by rfl) ⟨939807, by rfl⟩ : syracuseStep 2506153 = 1879615) B1879615
theorem B2227775 : Blo 1484062 2227775 := bstep (se 1 (by rfl) ⟨1670831, by rfl⟩ : syracuseStep 2227775 = 3341663) B3341663
theorem B9510479 : Blo 1484062 9510479 := bstep (se 1 (by rfl) ⟨7132859, by rfl⟩ : syracuseStep 9510479 = 14265719) B14265719
theorem B4226651 : Blo 1484062 4226651 := bstep (se 1 (by rfl) ⟨3169988, by rfl⟩ : syracuseStep 4226651 = 6339977) B6339977
theorem B3341915 : Blo 1484062 3341915 := bstep (se 1 (by rfl) ⟨2506436, by rfl⟩ : syracuseStep 3341915 = 5012873) B5012873
theorem B2228039 : Blo 1484062 2228039 := bstep (se 1 (by rfl) ⟨1671029, by rfl⟩ : syracuseStep 2228039 = 3342059) B3342059
theorem B2506619 : Blo 1484062 2506619 := bstep (se 1 (by rfl) ⟨1879964, by rfl⟩ : syracuseStep 2506619 = 3759929) B3759929
theorem B3342203 : Blo 1484062 3342203 := bstep (se 1 (by rfl) ⟨2506652, by rfl⟩ : syracuseStep 3342203 = 5013305) B5013305
theorem B2228123 : Blo 1484062 2228123 := bstep (se 1 (by rfl) ⟨1671092, by rfl⟩ : syracuseStep 2228123 = 3342185) B3342185
theorem B4227005 : Blo 1484062 4227005 := bstep (se 3 (by rfl) ⟨792563, by rfl⟩ : syracuseStep 4227005 = 1585127) B1585127
theorem B11001881 : Blo 1484062 11001881 := bstep (se 2 (by rfl) ⟨4125705, by rfl⟩ : syracuseStep 11001881 = 8251411) B8251411
theorem B3342527 : Blo 1484062 3342527 := bstep (se 1 (by rfl) ⟨2506895, by rfl⟩ : syracuseStep 3342527 = 5013791) B5013791
theorem B2506943 : Blo 1484062 2506943 := bstep (se 1 (by rfl) ⟨1880207, by rfl⟩ : syracuseStep 2506943 = 3760415) B3760415
theorem B2228459 : Blo 1484062 2228459 := bstep (se 1 (by rfl) ⟨1671344, by rfl⟩ : syracuseStep 2228459 = 3342689) B3342689
theorem B2228519 : Blo 1484062 2228519 := bstep (se 1 (by rfl) ⟨1671389, by rfl⟩ : syracuseStep 2228519 = 3342779) B3342779
theorem B12861821 : Blo 1484062 12861821 := bstep (se 3 (by rfl) ⟨2411591, by rfl⟩ : syracuseStep 12861821 = 4823183) B4823183
theorem B2507179 : Blo 1484062 2507179 := bstep (se 1 (by rfl) ⟨1880384, by rfl⟩ : syracuseStep 2507179 = 3760769) B3760769
theorem B5636567 : Blo 1484062 5636567 := bstep (se 1 (by rfl) ⟨4227425, by rfl⟩ : syracuseStep 5636567 = 8454851) B8454851
theorem B3170843 : Blo 1484062 3170843 := bstep (se 1 (by rfl) ⟨2378132, by rfl⟩ : syracuseStep 3170843 = 4756265) B4756265
theorem B9511505 : Blo 1484062 9511505 := bstep (se 2 (by rfl) ⟨3566814, by rfl⟩ : syracuseStep 9511505 = 7133629) B7133629
theorem B3342959 : Blo 1484062 3342959 := bstep (se 1 (by rfl) ⟨2507219, by rfl⟩ : syracuseStep 3342959 = 5014439) B5014439
theorem B2507375 : Blo 1484062 2507375 := bstep (se 1 (by rfl) ⟨1880531, by rfl⟩ : syracuseStep 2507375 = 3761063) B3761063
theorem B3760951 : Blo 1484062 3760951 := bstep (se 1 (by rfl) ⟨2820713, by rfl⟩ : syracuseStep 3760951 = 5641427) B5641427
theorem B12690341 : Blo 1484062 12690341 := bstep (se 4 (by rfl) ⟨1189719, by rfl⟩ : syracuseStep 12690341 = 2379439) B2379439
theorem B2507719 : Blo 1484062 2507719 := bstep (se 1 (by rfl) ⟨1880789, by rfl⟩ : syracuseStep 2507719 = 3761579) B3761579
theorem B3343355 : Blo 1484062 3343355 := bstep (se 1 (by rfl) ⟨2507516, by rfl⟩ : syracuseStep 3343355 = 5015033) B5015033
theorem B7521335 : Blo 1484062 7521335 := bstep (se 1 (by rfl) ⟨5641001, by rfl⟩ : syracuseStep 7521335 = 11282003) B11282003
theorem B3761225 : Blo 1484062 3761225 := bstep (se 2 (by rfl) ⟨1410459, by rfl⟩ : syracuseStep 3761225 = 2820919) B2820919
theorem B11281517 : Blo 1484062 11281517 := bstep (se 3 (by rfl) ⟨2115284, by rfl⟩ : syracuseStep 11281517 = 4230569) B4230569
theorem B3343535 : Blo 1484062 3343535 := bstep (se 1 (by rfl) ⟨2507651, by rfl⟩ : syracuseStep 3343535 = 5015303) B5015303
theorem B4015295 : Blo 1484062 4015295 := bstep (se 1 (by rfl) ⟨3011471, by rfl⟩ : syracuseStep 4015295 = 6022943) B6022943
theorem B3343571 : Blo 1484062 3343571 := bstep (se 1 (by rfl) ⟨2507678, by rfl⟩ : syracuseStep 3343571 = 5015357) B5015357
theorem B2114795 : Blo 1484062 2114795 := bstep (se 1 (by rfl) ⟨1586096, by rfl⟩ : syracuseStep 2114795 = 3172193) B3172193
theorem B1484079 : Blo 1484062 1484079 := bstep (se 1 (by rfl) ⟨1113059, by rfl⟩ : syracuseStep 1484079 = 2226119) B2226119
theorem B5080367 : Blo 1484062 5080367 := bstep (se 1 (by rfl) ⟨3810275, by rfl⟩ : syracuseStep 5080367 = 7620551) B7620551
theorem B8570299 : Blo 1484062 8570299 := bstep (se 1 (by rfl) ⟨6427724, by rfl⟩ : syracuseStep 8570299 = 12855449) B12855449
theorem B5350855 : Blo 1484062 5350855 := bstep (se 1 (by rfl) ⟨4013141, by rfl⟩ : syracuseStep 5350855 = 8026283) B8026283
theorem B1484315 : Blo 1484062 1484315 := bstep (se 1 (by rfl) ⟨1113236, by rfl⟩ : syracuseStep 1484315 = 2226473) B2226473
theorem B1484319 : Blo 1484062 1484319 := bstep (se 1 (by rfl) ⟨1113239, by rfl⟩ : syracuseStep 1484319 = 2226479) B2226479
theorem B1484479 : Blo 1484062 1484479 := bstep (se 1 (by rfl) ⟨1113359, by rfl⟩ : syracuseStep 1484479 = 2226719) B2226719
theorem B4515563 : Blo 1484062 4515563 := bstep (se 1 (by rfl) ⟨3386672, by rfl⟩ : syracuseStep 4515563 = 6773345) B6773345
theorem B6022991 : Blo 1484062 6022991 := bstep (se 1 (by rfl) ⟨4517243, by rfl⟩ : syracuseStep 6022991 = 9034487) B9034487
theorem B5351305 : Blo 1484062 5351305 := bstep (se 2 (by rfl) ⟨2006739, by rfl⟩ : syracuseStep 5351305 = 4013479) B4013479
theorem B1484735 : Blo 1484062 1484735 := bstep (se 1 (by rfl) ⟨1113551, by rfl⟩ : syracuseStep 1484735 = 2227103) B2227103
theorem B1484767 : Blo 1484062 1484767 := bstep (se 1 (by rfl) ⟨1113575, by rfl⟩ : syracuseStep 1484767 = 2227151) B2227151
theorem B1484827 : Blo 1484062 1484827 := bstep (se 1 (by rfl) ⟨1113620, by rfl⟩ : syracuseStep 1484827 = 2227241) B2227241
theorem B1484831 : Blo 1484062 1484831 := bstep (se 1 (by rfl) ⟨1113623, by rfl⟩ : syracuseStep 1484831 = 2227247) B2227247
theorem B1484847 : Blo 1484062 1484847 := bstep (se 1 (by rfl) ⟨1113635, by rfl⟩ : syracuseStep 1484847 = 2227271) B2227271
theorem B11438147 : Blo 1484062 11438147 := bstep (se 1 (by rfl) ⟨8578610, by rfl⟩ : syracuseStep 11438147 = 17157221) B17157221
theorem B45705293 : Blo 1484062 45705293 := bstep (se 3 (by rfl) ⟨8569742, by rfl⟩ : syracuseStep 45705293 = 17139485) B17139485
theorem B2820251 : Blo 1484062 2820251 := bstep (se 1 (by rfl) ⟨2115188, by rfl⟩ : syracuseStep 2820251 = 4230377) B4230377
theorem B34760897 : Blo 1484062 34760897 := bstep (se 2 (by rfl) ⟨13035336, by rfl⟩ : syracuseStep 34760897 = 26070673) B26070673
theorem B3213535 : Blo 1484062 3213535 := bstep (se 1 (by rfl) ⟨2410151, by rfl⟩ : syracuseStep 3213535 = 4820303) B4820303
theorem B1485023 : Blo 1484062 1485023 := bstep (se 1 (by rfl) ⟨1113767, by rfl⟩ : syracuseStep 1485023 = 2227535) B2227535
theorem B1485083 : Blo 1484062 1485083 := bstep (se 1 (by rfl) ⟨1113812, by rfl⟩ : syracuseStep 1485083 = 2227625) B2227625
theorem B6343019 : Blo 1484062 6343019 := bstep (se 1 (by rfl) ⟨4757264, by rfl⟩ : syracuseStep 6343019 = 9514529) B9514529
theorem B1485183 : Blo 1484062 1485183 := bstep (se 1 (by rfl) ⟨1113887, by rfl⟩ : syracuseStep 1485183 = 2227775) B2227775
theorem B1485359 : Blo 1484062 1485359 := bstep (se 1 (by rfl) ⟨1114019, by rfl⟩ : syracuseStep 1485359 = 2228039) B2228039
theorem B1485415 : Blo 1484062 1485415 := bstep (se 1 (by rfl) ⟨1114061, by rfl⟩ : syracuseStep 1485415 = 2228123) B2228123
theorem B40668085 : Blo 1484062 40668085 := bstep (se 5 (by rfl) ⟨1906316, by rfl⟩ : syracuseStep 40668085 = 3812633) B3812633
theorem B1485791 : Blo 1484062 1485791 := bstep (se 1 (by rfl) ⟨1114343, by rfl⟩ : syracuseStep 1485791 = 2228687) B2228687
theorem B1485819 : Blo 1484062 1485819 := bstep (se 1 (by rfl) ⟨1114364, by rfl⟩ : syracuseStep 1485819 = 2228729) B2228729
theorem B1485887 : Blo 1484062 1485887 := bstep (se 1 (by rfl) ⟨1114415, by rfl⟩ : syracuseStep 1485887 = 2228831) B2228831
theorem B4230251 : Blo 1484062 4230251 := bstep (se 1 (by rfl) ⟨3172688, by rfl⟩ : syracuseStep 4230251 = 6345377) B6345377
theorem B10710245 : Blo 1484062 10710245 := bstep (se 4 (by rfl) ⟨1004085, by rfl⟩ : syracuseStep 10710245 = 2008171) B2008171
theorem B3050873 : Blo 1484062 3050873 := bstep (se 2 (by rfl) ⟨1144077, by rfl⟩ : syracuseStep 3050873 = 2288155) B2288155
theorem B1879519 : Blo 1484062 1879519 := bstep (se 1 (by rfl) ⟨1409639, by rfl⟩ : syracuseStep 1879519 = 2819279) B2819279
theorem B9530875 : Blo 1484062 9530875 := bstep (se 1 (by rfl) ⟨7148156, by rfl⟩ : syracuseStep 9530875 = 14296313) B14296313
theorem B5009147 : Blo 1484062 5009147 := bstep (se 1 (by rfl) ⟨3756860, by rfl⟩ : syracuseStep 5009147 = 7513721) B7513721
theorem B42840049 : Blo 1484062 42840049 := bstep (se 2 (by rfl) ⟨16065018, by rfl⟩ : syracuseStep 42840049 = 32130037) B32130037
theorem B64237931 : Blo 1484062 64237931 := bstep (se 1 (by rfl) ⟨48178448, by rfl⟩ : syracuseStep 64237931 = 96356897) B96356897
theorem B5640637 : Blo 1484062 5640637 := bstep (se 3 (by rfl) ⟨1057619, by rfl⟩ : syracuseStep 5640637 = 2115239) B2115239
theorem B243724747 : Blo 1484062 243724747 := bstep (se 1 (by rfl) ⟨182793560, by rfl⟩ : syracuseStep 243724747 = 365587121) B365587121
theorem B13546187 : Blo 1484062 13546187 := bstep (se 1 (by rfl) ⟨10159640, by rfl⟩ : syracuseStep 13546187 = 20319281) B20319281
theorem B3339215 : Blo 1484062 3339215 := bstep (se 1 (by rfl) ⟨2504411, by rfl⟩ : syracuseStep 3339215 = 5008823) B5008823
theorem B3339305 : Blo 1484062 3339305 := bstep (se 2 (by rfl) ⟨1252239, by rfl⟩ : syracuseStep 3339305 = 2504479) B2504479
theorem B11277629 : Blo 1484062 11277629 := bstep (se 3 (by rfl) ⟨2114555, by rfl⟩ : syracuseStep 11277629 = 4229111) B4229111
theorem B3339593 : Blo 1484062 3339593 := bstep (se 2 (by rfl) ⟨1252347, by rfl⟩ : syracuseStep 3339593 = 2504695) B2504695
theorem B3257771 : Blo 1484062 3257771 := bstep (se 1 (by rfl) ⟨2443328, by rfl⟩ : syracuseStep 3257771 = 4886657) B4886657
theorem B5641883 : Blo 1484062 5641883 := bstep (se 1 (by rfl) ⟨4231412, by rfl⟩ : syracuseStep 5641883 = 8462825) B8462825
theorem B2504425 : Blo 1484062 2504425 := bstep (se 2 (by rfl) ⟨939159, by rfl⟩ : syracuseStep 2504425 = 1878319) B1878319
theorem B5642081 : Blo 1484062 5642081 := bstep (se 2 (by rfl) ⟨2115780, by rfl⟩ : syracuseStep 5642081 = 4231561) B4231561
theorem B4012103 : Blo 1484062 4012103 := bstep (se 1 (by rfl) ⟨3009077, by rfl⟩ : syracuseStep 4012103 = 6018155) B6018155
theorem B2226359 : Blo 1484062 2226359 := bstep (se 1 (by rfl) ⟨1669769, by rfl⟩ : syracuseStep 2226359 = 3339539) B3339539
theorem B250517701 : Blo 1484062 250517701 := bstep (se 4 (by rfl) ⟨23486034, by rfl⟩ : syracuseStep 250517701 = 46972069) B46972069
theorem B2226407 : Blo 1484062 2226407 := bstep (se 1 (by rfl) ⟨1669805, by rfl⟩ : syracuseStep 2226407 = 3339611) B3339611
theorem B3340583 : Blo 1484062 3340583 := bstep (se 1 (by rfl) ⟨2505437, by rfl⟩ : syracuseStep 3340583 = 5010875) B5010875
theorem B4757879 : Blo 1484062 4757879 := bstep (se 1 (by rfl) ⟨3568409, by rfl⟩ : syracuseStep 4757879 = 7136819) B7136819
theorem B8460683 : Blo 1484062 8460683 := bstep (se 1 (by rfl) ⟨6345512, by rfl⟩ : syracuseStep 8460683 = 12691025) B12691025
theorem B5012009 : Blo 1484062 5012009 := bstep (se 2 (by rfl) ⟨1879503, by rfl⟩ : syracuseStep 5012009 = 3759007) B3759007
theorem B2226779 : Blo 1484062 2226779 := bstep (se 1 (by rfl) ⟨1670084, by rfl⟩ : syracuseStep 2226779 = 3340169) B3340169
theorem B3570409 : Blo 1484062 3570409 := bstep (se 2 (by rfl) ⟨1338903, by rfl⟩ : syracuseStep 3570409 = 2677807) B2677807
theorem B3340943 : Blo 1484062 3340943 := bstep (se 1 (by rfl) ⟨2505707, by rfl⟩ : syracuseStep 3340943 = 5011415) B5011415
theorem B10705607 : Blo 1484062 10705607 := bstep (se 1 (by rfl) ⟨8029205, by rfl⟩ : syracuseStep 10705607 = 16058411) B16058411
theorem B14277329 : Blo 1484062 14277329 := bstep (se 2 (by rfl) ⟨5353998, by rfl⟩ : syracuseStep 14277329 = 10707997) B10707997
theorem B3341033 : Blo 1484062 3341033 := bstep (se 2 (by rfl) ⟨1252887, by rfl⟩ : syracuseStep 3341033 = 2505775) B2505775
theorem B2226923 : Blo 1484062 2226923 := bstep (se 1 (by rfl) ⟨1670192, by rfl⟩ : syracuseStep 2226923 = 3340385) B3340385
theorem B2505451 : Blo 1484062 2505451 := bstep (se 1 (by rfl) ⟨1879088, by rfl⟩ : syracuseStep 2505451 = 3758177) B3758177
theorem B2226953 : Blo 1484062 2226953 := bstep (se 2 (by rfl) ⟨835107, by rfl⟩ : syracuseStep 2226953 = 1670215) B1670215
theorem B7519067 : Blo 1484062 7519067 := bstep (se 1 (by rfl) ⟨5639300, by rfl⟩ : syracuseStep 7519067 = 11278601) B11278601
theorem B1669999 : Blo 1484062 1669999 := bstep (se 1 (by rfl) ⟨1252499, by rfl⟩ : syracuseStep 1669999 = 2504999) B2504999
theorem B3341267 : Blo 1484062 3341267 := bstep (se 1 (by rfl) ⟨2505950, by rfl⟩ : syracuseStep 3341267 = 5011901) B5011901
theorem B3341537 : Blo 1484062 3341537 := bstep (se 2 (by rfl) ⟨1253076, by rfl⟩ : syracuseStep 3341537 = 2506153) B2506153
theorem B38575399 : Blo 1484062 38575399 := bstep (se 1 (by rfl) ⟨28931549, by rfl⟩ : syracuseStep 38575399 = 57863099) B57863099
theorem B8027581 : Blo 1484062 8027581 := bstep (se 3 (by rfl) ⟨1505171, by rfl⟩ : syracuseStep 8027581 = 3010343) B3010343
theorem B3169783 : Blo 1484062 3169783 := bstep (se 1 (by rfl) ⟨2377337, by rfl⟩ : syracuseStep 3169783 = 4754675) B4754675
theorem B3341843 : Blo 1484062 3341843 := bstep (se 1 (by rfl) ⟨2506382, by rfl⟩ : syracuseStep 3341843 = 5012765) B5012765
theorem B2227823 : Blo 1484062 2227823 := bstep (se 1 (by rfl) ⟨1670867, by rfl⟩ : syracuseStep 2227823 = 3341735) B3341735
theorem B11280059 : Blo 1484062 11280059 := bstep (se 1 (by rfl) ⟨8460044, by rfl⟩ : syracuseStep 11280059 = 16920089) B16920089
theorem B6340319 : Blo 1484062 6340319 := bstep (se 1 (by rfl) ⟨4755239, by rfl⟩ : syracuseStep 6340319 = 9510479) B9510479
theorem B2817767 : Blo 1484062 2817767 := bstep (se 1 (by rfl) ⟨2113325, by rfl⟩ : syracuseStep 2817767 = 4226651) B4226651
theorem B2227943 : Blo 1484062 2227943 := bstep (se 1 (by rfl) ⟨1670957, by rfl⟩ : syracuseStep 2227943 = 3341915) B3341915
theorem B38657821 : Blo 1484062 38657821 := bstep (se 3 (by rfl) ⟨7248341, by rfl⟩ : syracuseStep 38657821 = 14496683) B14496683
theorem B19038077 : Blo 1484062 19038077 := bstep (se 3 (by rfl) ⟨3569639, by rfl⟩ : syracuseStep 19038077 = 7139279) B7139279
theorem B1671079 : Blo 1484062 1671079 := bstep (se 1 (by rfl) ⟨1253309, by rfl⟩ : syracuseStep 1671079 = 2506619) B2506619
theorem B2228135 : Blo 1484062 2228135 := bstep (se 1 (by rfl) ⟨1671101, by rfl⟩ : syracuseStep 2228135 = 3342203) B3342203
theorem B2818003 : Blo 1484062 2818003 := bstep (se 1 (by rfl) ⟨2113502, by rfl⟩ : syracuseStep 2818003 = 4227005) B4227005
theorem B2228351 : Blo 1484062 2228351 := bstep (se 1 (by rfl) ⟨1671263, by rfl⟩ : syracuseStep 2228351 = 3342527) B3342527
theorem B1671295 : Blo 1484062 1671295 := bstep (se 1 (by rfl) ⟨1253471, by rfl⟩ : syracuseStep 1671295 = 2506943) B2506943
theorem B10698941 : Blo 1484062 10698941 := bstep (se 3 (by rfl) ⟨2006051, by rfl⟩ : syracuseStep 10698941 = 4012103) B4012103
theorem B4284713 : Blo 1484062 4284713 := bstep (se 2 (by rfl) ⟨1606767, by rfl⟩ : syracuseStep 4284713 = 3213535) B3213535
theorem B2113895 : Blo 1484062 2113895 := bstep (se 1 (by rfl) ⟨1585421, by rfl⟩ : syracuseStep 2113895 = 3170843) B3170843
theorem B6341003 : Blo 1484062 6341003 := bstep (se 1 (by rfl) ⟨4755752, by rfl⟩ : syracuseStep 6341003 = 9511505) B9511505
theorem B2228639 : Blo 1484062 2228639 := bstep (se 1 (by rfl) ⟨1671479, by rfl⟩ : syracuseStep 2228639 = 3342959) B3342959
theorem B1671583 : Blo 1484062 1671583 := bstep (se 1 (by rfl) ⟨1253687, by rfl⟩ : syracuseStep 1671583 = 2507375) B2507375
theorem B3342905 : Blo 1484062 3342905 := bstep (se 2 (by rfl) ⟨1253589, by rfl⟩ : syracuseStep 3342905 = 2507179) B2507179
theorem B7520849 : Blo 1484062 7520849 := bstep (se 2 (by rfl) ⟨2820318, by rfl⟩ : syracuseStep 7520849 = 5640637) B5640637
theorem B2228903 : Blo 1484062 2228903 := bstep (se 1 (by rfl) ⟨1671677, by rfl⟩ : syracuseStep 2228903 = 3343355) B3343355
theorem B5014223 : Blo 1484062 5014223 := bstep (se 1 (by rfl) ⟨3760667, by rfl⟩ : syracuseStep 5014223 = 7521335) B7521335
theorem B2507483 : Blo 1484062 2507483 := bstep (se 1 (by rfl) ⟨1880612, by rfl⟩ : syracuseStep 2507483 = 3761225) B3761225
theorem B7521011 : Blo 1484062 7521011 := bstep (se 1 (by rfl) ⟨5640758, by rfl⟩ : syracuseStep 7521011 = 11281517) B11281517
theorem B2229023 : Blo 1484062 2229023 := bstep (se 1 (by rfl) ⟨1671767, by rfl⟩ : syracuseStep 2229023 = 3343535) B3343535
theorem B2229047 : Blo 1484062 2229047 := bstep (se 1 (by rfl) ⟨1671785, by rfl⟩ : syracuseStep 2229047 = 3343571) B3343571
theorem B4760545 : Blo 1484062 4760545 := bstep (se 2 (by rfl) ⟨1785204, by rfl⟩ : syracuseStep 4760545 = 3570409) B3570409
theorem B5014601 : Blo 1484062 5014601 := bstep (se 2 (by rfl) ⟨1880475, by rfl⟩ : syracuseStep 5014601 = 3760951) B3760951
theorem B3761255 : Blo 1484062 3761255 := bstep (se 1 (by rfl) ⟨2820941, by rfl⟩ : syracuseStep 3761255 = 5641883) B5641883
theorem B4015327 : Blo 1484062 4015327 := bstep (se 1 (by rfl) ⟨3011495, by rfl⟩ : syracuseStep 4015327 = 6022991) B6022991
theorem B3761387 : Blo 1484062 3761387 := bstep (se 1 (by rfl) ⟨2821040, by rfl⟩ : syracuseStep 3761387 = 5642081) B5642081
theorem B54224113 : Blo 1484062 54224113 := bstep (se 2 (by rfl) ⟨20334042, by rfl⟩ : syracuseStep 54224113 = 40668085) B40668085
theorem B3343625 : Blo 1484062 3343625 := bstep (se 2 (by rfl) ⟨1253859, by rfl⟩ : syracuseStep 3343625 = 2507719) B2507719
theorem B1484239 : Blo 1484062 1484239 := bstep (se 1 (by rfl) ⟨1113179, by rfl⟩ : syracuseStep 1484239 = 2226359) B2226359
theorem B1484271 : Blo 1484062 1484271 := bstep (se 1 (by rfl) ⟨1113203, by rfl⟩ : syracuseStep 1484271 = 2226407) B2226407
theorem B4228679 : Blo 1484062 4228679 := bstep (se 1 (by rfl) ⟨3171509, by rfl⟩ : syracuseStep 4228679 = 6343019) B6343019
theorem B1484519 : Blo 1484062 1484519 := bstep (se 1 (by rfl) ⟨1113389, by rfl⟩ : syracuseStep 1484519 = 2226779) B2226779
theorem B7137071 : Blo 1484062 7137071 := bstep (se 1 (by rfl) ⟨5352803, by rfl⟩ : syracuseStep 7137071 = 10705607) B10705607
theorem B1484615 : Blo 1484062 1484615 := bstep (se 1 (by rfl) ⟨1113461, by rfl⟩ : syracuseStep 1484615 = 2226923) B2226923
theorem B1484635 : Blo 1484062 1484635 := bstep (se 1 (by rfl) ⟨1113476, by rfl⟩ : syracuseStep 1484635 = 2226953) B2226953
theorem B7514045 : Blo 1484062 7514045 := bstep (se 3 (by rfl) ⟨1408883, by rfl⟩ : syracuseStep 7514045 = 2817767) B2817767
theorem B2820167 : Blo 1484062 2820167 := bstep (se 1 (by rfl) ⟨2115125, by rfl⟩ : syracuseStep 2820167 = 4230251) B4230251
theorem B2033915 : Blo 1484062 2033915 := bstep (se 1 (by rfl) ⟨1525436, by rfl⟩ : syracuseStep 2033915 = 3050873) B3050873
theorem B1485215 : Blo 1484062 1485215 := bstep (se 1 (by rfl) ⟨1113911, by rfl⟩ : syracuseStep 1485215 = 2227823) B2227823
theorem B1485295 : Blo 1484062 1485295 := bstep (se 1 (by rfl) ⟨1113971, by rfl⟩ : syracuseStep 1485295 = 2227943) B2227943
theorem B12692051 : Blo 1484062 12692051 := bstep (se 1 (by rfl) ⟨9519038, by rfl⟩ : syracuseStep 12692051 = 19038077) B19038077
theorem B1485423 : Blo 1484062 1485423 := bstep (se 1 (by rfl) ⟨1114067, by rfl⟩ : syracuseStep 1485423 = 2228135) B2228135
theorem B7334587 : Blo 1484062 7334587 := bstep (se 1 (by rfl) ⟨5500940, by rfl⟩ : syracuseStep 7334587 = 11001881) B11001881
theorem B1485639 : Blo 1484062 1485639 := bstep (se 1 (by rfl) ⟨1114229, by rfl⟩ : syracuseStep 1485639 = 2228459) B2228459
theorem B1485679 : Blo 1484062 1485679 := bstep (se 1 (by rfl) ⟨1114259, by rfl⟩ : syracuseStep 1485679 = 2228519) B2228519
theorem B334023601 : Blo 1484062 334023601 := bstep (se 2 (by rfl) ⟨125258850, by rfl⟩ : syracuseStep 334023601 = 250517701) B250517701
theorem B9030791 : Blo 1484062 9030791 := bstep (se 1 (by rfl) ⟨6773093, by rfl⟩ : syracuseStep 9030791 = 13546187) B13546187
theorem B5639453 : Blo 1484062 5639453 := bstep (se 3 (by rfl) ⟨1057397, by rfl⟩ : syracuseStep 5639453 = 2114795) B2114795
theorem B8687389 : Blo 1484062 8687389 := bstep (se 3 (by rfl) ⟨1628885, by rfl⟩ : syracuseStep 8687389 = 3257771) B3257771
theorem B3010375 : Blo 1484062 3010375 := bstep (se 1 (by rfl) ⟨2257781, by rfl⟩ : syracuseStep 3010375 = 4515563) B4515563
theorem B30470195 : Blo 1484062 30470195 := bstep (se 1 (by rfl) ⟨22852646, by rfl⟩ : syracuseStep 30470195 = 45705293) B45705293
theorem B1880167 : Blo 1484062 1880167 := bstep (se 1 (by rfl) ⟨1410125, by rfl⟩ : syracuseStep 1880167 = 2820251) B2820251
theorem B5640455 : Blo 1484062 5640455 := bstep (se 1 (by rfl) ⟨4230341, by rfl⟩ : syracuseStep 5640455 = 8460683) B8460683
theorem B51433865 : Blo 1484062 51433865 := bstep (se 2 (by rfl) ⟨19287699, by rfl⟩ : syracuseStep 51433865 = 38575399) B38575399
theorem B10703441 : Blo 1484062 10703441 := bstep (se 2 (by rfl) ⟨4013790, by rfl⟩ : syracuseStep 10703441 = 8027581) B8027581
theorem B7140163 : Blo 1484062 7140163 := bstep (se 1 (by rfl) ⟨5355122, by rfl⟩ : syracuseStep 7140163 = 10710245) B10710245
theorem B3339233 : Blo 1484062 3339233 := bstep (se 2 (by rfl) ⟨1252212, by rfl⟩ : syracuseStep 3339233 = 2504425) B2504425
theorem B3339431 : Blo 1484062 3339431 := bstep (se 1 (by rfl) ⟨2504573, by rfl⟩ : syracuseStep 3339431 = 5009147) B5009147
theorem B3757337 : Blo 1484062 3757337 := bstep (se 2 (by rfl) ⟨1409001, by rfl⟩ : syracuseStep 3757337 = 2818003) B2818003
theorem B16905509 : Blo 1484062 16905509 := bstep (se 4 (by rfl) ⟨1584891, by rfl⟩ : syracuseStep 16905509 = 3169783) B3169783
theorem B57120065 : Blo 1484062 57120065 := bstep (se 2 (by rfl) ⟨21420024, by rfl⟩ : syracuseStep 57120065 = 42840049) B42840049
theorem B42825287 : Blo 1484062 42825287 := bstep (se 1 (by rfl) ⟨32118965, by rfl⟩ : syracuseStep 42825287 = 64237931) B64237931
theorem B8574547 : Blo 1484062 8574547 := bstep (se 1 (by rfl) ⟨6430910, by rfl⟩ : syracuseStep 8574547 = 12861821) B12861821
theorem B3757711 : Blo 1484062 3757711 := bstep (se 1 (by rfl) ⟨2818283, by rfl⟩ : syracuseStep 3757711 = 5636567) B5636567
theorem B324966329 : Blo 1484062 324966329 := bstep (se 2 (by rfl) ⟨121862373, by rfl⟩ : syracuseStep 324966329 = 243724747) B243724747
theorem B8460227 : Blo 1484062 8460227 := bstep (se 1 (by rfl) ⟨6345170, by rfl⟩ : syracuseStep 8460227 = 12690341) B12690341
theorem B2226143 : Blo 1484062 2226143 := bstep (se 1 (by rfl) ⟨1669607, by rfl⟩ : syracuseStep 2226143 = 3339215) B3339215
theorem B2226203 : Blo 1484062 2226203 := bstep (se 1 (by rfl) ⟨1669652, by rfl⟩ : syracuseStep 2226203 = 3339305) B3339305
theorem B13547645 : Blo 1484062 13547645 := bstep (se 3 (by rfl) ⟨2540183, by rfl⟩ : syracuseStep 13547645 = 5080367) B5080367
theorem B2676863 : Blo 1484062 2676863 := bstep (se 1 (by rfl) ⟨2007647, by rfl⟩ : syracuseStep 2676863 = 4015295) B4015295
theorem B7518419 : Blo 1484062 7518419 := bstep (se 1 (by rfl) ⟨5638814, by rfl⟩ : syracuseStep 7518419 = 11277629) B11277629
theorem B2226395 : Blo 1484062 2226395 := bstep (se 1 (by rfl) ⟨1669796, by rfl⟩ : syracuseStep 2226395 = 3339593) B3339593
theorem B3340601 : Blo 1484062 3340601 := bstep (se 2 (by rfl) ⟨1252725, by rfl⟩ : syracuseStep 3340601 = 2505451) B2505451
theorem B12687677 : Blo 1484062 12687677 := bstep (se 3 (by rfl) ⟨2378939, by rfl⟩ : syracuseStep 12687677 = 4757879) B4757879
theorem B2226665 : Blo 1484062 2226665 := bstep (se 2 (by rfl) ⟨834999, by rfl⟩ : syracuseStep 2226665 = 1669999) B1669999
theorem B7625431 : Blo 1484062 7625431 := bstep (se 1 (by rfl) ⟨5719073, by rfl⟩ : syracuseStep 7625431 = 11438147) B11438147
theorem B23173931 : Blo 1484062 23173931 := bstep (se 1 (by rfl) ⟨17380448, by rfl⟩ : syracuseStep 23173931 = 34760897) B34760897
theorem B2227055 : Blo 1484062 2227055 := bstep (se 1 (by rfl) ⟨1670291, by rfl⟩ : syracuseStep 2227055 = 3340583) B3340583
theorem B3341339 : Blo 1484062 3341339 := bstep (se 1 (by rfl) ⟨2506004, by rfl⟩ : syracuseStep 3341339 = 5012009) B5012009
theorem B2227295 : Blo 1484062 2227295 := bstep (se 1 (by rfl) ⟨1670471, by rfl⟩ : syracuseStep 2227295 = 3340943) B3340943
theorem B9518219 : Blo 1484062 9518219 := bstep (se 1 (by rfl) ⟨7138664, by rfl⟩ : syracuseStep 9518219 = 14277329) B14277329
theorem B2227355 : Blo 1484062 2227355 := bstep (se 1 (by rfl) ⟨1670516, by rfl⟩ : syracuseStep 2227355 = 3341033) B3341033
theorem B5012711 : Blo 1484062 5012711 := bstep (se 1 (by rfl) ⟨3759533, by rfl⟩ : syracuseStep 5012711 = 7519067) B7519067
theorem B11427065 : Blo 1484062 11427065 := bstep (se 2 (by rfl) ⟨4285149, by rfl⟩ : syracuseStep 11427065 = 8570299) B8570299
theorem B7134473 : Blo 1484062 7134473 := bstep (se 2 (by rfl) ⟨2675427, by rfl⟩ : syracuseStep 7134473 = 5350855) B5350855
theorem B2506025 : Blo 1484062 2506025 := bstep (se 2 (by rfl) ⟨939759, by rfl⟩ : syracuseStep 2506025 = 1879519) B1879519
theorem B2227511 : Blo 1484062 2227511 := bstep (se 1 (by rfl) ⟨1670633, by rfl⟩ : syracuseStep 2227511 = 3341267) B3341267
theorem B2227691 : Blo 1484062 2227691 := bstep (se 1 (by rfl) ⟨1670768, by rfl⟩ : syracuseStep 2227691 = 3341537) B3341537
theorem B2227895 : Blo 1484062 2227895 := bstep (se 1 (by rfl) ⟨1670921, by rfl⟩ : syracuseStep 2227895 = 3341843) B3341843
theorem B51543761 : Blo 1484062 51543761 := bstep (se 2 (by rfl) ⟨19328910, by rfl⟩ : syracuseStep 51543761 = 38657821) B38657821
theorem B7520039 : Blo 1484062 7520039 := bstep (se 1 (by rfl) ⟨5640029, by rfl⟩ : syracuseStep 7520039 = 11280059) B11280059
theorem B4226879 : Blo 1484062 4226879 := bstep (se 1 (by rfl) ⟨3170159, by rfl⟩ : syracuseStep 4226879 = 6340319) B6340319
theorem B7135073 : Blo 1484062 7135073 := bstep (se 2 (by rfl) ⟨2675652, by rfl⟩ : syracuseStep 7135073 = 5351305) B5351305
theorem B2228105 : Blo 1484062 2228105 := bstep (se 2 (by rfl) ⟨835539, by rfl⟩ : syracuseStep 2228105 = 1671079) B1671079
theorem B50831333 : Blo 1484062 50831333 := bstep (se 4 (by rfl) ⟨4765437, by rfl⟩ : syracuseStep 50831333 = 9530875) B9530875
theorem B2506889 : Blo 1484062 2506889 := bstep (se 2 (by rfl) ⟨940083, by rfl⟩ : syracuseStep 2506889 = 1880167) B1880167
theorem B2228393 : Blo 1484062 2228393 := bstep (se 2 (by rfl) ⟨835647, by rfl⟩ : syracuseStep 2228393 = 1671295) B1671295
theorem B3760303 : Blo 1484062 3760303 := bstep (se 1 (by rfl) ⟨2820227, by rfl⟩ : syracuseStep 3760303 = 5640455) B5640455
theorem B4227335 : Blo 1484062 4227335 := bstep (se 1 (by rfl) ⟨3170501, by rfl⟩ : syracuseStep 4227335 = 6341003) B6341003
theorem B2228603 : Blo 1484062 2228603 := bstep (se 1 (by rfl) ⟨1671452, by rfl⟩ : syracuseStep 2228603 = 3342905) B3342905
theorem B7135627 : Blo 1484062 7135627 := bstep (se 1 (by rfl) ⟨5351720, by rfl⟩ : syracuseStep 7135627 = 10703441) B10703441
theorem B5013899 : Blo 1484062 5013899 := bstep (se 1 (by rfl) ⟨3760424, by rfl⟩ : syracuseStep 5013899 = 7520849) B7520849
theorem B3342815 : Blo 1484062 3342815 := bstep (se 1 (by rfl) ⟨2507111, by rfl⟩ : syracuseStep 3342815 = 5014223) B5014223
theorem B1671655 : Blo 1484062 1671655 := bstep (se 1 (by rfl) ⟨1253741, by rfl⟩ : syracuseStep 1671655 = 2507483) B2507483
theorem B5014007 : Blo 1484062 5014007 := bstep (se 1 (by rfl) ⟨3760505, by rfl⟩ : syracuseStep 5014007 = 7521011) B7521011
theorem B2228777 : Blo 1484062 2228777 := bstep (se 2 (by rfl) ⟨835791, by rfl⟩ : syracuseStep 2228777 = 1671583) B1671583
theorem B5423773 : Blo 1484062 5423773 := bstep (se 3 (by rfl) ⟨1016957, by rfl⟩ : syracuseStep 5423773 = 2033915) B2033915
theorem B3343067 : Blo 1484062 3343067 := bstep (se 1 (by rfl) ⟨2507300, by rfl⟩ : syracuseStep 3343067 = 5014601) B5014601
theorem B2507503 : Blo 1484062 2507503 := bstep (se 1 (by rfl) ⟨1880627, by rfl⟩ : syracuseStep 2507503 = 3761255) B3761255
theorem B2507591 : Blo 1484062 2507591 := bstep (se 1 (by rfl) ⟨1880693, by rfl⟩ : syracuseStep 2507591 = 3761387) B3761387
theorem B2229083 : Blo 1484062 2229083 := bstep (se 1 (by rfl) ⟨1671812, by rfl⟩ : syracuseStep 2229083 = 3343625) B3343625
theorem B5637053 : Blo 1484062 5637053 := bstep (se 3 (by rfl) ⟨1056947, by rfl⟩ : syracuseStep 5637053 = 2113895) B2113895
theorem B2819119 : Blo 1484062 2819119 := bstep (se 1 (by rfl) ⟨2114339, by rfl⟩ : syracuseStep 2819119 = 4228679) B4228679
theorem B28550191 : Blo 1484062 28550191 := bstep (se 1 (by rfl) ⟨21412643, by rfl⟩ : syracuseStep 28550191 = 42825287) B42825287
theorem B9520217 : Blo 1484062 9520217 := bstep (se 2 (by rfl) ⟨3570081, by rfl⟩ : syracuseStep 9520217 = 7140163) B7140163
theorem B1484095 : Blo 1484062 1484095 := bstep (se 1 (by rfl) ⟨1113071, by rfl⟩ : syracuseStep 1484095 = 2226143) B2226143
theorem B1484135 : Blo 1484062 1484135 := bstep (se 1 (by rfl) ⟨1113101, by rfl⟩ : syracuseStep 1484135 = 2226203) B2226203
theorem B1484263 : Blo 1484062 1484263 := bstep (se 1 (by rfl) ⟨1113197, by rfl⟩ : syracuseStep 1484263 = 2226395) B2226395
theorem B1484443 : Blo 1484062 1484443 := bstep (se 1 (by rfl) ⟨1113332, by rfl⟩ : syracuseStep 1484443 = 2226665) B2226665
theorem B1484703 : Blo 1484062 1484703 := bstep (se 1 (by rfl) ⟨1113527, by rfl⟩ : syracuseStep 1484703 = 2227055) B2227055
theorem B1484863 : Blo 1484062 1484863 := bstep (se 1 (by rfl) ⟨1113647, by rfl⟩ : syracuseStep 1484863 = 2227295) B2227295
theorem B1484903 : Blo 1484062 1484903 := bstep (se 1 (by rfl) ⟨1113677, by rfl⟩ : syracuseStep 1484903 = 2227355) B2227355
theorem B1485007 : Blo 1484062 1485007 := bstep (se 1 (by rfl) ⟨1113755, by rfl⟩ : syracuseStep 1485007 = 2227511) B2227511
theorem B1485127 : Blo 1484062 1485127 := bstep (se 1 (by rfl) ⟨1113845, by rfl⟩ : syracuseStep 1485127 = 2227691) B2227691
theorem B1485263 : Blo 1484062 1485263 := bstep (se 1 (by rfl) ⟨1113947, by rfl⟩ : syracuseStep 1485263 = 2227895) B2227895
theorem B1485403 : Blo 1484062 1485403 := bstep (se 1 (by rfl) ⟨1114052, by rfl⟩ : syracuseStep 1485403 = 2228105) B2228105
theorem B1485567 : Blo 1484062 1485567 := bstep (se 1 (by rfl) ⟨1114175, by rfl⟩ : syracuseStep 1485567 = 2228351) B2228351
theorem B1485759 : Blo 1484062 1485759 := bstep (se 1 (by rfl) ⟨1114319, by rfl⟩ : syracuseStep 1485759 = 2228639) B2228639
theorem B1485935 : Blo 1484062 1485935 := bstep (se 1 (by rfl) ⟨1114451, by rfl⟩ : syracuseStep 1485935 = 2228903) B2228903
theorem B1486015 : Blo 1484062 1486015 := bstep (se 1 (by rfl) ⟨1114511, by rfl⟩ : syracuseStep 1486015 = 2229023) B2229023
theorem B1486031 : Blo 1484062 1486031 := bstep (se 1 (by rfl) ⟨1114523, by rfl⟩ : syracuseStep 1486031 = 2229047) B2229047
theorem B38080043 : Blo 1484062 38080043 := bstep (se 1 (by rfl) ⟨28560032, by rfl⟩ : syracuseStep 38080043 = 57120065) B57120065
theorem B40668965 : Blo 1484062 40668965 := bstep (se 4 (by rfl) ⟨3812715, by rfl⟩ : syracuseStep 40668965 = 7625431) B7625431
theorem B5009363 : Blo 1484062 5009363 := bstep (se 1 (by rfl) ⟨3757022, by rfl⟩ : syracuseStep 5009363 = 7514045) B7514045
theorem B5640151 : Blo 1484062 5640151 := bstep (se 1 (by rfl) ⟨4230113, by rfl⟩ : syracuseStep 5640151 = 8460227) B8460227
theorem B1880111 : Blo 1484062 1880111 := bstep (se 1 (by rfl) ⟨1410083, by rfl⟩ : syracuseStep 1880111 = 2820167) B2820167
theorem B9031763 : Blo 1484062 9031763 := bstep (se 1 (by rfl) ⟨6773822, by rfl⟩ : syracuseStep 9031763 = 13547645) B13547645
theorem B8458451 : Blo 1484062 8458451 := bstep (se 1 (by rfl) ⟨6343838, by rfl⟩ : syracuseStep 8458451 = 12687677) B12687677
theorem B5353769 : Blo 1484062 5353769 := bstep (se 2 (by rfl) ⟨2007663, by rfl⟩ : syracuseStep 5353769 = 4015327) B4015327
theorem B72298817 : Blo 1484062 72298817 := bstep (se 2 (by rfl) ⟨27112056, by rfl⟩ : syracuseStep 72298817 = 54224113) B54224113
theorem B137450029 : Blo 1484062 137450029 := bstep (se 3 (by rfl) ⟨25771880, by rfl⟩ : syracuseStep 137450029 = 51543761) B51543761
theorem B6345479 : Blo 1484062 6345479 := bstep (se 1 (by rfl) ⟨4759109, by rfl⟩ : syracuseStep 6345479 = 9518219) B9518219
theorem B11432729 : Blo 1484062 11432729 := bstep (se 2 (by rfl) ⟨4287273, by rfl⟩ : syracuseStep 11432729 = 8574547) B8574547
theorem B4756315 : Blo 1484062 4756315 := bstep (se 1 (by rfl) ⟨3567236, by rfl⟩ : syracuseStep 4756315 = 7134473) B7134473
theorem B5010281 : Blo 1484062 5010281 := bstep (se 2 (by rfl) ⟨1878855, by rfl⟩ : syracuseStep 5010281 = 3757711) B3757711
theorem B4756715 : Blo 1484062 4756715 := bstep (se 1 (by rfl) ⟨3567536, by rfl⟩ : syracuseStep 4756715 = 7135073) B7135073
theorem B33887555 : Blo 1484062 33887555 := bstep (se 1 (by rfl) ⟨25415666, by rfl⟩ : syracuseStep 33887555 = 50831333) B50831333
theorem B7132627 : Blo 1484062 7132627 := bstep (se 1 (by rfl) ⟨5349470, by rfl⟩ : syracuseStep 7132627 = 10698941) B10698941
theorem B81253853 : Blo 1484062 81253853 := bstep (se 3 (by rfl) ⟨15235097, by rfl⟩ : syracuseStep 81253853 = 30470195) B30470195
theorem B2856475 : Blo 1484062 2856475 := bstep (se 1 (by rfl) ⟨2142356, by rfl⟩ : syracuseStep 2856475 = 4284713) B4284713
theorem B34289243 : Blo 1484062 34289243 := bstep (se 1 (by rfl) ⟨25716932, by rfl⟩ : syracuseStep 34289243 = 51433865) B51433865
theorem B2226155 : Blo 1484062 2226155 := bstep (se 1 (by rfl) ⟨1669616, by rfl⟩ : syracuseStep 2226155 = 3339233) B3339233
theorem B2226287 : Blo 1484062 2226287 := bstep (se 1 (by rfl) ⟨1669715, by rfl⟩ : syracuseStep 2226287 = 3339431) B3339431
theorem B2504891 : Blo 1484062 2504891 := bstep (se 1 (by rfl) ⟨1878668, by rfl⟩ : syracuseStep 2504891 = 3757337) B3757337
theorem B11270339 : Blo 1484062 11270339 := bstep (se 1 (by rfl) ⟨8452754, by rfl⟩ : syracuseStep 11270339 = 16905509) B16905509
theorem B9779449 : Blo 1484062 9779449 := bstep (se 2 (by rfl) ⟨3667293, by rfl⟩ : syracuseStep 9779449 = 7334587) B7334587
theorem B4758047 : Blo 1484062 4758047 := bstep (se 1 (by rfl) ⟨3568535, by rfl⟩ : syracuseStep 4758047 = 7137071) B7137071
theorem B445364801 : Blo 1484062 445364801 := bstep (se 2 (by rfl) ⟨167011800, by rfl⟩ : syracuseStep 445364801 = 334023601) B334023601
theorem B216644219 : Blo 1484062 216644219 := bstep (se 1 (by rfl) ⟨162483164, by rfl⟩ : syracuseStep 216644219 = 324966329) B324966329
theorem B6347393 : Blo 1484062 6347393 := bstep (se 2 (by rfl) ⟨2380272, by rfl⟩ : syracuseStep 6347393 = 4760545) B4760545
theorem B1784575 : Blo 1484062 1784575 := bstep (se 1 (by rfl) ⟨1338431, by rfl⟩ : syracuseStep 1784575 = 2676863) B2676863
theorem B5012279 : Blo 1484062 5012279 := bstep (se 1 (by rfl) ⟨3759209, by rfl⟩ : syracuseStep 5012279 = 7518419) B7518419
theorem B2227067 : Blo 1484062 2227067 := bstep (se 1 (by rfl) ⟨1670300, by rfl⟩ : syracuseStep 2227067 = 3340601) B3340601
theorem B16055333 : Blo 1484062 16055333 := bstep (se 4 (by rfl) ⟨1505187, by rfl⟩ : syracuseStep 16055333 = 3010375) B3010375
theorem B8461367 : Blo 1484062 8461367 := bstep (se 1 (by rfl) ⟨6346025, by rfl⟩ : syracuseStep 8461367 = 12692051) B12692051
theorem B15449287 : Blo 1484062 15449287 := bstep (se 1 (by rfl) ⟨11586965, by rfl⟩ : syracuseStep 15449287 = 23173931) B23173931
theorem B2227559 : Blo 1484062 2227559 := bstep (se 1 (by rfl) ⟨1670669, by rfl⟩ : syracuseStep 2227559 = 3341339) B3341339
theorem B6020527 : Blo 1484062 6020527 := bstep (se 1 (by rfl) ⟨4515395, by rfl⟩ : syracuseStep 6020527 = 9030791) B9030791
theorem B3341807 : Blo 1484062 3341807 := bstep (se 1 (by rfl) ⟨2506355, by rfl⟩ : syracuseStep 3341807 = 5012711) B5012711
theorem B7618043 : Blo 1484062 7618043 := bstep (se 1 (by rfl) ⟨5713532, by rfl⟩ : syracuseStep 7618043 = 11427065) B11427065
theorem B3759635 : Blo 1484062 3759635 := bstep (se 1 (by rfl) ⟨2819726, by rfl⟩ : syracuseStep 3759635 = 5639453) B5639453
theorem B1670683 : Blo 1484062 1670683 := bstep (se 1 (by rfl) ⟨1253012, by rfl⟩ : syracuseStep 1670683 = 2506025) B2506025
theorem B11583185 : Blo 1484062 11583185 := bstep (se 2 (by rfl) ⟨4343694, by rfl⟩ : syracuseStep 11583185 = 8687389) B8687389
theorem B5013359 : Blo 1484062 5013359 := bstep (se 1 (by rfl) ⟨3760019, by rfl⟩ : syracuseStep 5013359 = 7520039) B7520039
theorem B2817919 : Blo 1484062 2817919 := bstep (se 1 (by rfl) ⟨2113439, by rfl⟩ : syracuseStep 2817919 = 4226879) B4226879
theorem B6021175 : Blo 1484062 6021175 := bstep (se 1 (by rfl) ⟨4515881, by rfl⟩ : syracuseStep 6021175 = 9031763) B9031763
theorem B1671259 : Blo 1484062 1671259 := bstep (se 1 (by rfl) ⟨1253444, by rfl⟩ : syracuseStep 1671259 = 2506889) B2506889
theorem B5013629 : Blo 1484062 5013629 := bstep (se 3 (by rfl) ⟨940055, by rfl⟩ : syracuseStep 5013629 = 1880111) B1880111
theorem B2818223 : Blo 1484062 2818223 := bstep (se 1 (by rfl) ⟨2113667, by rfl⟩ : syracuseStep 2818223 = 4227335) B4227335
theorem B5013737 : Blo 1484062 5013737 := bstep (se 2 (by rfl) ⟨1880151, by rfl⟩ : syracuseStep 5013737 = 3760303) B3760303
theorem B3342599 : Blo 1484062 3342599 := bstep (se 1 (by rfl) ⟨2506949, by rfl⟩ : syracuseStep 3342599 = 5013899) B5013899
theorem B2228543 : Blo 1484062 2228543 := bstep (se 1 (by rfl) ⟨1671407, by rfl⟩ : syracuseStep 2228543 = 3342815) B3342815
theorem B3342671 : Blo 1484062 3342671 := bstep (se 1 (by rfl) ⟨2507003, by rfl⟩ : syracuseStep 3342671 = 5014007) B5014007
theorem B2228711 : Blo 1484062 2228711 := bstep (se 1 (by rfl) ⟨1671533, by rfl⟩ : syracuseStep 2228711 = 3343067) B3343067
theorem B1671727 : Blo 1484062 1671727 := bstep (se 1 (by rfl) ⟨1253795, by rfl⟩ : syracuseStep 1671727 = 2507591) B2507591
theorem B2228873 : Blo 1484062 2228873 := bstep (se 2 (by rfl) ⟨835827, by rfl⟩ : syracuseStep 2228873 = 1671655) B1671655
theorem B3171143 : Blo 1484062 3171143 := bstep (se 1 (by rfl) ⟨2378357, by rfl⟩ : syracuseStep 3171143 = 4756715) B4756715
theorem B3343337 : Blo 1484062 3343337 := bstep (se 2 (by rfl) ⟨1253751, by rfl⟩ : syracuseStep 3343337 = 2507503) B2507503
theorem B6341753 : Blo 1484062 6341753 := bstep (se 2 (by rfl) ⟨2378157, by rfl⟩ : syracuseStep 6341753 = 4756315) B4756315
theorem B1484103 : Blo 1484062 1484103 := bstep (se 1 (by rfl) ⟨1113077, by rfl⟩ : syracuseStep 1484103 = 2226155) B2226155
theorem B1484191 : Blo 1484062 1484191 := bstep (se 1 (by rfl) ⟨1113143, by rfl⟩ : syracuseStep 1484191 = 2226287) B2226287
theorem B7513559 : Blo 1484062 7513559 := bstep (se 1 (by rfl) ⟨5635169, by rfl⟩ : syracuseStep 7513559 = 11270339) B11270339
theorem B3172031 : Blo 1484062 3172031 := bstep (se 1 (by rfl) ⟨2379023, by rfl⟩ : syracuseStep 3172031 = 4758047) B4758047
theorem B1484711 : Blo 1484062 1484711 := bstep (se 1 (by rfl) ⟨1113533, by rfl⟩ : syracuseStep 1484711 = 2227067) B2227067
theorem B123553973 : Blo 1484062 123553973 := bstep (se 5 (by rfl) ⟨5791592, by rfl⟩ : syracuseStep 123553973 = 11583185) B11583185
theorem B1485039 : Blo 1484062 1485039 := bstep (se 1 (by rfl) ⟨1113779, by rfl⟩ : syracuseStep 1485039 = 2227559) B2227559
theorem B1485595 : Blo 1484062 1485595 := bstep (se 1 (by rfl) ⟨1114196, by rfl⟩ : syracuseStep 1485595 = 2228393) B2228393
theorem B5638967 : Blo 1484062 5638967 := bstep (se 1 (by rfl) ⟨4229225, by rfl⟩ : syracuseStep 5638967 = 8458451) B8458451
theorem B1485735 : Blo 1484062 1485735 := bstep (se 1 (by rfl) ⟨1114301, by rfl⟩ : syracuseStep 1485735 = 2228603) B2228603
theorem B1485851 : Blo 1484062 1485851 := bstep (se 1 (by rfl) ⟨1114388, by rfl⟩ : syracuseStep 1485851 = 2228777) B2228777
theorem B4230319 : Blo 1484062 4230319 := bstep (se 1 (by rfl) ⟨3172739, by rfl⟩ : syracuseStep 4230319 = 6345479) B6345479
theorem B9514169 : Blo 1484062 9514169 := bstep (se 2 (by rfl) ⟨3567813, by rfl⟩ : syracuseStep 9514169 = 7135627) B7135627
theorem B7621819 : Blo 1484062 7621819 := bstep (se 1 (by rfl) ⟨5716364, by rfl⟩ : syracuseStep 7621819 = 11432729) B11432729
theorem B1486055 : Blo 1484062 1486055 := bstep (se 1 (by rfl) ⟨1114541, by rfl⟩ : syracuseStep 1486055 = 2229083) B2229083
theorem B183266705 : Blo 1484062 183266705 := bstep (se 2 (by rfl) ⟨68725014, by rfl⟩ : syracuseStep 183266705 = 137450029) B137450029
theorem B54169235 : Blo 1484062 54169235 := bstep (se 1 (by rfl) ⟨40626926, by rfl⟩ : syracuseStep 54169235 = 81253853) B81253853
theorem B22859495 : Blo 1484062 22859495 := bstep (se 1 (by rfl) ⟨17144621, by rfl⟩ : syracuseStep 22859495 = 34289243) B34289243
theorem B20599049 : Blo 1484062 20599049 := bstep (se 2 (by rfl) ⟨7724643, by rfl⟩ : syracuseStep 20599049 = 15449287) B15449287
theorem B144429479 : Blo 1484062 144429479 := bstep (se 1 (by rfl) ⟨108322109, by rfl⟩ : syracuseStep 144429479 = 216644219) B216644219
theorem B4231595 : Blo 1484062 4231595 := bstep (se 1 (by rfl) ⟨3173696, by rfl⟩ : syracuseStep 4231595 = 6347393) B6347393
theorem B10703555 : Blo 1484062 10703555 := bstep (se 1 (by rfl) ⟨8027666, by rfl⟩ : syracuseStep 10703555 = 16055333) B16055333
theorem B5640911 : Blo 1484062 5640911 := bstep (se 1 (by rfl) ⟨4230683, by rfl⟩ : syracuseStep 5640911 = 8461367) B8461367
theorem B38040677 : Blo 1484062 38040677 := bstep (se 4 (by rfl) ⟨3566313, by rfl⟩ : syracuseStep 38040677 = 7132627) B7132627
theorem B3757225 : Blo 1484062 3757225 := bstep (se 2 (by rfl) ⟨1408959, by rfl⟩ : syracuseStep 3757225 = 2817919) B2817919
theorem B27112643 : Blo 1484062 27112643 := bstep (se 1 (by rfl) ⟨20334482, by rfl⟩ : syracuseStep 27112643 = 40668965) B40668965
theorem B3339575 : Blo 1484062 3339575 := bstep (se 1 (by rfl) ⟨2504681, by rfl⟩ : syracuseStep 3339575 = 5009363) B5009363
theorem B3569179 : Blo 1484062 3569179 := bstep (se 1 (by rfl) ⟨2676884, by rfl⟩ : syracuseStep 3569179 = 5353769) B5353769
theorem B48199211 : Blo 1484062 48199211 := bstep (se 1 (by rfl) ⟨36149408, by rfl⟩ : syracuseStep 48199211 = 72298817) B72298817
theorem B13039265 : Blo 1484062 13039265 := bstep (se 2 (by rfl) ⟨4889724, by rfl⟩ : syracuseStep 13039265 = 9779449) B9779449
theorem B3340187 : Blo 1484062 3340187 := bstep (se 1 (by rfl) ⟨2505140, by rfl⟩ : syracuseStep 3340187 = 5010281) B5010281
theorem B3758035 : Blo 1484062 3758035 := bstep (se 1 (by rfl) ⟨2818526, by rfl⟩ : syracuseStep 3758035 = 5637053) B5637053
theorem B6346811 : Blo 1484062 6346811 := bstep (se 1 (by rfl) ⟨4760108, by rfl⟩ : syracuseStep 6346811 = 9520217) B9520217
theorem B7231697 : Blo 1484062 7231697 := bstep (se 2 (by rfl) ⟨2711886, by rfl⟩ : syracuseStep 7231697 = 5423773) B5423773
theorem B22591703 : Blo 1484062 22591703 := bstep (se 1 (by rfl) ⟨16943777, by rfl⟩ : syracuseStep 22591703 = 33887555) B33887555
theorem B9517733 : Blo 1484062 9517733 := bstep (se 4 (by rfl) ⟨892287, by rfl⟩ : syracuseStep 9517733 = 1784575) B1784575
theorem B3758825 : Blo 1484062 3758825 := bstep (se 2 (by rfl) ⟨1409559, by rfl⟩ : syracuseStep 3758825 = 2819119) B2819119
theorem B38066921 : Blo 1484062 38066921 := bstep (se 2 (by rfl) ⟨14275095, by rfl⟩ : syracuseStep 38066921 = 28550191) B28550191
theorem B1669927 : Blo 1484062 1669927 := bstep (se 1 (by rfl) ⟨1252445, by rfl⟩ : syracuseStep 1669927 = 2504891) B2504891
theorem B296909867 : Blo 1484062 296909867 := bstep (se 1 (by rfl) ⟨222682400, by rfl⟩ : syracuseStep 296909867 = 445364801) B445364801
theorem B3341519 : Blo 1484062 3341519 := bstep (se 1 (by rfl) ⟨2506139, by rfl⟩ : syracuseStep 3341519 = 5012279) B5012279
theorem B8027369 : Blo 1484062 8027369 := bstep (se 2 (by rfl) ⟨3010263, by rfl⟩ : syracuseStep 8027369 = 6020527) B6020527
theorem B3808633 : Blo 1484062 3808633 := bstep (se 2 (by rfl) ⟨1428237, by rfl⟩ : syracuseStep 3808633 = 2856475) B2856475
theorem B2227577 : Blo 1484062 2227577 := bstep (se 2 (by rfl) ⟨835341, by rfl⟩ : syracuseStep 2227577 = 1670683) B1670683
theorem B2227871 : Blo 1484062 2227871 := bstep (se 1 (by rfl) ⟨1670903, by rfl⟩ : syracuseStep 2227871 = 3341807) B3341807
theorem B5078695 : Blo 1484062 5078695 := bstep (se 1 (by rfl) ⟨3809021, by rfl⟩ : syracuseStep 5078695 = 7618043) B7618043
theorem B2506423 : Blo 1484062 2506423 := bstep (se 1 (by rfl) ⟨1879817, by rfl⟩ : syracuseStep 2506423 = 3759635) B3759635
theorem B25386695 : Blo 1484062 25386695 := bstep (se 1 (by rfl) ⟨19040021, by rfl⟩ : syracuseStep 25386695 = 38080043) B38080043
theorem B3342239 : Blo 1484062 3342239 := bstep (se 1 (by rfl) ⟨2506679, by rfl⟩ : syracuseStep 3342239 = 5013359) B5013359
theorem B7520201 : Blo 1484062 7520201 := bstep (se 2 (by rfl) ⟨2820075, by rfl⟩ : syracuseStep 7520201 = 5640151) B5640151
theorem B8028233 : Blo 1484062 8028233 := bstep (se 2 (by rfl) ⟨3010587, by rfl⟩ : syracuseStep 8028233 = 6021175) B6021175
theorem B3342419 : Blo 1484062 3342419 := bstep (se 1 (by rfl) ⟨2506814, by rfl⟩ : syracuseStep 3342419 = 5013629) B5013629
theorem B2228345 : Blo 1484062 2228345 := bstep (se 2 (by rfl) ⟨835629, by rfl⟩ : syracuseStep 2228345 = 1671259) B1671259
theorem B3342491 : Blo 1484062 3342491 := bstep (se 1 (by rfl) ⟨2506868, by rfl⟩ : syracuseStep 3342491 = 5013737) B5013737
theorem B2228399 : Blo 1484062 2228399 := bstep (se 1 (by rfl) ⟨1671299, by rfl⟩ : syracuseStep 2228399 = 3342599) B3342599
theorem B2228447 : Blo 1484062 2228447 := bstep (se 1 (by rfl) ⟨1671335, by rfl⟩ : syracuseStep 2228447 = 3342671) B3342671
theorem B7135703 : Blo 1484062 7135703 := bstep (se 1 (by rfl) ⟨5351777, by rfl⟩ : syracuseStep 7135703 = 10703555) B10703555
theorem B3760607 : Blo 1484062 3760607 := bstep (se 1 (by rfl) ⟨2820455, by rfl⟩ : syracuseStep 3760607 = 5640911) B5640911
theorem B2114095 : Blo 1484062 2114095 := bstep (se 1 (by rfl) ⟨1585571, by rfl⟩ : syracuseStep 2114095 = 3171143) B3171143
theorem B2228891 : Blo 1484062 2228891 := bstep (se 1 (by rfl) ⟨1671668, by rfl⟩ : syracuseStep 2228891 = 3343337) B3343337
theorem B2228969 : Blo 1484062 2228969 := bstep (se 2 (by rfl) ⟨835863, by rfl⟩ : syracuseStep 2228969 = 1671727) B1671727
theorem B40649701 : Blo 1484062 40649701 := bstep (se 4 (by rfl) ⟨3810909, by rfl⟩ : syracuseStep 40649701 = 7621819) B7621819
theorem B8692843 : Blo 1484062 8692843 := bstep (se 1 (by rfl) ⟨6519632, by rfl⟩ : syracuseStep 8692843 = 13039265) B13039265
theorem B2114687 : Blo 1484062 2114687 := bstep (se 1 (by rfl) ⟨1586015, by rfl⟩ : syracuseStep 2114687 = 3172031) B3172031
theorem B6342779 : Blo 1484062 6342779 := bstep (se 1 (by rfl) ⟨4757084, by rfl⟩ : syracuseStep 6342779 = 9514169) B9514169
theorem B5351579 : Blo 1484062 5351579 := bstep (se 1 (by rfl) ⟨4013684, by rfl⟩ : syracuseStep 5351579 = 8027369) B8027369
theorem B1485051 : Blo 1484062 1485051 := bstep (se 1 (by rfl) ⟨1113788, by rfl⟩ : syracuseStep 1485051 = 2227577) B2227577
theorem B122177803 : Blo 1484062 122177803 := bstep (se 1 (by rfl) ⟨91633352, by rfl⟩ : syracuseStep 122177803 = 183266705) B183266705
theorem B36112823 : Blo 1484062 36112823 := bstep (se 1 (by rfl) ⟨27084617, by rfl⟩ : syracuseStep 36112823 = 54169235) B54169235
theorem B1485247 : Blo 1484062 1485247 := bstep (se 1 (by rfl) ⟨1113935, by rfl⟩ : syracuseStep 1485247 = 2227871) B2227871
theorem B15239663 : Blo 1484062 15239663 := bstep (se 1 (by rfl) ⟨11429747, by rfl⟩ : syracuseStep 15239663 = 22859495) B22859495
theorem B1878815 : Blo 1484062 1878815 := bstep (se 1 (by rfl) ⟨1409111, by rfl⟩ : syracuseStep 1878815 = 2818223) B2818223
theorem B1485695 : Blo 1484062 1485695 := bstep (se 1 (by rfl) ⟨1114271, by rfl⟩ : syracuseStep 1485695 = 2228543) B2228543
theorem B2821063 : Blo 1484062 2821063 := bstep (se 1 (by rfl) ⟨2115797, by rfl⟩ : syracuseStep 2821063 = 4231595) B4231595
theorem B16911341 : Blo 1484062 16911341 := bstep (se 3 (by rfl) ⟨3170876, by rfl⟩ : syracuseStep 16911341 = 6341753) B6341753
theorem B1485807 : Blo 1484062 1485807 := bstep (se 1 (by rfl) ⟨1114355, by rfl⟩ : syracuseStep 1485807 = 2228711) B2228711
theorem B1485915 : Blo 1484062 1485915 := bstep (se 1 (by rfl) ⟨1114436, by rfl⟩ : syracuseStep 1485915 = 2228873) B2228873
theorem B54930797 : Blo 1484062 54930797 := bstep (se 3 (by rfl) ⟨10299524, by rfl⟩ : syracuseStep 54930797 = 20599049) B20599049
theorem B18075095 : Blo 1484062 18075095 := bstep (se 1 (by rfl) ⟨13556321, by rfl⟩ : syracuseStep 18075095 = 27112643) B27112643
theorem B5009039 : Blo 1484062 5009039 := bstep (se 1 (by rfl) ⟨3756779, by rfl⟩ : syracuseStep 5009039 = 7513559) B7513559
theorem B32132807 : Blo 1484062 32132807 := bstep (se 1 (by rfl) ⟨24099605, by rfl⟩ : syracuseStep 32132807 = 48199211) B48199211
theorem B4231207 : Blo 1484062 4231207 := bstep (se 1 (by rfl) ⟨3173405, by rfl⟩ : syracuseStep 4231207 = 6346811) B6346811
theorem B4821131 : Blo 1484062 4821131 := bstep (se 1 (by rfl) ⟨3615848, by rfl⟩ : syracuseStep 4821131 = 7231697) B7231697
theorem B15061135 : Blo 1484062 15061135 := bstep (se 1 (by rfl) ⟨11295851, by rfl⟩ : syracuseStep 15061135 = 22591703) B22591703
theorem B5009633 : Blo 1484062 5009633 := bstep (se 2 (by rfl) ⟨1878612, by rfl⟩ : syracuseStep 5009633 = 3757225) B3757225
theorem B5640425 : Blo 1484062 5640425 := bstep (se 2 (by rfl) ⟨2115159, by rfl⟩ : syracuseStep 5640425 = 4230319) B4230319
theorem B6345155 : Blo 1484062 6345155 := bstep (se 1 (by rfl) ⟨4758866, by rfl⟩ : syracuseStep 6345155 = 9517733) B9517733
theorem B197939911 : Blo 1484062 197939911 := bstep (se 1 (by rfl) ⟨148454933, by rfl⟩ : syracuseStep 197939911 = 296909867) B296909867
theorem B6771593 : Blo 1484062 6771593 := bstep (se 2 (by rfl) ⟨2539347, by rfl⟩ : syracuseStep 6771593 = 5078695) B5078695
theorem B5010713 : Blo 1484062 5010713 := bstep (se 2 (by rfl) ⟨1879017, by rfl⟩ : syracuseStep 5010713 = 3758035) B3758035
theorem B96286319 : Blo 1484062 96286319 := bstep (se 1 (by rfl) ⟨72214739, by rfl⟩ : syracuseStep 96286319 = 144429479) B144429479
theorem B25360451 : Blo 1484062 25360451 := bstep (se 1 (by rfl) ⟨19020338, by rfl⟩ : syracuseStep 25360451 = 38040677) B38040677
theorem B2226383 : Blo 1484062 2226383 := bstep (se 1 (by rfl) ⟨1669787, by rfl⟩ : syracuseStep 2226383 = 3339575) B3339575
theorem B2226569 : Blo 1484062 2226569 := bstep (se 2 (by rfl) ⟨834963, by rfl⟩ : syracuseStep 2226569 = 1669927) B1669927
theorem B2226791 : Blo 1484062 2226791 := bstep (se 1 (by rfl) ⟨1670093, by rfl⟩ : syracuseStep 2226791 = 3340187) B3340187
theorem B82369315 : Blo 1484062 82369315 := bstep (se 1 (by rfl) ⟨61776986, by rfl⟩ : syracuseStep 82369315 = 123553973) B123553973
theorem B2505883 : Blo 1484062 2505883 := bstep (se 1 (by rfl) ⟨1879412, by rfl⟩ : syracuseStep 2505883 = 3758825) B3758825
theorem B25377947 : Blo 1484062 25377947 := bstep (se 1 (by rfl) ⟨19033460, by rfl⟩ : syracuseStep 25377947 = 38066921) B38066921
theorem B5078177 : Blo 1484062 5078177 := bstep (se 2 (by rfl) ⟨1904316, by rfl⟩ : syracuseStep 5078177 = 3808633) B3808633
theorem B3759311 : Blo 1484062 3759311 := bstep (se 1 (by rfl) ⟨2819483, by rfl⟩ : syracuseStep 3759311 = 5638967) B5638967
theorem B4758905 : Blo 1484062 4758905 := bstep (se 2 (by rfl) ⟨1784589, by rfl⟩ : syracuseStep 4758905 = 3569179) B3569179
theorem B2227679 : Blo 1484062 2227679 := bstep (se 1 (by rfl) ⟨1670759, by rfl⟩ : syracuseStep 2227679 = 3341519) B3341519
theorem B3341897 : Blo 1484062 3341897 := bstep (se 2 (by rfl) ⟨1253211, by rfl⟩ : syracuseStep 3341897 = 2506423) B2506423
theorem B16924463 : Blo 1484062 16924463 := bstep (se 1 (by rfl) ⟨12693347, by rfl⟩ : syracuseStep 16924463 = 25386695) B25386695
theorem B2228159 : Blo 1484062 2228159 := bstep (se 1 (by rfl) ⟨1671119, by rfl⟩ : syracuseStep 2228159 = 3342239) B3342239
theorem B5013467 : Blo 1484062 5013467 := bstep (se 1 (by rfl) ⟨3760100, by rfl⟩ : syracuseStep 5013467 = 7520201) B7520201
theorem B2228279 : Blo 1484062 2228279 := bstep (se 1 (by rfl) ⟨1671209, by rfl⟩ : syracuseStep 2228279 = 3342419) B3342419
theorem B2228327 : Blo 1484062 2228327 := bstep (se 1 (by rfl) ⟨1671245, by rfl⟩ : syracuseStep 2228327 = 3342491) B3342491
theorem B3760283 : Blo 1484062 3760283 := bstep (se 1 (by rfl) ⟨2820212, by rfl⟩ : syracuseStep 3760283 = 5640425) B5640425
theorem B2507071 : Blo 1484062 2507071 := bstep (se 1 (by rfl) ⟨1880303, by rfl⟩ : syracuseStep 2507071 = 3760607) B3760607
theorem B4514395 : Blo 1484062 4514395 := bstep (se 1 (by rfl) ⟨3385796, by rfl⟩ : syracuseStep 4514395 = 6771593) B6771593
theorem B2818793 : Blo 1484062 2818793 := bstep (se 2 (by rfl) ⟨1057047, by rfl⟩ : syracuseStep 2818793 = 2114095) B2114095
theorem B3761417 : Blo 1484062 3761417 := bstep (se 2 (by rfl) ⟨1410531, by rfl⟩ : syracuseStep 3761417 = 2821063) B2821063
theorem B54199601 : Blo 1484062 54199601 := bstep (se 2 (by rfl) ⟨20324850, by rfl⟩ : syracuseStep 54199601 = 40649701) B40649701
theorem B4228519 : Blo 1484062 4228519 := bstep (se 1 (by rfl) ⟨3171389, by rfl⟩ : syracuseStep 4228519 = 6342779) B6342779
theorem B1484255 : Blo 1484062 1484255 := bstep (se 1 (by rfl) ⟨1113191, by rfl⟩ : syracuseStep 1484255 = 2226383) B2226383
theorem B1484379 : Blo 1484062 1484379 := bstep (se 1 (by rfl) ⟨1113284, by rfl⟩ : syracuseStep 1484379 = 2226569) B2226569
theorem B10159775 : Blo 1484062 10159775 := bstep (se 1 (by rfl) ⟨7619831, by rfl⟩ : syracuseStep 10159775 = 15239663) B15239663
theorem B1484527 : Blo 1484062 1484527 := bstep (se 1 (by rfl) ⟨1113395, by rfl⟩ : syracuseStep 1484527 = 2226791) B2226791
theorem B11274227 : Blo 1484062 11274227 := bstep (se 1 (by rfl) ⟨8455670, by rfl⟩ : syracuseStep 11274227 = 16911341) B16911341
theorem B16918631 : Blo 1484062 16918631 := bstep (se 1 (by rfl) ⟨12688973, by rfl⟩ : syracuseStep 16918631 = 25377947) B25377947
theorem B3385451 : Blo 1484062 3385451 := bstep (se 1 (by rfl) ⟨2539088, by rfl⟩ : syracuseStep 3385451 = 5078177) B5078177
theorem B36620531 : Blo 1484062 36620531 := bstep (se 1 (by rfl) ⟨27465398, by rfl⟩ : syracuseStep 36620531 = 54930797) B54930797
theorem B3172603 : Blo 1484062 3172603 := bstep (se 1 (by rfl) ⟨2379452, by rfl⟩ : syracuseStep 3172603 = 4758905) B4758905
theorem B1485119 : Blo 1484062 1485119 := bstep (se 1 (by rfl) ⟨1113839, by rfl⟩ : syracuseStep 1485119 = 2227679) B2227679
theorem B11282975 : Blo 1484062 11282975 := bstep (se 1 (by rfl) ⟨8462231, by rfl⟩ : syracuseStep 11282975 = 16924463) B16924463
theorem B1485439 : Blo 1484062 1485439 := bstep (se 1 (by rfl) ⟨1114079, by rfl⟩ : syracuseStep 1485439 = 2228159) B2228159
theorem B5352155 : Blo 1484062 5352155 := bstep (se 1 (by rfl) ⟨4014116, by rfl⟩ : syracuseStep 5352155 = 8028233) B8028233
theorem B1485563 : Blo 1484062 1485563 := bstep (se 1 (by rfl) ⟨1114172, by rfl⟩ : syracuseStep 1485563 = 2228345) B2228345
theorem B3214087 : Blo 1484062 3214087 := bstep (se 1 (by rfl) ⟨2410565, by rfl⟩ : syracuseStep 3214087 = 4821131) B4821131
theorem B1485599 : Blo 1484062 1485599 := bstep (se 1 (by rfl) ⟨1114199, by rfl⟩ : syracuseStep 1485599 = 2228399) B2228399
theorem B1485631 : Blo 1484062 1485631 := bstep (se 1 (by rfl) ⟨1114223, by rfl⟩ : syracuseStep 1485631 = 2228447) B2228447
theorem B20081513 : Blo 1484062 20081513 := bstep (se 2 (by rfl) ⟨7530567, by rfl⟩ : syracuseStep 20081513 = 15061135) B15061135
theorem B4230103 : Blo 1484062 4230103 := bstep (se 1 (by rfl) ⟨3172577, by rfl⟩ : syracuseStep 4230103 = 6345155) B6345155
theorem B5639165 : Blo 1484062 5639165 := bstep (se 3 (by rfl) ⟨1057343, by rfl⟩ : syracuseStep 5639165 = 2114687) B2114687
theorem B1485927 : Blo 1484062 1485927 := bstep (se 1 (by rfl) ⟨1114445, by rfl⟩ : syracuseStep 1485927 = 2228891) B2228891
theorem B1485979 : Blo 1484062 1485979 := bstep (se 1 (by rfl) ⟨1114484, by rfl⟩ : syracuseStep 1485979 = 2228969) B2228969
theorem B109825753 : Blo 1484062 109825753 := bstep (se 2 (by rfl) ⟨41184657, by rfl⟩ : syracuseStep 109825753 = 82369315) B82369315
theorem B3567719 : Blo 1484062 3567719 := bstep (se 1 (by rfl) ⟨2675789, by rfl⟩ : syracuseStep 3567719 = 5351579) B5351579
theorem B5010173 : Blo 1484062 5010173 := bstep (se 3 (by rfl) ⟨939407, by rfl⟩ : syracuseStep 5010173 = 1878815) B1878815
theorem B3339359 : Blo 1484062 3339359 := bstep (se 1 (by rfl) ⟨2504519, by rfl⟩ : syracuseStep 3339359 = 5009039) B5009039
theorem B5641609 : Blo 1484062 5641609 := bstep (se 2 (by rfl) ⟨2115603, by rfl⟩ : syracuseStep 5641609 = 4231207) B4231207
theorem B3339755 : Blo 1484062 3339755 := bstep (se 1 (by rfl) ⟨2504816, by rfl⟩ : syracuseStep 3339755 = 5009633) B5009633
theorem B4757135 : Blo 1484062 4757135 := bstep (se 1 (by rfl) ⟨3567851, by rfl⟩ : syracuseStep 4757135 = 7135703) B7135703
theorem B162903737 : Blo 1484062 162903737 := bstep (se 2 (by rfl) ⟨61088901, by rfl⟩ : syracuseStep 162903737 = 122177803) B122177803
theorem B3340475 : Blo 1484062 3340475 := bstep (se 1 (by rfl) ⟨2505356, by rfl⟩ : syracuseStep 3340475 = 5010713) B5010713
theorem B263919881 : Blo 1484062 263919881 := bstep (se 2 (by rfl) ⟨98969955, by rfl⟩ : syracuseStep 263919881 = 197939911) B197939911
theorem B64190879 : Blo 1484062 64190879 := bstep (se 1 (by rfl) ⟨48143159, by rfl⟩ : syracuseStep 64190879 = 96286319) B96286319
theorem B16906967 : Blo 1484062 16906967 := bstep (se 1 (by rfl) ⟨12680225, by rfl⟩ : syracuseStep 16906967 = 25360451) B25360451
theorem B11590457 : Blo 1484062 11590457 := bstep (se 2 (by rfl) ⟨4346421, by rfl⟩ : syracuseStep 11590457 = 8692843) B8692843
theorem B3341177 : Blo 1484062 3341177 := bstep (se 2 (by rfl) ⟨1252941, by rfl⟩ : syracuseStep 3341177 = 2505883) B2505883
theorem B24075215 : Blo 1484062 24075215 := bstep (se 1 (by rfl) ⟨18056411, by rfl⟩ : syracuseStep 24075215 = 36112823) B36112823
theorem B2506207 : Blo 1484062 2506207 := bstep (se 1 (by rfl) ⟨1879655, by rfl⟩ : syracuseStep 2506207 = 3759311) B3759311
theorem B12050063 : Blo 1484062 12050063 := bstep (se 1 (by rfl) ⟨9037547, by rfl⟩ : syracuseStep 12050063 = 18075095) B18075095
theorem B2227931 : Blo 1484062 2227931 := bstep (se 1 (by rfl) ⟨1670948, by rfl⟩ : syracuseStep 2227931 = 3341897) B3341897
theorem B21421871 : Blo 1484062 21421871 := bstep (se 1 (by rfl) ⟨16066403, by rfl⟩ : syracuseStep 21421871 = 32132807) B32132807
theorem B3342311 : Blo 1484062 3342311 := bstep (se 1 (by rfl) ⟨2506733, by rfl⟩ : syracuseStep 3342311 = 5013467) B5013467
theorem B2506855 : Blo 1484062 2506855 := bstep (se 1 (by rfl) ⟨1880141, by rfl⟩ : syracuseStep 2506855 = 3760283) B3760283
theorem B3342761 : Blo 1484062 3342761 := bstep (se 2 (by rfl) ⟨1253535, by rfl⟩ : syracuseStep 3342761 = 2507071) B2507071
theorem B2507611 : Blo 1484062 2507611 := bstep (se 1 (by rfl) ⟨1880708, by rfl⟩ : syracuseStep 2507611 = 3761417) B3761417
theorem B108602491 : Blo 1484062 108602491 := bstep (se 1 (by rfl) ⟨81451868, by rfl⟩ : syracuseStep 108602491 = 162903737) B162903737
theorem B24413687 : Blo 1484062 24413687 := bstep (se 1 (by rfl) ⟨18310265, by rfl⟩ : syracuseStep 24413687 = 36620531) B36620531
theorem B7521983 : Blo 1484062 7521983 := bstep (se 1 (by rfl) ⟨5641487, by rfl⟩ : syracuseStep 7521983 = 11282975) B11282975
theorem B7522145 : Blo 1484062 7522145 := bstep (se 2 (by rfl) ⟨2820804, by rfl⟩ : syracuseStep 7522145 = 5641609) B5641609
theorem B5638025 : Blo 1484062 5638025 := bstep (se 2 (by rfl) ⟨2114259, by rfl⟩ : syracuseStep 5638025 = 4228519) B4228519
theorem B13387675 : Blo 1484062 13387675 := bstep (se 1 (by rfl) ⟨10040756, by rfl⟩ : syracuseStep 13387675 = 20081513) B20081513
theorem B16050143 : Blo 1484062 16050143 := bstep (se 1 (by rfl) ⟨12037607, by rfl⟩ : syracuseStep 16050143 = 24075215) B24075215
theorem B146434337 : Blo 1484062 146434337 := bstep (se 2 (by rfl) ⟨54912876, by rfl⟩ : syracuseStep 146434337 = 109825753) B109825753
theorem B1485287 : Blo 1484062 1485287 := bstep (se 1 (by rfl) ⟨1113965, by rfl⟩ : syracuseStep 1485287 = 2227931) B2227931
theorem B14281247 : Blo 1484062 14281247 := bstep (se 1 (by rfl) ⟨10710935, by rfl⟩ : syracuseStep 14281247 = 21421871) B21421871
theorem B1485519 : Blo 1484062 1485519 := bstep (se 1 (by rfl) ⟨1114139, by rfl⟩ : syracuseStep 1485519 = 2228279) B2228279
theorem B2378479 : Blo 1484062 2378479 := bstep (se 1 (by rfl) ⟨1783859, by rfl⟩ : syracuseStep 2378479 = 3567719) B3567719
theorem B1485551 : Blo 1484062 1485551 := bstep (se 1 (by rfl) ⟨1114163, by rfl⟩ : syracuseStep 1485551 = 2228327) B2228327
theorem B4230137 : Blo 1484062 4230137 := bstep (se 2 (by rfl) ⟨1586301, by rfl⟩ : syracuseStep 4230137 = 3172603) B3172603
theorem B1879195 : Blo 1484062 1879195 := bstep (se 1 (by rfl) ⟨1409396, by rfl⟩ : syracuseStep 1879195 = 2818793) B2818793
theorem B5640137 : Blo 1484062 5640137 := bstep (se 2 (by rfl) ⟨2115051, by rfl⟩ : syracuseStep 5640137 = 4230103) B4230103
theorem B7516151 : Blo 1484062 7516151 := bstep (se 1 (by rfl) ⟨5637113, by rfl⟩ : syracuseStep 7516151 = 11274227) B11274227
theorem B17141797 : Blo 1484062 17141797 := bstep (se 4 (by rfl) ⟨1607043, by rfl⟩ : syracuseStep 17141797 = 3214087) B3214087
theorem B2256967 : Blo 1484062 2256967 := bstep (se 1 (by rfl) ⟨1692725, by rfl⟩ : syracuseStep 2256967 = 3385451) B3385451
theorem B12685693 : Blo 1484062 12685693 := bstep (se 3 (by rfl) ⟨2378567, by rfl⟩ : syracuseStep 12685693 = 4757135) B4757135
theorem B3568103 : Blo 1484062 3568103 := bstep (se 1 (by rfl) ⟨2676077, by rfl⟩ : syracuseStep 3568103 = 5352155) B5352155
theorem B8033375 : Blo 1484062 8033375 := bstep (se 1 (by rfl) ⟨6025031, by rfl⟩ : syracuseStep 8033375 = 12050063) B12050063
theorem B3340115 : Blo 1484062 3340115 := bstep (se 1 (by rfl) ⟨2505086, by rfl⟩ : syracuseStep 3340115 = 5010173) B5010173
theorem B2226239 : Blo 1484062 2226239 := bstep (se 1 (by rfl) ⟨1669679, by rfl⟩ : syracuseStep 2226239 = 3339359) B3339359
theorem B6019193 : Blo 1484062 6019193 := bstep (se 2 (by rfl) ⟨2257197, by rfl⟩ : syracuseStep 6019193 = 4514395) B4514395
theorem B36133067 : Blo 1484062 36133067 := bstep (se 1 (by rfl) ⟨27099800, by rfl⟩ : syracuseStep 36133067 = 54199601) B54199601
theorem B2226503 : Blo 1484062 2226503 := bstep (se 1 (by rfl) ⟨1669877, by rfl⟩ : syracuseStep 2226503 = 3339755) B3339755
theorem B6773183 : Blo 1484062 6773183 := bstep (se 1 (by rfl) ⟨5079887, by rfl⟩ : syracuseStep 6773183 = 10159775) B10159775
theorem B11279087 : Blo 1484062 11279087 := bstep (se 1 (by rfl) ⟨8459315, by rfl⟩ : syracuseStep 11279087 = 16918631) B16918631
theorem B2226983 : Blo 1484062 2226983 := bstep (se 1 (by rfl) ⟨1670237, by rfl⟩ : syracuseStep 2226983 = 3340475) B3340475
theorem B175946587 : Blo 1484062 175946587 := bstep (se 1 (by rfl) ⟨131959940, by rfl⟩ : syracuseStep 175946587 = 263919881) B263919881
theorem B42793919 : Blo 1484062 42793919 := bstep (se 1 (by rfl) ⟨32095439, by rfl⟩ : syracuseStep 42793919 = 64190879) B64190879
theorem B11271311 : Blo 1484062 11271311 := bstep (se 1 (by rfl) ⟨8453483, by rfl⟩ : syracuseStep 11271311 = 16906967) B16906967
theorem B2227451 : Blo 1484062 2227451 := bstep (se 1 (by rfl) ⟨1670588, by rfl⟩ : syracuseStep 2227451 = 3341177) B3341177
theorem B3341609 : Blo 1484062 3341609 := bstep (se 2 (by rfl) ⟨1253103, by rfl⟩ : syracuseStep 3341609 = 2506207) B2506207
theorem B3759443 : Blo 1484062 3759443 := bstep (se 1 (by rfl) ⟨2819582, by rfl⟩ : syracuseStep 3759443 = 5639165) B5639165
theorem B30907885 : Blo 1484062 30907885 := bstep (se 3 (by rfl) ⟨5795228, by rfl⟩ : syracuseStep 30907885 = 11590457) B11590457
theorem B2228207 : Blo 1484062 2228207 := bstep (se 1 (by rfl) ⟨1671155, by rfl⟩ : syracuseStep 2228207 = 3342311) B3342311
theorem B22855729 : Blo 1484062 22855729 := bstep (se 2 (by rfl) ⟨8570898, by rfl⟩ : syracuseStep 22855729 = 17141797) B17141797
theorem B3342473 : Blo 1484062 3342473 := bstep (se 2 (by rfl) ⟨1253427, by rfl⟩ : syracuseStep 3342473 = 2506855) B2506855
theorem B21422333 : Blo 1484062 21422333 := bstep (se 3 (by rfl) ⟨4016687, by rfl⟩ : syracuseStep 21422333 = 8033375) B8033375
theorem B2228507 : Blo 1484062 2228507 := bstep (se 1 (by rfl) ⟨1671380, by rfl⟩ : syracuseStep 2228507 = 3342761) B3342761
theorem B3171305 : Blo 1484062 3171305 := bstep (se 2 (by rfl) ⟨1189239, by rfl⟩ : syracuseStep 3171305 = 2378479) B2378479
theorem B3343481 : Blo 1484062 3343481 := bstep (se 2 (by rfl) ⟨1253805, by rfl⟩ : syracuseStep 3343481 = 2507611) B2507611
theorem B5014655 : Blo 1484062 5014655 := bstep (se 1 (by rfl) ⟨3760991, by rfl⟩ : syracuseStep 5014655 = 7521983) B7521983
theorem B5014763 : Blo 1484062 5014763 := bstep (se 1 (by rfl) ⟨3761072, by rfl⟩ : syracuseStep 5014763 = 7522145) B7522145
theorem B10700095 : Blo 1484062 10700095 := bstep (se 1 (by rfl) ⟨8025071, by rfl⟩ : syracuseStep 10700095 = 16050143) B16050143
theorem B1484159 : Blo 1484062 1484159 := bstep (se 1 (by rfl) ⟨1113119, by rfl⟩ : syracuseStep 1484159 = 2226239) B2226239
theorem B144803321 : Blo 1484062 144803321 := bstep (se 2 (by rfl) ⟨54301245, by rfl⟩ : syracuseStep 144803321 = 108602491) B108602491
theorem B1484335 : Blo 1484062 1484335 := bstep (se 1 (by rfl) ⟨1113251, by rfl⟩ : syracuseStep 1484335 = 2226503) B2226503
theorem B4515455 : Blo 1484062 4515455 := bstep (se 1 (by rfl) ⟨3386591, by rfl⟩ : syracuseStep 4515455 = 6773183) B6773183
theorem B9520831 : Blo 1484062 9520831 := bstep (se 1 (by rfl) ⟨7140623, by rfl⟩ : syracuseStep 9520831 = 14281247) B14281247
theorem B1484655 : Blo 1484062 1484655 := bstep (se 1 (by rfl) ⟨1113491, by rfl⟩ : syracuseStep 1484655 = 2226983) B2226983
theorem B2820091 : Blo 1484062 2820091 := bstep (se 1 (by rfl) ⟨2115068, by rfl⟩ : syracuseStep 2820091 = 4230137) B4230137
theorem B7514207 : Blo 1484062 7514207 := bstep (se 1 (by rfl) ⟨5635655, by rfl⟩ : syracuseStep 7514207 = 11271311) B11271311
theorem B1484967 : Blo 1484062 1484967 := bstep (se 1 (by rfl) ⟨1113725, by rfl⟩ : syracuseStep 1484967 = 2227451) B2227451
theorem B1485471 : Blo 1484062 1485471 := bstep (se 1 (by rfl) ⟨1114103, by rfl⟩ : syracuseStep 1485471 = 2228207) B2228207
theorem B2378735 : Blo 1484062 2378735 := bstep (se 1 (by rfl) ⟨1784051, by rfl⟩ : syracuseStep 2378735 = 3568103) B3568103
theorem B12037157 : Blo 1484062 12037157 := bstep (se 4 (by rfl) ⟨1128483, by rfl⟩ : syracuseStep 12037157 = 2256967) B2256967
theorem B24088711 : Blo 1484062 24088711 := bstep (se 1 (by rfl) ⟨18066533, by rfl⟩ : syracuseStep 24088711 = 36133067) B36133067
theorem B938381797 : Blo 1484062 938381797 := bstep (se 4 (by rfl) ⟨87973293, by rfl⟩ : syracuseStep 938381797 = 175946587) B175946587
theorem B28529279 : Blo 1484062 28529279 := bstep (se 1 (by rfl) ⟨21396959, by rfl⟩ : syracuseStep 28529279 = 42793919) B42793919
theorem B41210513 : Blo 1484062 41210513 := bstep (se 2 (by rfl) ⟨15453942, by rfl⟩ : syracuseStep 41210513 = 30907885) B30907885
theorem B5010767 : Blo 1484062 5010767 := bstep (se 1 (by rfl) ⟨3758075, by rfl⟩ : syracuseStep 5010767 = 7516151) B7516151
theorem B16914257 : Blo 1484062 16914257 := bstep (se 2 (by rfl) ⟨6342846, by rfl⟩ : syracuseStep 16914257 = 12685693) B12685693
theorem B16275791 : Blo 1484062 16275791 := bstep (se 1 (by rfl) ⟨12206843, by rfl⟩ : syracuseStep 16275791 = 24413687) B24413687
theorem B2226743 : Blo 1484062 2226743 := bstep (se 1 (by rfl) ⟨1670057, by rfl⟩ : syracuseStep 2226743 = 3340115) B3340115
theorem B3758683 : Blo 1484062 3758683 := bstep (se 1 (by rfl) ⟨2819012, by rfl⟩ : syracuseStep 3758683 = 5638025) B5638025
theorem B4012795 : Blo 1484062 4012795 := bstep (se 1 (by rfl) ⟨3009596, by rfl⟩ : syracuseStep 4012795 = 6019193) B6019193
theorem B97622891 : Blo 1484062 97622891 := bstep (se 1 (by rfl) ⟨73217168, by rfl⟩ : syracuseStep 97622891 = 146434337) B146434337
theorem B2505593 : Blo 1484062 2505593 := bstep (se 2 (by rfl) ⟨939597, by rfl⟩ : syracuseStep 2505593 = 1879195) B1879195
theorem B7519391 : Blo 1484062 7519391 := bstep (se 1 (by rfl) ⟨5639543, by rfl⟩ : syracuseStep 7519391 = 11279087) B11279087
theorem B2227739 : Blo 1484062 2227739 := bstep (se 1 (by rfl) ⟨1670804, by rfl⟩ : syracuseStep 2227739 = 3341609) B3341609
theorem B2506295 : Blo 1484062 2506295 := bstep (se 1 (by rfl) ⟨1879721, by rfl⟩ : syracuseStep 2506295 = 3759443) B3759443
theorem B17850233 : Blo 1484062 17850233 := bstep (se 2 (by rfl) ⟨6693837, by rfl⟩ : syracuseStep 17850233 = 13387675) B13387675
theorem B3760091 : Blo 1484062 3760091 := bstep (se 1 (by rfl) ⟨2820068, by rfl⟩ : syracuseStep 3760091 = 5640137) B5640137
theorem B30474305 : Blo 1484062 30474305 := bstep (se 2 (by rfl) ⟨11427864, by rfl⟩ : syracuseStep 30474305 = 22855729) B22855729
theorem B2228315 : Blo 1484062 2228315 := bstep (se 1 (by rfl) ⟨1671236, by rfl⟩ : syracuseStep 2228315 = 3342473) B3342473
theorem B2114203 : Blo 1484062 2114203 := bstep (se 1 (by rfl) ⟨1585652, by rfl⟩ : syracuseStep 2114203 = 3171305) B3171305
theorem B2228987 : Blo 1484062 2228987 := bstep (se 1 (by rfl) ⟨1671740, by rfl⟩ : syracuseStep 2228987 = 3343481) B3343481
theorem B3343103 : Blo 1484062 3343103 := bstep (se 1 (by rfl) ⟨2507327, by rfl⟩ : syracuseStep 3343103 = 5014655) B5014655
theorem B3343175 : Blo 1484062 3343175 := bstep (se 1 (by rfl) ⟨2507381, by rfl⟩ : syracuseStep 3343175 = 5014763) B5014763
theorem B5350393 : Blo 1484062 5350393 := bstep (se 2 (by rfl) ⟨2006397, by rfl⟩ : syracuseStep 5350393 = 4012795) B4012795
theorem B96535547 : Blo 1484062 96535547 := bstep (se 1 (by rfl) ⟨72401660, by rfl⟩ : syracuseStep 96535547 = 144803321) B144803321
theorem B1484495 : Blo 1484062 1484495 := bstep (se 1 (by rfl) ⟨1113371, by rfl⟩ : syracuseStep 1484495 = 2226743) B2226743
theorem B1485159 : Blo 1484062 1485159 := bstep (se 1 (by rfl) ⟨1113869, by rfl⟩ : syracuseStep 1485159 = 2227739) B2227739
theorem B3760121 : Blo 1484062 3760121 := bstep (se 2 (by rfl) ⟨1410045, by rfl⟩ : syracuseStep 3760121 = 2820091) B2820091
theorem B14281555 : Blo 1484062 14281555 := bstep (se 1 (by rfl) ⟨10711166, by rfl⟩ : syracuseStep 14281555 = 21422333) B21422333
theorem B1485671 : Blo 1484062 1485671 := bstep (se 1 (by rfl) ⟨1114253, by rfl⟩ : syracuseStep 1485671 = 2228507) B2228507
theorem B1251175729 : Blo 1484062 1251175729 := bstep (se 2 (by rfl) ⟨469190898, by rfl⟩ : syracuseStep 1251175729 = 938381797) B938381797
theorem B3010303 : Blo 1484062 3010303 := bstep (se 1 (by rfl) ⟨2257727, by rfl⟩ : syracuseStep 3010303 = 4515455) B4515455
theorem B11276171 : Blo 1484062 11276171 := bstep (se 1 (by rfl) ⟨8457128, by rfl⟩ : syracuseStep 11276171 = 16914257) B16914257
theorem B5009471 : Blo 1484062 5009471 := bstep (se 1 (by rfl) ⟨3757103, by rfl⟩ : syracuseStep 5009471 = 7514207) B7514207
theorem B10850527 : Blo 1484062 10850527 := bstep (se 1 (by rfl) ⟨8137895, by rfl⟩ : syracuseStep 10850527 = 16275791) B16275791
theorem B14266793 : Blo 1484062 14266793 := bstep (se 2 (by rfl) ⟨5350047, by rfl⟩ : syracuseStep 14266793 = 10700095) B10700095
theorem B65081927 : Blo 1484062 65081927 := bstep (se 1 (by rfl) ⟨48811445, by rfl⟩ : syracuseStep 65081927 = 97622891) B97622891
theorem B1585823 : Blo 1484062 1585823 := bstep (se 1 (by rfl) ⟨1189367, by rfl⟩ : syracuseStep 1585823 = 2378735) B2378735
theorem B8024771 : Blo 1484062 8024771 := bstep (se 1 (by rfl) ⟨6018578, by rfl⟩ : syracuseStep 8024771 = 12037157) B12037157
theorem B12694441 : Blo 1484062 12694441 := bstep (se 2 (by rfl) ⟨4760415, by rfl⟩ : syracuseStep 12694441 = 9520831) B9520831
theorem B47600621 : Blo 1484062 47600621 := bstep (se 3 (by rfl) ⟨8925116, by rfl⟩ : syracuseStep 47600621 = 17850233) B17850233
theorem B32118281 : Blo 1484062 32118281 := bstep (se 2 (by rfl) ⟨12044355, by rfl⟩ : syracuseStep 32118281 = 24088711) B24088711
theorem B19019519 : Blo 1484062 19019519 := bstep (se 1 (by rfl) ⟨14264639, by rfl⟩ : syracuseStep 19019519 = 28529279) B28529279
theorem B27473675 : Blo 1484062 27473675 := bstep (se 1 (by rfl) ⟨20605256, by rfl⟩ : syracuseStep 27473675 = 41210513) B41210513
theorem B5011577 : Blo 1484062 5011577 := bstep (se 2 (by rfl) ⟨1879341, by rfl⟩ : syracuseStep 5011577 = 3758683) B3758683
theorem B3340511 : Blo 1484062 3340511 := bstep (se 1 (by rfl) ⟨2505383, by rfl⟩ : syracuseStep 3340511 = 5010767) B5010767
theorem B1670395 : Blo 1484062 1670395 := bstep (se 1 (by rfl) ⟨1252796, by rfl⟩ : syracuseStep 1670395 = 2505593) B2505593
theorem B5012927 : Blo 1484062 5012927 := bstep (se 1 (by rfl) ⟨3759695, by rfl⟩ : syracuseStep 5012927 = 7519391) B7519391
theorem B1670863 : Blo 1484062 1670863 := bstep (se 1 (by rfl) ⟨1253147, by rfl⟩ : syracuseStep 1670863 = 2506295) B2506295
theorem B2506727 : Blo 1484062 2506727 := bstep (se 1 (by rfl) ⟨1880045, by rfl⟩ : syracuseStep 2506727 = 3760091) B3760091
theorem B20316203 : Blo 1484062 20316203 := bstep (se 1 (by rfl) ⟨15237152, by rfl⟩ : syracuseStep 20316203 = 30474305) B30474305
theorem B9511195 : Blo 1484062 9511195 := bstep (se 1 (by rfl) ⟨7133396, by rfl⟩ : syracuseStep 9511195 = 14266793) B14266793
theorem B14467369 : Blo 1484062 14467369 := bstep (se 2 (by rfl) ⟨5425263, by rfl⟩ : syracuseStep 14467369 = 10850527) B10850527
theorem B5349847 : Blo 1484062 5349847 := bstep (se 1 (by rfl) ⟨4012385, by rfl⟩ : syracuseStep 5349847 = 8024771) B8024771
theorem B2228735 : Blo 1484062 2228735 := bstep (se 1 (by rfl) ⟨1671551, by rfl⟩ : syracuseStep 2228735 = 3343103) B3343103
theorem B2228783 : Blo 1484062 2228783 := bstep (se 1 (by rfl) ⟨1671587, by rfl⟩ : syracuseStep 2228783 = 3343175) B3343175
theorem B64357031 : Blo 1484062 64357031 := bstep (se 1 (by rfl) ⟨48267773, by rfl⟩ : syracuseStep 64357031 = 96535547) B96535547
theorem B2818937 : Blo 1484062 2818937 := bstep (se 2 (by rfl) ⟨1057101, by rfl⟩ : syracuseStep 2818937 = 2114203) B2114203
theorem B16925921 : Blo 1484062 16925921 := bstep (se 2 (by rfl) ⟨6347220, by rfl⟩ : syracuseStep 16925921 = 12694441) B12694441
theorem B4228861 : Blo 1484062 4228861 := bstep (se 3 (by rfl) ⟨792911, by rfl⟩ : syracuseStep 4228861 = 1585823) B1585823
theorem B73263133 : Blo 1484062 73263133 := bstep (se 3 (by rfl) ⟨13736837, by rfl⟩ : syracuseStep 73263133 = 27473675) B27473675
theorem B28535429 : Blo 1484062 28535429 := bstep (se 4 (by rfl) ⟨2675196, by rfl⟩ : syracuseStep 28535429 = 5350393) B5350393
theorem B1485543 : Blo 1484062 1485543 := bstep (se 1 (by rfl) ⟨1114157, by rfl⟩ : syracuseStep 1485543 = 2228315) B2228315
theorem B1485991 : Blo 1484062 1485991 := bstep (se 1 (by rfl) ⟨1114493, by rfl⟩ : syracuseStep 1485991 = 2228987) B2228987
theorem B19042073 : Blo 1484062 19042073 := bstep (se 2 (by rfl) ⟨7140777, by rfl⟩ : syracuseStep 19042073 = 14281555) B14281555
theorem B173551805 : Blo 1484062 173551805 := bstep (se 3 (by rfl) ⟨32540963, by rfl⟩ : syracuseStep 173551805 = 65081927) B65081927
theorem B2506747 : Blo 1484062 2506747 := bstep (se 1 (by rfl) ⟨1880060, by rfl⟩ : syracuseStep 2506747 = 3760121) B3760121
theorem B7517447 : Blo 1484062 7517447 := bstep (se 1 (by rfl) ⟨5638085, by rfl⟩ : syracuseStep 7517447 = 11276171) B11276171
theorem B3339647 : Blo 1484062 3339647 := bstep (se 1 (by rfl) ⟨2504735, by rfl⟩ : syracuseStep 3339647 = 5009471) B5009471
theorem B31733747 : Blo 1484062 31733747 := bstep (se 1 (by rfl) ⟨23800310, by rfl⟩ : syracuseStep 31733747 = 47600621) B47600621
theorem B21412187 : Blo 1484062 21412187 := bstep (se 1 (by rfl) ⟨16059140, by rfl⟩ : syracuseStep 21412187 = 32118281) B32118281
theorem B12679679 : Blo 1484062 12679679 := bstep (se 1 (by rfl) ⟨9509759, by rfl⟩ : syracuseStep 12679679 = 19019519) B19019519
theorem B16054949 : Blo 1484062 16054949 := bstep (se 4 (by rfl) ⟨1505151, by rfl⟩ : syracuseStep 16054949 = 3010303) B3010303
theorem B3341051 : Blo 1484062 3341051 := bstep (se 1 (by rfl) ⟨2505788, by rfl⟩ : syracuseStep 3341051 = 5011577) B5011577
theorem B2227007 : Blo 1484062 2227007 := bstep (se 1 (by rfl) ⟨1670255, by rfl⟩ : syracuseStep 2227007 = 3340511) B3340511
theorem B2227193 : Blo 1484062 2227193 := bstep (se 2 (by rfl) ⟨835197, by rfl⟩ : syracuseStep 2227193 = 1670395) B1670395
theorem B1668234305 : Blo 1484062 1668234305 := bstep (se 2 (by rfl) ⟨625587864, by rfl⟩ : syracuseStep 1668234305 = 1251175729) B1251175729
theorem B2227817 : Blo 1484062 2227817 := bstep (se 2 (by rfl) ⟨835431, by rfl⟩ : syracuseStep 2227817 = 1670863) B1670863
theorem B3341951 : Blo 1484062 3341951 := bstep (se 1 (by rfl) ⟨2506463, by rfl⟩ : syracuseStep 3341951 = 5012927) B5012927
theorem B1671151 : Blo 1484062 1671151 := bstep (se 1 (by rfl) ⟨1253363, by rfl⟩ : syracuseStep 1671151 = 2506727) B2506727
theorem B12681593 : Blo 1484062 12681593 := bstep (se 2 (by rfl) ⟨4755597, by rfl⟩ : syracuseStep 12681593 = 9511195) B9511195
theorem B19023619 : Blo 1484062 19023619 := bstep (se 1 (by rfl) ⟨14267714, by rfl⟩ : syracuseStep 19023619 = 28535429) B28535429
theorem B1484671 : Blo 1484062 1484671 := bstep (se 1 (by rfl) ⟨1113503, by rfl⟩ : syracuseStep 1484671 = 2227007) B2227007
theorem B1484795 : Blo 1484062 1484795 := bstep (se 1 (by rfl) ⟨1113596, by rfl⟩ : syracuseStep 1484795 = 2227193) B2227193
theorem B1112156203 : Blo 1484062 1112156203 := bstep (se 1 (by rfl) ⟨834117152, by rfl⟩ : syracuseStep 1112156203 = 1668234305) B1668234305
theorem B5638481 : Blo 1484062 5638481 := bstep (se 2 (by rfl) ⟨2114430, by rfl⟩ : syracuseStep 5638481 = 4228861) B4228861
theorem B1485211 : Blo 1484062 1485211 := bstep (se 1 (by rfl) ⟨1113908, by rfl⟩ : syracuseStep 1485211 = 2227817) B2227817
theorem B13544135 : Blo 1484062 13544135 := bstep (se 1 (by rfl) ⟨10158101, by rfl⟩ : syracuseStep 13544135 = 20316203) B20316203
theorem B97684177 : Blo 1484062 97684177 := bstep (se 2 (by rfl) ⟨36631566, by rfl⟩ : syracuseStep 97684177 = 73263133) B73263133
theorem B1485823 : Blo 1484062 1485823 := bstep (se 1 (by rfl) ⟨1114367, by rfl⟩ : syracuseStep 1485823 = 2228735) B2228735
theorem B1485855 : Blo 1484062 1485855 := bstep (se 1 (by rfl) ⟨1114391, by rfl⟩ : syracuseStep 1485855 = 2228783) B2228783
theorem B42904687 : Blo 1484062 42904687 := bstep (se 1 (by rfl) ⟨32178515, by rfl⟩ : syracuseStep 42904687 = 64357031) B64357031
theorem B1879291 : Blo 1484062 1879291 := bstep (se 1 (by rfl) ⟨1409468, by rfl⟩ : syracuseStep 1879291 = 2818937) B2818937
theorem B11283947 : Blo 1484062 11283947 := bstep (se 1 (by rfl) ⟨8462960, by rfl⟩ : syracuseStep 11283947 = 16925921) B16925921
theorem B21155831 : Blo 1484062 21155831 := bstep (se 1 (by rfl) ⟨15866873, by rfl⟩ : syracuseStep 21155831 = 31733747) B31733747
theorem B14274791 : Blo 1484062 14274791 := bstep (se 1 (by rfl) ⟨10706093, by rfl⟩ : syracuseStep 14274791 = 21412187) B21412187
theorem B10703299 : Blo 1484062 10703299 := bstep (se 1 (by rfl) ⟨8027474, by rfl⟩ : syracuseStep 10703299 = 16054949) B16054949
theorem B12694715 : Blo 1484062 12694715 := bstep (se 1 (by rfl) ⟨9521036, by rfl⟩ : syracuseStep 12694715 = 19042073) B19042073
theorem B115701203 : Blo 1484062 115701203 := bstep (se 1 (by rfl) ⟨86775902, by rfl⟩ : syracuseStep 115701203 = 173551805) B173551805
theorem B19289825 : Blo 1484062 19289825 := bstep (se 2 (by rfl) ⟨7233684, by rfl⟩ : syracuseStep 19289825 = 14467369) B14467369
theorem B7133129 : Blo 1484062 7133129 := bstep (se 2 (by rfl) ⟨2674923, by rfl⟩ : syracuseStep 7133129 = 5349847) B5349847
theorem B5011631 : Blo 1484062 5011631 := bstep (se 1 (by rfl) ⟨3758723, by rfl⟩ : syracuseStep 5011631 = 7517447) B7517447
theorem B2226431 : Blo 1484062 2226431 := bstep (se 1 (by rfl) ⟨1669823, by rfl⟩ : syracuseStep 2226431 = 3339647) B3339647
theorem B8453119 : Blo 1484062 8453119 := bstep (se 1 (by rfl) ⟨6339839, by rfl⟩ : syracuseStep 8453119 = 12679679) B12679679
theorem B2227367 : Blo 1484062 2227367 := bstep (se 1 (by rfl) ⟨1670525, by rfl⟩ : syracuseStep 2227367 = 3341051) B3341051
theorem B2227967 : Blo 1484062 2227967 := bstep (se 1 (by rfl) ⟨1670975, by rfl⟩ : syracuseStep 2227967 = 3341951) B3341951
theorem B2228201 : Blo 1484062 2228201 := bstep (se 2 (by rfl) ⟨835575, by rfl⟩ : syracuseStep 2228201 = 1671151) B1671151
theorem B3342329 : Blo 1484062 3342329 := bstep (se 2 (by rfl) ⟨1253373, by rfl⟩ : syracuseStep 3342329 = 2506747) B2506747
theorem B1482874937 : Blo 1484062 1482874937 := bstep (se 2 (by rfl) ⟨556078101, by rfl⟩ : syracuseStep 1482874937 = 1112156203) B1112156203
theorem B8454395 : Blo 1484062 8454395 := bstep (se 1 (by rfl) ⟨6340796, by rfl⟩ : syracuseStep 8454395 = 12681593) B12681593
theorem B14271065 : Blo 1484062 14271065 := bstep (se 2 (by rfl) ⟨5351649, by rfl⟩ : syracuseStep 14271065 = 10703299) B10703299
theorem B8463143 : Blo 1484062 8463143 := bstep (se 1 (by rfl) ⟨6347357, by rfl⟩ : syracuseStep 8463143 = 12694715) B12694715
theorem B130245569 : Blo 1484062 130245569 := bstep (se 2 (by rfl) ⟨48842088, by rfl⟩ : syracuseStep 130245569 = 97684177) B97684177
theorem B57206249 : Blo 1484062 57206249 := bstep (se 2 (by rfl) ⟨21452343, by rfl⟩ : syracuseStep 57206249 = 42904687) B42904687
theorem B1484287 : Blo 1484062 1484287 := bstep (se 1 (by rfl) ⟨1113215, by rfl⟩ : syracuseStep 1484287 = 2226431) B2226431
theorem B9029423 : Blo 1484062 9029423 := bstep (se 1 (by rfl) ⟨6772067, by rfl⟩ : syracuseStep 9029423 = 13544135) B13544135
theorem B1484911 : Blo 1484062 1484911 := bstep (se 1 (by rfl) ⟨1113683, by rfl⟩ : syracuseStep 1484911 = 2227367) B2227367
theorem B7522631 : Blo 1484062 7522631 := bstep (se 1 (by rfl) ⟨5641973, by rfl⟩ : syracuseStep 7522631 = 11283947) B11283947
theorem B25364825 : Blo 1484062 25364825 := bstep (se 2 (by rfl) ⟨9511809, by rfl⟩ : syracuseStep 25364825 = 19023619) B19023619
theorem B1485311 : Blo 1484062 1485311 := bstep (se 1 (by rfl) ⟨1113983, by rfl⟩ : syracuseStep 1485311 = 2227967) B2227967
theorem B1485467 : Blo 1484062 1485467 := bstep (se 1 (by rfl) ⟨1114100, by rfl⟩ : syracuseStep 1485467 = 2228201) B2228201
theorem B4755419 : Blo 1484062 4755419 := bstep (se 1 (by rfl) ⟨3566564, by rfl⟩ : syracuseStep 4755419 = 7133129) B7133129
theorem B14103887 : Blo 1484062 14103887 := bstep (se 1 (by rfl) ⟨10577915, by rfl⟩ : syracuseStep 14103887 = 21155831) B21155831
theorem B9516527 : Blo 1484062 9516527 := bstep (se 1 (by rfl) ⟨7137395, by rfl⟩ : syracuseStep 9516527 = 14274791) B14274791
theorem B77134135 : Blo 1484062 77134135 := bstep (se 1 (by rfl) ⟨57850601, by rfl⟩ : syracuseStep 77134135 = 115701203) B115701203
theorem B12859883 : Blo 1484062 12859883 := bstep (se 1 (by rfl) ⟨9644912, by rfl⟩ : syracuseStep 12859883 = 19289825) B19289825
theorem B11270825 : Blo 1484062 11270825 := bstep (se 2 (by rfl) ⟨4226559, by rfl⟩ : syracuseStep 11270825 = 8453119) B8453119
theorem B3341087 : Blo 1484062 3341087 := bstep (se 1 (by rfl) ⟨2505815, by rfl⟩ : syracuseStep 3341087 = 5011631) B5011631
theorem B3758987 : Blo 1484062 3758987 := bstep (se 1 (by rfl) ⟨2819240, by rfl⟩ : syracuseStep 3758987 = 5638481) B5638481
theorem B2505721 : Blo 1484062 2505721 := bstep (se 2 (by rfl) ⟨939645, by rfl⟩ : syracuseStep 2505721 = 1879291) B1879291
theorem B2228219 : Blo 1484062 2228219 := bstep (se 1 (by rfl) ⟨1671164, by rfl⟩ : syracuseStep 2228219 = 3342329) B3342329
theorem B5636263 : Blo 1484062 5636263 := bstep (se 1 (by rfl) ⟨4227197, by rfl⟩ : syracuseStep 5636263 = 8454395) B8454395
theorem B5015087 : Blo 1484062 5015087 := bstep (se 1 (by rfl) ⟨3761315, by rfl⟩ : syracuseStep 5015087 = 7522631) B7522631
theorem B16909883 : Blo 1484062 16909883 := bstep (se 1 (by rfl) ⟨12682412, by rfl⟩ : syracuseStep 16909883 = 25364825) B25364825
theorem B7513883 : Blo 1484062 7513883 := bstep (se 1 (by rfl) ⟨5635412, by rfl⟩ : syracuseStep 7513883 = 11270825) B11270825
theorem B1485479 : Blo 1484062 1485479 := bstep (se 1 (by rfl) ⟨1114109, by rfl⟩ : syracuseStep 1485479 = 2228219) B2228219
theorem B9514043 : Blo 1484062 9514043 := bstep (se 1 (by rfl) ⟨7135532, by rfl⟩ : syracuseStep 9514043 = 14271065) B14271065
theorem B102845513 : Blo 1484062 102845513 := bstep (se 2 (by rfl) ⟨38567067, by rfl⟩ : syracuseStep 102845513 = 77134135) B77134135
theorem B86830379 : Blo 1484062 86830379 := bstep (se 1 (by rfl) ⟨65122784, by rfl⟩ : syracuseStep 86830379 = 130245569) B130245569
theorem B150441461 : Blo 1484062 150441461 := bstep (se 5 (by rfl) ⟨7051943, by rfl⟩ : syracuseStep 150441461 = 14103887) B14103887
theorem B38137499 : Blo 1484062 38137499 := bstep (se 1 (by rfl) ⟨28603124, by rfl⟩ : syracuseStep 38137499 = 57206249) B57206249
theorem B6344351 : Blo 1484062 6344351 := bstep (se 1 (by rfl) ⟨4758263, by rfl⟩ : syracuseStep 6344351 = 9516527) B9516527
theorem B8573255 : Blo 1484062 8573255 := bstep (se 1 (by rfl) ⟨6429941, by rfl⟩ : syracuseStep 8573255 = 12859883) B12859883
theorem B988583291 : Blo 1484062 988583291 := bstep (se 1 (by rfl) ⟨741437468, by rfl⟩ : syracuseStep 988583291 = 1482874937) B1482874937
theorem B5642095 : Blo 1484062 5642095 := bstep (se 1 (by rfl) ⟨4231571, by rfl⟩ : syracuseStep 5642095 = 8463143) B8463143
theorem B6019615 : Blo 1484062 6019615 := bstep (se 1 (by rfl) ⟨4514711, by rfl⟩ : syracuseStep 6019615 = 9029423) B9029423
theorem B3340961 : Blo 1484062 3340961 := bstep (se 2 (by rfl) ⟨1252860, by rfl⟩ : syracuseStep 3340961 = 2505721) B2505721
theorem B2227391 : Blo 1484062 2227391 := bstep (se 1 (by rfl) ⟨1670543, by rfl⟩ : syracuseStep 2227391 = 3341087) B3341087
theorem B2505991 : Blo 1484062 2505991 := bstep (se 1 (by rfl) ⟨1879493, by rfl⟩ : syracuseStep 2505991 = 3758987) B3758987
theorem B3170279 : Blo 1484062 3170279 := bstep (se 1 (by rfl) ⟨2377709, by rfl⟩ : syracuseStep 3170279 = 4755419) B4755419
theorem B32104613 : Blo 1484062 32104613 := bstep (se 4 (by rfl) ⟨3009807, by rfl⟩ : syracuseStep 32104613 = 6019615) B6019615
theorem B659055527 : Blo 1484062 659055527 := bstep (se 1 (by rfl) ⟨494291645, by rfl⟩ : syracuseStep 659055527 = 988583291) B988583291
theorem B3343391 : Blo 1484062 3343391 := bstep (se 1 (by rfl) ⟨2507543, by rfl⟩ : syracuseStep 3343391 = 5015087) B5015087
theorem B11273255 : Blo 1484062 11273255 := bstep (se 1 (by rfl) ⟨8454941, by rfl⟩ : syracuseStep 11273255 = 16909883) B16909883
theorem B6342695 : Blo 1484062 6342695 := bstep (se 1 (by rfl) ⟨4757021, by rfl⟩ : syracuseStep 6342695 = 9514043) B9514043
theorem B1484927 : Blo 1484062 1484927 := bstep (se 1 (by rfl) ⟨1113695, by rfl⟩ : syracuseStep 1484927 = 2227391) B2227391
theorem B57886919 : Blo 1484062 57886919 := bstep (se 1 (by rfl) ⟨43415189, by rfl⟩ : syracuseStep 57886919 = 86830379) B86830379
theorem B4229567 : Blo 1484062 4229567 := bstep (se 1 (by rfl) ⟨3172175, by rfl⟩ : syracuseStep 4229567 = 6344351) B6344351
theorem B7522793 : Blo 1484062 7522793 := bstep (se 2 (by rfl) ⟨2821047, by rfl⟩ : syracuseStep 7522793 = 5642095) B5642095
theorem B7515017 : Blo 1484062 7515017 := bstep (se 2 (by rfl) ⟨2818131, by rfl⟩ : syracuseStep 7515017 = 5636263) B5636263
theorem B5009255 : Blo 1484062 5009255 := bstep (se 1 (by rfl) ⟨3756941, by rfl⟩ : syracuseStep 5009255 = 7513883) B7513883
theorem B68563675 : Blo 1484062 68563675 := bstep (se 1 (by rfl) ⟨51422756, by rfl⟩ : syracuseStep 68563675 = 102845513) B102845513
theorem B25424999 : Blo 1484062 25424999 := bstep (se 1 (by rfl) ⟨19068749, by rfl⟩ : syracuseStep 25424999 = 38137499) B38137499
theorem B5715503 : Blo 1484062 5715503 := bstep (se 1 (by rfl) ⟨4286627, by rfl⟩ : syracuseStep 5715503 = 8573255) B8573255
theorem B3341321 : Blo 1484062 3341321 := bstep (se 2 (by rfl) ⟨1252995, by rfl⟩ : syracuseStep 3341321 = 2505991) B2505991
theorem B2227307 : Blo 1484062 2227307 := bstep (se 1 (by rfl) ⟨1670480, by rfl⟩ : syracuseStep 2227307 = 3340961) B3340961
theorem B100294307 : Blo 1484062 100294307 := bstep (se 1 (by rfl) ⟨75220730, by rfl⟩ : syracuseStep 100294307 = 150441461) B150441461
theorem B8454077 : Blo 1484062 8454077 := bstep (se 3 (by rfl) ⟨1585139, by rfl⟩ : syracuseStep 8454077 = 3170279) B3170279
theorem B439370351 : Blo 1484062 439370351 := bstep (se 1 (by rfl) ⟨329527763, by rfl⟩ : syracuseStep 439370351 = 659055527) B659055527
theorem B2228927 : Blo 1484062 2228927 := bstep (se 1 (by rfl) ⟨1671695, by rfl⟩ : syracuseStep 2228927 = 3343391) B3343391
theorem B16949999 : Blo 1484062 16949999 := bstep (se 1 (by rfl) ⟨12712499, by rfl⟩ : syracuseStep 16949999 = 25424999) B25424999
theorem B3810335 : Blo 1484062 3810335 := bstep (se 1 (by rfl) ⟨2857751, by rfl⟩ : syracuseStep 3810335 = 5715503) B5715503
theorem B4228463 : Blo 1484062 4228463 := bstep (se 1 (by rfl) ⟨3171347, by rfl⟩ : syracuseStep 4228463 = 6342695) B6342695
theorem B2819711 : Blo 1484062 2819711 := bstep (se 1 (by rfl) ⟨2114783, by rfl⟩ : syracuseStep 2819711 = 4229567) B4229567
theorem B5015195 : Blo 1484062 5015195 := bstep (se 1 (by rfl) ⟨3761396, by rfl⟩ : syracuseStep 5015195 = 7522793) B7522793
theorem B1484871 : Blo 1484062 1484871 := bstep (se 1 (by rfl) ⟨1113653, by rfl⟩ : syracuseStep 1484871 = 2227307) B2227307
theorem B7515503 : Blo 1484062 7515503 := bstep (se 1 (by rfl) ⟨5636627, by rfl⟩ : syracuseStep 7515503 = 11273255) B11273255
theorem B91418233 : Blo 1484062 91418233 := bstep (se 2 (by rfl) ⟨34281837, by rfl⟩ : syracuseStep 91418233 = 68563675) B68563675
theorem B5010011 : Blo 1484062 5010011 := bstep (se 1 (by rfl) ⟨3757508, by rfl⟩ : syracuseStep 5010011 = 7515017) B7515017
theorem B3339503 : Blo 1484062 3339503 := bstep (se 1 (by rfl) ⟨2504627, by rfl⟩ : syracuseStep 3339503 = 5009255) B5009255
theorem B21403075 : Blo 1484062 21403075 := bstep (se 1 (by rfl) ⟨16052306, by rfl⟩ : syracuseStep 21403075 = 32104613) B32104613
theorem B38591279 : Blo 1484062 38591279 := bstep (se 1 (by rfl) ⟨28943459, by rfl⟩ : syracuseStep 38591279 = 57886919) B57886919
theorem B2227547 : Blo 1484062 2227547 := bstep (se 1 (by rfl) ⟨1670660, by rfl⟩ : syracuseStep 2227547 = 3341321) B3341321
theorem B66862871 : Blo 1484062 66862871 := bstep (se 1 (by rfl) ⟨50147153, by rfl⟩ : syracuseStep 66862871 = 100294307) B100294307
theorem B5636051 : Blo 1484062 5636051 := bstep (se 1 (by rfl) ⟨4227038, by rfl⟩ : syracuseStep 5636051 = 8454077) B8454077
theorem B292913567 : Blo 1484062 292913567 := bstep (se 1 (by rfl) ⟨219685175, by rfl⟩ : syracuseStep 292913567 = 439370351) B439370351
theorem B2818975 : Blo 1484062 2818975 := bstep (se 1 (by rfl) ⟨2114231, by rfl⟩ : syracuseStep 2818975 = 4228463) B4228463
theorem B3343463 : Blo 1484062 3343463 := bstep (se 1 (by rfl) ⟨2507597, by rfl⟩ : syracuseStep 3343463 = 5015195) B5015195
theorem B121890977 : Blo 1484062 121890977 := bstep (se 2 (by rfl) ⟨45709116, by rfl⟩ : syracuseStep 121890977 = 91418233) B91418233
theorem B1485031 : Blo 1484062 1485031 := bstep (se 1 (by rfl) ⟨1113773, by rfl⟩ : syracuseStep 1485031 = 2227547) B2227547
theorem B44575247 : Blo 1484062 44575247 := bstep (se 1 (by rfl) ⟨33431435, by rfl⟩ : syracuseStep 44575247 = 66862871) B66862871
theorem B10160893 : Blo 1484062 10160893 := bstep (se 3 (by rfl) ⟨1905167, by rfl⟩ : syracuseStep 10160893 = 3810335) B3810335
theorem B1485951 : Blo 1484062 1485951 := bstep (se 1 (by rfl) ⟨1114463, by rfl⟩ : syracuseStep 1485951 = 2228927) B2228927
theorem B11299999 : Blo 1484062 11299999 := bstep (se 1 (by rfl) ⟨8474999, by rfl⟩ : syracuseStep 11299999 = 16949999) B16949999
theorem B25727519 : Blo 1484062 25727519 := bstep (se 1 (by rfl) ⟨19295639, by rfl⟩ : syracuseStep 25727519 = 38591279) B38591279
theorem B28537433 : Blo 1484062 28537433 := bstep (se 2 (by rfl) ⟨10701537, by rfl⟩ : syracuseStep 28537433 = 21403075) B21403075
theorem B5010335 : Blo 1484062 5010335 := bstep (se 1 (by rfl) ⟨3757751, by rfl⟩ : syracuseStep 5010335 = 7515503) B7515503
theorem B3757367 : Blo 1484062 3757367 := bstep (se 1 (by rfl) ⟨2818025, by rfl⟩ : syracuseStep 3757367 = 5636051) B5636051
theorem B3340007 : Blo 1484062 3340007 := bstep (se 1 (by rfl) ⟨2505005, by rfl⟩ : syracuseStep 3340007 = 5010011) B5010011
theorem B2226335 : Blo 1484062 2226335 := bstep (se 1 (by rfl) ⟨1669751, by rfl⟩ : syracuseStep 2226335 = 3339503) B3339503
theorem B7519229 : Blo 1484062 7519229 := bstep (se 3 (by rfl) ⟨1409855, by rfl⟩ : syracuseStep 7519229 = 2819711) B2819711
theorem B2228975 : Blo 1484062 2228975 := bstep (se 1 (by rfl) ⟨1671731, by rfl⟩ : syracuseStep 2228975 = 3343463) B3343463
theorem B1484223 : Blo 1484062 1484223 := bstep (se 1 (by rfl) ⟨1113167, by rfl⟩ : syracuseStep 1484223 = 2226335) B2226335
theorem B15066665 : Blo 1484062 15066665 := bstep (se 2 (by rfl) ⟨5649999, by rfl⟩ : syracuseStep 15066665 = 11299999) B11299999
theorem B195275711 : Blo 1484062 195275711 := bstep (se 1 (by rfl) ⟨146456783, by rfl⟩ : syracuseStep 195275711 = 292913567) B292913567
theorem B19024955 : Blo 1484062 19024955 := bstep (se 1 (by rfl) ⟨14268716, by rfl⟩ : syracuseStep 19024955 = 28537433) B28537433
theorem B81260651 : Blo 1484062 81260651 := bstep (se 1 (by rfl) ⟨60945488, by rfl⟩ : syracuseStep 81260651 = 121890977) B121890977
theorem B29716831 : Blo 1484062 29716831 := bstep (se 1 (by rfl) ⟨22287623, by rfl⟩ : syracuseStep 29716831 = 44575247) B44575247
theorem B17151679 : Blo 1484062 17151679 := bstep (se 1 (by rfl) ⟨12863759, by rfl⟩ : syracuseStep 17151679 = 25727519) B25727519
theorem B3340223 : Blo 1484062 3340223 := bstep (se 1 (by rfl) ⟨2505167, by rfl⟩ : syracuseStep 3340223 = 5010335) B5010335
theorem B2504911 : Blo 1484062 2504911 := bstep (se 1 (by rfl) ⟨1878683, by rfl⟩ : syracuseStep 2504911 = 3757367) B3757367
theorem B13547857 : Blo 1484062 13547857 := bstep (se 2 (by rfl) ⟨5080446, by rfl⟩ : syracuseStep 13547857 = 10160893) B10160893
theorem B2226671 : Blo 1484062 2226671 := bstep (se 1 (by rfl) ⟨1670003, by rfl⟩ : syracuseStep 2226671 = 3340007) B3340007
theorem B3758633 : Blo 1484062 3758633 := bstep (se 2 (by rfl) ⟨1409487, by rfl⟩ : syracuseStep 3758633 = 2818975) B2818975
theorem B5012819 : Blo 1484062 5012819 := bstep (se 1 (by rfl) ⟨3759614, by rfl⟩ : syracuseStep 5012819 = 7519229) B7519229
theorem B54173767 : Blo 1484062 54173767 := bstep (se 1 (by rfl) ⟨40630325, by rfl⟩ : syracuseStep 54173767 = 81260651) B81260651
theorem B18063809 : Blo 1484062 18063809 := bstep (se 2 (by rfl) ⟨6773928, by rfl⟩ : syracuseStep 18063809 = 13547857) B13547857
theorem B10044443 : Blo 1484062 10044443 := bstep (se 1 (by rfl) ⟨7533332, by rfl⟩ : syracuseStep 10044443 = 15066665) B15066665
theorem B1484447 : Blo 1484062 1484447 := bstep (se 1 (by rfl) ⟨1113335, by rfl⟩ : syracuseStep 1484447 = 2226671) B2226671
theorem B12683303 : Blo 1484062 12683303 := bstep (se 1 (by rfl) ⟨9512477, by rfl⟩ : syracuseStep 12683303 = 19024955) B19024955
theorem B1485983 : Blo 1484062 1485983 := bstep (se 1 (by rfl) ⟨1114487, by rfl⟩ : syracuseStep 1485983 = 2228975) B2228975
theorem B130183807 : Blo 1484062 130183807 := bstep (se 1 (by rfl) ⟨97637855, by rfl⟩ : syracuseStep 130183807 = 195275711) B195275711
theorem B22868905 : Blo 1484062 22868905 := bstep (se 2 (by rfl) ⟨8575839, by rfl⟩ : syracuseStep 22868905 = 17151679) B17151679
theorem B3339881 : Blo 1484062 3339881 := bstep (se 2 (by rfl) ⟨1252455, by rfl⟩ : syracuseStep 3339881 = 2504911) B2504911
theorem B39622441 : Blo 1484062 39622441 := bstep (se 2 (by rfl) ⟨14858415, by rfl⟩ : syracuseStep 39622441 = 29716831) B29716831
theorem B2226815 : Blo 1484062 2226815 := bstep (se 1 (by rfl) ⟨1670111, by rfl⟩ : syracuseStep 2226815 = 3340223) B3340223
theorem B2505755 : Blo 1484062 2505755 := bstep (se 1 (by rfl) ⟨1879316, by rfl⟩ : syracuseStep 2505755 = 3758633) B3758633
theorem B3341879 : Blo 1484062 3341879 := bstep (se 1 (by rfl) ⟨2506409, by rfl⟩ : syracuseStep 3341879 = 5012819) B5012819
theorem B12042539 : Blo 1484062 12042539 := bstep (se 1 (by rfl) ⟨9031904, by rfl⟩ : syracuseStep 12042539 = 18063809) B18063809
theorem B30491873 : Blo 1484062 30491873 := bstep (se 2 (by rfl) ⟨11434452, by rfl⟩ : syracuseStep 30491873 = 22868905) B22868905
theorem B8455535 : Blo 1484062 8455535 := bstep (se 1 (by rfl) ⟨6341651, by rfl⟩ : syracuseStep 8455535 = 12683303) B12683303
theorem B1484543 : Blo 1484062 1484543 := bstep (se 1 (by rfl) ⟨1113407, by rfl⟩ : syracuseStep 1484543 = 2226815) B2226815
theorem B72231689 : Blo 1484062 72231689 := bstep (se 2 (by rfl) ⟨27086883, by rfl⟩ : syracuseStep 72231689 = 54173767) B54173767
theorem B26785181 : Blo 1484062 26785181 := bstep (se 3 (by rfl) ⟨5022221, by rfl⟩ : syracuseStep 26785181 = 10044443) B10044443
theorem B173578409 : Blo 1484062 173578409 := bstep (se 2 (by rfl) ⟨65091903, by rfl⟩ : syracuseStep 173578409 = 130183807) B130183807
theorem B2226587 : Blo 1484062 2226587 := bstep (se 1 (by rfl) ⟨1669940, by rfl⟩ : syracuseStep 2226587 = 3339881) B3339881
theorem B1670503 : Blo 1484062 1670503 := bstep (se 1 (by rfl) ⟨1252877, by rfl⟩ : syracuseStep 1670503 = 2505755) B2505755
theorem B2227919 : Blo 1484062 2227919 := bstep (se 1 (by rfl) ⟨1670939, by rfl⟩ : syracuseStep 2227919 = 3341879) B3341879
theorem B52829921 : Blo 1484062 52829921 := bstep (se 2 (by rfl) ⟨19811220, by rfl⟩ : syracuseStep 52829921 = 39622441) B39622441
theorem B8028359 : Blo 1484062 8028359 := bstep (se 1 (by rfl) ⟨6021269, by rfl⟩ : syracuseStep 8028359 = 12042539) B12042539
theorem B5637023 : Blo 1484062 5637023 := bstep (se 1 (by rfl) ⟨4227767, by rfl⟩ : syracuseStep 5637023 = 8455535) B8455535
theorem B1484391 : Blo 1484062 1484391 := bstep (se 1 (by rfl) ⟨1113293, by rfl⟩ : syracuseStep 1484391 = 2226587) B2226587
theorem B48154459 : Blo 1484062 48154459 := bstep (se 1 (by rfl) ⟨36115844, by rfl⟩ : syracuseStep 48154459 = 72231689) B72231689
theorem B1485279 : Blo 1484062 1485279 := bstep (se 1 (by rfl) ⟨1113959, by rfl⟩ : syracuseStep 1485279 = 2227919) B2227919
theorem B35219947 : Blo 1484062 35219947 := bstep (se 1 (by rfl) ⟨26414960, by rfl⟩ : syracuseStep 35219947 = 52829921) B52829921
theorem B20327915 : Blo 1484062 20327915 := bstep (se 1 (by rfl) ⟨15245936, by rfl⟩ : syracuseStep 20327915 = 30491873) B30491873
theorem B17856787 : Blo 1484062 17856787 := bstep (se 1 (by rfl) ⟨13392590, by rfl⟩ : syracuseStep 17856787 = 26785181) B26785181
theorem B115718939 : Blo 1484062 115718939 := bstep (se 1 (by rfl) ⟨86789204, by rfl⟩ : syracuseStep 115718939 = 173578409) B173578409
theorem B2227337 : Blo 1484062 2227337 := bstep (se 2 (by rfl) ⟨835251, by rfl⟩ : syracuseStep 2227337 = 1670503) B1670503
theorem B77145959 : Blo 1484062 77145959 := bstep (se 1 (by rfl) ⟨57859469, by rfl⟩ : syracuseStep 77145959 = 115718939) B115718939
theorem B1484891 : Blo 1484062 1484891 := bstep (se 1 (by rfl) ⟨1113668, by rfl⟩ : syracuseStep 1484891 = 2227337) B2227337
theorem B13551943 : Blo 1484062 13551943 := bstep (se 1 (by rfl) ⟨10163957, by rfl⟩ : syracuseStep 13551943 = 20327915) B20327915
theorem B5352239 : Blo 1484062 5352239 := bstep (se 1 (by rfl) ⟨4014179, by rfl⟩ : syracuseStep 5352239 = 8028359) B8028359
theorem B23809049 : Blo 1484062 23809049 := bstep (se 2 (by rfl) ⟨8928393, by rfl⟩ : syracuseStep 23809049 = 17856787) B17856787
theorem B46959929 : Blo 1484062 46959929 := bstep (se 2 (by rfl) ⟨17609973, by rfl⟩ : syracuseStep 46959929 = 35219947) B35219947
theorem B64205945 : Blo 1484062 64205945 := bstep (se 2 (by rfl) ⟨24077229, by rfl⟩ : syracuseStep 64205945 = 48154459) B48154459
theorem B3758015 : Blo 1484062 3758015 := bstep (se 1 (by rfl) ⟨2818511, by rfl⟩ : syracuseStep 3758015 = 5637023) B5637023
theorem B42803963 : Blo 1484062 42803963 := bstep (se 1 (by rfl) ⟨32102972, by rfl⟩ : syracuseStep 42803963 = 64205945) B64205945
theorem B51430639 : Blo 1484062 51430639 := bstep (se 1 (by rfl) ⟨38572979, by rfl⟩ : syracuseStep 51430639 = 77145959) B77145959
theorem B3568159 : Blo 1484062 3568159 := bstep (se 1 (by rfl) ⟨2676119, by rfl⟩ : syracuseStep 3568159 = 5352239) B5352239
theorem B15872699 : Blo 1484062 15872699 := bstep (se 1 (by rfl) ⟨11904524, by rfl⟩ : syracuseStep 15872699 = 23809049) B23809049
theorem B31306619 : Blo 1484062 31306619 := bstep (se 1 (by rfl) ⟨23479964, by rfl⟩ : syracuseStep 31306619 = 46959929) B46959929
theorem B18069257 : Blo 1484062 18069257 := bstep (se 2 (by rfl) ⟨6775971, by rfl⟩ : syracuseStep 18069257 = 13551943) B13551943
theorem B2505343 : Blo 1484062 2505343 := bstep (se 1 (by rfl) ⟨1879007, by rfl⟩ : syracuseStep 2505343 = 3758015) B3758015
theorem B28535975 : Blo 1484062 28535975 := bstep (se 1 (by rfl) ⟨21401981, by rfl⟩ : syracuseStep 28535975 = 42803963) B42803963
theorem B12046171 : Blo 1484062 12046171 := bstep (se 1 (by rfl) ⟨9034628, by rfl⟩ : syracuseStep 12046171 = 18069257) B18069257
theorem B4757545 : Blo 1484062 4757545 := bstep (se 2 (by rfl) ⟨1784079, by rfl⟩ : syracuseStep 4757545 = 3568159) B3568159
theorem B3340457 : Blo 1484062 3340457 := bstep (se 2 (by rfl) ⟨1252671, by rfl⟩ : syracuseStep 3340457 = 2505343) B2505343
theorem B68574185 : Blo 1484062 68574185 := bstep (se 2 (by rfl) ⟨25715319, by rfl⟩ : syracuseStep 68574185 = 51430639) B51430639
theorem B42327197 : Blo 1484062 42327197 := bstep (se 3 (by rfl) ⟨7936349, by rfl⟩ : syracuseStep 42327197 = 15872699) B15872699
theorem B83484317 : Blo 1484062 83484317 := bstep (se 3 (by rfl) ⟨15653309, by rfl⟩ : syracuseStep 83484317 = 31306619) B31306619
theorem B19023983 : Blo 1484062 19023983 := bstep (se 1 (by rfl) ⟨14267987, by rfl⟩ : syracuseStep 19023983 = 28535975) B28535975
theorem B25373573 : Blo 1484062 25373573 := bstep (se 4 (by rfl) ⟨2378772, by rfl⟩ : syracuseStep 25373573 = 4757545) B4757545
theorem B45716123 : Blo 1484062 45716123 := bstep (se 1 (by rfl) ⟨34287092, by rfl⟩ : syracuseStep 45716123 = 68574185) B68574185
theorem B28218131 : Blo 1484062 28218131 := bstep (se 1 (by rfl) ⟨21163598, by rfl⟩ : syracuseStep 28218131 = 42327197) B42327197
theorem B16061561 : Blo 1484062 16061561 := bstep (se 2 (by rfl) ⟨6023085, by rfl⟩ : syracuseStep 16061561 = 12046171) B12046171
theorem B2226971 : Blo 1484062 2226971 := bstep (se 1 (by rfl) ⟨1670228, by rfl⟩ : syracuseStep 2226971 = 3340457) B3340457
theorem B222624845 : Blo 1484062 222624845 := bstep (se 3 (by rfl) ⟨41742158, by rfl⟩ : syracuseStep 222624845 = 83484317) B83484317
theorem B10707707 : Blo 1484062 10707707 := bstep (se 1 (by rfl) ⟨8030780, by rfl⟩ : syracuseStep 10707707 = 16061561) B16061561
theorem B12682655 : Blo 1484062 12682655 := bstep (se 1 (by rfl) ⟨9511991, by rfl⟩ : syracuseStep 12682655 = 19023983) B19023983
theorem B1484647 : Blo 1484062 1484647 := bstep (se 1 (by rfl) ⟨1113485, by rfl⟩ : syracuseStep 1484647 = 2226971) B2226971
theorem B148416563 : Blo 1484062 148416563 := bstep (se 1 (by rfl) ⟨111312422, by rfl⟩ : syracuseStep 148416563 = 222624845) B222624845
theorem B18812087 : Blo 1484062 18812087 := bstep (se 1 (by rfl) ⟨14109065, by rfl⟩ : syracuseStep 18812087 = 28218131) B28218131
theorem B121909661 : Blo 1484062 121909661 := bstep (se 3 (by rfl) ⟨22858061, by rfl⟩ : syracuseStep 121909661 = 45716123) B45716123
theorem B16915715 : Blo 1484062 16915715 := bstep (se 1 (by rfl) ⟨12686786, by rfl⟩ : syracuseStep 16915715 = 25373573) B25373573
theorem B81273107 : Blo 1484062 81273107 := bstep (se 1 (by rfl) ⟨60954830, by rfl⟩ : syracuseStep 81273107 = 121909661) B121909661
theorem B8455103 : Blo 1484062 8455103 := bstep (se 1 (by rfl) ⟨6341327, by rfl⟩ : syracuseStep 8455103 = 12682655) B12682655
theorem B98944375 : Blo 1484062 98944375 := bstep (se 1 (by rfl) ⟨74208281, by rfl⟩ : syracuseStep 98944375 = 148416563) B148416563
theorem B7138471 : Blo 1484062 7138471 := bstep (se 1 (by rfl) ⟨5353853, by rfl⟩ : syracuseStep 7138471 = 10707707) B10707707
theorem B11277143 : Blo 1484062 11277143 := bstep (se 1 (by rfl) ⟨8457857, by rfl⟩ : syracuseStep 11277143 = 16915715) B16915715
theorem B12541391 : Blo 1484062 12541391 := bstep (se 1 (by rfl) ⟨9406043, by rfl⟩ : syracuseStep 12541391 = 18812087) B18812087
theorem B54182071 : Blo 1484062 54182071 := bstep (se 1 (by rfl) ⟨40636553, by rfl⟩ : syracuseStep 54182071 = 81273107) B81273107
theorem B5636735 : Blo 1484062 5636735 := bstep (se 1 (by rfl) ⟨4227551, by rfl⟩ : syracuseStep 5636735 = 8455103) B8455103
theorem B131925833 : Blo 1484062 131925833 := bstep (se 2 (by rfl) ⟨49472187, by rfl⟩ : syracuseStep 131925833 = 98944375) B98944375
theorem B8360927 : Blo 1484062 8360927 := bstep (se 1 (by rfl) ⟨6270695, by rfl⟩ : syracuseStep 8360927 = 12541391) B12541391
theorem B7518095 : Blo 1484062 7518095 := bstep (se 1 (by rfl) ⟨5638571, by rfl⟩ : syracuseStep 7518095 = 11277143) B11277143
theorem B9517961 : Blo 1484062 9517961 := bstep (se 2 (by rfl) ⟨3569235, by rfl⟩ : syracuseStep 9517961 = 7138471) B7138471
theorem B87950555 : Blo 1484062 87950555 := bstep (se 1 (by rfl) ⟨65962916, by rfl⟩ : syracuseStep 87950555 = 131925833) B131925833
theorem B5573951 : Blo 1484062 5573951 := bstep (se 1 (by rfl) ⟨4180463, by rfl⟩ : syracuseStep 5573951 = 8360927) B8360927
theorem B6345307 : Blo 1484062 6345307 := bstep (se 1 (by rfl) ⟨4758980, by rfl⟩ : syracuseStep 6345307 = 9517961) B9517961
theorem B72242761 : Blo 1484062 72242761 := bstep (se 2 (by rfl) ⟨27091035, by rfl⟩ : syracuseStep 72242761 = 54182071) B54182071
theorem B3757823 : Blo 1484062 3757823 := bstep (se 1 (by rfl) ⟨2818367, by rfl⟩ : syracuseStep 3757823 = 5636735) B5636735
theorem B5012063 : Blo 1484062 5012063 := bstep (se 1 (by rfl) ⟨3759047, by rfl⟩ : syracuseStep 5012063 = 7518095) B7518095
theorem B96323681 : Blo 1484062 96323681 := bstep (se 2 (by rfl) ⟨36121380, by rfl⟩ : syracuseStep 96323681 = 72242761) B72242761
theorem B58633703 : Blo 1484062 58633703 := bstep (se 1 (by rfl) ⟨43975277, by rfl⟩ : syracuseStep 58633703 = 87950555) B87950555
theorem B3715967 : Blo 1484062 3715967 := bstep (se 1 (by rfl) ⟨2786975, by rfl⟩ : syracuseStep 3715967 = 5573951) B5573951
theorem B8460409 : Blo 1484062 8460409 := bstep (se 2 (by rfl) ⟨3172653, by rfl⟩ : syracuseStep 8460409 = 6345307) B6345307
theorem B2505215 : Blo 1484062 2505215 := bstep (se 1 (by rfl) ⟨1878911, by rfl⟩ : syracuseStep 2505215 = 3757823) B3757823
theorem B3341375 : Blo 1484062 3341375 := bstep (se 1 (by rfl) ⟨2506031, by rfl⟩ : syracuseStep 3341375 = 5012063) B5012063
theorem B11280545 : Blo 1484062 11280545 := bstep (se 2 (by rfl) ⟨4230204, by rfl⟩ : syracuseStep 11280545 = 8460409) B8460409
theorem B2477311 : Blo 1484062 2477311 := bstep (se 1 (by rfl) ⟨1857983, by rfl⟩ : syracuseStep 2477311 = 3715967) B3715967
theorem B39089135 : Blo 1484062 39089135 := bstep (se 1 (by rfl) ⟨29316851, by rfl⟩ : syracuseStep 39089135 = 58633703) B58633703
theorem B64215787 : Blo 1484062 64215787 := bstep (se 1 (by rfl) ⟨48161840, by rfl⟩ : syracuseStep 64215787 = 96323681) B96323681
theorem B1670143 : Blo 1484062 1670143 := bstep (se 1 (by rfl) ⟨1252607, by rfl⟩ : syracuseStep 1670143 = 2505215) B2505215
theorem B2227583 : Blo 1484062 2227583 := bstep (se 1 (by rfl) ⟨1670687, by rfl⟩ : syracuseStep 2227583 = 3341375) B3341375
theorem B7520363 : Blo 1484062 7520363 := bstep (se 1 (by rfl) ⟨5640272, by rfl⟩ : syracuseStep 7520363 = 11280545) B11280545
theorem B26059423 : Blo 1484062 26059423 := bstep (se 1 (by rfl) ⟨19544567, by rfl⟩ : syracuseStep 26059423 = 39089135) B39089135
theorem B1485055 : Blo 1484062 1485055 := bstep (se 1 (by rfl) ⟨1113791, by rfl⟩ : syracuseStep 1485055 = 2227583) B2227583
theorem B85621049 : Blo 1484062 85621049 := bstep (se 2 (by rfl) ⟨32107893, by rfl⟩ : syracuseStep 85621049 = 64215787) B64215787
theorem B13212325 : Blo 1484062 13212325 := bstep (se 4 (by rfl) ⟨1238655, by rfl⟩ : syracuseStep 13212325 = 2477311) B2477311
theorem B2226857 : Blo 1484062 2226857 := bstep (se 2 (by rfl) ⟨835071, by rfl⟩ : syracuseStep 2226857 = 1670143) B1670143
theorem B5013575 : Blo 1484062 5013575 := bstep (se 1 (by rfl) ⟨3760181, by rfl⟩ : syracuseStep 5013575 = 7520363) B7520363
theorem B1484571 : Blo 1484062 1484571 := bstep (se 1 (by rfl) ⟨1113428, by rfl⟩ : syracuseStep 1484571 = 2226857) B2226857
theorem B34745897 : Blo 1484062 34745897 := bstep (se 2 (by rfl) ⟨13029711, by rfl⟩ : syracuseStep 34745897 = 26059423) B26059423
theorem B70465733 : Blo 1484062 70465733 := bstep (se 4 (by rfl) ⟨6606162, by rfl⟩ : syracuseStep 70465733 = 13212325) B13212325
theorem B57080699 : Blo 1484062 57080699 := bstep (se 1 (by rfl) ⟨42810524, by rfl⟩ : syracuseStep 57080699 = 85621049) B85621049
theorem B3342383 : Blo 1484062 3342383 := bstep (se 1 (by rfl) ⟨2506787, by rfl⟩ : syracuseStep 3342383 = 5013575) B5013575
theorem B38053799 : Blo 1484062 38053799 := bstep (se 1 (by rfl) ⟨28540349, by rfl⟩ : syracuseStep 38053799 = 57080699) B57080699
theorem B46977155 : Blo 1484062 46977155 := bstep (se 1 (by rfl) ⟨35232866, by rfl⟩ : syracuseStep 46977155 = 70465733) B70465733
theorem B23163931 : Blo 1484062 23163931 := bstep (se 1 (by rfl) ⟨17372948, by rfl⟩ : syracuseStep 23163931 = 34745897) B34745897
theorem B2228255 : Blo 1484062 2228255 := bstep (se 1 (by rfl) ⟨1671191, by rfl⟩ : syracuseStep 2228255 = 3342383) B3342383
theorem B31318103 : Blo 1484062 31318103 := bstep (se 1 (by rfl) ⟨23488577, by rfl⟩ : syracuseStep 31318103 = 46977155) B46977155
theorem B30885241 : Blo 1484062 30885241 := bstep (se 2 (by rfl) ⟨11581965, by rfl⟩ : syracuseStep 30885241 = 23163931) B23163931
theorem B25369199 : Blo 1484062 25369199 := bstep (se 1 (by rfl) ⟨19026899, by rfl⟩ : syracuseStep 25369199 = 38053799) B38053799
theorem B1485503 : Blo 1484062 1485503 := bstep (se 1 (by rfl) ⟨1114127, by rfl⟩ : syracuseStep 1485503 = 2228255) B2228255
theorem B16912799 : Blo 1484062 16912799 := bstep (se 1 (by rfl) ⟨12684599, by rfl⟩ : syracuseStep 16912799 = 25369199) B25369199
theorem B20878735 : Blo 1484062 20878735 := bstep (se 1 (by rfl) ⟨15659051, by rfl⟩ : syracuseStep 20878735 = 31318103) B31318103
theorem B41180321 : Blo 1484062 41180321 := bstep (se 2 (by rfl) ⟨15442620, by rfl⟩ : syracuseStep 41180321 = 30885241) B30885241
theorem B27838313 : Blo 1484062 27838313 := bstep (se 2 (by rfl) ⟨10439367, by rfl⟩ : syracuseStep 27838313 = 20878735) B20878735
theorem B27453547 : Blo 1484062 27453547 := bstep (se 1 (by rfl) ⟨20590160, by rfl⟩ : syracuseStep 27453547 = 41180321) B41180321
theorem B11275199 : Blo 1484062 11275199 := bstep (se 1 (by rfl) ⟨8456399, by rfl⟩ : syracuseStep 11275199 = 16912799) B16912799
theorem B36604729 : Blo 1484062 36604729 := bstep (se 2 (by rfl) ⟨13726773, by rfl⟩ : syracuseStep 36604729 = 27453547) B27453547
theorem B18558875 : Blo 1484062 18558875 := bstep (se 1 (by rfl) ⟨13919156, by rfl⟩ : syracuseStep 18558875 = 27838313) B27838313
theorem B7516799 : Blo 1484062 7516799 := bstep (se 1 (by rfl) ⟨5637599, by rfl⟩ : syracuseStep 7516799 = 11275199) B11275199
theorem B195225221 : Blo 1484062 195225221 := bstep (se 4 (by rfl) ⟨18302364, by rfl⟩ : syracuseStep 195225221 = 36604729) B36604729
theorem B12372583 : Blo 1484062 12372583 := bstep (se 1 (by rfl) ⟨9279437, by rfl⟩ : syracuseStep 12372583 = 18558875) B18558875
theorem B5011199 : Blo 1484062 5011199 := bstep (se 1 (by rfl) ⟨3758399, by rfl⟩ : syracuseStep 5011199 = 7516799) B7516799
theorem B130150147 : Blo 1484062 130150147 := bstep (se 1 (by rfl) ⟨97612610, by rfl⟩ : syracuseStep 130150147 = 195225221) B195225221
theorem B16496777 : Blo 1484062 16496777 := bstep (se 2 (by rfl) ⟨6186291, by rfl⟩ : syracuseStep 16496777 = 12372583) B12372583
theorem B3340799 : Blo 1484062 3340799 := bstep (se 1 (by rfl) ⟨2505599, by rfl⟩ : syracuseStep 3340799 = 5011199) B5011199
theorem B173533529 : Blo 1484062 173533529 := bstep (se 2 (by rfl) ⟨65075073, by rfl⟩ : syracuseStep 173533529 = 130150147) B130150147
theorem B10997851 : Blo 1484062 10997851 := bstep (se 1 (by rfl) ⟨8248388, by rfl⟩ : syracuseStep 10997851 = 16496777) B16496777
theorem B2227199 : Blo 1484062 2227199 := bstep (se 1 (by rfl) ⟨1670399, by rfl⟩ : syracuseStep 2227199 = 3340799) B3340799
theorem B14663801 : Blo 1484062 14663801 := bstep (se 2 (by rfl) ⟨5498925, by rfl⟩ : syracuseStep 14663801 = 10997851) B10997851
theorem B115689019 : Blo 1484062 115689019 := bstep (se 1 (by rfl) ⟨86766764, by rfl⟩ : syracuseStep 115689019 = 173533529) B173533529
theorem B1484799 : Blo 1484062 1484799 := bstep (se 1 (by rfl) ⟨1113599, by rfl⟩ : syracuseStep 1484799 = 2227199) B2227199
theorem B39103469 : Blo 1484062 39103469 := bstep (se 3 (by rfl) ⟨7331900, by rfl⟩ : syracuseStep 39103469 = 14663801) B14663801
theorem B154252025 : Blo 1484062 154252025 := bstep (se 2 (by rfl) ⟨57844509, by rfl⟩ : syracuseStep 154252025 = 115689019) B115689019
theorem B102834683 : Blo 1484062 102834683 := bstep (se 1 (by rfl) ⟨77126012, by rfl⟩ : syracuseStep 102834683 = 154252025) B154252025
theorem B26068979 : Blo 1484062 26068979 := bstep (se 1 (by rfl) ⟨19551734, by rfl⟩ : syracuseStep 26068979 = 39103469) B39103469
theorem B17379319 : Blo 1484062 17379319 := bstep (se 1 (by rfl) ⟨13034489, by rfl⟩ : syracuseStep 17379319 = 26068979) B26068979
theorem B68556455 : Blo 1484062 68556455 := bstep (se 1 (by rfl) ⟨51417341, by rfl⟩ : syracuseStep 68556455 = 102834683) B102834683
theorem B45704303 : Blo 1484062 45704303 := bstep (se 1 (by rfl) ⟨34278227, by rfl⟩ : syracuseStep 45704303 = 68556455) B68556455
theorem B23172425 : Blo 1484062 23172425 := bstep (se 2 (by rfl) ⟨8689659, by rfl⟩ : syracuseStep 23172425 = 17379319) B17379319
theorem B30469535 : Blo 1484062 30469535 := bstep (se 1 (by rfl) ⟨22852151, by rfl⟩ : syracuseStep 30469535 = 45704303) B45704303
theorem B15448283 : Blo 1484062 15448283 := bstep (se 1 (by rfl) ⟨11586212, by rfl⟩ : syracuseStep 15448283 = 23172425) B23172425
theorem B10298855 : Blo 1484062 10298855 := bstep (se 1 (by rfl) ⟨7724141, by rfl⟩ : syracuseStep 10298855 = 15448283) B15448283
theorem B20313023 : Blo 1484062 20313023 := bstep (se 1 (by rfl) ⟨15234767, by rfl⟩ : syracuseStep 20313023 = 30469535) B30469535
theorem B6865903 : Blo 1484062 6865903 := bstep (se 1 (by rfl) ⟨5149427, by rfl⟩ : syracuseStep 6865903 = 10298855) B10298855
theorem B54168061 : Blo 1484062 54168061 := bstep (se 3 (by rfl) ⟨10156511, by rfl⟩ : syracuseStep 54168061 = 20313023) B20313023
theorem B72224081 : Blo 1484062 72224081 := bstep (se 2 (by rfl) ⟨27084030, by rfl⟩ : syracuseStep 72224081 = 54168061) B54168061
theorem B36618149 : Blo 1484062 36618149 := bstep (se 4 (by rfl) ⟨3432951, by rfl⟩ : syracuseStep 36618149 = 6865903) B6865903
theorem B48149387 : Blo 1484062 48149387 := bstep (se 1 (by rfl) ⟨36112040, by rfl⟩ : syracuseStep 48149387 = 72224081) B72224081
theorem B24412099 : Blo 1484062 24412099 := bstep (se 1 (by rfl) ⟨18309074, by rfl⟩ : syracuseStep 24412099 = 36618149) B36618149
theorem B32549465 : Blo 1484062 32549465 := bstep (se 2 (by rfl) ⟨12206049, by rfl⟩ : syracuseStep 32549465 = 24412099) B24412099
theorem B32099591 : Blo 1484062 32099591 := bstep (se 1 (by rfl) ⟨24074693, by rfl⟩ : syracuseStep 32099591 = 48149387) B48149387
theorem B21399727 : Blo 1484062 21399727 := bstep (se 1 (by rfl) ⟨16049795, by rfl⟩ : syracuseStep 21399727 = 32099591) B32099591
theorem B86798573 : Blo 1484062 86798573 := bstep (se 3 (by rfl) ⟨16274732, by rfl⟩ : syracuseStep 86798573 = 32549465) B32549465
theorem B28532969 : Blo 1484062 28532969 := bstep (se 2 (by rfl) ⟨10699863, by rfl⟩ : syracuseStep 28532969 = 21399727) B21399727
theorem B57865715 : Blo 1484062 57865715 := bstep (se 1 (by rfl) ⟨43399286, by rfl⟩ : syracuseStep 57865715 = 86798573) B86798573
theorem B19021979 : Blo 1484062 19021979 := bstep (se 1 (by rfl) ⟨14266484, by rfl⟩ : syracuseStep 19021979 = 28532969) B28532969
theorem B38577143 : Blo 1484062 38577143 := bstep (se 1 (by rfl) ⟨28932857, by rfl⟩ : syracuseStep 38577143 = 57865715) B57865715
theorem B12681319 : Blo 1484062 12681319 := bstep (se 1 (by rfl) ⟨9510989, by rfl⟩ : syracuseStep 12681319 = 19021979) B19021979
theorem B25718095 : Blo 1484062 25718095 := bstep (se 1 (by rfl) ⟨19288571, by rfl⟩ : syracuseStep 25718095 = 38577143) B38577143
theorem B16908425 : Blo 1484062 16908425 := bstep (se 2 (by rfl) ⟨6340659, by rfl⟩ : syracuseStep 16908425 = 12681319) B12681319
theorem B34290793 : Blo 1484062 34290793 := bstep (se 2 (by rfl) ⟨12859047, by rfl⟩ : syracuseStep 34290793 = 25718095) B25718095
theorem B11272283 : Blo 1484062 11272283 := bstep (se 1 (by rfl) ⟨8454212, by rfl⟩ : syracuseStep 11272283 = 16908425) B16908425
theorem B45721057 : Blo 1484062 45721057 := bstep (se 2 (by rfl) ⟨17145396, by rfl⟩ : syracuseStep 45721057 = 34290793) B34290793
theorem B7514855 : Blo 1484062 7514855 := bstep (se 1 (by rfl) ⟨5636141, by rfl⟩ : syracuseStep 7514855 = 11272283) B11272283
theorem B60961409 : Blo 1484062 60961409 := bstep (se 2 (by rfl) ⟨22860528, by rfl⟩ : syracuseStep 60961409 = 45721057) B45721057
theorem B40640939 : Blo 1484062 40640939 := bstep (se 1 (by rfl) ⟨30480704, by rfl⟩ : syracuseStep 40640939 = 60961409) B60961409
theorem B5009903 : Blo 1484062 5009903 := bstep (se 1 (by rfl) ⟨3757427, by rfl⟩ : syracuseStep 5009903 = 7514855) B7514855
theorem B27093959 : Blo 1484062 27093959 := bstep (se 1 (by rfl) ⟨20320469, by rfl⟩ : syracuseStep 27093959 = 40640939) B40640939
theorem B3339935 : Blo 1484062 3339935 := bstep (se 1 (by rfl) ⟨2504951, by rfl⟩ : syracuseStep 3339935 = 5009903) B5009903
theorem B2226623 : Blo 1484062 2226623 := bstep (se 1 (by rfl) ⟨1669967, by rfl⟩ : syracuseStep 2226623 = 3339935) B3339935
theorem B18062639 : Blo 1484062 18062639 := bstep (se 1 (by rfl) ⟨13546979, by rfl⟩ : syracuseStep 18062639 = 27093959) B27093959
theorem B1484415 : Blo 1484062 1484415 := bstep (se 1 (by rfl) ⟨1113311, by rfl⟩ : syracuseStep 1484415 = 2226623) B2226623
theorem B12041759 : Blo 1484062 12041759 := bstep (se 1 (by rfl) ⟨9031319, by rfl⟩ : syracuseStep 12041759 = 18062639) B18062639
theorem B8027839 : Blo 1484062 8027839 := bstep (se 1 (by rfl) ⟨6020879, by rfl⟩ : syracuseStep 8027839 = 12041759) B12041759
theorem B42815141 : Blo 1484062 42815141 := bstep (se 4 (by rfl) ⟨4013919, by rfl⟩ : syracuseStep 42815141 = 8027839) B8027839
theorem B28543427 : Blo 1484062 28543427 := bstep (se 1 (by rfl) ⟨21407570, by rfl⟩ : syracuseStep 28543427 = 42815141) B42815141
theorem B19028951 : Blo 1484062 19028951 := bstep (se 1 (by rfl) ⟨14271713, by rfl⟩ : syracuseStep 19028951 = 28543427) B28543427
theorem B12685967 : Blo 1484062 12685967 := bstep (se 1 (by rfl) ⟨9514475, by rfl⟩ : syracuseStep 12685967 = 19028951) B19028951
theorem B8457311 : Blo 1484062 8457311 := bstep (se 1 (by rfl) ⟨6342983, by rfl⟩ : syracuseStep 8457311 = 12685967) B12685967
theorem B5638207 : Blo 1484062 5638207 := bstep (se 1 (by rfl) ⟨4228655, by rfl⟩ : syracuseStep 5638207 = 8457311) B8457311
theorem B7517609 : Blo 1484062 7517609 := bstep (se 2 (by rfl) ⟨2819103, by rfl⟩ : syracuseStep 7517609 = 5638207) B5638207
theorem B5011739 : Blo 1484062 5011739 := bstep (se 1 (by rfl) ⟨3758804, by rfl⟩ : syracuseStep 5011739 = 7517609) B7517609
theorem B3341159 : Blo 1484062 3341159 := bstep (se 1 (by rfl) ⟨2505869, by rfl⟩ : syracuseStep 3341159 = 5011739) B5011739
theorem B2227439 : Blo 1484062 2227439 := bstep (se 1 (by rfl) ⟨1670579, by rfl⟩ : syracuseStep 2227439 = 3341159) B3341159
theorem B1484959 : Blo 1484062 1484959 := bstep (se 1 (by rfl) ⟨1113719, by rfl⟩ : syracuseStep 1484959 = 2227439) B2227439

theorem C0 (j : ℕ) (h1 : 371015 ≤ j) (h2 : j ≤ 371514) : Blo 1484062 (4 * j + 3) := by
  interval_cases j
  · exact B1484063
  · exact B1484067
  · exact B1484071
  · exact B1484075
  · exact B1484079
  · exact B1484083
  · exact B1484087
  · exact B1484091
  · exact B1484095
  · exact B1484099
  · exact B1484103
  · exact B1484107
  · exact B1484111
  · exact B1484115
  · exact B1484119
  · exact B1484123
  · exact B1484127
  · exact B1484131
  · exact B1484135
  · exact B1484139
  · exact B1484143
  · exact B1484147
  · exact B1484151
  · exact B1484155
  · exact B1484159
  · exact B1484163
  · exact B1484167
  · exact B1484171
  · exact B1484175
  · exact B1484179
  · exact B1484183
  · exact B1484187
  · exact B1484191
  · exact B1484195
  · exact B1484199
  · exact B1484203
  · exact B1484207
  · exact B1484211
  · exact B1484215
  · exact B1484219
  · exact B1484223
  · exact B1484227
  · exact B1484231
  · exact B1484235
  · exact B1484239
  · exact B1484243
  · exact B1484247
  · exact B1484251
  · exact B1484255
  · exact B1484259
  · exact B1484263
  · exact B1484267
  · exact B1484271
  · exact B1484275
  · exact B1484279
  · exact B1484283
  · exact B1484287
  · exact B1484291
  · exact B1484295
  · exact B1484299
  · exact B1484303
  · exact B1484307
  · exact B1484311
  · exact B1484315
  · exact B1484319
  · exact B1484323
  · exact B1484327
  · exact B1484331
  · exact B1484335
  · exact B1484339
  · exact B1484343
  · exact B1484347
  · exact B1484351
  · exact B1484355
  · exact B1484359
  · exact B1484363
  · exact B1484367
  · exact B1484371
  · exact B1484375
  · exact B1484379
  · exact B1484383
  · exact B1484387
  · exact B1484391
  · exact B1484395
  · exact B1484399
  · exact B1484403
  · exact B1484407
  · exact B1484411
  · exact B1484415
  · exact B1484419
  · exact B1484423
  · exact B1484427
  · exact B1484431
  · exact B1484435
  · exact B1484439
  · exact B1484443
  · exact B1484447
  · exact B1484451
  · exact B1484455
  · exact B1484459
  · exact B1484463
  · exact B1484467
  · exact B1484471
  · exact B1484475
  · exact B1484479
  · exact B1484483
  · exact B1484487
  · exact B1484491
  · exact B1484495
  · exact B1484499
  · exact B1484503
  · exact B1484507
  · exact B1484511
  · exact B1484515
  · exact B1484519
  · exact B1484523
  · exact B1484527
  · exact B1484531
  · exact B1484535
  · exact B1484539
  · exact B1484543
  · exact B1484547
  · exact B1484551
  · exact B1484555
  · exact B1484559
  · exact B1484563
  · exact B1484567
  · exact B1484571
  · exact B1484575
  · exact B1484579
  · exact B1484583
  · exact B1484587
  · exact B1484591
  · exact B1484595
  · exact B1484599
  · exact B1484603
  · exact B1484607
  · exact B1484611
  · exact B1484615
  · exact B1484619
  · exact B1484623
  · exact B1484627
  · exact B1484631
  · exact B1484635
  · exact B1484639
  · exact B1484643
  · exact B1484647
  · exact B1484651
  · exact B1484655
  · exact B1484659
  · exact B1484663
  · exact B1484667
  · exact B1484671
  · exact B1484675
  · exact B1484679
  · exact B1484683
  · exact B1484687
  · exact B1484691
  · exact B1484695
  · exact B1484699
  · exact B1484703
  · exact B1484707
  · exact B1484711
  · exact B1484715
  · exact B1484719
  · exact B1484723
  · exact B1484727
  · exact B1484731
  · exact B1484735
  · exact B1484739
  · exact B1484743
  · exact B1484747
  · exact B1484751
  · exact B1484755
  · exact B1484759
  · exact B1484763
  · exact B1484767
  · exact B1484771
  · exact B1484775
  · exact B1484779
  · exact B1484783
  · exact B1484787
  · exact B1484791
  · exact B1484795
  · exact B1484799
  · exact B1484803
  · exact B1484807
  · exact B1484811
  · exact B1484815
  · exact B1484819
  · exact B1484823
  · exact B1484827
  · exact B1484831
  · exact B1484835
  · exact B1484839
  · exact B1484843
  · exact B1484847
  · exact B1484851
  · exact B1484855
  · exact B1484859
  · exact B1484863
  · exact B1484867
  · exact B1484871
  · exact B1484875
  · exact B1484879
  · exact B1484883
  · exact B1484887
  · exact B1484891
  · exact B1484895
  · exact B1484899
  · exact B1484903
  · exact B1484907
  · exact B1484911
  · exact B1484915
  · exact B1484919
  · exact B1484923
  · exact B1484927
  · exact B1484931
  · exact B1484935
  · exact B1484939
  · exact B1484943
  · exact B1484947
  · exact B1484951
  · exact B1484955
  · exact B1484959
  · exact B1484963
  · exact B1484967
  · exact B1484971
  · exact B1484975
  · exact B1484979
  · exact B1484983
  · exact B1484987
  · exact B1484991
  · exact B1484995
  · exact B1484999
  · exact B1485003
  · exact B1485007
  · exact B1485011
  · exact B1485015
  · exact B1485019
  · exact B1485023
  · exact B1485027
  · exact B1485031
  · exact B1485035
  · exact B1485039
  · exact B1485043
  · exact B1485047
  · exact B1485051
  · exact B1485055
  · exact B1485059
  · exact B1485063
  · exact B1485067
  · exact B1485071
  · exact B1485075
  · exact B1485079
  · exact B1485083
  · exact B1485087
  · exact B1485091
  · exact B1485095
  · exact B1485099
  · exact B1485103
  · exact B1485107
  · exact B1485111
  · exact B1485115
  · exact B1485119
  · exact B1485123
  · exact B1485127
  · exact B1485131
  · exact B1485135
  · exact B1485139
  · exact B1485143
  · exact B1485147
  · exact B1485151
  · exact B1485155
  · exact B1485159
  · exact B1485163
  · exact B1485167
  · exact B1485171
  · exact B1485175
  · exact B1485179
  · exact B1485183
  · exact B1485187
  · exact B1485191
  · exact B1485195
  · exact B1485199
  · exact B1485203
  · exact B1485207
  · exact B1485211
  · exact B1485215
  · exact B1485219
  · exact B1485223
  · exact B1485227
  · exact B1485231
  · exact B1485235
  · exact B1485239
  · exact B1485243
  · exact B1485247
  · exact B1485251
  · exact B1485255
  · exact B1485259
  · exact B1485263
  · exact B1485267
  · exact B1485271
  · exact B1485275
  · exact B1485279
  · exact B1485283
  · exact B1485287
  · exact B1485291
  · exact B1485295
  · exact B1485299
  · exact B1485303
  · exact B1485307
  · exact B1485311
  · exact B1485315
  · exact B1485319
  · exact B1485323
  · exact B1485327
  · exact B1485331
  · exact B1485335
  · exact B1485339
  · exact B1485343
  · exact B1485347
  · exact B1485351
  · exact B1485355
  · exact B1485359
  · exact B1485363
  · exact B1485367
  · exact B1485371
  · exact B1485375
  · exact B1485379
  · exact B1485383
  · exact B1485387
  · exact B1485391
  · exact B1485395
  · exact B1485399
  · exact B1485403
  · exact B1485407
  · exact B1485411
  · exact B1485415
  · exact B1485419
  · exact B1485423
  · exact B1485427
  · exact B1485431
  · exact B1485435
  · exact B1485439
  · exact B1485443
  · exact B1485447
  · exact B1485451
  · exact B1485455
  · exact B1485459
  · exact B1485463
  · exact B1485467
  · exact B1485471
  · exact B1485475
  · exact B1485479
  · exact B1485483
  · exact B1485487
  · exact B1485491
  · exact B1485495
  · exact B1485499
  · exact B1485503
  · exact B1485507
  · exact B1485511
  · exact B1485515
  · exact B1485519
  · exact B1485523
  · exact B1485527
  · exact B1485531
  · exact B1485535
  · exact B1485539
  · exact B1485543
  · exact B1485547
  · exact B1485551
  · exact B1485555
  · exact B1485559
  · exact B1485563
  · exact B1485567
  · exact B1485571
  · exact B1485575
  · exact B1485579
  · exact B1485583
  · exact B1485587
  · exact B1485591
  · exact B1485595
  · exact B1485599
  · exact B1485603
  · exact B1485607
  · exact B1485611
  · exact B1485615
  · exact B1485619
  · exact B1485623
  · exact B1485627
  · exact B1485631
  · exact B1485635
  · exact B1485639
  · exact B1485643
  · exact B1485647
  · exact B1485651
  · exact B1485655
  · exact B1485659
  · exact B1485663
  · exact B1485667
  · exact B1485671
  · exact B1485675
  · exact B1485679
  · exact B1485683
  · exact B1485687
  · exact B1485691
  · exact B1485695
  · exact B1485699
  · exact B1485703
  · exact B1485707
  · exact B1485711
  · exact B1485715
  · exact B1485719
  · exact B1485723
  · exact B1485727
  · exact B1485731
  · exact B1485735
  · exact B1485739
  · exact B1485743
  · exact B1485747
  · exact B1485751
  · exact B1485755
  · exact B1485759
  · exact B1485763
  · exact B1485767
  · exact B1485771
  · exact B1485775
  · exact B1485779
  · exact B1485783
  · exact B1485787
  · exact B1485791
  · exact B1485795
  · exact B1485799
  · exact B1485803
  · exact B1485807
  · exact B1485811
  · exact B1485815
  · exact B1485819
  · exact B1485823
  · exact B1485827
  · exact B1485831
  · exact B1485835
  · exact B1485839
  · exact B1485843
  · exact B1485847
  · exact B1485851
  · exact B1485855
  · exact B1485859
  · exact B1485863
  · exact B1485867
  · exact B1485871
  · exact B1485875
  · exact B1485879
  · exact B1485883
  · exact B1485887
  · exact B1485891
  · exact B1485895
  · exact B1485899
  · exact B1485903
  · exact B1485907
  · exact B1485911
  · exact B1485915
  · exact B1485919
  · exact B1485923
  · exact B1485927
  · exact B1485931
  · exact B1485935
  · exact B1485939
  · exact B1485943
  · exact B1485947
  · exact B1485951
  · exact B1485955
  · exact B1485959
  · exact B1485963
  · exact B1485967
  · exact B1485971
  · exact B1485975
  · exact B1485979
  · exact B1485983
  · exact B1485987
  · exact B1485991
  · exact B1485995
  · exact B1485999
  · exact B1486003
  · exact B1486007
  · exact B1486011
  · exact B1486015
  · exact B1486019
  · exact B1486023
  · exact B1486027
  · exact B1486031
  · exact B1486035
  · exact B1486039
  · exact B1486043
  · exact B1486047
  · exact B1486051
  · exact B1486055
  · exact B1486059

theorem solution (m : ℕ) (hlo : 1484062 ≤ m) (hhi : m ≤ 1486062) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 371015 ≤ j := by omega
    have hj2 : j ≤ 371514 := by omega
    have hb : Blo 1484062 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
