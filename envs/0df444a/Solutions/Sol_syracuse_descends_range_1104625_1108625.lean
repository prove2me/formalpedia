-- Prove2me | solution 1 for syracuse_descends_range_1104625_1108625
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:38.923406+00:00
-- url     : https://prove2.me/submissions/78fccca5-3c89-4ee2-94d2-adac73f90ec6

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


theorem B3735557 : Blo 1104625 3735557 := bbase (se 4 (by rfl) ⟨350208, by rfl⟩ : syracuseStep 3735557 = 700417) (by norm_num)
theorem B2490389 : Blo 1104625 2490389 := bbase (se 6 (by rfl) ⟨58368, by rfl⟩ : syracuseStep 2490389 = 116737) (by norm_num)
theorem B2097181 : Blo 1104625 2097181 := bbase (se 3 (by rfl) ⟨393221, by rfl⟩ : syracuseStep 2097181 = 786443) (by norm_num)
theorem B1245217 : Blo 1104625 1245217 := bbase (se 2 (by rfl) ⟨466956, by rfl⟩ : syracuseStep 1245217 = 933913) (by norm_num)
theorem B1245253 : Blo 1104625 1245253 := bbase (se 4 (by rfl) ⟨116742, by rfl⟩ : syracuseStep 1245253 = 233485) (by norm_num)
theorem B1867853 : Blo 1104625 1867853 := bbase (se 3 (by rfl) ⟨350222, by rfl⟩ : syracuseStep 1867853 = 700445) (by norm_num)
theorem B2359381 : Blo 1104625 2359381 := bbase (se 8 (by rfl) ⟨13824, by rfl⟩ : syracuseStep 2359381 = 27649) (by norm_num)
theorem B1572949 : Blo 1104625 1572949 := bbase (se 8 (by rfl) ⟨9216, by rfl⟩ : syracuseStep 1572949 = 18433) (by norm_num)
theorem B1179733 : Blo 1104625 1179733 := bbase (se 8 (by rfl) ⟨6912, by rfl⟩ : syracuseStep 1179733 = 13825) (by norm_num)
theorem B2490461 : Blo 1104625 2490461 := bbase (se 3 (by rfl) ⟨466961, by rfl⟩ : syracuseStep 2490461 = 933923) (by norm_num)
theorem B3539045 : Blo 1104625 3539045 := bbase (se 4 (by rfl) ⟨331785, by rfl⟩ : syracuseStep 3539045 = 663571) (by norm_num)
theorem B1245289 : Blo 1104625 1245289 := bbase (se 2 (by rfl) ⟨466983, by rfl⟩ : syracuseStep 1245289 = 933967) (by norm_num)
theorem B1245325 : Blo 1104625 1245325 := bbase (se 3 (by rfl) ⟨233498, by rfl⟩ : syracuseStep 1245325 = 466997) (by norm_num)
theorem B1179793 : Blo 1104625 1179793 := bbase (se 2 (by rfl) ⟨442422, by rfl⟩ : syracuseStep 1179793 = 884845) (by norm_num)
theorem B2490533 : Blo 1104625 2490533 := bbase (se 4 (by rfl) ⟨233487, by rfl⟩ : syracuseStep 2490533 = 466975) (by norm_num)
theorem B1245361 : Blo 1104625 1245361 := bbase (se 2 (by rfl) ⟨467010, by rfl⟩ : syracuseStep 1245361 = 934021) (by norm_num)
theorem B1867981 : Blo 1104625 1867981 := bbase (se 3 (by rfl) ⟨350246, by rfl⟩ : syracuseStep 1867981 = 700493) (by norm_num)
theorem B40337621 : Blo 1104625 40337621 := bbase (se 7 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 40337621 = 945413) (by norm_num)
theorem B1245397 : Blo 1104625 1245397 := bbase (se 7 (by rfl) ⟨14594, by rfl⟩ : syracuseStep 1245397 = 29189) (by norm_num)
theorem B2490605 : Blo 1104625 2490605 := bbase (se 3 (by rfl) ⟨466988, by rfl⟩ : syracuseStep 2490605 = 933977) (by norm_num)
theorem B1245433 : Blo 1104625 1245433 := bbase (se 2 (by rfl) ⟨467037, by rfl⟩ : syracuseStep 1245433 = 934075) (by norm_num)
theorem B1245469 : Blo 1104625 1245469 := bbase (se 3 (by rfl) ⟨233525, by rfl⟩ : syracuseStep 1245469 = 467051) (by norm_num)
theorem B1868069 : Blo 1104625 1868069 := bbase (se 4 (by rfl) ⟨175131, by rfl⟩ : syracuseStep 1868069 = 350263) (by norm_num)
theorem B2490677 : Blo 1104625 2490677 := bbase (se 5 (by rfl) ⟨116750, by rfl⟩ : syracuseStep 2490677 = 233501) (by norm_num)
theorem B1245505 : Blo 1104625 1245505 := bbase (se 2 (by rfl) ⟨467064, by rfl⟩ : syracuseStep 1245505 = 934129) (by norm_num)
theorem B2097485 : Blo 1104625 2097485 := bbase (se 3 (by rfl) ⟨393278, by rfl⟩ : syracuseStep 2097485 = 786557) (by norm_num)
theorem B1245541 : Blo 1104625 1245541 := bbase (se 4 (by rfl) ⟨116769, by rfl⟩ : syracuseStep 1245541 = 233539) (by norm_num)
theorem B2490749 : Blo 1104625 2490749 := bbase (se 3 (by rfl) ⟨467015, by rfl⟩ : syracuseStep 2490749 = 934031) (by norm_num)
theorem B1245577 : Blo 1104625 1245577 := bbase (se 2 (by rfl) ⟨467091, by rfl⟩ : syracuseStep 1245577 = 934183) (by norm_num)
theorem B1573285 : Blo 1104625 1573285 := bbase (se 4 (by rfl) ⟨147495, by rfl⟩ : syracuseStep 1573285 = 294991) (by norm_num)
theorem B1868197 : Blo 1104625 1868197 := bbase (se 4 (by rfl) ⟨175143, by rfl⟩ : syracuseStep 1868197 = 350287) (by norm_num)
theorem B1245613 : Blo 1104625 1245613 := bbase (se 3 (by rfl) ⟨233552, by rfl⟩ : syracuseStep 1245613 = 467105) (by norm_num)
theorem B3735989 : Blo 1104625 3735989 := bbase (se 5 (by rfl) ⟨175124, by rfl⟩ : syracuseStep 3735989 = 350249) (by norm_num)
theorem B2490821 : Blo 1104625 2490821 := bbase (se 4 (by rfl) ⟨233514, by rfl⟩ : syracuseStep 2490821 = 467029) (by norm_num)
theorem B2654669 : Blo 1104625 2654669 := bbase (se 3 (by rfl) ⟨497750, by rfl⟩ : syracuseStep 2654669 = 995501) (by norm_num)
theorem B1769933 : Blo 1104625 1769933 := bbase (se 3 (by rfl) ⟨331862, by rfl⟩ : syracuseStep 1769933 = 663725) (by norm_num)
theorem B1180109 : Blo 1104625 1180109 := bbase (se 3 (by rfl) ⟨221270, by rfl⟩ : syracuseStep 1180109 = 442541) (by norm_num)
theorem B1245649 : Blo 1104625 1245649 := bbase (se 2 (by rfl) ⟨467118, by rfl⟩ : syracuseStep 1245649 = 934237) (by norm_num)
theorem B4194773 : Blo 1104625 4194773 := bbase (se 7 (by rfl) ⟨49157, by rfl⟩ : syracuseStep 4194773 = 98315) (by norm_num)
theorem B1245685 : Blo 1104625 1245685 := bbase (se 5 (by rfl) ⟨58391, by rfl⟩ : syracuseStep 1245685 = 116783) (by norm_num)
theorem B1868285 : Blo 1104625 1868285 := bbase (se 3 (by rfl) ⟨350303, by rfl⟩ : syracuseStep 1868285 = 700607) (by norm_num)
theorem B2490893 : Blo 1104625 2490893 := bbase (se 3 (by rfl) ⟨467042, by rfl⟩ : syracuseStep 2490893 = 934085) (by norm_num)
theorem B1245721 : Blo 1104625 1245721 := bbase (se 2 (by rfl) ⟨467145, by rfl⟩ : syracuseStep 1245721 = 934291) (by norm_num)
theorem B1245757 : Blo 1104625 1245757 := bbase (se 3 (by rfl) ⟨233579, by rfl⟩ : syracuseStep 1245757 = 467159) (by norm_num)
theorem B2490965 : Blo 1104625 2490965 := bbase (se 8 (by rfl) ⟨14595, by rfl⟩ : syracuseStep 2490965 = 29191) (by norm_num)
theorem B2654813 : Blo 1104625 2654813 := bbase (se 3 (by rfl) ⟨497777, by rfl⟩ : syracuseStep 2654813 = 995555) (by norm_num)
theorem B1245793 : Blo 1104625 1245793 := bbase (se 2 (by rfl) ⟨467172, by rfl⟩ : syracuseStep 1245793 = 934345) (by norm_num)
theorem B1573501 : Blo 1104625 1573501 := bbase (se 3 (by rfl) ⟨295031, by rfl⟩ : syracuseStep 1573501 = 590063) (by norm_num)
theorem B1868413 : Blo 1104625 1868413 := bbase (se 3 (by rfl) ⟨350327, by rfl⟩ : syracuseStep 1868413 = 700655) (by norm_num)
theorem B1245829 : Blo 1104625 1245829 := bbase (se 4 (by rfl) ⟨116796, by rfl⟩ : syracuseStep 1245829 = 233593) (by norm_num)
theorem B6062741 : Blo 1104625 6062741 := bbase (se 6 (by rfl) ⟨142095, by rfl⟩ : syracuseStep 6062741 = 284191) (by norm_num)
theorem B2491037 : Blo 1104625 2491037 := bbase (se 3 (by rfl) ⟨467069, by rfl⟩ : syracuseStep 2491037 = 934139) (by norm_num)
theorem B1245865 : Blo 1104625 1245865 := bbase (se 2 (by rfl) ⟨467199, by rfl⟩ : syracuseStep 1245865 = 934399) (by norm_num)
theorem B1245901 : Blo 1104625 1245901 := bbase (se 3 (by rfl) ⟨233606, by rfl⟩ : syracuseStep 1245901 = 467213) (by norm_num)
theorem B6292181 : Blo 1104625 6292181 := bbase (se 7 (by rfl) ⟨73736, by rfl⟩ : syracuseStep 6292181 = 147473) (by norm_num)
theorem B1868501 : Blo 1104625 1868501 := bbase (se 7 (by rfl) ⟨21896, by rfl⟩ : syracuseStep 1868501 = 43793) (by norm_num)
theorem B2491109 : Blo 1104625 2491109 := bbase (se 4 (by rfl) ⟨233541, by rfl⟩ : syracuseStep 2491109 = 467083) (by norm_num)
theorem B1245937 : Blo 1104625 1245937 := bbase (se 2 (by rfl) ⟨467226, by rfl⟩ : syracuseStep 1245937 = 934453) (by norm_num)
theorem B4195061 : Blo 1104625 4195061 := bbase (se 5 (by rfl) ⟨196643, by rfl⟩ : syracuseStep 4195061 = 393287) (by norm_num)
theorem B3146501 : Blo 1104625 3146501 := bbase (se 4 (by rfl) ⟨294984, by rfl⟩ : syracuseStep 3146501 = 589969) (by norm_num)
theorem B1245973 : Blo 1104625 1245973 := bbase (se 6 (by rfl) ⟨29202, by rfl⟩ : syracuseStep 1245973 = 58405) (by norm_num)
theorem B2491181 : Blo 1104625 2491181 := bbase (se 3 (by rfl) ⟨467096, by rfl⟩ : syracuseStep 2491181 = 934193) (by norm_num)
theorem B1246009 : Blo 1104625 1246009 := bbase (se 2 (by rfl) ⟨467253, by rfl⟩ : syracuseStep 1246009 = 934507) (by norm_num)
theorem B1868629 : Blo 1104625 1868629 := bbase (se 9 (by rfl) ⟨5474, by rfl⟩ : syracuseStep 1868629 = 10949) (by norm_num)
theorem B1246045 : Blo 1104625 1246045 := bbase (se 3 (by rfl) ⟨233633, by rfl⟩ : syracuseStep 1246045 = 467267) (by norm_num)
theorem B3736421 : Blo 1104625 3736421 := bbase (se 4 (by rfl) ⟨350289, by rfl⟩ : syracuseStep 3736421 = 700579) (by norm_num)
theorem B2491253 : Blo 1104625 2491253 := bbase (se 5 (by rfl) ⟨116777, by rfl⟩ : syracuseStep 2491253 = 233555) (by norm_num)
theorem B1246081 : Blo 1104625 1246081 := bbase (se 2 (by rfl) ⟨467280, by rfl⟩ : syracuseStep 1246081 = 934561) (by norm_num)
theorem B1180553 : Blo 1104625 1180553 := bbase (se 2 (by rfl) ⟨442707, by rfl⟩ : syracuseStep 1180553 = 885415) (by norm_num)
theorem B14156693 : Blo 1104625 14156693 := bbase (se 6 (by rfl) ⟨331797, by rfl⟩ : syracuseStep 14156693 = 663595) (by norm_num)
theorem B10617749 : Blo 1104625 10617749 := bbase (se 6 (by rfl) ⟨248853, by rfl⟩ : syracuseStep 10617749 = 497707) (by norm_num)
theorem B1246117 : Blo 1104625 1246117 := bbase (se 4 (by rfl) ⟨116823, by rfl⟩ : syracuseStep 1246117 = 233647) (by norm_num)
theorem B1868717 : Blo 1104625 1868717 := bbase (se 3 (by rfl) ⟨350384, by rfl⟩ : syracuseStep 1868717 = 700769) (by norm_num)
theorem B2491325 : Blo 1104625 2491325 := bbase (se 3 (by rfl) ⟨467123, by rfl⟩ : syracuseStep 2491325 = 934247) (by norm_num)
theorem B1180613 : Blo 1104625 1180613 := bbase (se 4 (by rfl) ⟨110682, by rfl⟩ : syracuseStep 1180613 = 221365) (by norm_num)
theorem B1246153 : Blo 1104625 1246153 := bbase (se 2 (by rfl) ⟨467307, by rfl⟩ : syracuseStep 1246153 = 934615) (by norm_num)
theorem B2360269 : Blo 1104625 2360269 := bbase (se 3 (by rfl) ⟨442550, by rfl⟩ : syracuseStep 2360269 = 885101) (by norm_num)
theorem B1770445 : Blo 1104625 1770445 := bbase (se 3 (by rfl) ⟨331958, by rfl⟩ : syracuseStep 1770445 = 663917) (by norm_num)
theorem B1246189 : Blo 1104625 1246189 := bbase (se 3 (by rfl) ⟨233660, by rfl⟩ : syracuseStep 1246189 = 467321) (by norm_num)
theorem B1573877 : Blo 1104625 1573877 := bbase (se 5 (by rfl) ⟨73775, by rfl⟩ : syracuseStep 1573877 = 147551) (by norm_num)
theorem B10224629 : Blo 1104625 10224629 := bbase (se 5 (by rfl) ⟨479279, by rfl⟩ : syracuseStep 10224629 = 958559) (by norm_num)
theorem B2491397 : Blo 1104625 2491397 := bbase (se 4 (by rfl) ⟨233568, by rfl⟩ : syracuseStep 2491397 = 467137) (by norm_num)
theorem B1246225 : Blo 1104625 1246225 := bbase (se 2 (by rfl) ⟨467334, by rfl⟩ : syracuseStep 1246225 = 934669) (by norm_num)
theorem B5604389 : Blo 1104625 5604389 := bbase (se 4 (by rfl) ⟨525411, by rfl⟩ : syracuseStep 5604389 = 1050823) (by norm_num)
theorem B1868845 : Blo 1104625 1868845 := bbase (se 3 (by rfl) ⟨350408, by rfl⟩ : syracuseStep 1868845 = 700817) (by norm_num)
theorem B1246261 : Blo 1104625 1246261 := bbase (se 5 (by rfl) ⟨58418, by rfl⟩ : syracuseStep 1246261 = 116837) (by norm_num)
theorem B2098237 : Blo 1104625 2098237 := bbase (se 3 (by rfl) ⟨393419, by rfl⟩ : syracuseStep 2098237 = 786839) (by norm_num)
theorem B1180741 : Blo 1104625 1180741 := bbase (se 4 (by rfl) ⟨110694, by rfl⟩ : syracuseStep 1180741 = 221389) (by norm_num)
theorem B2491469 : Blo 1104625 2491469 := bbase (se 3 (by rfl) ⟨467150, by rfl⟩ : syracuseStep 2491469 = 934301) (by norm_num)
theorem B1246297 : Blo 1104625 1246297 := bbase (se 2 (by rfl) ⟨467361, by rfl⟩ : syracuseStep 1246297 = 934723) (by norm_num)
theorem B1246333 : Blo 1104625 1246333 := bbase (se 3 (by rfl) ⟨233687, by rfl⟩ : syracuseStep 1246333 = 467375) (by norm_num)
theorem B1868933 : Blo 1104625 1868933 := bbase (se 4 (by rfl) ⟨175212, by rfl⟩ : syracuseStep 1868933 = 350425) (by norm_num)
theorem B2491541 : Blo 1104625 2491541 := bbase (se 6 (by rfl) ⟨58395, by rfl⟩ : syracuseStep 2491541 = 116791) (by norm_num)
theorem B1246369 : Blo 1104625 1246369 := bbase (se 2 (by rfl) ⟨467388, by rfl⟩ : syracuseStep 1246369 = 934777) (by norm_num)
theorem B1246405 : Blo 1104625 1246405 := bbase (se 4 (by rfl) ⟨116850, by rfl⟩ : syracuseStep 1246405 = 233701) (by norm_num)
theorem B2098381 : Blo 1104625 2098381 := bbase (se 3 (by rfl) ⟨393446, by rfl⟩ : syracuseStep 2098381 = 786893) (by norm_num)
theorem B2491613 : Blo 1104625 2491613 := bbase (se 3 (by rfl) ⟨467177, by rfl⟩ : syracuseStep 2491613 = 934355) (by norm_num)
theorem B1246441 : Blo 1104625 1246441 := bbase (se 2 (by rfl) ⟨467415, by rfl⟩ : syracuseStep 1246441 = 934831) (by norm_num)
theorem B1869061 : Blo 1104625 1869061 := bbase (se 4 (by rfl) ⟨175224, by rfl⟩ : syracuseStep 1869061 = 350449) (by norm_num)
theorem B1246477 : Blo 1104625 1246477 := bbase (se 3 (by rfl) ⟨233714, by rfl⟩ : syracuseStep 1246477 = 467429) (by norm_num)
theorem B3736853 : Blo 1104625 3736853 := bbase (se 6 (by rfl) ⟨87582, by rfl⟩ : syracuseStep 3736853 = 175165) (by norm_num)
theorem B5047589 : Blo 1104625 5047589 := bbase (se 4 (by rfl) ⟨473211, by rfl⟩ : syracuseStep 5047589 = 946423) (by norm_num)
theorem B2491685 : Blo 1104625 2491685 := bbase (se 4 (by rfl) ⟨233595, by rfl⟩ : syracuseStep 2491685 = 467191) (by norm_num)
theorem B1246513 : Blo 1104625 1246513 := bbase (se 2 (by rfl) ⟨467442, by rfl⟩ : syracuseStep 1246513 = 934885) (by norm_num)
theorem B4719941 : Blo 1104625 4719941 := bbase (se 4 (by rfl) ⟨442494, by rfl⟩ : syracuseStep 4719941 = 884989) (by norm_num)
theorem B1246549 : Blo 1104625 1246549 := bbase (se 12 (by rfl) ⟨456, by rfl⟩ : syracuseStep 1246549 = 913) (by norm_num)
theorem B1869149 : Blo 1104625 1869149 := bbase (se 3 (by rfl) ⟨350465, by rfl⟩ : syracuseStep 1869149 = 700931) (by norm_num)
theorem B2098541 : Blo 1104625 2098541 := bbase (se 3 (by rfl) ⟨393476, by rfl⟩ : syracuseStep 2098541 = 786953) (by norm_num)
theorem B2491757 : Blo 1104625 2491757 := bbase (se 3 (by rfl) ⟨467204, by rfl⟩ : syracuseStep 2491757 = 934409) (by norm_num)
theorem B1246585 : Blo 1104625 1246585 := bbase (se 2 (by rfl) ⟨467469, by rfl⟩ : syracuseStep 1246585 = 934939) (by norm_num)
theorem B1246621 : Blo 1104625 1246621 := bbase (se 3 (by rfl) ⟨233741, by rfl⟩ : syracuseStep 1246621 = 467483) (by norm_num)
theorem B2491829 : Blo 1104625 2491829 := bbase (se 5 (by rfl) ⟨116804, by rfl⟩ : syracuseStep 2491829 = 233609) (by norm_num)
theorem B2360765 : Blo 1104625 2360765 := bbase (se 3 (by rfl) ⟨442643, by rfl⟩ : syracuseStep 2360765 = 885287) (by norm_num)
theorem B1246657 : Blo 1104625 1246657 := bbase (se 2 (by rfl) ⟨467496, by rfl⟩ : syracuseStep 1246657 = 934993) (by norm_num)
theorem B1869277 : Blo 1104625 1869277 := bbase (se 3 (by rfl) ⟨350489, by rfl⟩ : syracuseStep 1869277 = 700979) (by norm_num)
theorem B1246693 : Blo 1104625 1246693 := bbase (se 4 (by rfl) ⟨116877, by rfl⟩ : syracuseStep 1246693 = 233755) (by norm_num)
theorem B3540469 : Blo 1104625 3540469 := bbase (se 5 (by rfl) ⟨165959, by rfl⟩ : syracuseStep 3540469 = 331919) (by norm_num)
theorem B2098685 : Blo 1104625 2098685 := bbase (se 3 (by rfl) ⟨393503, by rfl⟩ : syracuseStep 2098685 = 787007) (by norm_num)
theorem B2491901 : Blo 1104625 2491901 := bbase (se 3 (by rfl) ⟨467231, by rfl⟩ : syracuseStep 2491901 = 934463) (by norm_num)
theorem B1181185 : Blo 1104625 1181185 := bbase (se 2 (by rfl) ⟨442944, by rfl⟩ : syracuseStep 1181185 = 885889) (by norm_num)
theorem B1246729 : Blo 1104625 1246729 := bbase (se 2 (by rfl) ⟨467523, by rfl⟩ : syracuseStep 1246729 = 935047) (by norm_num)
theorem B1246765 : Blo 1104625 1246765 := bbase (se 3 (by rfl) ⟨233768, by rfl⟩ : syracuseStep 1246765 = 467537) (by norm_num)
theorem B1869365 : Blo 1104625 1869365 := bbase (se 5 (by rfl) ⟨87626, by rfl⟩ : syracuseStep 1869365 = 175253) (by norm_num)
theorem B1705541 : Blo 1104625 1705541 := bbase (se 4 (by rfl) ⟨159894, by rfl⟩ : syracuseStep 1705541 = 319789) (by norm_num)
theorem B2491973 : Blo 1104625 2491973 := bbase (se 4 (by rfl) ⟨233622, by rfl⟩ : syracuseStep 2491973 = 467245) (by norm_num)
theorem B1246801 : Blo 1104625 1246801 := bbase (se 2 (by rfl) ⟨467550, by rfl⟩ : syracuseStep 1246801 = 935101) (by norm_num)
theorem B23004757 : Blo 1104625 23004757 := bbase (se 8 (by rfl) ⟨134793, by rfl⟩ : syracuseStep 23004757 = 269587) (by norm_num)
theorem B1246837 : Blo 1104625 1246837 := bbase (se 5 (by rfl) ⟨58445, by rfl⟩ : syracuseStep 1246837 = 116891) (by norm_num)
theorem B1181305 : Blo 1104625 1181305 := bbase (se 2 (by rfl) ⟨442989, by rfl⟩ : syracuseStep 1181305 = 885979) (by norm_num)
theorem B2492045 : Blo 1104625 2492045 := bbase (se 3 (by rfl) ⟨467258, by rfl⟩ : syracuseStep 2492045 = 934517) (by norm_num)
theorem B1246873 : Blo 1104625 1246873 := bbase (se 2 (by rfl) ⟨467577, by rfl⟩ : syracuseStep 1246873 = 935155) (by norm_num)
theorem B1869493 : Blo 1104625 1869493 := bbase (se 5 (by rfl) ⟨87632, by rfl⟩ : syracuseStep 1869493 = 175265) (by norm_num)
theorem B1246909 : Blo 1104625 1246909 := bbase (se 3 (by rfl) ⟨233795, by rfl⟩ : syracuseStep 1246909 = 467591) (by norm_num)
theorem B3737285 : Blo 1104625 3737285 := bbase (se 4 (by rfl) ⟨350370, by rfl⟩ : syracuseStep 3737285 = 700741) (by norm_num)
theorem B2492117 : Blo 1104625 2492117 := bbase (se 7 (by rfl) ⟨29204, by rfl⟩ : syracuseStep 2492117 = 58409) (by norm_num)
theorem B1246945 : Blo 1104625 1246945 := bbase (se 2 (by rfl) ⟨467604, by rfl⟩ : syracuseStep 1246945 = 935209) (by norm_num)
theorem B1246981 : Blo 1104625 1246981 := bbase (se 4 (by rfl) ⟨116904, by rfl⟩ : syracuseStep 1246981 = 233809) (by norm_num)
theorem B1869581 : Blo 1104625 1869581 := bbase (se 3 (by rfl) ⟨350546, by rfl⟩ : syracuseStep 1869581 = 701093) (by norm_num)
theorem B2098973 : Blo 1104625 2098973 := bbase (se 3 (by rfl) ⟨393557, by rfl⟩ : syracuseStep 2098973 = 787115) (by norm_num)
theorem B2492189 : Blo 1104625 2492189 := bbase (se 3 (by rfl) ⟨467285, by rfl⟩ : syracuseStep 2492189 = 934571) (by norm_num)
theorem B1247017 : Blo 1104625 1247017 := bbase (se 2 (by rfl) ⟨467631, by rfl⟩ : syracuseStep 1247017 = 935263) (by norm_num)
theorem B1247053 : Blo 1104625 1247053 := bbase (se 3 (by rfl) ⟨233822, by rfl⟩ : syracuseStep 1247053 = 467645) (by norm_num)
theorem B2492261 : Blo 1104625 2492261 := bbase (se 4 (by rfl) ⟨233649, by rfl⟩ : syracuseStep 2492261 = 467299) (by norm_num)
theorem B1247089 : Blo 1104625 1247089 := bbase (se 2 (by rfl) ⟨467658, by rfl⟩ : syracuseStep 1247089 = 935317) (by norm_num)
theorem B1181557 : Blo 1104625 1181557 := bbase (se 5 (by rfl) ⟨55385, by rfl⟩ : syracuseStep 1181557 = 110771) (by norm_num)
theorem B1181561 : Blo 1104625 1181561 := bbase (se 2 (by rfl) ⟨443085, by rfl⟩ : syracuseStep 1181561 = 886171) (by norm_num)
theorem B1869709 : Blo 1104625 1869709 := bbase (se 3 (by rfl) ⟨350570, by rfl⟩ : syracuseStep 1869709 = 701141) (by norm_num)
theorem B4196245 : Blo 1104625 4196245 := bbase (se 6 (by rfl) ⟨98349, by rfl⟩ : syracuseStep 4196245 = 196699) (by norm_num)
theorem B1247125 : Blo 1104625 1247125 := bbase (se 6 (by rfl) ⟨29229, by rfl⟩ : syracuseStep 1247125 = 58459) (by norm_num)
theorem B2492333 : Blo 1104625 2492333 := bbase (se 3 (by rfl) ⟨467312, by rfl⟩ : syracuseStep 2492333 = 934625) (by norm_num)
theorem B2099125 : Blo 1104625 2099125 := bbase (se 5 (by rfl) ⟨98396, by rfl⟩ : syracuseStep 2099125 = 196793) (by norm_num)
theorem B1771445 : Blo 1104625 1771445 := bbase (se 5 (by rfl) ⟨83036, by rfl⟩ : syracuseStep 1771445 = 166073) (by norm_num)
theorem B1247161 : Blo 1104625 1247161 := bbase (se 2 (by rfl) ⟨467685, by rfl⟩ : syracuseStep 1247161 = 935371) (by norm_num)
theorem B1247197 : Blo 1104625 1247197 := bbase (se 3 (by rfl) ⟨233849, by rfl⟩ : syracuseStep 1247197 = 467699) (by norm_num)
theorem B1869797 : Blo 1104625 1869797 := bbase (se 4 (by rfl) ⟨175293, by rfl⟩ : syracuseStep 1869797 = 350587) (by norm_num)
theorem B2492405 : Blo 1104625 2492405 := bbase (se 5 (by rfl) ⟨116831, by rfl⟩ : syracuseStep 2492405 = 233663) (by norm_num)
theorem B1771573 : Blo 1104625 1771573 := bbase (se 5 (by rfl) ⟨83042, by rfl⟩ : syracuseStep 1771573 = 166085) (by norm_num)
theorem B2492477 : Blo 1104625 2492477 := bbase (se 3 (by rfl) ⟨467339, by rfl⟩ : syracuseStep 2492477 = 934679) (by norm_num)
theorem B1869925 : Blo 1104625 1869925 := bbase (se 4 (by rfl) ⟨175305, by rfl⟩ : syracuseStep 1869925 = 350611) (by norm_num)
theorem B1771637 : Blo 1104625 1771637 := bbase (se 5 (by rfl) ⟨83045, by rfl⟩ : syracuseStep 1771637 = 166091) (by norm_num)
theorem B3737717 : Blo 1104625 3737717 := bbase (se 5 (by rfl) ⟨175205, by rfl⟩ : syracuseStep 3737717 = 350411) (by norm_num)
theorem B2492549 : Blo 1104625 2492549 := bbase (se 4 (by rfl) ⟨233676, by rfl⟩ : syracuseStep 2492549 = 467353) (by norm_num)
theorem B10389653 : Blo 1104625 10389653 := bbase (se 6 (by rfl) ⟨243507, by rfl⟩ : syracuseStep 10389653 = 487015) (by norm_num)
theorem B1870013 : Blo 1104625 1870013 := bbase (se 3 (by rfl) ⟨350627, by rfl⟩ : syracuseStep 1870013 = 701255) (by norm_num)
theorem B4196549 : Blo 1104625 4196549 := bbase (se 4 (by rfl) ⟨393426, by rfl⟩ : syracuseStep 4196549 = 786853) (by norm_num)
theorem B2492621 : Blo 1104625 2492621 := bbase (se 3 (by rfl) ⟨467366, by rfl⟩ : syracuseStep 2492621 = 934733) (by norm_num)
theorem B2099429 : Blo 1104625 2099429 := bbase (se 4 (by rfl) ⟨196821, by rfl⟩ : syracuseStep 2099429 = 393643) (by norm_num)
theorem B2492693 : Blo 1104625 2492693 := bbase (se 6 (by rfl) ⟨58422, by rfl⟩ : syracuseStep 2492693 = 116845) (by norm_num)
theorem B4720949 : Blo 1104625 4720949 := bbase (se 5 (by rfl) ⟨221294, by rfl⟩ : syracuseStep 4720949 = 442589) (by norm_num)
theorem B3148085 : Blo 1104625 3148085 := bbase (se 5 (by rfl) ⟨147566, by rfl⟩ : syracuseStep 3148085 = 295133) (by norm_num)
theorem B2361653 : Blo 1104625 2361653 := bbase (se 5 (by rfl) ⟨110702, by rfl⟩ : syracuseStep 2361653 = 221405) (by norm_num)
theorem B5605685 : Blo 1104625 5605685 := bbase (se 5 (by rfl) ⟨262766, by rfl⟩ : syracuseStep 5605685 = 525533) (by norm_num)
theorem B1870141 : Blo 1104625 1870141 := bbase (se 3 (by rfl) ⟨350651, by rfl⟩ : syracuseStep 1870141 = 701303) (by norm_num)
theorem B2492765 : Blo 1104625 2492765 := bbase (se 3 (by rfl) ⟨467393, by rfl⟩ : syracuseStep 2492765 = 934787) (by norm_num)
theorem B1345921 : Blo 1104625 1345921 := bbase (se 2 (by rfl) ⟨504720, by rfl⟩ : syracuseStep 1345921 = 1009441) (by norm_num)
theorem B1575301 : Blo 1104625 1575301 := bbase (se 4 (by rfl) ⟨147684, by rfl⟩ : syracuseStep 1575301 = 295369) (by norm_num)
theorem B1870229 : Blo 1104625 1870229 := bbase (se 6 (by rfl) ⟨43833, by rfl⟩ : syracuseStep 1870229 = 87667) (by norm_num)
theorem B2492837 : Blo 1104625 2492837 := bbase (se 4 (by rfl) ⟨233703, by rfl⟩ : syracuseStep 2492837 = 467407) (by norm_num)
theorem B2361773 : Blo 1104625 2361773 := bbase (se 3 (by rfl) ⟨442832, by rfl⟩ : syracuseStep 2361773 = 885665) (by norm_num)
theorem B1182125 : Blo 1104625 1182125 := bbase (se 3 (by rfl) ⟨221648, by rfl⟩ : syracuseStep 1182125 = 443297) (by norm_num)
theorem B2492909 : Blo 1104625 2492909 := bbase (se 3 (by rfl) ⟨467420, by rfl⟩ : syracuseStep 2492909 = 934841) (by norm_num)
theorem B1870357 : Blo 1104625 1870357 := bbase (se 6 (by rfl) ⟨43836, by rfl⟩ : syracuseStep 1870357 = 87673) (by norm_num)
theorem B3738149 : Blo 1104625 3738149 := bbase (se 4 (by rfl) ⟨350451, by rfl⟩ : syracuseStep 3738149 = 700903) (by norm_num)
theorem B2656813 : Blo 1104625 2656813 := bbase (se 3 (by rfl) ⟨498152, by rfl⟩ : syracuseStep 2656813 = 996305) (by norm_num)
theorem B2492981 : Blo 1104625 2492981 := bbase (se 5 (by rfl) ⟨116858, by rfl⟩ : syracuseStep 2492981 = 233717) (by norm_num)
theorem B1182313 : Blo 1104625 1182313 := bbase (se 2 (by rfl) ⟨443367, by rfl⟩ : syracuseStep 1182313 = 886735) (by norm_num)
theorem B1870445 : Blo 1104625 1870445 := bbase (se 3 (by rfl) ⟨350708, by rfl⟩ : syracuseStep 1870445 = 701417) (by norm_num)
theorem B2493053 : Blo 1104625 2493053 := bbase (se 3 (by rfl) ⟨467447, by rfl⟩ : syracuseStep 2493053 = 934895) (by norm_num)
theorem B2493125 : Blo 1104625 2493125 := bbase (se 4 (by rfl) ⟨233730, by rfl⟩ : syracuseStep 2493125 = 467461) (by norm_num)
theorem B1870573 : Blo 1104625 1870573 := bbase (se 3 (by rfl) ⟨350732, by rfl⟩ : syracuseStep 1870573 = 701465) (by norm_num)
theorem B2493197 : Blo 1104625 2493197 := bbase (se 3 (by rfl) ⟨467474, by rfl⟩ : syracuseStep 2493197 = 934949) (by norm_num)
theorem B11504405 : Blo 1104625 11504405 := bbase (se 6 (by rfl) ⟨269634, by rfl⟩ : syracuseStep 11504405 = 539269) (by norm_num)
theorem B1215253 : Blo 1104625 1215253 := bbase (se 6 (by rfl) ⟨28482, by rfl⟩ : syracuseStep 1215253 = 56965) (by norm_num)
theorem B1870661 : Blo 1104625 1870661 := bbase (se 4 (by rfl) ⟨175374, by rfl⟩ : syracuseStep 1870661 = 350749) (by norm_num)
theorem B2493269 : Blo 1104625 2493269 := bbase (se 9 (by rfl) ⟨7304, by rfl⟩ : syracuseStep 2493269 = 14609) (by norm_num)
theorem B2493341 : Blo 1104625 2493341 := bbase (se 3 (by rfl) ⟨467501, by rfl⟩ : syracuseStep 2493341 = 935003) (by norm_num)
theorem B1870789 : Blo 1104625 1870789 := bbase (se 4 (by rfl) ⟨175386, by rfl⟩ : syracuseStep 1870789 = 350773) (by norm_num)
theorem B3148757 : Blo 1104625 3148757 := bbase (se 7 (by rfl) ⟨36899, by rfl⟩ : syracuseStep 3148757 = 73799) (by norm_num)
theorem B2100181 : Blo 1104625 2100181 := bbase (se 7 (by rfl) ⟨24611, by rfl⟩ : syracuseStep 2100181 = 49223) (by norm_num)
theorem B1575893 : Blo 1104625 1575893 := bbase (se 7 (by rfl) ⟨18467, by rfl⟩ : syracuseStep 1575893 = 36935) (by norm_num)
theorem B3738581 : Blo 1104625 3738581 := bbase (se 7 (by rfl) ⟨43811, by rfl⟩ : syracuseStep 3738581 = 87623) (by norm_num)
theorem B2493413 : Blo 1104625 2493413 := bbase (se 4 (by rfl) ⟨233757, by rfl⟩ : syracuseStep 2493413 = 467515) (by norm_num)
theorem B2362405 : Blo 1104625 2362405 := bbase (se 4 (by rfl) ⟨221475, by rfl⟩ : syracuseStep 2362405 = 442951) (by norm_num)
theorem B1575973 : Blo 1104625 1575973 := bbase (se 4 (by rfl) ⟨147747, by rfl⟩ : syracuseStep 1575973 = 295495) (by norm_num)
theorem B2493485 : Blo 1104625 2493485 := bbase (se 3 (by rfl) ⟨467528, by rfl⟩ : syracuseStep 2493485 = 935057) (by norm_num)
theorem B3542069 : Blo 1104625 3542069 := bbase (se 5 (by rfl) ⟨166034, by rfl⟩ : syracuseStep 3542069 = 332069) (by norm_num)
theorem B2100325 : Blo 1104625 2100325 := bbase (se 4 (by rfl) ⟨196905, by rfl⟩ : syracuseStep 2100325 = 393811) (by norm_num)
theorem B2493557 : Blo 1104625 2493557 := bbase (se 5 (by rfl) ⟨116885, by rfl⟩ : syracuseStep 2493557 = 233771) (by norm_num)
theorem B1576093 : Blo 1104625 1576093 := bbase (se 3 (by rfl) ⟨295517, by rfl⟩ : syracuseStep 1576093 = 591035) (by norm_num)
theorem B7081141 : Blo 1104625 7081141 := bbase (se 5 (by rfl) ⟨331928, by rfl⟩ : syracuseStep 7081141 = 663857) (by norm_num)
theorem B2493629 : Blo 1104625 2493629 := bbase (se 3 (by rfl) ⟨467555, by rfl⟩ : syracuseStep 2493629 = 935111) (by norm_num)
theorem B1346765 : Blo 1104625 1346765 := bbase (se 3 (by rfl) ⟨252518, by rfl⟩ : syracuseStep 1346765 = 505037) (by norm_num)
theorem B2526421 : Blo 1104625 2526421 := bbase (se 7 (by rfl) ⟨29606, by rfl⟩ : syracuseStep 2526421 = 59213) (by norm_num)
theorem B1576189 : Blo 1104625 1576189 := bbase (se 3 (by rfl) ⟨295535, by rfl⟩ : syracuseStep 1576189 = 591071) (by norm_num)
theorem B2100485 : Blo 1104625 2100485 := bbase (se 4 (by rfl) ⟨196920, by rfl⟩ : syracuseStep 2100485 = 393841) (by norm_num)
theorem B2493701 : Blo 1104625 2493701 := bbase (se 4 (by rfl) ⟨233784, by rfl⟩ : syracuseStep 2493701 = 467569) (by norm_num)
theorem B2493773 : Blo 1104625 2493773 := bbase (se 3 (by rfl) ⟨467582, by rfl⟩ : syracuseStep 2493773 = 935165) (by norm_num)
theorem B3149189 : Blo 1104625 3149189 := bbase (se 4 (by rfl) ⟨295236, by rfl⟩ : syracuseStep 3149189 = 590473) (by norm_num)
theorem B3739013 : Blo 1104625 3739013 := bbase (se 4 (by rfl) ⟨350532, by rfl⟩ : syracuseStep 3739013 = 701065) (by norm_num)
theorem B2100629 : Blo 1104625 2100629 := bbase (se 6 (by rfl) ⟨49233, by rfl⟩ : syracuseStep 2100629 = 98467) (by norm_num)
theorem B2493845 : Blo 1104625 2493845 := bbase (se 6 (by rfl) ⟨58449, by rfl⟩ : syracuseStep 2493845 = 116899) (by norm_num)
theorem B1772957 : Blo 1104625 1772957 := bbase (se 3 (by rfl) ⟨332429, by rfl⟩ : syracuseStep 1772957 = 664859) (by norm_num)
theorem B1183133 : Blo 1104625 1183133 := bbase (se 3 (by rfl) ⟨221837, by rfl⟩ : syracuseStep 1183133 = 443675) (by norm_num)
theorem B11505077 : Blo 1104625 11505077 := bbase (se 5 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 11505077 = 1078601) (by norm_num)
theorem B2493917 : Blo 1104625 2493917 := bbase (se 3 (by rfl) ⟨467609, by rfl⟩ : syracuseStep 2493917 = 935219) (by norm_num)
theorem B1773085 : Blo 1104625 1773085 := bbase (se 3 (by rfl) ⟨332453, by rfl⟩ : syracuseStep 1773085 = 664907) (by norm_num)
theorem B2493989 : Blo 1104625 2493989 := bbase (se 4 (by rfl) ⟨233811, by rfl⟩ : syracuseStep 2493989 = 467623) (by norm_num)
theorem B5606981 : Blo 1104625 5606981 := bbase (se 4 (by rfl) ⟨525654, by rfl⟩ : syracuseStep 5606981 = 1051309) (by norm_num)
theorem B2494061 : Blo 1104625 2494061 := bbase (se 3 (by rfl) ⟨467636, by rfl⟩ : syracuseStep 2494061 = 935273) (by norm_num)
theorem B2100917 : Blo 1104625 2100917 := bbase (se 5 (by rfl) ⟨98480, by rfl⟩ : syracuseStep 2100917 = 196961) (by norm_num)
theorem B2494133 : Blo 1104625 2494133 := bbase (se 5 (by rfl) ⟨116912, by rfl⟩ : syracuseStep 2494133 = 233825) (by norm_num)
theorem B2559709 : Blo 1104625 2559709 := bbase (se 3 (by rfl) ⟨479945, by rfl⟩ : syracuseStep 2559709 = 959891) (by norm_num)
theorem B1576685 : Blo 1104625 1576685 := bbase (se 3 (by rfl) ⟨295628, by rfl⟩ : syracuseStep 1576685 = 591257) (by norm_num)
theorem B2494205 : Blo 1104625 2494205 := bbase (se 3 (by rfl) ⟨467663, by rfl⟩ : syracuseStep 2494205 = 935327) (by norm_num)
theorem B3739445 : Blo 1104625 3739445 := bbase (se 5 (by rfl) ⟨175286, by rfl⟩ : syracuseStep 3739445 = 350573) (by norm_num)
theorem B2494277 : Blo 1104625 2494277 := bbase (se 4 (by rfl) ⟨233838, by rfl⟩ : syracuseStep 2494277 = 467677) (by norm_num)
theorem B2101069 : Blo 1104625 2101069 := bbase (se 3 (by rfl) ⟨393950, by rfl⟩ : syracuseStep 2101069 = 787901) (by norm_num)
theorem B1183577 : Blo 1104625 1183577 := bbase (se 2 (by rfl) ⟨443841, by rfl⟩ : syracuseStep 1183577 = 887683) (by norm_num)
theorem B2494349 : Blo 1104625 2494349 := bbase (se 3 (by rfl) ⟨467690, by rfl⟩ : syracuseStep 2494349 = 935381) (by norm_num)
theorem B2658197 : Blo 1104625 2658197 := bbase (se 6 (by rfl) ⟨62301, by rfl⟩ : syracuseStep 2658197 = 124603) (by norm_num)
theorem B2658205 : Blo 1104625 2658205 := bbase (se 3 (by rfl) ⟨498413, by rfl⟩ : syracuseStep 2658205 = 996827) (by norm_num)
theorem B2363293 : Blo 1104625 2363293 := bbase (se 3 (by rfl) ⟨443117, by rfl⟩ : syracuseStep 2363293 = 886235) (by norm_num)
theorem B2363413 : Blo 1104625 2363413 := bbase (se 6 (by rfl) ⟨55392, by rfl⟩ : syracuseStep 2363413 = 110785) (by norm_num)
theorem B4722725 : Blo 1104625 4722725 := bbase (se 4 (by rfl) ⟨442755, by rfl⟩ : syracuseStep 4722725 = 885511) (by norm_num)
theorem B1183825 : Blo 1104625 1183825 := bbase (se 2 (by rfl) ⟨443934, by rfl⟩ : syracuseStep 1183825 = 887869) (by norm_num)
theorem B3149941 : Blo 1104625 3149941 := bbase (se 5 (by rfl) ⟨147653, by rfl⟩ : syracuseStep 3149941 = 295307) (by norm_num)
theorem B2101373 : Blo 1104625 2101373 := bbase (se 3 (by rfl) ⟨394007, by rfl⟩ : syracuseStep 2101373 = 788015) (by norm_num)
theorem B3543173 : Blo 1104625 3543173 := bbase (se 4 (by rfl) ⟨332172, by rfl⟩ : syracuseStep 3543173 = 664345) (by norm_num)
theorem B8523989 : Blo 1104625 8523989 := bbase (se 7 (by rfl) ⟨99890, by rfl⟩ : syracuseStep 8523989 = 199781) (by norm_num)
theorem B3739877 : Blo 1104625 3739877 := bbase (se 4 (by rfl) ⟨350613, by rfl⟩ : syracuseStep 3739877 = 701227) (by norm_num)
theorem B4198661 : Blo 1104625 4198661 := bbase (se 4 (by rfl) ⟨393624, by rfl⟩ : syracuseStep 4198661 = 787249) (by norm_num)
theorem B2363669 : Blo 1104625 2363669 := bbase (se 6 (by rfl) ⟨55398, by rfl⟩ : syracuseStep 2363669 = 110797) (by norm_num)
theorem B1577237 : Blo 1104625 1577237 := bbase (se 6 (by rfl) ⟨36966, by rfl⟩ : syracuseStep 1577237 = 73933) (by norm_num)
theorem B1773893 : Blo 1104625 1773893 := bbase (se 4 (by rfl) ⟨166302, by rfl⟩ : syracuseStep 1773893 = 332605) (by norm_num)
theorem B4198949 : Blo 1104625 4198949 := bbase (se 4 (by rfl) ⟨393651, by rfl⟩ : syracuseStep 4198949 = 787303) (by norm_num)
theorem B1774181 : Blo 1104625 1774181 := bbase (se 4 (by rfl) ⟨166329, by rfl⟩ : syracuseStep 1774181 = 332659) (by norm_num)
theorem B3740309 : Blo 1104625 3740309 := bbase (se 6 (by rfl) ⟨87663, by rfl⟩ : syracuseStep 3740309 = 175327) (by norm_num)
theorem B4264645 : Blo 1104625 4264645 := bbase (se 4 (by rfl) ⟨399810, by rfl⟩ : syracuseStep 4264645 = 799621) (by norm_num)
theorem B5608277 : Blo 1104625 5608277 := bbase (se 9 (by rfl) ⟨16430, by rfl⟩ : syracuseStep 5608277 = 32861) (by norm_num)
theorem B2102125 : Blo 1104625 2102125 := bbase (se 3 (by rfl) ⟨394148, by rfl⟩ : syracuseStep 2102125 = 788297) (by norm_num)
theorem B2659205 : Blo 1104625 2659205 := bbase (se 4 (by rfl) ⟨249300, by rfl⟩ : syracuseStep 2659205 = 498601) (by norm_num)
theorem B2102269 : Blo 1104625 2102269 := bbase (se 3 (by rfl) ⟨394175, by rfl⟩ : syracuseStep 2102269 = 788351) (by norm_num)
theorem B1774597 : Blo 1104625 1774597 := bbase (se 4 (by rfl) ⟨166368, by rfl⟩ : syracuseStep 1774597 = 332737) (by norm_num)
theorem B1577989 : Blo 1104625 1577989 := bbase (se 4 (by rfl) ⟨147936, by rfl⟩ : syracuseStep 1577989 = 295873) (by norm_num)
theorem B3740741 : Blo 1104625 3740741 := bbase (se 4 (by rfl) ⟨350694, by rfl⟩ : syracuseStep 3740741 = 701389) (by norm_num)
theorem B2364557 : Blo 1104625 2364557 := bbase (se 3 (by rfl) ⟨443354, by rfl⟩ : syracuseStep 2364557 = 886709) (by norm_num)
theorem B2102429 : Blo 1104625 2102429 := bbase (se 3 (by rfl) ⟨394205, by rfl⟩ : syracuseStep 2102429 = 788411) (by norm_num)
theorem B2987237 : Blo 1104625 2987237 := bbase (se 4 (by rfl) ⟨280053, by rfl⟩ : syracuseStep 2987237 = 560107) (by norm_num)
theorem B2102573 : Blo 1104625 2102573 := bbase (se 3 (by rfl) ⟨394232, by rfl⟩ : syracuseStep 2102573 = 788465) (by norm_num)
theorem B5051765 : Blo 1104625 5051765 := bbase (se 5 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 5051765 = 473603) (by norm_num)
theorem B2364797 : Blo 1104625 2364797 := bbase (se 3 (by rfl) ⟨443399, by rfl⟩ : syracuseStep 2364797 = 886799) (by norm_num)
theorem B3741173 : Blo 1104625 3741173 := bbase (se 5 (by rfl) ⟨175367, by rfl⟩ : syracuseStep 3741173 = 350735) (by norm_num)
theorem B2102861 : Blo 1104625 2102861 := bbase (se 3 (by rfl) ⟨394286, by rfl⟩ : syracuseStep 2102861 = 788573) (by norm_num)
theorem B2659973 : Blo 1104625 2659973 := bbase (se 4 (by rfl) ⟨249372, by rfl⟩ : syracuseStep 2659973 = 498745) (by norm_num)
theorem B4200133 : Blo 1104625 4200133 := bbase (se 4 (by rfl) ⟨393762, by rfl⟩ : syracuseStep 4200133 = 787525) (by norm_num)
theorem B2103013 : Blo 1104625 2103013 := bbase (se 4 (by rfl) ⟨197157, by rfl⟩ : syracuseStep 2103013 = 394315) (by norm_num)
theorem B2365301 : Blo 1104625 2365301 := bbase (se 5 (by rfl) ⟨110873, by rfl⟩ : syracuseStep 2365301 = 221747) (by norm_num)
theorem B2365309 : Blo 1104625 2365309 := bbase (se 3 (by rfl) ⟨443495, by rfl⟩ : syracuseStep 2365309 = 886991) (by norm_num)
theorem B1120133 : Blo 1104625 1120133 := bbase (se 4 (by rfl) ⟨105012, by rfl⟩ : syracuseStep 1120133 = 210025) (by norm_num)
theorem B3741605 : Blo 1104625 3741605 := bbase (se 4 (by rfl) ⟨350775, by rfl⟩ : syracuseStep 3741605 = 701551) (by norm_num)
theorem B1775533 : Blo 1104625 1775533 := bbase (se 3 (by rfl) ⟨332912, by rfl⟩ : syracuseStep 1775533 = 665825) (by norm_num)
theorem B8394677 : Blo 1104625 8394677 := bbase (se 5 (by rfl) ⟨393500, by rfl⟩ : syracuseStep 8394677 = 787001) (by norm_num)
theorem B4200437 : Blo 1104625 4200437 := bbase (se 5 (by rfl) ⟨196895, by rfl⟩ : syracuseStep 4200437 = 393791) (by norm_num)
theorem B5314565 : Blo 1104625 5314565 := bbase (se 4 (by rfl) ⟨498240, by rfl⟩ : syracuseStep 5314565 = 996481) (by norm_num)
theorem B3545093 : Blo 1104625 3545093 := bbase (se 4 (by rfl) ⟨332352, by rfl⟩ : syracuseStep 3545093 = 664705) (by norm_num)
theorem B2103317 : Blo 1104625 2103317 := bbase (se 6 (by rfl) ⟨49296, by rfl⟩ : syracuseStep 2103317 = 98593) (by norm_num)
theorem B5609573 : Blo 1104625 5609573 := bbase (se 4 (by rfl) ⟨525897, by rfl⟩ : syracuseStep 5609573 = 1051795) (by norm_num)
theorem B2104069 : Blo 1104625 2104069 := bbase (se 4 (by rfl) ⟨197256, by rfl⟩ : syracuseStep 2104069 = 394513) (by norm_num)
theorem B3152789 : Blo 1104625 3152789 := bbase (se 6 (by rfl) ⟨73893, by rfl⟩ : syracuseStep 3152789 = 147787) (by norm_num)
theorem B2104213 : Blo 1104625 2104213 := bbase (se 6 (by rfl) ⟨49317, by rfl⟩ : syracuseStep 2104213 = 98635) (by norm_num)
theorem B2694077 : Blo 1104625 2694077 := bbase (se 3 (by rfl) ⟨505139, by rfl⟩ : syracuseStep 2694077 = 1010279) (by norm_num)
theorem B2366437 : Blo 1104625 2366437 := bbase (se 4 (by rfl) ⟨221853, by rfl⟩ : syracuseStep 2366437 = 443707) (by norm_num)
theorem B1121297 : Blo 1104625 1121297 := bbase (se 2 (by rfl) ⟨420486, by rfl⟩ : syracuseStep 1121297 = 840973) (by norm_num)
theorem B1121333 : Blo 1104625 1121333 := bbase (se 5 (by rfl) ⟨52562, by rfl⟩ : syracuseStep 1121333 = 105125) (by norm_num)
theorem B2104373 : Blo 1104625 2104373 := bbase (se 5 (by rfl) ⟨98642, by rfl⟩ : syracuseStep 2104373 = 197285) (by norm_num)
theorem B2104517 : Blo 1104625 2104517 := bbase (se 4 (by rfl) ⟨197298, by rfl⟩ : syracuseStep 2104517 = 394597) (by norm_num)
theorem B2989349 : Blo 1104625 2989349 := bbase (se 4 (by rfl) ⟨280251, by rfl⟩ : syracuseStep 2989349 = 560503) (by norm_num)
theorem B2366813 : Blo 1104625 2366813 := bbase (se 3 (by rfl) ⟨443777, by rfl⟩ : syracuseStep 2366813 = 887555) (by norm_num)
theorem B8985973 : Blo 1104625 8985973 := bbase (se 5 (by rfl) ⟨421217, by rfl⟩ : syracuseStep 8985973 = 842435) (by norm_num)
theorem B5610869 : Blo 1104625 5610869 := bbase (se 5 (by rfl) ⟨263009, by rfl⟩ : syracuseStep 5610869 = 526019) (by norm_num)
theorem B5315989 : Blo 1104625 5315989 := bbase (se 6 (by rfl) ⟨124593, by rfl⟩ : syracuseStep 5315989 = 249187) (by norm_num)
theorem B3546517 : Blo 1104625 3546517 := bbase (se 6 (by rfl) ⟨83121, by rfl⟩ : syracuseStep 3546517 = 166243) (by norm_num)
theorem B2661781 : Blo 1104625 2661781 := bbase (se 6 (by rfl) ⟨62385, by rfl⟩ : syracuseStep 2661781 = 124771) (by norm_num)
theorem B1121861 : Blo 1104625 1121861 := bbase (se 4 (by rfl) ⟨105174, by rfl⟩ : syracuseStep 1121861 = 210349) (by norm_num)
theorem B2989781 : Blo 1104625 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B4038437 : Blo 1104625 4038437 := bbase (se 4 (by rfl) ⟨378603, by rfl⟩ : syracuseStep 4038437 = 757207) (by norm_num)
theorem B1122121 : Blo 1104625 1122121 := bbase (se 2 (by rfl) ⟨420795, by rfl⟩ : syracuseStep 1122121 = 841591) (by norm_num)
theorem B3546965 : Blo 1104625 3546965 := bbase (se 9 (by rfl) ⟨10391, by rfl⟩ : syracuseStep 3546965 = 20783) (by norm_num)
theorem B2662301 : Blo 1104625 2662301 := bbase (se 3 (by rfl) ⟨499181, by rfl⟩ : syracuseStep 2662301 = 998363) (by norm_num)
theorem B4202549 : Blo 1104625 4202549 := bbase (se 5 (by rfl) ⟨196994, by rfl⟩ : syracuseStep 4202549 = 393989) (by norm_num)
theorem B3153973 : Blo 1104625 3153973 := bbase (se 5 (by rfl) ⟨147842, by rfl⟩ : syracuseStep 3153973 = 295685) (by norm_num)
theorem B1417381 : Blo 1104625 1417381 := bbase (se 4 (by rfl) ⟨132879, by rfl⟩ : syracuseStep 1417381 = 265759) (by norm_num)
theorem B4726997 : Blo 1104625 4726997 := bbase (se 7 (by rfl) ⟨55394, by rfl⟩ : syracuseStep 4726997 = 110789) (by norm_num)
theorem B3154133 : Blo 1104625 3154133 := bbase (se 7 (by rfl) ⟨36962, by rfl⟩ : syracuseStep 3154133 = 73925) (by norm_num)
theorem B2662685 : Blo 1104625 2662685 := bbase (se 3 (by rfl) ⟨499253, by rfl⟩ : syracuseStep 2662685 = 998507) (by norm_num)
theorem B2662733 : Blo 1104625 2662733 := bbase (se 3 (by rfl) ⟨499262, by rfl⟩ : syracuseStep 2662733 = 998525) (by norm_num)
theorem B4202837 : Blo 1104625 4202837 := bbase (se 10 (by rfl) ⟨6156, by rfl⟩ : syracuseStep 4202837 = 12313) (by norm_num)
theorem B2662741 : Blo 1104625 2662741 := bbase (se 10 (by rfl) ⟨3900, by rfl⟩ : syracuseStep 2662741 = 7801) (by norm_num)
theorem B3154373 : Blo 1104625 3154373 := bbase (se 4 (by rfl) ⟨295722, by rfl⟩ : syracuseStep 3154373 = 591445) (by norm_num)
theorem B5677573 : Blo 1104625 5677573 := bbase (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) (by norm_num)
theorem B1679933 : Blo 1104625 1679933 := bbase (se 3 (by rfl) ⟨314987, by rfl⟩ : syracuseStep 1679933 = 629975) (by norm_num)
theorem B2990677 : Blo 1104625 2990677 := bbase (se 8 (by rfl) ⟨17523, by rfl⟩ : syracuseStep 2990677 = 35047) (by norm_num)
theorem B3154565 : Blo 1104625 3154565 := bbase (se 4 (by rfl) ⟨295740, by rfl⟩ : syracuseStep 3154565 = 591481) (by norm_num)
theorem B5612165 : Blo 1104625 5612165 := bbase (se 4 (by rfl) ⟨526140, by rfl⟩ : syracuseStep 5612165 = 1052281) (by norm_num)
theorem B5677733 : Blo 1104625 5677733 := bbase (se 4 (by rfl) ⟨532287, by rfl⟩ : syracuseStep 5677733 = 1064575) (by norm_num)
theorem B1418321 : Blo 1104625 1418321 := bbase (se 2 (by rfl) ⟨531870, by rfl⟩ : syracuseStep 1418321 = 1063741) (by norm_num)
theorem B1680589 : Blo 1104625 1680589 := bbase (se 3 (by rfl) ⟨315110, by rfl⟩ : syracuseStep 1680589 = 630221) (by norm_num)
theorem B2991509 : Blo 1104625 2991509 := bbase (se 6 (by rfl) ⟨70113, by rfl⟩ : syracuseStep 2991509 = 140227) (by norm_num)
theorem B4793845 : Blo 1104625 4793845 := bbase (se 5 (by rfl) ⟨224711, by rfl⟩ : syracuseStep 4793845 = 449423) (by norm_num)
theorem B4204021 : Blo 1104625 4204021 := bbase (se 5 (by rfl) ⟨197063, by rfl⟩ : syracuseStep 4204021 = 394127) (by norm_num)
theorem B3155557 : Blo 1104625 3155557 := bbase (se 4 (by rfl) ⟨295833, by rfl⟩ : syracuseStep 3155557 = 591667) (by norm_num)
theorem B4204325 : Blo 1104625 4204325 := bbase (se 4 (by rfl) ⟨394155, by rfl⟩ : syracuseStep 4204325 = 788311) (by norm_num)
theorem B4794229 : Blo 1104625 4794229 := bbase (se 5 (by rfl) ⟨224729, by rfl⟩ : syracuseStep 4794229 = 449459) (by norm_num)
theorem B4728773 : Blo 1104625 4728773 := bbase (se 4 (by rfl) ⟨443322, by rfl⟩ : syracuseStep 4728773 = 886645) (by norm_num)
theorem B3549221 : Blo 1104625 3549221 := bbase (se 4 (by rfl) ⟨332739, by rfl⟩ : syracuseStep 3549221 = 665479) (by norm_num)
theorem B4729013 : Blo 1104625 4729013 := bbase (se 5 (by rfl) ⟨221672, by rfl⟩ : syracuseStep 4729013 = 443345) (by norm_num)
theorem B20195669 : Blo 1104625 20195669 := bbase (se 10 (by rfl) ⟨29583, by rfl⟩ : syracuseStep 20195669 = 59167) (by norm_num)
theorem B6302069 : Blo 1104625 6302069 := bbase (se 5 (by rfl) ⟨295409, by rfl⟩ : syracuseStep 6302069 = 590819) (by norm_num)
theorem B2632357 : Blo 1104625 2632357 := bbase (se 4 (by rfl) ⟨246783, by rfl⟩ : syracuseStep 2632357 = 493567) (by norm_num)
theorem B3156661 : Blo 1104625 3156661 := bbase (se 5 (by rfl) ⟨147968, by rfl⟩ : syracuseStep 3156661 = 295937) (by norm_num)
theorem B2796221 : Blo 1104625 2796221 := bbase (se 3 (by rfl) ⟨524291, by rfl⟩ : syracuseStep 2796221 = 1048583) (by norm_num)
theorem B2796565 : Blo 1104625 2796565 := bbase (se 6 (by rfl) ⟨65544, by rfl⟩ : syracuseStep 2796565 = 131089) (by norm_num)
theorem B2796677 : Blo 1104625 2796677 := bbase (se 4 (by rfl) ⟨262188, by rfl⟩ : syracuseStep 2796677 = 524377) (by norm_num)
theorem B2993381 : Blo 1104625 2993381 := bbase (se 4 (by rfl) ⟨280629, by rfl⟩ : syracuseStep 2993381 = 561259) (by norm_num)
theorem B2796869 : Blo 1104625 2796869 := bbase (se 4 (by rfl) ⟨262206, by rfl⟩ : syracuseStep 2796869 = 524413) (by norm_num)
theorem B1420625 : Blo 1104625 1420625 := bbase (se 2 (by rfl) ⟨532734, by rfl⟩ : syracuseStep 1420625 = 1065469) (by norm_num)
theorem B2797213 : Blo 1104625 2797213 := bbase (se 3 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 2797213 = 1048955) (by norm_num)
theorem B3780341 : Blo 1104625 3780341 := bbase (se 5 (by rfl) ⟨177203, by rfl⟩ : syracuseStep 3780341 = 354407) (by norm_num)
theorem B5385989 : Blo 1104625 5385989 := bbase (se 4 (by rfl) ⟨504936, by rfl⟩ : syracuseStep 5385989 = 1009873) (by norm_num)
theorem B2797325 : Blo 1104625 2797325 := bbase (se 3 (by rfl) ⟨524498, by rfl⟩ : syracuseStep 2797325 = 1048997) (by norm_num)
theorem B4206437 : Blo 1104625 4206437 := bbase (se 4 (by rfl) ⟨394353, by rfl⟩ : syracuseStep 4206437 = 788707) (by norm_num)
theorem B2797517 : Blo 1104625 2797517 := bbase (se 3 (by rfl) ⟨524534, by rfl⟩ : syracuseStep 2797517 = 1049069) (by norm_num)
theorem B4206725 : Blo 1104625 4206725 := bbase (se 4 (by rfl) ⟨394380, by rfl⟩ : syracuseStep 4206725 = 788761) (by norm_num)
theorem B4796581 : Blo 1104625 4796581 := bbase (se 4 (by rfl) ⟨449679, by rfl⟩ : syracuseStep 4796581 = 899359) (by norm_num)
theorem B2699453 : Blo 1104625 2699453 := bbase (se 3 (by rfl) ⟨506147, by rfl⟩ : syracuseStep 2699453 = 1012295) (by norm_num)
theorem B2797861 : Blo 1104625 2797861 := bbase (se 4 (by rfl) ⟨262299, by rfl⟩ : syracuseStep 2797861 = 524599) (by norm_num)
theorem B2797973 : Blo 1104625 2797973 := bbase (se 6 (by rfl) ⟨65577, by rfl⟩ : syracuseStep 2797973 = 131155) (by norm_num)
theorem B4731301 : Blo 1104625 4731301 := bbase (se 4 (by rfl) ⟨443559, by rfl⟩ : syracuseStep 4731301 = 887119) (by norm_num)
theorem B2699693 : Blo 1104625 2699693 := bbase (se 3 (by rfl) ⟨506192, by rfl⟩ : syracuseStep 2699693 = 1012385) (by norm_num)
theorem B2241037 : Blo 1104625 2241037 := bbase (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) (by norm_num)
theorem B2798165 : Blo 1104625 2798165 := bbase (se 8 (by rfl) ⟨16395, by rfl⟩ : syracuseStep 2798165 = 32791) (by norm_num)
theorem B2798509 : Blo 1104625 2798509 := bbase (se 3 (by rfl) ⟨524720, by rfl⟩ : syracuseStep 2798509 = 1049441) (by norm_num)
theorem B13448213 : Blo 1104625 13448213 := bbase (se 6 (by rfl) ⟨315192, by rfl⟩ : syracuseStep 13448213 = 630385) (by norm_num)
theorem B2798621 : Blo 1104625 2798621 := bbase (se 3 (by rfl) ⟨524741, by rfl⟩ : syracuseStep 2798621 = 1049483) (by norm_num)
theorem B2798813 : Blo 1104625 2798813 := bbase (se 3 (by rfl) ⟨524777, by rfl⟩ : syracuseStep 2798813 = 1049555) (by norm_num)
theorem B4207909 : Blo 1104625 4207909 := bbase (se 4 (by rfl) ⟨394491, by rfl⟩ : syracuseStep 4207909 = 788983) (by norm_num)
theorem B8402453 : Blo 1104625 8402453 := bbase (se 6 (by rfl) ⟨196932, by rfl⟩ : syracuseStep 8402453 = 393865) (by norm_num)
theorem B2799157 : Blo 1104625 2799157 := bbase (se 5 (by rfl) ⟨131210, by rfl⟩ : syracuseStep 2799157 = 262421) (by norm_num)
theorem B5322293 : Blo 1104625 5322293 := bbase (se 5 (by rfl) ⟨249482, by rfl⟩ : syracuseStep 5322293 = 498965) (by norm_num)
theorem B3192389 : Blo 1104625 3192389 := bbase (se 4 (by rfl) ⟨299286, by rfl⟩ : syracuseStep 3192389 = 598573) (by norm_num)
theorem B4208213 : Blo 1104625 4208213 := bbase (se 8 (by rfl) ⟨24657, by rfl⟩ : syracuseStep 4208213 = 49315) (by norm_num)
theorem B2799269 : Blo 1104625 2799269 := bbase (se 4 (by rfl) ⟨262431, by rfl⟩ : syracuseStep 2799269 = 524863) (by norm_num)
theorem B1685261 : Blo 1104625 1685261 := bbase (se 3 (by rfl) ⟨315986, by rfl⟩ : syracuseStep 1685261 = 631973) (by norm_num)
theorem B2799461 : Blo 1104625 2799461 := bbase (se 4 (by rfl) ⟨262449, by rfl⟩ : syracuseStep 2799461 = 524899) (by norm_num)
theorem B4732789 : Blo 1104625 4732789 := bbase (se 5 (by rfl) ⟨221849, by rfl⟩ : syracuseStep 4732789 = 443699) (by norm_num)
theorem B4732805 : Blo 1104625 4732805 := bbase (se 4 (by rfl) ⟨443700, by rfl⟩ : syracuseStep 4732805 = 887401) (by norm_num)
theorem B2996149 : Blo 1104625 2996149 := bbase (se 5 (by rfl) ⟨140444, by rfl⟩ : syracuseStep 2996149 = 280889) (by norm_num)
theorem B7976981 : Blo 1104625 7976981 := bbase (se 6 (by rfl) ⟨186960, by rfl⟩ : syracuseStep 7976981 = 373921) (by norm_num)
theorem B2799805 : Blo 1104625 2799805 := bbase (se 3 (by rfl) ⟨524963, by rfl⟩ : syracuseStep 2799805 = 1049927) (by norm_num)
theorem B2799917 : Blo 1104625 2799917 := bbase (se 3 (by rfl) ⟨524984, by rfl⟩ : syracuseStep 2799917 = 1049969) (by norm_num)
theorem B2800109 : Blo 1104625 2800109 := bbase (se 3 (by rfl) ⟨525020, by rfl⟩ : syracuseStep 2800109 = 1050041) (by norm_num)
theorem B2800453 : Blo 1104625 2800453 := bbase (se 4 (by rfl) ⟨262542, by rfl⟩ : syracuseStep 2800453 = 525085) (by norm_num)
theorem B7093109 : Blo 1104625 7093109 := bbase (se 5 (by rfl) ⟨332489, by rfl⟩ : syracuseStep 7093109 = 664979) (by norm_num)
theorem B5323637 : Blo 1104625 5323637 := bbase (se 5 (by rfl) ⟨249545, by rfl⟩ : syracuseStep 5323637 = 499091) (by norm_num)
theorem B2800565 : Blo 1104625 2800565 := bbase (se 5 (by rfl) ⟨131276, by rfl⟩ : syracuseStep 2800565 = 262553) (by norm_num)
theorem B2800757 : Blo 1104625 2800757 := bbase (se 5 (by rfl) ⟨131285, by rfl⟩ : syracuseStep 2800757 = 262571) (by norm_num)
theorem B25509077 : Blo 1104625 25509077 := bbase (se 7 (by rfl) ⟨298934, by rfl⟩ : syracuseStep 25509077 = 597869) (by norm_num)
theorem B2244029 : Blo 1104625 2244029 := bbase (se 3 (by rfl) ⟨420755, by rfl⟩ : syracuseStep 2244029 = 841511) (by norm_num)
theorem B2801101 : Blo 1104625 2801101 := bbase (se 3 (by rfl) ⟨525206, by rfl⟩ : syracuseStep 2801101 = 1050413) (by norm_num)
theorem B3784229 : Blo 1104625 3784229 := bbase (se 4 (by rfl) ⟨354771, by rfl⟩ : syracuseStep 3784229 = 709543) (by norm_num)
theorem B2801213 : Blo 1104625 2801213 := bbase (se 3 (by rfl) ⟨525227, by rfl⟩ : syracuseStep 2801213 = 1050455) (by norm_num)
theorem B2801405 : Blo 1104625 2801405 := bbase (se 3 (by rfl) ⟨525263, by rfl⟩ : syracuseStep 2801405 = 1050527) (by norm_num)
theorem B1327061 : Blo 1104625 1327061 := bbase (se 7 (by rfl) ⟨15551, by rfl⟩ : syracuseStep 1327061 = 31103) (by norm_num)
theorem B1294321 : Blo 1104625 1294321 := bbase (se 2 (by rfl) ⟨485370, by rfl⟩ : syracuseStep 1294321 = 970741) (by norm_num)
theorem B2801749 : Blo 1104625 2801749 := bbase (se 8 (by rfl) ⟨16416, by rfl⟩ : syracuseStep 2801749 = 32833) (by norm_num)
theorem B4735061 : Blo 1104625 4735061 := bbase (se 8 (by rfl) ⟨27744, by rfl⟩ : syracuseStep 4735061 = 55489) (by norm_num)
theorem B2801861 : Blo 1104625 2801861 := bbase (se 4 (by rfl) ⟨262674, by rfl⟩ : syracuseStep 2801861 = 525349) (by norm_num)
theorem B5325061 : Blo 1104625 5325061 := bbase (se 4 (by rfl) ⟨499224, by rfl⟩ : syracuseStep 5325061 = 998449) (by norm_num)
theorem B1327369 : Blo 1104625 1327369 := bbase (se 2 (by rfl) ⟨497763, by rfl⟩ : syracuseStep 1327369 = 995527) (by norm_num)
theorem B10633589 : Blo 1104625 10633589 := bbase (se 5 (by rfl) ⟨498449, by rfl⟩ : syracuseStep 10633589 = 996899) (by norm_num)
theorem B2802053 : Blo 1104625 2802053 := bbase (se 4 (by rfl) ⟨262692, by rfl⟩ : syracuseStep 2802053 = 525385) (by norm_num)
theorem B1261993 : Blo 1104625 1261993 := bbase (se 2 (by rfl) ⟨473247, by rfl⟩ : syracuseStep 1261993 = 946495) (by norm_num)
theorem B5980661 : Blo 1104625 5980661 := bbase (se 5 (by rfl) ⟨280343, by rfl⟩ : syracuseStep 5980661 = 560687) (by norm_num)
theorem B1327757 : Blo 1104625 1327757 := bbase (se 3 (by rfl) ⟨248954, by rfl⟩ : syracuseStep 1327757 = 497909) (by norm_num)
theorem B2802397 : Blo 1104625 2802397 := bbase (se 3 (by rfl) ⟨525449, by rfl⟩ : syracuseStep 2802397 = 1050899) (by norm_num)
theorem B2802509 : Blo 1104625 2802509 := bbase (se 3 (by rfl) ⟨525470, by rfl⟩ : syracuseStep 2802509 = 1050941) (by norm_num)
theorem B1328113 : Blo 1104625 1328113 := bbase (se 2 (by rfl) ⟨498042, by rfl⟩ : syracuseStep 1328113 = 996085) (by norm_num)
theorem B2802701 : Blo 1104625 2802701 := bbase (se 3 (by rfl) ⟨525506, by rfl⟩ : syracuseStep 2802701 = 1051013) (by norm_num)
theorem B1197337 : Blo 1104625 1197337 := bbase (se 2 (by rfl) ⟨449001, by rfl⟩ : syracuseStep 1197337 = 898003) (by norm_num)
theorem B1328449 : Blo 1104625 1328449 := bbase (se 2 (by rfl) ⟨498168, by rfl⟩ : syracuseStep 1328449 = 996337) (by norm_num)
theorem B2803045 : Blo 1104625 2803045 := bbase (se 4 (by rfl) ⟨262785, by rfl⟩ : syracuseStep 2803045 = 525571) (by norm_num)
theorem B2803157 : Blo 1104625 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B1263161 : Blo 1104625 1263161 := bbase (se 2 (by rfl) ⟨473685, by rfl⟩ : syracuseStep 1263161 = 947371) (by norm_num)
theorem B3884645 : Blo 1104625 3884645 := bbase (se 4 (by rfl) ⟨364185, by rfl⟩ : syracuseStep 3884645 = 728371) (by norm_num)
theorem B3786389 : Blo 1104625 3786389 := bbase (se 6 (by rfl) ⟨88743, by rfl⟩ : syracuseStep 3786389 = 177487) (by norm_num)
theorem B2803349 : Blo 1104625 2803349 := bbase (se 6 (by rfl) ⟨65703, by rfl⟩ : syracuseStep 2803349 = 131407) (by norm_num)
theorem B2246357 : Blo 1104625 2246357 := bbase (se 7 (by rfl) ⟨26324, by rfl⟩ : syracuseStep 2246357 = 52649) (by norm_num)
theorem B2246381 : Blo 1104625 2246381 := bbase (se 3 (by rfl) ⟨421196, by rfl⟩ : syracuseStep 2246381 = 842393) (by norm_num)
theorem B2246429 : Blo 1104625 2246429 := bbase (se 3 (by rfl) ⟨421205, by rfl⟩ : syracuseStep 2246429 = 842411) (by norm_num)
theorem B2803693 : Blo 1104625 2803693 := bbase (se 3 (by rfl) ⟨525692, by rfl⟩ : syracuseStep 2803693 = 1051385) (by norm_num)
theorem B2803805 : Blo 1104625 2803805 := bbase (se 3 (by rfl) ⟨525713, by rfl⟩ : syracuseStep 2803805 = 1051427) (by norm_num)
theorem B1656941 : Blo 1104625 1656941 := bbase (se 3 (by rfl) ⟨310676, by rfl⟩ : syracuseStep 1656941 = 621353) (by norm_num)
theorem B1656965 : Blo 1104625 1656965 := bbase (se 4 (by rfl) ⟨155340, by rfl⟩ : syracuseStep 1656965 = 310681) (by norm_num)
theorem B12601493 : Blo 1104625 12601493 := bbase (se 6 (by rfl) ⟨295347, by rfl⟩ : syracuseStep 12601493 = 590695) (by norm_num)
theorem B1656989 : Blo 1104625 1656989 := bbase (se 3 (by rfl) ⟨310685, by rfl⟩ : syracuseStep 1656989 = 621371) (by norm_num)
theorem B1329329 : Blo 1104625 1329329 := bbase (se 2 (by rfl) ⟨498498, by rfl⟩ : syracuseStep 1329329 = 996997) (by norm_num)
theorem B1657013 : Blo 1104625 1657013 := bbase (se 5 (by rfl) ⟨77672, by rfl⟩ : syracuseStep 1657013 = 155345) (by norm_num)
theorem B1657037 : Blo 1104625 1657037 := bbase (se 3 (by rfl) ⟨310694, by rfl⟩ : syracuseStep 1657037 = 621389) (by norm_num)
theorem B1657061 : Blo 1104625 1657061 := bbase (se 4 (by rfl) ⟨155349, by rfl⟩ : syracuseStep 1657061 = 310699) (by norm_num)
theorem B6310133 : Blo 1104625 6310133 := bbase (se 5 (by rfl) ⟨295787, by rfl⟩ : syracuseStep 6310133 = 591575) (by norm_num)
theorem B1657085 : Blo 1104625 1657085 := bbase (se 3 (by rfl) ⟨310703, by rfl⟩ : syracuseStep 1657085 = 621407) (by norm_num)
theorem B1657109 : Blo 1104625 1657109 := bbase (se 6 (by rfl) ⟨38838, by rfl⟩ : syracuseStep 1657109 = 77677) (by norm_num)
theorem B2803997 : Blo 1104625 2803997 := bbase (se 3 (by rfl) ⟨525749, by rfl⟩ : syracuseStep 2803997 = 1051499) (by norm_num)
theorem B1657133 : Blo 1104625 1657133 := bbase (se 3 (by rfl) ⟨310712, by rfl⟩ : syracuseStep 1657133 = 621425) (by norm_num)
theorem B1657157 : Blo 1104625 1657157 := bbase (se 4 (by rfl) ⟨155358, by rfl⟩ : syracuseStep 1657157 = 310717) (by norm_num)
theorem B1657181 : Blo 1104625 1657181 := bbase (se 3 (by rfl) ⟨310721, by rfl⟩ : syracuseStep 1657181 = 621443) (by norm_num)
theorem B1657205 : Blo 1104625 1657205 := bbase (se 5 (by rfl) ⟨77681, by rfl⟩ : syracuseStep 1657205 = 155363) (by norm_num)
theorem B1657229 : Blo 1104625 1657229 := bbase (se 3 (by rfl) ⟨310730, by rfl⟩ : syracuseStep 1657229 = 621461) (by norm_num)
theorem B1657253 : Blo 1104625 1657253 := bbase (se 4 (by rfl) ⟨155367, by rfl⟩ : syracuseStep 1657253 = 310735) (by norm_num)
theorem B1657277 : Blo 1104625 1657277 := bbase (se 3 (by rfl) ⟨310739, by rfl⟩ : syracuseStep 1657277 = 621479) (by norm_num)
theorem B1657301 : Blo 1104625 1657301 := bbase (se 7 (by rfl) ⟨19421, by rfl⟩ : syracuseStep 1657301 = 38843) (by norm_num)
theorem B1329637 : Blo 1104625 1329637 := bbase (se 4 (by rfl) ⟨124653, by rfl⟩ : syracuseStep 1329637 = 249307) (by norm_num)
theorem B1657325 : Blo 1104625 1657325 := bbase (se 3 (by rfl) ⟨310748, by rfl⟩ : syracuseStep 1657325 = 621497) (by norm_num)
theorem B1657349 : Blo 1104625 1657349 := bbase (se 4 (by rfl) ⟨155376, by rfl⟩ : syracuseStep 1657349 = 310753) (by norm_num)
theorem B1657373 : Blo 1104625 1657373 := bbase (se 3 (by rfl) ⟨310757, by rfl⟩ : syracuseStep 1657373 = 621515) (by norm_num)
theorem B1657397 : Blo 1104625 1657397 := bbase (se 5 (by rfl) ⟨77690, by rfl⟩ : syracuseStep 1657397 = 155381) (by norm_num)
theorem B1657421 : Blo 1104625 1657421 := bbase (se 3 (by rfl) ⟨310766, by rfl⟩ : syracuseStep 1657421 = 621533) (by norm_num)
theorem B1657445 : Blo 1104625 1657445 := bbase (se 4 (by rfl) ⟨155385, by rfl⟩ : syracuseStep 1657445 = 310771) (by norm_num)
theorem B2804341 : Blo 1104625 2804341 := bbase (se 5 (by rfl) ⟨131453, by rfl⟩ : syracuseStep 2804341 = 262907) (by norm_num)
theorem B1657469 : Blo 1104625 1657469 := bbase (se 3 (by rfl) ⟨310775, by rfl⟩ : syracuseStep 1657469 = 621551) (by norm_num)
theorem B1657493 : Blo 1104625 1657493 := bbase (se 6 (by rfl) ⟨38847, by rfl⟩ : syracuseStep 1657493 = 77695) (by norm_num)
theorem B1657517 : Blo 1104625 1657517 := bbase (se 3 (by rfl) ⟨310784, by rfl⟩ : syracuseStep 1657517 = 621569) (by norm_num)
theorem B1657541 : Blo 1104625 1657541 := bbase (se 4 (by rfl) ⟨155394, by rfl⟩ : syracuseStep 1657541 = 310789) (by norm_num)
theorem B1657565 : Blo 1104625 1657565 := bbase (se 3 (by rfl) ⟨310793, by rfl⟩ : syracuseStep 1657565 = 621587) (by norm_num)
theorem B2804453 : Blo 1104625 2804453 := bbase (se 4 (by rfl) ⟨262917, by rfl⟩ : syracuseStep 2804453 = 525835) (by norm_num)
theorem B1657589 : Blo 1104625 1657589 := bbase (se 5 (by rfl) ⟨77699, by rfl⟩ : syracuseStep 1657589 = 155399) (by norm_num)
theorem B1657613 : Blo 1104625 1657613 := bbase (se 3 (by rfl) ⟨310802, by rfl⟩ : syracuseStep 1657613 = 621605) (by norm_num)
theorem B1657637 : Blo 1104625 1657637 := bbase (se 4 (by rfl) ⟨155403, by rfl⟩ : syracuseStep 1657637 = 310807) (by norm_num)
theorem B1657661 : Blo 1104625 1657661 := bbase (se 3 (by rfl) ⟨310811, by rfl⟩ : syracuseStep 1657661 = 621623) (by norm_num)
theorem B1657685 : Blo 1104625 1657685 := bbase (se 9 (by rfl) ⟨4856, by rfl⟩ : syracuseStep 1657685 = 9713) (by norm_num)
theorem B1330021 : Blo 1104625 1330021 := bbase (se 4 (by rfl) ⟨124689, by rfl⟩ : syracuseStep 1330021 = 249379) (by norm_num)
theorem B1330025 : Blo 1104625 1330025 := bbase (se 2 (by rfl) ⟨498759, by rfl⟩ : syracuseStep 1330025 = 997519) (by norm_num)
theorem B1657709 : Blo 1104625 1657709 := bbase (se 3 (by rfl) ⟨310820, by rfl⟩ : syracuseStep 1657709 = 621641) (by norm_num)
theorem B1657733 : Blo 1104625 1657733 := bbase (se 4 (by rfl) ⟨155412, by rfl⟩ : syracuseStep 1657733 = 310825) (by norm_num)
theorem B1657757 : Blo 1104625 1657757 := bbase (se 3 (by rfl) ⟨310829, by rfl⟩ : syracuseStep 1657757 = 621659) (by norm_num)
theorem B2804645 : Blo 1104625 2804645 := bbase (se 4 (by rfl) ⟨262935, by rfl⟩ : syracuseStep 2804645 = 525871) (by norm_num)
theorem B1657781 : Blo 1104625 1657781 := bbase (se 5 (by rfl) ⟨77708, by rfl⟩ : syracuseStep 1657781 = 155417) (by norm_num)
theorem B1657805 : Blo 1104625 1657805 := bbase (se 3 (by rfl) ⟨310838, by rfl⟩ : syracuseStep 1657805 = 621677) (by norm_num)
theorem B1493965 : Blo 1104625 1493965 := bbase (se 3 (by rfl) ⟨280118, by rfl⟩ : syracuseStep 1493965 = 560237) (by norm_num)
theorem B1657829 : Blo 1104625 1657829 := bbase (se 4 (by rfl) ⟨155421, by rfl⟩ : syracuseStep 1657829 = 310843) (by norm_num)
theorem B1657853 : Blo 1104625 1657853 := bbase (se 3 (by rfl) ⟨310847, by rfl⟩ : syracuseStep 1657853 = 621695) (by norm_num)
theorem B1657877 : Blo 1104625 1657877 := bbase (se 6 (by rfl) ⟨38856, by rfl⟩ : syracuseStep 1657877 = 77713) (by norm_num)
theorem B1657901 : Blo 1104625 1657901 := bbase (se 3 (by rfl) ⟨310856, by rfl⟩ : syracuseStep 1657901 = 621713) (by norm_num)
theorem B1657925 : Blo 1104625 1657925 := bbase (se 4 (by rfl) ⟨155430, by rfl⟩ : syracuseStep 1657925 = 310861) (by norm_num)
theorem B1657949 : Blo 1104625 1657949 := bbase (se 3 (by rfl) ⟨310865, by rfl⟩ : syracuseStep 1657949 = 621731) (by norm_num)
theorem B1657973 : Blo 1104625 1657973 := bbase (se 5 (by rfl) ⟨77717, by rfl⟩ : syracuseStep 1657973 = 155435) (by norm_num)
theorem B1657997 : Blo 1104625 1657997 := bbase (se 3 (by rfl) ⟨310874, by rfl⟩ : syracuseStep 1657997 = 621749) (by norm_num)
theorem B1658021 : Blo 1104625 1658021 := bbase (se 4 (by rfl) ⟨155439, by rfl⟩ : syracuseStep 1658021 = 310879) (by norm_num)
theorem B1658045 : Blo 1104625 1658045 := bbase (se 3 (by rfl) ⟨310883, by rfl⟩ : syracuseStep 1658045 = 621767) (by norm_num)
theorem B1658069 : Blo 1104625 1658069 := bbase (se 7 (by rfl) ⟨19430, by rfl⟩ : syracuseStep 1658069 = 38861) (by norm_num)
theorem B19188949 : Blo 1104625 19188949 := bbase (se 7 (by rfl) ⟨224870, by rfl⟩ : syracuseStep 19188949 = 449741) (by norm_num)
theorem B3788005 : Blo 1104625 3788005 := bbase (se 4 (by rfl) ⟨355125, by rfl⟩ : syracuseStep 3788005 = 710251) (by norm_num)
theorem B1658093 : Blo 1104625 1658093 := bbase (se 3 (by rfl) ⟨310892, by rfl⟩ : syracuseStep 1658093 = 621785) (by norm_num)
theorem B1330429 : Blo 1104625 1330429 := bbase (se 3 (by rfl) ⟨249455, by rfl⟩ : syracuseStep 1330429 = 498911) (by norm_num)
theorem B2804989 : Blo 1104625 2804989 := bbase (se 3 (by rfl) ⟨525935, by rfl⟩ : syracuseStep 2804989 = 1051871) (by norm_num)
theorem B1658117 : Blo 1104625 1658117 := bbase (se 4 (by rfl) ⟨155448, by rfl⟩ : syracuseStep 1658117 = 310897) (by norm_num)
theorem B1658141 : Blo 1104625 1658141 := bbase (se 3 (by rfl) ⟨310901, by rfl⟩ : syracuseStep 1658141 = 621803) (by norm_num)
theorem B1658165 : Blo 1104625 1658165 := bbase (se 5 (by rfl) ⟨77726, by rfl⟩ : syracuseStep 1658165 = 155453) (by norm_num)
theorem B1658189 : Blo 1104625 1658189 := bbase (se 3 (by rfl) ⟨310910, by rfl⟩ : syracuseStep 1658189 = 621821) (by norm_num)
theorem B1658213 : Blo 1104625 1658213 := bbase (se 4 (by rfl) ⟨155457, by rfl⟩ : syracuseStep 1658213 = 310915) (by norm_num)
theorem B2805101 : Blo 1104625 2805101 := bbase (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) (by norm_num)
theorem B1658237 : Blo 1104625 1658237 := bbase (se 3 (by rfl) ⟨310919, by rfl⟩ : syracuseStep 1658237 = 621839) (by norm_num)
theorem B1658261 : Blo 1104625 1658261 := bbase (se 6 (by rfl) ⟨38865, by rfl⟩ : syracuseStep 1658261 = 77731) (by norm_num)
theorem B6311317 : Blo 1104625 6311317 := bbase (se 6 (by rfl) ⟨147921, by rfl⟩ : syracuseStep 6311317 = 295843) (by norm_num)
theorem B1658285 : Blo 1104625 1658285 := bbase (se 3 (by rfl) ⟨310928, by rfl⟩ : syracuseStep 1658285 = 621857) (by norm_num)
theorem B1658309 : Blo 1104625 1658309 := bbase (se 4 (by rfl) ⟨155466, by rfl⟩ : syracuseStep 1658309 = 310933) (by norm_num)
theorem B1658333 : Blo 1104625 1658333 := bbase (se 3 (by rfl) ⟨310937, by rfl⟩ : syracuseStep 1658333 = 621875) (by norm_num)
theorem B1658357 : Blo 1104625 1658357 := bbase (se 5 (by rfl) ⟨77735, by rfl⟩ : syracuseStep 1658357 = 155471) (by norm_num)
theorem B1658381 : Blo 1104625 1658381 := bbase (se 3 (by rfl) ⟨310946, by rfl⟩ : syracuseStep 1658381 = 621893) (by norm_num)
theorem B4312597 : Blo 1104625 4312597 := bbase (se 6 (by rfl) ⟨101076, by rfl⟩ : syracuseStep 4312597 = 202153) (by norm_num)
theorem B1658405 : Blo 1104625 1658405 := bbase (se 4 (by rfl) ⟨155475, by rfl⟩ : syracuseStep 1658405 = 310951) (by norm_num)
theorem B2805293 : Blo 1104625 2805293 := bbase (se 3 (by rfl) ⟨525992, by rfl⟩ : syracuseStep 2805293 = 1051985) (by norm_num)
theorem B1658429 : Blo 1104625 1658429 := bbase (se 3 (by rfl) ⟨310955, by rfl⟩ : syracuseStep 1658429 = 621911) (by norm_num)
theorem B1658453 : Blo 1104625 1658453 := bbase (se 8 (by rfl) ⟨9717, by rfl⟩ : syracuseStep 1658453 = 19435) (by norm_num)
theorem B6475349 : Blo 1104625 6475349 := bbase (se 8 (by rfl) ⟨37941, by rfl⟩ : syracuseStep 6475349 = 75883) (by norm_num)
theorem B1658477 : Blo 1104625 1658477 := bbase (se 3 (by rfl) ⟨310964, by rfl⟩ : syracuseStep 1658477 = 621929) (by norm_num)
theorem B1658501 : Blo 1104625 1658501 := bbase (se 4 (by rfl) ⟨155484, by rfl⟩ : syracuseStep 1658501 = 310969) (by norm_num)
theorem B1658525 : Blo 1104625 1658525 := bbase (se 3 (by rfl) ⟨310973, by rfl⟩ : syracuseStep 1658525 = 621947) (by norm_num)
theorem B1658549 : Blo 1104625 1658549 := bbase (se 5 (by rfl) ⟨77744, by rfl⟩ : syracuseStep 1658549 = 155489) (by norm_num)
theorem B1560253 : Blo 1104625 1560253 := bbase (se 3 (by rfl) ⟨292547, by rfl⟩ : syracuseStep 1560253 = 585095) (by norm_num)
theorem B1658573 : Blo 1104625 1658573 := bbase (se 3 (by rfl) ⟨310982, by rfl⟩ : syracuseStep 1658573 = 621965) (by norm_num)
theorem B1658597 : Blo 1104625 1658597 := bbase (se 4 (by rfl) ⟨155493, by rfl⟩ : syracuseStep 1658597 = 310987) (by norm_num)
theorem B1658621 : Blo 1104625 1658621 := bbase (se 3 (by rfl) ⟨310991, by rfl⟩ : syracuseStep 1658621 = 621983) (by norm_num)
theorem B1658645 : Blo 1104625 1658645 := bbase (se 6 (by rfl) ⟨38874, by rfl⟩ : syracuseStep 1658645 = 77749) (by norm_num)
theorem B1658669 : Blo 1104625 1658669 := bbase (se 3 (by rfl) ⟨311000, by rfl⟩ : syracuseStep 1658669 = 622001) (by norm_num)
theorem B1658693 : Blo 1104625 1658693 := bbase (se 4 (by rfl) ⟨155502, by rfl⟩ : syracuseStep 1658693 = 311005) (by norm_num)
theorem B1658717 : Blo 1104625 1658717 := bbase (se 3 (by rfl) ⟨311009, by rfl⟩ : syracuseStep 1658717 = 622019) (by norm_num)
theorem B1199965 : Blo 1104625 1199965 := bbase (se 3 (by rfl) ⟨224993, by rfl⟩ : syracuseStep 1199965 = 449987) (by norm_num)
theorem B1658741 : Blo 1104625 1658741 := bbase (se 5 (by rfl) ⟨77753, by rfl⟩ : syracuseStep 1658741 = 155507) (by norm_num)
theorem B2805637 : Blo 1104625 2805637 := bbase (se 4 (by rfl) ⟨263028, by rfl⟩ : syracuseStep 2805637 = 526057) (by norm_num)
theorem B1658765 : Blo 1104625 1658765 := bbase (se 3 (by rfl) ⟨311018, by rfl⟩ : syracuseStep 1658765 = 622037) (by norm_num)
theorem B1658789 : Blo 1104625 1658789 := bbase (se 4 (by rfl) ⟨155511, by rfl⟩ : syracuseStep 1658789 = 311023) (by norm_num)
theorem B1658813 : Blo 1104625 1658813 := bbase (se 3 (by rfl) ⟨311027, by rfl⟩ : syracuseStep 1658813 = 622055) (by norm_num)
theorem B1658837 : Blo 1104625 1658837 := bbase (se 7 (by rfl) ⟨19439, by rfl⟩ : syracuseStep 1658837 = 38879) (by norm_num)
theorem B1658861 : Blo 1104625 1658861 := bbase (se 3 (by rfl) ⟨311036, by rfl⟩ : syracuseStep 1658861 = 622073) (by norm_num)
theorem B2805749 : Blo 1104625 2805749 := bbase (se 5 (by rfl) ⟨131519, by rfl⟩ : syracuseStep 2805749 = 263039) (by norm_num)
theorem B1658885 : Blo 1104625 1658885 := bbase (se 4 (by rfl) ⟨155520, by rfl⟩ : syracuseStep 1658885 = 311041) (by norm_num)
theorem B1658909 : Blo 1104625 1658909 := bbase (se 3 (by rfl) ⟨311045, by rfl⟩ : syracuseStep 1658909 = 622091) (by norm_num)
theorem B1658933 : Blo 1104625 1658933 := bbase (se 5 (by rfl) ⟨77762, by rfl⟩ : syracuseStep 1658933 = 155525) (by norm_num)
theorem B1658957 : Blo 1104625 1658957 := bbase (se 3 (by rfl) ⟨311054, by rfl⟩ : syracuseStep 1658957 = 622109) (by norm_num)
theorem B1658981 : Blo 1104625 1658981 := bbase (se 4 (by rfl) ⟨155529, by rfl⟩ : syracuseStep 1658981 = 311059) (by norm_num)
theorem B1659005 : Blo 1104625 1659005 := bbase (se 3 (by rfl) ⟨311063, by rfl⟩ : syracuseStep 1659005 = 622127) (by norm_num)
theorem B1659029 : Blo 1104625 1659029 := bbase (se 6 (by rfl) ⟨38883, by rfl⟩ : syracuseStep 1659029 = 77767) (by norm_num)
theorem B1659053 : Blo 1104625 1659053 := bbase (se 3 (by rfl) ⟨311072, by rfl⟩ : syracuseStep 1659053 = 622145) (by norm_num)
theorem B2805941 : Blo 1104625 2805941 := bbase (se 5 (by rfl) ⟨131528, by rfl⟩ : syracuseStep 2805941 = 263057) (by norm_num)
theorem B1659077 : Blo 1104625 1659077 := bbase (se 4 (by rfl) ⟨155538, by rfl⟩ : syracuseStep 1659077 = 311077) (by norm_num)
theorem B1659101 : Blo 1104625 1659101 := bbase (se 3 (by rfl) ⟨311081, by rfl⟩ : syracuseStep 1659101 = 622163) (by norm_num)
theorem B1659125 : Blo 1104625 1659125 := bbase (se 5 (by rfl) ⟨77771, by rfl⟩ : syracuseStep 1659125 = 155543) (by norm_num)
theorem B1659149 : Blo 1104625 1659149 := bbase (se 3 (by rfl) ⟨311090, by rfl⟩ : syracuseStep 1659149 = 622181) (by norm_num)
theorem B1659173 : Blo 1104625 1659173 := bbase (se 4 (by rfl) ⟨155547, by rfl⟩ : syracuseStep 1659173 = 311095) (by norm_num)
theorem B1659197 : Blo 1104625 1659197 := bbase (se 3 (by rfl) ⟨311099, by rfl⟩ : syracuseStep 1659197 = 622199) (by norm_num)
theorem B1659221 : Blo 1104625 1659221 := bbase (se 10 (by rfl) ⟨2430, by rfl⟩ : syracuseStep 1659221 = 4861) (by norm_num)
theorem B1659245 : Blo 1104625 1659245 := bbase (se 3 (by rfl) ⟨311108, by rfl⟩ : syracuseStep 1659245 = 622217) (by norm_num)
theorem B1659269 : Blo 1104625 1659269 := bbase (se 4 (by rfl) ⟨155556, by rfl⟩ : syracuseStep 1659269 = 311113) (by norm_num)
theorem B1659293 : Blo 1104625 1659293 := bbase (se 3 (by rfl) ⟨311117, by rfl⟩ : syracuseStep 1659293 = 622235) (by norm_num)
theorem B5394853 : Blo 1104625 5394853 := bbase (se 4 (by rfl) ⟨505767, by rfl⟩ : syracuseStep 5394853 = 1011535) (by norm_num)
theorem B1659317 : Blo 1104625 1659317 := bbase (se 5 (by rfl) ⟨77780, by rfl⟩ : syracuseStep 1659317 = 155561) (by norm_num)
theorem B1659341 : Blo 1104625 1659341 := bbase (se 3 (by rfl) ⟨311126, by rfl⟩ : syracuseStep 1659341 = 622253) (by norm_num)
theorem B1659365 : Blo 1104625 1659365 := bbase (se 4 (by rfl) ⟨155565, by rfl⟩ : syracuseStep 1659365 = 311131) (by norm_num)
theorem B1659389 : Blo 1104625 1659389 := bbase (se 3 (by rfl) ⟨311135, by rfl⟩ : syracuseStep 1659389 = 622271) (by norm_num)
theorem B1659413 : Blo 1104625 1659413 := bbase (se 6 (by rfl) ⟨38892, by rfl⟩ : syracuseStep 1659413 = 77785) (by norm_num)
theorem B1659437 : Blo 1104625 1659437 := bbase (se 3 (by rfl) ⟨311144, by rfl⟩ : syracuseStep 1659437 = 622289) (by norm_num)
theorem B1659461 : Blo 1104625 1659461 := bbase (se 4 (by rfl) ⟨155574, by rfl⟩ : syracuseStep 1659461 = 311149) (by norm_num)
theorem B1659485 : Blo 1104625 1659485 := bbase (se 3 (by rfl) ⟨311153, by rfl⟩ : syracuseStep 1659485 = 622307) (by norm_num)
theorem B1331813 : Blo 1104625 1331813 := bbase (se 4 (by rfl) ⟨124857, by rfl⟩ : syracuseStep 1331813 = 249715) (by norm_num)
theorem B1659509 : Blo 1104625 1659509 := bbase (se 5 (by rfl) ⟨77789, by rfl⟩ : syracuseStep 1659509 = 155579) (by norm_num)
theorem B1659533 : Blo 1104625 1659533 := bbase (se 3 (by rfl) ⟨311162, by rfl⟩ : syracuseStep 1659533 = 622325) (by norm_num)
theorem B1659557 : Blo 1104625 1659557 := bbase (se 4 (by rfl) ⟨155583, by rfl⟩ : syracuseStep 1659557 = 311167) (by norm_num)
theorem B8966837 : Blo 1104625 8966837 := bbase (se 5 (by rfl) ⟨420320, by rfl⟩ : syracuseStep 8966837 = 840641) (by norm_num)
theorem B1659581 : Blo 1104625 1659581 := bbase (se 3 (by rfl) ⟨311171, by rfl⟩ : syracuseStep 1659581 = 622343) (by norm_num)
theorem B1659605 : Blo 1104625 1659605 := bbase (se 7 (by rfl) ⟨19448, by rfl⟩ : syracuseStep 1659605 = 38897) (by norm_num)
theorem B1659629 : Blo 1104625 1659629 := bbase (se 3 (by rfl) ⟨311180, by rfl⟩ : syracuseStep 1659629 = 622361) (by norm_num)
theorem B1659653 : Blo 1104625 1659653 := bbase (se 4 (by rfl) ⟨155592, by rfl⟩ : syracuseStep 1659653 = 311185) (by norm_num)
theorem B1659677 : Blo 1104625 1659677 := bbase (se 3 (by rfl) ⟨311189, by rfl⟩ : syracuseStep 1659677 = 622379) (by norm_num)
theorem B1659701 : Blo 1104625 1659701 := bbase (se 5 (by rfl) ⟨77798, by rfl⟩ : syracuseStep 1659701 = 155597) (by norm_num)
theorem B1659725 : Blo 1104625 1659725 := bbase (se 3 (by rfl) ⟨311198, by rfl⟩ : syracuseStep 1659725 = 622397) (by norm_num)
theorem B1659749 : Blo 1104625 1659749 := bbase (se 4 (by rfl) ⟨155601, by rfl⟩ : syracuseStep 1659749 = 311203) (by norm_num)
theorem B1659773 : Blo 1104625 1659773 := bbase (se 3 (by rfl) ⟨311207, by rfl⟩ : syracuseStep 1659773 = 622415) (by norm_num)
theorem B1659797 : Blo 1104625 1659797 := bbase (se 6 (by rfl) ⟨38901, by rfl⟩ : syracuseStep 1659797 = 77803) (by norm_num)
theorem B1659821 : Blo 1104625 1659821 := bbase (se 3 (by rfl) ⟨311216, by rfl⟩ : syracuseStep 1659821 = 622433) (by norm_num)
theorem B1659845 : Blo 1104625 1659845 := bbase (se 4 (by rfl) ⟨155610, by rfl⟩ : syracuseStep 1659845 = 311221) (by norm_num)
theorem B1659869 : Blo 1104625 1659869 := bbase (se 3 (by rfl) ⟨311225, by rfl⟩ : syracuseStep 1659869 = 622451) (by norm_num)
theorem B1659893 : Blo 1104625 1659893 := bbase (se 5 (by rfl) ⟨77807, by rfl⟩ : syracuseStep 1659893 = 155615) (by norm_num)
theorem B1659917 : Blo 1104625 1659917 := bbase (se 3 (by rfl) ⟨311234, by rfl⟩ : syracuseStep 1659917 = 622469) (by norm_num)
theorem B1659941 : Blo 1104625 1659941 := bbase (se 4 (by rfl) ⟨155619, by rfl⟩ : syracuseStep 1659941 = 311239) (by norm_num)
theorem B1659965 : Blo 1104625 1659965 := bbase (se 3 (by rfl) ⟨311243, by rfl⟩ : syracuseStep 1659965 = 622487) (by norm_num)
theorem B1659989 : Blo 1104625 1659989 := bbase (se 8 (by rfl) ⟨9726, by rfl⟩ : syracuseStep 1659989 = 19453) (by norm_num)
theorem B1660013 : Blo 1104625 1660013 := bbase (se 3 (by rfl) ⟨311252, by rfl⟩ : syracuseStep 1660013 = 622505) (by norm_num)
theorem B8410229 : Blo 1104625 8410229 := bbase (se 5 (by rfl) ⟨394229, by rfl⟩ : syracuseStep 8410229 = 788459) (by norm_num)
theorem B1135745 : Blo 1104625 1135745 := bbase (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) (by norm_num)
theorem B1660037 : Blo 1104625 1660037 := bbase (se 4 (by rfl) ⟨155628, by rfl⟩ : syracuseStep 1660037 = 311257) (by norm_num)
theorem B1660061 : Blo 1104625 1660061 := bbase (se 3 (by rfl) ⟨311261, by rfl⟩ : syracuseStep 1660061 = 622523) (by norm_num)
theorem B1660085 : Blo 1104625 1660085 := bbase (se 5 (by rfl) ⟨77816, by rfl⟩ : syracuseStep 1660085 = 155633) (by norm_num)
theorem B1660109 : Blo 1104625 1660109 := bbase (se 3 (by rfl) ⟨311270, by rfl⟩ : syracuseStep 1660109 = 622541) (by norm_num)
theorem B1660133 : Blo 1104625 1660133 := bbase (se 4 (by rfl) ⟨155637, by rfl⟩ : syracuseStep 1660133 = 311275) (by norm_num)
theorem B1660157 : Blo 1104625 1660157 := bbase (se 3 (by rfl) ⟨311279, by rfl⟩ : syracuseStep 1660157 = 622559) (by norm_num)
theorem B1660181 : Blo 1104625 1660181 := bbase (se 6 (by rfl) ⟨38910, by rfl⟩ : syracuseStep 1660181 = 77821) (by norm_num)
theorem B1660205 : Blo 1104625 1660205 := bbase (se 3 (by rfl) ⟨311288, by rfl⟩ : syracuseStep 1660205 = 622577) (by norm_num)
theorem B1660229 : Blo 1104625 1660229 := bbase (se 4 (by rfl) ⟨155646, by rfl⟩ : syracuseStep 1660229 = 311293) (by norm_num)
theorem B6313301 : Blo 1104625 6313301 := bbase (se 16 (by rfl) ⟨144, by rfl⟩ : syracuseStep 6313301 = 289) (by norm_num)
theorem B1660253 : Blo 1104625 1660253 := bbase (se 3 (by rfl) ⟨311297, by rfl⟩ : syracuseStep 1660253 = 622595) (by norm_num)
theorem B1660277 : Blo 1104625 1660277 := bbase (se 5 (by rfl) ⟨77825, by rfl⟩ : syracuseStep 1660277 = 155651) (by norm_num)
theorem B1660301 : Blo 1104625 1660301 := bbase (se 3 (by rfl) ⟨311306, by rfl⟩ : syracuseStep 1660301 = 622613) (by norm_num)
theorem B1398161 : Blo 1104625 1398161 := bbase (se 2 (by rfl) ⟨524310, by rfl⟩ : syracuseStep 1398161 = 1048621) (by norm_num)
theorem B1660325 : Blo 1104625 1660325 := bbase (se 4 (by rfl) ⟨155655, by rfl⟩ : syracuseStep 1660325 = 311311) (by norm_num)
theorem B1660349 : Blo 1104625 1660349 := bbase (se 3 (by rfl) ⟨311315, by rfl⟩ : syracuseStep 1660349 = 622631) (by norm_num)
theorem B1398217 : Blo 1104625 1398217 := bbase (se 2 (by rfl) ⟨524331, by rfl⟩ : syracuseStep 1398217 = 1048663) (by norm_num)
theorem B1660373 : Blo 1104625 1660373 := bbase (se 7 (by rfl) ⟨19457, by rfl⟩ : syracuseStep 1660373 = 38915) (by norm_num)
theorem B1496549 : Blo 1104625 1496549 := bbase (se 4 (by rfl) ⟨140301, by rfl⟩ : syracuseStep 1496549 = 280603) (by norm_num)
theorem B1660397 : Blo 1104625 1660397 := bbase (se 3 (by rfl) ⟨311324, by rfl⟩ : syracuseStep 1660397 = 622649) (by norm_num)
theorem B1660421 : Blo 1104625 1660421 := bbase (se 4 (by rfl) ⟨155664, by rfl⟩ : syracuseStep 1660421 = 311329) (by norm_num)
theorem B1660445 : Blo 1104625 1660445 := bbase (se 3 (by rfl) ⟨311333, by rfl⟩ : syracuseStep 1660445 = 622667) (by norm_num)
theorem B1398313 : Blo 1104625 1398313 := bbase (se 2 (by rfl) ⟨524367, by rfl⟩ : syracuseStep 1398313 = 1048735) (by norm_num)
theorem B1660469 : Blo 1104625 1660469 := bbase (se 5 (by rfl) ⟨77834, by rfl⟩ : syracuseStep 1660469 = 155669) (by norm_num)
theorem B1660493 : Blo 1104625 1660493 := bbase (se 3 (by rfl) ⟨311342, by rfl⟩ : syracuseStep 1660493 = 622685) (by norm_num)
theorem B1660517 : Blo 1104625 1660517 := bbase (se 4 (by rfl) ⟨155673, by rfl⟩ : syracuseStep 1660517 = 311347) (by norm_num)
theorem B1660541 : Blo 1104625 1660541 := bbase (se 3 (by rfl) ⟨311351, by rfl⟩ : syracuseStep 1660541 = 622703) (by norm_num)
theorem B5592725 : Blo 1104625 5592725 := bbase (se 6 (by rfl) ⟨131079, by rfl⟩ : syracuseStep 5592725 = 262159) (by norm_num)
theorem B1660565 : Blo 1104625 1660565 := bbase (se 6 (by rfl) ⟨38919, by rfl⟩ : syracuseStep 1660565 = 77839) (by norm_num)
theorem B1660589 : Blo 1104625 1660589 := bbase (se 3 (by rfl) ⟨311360, by rfl⟩ : syracuseStep 1660589 = 622721) (by norm_num)
theorem B1660613 : Blo 1104625 1660613 := bbase (se 4 (by rfl) ⟨155682, by rfl⟩ : syracuseStep 1660613 = 311365) (by norm_num)
theorem B1398485 : Blo 1104625 1398485 := bbase (se 7 (by rfl) ⟨16388, by rfl⟩ : syracuseStep 1398485 = 32777) (by norm_num)
theorem B1660637 : Blo 1104625 1660637 := bbase (se 3 (by rfl) ⟨311369, by rfl⟩ : syracuseStep 1660637 = 622739) (by norm_num)
theorem B1660661 : Blo 1104625 1660661 := bbase (se 5 (by rfl) ⟨77843, by rfl⟩ : syracuseStep 1660661 = 155687) (by norm_num)
theorem B1398541 : Blo 1104625 1398541 := bbase (se 3 (by rfl) ⟨262226, by rfl⟩ : syracuseStep 1398541 = 524453) (by norm_num)
theorem B1660685 : Blo 1104625 1660685 := bbase (se 3 (by rfl) ⟨311378, by rfl⟩ : syracuseStep 1660685 = 622757) (by norm_num)
theorem B1660709 : Blo 1104625 1660709 := bbase (se 4 (by rfl) ⟨155691, by rfl⟩ : syracuseStep 1660709 = 311383) (by norm_num)
theorem B1660733 : Blo 1104625 1660733 := bbase (se 3 (by rfl) ⟨311387, by rfl⟩ : syracuseStep 1660733 = 622775) (by norm_num)
theorem B1660757 : Blo 1104625 1660757 := bbase (se 9 (by rfl) ⟨4865, by rfl⟩ : syracuseStep 1660757 = 9731) (by norm_num)
theorem B1398637 : Blo 1104625 1398637 := bbase (se 3 (by rfl) ⟨262244, by rfl⟩ : syracuseStep 1398637 = 524489) (by norm_num)
theorem B1660781 : Blo 1104625 1660781 := bbase (se 3 (by rfl) ⟨311396, by rfl⟩ : syracuseStep 1660781 = 622793) (by norm_num)
theorem B1660805 : Blo 1104625 1660805 := bbase (se 4 (by rfl) ⟨155700, by rfl⟩ : syracuseStep 1660805 = 311401) (by norm_num)
theorem B1660829 : Blo 1104625 1660829 := bbase (se 3 (by rfl) ⟨311405, by rfl⟩ : syracuseStep 1660829 = 622811) (by norm_num)
theorem B1660853 : Blo 1104625 1660853 := bbase (se 5 (by rfl) ⟨77852, by rfl⟩ : syracuseStep 1660853 = 155705) (by norm_num)
theorem B1660877 : Blo 1104625 1660877 := bbase (se 3 (by rfl) ⟨311414, by rfl⟩ : syracuseStep 1660877 = 622829) (by norm_num)
theorem B1660901 : Blo 1104625 1660901 := bbase (se 4 (by rfl) ⟨155709, by rfl⟩ : syracuseStep 1660901 = 311419) (by norm_num)
theorem B1660925 : Blo 1104625 1660925 := bbase (se 3 (by rfl) ⟨311423, by rfl⟩ : syracuseStep 1660925 = 622847) (by norm_num)
theorem B1660949 : Blo 1104625 1660949 := bbase (se 6 (by rfl) ⟨38928, by rfl⟩ : syracuseStep 1660949 = 77857) (by norm_num)
theorem B5986325 : Blo 1104625 5986325 := bbase (se 6 (by rfl) ⟨140304, by rfl⟩ : syracuseStep 5986325 = 280609) (by norm_num)
theorem B1398809 : Blo 1104625 1398809 := bbase (se 2 (by rfl) ⟨524553, by rfl⟩ : syracuseStep 1398809 = 1049107) (by norm_num)
theorem B1660973 : Blo 1104625 1660973 := bbase (se 3 (by rfl) ⟨311432, by rfl⟩ : syracuseStep 1660973 = 622865) (by norm_num)
theorem B1660997 : Blo 1104625 1660997 := bbase (se 4 (by rfl) ⟨155718, by rfl⟩ : syracuseStep 1660997 = 311437) (by norm_num)
theorem B1398865 : Blo 1104625 1398865 := bbase (se 2 (by rfl) ⟨524574, by rfl⟩ : syracuseStep 1398865 = 1049149) (by norm_num)
theorem B1661021 : Blo 1104625 1661021 := bbase (se 3 (by rfl) ⟨311441, by rfl⟩ : syracuseStep 1661021 = 622883) (by norm_num)
theorem B1661045 : Blo 1104625 1661045 := bbase (se 5 (by rfl) ⟨77861, by rfl⟩ : syracuseStep 1661045 = 155723) (by norm_num)
theorem B1661069 : Blo 1104625 1661069 := bbase (se 3 (by rfl) ⟨311450, by rfl⟩ : syracuseStep 1661069 = 622901) (by norm_num)
theorem B1661093 : Blo 1104625 1661093 := bbase (se 4 (by rfl) ⟨155727, by rfl⟩ : syracuseStep 1661093 = 311455) (by norm_num)
theorem B1398961 : Blo 1104625 1398961 := bbase (se 2 (by rfl) ⟨524610, by rfl⟩ : syracuseStep 1398961 = 1049221) (by norm_num)
theorem B1661117 : Blo 1104625 1661117 := bbase (se 3 (by rfl) ⟨311459, by rfl⟩ : syracuseStep 1661117 = 622919) (by norm_num)
theorem B1661141 : Blo 1104625 1661141 := bbase (se 7 (by rfl) ⟨19466, by rfl⟩ : syracuseStep 1661141 = 38933) (by norm_num)
theorem B1661165 : Blo 1104625 1661165 := bbase (se 3 (by rfl) ⟨311468, by rfl⟩ : syracuseStep 1661165 = 622937) (by norm_num)
theorem B1661189 : Blo 1104625 1661189 := bbase (se 4 (by rfl) ⟨155736, by rfl⟩ : syracuseStep 1661189 = 311473) (by norm_num)
theorem B1661213 : Blo 1104625 1661213 := bbase (se 3 (by rfl) ⟨311477, by rfl⟩ : syracuseStep 1661213 = 622955) (by norm_num)
theorem B1661237 : Blo 1104625 1661237 := bbase (se 5 (by rfl) ⟨77870, by rfl⟩ : syracuseStep 1661237 = 155741) (by norm_num)
theorem B1661261 : Blo 1104625 1661261 := bbase (se 3 (by rfl) ⟨311486, by rfl⟩ : syracuseStep 1661261 = 622973) (by norm_num)
theorem B1399133 : Blo 1104625 1399133 := bbase (se 3 (by rfl) ⟨262337, by rfl⟩ : syracuseStep 1399133 = 524675) (by norm_num)
theorem B1661285 : Blo 1104625 1661285 := bbase (se 4 (by rfl) ⟨155745, by rfl⟩ : syracuseStep 1661285 = 311491) (by norm_num)
theorem B1661309 : Blo 1104625 1661309 := bbase (se 3 (by rfl) ⟨311495, by rfl⟩ : syracuseStep 1661309 = 622991) (by norm_num)
theorem B1399189 : Blo 1104625 1399189 := bbase (se 6 (by rfl) ⟨32793, by rfl⟩ : syracuseStep 1399189 = 65587) (by norm_num)
theorem B1661333 : Blo 1104625 1661333 := bbase (se 6 (by rfl) ⟨38937, by rfl⟩ : syracuseStep 1661333 = 77875) (by norm_num)
theorem B1661357 : Blo 1104625 1661357 := bbase (se 3 (by rfl) ⟨311504, by rfl⟩ : syracuseStep 1661357 = 623009) (by norm_num)
theorem B1497533 : Blo 1104625 1497533 := bbase (se 3 (by rfl) ⟨280787, by rfl⟩ : syracuseStep 1497533 = 561575) (by norm_num)
theorem B1661381 : Blo 1104625 1661381 := bbase (se 4 (by rfl) ⟨155754, by rfl⟩ : syracuseStep 1661381 = 311509) (by norm_num)
theorem B1661405 : Blo 1104625 1661405 := bbase (se 3 (by rfl) ⟨311513, by rfl⟩ : syracuseStep 1661405 = 623027) (by norm_num)
theorem B1399285 : Blo 1104625 1399285 := bbase (se 5 (by rfl) ⟨65591, by rfl⟩ : syracuseStep 1399285 = 131183) (by norm_num)
theorem B1661429 : Blo 1104625 1661429 := bbase (se 5 (by rfl) ⟨77879, by rfl⟩ : syracuseStep 1661429 = 155759) (by norm_num)
theorem B1661453 : Blo 1104625 1661453 := bbase (se 3 (by rfl) ⟨311522, by rfl⟩ : syracuseStep 1661453 = 623045) (by norm_num)
theorem B1661477 : Blo 1104625 1661477 := bbase (se 4 (by rfl) ⟨155763, by rfl⟩ : syracuseStep 1661477 = 311527) (by norm_num)
theorem B1661501 : Blo 1104625 1661501 := bbase (se 3 (by rfl) ⟨311531, by rfl⟩ : syracuseStep 1661501 = 623063) (by norm_num)
theorem B1661525 : Blo 1104625 1661525 := bbase (se 8 (by rfl) ⟨9735, by rfl⟩ : syracuseStep 1661525 = 19471) (by norm_num)
theorem B1661549 : Blo 1104625 1661549 := bbase (se 3 (by rfl) ⟨311540, by rfl⟩ : syracuseStep 1661549 = 623081) (by norm_num)
theorem B1661573 : Blo 1104625 1661573 := bbase (se 4 (by rfl) ⟨155772, by rfl⟩ : syracuseStep 1661573 = 311545) (by norm_num)
theorem B1661597 : Blo 1104625 1661597 := bbase (se 3 (by rfl) ⟨311549, by rfl⟩ : syracuseStep 1661597 = 623099) (by norm_num)
theorem B1399457 : Blo 1104625 1399457 := bbase (se 2 (by rfl) ⟨524796, by rfl⟩ : syracuseStep 1399457 = 1049593) (by norm_num)
theorem B1661621 : Blo 1104625 1661621 := bbase (se 5 (by rfl) ⟨77888, by rfl⟩ : syracuseStep 1661621 = 155777) (by norm_num)
theorem B1661645 : Blo 1104625 1661645 := bbase (se 3 (by rfl) ⟨311558, by rfl⟩ : syracuseStep 1661645 = 623117) (by norm_num)
theorem B1399513 : Blo 1104625 1399513 := bbase (se 2 (by rfl) ⟨524817, by rfl⟩ : syracuseStep 1399513 = 1049635) (by norm_num)
theorem B1891045 : Blo 1104625 1891045 := bbase (se 4 (by rfl) ⟨177285, by rfl⟩ : syracuseStep 1891045 = 354571) (by norm_num)
theorem B1661669 : Blo 1104625 1661669 := bbase (se 4 (by rfl) ⟨155781, by rfl⟩ : syracuseStep 1661669 = 311563) (by norm_num)
theorem B1661693 : Blo 1104625 1661693 := bbase (se 3 (by rfl) ⟨311567, by rfl⟩ : syracuseStep 1661693 = 623135) (by norm_num)
theorem B1661717 : Blo 1104625 1661717 := bbase (se 6 (by rfl) ⟨38946, by rfl⟩ : syracuseStep 1661717 = 77893) (by norm_num)
theorem B1661741 : Blo 1104625 1661741 := bbase (se 3 (by rfl) ⟨311576, by rfl⟩ : syracuseStep 1661741 = 623153) (by norm_num)
theorem B1399609 : Blo 1104625 1399609 := bbase (se 2 (by rfl) ⟨524853, by rfl⟩ : syracuseStep 1399609 = 1049707) (by norm_num)
theorem B2841413 : Blo 1104625 2841413 := bbase (se 4 (by rfl) ⟨266382, by rfl⟩ : syracuseStep 2841413 = 532765) (by norm_num)
theorem B1661765 : Blo 1104625 1661765 := bbase (se 4 (by rfl) ⟨155790, by rfl⟩ : syracuseStep 1661765 = 311581) (by norm_num)
theorem B1661789 : Blo 1104625 1661789 := bbase (se 3 (by rfl) ⟨311585, by rfl⟩ : syracuseStep 1661789 = 623171) (by norm_num)
theorem B1661813 : Blo 1104625 1661813 := bbase (se 5 (by rfl) ⟨77897, by rfl⟩ : syracuseStep 1661813 = 155795) (by norm_num)
theorem B1661837 : Blo 1104625 1661837 := bbase (se 3 (by rfl) ⟨311594, by rfl⟩ : syracuseStep 1661837 = 623189) (by norm_num)
theorem B5594021 : Blo 1104625 5594021 := bbase (se 4 (by rfl) ⟨524439, by rfl⟩ : syracuseStep 5594021 = 1048879) (by norm_num)
theorem B1661861 : Blo 1104625 1661861 := bbase (se 4 (by rfl) ⟨155799, by rfl⟩ : syracuseStep 1661861 = 311599) (by norm_num)
theorem B1661885 : Blo 1104625 1661885 := bbase (se 3 (by rfl) ⟨311603, by rfl⟩ : syracuseStep 1661885 = 623207) (by norm_num)
theorem B1661909 : Blo 1104625 1661909 := bbase (se 7 (by rfl) ⟨19475, by rfl⟩ : syracuseStep 1661909 = 38951) (by norm_num)
theorem B1399781 : Blo 1104625 1399781 := bbase (se 4 (by rfl) ⟨131229, by rfl⟩ : syracuseStep 1399781 = 262459) (by norm_num)
theorem B1661933 : Blo 1104625 1661933 := bbase (se 3 (by rfl) ⟨311612, by rfl⟩ : syracuseStep 1661933 = 623225) (by norm_num)
theorem B1661957 : Blo 1104625 1661957 := bbase (se 4 (by rfl) ⟨155808, by rfl⟩ : syracuseStep 1661957 = 311617) (by norm_num)
theorem B1498117 : Blo 1104625 1498117 := bbase (se 4 (by rfl) ⟨140448, by rfl⟩ : syracuseStep 1498117 = 280897) (by norm_num)
theorem B1399837 : Blo 1104625 1399837 := bbase (se 3 (by rfl) ⟨262469, by rfl⟩ : syracuseStep 1399837 = 524939) (by norm_num)
theorem B1661981 : Blo 1104625 1661981 := bbase (se 3 (by rfl) ⟨311621, by rfl⟩ : syracuseStep 1661981 = 623243) (by norm_num)
theorem B1662005 : Blo 1104625 1662005 := bbase (se 5 (by rfl) ⟨77906, by rfl⟩ : syracuseStep 1662005 = 155813) (by norm_num)
theorem B1662029 : Blo 1104625 1662029 := bbase (se 3 (by rfl) ⟨311630, by rfl⟩ : syracuseStep 1662029 = 623261) (by norm_num)
theorem B86170709 : Blo 1104625 86170709 := bbase (se 8 (by rfl) ⟨504906, by rfl⟩ : syracuseStep 86170709 = 1009813) (by norm_num)
theorem B3988565 : Blo 1104625 3988565 := bbase (se 8 (by rfl) ⟨23370, by rfl⟩ : syracuseStep 3988565 = 46741) (by norm_num)
theorem B1662053 : Blo 1104625 1662053 := bbase (se 4 (by rfl) ⟨155817, by rfl⟩ : syracuseStep 1662053 = 311635) (by norm_num)
theorem B1399933 : Blo 1104625 1399933 := bbase (se 3 (by rfl) ⟨262487, by rfl⟩ : syracuseStep 1399933 = 524975) (by norm_num)
theorem B1662077 : Blo 1104625 1662077 := bbase (se 3 (by rfl) ⟨311639, by rfl⟩ : syracuseStep 1662077 = 623279) (by norm_num)
theorem B1662101 : Blo 1104625 1662101 := bbase (se 6 (by rfl) ⟨38955, by rfl⟩ : syracuseStep 1662101 = 77911) (by norm_num)
theorem B1662125 : Blo 1104625 1662125 := bbase (se 3 (by rfl) ⟨311648, by rfl⟩ : syracuseStep 1662125 = 623297) (by norm_num)
theorem B1662149 : Blo 1104625 1662149 := bbase (se 4 (by rfl) ⟨155826, by rfl⟩ : syracuseStep 1662149 = 311653) (by norm_num)
theorem B1662173 : Blo 1104625 1662173 := bbase (se 3 (by rfl) ⟨311657, by rfl⟩ : syracuseStep 1662173 = 623315) (by norm_num)
theorem B1662197 : Blo 1104625 1662197 := bbase (se 5 (by rfl) ⟨77915, by rfl⟩ : syracuseStep 1662197 = 155831) (by norm_num)
theorem B1662221 : Blo 1104625 1662221 := bbase (se 3 (by rfl) ⟨311666, by rfl⟩ : syracuseStep 1662221 = 623333) (by norm_num)
theorem B1662245 : Blo 1104625 1662245 := bbase (se 4 (by rfl) ⟨155835, by rfl⟩ : syracuseStep 1662245 = 311671) (by norm_num)
theorem B1400105 : Blo 1104625 1400105 := bbase (se 2 (by rfl) ⟨525039, by rfl⟩ : syracuseStep 1400105 = 1050079) (by norm_num)
theorem B1662269 : Blo 1104625 1662269 := bbase (se 3 (by rfl) ⟨311675, by rfl⟩ : syracuseStep 1662269 = 623351) (by norm_num)
theorem B1662293 : Blo 1104625 1662293 := bbase (se 11 (by rfl) ⟨1217, by rfl⟩ : syracuseStep 1662293 = 2435) (by norm_num)
theorem B1400161 : Blo 1104625 1400161 := bbase (se 2 (by rfl) ⟨525060, by rfl⟩ : syracuseStep 1400161 = 1050121) (by norm_num)
theorem B1662317 : Blo 1104625 1662317 := bbase (se 3 (by rfl) ⟨311684, by rfl⟩ : syracuseStep 1662317 = 623369) (by norm_num)
theorem B1662341 : Blo 1104625 1662341 := bbase (se 4 (by rfl) ⟨155844, by rfl⟩ : syracuseStep 1662341 = 311689) (by norm_num)
theorem B1662365 : Blo 1104625 1662365 := bbase (se 3 (by rfl) ⟨311693, by rfl⟩ : syracuseStep 1662365 = 623387) (by norm_num)
theorem B1662389 : Blo 1104625 1662389 := bbase (se 5 (by rfl) ⟨77924, by rfl⟩ : syracuseStep 1662389 = 155849) (by norm_num)
theorem B1400257 : Blo 1104625 1400257 := bbase (se 2 (by rfl) ⟨525096, by rfl⟩ : syracuseStep 1400257 = 1050193) (by norm_num)
theorem B1662413 : Blo 1104625 1662413 := bbase (se 3 (by rfl) ⟨311702, by rfl⟩ : syracuseStep 1662413 = 623405) (by norm_num)
theorem B1662437 : Blo 1104625 1662437 := bbase (se 4 (by rfl) ⟨155853, by rfl⟩ : syracuseStep 1662437 = 311707) (by norm_num)
theorem B1662461 : Blo 1104625 1662461 := bbase (se 3 (by rfl) ⟨311711, by rfl⟩ : syracuseStep 1662461 = 623423) (by norm_num)
theorem B1662485 : Blo 1104625 1662485 := bbase (se 6 (by rfl) ⟨38964, by rfl⟩ : syracuseStep 1662485 = 77929) (by norm_num)
theorem B1662509 : Blo 1104625 1662509 := bbase (se 3 (by rfl) ⟨311720, by rfl⟩ : syracuseStep 1662509 = 623441) (by norm_num)
theorem B1662533 : Blo 1104625 1662533 := bbase (se 4 (by rfl) ⟨155862, by rfl⟩ : syracuseStep 1662533 = 311725) (by norm_num)
theorem B1662557 : Blo 1104625 1662557 := bbase (se 3 (by rfl) ⟨311729, by rfl⟩ : syracuseStep 1662557 = 623459) (by norm_num)
theorem B1400429 : Blo 1104625 1400429 := bbase (se 3 (by rfl) ⟨262580, by rfl⟩ : syracuseStep 1400429 = 525161) (by norm_num)
theorem B1662581 : Blo 1104625 1662581 := bbase (se 5 (by rfl) ⟨77933, by rfl⟩ : syracuseStep 1662581 = 155867) (by norm_num)
theorem B1662605 : Blo 1104625 1662605 := bbase (se 3 (by rfl) ⟨311738, by rfl⟩ : syracuseStep 1662605 = 623477) (by norm_num)
theorem B1400485 : Blo 1104625 1400485 := bbase (se 4 (by rfl) ⟨131295, by rfl⟩ : syracuseStep 1400485 = 262591) (by norm_num)
theorem B1662629 : Blo 1104625 1662629 := bbase (se 4 (by rfl) ⟨155871, by rfl⟩ : syracuseStep 1662629 = 311743) (by norm_num)
theorem B1662653 : Blo 1104625 1662653 := bbase (se 3 (by rfl) ⟨311747, by rfl⟩ : syracuseStep 1662653 = 623495) (by norm_num)
theorem B1662677 : Blo 1104625 1662677 := bbase (se 7 (by rfl) ⟨19484, by rfl⟩ : syracuseStep 1662677 = 38969) (by norm_num)
theorem B1662701 : Blo 1104625 1662701 := bbase (se 3 (by rfl) ⟨311756, by rfl⟩ : syracuseStep 1662701 = 623513) (by norm_num)
theorem B1400581 : Blo 1104625 1400581 := bbase (se 4 (by rfl) ⟨131304, by rfl⟩ : syracuseStep 1400581 = 262609) (by norm_num)
theorem B1662725 : Blo 1104625 1662725 := bbase (se 4 (by rfl) ⟨155880, by rfl⟩ : syracuseStep 1662725 = 311761) (by norm_num)
theorem B1662749 : Blo 1104625 1662749 := bbase (se 3 (by rfl) ⟨311765, by rfl⟩ : syracuseStep 1662749 = 623531) (by norm_num)
theorem B1662773 : Blo 1104625 1662773 := bbase (se 5 (by rfl) ⟨77942, by rfl⟩ : syracuseStep 1662773 = 155885) (by norm_num)
theorem B1662797 : Blo 1104625 1662797 := bbase (se 3 (by rfl) ⟨311774, by rfl⟩ : syracuseStep 1662797 = 623549) (by norm_num)
theorem B1662821 : Blo 1104625 1662821 := bbase (se 4 (by rfl) ⟨155889, by rfl⟩ : syracuseStep 1662821 = 311779) (by norm_num)
theorem B1662845 : Blo 1104625 1662845 := bbase (se 3 (by rfl) ⟨311783, by rfl⟩ : syracuseStep 1662845 = 623567) (by norm_num)
theorem B1662869 : Blo 1104625 1662869 := bbase (se 6 (by rfl) ⟨38973, by rfl⟩ : syracuseStep 1662869 = 77947) (by norm_num)
theorem B1662893 : Blo 1104625 1662893 := bbase (se 3 (by rfl) ⟨311792, by rfl⟩ : syracuseStep 1662893 = 623585) (by norm_num)
theorem B1400753 : Blo 1104625 1400753 := bbase (se 2 (by rfl) ⟨525282, by rfl⟩ : syracuseStep 1400753 = 1050565) (by norm_num)
theorem B1662917 : Blo 1104625 1662917 := bbase (se 4 (by rfl) ⟨155898, by rfl⟩ : syracuseStep 1662917 = 311797) (by norm_num)
theorem B1400809 : Blo 1104625 1400809 := bbase (se 2 (by rfl) ⟨525303, by rfl⟩ : syracuseStep 1400809 = 1050607) (by norm_num)
theorem B1400905 : Blo 1104625 1400905 := bbase (se 2 (by rfl) ⟨525339, by rfl⟩ : syracuseStep 1400905 = 1050679) (by norm_num)
theorem B5595317 : Blo 1104625 5595317 := bbase (se 5 (by rfl) ⟨262280, by rfl⟩ : syracuseStep 5595317 = 524561) (by norm_num)
theorem B1401077 : Blo 1104625 1401077 := bbase (se 5 (by rfl) ⟨65675, by rfl⟩ : syracuseStep 1401077 = 131351) (by norm_num)
theorem B1401133 : Blo 1104625 1401133 := bbase (se 3 (by rfl) ⟨262712, by rfl⟩ : syracuseStep 1401133 = 525425) (by norm_num)
theorem B1139065 : Blo 1104625 1139065 := bbase (se 2 (by rfl) ⟨427149, by rfl⟩ : syracuseStep 1139065 = 854299) (by norm_num)
theorem B1401229 : Blo 1104625 1401229 := bbase (se 3 (by rfl) ⟨262730, by rfl⟩ : syracuseStep 1401229 = 525461) (by norm_num)
theorem B8511925 : Blo 1104625 8511925 := bbase (se 5 (by rfl) ⟨398996, by rfl⟩ : syracuseStep 8511925 = 797993) (by norm_num)
theorem B1991117 : Blo 1104625 1991117 := bbase (se 3 (by rfl) ⟨373334, by rfl⟩ : syracuseStep 1991117 = 746669) (by norm_num)
theorem B1401401 : Blo 1104625 1401401 := bbase (se 2 (by rfl) ⟨525525, by rfl⟩ : syracuseStep 1401401 = 1051051) (by norm_num)
theorem B1991261 : Blo 1104625 1991261 := bbase (se 3 (by rfl) ⟨373361, by rfl⟩ : syracuseStep 1991261 = 746723) (by norm_num)
theorem B1401457 : Blo 1104625 1401457 := bbase (se 2 (by rfl) ⟨525546, by rfl⟩ : syracuseStep 1401457 = 1051093) (by norm_num)
theorem B1991341 : Blo 1104625 1991341 := bbase (se 3 (by rfl) ⟨373376, by rfl⟩ : syracuseStep 1991341 = 746753) (by norm_num)
theorem B1401553 : Blo 1104625 1401553 := bbase (se 2 (by rfl) ⟨525582, by rfl⟩ : syracuseStep 1401553 = 1051165) (by norm_num)
theorem B1991405 : Blo 1104625 1991405 := bbase (se 3 (by rfl) ⟨373388, by rfl⟩ : syracuseStep 1991405 = 746777) (by norm_num)
theorem B3728213 : Blo 1104625 3728213 := bbase (se 9 (by rfl) ⟨10922, by rfl⟩ : syracuseStep 3728213 = 21845) (by norm_num)
theorem B1401725 : Blo 1104625 1401725 := bbase (se 3 (by rfl) ⟨262823, by rfl⟩ : syracuseStep 1401725 = 525647) (by norm_num)
theorem B1598341 : Blo 1104625 1598341 := bbase (se 4 (by rfl) ⟨149844, by rfl⟩ : syracuseStep 1598341 = 299689) (by norm_num)
theorem B3990421 : Blo 1104625 3990421 := bbase (se 6 (by rfl) ⟨93525, by rfl⟩ : syracuseStep 3990421 = 187051) (by norm_num)
theorem B1401781 : Blo 1104625 1401781 := bbase (se 5 (by rfl) ⟨65708, by rfl⟩ : syracuseStep 1401781 = 131417) (by norm_num)
theorem B1401877 : Blo 1104625 1401877 := bbase (se 6 (by rfl) ⟨32856, by rfl⟩ : syracuseStep 1401877 = 65713) (by norm_num)
theorem B11658325 : Blo 1104625 11658325 := bbase (se 8 (by rfl) ⟨68310, by rfl⟩ : syracuseStep 11658325 = 136621) (by norm_num)
theorem B18900053 : Blo 1104625 18900053 := bbase (se 8 (by rfl) ⟨110742, by rfl⟩ : syracuseStep 18900053 = 221485) (by norm_num)
theorem B1893509 : Blo 1104625 1893509 := bbase (se 4 (by rfl) ⟨177516, by rfl⟩ : syracuseStep 1893509 = 355033) (by norm_num)
theorem B1402049 : Blo 1104625 1402049 := bbase (se 2 (by rfl) ⟨525768, by rfl⟩ : syracuseStep 1402049 = 1051537) (by norm_num)
theorem B1402105 : Blo 1104625 1402105 := bbase (se 2 (by rfl) ⟨525789, by rfl⟩ : syracuseStep 1402105 = 1051579) (by norm_num)
theorem B3728645 : Blo 1104625 3728645 := bbase (se 4 (by rfl) ⟨349560, by rfl⟩ : syracuseStep 3728645 = 699121) (by norm_num)
theorem B1402201 : Blo 1104625 1402201 := bbase (se 2 (by rfl) ⟨525825, by rfl⟩ : syracuseStep 1402201 = 1051651) (by norm_num)
theorem B5596613 : Blo 1104625 5596613 := bbase (se 4 (by rfl) ⟨524682, by rfl⟩ : syracuseStep 5596613 = 1049365) (by norm_num)
theorem B3368405 : Blo 1104625 3368405 := bbase (se 7 (by rfl) ⟨39473, by rfl⟩ : syracuseStep 3368405 = 78947) (by norm_num)
theorem B1402373 : Blo 1104625 1402373 := bbase (se 4 (by rfl) ⟨131472, by rfl⟩ : syracuseStep 1402373 = 262945) (by norm_num)
theorem B1402429 : Blo 1104625 1402429 := bbase (se 3 (by rfl) ⟨262955, by rfl⟩ : syracuseStep 1402429 = 525911) (by norm_num)
theorem B1402525 : Blo 1104625 1402525 := bbase (se 3 (by rfl) ⟨262973, by rfl⟩ : syracuseStep 1402525 = 525947) (by norm_num)
theorem B3729077 : Blo 1104625 3729077 := bbase (se 5 (by rfl) ⟨174800, by rfl⟩ : syracuseStep 3729077 = 349601) (by norm_num)
theorem B1402697 : Blo 1104625 1402697 := bbase (se 2 (by rfl) ⟨526011, by rfl⟩ : syracuseStep 1402697 = 1052023) (by norm_num)
theorem B3499861 : Blo 1104625 3499861 := bbase (se 9 (by rfl) ⟨10253, by rfl⟩ : syracuseStep 3499861 = 20507) (by norm_num)
theorem B1402753 : Blo 1104625 1402753 := bbase (se 2 (by rfl) ⟨526032, by rfl⟩ : syracuseStep 1402753 = 1052065) (by norm_num)
theorem B1402849 : Blo 1104625 1402849 := bbase (se 2 (by rfl) ⟨526068, by rfl⟩ : syracuseStep 1402849 = 1052137) (by norm_num)
theorem B8513525 : Blo 1104625 8513525 := bbase (se 5 (by rfl) ⟨399071, by rfl⟩ : syracuseStep 8513525 = 798143) (by norm_num)
theorem B3729509 : Blo 1104625 3729509 := bbase (se 4 (by rfl) ⟨349641, by rfl⟩ : syracuseStep 3729509 = 699283) (by norm_num)
theorem B1403021 : Blo 1104625 1403021 := bbase (se 3 (by rfl) ⟨263066, by rfl⟩ : syracuseStep 1403021 = 526133) (by norm_num)
theorem B4614293 : Blo 1104625 4614293 := bbase (se 6 (by rfl) ⟨108147, by rfl⟩ : syracuseStep 4614293 = 216295) (by norm_num)
theorem B1403077 : Blo 1104625 1403077 := bbase (se 4 (by rfl) ⟨131538, by rfl⟩ : syracuseStep 1403077 = 263077) (by norm_num)
theorem B10774741 : Blo 1104625 10774741 := bbase (se 7 (by rfl) ⟨126266, by rfl⟩ : syracuseStep 10774741 = 252533) (by norm_num)
theorem B1796549 : Blo 1104625 1796549 := bbase (se 4 (by rfl) ⟨168426, by rfl⟩ : syracuseStep 1796549 = 336853) (by norm_num)
theorem B3729941 : Blo 1104625 3729941 := bbase (se 6 (by rfl) ⟨87420, by rfl⟩ : syracuseStep 3729941 = 174841) (by norm_num)
theorem B5597909 : Blo 1104625 5597909 := bbase (se 7 (by rfl) ⟨65600, by rfl⟩ : syracuseStep 5597909 = 131201) (by norm_num)
theorem B4549541 : Blo 1104625 4549541 := bbase (se 4 (by rfl) ⟨426519, by rfl⟩ : syracuseStep 4549541 = 853039) (by norm_num)
theorem B3730373 : Blo 1104625 3730373 := bbase (se 4 (by rfl) ⟨349722, by rfl⟩ : syracuseStep 3730373 = 699445) (by norm_num)
theorem B9464789 : Blo 1104625 9464789 := bbase (se 7 (by rfl) ⟨110915, by rfl⟩ : syracuseStep 9464789 = 221831) (by norm_num)
theorem B2485421 : Blo 1104625 2485421 := bbase (se 3 (by rfl) ⟨466016, by rfl⟩ : syracuseStep 2485421 = 932033) (by norm_num)
theorem B2485493 : Blo 1104625 2485493 := bbase (se 5 (by rfl) ⟨116507, by rfl⟩ : syracuseStep 2485493 = 233015) (by norm_num)
theorem B2485565 : Blo 1104625 2485565 := bbase (se 3 (by rfl) ⟨466043, by rfl⟩ : syracuseStep 2485565 = 932087) (by norm_num)
theorem B3730805 : Blo 1104625 3730805 := bbase (se 5 (by rfl) ⟨174881, by rfl⟩ : syracuseStep 3730805 = 349763) (by norm_num)
theorem B2485637 : Blo 1104625 2485637 := bbase (se 4 (by rfl) ⟨233028, by rfl⟩ : syracuseStep 2485637 = 466057) (by norm_num)
theorem B2485709 : Blo 1104625 2485709 := bbase (se 3 (by rfl) ⟨466070, by rfl⟩ : syracuseStep 2485709 = 932141) (by norm_num)
theorem B2485781 : Blo 1104625 2485781 := bbase (se 6 (by rfl) ⟨58260, by rfl⟩ : syracuseStep 2485781 = 116521) (by norm_num)
theorem B2485853 : Blo 1104625 2485853 := bbase (se 3 (by rfl) ⟨466097, by rfl⟩ : syracuseStep 2485853 = 932195) (by norm_num)
theorem B2485925 : Blo 1104625 2485925 := bbase (se 4 (by rfl) ⟨233055, by rfl⟩ : syracuseStep 2485925 = 466111) (by norm_num)
theorem B1437385 : Blo 1104625 1437385 := bbase (se 2 (by rfl) ⟨539019, by rfl⟩ : syracuseStep 1437385 = 1078039) (by norm_num)
theorem B2485997 : Blo 1104625 2485997 := bbase (se 3 (by rfl) ⟨466124, by rfl⟩ : syracuseStep 2485997 = 932249) (by norm_num)
theorem B3731237 : Blo 1104625 3731237 := bbase (se 4 (by rfl) ⟨349803, by rfl⟩ : syracuseStep 3731237 = 699607) (by norm_num)
theorem B2486069 : Blo 1104625 2486069 := bbase (se 5 (by rfl) ⟨116534, by rfl⟩ : syracuseStep 2486069 = 233069) (by norm_num)
theorem B2486141 : Blo 1104625 2486141 := bbase (se 3 (by rfl) ⟨466151, by rfl⟩ : syracuseStep 2486141 = 932303) (by norm_num)
theorem B2486213 : Blo 1104625 2486213 := bbase (se 4 (by rfl) ⟨233082, by rfl⟩ : syracuseStep 2486213 = 466165) (by norm_num)
theorem B5599205 : Blo 1104625 5599205 := bbase (se 4 (by rfl) ⟨524925, by rfl⟩ : syracuseStep 5599205 = 1049851) (by norm_num)
theorem B1994749 : Blo 1104625 1994749 := bbase (se 3 (by rfl) ⟨374015, by rfl⟩ : syracuseStep 1994749 = 748031) (by norm_num)
theorem B2486285 : Blo 1104625 2486285 := bbase (se 3 (by rfl) ⟨466178, by rfl⟩ : syracuseStep 2486285 = 932357) (by norm_num)
theorem B2486357 : Blo 1104625 2486357 := bbase (se 8 (by rfl) ⟨14568, by rfl⟩ : syracuseStep 2486357 = 29137) (by norm_num)
theorem B2486429 : Blo 1104625 2486429 := bbase (se 3 (by rfl) ⟨466205, by rfl⟩ : syracuseStep 2486429 = 932411) (by norm_num)
theorem B3731669 : Blo 1104625 3731669 := bbase (se 7 (by rfl) ⟨43730, by rfl⟩ : syracuseStep 3731669 = 87461) (by norm_num)
theorem B2486501 : Blo 1104625 2486501 := bbase (se 4 (by rfl) ⟨233109, by rfl⟩ : syracuseStep 2486501 = 466219) (by norm_num)
theorem B2486573 : Blo 1104625 2486573 := bbase (se 3 (by rfl) ⟨466232, by rfl⟩ : syracuseStep 2486573 = 932465) (by norm_num)
theorem B3993941 : Blo 1104625 3993941 := bbase (se 10 (by rfl) ⟨5850, by rfl⟩ : syracuseStep 3993941 = 11701) (by norm_num)
theorem B2486645 : Blo 1104625 2486645 := bbase (se 5 (by rfl) ⟨116561, by rfl⟩ : syracuseStep 2486645 = 233123) (by norm_num)
theorem B1864093 : Blo 1104625 1864093 := bbase (se 3 (by rfl) ⟨349517, by rfl⟩ : syracuseStep 1864093 = 699035) (by norm_num)
theorem B2486717 : Blo 1104625 2486717 := bbase (se 3 (by rfl) ⟨466259, by rfl⟩ : syracuseStep 2486717 = 932519) (by norm_num)
theorem B1995205 : Blo 1104625 1995205 := bbase (se 4 (by rfl) ⟨187050, by rfl⟩ : syracuseStep 1995205 = 374101) (by norm_num)
theorem B1864181 : Blo 1104625 1864181 := bbase (se 5 (by rfl) ⟨87383, by rfl⟩ : syracuseStep 1864181 = 174767) (by norm_num)
theorem B2486789 : Blo 1104625 2486789 := bbase (se 4 (by rfl) ⟨233136, by rfl⟩ : syracuseStep 2486789 = 466273) (by norm_num)
theorem B1798669 : Blo 1104625 1798669 := bbase (se 3 (by rfl) ⟨337250, by rfl⟩ : syracuseStep 1798669 = 674501) (by norm_num)
theorem B2486861 : Blo 1104625 2486861 := bbase (se 3 (by rfl) ⟨466286, by rfl⟩ : syracuseStep 2486861 = 932573) (by norm_num)
theorem B1864309 : Blo 1104625 1864309 := bbase (se 5 (by rfl) ⟨87389, by rfl⟩ : syracuseStep 1864309 = 174779) (by norm_num)
theorem B3732101 : Blo 1104625 3732101 := bbase (se 4 (by rfl) ⟨349884, by rfl⟩ : syracuseStep 3732101 = 699769) (by norm_num)
theorem B2486933 : Blo 1104625 2486933 := bbase (se 6 (by rfl) ⟨58287, by rfl⟩ : syracuseStep 2486933 = 116575) (by norm_num)
theorem B1864397 : Blo 1104625 1864397 := bbase (se 3 (by rfl) ⟨349574, by rfl⟩ : syracuseStep 1864397 = 699149) (by norm_num)
theorem B8418005 : Blo 1104625 8418005 := bbase (se 7 (by rfl) ⟨98648, by rfl⟩ : syracuseStep 8418005 = 197297) (by norm_num)
theorem B2487005 : Blo 1104625 2487005 := bbase (se 3 (by rfl) ⟨466313, by rfl⟩ : syracuseStep 2487005 = 932627) (by norm_num)
theorem B3994373 : Blo 1104625 3994373 := bbase (se 4 (by rfl) ⟨374472, by rfl⟩ : syracuseStep 3994373 = 748945) (by norm_num)
theorem B2487077 : Blo 1104625 2487077 := bbase (se 4 (by rfl) ⟨233163, by rfl⟩ : syracuseStep 2487077 = 466327) (by norm_num)
theorem B1864525 : Blo 1104625 1864525 := bbase (se 3 (by rfl) ⟨349598, by rfl⟩ : syracuseStep 1864525 = 699197) (by norm_num)
theorem B2487149 : Blo 1104625 2487149 := bbase (se 3 (by rfl) ⟨466340, by rfl⟩ : syracuseStep 2487149 = 932681) (by norm_num)
theorem B5108629 : Blo 1104625 5108629 := bbase (se 6 (by rfl) ⟨119733, by rfl⟩ : syracuseStep 5108629 = 239467) (by norm_num)
theorem B1864613 : Blo 1104625 1864613 := bbase (se 4 (by rfl) ⟨174807, by rfl⟩ : syracuseStep 1864613 = 349615) (by norm_num)
theorem B2487221 : Blo 1104625 2487221 := bbase (se 5 (by rfl) ⟨116588, by rfl⟩ : syracuseStep 2487221 = 233177) (by norm_num)
theorem B2487293 : Blo 1104625 2487293 := bbase (se 3 (by rfl) ⟨466367, by rfl⟩ : syracuseStep 2487293 = 932735) (by norm_num)
theorem B1864741 : Blo 1104625 1864741 := bbase (se 4 (by rfl) ⟨174819, by rfl⟩ : syracuseStep 1864741 = 349639) (by norm_num)
theorem B3732533 : Blo 1104625 3732533 := bbase (se 5 (by rfl) ⟨174962, by rfl⟩ : syracuseStep 3732533 = 349925) (by norm_num)
theorem B2487365 : Blo 1104625 2487365 := bbase (se 4 (by rfl) ⟨233190, by rfl⟩ : syracuseStep 2487365 = 466381) (by norm_num)
theorem B2520173 : Blo 1104625 2520173 := bbase (se 3 (by rfl) ⟨472532, by rfl⟩ : syracuseStep 2520173 = 945065) (by norm_num)
theorem B1864829 : Blo 1104625 1864829 := bbase (se 3 (by rfl) ⟨349655, by rfl⟩ : syracuseStep 1864829 = 699311) (by norm_num)
theorem B2487437 : Blo 1104625 2487437 := bbase (se 3 (by rfl) ⟨466394, by rfl⟩ : syracuseStep 2487437 = 932789) (by norm_num)
theorem B2487509 : Blo 1104625 2487509 := bbase (se 7 (by rfl) ⟨29150, by rfl⟩ : syracuseStep 2487509 = 58301) (by norm_num)
theorem B5600501 : Blo 1104625 5600501 := bbase (se 5 (by rfl) ⟨262523, by rfl⟩ : syracuseStep 5600501 = 525047) (by norm_num)
theorem B1864957 : Blo 1104625 1864957 := bbase (se 3 (by rfl) ⟨349679, by rfl⟩ : syracuseStep 1864957 = 699359) (by norm_num)
theorem B2487581 : Blo 1104625 2487581 := bbase (se 3 (by rfl) ⟨466421, by rfl⟩ : syracuseStep 2487581 = 932843) (by norm_num)
theorem B1865045 : Blo 1104625 1865045 := bbase (se 13 (by rfl) ⟨341, by rfl⟩ : syracuseStep 1865045 = 683) (by norm_num)
theorem B2487653 : Blo 1104625 2487653 := bbase (se 4 (by rfl) ⟨233217, by rfl⟩ : syracuseStep 2487653 = 466435) (by norm_num)
theorem B1996133 : Blo 1104625 1996133 := bbase (se 4 (by rfl) ⟨187137, by rfl⟩ : syracuseStep 1996133 = 374275) (by norm_num)
theorem B2487725 : Blo 1104625 2487725 := bbase (se 3 (by rfl) ⟨466448, by rfl⟩ : syracuseStep 2487725 = 932897) (by norm_num)
theorem B1865173 : Blo 1104625 1865173 := bbase (se 7 (by rfl) ⟨21857, by rfl⟩ : syracuseStep 1865173 = 43715) (by norm_num)
theorem B3732965 : Blo 1104625 3732965 := bbase (se 4 (by rfl) ⟨349965, by rfl⟩ : syracuseStep 3732965 = 699931) (by norm_num)
theorem B2487797 : Blo 1104625 2487797 := bbase (se 5 (by rfl) ⟨116615, by rfl⟩ : syracuseStep 2487797 = 233231) (by norm_num)
theorem B1996301 : Blo 1104625 1996301 := bbase (se 3 (by rfl) ⟨374306, by rfl⟩ : syracuseStep 1996301 = 748613) (by norm_num)
theorem B1865261 : Blo 1104625 1865261 := bbase (se 3 (by rfl) ⟨349736, by rfl⟩ : syracuseStep 1865261 = 699473) (by norm_num)
theorem B2487869 : Blo 1104625 2487869 := bbase (se 3 (by rfl) ⟨466475, by rfl⟩ : syracuseStep 2487869 = 932951) (by norm_num)
theorem B1242733 : Blo 1104625 1242733 := bbase (se 3 (by rfl) ⟨233012, by rfl⟩ : syracuseStep 1242733 = 466025) (by norm_num)
theorem B2487941 : Blo 1104625 2487941 := bbase (se 4 (by rfl) ⟨233244, by rfl⟩ : syracuseStep 2487941 = 466489) (by norm_num)
theorem B1242769 : Blo 1104625 1242769 := bbase (se 2 (by rfl) ⟨466038, by rfl⟩ : syracuseStep 1242769 = 932077) (by norm_num)
theorem B1865389 : Blo 1104625 1865389 := bbase (se 3 (by rfl) ⟨349760, by rfl⟩ : syracuseStep 1865389 = 699521) (by norm_num)
theorem B1242805 : Blo 1104625 1242805 := bbase (se 5 (by rfl) ⟨58256, by rfl⟩ : syracuseStep 1242805 = 116513) (by norm_num)
theorem B11368117 : Blo 1104625 11368117 := bbase (se 5 (by rfl) ⟨532880, by rfl⟩ : syracuseStep 11368117 = 1065761) (by norm_num)
theorem B2488013 : Blo 1104625 2488013 := bbase (se 3 (by rfl) ⟨466502, by rfl⟩ : syracuseStep 2488013 = 933005) (by norm_num)
theorem B1242841 : Blo 1104625 1242841 := bbase (se 2 (by rfl) ⟨466065, by rfl⟩ : syracuseStep 1242841 = 932131) (by norm_num)
theorem B2127581 : Blo 1104625 2127581 := bbase (se 3 (by rfl) ⟨398921, by rfl⟩ : syracuseStep 2127581 = 797843) (by norm_num)
theorem B1242877 : Blo 1104625 1242877 := bbase (se 3 (by rfl) ⟨233039, by rfl⟩ : syracuseStep 1242877 = 466079) (by norm_num)
theorem B1865477 : Blo 1104625 1865477 := bbase (se 4 (by rfl) ⟨174888, by rfl⟩ : syracuseStep 1865477 = 349777) (by norm_num)
theorem B2488085 : Blo 1104625 2488085 := bbase (se 6 (by rfl) ⟨58314, by rfl⟩ : syracuseStep 2488085 = 116629) (by norm_num)
theorem B1242913 : Blo 1104625 1242913 := bbase (se 2 (by rfl) ⟨466092, by rfl⟩ : syracuseStep 1242913 = 932185) (by norm_num)
theorem B2520877 : Blo 1104625 2520877 := bbase (se 3 (by rfl) ⟨472664, by rfl⟩ : syracuseStep 2520877 = 945329) (by norm_num)
theorem B1996589 : Blo 1104625 1996589 := bbase (se 3 (by rfl) ⟨374360, by rfl⟩ : syracuseStep 1996589 = 748721) (by norm_num)
theorem B1242949 : Blo 1104625 1242949 := bbase (se 4 (by rfl) ⟨116526, by rfl⟩ : syracuseStep 1242949 = 233053) (by norm_num)
theorem B2488157 : Blo 1104625 2488157 := bbase (se 3 (by rfl) ⟨466529, by rfl⟩ : syracuseStep 2488157 = 933059) (by norm_num)
theorem B1242985 : Blo 1104625 1242985 := bbase (se 2 (by rfl) ⟨466119, by rfl⟩ : syracuseStep 1242985 = 932239) (by norm_num)
theorem B9467765 : Blo 1104625 9467765 := bbase (se 5 (by rfl) ⟨443801, by rfl⟩ : syracuseStep 9467765 = 887603) (by norm_num)
theorem B1865605 : Blo 1104625 1865605 := bbase (se 4 (by rfl) ⟨174900, by rfl⟩ : syracuseStep 1865605 = 349801) (by norm_num)
theorem B1243021 : Blo 1104625 1243021 := bbase (se 3 (by rfl) ⟨233066, by rfl⟩ : syracuseStep 1243021 = 466133) (by norm_num)
theorem B3733397 : Blo 1104625 3733397 := bbase (se 6 (by rfl) ⟨87501, by rfl⟩ : syracuseStep 3733397 = 175003) (by norm_num)
theorem B2488229 : Blo 1104625 2488229 := bbase (se 4 (by rfl) ⟨233271, by rfl⟩ : syracuseStep 2488229 = 466543) (by norm_num)
theorem B1243057 : Blo 1104625 1243057 := bbase (se 2 (by rfl) ⟨466146, by rfl⟩ : syracuseStep 1243057 = 932293) (by norm_num)
theorem B1243093 : Blo 1104625 1243093 := bbase (se 7 (by rfl) ⟨14567, by rfl⟩ : syracuseStep 1243093 = 29135) (by norm_num)
theorem B1865693 : Blo 1104625 1865693 := bbase (se 3 (by rfl) ⟨349817, by rfl⟩ : syracuseStep 1865693 = 699635) (by norm_num)
theorem B2488301 : Blo 1104625 2488301 := bbase (se 3 (by rfl) ⟨466556, by rfl⟩ : syracuseStep 2488301 = 933113) (by norm_num)
theorem B1243129 : Blo 1104625 1243129 := bbase (se 2 (by rfl) ⟨466173, by rfl⟩ : syracuseStep 1243129 = 932347) (by norm_num)
theorem B1243165 : Blo 1104625 1243165 := bbase (se 3 (by rfl) ⟨233093, by rfl⟩ : syracuseStep 1243165 = 466187) (by norm_num)
theorem B2488373 : Blo 1104625 2488373 := bbase (se 5 (by rfl) ⟨116642, by rfl⟩ : syracuseStep 2488373 = 233285) (by norm_num)
theorem B1243201 : Blo 1104625 1243201 := bbase (se 2 (by rfl) ⟨466200, by rfl⟩ : syracuseStep 1243201 = 932401) (by norm_num)
theorem B1865821 : Blo 1104625 1865821 := bbase (se 3 (by rfl) ⟨349841, by rfl⟩ : syracuseStep 1865821 = 699683) (by norm_num)
theorem B1243237 : Blo 1104625 1243237 := bbase (se 4 (by rfl) ⟨116553, by rfl⟩ : syracuseStep 1243237 = 233107) (by norm_num)
theorem B10090613 : Blo 1104625 10090613 := bbase (se 5 (by rfl) ⟨472997, by rfl⟩ : syracuseStep 10090613 = 945995) (by norm_num)
theorem B2488445 : Blo 1104625 2488445 := bbase (se 3 (by rfl) ⟨466583, by rfl⟩ : syracuseStep 2488445 = 933167) (by norm_num)
theorem B1243273 : Blo 1104625 1243273 := bbase (se 2 (by rfl) ⟨466227, by rfl⟩ : syracuseStep 1243273 = 932455) (by norm_num)
theorem B1243309 : Blo 1104625 1243309 := bbase (se 3 (by rfl) ⟨233120, by rfl⟩ : syracuseStep 1243309 = 466241) (by norm_num)
theorem B1865909 : Blo 1104625 1865909 := bbase (se 5 (by rfl) ⟨87464, by rfl⟩ : syracuseStep 1865909 = 174929) (by norm_num)
theorem B2488517 : Blo 1104625 2488517 := bbase (se 4 (by rfl) ⟨233298, by rfl⟩ : syracuseStep 2488517 = 466597) (by norm_num)
theorem B1243345 : Blo 1104625 1243345 := bbase (se 2 (by rfl) ⟨466254, by rfl⟩ : syracuseStep 1243345 = 932509) (by norm_num)
theorem B1243381 : Blo 1104625 1243381 := bbase (se 5 (by rfl) ⟨58283, by rfl⟩ : syracuseStep 1243381 = 116567) (by norm_num)
theorem B2488589 : Blo 1104625 2488589 := bbase (se 3 (by rfl) ⟨466610, by rfl⟩ : syracuseStep 2488589 = 933221) (by norm_num)
theorem B1243417 : Blo 1104625 1243417 := bbase (se 2 (by rfl) ⟨466281, by rfl⟩ : syracuseStep 1243417 = 932563) (by norm_num)
theorem B1866037 : Blo 1104625 1866037 := bbase (se 5 (by rfl) ⟨87470, by rfl⟩ : syracuseStep 1866037 = 174941) (by norm_num)
theorem B1243453 : Blo 1104625 1243453 := bbase (se 3 (by rfl) ⟨233147, by rfl⟩ : syracuseStep 1243453 = 466295) (by norm_num)
theorem B3733829 : Blo 1104625 3733829 := bbase (se 4 (by rfl) ⟨350046, by rfl⟩ : syracuseStep 3733829 = 700093) (by norm_num)
theorem B2488661 : Blo 1104625 2488661 := bbase (se 10 (by rfl) ⟨3645, by rfl⟩ : syracuseStep 2488661 = 7291) (by norm_num)
theorem B1243489 : Blo 1104625 1243489 := bbase (se 2 (by rfl) ⟨466308, by rfl⟩ : syracuseStep 1243489 = 932617) (by norm_num)
theorem B1243525 : Blo 1104625 1243525 := bbase (se 4 (by rfl) ⟨116580, by rfl⟩ : syracuseStep 1243525 = 233161) (by norm_num)
theorem B1866125 : Blo 1104625 1866125 := bbase (se 3 (by rfl) ⟨349898, by rfl⟩ : syracuseStep 1866125 = 699797) (by norm_num)
theorem B2488733 : Blo 1104625 2488733 := bbase (se 3 (by rfl) ⟨466637, by rfl⟩ : syracuseStep 2488733 = 933275) (by norm_num)
theorem B1243561 : Blo 1104625 1243561 := bbase (se 2 (by rfl) ⟨466335, by rfl⟩ : syracuseStep 1243561 = 932671) (by norm_num)
theorem B1243597 : Blo 1104625 1243597 := bbase (se 3 (by rfl) ⟨233174, by rfl⟩ : syracuseStep 1243597 = 466349) (by norm_num)
theorem B4323797 : Blo 1104625 4323797 := bbase (se 7 (by rfl) ⟨50669, by rfl⟩ : syracuseStep 4323797 = 101339) (by norm_num)
theorem B2488805 : Blo 1104625 2488805 := bbase (se 4 (by rfl) ⟨233325, by rfl⟩ : syracuseStep 2488805 = 466651) (by norm_num)
theorem B1243633 : Blo 1104625 1243633 := bbase (se 2 (by rfl) ⟨466362, by rfl⟩ : syracuseStep 1243633 = 932725) (by norm_num)
theorem B4487669 : Blo 1104625 4487669 := bbase (se 5 (by rfl) ⟨210359, by rfl⟩ : syracuseStep 4487669 = 420719) (by norm_num)
theorem B5601797 : Blo 1104625 5601797 := bbase (se 4 (by rfl) ⟨525168, by rfl⟩ : syracuseStep 5601797 = 1050337) (by norm_num)
theorem B1866253 : Blo 1104625 1866253 := bbase (se 3 (by rfl) ⟨349922, by rfl⟩ : syracuseStep 1866253 = 699845) (by norm_num)
theorem B1243669 : Blo 1104625 1243669 := bbase (se 6 (by rfl) ⟨29148, by rfl⟩ : syracuseStep 1243669 = 58297) (by norm_num)
theorem B2488877 : Blo 1104625 2488877 := bbase (se 3 (by rfl) ⟨466664, by rfl⟩ : syracuseStep 2488877 = 933329) (by norm_num)
theorem B1243705 : Blo 1104625 1243705 := bbase (se 2 (by rfl) ⟨466389, by rfl⟩ : syracuseStep 1243705 = 932779) (by norm_num)
theorem B1243741 : Blo 1104625 1243741 := bbase (se 3 (by rfl) ⟨233201, by rfl⟩ : syracuseStep 1243741 = 466403) (by norm_num)
theorem B1866341 : Blo 1104625 1866341 := bbase (se 4 (by rfl) ⟨174969, by rfl⟩ : syracuseStep 1866341 = 349939) (by norm_num)
theorem B2488949 : Blo 1104625 2488949 := bbase (se 5 (by rfl) ⟨116669, by rfl⟩ : syracuseStep 2488949 = 233339) (by norm_num)
theorem B1243777 : Blo 1104625 1243777 := bbase (se 2 (by rfl) ⟨466416, by rfl⟩ : syracuseStep 1243777 = 932833) (by norm_num)
theorem B1243813 : Blo 1104625 1243813 := bbase (se 4 (by rfl) ⟨116607, by rfl⟩ : syracuseStep 1243813 = 233215) (by norm_num)
theorem B2489021 : Blo 1104625 2489021 := bbase (se 3 (by rfl) ⟨466691, by rfl⟩ : syracuseStep 2489021 = 933383) (by norm_num)
theorem B1243849 : Blo 1104625 1243849 := bbase (se 2 (by rfl) ⟨466443, by rfl⟩ : syracuseStep 1243849 = 932887) (by norm_num)
theorem B1866469 : Blo 1104625 1866469 := bbase (se 4 (by rfl) ⟨174981, by rfl⟩ : syracuseStep 1866469 = 349963) (by norm_num)
theorem B1243885 : Blo 1104625 1243885 := bbase (se 3 (by rfl) ⟨233228, by rfl⟩ : syracuseStep 1243885 = 466457) (by norm_num)
theorem B3734261 : Blo 1104625 3734261 := bbase (se 5 (by rfl) ⟨175043, by rfl⟩ : syracuseStep 3734261 = 350087) (by norm_num)
theorem B2489093 : Blo 1104625 2489093 := bbase (se 4 (by rfl) ⟨233352, by rfl⟩ : syracuseStep 2489093 = 466705) (by norm_num)
theorem B1243921 : Blo 1104625 1243921 := bbase (se 2 (by rfl) ⟨466470, by rfl⟩ : syracuseStep 1243921 = 932941) (by norm_num)
theorem B1243957 : Blo 1104625 1243957 := bbase (se 5 (by rfl) ⟨58310, by rfl⟩ : syracuseStep 1243957 = 116621) (by norm_num)
theorem B1866557 : Blo 1104625 1866557 := bbase (se 3 (by rfl) ⟨349979, by rfl⟩ : syracuseStep 1866557 = 699959) (by norm_num)
theorem B2489165 : Blo 1104625 2489165 := bbase (se 3 (by rfl) ⟨466718, by rfl⟩ : syracuseStep 2489165 = 933437) (by norm_num)
theorem B1243993 : Blo 1104625 1243993 := bbase (se 2 (by rfl) ⟨466497, by rfl⟩ : syracuseStep 1243993 = 932995) (by norm_num)
theorem B3406693 : Blo 1104625 3406693 := bbase (se 4 (by rfl) ⟨319377, by rfl⟩ : syracuseStep 3406693 = 638755) (by norm_num)
theorem B1244029 : Blo 1104625 1244029 := bbase (se 3 (by rfl) ⟨233255, by rfl⟩ : syracuseStep 1244029 = 466511) (by norm_num)
theorem B2882429 : Blo 1104625 2882429 := bbase (se 3 (by rfl) ⟨540455, by rfl⟩ : syracuseStep 2882429 = 1080911) (by norm_num)
theorem B5045125 : Blo 1104625 5045125 := bbase (se 4 (by rfl) ⟨472980, by rfl⟩ : syracuseStep 5045125 = 945961) (by norm_num)
theorem B2489237 : Blo 1104625 2489237 := bbase (se 6 (by rfl) ⟨58341, by rfl⟩ : syracuseStep 2489237 = 116683) (by norm_num)
theorem B1244065 : Blo 1104625 1244065 := bbase (se 2 (by rfl) ⟨466524, by rfl⟩ : syracuseStep 1244065 = 933049) (by norm_num)
theorem B1866685 : Blo 1104625 1866685 := bbase (se 3 (by rfl) ⟨350003, by rfl⟩ : syracuseStep 1866685 = 700007) (by norm_num)
theorem B1244101 : Blo 1104625 1244101 := bbase (se 4 (by rfl) ⟨116634, by rfl⟩ : syracuseStep 1244101 = 233269) (by norm_num)
theorem B2489309 : Blo 1104625 2489309 := bbase (se 3 (by rfl) ⟨466745, by rfl⟩ : syracuseStep 2489309 = 933491) (by norm_num)
theorem B1244137 : Blo 1104625 1244137 := bbase (se 2 (by rfl) ⟨466551, by rfl⟩ : syracuseStep 1244137 = 933103) (by norm_num)
theorem B1244173 : Blo 1104625 1244173 := bbase (se 3 (by rfl) ⟨233282, by rfl⟩ : syracuseStep 1244173 = 466565) (by norm_num)
theorem B5045269 : Blo 1104625 5045269 := bbase (se 6 (by rfl) ⟨118248, by rfl⟩ : syracuseStep 5045269 = 236497) (by norm_num)
theorem B1866773 : Blo 1104625 1866773 := bbase (se 6 (by rfl) ⟨43752, by rfl⟩ : syracuseStep 1866773 = 87505) (by norm_num)
theorem B2489381 : Blo 1104625 2489381 := bbase (se 4 (by rfl) ⟨233379, by rfl⟩ : syracuseStep 2489381 = 466759) (by norm_num)
theorem B1244209 : Blo 1104625 1244209 := bbase (se 2 (by rfl) ⟨466578, by rfl⟩ : syracuseStep 1244209 = 933157) (by norm_num)
theorem B1244245 : Blo 1104625 1244245 := bbase (se 8 (by rfl) ⟨7290, by rfl⟩ : syracuseStep 1244245 = 14581) (by norm_num)
theorem B2489453 : Blo 1104625 2489453 := bbase (se 3 (by rfl) ⟨466772, by rfl⟩ : syracuseStep 2489453 = 933545) (by norm_num)
theorem B1244281 : Blo 1104625 1244281 := bbase (se 2 (by rfl) ⟨466605, by rfl⟩ : syracuseStep 1244281 = 933211) (by norm_num)
theorem B1866901 : Blo 1104625 1866901 := bbase (se 6 (by rfl) ⟨43755, by rfl⟩ : syracuseStep 1866901 = 87511) (by norm_num)
theorem B1244317 : Blo 1104625 1244317 := bbase (se 3 (by rfl) ⟨233309, by rfl⟩ : syracuseStep 1244317 = 466619) (by norm_num)
theorem B3734693 : Blo 1104625 3734693 := bbase (se 4 (by rfl) ⟨350127, by rfl⟩ : syracuseStep 3734693 = 700255) (by norm_num)
theorem B2489525 : Blo 1104625 2489525 := bbase (se 5 (by rfl) ⟨116696, by rfl⟩ : syracuseStep 2489525 = 233393) (by norm_num)
theorem B1244353 : Blo 1104625 1244353 := bbase (se 2 (by rfl) ⟨466632, by rfl⟩ : syracuseStep 1244353 = 933265) (by norm_num)
theorem B1244389 : Blo 1104625 1244389 := bbase (se 4 (by rfl) ⟨116661, by rfl⟩ : syracuseStep 1244389 = 233323) (by norm_num)
theorem B1866989 : Blo 1104625 1866989 := bbase (se 3 (by rfl) ⟨350060, by rfl⟩ : syracuseStep 1866989 = 700121) (by norm_num)
theorem B2489597 : Blo 1104625 2489597 := bbase (se 3 (by rfl) ⟨466799, by rfl⟩ : syracuseStep 2489597 = 933599) (by norm_num)
theorem B1244425 : Blo 1104625 1244425 := bbase (se 2 (by rfl) ⟨466659, by rfl⟩ : syracuseStep 1244425 = 933319) (by norm_num)
theorem B1244461 : Blo 1104625 1244461 := bbase (se 3 (by rfl) ⟨233336, by rfl⟩ : syracuseStep 1244461 = 466673) (by norm_num)
theorem B2489669 : Blo 1104625 2489669 := bbase (se 4 (by rfl) ⟨233406, by rfl⟩ : syracuseStep 2489669 = 466813) (by norm_num)
theorem B1244497 : Blo 1104625 1244497 := bbase (se 2 (by rfl) ⟨466686, by rfl⟩ : syracuseStep 1244497 = 933373) (by norm_num)
theorem B1867117 : Blo 1104625 1867117 := bbase (se 3 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 1867117 = 700169) (by norm_num)
theorem B1244533 : Blo 1104625 1244533 := bbase (se 5 (by rfl) ⟨58337, by rfl⟩ : syracuseStep 1244533 = 116675) (by norm_num)
theorem B2489741 : Blo 1104625 2489741 := bbase (se 3 (by rfl) ⟨466826, by rfl⟩ : syracuseStep 2489741 = 933653) (by norm_num)
theorem B1244569 : Blo 1104625 1244569 := bbase (se 2 (by rfl) ⟨466713, by rfl⟩ : syracuseStep 1244569 = 933427) (by norm_num)
theorem B1244605 : Blo 1104625 1244605 := bbase (se 3 (by rfl) ⟨233363, by rfl⟩ : syracuseStep 1244605 = 466727) (by norm_num)
theorem B1867205 : Blo 1104625 1867205 := bbase (se 4 (by rfl) ⟨175050, by rfl⟩ : syracuseStep 1867205 = 350101) (by norm_num)
theorem B2489813 : Blo 1104625 2489813 := bbase (se 7 (by rfl) ⟨29177, by rfl⟩ : syracuseStep 2489813 = 58355) (by norm_num)
theorem B4259285 : Blo 1104625 4259285 := bbase (se 7 (by rfl) ⟨49913, by rfl⟩ : syracuseStep 4259285 = 99827) (by norm_num)
theorem B1244641 : Blo 1104625 1244641 := bbase (se 2 (by rfl) ⟨466740, by rfl⟩ : syracuseStep 1244641 = 933481) (by norm_num)
theorem B1244677 : Blo 1104625 1244677 := bbase (se 4 (by rfl) ⟨116688, by rfl⟩ : syracuseStep 1244677 = 233377) (by norm_num)
theorem B2489885 : Blo 1104625 2489885 := bbase (se 3 (by rfl) ⟨466853, by rfl⟩ : syracuseStep 2489885 = 933707) (by norm_num)
theorem B1244713 : Blo 1104625 1244713 := bbase (se 2 (by rfl) ⟨466767, by rfl⟩ : syracuseStep 1244713 = 933535) (by norm_num)
theorem B1867333 : Blo 1104625 1867333 := bbase (se 4 (by rfl) ⟨175062, by rfl⟩ : syracuseStep 1867333 = 350125) (by norm_num)
theorem B1244749 : Blo 1104625 1244749 := bbase (se 3 (by rfl) ⟨233390, by rfl⟩ : syracuseStep 1244749 = 466781) (by norm_num)
theorem B3735125 : Blo 1104625 3735125 := bbase (se 8 (by rfl) ⟨21885, by rfl⟩ : syracuseStep 3735125 = 43771) (by norm_num)
theorem B2489957 : Blo 1104625 2489957 := bbase (se 4 (by rfl) ⟨233433, by rfl⟩ : syracuseStep 2489957 = 466867) (by norm_num)
theorem B1244785 : Blo 1104625 1244785 := bbase (se 2 (by rfl) ⟨466794, by rfl⟩ : syracuseStep 1244785 = 933589) (by norm_num)
theorem B1244821 : Blo 1104625 1244821 := bbase (se 6 (by rfl) ⟨29175, by rfl⟩ : syracuseStep 1244821 = 58351) (by norm_num)
theorem B1867421 : Blo 1104625 1867421 := bbase (se 3 (by rfl) ⟨350141, by rfl⟩ : syracuseStep 1867421 = 700283) (by norm_num)
theorem B2490029 : Blo 1104625 2490029 := bbase (se 3 (by rfl) ⟨466880, by rfl⟩ : syracuseStep 2490029 = 933761) (by norm_num)
theorem B1244857 : Blo 1104625 1244857 := bbase (se 2 (by rfl) ⟨466821, by rfl⟩ : syracuseStep 1244857 = 933643) (by norm_num)
theorem B1244893 : Blo 1104625 1244893 := bbase (se 3 (by rfl) ⟨233417, by rfl⟩ : syracuseStep 1244893 = 466835) (by norm_num)
theorem B2490101 : Blo 1104625 2490101 := bbase (se 5 (by rfl) ⟨116723, by rfl⟩ : syracuseStep 2490101 = 233447) (by norm_num)
theorem B1244929 : Blo 1104625 1244929 := bbase (se 2 (by rfl) ⟨466848, by rfl⟩ : syracuseStep 1244929 = 933697) (by norm_num)
theorem B7962389 : Blo 1104625 7962389 := bbase (se 6 (by rfl) ⟨186618, by rfl⟩ : syracuseStep 7962389 = 373237) (by norm_num)
theorem B5603093 : Blo 1104625 5603093 := bbase (se 6 (by rfl) ⟨131322, by rfl⟩ : syracuseStep 5603093 = 262645) (by norm_num)
theorem B1867549 : Blo 1104625 1867549 := bbase (se 3 (by rfl) ⟨350165, by rfl⟩ : syracuseStep 1867549 = 700331) (by norm_num)
theorem B1244965 : Blo 1104625 1244965 := bbase (se 4 (by rfl) ⟨116715, by rfl⟩ : syracuseStep 1244965 = 233431) (by norm_num)
theorem B2490173 : Blo 1104625 2490173 := bbase (se 3 (by rfl) ⟨466907, by rfl⟩ : syracuseStep 2490173 = 933815) (by norm_num)
theorem B1245001 : Blo 1104625 1245001 := bbase (se 2 (by rfl) ⟨466875, by rfl⟩ : syracuseStep 1245001 = 933751) (by norm_num)
theorem B1245037 : Blo 1104625 1245037 := bbase (se 3 (by rfl) ⟨233444, by rfl⟩ : syracuseStep 1245037 = 466889) (by norm_num)
theorem B1867637 : Blo 1104625 1867637 := bbase (se 5 (by rfl) ⟨87545, by rfl⟩ : syracuseStep 1867637 = 175091) (by norm_num)
theorem B2490245 : Blo 1104625 2490245 := bbase (se 4 (by rfl) ⟨233460, by rfl⟩ : syracuseStep 2490245 = 466921) (by norm_num)
theorem B1245073 : Blo 1104625 1245073 := bbase (se 2 (by rfl) ⟨466902, by rfl⟩ : syracuseStep 1245073 = 933805) (by norm_num)
theorem B1245109 : Blo 1104625 1245109 := bbase (se 5 (by rfl) ⟨58364, by rfl⟩ : syracuseStep 1245109 = 116729) (by norm_num)
theorem B2490317 : Blo 1104625 2490317 := bbase (se 3 (by rfl) ⟨466934, by rfl⟩ : syracuseStep 2490317 = 933869) (by norm_num)
theorem B1245145 : Blo 1104625 1245145 := bbase (se 2 (by rfl) ⟨466929, by rfl⟩ : syracuseStep 1245145 = 933859) (by norm_num)
theorem B1867765 : Blo 1104625 1867765 := bbase (se 5 (by rfl) ⟨87551, by rfl⟩ : syracuseStep 1867765 = 175103) (by norm_num)
theorem B1245181 : Blo 1104625 1245181 := bbase (se 3 (by rfl) ⟨233471, by rfl⟩ : syracuseStep 1245181 = 466943) (by norm_num)
theorem B2490371 : Blo 1104625 2490371 := bstep (se 1 (by rfl) ⟨1867778, by rfl⟩ : syracuseStep 2490371 = 3735557) B3735557
theorem B1245235 : Blo 1104625 1245235 := bstep (se 1 (by rfl) ⟨933926, by rfl⟩ : syracuseStep 1245235 = 1867853) B1867853
theorem B2359363 : Blo 1104625 2359363 := bstep (se 1 (by rfl) ⟨1769522, by rfl⟩ : syracuseStep 2359363 = 3539045) B3539045
theorem B1867873 : Blo 1104625 1867873 := bstep (se 2 (by rfl) ⟨700452, by rfl⟩ : syracuseStep 1867873 = 1400905) B1400905
theorem B3145841 : Blo 1104625 3145841 := bstep (se 2 (by rfl) ⟨1179690, by rfl⟩ : syracuseStep 3145841 = 2359381) B2359381
theorem B2097265 : Blo 1104625 2097265 := bstep (se 2 (by rfl) ⟨786474, by rfl⟩ : syracuseStep 2097265 = 1572949) B1572949
theorem B1572977 : Blo 1104625 1572977 := bstep (se 2 (by rfl) ⟨589866, by rfl⟩ : syracuseStep 1572977 = 1179733) B1179733
theorem B3735665 : Blo 1104625 3735665 := bstep (se 2 (by rfl) ⟨1400874, by rfl⟩ : syracuseStep 3735665 = 2801749) B2801749
theorem B1867907 : Blo 1104625 1867907 := bstep (se 1 (by rfl) ⟨1400930, by rfl⟩ : syracuseStep 1867907 = 2801861) B2801861
theorem B1573057 : Blo 1104625 1573057 := bstep (se 2 (by rfl) ⟨589896, by rfl⟩ : syracuseStep 1573057 = 1179793) B1179793
theorem B1245379 : Blo 1104625 1245379 := bstep (se 1 (by rfl) ⟨934034, by rfl⟩ : syracuseStep 1245379 = 1868069) B1868069
theorem B1868035 : Blo 1104625 1868035 := bstep (se 1 (by rfl) ⟨1401026, by rfl⟩ : syracuseStep 1868035 = 2802053) B2802053
theorem B2490641 : Blo 1104625 2490641 := bstep (se 2 (by rfl) ⟨933990, by rfl⟩ : syracuseStep 2490641 = 1867981) B1867981
theorem B2490659 : Blo 1104625 2490659 := bstep (se 1 (by rfl) ⟨1867994, by rfl⟩ : syracuseStep 2490659 = 3735989) B3735989
theorem B1769779 : Blo 1104625 1769779 := bstep (se 1 (by rfl) ⟨1327334, by rfl⟩ : syracuseStep 1769779 = 2654669) B2654669
theorem B1179955 : Blo 1104625 1179955 := bstep (se 1 (by rfl) ⟨884966, by rfl⟩ : syracuseStep 1179955 = 1769933) B1769933
theorem B1245523 : Blo 1104625 1245523 := bstep (se 1 (by rfl) ⟨934142, by rfl⟩ : syracuseStep 1245523 = 1868285) B1868285
theorem B1769825 : Blo 1104625 1769825 := bstep (se 2 (by rfl) ⟨663684, by rfl⟩ : syracuseStep 1769825 = 1327369) B1327369
theorem B1868177 : Blo 1104625 1868177 := bstep (se 2 (by rfl) ⟨700566, by rfl⟩ : syracuseStep 1868177 = 1401133) B1401133
theorem B4194787 : Blo 1104625 4194787 := bstep (se 1 (by rfl) ⟨3146090, by rfl⟩ : syracuseStep 4194787 = 6292181) B6292181
theorem B1245667 : Blo 1104625 1245667 := bstep (se 1 (by rfl) ⟨934250, by rfl⟩ : syracuseStep 1245667 = 1868501) B1868501
theorem B2097667 : Blo 1104625 2097667 := bstep (se 1 (by rfl) ⟨1573250, by rfl⟩ : syracuseStep 2097667 = 3146501) B3146501
theorem B1868305 : Blo 1104625 1868305 := bstep (se 2 (by rfl) ⟨700614, by rfl⟩ : syracuseStep 1868305 = 1401229) B1401229
theorem B2097713 : Blo 1104625 2097713 := bstep (se 2 (by rfl) ⟨786642, by rfl⟩ : syracuseStep 2097713 = 1573285) B1573285
theorem B2490929 : Blo 1104625 2490929 := bstep (se 2 (by rfl) ⟨934098, by rfl⟩ : syracuseStep 2490929 = 1868197) B1868197
theorem B1868339 : Blo 1104625 1868339 := bstep (se 1 (by rfl) ⟨1401254, by rfl⟩ : syracuseStep 1868339 = 2802509) B2802509
theorem B11960885 : Blo 1104625 11960885 := bstep (se 5 (by rfl) ⟨560666, by rfl⟩ : syracuseStep 11960885 = 1121333) B1121333
theorem B2490947 : Blo 1104625 2490947 := bstep (se 1 (by rfl) ⟨1868210, by rfl⟩ : syracuseStep 2490947 = 3736421) B3736421
theorem B9437795 : Blo 1104625 9437795 := bstep (se 1 (by rfl) ⟨7078346, by rfl⟩ : syracuseStep 9437795 = 14156693) B14156693
theorem B7078499 : Blo 1104625 7078499 := bstep (se 1 (by rfl) ⟨5308874, by rfl⟩ : syracuseStep 7078499 = 10617749) B10617749
theorem B1245811 : Blo 1104625 1245811 := bstep (se 1 (by rfl) ⟨934358, by rfl⟩ : syracuseStep 1245811 = 1868717) B1868717
theorem B3736205 : Blo 1104625 3736205 := bstep (se 3 (by rfl) ⟨700538, by rfl⟩ : syracuseStep 3736205 = 1401077) B1401077
theorem B6816419 : Blo 1104625 6816419 := bstep (se 1 (by rfl) ⟨5112314, by rfl⟩ : syracuseStep 6816419 = 10224629) B10224629
theorem B7570097 : Blo 1104625 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B1868467 : Blo 1104625 1868467 := bstep (se 1 (by rfl) ⟨1401350, by rfl⟩ : syracuseStep 1868467 = 2802701) B2802701
theorem B3736259 : Blo 1104625 3736259 := bstep (se 1 (by rfl) ⟨2802194, by rfl⟩ : syracuseStep 3736259 = 5604389) B5604389
theorem B1245955 : Blo 1104625 1245955 := bstep (se 1 (by rfl) ⟨934466, by rfl⟩ : syracuseStep 1245955 = 1868933) B1868933
theorem B1868609 : Blo 1104625 1868609 := bstep (se 2 (by rfl) ⟨700728, by rfl⟩ : syracuseStep 1868609 = 1401457) B1401457
theorem B2098001 : Blo 1104625 2098001 := bstep (se 2 (by rfl) ⟨786750, by rfl⟩ : syracuseStep 2098001 = 1573501) B1573501
theorem B2491217 : Blo 1104625 2491217 := bstep (se 2 (by rfl) ⟨934206, by rfl⟩ : syracuseStep 2491217 = 1868413) B1868413
theorem B2491235 : Blo 1104625 2491235 := bstep (se 1 (by rfl) ⟨1868426, by rfl⟩ : syracuseStep 2491235 = 3736853) B3736853
theorem B3146627 : Blo 1104625 3146627 := bstep (se 1 (by rfl) ⟨2359970, by rfl⟩ : syracuseStep 3146627 = 4719941) B4719941
theorem B2655121 : Blo 1104625 2655121 := bstep (se 2 (by rfl) ⟨995670, by rfl⟩ : syracuseStep 2655121 = 1991341) B1991341
theorem B1246099 : Blo 1104625 1246099 := bstep (se 1 (by rfl) ⟨934574, by rfl⟩ : syracuseStep 1246099 = 1869149) B1869149
theorem B1868737 : Blo 1104625 1868737 := bstep (se 2 (by rfl) ⟨700776, by rfl⟩ : syracuseStep 1868737 = 1401553) B1401553
theorem B3736529 : Blo 1104625 3736529 := bstep (se 2 (by rfl) ⟨1401198, by rfl⟩ : syracuseStep 3736529 = 2802397) B2802397
theorem B1573843 : Blo 1104625 1573843 := bstep (se 1 (by rfl) ⟨1180382, by rfl⟩ : syracuseStep 1573843 = 2360765) B2360765
theorem B1868771 : Blo 1104625 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B1246243 : Blo 1104625 1246243 := bstep (se 1 (by rfl) ⟨934682, by rfl⟩ : syracuseStep 1246243 = 1869365) B1869365
theorem B2589763 : Blo 1104625 2589763 := bstep (se 1 (by rfl) ⟨1942322, by rfl⟩ : syracuseStep 2589763 = 3884645) B3884645
theorem B2524259 : Blo 1104625 2524259 := bstep (se 1 (by rfl) ⟨1893194, by rfl⟩ : syracuseStep 2524259 = 3786389) B3786389
theorem B1868899 : Blo 1104625 1868899 := bstep (se 1 (by rfl) ⟨1401674, by rfl⟩ : syracuseStep 1868899 = 2803349) B2803349
theorem B2491505 : Blo 1104625 2491505 := bstep (se 2 (by rfl) ⟨934314, by rfl⟩ : syracuseStep 2491505 = 1868629) B1868629
theorem B2491523 : Blo 1104625 2491523 := bstep (se 1 (by rfl) ⟨1868642, by rfl⟩ : syracuseStep 2491523 = 3737285) B3737285
theorem B2131121 : Blo 1104625 2131121 := bstep (se 2 (by rfl) ⟨799170, by rfl⟩ : syracuseStep 2131121 = 1598341) B1598341
theorem B1246387 : Blo 1104625 1246387 := bstep (se 1 (by rfl) ⟨934790, by rfl⟩ : syracuseStep 1246387 = 1869581) B1869581
theorem B3146957 : Blo 1104625 3146957 := bstep (se 3 (by rfl) ⟨590054, by rfl⟩ : syracuseStep 3146957 = 1180109) B1180109
theorem B1869041 : Blo 1104625 1869041 := bstep (se 2 (by rfl) ⟨700890, by rfl⟩ : syracuseStep 1869041 = 1401781) B1401781
theorem B3147025 : Blo 1104625 3147025 := bstep (se 2 (by rfl) ⟨1180134, by rfl⟩ : syracuseStep 3147025 = 2360269) B2360269
theorem B2360593 : Blo 1104625 2360593 := bstep (se 2 (by rfl) ⟨885222, by rfl⟩ : syracuseStep 2360593 = 1770445) B1770445
theorem B1180963 : Blo 1104625 1180963 := bstep (se 1 (by rfl) ⟨885722, by rfl⟩ : syracuseStep 1180963 = 1771445) B1771445
theorem B1770817 : Blo 1104625 1770817 := bstep (se 2 (by rfl) ⟨664056, by rfl⟩ : syracuseStep 1770817 = 1328113) B1328113
theorem B1246531 : Blo 1104625 1246531 := bstep (se 1 (by rfl) ⟨934898, by rfl⟩ : syracuseStep 1246531 = 1869797) B1869797
theorem B1869169 : Blo 1104625 1869169 := bstep (se 2 (by rfl) ⟨700938, by rfl⟩ : syracuseStep 1869169 = 1401877) B1401877
theorem B2491793 : Blo 1104625 2491793 := bstep (se 2 (by rfl) ⟨934422, by rfl⟩ : syracuseStep 2491793 = 1868845) B1868845
theorem B1869203 : Blo 1104625 1869203 := bstep (se 1 (by rfl) ⟨1401902, by rfl⟩ : syracuseStep 1869203 = 2803805) B2803805
theorem B2491811 : Blo 1104625 2491811 := bstep (se 1 (by rfl) ⟨1868858, by rfl⟩ : syracuseStep 2491811 = 3737717) B3737717
theorem B1574321 : Blo 1104625 1574321 := bstep (se 2 (by rfl) ⟨590370, by rfl⟩ : syracuseStep 1574321 = 1180741) B1180741
theorem B1246675 : Blo 1104625 1246675 := bstep (se 1 (by rfl) ⟨935006, by rfl⟩ : syracuseStep 1246675 = 1870013) B1870013
theorem B3737069 : Blo 1104625 3737069 := bstep (se 3 (by rfl) ⟨700700, by rfl⟩ : syracuseStep 3737069 = 1401401) B1401401
theorem B1869331 : Blo 1104625 1869331 := bstep (se 1 (by rfl) ⟨1401998, by rfl⟩ : syracuseStep 1869331 = 2803997) B2803997
theorem B3147299 : Blo 1104625 3147299 := bstep (se 1 (by rfl) ⟨2360474, by rfl⟩ : syracuseStep 3147299 = 4720949) B4720949
theorem B2098723 : Blo 1104625 2098723 := bstep (se 1 (by rfl) ⟨1574042, by rfl⟩ : syracuseStep 2098723 = 3148085) B3148085
theorem B1574435 : Blo 1104625 1574435 := bstep (se 1 (by rfl) ⟨1180826, by rfl⟩ : syracuseStep 1574435 = 2361653) B2361653
theorem B3737123 : Blo 1104625 3737123 := bstep (se 1 (by rfl) ⟨2802842, by rfl⟩ : syracuseStep 3737123 = 5605685) B5605685
theorem B7079501 : Blo 1104625 7079501 := bstep (se 3 (by rfl) ⟨1327406, by rfl⟩ : syracuseStep 7079501 = 2654813) B2654813
theorem B5310029 : Blo 1104625 5310029 := bstep (se 3 (by rfl) ⟨995630, by rfl⟩ : syracuseStep 5310029 = 1991261) B1991261
theorem B1246819 : Blo 1104625 1246819 := bstep (se 1 (by rfl) ⟨935114, by rfl⟩ : syracuseStep 1246819 = 1870229) B1870229
theorem B1574515 : Blo 1104625 1574515 := bstep (se 1 (by rfl) ⟨1180886, by rfl⟩ : syracuseStep 1574515 = 2361773) B2361773
theorem B1869473 : Blo 1104625 1869473 := bstep (se 2 (by rfl) ⟨701052, by rfl⟩ : syracuseStep 1869473 = 1402105) B1402105
theorem B2492081 : Blo 1104625 2492081 := bstep (se 2 (by rfl) ⟨934530, by rfl⟩ : syracuseStep 2492081 = 1869061) B1869061
theorem B2492099 : Blo 1104625 2492099 := bstep (se 1 (by rfl) ⟨1869074, by rfl⟩ : syracuseStep 2492099 = 3738149) B3738149
theorem B3540685 : Blo 1104625 3540685 := bstep (se 3 (by rfl) ⟨663878, by rfl⟩ : syracuseStep 3540685 = 1327757) B1327757
theorem B1246963 : Blo 1104625 1246963 := bstep (se 1 (by rfl) ⟨935222, by rfl⟩ : syracuseStep 1246963 = 1870445) B1870445
theorem B1771265 : Blo 1104625 1771265 := bstep (se 2 (by rfl) ⟨664224, by rfl⟩ : syracuseStep 1771265 = 1328449) B1328449
theorem B15140621 : Blo 1104625 15140621 := bstep (se 3 (by rfl) ⟨2838866, by rfl⟩ : syracuseStep 15140621 = 5677733) B5677733
theorem B1869601 : Blo 1104625 1869601 := bstep (se 2 (by rfl) ⟨701100, by rfl⟩ : syracuseStep 1869601 = 1402201) B1402201
theorem B3737393 : Blo 1104625 3737393 := bstep (se 2 (by rfl) ⟨1401522, by rfl⟩ : syracuseStep 3737393 = 2803045) B2803045
theorem B1869635 : Blo 1104625 1869635 := bstep (se 1 (by rfl) ⟨1402226, by rfl⟩ : syracuseStep 1869635 = 2804453) B2804453
theorem B7669603 : Blo 1104625 7669603 := bstep (se 1 (by rfl) ⟨5752202, by rfl⟩ : syracuseStep 7669603 = 11504405) B11504405
theorem B1247107 : Blo 1104625 1247107 := bstep (se 1 (by rfl) ⟨935330, by rfl⟩ : syracuseStep 1247107 = 1870661) B1870661
theorem B1869763 : Blo 1104625 1869763 := bstep (se 1 (by rfl) ⟨1402322, by rfl⟩ : syracuseStep 1869763 = 2804645) B2804645
theorem B5310413 : Blo 1104625 5310413 := bstep (se 3 (by rfl) ⟨995702, by rfl⟩ : syracuseStep 5310413 = 1991405) B1991405
theorem B2492369 : Blo 1104625 2492369 := bstep (se 2 (by rfl) ⟨934638, by rfl⟩ : syracuseStep 2492369 = 1869277) B1869277
theorem B2099171 : Blo 1104625 2099171 := bstep (se 1 (by rfl) ⟨1574378, by rfl⟩ : syracuseStep 2099171 = 3148757) B3148757
theorem B2492387 : Blo 1104625 2492387 := bstep (se 1 (by rfl) ⟨1869290, by rfl⟩ : syracuseStep 2492387 = 3738581) B3738581
theorem B4720625 : Blo 1104625 4720625 := bstep (se 2 (by rfl) ⟨1770234, by rfl⟩ : syracuseStep 4720625 = 3540469) B3540469
theorem B6391793 : Blo 1104625 6391793 := bstep (se 2 (by rfl) ⟨2396922, by rfl⟩ : syracuseStep 6391793 = 4793845) B4793845
theorem B5605361 : Blo 1104625 5605361 := bstep (se 2 (by rfl) ⟨2102010, by rfl⟩ : syracuseStep 5605361 = 4204021) B4204021
theorem B10651661 : Blo 1104625 10651661 := bstep (se 3 (by rfl) ⟨1997186, by rfl⟩ : syracuseStep 10651661 = 3994373) B3994373
theorem B1869905 : Blo 1104625 1869905 := bstep (se 2 (by rfl) ⟨701214, by rfl⟩ : syracuseStep 1869905 = 1402429) B1402429
theorem B30673009 : Blo 1104625 30673009 := bstep (se 2 (by rfl) ⟨11502378, by rfl⟩ : syracuseStep 30673009 = 23004757) B23004757
theorem B1575073 : Blo 1104625 1575073 := bstep (se 2 (by rfl) ⟨590652, by rfl⟩ : syracuseStep 1575073 = 1181305) B1181305
theorem B28772549 : Blo 1104625 28772549 := bstep (se 4 (by rfl) ⟨2697426, by rfl⟩ : syracuseStep 28772549 = 5394853) B5394853
theorem B1870033 : Blo 1104625 1870033 := bstep (se 2 (by rfl) ⟨701262, by rfl⟩ : syracuseStep 1870033 = 1402525) B1402525
theorem B2492657 : Blo 1104625 2492657 := bstep (se 2 (by rfl) ⟨934746, by rfl⟩ : syracuseStep 2492657 = 1869493) B1869493
theorem B1870067 : Blo 1104625 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B2099459 : Blo 1104625 2099459 := bstep (se 1 (by rfl) ⟨1574594, by rfl⟩ : syracuseStep 2099459 = 3149189) B3149189
theorem B2492675 : Blo 1104625 2492675 := bstep (se 1 (by rfl) ⟨1869506, by rfl⟩ : syracuseStep 2492675 = 3739013) B3739013
theorem B1181971 : Blo 1104625 1181971 := bstep (se 1 (by rfl) ⟨886478, by rfl⟩ : syracuseStep 1181971 = 1772957) B1772957
theorem B7670051 : Blo 1104625 7670051 := bstep (se 1 (by rfl) ⟨5752538, by rfl⟩ : syracuseStep 7670051 = 11505077) B11505077
theorem B3737933 : Blo 1104625 3737933 := bstep (se 3 (by rfl) ⟨700862, by rfl⟩ : syracuseStep 3737933 = 1401725) B1401725
theorem B3148141 : Blo 1104625 3148141 := bstep (se 3 (by rfl) ⟨590276, by rfl⟩ : syracuseStep 3148141 = 1180553) B1180553
theorem B1870195 : Blo 1104625 1870195 := bstep (se 1 (by rfl) ⟨1402646, by rfl⟩ : syracuseStep 1870195 = 2805293) B2805293
theorem B3737987 : Blo 1104625 3737987 := bstep (se 1 (by rfl) ⟨2803490, by rfl⟩ : syracuseStep 3737987 = 5606981) B5606981
theorem B6392305 : Blo 1104625 6392305 := bstep (se 2 (by rfl) ⟨2397114, by rfl⟩ : syracuseStep 6392305 = 4794229) B4794229
theorem B1870337 : Blo 1104625 1870337 := bstep (se 2 (by rfl) ⟨701376, by rfl⟩ : syracuseStep 1870337 = 1402753) B1402753
theorem B3148301 : Blo 1104625 3148301 := bstep (se 3 (by rfl) ⟨590306, by rfl⟩ : syracuseStep 3148301 = 1180613) B1180613
theorem B2492945 : Blo 1104625 2492945 := bstep (se 2 (by rfl) ⟨934854, by rfl⟩ : syracuseStep 2492945 = 1869709) B1869709
theorem B2492963 : Blo 1104625 2492963 := bstep (se 1 (by rfl) ⟨1869722, by rfl⟩ : syracuseStep 2492963 = 3739445) B3739445
theorem B1772131 : Blo 1104625 1772131 := bstep (se 1 (by rfl) ⟨1329098, by rfl⟩ : syracuseStep 1772131 = 2658197) B2658197
theorem B1870465 : Blo 1104625 1870465 := bstep (se 2 (by rfl) ⟨701424, by rfl⟩ : syracuseStep 1870465 = 1402849) B1402849
theorem B4197005 : Blo 1104625 4197005 := bstep (se 3 (by rfl) ⟨786938, by rfl⟩ : syracuseStep 4197005 = 1573877) B1573877
theorem B3738257 : Blo 1104625 3738257 := bstep (se 2 (by rfl) ⟨1401846, by rfl⟩ : syracuseStep 3738257 = 2803693) B2803693
theorem B1870499 : Blo 1104625 1870499 := bstep (se 1 (by rfl) ⟨1402874, by rfl⟩ : syracuseStep 1870499 = 2805749) B2805749
theorem B3148483 : Blo 1104625 3148483 := bstep (se 1 (by rfl) ⟨2361362, by rfl⟩ : syracuseStep 3148483 = 4722725) B4722725
theorem B2362097 : Blo 1104625 2362097 := bstep (se 2 (by rfl) ⟨885786, by rfl⟩ : syracuseStep 2362097 = 1771573) B1771573
theorem B2362115 : Blo 1104625 2362115 := bstep (se 1 (by rfl) ⟨1771586, by rfl⟩ : syracuseStep 2362115 = 3543173) B3543173
theorem B1870627 : Blo 1104625 1870627 := bstep (se 1 (by rfl) ⟨1402970, by rfl⟩ : syracuseStep 1870627 = 2805941) B2805941
theorem B2493233 : Blo 1104625 2493233 := bstep (se 2 (by rfl) ⟨934962, by rfl⟩ : syracuseStep 2493233 = 1869925) B1869925
theorem B2493251 : Blo 1104625 2493251 := bstep (se 1 (by rfl) ⟨1869938, by rfl⟩ : syracuseStep 2493251 = 3739877) B3739877
theorem B1575779 : Blo 1104625 1575779 := bstep (se 1 (by rfl) ⟨1181834, by rfl⟩ : syracuseStep 1575779 = 2363669) B2363669
theorem B1182595 : Blo 1104625 1182595 := bstep (se 1 (by rfl) ⟨886946, by rfl⟩ : syracuseStep 1182595 = 1773893) B1773893
theorem B1870769 : Blo 1104625 1870769 := bstep (se 2 (by rfl) ⟨701538, by rfl⟩ : syracuseStep 1870769 = 1403077) B1403077
theorem B2493521 : Blo 1104625 2493521 := bstep (se 2 (by rfl) ⟨935070, by rfl⟩ : syracuseStep 2493521 = 1870141) B1870141
theorem B2493539 : Blo 1104625 2493539 := bstep (se 1 (by rfl) ⟨1870154, by rfl⟩ : syracuseStep 2493539 = 3740309) B3740309
theorem B3738797 : Blo 1104625 3738797 := bstep (se 3 (by rfl) ⟨701024, by rfl⟩ : syracuseStep 3738797 = 1402049) B1402049
theorem B2100401 : Blo 1104625 2100401 := bstep (se 2 (by rfl) ⟨787650, by rfl⟩ : syracuseStep 2100401 = 1575301) B1575301
theorem B3738851 : Blo 1104625 3738851 := bstep (se 1 (by rfl) ⟨2804138, by rfl⟩ : syracuseStep 3738851 = 5608277) B5608277
theorem B1772803 : Blo 1104625 1772803 := bstep (se 1 (by rfl) ⟨1329602, by rfl⟩ : syracuseStep 1772803 = 2659205) B2659205
theorem B7965965 : Blo 1104625 7965965 := bstep (se 3 (by rfl) ⟨1493618, by rfl⟩ : syracuseStep 7965965 = 2987237) B2987237
theorem B1772849 : Blo 1104625 1772849 := bstep (se 2 (by rfl) ⟨664818, by rfl⟩ : syracuseStep 1772849 = 1329637) B1329637
theorem B2493809 : Blo 1104625 2493809 := bstep (se 2 (by rfl) ⟨935178, by rfl⟩ : syracuseStep 2493809 = 1870357) B1870357
theorem B2493827 : Blo 1104625 2493827 := bstep (se 1 (by rfl) ⟨1870370, by rfl⟩ : syracuseStep 2493827 = 3740741) B3740741
theorem B3542417 : Blo 1104625 3542417 := bstep (se 2 (by rfl) ⟨1328406, by rfl⟩ : syracuseStep 3542417 = 2656813) B2656813
theorem B5606819 : Blo 1104625 5606819 := bstep (se 1 (by rfl) ⟨4205114, by rfl⟩ : syracuseStep 5606819 = 8410229) B8410229
theorem B1576417 : Blo 1104625 1576417 := bstep (se 2 (by rfl) ⟨591156, by rfl⟩ : syracuseStep 1576417 = 1182313) B1182313
theorem B3739121 : Blo 1104625 3739121 := bstep (se 2 (by rfl) ⟨1402170, by rfl⟩ : syracuseStep 3739121 = 2804341) B2804341
theorem B1576531 : Blo 1104625 1576531 := bstep (se 1 (by rfl) ⟨1182398, by rfl⟩ : syracuseStep 1576531 = 2364797) B2364797
theorem B13471373 : Blo 1104625 13471373 := bstep (se 3 (by rfl) ⟨2525882, by rfl⟩ : syracuseStep 13471373 = 5051765) B5051765
theorem B2494097 : Blo 1104625 2494097 := bstep (se 2 (by rfl) ⟨935286, by rfl⟩ : syracuseStep 2494097 = 1870573) B1870573
theorem B2494115 : Blo 1104625 2494115 := bstep (se 1 (by rfl) ⟨1870586, by rfl⟩ : syracuseStep 2494115 = 3741173) B3741173
theorem B1773361 : Blo 1104625 1773361 := bstep (se 2 (by rfl) ⟨665010, by rfl⟩ : syracuseStep 1773361 = 1330021) B1330021
theorem B2494385 : Blo 1104625 2494385 := bstep (se 2 (by rfl) ⟨935394, by rfl⟩ : syracuseStep 2494385 = 1870789) B1870789
theorem B2494403 : Blo 1104625 2494403 := bstep (se 1 (by rfl) ⟨1870802, by rfl⟩ : syracuseStep 2494403 = 3741605) B3741605
theorem B3543043 : Blo 1104625 3543043 := bstep (se 1 (by rfl) ⟨2657282, by rfl⟩ : syracuseStep 3543043 = 5314565) B5314565
theorem B3739661 : Blo 1104625 3739661 := bstep (se 3 (by rfl) ⟨701186, by rfl⟩ : syracuseStep 3739661 = 1402373) B1402373
theorem B3149873 : Blo 1104625 3149873 := bstep (se 2 (by rfl) ⟨1181202, by rfl⟩ : syracuseStep 3149873 = 2362405) B2362405
theorem B2101297 : Blo 1104625 2101297 := bstep (se 2 (by rfl) ⟨787986, by rfl⟩ : syracuseStep 2101297 = 1575973) B1575973
theorem B3739715 : Blo 1104625 3739715 := bstep (se 1 (by rfl) ⟨2804786, by rfl⟩ : syracuseStep 3739715 = 5609573) B5609573
theorem B5607629 : Blo 1104625 5607629 := bstep (se 3 (by rfl) ⟨1051430, by rfl⟩ : syracuseStep 5607629 = 2102861) B2102861
theorem B2101457 : Blo 1104625 2101457 := bstep (se 2 (by rfl) ⟨788046, by rfl⟩ : syracuseStep 2101457 = 1576093) B1576093
theorem B9441521 : Blo 1104625 9441521 := bstep (se 2 (by rfl) ⟨3540570, by rfl⟩ : syracuseStep 9441521 = 7081141) B7081141
theorem B5050673 : Blo 1104625 5050673 := bstep (se 2 (by rfl) ⟨1894002, by rfl⟩ : syracuseStep 5050673 = 3788005) B3788005
theorem B1773905 : Blo 1104625 1773905 := bstep (se 2 (by rfl) ⟨665214, by rfl⟩ : syracuseStep 1773905 = 1330429) B1330429
theorem B3739985 : Blo 1104625 3739985 := bstep (se 2 (by rfl) ⟨1402494, by rfl⟩ : syracuseStep 3739985 = 2804989) B2804989
theorem B2101859 : Blo 1104625 2101859 := bstep (se 1 (by rfl) ⟨1576394, by rfl⟩ : syracuseStep 2101859 = 3152789) B3152789
theorem B2364113 : Blo 1104625 2364113 := bstep (se 2 (by rfl) ⟨886542, by rfl⟩ : syracuseStep 2364113 = 1773085) B1773085
theorem B57447139 : Blo 1104625 57447139 := bstep (se 1 (by rfl) ⟨43085354, by rfl⟩ : syracuseStep 57447139 = 86170709) B86170709
theorem B2659043 : Blo 1104625 2659043 := bstep (se 1 (by rfl) ⟨1994282, by rfl⟩ : syracuseStep 2659043 = 3988565) B3988565
theorem B3740525 : Blo 1104625 3740525 := bstep (se 3 (by rfl) ⟨701348, by rfl⟩ : syracuseStep 3740525 = 1402697) B1402697
theorem B1577875 : Blo 1104625 1577875 := bstep (se 1 (by rfl) ⟨1183406, by rfl⟩ : syracuseStep 1577875 = 2366813) B2366813
theorem B3740579 : Blo 1104625 3740579 := bstep (se 1 (by rfl) ⟨2805434, by rfl⟩ : syracuseStep 3740579 = 5610869) B5610869
theorem B3412945 : Blo 1104625 3412945 := bstep (se 2 (by rfl) ⟨1279854, by rfl⟩ : syracuseStep 3412945 = 2559709) B2559709
theorem B3150829 : Blo 1104625 3150829 := bstep (se 3 (by rfl) ⟨590780, by rfl⟩ : syracuseStep 3150829 = 1181561) B1181561
theorem B2987021 : Blo 1104625 2987021 := bstep (se 3 (by rfl) ⟨560066, by rfl⟩ : syracuseStep 2987021 = 1120133) B1120133
theorem B3740849 : Blo 1104625 3740849 := bstep (se 2 (by rfl) ⟨1402818, by rfl⟩ : syracuseStep 3740849 = 2805637) B2805637
theorem B3544273 : Blo 1104625 3544273 := bstep (se 2 (by rfl) ⟨1329102, by rfl⟩ : syracuseStep 3544273 = 2658205) B2658205
theorem B3151057 : Blo 1104625 3151057 := bstep (se 2 (by rfl) ⟨1181646, by rfl⟩ : syracuseStep 3151057 = 2363293) B2363293
theorem B2364643 : Blo 1104625 2364643 := bstep (se 1 (by rfl) ⟨1773482, by rfl⟩ : syracuseStep 2364643 = 3546965) B3546965
theorem B1774867 : Blo 1104625 1774867 := bstep (se 1 (by rfl) ⟨1331150, by rfl⟩ : syracuseStep 1774867 = 2662301) B2662301
theorem B3151217 : Blo 1104625 3151217 := bstep (se 2 (by rfl) ⟨1181706, by rfl⟩ : syracuseStep 3151217 = 2363413) B2363413
theorem B3151331 : Blo 1104625 3151331 := bstep (se 1 (by rfl) ⟨2363498, by rfl⟩ : syracuseStep 3151331 = 4726997) B4726997
theorem B2102755 : Blo 1104625 2102755 := bstep (se 1 (by rfl) ⟨1577066, by rfl⟩ : syracuseStep 2102755 = 3154133) B3154133
theorem B4199921 : Blo 1104625 4199921 := bstep (se 2 (by rfl) ⟨1574970, by rfl⟩ : syracuseStep 4199921 = 3149941) B3149941
theorem B1775123 : Blo 1104625 1775123 := bstep (se 1 (by rfl) ⟨1331342, by rfl⟩ : syracuseStep 1775123 = 2662685) B2662685
theorem B6395441 : Blo 1104625 6395441 := bstep (se 2 (by rfl) ⟨2398290, by rfl⟩ : syracuseStep 6395441 = 4796581) B4796581
theorem B2102915 : Blo 1104625 2102915 := bstep (se 1 (by rfl) ⟨1577186, by rfl⟩ : syracuseStep 2102915 = 3154373) B3154373
theorem B4724365 : Blo 1104625 4724365 := bstep (se 3 (by rfl) ⟨885818, by rfl⟩ : syracuseStep 4724365 = 1771637) B1771637
theorem B26908301 : Blo 1104625 26908301 := bstep (se 3 (by rfl) ⟨5045306, by rfl⟩ : syracuseStep 26908301 = 10090613) B10090613
theorem B3741389 : Blo 1104625 3741389 := bstep (se 3 (by rfl) ⟨701510, by rfl⟩ : syracuseStep 3741389 = 1403021) B1403021
theorem B1119955 : Blo 1104625 1119955 := bstep (se 1 (by rfl) ⟨839966, by rfl⟩ : syracuseStep 1119955 = 1679933) B1679933
theorem B3741443 : Blo 1104625 3741443 := bstep (se 1 (by rfl) ⟨2806082, by rfl⟩ : syracuseStep 3741443 = 5612165) B5612165
theorem B3544877 : Blo 1104625 3544877 := bstep (se 3 (by rfl) ⟨664664, by rfl⟩ : syracuseStep 3544877 = 1329329) B1329329
theorem B2660273 : Blo 1104625 2660273 := bstep (se 2 (by rfl) ⟨997602, by rfl⟩ : syracuseStep 2660273 = 1995205) B1995205
theorem B3152333 : Blo 1104625 3152333 := bstep (se 3 (by rfl) ⟨591062, by rfl⟩ : syracuseStep 3152333 = 1182125) B1182125
theorem B3152515 : Blo 1104625 3152515 := bstep (se 1 (by rfl) ⟨2364386, by rfl⟩ : syracuseStep 3152515 = 4728773) B4728773
theorem B5675683 : Blo 1104625 5675683 := bstep (se 1 (by rfl) ⟨4256762, by rfl⟩ : syracuseStep 5675683 = 8513525) B8513525
theorem B2366129 : Blo 1104625 2366129 := bstep (se 2 (by rfl) ⟨887298, by rfl⟩ : syracuseStep 2366129 = 1774597) B1774597
theorem B2103985 : Blo 1104625 2103985 := bstep (se 2 (by rfl) ⟨788994, by rfl⟩ : syracuseStep 2103985 = 1577989) B1577989
theorem B2366147 : Blo 1104625 2366147 := bstep (se 1 (by rfl) ⟨1774610, by rfl⟩ : syracuseStep 2366147 = 3549221) B3549221
theorem B3152675 : Blo 1104625 3152675 := bstep (se 1 (by rfl) ⟨2364506, by rfl⟩ : syracuseStep 3152675 = 4729013) B4729013
theorem B4201379 : Blo 1104625 4201379 := bstep (se 1 (by rfl) ⟨3151034, by rfl⟩ : syracuseStep 4201379 = 6302069) B6302069
theorem B5610545 : Blo 1104625 5610545 := bstep (se 2 (by rfl) ⟨2103954, by rfl⟩ : syracuseStep 5610545 = 4207909) B4207909
theorem B7577101 : Blo 1104625 7577101 := bstep (se 3 (by rfl) ⟨1420706, by rfl⟩ : syracuseStep 7577101 = 2841413) B2841413
theorem B12132109 : Blo 1104625 12132109 := bstep (se 3 (by rfl) ⟨2274770, by rfl⟩ : syracuseStep 12132109 = 4549541) B4549541
theorem B3153745 : Blo 1104625 3153745 := bstep (se 2 (by rfl) ⟨1182654, by rfl⟩ : syracuseStep 3153745 = 2365309) B2365309
theorem B4202381 : Blo 1104625 4202381 := bstep (se 3 (by rfl) ⟨787946, by rfl⟩ : syracuseStep 4202381 = 1575893) B1575893
theorem B2367377 : Blo 1104625 2367377 := bstep (se 2 (by rfl) ⟨887766, by rfl⟩ : syracuseStep 2367377 = 1775533) B1775533
theorem B6299653 : Blo 1104625 6299653 := bstep (se 4 (by rfl) ⟨590592, by rfl⟩ : syracuseStep 6299653 = 1181185) B1181185
theorem B28712981 : Blo 1104625 28712981 := bstep (se 6 (by rfl) ⟨672960, by rfl⟩ : syracuseStep 28712981 = 1345921) B1345921
theorem B2990125 : Blo 1104625 2990125 := bstep (se 3 (by rfl) ⟨560648, by rfl⟩ : syracuseStep 2990125 = 1121297) B1121297
theorem B9445517 : Blo 1104625 9445517 := bstep (se 3 (by rfl) ⟨1771034, by rfl⟩ : syracuseStep 9445517 = 3542069) B3542069
theorem B2662627 : Blo 1104625 2662627 := bstep (se 1 (by rfl) ⟨1996970, by rfl⟩ : syracuseStep 2662627 = 3993941) B3993941
theorem B5612003 : Blo 1104625 5612003 := bstep (se 1 (by rfl) ⟨4209002, by rfl⟩ : syracuseStep 5612003 = 8418005) B8418005
theorem B1680115 : Blo 1104625 1680115 := bstep (se 1 (by rfl) ⟨1260086, by rfl⟩ : syracuseStep 1680115 = 2520173) B2520173
theorem B12624821 : Blo 1104625 12624821 := bstep (se 5 (by rfl) ⟨591788, by rfl⟩ : syracuseStep 12624821 = 1183577) B1183577
theorem B3548195 : Blo 1104625 3548195 := bstep (se 1 (by rfl) ⟨2661146, by rfl⟩ : syracuseStep 3548195 = 5322293) B5322293
theorem B3155021 : Blo 1104625 3155021 := bstep (se 3 (by rfl) ⟨591566, by rfl⟩ : syracuseStep 3155021 = 1183133) B1183133
theorem B1418387 : Blo 1104625 1418387 := bstep (se 1 (by rfl) ⟨1063790, by rfl⟩ : syracuseStep 1418387 = 2127581) B2127581
theorem B6726833 : Blo 1104625 6726833 := bstep (se 2 (by rfl) ⟨2522562, by rfl⟩ : syracuseStep 6726833 = 5045125) B5045125
theorem B1123507 : Blo 1104625 1123507 := bstep (se 1 (by rfl) ⟨842630, by rfl⟩ : syracuseStep 1123507 = 1685261) B1685261
theorem B3155203 : Blo 1104625 3155203 := bstep (se 1 (by rfl) ⟨2366402, by rfl⟩ : syracuseStep 3155203 = 4732805) B4732805
theorem B3155249 : Blo 1104625 3155249 := bstep (se 2 (by rfl) ⟨1183218, by rfl⟩ : syracuseStep 3155249 = 2366437) B2366437
theorem B5317987 : Blo 1104625 5317987 := bstep (se 1 (by rfl) ⟨3988490, by rfl⟩ : syracuseStep 5317987 = 7976981) B7976981
theorem B6727025 : Blo 1104625 6727025 := bstep (se 2 (by rfl) ⟨2522634, by rfl⟩ : syracuseStep 6727025 = 5045269) B5045269
theorem B2991629 : Blo 1104625 2991629 := bstep (se 3 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 2991629 = 1121861) B1121861
theorem B2991779 : Blo 1104625 2991779 := bstep (se 1 (by rfl) ⟨2243834, by rfl⟩ : syracuseStep 2991779 = 4487669) B4487669
theorem B7087985 : Blo 1104625 7087985 := bstep (se 2 (by rfl) ⟨2657994, by rfl⟩ : syracuseStep 7087985 = 5315989) B5315989
theorem B4728689 : Blo 1104625 4728689 := bstep (se 2 (by rfl) ⟨1773258, by rfl⟩ : syracuseStep 4728689 = 3546517) B3546517
theorem B3549041 : Blo 1104625 3549041 := bstep (se 2 (by rfl) ⟨1330890, by rfl⟩ : syracuseStep 3549041 = 2661781) B2661781
theorem B4728739 : Blo 1104625 4728739 := bstep (se 1 (by rfl) ⟨3546554, by rfl⟩ : syracuseStep 4728739 = 7093109) B7093109
theorem B3549091 : Blo 1104625 3549091 := bstep (se 1 (by rfl) ⟨2661818, by rfl⟩ : syracuseStep 3549091 = 5323637) B5323637
theorem B6301637 : Blo 1104625 6301637 := bstep (se 4 (by rfl) ⟨590778, by rfl⟩ : syracuseStep 6301637 = 1181557) B1181557
theorem B4204493 : Blo 1104625 4204493 := bstep (se 3 (by rfl) ⟨788342, by rfl⟩ : syracuseStep 4204493 = 1576685) B1576685
theorem B2796241 : Blo 1104625 2796241 := bstep (se 2 (by rfl) ⟨1048590, by rfl⟩ : syracuseStep 2796241 = 2097181) B2097181
theorem B3156707 : Blo 1104625 3156707 := bstep (se 1 (by rfl) ⟨2367530, by rfl⟩ : syracuseStep 3156707 = 4735061) B4735061
theorem B4205297 : Blo 1104625 4205297 := bstep (se 2 (by rfl) ⟨1576986, by rfl⟩ : syracuseStep 4205297 = 3153973) B3153973
theorem B7089059 : Blo 1104625 7089059 := bstep (se 1 (by rfl) ⟨5316794, by rfl⟩ : syracuseStep 7089059 = 10633589) B10633589
theorem B2796515 : Blo 1104625 2796515 := bstep (se 1 (by rfl) ⟨2097386, by rfl⟩ : syracuseStep 2796515 = 4194773) B4194773
theorem B4041827 : Blo 1104625 4041827 := bstep (se 1 (by rfl) ⟨3031370, by rfl⟩ : syracuseStep 4041827 = 6062741) B6062741
theorem B3550321 : Blo 1104625 3550321 := bstep (se 2 (by rfl) ⟨1331370, by rfl⟩ : syracuseStep 3550321 = 2662741) B2662741
theorem B2796707 : Blo 1104625 2796707 := bstep (se 1 (by rfl) ⟨2097530, by rfl⟩ : syracuseStep 2796707 = 4195061) B4195061
theorem B1682657 : Blo 1104625 1682657 := bstep (se 2 (by rfl) ⟨630996, by rfl⟩ : syracuseStep 1682657 = 1261993) B1261993
theorem B11349233 : Blo 1104625 11349233 := bstep (se 2 (by rfl) ⟨4255962, by rfl⟩ : syracuseStep 11349233 = 8511925) B8511925
theorem B4205965 : Blo 1104625 4205965 := bstep (se 3 (by rfl) ⟨788618, by rfl⟩ : syracuseStep 4205965 = 1577237) B1577237
theorem B5320561 : Blo 1104625 5320561 := bstep (se 2 (by rfl) ⟨1995210, by rfl⟩ : syracuseStep 5320561 = 3990421) B3990421
theorem B2797649 : Blo 1104625 2797649 := bstep (se 2 (by rfl) ⟨1049118, by rfl⟩ : syracuseStep 2797649 = 2098237) B2098237
theorem B8400995 : Blo 1104625 8400995 := bstep (se 1 (by rfl) ⟨6300746, by rfl⟩ : syracuseStep 8400995 = 12601493) B12601493
theorem B6926435 : Blo 1104625 6926435 := bstep (se 1 (by rfl) ⟨5194826, by rfl⟩ : syracuseStep 6926435 = 10389653) B10389653
theorem B15544433 : Blo 1104625 15544433 := bstep (se 2 (by rfl) ⟨5829162, by rfl⟩ : syracuseStep 15544433 = 11658325) B11658325
theorem B2797699 : Blo 1104625 2797699 := bstep (se 1 (by rfl) ⟨2098274, by rfl⟩ : syracuseStep 2797699 = 4196549) B4196549
theorem B4206755 : Blo 1104625 4206755 := bstep (se 1 (by rfl) ⟨3155066, by rfl⟩ : syracuseStep 4206755 = 6310133) B6310133
theorem B4731149 : Blo 1104625 4731149 := bstep (se 3 (by rfl) ⟨887090, by rfl⟩ : syracuseStep 4731149 = 1774181) B1774181
theorem B3551501 : Blo 1104625 3551501 := bstep (se 3 (by rfl) ⟨665906, by rfl⟩ : syracuseStep 3551501 = 1331813) B1331813
theorem B2240785 : Blo 1104625 2240785 := bstep (se 2 (by rfl) ⟨840294, by rfl⟩ : syracuseStep 2240785 = 1680589) B1680589
theorem B2797841 : Blo 1104625 2797841 := bstep (se 2 (by rfl) ⟨1049190, by rfl⟩ : syracuseStep 2797841 = 2098381) B2098381
theorem B6075013 : Blo 1104625 6075013 := bstep (se 4 (by rfl) ⟨569532, by rfl⟩ : syracuseStep 6075013 = 1139065) B1139065
theorem B4207409 : Blo 1104625 4207409 := bstep (se 2 (by rfl) ⟨1577778, by rfl⟩ : syracuseStep 4207409 = 3155557) B3155557
theorem B4666481 : Blo 1104625 4666481 := bstep (se 2 (by rfl) ⟨1749930, by rfl⟩ : syracuseStep 4666481 = 3499861) B3499861
theorem B2798833 : Blo 1104625 2798833 := bstep (se 2 (by rfl) ⟨1049562, by rfl⟩ : syracuseStep 2798833 = 2099125) B2099125
theorem B5682659 : Blo 1104625 5682659 := bstep (se 1 (by rfl) ⟨4261994, by rfl⟩ : syracuseStep 5682659 = 8523989) B8523989
theorem B2799107 : Blo 1104625 2799107 := bstep (se 1 (by rfl) ⟨2099330, by rfl⟩ : syracuseStep 2799107 = 4198661) B4198661
theorem B3782189 : Blo 1104625 3782189 := bstep (se 3 (by rfl) ⟨709160, by rfl⟩ : syracuseStep 3782189 = 1418321) B1418321
theorem B14366321 : Blo 1104625 14366321 := bstep (se 2 (by rfl) ⟨5387370, by rfl⟩ : syracuseStep 14366321 = 10774741) B10774741
theorem B2799299 : Blo 1104625 2799299 := bstep (se 1 (by rfl) ⟨2099474, by rfl⟩ : syracuseStep 2799299 = 4198949) B4198949
theorem B6305485 : Blo 1104625 6305485 := bstep (se 3 (by rfl) ⟨1182278, by rfl⟩ : syracuseStep 6305485 = 2364557) B2364557
theorem B5977891 : Blo 1104625 5977891 := bstep (se 1 (by rfl) ⟨4483418, by rfl⟩ : syracuseStep 5977891 = 8966837) B8966837
theorem B14039237 : Blo 1104625 14039237 := bstep (se 4 (by rfl) ⟨1316178, by rfl⟩ : syracuseStep 14039237 = 2632357) B2632357
theorem B4208867 : Blo 1104625 4208867 := bstep (se 1 (by rfl) ⟨3156650, by rfl⟩ : syracuseStep 4208867 = 6313301) B6313301
theorem B4208881 : Blo 1104625 4208881 := bstep (se 2 (by rfl) ⟨1578330, by rfl⟩ : syracuseStep 4208881 = 3156661) B3156661
theorem B1620337 : Blo 1104625 1620337 := bstep (se 2 (by rfl) ⟨607626, by rfl⟩ : syracuseStep 1620337 = 1215253) B1215253
theorem B2800241 : Blo 1104625 2800241 := bstep (se 2 (by rfl) ⟨1050090, by rfl⟩ : syracuseStep 2800241 = 2100181) B2100181
theorem B2800291 : Blo 1104625 2800291 := bstep (se 1 (by rfl) ⟨2100218, by rfl⟩ : syracuseStep 2800291 = 4200437) B4200437
theorem B2800433 : Blo 1104625 2800433 := bstep (se 2 (by rfl) ⟨1050162, by rfl⟩ : syracuseStep 2800433 = 2100325) B2100325
theorem B7093261 : Blo 1104625 7093261 := bstep (se 3 (by rfl) ⟨1329986, by rfl⟩ : syracuseStep 7093261 = 2659973) B2659973
theorem B5750129 : Blo 1104625 5750129 := bstep (se 2 (by rfl) ⟨2156298, by rfl⟩ : syracuseStep 5750129 = 4312597) B4312597
theorem B5324237 : Blo 1104625 5324237 := bstep (se 3 (by rfl) ⟨998294, by rfl⟩ : syracuseStep 5324237 = 1996589) B1996589
theorem B45432373 : Blo 1104625 45432373 := bstep (se 5 (by rfl) ⟨2129642, by rfl⟩ : syracuseStep 45432373 = 4259285) B4259285
theorem B2080337 : Blo 1104625 2080337 := bstep (se 2 (by rfl) ⟨780126, by rfl⟩ : syracuseStep 2080337 = 1560253) B1560253
theorem B1916513 : Blo 1104625 1916513 := bstep (se 2 (by rfl) ⟨718692, by rfl⟩ : syracuseStep 1916513 = 1437385) B1437385
theorem B6307469 : Blo 1104625 6307469 := bstep (se 3 (by rfl) ⟨1182650, by rfl⟩ : syracuseStep 6307469 = 2365301) B2365301
theorem B2801425 : Blo 1104625 2801425 := bstep (se 2 (by rfl) ⟨1050534, by rfl⟩ : syracuseStep 2801425 = 2101069) B2101069
theorem B9453581 : Blo 1104625 9453581 := bstep (se 3 (by rfl) ⟨1772546, by rfl⟩ : syracuseStep 9453581 = 3545093) B3545093
theorem B2801699 : Blo 1104625 2801699 := bstep (se 1 (by rfl) ⟨2101274, by rfl⟩ : syracuseStep 2801699 = 4202549) B4202549
theorem B2801891 : Blo 1104625 2801891 := bstep (se 1 (by rfl) ⟨2101418, by rfl⟩ : syracuseStep 2801891 = 4202837) B4202837
theorem B1327411 : Blo 1104625 1327411 := bstep (se 1 (by rfl) ⟨995558, by rfl⟩ : syracuseStep 1327411 = 1991117) B1991117
theorem B12304781 : Blo 1104625 12304781 := bstep (se 3 (by rfl) ⟨2307146, by rfl⟩ : syracuseStep 12304781 = 4614293) B4614293
theorem B6308401 : Blo 1104625 6308401 := bstep (se 2 (by rfl) ⟨2365650, by rfl⟩ : syracuseStep 6308401 = 4731301) B4731301
theorem B12600035 : Blo 1104625 12600035 := bstep (se 1 (by rfl) ⟨9450026, by rfl⟩ : syracuseStep 12600035 = 18900053) B18900053
theorem B1262339 : Blo 1104625 1262339 := bstep (se 1 (by rfl) ⟨946754, by rfl⟩ : syracuseStep 1262339 = 1893509) B1893509
theorem B53855117 : Blo 1104625 53855117 := bstep (se 3 (by rfl) ⟨10097834, by rfl⟩ : syracuseStep 53855117 = 20195669) B20195669
theorem B5686193 : Blo 1104625 5686193 := bstep (se 2 (by rfl) ⟨2132322, by rfl⟩ : syracuseStep 5686193 = 4264645) B4264645
theorem B2245603 : Blo 1104625 2245603 := bstep (se 1 (by rfl) ⟨1684202, by rfl⟩ : syracuseStep 2245603 = 3368405) B3368405
theorem B2802833 : Blo 1104625 2802833 := bstep (se 2 (by rfl) ⟨1051062, by rfl⟩ : syracuseStep 2802833 = 2102125) B2102125
theorem B2802883 : Blo 1104625 2802883 := bstep (se 1 (by rfl) ⟨2102162, by rfl⟩ : syracuseStep 2802883 = 4204325) B4204325
theorem B8406341 : Blo 1104625 8406341 := bstep (se 4 (by rfl) ⟨788094, by rfl⟩ : syracuseStep 8406341 = 1576189) B1576189
theorem B2803025 : Blo 1104625 2803025 := bstep (se 2 (by rfl) ⟨1051134, by rfl⟩ : syracuseStep 2803025 = 2102269) B2102269
theorem B6309859 : Blo 1104625 6309859 := bstep (se 1 (by rfl) ⟨4732394, by rfl⟩ : syracuseStep 6309859 = 9464789) B9464789
theorem B1656947 : Blo 1104625 1656947 := bstep (se 1 (by rfl) ⟨1242710, by rfl⟩ : syracuseStep 1656947 = 2485421) B2485421
theorem B1656977 : Blo 1104625 1656977 := bstep (se 2 (by rfl) ⟨621366, by rfl⟩ : syracuseStep 1656977 = 1242733) B1242733
theorem B1656995 : Blo 1104625 1656995 := bstep (se 1 (by rfl) ⟨1242746, by rfl⟩ : syracuseStep 1656995 = 2485493) B2485493
theorem B1657025 : Blo 1104625 1657025 := bstep (se 2 (by rfl) ⟨621384, by rfl⟩ : syracuseStep 1657025 = 1242769) B1242769
theorem B1657043 : Blo 1104625 1657043 := bstep (se 1 (by rfl) ⟨1242782, by rfl⟩ : syracuseStep 1657043 = 2485565) B2485565
theorem B1657073 : Blo 1104625 1657073 := bstep (se 2 (by rfl) ⟨621402, by rfl⟩ : syracuseStep 1657073 = 1242805) B1242805
theorem B15157489 : Blo 1104625 15157489 := bstep (se 2 (by rfl) ⟨5684058, by rfl⟩ : syracuseStep 15157489 = 11368117) B11368117
theorem B1657091 : Blo 1104625 1657091 := bstep (se 1 (by rfl) ⟨1242818, by rfl⟩ : syracuseStep 1657091 = 2485637) B2485637
theorem B1657121 : Blo 1104625 1657121 := bstep (se 2 (by rfl) ⟨621420, by rfl⟩ : syracuseStep 1657121 = 1242841) B1242841
theorem B2804017 : Blo 1104625 2804017 := bstep (se 2 (by rfl) ⟨1051506, by rfl⟩ : syracuseStep 2804017 = 2103013) B2103013
theorem B1657139 : Blo 1104625 1657139 := bstep (se 1 (by rfl) ⟨1242854, by rfl⟩ : syracuseStep 1657139 = 2485709) B2485709
theorem B1657169 : Blo 1104625 1657169 := bstep (se 2 (by rfl) ⟨621438, by rfl⟩ : syracuseStep 1657169 = 1242877) B1242877
theorem B1657187 : Blo 1104625 1657187 := bstep (se 1 (by rfl) ⟨1242890, by rfl⟩ : syracuseStep 1657187 = 2485781) B2485781
theorem B1657217 : Blo 1104625 1657217 := bstep (se 2 (by rfl) ⟨621456, by rfl⟩ : syracuseStep 1657217 = 1242913) B1242913
theorem B3361169 : Blo 1104625 3361169 := bstep (se 2 (by rfl) ⟨1260438, by rfl⟩ : syracuseStep 3361169 = 2520877) B2520877
theorem B1657235 : Blo 1104625 1657235 := bstep (se 1 (by rfl) ⟨1242926, by rfl⟩ : syracuseStep 1657235 = 2485853) B2485853
theorem B1657265 : Blo 1104625 1657265 := bstep (se 2 (by rfl) ⟨621474, by rfl⟩ : syracuseStep 1657265 = 1242949) B1242949
theorem B1657283 : Blo 1104625 1657283 := bstep (se 1 (by rfl) ⟨1242962, by rfl⟩ : syracuseStep 1657283 = 2485925) B2485925
theorem B1657313 : Blo 1104625 1657313 := bstep (se 2 (by rfl) ⟨621492, by rfl⟩ : syracuseStep 1657313 = 1242985) B1242985
theorem B6310385 : Blo 1104625 6310385 := bstep (se 2 (by rfl) ⟨2366394, by rfl⟩ : syracuseStep 6310385 = 4732789) B4732789
theorem B1657331 : Blo 1104625 1657331 := bstep (se 1 (by rfl) ⟨1242998, by rfl⟩ : syracuseStep 1657331 = 2485997) B2485997
theorem B3590659 : Blo 1104625 3590659 := bstep (se 1 (by rfl) ⟨2692994, by rfl⟩ : syracuseStep 3590659 = 5385989) B5385989
theorem B1657361 : Blo 1104625 1657361 := bstep (se 2 (by rfl) ⟨621510, by rfl⟩ : syracuseStep 1657361 = 1243021) B1243021
theorem B1657379 : Blo 1104625 1657379 := bstep (se 1 (by rfl) ⟨1243034, by rfl⟩ : syracuseStep 1657379 = 2486069) B2486069
theorem B1657409 : Blo 1104625 1657409 := bstep (se 2 (by rfl) ⟨621528, by rfl⟩ : syracuseStep 1657409 = 1243057) B1243057
theorem B2804291 : Blo 1104625 2804291 := bstep (se 1 (by rfl) ⟨2103218, by rfl⟩ : syracuseStep 2804291 = 4206437) B4206437
theorem B1657427 : Blo 1104625 1657427 := bstep (se 1 (by rfl) ⟨1243070, by rfl⟩ : syracuseStep 1657427 = 2486141) B2486141
theorem B1657457 : Blo 1104625 1657457 := bstep (se 2 (by rfl) ⟨621546, by rfl⟩ : syracuseStep 1657457 = 1243093) B1243093
theorem B1657475 : Blo 1104625 1657475 := bstep (se 1 (by rfl) ⟨1243106, by rfl⟩ : syracuseStep 1657475 = 2486213) B2486213
theorem B1657505 : Blo 1104625 1657505 := bstep (se 2 (by rfl) ⟨621564, by rfl⟩ : syracuseStep 1657505 = 1243129) B1243129
theorem B1657523 : Blo 1104625 1657523 := bstep (se 1 (by rfl) ⟨1243142, by rfl⟩ : syracuseStep 1657523 = 2486285) B2486285
theorem B1657553 : Blo 1104625 1657553 := bstep (se 2 (by rfl) ⟨621582, by rfl⟩ : syracuseStep 1657553 = 1243165) B1243165
theorem B1657571 : Blo 1104625 1657571 := bstep (se 1 (by rfl) ⟨1243178, by rfl⟩ : syracuseStep 1657571 = 2486357) B2486357
theorem B1657601 : Blo 1104625 1657601 := bstep (se 2 (by rfl) ⟨621600, by rfl⟩ : syracuseStep 1657601 = 1243201) B1243201
theorem B2804483 : Blo 1104625 2804483 := bstep (se 1 (by rfl) ⟨2103362, by rfl⟩ : syracuseStep 2804483 = 4206725) B4206725
theorem B1657619 : Blo 1104625 1657619 := bstep (se 1 (by rfl) ⟨1243214, by rfl⟩ : syracuseStep 1657619 = 2486429) B2486429
theorem B1657649 : Blo 1104625 1657649 := bstep (se 2 (by rfl) ⟨621618, by rfl⟩ : syracuseStep 1657649 = 1243237) B1243237
theorem B1657667 : Blo 1104625 1657667 := bstep (se 1 (by rfl) ⟨1243250, by rfl⟩ : syracuseStep 1657667 = 2486501) B2486501
theorem B1657697 : Blo 1104625 1657697 := bstep (se 2 (by rfl) ⟨621636, by rfl⟩ : syracuseStep 1657697 = 1243273) B1243273
theorem B1657715 : Blo 1104625 1657715 := bstep (se 1 (by rfl) ⟨1243286, by rfl⟩ : syracuseStep 1657715 = 2486573) B2486573
theorem B1657745 : Blo 1104625 1657745 := bstep (se 2 (by rfl) ⟨621654, by rfl⟩ : syracuseStep 1657745 = 1243309) B1243309
theorem B1657763 : Blo 1104625 1657763 := bstep (se 1 (by rfl) ⟨1243322, by rfl⟩ : syracuseStep 1657763 = 2486645) B2486645
theorem B1657793 : Blo 1104625 1657793 := bstep (se 2 (by rfl) ⟨621672, by rfl⟩ : syracuseStep 1657793 = 1243345) B1243345
theorem B1657811 : Blo 1104625 1657811 := bstep (se 1 (by rfl) ⟨1243358, by rfl⟩ : syracuseStep 1657811 = 2486717) B2486717
theorem B1657841 : Blo 1104625 1657841 := bstep (se 2 (by rfl) ⟨621690, by rfl⟩ : syracuseStep 1657841 = 1243381) B1243381
theorem B1657859 : Blo 1104625 1657859 := bstep (se 1 (by rfl) ⟨1243394, by rfl⟩ : syracuseStep 1657859 = 2486789) B2486789
theorem B1657889 : Blo 1104625 1657889 := bstep (se 2 (by rfl) ⟨621708, by rfl⟩ : syracuseStep 1657889 = 1243417) B1243417
theorem B1657907 : Blo 1104625 1657907 := bstep (se 1 (by rfl) ⟨1243430, by rfl⟩ : syracuseStep 1657907 = 2486861) B2486861
theorem B1657937 : Blo 1104625 1657937 := bstep (se 2 (by rfl) ⟨621726, by rfl⟩ : syracuseStep 1657937 = 1243453) B1243453
theorem B1657955 : Blo 1104625 1657955 := bstep (se 1 (by rfl) ⟨1243466, by rfl⟩ : syracuseStep 1657955 = 2486933) B2486933
theorem B1657985 : Blo 1104625 1657985 := bstep (se 2 (by rfl) ⟨621744, by rfl⟩ : syracuseStep 1657985 = 1243489) B1243489
theorem B1658003 : Blo 1104625 1658003 := bstep (se 1 (by rfl) ⟨1243502, by rfl⟩ : syracuseStep 1658003 = 2487005) B2487005
theorem B1658033 : Blo 1104625 1658033 := bstep (se 2 (by rfl) ⟨621762, by rfl⟩ : syracuseStep 1658033 = 1243525) B1243525
theorem B1658051 : Blo 1104625 1658051 := bstep (se 1 (by rfl) ⟨1243538, by rfl⟩ : syracuseStep 1658051 = 2487077) B2487077
theorem B3591373 : Blo 1104625 3591373 := bstep (se 3 (by rfl) ⟨673382, by rfl⟩ : syracuseStep 3591373 = 1346765) B1346765
theorem B1658081 : Blo 1104625 1658081 := bstep (se 2 (by rfl) ⟨621780, by rfl⟩ : syracuseStep 1658081 = 1243561) B1243561
theorem B1658099 : Blo 1104625 1658099 := bstep (se 1 (by rfl) ⟨1243574, by rfl⟩ : syracuseStep 1658099 = 2487149) B2487149
theorem B1658129 : Blo 1104625 1658129 := bstep (se 2 (by rfl) ⟨621798, by rfl⟩ : syracuseStep 1658129 = 1243597) B1243597
theorem B1658147 : Blo 1104625 1658147 := bstep (se 1 (by rfl) ⟨1243610, by rfl⟩ : syracuseStep 1658147 = 2487221) B2487221
theorem B1658177 : Blo 1104625 1658177 := bstep (se 2 (by rfl) ⟨621816, by rfl⟩ : syracuseStep 1658177 = 1243633) B1243633
theorem B1658195 : Blo 1104625 1658195 := bstep (se 1 (by rfl) ⟨1243646, by rfl⟩ : syracuseStep 1658195 = 2487293) B2487293
theorem B8965475 : Blo 1104625 8965475 := bstep (se 1 (by rfl) ⟨6724106, by rfl⟩ : syracuseStep 8965475 = 13448213) B13448213
theorem B1658225 : Blo 1104625 1658225 := bstep (se 2 (by rfl) ⟨621834, by rfl⟩ : syracuseStep 1658225 = 1243669) B1243669
theorem B1658243 : Blo 1104625 1658243 := bstep (se 1 (by rfl) ⟨1243682, by rfl⟩ : syracuseStep 1658243 = 2487365) B2487365
theorem B1658273 : Blo 1104625 1658273 := bstep (se 2 (by rfl) ⟨621852, by rfl⟩ : syracuseStep 1658273 = 1243705) B1243705
theorem B1658291 : Blo 1104625 1658291 := bstep (se 1 (by rfl) ⟨1243718, by rfl⟩ : syracuseStep 1658291 = 2487437) B2487437
theorem B1658321 : Blo 1104625 1658321 := bstep (se 2 (by rfl) ⟨621870, by rfl⟩ : syracuseStep 1658321 = 1243741) B1243741
theorem B1658339 : Blo 1104625 1658339 := bstep (se 1 (by rfl) ⟨1243754, by rfl⟩ : syracuseStep 1658339 = 2487509) B2487509
theorem B1658369 : Blo 1104625 1658369 := bstep (se 2 (by rfl) ⟨621888, by rfl⟩ : syracuseStep 1658369 = 1243777) B1243777
theorem B1658387 : Blo 1104625 1658387 := bstep (se 1 (by rfl) ⟨1243790, by rfl⟩ : syracuseStep 1658387 = 2487581) B2487581
theorem B3788333 : Blo 1104625 3788333 := bstep (se 3 (by rfl) ⟨710312, by rfl⟩ : syracuseStep 3788333 = 1420625) B1420625
theorem B1658417 : Blo 1104625 1658417 := bstep (se 2 (by rfl) ⟨621906, by rfl⟩ : syracuseStep 1658417 = 1243813) B1243813
theorem B1658435 : Blo 1104625 1658435 := bstep (se 1 (by rfl) ⟨1243826, by rfl⟩ : syracuseStep 1658435 = 2487653) B2487653
theorem B1658465 : Blo 1104625 1658465 := bstep (se 2 (by rfl) ⟨621924, by rfl⟩ : syracuseStep 1658465 = 1243849) B1243849
theorem B1658483 : Blo 1104625 1658483 := bstep (se 1 (by rfl) ⟨1243862, by rfl⟩ : syracuseStep 1658483 = 2487725) B2487725
theorem B1658513 : Blo 1104625 1658513 := bstep (se 2 (by rfl) ⟨621942, by rfl⟩ : syracuseStep 1658513 = 1243885) B1243885
theorem B1658531 : Blo 1104625 1658531 := bstep (se 1 (by rfl) ⟨1243898, by rfl⟩ : syracuseStep 1658531 = 2487797) B2487797
theorem B2805425 : Blo 1104625 2805425 := bstep (se 2 (by rfl) ⟨1052034, by rfl⟩ : syracuseStep 2805425 = 2104069) B2104069
theorem B1330867 : Blo 1104625 1330867 := bstep (se 1 (by rfl) ⟨998150, by rfl⟩ : syracuseStep 1330867 = 1996301) B1996301
theorem B1658561 : Blo 1104625 1658561 := bstep (se 2 (by rfl) ⟨621960, by rfl⟩ : syracuseStep 1658561 = 1243921) B1243921
theorem B1658579 : Blo 1104625 1658579 := bstep (se 1 (by rfl) ⟨1243934, by rfl⟩ : syracuseStep 1658579 = 2487869) B2487869
theorem B2805475 : Blo 1104625 2805475 := bstep (se 1 (by rfl) ⟨2104106, by rfl⟩ : syracuseStep 2805475 = 4208213) B4208213
theorem B1658609 : Blo 1104625 1658609 := bstep (se 2 (by rfl) ⟨621978, by rfl⟩ : syracuseStep 1658609 = 1243957) B1243957
theorem B1658627 : Blo 1104625 1658627 := bstep (se 1 (by rfl) ⟨1243970, by rfl⟩ : syracuseStep 1658627 = 2487941) B2487941
theorem B1658657 : Blo 1104625 1658657 := bstep (se 2 (by rfl) ⟨621996, by rfl⟩ : syracuseStep 1658657 = 1243993) B1243993
theorem B4542257 : Blo 1104625 4542257 := bstep (se 2 (by rfl) ⟨1703346, by rfl⟩ : syracuseStep 4542257 = 3406693) B3406693
theorem B1658675 : Blo 1104625 1658675 := bstep (se 1 (by rfl) ⟨1244006, by rfl⟩ : syracuseStep 1658675 = 2488013) B2488013
theorem B5984077 : Blo 1104625 5984077 := bstep (se 3 (by rfl) ⟨1122014, by rfl⟩ : syracuseStep 5984077 = 2244029) B2244029
theorem B1658705 : Blo 1104625 1658705 := bstep (se 2 (by rfl) ⟨622014, by rfl⟩ : syracuseStep 1658705 = 1244029) B1244029
theorem B1658723 : Blo 1104625 1658723 := bstep (se 1 (by rfl) ⟨1244042, by rfl⟩ : syracuseStep 1658723 = 2488085) B2488085
theorem B2805617 : Blo 1104625 2805617 := bstep (se 2 (by rfl) ⟨1052106, by rfl⟩ : syracuseStep 2805617 = 2104213) B2104213
theorem B1658753 : Blo 1104625 1658753 := bstep (se 2 (by rfl) ⟨622032, by rfl⟩ : syracuseStep 1658753 = 1244065) B1244065
theorem B1658771 : Blo 1104625 1658771 := bstep (se 1 (by rfl) ⟨1244078, by rfl⟩ : syracuseStep 1658771 = 2488157) B2488157
theorem B6311843 : Blo 1104625 6311843 := bstep (se 1 (by rfl) ⟨4733882, by rfl⟩ : syracuseStep 6311843 = 9467765) B9467765
theorem B1658801 : Blo 1104625 1658801 := bstep (se 2 (by rfl) ⟨622050, by rfl⟩ : syracuseStep 1658801 = 1244101) B1244101
theorem B1658819 : Blo 1104625 1658819 := bstep (se 1 (by rfl) ⟨1244114, by rfl⟩ : syracuseStep 1658819 = 2488229) B2488229
theorem B1658849 : Blo 1104625 1658849 := bstep (se 2 (by rfl) ⟨622068, by rfl⟩ : syracuseStep 1658849 = 1244137) B1244137
theorem B1658867 : Blo 1104625 1658867 := bstep (se 1 (by rfl) ⟨1244150, by rfl⟩ : syracuseStep 1658867 = 2488301) B2488301
theorem B1658897 : Blo 1104625 1658897 := bstep (se 2 (by rfl) ⟨622086, by rfl⟩ : syracuseStep 1658897 = 1244173) B1244173
theorem B1658915 : Blo 1104625 1658915 := bstep (se 1 (by rfl) ⟨1244186, by rfl⟩ : syracuseStep 1658915 = 2488373) B2488373
theorem B1658945 : Blo 1104625 1658945 := bstep (se 2 (by rfl) ⟨622104, by rfl⟩ : syracuseStep 1658945 = 1244209) B1244209
theorem B1658963 : Blo 1104625 1658963 := bstep (se 1 (by rfl) ⟨1244222, by rfl⟩ : syracuseStep 1658963 = 2488445) B2488445
theorem B1658993 : Blo 1104625 1658993 := bstep (se 2 (by rfl) ⟨622122, by rfl⟩ : syracuseStep 1658993 = 1244245) B1244245
theorem B1659011 : Blo 1104625 1659011 := bstep (se 1 (by rfl) ⟨1244258, by rfl⟩ : syracuseStep 1659011 = 2488517) B2488517
theorem B1659041 : Blo 1104625 1659041 := bstep (se 2 (by rfl) ⟨622140, by rfl⟩ : syracuseStep 1659041 = 1244281) B1244281
theorem B1659059 : Blo 1104625 1659059 := bstep (se 1 (by rfl) ⟨1244294, by rfl⟩ : syracuseStep 1659059 = 2488589) B2488589
theorem B1659089 : Blo 1104625 1659089 := bstep (se 2 (by rfl) ⟨622158, by rfl⟩ : syracuseStep 1659089 = 1244317) B1244317
theorem B1659107 : Blo 1104625 1659107 := bstep (se 1 (by rfl) ⟨1244330, by rfl⟩ : syracuseStep 1659107 = 2488661) B2488661
theorem B1659137 : Blo 1104625 1659137 := bstep (se 2 (by rfl) ⟨622176, by rfl⟩ : syracuseStep 1659137 = 1244353) B1244353
theorem B1659155 : Blo 1104625 1659155 := bstep (se 1 (by rfl) ⟨1244366, by rfl⟩ : syracuseStep 1659155 = 2488733) B2488733
theorem B1659185 : Blo 1104625 1659185 := bstep (se 2 (by rfl) ⟨622194, by rfl⟩ : syracuseStep 1659185 = 1244389) B1244389
theorem B1659203 : Blo 1104625 1659203 := bstep (se 1 (by rfl) ⟨1244402, by rfl⟩ : syracuseStep 1659203 = 2488805) B2488805
theorem B1659233 : Blo 1104625 1659233 := bstep (se 2 (by rfl) ⟨622212, by rfl⟩ : syracuseStep 1659233 = 1244425) B1244425
theorem B1659251 : Blo 1104625 1659251 := bstep (se 1 (by rfl) ⟨1244438, by rfl⟩ : syracuseStep 1659251 = 2488877) B2488877
theorem B1659281 : Blo 1104625 1659281 := bstep (se 2 (by rfl) ⟨622230, by rfl⟩ : syracuseStep 1659281 = 1244461) B1244461
theorem B1659299 : Blo 1104625 1659299 := bstep (se 1 (by rfl) ⟨1244474, by rfl⟩ : syracuseStep 1659299 = 2488949) B2488949
theorem B1659329 : Blo 1104625 1659329 := bstep (se 2 (by rfl) ⟨622248, by rfl⟩ : syracuseStep 1659329 = 1244497) B1244497
theorem B1659347 : Blo 1104625 1659347 := bstep (se 1 (by rfl) ⟨1244510, by rfl⟩ : syracuseStep 1659347 = 2489021) B2489021
theorem B1659377 : Blo 1104625 1659377 := bstep (se 2 (by rfl) ⟨622266, by rfl⟩ : syracuseStep 1659377 = 1244533) B1244533
theorem B11981297 : Blo 1104625 11981297 := bstep (se 2 (by rfl) ⟨4492986, by rfl⟩ : syracuseStep 11981297 = 8985973) B8985973
theorem B1659395 : Blo 1104625 1659395 := bstep (se 1 (by rfl) ⟨1244546, by rfl⟩ : syracuseStep 1659395 = 2489093) B2489093
theorem B1659425 : Blo 1104625 1659425 := bstep (se 2 (by rfl) ⟨622284, by rfl⟩ : syracuseStep 1659425 = 1244569) B1244569
theorem B1659443 : Blo 1104625 1659443 := bstep (se 1 (by rfl) ⟨1244582, by rfl⟩ : syracuseStep 1659443 = 2489165) B2489165
theorem B1659473 : Blo 1104625 1659473 := bstep (se 2 (by rfl) ⟨622302, by rfl⟩ : syracuseStep 1659473 = 1244605) B1244605
theorem B1921619 : Blo 1104625 1921619 := bstep (se 1 (by rfl) ⟨1441214, by rfl⟩ : syracuseStep 1921619 = 2882429) B2882429
theorem B1659491 : Blo 1104625 1659491 := bstep (se 1 (by rfl) ⟨1244618, by rfl⟩ : syracuseStep 1659491 = 2489237) B2489237
theorem B1659521 : Blo 1104625 1659521 := bstep (se 2 (by rfl) ⟨622320, by rfl⟩ : syracuseStep 1659521 = 1244641) B1244641
theorem B1659539 : Blo 1104625 1659539 := bstep (se 1 (by rfl) ⟨1244654, by rfl⟩ : syracuseStep 1659539 = 2489309) B2489309
theorem B1659569 : Blo 1104625 1659569 := bstep (se 2 (by rfl) ⟨622338, by rfl⟩ : syracuseStep 1659569 = 1244677) B1244677
theorem B1659587 : Blo 1104625 1659587 := bstep (se 1 (by rfl) ⟨1244690, by rfl⟩ : syracuseStep 1659587 = 2489381) B2489381
theorem B1659617 : Blo 1104625 1659617 := bstep (se 2 (by rfl) ⟨622356, by rfl⟩ : syracuseStep 1659617 = 1244713) B1244713
theorem B1659635 : Blo 1104625 1659635 := bstep (se 1 (by rfl) ⟨1244726, by rfl⟩ : syracuseStep 1659635 = 2489453) B2489453
theorem B10769165 : Blo 1104625 10769165 := bstep (se 3 (by rfl) ⟨2019218, by rfl⟩ : syracuseStep 10769165 = 4038437) B4038437
theorem B1659665 : Blo 1104625 1659665 := bstep (se 2 (by rfl) ⟨622374, by rfl⟩ : syracuseStep 1659665 = 1244749) B1244749
theorem B1659683 : Blo 1104625 1659683 := bstep (se 1 (by rfl) ⟨1244762, by rfl⟩ : syracuseStep 1659683 = 2489525) B2489525
theorem B1659713 : Blo 1104625 1659713 := bstep (se 2 (by rfl) ⟨622392, by rfl⟩ : syracuseStep 1659713 = 1244785) B1244785
theorem B1659731 : Blo 1104625 1659731 := bstep (se 1 (by rfl) ⟨1244798, by rfl⟩ : syracuseStep 1659731 = 2489597) B2489597
theorem B1659761 : Blo 1104625 1659761 := bstep (se 2 (by rfl) ⟨622410, by rfl⟩ : syracuseStep 1659761 = 1244821) B1244821
theorem B1659779 : Blo 1104625 1659779 := bstep (se 1 (by rfl) ⟨1244834, by rfl⟩ : syracuseStep 1659779 = 2489669) B2489669
theorem B1659809 : Blo 1104625 1659809 := bstep (se 2 (by rfl) ⟨622428, by rfl⟩ : syracuseStep 1659809 = 1244857) B1244857
theorem B1659827 : Blo 1104625 1659827 := bstep (se 1 (by rfl) ⟨1244870, by rfl⟩ : syracuseStep 1659827 = 2489741) B2489741
theorem B1659857 : Blo 1104625 1659857 := bstep (se 2 (by rfl) ⟨622446, by rfl⟩ : syracuseStep 1659857 = 1244893) B1244893
theorem B1659875 : Blo 1104625 1659875 := bstep (se 1 (by rfl) ⟨1244906, by rfl⟩ : syracuseStep 1659875 = 2489813) B2489813
theorem B1659905 : Blo 1104625 1659905 := bstep (se 2 (by rfl) ⟨622464, by rfl⟩ : syracuseStep 1659905 = 1244929) B1244929
theorem B1659923 : Blo 1104625 1659923 := bstep (se 1 (by rfl) ⟨1244942, by rfl⟩ : syracuseStep 1659923 = 2489885) B2489885
theorem B1659953 : Blo 1104625 1659953 := bstep (se 2 (by rfl) ⟨622482, by rfl⟩ : syracuseStep 1659953 = 1244965) B1244965
theorem B1659971 : Blo 1104625 1659971 := bstep (se 1 (by rfl) ⟨1244978, by rfl⟩ : syracuseStep 1659971 = 2489957) B2489957
theorem B1660001 : Blo 1104625 1660001 := bstep (se 2 (by rfl) ⟨622500, by rfl⟩ : syracuseStep 1660001 = 1245001) B1245001
theorem B1496161 : Blo 1104625 1496161 := bstep (se 2 (by rfl) ⟨561060, by rfl⟩ : syracuseStep 1496161 = 1122121) B1122121
theorem B1660019 : Blo 1104625 1660019 := bstep (se 1 (by rfl) ⟨1245014, by rfl⟩ : syracuseStep 1660019 = 2490029) B2490029
theorem B1660049 : Blo 1104625 1660049 := bstep (se 2 (by rfl) ⟨622518, by rfl⟩ : syracuseStep 1660049 = 1245037) B1245037
theorem B1660067 : Blo 1104625 1660067 := bstep (se 1 (by rfl) ⟨1245050, by rfl⟩ : syracuseStep 1660067 = 2490101) B2490101
theorem B1660097 : Blo 1104625 1660097 := bstep (se 2 (by rfl) ⟨622536, by rfl⟩ : syracuseStep 1660097 = 1245073) B1245073
theorem B1660115 : Blo 1104625 1660115 := bstep (se 1 (by rfl) ⟨1245086, by rfl⟩ : syracuseStep 1660115 = 2490173) B2490173
theorem B1660145 : Blo 1104625 1660145 := bstep (se 2 (by rfl) ⟨622554, by rfl⟩ : syracuseStep 1660145 = 1245109) B1245109
theorem B1660163 : Blo 1104625 1660163 := bstep (se 1 (by rfl) ⟨1245122, by rfl⟩ : syracuseStep 1660163 = 2490245) B2490245
theorem B42554645 : Blo 1104625 42554645 := bstep (se 6 (by rfl) ⟨997374, by rfl⟩ : syracuseStep 42554645 = 1994749) B1994749
theorem B1660193 : Blo 1104625 1660193 := bstep (se 2 (by rfl) ⟨622572, by rfl⟩ : syracuseStep 1660193 = 1245145) B1245145
theorem B1660211 : Blo 1104625 1660211 := bstep (se 1 (by rfl) ⟨1245158, by rfl⟩ : syracuseStep 1660211 = 2490317) B2490317
theorem B1725761 : Blo 1104625 1725761 := bstep (se 2 (by rfl) ⟨647160, by rfl⟩ : syracuseStep 1725761 = 1294321) B1294321
theorem B1660241 : Blo 1104625 1660241 := bstep (se 2 (by rfl) ⟨622590, by rfl⟩ : syracuseStep 1660241 = 1245181) B1245181
theorem B1660259 : Blo 1104625 1660259 := bstep (se 1 (by rfl) ⟨1245194, by rfl⟩ : syracuseStep 1660259 = 2490389) B2490389
theorem B1660289 : Blo 1104625 1660289 := bstep (se 2 (by rfl) ⟨622608, by rfl⟩ : syracuseStep 1660289 = 1245217) B1245217
theorem B1660307 : Blo 1104625 1660307 := bstep (se 1 (by rfl) ⟨1245230, by rfl⟩ : syracuseStep 1660307 = 2490461) B2490461
theorem B1660337 : Blo 1104625 1660337 := bstep (se 2 (by rfl) ⟨622626, by rfl⟩ : syracuseStep 1660337 = 1245253) B1245253
theorem B1660355 : Blo 1104625 1660355 := bstep (se 1 (by rfl) ⟨1245266, by rfl⟩ : syracuseStep 1660355 = 2490533) B2490533
theorem B1660385 : Blo 1104625 1660385 := bstep (se 2 (by rfl) ⟨622644, by rfl⟩ : syracuseStep 1660385 = 1245289) B1245289
theorem B26891747 : Blo 1104625 26891747 := bstep (se 1 (by rfl) ⟨20168810, by rfl⟩ : syracuseStep 26891747 = 40337621) B40337621
theorem B1660403 : Blo 1104625 1660403 := bstep (se 1 (by rfl) ⟨1245302, by rfl⟩ : syracuseStep 1660403 = 2490605) B2490605
theorem B1660433 : Blo 1104625 1660433 := bstep (se 2 (by rfl) ⟨622662, by rfl⟩ : syracuseStep 1660433 = 1245325) B1245325
theorem B1660451 : Blo 1104625 1660451 := bstep (se 1 (by rfl) ⟨1245338, by rfl⟩ : syracuseStep 1660451 = 2490677) B2490677
theorem B1398323 : Blo 1104625 1398323 := bstep (se 1 (by rfl) ⟨1048742, by rfl⟩ : syracuseStep 1398323 = 2097485) B2097485
theorem B1660481 : Blo 1104625 1660481 := bstep (se 2 (by rfl) ⟨622680, by rfl⟩ : syracuseStep 1660481 = 1245361) B1245361
theorem B1660499 : Blo 1104625 1660499 := bstep (se 1 (by rfl) ⟨1245374, by rfl⟩ : syracuseStep 1660499 = 2490749) B2490749
theorem B1660529 : Blo 1104625 1660529 := bstep (se 2 (by rfl) ⟨622698, by rfl⟩ : syracuseStep 1660529 = 1245397) B1245397
theorem B1660547 : Blo 1104625 1660547 := bstep (se 1 (by rfl) ⟨1245410, by rfl⟩ : syracuseStep 1660547 = 2490821) B2490821
theorem B1660577 : Blo 1104625 1660577 := bstep (se 2 (by rfl) ⟨622716, by rfl⟩ : syracuseStep 1660577 = 1245433) B1245433
theorem B3987107 : Blo 1104625 3987107 := bstep (se 1 (by rfl) ⟨2990330, by rfl⟩ : syracuseStep 3987107 = 5980661) B5980661
theorem B7100081 : Blo 1104625 7100081 := bstep (se 2 (by rfl) ⟨2662530, by rfl⟩ : syracuseStep 7100081 = 5325061) B5325061
theorem B1660595 : Blo 1104625 1660595 := bstep (se 1 (by rfl) ⟨1245446, by rfl⟩ : syracuseStep 1660595 = 2490893) B2490893
theorem B1660625 : Blo 1104625 1660625 := bstep (se 2 (by rfl) ⟨622734, by rfl⟩ : syracuseStep 1660625 = 1245469) B1245469
theorem B1660643 : Blo 1104625 1660643 := bstep (se 1 (by rfl) ⟨1245482, by rfl⟩ : syracuseStep 1660643 = 2490965) B2490965
theorem B1660673 : Blo 1104625 1660673 := bstep (se 2 (by rfl) ⟨622752, by rfl⟩ : syracuseStep 1660673 = 1245505) B1245505
theorem B6313733 : Blo 1104625 6313733 := bstep (se 4 (by rfl) ⟨591912, by rfl⟩ : syracuseStep 6313733 = 1183825) B1183825
theorem B1660691 : Blo 1104625 1660691 := bstep (se 1 (by rfl) ⟨1245518, by rfl⟩ : syracuseStep 1660691 = 2491037) B2491037
theorem B1660721 : Blo 1104625 1660721 := bstep (se 2 (by rfl) ⟨622770, by rfl⟩ : syracuseStep 1660721 = 1245541) B1245541
theorem B1660739 : Blo 1104625 1660739 := bstep (se 1 (by rfl) ⟨1245554, by rfl⟩ : syracuseStep 1660739 = 2491109) B2491109
theorem B7198541 : Blo 1104625 7198541 := bstep (se 3 (by rfl) ⟨1349726, by rfl⟩ : syracuseStep 7198541 = 2699453) B2699453
theorem B1660769 : Blo 1104625 1660769 := bstep (se 2 (by rfl) ⟨622788, by rfl⟩ : syracuseStep 1660769 = 1245577) B1245577
theorem B1660787 : Blo 1104625 1660787 := bstep (se 1 (by rfl) ⟨1245590, by rfl⟩ : syracuseStep 1660787 = 2491181) B2491181
theorem B1660817 : Blo 1104625 1660817 := bstep (se 2 (by rfl) ⟨622806, by rfl⟩ : syracuseStep 1660817 = 1245613) B1245613
theorem B1660835 : Blo 1104625 1660835 := bstep (se 1 (by rfl) ⟨1245626, by rfl⟩ : syracuseStep 1660835 = 2491253) B2491253
theorem B1660865 : Blo 1104625 1660865 := bstep (se 2 (by rfl) ⟨622824, by rfl⟩ : syracuseStep 1660865 = 1245649) B1245649
theorem B1660883 : Blo 1104625 1660883 := bstep (se 1 (by rfl) ⟨1245662, by rfl⟩ : syracuseStep 1660883 = 2491325) B2491325
theorem B1660913 : Blo 1104625 1660913 := bstep (se 2 (by rfl) ⟨622842, by rfl⟩ : syracuseStep 1660913 = 1245685) B1245685
theorem B1660931 : Blo 1104625 1660931 := bstep (se 1 (by rfl) ⟨1245698, by rfl⟩ : syracuseStep 1660931 = 2491397) B2491397
theorem B1660961 : Blo 1104625 1660961 := bstep (se 2 (by rfl) ⟨622860, by rfl⟩ : syracuseStep 1660961 = 1245721) B1245721
theorem B1660979 : Blo 1104625 1660979 := bstep (se 1 (by rfl) ⟨1245734, by rfl⟩ : syracuseStep 1660979 = 2491469) B2491469
theorem B1661009 : Blo 1104625 1661009 := bstep (se 2 (by rfl) ⟨622878, by rfl⟩ : syracuseStep 1661009 = 1245757) B1245757
theorem B1661027 : Blo 1104625 1661027 := bstep (se 1 (by rfl) ⟨1245770, by rfl⟩ : syracuseStep 1661027 = 2491541) B2491541
theorem B3987569 : Blo 1104625 3987569 := bstep (se 2 (by rfl) ⟨1495338, by rfl⟩ : syracuseStep 3987569 = 2990677) B2990677
theorem B1661057 : Blo 1104625 1661057 := bstep (se 2 (by rfl) ⟨622896, by rfl⟩ : syracuseStep 1661057 = 1245793) B1245793
theorem B1661075 : Blo 1104625 1661075 := bstep (se 1 (by rfl) ⟨1245806, by rfl⟩ : syracuseStep 1661075 = 2491613) B2491613
theorem B1661105 : Blo 1104625 1661105 := bstep (se 2 (by rfl) ⟨622914, by rfl⟩ : syracuseStep 1661105 = 1245829) B1245829
theorem B3365059 : Blo 1104625 3365059 := bstep (se 1 (by rfl) ⟨2523794, by rfl⟩ : syracuseStep 3365059 = 5047589) B5047589
theorem B1661123 : Blo 1104625 1661123 := bstep (se 1 (by rfl) ⟨1245842, by rfl⟩ : syracuseStep 1661123 = 2491685) B2491685
theorem B7100621 : Blo 1104625 7100621 := bstep (se 3 (by rfl) ⟨1331366, by rfl⟩ : syracuseStep 7100621 = 2662733) B2662733
theorem B1661153 : Blo 1104625 1661153 := bstep (se 2 (by rfl) ⟨622932, by rfl⟩ : syracuseStep 1661153 = 1245865) B1245865
theorem B1399027 : Blo 1104625 1399027 := bstep (se 1 (by rfl) ⟨1049270, by rfl⟩ : syracuseStep 1399027 = 2098541) B2098541
theorem B1661171 : Blo 1104625 1661171 := bstep (se 1 (by rfl) ⟨1245878, by rfl⟩ : syracuseStep 1661171 = 2491757) B2491757
theorem B1661201 : Blo 1104625 1661201 := bstep (se 2 (by rfl) ⟨622950, by rfl⟩ : syracuseStep 1661201 = 1245901) B1245901
theorem B1661219 : Blo 1104625 1661219 := bstep (se 1 (by rfl) ⟨1245914, by rfl⟩ : syracuseStep 1661219 = 2491829) B2491829
theorem B1661249 : Blo 1104625 1661249 := bstep (se 2 (by rfl) ⟨622968, by rfl⟩ : syracuseStep 1661249 = 1245937) B1245937
theorem B1399123 : Blo 1104625 1399123 := bstep (se 1 (by rfl) ⟨1049342, by rfl⟩ : syracuseStep 1399123 = 2098685) B2098685
theorem B1661267 : Blo 1104625 1661267 := bstep (se 1 (by rfl) ⟨1245950, by rfl⟩ : syracuseStep 1661267 = 2491901) B2491901
theorem B1661297 : Blo 1104625 1661297 := bstep (se 2 (by rfl) ⟨622986, by rfl⟩ : syracuseStep 1661297 = 1245973) B1245973
theorem B1661315 : Blo 1104625 1661315 := bstep (se 1 (by rfl) ⟨1245986, by rfl⟩ : syracuseStep 1661315 = 2491973) B2491973
theorem B1661345 : Blo 1104625 1661345 := bstep (se 2 (by rfl) ⟨623004, by rfl⟩ : syracuseStep 1661345 = 1246009) B1246009
theorem B1661363 : Blo 1104625 1661363 := bstep (se 1 (by rfl) ⟨1246022, by rfl⟩ : syracuseStep 1661363 = 2492045) B2492045
theorem B1661393 : Blo 1104625 1661393 := bstep (se 2 (by rfl) ⟨623022, by rfl⟩ : syracuseStep 1661393 = 1246045) B1246045
theorem B1661411 : Blo 1104625 1661411 := bstep (se 1 (by rfl) ⟨1246058, by rfl⟩ : syracuseStep 1661411 = 2492117) B2492117
theorem B1497571 : Blo 1104625 1497571 := bstep (se 1 (by rfl) ⟨1123178, by rfl⟩ : syracuseStep 1497571 = 2246357) B2246357
theorem B1497587 : Blo 1104625 1497587 := bstep (se 1 (by rfl) ⟨1123190, by rfl⟩ : syracuseStep 1497587 = 2246381) B2246381
theorem B1661441 : Blo 1104625 1661441 := bstep (se 2 (by rfl) ⟨623040, by rfl⟩ : syracuseStep 1661441 = 1246081) B1246081
theorem B1661459 : Blo 1104625 1661459 := bstep (se 1 (by rfl) ⟨1246094, by rfl⟩ : syracuseStep 1661459 = 2492189) B2492189
theorem B1497619 : Blo 1104625 1497619 := bstep (se 1 (by rfl) ⟨1123214, by rfl⟩ : syracuseStep 1497619 = 2246429) B2246429
theorem B1661489 : Blo 1104625 1661489 := bstep (se 2 (by rfl) ⟨623058, by rfl⟩ : syracuseStep 1661489 = 1246117) B1246117
theorem B1661507 : Blo 1104625 1661507 := bstep (se 1 (by rfl) ⟨1246130, by rfl⟩ : syracuseStep 1661507 = 2492261) B2492261
theorem B1661537 : Blo 1104625 1661537 := bstep (se 2 (by rfl) ⟨623076, by rfl⟩ : syracuseStep 1661537 = 1246153) B1246153
theorem B1661555 : Blo 1104625 1661555 := bstep (se 1 (by rfl) ⟨1246166, by rfl⟩ : syracuseStep 1661555 = 2492333) B2492333
theorem B1661585 : Blo 1104625 1661585 := bstep (se 2 (by rfl) ⟨623094, by rfl⟩ : syracuseStep 1661585 = 1246189) B1246189
theorem B1661603 : Blo 1104625 1661603 := bstep (se 1 (by rfl) ⟨1246202, by rfl⟩ : syracuseStep 1661603 = 2492405) B2492405
theorem B12114613 : Blo 1104625 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B1661633 : Blo 1104625 1661633 := bstep (se 2 (by rfl) ⟨623112, by rfl⟩ : syracuseStep 1661633 = 1246225) B1246225
theorem B1661651 : Blo 1104625 1661651 := bstep (se 1 (by rfl) ⟨1246238, by rfl⟩ : syracuseStep 1661651 = 2492477) B2492477
theorem B1661681 : Blo 1104625 1661681 := bstep (se 2 (by rfl) ⟨623130, by rfl⟩ : syracuseStep 1661681 = 1246261) B1246261
theorem B1104627 : Blo 1104625 1104627 := bstep (se 1 (by rfl) ⟨828470, by rfl⟩ : syracuseStep 1104627 = 1656941) B1656941
theorem B1104643 : Blo 1104625 1104643 := bstep (se 1 (by rfl) ⟨828482, by rfl⟩ : syracuseStep 1104643 = 1656965) B1656965
theorem B1661699 : Blo 1104625 1661699 := bstep (se 1 (by rfl) ⟨1246274, by rfl⟩ : syracuseStep 1661699 = 2492549) B2492549
theorem B1104659 : Blo 1104625 1104659 := bstep (se 1 (by rfl) ⟨828494, by rfl⟩ : syracuseStep 1104659 = 1656989) B1656989
theorem B1661729 : Blo 1104625 1661729 := bstep (se 2 (by rfl) ⟨623148, by rfl⟩ : syracuseStep 1661729 = 1246297) B1246297
theorem B1104675 : Blo 1104625 1104675 := bstep (se 1 (by rfl) ⟨828506, by rfl⟩ : syracuseStep 1104675 = 1657013) B1657013
theorem B1104691 : Blo 1104625 1104691 := bstep (se 1 (by rfl) ⟨828518, by rfl⟩ : syracuseStep 1104691 = 1657037) B1657037
theorem B1661747 : Blo 1104625 1661747 := bstep (se 1 (by rfl) ⟨1246310, by rfl⟩ : syracuseStep 1661747 = 2492621) B2492621
theorem B1104707 : Blo 1104625 1104707 := bstep (se 1 (by rfl) ⟨828530, by rfl⟩ : syracuseStep 1104707 = 1657061) B1657061
theorem B1399619 : Blo 1104625 1399619 := bstep (se 1 (by rfl) ⟨1049714, by rfl⟩ : syracuseStep 1399619 = 2099429) B2099429
theorem B1661777 : Blo 1104625 1661777 := bstep (se 2 (by rfl) ⟨623166, by rfl⟩ : syracuseStep 1661777 = 1246333) B1246333
theorem B1104723 : Blo 1104625 1104723 := bstep (se 1 (by rfl) ⟨828542, by rfl⟩ : syracuseStep 1104723 = 1657085) B1657085
theorem B1104739 : Blo 1104625 1104739 := bstep (se 1 (by rfl) ⟨828554, by rfl⟩ : syracuseStep 1104739 = 1657109) B1657109
theorem B1661795 : Blo 1104625 1661795 := bstep (se 1 (by rfl) ⟨1246346, by rfl⟩ : syracuseStep 1661795 = 2492693) B2492693
theorem B1104755 : Blo 1104625 1104755 := bstep (se 1 (by rfl) ⟨828566, by rfl⟩ : syracuseStep 1104755 = 1657133) B1657133
theorem B1661825 : Blo 1104625 1661825 := bstep (se 2 (by rfl) ⟨623184, by rfl⟩ : syracuseStep 1661825 = 1246369) B1246369
theorem B1104771 : Blo 1104625 1104771 := bstep (se 1 (by rfl) ⟨828578, by rfl⟩ : syracuseStep 1104771 = 1657157) B1657157
theorem B1104787 : Blo 1104625 1104787 := bstep (se 1 (by rfl) ⟨828590, by rfl⟩ : syracuseStep 1104787 = 1657181) B1657181
theorem B1661843 : Blo 1104625 1661843 := bstep (se 1 (by rfl) ⟨1246382, by rfl⟩ : syracuseStep 1661843 = 2492765) B2492765
theorem B1104803 : Blo 1104625 1104803 := bstep (se 1 (by rfl) ⟨828602, by rfl⟩ : syracuseStep 1104803 = 1657205) B1657205
theorem B1661873 : Blo 1104625 1661873 := bstep (se 2 (by rfl) ⟨623202, by rfl⟩ : syracuseStep 1661873 = 1246405) B1246405
theorem B1104819 : Blo 1104625 1104819 := bstep (se 1 (by rfl) ⟨828614, by rfl⟩ : syracuseStep 1104819 = 1657229) B1657229
theorem B1104835 : Blo 1104625 1104835 := bstep (se 1 (by rfl) ⟨828626, by rfl⟩ : syracuseStep 1104835 = 1657253) B1657253
theorem B1661891 : Blo 1104625 1661891 := bstep (se 1 (by rfl) ⟨1246418, by rfl⟩ : syracuseStep 1661891 = 2492837) B2492837
theorem B1104851 : Blo 1104625 1104851 := bstep (se 1 (by rfl) ⟨828638, by rfl⟩ : syracuseStep 1104851 = 1657277) B1657277
theorem B1661921 : Blo 1104625 1661921 := bstep (se 2 (by rfl) ⟨623220, by rfl⟩ : syracuseStep 1661921 = 1246441) B1246441
theorem B1104867 : Blo 1104625 1104867 := bstep (se 1 (by rfl) ⟨828650, by rfl⟩ : syracuseStep 1104867 = 1657301) B1657301
theorem B1104883 : Blo 1104625 1104883 := bstep (se 1 (by rfl) ⟨828662, by rfl⟩ : syracuseStep 1104883 = 1657325) B1657325
theorem B1661939 : Blo 1104625 1661939 := bstep (se 1 (by rfl) ⟨1246454, by rfl⟩ : syracuseStep 1661939 = 2492909) B2492909
theorem B1104899 : Blo 1104625 1104899 := bstep (se 1 (by rfl) ⟨828674, by rfl⟩ : syracuseStep 1104899 = 1657349) B1657349
theorem B8412173 : Blo 1104625 8412173 := bstep (se 3 (by rfl) ⟨1577282, by rfl⟩ : syracuseStep 8412173 = 3154565) B3154565
theorem B1661969 : Blo 1104625 1661969 := bstep (se 2 (by rfl) ⟨623238, by rfl⟩ : syracuseStep 1661969 = 1246477) B1246477
theorem B1104915 : Blo 1104625 1104915 := bstep (se 1 (by rfl) ⟨828686, by rfl⟩ : syracuseStep 1104915 = 1657373) B1657373
theorem B1596449 : Blo 1104625 1596449 := bstep (se 2 (by rfl) ⟨598668, by rfl⟩ : syracuseStep 1596449 = 1197337) B1197337
theorem B1104931 : Blo 1104625 1104931 := bstep (se 1 (by rfl) ⟨828698, by rfl⟩ : syracuseStep 1104931 = 1657397) B1657397
theorem B1661987 : Blo 1104625 1661987 := bstep (se 1 (by rfl) ⟨1246490, by rfl⟩ : syracuseStep 1661987 = 2492981) B2492981
theorem B1104947 : Blo 1104625 1104947 := bstep (se 1 (by rfl) ⟨828710, by rfl⟩ : syracuseStep 1104947 = 1657421) B1657421
theorem B1662017 : Blo 1104625 1662017 := bstep (se 2 (by rfl) ⟨623256, by rfl⟩ : syracuseStep 1662017 = 1246513) B1246513
theorem B1104963 : Blo 1104625 1104963 := bstep (se 1 (by rfl) ⟨828722, by rfl⟩ : syracuseStep 1104963 = 1657445) B1657445
theorem B1104979 : Blo 1104625 1104979 := bstep (se 1 (by rfl) ⟨828734, by rfl⟩ : syracuseStep 1104979 = 1657469) B1657469
theorem B1662035 : Blo 1104625 1662035 := bstep (se 1 (by rfl) ⟨1246526, by rfl⟩ : syracuseStep 1662035 = 2493053) B2493053
theorem B1104995 : Blo 1104625 1104995 := bstep (se 1 (by rfl) ⟨828746, by rfl⟩ : syracuseStep 1104995 = 1657493) B1657493
theorem B1662065 : Blo 1104625 1662065 := bstep (se 2 (by rfl) ⟨623274, by rfl⟩ : syracuseStep 1662065 = 1246549) B1246549
theorem B1105011 : Blo 1104625 1105011 := bstep (se 1 (by rfl) ⟨828758, by rfl⟩ : syracuseStep 1105011 = 1657517) B1657517
theorem B1105027 : Blo 1104625 1105027 := bstep (se 1 (by rfl) ⟨828770, by rfl⟩ : syracuseStep 1105027 = 1657541) B1657541
theorem B1662083 : Blo 1104625 1662083 := bstep (se 1 (by rfl) ⟨1246562, by rfl⟩ : syracuseStep 1662083 = 2493125) B2493125
theorem B1105043 : Blo 1104625 1105043 := bstep (se 1 (by rfl) ⟨828782, by rfl⟩ : syracuseStep 1105043 = 1657565) B1657565
theorem B1662113 : Blo 1104625 1662113 := bstep (se 2 (by rfl) ⟨623292, by rfl⟩ : syracuseStep 1662113 = 1246585) B1246585
theorem B1105059 : Blo 1104625 1105059 := bstep (se 1 (by rfl) ⟨828794, by rfl⟩ : syracuseStep 1105059 = 1657589) B1657589
theorem B1105075 : Blo 1104625 1105075 := bstep (se 1 (by rfl) ⟨828806, by rfl⟩ : syracuseStep 1105075 = 1657613) B1657613
theorem B1662131 : Blo 1104625 1662131 := bstep (se 1 (by rfl) ⟨1246598, by rfl⟩ : syracuseStep 1662131 = 2493197) B2493197
theorem B1105091 : Blo 1104625 1105091 := bstep (se 1 (by rfl) ⟨828818, by rfl⟩ : syracuseStep 1105091 = 1657637) B1657637
theorem B1662161 : Blo 1104625 1662161 := bstep (se 2 (by rfl) ⟨623310, by rfl⟩ : syracuseStep 1662161 = 1246621) B1246621
theorem B1105107 : Blo 1104625 1105107 := bstep (se 1 (by rfl) ⟨828830, by rfl⟩ : syracuseStep 1105107 = 1657661) B1657661
theorem B1105123 : Blo 1104625 1105123 := bstep (se 1 (by rfl) ⟨828842, by rfl⟩ : syracuseStep 1105123 = 1657685) B1657685
theorem B1662179 : Blo 1104625 1662179 := bstep (se 1 (by rfl) ⟨1246634, by rfl⟩ : syracuseStep 1662179 = 2493269) B2493269
theorem B1105139 : Blo 1104625 1105139 := bstep (se 1 (by rfl) ⟨828854, by rfl⟩ : syracuseStep 1105139 = 1657709) B1657709
theorem B1662209 : Blo 1104625 1662209 := bstep (se 2 (by rfl) ⟨623328, by rfl⟩ : syracuseStep 1662209 = 1246657) B1246657
theorem B1105155 : Blo 1104625 1105155 := bstep (se 1 (by rfl) ⟨828866, by rfl⟩ : syracuseStep 1105155 = 1657733) B1657733
theorem B1105171 : Blo 1104625 1105171 := bstep (se 1 (by rfl) ⟨828878, by rfl⟩ : syracuseStep 1105171 = 1657757) B1657757
theorem B1662227 : Blo 1104625 1662227 := bstep (se 1 (by rfl) ⟨1246670, by rfl⟩ : syracuseStep 1662227 = 2493341) B2493341
theorem B1105187 : Blo 1104625 1105187 := bstep (se 1 (by rfl) ⟨828890, by rfl⟩ : syracuseStep 1105187 = 1657781) B1657781
theorem B1662257 : Blo 1104625 1662257 := bstep (se 2 (by rfl) ⟨623346, by rfl⟩ : syracuseStep 1662257 = 1246693) B1246693
theorem B1105203 : Blo 1104625 1105203 := bstep (se 1 (by rfl) ⟨828902, by rfl⟩ : syracuseStep 1105203 = 1657805) B1657805
theorem B1105219 : Blo 1104625 1105219 := bstep (se 1 (by rfl) ⟨828914, by rfl⟩ : syracuseStep 1105219 = 1657829) B1657829
theorem B1662275 : Blo 1104625 1662275 := bstep (se 1 (by rfl) ⟨1246706, by rfl⟩ : syracuseStep 1662275 = 2493413) B2493413
theorem B1105235 : Blo 1104625 1105235 := bstep (se 1 (by rfl) ⟨828926, by rfl⟩ : syracuseStep 1105235 = 1657853) B1657853
theorem B1662305 : Blo 1104625 1662305 := bstep (se 2 (by rfl) ⟨623364, by rfl⟩ : syracuseStep 1662305 = 1246729) B1246729
theorem B1105251 : Blo 1104625 1105251 := bstep (se 1 (by rfl) ⟨828938, by rfl⟩ : syracuseStep 1105251 = 1657877) B1657877
theorem B1105267 : Blo 1104625 1105267 := bstep (se 1 (by rfl) ⟨828950, by rfl⟩ : syracuseStep 1105267 = 1657901) B1657901
theorem B1662323 : Blo 1104625 1662323 := bstep (se 1 (by rfl) ⟨1246742, by rfl⟩ : syracuseStep 1662323 = 2493485) B2493485
theorem B1105283 : Blo 1104625 1105283 := bstep (se 1 (by rfl) ⟨828962, by rfl⟩ : syracuseStep 1105283 = 1657925) B1657925
theorem B1662353 : Blo 1104625 1662353 := bstep (se 2 (by rfl) ⟨623382, by rfl⟩ : syracuseStep 1662353 = 1246765) B1246765
theorem B1105299 : Blo 1104625 1105299 := bstep (se 1 (by rfl) ⟨828974, by rfl⟩ : syracuseStep 1105299 = 1657949) B1657949
theorem B1105315 : Blo 1104625 1105315 := bstep (se 1 (by rfl) ⟨828986, by rfl⟩ : syracuseStep 1105315 = 1657973) B1657973
theorem B1662371 : Blo 1104625 1662371 := bstep (se 1 (by rfl) ⟨1246778, by rfl⟩ : syracuseStep 1662371 = 2493557) B2493557
theorem B1105331 : Blo 1104625 1105331 := bstep (se 1 (by rfl) ⟨828998, by rfl⟩ : syracuseStep 1105331 = 1657997) B1657997
theorem B1662401 : Blo 1104625 1662401 := bstep (se 2 (by rfl) ⟨623400, by rfl⟩ : syracuseStep 1662401 = 1246801) B1246801
theorem B1105347 : Blo 1104625 1105347 := bstep (se 1 (by rfl) ⟨829010, by rfl⟩ : syracuseStep 1105347 = 1658021) B1658021
theorem B1105363 : Blo 1104625 1105363 := bstep (se 1 (by rfl) ⟨829022, by rfl⟩ : syracuseStep 1105363 = 1658045) B1658045
theorem B1662419 : Blo 1104625 1662419 := bstep (se 1 (by rfl) ⟨1246814, by rfl⟩ : syracuseStep 1662419 = 2493629) B2493629
theorem B1105379 : Blo 1104625 1105379 := bstep (se 1 (by rfl) ⟨829034, by rfl⟩ : syracuseStep 1105379 = 1658069) B1658069
theorem B1662449 : Blo 1104625 1662449 := bstep (se 2 (by rfl) ⟨623418, by rfl⟩ : syracuseStep 1662449 = 1246837) B1246837
theorem B1105395 : Blo 1104625 1105395 := bstep (se 1 (by rfl) ⟨829046, by rfl⟩ : syracuseStep 1105395 = 1658093) B1658093
theorem B1105411 : Blo 1104625 1105411 := bstep (se 1 (by rfl) ⟨829058, by rfl⟩ : syracuseStep 1105411 = 1658117) B1658117
theorem B1400323 : Blo 1104625 1400323 := bstep (se 1 (by rfl) ⟨1050242, by rfl⟩ : syracuseStep 1400323 = 2100485) B2100485
theorem B1662467 : Blo 1104625 1662467 := bstep (se 1 (by rfl) ⟨1246850, by rfl⟩ : syracuseStep 1662467 = 2493701) B2493701
theorem B1105427 : Blo 1104625 1105427 := bstep (se 1 (by rfl) ⟨829070, by rfl⟩ : syracuseStep 1105427 = 1658141) B1658141
theorem B1662497 : Blo 1104625 1662497 := bstep (se 2 (by rfl) ⟨623436, by rfl⟩ : syracuseStep 1662497 = 1246873) B1246873
theorem B1105443 : Blo 1104625 1105443 := bstep (se 1 (by rfl) ⟨829082, by rfl⟩ : syracuseStep 1105443 = 1658165) B1658165
theorem B1105459 : Blo 1104625 1105459 := bstep (se 1 (by rfl) ⟨829094, by rfl⟩ : syracuseStep 1105459 = 1658189) B1658189
theorem B1662515 : Blo 1104625 1662515 := bstep (se 1 (by rfl) ⟨1246886, by rfl⟩ : syracuseStep 1662515 = 2493773) B2493773
theorem B1105475 : Blo 1104625 1105475 := bstep (se 1 (by rfl) ⟨829106, by rfl⟩ : syracuseStep 1105475 = 1658213) B1658213
theorem B1662545 : Blo 1104625 1662545 := bstep (se 2 (by rfl) ⟨623454, by rfl⟩ : syracuseStep 1662545 = 1246909) B1246909
theorem B1105491 : Blo 1104625 1105491 := bstep (se 1 (by rfl) ⟨829118, by rfl⟩ : syracuseStep 1105491 = 1658237) B1658237
theorem B1105507 : Blo 1104625 1105507 := bstep (se 1 (by rfl) ⟨829130, by rfl⟩ : syracuseStep 1105507 = 1658261) B1658261
theorem B1400419 : Blo 1104625 1400419 := bstep (se 1 (by rfl) ⟨1050314, by rfl⟩ : syracuseStep 1400419 = 2100629) B2100629
theorem B1662563 : Blo 1104625 1662563 := bstep (se 1 (by rfl) ⟨1246922, by rfl⟩ : syracuseStep 1662563 = 2493845) B2493845
theorem B1105523 : Blo 1104625 1105523 := bstep (se 1 (by rfl) ⟨829142, by rfl⟩ : syracuseStep 1105523 = 1658285) B1658285
theorem B1662593 : Blo 1104625 1662593 := bstep (se 2 (by rfl) ⟨623472, by rfl⟩ : syracuseStep 1662593 = 1246945) B1246945
theorem B1105539 : Blo 1104625 1105539 := bstep (se 1 (by rfl) ⟨829154, by rfl⟩ : syracuseStep 1105539 = 1658309) B1658309
theorem B1105555 : Blo 1104625 1105555 := bstep (se 1 (by rfl) ⟨829166, by rfl⟩ : syracuseStep 1105555 = 1658333) B1658333
theorem B1662611 : Blo 1104625 1662611 := bstep (se 1 (by rfl) ⟨1246958, by rfl⟩ : syracuseStep 1662611 = 2493917) B2493917
theorem B1105571 : Blo 1104625 1105571 := bstep (se 1 (by rfl) ⟨829178, by rfl⟩ : syracuseStep 1105571 = 1658357) B1658357
theorem B1662641 : Blo 1104625 1662641 := bstep (se 2 (by rfl) ⟨623490, by rfl⟩ : syracuseStep 1662641 = 1246981) B1246981
theorem B1105587 : Blo 1104625 1105587 := bstep (se 1 (by rfl) ⟨829190, by rfl⟩ : syracuseStep 1105587 = 1658381) B1658381
theorem B1105603 : Blo 1104625 1105603 := bstep (se 1 (by rfl) ⟨829202, by rfl⟩ : syracuseStep 1105603 = 1658405) B1658405
theorem B1662659 : Blo 1104625 1662659 := bstep (se 1 (by rfl) ⟨1246994, by rfl⟩ : syracuseStep 1662659 = 2493989) B2493989
theorem B1105619 : Blo 1104625 1105619 := bstep (se 1 (by rfl) ⟨829214, by rfl⟩ : syracuseStep 1105619 = 1658429) B1658429
theorem B1662689 : Blo 1104625 1662689 := bstep (se 2 (by rfl) ⟨623508, by rfl⟩ : syracuseStep 1662689 = 1247017) B1247017
theorem B1105635 : Blo 1104625 1105635 := bstep (se 1 (by rfl) ⟨829226, by rfl⟩ : syracuseStep 1105635 = 1658453) B1658453
theorem B4316899 : Blo 1104625 4316899 := bstep (se 1 (by rfl) ⟨3237674, by rfl⟩ : syracuseStep 4316899 = 6475349) B6475349
theorem B1105651 : Blo 1104625 1105651 := bstep (se 1 (by rfl) ⟨829238, by rfl⟩ : syracuseStep 1105651 = 1658477) B1658477
theorem B1662707 : Blo 1104625 1662707 := bstep (se 1 (by rfl) ⟨1247030, by rfl⟩ : syracuseStep 1662707 = 2494061) B2494061
theorem B1105667 : Blo 1104625 1105667 := bstep (se 1 (by rfl) ⟨829250, by rfl⟩ : syracuseStep 1105667 = 1658501) B1658501
theorem B1662737 : Blo 1104625 1662737 := bstep (se 2 (by rfl) ⟨623526, by rfl⟩ : syracuseStep 1662737 = 1247053) B1247053
theorem B1105683 : Blo 1104625 1105683 := bstep (se 1 (by rfl) ⟨829262, by rfl⟩ : syracuseStep 1105683 = 1658525) B1658525
theorem B1105699 : Blo 1104625 1105699 := bstep (se 1 (by rfl) ⟨829274, by rfl⟩ : syracuseStep 1105699 = 1658549) B1658549
theorem B1662755 : Blo 1104625 1662755 := bstep (se 1 (by rfl) ⟨1247066, by rfl⟩ : syracuseStep 1662755 = 2494133) B2494133
theorem B1105715 : Blo 1104625 1105715 := bstep (se 1 (by rfl) ⟨829286, by rfl⟩ : syracuseStep 1105715 = 1658573) B1658573
theorem B1662785 : Blo 1104625 1662785 := bstep (se 2 (by rfl) ⟨623544, by rfl⟩ : syracuseStep 1662785 = 1247089) B1247089
theorem B1105731 : Blo 1104625 1105731 := bstep (se 1 (by rfl) ⟨829298, by rfl⟩ : syracuseStep 1105731 = 1658597) B1658597
theorem B1105747 : Blo 1104625 1105747 := bstep (se 1 (by rfl) ⟨829310, by rfl⟩ : syracuseStep 1105747 = 1658621) B1658621
theorem B1662803 : Blo 1104625 1662803 := bstep (se 1 (by rfl) ⟨1247102, by rfl⟩ : syracuseStep 1662803 = 2494205) B2494205
theorem B1105763 : Blo 1104625 1105763 := bstep (se 1 (by rfl) ⟨829322, by rfl⟩ : syracuseStep 1105763 = 1658645) B1658645
theorem B5594993 : Blo 1104625 5594993 := bstep (se 2 (by rfl) ⟨2098122, by rfl⟩ : syracuseStep 5594993 = 4196245) B4196245
theorem B1662833 : Blo 1104625 1662833 := bstep (se 2 (by rfl) ⟨623562, by rfl⟩ : syracuseStep 1662833 = 1247125) B1247125
theorem B1105779 : Blo 1104625 1105779 := bstep (se 1 (by rfl) ⟨829334, by rfl⟩ : syracuseStep 1105779 = 1658669) B1658669
theorem B1105795 : Blo 1104625 1105795 := bstep (se 1 (by rfl) ⟨829346, by rfl⟩ : syracuseStep 1105795 = 1658693) B1658693
theorem B1662851 : Blo 1104625 1662851 := bstep (se 1 (by rfl) ⟨1247138, by rfl⟩ : syracuseStep 1662851 = 2494277) B2494277
theorem B1105811 : Blo 1104625 1105811 := bstep (se 1 (by rfl) ⟨829358, by rfl⟩ : syracuseStep 1105811 = 1658717) B1658717
theorem B1662881 : Blo 1104625 1662881 := bstep (se 2 (by rfl) ⟨623580, by rfl⟩ : syracuseStep 1662881 = 1247161) B1247161
theorem B1105827 : Blo 1104625 1105827 := bstep (se 1 (by rfl) ⟨829370, by rfl⟩ : syracuseStep 1105827 = 1658741) B1658741
theorem B1105843 : Blo 1104625 1105843 := bstep (se 1 (by rfl) ⟨829382, by rfl⟩ : syracuseStep 1105843 = 1658765) B1658765
theorem B1662899 : Blo 1104625 1662899 := bstep (se 1 (by rfl) ⟨1247174, by rfl⟩ : syracuseStep 1662899 = 2494349) B2494349
theorem B1105859 : Blo 1104625 1105859 := bstep (se 1 (by rfl) ⟨829394, by rfl⟩ : syracuseStep 1105859 = 1658789) B1658789
theorem B1662929 : Blo 1104625 1662929 := bstep (se 2 (by rfl) ⟨623598, by rfl⟩ : syracuseStep 1662929 = 1247197) B1247197
theorem B1105875 : Blo 1104625 1105875 := bstep (se 1 (by rfl) ⟨829406, by rfl⟩ : syracuseStep 1105875 = 1658813) B1658813
theorem B1105891 : Blo 1104625 1105891 := bstep (se 1 (by rfl) ⟨829418, by rfl⟩ : syracuseStep 1105891 = 1658837) B1658837
theorem B1105907 : Blo 1104625 1105907 := bstep (se 1 (by rfl) ⟨829430, by rfl⟩ : syracuseStep 1105907 = 1658861) B1658861
theorem B1105923 : Blo 1104625 1105923 := bstep (se 1 (by rfl) ⟨829442, by rfl⟩ : syracuseStep 1105923 = 1658885) B1658885
theorem B1105939 : Blo 1104625 1105939 := bstep (se 1 (by rfl) ⟨829454, by rfl⟩ : syracuseStep 1105939 = 1658909) B1658909
theorem B1105955 : Blo 1104625 1105955 := bstep (se 1 (by rfl) ⟨829466, by rfl⟩ : syracuseStep 1105955 = 1658933) B1658933
theorem B1105971 : Blo 1104625 1105971 := bstep (se 1 (by rfl) ⟨829478, by rfl⟩ : syracuseStep 1105971 = 1658957) B1658957
theorem B1105987 : Blo 1104625 1105987 := bstep (se 1 (by rfl) ⟨829490, by rfl⟩ : syracuseStep 1105987 = 1658981) B1658981
theorem B11952197 : Blo 1104625 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B9592901 : Blo 1104625 9592901 := bstep (se 4 (by rfl) ⟨899334, by rfl⟩ : syracuseStep 9592901 = 1798669) B1798669
theorem B1106003 : Blo 1104625 1106003 := bstep (se 1 (by rfl) ⟨829502, by rfl⟩ : syracuseStep 1106003 = 1659005) B1659005
theorem B1400915 : Blo 1104625 1400915 := bstep (se 1 (by rfl) ⟨1050686, by rfl⟩ : syracuseStep 1400915 = 2101373) B2101373
theorem B1106019 : Blo 1104625 1106019 := bstep (se 1 (by rfl) ⟨829514, by rfl⟩ : syracuseStep 1106019 = 1659029) B1659029
theorem B1106035 : Blo 1104625 1106035 := bstep (se 1 (by rfl) ⟨829526, by rfl⟩ : syracuseStep 1106035 = 1659053) B1659053
theorem B1106051 : Blo 1104625 1106051 := bstep (se 1 (by rfl) ⟨829538, by rfl⟩ : syracuseStep 1106051 = 1659077) B1659077
theorem B1106067 : Blo 1104625 1106067 := bstep (se 1 (by rfl) ⟨829550, by rfl⟩ : syracuseStep 1106067 = 1659101) B1659101
theorem B1106083 : Blo 1104625 1106083 := bstep (se 1 (by rfl) ⟨829562, by rfl⟩ : syracuseStep 1106083 = 1659125) B1659125
theorem B1106099 : Blo 1104625 1106099 := bstep (se 1 (by rfl) ⟨829574, by rfl⟩ : syracuseStep 1106099 = 1659149) B1659149
theorem B1106115 : Blo 1104625 1106115 := bstep (se 1 (by rfl) ⟨829586, by rfl⟩ : syracuseStep 1106115 = 1659173) B1659173
theorem B1106131 : Blo 1104625 1106131 := bstep (se 1 (by rfl) ⟨829598, by rfl⟩ : syracuseStep 1106131 = 1659197) B1659197
theorem B1106147 : Blo 1104625 1106147 := bstep (se 1 (by rfl) ⟨829610, by rfl⟩ : syracuseStep 1106147 = 1659221) B1659221
theorem B1106163 : Blo 1104625 1106163 := bstep (se 1 (by rfl) ⟨829622, by rfl⟩ : syracuseStep 1106163 = 1659245) B1659245
theorem B1106179 : Blo 1104625 1106179 := bstep (se 1 (by rfl) ⟨829634, by rfl⟩ : syracuseStep 1106179 = 1659269) B1659269
theorem B1106195 : Blo 1104625 1106195 := bstep (se 1 (by rfl) ⟨829646, by rfl⟩ : syracuseStep 1106195 = 1659293) B1659293
theorem B1106211 : Blo 1104625 1106211 := bstep (se 1 (by rfl) ⟨829658, by rfl⟩ : syracuseStep 1106211 = 1659317) B1659317
theorem B1106227 : Blo 1104625 1106227 := bstep (se 1 (by rfl) ⟨829670, by rfl⟩ : syracuseStep 1106227 = 1659341) B1659341
theorem B1106243 : Blo 1104625 1106243 := bstep (se 1 (by rfl) ⟨829682, by rfl⟩ : syracuseStep 1106243 = 1659365) B1659365
theorem B1106259 : Blo 1104625 1106259 := bstep (se 1 (by rfl) ⟨829694, by rfl⟩ : syracuseStep 1106259 = 1659389) B1659389
theorem B1106275 : Blo 1104625 1106275 := bstep (se 1 (by rfl) ⟨829706, by rfl⟩ : syracuseStep 1106275 = 1659413) B1659413
theorem B1106291 : Blo 1104625 1106291 := bstep (se 1 (by rfl) ⟨829718, by rfl⟩ : syracuseStep 1106291 = 1659437) B1659437
theorem B1106307 : Blo 1104625 1106307 := bstep (se 1 (by rfl) ⟨829730, by rfl⟩ : syracuseStep 1106307 = 1659461) B1659461
theorem B1106323 : Blo 1104625 1106323 := bstep (se 1 (by rfl) ⟨829742, by rfl⟩ : syracuseStep 1106323 = 1659485) B1659485
theorem B1106339 : Blo 1104625 1106339 := bstep (se 1 (by rfl) ⟨829754, by rfl⟩ : syracuseStep 1106339 = 1659509) B1659509
theorem B1106355 : Blo 1104625 1106355 := bstep (se 1 (by rfl) ⟨829766, by rfl⟩ : syracuseStep 1106355 = 1659533) B1659533
theorem B1106371 : Blo 1104625 1106371 := bstep (se 1 (by rfl) ⟨829778, by rfl⟩ : syracuseStep 1106371 = 1659557) B1659557
theorem B1106387 : Blo 1104625 1106387 := bstep (se 1 (by rfl) ⟨829790, by rfl⟩ : syracuseStep 1106387 = 1659581) B1659581
theorem B1106403 : Blo 1104625 1106403 := bstep (se 1 (by rfl) ⟨829802, by rfl⟩ : syracuseStep 1106403 = 1659605) B1659605
theorem B1106419 : Blo 1104625 1106419 := bstep (se 1 (by rfl) ⟨829814, by rfl⟩ : syracuseStep 1106419 = 1659629) B1659629
theorem B1106435 : Blo 1104625 1106435 := bstep (se 1 (by rfl) ⟨829826, by rfl⟩ : syracuseStep 1106435 = 1659653) B1659653
theorem B1106451 : Blo 1104625 1106451 := bstep (se 1 (by rfl) ⟨829838, by rfl⟩ : syracuseStep 1106451 = 1659677) B1659677
theorem B1106467 : Blo 1104625 1106467 := bstep (se 1 (by rfl) ⟨829850, by rfl⟩ : syracuseStep 1106467 = 1659701) B1659701
theorem B1106483 : Blo 1104625 1106483 := bstep (se 1 (by rfl) ⟨829862, by rfl⟩ : syracuseStep 1106483 = 1659725) B1659725
theorem B1106499 : Blo 1104625 1106499 := bstep (se 1 (by rfl) ⟨829874, by rfl⟩ : syracuseStep 1106499 = 1659749) B1659749
theorem B1106515 : Blo 1104625 1106515 := bstep (se 1 (by rfl) ⟨829886, by rfl⟩ : syracuseStep 1106515 = 1659773) B1659773
theorem B1106531 : Blo 1104625 1106531 := bstep (se 1 (by rfl) ⟨829898, by rfl⟩ : syracuseStep 1106531 = 1659797) B1659797
theorem B1106547 : Blo 1104625 1106547 := bstep (se 1 (by rfl) ⟨829910, by rfl⟩ : syracuseStep 1106547 = 1659821) B1659821
theorem B1106563 : Blo 1104625 1106563 := bstep (se 1 (by rfl) ⟨829922, by rfl⟩ : syracuseStep 1106563 = 1659845) B1659845
theorem B1106579 : Blo 1104625 1106579 := bstep (se 1 (by rfl) ⟨829934, by rfl⟩ : syracuseStep 1106579 = 1659869) B1659869
theorem B1106595 : Blo 1104625 1106595 := bstep (se 1 (by rfl) ⟨829946, by rfl⟩ : syracuseStep 1106595 = 1659893) B1659893
theorem B1106611 : Blo 1104625 1106611 := bstep (se 1 (by rfl) ⟨829958, by rfl⟩ : syracuseStep 1106611 = 1659917) B1659917
theorem B1106627 : Blo 1104625 1106627 := bstep (se 1 (by rfl) ⟨829970, by rfl⟩ : syracuseStep 1106627 = 1659941) B1659941
theorem B1106643 : Blo 1104625 1106643 := bstep (se 1 (by rfl) ⟨829982, by rfl⟩ : syracuseStep 1106643 = 1659965) B1659965
theorem B1106659 : Blo 1104625 1106659 := bstep (se 1 (by rfl) ⟨829994, by rfl⟩ : syracuseStep 1106659 = 1659989) B1659989
theorem B1106675 : Blo 1104625 1106675 := bstep (se 1 (by rfl) ⟨830006, by rfl⟩ : syracuseStep 1106675 = 1660013) B1660013
theorem B1106691 : Blo 1104625 1106691 := bstep (se 1 (by rfl) ⟨830018, by rfl⟩ : syracuseStep 1106691 = 1660037) B1660037
theorem B1106707 : Blo 1104625 1106707 := bstep (se 1 (by rfl) ⟨830030, by rfl⟩ : syracuseStep 1106707 = 1660061) B1660061
theorem B30237461 : Blo 1104625 30237461 := bstep (se 6 (by rfl) ⟨708690, by rfl⟩ : syracuseStep 30237461 = 1417381) B1417381
theorem B1401619 : Blo 1104625 1401619 := bstep (se 1 (by rfl) ⟨1051214, by rfl⟩ : syracuseStep 1401619 = 2102429) B2102429
theorem B1106723 : Blo 1104625 1106723 := bstep (se 1 (by rfl) ⟨830042, by rfl⟩ : syracuseStep 1106723 = 1660085) B1660085
theorem B1106739 : Blo 1104625 1106739 := bstep (se 1 (by rfl) ⟨830054, by rfl⟩ : syracuseStep 1106739 = 1660109) B1660109
theorem B1106755 : Blo 1104625 1106755 := bstep (se 1 (by rfl) ⟨830066, by rfl⟩ : syracuseStep 1106755 = 1660133) B1660133
theorem B1106771 : Blo 1104625 1106771 := bstep (se 1 (by rfl) ⟨830078, by rfl⟩ : syracuseStep 1106771 = 1660157) B1660157
theorem B1106787 : Blo 1104625 1106787 := bstep (se 1 (by rfl) ⟨830090, by rfl⟩ : syracuseStep 1106787 = 1660181) B1660181
theorem B1106803 : Blo 1104625 1106803 := bstep (se 1 (by rfl) ⟨830102, by rfl⟩ : syracuseStep 1106803 = 1660205) B1660205
theorem B1401715 : Blo 1104625 1401715 := bstep (se 1 (by rfl) ⟨1051286, by rfl⟩ : syracuseStep 1401715 = 2102573) B2102573
theorem B1106819 : Blo 1104625 1106819 := bstep (se 1 (by rfl) ⟨830114, by rfl⟩ : syracuseStep 1106819 = 1660229) B1660229
theorem B1106835 : Blo 1104625 1106835 := bstep (se 1 (by rfl) ⟨830126, by rfl⟩ : syracuseStep 1106835 = 1660253) B1660253
theorem B1106851 : Blo 1104625 1106851 := bstep (se 1 (by rfl) ⟨830138, by rfl⟩ : syracuseStep 1106851 = 1660277) B1660277
theorem B1106867 : Blo 1104625 1106867 := bstep (se 1 (by rfl) ⟨830150, by rfl⟩ : syracuseStep 1106867 = 1660301) B1660301
theorem B1106883 : Blo 1104625 1106883 := bstep (se 1 (by rfl) ⟨830162, by rfl⟩ : syracuseStep 1106883 = 1660325) B1660325
theorem B1106899 : Blo 1104625 1106899 := bstep (se 1 (by rfl) ⟨830174, by rfl⟩ : syracuseStep 1106899 = 1660349) B1660349
theorem B1106915 : Blo 1104625 1106915 := bstep (se 1 (by rfl) ⟨830186, by rfl⟩ : syracuseStep 1106915 = 1660373) B1660373
theorem B1106931 : Blo 1104625 1106931 := bstep (se 1 (by rfl) ⟨830198, by rfl⟩ : syracuseStep 1106931 = 1660397) B1660397
theorem B1106947 : Blo 1104625 1106947 := bstep (se 1 (by rfl) ⟨830210, by rfl⟩ : syracuseStep 1106947 = 1660421) B1660421
theorem B1106963 : Blo 1104625 1106963 := bstep (se 1 (by rfl) ⟨830222, by rfl⟩ : syracuseStep 1106963 = 1660445) B1660445
theorem B1106979 : Blo 1104625 1106979 := bstep (se 1 (by rfl) ⟨830234, by rfl⟩ : syracuseStep 1106979 = 1660469) B1660469
theorem B3728429 : Blo 1104625 3728429 := bstep (se 3 (by rfl) ⟨699080, by rfl⟩ : syracuseStep 3728429 = 1398161) B1398161
theorem B1106995 : Blo 1104625 1106995 := bstep (se 1 (by rfl) ⟨830246, by rfl⟩ : syracuseStep 1106995 = 1660493) B1660493
theorem B21292085 : Blo 1104625 21292085 := bstep (se 5 (by rfl) ⟨998066, by rfl⟩ : syracuseStep 21292085 = 1996133) B1996133
theorem B1107011 : Blo 1104625 1107011 := bstep (se 1 (by rfl) ⟨830258, by rfl⟩ : syracuseStep 1107011 = 1660517) B1660517
theorem B1107027 : Blo 1104625 1107027 := bstep (se 1 (by rfl) ⟨830270, by rfl⟩ : syracuseStep 1107027 = 1660541) B1660541
theorem B3728483 : Blo 1104625 3728483 := bstep (se 1 (by rfl) ⟨2796362, by rfl⟩ : syracuseStep 3728483 = 5592725) B5592725
theorem B1107043 : Blo 1104625 1107043 := bstep (se 1 (by rfl) ⟨830282, by rfl⟩ : syracuseStep 1107043 = 1660565) B1660565
theorem B1107059 : Blo 1104625 1107059 := bstep (se 1 (by rfl) ⟨830294, by rfl⟩ : syracuseStep 1107059 = 1660589) B1660589
theorem B1107075 : Blo 1104625 1107075 := bstep (se 1 (by rfl) ⟨830306, by rfl⟩ : syracuseStep 1107075 = 1660613) B1660613
theorem B1107091 : Blo 1104625 1107091 := bstep (se 1 (by rfl) ⟨830318, by rfl⟩ : syracuseStep 1107091 = 1660637) B1660637
theorem B1107107 : Blo 1104625 1107107 := bstep (se 1 (by rfl) ⟨830330, by rfl⟩ : syracuseStep 1107107 = 1660661) B1660661
theorem B1107123 : Blo 1104625 1107123 := bstep (se 1 (by rfl) ⟨830342, by rfl⟩ : syracuseStep 1107123 = 1660685) B1660685
theorem B1107139 : Blo 1104625 1107139 := bstep (se 1 (by rfl) ⟨830354, by rfl⟩ : syracuseStep 1107139 = 1660709) B1660709
theorem B10085573 : Blo 1104625 10085573 := bstep (se 4 (by rfl) ⟨945522, by rfl⟩ : syracuseStep 10085573 = 1891045) B1891045
theorem B1107155 : Blo 1104625 1107155 := bstep (se 1 (by rfl) ⟨830366, by rfl⟩ : syracuseStep 1107155 = 1660733) B1660733
theorem B1107171 : Blo 1104625 1107171 := bstep (se 1 (by rfl) ⟨830378, by rfl⟩ : syracuseStep 1107171 = 1660757) B1660757
theorem B1107187 : Blo 1104625 1107187 := bstep (se 1 (by rfl) ⟨830390, by rfl⟩ : syracuseStep 1107187 = 1660781) B1660781
theorem B1107203 : Blo 1104625 1107203 := bstep (se 1 (by rfl) ⟨830402, by rfl⟩ : syracuseStep 1107203 = 1660805) B1660805
theorem B3990797 : Blo 1104625 3990797 := bstep (se 3 (by rfl) ⟨748274, by rfl⟩ : syracuseStep 3990797 = 1496549) B1496549
theorem B1991953 : Blo 1104625 1991953 := bstep (se 2 (by rfl) ⟨746982, by rfl⟩ : syracuseStep 1991953 = 1493965) B1493965
theorem B1107219 : Blo 1104625 1107219 := bstep (se 1 (by rfl) ⟨830414, by rfl⟩ : syracuseStep 1107219 = 1660829) B1660829
theorem B5596451 : Blo 1104625 5596451 := bstep (se 1 (by rfl) ⟨4197338, by rfl⟩ : syracuseStep 5596451 = 8394677) B8394677
theorem B1107235 : Blo 1104625 1107235 := bstep (se 1 (by rfl) ⟨830426, by rfl⟩ : syracuseStep 1107235 = 1660853) B1660853
theorem B1107251 : Blo 1104625 1107251 := bstep (se 1 (by rfl) ⟨830438, by rfl⟩ : syracuseStep 1107251 = 1660877) B1660877
theorem B1107267 : Blo 1104625 1107267 := bstep (se 1 (by rfl) ⟨830450, by rfl⟩ : syracuseStep 1107267 = 1660901) B1660901
theorem B1107283 : Blo 1104625 1107283 := bstep (se 1 (by rfl) ⟨830462, by rfl⟩ : syracuseStep 1107283 = 1660925) B1660925
theorem B1107299 : Blo 1104625 1107299 := bstep (se 1 (by rfl) ⟨830474, by rfl⟩ : syracuseStep 1107299 = 1660949) B1660949
theorem B3990883 : Blo 1104625 3990883 := bstep (se 1 (by rfl) ⟨2993162, by rfl⟩ : syracuseStep 3990883 = 5986325) B5986325
theorem B1402211 : Blo 1104625 1402211 := bstep (se 1 (by rfl) ⟨1051658, by rfl⟩ : syracuseStep 1402211 = 2103317) B2103317
theorem B3728753 : Blo 1104625 3728753 := bstep (se 2 (by rfl) ⟨1398282, by rfl⟩ : syracuseStep 3728753 = 2796565) B2796565
theorem B1107315 : Blo 1104625 1107315 := bstep (se 1 (by rfl) ⟨830486, by rfl⟩ : syracuseStep 1107315 = 1660973) B1660973
theorem B1107331 : Blo 1104625 1107331 := bstep (se 1 (by rfl) ⟨830498, by rfl⟩ : syracuseStep 1107331 = 1660997) B1660997
theorem B1107347 : Blo 1104625 1107347 := bstep (se 1 (by rfl) ⟨830510, by rfl⟩ : syracuseStep 1107347 = 1661021) B1661021
theorem B1107363 : Blo 1104625 1107363 := bstep (se 1 (by rfl) ⟨830522, by rfl⟩ : syracuseStep 1107363 = 1661045) B1661045
theorem B1107379 : Blo 1104625 1107379 := bstep (se 1 (by rfl) ⟨830534, by rfl⟩ : syracuseStep 1107379 = 1661069) B1661069
theorem B1107395 : Blo 1104625 1107395 := bstep (se 1 (by rfl) ⟨830546, by rfl⟩ : syracuseStep 1107395 = 1661093) B1661093
theorem B1107411 : Blo 1104625 1107411 := bstep (se 1 (by rfl) ⟨830558, by rfl⟩ : syracuseStep 1107411 = 1661117) B1661117
theorem B1107427 : Blo 1104625 1107427 := bstep (se 1 (by rfl) ⟨830570, by rfl⟩ : syracuseStep 1107427 = 1661141) B1661141
theorem B3368429 : Blo 1104625 3368429 := bstep (se 3 (by rfl) ⟨631580, by rfl⟩ : syracuseStep 3368429 = 1263161) B1263161
theorem B1107443 : Blo 1104625 1107443 := bstep (se 1 (by rfl) ⟨830582, by rfl⟩ : syracuseStep 1107443 = 1661165) B1661165
theorem B1107459 : Blo 1104625 1107459 := bstep (se 1 (by rfl) ⟨830594, by rfl⟩ : syracuseStep 1107459 = 1661189) B1661189
theorem B4548109 : Blo 1104625 4548109 := bstep (se 3 (by rfl) ⟨852770, by rfl⟩ : syracuseStep 4548109 = 1705541) B1705541
theorem B1107475 : Blo 1104625 1107475 := bstep (se 1 (by rfl) ⟨830606, by rfl⟩ : syracuseStep 1107475 = 1661213) B1661213
theorem B1107491 : Blo 1104625 1107491 := bstep (se 1 (by rfl) ⟨830618, by rfl⟩ : syracuseStep 1107491 = 1661237) B1661237
theorem B1107507 : Blo 1104625 1107507 := bstep (se 1 (by rfl) ⟨830630, by rfl⟩ : syracuseStep 1107507 = 1661261) B1661261
theorem B1107523 : Blo 1104625 1107523 := bstep (se 1 (by rfl) ⟨830642, by rfl⟩ : syracuseStep 1107523 = 1661285) B1661285
theorem B1107539 : Blo 1104625 1107539 := bstep (se 1 (by rfl) ⟨830654, by rfl⟩ : syracuseStep 1107539 = 1661309) B1661309
theorem B1107555 : Blo 1104625 1107555 := bstep (se 1 (by rfl) ⟨830666, by rfl⟩ : syracuseStep 1107555 = 1661333) B1661333
theorem B3368561 : Blo 1104625 3368561 := bstep (se 2 (by rfl) ⟨1263210, by rfl⟩ : syracuseStep 3368561 = 2526421) B2526421
theorem B25585265 : Blo 1104625 25585265 := bstep (se 2 (by rfl) ⟨9594474, by rfl⟩ : syracuseStep 25585265 = 19188949) B19188949
theorem B1107571 : Blo 1104625 1107571 := bstep (se 1 (by rfl) ⟨830678, by rfl⟩ : syracuseStep 1107571 = 1661357) B1661357
theorem B1107587 : Blo 1104625 1107587 := bstep (se 1 (by rfl) ⟨830690, by rfl⟩ : syracuseStep 1107587 = 1661381) B1661381
theorem B1107603 : Blo 1104625 1107603 := bstep (se 1 (by rfl) ⟨830702, by rfl⟩ : syracuseStep 1107603 = 1661405) B1661405
theorem B1107619 : Blo 1104625 1107619 := bstep (se 1 (by rfl) ⟨830714, by rfl⟩ : syracuseStep 1107619 = 1661429) B1661429
theorem B1107635 : Blo 1104625 1107635 := bstep (se 1 (by rfl) ⟨830726, by rfl⟩ : syracuseStep 1107635 = 1661453) B1661453
theorem B1107651 : Blo 1104625 1107651 := bstep (se 1 (by rfl) ⟨830738, by rfl⟩ : syracuseStep 1107651 = 1661477) B1661477
theorem B1107667 : Blo 1104625 1107667 := bstep (se 1 (by rfl) ⟨830750, by rfl⟩ : syracuseStep 1107667 = 1661501) B1661501
theorem B1107683 : Blo 1104625 1107683 := bstep (se 1 (by rfl) ⟨830762, by rfl⟩ : syracuseStep 1107683 = 1661525) B1661525
theorem B1107699 : Blo 1104625 1107699 := bstep (se 1 (by rfl) ⟨830774, by rfl⟩ : syracuseStep 1107699 = 1661549) B1661549
theorem B1107715 : Blo 1104625 1107715 := bstep (se 1 (by rfl) ⟨830786, by rfl⟩ : syracuseStep 1107715 = 1661573) B1661573
theorem B1107731 : Blo 1104625 1107731 := bstep (se 1 (by rfl) ⟨830798, by rfl⟩ : syracuseStep 1107731 = 1661597) B1661597
theorem B1107747 : Blo 1104625 1107747 := bstep (se 1 (by rfl) ⟨830810, by rfl⟩ : syracuseStep 1107747 = 1661621) B1661621
theorem B1107763 : Blo 1104625 1107763 := bstep (se 1 (by rfl) ⟨830822, by rfl⟩ : syracuseStep 1107763 = 1661645) B1661645
theorem B28796725 : Blo 1104625 28796725 := bstep (se 5 (by rfl) ⟨1349846, by rfl⟩ : syracuseStep 28796725 = 2699693) B2699693
theorem B1107779 : Blo 1104625 1107779 := bstep (se 1 (by rfl) ⟨830834, by rfl⟩ : syracuseStep 1107779 = 1661669) B1661669
theorem B1107795 : Blo 1104625 1107795 := bstep (se 1 (by rfl) ⟨830846, by rfl⟩ : syracuseStep 1107795 = 1661693) B1661693
theorem B1107811 : Blo 1104625 1107811 := bstep (se 1 (by rfl) ⟨830858, by rfl⟩ : syracuseStep 1107811 = 1661717) B1661717
theorem B8415089 : Blo 1104625 8415089 := bstep (se 2 (by rfl) ⟨3155658, by rfl⟩ : syracuseStep 8415089 = 6311317) B6311317
theorem B1107827 : Blo 1104625 1107827 := bstep (se 1 (by rfl) ⟨830870, by rfl⟩ : syracuseStep 1107827 = 1661741) B1661741
theorem B1107843 : Blo 1104625 1107843 := bstep (se 1 (by rfl) ⟨830882, by rfl⟩ : syracuseStep 1107843 = 1661765) B1661765
theorem B3729293 : Blo 1104625 3729293 := bstep (se 3 (by rfl) ⟨699242, by rfl⟩ : syracuseStep 3729293 = 1398485) B1398485
theorem B1107859 : Blo 1104625 1107859 := bstep (se 1 (by rfl) ⟨830894, by rfl⟩ : syracuseStep 1107859 = 1661789) B1661789
theorem B1107875 : Blo 1104625 1107875 := bstep (se 1 (by rfl) ⟨830906, by rfl⟩ : syracuseStep 1107875 = 1661813) B1661813
theorem B1107891 : Blo 1104625 1107891 := bstep (se 1 (by rfl) ⟨830918, by rfl⟩ : syracuseStep 1107891 = 1661837) B1661837
theorem B3729347 : Blo 1104625 3729347 := bstep (se 1 (by rfl) ⟨2797010, by rfl⟩ : syracuseStep 3729347 = 5594021) B5594021
theorem B1107907 : Blo 1104625 1107907 := bstep (se 1 (by rfl) ⟨830930, by rfl⟩ : syracuseStep 1107907 = 1661861) B1661861
theorem B1796051 : Blo 1104625 1796051 := bstep (se 1 (by rfl) ⟨1347038, by rfl⟩ : syracuseStep 1796051 = 2694077) B2694077
theorem B1107923 : Blo 1104625 1107923 := bstep (se 1 (by rfl) ⟨830942, by rfl⟩ : syracuseStep 1107923 = 1661885) B1661885
theorem B1107939 : Blo 1104625 1107939 := bstep (se 1 (by rfl) ⟨830954, by rfl⟩ : syracuseStep 1107939 = 1661909) B1661909
theorem B1107955 : Blo 1104625 1107955 := bstep (se 1 (by rfl) ⟨830966, by rfl⟩ : syracuseStep 1107955 = 1661933) B1661933
theorem B1107971 : Blo 1104625 1107971 := bstep (se 1 (by rfl) ⟨830978, by rfl⟩ : syracuseStep 1107971 = 1661957) B1661957
theorem B1107987 : Blo 1104625 1107987 := bstep (se 1 (by rfl) ⟨830990, by rfl⟩ : syracuseStep 1107987 = 1661981) B1661981
theorem B1108003 : Blo 1104625 1108003 := bstep (se 1 (by rfl) ⟨831002, by rfl⟩ : syracuseStep 1108003 = 1662005) B1662005
theorem B1402915 : Blo 1104625 1402915 := bstep (se 1 (by rfl) ⟨1052186, by rfl⟩ : syracuseStep 1402915 = 2104373) B2104373
theorem B1108019 : Blo 1104625 1108019 := bstep (se 1 (by rfl) ⟨831014, by rfl⟩ : syracuseStep 1108019 = 1662029) B1662029
theorem B19163189 : Blo 1104625 19163189 := bstep (se 5 (by rfl) ⟨898274, by rfl⟩ : syracuseStep 19163189 = 1796549) B1796549
theorem B1108035 : Blo 1104625 1108035 := bstep (se 1 (by rfl) ⟨831026, by rfl⟩ : syracuseStep 1108035 = 1662053) B1662053
theorem B5597261 : Blo 1104625 5597261 := bstep (se 3 (by rfl) ⟨1049486, by rfl⟩ : syracuseStep 5597261 = 2098973) B2098973
theorem B1108051 : Blo 1104625 1108051 := bstep (se 1 (by rfl) ⟨831038, by rfl⟩ : syracuseStep 1108051 = 1662077) B1662077
theorem B1108067 : Blo 1104625 1108067 := bstep (se 1 (by rfl) ⟨831050, by rfl⟩ : syracuseStep 1108067 = 1662101) B1662101
theorem B1108083 : Blo 1104625 1108083 := bstep (se 1 (by rfl) ⟨831062, by rfl⟩ : syracuseStep 1108083 = 1662125) B1662125
theorem B1108099 : Blo 1104625 1108099 := bstep (se 1 (by rfl) ⟨831074, by rfl⟩ : syracuseStep 1108099 = 1662149) B1662149
theorem B1403011 : Blo 1104625 1403011 := bstep (se 1 (by rfl) ⟨1052258, by rfl⟩ : syracuseStep 1403011 = 2104517) B2104517
theorem B1108115 : Blo 1104625 1108115 := bstep (se 1 (by rfl) ⟨831086, by rfl⟩ : syracuseStep 1108115 = 1662173) B1662173
theorem B1108131 : Blo 1104625 1108131 := bstep (se 1 (by rfl) ⟨831098, by rfl⟩ : syracuseStep 1108131 = 1662197) B1662197
theorem B1108147 : Blo 1104625 1108147 := bstep (se 1 (by rfl) ⟨831110, by rfl⟩ : syracuseStep 1108147 = 1662221) B1662221
theorem B1992899 : Blo 1104625 1992899 := bstep (se 1 (by rfl) ⟨1494674, by rfl⟩ : syracuseStep 1992899 = 2989349) B2989349
theorem B1108163 : Blo 1104625 1108163 := bstep (se 1 (by rfl) ⟨831122, by rfl⟩ : syracuseStep 1108163 = 1662245) B1662245
theorem B3729617 : Blo 1104625 3729617 := bstep (se 2 (by rfl) ⟨1398606, by rfl⟩ : syracuseStep 3729617 = 2797213) B2797213
theorem B1108179 : Blo 1104625 1108179 := bstep (se 1 (by rfl) ⟨831134, by rfl⟩ : syracuseStep 1108179 = 1662269) B1662269
theorem B1108195 : Blo 1104625 1108195 := bstep (se 1 (by rfl) ⟨831146, by rfl⟩ : syracuseStep 1108195 = 1662293) B1662293
theorem B1108211 : Blo 1104625 1108211 := bstep (se 1 (by rfl) ⟨831158, by rfl⟩ : syracuseStep 1108211 = 1662317) B1662317
theorem B1108227 : Blo 1104625 1108227 := bstep (se 1 (by rfl) ⟨831170, by rfl⟩ : syracuseStep 1108227 = 1662341) B1662341
theorem B1108243 : Blo 1104625 1108243 := bstep (se 1 (by rfl) ⟨831182, by rfl⟩ : syracuseStep 1108243 = 1662365) B1662365
theorem B1108259 : Blo 1104625 1108259 := bstep (se 1 (by rfl) ⟨831194, by rfl⟩ : syracuseStep 1108259 = 1662389) B1662389
theorem B1108275 : Blo 1104625 1108275 := bstep (se 1 (by rfl) ⟨831206, by rfl⟩ : syracuseStep 1108275 = 1662413) B1662413
theorem B1108291 : Blo 1104625 1108291 := bstep (se 1 (by rfl) ⟨831218, by rfl⟩ : syracuseStep 1108291 = 1662437) B1662437
theorem B1108307 : Blo 1104625 1108307 := bstep (se 1 (by rfl) ⟨831230, by rfl⟩ : syracuseStep 1108307 = 1662461) B1662461
theorem B1108323 : Blo 1104625 1108323 := bstep (se 1 (by rfl) ⟨831242, by rfl⟩ : syracuseStep 1108323 = 1662485) B1662485
theorem B1108339 : Blo 1104625 1108339 := bstep (se 1 (by rfl) ⟨831254, by rfl⟩ : syracuseStep 1108339 = 1662509) B1662509
theorem B1108355 : Blo 1104625 1108355 := bstep (se 1 (by rfl) ⟨831266, by rfl⟩ : syracuseStep 1108355 = 1662533) B1662533
theorem B1108371 : Blo 1104625 1108371 := bstep (se 1 (by rfl) ⟨831278, by rfl⟩ : syracuseStep 1108371 = 1662557) B1662557
theorem B1108387 : Blo 1104625 1108387 := bstep (se 1 (by rfl) ⟨831290, by rfl⟩ : syracuseStep 1108387 = 1662581) B1662581
theorem B1108403 : Blo 1104625 1108403 := bstep (se 1 (by rfl) ⟨831302, by rfl⟩ : syracuseStep 1108403 = 1662605) B1662605
theorem B1108419 : Blo 1104625 1108419 := bstep (se 1 (by rfl) ⟨831314, by rfl⟩ : syracuseStep 1108419 = 1662629) B1662629
theorem B1599953 : Blo 1104625 1599953 := bstep (se 2 (by rfl) ⟨599982, by rfl⟩ : syracuseStep 1599953 = 1199965) B1199965
theorem B1108435 : Blo 1104625 1108435 := bstep (se 1 (by rfl) ⟨831326, by rfl⟩ : syracuseStep 1108435 = 1662653) B1662653
theorem B1993187 : Blo 1104625 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B1108451 : Blo 1104625 1108451 := bstep (se 1 (by rfl) ⟨831338, by rfl⟩ : syracuseStep 1108451 = 1662677) B1662677
theorem B1108467 : Blo 1104625 1108467 := bstep (se 1 (by rfl) ⟨831350, by rfl⟩ : syracuseStep 1108467 = 1662701) B1662701
theorem B1108483 : Blo 1104625 1108483 := bstep (se 1 (by rfl) ⟨831362, by rfl⟩ : syracuseStep 1108483 = 1662725) B1662725
theorem B1108499 : Blo 1104625 1108499 := bstep (se 1 (by rfl) ⟨831374, by rfl⟩ : syracuseStep 1108499 = 1662749) B1662749
theorem B1108515 : Blo 1104625 1108515 := bstep (se 1 (by rfl) ⟨831386, by rfl⟩ : syracuseStep 1108515 = 1662773) B1662773
theorem B1108531 : Blo 1104625 1108531 := bstep (se 1 (by rfl) ⟨831398, by rfl⟩ : syracuseStep 1108531 = 1662797) B1662797
theorem B1108547 : Blo 1104625 1108547 := bstep (se 1 (by rfl) ⟨831410, by rfl⟩ : syracuseStep 1108547 = 1662821) B1662821
theorem B1108563 : Blo 1104625 1108563 := bstep (se 1 (by rfl) ⟨831422, by rfl⟩ : syracuseStep 1108563 = 1662845) B1662845
theorem B1108579 : Blo 1104625 1108579 := bstep (se 1 (by rfl) ⟨831434, by rfl⟩ : syracuseStep 1108579 = 1662869) B1662869
theorem B1108595 : Blo 1104625 1108595 := bstep (se 1 (by rfl) ⟨831446, by rfl⟩ : syracuseStep 1108595 = 1662893) B1662893
theorem B1108611 : Blo 1104625 1108611 := bstep (se 1 (by rfl) ⟨831458, by rfl⟩ : syracuseStep 1108611 = 1662917) B1662917
theorem B3730157 : Blo 1104625 3730157 := bstep (se 3 (by rfl) ⟨699404, by rfl⟩ : syracuseStep 3730157 = 1398809) B1398809
theorem B3730211 : Blo 1104625 3730211 := bstep (se 1 (by rfl) ⟨2797658, by rfl⟩ : syracuseStep 3730211 = 5595317) B5595317
theorem B3730481 : Blo 1104625 3730481 := bstep (se 2 (by rfl) ⟨1398930, by rfl⟩ : syracuseStep 3730481 = 2797861) B2797861
theorem B2485457 : Blo 1104625 2485457 := bstep (se 2 (by rfl) ⟨932046, by rfl⟩ : syracuseStep 2485457 = 1864093) B1864093
theorem B2485475 : Blo 1104625 2485475 := bstep (se 1 (by rfl) ⟨1864106, by rfl⟩ : syracuseStep 2485475 = 3728213) B3728213
theorem B2485745 : Blo 1104625 2485745 := bstep (se 2 (by rfl) ⟨932154, by rfl⟩ : syracuseStep 2485745 = 1864309) B1864309
theorem B2485763 : Blo 1104625 2485763 := bstep (se 1 (by rfl) ⟨1864322, by rfl⟩ : syracuseStep 2485763 = 3728645) B3728645
theorem B3731021 : Blo 1104625 3731021 := bstep (se 3 (by rfl) ⟨699566, by rfl⟩ : syracuseStep 3731021 = 1399133) B1399133
theorem B1994339 : Blo 1104625 1994339 := bstep (se 1 (by rfl) ⟨1495754, by rfl⟩ : syracuseStep 1994339 = 2991509) B2991509
theorem B3731075 : Blo 1104625 3731075 := bstep (se 1 (by rfl) ⟨2798306, by rfl⟩ : syracuseStep 3731075 = 5596613) B5596613
theorem B2486033 : Blo 1104625 2486033 := bstep (se 2 (by rfl) ⟨932262, by rfl⟩ : syracuseStep 2486033 = 1864525) B1864525
theorem B2486051 : Blo 1104625 2486051 := bstep (se 1 (by rfl) ⟨1864538, by rfl⟩ : syracuseStep 2486051 = 3729077) B3729077
theorem B3993421 : Blo 1104625 3993421 := bstep (se 3 (by rfl) ⟨748766, by rfl⟩ : syracuseStep 3993421 = 1497533) B1497533
theorem B6811505 : Blo 1104625 6811505 := bstep (se 2 (by rfl) ⟨2554314, by rfl⟩ : syracuseStep 6811505 = 5108629) B5108629
theorem B3731345 : Blo 1104625 3731345 := bstep (se 2 (by rfl) ⟨1399254, by rfl⟩ : syracuseStep 3731345 = 2798509) B2798509
theorem B2486321 : Blo 1104625 2486321 := bstep (se 2 (by rfl) ⟨932370, by rfl⟩ : syracuseStep 2486321 = 1864741) B1864741
theorem B2486339 : Blo 1104625 2486339 := bstep (se 1 (by rfl) ⟨1864754, by rfl⟩ : syracuseStep 2486339 = 3729509) B3729509
theorem B2486609 : Blo 1104625 2486609 := bstep (se 2 (by rfl) ⟨932478, by rfl⟩ : syracuseStep 2486609 = 1864957) B1864957
theorem B2486627 : Blo 1104625 2486627 := bstep (se 1 (by rfl) ⟨1864970, by rfl⟩ : syracuseStep 2486627 = 3729941) B3729941
theorem B3731885 : Blo 1104625 3731885 := bstep (se 3 (by rfl) ⟨699728, by rfl⟩ : syracuseStep 3731885 = 1399457) B1399457
theorem B1864147 : Blo 1104625 1864147 := bstep (se 1 (by rfl) ⟨1398110, by rfl⟩ : syracuseStep 1864147 = 2796221) B2796221
theorem B3731939 : Blo 1104625 3731939 := bstep (se 1 (by rfl) ⟨2798954, by rfl⟩ : syracuseStep 3731939 = 5597909) B5597909
theorem B1864289 : Blo 1104625 1864289 := bstep (se 2 (by rfl) ⟨699108, by rfl⟩ : syracuseStep 1864289 = 1398217) B1398217
theorem B2486897 : Blo 1104625 2486897 := bstep (se 2 (by rfl) ⟨932586, by rfl⟩ : syracuseStep 2486897 = 1865173) B1865173
theorem B2486915 : Blo 1104625 2486915 := bstep (se 1 (by rfl) ⟨1865186, by rfl⟩ : syracuseStep 2486915 = 3730373) B3730373
theorem B1864417 : Blo 1104625 1864417 := bstep (se 2 (by rfl) ⟨699156, by rfl⟩ : syracuseStep 1864417 = 1398313) B1398313
theorem B3732209 : Blo 1104625 3732209 := bstep (se 2 (by rfl) ⟨1399578, by rfl⟩ : syracuseStep 3732209 = 2799157) B2799157
theorem B1864451 : Blo 1104625 1864451 := bstep (se 1 (by rfl) ⟨1398338, by rfl⟩ : syracuseStep 1864451 = 2796677) B2796677
theorem B1995587 : Blo 1104625 1995587 := bstep (se 1 (by rfl) ⟨1496690, by rfl⟩ : syracuseStep 1995587 = 2993381) B2993381
theorem B1864579 : Blo 1104625 1864579 := bstep (se 1 (by rfl) ⟨1398434, by rfl⟩ : syracuseStep 1864579 = 2796869) B2796869
theorem B2487185 : Blo 1104625 2487185 := bstep (se 2 (by rfl) ⟨932694, by rfl⟩ : syracuseStep 2487185 = 1865389) B1865389
theorem B2487203 : Blo 1104625 2487203 := bstep (se 1 (by rfl) ⟨1865402, by rfl⟩ : syracuseStep 2487203 = 3730805) B3730805
theorem B5600177 : Blo 1104625 5600177 := bstep (se 2 (by rfl) ⟨2100066, by rfl⟩ : syracuseStep 5600177 = 4200133) B4200133
theorem B1864721 : Blo 1104625 1864721 := bstep (se 2 (by rfl) ⟨699270, by rfl⟩ : syracuseStep 1864721 = 1398541) B1398541
theorem B1864849 : Blo 1104625 1864849 := bstep (se 2 (by rfl) ⟨699318, by rfl⟩ : syracuseStep 1864849 = 1398637) B1398637
theorem B2520227 : Blo 1104625 2520227 := bstep (se 1 (by rfl) ⟨1890170, by rfl⟩ : syracuseStep 2520227 = 3780341) B3780341
theorem B2487473 : Blo 1104625 2487473 := bstep (se 2 (by rfl) ⟨932802, by rfl⟩ : syracuseStep 2487473 = 1865605) B1865605
theorem B1864883 : Blo 1104625 1864883 := bstep (se 1 (by rfl) ⟨1398662, by rfl⟩ : syracuseStep 1864883 = 2797325) B2797325
theorem B2487491 : Blo 1104625 2487491 := bstep (se 1 (by rfl) ⟨1865618, by rfl⟩ : syracuseStep 2487491 = 3731237) B3731237
theorem B3994865 : Blo 1104625 3994865 := bstep (se 2 (by rfl) ⟨1498074, by rfl⟩ : syracuseStep 3994865 = 2996149) B2996149
theorem B3732749 : Blo 1104625 3732749 := bstep (se 3 (by rfl) ⟨699890, by rfl⟩ : syracuseStep 3732749 = 1399781) B1399781
theorem B1865011 : Blo 1104625 1865011 := bstep (se 1 (by rfl) ⟨1398758, by rfl⟩ : syracuseStep 1865011 = 2797517) B2797517
theorem B3732803 : Blo 1104625 3732803 := bstep (se 1 (by rfl) ⟨2799602, by rfl⟩ : syracuseStep 3732803 = 5599205) B5599205
theorem B1865153 : Blo 1104625 1865153 := bstep (se 2 (by rfl) ⟨699432, by rfl⟩ : syracuseStep 1865153 = 1398865) B1398865
theorem B2487761 : Blo 1104625 2487761 := bstep (se 2 (by rfl) ⟨932910, by rfl⟩ : syracuseStep 2487761 = 1865821) B1865821
theorem B2487779 : Blo 1104625 2487779 := bstep (se 1 (by rfl) ⟨1865834, by rfl⟩ : syracuseStep 2487779 = 3731669) B3731669
theorem B1865281 : Blo 1104625 1865281 := bstep (se 2 (by rfl) ⟨699480, by rfl⟩ : syracuseStep 1865281 = 1398961) B1398961
theorem B3733073 : Blo 1104625 3733073 := bstep (se 2 (by rfl) ⟨1399902, by rfl⟩ : syracuseStep 3733073 = 2799805) B2799805
theorem B1865315 : Blo 1104625 1865315 := bstep (se 1 (by rfl) ⟨1398986, by rfl⟩ : syracuseStep 1865315 = 2797973) B2797973
theorem B1242787 : Blo 1104625 1242787 := bstep (se 1 (by rfl) ⟨932090, by rfl⟩ : syracuseStep 1242787 = 1864181) B1864181
theorem B1865443 : Blo 1104625 1865443 := bstep (se 1 (by rfl) ⟨1399082, by rfl⟩ : syracuseStep 1865443 = 2798165) B2798165
theorem B2488049 : Blo 1104625 2488049 := bstep (se 2 (by rfl) ⟨933018, by rfl⟩ : syracuseStep 2488049 = 1866037) B1866037
theorem B2488067 : Blo 1104625 2488067 := bstep (se 1 (by rfl) ⟨1866050, by rfl⟩ : syracuseStep 2488067 = 3732101) B3732101
theorem B1242931 : Blo 1104625 1242931 := bstep (se 1 (by rfl) ⟨932198, by rfl⟩ : syracuseStep 1242931 = 1864397) B1864397
theorem B1865585 : Blo 1104625 1865585 := bstep (se 2 (by rfl) ⟨699594, by rfl⟩ : syracuseStep 1865585 = 1399189) B1399189
theorem B1243075 : Blo 1104625 1243075 := bstep (se 1 (by rfl) ⟨932306, by rfl⟩ : syracuseStep 1243075 = 1864613) B1864613
theorem B1865713 : Blo 1104625 1865713 := bstep (se 2 (by rfl) ⟨699642, by rfl⟩ : syracuseStep 1865713 = 1399285) B1399285
theorem B2488337 : Blo 1104625 2488337 := bstep (se 2 (by rfl) ⟨933126, by rfl⟩ : syracuseStep 2488337 = 1866253) B1866253
theorem B1865747 : Blo 1104625 1865747 := bstep (se 1 (by rfl) ⟨1399310, by rfl⟩ : syracuseStep 1865747 = 2798621) B2798621
theorem B2488355 : Blo 1104625 2488355 := bstep (se 1 (by rfl) ⟨1866266, by rfl⟩ : syracuseStep 2488355 = 3732533) B3732533
theorem B1243219 : Blo 1104625 1243219 := bstep (se 1 (by rfl) ⟨932414, by rfl⟩ : syracuseStep 1243219 = 1864829) B1864829
theorem B3733613 : Blo 1104625 3733613 := bstep (se 3 (by rfl) ⟨700052, by rfl⟩ : syracuseStep 3733613 = 1400105) B1400105
theorem B1865875 : Blo 1104625 1865875 := bstep (se 1 (by rfl) ⟨1399406, by rfl⟩ : syracuseStep 1865875 = 2798813) B2798813
theorem B3733667 : Blo 1104625 3733667 := bstep (se 1 (by rfl) ⟨2800250, by rfl⟩ : syracuseStep 3733667 = 5600501) B5600501
theorem B1243363 : Blo 1104625 1243363 := bstep (se 1 (by rfl) ⟨932522, by rfl⟩ : syracuseStep 1243363 = 1865045) B1865045
theorem B1866017 : Blo 1104625 1866017 := bstep (se 2 (by rfl) ⟨699756, by rfl⟩ : syracuseStep 1866017 = 1399513) B1399513
theorem B2488625 : Blo 1104625 2488625 := bstep (se 2 (by rfl) ⟨933234, by rfl⟩ : syracuseStep 2488625 = 1866469) B1866469
theorem B2488643 : Blo 1104625 2488643 := bstep (se 1 (by rfl) ⟨1866482, by rfl⟩ : syracuseStep 2488643 = 3732965) B3732965
theorem B5601635 : Blo 1104625 5601635 := bstep (se 1 (by rfl) ⟨4201226, by rfl⟩ : syracuseStep 5601635 = 8402453) B8402453
theorem B1243507 : Blo 1104625 1243507 := bstep (se 1 (by rfl) ⟨932630, by rfl⟩ : syracuseStep 1243507 = 1865261) B1865261
theorem B2128259 : Blo 1104625 2128259 := bstep (se 1 (by rfl) ⟨1596194, by rfl⟩ : syracuseStep 2128259 = 3192389) B3192389
theorem B1866145 : Blo 1104625 1866145 := bstep (se 2 (by rfl) ⟨699804, by rfl⟩ : syracuseStep 1866145 = 1399609) B1399609
theorem B3733937 : Blo 1104625 3733937 := bstep (se 2 (by rfl) ⟨1400226, by rfl⟩ : syracuseStep 3733937 = 2800453) B2800453
theorem B14186933 : Blo 1104625 14186933 := bstep (se 5 (by rfl) ⟨665012, by rfl⟩ : syracuseStep 14186933 = 1330025) B1330025
theorem B1866179 : Blo 1104625 1866179 := bstep (se 1 (by rfl) ⟨1399634, by rfl⟩ : syracuseStep 1866179 = 2799269) B2799269
theorem B1243651 : Blo 1104625 1243651 := bstep (se 1 (by rfl) ⟨932738, by rfl⟩ : syracuseStep 1243651 = 1865477) B1865477
theorem B1866307 : Blo 1104625 1866307 := bstep (se 1 (by rfl) ⟨1399730, by rfl⟩ : syracuseStep 1866307 = 2799461) B2799461
theorem B2488913 : Blo 1104625 2488913 := bstep (se 2 (by rfl) ⟨933342, by rfl⟩ : syracuseStep 2488913 = 1866685) B1866685
theorem B2488931 : Blo 1104625 2488931 := bstep (se 1 (by rfl) ⟨1866698, by rfl⟩ : syracuseStep 2488931 = 3733397) B3733397
theorem B1243795 : Blo 1104625 1243795 := bstep (se 1 (by rfl) ⟨932846, by rfl⟩ : syracuseStep 1243795 = 1865693) B1865693
theorem B1997489 : Blo 1104625 1997489 := bstep (se 2 (by rfl) ⟨749058, by rfl⟩ : syracuseStep 1997489 = 1498117) B1498117
theorem B1866449 : Blo 1104625 1866449 := bstep (se 2 (by rfl) ⟨699918, by rfl⟩ : syracuseStep 1866449 = 1399837) B1399837
theorem B1243939 : Blo 1104625 1243939 := bstep (se 1 (by rfl) ⟨932954, by rfl⟩ : syracuseStep 1243939 = 1865909) B1865909
theorem B1866577 : Blo 1104625 1866577 := bstep (se 2 (by rfl) ⟨699966, by rfl⟩ : syracuseStep 1866577 = 1399933) B1399933
theorem B2489201 : Blo 1104625 2489201 := bstep (se 2 (by rfl) ⟨933450, by rfl⟩ : syracuseStep 2489201 = 1866901) B1866901
theorem B1866611 : Blo 1104625 1866611 := bstep (se 1 (by rfl) ⟨1399958, by rfl⟩ : syracuseStep 1866611 = 2799917) B2799917
theorem B2489219 : Blo 1104625 2489219 := bstep (se 1 (by rfl) ⟨1866914, by rfl⟩ : syracuseStep 2489219 = 3733829) B3733829
theorem B1244083 : Blo 1104625 1244083 := bstep (se 1 (by rfl) ⟨933062, by rfl⟩ : syracuseStep 1244083 = 1866125) B1866125
theorem B3734477 : Blo 1104625 3734477 := bstep (se 3 (by rfl) ⟨700214, by rfl⟩ : syracuseStep 3734477 = 1400429) B1400429
theorem B2882531 : Blo 1104625 2882531 := bstep (se 1 (by rfl) ⟨2161898, by rfl⟩ : syracuseStep 2882531 = 4323797) B4323797
theorem B1866739 : Blo 1104625 1866739 := bstep (se 1 (by rfl) ⟨1400054, by rfl⟩ : syracuseStep 1866739 = 2800109) B2800109
theorem B3734531 : Blo 1104625 3734531 := bstep (se 1 (by rfl) ⟨2800898, by rfl⟩ : syracuseStep 3734531 = 5601797) B5601797
theorem B1244227 : Blo 1104625 1244227 := bstep (se 1 (by rfl) ⟨933170, by rfl⟩ : syracuseStep 1244227 = 1866341) B1866341
theorem B1866881 : Blo 1104625 1866881 := bstep (se 2 (by rfl) ⟨700080, by rfl⟩ : syracuseStep 1866881 = 1400161) B1400161
theorem B5602445 : Blo 1104625 5602445 := bstep (se 3 (by rfl) ⟨1050458, by rfl⟩ : syracuseStep 5602445 = 2100917) B2100917
theorem B2489489 : Blo 1104625 2489489 := bstep (se 2 (by rfl) ⟨933558, by rfl⟩ : syracuseStep 2489489 = 1867117) B1867117
theorem B2489507 : Blo 1104625 2489507 := bstep (se 1 (by rfl) ⟨1867130, by rfl⟩ : syracuseStep 2489507 = 3734261) B3734261
theorem B1244371 : Blo 1104625 1244371 := bstep (se 1 (by rfl) ⟨933278, by rfl⟩ : syracuseStep 1244371 = 1866557) B1866557
theorem B1867009 : Blo 1104625 1867009 := bstep (se 2 (by rfl) ⟨700128, by rfl⟩ : syracuseStep 1867009 = 1400257) B1400257
theorem B3734801 : Blo 1104625 3734801 := bstep (se 2 (by rfl) ⟨1400550, by rfl⟩ : syracuseStep 3734801 = 2801101) B2801101
theorem B1867043 : Blo 1104625 1867043 := bstep (se 1 (by rfl) ⟨1400282, by rfl⟩ : syracuseStep 1867043 = 2800565) B2800565
theorem B1244515 : Blo 1104625 1244515 := bstep (se 1 (by rfl) ⟨933386, by rfl⟩ : syracuseStep 1244515 = 1866773) B1866773
theorem B1867171 : Blo 1104625 1867171 := bstep (se 1 (by rfl) ⟨1400378, by rfl⟩ : syracuseStep 1867171 = 2800757) B2800757
theorem B2489777 : Blo 1104625 2489777 := bstep (se 2 (by rfl) ⟨933666, by rfl⟩ : syracuseStep 2489777 = 1867333) B1867333
theorem B2489795 : Blo 1104625 2489795 := bstep (se 1 (by rfl) ⟨1867346, by rfl⟩ : syracuseStep 2489795 = 3734693) B3734693
theorem B17006051 : Blo 1104625 17006051 := bstep (se 1 (by rfl) ⟨12754538, by rfl⟩ : syracuseStep 17006051 = 25509077) B25509077
theorem B1244659 : Blo 1104625 1244659 := bstep (se 1 (by rfl) ⟨933494, by rfl⟩ : syracuseStep 1244659 = 1866989) B1866989
theorem B1867313 : Blo 1104625 1867313 := bstep (se 2 (by rfl) ⟨700242, by rfl⟩ : syracuseStep 1867313 = 1400485) B1400485
theorem B1244803 : Blo 1104625 1244803 := bstep (se 1 (by rfl) ⟨933602, by rfl⟩ : syracuseStep 1244803 = 1867205) B1867205
theorem B1867441 : Blo 1104625 1867441 := bstep (se 2 (by rfl) ⟨700290, by rfl⟩ : syracuseStep 1867441 = 1400581) B1400581
theorem B2522819 : Blo 1104625 2522819 := bstep (se 1 (by rfl) ⟨1892114, by rfl⟩ : syracuseStep 2522819 = 3784229) B3784229
theorem B2490065 : Blo 1104625 2490065 := bstep (se 2 (by rfl) ⟨933774, by rfl⟩ : syracuseStep 2490065 = 1867549) B1867549
theorem B1867475 : Blo 1104625 1867475 := bstep (se 1 (by rfl) ⟨1400606, by rfl⟩ : syracuseStep 1867475 = 2801213) B2801213
theorem B2490083 : Blo 1104625 2490083 := bstep (se 1 (by rfl) ⟨1867562, by rfl⟩ : syracuseStep 2490083 = 3735125) B3735125
theorem B1244947 : Blo 1104625 1244947 := bstep (se 1 (by rfl) ⟨933710, by rfl⟩ : syracuseStep 1244947 = 1867421) B1867421
theorem B3735341 : Blo 1104625 3735341 := bstep (se 3 (by rfl) ⟨700376, by rfl⟩ : syracuseStep 3735341 = 1400753) B1400753
theorem B1867603 : Blo 1104625 1867603 := bstep (se 1 (by rfl) ⟨1400702, by rfl⟩ : syracuseStep 1867603 = 2801405) B2801405
theorem B5308259 : Blo 1104625 5308259 := bstep (se 1 (by rfl) ⟨3981194, by rfl⟩ : syracuseStep 5308259 = 7962389) B7962389
theorem B3735395 : Blo 1104625 3735395 := bstep (se 1 (by rfl) ⟨2801546, by rfl⟩ : syracuseStep 3735395 = 5603093) B5603093
theorem B3538829 : Blo 1104625 3538829 := bstep (se 3 (by rfl) ⟨663530, by rfl⟩ : syracuseStep 3538829 = 1327061) B1327061
theorem B1245091 : Blo 1104625 1245091 := bstep (se 1 (by rfl) ⟨933818, by rfl⟩ : syracuseStep 1245091 = 1867637) B1867637
theorem B1867745 : Blo 1104625 1867745 := bstep (se 2 (by rfl) ⟨700404, by rfl⟩ : syracuseStep 1867745 = 1400809) B1400809
theorem B2490353 : Blo 1104625 2490353 := bstep (se 2 (by rfl) ⟨933882, by rfl⟩ : syracuseStep 2490353 = 1867765) B1867765
theorem B1867799 : Blo 1104625 1867799 := bstep (se 1 (by rfl) ⟨1400849, by rfl⟩ : syracuseStep 1867799 = 2801699) B2801699
theorem B2097227 : Blo 1104625 2097227 := bstep (se 1 (by rfl) ⟨1572920, by rfl⟩ : syracuseStep 2097227 = 3145841) B3145841
theorem B2490443 : Blo 1104625 2490443 := bstep (se 1 (by rfl) ⟨1867832, by rfl⟩ : syracuseStep 2490443 = 3735665) B3735665
theorem B1245271 : Blo 1104625 1245271 := bstep (se 1 (by rfl) ⟨933953, by rfl⟩ : syracuseStep 1245271 = 1867907) B1867907
theorem B3145817 : Blo 1104625 3145817 := bstep (se 2 (by rfl) ⟨1179681, by rfl⟩ : syracuseStep 3145817 = 2359363) B2359363
theorem B2490497 : Blo 1104625 2490497 := bstep (se 2 (by rfl) ⟨933936, by rfl⟩ : syracuseStep 2490497 = 1867873) B1867873
theorem B1867927 : Blo 1104625 1867927 := bstep (se 1 (by rfl) ⟨1400945, by rfl⟩ : syracuseStep 1867927 = 2801891) B2801891
theorem B3735773 : Blo 1104625 3735773 := bstep (se 3 (by rfl) ⟨700457, by rfl⟩ : syracuseStep 3735773 = 1400915) B1400915
theorem B1179883 : Blo 1104625 1179883 := bstep (se 1 (by rfl) ⟨884912, by rfl⟩ : syracuseStep 1179883 = 1769825) B1769825
theorem B2097409 : Blo 1104625 2097409 := bstep (se 2 (by rfl) ⟨786528, by rfl⟩ : syracuseStep 2097409 = 1573057) B1573057
theorem B1245451 : Blo 1104625 1245451 := bstep (se 1 (by rfl) ⟨934088, by rfl⟩ : syracuseStep 1245451 = 1868177) B1868177
theorem B4194605 : Blo 1104625 4194605 := bstep (se 3 (by rfl) ⟨786488, by rfl⟩ : syracuseStep 4194605 = 1572977) B1572977
theorem B2490713 : Blo 1104625 2490713 := bstep (se 2 (by rfl) ⟨934017, by rfl⟩ : syracuseStep 2490713 = 1868035) B1868035
theorem B1245559 : Blo 1104625 1245559 := bstep (se 1 (by rfl) ⟨934169, by rfl⟩ : syracuseStep 1245559 = 1868339) B1868339
theorem B6291863 : Blo 1104625 6291863 := bstep (se 1 (by rfl) ⟨4718897, by rfl⟩ : syracuseStep 6291863 = 9437795) B9437795
theorem B4718999 : Blo 1104625 4718999 := bstep (se 1 (by rfl) ⟨3539249, by rfl⟩ : syracuseStep 4718999 = 7078499) B7078499
theorem B2359705 : Blo 1104625 2359705 := bstep (se 2 (by rfl) ⟨884889, by rfl⟩ : syracuseStep 2359705 = 1769779) B1769779
theorem B1573273 : Blo 1104625 1573273 := bstep (se 2 (by rfl) ⟨589977, by rfl⟩ : syracuseStep 1573273 = 1179955) B1179955
theorem B2490803 : Blo 1104625 2490803 := bstep (se 1 (by rfl) ⟨1868102, by rfl⟩ : syracuseStep 2490803 = 3736205) B3736205
theorem B5046731 : Blo 1104625 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B2490839 : Blo 1104625 2490839 := bstep (se 1 (by rfl) ⟨1868129, by rfl⟩ : syracuseStep 2490839 = 3736259) B3736259
theorem B1245739 : Blo 1104625 1245739 := bstep (se 1 (by rfl) ⟨934304, by rfl⟩ : syracuseStep 1245739 = 1868609) B1868609
theorem B2097751 : Blo 1104625 2097751 := bstep (se 1 (by rfl) ⟨1573313, by rfl⟩ : syracuseStep 2097751 = 3146627) B3146627
theorem B2491019 : Blo 1104625 2491019 := bstep (se 1 (by rfl) ⟨1868264, by rfl⟩ : syracuseStep 2491019 = 3736529) B3736529
theorem B1245847 : Blo 1104625 1245847 := bstep (se 1 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 1245847 = 1868771) B1868771
theorem B2491073 : Blo 1104625 2491073 := bstep (se 2 (by rfl) ⟨934152, by rfl⟩ : syracuseStep 2491073 = 1868305) B1868305
theorem B1868555 : Blo 1104625 1868555 := bstep (se 1 (by rfl) ⟨1401416, by rfl⟩ : syracuseStep 1868555 = 2802833) B2802833
theorem B2097971 : Blo 1104625 2097971 := bstep (se 1 (by rfl) ⟨1573478, by rfl⟩ : syracuseStep 2097971 = 3146957) B3146957
theorem B1246027 : Blo 1104625 1246027 := bstep (se 1 (by rfl) ⟨934520, by rfl⟩ : syracuseStep 1246027 = 1869041) B1869041
theorem B5604227 : Blo 1104625 5604227 := bstep (se 1 (by rfl) ⟨4203170, by rfl⟩ : syracuseStep 5604227 = 8406341) B8406341
theorem B1868683 : Blo 1104625 1868683 := bstep (se 1 (by rfl) ⟨1401512, by rfl⟩ : syracuseStep 1868683 = 2803025) B2803025
theorem B2491289 : Blo 1104625 2491289 := bstep (se 2 (by rfl) ⟨934233, by rfl⟩ : syracuseStep 2491289 = 1868467) B1868467
theorem B1246135 : Blo 1104625 1246135 := bstep (se 1 (by rfl) ⟨934601, by rfl⟩ : syracuseStep 1246135 = 1869203) B1869203
theorem B2491379 : Blo 1104625 2491379 := bstep (se 1 (by rfl) ⟨1868534, by rfl⟩ : syracuseStep 2491379 = 3737069) B3737069
theorem B2098199 : Blo 1104625 2098199 := bstep (se 1 (by rfl) ⟨1573649, by rfl⟩ : syracuseStep 2098199 = 3147299) B3147299
theorem B2491415 : Blo 1104625 2491415 := bstep (se 1 (by rfl) ⟨1868561, by rfl⟩ : syracuseStep 2491415 = 3737123) B3737123
theorem B1868825 : Blo 1104625 1868825 := bstep (se 2 (by rfl) ⟨700809, by rfl⟩ : syracuseStep 1868825 = 1401619) B1401619
theorem B4719667 : Blo 1104625 4719667 := bstep (se 1 (by rfl) ⟨3539750, by rfl⟩ : syracuseStep 4719667 = 7079501) B7079501
theorem B3540019 : Blo 1104625 3540019 := bstep (se 1 (by rfl) ⟨2655014, by rfl⟩ : syracuseStep 3540019 = 5310029) B5310029
theorem B1246315 : Blo 1104625 1246315 := bstep (se 1 (by rfl) ⟨934736, by rfl⟩ : syracuseStep 1246315 = 1869473) B1869473
theorem B1868953 : Blo 1104625 1868953 := bstep (se 2 (by rfl) ⟨700857, by rfl⟩ : syracuseStep 1868953 = 1401715) B1401715
theorem B10093747 : Blo 1104625 10093747 := bstep (se 1 (by rfl) ⟨7570310, by rfl⟩ : syracuseStep 10093747 = 15140621) B15140621
theorem B3540161 : Blo 1104625 3540161 := bstep (se 2 (by rfl) ⟨1327560, by rfl⟩ : syracuseStep 3540161 = 2655121) B2655121
theorem B2491595 : Blo 1104625 2491595 := bstep (se 1 (by rfl) ⟨1868696, by rfl⟩ : syracuseStep 2491595 = 3737393) B3737393
theorem B1246423 : Blo 1104625 1246423 := bstep (se 1 (by rfl) ⟨934817, by rfl⟩ : syracuseStep 1246423 = 1869635) B1869635
theorem B2491649 : Blo 1104625 2491649 := bstep (se 2 (by rfl) ⟨934368, by rfl⟩ : syracuseStep 2491649 = 1868737) B1868737
theorem B2098457 : Blo 1104625 2098457 := bstep (se 2 (by rfl) ⟨786921, by rfl⟩ : syracuseStep 2098457 = 1573843) B1573843
theorem B31950125 : Blo 1104625 31950125 := bstep (se 3 (by rfl) ⟨5990648, by rfl⟩ : syracuseStep 31950125 = 11981297) B11981297
theorem B3540275 : Blo 1104625 3540275 := bstep (se 1 (by rfl) ⟨2655206, by rfl⟩ : syracuseStep 3540275 = 5310413) B5310413
theorem B3147083 : Blo 1104625 3147083 := bstep (se 1 (by rfl) ⟨2360312, by rfl⟩ : syracuseStep 3147083 = 4720625) B4720625
theorem B4261195 : Blo 1104625 4261195 := bstep (se 1 (by rfl) ⟨3195896, by rfl⟩ : syracuseStep 4261195 = 6391793) B6391793
theorem B3736907 : Blo 1104625 3736907 := bstep (se 1 (by rfl) ⟨2802680, by rfl⟩ : syracuseStep 3736907 = 5605361) B5605361
theorem B1246603 : Blo 1104625 1246603 := bstep (se 1 (by rfl) ⟨934952, by rfl⟩ : syracuseStep 1246603 = 1869905) B1869905
theorem B55248277 : Blo 1104625 55248277 := bstep (se 6 (by rfl) ⟨1294881, by rfl⟩ : syracuseStep 55248277 = 2589763) B2589763
theorem B2491865 : Blo 1104625 2491865 := bstep (se 2 (by rfl) ⟨934449, by rfl⟩ : syracuseStep 2491865 = 1868899) B1868899
theorem B1246711 : Blo 1104625 1246711 := bstep (se 1 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 1246711 = 1870067) B1870067
theorem B5113367 : Blo 1104625 5113367 := bstep (se 1 (by rfl) ⟨3835025, by rfl⟩ : syracuseStep 5113367 = 7670051) B7670051
theorem B2491955 : Blo 1104625 2491955 := bstep (se 1 (by rfl) ⟨1868966, by rfl⟩ : syracuseStep 2491955 = 3737933) B3737933
theorem B2491991 : Blo 1104625 2491991 := bstep (se 1 (by rfl) ⟨1868993, by rfl⟩ : syracuseStep 2491991 = 3737987) B3737987
theorem B3737177 : Blo 1104625 3737177 := bstep (se 2 (by rfl) ⟨1401441, by rfl⟩ : syracuseStep 3737177 = 2802883) B2802883
theorem B7079525 : Blo 1104625 7079525 := bstep (se 4 (by rfl) ⟨663705, by rfl⟩ : syracuseStep 7079525 = 1327411) B1327411
theorem B1246891 : Blo 1104625 1246891 := bstep (se 1 (by rfl) ⟨935168, by rfl⟩ : syracuseStep 1246891 = 1870337) B1870337
theorem B2098867 : Blo 1104625 2098867 := bstep (se 1 (by rfl) ⟨1574150, by rfl⟩ : syracuseStep 2098867 = 3148301) B3148301
theorem B4196033 : Blo 1104625 4196033 := bstep (se 2 (by rfl) ⟨1573512, by rfl⟩ : syracuseStep 4196033 = 3147025) B3147025
theorem B2655937 : Blo 1104625 2655937 := bstep (se 2 (by rfl) ⟨995976, by rfl⟩ : syracuseStep 2655937 = 1991953) B1991953
theorem B1869527 : Blo 1104625 1869527 := bstep (se 1 (by rfl) ⟨1402145, by rfl⟩ : syracuseStep 1869527 = 2804291) B2804291
theorem B2361089 : Blo 1104625 2361089 := bstep (se 2 (by rfl) ⟨885408, by rfl⟩ : syracuseStep 2361089 = 1770817) B1770817
theorem B2492171 : Blo 1104625 2492171 := bstep (se 1 (by rfl) ⟨1869128, by rfl⟩ : syracuseStep 2492171 = 3738257) B3738257
theorem B1246999 : Blo 1104625 1246999 := bstep (se 1 (by rfl) ⟨935249, by rfl⟩ : syracuseStep 1246999 = 1870499) B1870499
theorem B2492225 : Blo 1104625 2492225 := bstep (se 2 (by rfl) ⟨934584, by rfl⟩ : syracuseStep 2492225 = 1869169) B1869169
theorem B1574731 : Blo 1104625 1574731 := bstep (se 1 (by rfl) ⟨1181048, by rfl⟩ : syracuseStep 1574731 = 2362097) B2362097
theorem B1574743 : Blo 1104625 1574743 := bstep (se 1 (by rfl) ⟨1181057, by rfl⟩ : syracuseStep 1574743 = 2362115) B2362115
theorem B1869655 : Blo 1104625 1869655 := bstep (se 1 (by rfl) ⟨1402241, by rfl⟩ : syracuseStep 1869655 = 2804483) B2804483
theorem B1247179 : Blo 1104625 1247179 := bstep (se 1 (by rfl) ⟨935384, by rfl⟩ : syracuseStep 1247179 = 1870769) B1870769
theorem B6064145 : Blo 1104625 6064145 := bstep (se 2 (by rfl) ⟨2274054, by rfl⟩ : syracuseStep 6064145 = 4548109) B4548109
theorem B2492441 : Blo 1104625 2492441 := bstep (se 2 (by rfl) ⟨934665, by rfl⟩ : syracuseStep 2492441 = 1869331) B1869331
theorem B2492531 : Blo 1104625 2492531 := bstep (se 1 (by rfl) ⟨1869398, by rfl⟩ : syracuseStep 2492531 = 3738797) B3738797
theorem B2492567 : Blo 1104625 2492567 := bstep (se 1 (by rfl) ⟨1869425, by rfl⟩ : syracuseStep 2492567 = 3738851) B3738851
theorem B2099353 : Blo 1104625 2099353 := bstep (se 2 (by rfl) ⟨787257, by rfl⟩ : syracuseStep 2099353 = 1574515) B1574515
theorem B1181899 : Blo 1104625 1181899 := bstep (se 1 (by rfl) ⟨886424, by rfl⟩ : syracuseStep 1181899 = 1772849) B1772849
theorem B2361611 : Blo 1104625 2361611 := bstep (se 1 (by rfl) ⟨1771208, by rfl⟩ : syracuseStep 2361611 = 3542417) B3542417
theorem B4720913 : Blo 1104625 4720913 := bstep (se 2 (by rfl) ⟨1770342, by rfl⟩ : syracuseStep 4720913 = 3540685) B3540685
theorem B3737879 : Blo 1104625 3737879 := bstep (se 1 (by rfl) ⟨2803409, by rfl⟩ : syracuseStep 3737879 = 5606819) B5606819
theorem B2492747 : Blo 1104625 2492747 := bstep (se 1 (by rfl) ⟨1869560, by rfl⟩ : syracuseStep 2492747 = 3739121) B3739121
theorem B2525555 : Blo 1104625 2525555 := bstep (se 1 (by rfl) ⟨1894166, by rfl⟩ : syracuseStep 2525555 = 3788333) B3788333
theorem B2492801 : Blo 1104625 2492801 := bstep (se 2 (by rfl) ⟨934800, by rfl⟩ : syracuseStep 2492801 = 1869601) B1869601
theorem B1870283 : Blo 1104625 1870283 := bstep (se 1 (by rfl) ⟨1402712, by rfl⟩ : syracuseStep 1870283 = 2805425) B2805425
theorem B10226137 : Blo 1104625 10226137 := bstep (se 2 (by rfl) ⟨3834801, by rfl⟩ : syracuseStep 10226137 = 7669603) B7669603
theorem B1870411 : Blo 1104625 1870411 := bstep (se 1 (by rfl) ⟨1402808, by rfl⟩ : syracuseStep 1870411 = 2805617) B2805617
theorem B2493017 : Blo 1104625 2493017 := bstep (se 2 (by rfl) ⟨934881, by rfl⟩ : syracuseStep 2493017 = 1869763) B1869763
theorem B2493107 : Blo 1104625 2493107 := bstep (se 1 (by rfl) ⟨1869830, by rfl⟩ : syracuseStep 2493107 = 3739661) B3739661
theorem B2099915 : Blo 1104625 2099915 := bstep (se 1 (by rfl) ⟨1574936, by rfl⟩ : syracuseStep 2099915 = 3149873) B3149873
theorem B2493143 : Blo 1104625 2493143 := bstep (se 1 (by rfl) ⟨1869857, by rfl⟩ : syracuseStep 2493143 = 3739715) B3739715
theorem B1870553 : Blo 1104625 1870553 := bstep (se 2 (by rfl) ⟨701457, by rfl⟩ : syracuseStep 1870553 = 1402915) B1402915
theorem B3738419 : Blo 1104625 3738419 := bstep (se 1 (by rfl) ⟨2803814, by rfl⟩ : syracuseStep 3738419 = 5607629) B5607629
theorem B40897345 : Blo 1104625 40897345 := bstep (se 2 (by rfl) ⟨15336504, by rfl⟩ : syracuseStep 40897345 = 30673009) B30673009
theorem B6294347 : Blo 1104625 6294347 := bstep (se 1 (by rfl) ⟨4720760, by rfl⟩ : syracuseStep 6294347 = 9441521) B9441521
theorem B1870681 : Blo 1104625 1870681 := bstep (se 2 (by rfl) ⟨701505, by rfl⟩ : syracuseStep 1870681 = 1403011) B1403011
theorem B2100097 : Blo 1104625 2100097 := bstep (se 2 (by rfl) ⟨787536, by rfl⟩ : syracuseStep 2100097 = 1575073) B1575073
theorem B2493323 : Blo 1104625 2493323 := bstep (se 1 (by rfl) ⟨1869992, by rfl⟩ : syracuseStep 2493323 = 3739985) B3739985
theorem B2493377 : Blo 1104625 2493377 := bstep (se 2 (by rfl) ⟨935016, by rfl⟩ : syracuseStep 2493377 = 1870033) B1870033
theorem B1281079 : Blo 1104625 1281079 := bstep (se 1 (by rfl) ⟨960809, by rfl⟩ : syracuseStep 1281079 = 1921619) B1921619
theorem B3738689 : Blo 1104625 3738689 := bstep (se 2 (by rfl) ⟨1402008, by rfl⟩ : syracuseStep 3738689 = 2804017) B2804017
theorem B4197521 : Blo 1104625 4197521 := bstep (se 2 (by rfl) ⟨1574070, by rfl⟩ : syracuseStep 4197521 = 3148141) B3148141
theorem B1772695 : Blo 1104625 1772695 := bstep (se 1 (by rfl) ⟨1329521, by rfl⟩ : syracuseStep 1772695 = 2659043) B2659043
theorem B2493593 : Blo 1104625 2493593 := bstep (se 2 (by rfl) ⟨935097, by rfl⟩ : syracuseStep 2493593 = 1870195) B1870195
theorem B7179443 : Blo 1104625 7179443 := bstep (se 1 (by rfl) ⟨5384582, by rfl⟩ : syracuseStep 7179443 = 10769165) B10769165
theorem B2493683 : Blo 1104625 2493683 := bstep (se 1 (by rfl) ⟨1870262, by rfl⟩ : syracuseStep 2493683 = 3740525) B3740525
theorem B2493719 : Blo 1104625 2493719 := bstep (se 1 (by rfl) ⟨1870289, by rfl⟩ : syracuseStep 2493719 = 3740579) B3740579
theorem B8523073 : Blo 1104625 8523073 := bstep (se 2 (by rfl) ⟨3196152, by rfl⟩ : syracuseStep 8523073 = 6392305) B6392305
theorem B4787545 : Blo 1104625 4787545 := bstep (se 2 (by rfl) ⟨1795329, by rfl⟩ : syracuseStep 4787545 = 3590659) B3590659
theorem B2493899 : Blo 1104625 2493899 := bstep (se 1 (by rfl) ⟨1870424, by rfl⟩ : syracuseStep 2493899 = 3740849) B3740849
theorem B2362841 : Blo 1104625 2362841 := bstep (se 2 (by rfl) ⟨886065, by rfl⟩ : syracuseStep 2362841 = 1772131) B1772131
theorem B2493953 : Blo 1104625 2493953 := bstep (se 2 (by rfl) ⟨935232, by rfl⟩ : syracuseStep 2493953 = 1870465) B1870465
theorem B1150507 : Blo 1104625 1150507 := bstep (se 1 (by rfl) ⟨862880, by rfl⟩ : syracuseStep 1150507 = 1725761) B1725761
theorem B2100811 : Blo 1104625 2100811 := bstep (se 1 (by rfl) ⟨1575608, by rfl⟩ : syracuseStep 2100811 = 3151217) B3151217
theorem B4197977 : Blo 1104625 4197977 := bstep (se 2 (by rfl) ⟨1574241, by rfl⟩ : syracuseStep 4197977 = 3148483) B3148483
theorem B3739229 : Blo 1104625 3739229 := bstep (se 3 (by rfl) ⟨701105, by rfl⟩ : syracuseStep 3739229 = 1402211) B1402211
theorem B17927831 : Blo 1104625 17927831 := bstep (se 1 (by rfl) ⟨13445873, by rfl⟩ : syracuseStep 17927831 = 26891747) B26891747
theorem B2100887 : Blo 1104625 2100887 := bstep (se 1 (by rfl) ⟨1575665, by rfl⟩ : syracuseStep 2100887 = 3151331) B3151331
theorem B1183415 : Blo 1104625 1183415 := bstep (se 1 (by rfl) ⟨887561, by rfl⟩ : syracuseStep 1183415 = 1775123) B1775123
theorem B2494169 : Blo 1104625 2494169 := bstep (se 2 (by rfl) ⟨935313, by rfl⟩ : syracuseStep 2494169 = 1870627) B1870627
theorem B2658071 : Blo 1104625 2658071 := bstep (se 1 (by rfl) ⟨1993553, by rfl⟩ : syracuseStep 2658071 = 3987107) B3987107
theorem B4198189 : Blo 1104625 4198189 := bstep (se 3 (by rfl) ⟨787160, by rfl⟩ : syracuseStep 4198189 = 1574321) B1574321
theorem B2494259 : Blo 1104625 2494259 := bstep (se 1 (by rfl) ⟨1870694, by rfl⟩ : syracuseStep 2494259 = 3741389) B3741389
theorem B2494295 : Blo 1104625 2494295 := bstep (se 1 (by rfl) ⟨1870721, by rfl⟩ : syracuseStep 2494295 = 3741443) B3741443
theorem B1576793 : Blo 1104625 1576793 := bstep (se 2 (by rfl) ⟨591297, by rfl⟩ : syracuseStep 1576793 = 1182595) B1182595
theorem B2363251 : Blo 1104625 2363251 := bstep (se 1 (by rfl) ⟨1772438, by rfl⟩ : syracuseStep 2363251 = 3544877) B3544877
theorem B1773515 : Blo 1104625 1773515 := bstep (se 1 (by rfl) ⟨1330136, by rfl⟩ : syracuseStep 1773515 = 2660273) B2660273
theorem B2658379 : Blo 1104625 2658379 := bstep (se 1 (by rfl) ⟨1993784, by rfl⟩ : syracuseStep 2658379 = 3987569) B3987569
theorem B4198493 : Blo 1104625 4198493 := bstep (se 3 (by rfl) ⟨787217, by rfl⟩ : syracuseStep 4198493 = 1574435) B1574435
theorem B4788497 : Blo 1104625 4788497 := bstep (se 2 (by rfl) ⟨1795686, by rfl⟩ : syracuseStep 4788497 = 3591373) B3591373
theorem B8982829 : Blo 1104625 8982829 := bstep (se 3 (by rfl) ⟨1684280, by rfl⟩ : syracuseStep 8982829 = 3368561) B3368561
theorem B68227373 : Blo 1104625 68227373 := bstep (se 3 (by rfl) ⟨12792632, by rfl⟩ : syracuseStep 68227373 = 25585265) B25585265
theorem B2101555 : Blo 1104625 2101555 := bstep (se 1 (by rfl) ⟨1576166, by rfl⟩ : syracuseStep 2101555 = 3152333) B3152333
theorem B2363737 : Blo 1104625 2363737 := bstep (se 2 (by rfl) ⟨886401, by rfl⟩ : syracuseStep 2363737 = 1772803) B1772803
theorem B1577431 : Blo 1104625 1577431 := bstep (se 1 (by rfl) ⟨1183073, by rfl⟩ : syracuseStep 1577431 = 2366147) B2366147
theorem B5607953 : Blo 1104625 5607953 := bstep (se 2 (by rfl) ⟨2102982, by rfl⟩ : syracuseStep 5607953 = 4205965) B4205965
theorem B2101783 : Blo 1104625 2101783 := bstep (se 1 (by rfl) ⟨1576337, by rfl⟩ : syracuseStep 2101783 = 3152675) B3152675
theorem B2101889 : Blo 1104625 2101889 := bstep (se 2 (by rfl) ⟨788208, by rfl⟩ : syracuseStep 2101889 = 1576417) B1576417
theorem B4723373 : Blo 1104625 4723373 := bstep (se 3 (by rfl) ⟨885632, by rfl⟩ : syracuseStep 4723373 = 1771265) B1771265
theorem B5608115 : Blo 1104625 5608115 := bstep (se 1 (by rfl) ⟨4206086, by rfl⟩ : syracuseStep 5608115 = 8412173) B8412173
theorem B3740363 : Blo 1104625 3740363 := bstep (se 1 (by rfl) ⟨2805272, by rfl⟩ : syracuseStep 3740363 = 5610545) B5610545
theorem B2102041 : Blo 1104625 2102041 := bstep (se 2 (by rfl) ⟨788265, by rfl⟩ : syracuseStep 2102041 = 1576531) B1576531
theorem B1774489 : Blo 1104625 1774489 := bstep (se 2 (by rfl) ⟨665433, by rfl⟩ : syracuseStep 1774489 = 1330867) B1330867
theorem B3740633 : Blo 1104625 3740633 := bstep (se 2 (by rfl) ⟨1402737, by rfl⟩ : syracuseStep 3740633 = 2805475) B2805475
theorem B2364481 : Blo 1104625 2364481 := bstep (se 2 (by rfl) ⟨886680, by rfl⟩ : syracuseStep 2364481 = 1773361) B1773361
theorem B4789469 : Blo 1104625 4789469 := bstep (se 3 (by rfl) ⟨898025, by rfl⟩ : syracuseStep 4789469 = 1796051) B1796051
theorem B1578251 : Blo 1104625 1578251 := bstep (se 1 (by rfl) ⟨1183688, by rfl⟩ : syracuseStep 1578251 = 2367377) B2367377
theorem B4724057 : Blo 1104625 4724057 := bstep (se 2 (by rfl) ⟨1771521, by rfl⟩ : syracuseStep 4724057 = 3543043) B3543043
theorem B7968131 : Blo 1104625 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B6395267 : Blo 1104625 6395267 := bstep (se 1 (by rfl) ⟨4796450, by rfl⟩ : syracuseStep 6395267 = 9592901) B9592901
theorem B6297011 : Blo 1104625 6297011 := bstep (se 1 (by rfl) ⟨4722758, by rfl⟩ : syracuseStep 6297011 = 9445517) B9445517
theorem B3741335 : Blo 1104625 3741335 := bstep (se 1 (by rfl) ⟨2806001, by rfl⟩ : syracuseStep 3741335 = 5612003) B5612003
theorem B2987713 : Blo 1104625 2987713 := bstep (se 2 (by rfl) ⟨1120392, by rfl⟩ : syracuseStep 2987713 = 2240785) B2240785
theorem B20158307 : Blo 1104625 20158307 := bstep (se 1 (by rfl) ⟨15118730, by rfl⟩ : syracuseStep 20158307 = 30237461) B30237461
theorem B2365463 : Blo 1104625 2365463 := bstep (se 1 (by rfl) ⟨1774097, by rfl⟩ : syracuseStep 2365463 = 3548195) B3548195
theorem B14194723 : Blo 1104625 14194723 := bstep (se 1 (by rfl) ⟨10646042, by rfl⟩ : syracuseStep 14194723 = 21292085) B21292085
theorem B2103347 : Blo 1104625 2103347 := bstep (se 1 (by rfl) ⟨1577510, by rfl⟩ : syracuseStep 2103347 = 3155021) B3155021
theorem B8100017 : Blo 1104625 8100017 := bstep (se 2 (by rfl) ⟨3037506, by rfl⟩ : syracuseStep 8100017 = 6075013) B6075013
theorem B2660531 : Blo 1104625 2660531 := bstep (se 1 (by rfl) ⟨1995398, by rfl⟩ : syracuseStep 2660531 = 3990797) B3990797
theorem B2103499 : Blo 1104625 2103499 := bstep (se 1 (by rfl) ⟨1577624, by rfl⟩ : syracuseStep 2103499 = 3155249) B3155249
theorem B2103833 : Blo 1104625 2103833 := bstep (se 2 (by rfl) ⟨788937, by rfl⟩ : syracuseStep 2103833 = 1577875) B1577875
theorem B4266541 : Blo 1104625 4266541 := bstep (se 3 (by rfl) ⟨799976, by rfl⟩ : syracuseStep 4266541 = 1599953) B1599953
theorem B4725323 : Blo 1104625 4725323 := bstep (se 1 (by rfl) ⟨3543992, by rfl⟩ : syracuseStep 4725323 = 7087985) B7087985
theorem B3152459 : Blo 1104625 3152459 := bstep (se 1 (by rfl) ⟨2364344, by rfl⟩ : syracuseStep 3152459 = 4728689) B4728689
theorem B2366027 : Blo 1104625 2366027 := bstep (se 1 (by rfl) ⟨1774520, by rfl⟩ : syracuseStep 2366027 = 3549041) B3549041
theorem B5610059 : Blo 1104625 5610059 := bstep (se 1 (by rfl) ⟨4207544, by rfl⟩ : syracuseStep 5610059 = 8415089) B8415089
theorem B4201091 : Blo 1104625 4201091 := bstep (se 1 (by rfl) ⟨3150818, by rfl⟩ : syracuseStep 4201091 = 6301637) B6301637
theorem B4201105 : Blo 1104625 4201105 := bstep (se 2 (by rfl) ⟨1575414, by rfl⟩ : syracuseStep 4201105 = 3150829) B3150829
theorem B12589829 : Blo 1104625 12589829 := bstep (se 4 (by rfl) ⟨1180296, by rfl⟩ : syracuseStep 12589829 = 2360593) B2360593
theorem B6298469 : Blo 1104625 6298469 := bstep (se 4 (by rfl) ⟨590481, by rfl⟩ : syracuseStep 6298469 = 1180963) B1180963
theorem B4725697 : Blo 1104625 4725697 := bstep (se 2 (by rfl) ⟨1772136, by rfl⟩ : syracuseStep 4725697 = 3544273) B3544273
theorem B4201409 : Blo 1104625 4201409 := bstep (se 2 (by rfl) ⟨1575528, by rfl⟩ : syracuseStep 4201409 = 3151057) B3151057
theorem B3152857 : Blo 1104625 3152857 := bstep (se 2 (by rfl) ⟨1182321, by rfl⟩ : syracuseStep 3152857 = 2364643) B2364643
theorem B2366489 : Blo 1104625 2366489 := bstep (se 2 (by rfl) ⟨887433, by rfl⟩ : syracuseStep 2366489 = 1774867) B1774867
theorem B2104471 : Blo 1104625 2104471 := bstep (se 1 (by rfl) ⟨1578353, by rfl⟩ : syracuseStep 2104471 = 3156707) B3156707
theorem B4726039 : Blo 1104625 4726039 := bstep (se 1 (by rfl) ⟨3544529, by rfl⟩ : syracuseStep 4726039 = 7089059) B7089059
theorem B2694551 : Blo 1104625 2694551 := bstep (se 1 (by rfl) ⟨2020913, by rfl⟩ : syracuseStep 2694551 = 4041827) B4041827
theorem B1121771 : Blo 1104625 1121771 := bstep (se 1 (by rfl) ⟨841328, by rfl⟩ : syracuseStep 1121771 = 1682657) B1682657
theorem B6299153 : Blo 1104625 6299153 := bstep (se 2 (by rfl) ⟨2362182, by rfl⟩ : syracuseStep 6299153 = 4724365) B4724365
theorem B4202077 : Blo 1104625 4202077 := bstep (se 3 (by rfl) ⟨787889, by rfl⟩ : syracuseStep 4202077 = 1575779) B1575779
theorem B10362955 : Blo 1104625 10362955 := bstep (se 1 (by rfl) ⟨7772216, by rfl⟩ : syracuseStep 10362955 = 15544433) B15544433
theorem B3154099 : Blo 1104625 3154099 := bstep (se 1 (by rfl) ⟨2365574, by rfl⟩ : syracuseStep 3154099 = 4731149) B4731149
theorem B2367667 : Blo 1104625 2367667 := bstep (se 1 (by rfl) ⟨1775750, by rfl⟩ : syracuseStep 2367667 = 3551501) B3551501
theorem B5611841 : Blo 1104625 5611841 := bstep (se 2 (by rfl) ⟨2104440, by rfl⟩ : syracuseStep 5611841 = 4208881) B4208881
theorem B21242573 : Blo 1104625 21242573 := bstep (se 3 (by rfl) ⟨3982982, by rfl⟩ : syracuseStep 21242573 = 7965965) B7965965
theorem B1680151 : Blo 1104625 1680151 := bstep (se 1 (by rfl) ⟨1260113, by rfl⟩ : syracuseStep 1680151 = 2520227) B2520227
theorem B2663243 : Blo 1104625 2663243 := bstep (se 1 (by rfl) ⟨1997432, by rfl⟩ : syracuseStep 2663243 = 3994865) B3994865
theorem B4203353 : Blo 1104625 4203353 := bstep (se 2 (by rfl) ⟨1576257, by rfl⟩ : syracuseStep 4203353 = 3152515) B3152515
theorem B9577547 : Blo 1104625 9577547 := bstep (se 1 (by rfl) ⟨7183160, by rfl⟩ : syracuseStep 9577547 = 14366321) B14366321
theorem B5547565 : Blo 1104625 5547565 := bstep (se 3 (by rfl) ⟨1040168, by rfl⟩ : syracuseStep 5547565 = 2080337) B2080337
theorem B1418839 : Blo 1104625 1418839 := bstep (se 1 (by rfl) ⟨1064129, by rfl⟩ : syracuseStep 1418839 = 2128259) B2128259
theorem B5318237 : Blo 1104625 5318237 := bstep (se 3 (by rfl) ⟨997169, by rfl⟩ : syracuseStep 5318237 = 1994339) B1994339
theorem B35923661 : Blo 1104625 35923661 := bstep (se 3 (by rfl) ⟨6735686, by rfl⟩ : syracuseStep 35923661 = 13471373) B13471373
theorem B10102801 : Blo 1104625 10102801 := bstep (se 2 (by rfl) ⟨3788550, by rfl⟩ : syracuseStep 10102801 = 7577101) B7577101
theorem B3549491 : Blo 1104625 3549491 := bstep (se 1 (by rfl) ⟨2662118, by rfl⟩ : syracuseStep 3549491 = 5324237) B5324237
theorem B4204979 : Blo 1104625 4204979 := bstep (se 1 (by rfl) ⟨3153734, by rfl⟩ : syracuseStep 4204979 = 6307469) B6307469
theorem B4204993 : Blo 1104625 4204993 := bstep (se 2 (by rfl) ⟨1576872, by rfl⟩ : syracuseStep 4204993 = 3153745) B3153745
theorem B1681879 : Blo 1104625 1681879 := bstep (se 1 (by rfl) ⟨1261409, by rfl⟩ : syracuseStep 1681879 = 2522819) B2522819
theorem B8399537 : Blo 1104625 8399537 := bstep (se 2 (by rfl) ⟨3149826, by rfl⟩ : syracuseStep 8399537 = 6299653) B6299653
theorem B6302387 : Blo 1104625 6302387 := bstep (se 1 (by rfl) ⟨4726790, by rfl⟩ : syracuseStep 6302387 = 9453581) B9453581
theorem B2796353 : Blo 1104625 2796353 := bstep (se 2 (by rfl) ⟨1048632, by rfl⟩ : syracuseStep 2796353 = 2097265) B2097265
theorem B8203187 : Blo 1104625 8203187 := bstep (se 1 (by rfl) ⟨6152390, by rfl⟩ : syracuseStep 8203187 = 12304781) B12304781
theorem B3550169 : Blo 1104625 3550169 := bstep (se 2 (by rfl) ⟨1331313, by rfl⟩ : syracuseStep 3550169 = 2662627) B2662627
theorem B7973923 : Blo 1104625 7973923 := bstep (se 1 (by rfl) ⟨5980442, by rfl⟩ : syracuseStep 7973923 = 11960885) B11960885
theorem B8400023 : Blo 1104625 8400023 := bstep (se 1 (by rfl) ⟨6300017, by rfl⟩ : syracuseStep 8400023 = 12600035) B12600035
theorem B2796889 : Blo 1104625 2796889 := bstep (se 2 (by rfl) ⟨1048833, by rfl⟩ : syracuseStep 2796889 = 2097667) B2097667
theorem B1682839 : Blo 1104625 1682839 := bstep (se 1 (by rfl) ⟨1262129, by rfl⟩ : syracuseStep 1682839 = 2524259) B2524259
theorem B1420747 : Blo 1104625 1420747 := bstep (se 1 (by rfl) ⟨1065560, by rfl⟩ : syracuseStep 1420747 = 2131121) B2131121
theorem B4730413 : Blo 1104625 4730413 := bstep (se 3 (by rfl) ⟨886952, by rfl⟩ : syracuseStep 4730413 = 1773905) B1773905
theorem B2240153 : Blo 1104625 2240153 := bstep (se 2 (by rfl) ⟨840057, by rfl⟩ : syracuseStep 2240153 = 1680115) B1680115
theorem B2994137 : Blo 1104625 2994137 := bstep (se 2 (by rfl) ⟨1122801, by rfl⟩ : syracuseStep 2994137 = 2245603) B2245603
theorem B6303845 : Blo 1104625 6303845 := bstep (se 4 (by rfl) ⟨590985, by rfl⟩ : syracuseStep 6303845 = 1181971) B1181971
theorem B19181699 : Blo 1104625 19181699 := bstep (se 1 (by rfl) ⟨14386274, by rfl⟩ : syracuseStep 19181699 = 28772549) B28772549
theorem B2240779 : Blo 1104625 2240779 := bstep (se 1 (by rfl) ⟨1680584, by rfl⟩ : syracuseStep 2240779 = 3361169) B3361169
theorem B4206923 : Blo 1104625 4206923 := bstep (se 1 (by rfl) ⟨3155192, by rfl⟩ : syracuseStep 4206923 = 6310385) B6310385
theorem B4206937 : Blo 1104625 4206937 := bstep (se 2 (by rfl) ⟨1577601, by rfl⟩ : syracuseStep 4206937 = 3155203) B3155203
theorem B2798003 : Blo 1104625 2798003 := bstep (se 1 (by rfl) ⟨2098502, by rfl⟩ : syracuseStep 2798003 = 4197005) B4197005
theorem B7090649 : Blo 1104625 7090649 := bstep (se 2 (by rfl) ⟨2658993, by rfl⟩ : syracuseStep 7090649 = 5317987) B5317987
theorem B5321177 : Blo 1104625 5321177 := bstep (se 2 (by rfl) ⟨1995441, by rfl⟩ : syracuseStep 5321177 = 3990883) B3990883
theorem B6304301 : Blo 1104625 6304301 := bstep (se 3 (by rfl) ⟨1182056, by rfl⟩ : syracuseStep 6304301 = 2364113) B2364113
theorem B2798297 : Blo 1104625 2798297 := bstep (se 2 (by rfl) ⟨1049361, by rfl⟩ : syracuseStep 2798297 = 2098723) B2098723
theorem B5976983 : Blo 1104625 5976983 := bstep (se 1 (by rfl) ⟨4482737, by rfl⟩ : syracuseStep 5976983 = 8965475) B8965475
theorem B6304985 : Blo 1104625 6304985 := bstep (se 2 (by rfl) ⟨2364369, by rfl⟩ : syracuseStep 6304985 = 4728739) B4728739
theorem B4732121 : Blo 1104625 4732121 := bstep (se 2 (by rfl) ⟨1774545, by rfl⟩ : syracuseStep 4732121 = 3549091) B3549091
theorem B4207895 : Blo 1104625 4207895 := bstep (se 1 (by rfl) ⟨3155921, by rfl⟩ : syracuseStep 4207895 = 6311843) B6311843
theorem B2799947 : Blo 1104625 2799947 := bstep (se 1 (by rfl) ⟨2099960, by rfl⟩ : syracuseStep 2799947 = 4199921) B4199921
theorem B17938867 : Blo 1104625 17938867 := bstep (se 1 (by rfl) ⟨13454150, by rfl⟩ : syracuseStep 17938867 = 26908301) B26908301
theorem B4733387 : Blo 1104625 4733387 := bstep (se 1 (by rfl) ⟨3550040, by rfl⟩ : syracuseStep 4733387 = 7100081) B7100081
theorem B4209155 : Blo 1104625 4209155 := bstep (se 1 (by rfl) ⟨3156866, by rfl⟩ : syracuseStep 4209155 = 6313733) B6313733
theorem B4799027 : Blo 1104625 4799027 := bstep (se 1 (by rfl) ⟨3599270, by rfl⟩ : syracuseStep 4799027 = 7198541) B7198541
theorem B17054509 : Blo 1104625 17054509 := bstep (se 3 (by rfl) ⟨3197720, by rfl⟩ : syracuseStep 17054509 = 6395441) B6395441
theorem B4733747 : Blo 1104625 4733747 := bstep (se 1 (by rfl) ⟨3550310, by rfl⟩ : syracuseStep 4733747 = 7100621) B7100621
theorem B2800919 : Blo 1104625 2800919 := bstep (se 1 (by rfl) ⟨2100689, by rfl⟩ : syracuseStep 2800919 = 4201379) B4201379
theorem B7978769 : Blo 1104625 7978769 := bstep (se 2 (by rfl) ⟨2992038, by rfl⟩ : syracuseStep 7978769 = 5984077) B5984077
theorem B5324561 : Blo 1104625 5324561 := bstep (se 2 (by rfl) ⟨1996710, by rfl⟩ : syracuseStep 5324561 = 3993421) B3993421
theorem B7094081 : Blo 1104625 7094081 := bstep (se 2 (by rfl) ⟨2660280, by rfl⟩ : syracuseStep 7094081 = 5320561) B5320561
theorem B2801587 : Blo 1104625 2801587 := bstep (se 1 (by rfl) ⟨2101190, by rfl⟩ : syracuseStep 2801587 = 4202381) B4202381
theorem B2801729 : Blo 1104625 2801729 := bstep (se 2 (by rfl) ⟨1050648, by rfl⟩ : syracuseStep 2801729 = 2101297) B2101297
theorem B51101837 : Blo 1104625 51101837 := bstep (se 3 (by rfl) ⟨9581594, by rfl⟩ : syracuseStep 51101837 = 19163189) B19163189
theorem B76596185 : Blo 1104625 76596185 := bstep (se 2 (by rfl) ⟨28723569, by rfl⟩ : syracuseStep 76596185 = 57447139) B57447139
theorem B2245619 : Blo 1104625 2245619 := bstep (se 1 (by rfl) ⟨1684214, by rfl⟩ : syracuseStep 2245619 = 3368429) B3368429
theorem B2802995 : Blo 1104625 2802995 := bstep (se 1 (by rfl) ⟨2102246, by rfl⟩ : syracuseStep 2802995 = 4204493) B4204493
theorem B1328599 : Blo 1104625 1328599 := bstep (se 1 (by rfl) ⟨996449, by rfl⟩ : syracuseStep 1328599 = 1992899) B1992899
theorem B1328791 : Blo 1104625 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B6309677 : Blo 1104625 6309677 := bstep (se 3 (by rfl) ⟨1183064, by rfl⟩ : syracuseStep 6309677 = 2366129) B2366129
theorem B2803531 : Blo 1104625 2803531 := bstep (se 1 (by rfl) ⟨2102648, by rfl⟩ : syracuseStep 2803531 = 4205297) B4205297
theorem B2803673 : Blo 1104625 2803673 := bstep (se 2 (by rfl) ⟨1051377, by rfl⟩ : syracuseStep 2803673 = 2102755) B2102755
theorem B1656971 : Blo 1104625 1656971 := bstep (se 1 (by rfl) ⟨1242728, by rfl⟩ : syracuseStep 1656971 = 2485457) B2485457
theorem B1656983 : Blo 1104625 1656983 := bstep (se 1 (by rfl) ⟨1242737, by rfl⟩ : syracuseStep 1656983 = 2485475) B2485475
theorem B1657049 : Blo 1104625 1657049 := bstep (se 2 (by rfl) ⟨621393, by rfl⟩ : syracuseStep 1657049 = 1242787) B1242787
theorem B8407313 : Blo 1104625 8407313 := bstep (se 2 (by rfl) ⟨3152742, by rfl⟩ : syracuseStep 8407313 = 6305485) B6305485
theorem B1493273 : Blo 1104625 1493273 := bstep (se 2 (by rfl) ⟨559977, by rfl⟩ : syracuseStep 1493273 = 1119955) B1119955
theorem B1657163 : Blo 1104625 1657163 := bstep (se 1 (by rfl) ⟨1242872, by rfl⟩ : syracuseStep 1657163 = 2485745) B2485745
theorem B1657175 : Blo 1104625 1657175 := bstep (se 1 (by rfl) ⟨1242881, by rfl⟩ : syracuseStep 1657175 = 2485763) B2485763
theorem B1657241 : Blo 1104625 1657241 := bstep (se 2 (by rfl) ⟨621465, by rfl⟩ : syracuseStep 1657241 = 1242931) B1242931
theorem B1657355 : Blo 1104625 1657355 := bstep (se 1 (by rfl) ⟨1243016, by rfl⟩ : syracuseStep 1657355 = 2486033) B2486033
theorem B1657367 : Blo 1104625 1657367 := bstep (se 1 (by rfl) ⟨1243025, by rfl⟩ : syracuseStep 1657367 = 2486051) B2486051
theorem B4541003 : Blo 1104625 4541003 := bstep (se 1 (by rfl) ⟨3405752, by rfl⟩ : syracuseStep 4541003 = 6811505) B6811505
theorem B1657433 : Blo 1104625 1657433 := bstep (se 2 (by rfl) ⟨621537, by rfl⟩ : syracuseStep 1657433 = 1243075) B1243075
theorem B1657547 : Blo 1104625 1657547 := bstep (se 1 (by rfl) ⟨1243160, by rfl⟩ : syracuseStep 1657547 = 2486321) B2486321
theorem B1657559 : Blo 1104625 1657559 := bstep (se 1 (by rfl) ⟨1243169, by rfl⟩ : syracuseStep 1657559 = 2486339) B2486339
theorem B2804503 : Blo 1104625 2804503 := bstep (se 1 (by rfl) ⟨2103377, by rfl⟩ : syracuseStep 2804503 = 4206755) B4206755
theorem B1657625 : Blo 1104625 1657625 := bstep (se 2 (by rfl) ⟨621609, by rfl⟩ : syracuseStep 1657625 = 1243219) B1243219
theorem B1657739 : Blo 1104625 1657739 := bstep (se 1 (by rfl) ⟨1243304, by rfl⟩ : syracuseStep 1657739 = 2486609) B2486609
theorem B1657751 : Blo 1104625 1657751 := bstep (se 1 (by rfl) ⟨1243313, by rfl⟩ : syracuseStep 1657751 = 2486627) B2486627
theorem B1657817 : Blo 1104625 1657817 := bstep (se 2 (by rfl) ⟨621681, by rfl⟩ : syracuseStep 1657817 = 1243363) B1243363
theorem B1657931 : Blo 1104625 1657931 := bstep (se 1 (by rfl) ⟨1243448, by rfl⟩ : syracuseStep 1657931 = 2486897) B2486897
theorem B1657943 : Blo 1104625 1657943 := bstep (se 1 (by rfl) ⟨1243457, by rfl⟩ : syracuseStep 1657943 = 2486915) B2486915
theorem B1658009 : Blo 1104625 1658009 := bstep (se 2 (by rfl) ⟨621753, by rfl⟩ : syracuseStep 1658009 = 1243507) B1243507
theorem B2804939 : Blo 1104625 2804939 := bstep (se 1 (by rfl) ⟨2103704, by rfl⟩ : syracuseStep 2804939 = 4207409) B4207409
theorem B1330391 : Blo 1104625 1330391 := bstep (se 1 (by rfl) ⟨997793, by rfl⟩ : syracuseStep 1330391 = 1995587) B1995587
theorem B1658123 : Blo 1104625 1658123 := bstep (se 1 (by rfl) ⟨1243592, by rfl⟩ : syracuseStep 1658123 = 2487185) B2487185
theorem B1658135 : Blo 1104625 1658135 := bstep (se 1 (by rfl) ⟨1243601, by rfl⟩ : syracuseStep 1658135 = 2487203) B2487203
theorem B1658201 : Blo 1104625 1658201 := bstep (se 2 (by rfl) ⟨621825, by rfl⟩ : syracuseStep 1658201 = 1243651) B1243651
theorem B1658315 : Blo 1104625 1658315 := bstep (se 1 (by rfl) ⟨1243736, by rfl⟩ : syracuseStep 1658315 = 2487473) B2487473
theorem B1658327 : Blo 1104625 1658327 := bstep (se 1 (by rfl) ⟨1243745, by rfl⟩ : syracuseStep 1658327 = 2487491) B2487491
theorem B1658393 : Blo 1104625 1658393 := bstep (se 2 (by rfl) ⟨621897, by rfl⟩ : syracuseStep 1658393 = 1243795) B1243795
theorem B2805313 : Blo 1104625 2805313 := bstep (se 2 (by rfl) ⟨1051992, by rfl⟩ : syracuseStep 2805313 = 2103985) B2103985
theorem B1658507 : Blo 1104625 1658507 := bstep (se 1 (by rfl) ⟨1243880, by rfl⟩ : syracuseStep 1658507 = 2487761) B2487761
theorem B1658519 : Blo 1104625 1658519 := bstep (se 1 (by rfl) ⟨1243889, by rfl⟩ : syracuseStep 1658519 = 2487779) B2487779
theorem B1658585 : Blo 1104625 1658585 := bstep (se 2 (by rfl) ⟨621969, by rfl⟩ : syracuseStep 1658585 = 1243939) B1243939
theorem B1658699 : Blo 1104625 1658699 := bstep (se 1 (by rfl) ⟨1244024, by rfl⟩ : syracuseStep 1658699 = 2488049) B2488049
theorem B1658711 : Blo 1104625 1658711 := bstep (se 1 (by rfl) ⟨1244033, by rfl⟩ : syracuseStep 1658711 = 2488067) B2488067
theorem B1658777 : Blo 1104625 1658777 := bstep (se 2 (by rfl) ⟨622041, by rfl⟩ : syracuseStep 1658777 = 1244083) B1244083
theorem B1658891 : Blo 1104625 1658891 := bstep (se 1 (by rfl) ⟨1244168, by rfl⟩ : syracuseStep 1658891 = 2488337) B2488337
theorem B9457681 : Blo 1104625 9457681 := bstep (se 2 (by rfl) ⟨3546630, by rfl⟩ : syracuseStep 9457681 = 7093261) B7093261
theorem B1658903 : Blo 1104625 1658903 := bstep (se 1 (by rfl) ⟨1244177, by rfl⟩ : syracuseStep 1658903 = 2488355) B2488355
theorem B1658969 : Blo 1104625 1658969 := bstep (se 2 (by rfl) ⟨622113, by rfl⟩ : syracuseStep 1658969 = 1244227) B1244227
theorem B9359491 : Blo 1104625 9359491 := bstep (se 1 (by rfl) ⟨7019618, by rfl⟩ : syracuseStep 9359491 = 14039237) B14039237
theorem B2805911 : Blo 1104625 2805911 := bstep (se 1 (by rfl) ⟨2104433, by rfl⟩ : syracuseStep 2805911 = 4208867) B4208867
theorem B1659083 : Blo 1104625 1659083 := bstep (se 1 (by rfl) ⟨1244312, by rfl⟩ : syracuseStep 1659083 = 2488625) B2488625
theorem B1659095 : Blo 1104625 1659095 := bstep (se 1 (by rfl) ⟨1244321, by rfl⟩ : syracuseStep 1659095 = 2488643) B2488643
theorem B1659161 : Blo 1104625 1659161 := bstep (se 2 (by rfl) ⟨622185, by rfl⟩ : syracuseStep 1659161 = 1244371) B1244371
theorem B9457955 : Blo 1104625 9457955 := bstep (se 1 (by rfl) ⟨7093466, by rfl⟩ : syracuseStep 9457955 = 14186933) B14186933
theorem B1659275 : Blo 1104625 1659275 := bstep (se 1 (by rfl) ⟨1244456, by rfl⟩ : syracuseStep 1659275 = 2488913) B2488913
theorem B1659287 : Blo 1104625 1659287 := bstep (se 1 (by rfl) ⟨1244465, by rfl⟩ : syracuseStep 1659287 = 2488931) B2488931
theorem B1331659 : Blo 1104625 1331659 := bstep (se 1 (by rfl) ⟨998744, by rfl⟩ : syracuseStep 1331659 = 1997489) B1997489
theorem B1659353 : Blo 1104625 1659353 := bstep (se 2 (by rfl) ⟨622257, by rfl⟩ : syracuseStep 1659353 = 1244515) B1244515
theorem B1659467 : Blo 1104625 1659467 := bstep (se 1 (by rfl) ⟨1244600, by rfl⟩ : syracuseStep 1659467 = 2489201) B2489201
theorem B1659479 : Blo 1104625 1659479 := bstep (se 1 (by rfl) ⟨1244609, by rfl⟩ : syracuseStep 1659479 = 2489219) B2489219
theorem B1921687 : Blo 1104625 1921687 := bstep (se 1 (by rfl) ⟨1441265, by rfl⟩ : syracuseStep 1921687 = 2882531) B2882531
theorem B1659545 : Blo 1104625 1659545 := bstep (se 2 (by rfl) ⟨622329, by rfl⟩ : syracuseStep 1659545 = 1244659) B1244659
theorem B60576497 : Blo 1104625 60576497 := bstep (se 2 (by rfl) ⟨22716186, by rfl⟩ : syracuseStep 60576497 = 45432373) B45432373
theorem B1659659 : Blo 1104625 1659659 := bstep (se 1 (by rfl) ⟨1244744, by rfl⟩ : syracuseStep 1659659 = 2489489) B2489489
theorem B1659671 : Blo 1104625 1659671 := bstep (se 1 (by rfl) ⟨1244753, by rfl⟩ : syracuseStep 1659671 = 2489507) B2489507
theorem B12112685 : Blo 1104625 12112685 := bstep (se 3 (by rfl) ⟨2271128, by rfl⟩ : syracuseStep 12112685 = 4542257) B4542257
theorem B1659737 : Blo 1104625 1659737 := bstep (se 2 (by rfl) ⟨622401, by rfl⟩ : syracuseStep 1659737 = 1244803) B1244803
theorem B1659851 : Blo 1104625 1659851 := bstep (se 1 (by rfl) ⟨1244888, by rfl⟩ : syracuseStep 1659851 = 2489777) B2489777
theorem B1659863 : Blo 1104625 1659863 := bstep (se 1 (by rfl) ⟨1244897, by rfl⟩ : syracuseStep 1659863 = 2489795) B2489795
theorem B5755865 : Blo 1104625 5755865 := bstep (se 2 (by rfl) ⟨2158449, by rfl⟩ : syracuseStep 5755865 = 4316899) B4316899
theorem B16176145 : Blo 1104625 16176145 := bstep (se 2 (by rfl) ⟨6066054, by rfl⟩ : syracuseStep 16176145 = 12132109) B12132109
theorem B1659929 : Blo 1104625 1659929 := bstep (se 2 (by rfl) ⟨622473, by rfl⟩ : syracuseStep 1659929 = 1244947) B1244947
theorem B1660043 : Blo 1104625 1660043 := bstep (se 1 (by rfl) ⟨1245032, by rfl⟩ : syracuseStep 1660043 = 2490065) B2490065
theorem B1660055 : Blo 1104625 1660055 := bstep (se 1 (by rfl) ⟨1245041, by rfl⟩ : syracuseStep 1660055 = 2490083) B2490083
theorem B1660121 : Blo 1104625 1660121 := bstep (se 2 (by rfl) ⟨622545, by rfl⟩ : syracuseStep 1660121 = 1245091) B1245091
theorem B1660235 : Blo 1104625 1660235 := bstep (se 1 (by rfl) ⟨1245176, by rfl⟩ : syracuseStep 1660235 = 2490353) B2490353
theorem B1660247 : Blo 1104625 1660247 := bstep (se 1 (by rfl) ⟨1245185, by rfl⟩ : syracuseStep 1660247 = 2490371) B2490371
theorem B76567949 : Blo 1104625 76567949 := bstep (se 3 (by rfl) ⟨14356490, by rfl⟩ : syracuseStep 76567949 = 28712981) B28712981
theorem B3986833 : Blo 1104625 3986833 := bstep (se 2 (by rfl) ⟨1495062, by rfl⟩ : syracuseStep 3986833 = 2990125) B2990125
theorem B1660313 : Blo 1104625 1660313 := bstep (se 2 (by rfl) ⟨622617, by rfl⟩ : syracuseStep 1660313 = 1245235) B1245235
theorem B1660427 : Blo 1104625 1660427 := bstep (se 1 (by rfl) ⟨1245320, by rfl⟩ : syracuseStep 1660427 = 2490641) B2490641
theorem B1660439 : Blo 1104625 1660439 := bstep (se 1 (by rfl) ⟨1245329, by rfl⟩ : syracuseStep 1660439 = 2490659) B2490659
theorem B1660505 : Blo 1104625 1660505 := bstep (se 2 (by rfl) ⟨622689, by rfl⟩ : syracuseStep 1660505 = 1245379) B1245379
theorem B1398475 : Blo 1104625 1398475 := bstep (se 1 (by rfl) ⟨1048856, by rfl⟩ : syracuseStep 1398475 = 2097713) B2097713
theorem B1660619 : Blo 1104625 1660619 := bstep (se 1 (by rfl) ⟨1245464, by rfl⟩ : syracuseStep 1660619 = 2490929) B2490929
theorem B1660631 : Blo 1104625 1660631 := bstep (se 1 (by rfl) ⟨1245473, by rfl⟩ : syracuseStep 1660631 = 2490947) B2490947
theorem B4544279 : Blo 1104625 4544279 := bstep (se 1 (by rfl) ⟨3408209, by rfl⟩ : syracuseStep 4544279 = 6816419) B6816419
theorem B1660697 : Blo 1104625 1660697 := bstep (se 2 (by rfl) ⟨622761, by rfl⟩ : syracuseStep 1660697 = 1245523) B1245523
theorem B1660811 : Blo 1104625 1660811 := bstep (se 1 (by rfl) ⟨1245608, by rfl⟩ : syracuseStep 1660811 = 2491217) B2491217
theorem B1660823 : Blo 1104625 1660823 := bstep (se 1 (by rfl) ⟨1245617, by rfl⟩ : syracuseStep 1660823 = 2491235) B2491235
theorem B35903411 : Blo 1104625 35903411 := bstep (se 1 (by rfl) ⟨26927558, by rfl⟩ : syracuseStep 35903411 = 53855117) B53855117
theorem B3790795 : Blo 1104625 3790795 := bstep (se 1 (by rfl) ⟨2843096, by rfl⟩ : syracuseStep 3790795 = 5686193) B5686193
theorem B5593049 : Blo 1104625 5593049 := bstep (se 2 (by rfl) ⟨2097393, by rfl⟩ : syracuseStep 5593049 = 4194787) B4194787
theorem B1660889 : Blo 1104625 1660889 := bstep (se 2 (by rfl) ⟨622833, by rfl⟩ : syracuseStep 1660889 = 1245667) B1245667
theorem B8411201 : Blo 1104625 8411201 := bstep (se 2 (by rfl) ⟨3154200, by rfl⟩ : syracuseStep 8411201 = 6308401) B6308401
theorem B1661003 : Blo 1104625 1661003 := bstep (se 1 (by rfl) ⟨1245752, by rfl⟩ : syracuseStep 1661003 = 2491505) B2491505
theorem B1661015 : Blo 1104625 1661015 := bstep (se 1 (by rfl) ⟨1245761, by rfl⟩ : syracuseStep 1661015 = 2491523) B2491523
theorem B1661081 : Blo 1104625 1661081 := bstep (se 2 (by rfl) ⟨622905, by rfl⟩ : syracuseStep 1661081 = 1245811) B1245811
theorem B1661195 : Blo 1104625 1661195 := bstep (se 1 (by rfl) ⟨1245896, by rfl⟩ : syracuseStep 1661195 = 2491793) B2491793
theorem B1661207 : Blo 1104625 1661207 := bstep (se 1 (by rfl) ⟨1245905, by rfl⟩ : syracuseStep 1661207 = 2491811) B2491811
theorem B1661273 : Blo 1104625 1661273 := bstep (se 2 (by rfl) ⟨622977, by rfl⟩ : syracuseStep 1661273 = 1245955) B1245955
theorem B1661387 : Blo 1104625 1661387 := bstep (se 1 (by rfl) ⟨1246040, by rfl⟩ : syracuseStep 1661387 = 2492081) B2492081
theorem B1661399 : Blo 1104625 1661399 := bstep (se 1 (by rfl) ⟨1246049, by rfl⟩ : syracuseStep 1661399 = 2492099) B2492099
theorem B1661465 : Blo 1104625 1661465 := bstep (se 2 (by rfl) ⟨623049, by rfl⟩ : syracuseStep 1661465 = 1246099) B1246099
theorem B1661579 : Blo 1104625 1661579 := bstep (se 1 (by rfl) ⟨1246184, by rfl⟩ : syracuseStep 1661579 = 2492369) B2492369
theorem B1399447 : Blo 1104625 1399447 := bstep (se 1 (by rfl) ⟨1049585, by rfl⟩ : syracuseStep 1399447 = 2099171) B2099171
theorem B1661591 : Blo 1104625 1661591 := bstep (se 1 (by rfl) ⟨1246193, by rfl⟩ : syracuseStep 1661591 = 2492387) B2492387
theorem B7101107 : Blo 1104625 7101107 := bstep (se 1 (by rfl) ⟨5325830, by rfl⟩ : syracuseStep 7101107 = 10651661) B10651661
theorem B1661657 : Blo 1104625 1661657 := bstep (se 2 (by rfl) ⟨623121, by rfl⟩ : syracuseStep 1661657 = 1246243) B1246243
theorem B1104631 : Blo 1104625 1104631 := bstep (se 1 (by rfl) ⟨828473, by rfl⟩ : syracuseStep 1104631 = 1656947) B1656947
theorem B1104651 : Blo 1104625 1104651 := bstep (se 1 (by rfl) ⟨828488, by rfl⟩ : syracuseStep 1104651 = 1656977) B1656977
theorem B1104663 : Blo 1104625 1104663 := bstep (se 1 (by rfl) ⟨828497, by rfl⟩ : syracuseStep 1104663 = 1656995) B1656995
theorem B1104683 : Blo 1104625 1104683 := bstep (se 1 (by rfl) ⟨828512, by rfl⟩ : syracuseStep 1104683 = 1657025) B1657025
theorem B1104695 : Blo 1104625 1104695 := bstep (se 1 (by rfl) ⟨828521, by rfl⟩ : syracuseStep 1104695 = 1657043) B1657043
theorem B1104715 : Blo 1104625 1104715 := bstep (se 1 (by rfl) ⟨828536, by rfl⟩ : syracuseStep 1104715 = 1657073) B1657073
theorem B1661771 : Blo 1104625 1661771 := bstep (se 1 (by rfl) ⟨1246328, by rfl⟩ : syracuseStep 1661771 = 2492657) B2492657
theorem B1104727 : Blo 1104625 1104727 := bstep (se 1 (by rfl) ⟨828545, by rfl⟩ : syracuseStep 1104727 = 1657091) B1657091
theorem B1661783 : Blo 1104625 1661783 := bstep (se 1 (by rfl) ⟨1246337, by rfl⟩ : syracuseStep 1661783 = 2492675) B2492675
theorem B1104747 : Blo 1104625 1104747 := bstep (se 1 (by rfl) ⟨828560, by rfl⟩ : syracuseStep 1104747 = 1657121) B1657121
theorem B15129461 : Blo 1104625 15129461 := bstep (se 5 (by rfl) ⟨709193, by rfl⟩ : syracuseStep 15129461 = 1418387) B1418387
theorem B1104759 : Blo 1104625 1104759 := bstep (se 1 (by rfl) ⟨828569, by rfl⟩ : syracuseStep 1104759 = 1657139) B1657139
theorem B1104779 : Blo 1104625 1104779 := bstep (se 1 (by rfl) ⟨828584, by rfl⟩ : syracuseStep 1104779 = 1657169) B1657169
theorem B1104791 : Blo 1104625 1104791 := bstep (se 1 (by rfl) ⟨828593, by rfl⟩ : syracuseStep 1104791 = 1657187) B1657187
theorem B1661849 : Blo 1104625 1661849 := bstep (se 2 (by rfl) ⟨623193, by rfl⟩ : syracuseStep 1661849 = 1246387) B1246387
theorem B1498009 : Blo 1104625 1498009 := bstep (se 2 (by rfl) ⟨561753, by rfl⟩ : syracuseStep 1498009 = 1123507) B1123507
theorem B1104811 : Blo 1104625 1104811 := bstep (se 1 (by rfl) ⟨828608, by rfl⟩ : syracuseStep 1104811 = 1657217) B1657217
theorem B1104823 : Blo 1104625 1104823 := bstep (se 1 (by rfl) ⟨828617, by rfl⟩ : syracuseStep 1104823 = 1657235) B1657235
theorem B1104843 : Blo 1104625 1104843 := bstep (se 1 (by rfl) ⟨828632, by rfl⟩ : syracuseStep 1104843 = 1657265) B1657265
theorem B1104855 : Blo 1104625 1104855 := bstep (se 1 (by rfl) ⟨828641, by rfl⟩ : syracuseStep 1104855 = 1657283) B1657283
theorem B1104875 : Blo 1104625 1104875 := bstep (se 1 (by rfl) ⟨828656, by rfl⟩ : syracuseStep 1104875 = 1657313) B1657313
theorem B1104887 : Blo 1104625 1104887 := bstep (se 1 (by rfl) ⟨828665, by rfl⟩ : syracuseStep 1104887 = 1657331) B1657331
theorem B1104907 : Blo 1104625 1104907 := bstep (se 1 (by rfl) ⟨828680, by rfl⟩ : syracuseStep 1104907 = 1657361) B1657361
theorem B1661963 : Blo 1104625 1661963 := bstep (se 1 (by rfl) ⟨1246472, by rfl⟩ : syracuseStep 1661963 = 2492945) B2492945
theorem B1104919 : Blo 1104625 1104919 := bstep (se 1 (by rfl) ⟨828689, by rfl⟩ : syracuseStep 1104919 = 1657379) B1657379
theorem B1661975 : Blo 1104625 1661975 := bstep (se 1 (by rfl) ⟨1246481, by rfl⟩ : syracuseStep 1661975 = 2492963) B2492963
theorem B1104939 : Blo 1104625 1104939 := bstep (se 1 (by rfl) ⟨828704, by rfl⟩ : syracuseStep 1104939 = 1657409) B1657409
theorem B1104951 : Blo 1104625 1104951 := bstep (se 1 (by rfl) ⟨828713, by rfl⟩ : syracuseStep 1104951 = 1657427) B1657427
theorem B1104971 : Blo 1104625 1104971 := bstep (se 1 (by rfl) ⟨828728, by rfl⟩ : syracuseStep 1104971 = 1657457) B1657457
theorem B1104983 : Blo 1104625 1104983 := bstep (se 1 (by rfl) ⟨828737, by rfl⟩ : syracuseStep 1104983 = 1657475) B1657475
theorem B1662041 : Blo 1104625 1662041 := bstep (se 2 (by rfl) ⟨623265, by rfl⟩ : syracuseStep 1662041 = 1246531) B1246531
theorem B1105003 : Blo 1104625 1105003 := bstep (se 1 (by rfl) ⟨828752, by rfl⟩ : syracuseStep 1105003 = 1657505) B1657505
theorem B1105015 : Blo 1104625 1105015 := bstep (se 1 (by rfl) ⟨828761, by rfl⟩ : syracuseStep 1105015 = 1657523) B1657523
theorem B1105035 : Blo 1104625 1105035 := bstep (se 1 (by rfl) ⟨828776, by rfl⟩ : syracuseStep 1105035 = 1657553) B1657553
theorem B1105047 : Blo 1104625 1105047 := bstep (se 1 (by rfl) ⟨828785, by rfl⟩ : syracuseStep 1105047 = 1657571) B1657571
theorem B1105067 : Blo 1104625 1105067 := bstep (se 1 (by rfl) ⟨828800, by rfl⟩ : syracuseStep 1105067 = 1657601) B1657601
theorem B1105079 : Blo 1104625 1105079 := bstep (se 1 (by rfl) ⟨828809, by rfl⟩ : syracuseStep 1105079 = 1657619) B1657619
theorem B1105099 : Blo 1104625 1105099 := bstep (se 1 (by rfl) ⟨828824, by rfl⟩ : syracuseStep 1105099 = 1657649) B1657649
theorem B1662155 : Blo 1104625 1662155 := bstep (se 1 (by rfl) ⟨1246616, by rfl⟩ : syracuseStep 1662155 = 2493233) B2493233
theorem B1105111 : Blo 1104625 1105111 := bstep (se 1 (by rfl) ⟨828833, by rfl⟩ : syracuseStep 1105111 = 1657667) B1657667
theorem B1662167 : Blo 1104625 1662167 := bstep (se 1 (by rfl) ⟨1246625, by rfl⟩ : syracuseStep 1662167 = 2493251) B2493251
theorem B1105131 : Blo 1104625 1105131 := bstep (se 1 (by rfl) ⟨828848, by rfl⟩ : syracuseStep 1105131 = 1657697) B1657697
theorem B1105143 : Blo 1104625 1105143 := bstep (se 1 (by rfl) ⟨828857, by rfl⟩ : syracuseStep 1105143 = 1657715) B1657715
theorem B1105163 : Blo 1104625 1105163 := bstep (se 1 (by rfl) ⟨828872, by rfl⟩ : syracuseStep 1105163 = 1657745) B1657745
theorem B1105175 : Blo 1104625 1105175 := bstep (se 1 (by rfl) ⟨828881, by rfl⟩ : syracuseStep 1105175 = 1657763) B1657763
theorem B1662233 : Blo 1104625 1662233 := bstep (se 2 (by rfl) ⟨623337, by rfl⟩ : syracuseStep 1662233 = 1246675) B1246675
theorem B1105195 : Blo 1104625 1105195 := bstep (se 1 (by rfl) ⟨828896, by rfl⟩ : syracuseStep 1105195 = 1657793) B1657793
theorem B1105207 : Blo 1104625 1105207 := bstep (se 1 (by rfl) ⟨828905, by rfl⟩ : syracuseStep 1105207 = 1657811) B1657811
theorem B1105227 : Blo 1104625 1105227 := bstep (se 1 (by rfl) ⟨828920, by rfl⟩ : syracuseStep 1105227 = 1657841) B1657841
theorem B1105239 : Blo 1104625 1105239 := bstep (se 1 (by rfl) ⟨828929, by rfl⟩ : syracuseStep 1105239 = 1657859) B1657859
theorem B1105259 : Blo 1104625 1105259 := bstep (se 1 (by rfl) ⟨828944, by rfl⟩ : syracuseStep 1105259 = 1657889) B1657889
theorem B1105271 : Blo 1104625 1105271 := bstep (se 1 (by rfl) ⟨828953, by rfl⟩ : syracuseStep 1105271 = 1657907) B1657907
theorem B1105291 : Blo 1104625 1105291 := bstep (se 1 (by rfl) ⟨828968, by rfl⟩ : syracuseStep 1105291 = 1657937) B1657937
theorem B1662347 : Blo 1104625 1662347 := bstep (se 1 (by rfl) ⟨1246760, by rfl⟩ : syracuseStep 1662347 = 2493521) B2493521
theorem B1105303 : Blo 1104625 1105303 := bstep (se 1 (by rfl) ⟨828977, by rfl⟩ : syracuseStep 1105303 = 1657955) B1657955
theorem B1662359 : Blo 1104625 1662359 := bstep (se 1 (by rfl) ⟨1246769, by rfl⟩ : syracuseStep 1662359 = 2493539) B2493539
theorem B1105323 : Blo 1104625 1105323 := bstep (se 1 (by rfl) ⟨828992, by rfl⟩ : syracuseStep 1105323 = 1657985) B1657985
theorem B1105335 : Blo 1104625 1105335 := bstep (se 1 (by rfl) ⟨829001, by rfl⟩ : syracuseStep 1105335 = 1658003) B1658003
theorem B1105355 : Blo 1104625 1105355 := bstep (se 1 (by rfl) ⟨829016, by rfl⟩ : syracuseStep 1105355 = 1658033) B1658033
theorem B1400267 : Blo 1104625 1400267 := bstep (se 1 (by rfl) ⟨1050200, by rfl⟩ : syracuseStep 1400267 = 2100401) B2100401
theorem B1105367 : Blo 1104625 1105367 := bstep (se 1 (by rfl) ⟨829025, by rfl⟩ : syracuseStep 1105367 = 1658051) B1658051
theorem B1662425 : Blo 1104625 1662425 := bstep (se 2 (by rfl) ⟨623409, by rfl⟩ : syracuseStep 1662425 = 1246819) B1246819
theorem B1105387 : Blo 1104625 1105387 := bstep (se 1 (by rfl) ⟨829040, by rfl⟩ : syracuseStep 1105387 = 1658081) B1658081
theorem B1105399 : Blo 1104625 1105399 := bstep (se 1 (by rfl) ⟨829049, by rfl⟩ : syracuseStep 1105399 = 1658099) B1658099
theorem B1105419 : Blo 1104625 1105419 := bstep (se 1 (by rfl) ⟨829064, by rfl⟩ : syracuseStep 1105419 = 1658129) B1658129
theorem B1105431 : Blo 1104625 1105431 := bstep (se 1 (by rfl) ⟨829073, by rfl⟩ : syracuseStep 1105431 = 1658147) B1658147
theorem B1105451 : Blo 1104625 1105451 := bstep (se 1 (by rfl) ⟨829088, by rfl⟩ : syracuseStep 1105451 = 1658177) B1658177
theorem B5594669 : Blo 1104625 5594669 := bstep (se 3 (by rfl) ⟨1049000, by rfl⟩ : syracuseStep 5594669 = 2098001) B2098001
theorem B1105463 : Blo 1104625 1105463 := bstep (se 1 (by rfl) ⟨829097, by rfl⟩ : syracuseStep 1105463 = 1658195) B1658195
theorem B1105483 : Blo 1104625 1105483 := bstep (se 1 (by rfl) ⟨829112, by rfl⟩ : syracuseStep 1105483 = 1658225) B1658225
theorem B1662539 : Blo 1104625 1662539 := bstep (se 1 (by rfl) ⟨1246904, by rfl⟩ : syracuseStep 1662539 = 2493809) B2493809
theorem B1105495 : Blo 1104625 1105495 := bstep (se 1 (by rfl) ⟨829121, by rfl⟩ : syracuseStep 1105495 = 1658243) B1658243
theorem B1662551 : Blo 1104625 1662551 := bstep (se 1 (by rfl) ⟨1246913, by rfl⟩ : syracuseStep 1662551 = 2493827) B2493827
theorem B1105515 : Blo 1104625 1105515 := bstep (se 1 (by rfl) ⟨829136, by rfl⟩ : syracuseStep 1105515 = 1658273) B1658273
theorem B1105527 : Blo 1104625 1105527 := bstep (se 1 (by rfl) ⟨829145, by rfl⟩ : syracuseStep 1105527 = 1658291) B1658291
theorem B1105547 : Blo 1104625 1105547 := bstep (se 1 (by rfl) ⟨829160, by rfl⟩ : syracuseStep 1105547 = 1658321) B1658321
theorem B1105559 : Blo 1104625 1105559 := bstep (se 1 (by rfl) ⟨829169, by rfl⟩ : syracuseStep 1105559 = 1658339) B1658339
theorem B1662617 : Blo 1104625 1662617 := bstep (se 2 (by rfl) ⟨623481, by rfl⟩ : syracuseStep 1662617 = 1246963) B1246963
theorem B1105579 : Blo 1104625 1105579 := bstep (se 1 (by rfl) ⟨829184, by rfl⟩ : syracuseStep 1105579 = 1658369) B1658369
theorem B1105591 : Blo 1104625 1105591 := bstep (se 1 (by rfl) ⟨829193, by rfl⟩ : syracuseStep 1105591 = 1658387) B1658387
theorem B1105611 : Blo 1104625 1105611 := bstep (se 1 (by rfl) ⟨829208, by rfl⟩ : syracuseStep 1105611 = 1658417) B1658417
theorem B1105623 : Blo 1104625 1105623 := bstep (se 1 (by rfl) ⟨829217, by rfl⟩ : syracuseStep 1105623 = 1658435) B1658435
theorem B1105643 : Blo 1104625 1105643 := bstep (se 1 (by rfl) ⟨829232, by rfl⟩ : syracuseStep 1105643 = 1658465) B1658465
theorem B38395633 : Blo 1104625 38395633 := bstep (se 2 (by rfl) ⟨14398362, by rfl⟩ : syracuseStep 38395633 = 28796725) B28796725
theorem B1105655 : Blo 1104625 1105655 := bstep (se 1 (by rfl) ⟨829241, by rfl⟩ : syracuseStep 1105655 = 1658483) B1658483
theorem B1105675 : Blo 1104625 1105675 := bstep (se 1 (by rfl) ⟨829256, by rfl⟩ : syracuseStep 1105675 = 1658513) B1658513
theorem B1662731 : Blo 1104625 1662731 := bstep (se 1 (by rfl) ⟨1247048, by rfl⟩ : syracuseStep 1662731 = 2494097) B2494097
theorem B1105687 : Blo 1104625 1105687 := bstep (se 1 (by rfl) ⟨829265, by rfl⟩ : syracuseStep 1105687 = 1658531) B1658531
theorem B1662743 : Blo 1104625 1662743 := bstep (se 1 (by rfl) ⟨1247057, by rfl⟩ : syracuseStep 1662743 = 2494115) B2494115
theorem B1105707 : Blo 1104625 1105707 := bstep (se 1 (by rfl) ⟨829280, by rfl⟩ : syracuseStep 1105707 = 1658561) B1658561
theorem B1105719 : Blo 1104625 1105719 := bstep (se 1 (by rfl) ⟨829289, by rfl⟩ : syracuseStep 1105719 = 1658579) B1658579
theorem B1105739 : Blo 1104625 1105739 := bstep (se 1 (by rfl) ⟨829304, by rfl⟩ : syracuseStep 1105739 = 1658609) B1658609
theorem B1105751 : Blo 1104625 1105751 := bstep (se 1 (by rfl) ⟨829313, by rfl⟩ : syracuseStep 1105751 = 1658627) B1658627
theorem B1662809 : Blo 1104625 1662809 := bstep (se 2 (by rfl) ⟨623553, by rfl⟩ : syracuseStep 1662809 = 1247107) B1247107
theorem B7987045 : Blo 1104625 7987045 := bstep (se 4 (by rfl) ⟨748785, by rfl⟩ : syracuseStep 7987045 = 1497571) B1497571
theorem B1105771 : Blo 1104625 1105771 := bstep (se 1 (by rfl) ⟨829328, by rfl⟩ : syracuseStep 1105771 = 1658657) B1658657
theorem B1105783 : Blo 1104625 1105783 := bstep (se 1 (by rfl) ⟨829337, by rfl⟩ : syracuseStep 1105783 = 1658675) B1658675
theorem B1105803 : Blo 1104625 1105803 := bstep (se 1 (by rfl) ⟨829352, by rfl⟩ : syracuseStep 1105803 = 1658705) B1658705
theorem B1105815 : Blo 1104625 1105815 := bstep (se 1 (by rfl) ⟨829361, by rfl⟩ : syracuseStep 1105815 = 1658723) B1658723
theorem B1105835 : Blo 1104625 1105835 := bstep (se 1 (by rfl) ⟨829376, by rfl⟩ : syracuseStep 1105835 = 1658753) B1658753
theorem B1105847 : Blo 1104625 1105847 := bstep (se 1 (by rfl) ⟨829385, by rfl⟩ : syracuseStep 1105847 = 1658771) B1658771
theorem B1105867 : Blo 1104625 1105867 := bstep (se 1 (by rfl) ⟨829400, by rfl⟩ : syracuseStep 1105867 = 1658801) B1658801
theorem B1662923 : Blo 1104625 1662923 := bstep (se 1 (by rfl) ⟨1247192, by rfl⟩ : syracuseStep 1662923 = 2494385) B2494385
theorem B1105879 : Blo 1104625 1105879 := bstep (se 1 (by rfl) ⟨829409, by rfl⟩ : syracuseStep 1105879 = 1658819) B1658819
theorem B1662935 : Blo 1104625 1662935 := bstep (se 1 (by rfl) ⟨1247201, by rfl⟩ : syracuseStep 1662935 = 2494403) B2494403
theorem B8413145 : Blo 1104625 8413145 := bstep (se 2 (by rfl) ⟨3154929, by rfl⟩ : syracuseStep 8413145 = 6309859) B6309859
theorem B1105899 : Blo 1104625 1105899 := bstep (se 1 (by rfl) ⟨829424, by rfl⟩ : syracuseStep 1105899 = 1658849) B1658849
theorem B1105911 : Blo 1104625 1105911 := bstep (se 1 (by rfl) ⟨829433, by rfl⟩ : syracuseStep 1105911 = 1658867) B1658867
theorem B1105931 : Blo 1104625 1105931 := bstep (se 1 (by rfl) ⟨829448, by rfl⟩ : syracuseStep 1105931 = 1658897) B1658897
theorem B1105943 : Blo 1104625 1105943 := bstep (se 1 (by rfl) ⟨829457, by rfl⟩ : syracuseStep 1105943 = 1658915) B1658915
theorem B1105963 : Blo 1104625 1105963 := bstep (se 1 (by rfl) ⟨829472, by rfl⟩ : syracuseStep 1105963 = 1658945) B1658945
theorem B1105975 : Blo 1104625 1105975 := bstep (se 1 (by rfl) ⟨829481, by rfl⟩ : syracuseStep 1105975 = 1658963) B1658963
theorem B1105995 : Blo 1104625 1105995 := bstep (se 1 (by rfl) ⟨829496, by rfl⟩ : syracuseStep 1105995 = 1658993) B1658993
theorem B1106007 : Blo 1104625 1106007 := bstep (se 1 (by rfl) ⟨829505, by rfl⟩ : syracuseStep 1106007 = 1659011) B1659011
theorem B7987301 : Blo 1104625 7987301 := bstep (se 4 (by rfl) ⟨748809, by rfl⟩ : syracuseStep 7987301 = 1497619) B1497619
theorem B1106027 : Blo 1104625 1106027 := bstep (se 1 (by rfl) ⟨829520, by rfl⟩ : syracuseStep 1106027 = 1659041) B1659041
theorem B1106039 : Blo 1104625 1106039 := bstep (se 1 (by rfl) ⟨829529, by rfl⟩ : syracuseStep 1106039 = 1659059) B1659059
theorem B1106059 : Blo 1104625 1106059 := bstep (se 1 (by rfl) ⟨829544, by rfl⟩ : syracuseStep 1106059 = 1659089) B1659089
theorem B1400971 : Blo 1104625 1400971 := bstep (se 1 (by rfl) ⟨1050728, by rfl⟩ : syracuseStep 1400971 = 2101457) B2101457
theorem B1106071 : Blo 1104625 1106071 := bstep (se 1 (by rfl) ⟨829553, by rfl⟩ : syracuseStep 1106071 = 1659107) B1659107
theorem B1106091 : Blo 1104625 1106091 := bstep (se 1 (by rfl) ⟨829568, by rfl⟩ : syracuseStep 1106091 = 1659137) B1659137
theorem B1106103 : Blo 1104625 1106103 := bstep (se 1 (by rfl) ⟨829577, by rfl⟩ : syracuseStep 1106103 = 1659155) B1659155
theorem B1106123 : Blo 1104625 1106123 := bstep (se 1 (by rfl) ⟨829592, by rfl⟩ : syracuseStep 1106123 = 1659185) B1659185
theorem B3367115 : Blo 1104625 3367115 := bstep (se 1 (by rfl) ⟨2525336, by rfl⟩ : syracuseStep 3367115 = 5050673) B5050673
theorem B1106135 : Blo 1104625 1106135 := bstep (se 1 (by rfl) ⟨829601, by rfl⟩ : syracuseStep 1106135 = 1659203) B1659203
theorem B1106155 : Blo 1104625 1106155 := bstep (se 1 (by rfl) ⟨829616, by rfl⟩ : syracuseStep 1106155 = 1659233) B1659233
theorem B1106167 : Blo 1104625 1106167 := bstep (se 1 (by rfl) ⟨829625, by rfl⟩ : syracuseStep 1106167 = 1659251) B1659251
theorem B1106187 : Blo 1104625 1106187 := bstep (se 1 (by rfl) ⟨829640, by rfl⟩ : syracuseStep 1106187 = 1659281) B1659281
theorem B1106199 : Blo 1104625 1106199 := bstep (se 1 (by rfl) ⟨829649, by rfl⟩ : syracuseStep 1106199 = 1659299) B1659299
theorem B1106219 : Blo 1104625 1106219 := bstep (se 1 (by rfl) ⟨829664, by rfl⟩ : syracuseStep 1106219 = 1659329) B1659329
theorem B1106231 : Blo 1104625 1106231 := bstep (se 1 (by rfl) ⟨829673, by rfl⟩ : syracuseStep 1106231 = 1659347) B1659347
theorem B20209985 : Blo 1104625 20209985 := bstep (se 2 (by rfl) ⟨7578744, by rfl⟩ : syracuseStep 20209985 = 15157489) B15157489
theorem B1106251 : Blo 1104625 1106251 := bstep (se 1 (by rfl) ⟨829688, by rfl⟩ : syracuseStep 1106251 = 1659377) B1659377
theorem B1106263 : Blo 1104625 1106263 := bstep (se 1 (by rfl) ⟨829697, by rfl⟩ : syracuseStep 1106263 = 1659395) B1659395
theorem B1106283 : Blo 1104625 1106283 := bstep (se 1 (by rfl) ⟨829712, by rfl⟩ : syracuseStep 1106283 = 1659425) B1659425
theorem B1106295 : Blo 1104625 1106295 := bstep (se 1 (by rfl) ⟨829721, by rfl⟩ : syracuseStep 1106295 = 1659443) B1659443
theorem B1106315 : Blo 1104625 1106315 := bstep (se 1 (by rfl) ⟨829736, by rfl⟩ : syracuseStep 1106315 = 1659473) B1659473
theorem B1106327 : Blo 1104625 1106327 := bstep (se 1 (by rfl) ⟨829745, by rfl⟩ : syracuseStep 1106327 = 1659491) B1659491
theorem B1401239 : Blo 1104625 1401239 := bstep (se 1 (by rfl) ⟨1050929, by rfl⟩ : syracuseStep 1401239 = 2101859) B2101859
theorem B1106347 : Blo 1104625 1106347 := bstep (se 1 (by rfl) ⟨829760, by rfl⟩ : syracuseStep 1106347 = 1659521) B1659521
theorem B1106359 : Blo 1104625 1106359 := bstep (se 1 (by rfl) ⟨829769, by rfl⟩ : syracuseStep 1106359 = 1659539) B1659539
theorem B1106379 : Blo 1104625 1106379 := bstep (se 1 (by rfl) ⟨829784, by rfl⟩ : syracuseStep 1106379 = 1659569) B1659569
theorem B1106391 : Blo 1104625 1106391 := bstep (se 1 (by rfl) ⟨829793, by rfl⟩ : syracuseStep 1106391 = 1659587) B1659587
theorem B1106411 : Blo 1104625 1106411 := bstep (se 1 (by rfl) ⟨829808, by rfl⟩ : syracuseStep 1106411 = 1659617) B1659617
theorem B1106423 : Blo 1104625 1106423 := bstep (se 1 (by rfl) ⟨829817, by rfl⟩ : syracuseStep 1106423 = 1659635) B1659635
theorem B1106443 : Blo 1104625 1106443 := bstep (se 1 (by rfl) ⟨829832, by rfl⟩ : syracuseStep 1106443 = 1659665) B1659665
theorem B26894861 : Blo 1104625 26894861 := bstep (se 3 (by rfl) ⟨5042786, by rfl⟩ : syracuseStep 26894861 = 10085573) B10085573
theorem B1106455 : Blo 1104625 1106455 := bstep (se 1 (by rfl) ⟨829841, by rfl⟩ : syracuseStep 1106455 = 1659683) B1659683
theorem B1106475 : Blo 1104625 1106475 := bstep (se 1 (by rfl) ⟨829856, by rfl⟩ : syracuseStep 1106475 = 1659713) B1659713
theorem B1106487 : Blo 1104625 1106487 := bstep (se 1 (by rfl) ⟨829865, by rfl⟩ : syracuseStep 1106487 = 1659731) B1659731
theorem B1106507 : Blo 1104625 1106507 := bstep (se 1 (by rfl) ⟨829880, by rfl⟩ : syracuseStep 1106507 = 1659761) B1659761
theorem B1106519 : Blo 1104625 1106519 := bstep (se 1 (by rfl) ⟨829889, by rfl⟩ : syracuseStep 1106519 = 1659779) B1659779
theorem B1106539 : Blo 1104625 1106539 := bstep (se 1 (by rfl) ⟨829904, by rfl⟩ : syracuseStep 1106539 = 1659809) B1659809
theorem B1106551 : Blo 1104625 1106551 := bstep (se 1 (by rfl) ⟨829913, by rfl⟩ : syracuseStep 1106551 = 1659827) B1659827
theorem B1106571 : Blo 1104625 1106571 := bstep (se 1 (by rfl) ⟨829928, by rfl⟩ : syracuseStep 1106571 = 1659857) B1659857
theorem B1106583 : Blo 1104625 1106583 := bstep (se 1 (by rfl) ⟨829937, by rfl⟩ : syracuseStep 1106583 = 1659875) B1659875
theorem B1106603 : Blo 1104625 1106603 := bstep (se 1 (by rfl) ⟨829952, by rfl⟩ : syracuseStep 1106603 = 1659905) B1659905
theorem B1991347 : Blo 1104625 1991347 := bstep (se 1 (by rfl) ⟨1493510, by rfl⟩ : syracuseStep 1991347 = 2987021) B2987021
theorem B1106615 : Blo 1104625 1106615 := bstep (se 1 (by rfl) ⟨829961, by rfl⟩ : syracuseStep 1106615 = 1659923) B1659923
theorem B1106635 : Blo 1104625 1106635 := bstep (se 1 (by rfl) ⟨829976, by rfl⟩ : syracuseStep 1106635 = 1659953) B1659953
theorem B1106647 : Blo 1104625 1106647 := bstep (se 1 (by rfl) ⟨829985, by rfl⟩ : syracuseStep 1106647 = 1659971) B1659971
theorem B1106667 : Blo 1104625 1106667 := bstep (se 1 (by rfl) ⟨830000, by rfl⟩ : syracuseStep 1106667 = 1660001) B1660001
theorem B1106679 : Blo 1104625 1106679 := bstep (se 1 (by rfl) ⟨830009, by rfl⟩ : syracuseStep 1106679 = 1660019) B1660019
theorem B1106699 : Blo 1104625 1106699 := bstep (se 1 (by rfl) ⟨830024, by rfl⟩ : syracuseStep 1106699 = 1660049) B1660049
theorem B1106711 : Blo 1104625 1106711 := bstep (se 1 (by rfl) ⟨830033, by rfl⟩ : syracuseStep 1106711 = 1660067) B1660067
theorem B1106731 : Blo 1104625 1106731 := bstep (se 1 (by rfl) ⟨830048, by rfl⟩ : syracuseStep 1106731 = 1660097) B1660097
theorem B1106743 : Blo 1104625 1106743 := bstep (se 1 (by rfl) ⟨830057, by rfl⟩ : syracuseStep 1106743 = 1660115) B1660115
theorem B1106763 : Blo 1104625 1106763 := bstep (se 1 (by rfl) ⟨830072, by rfl⟩ : syracuseStep 1106763 = 1660145) B1660145
theorem B1106775 : Blo 1104625 1106775 := bstep (se 1 (by rfl) ⟨830081, by rfl⟩ : syracuseStep 1106775 = 1660163) B1660163
theorem B28369763 : Blo 1104625 28369763 := bstep (se 1 (by rfl) ⟨21277322, by rfl⟩ : syracuseStep 28369763 = 42554645) B42554645
theorem B1106795 : Blo 1104625 1106795 := bstep (se 1 (by rfl) ⟨830096, by rfl⟩ : syracuseStep 1106795 = 1660193) B1660193
theorem B1106807 : Blo 1104625 1106807 := bstep (se 1 (by rfl) ⟨830105, by rfl⟩ : syracuseStep 1106807 = 1660211) B1660211
theorem B1106827 : Blo 1104625 1106827 := bstep (se 1 (by rfl) ⟨830120, by rfl⟩ : syracuseStep 1106827 = 1660241) B1660241
theorem B1106839 : Blo 1104625 1106839 := bstep (se 1 (by rfl) ⟨830129, by rfl⟩ : syracuseStep 1106839 = 1660259) B1660259
theorem B1106859 : Blo 1104625 1106859 := bstep (se 1 (by rfl) ⟨830144, by rfl⟩ : syracuseStep 1106859 = 1660289) B1660289
theorem B1106871 : Blo 1104625 1106871 := bstep (se 1 (by rfl) ⟨830153, by rfl⟩ : syracuseStep 1106871 = 1660307) B1660307
theorem B3728321 : Blo 1104625 3728321 := bstep (se 2 (by rfl) ⟨1398120, by rfl⟩ : syracuseStep 3728321 = 2796241) B2796241
theorem B1106891 : Blo 1104625 1106891 := bstep (se 1 (by rfl) ⟨830168, by rfl⟩ : syracuseStep 1106891 = 1660337) B1660337
theorem B1106903 : Blo 1104625 1106903 := bstep (se 1 (by rfl) ⟨830177, by rfl⟩ : syracuseStep 1106903 = 1660355) B1660355
theorem B1106923 : Blo 1104625 1106923 := bstep (se 1 (by rfl) ⟨830192, by rfl⟩ : syracuseStep 1106923 = 1660385) B1660385
theorem B1106935 : Blo 1104625 1106935 := bstep (se 1 (by rfl) ⟨830201, by rfl⟩ : syracuseStep 1106935 = 1660403) B1660403
theorem B1106955 : Blo 1104625 1106955 := bstep (se 1 (by rfl) ⟨830216, by rfl⟩ : syracuseStep 1106955 = 1660433) B1660433
theorem B1106967 : Blo 1104625 1106967 := bstep (se 1 (by rfl) ⟨830225, by rfl⟩ : syracuseStep 1106967 = 1660451) B1660451
theorem B1106987 : Blo 1104625 1106987 := bstep (se 1 (by rfl) ⟨830240, by rfl⟩ : syracuseStep 1106987 = 1660481) B1660481
theorem B1106999 : Blo 1104625 1106999 := bstep (se 1 (by rfl) ⟨830249, by rfl⟩ : syracuseStep 1106999 = 1660499) B1660499
theorem B1107019 : Blo 1104625 1107019 := bstep (se 1 (by rfl) ⟨830264, by rfl⟩ : syracuseStep 1107019 = 1660529) B1660529
theorem B1107031 : Blo 1104625 1107031 := bstep (se 1 (by rfl) ⟨830273, by rfl⟩ : syracuseStep 1107031 = 1660547) B1660547
theorem B1401943 : Blo 1104625 1401943 := bstep (se 1 (by rfl) ⟨1051457, by rfl⟩ : syracuseStep 1401943 = 2102915) B2102915
theorem B1107051 : Blo 1104625 1107051 := bstep (se 1 (by rfl) ⟨830288, by rfl⟩ : syracuseStep 1107051 = 1660577) B1660577
theorem B1107063 : Blo 1104625 1107063 := bstep (se 1 (by rfl) ⟨830297, by rfl⟩ : syracuseStep 1107063 = 1660595) B1660595
theorem B1107083 : Blo 1104625 1107083 := bstep (se 1 (by rfl) ⟨830312, by rfl⟩ : syracuseStep 1107083 = 1660625) B1660625
theorem B1107095 : Blo 1104625 1107095 := bstep (se 1 (by rfl) ⟨830321, by rfl⟩ : syracuseStep 1107095 = 1660643) B1660643
theorem B1107115 : Blo 1104625 1107115 := bstep (se 1 (by rfl) ⟨830336, by rfl⟩ : syracuseStep 1107115 = 1660673) B1660673
theorem B1107127 : Blo 1104625 1107127 := bstep (se 1 (by rfl) ⟨830345, by rfl⟩ : syracuseStep 1107127 = 1660691) B1660691
theorem B1107147 : Blo 1104625 1107147 := bstep (se 1 (by rfl) ⟨830360, by rfl⟩ : syracuseStep 1107147 = 1660721) B1660721
theorem B1107159 : Blo 1104625 1107159 := bstep (se 1 (by rfl) ⟨830369, by rfl⟩ : syracuseStep 1107159 = 1660739) B1660739
theorem B1107179 : Blo 1104625 1107179 := bstep (se 1 (by rfl) ⟨830384, by rfl⟩ : syracuseStep 1107179 = 1660769) B1660769
theorem B1107191 : Blo 1104625 1107191 := bstep (se 1 (by rfl) ⟨830393, by rfl⟩ : syracuseStep 1107191 = 1660787) B1660787
theorem B1107211 : Blo 1104625 1107211 := bstep (se 1 (by rfl) ⟨830408, by rfl⟩ : syracuseStep 1107211 = 1660817) B1660817
theorem B1107223 : Blo 1104625 1107223 := bstep (se 1 (by rfl) ⟨830417, by rfl⟩ : syracuseStep 1107223 = 1660835) B1660835
theorem B1107243 : Blo 1104625 1107243 := bstep (se 1 (by rfl) ⟨830432, by rfl⟩ : syracuseStep 1107243 = 1660865) B1660865
theorem B1107255 : Blo 1104625 1107255 := bstep (se 1 (by rfl) ⟨830441, by rfl⟩ : syracuseStep 1107255 = 1660883) B1660883
theorem B1107275 : Blo 1104625 1107275 := bstep (se 1 (by rfl) ⟨830456, by rfl⟩ : syracuseStep 1107275 = 1660913) B1660913
theorem B1107287 : Blo 1104625 1107287 := bstep (se 1 (by rfl) ⟨830465, by rfl⟩ : syracuseStep 1107287 = 1660931) B1660931
theorem B1107307 : Blo 1104625 1107307 := bstep (se 1 (by rfl) ⟨830480, by rfl⟩ : syracuseStep 1107307 = 1660961) B1660961
theorem B1107319 : Blo 1104625 1107319 := bstep (se 1 (by rfl) ⟨830489, by rfl⟩ : syracuseStep 1107319 = 1660979) B1660979
theorem B1107339 : Blo 1104625 1107339 := bstep (se 1 (by rfl) ⟨830504, by rfl⟩ : syracuseStep 1107339 = 1661009) B1661009
theorem B1107351 : Blo 1104625 1107351 := bstep (se 1 (by rfl) ⟨830513, by rfl⟩ : syracuseStep 1107351 = 1661027) B1661027
theorem B1107371 : Blo 1104625 1107371 := bstep (se 1 (by rfl) ⟨830528, by rfl⟩ : syracuseStep 1107371 = 1661057) B1661057
theorem B1107383 : Blo 1104625 1107383 := bstep (se 1 (by rfl) ⟨830537, by rfl⟩ : syracuseStep 1107383 = 1661075) B1661075
theorem B1107403 : Blo 1104625 1107403 := bstep (se 1 (by rfl) ⟨830552, by rfl⟩ : syracuseStep 1107403 = 1661105) B1661105
theorem B1107415 : Blo 1104625 1107415 := bstep (se 1 (by rfl) ⟨830561, by rfl⟩ : syracuseStep 1107415 = 1661123) B1661123
theorem B3728861 : Blo 1104625 3728861 := bstep (se 3 (by rfl) ⟨699161, by rfl⟩ : syracuseStep 3728861 = 1398323) B1398323
theorem B1107435 : Blo 1104625 1107435 := bstep (se 1 (by rfl) ⟨830576, by rfl⟩ : syracuseStep 1107435 = 1661153) B1661153
theorem B1107447 : Blo 1104625 1107447 := bstep (se 1 (by rfl) ⟨830585, by rfl⟩ : syracuseStep 1107447 = 1661171) B1661171
theorem B1107467 : Blo 1104625 1107467 := bstep (se 1 (by rfl) ⟨830600, by rfl⟩ : syracuseStep 1107467 = 1661201) B1661201
theorem B1107479 : Blo 1104625 1107479 := bstep (se 1 (by rfl) ⟨830609, by rfl⟩ : syracuseStep 1107479 = 1661219) B1661219
theorem B1107499 : Blo 1104625 1107499 := bstep (se 1 (by rfl) ⟨830624, by rfl⟩ : syracuseStep 1107499 = 1661249) B1661249
theorem B1107511 : Blo 1104625 1107511 := bstep (se 1 (by rfl) ⟨830633, by rfl⟩ : syracuseStep 1107511 = 1661267) B1661267
theorem B1107531 : Blo 1104625 1107531 := bstep (se 1 (by rfl) ⟨830648, by rfl⟩ : syracuseStep 1107531 = 1661297) B1661297
theorem B1107543 : Blo 1104625 1107543 := bstep (se 1 (by rfl) ⟨830657, by rfl⟩ : syracuseStep 1107543 = 1661315) B1661315
theorem B1107563 : Blo 1104625 1107563 := bstep (se 1 (by rfl) ⟨830672, by rfl⟩ : syracuseStep 1107563 = 1661345) B1661345
theorem B1107575 : Blo 1104625 1107575 := bstep (se 1 (by rfl) ⟨830681, by rfl⟩ : syracuseStep 1107575 = 1661363) B1661363
theorem B1107595 : Blo 1104625 1107595 := bstep (se 1 (by rfl) ⟨830696, by rfl⟩ : syracuseStep 1107595 = 1661393) B1661393
theorem B1107607 : Blo 1104625 1107607 := bstep (se 1 (by rfl) ⟨830705, by rfl⟩ : syracuseStep 1107607 = 1661411) B1661411
theorem B1107627 : Blo 1104625 1107627 := bstep (se 1 (by rfl) ⟨830720, by rfl⟩ : syracuseStep 1107627 = 1661441) B1661441
theorem B1107639 : Blo 1104625 1107639 := bstep (se 1 (by rfl) ⟨830729, by rfl⟩ : syracuseStep 1107639 = 1661459) B1661459
theorem B1107659 : Blo 1104625 1107659 := bstep (se 1 (by rfl) ⟨830744, by rfl⟩ : syracuseStep 1107659 = 1661489) B1661489
theorem B1107671 : Blo 1104625 1107671 := bstep (se 1 (by rfl) ⟨830753, by rfl⟩ : syracuseStep 1107671 = 1661507) B1661507
theorem B1107691 : Blo 1104625 1107691 := bstep (se 1 (by rfl) ⟨830768, by rfl⟩ : syracuseStep 1107691 = 1661537) B1661537
theorem B1107703 : Blo 1104625 1107703 := bstep (se 1 (by rfl) ⟨830777, by rfl⟩ : syracuseStep 1107703 = 1661555) B1661555
theorem B1107723 : Blo 1104625 1107723 := bstep (se 1 (by rfl) ⟨830792, by rfl⟩ : syracuseStep 1107723 = 1661585) B1661585
theorem B1107735 : Blo 1104625 1107735 := bstep (se 1 (by rfl) ⟨830801, by rfl⟩ : syracuseStep 1107735 = 1661603) B1661603
theorem B1107755 : Blo 1104625 1107755 := bstep (se 1 (by rfl) ⟨830816, by rfl⟩ : syracuseStep 1107755 = 1661633) B1661633
theorem B1107767 : Blo 1104625 1107767 := bstep (se 1 (by rfl) ⟨830825, by rfl⟩ : syracuseStep 1107767 = 1661651) B1661651
theorem B1107787 : Blo 1104625 1107787 := bstep (se 1 (by rfl) ⟨830840, by rfl⟩ : syracuseStep 1107787 = 1661681) B1661681
theorem B1107799 : Blo 1104625 1107799 := bstep (se 1 (by rfl) ⟨830849, by rfl⟩ : syracuseStep 1107799 = 1661699) B1661699
theorem B1107819 : Blo 1104625 1107819 := bstep (se 1 (by rfl) ⟨830864, by rfl⟩ : syracuseStep 1107819 = 1661729) B1661729
theorem B1107831 : Blo 1104625 1107831 := bstep (se 1 (by rfl) ⟨830873, by rfl⟩ : syracuseStep 1107831 = 1661747) B1661747
theorem B1107851 : Blo 1104625 1107851 := bstep (se 1 (by rfl) ⟨830888, by rfl⟩ : syracuseStep 1107851 = 1661777) B1661777
theorem B1107863 : Blo 1104625 1107863 := bstep (se 1 (by rfl) ⟨830897, by rfl⟩ : syracuseStep 1107863 = 1661795) B1661795
theorem B1107883 : Blo 1104625 1107883 := bstep (se 1 (by rfl) ⟨830912, by rfl⟩ : syracuseStep 1107883 = 1661825) B1661825
theorem B1107895 : Blo 1104625 1107895 := bstep (se 1 (by rfl) ⟨830921, by rfl⟩ : syracuseStep 1107895 = 1661843) B1661843
theorem B1107915 : Blo 1104625 1107915 := bstep (se 1 (by rfl) ⟨830936, by rfl⟩ : syracuseStep 1107915 = 1661873) B1661873
theorem B1107927 : Blo 1104625 1107927 := bstep (se 1 (by rfl) ⟨830945, by rfl⟩ : syracuseStep 1107927 = 1661891) B1661891
theorem B1107947 : Blo 1104625 1107947 := bstep (se 1 (by rfl) ⟨830960, by rfl⟩ : syracuseStep 1107947 = 1661921) B1661921
theorem B1107959 : Blo 1104625 1107959 := bstep (se 1 (by rfl) ⟨830969, by rfl⟩ : syracuseStep 1107959 = 1661939) B1661939
theorem B1107979 : Blo 1104625 1107979 := bstep (se 1 (by rfl) ⟨830984, by rfl⟩ : syracuseStep 1107979 = 1661969) B1661969
theorem B1107991 : Blo 1104625 1107991 := bstep (se 1 (by rfl) ⟨830993, by rfl⟩ : syracuseStep 1107991 = 1661987) B1661987
theorem B1108011 : Blo 1104625 1108011 := bstep (se 1 (by rfl) ⟨831008, by rfl⟩ : syracuseStep 1108011 = 1662017) B1662017
theorem B1108023 : Blo 1104625 1108023 := bstep (se 1 (by rfl) ⟨831017, by rfl⟩ : syracuseStep 1108023 = 1662035) B1662035
theorem B1108043 : Blo 1104625 1108043 := bstep (se 1 (by rfl) ⟨831032, by rfl⟩ : syracuseStep 1108043 = 1662065) B1662065
theorem B1108055 : Blo 1104625 1108055 := bstep (se 1 (by rfl) ⟨831041, by rfl⟩ : syracuseStep 1108055 = 1662083) B1662083
theorem B1108075 : Blo 1104625 1108075 := bstep (se 1 (by rfl) ⟨831056, by rfl⟩ : syracuseStep 1108075 = 1662113) B1662113
theorem B1108087 : Blo 1104625 1108087 := bstep (se 1 (by rfl) ⟨831065, by rfl⟩ : syracuseStep 1108087 = 1662131) B1662131
theorem B1108107 : Blo 1104625 1108107 := bstep (se 1 (by rfl) ⟨831080, by rfl⟩ : syracuseStep 1108107 = 1662161) B1662161
theorem B1108119 : Blo 1104625 1108119 := bstep (se 1 (by rfl) ⟨831089, by rfl⟩ : syracuseStep 1108119 = 1662179) B1662179
theorem B1108139 : Blo 1104625 1108139 := bstep (se 1 (by rfl) ⟨831104, by rfl⟩ : syracuseStep 1108139 = 1662209) B1662209
theorem B1108151 : Blo 1104625 1108151 := bstep (se 1 (by rfl) ⟨831113, by rfl⟩ : syracuseStep 1108151 = 1662227) B1662227
theorem B1108171 : Blo 1104625 1108171 := bstep (se 1 (by rfl) ⟨831128, by rfl⟩ : syracuseStep 1108171 = 1662257) B1662257
theorem B1108183 : Blo 1104625 1108183 := bstep (se 1 (by rfl) ⟨831137, by rfl⟩ : syracuseStep 1108183 = 1662275) B1662275
theorem B1108203 : Blo 1104625 1108203 := bstep (se 1 (by rfl) ⟨831152, by rfl⟩ : syracuseStep 1108203 = 1662305) B1662305
theorem B1108215 : Blo 1104625 1108215 := bstep (se 1 (by rfl) ⟨831161, by rfl⟩ : syracuseStep 1108215 = 1662323) B1662323
theorem B1108235 : Blo 1104625 1108235 := bstep (se 1 (by rfl) ⟨831176, by rfl⟩ : syracuseStep 1108235 = 1662353) B1662353
theorem B1108247 : Blo 1104625 1108247 := bstep (se 1 (by rfl) ⟨831185, by rfl⟩ : syracuseStep 1108247 = 1662371) B1662371
theorem B1108267 : Blo 1104625 1108267 := bstep (se 1 (by rfl) ⟨831200, by rfl⟩ : syracuseStep 1108267 = 1662401) B1662401
theorem B1108279 : Blo 1104625 1108279 := bstep (se 1 (by rfl) ⟨831209, by rfl⟩ : syracuseStep 1108279 = 1662419) B1662419
theorem B1108299 : Blo 1104625 1108299 := bstep (se 1 (by rfl) ⟨831224, by rfl⟩ : syracuseStep 1108299 = 1662449) B1662449
theorem B1108311 : Blo 1104625 1108311 := bstep (se 1 (by rfl) ⟨831233, by rfl⟩ : syracuseStep 1108311 = 1662467) B1662467
theorem B1108331 : Blo 1104625 1108331 := bstep (se 1 (by rfl) ⟨831248, by rfl⟩ : syracuseStep 1108331 = 1662497) B1662497
theorem B60615029 : Blo 1104625 60615029 := bstep (se 5 (by rfl) ⟨2841329, by rfl⟩ : syracuseStep 60615029 = 5682659) B5682659
theorem B1108343 : Blo 1104625 1108343 := bstep (se 1 (by rfl) ⟨831257, by rfl⟩ : syracuseStep 1108343 = 1662515) B1662515
theorem B1108363 : Blo 1104625 1108363 := bstep (se 1 (by rfl) ⟨831272, by rfl⟩ : syracuseStep 1108363 = 1662545) B1662545
theorem B1108375 : Blo 1104625 1108375 := bstep (se 1 (by rfl) ⟨831281, by rfl⟩ : syracuseStep 1108375 = 1662563) B1662563
theorem B1108395 : Blo 1104625 1108395 := bstep (se 1 (by rfl) ⟨831296, by rfl⟩ : syracuseStep 1108395 = 1662593) B1662593
theorem B1108407 : Blo 1104625 1108407 := bstep (se 1 (by rfl) ⟨831305, by rfl⟩ : syracuseStep 1108407 = 1662611) B1662611
theorem B1108427 : Blo 1104625 1108427 := bstep (se 1 (by rfl) ⟨831320, by rfl⟩ : syracuseStep 1108427 = 1662641) B1662641
theorem B1108439 : Blo 1104625 1108439 := bstep (se 1 (by rfl) ⟨831329, by rfl⟩ : syracuseStep 1108439 = 1662659) B1662659
theorem B1108459 : Blo 1104625 1108459 := bstep (se 1 (by rfl) ⟨831344, by rfl⟩ : syracuseStep 1108459 = 1662689) B1662689
theorem B1108471 : Blo 1104625 1108471 := bstep (se 1 (by rfl) ⟨831353, by rfl⟩ : syracuseStep 1108471 = 1662707) B1662707
theorem B1108491 : Blo 1104625 1108491 := bstep (se 1 (by rfl) ⟨831368, by rfl⟩ : syracuseStep 1108491 = 1662737) B1662737
theorem B1108503 : Blo 1104625 1108503 := bstep (se 1 (by rfl) ⟨831377, by rfl⟩ : syracuseStep 1108503 = 1662755) B1662755
theorem B1108523 : Blo 1104625 1108523 := bstep (se 1 (by rfl) ⟨831392, by rfl⟩ : syracuseStep 1108523 = 1662785) B1662785
theorem B1108535 : Blo 1104625 1108535 := bstep (se 1 (by rfl) ⟨831401, by rfl⟩ : syracuseStep 1108535 = 1662803) B1662803
theorem B3729995 : Blo 1104625 3729995 := bstep (se 1 (by rfl) ⟨2797496, by rfl⟩ : syracuseStep 3729995 = 5594993) B5594993
theorem B1108555 : Blo 1104625 1108555 := bstep (se 1 (by rfl) ⟨831416, by rfl⟩ : syracuseStep 1108555 = 1662833) B1662833
theorem B1108567 : Blo 1104625 1108567 := bstep (se 1 (by rfl) ⟨831425, by rfl⟩ : syracuseStep 1108567 = 1662851) B1662851
theorem B1108587 : Blo 1104625 1108587 := bstep (se 1 (by rfl) ⟨831440, by rfl⟩ : syracuseStep 1108587 = 1662881) B1662881
theorem B1108599 : Blo 1104625 1108599 := bstep (se 1 (by rfl) ⟨831449, by rfl⟩ : syracuseStep 1108599 = 1662899) B1662899
theorem B1108619 : Blo 1104625 1108619 := bstep (se 1 (by rfl) ⟨831464, by rfl⟩ : syracuseStep 1108619 = 1662929) B1662929
theorem B3730265 : Blo 1104625 3730265 := bstep (se 2 (by rfl) ⟨1398849, by rfl⟩ : syracuseStep 3730265 = 2797699) B2797699
theorem B18935045 : Blo 1104625 18935045 := bstep (se 4 (by rfl) ⟨1775160, by rfl⟩ : syracuseStep 18935045 = 3550321) B3550321
theorem B2485529 : Blo 1104625 2485529 := bstep (se 2 (by rfl) ⟨932073, by rfl⟩ : syracuseStep 2485529 = 1864147) B1864147
theorem B8416547 : Blo 1104625 8416547 := bstep (se 1 (by rfl) ⟨6312410, by rfl⟩ : syracuseStep 8416547 = 12624821) B12624821
theorem B5598557 : Blo 1104625 5598557 := bstep (se 3 (by rfl) ⟨1049729, by rfl⟩ : syracuseStep 5598557 = 2099459) B2099459
theorem B2485619 : Blo 1104625 2485619 := bstep (se 1 (by rfl) ⟨1864214, by rfl⟩ : syracuseStep 2485619 = 3728429) B3728429
theorem B2485655 : Blo 1104625 2485655 := bstep (se 1 (by rfl) ⟨1864241, by rfl⟩ : syracuseStep 2485655 = 3728483) B3728483
theorem B4484555 : Blo 1104625 4484555 := bstep (se 1 (by rfl) ⟨3363416, by rfl⟩ : syracuseStep 4484555 = 6726833) B6726833
theorem B3730967 : Blo 1104625 3730967 := bstep (se 1 (by rfl) ⟨2798225, by rfl⟩ : syracuseStep 3730967 = 5596451) B5596451
theorem B2485835 : Blo 1104625 2485835 := bstep (se 1 (by rfl) ⟨1864376, by rfl⟩ : syracuseStep 2485835 = 3728753) B3728753
theorem B4484683 : Blo 1104625 4484683 := bstep (se 1 (by rfl) ⟨3363512, by rfl⟩ : syracuseStep 4484683 = 6727025) B6727025
theorem B2485889 : Blo 1104625 2485889 := bstep (se 2 (by rfl) ⟨932208, by rfl⟩ : syracuseStep 2485889 = 1864417) B1864417
theorem B1994419 : Blo 1104625 1994419 := bstep (se 1 (by rfl) ⟨1495814, by rfl⟩ : syracuseStep 1994419 = 2991629) B2991629
theorem B1994519 : Blo 1104625 1994519 := bstep (se 1 (by rfl) ⟨1495889, by rfl⟩ : syracuseStep 1994519 = 2991779) B2991779
theorem B2486105 : Blo 1104625 2486105 := bstep (se 2 (by rfl) ⟨932289, by rfl⟩ : syracuseStep 2486105 = 1864579) B1864579
theorem B2486195 : Blo 1104625 2486195 := bstep (se 1 (by rfl) ⟨1864646, by rfl⟩ : syracuseStep 2486195 = 3729293) B3729293
theorem B4550593 : Blo 1104625 4550593 := bstep (se 2 (by rfl) ⟨1706472, by rfl⟩ : syracuseStep 4550593 = 3412945) B3412945
theorem B2486231 : Blo 1104625 2486231 := bstep (se 1 (by rfl) ⟨1864673, by rfl⟩ : syracuseStep 2486231 = 3729347) B3729347
theorem B3993565 : Blo 1104625 3993565 := bstep (se 3 (by rfl) ⟨748793, by rfl⟩ : syracuseStep 3993565 = 1497587) B1497587
theorem B3731507 : Blo 1104625 3731507 := bstep (se 1 (by rfl) ⟨2798630, by rfl⟩ : syracuseStep 3731507 = 5597261) B5597261
theorem B1994881 : Blo 1104625 1994881 := bstep (se 2 (by rfl) ⟨748080, by rfl⟩ : syracuseStep 1994881 = 1496161) B1496161
theorem B2486411 : Blo 1104625 2486411 := bstep (se 1 (by rfl) ⟨1864808, by rfl⟩ : syracuseStep 2486411 = 3729617) B3729617
theorem B2486465 : Blo 1104625 2486465 := bstep (se 2 (by rfl) ⟨932424, by rfl⟩ : syracuseStep 2486465 = 1864849) B1864849
theorem B3731777 : Blo 1104625 3731777 := bstep (se 2 (by rfl) ⟨1399416, by rfl⟩ : syracuseStep 3731777 = 2798833) B2798833
theorem B2486681 : Blo 1104625 2486681 := bstep (se 2 (by rfl) ⟨932505, by rfl⟩ : syracuseStep 2486681 = 1865011) B1865011
theorem B2486771 : Blo 1104625 2486771 := bstep (se 1 (by rfl) ⟨1865078, by rfl⟩ : syracuseStep 2486771 = 3730157) B3730157
theorem B2486807 : Blo 1104625 2486807 := bstep (se 1 (by rfl) ⟨1865105, by rfl⟩ : syracuseStep 2486807 = 3730211) B3730211
theorem B1864343 : Blo 1104625 1864343 := bstep (se 1 (by rfl) ⟨1398257, by rfl⟩ : syracuseStep 1864343 = 2796515) B2796515
theorem B2486987 : Blo 1104625 2486987 := bstep (se 1 (by rfl) ⟨1865240, by rfl⟩ : syracuseStep 2486987 = 3730481) B3730481
theorem B2487041 : Blo 1104625 2487041 := bstep (se 2 (by rfl) ⟨932640, by rfl⟩ : syracuseStep 2487041 = 1865281) B1865281
theorem B1864471 : Blo 1104625 1864471 := bstep (se 1 (by rfl) ⟨1398353, by rfl⟩ : syracuseStep 1864471 = 2796707) B2796707
theorem B7566155 : Blo 1104625 7566155 := bstep (se 1 (by rfl) ⟨5674616, by rfl⟩ : syracuseStep 7566155 = 11349233) B11349233
theorem B3732317 : Blo 1104625 3732317 := bstep (se 3 (by rfl) ⟨699809, by rfl⟩ : syracuseStep 3732317 = 1399619) B1399619
theorem B2487257 : Blo 1104625 2487257 := bstep (se 2 (by rfl) ⟨932721, by rfl⟩ : syracuseStep 2487257 = 1865443) B1865443
theorem B2487347 : Blo 1104625 2487347 := bstep (se 1 (by rfl) ⟨1865510, by rfl⟩ : syracuseStep 2487347 = 3731021) B3731021
theorem B2487383 : Blo 1104625 2487383 := bstep (se 1 (by rfl) ⟨1865537, by rfl⟩ : syracuseStep 2487383 = 3731075) B3731075
theorem B2487563 : Blo 1104625 2487563 := bstep (se 1 (by rfl) ⟨1865672, by rfl⟩ : syracuseStep 2487563 = 3731345) B3731345
theorem B2487617 : Blo 1104625 2487617 := bstep (se 2 (by rfl) ⟨932856, by rfl⟩ : syracuseStep 2487617 = 1865713) B1865713
theorem B13464949 : Blo 1104625 13464949 := bstep (se 5 (by rfl) ⟨631169, by rfl⟩ : syracuseStep 13464949 = 1262339) B1262339
theorem B1865099 : Blo 1104625 1865099 := bstep (se 1 (by rfl) ⟨1398824, by rfl⟩ : syracuseStep 1865099 = 2797649) B2797649
theorem B5600663 : Blo 1104625 5600663 := bstep (se 1 (by rfl) ⟨4200497, by rfl⟩ : syracuseStep 5600663 = 8400995) B8400995
theorem B4617623 : Blo 1104625 4617623 := bstep (se 1 (by rfl) ⟨3463217, by rfl⟩ : syracuseStep 4617623 = 6926435) B6926435
theorem B4257197 : Blo 1104625 4257197 := bstep (se 3 (by rfl) ⟨798224, by rfl⟩ : syracuseStep 4257197 = 1596449) B1596449
theorem B1865227 : Blo 1104625 1865227 := bstep (se 1 (by rfl) ⟨1398920, by rfl⟩ : syracuseStep 1865227 = 2797841) B2797841
theorem B2487833 : Blo 1104625 2487833 := bstep (se 2 (by rfl) ⟨932937, by rfl⟩ : syracuseStep 2487833 = 1865875) B1865875
theorem B4486745 : Blo 1104625 4486745 := bstep (se 2 (by rfl) ⟨1682529, by rfl⟩ : syracuseStep 4486745 = 3365059) B3365059
theorem B2487923 : Blo 1104625 2487923 := bstep (se 1 (by rfl) ⟨1865942, by rfl⟩ : syracuseStep 2487923 = 3731885) B3731885
theorem B2487959 : Blo 1104625 2487959 := bstep (se 1 (by rfl) ⟨1865969, by rfl⟩ : syracuseStep 2487959 = 3731939) B3731939
theorem B1865369 : Blo 1104625 1865369 := bstep (se 2 (by rfl) ⟨699513, by rfl⟩ : syracuseStep 1865369 = 1399027) B1399027
theorem B1242859 : Blo 1104625 1242859 := bstep (se 1 (by rfl) ⟨932144, by rfl⟩ : syracuseStep 1242859 = 1864289) B1864289
theorem B1865497 : Blo 1104625 1865497 := bstep (se 2 (by rfl) ⟨699561, by rfl⟩ : syracuseStep 1865497 = 1399123) B1399123
theorem B2160449 : Blo 1104625 2160449 := bstep (se 2 (by rfl) ⟨810168, by rfl⟩ : syracuseStep 2160449 = 1620337) B1620337
theorem B2488139 : Blo 1104625 2488139 := bstep (se 1 (by rfl) ⟨1866104, by rfl⟩ : syracuseStep 2488139 = 3732209) B3732209
theorem B1242967 : Blo 1104625 1242967 := bstep (se 1 (by rfl) ⟨932225, by rfl⟩ : syracuseStep 1242967 = 1864451) B1864451
theorem B2488193 : Blo 1104625 2488193 := bstep (se 2 (by rfl) ⟨933072, by rfl⟩ : syracuseStep 2488193 = 1866145) B1866145
theorem B3733451 : Blo 1104625 3733451 := bstep (se 1 (by rfl) ⟨2800088, by rfl⟩ : syracuseStep 3733451 = 5600177) B5600177
theorem B1243147 : Blo 1104625 1243147 := bstep (se 1 (by rfl) ⟨932360, by rfl⟩ : syracuseStep 1243147 = 1864721) B1864721
theorem B3110987 : Blo 1104625 3110987 := bstep (se 1 (by rfl) ⟨2333240, by rfl⟩ : syracuseStep 3110987 = 4666481) B4666481
theorem B2488409 : Blo 1104625 2488409 := bstep (se 2 (by rfl) ⟨933153, by rfl⟩ : syracuseStep 2488409 = 1866307) B1866307
theorem B1243255 : Blo 1104625 1243255 := bstep (se 1 (by rfl) ⟨932441, by rfl⟩ : syracuseStep 1243255 = 1864883) B1864883
theorem B2488499 : Blo 1104625 2488499 := bstep (se 1 (by rfl) ⟨1866374, by rfl⟩ : syracuseStep 2488499 = 3732749) B3732749
theorem B2488535 : Blo 1104625 2488535 := bstep (se 1 (by rfl) ⟨1866401, by rfl⟩ : syracuseStep 2488535 = 3732803) B3732803
theorem B7567577 : Blo 1104625 7567577 := bstep (se 2 (by rfl) ⟨2837841, by rfl⟩ : syracuseStep 7567577 = 5675683) B5675683
theorem B3733721 : Blo 1104625 3733721 := bstep (se 2 (by rfl) ⟨1400145, by rfl⟩ : syracuseStep 3733721 = 2800291) B2800291
theorem B16152817 : Blo 1104625 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B1243435 : Blo 1104625 1243435 := bstep (se 1 (by rfl) ⟨932576, by rfl⟩ : syracuseStep 1243435 = 1865153) B1865153
theorem B1866071 : Blo 1104625 1866071 := bstep (se 1 (by rfl) ⟨1399553, by rfl⟩ : syracuseStep 1866071 = 2799107) B2799107
theorem B2521459 : Blo 1104625 2521459 := bstep (se 1 (by rfl) ⟨1891094, by rfl⟩ : syracuseStep 2521459 = 3782189) B3782189
theorem B2488715 : Blo 1104625 2488715 := bstep (se 1 (by rfl) ⟨1866536, by rfl⟩ : syracuseStep 2488715 = 3733073) B3733073
theorem B1243543 : Blo 1104625 1243543 := bstep (se 1 (by rfl) ⟨932657, by rfl⟩ : syracuseStep 1243543 = 1865315) B1865315
theorem B2488769 : Blo 1104625 2488769 := bstep (se 2 (by rfl) ⟨933288, by rfl⟩ : syracuseStep 2488769 = 1866577) B1866577
theorem B1866199 : Blo 1104625 1866199 := bstep (se 1 (by rfl) ⟨1399649, by rfl⟩ : syracuseStep 1866199 = 2799299) B2799299
theorem B1243723 : Blo 1104625 1243723 := bstep (se 1 (by rfl) ⟨932792, by rfl⟩ : syracuseStep 1243723 = 1865585) B1865585
theorem B2488985 : Blo 1104625 2488985 := bstep (se 2 (by rfl) ⟨933369, by rfl⟩ : syracuseStep 2488985 = 1866739) B1866739
theorem B1243831 : Blo 1104625 1243831 := bstep (se 1 (by rfl) ⟨932873, by rfl⟩ : syracuseStep 1243831 = 1865747) B1865747
theorem B2489075 : Blo 1104625 2489075 := bstep (se 1 (by rfl) ⟨1866806, by rfl⟩ : syracuseStep 2489075 = 3733613) B3733613
theorem B2489111 : Blo 1104625 2489111 := bstep (se 1 (by rfl) ⟨1866833, by rfl⟩ : syracuseStep 2489111 = 3733667) B3733667
theorem B31882085 : Blo 1104625 31882085 := bstep (se 4 (by rfl) ⟨2988945, by rfl⟩ : syracuseStep 31882085 = 5977891) B5977891
theorem B1244011 : Blo 1104625 1244011 := bstep (se 1 (by rfl) ⟨933008, by rfl⟩ : syracuseStep 1244011 = 1866017) B1866017
theorem B3734423 : Blo 1104625 3734423 := bstep (se 1 (by rfl) ⟨2800817, by rfl⟩ : syracuseStep 3734423 = 5601635) B5601635
theorem B2489291 : Blo 1104625 2489291 := bstep (se 1 (by rfl) ⟨1866968, by rfl⟩ : syracuseStep 2489291 = 3733937) B3733937
theorem B1244119 : Blo 1104625 1244119 := bstep (se 1 (by rfl) ⟨933089, by rfl⟩ : syracuseStep 1244119 = 1866179) B1866179
theorem B2489345 : Blo 1104625 2489345 := bstep (se 2 (by rfl) ⟨933504, by rfl⟩ : syracuseStep 2489345 = 1867009) B1867009
theorem B1866827 : Blo 1104625 1866827 := bstep (se 1 (by rfl) ⟨1400120, by rfl⟩ : syracuseStep 1866827 = 2800241) B2800241
theorem B1244299 : Blo 1104625 1244299 := bstep (se 1 (by rfl) ⟨933224, by rfl⟩ : syracuseStep 1244299 = 1866449) B1866449
theorem B1866955 : Blo 1104625 1866955 := bstep (se 1 (by rfl) ⟨1400216, by rfl⟩ : syracuseStep 1866955 = 2800433) B2800433
theorem B2489561 : Blo 1104625 2489561 := bstep (se 2 (by rfl) ⟨933585, by rfl⟩ : syracuseStep 2489561 = 1867171) B1867171
theorem B1244407 : Blo 1104625 1244407 := bstep (se 1 (by rfl) ⟨933305, by rfl⟩ : syracuseStep 1244407 = 1866611) B1866611
theorem B2489651 : Blo 1104625 2489651 := bstep (se 1 (by rfl) ⟨1867238, by rfl⟩ : syracuseStep 2489651 = 3734477) B3734477
theorem B2489687 : Blo 1104625 2489687 := bstep (se 1 (by rfl) ⟨1867265, by rfl⟩ : syracuseStep 2489687 = 3734531) B3734531
theorem B1867097 : Blo 1104625 1867097 := bstep (se 2 (by rfl) ⟨700161, by rfl⟩ : syracuseStep 1867097 = 1400323) B1400323
theorem B1244587 : Blo 1104625 1244587 := bstep (se 1 (by rfl) ⟨933440, by rfl⟩ : syracuseStep 1244587 = 1866881) B1866881
theorem B3734963 : Blo 1104625 3734963 := bstep (se 1 (by rfl) ⟨2801222, by rfl⟩ : syracuseStep 3734963 = 5602445) B5602445
theorem B1867225 : Blo 1104625 1867225 := bstep (se 2 (by rfl) ⟨700209, by rfl⟩ : syracuseStep 1867225 = 1400419) B1400419
theorem B2489867 : Blo 1104625 2489867 := bstep (se 1 (by rfl) ⟨1867400, by rfl⟩ : syracuseStep 2489867 = 3734801) B3734801
theorem B1244695 : Blo 1104625 1244695 := bstep (se 1 (by rfl) ⟨933521, by rfl⟩ : syracuseStep 1244695 = 1867043) B1867043
theorem B2489921 : Blo 1104625 2489921 := bstep (se 2 (by rfl) ⟨933720, by rfl⟩ : syracuseStep 2489921 = 1867441) B1867441
theorem B3833419 : Blo 1104625 3833419 := bstep (se 1 (by rfl) ⟨2875064, by rfl⟩ : syracuseStep 3833419 = 5750129) B5750129
theorem B14155357 : Blo 1104625 14155357 := bstep (se 3 (by rfl) ⟨2654129, by rfl⟩ : syracuseStep 14155357 = 5308259) B5308259
theorem B11337367 : Blo 1104625 11337367 := bstep (se 1 (by rfl) ⟨8503025, by rfl⟩ : syracuseStep 11337367 = 17006051) B17006051
theorem B3735233 : Blo 1104625 3735233 := bstep (se 2 (by rfl) ⟨1400712, by rfl⟩ : syracuseStep 3735233 = 2801425) B2801425
theorem B1244875 : Blo 1104625 1244875 := bstep (se 1 (by rfl) ⟨933656, by rfl⟩ : syracuseStep 1244875 = 1867313) B1867313
theorem B1277675 : Blo 1104625 1277675 := bstep (se 1 (by rfl) ⟨958256, by rfl⟩ : syracuseStep 1277675 = 1916513) B1916513
theorem B2490137 : Blo 1104625 2490137 := bstep (se 2 (by rfl) ⟨933801, by rfl⟩ : syracuseStep 2490137 = 1867603) B1867603
theorem B1244983 : Blo 1104625 1244983 := bstep (se 1 (by rfl) ⟨933737, by rfl⟩ : syracuseStep 1244983 = 1867475) B1867475
theorem B2490227 : Blo 1104625 2490227 := bstep (se 1 (by rfl) ⟨1867670, by rfl⟩ : syracuseStep 2490227 = 3735341) B3735341
theorem B2490263 : Blo 1104625 2490263 := bstep (se 1 (by rfl) ⟨1867697, by rfl⟩ : syracuseStep 2490263 = 3735395) B3735395
theorem B2359219 : Blo 1104625 2359219 := bstep (se 1 (by rfl) ⟨1769414, by rfl⟩ : syracuseStep 2359219 = 3538829) B3538829
theorem B1245163 : Blo 1104625 1245163 := bstep (se 1 (by rfl) ⟨933872, by rfl⟩ : syracuseStep 1245163 = 1867745) B1867745
theorem B1245199 : Blo 1104625 1245199 := bstep (se 1 (by rfl) ⟨933899, by rfl⟩ : syracuseStep 1245199 = 1867799) B1867799
theorem B1867819 : Blo 1104625 1867819 := bstep (se 1 (by rfl) ⟨1400864, by rfl⟩ : syracuseStep 1867819 = 2801729) B2801729
theorem B2490515 : Blo 1104625 2490515 := bstep (se 1 (by rfl) ⟨1867886, by rfl⟩ : syracuseStep 2490515 = 3735773) B3735773
theorem B1867961 : Blo 1104625 1867961 := bstep (se 2 (by rfl) ⟨700485, by rfl⟩ : syracuseStep 1867961 = 1400971) B1400971
theorem B2490569 : Blo 1104625 2490569 := bstep (se 2 (by rfl) ⟨933963, by rfl⟩ : syracuseStep 2490569 = 1867927) B1867927
theorem B8388845 : Blo 1104625 8388845 := bstep (se 3 (by rfl) ⟨1572908, by rfl⟩ : syracuseStep 8388845 = 3145817) B3145817
theorem B4194575 : Blo 1104625 4194575 := bstep (se 1 (by rfl) ⟨3145931, by rfl⟩ : syracuseStep 4194575 = 6291863) B6291863
theorem B1573177 : Blo 1104625 1573177 := bstep (se 2 (by rfl) ⟨589941, by rfl⟩ : syracuseStep 1573177 = 1179883) B1179883
theorem B1245703 : Blo 1104625 1245703 := bstep (se 1 (by rfl) ⟨934277, by rfl⟩ : syracuseStep 1245703 = 1868555) B1868555
theorem B3146273 : Blo 1104625 3146273 := bstep (se 2 (by rfl) ⟨1179852, by rfl⟩ : syracuseStep 3146273 = 2359705) B2359705
theorem B3736151 : Blo 1104625 3736151 := bstep (se 1 (by rfl) ⟨2802113, by rfl⟩ : syracuseStep 3736151 = 5604227) B5604227
theorem B1245883 : Blo 1104625 1245883 := bstep (se 1 (by rfl) ⟨934412, by rfl⟩ : syracuseStep 1245883 = 1868825) B1868825
theorem B2360107 : Blo 1104625 2360107 := bstep (se 1 (by rfl) ⟨1770080, by rfl⟩ : syracuseStep 2360107 = 3540161) B3540161
theorem B21300083 : Blo 1104625 21300083 := bstep (se 1 (by rfl) ⟨15975062, by rfl⟩ : syracuseStep 21300083 = 31950125) B31950125
theorem B2360183 : Blo 1104625 2360183 := bstep (se 1 (by rfl) ⟨1770137, by rfl⟩ : syracuseStep 2360183 = 3540275) B3540275
theorem B1868663 : Blo 1104625 1868663 := bstep (se 1 (by rfl) ⟨1401497, by rfl⟩ : syracuseStep 1868663 = 2802995) B2802995
theorem B2098055 : Blo 1104625 2098055 := bstep (se 1 (by rfl) ⟨1573541, by rfl⟩ : syracuseStep 2098055 = 3147083) B3147083
theorem B2491271 : Blo 1104625 2491271 := bstep (se 1 (by rfl) ⟨1868453, by rfl⟩ : syracuseStep 2491271 = 3736907) B3736907
theorem B3408911 : Blo 1104625 3408911 := bstep (se 1 (by rfl) ⟨2556683, by rfl⟩ : syracuseStep 3408911 = 5113367) B5113367
theorem B2491451 : Blo 1104625 2491451 := bstep (se 1 (by rfl) ⟨1868588, by rfl⟩ : syracuseStep 2491451 = 3737177) B3737177
theorem B12583997 : Blo 1104625 12583997 := bstep (se 3 (by rfl) ⟨2359499, by rfl⟩ : syracuseStep 12583997 = 4718999) B4718999
theorem B3736637 : Blo 1104625 3736637 := bstep (se 3 (by rfl) ⟨700619, by rfl⟩ : syracuseStep 3736637 = 1401239) B1401239
theorem B4719683 : Blo 1104625 4719683 := bstep (se 1 (by rfl) ⟨3539762, by rfl⟩ : syracuseStep 4719683 = 7079525) B7079525
theorem B1246351 : Blo 1104625 1246351 := bstep (se 1 (by rfl) ⟨934763, by rfl⟩ : syracuseStep 1246351 = 1869527) B1869527
theorem B2491577 : Blo 1104625 2491577 := bstep (se 2 (by rfl) ⟨934341, by rfl⟩ : syracuseStep 2491577 = 1868683) B1868683
theorem B1869115 : Blo 1104625 1869115 := bstep (se 1 (by rfl) ⟨1401836, by rfl⟩ : syracuseStep 1869115 = 2803673) B2803673
theorem B6292889 : Blo 1104625 6292889 := bstep (se 2 (by rfl) ⟨2359833, by rfl⟩ : syracuseStep 6292889 = 4719667) B4719667
theorem B4720025 : Blo 1104625 4720025 := bstep (se 2 (by rfl) ⟨1770009, by rfl⟩ : syracuseStep 4720025 = 3540019) B3540019
theorem B1869257 : Blo 1104625 1869257 := bstep (se 2 (by rfl) ⟨700971, by rfl⟩ : syracuseStep 1869257 = 1401943) B1401943
theorem B1574407 : Blo 1104625 1574407 := bstep (se 1 (by rfl) ⟨1180805, by rfl⟩ : syracuseStep 1574407 = 2361611) B2361611
theorem B3147275 : Blo 1104625 3147275 := bstep (se 1 (by rfl) ⟨2360456, by rfl⟩ : syracuseStep 3147275 = 4720913) B4720913
theorem B5604875 : Blo 1104625 5604875 := bstep (se 1 (by rfl) ⟨4203656, by rfl⟩ : syracuseStep 5604875 = 8407313) B8407313
theorem B2491919 : Blo 1104625 2491919 := bstep (se 1 (by rfl) ⟨1868939, by rfl⟩ : syracuseStep 2491919 = 3737879) B3737879
theorem B2491937 : Blo 1104625 2491937 := bstep (se 2 (by rfl) ⟨934476, by rfl⟩ : syracuseStep 2491937 = 1868953) B1868953
theorem B47908421 : Blo 1104625 47908421 := bstep (se 4 (by rfl) ⟨4491414, by rfl⟩ : syracuseStep 47908421 = 8982829) B8982829
theorem B1246855 : Blo 1104625 1246855 := bstep (se 1 (by rfl) ⟨935141, by rfl⟩ : syracuseStep 1246855 = 1870283) B1870283
theorem B5605037 : Blo 1104625 5605037 := bstep (se 3 (by rfl) ⟨1050944, by rfl⟩ : syracuseStep 5605037 = 2101889) B2101889
theorem B1247035 : Blo 1104625 1247035 := bstep (se 1 (by rfl) ⟨935276, by rfl⟩ : syracuseStep 1247035 = 1870553) B1870553
theorem B73664369 : Blo 1104625 73664369 := bstep (se 2 (by rfl) ⟨27624138, by rfl⟩ : syracuseStep 73664369 = 55248277) B55248277
theorem B2492279 : Blo 1104625 2492279 := bstep (se 1 (by rfl) ⟨1869209, by rfl⟩ : syracuseStep 2492279 = 3738419) B3738419
theorem B4196231 : Blo 1104625 4196231 := bstep (se 1 (by rfl) ⟨3147173, by rfl⟩ : syracuseStep 4196231 = 6294347) B6294347
theorem B1771465 : Blo 1104625 1771465 := bstep (se 2 (by rfl) ⟨664299, by rfl⟩ : syracuseStep 1771465 = 1328599) B1328599
theorem B2492459 : Blo 1104625 2492459 := bstep (se 1 (by rfl) ⟨1869344, by rfl⟩ : syracuseStep 2492459 = 3738689) B3738689
theorem B4786295 : Blo 1104625 4786295 := bstep (se 1 (by rfl) ⟨3589721, by rfl⟩ : syracuseStep 4786295 = 7179443) B7179443
theorem B8390789 : Blo 1104625 8390789 := bstep (se 4 (by rfl) ⟨786636, by rfl⟩ : syracuseStep 8390789 = 1573273) B1573273
theorem B1869959 : Blo 1104625 1869959 := bstep (se 1 (by rfl) ⟨1402469, by rfl⟩ : syracuseStep 1869959 = 2804939) B2804939
theorem B1771721 : Blo 1104625 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B3541249 : Blo 1104625 3541249 := bstep (se 2 (by rfl) ⟨1327968, by rfl⟩ : syracuseStep 3541249 = 2655937) B2655937
theorem B1575227 : Blo 1104625 1575227 := bstep (se 1 (by rfl) ⟨1181420, by rfl⟩ : syracuseStep 1575227 = 2362841) B2362841
theorem B2492819 : Blo 1104625 2492819 := bstep (se 1 (by rfl) ⟨1869614, by rfl⟩ : syracuseStep 2492819 = 3739229) B3739229
theorem B3738041 : Blo 1104625 3738041 := bstep (se 2 (by rfl) ⟨1401765, by rfl⟩ : syracuseStep 3738041 = 2803531) B2803531
theorem B2099657 : Blo 1104625 2099657 := bstep (se 2 (by rfl) ⟨787371, by rfl⟩ : syracuseStep 2099657 = 1574743) B1574743
theorem B2492873 : Blo 1104625 2492873 := bstep (se 2 (by rfl) ⟨934827, by rfl⟩ : syracuseStep 2492873 = 1869655) B1869655
theorem B1772047 : Blo 1104625 1772047 := bstep (se 1 (by rfl) ⟨1329035, by rfl⟩ : syracuseStep 1772047 = 2658071) B2658071
theorem B13470401 : Blo 1104625 13470401 := bstep (se 2 (by rfl) ⟨5051400, by rfl⟩ : syracuseStep 13470401 = 10102801) B10102801
theorem B1870607 : Blo 1104625 1870607 := bstep (se 1 (by rfl) ⟨1402955, by rfl⟩ : syracuseStep 1870607 = 2805911) B2805911
theorem B45484915 : Blo 1104625 45484915 := bstep (se 1 (by rfl) ⟨34113686, by rfl⟩ : syracuseStep 45484915 = 68227373) B68227373
theorem B1575865 : Blo 1104625 1575865 := bstep (se 2 (by rfl) ⟨590949, by rfl⟩ : syracuseStep 1575865 = 1181899) B1181899
theorem B3738635 : Blo 1104625 3738635 := bstep (se 1 (by rfl) ⟨2803976, by rfl⟩ : syracuseStep 3738635 = 5607953) B5607953
theorem B3738743 : Blo 1104625 3738743 := bstep (se 1 (by rfl) ⟨2804057, by rfl⟩ : syracuseStep 3738743 = 5608115) B5608115
theorem B2493575 : Blo 1104625 2493575 := bstep (se 1 (by rfl) ⟨1870181, by rfl⟩ : syracuseStep 2493575 = 3740363) B3740363
theorem B40995989 : Blo 1104625 40995989 := bstep (se 6 (by rfl) ⟨960843, by rfl⟩ : syracuseStep 40995989 = 1921687) B1921687
theorem B12618989 : Blo 1104625 12618989 := bstep (se 3 (by rfl) ⟨2366060, by rfl⟩ : syracuseStep 12618989 = 4732121) B4732121
theorem B5606657 : Blo 1104625 5606657 := bstep (se 2 (by rfl) ⟨2102496, by rfl⟩ : syracuseStep 5606657 = 4204993) B4204993
theorem B13634849 : Blo 1104625 13634849 := bstep (se 2 (by rfl) ⟨5113068, by rfl⟩ : syracuseStep 13634849 = 10226137) B10226137
theorem B2493755 : Blo 1104625 2493755 := bstep (se 1 (by rfl) ⟨1870316, by rfl⟩ : syracuseStep 2493755 = 3740633) B3740633
theorem B2493881 : Blo 1104625 2493881 := bstep (se 2 (by rfl) ⟨935205, by rfl⟩ : syracuseStep 2493881 = 1870411) B1870411
theorem B3149371 : Blo 1104625 3149371 := bstep (se 1 (by rfl) ⟨2362028, by rfl⟩ : syracuseStep 3149371 = 4724057) B4724057
theorem B5312087 : Blo 1104625 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B4263511 : Blo 1104625 4263511 := bstep (se 1 (by rfl) ⟨3197633, by rfl⟩ : syracuseStep 4263511 = 6395267) B6395267
theorem B10620517 : Blo 1104625 10620517 := bstep (se 4 (by rfl) ⟨995673, by rfl⟩ : syracuseStep 10620517 = 1991347) B1991347
theorem B4198007 : Blo 1104625 4198007 := bstep (se 1 (by rfl) ⟨3148505, by rfl⟩ : syracuseStep 4198007 = 6297011) B6297011
theorem B3739337 : Blo 1104625 3739337 := bstep (se 2 (by rfl) ⟨1402251, by rfl⟩ : syracuseStep 3739337 = 2804503) B2804503
theorem B54529793 : Blo 1104625 54529793 := bstep (se 2 (by rfl) ⟨20448672, by rfl⟩ : syracuseStep 54529793 = 40897345) B40897345
theorem B2494223 : Blo 1104625 2494223 := bstep (se 1 (by rfl) ⟨1870667, by rfl⟩ : syracuseStep 2494223 = 3741335) B3741335
theorem B2494241 : Blo 1104625 2494241 := bstep (se 2 (by rfl) ⟨935340, by rfl⟩ : syracuseStep 2494241 = 1870681) B1870681
theorem B13438871 : Blo 1104625 13438871 := bstep (se 1 (by rfl) ⟨10079153, by rfl⟩ : syracuseStep 13438871 = 20158307) B20158307
theorem B5607467 : Blo 1104625 5607467 := bstep (se 1 (by rfl) ⟨4205600, by rfl⟩ : syracuseStep 5607467 = 8411201) B8411201
theorem B2363593 : Blo 1104625 2363593 := bstep (se 2 (by rfl) ⟨886347, by rfl⟩ : syracuseStep 2363593 = 1772695) B1772695
theorem B3150215 : Blo 1104625 3150215 := bstep (se 1 (by rfl) ⟨2362661, by rfl⟩ : syracuseStep 3150215 = 4725323) B4725323
theorem B2101639 : Blo 1104625 2101639 := bstep (se 1 (by rfl) ⟨1576229, by rfl⟩ : syracuseStep 2101639 = 3152459) B3152459
theorem B1577351 : Blo 1104625 1577351 := bstep (se 1 (by rfl) ⟨1183013, by rfl⟩ : syracuseStep 1577351 = 2366027) B2366027
theorem B3740039 : Blo 1104625 3740039 := bstep (se 1 (by rfl) ⟨2805029, by rfl⟩ : syracuseStep 3740039 = 5610059) B5610059
theorem B8393219 : Blo 1104625 8393219 := bstep (se 1 (by rfl) ⟨6294914, by rfl⟩ : syracuseStep 8393219 = 12589829) B12589829
theorem B4198979 : Blo 1104625 4198979 := bstep (se 1 (by rfl) ⟨3149234, by rfl⟩ : syracuseStep 4198979 = 6298469) B6298469
theorem B6296237 : Blo 1104625 6296237 := bstep (se 3 (by rfl) ⟨1180544, by rfl⟩ : syracuseStep 6296237 = 2361089) B2361089
theorem B1577659 : Blo 1104625 1577659 := bstep (se 1 (by rfl) ⟨1183244, by rfl⟩ : syracuseStep 1577659 = 2366489) B2366489
theorem B3740417 : Blo 1104625 3740417 := bstep (se 2 (by rfl) ⟨1402656, by rfl⟩ : syracuseStep 3740417 = 2805313) B2805313
theorem B2659225 : Blo 1104625 2659225 := bstep (se 2 (by rfl) ⟨997209, by rfl⟩ : syracuseStep 2659225 = 1994419) B1994419
theorem B4199435 : Blo 1104625 4199435 := bstep (se 1 (by rfl) ⟨3149576, by rfl⟩ : syracuseStep 4199435 = 6299153) B6299153
theorem B3151001 : Blo 1104625 3151001 := bstep (se 2 (by rfl) ⟨1181625, by rfl⟩ : syracuseStep 3151001 = 2363251) B2363251
theorem B6067457 : Blo 1104625 6067457 := bstep (se 2 (by rfl) ⟨2275296, by rfl⟩ : syracuseStep 6067457 = 4550593) B4550593
theorem B5608763 : Blo 1104625 5608763 := bstep (se 1 (by rfl) ⟨4206572, by rfl⟩ : syracuseStep 5608763 = 8413145) B8413145
theorem B3544505 : Blo 1104625 3544505 := bstep (se 2 (by rfl) ⟨1329189, by rfl⟩ : syracuseStep 3544505 = 2658379) B2658379
theorem B5608925 : Blo 1104625 5608925 := bstep (se 3 (by rfl) ⟨1051673, by rfl⟩ : syracuseStep 5608925 = 2103347) B2103347
theorem B2659841 : Blo 1104625 2659841 := bstep (se 2 (by rfl) ⟨997440, by rfl⟩ : syracuseStep 2659841 = 1994881) B1994881
theorem B8295965 : Blo 1104625 8295965 := bstep (se 3 (by rfl) ⟨1555493, by rfl⟩ : syracuseStep 8295965 = 3110987) B3110987
theorem B13473323 : Blo 1104625 13473323 := bstep (se 1 (by rfl) ⟨10104992, by rfl⟩ : syracuseStep 13473323 = 20209985) B20209985
theorem B3741227 : Blo 1104625 3741227 := bstep (se 1 (by rfl) ⟨2805920, by rfl⟩ : syracuseStep 3741227 = 5611841) B5611841
theorem B17929907 : Blo 1104625 17929907 := bstep (se 1 (by rfl) ⟨13447430, by rfl⟩ : syracuseStep 17929907 = 26894861) B26894861
theorem B2987705 : Blo 1104625 2987705 := bstep (se 2 (by rfl) ⟨1120389, by rfl⟩ : syracuseStep 2987705 = 2240779) B2240779
theorem B3151649 : Blo 1104625 3151649 := bstep (se 2 (by rfl) ⟨1181868, by rfl⟩ : syracuseStep 3151649 = 2363737) B2363737
theorem B5609249 : Blo 1104625 5609249 := bstep (se 2 (by rfl) ⟨2103468, by rfl⟩ : syracuseStep 5609249 = 4206937) B4206937
theorem B14161715 : Blo 1104625 14161715 := bstep (se 1 (by rfl) ⟨10621286, by rfl⟩ : syracuseStep 14161715 = 21242573) B21242573
theorem B1775495 : Blo 1104625 1775495 := bstep (se 1 (by rfl) ⟨1331621, by rfl⟩ : syracuseStep 1775495 = 2663243) B2663243
theorem B18913175 : Blo 1104625 18913175 := bstep (se 1 (by rfl) ⟨14184881, by rfl⟩ : syracuseStep 18913175 = 28369763) B28369763
theorem B2103241 : Blo 1104625 2103241 := bstep (se 2 (by rfl) ⟨788715, by rfl⟩ : syracuseStep 2103241 = 1577431) B1577431
theorem B2365985 : Blo 1104625 2365985 := bstep (se 2 (by rfl) ⟨887244, by rfl⟩ : syracuseStep 2365985 = 1774489) B1774489
theorem B21568193 : Blo 1104625 21568193 := bstep (se 2 (by rfl) ⟨8088072, by rfl⟩ : syracuseStep 21568193 = 16176145) B16176145
theorem B5610221 : Blo 1104625 5610221 := bstep (se 3 (by rfl) ⟨1051916, by rfl⟩ : syracuseStep 5610221 = 2103833) B2103833
theorem B3152641 : Blo 1104625 3152641 := bstep (se 2 (by rfl) ⟨1182240, by rfl⟩ : syracuseStep 3152641 = 2364481) B2364481
theorem B2366327 : Blo 1104625 2366327 := bstep (se 1 (by rfl) ⟨1774745, by rfl⟩ : syracuseStep 2366327 = 3549491) B3549491
theorem B40410019 : Blo 1104625 40410019 := bstep (se 1 (by rfl) ⟨30307514, by rfl⟩ : syracuseStep 40410019 = 60615029) B60615029
theorem B4201591 : Blo 1104625 4201591 := bstep (se 1 (by rfl) ⟨3151193, by rfl⟩ : syracuseStep 4201591 = 6302387) B6302387
theorem B5315777 : Blo 1104625 5315777 := bstep (se 2 (by rfl) ⟨1993416, by rfl⟩ : syracuseStep 5315777 = 3986833) B3986833
theorem B2366779 : Blo 1104625 2366779 := bstep (se 1 (by rfl) ⟨1775084, by rfl⟩ : syracuseStep 2366779 = 3550169) B3550169
theorem B12623363 : Blo 1104625 12623363 := bstep (se 1 (by rfl) ⟨9467522, by rfl⟩ : syracuseStep 12623363 = 18935045) B18935045
theorem B5611031 : Blo 1104625 5611031 := bstep (se 1 (by rfl) ⟨4208273, by rfl⟩ : syracuseStep 5611031 = 8416547) B8416547
theorem B2989703 : Blo 1104625 2989703 := bstep (se 1 (by rfl) ⟨2242277, by rfl⟩ : syracuseStep 2989703 = 4484555) B4484555
theorem B40345229 : Blo 1104625 40345229 := bstep (se 3 (by rfl) ⟨7564730, by rfl⟩ : syracuseStep 40345229 = 15129461) B15129461
theorem B7577317 : Blo 1104625 7577317 := bstep (se 4 (by rfl) ⟨710373, by rfl⟩ : syracuseStep 7577317 = 1420747) B1420747
theorem B5054393 : Blo 1104625 5054393 := bstep (se 2 (by rfl) ⟨1895397, by rfl⟩ : syracuseStep 5054393 = 3790795) B3790795
theorem B4202563 : Blo 1104625 4202563 := bstep (se 1 (by rfl) ⟨3151922, by rfl⟩ : syracuseStep 4202563 = 6303845) B6303845
theorem B12787799 : Blo 1104625 12787799 := bstep (se 1 (by rfl) ⟨9590849, by rfl⟩ : syracuseStep 12787799 = 19181699) B19181699
theorem B4727099 : Blo 1104625 4727099 := bstep (se 1 (by rfl) ⟨3545324, by rfl⟩ : syracuseStep 4727099 = 7090649) B7090649
theorem B3547451 : Blo 1104625 3547451 := bstep (se 1 (by rfl) ⟨2660588, by rfl⟩ : syracuseStep 3547451 = 5321177) B5321177
theorem B21537089 : Blo 1104625 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B4202867 : Blo 1104625 4202867 := bstep (se 1 (by rfl) ⟨3152150, by rfl⟩ : syracuseStep 4202867 = 6304301) B6304301
theorem B3547709 : Blo 1104625 3547709 := bstep (se 3 (by rfl) ⟨665195, by rfl⟩ : syracuseStep 3547709 = 1330391) B1330391
theorem B4203323 : Blo 1104625 4203323 := bstep (se 1 (by rfl) ⟨3152492, by rfl⟩ : syracuseStep 4203323 = 6304985) B6304985
theorem B2991163 : Blo 1104625 2991163 := bstep (se 1 (by rfl) ⟨2243372, by rfl⟩ : syracuseStep 2991163 = 4486745) B4486745
theorem B7185469 : Blo 1104625 7185469 := bstep (se 3 (by rfl) ⟨1347275, by rfl⟩ : syracuseStep 7185469 = 2694551) B2694551
theorem B6300929 : Blo 1104625 6300929 := bstep (se 2 (by rfl) ⟨2362848, by rfl⟩ : syracuseStep 6300929 = 4725697) B4725697
theorem B2991389 : Blo 1104625 2991389 := bstep (se 3 (by rfl) ⟨560885, by rfl⟩ : syracuseStep 2991389 = 1121771) B1121771
theorem B4203809 : Blo 1104625 4203809 := bstep (se 2 (by rfl) ⟨1576428, by rfl⟩ : syracuseStep 4203809 = 3152857) B3152857
theorem B3155591 : Blo 1104625 3155591 := bstep (se 1 (by rfl) ⟨2366693, by rfl⟩ : syracuseStep 3155591 = 4733387) B4733387
theorem B6301385 : Blo 1104625 6301385 := bstep (se 2 (by rfl) ⟨2363019, by rfl⟩ : syracuseStep 6301385 = 4726039) B4726039
theorem B8398565 : Blo 1104625 8398565 := bstep (se 4 (by rfl) ⟨787365, by rfl⟩ : syracuseStep 8398565 = 1574731) B1574731
theorem B3155773 : Blo 1104625 3155773 := bstep (se 3 (by rfl) ⟨591707, by rfl⟩ : syracuseStep 3155773 = 1183415) B1183415
theorem B3155831 : Blo 1104625 3155831 := bstep (se 1 (by rfl) ⟨2366873, by rfl⟩ : syracuseStep 3155831 = 4733747) B4733747
theorem B18917549 : Blo 1104625 18917549 := bstep (se 3 (by rfl) ⟨3547040, by rfl⟩ : syracuseStep 18917549 = 7094081) B7094081
theorem B15116489 : Blo 1104625 15116489 := bstep (se 2 (by rfl) ⟨5668683, by rfl⟩ : syracuseStep 15116489 = 11337367) B11337367
theorem B4204781 : Blo 1104625 4204781 := bstep (se 3 (by rfl) ⟨788396, by rfl⟩ : syracuseStep 4204781 = 1576793) B1576793
theorem B51194177 : Blo 1104625 51194177 := bstep (se 2 (by rfl) ⟨19197816, by rfl⟩ : syracuseStep 51194177 = 38395633) B38395633
theorem B5319179 : Blo 1104625 5319179 := bstep (se 1 (by rfl) ⟨3989384, by rfl⟩ : syracuseStep 5319179 = 7978769) B7978769
theorem B3549707 : Blo 1104625 3549707 := bstep (se 1 (by rfl) ⟨2662280, by rfl⟩ : syracuseStep 3549707 = 5324561) B5324561
theorem B4729373 : Blo 1104625 4729373 := bstep (se 3 (by rfl) ⟨886757, by rfl⟩ : syracuseStep 4729373 = 1773515) B1773515
theorem B2796403 : Blo 1104625 2796403 := bstep (se 1 (by rfl) ⟨2097302, by rfl⟩ : syracuseStep 2796403 = 4194605) B4194605
theorem B4205465 : Blo 1104625 4205465 := bstep (se 2 (by rfl) ⟨1577049, by rfl⟩ : syracuseStep 4205465 = 3154099) B3154099
theorem B3156889 : Blo 1104625 3156889 := bstep (se 2 (by rfl) ⟨1183833, by rfl⟩ : syracuseStep 3156889 = 2367667) B2367667
theorem B2796545 : Blo 1104625 2796545 := bstep (se 2 (by rfl) ⟨1048704, by rfl⟩ : syracuseStep 2796545 = 2097409) B2097409
theorem B51064123 : Blo 1104625 51064123 := bstep (se 1 (by rfl) ⟨38298092, by rfl⟩ : syracuseStep 51064123 = 76596185) B76596185
theorem B2797001 : Blo 1104625 2797001 := bstep (se 2 (by rfl) ⟨1048875, by rfl⟩ : syracuseStep 2797001 = 2097751) B2097751
theorem B2240201 : Blo 1104625 2240201 := bstep (se 2 (by rfl) ⟨840075, by rfl⟩ : syracuseStep 2240201 = 1680151) B1680151
theorem B2797355 : Blo 1104625 2797355 := bstep (se 1 (by rfl) ⟨2098016, by rfl⟩ : syracuseStep 2797355 = 4196033) B4196033
theorem B4206451 : Blo 1104625 4206451 := bstep (se 1 (by rfl) ⟨3154838, by rfl⟩ : syracuseStep 4206451 = 6309677) B6309677
theorem B4042763 : Blo 1104625 4042763 := bstep (se 1 (by rfl) ⟨3032072, by rfl⟩ : syracuseStep 4042763 = 6064145) B6064145
theorem B1683703 : Blo 1104625 1683703 := bstep (se 1 (by rfl) ⟨1262777, by rfl⟩ : syracuseStep 1683703 = 2525555) B2525555
theorem B3027335 : Blo 1104625 3027335 := bstep (se 1 (by rfl) ⟨2270501, by rfl⟩ : syracuseStep 3027335 = 4541003) B4541003
theorem B5681593 : Blo 1104625 5681593 := bstep (se 2 (by rfl) ⟨2130597, by rfl⟩ : syracuseStep 5681593 = 4261195) B4261195
theorem B12595661 : Blo 1104625 12595661 := bstep (se 3 (by rfl) ⟨2361686, by rfl⟩ : syracuseStep 12595661 = 4723373) B4723373
theorem B13447781 : Blo 1104625 13447781 := bstep (se 4 (by rfl) ⟨1260729, by rfl⟩ : syracuseStep 13447781 = 2521459) B2521459
theorem B2798347 : Blo 1104625 2798347 := bstep (se 1 (by rfl) ⟨2098760, by rfl⟩ : syracuseStep 2798347 = 4197521) B4197521
theorem B2798489 : Blo 1104625 2798489 := bstep (se 2 (by rfl) ⟨1049433, by rfl⟩ : syracuseStep 2798489 = 2098867) B2098867
theorem B2798651 : Blo 1104625 2798651 := bstep (se 1 (by rfl) ⟨2098988, by rfl⟩ : syracuseStep 2798651 = 4197977) B4197977
theorem B2798995 : Blo 1104625 2798995 := bstep (se 1 (by rfl) ⟨2099246, by rfl⟩ : syracuseStep 2798995 = 4198493) B4198493
theorem B6305303 : Blo 1104625 6305303 := bstep (se 1 (by rfl) ⟨4728977, by rfl⟩ : syracuseStep 6305303 = 9457955) B9457955
theorem B2799137 : Blo 1104625 2799137 := bstep (se 2 (by rfl) ⟨1049676, by rfl⟩ : syracuseStep 2799137 = 2099353) B2099353
theorem B40384331 : Blo 1104625 40384331 := bstep (se 1 (by rfl) ⟨30288248, by rfl⟩ : syracuseStep 40384331 = 60576497) B60576497
theorem B8075123 : Blo 1104625 8075123 := bstep (se 1 (by rfl) ⟨6056342, by rfl⟩ : syracuseStep 8075123 = 12112685) B12112685
theorem B2242505 : Blo 1104625 2242505 := bstep (se 2 (by rfl) ⟨840939, by rfl⟩ : syracuseStep 2242505 = 1681879) B1681879
theorem B4208669 : Blo 1104625 4208669 := bstep (se 3 (by rfl) ⟨789125, by rfl⟩ : syracuseStep 4208669 = 1578251) B1578251
theorem B3192979 : Blo 1104625 3192979 := bstep (se 1 (by rfl) ⟨2394734, by rfl⟩ : syracuseStep 3192979 = 4789469) B4789469
theorem B2800129 : Blo 1104625 2800129 := bstep (se 2 (by rfl) ⟨1050048, by rfl⟩ : syracuseStep 2800129 = 2100097) B2100097
theorem B3029519 : Blo 1104625 3029519 := bstep (se 1 (by rfl) ⟨2272139, by rfl⟩ : syracuseStep 3029519 = 4544279) B4544279
theorem B23935607 : Blo 1104625 23935607 := bstep (se 1 (by rfl) ⟨17951705, by rfl⟩ : syracuseStep 23935607 = 35903411) B35903411
theorem B10631897 : Blo 1104625 10631897 := bstep (se 2 (by rfl) ⟨3986961, by rfl⟩ : syracuseStep 10631897 = 7973923) B7973923
theorem B2800727 : Blo 1104625 2800727 := bstep (se 1 (by rfl) ⟨2100545, by rfl⟩ : syracuseStep 2800727 = 4201091) B4201091
theorem B4734071 : Blo 1104625 4734071 := bstep (se 1 (by rfl) ⟨3550553, by rfl⟩ : syracuseStep 4734071 = 7101107) B7101107
theorem B2800939 : Blo 1104625 2800939 := bstep (se 1 (by rfl) ⟨2100704, by rfl⟩ : syracuseStep 2800939 = 4201409) B4201409
theorem B6307217 : Blo 1104625 6307217 := bstep (se 2 (by rfl) ⟨2365206, by rfl⟩ : syracuseStep 6307217 = 4730413) B4730413
theorem B5979577 : Blo 1104625 5979577 := bstep (se 2 (by rfl) ⟨2242341, by rfl⟩ : syracuseStep 5979577 = 4484683) B4484683
theorem B2801081 : Blo 1104625 2801081 := bstep (se 2 (by rfl) ⟨1050405, by rfl⟩ : syracuseStep 2801081 = 2100811) B2100811
theorem B5324753 : Blo 1104625 5324753 := bstep (se 2 (by rfl) ⟨1996782, by rfl⟩ : syracuseStep 5324753 = 3993565) B3993565
theorem B6307901 : Blo 1104625 6307901 := bstep (se 3 (by rfl) ⟨1182731, by rfl⟩ : syracuseStep 6307901 = 2365463) B2365463
theorem B5324867 : Blo 1104625 5324867 := bstep (se 1 (by rfl) ⟨3993650, by rfl⟩ : syracuseStep 5324867 = 7987301) B7987301
theorem B2244743 : Blo 1104625 2244743 := bstep (se 1 (by rfl) ⟨1683557, by rfl⟩ : syracuseStep 2244743 = 3367115) B3367115
theorem B6832421 : Blo 1104625 6832421 := bstep (se 4 (by rfl) ⟨640539, by rfl⟩ : syracuseStep 6832421 = 1281079) B1281079
theorem B2802073 : Blo 1104625 2802073 := bstep (se 2 (by rfl) ⟨1050777, by rfl⟩ : syracuseStep 2802073 = 2101555) B2101555
theorem B7094749 : Blo 1104625 7094749 := bstep (se 3 (by rfl) ⟨1330265, by rfl⟩ : syracuseStep 7094749 = 2660531) B2660531
theorem B2802235 : Blo 1104625 2802235 := bstep (se 1 (by rfl) ⟨2101676, by rfl⟩ : syracuseStep 2802235 = 4203353) B4203353
theorem B2802377 : Blo 1104625 2802377 := bstep (se 2 (by rfl) ⟨1050891, by rfl⟩ : syracuseStep 2802377 = 2101783) B2101783
theorem B3982061 : Blo 1104625 3982061 := bstep (se 3 (by rfl) ⟨746636, by rfl⟩ : syracuseStep 3982061 = 1493273) B1493273
theorem B2802721 : Blo 1104625 2802721 := bstep (se 2 (by rfl) ⟨1051020, by rfl⟩ : syracuseStep 2802721 = 2102041) B2102041
theorem B2803319 : Blo 1104625 2803319 := bstep (se 1 (by rfl) ⟨2102489, by rfl⟩ : syracuseStep 2803319 = 4204979) B4204979
theorem B1657019 : Blo 1104625 1657019 := bstep (se 1 (by rfl) ⟨1242764, by rfl⟩ : syracuseStep 1657019 = 2485529) B2485529
theorem B1657079 : Blo 1104625 1657079 := bstep (se 1 (by rfl) ⟨1242809, by rfl⟩ : syracuseStep 1657079 = 2485619) B2485619
theorem B3983617 : Blo 1104625 3983617 := bstep (se 2 (by rfl) ⟨1493856, by rfl⟩ : syracuseStep 3983617 = 2987713) B2987713
theorem B1657103 : Blo 1104625 1657103 := bstep (se 1 (by rfl) ⟨1242827, by rfl⟩ : syracuseStep 1657103 = 2485655) B2485655
theorem B1657145 : Blo 1104625 1657145 := bstep (se 2 (by rfl) ⟨621429, by rfl⟩ : syracuseStep 1657145 = 1242859) B1242859
theorem B1657223 : Blo 1104625 1657223 := bstep (se 1 (by rfl) ⟨1242917, by rfl⟩ : syracuseStep 1657223 = 2485835) B2485835
theorem B1657259 : Blo 1104625 1657259 := bstep (se 1 (by rfl) ⟨1242944, by rfl⟩ : syracuseStep 1657259 = 2485889) B2485889
theorem B1493435 : Blo 1104625 1493435 := bstep (se 1 (by rfl) ⟨1120076, by rfl⟩ : syracuseStep 1493435 = 2240153) B2240153
theorem B1657289 : Blo 1104625 1657289 := bstep (se 2 (by rfl) ⟨621483, by rfl⟩ : syracuseStep 1657289 = 1242967) B1242967
theorem B1329679 : Blo 1104625 1329679 := bstep (se 1 (by rfl) ⟨997259, by rfl⟩ : syracuseStep 1329679 = 1994519) B1994519
theorem B1657403 : Blo 1104625 1657403 := bstep (se 1 (by rfl) ⟨1243052, by rfl⟩ : syracuseStep 1657403 = 2486105) B2486105
theorem B1657463 : Blo 1104625 1657463 := bstep (se 1 (by rfl) ⟨1243097, by rfl⟩ : syracuseStep 1657463 = 2486195) B2486195
theorem B1657487 : Blo 1104625 1657487 := bstep (se 1 (by rfl) ⟨1243115, by rfl⟩ : syracuseStep 1657487 = 2486231) B2486231
theorem B1657529 : Blo 1104625 1657529 := bstep (se 2 (by rfl) ⟨621573, by rfl⟩ : syracuseStep 1657529 = 1243147) B1243147
theorem B18926297 : Blo 1104625 18926297 := bstep (se 2 (by rfl) ⟨7097361, by rfl⟩ : syracuseStep 18926297 = 14194723) B14194723
theorem B1657607 : Blo 1104625 1657607 := bstep (se 1 (by rfl) ⟨1243205, by rfl⟩ : syracuseStep 1657607 = 2486411) B2486411
theorem B1657643 : Blo 1104625 1657643 := bstep (se 1 (by rfl) ⟨1243232, by rfl⟩ : syracuseStep 1657643 = 2486465) B2486465
theorem B1657673 : Blo 1104625 1657673 := bstep (se 2 (by rfl) ⟨621627, by rfl⟩ : syracuseStep 1657673 = 1243255) B1243255
theorem B2804615 : Blo 1104625 2804615 := bstep (se 1 (by rfl) ⟨2103461, by rfl⟩ : syracuseStep 2804615 = 4206923) B4206923
theorem B2804665 : Blo 1104625 2804665 := bstep (se 2 (by rfl) ⟨1051749, by rfl⟩ : syracuseStep 2804665 = 2103499) B2103499
theorem B1657787 : Blo 1104625 1657787 := bstep (se 1 (by rfl) ⟨1243340, by rfl⟩ : syracuseStep 1657787 = 2486681) B2486681
theorem B1657847 : Blo 1104625 1657847 := bstep (se 1 (by rfl) ⟨1243385, by rfl⟩ : syracuseStep 1657847 = 2486771) B2486771
theorem B1657871 : Blo 1104625 1657871 := bstep (se 1 (by rfl) ⟨1243403, by rfl⟩ : syracuseStep 1657871 = 2486807) B2486807
theorem B1657913 : Blo 1104625 1657913 := bstep (se 2 (by rfl) ⟨621717, by rfl⟩ : syracuseStep 1657913 = 1243435) B1243435
theorem B1657991 : Blo 1104625 1657991 := bstep (se 1 (by rfl) ⟨1243493, by rfl⟩ : syracuseStep 1657991 = 2486987) B2486987
theorem B1658027 : Blo 1104625 1658027 := bstep (se 1 (by rfl) ⟨1243520, by rfl⟩ : syracuseStep 1658027 = 2487041) B2487041
theorem B1658057 : Blo 1104625 1658057 := bstep (se 2 (by rfl) ⟨621771, by rfl⟩ : syracuseStep 1658057 = 1243543) B1243543
theorem B3984655 : Blo 1104625 3984655 := bstep (se 1 (by rfl) ⟨2988491, by rfl⟩ : syracuseStep 3984655 = 5976983) B5976983
theorem B1658171 : Blo 1104625 1658171 := bstep (se 1 (by rfl) ⟨1243628, by rfl⟩ : syracuseStep 1658171 = 2487257) B2487257
theorem B1658231 : Blo 1104625 1658231 := bstep (se 1 (by rfl) ⟨1243673, by rfl⟩ : syracuseStep 1658231 = 2487347) B2487347
theorem B1658255 : Blo 1104625 1658255 := bstep (se 1 (by rfl) ⟨1243691, by rfl⟩ : syracuseStep 1658255 = 2487383) B2487383
theorem B5688721 : Blo 1104625 5688721 := bstep (se 2 (by rfl) ⟨2133270, by rfl⟩ : syracuseStep 5688721 = 4266541) B4266541
theorem B1658297 : Blo 1104625 1658297 := bstep (se 2 (by rfl) ⟨621861, by rfl⟩ : syracuseStep 1658297 = 1243723) B1243723
theorem B1658375 : Blo 1104625 1658375 := bstep (se 1 (by rfl) ⟨1243781, by rfl⟩ : syracuseStep 1658375 = 2487563) B2487563
theorem B2805263 : Blo 1104625 2805263 := bstep (se 1 (by rfl) ⟨2103947, by rfl⟩ : syracuseStep 2805263 = 4207895) B4207895
theorem B1658411 : Blo 1104625 1658411 := bstep (se 1 (by rfl) ⟨1243808, by rfl⟩ : syracuseStep 1658411 = 2487617) B2487617
theorem B1658441 : Blo 1104625 1658441 := bstep (se 2 (by rfl) ⟨621915, by rfl⟩ : syracuseStep 1658441 = 1243831) B1243831
theorem B2838131 : Blo 1104625 2838131 := bstep (se 1 (by rfl) ⟨2128598, by rfl⟩ : syracuseStep 2838131 = 4257197) B4257197
theorem B1658555 : Blo 1104625 1658555 := bstep (se 1 (by rfl) ⟨1243916, by rfl⟩ : syracuseStep 1658555 = 2487833) B2487833
theorem B1658615 : Blo 1104625 1658615 := bstep (se 1 (by rfl) ⟨1243961, by rfl⟩ : syracuseStep 1658615 = 2487923) B2487923
theorem B1658639 : Blo 1104625 1658639 := bstep (se 1 (by rfl) ⟨1243979, by rfl⟩ : syracuseStep 1658639 = 2487959) B2487959
theorem B1658681 : Blo 1104625 1658681 := bstep (se 2 (by rfl) ⟨622005, by rfl⟩ : syracuseStep 1658681 = 1244011) B1244011
theorem B1658759 : Blo 1104625 1658759 := bstep (se 1 (by rfl) ⟨1244069, by rfl⟩ : syracuseStep 1658759 = 2488139) B2488139
theorem B1658795 : Blo 1104625 1658795 := bstep (se 1 (by rfl) ⟨1244096, by rfl⟩ : syracuseStep 1658795 = 2488193) B2488193
theorem B1658825 : Blo 1104625 1658825 := bstep (se 2 (by rfl) ⟨622059, by rfl⟩ : syracuseStep 1658825 = 1244119) B1244119
theorem B1658939 : Blo 1104625 1658939 := bstep (se 1 (by rfl) ⟨1244204, by rfl⟩ : syracuseStep 1658939 = 2488409) B2488409
theorem B1658999 : Blo 1104625 1658999 := bstep (se 1 (by rfl) ⟨1244249, by rfl⟩ : syracuseStep 1658999 = 2488499) B2488499
theorem B1659023 : Blo 1104625 1659023 := bstep (se 1 (by rfl) ⟨1244267, by rfl⟩ : syracuseStep 1659023 = 2488535) B2488535
theorem B1659065 : Blo 1104625 1659065 := bstep (se 2 (by rfl) ⟨622149, by rfl⟩ : syracuseStep 1659065 = 1244299) B1244299
theorem B2805961 : Blo 1104625 2805961 := bstep (se 2 (by rfl) ⟨1052235, by rfl⟩ : syracuseStep 2805961 = 2104471) B2104471
theorem B1659143 : Blo 1104625 1659143 := bstep (se 1 (by rfl) ⟨1244357, by rfl⟩ : syracuseStep 1659143 = 2488715) B2488715
theorem B1659179 : Blo 1104625 1659179 := bstep (se 1 (by rfl) ⟨1244384, by rfl⟩ : syracuseStep 1659179 = 2488769) B2488769
theorem B1659209 : Blo 1104625 1659209 := bstep (se 2 (by rfl) ⟨622203, by rfl⟩ : syracuseStep 1659209 = 1244407) B1244407
theorem B2806103 : Blo 1104625 2806103 := bstep (se 1 (by rfl) ⟨2104577, by rfl⟩ : syracuseStep 2806103 = 4209155) B4209155
theorem B3199351 : Blo 1104625 3199351 := bstep (se 1 (by rfl) ⟨2399513, by rfl⟩ : syracuseStep 3199351 = 4799027) B4799027
theorem B1659323 : Blo 1104625 1659323 := bstep (se 1 (by rfl) ⟨1244492, by rfl⟩ : syracuseStep 1659323 = 2488985) B2488985
theorem B54514133 : Blo 1104625 54514133 := bstep (se 7 (by rfl) ⟨638837, by rfl⟩ : syracuseStep 54514133 = 1277675) B1277675
theorem B1659383 : Blo 1104625 1659383 := bstep (se 1 (by rfl) ⟨1244537, by rfl⟩ : syracuseStep 1659383 = 2489075) B2489075
theorem B1659407 : Blo 1104625 1659407 := bstep (se 1 (by rfl) ⟨1244555, by rfl⟩ : syracuseStep 1659407 = 2489111) B2489111
theorem B1659449 : Blo 1104625 1659449 := bstep (se 2 (by rfl) ⟨622293, by rfl⟩ : syracuseStep 1659449 = 1244587) B1244587
theorem B21254723 : Blo 1104625 21254723 := bstep (se 1 (by rfl) ⟨15941042, by rfl⟩ : syracuseStep 21254723 = 31882085) B31882085
theorem B1659527 : Blo 1104625 1659527 := bstep (se 1 (by rfl) ⟨1244645, by rfl⟩ : syracuseStep 1659527 = 2489291) B2489291
theorem B1659563 : Blo 1104625 1659563 := bstep (se 1 (by rfl) ⟨1244672, by rfl⟩ : syracuseStep 1659563 = 2489345) B2489345
theorem B1659593 : Blo 1104625 1659593 := bstep (se 2 (by rfl) ⟨622347, by rfl⟩ : syracuseStep 1659593 = 1244695) B1244695
theorem B1659707 : Blo 1104625 1659707 := bstep (se 1 (by rfl) ⟨1244780, by rfl⟩ : syracuseStep 1659707 = 2489561) B2489561
theorem B1659767 : Blo 1104625 1659767 := bstep (se 1 (by rfl) ⟨1244825, by rfl⟩ : syracuseStep 1659767 = 2489651) B2489651
theorem B1659791 : Blo 1104625 1659791 := bstep (se 1 (by rfl) ⟨1244843, by rfl⟩ : syracuseStep 1659791 = 2489687) B2489687
theorem B61395893 : Blo 1104625 61395893 := bstep (se 5 (by rfl) ⟨2877932, by rfl⟩ : syracuseStep 61395893 = 5755865) B5755865
theorem B1659833 : Blo 1104625 1659833 := bstep (se 2 (by rfl) ⟨622437, by rfl⟩ : syracuseStep 1659833 = 1244875) B1244875
theorem B1659911 : Blo 1104625 1659911 := bstep (se 1 (by rfl) ⟨1244933, by rfl⟩ : syracuseStep 1659911 = 2489867) B2489867
theorem B1659947 : Blo 1104625 1659947 := bstep (se 1 (by rfl) ⟨1244960, by rfl⟩ : syracuseStep 1659947 = 2489921) B2489921
theorem B1659977 : Blo 1104625 1659977 := bstep (se 2 (by rfl) ⟨622491, by rfl⟩ : syracuseStep 1659977 = 1244983) B1244983
theorem B1660091 : Blo 1104625 1660091 := bstep (se 1 (by rfl) ⟨1245068, by rfl⟩ : syracuseStep 1660091 = 2490137) B2490137
theorem B1660151 : Blo 1104625 1660151 := bstep (se 1 (by rfl) ⟨1245113, by rfl⟩ : syracuseStep 1660151 = 2490227) B2490227
theorem B1660175 : Blo 1104625 1660175 := bstep (se 1 (by rfl) ⟨1245131, by rfl⟩ : syracuseStep 1660175 = 2490263) B2490263
theorem B1660217 : Blo 1104625 1660217 := bstep (se 2 (by rfl) ⟨622581, by rfl⟩ : syracuseStep 1660217 = 1245163) B1245163
theorem B1398151 : Blo 1104625 1398151 := bstep (se 1 (by rfl) ⟨1048613, by rfl⟩ : syracuseStep 1398151 = 2097227) B2097227
theorem B1660295 : Blo 1104625 1660295 := bstep (se 1 (by rfl) ⟨1245221, by rfl⟩ : syracuseStep 1660295 = 2490443) B2490443
theorem B1660331 : Blo 1104625 1660331 := bstep (se 1 (by rfl) ⟨1245248, by rfl⟩ : syracuseStep 1660331 = 2490497) B2490497
theorem B34067891 : Blo 1104625 34067891 := bstep (se 1 (by rfl) ⟨25550918, by rfl⟩ : syracuseStep 34067891 = 51101837) B51101837
theorem B1660361 : Blo 1104625 1660361 := bstep (se 2 (by rfl) ⟨622635, by rfl⟩ : syracuseStep 1660361 = 1245271) B1245271
theorem B1660475 : Blo 1104625 1660475 := bstep (se 1 (by rfl) ⟨1245356, by rfl⟩ : syracuseStep 1660475 = 2490713) B2490713
theorem B1660535 : Blo 1104625 1660535 := bstep (se 1 (by rfl) ⟨1245401, by rfl⟩ : syracuseStep 1660535 = 2490803) B2490803
theorem B3364487 : Blo 1104625 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B1660559 : Blo 1104625 1660559 := bstep (se 1 (by rfl) ⟨1245419, by rfl⟩ : syracuseStep 1660559 = 2490839) B2490839
theorem B1660601 : Blo 1104625 1660601 := bstep (se 2 (by rfl) ⟨622725, by rfl⟩ : syracuseStep 1660601 = 1245451) B1245451
theorem B1660679 : Blo 1104625 1660679 := bstep (se 1 (by rfl) ⟨1245509, by rfl⟩ : syracuseStep 1660679 = 2491019) B2491019
theorem B1660715 : Blo 1104625 1660715 := bstep (se 1 (by rfl) ⟨1245536, by rfl⟩ : syracuseStep 1660715 = 2491073) B2491073
theorem B1660745 : Blo 1104625 1660745 := bstep (se 2 (by rfl) ⟨622779, by rfl⟩ : syracuseStep 1660745 = 1245559) B1245559
theorem B1398647 : Blo 1104625 1398647 := bstep (se 1 (by rfl) ⟨1048985, by rfl⟩ : syracuseStep 1398647 = 2097971) B2097971
theorem B1660859 : Blo 1104625 1660859 := bstep (se 1 (by rfl) ⟨1245644, by rfl⟩ : syracuseStep 1660859 = 2491289) B2491289
theorem B1660919 : Blo 1104625 1660919 := bstep (se 1 (by rfl) ⟨1245689, by rfl⟩ : syracuseStep 1660919 = 2491379) B2491379
theorem B1497079 : Blo 1104625 1497079 := bstep (se 1 (by rfl) ⟨1122809, by rfl⟩ : syracuseStep 1497079 = 2245619) B2245619
theorem B1398799 : Blo 1104625 1398799 := bstep (se 1 (by rfl) ⟨1049099, by rfl⟩ : syracuseStep 1398799 = 2098199) B2098199
theorem B1660943 : Blo 1104625 1660943 := bstep (se 1 (by rfl) ⟨1245707, by rfl⟩ : syracuseStep 1660943 = 2491415) B2491415
theorem B12769325 : Blo 1104625 12769325 := bstep (se 3 (by rfl) ⟨2394248, by rfl⟩ : syracuseStep 12769325 = 4788497) B4788497
theorem B1660985 : Blo 1104625 1660985 := bstep (se 2 (by rfl) ⟨622869, by rfl⟩ : syracuseStep 1660985 = 1245739) B1245739
theorem B1661063 : Blo 1104625 1661063 := bstep (se 1 (by rfl) ⟨1245797, by rfl⟩ : syracuseStep 1661063 = 2491595) B2491595
theorem B1661099 : Blo 1104625 1661099 := bstep (se 1 (by rfl) ⟨1245824, by rfl⟩ : syracuseStep 1661099 = 2491649) B2491649
theorem B1398971 : Blo 1104625 1398971 := bstep (se 1 (by rfl) ⟨1049228, by rfl⟩ : syracuseStep 1398971 = 2098457) B2098457
theorem B1661129 : Blo 1104625 1661129 := bstep (se 2 (by rfl) ⟨622923, by rfl⟩ : syracuseStep 1661129 = 1245847) B1245847
theorem B1661243 : Blo 1104625 1661243 := bstep (se 1 (by rfl) ⟨1245932, by rfl⟩ : syracuseStep 1661243 = 2491865) B2491865
theorem B1661303 : Blo 1104625 1661303 := bstep (se 1 (by rfl) ⟨1245977, by rfl⟩ : syracuseStep 1661303 = 2491955) B2491955
theorem B1661327 : Blo 1104625 1661327 := bstep (se 1 (by rfl) ⟨1245995, by rfl⟩ : syracuseStep 1661327 = 2491991) B2491991
theorem B1661369 : Blo 1104625 1661369 := bstep (se 2 (by rfl) ⟨623013, by rfl⟩ : syracuseStep 1661369 = 1246027) B1246027
theorem B1661447 : Blo 1104625 1661447 := bstep (se 1 (by rfl) ⟨1246085, by rfl⟩ : syracuseStep 1661447 = 2492171) B2492171
theorem B1661483 : Blo 1104625 1661483 := bstep (se 1 (by rfl) ⟨1246112, by rfl⟩ : syracuseStep 1661483 = 2492225) B2492225
theorem B1661513 : Blo 1104625 1661513 := bstep (se 2 (by rfl) ⟨623067, by rfl⟩ : syracuseStep 1661513 = 1246135) B1246135
theorem B1661627 : Blo 1104625 1661627 := bstep (se 1 (by rfl) ⟨1246220, by rfl⟩ : syracuseStep 1661627 = 2492441) B2492441
theorem B1661687 : Blo 1104625 1661687 := bstep (se 1 (by rfl) ⟨1246265, by rfl⟩ : syracuseStep 1661687 = 2492531) B2492531
theorem B1104647 : Blo 1104625 1104647 := bstep (se 1 (by rfl) ⟨828485, by rfl⟩ : syracuseStep 1104647 = 1656971) B1656971
theorem B1104655 : Blo 1104625 1104655 := bstep (se 1 (by rfl) ⟨828491, by rfl⟩ : syracuseStep 1104655 = 1656983) B1656983
theorem B1661711 : Blo 1104625 1661711 := bstep (se 1 (by rfl) ⟨1246283, by rfl⟩ : syracuseStep 1661711 = 2492567) B2492567
theorem B1661753 : Blo 1104625 1661753 := bstep (se 2 (by rfl) ⟨623157, by rfl⟩ : syracuseStep 1661753 = 1246315) B1246315
theorem B1104699 : Blo 1104625 1104699 := bstep (se 1 (by rfl) ⟨828524, by rfl⟩ : syracuseStep 1104699 = 1657049) B1657049
theorem B1104775 : Blo 1104625 1104775 := bstep (se 1 (by rfl) ⟨828581, by rfl⟩ : syracuseStep 1104775 = 1657163) B1657163
theorem B1661831 : Blo 1104625 1661831 := bstep (se 1 (by rfl) ⟨1246373, by rfl⟩ : syracuseStep 1661831 = 2492747) B2492747
theorem B1104783 : Blo 1104625 1104783 := bstep (se 1 (by rfl) ⟨828587, by rfl⟩ : syracuseStep 1104783 = 1657175) B1657175
theorem B221076373 : Blo 1104625 221076373 := bstep (se 6 (by rfl) ⟨5181477, by rfl⟩ : syracuseStep 221076373 = 10362955) B10362955
theorem B13458329 : Blo 1104625 13458329 := bstep (se 2 (by rfl) ⟨5046873, by rfl⟩ : syracuseStep 13458329 = 10093747) B10093747
theorem B1661867 : Blo 1104625 1661867 := bstep (se 1 (by rfl) ⟨1246400, by rfl⟩ : syracuseStep 1661867 = 2492801) B2492801
theorem B1104827 : Blo 1104625 1104827 := bstep (se 1 (by rfl) ⟨828620, by rfl⟩ : syracuseStep 1104827 = 1657241) B1657241
theorem B1661897 : Blo 1104625 1661897 := bstep (se 2 (by rfl) ⟨623211, by rfl⟩ : syracuseStep 1661897 = 1246423) B1246423
theorem B1104903 : Blo 1104625 1104903 := bstep (se 1 (by rfl) ⟨828677, by rfl⟩ : syracuseStep 1104903 = 1657355) B1657355
theorem B1104911 : Blo 1104625 1104911 := bstep (se 1 (by rfl) ⟨828683, by rfl⟩ : syracuseStep 1104911 = 1657367) B1657367
theorem B1104955 : Blo 1104625 1104955 := bstep (se 1 (by rfl) ⟨828716, by rfl⟩ : syracuseStep 1104955 = 1657433) B1657433
theorem B1662011 : Blo 1104625 1662011 := bstep (se 1 (by rfl) ⟨1246508, by rfl⟩ : syracuseStep 1662011 = 2493017) B2493017
theorem B1662071 : Blo 1104625 1662071 := bstep (se 1 (by rfl) ⟨1246553, by rfl⟩ : syracuseStep 1662071 = 2493107) B2493107
theorem B1105031 : Blo 1104625 1105031 := bstep (se 1 (by rfl) ⟨828773, by rfl⟩ : syracuseStep 1105031 = 1657547) B1657547
theorem B1399943 : Blo 1104625 1399943 := bstep (se 1 (by rfl) ⟨1049957, by rfl⟩ : syracuseStep 1399943 = 2099915) B2099915
theorem B1105039 : Blo 1104625 1105039 := bstep (se 1 (by rfl) ⟨828779, by rfl⟩ : syracuseStep 1105039 = 1657559) B1657559
theorem B1662095 : Blo 1104625 1662095 := bstep (se 1 (by rfl) ⟨1246571, by rfl⟩ : syracuseStep 1662095 = 2493143) B2493143
theorem B1662137 : Blo 1104625 1662137 := bstep (se 2 (by rfl) ⟨623301, by rfl⟩ : syracuseStep 1662137 = 1246603) B1246603
theorem B1105083 : Blo 1104625 1105083 := bstep (se 1 (by rfl) ⟨828812, by rfl⟩ : syracuseStep 1105083 = 1657625) B1657625
theorem B1105159 : Blo 1104625 1105159 := bstep (se 1 (by rfl) ⟨828869, by rfl⟩ : syracuseStep 1105159 = 1657739) B1657739
theorem B1662215 : Blo 1104625 1662215 := bstep (se 1 (by rfl) ⟨1246661, by rfl⟩ : syracuseStep 1662215 = 2493323) B2493323
theorem B1105167 : Blo 1104625 1105167 := bstep (se 1 (by rfl) ⟨828875, by rfl⟩ : syracuseStep 1105167 = 1657751) B1657751
theorem B1662251 : Blo 1104625 1662251 := bstep (se 1 (by rfl) ⟨1246688, by rfl⟩ : syracuseStep 1662251 = 2493377) B2493377
theorem B1105211 : Blo 1104625 1105211 := bstep (se 1 (by rfl) ⟨828908, by rfl⟩ : syracuseStep 1105211 = 1657817) B1657817
theorem B1662281 : Blo 1104625 1662281 := bstep (se 2 (by rfl) ⟨623355, by rfl⟩ : syracuseStep 1662281 = 1246711) B1246711
theorem B1105287 : Blo 1104625 1105287 := bstep (se 1 (by rfl) ⟨828965, by rfl⟩ : syracuseStep 1105287 = 1657931) B1657931
theorem B1105295 : Blo 1104625 1105295 := bstep (se 1 (by rfl) ⟨828971, by rfl⟩ : syracuseStep 1105295 = 1657943) B1657943
theorem B7396753 : Blo 1104625 7396753 := bstep (se 2 (by rfl) ⟨2773782, by rfl⟩ : syracuseStep 7396753 = 5547565) B5547565
theorem B1105339 : Blo 1104625 1105339 := bstep (se 1 (by rfl) ⟨829004, by rfl⟩ : syracuseStep 1105339 = 1658009) B1658009
theorem B1662395 : Blo 1104625 1662395 := bstep (se 1 (by rfl) ⟨1246796, by rfl⟩ : syracuseStep 1662395 = 2493593) B2493593
theorem B1662455 : Blo 1104625 1662455 := bstep (se 1 (by rfl) ⟨1246841, by rfl⟩ : syracuseStep 1662455 = 2493683) B2493683
theorem B1105415 : Blo 1104625 1105415 := bstep (se 1 (by rfl) ⟨829061, by rfl⟩ : syracuseStep 1105415 = 1658123) B1658123
theorem B1105423 : Blo 1104625 1105423 := bstep (se 1 (by rfl) ⟨829067, by rfl⟩ : syracuseStep 1105423 = 1658135) B1658135
theorem B1662479 : Blo 1104625 1662479 := bstep (se 1 (by rfl) ⟨1246859, by rfl⟩ : syracuseStep 1662479 = 2493719) B2493719
theorem B1662521 : Blo 1104625 1662521 := bstep (se 2 (by rfl) ⟨623445, by rfl⟩ : syracuseStep 1662521 = 1246891) B1246891
theorem B1105467 : Blo 1104625 1105467 := bstep (se 1 (by rfl) ⟨829100, by rfl⟩ : syracuseStep 1105467 = 1658201) B1658201
theorem B1105543 : Blo 1104625 1105543 := bstep (se 1 (by rfl) ⟨829157, by rfl⟩ : syracuseStep 1105543 = 1658315) B1658315
theorem B1662599 : Blo 1104625 1662599 := bstep (se 1 (by rfl) ⟨1246949, by rfl⟩ : syracuseStep 1662599 = 2493899) B2493899
theorem B1105551 : Blo 1104625 1105551 := bstep (se 1 (by rfl) ⟨829163, by rfl⟩ : syracuseStep 1105551 = 1658327) B1658327
theorem B1662635 : Blo 1104625 1662635 := bstep (se 1 (by rfl) ⟨1246976, by rfl⟩ : syracuseStep 1662635 = 2493953) B2493953
theorem B1105595 : Blo 1104625 1105595 := bstep (se 1 (by rfl) ⟨829196, by rfl⟩ : syracuseStep 1105595 = 1658393) B1658393
theorem B1662665 : Blo 1104625 1662665 := bstep (se 2 (by rfl) ⟨623499, by rfl⟩ : syracuseStep 1662665 = 1246999) B1246999
theorem B7102181 : Blo 1104625 7102181 := bstep (se 4 (by rfl) ⟨665829, by rfl⟩ : syracuseStep 7102181 = 1331659) B1331659
theorem B1105671 : Blo 1104625 1105671 := bstep (se 1 (by rfl) ⟨829253, by rfl⟩ : syracuseStep 1105671 = 1658507) B1658507
theorem B11951887 : Blo 1104625 11951887 := bstep (se 1 (by rfl) ⟨8963915, by rfl⟩ : syracuseStep 11951887 = 17927831) B17927831
theorem B1105679 : Blo 1104625 1105679 := bstep (se 1 (by rfl) ⟨829259, by rfl⟩ : syracuseStep 1105679 = 1658519) B1658519
theorem B1400591 : Blo 1104625 1400591 := bstep (se 1 (by rfl) ⟨1050443, by rfl⟩ : syracuseStep 1400591 = 2100887) B2100887
theorem B1105723 : Blo 1104625 1105723 := bstep (se 1 (by rfl) ⟨829292, by rfl⟩ : syracuseStep 1105723 = 1658585) B1658585
theorem B1662779 : Blo 1104625 1662779 := bstep (se 1 (by rfl) ⟨1247084, by rfl⟩ : syracuseStep 1662779 = 2494169) B2494169
theorem B1662839 : Blo 1104625 1662839 := bstep (se 1 (by rfl) ⟨1247129, by rfl⟩ : syracuseStep 1662839 = 2494259) B2494259
theorem B1105799 : Blo 1104625 1105799 := bstep (se 1 (by rfl) ⟨829349, by rfl⟩ : syracuseStep 1105799 = 1658699) B1658699
theorem B1105807 : Blo 1104625 1105807 := bstep (se 1 (by rfl) ⟨829355, by rfl⟩ : syracuseStep 1105807 = 1658711) B1658711
theorem B1662863 : Blo 1104625 1662863 := bstep (se 1 (by rfl) ⟨1247147, by rfl⟩ : syracuseStep 1662863 = 2494295) B2494295
theorem B1662905 : Blo 1104625 1662905 := bstep (se 2 (by rfl) ⟨623589, by rfl⟩ : syracuseStep 1662905 = 1247179) B1247179
theorem B1105851 : Blo 1104625 1105851 := bstep (se 1 (by rfl) ⟨829388, by rfl⟩ : syracuseStep 1105851 = 1658777) B1658777
theorem B1105927 : Blo 1104625 1105927 := bstep (se 1 (by rfl) ⟨829445, by rfl⟩ : syracuseStep 1105927 = 1658891) B1658891
theorem B1105935 : Blo 1104625 1105935 := bstep (se 1 (by rfl) ⟨829451, by rfl⟩ : syracuseStep 1105935 = 1658903) B1658903
theorem B1105979 : Blo 1104625 1105979 := bstep (se 1 (by rfl) ⟨829484, by rfl⟩ : syracuseStep 1105979 = 1658969) B1658969
theorem B1106055 : Blo 1104625 1106055 := bstep (se 1 (by rfl) ⟨829541, by rfl⟩ : syracuseStep 1106055 = 1659083) B1659083
theorem B1106063 : Blo 1104625 1106063 := bstep (se 1 (by rfl) ⟨829547, by rfl⟩ : syracuseStep 1106063 = 1659095) B1659095
theorem B1106107 : Blo 1104625 1106107 := bstep (se 1 (by rfl) ⟨829580, by rfl⟩ : syracuseStep 1106107 = 1659161) B1659161
theorem B1106183 : Blo 1104625 1106183 := bstep (se 1 (by rfl) ⟨829637, by rfl⟩ : syracuseStep 1106183 = 1659275) B1659275
theorem B1106191 : Blo 1104625 1106191 := bstep (se 1 (by rfl) ⟨829643, by rfl⟩ : syracuseStep 1106191 = 1659287) B1659287
theorem B1106235 : Blo 1104625 1106235 := bstep (se 1 (by rfl) ⟨829676, by rfl⟩ : syracuseStep 1106235 = 1659353) B1659353
theorem B1106311 : Blo 1104625 1106311 := bstep (se 1 (by rfl) ⟨829733, by rfl⟩ : syracuseStep 1106311 = 1659467) B1659467
theorem B1106319 : Blo 1104625 1106319 := bstep (se 1 (by rfl) ⟨829739, by rfl⟩ : syracuseStep 1106319 = 1659479) B1659479
theorem B1106363 : Blo 1104625 1106363 := bstep (se 1 (by rfl) ⟨829772, by rfl⟩ : syracuseStep 1106363 = 1659545) B1659545
theorem B1106439 : Blo 1104625 1106439 := bstep (se 1 (by rfl) ⟨829829, by rfl⟩ : syracuseStep 1106439 = 1659659) B1659659
theorem B1106447 : Blo 1104625 1106447 := bstep (se 1 (by rfl) ⟨829835, by rfl⟩ : syracuseStep 1106447 = 1659671) B1659671
theorem B1106491 : Blo 1104625 1106491 := bstep (se 1 (by rfl) ⟨829868, by rfl⟩ : syracuseStep 1106491 = 1659737) B1659737
theorem B1106567 : Blo 1104625 1106567 := bstep (se 1 (by rfl) ⟨829925, by rfl⟩ : syracuseStep 1106567 = 1659851) B1659851
theorem B1106575 : Blo 1104625 1106575 := bstep (se 1 (by rfl) ⟨829931, by rfl⟩ : syracuseStep 1106575 = 1659863) B1659863
theorem B1106619 : Blo 1104625 1106619 := bstep (se 1 (by rfl) ⟨829964, by rfl⟩ : syracuseStep 1106619 = 1659929) B1659929
theorem B1106695 : Blo 1104625 1106695 := bstep (se 1 (by rfl) ⟨830021, by rfl⟩ : syracuseStep 1106695 = 1660043) B1660043
theorem B1106703 : Blo 1104625 1106703 := bstep (se 1 (by rfl) ⟨830027, by rfl⟩ : syracuseStep 1106703 = 1660055) B1660055
theorem B1106747 : Blo 1104625 1106747 := bstep (se 1 (by rfl) ⟨830060, by rfl⟩ : syracuseStep 1106747 = 1660121) B1660121
theorem B1106823 : Blo 1104625 1106823 := bstep (se 1 (by rfl) ⟨830117, by rfl⟩ : syracuseStep 1106823 = 1660235) B1660235
theorem B1106831 : Blo 1104625 1106831 := bstep (se 1 (by rfl) ⟨830123, by rfl⟩ : syracuseStep 1106831 = 1660247) B1660247
theorem B51045299 : Blo 1104625 51045299 := bstep (se 1 (by rfl) ⟨38283974, by rfl⟩ : syracuseStep 51045299 = 76567949) B76567949
theorem B1106875 : Blo 1104625 1106875 := bstep (se 1 (by rfl) ⟨830156, by rfl⟩ : syracuseStep 1106875 = 1660313) B1660313
theorem B1106951 : Blo 1104625 1106951 := bstep (se 1 (by rfl) ⟨830213, by rfl⟩ : syracuseStep 1106951 = 1660427) B1660427
theorem B1106959 : Blo 1104625 1106959 := bstep (se 1 (by rfl) ⟨830219, by rfl⟩ : syracuseStep 1106959 = 1660439) B1660439
theorem B1107003 : Blo 1104625 1107003 := bstep (se 1 (by rfl) ⟨830252, by rfl⟩ : syracuseStep 1107003 = 1660505) B1660505
theorem B1107079 : Blo 1104625 1107079 := bstep (se 1 (by rfl) ⟨830309, by rfl⟩ : syracuseStep 1107079 = 1660619) B1660619
theorem B1107087 : Blo 1104625 1107087 := bstep (se 1 (by rfl) ⟨830315, by rfl⟩ : syracuseStep 1107087 = 1660631) B1660631
theorem B1107131 : Blo 1104625 1107131 := bstep (se 1 (by rfl) ⟨830348, by rfl⟩ : syracuseStep 1107131 = 1660697) B1660697
theorem B1107207 : Blo 1104625 1107207 := bstep (se 1 (by rfl) ⟨830405, by rfl⟩ : syracuseStep 1107207 = 1660811) B1660811
theorem B1107215 : Blo 1104625 1107215 := bstep (se 1 (by rfl) ⟨830411, by rfl⟩ : syracuseStep 1107215 = 1660823) B1660823
theorem B3728699 : Blo 1104625 3728699 := bstep (se 1 (by rfl) ⟨2796524, by rfl⟩ : syracuseStep 3728699 = 5593049) B5593049
theorem B1107259 : Blo 1104625 1107259 := bstep (se 1 (by rfl) ⟨830444, by rfl⟩ : syracuseStep 1107259 = 1660889) B1660889
theorem B1107335 : Blo 1104625 1107335 := bstep (se 1 (by rfl) ⟨830501, by rfl⟩ : syracuseStep 1107335 = 1661003) B1661003
theorem B1107343 : Blo 1104625 1107343 := bstep (se 1 (by rfl) ⟨830507, by rfl⟩ : syracuseStep 1107343 = 1661015) B1661015
theorem B1107387 : Blo 1104625 1107387 := bstep (se 1 (by rfl) ⟨830540, by rfl⟩ : syracuseStep 1107387 = 1661081) B1661081
theorem B5400011 : Blo 1104625 5400011 := bstep (se 1 (by rfl) ⟨4050008, by rfl⟩ : syracuseStep 5400011 = 8100017) B8100017
theorem B1107463 : Blo 1104625 1107463 := bstep (se 1 (by rfl) ⟨830597, by rfl⟩ : syracuseStep 1107463 = 1661195) B1661195
theorem B1107471 : Blo 1104625 1107471 := bstep (se 1 (by rfl) ⟨830603, by rfl⟩ : syracuseStep 1107471 = 1661207) B1661207
theorem B1107515 : Blo 1104625 1107515 := bstep (se 1 (by rfl) ⟨830636, by rfl⟩ : syracuseStep 1107515 = 1661273) B1661273
theorem B14181965 : Blo 1104625 14181965 := bstep (se 3 (by rfl) ⟨2659118, by rfl⟩ : syracuseStep 14181965 = 5318237) B5318237
theorem B1107591 : Blo 1104625 1107591 := bstep (se 1 (by rfl) ⟨830693, by rfl⟩ : syracuseStep 1107591 = 1661387) B1661387
theorem B1107599 : Blo 1104625 1107599 := bstep (se 1 (by rfl) ⟨830699, by rfl⟩ : syracuseStep 1107599 = 1661399) B1661399
theorem B1107643 : Blo 1104625 1107643 := bstep (se 1 (by rfl) ⟨830732, by rfl⟩ : syracuseStep 1107643 = 1661465) B1661465
theorem B11364097 : Blo 1104625 11364097 := bstep (se 2 (by rfl) ⟨4261536, by rfl⟩ : syracuseStep 11364097 = 8523073) B8523073
theorem B1107719 : Blo 1104625 1107719 := bstep (se 1 (by rfl) ⟨830789, by rfl⟩ : syracuseStep 1107719 = 1661579) B1661579
theorem B1107727 : Blo 1104625 1107727 := bstep (se 1 (by rfl) ⟨830795, by rfl⟩ : syracuseStep 1107727 = 1661591) B1661591
theorem B3729185 : Blo 1104625 3729185 := bstep (se 2 (by rfl) ⟨1398444, by rfl⟩ : syracuseStep 3729185 = 2796889) B2796889
theorem B6383393 : Blo 1104625 6383393 := bstep (se 2 (by rfl) ⟨2393772, by rfl⟩ : syracuseStep 6383393 = 4787545) B4787545
theorem B1107771 : Blo 1104625 1107771 := bstep (se 1 (by rfl) ⟨830828, by rfl⟩ : syracuseStep 1107771 = 1661657) B1661657
theorem B1107847 : Blo 1104625 1107847 := bstep (se 1 (by rfl) ⟨830885, by rfl⟩ : syracuseStep 1107847 = 1661771) B1661771
theorem B1107855 : Blo 1104625 1107855 := bstep (se 1 (by rfl) ⟨830891, by rfl⟩ : syracuseStep 1107855 = 1661783) B1661783
theorem B1107899 : Blo 1104625 1107899 := bstep (se 1 (by rfl) ⟨830924, by rfl⟩ : syracuseStep 1107899 = 1661849) B1661849
theorem B1107975 : Blo 1104625 1107975 := bstep (se 1 (by rfl) ⟨830981, by rfl⟩ : syracuseStep 1107975 = 1661963) B1661963
theorem B1107983 : Blo 1104625 1107983 := bstep (se 1 (by rfl) ⟨830987, by rfl⟩ : syracuseStep 1107983 = 1661975) B1661975
theorem B1534009 : Blo 1104625 1534009 := bstep (se 2 (by rfl) ⟨575253, by rfl⟩ : syracuseStep 1534009 = 1150507) B1150507
theorem B1108027 : Blo 1104625 1108027 := bstep (se 1 (by rfl) ⟨831020, by rfl⟩ : syracuseStep 1108027 = 1662041) B1662041
theorem B1108103 : Blo 1104625 1108103 := bstep (se 1 (by rfl) ⟨831077, by rfl⟩ : syracuseStep 1108103 = 1662155) B1662155
theorem B1108111 : Blo 1104625 1108111 := bstep (se 1 (by rfl) ⟨831083, by rfl⟩ : syracuseStep 1108111 = 1662167) B1662167
theorem B1108155 : Blo 1104625 1108155 := bstep (se 1 (by rfl) ⟨831116, by rfl⟩ : syracuseStep 1108155 = 1662233) B1662233
theorem B1108231 : Blo 1104625 1108231 := bstep (se 1 (by rfl) ⟨831173, by rfl⟩ : syracuseStep 1108231 = 1662347) B1662347
theorem B1108239 : Blo 1104625 1108239 := bstep (se 1 (by rfl) ⟨831179, by rfl⟩ : syracuseStep 1108239 = 1662359) B1662359
theorem B1108283 : Blo 1104625 1108283 := bstep (se 1 (by rfl) ⟨831212, by rfl⟩ : syracuseStep 1108283 = 1662425) B1662425
theorem B3729779 : Blo 1104625 3729779 := bstep (se 1 (by rfl) ⟨2797334, by rfl⟩ : syracuseStep 3729779 = 5594669) B5594669
theorem B1108359 : Blo 1104625 1108359 := bstep (se 1 (by rfl) ⟨831269, by rfl⟩ : syracuseStep 1108359 = 1662539) B1662539
theorem B1108367 : Blo 1104625 1108367 := bstep (se 1 (by rfl) ⟨831275, by rfl⟩ : syracuseStep 1108367 = 1662551) B1662551
theorem B5597585 : Blo 1104625 5597585 := bstep (se 2 (by rfl) ⟨2099094, by rfl⟩ : syracuseStep 5597585 = 4198189) B4198189
theorem B1108411 : Blo 1104625 1108411 := bstep (se 1 (by rfl) ⟨831308, by rfl⟩ : syracuseStep 1108411 = 1662617) B1662617
theorem B1108487 : Blo 1104625 1108487 := bstep (se 1 (by rfl) ⟨831365, by rfl⟩ : syracuseStep 1108487 = 1662731) B1662731
theorem B1108495 : Blo 1104625 1108495 := bstep (se 1 (by rfl) ⟨831371, by rfl⟩ : syracuseStep 1108495 = 1662743) B1662743
theorem B1108539 : Blo 1104625 1108539 := bstep (se 1 (by rfl) ⟨831404, by rfl⟩ : syracuseStep 1108539 = 1662809) B1662809
theorem B1108615 : Blo 1104625 1108615 := bstep (se 1 (by rfl) ⟨831461, by rfl⟩ : syracuseStep 1108615 = 1662923) B1662923
theorem B1108623 : Blo 1104625 1108623 := bstep (se 1 (by rfl) ⟨831467, by rfl⟩ : syracuseStep 1108623 = 1662935) B1662935
theorem B12610241 : Blo 1104625 12610241 := bstep (se 2 (by rfl) ⟨4728840, by rfl⟩ : syracuseStep 12610241 = 9457681) B9457681
theorem B12479321 : Blo 1104625 12479321 := bstep (se 2 (by rfl) ⟨4679745, by rfl⟩ : syracuseStep 12479321 = 9359491) B9359491
theorem B2485547 : Blo 1104625 2485547 := bstep (se 1 (by rfl) ⟨1864160, by rfl⟩ : syracuseStep 2485547 = 3728321) B3728321
theorem B6385031 : Blo 1104625 6385031 := bstep (se 1 (by rfl) ⟨4788773, by rfl⟩ : syracuseStep 6385031 = 9577547) B9577547
theorem B2485907 : Blo 1104625 2485907 := bstep (se 1 (by rfl) ⟨1864430, by rfl⟩ : syracuseStep 2485907 = 3728861) B3728861
theorem B2485961 : Blo 1104625 2485961 := bstep (se 2 (by rfl) ⟨932235, by rfl⟩ : syracuseStep 2485961 = 1864471) B1864471
theorem B23949107 : Blo 1104625 23949107 := bstep (se 1 (by rfl) ⟨17961830, by rfl⟩ : syracuseStep 23949107 = 35923661) B35923661
theorem B2486663 : Blo 1104625 2486663 := bstep (se 1 (by rfl) ⟨1864997, by rfl⟩ : syracuseStep 2486663 = 3729995) B3729995
theorem B5599691 : Blo 1104625 5599691 := bstep (se 1 (by rfl) ⟨4199768, by rfl⟩ : syracuseStep 5599691 = 8399537) B8399537
theorem B17953265 : Blo 1104625 17953265 := bstep (se 2 (by rfl) ⟨6732474, by rfl⟩ : syracuseStep 17953265 = 13464949) B13464949
theorem B1864235 : Blo 1104625 1864235 := bstep (se 1 (by rfl) ⟨1398176, by rfl⟩ : syracuseStep 1864235 = 2796353) B2796353
theorem B2486843 : Blo 1104625 2486843 := bstep (se 1 (by rfl) ⟨1865132, by rfl⟩ : syracuseStep 2486843 = 3730265) B3730265
theorem B5468791 : Blo 1104625 5468791 := bstep (se 1 (by rfl) ⟨4101593, by rfl⟩ : syracuseStep 5468791 = 8203187) B8203187
theorem B2486969 : Blo 1104625 2486969 := bstep (se 2 (by rfl) ⟨932613, by rfl⟩ : syracuseStep 2486969 = 1865227) B1865227
theorem B5600015 : Blo 1104625 5600015 := bstep (se 1 (by rfl) ⟨4200011, by rfl⟩ : syracuseStep 5600015 = 8400023) B8400023
theorem B8975141 : Blo 1104625 8975141 := bstep (se 4 (by rfl) ⟨841419, by rfl⟩ : syracuseStep 8975141 = 1682839) B1682839
theorem B3732371 : Blo 1104625 3732371 := bstep (se 1 (by rfl) ⟨2799278, by rfl⟩ : syracuseStep 3732371 = 5598557) B5598557
theorem B1864633 : Blo 1104625 1864633 := bstep (se 2 (by rfl) ⟨699237, by rfl⟩ : syracuseStep 1864633 = 1398475) B1398475
theorem B2487311 : Blo 1104625 2487311 := bstep (se 1 (by rfl) ⟨1865483, by rfl⟩ : syracuseStep 2487311 = 3730967) B3730967
theorem B2487329 : Blo 1104625 2487329 := bstep (se 2 (by rfl) ⟨932748, by rfl⟩ : syracuseStep 2487329 = 1865497) B1865497
theorem B1996091 : Blo 1104625 1996091 := bstep (se 1 (by rfl) ⟨1497068, by rfl⟩ : syracuseStep 1996091 = 2994137) B2994137
theorem B2487671 : Blo 1104625 2487671 := bstep (se 1 (by rfl) ⟨1865753, by rfl⟩ : syracuseStep 2487671 = 3731507) B3731507
theorem B2487851 : Blo 1104625 2487851 := bstep (se 1 (by rfl) ⟨1865888, by rfl⟩ : syracuseStep 2487851 = 3731777) B3731777
theorem B1865335 : Blo 1104625 1865335 := bstep (se 1 (by rfl) ⟨1399001, by rfl⟩ : syracuseStep 1865335 = 2798003) B2798003
theorem B1242895 : Blo 1104625 1242895 := bstep (se 1 (by rfl) ⟨932171, by rfl⟩ : syracuseStep 1242895 = 1864343) B1864343
theorem B7567141 : Blo 1104625 7567141 := bstep (se 4 (by rfl) ⟨709419, by rfl⟩ : syracuseStep 7567141 = 1418839) B1418839
theorem B1865531 : Blo 1104625 1865531 := bstep (se 1 (by rfl) ⟨1399148, by rfl⟩ : syracuseStep 1865531 = 2798297) B2798297
theorem B5044103 : Blo 1104625 5044103 := bstep (se 1 (by rfl) ⟨3783077, by rfl⟩ : syracuseStep 5044103 = 7566155) B7566155
theorem B2488211 : Blo 1104625 2488211 := bstep (se 1 (by rfl) ⟨1866158, by rfl⟩ : syracuseStep 2488211 = 3732317) B3732317
theorem B23918489 : Blo 1104625 23918489 := bstep (se 2 (by rfl) ⟨8969433, by rfl⟩ : syracuseStep 23918489 = 17938867) B17938867
theorem B2488265 : Blo 1104625 2488265 := bstep (se 2 (by rfl) ⟨933099, by rfl⟩ : syracuseStep 2488265 = 1866199) B1866199
theorem B5601473 : Blo 1104625 5601473 := bstep (se 2 (by rfl) ⟨2100552, by rfl⟩ : syracuseStep 5601473 = 4201105) B4201105
theorem B1865929 : Blo 1104625 1865929 := bstep (se 2 (by rfl) ⟨699723, by rfl⟩ : syracuseStep 1865929 = 1399447) B1399447
theorem B1243399 : Blo 1104625 1243399 := bstep (se 1 (by rfl) ⟨932549, by rfl⟩ : syracuseStep 1243399 = 1865099) B1865099
theorem B3733775 : Blo 1104625 3733775 := bstep (se 1 (by rfl) ⟨2800331, by rfl⟩ : syracuseStep 3733775 = 5600663) B5600663
theorem B3078415 : Blo 1104625 3078415 := bstep (se 1 (by rfl) ⟨2308811, by rfl⟩ : syracuseStep 3078415 = 4617623) B4617623
theorem B22739345 : Blo 1104625 22739345 := bstep (se 2 (by rfl) ⟨8527254, by rfl⟩ : syracuseStep 22739345 = 17054509) B17054509
theorem B1243579 : Blo 1104625 1243579 := bstep (se 1 (by rfl) ⟨932684, by rfl⟩ : syracuseStep 1243579 = 1865369) B1865369
theorem B3734045 : Blo 1104625 3734045 := bstep (se 3 (by rfl) ⟨700133, by rfl⟩ : syracuseStep 3734045 = 1400267) B1400267
theorem B1997345 : Blo 1104625 1997345 := bstep (se 2 (by rfl) ⟨749004, by rfl⟩ : syracuseStep 1997345 = 1498009) B1498009
theorem B1440299 : Blo 1104625 1440299 := bstep (se 1 (by rfl) ⟨1080224, by rfl⟩ : syracuseStep 1440299 = 2160449) B2160449
theorem B2488967 : Blo 1104625 2488967 := bstep (se 1 (by rfl) ⟨1866725, by rfl⟩ : syracuseStep 2488967 = 3733451) B3733451
theorem B5045051 : Blo 1104625 5045051 := bstep (se 1 (by rfl) ⟨3783788, by rfl⟩ : syracuseStep 5045051 = 7567577) B7567577
theorem B2489147 : Blo 1104625 2489147 := bstep (se 1 (by rfl) ⟨1866860, by rfl⟩ : syracuseStep 2489147 = 3733721) B3733721
theorem B1866631 : Blo 1104625 1866631 := bstep (se 1 (by rfl) ⟨1399973, by rfl⟩ : syracuseStep 1866631 = 2799947) B2799947
theorem B1244047 : Blo 1104625 1244047 := bstep (se 1 (by rfl) ⟨933035, by rfl⟩ : syracuseStep 1244047 = 1866071) B1866071
theorem B2489273 : Blo 1104625 2489273 := bstep (se 2 (by rfl) ⟨933477, by rfl⟩ : syracuseStep 2489273 = 1866955) B1866955
theorem B2489615 : Blo 1104625 2489615 := bstep (se 1 (by rfl) ⟨1867211, by rfl⟩ : syracuseStep 2489615 = 3734423) B3734423
theorem B2489633 : Blo 1104625 2489633 := bstep (se 2 (by rfl) ⟨933612, by rfl⟩ : syracuseStep 2489633 = 1867225) B1867225
theorem B1244551 : Blo 1104625 1244551 := bstep (se 1 (by rfl) ⟨933413, by rfl⟩ : syracuseStep 1244551 = 1866827) B1866827
theorem B5111225 : Blo 1104625 5111225 := bstep (se 2 (by rfl) ⟨1916709, by rfl⟩ : syracuseStep 5111225 = 3833419) B3833419
theorem B18873809 : Blo 1104625 18873809 := bstep (se 2 (by rfl) ⟨7077678, by rfl⟩ : syracuseStep 18873809 = 14155357) B14155357
theorem B5602769 : Blo 1104625 5602769 := bstep (se 2 (by rfl) ⟨2101038, by rfl⟩ : syracuseStep 5602769 = 4202077) B4202077
theorem B1867279 : Blo 1104625 1867279 := bstep (se 1 (by rfl) ⟨1400459, by rfl⟩ : syracuseStep 1867279 = 2800919) B2800919
theorem B1244731 : Blo 1104625 1244731 := bstep (se 1 (by rfl) ⟨933548, by rfl⟩ : syracuseStep 1244731 = 1867097) B1867097
theorem B2489975 : Blo 1104625 2489975 := bstep (se 1 (by rfl) ⟨1867481, by rfl⟩ : syracuseStep 2489975 = 3734963) B3734963
theorem B2490155 : Blo 1104625 2490155 := bstep (se 1 (by rfl) ⟨1867616, by rfl⟩ : syracuseStep 2490155 = 3735233) B3735233
theorem B10649393 : Blo 1104625 10649393 := bstep (se 2 (by rfl) ⟨3993522, by rfl⟩ : syracuseStep 10649393 = 7987045) B7987045
theorem B3145625 : Blo 1104625 3145625 := bstep (se 2 (by rfl) ⟨1179609, by rfl⟩ : syracuseStep 3145625 = 2359219) B2359219
theorem B3735449 : Blo 1104625 3735449 := bstep (se 2 (by rfl) ⟨1400793, by rfl⟩ : syracuseStep 3735449 = 2801587) B2801587
theorem B2490425 : Blo 1104625 2490425 := bstep (se 2 (by rfl) ⟨933909, by rfl⟩ : syracuseStep 2490425 = 1867819) B1867819
theorem B5603417 : Blo 1104625 5603417 := bstep (se 2 (by rfl) ⟨2101281, by rfl⟩ : syracuseStep 5603417 = 4202563) B4202563
theorem B1245307 : Blo 1104625 1245307 := bstep (se 1 (by rfl) ⟨933980, by rfl⟩ : syracuseStep 1245307 = 1867961) B1867961
theorem B4554947 : Blo 1104625 4554947 := bstep (se 1 (by rfl) ⟨3416210, by rfl⟩ : syracuseStep 4554947 = 6832421) B6832421
theorem B2097515 : Blo 1104625 2097515 := bstep (se 1 (by rfl) ⟨1573136, by rfl⟩ : syracuseStep 2097515 = 3146273) B3146273
theorem B2490767 : Blo 1104625 2490767 := bstep (se 1 (by rfl) ⟨1868075, by rfl⟩ : syracuseStep 2490767 = 3736151) B3736151
theorem B2097569 : Blo 1104625 2097569 := bstep (se 2 (by rfl) ⟨786588, by rfl⟩ : syracuseStep 2097569 = 1573177) B1573177
theorem B1868251 : Blo 1104625 1868251 := bstep (se 1 (by rfl) ⟨1401188, by rfl⟩ : syracuseStep 1868251 = 2802377) B2802377
theorem B2654707 : Blo 1104625 2654707 := bstep (se 1 (by rfl) ⟨1991030, by rfl⟩ : syracuseStep 2654707 = 3982061) B3982061
theorem B3736097 : Blo 1104625 3736097 := bstep (se 2 (by rfl) ⟨1401036, by rfl⟩ : syracuseStep 3736097 = 2802073) B2802073
theorem B1245775 : Blo 1104625 1245775 := bstep (se 1 (by rfl) ⟨934331, by rfl⟩ : syracuseStep 1245775 = 1868663) B1868663
theorem B8389331 : Blo 1104625 8389331 := bstep (se 1 (by rfl) ⟨6291998, by rfl⟩ : syracuseStep 8389331 = 12583997) B12583997
theorem B2491091 : Blo 1104625 2491091 := bstep (se 1 (by rfl) ⟨1868318, by rfl⟩ : syracuseStep 2491091 = 3736637) B3736637
theorem B3146455 : Blo 1104625 3146455 := bstep (se 1 (by rfl) ⟨2359841, by rfl⟩ : syracuseStep 3146455 = 4719683) B4719683
theorem B3736313 : Blo 1104625 3736313 := bstep (se 2 (by rfl) ⟨1401117, by rfl⟩ : syracuseStep 3736313 = 2802235) B2802235
theorem B4195259 : Blo 1104625 4195259 := bstep (se 1 (by rfl) ⟨3146444, by rfl⟩ : syracuseStep 4195259 = 6292889) B6292889
theorem B3146683 : Blo 1104625 3146683 := bstep (se 1 (by rfl) ⟨2360012, by rfl⟩ : syracuseStep 3146683 = 4720025) B4720025
theorem B1246171 : Blo 1104625 1246171 := bstep (se 1 (by rfl) ⟨934628, by rfl⟩ : syracuseStep 1246171 = 1869257) B1869257
theorem B3736583 : Blo 1104625 3736583 := bstep (se 1 (by rfl) ⟨2802437, by rfl⟩ : syracuseStep 3736583 = 5604875) B5604875
theorem B3146809 : Blo 1104625 3146809 := bstep (se 2 (by rfl) ⟨1180053, by rfl⟩ : syracuseStep 3146809 = 2360107) B2360107
theorem B1868879 : Blo 1104625 1868879 := bstep (se 1 (by rfl) ⟨1401659, by rfl⟩ : syracuseStep 1868879 = 2803319) B2803319
theorem B3736691 : Blo 1104625 3736691 := bstep (se 1 (by rfl) ⟨2802518, by rfl⟩ : syracuseStep 3736691 = 5605037) B5605037
theorem B3736961 : Blo 1104625 3736961 := bstep (se 2 (by rfl) ⟨1401360, by rfl⟩ : syracuseStep 3736961 = 2802721) B2802721
theorem B16418213 : Blo 1104625 16418213 := bstep (se 4 (by rfl) ⟨1539207, by rfl⟩ : syracuseStep 16418213 = 3078415) B3078415
theorem B1246639 : Blo 1104625 1246639 := bstep (se 1 (by rfl) ⟨934979, by rfl⟩ : syracuseStep 1246639 = 1869959) B1869959
theorem B1181147 : Blo 1104625 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B2492027 : Blo 1104625 2492027 := bstep (se 1 (by rfl) ⟨1869020, by rfl⟩ : syracuseStep 2492027 = 3738041) B3738041
theorem B2492153 : Blo 1104625 2492153 := bstep (se 2 (by rfl) ⟨934557, by rfl⟩ : syracuseStep 2492153 = 1869115) B1869115
theorem B8980267 : Blo 1104625 8980267 := bstep (se 1 (by rfl) ⟨6735200, by rfl⟩ : syracuseStep 8980267 = 13470401) B13470401
theorem B12617531 : Blo 1104625 12617531 := bstep (se 1 (by rfl) ⟨9463148, by rfl⟩ : syracuseStep 12617531 = 18926297) B18926297
theorem B1247071 : Blo 1104625 1247071 := bstep (se 1 (by rfl) ⟨935303, by rfl⟩ : syracuseStep 1247071 = 1870607) B1870607
theorem B1869743 : Blo 1104625 1869743 := bstep (se 1 (by rfl) ⟨1402307, by rfl⟩ : syracuseStep 1869743 = 2804615) B2804615
theorem B2492423 : Blo 1104625 2492423 := bstep (se 1 (by rfl) ⟨1869317, by rfl⟩ : syracuseStep 2492423 = 3738635) B3738635
theorem B2099209 : Blo 1104625 2099209 := bstep (se 2 (by rfl) ⟨787203, by rfl⟩ : syracuseStep 2099209 = 1574407) B1574407
theorem B2492495 : Blo 1104625 2492495 := bstep (se 1 (by rfl) ⟨1869371, by rfl⟩ : syracuseStep 2492495 = 3738743) B3738743
theorem B27330659 : Blo 1104625 27330659 := bstep (se 1 (by rfl) ⟨20497994, by rfl⟩ : syracuseStep 27330659 = 40995989) B40995989
theorem B3737771 : Blo 1104625 3737771 := bstep (se 1 (by rfl) ⟨2803328, by rfl⟩ : syracuseStep 3737771 = 5606657) B5606657
theorem B6293821 : Blo 1104625 6293821 := bstep (se 3 (by rfl) ⟨1180091, by rfl⟩ : syracuseStep 6293821 = 2360183) B2360183
theorem B1870175 : Blo 1104625 1870175 := bstep (se 1 (by rfl) ⟨1402631, by rfl⟩ : syracuseStep 1870175 = 2805263) B2805263
theorem B3541391 : Blo 1104625 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B2492891 : Blo 1104625 2492891 := bstep (se 1 (by rfl) ⟨1869668, by rfl⟩ : syracuseStep 2492891 = 3739337) B3739337
theorem B2361953 : Blo 1104625 2361953 := bstep (se 2 (by rfl) ⟨885732, by rfl⟩ : syracuseStep 2361953 = 1771465) B1771465
theorem B3738311 : Blo 1104625 3738311 := bstep (se 1 (by rfl) ⟨2803733, by rfl⟩ : syracuseStep 3738311 = 5607467) B5607467
theorem B1870735 : Blo 1104625 1870735 := bstep (se 1 (by rfl) ⟨1403051, by rfl⟩ : syracuseStep 1870735 = 2806103) B2806103
theorem B2100143 : Blo 1104625 2100143 := bstep (se 1 (by rfl) ⟨1575107, by rfl⟩ : syracuseStep 2100143 = 3150215) B3150215
theorem B2493359 : Blo 1104625 2493359 := bstep (se 1 (by rfl) ⟨1870019, by rfl⟩ : syracuseStep 2493359 = 3740039) B3740039
theorem B36342755 : Blo 1104625 36342755 := bstep (se 1 (by rfl) ⟨27257066, by rfl⟩ : syracuseStep 36342755 = 54514133) B54514133
theorem B5311489 : Blo 1104625 5311489 := bstep (se 2 (by rfl) ⟨1991808, by rfl⟩ : syracuseStep 5311489 = 3983617) B3983617
theorem B4721665 : Blo 1104625 4721665 := bstep (se 2 (by rfl) ⟨1770624, by rfl⟩ : syracuseStep 4721665 = 3541249) B3541249
theorem B4197491 : Blo 1104625 4197491 := bstep (se 1 (by rfl) ⟨3148118, by rfl⟩ : syracuseStep 4197491 = 6296237) B6296237
theorem B2493611 : Blo 1104625 2493611 := bstep (se 1 (by rfl) ⟨1870208, by rfl⟩ : syracuseStep 2493611 = 3740417) B3740417
theorem B40930595 : Blo 1104625 40930595 := bstep (se 1 (by rfl) ⟨30697946, by rfl⟩ : syracuseStep 40930595 = 61395893) B61395893
theorem B2100667 : Blo 1104625 2100667 := bstep (se 1 (by rfl) ⟨1575500, by rfl⟩ : syracuseStep 2100667 = 3151001) B3151001
theorem B3739175 : Blo 1104625 3739175 := bstep (se 1 (by rfl) ⟨2804381, by rfl⟩ : syracuseStep 3739175 = 5608763) B5608763
theorem B22711927 : Blo 1104625 22711927 := bstep (se 1 (by rfl) ⟨17033945, by rfl⟩ : syracuseStep 22711927 = 34067891) B34067891
theorem B2363003 : Blo 1104625 2363003 := bstep (se 1 (by rfl) ⟨1772252, by rfl⟩ : syracuseStep 2363003 = 3544505) B3544505
theorem B3739283 : Blo 1104625 3739283 := bstep (se 1 (by rfl) ⟨2804462, by rfl⟩ : syracuseStep 3739283 = 5608925) B5608925
theorem B1773227 : Blo 1104625 1773227 := bstep (se 1 (by rfl) ⟨1329920, by rfl⟩ : syracuseStep 1773227 = 2659841) B2659841
theorem B8982215 : Blo 1104625 8982215 := bstep (se 1 (by rfl) ⟨6736661, by rfl⟩ : syracuseStep 8982215 = 13473323) B13473323
theorem B2494151 : Blo 1104625 2494151 := bstep (se 1 (by rfl) ⟨1870613, by rfl⟩ : syracuseStep 2494151 = 3741227) B3741227
theorem B3739499 : Blo 1104625 3739499 := bstep (se 1 (by rfl) ⟨2804624, by rfl⟩ : syracuseStep 3739499 = 5609249) B5609249
theorem B9441143 : Blo 1104625 9441143 := bstep (se 1 (by rfl) ⟨7080857, by rfl⟩ : syracuseStep 9441143 = 14161715) B14161715
theorem B2101153 : Blo 1104625 2101153 := bstep (se 2 (by rfl) ⟨787932, by rfl⟩ : syracuseStep 2101153 = 1575865) B1575865
theorem B3739553 : Blo 1104625 3739553 := bstep (se 2 (by rfl) ⟨1402332, by rfl⟩ : syracuseStep 3739553 = 2804665) B2804665
theorem B1183663 : Blo 1104625 1183663 := bstep (se 1 (by rfl) ⟨887747, by rfl⟩ : syracuseStep 1183663 = 1775495) B1775495
theorem B8392733 : Blo 1104625 8392733 := bstep (se 3 (by rfl) ⟨1573637, by rfl⟩ : syracuseStep 8392733 = 3147275) B3147275
theorem B5312873 : Blo 1104625 5312873 := bstep (se 2 (by rfl) ⟨1992327, by rfl⟩ : syracuseStep 5312873 = 3984655) B3984655
theorem B1577323 : Blo 1104625 1577323 := bstep (se 1 (by rfl) ⟨1182992, by rfl⟩ : syracuseStep 1577323 = 2365985) B2365985
theorem B3740147 : Blo 1104625 3740147 := bstep (se 1 (by rfl) ⟨2805110, by rfl⟩ : syracuseStep 3740147 = 5610221) B5610221
theorem B1577551 : Blo 1104625 1577551 := bstep (se 1 (by rfl) ⟨1183163, by rfl⟩ : syracuseStep 1577551 = 2366327) B2366327
theorem B4199161 : Blo 1104625 4199161 := bstep (se 2 (by rfl) ⟨1574685, by rfl⟩ : syracuseStep 4199161 = 3149371) B3149371
theorem B3543851 : Blo 1104625 3543851 := bstep (se 1 (by rfl) ⟨2657888, by rfl⟩ : syracuseStep 3543851 = 5315777) B5315777
theorem B14160689 : Blo 1104625 14160689 := bstep (se 2 (by rfl) ⟨5310258, by rfl⟩ : syracuseStep 14160689 = 10620517) B10620517
theorem B3740687 : Blo 1104625 3740687 := bstep (se 1 (by rfl) ⟨2805515, by rfl⟩ : syracuseStep 3740687 = 5611031) B5611031
theorem B5608601 : Blo 1104625 5608601 := bstep (se 2 (by rfl) ⟨2103225, by rfl⟩ : syracuseStep 5608601 = 4206451) B4206451
theorem B3151399 : Blo 1104625 3151399 := bstep (se 1 (by rfl) ⟨2363549, by rfl⟩ : syracuseStep 3151399 = 4727099) B4727099
theorem B2364967 : Blo 1104625 2364967 := bstep (se 1 (by rfl) ⟨1773725, by rfl⟩ : syracuseStep 2364967 = 3547451) B3547451
theorem B14358059 : Blo 1104625 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B3151457 : Blo 1104625 3151457 := bstep (se 2 (by rfl) ⟨1181796, by rfl⟩ : syracuseStep 3151457 = 2363593) B2363593
theorem B3741281 : Blo 1104625 3741281 := bstep (se 2 (by rfl) ⟨1402980, by rfl⟩ : syracuseStep 3741281 = 2805961) B2805961
theorem B2365139 : Blo 1104625 2365139 := bstep (se 1 (by rfl) ⟨1773854, by rfl⟩ : syracuseStep 2365139 = 3547709) B3547709
theorem B4265801 : Blo 1104625 4265801 := bstep (se 2 (by rfl) ⟨1599675, by rfl⟩ : syracuseStep 4265801 = 3199351) B3199351
theorem B7575457 : Blo 1104625 7575457 := bstep (se 2 (by rfl) ⟨2840796, by rfl⟩ : syracuseStep 7575457 = 5681593) B5681593
theorem B4200605 : Blo 1104625 4200605 := bstep (se 3 (by rfl) ⟨787613, by rfl⟩ : syracuseStep 4200605 = 1575227) B1575227
theorem B4200619 : Blo 1104625 4200619 := bstep (se 1 (by rfl) ⟨3150464, by rfl⟩ : syracuseStep 4200619 = 6300929) B6300929
theorem B2103545 : Blo 1104625 2103545 := bstep (se 2 (by rfl) ⟨788829, by rfl⟩ : syracuseStep 2103545 = 1577659) B1577659
theorem B2103727 : Blo 1104625 2103727 := bstep (se 1 (by rfl) ⟨1577795, by rfl⟩ : syracuseStep 2103727 = 3155591) B3155591
theorem B4200923 : Blo 1104625 4200923 := bstep (se 1 (by rfl) ⟨3150692, by rfl⟩ : syracuseStep 4200923 = 6301385) B6301385
theorem B3545633 : Blo 1104625 3545633 := bstep (se 2 (by rfl) ⟨1329612, by rfl⟩ : syracuseStep 3545633 = 2659225) B2659225
theorem B2103887 : Blo 1104625 2103887 := bstep (se 1 (by rfl) ⟨1577915, by rfl⟩ : syracuseStep 2103887 = 3155831) B3155831
theorem B3840797 : Blo 1104625 3840797 := bstep (se 3 (by rfl) ⟨720149, by rfl⟩ : syracuseStep 3840797 = 1440299) B1440299
theorem B3546119 : Blo 1104625 3546119 := bstep (se 1 (by rfl) ⟨2659589, by rfl⟩ : syracuseStep 3546119 = 5319179) B5319179
theorem B2366471 : Blo 1104625 2366471 := bstep (se 1 (by rfl) ⟨1774853, by rfl⟩ : syracuseStep 2366471 = 3549707) B3549707
theorem B3152915 : Blo 1104625 3152915 := bstep (se 1 (by rfl) ⟨2364686, by rfl⟩ : syracuseStep 3152915 = 4729373) B4729373
theorem B15966071 : Blo 1104625 15966071 := bstep (se 1 (by rfl) ⟨11974553, by rfl⟩ : syracuseStep 15966071 = 23949107) B23949107
theorem B2695175 : Blo 1104625 2695175 := bstep (se 1 (by rfl) ⟨2021381, by rfl⟩ : syracuseStep 2695175 = 4042763) B4042763
theorem B8397107 : Blo 1104625 8397107 := bstep (se 1 (by rfl) ⟨6297830, by rfl⟩ : syracuseStep 8397107 = 12595661) B12595661
theorem B11968843 : Blo 1104625 11968843 := bstep (se 1 (by rfl) ⟨8976632, by rfl⟩ : syracuseStep 11968843 = 17953265) B17953265
theorem B4203521 : Blo 1104625 4203521 := bstep (se 2 (by rfl) ⟨1576320, by rfl⟩ : syracuseStep 4203521 = 3152641) B3152641
theorem B4203535 : Blo 1104625 4203535 := bstep (se 1 (by rfl) ⟨3152651, by rfl⟩ : syracuseStep 4203535 = 6305303) B6305303
theorem B40412357 : Blo 1104625 40412357 := bstep (se 4 (by rfl) ⟨3788658, by rfl⟩ : syracuseStep 40412357 = 7577317) B7577317
theorem B53880025 : Blo 1104625 53880025 := bstep (se 2 (by rfl) ⟨20205009, by rfl⟩ : syracuseStep 53880025 = 40410019) B40410019
theorem B5383415 : Blo 1104625 5383415 := bstep (se 1 (by rfl) ⟨4037561, by rfl⟩ : syracuseStep 5383415 = 8075123) B8075123
theorem B3155705 : Blo 1104625 3155705 := bstep (se 2 (by rfl) ⟨1183389, by rfl⟩ : syracuseStep 3155705 = 2366779) B2366779
theorem B7087931 : Blo 1104625 7087931 := bstep (se 1 (by rfl) ⟨5315948, by rfl⟩ : syracuseStep 7087931 = 10631897) B10631897
theorem B7972769 : Blo 1104625 7972769 := bstep (se 2 (by rfl) ⟨2989788, by rfl⟩ : syracuseStep 7972769 = 5979577) B5979577
theorem B3156047 : Blo 1104625 3156047 := bstep (se 1 (by rfl) ⟨2367035, by rfl⟩ : syracuseStep 3156047 = 4734071) B4734071
theorem B4204811 : Blo 1104625 4204811 := bstep (se 1 (by rfl) ⟨3153608, by rfl⟩ : syracuseStep 4204811 = 6307217) B6307217
theorem B15935849 : Blo 1104625 15935849 := bstep (se 2 (by rfl) ⟨5975943, by rfl⟩ : syracuseStep 15935849 = 11951887) B11951887
theorem B3549835 : Blo 1104625 3549835 := bstep (se 1 (by rfl) ⟨2662376, by rfl⟩ : syracuseStep 3549835 = 5324753) B5324753
theorem B4205267 : Blo 1104625 4205267 := bstep (se 1 (by rfl) ⟨3153950, by rfl⟩ : syracuseStep 4205267 = 6307901) B6307901
theorem B3549911 : Blo 1104625 3549911 := bstep (se 1 (by rfl) ⟨2662433, by rfl⟩ : syracuseStep 3549911 = 5324867) B5324867
theorem B2796383 : Blo 1104625 2796383 := bstep (se 1 (by rfl) ⟨2097287, by rfl⟩ : syracuseStep 2796383 = 4194575) B4194575
theorem B14200055 : Blo 1104625 14200055 := bstep (se 1 (by rfl) ⟨10650041, by rfl⟩ : syracuseStep 14200055 = 21300083) B21300083
theorem B2272607 : Blo 1104625 2272607 := bstep (se 1 (by rfl) ⟨1704455, by rfl⟩ : syracuseStep 2272607 = 3408911) B3408911
theorem B8072893 : Blo 1104625 8072893 := bstep (se 3 (by rfl) ⟨1513667, by rfl⟩ : syracuseStep 8072893 = 3027335) B3027335
theorem B4206269 : Blo 1104625 4206269 := bstep (se 3 (by rfl) ⟨788675, by rfl⟩ : syracuseStep 4206269 = 1577351) B1577351
theorem B2797487 : Blo 1104625 2797487 := bstep (se 1 (by rfl) ⟨2098115, by rfl⟩ : syracuseStep 2797487 = 4196231) B4196231
theorem B9580625 : Blo 1104625 9580625 := bstep (se 2 (by rfl) ⟨3592734, by rfl⟩ : syracuseStep 9580625 = 7185469) B7185469
theorem B15152129 : Blo 1104625 15152129 := bstep (se 2 (by rfl) ⟨5682048, by rfl⟩ : syracuseStep 15152129 = 11364097) B11364097
theorem B2798671 : Blo 1104625 2798671 := bstep (se 1 (by rfl) ⟨2099003, by rfl⟩ : syracuseStep 2798671 = 4198007) B4198007
theorem B4207697 : Blo 1104625 4207697 := bstep (se 2 (by rfl) ⟨1577886, by rfl⟩ : syracuseStep 4207697 = 3155773) B3155773
theorem B36353195 : Blo 1104625 36353195 := bstep (se 1 (by rfl) ⟨27264896, by rfl⟩ : syracuseStep 36353195 = 54529793) B54529793
theorem B8959247 : Blo 1104625 8959247 := bstep (se 1 (by rfl) ⟨6719435, by rfl⟩ : syracuseStep 8959247 = 13438871) B13438871
theorem B2045345 : Blo 1104625 2045345 := bstep (se 2 (by rfl) ⟨767004, by rfl⟩ : syracuseStep 2045345 = 1534009) B1534009
theorem B9450917 : Blo 1104625 9450917 := bstep (se 4 (by rfl) ⟨886023, by rfl⟩ : syracuseStep 9450917 = 1772047) B1772047
theorem B7091621 : Blo 1104625 7091621 := bstep (se 4 (by rfl) ⟨664839, by rfl⟩ : syracuseStep 7091621 = 1329679) B1329679
theorem B14169815 : Blo 1104625 14169815 := bstep (se 1 (by rfl) ⟨10627361, by rfl⟩ : syracuseStep 14169815 = 21254723) B21254723
theorem B2799319 : Blo 1104625 2799319 := bstep (se 1 (by rfl) ⟨2099489, by rfl⟩ : syracuseStep 2799319 = 4198979) B4198979
theorem B2799623 : Blo 1104625 2799623 := bstep (se 1 (by rfl) ⟨2099717, by rfl⟩ : syracuseStep 2799623 = 4199435) B4199435
theorem B7977037 : Blo 1104625 7977037 := bstep (se 3 (by rfl) ⟨1495694, by rfl⟩ : syracuseStep 7977037 = 2991389) B2991389
theorem B4044971 : Blo 1104625 4044971 := bstep (se 1 (by rfl) ⟨3033728, by rfl⟩ : syracuseStep 4044971 = 6067457) B6067457
theorem B2242991 : Blo 1104625 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B4209185 : Blo 1104625 4209185 := bstep (se 2 (by rfl) ⟨1578444, by rfl⟩ : syracuseStep 4209185 = 3156889) B3156889
theorem B7584961 : Blo 1104625 7584961 := bstep (se 2 (by rfl) ⟨2844360, by rfl⟩ : syracuseStep 7584961 = 5688721) B5688721
theorem B8404397 : Blo 1104625 8404397 := bstep (se 3 (by rfl) ⟨1575824, by rfl⟩ : syracuseStep 8404397 = 3151649) B3151649
theorem B5684681 : Blo 1104625 5684681 := bstep (se 2 (by rfl) ⟨2131755, by rfl⟩ : syracuseStep 5684681 = 4263511) B4263511
theorem B4734787 : Blo 1104625 4734787 := bstep (se 1 (by rfl) ⟨3551090, by rfl⟩ : syracuseStep 4734787 = 7102181) B7102181
theorem B2801911 : Blo 1104625 2801911 := bstep (se 1 (by rfl) ⟨2101433, by rfl⟩ : syracuseStep 2801911 = 4202867) B4202867
theorem B12763453 : Blo 1104625 12763453 := bstep (se 3 (by rfl) ⟨2393147, by rfl⟩ : syracuseStep 12763453 = 4786295) B4786295
theorem B2244937 : Blo 1104625 2244937 := bstep (se 2 (by rfl) ⟨841851, by rfl⟩ : syracuseStep 2244937 = 1683703) B1683703
theorem B2802185 : Blo 1104625 2802185 := bstep (se 2 (by rfl) ⟨1050819, by rfl⟩ : syracuseStep 2802185 = 2101639) B2101639
theorem B2802215 : Blo 1104625 2802215 := bstep (se 1 (by rfl) ⟨2101661, by rfl⟩ : syracuseStep 2802215 = 4203323) B4203323
theorem B34030199 : Blo 1104625 34030199 := bstep (se 1 (by rfl) ⟨25522649, by rfl⟩ : syracuseStep 34030199 = 51045299) B51045299
theorem B7291721 : Blo 1104625 7291721 := bstep (se 2 (by rfl) ⟨2734395, by rfl⟩ : syracuseStep 7291721 = 5468791) B5468791
theorem B2802539 : Blo 1104625 2802539 := bstep (se 1 (by rfl) ⟨2101904, by rfl⟩ : syracuseStep 2802539 = 4203809) B4203809
theorem B9454643 : Blo 1104625 9454643 := bstep (se 1 (by rfl) ⟨7090982, by rfl⟩ : syracuseStep 9454643 = 14181965) B14181965
theorem B3982493 : Blo 1104625 3982493 := bstep (se 3 (by rfl) ⟨746717, by rfl⟩ : syracuseStep 3982493 = 1493435) B1493435
theorem B8078717 : Blo 1104625 8078717 := bstep (se 3 (by rfl) ⟨1514759, by rfl⟩ : syracuseStep 8078717 = 3029519) B3029519
theorem B10077659 : Blo 1104625 10077659 := bstep (se 1 (by rfl) ⟨7558244, by rfl⟩ : syracuseStep 10077659 = 15116489) B15116489
theorem B2803187 : Blo 1104625 2803187 := bstep (se 1 (by rfl) ⟨2102390, by rfl⟩ : syracuseStep 2803187 = 4204781) B4204781
theorem B34129451 : Blo 1104625 34129451 := bstep (se 1 (by rfl) ⟨25597088, by rfl⟩ : syracuseStep 34129451 = 51194177) B51194177
theorem B8406827 : Blo 1104625 8406827 := bstep (se 1 (by rfl) ⟨6305120, by rfl⟩ : syracuseStep 8406827 = 12610241) B12610241
theorem B2803643 : Blo 1104625 2803643 := bstep (se 1 (by rfl) ⟨2102732, by rfl⟩ : syracuseStep 2803643 = 4205465) B4205465
theorem B1657031 : Blo 1104625 1657031 := bstep (se 1 (by rfl) ⟨1242773, by rfl⟩ : syracuseStep 1657031 = 2485547) B2485547
theorem B1657193 : Blo 1104625 1657193 := bstep (se 2 (by rfl) ⟨621447, by rfl⟩ : syracuseStep 1657193 = 1242895) B1242895
theorem B1657271 : Blo 1104625 1657271 := bstep (se 1 (by rfl) ⟨1242953, by rfl⟩ : syracuseStep 1657271 = 2485907) B2485907
theorem B1657307 : Blo 1104625 1657307 := bstep (se 1 (by rfl) ⟨1242980, by rfl⟩ : syracuseStep 1657307 = 2485961) B2485961
theorem B1493467 : Blo 1104625 1493467 := bstep (se 1 (by rfl) ⟨1120100, by rfl⟩ : syracuseStep 1493467 = 2240201) B2240201
theorem B2804321 : Blo 1104625 2804321 := bstep (se 2 (by rfl) ⟨1051620, by rfl⟩ : syracuseStep 2804321 = 2103241) B2103241
theorem B1657775 : Blo 1104625 1657775 := bstep (se 1 (by rfl) ⟨1243331, by rfl⟩ : syracuseStep 1657775 = 2486663) B2486663
theorem B1657865 : Blo 1104625 1657865 := bstep (se 2 (by rfl) ⟨621699, by rfl⟩ : syracuseStep 1657865 = 1243399) B1243399
theorem B1657895 : Blo 1104625 1657895 := bstep (se 1 (by rfl) ⟨1243421, by rfl⟩ : syracuseStep 1657895 = 2486843) B2486843
theorem B8965187 : Blo 1104625 8965187 := bstep (se 1 (by rfl) ⟨6723890, by rfl⟩ : syracuseStep 8965187 = 13447781) B13447781
theorem B1657979 : Blo 1104625 1657979 := bstep (se 1 (by rfl) ⟨1243484, by rfl⟩ : syracuseStep 1657979 = 2486969) B2486969
theorem B5983427 : Blo 1104625 5983427 := bstep (se 1 (by rfl) ⟨4487570, by rfl⟩ : syracuseStep 5983427 = 8975141) B8975141
theorem B1658105 : Blo 1104625 1658105 := bstep (se 2 (by rfl) ⟨621789, by rfl⟩ : syracuseStep 1658105 = 1243579) B1243579
theorem B1658207 : Blo 1104625 1658207 := bstep (se 1 (by rfl) ⟨1243655, by rfl⟩ : syracuseStep 1658207 = 2487311) B2487311
theorem B1658219 : Blo 1104625 1658219 := bstep (se 1 (by rfl) ⟨1243664, by rfl⟩ : syracuseStep 1658219 = 2487329) B2487329
theorem B36359597 : Blo 1104625 36359597 := bstep (se 3 (by rfl) ⟨6817424, by rfl⟩ : syracuseStep 36359597 = 13634849) B13634849
theorem B1330727 : Blo 1104625 1330727 := bstep (se 1 (by rfl) ⟨998045, by rfl⟩ : syracuseStep 1330727 = 1996091) B1996091
theorem B1658447 : Blo 1104625 1658447 := bstep (se 1 (by rfl) ⟨1243835, by rfl⟩ : syracuseStep 1658447 = 2487671) B2487671
theorem B1658567 : Blo 1104625 1658567 := bstep (se 1 (by rfl) ⟨1243925, by rfl⟩ : syracuseStep 1658567 = 2487851) B2487851
theorem B1658729 : Blo 1104625 1658729 := bstep (se 2 (by rfl) ⟨622023, by rfl⟩ : syracuseStep 1658729 = 1244047) B1244047
theorem B294768497 : Blo 1104625 294768497 := bstep (se 2 (by rfl) ⟨110538186, by rfl⟩ : syracuseStep 294768497 = 221076373) B221076373
theorem B26922887 : Blo 1104625 26922887 := bstep (se 1 (by rfl) ⟨20192165, by rfl⟩ : syracuseStep 26922887 = 40384331) B40384331
theorem B3362735 : Blo 1104625 3362735 := bstep (se 1 (by rfl) ⟨2522051, by rfl⟩ : syracuseStep 3362735 = 5044103) B5044103
theorem B1658807 : Blo 1104625 1658807 := bstep (se 1 (by rfl) ⟨1244105, by rfl⟩ : syracuseStep 1658807 = 2488211) B2488211
theorem B15945659 : Blo 1104625 15945659 := bstep (se 1 (by rfl) ⟨11959244, by rfl⟩ : syracuseStep 15945659 = 23918489) B23918489
theorem B1658843 : Blo 1104625 1658843 := bstep (se 1 (by rfl) ⟨1244132, by rfl⟩ : syracuseStep 1658843 = 2488265) B2488265
theorem B1495003 : Blo 1104625 1495003 := bstep (se 1 (by rfl) ⟨1121252, by rfl⟩ : syracuseStep 1495003 = 2242505) B2242505
theorem B2805779 : Blo 1104625 2805779 := bstep (se 1 (by rfl) ⟨2104334, by rfl⟩ : syracuseStep 2805779 = 4208669) B4208669
theorem B15159563 : Blo 1104625 15159563 := bstep (se 1 (by rfl) ⟨11369672, by rfl⟩ : syracuseStep 15159563 = 22739345) B22739345
theorem B1331563 : Blo 1104625 1331563 := bstep (se 1 (by rfl) ⟨998672, by rfl⟩ : syracuseStep 1331563 = 1997345) B1997345
theorem B1659311 : Blo 1104625 1659311 := bstep (se 1 (by rfl) ⟨1244483, by rfl⟩ : syracuseStep 1659311 = 2488967) B2488967
theorem B1659401 : Blo 1104625 1659401 := bstep (se 2 (by rfl) ⟨622275, by rfl⟩ : syracuseStep 1659401 = 1244551) B1244551
theorem B3363367 : Blo 1104625 3363367 := bstep (se 1 (by rfl) ⟨2522525, by rfl⟩ : syracuseStep 3363367 = 5045051) B5045051
theorem B1659431 : Blo 1104625 1659431 := bstep (se 1 (by rfl) ⟨1244573, by rfl⟩ : syracuseStep 1659431 = 2489147) B2489147
theorem B1659515 : Blo 1104625 1659515 := bstep (se 1 (by rfl) ⟨1244636, by rfl⟩ : syracuseStep 1659515 = 2489273) B2489273
theorem B1659641 : Blo 1104625 1659641 := bstep (se 2 (by rfl) ⟨622365, by rfl⟩ : syracuseStep 1659641 = 1244731) B1244731
theorem B1659743 : Blo 1104625 1659743 := bstep (se 1 (by rfl) ⟨1244807, by rfl⟩ : syracuseStep 1659743 = 2489615) B2489615
theorem B1659755 : Blo 1104625 1659755 := bstep (se 1 (by rfl) ⟨1244816, by rfl⟩ : syracuseStep 1659755 = 2489633) B2489633
theorem B1659983 : Blo 1104625 1659983 := bstep (se 1 (by rfl) ⟨1244987, by rfl⟩ : syracuseStep 1659983 = 2489975) B2489975
theorem B1660103 : Blo 1104625 1660103 := bstep (se 1 (by rfl) ⟨1245077, by rfl⟩ : syracuseStep 1660103 = 2490155) B2490155
theorem B7099595 : Blo 1104625 7099595 := bstep (se 1 (by rfl) ⟨5324696, by rfl⟩ : syracuseStep 7099595 = 10649393) B10649393
theorem B1660265 : Blo 1104625 1660265 := bstep (se 2 (by rfl) ⟨622599, by rfl⟩ : syracuseStep 1660265 = 1245199) B1245199
theorem B1496495 : Blo 1104625 1496495 := bstep (se 1 (by rfl) ⟨1122371, by rfl⟩ : syracuseStep 1496495 = 2244743) B2244743
theorem B1660343 : Blo 1104625 1660343 := bstep (se 1 (by rfl) ⟨1245257, by rfl⟩ : syracuseStep 1660343 = 2490515) B2490515
theorem B1660379 : Blo 1104625 1660379 := bstep (se 1 (by rfl) ⟨1245284, by rfl⟩ : syracuseStep 1660379 = 2490569) B2490569
theorem B5592563 : Blo 1104625 5592563 := bstep (se 1 (by rfl) ⟨4194422, by rfl⟩ : syracuseStep 5592563 = 8388845) B8388845
theorem B34100797 : Blo 1104625 34100797 := bstep (se 3 (by rfl) ⟨6393899, by rfl⟩ : syracuseStep 34100797 = 12787799) B12787799
theorem B1398703 : Blo 1104625 1398703 := bstep (se 1 (by rfl) ⟨1049027, by rfl⟩ : syracuseStep 1398703 = 2098055) B2098055
theorem B1660847 : Blo 1104625 1660847 := bstep (se 1 (by rfl) ⟨1245635, by rfl⟩ : syracuseStep 1660847 = 2491271) B2491271
theorem B9459665 : Blo 1104625 9459665 := bstep (se 2 (by rfl) ⟨3547374, by rfl⟩ : syracuseStep 9459665 = 7094749) B7094749
theorem B1660937 : Blo 1104625 1660937 := bstep (se 2 (by rfl) ⟨622851, by rfl⟩ : syracuseStep 1660937 = 1245703) B1245703
theorem B1660967 : Blo 1104625 1660967 := bstep (se 1 (by rfl) ⟨1245725, by rfl⟩ : syracuseStep 1660967 = 2491451) B2491451
theorem B1661051 : Blo 1104625 1661051 := bstep (se 1 (by rfl) ⟨1245788, by rfl⟩ : syracuseStep 1661051 = 2491577) B2491577
theorem B1661177 : Blo 1104625 1661177 := bstep (se 2 (by rfl) ⟨622941, by rfl⟩ : syracuseStep 1661177 = 1245883) B1245883
theorem B1661279 : Blo 1104625 1661279 := bstep (se 1 (by rfl) ⟨1245959, by rfl⟩ : syracuseStep 1661279 = 2491919) B2491919
theorem B1661291 : Blo 1104625 1661291 := bstep (se 1 (by rfl) ⟨1245968, by rfl⟩ : syracuseStep 1661291 = 2491937) B2491937
theorem B31938947 : Blo 1104625 31938947 := bstep (se 1 (by rfl) ⟨23954210, by rfl⟩ : syracuseStep 31938947 = 47908421) B47908421
theorem B49109579 : Blo 1104625 49109579 := bstep (se 1 (by rfl) ⟨36832184, by rfl⟩ : syracuseStep 49109579 = 73664369) B73664369
theorem B1661519 : Blo 1104625 1661519 := bstep (se 1 (by rfl) ⟨1246139, by rfl⟩ : syracuseStep 1661519 = 2492279) B2492279
theorem B1661639 : Blo 1104625 1661639 := bstep (se 1 (by rfl) ⟨1246229, by rfl⟩ : syracuseStep 1661639 = 2492459) B2492459
theorem B3988217 : Blo 1104625 3988217 := bstep (se 2 (by rfl) ⟨1495581, by rfl⟩ : syracuseStep 3988217 = 2991163) B2991163
theorem B5593859 : Blo 1104625 5593859 := bstep (se 1 (by rfl) ⟨4195394, by rfl⟩ : syracuseStep 5593859 = 8390789) B8390789
theorem B1104679 : Blo 1104625 1104679 := bstep (se 1 (by rfl) ⟨828509, by rfl⟩ : syracuseStep 1104679 = 1657019) B1657019
theorem B1104719 : Blo 1104625 1104719 := bstep (se 1 (by rfl) ⟨828539, by rfl⟩ : syracuseStep 1104719 = 1657079) B1657079
theorem B1104735 : Blo 1104625 1104735 := bstep (se 1 (by rfl) ⟨828551, by rfl⟩ : syracuseStep 1104735 = 1657103) B1657103
theorem B1661801 : Blo 1104625 1661801 := bstep (se 2 (by rfl) ⟨623175, by rfl⟩ : syracuseStep 1661801 = 1246351) B1246351
theorem B1104763 : Blo 1104625 1104763 := bstep (se 1 (by rfl) ⟨828572, by rfl⟩ : syracuseStep 1104763 = 1657145) B1657145
theorem B1104815 : Blo 1104625 1104815 := bstep (se 1 (by rfl) ⟨828611, by rfl⟩ : syracuseStep 1104815 = 1657223) B1657223
theorem B1661879 : Blo 1104625 1661879 := bstep (se 1 (by rfl) ⟨1246409, by rfl⟩ : syracuseStep 1661879 = 2492819) B2492819
theorem B1104839 : Blo 1104625 1104839 := bstep (se 1 (by rfl) ⟨828629, by rfl⟩ : syracuseStep 1104839 = 1657259) B1657259
theorem B1104859 : Blo 1104625 1104859 := bstep (se 1 (by rfl) ⟨828644, by rfl⟩ : syracuseStep 1104859 = 1657289) B1657289
theorem B1399771 : Blo 1104625 1399771 := bstep (se 1 (by rfl) ⟨1049828, by rfl⟩ : syracuseStep 1399771 = 2099657) B2099657
theorem B1661915 : Blo 1104625 1661915 := bstep (se 1 (by rfl) ⟨1246436, by rfl⟩ : syracuseStep 1661915 = 2492873) B2492873
theorem B1104935 : Blo 1104625 1104935 := bstep (se 1 (by rfl) ⟨828701, by rfl⟩ : syracuseStep 1104935 = 1657403) B1657403
theorem B1104975 : Blo 1104625 1104975 := bstep (se 1 (by rfl) ⟨828731, by rfl⟩ : syracuseStep 1104975 = 1657463) B1657463
theorem B1104991 : Blo 1104625 1104991 := bstep (se 1 (by rfl) ⟨828743, by rfl⟩ : syracuseStep 1104991 = 1657487) B1657487
theorem B1105019 : Blo 1104625 1105019 := bstep (se 1 (by rfl) ⟨828764, by rfl⟩ : syracuseStep 1105019 = 1657529) B1657529
theorem B1105071 : Blo 1104625 1105071 := bstep (se 1 (by rfl) ⟨828803, by rfl⟩ : syracuseStep 1105071 = 1657607) B1657607
theorem B1105095 : Blo 1104625 1105095 := bstep (se 1 (by rfl) ⟨828821, by rfl⟩ : syracuseStep 1105095 = 1657643) B1657643
theorem B1105115 : Blo 1104625 1105115 := bstep (se 1 (by rfl) ⟨828836, by rfl⟩ : syracuseStep 1105115 = 1657673) B1657673
theorem B1105191 : Blo 1104625 1105191 := bstep (se 1 (by rfl) ⟨828893, by rfl⟩ : syracuseStep 1105191 = 1657787) B1657787
theorem B1105231 : Blo 1104625 1105231 := bstep (se 1 (by rfl) ⟨828923, by rfl⟩ : syracuseStep 1105231 = 1657847) B1657847
theorem B1105247 : Blo 1104625 1105247 := bstep (se 1 (by rfl) ⟨828935, by rfl⟩ : syracuseStep 1105247 = 1657871) B1657871
theorem B1105275 : Blo 1104625 1105275 := bstep (se 1 (by rfl) ⟨828956, by rfl⟩ : syracuseStep 1105275 = 1657913) B1657913
theorem B1105327 : Blo 1104625 1105327 := bstep (se 1 (by rfl) ⟨828995, by rfl⟩ : syracuseStep 1105327 = 1657991) B1657991
theorem B1662383 : Blo 1104625 1662383 := bstep (se 1 (by rfl) ⟨1246787, by rfl⟩ : syracuseStep 1662383 = 2493575) B2493575
theorem B1105351 : Blo 1104625 1105351 := bstep (se 1 (by rfl) ⟨829013, by rfl⟩ : syracuseStep 1105351 = 1658027) B1658027
theorem B1105371 : Blo 1104625 1105371 := bstep (se 1 (by rfl) ⟨829028, by rfl⟩ : syracuseStep 1105371 = 1658057) B1658057
theorem B8412659 : Blo 1104625 8412659 := bstep (se 1 (by rfl) ⟨6309494, by rfl⟩ : syracuseStep 8412659 = 12618989) B12618989
theorem B1662473 : Blo 1104625 1662473 := bstep (se 2 (by rfl) ⟨623427, by rfl⟩ : syracuseStep 1662473 = 1246855) B1246855
theorem B1105447 : Blo 1104625 1105447 := bstep (se 1 (by rfl) ⟨829085, by rfl⟩ : syracuseStep 1105447 = 1658171) B1658171
theorem B1662503 : Blo 1104625 1662503 := bstep (se 1 (by rfl) ⟨1246877, by rfl⟩ : syracuseStep 1662503 = 2493755) B2493755
theorem B1105487 : Blo 1104625 1105487 := bstep (se 1 (by rfl) ⟨829115, by rfl⟩ : syracuseStep 1105487 = 1658231) B1658231
theorem B1105503 : Blo 1104625 1105503 := bstep (se 1 (by rfl) ⟨829127, by rfl⟩ : syracuseStep 1105503 = 1658255) B1658255
theorem B1105531 : Blo 1104625 1105531 := bstep (se 1 (by rfl) ⟨829148, by rfl⟩ : syracuseStep 1105531 = 1658297) B1658297
theorem B1662587 : Blo 1104625 1662587 := bstep (se 1 (by rfl) ⟨1246940, by rfl⟩ : syracuseStep 1662587 = 2493881) B2493881
theorem B1105583 : Blo 1104625 1105583 := bstep (se 1 (by rfl) ⟨829187, by rfl⟩ : syracuseStep 1105583 = 1658375) B1658375
theorem B1105607 : Blo 1104625 1105607 := bstep (se 1 (by rfl) ⟨829205, by rfl⟩ : syracuseStep 1105607 = 1658411) B1658411
theorem B1105627 : Blo 1104625 1105627 := bstep (se 1 (by rfl) ⟨829220, by rfl⟩ : syracuseStep 1105627 = 1658441) B1658441
theorem B1892087 : Blo 1104625 1892087 := bstep (se 1 (by rfl) ⟨1419065, by rfl⟩ : syracuseStep 1892087 = 2838131) B2838131
theorem B1662713 : Blo 1104625 1662713 := bstep (se 2 (by rfl) ⟨623517, by rfl⟩ : syracuseStep 1662713 = 1247035) B1247035
theorem B1105703 : Blo 1104625 1105703 := bstep (se 1 (by rfl) ⟨829277, by rfl⟩ : syracuseStep 1105703 = 1658555) B1658555
theorem B1105743 : Blo 1104625 1105743 := bstep (se 1 (by rfl) ⟨829307, by rfl⟩ : syracuseStep 1105743 = 1658615) B1658615
theorem B1105759 : Blo 1104625 1105759 := bstep (se 1 (by rfl) ⟨829319, by rfl⟩ : syracuseStep 1105759 = 1658639) B1658639
theorem B1662815 : Blo 1104625 1662815 := bstep (se 1 (by rfl) ⟨1247111, by rfl⟩ : syracuseStep 1662815 = 2494223) B2494223
theorem B1662827 : Blo 1104625 1662827 := bstep (se 1 (by rfl) ⟨1247120, by rfl⟩ : syracuseStep 1662827 = 2494241) B2494241
theorem B1105787 : Blo 1104625 1105787 := bstep (se 1 (by rfl) ⟨829340, by rfl⟩ : syracuseStep 1105787 = 1658681) B1658681
theorem B1105839 : Blo 1104625 1105839 := bstep (se 1 (by rfl) ⟨829379, by rfl⟩ : syracuseStep 1105839 = 1658759) B1658759
theorem B1105863 : Blo 1104625 1105863 := bstep (se 1 (by rfl) ⟨829397, by rfl⟩ : syracuseStep 1105863 = 1658795) B1658795
theorem B1105883 : Blo 1104625 1105883 := bstep (se 1 (by rfl) ⟨829412, by rfl⟩ : syracuseStep 1105883 = 1658825) B1658825
theorem B1105959 : Blo 1104625 1105959 := bstep (se 1 (by rfl) ⟨829469, by rfl⟩ : syracuseStep 1105959 = 1658939) B1658939
theorem B1105999 : Blo 1104625 1105999 := bstep (se 1 (by rfl) ⟨829499, by rfl⟩ : syracuseStep 1105999 = 1658999) B1658999
theorem B1106015 : Blo 1104625 1106015 := bstep (se 1 (by rfl) ⟨829511, by rfl⟩ : syracuseStep 1106015 = 1659023) B1659023
theorem B1106043 : Blo 1104625 1106043 := bstep (se 1 (by rfl) ⟨829532, by rfl⟩ : syracuseStep 1106043 = 1659065) B1659065
theorem B1106095 : Blo 1104625 1106095 := bstep (se 1 (by rfl) ⟨829571, by rfl⟩ : syracuseStep 1106095 = 1659143) B1659143
theorem B1106119 : Blo 1104625 1106119 := bstep (se 1 (by rfl) ⟨829589, by rfl⟩ : syracuseStep 1106119 = 1659179) B1659179
theorem B1106139 : Blo 1104625 1106139 := bstep (se 1 (by rfl) ⟨829604, by rfl⟩ : syracuseStep 1106139 = 1659209) B1659209
theorem B1106215 : Blo 1104625 1106215 := bstep (se 1 (by rfl) ⟨829661, by rfl⟩ : syracuseStep 1106215 = 1659323) B1659323
theorem B1106255 : Blo 1104625 1106255 := bstep (se 1 (by rfl) ⟨829691, by rfl⟩ : syracuseStep 1106255 = 1659383) B1659383
theorem B5595479 : Blo 1104625 5595479 := bstep (se 1 (by rfl) ⟨4196609, by rfl⟩ : syracuseStep 5595479 = 8393219) B8393219
theorem B1106271 : Blo 1104625 1106271 := bstep (se 1 (by rfl) ⟨829703, by rfl⟩ : syracuseStep 1106271 = 1659407) B1659407
theorem B1106299 : Blo 1104625 1106299 := bstep (se 1 (by rfl) ⟨829724, by rfl⟩ : syracuseStep 1106299 = 1659449) B1659449
theorem B1106351 : Blo 1104625 1106351 := bstep (se 1 (by rfl) ⟨829763, by rfl⟩ : syracuseStep 1106351 = 1659527) B1659527
theorem B1106375 : Blo 1104625 1106375 := bstep (se 1 (by rfl) ⟨829781, by rfl⟩ : syracuseStep 1106375 = 1659563) B1659563
theorem B1106395 : Blo 1104625 1106395 := bstep (se 1 (by rfl) ⟨829796, by rfl⟩ : syracuseStep 1106395 = 1659593) B1659593
theorem B1106471 : Blo 1104625 1106471 := bstep (se 1 (by rfl) ⟨829853, by rfl⟩ : syracuseStep 1106471 = 1659707) B1659707
theorem B1106511 : Blo 1104625 1106511 := bstep (se 1 (by rfl) ⟨829883, by rfl⟩ : syracuseStep 1106511 = 1659767) B1659767
theorem B1106527 : Blo 1104625 1106527 := bstep (se 1 (by rfl) ⟨829895, by rfl⟩ : syracuseStep 1106527 = 1659791) B1659791
theorem B1106555 : Blo 1104625 1106555 := bstep (se 1 (by rfl) ⟨829916, by rfl⟩ : syracuseStep 1106555 = 1659833) B1659833
theorem B1106607 : Blo 1104625 1106607 := bstep (se 1 (by rfl) ⟨829955, by rfl⟩ : syracuseStep 1106607 = 1659911) B1659911
theorem B1106631 : Blo 1104625 1106631 := bstep (se 1 (by rfl) ⟨829973, by rfl⟩ : syracuseStep 1106631 = 1659947) B1659947
theorem B1106651 : Blo 1104625 1106651 := bstep (se 1 (by rfl) ⟨829988, by rfl⟩ : syracuseStep 1106651 = 1659977) B1659977
theorem B1106727 : Blo 1104625 1106727 := bstep (se 1 (by rfl) ⟨830045, by rfl⟩ : syracuseStep 1106727 = 1660091) B1660091
theorem B1106767 : Blo 1104625 1106767 := bstep (se 1 (by rfl) ⟨830075, by rfl⟩ : syracuseStep 1106767 = 1660151) B1660151
theorem B1106783 : Blo 1104625 1106783 := bstep (se 1 (by rfl) ⟨830087, by rfl⟩ : syracuseStep 1106783 = 1660175) B1660175
theorem B1106811 : Blo 1104625 1106811 := bstep (se 1 (by rfl) ⟨830108, by rfl⟩ : syracuseStep 1106811 = 1660217) B1660217
theorem B1106863 : Blo 1104625 1106863 := bstep (se 1 (by rfl) ⟨830147, by rfl⟩ : syracuseStep 1106863 = 1660295) B1660295
theorem B1106887 : Blo 1104625 1106887 := bstep (se 1 (by rfl) ⟨830165, by rfl⟩ : syracuseStep 1106887 = 1660331) B1660331
theorem B1106907 : Blo 1104625 1106907 := bstep (se 1 (by rfl) ⟨830180, by rfl⟩ : syracuseStep 1106907 = 1660361) B1660361
theorem B5530643 : Blo 1104625 5530643 := bstep (se 1 (by rfl) ⟨4147982, by rfl⟩ : syracuseStep 5530643 = 8295965) B8295965
theorem B1106983 : Blo 1104625 1106983 := bstep (se 1 (by rfl) ⟨830237, by rfl⟩ : syracuseStep 1106983 = 1660475) B1660475
theorem B1107023 : Blo 1104625 1107023 := bstep (se 1 (by rfl) ⟨830267, by rfl⟩ : syracuseStep 1107023 = 1660535) B1660535
theorem B1107039 : Blo 1104625 1107039 := bstep (se 1 (by rfl) ⟨830279, by rfl⟩ : syracuseStep 1107039 = 1660559) B1660559
theorem B11953271 : Blo 1104625 11953271 := bstep (se 1 (by rfl) ⟨8964953, by rfl⟩ : syracuseStep 11953271 = 17929907) B17929907
theorem B1991803 : Blo 1104625 1991803 := bstep (se 1 (by rfl) ⟨1493852, by rfl⟩ : syracuseStep 1991803 = 2987705) B2987705
theorem B1107067 : Blo 1104625 1107067 := bstep (se 1 (by rfl) ⟨830300, by rfl⟩ : syracuseStep 1107067 = 1660601) B1660601
theorem B60646553 : Blo 1104625 60646553 := bstep (se 2 (by rfl) ⟨22742457, by rfl⟩ : syracuseStep 60646553 = 45484915) B45484915
theorem B3728537 : Blo 1104625 3728537 := bstep (se 2 (by rfl) ⟨1398201, by rfl⟩ : syracuseStep 3728537 = 2796403) B2796403
theorem B1107119 : Blo 1104625 1107119 := bstep (se 1 (by rfl) ⟨830339, by rfl⟩ : syracuseStep 1107119 = 1660679) B1660679
theorem B1107143 : Blo 1104625 1107143 := bstep (se 1 (by rfl) ⟨830357, by rfl⟩ : syracuseStep 1107143 = 1660715) B1660715
theorem B1107163 : Blo 1104625 1107163 := bstep (se 1 (by rfl) ⟨830372, by rfl⟩ : syracuseStep 1107163 = 1660745) B1660745
theorem B12608783 : Blo 1104625 12608783 := bstep (se 1 (by rfl) ⟨9456587, by rfl⟩ : syracuseStep 12608783 = 18913175) B18913175
theorem B1107239 : Blo 1104625 1107239 := bstep (se 1 (by rfl) ⟨830429, by rfl⟩ : syracuseStep 1107239 = 1660859) B1660859
theorem B1107279 : Blo 1104625 1107279 := bstep (se 1 (by rfl) ⟨830459, by rfl⟩ : syracuseStep 1107279 = 1660919) B1660919
theorem B1107295 : Blo 1104625 1107295 := bstep (se 1 (by rfl) ⟨830471, by rfl⟩ : syracuseStep 1107295 = 1660943) B1660943
theorem B8512883 : Blo 1104625 8512883 := bstep (se 1 (by rfl) ⟨6384662, by rfl⟩ : syracuseStep 8512883 = 12769325) B12769325
theorem B1107323 : Blo 1104625 1107323 := bstep (se 1 (by rfl) ⟨830492, by rfl⟩ : syracuseStep 1107323 = 1660985) B1660985
theorem B1107375 : Blo 1104625 1107375 := bstep (se 1 (by rfl) ⟨830531, by rfl⟩ : syracuseStep 1107375 = 1661063) B1661063
theorem B1107399 : Blo 1104625 1107399 := bstep (se 1 (by rfl) ⟨830549, by rfl⟩ : syracuseStep 1107399 = 1661099) B1661099
theorem B1107419 : Blo 1104625 1107419 := bstep (se 1 (by rfl) ⟨830564, by rfl⟩ : syracuseStep 1107419 = 1661129) B1661129
theorem B1107495 : Blo 1104625 1107495 := bstep (se 1 (by rfl) ⟨830621, by rfl⟩ : syracuseStep 1107495 = 1661243) B1661243
theorem B1107535 : Blo 1104625 1107535 := bstep (se 1 (by rfl) ⟨830651, by rfl⟩ : syracuseStep 1107535 = 1661303) B1661303
theorem B1107551 : Blo 1104625 1107551 := bstep (se 1 (by rfl) ⟨830663, by rfl⟩ : syracuseStep 1107551 = 1661327) B1661327
theorem B1107579 : Blo 1104625 1107579 := bstep (se 1 (by rfl) ⟨830684, by rfl⟩ : syracuseStep 1107579 = 1661369) B1661369
theorem B1107631 : Blo 1104625 1107631 := bstep (se 1 (by rfl) ⟨830723, by rfl⟩ : syracuseStep 1107631 = 1661447) B1661447
theorem B1107655 : Blo 1104625 1107655 := bstep (se 1 (by rfl) ⟨830741, by rfl⟩ : syracuseStep 1107655 = 1661483) B1661483
theorem B1107675 : Blo 1104625 1107675 := bstep (se 1 (by rfl) ⟨830756, by rfl⟩ : syracuseStep 1107675 = 1661513) B1661513
theorem B68085497 : Blo 1104625 68085497 := bstep (se 2 (by rfl) ⟨25532061, by rfl⟩ : syracuseStep 68085497 = 51064123) B51064123
theorem B1107751 : Blo 1104625 1107751 := bstep (se 1 (by rfl) ⟨830813, by rfl⟩ : syracuseStep 1107751 = 1661627) B1661627
theorem B14378795 : Blo 1104625 14378795 := bstep (se 1 (by rfl) ⟨10784096, by rfl⟩ : syracuseStep 14378795 = 21568193) B21568193
theorem B1107791 : Blo 1104625 1107791 := bstep (se 1 (by rfl) ⟨830843, by rfl⟩ : syracuseStep 1107791 = 1661687) B1661687
theorem B1107807 : Blo 1104625 1107807 := bstep (se 1 (by rfl) ⟨830855, by rfl⟩ : syracuseStep 1107807 = 1661711) B1661711
theorem B1107835 : Blo 1104625 1107835 := bstep (se 1 (by rfl) ⟨830876, by rfl⟩ : syracuseStep 1107835 = 1661753) B1661753
theorem B1107887 : Blo 1104625 1107887 := bstep (se 1 (by rfl) ⟨830915, by rfl⟩ : syracuseStep 1107887 = 1661831) B1661831
theorem B8972219 : Blo 1104625 8972219 := bstep (se 1 (by rfl) ⟨6729164, by rfl⟩ : syracuseStep 8972219 = 13458329) B13458329
theorem B1107911 : Blo 1104625 1107911 := bstep (se 1 (by rfl) ⟨830933, by rfl⟩ : syracuseStep 1107911 = 1661867) B1661867
theorem B1107931 : Blo 1104625 1107931 := bstep (se 1 (by rfl) ⟨830948, by rfl⟩ : syracuseStep 1107931 = 1661897) B1661897
theorem B1108007 : Blo 1104625 1108007 := bstep (se 1 (by rfl) ⟨831005, by rfl⟩ : syracuseStep 1108007 = 1662011) B1662011
theorem B1108047 : Blo 1104625 1108047 := bstep (se 1 (by rfl) ⟨831035, by rfl⟩ : syracuseStep 1108047 = 1662071) B1662071
theorem B1108063 : Blo 1104625 1108063 := bstep (se 1 (by rfl) ⟨831047, by rfl⟩ : syracuseStep 1108063 = 1662095) B1662095
theorem B1108091 : Blo 1104625 1108091 := bstep (se 1 (by rfl) ⟨831068, by rfl⟩ : syracuseStep 1108091 = 1662137) B1662137
theorem B1108143 : Blo 1104625 1108143 := bstep (se 1 (by rfl) ⟨831107, by rfl⟩ : syracuseStep 1108143 = 1662215) B1662215
theorem B1108167 : Blo 1104625 1108167 := bstep (se 1 (by rfl) ⟨831125, by rfl⟩ : syracuseStep 1108167 = 1662251) B1662251
theorem B1108187 : Blo 1104625 1108187 := bstep (se 1 (by rfl) ⟨831140, by rfl⟩ : syracuseStep 1108187 = 1662281) B1662281
theorem B1108263 : Blo 1104625 1108263 := bstep (se 1 (by rfl) ⟨831197, by rfl⟩ : syracuseStep 1108263 = 1662395) B1662395
theorem B3729725 : Blo 1104625 3729725 := bstep (se 3 (by rfl) ⟨699323, by rfl⟩ : syracuseStep 3729725 = 1398647) B1398647
theorem B1108303 : Blo 1104625 1108303 := bstep (se 1 (by rfl) ⟨831227, by rfl⟩ : syracuseStep 1108303 = 1662455) B1662455
theorem B8415575 : Blo 1104625 8415575 := bstep (se 1 (by rfl) ⟨6311681, by rfl⟩ : syracuseStep 8415575 = 12623363) B12623363
theorem B1108319 : Blo 1104625 1108319 := bstep (se 1 (by rfl) ⟨831239, by rfl⟩ : syracuseStep 1108319 = 1662479) B1662479
theorem B1108347 : Blo 1104625 1108347 := bstep (se 1 (by rfl) ⟨831260, by rfl⟩ : syracuseStep 1108347 = 1662521) B1662521
theorem B1993135 : Blo 1104625 1993135 := bstep (se 1 (by rfl) ⟨1494851, by rfl⟩ : syracuseStep 1993135 = 2989703) B2989703
theorem B1108399 : Blo 1104625 1108399 := bstep (se 1 (by rfl) ⟨831299, by rfl⟩ : syracuseStep 1108399 = 1662599) B1662599
theorem B26896819 : Blo 1104625 26896819 := bstep (se 1 (by rfl) ⟨20172614, by rfl⟩ : syracuseStep 26896819 = 40345229) B40345229
theorem B1108423 : Blo 1104625 1108423 := bstep (se 1 (by rfl) ⟨831317, by rfl⟩ : syracuseStep 1108423 = 1662635) B1662635
theorem B1108443 : Blo 1104625 1108443 := bstep (se 1 (by rfl) ⟨831332, by rfl⟩ : syracuseStep 1108443 = 1662665) B1662665
theorem B1108519 : Blo 1104625 1108519 := bstep (se 1 (by rfl) ⟨831389, by rfl⟩ : syracuseStep 1108519 = 1662779) B1662779
theorem B1108559 : Blo 1104625 1108559 := bstep (se 1 (by rfl) ⟨831419, by rfl⟩ : syracuseStep 1108559 = 1662839) B1662839
theorem B1108575 : Blo 1104625 1108575 := bstep (se 1 (by rfl) ⟨831431, by rfl⟩ : syracuseStep 1108575 = 1662863) B1662863
theorem B3369595 : Blo 1104625 3369595 := bstep (se 1 (by rfl) ⟨2527196, by rfl⟩ : syracuseStep 3369595 = 5054393) B5054393
theorem B1108603 : Blo 1104625 1108603 := bstep (se 1 (by rfl) ⟨831452, by rfl⟩ : syracuseStep 1108603 = 1662905) B1662905
theorem B3730589 : Blo 1104625 3730589 := bstep (se 3 (by rfl) ⟨699485, by rfl⟩ : syracuseStep 3730589 = 1398971) B1398971
theorem B2485799 : Blo 1104625 2485799 := bstep (se 1 (by rfl) ⟨1864349, by rfl⟩ : syracuseStep 2485799 = 3728699) B3728699
theorem B3600007 : Blo 1104625 3600007 := bstep (se 1 (by rfl) ⟨2700005, by rfl⟩ : syracuseStep 3600007 = 5400011) B5400011
theorem B3731129 : Blo 1104625 3731129 := bstep (se 2 (by rfl) ⟨1399173, by rfl⟩ : syracuseStep 3731129 = 2798347) B2798347
theorem B5599043 : Blo 1104625 5599043 := bstep (se 1 (by rfl) ⟨4199282, by rfl⟩ : syracuseStep 5599043 = 8398565) B8398565
theorem B2486123 : Blo 1104625 2486123 := bstep (se 1 (by rfl) ⟨1864592, by rfl⟩ : syracuseStep 2486123 = 3729185) B3729185
theorem B4255595 : Blo 1104625 4255595 := bstep (se 1 (by rfl) ⟨3191696, by rfl⟩ : syracuseStep 4255595 = 6383393) B6383393
theorem B2486177 : Blo 1104625 2486177 := bstep (se 2 (by rfl) ⟨932316, by rfl⟩ : syracuseStep 2486177 = 1864633) B1864633
theorem B12611699 : Blo 1104625 12611699 := bstep (se 1 (by rfl) ⟨9458774, by rfl⟩ : syracuseStep 12611699 = 18917549) B18917549
theorem B2486519 : Blo 1104625 2486519 := bstep (se 1 (by rfl) ⟨1864889, by rfl⟩ : syracuseStep 2486519 = 3729779) B3729779
theorem B3731723 : Blo 1104625 3731723 := bstep (se 1 (by rfl) ⟨2798792, by rfl⟩ : syracuseStep 3731723 = 5597585) B5597585
theorem B1864201 : Blo 1104625 1864201 := bstep (se 2 (by rfl) ⟨699075, by rfl⟩ : syracuseStep 1864201 = 1398151) B1398151
theorem B3731993 : Blo 1104625 3731993 := bstep (se 2 (by rfl) ⟨1399497, by rfl⟩ : syracuseStep 3731993 = 2798995) B2798995
theorem B8319547 : Blo 1104625 8319547 := bstep (se 1 (by rfl) ⟨6239660, by rfl⟩ : syracuseStep 8319547 = 12479321) B12479321
theorem B1864363 : Blo 1104625 1864363 := bstep (se 1 (by rfl) ⟨1398272, by rfl⟩ : syracuseStep 1864363 = 2796545) B2796545
theorem B2487113 : Blo 1104625 2487113 := bstep (se 2 (by rfl) ⟨932667, by rfl⟩ : syracuseStep 2487113 = 1865335) B1865335
theorem B4256687 : Blo 1104625 4256687 := bstep (se 1 (by rfl) ⟨3192515, by rfl⟩ : syracuseStep 4256687 = 6385031) B6385031
theorem B1864667 : Blo 1104625 1864667 := bstep (se 1 (by rfl) ⟨1398500, by rfl⟩ : syracuseStep 1864667 = 2797001) B2797001
theorem B10089521 : Blo 1104625 10089521 := bstep (se 2 (by rfl) ⟨3783570, by rfl⟩ : syracuseStep 10089521 = 7567141) B7567141
theorem B1864903 : Blo 1104625 1864903 := bstep (se 1 (by rfl) ⟨1398677, by rfl⟩ : syracuseStep 1864903 = 2797355) B2797355
theorem B1996105 : Blo 1104625 1996105 := bstep (se 2 (by rfl) ⟨748539, by rfl⟩ : syracuseStep 1996105 = 1497079) B1497079
theorem B1865065 : Blo 1104625 1865065 := bstep (se 2 (by rfl) ⟨699399, by rfl⟩ : syracuseStep 1865065 = 1398799) B1398799
theorem B4257305 : Blo 1104625 4257305 := bstep (se 2 (by rfl) ⟨1596489, by rfl⟩ : syracuseStep 4257305 = 3192979) B3192979
theorem B2487905 : Blo 1104625 2487905 := bstep (se 2 (by rfl) ⟨932964, by rfl⟩ : syracuseStep 2487905 = 1865929) B1865929
theorem B3733127 : Blo 1104625 3733127 := bstep (se 1 (by rfl) ⟨2799845, by rfl⟩ : syracuseStep 3733127 = 5599691) B5599691
theorem B3733181 : Blo 1104625 3733181 := bstep (se 3 (by rfl) ⟨699971, by rfl⟩ : syracuseStep 3733181 = 1399943) B1399943
theorem B1242823 : Blo 1104625 1242823 := bstep (se 1 (by rfl) ⟨932117, by rfl⟩ : syracuseStep 1242823 = 1864235) B1864235
theorem B3733343 : Blo 1104625 3733343 := bstep (se 1 (by rfl) ⟨2800007, by rfl⟩ : syracuseStep 3733343 = 5600015) B5600015
theorem B2488247 : Blo 1104625 2488247 := bstep (se 1 (by rfl) ⟨1866185, by rfl⟩ : syracuseStep 2488247 = 3732371) B3732371
theorem B1865659 : Blo 1104625 1865659 := bstep (se 1 (by rfl) ⟨1399244, by rfl⟩ : syracuseStep 1865659 = 2798489) B2798489
theorem B3733505 : Blo 1104625 3733505 := bstep (se 2 (by rfl) ⟨1400064, by rfl⟩ : syracuseStep 3733505 = 2800129) B2800129
theorem B1865767 : Blo 1104625 1865767 := bstep (se 1 (by rfl) ⟨1399325, by rfl⟩ : syracuseStep 1865767 = 2798651) B2798651
theorem B1866091 : Blo 1104625 1866091 := bstep (se 1 (by rfl) ⟨1399568, by rfl⟩ : syracuseStep 1866091 = 2799137) B2799137
theorem B2488841 : Blo 1104625 2488841 := bstep (se 2 (by rfl) ⟨933315, by rfl⟩ : syracuseStep 2488841 = 1866631) B1866631
theorem B1243687 : Blo 1104625 1243687 := bstep (se 1 (by rfl) ⟨932765, by rfl⟩ : syracuseStep 1243687 = 1865531) B1865531
theorem B3734315 : Blo 1104625 3734315 := bstep (se 1 (by rfl) ⟨2800736, by rfl⟩ : syracuseStep 3734315 = 5601473) B5601473
theorem B5602121 : Blo 1104625 5602121 := bstep (se 2 (by rfl) ⟨2100795, by rfl⟩ : syracuseStep 5602121 = 4201591) B4201591
theorem B2489183 : Blo 1104625 2489183 := bstep (se 1 (by rfl) ⟨1866887, by rfl⟩ : syracuseStep 2489183 = 3733775) B3733775
theorem B2489363 : Blo 1104625 2489363 := bstep (se 1 (by rfl) ⟨1867022, by rfl⟩ : syracuseStep 2489363 = 3734045) B3734045
theorem B3734585 : Blo 1104625 3734585 := bstep (se 2 (by rfl) ⟨1400469, by rfl⟩ : syracuseStep 3734585 = 2800939) B2800939
theorem B15957071 : Blo 1104625 15957071 := bstep (se 1 (by rfl) ⟨11967803, by rfl⟩ : syracuseStep 15957071 = 23935607) B23935607
theorem B9862337 : Blo 1104625 9862337 := bstep (se 2 (by rfl) ⟨3698376, by rfl⟩ : syracuseStep 9862337 = 7396753) B7396753
theorem B2489705 : Blo 1104625 2489705 := bstep (se 2 (by rfl) ⟨933639, by rfl⟩ : syracuseStep 2489705 = 1867279) B1867279
theorem B3734909 : Blo 1104625 3734909 := bstep (se 3 (by rfl) ⟨700295, by rfl⟩ : syracuseStep 3734909 = 1400591) B1400591
theorem B1867151 : Blo 1104625 1867151 := bstep (se 1 (by rfl) ⟨1400363, by rfl⟩ : syracuseStep 1867151 = 2800727) B2800727
theorem B3407483 : Blo 1104625 3407483 := bstep (se 1 (by rfl) ⟨2555612, by rfl⟩ : syracuseStep 3407483 = 5111225) B5111225
theorem B1867387 : Blo 1104625 1867387 := bstep (se 1 (by rfl) ⟨1400540, by rfl⟩ : syracuseStep 1867387 = 2801081) B2801081
theorem B12582539 : Blo 1104625 12582539 := bstep (se 1 (by rfl) ⟨9436904, by rfl⟩ : syracuseStep 12582539 = 18873809) B18873809
theorem B3735179 : Blo 1104625 3735179 := bstep (se 1 (by rfl) ⟨2801384, by rfl⟩ : syracuseStep 3735179 = 5602769) B5602769
theorem B2097083 : Blo 1104625 2097083 := bstep (se 1 (by rfl) ⟨1572812, by rfl⟩ : syracuseStep 2097083 = 3145625) B3145625
theorem B2490299 : Blo 1104625 2490299 := bstep (se 1 (by rfl) ⟨1867724, by rfl⟩ : syracuseStep 2490299 = 3735449) B3735449
theorem B3735611 : Blo 1104625 3735611 := bstep (se 1 (by rfl) ⟨2801708, by rfl⟩ : syracuseStep 3735611 = 5603417) B5603417
theorem B3735881 : Blo 1104625 3735881 := bstep (se 2 (by rfl) ⟨1400955, by rfl⟩ : syracuseStep 3735881 = 2801911) B2801911
theorem B1868123 : Blo 1104625 1868123 := bstep (se 1 (by rfl) ⟨1401092, by rfl⟩ : syracuseStep 1868123 = 2802185) B2802185
theorem B2490731 : Blo 1104625 2490731 := bstep (se 1 (by rfl) ⟨1868048, by rfl⟩ : syracuseStep 2490731 = 3736097) B3736097
theorem B1868143 : Blo 1104625 1868143 := bstep (se 1 (by rfl) ⟨1401107, by rfl⟩ : syracuseStep 1868143 = 2802215) B2802215
theorem B15958457 : Blo 1104625 15958457 := bstep (se 2 (by rfl) ⟨5984421, by rfl⟩ : syracuseStep 15958457 = 11968843) B11968843
theorem B2490875 : Blo 1104625 2490875 := bstep (se 1 (by rfl) ⟨1868156, by rfl⟩ : syracuseStep 2490875 = 3736313) B3736313
theorem B1868359 : Blo 1104625 1868359 := bstep (se 1 (by rfl) ⟨1401269, by rfl⟩ : syracuseStep 1868359 = 2802539) B2802539
theorem B2491001 : Blo 1104625 2491001 := bstep (se 2 (by rfl) ⟨934125, by rfl⟩ : syracuseStep 2491001 = 1868251) B1868251
theorem B3539609 : Blo 1104625 3539609 := bstep (se 2 (by rfl) ⟨1327353, by rfl⟩ : syracuseStep 3539609 = 2654707) B2654707
theorem B2491055 : Blo 1104625 2491055 := bstep (se 1 (by rfl) ⟨1868291, by rfl⟩ : syracuseStep 2491055 = 3736583) B3736583
theorem B1245919 : Blo 1104625 1245919 := bstep (se 1 (by rfl) ⟨934439, by rfl⟩ : syracuseStep 1245919 = 1868879) B1868879
theorem B2491127 : Blo 1104625 2491127 := bstep (se 1 (by rfl) ⟨1868345, by rfl⟩ : syracuseStep 2491127 = 3736691) B3736691
theorem B2491307 : Blo 1104625 2491307 := bstep (se 1 (by rfl) ⟨1868480, by rfl⟩ : syracuseStep 2491307 = 3736961) B3736961
theorem B10945475 : Blo 1104625 10945475 := bstep (se 1 (by rfl) ⟨8209106, by rfl⟩ : syracuseStep 10945475 = 16418213) B16418213
theorem B4195273 : Blo 1104625 4195273 := bstep (se 2 (by rfl) ⟨1573227, by rfl⟩ : syracuseStep 4195273 = 3146455) B3146455
theorem B6718439 : Blo 1104625 6718439 := bstep (se 1 (by rfl) ⟨5038829, by rfl⟩ : syracuseStep 6718439 = 10077659) B10077659
theorem B1868791 : Blo 1104625 1868791 := bstep (se 1 (by rfl) ⟨1401593, by rfl⟩ : syracuseStep 1868791 = 2803187) B2803187
theorem B5604551 : Blo 1104625 5604551 := bstep (se 1 (by rfl) ⟨4203413, by rfl⟩ : syracuseStep 5604551 = 8406827) B8406827
theorem B4195577 : Blo 1104625 4195577 := bstep (se 2 (by rfl) ⟨1573341, by rfl⟩ : syracuseStep 4195577 = 3146683) B3146683
theorem B1246495 : Blo 1104625 1246495 := bstep (se 1 (by rfl) ⟨934871, by rfl⟩ : syracuseStep 1246495 = 1869743) B1869743
theorem B1869095 : Blo 1104625 1869095 := bstep (se 1 (by rfl) ⟨1401821, by rfl⟩ : syracuseStep 1869095 = 2803643) B2803643
theorem B5604713 : Blo 1104625 5604713 := bstep (se 2 (by rfl) ⟨2101767, by rfl⟩ : syracuseStep 5604713 = 4203535) B4203535
theorem B18220439 : Blo 1104625 18220439 := bstep (se 1 (by rfl) ⟨13665329, by rfl⟩ : syracuseStep 18220439 = 27330659) B27330659
theorem B4195745 : Blo 1104625 4195745 := bstep (se 2 (by rfl) ⟨1573404, by rfl⟩ : syracuseStep 4195745 = 3146809) B3146809
theorem B2491847 : Blo 1104625 2491847 := bstep (se 1 (by rfl) ⟨1868885, by rfl⟩ : syracuseStep 2491847 = 3737771) B3737771
theorem B2655737 : Blo 1104625 2655737 := bstep (se 2 (by rfl) ⟨995901, by rfl⟩ : syracuseStep 2655737 = 1991803) B1991803
theorem B1246783 : Blo 1104625 1246783 := bstep (se 1 (by rfl) ⟨935087, by rfl⟩ : syracuseStep 1246783 = 1870175) B1870175
theorem B2360927 : Blo 1104625 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B1574635 : Blo 1104625 1574635 := bstep (se 1 (by rfl) ⟨1180976, by rfl⟩ : syracuseStep 1574635 = 2361953) B2361953
theorem B1869547 : Blo 1104625 1869547 := bstep (se 1 (by rfl) ⟨1402160, by rfl⟩ : syracuseStep 1869547 = 2804321) B2804321
theorem B2492207 : Blo 1104625 2492207 := bstep (se 1 (by rfl) ⟨1869155, by rfl⟩ : syracuseStep 2492207 = 3738311) B3738311
theorem B2492783 : Blo 1104625 2492783 := bstep (se 1 (by rfl) ⟨1869587, by rfl⟩ : syracuseStep 2492783 = 3739175) B3739175
theorem B1575335 : Blo 1104625 1575335 := bstep (se 1 (by rfl) ⟨1181501, by rfl⟩ : syracuseStep 1575335 = 2363003) B2363003
theorem B2492855 : Blo 1104625 2492855 := bstep (se 1 (by rfl) ⟨1869641, by rfl⟩ : syracuseStep 2492855 = 3739283) B3739283
theorem B1182151 : Blo 1104625 1182151 := bstep (se 1 (by rfl) ⟨886613, by rfl⟩ : syracuseStep 1182151 = 1773227) B1773227
theorem B7965157 : Blo 1104625 7965157 := bstep (se 4 (by rfl) ⟨746733, by rfl⟩ : syracuseStep 7965157 = 1493467) B1493467
theorem B2492999 : Blo 1104625 2492999 := bstep (se 1 (by rfl) ⟨1869749, by rfl⟩ : syracuseStep 2492999 = 3739499) B3739499
theorem B196512331 : Blo 1104625 196512331 := bstep (se 1 (by rfl) ⟨147384248, by rfl⟩ : syracuseStep 196512331 = 294768497) B294768497
theorem B6294095 : Blo 1104625 6294095 := bstep (se 1 (by rfl) ⟨4720571, by rfl⟩ : syracuseStep 6294095 = 9441143) B9441143
theorem B2493035 : Blo 1104625 2493035 := bstep (se 1 (by rfl) ⟨1869776, by rfl⟩ : syracuseStep 2493035 = 3739553) B3739553
theorem B1870519 : Blo 1104625 1870519 := bstep (se 1 (by rfl) ⟨1402889, by rfl⟩ : syracuseStep 1870519 = 2805779) B2805779
theorem B3541915 : Blo 1104625 3541915 := bstep (se 1 (by rfl) ⟨2656436, by rfl⟩ : syracuseStep 3541915 = 5312873) B5312873
theorem B2493431 : Blo 1104625 2493431 := bstep (se 1 (by rfl) ⟨1870073, by rfl⟩ : syracuseStep 2493431 = 3740147) B3740147
theorem B10619981 : Blo 1104625 10619981 := bstep (se 3 (by rfl) ⟨1991246, by rfl⟩ : syracuseStep 10619981 = 3982493) B3982493
theorem B8391761 : Blo 1104625 8391761 := bstep (se 2 (by rfl) ⟨3146910, by rfl⟩ : syracuseStep 8391761 = 6293821) B6293821
theorem B9440459 : Blo 1104625 9440459 := bstep (se 1 (by rfl) ⟨7080344, by rfl⟩ : syracuseStep 9440459 = 14160689) B14160689
theorem B2657513 : Blo 1104625 2657513 := bstep (se 2 (by rfl) ⟨996567, by rfl⟩ : syracuseStep 2657513 = 1993135) B1993135
theorem B2493791 : Blo 1104625 2493791 := bstep (se 1 (by rfl) ⟨1870343, by rfl⟩ : syracuseStep 2493791 = 3740687) B3740687
theorem B3739067 : Blo 1104625 3739067 := bstep (se 1 (by rfl) ⟨2804300, by rfl⟩ : syracuseStep 3739067 = 5608601) B5608601
theorem B4492793 : Blo 1104625 4492793 := bstep (se 2 (by rfl) ⟨1684797, by rfl⟩ : syracuseStep 4492793 = 3369595) B3369595
theorem B9572039 : Blo 1104625 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B2100971 : Blo 1104625 2100971 := bstep (se 1 (by rfl) ⟨1575728, by rfl⟩ : syracuseStep 2100971 = 3151457) B3151457
theorem B2494187 : Blo 1104625 2494187 := bstep (se 1 (by rfl) ⟨1870640, by rfl⟩ : syracuseStep 2494187 = 3741281) B3741281
theorem B1576759 : Blo 1104625 1576759 := bstep (se 1 (by rfl) ⟨1182569, by rfl⟩ : syracuseStep 1576759 = 2365139) B2365139
theorem B2494313 : Blo 1104625 2494313 := bstep (se 2 (by rfl) ⟨935367, by rfl⟩ : syracuseStep 2494313 = 1870735) B1870735
theorem B3149725 : Blo 1104625 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B7081985 : Blo 1104625 7081985 := bstep (se 2 (by rfl) ⟨2655744, by rfl⟩ : syracuseStep 7081985 = 5311489) B5311489
theorem B6295553 : Blo 1104625 6295553 := bstep (se 2 (by rfl) ⟨2360832, by rfl⟩ : syracuseStep 6295553 = 4721665) B4721665
theorem B2363755 : Blo 1104625 2363755 := bstep (se 1 (by rfl) ⟨1772816, by rfl⟩ : syracuseStep 2363755 = 3545633) B3545633
theorem B32739719 : Blo 1104625 32739719 := bstep (se 1 (by rfl) ⟨24554789, by rfl⟩ : syracuseStep 32739719 = 49109579) B49109579
theorem B2560531 : Blo 1104625 2560531 := bstep (se 1 (by rfl) ⟨1920398, by rfl⟩ : syracuseStep 2560531 = 3840797) B3840797
theorem B2364079 : Blo 1104625 2364079 := bstep (se 1 (by rfl) ⟨1773059, by rfl⟩ : syracuseStep 2364079 = 3546119) B3546119
theorem B1577647 : Blo 1104625 1577647 := bstep (se 1 (by rfl) ⟨1183235, by rfl⟩ : syracuseStep 1577647 = 2366471) B2366471
theorem B2101943 : Blo 1104625 2101943 := bstep (se 1 (by rfl) ⟨1576457, by rfl⟩ : syracuseStep 2101943 = 3152915) B3152915
theorem B30282569 : Blo 1104625 30282569 := bstep (se 2 (by rfl) ⟨11355963, by rfl⟩ : syracuseStep 30282569 = 22711927) B22711927
theorem B5608439 : Blo 1104625 5608439 := bstep (se 1 (by rfl) ⟨4206329, by rfl⟩ : syracuseStep 5608439 = 8412659) B8412659
theorem B23925917 : Blo 1104625 23925917 := bstep (se 3 (by rfl) ⟨4486109, by rfl⟩ : syracuseStep 23925917 = 8972219) B8972219
theorem B1578217 : Blo 1104625 1578217 := bstep (se 2 (by rfl) ⟨591831, by rfl⟩ : syracuseStep 1578217 = 1183663) B1183663
theorem B2103097 : Blo 1104625 2103097 := bstep (se 2 (by rfl) ⟨788661, by rfl⟩ : syracuseStep 2103097 = 1577323) B1577323
theorem B1775417 : Blo 1104625 1775417 := bstep (se 2 (by rfl) ⟨665781, by rfl⟩ : syracuseStep 1775417 = 1331563) B1331563
theorem B2103401 : Blo 1104625 2103401 := bstep (se 2 (by rfl) ⟨788775, by rfl⟩ : syracuseStep 2103401 = 1577551) B1577551
theorem B26941571 : Blo 1104625 26941571 := bstep (se 1 (by rfl) ⟨20206178, by rfl⟩ : syracuseStep 26941571 = 40412357) B40412357
theorem B5675255 : Blo 1104625 5675255 := bstep (se 1 (by rfl) ⟨4256441, by rfl⟩ : syracuseStep 5675255 = 8512883) B8512883
theorem B45390331 : Blo 1104625 45390331 := bstep (se 1 (by rfl) ⟨34042748, by rfl⟩ : syracuseStep 45390331 = 68085497) B68085497
theorem B2103803 : Blo 1104625 2103803 := bstep (se 1 (by rfl) ⟨1577852, by rfl⟩ : syracuseStep 2103803 = 3155705) B3155705
theorem B4725287 : Blo 1104625 4725287 := bstep (se 1 (by rfl) ⟨3543965, by rfl⟩ : syracuseStep 4725287 = 7087931) B7087931
theorem B2104031 : Blo 1104625 2104031 := bstep (se 1 (by rfl) ⟨1578023, by rfl⟩ : syracuseStep 2104031 = 3156047) B3156047
theorem B5610383 : Blo 1104625 5610383 := bstep (se 1 (by rfl) ⟨4207787, by rfl⟩ : syracuseStep 5610383 = 8415575) B8415575
theorem B10623899 : Blo 1104625 10623899 := bstep (se 1 (by rfl) ⟨7967924, by rfl⟩ : syracuseStep 10623899 = 15935849) B15935849
theorem B2661473 : Blo 1104625 2661473 := bstep (se 2 (by rfl) ⟨998052, by rfl⟩ : syracuseStep 2661473 = 1996105) B1996105
theorem B4201865 : Blo 1104625 4201865 := bstep (se 2 (by rfl) ⟨1575699, by rfl⟩ : syracuseStep 4201865 = 3151399) B3151399
theorem B1515071 : Blo 1104625 1515071 := bstep (se 1 (by rfl) ⟨1136303, by rfl⟩ : syracuseStep 1515071 = 2272607) B2272607
theorem B10100609 : Blo 1104625 10100609 := bstep (se 2 (by rfl) ⟨3787728, by rfl⟩ : syracuseStep 10100609 = 7575457) B7575457
theorem B10101419 : Blo 1104625 10101419 := bstep (se 1 (by rfl) ⟨7576064, by rfl⟩ : syracuseStep 10101419 = 15152129) B15152129
theorem B6726347 : Blo 1104625 6726347 := bstep (se 1 (by rfl) ⟨5044760, by rfl⟩ : syracuseStep 6726347 = 10089521) B10089521
theorem B5972831 : Blo 1104625 5972831 := bstep (se 1 (by rfl) ⟨4479623, by rfl⟩ : syracuseStep 5972831 = 8959247) B8959247
theorem B6300611 : Blo 1104625 6300611 := bstep (se 1 (by rfl) ⟨4725458, by rfl⟩ : syracuseStep 6300611 = 9450917) B9450917
theorem B4727747 : Blo 1104625 4727747 := bstep (se 1 (by rfl) ⟨3545810, by rfl⟩ : syracuseStep 4727747 = 7091621) B7091621
theorem B9446543 : Blo 1104625 9446543 := bstep (se 1 (by rfl) ⟨7084907, by rfl⟩ : syracuseStep 9446543 = 14169815) B14169815
theorem B3548605 : Blo 1104625 3548605 := bstep (se 3 (by rfl) ⟨665363, by rfl⟩ : syracuseStep 3548605 = 1330727) B1330727
theorem B2696647 : Blo 1104625 2696647 := bstep (se 1 (by rfl) ⟨2022485, by rfl⟩ : syracuseStep 2696647 = 4044971) B4044971
theorem B2271655 : Blo 1104625 2271655 := bstep (se 1 (by rfl) ⟨1703741, by rfl⟩ : syracuseStep 2271655 = 3407483) B3407483
theorem B22686799 : Blo 1104625 22686799 := bstep (se 1 (by rfl) ⟨17015099, by rfl⟩ : syracuseStep 22686799 = 34030199) B34030199
theorem B17017937 : Blo 1104625 17017937 := bstep (se 2 (by rfl) ⟨6381726, by rfl⟩ : syracuseStep 17017937 = 12763453) B12763453
theorem B2993249 : Blo 1104625 2993249 := bstep (se 2 (by rfl) ⟨1122468, by rfl⟩ : syracuseStep 2993249 = 2244937) B2244937
theorem B4861147 : Blo 1104625 4861147 := bstep (se 1 (by rfl) ⟨3645860, by rfl⟩ : syracuseStep 4861147 = 7291721) B7291721
theorem B2796839 : Blo 1104625 2796839 := bstep (se 1 (by rfl) ⟨2097629, by rfl⟩ : syracuseStep 2796839 = 4195259) B4195259
theorem B6303095 : Blo 1104625 6303095 := bstep (se 1 (by rfl) ⟨4727321, by rfl⟩ : syracuseStep 6303095 = 9454643) B9454643
theorem B5385811 : Blo 1104625 5385811 := bstep (se 1 (by rfl) ⟨4039358, by rfl⟩ : syracuseStep 5385811 = 8078717) B8078717
theorem B71840033 : Blo 1104625 71840033 := bstep (se 2 (by rfl) ⟨26940012, by rfl⟩ : syracuseStep 71840033 = 53880025) B53880025
theorem B24228503 : Blo 1104625 24228503 := bstep (se 1 (by rfl) ⟨18171377, by rfl⟩ : syracuseStep 24228503 = 36342755) B36342755
theorem B5976791 : Blo 1104625 5976791 := bstep (se 1 (by rfl) ⟨4482593, by rfl⟩ : syracuseStep 5976791 = 8965187) B8965187
theorem B2798327 : Blo 1104625 2798327 := bstep (se 1 (by rfl) ⟨2098745, by rfl⟩ : syracuseStep 2798327 = 4197491) B4197491
theorem B9450269 : Blo 1104625 9450269 := bstep (se 3 (by rfl) ⟨1771925, by rfl⟩ : syracuseStep 9450269 = 3543851) B3543851
theorem B11973689 : Blo 1104625 11973689 := bstep (se 2 (by rfl) ⟨4490133, by rfl⟩ : syracuseStep 11973689 = 8980267) B8980267
theorem B10630439 : Blo 1104625 10630439 := bstep (se 1 (by rfl) ⟨7972829, by rfl⟩ : syracuseStep 10630439 = 15945659) B15945659
theorem B2798945 : Blo 1104625 2798945 := bstep (se 2 (by rfl) ⟨1049604, by rfl⟩ : syracuseStep 2798945 = 2099209) B2099209
theorem B10106375 : Blo 1104625 10106375 := bstep (se 1 (by rfl) ⟨7579781, by rfl⟩ : syracuseStep 10106375 = 15159563) B15159563
theorem B35862425 : Blo 1104625 35862425 := bstep (se 2 (by rfl) ⟨13448409, by rfl⟩ : syracuseStep 35862425 = 26896819) B26896819
theorem B4733063 : Blo 1104625 4733063 := bstep (se 1 (by rfl) ⟨3549797, by rfl⟩ : syracuseStep 4733063 = 7099595) B7099595
theorem B4733113 : Blo 1104625 4733113 := bstep (se 2 (by rfl) ⟨1774917, by rfl⟩ : syracuseStep 4733113 = 3549835) B3549835
theorem B5454253 : Blo 1104625 5454253 := bstep (se 3 (by rfl) ⟨1022672, by rfl⟩ : syracuseStep 5454253 = 2045345) B2045345
theorem B6306443 : Blo 1104625 6306443 := bstep (se 1 (by rfl) ⟨4729832, by rfl⟩ : syracuseStep 6306443 = 9459665) B9459665
theorem B2800403 : Blo 1104625 2800403 := bstep (se 1 (by rfl) ⟨2100302, by rfl⟩ : syracuseStep 2800403 = 4200605) B4200605
theorem B91011869 : Blo 1104625 91011869 := bstep (se 3 (by rfl) ⟨17064725, by rfl⟩ : syracuseStep 91011869 = 34129451) B34129451
theorem B2800615 : Blo 1104625 2800615 := bstep (se 1 (by rfl) ⟨2100461, by rfl⟩ : syracuseStep 2800615 = 4200923) B4200923
theorem B2800889 : Blo 1104625 2800889 := bstep (se 2 (by rfl) ⟨1050333, by rfl⟩ : syracuseStep 2800889 = 2100667) B2100667
theorem B10763857 : Blo 1104625 10763857 := bstep (se 2 (by rfl) ⟨4036446, by rfl⟩ : syracuseStep 10763857 = 8072893) B8072893
theorem B1261391 : Blo 1104625 1261391 := bstep (se 1 (by rfl) ⟨946043, by rfl⟩ : syracuseStep 1261391 = 1892087) B1892087
theorem B2801537 : Blo 1104625 2801537 := bstep (se 2 (by rfl) ⟨1050576, by rfl⟩ : syracuseStep 2801537 = 2101153) B2101153
theorem B2802347 : Blo 1104625 2802347 := bstep (se 1 (by rfl) ⟨2101760, by rfl⟩ : syracuseStep 2802347 = 4203521) B4203521
theorem B3687095 : Blo 1104625 3687095 := bstep (se 1 (by rfl) ⟨2765321, by rfl⟩ : syracuseStep 3687095 = 5530643) B5530643
theorem B11092729 : Blo 1104625 11092729 := bstep (se 2 (by rfl) ⟨4159773, by rfl⟩ : syracuseStep 11092729 = 8319547) B8319547
theorem B3588943 : Blo 1104625 3588943 := bstep (se 1 (by rfl) ⟨2691707, by rfl⟩ : syracuseStep 3588943 = 5383415) B5383415
theorem B8405855 : Blo 1104625 8405855 := bstep (se 1 (by rfl) ⟨6304391, by rfl⟩ : syracuseStep 8405855 = 12608783) B12608783
theorem B5981309 : Blo 1104625 5981309 := bstep (se 3 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 5981309 = 2242991) B2242991
theorem B9585863 : Blo 1104625 9585863 := bstep (se 1 (by rfl) ⟨7189397, by rfl⟩ : syracuseStep 9585863 = 14378795) B14378795
theorem B2803207 : Blo 1104625 2803207 := bstep (se 1 (by rfl) ⟨2102405, by rfl⟩ : syracuseStep 2803207 = 4204811) B4204811
theorem B2803511 : Blo 1104625 2803511 := bstep (se 1 (by rfl) ⟨2102633, by rfl⟩ : syracuseStep 2803511 = 4205267) B4205267
theorem B10635245 : Blo 1104625 10635245 := bstep (se 3 (by rfl) ⟨1994108, by rfl⟩ : syracuseStep 10635245 = 3988217) B3988217
theorem B45467729 : Blo 1104625 45467729 := bstep (se 2 (by rfl) ⟨17050398, by rfl⟩ : syracuseStep 45467729 = 34100797) B34100797
theorem B1657097 : Blo 1104625 1657097 := bstep (se 2 (by rfl) ⟨621411, by rfl⟩ : syracuseStep 1657097 = 1242823) B1242823
theorem B1657199 : Blo 1104625 1657199 := bstep (se 1 (by rfl) ⟨1242899, by rfl⟩ : syracuseStep 1657199 = 2485799) B2485799
theorem B2804179 : Blo 1104625 2804179 := bstep (se 1 (by rfl) ⟨2103134, by rfl⟩ : syracuseStep 2804179 = 4206269) B4206269
theorem B1657415 : Blo 1104625 1657415 := bstep (se 1 (by rfl) ⟨1243061, by rfl⟩ : syracuseStep 1657415 = 2486123) B2486123
theorem B2837063 : Blo 1104625 2837063 := bstep (se 1 (by rfl) ⟨2127797, by rfl⟩ : syracuseStep 2837063 = 4255595) B4255595
theorem B1657451 : Blo 1104625 1657451 := bstep (se 1 (by rfl) ⟨1243088, by rfl⟩ : syracuseStep 1657451 = 2486177) B2486177
theorem B8407799 : Blo 1104625 8407799 := bstep (se 1 (by rfl) ⟨6305849, by rfl⟩ : syracuseStep 8407799 = 12611699) B12611699
theorem B10636049 : Blo 1104625 10636049 := bstep (se 2 (by rfl) ⟨3988518, by rfl⟩ : syracuseStep 10636049 = 7977037) B7977037
theorem B1657679 : Blo 1104625 1657679 := bstep (se 1 (by rfl) ⟨1243259, by rfl⟩ : syracuseStep 1657679 = 2486519) B2486519
theorem B1658075 : Blo 1104625 1658075 := bstep (se 1 (by rfl) ⟨1243556, by rfl⟩ : syracuseStep 1658075 = 2487113) B2487113
theorem B2804969 : Blo 1104625 2804969 := bstep (se 2 (by rfl) ⟨1051863, by rfl⟩ : syracuseStep 2804969 = 2103727) B2103727
theorem B2837791 : Blo 1104625 2837791 := bstep (se 1 (by rfl) ⟨2128343, by rfl⟩ : syracuseStep 2837791 = 4256687) B4256687
theorem B1658249 : Blo 1104625 1658249 := bstep (se 2 (by rfl) ⟨621843, by rfl⟩ : syracuseStep 1658249 = 1243687) B1243687
theorem B2805131 : Blo 1104625 2805131 := bstep (se 1 (by rfl) ⟨2103848, by rfl⟩ : syracuseStep 2805131 = 4207697) B4207697
theorem B24235463 : Blo 1104625 24235463 := bstep (se 1 (by rfl) ⟨18176597, by rfl⟩ : syracuseStep 24235463 = 36353195) B36353195
theorem B2838203 : Blo 1104625 2838203 := bstep (se 1 (by rfl) ⟨2128652, by rfl⟩ : syracuseStep 2838203 = 4257305) B4257305
theorem B1658603 : Blo 1104625 1658603 := bstep (se 1 (by rfl) ⟨1243952, by rfl⟩ : syracuseStep 1658603 = 2487905) B2487905
theorem B1658831 : Blo 1104625 1658831 := bstep (se 1 (by rfl) ⟨1244123, by rfl⟩ : syracuseStep 1658831 = 2488247) B2488247
theorem B10113281 : Blo 1104625 10113281 := bstep (se 2 (by rfl) ⟨3792480, by rfl⟩ : syracuseStep 10113281 = 7584961) B7584961
theorem B1659227 : Blo 1104625 1659227 := bstep (se 1 (by rfl) ⟨1244420, by rfl⟩ : syracuseStep 1659227 = 2488841) B2488841
theorem B2806123 : Blo 1104625 2806123 := bstep (se 1 (by rfl) ⟨2104592, by rfl⟩ : syracuseStep 2806123 = 4209185) B4209185
theorem B1659455 : Blo 1104625 1659455 := bstep (se 1 (by rfl) ⟨1244591, by rfl⟩ : syracuseStep 1659455 = 2489183) B2489183
theorem B1659575 : Blo 1104625 1659575 := bstep (se 1 (by rfl) ⟨1244681, by rfl⟩ : syracuseStep 1659575 = 2489363) B2489363
theorem B10638047 : Blo 1104625 10638047 := bstep (se 1 (by rfl) ⟨7978535, by rfl⟩ : syracuseStep 10638047 = 15957071) B15957071
theorem B6574891 : Blo 1104625 6574891 := bstep (se 1 (by rfl) ⟨4931168, by rfl⟩ : syracuseStep 6574891 = 9862337) B9862337
theorem B1659803 : Blo 1104625 1659803 := bstep (se 1 (by rfl) ⟨1244852, by rfl⟩ : syracuseStep 1659803 = 2489705) B2489705
theorem B3789787 : Blo 1104625 3789787 := bstep (se 1 (by rfl) ⟨2842340, by rfl⟩ : syracuseStep 3789787 = 5684681) B5684681
theorem B6313049 : Blo 1104625 6313049 := bstep (se 2 (by rfl) ⟨2367393, by rfl⟩ : syracuseStep 6313049 = 4734787) B4734787
theorem B8967293 : Blo 1104625 8967293 := bstep (se 3 (by rfl) ⟨1681367, by rfl⟩ : syracuseStep 8967293 = 3362735) B3362735
theorem B1398055 : Blo 1104625 1398055 := bstep (se 1 (by rfl) ⟨1048541, by rfl⟩ : syracuseStep 1398055 = 2097083) B2097083
theorem B1660199 : Blo 1104625 1660199 := bstep (se 1 (by rfl) ⟨1245149, by rfl⟩ : syracuseStep 1660199 = 2490299) B2490299
theorem B1660283 : Blo 1104625 1660283 := bstep (se 1 (by rfl) ⟨1245212, by rfl⟩ : syracuseStep 1660283 = 2490425) B2490425
theorem B3036631 : Blo 1104625 3036631 := bstep (se 1 (by rfl) ⟨2277473, by rfl⟩ : syracuseStep 3036631 = 4554947) B4554947
theorem B1660409 : Blo 1104625 1660409 := bstep (se 2 (by rfl) ⟨622653, by rfl⟩ : syracuseStep 1660409 = 1245307) B1245307
theorem B1660511 : Blo 1104625 1660511 := bstep (se 1 (by rfl) ⟨1245383, by rfl⟩ : syracuseStep 1660511 = 2490767) B2490767
theorem B1398379 : Blo 1104625 1398379 := bstep (se 1 (by rfl) ⟨1048784, by rfl⟩ : syracuseStep 1398379 = 2097569) B2097569
theorem B5592887 : Blo 1104625 5592887 := bstep (se 1 (by rfl) ⟨4194665, by rfl⟩ : syracuseStep 5592887 = 8389331) B8389331
theorem B1660727 : Blo 1104625 1660727 := bstep (se 1 (by rfl) ⟨1245545, by rfl⟩ : syracuseStep 1660727 = 2491091) B2491091
theorem B1661033 : Blo 1104625 1661033 := bstep (se 2 (by rfl) ⟨622887, by rfl⟩ : syracuseStep 1661033 = 1245775) B1245775
theorem B5593373 : Blo 1104625 5593373 := bstep (se 3 (by rfl) ⟨1048757, by rfl⟩ : syracuseStep 5593373 = 2097515) B2097515
theorem B1661351 : Blo 1104625 1661351 := bstep (se 1 (by rfl) ⟨1246013, by rfl⟩ : syracuseStep 1661351 = 2492027) B2492027
theorem B1661435 : Blo 1104625 1661435 := bstep (se 1 (by rfl) ⟨1246076, by rfl⟩ : syracuseStep 1661435 = 2492153) B2492153
theorem B8411687 : Blo 1104625 8411687 := bstep (se 1 (by rfl) ⟨6308765, by rfl⟩ : syracuseStep 8411687 = 12617531) B12617531
theorem B1661561 : Blo 1104625 1661561 := bstep (se 2 (by rfl) ⟨623085, by rfl⟩ : syracuseStep 1661561 = 1246171) B1246171
theorem B1661615 : Blo 1104625 1661615 := bstep (se 1 (by rfl) ⟨1246211, by rfl⟩ : syracuseStep 1661615 = 2492423) B2492423
theorem B1661663 : Blo 1104625 1661663 := bstep (se 1 (by rfl) ⟨1246247, by rfl⟩ : syracuseStep 1661663 = 2492495) B2492495
theorem B1104687 : Blo 1104625 1104687 := bstep (se 1 (by rfl) ⟨828515, by rfl⟩ : syracuseStep 1104687 = 1657031) B1657031
theorem B1104795 : Blo 1104625 1104795 := bstep (se 1 (by rfl) ⟨828596, by rfl⟩ : syracuseStep 1104795 = 1657193) B1657193
theorem B1104847 : Blo 1104625 1104847 := bstep (se 1 (by rfl) ⟨828635, by rfl⟩ : syracuseStep 1104847 = 1657271) B1657271
theorem B1104871 : Blo 1104625 1104871 := bstep (se 1 (by rfl) ⟨828653, by rfl⟩ : syracuseStep 1104871 = 1657307) B1657307
theorem B1661927 : Blo 1104625 1661927 := bstep (se 1 (by rfl) ⟨1246445, by rfl⟩ : syracuseStep 1661927 = 2492891) B2492891
theorem B1662185 : Blo 1104625 1662185 := bstep (se 2 (by rfl) ⟨623319, by rfl⟩ : syracuseStep 1662185 = 1246639) B1246639
theorem B1105183 : Blo 1104625 1105183 := bstep (se 1 (by rfl) ⟨828887, by rfl⟩ : syracuseStep 1105183 = 1657775) B1657775
theorem B1400095 : Blo 1104625 1400095 := bstep (se 1 (by rfl) ⟨1050071, by rfl⟩ : syracuseStep 1400095 = 2100143) B2100143
theorem B1662239 : Blo 1104625 1662239 := bstep (se 1 (by rfl) ⟨1246679, by rfl⟩ : syracuseStep 1662239 = 2493359) B2493359
theorem B1105243 : Blo 1104625 1105243 := bstep (se 1 (by rfl) ⟨828932, by rfl⟩ : syracuseStep 1105243 = 1657865) B1657865
theorem B1105263 : Blo 1104625 1105263 := bstep (se 1 (by rfl) ⟨828947, by rfl⟩ : syracuseStep 1105263 = 1657895) B1657895
theorem B1105319 : Blo 1104625 1105319 := bstep (se 1 (by rfl) ⟨828989, by rfl⟩ : syracuseStep 1105319 = 1657979) B1657979
theorem B1662407 : Blo 1104625 1662407 := bstep (se 1 (by rfl) ⟨1246805, by rfl⟩ : syracuseStep 1662407 = 2493611) B2493611
theorem B1105403 : Blo 1104625 1105403 := bstep (se 1 (by rfl) ⟨829052, by rfl⟩ : syracuseStep 1105403 = 1658105) B1658105
theorem B27287063 : Blo 1104625 27287063 := bstep (se 1 (by rfl) ⟨20465297, by rfl⟩ : syracuseStep 27287063 = 40930595) B40930595
theorem B1105471 : Blo 1104625 1105471 := bstep (se 1 (by rfl) ⟨829103, by rfl⟩ : syracuseStep 1105471 = 1658207) B1658207
theorem B1105479 : Blo 1104625 1105479 := bstep (se 1 (by rfl) ⟨829109, by rfl⟩ : syracuseStep 1105479 = 1658219) B1658219
theorem B24239731 : Blo 1104625 24239731 := bstep (se 1 (by rfl) ⟨18179798, by rfl⟩ : syracuseStep 24239731 = 36359597) B36359597
theorem B1105631 : Blo 1104625 1105631 := bstep (se 1 (by rfl) ⟨829223, by rfl⟩ : syracuseStep 1105631 = 1658447) B1658447
theorem B1662761 : Blo 1104625 1662761 := bstep (se 2 (by rfl) ⟨623535, by rfl⟩ : syracuseStep 1662761 = 1247071) B1247071
theorem B1105711 : Blo 1104625 1105711 := bstep (se 1 (by rfl) ⟨829283, by rfl⟩ : syracuseStep 1105711 = 1658567) B1658567
theorem B5988143 : Blo 1104625 5988143 := bstep (se 1 (by rfl) ⟨4491107, by rfl⟩ : syracuseStep 5988143 = 8982215) B8982215
theorem B1662767 : Blo 1104625 1662767 := bstep (se 1 (by rfl) ⟨1247075, by rfl⟩ : syracuseStep 1662767 = 2494151) B2494151
theorem B1105819 : Blo 1104625 1105819 := bstep (se 1 (by rfl) ⟨829364, by rfl⟩ : syracuseStep 1105819 = 1658729) B1658729
theorem B17948591 : Blo 1104625 17948591 := bstep (se 1 (by rfl) ⟨13461443, by rfl⟩ : syracuseStep 17948591 = 26922887) B26922887
theorem B1105871 : Blo 1104625 1105871 := bstep (se 1 (by rfl) ⟨829403, by rfl⟩ : syracuseStep 1105871 = 1658807) B1658807
theorem B1105895 : Blo 1104625 1105895 := bstep (se 1 (by rfl) ⟨829421, by rfl⟩ : syracuseStep 1105895 = 1658843) B1658843
theorem B5595155 : Blo 1104625 5595155 := bstep (se 1 (by rfl) ⟨4196366, by rfl⟩ : syracuseStep 5595155 = 8392733) B8392733
theorem B76800149 : Blo 1104625 76800149 := bstep (se 6 (by rfl) ⟨1800003, by rfl⟩ : syracuseStep 76800149 = 3600007) B3600007
theorem B1106207 : Blo 1104625 1106207 := bstep (se 1 (by rfl) ⟨829655, by rfl⟩ : syracuseStep 1106207 = 1659311) B1659311
theorem B31875389 : Blo 1104625 31875389 := bstep (se 3 (by rfl) ⟨5976635, by rfl⟩ : syracuseStep 31875389 = 11953271) B11953271
theorem B1106267 : Blo 1104625 1106267 := bstep (se 1 (by rfl) ⟨829700, by rfl⟩ : syracuseStep 1106267 = 1659401) B1659401
theorem B1106287 : Blo 1104625 1106287 := bstep (se 1 (by rfl) ⟨829715, by rfl⟩ : syracuseStep 1106287 = 1659431) B1659431
theorem B1106343 : Blo 1104625 1106343 := bstep (se 1 (by rfl) ⟨829757, by rfl⟩ : syracuseStep 1106343 = 1659515) B1659515
theorem B1106427 : Blo 1104625 1106427 := bstep (se 1 (by rfl) ⟨829820, by rfl⟩ : syracuseStep 1106427 = 1659641) B1659641
theorem B1106495 : Blo 1104625 1106495 := bstep (se 1 (by rfl) ⟨829871, by rfl⟩ : syracuseStep 1106495 = 1659743) B1659743
theorem B1106503 : Blo 1104625 1106503 := bstep (se 1 (by rfl) ⟨829877, by rfl⟩ : syracuseStep 1106503 = 1659755) B1659755
theorem B1106655 : Blo 1104625 1106655 := bstep (se 1 (by rfl) ⟨829991, by rfl⟩ : syracuseStep 1106655 = 1659983) B1659983
theorem B1106735 : Blo 1104625 1106735 := bstep (se 1 (by rfl) ⟨830051, by rfl⟩ : syracuseStep 1106735 = 1660103) B1660103
theorem B1106843 : Blo 1104625 1106843 := bstep (se 1 (by rfl) ⟨830132, by rfl⟩ : syracuseStep 1106843 = 1660265) B1660265
theorem B1106895 : Blo 1104625 1106895 := bstep (se 1 (by rfl) ⟨830171, by rfl⟩ : syracuseStep 1106895 = 1660343) B1660343
theorem B1106919 : Blo 1104625 1106919 := bstep (se 1 (by rfl) ⟨830189, by rfl⟩ : syracuseStep 1106919 = 1660379) B1660379
theorem B3728375 : Blo 1104625 3728375 := bstep (se 1 (by rfl) ⟨2796281, by rfl⟩ : syracuseStep 3728375 = 5592563) B5592563
theorem B3990653 : Blo 1104625 3990653 := bstep (se 3 (by rfl) ⟨748247, by rfl⟩ : syracuseStep 3990653 = 1496495) B1496495
theorem B2843867 : Blo 1104625 2843867 := bstep (se 1 (by rfl) ⟨2132900, by rfl⟩ : syracuseStep 2843867 = 4265801) B4265801
theorem B1107231 : Blo 1104625 1107231 := bstep (se 1 (by rfl) ⟨830423, by rfl⟩ : syracuseStep 1107231 = 1660847) B1660847
theorem B1107291 : Blo 1104625 1107291 := bstep (se 1 (by rfl) ⟨830468, by rfl⟩ : syracuseStep 1107291 = 1660937) B1660937
theorem B1107311 : Blo 1104625 1107311 := bstep (se 1 (by rfl) ⟨830483, by rfl⟩ : syracuseStep 1107311 = 1660967) B1660967
theorem B1107367 : Blo 1104625 1107367 := bstep (se 1 (by rfl) ⟨830525, by rfl⟩ : syracuseStep 1107367 = 1661051) B1661051
theorem B1107451 : Blo 1104625 1107451 := bstep (se 1 (by rfl) ⟨830588, by rfl⟩ : syracuseStep 1107451 = 1661177) B1661177
theorem B1402363 : Blo 1104625 1402363 := bstep (se 1 (by rfl) ⟨1051772, by rfl⟩ : syracuseStep 1402363 = 2103545) B2103545
theorem B1107519 : Blo 1104625 1107519 := bstep (se 1 (by rfl) ⟨830639, by rfl⟩ : syracuseStep 1107519 = 1661279) B1661279
theorem B1107527 : Blo 1104625 1107527 := bstep (se 1 (by rfl) ⟨830645, by rfl⟩ : syracuseStep 1107527 = 1661291) B1661291
theorem B21292631 : Blo 1104625 21292631 := bstep (se 1 (by rfl) ⟨15969473, by rfl⟩ : syracuseStep 21292631 = 31938947) B31938947
theorem B1107679 : Blo 1104625 1107679 := bstep (se 1 (by rfl) ⟨830759, by rfl⟩ : syracuseStep 1107679 = 1661519) B1661519
theorem B1402591 : Blo 1104625 1402591 := bstep (se 1 (by rfl) ⟨1051943, by rfl⟩ : syracuseStep 1402591 = 2103887) B2103887
theorem B1107759 : Blo 1104625 1107759 := bstep (se 1 (by rfl) ⟨830819, by rfl⟩ : syracuseStep 1107759 = 1661639) B1661639
theorem B3729239 : Blo 1104625 3729239 := bstep (se 1 (by rfl) ⟨2796929, by rfl⟩ : syracuseStep 3729239 = 5593859) B5593859
theorem B1107867 : Blo 1104625 1107867 := bstep (se 1 (by rfl) ⟨830900, by rfl⟩ : syracuseStep 1107867 = 1661801) B1661801
theorem B1107919 : Blo 1104625 1107919 := bstep (se 1 (by rfl) ⟨830939, by rfl⟩ : syracuseStep 1107919 = 1661879) B1661879
theorem B1107943 : Blo 1104625 1107943 := bstep (se 1 (by rfl) ⟨830957, by rfl⟩ : syracuseStep 1107943 = 1661915) B1661915
theorem B1108255 : Blo 1104625 1108255 := bstep (se 1 (by rfl) ⟨831191, by rfl⟩ : syracuseStep 1108255 = 1662383) B1662383
theorem B1108315 : Blo 1104625 1108315 := bstep (se 1 (by rfl) ⟨831236, by rfl⟩ : syracuseStep 1108315 = 1662473) B1662473
theorem B1108335 : Blo 1104625 1108335 := bstep (se 1 (by rfl) ⟨831251, by rfl⟩ : syracuseStep 1108335 = 1662503) B1662503
theorem B1108391 : Blo 1104625 1108391 := bstep (se 1 (by rfl) ⟨831293, by rfl⟩ : syracuseStep 1108391 = 1662587) B1662587
theorem B21260717 : Blo 1104625 21260717 := bstep (se 3 (by rfl) ⟨3986384, by rfl⟩ : syracuseStep 21260717 = 7972769) B7972769
theorem B1108475 : Blo 1104625 1108475 := bstep (se 1 (by rfl) ⟨831356, by rfl⟩ : syracuseStep 1108475 = 1662713) B1662713
theorem B1108543 : Blo 1104625 1108543 := bstep (se 1 (by rfl) ⟨831407, by rfl⟩ : syracuseStep 1108543 = 1662815) B1662815
theorem B1108551 : Blo 1104625 1108551 := bstep (se 1 (by rfl) ⟨831413, by rfl⟩ : syracuseStep 1108551 = 1662827) B1662827
theorem B10644047 : Blo 1104625 10644047 := bstep (se 1 (by rfl) ⟨7983035, by rfl⟩ : syracuseStep 10644047 = 15966071) B15966071
theorem B1993337 : Blo 1104625 1993337 := bstep (se 2 (by rfl) ⟨747501, by rfl⟩ : syracuseStep 1993337 = 1495003) B1495003
theorem B1796783 : Blo 1104625 1796783 := bstep (se 1 (by rfl) ⟨1347587, by rfl⟩ : syracuseStep 1796783 = 2695175) B2695175
theorem B5598071 : Blo 1104625 5598071 := bstep (se 1 (by rfl) ⟨4198553, by rfl⟩ : syracuseStep 5598071 = 8397107) B8397107
theorem B3730319 : Blo 1104625 3730319 := bstep (se 1 (by rfl) ⟨2797739, by rfl⟩ : syracuseStep 3730319 = 5595479) B5595479
theorem B2485601 : Blo 1104625 2485601 := bstep (se 2 (by rfl) ⟨932100, by rfl⟩ : syracuseStep 2485601 = 1864201) B1864201
theorem B4484489 : Blo 1104625 4484489 := bstep (se 2 (by rfl) ⟨1681683, by rfl⟩ : syracuseStep 4484489 = 3363367) B3363367
theorem B2485691 : Blo 1104625 2485691 := bstep (se 1 (by rfl) ⟨1864268, by rfl⟩ : syracuseStep 2485691 = 3728537) B3728537
theorem B40431035 : Blo 1104625 40431035 := bstep (se 1 (by rfl) ⟨30323276, by rfl⟩ : syracuseStep 40431035 = 60646553) B60646553
theorem B2485817 : Blo 1104625 2485817 := bstep (se 2 (by rfl) ⟨932181, by rfl⟩ : syracuseStep 2485817 = 1864363) B1864363
theorem B5598881 : Blo 1104625 5598881 := bstep (se 2 (by rfl) ⟨2099580, by rfl⟩ : syracuseStep 5598881 = 4199161) B4199161
theorem B3731561 : Blo 1104625 3731561 := bstep (se 2 (by rfl) ⟨1399335, by rfl⟩ : syracuseStep 3731561 = 2798671) B2798671
theorem B2486483 : Blo 1104625 2486483 := bstep (se 1 (by rfl) ⟨1864862, by rfl⟩ : syracuseStep 2486483 = 3729725) B3729725
theorem B2486537 : Blo 1104625 2486537 := bstep (se 2 (by rfl) ⟨932451, by rfl⟩ : syracuseStep 2486537 = 1864903) B1864903
theorem B2486753 : Blo 1104625 2486753 := bstep (se 2 (by rfl) ⟨932532, by rfl⟩ : syracuseStep 2486753 = 1865065) B1865065
theorem B9466429 : Blo 1104625 9466429 := bstep (se 3 (by rfl) ⟨1774955, by rfl⟩ : syracuseStep 9466429 = 3549911) B3549911
theorem B1864255 : Blo 1104625 1864255 := bstep (se 1 (by rfl) ⟨1398191, by rfl⟩ : syracuseStep 1864255 = 2796383) B2796383
theorem B2487059 : Blo 1104625 2487059 := bstep (se 1 (by rfl) ⟨1865294, by rfl⟩ : syracuseStep 2487059 = 3730589) B3730589
theorem B9466703 : Blo 1104625 9466703 := bstep (se 1 (by rfl) ⟨7100027, by rfl⟩ : syracuseStep 9466703 = 14200055) B14200055
theorem B3732425 : Blo 1104625 3732425 := bstep (se 2 (by rfl) ⟨1399659, by rfl⟩ : syracuseStep 3732425 = 2799319) B2799319
theorem B2487419 : Blo 1104625 2487419 := bstep (se 1 (by rfl) ⟨1865564, by rfl⟩ : syracuseStep 2487419 = 3731129) B3731129
theorem B3732695 : Blo 1104625 3732695 := bstep (se 1 (by rfl) ⟨2799521, by rfl⟩ : syracuseStep 3732695 = 5599043) B5599043
theorem B1864937 : Blo 1104625 1864937 := bstep (se 2 (by rfl) ⟨699351, by rfl⟩ : syracuseStep 1864937 = 1398703) B1398703
theorem B2487545 : Blo 1104625 2487545 := bstep (se 2 (by rfl) ⟨932829, by rfl⟩ : syracuseStep 2487545 = 1865659) B1865659
theorem B1864991 : Blo 1104625 1864991 := bstep (se 1 (by rfl) ⟨1398743, by rfl⟩ : syracuseStep 1864991 = 2797487) B2797487
theorem B2487689 : Blo 1104625 2487689 := bstep (se 2 (by rfl) ⟨932883, by rfl⟩ : syracuseStep 2487689 = 1865767) B1865767
theorem B6387083 : Blo 1104625 6387083 := bstep (se 1 (by rfl) ⟨4790312, by rfl⟩ : syracuseStep 6387083 = 9580625) B9580625
theorem B2487815 : Blo 1104625 2487815 := bstep (se 1 (by rfl) ⟨1865861, by rfl⟩ : syracuseStep 2487815 = 3731723) B3731723
theorem B12613157 : Blo 1104625 12613157 := bstep (se 4 (by rfl) ⟨1182483, by rfl⟩ : syracuseStep 12613157 = 2364967) B2364967
theorem B5600825 : Blo 1104625 5600825 := bstep (se 2 (by rfl) ⟨2100309, by rfl⟩ : syracuseStep 5600825 = 4200619) B4200619
theorem B2487995 : Blo 1104625 2487995 := bstep (se 1 (by rfl) ⟨1865996, by rfl⟩ : syracuseStep 2487995 = 3731993) B3731993
theorem B2488121 : Blo 1104625 2488121 := bstep (se 2 (by rfl) ⟨933045, by rfl⟩ : syracuseStep 2488121 = 1866091) B1866091
theorem B15955805 : Blo 1104625 15955805 := bstep (se 3 (by rfl) ⟨2991713, by rfl⟩ : syracuseStep 15955805 = 5983427) B5983427
theorem B1243111 : Blo 1104625 1243111 := bstep (se 1 (by rfl) ⟨932333, by rfl⟩ : syracuseStep 1243111 = 1864667) B1864667
theorem B2488751 : Blo 1104625 2488751 := bstep (se 1 (by rfl) ⟨1866563, by rfl⟩ : syracuseStep 2488751 = 3733127) B3733127
theorem B2488787 : Blo 1104625 2488787 := bstep (se 1 (by rfl) ⟨1866590, by rfl⟩ : syracuseStep 2488787 = 3733181) B3733181
theorem B2488895 : Blo 1104625 2488895 := bstep (se 1 (by rfl) ⟨1866671, by rfl⟩ : syracuseStep 2488895 = 3733343) B3733343
theorem B1866361 : Blo 1104625 1866361 := bstep (se 2 (by rfl) ⟨699885, by rfl⟩ : syracuseStep 1866361 = 1399771) B1399771
theorem B2489003 : Blo 1104625 2489003 := bstep (se 1 (by rfl) ⟨1866752, by rfl⟩ : syracuseStep 2489003 = 3733505) B3733505
theorem B1866415 : Blo 1104625 1866415 := bstep (se 1 (by rfl) ⟨1399811, by rfl⟩ : syracuseStep 1866415 = 2799623) B2799623
theorem B2489543 : Blo 1104625 2489543 := bstep (se 1 (by rfl) ⟨1867157, by rfl⟩ : syracuseStep 2489543 = 3734315) B3734315
theorem B3734747 : Blo 1104625 3734747 := bstep (se 1 (by rfl) ⟨2801060, by rfl⟩ : syracuseStep 3734747 = 5602121) B5602121
theorem B2489723 : Blo 1104625 2489723 := bstep (se 1 (by rfl) ⟨1867292, by rfl⟩ : syracuseStep 2489723 = 3734585) B3734585
theorem B2489849 : Blo 1104625 2489849 := bstep (se 2 (by rfl) ⟨933693, by rfl⟩ : syracuseStep 2489849 = 1867387) B1867387
theorem B2489939 : Blo 1104625 2489939 := bstep (se 1 (by rfl) ⟨1867454, by rfl⟩ : syracuseStep 2489939 = 3734909) B3734909
theorem B1244767 : Blo 1104625 1244767 := bstep (se 1 (by rfl) ⟨933575, by rfl⟩ : syracuseStep 1244767 = 1867151) B1867151
theorem B5602931 : Blo 1104625 5602931 := bstep (se 1 (by rfl) ⟨4202198, by rfl⟩ : syracuseStep 5602931 = 8404397) B8404397
theorem B8388359 : Blo 1104625 8388359 := bstep (se 1 (by rfl) ⟨6291269, by rfl⟩ : syracuseStep 8388359 = 12582539) B12582539
theorem B2490119 : Blo 1104625 2490119 := bstep (se 1 (by rfl) ⟨1867589, by rfl⟩ : syracuseStep 2490119 = 3735179) B3735179
theorem B2490407 : Blo 1104625 2490407 := bstep (se 1 (by rfl) ⟨1867805, by rfl⟩ : syracuseStep 2490407 = 3735611) B3735611
theorem B2490587 : Blo 1104625 2490587 := bstep (se 1 (by rfl) ⟨1867940, by rfl⟩ : syracuseStep 2490587 = 3735881) B3735881
theorem B1245415 : Blo 1104625 1245415 := bstep (se 1 (by rfl) ⟨934061, by rfl⟩ : syracuseStep 1245415 = 1868123) B1868123
theorem B2359739 : Blo 1104625 2359739 := bstep (se 1 (by rfl) ⟨1769804, by rfl⟩ : syracuseStep 2359739 = 3539609) B3539609
theorem B1868231 : Blo 1104625 1868231 := bstep (se 1 (by rfl) ⟨1401173, by rfl⟩ : syracuseStep 1868231 = 2802347) B2802347
theorem B2458063 : Blo 1104625 2458063 := bstep (se 1 (by rfl) ⟨1843547, by rfl⟩ : syracuseStep 2458063 = 3687095) B3687095
theorem B2490857 : Blo 1104625 2490857 := bstep (se 2 (by rfl) ⟨934071, by rfl⟩ : syracuseStep 2490857 = 1868143) B1868143
theorem B5603903 : Blo 1104625 5603903 := bstep (se 1 (by rfl) ⟨4202927, by rfl⟩ : syracuseStep 5603903 = 8405855) B8405855
theorem B2491145 : Blo 1104625 2491145 := bstep (se 2 (by rfl) ⟨934179, by rfl⟩ : syracuseStep 2491145 = 1868359) B1868359
theorem B6390575 : Blo 1104625 6390575 := bstep (se 1 (by rfl) ⟨4792931, by rfl⟩ : syracuseStep 6390575 = 9585863) B9585863
theorem B3736367 : Blo 1104625 3736367 := bstep (se 1 (by rfl) ⟨2802275, by rfl⟩ : syracuseStep 3736367 = 5604551) B5604551
theorem B1246063 : Blo 1104625 1246063 := bstep (se 1 (by rfl) ⟨934547, by rfl⟩ : syracuseStep 1246063 = 1869095) B1869095
theorem B3736475 : Blo 1104625 3736475 := bstep (se 1 (by rfl) ⟨2802356, by rfl⟩ : syracuseStep 3736475 = 5604713) B5604713
theorem B1770491 : Blo 1104625 1770491 := bstep (se 1 (by rfl) ⟨1327868, by rfl⟩ : syracuseStep 1770491 = 2655737) B2655737
theorem B4785257 : Blo 1104625 4785257 := bstep (se 2 (by rfl) ⟨1794471, by rfl⟩ : syracuseStep 4785257 = 3588943) B3588943
theorem B1869007 : Blo 1104625 1869007 := bstep (se 1 (by rfl) ⟨1401755, by rfl⟩ : syracuseStep 1869007 = 2803511) B2803511
theorem B2491721 : Blo 1104625 2491721 := bstep (se 2 (by rfl) ⟨934395, by rfl⟩ : syracuseStep 2491721 = 1868791) B1868791
theorem B30311819 : Blo 1104625 30311819 := bstep (se 1 (by rfl) ⟨22733864, by rfl⟩ : syracuseStep 30311819 = 45467729) B45467729
theorem B4196063 : Blo 1104625 4196063 := bstep (se 1 (by rfl) ⟨3147047, by rfl⟩ : syracuseStep 4196063 = 6294095) B6294095
theorem B5605199 : Blo 1104625 5605199 := bstep (se 1 (by rfl) ⟨4203899, by rfl⟩ : syracuseStep 5605199 = 8407799) B8407799
theorem B1869817 : Blo 1104625 1869817 := bstep (se 2 (by rfl) ⟨701181, by rfl⟩ : syracuseStep 1869817 = 1402363) B1402363
theorem B3737609 : Blo 1104625 3737609 := bstep (se 2 (by rfl) ⟨1401603, by rfl⟩ : syracuseStep 3737609 = 2803207) B2803207
theorem B7079987 : Blo 1104625 7079987 := bstep (se 1 (by rfl) ⟨5309990, by rfl⟩ : syracuseStep 7079987 = 10619981) B10619981
theorem B6293639 : Blo 1104625 6293639 := bstep (se 1 (by rfl) ⟨4720229, by rfl⟩ : syracuseStep 6293639 = 9440459) B9440459
theorem B1771675 : Blo 1104625 1771675 := bstep (se 1 (by rfl) ⟨1328756, by rfl⟩ : syracuseStep 1771675 = 2657513) B2657513
theorem B1869979 : Blo 1104625 1869979 := bstep (se 1 (by rfl) ⟨1402484, by rfl⟩ : syracuseStep 1869979 = 2804969) B2804969
theorem B1870087 : Blo 1104625 1870087 := bstep (se 1 (by rfl) ⟨1402565, by rfl⟩ : syracuseStep 1870087 = 2805131) B2805131
theorem B2492711 : Blo 1104625 2492711 := bstep (se 1 (by rfl) ⟨1869533, by rfl⟩ : syracuseStep 2492711 = 3739067) B3739067
theorem B1870121 : Blo 1104625 1870121 := bstep (se 2 (by rfl) ⟨701295, by rfl⟩ : syracuseStep 1870121 = 1402591) B1402591
theorem B2099513 : Blo 1104625 2099513 := bstep (se 2 (by rfl) ⟨787317, by rfl⟩ : syracuseStep 2099513 = 1574635) B1574635
theorem B2492729 : Blo 1104625 2492729 := bstep (se 2 (by rfl) ⟨934773, by rfl⟩ : syracuseStep 2492729 = 1869547) B1869547
theorem B4721323 : Blo 1104625 4721323 := bstep (se 1 (by rfl) ⟨3540992, by rfl⟩ : syracuseStep 4721323 = 7081985) B7081985
theorem B4197035 : Blo 1104625 4197035 := bstep (se 1 (by rfl) ⟨3147776, by rfl⟩ : syracuseStep 4197035 = 6295553) B6295553
theorem B20188379 : Blo 1104625 20188379 := bstep (se 1 (by rfl) ⟨15141284, by rfl⟩ : syracuseStep 20188379 = 30282569) B30282569
theorem B1576201 : Blo 1104625 1576201 := bstep (se 2 (by rfl) ⟨591075, by rfl⟩ : syracuseStep 1576201 = 1182151) B1182151
theorem B3738905 : Blo 1104625 3738905 := bstep (se 2 (by rfl) ⟨1402089, by rfl⟩ : syracuseStep 3738905 = 2804179) B2804179
theorem B10620209 : Blo 1104625 10620209 := bstep (se 2 (by rfl) ⟨3982578, by rfl⟩ : syracuseStep 10620209 = 7965157) B7965157
theorem B3738959 : Blo 1104625 3738959 := bstep (se 1 (by rfl) ⟨2804219, by rfl⟩ : syracuseStep 3738959 = 5608439) B5608439
theorem B262016441 : Blo 1104625 262016441 := bstep (se 2 (by rfl) ⟨98256165, by rfl⟩ : syracuseStep 262016441 = 196512331) B196512331
theorem B2494025 : Blo 1104625 2494025 := bstep (se 2 (by rfl) ⟨935259, by rfl⟩ : syracuseStep 2494025 = 1870519) B1870519
theorem B4722553 : Blo 1104625 4722553 := bstep (se 2 (by rfl) ⟨1770957, by rfl⟩ : syracuseStep 4722553 = 3541915) B3541915
theorem B17961047 : Blo 1104625 17961047 := bstep (se 1 (by rfl) ⟨13470785, by rfl⟩ : syracuseStep 17961047 = 26941571) B26941571
theorem B30249065 : Blo 1104625 30249065 := bstep (se 2 (by rfl) ⟨11343399, by rfl⟩ : syracuseStep 30249065 = 22686799) B22686799
theorem B6295805 : Blo 1104625 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B3150191 : Blo 1104625 3150191 := bstep (se 1 (by rfl) ⟨2362643, by rfl⟩ : syracuseStep 3150191 = 4725287) B4725287
theorem B5607791 : Blo 1104625 5607791 := bstep (se 1 (by rfl) ⟨4205843, by rfl⟩ : syracuseStep 5607791 = 8411687) B8411687
theorem B3740255 : Blo 1104625 3740255 := bstep (se 1 (by rfl) ⟨2805191, by rfl⟩ : syracuseStep 3740255 = 5610383) B5610383
theorem B1774315 : Blo 1104625 1774315 := bstep (se 1 (by rfl) ⟨1330736, by rfl⟩ : syracuseStep 1774315 = 2661473) B2661473
theorem B7181081 : Blo 1104625 7181081 := bstep (se 2 (by rfl) ⟨2692905, by rfl⟩ : syracuseStep 7181081 = 5385811) B5385811
theorem B18191375 : Blo 1104625 18191375 := bstep (se 1 (by rfl) ⟨13643531, by rfl⟩ : syracuseStep 18191375 = 27287063) B27287063
theorem B2102345 : Blo 1104625 2102345 := bstep (se 2 (by rfl) ⟨788379, by rfl⟩ : syracuseStep 2102345 = 1576759) B1576759
theorem B4199633 : Blo 1104625 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B11965727 : Blo 1104625 11965727 := bstep (se 1 (by rfl) ⟨8974295, by rfl⟩ : syracuseStep 11965727 = 17948591) B17948591
theorem B3151673 : Blo 1104625 3151673 := bstep (se 2 (by rfl) ⟨1181877, by rfl⟩ : syracuseStep 3151673 = 2363755) B2363755
theorem B3741497 : Blo 1104625 3741497 := bstep (se 2 (by rfl) ⟨1403061, by rfl⟩ : syracuseStep 3741497 = 2806123) B2806123
theorem B4200407 : Blo 1104625 4200407 := bstep (se 1 (by rfl) ⟨3150305, by rfl⟩ : syracuseStep 4200407 = 6300611) B6300611
theorem B3414041 : Blo 1104625 3414041 := bstep (se 2 (by rfl) ⟨1280265, by rfl⟩ : syracuseStep 3414041 = 2560531) B2560531
theorem B12621905 : Blo 1104625 12621905 := bstep (se 2 (by rfl) ⟨4733214, by rfl⟩ : syracuseStep 12621905 = 9466429) B9466429
theorem B2660435 : Blo 1104625 2660435 := bstep (se 1 (by rfl) ⟨1995326, by rfl⟩ : syracuseStep 2660435 = 3990653) B3990653
theorem B6297695 : Blo 1104625 6297695 := bstep (se 1 (by rfl) ⟨4723271, by rfl⟩ : syracuseStep 6297695 = 9446543) B9446543
theorem B3152105 : Blo 1104625 3152105 := bstep (se 2 (by rfl) ⟨1182039, by rfl⟩ : syracuseStep 3152105 = 2364079) B2364079
theorem B14195087 : Blo 1104625 14195087 := bstep (se 1 (by rfl) ⟨10646315, by rfl⟩ : syracuseStep 14195087 = 21292631) B21292631
theorem B4200893 : Blo 1104625 4200893 := bstep (se 3 (by rfl) ⟨787667, by rfl⟩ : syracuseStep 4200893 = 1575335) B1575335
theorem B5053049 : Blo 1104625 5053049 := bstep (se 2 (by rfl) ⟨1894893, by rfl⟩ : syracuseStep 5053049 = 3789787) B3789787
theorem B2104289 : Blo 1104625 2104289 := bstep (se 2 (by rfl) ⟨789108, by rfl⟩ : syracuseStep 2104289 = 1578217) B1578217
theorem B4791421 : Blo 1104625 4791421 := bstep (se 3 (by rfl) ⟨898391, by rfl⟩ : syracuseStep 4791421 = 1796783) B1796783
theorem B11345291 : Blo 1104625 11345291 := bstep (se 1 (by rfl) ⟨8508968, by rfl⟩ : syracuseStep 11345291 = 17017937) B17017937
theorem B4202063 : Blo 1104625 4202063 := bstep (se 1 (by rfl) ⟨3151547, by rfl⟩ : syracuseStep 4202063 = 6303095) B6303095
theorem B6300179 : Blo 1104625 6300179 := bstep (se 1 (by rfl) ⟨4725134, by rfl⟩ : syracuseStep 6300179 = 9450269) B9450269
theorem B7086959 : Blo 1104625 7086959 := bstep (se 1 (by rfl) ⟨5315219, by rfl⟩ : syracuseStep 7086959 = 10630439) B10630439
theorem B107816093 : Blo 1104625 107816093 := bstep (se 3 (by rfl) ⟨20215517, by rfl⟩ : syracuseStep 107816093 = 40431035) B40431035
theorem B64627901 : Blo 1104625 64627901 := bstep (se 3 (by rfl) ⟨12117731, by rfl⟩ : syracuseStep 64627901 = 24235463) B24235463
theorem B3155375 : Blo 1104625 3155375 := bstep (se 1 (by rfl) ⟨2366531, by rfl⟩ : syracuseStep 3155375 = 4733063) B4733063
theorem B4040189 : Blo 1104625 4040189 := bstep (se 3 (by rfl) ⟨757535, by rfl⟩ : syracuseStep 4040189 = 1515071) B1515071
theorem B4204295 : Blo 1104625 4204295 := bstep (se 1 (by rfl) ⟨3153221, by rfl⟩ : syracuseStep 4204295 = 6306443) B6306443
theorem B32319641 : Blo 1104625 32319641 := bstep (se 2 (by rfl) ⟨12119865, by rfl⟩ : syracuseStep 32319641 = 24239731) B24239731
theorem B2797051 : Blo 1104625 2797051 := bstep (se 1 (by rfl) ⟨2097788, by rfl⟩ : syracuseStep 2797051 = 4195577) B4195577
theorem B2797163 : Blo 1104625 2797163 := bstep (se 1 (by rfl) ⟨2097872, by rfl⟩ : syracuseStep 2797163 = 4195745) B4195745
theorem B14790305 : Blo 1104625 14790305 := bstep (se 2 (by rfl) ⟨5546364, by rfl⟩ : syracuseStep 14790305 = 11092729) B11092729
theorem B7090163 : Blo 1104625 7090163 := bstep (se 1 (by rfl) ⟨5317622, by rfl⟩ : syracuseStep 7090163 = 10635245) B10635245
theorem B7090699 : Blo 1104625 7090699 := bstep (se 1 (by rfl) ⟨5318024, by rfl⟩ : syracuseStep 7090699 = 10636049) B10636049
theorem B4731473 : Blo 1104625 4731473 := bstep (se 2 (by rfl) ⟨1774302, by rfl⟩ : syracuseStep 4731473 = 3548605) B3548605
theorem B7092031 : Blo 1104625 7092031 := bstep (se 1 (by rfl) ⟨5319023, by rfl⟩ : syracuseStep 7092031 = 10638047) B10638047
theorem B7583645 : Blo 1104625 7583645 := bstep (se 3 (by rfl) ⟨1421933, by rfl⟩ : syracuseStep 7583645 = 2843867) B2843867
theorem B4208699 : Blo 1104625 4208699 := bstep (se 1 (by rfl) ⟨3156524, by rfl⟩ : syracuseStep 4208699 = 6313049) B6313049
theorem B5978195 : Blo 1104625 5978195 := bstep (se 1 (by rfl) ⟨4483646, by rfl⟩ : syracuseStep 5978195 = 8967293) B8967293
theorem B26950333 : Blo 1104625 26950333 := bstep (se 3 (by rfl) ⟨5053187, by rfl⟩ : syracuseStep 26950333 = 10106375) B10106375
theorem B349223669 : Blo 1104625 349223669 := bstep (se 5 (by rfl) ⟨16369859, by rfl⟩ : syracuseStep 349223669 = 32739719) B32739719
theorem B3783503 : Blo 1104625 3783503 := bstep (se 1 (by rfl) ⟨2837627, by rfl⟩ : syracuseStep 3783503 = 5675255) B5675255
theorem B3783721 : Blo 1104625 3783721 := bstep (se 2 (by rfl) ⟨1418895, by rfl⟩ : syracuseStep 3783721 = 2837791) B2837791
theorem B4734445 : Blo 1104625 4734445 := bstep (se 3 (by rfl) ⟨887708, by rfl⟩ : syracuseStep 4734445 = 1775417) B1775417
theorem B2801243 : Blo 1104625 2801243 := bstep (se 1 (by rfl) ⟨2100932, by rfl⟩ : syracuseStep 2801243 = 4201865) B4201865
theorem B6733739 : Blo 1104625 6733739 := bstep (se 1 (by rfl) ⟨5050304, by rfl⟩ : syracuseStep 6733739 = 10100609) B10100609
theorem B51200099 : Blo 1104625 51200099 := bstep (se 1 (by rfl) ⟨38400074, by rfl⟩ : syracuseStep 51200099 = 76800149) B76800149
theorem B21250259 : Blo 1104625 21250259 := bstep (se 1 (by rfl) ⟨15937694, by rfl⟩ : syracuseStep 21250259 = 31875389) B31875389
theorem B6734279 : Blo 1104625 6734279 := bstep (se 1 (by rfl) ⟨5050709, by rfl⟩ : syracuseStep 6734279 = 10101419) B10101419
theorem B3981887 : Blo 1104625 3981887 := bstep (se 1 (by rfl) ⟨2986415, by rfl⟩ : syracuseStep 3981887 = 5972831) B5972831
theorem B8766521 : Blo 1104625 8766521 := bstep (se 2 (by rfl) ⟨3287445, by rfl⟩ : syracuseStep 8766521 = 6574891) B6574891
theorem B14173811 : Blo 1104625 14173811 := bstep (se 1 (by rfl) ⟨10630358, by rfl⟩ : syracuseStep 14173811 = 21260717) B21260717
theorem B7096031 : Blo 1104625 7096031 := bstep (se 1 (by rfl) ⟨5322023, by rfl⟩ : syracuseStep 7096031 = 10644047) B10644047
theorem B1328891 : Blo 1104625 1328891 := bstep (se 1 (by rfl) ⟨996668, by rfl⟩ : syracuseStep 1328891 = 1993337) B1993337
theorem B4048841 : Blo 1104625 4048841 := bstep (se 2 (by rfl) ⟨1518315, by rfl⟩ : syracuseStep 4048841 = 3036631) B3036631
theorem B1657067 : Blo 1104625 1657067 := bstep (se 1 (by rfl) ⟨1242800, by rfl⟩ : syracuseStep 1657067 = 2485601) B2485601
theorem B1657127 : Blo 1104625 1657127 := bstep (se 1 (by rfl) ⟨1242845, by rfl⟩ : syracuseStep 1657127 = 2485691) B2485691
theorem B1657211 : Blo 1104625 1657211 := bstep (se 1 (by rfl) ⟨1242908, by rfl⟩ : syracuseStep 1657211 = 2485817) B2485817
theorem B28330397 : Blo 1104625 28330397 := bstep (se 3 (by rfl) ⟨5311949, by rfl⟩ : syracuseStep 28330397 = 10623899) B10623899
theorem B2804129 : Blo 1104625 2804129 := bstep (se 2 (by rfl) ⟨1051548, by rfl⟩ : syracuseStep 2804129 = 2103097) B2103097
theorem B1657481 : Blo 1104625 1657481 := bstep (se 2 (by rfl) ⟨621555, by rfl⟩ : syracuseStep 1657481 = 1243111) B1243111
theorem B1657655 : Blo 1104625 1657655 := bstep (se 1 (by rfl) ⟨1243241, by rfl⟩ : syracuseStep 1657655 = 2486483) B2486483
theorem B1657691 : Blo 1104625 1657691 := bstep (se 1 (by rfl) ⟨1243268, by rfl⟩ : syracuseStep 1657691 = 2486537) B2486537
theorem B47893355 : Blo 1104625 47893355 := bstep (se 1 (by rfl) ⟨35920016, by rfl⟩ : syracuseStep 47893355 = 71840033) B71840033
theorem B6310817 : Blo 1104625 6310817 := bstep (se 2 (by rfl) ⟨2366556, by rfl⟩ : syracuseStep 6310817 = 4733113) B4733113
theorem B1657835 : Blo 1104625 1657835 := bstep (se 1 (by rfl) ⟨1243376, by rfl⟩ : syracuseStep 1657835 = 2486753) B2486753
theorem B3984527 : Blo 1104625 3984527 := bstep (se 1 (by rfl) ⟨2988395, by rfl⟩ : syracuseStep 3984527 = 5976791) B5976791
theorem B1658039 : Blo 1104625 1658039 := bstep (se 1 (by rfl) ⟨1243529, by rfl⟩ : syracuseStep 1658039 = 2487059) B2487059
theorem B6311135 : Blo 1104625 6311135 := bstep (se 1 (by rfl) ⟨4733351, by rfl⟩ : syracuseStep 6311135 = 9466703) B9466703
theorem B7982459 : Blo 1104625 7982459 := bstep (se 1 (by rfl) ⟨5986844, by rfl⟩ : syracuseStep 7982459 = 11973689) B11973689
theorem B1658279 : Blo 1104625 1658279 := bstep (se 1 (by rfl) ⟨1243709, by rfl⟩ : syracuseStep 1658279 = 2487419) B2487419
theorem B1658363 : Blo 1104625 1658363 := bstep (se 1 (by rfl) ⟨1243772, by rfl⟩ : syracuseStep 1658363 = 2487545) B2487545
theorem B1658459 : Blo 1104625 1658459 := bstep (se 1 (by rfl) ⟨1243844, by rfl⟩ : syracuseStep 1658459 = 2487689) B2487689
theorem B1658543 : Blo 1104625 1658543 := bstep (se 1 (by rfl) ⟨1243907, by rfl⟩ : syracuseStep 1658543 = 2487815) B2487815
theorem B8408771 : Blo 1104625 8408771 := bstep (se 1 (by rfl) ⟨6306578, by rfl⟩ : syracuseStep 8408771 = 12613157) B12613157
theorem B1658663 : Blo 1104625 1658663 := bstep (se 1 (by rfl) ⟨1243997, by rfl⟩ : syracuseStep 1658663 = 2487995) B2487995
theorem B1658747 : Blo 1104625 1658747 := bstep (se 1 (by rfl) ⟨1244060, by rfl⟩ : syracuseStep 1658747 = 2488121) B2488121
theorem B10637203 : Blo 1104625 10637203 := bstep (se 1 (by rfl) ⟨7977902, by rfl⟩ : syracuseStep 10637203 = 15955805) B15955805
theorem B23908283 : Blo 1104625 23908283 := bstep (se 1 (by rfl) ⟨17931212, by rfl⟩ : syracuseStep 23908283 = 35862425) B35862425
theorem B11980781 : Blo 1104625 11980781 := bstep (se 3 (by rfl) ⟨2246396, by rfl⟩ : syracuseStep 11980781 = 4492793) B4492793
theorem B1659167 : Blo 1104625 1659167 := bstep (se 1 (by rfl) ⟨1244375, by rfl⟩ : syracuseStep 1659167 = 2488751) B2488751
theorem B1659191 : Blo 1104625 1659191 := bstep (se 1 (by rfl) ⟨1244393, by rfl⟩ : syracuseStep 1659191 = 2488787) B2488787
theorem B1659263 : Blo 1104625 1659263 := bstep (se 1 (by rfl) ⟨1244447, by rfl⟩ : syracuseStep 1659263 = 2488895) B2488895
theorem B1659335 : Blo 1104625 1659335 := bstep (se 1 (by rfl) ⟨1244501, by rfl⟩ : syracuseStep 1659335 = 2489003) B2489003
theorem B60674579 : Blo 1104625 60674579 := bstep (se 1 (by rfl) ⟨45505934, by rfl⟩ : syracuseStep 60674579 = 91011869) B91011869
theorem B1659689 : Blo 1104625 1659689 := bstep (se 2 (by rfl) ⟨622383, by rfl⟩ : syracuseStep 1659689 = 1244767) B1244767
theorem B1659695 : Blo 1104625 1659695 := bstep (se 1 (by rfl) ⟨1244771, by rfl⟩ : syracuseStep 1659695 = 2489543) B2489543
theorem B3363709 : Blo 1104625 3363709 := bstep (se 3 (by rfl) ⟨630695, by rfl⟩ : syracuseStep 3363709 = 1261391) B1261391
theorem B1659815 : Blo 1104625 1659815 := bstep (se 1 (by rfl) ⟨1244861, by rfl⟩ : syracuseStep 1659815 = 2489723) B2489723
theorem B1659899 : Blo 1104625 1659899 := bstep (se 1 (by rfl) ⟨1244924, by rfl⟩ : syracuseStep 1659899 = 2489849) B2489849
theorem B1659959 : Blo 1104625 1659959 := bstep (se 1 (by rfl) ⟨1244969, by rfl⟩ : syracuseStep 1659959 = 2489939) B2489939
theorem B5592239 : Blo 1104625 5592239 := bstep (se 1 (by rfl) ⟨4194179, by rfl⟩ : syracuseStep 5592239 = 8388359) B8388359
theorem B1660079 : Blo 1104625 1660079 := bstep (se 1 (by rfl) ⟨1245059, by rfl⟩ : syracuseStep 1660079 = 2490119) B2490119
theorem B1660487 : Blo 1104625 1660487 := bstep (se 1 (by rfl) ⟨1245365, by rfl⟩ : syracuseStep 1660487 = 2490731) B2490731
theorem B10638971 : Blo 1104625 10638971 := bstep (se 1 (by rfl) ⟨7979228, by rfl⟩ : syracuseStep 10638971 = 15958457) B15958457
theorem B1660583 : Blo 1104625 1660583 := bstep (se 1 (by rfl) ⟨1245437, by rfl⟩ : syracuseStep 1660583 = 2490875) B2490875
theorem B1660667 : Blo 1104625 1660667 := bstep (se 1 (by rfl) ⟨1245500, by rfl⟩ : syracuseStep 1660667 = 2491001) B2491001
theorem B1660703 : Blo 1104625 1660703 := bstep (se 1 (by rfl) ⟨1245527, by rfl⟩ : syracuseStep 1660703 = 2491055) B2491055
theorem B1660751 : Blo 1104625 1660751 := bstep (se 1 (by rfl) ⟨1245563, by rfl⟩ : syracuseStep 1660751 = 2491127) B2491127
theorem B1660871 : Blo 1104625 1660871 := bstep (se 1 (by rfl) ⟨1245653, by rfl⟩ : syracuseStep 1660871 = 2491307) B2491307
theorem B7296983 : Blo 1104625 7296983 := bstep (se 1 (by rfl) ⟨5472737, by rfl⟩ : syracuseStep 7296983 = 10945475) B10945475
theorem B4478959 : Blo 1104625 4478959 := bstep (se 1 (by rfl) ⟨3359219, by rfl⟩ : syracuseStep 4478959 = 6718439) B6718439
theorem B3987539 : Blo 1104625 3987539 := bstep (se 1 (by rfl) ⟨2990654, by rfl⟩ : syracuseStep 3987539 = 5981309) B5981309
theorem B12146959 : Blo 1104625 12146959 := bstep (se 1 (by rfl) ⟨9110219, by rfl⟩ : syracuseStep 12146959 = 18220439) B18220439
theorem B1661225 : Blo 1104625 1661225 := bstep (se 2 (by rfl) ⟨622959, by rfl⟩ : syracuseStep 1661225 = 1245919) B1245919
theorem B1661231 : Blo 1104625 1661231 := bstep (se 1 (by rfl) ⟨1245923, by rfl⟩ : syracuseStep 1661231 = 2491847) B2491847
theorem B1661471 : Blo 1104625 1661471 := bstep (se 1 (by rfl) ⟨1246103, by rfl⟩ : syracuseStep 1661471 = 2492207) B2492207
theorem B5593697 : Blo 1104625 5593697 := bstep (se 2 (by rfl) ⟨2097636, by rfl⟩ : syracuseStep 5593697 = 4195273) B4195273
theorem B1104731 : Blo 1104625 1104731 := bstep (se 1 (by rfl) ⟨828548, by rfl⟩ : syracuseStep 1104731 = 1657097) B1657097
theorem B1104799 : Blo 1104625 1104799 := bstep (se 1 (by rfl) ⟨828599, by rfl⟩ : syracuseStep 1104799 = 1657199) B1657199
theorem B1661855 : Blo 1104625 1661855 := bstep (se 1 (by rfl) ⟨1246391, by rfl⟩ : syracuseStep 1661855 = 2492783) B2492783
theorem B1661903 : Blo 1104625 1661903 := bstep (se 1 (by rfl) ⟨1246427, by rfl⟩ : syracuseStep 1661903 = 2492855) B2492855
theorem B1661993 : Blo 1104625 1661993 := bstep (se 2 (by rfl) ⟨623247, by rfl⟩ : syracuseStep 1661993 = 1246495) B1246495
theorem B1104943 : Blo 1104625 1104943 := bstep (se 1 (by rfl) ⟨828707, by rfl⟩ : syracuseStep 1104943 = 1657415) B1657415
theorem B1661999 : Blo 1104625 1661999 := bstep (se 1 (by rfl) ⟨1246499, by rfl⟩ : syracuseStep 1661999 = 2492999) B2492999
theorem B1104967 : Blo 1104625 1104967 := bstep (se 1 (by rfl) ⟨828725, by rfl⟩ : syracuseStep 1104967 = 1657451) B1657451
theorem B1662023 : Blo 1104625 1662023 := bstep (se 1 (by rfl) ⟨1246517, by rfl⟩ : syracuseStep 1662023 = 2493035) B2493035
theorem B1105119 : Blo 1104625 1105119 := bstep (se 1 (by rfl) ⟨828839, by rfl⟩ : syracuseStep 1105119 = 1657679) B1657679
theorem B3595529 : Blo 1104625 3595529 := bstep (se 2 (by rfl) ⟨1348323, by rfl⟩ : syracuseStep 3595529 = 2696647) B2696647
theorem B1662287 : Blo 1104625 1662287 := bstep (se 1 (by rfl) ⟨1246715, by rfl⟩ : syracuseStep 1662287 = 2493431) B2493431
theorem B5594507 : Blo 1104625 5594507 := bstep (se 1 (by rfl) ⟨4195880, by rfl⟩ : syracuseStep 5594507 = 8391761) B8391761
theorem B1662377 : Blo 1104625 1662377 := bstep (se 2 (by rfl) ⟨623391, by rfl⟩ : syracuseStep 1662377 = 1246783) B1246783
theorem B1105383 : Blo 1104625 1105383 := bstep (se 1 (by rfl) ⟨829037, by rfl⟩ : syracuseStep 1105383 = 1658075) B1658075
theorem B12115493 : Blo 1104625 12115493 := bstep (se 4 (by rfl) ⟨1135827, by rfl⟩ : syracuseStep 12115493 = 2271655) B2271655
theorem B1662527 : Blo 1104625 1662527 := bstep (se 1 (by rfl) ⟨1246895, by rfl⟩ : syracuseStep 1662527 = 2493791) B2493791
theorem B1105499 : Blo 1104625 1105499 := bstep (se 1 (by rfl) ⟨829124, by rfl⟩ : syracuseStep 1105499 = 1658249) B1658249
theorem B1892135 : Blo 1104625 1892135 := bstep (se 1 (by rfl) ⟨1419101, by rfl⟩ : syracuseStep 1892135 = 2838203) B2838203
theorem B6381359 : Blo 1104625 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B1105735 : Blo 1104625 1105735 := bstep (se 1 (by rfl) ⟨829301, by rfl⟩ : syracuseStep 1105735 = 1658603) B1658603
theorem B1400647 : Blo 1104625 1400647 := bstep (se 1 (by rfl) ⟨1050485, by rfl⟩ : syracuseStep 1400647 = 2100971) B2100971
theorem B1662791 : Blo 1104625 1662791 := bstep (se 1 (by rfl) ⟨1247093, by rfl⟩ : syracuseStep 1662791 = 2494187) B2494187
theorem B12607325 : Blo 1104625 12607325 := bstep (se 3 (by rfl) ⟨2363873, by rfl⟩ : syracuseStep 12607325 = 4727747) B4727747
theorem B1662875 : Blo 1104625 1662875 := bstep (se 1 (by rfl) ⟨1247156, by rfl⟩ : syracuseStep 1662875 = 2494313) B2494313
theorem B1105887 : Blo 1104625 1105887 := bstep (se 1 (by rfl) ⟨829415, by rfl⟩ : syracuseStep 1105887 = 1658831) B1658831
theorem B6742187 : Blo 1104625 6742187 := bstep (se 1 (by rfl) ⟨5056640, by rfl⟩ : syracuseStep 6742187 = 10113281) B10113281
theorem B1106151 : Blo 1104625 1106151 := bstep (se 1 (by rfl) ⟨829613, by rfl⟩ : syracuseStep 1106151 = 1659227) B1659227
theorem B1106303 : Blo 1104625 1106303 := bstep (se 1 (by rfl) ⟨829727, by rfl⟩ : syracuseStep 1106303 = 1659455) B1659455
theorem B1106383 : Blo 1104625 1106383 := bstep (se 1 (by rfl) ⟨829787, by rfl⟩ : syracuseStep 1106383 = 1659575) B1659575
theorem B1401295 : Blo 1104625 1401295 := bstep (se 1 (by rfl) ⟨1050971, by rfl⟩ : syracuseStep 1401295 = 2101943) B2101943
theorem B1106535 : Blo 1104625 1106535 := bstep (se 1 (by rfl) ⟨829901, by rfl⟩ : syracuseStep 1106535 = 1659803) B1659803
theorem B15950611 : Blo 1104625 15950611 := bstep (se 1 (by rfl) ⟨11962958, by rfl⟩ : syracuseStep 15950611 = 23925917) B23925917
theorem B1106799 : Blo 1104625 1106799 := bstep (se 1 (by rfl) ⟨830099, by rfl⟩ : syracuseStep 1106799 = 1660199) B1660199
theorem B8414117 : Blo 1104625 8414117 := bstep (se 4 (by rfl) ⟨788823, by rfl⟩ : syracuseStep 8414117 = 1577647) B1577647
theorem B1106855 : Blo 1104625 1106855 := bstep (se 1 (by rfl) ⟨830141, by rfl⟩ : syracuseStep 1106855 = 1660283) B1660283
theorem B1106939 : Blo 1104625 1106939 := bstep (se 1 (by rfl) ⟨830204, by rfl⟩ : syracuseStep 1106939 = 1660409) B1660409
theorem B1107007 : Blo 1104625 1107007 := bstep (se 1 (by rfl) ⟨830255, by rfl⟩ : syracuseStep 1107007 = 1660511) B1660511
theorem B3728591 : Blo 1104625 3728591 := bstep (se 1 (by rfl) ⟨2796443, by rfl⟩ : syracuseStep 3728591 = 5592887) B5592887
theorem B1107151 : Blo 1104625 1107151 := bstep (se 1 (by rfl) ⟨830363, by rfl⟩ : syracuseStep 1107151 = 1660727) B1660727
theorem B1107355 : Blo 1104625 1107355 := bstep (se 1 (by rfl) ⟨830516, by rfl⟩ : syracuseStep 1107355 = 1661033) B1661033
theorem B1402267 : Blo 1104625 1402267 := bstep (se 1 (by rfl) ⟨1051700, by rfl⟩ : syracuseStep 1402267 = 2103401) B2103401
theorem B3728915 : Blo 1104625 3728915 := bstep (se 1 (by rfl) ⟨2796686, by rfl⟩ : syracuseStep 3728915 = 5593373) B5593373
theorem B1107567 : Blo 1104625 1107567 := bstep (se 1 (by rfl) ⟨830675, by rfl⟩ : syracuseStep 1107567 = 1661351) B1661351
theorem B6481529 : Blo 1104625 6481529 := bstep (se 2 (by rfl) ⟨2430573, by rfl⟩ : syracuseStep 6481529 = 4861147) B4861147
theorem B1107623 : Blo 1104625 1107623 := bstep (se 1 (by rfl) ⟨830717, by rfl⟩ : syracuseStep 1107623 = 1661435) B1661435
theorem B1402535 : Blo 1104625 1402535 := bstep (se 1 (by rfl) ⟨1051901, by rfl⟩ : syracuseStep 1402535 = 2103803) B2103803
theorem B1107707 : Blo 1104625 1107707 := bstep (se 1 (by rfl) ⟨830780, by rfl⟩ : syracuseStep 1107707 = 1661561) B1661561
theorem B1107743 : Blo 1104625 1107743 := bstep (se 1 (by rfl) ⟨830807, by rfl⟩ : syracuseStep 1107743 = 1661615) B1661615
theorem B1107775 : Blo 1104625 1107775 := bstep (se 1 (by rfl) ⟨830831, by rfl⟩ : syracuseStep 1107775 = 1661663) B1661663
theorem B1402687 : Blo 1104625 1402687 := bstep (se 1 (by rfl) ⟨1052015, by rfl⟩ : syracuseStep 1402687 = 2104031) B2104031
theorem B1107951 : Blo 1104625 1107951 := bstep (se 1 (by rfl) ⟨830963, by rfl⟩ : syracuseStep 1107951 = 1661927) B1661927
theorem B1108123 : Blo 1104625 1108123 := bstep (se 1 (by rfl) ⟨831092, by rfl⟩ : syracuseStep 1108123 = 1662185) B1662185
theorem B1108159 : Blo 1104625 1108159 := bstep (se 1 (by rfl) ⟨831119, by rfl⟩ : syracuseStep 1108159 = 1662239) B1662239
theorem B1108271 : Blo 1104625 1108271 := bstep (se 1 (by rfl) ⟨831203, by rfl⟩ : syracuseStep 1108271 = 1662407) B1662407
theorem B1108507 : Blo 1104625 1108507 := bstep (se 1 (by rfl) ⟨831380, by rfl⟩ : syracuseStep 1108507 = 1662761) B1662761
theorem B3992095 : Blo 1104625 3992095 := bstep (se 1 (by rfl) ⟨2994071, by rfl⟩ : syracuseStep 3992095 = 5988143) B5988143
theorem B1108511 : Blo 1104625 1108511 := bstep (se 1 (by rfl) ⟨831383, by rfl⟩ : syracuseStep 1108511 = 1662767) B1662767
theorem B3730103 : Blo 1104625 3730103 := bstep (se 1 (by rfl) ⟨2797577, by rfl⟩ : syracuseStep 3730103 = 5595155) B5595155
theorem B4484231 : Blo 1104625 4484231 := bstep (se 1 (by rfl) ⟨3363173, by rfl⟩ : syracuseStep 4484231 = 6726347) B6726347
theorem B2485583 : Blo 1104625 2485583 := bstep (se 1 (by rfl) ⟨1864187, by rfl⟩ : syracuseStep 2485583 = 3728375) B3728375
theorem B2485673 : Blo 1104625 2485673 := bstep (se 2 (by rfl) ⟨932127, by rfl⟩ : syracuseStep 2485673 = 1864255) B1864255
theorem B2486159 : Blo 1104625 2486159 := bstep (se 1 (by rfl) ⟨1864619, by rfl⟩ : syracuseStep 2486159 = 3729239) B3729239
theorem B7565501 : Blo 1104625 7565501 := bstep (se 3 (by rfl) ⟨1418531, by rfl⟩ : syracuseStep 7565501 = 2837063) B2837063
theorem B1864073 : Blo 1104625 1864073 := bstep (se 2 (by rfl) ⟨699027, by rfl⟩ : syracuseStep 1864073 = 1398055) B1398055
theorem B3732047 : Blo 1104625 3732047 := bstep (se 1 (by rfl) ⟨2799035, by rfl⟩ : syracuseStep 3732047 = 5598071) B5598071
theorem B2486879 : Blo 1104625 2486879 := bstep (se 1 (by rfl) ⟨1865159, by rfl⟩ : syracuseStep 2486879 = 3730319) B3730319
theorem B1995499 : Blo 1104625 1995499 := bstep (se 1 (by rfl) ⟨1496624, by rfl⟩ : syracuseStep 1995499 = 2993249) B2993249
theorem B1864505 : Blo 1104625 1864505 := bstep (se 2 (by rfl) ⟨699189, by rfl⟩ : syracuseStep 1864505 = 1398379) B1398379
theorem B1864559 : Blo 1104625 1864559 := bstep (se 1 (by rfl) ⟨1398419, by rfl⟩ : syracuseStep 1864559 = 2796839) B2796839
theorem B3732587 : Blo 1104625 3732587 := bstep (se 1 (by rfl) ⟨2799440, by rfl⟩ : syracuseStep 3732587 = 5598881) B5598881
theorem B2487707 : Blo 1104625 2487707 := bstep (se 1 (by rfl) ⟨1865780, by rfl⟩ : syracuseStep 2487707 = 3731561) B3731561
theorem B57407237 : Blo 1104625 57407237 := bstep (se 4 (by rfl) ⟨5381928, by rfl⟩ : syracuseStep 57407237 = 10763857) B10763857
theorem B16152335 : Blo 1104625 16152335 := bstep (se 1 (by rfl) ⟨12114251, by rfl⟩ : syracuseStep 16152335 = 24228503) B24228503
theorem B1865551 : Blo 1104625 1865551 := bstep (se 1 (by rfl) ⟨1399163, by rfl⟩ : syracuseStep 1865551 = 2798327) B2798327
theorem B7272337 : Blo 1104625 7272337 := bstep (se 2 (by rfl) ⟨2727126, by rfl⟩ : syracuseStep 7272337 = 5454253) B5454253
theorem B2488283 : Blo 1104625 2488283 := bstep (se 1 (by rfl) ⟨1866212, by rfl⟩ : syracuseStep 2488283 = 3732425) B3732425
theorem B60520441 : Blo 1104625 60520441 := bstep (se 2 (by rfl) ⟨22695165, by rfl⟩ : syracuseStep 60520441 = 45390331) B45390331
theorem B2488463 : Blo 1104625 2488463 := bstep (se 1 (by rfl) ⟨1866347, by rfl⟩ : syracuseStep 2488463 = 3732695) B3732695
theorem B1243291 : Blo 1104625 1243291 := bstep (se 1 (by rfl) ⟨932468, by rfl⟩ : syracuseStep 1243291 = 1864937) B1864937
theorem B2488481 : Blo 1104625 2488481 := bstep (se 2 (by rfl) ⟨933180, by rfl⟩ : syracuseStep 2488481 = 1866361) B1866361
theorem B1243327 : Blo 1104625 1243327 := bstep (se 1 (by rfl) ⟨932495, by rfl⟩ : syracuseStep 1243327 = 1864991) B1864991
theorem B2488553 : Blo 1104625 2488553 := bstep (se 2 (by rfl) ⟨933207, by rfl⟩ : syracuseStep 2488553 = 1866415) B1866415
theorem B1865963 : Blo 1104625 1865963 := bstep (se 1 (by rfl) ⟨1399472, by rfl⟩ : syracuseStep 1865963 = 2798945) B2798945
theorem B4258055 : Blo 1104625 4258055 := bstep (se 1 (by rfl) ⟨3193541, by rfl⟩ : syracuseStep 4258055 = 6387083) B6387083
theorem B11958637 : Blo 1104625 11958637 := bstep (se 3 (by rfl) ⟨2242244, by rfl⟩ : syracuseStep 11958637 = 4484489) B4484489
theorem B3733883 : Blo 1104625 3733883 := bstep (se 1 (by rfl) ⟨2800412, by rfl⟩ : syracuseStep 3733883 = 5600825) B5600825
theorem B3734153 : Blo 1104625 3734153 := bstep (se 2 (by rfl) ⟨1400307, by rfl⟩ : syracuseStep 3734153 = 2800615) B2800615
theorem B1866793 : Blo 1104625 1866793 := bstep (se 2 (by rfl) ⟨700047, by rfl⟩ : syracuseStep 1866793 = 1400095) B1400095
theorem B1866935 : Blo 1104625 1866935 := bstep (se 1 (by rfl) ⟨1400201, by rfl⟩ : syracuseStep 1866935 = 2800403) B2800403
theorem B2489831 : Blo 1104625 2489831 := bstep (se 1 (by rfl) ⟨1867373, by rfl⟩ : syracuseStep 2489831 = 3734747) B3734747
theorem B1867259 : Blo 1104625 1867259 := bstep (se 1 (by rfl) ⟨1400444, by rfl⟩ : syracuseStep 1867259 = 2800889) B2800889
theorem B3735287 : Blo 1104625 3735287 := bstep (se 1 (by rfl) ⟨2801465, by rfl⟩ : syracuseStep 3735287 = 5602931) B5602931
theorem B1867691 : Blo 1104625 1867691 := bstep (se 1 (by rfl) ⟨1400768, by rfl⟩ : syracuseStep 1867691 = 2801537) B2801537
theorem B1245487 : Blo 1104625 1245487 := bstep (se 1 (by rfl) ⟨934115, by rfl⟩ : syracuseStep 1245487 = 1868231) B1868231
theorem B4489519 : Blo 1104625 4489519 := bstep (se 1 (by rfl) ⟨3367139, by rfl⟩ : syracuseStep 4489519 = 6734279) B6734279
theorem B2654591 : Blo 1104625 2654591 := bstep (se 1 (by rfl) ⟨1990943, by rfl⟩ : syracuseStep 2654591 = 3981887) B3981887
theorem B3735935 : Blo 1104625 3735935 := bstep (se 1 (by rfl) ⟨2801951, by rfl⟩ : syracuseStep 3735935 = 5603903) B5603903
theorem B4260383 : Blo 1104625 4260383 := bstep (se 1 (by rfl) ⟨3195287, by rfl⟩ : syracuseStep 4260383 = 6390575) B6390575
theorem B2490911 : Blo 1104625 2490911 := bstep (se 1 (by rfl) ⟨1868183, by rfl⟩ : syracuseStep 2490911 = 3736367) B3736367
theorem B2490983 : Blo 1104625 2490983 := bstep (se 1 (by rfl) ⟨1868237, by rfl⟩ : syracuseStep 2490983 = 3736475) B3736475
theorem B3277417 : Blo 1104625 3277417 := bstep (se 2 (by rfl) ⟨1229031, by rfl⟩ : syracuseStep 3277417 = 2458063) B2458063
theorem B1868393 : Blo 1104625 1868393 := bstep (se 2 (by rfl) ⟨700647, by rfl⟩ : syracuseStep 1868393 = 1401295) B1401295
theorem B1180327 : Blo 1104625 1180327 := bstep (se 1 (by rfl) ⟨885245, by rfl⟩ : syracuseStep 1180327 = 1770491) B1770491
theorem B21267481 : Blo 1104625 21267481 := bstep (se 2 (by rfl) ⟨7975305, by rfl⟩ : syracuseStep 21267481 = 15950611) B15950611
theorem B6292637 : Blo 1104625 6292637 := bstep (se 3 (by rfl) ⟨1179869, by rfl⟩ : syracuseStep 6292637 = 2359739) B2359739
theorem B3736799 : Blo 1104625 3736799 := bstep (se 1 (by rfl) ⟨2802599, by rfl⟩ : syracuseStep 3736799 = 5605199) B5605199
theorem B2491739 : Blo 1104625 2491739 := bstep (se 1 (by rfl) ⟨1868804, by rfl⟩ : syracuseStep 2491739 = 3737609) B3737609
theorem B4719991 : Blo 1104625 4719991 := bstep (se 1 (by rfl) ⟨3539993, by rfl⟩ : syracuseStep 4719991 = 7079987) B7079987
theorem B4195759 : Blo 1104625 4195759 := bstep (se 1 (by rfl) ⟨3146819, by rfl⟩ : syracuseStep 4195759 = 6293639) B6293639
theorem B1246747 : Blo 1104625 1246747 := bstep (se 1 (by rfl) ⟨935060, by rfl⟩ : syracuseStep 1246747 = 1870121) B1870121
theorem B2492009 : Blo 1104625 2492009 := bstep (se 2 (by rfl) ⟨934503, by rfl⟩ : syracuseStep 2492009 = 1869007) B1869007
theorem B1869419 : Blo 1104625 1869419 := bstep (se 1 (by rfl) ⟨1402064, by rfl⟩ : syracuseStep 1869419 = 2804129) B2804129
theorem B1869689 : Blo 1104625 1869689 := bstep (se 2 (by rfl) ⟨701133, by rfl⟩ : syracuseStep 1869689 = 1402267) B1402267
theorem B2656351 : Blo 1104625 2656351 := bstep (se 1 (by rfl) ⟨1992263, by rfl⟩ : syracuseStep 2656351 = 3984527) B3984527
theorem B2492603 : Blo 1104625 2492603 := bstep (se 1 (by rfl) ⟨1869452, by rfl⟩ : syracuseStep 2492603 = 3738905) B3738905
theorem B7080139 : Blo 1104625 7080139 := bstep (se 1 (by rfl) ⟨5310104, by rfl⟩ : syracuseStep 7080139 = 10620209) B10620209
theorem B2492639 : Blo 1104625 2492639 := bstep (se 1 (by rfl) ⟨1869479, by rfl⟩ : syracuseStep 2492639 = 3738959) B3738959
theorem B1870249 : Blo 1104625 1870249 := bstep (se 2 (by rfl) ⟨701343, by rfl⟩ : syracuseStep 1870249 = 1402687) B1402687
theorem B5605847 : Blo 1104625 5605847 := bstep (se 1 (by rfl) ⟨4204385, by rfl⟩ : syracuseStep 5605847 = 8408771) B8408771
theorem B2493089 : Blo 1104625 2493089 := bstep (se 2 (by rfl) ⟨934908, by rfl⟩ : syracuseStep 2493089 = 1869817) B1869817
theorem B4197203 : Blo 1104625 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B2493305 : Blo 1104625 2493305 := bstep (se 2 (by rfl) ⟨934989, by rfl⟩ : syracuseStep 2493305 = 1869979) B1869979
theorem B3738527 : Blo 1104625 3738527 := bstep (se 1 (by rfl) ⟨2803895, by rfl⟩ : syracuseStep 3738527 = 5607791) B5607791
theorem B2493449 : Blo 1104625 2493449 := bstep (se 2 (by rfl) ⟨935043, by rfl⟩ : syracuseStep 2493449 = 1870087) B1870087
theorem B2493503 : Blo 1104625 2493503 := bstep (se 1 (by rfl) ⟨1870127, by rfl⟩ : syracuseStep 2493503 = 3740255) B3740255
theorem B4787387 : Blo 1104625 4787387 := bstep (se 1 (by rfl) ⟨3590540, by rfl⟩ : syracuseStep 4787387 = 7181081) B7181081
theorem B12127583 : Blo 1104625 12127583 := bstep (se 1 (by rfl) ⟨9095687, by rfl⟩ : syracuseStep 12127583 = 18191375) B18191375
theorem B6295097 : Blo 1104625 6295097 := bstep (se 2 (by rfl) ⟨2360661, by rfl⟩ : syracuseStep 6295097 = 4721323) B4721323
theorem B2101115 : Blo 1104625 2101115 := bstep (se 1 (by rfl) ⟨1575836, by rfl⟩ : syracuseStep 2101115 = 3151673) B3151673
theorem B2494331 : Blo 1104625 2494331 := bstep (se 1 (by rfl) ⟨1870748, by rfl⟩ : syracuseStep 2494331 = 3741497) B3741497
theorem B2658359 : Blo 1104625 2658359 := bstep (se 1 (by rfl) ⟨1993769, by rfl⟩ : syracuseStep 2658359 = 3987539) B3987539
theorem B1773623 : Blo 1104625 1773623 := bstep (se 1 (by rfl) ⟨1330217, by rfl⟩ : syracuseStep 1773623 = 2660435) B2660435
theorem B4198463 : Blo 1104625 4198463 := bstep (se 1 (by rfl) ⟨3148847, by rfl⟩ : syracuseStep 4198463 = 6297695) B6297695
theorem B2101403 : Blo 1104625 2101403 := bstep (se 1 (by rfl) ⟨1576052, by rfl⟩ : syracuseStep 2101403 = 3152105) B3152105
theorem B2101601 : Blo 1104625 2101601 := bstep (se 2 (by rfl) ⟨788100, by rfl⟩ : syracuseStep 2101601 = 1576201) B1576201
theorem B3740093 : Blo 1104625 3740093 := bstep (se 3 (by rfl) ⟨701267, by rfl⟩ : syracuseStep 3740093 = 1402535) B1402535
theorem B2397019 : Blo 1104625 2397019 := bstep (se 1 (by rfl) ⟨1797764, by rfl⟩ : syracuseStep 2397019 = 3595529) B3595529
theorem B20223053 : Blo 1104625 20223053 := bstep (se 3 (by rfl) ⟨3791822, by rfl⟩ : syracuseStep 20223053 = 7583645) B7583645
theorem B6296737 : Blo 1104625 6296737 := bstep (se 2 (by rfl) ⟨2361276, by rfl⟩ : syracuseStep 6296737 = 4722553) B4722553
theorem B4494791 : Blo 1104625 4494791 := bstep (se 1 (by rfl) ⟨3371093, by rfl⟩ : syracuseStep 4494791 = 6742187) B6742187
theorem B4200119 : Blo 1104625 4200119 := bstep (se 1 (by rfl) ⟨3150089, by rfl⟩ : syracuseStep 4200119 = 6300179) B6300179
theorem B4724639 : Blo 1104625 4724639 := bstep (se 1 (by rfl) ⟨3543479, by rfl⟩ : syracuseStep 4724639 = 7086959) B7086959
theorem B5609411 : Blo 1104625 5609411 := bstep (se 1 (by rfl) ⟨4207058, by rfl⟩ : syracuseStep 5609411 = 8414117) B8414117
theorem B2103583 : Blo 1104625 2103583 := bstep (se 1 (by rfl) ⟨1577687, by rfl⟩ : syracuseStep 2103583 = 3155375) B3155375
theorem B2693459 : Blo 1104625 2693459 := bstep (se 1 (by rfl) ⟨2020094, by rfl⟩ : syracuseStep 2693459 = 4040189) B4040189
theorem B2989487 : Blo 1104625 2989487 := bstep (se 1 (by rfl) ⟨2242115, by rfl⟩ : syracuseStep 2989487 = 4484231) B4484231
theorem B4726775 : Blo 1104625 4726775 := bstep (se 1 (by rfl) ⟨3545081, by rfl⟩ : syracuseStep 4726775 = 7090163) B7090163
theorem B16195945 : Blo 1104625 16195945 := bstep (se 2 (by rfl) ⟨6073479, by rfl⟩ : syracuseStep 16195945 = 12146959) B12146959
theorem B3154315 : Blo 1104625 3154315 := bstep (se 1 (by rfl) ⟨2365736, by rfl⟩ : syracuseStep 3154315 = 4731473) B4731473
theorem B14166839 : Blo 1104625 14166839 := bstep (se 1 (by rfl) ⟨10625129, by rfl⟩ : syracuseStep 14166839 = 21250259) B21250259
theorem B5844347 : Blo 1104625 5844347 := bstep (se 1 (by rfl) ⟨4383260, by rfl⟩ : syracuseStep 5844347 = 8766521) B8766521
theorem B9448933 : Blo 1104625 9448933 := bstep (se 4 (by rfl) ⟨885837, by rfl⟩ : syracuseStep 9448933 = 1771675) B1771675
theorem B8400509 : Blo 1104625 8400509 := bstep (se 3 (by rfl) ⟨1575095, by rfl⟩ : syracuseStep 8400509 = 3150191) B3150191
theorem B9449207 : Blo 1104625 9449207 := bstep (se 1 (by rfl) ⟨7086905, by rfl⟩ : syracuseStep 9449207 = 14173811) B14173811
theorem B2797375 : Blo 1104625 2797375 := bstep (se 1 (by rfl) ⟨2098031, by rfl⟩ : syracuseStep 2797375 = 4196063) B4196063
theorem B4730687 : Blo 1104625 4730687 := bstep (se 1 (by rfl) ⟨3548015, by rfl⟩ : syracuseStep 4730687 = 7096031) B7096031
theorem B2699227 : Blo 1104625 2699227 := bstep (se 1 (by rfl) ⟨2024420, by rfl⟩ : syracuseStep 2699227 = 4048841) B4048841
theorem B18886931 : Blo 1104625 18886931 := bstep (se 1 (by rfl) ⟨14165198, by rfl⟩ : syracuseStep 18886931 = 28330397) B28330397
theorem B2798023 : Blo 1104625 2798023 := bstep (se 1 (by rfl) ⟨2098517, by rfl⟩ : syracuseStep 2798023 = 4197035) B4197035
theorem B31928903 : Blo 1104625 31928903 := bstep (se 1 (by rfl) ⟨23946677, by rfl⟩ : syracuseStep 31928903 = 47893355) B47893355
theorem B4207211 : Blo 1104625 4207211 := bstep (se 1 (by rfl) ⟨3155408, by rfl⟩ : syracuseStep 4207211 = 6310817) B6310817
theorem B4207423 : Blo 1104625 4207423 := bstep (se 1 (by rfl) ⟨3155567, by rfl⟩ : syracuseStep 4207423 = 6311135) B6311135
theorem B5321639 : Blo 1104625 5321639 := bstep (se 1 (by rfl) ⟨3991229, by rfl⟩ : syracuseStep 5321639 = 7982459) B7982459
theorem B15938855 : Blo 1104625 15938855 := bstep (se 1 (by rfl) ⟨11954141, by rfl⟩ : syracuseStep 15938855 = 23908283) B23908283
theorem B11974031 : Blo 1104625 11974031 := bstep (se 1 (by rfl) ⟨8980523, by rfl⟩ : syracuseStep 11974031 = 17961047) B17961047
theorem B20166043 : Blo 1104625 20166043 := bstep (se 1 (by rfl) ⟨15124532, by rfl⟩ : syracuseStep 20166043 = 30249065) B30249065
theorem B12760685 : Blo 1104625 12760685 := bstep (se 3 (by rfl) ⟨2392628, by rfl⟩ : syracuseStep 12760685 = 4785257) B4785257
theorem B40449719 : Blo 1104625 40449719 := bstep (se 1 (by rfl) ⟨30337289, by rfl⟩ : syracuseStep 40449719 = 60674579) B60674579
theorem B5322793 : Blo 1104625 5322793 := bstep (se 2 (by rfl) ⟨1996047, by rfl⟩ : syracuseStep 5322793 = 3992095) B3992095
theorem B2799755 : Blo 1104625 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B7977151 : Blo 1104625 7977151 := bstep (se 1 (by rfl) ⟨5982863, by rfl⟩ : syracuseStep 7977151 = 11965727) B11965727
theorem B7092647 : Blo 1104625 7092647 := bstep (se 1 (by rfl) ⟨5319485, by rfl⟩ : syracuseStep 7092647 = 10638971) B10638971
theorem B2800271 : Blo 1104625 2800271 := bstep (se 1 (by rfl) ⟨2100203, by rfl⟩ : syracuseStep 2800271 = 4200407) B4200407
theorem B4864655 : Blo 1104625 4864655 := bstep (se 1 (by rfl) ⟨3648491, by rfl⟩ : syracuseStep 4864655 = 7296983) B7296983
theorem B2276027 : Blo 1104625 2276027 := bstep (se 1 (by rfl) ⟨1707020, by rfl⟩ : syracuseStep 2276027 = 3414041) B3414041
theorem B2800595 : Blo 1104625 2800595 := bstep (se 1 (by rfl) ⟨2100446, by rfl⟩ : syracuseStep 2800595 = 4200893) B4200893
theorem B8076995 : Blo 1104625 8076995 := bstep (se 1 (by rfl) ⟨6057746, by rfl⟩ : syracuseStep 8076995 = 12115493) B12115493
theorem B2801375 : Blo 1104625 2801375 := bstep (se 1 (by rfl) ⟨2101031, by rfl⟩ : syracuseStep 2801375 = 4202063) B4202063
theorem B1261423 : Blo 1104625 1261423 := bstep (se 1 (by rfl) ⟨946067, by rfl⟩ : syracuseStep 1261423 = 1892135) B1892135
theorem B8404883 : Blo 1104625 8404883 := bstep (se 1 (by rfl) ⟨6303662, by rfl⟩ : syracuseStep 8404883 = 12607325) B12607325
theorem B9454265 : Blo 1104625 9454265 := bstep (se 2 (by rfl) ⟨3545349, by rfl⟩ : syracuseStep 9454265 = 7090699) B7090699
theorem B11354813 : Blo 1104625 11354813 := bstep (se 3 (by rfl) ⟨2129027, by rfl⟩ : syracuseStep 11354813 = 4258055) B4258055
theorem B71877395 : Blo 1104625 71877395 := bstep (se 1 (by rfl) ⟨53908046, by rfl⟩ : syracuseStep 71877395 = 107816093) B107816093
theorem B2802863 : Blo 1104625 2802863 := bstep (se 1 (by rfl) ⟨2102147, by rfl⟩ : syracuseStep 2802863 = 4204295) B4204295
theorem B21546427 : Blo 1104625 21546427 := bstep (se 1 (by rfl) ⟨16159820, by rfl⟩ : syracuseStep 21546427 = 32319641) B32319641
theorem B1657055 : Blo 1104625 1657055 := bstep (se 1 (by rfl) ⟨1242791, by rfl⟩ : syracuseStep 1657055 = 2485583) B2485583
theorem B1657115 : Blo 1104625 1657115 := bstep (se 1 (by rfl) ⟨1242836, by rfl⟩ : syracuseStep 1657115 = 2485673) B2485673
theorem B9456041 : Blo 1104625 9456041 := bstep (se 2 (by rfl) ⟨3546015, by rfl⟩ : syracuseStep 9456041 = 7092031) B7092031
theorem B1657439 : Blo 1104625 1657439 := bstep (se 1 (by rfl) ⟨1243079, by rfl⟩ : syracuseStep 1657439 = 2486159) B2486159
theorem B14174837 : Blo 1104625 14174837 := bstep (se 5 (by rfl) ⟨664445, by rfl⟩ : syracuseStep 14174837 = 1328891) B1328891
theorem B80693921 : Blo 1104625 80693921 := bstep (se 2 (by rfl) ⟨30260220, by rfl⟩ : syracuseStep 80693921 = 60520441) B60520441
theorem B1657721 : Blo 1104625 1657721 := bstep (se 2 (by rfl) ⟨621645, by rfl⟩ : syracuseStep 1657721 = 1243291) B1243291
theorem B1657769 : Blo 1104625 1657769 := bstep (se 2 (by rfl) ⟨621663, by rfl⟩ : syracuseStep 1657769 = 1243327) B1243327
theorem B1657919 : Blo 1104625 1657919 := bstep (se 1 (by rfl) ⟨1243439, by rfl⟩ : syracuseStep 1657919 = 2486879) B2486879
theorem B15944849 : Blo 1104625 15944849 := bstep (se 2 (by rfl) ⟨5979318, by rfl⟩ : syracuseStep 15944849 = 11958637) B11958637
theorem B35933777 : Blo 1104625 35933777 := bstep (se 2 (by rfl) ⟨13475166, by rfl⟩ : syracuseStep 35933777 = 26950333) B26950333
theorem B1658471 : Blo 1104625 1658471 := bstep (se 1 (by rfl) ⟨1243853, by rfl⟩ : syracuseStep 1658471 = 2487707) B2487707
theorem B10768223 : Blo 1104625 10768223 := bstep (se 1 (by rfl) ⟨8076167, by rfl⟩ : syracuseStep 10768223 = 16152335) B16152335
theorem B1658855 : Blo 1104625 1658855 := bstep (se 1 (by rfl) ⟨1244141, by rfl⟩ : syracuseStep 1658855 = 2488283) B2488283
theorem B2805799 : Blo 1104625 2805799 := bstep (se 1 (by rfl) ⟨2104349, by rfl⟩ : syracuseStep 2805799 = 4208699) B4208699
theorem B3985463 : Blo 1104625 3985463 := bstep (se 1 (by rfl) ⟨2989097, by rfl⟩ : syracuseStep 3985463 = 5978195) B5978195
theorem B1658975 : Blo 1104625 1658975 := bstep (se 1 (by rfl) ⟨1244231, by rfl⟩ : syracuseStep 1658975 = 2488463) B2488463
theorem B1658987 : Blo 1104625 1658987 := bstep (se 1 (by rfl) ⟨1244240, by rfl⟩ : syracuseStep 1658987 = 2488481) B2488481
theorem B1659035 : Blo 1104625 1659035 := bstep (se 1 (by rfl) ⟨1244276, by rfl⟩ : syracuseStep 1659035 = 2488553) B2488553
theorem B6312593 : Blo 1104625 6312593 := bstep (se 2 (by rfl) ⟨2367222, by rfl⟩ : syracuseStep 6312593 = 4734445) B4734445
theorem B1659887 : Blo 1104625 1659887 := bstep (se 1 (by rfl) ⟨1244915, by rfl⟩ : syracuseStep 1659887 = 2489831) B2489831
theorem B1660271 : Blo 1104625 1660271 := bstep (se 1 (by rfl) ⟨1245203, by rfl⟩ : syracuseStep 1660271 = 2490407) B2490407
theorem B34133399 : Blo 1104625 34133399 := bstep (se 1 (by rfl) ⟨25600049, by rfl⟩ : syracuseStep 34133399 = 51200099) B51200099
theorem B1660391 : Blo 1104625 1660391 := bstep (se 1 (by rfl) ⟨1245293, by rfl⟩ : syracuseStep 1660391 = 2490587) B2490587
theorem B1660553 : Blo 1104625 1660553 := bstep (se 2 (by rfl) ⟨622707, by rfl⟩ : syracuseStep 1660553 = 1245415) B1245415
theorem B1660571 : Blo 1104625 1660571 := bstep (se 1 (by rfl) ⟨1245428, by rfl⟩ : syracuseStep 1660571 = 2490857) B2490857
theorem B1660763 : Blo 1104625 1660763 := bstep (se 1 (by rfl) ⟨1245572, by rfl⟩ : syracuseStep 1660763 = 2491145) B2491145
theorem B1661147 : Blo 1104625 1661147 := bstep (se 1 (by rfl) ⟨1245860, by rfl⟩ : syracuseStep 1661147 = 2491721) B2491721
theorem B20207879 : Blo 1104625 20207879 := bstep (se 1 (by rfl) ⟨15155909, by rfl⟩ : syracuseStep 20207879 = 30311819) B30311819
theorem B1661417 : Blo 1104625 1661417 := bstep (se 2 (by rfl) ⟨623031, by rfl⟩ : syracuseStep 1661417 = 1246063) B1246063
theorem B1104711 : Blo 1104625 1104711 := bstep (se 1 (by rfl) ⟨828533, by rfl⟩ : syracuseStep 1104711 = 1657067) B1657067
theorem B1104751 : Blo 1104625 1104751 := bstep (se 1 (by rfl) ⟨828563, by rfl⟩ : syracuseStep 1104751 = 1657127) B1657127
theorem B1661807 : Blo 1104625 1661807 := bstep (se 1 (by rfl) ⟨1246355, by rfl⟩ : syracuseStep 1661807 = 2492711) B2492711
theorem B1399675 : Blo 1104625 1399675 := bstep (se 1 (by rfl) ⟨1049756, by rfl⟩ : syracuseStep 1399675 = 2099513) B2099513
theorem B1661819 : Blo 1104625 1661819 := bstep (se 1 (by rfl) ⟨1246364, by rfl⟩ : syracuseStep 1661819 = 2492729) B2492729
theorem B1104807 : Blo 1104625 1104807 := bstep (se 1 (by rfl) ⟨828605, by rfl⟩ : syracuseStep 1104807 = 1657211) B1657211
theorem B1104987 : Blo 1104625 1104987 := bstep (se 1 (by rfl) ⟨828740, by rfl⟩ : syracuseStep 1104987 = 1657481) B1657481
theorem B1105103 : Blo 1104625 1105103 := bstep (se 1 (by rfl) ⟨828827, by rfl⟩ : syracuseStep 1105103 = 1657655) B1657655
theorem B1105127 : Blo 1104625 1105127 := bstep (se 1 (by rfl) ⟨828845, by rfl⟩ : syracuseStep 1105127 = 1657691) B1657691
theorem B1105223 : Blo 1104625 1105223 := bstep (se 1 (by rfl) ⟨828917, by rfl⟩ : syracuseStep 1105223 = 1657835) B1657835
theorem B1105359 : Blo 1104625 1105359 := bstep (se 1 (by rfl) ⟨829019, by rfl⟩ : syracuseStep 1105359 = 1658039) B1658039
theorem B13458919 : Blo 1104625 13458919 := bstep (se 1 (by rfl) ⟨10094189, by rfl⟩ : syracuseStep 13458919 = 20188379) B20188379
theorem B1105519 : Blo 1104625 1105519 := bstep (se 1 (by rfl) ⟨829139, by rfl⟩ : syracuseStep 1105519 = 1658279) B1658279
theorem B174677627 : Blo 1104625 174677627 := bstep (se 1 (by rfl) ⟨131008220, by rfl⟩ : syracuseStep 174677627 = 262016441) B262016441
theorem B1105575 : Blo 1104625 1105575 := bstep (se 1 (by rfl) ⟨829181, by rfl⟩ : syracuseStep 1105575 = 1658363) B1658363
theorem B1662683 : Blo 1104625 1662683 := bstep (se 1 (by rfl) ⟨1247012, by rfl⟩ : syracuseStep 1662683 = 2494025) B2494025
theorem B1105639 : Blo 1104625 1105639 := bstep (se 1 (by rfl) ⟨829229, by rfl⟩ : syracuseStep 1105639 = 1658459) B1658459
theorem B1105695 : Blo 1104625 1105695 := bstep (se 1 (by rfl) ⟨829271, by rfl⟩ : syracuseStep 1105695 = 1658543) B1658543
theorem B1105775 : Blo 1104625 1105775 := bstep (se 1 (by rfl) ⟨829331, by rfl⟩ : syracuseStep 1105775 = 1658663) B1658663
theorem B1105831 : Blo 1104625 1105831 := bstep (se 1 (by rfl) ⟨829373, by rfl⟩ : syracuseStep 1105831 = 1658747) B1658747
theorem B7987187 : Blo 1104625 7987187 := bstep (se 1 (by rfl) ⟨5990390, by rfl⟩ : syracuseStep 7987187 = 11980781) B11980781
theorem B1106111 : Blo 1104625 1106111 := bstep (se 1 (by rfl) ⟨829583, by rfl⟩ : syracuseStep 1106111 = 1659167) B1659167
theorem B1106127 : Blo 1104625 1106127 := bstep (se 1 (by rfl) ⟨829595, by rfl⟩ : syracuseStep 1106127 = 1659191) B1659191
theorem B1106175 : Blo 1104625 1106175 := bstep (se 1 (by rfl) ⟨829631, by rfl⟩ : syracuseStep 1106175 = 1659263) B1659263
theorem B1106223 : Blo 1104625 1106223 := bstep (se 1 (by rfl) ⟨829667, by rfl⟩ : syracuseStep 1106223 = 1659335) B1659335
theorem B1106459 : Blo 1104625 1106459 := bstep (se 1 (by rfl) ⟨829844, by rfl⟩ : syracuseStep 1106459 = 1659689) B1659689
theorem B1106463 : Blo 1104625 1106463 := bstep (se 1 (by rfl) ⟨829847, by rfl⟩ : syracuseStep 1106463 = 1659695) B1659695
theorem B1106543 : Blo 1104625 1106543 := bstep (se 1 (by rfl) ⟨829907, by rfl⟩ : syracuseStep 1106543 = 1659815) B1659815
theorem B1106599 : Blo 1104625 1106599 := bstep (se 1 (by rfl) ⟨829949, by rfl⟩ : syracuseStep 1106599 = 1659899) B1659899
theorem B1106639 : Blo 1104625 1106639 := bstep (se 1 (by rfl) ⟨829979, by rfl⟩ : syracuseStep 1106639 = 1659959) B1659959
theorem B1401563 : Blo 1104625 1401563 := bstep (se 1 (by rfl) ⟨1051172, by rfl⟩ : syracuseStep 1401563 = 2102345) B2102345
theorem B3728159 : Blo 1104625 3728159 := bstep (se 1 (by rfl) ⟨2796119, by rfl⟩ : syracuseStep 3728159 = 5592239) B5592239
theorem B1106719 : Blo 1104625 1106719 := bstep (se 1 (by rfl) ⟨830039, by rfl⟩ : syracuseStep 1106719 = 1660079) B1660079
theorem B1106991 : Blo 1104625 1106991 := bstep (se 1 (by rfl) ⟨830243, by rfl⟩ : syracuseStep 1106991 = 1660487) B1660487
theorem B1107055 : Blo 1104625 1107055 := bstep (se 1 (by rfl) ⟨830291, by rfl⟩ : syracuseStep 1107055 = 1660583) B1660583
theorem B1107111 : Blo 1104625 1107111 := bstep (se 1 (by rfl) ⟨830333, by rfl⟩ : syracuseStep 1107111 = 1660667) B1660667
theorem B1107135 : Blo 1104625 1107135 := bstep (se 1 (by rfl) ⟨830351, by rfl⟩ : syracuseStep 1107135 = 1660703) B1660703
theorem B1107167 : Blo 1104625 1107167 := bstep (se 1 (by rfl) ⟨830375, by rfl⟩ : syracuseStep 1107167 = 1660751) B1660751
theorem B10642661 : Blo 1104625 10642661 := bstep (se 4 (by rfl) ⟨997749, by rfl⟩ : syracuseStep 10642661 = 1995499) B1995499
theorem B9463013 : Blo 1104625 9463013 := bstep (se 4 (by rfl) ⟨887157, by rfl⟩ : syracuseStep 9463013 = 1774315) B1774315
theorem B1107247 : Blo 1104625 1107247 := bstep (se 1 (by rfl) ⟨830435, by rfl⟩ : syracuseStep 1107247 = 1660871) B1660871
theorem B8414603 : Blo 1104625 8414603 := bstep (se 1 (by rfl) ⟨6310952, by rfl⟩ : syracuseStep 8414603 = 12621905) B12621905
theorem B1107483 : Blo 1104625 1107483 := bstep (se 1 (by rfl) ⟨830612, by rfl⟩ : syracuseStep 1107483 = 1661225) B1661225
theorem B1107487 : Blo 1104625 1107487 := bstep (se 1 (by rfl) ⟨830615, by rfl⟩ : syracuseStep 1107487 = 1661231) B1661231
theorem B9463391 : Blo 1104625 9463391 := bstep (se 1 (by rfl) ⟨7097543, by rfl⟩ : syracuseStep 9463391 = 14195087) B14195087
theorem B1107647 : Blo 1104625 1107647 := bstep (se 1 (by rfl) ⟨830735, by rfl⟩ : syracuseStep 1107647 = 1661471) B1661471
theorem B3729131 : Blo 1104625 3729131 := bstep (se 1 (by rfl) ⟨2796848, by rfl⟩ : syracuseStep 3729131 = 5593697) B5593697
theorem B3368699 : Blo 1104625 3368699 := bstep (se 1 (by rfl) ⟨2526524, by rfl⟩ : syracuseStep 3368699 = 5053049) B5053049
theorem B1107903 : Blo 1104625 1107903 := bstep (se 1 (by rfl) ⟨830927, by rfl⟩ : syracuseStep 1107903 = 1661855) B1661855
theorem B1107935 : Blo 1104625 1107935 := bstep (se 1 (by rfl) ⟨830951, by rfl⟩ : syracuseStep 1107935 = 1661903) B1661903
theorem B1402859 : Blo 1104625 1402859 := bstep (se 1 (by rfl) ⟨1052144, by rfl⟩ : syracuseStep 1402859 = 2104289) B2104289
theorem B3729401 : Blo 1104625 3729401 := bstep (se 2 (by rfl) ⟨1398525, by rfl⟩ : syracuseStep 3729401 = 2797051) B2797051
theorem B1107995 : Blo 1104625 1107995 := bstep (se 1 (by rfl) ⟨830996, by rfl⟩ : syracuseStep 1107995 = 1661993) B1661993
theorem B1107999 : Blo 1104625 1107999 := bstep (se 1 (by rfl) ⟨830999, by rfl⟩ : syracuseStep 1107999 = 1661999) B1661999
theorem B1108015 : Blo 1104625 1108015 := bstep (se 1 (by rfl) ⟨831011, by rfl⟩ : syracuseStep 1108015 = 1662023) B1662023
theorem B1108191 : Blo 1104625 1108191 := bstep (se 1 (by rfl) ⟨831143, by rfl⟩ : syracuseStep 1108191 = 1662287) B1662287
theorem B3729671 : Blo 1104625 3729671 := bstep (se 1 (by rfl) ⟨2797253, by rfl⟩ : syracuseStep 3729671 = 5594507) B5594507
theorem B7563527 : Blo 1104625 7563527 := bstep (se 1 (by rfl) ⟨5672645, by rfl⟩ : syracuseStep 7563527 = 11345291) B11345291
theorem B1108251 : Blo 1104625 1108251 := bstep (se 1 (by rfl) ⟨831188, by rfl⟩ : syracuseStep 1108251 = 1662377) B1662377
theorem B1108351 : Blo 1104625 1108351 := bstep (se 1 (by rfl) ⟨831263, by rfl⟩ : syracuseStep 1108351 = 1662527) B1662527
theorem B14182937 : Blo 1104625 14182937 := bstep (se 2 (by rfl) ⟨5318601, by rfl⟩ : syracuseStep 14182937 = 10637203) B10637203
theorem B4254239 : Blo 1104625 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B1108527 : Blo 1104625 1108527 := bstep (se 1 (by rfl) ⟨831395, by rfl⟩ : syracuseStep 1108527 = 1662791) B1662791
theorem B1108583 : Blo 1104625 1108583 := bstep (se 1 (by rfl) ⟨831437, by rfl⟩ : syracuseStep 1108583 = 1662875) B1662875
theorem B43085267 : Blo 1104625 43085267 := bstep (se 1 (by rfl) ⟨32313950, by rfl⟩ : syracuseStep 43085267 = 64627901) B64627901
theorem B2485727 : Blo 1104625 2485727 := bstep (se 1 (by rfl) ⟨1864295, by rfl⟩ : syracuseStep 2485727 = 3728591) B3728591
theorem B2485943 : Blo 1104625 2485943 := bstep (se 1 (by rfl) ⟨1864457, by rfl⟩ : syracuseStep 2485943 = 3728915) B3728915
theorem B4321019 : Blo 1104625 4321019 := bstep (se 1 (by rfl) ⟨3240764, by rfl⟩ : syracuseStep 4321019 = 6481529) B6481529
theorem B4484945 : Blo 1104625 4484945 := bstep (se 2 (by rfl) ⟨1681854, by rfl⟩ : syracuseStep 4484945 = 3363709) B3363709
theorem B2486735 : Blo 1104625 2486735 := bstep (se 1 (by rfl) ⟨1865051, by rfl⟩ : syracuseStep 2486735 = 3730103) B3730103
theorem B1864775 : Blo 1104625 1864775 := bstep (se 1 (by rfl) ⟨1398581, by rfl⟩ : syracuseStep 1864775 = 2797163) B2797163
theorem B2487401 : Blo 1104625 2487401 := bstep (se 2 (by rfl) ⟨932775, by rfl⟩ : syracuseStep 2487401 = 1865551) B1865551
theorem B9860203 : Blo 1104625 9860203 := bstep (se 1 (by rfl) ⟨7395152, by rfl⟩ : syracuseStep 9860203 = 14790305) B14790305
theorem B9696449 : Blo 1104625 9696449 := bstep (se 2 (by rfl) ⟨3636168, by rfl⟩ : syracuseStep 9696449 = 7272337) B7272337
theorem B5043667 : Blo 1104625 5043667 := bstep (se 1 (by rfl) ⟨3782750, by rfl⟩ : syracuseStep 5043667 = 7565501) B7565501
theorem B1242715 : Blo 1104625 1242715 := bstep (se 1 (by rfl) ⟨932036, by rfl⟩ : syracuseStep 1242715 = 1864073) B1864073
theorem B2488031 : Blo 1104625 2488031 := bstep (se 1 (by rfl) ⟨1866023, by rfl⟩ : syracuseStep 2488031 = 3732047) B3732047
theorem B1243003 : Blo 1104625 1243003 := bstep (se 1 (by rfl) ⟨932252, by rfl⟩ : syracuseStep 1243003 = 1864505) B1864505
theorem B1243039 : Blo 1104625 1243039 := bstep (se 1 (by rfl) ⟨932279, by rfl⟩ : syracuseStep 1243039 = 1864559) B1864559
theorem B2488391 : Blo 1104625 2488391 := bstep (se 1 (by rfl) ⟨1866293, by rfl⟩ : syracuseStep 2488391 = 3732587) B3732587
theorem B38271491 : Blo 1104625 38271491 := bstep (se 1 (by rfl) ⟨28703618, by rfl⟩ : syracuseStep 38271491 = 57407237) B57407237
theorem B5044961 : Blo 1104625 5044961 := bstep (se 2 (by rfl) ⟨1891860, by rfl⟩ : syracuseStep 5044961 = 3783721) B3783721
theorem B2489057 : Blo 1104625 2489057 := bstep (se 2 (by rfl) ⟨933396, by rfl⟩ : syracuseStep 2489057 = 1866793) B1866793
theorem B1243975 : Blo 1104625 1243975 := bstep (se 1 (by rfl) ⟨932981, by rfl⟩ : syracuseStep 1243975 = 1865963) B1865963
theorem B6388561 : Blo 1104625 6388561 := bstep (se 2 (by rfl) ⟨2395710, by rfl⟩ : syracuseStep 6388561 = 4791421) B4791421
theorem B2489255 : Blo 1104625 2489255 := bstep (se 1 (by rfl) ⟨1866941, by rfl⟩ : syracuseStep 2489255 = 3733883) B3733883
theorem B2489435 : Blo 1104625 2489435 := bstep (se 1 (by rfl) ⟨1867076, by rfl⟩ : syracuseStep 2489435 = 3734153) B3734153
theorem B232815779 : Blo 1104625 232815779 := bstep (se 1 (by rfl) ⟨174611834, by rfl⟩ : syracuseStep 232815779 = 349223669) B349223669
theorem B2522335 : Blo 1104625 2522335 := bstep (se 1 (by rfl) ⟨1891751, by rfl⟩ : syracuseStep 2522335 = 3783503) B3783503
theorem B1244623 : Blo 1104625 1244623 := bstep (se 1 (by rfl) ⟨933467, by rfl⟩ : syracuseStep 1244623 = 1866935) B1866935
theorem B1244839 : Blo 1104625 1244839 := bstep (se 1 (by rfl) ⟨933629, by rfl⟩ : syracuseStep 1244839 = 1867259) B1867259
theorem B1867495 : Blo 1104625 1867495 := bstep (se 1 (by rfl) ⟨1400621, by rfl⟩ : syracuseStep 1867495 = 2801243) B2801243
theorem B1867529 : Blo 1104625 1867529 := bstep (se 2 (by rfl) ⟨700323, by rfl⟩ : syracuseStep 1867529 = 1400647) B1400647
theorem B17956637 : Blo 1104625 17956637 := bstep (se 3 (by rfl) ⟨3366869, by rfl⟩ : syracuseStep 17956637 = 6733739) B6733739
theorem B2490191 : Blo 1104625 2490191 := bstep (se 1 (by rfl) ⟨1867643, by rfl⟩ : syracuseStep 2490191 = 3735287) B3735287
theorem B23887781 : Blo 1104625 23887781 := bstep (se 4 (by rfl) ⟨2239479, by rfl⟩ : syracuseStep 23887781 = 4478959) B4478959
theorem B1245127 : Blo 1104625 1245127 := bstep (se 1 (by rfl) ⟨933845, by rfl⟩ : syracuseStep 1245127 = 1867691) B1867691
theorem B2490623 : Blo 1104625 2490623 := bstep (se 1 (by rfl) ⟨1867967, by rfl⟩ : syracuseStep 2490623 = 3735935) B3735935
theorem B1245595 : Blo 1104625 1245595 := bstep (se 1 (by rfl) ⟨934196, by rfl⟩ : syracuseStep 1245595 = 1868393) B1868393
theorem B5603741 : Blo 1104625 5603741 := bstep (se 3 (by rfl) ⟨1050701, by rfl⟩ : syracuseStep 5603741 = 2101403) B2101403
theorem B7569875 : Blo 1104625 7569875 := bstep (se 1 (by rfl) ⟨5677406, by rfl⟩ : syracuseStep 7569875 = 11354813) B11354813
theorem B21594593 : Blo 1104625 21594593 := bstep (se 2 (by rfl) ⟨8097972, by rfl⟩ : syracuseStep 21594593 = 16195945) B16195945
theorem B4195091 : Blo 1104625 4195091 := bstep (se 1 (by rfl) ⟨3146318, by rfl⟩ : syracuseStep 4195091 = 6292637) B6292637
theorem B1868575 : Blo 1104625 1868575 := bstep (se 1 (by rfl) ⟨1401431, by rfl⟩ : syracuseStep 1868575 = 2802863) B2802863
theorem B2491199 : Blo 1104625 2491199 := bstep (se 1 (by rfl) ⟨1868399, by rfl⟩ : syracuseStep 2491199 = 3736799) B3736799
theorem B1573769 : Blo 1104625 1573769 := bstep (se 2 (by rfl) ⟨590163, by rfl⟩ : syracuseStep 1573769 = 1180327) B1180327
theorem B7078909 : Blo 1104625 7078909 := bstep (se 3 (by rfl) ⟨1327295, by rfl⟩ : syracuseStep 7078909 = 2654591) B2654591
theorem B1246279 : Blo 1104625 1246279 := bstep (se 1 (by rfl) ⟨934709, by rfl⟩ : syracuseStep 1246279 = 1869419) B1869419
theorem B1246459 : Blo 1104625 1246459 := bstep (se 1 (by rfl) ⟨934844, by rfl⟩ : syracuseStep 1246459 = 1869689) B1869689
theorem B3737231 : Blo 1104625 3737231 := bstep (se 1 (by rfl) ⟨2802923, by rfl⟩ : syracuseStep 3737231 = 5605847) B5605847
theorem B6293321 : Blo 1104625 6293321 := bstep (se 2 (by rfl) ⟨2359995, by rfl⟩ : syracuseStep 6293321 = 4719991) B4719991
theorem B3737501 : Blo 1104625 3737501 := bstep (se 3 (by rfl) ⟨700781, by rfl⟩ : syracuseStep 3737501 = 1401563) B1401563
theorem B2492351 : Blo 1104625 2492351 := bstep (se 1 (by rfl) ⟨1869263, by rfl⟩ : syracuseStep 2492351 = 3738527) B3738527
theorem B4196731 : Blo 1104625 4196731 := bstep (se 1 (by rfl) ⟨3147548, by rfl⟩ : syracuseStep 4196731 = 6295097) B6295097
theorem B23955851 : Blo 1104625 23955851 := bstep (se 1 (by rfl) ⟨17966888, by rfl⟩ : syracuseStep 23955851 = 35933777) B35933777
theorem B7178815 : Blo 1104625 7178815 := bstep (se 1 (by rfl) ⟨5384111, by rfl⟩ : syracuseStep 7178815 = 10768223) B10768223
theorem B2656975 : Blo 1104625 2656975 := bstep (se 1 (by rfl) ⟨1992731, by rfl⟩ : syracuseStep 2656975 = 3985463) B3985463
theorem B3541801 : Blo 1104625 3541801 := bstep (se 2 (by rfl) ⟨1328175, by rfl⟩ : syracuseStep 3541801 = 2656351) B2656351
theorem B9440185 : Blo 1104625 9440185 := bstep (se 2 (by rfl) ⟨3540069, by rfl⟩ : syracuseStep 9440185 = 7080139) B7080139
theorem B2493395 : Blo 1104625 2493395 := bstep (se 1 (by rfl) ⟨1870046, by rfl⟩ : syracuseStep 2493395 = 3740093) B3740093
theorem B25857197 : Blo 1104625 25857197 := bstep (se 3 (by rfl) ⟨4848224, by rfl⟩ : syracuseStep 25857197 = 9696449) B9696449
theorem B2493665 : Blo 1104625 2493665 := bstep (se 2 (by rfl) ⟨935124, by rfl⟩ : syracuseStep 2493665 = 1870249) B1870249
theorem B3149759 : Blo 1104625 3149759 := bstep (se 1 (by rfl) ⟨2362319, by rfl⟩ : syracuseStep 3149759 = 4724639) B4724639
theorem B3739607 : Blo 1104625 3739607 := bstep (se 1 (by rfl) ⟨2804705, by rfl⟩ : syracuseStep 3739607 = 5609411) B5609411
theorem B13471919 : Blo 1104625 13471919 := bstep (se 1 (by rfl) ⟨10103939, by rfl⟩ : syracuseStep 13471919 = 20207879) B20207879
theorem B3740957 : Blo 1104625 3740957 := bstep (se 3 (by rfl) ⟨701429, by rfl⟩ : syracuseStep 3740957 = 1402859) B1402859
theorem B3151183 : Blo 1104625 3151183 := bstep (se 1 (by rfl) ⟨2363387, by rfl⟩ : syracuseStep 3151183 = 4726775) B4726775
theorem B3741065 : Blo 1104625 3741065 := bstep (se 2 (by rfl) ⟨1402899, by rfl⟩ : syracuseStep 3741065 = 2805799) B2805799
theorem B7182557 : Blo 1104625 7182557 := bstep (se 3 (by rfl) ⟨1346729, by rfl⟩ : syracuseStep 7182557 = 2693459) B2693459
theorem B5609735 : Blo 1104625 5609735 := bstep (se 1 (by rfl) ⟨4207301, by rfl⟩ : syracuseStep 5609735 = 8414603) B8414603
theorem B5609897 : Blo 1104625 5609897 := bstep (se 2 (by rfl) ⟨2103711, by rfl⟩ : syracuseStep 5609897 = 4207423) B4207423
theorem B11344637 : Blo 1104625 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B13146937 : Blo 1104625 13146937 := bstep (se 2 (by rfl) ⟨4930101, by rfl⟩ : syracuseStep 13146937 = 9860203) B9860203
theorem B8395649 : Blo 1104625 8395649 := bstep (se 2 (by rfl) ⟨3148368, by rfl⟩ : syracuseStep 8395649 = 6296737) B6296737
theorem B9444559 : Blo 1104625 9444559 := bstep (se 1 (by rfl) ⟨7083419, by rfl⟩ : syracuseStep 9444559 = 14166839) B14166839
theorem B6724889 : Blo 1104625 6724889 := bstep (se 2 (by rfl) ⟨2521833, by rfl⟩ : syracuseStep 6724889 = 5043667) B5043667
theorem B6299471 : Blo 1104625 6299471 := bstep (se 1 (by rfl) ⟨4724603, by rfl⟩ : syracuseStep 6299471 = 9449207) B9449207
theorem B3153791 : Blo 1104625 3153791 := bstep (se 1 (by rfl) ⟨2365343, by rfl⟩ : syracuseStep 3153791 = 4730687) B4730687
theorem B2989963 : Blo 1104625 2989963 := bstep (se 1 (by rfl) ⟨2242472, by rfl⟩ : syracuseStep 2989963 = 4484945) B4484945
theorem B12591287 : Blo 1104625 12591287 := bstep (se 1 (by rfl) ⟨9443465, by rfl⟩ : syracuseStep 12591287 = 18886931) B18886931
theorem B3547759 : Blo 1104625 3547759 := bstep (se 1 (by rfl) ⟨2660819, by rfl⟩ : syracuseStep 3547759 = 5321639) B5321639
theorem B10625903 : Blo 1104625 10625903 := bstep (se 1 (by rfl) ⟨7969427, by rfl⟩ : syracuseStep 10625903 = 15938855) B15938855
theorem B7971965 : Blo 1104625 7971965 := bstep (se 3 (by rfl) ⟨1494743, by rfl⟩ : syracuseStep 7971965 = 2989487) B2989487
theorem B4728431 : Blo 1104625 4728431 := bstep (se 1 (by rfl) ⟨3546323, by rfl⟩ : syracuseStep 4728431 = 7092647) B7092647
theorem B1517351 : Blo 1104625 1517351 := bstep (se 1 (by rfl) ⟨1138013, by rfl⟩ : syracuseStep 1517351 = 2276027) B2276027
theorem B6727589 : Blo 1104625 6727589 := bstep (se 4 (by rfl) ⟨630711, by rfl⟩ : syracuseStep 6727589 = 1261423) B1261423
theorem B5384663 : Blo 1104625 5384663 := bstep (se 1 (by rfl) ⟨4038497, by rfl⟩ : syracuseStep 5384663 = 8076995) B8076995
theorem B14395877 : Blo 1104625 14395877 := bstep (se 4 (by rfl) ⟨1349613, by rfl⟩ : syracuseStep 14395877 = 2699227) B2699227
theorem B11971091 : Blo 1104625 11971091 := bstep (se 1 (by rfl) ⟨8978318, by rfl⟩ : syracuseStep 11971091 = 17956637) B17956637
theorem B7088957 : Blo 1104625 7088957 := bstep (se 3 (by rfl) ⟨1329179, by rfl⟩ : syracuseStep 7088957 = 2658359) B2658359
theorem B4729661 : Blo 1104625 4729661 := bstep (se 3 (by rfl) ⟨886811, by rfl⟩ : syracuseStep 4729661 = 1773623) B1773623
theorem B6302843 : Blo 1104625 6302843 := bstep (se 1 (by rfl) ⟨4727132, by rfl⟩ : syracuseStep 6302843 = 9454265) B9454265
theorem B47918263 : Blo 1104625 47918263 := bstep (se 1 (by rfl) ⟨35938697, by rfl⟩ : syracuseStep 47918263 = 71877395) B71877395
theorem B4205753 : Blo 1104625 4205753 := bstep (se 2 (by rfl) ⟨1577157, by rfl⟩ : syracuseStep 4205753 = 3154315) B3154315
theorem B4369889 : Blo 1104625 4369889 := bstep (se 2 (by rfl) ⟨1638708, by rfl⟩ : syracuseStep 4369889 = 3277417) B3277417
theorem B28356641 : Blo 1104625 28356641 := bstep (se 2 (by rfl) ⟨10633740, by rfl⟩ : syracuseStep 28356641 = 21267481) B21267481
theorem B6304027 : Blo 1104625 6304027 := bstep (se 1 (by rfl) ⟨4728020, by rfl⟩ : syracuseStep 6304027 = 9456041) B9456041
theorem B9449891 : Blo 1104625 9449891 := bstep (se 1 (by rfl) ⟨7087418, by rfl⟩ : syracuseStep 9449891 = 14174837) B14174837
theorem B2798135 : Blo 1104625 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B10629899 : Blo 1104625 10629899 := bstep (se 1 (by rfl) ⟨7972424, by rfl⟩ : syracuseStep 10629899 = 15944849) B15944849
theorem B3191591 : Blo 1104625 3191591 := bstep (se 1 (by rfl) ⟨2393693, by rfl⟩ : syracuseStep 3191591 = 4787387) B4787387
theorem B2798975 : Blo 1104625 2798975 := bstep (se 1 (by rfl) ⟨2099231, by rfl⟩ : syracuseStep 2798975 = 4198463) B4198463
theorem B4208395 : Blo 1104625 4208395 := bstep (se 1 (by rfl) ⟨3156296, by rfl⟩ : syracuseStep 4208395 = 6312593) B6312593
theorem B13482035 : Blo 1104625 13482035 := bstep (se 1 (by rfl) ⟨10111526, by rfl⟩ : syracuseStep 13482035 = 20223053) B20223053
theorem B22755599 : Blo 1104625 22755599 := bstep (se 1 (by rfl) ⟨17066699, by rfl⟩ : syracuseStep 22755599 = 34133399) B34133399
theorem B2996527 : Blo 1104625 2996527 := bstep (se 1 (by rfl) ⟨2247395, by rfl⟩ : syracuseStep 2996527 = 4494791) B4494791
theorem B2800079 : Blo 1104625 2800079 := bstep (se 1 (by rfl) ⟨2100059, by rfl⟩ : syracuseStep 2800079 = 4200119) B4200119
theorem B62339701 : Blo 1104625 62339701 := bstep (se 5 (by rfl) ⟨2922173, by rfl⟩ : syracuseStep 62339701 = 5844347) B5844347
theorem B12598577 : Blo 1104625 12598577 := bstep (se 2 (by rfl) ⟨4724466, by rfl⟩ : syracuseStep 12598577 = 9448933) B9448933
theorem B5324791 : Blo 1104625 5324791 := bstep (se 1 (by rfl) ⟨3993593, by rfl⟩ : syracuseStep 5324791 = 7987187) B7987187
theorem B7095107 : Blo 1104625 7095107 := bstep (se 1 (by rfl) ⟨5321330, by rfl⟩ : syracuseStep 7095107 = 10642661) B10642661
theorem B6308675 : Blo 1104625 6308675 := bstep (se 1 (by rfl) ⟨4731506, by rfl⟩ : syracuseStep 6308675 = 9463013) B9463013
theorem B6308927 : Blo 1104625 6308927 := bstep (se 1 (by rfl) ⟨4731695, by rfl⟩ : syracuseStep 6308927 = 9463391) B9463391
theorem B3196025 : Blo 1104625 3196025 := bstep (se 2 (by rfl) ⟨1198509, by rfl⟩ : syracuseStep 3196025 = 2397019) B2397019
theorem B2245799 : Blo 1104625 2245799 := bstep (se 1 (by rfl) ⟨1684349, by rfl⟩ : syracuseStep 2245799 = 3368699) B3368699
theorem B9455291 : Blo 1104625 9455291 := bstep (se 1 (by rfl) ⟨7091468, by rfl⟩ : syracuseStep 9455291 = 14182937) B14182937
theorem B26888057 : Blo 1104625 26888057 := bstep (se 2 (by rfl) ⟨10083021, by rfl⟩ : syracuseStep 26888057 = 20166043) B20166043
theorem B13453229 : Blo 1104625 13453229 := bstep (se 3 (by rfl) ⟨2522480, by rfl⟩ : syracuseStep 13453229 = 5044961) B5044961
theorem B1656953 : Blo 1104625 1656953 := bstep (se 2 (by rfl) ⟨621357, by rfl⟩ : syracuseStep 1656953 = 1242715) B1242715
theorem B28723511 : Blo 1104625 28723511 := bstep (se 1 (by rfl) ⟨21542633, by rfl⟩ : syracuseStep 28723511 = 43085267) B43085267
theorem B1657151 : Blo 1104625 1657151 := bstep (se 1 (by rfl) ⟨1242863, by rfl⟩ : syracuseStep 1657151 = 2485727) B2485727
theorem B1657295 : Blo 1104625 1657295 := bstep (se 1 (by rfl) ⟨1242971, by rfl⟩ : syracuseStep 1657295 = 2485943) B2485943
theorem B1657337 : Blo 1104625 1657337 := bstep (se 2 (by rfl) ⟨621501, by rfl⟩ : syracuseStep 1657337 = 1243003) B1243003
theorem B1657385 : Blo 1104625 1657385 := bstep (se 2 (by rfl) ⟨621519, by rfl⟩ : syracuseStep 1657385 = 1243039) B1243039
theorem B7097057 : Blo 1104625 7097057 := bstep (se 2 (by rfl) ⟨2661396, by rfl⟩ : syracuseStep 7097057 = 5322793) B5322793
theorem B10636201 : Blo 1104625 10636201 := bstep (se 2 (by rfl) ⟨3988575, by rfl⟩ : syracuseStep 10636201 = 7977151) B7977151
theorem B1657823 : Blo 1104625 1657823 := bstep (se 1 (by rfl) ⟨1243367, by rfl⟩ : syracuseStep 1657823 = 2486735) B2486735
theorem B2804777 : Blo 1104625 2804777 := bstep (se 2 (by rfl) ⟨1051791, by rfl⟩ : syracuseStep 2804777 = 2103583) B2103583
theorem B21285935 : Blo 1104625 21285935 := bstep (se 1 (by rfl) ⟨15964451, by rfl⟩ : syracuseStep 21285935 = 31928903) B31928903
theorem B2804807 : Blo 1104625 2804807 := bstep (se 1 (by rfl) ⟨2103605, by rfl⟩ : syracuseStep 2804807 = 4207211) B4207211
theorem B1658267 : Blo 1104625 1658267 := bstep (se 1 (by rfl) ⟨1243700, by rfl⟩ : syracuseStep 1658267 = 2487401) B2487401
theorem B7982687 : Blo 1104625 7982687 := bstep (se 1 (by rfl) ⟨5987015, by rfl⟩ : syracuseStep 7982687 = 11974031) B11974031
theorem B8507123 : Blo 1104625 8507123 := bstep (se 1 (by rfl) ⟨6380342, by rfl⟩ : syracuseStep 8507123 = 12760685) B12760685
theorem B1658633 : Blo 1104625 1658633 := bstep (se 2 (by rfl) ⟨621987, by rfl⟩ : syracuseStep 1658633 = 1243975) B1243975
theorem B1658687 : Blo 1104625 1658687 := bstep (se 1 (by rfl) ⟨1244015, by rfl⟩ : syracuseStep 1658687 = 2488031) B2488031
theorem B1658927 : Blo 1104625 1658927 := bstep (se 1 (by rfl) ⟨1244195, by rfl⟩ : syracuseStep 1658927 = 2488391) B2488391
theorem B3363113 : Blo 1104625 3363113 := bstep (se 2 (by rfl) ⟨1261167, by rfl⟩ : syracuseStep 3363113 = 2522335) B2522335
theorem B25514327 : Blo 1104625 25514327 := bstep (se 1 (by rfl) ⟨19135745, by rfl⟩ : syracuseStep 25514327 = 38271491) B38271491
theorem B1659371 : Blo 1104625 1659371 := bstep (se 1 (by rfl) ⟨1244528, by rfl⟩ : syracuseStep 1659371 = 2489057) B2489057
theorem B1659497 : Blo 1104625 1659497 := bstep (se 2 (by rfl) ⟨622311, by rfl⟩ : syracuseStep 1659497 = 1244623) B1244623
theorem B1659503 : Blo 1104625 1659503 := bstep (se 1 (by rfl) ⟨1244627, by rfl⟩ : syracuseStep 1659503 = 2489255) B2489255
theorem B17945225 : Blo 1104625 17945225 := bstep (se 2 (by rfl) ⟨6729459, by rfl⟩ : syracuseStep 17945225 = 13458919) B13458919
theorem B1659623 : Blo 1104625 1659623 := bstep (se 1 (by rfl) ⟨1244717, by rfl⟩ : syracuseStep 1659623 = 2489435) B2489435
theorem B155210519 : Blo 1104625 155210519 := bstep (se 1 (by rfl) ⟨116407889, by rfl⟩ : syracuseStep 155210519 = 232815779) B232815779
theorem B1659785 : Blo 1104625 1659785 := bstep (se 2 (by rfl) ⟨622419, by rfl⟩ : syracuseStep 1659785 = 1244839) B1244839
theorem B1660127 : Blo 1104625 1660127 := bstep (se 1 (by rfl) ⟨1245095, by rfl⟩ : syracuseStep 1660127 = 2490191) B2490191
theorem B1660169 : Blo 1104625 1660169 := bstep (se 2 (by rfl) ⟨622563, by rfl⟩ : syracuseStep 1660169 = 1245127) B1245127
theorem B2840255 : Blo 1104625 2840255 := bstep (se 1 (by rfl) ⟨2130191, by rfl⟩ : syracuseStep 2840255 = 4260383) B4260383
theorem B1660607 : Blo 1104625 1660607 := bstep (se 1 (by rfl) ⟨1245455, by rfl⟩ : syracuseStep 1660607 = 2490911) B2490911
theorem B1660649 : Blo 1104625 1660649 := bstep (se 2 (by rfl) ⟨622743, by rfl⟩ : syracuseStep 1660649 = 1245487) B1245487
theorem B5986025 : Blo 1104625 5986025 := bstep (se 2 (by rfl) ⟨2244759, by rfl⟩ : syracuseStep 5986025 = 4489519) B4489519
theorem B1660655 : Blo 1104625 1660655 := bstep (se 1 (by rfl) ⟨1245491, by rfl⟩ : syracuseStep 1660655 = 2490983) B2490983
theorem B1661159 : Blo 1104625 1661159 := bstep (se 1 (by rfl) ⟨1245869, by rfl⟩ : syracuseStep 1661159 = 2491739) B2491739
theorem B1661339 : Blo 1104625 1661339 := bstep (se 1 (by rfl) ⟨1246004, by rfl⟩ : syracuseStep 1661339 = 2492009) B2492009
theorem B1661735 : Blo 1104625 1661735 := bstep (se 1 (by rfl) ⟨1246301, by rfl⟩ : syracuseStep 1661735 = 2492603) B2492603
theorem B1104703 : Blo 1104625 1104703 := bstep (se 1 (by rfl) ⟨828527, by rfl⟩ : syracuseStep 1104703 = 1657055) B1657055
theorem B1661759 : Blo 1104625 1661759 := bstep (se 1 (by rfl) ⟨1246319, by rfl⟩ : syracuseStep 1661759 = 2492639) B2492639
theorem B1104743 : Blo 1104625 1104743 := bstep (se 1 (by rfl) ⟨828557, by rfl⟩ : syracuseStep 1104743 = 1657115) B1657115
theorem B1104959 : Blo 1104625 1104959 := bstep (se 1 (by rfl) ⟨828719, by rfl⟩ : syracuseStep 1104959 = 1657439) B1657439
theorem B53795947 : Blo 1104625 53795947 := bstep (se 1 (by rfl) ⟨40346960, by rfl⟩ : syracuseStep 53795947 = 80693921) B80693921
theorem B1662059 : Blo 1104625 1662059 := bstep (se 1 (by rfl) ⟨1246544, by rfl⟩ : syracuseStep 1662059 = 2493089) B2493089
theorem B5594345 : Blo 1104625 5594345 := bstep (se 2 (by rfl) ⟨2097879, by rfl⟩ : syracuseStep 5594345 = 4195759) B4195759
theorem B28728569 : Blo 1104625 28728569 := bstep (se 2 (by rfl) ⟨10773213, by rfl⟩ : syracuseStep 28728569 = 21546427) B21546427
theorem B1105147 : Blo 1104625 1105147 := bstep (se 1 (by rfl) ⟨828860, by rfl⟩ : syracuseStep 1105147 = 1657721) B1657721
theorem B1662203 : Blo 1104625 1662203 := bstep (se 1 (by rfl) ⟨1246652, by rfl⟩ : syracuseStep 1662203 = 2493305) B2493305
theorem B1105179 : Blo 1104625 1105179 := bstep (se 1 (by rfl) ⟨828884, by rfl⟩ : syracuseStep 1105179 = 1657769) B1657769
theorem B1662299 : Blo 1104625 1662299 := bstep (se 1 (by rfl) ⟨1246724, by rfl⟩ : syracuseStep 1662299 = 2493449) B2493449
theorem B1662329 : Blo 1104625 1662329 := bstep (se 2 (by rfl) ⟨623373, by rfl⟩ : syracuseStep 1662329 = 1246747) B1246747
theorem B1105279 : Blo 1104625 1105279 := bstep (se 1 (by rfl) ⟨828959, by rfl⟩ : syracuseStep 1105279 = 1657919) B1657919
theorem B1662335 : Blo 1104625 1662335 := bstep (se 1 (by rfl) ⟨1246751, by rfl⟩ : syracuseStep 1662335 = 2493503) B2493503
theorem B8085055 : Blo 1104625 8085055 := bstep (se 1 (by rfl) ⟨6063791, by rfl⟩ : syracuseStep 8085055 = 12127583) B12127583
theorem B1105647 : Blo 1104625 1105647 := bstep (se 1 (by rfl) ⟨829235, by rfl⟩ : syracuseStep 1105647 = 1658471) B1658471
theorem B1400743 : Blo 1104625 1400743 := bstep (se 1 (by rfl) ⟨1050557, by rfl⟩ : syracuseStep 1400743 = 2101115) B2101115
theorem B1662887 : Blo 1104625 1662887 := bstep (se 1 (by rfl) ⟨1247165, by rfl⟩ : syracuseStep 1662887 = 2494331) B2494331
theorem B1105903 : Blo 1104625 1105903 := bstep (se 1 (by rfl) ⟨829427, by rfl⟩ : syracuseStep 1105903 = 1658855) B1658855
theorem B1105983 : Blo 1104625 1105983 := bstep (se 1 (by rfl) ⟨829487, by rfl⟩ : syracuseStep 1105983 = 1658975) B1658975
theorem B1105991 : Blo 1104625 1105991 := bstep (se 1 (by rfl) ⟨829493, by rfl⟩ : syracuseStep 1105991 = 1658987) B1658987
theorem B1106023 : Blo 1104625 1106023 := bstep (se 1 (by rfl) ⟨829517, by rfl⟩ : syracuseStep 1106023 = 1659035) B1659035
theorem B1401067 : Blo 1104625 1401067 := bstep (se 1 (by rfl) ⟨1050800, by rfl⟩ : syracuseStep 1401067 = 2101601) B2101601
theorem B1106591 : Blo 1104625 1106591 := bstep (se 1 (by rfl) ⟨829943, by rfl⟩ : syracuseStep 1106591 = 1659887) B1659887
theorem B1106847 : Blo 1104625 1106847 := bstep (se 1 (by rfl) ⟨830135, by rfl⟩ : syracuseStep 1106847 = 1660271) B1660271
theorem B1106927 : Blo 1104625 1106927 := bstep (se 1 (by rfl) ⟨830195, by rfl⟩ : syracuseStep 1106927 = 1660391) B1660391
theorem B1107035 : Blo 1104625 1107035 := bstep (se 1 (by rfl) ⟨830276, by rfl⟩ : syracuseStep 1107035 = 1660553) B1660553
theorem B1107047 : Blo 1104625 1107047 := bstep (se 1 (by rfl) ⟨830285, by rfl⟩ : syracuseStep 1107047 = 1660571) B1660571
theorem B1107175 : Blo 1104625 1107175 := bstep (se 1 (by rfl) ⟨830381, by rfl⟩ : syracuseStep 1107175 = 1660763) B1660763
theorem B1107431 : Blo 1104625 1107431 := bstep (se 1 (by rfl) ⟨830573, by rfl⟩ : syracuseStep 1107431 = 1661147) B1661147
theorem B1107611 : Blo 1104625 1107611 := bstep (se 1 (by rfl) ⟨830708, by rfl⟩ : syracuseStep 1107611 = 1661417) B1661417
theorem B107865917 : Blo 1104625 107865917 := bstep (se 3 (by rfl) ⟨20224859, by rfl⟩ : syracuseStep 107865917 = 40449719) B40449719
theorem B1107871 : Blo 1104625 1107871 := bstep (se 1 (by rfl) ⟨830903, by rfl⟩ : syracuseStep 1107871 = 1661807) B1661807
theorem B1107879 : Blo 1104625 1107879 := bstep (se 1 (by rfl) ⟨830909, by rfl⟩ : syracuseStep 1107879 = 1661819) B1661819
theorem B116451751 : Blo 1104625 116451751 := bstep (se 1 (by rfl) ⟨87338813, by rfl⟩ : syracuseStep 116451751 = 174677627) B174677627
theorem B3729833 : Blo 1104625 3729833 := bstep (se 2 (by rfl) ⟨1398687, by rfl⟩ : syracuseStep 3729833 = 2797375) B2797375
theorem B1108455 : Blo 1104625 1108455 := bstep (se 1 (by rfl) ⟨831341, by rfl⟩ : syracuseStep 1108455 = 1662683) B1662683
theorem B2485439 : Blo 1104625 2485439 := bstep (se 1 (by rfl) ⟨1864079, by rfl⟩ : syracuseStep 2485439 = 3728159) B3728159
theorem B3730697 : Blo 1104625 3730697 := bstep (se 2 (by rfl) ⟨1399011, by rfl⟩ : syracuseStep 3730697 = 2798023) B2798023
theorem B2486087 : Blo 1104625 2486087 := bstep (se 1 (by rfl) ⟨1864565, by rfl⟩ : syracuseStep 2486087 = 3729131) B3729131
theorem B2486267 : Blo 1104625 2486267 := bstep (se 1 (by rfl) ⟨1864700, by rfl⟩ : syracuseStep 2486267 = 3729401) B3729401
theorem B2486447 : Blo 1104625 2486447 := bstep (se 1 (by rfl) ⟨1864835, by rfl⟩ : syracuseStep 2486447 = 3729671) B3729671
theorem B5042351 : Blo 1104625 5042351 := bstep (se 1 (by rfl) ⟨3781763, by rfl⟩ : syracuseStep 5042351 = 7563527) B7563527
theorem B12972413 : Blo 1104625 12972413 := bstep (se 3 (by rfl) ⟨2432327, by rfl⟩ : syracuseStep 12972413 = 4864655) B4864655
theorem B5600339 : Blo 1104625 5600339 := bstep (se 1 (by rfl) ⟨4200254, by rfl⟩ : syracuseStep 5600339 = 8400509) B8400509
theorem B2880679 : Blo 1104625 2880679 := bstep (se 1 (by rfl) ⟨2160509, by rfl⟩ : syracuseStep 2880679 = 4321019) B4321019
theorem B1243183 : Blo 1104625 1243183 := bstep (se 1 (by rfl) ⟨932387, by rfl⟩ : syracuseStep 1243183 = 1864775) B1864775
theorem B8518081 : Blo 1104625 8518081 := bstep (se 2 (by rfl) ⟨3194280, by rfl⟩ : syracuseStep 8518081 = 6388561) B6388561
theorem B1866233 : Blo 1104625 1866233 := bstep (se 2 (by rfl) ⟨699837, by rfl⟩ : syracuseStep 1866233 = 1399675) B1399675
theorem B1866503 : Blo 1104625 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B1866847 : Blo 1104625 1866847 := bstep (se 1 (by rfl) ⟨1400135, by rfl⟩ : syracuseStep 1866847 = 2800271) B2800271
theorem B1867063 : Blo 1104625 1867063 := bstep (se 1 (by rfl) ⟨1400297, by rfl⟩ : syracuseStep 1867063 = 2800595) B2800595
theorem B2489993 : Blo 1104625 2489993 := bstep (se 2 (by rfl) ⟨933747, by rfl⟩ : syracuseStep 2489993 = 1867495) B1867495
theorem B1867583 : Blo 1104625 1867583 := bstep (se 1 (by rfl) ⟨1400687, by rfl⟩ : syracuseStep 1867583 = 2801375) B2801375
theorem B1245019 : Blo 1104625 1245019 := bstep (se 1 (by rfl) ⟨933764, by rfl⟩ : syracuseStep 1245019 = 1867529) B1867529
theorem B5603255 : Blo 1104625 5603255 := bstep (se 1 (by rfl) ⟨4202441, by rfl⟩ : syracuseStep 5603255 = 8404883) B8404883
theorem B15925187 : Blo 1104625 15925187 := bstep (se 1 (by rfl) ⟨11943890, by rfl⟩ : syracuseStep 15925187 = 23887781) B23887781
theorem B3735827 : Blo 1104625 3735827 := bstep (se 1 (by rfl) ⟨2801870, by rfl⟩ : syracuseStep 3735827 = 5603741) B5603741
theorem B5046583 : Blo 1104625 5046583 := bstep (se 1 (by rfl) ⟨3784937, by rfl⟩ : syracuseStep 5046583 = 7569875) B7569875
theorem B1868089 : Blo 1104625 1868089 := bstep (se 2 (by rfl) ⟨700533, by rfl⟩ : syracuseStep 1868089 = 1401067) B1401067
theorem B2130683 : Blo 1104625 2130683 := bstep (se 1 (by rfl) ⟨1598012, by rfl⟩ : syracuseStep 2130683 = 3196025) B3196025
theorem B2491433 : Blo 1104625 2491433 := bstep (se 2 (by rfl) ⟨934287, by rfl⟩ : syracuseStep 2491433 = 1868575) B1868575
theorem B2491487 : Blo 1104625 2491487 := bstep (se 1 (by rfl) ⟨1868615, by rfl⟩ : syracuseStep 2491487 = 3737231) B3737231
theorem B4195547 : Blo 1104625 4195547 := bstep (se 1 (by rfl) ⟨3146660, by rfl⟩ : syracuseStep 4195547 = 6293321) B6293321
theorem B17925371 : Blo 1104625 17925371 := bstep (se 1 (by rfl) ⟨13444028, by rfl⟩ : syracuseStep 17925371 = 26888057) B26888057
theorem B2491667 : Blo 1104625 2491667 := bstep (se 1 (by rfl) ⟨1868750, by rfl⟩ : syracuseStep 2491667 = 3737501) B3737501
theorem B9438545 : Blo 1104625 9438545 := bstep (se 2 (by rfl) ⟨3539454, by rfl⟩ : syracuseStep 9438545 = 7078909) B7078909
theorem B1869851 : Blo 1104625 1869851 := bstep (se 1 (by rfl) ⟨1402388, by rfl⟩ : syracuseStep 1869851 = 2804777) B2804777
theorem B14190623 : Blo 1104625 14190623 := bstep (se 1 (by rfl) ⟨10642967, by rfl⟩ : syracuseStep 14190623 = 21285935) B21285935
theorem B1869871 : Blo 1104625 1869871 := bstep (se 1 (by rfl) ⟨1402403, by rfl⟩ : syracuseStep 1869871 = 2804807) B2804807
theorem B413894717 : Blo 1104625 413894717 := bstep (se 3 (by rfl) ⟨77605259, by rfl⟩ : syracuseStep 413894717 = 155210519) B155210519
theorem B17238131 : Blo 1104625 17238131 := bstep (se 1 (by rfl) ⟨12928598, by rfl⟩ : syracuseStep 17238131 = 25857197) B25857197
theorem B4196717 : Blo 1104625 4196717 := bstep (se 3 (by rfl) ⟨786884, by rfl⟩ : syracuseStep 4196717 = 1573769) B1573769
theorem B5671415 : Blo 1104625 5671415 := bstep (se 1 (by rfl) ⟨4253561, by rfl⟩ : syracuseStep 5671415 = 8507123) B8507123
theorem B2099839 : Blo 1104625 2099839 := bstep (se 1 (by rfl) ⟨1574879, by rfl⟩ : syracuseStep 2099839 = 3149759) B3149759
theorem B2493071 : Blo 1104625 2493071 := bstep (se 1 (by rfl) ⟨1869803, by rfl⟩ : syracuseStep 2493071 = 3739607) B3739607
theorem B8981279 : Blo 1104625 8981279 := bstep (se 1 (by rfl) ⟨6735959, by rfl⟩ : syracuseStep 8981279 = 13471919) B13471919
theorem B17009551 : Blo 1104625 17009551 := bstep (se 1 (by rfl) ⟨12757163, by rfl⟩ : syracuseStep 17009551 = 25514327) B25514327
theorem B11963483 : Blo 1104625 11963483 := bstep (se 1 (by rfl) ⟨8972612, by rfl⟩ : syracuseStep 11963483 = 17945225) B17945225
theorem B9571753 : Blo 1104625 9571753 := bstep (se 2 (by rfl) ⟨3589407, by rfl⟩ : syracuseStep 9571753 = 7178815) B7178815
theorem B2493971 : Blo 1104625 2493971 := bstep (se 1 (by rfl) ⟨1870478, by rfl⟩ : syracuseStep 2493971 = 3740957) B3740957
theorem B2494043 : Blo 1104625 2494043 := bstep (se 1 (by rfl) ⟨1870532, by rfl⟩ : syracuseStep 2494043 = 3741065) B3741065
theorem B3542633 : Blo 1104625 3542633 := bstep (se 2 (by rfl) ⟨1328487, by rfl⟩ : syracuseStep 3542633 = 2656975) B2656975
theorem B4722401 : Blo 1104625 4722401 := bstep (se 2 (by rfl) ⟨1770900, by rfl⟩ : syracuseStep 4722401 = 3541801) B3541801
theorem B12586913 : Blo 1104625 12586913 := bstep (se 2 (by rfl) ⟨4720092, by rfl⟩ : syracuseStep 12586913 = 9440185) B9440185
theorem B4788371 : Blo 1104625 4788371 := bstep (se 1 (by rfl) ⟨3591278, by rfl⟩ : syracuseStep 4788371 = 7182557) B7182557
theorem B3739823 : Blo 1104625 3739823 := bstep (se 1 (by rfl) ⟨2804867, by rfl⟩ : syracuseStep 3739823 = 5609735) B5609735
theorem B3739931 : Blo 1104625 3739931 := bstep (se 1 (by rfl) ⟨2804948, by rfl⟩ : syracuseStep 3739931 = 5609897) B5609897
theorem B4199647 : Blo 1104625 4199647 := bstep (se 1 (by rfl) ⟨3149735, by rfl⟩ : syracuseStep 4199647 = 6299471) B6299471
theorem B2102527 : Blo 1104625 2102527 := bstep (se 1 (by rfl) ⟨1576895, by rfl⟩ : syracuseStep 2102527 = 3153791) B3153791
theorem B8394191 : Blo 1104625 8394191 := bstep (se 1 (by rfl) ⟨6295643, by rfl⟩ : syracuseStep 8394191 = 12591287) B12591287
theorem B7083935 : Blo 1104625 7083935 := bstep (se 1 (by rfl) ⟨5312951, by rfl⟩ : syracuseStep 7083935 = 10625903) B10625903
theorem B5314643 : Blo 1104625 5314643 := bstep (se 1 (by rfl) ⟨3985982, by rfl⟩ : syracuseStep 5314643 = 7971965) B7971965
theorem B3152287 : Blo 1104625 3152287 := bstep (se 1 (by rfl) ⟨2364215, by rfl⟩ : syracuseStep 3152287 = 4728431) B4728431
theorem B31922909 : Blo 1104625 31922909 := bstep (se 3 (by rfl) ⟨5985545, by rfl⟩ : syracuseStep 31922909 = 11971091) B11971091
theorem B3840905 : Blo 1104625 3840905 := bstep (se 2 (by rfl) ⟨1440339, by rfl⟩ : syracuseStep 3840905 = 2880679) B2880679
theorem B4201577 : Blo 1104625 4201577 := bstep (se 2 (by rfl) ⟨1575591, by rfl⟩ : syracuseStep 4201577 = 3151183) B3151183
theorem B4725971 : Blo 1104625 4725971 := bstep (se 1 (by rfl) ⟨3544478, by rfl⟩ : syracuseStep 4725971 = 7088957) B7088957
theorem B3153107 : Blo 1104625 3153107 := bstep (se 1 (by rfl) ⟨2364830, by rfl⟩ : syracuseStep 3153107 = 4729661) B4729661
theorem B4201895 : Blo 1104625 4201895 := bstep (se 1 (by rfl) ⟨3151421, by rfl⟩ : syracuseStep 4201895 = 6302843) B6302843
theorem B5611193 : Blo 1104625 5611193 := bstep (se 2 (by rfl) ⟨2104197, by rfl⟩ : syracuseStep 5611193 = 4208395) B4208395
theorem B6299927 : Blo 1104625 6299927 := bstep (se 1 (by rfl) ⟨4724945, by rfl⟩ : syracuseStep 6299927 = 9449891) B9449891
theorem B7086599 : Blo 1104625 7086599 := bstep (se 1 (by rfl) ⟨5314949, by rfl⟩ : syracuseStep 7086599 = 10629899) B10629899
theorem B8988023 : Blo 1104625 8988023 := bstep (se 1 (by rfl) ⟨6741017, by rfl⟩ : syracuseStep 8988023 = 13482035) B13482035
theorem B12592745 : Blo 1104625 12592745 := bstep (se 2 (by rfl) ⟨4722279, by rfl⟩ : syracuseStep 12592745 = 9444559) B9444559
theorem B8399051 : Blo 1104625 8399051 := bstep (se 1 (by rfl) ⟨6299288, by rfl⟩ : syracuseStep 8399051 = 12598577) B12598577
theorem B14396395 : Blo 1104625 14396395 := bstep (se 1 (by rfl) ⟨10797296, by rfl⟩ : syracuseStep 14396395 = 21594593) B21594593
theorem B13446269 : Blo 1104625 13446269 := bstep (se 3 (by rfl) ⟨2521175, by rfl⟩ : syracuseStep 13446269 = 5042351) B5042351
theorem B2796727 : Blo 1104625 2796727 := bstep (se 1 (by rfl) ⟨2097545, by rfl⟩ : syracuseStep 2796727 = 4195091) B4195091
theorem B4730071 : Blo 1104625 4730071 := bstep (se 1 (by rfl) ⟨3547553, by rfl⟩ : syracuseStep 4730071 = 7095107) B7095107
theorem B4205783 : Blo 1104625 4205783 := bstep (se 1 (by rfl) ⟨3154337, by rfl⟩ : syracuseStep 4205783 = 6308675) B6308675
theorem B4205951 : Blo 1104625 4205951 := bstep (se 1 (by rfl) ⟨3154463, by rfl⟩ : syracuseStep 4205951 = 6308927) B6308927
theorem B4730345 : Blo 1104625 4730345 := bstep (se 2 (by rfl) ⟨1773879, by rfl⟩ : syracuseStep 4730345 = 3547759) B3547759
theorem B6303527 : Blo 1104625 6303527 := bstep (se 1 (by rfl) ⟨4727645, by rfl⟩ : syracuseStep 6303527 = 9455291) B9455291
theorem B19149007 : Blo 1104625 19149007 := bstep (se 1 (by rfl) ⟨14361755, by rfl⟩ : syracuseStep 19149007 = 28723511) B28723511
theorem B15970567 : Blo 1104625 15970567 := bstep (se 1 (by rfl) ⟨11977925, by rfl⟩ : syracuseStep 15970567 = 23955851) B23955851
theorem B4731371 : Blo 1104625 4731371 := bstep (se 1 (by rfl) ⟨3548528, by rfl⟩ : syracuseStep 4731371 = 7097057) B7097057
theorem B5321791 : Blo 1104625 5321791 := bstep (se 1 (by rfl) ⟨3991343, by rfl⟩ : syracuseStep 5321791 = 7982687) B7982687
theorem B2242075 : Blo 1104625 2242075 := bstep (se 1 (by rfl) ⟨1681556, by rfl⟩ : syracuseStep 2242075 = 3363113) B3363113
theorem B155269001 : Blo 1104625 155269001 := bstep (se 2 (by rfl) ⟨58225875, by rfl⟩ : syracuseStep 155269001 = 116451751) B116451751
theorem B4046269 : Blo 1104625 4046269 := bstep (se 3 (by rfl) ⟨758675, by rfl⟩ : syracuseStep 4046269 = 1517351) B1517351
theorem B19152379 : Blo 1104625 19152379 := bstep (se 1 (by rfl) ⟨14364284, by rfl⟩ : syracuseStep 19152379 = 28728569) B28728569
theorem B8405369 : Blo 1104625 8405369 := bstep (se 2 (by rfl) ⟨3152013, by rfl⟩ : syracuseStep 8405369 = 6304027) B6304027
theorem B71910611 : Blo 1104625 71910611 := bstep (se 1 (by rfl) ⟨53932958, by rfl⟩ : syracuseStep 71910611 = 107865917) B107865917
theorem B3589775 : Blo 1104625 3589775 := bstep (se 1 (by rfl) ⟨2692331, by rfl⟩ : syracuseStep 3589775 = 5384663) B5384663
theorem B2803835 : Blo 1104625 2803835 := bstep (se 1 (by rfl) ⟨2102876, by rfl⟩ : syracuseStep 2803835 = 4205753) B4205753
theorem B1656959 : Blo 1104625 1656959 := bstep (se 1 (by rfl) ⟨1242719, by rfl⟩ : syracuseStep 1656959 = 2485439) B2485439
theorem B1657391 : Blo 1104625 1657391 := bstep (se 1 (by rfl) ⟨1243043, by rfl⟩ : syracuseStep 1657391 = 2486087) B2486087
theorem B1657511 : Blo 1104625 1657511 := bstep (se 1 (by rfl) ⟨1243133, by rfl⟩ : syracuseStep 1657511 = 2486267) B2486267
theorem B1657577 : Blo 1104625 1657577 := bstep (se 2 (by rfl) ⟨621591, by rfl⟩ : syracuseStep 1657577 = 1243183) B1243183
theorem B1657631 : Blo 1104625 1657631 := bstep (se 1 (by rfl) ⟨1243223, by rfl⟩ : syracuseStep 1657631 = 2486447) B2486447
theorem B11357441 : Blo 1104625 11357441 := bstep (se 2 (by rfl) ⟨4259040, by rfl⟩ : syracuseStep 11357441 = 8518081) B8518081
theorem B83119601 : Blo 1104625 83119601 := bstep (se 2 (by rfl) ⟨31169850, by rfl⟩ : syracuseStep 83119601 = 62339701) B62339701
theorem B1659995 : Blo 1104625 1659995 := bstep (se 1 (by rfl) ⟨1244996, by rfl⟩ : syracuseStep 1659995 = 2489993) B2489993
theorem B1660025 : Blo 1104625 1660025 := bstep (se 2 (by rfl) ⟨622509, by rfl⟩ : syracuseStep 1660025 = 1245019) B1245019
theorem B3986617 : Blo 1104625 3986617 := bstep (se 2 (by rfl) ⟨1494981, by rfl⟩ : syracuseStep 3986617 = 2989963) B2989963
theorem B7099721 : Blo 1104625 7099721 := bstep (se 2 (by rfl) ⟨2662395, by rfl⟩ : syracuseStep 7099721 = 5324791) B5324791
theorem B1660415 : Blo 1104625 1660415 := bstep (se 1 (by rfl) ⟨1245311, by rfl⟩ : syracuseStep 1660415 = 2490623) B2490623
theorem B1660793 : Blo 1104625 1660793 := bstep (se 2 (by rfl) ⟨622797, by rfl⟩ : syracuseStep 1660793 = 1245595) B1245595
theorem B1660799 : Blo 1104625 1660799 := bstep (se 1 (by rfl) ⟨1245599, by rfl⟩ : syracuseStep 1660799 = 2491199) B2491199
theorem B1497199 : Blo 1104625 1497199 := bstep (se 1 (by rfl) ⟨1122899, by rfl⟩ : syracuseStep 1497199 = 2245799) B2245799
theorem B34593101 : Blo 1104625 34593101 := bstep (se 3 (by rfl) ⟨6486206, by rfl⟩ : syracuseStep 34593101 = 12972413) B12972413
theorem B8968819 : Blo 1104625 8968819 := bstep (se 1 (by rfl) ⟨6726614, by rfl⟩ : syracuseStep 8968819 = 13453229) B13453229
theorem B1661567 : Blo 1104625 1661567 := bstep (se 1 (by rfl) ⟨1246175, by rfl⟩ : syracuseStep 1661567 = 2492351) B2492351
theorem B1104635 : Blo 1104625 1104635 := bstep (se 1 (by rfl) ⟨828476, by rfl⟩ : syracuseStep 1104635 = 1656953) B1656953
theorem B1661705 : Blo 1104625 1661705 := bstep (se 2 (by rfl) ⟨623139, by rfl⟩ : syracuseStep 1661705 = 1246279) B1246279
theorem B1104767 : Blo 1104625 1104767 := bstep (se 1 (by rfl) ⟨828575, by rfl⟩ : syracuseStep 1104767 = 1657151) B1657151
theorem B1104863 : Blo 1104625 1104863 := bstep (se 1 (by rfl) ⟨828647, by rfl⟩ : syracuseStep 1104863 = 1657295) B1657295
theorem B1661945 : Blo 1104625 1661945 := bstep (se 2 (by rfl) ⟨623229, by rfl⟩ : syracuseStep 1661945 = 1246459) B1246459
theorem B1104891 : Blo 1104625 1104891 := bstep (se 1 (by rfl) ⟨828668, by rfl⟩ : syracuseStep 1104891 = 1657337) B1657337
theorem B1104923 : Blo 1104625 1104923 := bstep (se 1 (by rfl) ⟨828692, by rfl⟩ : syracuseStep 1104923 = 1657385) B1657385
theorem B1662263 : Blo 1104625 1662263 := bstep (se 1 (by rfl) ⟨1246697, by rfl⟩ : syracuseStep 1662263 = 2493395) B2493395
theorem B1105215 : Blo 1104625 1105215 := bstep (se 1 (by rfl) ⟨828911, by rfl⟩ : syracuseStep 1105215 = 1657823) B1657823
theorem B1662443 : Blo 1104625 1662443 := bstep (se 1 (by rfl) ⟨1246832, by rfl⟩ : syracuseStep 1662443 = 2493665) B2493665
theorem B1105511 : Blo 1104625 1105511 := bstep (se 1 (by rfl) ⟨829133, by rfl⟩ : syracuseStep 1105511 = 1658267) B1658267
theorem B1105755 : Blo 1104625 1105755 := bstep (se 1 (by rfl) ⟨829316, by rfl⟩ : syracuseStep 1105755 = 1658633) B1658633
theorem B1105791 : Blo 1104625 1105791 := bstep (se 1 (by rfl) ⟨829343, by rfl⟩ : syracuseStep 1105791 = 1658687) B1658687
theorem B1105951 : Blo 1104625 1105951 := bstep (se 1 (by rfl) ⟨829463, by rfl⟩ : syracuseStep 1105951 = 1658927) B1658927
theorem B1106247 : Blo 1104625 1106247 := bstep (se 1 (by rfl) ⟨829685, by rfl⟩ : syracuseStep 1106247 = 1659371) B1659371
theorem B1106331 : Blo 1104625 1106331 := bstep (se 1 (by rfl) ⟨829748, by rfl⟩ : syracuseStep 1106331 = 1659497) B1659497
theorem B1106335 : Blo 1104625 1106335 := bstep (se 1 (by rfl) ⟨829751, by rfl⟩ : syracuseStep 1106335 = 1659503) B1659503
theorem B1106415 : Blo 1104625 1106415 := bstep (se 1 (by rfl) ⟨829811, by rfl⟩ : syracuseStep 1106415 = 1659623) B1659623
theorem B5595641 : Blo 1104625 5595641 := bstep (se 2 (by rfl) ⟨2098365, by rfl⟩ : syracuseStep 5595641 = 4196731) B4196731
theorem B1106523 : Blo 1104625 1106523 := bstep (se 1 (by rfl) ⟨829892, by rfl⟩ : syracuseStep 1106523 = 1659785) B1659785
theorem B1106751 : Blo 1104625 1106751 := bstep (se 1 (by rfl) ⟨830063, by rfl⟩ : syracuseStep 1106751 = 1660127) B1660127
theorem B1106779 : Blo 1104625 1106779 := bstep (se 1 (by rfl) ⟨830084, by rfl⟩ : syracuseStep 1106779 = 1660169) B1660169
theorem B1893503 : Blo 1104625 1893503 := bstep (se 1 (by rfl) ⟨1420127, by rfl⟩ : syracuseStep 1893503 = 2840255) B2840255
theorem B1107071 : Blo 1104625 1107071 := bstep (se 1 (by rfl) ⟨830303, by rfl⟩ : syracuseStep 1107071 = 1660607) B1660607
theorem B1107099 : Blo 1104625 1107099 := bstep (se 1 (by rfl) ⟨830324, by rfl⟩ : syracuseStep 1107099 = 1660649) B1660649
theorem B3990683 : Blo 1104625 3990683 := bstep (se 1 (by rfl) ⟨2993012, by rfl⟩ : syracuseStep 3990683 = 5986025) B5986025
theorem B1107103 : Blo 1104625 1107103 := bstep (se 1 (by rfl) ⟨830327, by rfl⟩ : syracuseStep 1107103 = 1660655) B1660655
theorem B14181601 : Blo 1104625 14181601 := bstep (se 2 (by rfl) ⟨5318100, by rfl⟩ : syracuseStep 14181601 = 10636201) B10636201
theorem B1107439 : Blo 1104625 1107439 := bstep (se 1 (by rfl) ⟨830579, by rfl⟩ : syracuseStep 1107439 = 1661159) B1661159
theorem B63891017 : Blo 1104625 63891017 := bstep (se 2 (by rfl) ⟨23959131, by rfl⟩ : syracuseStep 63891017 = 47918263) B47918263
theorem B1107559 : Blo 1104625 1107559 := bstep (se 1 (by rfl) ⟨830669, by rfl⟩ : syracuseStep 1107559 = 1661339) B1661339
theorem B70116997 : Blo 1104625 70116997 := bstep (se 4 (by rfl) ⟨6573468, by rfl⟩ : syracuseStep 70116997 = 13146937) B13146937
theorem B7563091 : Blo 1104625 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B1107823 : Blo 1104625 1107823 := bstep (se 1 (by rfl) ⟨830867, by rfl⟩ : syracuseStep 1107823 = 1661735) B1661735
theorem B1107839 : Blo 1104625 1107839 := bstep (se 1 (by rfl) ⟨830879, by rfl⟩ : syracuseStep 1107839 = 1661759) B1661759
theorem B5597099 : Blo 1104625 5597099 := bstep (se 1 (by rfl) ⟨4197824, by rfl⟩ : syracuseStep 5597099 = 8395649) B8395649
theorem B1108039 : Blo 1104625 1108039 := bstep (se 1 (by rfl) ⟨831029, by rfl⟩ : syracuseStep 1108039 = 1662059) B1662059
theorem B3729563 : Blo 1104625 3729563 := bstep (se 1 (by rfl) ⟨2797172, by rfl⟩ : syracuseStep 3729563 = 5594345) B5594345
theorem B1108135 : Blo 1104625 1108135 := bstep (se 1 (by rfl) ⟨831101, by rfl⟩ : syracuseStep 1108135 = 1662203) B1662203
theorem B4483259 : Blo 1104625 4483259 := bstep (se 1 (by rfl) ⟨3362444, by rfl⟩ : syracuseStep 4483259 = 6724889) B6724889
theorem B1108199 : Blo 1104625 1108199 := bstep (se 1 (by rfl) ⟨831149, by rfl⟩ : syracuseStep 1108199 = 1662299) B1662299
theorem B1108219 : Blo 1104625 1108219 := bstep (se 1 (by rfl) ⟨831164, by rfl⟩ : syracuseStep 1108219 = 1662329) B1662329
theorem B1108223 : Blo 1104625 1108223 := bstep (se 1 (by rfl) ⟨831167, by rfl⟩ : syracuseStep 1108223 = 1662335) B1662335
theorem B1108591 : Blo 1104625 1108591 := bstep (se 1 (by rfl) ⟨831443, by rfl⟩ : syracuseStep 1108591 = 1662887) B1662887
theorem B4485059 : Blo 1104625 4485059 := bstep (se 1 (by rfl) ⟨3363794, by rfl⟩ : syracuseStep 4485059 = 6727589) B6727589
theorem B2486555 : Blo 1104625 2486555 := bstep (se 1 (by rfl) ⟨1864916, by rfl⟩ : syracuseStep 2486555 = 3729833) B3729833
theorem B9597251 : Blo 1104625 9597251 := bstep (se 1 (by rfl) ⟨7197938, by rfl⟩ : syracuseStep 9597251 = 14395877) B14395877
theorem B2487131 : Blo 1104625 2487131 := bstep (se 1 (by rfl) ⟨1865348, by rfl⟩ : syracuseStep 2487131 = 3730697) B3730697
theorem B2913259 : Blo 1104625 2913259 := bstep (se 1 (by rfl) ⟨2184944, by rfl⟩ : syracuseStep 2913259 = 4369889) B4369889
theorem B18904427 : Blo 1104625 18904427 := bstep (se 1 (by rfl) ⟨14178320, by rfl⟩ : syracuseStep 18904427 = 28356641) B28356641
theorem B1865423 : Blo 1104625 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B3995369 : Blo 1104625 3995369 := bstep (se 2 (by rfl) ⟨1498263, by rfl⟩ : syracuseStep 3995369 = 2996527) B2996527
theorem B2127727 : Blo 1104625 2127727 := bstep (se 1 (by rfl) ⟨1595795, by rfl⟩ : syracuseStep 2127727 = 3191591) B3191591
theorem B3733559 : Blo 1104625 3733559 := bstep (se 1 (by rfl) ⟨2800169, by rfl⟩ : syracuseStep 3733559 = 5600339) B5600339
theorem B1865983 : Blo 1104625 1865983 := bstep (se 1 (by rfl) ⟨1399487, by rfl⟩ : syracuseStep 1865983 = 2798975) B2798975
theorem B2489129 : Blo 1104625 2489129 := bstep (se 2 (by rfl) ⟨933423, by rfl⟩ : syracuseStep 2489129 = 1866847) B1866847
theorem B71727929 : Blo 1104625 71727929 := bstep (se 2 (by rfl) ⟨26897973, by rfl⟩ : syracuseStep 71727929 = 53795947) B53795947
theorem B15170399 : Blo 1104625 15170399 := bstep (se 1 (by rfl) ⟨11377799, by rfl⟩ : syracuseStep 15170399 = 22755599) B22755599
theorem B1866719 : Blo 1104625 1866719 := bstep (se 1 (by rfl) ⟨1400039, by rfl⟩ : syracuseStep 1866719 = 2800079) B2800079
theorem B1244155 : Blo 1104625 1244155 := bstep (se 1 (by rfl) ⟨933116, by rfl⟩ : syracuseStep 1244155 = 1866233) B1866233
theorem B2489417 : Blo 1104625 2489417 := bstep (se 2 (by rfl) ⟨933531, by rfl⟩ : syracuseStep 2489417 = 1867063) B1867063
theorem B1244335 : Blo 1104625 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B10780073 : Blo 1104625 10780073 := bstep (se 2 (by rfl) ⟨4042527, by rfl⟩ : syracuseStep 10780073 = 8085055) B8085055
theorem B1245055 : Blo 1104625 1245055 := bstep (se 1 (by rfl) ⟨933791, by rfl⟩ : syracuseStep 1245055 = 1867583) B1867583
theorem B1867657 : Blo 1104625 1867657 := bstep (se 2 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 1867657 = 1400743) B1400743
theorem B3735503 : Blo 1104625 3735503 := bstep (se 1 (by rfl) ⟨2801627, by rfl⟩ : syracuseStep 3735503 = 5603255) B5603255
theorem B10616791 : Blo 1104625 10616791 := bstep (se 1 (by rfl) ⟨7962593, by rfl⟩ : syracuseStep 10616791 = 15925187) B15925187
theorem B2490551 : Blo 1104625 2490551 := bstep (se 1 (by rfl) ⟨1867913, by rfl⟩ : syracuseStep 2490551 = 3735827) B3735827
theorem B5603579 : Blo 1104625 5603579 := bstep (se 1 (by rfl) ⟨4202684, by rfl⟩ : syracuseStep 5603579 = 8405369) B8405369
theorem B2490785 : Blo 1104625 2490785 := bstep (se 2 (by rfl) ⟨934044, by rfl⟩ : syracuseStep 2490785 = 1868089) B1868089
theorem B47940407 : Blo 1104625 47940407 := bstep (se 1 (by rfl) ⟨35955305, by rfl⟩ : syracuseStep 47940407 = 71910611) B71910611
theorem B25592669 : Blo 1104625 25592669 := bstep (se 3 (by rfl) ⟨4798625, by rfl⟩ : syracuseStep 25592669 = 9597251) B9597251
theorem B6292363 : Blo 1104625 6292363 := bstep (se 1 (by rfl) ⟨4719272, by rfl⟩ : syracuseStep 6292363 = 9438545) B9438545
theorem B2393183 : Blo 1104625 2393183 := bstep (se 1 (by rfl) ⟨1794887, by rfl⟩ : syracuseStep 2393183 = 3589775) B3589775
theorem B1246567 : Blo 1104625 1246567 := bstep (se 1 (by rfl) ⟨934925, by rfl⟩ : syracuseStep 1246567 = 1869851) B1869851
theorem B1869223 : Blo 1104625 1869223 := bstep (se 1 (by rfl) ⟨1401917, by rfl⟩ : syracuseStep 1869223 = 2803835) B2803835
theorem B18908801 : Blo 1104625 18908801 := bstep (se 2 (by rfl) ⟨7090800, by rfl⟩ : syracuseStep 18908801 = 14181601) B14181601
theorem B7571627 : Blo 1104625 7571627 := bstep (se 1 (by rfl) ⟨5678720, by rfl⟩ : syracuseStep 7571627 = 11357441) B11357441
theorem B93489329 : Blo 1104625 93489329 := bstep (se 2 (by rfl) ⟨35058498, by rfl⟩ : syracuseStep 93489329 = 70116997) B70116997
theorem B55413067 : Blo 1104625 55413067 := bstep (se 1 (by rfl) ⟨41559800, by rfl⟩ : syracuseStep 55413067 = 83119601) B83119601
theorem B2361755 : Blo 1104625 2361755 := bstep (se 1 (by rfl) ⟨1771316, by rfl⟩ : syracuseStep 2361755 = 3542633) B3542633
theorem B3148267 : Blo 1104625 3148267 := bstep (se 1 (by rfl) ⟨2361200, by rfl⟩ : syracuseStep 3148267 = 4722401) B4722401
theorem B8391275 : Blo 1104625 8391275 := bstep (se 1 (by rfl) ⟨6293456, by rfl⟩ : syracuseStep 8391275 = 12586913) B12586913
theorem B2493161 : Blo 1104625 2493161 := bstep (se 2 (by rfl) ⟨934935, by rfl⟩ : syracuseStep 2493161 = 1869871) B1869871
theorem B2493215 : Blo 1104625 2493215 := bstep (se 1 (by rfl) ⟨1869911, by rfl⟩ : syracuseStep 2493215 = 3739823) B3739823
theorem B2493287 : Blo 1104625 2493287 := bstep (se 1 (by rfl) ⟨1869965, by rfl⟩ : syracuseStep 2493287 = 3739931) B3739931
theorem B22679401 : Blo 1104625 22679401 := bstep (se 2 (by rfl) ⟨8504775, by rfl⟩ : syracuseStep 22679401 = 17009551) B17009551
theorem B4722623 : Blo 1104625 4722623 := bstep (se 1 (by rfl) ⟨3541967, by rfl⟩ : syracuseStep 4722623 = 7083935) B7083935
theorem B3543095 : Blo 1104625 3543095 := bstep (se 1 (by rfl) ⟨2657321, by rfl⟩ : syracuseStep 3543095 = 5314643) B5314643
theorem B3150647 : Blo 1104625 3150647 := bstep (se 1 (by rfl) ⟨2362985, by rfl⟩ : syracuseStep 3150647 = 4725971) B4725971
theorem B3740795 : Blo 1104625 3740795 := bstep (se 1 (by rfl) ⟨2805596, by rfl⟩ : syracuseStep 3740795 = 5611193) B5611193
theorem B4199951 : Blo 1104625 4199951 := bstep (se 1 (by rfl) ⟨3149963, by rfl⟩ : syracuseStep 4199951 = 6299927) B6299927
theorem B25532009 : Blo 1104625 25532009 := bstep (se 2 (by rfl) ⟨9574503, by rfl⟩ : syracuseStep 25532009 = 19149007) B19149007
theorem B28382885 : Blo 1104625 28382885 := bstep (se 4 (by rfl) ⟨2660895, by rfl⟩ : syracuseStep 28382885 = 5321791) B5321791
theorem B4724399 : Blo 1104625 4724399 := bstep (se 1 (by rfl) ⟨3543299, by rfl⟩ : syracuseStep 4724399 = 7086599) B7086599
theorem B2660455 : Blo 1104625 2660455 := bstep (se 1 (by rfl) ⟨1995341, by rfl⟩ : syracuseStep 2660455 = 3990683) B3990683
theorem B8395163 : Blo 1104625 8395163 := bstep (se 1 (by rfl) ⟨6296372, by rfl⟩ : syracuseStep 8395163 = 12592745) B12592745
theorem B2988839 : Blo 1104625 2988839 := bstep (se 1 (by rfl) ⟨2241629, by rfl⟩ : syracuseStep 2988839 = 4483259) B4483259
theorem B5315489 : Blo 1104625 5315489 := bstep (se 2 (by rfl) ⟨1993308, by rfl⟩ : syracuseStep 5315489 = 3986617) B3986617
theorem B2989433 : Blo 1104625 2989433 := bstep (se 2 (by rfl) ⟨1121037, by rfl⟩ : syracuseStep 2989433 = 2242075) B2242075
theorem B3153563 : Blo 1104625 3153563 := bstep (se 1 (by rfl) ⟨2365172, by rfl⟩ : syracuseStep 3153563 = 4730345) B4730345
theorem B4202351 : Blo 1104625 4202351 := bstep (se 1 (by rfl) ⟨3151763, by rfl⟩ : syracuseStep 4202351 = 6303527) B6303527
theorem B2990039 : Blo 1104625 2990039 := bstep (se 1 (by rfl) ⟨2242529, by rfl⟩ : syracuseStep 2990039 = 4485059) B4485059
theorem B3154247 : Blo 1104625 3154247 := bstep (se 1 (by rfl) ⟨2365685, by rfl⟩ : syracuseStep 3154247 = 4731371) B4731371
theorem B4203049 : Blo 1104625 4203049 := bstep (se 2 (by rfl) ⟨1576143, by rfl⟩ : syracuseStep 4203049 = 3152287) B3152287
theorem B2663579 : Blo 1104625 2663579 := bstep (se 1 (by rfl) ⟨1997684, by rfl⟩ : syracuseStep 2663579 = 3995369) B3995369
theorem B47818619 : Blo 1104625 47818619 := bstep (se 1 (by rfl) ⟨35863964, by rfl⟩ : syracuseStep 47818619 = 71727929) B71727929
theorem B11347877 : Blo 1104625 11347877 := bstep (se 4 (by rfl) ⟨1063863, by rfl⟩ : syracuseStep 11347877 = 2127727) B2127727
theorem B25536505 : Blo 1104625 25536505 := bstep (se 2 (by rfl) ⟨9576189, by rfl⟩ : syracuseStep 25536505 = 19152379) B19152379
theorem B7186715 : Blo 1104625 7186715 := bstep (se 1 (by rfl) ⟨5390036, by rfl⟩ : syracuseStep 7186715 = 10780073) B10780073
theorem B6728777 : Blo 1104625 6728777 := bstep (se 2 (by rfl) ⟨2523291, by rfl⟩ : syracuseStep 6728777 = 5046583) B5046583
theorem B2797031 : Blo 1104625 2797031 := bstep (se 1 (by rfl) ⟨2097773, by rfl⟩ : syracuseStep 2797031 = 4195547) B4195547
theorem B183873397 : Blo 1104625 183873397 := bstep (se 5 (by rfl) ⟨8619065, by rfl⟩ : syracuseStep 183873397 = 17238131) B17238131
theorem B2797811 : Blo 1104625 2797811 := bstep (se 1 (by rfl) ⟨2098358, by rfl⟩ : syracuseStep 2797811 = 4196717) B4196717
theorem B5681821 : Blo 1104625 5681821 := bstep (se 3 (by rfl) ⟨1065341, by rfl⟩ : syracuseStep 5681821 = 2130683) B2130683
theorem B7975655 : Blo 1104625 7975655 := bstep (se 1 (by rfl) ⟨5981741, by rfl⟩ : syracuseStep 7975655 = 11963483) B11963483
theorem B3192247 : Blo 1104625 3192247 := bstep (se 1 (by rfl) ⟨2394185, by rfl⟩ : syracuseStep 3192247 = 4788371) B4788371
theorem B2799785 : Blo 1104625 2799785 := bstep (se 2 (by rfl) ⟨1049919, by rfl⟩ : syracuseStep 2799785 = 2099839) B2099839
theorem B4733147 : Blo 1104625 4733147 := bstep (se 1 (by rfl) ⟨3549860, by rfl⟩ : syracuseStep 4733147 = 7099721) B7099721
theorem B6306761 : Blo 1104625 6306761 := bstep (se 2 (by rfl) ⟨2365035, by rfl⟩ : syracuseStep 6306761 = 4730071) B4730071
theorem B21281939 : Blo 1104625 21281939 := bstep (se 1 (by rfl) ⟨15961454, by rfl⟩ : syracuseStep 21281939 = 31922909) B31922909
theorem B2801051 : Blo 1104625 2801051 := bstep (se 1 (by rfl) ⟨2100788, by rfl⟩ : syracuseStep 2801051 = 4201577) B4201577
theorem B2801263 : Blo 1104625 2801263 := bstep (se 1 (by rfl) ⟨2100947, by rfl⟩ : syracuseStep 2801263 = 4201895) B4201895
theorem B1262335 : Blo 1104625 1262335 := bstep (se 1 (by rfl) ⟨946751, by rfl⟩ : syracuseStep 1262335 = 1893503) B1893503
theorem B3884345 : Blo 1104625 3884345 := bstep (se 2 (by rfl) ⟨1456629, by rfl⟩ : syracuseStep 3884345 = 2913259) B2913259
theorem B15123773 : Blo 1104625 15123773 := bstep (se 3 (by rfl) ⟨2835707, by rfl⟩ : syracuseStep 15123773 = 5671415) B5671415
theorem B2803369 : Blo 1104625 2803369 := bstep (se 2 (by rfl) ⟨1051263, by rfl⟩ : syracuseStep 2803369 = 2102527) B2102527
theorem B8964179 : Blo 1104625 8964179 := bstep (se 1 (by rfl) ⟨6723134, by rfl⟩ : syracuseStep 8964179 = 13446269) B13446269
theorem B2803855 : Blo 1104625 2803855 := bstep (se 1 (by rfl) ⟨2102891, by rfl⟩ : syracuseStep 2803855 = 4205783) B4205783
theorem B2803967 : Blo 1104625 2803967 := bstep (se 1 (by rfl) ⟨2102975, by rfl⟩ : syracuseStep 2803967 = 4205951) B4205951
theorem B10242413 : Blo 1104625 10242413 := bstep (se 3 (by rfl) ⟨1920452, by rfl⟩ : syracuseStep 10242413 = 3840905) B3840905
theorem B1657703 : Blo 1104625 1657703 := bstep (se 1 (by rfl) ⟨1243277, by rfl⟩ : syracuseStep 1657703 = 2486555) B2486555
theorem B8408285 : Blo 1104625 8408285 := bstep (se 3 (by rfl) ⟨1576553, by rfl⟩ : syracuseStep 8408285 = 3153107) B3153107
theorem B1658087 : Blo 1104625 1658087 := bstep (se 1 (by rfl) ⟨1243565, by rfl⟩ : syracuseStep 1658087 = 2487131) B2487131
theorem B12602951 : Blo 1104625 12602951 := bstep (se 1 (by rfl) ⟨9452213, by rfl⟩ : syracuseStep 12602951 = 18904427) B18904427
theorem B1658873 : Blo 1104625 1658873 := bstep (se 2 (by rfl) ⟨622077, by rfl⟩ : syracuseStep 1658873 = 1244155) B1244155
theorem B1659113 : Blo 1104625 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B1659419 : Blo 1104625 1659419 := bstep (se 1 (by rfl) ⟨1244564, by rfl⟩ : syracuseStep 1659419 = 2489129) B2489129
theorem B10113599 : Blo 1104625 10113599 := bstep (se 1 (by rfl) ⟨7585199, by rfl⟩ : syracuseStep 10113599 = 15170399) B15170399
theorem B5395025 : Blo 1104625 5395025 := bstep (se 2 (by rfl) ⟨2023134, by rfl⟩ : syracuseStep 5395025 = 4046269) B4046269
theorem B1659611 : Blo 1104625 1659611 := bstep (se 1 (by rfl) ⟨1244708, by rfl⟩ : syracuseStep 1659611 = 2489417) B2489417
theorem B1660073 : Blo 1104625 1660073 := bstep (se 2 (by rfl) ⟨622527, by rfl⟩ : syracuseStep 1660073 = 1245055) B1245055
theorem B1660955 : Blo 1104625 1660955 := bstep (se 1 (by rfl) ⟨1245716, by rfl⟩ : syracuseStep 1660955 = 2491433) B2491433
theorem B1660991 : Blo 1104625 1660991 := bstep (se 1 (by rfl) ⟨1245743, by rfl⟩ : syracuseStep 1660991 = 2491487) B2491487
theorem B11950247 : Blo 1104625 11950247 := bstep (se 1 (by rfl) ⟨8962685, by rfl⟩ : syracuseStep 11950247 = 17925371) B17925371
theorem B1661111 : Blo 1104625 1661111 := bstep (se 1 (by rfl) ⟨1245833, by rfl⟩ : syracuseStep 1661111 = 2491667) B2491667
theorem B9460415 : Blo 1104625 9460415 := bstep (se 1 (by rfl) ⟨7095311, by rfl⟩ : syracuseStep 9460415 = 14190623) B14190623
theorem B275929811 : Blo 1104625 275929811 := bstep (se 1 (by rfl) ⟨206947358, by rfl⟩ : syracuseStep 275929811 = 413894717) B413894717
theorem B1104639 : Blo 1104625 1104639 := bstep (se 1 (by rfl) ⟨828479, by rfl⟩ : syracuseStep 1104639 = 1656959) B1656959
theorem B1104927 : Blo 1104625 1104927 := bstep (se 1 (by rfl) ⟨828695, by rfl⟩ : syracuseStep 1104927 = 1657391) B1657391
theorem B1662047 : Blo 1104625 1662047 := bstep (se 1 (by rfl) ⟨1246535, by rfl⟩ : syracuseStep 1662047 = 2493071) B2493071
theorem B1105007 : Blo 1104625 1105007 := bstep (se 1 (by rfl) ⟨828755, by rfl⟩ : syracuseStep 1105007 = 1657511) B1657511
theorem B1105051 : Blo 1104625 1105051 := bstep (se 1 (by rfl) ⟨828788, by rfl⟩ : syracuseStep 1105051 = 1657577) B1657577
theorem B1105087 : Blo 1104625 1105087 := bstep (se 1 (by rfl) ⟨828815, by rfl⟩ : syracuseStep 1105087 = 1657631) B1657631
theorem B5987519 : Blo 1104625 5987519 := bstep (se 1 (by rfl) ⟨4490639, by rfl⟩ : syracuseStep 5987519 = 8981279) B8981279
theorem B1662647 : Blo 1104625 1662647 := bstep (se 1 (by rfl) ⟨1246985, by rfl⟩ : syracuseStep 1662647 = 2493971) B2493971
theorem B1662695 : Blo 1104625 1662695 := bstep (se 1 (by rfl) ⟨1247021, by rfl⟩ : syracuseStep 1662695 = 2494043) B2494043
theorem B10084121 : Blo 1104625 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B1106663 : Blo 1104625 1106663 := bstep (se 1 (by rfl) ⟨829997, by rfl⟩ : syracuseStep 1106663 = 1659995) B1659995
theorem B1106683 : Blo 1104625 1106683 := bstep (se 1 (by rfl) ⟨830012, by rfl⟩ : syracuseStep 1106683 = 1660025) B1660025
theorem B5596127 : Blo 1104625 5596127 := bstep (se 1 (by rfl) ⟨4197095, by rfl⟩ : syracuseStep 5596127 = 8394191) B8394191
theorem B1106943 : Blo 1104625 1106943 := bstep (se 1 (by rfl) ⟨830207, by rfl⟩ : syracuseStep 1106943 = 1660415) B1660415
theorem B1107195 : Blo 1104625 1107195 := bstep (se 1 (by rfl) ⟨830396, by rfl⟩ : syracuseStep 1107195 = 1660793) B1660793
theorem B1107199 : Blo 1104625 1107199 := bstep (se 1 (by rfl) ⟨830399, by rfl⟩ : syracuseStep 1107199 = 1660799) B1660799
theorem B19195193 : Blo 1104625 19195193 := bstep (se 2 (by rfl) ⟨7198197, by rfl⟩ : syracuseStep 19195193 = 14396395) B14396395
theorem B23062067 : Blo 1104625 23062067 := bstep (se 1 (by rfl) ⟨17296550, by rfl⟩ : syracuseStep 23062067 = 34593101) B34593101
theorem B3728969 : Blo 1104625 3728969 := bstep (se 2 (by rfl) ⟨1398363, by rfl⟩ : syracuseStep 3728969 = 2796727) B2796727
theorem B1107711 : Blo 1104625 1107711 := bstep (se 1 (by rfl) ⟨830783, by rfl⟩ : syracuseStep 1107711 = 1661567) B1661567
theorem B1107803 : Blo 1104625 1107803 := bstep (se 1 (by rfl) ⟨830852, by rfl⟩ : syracuseStep 1107803 = 1661705) B1661705
theorem B1107963 : Blo 1104625 1107963 := bstep (se 1 (by rfl) ⟨830972, by rfl⟩ : syracuseStep 1107963 = 1661945) B1661945
theorem B1108175 : Blo 1104625 1108175 := bstep (se 1 (by rfl) ⟨831131, by rfl⟩ : syracuseStep 1108175 = 1662263) B1662263
theorem B1108295 : Blo 1104625 1108295 := bstep (se 1 (by rfl) ⟨831221, by rfl⟩ : syracuseStep 1108295 = 1662443) B1662443
theorem B3730427 : Blo 1104625 3730427 := bstep (se 1 (by rfl) ⟨2797820, by rfl⟩ : syracuseStep 3730427 = 5595641) B5595641
theorem B21294089 : Blo 1104625 21294089 := bstep (se 2 (by rfl) ⟨7985283, by rfl⟩ : syracuseStep 21294089 = 15970567) B15970567
theorem B5992015 : Blo 1104625 5992015 := bstep (se 1 (by rfl) ⟨4494011, by rfl⟩ : syracuseStep 5992015 = 8988023) B8988023
theorem B42594011 : Blo 1104625 42594011 := bstep (se 1 (by rfl) ⟨31945508, by rfl⟩ : syracuseStep 42594011 = 63891017) B63891017
theorem B3731399 : Blo 1104625 3731399 := bstep (se 1 (by rfl) ⟨2798549, by rfl⟩ : syracuseStep 3731399 = 5597099) B5597099
theorem B2486375 : Blo 1104625 2486375 := bstep (se 1 (by rfl) ⟨1864781, by rfl⟩ : syracuseStep 2486375 = 3729563) B3729563
theorem B5599367 : Blo 1104625 5599367 := bstep (se 1 (by rfl) ⟨4199525, by rfl⟩ : syracuseStep 5599367 = 8399051) B8399051
theorem B5599529 : Blo 1104625 5599529 := bstep (se 2 (by rfl) ⟨2099823, by rfl⟩ : syracuseStep 5599529 = 4199647) B4199647
theorem B51049349 : Blo 1104625 51049349 := bstep (se 4 (by rfl) ⟨4785876, by rfl⟩ : syracuseStep 51049349 = 9571753) B9571753
theorem B1996265 : Blo 1104625 1996265 := bstep (se 2 (by rfl) ⟨748599, by rfl⟩ : syracuseStep 1996265 = 1497199) B1497199
theorem B2487977 : Blo 1104625 2487977 := bstep (se 2 (by rfl) ⟨932991, by rfl⟩ : syracuseStep 2487977 = 1865983) B1865983
theorem B11958425 : Blo 1104625 11958425 := bstep (se 2 (by rfl) ⟨4484409, by rfl⟩ : syracuseStep 11958425 = 8968819) B8968819
theorem B1243615 : Blo 1104625 1243615 := bstep (se 1 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 1243615 = 1865423) B1865423
theorem B103512667 : Blo 1104625 103512667 := bstep (se 1 (by rfl) ⟨77634500, by rfl⟩ : syracuseStep 103512667 = 155269001) B155269001
theorem B2489039 : Blo 1104625 2489039 := bstep (se 1 (by rfl) ⟨1866779, by rfl⟩ : syracuseStep 2489039 = 3733559) B3733559
theorem B1244479 : Blo 1104625 1244479 := bstep (se 1 (by rfl) ⟨933359, by rfl⟩ : syracuseStep 1244479 = 1866719) B1866719
theorem B2490209 : Blo 1104625 2490209 := bstep (se 2 (by rfl) ⟨933828, by rfl⟩ : syracuseStep 2490209 = 1867657) B1867657
theorem B14155721 : Blo 1104625 14155721 := bstep (se 2 (by rfl) ⟨5308395, by rfl⟩ : syracuseStep 14155721 = 10616791) B10616791
theorem B2490335 : Blo 1104625 2490335 := bstep (se 1 (by rfl) ⟨1867751, by rfl⟩ : syracuseStep 2490335 = 3735503) B3735503
theorem B3735719 : Blo 1104625 3735719 := bstep (se 1 (by rfl) ⟨2801789, by rfl⟩ : syracuseStep 3735719 = 5603579) B5603579
theorem B5604065 : Blo 1104625 5604065 := bstep (se 2 (by rfl) ⟨2101524, by rfl⟩ : syracuseStep 5604065 = 4203049) B4203049
theorem B2589563 : Blo 1104625 2589563 := bstep (se 1 (by rfl) ⟨1942172, by rfl⟩ : syracuseStep 2589563 = 3884345) B3884345
theorem B8389817 : Blo 1104625 8389817 := bstep (se 2 (by rfl) ⟨3146181, by rfl⟩ : syracuseStep 8389817 = 6292363) B6292363
theorem B5047751 : Blo 1104625 5047751 := bstep (se 1 (by rfl) ⟨3785813, by rfl⟩ : syracuseStep 5047751 = 7571627) B7571627
theorem B62326219 : Blo 1104625 62326219 := bstep (se 1 (by rfl) ⟨46744664, by rfl⟩ : syracuseStep 62326219 = 93489329) B93489329
theorem B1869311 : Blo 1104625 1869311 := bstep (se 1 (by rfl) ⟨1401983, by rfl⟩ : syracuseStep 1869311 = 2803967) B2803967
theorem B26969597 : Blo 1104625 26969597 := bstep (se 3 (by rfl) ⟨5056799, by rfl⟩ : syracuseStep 26969597 = 10113599) B10113599
theorem B2492297 : Blo 1104625 2492297 := bstep (se 2 (by rfl) ⟨934611, by rfl⟩ : syracuseStep 2492297 = 1869223) B1869223
theorem B5605523 : Blo 1104625 5605523 := bstep (se 1 (by rfl) ⟨4204142, by rfl⟩ : syracuseStep 5605523 = 8408285) B8408285
theorem B3737825 : Blo 1104625 3737825 := bstep (se 2 (by rfl) ⟨1401684, by rfl⟩ : syracuseStep 3737825 = 2803369) B2803369
theorem B3148415 : Blo 1104625 3148415 := bstep (se 1 (by rfl) ⟨2361311, by rfl⟩ : syracuseStep 3148415 = 4722623) B4722623
theorem B34048673 : Blo 1104625 34048673 := bstep (se 2 (by rfl) ⟨12768252, by rfl⟩ : syracuseStep 34048673 = 25536505) B25536505
theorem B2362063 : Blo 1104625 2362063 := bstep (se 1 (by rfl) ⟨1771547, by rfl⟩ : syracuseStep 2362063 = 3543095) B3543095
theorem B3738473 : Blo 1104625 3738473 := bstep (se 2 (by rfl) ⟨1401927, by rfl⟩ : syracuseStep 3738473 = 2803855) B2803855
theorem B2100431 : Blo 1104625 2100431 := bstep (se 1 (by rfl) ⟨1575323, by rfl⟩ : syracuseStep 2100431 = 3150647) B3150647
theorem B4197689 : Blo 1104625 4197689 := bstep (se 2 (by rfl) ⟨1574133, by rfl⟩ : syracuseStep 4197689 = 3148267) B3148267
theorem B2493863 : Blo 1104625 2493863 := bstep (se 1 (by rfl) ⟨1870397, by rfl⟩ : syracuseStep 2493863 = 3740795) B3740795
theorem B3149599 : Blo 1104625 3149599 := bstep (se 1 (by rfl) ⟨2362199, by rfl⟩ : syracuseStep 3149599 = 4724399) B4724399
theorem B7966831 : Blo 1104625 7966831 := bstep (se 1 (by rfl) ⟨5975123, by rfl⟩ : syracuseStep 7966831 = 11950247) B11950247
theorem B3543659 : Blo 1104625 3543659 := bstep (se 1 (by rfl) ⟨2657744, by rfl⟩ : syracuseStep 3543659 = 5315489) B5315489
theorem B2102375 : Blo 1104625 2102375 := bstep (se 1 (by rfl) ⟨1576781, by rfl⟩ : syracuseStep 2102375 = 3153563) B3153563
theorem B6722747 : Blo 1104625 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B2102831 : Blo 1104625 2102831 := bstep (se 1 (by rfl) ⟨1577123, by rfl⟩ : syracuseStep 2102831 = 3154247) B3154247
theorem B1775719 : Blo 1104625 1775719 := bstep (se 1 (by rfl) ⟨1331789, by rfl⟩ : syracuseStep 1775719 = 2663579) B2663579
theorem B7575761 : Blo 1104625 7575761 := bstep (se 2 (by rfl) ⟨2840910, by rfl⟩ : syracuseStep 7575761 = 5681821) B5681821
theorem B15374711 : Blo 1104625 15374711 := bstep (se 1 (by rfl) ⟨11531033, by rfl⟩ : syracuseStep 15374711 = 23062067) B23062067
theorem B6298013 : Blo 1104625 6298013 := bstep (se 3 (by rfl) ⟨1180877, by rfl⟩ : syracuseStep 6298013 = 2361755) B2361755
theorem B4791143 : Blo 1104625 4791143 := bstep (se 1 (by rfl) ⟨3593357, by rfl⟩ : syracuseStep 4791143 = 7186715) B7186715
theorem B14196059 : Blo 1104625 14196059 := bstep (se 1 (by rfl) ⟨10647044, by rfl⟩ : syracuseStep 14196059 = 21294089) B21294089
theorem B3547273 : Blo 1104625 3547273 := bstep (se 2 (by rfl) ⟨1330227, by rfl⟩ : syracuseStep 3547273 = 2660455) B2660455
theorem B5317103 : Blo 1104625 5317103 := bstep (se 1 (by rfl) ⟨3987827, by rfl⟩ : syracuseStep 5317103 = 7975655) B7975655
theorem B7971821 : Blo 1104625 7971821 := bstep (se 3 (by rfl) ⟨1494716, by rfl⟩ : syracuseStep 7971821 = 2989433) B2989433
theorem B7972283 : Blo 1104625 7972283 := bstep (se 1 (by rfl) ⟨5979212, by rfl⟩ : syracuseStep 7972283 = 11958425) B11958425
theorem B3155431 : Blo 1104625 3155431 := bstep (se 1 (by rfl) ⟨2366573, by rfl⟩ : syracuseStep 3155431 = 4733147) B4733147
theorem B4204507 : Blo 1104625 4204507 := bstep (se 1 (by rfl) ⟨3153380, by rfl⟩ : syracuseStep 4204507 = 6306761) B6306761
theorem B7973437 : Blo 1104625 7973437 := bstep (se 3 (by rfl) ⟨1495019, by rfl⟩ : syracuseStep 7973437 = 2990039) B2990039
theorem B31960271 : Blo 1104625 31960271 := bstep (se 1 (by rfl) ⟨23970203, by rfl⟩ : syracuseStep 31960271 = 47940407) B47940407
theorem B1683113 : Blo 1104625 1683113 := bstep (se 2 (by rfl) ⟨631167, by rfl⟩ : syracuseStep 1683113 = 1262335) B1262335
theorem B5976119 : Blo 1104625 5976119 := bstep (se 1 (by rfl) ⟨4482089, by rfl⟩ : syracuseStep 5976119 = 8964179) B8964179
theorem B6828275 : Blo 1104625 6828275 := bstep (se 1 (by rfl) ⟨5121206, by rfl⟩ : syracuseStep 6828275 = 10242413) B10242413
theorem B8401967 : Blo 1104625 8401967 := bstep (se 1 (by rfl) ⟨6301475, by rfl⟩ : syracuseStep 8401967 = 12602951) B12602951
theorem B2799967 : Blo 1104625 2799967 := bstep (se 1 (by rfl) ⟨2099975, by rfl⟩ : syracuseStep 2799967 = 4199951) B4199951
theorem B17021339 : Blo 1104625 17021339 := bstep (se 1 (by rfl) ⟨12766004, by rfl⟩ : syracuseStep 17021339 = 25532009) B25532009
theorem B18921923 : Blo 1104625 18921923 := bstep (se 1 (by rfl) ⟨14191442, by rfl⟩ : syracuseStep 18921923 = 28382885) B28382885
theorem B6306943 : Blo 1104625 6306943 := bstep (se 1 (by rfl) ⟨4730207, by rfl⟩ : syracuseStep 6306943 = 9460415) B9460415
theorem B2801567 : Blo 1104625 2801567 := bstep (se 1 (by rfl) ⟨2101175, by rfl⟩ : syracuseStep 2801567 = 4202351) B4202351
theorem B12796795 : Blo 1104625 12796795 := bstep (se 1 (by rfl) ⟨9597596, by rfl⟩ : syracuseStep 12796795 = 19195193) B19195193
theorem B28396007 : Blo 1104625 28396007 := bstep (se 1 (by rfl) ⟨21297005, by rfl⟩ : syracuseStep 28396007 = 42594011) B42594011
theorem B1657583 : Blo 1104625 1657583 := bstep (se 1 (by rfl) ⟨1243187, by rfl⟩ : syracuseStep 1657583 = 2486375) B2486375
theorem B34032899 : Blo 1104625 34032899 := bstep (se 1 (by rfl) ⟨25524674, by rfl⟩ : syracuseStep 34032899 = 51049349) B51049349
theorem B1658153 : Blo 1104625 1658153 := bstep (se 2 (by rfl) ⟨621807, by rfl⟩ : syracuseStep 1658153 = 1243615) B1243615
theorem B1330843 : Blo 1104625 1330843 := bstep (se 1 (by rfl) ⟨998132, by rfl⟩ : syracuseStep 1330843 = 1996265) B1996265
theorem B1658651 : Blo 1104625 1658651 := bstep (se 1 (by rfl) ⟨1243988, by rfl⟩ : syracuseStep 1658651 = 2487977) B2487977
theorem B1659305 : Blo 1104625 1659305 := bstep (se 2 (by rfl) ⟨622239, by rfl⟩ : syracuseStep 1659305 = 1244479) B1244479
theorem B1659359 : Blo 1104625 1659359 := bstep (se 1 (by rfl) ⟨1244519, by rfl⟩ : syracuseStep 1659359 = 2489039) B2489039
theorem B1660139 : Blo 1104625 1660139 := bstep (se 1 (by rfl) ⟨1245104, by rfl⟩ : syracuseStep 1660139 = 2490209) B2490209
theorem B1660223 : Blo 1104625 1660223 := bstep (se 1 (by rfl) ⟨1245167, by rfl⟩ : syracuseStep 1660223 = 2490335) B2490335
theorem B1660367 : Blo 1104625 1660367 := bstep (se 1 (by rfl) ⟨1245275, by rfl⟩ : syracuseStep 1660367 = 2490551) B2490551
theorem B1660523 : Blo 1104625 1660523 := bstep (se 1 (by rfl) ⟨1245392, by rfl⟩ : syracuseStep 1660523 = 2490785) B2490785
theorem B17061779 : Blo 1104625 17061779 := bstep (se 1 (by rfl) ⟨12796334, by rfl⟩ : syracuseStep 17061779 = 25592669) B25592669
theorem B10082515 : Blo 1104625 10082515 := bstep (se 1 (by rfl) ⟨7561886, by rfl⟩ : syracuseStep 10082515 = 15123773) B15123773
theorem B12605867 : Blo 1104625 12605867 := bstep (se 1 (by rfl) ⟨9454400, by rfl⟩ : syracuseStep 12605867 = 18908801) B18908801
theorem B5594183 : Blo 1104625 5594183 := bstep (se 1 (by rfl) ⟨4195637, by rfl⟩ : syracuseStep 5594183 = 8391275) B8391275
theorem B1662089 : Blo 1104625 1662089 := bstep (se 2 (by rfl) ⟨623283, by rfl⟩ : syracuseStep 1662089 = 1246567) B1246567
theorem B1662107 : Blo 1104625 1662107 := bstep (se 1 (by rfl) ⟨1246580, by rfl⟩ : syracuseStep 1662107 = 2493161) B2493161
theorem B1662143 : Blo 1104625 1662143 := bstep (se 1 (by rfl) ⟨1246607, by rfl⟩ : syracuseStep 1662143 = 2493215) B2493215
theorem B1105135 : Blo 1104625 1105135 := bstep (se 1 (by rfl) ⟨828851, by rfl⟩ : syracuseStep 1105135 = 1657703) B1657703
theorem B1662191 : Blo 1104625 1662191 := bstep (se 1 (by rfl) ⟨1246643, by rfl⟩ : syracuseStep 1662191 = 2493287) B2493287
theorem B1105391 : Blo 1104625 1105391 := bstep (se 1 (by rfl) ⟨829043, by rfl⟩ : syracuseStep 1105391 = 1658087) B1658087
theorem B1105915 : Blo 1104625 1105915 := bstep (se 1 (by rfl) ⟨829436, by rfl⟩ : syracuseStep 1105915 = 1658873) B1658873
theorem B1106075 : Blo 1104625 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B6381821 : Blo 1104625 6381821 := bstep (se 3 (by rfl) ⟨1196591, by rfl⟩ : syracuseStep 6381821 = 2393183) B2393183
theorem B1106279 : Blo 1104625 1106279 := bstep (se 1 (by rfl) ⟨829709, by rfl⟩ : syracuseStep 1106279 = 1659419) B1659419
theorem B3596683 : Blo 1104625 3596683 := bstep (se 1 (by rfl) ⟨2697512, by rfl⟩ : syracuseStep 3596683 = 5395025) B5395025
theorem B73884089 : Blo 1104625 73884089 := bstep (se 2 (by rfl) ⟨27706533, by rfl⟩ : syracuseStep 73884089 = 55413067) B55413067
theorem B1106407 : Blo 1104625 1106407 := bstep (se 1 (by rfl) ⟨829805, by rfl⟩ : syracuseStep 1106407 = 1659611) B1659611
theorem B1106715 : Blo 1104625 1106715 := bstep (se 1 (by rfl) ⟨830036, by rfl⟩ : syracuseStep 1106715 = 1660073) B1660073
theorem B1107303 : Blo 1104625 1107303 := bstep (se 1 (by rfl) ⟨830477, by rfl⟩ : syracuseStep 1107303 = 1660955) B1660955
theorem B1107327 : Blo 1104625 1107327 := bstep (se 1 (by rfl) ⟨830495, by rfl⟩ : syracuseStep 1107327 = 1660991) B1660991
theorem B1107407 : Blo 1104625 1107407 := bstep (se 1 (by rfl) ⟨830555, by rfl⟩ : syracuseStep 1107407 = 1661111) B1661111
theorem B5596775 : Blo 1104625 5596775 := bstep (se 1 (by rfl) ⟨4197581, by rfl⟩ : syracuseStep 5596775 = 8395163) B8395163
theorem B183953207 : Blo 1104625 183953207 := bstep (se 1 (by rfl) ⟨137964905, by rfl⟩ : syracuseStep 183953207 = 275929811) B275929811
theorem B1992559 : Blo 1104625 1992559 := bstep (se 1 (by rfl) ⟨1494419, by rfl⟩ : syracuseStep 1992559 = 2988839) B2988839
theorem B1108031 : Blo 1104625 1108031 := bstep (se 1 (by rfl) ⟨831023, by rfl⟩ : syracuseStep 1108031 = 1662047) B1662047
theorem B7989353 : Blo 1104625 7989353 := bstep (se 2 (by rfl) ⟨2996007, by rfl⟩ : syracuseStep 7989353 = 5992015) B5992015
theorem B3991679 : Blo 1104625 3991679 := bstep (se 1 (by rfl) ⟨2993759, by rfl⟩ : syracuseStep 3991679 = 5987519) B5987519
theorem B1108431 : Blo 1104625 1108431 := bstep (se 1 (by rfl) ⟨831323, by rfl⟩ : syracuseStep 1108431 = 1662647) B1662647
theorem B30239201 : Blo 1104625 30239201 := bstep (se 2 (by rfl) ⟨11339700, by rfl⟩ : syracuseStep 30239201 = 22679401) B22679401
theorem B1108463 : Blo 1104625 1108463 := bstep (se 1 (by rfl) ⟨831347, by rfl⟩ : syracuseStep 1108463 = 1662695) B1662695
theorem B245164529 : Blo 1104625 245164529 := bstep (se 2 (by rfl) ⟨91936698, by rfl⟩ : syracuseStep 245164529 = 183873397) B183873397
theorem B3730751 : Blo 1104625 3730751 := bstep (se 1 (by rfl) ⟨2798063, by rfl⟩ : syracuseStep 3730751 = 5596127) B5596127
theorem B2485979 : Blo 1104625 2485979 := bstep (se 1 (by rfl) ⟨1864484, by rfl⟩ : syracuseStep 2485979 = 3728969) B3728969
theorem B31879079 : Blo 1104625 31879079 := bstep (se 1 (by rfl) ⟨23909309, by rfl⟩ : syracuseStep 31879079 = 47818619) B47818619
theorem B7565251 : Blo 1104625 7565251 := bstep (se 1 (by rfl) ⟨5673938, by rfl⟩ : syracuseStep 7565251 = 11347877) B11347877
theorem B4256329 : Blo 1104625 4256329 := bstep (se 2 (by rfl) ⟨1596123, by rfl⟩ : syracuseStep 4256329 = 3192247) B3192247
theorem B2486951 : Blo 1104625 2486951 := bstep (se 1 (by rfl) ⟨1865213, by rfl⟩ : syracuseStep 2486951 = 3730427) B3730427
theorem B4485851 : Blo 1104625 4485851 := bstep (se 1 (by rfl) ⟨3364388, by rfl⟩ : syracuseStep 4485851 = 6728777) B6728777
theorem B1864687 : Blo 1104625 1864687 := bstep (se 1 (by rfl) ⟨1398515, by rfl⟩ : syracuseStep 1864687 = 2797031) B2797031
theorem B2487599 : Blo 1104625 2487599 := bstep (se 1 (by rfl) ⟨1865699, by rfl⟩ : syracuseStep 2487599 = 3731399) B3731399
theorem B3732911 : Blo 1104625 3732911 := bstep (se 1 (by rfl) ⟨2799683, by rfl⟩ : syracuseStep 3732911 = 5599367) B5599367
theorem B1865207 : Blo 1104625 1865207 := bstep (se 1 (by rfl) ⟨1398905, by rfl⟩ : syracuseStep 1865207 = 2797811) B2797811
theorem B3733019 : Blo 1104625 3733019 := bstep (se 1 (by rfl) ⟨2799764, by rfl⟩ : syracuseStep 3733019 = 5599529) B5599529
theorem B138016889 : Blo 1104625 138016889 := bstep (se 2 (by rfl) ⟨51756333, by rfl⟩ : syracuseStep 138016889 = 103512667) B103512667
theorem B1866523 : Blo 1104625 1866523 := bstep (se 1 (by rfl) ⟨1399892, by rfl⟩ : syracuseStep 1866523 = 2799785) B2799785
theorem B14187959 : Blo 1104625 14187959 := bstep (se 1 (by rfl) ⟨10640969, by rfl⟩ : syracuseStep 14187959 = 21281939) B21281939
theorem B3735017 : Blo 1104625 3735017 := bstep (se 2 (by rfl) ⟨1400631, by rfl⟩ : syracuseStep 3735017 = 2801263) B2801263
theorem B1867367 : Blo 1104625 1867367 := bstep (se 1 (by rfl) ⟨1400525, by rfl⟩ : syracuseStep 1867367 = 2801051) B2801051
theorem B9437147 : Blo 1104625 9437147 := bstep (se 1 (by rfl) ⟨7077860, by rfl⟩ : syracuseStep 9437147 = 14155721) B14155721
theorem B2490479 : Blo 1104625 2490479 := bstep (se 1 (by rfl) ⟨1867859, by rfl⟩ : syracuseStep 2490479 = 3735719) B3735719
theorem B3736043 : Blo 1104625 3736043 := bstep (se 1 (by rfl) ⟨2802032, by rfl⟩ : syracuseStep 3736043 = 5604065) B5604065
theorem B1246207 : Blo 1104625 1246207 := bstep (se 1 (by rfl) ⟨934655, by rfl⟩ : syracuseStep 1246207 = 1869311) B1869311
theorem B3737015 : Blo 1104625 3737015 := bstep (se 1 (by rfl) ⟨2802761, by rfl⟩ : syracuseStep 3737015 = 5605523) B5605523
theorem B2491883 : Blo 1104625 2491883 := bstep (se 1 (by rfl) ⟨1868912, by rfl⟩ : syracuseStep 2491883 = 3737825) B3737825
theorem B2098943 : Blo 1104625 2098943 := bstep (se 1 (by rfl) ⟨1574207, by rfl⟩ : syracuseStep 2098943 = 3148415) B3148415
theorem B2492315 : Blo 1104625 2492315 := bstep (se 1 (by rfl) ⟨1869236, by rfl⟩ : syracuseStep 2492315 = 3738473) B3738473
theorem B83101625 : Blo 1104625 83101625 := bstep (se 2 (by rfl) ⟨31163109, by rfl⟩ : syracuseStep 83101625 = 62326219) B62326219
theorem B2656745 : Blo 1104625 2656745 := bstep (se 2 (by rfl) ⟨996279, by rfl⟩ : syracuseStep 2656745 = 1992559) B1992559
theorem B5606009 : Blo 1104625 5606009 := bstep (se 2 (by rfl) ⟨2102253, by rfl⟩ : syracuseStep 5606009 = 4204507) B4204507
theorem B5606333 : Blo 1104625 5606333 := bstep (se 3 (by rfl) ⟨1051187, by rfl⟩ : syracuseStep 5606333 = 2102375) B2102375
theorem B2362439 : Blo 1104625 2362439 := bstep (se 1 (by rfl) ⟨1771829, by rfl⟩ : syracuseStep 2362439 = 3543659) B3543659
theorem B3149417 : Blo 1104625 3149417 := bstep (se 2 (by rfl) ⟨1181031, by rfl⟩ : syracuseStep 3149417 = 2362063) B2362063
theorem B11374519 : Blo 1104625 11374519 := bstep (se 1 (by rfl) ⟨8530889, by rfl⟩ : syracuseStep 11374519 = 17061779) B17061779
theorem B5050507 : Blo 1104625 5050507 := bstep (se 1 (by rfl) ⟨3787880, by rfl⟩ : syracuseStep 5050507 = 7575761) B7575761
theorem B4198675 : Blo 1104625 4198675 := bstep (se 1 (by rfl) ⟨3149006, by rfl⟩ : syracuseStep 4198675 = 6298013) B6298013
theorem B1774457 : Blo 1104625 1774457 := bstep (se 2 (by rfl) ⟨665421, by rfl⟩ : syracuseStep 1774457 = 1330843) B1330843
theorem B4199465 : Blo 1104625 4199465 := bstep (se 2 (by rfl) ⟨1574799, by rfl⟩ : syracuseStep 4199465 = 3149599) B3149599
theorem B10622441 : Blo 1104625 10622441 := bstep (se 2 (by rfl) ⟨3983415, by rfl⟩ : syracuseStep 10622441 = 7966831) B7966831
theorem B49256059 : Blo 1104625 49256059 := bstep (se 1 (by rfl) ⟨36942044, by rfl⟩ : syracuseStep 49256059 = 73884089) B73884089
theorem B3544735 : Blo 1104625 3544735 := bstep (se 1 (by rfl) ⟨2658551, by rfl⟩ : syracuseStep 3544735 = 5317103) B5317103
theorem B5314547 : Blo 1104625 5314547 := bstep (se 1 (by rfl) ⟨3985910, by rfl⟩ : syracuseStep 5314547 = 7971821) B7971821
theorem B5675105 : Blo 1104625 5675105 := bstep (se 2 (by rfl) ⟨2128164, by rfl⟩ : syracuseStep 5675105 = 4256329) B4256329
theorem B5314855 : Blo 1104625 5314855 := bstep (se 1 (by rfl) ⟨3986141, by rfl⟩ : syracuseStep 5314855 = 7972283) B7972283
theorem B40999229 : Blo 1104625 40999229 := bstep (se 3 (by rfl) ⟨7687355, by rfl⟩ : syracuseStep 40999229 = 15374711) B15374711
theorem B2661119 : Blo 1104625 2661119 := bstep (se 1 (by rfl) ⟨1995839, by rfl⟩ : syracuseStep 2661119 = 3991679) B3991679
theorem B21306847 : Blo 1104625 21306847 := bstep (se 1 (by rfl) ⟨15980135, by rfl⟩ : syracuseStep 21306847 = 31960271) B31960271
theorem B2367625 : Blo 1104625 2367625 := bstep (se 2 (by rfl) ⟨887859, by rfl⟩ : syracuseStep 2367625 = 1775719) B1775719
theorem B13443353 : Blo 1104625 13443353 := bstep (se 2 (by rfl) ⟨5041257, by rfl⟩ : syracuseStep 13443353 = 10082515) B10082515
theorem B2990567 : Blo 1104625 2990567 := bstep (se 1 (by rfl) ⟨2242925, by rfl⟩ : syracuseStep 2990567 = 4485851) B4485851
theorem B11347559 : Blo 1104625 11347559 := bstep (se 1 (by rfl) ⟨8510669, by rfl⟩ : syracuseStep 11347559 = 17021339) B17021339
theorem B4729697 : Blo 1104625 4729697 := bstep (se 2 (by rfl) ⟨1773636, by rfl⟩ : syracuseStep 4729697 = 3547273) B3547273
theorem B4795577 : Blo 1104625 4795577 := bstep (se 2 (by rfl) ⟨1798341, by rfl⟩ : syracuseStep 4795577 = 3596683) B3596683
theorem B4207241 : Blo 1104625 4207241 := bstep (se 2 (by rfl) ⟨1577715, by rfl⟩ : syracuseStep 4207241 = 3155431) B3155431
theorem B22688599 : Blo 1104625 22688599 := bstep (se 1 (by rfl) ⟨17016449, by rfl⟩ : syracuseStep 22688599 = 34032899) B34032899
theorem B2798459 : Blo 1104625 2798459 := bstep (se 1 (by rfl) ⟨2098844, by rfl⟩ : syracuseStep 2798459 = 4197689) B4197689
theorem B10631249 : Blo 1104625 10631249 := bstep (se 2 (by rfl) ⟨3986718, by rfl⟩ : syracuseStep 10631249 = 7973437) B7973437
theorem B8403911 : Blo 1104625 8403911 := bstep (se 1 (by rfl) ⟨6302933, by rfl⟩ : syracuseStep 8403911 = 12605867) B12605867
theorem B3194095 : Blo 1104625 3194095 := bstep (se 1 (by rfl) ⟨2395571, by rfl⟩ : syracuseStep 3194095 = 4791143) B4791143
theorem B122635471 : Blo 1104625 122635471 := bstep (se 1 (by rfl) ⟨91976603, by rfl⟩ : syracuseStep 122635471 = 183953207) B183953207
theorem B5326235 : Blo 1104625 5326235 := bstep (se 1 (by rfl) ⟨3994676, by rfl⟩ : syracuseStep 5326235 = 7989353) B7989353
theorem B1657319 : Blo 1104625 1657319 := bstep (se 1 (by rfl) ⟨1242989, by rfl⟩ : syracuseStep 1657319 = 2485979) B2485979
theorem B21252719 : Blo 1104625 21252719 := bstep (se 1 (by rfl) ⟨15939539, by rfl⟩ : syracuseStep 21252719 = 31879079) B31879079
theorem B3984079 : Blo 1104625 3984079 := bstep (se 1 (by rfl) ⟨2988059, by rfl⟩ : syracuseStep 3984079 = 5976119) B5976119
theorem B1657967 : Blo 1104625 1657967 := bstep (se 1 (by rfl) ⟨1243475, by rfl⟩ : syracuseStep 1657967 = 2486951) B2486951
theorem B1658399 : Blo 1104625 1658399 := bstep (se 1 (by rfl) ⟨1243799, by rfl⟩ : syracuseStep 1658399 = 2487599) B2487599
theorem B8409257 : Blo 1104625 8409257 := bstep (se 2 (by rfl) ⟨3153471, by rfl⟩ : syracuseStep 8409257 = 6306943) B6306943
theorem B9458639 : Blo 1104625 9458639 := bstep (se 1 (by rfl) ⟨7093979, by rfl⟩ : syracuseStep 9458639 = 14187959) B14187959
theorem B1726375 : Blo 1104625 1726375 := bstep (se 1 (by rfl) ⟨1294781, by rfl⟩ : syracuseStep 1726375 = 2589563) B2589563
theorem B5593211 : Blo 1104625 5593211 := bstep (se 1 (by rfl) ⟨4194908, by rfl⟩ : syracuseStep 5593211 = 8389817) B8389817
theorem B3365167 : Blo 1104625 3365167 := bstep (se 1 (by rfl) ⟨2523875, by rfl⟩ : syracuseStep 3365167 = 5047751) B5047751
theorem B17979731 : Blo 1104625 17979731 := bstep (se 1 (by rfl) ⟨13484798, by rfl⟩ : syracuseStep 17979731 = 26969597) B26969597
theorem B1661531 : Blo 1104625 1661531 := bstep (se 1 (by rfl) ⟨1246148, by rfl⟩ : syracuseStep 1661531 = 2492297) B2492297
theorem B18930671 : Blo 1104625 18930671 := bstep (se 1 (by rfl) ⟨14198003, by rfl⟩ : syracuseStep 18930671 = 28396007) B28396007
theorem B22699115 : Blo 1104625 22699115 := bstep (se 1 (by rfl) ⟨17024336, by rfl⟩ : syracuseStep 22699115 = 34048673) B34048673
theorem B1105055 : Blo 1104625 1105055 := bstep (se 1 (by rfl) ⟨828791, by rfl⟩ : syracuseStep 1105055 = 1657583) B1657583
theorem B1105435 : Blo 1104625 1105435 := bstep (se 1 (by rfl) ⟨829076, by rfl⟩ : syracuseStep 1105435 = 1658153) B1658153
theorem B1662575 : Blo 1104625 1662575 := bstep (se 1 (by rfl) ⟨1246931, by rfl⟩ : syracuseStep 1662575 = 2493863) B2493863
theorem B1105767 : Blo 1104625 1105767 := bstep (se 1 (by rfl) ⟨829325, by rfl⟩ : syracuseStep 1105767 = 1658651) B1658651
theorem B1106203 : Blo 1104625 1106203 := bstep (se 1 (by rfl) ⟨829652, by rfl⟩ : syracuseStep 1106203 = 1659305) B1659305
theorem B1106239 : Blo 1104625 1106239 := bstep (se 1 (by rfl) ⟨829679, by rfl⟩ : syracuseStep 1106239 = 1659359) B1659359
theorem B4481831 : Blo 1104625 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B1106759 : Blo 1104625 1106759 := bstep (se 1 (by rfl) ⟨830069, by rfl⟩ : syracuseStep 1106759 = 1660139) B1660139
theorem B1106815 : Blo 1104625 1106815 := bstep (se 1 (by rfl) ⟨830111, by rfl⟩ : syracuseStep 1106815 = 1660223) B1660223
theorem B1106911 : Blo 1104625 1106911 := bstep (se 1 (by rfl) ⟨830183, by rfl⟩ : syracuseStep 1106911 = 1660367) B1660367
theorem B1401887 : Blo 1104625 1401887 := bstep (se 1 (by rfl) ⟨1051415, by rfl⟩ : syracuseStep 1401887 = 2102831) B2102831
theorem B1107015 : Blo 1104625 1107015 := bstep (se 1 (by rfl) ⟨830261, by rfl⟩ : syracuseStep 1107015 = 1660523) B1660523
theorem B68249573 : Blo 1104625 68249573 := bstep (se 4 (by rfl) ⟨6398397, by rfl⟩ : syracuseStep 68249573 = 12796795) B12796795
theorem B3729455 : Blo 1104625 3729455 := bstep (se 1 (by rfl) ⟨2797091, by rfl⟩ : syracuseStep 3729455 = 5594183) B5594183
theorem B1108059 : Blo 1104625 1108059 := bstep (se 1 (by rfl) ⟨831044, by rfl⟩ : syracuseStep 1108059 = 1662089) B1662089
theorem B1108071 : Blo 1104625 1108071 := bstep (se 1 (by rfl) ⟨831053, by rfl⟩ : syracuseStep 1108071 = 1662107) B1662107
theorem B1108095 : Blo 1104625 1108095 := bstep (se 1 (by rfl) ⟨831071, by rfl⟩ : syracuseStep 1108095 = 1662143) B1662143
theorem B1108127 : Blo 1104625 1108127 := bstep (se 1 (by rfl) ⟨831095, by rfl⟩ : syracuseStep 1108127 = 1662191) B1662191
theorem B9464039 : Blo 1104625 9464039 := bstep (se 1 (by rfl) ⟨7098029, by rfl⟩ : syracuseStep 9464039 = 14196059) B14196059
theorem B10087001 : Blo 1104625 10087001 := bstep (se 2 (by rfl) ⟨3782625, by rfl⟩ : syracuseStep 10087001 = 7565251) B7565251
theorem B4254547 : Blo 1104625 4254547 := bstep (se 1 (by rfl) ⟨3190910, by rfl⟩ : syracuseStep 4254547 = 6381821) B6381821
theorem B3731183 : Blo 1104625 3731183 := bstep (se 1 (by rfl) ⟨2798387, by rfl⟩ : syracuseStep 3731183 = 5596775) B5596775
theorem B80637869 : Blo 1104625 80637869 := bstep (se 3 (by rfl) ⟨15119600, by rfl⟩ : syracuseStep 80637869 = 30239201) B30239201
theorem B2486249 : Blo 1104625 2486249 := bstep (se 2 (by rfl) ⟨932343, by rfl⟩ : syracuseStep 2486249 = 1864687) B1864687
theorem B163443019 : Blo 1104625 163443019 := bstep (se 1 (by rfl) ⟨122582264, by rfl⟩ : syracuseStep 163443019 = 245164529) B245164529
theorem B2487167 : Blo 1104625 2487167 := bstep (se 1 (by rfl) ⟨1865375, by rfl⟩ : syracuseStep 2487167 = 3730751) B3730751
theorem B4552183 : Blo 1104625 4552183 := bstep (se 1 (by rfl) ⟨3414137, by rfl⟩ : syracuseStep 4552183 = 6828275) B6828275
theorem B3733289 : Blo 1104625 3733289 := bstep (se 2 (by rfl) ⟨1399983, by rfl⟩ : syracuseStep 3733289 = 2799967) B2799967
theorem B5601149 : Blo 1104625 5601149 := bstep (se 3 (by rfl) ⟨1050215, by rfl⟩ : syracuseStep 5601149 = 2100431) B2100431
theorem B5601311 : Blo 1104625 5601311 := bstep (se 1 (by rfl) ⟨4200983, by rfl⟩ : syracuseStep 5601311 = 8401967) B8401967
theorem B2488607 : Blo 1104625 2488607 := bstep (se 1 (by rfl) ⟨1866455, by rfl⟩ : syracuseStep 2488607 = 3732911) B3732911
theorem B1243471 : Blo 1104625 1243471 := bstep (se 1 (by rfl) ⟨932603, by rfl⟩ : syracuseStep 1243471 = 1865207) B1865207
theorem B2488679 : Blo 1104625 2488679 := bstep (se 1 (by rfl) ⟨1866509, by rfl⟩ : syracuseStep 2488679 = 3733019) B3733019
theorem B2488697 : Blo 1104625 2488697 := bstep (se 2 (by rfl) ⟨933261, by rfl⟩ : syracuseStep 2488697 = 1866523) B1866523
theorem B92011259 : Blo 1104625 92011259 := bstep (se 1 (by rfl) ⟨69008444, by rfl⟩ : syracuseStep 92011259 = 138016889) B138016889
theorem B12614615 : Blo 1104625 12614615 := bstep (se 1 (by rfl) ⟨9460961, by rfl⟩ : syracuseStep 12614615 = 18921923) B18921923
theorem B4488301 : Blo 1104625 4488301 := bstep (se 3 (by rfl) ⟨841556, by rfl⟩ : syracuseStep 4488301 = 1683113) B1683113
theorem B2490011 : Blo 1104625 2490011 := bstep (se 1 (by rfl) ⟨1867508, by rfl⟩ : syracuseStep 2490011 = 3735017) B3735017
theorem B1244911 : Blo 1104625 1244911 := bstep (se 1 (by rfl) ⟨933683, by rfl⟩ : syracuseStep 1244911 = 1867367) B1867367
theorem B1867711 : Blo 1104625 1867711 := bstep (se 1 (by rfl) ⟨1400783, by rfl⟩ : syracuseStep 1867711 = 2801567) B2801567
theorem B6291431 : Blo 1104625 6291431 := bstep (se 1 (by rfl) ⟨4718573, by rfl⟩ : syracuseStep 6291431 = 9437147) B9437147
theorem B2490695 : Blo 1104625 2490695 := bstep (se 1 (by rfl) ⟨1868021, by rfl⟩ : syracuseStep 2490695 = 3736043) B3736043
theorem B2491343 : Blo 1104625 2491343 := bstep (se 1 (by rfl) ⟨1868507, by rfl⟩ : syracuseStep 2491343 = 3737015) B3737015
theorem B163513961 : Blo 1104625 163513961 := bstep (se 2 (by rfl) ⟨61317735, by rfl⟩ : syracuseStep 163513961 = 122635471) B122635471
theorem B1771163 : Blo 1104625 1771163 := bstep (se 1 (by rfl) ⟨1328372, by rfl⟩ : syracuseStep 1771163 = 2656745) B2656745
theorem B3737339 : Blo 1104625 3737339 := bstep (se 1 (by rfl) ⟨2803004, by rfl⟩ : syracuseStep 3737339 = 5606009) B5606009
theorem B3737555 : Blo 1104625 3737555 := bstep (se 1 (by rfl) ⟨2803166, by rfl⟩ : syracuseStep 3737555 = 5606333) B5606333
theorem B1574959 : Blo 1104625 1574959 := bstep (se 1 (by rfl) ⟨1181219, by rfl⟩ : syracuseStep 1574959 = 2362439) B2362439
theorem B2099611 : Blo 1104625 2099611 := bstep (se 1 (by rfl) ⟨1574708, by rfl⟩ : syracuseStep 2099611 = 3149417) B3149417
theorem B3738365 : Blo 1104625 3738365 := bstep (se 3 (by rfl) ⟨700943, by rfl⟩ : syracuseStep 3738365 = 1401887) B1401887
theorem B5606171 : Blo 1104625 5606171 := bstep (se 1 (by rfl) ⟨4204628, by rfl⟩ : syracuseStep 5606171 = 8409257) B8409257
theorem B1182971 : Blo 1104625 1182971 := bstep (se 1 (by rfl) ⟨887228, by rfl⟩ : syracuseStep 1182971 = 1774457) B1774457
theorem B5312105 : Blo 1104625 5312105 := bstep (se 2 (by rfl) ⟨1992039, by rfl⟩ : syracuseStep 5312105 = 3984079) B3984079
theorem B7081627 : Blo 1104625 7081627 := bstep (se 1 (by rfl) ⟨5311220, by rfl⟩ : syracuseStep 7081627 = 10622441) B10622441
theorem B5672729 : Blo 1104625 5672729 := bstep (se 2 (by rfl) ⟨2127273, by rfl⟩ : syracuseStep 5672729 = 4254547) B4254547
theorem B3543031 : Blo 1104625 3543031 := bstep (se 1 (by rfl) ⟨2657273, by rfl⟩ : syracuseStep 3543031 = 5314547) B5314547
theorem B27332819 : Blo 1104625 27332819 := bstep (se 1 (by rfl) ⟨20499614, by rfl⟩ : syracuseStep 27332819 = 40999229) B40999229
theorem B1774079 : Blo 1104625 1774079 := bstep (se 1 (by rfl) ⟨1330559, by rfl⟩ : syracuseStep 1774079 = 2661119) B2661119
theorem B12620447 : Blo 1104625 12620447 := bstep (se 1 (by rfl) ⟨9465335, by rfl⟩ : syracuseStep 12620447 = 18930671) B18930671
theorem B2987887 : Blo 1104625 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B30251465 : Blo 1104625 30251465 := bstep (se 2 (by rfl) ⟨11344299, by rfl⟩ : syracuseStep 30251465 = 22688599) B22688599
theorem B6724667 : Blo 1104625 6724667 := bstep (se 1 (by rfl) ⟨5043500, by rfl⟩ : syracuseStep 6724667 = 10087001) B10087001
theorem B3153131 : Blo 1104625 3153131 := bstep (se 1 (by rfl) ⟨2364848, by rfl⟩ : syracuseStep 3153131 = 4729697) B4729697
theorem B65674745 : Blo 1104625 65674745 := bstep (se 2 (by rfl) ⟨24628029, by rfl⟩ : syracuseStep 65674745 = 49256059) B49256059
theorem B4726313 : Blo 1104625 4726313 := bstep (se 2 (by rfl) ⟨1772367, by rfl⟩ : syracuseStep 4726313 = 3544735) B3544735
theorem B2301833 : Blo 1104625 2301833 := bstep (se 2 (by rfl) ⟨863187, by rfl⟩ : syracuseStep 2301833 = 1726375) B1726375
theorem B7086473 : Blo 1104625 7086473 := bstep (se 2 (by rfl) ⟨2657427, by rfl⟩ : syracuseStep 7086473 = 5314855) B5314855
theorem B7087499 : Blo 1104625 7087499 := bstep (se 1 (by rfl) ⟨5315624, by rfl⟩ : syracuseStep 7087499 = 10631249) B10631249
theorem B3156833 : Blo 1104625 3156833 := bstep (se 2 (by rfl) ⟨1183812, by rfl⟩ : syracuseStep 3156833 = 2367625) B2367625
theorem B3550823 : Blo 1104625 3550823 := bstep (se 1 (by rfl) ⟨2663117, by rfl⟩ : syracuseStep 3550823 = 5326235) B5326235
theorem B7974845 : Blo 1104625 7974845 := bstep (se 3 (by rfl) ⟨1495283, by rfl⟩ : syracuseStep 7974845 = 2990567) B2990567
theorem B14168479 : Blo 1104625 14168479 := bstep (se 1 (by rfl) ⟨10626359, by rfl⟩ : syracuseStep 14168479 = 21252719) B21252719
theorem B6305759 : Blo 1104625 6305759 := bstep (se 1 (by rfl) ⟨4729319, by rfl⟩ : syracuseStep 6305759 = 9458639) B9458639
theorem B2799643 : Blo 1104625 2799643 := bstep (se 1 (by rfl) ⟨2099732, by rfl⟩ : syracuseStep 2799643 = 4199465) B4199465
theorem B6734009 : Blo 1104625 6734009 := bstep (se 2 (by rfl) ⟨2525253, by rfl⟩ : syracuseStep 6734009 = 5050507) B5050507
theorem B8962235 : Blo 1104625 8962235 := bstep (se 1 (by rfl) ⟨6721676, by rfl⟩ : syracuseStep 8962235 = 13443353) B13443353
theorem B217924025 : Blo 1104625 217924025 := bstep (se 2 (by rfl) ⟨81721509, by rfl⟩ : syracuseStep 217924025 = 163443019) B163443019
theorem B23937605 : Blo 1104625 23937605 := bstep (se 4 (by rfl) ⟨2244150, by rfl⟩ : syracuseStep 23937605 = 4488301) B4488301
theorem B45499715 : Blo 1104625 45499715 := bstep (se 1 (by rfl) ⟨34124786, by rfl⟩ : syracuseStep 45499715 = 68249573) B68249573
theorem B6309359 : Blo 1104625 6309359 := bstep (se 1 (by rfl) ⟨4732019, by rfl⟩ : syracuseStep 6309359 = 9464039) B9464039
theorem B3197051 : Blo 1104625 3197051 := bstep (se 1 (by rfl) ⟨2397788, by rfl⟩ : syracuseStep 3197051 = 4795577) B4795577
theorem B53758579 : Blo 1104625 53758579 := bstep (se 1 (by rfl) ⟨40318934, by rfl⟩ : syracuseStep 53758579 = 80637869) B80637869
theorem B1657499 : Blo 1104625 1657499 := bstep (se 1 (by rfl) ⟨1243124, by rfl⟩ : syracuseStep 1657499 = 2486249) B2486249
theorem B2804827 : Blo 1104625 2804827 := bstep (se 1 (by rfl) ⟨2103620, by rfl⟩ : syracuseStep 2804827 = 4207241) B4207241
theorem B1657961 : Blo 1104625 1657961 := bstep (se 2 (by rfl) ⟨621735, by rfl⟩ : syracuseStep 1657961 = 1243471) B1243471
theorem B1658111 : Blo 1104625 1658111 := bstep (se 1 (by rfl) ⟨1243583, by rfl⟩ : syracuseStep 1658111 = 2487167) B2487167
theorem B1659071 : Blo 1104625 1659071 := bstep (se 1 (by rfl) ⟨1244303, by rfl⟩ : syracuseStep 1659071 = 2488607) B2488607
theorem B1659119 : Blo 1104625 1659119 := bstep (se 1 (by rfl) ⟨1244339, by rfl⟩ : syracuseStep 1659119 = 2488679) B2488679
theorem B1659131 : Blo 1104625 1659131 := bstep (se 1 (by rfl) ⟨1244348, by rfl⟩ : syracuseStep 1659131 = 2488697) B2488697
theorem B8409743 : Blo 1104625 8409743 := bstep (se 1 (by rfl) ⟨6307307, by rfl⟩ : syracuseStep 8409743 = 12614615) B12614615
theorem B1659881 : Blo 1104625 1659881 := bstep (se 2 (by rfl) ⟨622455, by rfl⟩ : syracuseStep 1659881 = 1244911) B1244911
theorem B1660007 : Blo 1104625 1660007 := bstep (se 1 (by rfl) ⟨1245005, by rfl⟩ : syracuseStep 1660007 = 2490011) B2490011
theorem B1660319 : Blo 1104625 1660319 := bstep (se 1 (by rfl) ⟨1245239, by rfl⟩ : syracuseStep 1660319 = 2490479) B2490479
theorem B1661255 : Blo 1104625 1661255 := bstep (se 1 (by rfl) ⟨1245941, by rfl⟩ : syracuseStep 1661255 = 2491883) B2491883
theorem B1399295 : Blo 1104625 1399295 := bstep (se 1 (by rfl) ⟨1049471, by rfl⟩ : syracuseStep 1399295 = 2098943) B2098943
theorem B1661543 : Blo 1104625 1661543 := bstep (se 1 (by rfl) ⟨1246157, by rfl⟩ : syracuseStep 1661543 = 2492315) B2492315
theorem B55401083 : Blo 1104625 55401083 := bstep (se 1 (by rfl) ⟨41550812, by rfl⟩ : syracuseStep 55401083 = 83101625) B83101625
theorem B1661609 : Blo 1104625 1661609 := bstep (se 2 (by rfl) ⟨623103, by rfl⟩ : syracuseStep 1661609 = 1246207) B1246207
theorem B1104879 : Blo 1104625 1104879 := bstep (se 1 (by rfl) ⟨828659, by rfl⟩ : syracuseStep 1104879 = 1657319) B1657319
theorem B1105311 : Blo 1104625 1105311 := bstep (se 1 (by rfl) ⟨828983, by rfl⟩ : syracuseStep 1105311 = 1657967) B1657967
theorem B1105599 : Blo 1104625 1105599 := bstep (se 1 (by rfl) ⟨829199, by rfl⟩ : syracuseStep 1105599 = 1658399) B1658399
theorem B3728807 : Blo 1104625 3728807 := bstep (se 1 (by rfl) ⟨2796605, by rfl⟩ : syracuseStep 3728807 = 5593211) B5593211
theorem B11986487 : Blo 1104625 11986487 := bstep (se 1 (by rfl) ⟨8989865, by rfl⟩ : syracuseStep 11986487 = 17979731) B17979731
theorem B1107687 : Blo 1104625 1107687 := bstep (se 1 (by rfl) ⟨830765, by rfl⟩ : syracuseStep 1107687 = 1661531) B1661531
theorem B15132743 : Blo 1104625 15132743 := bstep (se 1 (by rfl) ⟨11349557, by rfl⟩ : syracuseStep 15132743 = 22699115) B22699115
theorem B1108383 : Blo 1104625 1108383 := bstep (se 1 (by rfl) ⟨831287, by rfl⟩ : syracuseStep 1108383 = 1662575) B1662575
theorem B15166025 : Blo 1104625 15166025 := bstep (se 2 (by rfl) ⟨5687259, by rfl⟩ : syracuseStep 15166025 = 11374519) B11374519
theorem B15133613 : Blo 1104625 15133613 := bstep (se 3 (by rfl) ⟨2837552, by rfl⟩ : syracuseStep 15133613 = 5675105) B5675105
theorem B5598233 : Blo 1104625 5598233 := bstep (se 2 (by rfl) ⟨2099337, by rfl⟩ : syracuseStep 5598233 = 4198675) B4198675
theorem B7565039 : Blo 1104625 7565039 := bstep (se 1 (by rfl) ⟨5673779, by rfl⟩ : syracuseStep 7565039 = 11347559) B11347559
theorem B2486303 : Blo 1104625 2486303 := bstep (se 1 (by rfl) ⟨1864727, by rfl⟩ : syracuseStep 2486303 = 3729455) B3729455
theorem B245363357 : Blo 1104625 245363357 := bstep (se 3 (by rfl) ⟨46005629, by rfl⟩ : syracuseStep 245363357 = 92011259) B92011259
theorem B2487455 : Blo 1104625 2487455 := bstep (se 1 (by rfl) ⟨1865591, by rfl⟩ : syracuseStep 2487455 = 3731183) B3731183
theorem B24278309 : Blo 1104625 24278309 := bstep (se 4 (by rfl) ⟨2276091, by rfl⟩ : syracuseStep 24278309 = 4552183) B4552183
theorem B4486889 : Blo 1104625 4486889 := bstep (se 2 (by rfl) ⟨1682583, by rfl⟩ : syracuseStep 4486889 = 3365167) B3365167
theorem B1865639 : Blo 1104625 1865639 := bstep (se 1 (by rfl) ⟨1399229, by rfl⟩ : syracuseStep 1865639 = 2798459) B2798459
theorem B2488859 : Blo 1104625 2488859 := bstep (se 1 (by rfl) ⟨1866644, by rfl⟩ : syracuseStep 2488859 = 3733289) B3733289
theorem B3734099 : Blo 1104625 3734099 := bstep (se 1 (by rfl) ⟨2800574, by rfl⟩ : syracuseStep 3734099 = 5601149) B5601149
theorem B3734207 : Blo 1104625 3734207 := bstep (se 1 (by rfl) ⟨2800655, by rfl⟩ : syracuseStep 3734207 = 5601311) B5601311
theorem B4258793 : Blo 1104625 4258793 := bstep (se 2 (by rfl) ⟨1597047, by rfl⟩ : syracuseStep 4258793 = 3194095) B3194095
theorem B28409129 : Blo 1104625 28409129 := bstep (se 2 (by rfl) ⟨10653423, by rfl⟩ : syracuseStep 28409129 = 21306847) B21306847
theorem B5602607 : Blo 1104625 5602607 := bstep (se 1 (by rfl) ⟨4201955, by rfl⟩ : syracuseStep 5602607 = 8403911) B8403911
theorem B2490281 : Blo 1104625 2490281 := bstep (se 2 (by rfl) ⟨933855, by rfl⟩ : syracuseStep 2490281 = 1867711) B1867711
theorem B4194287 : Blo 1104625 4194287 := bstep (se 1 (by rfl) ⟨3145715, by rfl⟩ : syracuseStep 4194287 = 6291431) B6291431
theorem B4489339 : Blo 1104625 4489339 := bstep (se 1 (by rfl) ⟨3367004, by rfl⟩ : syracuseStep 4489339 = 6734009) B6734009
theorem B15958403 : Blo 1104625 15958403 := bstep (se 1 (by rfl) ⟨11968802, by rfl⟩ : syracuseStep 15958403 = 23937605) B23937605
theorem B1180775 : Blo 1104625 1180775 := bstep (se 1 (by rfl) ⟨885581, by rfl⟩ : syracuseStep 1180775 = 1771163) B1771163
theorem B2491559 : Blo 1104625 2491559 := bstep (se 1 (by rfl) ⟨1868669, by rfl⟩ : syracuseStep 2491559 = 3737339) B3737339
theorem B2491703 : Blo 1104625 2491703 := bstep (se 1 (by rfl) ⟨1868777, by rfl⟩ : syracuseStep 2491703 = 3737555) B3737555
theorem B2131367 : Blo 1104625 2131367 := bstep (se 1 (by rfl) ⟨1598525, by rfl⟩ : syracuseStep 2131367 = 3197051) B3197051
theorem B2492243 : Blo 1104625 2492243 := bstep (se 1 (by rfl) ⟨1869182, by rfl⟩ : syracuseStep 2492243 = 3738365) B3738365
theorem B3737447 : Blo 1104625 3737447 := bstep (se 1 (by rfl) ⟨2803085, by rfl⟩ : syracuseStep 3737447 = 5606171) B5606171
theorem B3541403 : Blo 1104625 3541403 := bstep (se 1 (by rfl) ⟨2656052, by rfl⟩ : syracuseStep 3541403 = 5312105) B5312105
theorem B2099945 : Blo 1104625 2099945 := bstep (se 2 (by rfl) ⟨787479, by rfl⟩ : syracuseStep 2099945 = 1574959) B1574959
theorem B18221879 : Blo 1104625 18221879 := bstep (se 1 (by rfl) ⟨13666409, by rfl⟩ : syracuseStep 18221879 = 27332819) B27332819
theorem B1182719 : Blo 1104625 1182719 := bstep (se 1 (by rfl) ⟨887039, by rfl⟩ : syracuseStep 1182719 = 1774079) B1774079
theorem B5606495 : Blo 1104625 5606495 := bstep (se 1 (by rfl) ⟨4204871, by rfl⟩ : syracuseStep 5606495 = 8409743) B8409743
theorem B3739769 : Blo 1104625 3739769 := bstep (se 2 (by rfl) ⟨1402413, by rfl⟩ : syracuseStep 3739769 = 2804827) B2804827
theorem B36934055 : Blo 1104625 36934055 := bstep (se 1 (by rfl) ⟨27700541, by rfl⟩ : syracuseStep 36934055 = 55401083) B55401083
theorem B2102087 : Blo 1104625 2102087 := bstep (se 1 (by rfl) ⟨1576565, by rfl⟩ : syracuseStep 2102087 = 3153131) B3153131
theorem B9442169 : Blo 1104625 9442169 := bstep (se 2 (by rfl) ⟨3540813, by rfl⟩ : syracuseStep 9442169 = 7081627) B7081627
theorem B43783163 : Blo 1104625 43783163 := bstep (se 1 (by rfl) ⟨32837372, by rfl⟩ : syracuseStep 43783163 = 65674745) B65674745
theorem B3150875 : Blo 1104625 3150875 := bstep (se 1 (by rfl) ⟨2363156, by rfl⟩ : syracuseStep 3150875 = 4726313) B4726313
theorem B4724041 : Blo 1104625 4724041 := bstep (se 2 (by rfl) ⟨1771515, by rfl⟩ : syracuseStep 4724041 = 3543031) B3543031
theorem B4724315 : Blo 1104625 4724315 := bstep (se 1 (by rfl) ⟨3543236, by rfl⟩ : syracuseStep 4724315 = 7086473) B7086473
theorem B4724999 : Blo 1104625 4724999 := bstep (se 1 (by rfl) ⟨3543749, by rfl⟩ : syracuseStep 4724999 = 7087499) B7087499
theorem B2104555 : Blo 1104625 2104555 := bstep (se 1 (by rfl) ⟨1578416, by rfl⟩ : syracuseStep 2104555 = 3156833) B3156833
theorem B2367215 : Blo 1104625 2367215 := bstep (se 1 (by rfl) ⟨1775411, by rfl⟩ : syracuseStep 2367215 = 3550823) B3550823
theorem B5316563 : Blo 1104625 5316563 := bstep (se 1 (by rfl) ⟨3987422, by rfl⟩ : syracuseStep 5316563 = 7974845) B7974845
theorem B3154589 : Blo 1104625 3154589 := bstep (se 3 (by rfl) ⟨591485, by rfl⟩ : syracuseStep 3154589 = 1182971) B1182971
theorem B2991259 : Blo 1104625 2991259 := bstep (se 1 (by rfl) ⟨2243444, by rfl⟩ : syracuseStep 2991259 = 4486889) B4486889
theorem B4203839 : Blo 1104625 4203839 := bstep (se 1 (by rfl) ⟨3152879, by rfl⟩ : syracuseStep 4203839 = 6305759) B6305759
theorem B2796191 : Blo 1104625 2796191 := bstep (se 1 (by rfl) ⟨2097143, by rfl⟩ : syracuseStep 2796191 = 4194287) B4194287
theorem B5974823 : Blo 1104625 5974823 := bstep (se 1 (by rfl) ⟨4481117, by rfl⟩ : syracuseStep 5974823 = 8962235) B8962235
theorem B4206239 : Blo 1104625 4206239 := bstep (se 1 (by rfl) ⟨3154679, by rfl⟩ : syracuseStep 4206239 = 6309359) B6309359
theorem B3781819 : Blo 1104625 3781819 := bstep (se 1 (by rfl) ⟨2836364, by rfl⟩ : syracuseStep 3781819 = 5672729) B5672729
theorem B2799481 : Blo 1104625 2799481 := bstep (se 2 (by rfl) ⟨1049805, by rfl⟩ : syracuseStep 2799481 = 2099611) B2099611
theorem B71678105 : Blo 1104625 71678105 := bstep (se 2 (by rfl) ⟨26879289, by rfl⟩ : syracuseStep 71678105 = 53758579) B53758579
theorem B20167643 : Blo 1104625 20167643 := bstep (se 1 (by rfl) ⟨15125732, by rfl⟩ : syracuseStep 20167643 = 30251465) B30251465
theorem B18891305 : Blo 1104625 18891305 := bstep (se 2 (by rfl) ⟨7084239, by rfl⟩ : syracuseStep 18891305 = 14168479) B14168479
theorem B10110683 : Blo 1104625 10110683 := bstep (se 1 (by rfl) ⟨7583012, by rfl⟩ : syracuseStep 10110683 = 15166025) B15166025
theorem B40356301 : Blo 1104625 40356301 := bstep (se 3 (by rfl) ⟨7566806, by rfl⟩ : syracuseStep 40356301 = 15133613) B15133613
theorem B3983849 : Blo 1104625 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B1657535 : Blo 1104625 1657535 := bstep (se 1 (by rfl) ⟨1243151, by rfl⟩ : syracuseStep 1657535 = 2486303) B2486303
theorem B1658303 : Blo 1104625 1658303 := bstep (se 1 (by rfl) ⟨1243727, by rfl⟩ : syracuseStep 1658303 = 2487455) B2487455
theorem B1659239 : Blo 1104625 1659239 := bstep (se 1 (by rfl) ⟨1244429, by rfl⟩ : syracuseStep 1659239 = 2488859) B2488859
theorem B2839195 : Blo 1104625 2839195 := bstep (se 1 (by rfl) ⟨2129396, by rfl⟩ : syracuseStep 2839195 = 4258793) B4258793
theorem B1660187 : Blo 1104625 1660187 := bstep (se 1 (by rfl) ⟨1245140, by rfl⟩ : syracuseStep 1660187 = 2490281) B2490281
theorem B1660463 : Blo 1104625 1660463 := bstep (se 1 (by rfl) ⟨1245347, by rfl⟩ : syracuseStep 1660463 = 2490695) B2490695
theorem B1660895 : Blo 1104625 1660895 := bstep (se 1 (by rfl) ⟨1245671, by rfl⟩ : syracuseStep 1660895 = 2491343) B2491343
theorem B30333143 : Blo 1104625 30333143 := bstep (se 1 (by rfl) ⟨22749857, by rfl⟩ : syracuseStep 30333143 = 45499715) B45499715
theorem B109009307 : Blo 1104625 109009307 := bstep (se 1 (by rfl) ⟨81756980, by rfl⟩ : syracuseStep 109009307 = 163513961) B163513961
theorem B1104999 : Blo 1104625 1104999 := bstep (se 1 (by rfl) ⟨828749, by rfl⟩ : syracuseStep 1104999 = 1657499) B1657499
theorem B1105307 : Blo 1104625 1105307 := bstep (se 1 (by rfl) ⟨828980, by rfl⟩ : syracuseStep 1105307 = 1657961) B1657961
theorem B1105407 : Blo 1104625 1105407 := bstep (se 1 (by rfl) ⟨829055, by rfl⟩ : syracuseStep 1105407 = 1658111) B1658111
theorem B1106047 : Blo 1104625 1106047 := bstep (se 1 (by rfl) ⟨829535, by rfl⟩ : syracuseStep 1106047 = 1659071) B1659071
theorem B1106079 : Blo 1104625 1106079 := bstep (se 1 (by rfl) ⟨829559, by rfl⟩ : syracuseStep 1106079 = 1659119) B1659119
theorem B1106087 : Blo 1104625 1106087 := bstep (se 1 (by rfl) ⟨829565, by rfl⟩ : syracuseStep 1106087 = 1659131) B1659131
theorem B8413631 : Blo 1104625 8413631 := bstep (se 1 (by rfl) ⟨6310223, by rfl⟩ : syracuseStep 8413631 = 12620447) B12620447
theorem B1106587 : Blo 1104625 1106587 := bstep (se 1 (by rfl) ⟨829940, by rfl⟩ : syracuseStep 1106587 = 1659881) B1659881
theorem B1106671 : Blo 1104625 1106671 := bstep (se 1 (by rfl) ⟨830003, by rfl⟩ : syracuseStep 1106671 = 1660007) B1660007
theorem B1106879 : Blo 1104625 1106879 := bstep (se 1 (by rfl) ⟨830159, by rfl⟩ : syracuseStep 1106879 = 1660319) B1660319
theorem B1107503 : Blo 1104625 1107503 := bstep (se 1 (by rfl) ⟨830627, by rfl⟩ : syracuseStep 1107503 = 1661255) B1661255
theorem B1107695 : Blo 1104625 1107695 := bstep (se 1 (by rfl) ⟨830771, by rfl⟩ : syracuseStep 1107695 = 1661543) B1661543
theorem B1107739 : Blo 1104625 1107739 := bstep (se 1 (by rfl) ⟨830804, by rfl⟩ : syracuseStep 1107739 = 1661609) B1661609
theorem B2324522933 : Blo 1104625 2324522933 := bstep (se 5 (by rfl) ⟨108962012, by rfl⟩ : syracuseStep 2324522933 = 217924025) B217924025
theorem B4483111 : Blo 1104625 4483111 := bstep (se 1 (by rfl) ⟨3362333, by rfl⟩ : syracuseStep 4483111 = 6724667) B6724667
theorem B1534555 : Blo 1104625 1534555 := bstep (se 1 (by rfl) ⟨1150916, by rfl⟩ : syracuseStep 1534555 = 2301833) B2301833
theorem B2485871 : Blo 1104625 2485871 := bstep (se 1 (by rfl) ⟨1864403, by rfl⟩ : syracuseStep 2485871 = 3728807) B3728807
theorem B7990991 : Blo 1104625 7990991 := bstep (se 1 (by rfl) ⟨5993243, by rfl⟩ : syracuseStep 7990991 = 11986487) B11986487
theorem B3731453 : Blo 1104625 3731453 := bstep (se 3 (by rfl) ⟨699647, by rfl⟩ : syracuseStep 3731453 = 1399295) B1399295
theorem B10088495 : Blo 1104625 10088495 := bstep (se 1 (by rfl) ⟨7566371, by rfl⟩ : syracuseStep 10088495 = 15132743) B15132743
theorem B3732155 : Blo 1104625 3732155 := bstep (se 1 (by rfl) ⟨2799116, by rfl⟩ : syracuseStep 3732155 = 5598233) B5598233
theorem B5043359 : Blo 1104625 5043359 := bstep (se 1 (by rfl) ⟨3782519, by rfl⟩ : syracuseStep 5043359 = 7565039) B7565039
theorem B3732857 : Blo 1104625 3732857 := bstep (se 2 (by rfl) ⟨1399821, by rfl⟩ : syracuseStep 3732857 = 2799643) B2799643
theorem B163575571 : Blo 1104625 163575571 := bstep (se 1 (by rfl) ⟨122681678, by rfl⟩ : syracuseStep 163575571 = 245363357) B245363357
theorem B16185539 : Blo 1104625 16185539 := bstep (se 1 (by rfl) ⟨12139154, by rfl⟩ : syracuseStep 16185539 = 24278309) B24278309
theorem B1243759 : Blo 1104625 1243759 := bstep (se 1 (by rfl) ⟨932819, by rfl⟩ : syracuseStep 1243759 = 1865639) B1865639
theorem B2489399 : Blo 1104625 2489399 := bstep (se 1 (by rfl) ⟨1867049, by rfl⟩ : syracuseStep 2489399 = 3734099) B3734099
theorem B2489471 : Blo 1104625 2489471 := bstep (se 1 (by rfl) ⟨1867103, by rfl⟩ : syracuseStep 2489471 = 3734207) B3734207
theorem B18939419 : Blo 1104625 18939419 := bstep (se 1 (by rfl) ⟨14204564, by rfl⟩ : syracuseStep 18939419 = 28409129) B28409129
theorem B3735071 : Blo 1104625 3735071 := bstep (se 1 (by rfl) ⟨2801303, by rfl⟩ : syracuseStep 3735071 = 5602607) B5602607
theorem B2491631 : Blo 1104625 2491631 := bstep (se 1 (by rfl) ⟨1868723, by rfl⟩ : syracuseStep 2491631 = 3737447) B3737447
theorem B2360935 : Blo 1104625 2360935 := bstep (se 1 (by rfl) ⟨1770701, by rfl⟩ : syracuseStep 2360935 = 3541403) B3541403
theorem B2655899 : Blo 1104625 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B3737663 : Blo 1104625 3737663 := bstep (se 1 (by rfl) ⟨2803247, by rfl⟩ : syracuseStep 3737663 = 5606495) B5606495
theorem B2493179 : Blo 1104625 2493179 := bstep (se 1 (by rfl) ⟨1869884, by rfl⟩ : syracuseStep 2493179 = 3739769) B3739769
theorem B3148733 : Blo 1104625 3148733 := bstep (se 3 (by rfl) ⟨590387, by rfl⟩ : syracuseStep 3148733 = 1180775) B1180775
theorem B6294779 : Blo 1104625 6294779 := bstep (se 1 (by rfl) ⟨4721084, by rfl⟩ : syracuseStep 6294779 = 9442169) B9442169
theorem B53808401 : Blo 1104625 53808401 := bstep (se 2 (by rfl) ⟨20178150, by rfl⟩ : syracuseStep 53808401 = 40356301) B40356301
theorem B2100583 : Blo 1104625 2100583 := bstep (se 1 (by rfl) ⟨1575437, by rfl⟩ : syracuseStep 2100583 = 3150875) B3150875
theorem B15142373 : Blo 1104625 15142373 := bstep (se 4 (by rfl) ⟨1419597, by rfl⟩ : syracuseStep 15142373 = 2839195) B2839195
theorem B3149543 : Blo 1104625 3149543 := bstep (se 1 (by rfl) ⟨2362157, by rfl⟩ : syracuseStep 3149543 = 4724315) B4724315
theorem B20222095 : Blo 1104625 20222095 := bstep (se 1 (by rfl) ⟨15166571, by rfl⟩ : syracuseStep 20222095 = 30333143) B30333143
theorem B3149999 : Blo 1104625 3149999 := bstep (se 1 (by rfl) ⟨2362499, by rfl⟩ : syracuseStep 3149999 = 4724999) B4724999
theorem B1578143 : Blo 1104625 1578143 := bstep (se 1 (by rfl) ⟨1183607, by rfl⟩ : syracuseStep 1578143 = 2367215) B2367215
theorem B5609087 : Blo 1104625 5609087 := bstep (se 1 (by rfl) ⟨4206815, by rfl⟩ : syracuseStep 5609087 = 8413631) B8413631
theorem B2103059 : Blo 1104625 2103059 := bstep (se 1 (by rfl) ⟨1577294, by rfl⟩ : syracuseStep 2103059 = 3154589) B3154589
theorem B43161437 : Blo 1104625 43161437 := bstep (se 3 (by rfl) ⟨8092769, by rfl⟩ : syracuseStep 43161437 = 16185539) B16185539
theorem B6298721 : Blo 1104625 6298721 := bstep (se 2 (by rfl) ⟨2362020, by rfl⟩ : syracuseStep 6298721 = 4724041) B4724041
theorem B53780381 : Blo 1104625 53780381 := bstep (se 3 (by rfl) ⟨10083821, by rfl⟩ : syracuseStep 53780381 = 20167643) B20167643
theorem B3153917 : Blo 1104625 3153917 := bstep (se 3 (by rfl) ⟨591359, by rfl⟩ : syracuseStep 3153917 = 1182719) B1182719
theorem B6725663 : Blo 1104625 6725663 := bstep (se 1 (by rfl) ⟨5044247, by rfl⟩ : syracuseStep 6725663 = 10088495) B10088495
theorem B47785403 : Blo 1104625 47785403 := bstep (se 1 (by rfl) ⟨35839052, by rfl⟩ : syracuseStep 47785403 = 71678105) B71678105
theorem B12626279 : Blo 1104625 12626279 := bstep (se 1 (by rfl) ⟨9469709, by rfl⟩ : syracuseStep 12626279 = 18939419) B18939419
theorem B12594203 : Blo 1104625 12594203 := bstep (se 1 (by rfl) ⟨9445652, by rfl⟩ : syracuseStep 12594203 = 18891305) B18891305
theorem B5977481 : Blo 1104625 5977481 := bstep (se 2 (by rfl) ⟨2241555, by rfl⟩ : syracuseStep 5977481 = 4483111) B4483111
theorem B24622703 : Blo 1104625 24622703 := bstep (se 1 (by rfl) ⟨18467027, by rfl⟩ : syracuseStep 24622703 = 36934055) B36934055
theorem B2046073 : Blo 1104625 2046073 := bstep (se 2 (by rfl) ⟨767277, by rfl⟩ : syracuseStep 2046073 = 1534555) B1534555
theorem B5683645 : Blo 1104625 5683645 := bstep (se 3 (by rfl) ⟨1065683, by rfl⟩ : syracuseStep 5683645 = 2131367) B2131367
theorem B2802559 : Blo 1104625 2802559 := bstep (se 1 (by rfl) ⟨2101919, by rfl⟩ : syracuseStep 2802559 = 4203839) B4203839
theorem B1549681955 : Blo 1104625 1549681955 := bstep (se 1 (by rfl) ⟨1162261466, by rfl⟩ : syracuseStep 1549681955 = 2324522933) B2324522933
theorem B3983215 : Blo 1104625 3983215 := bstep (se 1 (by rfl) ⟨2987411, by rfl⟩ : syracuseStep 3983215 = 5974823) B5974823
theorem B1657247 : Blo 1104625 1657247 := bstep (se 1 (by rfl) ⟨1242935, by rfl⟩ : syracuseStep 1657247 = 2485871) B2485871
theorem B2804159 : Blo 1104625 2804159 := bstep (se 1 (by rfl) ⟨2103119, by rfl⟩ : syracuseStep 2804159 = 4206239) B4206239
theorem B5327327 : Blo 1104625 5327327 := bstep (se 1 (by rfl) ⟨3995495, by rfl⟩ : syracuseStep 5327327 = 7990991) B7990991
theorem B3362239 : Blo 1104625 3362239 := bstep (se 1 (by rfl) ⟨2521679, by rfl⟩ : syracuseStep 3362239 = 5043359) B5043359
theorem B1658345 : Blo 1104625 1658345 := bstep (se 2 (by rfl) ⟨621879, by rfl⟩ : syracuseStep 1658345 = 1243759) B1243759
theorem B2806073 : Blo 1104625 2806073 := bstep (se 2 (by rfl) ⟨1052277, by rfl⟩ : syracuseStep 2806073 = 2104555) B2104555
theorem B1659599 : Blo 1104625 1659599 := bstep (se 1 (by rfl) ⟨1244699, by rfl⟩ : syracuseStep 1659599 = 2489399) B2489399
theorem B1659647 : Blo 1104625 1659647 := bstep (se 1 (by rfl) ⟨1244735, by rfl⟩ : syracuseStep 1659647 = 2489471) B2489471
theorem B14177501 : Blo 1104625 14177501 := bstep (se 3 (by rfl) ⟨2658281, by rfl⟩ : syracuseStep 14177501 = 5316563) B5316563
theorem B5985785 : Blo 1104625 5985785 := bstep (se 2 (by rfl) ⟨2244669, by rfl⟩ : syracuseStep 5985785 = 4489339) B4489339
theorem B10638935 : Blo 1104625 10638935 := bstep (se 1 (by rfl) ⟨7979201, by rfl⟩ : syracuseStep 10638935 = 15958403) B15958403
theorem B1661039 : Blo 1104625 1661039 := bstep (se 1 (by rfl) ⟨1245779, by rfl⟩ : syracuseStep 1661039 = 2491559) B2491559
theorem B1661135 : Blo 1104625 1661135 := bstep (se 1 (by rfl) ⟨1245851, by rfl⟩ : syracuseStep 1661135 = 2491703) B2491703
theorem B6740455 : Blo 1104625 6740455 := bstep (se 1 (by rfl) ⟨5055341, by rfl⟩ : syracuseStep 6740455 = 10110683) B10110683
theorem B1661495 : Blo 1104625 1661495 := bstep (se 1 (by rfl) ⟨1246121, by rfl⟩ : syracuseStep 1661495 = 2492243) B2492243
theorem B1105023 : Blo 1104625 1105023 := bstep (se 1 (by rfl) ⟨828767, by rfl⟩ : syracuseStep 1105023 = 1657535) B1657535
theorem B1105535 : Blo 1104625 1105535 := bstep (se 1 (by rfl) ⟨829151, by rfl⟩ : syracuseStep 1105535 = 1658303) B1658303
theorem B1106159 : Blo 1104625 1106159 := bstep (se 1 (by rfl) ⟨829619, by rfl⟩ : syracuseStep 1106159 = 1659239) B1659239
theorem B1401391 : Blo 1104625 1401391 := bstep (se 1 (by rfl) ⟨1051043, by rfl⟩ : syracuseStep 1401391 = 2102087) B2102087
theorem B29188775 : Blo 1104625 29188775 := bstep (se 1 (by rfl) ⟨21891581, by rfl⟩ : syracuseStep 29188775 = 43783163) B43783163
theorem B1106791 : Blo 1104625 1106791 := bstep (se 1 (by rfl) ⟨830093, by rfl⟩ : syracuseStep 1106791 = 1660187) B1660187
theorem B1106975 : Blo 1104625 1106975 := bstep (se 1 (by rfl) ⟨830231, by rfl⟩ : syracuseStep 1106975 = 1660463) B1660463
theorem B1107263 : Blo 1104625 1107263 := bstep (se 1 (by rfl) ⟨830447, by rfl⟩ : syracuseStep 1107263 = 1660895) B1660895
theorem B72672871 : Blo 1104625 72672871 := bstep (se 1 (by rfl) ⟨54504653, by rfl⟩ : syracuseStep 72672871 = 109009307) B109009307
theorem B15953381 : Blo 1104625 15953381 := bstep (se 4 (by rfl) ⟨1495629, by rfl⟩ : syracuseStep 15953381 = 2991259) B2991259
theorem B5042425 : Blo 1104625 5042425 := bstep (se 2 (by rfl) ⟨1890909, by rfl⟩ : syracuseStep 5042425 = 3781819) B3781819
theorem B1864127 : Blo 1104625 1864127 := bstep (se 1 (by rfl) ⟨1398095, by rfl⟩ : syracuseStep 1864127 = 2796191) B2796191
theorem B5599853 : Blo 1104625 5599853 := bstep (se 3 (by rfl) ⟨1049972, by rfl⟩ : syracuseStep 5599853 = 2099945) B2099945
theorem B48591677 : Blo 1104625 48591677 := bstep (se 3 (by rfl) ⟨9110939, by rfl⟩ : syracuseStep 48591677 = 18221879) B18221879
theorem B218100761 : Blo 1104625 218100761 := bstep (se 2 (by rfl) ⟨81787785, by rfl⟩ : syracuseStep 218100761 = 163575571) B163575571
theorem B3732641 : Blo 1104625 3732641 := bstep (se 2 (by rfl) ⟨1399740, by rfl⟩ : syracuseStep 3732641 = 2799481) B2799481
theorem B2487635 : Blo 1104625 2487635 := bstep (se 1 (by rfl) ⟨1865726, by rfl⟩ : syracuseStep 2487635 = 3731453) B3731453
theorem B2488103 : Blo 1104625 2488103 := bstep (se 1 (by rfl) ⟨1866077, by rfl⟩ : syracuseStep 2488103 = 3732155) B3732155
theorem B2488571 : Blo 1104625 2488571 := bstep (se 1 (by rfl) ⟨1866428, by rfl⟩ : syracuseStep 2488571 = 3732857) B3732857
theorem B2490047 : Blo 1104625 2490047 := bstep (se 1 (by rfl) ⟨1867535, by rfl⟩ : syracuseStep 2490047 = 3735071) B3735071
theorem B1868521 : Blo 1104625 1868521 := bstep (se 2 (by rfl) ⟨700695, by rfl⟩ : syracuseStep 1868521 = 1401391) B1401391
theorem B1770599 : Blo 1104625 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B3736745 : Blo 1104625 3736745 := bstep (se 2 (by rfl) ⟨1401279, by rfl⟩ : syracuseStep 3736745 = 2802559) B2802559
theorem B2491775 : Blo 1104625 2491775 := bstep (se 1 (by rfl) ⟨1868831, by rfl⟩ : syracuseStep 2491775 = 3737663) B3737663
theorem B1869439 : Blo 1104625 1869439 := bstep (se 1 (by rfl) ⟨1402079, by rfl⟩ : syracuseStep 1869439 = 2804159) B2804159
theorem B96897161 : Blo 1104625 96897161 := bstep (se 2 (by rfl) ⟨36336435, by rfl⟩ : syracuseStep 96897161 = 72672871) B72672871
theorem B3147913 : Blo 1104625 3147913 := bstep (se 2 (by rfl) ⟨1180467, by rfl⟩ : syracuseStep 3147913 = 2360935) B2360935
theorem B4196519 : Blo 1104625 4196519 := bstep (se 1 (by rfl) ⟨3147389, by rfl⟩ : syracuseStep 4196519 = 6294779) B6294779
theorem B10094915 : Blo 1104625 10094915 := bstep (se 1 (by rfl) ⟨7571186, by rfl⟩ : syracuseStep 10094915 = 15142373) B15142373
theorem B5310953 : Blo 1104625 5310953 := bstep (se 2 (by rfl) ⟨1991607, by rfl⟩ : syracuseStep 5310953 = 3983215) B3983215
theorem B2099695 : Blo 1104625 2099695 := bstep (se 1 (by rfl) ⟨1574771, by rfl⟩ : syracuseStep 2099695 = 3149543) B3149543
theorem B2099999 : Blo 1104625 2099999 := bstep (se 1 (by rfl) ⟨1574999, by rfl⟩ : syracuseStep 2099999 = 3149999) B3149999
theorem B1870715 : Blo 1104625 1870715 := bstep (se 1 (by rfl) ⟨1403036, by rfl⟩ : syracuseStep 1870715 = 2806073) B2806073
theorem B3739391 : Blo 1104625 3739391 := bstep (se 1 (by rfl) ⟨2804543, by rfl⟩ : syracuseStep 3739391 = 5609087) B5609087
theorem B28774291 : Blo 1104625 28774291 := bstep (se 1 (by rfl) ⟨21580718, by rfl⟩ : syracuseStep 28774291 = 43161437) B43161437
theorem B15962093 : Blo 1104625 15962093 := bstep (se 3 (by rfl) ⟨2992892, by rfl⟩ : syracuseStep 15962093 = 5985785) B5985785
theorem B4199147 : Blo 1104625 4199147 := bstep (se 1 (by rfl) ⟨3149360, by rfl⟩ : syracuseStep 4199147 = 6298721) B6298721
theorem B35853587 : Blo 1104625 35853587 := bstep (se 1 (by rfl) ⟨26890190, by rfl⟩ : syracuseStep 35853587 = 53780381) B53780381
theorem B2102611 : Blo 1104625 2102611 := bstep (se 1 (by rfl) ⟨1576958, by rfl⟩ : syracuseStep 2102611 = 3153917) B3153917
theorem B6723233 : Blo 1104625 6723233 := bstep (se 2 (by rfl) ⟨2521212, by rfl⟩ : syracuseStep 6723233 = 5042425) B5042425
theorem B31856935 : Blo 1104625 31856935 := bstep (se 1 (by rfl) ⟨23892701, by rfl⟩ : syracuseStep 31856935 = 47785403) B47785403
theorem B8396135 : Blo 1104625 8396135 := bstep (se 1 (by rfl) ⟨6297101, by rfl⟩ : syracuseStep 8396135 = 12594203) B12594203
theorem B8396621 : Blo 1104625 8396621 := bstep (se 3 (by rfl) ⟨1574366, by rfl⟩ : syracuseStep 8396621 = 3148733) B3148733
theorem B2728097 : Blo 1104625 2728097 := bstep (se 2 (by rfl) ⟨1023036, by rfl⟩ : syracuseStep 2728097 = 2046073) B2046073
theorem B7578193 : Blo 1104625 7578193 := bstep (se 2 (by rfl) ⟨2841822, by rfl⟩ : syracuseStep 7578193 = 5683645) B5683645
theorem B8987273 : Blo 1104625 8987273 := bstep (se 2 (by rfl) ⟨3370227, by rfl⟩ : syracuseStep 8987273 = 6740455) B6740455
theorem B145400507 : Blo 1104625 145400507 := bstep (se 1 (by rfl) ⟨109050380, by rfl⟩ : syracuseStep 145400507 = 218100761) B218100761
theorem B1033121303 : Blo 1104625 1033121303 := bstep (se 1 (by rfl) ⟨774840977, by rfl⟩ : syracuseStep 1033121303 = 1549681955) B1549681955
theorem B129577805 : Blo 1104625 129577805 := bstep (se 3 (by rfl) ⟨24295838, by rfl⟩ : syracuseStep 129577805 = 48591677) B48591677
theorem B4208381 : Blo 1104625 4208381 := bstep (se 3 (by rfl) ⟨789071, by rfl⟩ : syracuseStep 4208381 = 1578143) B1578143
theorem B9451667 : Blo 1104625 9451667 := bstep (se 1 (by rfl) ⟨7088750, by rfl⟩ : syracuseStep 9451667 = 14177501) B14177501
theorem B15939949 : Blo 1104625 15939949 := bstep (se 3 (by rfl) ⟨2988740, by rfl⟩ : syracuseStep 15939949 = 5977481) B5977481
theorem B7092623 : Blo 1104625 7092623 := bstep (se 1 (by rfl) ⟨5319467, by rfl⟩ : syracuseStep 7092623 = 10638935) B10638935
theorem B2800777 : Blo 1104625 2800777 := bstep (se 2 (by rfl) ⟨1050291, by rfl⟩ : syracuseStep 2800777 = 2100583) B2100583
theorem B14206205 : Blo 1104625 14206205 := bstep (se 3 (by rfl) ⟨2663663, by rfl⟩ : syracuseStep 14206205 = 5327327) B5327327
theorem B10635587 : Blo 1104625 10635587 := bstep (se 1 (by rfl) ⟨7976690, by rfl⟩ : syracuseStep 10635587 = 15953381) B15953381
theorem B1658423 : Blo 1104625 1658423 := bstep (se 1 (by rfl) ⟨1243817, by rfl⟩ : syracuseStep 1658423 = 2487635) B2487635
theorem B1658735 : Blo 1104625 1658735 := bstep (se 1 (by rfl) ⟨1244051, by rfl⟩ : syracuseStep 1658735 = 2488103) B2488103
theorem B1659047 : Blo 1104625 1659047 := bstep (se 1 (by rfl) ⟨1244285, by rfl⟩ : syracuseStep 1659047 = 2488571) B2488571
theorem B1660031 : Blo 1104625 1660031 := bstep (se 1 (by rfl) ⟨1245023, by rfl⟩ : syracuseStep 1660031 = 2490047) B2490047
theorem B1661087 : Blo 1104625 1661087 := bstep (se 1 (by rfl) ⟨1245815, by rfl⟩ : syracuseStep 1661087 = 2491631) B2491631
theorem B1104831 : Blo 1104625 1104831 := bstep (se 1 (by rfl) ⟨828623, by rfl⟩ : syracuseStep 1104831 = 1657247) B1657247
theorem B1662119 : Blo 1104625 1662119 := bstep (se 1 (by rfl) ⟨1246589, by rfl⟩ : syracuseStep 1662119 = 2493179) B2493179
theorem B1105563 : Blo 1104625 1105563 := bstep (se 1 (by rfl) ⟨829172, by rfl⟩ : syracuseStep 1105563 = 1658345) B1658345
theorem B1106399 : Blo 1104625 1106399 := bstep (se 1 (by rfl) ⟨829799, by rfl⟩ : syracuseStep 1106399 = 1659599) B1659599
theorem B1106431 : Blo 1104625 1106431 := bstep (se 1 (by rfl) ⟨829823, by rfl⟩ : syracuseStep 1106431 = 1659647) B1659647
theorem B1402039 : Blo 1104625 1402039 := bstep (se 1 (by rfl) ⟨1051529, by rfl⟩ : syracuseStep 1402039 = 2103059) B2103059
theorem B1107359 : Blo 1104625 1107359 := bstep (se 1 (by rfl) ⟨830519, by rfl⟩ : syracuseStep 1107359 = 1661039) B1661039
theorem B1107423 : Blo 1104625 1107423 := bstep (se 1 (by rfl) ⟨830567, by rfl⟩ : syracuseStep 1107423 = 1661135) B1661135
theorem B1107663 : Blo 1104625 1107663 := bstep (se 1 (by rfl) ⟨830747, by rfl⟩ : syracuseStep 1107663 = 1661495) B1661495
theorem B4482985 : Blo 1104625 4482985 := bstep (se 2 (by rfl) ⟨1681119, by rfl⟩ : syracuseStep 4482985 = 3362239) B3362239
theorem B4483775 : Blo 1104625 4483775 := bstep (se 1 (by rfl) ⟨3362831, by rfl⟩ : syracuseStep 4483775 = 6725663) B6725663
theorem B26962793 : Blo 1104625 26962793 := bstep (se 2 (by rfl) ⟨10111047, by rfl⟩ : syracuseStep 26962793 = 20222095) B20222095
theorem B19459183 : Blo 1104625 19459183 := bstep (se 1 (by rfl) ⟨14594387, by rfl⟩ : syracuseStep 19459183 = 29188775) B29188775
theorem B8417519 : Blo 1104625 8417519 := bstep (se 1 (by rfl) ⟨6313139, by rfl⟩ : syracuseStep 8417519 = 12626279) B12626279
theorem B1242751 : Blo 1104625 1242751 := bstep (se 1 (by rfl) ⟨932063, by rfl⟩ : syracuseStep 1242751 = 1864127) B1864127
theorem B3733235 : Blo 1104625 3733235 := bstep (se 1 (by rfl) ⟨2799926, by rfl⟩ : syracuseStep 3733235 = 5599853) B5599853
theorem B143489069 : Blo 1104625 143489069 := bstep (se 3 (by rfl) ⟨26904200, by rfl⟩ : syracuseStep 143489069 = 53808401) B53808401
theorem B2488427 : Blo 1104625 2488427 := bstep (se 1 (by rfl) ⟨1866320, by rfl⟩ : syracuseStep 2488427 = 3732641) B3732641
theorem B16415135 : Blo 1104625 16415135 := bstep (se 1 (by rfl) ⟨12311351, by rfl⟩ : syracuseStep 16415135 = 24622703) B24622703
theorem B2491163 : Blo 1104625 2491163 := bstep (se 1 (by rfl) ⟨1868372, by rfl⟩ : syracuseStep 2491163 = 3736745) B3736745
theorem B9470803 : Blo 1104625 9470803 := bstep (se 1 (by rfl) ⟨7103102, by rfl⟩ : syracuseStep 9470803 = 14206205) B14206205
theorem B2491361 : Blo 1104625 2491361 := bstep (se 2 (by rfl) ⟨934260, by rfl⟩ : syracuseStep 2491361 = 1868521) B1868521
theorem B1869385 : Blo 1104625 1869385 := bstep (se 2 (by rfl) ⟨701019, by rfl⟩ : syracuseStep 1869385 = 1402039) B1402039
theorem B3540635 : Blo 1104625 3540635 := bstep (se 1 (by rfl) ⟨2655476, by rfl⟩ : syracuseStep 3540635 = 5310953) B5310953
theorem B1247143 : Blo 1104625 1247143 := bstep (se 1 (by rfl) ⟨935357, by rfl⟩ : syracuseStep 1247143 = 1870715) B1870715
theorem B2492585 : Blo 1104625 2492585 := bstep (se 2 (by rfl) ⟨934719, by rfl⟩ : syracuseStep 2492585 = 1869439) B1869439
theorem B2492927 : Blo 1104625 2492927 := bstep (se 1 (by rfl) ⟨1869695, by rfl⟩ : syracuseStep 2492927 = 3739391) B3739391
theorem B4197217 : Blo 1104625 4197217 := bstep (se 2 (by rfl) ⟨1573956, by rfl⟩ : syracuseStep 4197217 = 3147913) B3147913
theorem B4721597 : Blo 1104625 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B96933671 : Blo 1104625 96933671 := bstep (se 1 (by rfl) ⟨72700253, by rfl⟩ : syracuseStep 96933671 = 145400507) B145400507
theorem B5611679 : Blo 1104625 5611679 := bstep (se 1 (by rfl) ⟨4208759, by rfl⟩ : syracuseStep 5611679 = 8417519) B8417519
theorem B42475913 : Blo 1104625 42475913 := bstep (se 2 (by rfl) ⟨15928467, by rfl⟩ : syracuseStep 42475913 = 31856935) B31856935
theorem B86385203 : Blo 1104625 86385203 := bstep (se 1 (by rfl) ⟨64788902, by rfl⟩ : syracuseStep 86385203 = 129577805) B129577805
theorem B95659379 : Blo 1104625 95659379 := bstep (se 1 (by rfl) ⟨71744534, by rfl⟩ : syracuseStep 95659379 = 143489069) B143489069
theorem B6301111 : Blo 1104625 6301111 := bstep (se 1 (by rfl) ⟨4725833, by rfl⟩ : syracuseStep 6301111 = 9451667) B9451667
theorem B4728415 : Blo 1104625 4728415 := bstep (se 1 (by rfl) ⟨3546311, by rfl⟩ : syracuseStep 4728415 = 7092623) B7092623
theorem B10104257 : Blo 1104625 10104257 := bstep (se 2 (by rfl) ⟨3789096, by rfl⟩ : syracuseStep 10104257 = 7578193) B7578193
theorem B2797679 : Blo 1104625 2797679 := bstep (se 1 (by rfl) ⟨2098259, by rfl⟩ : syracuseStep 2797679 = 4196519) B4196519
theorem B7090391 : Blo 1104625 7090391 := bstep (se 1 (by rfl) ⟨5317793, by rfl⟩ : syracuseStep 7090391 = 10635587) B10635587
theorem B5977313 : Blo 1104625 5977313 := bstep (se 2 (by rfl) ⟨2241492, by rfl⟩ : syracuseStep 5977313 = 4482985) B4482985
theorem B2799431 : Blo 1104625 2799431 := bstep (se 1 (by rfl) ⟨2099573, by rfl⟩ : syracuseStep 2799431 = 4199147) B4199147
theorem B2799593 : Blo 1104625 2799593 := bstep (se 2 (by rfl) ⟨1049847, by rfl⟩ : syracuseStep 2799593 = 2099695) B2099695
theorem B23902391 : Blo 1104625 23902391 := bstep (se 1 (by rfl) ⟨17926793, by rfl⟩ : syracuseStep 23902391 = 35853587) B35853587
theorem B1818731 : Blo 1104625 1818731 := bstep (se 1 (by rfl) ⟨1364048, by rfl⟩ : syracuseStep 1818731 = 2728097) B2728097
theorem B258392429 : Blo 1104625 258392429 := bstep (se 3 (by rfl) ⟨48448580, by rfl⟩ : syracuseStep 258392429 = 96897161) B96897161
theorem B26919773 : Blo 1104625 26919773 := bstep (se 3 (by rfl) ⟨5047457, by rfl⟩ : syracuseStep 26919773 = 10094915) B10094915
theorem B2803481 : Blo 1104625 2803481 := bstep (se 2 (by rfl) ⟨1051305, by rfl⟩ : syracuseStep 2803481 = 2102611) B2102611
theorem B17975195 : Blo 1104625 17975195 := bstep (se 1 (by rfl) ⟨13481396, by rfl⟩ : syracuseStep 17975195 = 26962793) B26962793
theorem B1657001 : Blo 1104625 1657001 := bstep (se 2 (by rfl) ⟨621375, by rfl⟩ : syracuseStep 1657001 = 1242751) B1242751
theorem B21253265 : Blo 1104625 21253265 := bstep (se 2 (by rfl) ⟨7969974, by rfl⟩ : syracuseStep 21253265 = 15939949) B15939949
theorem B2805587 : Blo 1104625 2805587 := bstep (se 1 (by rfl) ⟨2104190, by rfl⟩ : syracuseStep 2805587 = 4208381) B4208381
theorem B1658951 : Blo 1104625 1658951 := bstep (se 1 (by rfl) ⟨1244213, by rfl⟩ : syracuseStep 1658951 = 2488427) B2488427
theorem B1661183 : Blo 1104625 1661183 := bstep (se 1 (by rfl) ⟨1245887, by rfl⟩ : syracuseStep 1661183 = 2491775) B2491775
theorem B1399999 : Blo 1104625 1399999 := bstep (se 1 (by rfl) ⟨1049999, by rfl⟩ : syracuseStep 1399999 = 2099999) B2099999
theorem B1105615 : Blo 1104625 1105615 := bstep (se 1 (by rfl) ⟨829211, by rfl⟩ : syracuseStep 1105615 = 1658423) B1658423
theorem B1105823 : Blo 1104625 1105823 := bstep (se 1 (by rfl) ⟨829367, by rfl⟩ : syracuseStep 1105823 = 1658735) B1658735
theorem B10641395 : Blo 1104625 10641395 := bstep (se 1 (by rfl) ⟨7981046, by rfl⟩ : syracuseStep 10641395 = 15962093) B15962093
theorem B1106031 : Blo 1104625 1106031 := bstep (se 1 (by rfl) ⟨829523, by rfl⟩ : syracuseStep 1106031 = 1659047) B1659047
theorem B1106687 : Blo 1104625 1106687 := bstep (se 1 (by rfl) ⟨830015, by rfl⟩ : syracuseStep 1106687 = 1660031) B1660031
theorem B4482155 : Blo 1104625 4482155 := bstep (se 1 (by rfl) ⟨3361616, by rfl⟩ : syracuseStep 4482155 = 6723233) B6723233
theorem B1107391 : Blo 1104625 1107391 := bstep (se 1 (by rfl) ⟨830543, by rfl⟩ : syracuseStep 1107391 = 1661087) B1661087
theorem B25945577 : Blo 1104625 25945577 := bstep (se 2 (by rfl) ⟨9729591, by rfl⟩ : syracuseStep 25945577 = 19459183) B19459183
theorem B1108079 : Blo 1104625 1108079 := bstep (se 1 (by rfl) ⟨831059, by rfl⟩ : syracuseStep 1108079 = 1662119) B1662119
theorem B5597423 : Blo 1104625 5597423 := bstep (se 1 (by rfl) ⟨4198067, by rfl⟩ : syracuseStep 5597423 = 8396135) B8396135
theorem B38365721 : Blo 1104625 38365721 := bstep (se 2 (by rfl) ⟨14387145, by rfl⟩ : syracuseStep 38365721 = 28774291) B28774291
theorem B5597747 : Blo 1104625 5597747 := bstep (se 1 (by rfl) ⟨4198310, by rfl⟩ : syracuseStep 5597747 = 8396621) B8396621
theorem B5991515 : Blo 1104625 5991515 := bstep (se 1 (by rfl) ⟨4493636, by rfl⟩ : syracuseStep 5991515 = 8987273) B8987273
theorem B11956733 : Blo 1104625 11956733 := bstep (se 3 (by rfl) ⟨2241887, by rfl⟩ : syracuseStep 11956733 = 4483775) B4483775
theorem B688747535 : Blo 1104625 688747535 := bstep (se 1 (by rfl) ⟨516560651, by rfl⟩ : syracuseStep 688747535 = 1033121303) B1033121303
theorem B2488823 : Blo 1104625 2488823 := bstep (se 1 (by rfl) ⟨1866617, by rfl⟩ : syracuseStep 2488823 = 3733235) B3733235
theorem B3734369 : Blo 1104625 3734369 := bstep (se 2 (by rfl) ⟨1400388, by rfl⟩ : syracuseStep 3734369 = 2800777) B2800777
theorem B10943423 : Blo 1104625 10943423 := bstep (se 1 (by rfl) ⟨8207567, by rfl⟩ : syracuseStep 10943423 = 16415135) B16415135
theorem B172261619 : Blo 1104625 172261619 := bstep (se 1 (by rfl) ⟨129196214, by rfl⟩ : syracuseStep 172261619 = 258392429) B258392429
theorem B4849949 : Blo 1104625 4849949 := bstep (se 3 (by rfl) ⟨909365, by rfl⟩ : syracuseStep 4849949 = 1818731) B1818731
theorem B2360423 : Blo 1104625 2360423 := bstep (se 1 (by rfl) ⟨1770317, by rfl⟩ : syracuseStep 2360423 = 3540635) B3540635
theorem B1868987 : Blo 1104625 1868987 := bstep (se 1 (by rfl) ⟨1401740, by rfl⟩ : syracuseStep 1868987 = 2803481) B2803481
theorem B3147731 : Blo 1104625 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B2492513 : Blo 1104625 2492513 := bstep (se 2 (by rfl) ⟨934692, by rfl⟩ : syracuseStep 2492513 = 1869385) B1869385
theorem B1870391 : Blo 1104625 1870391 := bstep (se 1 (by rfl) ⟨1402793, by rfl⟩ : syracuseStep 1870391 = 2805587) B2805587
theorem B64622447 : Blo 1104625 64622447 := bstep (se 1 (by rfl) ⟨48466835, by rfl⟩ : syracuseStep 64622447 = 96933671) B96933671
theorem B3741119 : Blo 1104625 3741119 := bstep (se 1 (by rfl) ⟨2805839, by rfl⟩ : syracuseStep 3741119 = 5611679) B5611679
theorem B28317275 : Blo 1104625 28317275 := bstep (se 1 (by rfl) ⟨21237956, by rfl⟩ : syracuseStep 28317275 = 42475913) B42475913
theorem B2988103 : Blo 1104625 2988103 := bstep (se 1 (by rfl) ⟨2241077, by rfl⟩ : syracuseStep 2988103 = 4482155) B4482155
theorem B63772919 : Blo 1104625 63772919 := bstep (se 1 (by rfl) ⟨47829689, by rfl⟩ : syracuseStep 63772919 = 95659379) B95659379
theorem B4726927 : Blo 1104625 4726927 := bstep (se 1 (by rfl) ⟨3545195, by rfl⟩ : syracuseStep 4726927 = 7090391) B7090391
theorem B7971155 : Blo 1104625 7971155 := bstep (se 1 (by rfl) ⟨5978366, by rfl⟩ : syracuseStep 7971155 = 11956733) B11956733
theorem B15934927 : Blo 1104625 15934927 := bstep (se 1 (by rfl) ⟨11951195, by rfl⟩ : syracuseStep 15934927 = 23902391) B23902391
theorem B12627737 : Blo 1104625 12627737 := bstep (se 2 (by rfl) ⟨4735401, by rfl⟩ : syracuseStep 12627737 = 9470803) B9470803
theorem B8401481 : Blo 1104625 8401481 := bstep (se 2 (by rfl) ⟨3150555, by rfl⟩ : syracuseStep 8401481 = 6301111) B6301111
theorem B14168843 : Blo 1104625 14168843 := bstep (se 1 (by rfl) ⟨10626632, by rfl⟩ : syracuseStep 14168843 = 21253265) B21253265
theorem B6304553 : Blo 1104625 6304553 := bstep (se 2 (by rfl) ⟨2364207, by rfl⟩ : syracuseStep 6304553 = 4728415) B4728415
theorem B7094263 : Blo 1104625 7094263 := bstep (se 1 (by rfl) ⟨5320697, by rfl⟩ : syracuseStep 7094263 = 10641395) B10641395
theorem B57590135 : Blo 1104625 57590135 := bstep (se 1 (by rfl) ⟨43192601, by rfl⟩ : syracuseStep 57590135 = 86385203) B86385203
theorem B25577147 : Blo 1104625 25577147 := bstep (se 1 (by rfl) ⟨19182860, by rfl⟩ : syracuseStep 25577147 = 38365721) B38365721
theorem B6736171 : Blo 1104625 6736171 := bstep (se 1 (by rfl) ⟨5052128, by rfl⟩ : syracuseStep 6736171 = 10104257) B10104257
theorem B459165023 : Blo 1104625 459165023 := bstep (se 1 (by rfl) ⟨344373767, by rfl⟩ : syracuseStep 459165023 = 688747535) B688747535
theorem B3984875 : Blo 1104625 3984875 := bstep (se 1 (by rfl) ⟨2988656, by rfl⟩ : syracuseStep 3984875 = 5977313) B5977313
theorem B1659215 : Blo 1104625 1659215 := bstep (se 1 (by rfl) ⟨1244411, by rfl⟩ : syracuseStep 1659215 = 2488823) B2488823
theorem B7295615 : Blo 1104625 7295615 := bstep (se 1 (by rfl) ⟨5471711, by rfl⟩ : syracuseStep 7295615 = 10943423) B10943423
theorem B1660775 : Blo 1104625 1660775 := bstep (se 1 (by rfl) ⟨1245581, by rfl⟩ : syracuseStep 1660775 = 2491163) B2491163
theorem B17946515 : Blo 1104625 17946515 := bstep (se 1 (by rfl) ⟨13459886, by rfl⟩ : syracuseStep 17946515 = 26919773) B26919773
theorem B1660907 : Blo 1104625 1660907 := bstep (se 1 (by rfl) ⟨1245680, by rfl⟩ : syracuseStep 1660907 = 2491361) B2491361
theorem B11983463 : Blo 1104625 11983463 := bstep (se 1 (by rfl) ⟨8987597, by rfl⟩ : syracuseStep 11983463 = 17975195) B17975195
theorem B1104667 : Blo 1104625 1104667 := bstep (se 1 (by rfl) ⟨828500, by rfl⟩ : syracuseStep 1104667 = 1657001) B1657001
theorem B1661723 : Blo 1104625 1661723 := bstep (se 1 (by rfl) ⟨1246292, by rfl⟩ : syracuseStep 1661723 = 2492585) B2492585
theorem B1661951 : Blo 1104625 1661951 := bstep (se 1 (by rfl) ⟨1246463, by rfl⟩ : syracuseStep 1661951 = 2492927) B2492927
theorem B1662857 : Blo 1104625 1662857 := bstep (se 2 (by rfl) ⟨623571, by rfl⟩ : syracuseStep 1662857 = 1247143) B1247143
theorem B1105967 : Blo 1104625 1105967 := bstep (se 1 (by rfl) ⟨829475, by rfl⟩ : syracuseStep 1105967 = 1658951) B1658951
theorem B5596289 : Blo 1104625 5596289 := bstep (se 2 (by rfl) ⟨2098608, by rfl⟩ : syracuseStep 5596289 = 4197217) B4197217
theorem B1107455 : Blo 1104625 1107455 := bstep (se 1 (by rfl) ⟨830591, by rfl⟩ : syracuseStep 1107455 = 1661183) B1661183
theorem B276752821 : Blo 1104625 276752821 := bstep (se 5 (by rfl) ⟨12972788, by rfl⟩ : syracuseStep 276752821 = 25945577) B25945577
theorem B3731615 : Blo 1104625 3731615 := bstep (se 1 (by rfl) ⟨2798711, by rfl⟩ : syracuseStep 3731615 = 5597423) B5597423
theorem B3731831 : Blo 1104625 3731831 := bstep (se 1 (by rfl) ⟨2798873, by rfl⟩ : syracuseStep 3731831 = 5597747) B5597747
theorem B3994343 : Blo 1104625 3994343 := bstep (se 1 (by rfl) ⟨2995757, by rfl⟩ : syracuseStep 3994343 = 5991515) B5991515
theorem B1865119 : Blo 1104625 1865119 := bstep (se 1 (by rfl) ⟨1398839, by rfl⟩ : syracuseStep 1865119 = 2797679) B2797679
theorem B1866287 : Blo 1104625 1866287 := bstep (se 1 (by rfl) ⟨1399715, by rfl⟩ : syracuseStep 1866287 = 2799431) B2799431
theorem B1866395 : Blo 1104625 1866395 := bstep (se 1 (by rfl) ⟨1399796, by rfl⟩ : syracuseStep 1866395 = 2799593) B2799593
theorem B1866665 : Blo 1104625 1866665 := bstep (se 2 (by rfl) ⟨699999, by rfl⟩ : syracuseStep 1866665 = 1399999) B1399999
theorem B2489579 : Blo 1104625 2489579 := bstep (se 1 (by rfl) ⟨1867184, by rfl⟩ : syracuseStep 2489579 = 3734369) B3734369
theorem B1573615 : Blo 1104625 1573615 := bstep (se 1 (by rfl) ⟨1180211, by rfl⟩ : syracuseStep 1573615 = 2360423) B2360423
theorem B1245991 : Blo 1104625 1245991 := bstep (se 1 (by rfl) ⟨934493, by rfl⟩ : syracuseStep 1245991 = 1868987) B1868987
theorem B2098487 : Blo 1104625 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B1246927 : Blo 1104625 1246927 := bstep (se 1 (by rfl) ⟨935195, by rfl⟩ : syracuseStep 1246927 = 1870391) B1870391
theorem B2656583 : Blo 1104625 2656583 := bstep (se 1 (by rfl) ⟨1992437, by rfl⟩ : syracuseStep 2656583 = 3984875) B3984875
theorem B8981561 : Blo 1104625 8981561 := bstep (se 2 (by rfl) ⟨3368085, by rfl⟩ : syracuseStep 8981561 = 6736171) B6736171
theorem B369003761 : Blo 1104625 369003761 := bstep (se 2 (by rfl) ⟨138376410, by rfl⟩ : syracuseStep 369003761 = 276752821) B276752821
theorem B2494079 : Blo 1104625 2494079 := bstep (se 1 (by rfl) ⟨1870559, by rfl⟩ : syracuseStep 2494079 = 3741119) B3741119
theorem B18878183 : Blo 1104625 18878183 := bstep (se 1 (by rfl) ⟨14158637, by rfl⟩ : syracuseStep 18878183 = 28317275) B28317275
theorem B11964343 : Blo 1104625 11964343 := bstep (se 1 (by rfl) ⟨8973257, by rfl⟩ : syracuseStep 11964343 = 17946515) B17946515
theorem B5314103 : Blo 1104625 5314103 := bstep (se 1 (by rfl) ⟨3985577, by rfl⟩ : syracuseStep 5314103 = 7971155) B7971155
theorem B2662895 : Blo 1104625 2662895 := bstep (se 1 (by rfl) ⟨1997171, by rfl⟩ : syracuseStep 2662895 = 3994343) B3994343
theorem B9445895 : Blo 1104625 9445895 := bstep (se 1 (by rfl) ⟨7084421, by rfl⟩ : syracuseStep 9445895 = 14168843) B14168843
theorem B4203035 : Blo 1104625 4203035 := bstep (se 1 (by rfl) ⟨3152276, by rfl⟩ : syracuseStep 4203035 = 6304553) B6304553
theorem B6302569 : Blo 1104625 6302569 := bstep (se 2 (by rfl) ⟨2363463, by rfl⟩ : syracuseStep 6302569 = 4726927) B4726927
theorem B17051431 : Blo 1104625 17051431 := bstep (se 1 (by rfl) ⟨12788573, by rfl⟩ : syracuseStep 17051431 = 25577147) B25577147
theorem B21246569 : Blo 1104625 21246569 := bstep (se 2 (by rfl) ⟨7967463, by rfl⟩ : syracuseStep 21246569 = 15934927) B15934927
theorem B4863743 : Blo 1104625 4863743 := bstep (se 1 (by rfl) ⟨3647807, by rfl⟩ : syracuseStep 4863743 = 7295615) B7295615
theorem B42515279 : Blo 1104625 42515279 := bstep (se 1 (by rfl) ⟨31886459, by rfl⟩ : syracuseStep 42515279 = 63772919) B63772919
theorem B3984137 : Blo 1104625 3984137 := bstep (se 2 (by rfl) ⟨1494051, by rfl⟩ : syracuseStep 3984137 = 2988103) B2988103
theorem B1659719 : Blo 1104625 1659719 := bstep (se 1 (by rfl) ⟨1244789, by rfl⟩ : syracuseStep 1659719 = 2489579) B2489579
theorem B9459017 : Blo 1104625 9459017 := bstep (se 2 (by rfl) ⟨3547131, by rfl⟩ : syracuseStep 9459017 = 7094263) B7094263
theorem B114841079 : Blo 1104625 114841079 := bstep (se 1 (by rfl) ⟨86130809, by rfl⟩ : syracuseStep 114841079 = 172261619) B172261619
theorem B3233299 : Blo 1104625 3233299 := bstep (se 1 (by rfl) ⟨2424974, by rfl⟩ : syracuseStep 3233299 = 4849949) B4849949
theorem B38393423 : Blo 1104625 38393423 := bstep (se 1 (by rfl) ⟨28795067, by rfl⟩ : syracuseStep 38393423 = 57590135) B57590135
theorem B1661675 : Blo 1104625 1661675 := bstep (se 1 (by rfl) ⟨1246256, by rfl⟩ : syracuseStep 1661675 = 2492513) B2492513
theorem B306110015 : Blo 1104625 306110015 := bstep (se 1 (by rfl) ⟨229582511, by rfl⟩ : syracuseStep 306110015 = 459165023) B459165023
theorem B43081631 : Blo 1104625 43081631 := bstep (se 1 (by rfl) ⟨32311223, by rfl⟩ : syracuseStep 43081631 = 64622447) B64622447
theorem B1106143 : Blo 1104625 1106143 := bstep (se 1 (by rfl) ⟨829607, by rfl⟩ : syracuseStep 1106143 = 1659215) B1659215
theorem B1107183 : Blo 1104625 1107183 := bstep (se 1 (by rfl) ⟨830387, by rfl⟩ : syracuseStep 1107183 = 1660775) B1660775
theorem B1107271 : Blo 1104625 1107271 := bstep (se 1 (by rfl) ⟨830453, by rfl⟩ : syracuseStep 1107271 = 1660907) B1660907
theorem B7988975 : Blo 1104625 7988975 := bstep (se 1 (by rfl) ⟨5991731, by rfl⟩ : syracuseStep 7988975 = 11983463) B11983463
theorem B1107815 : Blo 1104625 1107815 := bstep (se 1 (by rfl) ⟨830861, by rfl⟩ : syracuseStep 1107815 = 1661723) B1661723
theorem B1107967 : Blo 1104625 1107967 := bstep (se 1 (by rfl) ⟨830975, by rfl⟩ : syracuseStep 1107967 = 1661951) B1661951
theorem B1108571 : Blo 1104625 1108571 := bstep (se 1 (by rfl) ⟨831428, by rfl⟩ : syracuseStep 1108571 = 1662857) B1662857
theorem B3730859 : Blo 1104625 3730859 := bstep (se 1 (by rfl) ⟨2798144, by rfl⟩ : syracuseStep 3730859 = 5596289) B5596289
theorem B2486825 : Blo 1104625 2486825 := bstep (se 2 (by rfl) ⟨932559, by rfl⟩ : syracuseStep 2486825 = 1865119) B1865119
theorem B8418491 : Blo 1104625 8418491 := bstep (se 1 (by rfl) ⟨6313868, by rfl⟩ : syracuseStep 8418491 = 12627737) B12627737
theorem B2487743 : Blo 1104625 2487743 := bstep (se 1 (by rfl) ⟨1865807, by rfl⟩ : syracuseStep 2487743 = 3731615) B3731615
theorem B2487887 : Blo 1104625 2487887 := bstep (se 1 (by rfl) ⟨1865915, by rfl⟩ : syracuseStep 2487887 = 3731831) B3731831
theorem B5600987 : Blo 1104625 5600987 := bstep (se 1 (by rfl) ⟨4200740, by rfl⟩ : syracuseStep 5600987 = 8401481) B8401481
theorem B1244191 : Blo 1104625 1244191 := bstep (se 1 (by rfl) ⟨933143, by rfl⟩ : syracuseStep 1244191 = 1866287) B1866287
theorem B1244263 : Blo 1104625 1244263 := bstep (se 1 (by rfl) ⟨933197, by rfl⟩ : syracuseStep 1244263 = 1866395) B1866395
theorem B1244443 : Blo 1104625 1244443 := bstep (se 1 (by rfl) ⟨933332, by rfl⟩ : syracuseStep 1244443 = 1866665) B1866665
theorem B2098153 : Blo 1104625 2098153 := bstep (se 2 (by rfl) ⟨786807, by rfl⟩ : syracuseStep 2098153 = 1573615) B1573615
theorem B1771055 : Blo 1104625 1771055 := bstep (se 1 (by rfl) ⟨1328291, by rfl⟩ : syracuseStep 1771055 = 2656583) B2656583
theorem B2656091 : Blo 1104625 2656091 := bstep (se 1 (by rfl) ⟨1992068, by rfl⟩ : syracuseStep 2656091 = 3984137) B3984137
theorem B12585455 : Blo 1104625 12585455 := bstep (se 1 (by rfl) ⟨9439091, by rfl⟩ : syracuseStep 12585455 = 18878183) B18878183
theorem B3542735 : Blo 1104625 3542735 := bstep (se 1 (by rfl) ⟨2657051, by rfl⟩ : syracuseStep 3542735 = 5314103) B5314103
theorem B25595615 : Blo 1104625 25595615 := bstep (se 1 (by rfl) ⟨19196711, by rfl⟩ : syracuseStep 25595615 = 38393423) B38393423
theorem B6297263 : Blo 1104625 6297263 := bstep (se 1 (by rfl) ⟨4722947, by rfl⟩ : syracuseStep 6297263 = 9445895) B9445895
theorem B14164379 : Blo 1104625 14164379 := bstep (se 1 (by rfl) ⟨10623284, by rfl⟩ : syracuseStep 14164379 = 21246569) B21246569
theorem B5612327 : Blo 1104625 5612327 := bstep (se 1 (by rfl) ⟨4209245, by rfl⟩ : syracuseStep 5612327 = 8418491) B8418491
theorem B246002507 : Blo 1104625 246002507 := bstep (se 1 (by rfl) ⟨184501880, by rfl⟩ : syracuseStep 246002507 = 369003761) B369003761
theorem B6306011 : Blo 1104625 6306011 := bstep (se 1 (by rfl) ⟨4729508, by rfl⟩ : syracuseStep 6306011 = 9459017) B9459017
theorem B76560719 : Blo 1104625 76560719 := bstep (se 1 (by rfl) ⟨57420539, by rfl⟩ : syracuseStep 76560719 = 114841079) B114841079
theorem B8403425 : Blo 1104625 8403425 := bstep (se 2 (by rfl) ⟨3151284, by rfl⟩ : syracuseStep 8403425 = 6302569) B6302569
theorem B28721087 : Blo 1104625 28721087 := bstep (se 1 (by rfl) ⟨21540815, by rfl⟩ : syracuseStep 28721087 = 43081631) B43081631
theorem B2802023 : Blo 1104625 2802023 := bstep (se 1 (by rfl) ⟨2101517, by rfl⟩ : syracuseStep 2802023 = 4203035) B4203035
theorem B5325983 : Blo 1104625 5325983 := bstep (se 1 (by rfl) ⟨3994487, by rfl⟩ : syracuseStep 5325983 = 7988975) B7988975
theorem B4311065 : Blo 1104625 4311065 := bstep (se 2 (by rfl) ⟨1616649, by rfl⟩ : syracuseStep 4311065 = 3233299) B3233299
theorem B1657883 : Blo 1104625 1657883 := bstep (se 1 (by rfl) ⟨1243412, by rfl⟩ : syracuseStep 1657883 = 2486825) B2486825
theorem B1658495 : Blo 1104625 1658495 := bstep (se 1 (by rfl) ⟨1243871, by rfl⟩ : syracuseStep 1658495 = 2487743) B2487743
theorem B1658591 : Blo 1104625 1658591 := bstep (se 1 (by rfl) ⟨1243943, by rfl⟩ : syracuseStep 1658591 = 2487887) B2487887
theorem B1658921 : Blo 1104625 1658921 := bstep (se 2 (by rfl) ⟨622095, by rfl⟩ : syracuseStep 1658921 = 1244191) B1244191
theorem B1659017 : Blo 1104625 1659017 := bstep (se 2 (by rfl) ⟨622131, by rfl⟩ : syracuseStep 1659017 = 1244263) B1244263
theorem B1659257 : Blo 1104625 1659257 := bstep (se 2 (by rfl) ⟨622221, by rfl⟩ : syracuseStep 1659257 = 1244443) B1244443
theorem B1661321 : Blo 1104625 1661321 := bstep (se 2 (by rfl) ⟨622995, by rfl⟩ : syracuseStep 1661321 = 1245991) B1245991
theorem B7101053 : Blo 1104625 7101053 := bstep (se 3 (by rfl) ⟨1331447, by rfl⟩ : syracuseStep 7101053 = 2662895) B2662895
theorem B1662569 : Blo 1104625 1662569 := bstep (se 2 (by rfl) ⟨623463, by rfl⟩ : syracuseStep 1662569 = 1246927) B1246927
theorem B1662719 : Blo 1104625 1662719 := bstep (se 1 (by rfl) ⟨1247039, by rfl⟩ : syracuseStep 1662719 = 2494079) B2494079
theorem B1106479 : Blo 1104625 1106479 := bstep (se 1 (by rfl) ⟨829859, by rfl⟩ : syracuseStep 1106479 = 1659719) B1659719
theorem B5595965 : Blo 1104625 5595965 := bstep (se 3 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 5595965 = 2098487) B2098487
theorem B1107783 : Blo 1104625 1107783 := bstep (se 1 (by rfl) ⟨830837, by rfl⟩ : syracuseStep 1107783 = 1661675) B1661675
theorem B204073343 : Blo 1104625 204073343 := bstep (se 1 (by rfl) ⟨153055007, by rfl⟩ : syracuseStep 204073343 = 306110015) B306110015
theorem B22735241 : Blo 1104625 22735241 := bstep (se 2 (by rfl) ⟨8525715, by rfl⟩ : syracuseStep 22735241 = 17051431) B17051431
theorem B15952457 : Blo 1104625 15952457 := bstep (se 2 (by rfl) ⟨5982171, by rfl⟩ : syracuseStep 15952457 = 11964343) B11964343
theorem B2487239 : Blo 1104625 2487239 := bstep (se 1 (by rfl) ⟨1865429, by rfl⟩ : syracuseStep 2487239 = 3730859) B3730859
theorem B23950829 : Blo 1104625 23950829 := bstep (se 3 (by rfl) ⟨4490780, by rfl⟩ : syracuseStep 23950829 = 8981561) B8981561
theorem B3733991 : Blo 1104625 3733991 := bstep (se 1 (by rfl) ⟨2800493, by rfl⟩ : syracuseStep 3733991 = 5600987) B5600987
theorem B3242495 : Blo 1104625 3242495 := bstep (se 1 (by rfl) ⟨2431871, by rfl⟩ : syracuseStep 3242495 = 4863743) B4863743
theorem B28343519 : Blo 1104625 28343519 := bstep (se 1 (by rfl) ⟨21257639, by rfl⟩ : syracuseStep 28343519 = 42515279) B42515279
theorem B1868015 : Blo 1104625 1868015 := bstep (se 1 (by rfl) ⟨1401011, by rfl⟩ : syracuseStep 1868015 = 2802023) B2802023
theorem B1180703 : Blo 1104625 1180703 := bstep (se 1 (by rfl) ⟨885527, by rfl⟩ : syracuseStep 1180703 = 1771055) B1771055
theorem B8390303 : Blo 1104625 8390303 := bstep (se 1 (by rfl) ⟨6292727, by rfl⟩ : syracuseStep 8390303 = 12585455) B12585455
theorem B4198175 : Blo 1104625 4198175 := bstep (se 1 (by rfl) ⟨3148631, by rfl⟩ : syracuseStep 4198175 = 6297263) B6297263
theorem B7082909 : Blo 1104625 7082909 := bstep (se 3 (by rfl) ⟨1328045, by rfl⟩ : syracuseStep 7082909 = 2656091) B2656091
theorem B9442919 : Blo 1104625 9442919 := bstep (se 1 (by rfl) ⟨7082189, by rfl⟩ : syracuseStep 9442919 = 14164379) B14164379
theorem B3741551 : Blo 1104625 3741551 := bstep (se 1 (by rfl) ⟨2806163, by rfl⟩ : syracuseStep 3741551 = 5612327) B5612327
theorem B15967219 : Blo 1104625 15967219 := bstep (se 1 (by rfl) ⟨11975414, by rfl⟩ : syracuseStep 15967219 = 23950829) B23950829
theorem B4204007 : Blo 1104625 4204007 := bstep (se 1 (by rfl) ⟨3153005, by rfl⟩ : syracuseStep 4204007 = 6306011) B6306011
theorem B9447293 : Blo 1104625 9447293 := bstep (se 3 (by rfl) ⟨1771367, by rfl⟩ : syracuseStep 9447293 = 3542735) B3542735
theorem B19147391 : Blo 1104625 19147391 := bstep (se 1 (by rfl) ⟨14360543, by rfl⟩ : syracuseStep 19147391 = 28721087) B28721087
theorem B3550655 : Blo 1104625 3550655 := bstep (se 1 (by rfl) ⟨2662991, by rfl⟩ : syracuseStep 3550655 = 5325983) B5325983
theorem B2797537 : Blo 1104625 2797537 := bstep (se 2 (by rfl) ⟨1049076, by rfl⟩ : syracuseStep 2797537 = 2098153) B2098153
theorem B4734035 : Blo 1104625 4734035 := bstep (se 1 (by rfl) ⟨3550526, by rfl⟩ : syracuseStep 4734035 = 7101053) B7101053
theorem B204161917 : Blo 1104625 204161917 := bstep (se 3 (by rfl) ⟨38280359, by rfl⟩ : syracuseStep 204161917 = 76560719) B76560719
theorem B15156827 : Blo 1104625 15156827 := bstep (se 1 (by rfl) ⟨11367620, by rfl⟩ : syracuseStep 15156827 = 22735241) B22735241
theorem B10634971 : Blo 1104625 10634971 := bstep (se 1 (by rfl) ⟨7976228, by rfl⟩ : syracuseStep 10634971 = 15952457) B15952457
theorem B1658159 : Blo 1104625 1658159 := bstep (se 1 (by rfl) ⟨1243619, by rfl⟩ : syracuseStep 1658159 = 2487239) B2487239
theorem B18895679 : Blo 1104625 18895679 := bstep (se 1 (by rfl) ⟨14171759, by rfl⟩ : syracuseStep 18895679 = 28343519) B28343519
theorem B2874043 : Blo 1104625 2874043 := bstep (se 1 (by rfl) ⟨2155532, by rfl⟩ : syracuseStep 2874043 = 4311065) B4311065
theorem B1105255 : Blo 1104625 1105255 := bstep (se 1 (by rfl) ⟨828941, by rfl⟩ : syracuseStep 1105255 = 1657883) B1657883
theorem B1105663 : Blo 1104625 1105663 := bstep (se 1 (by rfl) ⟨829247, by rfl⟩ : syracuseStep 1105663 = 1658495) B1658495
theorem B1105727 : Blo 1104625 1105727 := bstep (se 1 (by rfl) ⟨829295, by rfl⟩ : syracuseStep 1105727 = 1658591) B1658591
theorem B1105947 : Blo 1104625 1105947 := bstep (se 1 (by rfl) ⟨829460, by rfl⟩ : syracuseStep 1105947 = 1658921) B1658921
theorem B1106011 : Blo 1104625 1106011 := bstep (se 1 (by rfl) ⟨829508, by rfl⟩ : syracuseStep 1106011 = 1659017) B1659017
theorem B1106171 : Blo 1104625 1106171 := bstep (se 1 (by rfl) ⟨829628, by rfl⟩ : syracuseStep 1106171 = 1659257) B1659257
theorem B1107547 : Blo 1104625 1107547 := bstep (se 1 (by rfl) ⟨830660, by rfl⟩ : syracuseStep 1107547 = 1661321) B1661321
theorem B1108379 : Blo 1104625 1108379 := bstep (se 1 (by rfl) ⟨831284, by rfl⟩ : syracuseStep 1108379 = 1662569) B1662569
theorem B1108479 : Blo 1104625 1108479 := bstep (se 1 (by rfl) ⟨831359, by rfl⟩ : syracuseStep 1108479 = 1662719) B1662719
theorem B3730643 : Blo 1104625 3730643 := bstep (se 1 (by rfl) ⟨2797982, by rfl⟩ : syracuseStep 3730643 = 5595965) B5595965
theorem B8646653 : Blo 1104625 8646653 := bstep (se 3 (by rfl) ⟨1621247, by rfl⟩ : syracuseStep 8646653 = 3242495) B3242495
theorem B136048895 : Blo 1104625 136048895 := bstep (se 1 (by rfl) ⟨102036671, by rfl⟩ : syracuseStep 136048895 = 204073343) B204073343
theorem B164001671 : Blo 1104625 164001671 := bstep (se 1 (by rfl) ⟨123001253, by rfl⟩ : syracuseStep 164001671 = 246002507) B246002507
theorem B5602283 : Blo 1104625 5602283 := bstep (se 1 (by rfl) ⟨4201712, by rfl⟩ : syracuseStep 5602283 = 8403425) B8403425
theorem B2489327 : Blo 1104625 2489327 := bstep (se 1 (by rfl) ⟨1866995, by rfl⟩ : syracuseStep 2489327 = 3733991) B3733991
theorem B68254973 : Blo 1104625 68254973 := bstep (se 3 (by rfl) ⟨12797807, by rfl⟩ : syracuseStep 68254973 = 25595615) B25595615
theorem B1245343 : Blo 1104625 1245343 := bstep (se 1 (by rfl) ⟨934007, by rfl⟩ : syracuseStep 1245343 = 1868015) B1868015
theorem B3148541 : Blo 1104625 3148541 := bstep (se 3 (by rfl) ⟨590351, by rfl⟩ : syracuseStep 3148541 = 1180703) B1180703
theorem B4721939 : Blo 1104625 4721939 := bstep (se 1 (by rfl) ⟨3541454, by rfl⟩ : syracuseStep 4721939 = 7082909) B7082909
theorem B6295279 : Blo 1104625 6295279 := bstep (se 1 (by rfl) ⟨4721459, by rfl⟩ : syracuseStep 6295279 = 9442919) B9442919
theorem B2494367 : Blo 1104625 2494367 := bstep (se 1 (by rfl) ⟨1870775, by rfl⟩ : syracuseStep 2494367 = 3741551) B3741551
theorem B6298195 : Blo 1104625 6298195 := bstep (se 1 (by rfl) ⟨4723646, by rfl⟩ : syracuseStep 6298195 = 9447293) B9447293
theorem B3156023 : Blo 1104625 3156023 := bstep (se 1 (by rfl) ⟨2367017, by rfl⟩ : syracuseStep 3156023 = 4734035) B4734035
theorem B10104551 : Blo 1104625 10104551 := bstep (se 1 (by rfl) ⟨7578413, by rfl⟩ : syracuseStep 10104551 = 15156827) B15156827
theorem B272215889 : Blo 1104625 272215889 := bstep (se 2 (by rfl) ⟨102080958, by rfl⟩ : syracuseStep 272215889 = 204161917) B204161917
theorem B2798783 : Blo 1104625 2798783 := bstep (se 1 (by rfl) ⟨2099087, by rfl⟩ : syracuseStep 2798783 = 4198175) B4198175
theorem B12597119 : Blo 1104625 12597119 := bstep (se 1 (by rfl) ⟨9447839, by rfl⟩ : syracuseStep 12597119 = 18895679) B18895679
theorem B2802671 : Blo 1104625 2802671 := bstep (se 1 (by rfl) ⟨2102003, by rfl⟩ : syracuseStep 2802671 = 4204007) B4204007
theorem B12764927 : Blo 1104625 12764927 := bstep (se 1 (by rfl) ⟨9573695, by rfl⟩ : syracuseStep 12764927 = 19147391) B19147391
theorem B109334447 : Blo 1104625 109334447 := bstep (se 1 (by rfl) ⟨82000835, by rfl⟩ : syracuseStep 109334447 = 164001671) B164001671
theorem B1659551 : Blo 1104625 1659551 := bstep (se 1 (by rfl) ⟨1244663, by rfl⟩ : syracuseStep 1659551 = 2489327) B2489327
theorem B45503315 : Blo 1104625 45503315 := bstep (se 1 (by rfl) ⟨34127486, by rfl⟩ : syracuseStep 45503315 = 68254973) B68254973
theorem B23057741 : Blo 1104625 23057741 := bstep (se 3 (by rfl) ⟨4323326, by rfl⟩ : syracuseStep 23057741 = 8646653) B8646653
theorem B5593535 : Blo 1104625 5593535 := bstep (se 1 (by rfl) ⟨4195151, by rfl⟩ : syracuseStep 5593535 = 8390303) B8390303
theorem B21289625 : Blo 1104625 21289625 := bstep (se 2 (by rfl) ⟨7983609, by rfl⟩ : syracuseStep 21289625 = 15967219) B15967219
theorem B1105439 : Blo 1104625 1105439 := bstep (se 1 (by rfl) ⟨829079, by rfl⟩ : syracuseStep 1105439 = 1658159) B1658159
theorem B14179961 : Blo 1104625 14179961 := bstep (se 2 (by rfl) ⟨5317485, by rfl⟩ : syracuseStep 14179961 = 10634971) B10634971
theorem B3730049 : Blo 1104625 3730049 := bstep (se 2 (by rfl) ⟨1398768, by rfl⟩ : syracuseStep 3730049 = 2797537) B2797537
theorem B2487095 : Blo 1104625 2487095 := bstep (se 1 (by rfl) ⟨1865321, by rfl⟩ : syracuseStep 2487095 = 3730643) B3730643
theorem B90699263 : Blo 1104625 90699263 := bstep (se 1 (by rfl) ⟨68024447, by rfl⟩ : syracuseStep 90699263 = 136048895) B136048895
theorem B3832057 : Blo 1104625 3832057 := bstep (se 2 (by rfl) ⟨1437021, by rfl⟩ : syracuseStep 3832057 = 2874043) B2874043
theorem B9468413 : Blo 1104625 9468413 := bstep (se 3 (by rfl) ⟨1775327, by rfl⟩ : syracuseStep 9468413 = 3550655) B3550655
theorem B3734855 : Blo 1104625 3734855 := bstep (se 1 (by rfl) ⟨2801141, by rfl⟩ : syracuseStep 3734855 = 5602283) B5602283
theorem B1868447 : Blo 1104625 1868447 := bstep (se 1 (by rfl) ⟨1401335, by rfl⟩ : syracuseStep 1868447 = 2802671) B2802671
theorem B2099027 : Blo 1104625 2099027 := bstep (se 1 (by rfl) ⟨1574270, by rfl⟩ : syracuseStep 2099027 = 3148541) B3148541
theorem B3147959 : Blo 1104625 3147959 := bstep (se 1 (by rfl) ⟨2360969, by rfl⟩ : syracuseStep 3147959 = 4721939) B4721939
theorem B14193083 : Blo 1104625 14193083 := bstep (se 1 (by rfl) ⟨10644812, by rfl⟩ : syracuseStep 14193083 = 21289625) B21289625
theorem B8393705 : Blo 1104625 8393705 := bstep (se 2 (by rfl) ⟨3147639, by rfl⟩ : syracuseStep 8393705 = 6295279) B6295279
theorem B181477259 : Blo 1104625 181477259 := bstep (se 1 (by rfl) ⟨136107944, by rfl⟩ : syracuseStep 181477259 = 272215889) B272215889
theorem B8397593 : Blo 1104625 8397593 := bstep (se 2 (by rfl) ⟨3149097, by rfl⟩ : syracuseStep 8397593 = 6298195) B6298195
theorem B60466175 : Blo 1104625 60466175 := bstep (se 1 (by rfl) ⟨45349631, by rfl⟩ : syracuseStep 60466175 = 90699263) B90699263
theorem B8398079 : Blo 1104625 8398079 := bstep (se 1 (by rfl) ⟨6298559, by rfl⟩ : syracuseStep 8398079 = 12597119) B12597119
theorem B72889631 : Blo 1104625 72889631 := bstep (se 1 (by rfl) ⟨54667223, by rfl⟩ : syracuseStep 72889631 = 109334447) B109334447
theorem B61487309 : Blo 1104625 61487309 := bstep (se 3 (by rfl) ⟨11528870, by rfl⟩ : syracuseStep 61487309 = 23057741) B23057741
theorem B9453307 : Blo 1104625 9453307 := bstep (se 1 (by rfl) ⟨7089980, by rfl⟩ : syracuseStep 9453307 = 14179961) B14179961
theorem B6736367 : Blo 1104625 6736367 := bstep (se 1 (by rfl) ⟨5052275, by rfl⟩ : syracuseStep 6736367 = 10104551) B10104551
theorem B1658063 : Blo 1104625 1658063 := bstep (se 1 (by rfl) ⟨1243547, by rfl⟩ : syracuseStep 1658063 = 2487095) B2487095
theorem B6312275 : Blo 1104625 6312275 := bstep (se 1 (by rfl) ⟨4734206, by rfl⟩ : syracuseStep 6312275 = 9468413) B9468413
theorem B1660457 : Blo 1104625 1660457 := bstep (se 2 (by rfl) ⟨622671, by rfl⟩ : syracuseStep 1660457 = 1245343) B1245343
theorem B8509951 : Blo 1104625 8509951 := bstep (se 1 (by rfl) ⟨6382463, by rfl⟩ : syracuseStep 8509951 = 12764927) B12764927
theorem B1662911 : Blo 1104625 1662911 := bstep (se 1 (by rfl) ⟨1247183, by rfl⟩ : syracuseStep 1662911 = 2494367) B2494367
theorem B1106367 : Blo 1104625 1106367 := bstep (se 1 (by rfl) ⟨829775, by rfl⟩ : syracuseStep 1106367 = 1659551) B1659551
theorem B30335543 : Blo 1104625 30335543 := bstep (se 1 (by rfl) ⟨22751657, by rfl⟩ : syracuseStep 30335543 = 45503315) B45503315
theorem B3729023 : Blo 1104625 3729023 := bstep (se 1 (by rfl) ⟨2796767, by rfl⟩ : syracuseStep 3729023 = 5593535) B5593535
theorem B8416061 : Blo 1104625 8416061 := bstep (se 3 (by rfl) ⟨1578011, by rfl⟩ : syracuseStep 8416061 = 3156023) B3156023
theorem B2486699 : Blo 1104625 2486699 := bstep (se 1 (by rfl) ⟨1865024, by rfl⟩ : syracuseStep 2486699 = 3730049) B3730049
theorem B5109409 : Blo 1104625 5109409 := bstep (se 2 (by rfl) ⟨1916028, by rfl⟩ : syracuseStep 5109409 = 3832057) B3832057
theorem B1865855 : Blo 1104625 1865855 := bstep (se 1 (by rfl) ⟨1399391, by rfl⟩ : syracuseStep 1865855 = 2798783) B2798783
theorem B2489903 : Blo 1104625 2489903 := bstep (se 1 (by rfl) ⟨1867427, by rfl⟩ : syracuseStep 2489903 = 3734855) B3734855
theorem B1245631 : Blo 1104625 1245631 := bstep (se 1 (by rfl) ⟨934223, by rfl⟩ : syracuseStep 1245631 = 1868447) B1868447
theorem B2098639 : Blo 1104625 2098639 := bstep (se 1 (by rfl) ⟨1573979, by rfl⟩ : syracuseStep 2098639 = 3147959) B3147959
theorem B4490911 : Blo 1104625 4490911 := bstep (se 1 (by rfl) ⟨3368183, by rfl⟩ : syracuseStep 4490911 = 6736367) B6736367
theorem B120984839 : Blo 1104625 120984839 := bstep (se 1 (by rfl) ⟨90738629, by rfl⟩ : syracuseStep 120984839 = 181477259) B181477259
theorem B20223695 : Blo 1104625 20223695 := bstep (se 1 (by rfl) ⟨15167771, by rfl⟩ : syracuseStep 20223695 = 30335543) B30335543
theorem B40310783 : Blo 1104625 40310783 := bstep (se 1 (by rfl) ⟨30233087, by rfl⟩ : syracuseStep 40310783 = 60466175) B60466175
theorem B5610707 : Blo 1104625 5610707 := bstep (se 1 (by rfl) ⟨4208030, by rfl⟩ : syracuseStep 5610707 = 8416061) B8416061
theorem B11346601 : Blo 1104625 11346601 := bstep (se 2 (by rfl) ⟨4254975, by rfl⟩ : syracuseStep 11346601 = 8509951) B8509951
theorem B4208183 : Blo 1104625 4208183 := bstep (se 1 (by rfl) ⟨3156137, by rfl⟩ : syracuseStep 4208183 = 6312275) B6312275
theorem B1657799 : Blo 1104625 1657799 := bstep (se 1 (by rfl) ⟨1243349, by rfl⟩ : syracuseStep 1657799 = 2486699) B2486699
theorem B27250181 : Blo 1104625 27250181 := bstep (se 4 (by rfl) ⟨2554704, by rfl⟩ : syracuseStep 27250181 = 5109409) B5109409
theorem B12604409 : Blo 1104625 12604409 := bstep (se 2 (by rfl) ⟨4726653, by rfl⟩ : syracuseStep 12604409 = 9453307) B9453307
theorem B1659935 : Blo 1104625 1659935 := bstep (se 1 (by rfl) ⟨1244951, by rfl⟩ : syracuseStep 1659935 = 2489903) B2489903
theorem B1399351 : Blo 1104625 1399351 := bstep (se 1 (by rfl) ⟨1049513, by rfl⟩ : syracuseStep 1399351 = 2099027) B2099027
theorem B1105375 : Blo 1104625 1105375 := bstep (se 1 (by rfl) ⟨829031, by rfl⟩ : syracuseStep 1105375 = 1658063) B1658063
theorem B9462055 : Blo 1104625 9462055 := bstep (se 1 (by rfl) ⟨7096541, by rfl⟩ : syracuseStep 9462055 = 14193083) B14193083
theorem B5595803 : Blo 1104625 5595803 := bstep (se 1 (by rfl) ⟨4196852, by rfl⟩ : syracuseStep 5595803 = 8393705) B8393705
theorem B1106971 : Blo 1104625 1106971 := bstep (se 1 (by rfl) ⟨830228, by rfl⟩ : syracuseStep 1106971 = 1660457) B1660457
theorem B1108607 : Blo 1104625 1108607 := bstep (se 1 (by rfl) ⟨831455, by rfl⟩ : syracuseStep 1108607 = 1662911) B1662911
theorem B5598395 : Blo 1104625 5598395 := bstep (se 1 (by rfl) ⟨4198796, by rfl⟩ : syracuseStep 5598395 = 8397593) B8397593
theorem B163966157 : Blo 1104625 163966157 := bstep (se 3 (by rfl) ⟨30743654, by rfl⟩ : syracuseStep 163966157 = 61487309) B61487309
theorem B5598719 : Blo 1104625 5598719 := bstep (se 1 (by rfl) ⟨4199039, by rfl⟩ : syracuseStep 5598719 = 8398079) B8398079
theorem B2486015 : Blo 1104625 2486015 := bstep (se 1 (by rfl) ⟨1864511, by rfl⟩ : syracuseStep 2486015 = 3729023) B3729023
theorem B48593087 : Blo 1104625 48593087 := bstep (se 1 (by rfl) ⟨36444815, by rfl⟩ : syracuseStep 48593087 = 72889631) B72889631
theorem B1243903 : Blo 1104625 1243903 := bstep (se 1 (by rfl) ⟨932927, by rfl⟩ : syracuseStep 1243903 = 1865855) B1865855
theorem B12616073 : Blo 1104625 12616073 := bstep (se 2 (by rfl) ⟨4731027, by rfl⟩ : syracuseStep 12616073 = 9462055) B9462055
theorem B26873855 : Blo 1104625 26873855 := bstep (se 1 (by rfl) ⟨20155391, by rfl⟩ : syracuseStep 26873855 = 40310783) B40310783
theorem B3740471 : Blo 1104625 3740471 := bstep (se 1 (by rfl) ⟨2805353, by rfl⟩ : syracuseStep 3740471 = 5610707) B5610707
theorem B2798185 : Blo 1104625 2798185 := bstep (se 2 (by rfl) ⟨1049319, by rfl⟩ : syracuseStep 2798185 = 2098639) B2098639
theorem B18166787 : Blo 1104625 18166787 := bstep (se 1 (by rfl) ⟨13625090, by rfl⟩ : syracuseStep 18166787 = 27250181) B27250181
theorem B8402939 : Blo 1104625 8402939 := bstep (se 1 (by rfl) ⟨6302204, by rfl⟩ : syracuseStep 8402939 = 12604409) B12604409
theorem B80656559 : Blo 1104625 80656559 := bstep (se 1 (by rfl) ⟨60492419, by rfl⟩ : syracuseStep 80656559 = 120984839) B120984839
theorem B13482463 : Blo 1104625 13482463 := bstep (se 1 (by rfl) ⟨10111847, by rfl⟩ : syracuseStep 13482463 = 20223695) B20223695
theorem B1657343 : Blo 1104625 1657343 := bstep (se 1 (by rfl) ⟨1243007, by rfl⟩ : syracuseStep 1657343 = 2486015) B2486015
theorem B1658537 : Blo 1104625 1658537 := bstep (se 2 (by rfl) ⟨621951, by rfl⟩ : syracuseStep 1658537 = 1243903) B1243903
theorem B2805455 : Blo 1104625 2805455 := bstep (se 1 (by rfl) ⟨2104091, by rfl⟩ : syracuseStep 2805455 = 4208183) B4208183
theorem B32395391 : Blo 1104625 32395391 := bstep (se 1 (by rfl) ⟨24296543, by rfl⟩ : syracuseStep 32395391 = 48593087) B48593087
theorem B1660841 : Blo 1104625 1660841 := bstep (se 2 (by rfl) ⟨622815, by rfl⟩ : syracuseStep 1660841 = 1245631) B1245631
theorem B15128801 : Blo 1104625 15128801 := bstep (se 2 (by rfl) ⟨5673300, by rfl⟩ : syracuseStep 15128801 = 11346601) B11346601
theorem B1105199 : Blo 1104625 1105199 := bstep (se 1 (by rfl) ⟨828899, by rfl⟩ : syracuseStep 1105199 = 1657799) B1657799
theorem B5987881 : Blo 1104625 5987881 := bstep (se 2 (by rfl) ⟨2245455, by rfl⟩ : syracuseStep 5987881 = 4490911) B4490911
theorem B1106623 : Blo 1104625 1106623 := bstep (se 1 (by rfl) ⟨829967, by rfl⟩ : syracuseStep 1106623 = 1659935) B1659935
theorem B3730535 : Blo 1104625 3730535 := bstep (se 1 (by rfl) ⟨2797901, by rfl⟩ : syracuseStep 3730535 = 5595803) B5595803
theorem B3732263 : Blo 1104625 3732263 := bstep (se 1 (by rfl) ⟨2799197, by rfl⟩ : syracuseStep 3732263 = 5598395) B5598395
theorem B109310771 : Blo 1104625 109310771 := bstep (se 1 (by rfl) ⟨81983078, by rfl⟩ : syracuseStep 109310771 = 163966157) B163966157
theorem B3732479 : Blo 1104625 3732479 := bstep (se 1 (by rfl) ⟨2799359, by rfl⟩ : syracuseStep 3732479 = 5598719) B5598719
theorem B1865801 : Blo 1104625 1865801 := bstep (se 2 (by rfl) ⟨699675, by rfl⟩ : syracuseStep 1865801 = 1399351) B1399351
theorem B1870303 : Blo 1104625 1870303 := bstep (se 1 (by rfl) ⟨1402727, by rfl⟩ : syracuseStep 1870303 = 2805455) B2805455
theorem B21596927 : Blo 1104625 21596927 := bstep (se 1 (by rfl) ⟨16197695, by rfl⟩ : syracuseStep 21596927 = 32395391) B32395391
theorem B2493647 : Blo 1104625 2493647 := bstep (se 1 (by rfl) ⟨1870235, by rfl⟩ : syracuseStep 2493647 = 3740471) B3740471
theorem B17976617 : Blo 1104625 17976617 := bstep (se 2 (by rfl) ⟨6741231, by rfl⟩ : syracuseStep 17976617 = 13482463) B13482463
theorem B12111191 : Blo 1104625 12111191 := bstep (se 1 (by rfl) ⟨9083393, by rfl⟩ : syracuseStep 12111191 = 18166787) B18166787
theorem B7983841 : Blo 1104625 7983841 := bstep (se 2 (by rfl) ⟨2993940, by rfl⟩ : syracuseStep 7983841 = 5987881) B5987881
theorem B8410715 : Blo 1104625 8410715 := bstep (se 1 (by rfl) ⟨6308036, by rfl⟩ : syracuseStep 8410715 = 12616073) B12616073
theorem B1104895 : Blo 1104625 1104895 := bstep (se 1 (by rfl) ⟨828671, by rfl⟩ : syracuseStep 1104895 = 1657343) B1657343
theorem B1105691 : Blo 1104625 1105691 := bstep (se 1 (by rfl) ⟨829268, by rfl⟩ : syracuseStep 1105691 = 1658537) B1658537
theorem B17915903 : Blo 1104625 17915903 := bstep (se 1 (by rfl) ⟨13436927, by rfl⟩ : syracuseStep 17915903 = 26873855) B26873855
theorem B1107227 : Blo 1104625 1107227 := bstep (se 1 (by rfl) ⟨830420, by rfl⟩ : syracuseStep 1107227 = 1660841) B1660841
theorem B10085867 : Blo 1104625 10085867 := bstep (se 1 (by rfl) ⟨7564400, by rfl⟩ : syracuseStep 10085867 = 15128801) B15128801
theorem B3730913 : Blo 1104625 3730913 := bstep (se 2 (by rfl) ⟨1399092, by rfl⟩ : syracuseStep 3730913 = 2798185) B2798185
theorem B2487023 : Blo 1104625 2487023 := bstep (se 1 (by rfl) ⟨1865267, by rfl⟩ : syracuseStep 2487023 = 3730535) B3730535
theorem B2488175 : Blo 1104625 2488175 := bstep (se 1 (by rfl) ⟨1866131, by rfl⟩ : syracuseStep 2488175 = 3732263) B3732263
theorem B72873847 : Blo 1104625 72873847 := bstep (se 1 (by rfl) ⟨54655385, by rfl⟩ : syracuseStep 72873847 = 109310771) B109310771
theorem B2488319 : Blo 1104625 2488319 := bstep (se 1 (by rfl) ⟨1866239, by rfl⟩ : syracuseStep 2488319 = 3732479) B3732479
theorem B5601959 : Blo 1104625 5601959 := bstep (se 1 (by rfl) ⟨4201469, by rfl⟩ : syracuseStep 5601959 = 8402939) B8402939
theorem B1243867 : Blo 1104625 1243867 := bstep (se 1 (by rfl) ⟨932900, by rfl⟩ : syracuseStep 1243867 = 1865801) B1865801
theorem B53771039 : Blo 1104625 53771039 := bstep (se 1 (by rfl) ⟨40328279, by rfl⟩ : syracuseStep 53771039 = 80656559) B80656559
theorem B2493737 : Blo 1104625 2493737 := bstep (se 2 (by rfl) ⟨935151, by rfl⟩ : syracuseStep 2493737 = 1870303) B1870303
theorem B5607143 : Blo 1104625 5607143 := bstep (se 1 (by rfl) ⟨4205357, by rfl⟩ : syracuseStep 5607143 = 8410715) B8410715
theorem B6723911 : Blo 1104625 6723911 := bstep (se 1 (by rfl) ⟨5042933, by rfl⟩ : syracuseStep 6723911 = 10085867) B10085867
theorem B8074127 : Blo 1104625 8074127 := bstep (se 1 (by rfl) ⟨6055595, by rfl⟩ : syracuseStep 8074127 = 12111191) B12111191
theorem B11943935 : Blo 1104625 11943935 := bstep (se 1 (by rfl) ⟨8957951, by rfl⟩ : syracuseStep 11943935 = 17915903) B17915903
theorem B57591805 : Blo 1104625 57591805 := bstep (se 3 (by rfl) ⟨10798463, by rfl⟩ : syracuseStep 57591805 = 21596927) B21596927
theorem B1658015 : Blo 1104625 1658015 := bstep (se 1 (by rfl) ⟨1243511, by rfl⟩ : syracuseStep 1658015 = 2487023) B2487023
theorem B1658489 : Blo 1104625 1658489 := bstep (se 2 (by rfl) ⟨621933, by rfl⟩ : syracuseStep 1658489 = 1243867) B1243867
theorem B1658783 : Blo 1104625 1658783 := bstep (se 1 (by rfl) ⟨1244087, by rfl⟩ : syracuseStep 1658783 = 2488175) B2488175
theorem B1658879 : Blo 1104625 1658879 := bstep (se 1 (by rfl) ⟨1244159, by rfl⟩ : syracuseStep 1658879 = 2488319) B2488319
theorem B1662431 : Blo 1104625 1662431 := bstep (se 1 (by rfl) ⟨1246823, by rfl⟩ : syracuseStep 1662431 = 2493647) B2493647
theorem B11984411 : Blo 1104625 11984411 := bstep (se 1 (by rfl) ⟨8988308, by rfl⟩ : syracuseStep 11984411 = 17976617) B17976617
theorem B10645121 : Blo 1104625 10645121 := bstep (se 2 (by rfl) ⟨3991920, by rfl⟩ : syracuseStep 10645121 = 7983841) B7983841
theorem B2487275 : Blo 1104625 2487275 := bstep (se 1 (by rfl) ⟨1865456, by rfl⟩ : syracuseStep 2487275 = 3730913) B3730913
theorem B3734639 : Blo 1104625 3734639 := bstep (se 1 (by rfl) ⟨2800979, by rfl⟩ : syracuseStep 3734639 = 5601959) B5601959
theorem B35847359 : Blo 1104625 35847359 := bstep (se 1 (by rfl) ⟨26885519, by rfl⟩ : syracuseStep 35847359 = 53771039) B53771039
theorem B388660517 : Blo 1104625 388660517 := bstep (se 4 (by rfl) ⟨36436923, by rfl⟩ : syracuseStep 388660517 = 72873847) B72873847
theorem B21531005 : Blo 1104625 21531005 := bstep (se 3 (by rfl) ⟨4037063, by rfl⟩ : syracuseStep 21531005 = 8074127) B8074127
theorem B3738095 : Blo 1104625 3738095 := bstep (se 1 (by rfl) ⟨2803571, by rfl⟩ : syracuseStep 3738095 = 5607143) B5607143
theorem B17930429 : Blo 1104625 17930429 := bstep (se 3 (by rfl) ⟨3361955, by rfl⟩ : syracuseStep 17930429 = 6723911) B6723911
theorem B23898239 : Blo 1104625 23898239 := bstep (se 1 (by rfl) ⟨17923679, by rfl⟩ : syracuseStep 23898239 = 35847359) B35847359
theorem B259107011 : Blo 1104625 259107011 := bstep (se 1 (by rfl) ⟨194330258, by rfl⟩ : syracuseStep 259107011 = 388660517) B388660517
theorem B76789073 : Blo 1104625 76789073 := bstep (se 2 (by rfl) ⟨28795902, by rfl⟩ : syracuseStep 76789073 = 57591805) B57591805
theorem B7096747 : Blo 1104625 7096747 := bstep (se 1 (by rfl) ⟨5322560, by rfl⟩ : syracuseStep 7096747 = 10645121) B10645121
theorem B7962623 : Blo 1104625 7962623 := bstep (se 1 (by rfl) ⟨5971967, by rfl⟩ : syracuseStep 7962623 = 11943935) B11943935
theorem B1658183 : Blo 1104625 1658183 := bstep (se 1 (by rfl) ⟨1243637, by rfl⟩ : syracuseStep 1658183 = 2487275) B2487275
theorem B1105343 : Blo 1104625 1105343 := bstep (se 1 (by rfl) ⟨829007, by rfl⟩ : syracuseStep 1105343 = 1658015) B1658015
theorem B1662491 : Blo 1104625 1662491 := bstep (se 1 (by rfl) ⟨1246868, by rfl⟩ : syracuseStep 1662491 = 2493737) B2493737
theorem B1105659 : Blo 1104625 1105659 := bstep (se 1 (by rfl) ⟨829244, by rfl⟩ : syracuseStep 1105659 = 1658489) B1658489
theorem B1105855 : Blo 1104625 1105855 := bstep (se 1 (by rfl) ⟨829391, by rfl⟩ : syracuseStep 1105855 = 1658783) B1658783
theorem B1105919 : Blo 1104625 1105919 := bstep (se 1 (by rfl) ⟨829439, by rfl⟩ : syracuseStep 1105919 = 1658879) B1658879
theorem B1108287 : Blo 1104625 1108287 := bstep (se 1 (by rfl) ⟨831215, by rfl⟩ : syracuseStep 1108287 = 1662431) B1662431
theorem B7989607 : Blo 1104625 7989607 := bstep (se 1 (by rfl) ⟨5992205, by rfl⟩ : syracuseStep 7989607 = 11984411) B11984411
theorem B2489759 : Blo 1104625 2489759 := bstep (se 1 (by rfl) ⟨1867319, by rfl⟩ : syracuseStep 2489759 = 3734639) B3734639
theorem B14354003 : Blo 1104625 14354003 := bstep (se 1 (by rfl) ⟨10765502, by rfl⟩ : syracuseStep 14354003 = 21531005) B21531005
theorem B2492063 : Blo 1104625 2492063 := bstep (se 1 (by rfl) ⟨1869047, by rfl⟩ : syracuseStep 2492063 = 3738095) B3738095
theorem B10652809 : Blo 1104625 10652809 := bstep (se 2 (by rfl) ⟨3994803, by rfl⟩ : syracuseStep 10652809 = 7989607) B7989607
theorem B204770861 : Blo 1104625 204770861 := bstep (se 3 (by rfl) ⟨38394536, by rfl⟩ : syracuseStep 204770861 = 76789073) B76789073
theorem B15932159 : Blo 1104625 15932159 := bstep (se 1 (by rfl) ⟨11949119, by rfl⟩ : syracuseStep 15932159 = 23898239) B23898239
theorem B172738007 : Blo 1104625 172738007 := bstep (se 1 (by rfl) ⟨129553505, by rfl⟩ : syracuseStep 172738007 = 259107011) B259107011
theorem B1659839 : Blo 1104625 1659839 := bstep (se 1 (by rfl) ⟨1244879, by rfl⟩ : syracuseStep 1659839 = 2489759) B2489759
theorem B1105455 : Blo 1104625 1105455 := bstep (se 1 (by rfl) ⟨829091, by rfl⟩ : syracuseStep 1105455 = 1658183) B1658183
theorem B9462329 : Blo 1104625 9462329 := bstep (se 2 (by rfl) ⟨3548373, by rfl⟩ : syracuseStep 9462329 = 7096747) B7096747
theorem B11953619 : Blo 1104625 11953619 := bstep (se 1 (by rfl) ⟨8965214, by rfl⟩ : syracuseStep 11953619 = 17930429) B17930429
theorem B1108327 : Blo 1104625 1108327 := bstep (se 1 (by rfl) ⟨831245, by rfl⟩ : syracuseStep 1108327 = 1662491) B1662491
theorem B5308415 : Blo 1104625 5308415 := bstep (se 1 (by rfl) ⟨3981311, by rfl⟩ : syracuseStep 5308415 = 7962623) B7962623
theorem B9569335 : Blo 1104625 9569335 := bstep (se 1 (by rfl) ⟨7177001, by rfl⟩ : syracuseStep 9569335 = 14354003) B14354003
theorem B136513907 : Blo 1104625 136513907 := bstep (se 1 (by rfl) ⟨102385430, by rfl⟩ : syracuseStep 136513907 = 204770861) B204770861
theorem B10621439 : Blo 1104625 10621439 := bstep (se 1 (by rfl) ⟨7966079, by rfl⟩ : syracuseStep 10621439 = 15932159) B15932159
theorem B7969079 : Blo 1104625 7969079 := bstep (se 1 (by rfl) ⟨5976809, by rfl⟩ : syracuseStep 7969079 = 11953619) B11953619
theorem B115158671 : Blo 1104625 115158671 := bstep (se 1 (by rfl) ⟨86369003, by rfl⟩ : syracuseStep 115158671 = 172738007) B172738007
theorem B3538943 : Blo 1104625 3538943 := bstep (se 1 (by rfl) ⟨2654207, by rfl⟩ : syracuseStep 3538943 = 5308415) B5308415
theorem B14203745 : Blo 1104625 14203745 := bstep (se 2 (by rfl) ⟨5326404, by rfl⟩ : syracuseStep 14203745 = 10652809) B10652809
theorem B6308219 : Blo 1104625 6308219 := bstep (se 1 (by rfl) ⟨4731164, by rfl⟩ : syracuseStep 6308219 = 9462329) B9462329
theorem B1661375 : Blo 1104625 1661375 := bstep (se 1 (by rfl) ⟨1246031, by rfl⟩ : syracuseStep 1661375 = 2492063) B2492063
theorem B1106559 : Blo 1104625 1106559 := bstep (se 1 (by rfl) ⟨829919, by rfl⟩ : syracuseStep 1106559 = 1659839) B1659839
theorem B7080959 : Blo 1104625 7080959 := bstep (se 1 (by rfl) ⟨5310719, by rfl⟩ : syracuseStep 7080959 = 10621439) B10621439
theorem B5312719 : Blo 1104625 5312719 := bstep (se 1 (by rfl) ⟨3984539, by rfl⟩ : syracuseStep 5312719 = 7969079) B7969079
theorem B2359295 : Blo 1104625 2359295 := bstep (se 1 (by rfl) ⟨1769471, by rfl⟩ : syracuseStep 2359295 = 3538943) B3538943
theorem B4205479 : Blo 1104625 4205479 := bstep (se 1 (by rfl) ⟨3154109, by rfl⟩ : syracuseStep 4205479 = 6308219) B6308219
theorem B12759113 : Blo 1104625 12759113 := bstep (se 2 (by rfl) ⟨4784667, by rfl⟩ : syracuseStep 12759113 = 9569335) B9569335
theorem B91009271 : Blo 1104625 91009271 := bstep (se 1 (by rfl) ⟨68256953, by rfl⟩ : syracuseStep 91009271 = 136513907) B136513907
theorem B1107583 : Blo 1104625 1107583 := bstep (se 1 (by rfl) ⟨830687, by rfl⟩ : syracuseStep 1107583 = 1661375) B1661375
theorem B76772447 : Blo 1104625 76772447 := bstep (se 1 (by rfl) ⟨57579335, by rfl⟩ : syracuseStep 76772447 = 115158671) B115158671
theorem B9469163 : Blo 1104625 9469163 := bstep (se 1 (by rfl) ⟨7101872, by rfl⟩ : syracuseStep 9469163 = 14203745) B14203745
theorem B5607305 : Blo 1104625 5607305 := bstep (se 2 (by rfl) ⟨2102739, by rfl⟩ : syracuseStep 5607305 = 4205479) B4205479
theorem B7083625 : Blo 1104625 7083625 := bstep (se 2 (by rfl) ⟨2656359, by rfl⟩ : syracuseStep 7083625 = 5312719) B5312719
theorem B18882557 : Blo 1104625 18882557 := bstep (se 3 (by rfl) ⟨3540479, by rfl⟩ : syracuseStep 18882557 = 7080959) B7080959
theorem B1572863 : Blo 1104625 1572863 := bstep (se 1 (by rfl) ⟨1179647, by rfl⟩ : syracuseStep 1572863 = 2359295) B2359295
theorem B8506075 : Blo 1104625 8506075 := bstep (se 1 (by rfl) ⟨6379556, by rfl⟩ : syracuseStep 8506075 = 12759113) B12759113
theorem B60672847 : Blo 1104625 60672847 := bstep (se 1 (by rfl) ⟨45504635, by rfl⟩ : syracuseStep 60672847 = 91009271) B91009271
theorem B6312775 : Blo 1104625 6312775 := bstep (se 1 (by rfl) ⟨4734581, by rfl⟩ : syracuseStep 6312775 = 9469163) B9469163
theorem B51181631 : Blo 1104625 51181631 := bstep (se 1 (by rfl) ⟨38386223, by rfl⟩ : syracuseStep 51181631 = 76772447) B76772447
theorem B3738203 : Blo 1104625 3738203 := bstep (se 1 (by rfl) ⟨2803652, by rfl⟩ : syracuseStep 3738203 = 5607305) B5607305
theorem B11341433 : Blo 1104625 11341433 := bstep (se 2 (by rfl) ⟨4253037, by rfl⟩ : syracuseStep 11341433 = 8506075) B8506075
theorem B12588371 : Blo 1104625 12588371 := bstep (se 1 (by rfl) ⟨9441278, by rfl⟩ : syracuseStep 12588371 = 18882557) B18882557
theorem B9444833 : Blo 1104625 9444833 := bstep (se 2 (by rfl) ⟨3541812, by rfl⟩ : syracuseStep 9444833 = 7083625) B7083625
theorem B34121087 : Blo 1104625 34121087 := bstep (se 1 (by rfl) ⟨25590815, by rfl⟩ : syracuseStep 34121087 = 51181631) B51181631
theorem B80897129 : Blo 1104625 80897129 := bstep (se 2 (by rfl) ⟨30336423, by rfl⟩ : syracuseStep 80897129 = 60672847) B60672847
theorem B8417033 : Blo 1104625 8417033 := bstep (se 2 (by rfl) ⟨3156387, by rfl⟩ : syracuseStep 8417033 = 6312775) B6312775
theorem B4194301 : Blo 1104625 4194301 := bstep (se 3 (by rfl) ⟨786431, by rfl⟩ : syracuseStep 4194301 = 1572863) B1572863
theorem B2492135 : Blo 1104625 2492135 := bstep (se 1 (by rfl) ⟨1869101, by rfl⟩ : syracuseStep 2492135 = 3738203) B3738203
theorem B8392247 : Blo 1104625 8392247 := bstep (se 1 (by rfl) ⟨6294185, by rfl⟩ : syracuseStep 8392247 = 12588371) B12588371
theorem B6296555 : Blo 1104625 6296555 := bstep (se 1 (by rfl) ⟨4722416, by rfl⟩ : syracuseStep 6296555 = 9444833) B9444833
theorem B22747391 : Blo 1104625 22747391 := bstep (se 1 (by rfl) ⟨17060543, by rfl⟩ : syracuseStep 22747391 = 34121087) B34121087
theorem B5611355 : Blo 1104625 5611355 := bstep (se 1 (by rfl) ⟨4208516, by rfl⟩ : syracuseStep 5611355 = 8417033) B8417033
theorem B5592401 : Blo 1104625 5592401 := bstep (se 2 (by rfl) ⟨2097150, by rfl⟩ : syracuseStep 5592401 = 4194301) B4194301
theorem B7560955 : Blo 1104625 7560955 := bstep (se 1 (by rfl) ⟨5670716, by rfl⟩ : syracuseStep 7560955 = 11341433) B11341433
theorem B53931419 : Blo 1104625 53931419 := bstep (se 1 (by rfl) ⟨40448564, by rfl⟩ : syracuseStep 53931419 = 80897129) B80897129
theorem B4197703 : Blo 1104625 4197703 := bstep (se 1 (by rfl) ⟨3148277, by rfl⟩ : syracuseStep 4197703 = 6296555) B6296555
theorem B3740903 : Blo 1104625 3740903 := bstep (se 1 (by rfl) ⟨2805677, by rfl⟩ : syracuseStep 3740903 = 5611355) B5611355
theorem B35954279 : Blo 1104625 35954279 := bstep (se 1 (by rfl) ⟨26965709, by rfl⟩ : syracuseStep 35954279 = 53931419) B53931419
theorem B10081273 : Blo 1104625 10081273 := bstep (se 2 (by rfl) ⟨3780477, by rfl⟩ : syracuseStep 10081273 = 7560955) B7560955
theorem B1661423 : Blo 1104625 1661423 := bstep (se 1 (by rfl) ⟨1246067, by rfl⟩ : syracuseStep 1661423 = 2492135) B2492135
theorem B5594831 : Blo 1104625 5594831 := bstep (se 1 (by rfl) ⟨4196123, by rfl⟩ : syracuseStep 5594831 = 8392247) B8392247
theorem B3728267 : Blo 1104625 3728267 := bstep (se 1 (by rfl) ⟨2796200, by rfl⟩ : syracuseStep 3728267 = 5592401) B5592401
theorem B15164927 : Blo 1104625 15164927 := bstep (se 1 (by rfl) ⟨11373695, by rfl⟩ : syracuseStep 15164927 = 22747391) B22747391
theorem B2493935 : Blo 1104625 2493935 := bstep (se 1 (by rfl) ⟨1870451, by rfl⟩ : syracuseStep 2493935 = 3740903) B3740903
theorem B13441697 : Blo 1104625 13441697 := bstep (se 2 (by rfl) ⟨5040636, by rfl⟩ : syracuseStep 13441697 = 10081273) B10081273
theorem B23969519 : Blo 1104625 23969519 := bstep (se 1 (by rfl) ⟨17977139, by rfl⟩ : syracuseStep 23969519 = 35954279) B35954279
theorem B10109951 : Blo 1104625 10109951 := bstep (se 1 (by rfl) ⟨7582463, by rfl⟩ : syracuseStep 10109951 = 15164927) B15164927
theorem B1107615 : Blo 1104625 1107615 := bstep (se 1 (by rfl) ⟨830711, by rfl⟩ : syracuseStep 1107615 = 1661423) B1661423
theorem B5596937 : Blo 1104625 5596937 := bstep (se 2 (by rfl) ⟨2098851, by rfl⟩ : syracuseStep 5596937 = 4197703) B4197703
theorem B3729887 : Blo 1104625 3729887 := bstep (se 1 (by rfl) ⟨2797415, by rfl⟩ : syracuseStep 3729887 = 5594831) B5594831
theorem B2485511 : Blo 1104625 2485511 := bstep (se 1 (by rfl) ⟨1864133, by rfl⟩ : syracuseStep 2485511 = 3728267) B3728267
theorem B8961131 : Blo 1104625 8961131 := bstep (se 1 (by rfl) ⟨6720848, by rfl⟩ : syracuseStep 8961131 = 13441697) B13441697
theorem B1657007 : Blo 1104625 1657007 := bstep (se 1 (by rfl) ⟨1242755, by rfl⟩ : syracuseStep 1657007 = 2485511) B2485511
theorem B15979679 : Blo 1104625 15979679 := bstep (se 1 (by rfl) ⟨11984759, by rfl⟩ : syracuseStep 15979679 = 23969519) B23969519
theorem B6739967 : Blo 1104625 6739967 := bstep (se 1 (by rfl) ⟨5054975, by rfl⟩ : syracuseStep 6739967 = 10109951) B10109951
theorem B1662623 : Blo 1104625 1662623 := bstep (se 1 (by rfl) ⟨1246967, by rfl⟩ : syracuseStep 1662623 = 2493935) B2493935
theorem B3731291 : Blo 1104625 3731291 := bstep (se 1 (by rfl) ⟨2798468, by rfl⟩ : syracuseStep 3731291 = 5596937) B5596937
theorem B2486591 : Blo 1104625 2486591 := bstep (se 1 (by rfl) ⟨1864943, by rfl⟩ : syracuseStep 2486591 = 3729887) B3729887
theorem B10653119 : Blo 1104625 10653119 := bstep (se 1 (by rfl) ⟨7989839, by rfl⟩ : syracuseStep 10653119 = 15979679) B15979679
theorem B5974087 : Blo 1104625 5974087 := bstep (se 1 (by rfl) ⟨4480565, by rfl⟩ : syracuseStep 5974087 = 8961131) B8961131
theorem B17973245 : Blo 1104625 17973245 := bstep (se 3 (by rfl) ⟨3369983, by rfl⟩ : syracuseStep 17973245 = 6739967) B6739967
theorem B1657727 : Blo 1104625 1657727 := bstep (se 1 (by rfl) ⟨1243295, by rfl⟩ : syracuseStep 1657727 = 2486591) B2486591
theorem B1104671 : Blo 1104625 1104671 := bstep (se 1 (by rfl) ⟨828503, by rfl⟩ : syracuseStep 1104671 = 1657007) B1657007
theorem B1108415 : Blo 1104625 1108415 := bstep (se 1 (by rfl) ⟨831311, by rfl⟩ : syracuseStep 1108415 = 1662623) B1662623
theorem B2487527 : Blo 1104625 2487527 := bstep (se 1 (by rfl) ⟨1865645, by rfl⟩ : syracuseStep 2487527 = 3731291) B3731291
theorem B7965449 : Blo 1104625 7965449 := bstep (se 2 (by rfl) ⟨2987043, by rfl⟩ : syracuseStep 7965449 = 5974087) B5974087
theorem B1658351 : Blo 1104625 1658351 := bstep (se 1 (by rfl) ⟨1243763, by rfl⟩ : syracuseStep 1658351 = 2487527) B2487527
theorem B11982163 : Blo 1104625 11982163 := bstep (se 1 (by rfl) ⟨8986622, by rfl⟩ : syracuseStep 11982163 = 17973245) B17973245
theorem B1105151 : Blo 1104625 1105151 := bstep (se 1 (by rfl) ⟨828863, by rfl⟩ : syracuseStep 1105151 = 1657727) B1657727
theorem B7102079 : Blo 1104625 7102079 := bstep (se 1 (by rfl) ⟨5326559, by rfl⟩ : syracuseStep 7102079 = 10653119) B10653119
theorem B5310299 : Blo 1104625 5310299 := bstep (se 1 (by rfl) ⟨3982724, by rfl⟩ : syracuseStep 5310299 = 7965449) B7965449
theorem B4734719 : Blo 1104625 4734719 := bstep (se 1 (by rfl) ⟨3551039, by rfl⟩ : syracuseStep 4734719 = 7102079) B7102079
theorem B15976217 : Blo 1104625 15976217 := bstep (se 2 (by rfl) ⟨5991081, by rfl⟩ : syracuseStep 15976217 = 11982163) B11982163
theorem B1105567 : Blo 1104625 1105567 := bstep (se 1 (by rfl) ⟨829175, by rfl⟩ : syracuseStep 1105567 = 1658351) B1658351
theorem B10650811 : Blo 1104625 10650811 := bstep (se 1 (by rfl) ⟨7988108, by rfl⟩ : syracuseStep 10650811 = 15976217) B15976217
theorem B3540199 : Blo 1104625 3540199 := bstep (se 1 (by rfl) ⟨2655149, by rfl⟩ : syracuseStep 3540199 = 5310299) B5310299
theorem B3156479 : Blo 1104625 3156479 := bstep (se 1 (by rfl) ⟨2367359, by rfl⟩ : syracuseStep 3156479 = 4734719) B4734719
theorem B4720265 : Blo 1104625 4720265 := bstep (se 2 (by rfl) ⟨1770099, by rfl⟩ : syracuseStep 4720265 = 3540199) B3540199
theorem B2104319 : Blo 1104625 2104319 := bstep (se 1 (by rfl) ⟨1578239, by rfl⟩ : syracuseStep 2104319 = 3156479) B3156479
theorem B14201081 : Blo 1104625 14201081 := bstep (se 2 (by rfl) ⟨5325405, by rfl⟩ : syracuseStep 14201081 = 10650811) B10650811
theorem B3146843 : Blo 1104625 3146843 := bstep (se 1 (by rfl) ⟨2360132, by rfl⟩ : syracuseStep 3146843 = 4720265) B4720265
theorem B5611517 : Blo 1104625 5611517 := bstep (se 3 (by rfl) ⟨1052159, by rfl⟩ : syracuseStep 5611517 = 2104319) B2104319
theorem B9467387 : Blo 1104625 9467387 := bstep (se 1 (by rfl) ⟨7100540, by rfl⟩ : syracuseStep 9467387 = 14201081) B14201081
theorem B2097895 : Blo 1104625 2097895 := bstep (se 1 (by rfl) ⟨1573421, by rfl⟩ : syracuseStep 2097895 = 3146843) B3146843
theorem B3741011 : Blo 1104625 3741011 := bstep (se 1 (by rfl) ⟨2805758, by rfl⟩ : syracuseStep 3741011 = 5611517) B5611517
theorem B6311591 : Blo 1104625 6311591 := bstep (se 1 (by rfl) ⟨4733693, by rfl⟩ : syracuseStep 6311591 = 9467387) B9467387
theorem B2494007 : Blo 1104625 2494007 := bstep (se 1 (by rfl) ⟨1870505, by rfl⟩ : syracuseStep 2494007 = 3741011) B3741011
theorem B2797193 : Blo 1104625 2797193 := bstep (se 2 (by rfl) ⟨1048947, by rfl⟩ : syracuseStep 2797193 = 2097895) B2097895
theorem B4207727 : Blo 1104625 4207727 := bstep (se 1 (by rfl) ⟨3155795, by rfl⟩ : syracuseStep 4207727 = 6311591) B6311591
theorem B2805151 : Blo 1104625 2805151 := bstep (se 1 (by rfl) ⟨2103863, by rfl⟩ : syracuseStep 2805151 = 4207727) B4207727
theorem B1662671 : Blo 1104625 1662671 := bstep (se 1 (by rfl) ⟨1247003, by rfl⟩ : syracuseStep 1662671 = 2494007) B2494007
theorem B1864795 : Blo 1104625 1864795 := bstep (se 1 (by rfl) ⟨1398596, by rfl⟩ : syracuseStep 1864795 = 2797193) B2797193
theorem B3740201 : Blo 1104625 3740201 := bstep (se 2 (by rfl) ⟨1402575, by rfl⟩ : syracuseStep 3740201 = 2805151) B2805151
theorem B1108447 : Blo 1104625 1108447 := bstep (se 1 (by rfl) ⟨831335, by rfl⟩ : syracuseStep 1108447 = 1662671) B1662671
theorem B2486393 : Blo 1104625 2486393 := bstep (se 2 (by rfl) ⟨932397, by rfl⟩ : syracuseStep 2486393 = 1864795) B1864795
theorem B2493467 : Blo 1104625 2493467 := bstep (se 1 (by rfl) ⟨1870100, by rfl⟩ : syracuseStep 2493467 = 3740201) B3740201
theorem B1657595 : Blo 1104625 1657595 := bstep (se 1 (by rfl) ⟨1243196, by rfl⟩ : syracuseStep 1657595 = 2486393) B2486393
theorem B1105063 : Blo 1104625 1105063 := bstep (se 1 (by rfl) ⟨828797, by rfl⟩ : syracuseStep 1105063 = 1657595) B1657595
theorem B1662311 : Blo 1104625 1662311 := bstep (se 1 (by rfl) ⟨1246733, by rfl⟩ : syracuseStep 1662311 = 2493467) B2493467
theorem B1108207 : Blo 1104625 1108207 := bstep (se 1 (by rfl) ⟨831155, by rfl⟩ : syracuseStep 1108207 = 1662311) B1662311

theorem C0 (j : ℕ) (h1 : 276156 ≤ j) (h2 : j ≤ 276855) : Blo 1104625 (4 * j + 3) := by
  interval_cases j
  · exact B1104627
  · exact B1104631
  · exact B1104635
  · exact B1104639
  · exact B1104643
  · exact B1104647
  · exact B1104651
  · exact B1104655
  · exact B1104659
  · exact B1104663
  · exact B1104667
  · exact B1104671
  · exact B1104675
  · exact B1104679
  · exact B1104683
  · exact B1104687
  · exact B1104691
  · exact B1104695
  · exact B1104699
  · exact B1104703
  · exact B1104707
  · exact B1104711
  · exact B1104715
  · exact B1104719
  · exact B1104723
  · exact B1104727
  · exact B1104731
  · exact B1104735
  · exact B1104739
  · exact B1104743
  · exact B1104747
  · exact B1104751
  · exact B1104755
  · exact B1104759
  · exact B1104763
  · exact B1104767
  · exact B1104771
  · exact B1104775
  · exact B1104779
  · exact B1104783
  · exact B1104787
  · exact B1104791
  · exact B1104795
  · exact B1104799
  · exact B1104803
  · exact B1104807
  · exact B1104811
  · exact B1104815
  · exact B1104819
  · exact B1104823
  · exact B1104827
  · exact B1104831
  · exact B1104835
  · exact B1104839
  · exact B1104843
  · exact B1104847
  · exact B1104851
  · exact B1104855
  · exact B1104859
  · exact B1104863
  · exact B1104867
  · exact B1104871
  · exact B1104875
  · exact B1104879
  · exact B1104883
  · exact B1104887
  · exact B1104891
  · exact B1104895
  · exact B1104899
  · exact B1104903
  · exact B1104907
  · exact B1104911
  · exact B1104915
  · exact B1104919
  · exact B1104923
  · exact B1104927
  · exact B1104931
  · exact B1104935
  · exact B1104939
  · exact B1104943
  · exact B1104947
  · exact B1104951
  · exact B1104955
  · exact B1104959
  · exact B1104963
  · exact B1104967
  · exact B1104971
  · exact B1104975
  · exact B1104979
  · exact B1104983
  · exact B1104987
  · exact B1104991
  · exact B1104995
  · exact B1104999
  · exact B1105003
  · exact B1105007
  · exact B1105011
  · exact B1105015
  · exact B1105019
  · exact B1105023
  · exact B1105027
  · exact B1105031
  · exact B1105035
  · exact B1105039
  · exact B1105043
  · exact B1105047
  · exact B1105051
  · exact B1105055
  · exact B1105059
  · exact B1105063
  · exact B1105067
  · exact B1105071
  · exact B1105075
  · exact B1105079
  · exact B1105083
  · exact B1105087
  · exact B1105091
  · exact B1105095
  · exact B1105099
  · exact B1105103
  · exact B1105107
  · exact B1105111
  · exact B1105115
  · exact B1105119
  · exact B1105123
  · exact B1105127
  · exact B1105131
  · exact B1105135
  · exact B1105139
  · exact B1105143
  · exact B1105147
  · exact B1105151
  · exact B1105155
  · exact B1105159
  · exact B1105163
  · exact B1105167
  · exact B1105171
  · exact B1105175
  · exact B1105179
  · exact B1105183
  · exact B1105187
  · exact B1105191
  · exact B1105195
  · exact B1105199
  · exact B1105203
  · exact B1105207
  · exact B1105211
  · exact B1105215
  · exact B1105219
  · exact B1105223
  · exact B1105227
  · exact B1105231
  · exact B1105235
  · exact B1105239
  · exact B1105243
  · exact B1105247
  · exact B1105251
  · exact B1105255
  · exact B1105259
  · exact B1105263
  · exact B1105267
  · exact B1105271
  · exact B1105275
  · exact B1105279
  · exact B1105283
  · exact B1105287
  · exact B1105291
  · exact B1105295
  · exact B1105299
  · exact B1105303
  · exact B1105307
  · exact B1105311
  · exact B1105315
  · exact B1105319
  · exact B1105323
  · exact B1105327
  · exact B1105331
  · exact B1105335
  · exact B1105339
  · exact B1105343
  · exact B1105347
  · exact B1105351
  · exact B1105355
  · exact B1105359
  · exact B1105363
  · exact B1105367
  · exact B1105371
  · exact B1105375
  · exact B1105379
  · exact B1105383
  · exact B1105387
  · exact B1105391
  · exact B1105395
  · exact B1105399
  · exact B1105403
  · exact B1105407
  · exact B1105411
  · exact B1105415
  · exact B1105419
  · exact B1105423
  · exact B1105427
  · exact B1105431
  · exact B1105435
  · exact B1105439
  · exact B1105443
  · exact B1105447
  · exact B1105451
  · exact B1105455
  · exact B1105459
  · exact B1105463
  · exact B1105467
  · exact B1105471
  · exact B1105475
  · exact B1105479
  · exact B1105483
  · exact B1105487
  · exact B1105491
  · exact B1105495
  · exact B1105499
  · exact B1105503
  · exact B1105507
  · exact B1105511
  · exact B1105515
  · exact B1105519
  · exact B1105523
  · exact B1105527
  · exact B1105531
  · exact B1105535
  · exact B1105539
  · exact B1105543
  · exact B1105547
  · exact B1105551
  · exact B1105555
  · exact B1105559
  · exact B1105563
  · exact B1105567
  · exact B1105571
  · exact B1105575
  · exact B1105579
  · exact B1105583
  · exact B1105587
  · exact B1105591
  · exact B1105595
  · exact B1105599
  · exact B1105603
  · exact B1105607
  · exact B1105611
  · exact B1105615
  · exact B1105619
  · exact B1105623
  · exact B1105627
  · exact B1105631
  · exact B1105635
  · exact B1105639
  · exact B1105643
  · exact B1105647
  · exact B1105651
  · exact B1105655
  · exact B1105659
  · exact B1105663
  · exact B1105667
  · exact B1105671
  · exact B1105675
  · exact B1105679
  · exact B1105683
  · exact B1105687
  · exact B1105691
  · exact B1105695
  · exact B1105699
  · exact B1105703
  · exact B1105707
  · exact B1105711
  · exact B1105715
  · exact B1105719
  · exact B1105723
  · exact B1105727
  · exact B1105731
  · exact B1105735
  · exact B1105739
  · exact B1105743
  · exact B1105747
  · exact B1105751
  · exact B1105755
  · exact B1105759
  · exact B1105763
  · exact B1105767
  · exact B1105771
  · exact B1105775
  · exact B1105779
  · exact B1105783
  · exact B1105787
  · exact B1105791
  · exact B1105795
  · exact B1105799
  · exact B1105803
  · exact B1105807
  · exact B1105811
  · exact B1105815
  · exact B1105819
  · exact B1105823
  · exact B1105827
  · exact B1105831
  · exact B1105835
  · exact B1105839
  · exact B1105843
  · exact B1105847
  · exact B1105851
  · exact B1105855
  · exact B1105859
  · exact B1105863
  · exact B1105867
  · exact B1105871
  · exact B1105875
  · exact B1105879
  · exact B1105883
  · exact B1105887
  · exact B1105891
  · exact B1105895
  · exact B1105899
  · exact B1105903
  · exact B1105907
  · exact B1105911
  · exact B1105915
  · exact B1105919
  · exact B1105923
  · exact B1105927
  · exact B1105931
  · exact B1105935
  · exact B1105939
  · exact B1105943
  · exact B1105947
  · exact B1105951
  · exact B1105955
  · exact B1105959
  · exact B1105963
  · exact B1105967
  · exact B1105971
  · exact B1105975
  · exact B1105979
  · exact B1105983
  · exact B1105987
  · exact B1105991
  · exact B1105995
  · exact B1105999
  · exact B1106003
  · exact B1106007
  · exact B1106011
  · exact B1106015
  · exact B1106019
  · exact B1106023
  · exact B1106027
  · exact B1106031
  · exact B1106035
  · exact B1106039
  · exact B1106043
  · exact B1106047
  · exact B1106051
  · exact B1106055
  · exact B1106059
  · exact B1106063
  · exact B1106067
  · exact B1106071
  · exact B1106075
  · exact B1106079
  · exact B1106083
  · exact B1106087
  · exact B1106091
  · exact B1106095
  · exact B1106099
  · exact B1106103
  · exact B1106107
  · exact B1106111
  · exact B1106115
  · exact B1106119
  · exact B1106123
  · exact B1106127
  · exact B1106131
  · exact B1106135
  · exact B1106139
  · exact B1106143
  · exact B1106147
  · exact B1106151
  · exact B1106155
  · exact B1106159
  · exact B1106163
  · exact B1106167
  · exact B1106171
  · exact B1106175
  · exact B1106179
  · exact B1106183
  · exact B1106187
  · exact B1106191
  · exact B1106195
  · exact B1106199
  · exact B1106203
  · exact B1106207
  · exact B1106211
  · exact B1106215
  · exact B1106219
  · exact B1106223
  · exact B1106227
  · exact B1106231
  · exact B1106235
  · exact B1106239
  · exact B1106243
  · exact B1106247
  · exact B1106251
  · exact B1106255
  · exact B1106259
  · exact B1106263
  · exact B1106267
  · exact B1106271
  · exact B1106275
  · exact B1106279
  · exact B1106283
  · exact B1106287
  · exact B1106291
  · exact B1106295
  · exact B1106299
  · exact B1106303
  · exact B1106307
  · exact B1106311
  · exact B1106315
  · exact B1106319
  · exact B1106323
  · exact B1106327
  · exact B1106331
  · exact B1106335
  · exact B1106339
  · exact B1106343
  · exact B1106347
  · exact B1106351
  · exact B1106355
  · exact B1106359
  · exact B1106363
  · exact B1106367
  · exact B1106371
  · exact B1106375
  · exact B1106379
  · exact B1106383
  · exact B1106387
  · exact B1106391
  · exact B1106395
  · exact B1106399
  · exact B1106403
  · exact B1106407
  · exact B1106411
  · exact B1106415
  · exact B1106419
  · exact B1106423
  · exact B1106427
  · exact B1106431
  · exact B1106435
  · exact B1106439
  · exact B1106443
  · exact B1106447
  · exact B1106451
  · exact B1106455
  · exact B1106459
  · exact B1106463
  · exact B1106467
  · exact B1106471
  · exact B1106475
  · exact B1106479
  · exact B1106483
  · exact B1106487
  · exact B1106491
  · exact B1106495
  · exact B1106499
  · exact B1106503
  · exact B1106507
  · exact B1106511
  · exact B1106515
  · exact B1106519
  · exact B1106523
  · exact B1106527
  · exact B1106531
  · exact B1106535
  · exact B1106539
  · exact B1106543
  · exact B1106547
  · exact B1106551
  · exact B1106555
  · exact B1106559
  · exact B1106563
  · exact B1106567
  · exact B1106571
  · exact B1106575
  · exact B1106579
  · exact B1106583
  · exact B1106587
  · exact B1106591
  · exact B1106595
  · exact B1106599
  · exact B1106603
  · exact B1106607
  · exact B1106611
  · exact B1106615
  · exact B1106619
  · exact B1106623
  · exact B1106627
  · exact B1106631
  · exact B1106635
  · exact B1106639
  · exact B1106643
  · exact B1106647
  · exact B1106651
  · exact B1106655
  · exact B1106659
  · exact B1106663
  · exact B1106667
  · exact B1106671
  · exact B1106675
  · exact B1106679
  · exact B1106683
  · exact B1106687
  · exact B1106691
  · exact B1106695
  · exact B1106699
  · exact B1106703
  · exact B1106707
  · exact B1106711
  · exact B1106715
  · exact B1106719
  · exact B1106723
  · exact B1106727
  · exact B1106731
  · exact B1106735
  · exact B1106739
  · exact B1106743
  · exact B1106747
  · exact B1106751
  · exact B1106755
  · exact B1106759
  · exact B1106763
  · exact B1106767
  · exact B1106771
  · exact B1106775
  · exact B1106779
  · exact B1106783
  · exact B1106787
  · exact B1106791
  · exact B1106795
  · exact B1106799
  · exact B1106803
  · exact B1106807
  · exact B1106811
  · exact B1106815
  · exact B1106819
  · exact B1106823
  · exact B1106827
  · exact B1106831
  · exact B1106835
  · exact B1106839
  · exact B1106843
  · exact B1106847
  · exact B1106851
  · exact B1106855
  · exact B1106859
  · exact B1106863
  · exact B1106867
  · exact B1106871
  · exact B1106875
  · exact B1106879
  · exact B1106883
  · exact B1106887
  · exact B1106891
  · exact B1106895
  · exact B1106899
  · exact B1106903
  · exact B1106907
  · exact B1106911
  · exact B1106915
  · exact B1106919
  · exact B1106923
  · exact B1106927
  · exact B1106931
  · exact B1106935
  · exact B1106939
  · exact B1106943
  · exact B1106947
  · exact B1106951
  · exact B1106955
  · exact B1106959
  · exact B1106963
  · exact B1106967
  · exact B1106971
  · exact B1106975
  · exact B1106979
  · exact B1106983
  · exact B1106987
  · exact B1106991
  · exact B1106995
  · exact B1106999
  · exact B1107003
  · exact B1107007
  · exact B1107011
  · exact B1107015
  · exact B1107019
  · exact B1107023
  · exact B1107027
  · exact B1107031
  · exact B1107035
  · exact B1107039
  · exact B1107043
  · exact B1107047
  · exact B1107051
  · exact B1107055
  · exact B1107059
  · exact B1107063
  · exact B1107067
  · exact B1107071
  · exact B1107075
  · exact B1107079
  · exact B1107083
  · exact B1107087
  · exact B1107091
  · exact B1107095
  · exact B1107099
  · exact B1107103
  · exact B1107107
  · exact B1107111
  · exact B1107115
  · exact B1107119
  · exact B1107123
  · exact B1107127
  · exact B1107131
  · exact B1107135
  · exact B1107139
  · exact B1107143
  · exact B1107147
  · exact B1107151
  · exact B1107155
  · exact B1107159
  · exact B1107163
  · exact B1107167
  · exact B1107171
  · exact B1107175
  · exact B1107179
  · exact B1107183
  · exact B1107187
  · exact B1107191
  · exact B1107195
  · exact B1107199
  · exact B1107203
  · exact B1107207
  · exact B1107211
  · exact B1107215
  · exact B1107219
  · exact B1107223
  · exact B1107227
  · exact B1107231
  · exact B1107235
  · exact B1107239
  · exact B1107243
  · exact B1107247
  · exact B1107251
  · exact B1107255
  · exact B1107259
  · exact B1107263
  · exact B1107267
  · exact B1107271
  · exact B1107275
  · exact B1107279
  · exact B1107283
  · exact B1107287
  · exact B1107291
  · exact B1107295
  · exact B1107299
  · exact B1107303
  · exact B1107307
  · exact B1107311
  · exact B1107315
  · exact B1107319
  · exact B1107323
  · exact B1107327
  · exact B1107331
  · exact B1107335
  · exact B1107339
  · exact B1107343
  · exact B1107347
  · exact B1107351
  · exact B1107355
  · exact B1107359
  · exact B1107363
  · exact B1107367
  · exact B1107371
  · exact B1107375
  · exact B1107379
  · exact B1107383
  · exact B1107387
  · exact B1107391
  · exact B1107395
  · exact B1107399
  · exact B1107403
  · exact B1107407
  · exact B1107411
  · exact B1107415
  · exact B1107419
  · exact B1107423

theorem C1 (j : ℕ) (h1 : 276856 ≤ j) (h2 : j ≤ 277155) : Blo 1104625 (4 * j + 3) := by
  interval_cases j
  · exact B1107427
  · exact B1107431
  · exact B1107435
  · exact B1107439
  · exact B1107443
  · exact B1107447
  · exact B1107451
  · exact B1107455
  · exact B1107459
  · exact B1107463
  · exact B1107467
  · exact B1107471
  · exact B1107475
  · exact B1107479
  · exact B1107483
  · exact B1107487
  · exact B1107491
  · exact B1107495
  · exact B1107499
  · exact B1107503
  · exact B1107507
  · exact B1107511
  · exact B1107515
  · exact B1107519
  · exact B1107523
  · exact B1107527
  · exact B1107531
  · exact B1107535
  · exact B1107539
  · exact B1107543
  · exact B1107547
  · exact B1107551
  · exact B1107555
  · exact B1107559
  · exact B1107563
  · exact B1107567
  · exact B1107571
  · exact B1107575
  · exact B1107579
  · exact B1107583
  · exact B1107587
  · exact B1107591
  · exact B1107595
  · exact B1107599
  · exact B1107603
  · exact B1107607
  · exact B1107611
  · exact B1107615
  · exact B1107619
  · exact B1107623
  · exact B1107627
  · exact B1107631
  · exact B1107635
  · exact B1107639
  · exact B1107643
  · exact B1107647
  · exact B1107651
  · exact B1107655
  · exact B1107659
  · exact B1107663
  · exact B1107667
  · exact B1107671
  · exact B1107675
  · exact B1107679
  · exact B1107683
  · exact B1107687
  · exact B1107691
  · exact B1107695
  · exact B1107699
  · exact B1107703
  · exact B1107707
  · exact B1107711
  · exact B1107715
  · exact B1107719
  · exact B1107723
  · exact B1107727
  · exact B1107731
  · exact B1107735
  · exact B1107739
  · exact B1107743
  · exact B1107747
  · exact B1107751
  · exact B1107755
  · exact B1107759
  · exact B1107763
  · exact B1107767
  · exact B1107771
  · exact B1107775
  · exact B1107779
  · exact B1107783
  · exact B1107787
  · exact B1107791
  · exact B1107795
  · exact B1107799
  · exact B1107803
  · exact B1107807
  · exact B1107811
  · exact B1107815
  · exact B1107819
  · exact B1107823
  · exact B1107827
  · exact B1107831
  · exact B1107835
  · exact B1107839
  · exact B1107843
  · exact B1107847
  · exact B1107851
  · exact B1107855
  · exact B1107859
  · exact B1107863
  · exact B1107867
  · exact B1107871
  · exact B1107875
  · exact B1107879
  · exact B1107883
  · exact B1107887
  · exact B1107891
  · exact B1107895
  · exact B1107899
  · exact B1107903
  · exact B1107907
  · exact B1107911
  · exact B1107915
  · exact B1107919
  · exact B1107923
  · exact B1107927
  · exact B1107931
  · exact B1107935
  · exact B1107939
  · exact B1107943
  · exact B1107947
  · exact B1107951
  · exact B1107955
  · exact B1107959
  · exact B1107963
  · exact B1107967
  · exact B1107971
  · exact B1107975
  · exact B1107979
  · exact B1107983
  · exact B1107987
  · exact B1107991
  · exact B1107995
  · exact B1107999
  · exact B1108003
  · exact B1108007
  · exact B1108011
  · exact B1108015
  · exact B1108019
  · exact B1108023
  · exact B1108027
  · exact B1108031
  · exact B1108035
  · exact B1108039
  · exact B1108043
  · exact B1108047
  · exact B1108051
  · exact B1108055
  · exact B1108059
  · exact B1108063
  · exact B1108067
  · exact B1108071
  · exact B1108075
  · exact B1108079
  · exact B1108083
  · exact B1108087
  · exact B1108091
  · exact B1108095
  · exact B1108099
  · exact B1108103
  · exact B1108107
  · exact B1108111
  · exact B1108115
  · exact B1108119
  · exact B1108123
  · exact B1108127
  · exact B1108131
  · exact B1108135
  · exact B1108139
  · exact B1108143
  · exact B1108147
  · exact B1108151
  · exact B1108155
  · exact B1108159
  · exact B1108163
  · exact B1108167
  · exact B1108171
  · exact B1108175
  · exact B1108179
  · exact B1108183
  · exact B1108187
  · exact B1108191
  · exact B1108195
  · exact B1108199
  · exact B1108203
  · exact B1108207
  · exact B1108211
  · exact B1108215
  · exact B1108219
  · exact B1108223
  · exact B1108227
  · exact B1108231
  · exact B1108235
  · exact B1108239
  · exact B1108243
  · exact B1108247
  · exact B1108251
  · exact B1108255
  · exact B1108259
  · exact B1108263
  · exact B1108267
  · exact B1108271
  · exact B1108275
  · exact B1108279
  · exact B1108283
  · exact B1108287
  · exact B1108291
  · exact B1108295
  · exact B1108299
  · exact B1108303
  · exact B1108307
  · exact B1108311
  · exact B1108315
  · exact B1108319
  · exact B1108323
  · exact B1108327
  · exact B1108331
  · exact B1108335
  · exact B1108339
  · exact B1108343
  · exact B1108347
  · exact B1108351
  · exact B1108355
  · exact B1108359
  · exact B1108363
  · exact B1108367
  · exact B1108371
  · exact B1108375
  · exact B1108379
  · exact B1108383
  · exact B1108387
  · exact B1108391
  · exact B1108395
  · exact B1108399
  · exact B1108403
  · exact B1108407
  · exact B1108411
  · exact B1108415
  · exact B1108419
  · exact B1108423
  · exact B1108427
  · exact B1108431
  · exact B1108435
  · exact B1108439
  · exact B1108443
  · exact B1108447
  · exact B1108451
  · exact B1108455
  · exact B1108459
  · exact B1108463
  · exact B1108467
  · exact B1108471
  · exact B1108475
  · exact B1108479
  · exact B1108483
  · exact B1108487
  · exact B1108491
  · exact B1108495
  · exact B1108499
  · exact B1108503
  · exact B1108507
  · exact B1108511
  · exact B1108515
  · exact B1108519
  · exact B1108523
  · exact B1108527
  · exact B1108531
  · exact B1108535
  · exact B1108539
  · exact B1108543
  · exact B1108547
  · exact B1108551
  · exact B1108555
  · exact B1108559
  · exact B1108563
  · exact B1108567
  · exact B1108571
  · exact B1108575
  · exact B1108579
  · exact B1108583
  · exact B1108587
  · exact B1108591
  · exact B1108595
  · exact B1108599
  · exact B1108603
  · exact B1108607
  · exact B1108611
  · exact B1108615
  · exact B1108619
  · exact B1108623

theorem solution (m : ℕ) (hlo : 1104625 ≤ m) (hhi : m ≤ 1108625) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 276156 ≤ j := by omega
    have hj2 : j ≤ 277155 := by omega
    have hb : Blo 1104625 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 276856 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
