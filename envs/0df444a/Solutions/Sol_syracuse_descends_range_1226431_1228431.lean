-- Prove2me | solution 1 for syracuse_descends_range_1226431_1228431
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:00.793602+00:00
-- url     : https://prove2.me/submissions/2974c364-73e6-4165-a490-46d32867ca86

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


theorem B3498005 : Blo 1226431 3498005 := bbase (se 6 (by rfl) ⟨81984, by rfl⟩ : syracuseStep 3498005 = 163969) (by norm_num)
theorem B2760749 : Blo 1226431 2760749 := bbase (se 3 (by rfl) ⟨517640, by rfl⟩ : syracuseStep 2760749 = 1035281) (by norm_num)
theorem B2072621 : Blo 1226431 2072621 := bbase (se 3 (by rfl) ⟨388616, by rfl⟩ : syracuseStep 2072621 = 777233) (by norm_num)
theorem B6987829 : Blo 1226431 6987829 := bbase (se 5 (by rfl) ⟨327554, by rfl⟩ : syracuseStep 6987829 = 655109) (by norm_num)
theorem B4481093 : Blo 1226431 4481093 := bbase (se 4 (by rfl) ⟨420102, by rfl⟩ : syracuseStep 4481093 = 840205) (by norm_num)
theorem B6209621 : Blo 1226431 6209621 := bbase (se 8 (by rfl) ⟨36384, by rfl⟩ : syracuseStep 6209621 = 72769) (by norm_num)
theorem B10485845 : Blo 1226431 10485845 := bbase (se 8 (by rfl) ⟨61440, by rfl⟩ : syracuseStep 10485845 = 122881) (by norm_num)
theorem B4661333 : Blo 1226431 4661333 := bbase (se 8 (by rfl) ⟨27312, by rfl⟩ : syracuseStep 4661333 = 54625) (by norm_num)
theorem B2949221 : Blo 1226431 2949221 := bbase (se 4 (by rfl) ⟨276489, by rfl⟩ : syracuseStep 2949221 = 552979) (by norm_num)
theorem B4972661 : Blo 1226431 4972661 := bbase (se 5 (by rfl) ⟨233093, by rfl⟩ : syracuseStep 4972661 = 466187) (by norm_num)
theorem B2760821 : Blo 1226431 2760821 := bbase (se 5 (by rfl) ⟨129413, by rfl⟩ : syracuseStep 2760821 = 258827) (by norm_num)
theorem B2072749 : Blo 1226431 2072749 := bbase (se 3 (by rfl) ⟨388640, by rfl⟩ : syracuseStep 2072749 = 777281) (by norm_num)
theorem B2760893 : Blo 1226431 2760893 := bbase (se 3 (by rfl) ⟨517667, by rfl⟩ : syracuseStep 2760893 = 1035335) (by norm_num)
theorem B10477781 : Blo 1226431 10477781 := bbase (se 7 (by rfl) ⟨122786, by rfl⟩ : syracuseStep 10477781 = 245573) (by norm_num)
theorem B1310953 : Blo 1226431 1310953 := bbase (se 2 (by rfl) ⟨491607, by rfl⟩ : syracuseStep 1310953 = 983215) (by norm_num)
theorem B3105013 : Blo 1226431 3105013 := bbase (se 5 (by rfl) ⟨145547, by rfl⟩ : syracuseStep 3105013 = 291095) (by norm_num)
theorem B2760965 : Blo 1226431 2760965 := bbase (se 4 (by rfl) ⟨258840, by rfl⟩ : syracuseStep 2760965 = 517681) (by norm_num)
theorem B2072837 : Blo 1226431 2072837 := bbase (se 4 (by rfl) ⟨194328, by rfl⟩ : syracuseStep 2072837 = 388657) (by norm_num)
theorem B14934293 : Blo 1226431 14934293 := bbase (se 6 (by rfl) ⟨350022, by rfl⟩ : syracuseStep 14934293 = 700045) (by norm_num)
theorem B1311013 : Blo 1226431 1311013 := bbase (se 4 (by rfl) ⟨122907, by rfl⟩ : syracuseStep 1311013 = 245815) (by norm_num)
theorem B4424005 : Blo 1226431 4424005 := bbase (se 4 (by rfl) ⟨414750, by rfl⟩ : syracuseStep 4424005 = 829501) (by norm_num)
theorem B2761037 : Blo 1226431 2761037 := bbase (se 3 (by rfl) ⟨517694, by rfl⟩ : syracuseStep 2761037 = 1035389) (by norm_num)
theorem B3105125 : Blo 1226431 3105125 := bbase (se 4 (by rfl) ⟨291105, by rfl⟩ : syracuseStep 3105125 = 582211) (by norm_num)
theorem B4661621 : Blo 1226431 4661621 := bbase (se 5 (by rfl) ⟨218513, by rfl⟩ : syracuseStep 4661621 = 437027) (by norm_num)
theorem B4145525 : Blo 1226431 4145525 := bbase (se 5 (by rfl) ⟨194321, by rfl⟩ : syracuseStep 4145525 = 388643) (by norm_num)
theorem B2621821 : Blo 1226431 2621821 := bbase (se 3 (by rfl) ⟨491591, by rfl⟩ : syracuseStep 2621821 = 983183) (by norm_num)
theorem B2072965 : Blo 1226431 2072965 := bbase (se 4 (by rfl) ⟨194340, by rfl⟩ : syracuseStep 2072965 = 388681) (by norm_num)
theorem B1474957 : Blo 1226431 1474957 := bbase (se 3 (by rfl) ⟨276554, by rfl⟩ : syracuseStep 1474957 = 553109) (by norm_num)
theorem B2761109 : Blo 1226431 2761109 := bbase (se 6 (by rfl) ⟨64713, by rfl⟩ : syracuseStep 2761109 = 129427) (by norm_num)
theorem B1475029 : Blo 1226431 1475029 := bbase (se 7 (by rfl) ⟨17285, by rfl⟩ : syracuseStep 1475029 = 34571) (by norm_num)
theorem B2761181 : Blo 1226431 2761181 := bbase (se 3 (by rfl) ⟨517721, by rfl⟩ : syracuseStep 2761181 = 1035443) (by norm_num)
theorem B3105317 : Blo 1226431 3105317 := bbase (se 4 (by rfl) ⟨291123, by rfl⟩ : syracuseStep 3105317 = 582247) (by norm_num)
theorem B2761253 : Blo 1226431 2761253 := bbase (se 4 (by rfl) ⟨258867, by rfl⟩ : syracuseStep 2761253 = 517735) (by norm_num)
theorem B1311329 : Blo 1226431 1311329 := bbase (se 2 (by rfl) ⟨491748, by rfl⟩ : syracuseStep 1311329 = 983497) (by norm_num)
theorem B2761325 : Blo 1226431 2761325 := bbase (se 3 (by rfl) ⟨517748, by rfl⟩ : syracuseStep 2761325 = 1035497) (by norm_num)
theorem B2761397 : Blo 1226431 2761397 := bbase (se 5 (by rfl) ⟨129440, by rfl⟩ : syracuseStep 2761397 = 258881) (by norm_num)
theorem B1573597 : Blo 1226431 1573597 := bbase (se 3 (by rfl) ⟨295049, by rfl⟩ : syracuseStep 1573597 = 590099) (by norm_num)
theorem B2761469 : Blo 1226431 2761469 := bbase (se 3 (by rfl) ⟨517775, by rfl⟩ : syracuseStep 2761469 = 1035551) (by norm_num)
theorem B5595925 : Blo 1226431 5595925 := bbase (se 6 (by rfl) ⟨131154, by rfl⟩ : syracuseStep 5595925 = 262309) (by norm_num)
theorem B4145957 : Blo 1226431 4145957 := bbase (se 4 (by rfl) ⟨388683, by rfl⟩ : syracuseStep 4145957 = 777367) (by norm_num)
theorem B2761541 : Blo 1226431 2761541 := bbase (se 4 (by rfl) ⟨258894, by rfl⟩ : syracuseStep 2761541 = 517789) (by norm_num)
theorem B3105661 : Blo 1226431 3105661 := bbase (se 3 (by rfl) ⟨582311, by rfl⟩ : syracuseStep 3105661 = 1164623) (by norm_num)
theorem B2761613 : Blo 1226431 2761613 := bbase (se 3 (by rfl) ⟨517802, by rfl⟩ : syracuseStep 2761613 = 1035605) (by norm_num)
theorem B6218693 : Blo 1226431 6218693 := bbase (se 4 (by rfl) ⟨583002, by rfl⟩ : syracuseStep 6218693 = 1166005) (by norm_num)
theorem B2761685 : Blo 1226431 2761685 := bbase (se 7 (by rfl) ⟨32363, by rfl⟩ : syracuseStep 2761685 = 64727) (by norm_num)
theorem B3105773 : Blo 1226431 3105773 := bbase (se 3 (by rfl) ⟨582332, by rfl⟩ : syracuseStep 3105773 = 1164665) (by norm_num)
theorem B1328113 : Blo 1226431 1328113 := bbase (se 2 (by rfl) ⟨498042, by rfl⟩ : syracuseStep 1328113 = 996085) (by norm_num)
theorem B2761757 : Blo 1226431 2761757 := bbase (se 3 (by rfl) ⟨517829, by rfl⟩ : syracuseStep 2761757 = 1035659) (by norm_num)
theorem B1311773 : Blo 1226431 1311773 := bbase (se 3 (by rfl) ⟨245957, by rfl⟩ : syracuseStep 1311773 = 491915) (by norm_num)
theorem B2212925 : Blo 1226431 2212925 := bbase (se 3 (by rfl) ⟨414923, by rfl⟩ : syracuseStep 2212925 = 829847) (by norm_num)
theorem B3933269 : Blo 1226431 3933269 := bbase (se 8 (by rfl) ⟨23046, by rfl⟩ : syracuseStep 3933269 = 46093) (by norm_num)
theorem B2761829 : Blo 1226431 2761829 := bbase (se 4 (by rfl) ⟨258921, by rfl⟩ : syracuseStep 2761829 = 517843) (by norm_num)
theorem B2213005 : Blo 1226431 2213005 := bbase (se 3 (by rfl) ⟨414938, by rfl⟩ : syracuseStep 2213005 = 829877) (by norm_num)
theorem B3105965 : Blo 1226431 3105965 := bbase (se 3 (by rfl) ⟨582368, by rfl⟩ : syracuseStep 3105965 = 1164737) (by norm_num)
theorem B2761901 : Blo 1226431 2761901 := bbase (se 3 (by rfl) ⟨517856, by rfl⟩ : syracuseStep 2761901 = 1035713) (by norm_num)
theorem B2761973 : Blo 1226431 2761973 := bbase (se 5 (by rfl) ⟨129467, by rfl⟩ : syracuseStep 2761973 = 258935) (by norm_num)
theorem B2622709 : Blo 1226431 2622709 := bbase (se 5 (by rfl) ⟨122939, by rfl⟩ : syracuseStep 2622709 = 245879) (by norm_num)
theorem B2762045 : Blo 1226431 2762045 := bbase (se 3 (by rfl) ⟨517883, by rfl⟩ : syracuseStep 2762045 = 1035767) (by norm_num)
theorem B3540293 : Blo 1226431 3540293 := bbase (se 4 (by rfl) ⟨331902, by rfl⟩ : syracuseStep 3540293 = 663805) (by norm_num)
theorem B1967429 : Blo 1226431 1967429 := bbase (se 4 (by rfl) ⟨184446, by rfl⟩ : syracuseStep 1967429 = 368893) (by norm_num)
theorem B1680733 : Blo 1226431 1680733 := bbase (se 3 (by rfl) ⟨315137, by rfl⟩ : syracuseStep 1680733 = 630275) (by norm_num)
theorem B6210917 : Blo 1226431 6210917 := bbase (se 4 (by rfl) ⟨582273, by rfl⟩ : syracuseStep 6210917 = 1164547) (by norm_num)
theorem B2213237 : Blo 1226431 2213237 := bbase (se 5 (by rfl) ⟨103745, by rfl⟩ : syracuseStep 2213237 = 207491) (by norm_num)
theorem B2762117 : Blo 1226431 2762117 := bbase (se 4 (by rfl) ⟨258948, by rfl⟩ : syracuseStep 2762117 = 517897) (by norm_num)
theorem B1574321 : Blo 1226431 1574321 := bbase (se 2 (by rfl) ⟨590370, by rfl⟩ : syracuseStep 1574321 = 1180741) (by norm_num)
theorem B1746365 : Blo 1226431 1746365 := bbase (se 3 (by rfl) ⟨327443, by rfl⟩ : syracuseStep 1746365 = 654887) (by norm_num)
theorem B2950597 : Blo 1226431 2950597 := bbase (se 4 (by rfl) ⟨276618, by rfl⟩ : syracuseStep 2950597 = 553237) (by norm_num)
theorem B2762189 : Blo 1226431 2762189 := bbase (se 3 (by rfl) ⟨517910, by rfl⟩ : syracuseStep 2762189 = 1035821) (by norm_num)
theorem B3106309 : Blo 1226431 3106309 := bbase (se 4 (by rfl) ⟨291216, by rfl⟩ : syracuseStep 3106309 = 582433) (by norm_num)
theorem B2762261 : Blo 1226431 2762261 := bbase (se 6 (by rfl) ⟨64740, by rfl⟩ : syracuseStep 2762261 = 129481) (by norm_num)
theorem B4662805 : Blo 1226431 4662805 := bbase (se 6 (by rfl) ⟨109284, by rfl⟩ : syracuseStep 4662805 = 218569) (by norm_num)
theorem B2762333 : Blo 1226431 2762333 := bbase (se 3 (by rfl) ⟨517937, by rfl⟩ : syracuseStep 2762333 = 1035875) (by norm_num)
theorem B3106421 : Blo 1226431 3106421 := bbase (se 5 (by rfl) ⟨145613, by rfl⟩ : syracuseStep 3106421 = 291227) (by norm_num)
theorem B2762405 : Blo 1226431 2762405 := bbase (se 4 (by rfl) ⟨258975, by rfl⟩ : syracuseStep 2762405 = 517951) (by norm_num)
theorem B2623205 : Blo 1226431 2623205 := bbase (se 4 (by rfl) ⟨245925, by rfl⟩ : syracuseStep 2623205 = 491851) (by norm_num)
theorem B2762477 : Blo 1226431 2762477 := bbase (se 3 (by rfl) ⟨517964, by rfl⟩ : syracuseStep 2762477 = 1035929) (by norm_num)
theorem B2328365 : Blo 1226431 2328365 := bbase (se 3 (by rfl) ⟨436568, by rfl⟩ : syracuseStep 2328365 = 873137) (by norm_num)
theorem B3106613 : Blo 1226431 3106613 := bbase (se 5 (by rfl) ⟨145622, by rfl⟩ : syracuseStep 3106613 = 291245) (by norm_num)
theorem B2762549 : Blo 1226431 2762549 := bbase (se 5 (by rfl) ⟨129494, by rfl⟩ : syracuseStep 2762549 = 258989) (by norm_num)
theorem B4663109 : Blo 1226431 4663109 := bbase (se 4 (by rfl) ⟨437166, by rfl⟩ : syracuseStep 4663109 = 874333) (by norm_num)
theorem B1992557 : Blo 1226431 1992557 := bbase (se 3 (by rfl) ⟨373604, by rfl⟩ : syracuseStep 1992557 = 747209) (by norm_num)
theorem B7866229 : Blo 1226431 7866229 := bbase (se 5 (by rfl) ⟨368729, by rfl⟩ : syracuseStep 7866229 = 737459) (by norm_num)
theorem B2762621 : Blo 1226431 2762621 := bbase (se 3 (by rfl) ⟨517991, by rfl⟩ : syracuseStep 2762621 = 1035983) (by norm_num)
theorem B5244821 : Blo 1226431 5244821 := bbase (se 6 (by rfl) ⟨122925, by rfl⟩ : syracuseStep 5244821 = 245851) (by norm_num)
theorem B1574813 : Blo 1226431 1574813 := bbase (se 3 (by rfl) ⟨295277, by rfl⟩ : syracuseStep 1574813 = 590555) (by norm_num)
theorem B2328517 : Blo 1226431 2328517 := bbase (se 4 (by rfl) ⟨218298, by rfl⟩ : syracuseStep 2328517 = 436597) (by norm_num)
theorem B2762693 : Blo 1226431 2762693 := bbase (se 4 (by rfl) ⟨259002, by rfl⟩ : syracuseStep 2762693 = 518005) (by norm_num)
theorem B7858133 : Blo 1226431 7858133 := bbase (se 7 (by rfl) ⟨92087, by rfl⟩ : syracuseStep 7858133 = 184175) (by norm_num)
theorem B6989813 : Blo 1226431 6989813 := bbase (se 5 (by rfl) ⟨327647, by rfl⟩ : syracuseStep 6989813 = 655295) (by norm_num)
theorem B2762765 : Blo 1226431 2762765 := bbase (se 3 (by rfl) ⟨518018, by rfl⟩ : syracuseStep 2762765 = 1036037) (by norm_num)
theorem B2762837 : Blo 1226431 2762837 := bbase (se 8 (by rfl) ⟨16188, by rfl⟩ : syracuseStep 2762837 = 32377) (by norm_num)
theorem B6383717 : Blo 1226431 6383717 := bbase (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) (by norm_num)
theorem B3106957 : Blo 1226431 3106957 := bbase (se 3 (by rfl) ⟨582554, by rfl⟩ : syracuseStep 3106957 = 1165109) (by norm_num)
theorem B2762909 : Blo 1226431 2762909 := bbase (se 3 (by rfl) ⟨518045, by rfl⟩ : syracuseStep 2762909 = 1036091) (by norm_num)
theorem B1747117 : Blo 1226431 1747117 := bbase (se 3 (by rfl) ⟨327584, by rfl⟩ : syracuseStep 1747117 = 655169) (by norm_num)
theorem B2762981 : Blo 1226431 2762981 := bbase (se 4 (by rfl) ⟨259029, by rfl⟩ : syracuseStep 2762981 = 518059) (by norm_num)
theorem B2328821 : Blo 1226431 2328821 := bbase (se 5 (by rfl) ⟨109163, by rfl⟩ : syracuseStep 2328821 = 218327) (by norm_num)
theorem B3107069 : Blo 1226431 3107069 := bbase (se 3 (by rfl) ⟨582575, by rfl⟩ : syracuseStep 3107069 = 1165151) (by norm_num)
theorem B2763053 : Blo 1226431 2763053 := bbase (se 3 (by rfl) ⟨518072, by rfl⟩ : syracuseStep 2763053 = 1036145) (by norm_num)
theorem B2763125 : Blo 1226431 2763125 := bbase (se 5 (by rfl) ⟨129521, by rfl⟩ : syracuseStep 2763125 = 259043) (by norm_num)
theorem B2099621 : Blo 1226431 2099621 := bbase (se 4 (by rfl) ⟨196839, by rfl⟩ : syracuseStep 2099621 = 393679) (by norm_num)
theorem B3107261 : Blo 1226431 3107261 := bbase (se 3 (by rfl) ⟨582611, by rfl⟩ : syracuseStep 3107261 = 1165223) (by norm_num)
theorem B2763197 : Blo 1226431 2763197 := bbase (se 3 (by rfl) ⟨518099, by rfl⟩ : syracuseStep 2763197 = 1036199) (by norm_num)
theorem B4139477 : Blo 1226431 4139477 := bbase (se 7 (by rfl) ⟨48509, by rfl⟩ : syracuseStep 4139477 = 97019) (by norm_num)
theorem B5900789 : Blo 1226431 5900789 := bbase (se 5 (by rfl) ⟨276599, by rfl⟩ : syracuseStep 5900789 = 553199) (by norm_num)
theorem B2763269 : Blo 1226431 2763269 := bbase (se 4 (by rfl) ⟨259056, by rfl⟩ : syracuseStep 2763269 = 518113) (by norm_num)
theorem B2763341 : Blo 1226431 2763341 := bbase (se 3 (by rfl) ⟨518126, by rfl⟩ : syracuseStep 2763341 = 1036253) (by norm_num)
theorem B6212213 : Blo 1226431 6212213 := bbase (se 5 (by rfl) ⟨291197, by rfl⟩ : syracuseStep 6212213 = 582395) (by norm_num)
theorem B2763413 : Blo 1226431 2763413 := bbase (se 6 (by rfl) ⟨64767, by rfl⟩ : syracuseStep 2763413 = 129535) (by norm_num)
theorem B2763485 : Blo 1226431 2763485 := bbase (se 3 (by rfl) ⟨518153, by rfl⟩ : syracuseStep 2763485 = 1036307) (by norm_num)
theorem B3492629 : Blo 1226431 3492629 := bbase (se 6 (by rfl) ⟨81858, by rfl⟩ : syracuseStep 3492629 = 163717) (by norm_num)
theorem B3107605 : Blo 1226431 3107605 := bbase (se 6 (by rfl) ⟨72834, by rfl⟩ : syracuseStep 3107605 = 145669) (by norm_num)
theorem B1993493 : Blo 1226431 1993493 := bbase (se 6 (by rfl) ⟨46722, by rfl⟩ : syracuseStep 1993493 = 93445) (by norm_num)
theorem B2763557 : Blo 1226431 2763557 := bbase (se 4 (by rfl) ⟨259083, by rfl⟩ : syracuseStep 2763557 = 518167) (by norm_num)
theorem B2362165 : Blo 1226431 2362165 := bbase (se 5 (by rfl) ⟨110726, by rfl⟩ : syracuseStep 2362165 = 221453) (by norm_num)
theorem B2763629 : Blo 1226431 2763629 := bbase (se 3 (by rfl) ⟨518180, by rfl⟩ : syracuseStep 2763629 = 1036361) (by norm_num)
theorem B4139909 : Blo 1226431 4139909 := bbase (se 4 (by rfl) ⟨388116, by rfl⟩ : syracuseStep 4139909 = 776233) (by norm_num)
theorem B3107717 : Blo 1226431 3107717 := bbase (se 4 (by rfl) ⟨291348, by rfl⟩ : syracuseStep 3107717 = 582697) (by norm_num)
theorem B5245829 : Blo 1226431 5245829 := bbase (se 4 (by rfl) ⟨491796, by rfl⟩ : syracuseStep 5245829 = 983593) (by norm_num)
theorem B2763701 : Blo 1226431 2763701 := bbase (se 5 (by rfl) ⟨129548, by rfl⟩ : syracuseStep 2763701 = 259097) (by norm_num)
theorem B1747909 : Blo 1226431 1747909 := bbase (se 4 (by rfl) ⟨163866, by rfl⟩ : syracuseStep 1747909 = 327733) (by norm_num)
theorem B3492821 : Blo 1226431 3492821 := bbase (se 7 (by rfl) ⟨40931, by rfl⟩ : syracuseStep 3492821 = 81863) (by norm_num)
theorem B1657813 : Blo 1226431 1657813 := bbase (se 7 (by rfl) ⟨19427, by rfl⟩ : syracuseStep 1657813 = 38855) (by norm_num)
theorem B2329573 : Blo 1226431 2329573 := bbase (se 4 (by rfl) ⟨218397, by rfl⟩ : syracuseStep 2329573 = 436795) (by norm_num)
theorem B2763773 : Blo 1226431 2763773 := bbase (se 3 (by rfl) ⟨518207, by rfl⟩ : syracuseStep 2763773 = 1036415) (by norm_num)
theorem B3107909 : Blo 1226431 3107909 := bbase (se 4 (by rfl) ⟨291366, by rfl⟩ : syracuseStep 3107909 = 582733) (by norm_num)
theorem B2763845 : Blo 1226431 2763845 := bbase (se 4 (by rfl) ⟨259110, by rfl⟩ : syracuseStep 2763845 = 518221) (by norm_num)
theorem B1993805 : Blo 1226431 1993805 := bbase (se 3 (by rfl) ⟨373838, by rfl⟩ : syracuseStep 1993805 = 747677) (by norm_num)
theorem B2329717 : Blo 1226431 2329717 := bbase (se 5 (by rfl) ⟨109205, by rfl⟩ : syracuseStep 2329717 = 218411) (by norm_num)
theorem B2763917 : Blo 1226431 2763917 := bbase (se 3 (by rfl) ⟨518234, by rfl⟩ : syracuseStep 2763917 = 1036469) (by norm_num)
theorem B1346737 : Blo 1226431 1346737 := bbase (se 2 (by rfl) ⟨505026, by rfl⟩ : syracuseStep 1346737 = 1010053) (by norm_num)
theorem B4426933 : Blo 1226431 4426933 := bbase (se 5 (by rfl) ⟨207512, by rfl⟩ : syracuseStep 4426933 = 415025) (by norm_num)
theorem B4197653 : Blo 1226431 4197653 := bbase (se 6 (by rfl) ⟨98382, by rfl⟩ : syracuseStep 4197653 = 196765) (by norm_num)
theorem B2329877 : Blo 1226431 2329877 := bbase (se 6 (by rfl) ⟨54606, by rfl⟩ : syracuseStep 2329877 = 109213) (by norm_num)
theorem B1748245 : Blo 1226431 1748245 := bbase (se 6 (by rfl) ⟨40974, by rfl⟩ : syracuseStep 1748245 = 81949) (by norm_num)
theorem B4140341 : Blo 1226431 4140341 := bbase (se 5 (by rfl) ⟨194078, by rfl⟩ : syracuseStep 4140341 = 388157) (by norm_num)
theorem B4721989 : Blo 1226431 4721989 := bbase (se 4 (by rfl) ⟨442686, by rfl⟩ : syracuseStep 4721989 = 885373) (by norm_num)
theorem B3108253 : Blo 1226431 3108253 := bbase (se 3 (by rfl) ⟨582797, by rfl⟩ : syracuseStep 3108253 = 1165595) (by norm_num)
theorem B1379749 : Blo 1226431 1379749 := bbase (se 4 (by rfl) ⟨129351, by rfl⟩ : syracuseStep 1379749 = 258703) (by norm_num)
theorem B2330021 : Blo 1226431 2330021 := bbase (se 4 (by rfl) ⟨218439, by rfl⟩ : syracuseStep 2330021 = 436879) (by norm_num)
theorem B1379785 : Blo 1226431 1379785 := bbase (se 2 (by rfl) ⟨517419, by rfl⟩ : syracuseStep 1379785 = 1034839) (by norm_num)
theorem B1379821 : Blo 1226431 1379821 := bbase (se 3 (by rfl) ⟨258716, by rfl⟩ : syracuseStep 1379821 = 517433) (by norm_num)
theorem B1748461 : Blo 1226431 1748461 := bbase (se 3 (by rfl) ⟨327836, by rfl⟩ : syracuseStep 1748461 = 655673) (by norm_num)
theorem B3108365 : Blo 1226431 3108365 := bbase (se 3 (by rfl) ⟨582818, by rfl⟩ : syracuseStep 3108365 = 1165637) (by norm_num)
theorem B1379857 : Blo 1226431 1379857 := bbase (se 2 (by rfl) ⟨517446, by rfl⟩ : syracuseStep 1379857 = 1034893) (by norm_num)
theorem B3730981 : Blo 1226431 3730981 := bbase (se 4 (by rfl) ⟨349779, by rfl⟩ : syracuseStep 3730981 = 699559) (by norm_num)
theorem B2428453 : Blo 1226431 2428453 := bbase (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) (by norm_num)
theorem B1379893 : Blo 1226431 1379893 := bbase (se 5 (by rfl) ⟨64682, by rfl⟩ : syracuseStep 1379893 = 129365) (by norm_num)
theorem B1379929 : Blo 1226431 1379929 := bbase (se 2 (by rfl) ⟨517473, by rfl⟩ : syracuseStep 1379929 = 1034947) (by norm_num)
theorem B1379965 : Blo 1226431 1379965 := bbase (se 3 (by rfl) ⟨258743, by rfl⟩ : syracuseStep 1379965 = 517487) (by norm_num)
theorem B1380001 : Blo 1226431 1380001 := bbase (se 2 (by rfl) ⟨517500, by rfl⟩ : syracuseStep 1380001 = 1035001) (by norm_num)
theorem B1380037 : Blo 1226431 1380037 := bbase (se 4 (by rfl) ⟨129378, by rfl⟩ : syracuseStep 1380037 = 258757) (by norm_num)
theorem B2330309 : Blo 1226431 2330309 := bbase (se 4 (by rfl) ⟨218466, by rfl⟩ : syracuseStep 2330309 = 436933) (by norm_num)
theorem B3108557 : Blo 1226431 3108557 := bbase (se 3 (by rfl) ⟨582854, by rfl⟩ : syracuseStep 3108557 = 1165709) (by norm_num)
theorem B19910357 : Blo 1226431 19910357 := bbase (se 7 (by rfl) ⟨233324, by rfl⟩ : syracuseStep 19910357 = 466649) (by norm_num)
theorem B4140773 : Blo 1226431 4140773 := bbase (se 4 (by rfl) ⟨388197, by rfl⟩ : syracuseStep 4140773 = 776395) (by norm_num)
theorem B1380073 : Blo 1226431 1380073 := bbase (se 2 (by rfl) ⟨517527, by rfl⟩ : syracuseStep 1380073 = 1035055) (by norm_num)
theorem B1380109 : Blo 1226431 1380109 := bbase (se 3 (by rfl) ⟨258770, by rfl⟩ : syracuseStep 1380109 = 517541) (by norm_num)
theorem B3731237 : Blo 1226431 3731237 := bbase (se 4 (by rfl) ⟨349803, by rfl⟩ : syracuseStep 3731237 = 699607) (by norm_num)
theorem B1380145 : Blo 1226431 1380145 := bbase (se 2 (by rfl) ⟨517554, by rfl⟩ : syracuseStep 1380145 = 1035109) (by norm_num)
theorem B1552213 : Blo 1226431 1552213 := bbase (se 9 (by rfl) ⟨4547, by rfl⟩ : syracuseStep 1552213 = 9095) (by norm_num)
theorem B1380181 : Blo 1226431 1380181 := bbase (se 9 (by rfl) ⟨4043, by rfl⟩ : syracuseStep 1380181 = 8087) (by norm_num)
theorem B2330461 : Blo 1226431 2330461 := bbase (se 3 (by rfl) ⟨436961, by rfl⟩ : syracuseStep 2330461 = 873923) (by norm_num)
theorem B1748837 : Blo 1226431 1748837 := bbase (se 4 (by rfl) ⟨163953, by rfl⟩ : syracuseStep 1748837 = 327907) (by norm_num)
theorem B1380217 : Blo 1226431 1380217 := bbase (se 2 (by rfl) ⟨517581, by rfl⟩ : syracuseStep 1380217 = 1035163) (by norm_num)
theorem B6213509 : Blo 1226431 6213509 := bbase (se 4 (by rfl) ⟨582516, by rfl⟩ : syracuseStep 6213509 = 1165033) (by norm_num)
theorem B1380253 : Blo 1226431 1380253 := bbase (se 3 (by rfl) ⟨258797, by rfl⟩ : syracuseStep 1380253 = 517595) (by norm_num)
theorem B3493813 : Blo 1226431 3493813 := bbase (se 5 (by rfl) ⟨163772, by rfl⟩ : syracuseStep 3493813 = 327545) (by norm_num)
theorem B1380289 : Blo 1226431 1380289 := bbase (se 2 (by rfl) ⟨517608, by rfl⟩ : syracuseStep 1380289 = 1035217) (by norm_num)
theorem B4542437 : Blo 1226431 4542437 := bbase (se 4 (by rfl) ⟨425853, by rfl⟩ : syracuseStep 4542437 = 851707) (by norm_num)
theorem B1380325 : Blo 1226431 1380325 := bbase (se 4 (by rfl) ⟨129405, by rfl⟩ : syracuseStep 1380325 = 258811) (by norm_num)
theorem B1552385 : Blo 1226431 1552385 := bbase (se 2 (by rfl) ⟨582144, by rfl⟩ : syracuseStep 1552385 = 1164289) (by norm_num)
theorem B1380361 : Blo 1226431 1380361 := bbase (se 2 (by rfl) ⟨517635, by rfl⟩ : syracuseStep 1380361 = 1035271) (by norm_num)
theorem B3108901 : Blo 1226431 3108901 := bbase (se 4 (by rfl) ⟨291459, by rfl⟩ : syracuseStep 3108901 = 582919) (by norm_num)
theorem B1380397 : Blo 1226431 1380397 := bbase (se 3 (by rfl) ⟨258824, by rfl⟩ : syracuseStep 1380397 = 517649) (by norm_num)
theorem B1552441 : Blo 1226431 1552441 := bbase (se 2 (by rfl) ⟨582165, by rfl⟩ : syracuseStep 1552441 = 1164331) (by norm_num)
theorem B1380433 : Blo 1226431 1380433 := bbase (se 2 (by rfl) ⟨517662, by rfl⟩ : syracuseStep 1380433 = 1035325) (by norm_num)
theorem B1380469 : Blo 1226431 1380469 := bbase (se 5 (by rfl) ⟨64709, by rfl⟩ : syracuseStep 1380469 = 129419) (by norm_num)
theorem B2330765 : Blo 1226431 2330765 := bbase (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) (by norm_num)
theorem B4141205 : Blo 1226431 4141205 := bbase (se 6 (by rfl) ⟨97059, by rfl⟩ : syracuseStep 4141205 = 194119) (by norm_num)
theorem B6992021 : Blo 1226431 6992021 := bbase (se 6 (by rfl) ⟨163875, by rfl⟩ : syracuseStep 6992021 = 327751) (by norm_num)
theorem B3109013 : Blo 1226431 3109013 := bbase (se 6 (by rfl) ⟨72867, by rfl⟩ : syracuseStep 3109013 = 145735) (by norm_num)
theorem B1552537 : Blo 1226431 1552537 := bbase (se 2 (by rfl) ⟨582201, by rfl⟩ : syracuseStep 1552537 = 1164403) (by norm_num)
theorem B1380505 : Blo 1226431 1380505 := bbase (se 2 (by rfl) ⟨517689, by rfl⟩ : syracuseStep 1380505 = 1035379) (by norm_num)
theorem B1380541 : Blo 1226431 1380541 := bbase (se 3 (by rfl) ⟨258851, by rfl⟩ : syracuseStep 1380541 = 517703) (by norm_num)
theorem B1380577 : Blo 1226431 1380577 := bbase (se 2 (by rfl) ⟨517716, by rfl⟩ : syracuseStep 1380577 = 1035433) (by norm_num)
theorem B1380613 : Blo 1226431 1380613 := bbase (se 4 (by rfl) ⟨129432, by rfl⟩ : syracuseStep 1380613 = 258865) (by norm_num)
theorem B4657445 : Blo 1226431 4657445 := bbase (se 4 (by rfl) ⟨436635, by rfl⟩ : syracuseStep 4657445 = 873271) (by norm_num)
theorem B1380649 : Blo 1226431 1380649 := bbase (se 2 (by rfl) ⟨517743, by rfl⟩ : syracuseStep 1380649 = 1035487) (by norm_num)
theorem B1552709 : Blo 1226431 1552709 := bbase (se 4 (by rfl) ⟨145566, by rfl⟩ : syracuseStep 1552709 = 291133) (by norm_num)
theorem B1380685 : Blo 1226431 1380685 := bbase (se 3 (by rfl) ⟨258878, by rfl⟩ : syracuseStep 1380685 = 517757) (by norm_num)
theorem B3109205 : Blo 1226431 3109205 := bbase (se 10 (by rfl) ⟨4554, by rfl⟩ : syracuseStep 3109205 = 9109) (by norm_num)
theorem B1380721 : Blo 1226431 1380721 := bbase (se 2 (by rfl) ⟨517770, by rfl⟩ : syracuseStep 1380721 = 1035541) (by norm_num)
theorem B1552765 : Blo 1226431 1552765 := bbase (se 3 (by rfl) ⟨291143, by rfl⟩ : syracuseStep 1552765 = 582287) (by norm_num)
theorem B1380757 : Blo 1226431 1380757 := bbase (se 6 (by rfl) ⟨32361, by rfl⟩ : syracuseStep 1380757 = 64723) (by norm_num)
theorem B1380793 : Blo 1226431 1380793 := bbase (se 2 (by rfl) ⟨517797, by rfl⟩ : syracuseStep 1380793 = 1035595) (by norm_num)
theorem B1552861 : Blo 1226431 1552861 := bbase (se 3 (by rfl) ⟨291161, by rfl⟩ : syracuseStep 1552861 = 582323) (by norm_num)
theorem B1380829 : Blo 1226431 1380829 := bbase (se 3 (by rfl) ⟨258905, by rfl⟩ : syracuseStep 1380829 = 517811) (by norm_num)
theorem B1380865 : Blo 1226431 1380865 := bbase (se 2 (by rfl) ⟨517824, by rfl⟩ : syracuseStep 1380865 = 1035649) (by norm_num)
theorem B1659413 : Blo 1226431 1659413 := bbase (se 6 (by rfl) ⟨38892, by rfl⟩ : syracuseStep 1659413 = 77785) (by norm_num)
theorem B1839653 : Blo 1226431 1839653 := bbase (se 4 (by rfl) ⟨172467, by rfl⟩ : syracuseStep 1839653 = 344935) (by norm_num)
theorem B1380901 : Blo 1226431 1380901 := bbase (se 4 (by rfl) ⟨129459, by rfl⟩ : syracuseStep 1380901 = 258919) (by norm_num)
theorem B1839677 : Blo 1226431 1839677 := bbase (se 3 (by rfl) ⟨344939, by rfl⟩ : syracuseStep 1839677 = 689879) (by norm_num)
theorem B4657733 : Blo 1226431 4657733 := bbase (se 4 (by rfl) ⟨436662, by rfl⟩ : syracuseStep 4657733 = 873325) (by norm_num)
theorem B4141637 : Blo 1226431 4141637 := bbase (se 4 (by rfl) ⟨388278, by rfl⟩ : syracuseStep 4141637 = 776557) (by norm_num)
theorem B1380937 : Blo 1226431 1380937 := bbase (se 2 (by rfl) ⟨517851, by rfl⟩ : syracuseStep 1380937 = 1035703) (by norm_num)
theorem B1839701 : Blo 1226431 1839701 := bbase (se 8 (by rfl) ⟨10779, by rfl⟩ : syracuseStep 1839701 = 21559) (by norm_num)
theorem B7967317 : Blo 1226431 7967317 := bbase (se 8 (by rfl) ⟨46683, by rfl⟩ : syracuseStep 7967317 = 93367) (by norm_num)
theorem B1839725 : Blo 1226431 1839725 := bbase (se 3 (by rfl) ⟨344948, by rfl⟩ : syracuseStep 1839725 = 689897) (by norm_num)
theorem B1380973 : Blo 1226431 1380973 := bbase (se 3 (by rfl) ⟨258932, by rfl⟩ : syracuseStep 1380973 = 517865) (by norm_num)
theorem B1839749 : Blo 1226431 1839749 := bbase (se 4 (by rfl) ⟨172476, by rfl⟩ : syracuseStep 1839749 = 344953) (by norm_num)
theorem B1553033 : Blo 1226431 1553033 := bbase (se 2 (by rfl) ⟨582387, by rfl⟩ : syracuseStep 1553033 = 1164775) (by norm_num)
theorem B1381009 : Blo 1226431 1381009 := bbase (se 2 (by rfl) ⟨517878, by rfl⟩ : syracuseStep 1381009 = 1035757) (by norm_num)
theorem B1839773 : Blo 1226431 1839773 := bbase (se 3 (by rfl) ⟨344957, by rfl⟩ : syracuseStep 1839773 = 689915) (by norm_num)
theorem B1839797 : Blo 1226431 1839797 := bbase (se 5 (by rfl) ⟨86240, by rfl⟩ : syracuseStep 1839797 = 172481) (by norm_num)
theorem B6632117 : Blo 1226431 6632117 := bbase (se 5 (by rfl) ⟨310880, by rfl⟩ : syracuseStep 6632117 = 621761) (by norm_num)
theorem B1381045 : Blo 1226431 1381045 := bbase (se 5 (by rfl) ⟨64736, by rfl⟩ : syracuseStep 1381045 = 129473) (by norm_num)
theorem B1553089 : Blo 1226431 1553089 := bbase (se 2 (by rfl) ⟨582408, by rfl⟩ : syracuseStep 1553089 = 1164817) (by norm_num)
theorem B1839821 : Blo 1226431 1839821 := bbase (se 3 (by rfl) ⟨344966, by rfl⟩ : syracuseStep 1839821 = 689933) (by norm_num)
theorem B1381081 : Blo 1226431 1381081 := bbase (se 2 (by rfl) ⟨517905, by rfl⟩ : syracuseStep 1381081 = 1035811) (by norm_num)
theorem B1839845 : Blo 1226431 1839845 := bbase (se 4 (by rfl) ⟨172485, by rfl⟩ : syracuseStep 1839845 = 344971) (by norm_num)
theorem B1839869 : Blo 1226431 1839869 := bbase (se 3 (by rfl) ⟨344975, by rfl⟩ : syracuseStep 1839869 = 689951) (by norm_num)
theorem B2487037 : Blo 1226431 2487037 := bbase (se 3 (by rfl) ⟨466319, by rfl⟩ : syracuseStep 2487037 = 932639) (by norm_num)
theorem B1381117 : Blo 1226431 1381117 := bbase (se 3 (by rfl) ⟨258959, by rfl⟩ : syracuseStep 1381117 = 517919) (by norm_num)
theorem B1839893 : Blo 1226431 1839893 := bbase (se 6 (by rfl) ⟨43122, by rfl⟩ : syracuseStep 1839893 = 86245) (by norm_num)
theorem B7467797 : Blo 1226431 7467797 := bbase (se 6 (by rfl) ⟨175026, by rfl⟩ : syracuseStep 7467797 = 350053) (by norm_num)
theorem B3150613 : Blo 1226431 3150613 := bbase (se 6 (by rfl) ⟨73842, by rfl⟩ : syracuseStep 3150613 = 147685) (by norm_num)
theorem B1553185 : Blo 1226431 1553185 := bbase (se 2 (by rfl) ⟨582444, by rfl⟩ : syracuseStep 1553185 = 1164889) (by norm_num)
theorem B1381153 : Blo 1226431 1381153 := bbase (se 2 (by rfl) ⟨517932, by rfl⟩ : syracuseStep 1381153 = 1035865) (by norm_num)
theorem B1839917 : Blo 1226431 1839917 := bbase (se 3 (by rfl) ⟨344984, by rfl⟩ : syracuseStep 1839917 = 689969) (by norm_num)
theorem B1839941 : Blo 1226431 1839941 := bbase (se 4 (by rfl) ⟨172494, by rfl⟩ : syracuseStep 1839941 = 344989) (by norm_num)
theorem B1381189 : Blo 1226431 1381189 := bbase (se 4 (by rfl) ⟨129486, by rfl⟩ : syracuseStep 1381189 = 258973) (by norm_num)
theorem B1839965 : Blo 1226431 1839965 := bbase (se 3 (by rfl) ⟨344993, by rfl⟩ : syracuseStep 1839965 = 689987) (by norm_num)
theorem B1381225 : Blo 1226431 1381225 := bbase (se 2 (by rfl) ⟨517959, by rfl⟩ : syracuseStep 1381225 = 1035919) (by norm_num)
theorem B1839989 : Blo 1226431 1839989 := bbase (se 5 (by rfl) ⟨86249, by rfl⟩ : syracuseStep 1839989 = 172499) (by norm_num)
theorem B2331517 : Blo 1226431 2331517 := bbase (se 3 (by rfl) ⟨437159, by rfl⟩ : syracuseStep 2331517 = 874319) (by norm_num)
theorem B1659781 : Blo 1226431 1659781 := bbase (se 4 (by rfl) ⟨155604, by rfl⟩ : syracuseStep 1659781 = 311209) (by norm_num)
theorem B1840013 : Blo 1226431 1840013 := bbase (se 3 (by rfl) ⟨345002, by rfl⟩ : syracuseStep 1840013 = 690005) (by norm_num)
theorem B1381261 : Blo 1226431 1381261 := bbase (se 3 (by rfl) ⟨258986, by rfl⟩ : syracuseStep 1381261 = 517973) (by norm_num)
theorem B1840037 : Blo 1226431 1840037 := bbase (se 4 (by rfl) ⟨172503, by rfl⟩ : syracuseStep 1840037 = 345007) (by norm_num)
theorem B1381297 : Blo 1226431 1381297 := bbase (se 2 (by rfl) ⟨517986, by rfl⟩ : syracuseStep 1381297 = 1035973) (by norm_num)
theorem B1840061 : Blo 1226431 1840061 := bbase (se 3 (by rfl) ⟨345011, by rfl⟩ : syracuseStep 1840061 = 690023) (by norm_num)
theorem B1553357 : Blo 1226431 1553357 := bbase (se 3 (by rfl) ⟨291254, by rfl⟩ : syracuseStep 1553357 = 582509) (by norm_num)
theorem B1840085 : Blo 1226431 1840085 := bbase (se 7 (by rfl) ⟨21563, by rfl⟩ : syracuseStep 1840085 = 43127) (by norm_num)
theorem B1381333 : Blo 1226431 1381333 := bbase (se 7 (by rfl) ⟨16187, by rfl⟩ : syracuseStep 1381333 = 32375) (by norm_num)
theorem B1684453 : Blo 1226431 1684453 := bbase (se 4 (by rfl) ⟨157917, by rfl⟩ : syracuseStep 1684453 = 315835) (by norm_num)
theorem B1840109 : Blo 1226431 1840109 := bbase (se 3 (by rfl) ⟨345020, by rfl⟩ : syracuseStep 1840109 = 690041) (by norm_num)
theorem B4142069 : Blo 1226431 4142069 := bbase (se 5 (by rfl) ⟨194159, by rfl⟩ : syracuseStep 4142069 = 388319) (by norm_num)
theorem B1381369 : Blo 1226431 1381369 := bbase (se 2 (by rfl) ⟨518013, by rfl⟩ : syracuseStep 1381369 = 1036027) (by norm_num)
theorem B1840133 : Blo 1226431 1840133 := bbase (se 4 (by rfl) ⟨172512, by rfl⟩ : syracuseStep 1840133 = 345025) (by norm_num)
theorem B3494917 : Blo 1226431 3494917 := bbase (se 4 (by rfl) ⟨327648, by rfl⟩ : syracuseStep 3494917 = 655297) (by norm_num)
theorem B1553413 : Blo 1226431 1553413 := bbase (se 4 (by rfl) ⟨145632, by rfl⟩ : syracuseStep 1553413 = 291265) (by norm_num)
theorem B2331661 : Blo 1226431 2331661 := bbase (se 3 (by rfl) ⟨437186, by rfl⟩ : syracuseStep 2331661 = 874373) (by norm_num)
theorem B1840157 : Blo 1226431 1840157 := bbase (se 3 (by rfl) ⟨345029, by rfl⟩ : syracuseStep 1840157 = 690059) (by norm_num)
theorem B1381405 : Blo 1226431 1381405 := bbase (se 3 (by rfl) ⟨259013, by rfl⟩ : syracuseStep 1381405 = 518027) (by norm_num)
theorem B1840181 : Blo 1226431 1840181 := bbase (se 5 (by rfl) ⟨86258, by rfl⟩ : syracuseStep 1840181 = 172517) (by norm_num)
theorem B1381441 : Blo 1226431 1381441 := bbase (se 2 (by rfl) ⟨518040, by rfl⟩ : syracuseStep 1381441 = 1036081) (by norm_num)
theorem B1840205 : Blo 1226431 1840205 := bbase (se 3 (by rfl) ⟨345038, by rfl⟩ : syracuseStep 1840205 = 690077) (by norm_num)
theorem B1840229 : Blo 1226431 1840229 := bbase (se 4 (by rfl) ⟨172521, by rfl⟩ : syracuseStep 1840229 = 345043) (by norm_num)
theorem B1553509 : Blo 1226431 1553509 := bbase (se 4 (by rfl) ⟨145641, by rfl⟩ : syracuseStep 1553509 = 291283) (by norm_num)
theorem B1381477 : Blo 1226431 1381477 := bbase (se 4 (by rfl) ⟨129513, by rfl⟩ : syracuseStep 1381477 = 259027) (by norm_num)
theorem B2126965 : Blo 1226431 2126965 := bbase (se 5 (by rfl) ⟨99701, by rfl⟩ : syracuseStep 2126965 = 199403) (by norm_num)
theorem B1840253 : Blo 1226431 1840253 := bbase (se 3 (by rfl) ⟨345047, by rfl⟩ : syracuseStep 1840253 = 690095) (by norm_num)
theorem B1381513 : Blo 1226431 1381513 := bbase (se 2 (by rfl) ⟨518067, by rfl⟩ : syracuseStep 1381513 = 1036135) (by norm_num)
theorem B1840277 : Blo 1226431 1840277 := bbase (se 6 (by rfl) ⟨43131, by rfl⟩ : syracuseStep 1840277 = 86263) (by norm_num)
theorem B6214805 : Blo 1226431 6214805 := bbase (se 6 (by rfl) ⟨145659, by rfl⟩ : syracuseStep 6214805 = 291319) (by norm_num)
theorem B1840301 : Blo 1226431 1840301 := bbase (se 3 (by rfl) ⟨345056, by rfl⟩ : syracuseStep 1840301 = 690113) (by norm_num)
theorem B1381549 : Blo 1226431 1381549 := bbase (se 3 (by rfl) ⟨259040, by rfl⟩ : syracuseStep 1381549 = 518081) (by norm_num)
theorem B2331821 : Blo 1226431 2331821 := bbase (se 3 (by rfl) ⟨437216, by rfl⟩ : syracuseStep 2331821 = 874433) (by norm_num)
theorem B9327797 : Blo 1226431 9327797 := bbase (se 5 (by rfl) ⟨437240, by rfl⟩ : syracuseStep 9327797 = 874481) (by norm_num)
theorem B1840325 : Blo 1226431 1840325 := bbase (se 4 (by rfl) ⟨172530, by rfl⟩ : syracuseStep 1840325 = 345061) (by norm_num)
theorem B1381585 : Blo 1226431 1381585 := bbase (se 2 (by rfl) ⟨518094, by rfl⟩ : syracuseStep 1381585 = 1036189) (by norm_num)
theorem B2069725 : Blo 1226431 2069725 := bbase (se 3 (by rfl) ⟨388073, by rfl⟩ : syracuseStep 2069725 = 776147) (by norm_num)
theorem B1840349 : Blo 1226431 1840349 := bbase (se 3 (by rfl) ⟨345065, by rfl⟩ : syracuseStep 1840349 = 690131) (by norm_num)
theorem B1840373 : Blo 1226431 1840373 := bbase (se 5 (by rfl) ⟨86267, by rfl⟩ : syracuseStep 1840373 = 172535) (by norm_num)
theorem B1381621 : Blo 1226431 1381621 := bbase (se 5 (by rfl) ⟨64763, by rfl⟩ : syracuseStep 1381621 = 129527) (by norm_num)
theorem B1840397 : Blo 1226431 1840397 := bbase (se 3 (by rfl) ⟨345074, by rfl⟩ : syracuseStep 1840397 = 690149) (by norm_num)
theorem B1553681 : Blo 1226431 1553681 := bbase (se 2 (by rfl) ⟨582630, by rfl⟩ : syracuseStep 1553681 = 1165261) (by norm_num)
theorem B25212181 : Blo 1226431 25212181 := bbase (se 6 (by rfl) ⟨590910, by rfl⟩ : syracuseStep 25212181 = 1181821) (by norm_num)
theorem B1381657 : Blo 1226431 1381657 := bbase (se 2 (by rfl) ⟨518121, by rfl⟩ : syracuseStep 1381657 = 1036243) (by norm_num)
theorem B1840421 : Blo 1226431 1840421 := bbase (se 4 (by rfl) ⟨172539, by rfl⟩ : syracuseStep 1840421 = 345079) (by norm_num)
theorem B2069813 : Blo 1226431 2069813 := bbase (se 5 (by rfl) ⟨97022, by rfl⟩ : syracuseStep 2069813 = 194045) (by norm_num)
theorem B1840445 : Blo 1226431 1840445 := bbase (se 3 (by rfl) ⟨345083, by rfl⟩ : syracuseStep 1840445 = 690167) (by norm_num)
theorem B1381693 : Blo 1226431 1381693 := bbase (se 3 (by rfl) ⟨259067, by rfl⟩ : syracuseStep 1381693 = 518135) (by norm_num)
theorem B2331965 : Blo 1226431 2331965 := bbase (se 3 (by rfl) ⟨437243, by rfl⟩ : syracuseStep 2331965 = 874487) (by norm_num)
theorem B1553737 : Blo 1226431 1553737 := bbase (se 2 (by rfl) ⟨582651, by rfl⟩ : syracuseStep 1553737 = 1165303) (by norm_num)
theorem B1840469 : Blo 1226431 1840469 := bbase (se 14 (by rfl) ⟨168, by rfl⟩ : syracuseStep 1840469 = 337) (by norm_num)
theorem B1381729 : Blo 1226431 1381729 := bbase (se 2 (by rfl) ⟨518148, by rfl⟩ : syracuseStep 1381729 = 1036297) (by norm_num)
theorem B1840493 : Blo 1226431 1840493 := bbase (se 3 (by rfl) ⟨345092, by rfl⟩ : syracuseStep 1840493 = 690185) (by norm_num)
theorem B1840517 : Blo 1226431 1840517 := bbase (se 4 (by rfl) ⟨172548, by rfl⟩ : syracuseStep 1840517 = 345097) (by norm_num)
theorem B1381765 : Blo 1226431 1381765 := bbase (se 4 (by rfl) ⟨129540, by rfl⟩ : syracuseStep 1381765 = 259081) (by norm_num)
theorem B1840541 : Blo 1226431 1840541 := bbase (se 3 (by rfl) ⟨345101, by rfl⟩ : syracuseStep 1840541 = 690203) (by norm_num)
theorem B2487709 : Blo 1226431 2487709 := bbase (se 3 (by rfl) ⟨466445, by rfl⟩ : syracuseStep 2487709 = 932891) (by norm_num)
theorem B4142501 : Blo 1226431 4142501 := bbase (se 4 (by rfl) ⟨388359, by rfl⟩ : syracuseStep 4142501 = 776719) (by norm_num)
theorem B1553833 : Blo 1226431 1553833 := bbase (se 2 (by rfl) ⟨582687, by rfl⟩ : syracuseStep 1553833 = 1165375) (by norm_num)
theorem B1381801 : Blo 1226431 1381801 := bbase (se 2 (by rfl) ⟨518175, by rfl⟩ : syracuseStep 1381801 = 1036351) (by norm_num)
theorem B2069941 : Blo 1226431 2069941 := bbase (se 5 (by rfl) ⟨97028, by rfl⟩ : syracuseStep 2069941 = 194057) (by norm_num)
theorem B1840565 : Blo 1226431 1840565 := bbase (se 5 (by rfl) ⟨86276, by rfl⟩ : syracuseStep 1840565 = 172553) (by norm_num)
theorem B1840589 : Blo 1226431 1840589 := bbase (se 3 (by rfl) ⟨345110, by rfl⟩ : syracuseStep 1840589 = 690221) (by norm_num)
theorem B1381837 : Blo 1226431 1381837 := bbase (se 3 (by rfl) ⟨259094, by rfl⟩ : syracuseStep 1381837 = 518189) (by norm_num)
theorem B1840613 : Blo 1226431 1840613 := bbase (se 4 (by rfl) ⟨172557, by rfl⟩ : syracuseStep 1840613 = 345115) (by norm_num)
theorem B1381873 : Blo 1226431 1381873 := bbase (se 2 (by rfl) ⟨518202, by rfl⟩ : syracuseStep 1381873 = 1036405) (by norm_num)
theorem B1840637 : Blo 1226431 1840637 := bbase (se 3 (by rfl) ⟨345119, by rfl⟩ : syracuseStep 1840637 = 690239) (by norm_num)
theorem B2070029 : Blo 1226431 2070029 := bbase (se 3 (by rfl) ⟨388130, by rfl⟩ : syracuseStep 2070029 = 776261) (by norm_num)
theorem B1840661 : Blo 1226431 1840661 := bbase (se 6 (by rfl) ⟨43140, by rfl⟩ : syracuseStep 1840661 = 86281) (by norm_num)
theorem B1381909 : Blo 1226431 1381909 := bbase (se 6 (by rfl) ⟨32388, by rfl⟩ : syracuseStep 1381909 = 64777) (by norm_num)
theorem B1840685 : Blo 1226431 1840685 := bbase (se 3 (by rfl) ⟨345128, by rfl⟩ : syracuseStep 1840685 = 690257) (by norm_num)
theorem B1381945 : Blo 1226431 1381945 := bbase (se 2 (by rfl) ⟨518229, by rfl⟩ : syracuseStep 1381945 = 1036459) (by norm_num)
theorem B1840709 : Blo 1226431 1840709 := bbase (se 4 (by rfl) ⟨172566, by rfl⟩ : syracuseStep 1840709 = 345133) (by norm_num)
theorem B14161493 : Blo 1226431 14161493 := bbase (se 8 (by rfl) ⟨82977, by rfl⟩ : syracuseStep 14161493 = 165955) (by norm_num)
theorem B9320021 : Blo 1226431 9320021 := bbase (se 8 (by rfl) ⟨54609, by rfl⟩ : syracuseStep 9320021 = 109219) (by norm_num)
theorem B1554005 : Blo 1226431 1554005 := bbase (se 8 (by rfl) ⟨9105, by rfl⟩ : syracuseStep 1554005 = 18211) (by norm_num)
theorem B1840733 : Blo 1226431 1840733 := bbase (se 3 (by rfl) ⟨345137, by rfl⟩ : syracuseStep 1840733 = 690275) (by norm_num)
theorem B1381981 : Blo 1226431 1381981 := bbase (se 3 (by rfl) ⟨259121, by rfl⟩ : syracuseStep 1381981 = 518243) (by norm_num)
theorem B1840757 : Blo 1226431 1840757 := bbase (se 5 (by rfl) ⟨86285, by rfl⟩ : syracuseStep 1840757 = 172571) (by norm_num)
theorem B2070157 : Blo 1226431 2070157 := bbase (se 3 (by rfl) ⟨388154, by rfl⟩ : syracuseStep 2070157 = 776309) (by norm_num)
theorem B1840781 : Blo 1226431 1840781 := bbase (se 3 (by rfl) ⟨345146, by rfl⟩ : syracuseStep 1840781 = 690293) (by norm_num)
theorem B1554061 : Blo 1226431 1554061 := bbase (se 3 (by rfl) ⟨291386, by rfl⟩ : syracuseStep 1554061 = 582773) (by norm_num)
theorem B1840805 : Blo 1226431 1840805 := bbase (se 4 (by rfl) ⟨172575, by rfl⟩ : syracuseStep 1840805 = 345151) (by norm_num)
theorem B1865405 : Blo 1226431 1865405 := bbase (se 3 (by rfl) ⟨349763, by rfl⟩ : syracuseStep 1865405 = 699527) (by norm_num)
theorem B1840829 : Blo 1226431 1840829 := bbase (se 3 (by rfl) ⟨345155, by rfl⟩ : syracuseStep 1840829 = 690311) (by norm_num)
theorem B1840853 : Blo 1226431 1840853 := bbase (se 7 (by rfl) ⟨21572, by rfl⟩ : syracuseStep 1840853 = 43145) (by norm_num)
theorem B2070245 : Blo 1226431 2070245 := bbase (se 4 (by rfl) ⟨194085, by rfl⟩ : syracuseStep 2070245 = 388171) (by norm_num)
theorem B4658917 : Blo 1226431 4658917 := bbase (se 4 (by rfl) ⟨436773, by rfl⟩ : syracuseStep 4658917 = 873547) (by norm_num)
theorem B1840877 : Blo 1226431 1840877 := bbase (se 3 (by rfl) ⟨345164, by rfl⟩ : syracuseStep 1840877 = 690329) (by norm_num)
theorem B1554157 : Blo 1226431 1554157 := bbase (se 3 (by rfl) ⟨291404, by rfl⟩ : syracuseStep 1554157 = 582809) (by norm_num)
theorem B1840901 : Blo 1226431 1840901 := bbase (se 4 (by rfl) ⟨172584, by rfl⟩ : syracuseStep 1840901 = 345169) (by norm_num)
theorem B7870229 : Blo 1226431 7870229 := bbase (se 6 (by rfl) ⟨184458, by rfl⟩ : syracuseStep 7870229 = 368917) (by norm_num)
theorem B1840925 : Blo 1226431 1840925 := bbase (se 3 (by rfl) ⟨345173, by rfl⟩ : syracuseStep 1840925 = 690347) (by norm_num)
theorem B1840949 : Blo 1226431 1840949 := bbase (se 5 (by rfl) ⟨86294, by rfl⟩ : syracuseStep 1840949 = 172589) (by norm_num)
theorem B1840973 : Blo 1226431 1840973 := bbase (se 3 (by rfl) ⟨345182, by rfl⟩ : syracuseStep 1840973 = 690365) (by norm_num)
theorem B4142933 : Blo 1226431 4142933 := bbase (se 9 (by rfl) ⟨12137, by rfl⟩ : syracuseStep 4142933 = 24275) (by norm_num)
theorem B2070373 : Blo 1226431 2070373 := bbase (se 4 (by rfl) ⟨194097, by rfl⟩ : syracuseStep 2070373 = 388195) (by norm_num)
theorem B1840997 : Blo 1226431 1840997 := bbase (se 4 (by rfl) ⟨172593, by rfl⟩ : syracuseStep 1840997 = 345187) (by norm_num)
theorem B1841021 : Blo 1226431 1841021 := bbase (se 3 (by rfl) ⟨345191, by rfl⟩ : syracuseStep 1841021 = 690383) (by norm_num)
theorem B1841045 : Blo 1226431 1841045 := bbase (se 6 (by rfl) ⟨43149, by rfl⟩ : syracuseStep 1841045 = 86299) (by norm_num)
theorem B1554329 : Blo 1226431 1554329 := bbase (se 2 (by rfl) ⟨582873, by rfl⟩ : syracuseStep 1554329 = 1165747) (by norm_num)
theorem B2488229 : Blo 1226431 2488229 := bbase (se 4 (by rfl) ⟨233271, by rfl⟩ : syracuseStep 2488229 = 466543) (by norm_num)
theorem B1841069 : Blo 1226431 1841069 := bbase (se 3 (by rfl) ⟨345200, by rfl⟩ : syracuseStep 1841069 = 690401) (by norm_num)
theorem B2070461 : Blo 1226431 2070461 := bbase (se 3 (by rfl) ⟨388211, by rfl⟩ : syracuseStep 2070461 = 776423) (by norm_num)
theorem B1841093 : Blo 1226431 1841093 := bbase (se 4 (by rfl) ⟨172602, by rfl⟩ : syracuseStep 1841093 = 345205) (by norm_num)
theorem B1554385 : Blo 1226431 1554385 := bbase (se 2 (by rfl) ⟨582894, by rfl⟩ : syracuseStep 1554385 = 1165789) (by norm_num)
theorem B1841117 : Blo 1226431 1841117 := bbase (se 3 (by rfl) ⟨345209, by rfl⟩ : syracuseStep 1841117 = 690419) (by norm_num)
theorem B1841141 : Blo 1226431 1841141 := bbase (se 5 (by rfl) ⟨86303, by rfl⟩ : syracuseStep 1841141 = 172607) (by norm_num)
theorem B1841165 : Blo 1226431 1841165 := bbase (se 3 (by rfl) ⟨345218, by rfl⟩ : syracuseStep 1841165 = 690437) (by norm_num)
theorem B4659221 : Blo 1226431 4659221 := bbase (se 6 (by rfl) ⟨109200, by rfl⟩ : syracuseStep 4659221 = 218401) (by norm_num)
theorem B1841189 : Blo 1226431 1841189 := bbase (se 4 (by rfl) ⟨172611, by rfl⟩ : syracuseStep 1841189 = 345223) (by norm_num)
theorem B1554481 : Blo 1226431 1554481 := bbase (se 2 (by rfl) ⟨582930, by rfl⟩ : syracuseStep 1554481 = 1165861) (by norm_num)
theorem B2070589 : Blo 1226431 2070589 := bbase (se 3 (by rfl) ⟨388235, by rfl⟩ : syracuseStep 2070589 = 776471) (by norm_num)
theorem B1841213 : Blo 1226431 1841213 := bbase (se 3 (by rfl) ⟨345227, by rfl⟩ : syracuseStep 1841213 = 690455) (by norm_num)
theorem B2799677 : Blo 1226431 2799677 := bbase (se 3 (by rfl) ⟨524939, by rfl⟩ : syracuseStep 2799677 = 1049879) (by norm_num)
theorem B4978757 : Blo 1226431 4978757 := bbase (se 4 (by rfl) ⟨466758, by rfl⟩ : syracuseStep 4978757 = 933517) (by norm_num)
theorem B1841237 : Blo 1226431 1841237 := bbase (se 8 (by rfl) ⟨10788, by rfl⟩ : syracuseStep 1841237 = 21577) (by norm_num)
theorem B1841261 : Blo 1226431 1841261 := bbase (se 3 (by rfl) ⟨345236, by rfl⟩ : syracuseStep 1841261 = 690473) (by norm_num)
theorem B3930245 : Blo 1226431 3930245 := bbase (se 4 (by rfl) ⟨368460, by rfl⟩ : syracuseStep 3930245 = 736921) (by norm_num)
theorem B1841285 : Blo 1226431 1841285 := bbase (se 4 (by rfl) ⟨172620, by rfl⟩ : syracuseStep 1841285 = 345241) (by norm_num)
theorem B2070677 : Blo 1226431 2070677 := bbase (se 6 (by rfl) ⟨48531, by rfl⟩ : syracuseStep 2070677 = 97063) (by norm_num)
theorem B1841309 : Blo 1226431 1841309 := bbase (se 3 (by rfl) ⟨345245, by rfl⟩ : syracuseStep 1841309 = 690491) (by norm_num)
theorem B1841333 : Blo 1226431 1841333 := bbase (se 5 (by rfl) ⟨86312, by rfl⟩ : syracuseStep 1841333 = 172625) (by norm_num)
theorem B1841357 : Blo 1226431 1841357 := bbase (se 3 (by rfl) ⟨345254, by rfl⟩ : syracuseStep 1841357 = 690509) (by norm_num)
theorem B1579225 : Blo 1226431 1579225 := bbase (se 2 (by rfl) ⟨592209, by rfl⟩ : syracuseStep 1579225 = 1184419) (by norm_num)
theorem B1554653 : Blo 1226431 1554653 := bbase (se 3 (by rfl) ⟨291497, by rfl⟩ : syracuseStep 1554653 = 582995) (by norm_num)
theorem B1841381 : Blo 1226431 1841381 := bbase (se 4 (by rfl) ⟨172629, by rfl⟩ : syracuseStep 1841381 = 345259) (by norm_num)
theorem B1841405 : Blo 1226431 1841405 := bbase (se 3 (by rfl) ⟨345263, by rfl⟩ : syracuseStep 1841405 = 690527) (by norm_num)
theorem B3930373 : Blo 1226431 3930373 := bbase (se 4 (by rfl) ⟨368472, by rfl⟩ : syracuseStep 3930373 = 736945) (by norm_num)
theorem B4143365 : Blo 1226431 4143365 := bbase (se 4 (by rfl) ⟨388440, by rfl⟩ : syracuseStep 4143365 = 776881) (by norm_num)
theorem B2070805 : Blo 1226431 2070805 := bbase (se 6 (by rfl) ⟨48534, by rfl⟩ : syracuseStep 2070805 = 97069) (by norm_num)
theorem B1841429 : Blo 1226431 1841429 := bbase (se 6 (by rfl) ⟨43158, by rfl⟩ : syracuseStep 1841429 = 86317) (by norm_num)
theorem B1554709 : Blo 1226431 1554709 := bbase (se 6 (by rfl) ⟨36438, by rfl⟩ : syracuseStep 1554709 = 72877) (by norm_num)
theorem B2619677 : Blo 1226431 2619677 := bbase (se 3 (by rfl) ⟨491189, by rfl⟩ : syracuseStep 2619677 = 982379) (by norm_num)
theorem B1841453 : Blo 1226431 1841453 := bbase (se 3 (by rfl) ⟨345272, by rfl⟩ : syracuseStep 1841453 = 690545) (by norm_num)
theorem B1841477 : Blo 1226431 1841477 := bbase (se 4 (by rfl) ⟨172638, by rfl⟩ : syracuseStep 1841477 = 345277) (by norm_num)
theorem B2242885 : Blo 1226431 2242885 := bbase (se 4 (by rfl) ⟨210270, by rfl⟩ : syracuseStep 2242885 = 420541) (by norm_num)
theorem B1841501 : Blo 1226431 1841501 := bbase (se 3 (by rfl) ⟨345281, by rfl⟩ : syracuseStep 1841501 = 690563) (by norm_num)
theorem B2070893 : Blo 1226431 2070893 := bbase (se 3 (by rfl) ⟨388292, by rfl⟩ : syracuseStep 2070893 = 776585) (by norm_num)
theorem B1841525 : Blo 1226431 1841525 := bbase (se 5 (by rfl) ⟨86321, by rfl⟩ : syracuseStep 1841525 = 172643) (by norm_num)
theorem B1841549 : Blo 1226431 1841549 := bbase (se 3 (by rfl) ⟨345290, by rfl⟩ : syracuseStep 1841549 = 690581) (by norm_num)
theorem B5896597 : Blo 1226431 5896597 := bbase (se 6 (by rfl) ⟨138201, by rfl⟩ : syracuseStep 5896597 = 276403) (by norm_num)
theorem B1841573 : Blo 1226431 1841573 := bbase (se 4 (by rfl) ⟨172647, by rfl⟩ : syracuseStep 1841573 = 345295) (by norm_num)
theorem B6216101 : Blo 1226431 6216101 := bbase (se 4 (by rfl) ⟨582759, by rfl⟩ : syracuseStep 6216101 = 1165519) (by norm_num)
theorem B2619821 : Blo 1226431 2619821 := bbase (se 3 (by rfl) ⟨491216, by rfl⟩ : syracuseStep 2619821 = 982433) (by norm_num)
theorem B1841597 : Blo 1226431 1841597 := bbase (se 3 (by rfl) ⟨345299, by rfl⟩ : syracuseStep 1841597 = 690599) (by norm_num)
theorem B1841621 : Blo 1226431 1841621 := bbase (se 7 (by rfl) ⟨21581, by rfl⟩ : syracuseStep 1841621 = 43163) (by norm_num)
theorem B3496421 : Blo 1226431 3496421 := bbase (se 4 (by rfl) ⟨327789, by rfl⟩ : syracuseStep 3496421 = 655579) (by norm_num)
theorem B2071021 : Blo 1226431 2071021 := bbase (se 3 (by rfl) ⟨388316, by rfl⟩ : syracuseStep 2071021 = 776633) (by norm_num)
theorem B1841645 : Blo 1226431 1841645 := bbase (se 3 (by rfl) ⟨345308, by rfl⟩ : syracuseStep 1841645 = 690617) (by norm_num)
theorem B1841669 : Blo 1226431 1841669 := bbase (se 4 (by rfl) ⟨172656, by rfl⟩ : syracuseStep 1841669 = 345313) (by norm_num)
theorem B1866269 : Blo 1226431 1866269 := bbase (se 3 (by rfl) ⟨349925, by rfl⟩ : syracuseStep 1866269 = 699851) (by norm_num)
theorem B1841693 : Blo 1226431 1841693 := bbase (se 3 (by rfl) ⟨345317, by rfl⟩ : syracuseStep 1841693 = 690635) (by norm_num)
theorem B1841717 : Blo 1226431 1841717 := bbase (se 5 (by rfl) ⟨86330, by rfl⟩ : syracuseStep 1841717 = 172661) (by norm_num)
theorem B2071109 : Blo 1226431 2071109 := bbase (se 4 (by rfl) ⟨194166, by rfl⟩ : syracuseStep 2071109 = 388333) (by norm_num)
theorem B1841741 : Blo 1226431 1841741 := bbase (se 3 (by rfl) ⟨345326, by rfl⟩ : syracuseStep 1841741 = 690653) (by norm_num)
theorem B1841765 : Blo 1226431 1841765 := bbase (se 4 (by rfl) ⟨172665, by rfl⟩ : syracuseStep 1841765 = 345331) (by norm_num)
theorem B11188853 : Blo 1226431 11188853 := bbase (se 5 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 11188853 = 1048955) (by norm_num)
theorem B9837173 : Blo 1226431 9837173 := bbase (se 5 (by rfl) ⟨461117, by rfl⟩ : syracuseStep 9837173 = 922235) (by norm_num)
theorem B1841789 : Blo 1226431 1841789 := bbase (se 3 (by rfl) ⟨345335, by rfl⟩ : syracuseStep 1841789 = 690671) (by norm_num)
theorem B1841813 : Blo 1226431 1841813 := bbase (se 6 (by rfl) ⟨43167, by rfl⟩ : syracuseStep 1841813 = 86335) (by norm_num)
theorem B1866397 : Blo 1226431 1866397 := bbase (se 3 (by rfl) ⟨349949, by rfl⟩ : syracuseStep 1866397 = 699899) (by norm_num)
theorem B1841837 : Blo 1226431 1841837 := bbase (se 3 (by rfl) ⟨345344, by rfl⟩ : syracuseStep 1841837 = 690689) (by norm_num)
theorem B4143797 : Blo 1226431 4143797 := bbase (se 5 (by rfl) ⟨194240, by rfl⟩ : syracuseStep 4143797 = 388481) (by norm_num)
theorem B2071237 : Blo 1226431 2071237 := bbase (se 4 (by rfl) ⟨194178, by rfl⟩ : syracuseStep 2071237 = 388357) (by norm_num)
theorem B1841861 : Blo 1226431 1841861 := bbase (se 4 (by rfl) ⟨172674, by rfl⟩ : syracuseStep 1841861 = 345349) (by norm_num)
theorem B1841885 : Blo 1226431 1841885 := bbase (se 3 (by rfl) ⟨345353, by rfl⟩ : syracuseStep 1841885 = 690707) (by norm_num)
theorem B1841909 : Blo 1226431 1841909 := bbase (se 5 (by rfl) ⟨86339, by rfl⟩ : syracuseStep 1841909 = 172679) (by norm_num)
theorem B2947837 : Blo 1226431 2947837 := bbase (se 3 (by rfl) ⟨552719, by rfl⟩ : syracuseStep 2947837 = 1105439) (by norm_num)
theorem B1841933 : Blo 1226431 1841933 := bbase (se 3 (by rfl) ⟨345362, by rfl⟩ : syracuseStep 1841933 = 690725) (by norm_num)
theorem B2620181 : Blo 1226431 2620181 := bbase (se 6 (by rfl) ⟨61410, by rfl⟩ : syracuseStep 2620181 = 122821) (by norm_num)
theorem B2071325 : Blo 1226431 2071325 := bbase (se 3 (by rfl) ⟨388373, by rfl⟩ : syracuseStep 2071325 = 776747) (by norm_num)
theorem B1841957 : Blo 1226431 1841957 := bbase (se 4 (by rfl) ⟨172683, by rfl⟩ : syracuseStep 1841957 = 345367) (by norm_num)
theorem B1841981 : Blo 1226431 1841981 := bbase (se 3 (by rfl) ⟨345371, by rfl⟩ : syracuseStep 1841981 = 690743) (by norm_num)
theorem B1596233 : Blo 1226431 1596233 := bbase (se 2 (by rfl) ⟨598587, by rfl⟩ : syracuseStep 1596233 = 1197175) (by norm_num)
theorem B8846165 : Blo 1226431 8846165 := bbase (se 9 (by rfl) ⟨25916, by rfl⟩ : syracuseStep 8846165 = 51833) (by norm_num)
theorem B1842005 : Blo 1226431 1842005 := bbase (se 9 (by rfl) ⟨5396, by rfl⟩ : syracuseStep 1842005 = 10793) (by norm_num)
theorem B2759525 : Blo 1226431 2759525 := bbase (se 4 (by rfl) ⟨258705, by rfl⟩ : syracuseStep 2759525 = 517411) (by norm_num)
theorem B1842029 : Blo 1226431 1842029 := bbase (se 3 (by rfl) ⟨345380, by rfl⟩ : syracuseStep 1842029 = 690761) (by norm_num)
theorem B1964917 : Blo 1226431 1964917 := bbase (se 5 (by rfl) ⟨92105, by rfl⟩ : syracuseStep 1964917 = 184211) (by norm_num)
theorem B1842053 : Blo 1226431 1842053 := bbase (se 4 (by rfl) ⟨172692, by rfl⟩ : syracuseStep 1842053 = 345385) (by norm_num)
theorem B6986645 : Blo 1226431 6986645 := bbase (se 6 (by rfl) ⟨163749, by rfl⟩ : syracuseStep 6986645 = 327499) (by norm_num)
theorem B2071453 : Blo 1226431 2071453 := bbase (se 3 (by rfl) ⟨388397, by rfl⟩ : syracuseStep 2071453 = 776795) (by norm_num)
theorem B1842077 : Blo 1226431 1842077 := bbase (se 3 (by rfl) ⟨345389, by rfl⟩ : syracuseStep 1842077 = 690779) (by norm_num)
theorem B2759597 : Blo 1226431 2759597 := bbase (se 3 (by rfl) ⟨517424, by rfl⟩ : syracuseStep 2759597 = 1034849) (by norm_num)
theorem B1842101 : Blo 1226431 1842101 := bbase (se 5 (by rfl) ⟨86348, by rfl⟩ : syracuseStep 1842101 = 172697) (by norm_num)
theorem B1842125 : Blo 1226431 1842125 := bbase (se 3 (by rfl) ⟨345398, by rfl⟩ : syracuseStep 1842125 = 690797) (by norm_num)
theorem B2948069 : Blo 1226431 2948069 := bbase (se 4 (by rfl) ⟨276381, by rfl⟩ : syracuseStep 2948069 = 552763) (by norm_num)
theorem B5241829 : Blo 1226431 5241829 := bbase (se 4 (by rfl) ⟨491421, by rfl⟩ : syracuseStep 5241829 = 982843) (by norm_num)
theorem B1842149 : Blo 1226431 1842149 := bbase (se 4 (by rfl) ⟨172701, by rfl⟩ : syracuseStep 1842149 = 345403) (by norm_num)
theorem B2759669 : Blo 1226431 2759669 := bbase (se 5 (by rfl) ⟨129359, by rfl⟩ : syracuseStep 2759669 = 258719) (by norm_num)
theorem B2071541 : Blo 1226431 2071541 := bbase (se 5 (by rfl) ⟨97103, by rfl⟩ : syracuseStep 2071541 = 194207) (by norm_num)
theorem B1842173 : Blo 1226431 1842173 := bbase (se 3 (by rfl) ⟨345407, by rfl⟩ : syracuseStep 1842173 = 690815) (by norm_num)
theorem B1842197 : Blo 1226431 1842197 := bbase (se 6 (by rfl) ⟨43176, by rfl⟩ : syracuseStep 1842197 = 86353) (by norm_num)
theorem B1842221 : Blo 1226431 1842221 := bbase (se 3 (by rfl) ⟨345416, by rfl⟩ : syracuseStep 1842221 = 690833) (by norm_num)
theorem B2759741 : Blo 1226431 2759741 := bbase (se 3 (by rfl) ⟨517451, by rfl⟩ : syracuseStep 2759741 = 1034903) (by norm_num)
theorem B1842245 : Blo 1226431 1842245 := bbase (se 4 (by rfl) ⟨172710, by rfl⟩ : syracuseStep 1842245 = 345421) (by norm_num)
theorem B1842269 : Blo 1226431 1842269 := bbase (se 3 (by rfl) ⟨345425, by rfl⟩ : syracuseStep 1842269 = 690851) (by norm_num)
theorem B4144229 : Blo 1226431 4144229 := bbase (se 4 (by rfl) ⟨388521, by rfl⟩ : syracuseStep 4144229 = 777043) (by norm_num)
theorem B2948213 : Blo 1226431 2948213 := bbase (se 5 (by rfl) ⟨138197, by rfl⟩ : syracuseStep 2948213 = 276395) (by norm_num)
theorem B2071669 : Blo 1226431 2071669 := bbase (se 5 (by rfl) ⟨97109, by rfl⟩ : syracuseStep 2071669 = 194219) (by norm_num)
theorem B1842293 : Blo 1226431 1842293 := bbase (se 5 (by rfl) ⟨86357, by rfl⟩ : syracuseStep 1842293 = 172715) (by norm_num)
theorem B1309817 : Blo 1226431 1309817 := bbase (se 2 (by rfl) ⟨491181, by rfl⟩ : syracuseStep 1309817 = 982363) (by norm_num)
theorem B2759813 : Blo 1226431 2759813 := bbase (se 4 (by rfl) ⟨258732, by rfl⟩ : syracuseStep 2759813 = 517465) (by norm_num)
theorem B1842317 : Blo 1226431 1842317 := bbase (se 3 (by rfl) ⟨345434, by rfl⟩ : syracuseStep 1842317 = 690869) (by norm_num)
theorem B3734677 : Blo 1226431 3734677 := bbase (se 6 (by rfl) ⟨87531, by rfl⟩ : syracuseStep 3734677 = 175063) (by norm_num)
theorem B1842341 : Blo 1226431 1842341 := bbase (se 4 (by rfl) ⟨172719, by rfl⟩ : syracuseStep 1842341 = 345439) (by norm_num)
theorem B1244333 : Blo 1226431 1244333 := bbase (se 3 (by rfl) ⟨233312, by rfl⟩ : syracuseStep 1244333 = 466625) (by norm_num)
theorem B1842365 : Blo 1226431 1842365 := bbase (se 3 (by rfl) ⟨345443, by rfl⟩ : syracuseStep 1842365 = 690887) (by norm_num)
theorem B2759885 : Blo 1226431 2759885 := bbase (se 3 (by rfl) ⟨517478, by rfl⟩ : syracuseStep 2759885 = 1034957) (by norm_num)
theorem B2071757 : Blo 1226431 2071757 := bbase (se 3 (by rfl) ⟨388454, by rfl⟩ : syracuseStep 2071757 = 776909) (by norm_num)
theorem B4259029 : Blo 1226431 4259029 := bbase (se 7 (by rfl) ⟨49910, by rfl⟩ : syracuseStep 4259029 = 99821) (by norm_num)
theorem B1842389 : Blo 1226431 1842389 := bbase (se 7 (by rfl) ⟨21590, by rfl⟩ : syracuseStep 1842389 = 43181) (by norm_num)
theorem B1473761 : Blo 1226431 1473761 := bbase (se 2 (by rfl) ⟨552660, by rfl⟩ : syracuseStep 1473761 = 1105321) (by norm_num)
theorem B2489573 : Blo 1226431 2489573 := bbase (se 4 (by rfl) ⟨233397, by rfl⟩ : syracuseStep 2489573 = 466795) (by norm_num)
theorem B1842413 : Blo 1226431 1842413 := bbase (se 3 (by rfl) ⟨345452, by rfl⟩ : syracuseStep 1842413 = 690905) (by norm_num)
theorem B1842437 : Blo 1226431 1842437 := bbase (se 4 (by rfl) ⟨172728, by rfl⟩ : syracuseStep 1842437 = 345457) (by norm_num)
theorem B2759957 : Blo 1226431 2759957 := bbase (se 6 (by rfl) ⟨64686, by rfl⟩ : syracuseStep 2759957 = 129373) (by norm_num)
theorem B1842461 : Blo 1226431 1842461 := bbase (se 3 (by rfl) ⟨345461, by rfl⟩ : syracuseStep 1842461 = 690923) (by norm_num)
theorem B1842485 : Blo 1226431 1842485 := bbase (se 5 (by rfl) ⟨86366, by rfl⟩ : syracuseStep 1842485 = 172733) (by norm_num)
theorem B2071885 : Blo 1226431 2071885 := bbase (se 3 (by rfl) ⟨388478, by rfl⟩ : syracuseStep 2071885 = 776957) (by norm_num)
theorem B1842509 : Blo 1226431 1842509 := bbase (se 3 (by rfl) ⟨345470, by rfl⟩ : syracuseStep 1842509 = 690941) (by norm_num)
theorem B23928149 : Blo 1226431 23928149 := bbase (se 11 (by rfl) ⟨17525, by rfl⟩ : syracuseStep 23928149 = 35051) (by norm_num)
theorem B2760029 : Blo 1226431 2760029 := bbase (se 3 (by rfl) ⟨517505, by rfl⟩ : syracuseStep 2760029 = 1035011) (by norm_num)
theorem B2948453 : Blo 1226431 2948453 := bbase (se 4 (by rfl) ⟨276417, by rfl⟩ : syracuseStep 2948453 = 552835) (by norm_num)
theorem B1842533 : Blo 1226431 1842533 := bbase (se 4 (by rfl) ⟨172737, by rfl⟩ : syracuseStep 1842533 = 345475) (by norm_num)
theorem B1842557 : Blo 1226431 1842557 := bbase (se 3 (by rfl) ⟨345479, by rfl⟩ : syracuseStep 1842557 = 690959) (by norm_num)
theorem B1842581 : Blo 1226431 1842581 := bbase (se 6 (by rfl) ⟨43185, by rfl⟩ : syracuseStep 1842581 = 86371) (by norm_num)
theorem B2760101 : Blo 1226431 2760101 := bbase (se 4 (by rfl) ⟨258759, by rfl⟩ : syracuseStep 2760101 = 517519) (by norm_num)
theorem B2071973 : Blo 1226431 2071973 := bbase (se 4 (by rfl) ⟨194247, by rfl⟩ : syracuseStep 2071973 = 388495) (by norm_num)
theorem B1842605 : Blo 1226431 1842605 := bbase (se 3 (by rfl) ⟨345488, by rfl⟩ : syracuseStep 1842605 = 690977) (by norm_num)
theorem B1244593 : Blo 1226431 1244593 := bbase (se 2 (by rfl) ⟨466722, by rfl⟩ : syracuseStep 1244593 = 933445) (by norm_num)
theorem B1842629 : Blo 1226431 1842629 := bbase (se 4 (by rfl) ⟨172746, by rfl⟩ : syracuseStep 1842629 = 345493) (by norm_num)
theorem B2760173 : Blo 1226431 2760173 := bbase (se 3 (by rfl) ⟨517532, by rfl⟩ : syracuseStep 2760173 = 1035065) (by norm_num)
theorem B1244657 : Blo 1226431 1244657 := bbase (se 2 (by rfl) ⟨466746, by rfl⟩ : syracuseStep 1244657 = 933493) (by norm_num)
theorem B3317269 : Blo 1226431 3317269 := bbase (se 6 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 3317269 = 155497) (by norm_num)
theorem B4144661 : Blo 1226431 4144661 := bbase (se 6 (by rfl) ⟨97140, by rfl⟩ : syracuseStep 4144661 = 194281) (by norm_num)
theorem B2072101 : Blo 1226431 2072101 := bbase (se 4 (by rfl) ⟨194259, by rfl⟩ : syracuseStep 2072101 = 388519) (by norm_num)
theorem B2760245 : Blo 1226431 2760245 := bbase (se 5 (by rfl) ⟨129386, by rfl⟩ : syracuseStep 2760245 = 258773) (by norm_num)
theorem B1310261 : Blo 1226431 1310261 := bbase (se 5 (by rfl) ⟨61418, by rfl⟩ : syracuseStep 1310261 = 122837) (by norm_num)
theorem B2760317 : Blo 1226431 2760317 := bbase (se 3 (by rfl) ⟨517559, by rfl⟩ : syracuseStep 2760317 = 1035119) (by norm_num)
theorem B2072189 : Blo 1226431 2072189 := bbase (se 3 (by rfl) ⟨388535, by rfl⟩ : syracuseStep 2072189 = 777071) (by norm_num)
theorem B2621069 : Blo 1226431 2621069 := bbase (se 3 (by rfl) ⟨491450, by rfl⟩ : syracuseStep 2621069 = 982901) (by norm_num)
theorem B2916013 : Blo 1226431 2916013 := bbase (se 3 (by rfl) ⟨546752, by rfl⟩ : syracuseStep 2916013 = 1093505) (by norm_num)
theorem B6217397 : Blo 1226431 6217397 := bbase (se 5 (by rfl) ⟨291440, by rfl⟩ : syracuseStep 6217397 = 582881) (by norm_num)
theorem B2760389 : Blo 1226431 2760389 := bbase (se 4 (by rfl) ⟨258786, by rfl⟩ : syracuseStep 2760389 = 517573) (by norm_num)
theorem B2490061 : Blo 1226431 2490061 := bbase (se 3 (by rfl) ⟨466886, by rfl⟩ : syracuseStep 2490061 = 933773) (by norm_num)
theorem B3104477 : Blo 1226431 3104477 := bbase (se 3 (by rfl) ⟨582089, by rfl⟩ : syracuseStep 3104477 = 1164179) (by norm_num)
theorem B1244917 : Blo 1226431 1244917 := bbase (se 5 (by rfl) ⟨58355, by rfl⟩ : syracuseStep 1244917 = 116711) (by norm_num)
theorem B2072317 : Blo 1226431 2072317 := bbase (se 3 (by rfl) ⟨388559, by rfl⟩ : syracuseStep 2072317 = 777119) (by norm_num)
theorem B2760461 : Blo 1226431 2760461 := bbase (se 3 (by rfl) ⟨517586, by rfl⟩ : syracuseStep 2760461 = 1035173) (by norm_num)
theorem B2801429 : Blo 1226431 2801429 := bbase (se 6 (by rfl) ⟨65658, by rfl⟩ : syracuseStep 2801429 = 131317) (by norm_num)
theorem B1310509 : Blo 1226431 1310509 := bbase (se 3 (by rfl) ⟨245720, by rfl⟩ : syracuseStep 1310509 = 491441) (by norm_num)
theorem B6635317 : Blo 1226431 6635317 := bbase (se 5 (by rfl) ⟨311030, by rfl⟩ : syracuseStep 6635317 = 622061) (by norm_num)
theorem B2760533 : Blo 1226431 2760533 := bbase (se 9 (by rfl) ⟨8087, by rfl⟩ : syracuseStep 2760533 = 16175) (by norm_num)
theorem B2072405 : Blo 1226431 2072405 := bbase (se 9 (by rfl) ⟨6071, by rfl⟩ : syracuseStep 2072405 = 12143) (by norm_num)
theorem B1965917 : Blo 1226431 1965917 := bbase (se 3 (by rfl) ⟨368609, by rfl⟩ : syracuseStep 1965917 = 737219) (by norm_num)
theorem B2621317 : Blo 1226431 2621317 := bbase (se 4 (by rfl) ⟨245748, by rfl⟩ : syracuseStep 2621317 = 491497) (by norm_num)
theorem B4202389 : Blo 1226431 4202389 := bbase (se 6 (by rfl) ⟨98493, by rfl⟩ : syracuseStep 4202389 = 196987) (by norm_num)
theorem B3104669 : Blo 1226431 3104669 := bbase (se 3 (by rfl) ⟨582125, by rfl⟩ : syracuseStep 3104669 = 1164251) (by norm_num)
theorem B2760605 : Blo 1226431 2760605 := bbase (se 3 (by rfl) ⟨517613, by rfl⟩ : syracuseStep 2760605 = 1035227) (by norm_num)
theorem B3317701 : Blo 1226431 3317701 := bbase (se 4 (by rfl) ⟨311034, by rfl⟩ : syracuseStep 3317701 = 622069) (by norm_num)
theorem B4145093 : Blo 1226431 4145093 := bbase (se 4 (by rfl) ⟨388602, by rfl⟩ : syracuseStep 4145093 = 777205) (by norm_num)
theorem B2072533 : Blo 1226431 2072533 := bbase (se 7 (by rfl) ⟨24287, by rfl⟩ : syracuseStep 2072533 = 48575) (by norm_num)
theorem B2760677 : Blo 1226431 2760677 := bbase (se 4 (by rfl) ⟨258813, by rfl⟩ : syracuseStep 2760677 = 517627) (by norm_num)
theorem B4145201 : Blo 1226431 4145201 := bstep (se 2 (by rfl) ⟨1554450, by rfl⟩ : syracuseStep 4145201 = 3108901) B3108901
theorem B2072641 : Blo 1226431 2072641 := bstep (se 2 (by rfl) ⟨777240, by rfl⟩ : syracuseStep 2072641 = 1554481) B1554481
theorem B3498061 : Blo 1226431 3498061 := bstep (se 3 (by rfl) ⟨655886, by rfl⟩ : syracuseStep 3498061 = 1311773) B1311773
theorem B2760785 : Blo 1226431 2760785 := bstep (se 2 (by rfl) ⟨1035294, by rfl⟩ : syracuseStep 2760785 = 2070589) B2070589
theorem B2760803 : Blo 1226431 2760803 := bstep (se 1 (by rfl) ⟨2070602, by rfl⟩ : syracuseStep 2760803 = 4141205) B4141205
theorem B4661347 : Blo 1226431 4661347 := bstep (se 1 (by rfl) ⟨3496010, by rfl⟩ : syracuseStep 4661347 = 6992021) B6992021
theorem B2072675 : Blo 1226431 2072675 := bstep (se 1 (by rfl) ⟨1554506, by rfl⟩ : syracuseStep 2072675 = 3109013) B3109013
theorem B3104963 : Blo 1226431 3104963 := bstep (se 1 (by rfl) ⟨2328722, by rfl⟩ : syracuseStep 3104963 = 4657445) B4657445
theorem B2072803 : Blo 1226431 2072803 := bstep (se 1 (by rfl) ⟨1554602, by rfl⟩ : syracuseStep 2072803 = 3109205) B3109205
theorem B7864589 : Blo 1226431 7864589 := bstep (se 3 (by rfl) ⟨1474610, by rfl⟩ : syracuseStep 7864589 = 2949221) B2949221
theorem B2105633 : Blo 1226431 2105633 := bstep (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) B1579225
theorem B2761073 : Blo 1226431 2761073 := bstep (se 2 (by rfl) ⟨1035402, by rfl⟩ : syracuseStep 2761073 = 2070805) B2070805
theorem B2072945 : Blo 1226431 2072945 := bstep (se 2 (by rfl) ⟨777354, by rfl⟩ : syracuseStep 2072945 = 1554709) B1554709
theorem B3105155 : Blo 1226431 3105155 := bstep (se 1 (by rfl) ⟨2328866, by rfl⟩ : syracuseStep 3105155 = 4657733) B4657733
theorem B2761091 : Blo 1226431 2761091 := bstep (se 1 (by rfl) ⟨2070818, by rfl⟩ : syracuseStep 2761091 = 4141637) B4141637
theorem B5898673 : Blo 1226431 5898673 := bstep (se 2 (by rfl) ⟨2212002, by rfl⟩ : syracuseStep 5898673 = 4424005) B4424005
theorem B2990513 : Blo 1226431 2990513 := bstep (se 2 (by rfl) ⟨1121442, by rfl⟩ : syracuseStep 2990513 = 2242885) B2242885
theorem B3318221 : Blo 1226431 3318221 := bstep (se 3 (by rfl) ⟨622166, by rfl⟩ : syracuseStep 3318221 = 1244333) B1244333
theorem B1966609 : Blo 1226431 1966609 := bstep (se 2 (by rfl) ⟨737478, by rfl⟩ : syracuseStep 1966609 = 1474957) B1474957
theorem B4145741 : Blo 1226431 4145741 := bstep (se 3 (by rfl) ⟨777326, by rfl⟩ : syracuseStep 4145741 = 1554653) B1554653
theorem B4145795 : Blo 1226431 4145795 := bstep (se 1 (by rfl) ⟨3109346, by rfl⟩ : syracuseStep 4145795 = 6218693) B6218693
theorem B2761361 : Blo 1226431 2761361 := bstep (se 2 (by rfl) ⟨1035510, by rfl⟩ : syracuseStep 2761361 = 2071021) B2071021
theorem B2761379 : Blo 1226431 2761379 := bstep (se 1 (by rfl) ⟨2071034, by rfl⟩ : syracuseStep 2761379 = 4142069) B4142069
theorem B2622179 : Blo 1226431 2622179 := bstep (se 1 (by rfl) ⟨1966634, by rfl⟩ : syracuseStep 2622179 = 3933269) B3933269
theorem B6218531 : Blo 1226431 6218531 := bstep (se 1 (by rfl) ⟨4663898, by rfl⟩ : syracuseStep 6218531 = 9327797) B9327797
theorem B2360195 : Blo 1226431 2360195 := bstep (se 1 (by rfl) ⟨1770146, by rfl⟩ : syracuseStep 2360195 = 3540293) B3540293
theorem B1475491 : Blo 1226431 1475491 := bstep (se 1 (by rfl) ⟨1106618, by rfl⟩ : syracuseStep 1475491 = 2213237) B2213237
theorem B2761649 : Blo 1226431 2761649 := bstep (se 2 (by rfl) ⟨1035618, by rfl⟩ : syracuseStep 2761649 = 2071237) B2071237
theorem B2761667 : Blo 1226431 2761667 := bstep (se 1 (by rfl) ⟨2071250, by rfl⟩ : syracuseStep 2761667 = 4142501) B4142501
theorem B2098129 : Blo 1226431 2098129 := bstep (se 2 (by rfl) ⟨786798, by rfl⟩ : syracuseStep 2098129 = 1573597) B1573597
theorem B2761937 : Blo 1226431 2761937 := bstep (se 2 (by rfl) ⟨1035726, by rfl⟩ : syracuseStep 2761937 = 2071453) B2071453
theorem B2761955 : Blo 1226431 2761955 := bstep (se 1 (by rfl) ⟨2071466, by rfl⟩ : syracuseStep 2761955 = 4142933) B4142933
theorem B3319085 : Blo 1226431 3319085 := bstep (se 3 (by rfl) ⟨622328, by rfl⟩ : syracuseStep 3319085 = 1244657) B1244657
theorem B2245937 : Blo 1226431 2245937 := bstep (se 2 (by rfl) ⟨842226, by rfl⟩ : syracuseStep 2245937 = 1684453) B1684453
theorem B3106097 : Blo 1226431 3106097 := bstep (se 2 (by rfl) ⟨1164786, by rfl⟩ : syracuseStep 3106097 = 2329573) B2329573
theorem B6989105 : Blo 1226431 6989105 := bstep (se 2 (by rfl) ⟨2620914, by rfl⟩ : syracuseStep 6989105 = 5241829) B5241829
theorem B1770817 : Blo 1226431 1770817 := bstep (se 2 (by rfl) ⟨664056, by rfl⟩ : syracuseStep 1770817 = 1328113) B1328113
theorem B3106147 : Blo 1226431 3106147 := bstep (se 1 (by rfl) ⟨2329610, by rfl⟩ : syracuseStep 3106147 = 4659221) B4659221
theorem B4425101 : Blo 1226431 4425101 := bstep (se 3 (by rfl) ⟨829706, by rfl⟩ : syracuseStep 4425101 = 1659413) B1659413
theorem B2835953 : Blo 1226431 2835953 := bstep (se 2 (by rfl) ⟨1063482, by rfl⟩ : syracuseStep 2835953 = 2126965) B2126965
theorem B3106289 : Blo 1226431 3106289 := bstep (se 2 (by rfl) ⟨1164858, by rfl⟩ : syracuseStep 3106289 = 2329717) B2329717
theorem B2762225 : Blo 1226431 2762225 := bstep (se 2 (by rfl) ⟨1035834, by rfl⟩ : syracuseStep 2762225 = 2071669) B2071669
theorem B2762243 : Blo 1226431 2762243 := bstep (se 1 (by rfl) ⟨2071682, by rfl⟩ : syracuseStep 2762243 = 4143365) B4143365
theorem B2950673 : Blo 1226431 2950673 := bstep (se 2 (by rfl) ⟨1106502, by rfl⟩ : syracuseStep 2950673 = 2213005) B2213005
theorem B1746451 : Blo 1226431 1746451 := bstep (se 1 (by rfl) ⟨1309838, by rfl⟩ : syracuseStep 1746451 = 2619677) B2619677
theorem B1795649 : Blo 1226431 1795649 := bstep (se 2 (by rfl) ⟨673368, by rfl⟩ : syracuseStep 1795649 = 1346737) B1346737
theorem B5678705 : Blo 1226431 5678705 := bstep (se 2 (by rfl) ⟨2129514, by rfl⟩ : syracuseStep 5678705 = 4259029) B4259029
theorem B3933859 : Blo 1226431 3933859 := bstep (se 1 (by rfl) ⟨2950394, by rfl⟩ : syracuseStep 3933859 = 5900789) B5900789
theorem B2762513 : Blo 1226431 2762513 := bstep (se 2 (by rfl) ⟨1035942, by rfl⟩ : syracuseStep 2762513 = 2071885) B2071885
theorem B2762531 : Blo 1226431 2762531 := bstep (se 1 (by rfl) ⟨2071898, by rfl⟩ : syracuseStep 2762531 = 4143797) B4143797
theorem B8963909 : Blo 1226431 8963909 := bstep (se 4 (by rfl) ⟨840366, by rfl⟩ : syracuseStep 8963909 = 1680733) B1680733
theorem B2328419 : Blo 1226431 2328419 := bstep (se 1 (by rfl) ⟨1746314, by rfl⟩ : syracuseStep 2328419 = 3492629) B3492629
theorem B1746787 : Blo 1226431 1746787 := bstep (se 1 (by rfl) ⟨1310090, by rfl⟩ : syracuseStep 1746787 = 2620181) B2620181
theorem B1328995 : Blo 1226431 1328995 := bstep (se 1 (by rfl) ⟨996746, by rfl⟩ : syracuseStep 1328995 = 1993493) B1993493
theorem B3934129 : Blo 1226431 3934129 := bstep (se 2 (by rfl) ⟨1475298, by rfl⟩ : syracuseStep 3934129 = 2950597) B2950597
theorem B10479557 : Blo 1226431 10479557 := bstep (se 4 (by rfl) ⟨982458, by rfl⟩ : syracuseStep 10479557 = 1964917) B1964917
theorem B4974641 : Blo 1226431 4974641 := bstep (se 2 (by rfl) ⟨1865490, by rfl⟩ : syracuseStep 4974641 = 3730981) B3730981
theorem B2762801 : Blo 1226431 2762801 := bstep (se 2 (by rfl) ⟨1036050, by rfl⟩ : syracuseStep 2762801 = 2072101) B2072101
theorem B1329203 : Blo 1226431 1329203 := bstep (se 1 (by rfl) ⟨996902, by rfl⟩ : syracuseStep 1329203 = 1993805) B1993805
theorem B3237937 : Blo 1226431 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B2762819 : Blo 1226431 2762819 := bstep (se 1 (by rfl) ⟨2072114, by rfl⟩ : syracuseStep 2762819 = 4144229) B4144229
theorem B15952099 : Blo 1226431 15952099 := bstep (se 1 (by rfl) ⟨11964074, by rfl⟩ : syracuseStep 15952099 = 23928149) B23928149
theorem B4663565 : Blo 1226431 4663565 := bstep (se 3 (by rfl) ⟨874418, by rfl⟩ : syracuseStep 4663565 = 1748837) B1748837
theorem B3320081 : Blo 1226431 3320081 := bstep (se 2 (by rfl) ⟨1245030, by rfl⟩ : syracuseStep 3320081 = 2490061) B2490061
theorem B6211889 : Blo 1226431 6211889 := bstep (se 2 (by rfl) ⟨2329458, by rfl⟩ : syracuseStep 6211889 = 4658917) B4658917
theorem B2763089 : Blo 1226431 2763089 := bstep (se 2 (by rfl) ⟨1036158, by rfl⟩ : syracuseStep 2763089 = 2072317) B2072317
theorem B2763107 : Blo 1226431 2763107 := bstep (se 1 (by rfl) ⟨2072330, by rfl⟩ : syracuseStep 2763107 = 4144661) B4144661
theorem B1747345 : Blo 1226431 1747345 := bstep (se 2 (by rfl) ⟨655254, by rfl⟩ : syracuseStep 1747345 = 1310509) B1310509
theorem B1747379 : Blo 1226431 1747379 := bstep (se 1 (by rfl) ⟨1310534, by rfl⟩ : syracuseStep 1747379 = 2621069) B2621069
theorem B7866821 : Blo 1226431 7866821 := bstep (se 4 (by rfl) ⟨737514, by rfl⟩ : syracuseStep 7866821 = 1475029) B1475029
theorem B3107281 : Blo 1226431 3107281 := bstep (se 2 (by rfl) ⟨1165230, by rfl⟩ : syracuseStep 3107281 = 2330461) B2330461
theorem B13273571 : Blo 1226431 13273571 := bstep (se 1 (by rfl) ⟨9955178, by rfl⟩ : syracuseStep 13273571 = 19910357) B19910357
theorem B10488305 : Blo 1226431 10488305 := bstep (se 2 (by rfl) ⟨3933114, by rfl⟩ : syracuseStep 10488305 = 7866229) B7866229
theorem B2763377 : Blo 1226431 2763377 := bstep (se 2 (by rfl) ⟨1036266, by rfl⟩ : syracuseStep 2763377 = 2072533) B2072533
theorem B2763395 : Blo 1226431 2763395 := bstep (se 1 (by rfl) ⟨2072546, by rfl⟩ : syracuseStep 2763395 = 4145093) B4145093
theorem B4139693 : Blo 1226431 4139693 := bstep (se 3 (by rfl) ⟨776192, by rfl⟩ : syracuseStep 4139693 = 1552385) B1552385
theorem B4139747 : Blo 1226431 4139747 := bstep (se 1 (by rfl) ⟨3104810, by rfl⟩ : syracuseStep 4139747 = 6209621) B6209621
theorem B6990563 : Blo 1226431 6990563 := bstep (se 1 (by rfl) ⟨5242922, by rfl⟩ : syracuseStep 6990563 = 10485845) B10485845
theorem B3107555 : Blo 1226431 3107555 := bstep (se 1 (by rfl) ⟨2330666, by rfl⟩ : syracuseStep 3107555 = 4661333) B4661333
theorem B9317105 : Blo 1226431 9317105 := bstep (se 2 (by rfl) ⟨3493914, by rfl⟩ : syracuseStep 9317105 = 6987829) B6987829
theorem B9956195 : Blo 1226431 9956195 := bstep (se 1 (by rfl) ⟨7467146, by rfl⟩ : syracuseStep 9956195 = 14934293) B14934293
theorem B2329489 : Blo 1226431 2329489 := bstep (se 2 (by rfl) ⟨873558, by rfl⟩ : syracuseStep 2329489 = 1747117) B1747117
theorem B2763665 : Blo 1226431 2763665 := bstep (se 2 (by rfl) ⟨1036374, by rfl⟩ : syracuseStep 2763665 = 2072749) B2072749
theorem B3107747 : Blo 1226431 3107747 := bstep (se 1 (by rfl) ⟨2330810, by rfl⟩ : syracuseStep 3107747 = 4661621) B4661621
theorem B2763683 : Blo 1226431 2763683 := bstep (se 1 (by rfl) ⟨2072762, by rfl⟩ : syracuseStep 2763683 = 4145525) B4145525
theorem B1747937 : Blo 1226431 1747937 := bstep (se 2 (by rfl) ⟨655476, by rfl⟩ : syracuseStep 1747937 = 1310953) B1310953
theorem B3492845 : Blo 1226431 3492845 := bstep (se 3 (by rfl) ⟨654908, by rfl⟩ : syracuseStep 3492845 = 1309817) B1309817
theorem B4140017 : Blo 1226431 4140017 := bstep (se 2 (by rfl) ⟨1552506, by rfl⟩ : syracuseStep 4140017 = 3105013) B3105013
theorem B1748017 : Blo 1226431 1748017 := bstep (se 2 (by rfl) ⟨655506, by rfl⟩ : syracuseStep 1748017 = 1311013) B1311013
theorem B2763953 : Blo 1226431 2763953 := bstep (se 2 (by rfl) ⟨1036482, by rfl⟩ : syracuseStep 2763953 = 2072965) B2072965
theorem B2763971 : Blo 1226431 2763971 := bstep (se 1 (by rfl) ⟨2072978, by rfl⟩ : syracuseStep 2763971 = 4145957) B4145957
theorem B6638861 : Blo 1226431 6638861 := bstep (se 3 (by rfl) ⟨1244786, by rfl⟩ : syracuseStep 6638861 = 2489573) B2489573
theorem B23604533 : Blo 1226431 23604533 := bstep (se 5 (by rfl) ⟨1106462, by rfl⟩ : syracuseStep 23604533 = 2212925) B2212925
theorem B4140557 : Blo 1226431 4140557 := bstep (se 3 (by rfl) ⟨776354, by rfl⟩ : syracuseStep 4140557 = 1552709) B1552709
theorem B5246477 : Blo 1226431 5246477 := bstep (se 3 (by rfl) ⟨983714, by rfl⟩ : syracuseStep 5246477 = 1967429) B1967429
theorem B1379875 : Blo 1226431 1379875 := bstep (se 1 (by rfl) ⟨1034906, by rfl⟩ : syracuseStep 1379875 = 2069813) B2069813
theorem B4140611 : Blo 1226431 4140611 := bstep (se 1 (by rfl) ⟨3105458, by rfl⟩ : syracuseStep 4140611 = 6210917) B6210917
theorem B1380019 : Blo 1226431 1380019 := bstep (se 1 (by rfl) ⟨1035014, by rfl⟩ : syracuseStep 1380019 = 2070029) B2070029
theorem B9440995 : Blo 1226431 9440995 := bstep (se 1 (by rfl) ⟨7080746, by rfl⟩ : syracuseStep 9440995 = 14161493) B14161493
theorem B6213347 : Blo 1226431 6213347 := bstep (se 1 (by rfl) ⟨4660010, by rfl⟩ : syracuseStep 6213347 = 9320021) B9320021
theorem B5598989 : Blo 1226431 5598989 := bstep (se 3 (by rfl) ⟨1049810, by rfl⟩ : syracuseStep 5598989 = 2099621) B2099621
theorem B1380163 : Blo 1226431 1380163 := bstep (se 1 (by rfl) ⟨1035122, by rfl⟩ : syracuseStep 1380163 = 2070245) B2070245
theorem B1748803 : Blo 1226431 1748803 := bstep (se 1 (by rfl) ⟨1311602, by rfl⟩ : syracuseStep 1748803 = 2623205) B2623205
theorem B4656973 : Blo 1226431 4656973 := bstep (se 3 (by rfl) ⟨873182, by rfl⟩ : syracuseStep 4656973 = 1746365) B1746365
theorem B4140881 : Blo 1226431 4140881 := bstep (se 2 (by rfl) ⟨1552830, by rfl⟩ : syracuseStep 4140881 = 3105661) B3105661
theorem B3108689 : Blo 1226431 3108689 := bstep (se 2 (by rfl) ⟨1165758, by rfl⟩ : syracuseStep 3108689 = 2331517) B2331517
theorem B5246819 : Blo 1226431 5246819 := bstep (se 1 (by rfl) ⟨3935114, by rfl⟩ : syracuseStep 5246819 = 7870229) B7870229
theorem B3108739 : Blo 1226431 3108739 := bstep (se 1 (by rfl) ⟨2331554, by rfl⟩ : syracuseStep 3108739 = 4663109) B4663109
theorem B2330545 : Blo 1226431 2330545 := bstep (se 2 (by rfl) ⟨873954, by rfl⟩ : syracuseStep 2330545 = 1747909) B1747909
theorem B1658819 : Blo 1226431 1658819 := bstep (se 1 (by rfl) ⟨1244114, by rfl⟩ : syracuseStep 1658819 = 2488229) B2488229
theorem B1380307 : Blo 1226431 1380307 := bstep (se 1 (by rfl) ⟨1035230, by rfl⟩ : syracuseStep 1380307 = 2070461) B2070461
theorem B5238755 : Blo 1226431 5238755 := bstep (se 1 (by rfl) ⟨3929066, by rfl⟩ : syracuseStep 5238755 = 7858133) B7858133
theorem B3108881 : Blo 1226431 3108881 := bstep (se 2 (by rfl) ⟨1165830, by rfl⟩ : syracuseStep 3108881 = 2331661) B2331661
theorem B4255811 : Blo 1226431 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B1380451 : Blo 1226431 1380451 := bstep (se 1 (by rfl) ⟨1035338, by rfl⟩ : syracuseStep 1380451 = 2070677) B2070677
theorem B3494029 : Blo 1226431 3494029 := bstep (se 3 (by rfl) ⟨655130, by rfl⟩ : syracuseStep 3494029 = 1310261) B1310261
theorem B1552547 : Blo 1226431 1552547 := bstep (se 1 (by rfl) ⟨1164410, by rfl⟩ : syracuseStep 1552547 = 2328821) B2328821
theorem B5902577 : Blo 1226431 5902577 := bstep (se 2 (by rfl) ⟨2213466, by rfl⟩ : syracuseStep 5902577 = 4426933) B4426933
theorem B1380595 : Blo 1226431 1380595 := bstep (se 1 (by rfl) ⟨1035446, by rfl⟩ : syracuseStep 1380595 = 2070893) B2070893
theorem B2330947 : Blo 1226431 2330947 := bstep (se 1 (by rfl) ⟨1748210, by rfl⟩ : syracuseStep 2330947 = 3496421) B3496421
theorem B4141421 : Blo 1226431 4141421 := bstep (se 3 (by rfl) ⟨776516, by rfl⟩ : syracuseStep 4141421 = 1553033) B1553033
theorem B2330993 : Blo 1226431 2330993 := bstep (se 2 (by rfl) ⟨874122, by rfl⟩ : syracuseStep 2330993 = 1748245) B1748245
theorem B33616241 : Blo 1226431 33616241 := bstep (se 2 (by rfl) ⟨12606090, by rfl⟩ : syracuseStep 33616241 = 25212181) B25212181
theorem B1380739 : Blo 1226431 1380739 := bstep (se 1 (by rfl) ⟨1035554, by rfl⟩ : syracuseStep 1380739 = 2071109) B2071109
theorem B7459235 : Blo 1226431 7459235 := bstep (se 1 (by rfl) ⟨5594426, by rfl⟩ : syracuseStep 7459235 = 11188853) B11188853
theorem B6558115 : Blo 1226431 6558115 := bstep (se 1 (by rfl) ⟨4918586, by rfl⟩ : syracuseStep 6558115 = 9837173) B9837173
theorem B4141475 : Blo 1226431 4141475 := bstep (se 1 (by rfl) ⟨3106106, by rfl⟩ : syracuseStep 4141475 = 6212213) B6212213
theorem B6295985 : Blo 1226431 6295985 := bstep (se 2 (by rfl) ⟨2360994, by rfl⟩ : syracuseStep 6295985 = 4721989) B4721989
theorem B6214157 : Blo 1226431 6214157 := bstep (se 3 (by rfl) ⟨1165154, by rfl⟩ : syracuseStep 6214157 = 2330309) B2330309
theorem B1380883 : Blo 1226431 1380883 := bstep (se 1 (by rfl) ⟨1035662, by rfl⟩ : syracuseStep 1380883 = 2071325) B2071325
theorem B1839665 : Blo 1226431 1839665 := bstep (se 2 (by rfl) ⟨689874, by rfl⟩ : syracuseStep 1839665 = 1379749) B1379749
theorem B1659457 : Blo 1226431 1659457 := bstep (se 2 (by rfl) ⟨622296, by rfl⟩ : syracuseStep 1659457 = 1244593) B1244593
theorem B1839683 : Blo 1226431 1839683 := bstep (se 1 (by rfl) ⟨1379762, by rfl⟩ : syracuseStep 1839683 = 2759525) B2759525
theorem B1839713 : Blo 1226431 1839713 := bstep (se 2 (by rfl) ⟨689892, by rfl⟩ : syracuseStep 1839713 = 1379785) B1379785
theorem B4657763 : Blo 1226431 4657763 := bstep (se 1 (by rfl) ⟨3493322, by rfl⟩ : syracuseStep 4657763 = 6986645) B6986645
theorem B1839731 : Blo 1226431 1839731 := bstep (se 1 (by rfl) ⟨1379798, by rfl⟩ : syracuseStep 1839731 = 2759597) B2759597
theorem B1839761 : Blo 1226431 1839761 := bstep (se 2 (by rfl) ⟨689910, by rfl⟩ : syracuseStep 1839761 = 1379821) B1379821
theorem B2331281 : Blo 1226431 2331281 := bstep (se 2 (by rfl) ⟨874230, by rfl⟩ : syracuseStep 2331281 = 1748461) B1748461
theorem B1839779 : Blo 1226431 1839779 := bstep (se 1 (by rfl) ⟨1379834, by rfl⟩ : syracuseStep 1839779 = 2759669) B2759669
theorem B1381027 : Blo 1226431 1381027 := bstep (se 1 (by rfl) ⟨1035770, by rfl⟩ : syracuseStep 1381027 = 2071541) B2071541
theorem B4141745 : Blo 1226431 4141745 := bstep (se 2 (by rfl) ⟨1553154, by rfl⟩ : syracuseStep 4141745 = 3106309) B3106309
theorem B1839809 : Blo 1226431 1839809 := bstep (se 2 (by rfl) ⟨689928, by rfl⟩ : syracuseStep 1839809 = 1379857) B1379857
theorem B8852165 : Blo 1226431 8852165 := bstep (se 4 (by rfl) ⟨829890, by rfl⟩ : syracuseStep 8852165 = 1659781) B1659781
theorem B1839827 : Blo 1226431 1839827 := bstep (se 1 (by rfl) ⟨1379870, by rfl⟩ : syracuseStep 1839827 = 2759741) B2759741
theorem B1839857 : Blo 1226431 1839857 := bstep (se 2 (by rfl) ⟨689946, by rfl⟩ : syracuseStep 1839857 = 1379893) B1379893
theorem B1839875 : Blo 1226431 1839875 := bstep (se 1 (by rfl) ⟨1379906, by rfl⟩ : syracuseStep 1839875 = 2759813) B2759813
theorem B1839905 : Blo 1226431 1839905 := bstep (se 2 (by rfl) ⟨689964, by rfl⟩ : syracuseStep 1839905 = 1379929) B1379929
theorem B1839923 : Blo 1226431 1839923 := bstep (se 1 (by rfl) ⟨1379942, by rfl⟩ : syracuseStep 1839923 = 2759885) B2759885
theorem B1381171 : Blo 1226431 1381171 := bstep (se 1 (by rfl) ⟨1035878, by rfl⟩ : syracuseStep 1381171 = 2071757) B2071757
theorem B1839953 : Blo 1226431 1839953 := bstep (se 2 (by rfl) ⟨689982, by rfl⟩ : syracuseStep 1839953 = 1379965) B1379965
theorem B1839971 : Blo 1226431 1839971 := bstep (se 1 (by rfl) ⟨1379978, by rfl⟩ : syracuseStep 1839971 = 2759957) B2759957
theorem B2798435 : Blo 1226431 2798435 := bstep (se 1 (by rfl) ⟨2098826, by rfl⟩ : syracuseStep 2798435 = 4197653) B4197653
theorem B1553251 : Blo 1226431 1553251 := bstep (se 1 (by rfl) ⟨1164938, by rfl⟩ : syracuseStep 1553251 = 2329877) B2329877
theorem B4256621 : Blo 1226431 4256621 := bstep (se 3 (by rfl) ⟨798116, by rfl⟩ : syracuseStep 4256621 = 1596233) B1596233
theorem B1840001 : Blo 1226431 1840001 := bstep (se 2 (by rfl) ⟨690000, by rfl⟩ : syracuseStep 1840001 = 1380001) B1380001
theorem B3888017 : Blo 1226431 3888017 := bstep (se 2 (by rfl) ⟨1458006, by rfl⟩ : syracuseStep 3888017 = 2916013) B2916013
theorem B1840019 : Blo 1226431 1840019 := bstep (se 1 (by rfl) ⟨1380014, by rfl⟩ : syracuseStep 1840019 = 2760029) B2760029
theorem B1840049 : Blo 1226431 1840049 := bstep (se 2 (by rfl) ⟨690018, by rfl⟩ : syracuseStep 1840049 = 1380037) B1380037
theorem B1840067 : Blo 1226431 1840067 := bstep (se 1 (by rfl) ⟨1380050, by rfl⟩ : syracuseStep 1840067 = 2760101) B2760101
theorem B1553347 : Blo 1226431 1553347 := bstep (se 1 (by rfl) ⟨1165010, by rfl⟩ : syracuseStep 1553347 = 2330021) B2330021
theorem B1381315 : Blo 1226431 1381315 := bstep (se 1 (by rfl) ⟨1035986, by rfl⟩ : syracuseStep 1381315 = 2071973) B2071973
theorem B5313485 : Blo 1226431 5313485 := bstep (se 3 (by rfl) ⟨996278, by rfl⟩ : syracuseStep 5313485 = 1992557) B1992557
theorem B1840097 : Blo 1226431 1840097 := bstep (se 2 (by rfl) ⟨690036, by rfl⟩ : syracuseStep 1840097 = 1380073) B1380073
theorem B1659889 : Blo 1226431 1659889 := bstep (se 2 (by rfl) ⟨622458, by rfl⟩ : syracuseStep 1659889 = 1244917) B1244917
theorem B1840115 : Blo 1226431 1840115 := bstep (se 1 (by rfl) ⟨1380086, by rfl⟩ : syracuseStep 1840115 = 2760173) B2760173
theorem B1840145 : Blo 1226431 1840145 := bstep (se 2 (by rfl) ⟨690054, by rfl⟩ : syracuseStep 1840145 = 1380109) B1380109
theorem B1840163 : Blo 1226431 1840163 := bstep (se 1 (by rfl) ⟨1380122, by rfl⟩ : syracuseStep 1840163 = 2760245) B2760245
theorem B1840193 : Blo 1226431 1840193 := bstep (se 2 (by rfl) ⟨690072, by rfl⟩ : syracuseStep 1840193 = 1380145) B1380145
theorem B4199501 : Blo 1226431 4199501 := bstep (se 3 (by rfl) ⟨787406, by rfl⟩ : syracuseStep 4199501 = 1574813) B1574813
theorem B1840211 : Blo 1226431 1840211 := bstep (se 1 (by rfl) ⟨1380158, by rfl⟩ : syracuseStep 1840211 = 2760317) B2760317
theorem B1381459 : Blo 1226431 1381459 := bstep (se 1 (by rfl) ⟨1036094, by rfl⟩ : syracuseStep 1381459 = 2072189) B2072189
theorem B2069617 : Blo 1226431 2069617 := bstep (se 2 (by rfl) ⟨776106, by rfl⟩ : syracuseStep 2069617 = 1552213) B1552213
theorem B1840241 : Blo 1226431 1840241 := bstep (se 2 (by rfl) ⟨690090, by rfl⟩ : syracuseStep 1840241 = 1380181) B1380181
theorem B1840259 : Blo 1226431 1840259 := bstep (se 1 (by rfl) ⟨1380194, by rfl⟩ : syracuseStep 1840259 = 2760389) B2760389
theorem B2069651 : Blo 1226431 2069651 := bstep (se 1 (by rfl) ⟨1552238, by rfl⟩ : syracuseStep 2069651 = 3104477) B3104477
theorem B1840289 : Blo 1226431 1840289 := bstep (se 2 (by rfl) ⟨690108, by rfl⟩ : syracuseStep 1840289 = 1380217) B1380217
theorem B3495089 : Blo 1226431 3495089 := bstep (se 2 (by rfl) ⟨1310658, by rfl⟩ : syracuseStep 3495089 = 2621317) B2621317
theorem B1840307 : Blo 1226431 1840307 := bstep (se 1 (by rfl) ⟨1380230, by rfl⟩ : syracuseStep 1840307 = 2760461) B2760461
theorem B2487491 : Blo 1226431 2487491 := bstep (se 1 (by rfl) ⟨1865618, by rfl⟩ : syracuseStep 2487491 = 3731237) B3731237
theorem B4142285 : Blo 1226431 4142285 := bstep (se 3 (by rfl) ⟨776678, by rfl⟩ : syracuseStep 4142285 = 1553357) B1553357
theorem B1840337 : Blo 1226431 1840337 := bstep (se 2 (by rfl) ⟨690126, by rfl⟩ : syracuseStep 1840337 = 1380253) B1380253
theorem B1840355 : Blo 1226431 1840355 := bstep (se 1 (by rfl) ⟨1380266, by rfl⟩ : syracuseStep 1840355 = 2760533) B2760533
theorem B1381603 : Blo 1226431 1381603 := bstep (se 1 (by rfl) ⟨1036202, by rfl⟩ : syracuseStep 1381603 = 2072405) B2072405
theorem B4658417 : Blo 1226431 4658417 := bstep (se 2 (by rfl) ⟨1746906, by rfl⟩ : syracuseStep 4658417 = 3493813) B3493813
theorem B1840385 : Blo 1226431 1840385 := bstep (se 2 (by rfl) ⟨690144, by rfl⟩ : syracuseStep 1840385 = 1380289) B1380289
theorem B4142339 : Blo 1226431 4142339 := bstep (se 1 (by rfl) ⟨3106754, by rfl⟩ : syracuseStep 4142339 = 6213509) B6213509
theorem B2069779 : Blo 1226431 2069779 := bstep (se 1 (by rfl) ⟨1552334, by rfl⟩ : syracuseStep 2069779 = 3104669) B3104669
theorem B1840403 : Blo 1226431 1840403 := bstep (se 1 (by rfl) ⟨1380302, by rfl⟩ : syracuseStep 1840403 = 2760605) B2760605
theorem B1840433 : Blo 1226431 1840433 := bstep (se 2 (by rfl) ⟨690162, by rfl⟩ : syracuseStep 1840433 = 1380325) B1380325
theorem B3028291 : Blo 1226431 3028291 := bstep (se 1 (by rfl) ⟨2271218, by rfl⟩ : syracuseStep 3028291 = 4542437) B4542437
theorem B1840451 : Blo 1226431 1840451 := bstep (se 1 (by rfl) ⟨1380338, by rfl⟩ : syracuseStep 1840451 = 2760677) B2760677
theorem B1840481 : Blo 1226431 1840481 := bstep (se 2 (by rfl) ⟨690180, by rfl⟩ : syracuseStep 1840481 = 1380361) B1380361
theorem B2332003 : Blo 1226431 2332003 := bstep (se 1 (by rfl) ⟨1749002, by rfl⟩ : syracuseStep 2332003 = 3498005) B3498005
theorem B1840499 : Blo 1226431 1840499 := bstep (se 1 (by rfl) ⟨1380374, by rfl⟩ : syracuseStep 1840499 = 2760749) B2760749
theorem B1381747 : Blo 1226431 1381747 := bstep (se 1 (by rfl) ⟨1036310, by rfl⟩ : syracuseStep 1381747 = 2072621) B2072621
theorem B1840529 : Blo 1226431 1840529 := bstep (se 2 (by rfl) ⟨690198, by rfl⟩ : syracuseStep 1840529 = 1380397) B1380397
theorem B2069921 : Blo 1226431 2069921 := bstep (se 2 (by rfl) ⟨776220, by rfl⟩ : syracuseStep 2069921 = 1552441) B1552441
theorem B3315107 : Blo 1226431 3315107 := bstep (se 1 (by rfl) ⟨2486330, by rfl⟩ : syracuseStep 3315107 = 4972661) B4972661
theorem B1840547 : Blo 1226431 1840547 := bstep (se 1 (by rfl) ⟨1380410, by rfl⟩ : syracuseStep 1840547 = 2760821) B2760821
theorem B1553843 : Blo 1226431 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B1840577 : Blo 1226431 1840577 := bstep (se 2 (by rfl) ⟨690216, by rfl⟩ : syracuseStep 1840577 = 1380433) B1380433
theorem B1840595 : Blo 1226431 1840595 := bstep (se 1 (by rfl) ⟨1380446, by rfl⟩ : syracuseStep 1840595 = 2760893) B2760893
theorem B6985187 : Blo 1226431 6985187 := bstep (se 1 (by rfl) ⟨5238890, by rfl⟩ : syracuseStep 6985187 = 10477781) B10477781
theorem B1840625 : Blo 1226431 1840625 := bstep (se 2 (by rfl) ⟨690234, by rfl⟩ : syracuseStep 1840625 = 1380469) B1380469
theorem B1840643 : Blo 1226431 1840643 := bstep (se 1 (by rfl) ⟨1380482, by rfl⟩ : syracuseStep 1840643 = 2760965) B2760965
theorem B1381891 : Blo 1226431 1381891 := bstep (se 1 (by rfl) ⟨1036418, by rfl⟩ : syracuseStep 1381891 = 2072837) B2072837
theorem B11949581 : Blo 1226431 11949581 := bstep (se 3 (by rfl) ⟨2240546, by rfl⟩ : syracuseStep 11949581 = 4481093) B4481093
theorem B4142609 : Blo 1226431 4142609 := bstep (se 2 (by rfl) ⟨1553478, by rfl⟩ : syracuseStep 4142609 = 3106957) B3106957
theorem B13276685 : Blo 1226431 13276685 := bstep (se 3 (by rfl) ⟨2489378, by rfl⟩ : syracuseStep 13276685 = 4978757) B4978757
theorem B2070049 : Blo 1226431 2070049 := bstep (se 2 (by rfl) ⟨776268, by rfl⟩ : syracuseStep 2070049 = 1552537) B1552537
theorem B1840673 : Blo 1226431 1840673 := bstep (se 2 (by rfl) ⟨690252, by rfl⟩ : syracuseStep 1840673 = 1380505) B1380505
theorem B1840691 : Blo 1226431 1840691 := bstep (se 1 (by rfl) ⟨1380518, by rfl⟩ : syracuseStep 1840691 = 2761037) B2761037
theorem B2070083 : Blo 1226431 2070083 := bstep (se 1 (by rfl) ⟨1552562, by rfl⟩ : syracuseStep 2070083 = 3105125) B3105125
theorem B1840721 : Blo 1226431 1840721 := bstep (se 2 (by rfl) ⟨690270, by rfl⟩ : syracuseStep 1840721 = 1380541) B1380541
theorem B1840739 : Blo 1226431 1840739 := bstep (se 1 (by rfl) ⟨1380554, by rfl⟩ : syracuseStep 1840739 = 2761109) B2761109
theorem B1840769 : Blo 1226431 1840769 := bstep (se 2 (by rfl) ⟨690288, by rfl⟩ : syracuseStep 1840769 = 1380577) B1380577
theorem B1840787 : Blo 1226431 1840787 := bstep (se 1 (by rfl) ⟨1380590, by rfl⟩ : syracuseStep 1840787 = 2761181) B2761181
theorem B5240497 : Blo 1226431 5240497 := bstep (se 2 (by rfl) ⟨1965186, by rfl⟩ : syracuseStep 5240497 = 3930373) B3930373
theorem B1840817 : Blo 1226431 1840817 := bstep (se 2 (by rfl) ⟨690306, by rfl⟩ : syracuseStep 1840817 = 1380613) B1380613
theorem B1226435 : Blo 1226431 1226435 := bstep (se 1 (by rfl) ⟨919826, by rfl⟩ : syracuseStep 1226435 = 1839653) B1839653
theorem B2070211 : Blo 1226431 2070211 := bstep (se 1 (by rfl) ⟨1552658, by rfl⟩ : syracuseStep 2070211 = 3105317) B3105317
theorem B1840835 : Blo 1226431 1840835 := bstep (se 1 (by rfl) ⟨1380626, by rfl⟩ : syracuseStep 1840835 = 2761253) B2761253
theorem B1226451 : Blo 1226431 1226451 := bstep (se 1 (by rfl) ⟨919838, by rfl⟩ : syracuseStep 1226451 = 1839677) B1839677
theorem B1840865 : Blo 1226431 1840865 := bstep (se 2 (by rfl) ⟨690324, by rfl⟩ : syracuseStep 1840865 = 1380649) B1380649
theorem B1226467 : Blo 1226431 1226467 := bstep (se 1 (by rfl) ⟨919850, by rfl⟩ : syracuseStep 1226467 = 1839701) B1839701
theorem B1226483 : Blo 1226431 1226483 := bstep (se 1 (by rfl) ⟨919862, by rfl⟩ : syracuseStep 1226483 = 1839725) B1839725
theorem B1840883 : Blo 1226431 1840883 := bstep (se 1 (by rfl) ⟨1380662, by rfl⟩ : syracuseStep 1840883 = 2761325) B2761325
theorem B1226499 : Blo 1226431 1226499 := bstep (se 1 (by rfl) ⟨919874, by rfl⟩ : syracuseStep 1226499 = 1839749) B1839749
theorem B1840913 : Blo 1226431 1840913 := bstep (se 2 (by rfl) ⟨690342, by rfl⟩ : syracuseStep 1840913 = 1380685) B1380685
theorem B1226515 : Blo 1226431 1226515 := bstep (se 1 (by rfl) ⟨919886, by rfl⟩ : syracuseStep 1226515 = 1839773) B1839773
theorem B1226531 : Blo 1226431 1226531 := bstep (se 1 (by rfl) ⟨919898, by rfl⟩ : syracuseStep 1226531 = 1839797) B1839797
theorem B4421411 : Blo 1226431 4421411 := bstep (se 1 (by rfl) ⟨3316058, by rfl⟩ : syracuseStep 4421411 = 6632117) B6632117
theorem B1840931 : Blo 1226431 1840931 := bstep (se 1 (by rfl) ⟨1380698, by rfl⟩ : syracuseStep 1840931 = 2761397) B2761397
theorem B1226547 : Blo 1226431 1226547 := bstep (se 1 (by rfl) ⟨919910, by rfl⟩ : syracuseStep 1226547 = 1839821) B1839821
theorem B1840961 : Blo 1226431 1840961 := bstep (se 2 (by rfl) ⟨690360, by rfl⟩ : syracuseStep 1840961 = 1380721) B1380721
theorem B1226563 : Blo 1226431 1226563 := bstep (se 1 (by rfl) ⟨919922, by rfl⟩ : syracuseStep 1226563 = 1839845) B1839845
theorem B2070353 : Blo 1226431 2070353 := bstep (se 2 (by rfl) ⟨776382, by rfl⟩ : syracuseStep 2070353 = 1552765) B1552765
theorem B3495761 : Blo 1226431 3495761 := bstep (se 2 (by rfl) ⟨1310910, by rfl⟩ : syracuseStep 3495761 = 2621821) B2621821
theorem B1226579 : Blo 1226431 1226579 := bstep (se 1 (by rfl) ⟨919934, by rfl⟩ : syracuseStep 1226579 = 1839869) B1839869
theorem B1840979 : Blo 1226431 1840979 := bstep (se 1 (by rfl) ⟨1380734, by rfl⟩ : syracuseStep 1840979 = 2761469) B2761469
theorem B1226595 : Blo 1226431 1226595 := bstep (se 1 (by rfl) ⟨919946, by rfl⟩ : syracuseStep 1226595 = 1839893) B1839893
theorem B4978531 : Blo 1226431 4978531 := bstep (se 1 (by rfl) ⟨3733898, by rfl⟩ : syracuseStep 4978531 = 7467797) B7467797
theorem B7862129 : Blo 1226431 7862129 := bstep (se 2 (by rfl) ⟨2948298, by rfl⟩ : syracuseStep 7862129 = 5896597) B5896597
theorem B1841009 : Blo 1226431 1841009 := bstep (se 2 (by rfl) ⟨690378, by rfl⟩ : syracuseStep 1841009 = 1380757) B1380757
theorem B1226611 : Blo 1226431 1226611 := bstep (se 1 (by rfl) ⟨919958, by rfl⟩ : syracuseStep 1226611 = 1839917) B1839917
theorem B1226627 : Blo 1226431 1226627 := bstep (se 1 (by rfl) ⟨919970, by rfl⟩ : syracuseStep 1226627 = 1839941) B1839941
theorem B1841027 : Blo 1226431 1841027 := bstep (se 1 (by rfl) ⟨1380770, by rfl⟩ : syracuseStep 1841027 = 2761541) B2761541
theorem B1226643 : Blo 1226431 1226643 := bstep (se 1 (by rfl) ⟨919982, by rfl⟩ : syracuseStep 1226643 = 1839965) B1839965
theorem B1841057 : Blo 1226431 1841057 := bstep (se 2 (by rfl) ⟨690396, by rfl⟩ : syracuseStep 1841057 = 1380793) B1380793
theorem B1226659 : Blo 1226431 1226659 := bstep (se 1 (by rfl) ⟨919994, by rfl⟩ : syracuseStep 1226659 = 1839989) B1839989
theorem B3930029 : Blo 1226431 3930029 := bstep (se 3 (by rfl) ⟨736880, by rfl⟩ : syracuseStep 3930029 = 1473761) B1473761
theorem B1226675 : Blo 1226431 1226675 := bstep (se 1 (by rfl) ⟨920006, by rfl⟩ : syracuseStep 1226675 = 1840013) B1840013
theorem B1841075 : Blo 1226431 1841075 := bstep (se 1 (by rfl) ⟨1380806, by rfl⟩ : syracuseStep 1841075 = 2761613) B2761613
theorem B1226691 : Blo 1226431 1226691 := bstep (se 1 (by rfl) ⟨920018, by rfl⟩ : syracuseStep 1226691 = 1840037) B1840037
theorem B2070481 : Blo 1226431 2070481 := bstep (se 2 (by rfl) ⟨776430, by rfl⟩ : syracuseStep 2070481 = 1552861) B1552861
theorem B1841105 : Blo 1226431 1841105 := bstep (se 2 (by rfl) ⟨690414, by rfl⟩ : syracuseStep 1841105 = 1380829) B1380829
theorem B1226707 : Blo 1226431 1226707 := bstep (se 1 (by rfl) ⟨920030, by rfl⟩ : syracuseStep 1226707 = 1840061) B1840061
theorem B1226723 : Blo 1226431 1226723 := bstep (se 1 (by rfl) ⟨920042, by rfl⟩ : syracuseStep 1226723 = 1840085) B1840085
theorem B1841123 : Blo 1226431 1841123 := bstep (se 1 (by rfl) ⟨1380842, by rfl⟩ : syracuseStep 1841123 = 2761685) B2761685
theorem B1226739 : Blo 1226431 1226739 := bstep (se 1 (by rfl) ⟨920054, by rfl⟩ : syracuseStep 1226739 = 1840109) B1840109
theorem B2070515 : Blo 1226431 2070515 := bstep (se 1 (by rfl) ⟨1552886, by rfl⟩ : syracuseStep 2070515 = 3105773) B3105773
theorem B1841153 : Blo 1226431 1841153 := bstep (se 2 (by rfl) ⟨690432, by rfl⟩ : syracuseStep 1841153 = 1380865) B1380865
theorem B1226755 : Blo 1226431 1226755 := bstep (se 1 (by rfl) ⟨920066, by rfl⟩ : syracuseStep 1226755 = 1840133) B1840133
theorem B1226771 : Blo 1226431 1226771 := bstep (se 1 (by rfl) ⟨920078, by rfl⟩ : syracuseStep 1226771 = 1840157) B1840157
theorem B1841171 : Blo 1226431 1841171 := bstep (se 1 (by rfl) ⟨1380878, by rfl⟩ : syracuseStep 1841171 = 2761757) B2761757
theorem B1226787 : Blo 1226431 1226787 := bstep (se 1 (by rfl) ⟨920090, by rfl⟩ : syracuseStep 1226787 = 1840181) B1840181
theorem B4143149 : Blo 1226431 4143149 := bstep (se 3 (by rfl) ⟨776840, by rfl⟩ : syracuseStep 4143149 = 1553681) B1553681
theorem B1841201 : Blo 1226431 1841201 := bstep (se 2 (by rfl) ⟨690450, by rfl⟩ : syracuseStep 1841201 = 1380901) B1380901
theorem B1226803 : Blo 1226431 1226803 := bstep (se 1 (by rfl) ⟨920102, by rfl⟩ : syracuseStep 1226803 = 1840205) B1840205
theorem B1226819 : Blo 1226431 1226819 := bstep (se 1 (by rfl) ⟨920114, by rfl⟩ : syracuseStep 1226819 = 1840229) B1840229
theorem B1841219 : Blo 1226431 1841219 := bstep (se 1 (by rfl) ⟨1380914, by rfl⟩ : syracuseStep 1841219 = 2761829) B2761829
theorem B1226835 : Blo 1226431 1226835 := bstep (se 1 (by rfl) ⟨920126, by rfl⟩ : syracuseStep 1226835 = 1840253) B1840253
theorem B1841249 : Blo 1226431 1841249 := bstep (se 2 (by rfl) ⟨690468, by rfl⟩ : syracuseStep 1841249 = 1380937) B1380937
theorem B1226851 : Blo 1226431 1226851 := bstep (se 1 (by rfl) ⟨920138, by rfl⟩ : syracuseStep 1226851 = 1840277) B1840277
theorem B4143203 : Blo 1226431 4143203 := bstep (se 1 (by rfl) ⟨3107402, by rfl⟩ : syracuseStep 4143203 = 6214805) B6214805
theorem B10623089 : Blo 1226431 10623089 := bstep (se 2 (by rfl) ⟨3983658, by rfl⟩ : syracuseStep 10623089 = 7967317) B7967317
theorem B1226867 : Blo 1226431 1226867 := bstep (se 1 (by rfl) ⟨920150, by rfl⟩ : syracuseStep 1226867 = 1840301) B1840301
theorem B2070643 : Blo 1226431 2070643 := bstep (se 1 (by rfl) ⟨1552982, by rfl⟩ : syracuseStep 2070643 = 3105965) B3105965
theorem B1841267 : Blo 1226431 1841267 := bstep (se 1 (by rfl) ⟨1380950, by rfl⟩ : syracuseStep 1841267 = 2761901) B2761901
theorem B1554547 : Blo 1226431 1554547 := bstep (se 1 (by rfl) ⟨1165910, by rfl⟩ : syracuseStep 1554547 = 2331821) B2331821
theorem B1226883 : Blo 1226431 1226883 := bstep (se 1 (by rfl) ⟨920162, by rfl⟩ : syracuseStep 1226883 = 1840325) B1840325
theorem B1841297 : Blo 1226431 1841297 := bstep (se 2 (by rfl) ⟨690486, by rfl⟩ : syracuseStep 1841297 = 1380973) B1380973
theorem B1226899 : Blo 1226431 1226899 := bstep (se 1 (by rfl) ⟨920174, by rfl⟩ : syracuseStep 1226899 = 1840349) B1840349
theorem B1226915 : Blo 1226431 1226915 := bstep (se 1 (by rfl) ⟨920186, by rfl⟩ : syracuseStep 1226915 = 1840373) B1840373
theorem B1841315 : Blo 1226431 1841315 := bstep (se 1 (by rfl) ⟨1380986, by rfl⟩ : syracuseStep 1841315 = 2761973) B2761973
theorem B1226931 : Blo 1226431 1226931 := bstep (se 1 (by rfl) ⟨920198, by rfl⟩ : syracuseStep 1226931 = 1840397) B1840397
theorem B1841345 : Blo 1226431 1841345 := bstep (se 2 (by rfl) ⟨690504, by rfl⟩ : syracuseStep 1841345 = 1381009) B1381009
theorem B1226947 : Blo 1226431 1226947 := bstep (se 1 (by rfl) ⟨920210, by rfl⟩ : syracuseStep 1226947 = 1840421) B1840421
theorem B2488529 : Blo 1226431 2488529 := bstep (se 2 (by rfl) ⟨933198, by rfl⟩ : syracuseStep 2488529 = 1866397) B1866397
theorem B1226963 : Blo 1226431 1226963 := bstep (se 1 (by rfl) ⟨920222, by rfl⟩ : syracuseStep 1226963 = 1840445) B1840445
theorem B1841363 : Blo 1226431 1841363 := bstep (se 1 (by rfl) ⟨1381022, by rfl⟩ : syracuseStep 1841363 = 2762045) B2762045
theorem B1554643 : Blo 1226431 1554643 := bstep (se 1 (by rfl) ⟨1165982, by rfl⟩ : syracuseStep 1554643 = 2331965) B2331965
theorem B1226979 : Blo 1226431 1226979 := bstep (se 1 (by rfl) ⟨920234, by rfl⟩ : syracuseStep 1226979 = 1840469) B1840469
theorem B1841393 : Blo 1226431 1841393 := bstep (se 2 (by rfl) ⟨690522, by rfl⟩ : syracuseStep 1841393 = 1381045) B1381045
theorem B1226995 : Blo 1226431 1226995 := bstep (se 1 (by rfl) ⟨920246, by rfl⟩ : syracuseStep 1226995 = 1840493) B1840493
theorem B2070785 : Blo 1226431 2070785 := bstep (se 2 (by rfl) ⟨776544, by rfl⟩ : syracuseStep 2070785 = 1553089) B1553089
theorem B1227011 : Blo 1226431 1227011 := bstep (se 1 (by rfl) ⟨920258, by rfl⟩ : syracuseStep 1227011 = 1840517) B1840517
theorem B1841411 : Blo 1226431 1841411 := bstep (se 1 (by rfl) ⟨1381058, by rfl⟩ : syracuseStep 1841411 = 2762117) B2762117
theorem B1227027 : Blo 1226431 1227027 := bstep (se 1 (by rfl) ⟨920270, by rfl⟩ : syracuseStep 1227027 = 1840541) B1840541
theorem B1841441 : Blo 1226431 1841441 := bstep (se 2 (by rfl) ⟨690540, by rfl⟩ : syracuseStep 1841441 = 1381081) B1381081
theorem B1227043 : Blo 1226431 1227043 := bstep (se 1 (by rfl) ⟨920282, by rfl⟩ : syracuseStep 1227043 = 1840565) B1840565
theorem B1227059 : Blo 1226431 1227059 := bstep (se 1 (by rfl) ⟨920294, by rfl⟩ : syracuseStep 1227059 = 1840589) B1840589
theorem B1841459 : Blo 1226431 1841459 := bstep (se 1 (by rfl) ⟨1381094, by rfl⟩ : syracuseStep 1841459 = 2762189) B2762189
theorem B1227075 : Blo 1226431 1227075 := bstep (se 1 (by rfl) ⟨920306, by rfl⟩ : syracuseStep 1227075 = 1840613) B1840613
theorem B3316049 : Blo 1226431 3316049 := bstep (se 2 (by rfl) ⟨1243518, by rfl⟩ : syracuseStep 3316049 = 2487037) B2487037
theorem B3930449 : Blo 1226431 3930449 := bstep (se 2 (by rfl) ⟨1473918, by rfl⟩ : syracuseStep 3930449 = 2947837) B2947837
theorem B1227091 : Blo 1226431 1227091 := bstep (se 1 (by rfl) ⟨920318, by rfl⟩ : syracuseStep 1227091 = 1840637) B1840637
theorem B1841489 : Blo 1226431 1841489 := bstep (se 2 (by rfl) ⟨690558, by rfl⟩ : syracuseStep 1841489 = 1381117) B1381117
theorem B1227107 : Blo 1226431 1227107 := bstep (se 1 (by rfl) ⟨920330, by rfl⟩ : syracuseStep 1227107 = 1840661) B1840661
theorem B1841507 : Blo 1226431 1841507 := bstep (se 1 (by rfl) ⟨1381130, by rfl⟩ : syracuseStep 1841507 = 2762261) B2762261
theorem B7461233 : Blo 1226431 7461233 := bstep (se 2 (by rfl) ⟨2797962, by rfl⟩ : syracuseStep 7461233 = 5595925) B5595925
theorem B4143473 : Blo 1226431 4143473 := bstep (se 2 (by rfl) ⟨1553802, by rfl⟩ : syracuseStep 4143473 = 3107605) B3107605
theorem B1227123 : Blo 1226431 1227123 := bstep (se 1 (by rfl) ⟨920342, by rfl⟩ : syracuseStep 1227123 = 1840685) B1840685
theorem B4200817 : Blo 1226431 4200817 := bstep (se 2 (by rfl) ⟨1575306, by rfl⟩ : syracuseStep 4200817 = 3150613) B3150613
theorem B2070913 : Blo 1226431 2070913 := bstep (se 2 (by rfl) ⟨776592, by rfl⟩ : syracuseStep 2070913 = 1553185) B1553185
theorem B1841537 : Blo 1226431 1841537 := bstep (se 2 (by rfl) ⟨690576, by rfl⟩ : syracuseStep 1841537 = 1381153) B1381153
theorem B1227139 : Blo 1226431 1227139 := bstep (se 1 (by rfl) ⟨920354, by rfl⟩ : syracuseStep 1227139 = 1840709) B1840709
theorem B1227155 : Blo 1226431 1227155 := bstep (se 1 (by rfl) ⟨920366, by rfl⟩ : syracuseStep 1227155 = 1840733) B1840733
theorem B1841555 : Blo 1226431 1841555 := bstep (se 1 (by rfl) ⟨1381166, by rfl⟩ : syracuseStep 1841555 = 2762333) B2762333
theorem B1227171 : Blo 1226431 1227171 := bstep (se 1 (by rfl) ⟨920378, by rfl⟩ : syracuseStep 1227171 = 1840757) B1840757
theorem B2070947 : Blo 1226431 2070947 := bstep (se 1 (by rfl) ⟨1553210, by rfl⟩ : syracuseStep 2070947 = 3106421) B3106421
theorem B1841585 : Blo 1226431 1841585 := bstep (se 2 (by rfl) ⟨690594, by rfl⟩ : syracuseStep 1841585 = 1381189) B1381189
theorem B1227187 : Blo 1226431 1227187 := bstep (se 1 (by rfl) ⟨920390, by rfl⟩ : syracuseStep 1227187 = 1840781) B1840781
theorem B1227203 : Blo 1226431 1227203 := bstep (se 1 (by rfl) ⟨920402, by rfl⟩ : syracuseStep 1227203 = 1840805) B1840805
theorem B1841603 : Blo 1226431 1841603 := bstep (se 1 (by rfl) ⟨1381202, by rfl⟩ : syracuseStep 1841603 = 2762405) B2762405
theorem B6986189 : Blo 1226431 6986189 := bstep (se 3 (by rfl) ⟨1309910, by rfl⟩ : syracuseStep 6986189 = 2619821) B2619821
theorem B1243603 : Blo 1226431 1243603 := bstep (se 1 (by rfl) ⟨932702, by rfl⟩ : syracuseStep 1243603 = 1865405) B1865405
theorem B1227219 : Blo 1226431 1227219 := bstep (se 1 (by rfl) ⟨920414, by rfl⟩ : syracuseStep 1227219 = 1840829) B1840829
theorem B1841633 : Blo 1226431 1841633 := bstep (se 2 (by rfl) ⟨690612, by rfl⟩ : syracuseStep 1841633 = 1381225) B1381225
theorem B1227235 : Blo 1226431 1227235 := bstep (se 1 (by rfl) ⟨920426, by rfl⟩ : syracuseStep 1227235 = 1840853) B1840853
theorem B1227251 : Blo 1226431 1227251 := bstep (se 1 (by rfl) ⟨920438, by rfl⟩ : syracuseStep 1227251 = 1840877) B1840877
theorem B1841651 : Blo 1226431 1841651 := bstep (se 1 (by rfl) ⟨1381238, by rfl⟩ : syracuseStep 1841651 = 2762477) B2762477
theorem B1227267 : Blo 1226431 1227267 := bstep (se 1 (by rfl) ⟨920450, by rfl⟩ : syracuseStep 1227267 = 1840901) B1840901
theorem B1841681 : Blo 1226431 1841681 := bstep (se 2 (by rfl) ⟨690630, by rfl⟩ : syracuseStep 1841681 = 1381261) B1381261
theorem B1227283 : Blo 1226431 1227283 := bstep (se 1 (by rfl) ⟨920462, by rfl⟩ : syracuseStep 1227283 = 1840925) B1840925
theorem B1227299 : Blo 1226431 1227299 := bstep (se 1 (by rfl) ⟨920474, by rfl⟩ : syracuseStep 1227299 = 1840949) B1840949
theorem B2071075 : Blo 1226431 2071075 := bstep (se 1 (by rfl) ⟨1553306, by rfl⟩ : syracuseStep 2071075 = 3106613) B3106613
theorem B1841699 : Blo 1226431 1841699 := bstep (se 1 (by rfl) ⟨1381274, by rfl⟩ : syracuseStep 1841699 = 2762549) B2762549
theorem B1227315 : Blo 1226431 1227315 := bstep (se 1 (by rfl) ⟨920486, by rfl⟩ : syracuseStep 1227315 = 1840973) B1840973
theorem B1841729 : Blo 1226431 1841729 := bstep (se 2 (by rfl) ⟨690648, by rfl⟩ : syracuseStep 1841729 = 1381297) B1381297
theorem B1227331 : Blo 1226431 1227331 := bstep (se 1 (by rfl) ⟨920498, by rfl⟩ : syracuseStep 1227331 = 1840997) B1840997
theorem B1227347 : Blo 1226431 1227347 := bstep (se 1 (by rfl) ⟨920510, by rfl⟩ : syracuseStep 1227347 = 1841021) B1841021
theorem B1841747 : Blo 1226431 1841747 := bstep (se 1 (by rfl) ⟨1381310, by rfl⟩ : syracuseStep 1841747 = 2762621) B2762621
theorem B1227363 : Blo 1226431 1227363 := bstep (se 1 (by rfl) ⟨920522, by rfl⟩ : syracuseStep 1227363 = 1841045) B1841045
theorem B3496547 : Blo 1226431 3496547 := bstep (se 1 (by rfl) ⟨2622410, by rfl⟩ : syracuseStep 3496547 = 5244821) B5244821
theorem B2210417 : Blo 1226431 2210417 := bstep (se 2 (by rfl) ⟨828906, by rfl⟩ : syracuseStep 2210417 = 1657813) B1657813
theorem B1841777 : Blo 1226431 1841777 := bstep (se 2 (by rfl) ⟨690666, by rfl⟩ : syracuseStep 1841777 = 1381333) B1381333
theorem B1227379 : Blo 1226431 1227379 := bstep (se 1 (by rfl) ⟨920534, by rfl⟩ : syracuseStep 1227379 = 1841069) B1841069
theorem B1227395 : Blo 1226431 1227395 := bstep (se 1 (by rfl) ⟨920546, by rfl⟩ : syracuseStep 1227395 = 1841093) B1841093
theorem B1841795 : Blo 1226431 1841795 := bstep (se 1 (by rfl) ⟨1381346, by rfl⟩ : syracuseStep 1841795 = 2762693) B2762693
theorem B1227411 : Blo 1226431 1227411 := bstep (se 1 (by rfl) ⟨920558, by rfl⟩ : syracuseStep 1227411 = 1841117) B1841117
theorem B1841825 : Blo 1226431 1841825 := bstep (se 2 (by rfl) ⟨690684, by rfl⟩ : syracuseStep 1841825 = 1381369) B1381369
theorem B4659875 : Blo 1226431 4659875 := bstep (se 1 (by rfl) ⟨3494906, by rfl⟩ : syracuseStep 4659875 = 6989813) B6989813
theorem B1227427 : Blo 1226431 1227427 := bstep (se 1 (by rfl) ⟨920570, by rfl⟩ : syracuseStep 1227427 = 1841141) B1841141
theorem B4659889 : Blo 1226431 4659889 := bstep (se 2 (by rfl) ⟨1747458, by rfl⟩ : syracuseStep 4659889 = 3494917) B3494917
theorem B2071217 : Blo 1226431 2071217 := bstep (se 2 (by rfl) ⟨776706, by rfl⟩ : syracuseStep 2071217 = 1553413) B1553413
theorem B1227443 : Blo 1226431 1227443 := bstep (se 1 (by rfl) ⟨920582, by rfl⟩ : syracuseStep 1227443 = 1841165) B1841165
theorem B1841843 : Blo 1226431 1841843 := bstep (se 1 (by rfl) ⟨1381382, by rfl⟩ : syracuseStep 1841843 = 2762765) B2762765
theorem B1227459 : Blo 1226431 1227459 := bstep (se 1 (by rfl) ⟨920594, by rfl⟩ : syracuseStep 1227459 = 1841189) B1841189
theorem B1841873 : Blo 1226431 1841873 := bstep (se 2 (by rfl) ⟨690702, by rfl⟩ : syracuseStep 1841873 = 1381405) B1381405
theorem B1227475 : Blo 1226431 1227475 := bstep (se 1 (by rfl) ⟨920606, by rfl⟩ : syracuseStep 1227475 = 1841213) B1841213
theorem B1866451 : Blo 1226431 1866451 := bstep (se 1 (by rfl) ⟨1399838, by rfl⟩ : syracuseStep 1866451 = 2799677) B2799677
theorem B1227491 : Blo 1226431 1227491 := bstep (se 1 (by rfl) ⟨920618, by rfl⟩ : syracuseStep 1227491 = 1841237) B1841237
theorem B1841891 : Blo 1226431 1841891 := bstep (se 1 (by rfl) ⟨1381418, by rfl⟩ : syracuseStep 1841891 = 2762837) B2762837
theorem B1227507 : Blo 1226431 1227507 := bstep (se 1 (by rfl) ⟨920630, by rfl⟩ : syracuseStep 1227507 = 1841261) B1841261
theorem B1841921 : Blo 1226431 1841921 := bstep (se 2 (by rfl) ⟨690720, by rfl⟩ : syracuseStep 1841921 = 1381441) B1381441
theorem B2620163 : Blo 1226431 2620163 := bstep (se 1 (by rfl) ⟨1965122, by rfl⟩ : syracuseStep 2620163 = 3930245) B3930245
theorem B1227523 : Blo 1226431 1227523 := bstep (se 1 (by rfl) ⟨920642, by rfl⟩ : syracuseStep 1227523 = 1841285) B1841285
theorem B1227539 : Blo 1226431 1227539 := bstep (se 1 (by rfl) ⟨920654, by rfl⟩ : syracuseStep 1227539 = 1841309) B1841309
theorem B1841939 : Blo 1226431 1841939 := bstep (se 1 (by rfl) ⟨1381454, by rfl⟩ : syracuseStep 1841939 = 2762909) B2762909
theorem B1227555 : Blo 1226431 1227555 := bstep (se 1 (by rfl) ⟨920666, by rfl⟩ : syracuseStep 1227555 = 1841333) B1841333
theorem B2071345 : Blo 1226431 2071345 := bstep (se 2 (by rfl) ⟨776754, by rfl⟩ : syracuseStep 2071345 = 1553509) B1553509
theorem B1841969 : Blo 1226431 1841969 := bstep (se 2 (by rfl) ⟨690738, by rfl⟩ : syracuseStep 1841969 = 1381477) B1381477
theorem B1227571 : Blo 1226431 1227571 := bstep (se 1 (by rfl) ⟨920678, by rfl⟩ : syracuseStep 1227571 = 1841357) B1841357
theorem B1227587 : Blo 1226431 1227587 := bstep (se 1 (by rfl) ⟨920690, by rfl⟩ : syracuseStep 1227587 = 1841381) B1841381
theorem B1841987 : Blo 1226431 1841987 := bstep (se 1 (by rfl) ⟨1381490, by rfl⟩ : syracuseStep 1841987 = 2762981) B2762981
theorem B2071379 : Blo 1226431 2071379 := bstep (se 1 (by rfl) ⟨1553534, by rfl⟩ : syracuseStep 2071379 = 3107069) B3107069
theorem B1227603 : Blo 1226431 1227603 := bstep (se 1 (by rfl) ⟨920702, by rfl⟩ : syracuseStep 1227603 = 1841405) B1841405
theorem B1842017 : Blo 1226431 1842017 := bstep (se 2 (by rfl) ⟨690756, by rfl⟩ : syracuseStep 1842017 = 1381513) B1381513
theorem B1227619 : Blo 1226431 1227619 := bstep (se 1 (by rfl) ⟨920714, by rfl⟩ : syracuseStep 1227619 = 1841429) B1841429
theorem B4979569 : Blo 1226431 4979569 := bstep (se 2 (by rfl) ⟨1867338, by rfl⟩ : syracuseStep 4979569 = 3734677) B3734677
theorem B1227635 : Blo 1226431 1227635 := bstep (se 1 (by rfl) ⟨920726, by rfl⟩ : syracuseStep 1227635 = 1841453) B1841453
theorem B1842035 : Blo 1226431 1842035 := bstep (se 1 (by rfl) ⟨1381526, by rfl⟩ : syracuseStep 1842035 = 2763053) B2763053
theorem B1227651 : Blo 1226431 1227651 := bstep (se 1 (by rfl) ⟨920738, by rfl⟩ : syracuseStep 1227651 = 1841477) B1841477
theorem B4144013 : Blo 1226431 4144013 := bstep (se 3 (by rfl) ⟨777002, by rfl⟩ : syracuseStep 4144013 = 1554005) B1554005
theorem B1842065 : Blo 1226431 1842065 := bstep (se 2 (by rfl) ⟨690774, by rfl⟩ : syracuseStep 1842065 = 1381549) B1381549
theorem B1227667 : Blo 1226431 1227667 := bstep (se 1 (by rfl) ⟨920750, by rfl⟩ : syracuseStep 1227667 = 1841501) B1841501
theorem B1227683 : Blo 1226431 1227683 := bstep (se 1 (by rfl) ⟨920762, by rfl⟩ : syracuseStep 1227683 = 1841525) B1841525
theorem B1842083 : Blo 1226431 1842083 := bstep (se 1 (by rfl) ⟨1381562, by rfl⟩ : syracuseStep 1842083 = 2763125) B2763125
theorem B3496877 : Blo 1226431 3496877 := bstep (se 3 (by rfl) ⟨655664, by rfl⟩ : syracuseStep 3496877 = 1311329) B1311329
theorem B1227699 : Blo 1226431 1227699 := bstep (se 1 (by rfl) ⟨920774, by rfl⟩ : syracuseStep 1227699 = 1841549) B1841549
theorem B12598213 : Blo 1226431 12598213 := bstep (se 4 (by rfl) ⟨1181082, by rfl⟩ : syracuseStep 12598213 = 2362165) B2362165
theorem B1227715 : Blo 1226431 1227715 := bstep (se 1 (by rfl) ⟨920786, by rfl⟩ : syracuseStep 1227715 = 1841573) B1841573
theorem B4144067 : Blo 1226431 4144067 := bstep (se 1 (by rfl) ⟨3108050, by rfl⟩ : syracuseStep 4144067 = 6216101) B6216101
theorem B1842113 : Blo 1226431 1842113 := bstep (se 2 (by rfl) ⟨690792, by rfl⟩ : syracuseStep 1842113 = 1381585) B1381585
theorem B2759633 : Blo 1226431 2759633 := bstep (se 2 (by rfl) ⟨1034862, by rfl⟩ : syracuseStep 2759633 = 2069725) B2069725
theorem B2071507 : Blo 1226431 2071507 := bstep (se 1 (by rfl) ⟨1553630, by rfl⟩ : syracuseStep 2071507 = 3107261) B3107261
theorem B1227731 : Blo 1226431 1227731 := bstep (se 1 (by rfl) ⟨920798, by rfl⟩ : syracuseStep 1227731 = 1841597) B1841597
theorem B1842131 : Blo 1226431 1842131 := bstep (se 1 (by rfl) ⟨1381598, by rfl⟩ : syracuseStep 1842131 = 2763197) B2763197
theorem B2759651 : Blo 1226431 2759651 := bstep (se 1 (by rfl) ⟨2069738, by rfl⟩ : syracuseStep 2759651 = 4139477) B4139477
theorem B1227747 : Blo 1226431 1227747 := bstep (se 1 (by rfl) ⟨920810, by rfl⟩ : syracuseStep 1227747 = 1841621) B1841621
theorem B3496945 : Blo 1226431 3496945 := bstep (se 2 (by rfl) ⟨1311354, by rfl⟩ : syracuseStep 3496945 = 2622709) B2622709
theorem B1842161 : Blo 1226431 1842161 := bstep (se 2 (by rfl) ⟨690810, by rfl⟩ : syracuseStep 1842161 = 1381621) B1381621
theorem B1227763 : Blo 1226431 1227763 := bstep (se 1 (by rfl) ⟨920822, by rfl⟩ : syracuseStep 1227763 = 1841645) B1841645
theorem B1227779 : Blo 1226431 1227779 := bstep (se 1 (by rfl) ⟨920834, by rfl⟩ : syracuseStep 1227779 = 1841669) B1841669
theorem B1842179 : Blo 1226431 1842179 := bstep (se 1 (by rfl) ⟨1381634, by rfl⟩ : syracuseStep 1842179 = 2763269) B2763269
theorem B1244179 : Blo 1226431 1244179 := bstep (se 1 (by rfl) ⟨933134, by rfl⟩ : syracuseStep 1244179 = 1866269) B1866269
theorem B1227795 : Blo 1226431 1227795 := bstep (se 1 (by rfl) ⟨920846, by rfl⟩ : syracuseStep 1227795 = 1841693) B1841693
theorem B1842209 : Blo 1226431 1842209 := bstep (se 2 (by rfl) ⟨690828, by rfl⟩ : syracuseStep 1842209 = 1381657) B1381657
theorem B1227811 : Blo 1226431 1227811 := bstep (se 1 (by rfl) ⟨920858, by rfl⟩ : syracuseStep 1227811 = 1841717) B1841717
theorem B1227827 : Blo 1226431 1227827 := bstep (se 1 (by rfl) ⟨920870, by rfl⟩ : syracuseStep 1227827 = 1841741) B1841741
theorem B1842227 : Blo 1226431 1842227 := bstep (se 1 (by rfl) ⟨1381670, by rfl⟩ : syracuseStep 1842227 = 2763341) B2763341
theorem B1227843 : Blo 1226431 1227843 := bstep (se 1 (by rfl) ⟨920882, by rfl⟩ : syracuseStep 1227843 = 1841765) B1841765
theorem B1842257 : Blo 1226431 1842257 := bstep (se 2 (by rfl) ⟨690846, by rfl⟩ : syracuseStep 1842257 = 1381693) B1381693
theorem B1227859 : Blo 1226431 1227859 := bstep (se 1 (by rfl) ⟨920894, by rfl⟩ : syracuseStep 1227859 = 1841789) B1841789
theorem B2071649 : Blo 1226431 2071649 := bstep (se 2 (by rfl) ⟨776868, by rfl⟩ : syracuseStep 2071649 = 1553737) B1553737
theorem B1227875 : Blo 1226431 1227875 := bstep (se 1 (by rfl) ⟨920906, by rfl⟩ : syracuseStep 1227875 = 1841813) B1841813
theorem B1842275 : Blo 1226431 1842275 := bstep (se 1 (by rfl) ⟨1381706, by rfl⟩ : syracuseStep 1842275 = 2763413) B2763413
theorem B1227891 : Blo 1226431 1227891 := bstep (se 1 (by rfl) ⟨920918, by rfl⟩ : syracuseStep 1227891 = 1841837) B1841837
theorem B1842305 : Blo 1226431 1842305 := bstep (se 2 (by rfl) ⟨690864, by rfl⟩ : syracuseStep 1842305 = 1381729) B1381729
theorem B1227907 : Blo 1226431 1227907 := bstep (se 1 (by rfl) ⟨920930, by rfl⟩ : syracuseStep 1227907 = 1841861) B1841861
theorem B1227923 : Blo 1226431 1227923 := bstep (se 1 (by rfl) ⟨920942, by rfl⟩ : syracuseStep 1227923 = 1841885) B1841885
theorem B1842323 : Blo 1226431 1842323 := bstep (se 1 (by rfl) ⟨1381742, by rfl⟩ : syracuseStep 1842323 = 2763485) B2763485
theorem B1227939 : Blo 1226431 1227939 := bstep (se 1 (by rfl) ⟨920954, by rfl⟩ : syracuseStep 1227939 = 1841909) B1841909
theorem B1842353 : Blo 1226431 1842353 := bstep (se 2 (by rfl) ⟨690882, by rfl⟩ : syracuseStep 1842353 = 1381765) B1381765
theorem B1227955 : Blo 1226431 1227955 := bstep (se 1 (by rfl) ⟨920966, by rfl⟩ : syracuseStep 1227955 = 1841933) B1841933
theorem B16792757 : Blo 1226431 16792757 := bstep (se 5 (by rfl) ⟨787160, by rfl⟩ : syracuseStep 16792757 = 1574321) B1574321
theorem B1227971 : Blo 1226431 1227971 := bstep (se 1 (by rfl) ⟨920978, by rfl⟩ : syracuseStep 1227971 = 1841957) B1841957
theorem B1842371 : Blo 1226431 1842371 := bstep (se 1 (by rfl) ⟨1381778, by rfl⟩ : syracuseStep 1842371 = 2763557) B2763557
theorem B3316945 : Blo 1226431 3316945 := bstep (se 2 (by rfl) ⟨1243854, by rfl⟩ : syracuseStep 3316945 = 2487709) B2487709
theorem B4144337 : Blo 1226431 4144337 := bstep (se 2 (by rfl) ⟨1554126, by rfl⟩ : syracuseStep 4144337 = 3108253) B3108253
theorem B1227987 : Blo 1226431 1227987 := bstep (se 1 (by rfl) ⟨920990, by rfl⟩ : syracuseStep 1227987 = 1841981) B1841981
theorem B5897443 : Blo 1226431 5897443 := bstep (se 1 (by rfl) ⟨4423082, by rfl⟩ : syracuseStep 5897443 = 8846165) B8846165
theorem B2071777 : Blo 1226431 2071777 := bstep (se 2 (by rfl) ⟨776916, by rfl⟩ : syracuseStep 2071777 = 1553833) B1553833
theorem B1228003 : Blo 1226431 1228003 := bstep (se 1 (by rfl) ⟨921002, by rfl⟩ : syracuseStep 1228003 = 1842005) B1842005
theorem B1842401 : Blo 1226431 1842401 := bstep (se 2 (by rfl) ⟨690900, by rfl⟩ : syracuseStep 1842401 = 1381801) B1381801
theorem B2759921 : Blo 1226431 2759921 := bstep (se 2 (by rfl) ⟨1034970, by rfl⟩ : syracuseStep 2759921 = 2069941) B2069941
theorem B1228019 : Blo 1226431 1228019 := bstep (se 1 (by rfl) ⟨921014, by rfl⟩ : syracuseStep 1228019 = 1842029) B1842029
theorem B1842419 : Blo 1226431 1842419 := bstep (se 1 (by rfl) ⟨1381814, by rfl⟩ : syracuseStep 1842419 = 2763629) B2763629
theorem B2759939 : Blo 1226431 2759939 := bstep (se 1 (by rfl) ⟨2069954, by rfl⟩ : syracuseStep 2759939 = 4139909) B4139909
theorem B2071811 : Blo 1226431 2071811 := bstep (se 1 (by rfl) ⟨1553858, by rfl⟩ : syracuseStep 2071811 = 3107717) B3107717
theorem B1228035 : Blo 1226431 1228035 := bstep (se 1 (by rfl) ⟨921026, by rfl⟩ : syracuseStep 1228035 = 1842053) B1842053
theorem B3497219 : Blo 1226431 3497219 := bstep (se 1 (by rfl) ⟨2622914, by rfl⟩ : syracuseStep 3497219 = 5245829) B5245829
theorem B1842449 : Blo 1226431 1842449 := bstep (se 2 (by rfl) ⟨690918, by rfl⟩ : syracuseStep 1842449 = 1381837) B1381837
theorem B1228051 : Blo 1226431 1228051 := bstep (se 1 (by rfl) ⟨921038, by rfl⟩ : syracuseStep 1228051 = 1842077) B1842077
theorem B1228067 : Blo 1226431 1228067 := bstep (se 1 (by rfl) ⟨921050, by rfl⟩ : syracuseStep 1228067 = 1842101) B1842101
theorem B1842467 : Blo 1226431 1842467 := bstep (se 1 (by rfl) ⟨1381850, by rfl⟩ : syracuseStep 1842467 = 2763701) B2763701
theorem B1228083 : Blo 1226431 1228083 := bstep (se 1 (by rfl) ⟨921062, by rfl⟩ : syracuseStep 1228083 = 1842125) B1842125
theorem B1842497 : Blo 1226431 1842497 := bstep (se 2 (by rfl) ⟨690936, by rfl⟩ : syracuseStep 1842497 = 1381873) B1381873
theorem B1965379 : Blo 1226431 1965379 := bstep (se 1 (by rfl) ⟨1474034, by rfl⟩ : syracuseStep 1965379 = 2948069) B2948069
theorem B1228099 : Blo 1226431 1228099 := bstep (se 1 (by rfl) ⟨921074, by rfl⟩ : syracuseStep 1228099 = 1842149) B1842149
theorem B1228115 : Blo 1226431 1228115 := bstep (se 1 (by rfl) ⟨921086, by rfl⟩ : syracuseStep 1228115 = 1842173) B1842173
theorem B1842515 : Blo 1226431 1842515 := bstep (se 1 (by rfl) ⟨1381886, by rfl⟩ : syracuseStep 1842515 = 2763773) B2763773
theorem B1228131 : Blo 1226431 1228131 := bstep (se 1 (by rfl) ⟨921098, by rfl⟩ : syracuseStep 1228131 = 1842197) B1842197
theorem B4423025 : Blo 1226431 4423025 := bstep (se 2 (by rfl) ⟨1658634, by rfl⟩ : syracuseStep 4423025 = 3317269) B3317269
theorem B6217073 : Blo 1226431 6217073 := bstep (se 2 (by rfl) ⟨2331402, by rfl⟩ : syracuseStep 6217073 = 4662805) B4662805
theorem B1228147 : Blo 1226431 1228147 := bstep (se 1 (by rfl) ⟨921110, by rfl⟩ : syracuseStep 1228147 = 1842221) B1842221
theorem B1842545 : Blo 1226431 1842545 := bstep (se 2 (by rfl) ⟨690954, by rfl⟩ : syracuseStep 1842545 = 1381909) B1381909
theorem B2071939 : Blo 1226431 2071939 := bstep (se 1 (by rfl) ⟨1553954, by rfl⟩ : syracuseStep 2071939 = 3107909) B3107909
theorem B1228163 : Blo 1226431 1228163 := bstep (se 1 (by rfl) ⟨921122, by rfl⟩ : syracuseStep 1228163 = 1842245) B1842245
theorem B1842563 : Blo 1226431 1842563 := bstep (se 1 (by rfl) ⟨1381922, by rfl⟩ : syracuseStep 1842563 = 2763845) B2763845
theorem B1228179 : Blo 1226431 1228179 := bstep (se 1 (by rfl) ⟨921134, by rfl⟩ : syracuseStep 1228179 = 1842269) B1842269
theorem B1842593 : Blo 1226431 1842593 := bstep (se 2 (by rfl) ⟨690972, by rfl⟩ : syracuseStep 1842593 = 1381945) B1381945
theorem B1965475 : Blo 1226431 1965475 := bstep (se 1 (by rfl) ⟨1474106, by rfl⟩ : syracuseStep 1965475 = 2948213) B2948213
theorem B1228195 : Blo 1226431 1228195 := bstep (se 1 (by rfl) ⟨921146, by rfl⟩ : syracuseStep 1228195 = 1842293) B1842293
theorem B1228211 : Blo 1226431 1228211 := bstep (se 1 (by rfl) ⟨921158, by rfl⟩ : syracuseStep 1228211 = 1842317) B1842317
theorem B1842611 : Blo 1226431 1842611 := bstep (se 1 (by rfl) ⟨1381958, by rfl⟩ : syracuseStep 1842611 = 2763917) B2763917
theorem B1228227 : Blo 1226431 1228227 := bstep (se 1 (by rfl) ⟨921170, by rfl⟩ : syracuseStep 1228227 = 1842341) B1842341
theorem B6208973 : Blo 1226431 6208973 := bstep (se 3 (by rfl) ⟨1164182, by rfl⟩ : syracuseStep 6208973 = 2328365) B2328365
theorem B1842641 : Blo 1226431 1842641 := bstep (se 2 (by rfl) ⟨690990, by rfl⟩ : syracuseStep 1842641 = 1381981) B1381981
theorem B1228243 : Blo 1226431 1228243 := bstep (se 1 (by rfl) ⟨921182, by rfl⟩ : syracuseStep 1228243 = 1842365) B1842365
theorem B1228259 : Blo 1226431 1228259 := bstep (se 1 (by rfl) ⟨921194, by rfl⟩ : syracuseStep 1228259 = 1842389) B1842389
theorem B1228275 : Blo 1226431 1228275 := bstep (se 1 (by rfl) ⟨921206, by rfl⟩ : syracuseStep 1228275 = 1842413) B1842413
theorem B1228291 : Blo 1226431 1228291 := bstep (se 1 (by rfl) ⟨921218, by rfl⟩ : syracuseStep 1228291 = 1842437) B1842437
theorem B2760209 : Blo 1226431 2760209 := bstep (se 2 (by rfl) ⟨1035078, by rfl⟩ : syracuseStep 2760209 = 2070157) B2070157
theorem B2072081 : Blo 1226431 2072081 := bstep (se 2 (by rfl) ⟨777030, by rfl⟩ : syracuseStep 2072081 = 1554061) B1554061
theorem B1228307 : Blo 1226431 1228307 := bstep (se 1 (by rfl) ⟨921230, by rfl⟩ : syracuseStep 1228307 = 1842461) B1842461
theorem B2760227 : Blo 1226431 2760227 := bstep (se 1 (by rfl) ⟨2070170, by rfl⟩ : syracuseStep 2760227 = 4140341) B4140341
theorem B1228323 : Blo 1226431 1228323 := bstep (se 1 (by rfl) ⟨921242, by rfl⟩ : syracuseStep 1228323 = 1842485) B1842485
theorem B1228339 : Blo 1226431 1228339 := bstep (se 1 (by rfl) ⟨921254, by rfl⟩ : syracuseStep 1228339 = 1842509) B1842509
theorem B1965635 : Blo 1226431 1965635 := bstep (se 1 (by rfl) ⟨1474226, by rfl⟩ : syracuseStep 1965635 = 2948453) B2948453
theorem B1228355 : Blo 1226431 1228355 := bstep (se 1 (by rfl) ⟨921266, by rfl⟩ : syracuseStep 1228355 = 1842533) B1842533
theorem B5242445 : Blo 1226431 5242445 := bstep (se 3 (by rfl) ⟨982958, by rfl⟩ : syracuseStep 5242445 = 1965917) B1965917
theorem B1228371 : Blo 1226431 1228371 := bstep (se 1 (by rfl) ⟨921278, by rfl⟩ : syracuseStep 1228371 = 1842557) B1842557
theorem B1228387 : Blo 1226431 1228387 := bstep (se 1 (by rfl) ⟨921290, by rfl⟩ : syracuseStep 1228387 = 1842581) B1842581
theorem B1228403 : Blo 1226431 1228403 := bstep (se 1 (by rfl) ⟨921302, by rfl⟩ : syracuseStep 1228403 = 1842605) B1842605
theorem B1228419 : Blo 1226431 1228419 := bstep (se 1 (by rfl) ⟨921314, by rfl⟩ : syracuseStep 1228419 = 1842629) B1842629
theorem B2072209 : Blo 1226431 2072209 := bstep (se 2 (by rfl) ⟨777078, by rfl⟩ : syracuseStep 2072209 = 1554157) B1554157
theorem B2072243 : Blo 1226431 2072243 := bstep (se 1 (by rfl) ⟨1554182, by rfl⟩ : syracuseStep 2072243 = 3108365) B3108365
theorem B4144877 : Blo 1226431 4144877 := bstep (se 3 (by rfl) ⟨777164, by rfl⟩ : syracuseStep 4144877 = 1554329) B1554329
theorem B8847089 : Blo 1226431 8847089 := bstep (se 2 (by rfl) ⟨3317658, by rfl⟩ : syracuseStep 8847089 = 6635317) B6635317
theorem B4144931 : Blo 1226431 4144931 := bstep (se 1 (by rfl) ⟨3108698, by rfl⟩ : syracuseStep 4144931 = 6217397) B6217397
theorem B2760497 : Blo 1226431 2760497 := bstep (se 2 (by rfl) ⟨1035186, by rfl⟩ : syracuseStep 2760497 = 2070373) B2070373
theorem B2072371 : Blo 1226431 2072371 := bstep (se 1 (by rfl) ⟨1554278, by rfl⟩ : syracuseStep 2072371 = 3108557) B3108557
theorem B2760515 : Blo 1226431 2760515 := bstep (se 1 (by rfl) ⟨2070386, by rfl⟩ : syracuseStep 2760515 = 4140773) B4140773
theorem B1867619 : Blo 1226431 1867619 := bstep (se 1 (by rfl) ⟨1400714, by rfl⟩ : syracuseStep 1867619 = 2801429) B2801429
theorem B5603185 : Blo 1226431 5603185 := bstep (se 2 (by rfl) ⟨2101194, by rfl⟩ : syracuseStep 5603185 = 4202389) B4202389
theorem B9314189 : Blo 1226431 9314189 := bstep (se 3 (by rfl) ⟨1746410, by rfl⟩ : syracuseStep 9314189 = 3492821) B3492821
theorem B3104689 : Blo 1226431 3104689 := bstep (se 2 (by rfl) ⟨1164258, by rfl⟩ : syracuseStep 3104689 = 2328517) B2328517
theorem B4423601 : Blo 1226431 4423601 := bstep (se 2 (by rfl) ⟨1658850, by rfl⟩ : syracuseStep 4423601 = 3317701) B3317701
theorem B2072513 : Blo 1226431 2072513 := bstep (se 2 (by rfl) ⟨777192, by rfl⟩ : syracuseStep 2072513 = 1554385) B1554385
theorem B2072587 : Blo 1226431 2072587 := bstep (se 1 (by rfl) ⟨1554440, by rfl⟩ : syracuseStep 2072587 = 3108881) B3108881
theorem B6635621 : Blo 1226431 6635621 := bstep (se 4 (by rfl) ⟨622089, by rfl⟩ : syracuseStep 6635621 = 1244179) B1244179
theorem B2760857 : Blo 1226431 2760857 := bstep (se 2 (by rfl) ⟨1035321, by rfl⟩ : syracuseStep 2760857 = 2070643) B2070643
theorem B2072729 : Blo 1226431 2072729 := bstep (se 2 (by rfl) ⟨777273, by rfl⟩ : syracuseStep 2072729 = 1554547) B1554547
theorem B5243059 : Blo 1226431 5243059 := bstep (se 1 (by rfl) ⟨3932294, by rfl⟩ : syracuseStep 5243059 = 7864589) B7864589
theorem B2760947 : Blo 1226431 2760947 := bstep (se 1 (by rfl) ⟨2070710, by rfl⟩ : syracuseStep 2760947 = 4141421) B4141421
theorem B17268997 : Blo 1226431 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B4972823 : Blo 1226431 4972823 := bstep (se 1 (by rfl) ⟨3729617, by rfl⟩ : syracuseStep 4972823 = 7459235) B7459235
theorem B2760983 : Blo 1226431 2760983 := bstep (se 1 (by rfl) ⟨2070737, by rfl⟩ : syracuseStep 2760983 = 4141475) B4141475
theorem B2072857 : Blo 1226431 2072857 := bstep (se 2 (by rfl) ⟨777321, by rfl⟩ : syracuseStep 2072857 = 1554643) B1554643
theorem B2212147 : Blo 1226431 2212147 := bstep (se 1 (by rfl) ⟨1659110, by rfl⟩ : syracuseStep 2212147 = 3318221) B3318221
theorem B3105175 : Blo 1226431 3105175 := bstep (se 1 (by rfl) ⟨2328881, by rfl⟩ : syracuseStep 3105175 = 4657763) B4657763
theorem B2761163 : Blo 1226431 2761163 := bstep (se 1 (by rfl) ⟨2070872, by rfl⟩ : syracuseStep 2761163 = 4141745) B4141745
theorem B2761217 : Blo 1226431 2761217 := bstep (se 2 (by rfl) ⟨1035456, by rfl⟩ : syracuseStep 2761217 = 2070913) B2070913
theorem B4145687 : Blo 1226431 4145687 := bstep (se 1 (by rfl) ⟨3109265, by rfl⟩ : syracuseStep 4145687 = 6218531) B6218531
theorem B6636077 : Blo 1226431 6636077 := bstep (se 3 (by rfl) ⟨1244264, by rfl⟩ : syracuseStep 6636077 = 2488529) B2488529
theorem B7864897 : Blo 1226431 7864897 := bstep (se 2 (by rfl) ⟨2949336, by rfl⟩ : syracuseStep 7864897 = 5898673) B5898673
theorem B1573463 : Blo 1226431 1573463 := bstep (se 1 (by rfl) ⟨1180097, by rfl⟩ : syracuseStep 1573463 = 2360195) B2360195
theorem B2622145 : Blo 1226431 2622145 := bstep (se 2 (by rfl) ⟨983304, by rfl⟩ : syracuseStep 2622145 = 1966609) B1966609
theorem B17703629 : Blo 1226431 17703629 := bstep (se 3 (by rfl) ⟨3319430, by rfl⟩ : syracuseStep 17703629 = 6638861) B6638861
theorem B2761433 : Blo 1226431 2761433 := bstep (se 2 (by rfl) ⟨1035537, by rfl⟩ : syracuseStep 2761433 = 2071075) B2071075
theorem B2212609 : Blo 1226431 2212609 := bstep (se 2 (by rfl) ⟨829728, by rfl⟩ : syracuseStep 2212609 = 1659457) B1659457
theorem B2761523 : Blo 1226431 2761523 := bstep (se 1 (by rfl) ⟨2071142, by rfl⟩ : syracuseStep 2761523 = 4142285) B4142285
theorem B3105611 : Blo 1226431 3105611 := bstep (se 1 (by rfl) ⟨2329208, by rfl⟩ : syracuseStep 3105611 = 4658417) B4658417
theorem B2761559 : Blo 1226431 2761559 := bstep (se 1 (by rfl) ⟨2071169, by rfl⟩ : syracuseStep 2761559 = 4142339) B4142339
theorem B2212723 : Blo 1226431 2212723 := bstep (se 1 (by rfl) ⟨1659542, by rfl⟩ : syracuseStep 2212723 = 3319085) B3319085
theorem B2950067 : Blo 1226431 2950067 := bstep (se 1 (by rfl) ⟨2212550, by rfl⟩ : syracuseStep 2950067 = 4425101) B4425101
theorem B2761739 : Blo 1226431 2761739 := bstep (se 1 (by rfl) ⟨2071304, by rfl⟩ : syracuseStep 2761739 = 4142609) B4142609
theorem B2761793 : Blo 1226431 2761793 := bstep (se 2 (by rfl) ⟨1035672, by rfl⟩ : syracuseStep 2761793 = 2071345) B2071345
theorem B3105985 : Blo 1226431 3105985 := bstep (se 2 (by rfl) ⟨1164744, by rfl⟩ : syracuseStep 3105985 = 2329489) B2329489
theorem B1967321 : Blo 1226431 1967321 := bstep (se 2 (by rfl) ⟨737745, by rfl⟩ : syracuseStep 1967321 = 1475491) B1475491
theorem B2762009 : Blo 1226431 2762009 := bstep (se 2 (by rfl) ⟨1035753, by rfl⟩ : syracuseStep 2762009 = 2071507) B2071507
theorem B4662593 : Blo 1226431 4662593 := bstep (se 2 (by rfl) ⟨1748472, by rfl⟩ : syracuseStep 4662593 = 3496945) B3496945
theorem B2213185 : Blo 1226431 2213185 := bstep (se 2 (by rfl) ⟨829944, by rfl⟩ : syracuseStep 2213185 = 1659889) B1659889
theorem B2762099 : Blo 1226431 2762099 := bstep (se 1 (by rfl) ⟨2071574, by rfl⟩ : syracuseStep 2762099 = 4143149) B4143149
theorem B64603541 : Blo 1226431 64603541 := bstep (se 6 (by rfl) ⟨1514145, by rfl⟩ : syracuseStep 64603541 = 3028291) B3028291
theorem B2762135 : Blo 1226431 2762135 := bstep (se 1 (by rfl) ⟨2071601, by rfl⟩ : syracuseStep 2762135 = 4143203) B4143203
theorem B2213387 : Blo 1226431 2213387 := bstep (se 1 (by rfl) ⟨1660040, by rfl⟩ : syracuseStep 2213387 = 3320081) B3320081
theorem B4974155 : Blo 1226431 4974155 := bstep (se 1 (by rfl) ⟨3730616, by rfl⟩ : syracuseStep 4974155 = 7461233) B7461233
theorem B2762315 : Blo 1226431 2762315 := bstep (se 1 (by rfl) ⟨2071736, by rfl⟩ : syracuseStep 2762315 = 4143473) B4143473
theorem B2762369 : Blo 1226431 2762369 := bstep (se 2 (by rfl) ⟨1035888, by rfl⟩ : syracuseStep 2762369 = 2071777) B2071777
theorem B5244547 : Blo 1226431 5244547 := bstep (se 1 (by rfl) ⟨3933410, by rfl⟩ : syracuseStep 5244547 = 7866821) B7866821
theorem B8849047 : Blo 1226431 8849047 := bstep (se 1 (by rfl) ⟨6636785, by rfl⟩ : syracuseStep 8849047 = 13273571) B13273571
theorem B2361089 : Blo 1226431 2361089 := bstep (se 2 (by rfl) ⟨885408, by rfl⟩ : syracuseStep 2361089 = 1770817) B1770817
theorem B3106583 : Blo 1226431 3106583 := bstep (se 1 (by rfl) ⟨2329937, by rfl⟩ : syracuseStep 3106583 = 4659875) B4659875
theorem B6211403 : Blo 1226431 6211403 := bstep (se 1 (by rfl) ⟨4658552, by rfl⟩ : syracuseStep 6211403 = 9317105) B9317105
theorem B1746775 : Blo 1226431 1746775 := bstep (se 1 (by rfl) ⟨1310081, by rfl⟩ : syracuseStep 1746775 = 2620163) B2620163
theorem B2762585 : Blo 1226431 2762585 := bstep (se 2 (by rfl) ⟨1035969, by rfl⟩ : syracuseStep 2762585 = 2071939) B2071939
theorem B6637463 : Blo 1226431 6637463 := bstep (se 1 (by rfl) ⟨4978097, by rfl⟩ : syracuseStep 6637463 = 9956195) B9956195
theorem B2762675 : Blo 1226431 2762675 := bstep (se 1 (by rfl) ⟨2072006, by rfl⟩ : syracuseStep 2762675 = 4144013) B4144013
theorem B2762711 : Blo 1226431 2762711 := bstep (se 1 (by rfl) ⟨2072033, by rfl⟩ : syracuseStep 2762711 = 4144067) B4144067
theorem B2328563 : Blo 1226431 2328563 := bstep (se 1 (by rfl) ⟨1746422, by rfl⟩ : syracuseStep 2328563 = 3492845) B3492845
theorem B2328601 : Blo 1226431 2328601 := bstep (se 2 (by rfl) ⟨873225, by rfl⟩ : syracuseStep 2328601 = 1746451) B1746451
theorem B2762891 : Blo 1226431 2762891 := bstep (se 1 (by rfl) ⟨2072168, by rfl⟩ : syracuseStep 2762891 = 4144337) B4144337
theorem B2762945 : Blo 1226431 2762945 := bstep (se 2 (by rfl) ⟨1036104, by rfl⟩ : syracuseStep 2762945 = 2072209) B2072209
theorem B5245145 : Blo 1226431 5245145 := bstep (se 2 (by rfl) ⟨1966929, by rfl⟩ : syracuseStep 5245145 = 3933859) B3933859
theorem B4139315 : Blo 1226431 4139315 := bstep (se 1 (by rfl) ⟨3104486, by rfl⟩ : syracuseStep 4139315 = 6208973) B6208973
theorem B2763161 : Blo 1226431 2763161 := bstep (se 2 (by rfl) ⟨1036185, by rfl⟩ : syracuseStep 2763161 = 2072371) B2072371
theorem B2329049 : Blo 1226431 2329049 := bstep (se 2 (by rfl) ⟨873393, by rfl⟩ : syracuseStep 2329049 = 1746787) B1746787
theorem B1771993 : Blo 1226431 1771993 := bstep (se 2 (by rfl) ⟨664497, by rfl⟩ : syracuseStep 1771993 = 1328995) B1328995
theorem B6638041 : Blo 1226431 6638041 := bstep (se 2 (by rfl) ⟨2489265, by rfl⟩ : syracuseStep 6638041 = 4978531) B4978531
theorem B2763251 : Blo 1226431 2763251 := bstep (se 1 (by rfl) ⟨2072438, by rfl⟩ : syracuseStep 2763251 = 4144877) B4144877
theorem B2763287 : Blo 1226431 2763287 := bstep (se 1 (by rfl) ⟨2072465, by rfl⟩ : syracuseStep 2763287 = 4144931) B4144931
theorem B4139585 : Blo 1226431 4139585 := bstep (se 2 (by rfl) ⟨1552344, by rfl⟩ : syracuseStep 4139585 = 3104689) B3104689
theorem B3107393 : Blo 1226431 3107393 := bstep (se 2 (by rfl) ⟨1165272, by rfl⟩ : syracuseStep 3107393 = 2330545) B2330545
theorem B5245505 : Blo 1226431 5245505 := bstep (se 2 (by rfl) ⟨1967064, by rfl⟩ : syracuseStep 5245505 = 3934129) B3934129
theorem B3492503 : Blo 1226431 3492503 := bstep (se 1 (by rfl) ⟨2619377, by rfl⟩ : syracuseStep 3492503 = 5238755) B5238755
theorem B2763467 : Blo 1226431 2763467 := bstep (se 1 (by rfl) ⟨2072600, by rfl⟩ : syracuseStep 2763467 = 4145201) B4145201
theorem B2837207 : Blo 1226431 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B2763521 : Blo 1226431 2763521 := bstep (se 2 (by rfl) ⟨1036320, by rfl⟩ : syracuseStep 2763521 = 2072641) B2072641
theorem B4664081 : Blo 1226431 4664081 := bstep (se 2 (by rfl) ⟨1749030, by rfl⟩ : syracuseStep 4664081 = 3498061) B3498061
theorem B3935051 : Blo 1226431 3935051 := bstep (se 1 (by rfl) ⟨2951288, by rfl⟩ : syracuseStep 3935051 = 5902577) B5902577
theorem B4197323 : Blo 1226431 4197323 := bstep (se 1 (by rfl) ⟨3147992, by rfl⟩ : syracuseStep 4197323 = 6295985) B6295985
theorem B1993675 : Blo 1226431 1993675 := bstep (se 1 (by rfl) ⟨1495256, by rfl⟩ : syracuseStep 1993675 = 2990513) B2990513
theorem B21269465 : Blo 1226431 21269465 := bstep (se 2 (by rfl) ⟨7976049, by rfl⟩ : syracuseStep 21269465 = 15952099) B15952099
theorem B2763737 : Blo 1226431 2763737 := bstep (se 2 (by rfl) ⟨1036401, by rfl⟩ : syracuseStep 2763737 = 2072803) B2072803
theorem B2763827 : Blo 1226431 2763827 := bstep (se 1 (by rfl) ⟨2072870, by rfl⟩ : syracuseStep 2763827 = 4145741) B4145741
theorem B2763863 : Blo 1226431 2763863 := bstep (se 1 (by rfl) ⟨2072897, by rfl⟩ : syracuseStep 2763863 = 4145795) B4145795
theorem B3107929 : Blo 1226431 3107929 := bstep (se 2 (by rfl) ⟨1165473, by rfl⟩ : syracuseStep 3107929 = 2330947) B2330947
theorem B4140125 : Blo 1226431 4140125 := bstep (se 3 (by rfl) ⟨776273, by rfl⟩ : syracuseStep 4140125 = 1552547) B1552547
theorem B5901443 : Blo 1226431 5901443 := bstep (se 1 (by rfl) ⟨4426082, by rfl⟩ : syracuseStep 5901443 = 8852165) B8852165
theorem B23956661 : Blo 1226431 23956661 := bstep (se 5 (by rfl) ⟨1122968, by rfl⟩ : syracuseStep 23956661 = 2245937) B2245937
theorem B2329793 : Blo 1226431 2329793 := bstep (se 2 (by rfl) ⟨873672, by rfl⟩ : syracuseStep 2329793 = 1747345) B1747345
theorem B8744153 : Blo 1226431 8744153 := bstep (se 2 (by rfl) ⟨3279057, by rfl⟩ : syracuseStep 8744153 = 6558115) B6558115
theorem B2837747 : Blo 1226431 2837747 := bstep (se 1 (by rfl) ⟨2128310, by rfl⟩ : syracuseStep 2837747 = 4256621) B4256621
theorem B2592011 : Blo 1226431 2592011 := bstep (se 1 (by rfl) ⟨1944008, by rfl⟩ : syracuseStep 2592011 = 3888017) B3888017
theorem B5615021 : Blo 1226431 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B1379767 : Blo 1226431 1379767 := bstep (se 1 (by rfl) ⟨1034825, by rfl⟩ : syracuseStep 1379767 = 2069651) B2069651
theorem B2330059 : Blo 1226431 2330059 := bstep (se 1 (by rfl) ⟨1747544, by rfl⟩ : syracuseStep 2330059 = 3495089) B3495089
theorem B1658327 : Blo 1226431 1658327 := bstep (se 1 (by rfl) ⟨1243745, by rfl⟩ : syracuseStep 1658327 = 2487491) B2487491
theorem B10481197 : Blo 1226431 10481197 := bstep (se 3 (by rfl) ⟨1965224, by rfl⟩ : syracuseStep 10481197 = 3930449) B3930449
theorem B6213185 : Blo 1226431 6213185 := bstep (se 2 (by rfl) ⟨2329944, by rfl⟩ : syracuseStep 6213185 = 4659889) B4659889
theorem B1379947 : Blo 1226431 1379947 := bstep (se 1 (by rfl) ⟨1034960, by rfl⟩ : syracuseStep 1379947 = 2069921) B2069921
theorem B4656791 : Blo 1226431 4656791 := bstep (se 1 (by rfl) ⟨3492593, by rfl⟩ : syracuseStep 4656791 = 6985187) B6985187
theorem B7966387 : Blo 1226431 7966387 := bstep (se 1 (by rfl) ⟨5974790, by rfl⟩ : syracuseStep 7966387 = 11949581) B11949581
theorem B8851123 : Blo 1226431 8851123 := bstep (se 1 (by rfl) ⟨6638342, by rfl⟩ : syracuseStep 8851123 = 13276685) B13276685
theorem B1380055 : Blo 1226431 1380055 := bstep (se 1 (by rfl) ⟨1035041, by rfl⟩ : syracuseStep 1380055 = 2070083) B2070083
theorem B6639425 : Blo 1226431 6639425 := bstep (se 2 (by rfl) ⟨2489784, by rfl⟩ : syracuseStep 6639425 = 4979569) B4979569
theorem B5975939 : Blo 1226431 5975939 := bstep (se 1 (by rfl) ⟨4481954, by rfl⟩ : syracuseStep 5975939 = 8963909) B8963909
theorem B1380235 : Blo 1226431 1380235 := bstep (se 1 (by rfl) ⟨1035176, by rfl⟩ : syracuseStep 1380235 = 2070353) B2070353
theorem B2330507 : Blo 1226431 2330507 := bstep (se 1 (by rfl) ⟨1747880, by rfl⟩ : syracuseStep 2330507 = 3495761) B3495761
theorem B1552279 : Blo 1226431 1552279 := bstep (se 1 (by rfl) ⟨1164209, by rfl⟩ : syracuseStep 1552279 = 2328419) B2328419
theorem B16797617 : Blo 1226431 16797617 := bstep (se 2 (by rfl) ⟨6299106, by rfl⟩ : syracuseStep 16797617 = 12598213) B12598213
theorem B2797505 : Blo 1226431 2797505 := bstep (se 2 (by rfl) ⟨1049064, by rfl⟩ : syracuseStep 2797505 = 2098129) B2098129
theorem B1380343 : Blo 1226431 1380343 := bstep (se 1 (by rfl) ⟨1035257, by rfl⟩ : syracuseStep 1380343 = 2070515) B2070515
theorem B7868461 : Blo 1226431 7868461 := bstep (se 3 (by rfl) ⟨1475336, by rfl⟩ : syracuseStep 7868461 = 2950673) B2950673
theorem B2330689 : Blo 1226431 2330689 := bstep (se 2 (by rfl) ⟨874008, by rfl⟩ : syracuseStep 2330689 = 1748017) B1748017
theorem B7082059 : Blo 1226431 7082059 := bstep (se 1 (by rfl) ⟨5311544, by rfl⟩ : syracuseStep 7082059 = 10623089) B10623089
theorem B1380523 : Blo 1226431 1380523 := bstep (se 1 (by rfl) ⟨1035392, by rfl⟩ : syracuseStep 1380523 = 2070785) B2070785
theorem B4788397 : Blo 1226431 4788397 := bstep (se 3 (by rfl) ⟨897824, by rfl⟩ : syracuseStep 4788397 = 1795649) B1795649
theorem B3109043 : Blo 1226431 3109043 := bstep (se 1 (by rfl) ⟨2331782, by rfl⟩ : syracuseStep 3109043 = 4663565) B4663565
theorem B4141259 : Blo 1226431 4141259 := bstep (se 1 (by rfl) ⟨3105944, by rfl⟩ : syracuseStep 4141259 = 6211889) B6211889
theorem B1380631 : Blo 1226431 1380631 := bstep (se 1 (by rfl) ⟨1035473, by rfl⟩ : syracuseStep 1380631 = 2070947) B2070947
theorem B15143213 : Blo 1226431 15143213 := bstep (se 3 (by rfl) ⟨2839352, by rfl⟩ : syracuseStep 15143213 = 5678705) B5678705
theorem B4657459 : Blo 1226431 4657459 := bstep (se 1 (by rfl) ⟨3493094, by rfl⟩ : syracuseStep 4657459 = 6986189) B6986189
theorem B6992203 : Blo 1226431 6992203 := bstep (se 1 (by rfl) ⟨5244152, by rfl⟩ : syracuseStep 6992203 = 10488305) B10488305
theorem B2331031 : Blo 1226431 2331031 := bstep (se 1 (by rfl) ⟨1748273, by rfl⟩ : syracuseStep 2331031 = 3496547) B3496547
theorem B1380811 : Blo 1226431 1380811 := bstep (se 1 (by rfl) ⟨1035608, by rfl⟩ : syracuseStep 1380811 = 2071217) B2071217
theorem B4141529 : Blo 1226431 4141529 := bstep (se 2 (by rfl) ⟨1553073, by rfl⟩ : syracuseStep 4141529 = 3106147) B3106147
theorem B3109337 : Blo 1226431 3109337 := bstep (se 2 (by rfl) ⟨1166001, by rfl⟩ : syracuseStep 3109337 = 2332003) B2332003
theorem B1380919 : Blo 1226431 1380919 := bstep (se 1 (by rfl) ⟨1035689, by rfl⟩ : syracuseStep 1380919 = 2071379) B2071379
theorem B6992477 : Blo 1226431 6992477 := bstep (se 3 (by rfl) ⟨1311089, by rfl⟩ : syracuseStep 6992477 = 2622179) B2622179
theorem B2331251 : Blo 1226431 2331251 := bstep (se 1 (by rfl) ⟨1748438, by rfl⟩ : syracuseStep 2331251 = 3496877) B3496877
theorem B1839755 : Blo 1226431 1839755 := bstep (se 1 (by rfl) ⟨1379816, by rfl⟩ : syracuseStep 1839755 = 2759633) B2759633
theorem B1839767 : Blo 1226431 1839767 := bstep (se 1 (by rfl) ⟨1379825, by rfl⟩ : syracuseStep 1839767 = 2759651) B2759651
theorem B1839833 : Blo 1226431 1839833 := bstep (se 2 (by rfl) ⟨689937, by rfl⟩ : syracuseStep 1839833 = 1379875) B1379875
theorem B1381099 : Blo 1226431 1381099 := bstep (se 1 (by rfl) ⟨1035824, by rfl⟩ : syracuseStep 1381099 = 2071649) B2071649
theorem B11195171 : Blo 1226431 11195171 := bstep (se 1 (by rfl) ⟨8396378, by rfl⟩ : syracuseStep 11195171 = 16792757) B16792757
theorem B1839947 : Blo 1226431 1839947 := bstep (se 1 (by rfl) ⟨1379960, by rfl⟩ : syracuseStep 1839947 = 2759921) B2759921
theorem B1839959 : Blo 1226431 1839959 := bstep (se 1 (by rfl) ⟨1379969, by rfl⟩ : syracuseStep 1839959 = 2759939) B2759939
theorem B1381207 : Blo 1226431 1381207 := bstep (se 1 (by rfl) ⟨1035905, by rfl⟩ : syracuseStep 1381207 = 2071811) B2071811
theorem B2331479 : Blo 1226431 2331479 := bstep (se 1 (by rfl) ⟨1748609, by rfl⟩ : syracuseStep 2331479 = 3497219) B3497219
theorem B10482533 : Blo 1226431 10482533 := bstep (se 4 (by rfl) ⟨982737, by rfl⟩ : syracuseStep 10482533 = 1965475) B1965475
theorem B1840025 : Blo 1226431 1840025 := bstep (se 2 (by rfl) ⟨690009, by rfl⟩ : syracuseStep 1840025 = 1380019) B1380019
theorem B12587993 : Blo 1226431 12587993 := bstep (se 2 (by rfl) ⟨4720497, by rfl⟩ : syracuseStep 12587993 = 9440995) B9440995
theorem B1840139 : Blo 1226431 1840139 := bstep (se 1 (by rfl) ⟨1380104, by rfl⟩ : syracuseStep 1840139 = 2760209) B2760209
theorem B1381387 : Blo 1226431 1381387 := bstep (se 1 (by rfl) ⟨1036040, by rfl⟩ : syracuseStep 1381387 = 2072081) B2072081
theorem B1840151 : Blo 1226431 1840151 := bstep (se 1 (by rfl) ⟨1380113, by rfl⟩ : syracuseStep 1840151 = 2760227) B2760227
theorem B3494963 : Blo 1226431 3494963 := bstep (se 1 (by rfl) ⟨2621222, by rfl⟩ : syracuseStep 3494963 = 5242445) B5242445
theorem B1840217 : Blo 1226431 1840217 := bstep (se 2 (by rfl) ⟨690081, by rfl⟩ : syracuseStep 1840217 = 1380163) B1380163
theorem B2331737 : Blo 1226431 2331737 := bstep (se 2 (by rfl) ⟨874401, by rfl⟩ : syracuseStep 2331737 = 1748803) B1748803
theorem B6632549 : Blo 1226431 6632549 := bstep (se 4 (by rfl) ⟨621801, by rfl⟩ : syracuseStep 6632549 = 1243603) B1243603
theorem B1381495 : Blo 1226431 1381495 := bstep (se 1 (by rfl) ⟨1036121, by rfl⟩ : syracuseStep 1381495 = 2072243) B2072243
theorem B4142231 : Blo 1226431 4142231 := bstep (se 1 (by rfl) ⟨3106673, by rfl⟩ : syracuseStep 4142231 = 6213347) B6213347
theorem B3732659 : Blo 1226431 3732659 := bstep (se 1 (by rfl) ⟨2799494, by rfl⟩ : syracuseStep 3732659 = 5598989) B5598989
theorem B1840331 : Blo 1226431 1840331 := bstep (se 1 (by rfl) ⟨1380248, by rfl⟩ : syracuseStep 1840331 = 2760497) B2760497
theorem B14169293 : Blo 1226431 14169293 := bstep (se 3 (by rfl) ⟨2656742, by rfl⟩ : syracuseStep 14169293 = 5313485) B5313485
theorem B1840343 : Blo 1226431 1840343 := bstep (se 1 (by rfl) ⟨1380257, by rfl⟩ : syracuseStep 1840343 = 2760515) B2760515
theorem B1840409 : Blo 1226431 1840409 := bstep (se 2 (by rfl) ⟨690153, by rfl⟩ : syracuseStep 1840409 = 1380307) B1380307
theorem B1381675 : Blo 1226431 1381675 := bstep (se 1 (by rfl) ⟨1036256, by rfl⟩ : syracuseStep 1381675 = 2072513) B2072513
theorem B1840523 : Blo 1226431 1840523 := bstep (se 1 (by rfl) ⟨1380392, by rfl⟩ : syracuseStep 1840523 = 2760785) B2760785
theorem B1840535 : Blo 1226431 1840535 := bstep (se 1 (by rfl) ⟨1380401, by rfl⟩ : syracuseStep 1840535 = 2760803) B2760803
theorem B1381783 : Blo 1226431 1381783 := bstep (se 1 (by rfl) ⟨1036337, by rfl⟩ : syracuseStep 1381783 = 2072675) B2072675
theorem B2069975 : Blo 1226431 2069975 := bstep (se 1 (by rfl) ⟨1552481, by rfl⟩ : syracuseStep 2069975 = 3104963) B3104963
theorem B1840601 : Blo 1226431 1840601 := bstep (se 2 (by rfl) ⟨690225, by rfl⟩ : syracuseStep 1840601 = 1380451) B1380451
theorem B6215129 : Blo 1226431 6215129 := bstep (se 2 (by rfl) ⟨2330673, by rfl⟩ : syracuseStep 6215129 = 4661347) B4661347
theorem B3544541 : Blo 1226431 3544541 := bstep (se 3 (by rfl) ⟨664601, by rfl⟩ : syracuseStep 3544541 = 1329203) B1329203
theorem B4658705 : Blo 1226431 4658705 := bstep (se 2 (by rfl) ⟨1747014, by rfl⟩ : syracuseStep 4658705 = 3494029) B3494029
theorem B1840715 : Blo 1226431 1840715 := bstep (se 1 (by rfl) ⟨1380536, by rfl⟩ : syracuseStep 1840715 = 2761073) B2761073
theorem B1553995 : Blo 1226431 1553995 := bstep (se 1 (by rfl) ⟨1165496, by rfl⟩ : syracuseStep 1553995 = 2330993) B2330993
theorem B22410827 : Blo 1226431 22410827 := bstep (se 1 (by rfl) ⟨16808120, by rfl⟩ : syracuseStep 22410827 = 33616241) B33616241
theorem B1381963 : Blo 1226431 1381963 := bstep (se 1 (by rfl) ⟨1036472, by rfl⟩ : syracuseStep 1381963 = 2072945) B2072945
theorem B2070103 : Blo 1226431 2070103 := bstep (se 1 (by rfl) ⟨1552577, by rfl⟩ : syracuseStep 2070103 = 3105155) B3105155
theorem B1840727 : Blo 1226431 1840727 := bstep (se 1 (by rfl) ⟨1380545, by rfl⟩ : syracuseStep 1840727 = 2761091) B2761091
theorem B1840793 : Blo 1226431 1840793 := bstep (se 2 (by rfl) ⟨690297, by rfl⟩ : syracuseStep 1840793 = 1380595) B1380595
theorem B4142771 : Blo 1226431 4142771 := bstep (se 1 (by rfl) ⟨3107078, by rfl⟩ : syracuseStep 4142771 = 6214157) B6214157
theorem B1226443 : Blo 1226431 1226443 := bstep (se 1 (by rfl) ⟨919832, by rfl⟩ : syracuseStep 1226443 = 1839665) B1839665
theorem B1226455 : Blo 1226431 1226455 := bstep (se 1 (by rfl) ⟨919841, by rfl⟩ : syracuseStep 1226455 = 1839683) B1839683
theorem B1226475 : Blo 1226431 1226475 := bstep (se 1 (by rfl) ⟨919856, by rfl⟩ : syracuseStep 1226475 = 1839713) B1839713
theorem B1226487 : Blo 1226431 1226487 := bstep (se 1 (by rfl) ⟨919865, by rfl⟩ : syracuseStep 1226487 = 1839731) B1839731
theorem B1226507 : Blo 1226431 1226507 := bstep (se 1 (by rfl) ⟨919880, by rfl⟩ : syracuseStep 1226507 = 1839761) B1839761
theorem B1840907 : Blo 1226431 1840907 := bstep (se 1 (by rfl) ⟨1380680, by rfl⟩ : syracuseStep 1840907 = 2761361) B2761361
theorem B1226519 : Blo 1226431 1226519 := bstep (se 1 (by rfl) ⟨919889, by rfl⟩ : syracuseStep 1226519 = 1839779) B1839779
theorem B1840919 : Blo 1226431 1840919 := bstep (se 1 (by rfl) ⟨1380689, by rfl⟩ : syracuseStep 1840919 = 2761379) B2761379
theorem B1226539 : Blo 1226431 1226539 := bstep (se 1 (by rfl) ⟨919904, by rfl⟩ : syracuseStep 1226539 = 1839809) B1839809
theorem B1226551 : Blo 1226431 1226551 := bstep (se 1 (by rfl) ⟨919913, by rfl⟩ : syracuseStep 1226551 = 1839827) B1839827
theorem B5601089 : Blo 1226431 5601089 := bstep (se 2 (by rfl) ⟨2100408, by rfl⟩ : syracuseStep 5601089 = 4200817) B4200817
theorem B1226571 : Blo 1226431 1226571 := bstep (se 1 (by rfl) ⟨919928, by rfl⟩ : syracuseStep 1226571 = 1839857) B1839857
theorem B1226583 : Blo 1226431 1226583 := bstep (se 1 (by rfl) ⟨919937, by rfl⟩ : syracuseStep 1226583 = 1839875) B1839875
theorem B1840985 : Blo 1226431 1840985 := bstep (se 2 (by rfl) ⟨690369, by rfl⟩ : syracuseStep 1840985 = 1380739) B1380739
theorem B1226603 : Blo 1226431 1226603 := bstep (se 1 (by rfl) ⟨919952, by rfl⟩ : syracuseStep 1226603 = 1839905) B1839905
theorem B1226615 : Blo 1226431 1226615 := bstep (se 1 (by rfl) ⟨919961, by rfl⟩ : syracuseStep 1226615 = 1839923) B1839923
theorem B1226635 : Blo 1226431 1226635 := bstep (se 1 (by rfl) ⟨919976, by rfl⟩ : syracuseStep 1226635 = 1839953) B1839953
theorem B1226647 : Blo 1226431 1226647 := bstep (se 1 (by rfl) ⟨919985, by rfl⟩ : syracuseStep 1226647 = 1839971) B1839971
theorem B1226667 : Blo 1226431 1226667 := bstep (se 1 (by rfl) ⟨920000, by rfl⟩ : syracuseStep 1226667 = 1840001) B1840001
theorem B1226679 : Blo 1226431 1226679 := bstep (se 1 (by rfl) ⟨920009, by rfl⟩ : syracuseStep 1226679 = 1840019) B1840019
theorem B4143041 : Blo 1226431 4143041 := bstep (se 2 (by rfl) ⟨1553640, by rfl⟩ : syracuseStep 4143041 = 3107281) B3107281
theorem B1226699 : Blo 1226431 1226699 := bstep (se 1 (by rfl) ⟨920024, by rfl⟩ : syracuseStep 1226699 = 1840049) B1840049
theorem B1841099 : Blo 1226431 1841099 := bstep (se 1 (by rfl) ⟨1380824, by rfl⟩ : syracuseStep 1841099 = 2761649) B2761649
theorem B1226711 : Blo 1226431 1226711 := bstep (se 1 (by rfl) ⟨920033, by rfl⟩ : syracuseStep 1226711 = 1840067) B1840067
theorem B1841111 : Blo 1226431 1841111 := bstep (se 1 (by rfl) ⟨1380833, by rfl⟩ : syracuseStep 1841111 = 2761667) B2761667
theorem B1226731 : Blo 1226431 1226731 := bstep (se 1 (by rfl) ⟨920048, by rfl⟩ : syracuseStep 1226731 = 1840097) B1840097
theorem B1226743 : Blo 1226431 1226743 := bstep (se 1 (by rfl) ⟨920057, by rfl⟩ : syracuseStep 1226743 = 1840115) B1840115
theorem B1226763 : Blo 1226431 1226763 := bstep (se 1 (by rfl) ⟨920072, by rfl⟩ : syracuseStep 1226763 = 1840145) B1840145
theorem B1226775 : Blo 1226431 1226775 := bstep (se 1 (by rfl) ⟨920081, by rfl⟩ : syracuseStep 1226775 = 1840163) B1840163
theorem B1841177 : Blo 1226431 1841177 := bstep (se 2 (by rfl) ⟨690441, by rfl⟩ : syracuseStep 1841177 = 1380883) B1380883
theorem B1226795 : Blo 1226431 1226795 := bstep (se 1 (by rfl) ⟨920096, by rfl⟩ : syracuseStep 1226795 = 1840193) B1840193
theorem B2799667 : Blo 1226431 2799667 := bstep (se 1 (by rfl) ⟨2099750, by rfl⟩ : syracuseStep 2799667 = 4199501) B4199501
theorem B1226807 : Blo 1226431 1226807 := bstep (se 1 (by rfl) ⟨920105, by rfl⟩ : syracuseStep 1226807 = 1840211) B1840211
theorem B1226827 : Blo 1226431 1226827 := bstep (se 1 (by rfl) ⟨920120, by rfl⟩ : syracuseStep 1226827 = 1840241) B1840241
theorem B1226839 : Blo 1226431 1226839 := bstep (se 1 (by rfl) ⟨920129, by rfl⟩ : syracuseStep 1226839 = 1840259) B1840259
theorem B1226859 : Blo 1226431 1226859 := bstep (se 1 (by rfl) ⟨920144, by rfl⟩ : syracuseStep 1226859 = 1840289) B1840289
theorem B1226871 : Blo 1226431 1226871 := bstep (se 1 (by rfl) ⟨920153, by rfl⟩ : syracuseStep 1226871 = 1840307) B1840307
theorem B1226891 : Blo 1226431 1226891 := bstep (se 1 (by rfl) ⟨920168, by rfl⟩ : syracuseStep 1226891 = 1840337) B1840337
theorem B1841291 : Blo 1226431 1841291 := bstep (se 1 (by rfl) ⟨1380968, by rfl⟩ : syracuseStep 1841291 = 2761937) B2761937
theorem B1226903 : Blo 1226431 1226903 := bstep (se 1 (by rfl) ⟨920177, by rfl⟩ : syracuseStep 1226903 = 1840355) B1840355
theorem B1841303 : Blo 1226431 1841303 := bstep (se 1 (by rfl) ⟨1380977, by rfl⟩ : syracuseStep 1841303 = 2761955) B2761955
theorem B1226923 : Blo 1226431 1226923 := bstep (se 1 (by rfl) ⟨920192, by rfl⟩ : syracuseStep 1226923 = 1840385) B1840385
theorem B1226935 : Blo 1226431 1226935 := bstep (se 1 (by rfl) ⟨920201, by rfl⟩ : syracuseStep 1226935 = 1840403) B1840403
theorem B1226955 : Blo 1226431 1226955 := bstep (se 1 (by rfl) ⟨920216, by rfl⟩ : syracuseStep 1226955 = 1840433) B1840433
theorem B2070731 : Blo 1226431 2070731 := bstep (se 1 (by rfl) ⟨1553048, by rfl⟩ : syracuseStep 2070731 = 3106097) B3106097
theorem B4659403 : Blo 1226431 4659403 := bstep (se 1 (by rfl) ⟨3494552, by rfl⟩ : syracuseStep 4659403 = 6989105) B6989105
theorem B1226967 : Blo 1226431 1226967 := bstep (se 1 (by rfl) ⟨920225, by rfl⟩ : syracuseStep 1226967 = 1840451) B1840451
theorem B1841369 : Blo 1226431 1841369 := bstep (se 2 (by rfl) ⟨690513, by rfl⟩ : syracuseStep 1841369 = 1381027) B1381027
theorem B1226987 : Blo 1226431 1226987 := bstep (se 1 (by rfl) ⟨920240, by rfl⟩ : syracuseStep 1226987 = 1840481) B1840481
theorem B1226999 : Blo 1226431 1226999 := bstep (se 1 (by rfl) ⟨920249, by rfl⟩ : syracuseStep 1226999 = 1840499) B1840499
theorem B1227019 : Blo 1226431 1227019 := bstep (se 1 (by rfl) ⟨920264, by rfl⟩ : syracuseStep 1227019 = 1840529) B1840529
theorem B2210071 : Blo 1226431 2210071 := bstep (se 1 (by rfl) ⟨1657553, by rfl⟩ : syracuseStep 2210071 = 3315107) B3315107
theorem B1227031 : Blo 1226431 1227031 := bstep (se 1 (by rfl) ⟨920273, by rfl⟩ : syracuseStep 1227031 = 1840547) B1840547
theorem B2488601 : Blo 1226431 2488601 := bstep (se 2 (by rfl) ⟨933225, by rfl⟩ : syracuseStep 2488601 = 1866451) B1866451
theorem B1227051 : Blo 1226431 1227051 := bstep (se 1 (by rfl) ⟨920288, by rfl⟩ : syracuseStep 1227051 = 1840577) B1840577
theorem B11794733 : Blo 1226431 11794733 := bstep (se 3 (by rfl) ⟨2211512, by rfl⟩ : syracuseStep 11794733 = 4423025) B4423025
theorem B1227063 : Blo 1226431 1227063 := bstep (se 1 (by rfl) ⟨920297, by rfl⟩ : syracuseStep 1227063 = 1840595) B1840595
theorem B1890635 : Blo 1226431 1890635 := bstep (se 1 (by rfl) ⟨1417976, by rfl⟩ : syracuseStep 1890635 = 2835953) B2835953
theorem B1227083 : Blo 1226431 1227083 := bstep (se 1 (by rfl) ⟨920312, by rfl⟩ : syracuseStep 1227083 = 1840625) B1840625
theorem B2070859 : Blo 1226431 2070859 := bstep (se 1 (by rfl) ⟨1553144, by rfl⟩ : syracuseStep 2070859 = 3106289) B3106289
theorem B1841483 : Blo 1226431 1841483 := bstep (se 1 (by rfl) ⟨1381112, by rfl⟩ : syracuseStep 1841483 = 2762225) B2762225
theorem B1227095 : Blo 1226431 1227095 := bstep (se 1 (by rfl) ⟨920321, by rfl⟩ : syracuseStep 1227095 = 1840643) B1840643
theorem B1841495 : Blo 1226431 1841495 := bstep (se 1 (by rfl) ⟨1381121, by rfl⟩ : syracuseStep 1841495 = 2762243) B2762243
theorem B1227115 : Blo 1226431 1227115 := bstep (se 1 (by rfl) ⟨920336, by rfl⟩ : syracuseStep 1227115 = 1840673) B1840673
theorem B1227127 : Blo 1226431 1227127 := bstep (se 1 (by rfl) ⟨920345, by rfl⟩ : syracuseStep 1227127 = 1840691) B1840691
theorem B1227147 : Blo 1226431 1227147 := bstep (se 1 (by rfl) ⟨920360, by rfl⟩ : syracuseStep 1227147 = 1840721) B1840721
theorem B1227159 : Blo 1226431 1227159 := bstep (se 1 (by rfl) ⟨920369, by rfl⟩ : syracuseStep 1227159 = 1840739) B1840739
theorem B1841561 : Blo 1226431 1841561 := bstep (se 2 (by rfl) ⟨690585, by rfl⟩ : syracuseStep 1841561 = 1381171) B1381171
theorem B1227179 : Blo 1226431 1227179 := bstep (se 1 (by rfl) ⟨920384, by rfl⟩ : syracuseStep 1227179 = 1840769) B1840769
theorem B1227191 : Blo 1226431 1227191 := bstep (se 1 (by rfl) ⟨920393, by rfl⟩ : syracuseStep 1227191 = 1840787) B1840787
theorem B1227211 : Blo 1226431 1227211 := bstep (se 1 (by rfl) ⟨920408, by rfl⟩ : syracuseStep 1227211 = 1840817) B1840817
theorem B1227223 : Blo 1226431 1227223 := bstep (se 1 (by rfl) ⟨920417, by rfl⟩ : syracuseStep 1227223 = 1840835) B1840835
theorem B2071001 : Blo 1226431 2071001 := bstep (se 2 (by rfl) ⟨776625, by rfl⟩ : syracuseStep 2071001 = 1553251) B1553251
theorem B4659677 : Blo 1226431 4659677 := bstep (se 3 (by rfl) ⟨873689, by rfl⟩ : syracuseStep 4659677 = 1747379) B1747379
theorem B4143581 : Blo 1226431 4143581 := bstep (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) B1553843
theorem B1227243 : Blo 1226431 1227243 := bstep (se 1 (by rfl) ⟨920432, by rfl⟩ : syracuseStep 1227243 = 1840865) B1840865
theorem B1227255 : Blo 1226431 1227255 := bstep (se 1 (by rfl) ⟨920441, by rfl⟩ : syracuseStep 1227255 = 1840883) B1840883
theorem B1227275 : Blo 1226431 1227275 := bstep (se 1 (by rfl) ⟨920456, by rfl⟩ : syracuseStep 1227275 = 1840913) B1840913
theorem B1841675 : Blo 1226431 1841675 := bstep (se 1 (by rfl) ⟨1381256, by rfl⟩ : syracuseStep 1841675 = 2762513) B2762513
theorem B2947607 : Blo 1226431 2947607 := bstep (se 1 (by rfl) ⟨2210705, by rfl⟩ : syracuseStep 2947607 = 4421411) B4421411
theorem B1227287 : Blo 1226431 1227287 := bstep (se 1 (by rfl) ⟨920465, by rfl⟩ : syracuseStep 1227287 = 1840931) B1840931
theorem B1841687 : Blo 1226431 1841687 := bstep (se 1 (by rfl) ⟨1381265, by rfl⟩ : syracuseStep 1841687 = 2762531) B2762531
theorem B1227307 : Blo 1226431 1227307 := bstep (se 1 (by rfl) ⟨920480, by rfl⟩ : syracuseStep 1227307 = 1840961) B1840961
theorem B1227319 : Blo 1226431 1227319 := bstep (se 1 (by rfl) ⟨920489, by rfl⟩ : syracuseStep 1227319 = 1840979) B1840979
theorem B5241419 : Blo 1226431 5241419 := bstep (se 1 (by rfl) ⟨3931064, by rfl⟩ : syracuseStep 5241419 = 7862129) B7862129
theorem B1227339 : Blo 1226431 1227339 := bstep (se 1 (by rfl) ⟨920504, by rfl⟩ : syracuseStep 1227339 = 1841009) B1841009
theorem B1227351 : Blo 1226431 1227351 := bstep (se 1 (by rfl) ⟨920513, by rfl⟩ : syracuseStep 1227351 = 1841027) B1841027
theorem B2071129 : Blo 1226431 2071129 := bstep (se 2 (by rfl) ⟨776673, by rfl⟩ : syracuseStep 2071129 = 1553347) B1553347
theorem B1841753 : Blo 1226431 1841753 := bstep (se 2 (by rfl) ⟨690657, by rfl⟩ : syracuseStep 1841753 = 1381315) B1381315
theorem B1227371 : Blo 1226431 1227371 := bstep (se 1 (by rfl) ⟨920528, by rfl⟩ : syracuseStep 1227371 = 1841057) B1841057
theorem B2620019 : Blo 1226431 2620019 := bstep (se 1 (by rfl) ⟨1965014, by rfl⟩ : syracuseStep 2620019 = 3930029) B3930029
theorem B1227383 : Blo 1226431 1227383 := bstep (se 1 (by rfl) ⟨920537, by rfl⟩ : syracuseStep 1227383 = 1841075) B1841075
theorem B6986371 : Blo 1226431 6986371 := bstep (se 1 (by rfl) ⟨5239778, by rfl⟩ : syracuseStep 6986371 = 10479557) B10479557
theorem B1227403 : Blo 1226431 1227403 := bstep (se 1 (by rfl) ⟨920552, by rfl⟩ : syracuseStep 1227403 = 1841105) B1841105
theorem B1227415 : Blo 1226431 1227415 := bstep (se 1 (by rfl) ⟨920561, by rfl⟩ : syracuseStep 1227415 = 1841123) B1841123
theorem B1227435 : Blo 1226431 1227435 := bstep (se 1 (by rfl) ⟨920576, by rfl⟩ : syracuseStep 1227435 = 1841153) B1841153
theorem B1227447 : Blo 1226431 1227447 := bstep (se 1 (by rfl) ⟨920585, by rfl⟩ : syracuseStep 1227447 = 1841171) B1841171
theorem B3316427 : Blo 1226431 3316427 := bstep (se 1 (by rfl) ⟨2487320, by rfl⟩ : syracuseStep 3316427 = 4974641) B4974641
theorem B1227467 : Blo 1226431 1227467 := bstep (se 1 (by rfl) ⟨920600, by rfl⟩ : syracuseStep 1227467 = 1841201) B1841201
theorem B1841867 : Blo 1226431 1841867 := bstep (se 1 (by rfl) ⟨1381400, by rfl⟩ : syracuseStep 1841867 = 2762801) B2762801
theorem B1227479 : Blo 1226431 1227479 := bstep (se 1 (by rfl) ⟨920609, by rfl⟩ : syracuseStep 1227479 = 1841219) B1841219
theorem B1841879 : Blo 1226431 1841879 := bstep (se 1 (by rfl) ⟨1381409, by rfl⟩ : syracuseStep 1841879 = 2762819) B2762819
theorem B1227499 : Blo 1226431 1227499 := bstep (se 1 (by rfl) ⟨920624, by rfl⟩ : syracuseStep 1227499 = 1841249) B1841249
theorem B1227511 : Blo 1226431 1227511 := bstep (se 1 (by rfl) ⟨920633, by rfl⟩ : syracuseStep 1227511 = 1841267) B1841267
theorem B1227531 : Blo 1226431 1227531 := bstep (se 1 (by rfl) ⟨920648, by rfl⟩ : syracuseStep 1227531 = 1841297) B1841297
theorem B1227543 : Blo 1226431 1227543 := bstep (se 1 (by rfl) ⟨920657, by rfl⟩ : syracuseStep 1227543 = 1841315) B1841315
theorem B1841945 : Blo 1226431 1841945 := bstep (se 2 (by rfl) ⟨690729, by rfl⟩ : syracuseStep 1841945 = 1381459) B1381459
theorem B1227563 : Blo 1226431 1227563 := bstep (se 1 (by rfl) ⟨920672, by rfl⟩ : syracuseStep 1227563 = 1841345) B1841345
theorem B1227575 : Blo 1226431 1227575 := bstep (se 1 (by rfl) ⟨920681, by rfl⟩ : syracuseStep 1227575 = 1841363) B1841363
theorem B2759489 : Blo 1226431 2759489 := bstep (se 2 (by rfl) ⟨1034808, by rfl⟩ : syracuseStep 2759489 = 2069617) B2069617
theorem B1227595 : Blo 1226431 1227595 := bstep (se 1 (by rfl) ⟨920696, by rfl⟩ : syracuseStep 1227595 = 1841393) B1841393
theorem B1227607 : Blo 1226431 1227607 := bstep (se 1 (by rfl) ⟨920705, by rfl⟩ : syracuseStep 1227607 = 1841411) B1841411
theorem B1227627 : Blo 1226431 1227627 := bstep (se 1 (by rfl) ⟨920720, by rfl⟩ : syracuseStep 1227627 = 1841441) B1841441
theorem B1227639 : Blo 1226431 1227639 := bstep (se 1 (by rfl) ⟨920729, by rfl⟩ : syracuseStep 1227639 = 1841459) B1841459
theorem B2210699 : Blo 1226431 2210699 := bstep (se 1 (by rfl) ⟨1658024, by rfl⟩ : syracuseStep 2210699 = 3316049) B3316049
theorem B1227659 : Blo 1226431 1227659 := bstep (se 1 (by rfl) ⟨920744, by rfl⟩ : syracuseStep 1227659 = 1841489) B1841489
theorem B1842059 : Blo 1226431 1842059 := bstep (se 1 (by rfl) ⟨1381544, by rfl⟩ : syracuseStep 1842059 = 2763089) B2763089
theorem B1227671 : Blo 1226431 1227671 := bstep (se 1 (by rfl) ⟨920753, by rfl⟩ : syracuseStep 1227671 = 1841507) B1841507
theorem B1842071 : Blo 1226431 1842071 := bstep (se 1 (by rfl) ⟨1381553, by rfl⟩ : syracuseStep 1842071 = 2763107) B2763107
theorem B1227691 : Blo 1226431 1227691 := bstep (se 1 (by rfl) ⟨920768, by rfl⟩ : syracuseStep 1227691 = 1841537) B1841537
theorem B1227703 : Blo 1226431 1227703 := bstep (se 1 (by rfl) ⟨920777, by rfl⟩ : syracuseStep 1227703 = 1841555) B1841555
theorem B4422593 : Blo 1226431 4422593 := bstep (se 2 (by rfl) ⟨1658472, by rfl⟩ : syracuseStep 4422593 = 3316945) B3316945
theorem B1227723 : Blo 1226431 1227723 := bstep (se 1 (by rfl) ⟨920792, by rfl⟩ : syracuseStep 1227723 = 1841585) B1841585
theorem B1227735 : Blo 1226431 1227735 := bstep (se 1 (by rfl) ⟨920801, by rfl⟩ : syracuseStep 1227735 = 1841603) B1841603
theorem B7863257 : Blo 1226431 7863257 := bstep (se 2 (by rfl) ⟨2948721, by rfl⟩ : syracuseStep 7863257 = 5897443) B5897443
theorem B1842137 : Blo 1226431 1842137 := bstep (se 2 (by rfl) ⟨690801, by rfl⟩ : syracuseStep 1842137 = 1381603) B1381603
theorem B1227755 : Blo 1226431 1227755 := bstep (se 1 (by rfl) ⟨920816, by rfl⟩ : syracuseStep 1227755 = 1841633) B1841633
theorem B1227767 : Blo 1226431 1227767 := bstep (se 1 (by rfl) ⟨920825, by rfl⟩ : syracuseStep 1227767 = 1841651) B1841651
theorem B1227787 : Blo 1226431 1227787 := bstep (se 1 (by rfl) ⟨920840, by rfl⟩ : syracuseStep 1227787 = 1841681) B1841681
theorem B1227799 : Blo 1226431 1227799 := bstep (se 1 (by rfl) ⟨920849, by rfl⟩ : syracuseStep 1227799 = 1841699) B1841699
theorem B2759705 : Blo 1226431 2759705 := bstep (se 2 (by rfl) ⟨1034889, by rfl⟩ : syracuseStep 2759705 = 2069779) B2069779
theorem B1227819 : Blo 1226431 1227819 := bstep (se 1 (by rfl) ⟨920864, by rfl⟩ : syracuseStep 1227819 = 1841729) B1841729
theorem B6216749 : Blo 1226431 6216749 := bstep (se 3 (by rfl) ⟨1165640, by rfl⟩ : syracuseStep 6216749 = 2331281) B2331281
theorem B1227831 : Blo 1226431 1227831 := bstep (se 1 (by rfl) ⟨920873, by rfl⟩ : syracuseStep 1227831 = 1841747) B1841747
theorem B1473611 : Blo 1226431 1473611 := bstep (se 1 (by rfl) ⟨1105208, by rfl⟩ : syracuseStep 1473611 = 2210417) B2210417
theorem B1227851 : Blo 1226431 1227851 := bstep (se 1 (by rfl) ⟨920888, by rfl⟩ : syracuseStep 1227851 = 1841777) B1841777
theorem B1842251 : Blo 1226431 1842251 := bstep (se 1 (by rfl) ⟨1381688, by rfl⟩ : syracuseStep 1842251 = 2763377) B2763377
theorem B1227863 : Blo 1226431 1227863 := bstep (se 1 (by rfl) ⟨920897, by rfl⟩ : syracuseStep 1227863 = 1841795) B1841795
theorem B1842263 : Blo 1226431 1842263 := bstep (se 1 (by rfl) ⟨1381697, by rfl⟩ : syracuseStep 1842263 = 2763395) B2763395
theorem B2620505 : Blo 1226431 2620505 := bstep (se 2 (by rfl) ⟨982689, by rfl⟩ : syracuseStep 2620505 = 1965379) B1965379
theorem B1227883 : Blo 1226431 1227883 := bstep (se 1 (by rfl) ⟨920912, by rfl⟩ : syracuseStep 1227883 = 1841825) B1841825
theorem B2759795 : Blo 1226431 2759795 := bstep (se 1 (by rfl) ⟨2069846, by rfl⟩ : syracuseStep 2759795 = 4139693) B4139693
theorem B1227895 : Blo 1226431 1227895 := bstep (se 1 (by rfl) ⟨920921, by rfl⟩ : syracuseStep 1227895 = 1841843) B1841843
theorem B1227915 : Blo 1226431 1227915 := bstep (se 1 (by rfl) ⟨920936, by rfl⟩ : syracuseStep 1227915 = 1841873) B1841873
theorem B2759831 : Blo 1226431 2759831 := bstep (se 1 (by rfl) ⟨2069873, by rfl⟩ : syracuseStep 2759831 = 4139747) B4139747
theorem B4660375 : Blo 1226431 4660375 := bstep (se 1 (by rfl) ⟨3495281, by rfl⟩ : syracuseStep 4660375 = 6990563) B6990563
theorem B2071703 : Blo 1226431 2071703 := bstep (se 1 (by rfl) ⟨1553777, by rfl⟩ : syracuseStep 2071703 = 3107555) B3107555
theorem B1227927 : Blo 1226431 1227927 := bstep (se 1 (by rfl) ⟨920945, by rfl⟩ : syracuseStep 1227927 = 1841891) B1841891
theorem B1842329 : Blo 1226431 1842329 := bstep (se 2 (by rfl) ⟨690873, by rfl⟩ : syracuseStep 1842329 = 1381747) B1381747
theorem B1227947 : Blo 1226431 1227947 := bstep (se 1 (by rfl) ⟨920960, by rfl⟩ : syracuseStep 1227947 = 1841921) B1841921
theorem B1227959 : Blo 1226431 1227959 := bstep (se 1 (by rfl) ⟨920969, by rfl⟩ : syracuseStep 1227959 = 1841939) B1841939
theorem B1227979 : Blo 1226431 1227979 := bstep (se 1 (by rfl) ⟨920984, by rfl⟩ : syracuseStep 1227979 = 1841969) B1841969
theorem B1227991 : Blo 1226431 1227991 := bstep (se 1 (by rfl) ⟨920993, by rfl⟩ : syracuseStep 1227991 = 1841987) B1841987
theorem B1228011 : Blo 1226431 1228011 := bstep (se 1 (by rfl) ⟨921008, by rfl⟩ : syracuseStep 1228011 = 1842017) B1842017
theorem B1228023 : Blo 1226431 1228023 := bstep (se 1 (by rfl) ⟨921017, by rfl⟩ : syracuseStep 1228023 = 1842035) B1842035
theorem B1228043 : Blo 1226431 1228043 := bstep (se 1 (by rfl) ⟨921032, by rfl⟩ : syracuseStep 1228043 = 1842065) B1842065
theorem B1842443 : Blo 1226431 1842443 := bstep (se 1 (by rfl) ⟨1381832, by rfl⟩ : syracuseStep 1842443 = 2763665) B2763665
theorem B2071831 : Blo 1226431 2071831 := bstep (se 1 (by rfl) ⟨1553873, by rfl⟩ : syracuseStep 2071831 = 3107747) B3107747
theorem B1228055 : Blo 1226431 1228055 := bstep (se 1 (by rfl) ⟨921041, by rfl⟩ : syracuseStep 1228055 = 1842083) B1842083
theorem B1842455 : Blo 1226431 1842455 := bstep (se 1 (by rfl) ⟨1381841, by rfl⟩ : syracuseStep 1842455 = 2763683) B2763683
theorem B1228075 : Blo 1226431 1228075 := bstep (se 1 (by rfl) ⟨921056, by rfl⟩ : syracuseStep 1228075 = 1842113) B1842113
theorem B1228087 : Blo 1226431 1228087 := bstep (se 1 (by rfl) ⟨921065, by rfl⟩ : syracuseStep 1228087 = 1842131) B1842131
theorem B2760011 : Blo 1226431 2760011 := bstep (se 1 (by rfl) ⟨2070008, by rfl⟩ : syracuseStep 2760011 = 4140017) B4140017
theorem B1228107 : Blo 1226431 1228107 := bstep (se 1 (by rfl) ⟨921080, by rfl⟩ : syracuseStep 1228107 = 1842161) B1842161
theorem B1228119 : Blo 1226431 1228119 := bstep (se 1 (by rfl) ⟨921089, by rfl⟩ : syracuseStep 1228119 = 1842179) B1842179
theorem B1842521 : Blo 1226431 1842521 := bstep (se 2 (by rfl) ⟨690945, by rfl⟩ : syracuseStep 1842521 = 1381891) B1381891
theorem B1228139 : Blo 1226431 1228139 := bstep (se 1 (by rfl) ⟨921104, by rfl⟩ : syracuseStep 1228139 = 1842209) B1842209
theorem B1228151 : Blo 1226431 1228151 := bstep (se 1 (by rfl) ⟨921113, by rfl⟩ : syracuseStep 1228151 = 1842227) B1842227
theorem B2760065 : Blo 1226431 2760065 := bstep (se 2 (by rfl) ⟨1035024, by rfl⟩ : syracuseStep 2760065 = 2070049) B2070049
theorem B1228171 : Blo 1226431 1228171 := bstep (se 1 (by rfl) ⟨921128, by rfl⟩ : syracuseStep 1228171 = 1842257) B1842257
theorem B1228183 : Blo 1226431 1228183 := bstep (se 1 (by rfl) ⟨921137, by rfl⟩ : syracuseStep 1228183 = 1842275) B1842275
theorem B1228203 : Blo 1226431 1228203 := bstep (se 1 (by rfl) ⟨921152, by rfl⟩ : syracuseStep 1228203 = 1842305) B1842305
theorem B1228215 : Blo 1226431 1228215 := bstep (se 1 (by rfl) ⟨921161, by rfl⟩ : syracuseStep 1228215 = 1842323) B1842323
theorem B1228235 : Blo 1226431 1228235 := bstep (se 1 (by rfl) ⟨921176, by rfl⟩ : syracuseStep 1228235 = 1842353) B1842353
theorem B1842635 : Blo 1226431 1842635 := bstep (se 1 (by rfl) ⟨1381976, by rfl⟩ : syracuseStep 1842635 = 2763953) B2763953
theorem B1228247 : Blo 1226431 1228247 := bstep (se 1 (by rfl) ⟨921185, by rfl⟩ : syracuseStep 1228247 = 1842371) B1842371
theorem B1842647 : Blo 1226431 1842647 := bstep (se 1 (by rfl) ⟨1381985, by rfl⟩ : syracuseStep 1842647 = 2763971) B2763971
theorem B1228267 : Blo 1226431 1228267 := bstep (se 1 (by rfl) ⟨921200, by rfl⟩ : syracuseStep 1228267 = 1842401) B1842401
theorem B1228279 : Blo 1226431 1228279 := bstep (se 1 (by rfl) ⟨921209, by rfl⟩ : syracuseStep 1228279 = 1842419) B1842419
theorem B1228299 : Blo 1226431 1228299 := bstep (se 1 (by rfl) ⟨921224, by rfl⟩ : syracuseStep 1228299 = 1842449) B1842449
theorem B1228311 : Blo 1226431 1228311 := bstep (se 1 (by rfl) ⟨921233, by rfl⟩ : syracuseStep 1228311 = 1842467) B1842467
theorem B15736355 : Blo 1226431 15736355 := bstep (se 1 (by rfl) ⟨11802266, by rfl⟩ : syracuseStep 15736355 = 23604533) B23604533
theorem B1228331 : Blo 1226431 1228331 := bstep (se 1 (by rfl) ⟨921248, by rfl⟩ : syracuseStep 1228331 = 1842497) B1842497
theorem B1228343 : Blo 1226431 1228343 := bstep (se 1 (by rfl) ⟨921257, by rfl⟩ : syracuseStep 1228343 = 1842515) B1842515
theorem B6987329 : Blo 1226431 6987329 := bstep (se 2 (by rfl) ⟨2620248, by rfl⟩ : syracuseStep 6987329 = 5240497) B5240497
theorem B4144715 : Blo 1226431 4144715 := bstep (se 1 (by rfl) ⟨3108536, by rfl⟩ : syracuseStep 4144715 = 6217073) B6217073
theorem B1228363 : Blo 1226431 1228363 := bstep (se 1 (by rfl) ⟨921272, by rfl⟩ : syracuseStep 1228363 = 1842545) B1842545
theorem B1228375 : Blo 1226431 1228375 := bstep (se 1 (by rfl) ⟨921281, by rfl⟩ : syracuseStep 1228375 = 1842563) B1842563
theorem B2760281 : Blo 1226431 2760281 := bstep (se 2 (by rfl) ⟨1035105, by rfl⟩ : syracuseStep 2760281 = 2070211) B2070211
theorem B7462493 : Blo 1226431 7462493 := bstep (se 3 (by rfl) ⟨1399217, by rfl⟩ : syracuseStep 7462493 = 2798435) B2798435
theorem B1228395 : Blo 1226431 1228395 := bstep (se 1 (by rfl) ⟨921296, by rfl⟩ : syracuseStep 1228395 = 1842593) B1842593
theorem B1228407 : Blo 1226431 1228407 := bstep (se 1 (by rfl) ⟨921305, by rfl⟩ : syracuseStep 1228407 = 1842611) B1842611
theorem B1228427 : Blo 1226431 1228427 := bstep (se 1 (by rfl) ⟨921320, by rfl⟩ : syracuseStep 1228427 = 1842641) B1842641
theorem B2760371 : Blo 1226431 2760371 := bstep (se 1 (by rfl) ⟨2070278, by rfl⟩ : syracuseStep 2760371 = 4140557) B4140557
theorem B3497651 : Blo 1226431 3497651 := bstep (se 1 (by rfl) ⟨2623238, by rfl⟩ : syracuseStep 3497651 = 5246477) B5246477
theorem B1310423 : Blo 1226431 1310423 := bstep (se 1 (by rfl) ⟨982817, by rfl⟩ : syracuseStep 1310423 = 1965635) B1965635
theorem B2760407 : Blo 1226431 2760407 := bstep (se 1 (by rfl) ⟨2070305, by rfl⟩ : syracuseStep 2760407 = 4140611) B4140611
theorem B6209297 : Blo 1226431 6209297 := bstep (se 2 (by rfl) ⟨2328486, by rfl⟩ : syracuseStep 6209297 = 4656973) B4656973
theorem B7470913 : Blo 1226431 7470913 := bstep (se 2 (by rfl) ⟨2801592, by rfl⟩ : syracuseStep 7470913 = 5603185) B5603185
theorem B5898059 : Blo 1226431 5898059 := bstep (se 1 (by rfl) ⟨4423544, by rfl⟩ : syracuseStep 5898059 = 8847089) B8847089
theorem B4144985 : Blo 1226431 4144985 := bstep (se 2 (by rfl) ⟨1554369, by rfl⟩ : syracuseStep 4144985 = 3108739) B3108739
theorem B4423517 : Blo 1226431 4423517 := bstep (se 3 (by rfl) ⟨829409, by rfl⟩ : syracuseStep 4423517 = 1658819) B1658819
theorem B2760587 : Blo 1226431 2760587 := bstep (se 1 (by rfl) ⟨2070440, by rfl⟩ : syracuseStep 2760587 = 4140881) B4140881
theorem B2072459 : Blo 1226431 2072459 := bstep (se 1 (by rfl) ⟨1554344, by rfl⟩ : syracuseStep 2072459 = 3108689) B3108689
theorem B1245079 : Blo 1226431 1245079 := bstep (se 1 (by rfl) ⟨933809, by rfl⟩ : syracuseStep 1245079 = 1867619) B1867619
theorem B3497879 : Blo 1226431 3497879 := bstep (se 1 (by rfl) ⟨2623409, by rfl⟩ : syracuseStep 3497879 = 5246819) B5246819
theorem B4661165 : Blo 1226431 4661165 := bstep (se 3 (by rfl) ⟨873968, by rfl⟩ : syracuseStep 4661165 = 1747937) B1747937
theorem B6209459 : Blo 1226431 6209459 := bstep (se 1 (by rfl) ⟨4657094, by rfl⟩ : syracuseStep 6209459 = 9314189) B9314189
theorem B2760641 : Blo 1226431 2760641 := bstep (se 2 (by rfl) ⟨1035240, by rfl⟩ : syracuseStep 2760641 = 2070481) B2070481
theorem B2949067 : Blo 1226431 2949067 := bstep (se 1 (by rfl) ⟨2211800, by rfl⟩ : syracuseStep 2949067 = 4423601) B4423601
theorem B3104801 : Blo 1226431 3104801 := bstep (se 2 (by rfl) ⟨1164300, by rfl⟩ : syracuseStep 3104801 = 2328601) B2328601
theorem B4423747 : Blo 1226431 4423747 := bstep (se 1 (by rfl) ⟨3317810, by rfl⟩ : syracuseStep 4423747 = 6635621) B6635621
theorem B2072695 : Blo 1226431 2072695 := bstep (se 1 (by rfl) ⟨1554521, by rfl⟩ : syracuseStep 2072695 = 3109043) B3109043
theorem B2760839 : Blo 1226431 2760839 := bstep (se 1 (by rfl) ⟨2070629, by rfl⟩ : syracuseStep 2760839 = 4141259) B4141259
theorem B2761019 : Blo 1226431 2761019 := bstep (se 1 (by rfl) ⟨2070764, by rfl⟩ : syracuseStep 2761019 = 4141529) B4141529
theorem B2072891 : Blo 1226431 2072891 := bstep (se 1 (by rfl) ⟨1554668, by rfl⟩ : syracuseStep 2072891 = 3109337) B3109337
theorem B4424051 : Blo 1226431 4424051 := bstep (se 1 (by rfl) ⟨3318038, by rfl⟩ : syracuseStep 4424051 = 6636077) B6636077
theorem B4661651 : Blo 1226431 4661651 := bstep (se 1 (by rfl) ⟨3496238, by rfl⟩ : syracuseStep 4661651 = 6992477) B6992477
theorem B6209945 : Blo 1226431 6209945 := bstep (se 2 (by rfl) ⟨2328729, by rfl⟩ : syracuseStep 6209945 = 4657459) B4657459
theorem B2949529 : Blo 1226431 2949529 := bstep (se 2 (by rfl) ⟨1106073, by rfl⟩ : syracuseStep 2949529 = 2212147) B2212147
theorem B2761145 : Blo 1226431 2761145 := bstep (se 2 (by rfl) ⟨1035429, by rfl⟩ : syracuseStep 2761145 = 2070859) B2070859
theorem B9322937 : Blo 1226431 9322937 := bstep (se 2 (by rfl) ⟨3496101, by rfl⟩ : syracuseStep 9322937 = 6992203) B6992203
theorem B7463447 : Blo 1226431 7463447 := bstep (se 1 (by rfl) ⟨5597585, by rfl⟩ : syracuseStep 7463447 = 11195171) B11195171
theorem B6988355 : Blo 1226431 6988355 := bstep (se 1 (by rfl) ⟨5241266, by rfl⟩ : syracuseStep 6988355 = 10482533) B10482533
theorem B6636269 : Blo 1226431 6636269 := bstep (se 3 (by rfl) ⟨1244300, by rfl⟩ : syracuseStep 6636269 = 2488601) B2488601
theorem B10486529 : Blo 1226431 10486529 := bstep (se 2 (by rfl) ⟨3932448, by rfl⟩ : syracuseStep 10486529 = 7864897) B7864897
theorem B2761487 : Blo 1226431 2761487 := bstep (se 1 (by rfl) ⟨2071115, by rfl⟩ : syracuseStep 2761487 = 4142231) B4142231
theorem B2761505 : Blo 1226431 2761505 := bstep (se 2 (by rfl) ⟨1035564, by rfl⟩ : syracuseStep 2761505 = 2071129) B2071129
theorem B9446195 : Blo 1226431 9446195 := bstep (se 1 (by rfl) ⟨7084646, by rfl⟩ : syracuseStep 9446195 = 14169293) B14169293
theorem B1311547 : Blo 1226431 1311547 := bstep (se 1 (by rfl) ⟨983660, by rfl⟩ : syracuseStep 1311547 = 1967321) B1967321
theorem B9315161 : Blo 1226431 9315161 := bstep (se 2 (by rfl) ⟨3493185, by rfl⟩ : syracuseStep 9315161 = 6986371) B6986371
theorem B2950145 : Blo 1226431 2950145 := bstep (se 2 (by rfl) ⟨1106304, by rfl⟩ : syracuseStep 2950145 = 2212609) B2212609
theorem B1475591 : Blo 1226431 1475591 := bstep (se 1 (by rfl) ⟨1106693, by rfl⟩ : syracuseStep 1475591 = 2213387) B2213387
theorem B3105803 : Blo 1226431 3105803 := bstep (se 1 (by rfl) ⟨2329352, by rfl⟩ : syracuseStep 3105803 = 4658705) B4658705
theorem B2761847 : Blo 1226431 2761847 := bstep (se 1 (by rfl) ⟨2071385, by rfl⟩ : syracuseStep 2761847 = 4142771) B4142771
theorem B4424975 : Blo 1226431 4424975 := bstep (se 1 (by rfl) ⟨3318731, by rfl⟩ : syracuseStep 4424975 = 6637463) B6637463
theorem B2762027 : Blo 1226431 2762027 := bstep (se 1 (by rfl) ⟨2071520, by rfl⟩ : syracuseStep 2762027 = 4143041) B4143041
theorem B4195901 : Blo 1226431 4195901 := bstep (se 3 (by rfl) ⟨786731, by rfl⟩ : syracuseStep 4195901 = 1573463) B1573463
theorem B3106451 : Blo 1226431 3106451 := bstep (se 1 (by rfl) ⟨2329838, by rfl⟩ : syracuseStep 3106451 = 4659677) B4659677
theorem B2762387 : Blo 1226431 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B2762441 : Blo 1226431 2762441 := bstep (se 2 (by rfl) ⟨1035915, by rfl⟩ : syracuseStep 2762441 = 2071831) B2071831
theorem B1746679 : Blo 1226431 1746679 := bstep (se 1 (by rfl) ⟨1310009, by rfl⟩ : syracuseStep 1746679 = 2620019) B2620019
theorem B2950913 : Blo 1226431 2950913 := bstep (se 2 (by rfl) ⟨1106592, by rfl⟩ : syracuseStep 2950913 = 2213185) B2213185
theorem B2328335 : Blo 1226431 2328335 := bstep (se 1 (by rfl) ⟨1746251, by rfl⟩ : syracuseStep 2328335 = 3492503) B3492503
theorem B9316133 : Blo 1226431 9316133 := bstep (se 4 (by rfl) ⟨873387, by rfl⟩ : syracuseStep 9316133 = 1746775) B1746775
theorem B2623367 : Blo 1226431 2623367 := bstep (se 1 (by rfl) ⟨1967525, by rfl⟩ : syracuseStep 2623367 = 3935051) B3935051
theorem B3106745 : Blo 1226431 3106745 := bstep (se 2 (by rfl) ⟨1165029, by rfl⟩ : syracuseStep 3106745 = 2330059) B2330059
theorem B1747003 : Blo 1226431 1747003 := bstep (se 1 (by rfl) ⟨1310252, by rfl⟩ : syracuseStep 1747003 = 2620505) B2620505
theorem B3934295 : Blo 1226431 3934295 := bstep (se 1 (by rfl) ⟨2950721, by rfl⟩ : syracuseStep 3934295 = 5901443) B5901443
theorem B11798729 : Blo 1226431 11798729 := bstep (se 2 (by rfl) ⟨4424523, by rfl⟩ : syracuseStep 11798729 = 8849047) B8849047
theorem B13977845 : Blo 1226431 13977845 := bstep (se 5 (by rfl) ⟨655211, by rfl⟩ : syracuseStep 13977845 = 1310423) B1310423
theorem B2763143 : Blo 1226431 2763143 := bstep (se 1 (by rfl) ⟨2072357, by rfl⟩ : syracuseStep 2763143 = 4144715) B4144715
theorem B4974995 : Blo 1226431 4974995 := bstep (se 1 (by rfl) ⟨3731246, by rfl⟩ : syracuseStep 4974995 = 7462493) B7462493
theorem B7866845 : Blo 1226431 7866845 := bstep (se 3 (by rfl) ⟨1475033, by rfl⟩ : syracuseStep 7866845 = 2950067) B2950067
theorem B4139531 : Blo 1226431 4139531 := bstep (se 1 (by rfl) ⟨3104648, by rfl⟩ : syracuseStep 4139531 = 6209297) B6209297
theorem B11192861 : Blo 1226431 11192861 := bstep (se 3 (by rfl) ⟨2098661, by rfl⟩ : syracuseStep 11192861 = 4197323) B4197323
theorem B4426283 : Blo 1226431 4426283 := bstep (se 1 (by rfl) ⟨3319712, by rfl⟩ : syracuseStep 4426283 = 6639425) B6639425
theorem B2763323 : Blo 1226431 2763323 := bstep (se 1 (by rfl) ⟨2072492, by rfl⟩ : syracuseStep 2763323 = 4144985) B4144985
theorem B3983959 : Blo 1226431 3983959 := bstep (se 1 (by rfl) ⟨2987969, by rfl⟩ : syracuseStep 3983959 = 5975939) B5975939
theorem B3107443 : Blo 1226431 3107443 := bstep (se 1 (by rfl) ⟨2330582, by rfl⟩ : syracuseStep 3107443 = 4661165) B4661165
theorem B4139639 : Blo 1226431 4139639 := bstep (se 1 (by rfl) ⟨3104729, by rfl⟩ : syracuseStep 4139639 = 6209459) B6209459
theorem B2763449 : Blo 1226431 2763449 := bstep (se 2 (by rfl) ⟨1036293, by rfl⟩ : syracuseStep 2763449 = 2072587) B2072587
theorem B3107585 : Blo 1226431 3107585 := bstep (se 2 (by rfl) ⟨1165344, by rfl⟩ : syracuseStep 3107585 = 2330689) B2330689
theorem B10095475 : Blo 1226431 10095475 := bstep (se 1 (by rfl) ⟨7571606, by rfl⟩ : syracuseStep 10095475 = 15143213) B15143213
theorem B6384529 : Blo 1226431 6384529 := bstep (se 2 (by rfl) ⟨2394198, by rfl⟩ : syracuseStep 6384529 = 4788397) B4788397
theorem B6990745 : Blo 1226431 6990745 := bstep (se 2 (by rfl) ⟨2621529, by rfl⟩ : syracuseStep 6990745 = 5243059) B5243059
theorem B6212537 : Blo 1226431 6212537 := bstep (se 2 (by rfl) ⟨2329701, by rfl⟩ : syracuseStep 6212537 = 4659403) B4659403
theorem B2763791 : Blo 1226431 2763791 := bstep (se 1 (by rfl) ⟨2072843, by rfl⟩ : syracuseStep 2763791 = 4145687) B4145687
theorem B2763809 : Blo 1226431 2763809 := bstep (se 2 (by rfl) ⟨1036428, by rfl⟩ : syracuseStep 2763809 = 2072857) B2072857
theorem B4140233 : Blo 1226431 4140233 := bstep (se 2 (by rfl) ⟨1552587, by rfl⟩ : syracuseStep 4140233 = 3105175) B3105175
theorem B3108041 : Blo 1226431 3108041 := bstep (se 2 (by rfl) ⟨1165515, by rfl⟩ : syracuseStep 3108041 = 2331031) B2331031
theorem B23317741 : Blo 1226431 23317741 := bstep (se 3 (by rfl) ⟨4372076, by rfl⟩ : syracuseStep 23317741 = 8744153) B8744153
theorem B2362657 : Blo 1226431 2362657 := bstep (se 2 (by rfl) ⟨885996, by rfl⟩ : syracuseStep 2362657 = 1771993) B1771993
theorem B8850721 : Blo 1226431 8850721 := bstep (se 2 (by rfl) ⟨3319020, by rfl⟩ : syracuseStep 8850721 = 6638041) B6638041
theorem B8391995 : Blo 1226431 8391995 := bstep (se 1 (by rfl) ⟨6293996, by rfl⟩ : syracuseStep 8391995 = 12587993) B12587993
theorem B2329975 : Blo 1226431 2329975 := bstep (se 1 (by rfl) ⟨1747481, by rfl⟩ : syracuseStep 2329975 = 3494963) B3494963
theorem B5041693 : Blo 1226431 5041693 := bstep (se 3 (by rfl) ⟨945317, by rfl⟩ : syracuseStep 5041693 = 1890635) B1890635
theorem B3108395 : Blo 1226431 3108395 := bstep (se 1 (by rfl) ⟨2331296, by rfl⟩ : syracuseStep 3108395 = 4662593) B4662593
theorem B43069027 : Blo 1226431 43069027 := bstep (se 1 (by rfl) ⟨32301770, by rfl⟩ : syracuseStep 43069027 = 64603541) B64603541
theorem B1379983 : Blo 1226431 1379983 := bstep (se 1 (by rfl) ⟨1034987, by rfl⟩ : syracuseStep 1379983 = 2069975) B2069975
theorem B2363027 : Blo 1226431 2363027 := bstep (se 1 (by rfl) ⟨1772270, by rfl⟩ : syracuseStep 2363027 = 3544541) B3544541
theorem B4140935 : Blo 1226431 4140935 := bstep (se 1 (by rfl) ⟨3105701, by rfl⟩ : syracuseStep 4140935 = 6211403) B6211403
theorem B2658233 : Blo 1226431 2658233 := bstep (se 2 (by rfl) ⟨996837, by rfl⟩ : syracuseStep 2658233 = 1993675) B1993675
theorem B1552375 : Blo 1226431 1552375 := bstep (se 1 (by rfl) ⟨1164281, by rfl⟩ : syracuseStep 1552375 = 2328563) B2328563
theorem B1380487 : Blo 1226431 1380487 := bstep (se 1 (by rfl) ⟨1035365, by rfl⟩ : syracuseStep 1380487 = 2070731) B2070731
theorem B6213833 : Blo 1226431 6213833 := bstep (se 2 (by rfl) ⟨2330187, by rfl⟩ : syracuseStep 6213833 = 4660375) B4660375
theorem B4141313 : Blo 1226431 4141313 := bstep (se 2 (by rfl) ⟨1552992, by rfl⟩ : syracuseStep 4141313 = 3105985) B3105985
theorem B1552699 : Blo 1226431 1552699 := bstep (se 1 (by rfl) ⟨1164524, by rfl⟩ : syracuseStep 1552699 = 2329049) B2329049
theorem B1380667 : Blo 1226431 1380667 := bstep (se 1 (by rfl) ⟨1035500, by rfl⟩ : syracuseStep 1380667 = 2071001) B2071001
theorem B3494279 : Blo 1226431 3494279 := bstep (se 1 (by rfl) ⟨2620709, by rfl⟩ : syracuseStep 3494279 = 5241419) B5241419
theorem B3109387 : Blo 1226431 3109387 := bstep (se 1 (by rfl) ⟨2332040, by rfl⟩ : syracuseStep 3109387 = 4664081) B4664081
theorem B1839659 : Blo 1226431 1839659 := bstep (se 1 (by rfl) ⟨1379744, by rfl⟩ : syracuseStep 1839659 = 2759489) B2759489
theorem B7565885 : Blo 1226431 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B1839689 : Blo 1226431 1839689 := bstep (se 2 (by rfl) ⟨689883, by rfl⟩ : syracuseStep 1839689 = 1379767) B1379767
theorem B11801189 : Blo 1226431 11801189 := bstep (se 4 (by rfl) ⟨1106361, by rfl⟩ : syracuseStep 11801189 = 2212723) B2212723
theorem B6296237 : Blo 1226431 6296237 := bstep (se 3 (by rfl) ⟨1180544, by rfl⟩ : syracuseStep 6296237 = 2361089) B2361089
theorem B1839803 : Blo 1226431 1839803 := bstep (se 1 (by rfl) ⟨1379852, by rfl⟩ : syracuseStep 1839803 = 2759705) B2759705
theorem B1839863 : Blo 1226431 1839863 := bstep (se 1 (by rfl) ⟨1379897, by rfl⟩ : syracuseStep 1839863 = 2759795) B2759795
theorem B1839887 : Blo 1226431 1839887 := bstep (se 1 (by rfl) ⟨1379915, by rfl⟩ : syracuseStep 1839887 = 2759831) B2759831
theorem B1381135 : Blo 1226431 1381135 := bstep (se 1 (by rfl) ⟨1035851, by rfl⟩ : syracuseStep 1381135 = 2071703) B2071703
theorem B15971107 : Blo 1226431 15971107 := bstep (se 1 (by rfl) ⟨11978330, by rfl⟩ : syracuseStep 15971107 = 23956661) B23956661
theorem B1553195 : Blo 1226431 1553195 := bstep (se 1 (by rfl) ⟨1164896, by rfl⟩ : syracuseStep 1553195 = 2329793) B2329793
theorem B1839929 : Blo 1226431 1839929 := bstep (se 2 (by rfl) ⟨689973, by rfl⟩ : syracuseStep 1839929 = 1379947) B1379947
theorem B6992729 : Blo 1226431 6992729 := bstep (se 2 (by rfl) ⟨2622273, by rfl⟩ : syracuseStep 6992729 = 5244547) B5244547
theorem B1840007 : Blo 1226431 1840007 := bstep (se 1 (by rfl) ⟨1380005, by rfl⟩ : syracuseStep 1840007 = 2760011) B2760011
theorem B10621849 : Blo 1226431 10621849 := bstep (se 2 (by rfl) ⟨3983193, by rfl⟩ : syracuseStep 10621849 = 7966387) B7966387
theorem B11801497 : Blo 1226431 11801497 := bstep (se 2 (by rfl) ⟨4425561, by rfl⟩ : syracuseStep 11801497 = 8851123) B8851123
theorem B1840043 : Blo 1226431 1840043 := bstep (se 1 (by rfl) ⟨1380032, by rfl⟩ : syracuseStep 1840043 = 2760065) B2760065
theorem B1840073 : Blo 1226431 1840073 := bstep (se 2 (by rfl) ⟨690027, by rfl⟩ : syracuseStep 1840073 = 1380055) B1380055
theorem B10490903 : Blo 1226431 10490903 := bstep (se 1 (by rfl) ⟨7868177, by rfl⟩ : syracuseStep 10490903 = 15736355) B15736355
theorem B4658219 : Blo 1226431 4658219 := bstep (se 1 (by rfl) ⟨3493664, by rfl⟩ : syracuseStep 4658219 = 6987329) B6987329
theorem B4142123 : Blo 1226431 4142123 := bstep (se 1 (by rfl) ⟨3106592, by rfl⟩ : syracuseStep 4142123 = 6213185) B6213185
theorem B1840187 : Blo 1226431 1840187 := bstep (se 1 (by rfl) ⟨1380140, by rfl⟩ : syracuseStep 1840187 = 2760281) B2760281
theorem B1840247 : Blo 1226431 1840247 := bstep (se 1 (by rfl) ⟨1380185, by rfl⟩ : syracuseStep 1840247 = 2760371) B2760371
theorem B2331767 : Blo 1226431 2331767 := bstep (se 1 (by rfl) ⟨1748825, by rfl⟩ : syracuseStep 2331767 = 3497651) B3497651
theorem B1840271 : Blo 1226431 1840271 := bstep (se 1 (by rfl) ⟨1380203, by rfl⟩ : syracuseStep 1840271 = 2760407) B2760407
theorem B1840313 : Blo 1226431 1840313 := bstep (se 2 (by rfl) ⟨690117, by rfl⟩ : syracuseStep 1840313 = 1380235) B1380235
theorem B2069705 : Blo 1226431 2069705 := bstep (se 2 (by rfl) ⟨776139, by rfl⟩ : syracuseStep 2069705 = 1552279) B1552279
theorem B1660105 : Blo 1226431 1660105 := bstep (se 2 (by rfl) ⟨622539, by rfl⟩ : syracuseStep 1660105 = 1245079) B1245079
theorem B1840391 : Blo 1226431 1840391 := bstep (se 1 (by rfl) ⟨1380293, by rfl⟩ : syracuseStep 1840391 = 2760587) B2760587
theorem B1553671 : Blo 1226431 1553671 := bstep (se 1 (by rfl) ⟨1165253, by rfl⟩ : syracuseStep 1553671 = 2330507) B2330507
theorem B1381639 : Blo 1226431 1381639 := bstep (se 1 (by rfl) ⟨1036229, by rfl⟩ : syracuseStep 1381639 = 2072459) B2072459
theorem B2331919 : Blo 1226431 2331919 := bstep (se 1 (by rfl) ⟨1748939, by rfl⟩ : syracuseStep 2331919 = 3497879) B3497879
theorem B1865003 : Blo 1226431 1865003 := bstep (se 1 (by rfl) ⟨1398752, by rfl⟩ : syracuseStep 1865003 = 2797505) B2797505
theorem B1840427 : Blo 1226431 1840427 := bstep (se 1 (by rfl) ⟨1380320, by rfl⟩ : syracuseStep 1840427 = 2760641) B2760641
theorem B1840457 : Blo 1226431 1840457 := bstep (se 2 (by rfl) ⟨690171, by rfl⟩ : syracuseStep 1840457 = 1380343) B1380343
theorem B10491281 : Blo 1226431 10491281 := bstep (se 2 (by rfl) ⟨3934230, by rfl⟩ : syracuseStep 10491281 = 7868461) B7868461
theorem B3732889 : Blo 1226431 3732889 := bstep (se 2 (by rfl) ⟨1399833, by rfl⟩ : syracuseStep 3732889 = 2799667) B2799667
theorem B9442745 : Blo 1226431 9442745 := bstep (se 2 (by rfl) ⟨3541029, by rfl⟩ : syracuseStep 9442745 = 7082059) B7082059
theorem B1840571 : Blo 1226431 1840571 := bstep (se 1 (by rfl) ⟨1380428, by rfl⟩ : syracuseStep 1840571 = 2760857) B2760857
theorem B1381819 : Blo 1226431 1381819 := bstep (se 1 (by rfl) ⟨1036364, by rfl⟩ : syracuseStep 1381819 = 2072729) B2072729
theorem B1840631 : Blo 1226431 1840631 := bstep (se 1 (by rfl) ⟨1380473, by rfl⟩ : syracuseStep 1840631 = 2760947) B2760947
theorem B3315215 : Blo 1226431 3315215 := bstep (se 1 (by rfl) ⟨2486411, by rfl⟩ : syracuseStep 3315215 = 4972823) B4972823
theorem B1840655 : Blo 1226431 1840655 := bstep (se 1 (by rfl) ⟨1380491, by rfl⟩ : syracuseStep 1840655 = 2760983) B2760983
theorem B3929629 : Blo 1226431 3929629 := bstep (se 3 (by rfl) ⟨736805, by rfl⟩ : syracuseStep 3929629 = 1473611) B1473611
theorem B1840697 : Blo 1226431 1840697 := bstep (se 2 (by rfl) ⟨690261, by rfl⟩ : syracuseStep 1840697 = 1380523) B1380523
theorem B1840775 : Blo 1226431 1840775 := bstep (se 1 (by rfl) ⟨1380581, by rfl⟩ : syracuseStep 1840775 = 2761163) B2761163
theorem B1840811 : Blo 1226431 1840811 := bstep (se 1 (by rfl) ⟨1380608, by rfl⟩ : syracuseStep 1840811 = 2761217) B2761217
theorem B23025329 : Blo 1226431 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B2946761 : Blo 1226431 2946761 := bstep (se 2 (by rfl) ⟨1105035, by rfl⟩ : syracuseStep 2946761 = 2210071) B2210071
theorem B1840841 : Blo 1226431 1840841 := bstep (se 2 (by rfl) ⟨690315, by rfl⟩ : syracuseStep 1840841 = 1380631) B1380631
theorem B1554167 : Blo 1226431 1554167 := bstep (se 1 (by rfl) ⟨1165625, by rfl⟩ : syracuseStep 1554167 = 2331251) B2331251
theorem B1226503 : Blo 1226431 1226503 := bstep (se 1 (by rfl) ⟨919877, by rfl⟩ : syracuseStep 1226503 = 1839755) B1839755
theorem B1226511 : Blo 1226431 1226511 := bstep (se 1 (by rfl) ⟨919883, by rfl⟩ : syracuseStep 1226511 = 1839767) B1839767
theorem B11802419 : Blo 1226431 11802419 := bstep (se 1 (by rfl) ⟨8851814, by rfl⟩ : syracuseStep 11802419 = 17703629) B17703629
theorem B1226555 : Blo 1226431 1226555 := bstep (se 1 (by rfl) ⟨919916, by rfl⟩ : syracuseStep 1226555 = 1839833) B1839833
theorem B1840955 : Blo 1226431 1840955 := bstep (se 1 (by rfl) ⟨1380716, by rfl⟩ : syracuseStep 1840955 = 2761433) B2761433
theorem B1841015 : Blo 1226431 1841015 := bstep (se 1 (by rfl) ⟨1380761, by rfl⟩ : syracuseStep 1841015 = 2761523) B2761523
theorem B1226631 : Blo 1226431 1226631 := bstep (se 1 (by rfl) ⟨919973, by rfl⟩ : syracuseStep 1226631 = 1839947) B1839947
theorem B2070407 : Blo 1226431 2070407 := bstep (se 1 (by rfl) ⟨1552805, by rfl⟩ : syracuseStep 2070407 = 3105611) B3105611
theorem B1226639 : Blo 1226431 1226639 := bstep (se 1 (by rfl) ⟨919979, by rfl⟩ : syracuseStep 1226639 = 1839959) B1839959
theorem B1841039 : Blo 1226431 1841039 := bstep (se 1 (by rfl) ⟨1380779, by rfl⟩ : syracuseStep 1841039 = 2761559) B2761559
theorem B1554319 : Blo 1226431 1554319 := bstep (se 1 (by rfl) ⟨1165739, by rfl⟩ : syracuseStep 1554319 = 2331479) B2331479
theorem B1841081 : Blo 1226431 1841081 := bstep (se 2 (by rfl) ⟨690405, by rfl⟩ : syracuseStep 1841081 = 1380811) B1380811
theorem B1226683 : Blo 1226431 1226683 := bstep (se 1 (by rfl) ⟨920012, by rfl⟩ : syracuseStep 1226683 = 1840025) B1840025
theorem B1226759 : Blo 1226431 1226759 := bstep (se 1 (by rfl) ⟨920069, by rfl⟩ : syracuseStep 1226759 = 1840139) B1840139
theorem B1841159 : Blo 1226431 1841159 := bstep (se 1 (by rfl) ⟨1380869, by rfl⟩ : syracuseStep 1841159 = 2761739) B2761739
theorem B1226767 : Blo 1226431 1226767 := bstep (se 1 (by rfl) ⟨920075, by rfl⟩ : syracuseStep 1226767 = 1840151) B1840151
theorem B6912029 : Blo 1226431 6912029 := bstep (se 3 (by rfl) ⟨1296005, by rfl⟩ : syracuseStep 6912029 = 2592011) B2592011
theorem B1841195 : Blo 1226431 1841195 := bstep (se 1 (by rfl) ⟨1380896, by rfl⟩ : syracuseStep 1841195 = 2761793) B2761793
theorem B1226811 : Blo 1226431 1226811 := bstep (se 1 (by rfl) ⟨920108, by rfl⟩ : syracuseStep 1226811 = 1840217) B1840217
theorem B1554491 : Blo 1226431 1554491 := bstep (se 1 (by rfl) ⟨1165868, by rfl⟩ : syracuseStep 1554491 = 2331737) B2331737
theorem B4421699 : Blo 1226431 4421699 := bstep (se 1 (by rfl) ⟨3316274, by rfl⟩ : syracuseStep 4421699 = 6632549) B6632549
theorem B1841225 : Blo 1226431 1841225 := bstep (se 2 (by rfl) ⟨690459, by rfl⟩ : syracuseStep 1841225 = 1380919) B1380919
theorem B2488439 : Blo 1226431 2488439 := bstep (se 1 (by rfl) ⟨1866329, by rfl⟩ : syracuseStep 2488439 = 3732659) B3732659
theorem B1226887 : Blo 1226431 1226887 := bstep (se 1 (by rfl) ⟨920165, by rfl⟩ : syracuseStep 1226887 = 1840331) B1840331
theorem B1226895 : Blo 1226431 1226895 := bstep (se 1 (by rfl) ⟨920171, by rfl⟩ : syracuseStep 1226895 = 1840343) B1840343
theorem B1226939 : Blo 1226431 1226939 := bstep (se 1 (by rfl) ⟨920204, by rfl⟩ : syracuseStep 1226939 = 1840409) B1840409
theorem B1841339 : Blo 1226431 1841339 := bstep (se 1 (by rfl) ⟨1381004, by rfl⟩ : syracuseStep 1841339 = 2762009) B2762009
theorem B1841399 : Blo 1226431 1841399 := bstep (se 1 (by rfl) ⟨1381049, by rfl⟩ : syracuseStep 1841399 = 2762099) B2762099
theorem B3496193 : Blo 1226431 3496193 := bstep (se 2 (by rfl) ⟨1311072, by rfl⟩ : syracuseStep 3496193 = 2622145) B2622145
theorem B1227015 : Blo 1226431 1227015 := bstep (se 1 (by rfl) ⟨920261, by rfl⟩ : syracuseStep 1227015 = 1840523) B1840523
theorem B1227023 : Blo 1226431 1227023 := bstep (se 1 (by rfl) ⟨920267, by rfl⟩ : syracuseStep 1227023 = 1840535) B1840535
theorem B1841423 : Blo 1226431 1841423 := bstep (se 1 (by rfl) ⟨1381067, by rfl⟩ : syracuseStep 1841423 = 2762135) B2762135
theorem B1841465 : Blo 1226431 1841465 := bstep (se 2 (by rfl) ⟨690549, by rfl⟩ : syracuseStep 1841465 = 1381099) B1381099
theorem B1227067 : Blo 1226431 1227067 := bstep (se 1 (by rfl) ⟨920300, by rfl⟩ : syracuseStep 1227067 = 1840601) B1840601
theorem B4143419 : Blo 1226431 4143419 := bstep (se 1 (by rfl) ⟨3107564, by rfl⟩ : syracuseStep 4143419 = 6215129) B6215129
theorem B3316103 : Blo 1226431 3316103 := bstep (se 1 (by rfl) ⟨2487077, by rfl⟩ : syracuseStep 3316103 = 4974155) B4974155
theorem B1227143 : Blo 1226431 1227143 := bstep (se 1 (by rfl) ⟨920357, by rfl⟩ : syracuseStep 1227143 = 1840715) B1840715
theorem B1841543 : Blo 1226431 1841543 := bstep (se 1 (by rfl) ⟨1381157, by rfl⟩ : syracuseStep 1841543 = 2762315) B2762315
theorem B14940551 : Blo 1226431 14940551 := bstep (se 1 (by rfl) ⟨11205413, by rfl⟩ : syracuseStep 14940551 = 22410827) B22410827
theorem B1227151 : Blo 1226431 1227151 := bstep (se 1 (by rfl) ⟨920363, by rfl⟩ : syracuseStep 1227151 = 1840727) B1840727
theorem B1841579 : Blo 1226431 1841579 := bstep (se 1 (by rfl) ⟨1381184, by rfl⟩ : syracuseStep 1841579 = 2762369) B2762369
theorem B1227195 : Blo 1226431 1227195 := bstep (se 1 (by rfl) ⟨920396, by rfl⟩ : syracuseStep 1227195 = 1840793) B1840793
theorem B1841609 : Blo 1226431 1841609 := bstep (se 2 (by rfl) ⟨690603, by rfl⟩ : syracuseStep 1841609 = 1381207) B1381207
theorem B1227271 : Blo 1226431 1227271 := bstep (se 1 (by rfl) ⟨920453, by rfl⟩ : syracuseStep 1227271 = 1840907) B1840907
theorem B1227279 : Blo 1226431 1227279 := bstep (se 1 (by rfl) ⟨920459, by rfl⟩ : syracuseStep 1227279 = 1840919) B1840919
theorem B2071055 : Blo 1226431 2071055 := bstep (se 1 (by rfl) ⟨1553291, by rfl⟩ : syracuseStep 2071055 = 3106583) B3106583
theorem B3734059 : Blo 1226431 3734059 := bstep (se 1 (by rfl) ⟨2800544, by rfl⟩ : syracuseStep 3734059 = 5601089) B5601089
theorem B1227323 : Blo 1226431 1227323 := bstep (se 1 (by rfl) ⟨920492, by rfl⟩ : syracuseStep 1227323 = 1840985) B1840985
theorem B1841723 : Blo 1226431 1841723 := bstep (se 1 (by rfl) ⟨1381292, by rfl⟩ : syracuseStep 1841723 = 2762585) B2762585
theorem B4422205 : Blo 1226431 4422205 := bstep (se 3 (by rfl) ⟨829163, by rfl⟩ : syracuseStep 4422205 = 1658327) B1658327
theorem B1841783 : Blo 1226431 1841783 := bstep (se 1 (by rfl) ⟨1381337, by rfl⟩ : syracuseStep 1841783 = 2762675) B2762675
theorem B1227399 : Blo 1226431 1227399 := bstep (se 1 (by rfl) ⟨920549, by rfl⟩ : syracuseStep 1227399 = 1841099) B1841099
theorem B1227407 : Blo 1226431 1227407 := bstep (se 1 (by rfl) ⟨920555, by rfl⟩ : syracuseStep 1227407 = 1841111) B1841111
theorem B1841807 : Blo 1226431 1841807 := bstep (se 1 (by rfl) ⟨1381355, by rfl⟩ : syracuseStep 1841807 = 2762711) B2762711
theorem B1841849 : Blo 1226431 1841849 := bstep (se 2 (by rfl) ⟨690693, by rfl⟩ : syracuseStep 1841849 = 1381387) B1381387
theorem B1227451 : Blo 1226431 1227451 := bstep (se 1 (by rfl) ⟨920588, by rfl⟩ : syracuseStep 1227451 = 1841177) B1841177
theorem B1227527 : Blo 1226431 1227527 := bstep (se 1 (by rfl) ⟨920645, by rfl⟩ : syracuseStep 1227527 = 1841291) B1841291
theorem B1841927 : Blo 1226431 1841927 := bstep (se 1 (by rfl) ⟨1381445, by rfl⟩ : syracuseStep 1841927 = 2762891) B2762891
theorem B1227535 : Blo 1226431 1227535 := bstep (se 1 (by rfl) ⟨920651, by rfl⟩ : syracuseStep 1227535 = 1841303) B1841303
theorem B4143905 : Blo 1226431 4143905 := bstep (se 2 (by rfl) ⟨1553964, by rfl⟩ : syracuseStep 4143905 = 3107929) B3107929
theorem B1841963 : Blo 1226431 1841963 := bstep (se 1 (by rfl) ⟨1381472, by rfl⟩ : syracuseStep 1841963 = 2762945) B2762945
theorem B1227579 : Blo 1226431 1227579 := bstep (se 1 (by rfl) ⟨920684, by rfl⟩ : syracuseStep 1227579 = 1841369) B1841369
theorem B3496763 : Blo 1226431 3496763 := bstep (se 1 (by rfl) ⟨2622572, by rfl⟩ : syracuseStep 3496763 = 5245145) B5245145
theorem B1841993 : Blo 1226431 1841993 := bstep (se 2 (by rfl) ⟨690747, by rfl⟩ : syracuseStep 1841993 = 1381495) B1381495
theorem B7863155 : Blo 1226431 7863155 := bstep (se 1 (by rfl) ⟨5897366, by rfl⟩ : syracuseStep 7863155 = 11794733) B11794733
theorem B2759543 : Blo 1226431 2759543 := bstep (se 1 (by rfl) ⟨2069657, by rfl⟩ : syracuseStep 2759543 = 4139315) B4139315
theorem B1227655 : Blo 1226431 1227655 := bstep (se 1 (by rfl) ⟨920741, by rfl⟩ : syracuseStep 1227655 = 1841483) B1841483
theorem B1227663 : Blo 1226431 1227663 := bstep (se 1 (by rfl) ⟨920747, by rfl⟩ : syracuseStep 1227663 = 1841495) B1841495
theorem B1227707 : Blo 1226431 1227707 := bstep (se 1 (by rfl) ⟨920780, by rfl⟩ : syracuseStep 1227707 = 1841561) B1841561
theorem B1842107 : Blo 1226431 1842107 := bstep (se 1 (by rfl) ⟨1381580, by rfl⟩ : syracuseStep 1842107 = 2763161) B2763161
theorem B1842167 : Blo 1226431 1842167 := bstep (se 1 (by rfl) ⟨1381625, by rfl⟩ : syracuseStep 1842167 = 2763251) B2763251
theorem B1227783 : Blo 1226431 1227783 := bstep (se 1 (by rfl) ⟨920837, by rfl⟩ : syracuseStep 1227783 = 1841675) B1841675
theorem B1965071 : Blo 1226431 1965071 := bstep (se 1 (by rfl) ⟨1473803, by rfl⟩ : syracuseStep 1965071 = 2947607) B2947607
theorem B1227791 : Blo 1226431 1227791 := bstep (se 1 (by rfl) ⟨920843, by rfl⟩ : syracuseStep 1227791 = 1841687) B1841687
theorem B1842191 : Blo 1226431 1842191 := bstep (se 1 (by rfl) ⟨1381643, by rfl⟩ : syracuseStep 1842191 = 2763287) B2763287
theorem B2759723 : Blo 1226431 2759723 := bstep (se 1 (by rfl) ⟨2069792, by rfl⟩ : syracuseStep 2759723 = 4139585) B4139585
theorem B2071595 : Blo 1226431 2071595 := bstep (se 1 (by rfl) ⟨1553696, by rfl⟩ : syracuseStep 2071595 = 3107393) B3107393
theorem B3497003 : Blo 1226431 3497003 := bstep (se 1 (by rfl) ⟨2622752, by rfl⟩ : syracuseStep 3497003 = 5245505) B5245505
theorem B1227835 : Blo 1226431 1227835 := bstep (se 1 (by rfl) ⟨920876, by rfl⟩ : syracuseStep 1227835 = 1841753) B1841753
theorem B1842233 : Blo 1226431 1842233 := bstep (se 2 (by rfl) ⟨690837, by rfl⟩ : syracuseStep 1842233 = 1381675) B1381675
theorem B2210951 : Blo 1226431 2210951 := bstep (se 1 (by rfl) ⟨1658213, by rfl⟩ : syracuseStep 2210951 = 3316427) B3316427
theorem B1227911 : Blo 1226431 1227911 := bstep (se 1 (by rfl) ⟨920933, by rfl⟩ : syracuseStep 1227911 = 1841867) B1841867
theorem B1842311 : Blo 1226431 1842311 := bstep (se 1 (by rfl) ⟨1381733, by rfl⟩ : syracuseStep 1842311 = 2763467) B2763467
theorem B1227919 : Blo 1226431 1227919 := bstep (se 1 (by rfl) ⟨920939, by rfl⟩ : syracuseStep 1227919 = 1841879) B1841879
theorem B1842347 : Blo 1226431 1842347 := bstep (se 1 (by rfl) ⟨1381760, by rfl⟩ : syracuseStep 1842347 = 2763521) B2763521
theorem B1227963 : Blo 1226431 1227963 := bstep (se 1 (by rfl) ⟨920972, by rfl⟩ : syracuseStep 1227963 = 1841945) B1841945
theorem B1842377 : Blo 1226431 1842377 := bstep (se 2 (by rfl) ⟨690891, by rfl⟩ : syracuseStep 1842377 = 1381783) B1381783
theorem B1473799 : Blo 1226431 1473799 := bstep (se 1 (by rfl) ⟨1105349, by rfl⟩ : syracuseStep 1473799 = 2210699) B2210699
theorem B1228039 : Blo 1226431 1228039 := bstep (se 1 (by rfl) ⟨921029, by rfl⟩ : syracuseStep 1228039 = 1842059) B1842059
theorem B1228047 : Blo 1226431 1228047 := bstep (se 1 (by rfl) ⟨921035, by rfl⟩ : syracuseStep 1228047 = 1842071) B1842071
theorem B2948395 : Blo 1226431 2948395 := bstep (se 1 (by rfl) ⟨2211296, by rfl⟩ : syracuseStep 2948395 = 4422593) B4422593
theorem B5242171 : Blo 1226431 5242171 := bstep (se 1 (by rfl) ⟨3931628, by rfl⟩ : syracuseStep 5242171 = 7863257) B7863257
theorem B1228091 : Blo 1226431 1228091 := bstep (se 1 (by rfl) ⟨921068, by rfl⟩ : syracuseStep 1228091 = 1842137) B1842137
theorem B14179643 : Blo 1226431 14179643 := bstep (se 1 (by rfl) ⟨10634732, by rfl⟩ : syracuseStep 14179643 = 21269465) B21269465
theorem B1842491 : Blo 1226431 1842491 := bstep (se 1 (by rfl) ⟨1381868, by rfl⟩ : syracuseStep 1842491 = 2763737) B2763737
theorem B4144499 : Blo 1226431 4144499 := bstep (se 1 (by rfl) ⟨3108374, by rfl⟩ : syracuseStep 4144499 = 6216749) B6216749
theorem B1842551 : Blo 1226431 1842551 := bstep (se 1 (by rfl) ⟨1381913, by rfl⟩ : syracuseStep 1842551 = 2763827) B2763827
theorem B1228167 : Blo 1226431 1228167 := bstep (se 1 (by rfl) ⟨921125, by rfl⟩ : syracuseStep 1228167 = 1842251) B1842251
theorem B1228175 : Blo 1226431 1228175 := bstep (se 1 (by rfl) ⟨921131, by rfl⟩ : syracuseStep 1228175 = 1842263) B1842263
theorem B1842575 : Blo 1226431 1842575 := bstep (se 1 (by rfl) ⟨1381931, by rfl⟩ : syracuseStep 1842575 = 2763863) B2763863
theorem B13974929 : Blo 1226431 13974929 := bstep (se 2 (by rfl) ⟨5240598, by rfl⟩ : syracuseStep 13974929 = 10481197) B10481197
theorem B2760083 : Blo 1226431 2760083 := bstep (se 1 (by rfl) ⟨2070062, by rfl⟩ : syracuseStep 2760083 = 4140125) B4140125
theorem B2071993 : Blo 1226431 2071993 := bstep (se 2 (by rfl) ⟨776997, by rfl⟩ : syracuseStep 2071993 = 1553995) B1553995
theorem B1228219 : Blo 1226431 1228219 := bstep (se 1 (by rfl) ⟨921164, by rfl⟩ : syracuseStep 1228219 = 1842329) B1842329
theorem B1842617 : Blo 1226431 1842617 := bstep (se 2 (by rfl) ⟨690981, by rfl⟩ : syracuseStep 1842617 = 1381963) B1381963
theorem B2760137 : Blo 1226431 2760137 := bstep (se 2 (by rfl) ⟨1035051, by rfl⟩ : syracuseStep 2760137 = 2070103) B2070103
theorem B1891831 : Blo 1226431 1891831 := bstep (se 1 (by rfl) ⟨1418873, by rfl⟩ : syracuseStep 1891831 = 2837747) B2837747
theorem B1228295 : Blo 1226431 1228295 := bstep (se 1 (by rfl) ⟨921221, by rfl⟩ : syracuseStep 1228295 = 1842443) B1842443
theorem B1228303 : Blo 1226431 1228303 := bstep (se 1 (by rfl) ⟨921227, by rfl⟩ : syracuseStep 1228303 = 1842455) B1842455
theorem B1228347 : Blo 1226431 1228347 := bstep (se 1 (by rfl) ⟨921260, by rfl⟩ : syracuseStep 1228347 = 1842521) B1842521
theorem B3743347 : Blo 1226431 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B1228423 : Blo 1226431 1228423 := bstep (se 1 (by rfl) ⟨921317, by rfl⟩ : syracuseStep 1228423 = 1842635) B1842635
theorem B1228431 : Blo 1226431 1228431 := bstep (se 1 (by rfl) ⟨921323, by rfl⟩ : syracuseStep 1228431 = 1842647) B1842647
theorem B15728357 : Blo 1226431 15728357 := bstep (se 4 (by rfl) ⟨1474533, by rfl⟩ : syracuseStep 15728357 = 2949067) B2949067
theorem B9961217 : Blo 1226431 9961217 := bstep (se 2 (by rfl) ⟨3735456, by rfl⟩ : syracuseStep 9961217 = 7470913) B7470913
theorem B3104527 : Blo 1226431 3104527 := bstep (se 1 (by rfl) ⟨2328395, by rfl⟩ : syracuseStep 3104527 = 4656791) B4656791
theorem B3932039 : Blo 1226431 3932039 := bstep (se 1 (by rfl) ⟨2949029, by rfl⟩ : syracuseStep 3932039 = 5898059) B5898059
theorem B2949011 : Blo 1226431 2949011 := bstep (se 1 (by rfl) ⟨2211758, by rfl⟩ : syracuseStep 2949011 = 4423517) B4423517
theorem B11198411 : Blo 1226431 11198411 := bstep (se 1 (by rfl) ⟨8398808, by rfl⟩ : syracuseStep 11198411 = 16797617) B16797617
theorem B5898329 : Blo 1226431 5898329 := bstep (se 2 (by rfl) ⟨2211873, by rfl⟩ : syracuseStep 5898329 = 4423747) B4423747
theorem B4145309 : Blo 1226431 4145309 := bstep (se 3 (by rfl) ⟨777245, by rfl⟩ : syracuseStep 4145309 = 1554491) B1554491
theorem B2760875 : Blo 1226431 2760875 := bstep (se 1 (by rfl) ⟨2070656, by rfl⟩ : syracuseStep 2760875 = 4141313) B4141313
theorem B2949367 : Blo 1226431 2949367 := bstep (se 1 (by rfl) ⟨2212025, by rfl⟩ : syracuseStep 2949367 = 4424051) B4424051
theorem B6635837 : Blo 1226431 6635837 := bstep (se 3 (by rfl) ⟨1244219, by rfl⟩ : syracuseStep 6635837 = 2488439) B2488439
theorem B6218045 : Blo 1226431 6218045 := bstep (se 3 (by rfl) ⟨1165883, by rfl⟩ : syracuseStep 6218045 = 2331767) B2331767
theorem B4424179 : Blo 1226431 4424179 := bstep (se 1 (by rfl) ⟨3318134, by rfl⟩ : syracuseStep 4424179 = 6636269) B6636269
theorem B3932705 : Blo 1226431 3932705 := bstep (se 2 (by rfl) ⟨1474764, by rfl⟩ : syracuseStep 3932705 = 2949529) B2949529
theorem B6210107 : Blo 1226431 6210107 := bstep (se 1 (by rfl) ⟨4657580, by rfl⟩ : syracuseStep 6210107 = 9315161) B9315161
theorem B4661819 : Blo 1226431 4661819 := bstep (se 1 (by rfl) ⟨3496364, by rfl⟩ : syracuseStep 4661819 = 6992729) B6992729
theorem B1966763 : Blo 1226431 1966763 := bstep (se 1 (by rfl) ⟨1475072, by rfl⟩ : syracuseStep 1966763 = 2950145) B2950145
theorem B4145849 : Blo 1226431 4145849 := bstep (se 2 (by rfl) ⟨1554693, by rfl⟩ : syracuseStep 4145849 = 3109387) B3109387
theorem B3105479 : Blo 1226431 3105479 := bstep (se 1 (by rfl) ⟨2329109, by rfl⟩ : syracuseStep 3105479 = 4658219) B4658219
theorem B2761415 : Blo 1226431 2761415 := bstep (se 1 (by rfl) ⟨2071061, by rfl⟩ : syracuseStep 2761415 = 4142123) B4142123
theorem B4973341 : Blo 1226431 4973341 := bstep (se 3 (by rfl) ⟨932501, by rfl⟩ : syracuseStep 4973341 = 1865003) B1865003
theorem B2949983 : Blo 1226431 2949983 := bstep (se 1 (by rfl) ⟨2212487, by rfl⟩ : syracuseStep 2949983 = 4424975) B4424975
theorem B13460633 : Blo 1226431 13460633 := bstep (se 2 (by rfl) ⟨5047737, by rfl⟩ : syracuseStep 13460633 = 10095475) B10095475
theorem B1967275 : Blo 1226431 1967275 := bstep (se 1 (by rfl) ⟨1475456, by rfl⟩ : syracuseStep 1967275 = 2950913) B2950913
theorem B8512705 : Blo 1226431 8512705 := bstep (se 2 (by rfl) ⟨3192264, by rfl⟩ : syracuseStep 8512705 = 6384529) B6384529
theorem B6210755 : Blo 1226431 6210755 := bstep (se 1 (by rfl) ⟨4658066, by rfl⟩ : syracuseStep 6210755 = 9316133) B9316133
theorem B8840573 : Blo 1226431 8840573 := bstep (se 3 (by rfl) ⟨1657607, by rfl⟩ : syracuseStep 8840573 = 3315215) B3315215
theorem B2622863 : Blo 1226431 2622863 := bstep (se 1 (by rfl) ⟨1967147, by rfl⟩ : syracuseStep 2622863 = 3934295) B3934295
theorem B7865819 : Blo 1226431 7865819 := bstep (se 1 (by rfl) ⟨5899364, by rfl⟩ : syracuseStep 7865819 = 11798729) B11798729
theorem B2762279 : Blo 1226431 2762279 := bstep (se 1 (by rfl) ⟨2071709, by rfl⟩ : syracuseStep 2762279 = 4143419) B4143419
theorem B31090321 : Blo 1226431 31090321 := bstep (se 2 (by rfl) ⟨11658870, by rfl⟩ : syracuseStep 31090321 = 23317741) B23317741
theorem B5244563 : Blo 1226431 5244563 := bstep (se 1 (by rfl) ⟨3933422, by rfl⟩ : syracuseStep 5244563 = 7866845) B7866845
theorem B6301405 : Blo 1226431 6301405 := bstep (se 3 (by rfl) ⟨1181513, by rfl⟩ : syracuseStep 6301405 = 2363027) B2363027
theorem B6989561 : Blo 1226431 6989561 := bstep (se 2 (by rfl) ⟨2621085, by rfl⟩ : syracuseStep 6989561 = 5242171) B5242171
theorem B3106633 : Blo 1226431 3106633 := bstep (se 2 (by rfl) ⟨1164987, by rfl⟩ : syracuseStep 3106633 = 2329975) B2329975
theorem B2762603 : Blo 1226431 2762603 := bstep (se 1 (by rfl) ⟨2071952, by rfl⟩ : syracuseStep 2762603 = 4143905) B4143905
theorem B2762657 : Blo 1226431 2762657 := bstep (se 2 (by rfl) ⟨1035996, by rfl⟩ : syracuseStep 2762657 = 2071993) B2071993
theorem B4991129 : Blo 1226431 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B2762999 : Blo 1226431 2762999 := bstep (se 1 (by rfl) ⟨2072249, by rfl⟩ : syracuseStep 2762999 = 4144499) B4144499
theorem B9316619 : Blo 1226431 9316619 := bstep (se 1 (by rfl) ⟨6987464, by rfl⟩ : syracuseStep 9316619 = 13974929) B13974929
theorem B2328905 : Blo 1226431 2328905 := bstep (se 2 (by rfl) ⟨873339, by rfl⟩ : syracuseStep 2328905 = 1746679) B1746679
theorem B4139369 : Blo 1226431 4139369 := bstep (se 2 (by rfl) ⟨1552263, by rfl⟩ : syracuseStep 4139369 = 3104527) B3104527
theorem B1772155 : Blo 1226431 1772155 := bstep (se 1 (by rfl) ⟨1329116, by rfl⟩ : syracuseStep 1772155 = 2658233) B2658233
theorem B7465607 : Blo 1226431 7465607 := bstep (se 1 (by rfl) ⟨5599205, by rfl⟩ : syracuseStep 7465607 = 11198411) B11198411
theorem B3934909 : Blo 1226431 3934909 := bstep (se 3 (by rfl) ⟨737795, by rfl⟩ : syracuseStep 3934909 = 1475591) B1475591
theorem B2329337 : Blo 1226431 2329337 := bstep (se 2 (by rfl) ⟨873501, by rfl⟩ : syracuseStep 2329337 = 1747003) B1747003
theorem B26889029 : Blo 1226431 26889029 := bstep (se 4 (by rfl) ⟨2520846, by rfl⟩ : syracuseStep 26889029 = 5041693) B5041693
theorem B2763593 : Blo 1226431 2763593 := bstep (se 2 (by rfl) ⟨1036347, by rfl⟩ : syracuseStep 2763593 = 2072695) B2072695
theorem B3107767 : Blo 1226431 3107767 := bstep (se 1 (by rfl) ⟨2330825, by rfl⟩ : syracuseStep 3107767 = 4661651) B4661651
theorem B4139963 : Blo 1226431 4139963 := bstep (se 1 (by rfl) ⟨3104972, by rfl⟩ : syracuseStep 4139963 = 6209945) B6209945
theorem B4975631 : Blo 1226431 4975631 := bstep (se 1 (by rfl) ⟨3731723, by rfl⟩ : syracuseStep 4975631 = 7463447) B7463447
theorem B7867459 : Blo 1226431 7867459 := bstep (se 1 (by rfl) ⟨5900594, by rfl⟩ : syracuseStep 7867459 = 11801189) B11801189
theorem B4197491 : Blo 1226431 4197491 := bstep (se 1 (by rfl) ⟨3148118, by rfl⟩ : syracuseStep 4197491 = 6296237) B6296237
theorem B6991019 : Blo 1226431 6991019 := bstep (se 1 (by rfl) ⟨5243264, by rfl⟩ : syracuseStep 6991019 = 10486529) B10486529
theorem B5311945 : Blo 1226431 5311945 := bstep (se 2 (by rfl) ⟨1991979, by rfl⟩ : syracuseStep 5311945 = 3983959) B3983959
theorem B1379803 : Blo 1226431 1379803 := bstep (se 1 (by rfl) ⟨1034852, by rfl⟩ : syracuseStep 1379803 = 2069705) B2069705
theorem B6295163 : Blo 1226431 6295163 := bstep (se 1 (by rfl) ⟨4721372, by rfl⟩ : syracuseStep 6295163 = 9442745) B9442745
theorem B9318077 : Blo 1226431 9318077 := bstep (se 3 (by rfl) ⟨1747139, by rfl⟩ : syracuseStep 9318077 = 3494279) B3494279
theorem B39841469 : Blo 1226431 39841469 := bstep (se 3 (by rfl) ⟨7470275, by rfl⟩ : syracuseStep 39841469 = 14940551) B14940551
theorem B2797267 : Blo 1226431 2797267 := bstep (se 1 (by rfl) ⟨2097950, by rfl⟩ : syracuseStep 2797267 = 4195901) B4195901
theorem B21294809 : Blo 1226431 21294809 := bstep (se 2 (by rfl) ⟨7985553, by rfl⟩ : syracuseStep 21294809 = 15971107) B15971107
theorem B1748729 : Blo 1226431 1748729 := bstep (se 2 (by rfl) ⟨655773, by rfl⟩ : syracuseStep 1748729 = 1311547) B1311547
theorem B1552223 : Blo 1226431 1552223 := bstep (se 1 (by rfl) ⟨1164167, by rfl⟩ : syracuseStep 1552223 = 2328335) B2328335
theorem B7868279 : Blo 1226431 7868279 := bstep (se 1 (by rfl) ⟨5901209, by rfl⟩ : syracuseStep 7868279 = 11802419) B11802419
theorem B1380271 : Blo 1226431 1380271 := bstep (se 1 (by rfl) ⟨1035203, by rfl⟩ : syracuseStep 1380271 = 2070407) B2070407
theorem B4608019 : Blo 1226431 4608019 := bstep (se 1 (by rfl) ⟨3456014, by rfl⟩ : syracuseStep 4608019 = 6912029) B6912029
theorem B29847629 : Blo 1226431 29847629 := bstep (se 3 (by rfl) ⟨5596430, by rfl⟩ : syracuseStep 29847629 = 11192861) B11192861
theorem B9318563 : Blo 1226431 9318563 := bstep (se 1 (by rfl) ⟨6988922, by rfl⟩ : syracuseStep 9318563 = 13977845) B13977845
theorem B2330795 : Blo 1226431 2330795 := bstep (se 1 (by rfl) ⟨1748096, by rfl⟩ : syracuseStep 2330795 = 3496193) B3496193
theorem B1380703 : Blo 1226431 1380703 := bstep (se 1 (by rfl) ⟨1035527, by rfl⟩ : syracuseStep 1380703 = 2071055) B2071055
theorem B3109225 : Blo 1226431 3109225 := bstep (se 2 (by rfl) ⟨1165959, by rfl⟩ : syracuseStep 3109225 = 2331919) B2331919
theorem B3150209 : Blo 1226431 3150209 := bstep (se 2 (by rfl) ⟨1181328, by rfl⟩ : syracuseStep 3150209 = 2362657) B2362657
theorem B11800961 : Blo 1226431 11800961 := bstep (se 2 (by rfl) ⟨4425360, by rfl⟩ : syracuseStep 11800961 = 8850721) B8850721
theorem B4977185 : Blo 1226431 4977185 := bstep (se 2 (by rfl) ⟨1866444, by rfl⟩ : syracuseStep 4977185 = 3732889) B3732889
theorem B2331175 : Blo 1226431 2331175 := bstep (se 1 (by rfl) ⟨1748381, by rfl⟩ : syracuseStep 2331175 = 3496763) B3496763
theorem B1839695 : Blo 1226431 1839695 := bstep (se 1 (by rfl) ⟨1379771, by rfl⟩ : syracuseStep 1839695 = 2759543) B2759543
theorem B4141691 : Blo 1226431 4141691 := bstep (se 1 (by rfl) ⟨3106268, by rfl⟩ : syracuseStep 4141691 = 6212537) B6212537
theorem B1839815 : Blo 1226431 1839815 := bstep (se 1 (by rfl) ⟨1379861, by rfl⟩ : syracuseStep 1839815 = 2759723) B2759723
theorem B1381063 : Blo 1226431 1381063 := bstep (se 1 (by rfl) ⟨1035797, by rfl⟩ : syracuseStep 1381063 = 2071595) B2071595
theorem B2331335 : Blo 1226431 2331335 := bstep (se 1 (by rfl) ⟨1748501, by rfl⟩ : syracuseStep 2331335 = 3497003) B3497003
theorem B5239505 : Blo 1226431 5239505 := bstep (se 2 (by rfl) ⟨1964814, by rfl⟩ : syracuseStep 5239505 = 3929629) B3929629
theorem B4141853 : Blo 1226431 4141853 := bstep (se 3 (by rfl) ⟨776597, by rfl⟩ : syracuseStep 4141853 = 1553195) B1553195
theorem B1839977 : Blo 1226431 1839977 := bstep (se 2 (by rfl) ⟨689991, by rfl⟩ : syracuseStep 1839977 = 1379983) B1379983
theorem B1840055 : Blo 1226431 1840055 := bstep (se 1 (by rfl) ⟨1380041, by rfl⟩ : syracuseStep 1840055 = 2760083) B2760083
theorem B1840091 : Blo 1226431 1840091 := bstep (se 1 (by rfl) ⟨1380068, by rfl⟩ : syracuseStep 1840091 = 2760137) B2760137
theorem B6640811 : Blo 1226431 6640811 := bstep (se 1 (by rfl) ⟨4980608, by rfl⟩ : syracuseStep 6640811 = 9961217) B9961217
theorem B2069833 : Blo 1226431 2069833 := bstep (se 2 (by rfl) ⟨776187, by rfl⟩ : syracuseStep 2069833 = 1552375) B1552375
theorem B2069867 : Blo 1226431 2069867 := bstep (se 1 (by rfl) ⟨1552400, by rfl⟩ : syracuseStep 2069867 = 3104801) B3104801
theorem B5240189 : Blo 1226431 5240189 := bstep (se 3 (by rfl) ⟨982535, by rfl⟩ : syracuseStep 5240189 = 1965071) B1965071
theorem B1840559 : Blo 1226431 1840559 := bstep (se 1 (by rfl) ⟨1380419, by rfl⟩ : syracuseStep 1840559 = 2760839) B2760839
theorem B4142555 : Blo 1226431 4142555 := bstep (se 1 (by rfl) ⟨3106916, by rfl⟩ : syracuseStep 4142555 = 6213833) B6213833
theorem B1840649 : Blo 1226431 1840649 := bstep (se 2 (by rfl) ⟨690243, by rfl⟩ : syracuseStep 1840649 = 1380487) B1380487
theorem B1840679 : Blo 1226431 1840679 := bstep (se 1 (by rfl) ⟨1380509, by rfl⟩ : syracuseStep 1840679 = 2761019) B2761019
theorem B1381927 : Blo 1226431 1381927 := bstep (se 1 (by rfl) ⟨1036445, by rfl⟩ : syracuseStep 1381927 = 2072891) B2072891
theorem B1840763 : Blo 1226431 1840763 := bstep (se 1 (by rfl) ⟨1380572, by rfl⟩ : syracuseStep 1840763 = 2761145) B2761145
theorem B6215291 : Blo 1226431 6215291 := bstep (se 1 (by rfl) ⟨4661468, by rfl⟩ : syracuseStep 6215291 = 9322937) B9322937
theorem B1226439 : Blo 1226431 1226439 := bstep (se 1 (by rfl) ⟨919829, by rfl⟩ : syracuseStep 1226439 = 1839659) B1839659
theorem B4658903 : Blo 1226431 4658903 := bstep (se 1 (by rfl) ⟨3494177, by rfl⟩ : syracuseStep 4658903 = 6988355) B6988355
theorem B5043923 : Blo 1226431 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B1226459 : Blo 1226431 1226459 := bstep (se 1 (by rfl) ⟨919844, by rfl⟩ : syracuseStep 1226459 = 1839689) B1839689
theorem B2070265 : Blo 1226431 2070265 := bstep (se 2 (by rfl) ⟨776349, by rfl⟩ : syracuseStep 2070265 = 1552699) B1552699
theorem B1840889 : Blo 1226431 1840889 := bstep (se 2 (by rfl) ⟨690333, by rfl⟩ : syracuseStep 1840889 = 1380667) B1380667
theorem B1226535 : Blo 1226431 1226535 := bstep (se 1 (by rfl) ⟨919901, by rfl⟩ : syracuseStep 1226535 = 1839803) B1839803
theorem B1226575 : Blo 1226431 1226575 := bstep (se 1 (by rfl) ⟨919931, by rfl⟩ : syracuseStep 1226575 = 1839863) B1839863
theorem B1226591 : Blo 1226431 1226591 := bstep (se 1 (by rfl) ⟨919943, by rfl⟩ : syracuseStep 1226591 = 1839887) B1839887
theorem B1840991 : Blo 1226431 1840991 := bstep (se 1 (by rfl) ⟨1380743, by rfl⟩ : syracuseStep 1840991 = 2761487) B2761487
theorem B1841003 : Blo 1226431 1841003 := bstep (se 1 (by rfl) ⟨1380752, by rfl⟩ : syracuseStep 1841003 = 2761505) B2761505
theorem B6297463 : Blo 1226431 6297463 := bstep (se 1 (by rfl) ⟨4723097, by rfl⟩ : syracuseStep 6297463 = 9446195) B9446195
theorem B1226619 : Blo 1226431 1226619 := bstep (se 1 (by rfl) ⟨919964, by rfl⟩ : syracuseStep 1226619 = 1839929) B1839929
theorem B1226671 : Blo 1226431 1226671 := bstep (se 1 (by rfl) ⟨920003, by rfl⟩ : syracuseStep 1226671 = 1840007) B1840007
theorem B1226695 : Blo 1226431 1226695 := bstep (se 1 (by rfl) ⟨920021, by rfl⟩ : syracuseStep 1226695 = 1840043) B1840043
theorem B1226715 : Blo 1226431 1226715 := bstep (se 1 (by rfl) ⟨920036, by rfl⟩ : syracuseStep 1226715 = 1840073) B1840073
theorem B2070535 : Blo 1226431 2070535 := bstep (se 1 (by rfl) ⟨1552901, by rfl⟩ : syracuseStep 2070535 = 3105803) B3105803
theorem B6993935 : Blo 1226431 6993935 := bstep (se 1 (by rfl) ⟨5245451, by rfl⟩ : syracuseStep 6993935 = 10490903) B10490903
theorem B1226791 : Blo 1226431 1226791 := bstep (se 1 (by rfl) ⟨920093, by rfl⟩ : syracuseStep 1226791 = 1840187) B1840187
theorem B4978745 : Blo 1226431 4978745 := bstep (se 2 (by rfl) ⟨1867029, by rfl⟩ : syracuseStep 4978745 = 3734059) B3734059
theorem B1226831 : Blo 1226431 1226831 := bstep (se 1 (by rfl) ⟨920123, by rfl⟩ : syracuseStep 1226831 = 1840247) B1840247
theorem B1841231 : Blo 1226431 1841231 := bstep (se 1 (by rfl) ⟨1380923, by rfl⟩ : syracuseStep 1841231 = 2761847) B2761847
theorem B5896273 : Blo 1226431 5896273 := bstep (se 2 (by rfl) ⟨2211102, by rfl⟩ : syracuseStep 5896273 = 4422205) B4422205
theorem B1226847 : Blo 1226431 1226847 := bstep (se 1 (by rfl) ⟨920135, by rfl⟩ : syracuseStep 1226847 = 1840271) B1840271
theorem B1226875 : Blo 1226431 1226875 := bstep (se 1 (by rfl) ⟨920156, by rfl⟩ : syracuseStep 1226875 = 1840313) B1840313
theorem B4143257 : Blo 1226431 4143257 := bstep (se 2 (by rfl) ⟨1553721, by rfl⟩ : syracuseStep 4143257 = 3107443) B3107443
theorem B1226927 : Blo 1226431 1226927 := bstep (se 1 (by rfl) ⟨920195, by rfl⟩ : syracuseStep 1226927 = 1840391) B1840391
theorem B1226951 : Blo 1226431 1226951 := bstep (se 1 (by rfl) ⟨920213, by rfl⟩ : syracuseStep 1226951 = 1840427) B1840427
theorem B1841351 : Blo 1226431 1841351 := bstep (se 1 (by rfl) ⟨1381013, by rfl⟩ : syracuseStep 1841351 = 2762027) B2762027
theorem B1226971 : Blo 1226431 1226971 := bstep (se 1 (by rfl) ⟨920228, by rfl⟩ : syracuseStep 1226971 = 1840457) B1840457
theorem B6994187 : Blo 1226431 6994187 := bstep (se 1 (by rfl) ⟨5245640, by rfl⟩ : syracuseStep 6994187 = 10491281) B10491281
theorem B1227047 : Blo 1226431 1227047 := bstep (se 1 (by rfl) ⟨920285, by rfl⟩ : syracuseStep 1227047 = 1840571) B1840571
theorem B1227087 : Blo 1226431 1227087 := bstep (se 1 (by rfl) ⟨920315, by rfl⟩ : syracuseStep 1227087 = 1840631) B1840631
theorem B1227103 : Blo 1226431 1227103 := bstep (se 1 (by rfl) ⟨920327, by rfl⟩ : syracuseStep 1227103 = 1840655) B1840655
theorem B1841513 : Blo 1226431 1841513 := bstep (se 2 (by rfl) ⟨690567, by rfl⟩ : syracuseStep 1841513 = 1381135) B1381135
theorem B1227131 : Blo 1226431 1227131 := bstep (se 1 (by rfl) ⟨920348, by rfl⟩ : syracuseStep 1227131 = 1840697) B1840697
theorem B8853893 : Blo 1226431 8853893 := bstep (se 4 (by rfl) ⟨830052, by rfl⟩ : syracuseStep 8853893 = 1660105) B1660105
theorem B1227183 : Blo 1226431 1227183 := bstep (se 1 (by rfl) ⟨920387, by rfl⟩ : syracuseStep 1227183 = 1840775) B1840775
theorem B2070967 : Blo 1226431 2070967 := bstep (se 1 (by rfl) ⟨1553225, by rfl⟩ : syracuseStep 2070967 = 3106451) B3106451
theorem B1841591 : Blo 1226431 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B1227207 : Blo 1226431 1227207 := bstep (se 1 (by rfl) ⟨920405, by rfl⟩ : syracuseStep 1227207 = 1840811) B1840811
theorem B15350219 : Blo 1226431 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B1964507 : Blo 1226431 1964507 := bstep (se 1 (by rfl) ⟨1473380, by rfl⟩ : syracuseStep 1964507 = 2946761) B2946761
theorem B1227227 : Blo 1226431 1227227 := bstep (se 1 (by rfl) ⟨920420, by rfl⟩ : syracuseStep 1227227 = 1840841) B1840841
theorem B1841627 : Blo 1226431 1841627 := bstep (se 1 (by rfl) ⟨1381220, by rfl⟩ : syracuseStep 1841627 = 2762441) B2762441
theorem B14162465 : Blo 1226431 14162465 := bstep (se 2 (by rfl) ⟨5310924, by rfl⟩ : syracuseStep 14162465 = 10621849) B10621849
theorem B9320993 : Blo 1226431 9320993 := bstep (se 2 (by rfl) ⟨3495372, by rfl⟩ : syracuseStep 9320993 = 6990745) B6990745
theorem B15735329 : Blo 1226431 15735329 := bstep (se 2 (by rfl) ⟨5900748, by rfl⟩ : syracuseStep 15735329 = 11801497) B11801497
theorem B1227303 : Blo 1226431 1227303 := bstep (se 1 (by rfl) ⟨920477, by rfl⟩ : syracuseStep 1227303 = 1840955) B1840955
theorem B1227343 : Blo 1226431 1227343 := bstep (se 1 (by rfl) ⟨920507, by rfl⟩ : syracuseStep 1227343 = 1841015) B1841015
theorem B1227359 : Blo 1226431 1227359 := bstep (se 1 (by rfl) ⟨920519, by rfl⟩ : syracuseStep 1227359 = 1841039) B1841039
theorem B2071163 : Blo 1226431 2071163 := bstep (se 1 (by rfl) ⟨1553372, by rfl⟩ : syracuseStep 2071163 = 3106745) B3106745
theorem B1227387 : Blo 1226431 1227387 := bstep (se 1 (by rfl) ⟨920540, by rfl⟩ : syracuseStep 1227387 = 1841081) B1841081
theorem B1227439 : Blo 1226431 1227439 := bstep (se 1 (by rfl) ⟨920579, by rfl⟩ : syracuseStep 1227439 = 1841159) B1841159
theorem B1227463 : Blo 1226431 1227463 := bstep (se 1 (by rfl) ⟨920597, by rfl⟩ : syracuseStep 1227463 = 1841195) B1841195
theorem B2947799 : Blo 1226431 2947799 := bstep (se 1 (by rfl) ⟨2210849, by rfl⟩ : syracuseStep 2947799 = 4421699) B4421699
theorem B1227483 : Blo 1226431 1227483 := bstep (se 1 (by rfl) ⟨920612, by rfl⟩ : syracuseStep 1227483 = 1841225) B1841225
theorem B11803421 : Blo 1226431 11803421 := bstep (se 3 (by rfl) ⟨2213141, by rfl⟩ : syracuseStep 11803421 = 4426283) B4426283
theorem B1227559 : Blo 1226431 1227559 := bstep (se 1 (by rfl) ⟨920669, by rfl⟩ : syracuseStep 1227559 = 1841339) B1841339
theorem B1227599 : Blo 1226431 1227599 := bstep (se 1 (by rfl) ⟨920699, by rfl⟩ : syracuseStep 1227599 = 1841399) B1841399
theorem B1227615 : Blo 1226431 1227615 := bstep (se 1 (by rfl) ⟨920711, by rfl⟩ : syracuseStep 1227615 = 1841423) B1841423
theorem B1227643 : Blo 1226431 1227643 := bstep (se 1 (by rfl) ⟨920732, by rfl⟩ : syracuseStep 1227643 = 1841465) B1841465
theorem B2210735 : Blo 1226431 2210735 := bstep (se 1 (by rfl) ⟨1658051, by rfl⟩ : syracuseStep 2210735 = 3316103) B3316103
theorem B1227695 : Blo 1226431 1227695 := bstep (se 1 (by rfl) ⟨920771, by rfl⟩ : syracuseStep 1227695 = 1841543) B1841543
theorem B1842095 : Blo 1226431 1842095 := bstep (se 1 (by rfl) ⟨1381571, by rfl⟩ : syracuseStep 1842095 = 2763143) B2763143
theorem B3316663 : Blo 1226431 3316663 := bstep (se 1 (by rfl) ⟨2487497, by rfl⟩ : syracuseStep 3316663 = 4974995) B4974995
theorem B1227719 : Blo 1226431 1227719 := bstep (se 1 (by rfl) ⟨920789, by rfl⟩ : syracuseStep 1227719 = 1841579) B1841579
theorem B1227739 : Blo 1226431 1227739 := bstep (se 1 (by rfl) ⟨920804, by rfl⟩ : syracuseStep 1227739 = 1841609) B1841609
theorem B2759687 : Blo 1226431 2759687 := bstep (se 1 (by rfl) ⟨2069765, by rfl⟩ : syracuseStep 2759687 = 4139531) B4139531
theorem B1965065 : Blo 1226431 1965065 := bstep (se 2 (by rfl) ⟨736899, by rfl⟩ : syracuseStep 1965065 = 1473799) B1473799
theorem B2071561 : Blo 1226431 2071561 := bstep (se 2 (by rfl) ⟨776835, by rfl⟩ : syracuseStep 2071561 = 1553671) B1553671
theorem B1842185 : Blo 1226431 1842185 := bstep (se 2 (by rfl) ⟨690819, by rfl⟩ : syracuseStep 1842185 = 1381639) B1381639
theorem B1227815 : Blo 1226431 1227815 := bstep (se 1 (by rfl) ⟨920861, by rfl⟩ : syracuseStep 1227815 = 1841723) B1841723
theorem B1842215 : Blo 1226431 1842215 := bstep (se 1 (by rfl) ⟨1381661, by rfl⟩ : syracuseStep 1842215 = 2763323) B2763323
theorem B3931193 : Blo 1226431 3931193 := bstep (se 2 (by rfl) ⟨1474197, by rfl⟩ : syracuseStep 3931193 = 2948395) B2948395
theorem B2759759 : Blo 1226431 2759759 := bstep (se 1 (by rfl) ⟨2069819, by rfl⟩ : syracuseStep 2759759 = 4139639) B4139639
theorem B1227855 : Blo 1226431 1227855 := bstep (se 1 (by rfl) ⟨920891, by rfl⟩ : syracuseStep 1227855 = 1841783) B1841783
theorem B1227871 : Blo 1226431 1227871 := bstep (se 1 (by rfl) ⟨920903, by rfl⟩ : syracuseStep 1227871 = 1841807) B1841807
theorem B1227899 : Blo 1226431 1227899 := bstep (se 1 (by rfl) ⟨920924, by rfl⟩ : syracuseStep 1227899 = 1841849) B1841849
theorem B1842299 : Blo 1226431 1842299 := bstep (se 1 (by rfl) ⟨1381724, by rfl⟩ : syracuseStep 1842299 = 2763449) B2763449
theorem B2071723 : Blo 1226431 2071723 := bstep (se 1 (by rfl) ⟨1553792, by rfl⟩ : syracuseStep 2071723 = 3107585) B3107585
theorem B1227951 : Blo 1226431 1227951 := bstep (se 1 (by rfl) ⟨920963, by rfl⟩ : syracuseStep 1227951 = 1841927) B1841927
theorem B1227975 : Blo 1226431 1227975 := bstep (se 1 (by rfl) ⟨920981, by rfl⟩ : syracuseStep 1227975 = 1841963) B1841963
theorem B1227995 : Blo 1226431 1227995 := bstep (se 1 (by rfl) ⟨920996, by rfl⟩ : syracuseStep 1227995 = 1841993) B1841993
theorem B5242103 : Blo 1226431 5242103 := bstep (se 1 (by rfl) ⟨3931577, by rfl⟩ : syracuseStep 5242103 = 7863155) B7863155
theorem B1842425 : Blo 1226431 1842425 := bstep (se 2 (by rfl) ⟨690909, by rfl⟩ : syracuseStep 1842425 = 1381819) B1381819
theorem B1228071 : Blo 1226431 1228071 := bstep (se 1 (by rfl) ⟨921053, by rfl⟩ : syracuseStep 1228071 = 1842107) B1842107
theorem B4144445 : Blo 1226431 4144445 := bstep (se 3 (by rfl) ⟨777083, by rfl⟩ : syracuseStep 4144445 = 1554167) B1554167
theorem B2522441 : Blo 1226431 2522441 := bstep (se 2 (by rfl) ⟨945915, by rfl⟩ : syracuseStep 2522441 = 1891831) B1891831
theorem B1228111 : Blo 1226431 1228111 := bstep (se 1 (by rfl) ⟨921083, by rfl⟩ : syracuseStep 1228111 = 1842167) B1842167
theorem B1228127 : Blo 1226431 1228127 := bstep (se 1 (by rfl) ⟨921095, by rfl⟩ : syracuseStep 1228127 = 1842191) B1842191
theorem B1842527 : Blo 1226431 1842527 := bstep (se 1 (by rfl) ⟨1381895, by rfl⟩ : syracuseStep 1842527 = 2763791) B2763791
theorem B1842539 : Blo 1226431 1842539 := bstep (se 1 (by rfl) ⟨1381904, by rfl⟩ : syracuseStep 1842539 = 2763809) B2763809
theorem B1228155 : Blo 1226431 1228155 := bstep (se 1 (by rfl) ⟨921116, by rfl⟩ : syracuseStep 1228155 = 1842233) B1842233
theorem B1473967 : Blo 1226431 1473967 := bstep (se 1 (by rfl) ⟨1105475, by rfl⟩ : syracuseStep 1473967 = 2210951) B2210951
theorem B1228207 : Blo 1226431 1228207 := bstep (se 1 (by rfl) ⟨921155, by rfl⟩ : syracuseStep 1228207 = 1842311) B1842311
theorem B1228231 : Blo 1226431 1228231 := bstep (se 1 (by rfl) ⟨921173, by rfl⟩ : syracuseStep 1228231 = 1842347) B1842347
theorem B57425369 : Blo 1226431 57425369 := bstep (se 2 (by rfl) ⟨21534513, by rfl⟩ : syracuseStep 57425369 = 43069027) B43069027
theorem B2760155 : Blo 1226431 2760155 := bstep (se 1 (by rfl) ⟨2070116, by rfl⟩ : syracuseStep 2760155 = 4140233) B4140233
theorem B2072027 : Blo 1226431 2072027 := bstep (se 1 (by rfl) ⟨1554020, by rfl⟩ : syracuseStep 2072027 = 3108041) B3108041
theorem B1228251 : Blo 1226431 1228251 := bstep (se 1 (by rfl) ⟨921188, by rfl⟩ : syracuseStep 1228251 = 1842377) B1842377
theorem B5594663 : Blo 1226431 5594663 := bstep (se 1 (by rfl) ⟨4195997, by rfl⟩ : syracuseStep 5594663 = 8391995) B8391995
theorem B9453095 : Blo 1226431 9453095 := bstep (se 1 (by rfl) ⟨7089821, by rfl⟩ : syracuseStep 9453095 = 14179643) B14179643
theorem B1228327 : Blo 1226431 1228327 := bstep (se 1 (by rfl) ⟨921245, by rfl⟩ : syracuseStep 1228327 = 1842491) B1842491
theorem B1228367 : Blo 1226431 1228367 := bstep (se 1 (by rfl) ⟨921275, by rfl⟩ : syracuseStep 1228367 = 1842551) B1842551
theorem B1228383 : Blo 1226431 1228383 := bstep (se 1 (by rfl) ⟨921287, by rfl⟩ : syracuseStep 1228383 = 1842575) B1842575
theorem B1228411 : Blo 1226431 1228411 := bstep (se 1 (by rfl) ⟨921308, by rfl⟩ : syracuseStep 1228411 = 1842617) B1842617
theorem B6995645 : Blo 1226431 6995645 := bstep (se 3 (by rfl) ⟨1311683, by rfl⟩ : syracuseStep 6995645 = 2623367) B2623367
theorem B2072263 : Blo 1226431 2072263 := bstep (se 1 (by rfl) ⟨1554197, by rfl⟩ : syracuseStep 2072263 = 3108395) B3108395
theorem B10485571 : Blo 1226431 10485571 := bstep (se 1 (by rfl) ⟨7864178, by rfl⟩ : syracuseStep 10485571 = 15728357) B15728357
theorem B2072425 : Blo 1226431 2072425 := bstep (se 2 (by rfl) ⟨777159, by rfl⟩ : syracuseStep 2072425 = 1554319) B1554319
theorem B2760623 : Blo 1226431 2760623 := bstep (se 1 (by rfl) ⟨2070467, by rfl⟩ : syracuseStep 2760623 = 4140935) B4140935
theorem B2621359 : Blo 1226431 2621359 := bstep (se 1 (by rfl) ⟨1966019, by rfl⟩ : syracuseStep 2621359 = 3932039) B3932039
theorem B1966007 : Blo 1226431 1966007 := bstep (se 1 (by rfl) ⟨1474505, by rfl⟩ : syracuseStep 1966007 = 2949011) B2949011
theorem B2760713 : Blo 1226431 2760713 := bstep (se 2 (by rfl) ⟨1035267, by rfl⟩ : syracuseStep 2760713 = 2070535) B2070535
theorem B6144025 : Blo 1226431 6144025 := bstep (se 2 (by rfl) ⟨2304009, by rfl⟩ : syracuseStep 6144025 = 4608019) B4608019
theorem B3932219 : Blo 1226431 3932219 := bstep (se 1 (by rfl) ⟨2949164, by rfl⟩ : syracuseStep 3932219 = 5898329) B5898329
theorem B79593677 : Blo 1226431 79593677 := bstep (se 3 (by rfl) ⟨14923814, by rfl⟩ : syracuseStep 79593677 = 29847629) B29847629
theorem B4423891 : Blo 1226431 4423891 := bstep (se 1 (by rfl) ⟨3317918, by rfl⟩ : syracuseStep 4423891 = 6635837) B6635837
theorem B4145363 : Blo 1226431 4145363 := bstep (se 1 (by rfl) ⟨3109022, by rfl⟩ : syracuseStep 4145363 = 6218045) B6218045
theorem B3932489 : Blo 1226431 3932489 := bstep (se 2 (by rfl) ⟨1474683, by rfl⟩ : syracuseStep 3932489 = 2949367) B2949367
theorem B2621803 : Blo 1226431 2621803 := bstep (se 1 (by rfl) ⟨1966352, by rfl⟩ : syracuseStep 2621803 = 3932705) B3932705
theorem B2761127 : Blo 1226431 2761127 := bstep (se 1 (by rfl) ⟨2070845, by rfl⟩ : syracuseStep 2761127 = 4141691) B4141691
theorem B1311175 : Blo 1226431 1311175 := bstep (se 1 (by rfl) ⟨983381, by rfl⟩ : syracuseStep 1311175 = 1966763) B1966763
theorem B4145633 : Blo 1226431 4145633 := bstep (se 2 (by rfl) ⟨1554612, by rfl⟩ : syracuseStep 4145633 = 3109225) B3109225
theorem B2761235 : Blo 1226431 2761235 := bstep (se 1 (by rfl) ⟨2070926, by rfl⟩ : syracuseStep 2761235 = 4141853) B4141853
theorem B1966655 : Blo 1226431 1966655 := bstep (se 1 (by rfl) ⟨1474991, by rfl⟩ : syracuseStep 1966655 = 2949983) B2949983
theorem B2761289 : Blo 1226431 2761289 := bstep (se 2 (by rfl) ⟨1035483, by rfl⟩ : syracuseStep 2761289 = 2070967) B2070967
theorem B5898905 : Blo 1226431 5898905 := bstep (se 2 (by rfl) ⟨2212089, by rfl⟩ : syracuseStep 5898905 = 4424179) B4424179
theorem B165815045 : Blo 1226431 165815045 := bstep (se 4 (by rfl) ⟨15545160, by rfl⟩ : syracuseStep 165815045 = 31090321) B31090321
theorem B2761703 : Blo 1226431 2761703 := bstep (se 1 (by rfl) ⟨2071277, by rfl⟩ : syracuseStep 2761703 = 4142555) B4142555
theorem B5243879 : Blo 1226431 5243879 := bstep (se 1 (by rfl) ⟨3932909, by rfl⟩ : syracuseStep 5243879 = 7865819) B7865819
theorem B3105935 : Blo 1226431 3105935 := bstep (se 1 (by rfl) ⟨2329451, by rfl⟩ : syracuseStep 3105935 = 4658903) B4658903
theorem B153134317 : Blo 1226431 153134317 := bstep (se 3 (by rfl) ⟨28712684, by rfl⟩ : syracuseStep 153134317 = 57425369) B57425369
theorem B4662623 : Blo 1226431 4662623 := bstep (se 1 (by rfl) ⟨3496967, by rfl⟩ : syracuseStep 4662623 = 6993935) B6993935
theorem B2762081 : Blo 1226431 2762081 := bstep (se 2 (by rfl) ⟨1035780, by rfl⟩ : syracuseStep 2762081 = 2071561) B2071561
theorem B3319163 : Blo 1226431 3319163 := bstep (se 1 (by rfl) ⟨2489372, by rfl⟩ : syracuseStep 3319163 = 4978745) B4978745
theorem B37766573 : Blo 1226431 37766573 := bstep (se 3 (by rfl) ⟨7081232, by rfl⟩ : syracuseStep 37766573 = 14162465) B14162465
theorem B13272493 : Blo 1226431 13272493 := bstep (se 3 (by rfl) ⟨2488592, by rfl⟩ : syracuseStep 13272493 = 4977185) B4977185
theorem B2762171 : Blo 1226431 2762171 := bstep (se 1 (by rfl) ⟨2071628, by rfl⟩ : syracuseStep 2762171 = 4143257) B4143257
theorem B3327419 : Blo 1226431 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B6211079 : Blo 1226431 6211079 := bstep (se 1 (by rfl) ⟨4658309, by rfl⟩ : syracuseStep 6211079 = 9316619) B9316619
theorem B4662791 : Blo 1226431 4662791 := bstep (se 1 (by rfl) ⟨3497093, by rfl⟩ : syracuseStep 4662791 = 6994187) B6994187
theorem B2762297 : Blo 1226431 2762297 := bstep (se 2 (by rfl) ⟨1035861, by rfl⟩ : syracuseStep 2762297 = 2071723) B2071723
theorem B2623033 : Blo 1226431 2623033 := bstep (se 2 (by rfl) ⟨983637, by rfl⟩ : syracuseStep 2623033 = 1967275) B1967275
theorem B10233479 : Blo 1226431 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B16787101 : Blo 1226431 16787101 := bstep (se 3 (by rfl) ⟨3147581, by rfl⟩ : syracuseStep 16787101 = 6295163) B6295163
theorem B17926019 : Blo 1226431 17926019 := bstep (se 1 (by rfl) ⟨13444514, by rfl⟩ : syracuseStep 17926019 = 26889029) B26889029
theorem B6211565 : Blo 1226431 6211565 := bstep (se 3 (by rfl) ⟨1164668, by rfl⟩ : syracuseStep 6211565 = 2329337) B2329337
theorem B4663277 : Blo 1226431 4663277 := bstep (se 3 (by rfl) ⟨874364, by rfl⟩ : syracuseStep 4663277 = 1748729) B1748729
theorem B2762963 : Blo 1226431 2762963 := bstep (se 1 (by rfl) ⟨2072222, by rfl⟩ : syracuseStep 2762963 = 4144445) B4144445
theorem B1681627 : Blo 1226431 1681627 := bstep (se 1 (by rfl) ⟨1261220, by rfl⟩ : syracuseStep 1681627 = 2522441) B2522441
theorem B4139261 : Blo 1226431 4139261 := bstep (se 3 (by rfl) ⟨776111, by rfl⟩ : syracuseStep 4139261 = 1552223) B1552223
theorem B2763017 : Blo 1226431 2763017 := bstep (se 2 (by rfl) ⟨1036131, by rfl⟩ : syracuseStep 2763017 = 2072263) B2072263
theorem B3729689 : Blo 1226431 3729689 := bstep (se 2 (by rfl) ⟨1398633, by rfl⟩ : syracuseStep 3729689 = 2797267) B2797267
theorem B20982077 : Blo 1226431 20982077 := bstep (se 3 (by rfl) ⟨3934139, by rfl⟩ : syracuseStep 20982077 = 7868279) B7868279
theorem B3729775 : Blo 1226431 3729775 := bstep (se 1 (by rfl) ⟨2797331, by rfl⟩ : syracuseStep 3729775 = 5594663) B5594663
theorem B6302063 : Blo 1226431 6302063 := bstep (se 1 (by rfl) ⟨4726547, by rfl⟩ : syracuseStep 6302063 = 9453095) B9453095
theorem B28330373 : Blo 1226431 28330373 := bstep (se 4 (by rfl) ⟨2655972, by rfl⟩ : syracuseStep 28330373 = 5311945) B5311945
theorem B6212051 : Blo 1226431 6212051 := bstep (se 1 (by rfl) ⟨4659038, by rfl⟩ : syracuseStep 6212051 = 9318077) B9318077
theorem B26560979 : Blo 1226431 26560979 := bstep (se 1 (by rfl) ⟨19920734, by rfl⟩ : syracuseStep 26560979 = 39841469) B39841469
theorem B4663763 : Blo 1226431 4663763 := bstep (se 1 (by rfl) ⟨3497822, by rfl⟩ : syracuseStep 4663763 = 6995645) B6995645
theorem B2763233 : Blo 1226431 2763233 := bstep (se 2 (by rfl) ⟨1036212, by rfl⟩ : syracuseStep 2763233 = 2072425) B2072425
theorem B2763539 : Blo 1226431 2763539 := bstep (se 1 (by rfl) ⟨2072654, by rfl⟩ : syracuseStep 2763539 = 4145309) B4145309
theorem B6212375 : Blo 1226431 6212375 := bstep (se 1 (by rfl) ⟨4659281, by rfl⟩ : syracuseStep 6212375 = 9318563) B9318563
theorem B7867307 : Blo 1226431 7867307 := bstep (se 1 (by rfl) ⟨5900480, by rfl⟩ : syracuseStep 7867307 = 11800961) B11800961
theorem B4140071 : Blo 1226431 4140071 := bstep (se 1 (by rfl) ⟨3105053, by rfl⟩ : syracuseStep 4140071 = 6210107) B6210107
theorem B3107879 : Blo 1226431 3107879 := bstep (se 1 (by rfl) ⟨2330909, by rfl⟩ : syracuseStep 3107879 = 4661819) B4661819
theorem B2763899 : Blo 1226431 2763899 := bstep (se 1 (by rfl) ⟨2072924, by rfl⟩ : syracuseStep 2763899 = 4145849) B4145849
theorem B3108233 : Blo 1226431 3108233 := bstep (se 2 (by rfl) ⟨1165587, by rfl⟩ : syracuseStep 3108233 = 2331175) B2331175
theorem B8973755 : Blo 1226431 8973755 := bstep (se 1 (by rfl) ⟨6730316, by rfl⟩ : syracuseStep 8973755 = 13460633) B13460633
theorem B4427207 : Blo 1226431 4427207 := bstep (se 1 (by rfl) ⟨3320405, by rfl⟩ : syracuseStep 4427207 = 6640811) B6640811
theorem B4140503 : Blo 1226431 4140503 := bstep (se 1 (by rfl) ⟨3105377, by rfl⟩ : syracuseStep 4140503 = 6210755) B6210755
theorem B1379911 : Blo 1226431 1379911 := bstep (se 1 (by rfl) ⟨1034933, by rfl⟩ : syracuseStep 1379911 = 2069867) B2069867
theorem B5246545 : Blo 1226431 5246545 := bstep (se 2 (by rfl) ⟨1967454, by rfl⟩ : syracuseStep 5246545 = 3934909) B3934909
theorem B5893715 : Blo 1226431 5893715 := bstep (se 1 (by rfl) ⟨4420286, by rfl⟩ : syracuseStep 5893715 = 8840573) B8840573
theorem B3493459 : Blo 1226431 3493459 := bstep (se 1 (by rfl) ⟨2620094, by rfl⟩ : syracuseStep 3493459 = 5240189) B5240189
theorem B1748575 : Blo 1226431 1748575 := bstep (se 1 (by rfl) ⟨1311431, by rfl⟩ : syracuseStep 1748575 = 2622863) B2622863
theorem B8400557 : Blo 1226431 8400557 := bstep (se 3 (by rfl) ⟨1575104, by rfl⟩ : syracuseStep 8400557 = 3150209) B3150209
theorem B6631121 : Blo 1226431 6631121 := bstep (se 2 (by rfl) ⟨2486670, by rfl⟩ : syracuseStep 6631121 = 4973341) B4973341
theorem B3362615 : Blo 1226431 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B33607493 : Blo 1226431 33607493 := bstep (se 4 (by rfl) ⟨3150702, by rfl⟩ : syracuseStep 33607493 = 6301405) B6301405
theorem B5238685 : Blo 1226431 5238685 := bstep (se 3 (by rfl) ⟨982253, by rfl⟩ : syracuseStep 5238685 = 1964507) B1964507
theorem B10489945 : Blo 1226431 10489945 := bstep (se 2 (by rfl) ⟨3933729, by rfl⟩ : syracuseStep 10489945 = 7867459) B7867459
theorem B1552603 : Blo 1226431 1552603 := bstep (se 1 (by rfl) ⟨1164452, by rfl⟩ : syracuseStep 1552603 = 2328905) B2328905
theorem B11350273 : Blo 1226431 11350273 := bstep (se 2 (by rfl) ⟨4256352, by rfl⟩ : syracuseStep 11350273 = 8512705) B8512705
theorem B5902595 : Blo 1226431 5902595 := bstep (se 1 (by rfl) ⟨4426946, by rfl⟩ : syracuseStep 5902595 = 8853893) B8853893
theorem B6213995 : Blo 1226431 6213995 := bstep (se 1 (by rfl) ⟨4660496, by rfl⟩ : syracuseStep 6213995 = 9320993) B9320993
theorem B10490219 : Blo 1226431 10490219 := bstep (se 1 (by rfl) ⟨7867664, by rfl⟩ : syracuseStep 10490219 = 15735329) B15735329
theorem B1380775 : Blo 1226431 1380775 := bstep (se 1 (by rfl) ⟨1035581, by rfl⟩ : syracuseStep 1380775 = 2071163) B2071163
theorem B4977071 : Blo 1226431 4977071 := bstep (se 1 (by rfl) ⟨3732803, by rfl⟩ : syracuseStep 4977071 = 7465607) B7465607
theorem B7868947 : Blo 1226431 7868947 := bstep (se 1 (by rfl) ⟨5901710, by rfl⟩ : syracuseStep 7868947 = 11803421) B11803421
theorem B13972013 : Blo 1226431 13972013 := bstep (se 3 (by rfl) ⟨2619752, by rfl⟩ : syracuseStep 13972013 = 5239505) B5239505
theorem B7860797 : Blo 1226431 7860797 := bstep (se 3 (by rfl) ⟨1473899, by rfl⟩ : syracuseStep 7860797 = 2947799) B2947799
theorem B1839737 : Blo 1226431 1839737 := bstep (se 2 (by rfl) ⟨689901, by rfl⟩ : syracuseStep 1839737 = 1379803) B1379803
theorem B1839791 : Blo 1226431 1839791 := bstep (se 1 (by rfl) ⟨1379843, by rfl⟩ : syracuseStep 1839791 = 2759687) B2759687
theorem B1839839 : Blo 1226431 1839839 := bstep (se 1 (by rfl) ⟨1379879, by rfl⟩ : syracuseStep 1839839 = 2759759) B2759759
theorem B2798327 : Blo 1226431 2798327 := bstep (se 1 (by rfl) ⟨2098745, by rfl⟩ : syracuseStep 2798327 = 4197491) B4197491
theorem B3494735 : Blo 1226431 3494735 := bstep (se 1 (by rfl) ⟨2621051, by rfl⟩ : syracuseStep 3494735 = 5242103) B5242103
theorem B7861157 : Blo 1226431 7861157 := bstep (se 4 (by rfl) ⟨736983, by rfl⟩ : syracuseStep 7861157 = 1473967) B1473967
theorem B1840103 : Blo 1226431 1840103 := bstep (se 1 (by rfl) ⟨1380077, by rfl⟩ : syracuseStep 1840103 = 2760155) B2760155
theorem B1381351 : Blo 1226431 1381351 := bstep (se 1 (by rfl) ⟨1036013, by rfl⟩ : syracuseStep 1381351 = 2072027) B2072027
theorem B13980761 : Blo 1226431 13980761 := bstep (se 2 (by rfl) ⟨5242785, by rfl⟩ : syracuseStep 13980761 = 10485571) B10485571
theorem B4142177 : Blo 1226431 4142177 := bstep (se 2 (by rfl) ⟨1553316, by rfl⟩ : syracuseStep 4142177 = 3106633) B3106633
theorem B1840361 : Blo 1226431 1840361 := bstep (se 2 (by rfl) ⟨690135, by rfl⟩ : syracuseStep 1840361 = 1380271) B1380271
theorem B3495145 : Blo 1226431 3495145 := bstep (se 2 (by rfl) ⟨1310679, by rfl⟩ : syracuseStep 3495145 = 2621359) B2621359
theorem B1840415 : Blo 1226431 1840415 := bstep (se 1 (by rfl) ⟨1380311, by rfl⟩ : syracuseStep 1840415 = 2760623) B2760623
theorem B5240173 : Blo 1226431 5240173 := bstep (se 3 (by rfl) ⟨982532, by rfl⟩ : syracuseStep 5240173 = 1965065) B1965065
theorem B7861697 : Blo 1226431 7861697 := bstep (se 2 (by rfl) ⟨2948136, by rfl⟩ : syracuseStep 7861697 = 5896273) B5896273
theorem B1840583 : Blo 1226431 1840583 := bstep (se 1 (by rfl) ⟨1380437, by rfl⟩ : syracuseStep 1840583 = 2760875) B2760875
theorem B10483181 : Blo 1226431 10483181 := bstep (se 3 (by rfl) ⟨1965596, by rfl⟩ : syracuseStep 10483181 = 3931193) B3931193
theorem B1226463 : Blo 1226431 1226463 := bstep (se 1 (by rfl) ⟨919847, by rfl⟩ : syracuseStep 1226463 = 1839695) B1839695
theorem B6215453 : Blo 1226431 6215453 := bstep (se 3 (by rfl) ⟨1165397, by rfl⟩ : syracuseStep 6215453 = 2330795) B2330795
theorem B1840937 : Blo 1226431 1840937 := bstep (se 2 (by rfl) ⟨690351, by rfl⟩ : syracuseStep 1840937 = 1380703) B1380703
theorem B1226543 : Blo 1226431 1226543 := bstep (se 1 (by rfl) ⟨919907, by rfl⟩ : syracuseStep 1226543 = 1839815) B1839815
theorem B2070319 : Blo 1226431 2070319 := bstep (se 1 (by rfl) ⟨1552739, by rfl⟩ : syracuseStep 2070319 = 3105479) B3105479
theorem B1840943 : Blo 1226431 1840943 := bstep (se 1 (by rfl) ⟨1380707, by rfl⟩ : syracuseStep 1840943 = 2761415) B2761415
theorem B1554223 : Blo 1226431 1554223 := bstep (se 1 (by rfl) ⟨1165667, by rfl⟩ : syracuseStep 1554223 = 2331335) B2331335
theorem B1226651 : Blo 1226431 1226651 := bstep (se 1 (by rfl) ⟨919988, by rfl⟩ : syracuseStep 1226651 = 1839977) B1839977
theorem B1226703 : Blo 1226431 1226703 := bstep (se 1 (by rfl) ⟨920027, by rfl⟩ : syracuseStep 1226703 = 1840055) B1840055
theorem B9451493 : Blo 1226431 9451493 := bstep (se 4 (by rfl) ⟨886077, by rfl⟩ : syracuseStep 9451493 = 1772155) B1772155
theorem B1226727 : Blo 1226431 1226727 := bstep (se 1 (by rfl) ⟨920045, by rfl⟩ : syracuseStep 1226727 = 1840091) B1840091
theorem B1841417 : Blo 1226431 1841417 := bstep (se 2 (by rfl) ⟨690531, by rfl⟩ : syracuseStep 1841417 = 1381063) B1381063
theorem B1227039 : Blo 1226431 1227039 := bstep (se 1 (by rfl) ⟨920279, by rfl⟩ : syracuseStep 1227039 = 1840559) B1840559
theorem B1227099 : Blo 1226431 1227099 := bstep (se 1 (by rfl) ⟨920324, by rfl⟩ : syracuseStep 1227099 = 1840649) B1840649
theorem B1227119 : Blo 1226431 1227119 := bstep (se 1 (by rfl) ⟨920339, by rfl⟩ : syracuseStep 1227119 = 1840679) B1840679
theorem B1841519 : Blo 1226431 1841519 := bstep (se 1 (by rfl) ⟨1381139, by rfl⟩ : syracuseStep 1841519 = 2762279) B2762279
theorem B1227175 : Blo 1226431 1227175 := bstep (se 1 (by rfl) ⟨920381, by rfl⟩ : syracuseStep 1227175 = 1840763) B1840763
theorem B4143527 : Blo 1226431 4143527 := bstep (se 1 (by rfl) ⟨3107645, by rfl⟩ : syracuseStep 4143527 = 6215291) B6215291
theorem B3496375 : Blo 1226431 3496375 := bstep (se 1 (by rfl) ⟨2622281, by rfl⟩ : syracuseStep 3496375 = 5244563) B5244563
theorem B4659707 : Blo 1226431 4659707 := bstep (se 1 (by rfl) ⟨3494780, by rfl⟩ : syracuseStep 4659707 = 6989561) B6989561
theorem B1227259 : Blo 1226431 1227259 := bstep (se 1 (by rfl) ⟨920444, by rfl⟩ : syracuseStep 1227259 = 1840889) B1840889
theorem B1227327 : Blo 1226431 1227327 := bstep (se 1 (by rfl) ⟨920495, by rfl⟩ : syracuseStep 1227327 = 1840991) B1840991
theorem B1227335 : Blo 1226431 1227335 := bstep (se 1 (by rfl) ⟨920501, by rfl⟩ : syracuseStep 1227335 = 1841003) B1841003
theorem B1841735 : Blo 1226431 1841735 := bstep (se 1 (by rfl) ⟨1381301, by rfl⟩ : syracuseStep 1841735 = 2762603) B2762603
theorem B4422217 : Blo 1226431 4422217 := bstep (se 2 (by rfl) ⟨1658331, by rfl⟩ : syracuseStep 4422217 = 3316663) B3316663
theorem B4143689 : Blo 1226431 4143689 := bstep (se 2 (by rfl) ⟨1553883, by rfl⟩ : syracuseStep 4143689 = 3107767) B3107767
theorem B1841771 : Blo 1226431 1841771 := bstep (se 1 (by rfl) ⟨1381328, by rfl⟩ : syracuseStep 1841771 = 2762657) B2762657
theorem B1227487 : Blo 1226431 1227487 := bstep (se 1 (by rfl) ⟨920615, by rfl⟩ : syracuseStep 1227487 = 1841231) B1841231
theorem B1227567 : Blo 1226431 1227567 := bstep (se 1 (by rfl) ⟨920675, by rfl⟩ : syracuseStep 1227567 = 1841351) B1841351
theorem B1841999 : Blo 1226431 1841999 := bstep (se 1 (by rfl) ⟨1381499, by rfl⟩ : syracuseStep 1841999 = 2762999) B2762999
theorem B2759579 : Blo 1226431 2759579 := bstep (se 1 (by rfl) ⟨2069684, by rfl⟩ : syracuseStep 2759579 = 4139369) B4139369
theorem B1227675 : Blo 1226431 1227675 := bstep (se 1 (by rfl) ⟨920756, by rfl⟩ : syracuseStep 1227675 = 1841513) B1841513
theorem B1227727 : Blo 1226431 1227727 := bstep (se 1 (by rfl) ⟨920795, by rfl⟩ : syracuseStep 1227727 = 1841591) B1841591
theorem B1227751 : Blo 1226431 1227751 := bstep (se 1 (by rfl) ⟨920813, by rfl⟩ : syracuseStep 1227751 = 1841627) B1841627
theorem B2759777 : Blo 1226431 2759777 := bstep (se 2 (by rfl) ⟨1034916, by rfl⟩ : syracuseStep 2759777 = 2069833) B2069833
theorem B1842395 : Blo 1226431 1842395 := bstep (se 1 (by rfl) ⟨1381796, by rfl⟩ : syracuseStep 1842395 = 2763593) B2763593
theorem B1473823 : Blo 1226431 1473823 := bstep (se 1 (by rfl) ⟨1105367, by rfl⟩ : syracuseStep 1473823 = 2210735) B2210735
theorem B1228063 : Blo 1226431 1228063 := bstep (se 1 (by rfl) ⟨921047, by rfl⟩ : syracuseStep 1228063 = 1842095) B1842095
theorem B2759975 : Blo 1226431 2759975 := bstep (se 1 (by rfl) ⟨2069981, by rfl⟩ : syracuseStep 2759975 = 4139963) B4139963
theorem B1228123 : Blo 1226431 1228123 := bstep (se 1 (by rfl) ⟨921092, by rfl⟩ : syracuseStep 1228123 = 1842185) B1842185
theorem B3317087 : Blo 1226431 3317087 := bstep (se 1 (by rfl) ⟨2487815, by rfl⟩ : syracuseStep 3317087 = 4975631) B4975631
theorem B1228143 : Blo 1226431 1228143 := bstep (se 1 (by rfl) ⟨921107, by rfl⟩ : syracuseStep 1228143 = 1842215) B1842215
theorem B1842569 : Blo 1226431 1842569 := bstep (se 2 (by rfl) ⟨690963, by rfl⟩ : syracuseStep 1842569 = 1381927) B1381927
theorem B1228199 : Blo 1226431 1228199 := bstep (se 1 (by rfl) ⟨921149, by rfl⟩ : syracuseStep 1228199 = 1842299) B1842299
theorem B4660679 : Blo 1226431 4660679 := bstep (se 1 (by rfl) ⟨3495509, by rfl⟩ : syracuseStep 4660679 = 6991019) B6991019
theorem B1228283 : Blo 1226431 1228283 := bstep (se 1 (by rfl) ⟨921212, by rfl⟩ : syracuseStep 1228283 = 1842425) B1842425
theorem B1228351 : Blo 1226431 1228351 := bstep (se 1 (by rfl) ⟨921263, by rfl⟩ : syracuseStep 1228351 = 1842527) B1842527
theorem B1228359 : Blo 1226431 1228359 := bstep (se 1 (by rfl) ⟨921269, by rfl⟩ : syracuseStep 1228359 = 1842539) B1842539
theorem B2760353 : Blo 1226431 2760353 := bstep (se 2 (by rfl) ⟨1035132, by rfl⟩ : syracuseStep 2760353 = 2070265) B2070265
theorem B14196539 : Blo 1226431 14196539 := bstep (se 1 (by rfl) ⟨10647404, by rfl⟩ : syracuseStep 14196539 = 21294809) B21294809
theorem B8396617 : Blo 1226431 8396617 := bstep (se 2 (by rfl) ⟨3148731, by rfl⟩ : syracuseStep 8396617 = 6297463) B6297463
theorem B1310671 : Blo 1226431 1310671 := bstep (se 1 (by rfl) ⟨983003, by rfl⟩ : syracuseStep 1310671 = 1966007) B1966007
theorem B8192033 : Blo 1226431 8192033 := bstep (se 2 (by rfl) ⟨3072012, by rfl⟩ : syracuseStep 8192033 = 6144025) B6144025
theorem B2621479 : Blo 1226431 2621479 := bstep (se 1 (by rfl) ⟨1966109, by rfl⟩ : syracuseStep 2621479 = 3932219) B3932219
theorem B2621659 : Blo 1226431 2621659 := bstep (se 1 (by rfl) ⟨1966244, by rfl⟩ : syracuseStep 2621659 = 3932489) B3932489
theorem B5898521 : Blo 1226431 5898521 := bstep (se 2 (by rfl) ⟨2211945, by rfl⟩ : syracuseStep 5898521 = 4423891) B4423891
theorem B3318047 : Blo 1226431 3318047 := bstep (se 1 (by rfl) ⟨2488535, by rfl⟩ : syracuseStep 3318047 = 4977071) B4977071
theorem B9314675 : Blo 1226431 9314675 := bstep (se 1 (by rfl) ⟨6986006, by rfl⟩ : syracuseStep 9314675 = 13972013) B13972013
theorem B1311103 : Blo 1226431 1311103 := bstep (se 1 (by rfl) ⟨983327, by rfl⟩ : syracuseStep 1311103 = 1966655) B1966655
theorem B3932603 : Blo 1226431 3932603 := bstep (se 1 (by rfl) ⟨2949452, by rfl⟩ : syracuseStep 3932603 = 5898905) B5898905
theorem B4973033 : Blo 1226431 4973033 := bstep (se 2 (by rfl) ⟨1864887, by rfl⟩ : syracuseStep 4973033 = 3729775) B3729775
theorem B110543363 : Blo 1226431 110543363 := bstep (se 1 (by rfl) ⟨82907522, by rfl⟩ : syracuseStep 110543363 = 165815045) B165815045
theorem B4661833 : Blo 1226431 4661833 := bstep (se 2 (by rfl) ⟨1748187, by rfl⟩ : syracuseStep 4661833 = 3496375) B3496375
theorem B2761451 : Blo 1226431 2761451 := bstep (se 1 (by rfl) ⟨2071088, by rfl⟩ : syracuseStep 2761451 = 4142177) B4142177
theorem B2212775 : Blo 1226431 2212775 := bstep (se 1 (by rfl) ⟨1659581, by rfl⟩ : syracuseStep 2212775 = 3319163) B3319163
theorem B6988787 : Blo 1226431 6988787 := bstep (se 1 (by rfl) ⟨5241590, by rfl⟩ : syracuseStep 6988787 = 10483181) B10483181
theorem B6300995 : Blo 1226431 6300995 := bstep (se 1 (by rfl) ⟨4725746, by rfl⟩ : syracuseStep 6300995 = 9451493) B9451493
theorem B2762351 : Blo 1226431 2762351 := bstep (se 1 (by rfl) ⟨2071763, by rfl⟩ : syracuseStep 2762351 = 4143527) B4143527
theorem B3106471 : Blo 1226431 3106471 := bstep (se 1 (by rfl) ⟨2329853, by rfl⟩ : syracuseStep 3106471 = 4659707) B4659707
theorem B2762459 : Blo 1226431 2762459 := bstep (se 1 (by rfl) ⟨2071844, by rfl⟩ : syracuseStep 2762459 = 4143689) B4143689
theorem B17696657 : Blo 1226431 17696657 := bstep (se 2 (by rfl) ⟨6636246, by rfl⟩ : syracuseStep 17696657 = 13272493) B13272493
theorem B5244871 : Blo 1226431 5244871 := bstep (se 1 (by rfl) ⟨3933653, by rfl⟩ : syracuseStep 5244871 = 7867307) B7867307
theorem B22382801 : Blo 1226431 22382801 := bstep (se 2 (by rfl) ⟨8393550, by rfl⟩ : syracuseStep 22382801 = 16787101) B16787101
theorem B5982503 : Blo 1226431 5982503 := bstep (se 1 (by rfl) ⟨4486877, by rfl⟩ : syracuseStep 5982503 = 8973755) B8973755
theorem B3107119 : Blo 1226431 3107119 := bstep (se 1 (by rfl) ⟨2330339, by rfl⟩ : syracuseStep 3107119 = 4660679) B4660679
theorem B2951471 : Blo 1226431 2951471 := bstep (se 1 (by rfl) ⟨2213603, by rfl⟩ : syracuseStep 2951471 = 4427207) B4427207
theorem B6990245 : Blo 1226431 6990245 := bstep (se 4 (by rfl) ⟨655335, by rfl⟩ : syracuseStep 6990245 = 1310671) B1310671
theorem B9464359 : Blo 1226431 9464359 := bstep (se 1 (by rfl) ⟨7098269, by rfl⟩ : syracuseStep 9464359 = 14196539) B14196539
theorem B13986593 : Blo 1226431 13986593 := bstep (se 2 (by rfl) ⟨5244972, by rfl⟩ : syracuseStep 13986593 = 10489945) B10489945
theorem B53062451 : Blo 1226431 53062451 := bstep (se 1 (by rfl) ⟨39796838, by rfl⟩ : syracuseStep 53062451 = 79593677) B79593677
theorem B2763575 : Blo 1226431 2763575 := bstep (se 1 (by rfl) ⟨2072681, by rfl⟩ : syracuseStep 2763575 = 4145363) B4145363
theorem B3935063 : Blo 1226431 3935063 := bstep (se 1 (by rfl) ⟨2951297, by rfl⟩ : syracuseStep 3935063 = 5902595) B5902595
theorem B2763755 : Blo 1226431 2763755 := bstep (se 1 (by rfl) ⟨2072816, by rfl⟩ : syracuseStep 2763755 = 4145633) B4145633
theorem B15133697 : Blo 1226431 15133697 := bstep (se 2 (by rfl) ⟨5675136, by rfl⟩ : syracuseStep 15133697 = 11350273) B11350273
theorem B2329823 : Blo 1226431 2329823 := bstep (se 1 (by rfl) ⟨1747367, by rfl⟩ : syracuseStep 2329823 = 3494735) B3494735
theorem B1748233 : Blo 1226431 1748233 := bstep (se 2 (by rfl) ⟨655587, by rfl⟩ : syracuseStep 1748233 = 1311175) B1311175
theorem B3108415 : Blo 1226431 3108415 := bstep (se 1 (by rfl) ⟨2331311, by rfl⟩ : syracuseStep 3108415 = 4662623) B4662623
theorem B25177715 : Blo 1226431 25177715 := bstep (se 1 (by rfl) ⟨18883286, by rfl⟩ : syracuseStep 25177715 = 37766573) B37766573
theorem B16805501 : Blo 1226431 16805501 := bstep (se 3 (by rfl) ⟨3151031, by rfl⟩ : syracuseStep 16805501 = 6302063) B6302063
theorem B4140719 : Blo 1226431 4140719 := bstep (se 1 (by rfl) ⟨3105539, by rfl⟩ : syracuseStep 4140719 = 6211079) B6211079
theorem B3108527 : Blo 1226431 3108527 := bstep (se 1 (by rfl) ⟨2331395, by rfl⟩ : syracuseStep 3108527 = 4662791) B4662791
theorem B4141043 : Blo 1226431 4141043 := bstep (se 1 (by rfl) ⟨3105782, by rfl⟩ : syracuseStep 4141043 = 6211565) B6211565
theorem B3108851 : Blo 1226431 3108851 := bstep (se 1 (by rfl) ⟨2331638, by rfl⟩ : syracuseStep 3108851 = 4663277) B4663277
theorem B2486459 : Blo 1226431 2486459 := bstep (se 1 (by rfl) ⟨1864844, by rfl⟩ : syracuseStep 2486459 = 3729689) B3729689
theorem B13988051 : Blo 1226431 13988051 := bstep (se 1 (by rfl) ⟨10491038, by rfl⟩ : syracuseStep 13988051 = 20982077) B20982077
theorem B18886915 : Blo 1226431 18886915 := bstep (se 1 (by rfl) ⟨14165186, by rfl⟩ : syracuseStep 18886915 = 28330373) B28330373
theorem B4141367 : Blo 1226431 4141367 := bstep (se 1 (by rfl) ⟨3106025, by rfl⟩ : syracuseStep 4141367 = 6212051) B6212051
theorem B17707319 : Blo 1226431 17707319 := bstep (se 1 (by rfl) ⟨13280489, by rfl⟩ : syracuseStep 17707319 = 26560979) B26560979
theorem B3109175 : Blo 1226431 3109175 := bstep (se 1 (by rfl) ⟨2331881, by rfl⟩ : syracuseStep 3109175 = 4663763) B4663763
theorem B22401485 : Blo 1226431 22401485 := bstep (se 3 (by rfl) ⟨4200278, by rfl⟩ : syracuseStep 22401485 = 8400557) B8400557
theorem B4141583 : Blo 1226431 4141583 := bstep (se 1 (by rfl) ⟨3106187, by rfl⟩ : syracuseStep 4141583 = 6212375) B6212375
theorem B1839719 : Blo 1226431 1839719 := bstep (se 1 (by rfl) ⟨1379789, by rfl⟩ : syracuseStep 1839719 = 2759579) B2759579
theorem B1839851 : Blo 1226431 1839851 := bstep (se 1 (by rfl) ⟨1379888, by rfl⟩ : syracuseStep 1839851 = 2759777) B2759777
theorem B1839881 : Blo 1226431 1839881 := bstep (se 2 (by rfl) ⟨689955, by rfl⟩ : syracuseStep 1839881 = 1379911) B1379911
theorem B4657945 : Blo 1226431 4657945 := bstep (se 2 (by rfl) ⟨1746729, by rfl⟩ : syracuseStep 4657945 = 3493459) B3493459
theorem B2331433 : Blo 1226431 2331433 := bstep (se 2 (by rfl) ⟨874287, by rfl⟩ : syracuseStep 2331433 = 1748575) B1748575
theorem B1839983 : Blo 1226431 1839983 := bstep (se 1 (by rfl) ⟨1379987, by rfl⟩ : syracuseStep 1839983 = 2759975) B2759975
theorem B3929143 : Blo 1226431 3929143 := bstep (se 1 (by rfl) ⟨2946857, by rfl⟩ : syracuseStep 3929143 = 5893715) B5893715
theorem B11195489 : Blo 1226431 11195489 := bstep (se 2 (by rfl) ⟨4198308, by rfl⟩ : syracuseStep 11195489 = 8396617) B8396617
theorem B1840235 : Blo 1226431 1840235 := bstep (se 1 (by rfl) ⟨1380176, by rfl⟩ : syracuseStep 1840235 = 2760353) B2760353
theorem B4420747 : Blo 1226431 4420747 := bstep (se 1 (by rfl) ⟨3315560, by rfl⟩ : syracuseStep 4420747 = 6631121) B6631121
theorem B2241743 : Blo 1226431 2241743 := bstep (se 1 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 2241743 = 3362615) B3362615
theorem B6984913 : Blo 1226431 6984913 := bstep (se 2 (by rfl) ⟨2619342, by rfl⟩ : syracuseStep 6984913 = 5238685) B5238685
theorem B1840475 : Blo 1226431 1840475 := bstep (se 1 (by rfl) ⟨1380356, by rfl⟩ : syracuseStep 1840475 = 2760713) B2760713
theorem B4142663 : Blo 1226431 4142663 := bstep (se 1 (by rfl) ⟨3106997, by rfl⟩ : syracuseStep 4142663 = 6213995) B6213995
theorem B6993479 : Blo 1226431 6993479 := bstep (se 1 (by rfl) ⟨5245109, by rfl⟩ : syracuseStep 6993479 = 10490219) B10490219
theorem B1840751 : Blo 1226431 1840751 := bstep (se 1 (by rfl) ⟨1380563, by rfl⟩ : syracuseStep 1840751 = 2761127) B2761127
theorem B2070137 : Blo 1226431 2070137 := bstep (se 2 (by rfl) ⟨776301, by rfl⟩ : syracuseStep 2070137 = 1552603) B1552603
theorem B2242169 : Blo 1226431 2242169 := bstep (se 2 (by rfl) ⟨840813, by rfl⟩ : syracuseStep 2242169 = 1681627) B1681627
theorem B13989509 : Blo 1226431 13989509 := bstep (se 4 (by rfl) ⟨1311516, by rfl⟩ : syracuseStep 13989509 = 2623033) B2623033
theorem B1840823 : Blo 1226431 1840823 := bstep (se 1 (by rfl) ⟨1380617, by rfl⟩ : syracuseStep 1840823 = 2761235) B2761235
theorem B5240531 : Blo 1226431 5240531 := bstep (se 1 (by rfl) ⟨3930398, by rfl⟩ : syracuseStep 5240531 = 7860797) B7860797
theorem B1840859 : Blo 1226431 1840859 := bstep (se 1 (by rfl) ⟨1380644, by rfl⟩ : syracuseStep 1840859 = 2761289) B2761289
theorem B1226491 : Blo 1226431 1226491 := bstep (se 1 (by rfl) ⟨919868, by rfl⟩ : syracuseStep 1226491 = 1839737) B1839737
theorem B1226527 : Blo 1226431 1226527 := bstep (se 1 (by rfl) ⟨919895, by rfl⟩ : syracuseStep 1226527 = 1839791) B1839791
theorem B3495737 : Blo 1226431 3495737 := bstep (se 2 (by rfl) ⟨1310901, by rfl⟩ : syracuseStep 3495737 = 2621803) B2621803
theorem B1226559 : Blo 1226431 1226559 := bstep (se 1 (by rfl) ⟨919919, by rfl⟩ : syracuseStep 1226559 = 1839839) B1839839
theorem B1841033 : Blo 1226431 1841033 := bstep (se 2 (by rfl) ⟨690387, by rfl⟩ : syracuseStep 1841033 = 1380775) B1380775
theorem B5240771 : Blo 1226431 5240771 := bstep (se 1 (by rfl) ⟨3930578, by rfl⟩ : syracuseStep 5240771 = 7861157) B7861157
theorem B1226735 : Blo 1226431 1226735 := bstep (se 1 (by rfl) ⟨920051, by rfl⟩ : syracuseStep 1226735 = 1840103) B1840103
theorem B1841135 : Blo 1226431 1841135 := bstep (se 1 (by rfl) ⟨1380851, by rfl⟩ : syracuseStep 1841135 = 2761703) B2761703
theorem B10491929 : Blo 1226431 10491929 := bstep (se 2 (by rfl) ⟨3934473, by rfl⟩ : syracuseStep 10491929 = 7868947) B7868947
theorem B9320507 : Blo 1226431 9320507 := bstep (se 1 (by rfl) ⟨6990380, by rfl⟩ : syracuseStep 9320507 = 13980761) B13980761
theorem B2070623 : Blo 1226431 2070623 := bstep (se 1 (by rfl) ⟨1552967, by rfl⟩ : syracuseStep 2070623 = 3105935) B3105935
theorem B5896289 : Blo 1226431 5896289 := bstep (se 2 (by rfl) ⟨2211108, by rfl⟩ : syracuseStep 5896289 = 4422217) B4422217
theorem B1226907 : Blo 1226431 1226907 := bstep (se 1 (by rfl) ⟨920180, by rfl⟩ : syracuseStep 1226907 = 1840361) B1840361
theorem B1226943 : Blo 1226431 1226943 := bstep (se 1 (by rfl) ⟨920207, by rfl⟩ : syracuseStep 1226943 = 1840415) B1840415
theorem B1841387 : Blo 1226431 1841387 := bstep (se 1 (by rfl) ⟨1381040, by rfl⟩ : syracuseStep 1841387 = 2762081) B2762081
theorem B1841447 : Blo 1226431 1841447 := bstep (se 1 (by rfl) ⟨1381085, by rfl⟩ : syracuseStep 1841447 = 2762171) B2762171
theorem B2218279 : Blo 1226431 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B5241131 : Blo 1226431 5241131 := bstep (se 1 (by rfl) ⟨3930848, by rfl⟩ : syracuseStep 5241131 = 7861697) B7861697
theorem B1227055 : Blo 1226431 1227055 := bstep (se 1 (by rfl) ⟨920291, by rfl⟩ : syracuseStep 1227055 = 1840583) B1840583
theorem B1841531 : Blo 1226431 1841531 := bstep (se 1 (by rfl) ⟨1381148, by rfl⟩ : syracuseStep 1841531 = 2762297) B2762297
theorem B6822319 : Blo 1226431 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B4143635 : Blo 1226431 4143635 := bstep (se 1 (by rfl) ⟨3107726, by rfl⟩ : syracuseStep 4143635 = 6215453) B6215453
theorem B1227291 : Blo 1226431 1227291 := bstep (se 1 (by rfl) ⟨920468, by rfl⟩ : syracuseStep 1227291 = 1840937) B1840937
theorem B1227295 : Blo 1226431 1227295 := bstep (se 1 (by rfl) ⟨920471, by rfl⟩ : syracuseStep 1227295 = 1840943) B1840943
theorem B816716357 : Blo 1226431 816716357 := bstep (se 4 (by rfl) ⟨76567158, by rfl⟩ : syracuseStep 816716357 = 153134317) B153134317
theorem B11950679 : Blo 1226431 11950679 := bstep (se 1 (by rfl) ⟨8963009, by rfl⟩ : syracuseStep 11950679 = 17926019) B17926019
theorem B1841801 : Blo 1226431 1841801 := bstep (se 2 (by rfl) ⟨690675, by rfl⟩ : syracuseStep 1841801 = 1381351) B1381351
theorem B1841975 : Blo 1226431 1841975 := bstep (se 1 (by rfl) ⟨1381481, by rfl⟩ : syracuseStep 1841975 = 2762963) B2762963
theorem B2759507 : Blo 1226431 2759507 := bstep (se 1 (by rfl) ⟨2069630, by rfl⟩ : syracuseStep 2759507 = 4139261) B4139261
theorem B1227611 : Blo 1226431 1227611 := bstep (se 1 (by rfl) ⟨920708, by rfl⟩ : syracuseStep 1227611 = 1841417) B1841417
theorem B1842011 : Blo 1226431 1842011 := bstep (se 1 (by rfl) ⟨1381508, by rfl⟩ : syracuseStep 1842011 = 2763017) B2763017
theorem B1227679 : Blo 1226431 1227679 := bstep (se 1 (by rfl) ⟨920759, by rfl⟩ : syracuseStep 1227679 = 1841519) B1841519
theorem B4660193 : Blo 1226431 4660193 := bstep (se 2 (by rfl) ⟨1747572, by rfl⟩ : syracuseStep 4660193 = 3495145) B3495145
theorem B1842155 : Blo 1226431 1842155 := bstep (se 1 (by rfl) ⟨1381616, by rfl⟩ : syracuseStep 1842155 = 2763233) B2763233
theorem B1965097 : Blo 1226431 1965097 := bstep (se 2 (by rfl) ⟨736911, by rfl⟩ : syracuseStep 1965097 = 1473823) B1473823
theorem B1227823 : Blo 1226431 1227823 := bstep (se 1 (by rfl) ⟨920867, by rfl⟩ : syracuseStep 1227823 = 1841735) B1841735
theorem B1227847 : Blo 1226431 1227847 := bstep (se 1 (by rfl) ⟨920885, by rfl⟩ : syracuseStep 1227847 = 1841771) B1841771
theorem B6986897 : Blo 1226431 6986897 := bstep (se 2 (by rfl) ⟨2620086, by rfl⟩ : syracuseStep 6986897 = 5240173) B5240173
theorem B1842359 : Blo 1226431 1842359 := bstep (se 1 (by rfl) ⟨1381769, by rfl⟩ : syracuseStep 1842359 = 2763539) B2763539
theorem B1227999 : Blo 1226431 1227999 := bstep (se 1 (by rfl) ⟨920999, by rfl⟩ : syracuseStep 1227999 = 1841999) B1841999
theorem B7462205 : Blo 1226431 7462205 := bstep (se 3 (by rfl) ⟨1399163, by rfl⟩ : syracuseStep 7462205 = 2798327) B2798327
theorem B2760047 : Blo 1226431 2760047 := bstep (se 1 (by rfl) ⟨2070035, by rfl⟩ : syracuseStep 2760047 = 4140071) B4140071
theorem B2071919 : Blo 1226431 2071919 := bstep (se 1 (by rfl) ⟨1553939, by rfl⟩ : syracuseStep 2071919 = 3107879) B3107879
theorem B1842599 : Blo 1226431 1842599 := bstep (se 1 (by rfl) ⟨1381949, by rfl⟩ : syracuseStep 1842599 = 2763899) B2763899
theorem B6995393 : Blo 1226431 6995393 := bstep (se 2 (by rfl) ⟨2623272, by rfl⟩ : syracuseStep 6995393 = 5246545) B5246545
theorem B1228263 : Blo 1226431 1228263 := bstep (se 1 (by rfl) ⟨921197, by rfl⟩ : syracuseStep 1228263 = 1842395) B1842395
theorem B2211391 : Blo 1226431 2211391 := bstep (se 1 (by rfl) ⟨1658543, by rfl⟩ : syracuseStep 2211391 = 3317087) B3317087
theorem B2072155 : Blo 1226431 2072155 := bstep (se 1 (by rfl) ⟨1554116, by rfl⟩ : syracuseStep 2072155 = 3108233) B3108233
theorem B1228379 : Blo 1226431 1228379 := bstep (se 1 (by rfl) ⟨921284, by rfl⟩ : syracuseStep 1228379 = 1842569) B1842569
theorem B2760335 : Blo 1226431 2760335 := bstep (se 1 (by rfl) ⟨2070251, by rfl⟩ : syracuseStep 2760335 = 4140503) B4140503
theorem B2760425 : Blo 1226431 2760425 := bstep (se 2 (by rfl) ⟨1035159, by rfl⟩ : syracuseStep 2760425 = 2070319) B2070319
theorem B2072297 : Blo 1226431 2072297 := bstep (se 2 (by rfl) ⟨777111, by rfl⟩ : syracuseStep 2072297 = 1554223) B1554223
theorem B22404995 : Blo 1226431 22404995 := bstep (se 1 (by rfl) ⟨16803746, by rfl⟩ : syracuseStep 22404995 = 33607493) B33607493
theorem B13983677 : Blo 1226431 13983677 := bstep (se 3 (by rfl) ⟨2621939, by rfl⟩ : syracuseStep 13983677 = 5243879) B5243879
theorem B3932347 : Blo 1226431 3932347 := bstep (se 1 (by rfl) ⟨2949260, by rfl⟩ : syracuseStep 3932347 = 5898521) B5898521
theorem B2212031 : Blo 1226431 2212031 := bstep (se 1 (by rfl) ⟨1659023, by rfl⟩ : syracuseStep 2212031 = 3318047) B3318047
theorem B2760911 : Blo 1226431 2760911 := bstep (se 1 (by rfl) ⟨2070683, by rfl⟩ : syracuseStep 2760911 = 4141367) B4141367
theorem B11804879 : Blo 1226431 11804879 := bstep (se 1 (by rfl) ⟨8853659, by rfl⟩ : syracuseStep 11804879 = 17707319) B17707319
theorem B2072783 : Blo 1226431 2072783 := bstep (se 1 (by rfl) ⟨1554587, by rfl⟩ : syracuseStep 2072783 = 3109175) B3109175
theorem B6209783 : Blo 1226431 6209783 := bstep (se 1 (by rfl) ⟨4657337, by rfl⟩ : syracuseStep 6209783 = 9314675) B9314675
theorem B2621735 : Blo 1226431 2621735 := bstep (se 1 (by rfl) ⟨1966301, by rfl⟩ : syracuseStep 2621735 = 3932603) B3932603
theorem B14934323 : Blo 1226431 14934323 := bstep (se 1 (by rfl) ⟨11200742, by rfl⟩ : syracuseStep 14934323 = 22401485) B22401485
theorem B73695575 : Blo 1226431 73695575 := bstep (se 1 (by rfl) ⟨55271681, by rfl⟩ : syracuseStep 73695575 = 110543363) B110543363
theorem B2761055 : Blo 1226431 2761055 := bstep (se 1 (by rfl) ⟨2070791, by rfl⟩ : syracuseStep 2761055 = 4141583) B4141583
theorem B2957705 : Blo 1226431 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B1475183 : Blo 1226431 1475183 := bstep (se 1 (by rfl) ⟨1106387, by rfl⟩ : syracuseStep 1475183 = 2212775) B2212775
theorem B23577317 : Blo 1226431 23577317 := bstep (se 4 (by rfl) ⟨2210373, by rfl⟩ : syracuseStep 23577317 = 4420747) B4420747
theorem B7463659 : Blo 1226431 7463659 := bstep (se 1 (by rfl) ⟨5597744, by rfl⟩ : syracuseStep 7463659 = 11195489) B11195489
theorem B16802653 : Blo 1226431 16802653 := bstep (se 3 (by rfl) ⟨3150497, by rfl⟩ : syracuseStep 16802653 = 6300995) B6300995
theorem B6210593 : Blo 1226431 6210593 := bstep (se 2 (by rfl) ⟨2328972, by rfl⟩ : syracuseStep 6210593 = 4657945) B4657945
theorem B2761775 : Blo 1226431 2761775 := bstep (se 1 (by rfl) ⟨2071331, by rfl⟩ : syracuseStep 2761775 = 4142663) B4142663
theorem B4662319 : Blo 1226431 4662319 := bstep (se 1 (by rfl) ⟨3496739, by rfl⟩ : syracuseStep 4662319 = 6993479) B6993479
theorem B11797771 : Blo 1226431 11797771 := bstep (se 1 (by rfl) ⟨8848328, by rfl⟩ : syracuseStep 11797771 = 17696657) B17696657
theorem B100730213 : Blo 1226431 100730213 := bstep (se 4 (by rfl) ⟨9443457, by rfl⟩ : syracuseStep 100730213 = 18886915) B18886915
theorem B9323909 : Blo 1226431 9323909 := bstep (se 4 (by rfl) ⟨874116, by rfl⟩ : syracuseStep 9323909 = 1748233) B1748233
theorem B1967647 : Blo 1226431 1967647 := bstep (se 1 (by rfl) ⟨1475735, by rfl⟩ : syracuseStep 1967647 = 2951471) B2951471
theorem B2762423 : Blo 1226431 2762423 := bstep (se 1 (by rfl) ⟨2071817, by rfl⟩ : syracuseStep 2762423 = 4143635) B4143635
theorem B9324395 : Blo 1226431 9324395 := bstep (se 1 (by rfl) ⟨6993296, by rfl⟩ : syracuseStep 9324395 = 13986593) B13986593
theorem B35374967 : Blo 1226431 35374967 := bstep (se 1 (by rfl) ⟨26531225, by rfl⟩ : syracuseStep 35374967 = 53062451) B53062451
theorem B2623375 : Blo 1226431 2623375 := bstep (se 1 (by rfl) ⟨1967531, by rfl⟩ : syracuseStep 2623375 = 3935063) B3935063
theorem B3106795 : Blo 1226431 3106795 := bstep (se 1 (by rfl) ⟨2330096, by rfl⟩ : syracuseStep 3106795 = 4660193) B4660193
theorem B2762873 : Blo 1226431 2762873 := bstep (se 2 (by rfl) ⟨1036077, by rfl⟩ : syracuseStep 2762873 = 2072155) B2072155
theorem B4974803 : Blo 1226431 4974803 := bstep (se 1 (by rfl) ⟨3731102, by rfl⟩ : syracuseStep 4974803 = 7462205) B7462205
theorem B4663595 : Blo 1226431 4663595 := bstep (se 1 (by rfl) ⟨3497696, by rfl⟩ : syracuseStep 4663595 = 6995393) B6995393
theorem B14936663 : Blo 1226431 14936663 := bstep (se 1 (by rfl) ⟨11202497, by rfl⟩ : syracuseStep 14936663 = 22404995) B22404995
theorem B9325367 : Blo 1226431 9325367 := bstep (se 1 (by rfl) ⟨6994025, by rfl⟩ : syracuseStep 9325367 = 13988051) B13988051
theorem B6630557 : Blo 1226431 6630557 := bstep (se 3 (by rfl) ⟨1243229, by rfl⟩ : syracuseStep 6630557 = 2486459) B2486459
theorem B1748137 : Blo 1226431 1748137 := bstep (se 2 (by rfl) ⟨655551, by rfl⟩ : syracuseStep 1748137 = 1311103) B1311103
theorem B9096425 : Blo 1226431 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B6212861 : Blo 1226431 6212861 := bstep (se 3 (by rfl) ⟨1164911, by rfl⟩ : syracuseStep 6212861 = 2329823) B2329823
theorem B12619145 : Blo 1226431 12619145 := bstep (se 2 (by rfl) ⟨4732179, by rfl⟩ : syracuseStep 12619145 = 9464359) B9464359
theorem B3108577 : Blo 1226431 3108577 := bstep (se 2 (by rfl) ⟨1165716, by rfl⟩ : syracuseStep 3108577 = 2331433) B2331433
theorem B1380091 : Blo 1226431 1380091 := bstep (se 1 (by rfl) ⟨1035068, by rfl⟩ : syracuseStep 1380091 = 2070137) B2070137
theorem B1494779 : Blo 1226431 1494779 := bstep (se 1 (by rfl) ⟨1121084, by rfl⟩ : syracuseStep 1494779 = 2242169) B2242169
theorem B9326339 : Blo 1226431 9326339 := bstep (se 1 (by rfl) ⟨6994754, by rfl⟩ : syracuseStep 9326339 = 13989509) B13989509
theorem B3493687 : Blo 1226431 3493687 := bstep (se 1 (by rfl) ⟨2620265, by rfl⟩ : syracuseStep 3493687 = 5240531) B5240531
theorem B3493847 : Blo 1226431 3493847 := bstep (se 1 (by rfl) ⟨2620385, by rfl⟩ : syracuseStep 3493847 = 5240771) B5240771
theorem B6213671 : Blo 1226431 6213671 := bstep (se 1 (by rfl) ⟨4660253, by rfl⟩ : syracuseStep 6213671 = 9320507) B9320507
theorem B1380415 : Blo 1226431 1380415 := bstep (se 1 (by rfl) ⟨1035311, by rfl⟩ : syracuseStep 1380415 = 2070623) B2070623
theorem B5238857 : Blo 1226431 5238857 := bstep (se 2 (by rfl) ⟨1964571, by rfl⟩ : syracuseStep 5238857 = 3929143) B3929143
theorem B14921867 : Blo 1226431 14921867 := bstep (se 1 (by rfl) ⟨11191400, by rfl⟩ : syracuseStep 14921867 = 22382801) B22382801
theorem B3494087 : Blo 1226431 3494087 := bstep (se 1 (by rfl) ⟨2620565, by rfl⟩ : syracuseStep 3494087 = 5241131) B5241131
theorem B1842383 : Blo 1226431 1842383 := bstep (se 1 (by rfl) ⟨1381787, by rfl⟩ : syracuseStep 1842383 = 2763575) B2763575
theorem B544477571 : Blo 1226431 544477571 := bstep (se 1 (by rfl) ⟨408358178, by rfl⟩ : syracuseStep 544477571 = 816716357) B816716357
theorem B7967119 : Blo 1226431 7967119 := bstep (se 1 (by rfl) ⟨5975339, by rfl⟩ : syracuseStep 7967119 = 11950679) B11950679
theorem B1839671 : Blo 1226431 1839671 := bstep (se 1 (by rfl) ⟨1379753, by rfl⟩ : syracuseStep 1839671 = 2759507) B2759507
theorem B10089131 : Blo 1226431 10089131 := bstep (se 1 (by rfl) ⟨7566848, by rfl⟩ : syracuseStep 10089131 = 15133697) B15133697
theorem B4657931 : Blo 1226431 4657931 := bstep (se 1 (by rfl) ⟨3493448, by rfl⟩ : syracuseStep 4657931 = 6986897) B6986897
theorem B4141961 : Blo 1226431 4141961 := bstep (se 2 (by rfl) ⟨1553235, by rfl⟩ : syracuseStep 4141961 = 3106471) B3106471
theorem B1840031 : Blo 1226431 1840031 := bstep (se 1 (by rfl) ⟨1380023, by rfl⟩ : syracuseStep 1840031 = 2760047) B2760047
theorem B1381279 : Blo 1226431 1381279 := bstep (se 1 (by rfl) ⟨1035959, by rfl⟩ : syracuseStep 1381279 = 2071919) B2071919
theorem B11203667 : Blo 1226431 11203667 := bstep (se 1 (by rfl) ⟨8402750, by rfl⟩ : syracuseStep 11203667 = 16805501) B16805501
theorem B1840223 : Blo 1226431 1840223 := bstep (se 1 (by rfl) ⟨1380167, by rfl⟩ : syracuseStep 1840223 = 2760335) B2760335
theorem B1840283 : Blo 1226431 1840283 := bstep (se 1 (by rfl) ⟨1380212, by rfl⟩ : syracuseStep 1840283 = 2760425) B2760425
theorem B1381531 : Blo 1226431 1381531 := bstep (se 1 (by rfl) ⟨1036148, by rfl⟩ : syracuseStep 1381531 = 2072297) B2072297
theorem B6993161 : Blo 1226431 6993161 := bstep (se 2 (by rfl) ⟨2622435, by rfl⟩ : syracuseStep 6993161 = 5244871) B5244871
theorem B5461355 : Blo 1226431 5461355 := bstep (se 1 (by rfl) ⟨4096016, by rfl⟩ : syracuseStep 5461355 = 8192033) B8192033
theorem B3495305 : Blo 1226431 3495305 := bstep (se 2 (by rfl) ⟨1310739, by rfl⟩ : syracuseStep 3495305 = 2621479) B2621479
theorem B3495545 : Blo 1226431 3495545 := bstep (se 2 (by rfl) ⟨1310829, by rfl⟩ : syracuseStep 3495545 = 2621659) B2621659
theorem B4142825 : Blo 1226431 4142825 := bstep (se 2 (by rfl) ⟨1553559, by rfl⟩ : syracuseStep 4142825 = 3107119) B3107119
theorem B1226479 : Blo 1226431 1226479 := bstep (se 1 (by rfl) ⟨919859, by rfl⟩ : syracuseStep 1226479 = 1839719) B1839719
theorem B63813365 : Blo 1226431 63813365 := bstep (se 5 (by rfl) ⟨2991251, by rfl⟩ : syracuseStep 63813365 = 5982503) B5982503
theorem B1226567 : Blo 1226431 1226567 := bstep (se 1 (by rfl) ⟨919925, by rfl⟩ : syracuseStep 1226567 = 1839851) B1839851
theorem B1840967 : Blo 1226431 1840967 := bstep (se 1 (by rfl) ⟨1380725, by rfl⟩ : syracuseStep 1840967 = 2761451) B2761451
theorem B1226587 : Blo 1226431 1226587 := bstep (se 1 (by rfl) ⟨919940, by rfl⟩ : syracuseStep 1226587 = 1839881) B1839881
theorem B5977981 : Blo 1226431 5977981 := bstep (se 3 (by rfl) ⟨1120871, by rfl⟩ : syracuseStep 5977981 = 2241743) B2241743
theorem B1226655 : Blo 1226431 1226655 := bstep (se 1 (by rfl) ⟨919991, by rfl⟩ : syracuseStep 1226655 = 1839983) B1839983
theorem B4659191 : Blo 1226431 4659191 := bstep (se 1 (by rfl) ⟨3494393, by rfl⟩ : syracuseStep 4659191 = 6988787) B6988787
theorem B1226823 : Blo 1226431 1226823 := bstep (se 1 (by rfl) ⟨920117, by rfl⟩ : syracuseStep 1226823 = 1840235) B1840235
theorem B6215777 : Blo 1226431 6215777 := bstep (se 2 (by rfl) ⟨2330916, by rfl⟩ : syracuseStep 6215777 = 4661833) B4661833
theorem B1226983 : Blo 1226431 1226983 := bstep (se 1 (by rfl) ⟨920237, by rfl⟩ : syracuseStep 1226983 = 1840475) B1840475
theorem B1227167 : Blo 1226431 1227167 := bstep (se 1 (by rfl) ⟨920375, by rfl⟩ : syracuseStep 1227167 = 1840751) B1840751
theorem B1841567 : Blo 1226431 1841567 := bstep (se 1 (by rfl) ⟨1381175, by rfl⟩ : syracuseStep 1841567 = 2762351) B2762351
theorem B1227215 : Blo 1226431 1227215 := bstep (se 1 (by rfl) ⟨920411, by rfl⟩ : syracuseStep 1227215 = 1840823) B1840823
theorem B1227239 : Blo 1226431 1227239 := bstep (se 1 (by rfl) ⟨920429, by rfl⟩ : syracuseStep 1227239 = 1840859) B1840859
theorem B1841639 : Blo 1226431 1841639 := bstep (se 1 (by rfl) ⟨1381229, by rfl⟩ : syracuseStep 1841639 = 2762459) B2762459
theorem B1227355 : Blo 1226431 1227355 := bstep (se 1 (by rfl) ⟨920516, by rfl⟩ : syracuseStep 1227355 = 1841033) B1841033
theorem B13261421 : Blo 1226431 13261421 := bstep (se 3 (by rfl) ⟨2486516, by rfl⟩ : syracuseStep 13261421 = 4973033) B4973033
theorem B1227423 : Blo 1226431 1227423 := bstep (se 1 (by rfl) ⟨920567, by rfl⟩ : syracuseStep 1227423 = 1841135) B1841135
theorem B6994619 : Blo 1226431 6994619 := bstep (se 1 (by rfl) ⟨5245964, by rfl⟩ : syracuseStep 6994619 = 10491929) B10491929
theorem B2620129 : Blo 1226431 2620129 := bstep (se 2 (by rfl) ⟨982548, by rfl⟩ : syracuseStep 2620129 = 1965097) B1965097
theorem B3930859 : Blo 1226431 3930859 := bstep (se 1 (by rfl) ⟨2948144, by rfl⟩ : syracuseStep 3930859 = 5896289) B5896289
theorem B1227591 : Blo 1226431 1227591 := bstep (se 1 (by rfl) ⟨920693, by rfl⟩ : syracuseStep 1227591 = 1841387) B1841387
theorem B1227631 : Blo 1226431 1227631 := bstep (se 1 (by rfl) ⟨920723, by rfl⟩ : syracuseStep 1227631 = 1841447) B1841447
theorem B1227687 : Blo 1226431 1227687 := bstep (se 1 (by rfl) ⟨920765, by rfl⟩ : syracuseStep 1227687 = 1841531) B1841531
theorem B9313217 : Blo 1226431 9313217 := bstep (se 2 (by rfl) ⟨3492456, by rfl⟩ : syracuseStep 9313217 = 6984913) B6984913
theorem B4660163 : Blo 1226431 4660163 := bstep (se 1 (by rfl) ⟨3495122, by rfl⟩ : syracuseStep 4660163 = 6990245) B6990245
theorem B1227867 : Blo 1226431 1227867 := bstep (se 1 (by rfl) ⟨920900, by rfl⟩ : syracuseStep 1227867 = 1841801) B1841801
theorem B1227983 : Blo 1226431 1227983 := bstep (se 1 (by rfl) ⟨920987, by rfl⟩ : syracuseStep 1227983 = 1841975) B1841975
theorem B2072567 : Blo 1226431 2072567 := bstep (se 1 (by rfl) ⟨1554425, by rfl⟩ : syracuseStep 2072567 = 3108851) B3108851
theorem B1228007 : Blo 1226431 1228007 := bstep (se 1 (by rfl) ⟨921005, by rfl⟩ : syracuseStep 1228007 = 1842011) B1842011
theorem B1228103 : Blo 1226431 1228103 := bstep (se 1 (by rfl) ⟨921077, by rfl⟩ : syracuseStep 1228103 = 1842155) B1842155
theorem B1842503 : Blo 1226431 1842503 := bstep (se 1 (by rfl) ⟨1381877, by rfl⟩ : syracuseStep 1842503 = 2763755) B2763755
theorem B2948521 : Blo 1226431 2948521 := bstep (se 2 (by rfl) ⟨1105695, by rfl⟩ : syracuseStep 2948521 = 2211391) B2211391
theorem B4144553 : Blo 1226431 4144553 := bstep (se 2 (by rfl) ⟨1554207, by rfl⟩ : syracuseStep 4144553 = 3108415) B3108415
theorem B1228239 : Blo 1226431 1228239 := bstep (se 1 (by rfl) ⟨921179, by rfl⟩ : syracuseStep 1228239 = 1842359) B1842359
theorem B9321965 : Blo 1226431 9321965 := bstep (se 3 (by rfl) ⟨1747868, by rfl⟩ : syracuseStep 9321965 = 3495737) B3495737
theorem B1228399 : Blo 1226431 1228399 := bstep (se 1 (by rfl) ⟨921299, by rfl⟩ : syracuseStep 1228399 = 1842599) B1842599
theorem B16785143 : Blo 1226431 16785143 := bstep (se 1 (by rfl) ⟨12588857, by rfl⟩ : syracuseStep 16785143 = 25177715) B25177715
theorem B2760479 : Blo 1226431 2760479 := bstep (se 1 (by rfl) ⟨2070359, by rfl⟩ : syracuseStep 2760479 = 4140719) B4140719
theorem B2072351 : Blo 1226431 2072351 := bstep (se 1 (by rfl) ⟨1554263, by rfl⟩ : syracuseStep 2072351 = 3108527) B3108527
theorem B9322451 : Blo 1226431 9322451 := bstep (se 1 (by rfl) ⟨6991838, by rfl⟩ : syracuseStep 9322451 = 13983677) B13983677
theorem B2760695 : Blo 1226431 2760695 := bstep (se 1 (by rfl) ⟨2070521, by rfl⟩ : syracuseStep 2760695 = 4141043) B4141043
theorem B5243129 : Blo 1226431 5243129 := bstep (se 2 (by rfl) ⟨1966173, by rfl⟩ : syracuseStep 5243129 = 3932347) B3932347
theorem B5898749 : Blo 1226431 5898749 := bstep (se 3 (by rfl) ⟨1106015, by rfl⟩ : syracuseStep 5898749 = 2212031) B2212031
theorem B3105287 : Blo 1226431 3105287 := bstep (se 1 (by rfl) ⟨2328965, by rfl⟩ : syracuseStep 3105287 = 4657931) B4657931
theorem B2761307 : Blo 1226431 2761307 := bstep (se 1 (by rfl) ⟨2070980, by rfl⟩ : syracuseStep 2761307 = 4141961) B4141961
theorem B4662107 : Blo 1226431 4662107 := bstep (se 1 (by rfl) ⟨3496580, by rfl⟩ : syracuseStep 4662107 = 6993161) B6993161
theorem B2761883 : Blo 1226431 2761883 := bstep (se 1 (by rfl) ⟨2071412, by rfl⟩ : syracuseStep 2761883 = 4142825) B4142825
theorem B42542243 : Blo 1226431 42542243 := bstep (se 1 (by rfl) ⟨31906682, by rfl⟩ : syracuseStep 42542243 = 63813365) B63813365
theorem B20964581 : Blo 1226431 20964581 := bstep (se 4 (by rfl) ⟨1965429, by rfl⟩ : syracuseStep 20964581 = 3930859) B3930859
theorem B3106127 : Blo 1226431 3106127 := bstep (se 1 (by rfl) ⟨2329595, by rfl⟩ : syracuseStep 3106127 = 4659191) B4659191
theorem B3933821 : Blo 1226431 3933821 := bstep (se 3 (by rfl) ⟨737591, by rfl⟩ : syracuseStep 3933821 = 1475183) B1475183
theorem B15730361 : Blo 1226431 15730361 := bstep (se 2 (by rfl) ⟨5898885, by rfl⟩ : syracuseStep 15730361 = 11797771) B11797771
theorem B26904349 : Blo 1226431 26904349 := bstep (se 3 (by rfl) ⟨5044565, by rfl⟩ : syracuseStep 26904349 = 10089131) B10089131
theorem B4663079 : Blo 1226431 4663079 := bstep (se 1 (by rfl) ⟨3497309, by rfl⟩ : syracuseStep 4663079 = 6994619) B6994619
theorem B3106775 : Blo 1226431 3106775 := bstep (se 1 (by rfl) ⟨2330081, by rfl⟩ : syracuseStep 3106775 = 4660163) B4660163
theorem B2623529 : Blo 1226431 2623529 := bstep (se 2 (by rfl) ⟨983823, by rfl⟩ : syracuseStep 2623529 = 1967647) B1967647
theorem B6064283 : Blo 1226431 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B2763035 : Blo 1226431 2763035 := bstep (se 1 (by rfl) ⟨2072276, by rfl⟩ : syracuseStep 2763035 = 4144553) B4144553
theorem B15944309 : Blo 1226431 15944309 := bstep (se 5 (by rfl) ⟨747389, by rfl⟩ : syracuseStep 15944309 = 1494779) B1494779
theorem B2329231 : Blo 1226431 2329231 := bstep (se 1 (by rfl) ⟨1746923, by rfl⟩ : syracuseStep 2329231 = 3493847) B3493847
theorem B3492571 : Blo 1226431 3492571 := bstep (se 1 (by rfl) ⟨2619428, by rfl⟩ : syracuseStep 3492571 = 5238857) B5238857
theorem B2329391 : Blo 1226431 2329391 := bstep (se 1 (by rfl) ⟨1747043, by rfl⟩ : syracuseStep 2329391 = 3494087) B3494087
theorem B4139855 : Blo 1226431 4139855 := bstep (se 1 (by rfl) ⟨3104891, by rfl⟩ : syracuseStep 4139855 = 6209783) B6209783
theorem B1747823 : Blo 1226431 1747823 := bstep (se 1 (by rfl) ⟨1310867, by rfl⟩ : syracuseStep 1747823 = 2621735) B2621735
theorem B9956215 : Blo 1226431 9956215 := bstep (se 1 (by rfl) ⟨7467161, by rfl⟩ : syracuseStep 9956215 = 14934323) B14934323
theorem B49130383 : Blo 1226431 49130383 := bstep (se 1 (by rfl) ⟨36847787, by rfl⟩ : syracuseStep 49130383 = 73695575) B73695575
theorem B39791645 : Blo 1226431 39791645 := bstep (se 3 (by rfl) ⟨7460933, by rfl⟩ : syracuseStep 39791645 = 14921867) B14921867
theorem B17681485 : Blo 1226431 17681485 := bstep (se 3 (by rfl) ⟨3315278, by rfl⟩ : syracuseStep 17681485 = 6630557) B6630557
theorem B4140395 : Blo 1226431 4140395 := bstep (se 1 (by rfl) ⟨3105296, by rfl⟩ : syracuseStep 4140395 = 6210593) B6210593
theorem B67153475 : Blo 1226431 67153475 := bstep (se 1 (by rfl) ⟨50365106, by rfl⟩ : syracuseStep 67153475 = 100730213) B100730213
theorem B2330203 : Blo 1226431 2330203 := bstep (se 1 (by rfl) ⟨1747652, by rfl⟩ : syracuseStep 2330203 = 3495305) B3495305
theorem B3493505 : Blo 1226431 3493505 := bstep (se 2 (by rfl) ⟨1310064, by rfl⟩ : syracuseStep 3493505 = 2620129) B2620129
theorem B2330363 : Blo 1226431 2330363 := bstep (se 1 (by rfl) ⟨1747772, by rfl⟩ : syracuseStep 2330363 = 3495545) B3495545
theorem B3109063 : Blo 1226431 3109063 := bstep (se 1 (by rfl) ⟨2331797, by rfl⟩ : syracuseStep 3109063 = 4663595) B4663595
theorem B2330849 : Blo 1226431 2330849 := bstep (se 2 (by rfl) ⟨874068, by rfl⟩ : syracuseStep 2330849 = 1748137) B1748137
theorem B9957775 : Blo 1226431 9957775 := bstep (se 1 (by rfl) ⟨7468331, by rfl⟩ : syracuseStep 9957775 = 14936663) B14936663
theorem B4141907 : Blo 1226431 4141907 := bstep (se 1 (by rfl) ⟨3106430, by rfl⟩ : syracuseStep 4141907 = 6212861) B6212861
theorem B6214643 : Blo 1226431 6214643 := bstep (se 1 (by rfl) ⟨4660982, by rfl⟩ : syracuseStep 6214643 = 9321965) B9321965
theorem B1840121 : Blo 1226431 1840121 := bstep (se 2 (by rfl) ⟨690045, by rfl⟩ : syracuseStep 1840121 = 1380091) B1380091
theorem B4658249 : Blo 1226431 4658249 := bstep (se 2 (by rfl) ⟨1746843, by rfl⟩ : syracuseStep 4658249 = 3493687) B3493687
theorem B1840319 : Blo 1226431 1840319 := bstep (se 1 (by rfl) ⟨1380239, by rfl⟩ : syracuseStep 1840319 = 2760479) B2760479
theorem B1381567 : Blo 1226431 1381567 := bstep (se 1 (by rfl) ⟨1036175, by rfl⟩ : syracuseStep 1381567 = 2072351) B2072351
theorem B6214967 : Blo 1226431 6214967 := bstep (se 1 (by rfl) ⟨4661225, by rfl⟩ : syracuseStep 6214967 = 9322451) B9322451
theorem B4142393 : Blo 1226431 4142393 := bstep (se 2 (by rfl) ⟨1553397, by rfl⟩ : syracuseStep 4142393 = 3106795) B3106795
theorem B1840463 : Blo 1226431 1840463 := bstep (se 1 (by rfl) ⟨1380347, by rfl⟩ : syracuseStep 1840463 = 2760695) B2760695
theorem B1381711 : Blo 1226431 1381711 := bstep (se 1 (by rfl) ⟨1036283, by rfl⟩ : syracuseStep 1381711 = 2072567) B2072567
theorem B4142447 : Blo 1226431 4142447 := bstep (se 1 (by rfl) ⟨3106835, by rfl⟩ : syracuseStep 4142447 = 6213671) B6213671
theorem B1840553 : Blo 1226431 1840553 := bstep (se 2 (by rfl) ⟨690207, by rfl⟩ : syracuseStep 1840553 = 1380415) B1380415
theorem B1840607 : Blo 1226431 1840607 := bstep (se 1 (by rfl) ⟨1380455, by rfl⟩ : syracuseStep 1840607 = 2760911) B2760911
theorem B1381855 : Blo 1226431 1381855 := bstep (se 1 (by rfl) ⟨1036391, by rfl⟩ : syracuseStep 1381855 = 2072783) B2072783
theorem B1840703 : Blo 1226431 1840703 := bstep (se 1 (by rfl) ⟨1380527, by rfl⟩ : syracuseStep 1840703 = 2761055) B2761055
theorem B362985047 : Blo 1226431 362985047 := bstep (se 1 (by rfl) ⟨272238785, by rfl⟩ : syracuseStep 362985047 = 544477571) B544477571
theorem B1971803 : Blo 1226431 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B1226447 : Blo 1226431 1226447 := bstep (se 1 (by rfl) ⟨919835, by rfl⟩ : syracuseStep 1226447 = 1839671) B1839671
theorem B15718211 : Blo 1226431 15718211 := bstep (se 1 (by rfl) ⟨11788658, by rfl⟩ : syracuseStep 15718211 = 23577317) B23577317
theorem B10622825 : Blo 1226431 10622825 := bstep (se 2 (by rfl) ⟨3983559, by rfl⟩ : syracuseStep 10622825 = 7967119) B7967119
theorem B31479677 : Blo 1226431 31479677 := bstep (se 3 (by rfl) ⟨5902439, by rfl⟩ : syracuseStep 31479677 = 11804879) B11804879
theorem B1226687 : Blo 1226431 1226687 := bstep (se 1 (by rfl) ⟨920015, by rfl⟩ : syracuseStep 1226687 = 1840031) B1840031
theorem B1841183 : Blo 1226431 1841183 := bstep (se 1 (by rfl) ⟨1380887, by rfl⟩ : syracuseStep 1841183 = 2761775) B2761775
theorem B7469111 : Blo 1226431 7469111 := bstep (se 1 (by rfl) ⟨5601833, by rfl⟩ : syracuseStep 7469111 = 11203667) B11203667
theorem B1226815 : Blo 1226431 1226815 := bstep (se 1 (by rfl) ⟨920111, by rfl⟩ : syracuseStep 1226815 = 1840223) B1840223
theorem B1226855 : Blo 1226431 1226855 := bstep (se 1 (by rfl) ⟨920141, by rfl⟩ : syracuseStep 1226855 = 1840283) B1840283
theorem B6215939 : Blo 1226431 6215939 := bstep (se 1 (by rfl) ⟨4661954, by rfl⟩ : syracuseStep 6215939 = 9323909) B9323909
theorem B14563613 : Blo 1226431 14563613 := bstep (se 3 (by rfl) ⟨2730677, by rfl⟩ : syracuseStep 14563613 = 5461355) B5461355
theorem B9951545 : Blo 1226431 9951545 := bstep (se 2 (by rfl) ⟨3731829, by rfl⟩ : syracuseStep 9951545 = 7463659) B7463659
theorem B1841615 : Blo 1226431 1841615 := bstep (se 1 (by rfl) ⟨1381211, by rfl⟩ : syracuseStep 1841615 = 2762423) B2762423
theorem B22403537 : Blo 1226431 22403537 := bstep (se 2 (by rfl) ⟨8401326, by rfl⟩ : syracuseStep 22403537 = 16802653) B16802653
theorem B1841705 : Blo 1226431 1841705 := bstep (se 2 (by rfl) ⟨690639, by rfl⟩ : syracuseStep 1841705 = 1381279) B1381279
theorem B1227311 : Blo 1226431 1227311 := bstep (se 1 (by rfl) ⟨920483, by rfl⟩ : syracuseStep 1227311 = 1840967) B1840967
theorem B6216263 : Blo 1226431 6216263 := bstep (se 1 (by rfl) ⟨4662197, by rfl⟩ : syracuseStep 6216263 = 9324395) B9324395
theorem B23583311 : Blo 1226431 23583311 := bstep (se 1 (by rfl) ⟨17687483, by rfl⟩ : syracuseStep 23583311 = 35374967) B35374967
theorem B6216425 : Blo 1226431 6216425 := bstep (se 2 (by rfl) ⟨2331159, by rfl⟩ : syracuseStep 6216425 = 4662319) B4662319
theorem B4143851 : Blo 1226431 4143851 := bstep (se 1 (by rfl) ⟨3107888, by rfl⟩ : syracuseStep 4143851 = 6215777) B6215777
theorem B1841915 : Blo 1226431 1841915 := bstep (se 1 (by rfl) ⟨1381436, by rfl⟩ : syracuseStep 1841915 = 2762873) B2762873
theorem B3316535 : Blo 1226431 3316535 := bstep (se 1 (by rfl) ⟨2487401, by rfl⟩ : syracuseStep 3316535 = 4974803) B4974803
theorem B1842041 : Blo 1226431 1842041 := bstep (se 2 (by rfl) ⟨690765, by rfl⟩ : syracuseStep 1842041 = 1381531) B1381531
theorem B1227711 : Blo 1226431 1227711 := bstep (se 1 (by rfl) ⟨920783, by rfl⟩ : syracuseStep 1227711 = 1841567) B1841567
theorem B35363789 : Blo 1226431 35363789 := bstep (se 3 (by rfl) ⟨6630710, by rfl⟩ : syracuseStep 35363789 = 13261421) B13261421
theorem B1227759 : Blo 1226431 1227759 := bstep (se 1 (by rfl) ⟨920819, by rfl⟩ : syracuseStep 1227759 = 1841639) B1841639
theorem B6216911 : Blo 1226431 6216911 := bstep (se 1 (by rfl) ⟨4662683, by rfl⟩ : syracuseStep 6216911 = 9325367) B9325367
theorem B3931361 : Blo 1226431 3931361 := bstep (se 2 (by rfl) ⟨1474260, by rfl⟩ : syracuseStep 3931361 = 2948521) B2948521
theorem B6208811 : Blo 1226431 6208811 := bstep (se 1 (by rfl) ⟨4656608, by rfl⟩ : syracuseStep 6208811 = 9313217) B9313217
theorem B31882565 : Blo 1226431 31882565 := bstep (se 4 (by rfl) ⟨2988990, by rfl⟩ : syracuseStep 31882565 = 5977981) B5977981
theorem B1228255 : Blo 1226431 1228255 := bstep (se 1 (by rfl) ⟨921191, by rfl⟩ : syracuseStep 1228255 = 1842383) B1842383
theorem B1228335 : Blo 1226431 1228335 := bstep (se 1 (by rfl) ⟨921251, by rfl⟩ : syracuseStep 1228335 = 1842503) B1842503
theorem B8412763 : Blo 1226431 8412763 := bstep (se 1 (by rfl) ⟨6309572, by rfl⟩ : syracuseStep 8412763 = 12619145) B12619145
theorem B4144769 : Blo 1226431 4144769 := bstep (se 2 (by rfl) ⟨1554288, by rfl⟩ : syracuseStep 4144769 = 3108577) B3108577
theorem B11190095 : Blo 1226431 11190095 := bstep (se 1 (by rfl) ⟨8392571, by rfl⟩ : syracuseStep 11190095 = 16785143) B16785143
theorem B6217559 : Blo 1226431 6217559 := bstep (se 1 (by rfl) ⟨4663169, by rfl⟩ : syracuseStep 6217559 = 9326339) B9326339
theorem B3497833 : Blo 1226431 3497833 := bstep (se 2 (by rfl) ⟨1311687, by rfl⟩ : syracuseStep 3497833 = 2623375) B2623375
theorem B6996077 : Blo 1226431 6996077 := bstep (se 3 (by rfl) ⟨1311764, by rfl⟩ : syracuseStep 6996077 = 2623529) B2623529
theorem B4145417 : Blo 1226431 4145417 := bstep (se 2 (by rfl) ⟨1554531, by rfl⟩ : syracuseStep 4145417 = 3109063) B3109063
theorem B2761271 : Blo 1226431 2761271 := bstep (se 1 (by rfl) ⟨2070953, by rfl⟩ : syracuseStep 2761271 = 4141907) B4141907
theorem B3105499 : Blo 1226431 3105499 := bstep (se 1 (by rfl) ⟨2329124, by rfl⟩ : syracuseStep 3105499 = 4658249) B4658249
theorem B28361495 : Blo 1226431 28361495 := bstep (se 1 (by rfl) ⟨21271121, by rfl⟩ : syracuseStep 28361495 = 42542243) B42542243
theorem B13976387 : Blo 1226431 13976387 := bstep (se 1 (by rfl) ⟨10482290, by rfl⟩ : syracuseStep 13976387 = 20964581) B20964581
theorem B3105641 : Blo 1226431 3105641 := bstep (se 2 (by rfl) ⟨1164615, by rfl⟩ : syracuseStep 3105641 = 2329231) B2329231
theorem B2761595 : Blo 1226431 2761595 := bstep (se 1 (by rfl) ⟨2071196, by rfl⟩ : syracuseStep 2761595 = 4142393) B4142393
theorem B2761631 : Blo 1226431 2761631 := bstep (se 1 (by rfl) ⟨2071223, by rfl⟩ : syracuseStep 2761631 = 4142447) B4142447
theorem B2622547 : Blo 1226431 2622547 := bstep (se 1 (by rfl) ⟨1966910, by rfl⟩ : syracuseStep 2622547 = 3933821) B3933821
theorem B10486907 : Blo 1226431 10486907 := bstep (se 1 (by rfl) ⟨7865180, by rfl⟩ : syracuseStep 10486907 = 15730361) B15730361
theorem B10478807 : Blo 1226431 10478807 := bstep (se 1 (by rfl) ⟨7859105, by rfl⟩ : syracuseStep 10478807 = 15718211) B15718211
theorem B15729997 : Blo 1226431 15729997 := bstep (se 3 (by rfl) ⟨2949374, by rfl⟩ : syracuseStep 15729997 = 5898749) B5898749
theorem B9709075 : Blo 1226431 9709075 := bstep (se 1 (by rfl) ⟨7281806, by rfl⟩ : syracuseStep 9709075 = 14563613) B14563613
theorem B14935691 : Blo 1226431 14935691 := bstep (se 1 (by rfl) ⟨11201768, by rfl⟩ : syracuseStep 14935691 = 22403537) B22403537
theorem B15722207 : Blo 1226431 15722207 := bstep (se 1 (by rfl) ⟨11791655, by rfl⟩ : syracuseStep 15722207 = 23583311) B23583311
theorem B2762567 : Blo 1226431 2762567 := bstep (se 1 (by rfl) ⟨2071925, by rfl⟩ : syracuseStep 2762567 = 4143851) B4143851
theorem B26527763 : Blo 1226431 26527763 := bstep (se 1 (by rfl) ⟨19895822, by rfl⟩ : syracuseStep 26527763 = 39791645) B39791645
theorem B11217017 : Blo 1226431 11217017 := bstep (se 2 (by rfl) ⟨4206381, by rfl⟩ : syracuseStep 11217017 = 8412763) B8412763
theorem B3106937 : Blo 1226431 3106937 := bstep (se 2 (by rfl) ⟨1165101, by rfl⟩ : syracuseStep 3106937 = 2330203) B2330203
theorem B4139207 : Blo 1226431 4139207 := bstep (se 1 (by rfl) ⟨3104405, by rfl⟩ : syracuseStep 4139207 = 6208811) B6208811
theorem B2329003 : Blo 1226431 2329003 := bstep (se 1 (by rfl) ⟨1746752, by rfl⟩ : syracuseStep 2329003 = 3493505) B3493505
theorem B2763179 : Blo 1226431 2763179 := bstep (se 1 (by rfl) ⟨2072384, by rfl⟩ : syracuseStep 2763179 = 4144769) B4144769
theorem B4663777 : Blo 1226431 4663777 := bstep (se 2 (by rfl) ⟨1748916, by rfl⟩ : syracuseStep 4663777 = 3497833) B3497833
theorem B3108071 : Blo 1226431 3108071 := bstep (se 1 (by rfl) ⟨2331053, by rfl⟩ : syracuseStep 3108071 = 4662107) B4662107
theorem B26537453 : Blo 1226431 26537453 := bstep (se 3 (by rfl) ⟨4975772, by rfl⟩ : syracuseStep 26537453 = 9951545) B9951545
theorem B4656761 : Blo 1226431 4656761 := bstep (se 2 (by rfl) ⟨1746285, by rfl⟩ : syracuseStep 4656761 = 3492571) B3492571
theorem B65507177 : Blo 1226431 65507177 := bstep (se 2 (by rfl) ⟨24565191, by rfl⟩ : syracuseStep 65507177 = 49130383) B49130383
theorem B3108719 : Blo 1226431 3108719 := bstep (se 1 (by rfl) ⟨2331539, by rfl⟩ : syracuseStep 3108719 = 4663079) B4663079
theorem B7081883 : Blo 1226431 7081883 := bstep (se 1 (by rfl) ⟨5311412, by rfl⟩ : syracuseStep 7081883 = 10622825) B10622825
theorem B4042855 : Blo 1226431 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B10629539 : Blo 1226431 10629539 := bstep (se 1 (by rfl) ⟨7972154, by rfl⟩ : syracuseStep 10629539 = 15944309) B15944309
theorem B1552927 : Blo 1226431 1552927 := bstep (se 1 (by rfl) ⟨1164695, by rfl⟩ : syracuseStep 1552927 = 2329391) B2329391
theorem B21255043 : Blo 1226431 21255043 := bstep (se 1 (by rfl) ⟨15941282, by rfl⟩ : syracuseStep 21255043 = 31882565) B31882565
theorem B1553575 : Blo 1226431 1553575 := bstep (se 1 (by rfl) ⟨1165181, by rfl⟩ : syracuseStep 1553575 = 2330363) B2330363
theorem B7460063 : Blo 1226431 7460063 := bstep (se 1 (by rfl) ⟨5595047, by rfl⟩ : syracuseStep 7460063 = 11190095) B11190095
theorem B1553899 : Blo 1226431 1553899 := bstep (se 1 (by rfl) ⟨1165424, by rfl⟩ : syracuseStep 1553899 = 2330849) B2330849
theorem B3495419 : Blo 1226431 3495419 := bstep (se 1 (by rfl) ⟨2621564, by rfl⟩ : syracuseStep 3495419 = 5243129) B5243129
theorem B2070191 : Blo 1226431 2070191 := bstep (se 1 (by rfl) ⟨1552643, by rfl⟩ : syracuseStep 2070191 = 3105287) B3105287
theorem B1840871 : Blo 1226431 1840871 := bstep (se 1 (by rfl) ⟨1380653, by rfl⟩ : syracuseStep 1840871 = 2761307) B2761307
theorem B13277033 : Blo 1226431 13277033 := bstep (se 2 (by rfl) ⟨4978887, by rfl⟩ : syracuseStep 13277033 = 9957775) B9957775
theorem B4143095 : Blo 1226431 4143095 := bstep (se 1 (by rfl) ⟨3107321, by rfl⟩ : syracuseStep 4143095 = 6214643) B6214643
theorem B1226747 : Blo 1226431 1226747 := bstep (se 1 (by rfl) ⟨920060, by rfl⟩ : syracuseStep 1226747 = 1840121) B1840121
theorem B1841255 : Blo 1226431 1841255 := bstep (se 1 (by rfl) ⟨1380941, by rfl⟩ : syracuseStep 1841255 = 2761883) B2761883
theorem B1226879 : Blo 1226431 1226879 := bstep (se 1 (by rfl) ⟨920159, by rfl⟩ : syracuseStep 1226879 = 1840319) B1840319
theorem B4143311 : Blo 1226431 4143311 := bstep (se 1 (by rfl) ⟨3107483, by rfl⟩ : syracuseStep 4143311 = 6214967) B6214967
theorem B1226975 : Blo 1226431 1226975 := bstep (se 1 (by rfl) ⟨920231, by rfl⟩ : syracuseStep 1226975 = 1840463) B1840463
theorem B2070751 : Blo 1226431 2070751 := bstep (se 1 (by rfl) ⟨1553063, by rfl⟩ : syracuseStep 2070751 = 3106127) B3106127
theorem B1227035 : Blo 1226431 1227035 := bstep (se 1 (by rfl) ⟨920276, by rfl⟩ : syracuseStep 1227035 = 1840553) B1840553
theorem B1227071 : Blo 1226431 1227071 := bstep (se 1 (by rfl) ⟨920303, by rfl⟩ : syracuseStep 1227071 = 1840607) B1840607
theorem B1227135 : Blo 1226431 1227135 := bstep (se 1 (by rfl) ⟨920351, by rfl⟩ : syracuseStep 1227135 = 1840703) B1840703
theorem B241990031 : Blo 1226431 241990031 := bstep (se 1 (by rfl) ⟨181492523, by rfl⟩ : syracuseStep 241990031 = 362985047) B362985047
theorem B20986451 : Blo 1226431 20986451 := bstep (se 1 (by rfl) ⟨15739838, by rfl⟩ : syracuseStep 20986451 = 31479677) B31479677
theorem B2071183 : Blo 1226431 2071183 := bstep (se 1 (by rfl) ⟨1553387, by rfl⟩ : syracuseStep 2071183 = 3106775) B3106775
theorem B1227455 : Blo 1226431 1227455 := bstep (se 1 (by rfl) ⟨920591, by rfl⟩ : syracuseStep 1227455 = 1841183) B1841183
theorem B4979407 : Blo 1226431 4979407 := bstep (se 1 (by rfl) ⟨3734555, by rfl⟩ : syracuseStep 4979407 = 7469111) B7469111
theorem B23575313 : Blo 1226431 23575313 := bstep (se 2 (by rfl) ⟨8840742, by rfl⟩ : syracuseStep 23575313 = 17681485) B17681485
theorem B4143959 : Blo 1226431 4143959 := bstep (se 1 (by rfl) ⟨3107969, by rfl⟩ : syracuseStep 4143959 = 6215939) B6215939
theorem B1842023 : Blo 1226431 1842023 := bstep (se 1 (by rfl) ⟨1381517, by rfl⟩ : syracuseStep 1842023 = 2763035) B2763035
theorem B5258141 : Blo 1226431 5258141 := bstep (se 3 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 5258141 = 1971803) B1971803
theorem B1842089 : Blo 1226431 1842089 := bstep (se 2 (by rfl) ⟨690783, by rfl⟩ : syracuseStep 1842089 = 1381567) B1381567
theorem B1227743 : Blo 1226431 1227743 := bstep (se 1 (by rfl) ⟨920807, by rfl⟩ : syracuseStep 1227743 = 1841615) B1841615
theorem B1227803 : Blo 1226431 1227803 := bstep (se 1 (by rfl) ⟨920852, by rfl⟩ : syracuseStep 1227803 = 1841705) B1841705
theorem B4144175 : Blo 1226431 4144175 := bstep (se 1 (by rfl) ⟨3108131, by rfl⟩ : syracuseStep 4144175 = 6216263) B6216263
theorem B1842281 : Blo 1226431 1842281 := bstep (se 2 (by rfl) ⟨690855, by rfl⟩ : syracuseStep 1842281 = 1381711) B1381711
theorem B4144283 : Blo 1226431 4144283 := bstep (se 1 (by rfl) ⟨3108212, by rfl⟩ : syracuseStep 4144283 = 6216425) B6216425
theorem B1227943 : Blo 1226431 1227943 := bstep (se 1 (by rfl) ⟨920957, by rfl⟩ : syracuseStep 1227943 = 1841915) B1841915
theorem B2211023 : Blo 1226431 2211023 := bstep (se 1 (by rfl) ⟨1658267, by rfl⟩ : syracuseStep 2211023 = 3316535) B3316535
theorem B2759903 : Blo 1226431 2759903 := bstep (se 1 (by rfl) ⟨2069927, by rfl⟩ : syracuseStep 2759903 = 4139855) B4139855
theorem B1228027 : Blo 1226431 1228027 := bstep (se 1 (by rfl) ⟨921020, by rfl⟩ : syracuseStep 1228027 = 1842041) B1842041
theorem B53099813 : Blo 1226431 53099813 := bstep (se 4 (by rfl) ⟨4978107, by rfl⟩ : syracuseStep 53099813 = 9956215) B9956215
theorem B1842473 : Blo 1226431 1842473 := bstep (se 2 (by rfl) ⟨690927, by rfl⟩ : syracuseStep 1842473 = 1381855) B1381855
theorem B23575859 : Blo 1226431 23575859 := bstep (se 1 (by rfl) ⟨17681894, by rfl⟩ : syracuseStep 23575859 = 35363789) B35363789
theorem B4144607 : Blo 1226431 4144607 := bstep (se 1 (by rfl) ⟨3108455, by rfl⟩ : syracuseStep 4144607 = 6216911) B6216911
theorem B2620907 : Blo 1226431 2620907 := bstep (se 1 (by rfl) ⟨1965680, by rfl⟩ : syracuseStep 2620907 = 3931361) B3931361
theorem B2760263 : Blo 1226431 2760263 := bstep (se 1 (by rfl) ⟨2070197, by rfl⟩ : syracuseStep 2760263 = 4140395) B4140395
theorem B4660861 : Blo 1226431 4660861 := bstep (se 3 (by rfl) ⟨873911, by rfl⟩ : syracuseStep 4660861 = 1747823) B1747823
theorem B35872465 : Blo 1226431 35872465 := bstep (se 2 (by rfl) ⟨13452174, by rfl⟩ : syracuseStep 35872465 = 26904349) B26904349
theorem B44768983 : Blo 1226431 44768983 := bstep (se 1 (by rfl) ⟨33576737, by rfl⟩ : syracuseStep 44768983 = 67153475) B67153475
theorem B4145039 : Blo 1226431 4145039 := bstep (se 1 (by rfl) ⟨3108779, by rfl⟩ : syracuseStep 4145039 = 6217559) B6217559
theorem B51781733 : Blo 1226431 51781733 := bstep (se 4 (by rfl) ⟨4854537, by rfl⟩ : syracuseStep 51781733 = 9709075) B9709075
theorem B5390473 : Blo 1226431 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B7086359 : Blo 1226431 7086359 := bstep (se 1 (by rfl) ⟨5314769, by rfl⟩ : syracuseStep 7086359 = 10629539) B10629539
theorem B2761001 : Blo 1226431 2761001 := bstep (se 2 (by rfl) ⟨1035375, by rfl⟩ : syracuseStep 2761001 = 2070751) B2070751
theorem B18907663 : Blo 1226431 18907663 := bstep (se 1 (by rfl) ⟨14180747, by rfl⟩ : syracuseStep 18907663 = 28361495) B28361495
theorem B3105337 : Blo 1226431 3105337 := bstep (se 2 (by rfl) ⟨1164501, by rfl⟩ : syracuseStep 3105337 = 2329003) B2329003
theorem B6218369 : Blo 1226431 6218369 := bstep (se 2 (by rfl) ⟨2331888, by rfl⟩ : syracuseStep 6218369 = 4663777) B4663777
theorem B4973375 : Blo 1226431 4973375 := bstep (se 1 (by rfl) ⟨3730031, by rfl⟩ : syracuseStep 4973375 = 7460063) B7460063
theorem B2761577 : Blo 1226431 2761577 := bstep (se 2 (by rfl) ⟨1035591, by rfl⟩ : syracuseStep 2761577 = 2071183) B2071183
theorem B2762063 : Blo 1226431 2762063 := bstep (se 1 (by rfl) ⟨2071547, by rfl⟩ : syracuseStep 2762063 = 4143095) B4143095
theorem B2762207 : Blo 1226431 2762207 := bstep (se 1 (by rfl) ⟨2071655, by rfl⟩ : syracuseStep 2762207 = 4143311) B4143311
theorem B161326687 : Blo 1226431 161326687 := bstep (se 1 (by rfl) ⟨120995015, by rfl⟩ : syracuseStep 161326687 = 241990031) B241990031
theorem B20973329 : Blo 1226431 20973329 := bstep (se 2 (by rfl) ⟨7864998, by rfl⟩ : syracuseStep 20973329 = 15729997) B15729997
theorem B2762639 : Blo 1226431 2762639 := bstep (se 1 (by rfl) ⟨2071979, by rfl⟩ : syracuseStep 2762639 = 4143959) B4143959
theorem B2762783 : Blo 1226431 2762783 := bstep (se 1 (by rfl) ⟨2072087, by rfl⟩ : syracuseStep 2762783 = 4144175) B4144175
theorem B2762855 : Blo 1226431 2762855 := bstep (se 1 (by rfl) ⟨2072141, by rfl⟩ : syracuseStep 2762855 = 4144283) B4144283
theorem B35399875 : Blo 1226431 35399875 := bstep (se 1 (by rfl) ⟨26549906, by rfl⟩ : syracuseStep 35399875 = 53099813) B53099813
theorem B2763071 : Blo 1226431 2763071 := bstep (se 1 (by rfl) ⟨2072303, by rfl⟩ : syracuseStep 2763071 = 4144607) B4144607
theorem B1747271 : Blo 1226431 1747271 := bstep (se 1 (by rfl) ⟨1310453, by rfl⟩ : syracuseStep 1747271 = 2620907) B2620907
theorem B2763359 : Blo 1226431 2763359 := bstep (se 1 (by rfl) ⟨2072519, by rfl⟩ : syracuseStep 2763359 = 4145039) B4145039
theorem B4721255 : Blo 1226431 4721255 := bstep (se 1 (by rfl) ⟨3540941, by rfl⟩ : syracuseStep 4721255 = 7081883) B7081883
theorem B70740701 : Blo 1226431 70740701 := bstep (se 3 (by rfl) ⟨13263881, by rfl⟩ : syracuseStep 70740701 = 26527763) B26527763
theorem B4664051 : Blo 1226431 4664051 := bstep (se 1 (by rfl) ⟨3498038, by rfl⟩ : syracuseStep 4664051 = 6996077) B6996077
theorem B2763611 : Blo 1226431 2763611 := bstep (se 1 (by rfl) ⟨2072708, by rfl⟩ : syracuseStep 2763611 = 4145417) B4145417
theorem B9317591 : Blo 1226431 9317591 := bstep (se 1 (by rfl) ⟨6988193, by rfl⟩ : syracuseStep 9317591 = 13976387) B13976387
theorem B6991271 : Blo 1226431 6991271 := bstep (se 1 (by rfl) ⟨5243453, by rfl⟩ : syracuseStep 6991271 = 10486907) B10486907
theorem B6639209 : Blo 1226431 6639209 := bstep (se 2 (by rfl) ⟨2489703, by rfl⟩ : syracuseStep 6639209 = 4979407) B4979407
theorem B4140665 : Blo 1226431 4140665 := bstep (se 2 (by rfl) ⟨1552749, by rfl⟩ : syracuseStep 4140665 = 3105499) B3105499
theorem B2330279 : Blo 1226431 2330279 := bstep (se 1 (by rfl) ⟨1747709, by rfl⟩ : syracuseStep 2330279 = 3495419) B3495419
theorem B9957127 : Blo 1226431 9957127 := bstep (se 1 (by rfl) ⟨7467845, by rfl⟩ : syracuseStep 9957127 = 14935691) B14935691
theorem B1380127 : Blo 1226431 1380127 := bstep (se 1 (by rfl) ⟨1035095, by rfl⟩ : syracuseStep 1380127 = 2070191) B2070191
theorem B10481471 : Blo 1226431 10481471 := bstep (se 1 (by rfl) ⟨7861103, by rfl⟩ : syracuseStep 10481471 = 15722207) B15722207
theorem B28340057 : Blo 1226431 28340057 := bstep (se 2 (by rfl) ⟨10627521, by rfl⟩ : syracuseStep 28340057 = 21255043) B21255043
theorem B8851355 : Blo 1226431 8851355 := bstep (se 1 (by rfl) ⟨6638516, by rfl⟩ : syracuseStep 8851355 = 13277033) B13277033
theorem B15716875 : Blo 1226431 15716875 := bstep (se 1 (by rfl) ⟨11787656, by rfl⟩ : syracuseStep 15716875 = 23575313) B23575313
theorem B1839935 : Blo 1226431 1839935 := bstep (se 1 (by rfl) ⟨1379951, by rfl⟩ : syracuseStep 1839935 = 2759903) B2759903
theorem B6214481 : Blo 1226431 6214481 := bstep (se 2 (by rfl) ⟨2330430, by rfl⟩ : syracuseStep 6214481 = 4660861) B4660861
theorem B15717239 : Blo 1226431 15717239 := bstep (se 1 (by rfl) ⟨11787929, by rfl⟩ : syracuseStep 15717239 = 23575859) B23575859
theorem B47829953 : Blo 1226431 47829953 := bstep (se 2 (by rfl) ⟨17936232, by rfl⟩ : syracuseStep 47829953 = 35872465) B35872465
theorem B59691977 : Blo 1226431 59691977 := bstep (se 2 (by rfl) ⟨22384491, by rfl⟩ : syracuseStep 59691977 = 44768983) B44768983
theorem B17691635 : Blo 1226431 17691635 := bstep (se 1 (by rfl) ⟨13268726, by rfl⟩ : syracuseStep 17691635 = 26537453) B26537453
theorem B1840175 : Blo 1226431 1840175 := bstep (se 1 (by rfl) ⟨1380131, by rfl⟩ : syracuseStep 1840175 = 2760263) B2760263
theorem B1840847 : Blo 1226431 1840847 := bstep (se 1 (by rfl) ⟨1380635, by rfl⟩ : syracuseStep 1840847 = 2761271) B2761271
theorem B5896061 : Blo 1226431 5896061 := bstep (se 3 (by rfl) ⟨1105511, by rfl⟩ : syracuseStep 5896061 = 2211023) B2211023
theorem B2070427 : Blo 1226431 2070427 := bstep (se 1 (by rfl) ⟨1552820, by rfl⟩ : syracuseStep 2070427 = 3105641) B3105641
theorem B1841063 : Blo 1226431 1841063 := bstep (se 1 (by rfl) ⟨1380797, by rfl⟩ : syracuseStep 1841063 = 2761595) B2761595
theorem B1841087 : Blo 1226431 1841087 := bstep (se 1 (by rfl) ⟨1380815, by rfl⟩ : syracuseStep 1841087 = 2761631) B2761631
theorem B2070569 : Blo 1226431 2070569 := bstep (se 2 (by rfl) ⟨776463, by rfl⟩ : syracuseStep 2070569 = 1552927) B1552927
theorem B6985871 : Blo 1226431 6985871 := bstep (se 1 (by rfl) ⟨5239403, by rfl⟩ : syracuseStep 6985871 = 10478807) B10478807
theorem B1227247 : Blo 1226431 1227247 := bstep (se 1 (by rfl) ⟨920435, by rfl⟩ : syracuseStep 1227247 = 1840871) B1840871
theorem B1841711 : Blo 1226431 1841711 := bstep (se 1 (by rfl) ⟨1381283, by rfl⟩ : syracuseStep 1841711 = 2762567) B2762567
theorem B1227503 : Blo 1226431 1227503 := bstep (se 1 (by rfl) ⟨920627, by rfl⟩ : syracuseStep 1227503 = 1841255) B1841255
theorem B7478011 : Blo 1226431 7478011 := bstep (se 1 (by rfl) ⟨5608508, by rfl⟩ : syracuseStep 7478011 = 11217017) B11217017
theorem B2071291 : Blo 1226431 2071291 := bstep (se 1 (by rfl) ⟨1553468, by rfl⟩ : syracuseStep 2071291 = 3106937) B3106937
theorem B3496729 : Blo 1226431 3496729 := bstep (se 2 (by rfl) ⟨1311273, by rfl⟩ : syracuseStep 3496729 = 2622547) B2622547
theorem B2759471 : Blo 1226431 2759471 := bstep (se 1 (by rfl) ⟨2069603, by rfl⟩ : syracuseStep 2759471 = 4139207) B4139207
theorem B2071433 : Blo 1226431 2071433 := bstep (se 2 (by rfl) ⟨776787, by rfl⟩ : syracuseStep 2071433 = 1553575) B1553575
theorem B1842119 : Blo 1226431 1842119 := bstep (se 1 (by rfl) ⟨1381589, by rfl⟩ : syracuseStep 1842119 = 2763179) B2763179
theorem B13990967 : Blo 1226431 13990967 := bstep (se 1 (by rfl) ⟨10493225, by rfl⟩ : syracuseStep 13990967 = 20986451) B20986451
theorem B1228015 : Blo 1226431 1228015 := bstep (se 1 (by rfl) ⟨921011, by rfl⟩ : syracuseStep 1228015 = 1842023) B1842023
theorem B3505427 : Blo 1226431 3505427 := bstep (se 1 (by rfl) ⟨2629070, by rfl⟩ : syracuseStep 3505427 = 5258141) B5258141
theorem B1228059 : Blo 1226431 1228059 := bstep (se 1 (by rfl) ⟨921044, by rfl⟩ : syracuseStep 1228059 = 1842089) B1842089
theorem B2071865 : Blo 1226431 2071865 := bstep (se 2 (by rfl) ⟨776949, by rfl⟩ : syracuseStep 2071865 = 1553899) B1553899
theorem B1228187 : Blo 1226431 1228187 := bstep (se 1 (by rfl) ⟨921140, by rfl⟩ : syracuseStep 1228187 = 1842281) B1842281
theorem B2072047 : Blo 1226431 2072047 := bstep (se 1 (by rfl) ⟨1554035, by rfl⟩ : syracuseStep 2072047 = 3108071) B3108071
theorem B1228315 : Blo 1226431 1228315 := bstep (se 1 (by rfl) ⟨921236, by rfl⟩ : syracuseStep 1228315 = 1842473) B1842473
theorem B174685805 : Blo 1226431 174685805 := bstep (se 3 (by rfl) ⟨32753588, by rfl⟩ : syracuseStep 174685805 = 65507177) B65507177
theorem B3104507 : Blo 1226431 3104507 := bstep (se 1 (by rfl) ⟨2328380, by rfl⟩ : syracuseStep 3104507 = 4656761) B4656761
theorem B2072479 : Blo 1226431 2072479 := bstep (se 1 (by rfl) ⟨1554359, by rfl⟩ : syracuseStep 2072479 = 3108719) B3108719
theorem B34521155 : Blo 1226431 34521155 := bstep (se 1 (by rfl) ⟨25890866, by rfl⟩ : syracuseStep 34521155 = 51781733) B51781733
theorem B4145579 : Blo 1226431 4145579 := bstep (se 1 (by rfl) ⟨3109184, by rfl⟩ : syracuseStep 4145579 = 6218369) B6218369
theorem B10478159 : Blo 1226431 10478159 := bstep (se 1 (by rfl) ⟨7858619, by rfl⟩ : syracuseStep 10478159 = 15717239) B15717239
theorem B20955833 : Blo 1226431 20955833 := bstep (se 2 (by rfl) ⟨7858437, by rfl⟩ : syracuseStep 20955833 = 15716875) B15716875
theorem B2761721 : Blo 1226431 2761721 := bstep (se 2 (by rfl) ⟨1035645, by rfl⟩ : syracuseStep 2761721 = 2071291) B2071291
theorem B4662305 : Blo 1226431 4662305 := bstep (se 2 (by rfl) ⟨1748364, by rfl⟩ : syracuseStep 4662305 = 3496729) B3496729
theorem B3147503 : Blo 1226431 3147503 := bstep (se 1 (by rfl) ⟨2360627, by rfl⟩ : syracuseStep 3147503 = 4721255) B4721255
theorem B2762729 : Blo 1226431 2762729 := bstep (se 2 (by rfl) ⟨1036023, by rfl⟩ : syracuseStep 2762729 = 2072047) B2072047
theorem B6211727 : Blo 1226431 6211727 := bstep (se 1 (by rfl) ⟨4658795, by rfl⟩ : syracuseStep 6211727 = 9317591) B9317591
theorem B2336951 : Blo 1226431 2336951 := bstep (se 1 (by rfl) ⟨1752713, by rfl⟩ : syracuseStep 2336951 = 3505427) B3505427
theorem B75573485 : Blo 1226431 75573485 := bstep (se 3 (by rfl) ⟨14170028, by rfl⟩ : syracuseStep 75573485 = 28340057) B28340057
theorem B4426139 : Blo 1226431 4426139 := bstep (se 1 (by rfl) ⟨3319604, by rfl⟩ : syracuseStep 4426139 = 6639209) B6639209
theorem B2763305 : Blo 1226431 2763305 := bstep (se 2 (by rfl) ⟨1036239, by rfl⟩ : syracuseStep 2763305 = 2072479) B2072479
theorem B5900903 : Blo 1226431 5900903 := bstep (se 1 (by rfl) ⟨4425677, by rfl⟩ : syracuseStep 5900903 = 8851355) B8851355
theorem B7187297 : Blo 1226431 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B31886635 : Blo 1226431 31886635 := bstep (se 1 (by rfl) ⟨23914976, by rfl⟩ : syracuseStep 31886635 = 47829953) B47829953
theorem B25210217 : Blo 1226431 25210217 := bstep (se 2 (by rfl) ⟨9453831, by rfl⟩ : syracuseStep 25210217 = 18907663) B18907663
theorem B4140449 : Blo 1226431 4140449 := bstep (se 2 (by rfl) ⟨1552668, by rfl⟩ : syracuseStep 4140449 = 3105337) B3105337
theorem B39882725 : Blo 1226431 39882725 := bstep (se 4 (by rfl) ⟨3739005, by rfl⟩ : syracuseStep 39882725 = 7478011) B7478011
theorem B1380379 : Blo 1226431 1380379 := bstep (se 1 (by rfl) ⟨1035284, by rfl⟩ : syracuseStep 1380379 = 2070569) B2070569
theorem B4657247 : Blo 1226431 4657247 := bstep (se 1 (by rfl) ⟨3492935, by rfl⟩ : syracuseStep 4657247 = 6985871) B6985871
theorem B3109367 : Blo 1226431 3109367 := bstep (se 1 (by rfl) ⟨2332025, by rfl⟩ : syracuseStep 3109367 = 4664051) B4664051
theorem B1839647 : Blo 1226431 1839647 := bstep (se 1 (by rfl) ⟨1379735, by rfl⟩ : syracuseStep 1839647 = 2759471) B2759471
theorem B1380955 : Blo 1226431 1380955 := bstep (se 1 (by rfl) ⟨1035716, by rfl⟩ : syracuseStep 1380955 = 2071433) B2071433
theorem B9327311 : Blo 1226431 9327311 := bstep (se 1 (by rfl) ⟨6995483, by rfl⟩ : syracuseStep 9327311 = 13990967) B13990967
theorem B215102249 : Blo 1226431 215102249 := bstep (se 2 (by rfl) ⟨80663343, by rfl⟩ : syracuseStep 215102249 = 161326687) B161326687
theorem B1381243 : Blo 1226431 1381243 := bstep (se 1 (by rfl) ⟨1035932, by rfl⟩ : syracuseStep 1381243 = 2071865) B2071865
theorem B13276169 : Blo 1226431 13276169 := bstep (se 2 (by rfl) ⟨4978563, by rfl⟩ : syracuseStep 13276169 = 9957127) B9957127
theorem B1840169 : Blo 1226431 1840169 := bstep (se 2 (by rfl) ⟨690063, by rfl⟩ : syracuseStep 1840169 = 1380127) B1380127
theorem B1553519 : Blo 1226431 1553519 := bstep (se 1 (by rfl) ⟨1165139, by rfl⟩ : syracuseStep 1553519 = 2330279) B2330279
theorem B2069671 : Blo 1226431 2069671 := bstep (se 1 (by rfl) ⟨1552253, by rfl⟩ : syracuseStep 2069671 = 3104507) B3104507
theorem B4724239 : Blo 1226431 4724239 := bstep (se 1 (by rfl) ⟨3543179, by rfl⟩ : syracuseStep 4724239 = 7086359) B7086359
theorem B1840667 : Blo 1226431 1840667 := bstep (se 1 (by rfl) ⟨1380500, by rfl⟩ : syracuseStep 1840667 = 2761001) B2761001
theorem B47199833 : Blo 1226431 47199833 := bstep (se 2 (by rfl) ⟨17699937, by rfl⟩ : syracuseStep 47199833 = 35399875) B35399875
theorem B3315583 : Blo 1226431 3315583 := bstep (se 1 (by rfl) ⟨2486687, by rfl⟩ : syracuseStep 3315583 = 4973375) B4973375
theorem B1226623 : Blo 1226431 1226623 := bstep (se 1 (by rfl) ⟨919967, by rfl⟩ : syracuseStep 1226623 = 1839935) B1839935
theorem B4142987 : Blo 1226431 4142987 := bstep (se 1 (by rfl) ⟨3107240, by rfl⟩ : syracuseStep 4142987 = 6214481) B6214481
theorem B1841051 : Blo 1226431 1841051 := bstep (se 1 (by rfl) ⟨1380788, by rfl⟩ : syracuseStep 1841051 = 2761577) B2761577
theorem B39794651 : Blo 1226431 39794651 := bstep (se 1 (by rfl) ⟨29845988, by rfl⟩ : syracuseStep 39794651 = 59691977) B59691977
theorem B11794423 : Blo 1226431 11794423 := bstep (se 1 (by rfl) ⟨8845817, by rfl⟩ : syracuseStep 11794423 = 17691635) B17691635
theorem B1226783 : Blo 1226431 1226783 := bstep (se 1 (by rfl) ⟨920087, by rfl⟩ : syracuseStep 1226783 = 1840175) B1840175
theorem B4659389 : Blo 1226431 4659389 := bstep (se 3 (by rfl) ⟨873635, by rfl⟩ : syracuseStep 4659389 = 1747271) B1747271
theorem B1841375 : Blo 1226431 1841375 := bstep (se 1 (by rfl) ⟨1381031, by rfl⟩ : syracuseStep 1841375 = 2762063) B2762063
theorem B1841471 : Blo 1226431 1841471 := bstep (se 1 (by rfl) ⟨1381103, by rfl⟩ : syracuseStep 1841471 = 2762207) B2762207
theorem B1227231 : Blo 1226431 1227231 := bstep (se 1 (by rfl) ⟨920423, by rfl⟩ : syracuseStep 1227231 = 1840847) B1840847
theorem B13982219 : Blo 1226431 13982219 := bstep (se 1 (by rfl) ⟨10486664, by rfl⟩ : syracuseStep 13982219 = 20973329) B20973329
theorem B3930707 : Blo 1226431 3930707 := bstep (se 1 (by rfl) ⟨2948030, by rfl⟩ : syracuseStep 3930707 = 5896061) B5896061
theorem B1841759 : Blo 1226431 1841759 := bstep (se 1 (by rfl) ⟨1381319, by rfl⟩ : syracuseStep 1841759 = 2762639) B2762639
theorem B1227375 : Blo 1226431 1227375 := bstep (se 1 (by rfl) ⟨920531, by rfl⟩ : syracuseStep 1227375 = 1841063) B1841063
theorem B1227391 : Blo 1226431 1227391 := bstep (se 1 (by rfl) ⟨920543, by rfl⟩ : syracuseStep 1227391 = 1841087) B1841087
theorem B1841855 : Blo 1226431 1841855 := bstep (se 1 (by rfl) ⟨1381391, by rfl⟩ : syracuseStep 1841855 = 2762783) B2762783
theorem B1841903 : Blo 1226431 1841903 := bstep (se 1 (by rfl) ⟨1381427, by rfl⟩ : syracuseStep 1841903 = 2762855) B2762855
theorem B1842047 : Blo 1226431 1842047 := bstep (se 1 (by rfl) ⟨1381535, by rfl⟩ : syracuseStep 1842047 = 2763071) B2763071
theorem B1227807 : Blo 1226431 1227807 := bstep (se 1 (by rfl) ⟨920855, by rfl⟩ : syracuseStep 1227807 = 1841711) B1841711
theorem B1842239 : Blo 1226431 1842239 := bstep (se 1 (by rfl) ⟨1381679, by rfl⟩ : syracuseStep 1842239 = 2763359) B2763359
theorem B47160467 : Blo 1226431 47160467 := bstep (se 1 (by rfl) ⟨35370350, by rfl⟩ : syracuseStep 47160467 = 70740701) B70740701
theorem B1842407 : Blo 1226431 1842407 := bstep (se 1 (by rfl) ⟨1381805, by rfl⟩ : syracuseStep 1842407 = 2763611) B2763611
theorem B1228079 : Blo 1226431 1228079 := bstep (se 1 (by rfl) ⟨921059, by rfl⟩ : syracuseStep 1228079 = 1842119) B1842119
theorem B4660847 : Blo 1226431 4660847 := bstep (se 1 (by rfl) ⟨3495635, by rfl⟩ : syracuseStep 4660847 = 6991271) B6991271
theorem B116457203 : Blo 1226431 116457203 := bstep (se 1 (by rfl) ⟨87342902, by rfl⟩ : syracuseStep 116457203 = 174685805) B174685805
theorem B2760443 : Blo 1226431 2760443 := bstep (se 1 (by rfl) ⟨2070332, by rfl⟩ : syracuseStep 2760443 = 4140665) B4140665
theorem B2760569 : Blo 1226431 2760569 := bstep (se 2 (by rfl) ⟨1035213, by rfl⟩ : syracuseStep 2760569 = 2070427) B2070427
theorem B6987647 : Blo 1226431 6987647 := bstep (se 1 (by rfl) ⟨5240735, by rfl⟩ : syracuseStep 6987647 = 10481471) B10481471
theorem B3104831 : Blo 1226431 3104831 := bstep (se 1 (by rfl) ⟨2328623, by rfl⟩ : syracuseStep 3104831 = 4657247) B4657247
theorem B2072911 : Blo 1226431 2072911 := bstep (se 1 (by rfl) ⟨1554683, by rfl⟩ : syracuseStep 2072911 = 3109367) B3109367
theorem B6218207 : Blo 1226431 6218207 := bstep (se 1 (by rfl) ⟨4663655, by rfl⟩ : syracuseStep 6218207 = 9327311) B9327311
theorem B143401499 : Blo 1226431 143401499 := bstep (se 1 (by rfl) ⟨107551124, by rfl⟩ : syracuseStep 143401499 = 215102249) B215102249
theorem B31466555 : Blo 1226431 31466555 := bstep (se 1 (by rfl) ⟨23599916, by rfl⟩ : syracuseStep 31466555 = 47199833) B47199833
theorem B2761991 : Blo 1226431 2761991 := bstep (se 1 (by rfl) ⟨2071493, by rfl⟩ : syracuseStep 2761991 = 4142987) B4142987
theorem B3106259 : Blo 1226431 3106259 := bstep (se 1 (by rfl) ⟨2329694, by rfl⟩ : syracuseStep 3106259 = 4659389) B4659389
theorem B50382323 : Blo 1226431 50382323 := bstep (se 1 (by rfl) ⟨37786742, by rfl⟩ : syracuseStep 50382323 = 75573485) B75573485
theorem B2950759 : Blo 1226431 2950759 := bstep (se 1 (by rfl) ⟨2213069, by rfl⟩ : syracuseStep 2950759 = 4426139) B4426139
theorem B3933935 : Blo 1226431 3933935 := bstep (se 1 (by rfl) ⟨2950451, by rfl⟩ : syracuseStep 3933935 = 5900903) B5900903
theorem B3107231 : Blo 1226431 3107231 := bstep (se 1 (by rfl) ⟨2330423, by rfl⟩ : syracuseStep 3107231 = 4660847) B4660847
theorem B77638135 : Blo 1226431 77638135 := bstep (se 1 (by rfl) ⟨58228601, by rfl⟩ : syracuseStep 77638135 = 116457203) B116457203
theorem B23014103 : Blo 1226431 23014103 := bstep (se 1 (by rfl) ⟨17260577, by rfl⟩ : syracuseStep 23014103 = 34521155) B34521155
theorem B2763719 : Blo 1226431 2763719 := bstep (se 1 (by rfl) ⟨2072789, by rfl⟩ : syracuseStep 2763719 = 4145579) B4145579
theorem B13970555 : Blo 1226431 13970555 := bstep (se 1 (by rfl) ⟨10477916, by rfl⟩ : syracuseStep 13970555 = 20955833) B20955833
theorem B8850779 : Blo 1226431 8850779 := bstep (se 1 (by rfl) ⟨6638084, by rfl⟩ : syracuseStep 8850779 = 13276169) B13276169
theorem B3108203 : Blo 1226431 3108203 := bstep (se 1 (by rfl) ⟨2331152, by rfl⟩ : syracuseStep 3108203 = 4662305) B4662305
theorem B76664501 : Blo 1226431 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B26529767 : Blo 1226431 26529767 := bstep (se 1 (by rfl) ⟨19897325, by rfl⟩ : syracuseStep 26529767 = 39794651) B39794651
theorem B4141151 : Blo 1226431 4141151 := bstep (se 1 (by rfl) ⟨3105863, by rfl⟩ : syracuseStep 4141151 = 6211727) B6211727
theorem B8393341 : Blo 1226431 8393341 := bstep (se 3 (by rfl) ⟨1573751, by rfl⟩ : syracuseStep 8393341 = 3147503) B3147503
theorem B16806811 : Blo 1226431 16806811 := bstep (se 1 (by rfl) ⟨12605108, by rfl⟩ : syracuseStep 16806811 = 25210217) B25210217
theorem B1840295 : Blo 1226431 1840295 := bstep (se 1 (by rfl) ⟨1380221, by rfl⟩ : syracuseStep 1840295 = 2760443) B2760443
theorem B4420777 : Blo 1226431 4420777 := bstep (se 2 (by rfl) ⟨1657791, by rfl⟩ : syracuseStep 4420777 = 3315583) B3315583
theorem B1840379 : Blo 1226431 1840379 := bstep (se 1 (by rfl) ⟨1380284, by rfl⟩ : syracuseStep 1840379 = 2760569) B2760569
theorem B4658431 : Blo 1226431 4658431 := bstep (se 1 (by rfl) ⟨3493823, by rfl⟩ : syracuseStep 4658431 = 6987647) B6987647
theorem B26588483 : Blo 1226431 26588483 := bstep (se 1 (by rfl) ⟨19941362, by rfl⟩ : syracuseStep 26588483 = 39882725) B39882725
theorem B15725897 : Blo 1226431 15725897 := bstep (se 2 (by rfl) ⟨5897211, by rfl⟩ : syracuseStep 15725897 = 11794423) B11794423
theorem B1840505 : Blo 1226431 1840505 := bstep (se 2 (by rfl) ⟨690189, by rfl⟩ : syracuseStep 1840505 = 1380379) B1380379
theorem B4142717 : Blo 1226431 4142717 := bstep (se 3 (by rfl) ⟨776759, by rfl⟩ : syracuseStep 4142717 = 1553519) B1553519
theorem B1226431 : Blo 1226431 1226431 := bstep (se 1 (by rfl) ⟨919823, by rfl⟩ : syracuseStep 1226431 = 1839647) B1839647
theorem B6985439 : Blo 1226431 6985439 := bstep (se 1 (by rfl) ⟨5239079, by rfl⟩ : syracuseStep 6985439 = 10478159) B10478159
theorem B6231869 : Blo 1226431 6231869 := bstep (se 3 (by rfl) ⟨1168475, by rfl⟩ : syracuseStep 6231869 = 2336951) B2336951
theorem B1841147 : Blo 1226431 1841147 := bstep (se 1 (by rfl) ⟨1380860, by rfl⟩ : syracuseStep 1841147 = 2761721) B2761721
theorem B1226779 : Blo 1226431 1226779 := bstep (se 1 (by rfl) ⟨920084, by rfl⟩ : syracuseStep 1226779 = 1840169) B1840169
theorem B1841273 : Blo 1226431 1841273 := bstep (se 2 (by rfl) ⟨690477, by rfl⟩ : syracuseStep 1841273 = 1380955) B1380955
theorem B1227111 : Blo 1226431 1227111 := bstep (se 1 (by rfl) ⟨920333, by rfl⟩ : syracuseStep 1227111 = 1840667) B1840667
theorem B1841657 : Blo 1226431 1841657 := bstep (se 2 (by rfl) ⟨690621, by rfl⟩ : syracuseStep 1841657 = 1381243) B1381243
theorem B1227367 : Blo 1226431 1227367 := bstep (se 1 (by rfl) ⟨920525, by rfl⟩ : syracuseStep 1227367 = 1841051) B1841051
theorem B1841819 : Blo 1226431 1841819 := bstep (se 1 (by rfl) ⟨1381364, by rfl⟩ : syracuseStep 1841819 = 2762729) B2762729
theorem B1227583 : Blo 1226431 1227583 := bstep (se 1 (by rfl) ⟨920687, by rfl⟩ : syracuseStep 1227583 = 1841375) B1841375
theorem B1227647 : Blo 1226431 1227647 := bstep (se 1 (by rfl) ⟨920735, by rfl⟩ : syracuseStep 1227647 = 1841471) B1841471
theorem B2759561 : Blo 1226431 2759561 := bstep (se 2 (by rfl) ⟨1034835, by rfl⟩ : syracuseStep 2759561 = 2069671) B2069671
theorem B9321479 : Blo 1226431 9321479 := bstep (se 1 (by rfl) ⟨6991109, by rfl⟩ : syracuseStep 9321479 = 13982219) B13982219
theorem B1842203 : Blo 1226431 1842203 := bstep (se 1 (by rfl) ⟨1381652, by rfl⟩ : syracuseStep 1842203 = 2763305) B2763305
theorem B2620471 : Blo 1226431 2620471 := bstep (se 1 (by rfl) ⟨1965353, by rfl⟩ : syracuseStep 2620471 = 3930707) B3930707
theorem B42515513 : Blo 1226431 42515513 := bstep (se 2 (by rfl) ⟨15943317, by rfl⟩ : syracuseStep 42515513 = 31886635) B31886635
theorem B1227839 : Blo 1226431 1227839 := bstep (se 1 (by rfl) ⟨920879, by rfl⟩ : syracuseStep 1227839 = 1841759) B1841759
theorem B1227903 : Blo 1226431 1227903 := bstep (se 1 (by rfl) ⟨920927, by rfl⟩ : syracuseStep 1227903 = 1841855) B1841855
theorem B1227935 : Blo 1226431 1227935 := bstep (se 1 (by rfl) ⟨920951, by rfl⟩ : syracuseStep 1227935 = 1841903) B1841903
theorem B1228031 : Blo 1226431 1228031 := bstep (se 1 (by rfl) ⟨921023, by rfl⟩ : syracuseStep 1228031 = 1842047) B1842047
theorem B6298985 : Blo 1226431 6298985 := bstep (se 2 (by rfl) ⟨2362119, by rfl⟩ : syracuseStep 6298985 = 4724239) B4724239
theorem B1228159 : Blo 1226431 1228159 := bstep (se 1 (by rfl) ⟨921119, by rfl⟩ : syracuseStep 1228159 = 1842239) B1842239
theorem B31440311 : Blo 1226431 31440311 := bstep (se 1 (by rfl) ⟨23580233, by rfl⟩ : syracuseStep 31440311 = 47160467) B47160467
theorem B1228271 : Blo 1226431 1228271 := bstep (se 1 (by rfl) ⟨921203, by rfl⟩ : syracuseStep 1228271 = 1842407) B1842407
theorem B2760299 : Blo 1226431 2760299 := bstep (se 1 (by rfl) ⟨2070224, by rfl⟩ : syracuseStep 2760299 = 4140449) B4140449
theorem B2760767 : Blo 1226431 2760767 := bstep (se 1 (by rfl) ⟨2070575, by rfl⟩ : syracuseStep 2760767 = 4141151) B4141151
theorem B4145471 : Blo 1226431 4145471 := bstep (se 1 (by rfl) ⟨3109103, by rfl⟩ : syracuseStep 4145471 = 6218207) B6218207
theorem B95600999 : Blo 1226431 95600999 := bstep (se 1 (by rfl) ⟨71700749, by rfl⟩ : syracuseStep 95600999 = 143401499) B143401499
theorem B11191121 : Blo 1226431 11191121 := bstep (se 2 (by rfl) ⟨4196670, by rfl⟩ : syracuseStep 11191121 = 8393341) B8393341
theorem B33588215 : Blo 1226431 33588215 := bstep (se 1 (by rfl) ⟨25191161, by rfl⟩ : syracuseStep 33588215 = 50382323) B50382323
theorem B2761811 : Blo 1226431 2761811 := bstep (se 1 (by rfl) ⟨2071358, by rfl⟩ : syracuseStep 2761811 = 4142717) B4142717
theorem B2622623 : Blo 1226431 2622623 := bstep (se 1 (by rfl) ⟨1966967, by rfl⟩ : syracuseStep 2622623 = 3933935) B3933935
theorem B4154579 : Blo 1226431 4154579 := bstep (se 1 (by rfl) ⟨3115934, by rfl⟩ : syracuseStep 4154579 = 6231869) B6231869
theorem B6211241 : Blo 1226431 6211241 := bstep (se 2 (by rfl) ⟨2329215, by rfl⟩ : syracuseStep 6211241 = 4658431) B4658431
theorem B3934345 : Blo 1226431 3934345 := bstep (se 2 (by rfl) ⟨1475379, by rfl⟩ : syracuseStep 3934345 = 2950759) B2950759
theorem B5900519 : Blo 1226431 5900519 := bstep (se 1 (by rfl) ⟨4425389, by rfl⟩ : syracuseStep 5900519 = 8850779) B8850779
theorem B2763881 : Blo 1226431 2763881 := bstep (se 2 (by rfl) ⟨1036455, by rfl⟩ : syracuseStep 2763881 = 2072911) B2072911
theorem B103517513 : Blo 1226431 103517513 := bstep (se 2 (by rfl) ⟨38819067, by rfl⟩ : syracuseStep 103517513 = 77638135) B77638135
theorem B4656959 : Blo 1226431 4656959 := bstep (se 1 (by rfl) ⟨3492719, by rfl⟩ : syracuseStep 4656959 = 6985439) B6985439
theorem B22409081 : Blo 1226431 22409081 := bstep (se 2 (by rfl) ⟨8403405, by rfl⟩ : syracuseStep 22409081 = 16806811) B16806811
theorem B3493961 : Blo 1226431 3493961 := bstep (se 2 (by rfl) ⟨1310235, by rfl⟩ : syracuseStep 3493961 = 2620471) B2620471
theorem B5894369 : Blo 1226431 5894369 := bstep (se 2 (by rfl) ⟨2210388, by rfl⟩ : syracuseStep 5894369 = 4420777) B4420777
theorem B61370941 : Blo 1226431 61370941 := bstep (se 3 (by rfl) ⟨11507051, by rfl⟩ : syracuseStep 61370941 = 23014103) B23014103
theorem B1839707 : Blo 1226431 1839707 := bstep (se 1 (by rfl) ⟨1379780, by rfl⟩ : syracuseStep 1839707 = 2759561) B2759561
theorem B6214319 : Blo 1226431 6214319 := bstep (se 1 (by rfl) ⟨4660739, by rfl⟩ : syracuseStep 6214319 = 9321479) B9321479
theorem B4199323 : Blo 1226431 4199323 := bstep (se 1 (by rfl) ⟨3149492, by rfl⟩ : syracuseStep 4199323 = 6298985) B6298985
theorem B20960207 : Blo 1226431 20960207 := bstep (se 1 (by rfl) ⟨15720155, by rfl⟩ : syracuseStep 20960207 = 31440311) B31440311
theorem B1840199 : Blo 1226431 1840199 := bstep (se 1 (by rfl) ⟨1380149, by rfl⟩ : syracuseStep 1840199 = 2760299) B2760299
theorem B2069887 : Blo 1226431 2069887 := bstep (se 1 (by rfl) ⟨1552415, by rfl⟩ : syracuseStep 2069887 = 3104831) B3104831
theorem B20977703 : Blo 1226431 20977703 := bstep (se 1 (by rfl) ⟨15733277, by rfl⟩ : syracuseStep 20977703 = 31466555) B31466555
theorem B1226863 : Blo 1226431 1226863 := bstep (se 1 (by rfl) ⟨920147, by rfl⟩ : syracuseStep 1226863 = 1840295) B1840295
theorem B1226919 : Blo 1226431 1226919 := bstep (se 1 (by rfl) ⟨920189, by rfl⟩ : syracuseStep 1226919 = 1840379) B1840379
theorem B1841327 : Blo 1226431 1841327 := bstep (se 1 (by rfl) ⟨1380995, by rfl⟩ : syracuseStep 1841327 = 2761991) B2761991
theorem B17725655 : Blo 1226431 17725655 := bstep (se 1 (by rfl) ⟨13294241, by rfl⟩ : syracuseStep 17725655 = 26588483) B26588483
theorem B10483931 : Blo 1226431 10483931 := bstep (se 1 (by rfl) ⟨7862948, by rfl⟩ : syracuseStep 10483931 = 15725897) B15725897
theorem B1227003 : Blo 1226431 1227003 := bstep (se 1 (by rfl) ⟨920252, by rfl⟩ : syracuseStep 1227003 = 1840505) B1840505
theorem B2070839 : Blo 1226431 2070839 := bstep (se 1 (by rfl) ⟨1553129, by rfl⟩ : syracuseStep 2070839 = 3106259) B3106259
theorem B1227431 : Blo 1226431 1227431 := bstep (se 1 (by rfl) ⟨920573, by rfl⟩ : syracuseStep 1227431 = 1841147) B1841147
theorem B1227515 : Blo 1226431 1227515 := bstep (se 1 (by rfl) ⟨920636, by rfl⟩ : syracuseStep 1227515 = 1841273) B1841273
theorem B2071487 : Blo 1226431 2071487 := bstep (se 1 (by rfl) ⟨1553615, by rfl⟩ : syracuseStep 2071487 = 3107231) B3107231
theorem B1227771 : Blo 1226431 1227771 := bstep (se 1 (by rfl) ⟨920828, by rfl⟩ : syracuseStep 1227771 = 1841657) B1841657
theorem B1227879 : Blo 1226431 1227879 := bstep (se 1 (by rfl) ⟨920909, by rfl⟩ : syracuseStep 1227879 = 1841819) B1841819
theorem B1842479 : Blo 1226431 1842479 := bstep (se 1 (by rfl) ⟨1381859, by rfl⟩ : syracuseStep 1842479 = 2763719) B2763719
theorem B1228135 : Blo 1226431 1228135 := bstep (se 1 (by rfl) ⟨921101, by rfl⟩ : syracuseStep 1228135 = 1842203) B1842203
theorem B28343675 : Blo 1226431 28343675 := bstep (se 1 (by rfl) ⟨21257756, by rfl⟩ : syracuseStep 28343675 = 42515513) B42515513
theorem B9313703 : Blo 1226431 9313703 := bstep (se 1 (by rfl) ⟨6985277, by rfl⟩ : syracuseStep 9313703 = 13970555) B13970555
theorem B2072135 : Blo 1226431 2072135 := bstep (se 1 (by rfl) ⟨1554101, by rfl⟩ : syracuseStep 2072135 = 3108203) B3108203
theorem B51109667 : Blo 1226431 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B17686511 : Blo 1226431 17686511 := bstep (se 1 (by rfl) ⟨13264883, by rfl⟩ : syracuseStep 17686511 = 26529767) B26529767
theorem B63733999 : Blo 1226431 63733999 := bstep (se 1 (by rfl) ⟨47800499, by rfl⟩ : syracuseStep 63733999 = 95600999) B95600999
theorem B2769719 : Blo 1226431 2769719 := bstep (se 1 (by rfl) ⟨2077289, by rfl⟩ : syracuseStep 2769719 = 4154579) B4154579
theorem B13985135 : Blo 1226431 13985135 := bstep (se 1 (by rfl) ⟨10488851, by rfl⟩ : syracuseStep 13985135 = 20977703) B20977703
theorem B6989287 : Blo 1226431 6989287 := bstep (se 1 (by rfl) ⟨5241965, by rfl⟩ : syracuseStep 6989287 = 10483931) B10483931
theorem B3933679 : Blo 1226431 3933679 := bstep (se 1 (by rfl) ⟨2950259, by rfl⟩ : syracuseStep 3933679 = 5900519) B5900519
theorem B69011675 : Blo 1226431 69011675 := bstep (se 1 (by rfl) ⟨51758756, by rfl⟩ : syracuseStep 69011675 = 103517513) B103517513
theorem B34073111 : Blo 1226431 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B11791007 : Blo 1226431 11791007 := bstep (se 1 (by rfl) ⟨8843255, by rfl⟩ : syracuseStep 11791007 = 17686511) B17686511
theorem B2329307 : Blo 1226431 2329307 := bstep (se 1 (by rfl) ⟨1746980, by rfl⟩ : syracuseStep 2329307 = 3493961) B3493961
theorem B5245793 : Blo 1226431 5245793 := bstep (se 2 (by rfl) ⟨1967172, by rfl⟩ : syracuseStep 5245793 = 3934345) B3934345
theorem B2763647 : Blo 1226431 2763647 := bstep (se 1 (by rfl) ⟨2072735, by rfl⟩ : syracuseStep 2763647 = 4145471) B4145471
theorem B22392143 : Blo 1226431 22392143 := bstep (se 1 (by rfl) ⟨16794107, by rfl⟩ : syracuseStep 22392143 = 33588215) B33588215
theorem B4140827 : Blo 1226431 4140827 := bstep (se 1 (by rfl) ⟨3105620, by rfl⟩ : syracuseStep 4140827 = 6211241) B6211241
theorem B5599097 : Blo 1226431 5599097 := bstep (se 2 (by rfl) ⟨2099661, by rfl⟩ : syracuseStep 5599097 = 4199323) B4199323
theorem B11817103 : Blo 1226431 11817103 := bstep (se 1 (by rfl) ⟨8862827, by rfl⟩ : syracuseStep 11817103 = 17725655) B17725655
theorem B1380559 : Blo 1226431 1380559 := bstep (se 1 (by rfl) ⟨1035419, by rfl⟩ : syracuseStep 1380559 = 2070839) B2070839
theorem B1380991 : Blo 1226431 1380991 := bstep (se 1 (by rfl) ⟨1035743, by rfl⟩ : syracuseStep 1380991 = 2071487) B2071487
theorem B18895783 : Blo 1226431 18895783 := bstep (se 1 (by rfl) ⟨14171837, by rfl⟩ : syracuseStep 18895783 = 28343675) B28343675
theorem B1381423 : Blo 1226431 1381423 := bstep (se 1 (by rfl) ⟨1036067, by rfl⟩ : syracuseStep 1381423 = 2072135) B2072135
theorem B14939387 : Blo 1226431 14939387 := bstep (se 1 (by rfl) ⟨11204540, by rfl⟩ : syracuseStep 14939387 = 22409081) B22409081
theorem B1840511 : Blo 1226431 1840511 := bstep (se 1 (by rfl) ⟨1380383, by rfl⟩ : syracuseStep 1840511 = 2760767) B2760767
theorem B3929579 : Blo 1226431 3929579 := bstep (se 1 (by rfl) ⟨2947184, by rfl⟩ : syracuseStep 3929579 = 5894369) B5894369
theorem B1226471 : Blo 1226431 1226471 := bstep (se 1 (by rfl) ⟨919853, by rfl⟩ : syracuseStep 1226471 = 1839707) B1839707
theorem B6993661 : Blo 1226431 6993661 := bstep (se 3 (by rfl) ⟨1311311, by rfl⟩ : syracuseStep 6993661 = 2622623) B2622623
theorem B4142879 : Blo 1226431 4142879 := bstep (se 1 (by rfl) ⟨3107159, by rfl⟩ : syracuseStep 4142879 = 6214319) B6214319
theorem B7460747 : Blo 1226431 7460747 := bstep (se 1 (by rfl) ⟨5595560, by rfl⟩ : syracuseStep 7460747 = 11191121) B11191121
theorem B13973471 : Blo 1226431 13973471 := bstep (se 1 (by rfl) ⟨10480103, by rfl⟩ : syracuseStep 13973471 = 20960207) B20960207
theorem B1226799 : Blo 1226431 1226799 := bstep (se 1 (by rfl) ⟨920099, by rfl⟩ : syracuseStep 1226799 = 1840199) B1840199
theorem B1841207 : Blo 1226431 1841207 := bstep (se 1 (by rfl) ⟨1380905, by rfl⟩ : syracuseStep 1841207 = 2761811) B2761811
theorem B81827921 : Blo 1226431 81827921 := bstep (se 2 (by rfl) ⟨30685470, by rfl⟩ : syracuseStep 81827921 = 61370941) B61370941
theorem B1227551 : Blo 1226431 1227551 := bstep (se 1 (by rfl) ⟨920663, by rfl⟩ : syracuseStep 1227551 = 1841327) B1841327
theorem B2759849 : Blo 1226431 2759849 := bstep (se 2 (by rfl) ⟨1034943, by rfl⟩ : syracuseStep 2759849 = 2069887) B2069887
theorem B1842587 : Blo 1226431 1842587 := bstep (se 1 (by rfl) ⟨1381940, by rfl⟩ : syracuseStep 1842587 = 2763881) B2763881
theorem B1228319 : Blo 1226431 1228319 := bstep (se 1 (by rfl) ⟨921239, by rfl⟩ : syracuseStep 1228319 = 1842479) B1842479
theorem B6209135 : Blo 1226431 6209135 := bstep (se 1 (by rfl) ⟨4656851, by rfl⟩ : syracuseStep 6209135 = 9313703) B9313703
theorem B3104639 : Blo 1226431 3104639 := bstep (se 1 (by rfl) ⟨2328479, by rfl⟩ : syracuseStep 3104639 = 4656959) B4656959
theorem B9323423 : Blo 1226431 9323423 := bstep (se 1 (by rfl) ⟨6992567, by rfl⟩ : syracuseStep 9323423 = 13985135) B13985135
theorem B2761919 : Blo 1226431 2761919 := bstep (se 1 (by rfl) ⟨2071439, by rfl⟩ : syracuseStep 2761919 = 4142879) B4142879
theorem B4973831 : Blo 1226431 4973831 := bstep (se 1 (by rfl) ⟨3730373, by rfl⟩ : syracuseStep 4973831 = 7460747) B7460747
theorem B9315647 : Blo 1226431 9315647 := bstep (se 1 (by rfl) ⟨6986735, by rfl⟩ : syracuseStep 9315647 = 13973471) B13973471
theorem B46007783 : Blo 1226431 46007783 := bstep (se 1 (by rfl) ⟨34505837, by rfl⟩ : syracuseStep 46007783 = 69011675) B69011675
theorem B5244905 : Blo 1226431 5244905 := bstep (se 2 (by rfl) ⟨1966839, by rfl⟩ : syracuseStep 5244905 = 3933679) B3933679
theorem B14928095 : Blo 1226431 14928095 := bstep (se 1 (by rfl) ⟨11196071, by rfl⟩ : syracuseStep 14928095 = 22392143) B22392143
theorem B9324881 : Blo 1226431 9324881 := bstep (se 2 (by rfl) ⟨3496830, by rfl⟩ : syracuseStep 9324881 = 6993661) B6993661
theorem B4139423 : Blo 1226431 4139423 := bstep (se 1 (by rfl) ⟨3104567, by rfl⟩ : syracuseStep 4139423 = 6209135) B6209135
theorem B15756137 : Blo 1226431 15756137 := bstep (se 2 (by rfl) ⟨5908551, by rfl⟩ : syracuseStep 15756137 = 11817103) B11817103
theorem B84978665 : Blo 1226431 84978665 := bstep (se 2 (by rfl) ⟨31866999, by rfl⟩ : syracuseStep 84978665 = 63733999) B63733999
theorem B25194377 : Blo 1226431 25194377 := bstep (se 2 (by rfl) ⟨9447891, by rfl⟩ : syracuseStep 25194377 = 18895783) B18895783
theorem B7860671 : Blo 1226431 7860671 := bstep (se 1 (by rfl) ⟨5895503, by rfl⟩ : syracuseStep 7860671 = 11791007) B11791007
theorem B1552871 : Blo 1226431 1552871 := bstep (se 1 (by rfl) ⟨1164653, by rfl⟩ : syracuseStep 1552871 = 2329307) B2329307
theorem B9319049 : Blo 1226431 9319049 := bstep (se 2 (by rfl) ⟨3494643, by rfl⟩ : syracuseStep 9319049 = 6989287) B6989287
theorem B1839899 : Blo 1226431 1839899 := bstep (se 1 (by rfl) ⟨1379924, by rfl⟩ : syracuseStep 1839899 = 2759849) B2759849
theorem B7385917 : Blo 1226431 7385917 := bstep (se 3 (by rfl) ⟨1384859, by rfl⟩ : syracuseStep 7385917 = 2769719) B2769719
theorem B3732731 : Blo 1226431 3732731 := bstep (se 1 (by rfl) ⟨2799548, by rfl⟩ : syracuseStep 3732731 = 5599097) B5599097
theorem B2069759 : Blo 1226431 2069759 := bstep (se 1 (by rfl) ⟨1552319, by rfl⟩ : syracuseStep 2069759 = 3104639) B3104639
theorem B218207789 : Blo 1226431 218207789 := bstep (se 3 (by rfl) ⟨40913960, by rfl⟩ : syracuseStep 218207789 = 81827921) B81827921
theorem B1840745 : Blo 1226431 1840745 := bstep (se 2 (by rfl) ⟨690279, by rfl⟩ : syracuseStep 1840745 = 1380559) B1380559
theorem B1841321 : Blo 1226431 1841321 := bstep (se 2 (by rfl) ⟨690495, by rfl⟩ : syracuseStep 1841321 = 1380991) B1380991
theorem B9959591 : Blo 1226431 9959591 := bstep (se 1 (by rfl) ⟨7469693, by rfl⟩ : syracuseStep 9959591 = 14939387) B14939387
theorem B1227007 : Blo 1226431 1227007 := bstep (se 1 (by rfl) ⟨920255, by rfl⟩ : syracuseStep 1227007 = 1840511) B1840511
theorem B2619719 : Blo 1226431 2619719 := bstep (se 1 (by rfl) ⟨1964789, by rfl⟩ : syracuseStep 2619719 = 3929579) B3929579
theorem B1227471 : Blo 1226431 1227471 := bstep (se 1 (by rfl) ⟨920603, by rfl⟩ : syracuseStep 1227471 = 1841207) B1841207
theorem B1841897 : Blo 1226431 1841897 := bstep (se 2 (by rfl) ⟨690711, by rfl⟩ : syracuseStep 1841897 = 1381423) B1381423
theorem B22715407 : Blo 1226431 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B3497195 : Blo 1226431 3497195 := bstep (se 1 (by rfl) ⟨2622896, by rfl⟩ : syracuseStep 3497195 = 5245793) B5245793
theorem B1842431 : Blo 1226431 1842431 := bstep (se 1 (by rfl) ⟨1381823, by rfl⟩ : syracuseStep 1842431 = 2763647) B2763647
theorem B1228391 : Blo 1226431 1228391 := bstep (se 1 (by rfl) ⟨921293, by rfl⟩ : syracuseStep 1228391 = 1842587) B1842587
theorem B2760551 : Blo 1226431 2760551 := bstep (se 1 (by rfl) ⟨2070413, by rfl⟩ : syracuseStep 2760551 = 4140827) B4140827
theorem B6210431 : Blo 1226431 6210431 := bstep (se 1 (by rfl) ⟨4657823, by rfl⟩ : syracuseStep 6210431 = 9315647) B9315647
theorem B30671855 : Blo 1226431 30671855 := bstep (se 1 (by rfl) ⟨23003891, by rfl⟩ : syracuseStep 30671855 = 46007783) B46007783
theorem B9847889 : Blo 1226431 9847889 := bstep (se 2 (by rfl) ⟨3692958, by rfl⟩ : syracuseStep 9847889 = 7385917) B7385917
theorem B30287209 : Blo 1226431 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B1746479 : Blo 1226431 1746479 := bstep (se 1 (by rfl) ⟨1309859, by rfl⟩ : syracuseStep 1746479 = 2619719) B2619719
theorem B10504091 : Blo 1226431 10504091 := bstep (se 1 (by rfl) ⟨7878068, by rfl⟩ : syracuseStep 10504091 = 15756137) B15756137
theorem B16796251 : Blo 1226431 16796251 := bstep (se 1 (by rfl) ⟨12597188, by rfl⟩ : syracuseStep 16796251 = 25194377) B25194377
theorem B6212699 : Blo 1226431 6212699 := bstep (se 1 (by rfl) ⟨4659524, by rfl⟩ : syracuseStep 6212699 = 9319049) B9319049
theorem B39808253 : Blo 1226431 39808253 := bstep (se 3 (by rfl) ⟨7464047, by rfl⟩ : syracuseStep 39808253 = 14928095) B14928095
theorem B9325853 : Blo 1226431 9325853 := bstep (se 3 (by rfl) ⟨1748597, by rfl⟩ : syracuseStep 9325853 = 3497195) B3497195
theorem B1379839 : Blo 1226431 1379839 := bstep (se 1 (by rfl) ⟨1034879, by rfl⟩ : syracuseStep 1379839 = 2069759) B2069759
theorem B4140989 : Blo 1226431 4140989 := bstep (se 3 (by rfl) ⟨776435, by rfl⟩ : syracuseStep 4140989 = 1552871) B1552871
theorem B6639727 : Blo 1226431 6639727 := bstep (se 1 (by rfl) ⟨4979795, by rfl⟩ : syracuseStep 6639727 = 9959591) B9959591
theorem B56652443 : Blo 1226431 56652443 := bstep (se 1 (by rfl) ⟨42489332, by rfl⟩ : syracuseStep 56652443 = 84978665) B84978665
theorem B1840367 : Blo 1226431 1840367 := bstep (se 1 (by rfl) ⟨1380275, by rfl⟩ : syracuseStep 1840367 = 2760551) B2760551
theorem B5240447 : Blo 1226431 5240447 := bstep (se 1 (by rfl) ⟨3930335, by rfl⟩ : syracuseStep 5240447 = 7860671) B7860671
theorem B1226599 : Blo 1226431 1226599 := bstep (se 1 (by rfl) ⟨919949, by rfl⟩ : syracuseStep 1226599 = 1839899) B1839899
theorem B6215615 : Blo 1226431 6215615 := bstep (se 1 (by rfl) ⟨4661711, by rfl⟩ : syracuseStep 6215615 = 9323423) B9323423
theorem B1841279 : Blo 1226431 1841279 := bstep (se 1 (by rfl) ⟨1380959, by rfl⟩ : syracuseStep 1841279 = 2761919) B2761919
theorem B2488487 : Blo 1226431 2488487 := bstep (se 1 (by rfl) ⟨1866365, by rfl⟩ : syracuseStep 2488487 = 3732731) B3732731
theorem B3315887 : Blo 1226431 3315887 := bstep (se 1 (by rfl) ⟨2486915, by rfl⟩ : syracuseStep 3315887 = 4973831) B4973831
theorem B145471859 : Blo 1226431 145471859 := bstep (se 1 (by rfl) ⟨109103894, by rfl⟩ : syracuseStep 145471859 = 218207789) B218207789
theorem B1227163 : Blo 1226431 1227163 := bstep (se 1 (by rfl) ⟨920372, by rfl⟩ : syracuseStep 1227163 = 1840745) B1840745
theorem B3496603 : Blo 1226431 3496603 := bstep (se 1 (by rfl) ⟨2622452, by rfl⟩ : syracuseStep 3496603 = 5244905) B5244905
theorem B1227547 : Blo 1226431 1227547 := bstep (se 1 (by rfl) ⟨920660, by rfl⟩ : syracuseStep 1227547 = 1841321) B1841321
theorem B6216587 : Blo 1226431 6216587 := bstep (se 1 (by rfl) ⟨4662440, by rfl⟩ : syracuseStep 6216587 = 9324881) B9324881
theorem B2759615 : Blo 1226431 2759615 := bstep (se 1 (by rfl) ⟨2069711, by rfl⟩ : syracuseStep 2759615 = 4139423) B4139423
theorem B1227931 : Blo 1226431 1227931 := bstep (se 1 (by rfl) ⟨920948, by rfl⟩ : syracuseStep 1227931 = 1841897) B1841897
theorem B1228287 : Blo 1226431 1228287 := bstep (se 1 (by rfl) ⟨921215, by rfl⟩ : syracuseStep 1228287 = 1842431) B1842431
theorem B20447903 : Blo 1226431 20447903 := bstep (se 1 (by rfl) ⟨15335927, by rfl⟩ : syracuseStep 20447903 = 30671855) B30671855
theorem B4662137 : Blo 1226431 4662137 := bstep (se 2 (by rfl) ⟨1748301, by rfl⟩ : syracuseStep 4662137 = 3496603) B3496603
theorem B26543861 : Blo 1226431 26543861 := bstep (se 5 (by rfl) ⟨1244243, by rfl⟩ : syracuseStep 26543861 = 2488487) B2488487
theorem B28010909 : Blo 1226431 28010909 := bstep (se 3 (by rfl) ⟨5252045, by rfl⟩ : syracuseStep 28010909 = 10504091) B10504091
theorem B37768295 : Blo 1226431 37768295 := bstep (se 1 (by rfl) ⟨28326221, by rfl⟩ : syracuseStep 37768295 = 56652443) B56652443
theorem B4140287 : Blo 1226431 4140287 := bstep (se 1 (by rfl) ⟨3105215, by rfl⟩ : syracuseStep 4140287 = 6210431) B6210431
theorem B6565259 : Blo 1226431 6565259 := bstep (se 1 (by rfl) ⟨4923944, by rfl⟩ : syracuseStep 6565259 = 9847889) B9847889
theorem B3493631 : Blo 1226431 3493631 := bstep (se 1 (by rfl) ⟨2620223, by rfl⟩ : syracuseStep 3493631 = 5240447) B5240447
theorem B4657277 : Blo 1226431 4657277 := bstep (se 3 (by rfl) ⟨873239, by rfl⟩ : syracuseStep 4657277 = 1746479) B1746479
theorem B96981239 : Blo 1226431 96981239 := bstep (se 1 (by rfl) ⟨72735929, by rfl⟩ : syracuseStep 96981239 = 145471859) B145471859
theorem B40382945 : Blo 1226431 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B1839743 : Blo 1226431 1839743 := bstep (se 1 (by rfl) ⟨1379807, by rfl⟩ : syracuseStep 1839743 = 2759615) B2759615
theorem B1839785 : Blo 1226431 1839785 := bstep (se 2 (by rfl) ⟨689919, by rfl⟩ : syracuseStep 1839785 = 1379839) B1379839
theorem B4141799 : Blo 1226431 4141799 := bstep (se 1 (by rfl) ⟨3106349, by rfl⟩ : syracuseStep 4141799 = 6212699) B6212699
theorem B26538835 : Blo 1226431 26538835 := bstep (se 1 (by rfl) ⟨19904126, by rfl⟩ : syracuseStep 26538835 = 39808253) B39808253
theorem B8852969 : Blo 1226431 8852969 := bstep (se 2 (by rfl) ⟨3319863, by rfl⟩ : syracuseStep 8852969 = 6639727) B6639727
theorem B22395001 : Blo 1226431 22395001 := bstep (se 2 (by rfl) ⟨8398125, by rfl⟩ : syracuseStep 22395001 = 16796251) B16796251
theorem B1226911 : Blo 1226431 1226911 := bstep (se 1 (by rfl) ⟨920183, by rfl⟩ : syracuseStep 1226911 = 1840367) B1840367
theorem B4143743 : Blo 1226431 4143743 := bstep (se 1 (by rfl) ⟨3107807, by rfl⟩ : syracuseStep 4143743 = 6215615) B6215615
theorem B1227519 : Blo 1226431 1227519 := bstep (se 1 (by rfl) ⟨920639, by rfl⟩ : syracuseStep 1227519 = 1841279) B1841279
theorem B2210591 : Blo 1226431 2210591 := bstep (se 1 (by rfl) ⟨1657943, by rfl⟩ : syracuseStep 2210591 = 3315887) B3315887
theorem B4144391 : Blo 1226431 4144391 := bstep (se 1 (by rfl) ⟨3108293, by rfl⟩ : syracuseStep 4144391 = 6216587) B6216587
theorem B6217235 : Blo 1226431 6217235 := bstep (se 1 (by rfl) ⟨4662926, by rfl⟩ : syracuseStep 6217235 = 9325853) B9325853
theorem B2760659 : Blo 1226431 2760659 := bstep (se 1 (by rfl) ⟨2070494, by rfl⟩ : syracuseStep 2760659 = 4140989) B4140989
theorem B3104851 : Blo 1226431 3104851 := bstep (se 1 (by rfl) ⟨2328638, by rfl⟩ : syracuseStep 3104851 = 4657277) B4657277
theorem B29860001 : Blo 1226431 29860001 := bstep (se 2 (by rfl) ⟨11197500, by rfl⟩ : syracuseStep 29860001 = 22395001) B22395001
theorem B13631935 : Blo 1226431 13631935 := bstep (se 1 (by rfl) ⟨10223951, by rfl⟩ : syracuseStep 13631935 = 20447903) B20447903
theorem B2761199 : Blo 1226431 2761199 := bstep (se 1 (by rfl) ⟨2070899, by rfl⟩ : syracuseStep 2761199 = 4141799) B4141799
theorem B17507357 : Blo 1226431 17507357 := bstep (se 3 (by rfl) ⟨3282629, by rfl⟩ : syracuseStep 17507357 = 6565259) B6565259
theorem B17695907 : Blo 1226431 17695907 := bstep (se 1 (by rfl) ⟨13271930, by rfl⟩ : syracuseStep 17695907 = 26543861) B26543861
theorem B2762495 : Blo 1226431 2762495 := bstep (se 1 (by rfl) ⟨2071871, by rfl⟩ : syracuseStep 2762495 = 4143743) B4143743
theorem B2762927 : Blo 1226431 2762927 := bstep (se 1 (by rfl) ⟨2072195, by rfl⟩ : syracuseStep 2762927 = 4144391) B4144391
theorem B2329087 : Blo 1226431 2329087 := bstep (se 1 (by rfl) ⟨1746815, by rfl⟩ : syracuseStep 2329087 = 3493631) B3493631
theorem B64654159 : Blo 1226431 64654159 := bstep (se 1 (by rfl) ⟨48490619, by rfl⟩ : syracuseStep 64654159 = 96981239) B96981239
theorem B26921963 : Blo 1226431 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B3108091 : Blo 1226431 3108091 := bstep (se 1 (by rfl) ⟨2331068, by rfl⟩ : syracuseStep 3108091 = 4662137) B4662137
theorem B5901979 : Blo 1226431 5901979 := bstep (se 1 (by rfl) ⟨4426484, by rfl⟩ : syracuseStep 5901979 = 8852969) B8852969
theorem B35385113 : Blo 1226431 35385113 := bstep (se 2 (by rfl) ⟨13269417, by rfl⟩ : syracuseStep 35385113 = 26538835) B26538835
theorem B18673939 : Blo 1226431 18673939 := bstep (se 1 (by rfl) ⟨14005454, by rfl⟩ : syracuseStep 18673939 = 28010909) B28010909
theorem B25178863 : Blo 1226431 25178863 := bstep (se 1 (by rfl) ⟨18884147, by rfl⟩ : syracuseStep 25178863 = 37768295) B37768295
theorem B1840439 : Blo 1226431 1840439 := bstep (se 1 (by rfl) ⟨1380329, by rfl⟩ : syracuseStep 1840439 = 2760659) B2760659
theorem B1226495 : Blo 1226431 1226495 := bstep (se 1 (by rfl) ⟨919871, by rfl⟩ : syracuseStep 1226495 = 1839743) B1839743
theorem B1226523 : Blo 1226431 1226523 := bstep (se 1 (by rfl) ⟨919892, by rfl⟩ : syracuseStep 1226523 = 1839785) B1839785
theorem B1473727 : Blo 1226431 1473727 := bstep (se 1 (by rfl) ⟨1105295, by rfl⟩ : syracuseStep 1473727 = 2210591) B2210591
theorem B2760191 : Blo 1226431 2760191 := bstep (se 1 (by rfl) ⟨2070143, by rfl⟩ : syracuseStep 2760191 = 4140287) B4140287
theorem B4144823 : Blo 1226431 4144823 := bstep (se 1 (by rfl) ⟨3108617, by rfl⟩ : syracuseStep 4144823 = 6217235) B6217235
theorem B19906667 : Blo 1226431 19906667 := bstep (se 1 (by rfl) ⟨14930000, by rfl⟩ : syracuseStep 19906667 = 29860001) B29860001
theorem B3105449 : Blo 1226431 3105449 := bstep (se 2 (by rfl) ⟨1164543, by rfl⟩ : syracuseStep 3105449 = 2329087) B2329087
theorem B11797271 : Blo 1226431 11797271 := bstep (se 1 (by rfl) ⟨8847953, by rfl⟩ : syracuseStep 11797271 = 17695907) B17695907
theorem B33571817 : Blo 1226431 33571817 := bstep (se 2 (by rfl) ⟨12589431, by rfl⟩ : syracuseStep 33571817 = 25178863) B25178863
theorem B86205545 : Blo 1226431 86205545 := bstep (se 2 (by rfl) ⟨32327079, by rfl⟩ : syracuseStep 86205545 = 64654159) B64654159
theorem B2763215 : Blo 1226431 2763215 := bstep (se 1 (by rfl) ⟨2072411, by rfl⟩ : syracuseStep 2763215 = 4144823) B4144823
theorem B4139801 : Blo 1226431 4139801 := bstep (se 2 (by rfl) ⟨1552425, by rfl⟩ : syracuseStep 4139801 = 3104851) B3104851
theorem B24898585 : Blo 1226431 24898585 := bstep (se 2 (by rfl) ⟨9336969, by rfl⟩ : syracuseStep 24898585 = 18673939) B18673939
theorem B7869305 : Blo 1226431 7869305 := bstep (se 2 (by rfl) ⟨2950989, by rfl⟩ : syracuseStep 7869305 = 5901979) B5901979
theorem B1840127 : Blo 1226431 1840127 := bstep (se 1 (by rfl) ⟨1380095, by rfl⟩ : syracuseStep 1840127 = 2760191) B2760191
theorem B23590075 : Blo 1226431 23590075 := bstep (se 1 (by rfl) ⟨17692556, by rfl⟩ : syracuseStep 23590075 = 35385113) B35385113
theorem B1840799 : Blo 1226431 1840799 := bstep (se 1 (by rfl) ⟨1380599, by rfl⟩ : syracuseStep 1840799 = 2761199) B2761199
theorem B18175913 : Blo 1226431 18175913 := bstep (se 2 (by rfl) ⟨6815967, by rfl⟩ : syracuseStep 18175913 = 13631935) B13631935
theorem B11671571 : Blo 1226431 11671571 := bstep (se 1 (by rfl) ⟨8753678, by rfl⟩ : syracuseStep 11671571 = 17507357) B17507357
theorem B1226959 : Blo 1226431 1226959 := bstep (se 1 (by rfl) ⟨920219, by rfl⟩ : syracuseStep 1226959 = 1840439) B1840439
theorem B1841663 : Blo 1226431 1841663 := bstep (se 1 (by rfl) ⟨1381247, by rfl⟩ : syracuseStep 1841663 = 2762495) B2762495
theorem B1841951 : Blo 1226431 1841951 := bstep (se 1 (by rfl) ⟨1381463, by rfl⟩ : syracuseStep 1841951 = 2762927) B2762927
theorem B1964969 : Blo 1226431 1964969 := bstep (se 2 (by rfl) ⟨736863, by rfl⟩ : syracuseStep 1964969 = 1473727) B1473727
theorem B4144121 : Blo 1226431 4144121 := bstep (se 2 (by rfl) ⟨1554045, by rfl⟩ : syracuseStep 4144121 = 3108091) B3108091
theorem B17947975 : Blo 1226431 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B13271111 : Blo 1226431 13271111 := bstep (se 1 (by rfl) ⟨9953333, by rfl⟩ : syracuseStep 13271111 = 19906667) B19906667
theorem B7864847 : Blo 1226431 7864847 := bstep (se 1 (by rfl) ⟨5898635, by rfl⟩ : syracuseStep 7864847 = 11797271) B11797271
theorem B22381211 : Blo 1226431 22381211 := bstep (se 1 (by rfl) ⟨16785908, by rfl⟩ : syracuseStep 22381211 = 33571817) B33571817
theorem B12117275 : Blo 1226431 12117275 := bstep (se 1 (by rfl) ⟨9087956, by rfl⟩ : syracuseStep 12117275 = 18175913) B18175913
theorem B23930633 : Blo 1226431 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B2762747 : Blo 1226431 2762747 := bstep (se 1 (by rfl) ⟨2072060, by rfl⟩ : syracuseStep 2762747 = 4144121) B4144121
theorem B31124189 : Blo 1226431 31124189 := bstep (se 3 (by rfl) ⟨5835785, by rfl⟩ : syracuseStep 31124189 = 11671571) B11671571
theorem B5246203 : Blo 1226431 5246203 := bstep (se 1 (by rfl) ⟨3934652, by rfl⟩ : syracuseStep 5246203 = 7869305) B7869305
theorem B57470363 : Blo 1226431 57470363 := bstep (se 1 (by rfl) ⟨43102772, by rfl⟩ : syracuseStep 57470363 = 86205545) B86205545
theorem B33198113 : Blo 1226431 33198113 := bstep (se 2 (by rfl) ⟨12449292, by rfl⟩ : syracuseStep 33198113 = 24898585) B24898585
theorem B31453433 : Blo 1226431 31453433 := bstep (se 2 (by rfl) ⟨11795037, by rfl⟩ : syracuseStep 31453433 = 23590075) B23590075
theorem B2070299 : Blo 1226431 2070299 := bstep (se 1 (by rfl) ⟨1552724, by rfl⟩ : syracuseStep 2070299 = 3105449) B3105449
theorem B1226751 : Blo 1226431 1226751 := bstep (se 1 (by rfl) ⟨920063, by rfl⟩ : syracuseStep 1226751 = 1840127) B1840127
theorem B1227199 : Blo 1226431 1227199 := bstep (se 1 (by rfl) ⟨920399, by rfl⟩ : syracuseStep 1227199 = 1840799) B1840799
theorem B1842143 : Blo 1226431 1842143 := bstep (se 1 (by rfl) ⟨1381607, by rfl⟩ : syracuseStep 1842143 = 2763215) B2763215
theorem B1227775 : Blo 1226431 1227775 := bstep (se 1 (by rfl) ⟨920831, by rfl⟩ : syracuseStep 1227775 = 1841663) B1841663
theorem B2759867 : Blo 1226431 2759867 := bstep (se 1 (by rfl) ⟨2069900, by rfl⟩ : syracuseStep 2759867 = 4139801) B4139801
theorem B1227967 : Blo 1226431 1227967 := bstep (se 1 (by rfl) ⟨920975, by rfl⟩ : syracuseStep 1227967 = 1841951) B1841951
theorem B1309979 : Blo 1226431 1309979 := bstep (se 1 (by rfl) ⟨982484, by rfl⟩ : syracuseStep 1309979 = 1964969) B1964969
theorem B8847407 : Blo 1226431 8847407 := bstep (se 1 (by rfl) ⟨6635555, by rfl⟩ : syracuseStep 8847407 = 13271111) B13271111
theorem B5243231 : Blo 1226431 5243231 := bstep (se 1 (by rfl) ⟨3932423, by rfl⟩ : syracuseStep 5243231 = 7864847) B7864847
theorem B8078183 : Blo 1226431 8078183 := bstep (se 1 (by rfl) ⟨6058637, by rfl⟩ : syracuseStep 8078183 = 12117275) B12117275
theorem B14920807 : Blo 1226431 14920807 := bstep (se 1 (by rfl) ⟨11190605, by rfl⟩ : syracuseStep 14920807 = 22381211) B22381211
theorem B3493277 : Blo 1226431 3493277 := bstep (se 3 (by rfl) ⟨654989, by rfl⟩ : syracuseStep 3493277 = 1309979) B1309979
theorem B15953755 : Blo 1226431 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B1380199 : Blo 1226431 1380199 := bstep (se 1 (by rfl) ⟨1035149, by rfl⟩ : syracuseStep 1380199 = 2070299) B2070299
theorem B1839911 : Blo 1226431 1839911 := bstep (se 1 (by rfl) ⟨1379933, by rfl⟩ : syracuseStep 1839911 = 2759867) B2759867
theorem B20749459 : Blo 1226431 20749459 := bstep (se 1 (by rfl) ⟨15562094, by rfl⟩ : syracuseStep 20749459 = 31124189) B31124189
theorem B22132075 : Blo 1226431 22132075 := bstep (se 1 (by rfl) ⟨16599056, by rfl⟩ : syracuseStep 22132075 = 33198113) B33198113
theorem B20968955 : Blo 1226431 20968955 := bstep (se 1 (by rfl) ⟨15726716, by rfl⟩ : syracuseStep 20968955 = 31453433) B31453433
theorem B1841831 : Blo 1226431 1841831 := bstep (se 1 (by rfl) ⟨1381373, by rfl⟩ : syracuseStep 1841831 = 2762747) B2762747
theorem B6994937 : Blo 1226431 6994937 := bstep (se 2 (by rfl) ⟨2623101, by rfl⟩ : syracuseStep 6994937 = 5246203) B5246203
theorem B1228095 : Blo 1226431 1228095 := bstep (se 1 (by rfl) ⟨921071, by rfl⟩ : syracuseStep 1228095 = 1842143) B1842143
theorem B38313575 : Blo 1226431 38313575 := bstep (se 1 (by rfl) ⟨28735181, by rfl⟩ : syracuseStep 38313575 = 57470363) B57470363
theorem B5898271 : Blo 1226431 5898271 := bstep (se 1 (by rfl) ⟨4423703, by rfl⟩ : syracuseStep 5898271 = 8847407) B8847407
theorem B27665945 : Blo 1226431 27665945 := bstep (se 2 (by rfl) ⟨10374729, by rfl⟩ : syracuseStep 27665945 = 20749459) B20749459
theorem B29509433 : Blo 1226431 29509433 := bstep (se 2 (by rfl) ⟨11066037, by rfl⟩ : syracuseStep 29509433 = 22132075) B22132075
theorem B4663291 : Blo 1226431 4663291 := bstep (se 1 (by rfl) ⟨3497468, by rfl⟩ : syracuseStep 4663291 = 6994937) B6994937
theorem B2328851 : Blo 1226431 2328851 := bstep (se 1 (by rfl) ⟨1746638, by rfl⟩ : syracuseStep 2328851 = 3493277) B3493277
theorem B5385455 : Blo 1226431 5385455 := bstep (se 1 (by rfl) ⟨4039091, by rfl⟩ : syracuseStep 5385455 = 8078183) B8078183
theorem B13979303 : Blo 1226431 13979303 := bstep (se 1 (by rfl) ⟨10484477, by rfl⟩ : syracuseStep 13979303 = 20968955) B20968955
theorem B19894409 : Blo 1226431 19894409 := bstep (se 2 (by rfl) ⟨7460403, by rfl⟩ : syracuseStep 19894409 = 14920807) B14920807
theorem B21271673 : Blo 1226431 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B1840265 : Blo 1226431 1840265 := bstep (se 2 (by rfl) ⟨690099, by rfl⟩ : syracuseStep 1840265 = 1380199) B1380199
theorem B3495487 : Blo 1226431 3495487 := bstep (se 1 (by rfl) ⟨2621615, by rfl⟩ : syracuseStep 3495487 = 5243231) B5243231
theorem B1226607 : Blo 1226431 1226607 := bstep (se 1 (by rfl) ⟨919955, by rfl⟩ : syracuseStep 1226607 = 1839911) B1839911
theorem B1227887 : Blo 1226431 1227887 := bstep (se 1 (by rfl) ⟨920915, by rfl⟩ : syracuseStep 1227887 = 1841831) B1841831
theorem B25542383 : Blo 1226431 25542383 := bstep (se 1 (by rfl) ⟨19156787, by rfl⟩ : syracuseStep 25542383 = 38313575) B38313575
theorem B7864361 : Blo 1226431 7864361 := bstep (se 2 (by rfl) ⟨2949135, by rfl⟩ : syracuseStep 7864361 = 5898271) B5898271
theorem B13262939 : Blo 1226431 13262939 := bstep (se 1 (by rfl) ⟨9947204, by rfl⟩ : syracuseStep 13262939 = 19894409) B19894409
theorem B6210269 : Blo 1226431 6210269 := bstep (se 3 (by rfl) ⟨1164425, by rfl⟩ : syracuseStep 6210269 = 2328851) B2328851
theorem B3590303 : Blo 1226431 3590303 := bstep (se 1 (by rfl) ⟨2692727, by rfl⟩ : syracuseStep 3590303 = 5385455) B5385455
theorem B56724461 : Blo 1226431 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B18443963 : Blo 1226431 18443963 := bstep (se 1 (by rfl) ⟨13832972, by rfl⟩ : syracuseStep 18443963 = 27665945) B27665945
theorem B19672955 : Blo 1226431 19672955 := bstep (se 1 (by rfl) ⟨14754716, by rfl⟩ : syracuseStep 19672955 = 29509433) B29509433
theorem B68113021 : Blo 1226431 68113021 := bstep (se 3 (by rfl) ⟨12771191, by rfl⟩ : syracuseStep 68113021 = 25542383) B25542383
theorem B9319535 : Blo 1226431 9319535 := bstep (se 1 (by rfl) ⟨6989651, by rfl⟩ : syracuseStep 9319535 = 13979303) B13979303
theorem B1226843 : Blo 1226431 1226843 := bstep (se 1 (by rfl) ⟨920132, by rfl⟩ : syracuseStep 1226843 = 1840265) B1840265
theorem B4660649 : Blo 1226431 4660649 := bstep (se 2 (by rfl) ⟨1747743, by rfl⟩ : syracuseStep 4660649 = 3495487) B3495487
theorem B6217721 : Blo 1226431 6217721 := bstep (se 2 (by rfl) ⟨2331645, by rfl⟩ : syracuseStep 6217721 = 4663291) B4663291
theorem B5242907 : Blo 1226431 5242907 := bstep (se 1 (by rfl) ⟨3932180, by rfl⟩ : syracuseStep 5242907 = 7864361) B7864361
theorem B90817361 : Blo 1226431 90817361 := bstep (se 2 (by rfl) ⟨34056510, by rfl⟩ : syracuseStep 90817361 = 68113021) B68113021
theorem B37816307 : Blo 1226431 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B3107099 : Blo 1226431 3107099 := bstep (se 1 (by rfl) ⟨2330324, by rfl⟩ : syracuseStep 3107099 = 4660649) B4660649
theorem B8841959 : Blo 1226431 8841959 := bstep (se 1 (by rfl) ⟨6631469, by rfl⟩ : syracuseStep 8841959 = 13262939) B13262939
theorem B4140179 : Blo 1226431 4140179 := bstep (se 1 (by rfl) ⟨3105134, by rfl⟩ : syracuseStep 4140179 = 6210269) B6210269
theorem B6213023 : Blo 1226431 6213023 := bstep (se 1 (by rfl) ⟨4659767, by rfl⟩ : syracuseStep 6213023 = 9319535) B9319535
theorem B9574141 : Blo 1226431 9574141 := bstep (se 3 (by rfl) ⟨1795151, by rfl⟩ : syracuseStep 9574141 = 3590303) B3590303
theorem B12295975 : Blo 1226431 12295975 := bstep (se 1 (by rfl) ⟨9221981, by rfl⟩ : syracuseStep 12295975 = 18443963) B18443963
theorem B13115303 : Blo 1226431 13115303 := bstep (se 1 (by rfl) ⟨9836477, by rfl⟩ : syracuseStep 13115303 = 19672955) B19672955
theorem B4145147 : Blo 1226431 4145147 := bstep (se 1 (by rfl) ⟨3108860, by rfl⟩ : syracuseStep 4145147 = 6217721) B6217721
theorem B12765521 : Blo 1226431 12765521 := bstep (se 2 (by rfl) ⟨4787070, by rfl⟩ : syracuseStep 12765521 = 9574141) B9574141
theorem B16394633 : Blo 1226431 16394633 := bstep (se 2 (by rfl) ⟨6147987, by rfl⟩ : syracuseStep 16394633 = 12295975) B12295975
theorem B8743535 : Blo 1226431 8743535 := bstep (se 1 (by rfl) ⟨6557651, by rfl⟩ : syracuseStep 8743535 = 13115303) B13115303
theorem B2763431 : Blo 1226431 2763431 := bstep (se 1 (by rfl) ⟨2072573, by rfl⟩ : syracuseStep 2763431 = 4145147) B4145147
theorem B25210871 : Blo 1226431 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B5894639 : Blo 1226431 5894639 := bstep (se 1 (by rfl) ⟨4420979, by rfl⟩ : syracuseStep 5894639 = 8841959) B8841959
theorem B4142015 : Blo 1226431 4142015 := bstep (se 1 (by rfl) ⟨3106511, by rfl⟩ : syracuseStep 4142015 = 6213023) B6213023
theorem B3495271 : Blo 1226431 3495271 := bstep (se 1 (by rfl) ⟨2621453, by rfl⟩ : syracuseStep 3495271 = 5242907) B5242907
theorem B60544907 : Blo 1226431 60544907 := bstep (se 1 (by rfl) ⟨45408680, by rfl⟩ : syracuseStep 60544907 = 90817361) B90817361
theorem B2071399 : Blo 1226431 2071399 := bstep (se 1 (by rfl) ⟨1553549, by rfl⟩ : syracuseStep 2071399 = 3107099) B3107099
theorem B2760119 : Blo 1226431 2760119 := bstep (se 1 (by rfl) ⟨2070089, by rfl⟩ : syracuseStep 2760119 = 4140179) B4140179
theorem B2761343 : Blo 1226431 2761343 := bstep (se 1 (by rfl) ⟨2071007, by rfl⟩ : syracuseStep 2761343 = 4142015) B4142015
theorem B2761865 : Blo 1226431 2761865 := bstep (se 2 (by rfl) ⟨1035699, by rfl⟩ : syracuseStep 2761865 = 2071399) B2071399
theorem B40363271 : Blo 1226431 40363271 := bstep (se 1 (by rfl) ⟨30272453, by rfl⟩ : syracuseStep 40363271 = 60544907) B60544907
theorem B10929755 : Blo 1226431 10929755 := bstep (se 1 (by rfl) ⟨8197316, by rfl⟩ : syracuseStep 10929755 = 16394633) B16394633
theorem B5829023 : Blo 1226431 5829023 := bstep (se 1 (by rfl) ⟨4371767, by rfl⟩ : syracuseStep 5829023 = 8743535) B8743535
theorem B1840079 : Blo 1226431 1840079 := bstep (se 1 (by rfl) ⟨1380059, by rfl⟩ : syracuseStep 1840079 = 2760119) B2760119
theorem B16807247 : Blo 1226431 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B3929759 : Blo 1226431 3929759 := bstep (se 1 (by rfl) ⟨2947319, by rfl⟩ : syracuseStep 3929759 = 5894639) B5894639
theorem B8510347 : Blo 1226431 8510347 := bstep (se 1 (by rfl) ⟨6382760, by rfl⟩ : syracuseStep 8510347 = 12765521) B12765521
theorem B1842287 : Blo 1226431 1842287 := bstep (se 1 (by rfl) ⟨1381715, by rfl⟩ : syracuseStep 1842287 = 2763431) B2763431
theorem B4660361 : Blo 1226431 4660361 := bstep (se 2 (by rfl) ⟨1747635, by rfl⟩ : syracuseStep 4660361 = 3495271) B3495271
theorem B11347129 : Blo 1226431 11347129 := bstep (se 2 (by rfl) ⟨4255173, by rfl⟩ : syracuseStep 11347129 = 8510347) B8510347
theorem B3106907 : Blo 1226431 3106907 := bstep (se 1 (by rfl) ⟨2330180, by rfl⟩ : syracuseStep 3106907 = 4660361) B4660361
theorem B3886015 : Blo 1226431 3886015 := bstep (se 1 (by rfl) ⟨2914511, by rfl⟩ : syracuseStep 3886015 = 5829023) B5829023
theorem B1840895 : Blo 1226431 1840895 := bstep (se 1 (by rfl) ⟨1380671, by rfl⟩ : syracuseStep 1840895 = 2761343) B2761343
theorem B1226719 : Blo 1226431 1226719 := bstep (se 1 (by rfl) ⟨920039, by rfl⟩ : syracuseStep 1226719 = 1840079) B1840079
theorem B1841243 : Blo 1226431 1841243 := bstep (se 1 (by rfl) ⟨1380932, by rfl⟩ : syracuseStep 1841243 = 2761865) B2761865
theorem B26908847 : Blo 1226431 26908847 := bstep (se 1 (by rfl) ⟨20181635, by rfl⟩ : syracuseStep 26908847 = 40363271) B40363271
theorem B11204831 : Blo 1226431 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B2619839 : Blo 1226431 2619839 := bstep (se 1 (by rfl) ⟨1964879, by rfl⟩ : syracuseStep 2619839 = 3929759) B3929759
theorem B29146013 : Blo 1226431 29146013 := bstep (se 3 (by rfl) ⟨5464877, by rfl⟩ : syracuseStep 29146013 = 10929755) B10929755
theorem B1228191 : Blo 1226431 1228191 := bstep (se 1 (by rfl) ⟨921143, by rfl⟩ : syracuseStep 1228191 = 1842287) B1842287
theorem B1746559 : Blo 1226431 1746559 := bstep (se 1 (by rfl) ⟨1309919, by rfl⟩ : syracuseStep 1746559 = 2619839) B2619839
theorem B5181353 : Blo 1226431 5181353 := bstep (se 2 (by rfl) ⟨1943007, by rfl⟩ : syracuseStep 5181353 = 3886015) B3886015
theorem B1227263 : Blo 1226431 1227263 := bstep (se 1 (by rfl) ⟨920447, by rfl⟩ : syracuseStep 1227263 = 1840895) B1840895
theorem B2071271 : Blo 1226431 2071271 := bstep (se 1 (by rfl) ⟨1553453, by rfl⟩ : syracuseStep 2071271 = 3106907) B3106907
theorem B1227495 : Blo 1226431 1227495 := bstep (se 1 (by rfl) ⟨920621, by rfl⟩ : syracuseStep 1227495 = 1841243) B1841243
theorem B17939231 : Blo 1226431 17939231 := bstep (se 1 (by rfl) ⟨13454423, by rfl⟩ : syracuseStep 17939231 = 26908847) B26908847
theorem B7469887 : Blo 1226431 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B15129505 : Blo 1226431 15129505 := bstep (se 2 (by rfl) ⟨5673564, by rfl⟩ : syracuseStep 15129505 = 11347129) B11347129
theorem B19430675 : Blo 1226431 19430675 := bstep (se 1 (by rfl) ⟨14573006, by rfl⟩ : syracuseStep 19430675 = 29146013) B29146013
theorem B2328745 : Blo 1226431 2328745 := bstep (se 2 (by rfl) ⟨873279, by rfl⟩ : syracuseStep 2328745 = 1746559) B1746559
theorem B12953783 : Blo 1226431 12953783 := bstep (se 1 (by rfl) ⟨9715337, by rfl⟩ : syracuseStep 12953783 = 19430675) B19430675
theorem B20172673 : Blo 1226431 20172673 := bstep (se 2 (by rfl) ⟨7564752, by rfl⟩ : syracuseStep 20172673 = 15129505) B15129505
theorem B1380847 : Blo 1226431 1380847 := bstep (se 1 (by rfl) ⟨1035635, by rfl⟩ : syracuseStep 1380847 = 2071271) B2071271
theorem B3454235 : Blo 1226431 3454235 := bstep (se 1 (by rfl) ⟨2590676, by rfl⟩ : syracuseStep 3454235 = 5181353) B5181353
theorem B9959849 : Blo 1226431 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B11959487 : Blo 1226431 11959487 := bstep (se 1 (by rfl) ⟨8969615, by rfl⟩ : syracuseStep 11959487 = 17939231) B17939231
theorem B3104993 : Blo 1226431 3104993 := bstep (se 2 (by rfl) ⟨1164372, by rfl⟩ : syracuseStep 3104993 = 2328745) B2328745
theorem B2302823 : Blo 1226431 2302823 := bstep (se 1 (by rfl) ⟨1727117, by rfl⟩ : syracuseStep 2302823 = 3454235) B3454235
theorem B8635855 : Blo 1226431 8635855 := bstep (se 1 (by rfl) ⟨6476891, by rfl⟩ : syracuseStep 8635855 = 12953783) B12953783
theorem B7972991 : Blo 1226431 7972991 := bstep (se 1 (by rfl) ⟨5979743, by rfl⟩ : syracuseStep 7972991 = 11959487) B11959487
theorem B26896897 : Blo 1226431 26896897 := bstep (se 2 (by rfl) ⟨10086336, by rfl⟩ : syracuseStep 26896897 = 20172673) B20172673
theorem B6639899 : Blo 1226431 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B1841129 : Blo 1226431 1841129 := bstep (se 2 (by rfl) ⟨690423, by rfl⟩ : syracuseStep 1841129 = 1380847) B1380847
theorem B1535215 : Blo 1226431 1535215 := bstep (se 1 (by rfl) ⟨1151411, by rfl⟩ : syracuseStep 1535215 = 2302823) B2302823
theorem B17706397 : Blo 1226431 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B11514473 : Blo 1226431 11514473 := bstep (se 2 (by rfl) ⟨4317927, by rfl⟩ : syracuseStep 11514473 = 8635855) B8635855
theorem B2069995 : Blo 1226431 2069995 := bstep (se 1 (by rfl) ⟨1552496, by rfl⟩ : syracuseStep 2069995 = 3104993) B3104993
theorem B35862529 : Blo 1226431 35862529 := bstep (se 2 (by rfl) ⟨13448448, by rfl⟩ : syracuseStep 35862529 = 26896897) B26896897
theorem B1227419 : Blo 1226431 1227419 := bstep (se 1 (by rfl) ⟨920564, by rfl⟩ : syracuseStep 1227419 = 1841129) B1841129
theorem B5315327 : Blo 1226431 5315327 := bstep (se 1 (by rfl) ⟨3986495, by rfl⟩ : syracuseStep 5315327 = 7972991) B7972991
theorem B47816705 : Blo 1226431 47816705 := bstep (se 2 (by rfl) ⟨17931264, by rfl⟩ : syracuseStep 47816705 = 35862529) B35862529
theorem B7676315 : Blo 1226431 7676315 := bstep (se 1 (by rfl) ⟨5757236, by rfl⟩ : syracuseStep 7676315 = 11514473) B11514473
theorem B3543551 : Blo 1226431 3543551 := bstep (se 1 (by rfl) ⟨2657663, by rfl⟩ : syracuseStep 3543551 = 5315327) B5315327
theorem B2046953 : Blo 1226431 2046953 := bstep (se 2 (by rfl) ⟨767607, by rfl⟩ : syracuseStep 2046953 = 1535215) B1535215
theorem B23608529 : Blo 1226431 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B2759993 : Blo 1226431 2759993 := bstep (se 2 (by rfl) ⟨1034997, by rfl⟩ : syracuseStep 2759993 = 2069995) B2069995
theorem B15739019 : Blo 1226431 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B31877803 : Blo 1226431 31877803 := bstep (se 1 (by rfl) ⟨23908352, by rfl⟩ : syracuseStep 31877803 = 47816705) B47816705
theorem B2362367 : Blo 1226431 2362367 := bstep (se 1 (by rfl) ⟨1771775, by rfl⟩ : syracuseStep 2362367 = 3543551) B3543551
theorem B1364635 : Blo 1226431 1364635 := bstep (se 1 (by rfl) ⟨1023476, by rfl⟩ : syracuseStep 1364635 = 2046953) B2046953
theorem B1839995 : Blo 1226431 1839995 := bstep (se 1 (by rfl) ⟨1379996, by rfl⟩ : syracuseStep 1839995 = 2759993) B2759993
theorem B5117543 : Blo 1226431 5117543 := bstep (se 1 (by rfl) ⟨3838157, by rfl⟩ : syracuseStep 5117543 = 7676315) B7676315
theorem B1819513 : Blo 1226431 1819513 := bstep (se 2 (by rfl) ⟨682317, by rfl⟩ : syracuseStep 1819513 = 1364635) B1364635
theorem B1574911 : Blo 1226431 1574911 := bstep (se 1 (by rfl) ⟨1181183, by rfl⟩ : syracuseStep 1574911 = 2362367) B2362367
theorem B42503737 : Blo 1226431 42503737 := bstep (se 2 (by rfl) ⟨15938901, by rfl⟩ : syracuseStep 42503737 = 31877803) B31877803
theorem B3411695 : Blo 1226431 3411695 := bstep (se 1 (by rfl) ⟨2558771, by rfl⟩ : syracuseStep 3411695 = 5117543) B5117543
theorem B1226663 : Blo 1226431 1226663 := bstep (se 1 (by rfl) ⟨919997, by rfl⟩ : syracuseStep 1226663 = 1839995) B1839995
theorem B10492679 : Blo 1226431 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B2099881 : Blo 1226431 2099881 := bstep (se 2 (by rfl) ⟨787455, by rfl⟩ : syracuseStep 2099881 = 1574911) B1574911
theorem B9704069 : Blo 1226431 9704069 := bstep (se 4 (by rfl) ⟨909756, by rfl⟩ : syracuseStep 9704069 = 1819513) B1819513
theorem B2274463 : Blo 1226431 2274463 := bstep (se 1 (by rfl) ⟨1705847, by rfl⟩ : syracuseStep 2274463 = 3411695) B3411695
theorem B6995119 : Blo 1226431 6995119 := bstep (se 1 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 6995119 = 10492679) B10492679
theorem B56671649 : Blo 1226431 56671649 := bstep (se 2 (by rfl) ⟨21251868, by rfl⟩ : syracuseStep 56671649 = 42503737) B42503737
theorem B9326825 : Blo 1226431 9326825 := bstep (se 2 (by rfl) ⟨3497559, by rfl⟩ : syracuseStep 9326825 = 6995119) B6995119
theorem B6469379 : Blo 1226431 6469379 := bstep (se 1 (by rfl) ⟨4852034, by rfl⟩ : syracuseStep 6469379 = 9704069) B9704069
theorem B12130469 : Blo 1226431 12130469 := bstep (se 4 (by rfl) ⟨1137231, by rfl⟩ : syracuseStep 12130469 = 2274463) B2274463
theorem B2799841 : Blo 1226431 2799841 := bstep (se 2 (by rfl) ⟨1049940, by rfl⟩ : syracuseStep 2799841 = 2099881) B2099881
theorem B37781099 : Blo 1226431 37781099 := bstep (se 1 (by rfl) ⟨28335824, by rfl⟩ : syracuseStep 37781099 = 56671649) B56671649
theorem B6217883 : Blo 1226431 6217883 := bstep (se 1 (by rfl) ⟨4663412, by rfl⟩ : syracuseStep 6217883 = 9326825) B9326825
theorem B8086979 : Blo 1226431 8086979 := bstep (se 1 (by rfl) ⟨6065234, by rfl⟩ : syracuseStep 8086979 = 12130469) B12130469
theorem B4312919 : Blo 1226431 4312919 := bstep (se 1 (by rfl) ⟨3234689, by rfl⟩ : syracuseStep 4312919 = 6469379) B6469379
theorem B25187399 : Blo 1226431 25187399 := bstep (se 1 (by rfl) ⟨18890549, by rfl⟩ : syracuseStep 25187399 = 37781099) B37781099
theorem B3733121 : Blo 1226431 3733121 := bstep (se 2 (by rfl) ⟨1399920, by rfl⟩ : syracuseStep 3733121 = 2799841) B2799841
theorem B4145255 : Blo 1226431 4145255 := bstep (se 1 (by rfl) ⟨3108941, by rfl⟩ : syracuseStep 4145255 = 6217883) B6217883
theorem B21565277 : Blo 1226431 21565277 := bstep (se 3 (by rfl) ⟨4043489, by rfl⟩ : syracuseStep 21565277 = 8086979) B8086979
theorem B16791599 : Blo 1226431 16791599 := bstep (se 1 (by rfl) ⟨12593699, by rfl⟩ : syracuseStep 16791599 = 25187399) B25187399
theorem B2488747 : Blo 1226431 2488747 := bstep (se 1 (by rfl) ⟨1866560, by rfl⟩ : syracuseStep 2488747 = 3733121) B3733121
theorem B2875279 : Blo 1226431 2875279 := bstep (se 1 (by rfl) ⟨2156459, by rfl⟩ : syracuseStep 2875279 = 4312919) B4312919
theorem B3318329 : Blo 1226431 3318329 := bstep (se 2 (by rfl) ⟨1244373, by rfl⟩ : syracuseStep 3318329 = 2488747) B2488747
theorem B2763503 : Blo 1226431 2763503 := bstep (se 1 (by rfl) ⟨2072627, by rfl⟩ : syracuseStep 2763503 = 4145255) B4145255
theorem B11194399 : Blo 1226431 11194399 := bstep (se 1 (by rfl) ⟨8395799, by rfl⟩ : syracuseStep 11194399 = 16791599) B16791599
theorem B3833705 : Blo 1226431 3833705 := bstep (se 2 (by rfl) ⟨1437639, by rfl⟩ : syracuseStep 3833705 = 2875279) B2875279
theorem B14376851 : Blo 1226431 14376851 := bstep (se 1 (by rfl) ⟨10782638, by rfl⟩ : syracuseStep 14376851 = 21565277) B21565277
theorem B14925865 : Blo 1226431 14925865 := bstep (se 2 (by rfl) ⟨5597199, by rfl⟩ : syracuseStep 14925865 = 11194399) B11194399
theorem B2212219 : Blo 1226431 2212219 := bstep (se 1 (by rfl) ⟨1659164, by rfl⟩ : syracuseStep 2212219 = 3318329) B3318329
theorem B1842335 : Blo 1226431 1842335 := bstep (se 1 (by rfl) ⟨1381751, by rfl⟩ : syracuseStep 1842335 = 2763503) B2763503
theorem B2555803 : Blo 1226431 2555803 := bstep (se 1 (by rfl) ⟨1916852, by rfl⟩ : syracuseStep 2555803 = 3833705) B3833705
theorem B9584567 : Blo 1226431 9584567 := bstep (se 1 (by rfl) ⟨7188425, by rfl⟩ : syracuseStep 9584567 = 14376851) B14376851
theorem B2949625 : Blo 1226431 2949625 := bstep (se 2 (by rfl) ⟨1106109, by rfl⟩ : syracuseStep 2949625 = 2212219) B2212219
theorem B19901153 : Blo 1226431 19901153 := bstep (se 2 (by rfl) ⟨7462932, by rfl⟩ : syracuseStep 19901153 = 14925865) B14925865
theorem B1228223 : Blo 1226431 1228223 := bstep (se 1 (by rfl) ⟨921167, by rfl⟩ : syracuseStep 1228223 = 1842335) B1842335
theorem B13630949 : Blo 1226431 13630949 := bstep (se 4 (by rfl) ⟨1277901, by rfl⟩ : syracuseStep 13630949 = 2555803) B2555803
theorem B6389711 : Blo 1226431 6389711 := bstep (se 1 (by rfl) ⟨4792283, by rfl⟩ : syracuseStep 6389711 = 9584567) B9584567
theorem B9087299 : Blo 1226431 9087299 := bstep (se 1 (by rfl) ⟨6815474, by rfl⟩ : syracuseStep 9087299 = 13630949) B13630949
theorem B15731333 : Blo 1226431 15731333 := bstep (se 4 (by rfl) ⟨1474812, by rfl⟩ : syracuseStep 15731333 = 2949625) B2949625
theorem B13267435 : Blo 1226431 13267435 := bstep (se 1 (by rfl) ⟨9950576, by rfl⟩ : syracuseStep 13267435 = 19901153) B19901153
theorem B4259807 : Blo 1226431 4259807 := bstep (se 1 (by rfl) ⟨3194855, by rfl⟩ : syracuseStep 4259807 = 6389711) B6389711
theorem B10487555 : Blo 1226431 10487555 := bstep (se 1 (by rfl) ⟨7865666, by rfl⟩ : syracuseStep 10487555 = 15731333) B15731333
theorem B17689913 : Blo 1226431 17689913 := bstep (se 2 (by rfl) ⟨6633717, by rfl⟩ : syracuseStep 17689913 = 13267435) B13267435
theorem B6058199 : Blo 1226431 6058199 := bstep (se 1 (by rfl) ⟨4543649, by rfl⟩ : syracuseStep 6058199 = 9087299) B9087299
theorem B2839871 : Blo 1226431 2839871 := bstep (se 1 (by rfl) ⟨2129903, by rfl⟩ : syracuseStep 2839871 = 4259807) B4259807
theorem B16155197 : Blo 1226431 16155197 := bstep (se 3 (by rfl) ⟨3029099, by rfl⟩ : syracuseStep 16155197 = 6058199) B6058199
theorem B7572989 : Blo 1226431 7572989 := bstep (se 3 (by rfl) ⟨1419935, by rfl⟩ : syracuseStep 7572989 = 2839871) B2839871
theorem B6991703 : Blo 1226431 6991703 := bstep (se 1 (by rfl) ⟨5243777, by rfl⟩ : syracuseStep 6991703 = 10487555) B10487555
theorem B11793275 : Blo 1226431 11793275 := bstep (se 1 (by rfl) ⟨8844956, by rfl⟩ : syracuseStep 11793275 = 17689913) B17689913
theorem B5048659 : Blo 1226431 5048659 := bstep (se 1 (by rfl) ⟨3786494, by rfl⟩ : syracuseStep 5048659 = 7572989) B7572989
theorem B10770131 : Blo 1226431 10770131 := bstep (se 1 (by rfl) ⟨8077598, by rfl⟩ : syracuseStep 10770131 = 16155197) B16155197
theorem B7862183 : Blo 1226431 7862183 := bstep (se 1 (by rfl) ⟨5896637, by rfl⟩ : syracuseStep 7862183 = 11793275) B11793275
theorem B4661135 : Blo 1226431 4661135 := bstep (se 1 (by rfl) ⟨3495851, by rfl⟩ : syracuseStep 4661135 = 6991703) B6991703
theorem B3107423 : Blo 1226431 3107423 := bstep (se 1 (by rfl) ⟨2330567, by rfl⟩ : syracuseStep 3107423 = 4661135) B4661135
theorem B6731545 : Blo 1226431 6731545 := bstep (se 2 (by rfl) ⟨2524329, by rfl⟩ : syracuseStep 6731545 = 5048659) B5048659
theorem B5241455 : Blo 1226431 5241455 := bstep (se 1 (by rfl) ⟨3931091, by rfl⟩ : syracuseStep 5241455 = 7862183) B7862183
theorem B28720349 : Blo 1226431 28720349 := bstep (se 3 (by rfl) ⟨5385065, by rfl⟩ : syracuseStep 28720349 = 10770131) B10770131
theorem B19146899 : Blo 1226431 19146899 := bstep (se 1 (by rfl) ⟨14360174, by rfl⟩ : syracuseStep 19146899 = 28720349) B28720349
theorem B3494303 : Blo 1226431 3494303 := bstep (se 1 (by rfl) ⟨2620727, by rfl⟩ : syracuseStep 3494303 = 5241455) B5241455
theorem B8975393 : Blo 1226431 8975393 := bstep (se 2 (by rfl) ⟨3365772, by rfl⟩ : syracuseStep 8975393 = 6731545) B6731545
theorem B2071615 : Blo 1226431 2071615 := bstep (se 1 (by rfl) ⟨1553711, by rfl⟩ : syracuseStep 2071615 = 3107423) B3107423
theorem B2762153 : Blo 1226431 2762153 := bstep (se 2 (by rfl) ⟨1035807, by rfl⟩ : syracuseStep 2762153 = 2071615) B2071615
theorem B2329535 : Blo 1226431 2329535 := bstep (se 1 (by rfl) ⟨1747151, by rfl⟩ : syracuseStep 2329535 = 3494303) B3494303
theorem B5983595 : Blo 1226431 5983595 := bstep (se 1 (by rfl) ⟨4487696, by rfl⟩ : syracuseStep 5983595 = 8975393) B8975393
theorem B51058397 : Blo 1226431 51058397 := bstep (se 3 (by rfl) ⟨9573449, by rfl⟩ : syracuseStep 51058397 = 19146899) B19146899
theorem B136155725 : Blo 1226431 136155725 := bstep (se 3 (by rfl) ⟨25529198, by rfl⟩ : syracuseStep 136155725 = 51058397) B51058397
theorem B1553023 : Blo 1226431 1553023 := bstep (se 1 (by rfl) ⟨1164767, by rfl⟩ : syracuseStep 1553023 = 2329535) B2329535
theorem B1841435 : Blo 1226431 1841435 := bstep (se 1 (by rfl) ⟨1381076, by rfl⟩ : syracuseStep 1841435 = 2762153) B2762153
theorem B3989063 : Blo 1226431 3989063 := bstep (se 1 (by rfl) ⟨2991797, by rfl⟩ : syracuseStep 3989063 = 5983595) B5983595
theorem B90770483 : Blo 1226431 90770483 := bstep (se 1 (by rfl) ⟨68077862, by rfl⟩ : syracuseStep 90770483 = 136155725) B136155725
theorem B2659375 : Blo 1226431 2659375 := bstep (se 1 (by rfl) ⟨1994531, by rfl⟩ : syracuseStep 2659375 = 3989063) B3989063
theorem B2070697 : Blo 1226431 2070697 := bstep (se 2 (by rfl) ⟨776511, by rfl⟩ : syracuseStep 2070697 = 1553023) B1553023
theorem B1227623 : Blo 1226431 1227623 := bstep (se 1 (by rfl) ⟨920717, by rfl⟩ : syracuseStep 1227623 = 1841435) B1841435
theorem B2760929 : Blo 1226431 2760929 := bstep (se 2 (by rfl) ⟨1035348, by rfl⟩ : syracuseStep 2760929 = 2070697) B2070697
theorem B14183333 : Blo 1226431 14183333 := bstep (se 4 (by rfl) ⟨1329687, by rfl⟩ : syracuseStep 14183333 = 2659375) B2659375
theorem B60513655 : Blo 1226431 60513655 := bstep (se 1 (by rfl) ⟨45385241, by rfl⟩ : syracuseStep 60513655 = 90770483) B90770483
theorem B80684873 : Blo 1226431 80684873 := bstep (se 2 (by rfl) ⟨30256827, by rfl⟩ : syracuseStep 80684873 = 60513655) B60513655
theorem B9455555 : Blo 1226431 9455555 := bstep (se 1 (by rfl) ⟨7091666, by rfl⟩ : syracuseStep 9455555 = 14183333) B14183333
theorem B1840619 : Blo 1226431 1840619 := bstep (se 1 (by rfl) ⟨1380464, by rfl⟩ : syracuseStep 1840619 = 2760929) B2760929
theorem B53789915 : Blo 1226431 53789915 := bstep (se 1 (by rfl) ⟨40342436, by rfl⟩ : syracuseStep 53789915 = 80684873) B80684873
theorem B6303703 : Blo 1226431 6303703 := bstep (se 1 (by rfl) ⟨4727777, by rfl⟩ : syracuseStep 6303703 = 9455555) B9455555
theorem B1227079 : Blo 1226431 1227079 := bstep (se 1 (by rfl) ⟨920309, by rfl⟩ : syracuseStep 1227079 = 1840619) B1840619
theorem B35859943 : Blo 1226431 35859943 := bstep (se 1 (by rfl) ⟨26894957, by rfl⟩ : syracuseStep 35859943 = 53789915) B53789915
theorem B8404937 : Blo 1226431 8404937 := bstep (se 2 (by rfl) ⟨3151851, by rfl⟩ : syracuseStep 8404937 = 6303703) B6303703
theorem B47813257 : Blo 1226431 47813257 := bstep (se 2 (by rfl) ⟨17929971, by rfl⟩ : syracuseStep 47813257 = 35859943) B35859943
theorem B5603291 : Blo 1226431 5603291 := bstep (se 1 (by rfl) ⟨4202468, by rfl⟩ : syracuseStep 5603291 = 8404937) B8404937
theorem B63751009 : Blo 1226431 63751009 := bstep (se 2 (by rfl) ⟨23906628, by rfl⟩ : syracuseStep 63751009 = 47813257) B47813257
theorem B3735527 : Blo 1226431 3735527 := bstep (se 1 (by rfl) ⟨2801645, by rfl⟩ : syracuseStep 3735527 = 5603291) B5603291
theorem B85001345 : Blo 1226431 85001345 := bstep (se 2 (by rfl) ⟨31875504, by rfl⟩ : syracuseStep 85001345 = 63751009) B63751009
theorem B39845621 : Blo 1226431 39845621 := bstep (se 5 (by rfl) ⟨1867763, by rfl⟩ : syracuseStep 39845621 = 3735527) B3735527
theorem B56667563 : Blo 1226431 56667563 := bstep (se 1 (by rfl) ⟨42500672, by rfl⟩ : syracuseStep 56667563 = 85001345) B85001345
theorem B26563747 : Blo 1226431 26563747 := bstep (se 1 (by rfl) ⟨19922810, by rfl⟩ : syracuseStep 26563747 = 39845621) B39845621
theorem B35418329 : Blo 1226431 35418329 := bstep (se 2 (by rfl) ⟨13281873, by rfl⟩ : syracuseStep 35418329 = 26563747) B26563747
theorem B37778375 : Blo 1226431 37778375 := bstep (se 1 (by rfl) ⟨28333781, by rfl⟩ : syracuseStep 37778375 = 56667563) B56667563
theorem B23612219 : Blo 1226431 23612219 := bstep (se 1 (by rfl) ⟨17709164, by rfl⟩ : syracuseStep 23612219 = 35418329) B35418329
theorem B25185583 : Blo 1226431 25185583 := bstep (se 1 (by rfl) ⟨18889187, by rfl⟩ : syracuseStep 25185583 = 37778375) B37778375
theorem B33580777 : Blo 1226431 33580777 := bstep (se 2 (by rfl) ⟨12592791, by rfl⟩ : syracuseStep 33580777 = 25185583) B25185583
theorem B15741479 : Blo 1226431 15741479 := bstep (se 1 (by rfl) ⟨11806109, by rfl⟩ : syracuseStep 15741479 = 23612219) B23612219
theorem B10494319 : Blo 1226431 10494319 := bstep (se 1 (by rfl) ⟨7870739, by rfl⟩ : syracuseStep 10494319 = 15741479) B15741479
theorem B44774369 : Blo 1226431 44774369 := bstep (se 2 (by rfl) ⟨16790388, by rfl⟩ : syracuseStep 44774369 = 33580777) B33580777
theorem B13992425 : Blo 1226431 13992425 := bstep (se 2 (by rfl) ⟨5247159, by rfl⟩ : syracuseStep 13992425 = 10494319) B10494319
theorem B29849579 : Blo 1226431 29849579 := bstep (se 1 (by rfl) ⟨22387184, by rfl⟩ : syracuseStep 29849579 = 44774369) B44774369
theorem B19899719 : Blo 1226431 19899719 := bstep (se 1 (by rfl) ⟨14924789, by rfl⟩ : syracuseStep 19899719 = 29849579) B29849579
theorem B9328283 : Blo 1226431 9328283 := bstep (se 1 (by rfl) ⟨6996212, by rfl⟩ : syracuseStep 9328283 = 13992425) B13992425
theorem B6218855 : Blo 1226431 6218855 := bstep (se 1 (by rfl) ⟨4664141, by rfl⟩ : syracuseStep 6218855 = 9328283) B9328283
theorem B13266479 : Blo 1226431 13266479 := bstep (se 1 (by rfl) ⟨9949859, by rfl⟩ : syracuseStep 13266479 = 19899719) B19899719
theorem B4145903 : Blo 1226431 4145903 := bstep (se 1 (by rfl) ⟨3109427, by rfl⟩ : syracuseStep 4145903 = 6218855) B6218855
theorem B8844319 : Blo 1226431 8844319 := bstep (se 1 (by rfl) ⟨6633239, by rfl⟩ : syracuseStep 8844319 = 13266479) B13266479
theorem B2763935 : Blo 1226431 2763935 := bstep (se 1 (by rfl) ⟨2072951, by rfl⟩ : syracuseStep 2763935 = 4145903) B4145903
theorem B11792425 : Blo 1226431 11792425 := bstep (se 2 (by rfl) ⟨4422159, by rfl⟩ : syracuseStep 11792425 = 8844319) B8844319
theorem B15723233 : Blo 1226431 15723233 := bstep (se 2 (by rfl) ⟨5896212, by rfl⟩ : syracuseStep 15723233 = 11792425) B11792425
theorem B1842623 : Blo 1226431 1842623 := bstep (se 1 (by rfl) ⟨1381967, by rfl⟩ : syracuseStep 1842623 = 2763935) B2763935
theorem B10482155 : Blo 1226431 10482155 := bstep (se 1 (by rfl) ⟨7861616, by rfl⟩ : syracuseStep 10482155 = 15723233) B15723233
theorem B1228415 : Blo 1226431 1228415 := bstep (se 1 (by rfl) ⟨921311, by rfl⟩ : syracuseStep 1228415 = 1842623) B1842623
theorem B6988103 : Blo 1226431 6988103 := bstep (se 1 (by rfl) ⟨5241077, by rfl⟩ : syracuseStep 6988103 = 10482155) B10482155
theorem B4658735 : Blo 1226431 4658735 := bstep (se 1 (by rfl) ⟨3494051, by rfl⟩ : syracuseStep 4658735 = 6988103) B6988103
theorem B3105823 : Blo 1226431 3105823 := bstep (se 1 (by rfl) ⟨2329367, by rfl⟩ : syracuseStep 3105823 = 4658735) B4658735
theorem B4141097 : Blo 1226431 4141097 := bstep (se 2 (by rfl) ⟨1552911, by rfl⟩ : syracuseStep 4141097 = 3105823) B3105823
theorem B2760731 : Blo 1226431 2760731 := bstep (se 1 (by rfl) ⟨2070548, by rfl⟩ : syracuseStep 2760731 = 4141097) B4141097
theorem B1840487 : Blo 1226431 1840487 := bstep (se 1 (by rfl) ⟨1380365, by rfl⟩ : syracuseStep 1840487 = 2760731) B2760731
theorem B1226991 : Blo 1226431 1226991 := bstep (se 1 (by rfl) ⟨920243, by rfl⟩ : syracuseStep 1226991 = 1840487) B1840487

theorem C0 (j : ℕ) (h1 : 306607 ≤ j) (h2 : j ≤ 307107) : Blo 1226431 (4 * j + 3) := by
  interval_cases j
  · exact B1226431
  · exact B1226435
  · exact B1226439
  · exact B1226443
  · exact B1226447
  · exact B1226451
  · exact B1226455
  · exact B1226459
  · exact B1226463
  · exact B1226467
  · exact B1226471
  · exact B1226475
  · exact B1226479
  · exact B1226483
  · exact B1226487
  · exact B1226491
  · exact B1226495
  · exact B1226499
  · exact B1226503
  · exact B1226507
  · exact B1226511
  · exact B1226515
  · exact B1226519
  · exact B1226523
  · exact B1226527
  · exact B1226531
  · exact B1226535
  · exact B1226539
  · exact B1226543
  · exact B1226547
  · exact B1226551
  · exact B1226555
  · exact B1226559
  · exact B1226563
  · exact B1226567
  · exact B1226571
  · exact B1226575
  · exact B1226579
  · exact B1226583
  · exact B1226587
  · exact B1226591
  · exact B1226595
  · exact B1226599
  · exact B1226603
  · exact B1226607
  · exact B1226611
  · exact B1226615
  · exact B1226619
  · exact B1226623
  · exact B1226627
  · exact B1226631
  · exact B1226635
  · exact B1226639
  · exact B1226643
  · exact B1226647
  · exact B1226651
  · exact B1226655
  · exact B1226659
  · exact B1226663
  · exact B1226667
  · exact B1226671
  · exact B1226675
  · exact B1226679
  · exact B1226683
  · exact B1226687
  · exact B1226691
  · exact B1226695
  · exact B1226699
  · exact B1226703
  · exact B1226707
  · exact B1226711
  · exact B1226715
  · exact B1226719
  · exact B1226723
  · exact B1226727
  · exact B1226731
  · exact B1226735
  · exact B1226739
  · exact B1226743
  · exact B1226747
  · exact B1226751
  · exact B1226755
  · exact B1226759
  · exact B1226763
  · exact B1226767
  · exact B1226771
  · exact B1226775
  · exact B1226779
  · exact B1226783
  · exact B1226787
  · exact B1226791
  · exact B1226795
  · exact B1226799
  · exact B1226803
  · exact B1226807
  · exact B1226811
  · exact B1226815
  · exact B1226819
  · exact B1226823
  · exact B1226827
  · exact B1226831
  · exact B1226835
  · exact B1226839
  · exact B1226843
  · exact B1226847
  · exact B1226851
  · exact B1226855
  · exact B1226859
  · exact B1226863
  · exact B1226867
  · exact B1226871
  · exact B1226875
  · exact B1226879
  · exact B1226883
  · exact B1226887
  · exact B1226891
  · exact B1226895
  · exact B1226899
  · exact B1226903
  · exact B1226907
  · exact B1226911
  · exact B1226915
  · exact B1226919
  · exact B1226923
  · exact B1226927
  · exact B1226931
  · exact B1226935
  · exact B1226939
  · exact B1226943
  · exact B1226947
  · exact B1226951
  · exact B1226955
  · exact B1226959
  · exact B1226963
  · exact B1226967
  · exact B1226971
  · exact B1226975
  · exact B1226979
  · exact B1226983
  · exact B1226987
  · exact B1226991
  · exact B1226995
  · exact B1226999
  · exact B1227003
  · exact B1227007
  · exact B1227011
  · exact B1227015
  · exact B1227019
  · exact B1227023
  · exact B1227027
  · exact B1227031
  · exact B1227035
  · exact B1227039
  · exact B1227043
  · exact B1227047
  · exact B1227051
  · exact B1227055
  · exact B1227059
  · exact B1227063
  · exact B1227067
  · exact B1227071
  · exact B1227075
  · exact B1227079
  · exact B1227083
  · exact B1227087
  · exact B1227091
  · exact B1227095
  · exact B1227099
  · exact B1227103
  · exact B1227107
  · exact B1227111
  · exact B1227115
  · exact B1227119
  · exact B1227123
  · exact B1227127
  · exact B1227131
  · exact B1227135
  · exact B1227139
  · exact B1227143
  · exact B1227147
  · exact B1227151
  · exact B1227155
  · exact B1227159
  · exact B1227163
  · exact B1227167
  · exact B1227171
  · exact B1227175
  · exact B1227179
  · exact B1227183
  · exact B1227187
  · exact B1227191
  · exact B1227195
  · exact B1227199
  · exact B1227203
  · exact B1227207
  · exact B1227211
  · exact B1227215
  · exact B1227219
  · exact B1227223
  · exact B1227227
  · exact B1227231
  · exact B1227235
  · exact B1227239
  · exact B1227243
  · exact B1227247
  · exact B1227251
  · exact B1227255
  · exact B1227259
  · exact B1227263
  · exact B1227267
  · exact B1227271
  · exact B1227275
  · exact B1227279
  · exact B1227283
  · exact B1227287
  · exact B1227291
  · exact B1227295
  · exact B1227299
  · exact B1227303
  · exact B1227307
  · exact B1227311
  · exact B1227315
  · exact B1227319
  · exact B1227323
  · exact B1227327
  · exact B1227331
  · exact B1227335
  · exact B1227339
  · exact B1227343
  · exact B1227347
  · exact B1227351
  · exact B1227355
  · exact B1227359
  · exact B1227363
  · exact B1227367
  · exact B1227371
  · exact B1227375
  · exact B1227379
  · exact B1227383
  · exact B1227387
  · exact B1227391
  · exact B1227395
  · exact B1227399
  · exact B1227403
  · exact B1227407
  · exact B1227411
  · exact B1227415
  · exact B1227419
  · exact B1227423
  · exact B1227427
  · exact B1227431
  · exact B1227435
  · exact B1227439
  · exact B1227443
  · exact B1227447
  · exact B1227451
  · exact B1227455
  · exact B1227459
  · exact B1227463
  · exact B1227467
  · exact B1227471
  · exact B1227475
  · exact B1227479
  · exact B1227483
  · exact B1227487
  · exact B1227491
  · exact B1227495
  · exact B1227499
  · exact B1227503
  · exact B1227507
  · exact B1227511
  · exact B1227515
  · exact B1227519
  · exact B1227523
  · exact B1227527
  · exact B1227531
  · exact B1227535
  · exact B1227539
  · exact B1227543
  · exact B1227547
  · exact B1227551
  · exact B1227555
  · exact B1227559
  · exact B1227563
  · exact B1227567
  · exact B1227571
  · exact B1227575
  · exact B1227579
  · exact B1227583
  · exact B1227587
  · exact B1227591
  · exact B1227595
  · exact B1227599
  · exact B1227603
  · exact B1227607
  · exact B1227611
  · exact B1227615
  · exact B1227619
  · exact B1227623
  · exact B1227627
  · exact B1227631
  · exact B1227635
  · exact B1227639
  · exact B1227643
  · exact B1227647
  · exact B1227651
  · exact B1227655
  · exact B1227659
  · exact B1227663
  · exact B1227667
  · exact B1227671
  · exact B1227675
  · exact B1227679
  · exact B1227683
  · exact B1227687
  · exact B1227691
  · exact B1227695
  · exact B1227699
  · exact B1227703
  · exact B1227707
  · exact B1227711
  · exact B1227715
  · exact B1227719
  · exact B1227723
  · exact B1227727
  · exact B1227731
  · exact B1227735
  · exact B1227739
  · exact B1227743
  · exact B1227747
  · exact B1227751
  · exact B1227755
  · exact B1227759
  · exact B1227763
  · exact B1227767
  · exact B1227771
  · exact B1227775
  · exact B1227779
  · exact B1227783
  · exact B1227787
  · exact B1227791
  · exact B1227795
  · exact B1227799
  · exact B1227803
  · exact B1227807
  · exact B1227811
  · exact B1227815
  · exact B1227819
  · exact B1227823
  · exact B1227827
  · exact B1227831
  · exact B1227835
  · exact B1227839
  · exact B1227843
  · exact B1227847
  · exact B1227851
  · exact B1227855
  · exact B1227859
  · exact B1227863
  · exact B1227867
  · exact B1227871
  · exact B1227875
  · exact B1227879
  · exact B1227883
  · exact B1227887
  · exact B1227891
  · exact B1227895
  · exact B1227899
  · exact B1227903
  · exact B1227907
  · exact B1227911
  · exact B1227915
  · exact B1227919
  · exact B1227923
  · exact B1227927
  · exact B1227931
  · exact B1227935
  · exact B1227939
  · exact B1227943
  · exact B1227947
  · exact B1227951
  · exact B1227955
  · exact B1227959
  · exact B1227963
  · exact B1227967
  · exact B1227971
  · exact B1227975
  · exact B1227979
  · exact B1227983
  · exact B1227987
  · exact B1227991
  · exact B1227995
  · exact B1227999
  · exact B1228003
  · exact B1228007
  · exact B1228011
  · exact B1228015
  · exact B1228019
  · exact B1228023
  · exact B1228027
  · exact B1228031
  · exact B1228035
  · exact B1228039
  · exact B1228043
  · exact B1228047
  · exact B1228051
  · exact B1228055
  · exact B1228059
  · exact B1228063
  · exact B1228067
  · exact B1228071
  · exact B1228075
  · exact B1228079
  · exact B1228083
  · exact B1228087
  · exact B1228091
  · exact B1228095
  · exact B1228099
  · exact B1228103
  · exact B1228107
  · exact B1228111
  · exact B1228115
  · exact B1228119
  · exact B1228123
  · exact B1228127
  · exact B1228131
  · exact B1228135
  · exact B1228139
  · exact B1228143
  · exact B1228147
  · exact B1228151
  · exact B1228155
  · exact B1228159
  · exact B1228163
  · exact B1228167
  · exact B1228171
  · exact B1228175
  · exact B1228179
  · exact B1228183
  · exact B1228187
  · exact B1228191
  · exact B1228195
  · exact B1228199
  · exact B1228203
  · exact B1228207
  · exact B1228211
  · exact B1228215
  · exact B1228219
  · exact B1228223
  · exact B1228227
  · exact B1228231
  · exact B1228235
  · exact B1228239
  · exact B1228243
  · exact B1228247
  · exact B1228251
  · exact B1228255
  · exact B1228259
  · exact B1228263
  · exact B1228267
  · exact B1228271
  · exact B1228275
  · exact B1228279
  · exact B1228283
  · exact B1228287
  · exact B1228291
  · exact B1228295
  · exact B1228299
  · exact B1228303
  · exact B1228307
  · exact B1228311
  · exact B1228315
  · exact B1228319
  · exact B1228323
  · exact B1228327
  · exact B1228331
  · exact B1228335
  · exact B1228339
  · exact B1228343
  · exact B1228347
  · exact B1228351
  · exact B1228355
  · exact B1228359
  · exact B1228363
  · exact B1228367
  · exact B1228371
  · exact B1228375
  · exact B1228379
  · exact B1228383
  · exact B1228387
  · exact B1228391
  · exact B1228395
  · exact B1228399
  · exact B1228403
  · exact B1228407
  · exact B1228411
  · exact B1228415
  · exact B1228419
  · exact B1228423
  · exact B1228427
  · exact B1228431

theorem solution (m : ℕ) (hlo : 1226431 ≤ m) (hhi : m ≤ 1228431) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 306607 ≤ j := by omega
    have hj2 : j ≤ 307107 := by omega
    have hb : Blo 1226431 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
