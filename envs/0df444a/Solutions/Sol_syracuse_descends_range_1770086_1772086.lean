-- Prove2me | solution 1 for syracuse_descends_range_1770086_1772086
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:41:40.370296+00:00
-- url     : https://prove2.me/submissions/ebdc3bf6-32f6-4d55-bb46-50e3d2df7e63

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


theorem B7569413 : Blo 1770086 7569413 := bbase (se 4 (by rfl) ⟨709632, by rfl⟩ : syracuseStep 7569413 = 1419265) (by norm_num)
theorem B2990101 : Blo 1770086 2990101 := bbase (se 6 (by rfl) ⟨70080, by rfl⟩ : syracuseStep 2990101 = 140161) (by norm_num)
theorem B5980229 : Blo 1770086 5980229 := bbase (se 4 (by rfl) ⟨560646, by rfl⟩ : syracuseStep 5980229 = 1121293) (by norm_num)
theorem B2990189 : Blo 1770086 2990189 := bbase (se 3 (by rfl) ⟨560660, by rfl⟩ : syracuseStep 2990189 = 1121321) (by norm_num)
theorem B7561349 : Blo 1770086 7561349 := bbase (se 4 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 7561349 = 1417753) (by norm_num)
theorem B6725861 : Blo 1770086 6725861 := bbase (se 4 (by rfl) ⟨630549, by rfl⟩ : syracuseStep 6725861 = 1261099) (by norm_num)
theorem B2990317 : Blo 1770086 2990317 := bbase (se 3 (by rfl) ⟨560684, by rfl⟩ : syracuseStep 2990317 = 1121369) (by norm_num)
theorem B7184645 : Blo 1770086 7184645 := bbase (se 4 (by rfl) ⟨673560, by rfl⟩ : syracuseStep 7184645 = 1347121) (by norm_num)
theorem B8962325 : Blo 1770086 8962325 := bbase (se 6 (by rfl) ⟨210054, by rfl⟩ : syracuseStep 8962325 = 420109) (by norm_num)
theorem B4481365 : Blo 1770086 4481365 := bbase (se 10 (by rfl) ⟨6564, by rfl⟩ : syracuseStep 4481365 = 13129) (by norm_num)
theorem B6472021 : Blo 1770086 6472021 := bbase (se 10 (by rfl) ⟨9480, by rfl⟩ : syracuseStep 6472021 = 18961) (by norm_num)
theorem B1794421 : Blo 1770086 1794421 := bbase (se 5 (by rfl) ⟨84113, by rfl⟩ : syracuseStep 1794421 = 168227) (by norm_num)
theorem B4481477 : Blo 1770086 4481477 := bbase (se 4 (by rfl) ⟨420138, by rfl⟩ : syracuseStep 4481477 = 840277) (by norm_num)
theorem B5980661 : Blo 1770086 5980661 := bbase (se 5 (by rfl) ⟨280343, by rfl⟩ : syracuseStep 5980661 = 560687) (by norm_num)
theorem B6726149 : Blo 1770086 6726149 := bbase (se 4 (by rfl) ⟨630576, by rfl⟩ : syracuseStep 6726149 = 1261153) (by norm_num)
theorem B3408421 : Blo 1770086 3408421 := bbase (se 4 (by rfl) ⟨319539, by rfl⟩ : syracuseStep 3408421 = 639079) (by norm_num)
theorem B4481669 : Blo 1770086 4481669 := bbase (se 4 (by rfl) ⟨420156, by rfl⟩ : syracuseStep 4481669 = 840313) (by norm_num)
theorem B9085589 : Blo 1770086 9085589 := bbase (se 6 (by rfl) ⟨212943, by rfl⟩ : syracuseStep 9085589 = 425887) (by norm_num)
theorem B1991353 : Blo 1770086 1991353 := bbase (se 2 (by rfl) ⟨746757, by rfl⟩ : syracuseStep 1991353 = 1493515) (by norm_num)
theorem B1991389 : Blo 1770086 1991389 := bbase (se 3 (by rfl) ⟨373385, by rfl⟩ : syracuseStep 1991389 = 746771) (by norm_num)
theorem B1991425 : Blo 1770086 1991425 := bbase (se 2 (by rfl) ⟨746784, by rfl⟩ : syracuseStep 1991425 = 1493569) (by norm_num)
theorem B1991461 : Blo 1770086 1991461 := bbase (se 4 (by rfl) ⟨186699, by rfl⟩ : syracuseStep 1991461 = 373399) (by norm_num)
theorem B1991497 : Blo 1770086 1991497 := bbase (se 2 (by rfl) ⟨746811, by rfl⟩ : syracuseStep 1991497 = 1493623) (by norm_num)
theorem B1991533 : Blo 1770086 1991533 := bbase (se 3 (by rfl) ⟨373412, by rfl⟩ : syracuseStep 1991533 = 746825) (by norm_num)
theorem B12944245 : Blo 1770086 12944245 := bbase (se 5 (by rfl) ⟨606761, by rfl⟩ : syracuseStep 12944245 = 1213523) (by norm_num)
theorem B1991569 : Blo 1770086 1991569 := bbase (se 2 (by rfl) ⟨746838, by rfl⟩ : syracuseStep 1991569 = 1493677) (by norm_num)
theorem B2655149 : Blo 1770086 2655149 := bbase (se 3 (by rfl) ⟨497840, by rfl⟩ : syracuseStep 2655149 = 995681) (by norm_num)
theorem B1991605 : Blo 1770086 1991605 := bbase (se 5 (by rfl) ⟨93356, by rfl⟩ : syracuseStep 1991605 = 186713) (by norm_num)
theorem B2655173 : Blo 1770086 2655173 := bbase (se 4 (by rfl) ⟨248922, by rfl⟩ : syracuseStep 2655173 = 497845) (by norm_num)
theorem B1991641 : Blo 1770086 1991641 := bbase (se 2 (by rfl) ⟨746865, by rfl⟩ : syracuseStep 1991641 = 1493731) (by norm_num)
theorem B2655197 : Blo 1770086 2655197 := bbase (se 3 (by rfl) ⟨497849, by rfl⟩ : syracuseStep 2655197 = 995699) (by norm_num)
theorem B4482013 : Blo 1770086 4482013 := bbase (se 3 (by rfl) ⟨840377, by rfl⟩ : syracuseStep 4482013 = 1680755) (by norm_num)
theorem B2655221 : Blo 1770086 2655221 := bbase (se 5 (by rfl) ⟨124463, by rfl⟩ : syracuseStep 2655221 = 248927) (by norm_num)
theorem B1991677 : Blo 1770086 1991677 := bbase (se 3 (by rfl) ⟨373439, by rfl⟩ : syracuseStep 1991677 = 746879) (by norm_num)
theorem B2655245 : Blo 1770086 2655245 := bbase (se 3 (by rfl) ⟨497858, by rfl⟩ : syracuseStep 2655245 = 995717) (by norm_num)
theorem B1991713 : Blo 1770086 1991713 := bbase (se 2 (by rfl) ⟨746892, by rfl⟩ : syracuseStep 1991713 = 1493785) (by norm_num)
theorem B2655269 : Blo 1770086 2655269 := bbase (se 4 (by rfl) ⟨248931, by rfl⟩ : syracuseStep 2655269 = 497863) (by norm_num)
theorem B10773557 : Blo 1770086 10773557 := bbase (se 5 (by rfl) ⟨505010, by rfl⟩ : syracuseStep 10773557 = 1010021) (by norm_num)
theorem B2655293 : Blo 1770086 2655293 := bbase (se 3 (by rfl) ⟨497867, by rfl⟩ : syracuseStep 2655293 = 995735) (by norm_num)
theorem B1991749 : Blo 1770086 1991749 := bbase (se 4 (by rfl) ⟨186726, by rfl⟩ : syracuseStep 1991749 = 373453) (by norm_num)
theorem B4482125 : Blo 1770086 4482125 := bbase (se 3 (by rfl) ⟨840398, by rfl⟩ : syracuseStep 4482125 = 1680797) (by norm_num)
theorem B2655317 : Blo 1770086 2655317 := bbase (se 8 (by rfl) ⟨15558, by rfl⟩ : syracuseStep 2655317 = 31117) (by norm_num)
theorem B1991785 : Blo 1770086 1991785 := bbase (se 2 (by rfl) ⟨746919, by rfl⟩ : syracuseStep 1991785 = 1493839) (by norm_num)
theorem B2655341 : Blo 1770086 2655341 := bbase (se 3 (by rfl) ⟨497876, by rfl⟩ : syracuseStep 2655341 = 995753) (by norm_num)
theorem B2655365 : Blo 1770086 2655365 := bbase (se 4 (by rfl) ⟨248940, by rfl⟩ : syracuseStep 2655365 = 497881) (by norm_num)
theorem B1991821 : Blo 1770086 1991821 := bbase (se 3 (by rfl) ⟨373466, by rfl⟩ : syracuseStep 1991821 = 746933) (by norm_num)
theorem B2655389 : Blo 1770086 2655389 := bbase (se 3 (by rfl) ⟨497885, by rfl⟩ : syracuseStep 2655389 = 995771) (by norm_num)
theorem B1991857 : Blo 1770086 1991857 := bbase (se 2 (by rfl) ⟨746946, by rfl⟩ : syracuseStep 1991857 = 1493893) (by norm_num)
theorem B2655413 : Blo 1770086 2655413 := bbase (se 5 (by rfl) ⟨124472, by rfl⟩ : syracuseStep 2655413 = 248945) (by norm_num)
theorem B2655437 : Blo 1770086 2655437 := bbase (se 3 (by rfl) ⟨497894, by rfl⟩ : syracuseStep 2655437 = 995789) (by norm_num)
theorem B4039885 : Blo 1770086 4039885 := bbase (se 3 (by rfl) ⟨757478, by rfl⟩ : syracuseStep 4039885 = 1514957) (by norm_num)
theorem B1991893 : Blo 1770086 1991893 := bbase (se 7 (by rfl) ⟨23342, by rfl⟩ : syracuseStep 1991893 = 46685) (by norm_num)
theorem B2835685 : Blo 1770086 2835685 := bbase (se 4 (by rfl) ⟨265845, by rfl⟩ : syracuseStep 2835685 = 531691) (by norm_num)
theorem B2655461 : Blo 1770086 2655461 := bbase (se 4 (by rfl) ⟨248949, by rfl⟩ : syracuseStep 2655461 = 497899) (by norm_num)
theorem B1991929 : Blo 1770086 1991929 := bbase (se 2 (by rfl) ⟨746973, by rfl⟩ : syracuseStep 1991929 = 1493947) (by norm_num)
theorem B2655485 : Blo 1770086 2655485 := bbase (se 3 (by rfl) ⟨497903, by rfl⟩ : syracuseStep 2655485 = 995807) (by norm_num)
theorem B1795333 : Blo 1770086 1795333 := bbase (se 4 (by rfl) ⟨168312, by rfl⟩ : syracuseStep 1795333 = 336625) (by norm_num)
theorem B4482317 : Blo 1770086 4482317 := bbase (se 3 (by rfl) ⟨840434, by rfl⟩ : syracuseStep 4482317 = 1680869) (by norm_num)
theorem B2655509 : Blo 1770086 2655509 := bbase (se 6 (by rfl) ⟨62238, by rfl⟩ : syracuseStep 2655509 = 124477) (by norm_num)
theorem B1991965 : Blo 1770086 1991965 := bbase (se 3 (by rfl) ⟨373493, by rfl⟩ : syracuseStep 1991965 = 746987) (by norm_num)
theorem B2655533 : Blo 1770086 2655533 := bbase (se 3 (by rfl) ⟨497912, by rfl⟩ : syracuseStep 2655533 = 995825) (by norm_num)
theorem B2155829 : Blo 1770086 2155829 := bbase (se 5 (by rfl) ⟨101054, by rfl⟩ : syracuseStep 2155829 = 202109) (by norm_num)
theorem B1992001 : Blo 1770086 1992001 := bbase (se 2 (by rfl) ⟨747000, by rfl⟩ : syracuseStep 1992001 = 1494001) (by norm_num)
theorem B2655557 : Blo 1770086 2655557 := bbase (se 4 (by rfl) ⟨248958, by rfl⟩ : syracuseStep 2655557 = 497917) (by norm_num)
theorem B2655581 : Blo 1770086 2655581 := bbase (se 3 (by rfl) ⟨497921, by rfl⟩ : syracuseStep 2655581 = 995843) (by norm_num)
theorem B1992037 : Blo 1770086 1992037 := bbase (se 4 (by rfl) ⟨186753, by rfl⟩ : syracuseStep 1992037 = 373507) (by norm_num)
theorem B2655605 : Blo 1770086 2655605 := bbase (se 5 (by rfl) ⟨124481, by rfl⟩ : syracuseStep 2655605 = 248963) (by norm_num)
theorem B1992073 : Blo 1770086 1992073 := bbase (se 2 (by rfl) ⟨747027, by rfl⟩ : syracuseStep 1992073 = 1494055) (by norm_num)
theorem B3982733 : Blo 1770086 3982733 := bbase (se 3 (by rfl) ⟨746762, by rfl⟩ : syracuseStep 3982733 = 1493525) (by norm_num)
theorem B2655629 : Blo 1770086 2655629 := bbase (se 3 (by rfl) ⟨497930, by rfl⟩ : syracuseStep 2655629 = 995861) (by norm_num)
theorem B2655653 : Blo 1770086 2655653 := bbase (se 4 (by rfl) ⟨248967, by rfl⟩ : syracuseStep 2655653 = 497935) (by norm_num)
theorem B1992109 : Blo 1770086 1992109 := bbase (se 3 (by rfl) ⟨373520, by rfl⟩ : syracuseStep 1992109 = 747041) (by norm_num)
theorem B2655677 : Blo 1770086 2655677 := bbase (se 3 (by rfl) ⟨497939, by rfl⟩ : syracuseStep 2655677 = 995879) (by norm_num)
theorem B2590141 : Blo 1770086 2590141 := bbase (se 3 (by rfl) ⟨485651, by rfl⟩ : syracuseStep 2590141 = 971303) (by norm_num)
theorem B1992145 : Blo 1770086 1992145 := bbase (se 2 (by rfl) ⟨747054, by rfl⟩ : syracuseStep 1992145 = 1494109) (by norm_num)
theorem B3982805 : Blo 1770086 3982805 := bbase (se 7 (by rfl) ⟨46673, by rfl⟩ : syracuseStep 3982805 = 93347) (by norm_num)
theorem B2655701 : Blo 1770086 2655701 := bbase (se 7 (by rfl) ⟨31121, by rfl⟩ : syracuseStep 2655701 = 62243) (by norm_num)
theorem B2655725 : Blo 1770086 2655725 := bbase (se 3 (by rfl) ⟨497948, by rfl⟩ : syracuseStep 2655725 = 995897) (by norm_num)
theorem B1992181 : Blo 1770086 1992181 := bbase (se 5 (by rfl) ⟨93383, by rfl⟩ : syracuseStep 1992181 = 186767) (by norm_num)
theorem B2655749 : Blo 1770086 2655749 := bbase (se 4 (by rfl) ⟨248976, by rfl⟩ : syracuseStep 2655749 = 497953) (by norm_num)
theorem B1992217 : Blo 1770086 1992217 := bbase (se 2 (by rfl) ⟨747081, by rfl⟩ : syracuseStep 1992217 = 1494163) (by norm_num)
theorem B3982877 : Blo 1770086 3982877 := bbase (se 3 (by rfl) ⟨746789, by rfl⟩ : syracuseStep 3982877 = 1493579) (by norm_num)
theorem B2655773 : Blo 1770086 2655773 := bbase (se 3 (by rfl) ⟨497957, by rfl⟩ : syracuseStep 2655773 = 995915) (by norm_num)
theorem B8963621 : Blo 1770086 8963621 := bbase (se 4 (by rfl) ⟨840339, by rfl⟩ : syracuseStep 8963621 = 1680679) (by norm_num)
theorem B2655797 : Blo 1770086 2655797 := bbase (se 5 (by rfl) ⟨124490, by rfl⟩ : syracuseStep 2655797 = 248981) (by norm_num)
theorem B1992253 : Blo 1770086 1992253 := bbase (se 3 (by rfl) ⟨373547, by rfl⟩ : syracuseStep 1992253 = 747095) (by norm_num)
theorem B2655821 : Blo 1770086 2655821 := bbase (se 3 (by rfl) ⟨497966, by rfl⟩ : syracuseStep 2655821 = 995933) (by norm_num)
theorem B23004757 : Blo 1770086 23004757 := bbase (se 8 (by rfl) ⟨134793, by rfl⟩ : syracuseStep 23004757 = 269587) (by norm_num)
theorem B1992289 : Blo 1770086 1992289 := bbase (se 2 (by rfl) ⟨747108, by rfl⟩ : syracuseStep 1992289 = 1494217) (by norm_num)
theorem B3982949 : Blo 1770086 3982949 := bbase (se 4 (by rfl) ⟨373401, by rfl⟩ : syracuseStep 3982949 = 746803) (by norm_num)
theorem B2655845 : Blo 1770086 2655845 := bbase (se 4 (by rfl) ⟨248985, by rfl⟩ : syracuseStep 2655845 = 497971) (by norm_num)
theorem B4482661 : Blo 1770086 4482661 := bbase (se 4 (by rfl) ⟨420249, by rfl⟩ : syracuseStep 4482661 = 840499) (by norm_num)
theorem B2655869 : Blo 1770086 2655869 := bbase (se 3 (by rfl) ⟨497975, by rfl⟩ : syracuseStep 2655869 = 995951) (by norm_num)
theorem B1992325 : Blo 1770086 1992325 := bbase (se 4 (by rfl) ⟨186780, by rfl⟩ : syracuseStep 1992325 = 373561) (by norm_num)
theorem B2836109 : Blo 1770086 2836109 := bbase (se 3 (by rfl) ⟨531770, by rfl⟩ : syracuseStep 2836109 = 1063541) (by norm_num)
theorem B2655893 : Blo 1770086 2655893 := bbase (se 6 (by rfl) ⟨62247, by rfl⟩ : syracuseStep 2655893 = 124495) (by norm_num)
theorem B28731029 : Blo 1770086 28731029 := bbase (se 6 (by rfl) ⟨673383, by rfl⟩ : syracuseStep 28731029 = 1346767) (by norm_num)
theorem B6727333 : Blo 1770086 6727333 := bbase (se 4 (by rfl) ⟨630687, by rfl⟩ : syracuseStep 6727333 = 1261375) (by norm_num)
theorem B1992361 : Blo 1770086 1992361 := bbase (se 2 (by rfl) ⟨747135, by rfl⟩ : syracuseStep 1992361 = 1494271) (by norm_num)
theorem B3983021 : Blo 1770086 3983021 := bbase (se 3 (by rfl) ⟨746816, by rfl⟩ : syracuseStep 3983021 = 1493633) (by norm_num)
theorem B2655917 : Blo 1770086 2655917 := bbase (se 3 (by rfl) ⟨497984, by rfl⟩ : syracuseStep 2655917 = 995969) (by norm_num)
theorem B2655941 : Blo 1770086 2655941 := bbase (se 4 (by rfl) ⟨248994, by rfl⟩ : syracuseStep 2655941 = 497989) (by norm_num)
theorem B1992397 : Blo 1770086 1992397 := bbase (se 3 (by rfl) ⟨373574, by rfl⟩ : syracuseStep 1992397 = 747149) (by norm_num)
theorem B9570005 : Blo 1770086 9570005 := bbase (se 7 (by rfl) ⟨112148, by rfl⟩ : syracuseStep 9570005 = 224297) (by norm_num)
theorem B4482773 : Blo 1770086 4482773 := bbase (se 7 (by rfl) ⟨52532, by rfl⟩ : syracuseStep 4482773 = 105065) (by norm_num)
theorem B2655965 : Blo 1770086 2655965 := bbase (se 3 (by rfl) ⟨497993, by rfl⟩ : syracuseStep 2655965 = 995987) (by norm_num)
theorem B1992433 : Blo 1770086 1992433 := bbase (se 2 (by rfl) ⟨747162, by rfl⟩ : syracuseStep 1992433 = 1494325) (by norm_num)
theorem B3983093 : Blo 1770086 3983093 := bbase (se 5 (by rfl) ⟨186707, by rfl⟩ : syracuseStep 3983093 = 373415) (by norm_num)
theorem B2655989 : Blo 1770086 2655989 := bbase (se 5 (by rfl) ⟨124499, by rfl⟩ : syracuseStep 2655989 = 248999) (by norm_num)
theorem B2656013 : Blo 1770086 2656013 := bbase (se 3 (by rfl) ⟨498002, by rfl⟩ : syracuseStep 2656013 = 996005) (by norm_num)
theorem B9086741 : Blo 1770086 9086741 := bbase (se 6 (by rfl) ⟨212970, by rfl⟩ : syracuseStep 9086741 = 425941) (by norm_num)
theorem B1992469 : Blo 1770086 1992469 := bbase (se 6 (by rfl) ⟨46698, by rfl⟩ : syracuseStep 1992469 = 93397) (by norm_num)
theorem B2656037 : Blo 1770086 2656037 := bbase (se 4 (by rfl) ⟨249003, by rfl⟩ : syracuseStep 2656037 = 498007) (by norm_num)
theorem B2271025 : Blo 1770086 2271025 := bbase (se 2 (by rfl) ⟨851634, by rfl⟩ : syracuseStep 2271025 = 1703269) (by norm_num)
theorem B6055733 : Blo 1770086 6055733 := bbase (se 5 (by rfl) ⟨283862, by rfl⟩ : syracuseStep 6055733 = 567725) (by norm_num)
theorem B1992505 : Blo 1770086 1992505 := bbase (se 2 (by rfl) ⟨747189, by rfl⟩ : syracuseStep 1992505 = 1494379) (by norm_num)
theorem B3983165 : Blo 1770086 3983165 := bbase (se 3 (by rfl) ⟨746843, by rfl⟩ : syracuseStep 3983165 = 1493687) (by norm_num)
theorem B2656061 : Blo 1770086 2656061 := bbase (se 3 (by rfl) ⟨498011, by rfl⟩ : syracuseStep 2656061 = 996023) (by norm_num)
theorem B2656085 : Blo 1770086 2656085 := bbase (se 9 (by rfl) ⟨7781, by rfl⟩ : syracuseStep 2656085 = 15563) (by norm_num)
theorem B1992541 : Blo 1770086 1992541 := bbase (se 3 (by rfl) ⟨373601, by rfl⟩ : syracuseStep 1992541 = 747203) (by norm_num)
theorem B2656109 : Blo 1770086 2656109 := bbase (se 3 (by rfl) ⟨498020, by rfl⟩ : syracuseStep 2656109 = 996041) (by norm_num)
theorem B3360629 : Blo 1770086 3360629 := bbase (se 5 (by rfl) ⟨157529, by rfl⟩ : syracuseStep 3360629 = 315059) (by norm_num)
theorem B7563125 : Blo 1770086 7563125 := bbase (se 5 (by rfl) ⟨354521, by rfl⟩ : syracuseStep 7563125 = 709043) (by norm_num)
theorem B1992577 : Blo 1770086 1992577 := bbase (se 2 (by rfl) ⟨747216, by rfl⟩ : syracuseStep 1992577 = 1494433) (by norm_num)
theorem B3983237 : Blo 1770086 3983237 := bbase (se 4 (by rfl) ⟨373428, by rfl⟩ : syracuseStep 3983237 = 746857) (by norm_num)
theorem B2656133 : Blo 1770086 2656133 := bbase (se 4 (by rfl) ⟨249012, by rfl⟩ : syracuseStep 2656133 = 498025) (by norm_num)
theorem B4482965 : Blo 1770086 4482965 := bbase (se 6 (by rfl) ⟨105069, by rfl⟩ : syracuseStep 4482965 = 210139) (by norm_num)
theorem B4253597 : Blo 1770086 4253597 := bbase (se 3 (by rfl) ⟨797549, by rfl⟩ : syracuseStep 4253597 = 1595099) (by norm_num)
theorem B2656157 : Blo 1770086 2656157 := bbase (se 3 (by rfl) ⟨498029, by rfl⟩ : syracuseStep 2656157 = 996059) (by norm_num)
theorem B1992613 : Blo 1770086 1992613 := bbase (se 4 (by rfl) ⟨186807, by rfl⟩ : syracuseStep 1992613 = 373615) (by norm_num)
theorem B2836397 : Blo 1770086 2836397 := bbase (se 3 (by rfl) ⟨531824, by rfl⟩ : syracuseStep 2836397 = 1063649) (by norm_num)
theorem B2656181 : Blo 1770086 2656181 := bbase (se 5 (by rfl) ⟨124508, by rfl⟩ : syracuseStep 2656181 = 249017) (by norm_num)
theorem B1943477 : Blo 1770086 1943477 := bbase (se 5 (by rfl) ⟨91100, by rfl⟩ : syracuseStep 1943477 = 182201) (by norm_num)
theorem B1992649 : Blo 1770086 1992649 := bbase (se 2 (by rfl) ⟨747243, by rfl⟩ : syracuseStep 1992649 = 1494487) (by norm_num)
theorem B3983309 : Blo 1770086 3983309 := bbase (se 3 (by rfl) ⟨746870, by rfl⟩ : syracuseStep 3983309 = 1493741) (by norm_num)
theorem B2656205 : Blo 1770086 2656205 := bbase (se 3 (by rfl) ⟨498038, by rfl⟩ : syracuseStep 2656205 = 996077) (by norm_num)
theorem B6727637 : Blo 1770086 6727637 := bbase (se 7 (by rfl) ⟨78839, by rfl⟩ : syracuseStep 6727637 = 157679) (by norm_num)
theorem B2656229 : Blo 1770086 2656229 := bbase (se 4 (by rfl) ⟨249021, by rfl⟩ : syracuseStep 2656229 = 498043) (by norm_num)
theorem B1992685 : Blo 1770086 1992685 := bbase (se 3 (by rfl) ⟨373628, by rfl⟩ : syracuseStep 1992685 = 747257) (by norm_num)
theorem B2656253 : Blo 1770086 2656253 := bbase (se 3 (by rfl) ⟨498047, by rfl⟩ : syracuseStep 2656253 = 996095) (by norm_num)
theorem B3360781 : Blo 1770086 3360781 := bbase (se 3 (by rfl) ⟨630146, by rfl⟩ : syracuseStep 3360781 = 1260293) (by norm_num)
theorem B1992721 : Blo 1770086 1992721 := bbase (se 2 (by rfl) ⟨747270, by rfl⟩ : syracuseStep 1992721 = 1494541) (by norm_num)
theorem B3983381 : Blo 1770086 3983381 := bbase (se 6 (by rfl) ⟨93360, by rfl⟩ : syracuseStep 3983381 = 186721) (by norm_num)
theorem B2656277 : Blo 1770086 2656277 := bbase (se 6 (by rfl) ⟨62256, by rfl⟩ : syracuseStep 2656277 = 124513) (by norm_num)
theorem B2656301 : Blo 1770086 2656301 := bbase (se 3 (by rfl) ⟨498056, by rfl⟩ : syracuseStep 2656301 = 996113) (by norm_num)
theorem B1992757 : Blo 1770086 1992757 := bbase (se 5 (by rfl) ⟨93410, by rfl⟩ : syracuseStep 1992757 = 186821) (by norm_num)
theorem B2656325 : Blo 1770086 2656325 := bbase (se 4 (by rfl) ⟨249030, by rfl⟩ : syracuseStep 2656325 = 498061) (by norm_num)
theorem B1992793 : Blo 1770086 1992793 := bbase (se 2 (by rfl) ⟨747297, by rfl⟩ : syracuseStep 1992793 = 1494595) (by norm_num)
theorem B1796185 : Blo 1770086 1796185 := bbase (se 2 (by rfl) ⟨673569, by rfl⟩ : syracuseStep 1796185 = 1347139) (by norm_num)
theorem B3983453 : Blo 1770086 3983453 := bbase (se 3 (by rfl) ⟨746897, by rfl⟩ : syracuseStep 3983453 = 1493795) (by norm_num)
theorem B2656349 : Blo 1770086 2656349 := bbase (se 3 (by rfl) ⟨498065, by rfl⟩ : syracuseStep 2656349 = 996131) (by norm_num)
theorem B7563365 : Blo 1770086 7563365 := bbase (se 4 (by rfl) ⟨709065, by rfl⟩ : syracuseStep 7563365 = 1418131) (by norm_num)
theorem B2656373 : Blo 1770086 2656373 := bbase (se 5 (by rfl) ⟨124517, by rfl⟩ : syracuseStep 2656373 = 249035) (by norm_num)
theorem B1992829 : Blo 1770086 1992829 := bbase (se 3 (by rfl) ⟨373655, by rfl⟩ : syracuseStep 1992829 = 747311) (by norm_num)
theorem B2656397 : Blo 1770086 2656397 := bbase (se 3 (by rfl) ⟨498074, by rfl⟩ : syracuseStep 2656397 = 996149) (by norm_num)
theorem B1992865 : Blo 1770086 1992865 := bbase (se 2 (by rfl) ⟨747324, by rfl⟩ : syracuseStep 1992865 = 1494649) (by norm_num)
theorem B5974181 : Blo 1770086 5974181 := bbase (se 4 (by rfl) ⟨560079, by rfl⟩ : syracuseStep 5974181 = 1120159) (by norm_num)
theorem B3983525 : Blo 1770086 3983525 := bbase (se 4 (by rfl) ⟨373455, by rfl⟩ : syracuseStep 3983525 = 746911) (by norm_num)
theorem B2656421 : Blo 1770086 2656421 := bbase (se 4 (by rfl) ⟨249039, by rfl⟩ : syracuseStep 2656421 = 498079) (by norm_num)
theorem B2656445 : Blo 1770086 2656445 := bbase (se 3 (by rfl) ⟨498083, by rfl⟩ : syracuseStep 2656445 = 996167) (by norm_num)
theorem B1992901 : Blo 1770086 1992901 := bbase (se 4 (by rfl) ⟨186834, by rfl⟩ : syracuseStep 1992901 = 373669) (by norm_num)
theorem B2656469 : Blo 1770086 2656469 := bbase (se 7 (by rfl) ⟨31130, by rfl⟩ : syracuseStep 2656469 = 62261) (by norm_num)
theorem B1992937 : Blo 1770086 1992937 := bbase (se 2 (by rfl) ⟨747351, by rfl⟩ : syracuseStep 1992937 = 1494703) (by norm_num)
theorem B3983597 : Blo 1770086 3983597 := bbase (se 3 (by rfl) ⟨746924, by rfl⟩ : syracuseStep 3983597 = 1493849) (by norm_num)
theorem B2656493 : Blo 1770086 2656493 := bbase (se 3 (by rfl) ⟨498092, by rfl⟩ : syracuseStep 2656493 = 996185) (by norm_num)
theorem B4483309 : Blo 1770086 4483309 := bbase (se 3 (by rfl) ⟨840620, by rfl⟩ : syracuseStep 4483309 = 1681241) (by norm_num)
theorem B2656517 : Blo 1770086 2656517 := bbase (se 4 (by rfl) ⟨249048, by rfl⟩ : syracuseStep 2656517 = 498097) (by norm_num)
theorem B1992973 : Blo 1770086 1992973 := bbase (se 3 (by rfl) ⟨373682, by rfl⟩ : syracuseStep 1992973 = 747365) (by norm_num)
theorem B2656541 : Blo 1770086 2656541 := bbase (se 3 (by rfl) ⟨498101, by rfl⟩ : syracuseStep 2656541 = 996203) (by norm_num)
theorem B1993009 : Blo 1770086 1993009 := bbase (se 2 (by rfl) ⟨747378, by rfl⟩ : syracuseStep 1993009 = 1494757) (by norm_num)
theorem B3983669 : Blo 1770086 3983669 := bbase (se 5 (by rfl) ⟨186734, by rfl⟩ : syracuseStep 3983669 = 373469) (by norm_num)
theorem B2656565 : Blo 1770086 2656565 := bbase (se 5 (by rfl) ⟨124526, by rfl⟩ : syracuseStep 2656565 = 249053) (by norm_num)
theorem B3361085 : Blo 1770086 3361085 := bbase (se 3 (by rfl) ⟨630203, by rfl⟩ : syracuseStep 3361085 = 1260407) (by norm_num)
theorem B2656589 : Blo 1770086 2656589 := bbase (se 3 (by rfl) ⟨498110, by rfl⟩ : syracuseStep 2656589 = 996221) (by norm_num)
theorem B1993045 : Blo 1770086 1993045 := bbase (se 10 (by rfl) ⟨2919, by rfl⟩ : syracuseStep 1993045 = 5839) (by norm_num)
theorem B4483421 : Blo 1770086 4483421 := bbase (se 3 (by rfl) ⟨840641, by rfl⟩ : syracuseStep 4483421 = 1681283) (by norm_num)
theorem B2656613 : Blo 1770086 2656613 := bbase (se 4 (by rfl) ⟨249057, by rfl⟩ : syracuseStep 2656613 = 498115) (by norm_num)
theorem B1993081 : Blo 1770086 1993081 := bbase (se 2 (by rfl) ⟨747405, by rfl⟩ : syracuseStep 1993081 = 1494811) (by norm_num)
theorem B3983741 : Blo 1770086 3983741 := bbase (se 3 (by rfl) ⟨746951, by rfl⟩ : syracuseStep 3983741 = 1493903) (by norm_num)
theorem B2656637 : Blo 1770086 2656637 := bbase (se 3 (by rfl) ⟨498119, by rfl⟩ : syracuseStep 2656637 = 996239) (by norm_num)
theorem B2656661 : Blo 1770086 2656661 := bbase (se 6 (by rfl) ⟨62265, by rfl⟩ : syracuseStep 2656661 = 124531) (by norm_num)
theorem B1993117 : Blo 1770086 1993117 := bbase (se 3 (by rfl) ⟨373709, by rfl⟩ : syracuseStep 1993117 = 747419) (by norm_num)
theorem B2656685 : Blo 1770086 2656685 := bbase (se 3 (by rfl) ⟨498128, by rfl⟩ : syracuseStep 2656685 = 996257) (by norm_num)
theorem B1993153 : Blo 1770086 1993153 := bbase (se 2 (by rfl) ⟨747432, by rfl⟩ : syracuseStep 1993153 = 1494865) (by norm_num)
theorem B3983813 : Blo 1770086 3983813 := bbase (se 4 (by rfl) ⟨373482, by rfl⟩ : syracuseStep 3983813 = 746965) (by norm_num)
theorem B2656709 : Blo 1770086 2656709 := bbase (se 4 (by rfl) ⟨249066, by rfl⟩ : syracuseStep 2656709 = 498133) (by norm_num)
theorem B2656733 : Blo 1770086 2656733 := bbase (se 3 (by rfl) ⟨498137, by rfl⟩ : syracuseStep 2656733 = 996275) (by norm_num)
theorem B5671397 : Blo 1770086 5671397 := bbase (se 4 (by rfl) ⟨531693, by rfl⟩ : syracuseStep 5671397 = 1063387) (by norm_num)
theorem B1993189 : Blo 1770086 1993189 := bbase (se 4 (by rfl) ⟨186861, by rfl⟩ : syracuseStep 1993189 = 373723) (by norm_num)
theorem B2656757 : Blo 1770086 2656757 := bbase (se 5 (by rfl) ⟨124535, by rfl⟩ : syracuseStep 2656757 = 249071) (by norm_num)
theorem B1993225 : Blo 1770086 1993225 := bbase (se 2 (by rfl) ⟨747459, by rfl⟩ : syracuseStep 1993225 = 1494919) (by norm_num)
theorem B3983885 : Blo 1770086 3983885 := bbase (se 3 (by rfl) ⟨746978, by rfl⟩ : syracuseStep 3983885 = 1493957) (by norm_num)
theorem B2656781 : Blo 1770086 2656781 := bbase (se 3 (by rfl) ⟨498146, by rfl⟩ : syracuseStep 2656781 = 996293) (by norm_num)
theorem B4483613 : Blo 1770086 4483613 := bbase (se 3 (by rfl) ⟨840677, by rfl⟩ : syracuseStep 4483613 = 1681355) (by norm_num)
theorem B2656805 : Blo 1770086 2656805 := bbase (se 4 (by rfl) ⟨249075, by rfl⟩ : syracuseStep 2656805 = 498151) (by norm_num)
theorem B1993261 : Blo 1770086 1993261 := bbase (se 3 (by rfl) ⟨373736, by rfl⟩ : syracuseStep 1993261 = 747473) (by norm_num)
theorem B2656829 : Blo 1770086 2656829 := bbase (se 3 (by rfl) ⟨498155, by rfl⟩ : syracuseStep 2656829 = 996311) (by norm_num)
theorem B1993297 : Blo 1770086 1993297 := bbase (se 2 (by rfl) ⟨747486, by rfl⟩ : syracuseStep 1993297 = 1494973) (by norm_num)
theorem B5974613 : Blo 1770086 5974613 := bbase (se 8 (by rfl) ⟨35007, by rfl⟩ : syracuseStep 5974613 = 70015) (by norm_num)
theorem B3983957 : Blo 1770086 3983957 := bbase (se 8 (by rfl) ⟨23343, by rfl⟩ : syracuseStep 3983957 = 46687) (by norm_num)
theorem B2656853 : Blo 1770086 2656853 := bbase (se 8 (by rfl) ⟨15567, by rfl⟩ : syracuseStep 2656853 = 31135) (by norm_num)
theorem B2656877 : Blo 1770086 2656877 := bbase (se 3 (by rfl) ⟨498164, by rfl⟩ : syracuseStep 2656877 = 996329) (by norm_num)
theorem B1993333 : Blo 1770086 1993333 := bbase (se 5 (by rfl) ⟨93437, by rfl⟩ : syracuseStep 1993333 = 186875) (by norm_num)
theorem B2656901 : Blo 1770086 2656901 := bbase (se 4 (by rfl) ⟨249084, by rfl⟩ : syracuseStep 2656901 = 498169) (by norm_num)
theorem B1993369 : Blo 1770086 1993369 := bbase (se 2 (by rfl) ⟨747513, by rfl⟩ : syracuseStep 1993369 = 1495027) (by norm_num)
theorem B4254365 : Blo 1770086 4254365 := bbase (se 3 (by rfl) ⟨797693, by rfl⟩ : syracuseStep 4254365 = 1595387) (by norm_num)
theorem B3984029 : Blo 1770086 3984029 := bbase (se 3 (by rfl) ⟨747005, by rfl⟩ : syracuseStep 3984029 = 1494011) (by norm_num)
theorem B3590813 : Blo 1770086 3590813 := bbase (se 3 (by rfl) ⟨673277, by rfl⟩ : syracuseStep 3590813 = 1346555) (by norm_num)
theorem B2656925 : Blo 1770086 2656925 := bbase (se 3 (by rfl) ⟨498173, by rfl⟩ : syracuseStep 2656925 = 996347) (by norm_num)
theorem B4254373 : Blo 1770086 4254373 := bbase (se 4 (by rfl) ⟨398847, by rfl⟩ : syracuseStep 4254373 = 797695) (by norm_num)
theorem B2656949 : Blo 1770086 2656949 := bbase (se 5 (by rfl) ⟨124544, by rfl⟩ : syracuseStep 2656949 = 249089) (by norm_num)
theorem B4041397 : Blo 1770086 4041397 := bbase (se 5 (by rfl) ⟨189440, by rfl⟩ : syracuseStep 4041397 = 378881) (by norm_num)
theorem B1993405 : Blo 1770086 1993405 := bbase (se 3 (by rfl) ⟨373763, by rfl⟩ : syracuseStep 1993405 = 747527) (by norm_num)
theorem B2837197 : Blo 1770086 2837197 := bbase (se 3 (by rfl) ⟨531974, by rfl⟩ : syracuseStep 2837197 = 1063949) (by norm_num)
theorem B2656973 : Blo 1770086 2656973 := bbase (se 3 (by rfl) ⟨498182, by rfl⟩ : syracuseStep 2656973 = 996365) (by norm_num)
theorem B1993441 : Blo 1770086 1993441 := bbase (se 2 (by rfl) ⟨747540, by rfl⟩ : syracuseStep 1993441 = 1495081) (by norm_num)
theorem B3984101 : Blo 1770086 3984101 := bbase (se 4 (by rfl) ⟨373509, by rfl⟩ : syracuseStep 3984101 = 747019) (by norm_num)
theorem B2656997 : Blo 1770086 2656997 := bbase (se 4 (by rfl) ⟨249093, by rfl⟩ : syracuseStep 2656997 = 498187) (by norm_num)
theorem B2657021 : Blo 1770086 2657021 := bbase (se 3 (by rfl) ⟨498191, by rfl⟩ : syracuseStep 2657021 = 996383) (by norm_num)
theorem B4041469 : Blo 1770086 4041469 := bbase (se 3 (by rfl) ⟨757775, by rfl⟩ : syracuseStep 4041469 = 1515551) (by norm_num)
theorem B1993477 : Blo 1770086 1993477 := bbase (se 4 (by rfl) ⟨186888, by rfl⟩ : syracuseStep 1993477 = 373777) (by norm_num)
theorem B2657045 : Blo 1770086 2657045 := bbase (se 6 (by rfl) ⟨62274, by rfl⟩ : syracuseStep 2657045 = 124549) (by norm_num)
theorem B11504405 : Blo 1770086 11504405 := bbase (se 6 (by rfl) ⟨269634, by rfl⟩ : syracuseStep 11504405 = 539269) (by norm_num)
theorem B1993513 : Blo 1770086 1993513 := bbase (se 2 (by rfl) ⟨747567, by rfl⟩ : syracuseStep 1993513 = 1495135) (by norm_num)
theorem B3984173 : Blo 1770086 3984173 := bbase (se 3 (by rfl) ⟨747032, by rfl⟩ : syracuseStep 3984173 = 1494065) (by norm_num)
theorem B2657069 : Blo 1770086 2657069 := bbase (se 3 (by rfl) ⟨498200, by rfl⟩ : syracuseStep 2657069 = 996401) (by norm_num)
theorem B8964917 : Blo 1770086 8964917 := bbase (se 5 (by rfl) ⟨420230, by rfl⟩ : syracuseStep 8964917 = 840461) (by norm_num)
theorem B15133493 : Blo 1770086 15133493 := bbase (se 5 (by rfl) ⟨709382, by rfl⟩ : syracuseStep 15133493 = 1418765) (by norm_num)
theorem B2657093 : Blo 1770086 2657093 := bbase (se 4 (by rfl) ⟨249102, by rfl⟩ : syracuseStep 2657093 = 498205) (by norm_num)
theorem B1993549 : Blo 1770086 1993549 := bbase (se 3 (by rfl) ⟨373790, by rfl⟩ : syracuseStep 1993549 = 747581) (by norm_num)
theorem B2657117 : Blo 1770086 2657117 := bbase (se 3 (by rfl) ⟨498209, by rfl⟩ : syracuseStep 2657117 = 996419) (by norm_num)
theorem B1993585 : Blo 1770086 1993585 := bbase (se 2 (by rfl) ⟨747594, by rfl⟩ : syracuseStep 1993585 = 1495189) (by norm_num)
theorem B3984245 : Blo 1770086 3984245 := bbase (se 5 (by rfl) ⟨186761, by rfl⟩ : syracuseStep 3984245 = 373523) (by norm_num)
theorem B2657141 : Blo 1770086 2657141 := bbase (se 5 (by rfl) ⟨124553, by rfl⟩ : syracuseStep 2657141 = 249107) (by norm_num)
theorem B4483957 : Blo 1770086 4483957 := bbase (se 5 (by rfl) ⟨210185, by rfl⟩ : syracuseStep 4483957 = 420371) (by norm_num)
theorem B2657165 : Blo 1770086 2657165 := bbase (se 3 (by rfl) ⟨498218, by rfl⟩ : syracuseStep 2657165 = 996437) (by norm_num)
theorem B2657189 : Blo 1770086 2657189 := bbase (se 4 (by rfl) ⟨249111, by rfl⟩ : syracuseStep 2657189 = 498223) (by norm_num)
theorem B14560181 : Blo 1770086 14560181 := bbase (se 5 (by rfl) ⟨682508, by rfl⟩ : syracuseStep 14560181 = 1365017) (by norm_num)
theorem B3984317 : Blo 1770086 3984317 := bbase (se 3 (by rfl) ⟨747059, by rfl⟩ : syracuseStep 3984317 = 1494119) (by norm_num)
theorem B2657213 : Blo 1770086 2657213 := bbase (se 3 (by rfl) ⟨498227, by rfl⟩ : syracuseStep 2657213 = 996455) (by norm_num)
theorem B2657237 : Blo 1770086 2657237 := bbase (se 7 (by rfl) ⟨31139, by rfl⟩ : syracuseStep 2657237 = 62279) (by norm_num)
theorem B4484069 : Blo 1770086 4484069 := bbase (se 4 (by rfl) ⟨420381, by rfl⟩ : syracuseStep 4484069 = 840763) (by norm_num)
theorem B2657261 : Blo 1770086 2657261 := bbase (se 3 (by rfl) ⟨498236, by rfl⟩ : syracuseStep 2657261 = 996473) (by norm_num)
theorem B5975045 : Blo 1770086 5975045 := bbase (se 4 (by rfl) ⟨560160, by rfl⟩ : syracuseStep 5975045 = 1120321) (by norm_num)
theorem B3984389 : Blo 1770086 3984389 := bbase (se 4 (by rfl) ⟨373536, by rfl⟩ : syracuseStep 3984389 = 747073) (by norm_num)
theorem B5385221 : Blo 1770086 5385221 := bbase (se 4 (by rfl) ⟨504864, by rfl⟩ : syracuseStep 5385221 = 1009729) (by norm_num)
theorem B2657285 : Blo 1770086 2657285 := bbase (se 4 (by rfl) ⟨249120, by rfl⟩ : syracuseStep 2657285 = 498241) (by norm_num)
theorem B2657309 : Blo 1770086 2657309 := bbase (se 3 (by rfl) ⟨498245, by rfl⟩ : syracuseStep 2657309 = 996491) (by norm_num)
theorem B3361837 : Blo 1770086 3361837 := bbase (se 3 (by rfl) ⟨630344, by rfl⟩ : syracuseStep 3361837 = 1260689) (by norm_num)
theorem B2657333 : Blo 1770086 2657333 := bbase (se 5 (by rfl) ⟨124562, by rfl⟩ : syracuseStep 2657333 = 249125) (by norm_num)
theorem B8514629 : Blo 1770086 8514629 := bbase (se 4 (by rfl) ⟨798246, by rfl⟩ : syracuseStep 8514629 = 1596493) (by norm_num)
theorem B3984461 : Blo 1770086 3984461 := bbase (se 3 (by rfl) ⟨747086, by rfl⟩ : syracuseStep 3984461 = 1494173) (by norm_num)
theorem B2657357 : Blo 1770086 2657357 := bbase (se 3 (by rfl) ⟨498254, by rfl⟩ : syracuseStep 2657357 = 996509) (by norm_num)
theorem B69028949 : Blo 1770086 69028949 := bbase (se 8 (by rfl) ⟨404466, by rfl⟩ : syracuseStep 69028949 = 808933) (by norm_num)
theorem B2657381 : Blo 1770086 2657381 := bbase (se 4 (by rfl) ⟨249129, by rfl⟩ : syracuseStep 2657381 = 498259) (by norm_num)
theorem B2657405 : Blo 1770086 2657405 := bbase (se 3 (by rfl) ⟨498263, by rfl⟩ : syracuseStep 2657405 = 996527) (by norm_num)
theorem B3984533 : Blo 1770086 3984533 := bbase (se 6 (by rfl) ⟨93387, by rfl⟩ : syracuseStep 3984533 = 186775) (by norm_num)
theorem B2657429 : Blo 1770086 2657429 := bbase (se 6 (by rfl) ⟨62283, by rfl⟩ : syracuseStep 2657429 = 124567) (by norm_num)
theorem B4484261 : Blo 1770086 4484261 := bbase (se 4 (by rfl) ⟨420399, by rfl⟩ : syracuseStep 4484261 = 840799) (by norm_num)
theorem B2657453 : Blo 1770086 2657453 := bbase (se 3 (by rfl) ⟨498272, by rfl⟩ : syracuseStep 2657453 = 996545) (by norm_num)
theorem B3361981 : Blo 1770086 3361981 := bbase (se 3 (by rfl) ⟨630371, by rfl⟩ : syracuseStep 3361981 = 1260743) (by norm_num)
theorem B2657477 : Blo 1770086 2657477 := bbase (se 4 (by rfl) ⟨249138, by rfl⟩ : syracuseStep 2657477 = 498277) (by norm_num)
theorem B3591373 : Blo 1770086 3591373 := bbase (se 3 (by rfl) ⟨673382, by rfl⟩ : syracuseStep 3591373 = 1346765) (by norm_num)
theorem B3984605 : Blo 1770086 3984605 := bbase (se 3 (by rfl) ⟨747113, by rfl⟩ : syracuseStep 3984605 = 1494227) (by norm_num)
theorem B2657501 : Blo 1770086 2657501 := bbase (se 3 (by rfl) ⟨498281, by rfl⟩ : syracuseStep 2657501 = 996563) (by norm_num)
theorem B2018545 : Blo 1770086 2018545 := bbase (se 2 (by rfl) ⟨756954, by rfl⟩ : syracuseStep 2018545 = 1513909) (by norm_num)
theorem B2837749 : Blo 1770086 2837749 := bbase (se 5 (by rfl) ⟨133019, by rfl⟩ : syracuseStep 2837749 = 266039) (by norm_num)
theorem B2657525 : Blo 1770086 2657525 := bbase (se 5 (by rfl) ⟨124571, by rfl⟩ : syracuseStep 2657525 = 249143) (by norm_num)
theorem B2657549 : Blo 1770086 2657549 := bbase (se 3 (by rfl) ⟨498290, by rfl⟩ : syracuseStep 2657549 = 996581) (by norm_num)
theorem B3984677 : Blo 1770086 3984677 := bbase (se 4 (by rfl) ⟨373563, by rfl⟩ : syracuseStep 3984677 = 747127) (by norm_num)
theorem B2657573 : Blo 1770086 2657573 := bbase (se 4 (by rfl) ⟨249147, by rfl⟩ : syracuseStep 2657573 = 498295) (by norm_num)
theorem B2657597 : Blo 1770086 2657597 := bbase (se 3 (by rfl) ⟨498299, by rfl⟩ : syracuseStep 2657597 = 996599) (by norm_num)
theorem B2657621 : Blo 1770086 2657621 := bbase (se 11 (by rfl) ⟨1946, by rfl⟩ : syracuseStep 2657621 = 3893) (by norm_num)
theorem B3362141 : Blo 1770086 3362141 := bbase (se 3 (by rfl) ⟨630401, by rfl⟩ : syracuseStep 3362141 = 1260803) (by norm_num)
theorem B3984749 : Blo 1770086 3984749 := bbase (se 3 (by rfl) ⟨747140, by rfl⟩ : syracuseStep 3984749 = 1494281) (by norm_num)
theorem B2657645 : Blo 1770086 2657645 := bbase (se 3 (by rfl) ⟨498308, by rfl⟩ : syracuseStep 2657645 = 996617) (by norm_num)
theorem B2657669 : Blo 1770086 2657669 := bbase (se 4 (by rfl) ⟨249156, by rfl⟩ : syracuseStep 2657669 = 498313) (by norm_num)
theorem B2657693 : Blo 1770086 2657693 := bbase (se 3 (by rfl) ⟨498317, by rfl⟩ : syracuseStep 2657693 = 996635) (by norm_num)
theorem B5975477 : Blo 1770086 5975477 := bbase (se 5 (by rfl) ⟨280100, by rfl⟩ : syracuseStep 5975477 = 560201) (by norm_num)
theorem B3984821 : Blo 1770086 3984821 := bbase (se 5 (by rfl) ⟨186788, by rfl⟩ : syracuseStep 3984821 = 373577) (by norm_num)
theorem B2657717 : Blo 1770086 2657717 := bbase (se 5 (by rfl) ⟨124580, by rfl⟩ : syracuseStep 2657717 = 249161) (by norm_num)
theorem B4255181 : Blo 1770086 4255181 := bbase (se 3 (by rfl) ⟨797846, by rfl⟩ : syracuseStep 4255181 = 1595693) (by norm_num)
theorem B2657741 : Blo 1770086 2657741 := bbase (se 3 (by rfl) ⟨498326, by rfl⟩ : syracuseStep 2657741 = 996653) (by norm_num)
theorem B2657765 : Blo 1770086 2657765 := bbase (se 4 (by rfl) ⟨249165, by rfl⟩ : syracuseStep 2657765 = 498331) (by norm_num)
theorem B3362285 : Blo 1770086 3362285 := bbase (se 3 (by rfl) ⟨630428, by rfl⟩ : syracuseStep 3362285 = 1260857) (by norm_num)
theorem B3190261 : Blo 1770086 3190261 := bbase (se 5 (by rfl) ⟨149543, by rfl⟩ : syracuseStep 3190261 = 299087) (by norm_num)
theorem B2838005 : Blo 1770086 2838005 := bbase (se 5 (by rfl) ⟨133031, by rfl⟩ : syracuseStep 2838005 = 266063) (by norm_num)
theorem B3984893 : Blo 1770086 3984893 := bbase (se 3 (by rfl) ⟨747167, by rfl⟩ : syracuseStep 3984893 = 1494335) (by norm_num)
theorem B4484605 : Blo 1770086 4484605 := bbase (se 3 (by rfl) ⟨840863, by rfl⟩ : syracuseStep 4484605 = 1681727) (by norm_num)
theorem B2657789 : Blo 1770086 2657789 := bbase (se 3 (by rfl) ⟨498335, by rfl⟩ : syracuseStep 2657789 = 996671) (by norm_num)
theorem B4312597 : Blo 1770086 4312597 := bbase (se 6 (by rfl) ⟨101076, by rfl⟩ : syracuseStep 4312597 = 202153) (by norm_num)
theorem B2657813 : Blo 1770086 2657813 := bbase (se 6 (by rfl) ⟨62292, by rfl⟩ : syracuseStep 2657813 = 124585) (by norm_num)
theorem B2657837 : Blo 1770086 2657837 := bbase (se 3 (by rfl) ⟨498344, by rfl⟩ : syracuseStep 2657837 = 996689) (by norm_num)
theorem B3984965 : Blo 1770086 3984965 := bbase (se 4 (by rfl) ⟨373590, by rfl⟩ : syracuseStep 3984965 = 747181) (by norm_num)
theorem B2657861 : Blo 1770086 2657861 := bbase (se 4 (by rfl) ⟨249174, by rfl⟩ : syracuseStep 2657861 = 498349) (by norm_num)
theorem B2657885 : Blo 1770086 2657885 := bbase (se 3 (by rfl) ⟨498353, by rfl⟩ : syracuseStep 2657885 = 996707) (by norm_num)
theorem B4787813 : Blo 1770086 4787813 := bbase (se 4 (by rfl) ⟨448857, by rfl⟩ : syracuseStep 4787813 = 897715) (by norm_num)
theorem B4484717 : Blo 1770086 4484717 := bbase (se 3 (by rfl) ⟨840884, by rfl⟩ : syracuseStep 4484717 = 1681769) (by norm_num)
theorem B2657909 : Blo 1770086 2657909 := bbase (se 5 (by rfl) ⟨124589, by rfl⟩ : syracuseStep 2657909 = 249179) (by norm_num)
theorem B3985037 : Blo 1770086 3985037 := bbase (se 3 (by rfl) ⟨747194, by rfl⟩ : syracuseStep 3985037 = 1494389) (by norm_num)
theorem B2657933 : Blo 1770086 2657933 := bbase (se 3 (by rfl) ⟨498362, by rfl⟩ : syracuseStep 2657933 = 996725) (by norm_num)
theorem B2657957 : Blo 1770086 2657957 := bbase (se 4 (by rfl) ⟨249183, by rfl⟩ : syracuseStep 2657957 = 498367) (by norm_num)
theorem B2657981 : Blo 1770086 2657981 := bbase (se 3 (by rfl) ⟨498371, by rfl⟩ : syracuseStep 2657981 = 996743) (by norm_num)
theorem B3985109 : Blo 1770086 3985109 := bbase (se 7 (by rfl) ⟨46700, by rfl⟩ : syracuseStep 3985109 = 93401) (by norm_num)
theorem B2658005 : Blo 1770086 2658005 := bbase (se 7 (by rfl) ⟨31148, by rfl⟩ : syracuseStep 2658005 = 62297) (by norm_num)
theorem B2658029 : Blo 1770086 2658029 := bbase (se 3 (by rfl) ⟨498380, by rfl⟩ : syracuseStep 2658029 = 996761) (by norm_num)
theorem B5385989 : Blo 1770086 5385989 := bbase (se 4 (by rfl) ⟨504936, by rfl⟩ : syracuseStep 5385989 = 1009873) (by norm_num)
theorem B2658053 : Blo 1770086 2658053 := bbase (se 4 (by rfl) ⟨249192, by rfl⟩ : syracuseStep 2658053 = 498385) (by norm_num)
theorem B3362573 : Blo 1770086 3362573 := bbase (se 3 (by rfl) ⟨630482, by rfl⟩ : syracuseStep 3362573 = 1260965) (by norm_num)
theorem B3985181 : Blo 1770086 3985181 := bbase (se 3 (by rfl) ⟨747221, by rfl⟩ : syracuseStep 3985181 = 1494443) (by norm_num)
theorem B2658077 : Blo 1770086 2658077 := bbase (se 3 (by rfl) ⟨498389, by rfl⟩ : syracuseStep 2658077 = 996779) (by norm_num)
theorem B2240293 : Blo 1770086 2240293 := bbase (se 4 (by rfl) ⟨210027, by rfl⟩ : syracuseStep 2240293 = 420055) (by norm_num)
theorem B4484909 : Blo 1770086 4484909 := bbase (se 3 (by rfl) ⟨840920, by rfl⟩ : syracuseStep 4484909 = 1681841) (by norm_num)
theorem B2658101 : Blo 1770086 2658101 := bbase (se 5 (by rfl) ⟨124598, by rfl⟩ : syracuseStep 2658101 = 249197) (by norm_num)
theorem B2658125 : Blo 1770086 2658125 := bbase (se 3 (by rfl) ⟨498398, by rfl⟩ : syracuseStep 2658125 = 996797) (by norm_num)
theorem B5975909 : Blo 1770086 5975909 := bbase (se 4 (by rfl) ⟨560241, by rfl⟩ : syracuseStep 5975909 = 1120483) (by norm_num)
theorem B3985253 : Blo 1770086 3985253 := bbase (se 4 (by rfl) ⟨373617, by rfl⟩ : syracuseStep 3985253 = 747235) (by norm_num)
theorem B3592045 : Blo 1770086 3592045 := bbase (se 3 (by rfl) ⟨673508, by rfl⟩ : syracuseStep 3592045 = 1347017) (by norm_num)
theorem B3780469 : Blo 1770086 3780469 := bbase (se 5 (by rfl) ⟨177209, by rfl⟩ : syracuseStep 3780469 = 354419) (by norm_num)
theorem B2240389 : Blo 1770086 2240389 := bbase (se 4 (by rfl) ⟨210036, by rfl⟩ : syracuseStep 2240389 = 420073) (by norm_num)
theorem B15339413 : Blo 1770086 15339413 := bbase (se 6 (by rfl) ⟨359517, by rfl⟩ : syracuseStep 15339413 = 719035) (by norm_num)
theorem B3362725 : Blo 1770086 3362725 := bbase (se 4 (by rfl) ⟨315255, by rfl⟩ : syracuseStep 3362725 = 630511) (by norm_num)
theorem B3985325 : Blo 1770086 3985325 := bbase (se 3 (by rfl) ⟨747248, by rfl⟩ : syracuseStep 3985325 = 1494497) (by norm_num)
theorem B8081333 : Blo 1770086 8081333 := bbase (se 5 (by rfl) ⟨378812, by rfl⟩ : syracuseStep 8081333 = 757625) (by norm_num)
theorem B3780589 : Blo 1770086 3780589 := bbase (se 3 (by rfl) ⟨708860, by rfl⟩ : syracuseStep 3780589 = 1417721) (by norm_num)
theorem B3985397 : Blo 1770086 3985397 := bbase (se 5 (by rfl) ⟨186815, by rfl⟩ : syracuseStep 3985397 = 373631) (by norm_num)
theorem B2240561 : Blo 1770086 2240561 := bbase (se 2 (by rfl) ⟨840210, by rfl⟩ : syracuseStep 2240561 = 1680421) (by norm_num)
theorem B3985469 : Blo 1770086 3985469 := bbase (se 3 (by rfl) ⟨747275, by rfl⟩ : syracuseStep 3985469 = 1494551) (by norm_num)
theorem B8966213 : Blo 1770086 8966213 := bbase (se 4 (by rfl) ⟨840582, by rfl⟩ : syracuseStep 8966213 = 1681165) (by norm_num)
theorem B2240617 : Blo 1770086 2240617 := bbase (se 2 (by rfl) ⟨840231, by rfl⟩ : syracuseStep 2240617 = 1680463) (by norm_num)
theorem B3985541 : Blo 1770086 3985541 := bbase (se 4 (by rfl) ⟨373644, by rfl⟩ : syracuseStep 3985541 = 747289) (by norm_num)
theorem B4485253 : Blo 1770086 4485253 := bbase (se 4 (by rfl) ⟨420492, by rfl⟩ : syracuseStep 4485253 = 840985) (by norm_num)
theorem B5042357 : Blo 1770086 5042357 := bbase (se 5 (by rfl) ⟨236360, by rfl⟩ : syracuseStep 5042357 = 472721) (by norm_num)
theorem B2240713 : Blo 1770086 2240713 := bbase (se 2 (by rfl) ⟨840267, by rfl⟩ : syracuseStep 2240713 = 1680535) (by norm_num)
theorem B3985613 : Blo 1770086 3985613 := bbase (se 3 (by rfl) ⟨747302, by rfl⟩ : syracuseStep 3985613 = 1494605) (by norm_num)
theorem B14356693 : Blo 1770086 14356693 := bbase (se 7 (by rfl) ⟨168242, by rfl⟩ : syracuseStep 14356693 = 336485) (by norm_num)
theorem B2019541 : Blo 1770086 2019541 := bbase (se 7 (by rfl) ⟨23666, by rfl⟩ : syracuseStep 2019541 = 47333) (by norm_num)
theorem B3363029 : Blo 1770086 3363029 := bbase (se 7 (by rfl) ⟨39410, by rfl⟩ : syracuseStep 3363029 = 78821) (by norm_num)
theorem B3780845 : Blo 1770086 3780845 := bbase (se 3 (by rfl) ⟨708908, by rfl⟩ : syracuseStep 3780845 = 1417817) (by norm_num)
theorem B4485365 : Blo 1770086 4485365 := bbase (se 5 (by rfl) ⟨210251, by rfl⟩ : syracuseStep 4485365 = 420503) (by norm_num)
theorem B5976341 : Blo 1770086 5976341 := bbase (se 6 (by rfl) ⟨140070, by rfl⟩ : syracuseStep 5976341 = 280141) (by norm_num)
theorem B3985685 : Blo 1770086 3985685 := bbase (se 6 (by rfl) ⟨93414, by rfl⟩ : syracuseStep 3985685 = 186829) (by norm_num)
theorem B3191069 : Blo 1770086 3191069 := bbase (se 3 (by rfl) ⟨598325, by rfl⟩ : syracuseStep 3191069 = 1196651) (by norm_num)
theorem B7565653 : Blo 1770086 7565653 := bbase (se 10 (by rfl) ⟨11082, by rfl⟩ : syracuseStep 7565653 = 22165) (by norm_num)
theorem B3985757 : Blo 1770086 3985757 := bbase (se 3 (by rfl) ⟨747329, by rfl⟩ : syracuseStep 3985757 = 1494659) (by norm_num)
theorem B3191141 : Blo 1770086 3191141 := bbase (se 4 (by rfl) ⟨299169, by rfl⟩ : syracuseStep 3191141 = 598339) (by norm_num)
theorem B2240885 : Blo 1770086 2240885 := bbase (se 5 (by rfl) ⟨105041, by rfl⟩ : syracuseStep 2240885 = 210083) (by norm_num)
theorem B2019713 : Blo 1770086 2019713 := bbase (se 2 (by rfl) ⟨757392, by rfl⟩ : syracuseStep 2019713 = 1514785) (by norm_num)
theorem B3985829 : Blo 1770086 3985829 := bbase (se 4 (by rfl) ⟨373671, by rfl⟩ : syracuseStep 3985829 = 747343) (by norm_num)
theorem B2240941 : Blo 1770086 2240941 := bbase (se 3 (by rfl) ⟨420176, by rfl⟩ : syracuseStep 2240941 = 840353) (by norm_num)
theorem B6721973 : Blo 1770086 6721973 := bbase (se 5 (by rfl) ⟨315092, by rfl⟩ : syracuseStep 6721973 = 630185) (by norm_num)
theorem B4485557 : Blo 1770086 4485557 := bbase (se 5 (by rfl) ⟨210260, by rfl⟩ : syracuseStep 4485557 = 420521) (by norm_num)
theorem B3985901 : Blo 1770086 3985901 := bbase (se 3 (by rfl) ⟨747356, by rfl⟩ : syracuseStep 3985901 = 1494713) (by norm_num)
theorem B2241037 : Blo 1770086 2241037 := bbase (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) (by norm_num)
theorem B3985973 : Blo 1770086 3985973 := bbase (se 5 (by rfl) ⟨186842, by rfl⟩ : syracuseStep 3985973 = 373685) (by norm_num)
theorem B3191357 : Blo 1770086 3191357 := bbase (se 3 (by rfl) ⟨598379, by rfl⟩ : syracuseStep 3191357 = 1196759) (by norm_num)
theorem B3986045 : Blo 1770086 3986045 := bbase (se 3 (by rfl) ⟨747383, by rfl⟩ : syracuseStep 3986045 = 1494767) (by norm_num)
theorem B2241209 : Blo 1770086 2241209 := bbase (se 2 (by rfl) ⟨840453, by rfl⟩ : syracuseStep 2241209 = 1680907) (by norm_num)
theorem B5976773 : Blo 1770086 5976773 := bbase (se 4 (by rfl) ⟨560322, by rfl⟩ : syracuseStep 5976773 = 1120645) (by norm_num)
theorem B3986117 : Blo 1770086 3986117 := bbase (se 4 (by rfl) ⟨373698, by rfl⟩ : syracuseStep 3986117 = 747397) (by norm_num)
theorem B6722261 : Blo 1770086 6722261 := bbase (se 7 (by rfl) ⟨78776, by rfl⟩ : syracuseStep 6722261 = 157553) (by norm_num)
theorem B2241265 : Blo 1770086 2241265 := bbase (se 2 (by rfl) ⟨840474, by rfl⟩ : syracuseStep 2241265 = 1680949) (by norm_num)
theorem B3986189 : Blo 1770086 3986189 := bbase (se 3 (by rfl) ⟨747410, by rfl⟩ : syracuseStep 3986189 = 1494821) (by norm_num)
theorem B10089269 : Blo 1770086 10089269 := bbase (se 5 (by rfl) ⟨472934, by rfl⟩ : syracuseStep 10089269 = 945869) (by norm_num)
theorem B2241361 : Blo 1770086 2241361 := bbase (se 2 (by rfl) ⟨840510, by rfl⟩ : syracuseStep 2241361 = 1681021) (by norm_num)
theorem B3986261 : Blo 1770086 3986261 := bbase (se 9 (by rfl) ⟨11678, by rfl⟩ : syracuseStep 3986261 = 23357) (by norm_num)
theorem B3986333 : Blo 1770086 3986333 := bbase (se 3 (by rfl) ⟨747437, by rfl⟩ : syracuseStep 3986333 = 1494875) (by norm_num)
theorem B10081205 : Blo 1770086 10081205 := bbase (se 5 (by rfl) ⟨472556, by rfl⟩ : syracuseStep 10081205 = 945113) (by norm_num)
theorem B2692021 : Blo 1770086 2692021 := bbase (se 5 (by rfl) ⟨126188, by rfl⟩ : syracuseStep 2692021 = 252377) (by norm_num)
theorem B3363781 : Blo 1770086 3363781 := bbase (se 4 (by rfl) ⟨315354, by rfl⟩ : syracuseStep 3363781 = 630709) (by norm_num)
theorem B3986405 : Blo 1770086 3986405 := bbase (se 4 (by rfl) ⟨373725, by rfl⟩ : syracuseStep 3986405 = 747451) (by norm_num)
theorem B2241533 : Blo 1770086 2241533 := bbase (se 3 (by rfl) ⟨420287, by rfl⟩ : syracuseStep 2241533 = 840575) (by norm_num)
theorem B3986477 : Blo 1770086 3986477 := bbase (se 3 (by rfl) ⟨747464, by rfl⟩ : syracuseStep 3986477 = 1494929) (by norm_num)
theorem B2241589 : Blo 1770086 2241589 := bbase (se 5 (by rfl) ⟨105074, by rfl⟩ : syracuseStep 2241589 = 210149) (by norm_num)
theorem B2987077 : Blo 1770086 2987077 := bbase (se 4 (by rfl) ⟨280038, by rfl⟩ : syracuseStep 2987077 = 560077) (by norm_num)
theorem B3363925 : Blo 1770086 3363925 := bbase (se 8 (by rfl) ⟨19710, by rfl⟩ : syracuseStep 3363925 = 39421) (by norm_num)
theorem B3781733 : Blo 1770086 3781733 := bbase (se 4 (by rfl) ⟨354537, by rfl⟩ : syracuseStep 3781733 = 709075) (by norm_num)
theorem B5977205 : Blo 1770086 5977205 := bbase (se 5 (by rfl) ⟨280181, by rfl⟩ : syracuseStep 5977205 = 560363) (by norm_num)
theorem B3986549 : Blo 1770086 3986549 := bbase (se 5 (by rfl) ⟨186869, by rfl⟩ : syracuseStep 3986549 = 373739) (by norm_num)
theorem B2241685 : Blo 1770086 2241685 := bbase (se 6 (by rfl) ⟨52539, by rfl⟩ : syracuseStep 2241685 = 105079) (by norm_num)
theorem B2987165 : Blo 1770086 2987165 := bbase (se 3 (by rfl) ⟨560093, by rfl⟩ : syracuseStep 2987165 = 1120187) (by norm_num)
theorem B6812837 : Blo 1770086 6812837 := bbase (se 4 (by rfl) ⟨638703, by rfl⟩ : syracuseStep 6812837 = 1277407) (by norm_num)
theorem B3986621 : Blo 1770086 3986621 := bbase (se 3 (by rfl) ⟨747491, by rfl⟩ : syracuseStep 3986621 = 1494983) (by norm_num)
theorem B3364085 : Blo 1770086 3364085 := bbase (se 5 (by rfl) ⟨157691, by rfl⟩ : syracuseStep 3364085 = 315383) (by norm_num)
theorem B3986693 : Blo 1770086 3986693 := bbase (se 4 (by rfl) ⟨373752, by rfl⟩ : syracuseStep 3986693 = 747505) (by norm_num)
theorem B2987293 : Blo 1770086 2987293 := bbase (se 3 (by rfl) ⟨560117, by rfl⟩ : syracuseStep 2987293 = 1120235) (by norm_num)
theorem B2241857 : Blo 1770086 2241857 := bbase (se 2 (by rfl) ⟨840696, by rfl⟩ : syracuseStep 2241857 = 1681393) (by norm_num)
theorem B3986765 : Blo 1770086 3986765 := bbase (se 3 (by rfl) ⟨747518, by rfl⟩ : syracuseStep 3986765 = 1495037) (by norm_num)
theorem B3781973 : Blo 1770086 3781973 := bbase (se 13 (by rfl) ⟨692, by rfl⟩ : syracuseStep 3781973 = 1385) (by norm_num)
theorem B5043541 : Blo 1770086 5043541 := bbase (se 13 (by rfl) ⟨923, by rfl⟩ : syracuseStep 5043541 = 1847) (by norm_num)
theorem B8967509 : Blo 1770086 8967509 := bbase (se 15 (by rfl) ⟨410, by rfl⟩ : syracuseStep 8967509 = 821) (by norm_num)
theorem B2020717 : Blo 1770086 2020717 := bbase (se 3 (by rfl) ⟨378884, by rfl⟩ : syracuseStep 2020717 = 757769) (by norm_num)
theorem B2987381 : Blo 1770086 2987381 := bbase (se 5 (by rfl) ⟨140033, by rfl⟩ : syracuseStep 2987381 = 280067) (by norm_num)
theorem B4789621 : Blo 1770086 4789621 := bbase (se 5 (by rfl) ⟨224513, by rfl⟩ : syracuseStep 4789621 = 449027) (by norm_num)
theorem B2241913 : Blo 1770086 2241913 := bbase (se 2 (by rfl) ⟨840717, by rfl⟩ : syracuseStep 2241913 = 1681435) (by norm_num)
theorem B3986837 : Blo 1770086 3986837 := bbase (se 6 (by rfl) ⟨93441, by rfl⟩ : syracuseStep 3986837 = 186883) (by norm_num)
theorem B10221013 : Blo 1770086 10221013 := bbase (se 7 (by rfl) ⟨119777, by rfl⟩ : syracuseStep 10221013 = 239555) (by norm_num)
theorem B18175445 : Blo 1770086 18175445 := bbase (se 7 (by rfl) ⟨212993, by rfl⟩ : syracuseStep 18175445 = 425987) (by norm_num)
theorem B2242009 : Blo 1770086 2242009 := bbase (se 2 (by rfl) ⟨840753, by rfl⟩ : syracuseStep 2242009 = 1681507) (by norm_num)
theorem B3986909 : Blo 1770086 3986909 := bbase (se 3 (by rfl) ⟨747545, by rfl⟩ : syracuseStep 3986909 = 1495091) (by norm_num)
theorem B2987509 : Blo 1770086 2987509 := bbase (se 5 (by rfl) ⟨140039, by rfl⟩ : syracuseStep 2987509 = 280079) (by norm_num)
theorem B5043701 : Blo 1770086 5043701 := bbase (se 5 (by rfl) ⟨236423, by rfl⟩ : syracuseStep 5043701 = 472847) (by norm_num)
theorem B2127389 : Blo 1770086 2127389 := bbase (se 3 (by rfl) ⟨398885, by rfl⟩ : syracuseStep 2127389 = 797771) (by norm_num)
theorem B5977637 : Blo 1770086 5977637 := bbase (se 4 (by rfl) ⟨560403, by rfl⟩ : syracuseStep 5977637 = 1120807) (by norm_num)
theorem B3986981 : Blo 1770086 3986981 := bbase (se 4 (by rfl) ⟨373779, by rfl⟩ : syracuseStep 3986981 = 747559) (by norm_num)
theorem B2987597 : Blo 1770086 2987597 := bbase (se 3 (by rfl) ⟨560174, by rfl⟩ : syracuseStep 2987597 = 1120349) (by norm_num)
theorem B2692685 : Blo 1770086 2692685 := bbase (se 3 (by rfl) ⟨504878, by rfl⟩ : syracuseStep 2692685 = 1009757) (by norm_num)
theorem B2520677 : Blo 1770086 2520677 := bbase (se 4 (by rfl) ⟨236313, by rfl⟩ : syracuseStep 2520677 = 472627) (by norm_num)
theorem B3987053 : Blo 1770086 3987053 := bbase (se 3 (by rfl) ⟨747572, by rfl⟩ : syracuseStep 3987053 = 1495145) (by norm_num)
theorem B2242181 : Blo 1770086 2242181 := bbase (se 4 (by rfl) ⟨210204, by rfl⟩ : syracuseStep 2242181 = 420409) (by norm_num)
theorem B2520757 : Blo 1770086 2520757 := bbase (se 5 (by rfl) ⟨118160, by rfl⟩ : syracuseStep 2520757 = 236321) (by norm_num)
theorem B3987125 : Blo 1770086 3987125 := bbase (se 5 (by rfl) ⟨186896, by rfl⟩ : syracuseStep 3987125 = 373793) (by norm_num)
theorem B2242237 : Blo 1770086 2242237 := bbase (se 3 (by rfl) ⟨420419, by rfl⟩ : syracuseStep 2242237 = 840839) (by norm_num)
theorem B2987725 : Blo 1770086 2987725 := bbase (se 3 (by rfl) ⟨560198, by rfl⟩ : syracuseStep 2987725 = 1120397) (by norm_num)
theorem B15136469 : Blo 1770086 15136469 := bbase (se 7 (by rfl) ⟨177380, by rfl⟩ : syracuseStep 15136469 = 354761) (by norm_num)
theorem B5043941 : Blo 1770086 5043941 := bbase (se 4 (by rfl) ⟨472869, by rfl⟩ : syracuseStep 5043941 = 945739) (by norm_num)
theorem B2242333 : Blo 1770086 2242333 := bbase (se 3 (by rfl) ⟨420437, by rfl⟩ : syracuseStep 2242333 = 840875) (by norm_num)
theorem B2987813 : Blo 1770086 2987813 := bbase (se 4 (by rfl) ⟨280107, by rfl⟩ : syracuseStep 2987813 = 560215) (by norm_num)
theorem B7567141 : Blo 1770086 7567141 := bbase (se 4 (by rfl) ⟨709419, by rfl⟩ : syracuseStep 7567141 = 1418839) (by norm_num)
theorem B2520877 : Blo 1770086 2520877 := bbase (se 3 (by rfl) ⟨472664, by rfl⟩ : syracuseStep 2520877 = 945329) (by norm_num)
theorem B5674805 : Blo 1770086 5674805 := bbase (se 5 (by rfl) ⟨266006, by rfl⟩ : syracuseStep 5674805 = 532013) (by norm_num)
theorem B7567157 : Blo 1770086 7567157 := bbase (se 5 (by rfl) ⟨354710, by rfl⟩ : syracuseStep 7567157 = 709421) (by norm_num)
theorem B3782477 : Blo 1770086 3782477 := bbase (se 3 (by rfl) ⟨709214, by rfl⟩ : syracuseStep 3782477 = 1418429) (by norm_num)
theorem B3782485 : Blo 1770086 3782485 := bbase (se 9 (by rfl) ⟨11081, by rfl⟩ : syracuseStep 3782485 = 22163) (by norm_num)
theorem B2127721 : Blo 1770086 2127721 := bbase (se 2 (by rfl) ⟨797895, by rfl⟩ : syracuseStep 2127721 = 1595791) (by norm_num)
theorem B6723445 : Blo 1770086 6723445 := bbase (se 5 (by rfl) ⟨315161, by rfl⟩ : syracuseStep 6723445 = 630323) (by norm_num)
theorem B13449077 : Blo 1770086 13449077 := bbase (se 5 (by rfl) ⟨630425, by rfl⟩ : syracuseStep 13449077 = 1260851) (by norm_num)
theorem B2520973 : Blo 1770086 2520973 := bbase (se 3 (by rfl) ⟨472682, by rfl⟩ : syracuseStep 2520973 = 945365) (by norm_num)
theorem B2987941 : Blo 1770086 2987941 := bbase (se 4 (by rfl) ⟨280119, by rfl⟩ : syracuseStep 2987941 = 560239) (by norm_num)
theorem B5044133 : Blo 1770086 5044133 := bbase (se 4 (by rfl) ⟨472887, by rfl⟩ : syracuseStep 5044133 = 945775) (by norm_num)
theorem B2242505 : Blo 1770086 2242505 := bbase (se 2 (by rfl) ⟨840939, by rfl⟩ : syracuseStep 2242505 = 1681879) (by norm_num)
theorem B5978069 : Blo 1770086 5978069 := bbase (se 7 (by rfl) ⟨70055, by rfl⟩ : syracuseStep 5978069 = 140111) (by norm_num)
theorem B10090453 : Blo 1770086 10090453 := bbase (se 7 (by rfl) ⟨118247, by rfl⟩ : syracuseStep 10090453 = 236495) (by norm_num)
theorem B2988029 : Blo 1770086 2988029 := bbase (se 3 (by rfl) ⟨560255, by rfl⟩ : syracuseStep 2988029 = 1120511) (by norm_num)
theorem B2242561 : Blo 1770086 2242561 := bbase (se 2 (by rfl) ⟨840960, by rfl⟩ : syracuseStep 2242561 = 1681921) (by norm_num)
theorem B11352149 : Blo 1770086 11352149 := bbase (se 8 (by rfl) ⟨66516, by rfl⟩ : syracuseStep 11352149 = 133033) (by norm_num)
theorem B2242657 : Blo 1770086 2242657 := bbase (se 2 (by rfl) ⟨840996, by rfl⟩ : syracuseStep 2242657 = 1681993) (by norm_num)
theorem B2988157 : Blo 1770086 2988157 := bbase (se 3 (by rfl) ⟨560279, by rfl⟩ : syracuseStep 2988157 = 1120559) (by norm_num)
theorem B6723749 : Blo 1770086 6723749 := bbase (se 4 (by rfl) ⟨630351, by rfl⟩ : syracuseStep 6723749 = 1260703) (by norm_num)
theorem B2988245 : Blo 1770086 2988245 := bbase (se 7 (by rfl) ⟨35018, by rfl⟩ : syracuseStep 2988245 = 70037) (by norm_num)
theorem B5749061 : Blo 1770086 5749061 := bbase (se 4 (by rfl) ⟨538974, by rfl⟩ : syracuseStep 5749061 = 1077949) (by norm_num)
theorem B2988373 : Blo 1770086 2988373 := bbase (se 10 (by rfl) ⟨4377, by rfl⟩ : syracuseStep 2988373 = 8755) (by norm_num)
theorem B2521469 : Blo 1770086 2521469 := bbase (se 3 (by rfl) ⟨472775, by rfl⟩ : syracuseStep 2521469 = 945551) (by norm_num)
theorem B5978501 : Blo 1770086 5978501 := bbase (se 4 (by rfl) ⟨560484, by rfl⟩ : syracuseStep 5978501 = 1120969) (by norm_num)
theorem B21543317 : Blo 1770086 21543317 := bbase (se 6 (by rfl) ⟨504921, by rfl⟩ : syracuseStep 21543317 = 1009843) (by norm_num)
theorem B1890713 : Blo 1770086 1890713 := bbase (se 2 (by rfl) ⟨709017, by rfl⟩ : syracuseStep 1890713 = 1418035) (by norm_num)
theorem B2988461 : Blo 1770086 2988461 := bbase (se 3 (by rfl) ⟨560336, by rfl⟩ : syracuseStep 2988461 = 1120673) (by norm_num)
theorem B3832309 : Blo 1770086 3832309 := bbase (se 5 (by rfl) ⟨179639, by rfl⟩ : syracuseStep 3832309 = 359279) (by norm_num)
theorem B4037165 : Blo 1770086 4037165 := bbase (se 3 (by rfl) ⟨756968, by rfl⟩ : syracuseStep 4037165 = 1513937) (by norm_num)
theorem B2988589 : Blo 1770086 2988589 := bbase (se 3 (by rfl) ⟨560360, by rfl⟩ : syracuseStep 2988589 = 1120721) (by norm_num)
theorem B2693693 : Blo 1770086 2693693 := bbase (se 3 (by rfl) ⟨505067, by rfl⟩ : syracuseStep 2693693 = 1010135) (by norm_num)
theorem B1890901 : Blo 1770086 1890901 := bbase (se 8 (by rfl) ⟨11079, by rfl⟩ : syracuseStep 1890901 = 22159) (by norm_num)
theorem B8968805 : Blo 1770086 8968805 := bbase (se 4 (by rfl) ⟨840825, by rfl⟩ : syracuseStep 8968805 = 1681651) (by norm_num)
theorem B2988677 : Blo 1770086 2988677 := bbase (se 4 (by rfl) ⟨280188, by rfl⟩ : syracuseStep 2988677 = 560377) (by norm_num)
theorem B12114613 : Blo 1770086 12114613 := bbase (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) (by norm_num)
theorem B2128609 : Blo 1770086 2128609 := bbase (se 2 (by rfl) ⟨798228, by rfl⟩ : syracuseStep 2128609 = 1596457) (by norm_num)
theorem B17013493 : Blo 1770086 17013493 := bbase (se 5 (by rfl) ⟨797507, by rfl⟩ : syracuseStep 17013493 = 1595015) (by norm_num)
theorem B2988805 : Blo 1770086 2988805 := bbase (se 4 (by rfl) ⟨280200, by rfl⟩ : syracuseStep 2988805 = 560401) (by norm_num)
theorem B3455765 : Blo 1770086 3455765 := bbase (se 6 (by rfl) ⟨80994, by rfl⟩ : syracuseStep 3455765 = 161989) (by norm_num)
theorem B5978933 : Blo 1770086 5978933 := bbase (se 5 (by rfl) ⟨280262, by rfl⟩ : syracuseStep 5978933 = 560525) (by norm_num)
theorem B2988893 : Blo 1770086 2988893 := bbase (se 3 (by rfl) ⟨560417, by rfl⟩ : syracuseStep 2988893 = 1120835) (by norm_num)
theorem B5045125 : Blo 1770086 5045125 := bbase (se 4 (by rfl) ⟨472980, by rfl⟩ : syracuseStep 5045125 = 945961) (by norm_num)
theorem B11344789 : Blo 1770086 11344789 := bbase (se 6 (by rfl) ⟨265893, by rfl⟩ : syracuseStep 11344789 = 531787) (by norm_num)
theorem B2522021 : Blo 1770086 2522021 := bbase (se 4 (by rfl) ⟨236439, by rfl⟩ : syracuseStep 2522021 = 472879) (by norm_num)
theorem B3783613 : Blo 1770086 3783613 := bbase (se 3 (by rfl) ⟨709427, by rfl⟩ : syracuseStep 3783613 = 1418855) (by norm_num)
theorem B17030101 : Blo 1770086 17030101 := bbase (se 7 (by rfl) ⟨199571, by rfl⟩ : syracuseStep 17030101 = 399143) (by norm_num)
theorem B2989021 : Blo 1770086 2989021 := bbase (se 3 (by rfl) ⟨560441, by rfl⟩ : syracuseStep 2989021 = 1120883) (by norm_num)
theorem B8510437 : Blo 1770086 8510437 := bbase (se 4 (by rfl) ⟨797853, by rfl⟩ : syracuseStep 8510437 = 1595707) (by norm_num)
theorem B2989109 : Blo 1770086 2989109 := bbase (se 5 (by rfl) ⟨140114, by rfl⟩ : syracuseStep 2989109 = 280229) (by norm_num)
theorem B5676085 : Blo 1770086 5676085 := bbase (se 5 (by rfl) ⟨266066, by rfl⟩ : syracuseStep 5676085 = 532133) (by norm_num)
theorem B4545629 : Blo 1770086 4545629 := bbase (se 3 (by rfl) ⟨852305, by rfl⟩ : syracuseStep 4545629 = 1704611) (by norm_num)
theorem B2989237 : Blo 1770086 2989237 := bbase (se 5 (by rfl) ⟨140120, by rfl⟩ : syracuseStep 2989237 = 280241) (by norm_num)
theorem B5979365 : Blo 1770086 5979365 := bbase (se 4 (by rfl) ⟨560565, by rfl⟩ : syracuseStep 5979365 = 1121131) (by norm_num)
theorem B4545773 : Blo 1770086 4545773 := bbase (se 3 (by rfl) ⟨852332, by rfl⟩ : syracuseStep 4545773 = 1704665) (by norm_num)
theorem B2989325 : Blo 1770086 2989325 := bbase (se 3 (by rfl) ⟨560498, by rfl⟩ : syracuseStep 2989325 = 1120997) (by norm_num)
theorem B3783989 : Blo 1770086 3783989 := bbase (se 5 (by rfl) ⟨177374, by rfl⟩ : syracuseStep 3783989 = 354749) (by norm_num)
theorem B6380869 : Blo 1770086 6380869 := bbase (se 4 (by rfl) ⟨598206, by rfl⟩ : syracuseStep 6380869 = 1196413) (by norm_num)
theorem B4545877 : Blo 1770086 4545877 := bbase (se 11 (by rfl) ⟨3329, by rfl⟩ : syracuseStep 4545877 = 6659) (by norm_num)
theorem B1891721 : Blo 1770086 1891721 := bbase (se 2 (by rfl) ⟨709395, by rfl⟩ : syracuseStep 1891721 = 1418791) (by norm_num)
theorem B2989453 : Blo 1770086 2989453 := bbase (se 3 (by rfl) ⟨560522, by rfl⟩ : syracuseStep 2989453 = 1121045) (by norm_num)
theorem B2989541 : Blo 1770086 2989541 := bbase (se 4 (by rfl) ⟨280269, by rfl⟩ : syracuseStep 2989541 = 560539) (by norm_num)
theorem B12115541 : Blo 1770086 12115541 := bbase (se 8 (by rfl) ⟨70989, by rfl⟩ : syracuseStep 12115541 = 141979) (by norm_num)
theorem B2989669 : Blo 1770086 2989669 := bbase (se 4 (by rfl) ⟨280281, by rfl⟩ : syracuseStep 2989669 = 560563) (by norm_num)
theorem B3030637 : Blo 1770086 3030637 := bbase (se 3 (by rfl) ⟨568244, by rfl⟩ : syracuseStep 3030637 = 1136489) (by norm_num)
theorem B13631093 : Blo 1770086 13631093 := bbase (se 5 (by rfl) ⟨638957, by rfl⟩ : syracuseStep 13631093 = 1277915) (by norm_num)
theorem B5979797 : Blo 1770086 5979797 := bbase (se 6 (by rfl) ⟨140151, by rfl⟩ : syracuseStep 5979797 = 280303) (by norm_num)
theorem B2522773 : Blo 1770086 2522773 := bbase (se 6 (by rfl) ⟨59127, by rfl⟩ : syracuseStep 2522773 = 118255) (by norm_num)
theorem B2989757 : Blo 1770086 2989757 := bbase (se 3 (by rfl) ⟨560579, by rfl⟩ : syracuseStep 2989757 = 1121159) (by norm_num)
theorem B4480717 : Blo 1770086 4480717 := bbase (se 3 (by rfl) ⟨840134, by rfl⟩ : syracuseStep 4480717 = 1680269) (by norm_num)
theorem B3407581 : Blo 1770086 3407581 := bbase (se 3 (by rfl) ⟨638921, by rfl⟩ : syracuseStep 3407581 = 1277843) (by norm_num)
theorem B6381317 : Blo 1770086 6381317 := bbase (se 4 (by rfl) ⟨598248, by rfl⟩ : syracuseStep 6381317 = 1196497) (by norm_num)
theorem B7282469 : Blo 1770086 7282469 := bbase (se 4 (by rfl) ⟨682731, by rfl⟩ : syracuseStep 7282469 = 1365463) (by norm_num)
theorem B4480829 : Blo 1770086 4480829 := bbase (se 3 (by rfl) ⟨840155, by rfl⟩ : syracuseStep 4480829 = 1680311) (by norm_num)
theorem B2989885 : Blo 1770086 2989885 := bbase (se 3 (by rfl) ⟨560603, by rfl⟩ : syracuseStep 2989885 = 1121207) (by norm_num)
theorem B1892165 : Blo 1770086 1892165 := bbase (se 4 (by rfl) ⟨177390, by rfl⟩ : syracuseStep 1892165 = 354781) (by norm_num)
theorem B8970101 : Blo 1770086 8970101 := bbase (se 5 (by rfl) ⟨420473, by rfl⟩ : syracuseStep 8970101 = 840947) (by norm_num)
theorem B2989973 : Blo 1770086 2989973 := bbase (se 6 (by rfl) ⟨70077, by rfl⟩ : syracuseStep 2989973 = 140155) (by norm_num)
theorem B10092437 : Blo 1770086 10092437 := bbase (se 6 (by rfl) ⟨236541, by rfl⟩ : syracuseStep 10092437 = 473083) (by norm_num)
theorem B5046229 : Blo 1770086 5046229 := bbase (se 7 (by rfl) ⟨59135, by rfl⟩ : syracuseStep 5046229 = 118271) (by norm_num)
theorem B4481021 : Blo 1770086 4481021 := bbase (se 3 (by rfl) ⟨840191, by rfl⟩ : syracuseStep 4481021 = 1680383) (by norm_num)
theorem B2990081 : Blo 1770086 2990081 := bstep (se 2 (by rfl) ⟨1121280, by rfl⟩ : syracuseStep 2990081 = 2242561) B2242561
theorem B5046275 : Blo 1770086 5046275 := bstep (se 1 (by rfl) ⟨3784706, by rfl⟩ : syracuseStep 5046275 = 7569413) B7569413
theorem B4481041 : Blo 1770086 4481041 := bstep (se 2 (by rfl) ⟨1680390, by rfl⟩ : syracuseStep 4481041 = 3360781) B3360781
theorem B2990209 : Blo 1770086 2990209 := bstep (se 2 (by rfl) ⟨1121328, by rfl⟩ : syracuseStep 2990209 = 2242657) B2242657
theorem B2990243 : Blo 1770086 2990243 := bstep (se 1 (by rfl) ⟨2242682, by rfl⟩ : syracuseStep 2990243 = 4485365) B4485365
theorem B5980337 : Blo 1770086 5980337 := bstep (se 2 (by rfl) ⟨2242626, by rfl⟩ : syracuseStep 5980337 = 4485253) B4485253
theorem B10084621 : Blo 1770086 10084621 := bstep (se 3 (by rfl) ⟨1890866, by rfl⟩ : syracuseStep 10084621 = 3781733) B3781733
theorem B4481315 : Blo 1770086 4481315 := bstep (se 1 (by rfl) ⟨3360986, by rfl⟩ : syracuseStep 4481315 = 6721973) B6721973
theorem B2990371 : Blo 1770086 2990371 := bstep (se 1 (by rfl) ⟨2242778, by rfl⟩ : syracuseStep 2990371 = 4485557) B4485557
theorem B4481507 : Blo 1770086 4481507 := bstep (se 1 (by rfl) ⟨3361130, by rfl⟩ : syracuseStep 4481507 = 6722261) B6722261
theorem B2392561 : Blo 1770086 2392561 := bstep (se 2 (by rfl) ⟨897210, by rfl⟩ : syracuseStep 2392561 = 1794421) B1794421
theorem B6726179 : Blo 1770086 6726179 := bstep (se 1 (by rfl) ⟨5044634, by rfl⟩ : syracuseStep 6726179 = 10089269) B10089269
theorem B1770099 : Blo 1770086 1770099 := bstep (se 1 (by rfl) ⟨1327574, by rfl⟩ : syracuseStep 1770099 = 2655149) B2655149
theorem B1770115 : Blo 1770086 1770115 := bstep (se 1 (by rfl) ⟨1327586, by rfl⟩ : syracuseStep 1770115 = 2655173) B2655173
theorem B1770131 : Blo 1770086 1770131 := bstep (se 1 (by rfl) ⟨1327598, by rfl⟩ : syracuseStep 1770131 = 2655197) B2655197
theorem B1770147 : Blo 1770086 1770147 := bstep (se 1 (by rfl) ⟨1327610, by rfl⟩ : syracuseStep 1770147 = 2655221) B2655221
theorem B1770163 : Blo 1770086 1770163 := bstep (se 1 (by rfl) ⟨1327622, by rfl⟩ : syracuseStep 1770163 = 2655245) B2655245
theorem B1770179 : Blo 1770086 1770179 := bstep (se 1 (by rfl) ⟨1327634, by rfl⟩ : syracuseStep 1770179 = 2655269) B2655269
theorem B1770195 : Blo 1770086 1770195 := bstep (se 1 (by rfl) ⟨1327646, by rfl⟩ : syracuseStep 1770195 = 2655293) B2655293
theorem B1770211 : Blo 1770086 1770211 := bstep (se 1 (by rfl) ⟨1327658, by rfl⟩ : syracuseStep 1770211 = 2655317) B2655317
theorem B1770227 : Blo 1770086 1770227 := bstep (se 1 (by rfl) ⟨1327670, by rfl⟩ : syracuseStep 1770227 = 2655341) B2655341
theorem B1770243 : Blo 1770086 1770243 := bstep (se 1 (by rfl) ⟨1327682, by rfl⟩ : syracuseStep 1770243 = 2655365) B2655365
theorem B1991443 : Blo 1770086 1991443 := bstep (se 1 (by rfl) ⟨1493582, by rfl⟩ : syracuseStep 1991443 = 2987165) B2987165
theorem B1770259 : Blo 1770086 1770259 := bstep (se 1 (by rfl) ⟨1327694, by rfl⟩ : syracuseStep 1770259 = 2655389) B2655389
theorem B1770275 : Blo 1770086 1770275 := bstep (se 1 (by rfl) ⟨1327706, by rfl⟩ : syracuseStep 1770275 = 2655413) B2655413
theorem B1770291 : Blo 1770086 1770291 := bstep (se 1 (by rfl) ⟨1327718, by rfl⟩ : syracuseStep 1770291 = 2655437) B2655437
theorem B1770307 : Blo 1770086 1770307 := bstep (se 1 (by rfl) ⟨1327730, by rfl⟩ : syracuseStep 1770307 = 2655461) B2655461
theorem B1770323 : Blo 1770086 1770323 := bstep (se 1 (by rfl) ⟨1327742, by rfl⟩ : syracuseStep 1770323 = 2655485) B2655485
theorem B1770339 : Blo 1770086 1770339 := bstep (se 1 (by rfl) ⟨1327754, by rfl⟩ : syracuseStep 1770339 = 2655509) B2655509
theorem B1770355 : Blo 1770086 1770355 := bstep (se 1 (by rfl) ⟨1327766, by rfl⟩ : syracuseStep 1770355 = 2655533) B2655533
theorem B1770371 : Blo 1770086 1770371 := bstep (se 1 (by rfl) ⟨1327778, by rfl⟩ : syracuseStep 1770371 = 2655557) B2655557
theorem B1770387 : Blo 1770086 1770387 := bstep (se 1 (by rfl) ⟨1327790, by rfl⟩ : syracuseStep 1770387 = 2655581) B2655581
theorem B2655137 : Blo 1770086 2655137 := bstep (se 2 (by rfl) ⟨995676, by rfl⟩ : syracuseStep 2655137 = 1991353) B1991353
theorem B1991587 : Blo 1770086 1991587 := bstep (se 1 (by rfl) ⟨1493690, by rfl⟩ : syracuseStep 1991587 = 2987381) B2987381
theorem B1770403 : Blo 1770086 1770403 := bstep (se 1 (by rfl) ⟨1327802, by rfl⟩ : syracuseStep 1770403 = 2655605) B2655605
theorem B2655155 : Blo 1770086 2655155 := bstep (se 1 (by rfl) ⟨1991366, by rfl⟩ : syracuseStep 2655155 = 3982733) B3982733
theorem B1770419 : Blo 1770086 1770419 := bstep (se 1 (by rfl) ⟨1327814, by rfl⟩ : syracuseStep 1770419 = 2655629) B2655629
theorem B1770435 : Blo 1770086 1770435 := bstep (se 1 (by rfl) ⟨1327826, by rfl⟩ : syracuseStep 1770435 = 2655653) B2655653
theorem B2655185 : Blo 1770086 2655185 := bstep (se 2 (by rfl) ⟨995694, by rfl⟩ : syracuseStep 2655185 = 1991389) B1991389
theorem B1770451 : Blo 1770086 1770451 := bstep (se 1 (by rfl) ⟨1327838, by rfl⟩ : syracuseStep 1770451 = 2655677) B2655677
theorem B2655203 : Blo 1770086 2655203 := bstep (se 1 (by rfl) ⟨1991402, by rfl⟩ : syracuseStep 2655203 = 3982805) B3982805
theorem B1770467 : Blo 1770086 1770467 := bstep (se 1 (by rfl) ⟨1327850, by rfl⟩ : syracuseStep 1770467 = 2655701) B2655701
theorem B12116963 : Blo 1770086 12116963 := bstep (se 1 (by rfl) ⟨9087722, by rfl⟩ : syracuseStep 12116963 = 18175445) B18175445
theorem B22684657 : Blo 1770086 22684657 := bstep (se 2 (by rfl) ⟨8506746, by rfl⟩ : syracuseStep 22684657 = 17013493) B17013493
theorem B1770483 : Blo 1770086 1770483 := bstep (se 1 (by rfl) ⟨1327862, by rfl⟩ : syracuseStep 1770483 = 2655725) B2655725
theorem B2655233 : Blo 1770086 2655233 := bstep (se 2 (by rfl) ⟨995712, by rfl⟩ : syracuseStep 2655233 = 1991425) B1991425
theorem B1770499 : Blo 1770086 1770499 := bstep (se 1 (by rfl) ⟨1327874, by rfl⟩ : syracuseStep 1770499 = 2655749) B2655749
theorem B2655251 : Blo 1770086 2655251 := bstep (se 1 (by rfl) ⟨1991438, by rfl⟩ : syracuseStep 2655251 = 3982877) B3982877
theorem B1770515 : Blo 1770086 1770515 := bstep (se 1 (by rfl) ⟨1327886, by rfl⟩ : syracuseStep 1770515 = 2655773) B2655773
theorem B1770531 : Blo 1770086 1770531 := bstep (se 1 (by rfl) ⟨1327898, by rfl⟩ : syracuseStep 1770531 = 2655797) B2655797
theorem B2655281 : Blo 1770086 2655281 := bstep (se 2 (by rfl) ⟨995730, by rfl⟩ : syracuseStep 2655281 = 1991461) B1991461
theorem B1991731 : Blo 1770086 1991731 := bstep (se 1 (by rfl) ⟨1493798, by rfl⟩ : syracuseStep 1991731 = 2987597) B2987597
theorem B1770547 : Blo 1770086 1770547 := bstep (se 1 (by rfl) ⟨1327910, by rfl⟩ : syracuseStep 1770547 = 2655821) B2655821
theorem B1795123 : Blo 1770086 1795123 := bstep (se 1 (by rfl) ⟨1346342, by rfl⟩ : syracuseStep 1795123 = 2692685) B2692685
theorem B2655299 : Blo 1770086 2655299 := bstep (se 1 (by rfl) ⟨1991474, by rfl⟩ : syracuseStep 2655299 = 3982949) B3982949
theorem B1770563 : Blo 1770086 1770563 := bstep (se 1 (by rfl) ⟨1327922, by rfl⟩ : syracuseStep 1770563 = 2655845) B2655845
theorem B15131717 : Blo 1770086 15131717 := bstep (se 4 (by rfl) ⟨1418598, by rfl⟩ : syracuseStep 15131717 = 2837197) B2837197
theorem B1770579 : Blo 1770086 1770579 := bstep (se 1 (by rfl) ⟨1327934, by rfl⟩ : syracuseStep 1770579 = 2655869) B2655869
theorem B2655329 : Blo 1770086 2655329 := bstep (se 2 (by rfl) ⟨995748, by rfl⟩ : syracuseStep 2655329 = 1991497) B1991497
theorem B1770595 : Blo 1770086 1770595 := bstep (se 1 (by rfl) ⟨1327946, by rfl⟩ : syracuseStep 1770595 = 2655893) B2655893
theorem B2655347 : Blo 1770086 2655347 := bstep (se 1 (by rfl) ⟨1991510, by rfl⟩ : syracuseStep 2655347 = 3983021) B3983021
theorem B1770611 : Blo 1770086 1770611 := bstep (se 1 (by rfl) ⟨1327958, by rfl⟩ : syracuseStep 1770611 = 2655917) B2655917
theorem B1770627 : Blo 1770086 1770627 := bstep (se 1 (by rfl) ⟨1327970, by rfl⟩ : syracuseStep 1770627 = 2655941) B2655941
theorem B2655377 : Blo 1770086 2655377 := bstep (se 2 (by rfl) ⟨995766, by rfl⟩ : syracuseStep 2655377 = 1991533) B1991533
theorem B1770643 : Blo 1770086 1770643 := bstep (se 1 (by rfl) ⟨1327982, by rfl⟩ : syracuseStep 1770643 = 2655965) B2655965
theorem B2655395 : Blo 1770086 2655395 := bstep (se 1 (by rfl) ⟨1991546, by rfl⟩ : syracuseStep 2655395 = 3983093) B3983093
theorem B1770659 : Blo 1770086 1770659 := bstep (se 1 (by rfl) ⟨1327994, by rfl⟩ : syracuseStep 1770659 = 2655989) B2655989
theorem B6726833 : Blo 1770086 6726833 := bstep (se 2 (by rfl) ⟨2522562, by rfl⟩ : syracuseStep 6726833 = 5045125) B5045125
theorem B1770675 : Blo 1770086 1770675 := bstep (se 1 (by rfl) ⟨1328006, by rfl⟩ : syracuseStep 1770675 = 2656013) B2656013
theorem B2655425 : Blo 1770086 2655425 := bstep (se 2 (by rfl) ⟨995784, by rfl⟩ : syracuseStep 2655425 = 1991569) B1991569
theorem B1991875 : Blo 1770086 1991875 := bstep (se 1 (by rfl) ⟨1493906, by rfl⟩ : syracuseStep 1991875 = 2987813) B2987813
theorem B1770691 : Blo 1770086 1770691 := bstep (se 1 (by rfl) ⟨1328018, by rfl⟩ : syracuseStep 1770691 = 2656037) B2656037
theorem B2655443 : Blo 1770086 2655443 := bstep (se 1 (by rfl) ⟨1991582, by rfl⟩ : syracuseStep 2655443 = 3983165) B3983165
theorem B1770707 : Blo 1770086 1770707 := bstep (se 1 (by rfl) ⟨1328030, by rfl⟩ : syracuseStep 1770707 = 2656061) B2656061
theorem B1770723 : Blo 1770086 1770723 := bstep (se 1 (by rfl) ⟨1328042, by rfl⟩ : syracuseStep 1770723 = 2656085) B2656085
theorem B2655473 : Blo 1770086 2655473 := bstep (se 2 (by rfl) ⟨995802, by rfl⟩ : syracuseStep 2655473 = 1991605) B1991605
theorem B3589361 : Blo 1770086 3589361 := bstep (se 2 (by rfl) ⟨1346010, by rfl⟩ : syracuseStep 3589361 = 2692021) B2692021
theorem B1770739 : Blo 1770086 1770739 := bstep (se 1 (by rfl) ⟨1328054, by rfl⟩ : syracuseStep 1770739 = 2656109) B2656109
theorem B2655491 : Blo 1770086 2655491 := bstep (se 1 (by rfl) ⟨1991618, by rfl⟩ : syracuseStep 2655491 = 3983237) B3983237
theorem B1770755 : Blo 1770086 1770755 := bstep (se 1 (by rfl) ⟨1328066, by rfl⟩ : syracuseStep 1770755 = 2656133) B2656133
theorem B2835731 : Blo 1770086 2835731 := bstep (se 1 (by rfl) ⟨2126798, by rfl⟩ : syracuseStep 2835731 = 4253597) B4253597
theorem B1770771 : Blo 1770086 1770771 := bstep (se 1 (by rfl) ⟨1328078, by rfl⟩ : syracuseStep 1770771 = 2656157) B2656157
theorem B2655521 : Blo 1770086 2655521 := bstep (se 2 (by rfl) ⟨995820, by rfl⟩ : syracuseStep 2655521 = 1991641) B1991641
theorem B1770787 : Blo 1770086 1770787 := bstep (se 1 (by rfl) ⟨1328090, by rfl⟩ : syracuseStep 1770787 = 2656181) B2656181
theorem B2655539 : Blo 1770086 2655539 := bstep (se 1 (by rfl) ⟨1991654, by rfl⟩ : syracuseStep 2655539 = 3983309) B3983309
theorem B1770803 : Blo 1770086 1770803 := bstep (se 1 (by rfl) ⟨1328102, by rfl⟩ : syracuseStep 1770803 = 2656205) B2656205
theorem B1770819 : Blo 1770086 1770819 := bstep (se 1 (by rfl) ⟨1328114, by rfl⟩ : syracuseStep 1770819 = 2656229) B2656229
theorem B2655569 : Blo 1770086 2655569 := bstep (se 2 (by rfl) ⟨995838, by rfl⟩ : syracuseStep 2655569 = 1991677) B1991677
theorem B1992019 : Blo 1770086 1992019 := bstep (se 1 (by rfl) ⟨1494014, by rfl⟩ : syracuseStep 1992019 = 2988029) B2988029
theorem B1770835 : Blo 1770086 1770835 := bstep (se 1 (by rfl) ⟨1328126, by rfl⟩ : syracuseStep 1770835 = 2656253) B2656253
theorem B2655587 : Blo 1770086 2655587 := bstep (se 1 (by rfl) ⟨1991690, by rfl⟩ : syracuseStep 2655587 = 3983381) B3983381
theorem B1770851 : Blo 1770086 1770851 := bstep (se 1 (by rfl) ⟨1328138, by rfl⟩ : syracuseStep 1770851 = 2656277) B2656277
theorem B1770867 : Blo 1770086 1770867 := bstep (se 1 (by rfl) ⟨1328150, by rfl⟩ : syracuseStep 1770867 = 2656301) B2656301
theorem B2655617 : Blo 1770086 2655617 := bstep (se 2 (by rfl) ⟨995856, by rfl⟩ : syracuseStep 2655617 = 1991713) B1991713
theorem B1770883 : Blo 1770086 1770883 := bstep (se 1 (by rfl) ⟨1328162, by rfl⟩ : syracuseStep 1770883 = 2656325) B2656325
theorem B4482449 : Blo 1770086 4482449 := bstep (se 2 (by rfl) ⟨1680918, by rfl⟩ : syracuseStep 4482449 = 3361837) B3361837
theorem B2655635 : Blo 1770086 2655635 := bstep (se 1 (by rfl) ⟨1991726, by rfl⟩ : syracuseStep 2655635 = 3983453) B3983453
theorem B1770899 : Blo 1770086 1770899 := bstep (se 1 (by rfl) ⟨1328174, by rfl⟩ : syracuseStep 1770899 = 2656349) B2656349
theorem B1770915 : Blo 1770086 1770915 := bstep (se 1 (by rfl) ⟨1328186, by rfl⟩ : syracuseStep 1770915 = 2656373) B2656373
theorem B3982769 : Blo 1770086 3982769 := bstep (se 2 (by rfl) ⟨1493538, by rfl⟩ : syracuseStep 3982769 = 2987077) B2987077
theorem B2655665 : Blo 1770086 2655665 := bstep (se 2 (by rfl) ⟨995874, by rfl⟩ : syracuseStep 2655665 = 1991749) B1991749
theorem B1770931 : Blo 1770086 1770931 := bstep (se 1 (by rfl) ⟨1328198, by rfl⟩ : syracuseStep 1770931 = 2656397) B2656397
theorem B3982787 : Blo 1770086 3982787 := bstep (se 1 (by rfl) ⟨2987090, by rfl⟩ : syracuseStep 3982787 = 5974181) B5974181
theorem B2655683 : Blo 1770086 2655683 := bstep (se 1 (by rfl) ⟨1991762, by rfl⟩ : syracuseStep 2655683 = 3983525) B3983525
theorem B4482499 : Blo 1770086 4482499 := bstep (se 1 (by rfl) ⟨3361874, by rfl⟩ : syracuseStep 4482499 = 6723749) B6723749
theorem B1770947 : Blo 1770086 1770947 := bstep (se 1 (by rfl) ⟨1328210, by rfl⟩ : syracuseStep 1770947 = 2656421) B2656421
theorem B1770963 : Blo 1770086 1770963 := bstep (se 1 (by rfl) ⟨1328222, by rfl⟩ : syracuseStep 1770963 = 2656445) B2656445
theorem B2655713 : Blo 1770086 2655713 := bstep (se 2 (by rfl) ⟨995892, by rfl⟩ : syracuseStep 2655713 = 1991785) B1991785
theorem B1992163 : Blo 1770086 1992163 := bstep (se 1 (by rfl) ⟨1494122, by rfl⟩ : syracuseStep 1992163 = 2988245) B2988245
theorem B1770979 : Blo 1770086 1770979 := bstep (se 1 (by rfl) ⟨1328234, by rfl⟩ : syracuseStep 1770979 = 2656469) B2656469
theorem B2655731 : Blo 1770086 2655731 := bstep (se 1 (by rfl) ⟨1991798, by rfl⟩ : syracuseStep 2655731 = 3983597) B3983597
theorem B1770995 : Blo 1770086 1770995 := bstep (se 1 (by rfl) ⟨1328246, by rfl⟩ : syracuseStep 1770995 = 2656493) B2656493
theorem B1771011 : Blo 1770086 1771011 := bstep (se 1 (by rfl) ⟨1328258, by rfl⟩ : syracuseStep 1771011 = 2656517) B2656517
theorem B2655761 : Blo 1770086 2655761 := bstep (se 2 (by rfl) ⟨995910, by rfl⟩ : syracuseStep 2655761 = 1991821) B1991821
theorem B1771027 : Blo 1770086 1771027 := bstep (se 1 (by rfl) ⟨1328270, by rfl⟩ : syracuseStep 1771027 = 2656541) B2656541
theorem B2655779 : Blo 1770086 2655779 := bstep (se 1 (by rfl) ⟨1991834, by rfl⟩ : syracuseStep 2655779 = 3983669) B3983669
theorem B1771043 : Blo 1770086 1771043 := bstep (se 1 (by rfl) ⟨1328282, by rfl⟩ : syracuseStep 1771043 = 2656565) B2656565
theorem B1771059 : Blo 1770086 1771059 := bstep (se 1 (by rfl) ⟨1328294, by rfl⟩ : syracuseStep 1771059 = 2656589) B2656589
theorem B2655809 : Blo 1770086 2655809 := bstep (se 2 (by rfl) ⟨995928, by rfl⟩ : syracuseStep 2655809 = 1991857) B1991857
theorem B1771075 : Blo 1770086 1771075 := bstep (se 1 (by rfl) ⟨1328306, by rfl⟩ : syracuseStep 1771075 = 2656613) B2656613
theorem B4482641 : Blo 1770086 4482641 := bstep (se 2 (by rfl) ⟨1680990, by rfl⟩ : syracuseStep 4482641 = 3361981) B3361981
theorem B2655827 : Blo 1770086 2655827 := bstep (se 1 (by rfl) ⟨1991870, by rfl⟩ : syracuseStep 2655827 = 3983741) B3983741
theorem B1771091 : Blo 1770086 1771091 := bstep (se 1 (by rfl) ⟨1328318, by rfl⟩ : syracuseStep 1771091 = 2656637) B2656637
theorem B1771107 : Blo 1770086 1771107 := bstep (se 1 (by rfl) ⟨1328330, by rfl⟩ : syracuseStep 1771107 = 2656661) B2656661
theorem B14362211 : Blo 1770086 14362211 := bstep (se 1 (by rfl) ⟨10771658, by rfl⟩ : syracuseStep 14362211 = 21543317) B21543317
theorem B2655857 : Blo 1770086 2655857 := bstep (se 2 (by rfl) ⟨995946, by rfl⟩ : syracuseStep 2655857 = 1991893) B1991893
theorem B1992307 : Blo 1770086 1992307 := bstep (se 1 (by rfl) ⟨1494230, by rfl⟩ : syracuseStep 1992307 = 2988461) B2988461
theorem B1771123 : Blo 1770086 1771123 := bstep (se 1 (by rfl) ⟨1328342, by rfl⟩ : syracuseStep 1771123 = 2656685) B2656685
theorem B2655875 : Blo 1770086 2655875 := bstep (se 1 (by rfl) ⟨1991906, by rfl⟩ : syracuseStep 2655875 = 3983813) B3983813
theorem B1771139 : Blo 1770086 1771139 := bstep (se 1 (by rfl) ⟨1328354, by rfl⟩ : syracuseStep 1771139 = 2656709) B2656709
theorem B1771155 : Blo 1770086 1771155 := bstep (se 1 (by rfl) ⟨1328366, by rfl⟩ : syracuseStep 1771155 = 2656733) B2656733
theorem B2655905 : Blo 1770086 2655905 := bstep (se 2 (by rfl) ⟨995964, by rfl⟩ : syracuseStep 2655905 = 1991929) B1991929
theorem B1771171 : Blo 1770086 1771171 := bstep (se 1 (by rfl) ⟨1328378, by rfl⟩ : syracuseStep 1771171 = 2656757) B2656757
theorem B2393777 : Blo 1770086 2393777 := bstep (se 2 (by rfl) ⟨897666, by rfl⟩ : syracuseStep 2393777 = 1795333) B1795333
theorem B2655923 : Blo 1770086 2655923 := bstep (se 1 (by rfl) ⟨1991942, by rfl⟩ : syracuseStep 2655923 = 3983885) B3983885
theorem B1771187 : Blo 1770086 1771187 := bstep (se 1 (by rfl) ⟨1328390, by rfl⟩ : syracuseStep 1771187 = 2656781) B2656781
theorem B1771203 : Blo 1770086 1771203 := bstep (se 1 (by rfl) ⟨1328402, by rfl⟩ : syracuseStep 1771203 = 2656805) B2656805
theorem B3983057 : Blo 1770086 3983057 := bstep (se 2 (by rfl) ⟨1493646, by rfl⟩ : syracuseStep 3983057 = 2987293) B2987293
theorem B2655953 : Blo 1770086 2655953 := bstep (se 2 (by rfl) ⟨995982, by rfl⟩ : syracuseStep 2655953 = 1991965) B1991965
theorem B1771219 : Blo 1770086 1771219 := bstep (se 1 (by rfl) ⟨1328414, by rfl⟩ : syracuseStep 1771219 = 2656829) B2656829
theorem B3983075 : Blo 1770086 3983075 := bstep (se 1 (by rfl) ⟨2987306, by rfl⟩ : syracuseStep 3983075 = 5974613) B5974613
theorem B2655971 : Blo 1770086 2655971 := bstep (se 1 (by rfl) ⟨1991978, by rfl⟩ : syracuseStep 2655971 = 3983957) B3983957
theorem B1771235 : Blo 1770086 1771235 := bstep (se 1 (by rfl) ⟨1328426, by rfl⟩ : syracuseStep 1771235 = 2656853) B2656853
theorem B1771251 : Blo 1770086 1771251 := bstep (se 1 (by rfl) ⟨1328438, by rfl⟩ : syracuseStep 1771251 = 2656877) B2656877
theorem B2656001 : Blo 1770086 2656001 := bstep (se 2 (by rfl) ⟨996000, by rfl⟩ : syracuseStep 2656001 = 1992001) B1992001
theorem B1992451 : Blo 1770086 1992451 := bstep (se 1 (by rfl) ⟨1494338, by rfl⟩ : syracuseStep 1992451 = 2988677) B2988677
theorem B1771267 : Blo 1770086 1771267 := bstep (se 1 (by rfl) ⟨1328450, by rfl⟩ : syracuseStep 1771267 = 2656901) B2656901
theorem B2836243 : Blo 1770086 2836243 := bstep (se 1 (by rfl) ⟨2127182, by rfl⟩ : syracuseStep 2836243 = 4254365) B4254365
theorem B2656019 : Blo 1770086 2656019 := bstep (se 1 (by rfl) ⟨1992014, by rfl⟩ : syracuseStep 2656019 = 3984029) B3984029
theorem B2393875 : Blo 1770086 2393875 := bstep (se 1 (by rfl) ⟨1795406, by rfl⟩ : syracuseStep 2393875 = 3590813) B3590813
theorem B1771283 : Blo 1770086 1771283 := bstep (se 1 (by rfl) ⟨1328462, by rfl⟩ : syracuseStep 1771283 = 2656925) B2656925
theorem B1771299 : Blo 1770086 1771299 := bstep (se 1 (by rfl) ⟨1328474, by rfl⟩ : syracuseStep 1771299 = 2656949) B2656949
theorem B2656049 : Blo 1770086 2656049 := bstep (se 2 (by rfl) ⟨996018, by rfl⟩ : syracuseStep 2656049 = 1992037) B1992037
theorem B1771315 : Blo 1770086 1771315 := bstep (se 1 (by rfl) ⟨1328486, by rfl⟩ : syracuseStep 1771315 = 2656973) B2656973
theorem B2656067 : Blo 1770086 2656067 := bstep (se 1 (by rfl) ⟨1992050, by rfl⟩ : syracuseStep 2656067 = 3984101) B3984101
theorem B1771331 : Blo 1770086 1771331 := bstep (se 1 (by rfl) ⟨1328498, by rfl⟩ : syracuseStep 1771331 = 2656997) B2656997
theorem B1771347 : Blo 1770086 1771347 := bstep (se 1 (by rfl) ⟨1328510, by rfl⟩ : syracuseStep 1771347 = 2657021) B2657021
theorem B2656097 : Blo 1770086 2656097 := bstep (se 2 (by rfl) ⟨996036, by rfl⟩ : syracuseStep 2656097 = 1992073) B1992073
theorem B1771363 : Blo 1770086 1771363 := bstep (se 1 (by rfl) ⟨1328522, by rfl⟩ : syracuseStep 1771363 = 2657045) B2657045
theorem B7669603 : Blo 1770086 7669603 := bstep (se 1 (by rfl) ⟨5752202, by rfl⟩ : syracuseStep 7669603 = 11504405) B11504405
theorem B2656115 : Blo 1770086 2656115 := bstep (se 1 (by rfl) ⟨1992086, by rfl⟩ : syracuseStep 2656115 = 3984173) B3984173
theorem B1771379 : Blo 1770086 1771379 := bstep (se 1 (by rfl) ⟨1328534, by rfl⟩ : syracuseStep 1771379 = 2657069) B2657069
theorem B1771395 : Blo 1770086 1771395 := bstep (se 1 (by rfl) ⟨1328546, by rfl⟩ : syracuseStep 1771395 = 2657093) B2657093
theorem B2656145 : Blo 1770086 2656145 := bstep (se 2 (by rfl) ⟨996054, by rfl⟩ : syracuseStep 2656145 = 1992109) B1992109
theorem B1992595 : Blo 1770086 1992595 := bstep (se 1 (by rfl) ⟨1494446, by rfl⟩ : syracuseStep 1992595 = 2988893) B2988893
theorem B1771411 : Blo 1770086 1771411 := bstep (se 1 (by rfl) ⟨1328558, by rfl⟩ : syracuseStep 1771411 = 2657117) B2657117
theorem B2656163 : Blo 1770086 2656163 := bstep (se 1 (by rfl) ⟨1992122, by rfl⟩ : syracuseStep 2656163 = 3984245) B3984245
theorem B1771427 : Blo 1770086 1771427 := bstep (se 1 (by rfl) ⟨1328570, by rfl⟩ : syracuseStep 1771427 = 2657141) B2657141
theorem B1771443 : Blo 1770086 1771443 := bstep (se 1 (by rfl) ⟨1328582, by rfl⟩ : syracuseStep 1771443 = 2657165) B2657165
theorem B2656193 : Blo 1770086 2656193 := bstep (se 2 (by rfl) ⟨996072, by rfl⟩ : syracuseStep 2656193 = 1992145) B1992145
theorem B1771459 : Blo 1770086 1771459 := bstep (se 1 (by rfl) ⟨1328594, by rfl⟩ : syracuseStep 1771459 = 2657189) B2657189
theorem B2656211 : Blo 1770086 2656211 := bstep (se 1 (by rfl) ⟨1992158, by rfl⟩ : syracuseStep 2656211 = 3984317) B3984317
theorem B1771475 : Blo 1770086 1771475 := bstep (se 1 (by rfl) ⟨1328606, by rfl⟩ : syracuseStep 1771475 = 2657213) B2657213
theorem B1771491 : Blo 1770086 1771491 := bstep (se 1 (by rfl) ⟨1328618, by rfl⟩ : syracuseStep 1771491 = 2657237) B2657237
theorem B4253681 : Blo 1770086 4253681 := bstep (se 2 (by rfl) ⟨1595130, by rfl⟩ : syracuseStep 4253681 = 3190261) B3190261
theorem B3983345 : Blo 1770086 3983345 := bstep (se 2 (by rfl) ⟨1493754, by rfl⟩ : syracuseStep 3983345 = 2987509) B2987509
theorem B2656241 : Blo 1770086 2656241 := bstep (se 2 (by rfl) ⟨996090, by rfl⟩ : syracuseStep 2656241 = 1992181) B1992181
theorem B1771507 : Blo 1770086 1771507 := bstep (se 1 (by rfl) ⟨1328630, by rfl⟩ : syracuseStep 1771507 = 2657261) B2657261
theorem B3983363 : Blo 1770086 3983363 := bstep (se 1 (by rfl) ⟨2987522, by rfl⟩ : syracuseStep 3983363 = 5975045) B5975045
theorem B2656259 : Blo 1770086 2656259 := bstep (se 1 (by rfl) ⟨1992194, by rfl⟩ : syracuseStep 2656259 = 3984389) B3984389
theorem B3590147 : Blo 1770086 3590147 := bstep (se 1 (by rfl) ⟨2692610, by rfl⟩ : syracuseStep 3590147 = 5385221) B5385221
theorem B1771523 : Blo 1770086 1771523 := bstep (se 1 (by rfl) ⟨1328642, by rfl⟩ : syracuseStep 1771523 = 2657285) B2657285
theorem B1771539 : Blo 1770086 1771539 := bstep (se 1 (by rfl) ⟨1328654, by rfl⟩ : syracuseStep 1771539 = 2657309) B2657309
theorem B2656289 : Blo 1770086 2656289 := bstep (se 2 (by rfl) ⟨996108, by rfl⟩ : syracuseStep 2656289 = 1992217) B1992217
theorem B1992739 : Blo 1770086 1992739 := bstep (se 1 (by rfl) ⟨1494554, by rfl⟩ : syracuseStep 1992739 = 2989109) B2989109
theorem B1771555 : Blo 1770086 1771555 := bstep (se 1 (by rfl) ⟨1328666, by rfl⟩ : syracuseStep 1771555 = 2657333) B2657333
theorem B2656307 : Blo 1770086 2656307 := bstep (se 1 (by rfl) ⟨1992230, by rfl⟩ : syracuseStep 2656307 = 3984461) B3984461
theorem B1771571 : Blo 1770086 1771571 := bstep (se 1 (by rfl) ⟨1328678, by rfl⟩ : syracuseStep 1771571 = 2657357) B2657357
theorem B1771587 : Blo 1770086 1771587 := bstep (se 1 (by rfl) ⟨1328690, by rfl⟩ : syracuseStep 1771587 = 2657381) B2657381
theorem B13445189 : Blo 1770086 13445189 := bstep (se 4 (by rfl) ⟨1260486, by rfl⟩ : syracuseStep 13445189 = 2520973) B2520973
theorem B2656337 : Blo 1770086 2656337 := bstep (se 2 (by rfl) ⟨996126, by rfl⟩ : syracuseStep 2656337 = 1992253) B1992253
theorem B1771603 : Blo 1770086 1771603 := bstep (se 1 (by rfl) ⟨1328702, by rfl⟩ : syracuseStep 1771603 = 2657405) B2657405
theorem B2656355 : Blo 1770086 2656355 := bstep (se 1 (by rfl) ⟨1992266, by rfl⟩ : syracuseStep 2656355 = 3984533) B3984533
theorem B1771619 : Blo 1770086 1771619 := bstep (se 1 (by rfl) ⟨1328714, by rfl⟩ : syracuseStep 1771619 = 2657429) B2657429
theorem B30673009 : Blo 1770086 30673009 := bstep (se 2 (by rfl) ⟨11502378, by rfl⟩ : syracuseStep 30673009 = 23004757) B23004757
theorem B1771635 : Blo 1770086 1771635 := bstep (se 1 (by rfl) ⟨1328726, by rfl⟩ : syracuseStep 1771635 = 2657453) B2657453
theorem B2656385 : Blo 1770086 2656385 := bstep (se 2 (by rfl) ⟨996144, by rfl⟩ : syracuseStep 2656385 = 1992289) B1992289
theorem B1771651 : Blo 1770086 1771651 := bstep (se 1 (by rfl) ⟨1328738, by rfl⟩ : syracuseStep 1771651 = 2657477) B2657477
theorem B16148621 : Blo 1770086 16148621 := bstep (se 3 (by rfl) ⟨3027866, by rfl⟩ : syracuseStep 16148621 = 6055733) B6055733
theorem B4040849 : Blo 1770086 4040849 := bstep (se 2 (by rfl) ⟨1515318, by rfl⟩ : syracuseStep 4040849 = 3030637) B3030637
theorem B2656403 : Blo 1770086 2656403 := bstep (se 1 (by rfl) ⟨1992302, by rfl⟩ : syracuseStep 2656403 = 3984605) B3984605
theorem B1771667 : Blo 1770086 1771667 := bstep (se 1 (by rfl) ⟨1328750, by rfl⟩ : syracuseStep 1771667 = 2657501) B2657501
theorem B1771683 : Blo 1770086 1771683 := bstep (se 1 (by rfl) ⟨1328762, by rfl⟩ : syracuseStep 1771683 = 2657525) B2657525
theorem B2656433 : Blo 1770086 2656433 := bstep (se 2 (by rfl) ⟨996162, by rfl⟩ : syracuseStep 2656433 = 1992325) B1992325
theorem B1992883 : Blo 1770086 1992883 := bstep (se 1 (by rfl) ⟨1494662, by rfl⟩ : syracuseStep 1992883 = 2989325) B2989325
theorem B1771699 : Blo 1770086 1771699 := bstep (se 1 (by rfl) ⟨1328774, by rfl⟩ : syracuseStep 1771699 = 2657549) B2657549
theorem B2656451 : Blo 1770086 2656451 := bstep (se 1 (by rfl) ⟨1992338, by rfl⟩ : syracuseStep 2656451 = 3984677) B3984677
theorem B1771715 : Blo 1770086 1771715 := bstep (se 1 (by rfl) ⟨1328786, by rfl⟩ : syracuseStep 1771715 = 2657573) B2657573
theorem B10086605 : Blo 1770086 10086605 := bstep (se 3 (by rfl) ⟨1891238, by rfl⟩ : syracuseStep 10086605 = 3782477) B3782477
theorem B1771731 : Blo 1770086 1771731 := bstep (se 1 (by rfl) ⟨1328798, by rfl⟩ : syracuseStep 1771731 = 2657597) B2657597
theorem B2656481 : Blo 1770086 2656481 := bstep (se 2 (by rfl) ⟨996180, by rfl⟩ : syracuseStep 2656481 = 1992361) B1992361
theorem B1771747 : Blo 1770086 1771747 := bstep (se 1 (by rfl) ⟨1328810, by rfl⟩ : syracuseStep 1771747 = 2657621) B2657621
theorem B3361009 : Blo 1770086 3361009 := bstep (se 2 (by rfl) ⟨1260378, by rfl⟩ : syracuseStep 3361009 = 2520757) B2520757
theorem B2656499 : Blo 1770086 2656499 := bstep (se 1 (by rfl) ⟨1992374, by rfl⟩ : syracuseStep 2656499 = 3984749) B3984749
theorem B1771763 : Blo 1770086 1771763 := bstep (se 1 (by rfl) ⟨1328822, by rfl⟩ : syracuseStep 1771763 = 2657645) B2657645
theorem B1771779 : Blo 1770086 1771779 := bstep (se 1 (by rfl) ⟨1328834, by rfl⟩ : syracuseStep 1771779 = 2657669) B2657669
theorem B5974289 : Blo 1770086 5974289 := bstep (se 2 (by rfl) ⟨2240358, by rfl⟩ : syracuseStep 5974289 = 4480717) B4480717
theorem B3983633 : Blo 1770086 3983633 := bstep (se 2 (by rfl) ⟨1493862, by rfl⟩ : syracuseStep 3983633 = 2987725) B2987725
theorem B2656529 : Blo 1770086 2656529 := bstep (se 2 (by rfl) ⟨996198, by rfl⟩ : syracuseStep 2656529 = 1992397) B1992397
theorem B1771795 : Blo 1770086 1771795 := bstep (se 1 (by rfl) ⟨1328846, by rfl⟩ : syracuseStep 1771795 = 2657693) B2657693
theorem B3983651 : Blo 1770086 3983651 := bstep (se 1 (by rfl) ⟨2987738, by rfl⟩ : syracuseStep 3983651 = 5975477) B5975477
theorem B2656547 : Blo 1770086 2656547 := bstep (se 1 (by rfl) ⟨1992410, by rfl⟩ : syracuseStep 2656547 = 3984821) B3984821
theorem B1771811 : Blo 1770086 1771811 := bstep (se 1 (by rfl) ⟨1328858, by rfl⟩ : syracuseStep 1771811 = 2657717) B2657717
theorem B2836787 : Blo 1770086 2836787 := bstep (se 1 (by rfl) ⟨2127590, by rfl⟩ : syracuseStep 2836787 = 4255181) B4255181
theorem B1771827 : Blo 1770086 1771827 := bstep (se 1 (by rfl) ⟨1328870, by rfl⟩ : syracuseStep 1771827 = 2657741) B2657741
theorem B2656577 : Blo 1770086 2656577 := bstep (se 2 (by rfl) ⟨996216, by rfl⟩ : syracuseStep 2656577 = 1992433) B1992433
theorem B1993027 : Blo 1770086 1993027 := bstep (se 1 (by rfl) ⟨1494770, by rfl⟩ : syracuseStep 1993027 = 2989541) B2989541
theorem B1771843 : Blo 1770086 1771843 := bstep (se 1 (by rfl) ⟨1328882, by rfl⟩ : syracuseStep 1771843 = 2657765) B2657765
theorem B2656595 : Blo 1770086 2656595 := bstep (se 1 (by rfl) ⟨1992446, by rfl⟩ : syracuseStep 2656595 = 3984893) B3984893
theorem B1771859 : Blo 1770086 1771859 := bstep (se 1 (by rfl) ⟨1328894, by rfl⟩ : syracuseStep 1771859 = 2657789) B2657789
theorem B1771875 : Blo 1770086 1771875 := bstep (se 1 (by rfl) ⟨1328906, by rfl⟩ : syracuseStep 1771875 = 2657813) B2657813
theorem B2656625 : Blo 1770086 2656625 := bstep (se 2 (by rfl) ⟨996234, by rfl⟩ : syracuseStep 2656625 = 1992469) B1992469
theorem B1771891 : Blo 1770086 1771891 := bstep (se 1 (by rfl) ⟨1328918, by rfl⟩ : syracuseStep 1771891 = 2657837) B2657837
theorem B2656643 : Blo 1770086 2656643 := bstep (se 1 (by rfl) ⟨1992482, by rfl⟩ : syracuseStep 2656643 = 3984965) B3984965
theorem B1771907 : Blo 1770086 1771907 := bstep (se 1 (by rfl) ⟨1328930, by rfl⟩ : syracuseStep 1771907 = 2657861) B2657861
theorem B40905101 : Blo 1770086 40905101 := bstep (se 3 (by rfl) ⟨7669706, by rfl⟩ : syracuseStep 40905101 = 15339413) B15339413
theorem B3361169 : Blo 1770086 3361169 := bstep (se 2 (by rfl) ⟨1260438, by rfl⟩ : syracuseStep 3361169 = 2520877) B2520877
theorem B1771923 : Blo 1770086 1771923 := bstep (se 1 (by rfl) ⟨1328942, by rfl⟩ : syracuseStep 1771923 = 2657885) B2657885
theorem B2656673 : Blo 1770086 2656673 := bstep (se 2 (by rfl) ⟨996252, by rfl⟩ : syracuseStep 2656673 = 1992505) B1992505
theorem B9087395 : Blo 1770086 9087395 := bstep (se 1 (by rfl) ⟨6815546, by rfl⟩ : syracuseStep 9087395 = 13631093) B13631093
theorem B1771939 : Blo 1770086 1771939 := bstep (se 1 (by rfl) ⟨1328954, by rfl⟩ : syracuseStep 1771939 = 2657909) B2657909
theorem B2656691 : Blo 1770086 2656691 := bstep (se 1 (by rfl) ⟨1992518, by rfl⟩ : syracuseStep 2656691 = 3985037) B3985037
theorem B1771955 : Blo 1770086 1771955 := bstep (se 1 (by rfl) ⟨1328966, by rfl⟩ : syracuseStep 1771955 = 2657933) B2657933
theorem B1771971 : Blo 1770086 1771971 := bstep (se 1 (by rfl) ⟨1328978, by rfl⟩ : syracuseStep 1771971 = 2657957) B2657957
theorem B7563725 : Blo 1770086 7563725 := bstep (se 3 (by rfl) ⟨1418198, by rfl⟩ : syracuseStep 7563725 = 2836397) B2836397
theorem B2656721 : Blo 1770086 2656721 := bstep (se 2 (by rfl) ⟨996270, by rfl⟩ : syracuseStep 2656721 = 1992541) B1992541
theorem B1993171 : Blo 1770086 1993171 := bstep (se 1 (by rfl) ⟨1494878, by rfl⟩ : syracuseStep 1993171 = 2989757) B2989757
theorem B1771987 : Blo 1770086 1771987 := bstep (se 1 (by rfl) ⟨1328990, by rfl⟩ : syracuseStep 1771987 = 2657981) B2657981
theorem B2836961 : Blo 1770086 2836961 := bstep (se 2 (by rfl) ⟨1063860, by rfl⟩ : syracuseStep 2836961 = 2127721) B2127721
theorem B2656739 : Blo 1770086 2656739 := bstep (se 1 (by rfl) ⟨1992554, by rfl⟩ : syracuseStep 2656739 = 3985109) B3985109
theorem B1772003 : Blo 1770086 1772003 := bstep (se 1 (by rfl) ⟨1329002, by rfl⟩ : syracuseStep 1772003 = 2658005) B2658005
theorem B5040625 : Blo 1770086 5040625 := bstep (se 2 (by rfl) ⟨1890234, by rfl⟩ : syracuseStep 5040625 = 3780469) B3780469
theorem B8964593 : Blo 1770086 8964593 := bstep (se 2 (by rfl) ⟨3361722, by rfl⟩ : syracuseStep 8964593 = 6723445) B6723445
theorem B1772019 : Blo 1770086 1772019 := bstep (se 1 (by rfl) ⟨1329014, by rfl⟩ : syracuseStep 1772019 = 2658029) B2658029
theorem B2656769 : Blo 1770086 2656769 := bstep (se 2 (by rfl) ⟨996288, by rfl⟩ : syracuseStep 2656769 = 1992577) B1992577
theorem B4254211 : Blo 1770086 4254211 := bstep (se 1 (by rfl) ⟨3190658, by rfl⟩ : syracuseStep 4254211 = 6381317) B6381317
theorem B3590659 : Blo 1770086 3590659 := bstep (se 1 (by rfl) ⟨2692994, by rfl⟩ : syracuseStep 3590659 = 5385989) B5385989
theorem B1772035 : Blo 1770086 1772035 := bstep (se 1 (by rfl) ⟨1329026, by rfl⟩ : syracuseStep 1772035 = 2658053) B2658053
theorem B2656787 : Blo 1770086 2656787 := bstep (se 1 (by rfl) ⟨1992590, by rfl⟩ : syracuseStep 2656787 = 3985181) B3985181
theorem B1772051 : Blo 1770086 1772051 := bstep (se 1 (by rfl) ⟨1329038, by rfl⟩ : syracuseStep 1772051 = 2658077) B2658077
theorem B1772067 : Blo 1770086 1772067 := bstep (se 1 (by rfl) ⟨1329050, by rfl⟩ : syracuseStep 1772067 = 2658101) B2658101
theorem B3983921 : Blo 1770086 3983921 := bstep (se 2 (by rfl) ⟨1493970, by rfl⟩ : syracuseStep 3983921 = 2987941) B2987941
theorem B2656817 : Blo 1770086 2656817 := bstep (se 2 (by rfl) ⟨996306, by rfl⟩ : syracuseStep 2656817 = 1992613) B1992613
theorem B4483633 : Blo 1770086 4483633 := bstep (se 2 (by rfl) ⟨1681362, by rfl⟩ : syracuseStep 4483633 = 3362725) B3362725
theorem B1772083 : Blo 1770086 1772083 := bstep (se 1 (by rfl) ⟨1329062, by rfl⟩ : syracuseStep 1772083 = 2658125) B2658125
theorem B3983939 : Blo 1770086 3983939 := bstep (se 1 (by rfl) ⟨2987954, by rfl⟩ : syracuseStep 3983939 = 5975909) B5975909
theorem B2656835 : Blo 1770086 2656835 := bstep (se 1 (by rfl) ⟨1992626, by rfl⟩ : syracuseStep 2656835 = 3985253) B3985253
theorem B2656865 : Blo 1770086 2656865 := bstep (se 2 (by rfl) ⟨996324, by rfl⟩ : syracuseStep 2656865 = 1992649) B1992649
theorem B1993315 : Blo 1770086 1993315 := bstep (se 1 (by rfl) ⟨1494986, by rfl⟩ : syracuseStep 1993315 = 2989973) B2989973
theorem B6728291 : Blo 1770086 6728291 := bstep (se 1 (by rfl) ⟨5046218, by rfl⟩ : syracuseStep 6728291 = 10092437) B10092437
theorem B13453937 : Blo 1770086 13453937 := bstep (se 2 (by rfl) ⟨5045226, by rfl⟩ : syracuseStep 13453937 = 10090453) B10090453
theorem B6728305 : Blo 1770086 6728305 := bstep (se 2 (by rfl) ⟨2523114, by rfl⟩ : syracuseStep 6728305 = 5046229) B5046229
theorem B2656883 : Blo 1770086 2656883 := bstep (se 1 (by rfl) ⟨1992662, by rfl⟩ : syracuseStep 2656883 = 3985325) B3985325
theorem B5040785 : Blo 1770086 5040785 := bstep (se 2 (by rfl) ⟨1890294, by rfl⟩ : syracuseStep 5040785 = 3780589) B3780589
theorem B2656913 : Blo 1770086 2656913 := bstep (se 2 (by rfl) ⟨996342, by rfl⟩ : syracuseStep 2656913 = 1992685) B1992685
theorem B2656931 : Blo 1770086 2656931 := bstep (se 1 (by rfl) ⟨1992698, by rfl⟩ : syracuseStep 2656931 = 3985397) B3985397
theorem B2656961 : Blo 1770086 2656961 := bstep (se 2 (by rfl) ⟨996360, by rfl⟩ : syracuseStep 2656961 = 1992721) B1992721
theorem B2656979 : Blo 1770086 2656979 := bstep (se 1 (by rfl) ⟨1992734, by rfl⟩ : syracuseStep 2656979 = 3985469) B3985469
theorem B2657009 : Blo 1770086 2657009 := bstep (se 2 (by rfl) ⟨996378, by rfl⟩ : syracuseStep 2657009 = 1992757) B1992757
theorem B1993459 : Blo 1770086 1993459 := bstep (se 1 (by rfl) ⟨1495094, by rfl⟩ : syracuseStep 1993459 = 2990189) B2990189
theorem B5040899 : Blo 1770086 5040899 := bstep (se 1 (by rfl) ⟨3780674, by rfl⟩ : syracuseStep 5040899 = 7561349) B7561349
theorem B2657027 : Blo 1770086 2657027 := bstep (se 1 (by rfl) ⟨1992770, by rfl⟩ : syracuseStep 2657027 = 3985541) B3985541
theorem B2657057 : Blo 1770086 2657057 := bstep (se 2 (by rfl) ⟨996396, by rfl⟩ : syracuseStep 2657057 = 1992793) B1992793
theorem B3361571 : Blo 1770086 3361571 := bstep (se 1 (by rfl) ⟨2521178, by rfl⟩ : syracuseStep 3361571 = 5042357) B5042357
theorem B5974829 : Blo 1770086 5974829 := bstep (se 3 (by rfl) ⟨1120280, by rfl⟩ : syracuseStep 5974829 = 2240561) B2240561
theorem B2657075 : Blo 1770086 2657075 := bstep (se 1 (by rfl) ⟨1992806, by rfl⟩ : syracuseStep 2657075 = 3985613) B3985613
theorem B4483907 : Blo 1770086 4483907 := bstep (se 1 (by rfl) ⟨3362930, by rfl⟩ : syracuseStep 4483907 = 6725861) B6725861
theorem B3984209 : Blo 1770086 3984209 := bstep (se 2 (by rfl) ⟨1494078, by rfl⟩ : syracuseStep 3984209 = 2988157) B2988157
theorem B2657105 : Blo 1770086 2657105 := bstep (se 2 (by rfl) ⟨996414, by rfl⟩ : syracuseStep 2657105 = 1992829) B1992829
theorem B5974883 : Blo 1770086 5974883 := bstep (se 1 (by rfl) ⟨4481162, by rfl⟩ : syracuseStep 5974883 = 8962325) B8962325
theorem B3984227 : Blo 1770086 3984227 := bstep (se 1 (by rfl) ⟨2988170, by rfl⟩ : syracuseStep 3984227 = 5976341) B5976341
theorem B2657123 : Blo 1770086 2657123 := bstep (se 1 (by rfl) ⟨1992842, by rfl⟩ : syracuseStep 2657123 = 3985685) B3985685
theorem B2657153 : Blo 1770086 2657153 := bstep (se 2 (by rfl) ⟨996432, by rfl⟩ : syracuseStep 2657153 = 1992865) B1992865
theorem B2657171 : Blo 1770086 2657171 := bstep (se 1 (by rfl) ⟨1992878, by rfl⟩ : syracuseStep 2657171 = 3985757) B3985757
theorem B2657201 : Blo 1770086 2657201 := bstep (se 2 (by rfl) ⟨996450, by rfl⟩ : syracuseStep 2657201 = 1992901) B1992901
theorem B2657219 : Blo 1770086 2657219 := bstep (se 1 (by rfl) ⟨1992914, by rfl⟩ : syracuseStep 2657219 = 3985829) B3985829
theorem B30272453 : Blo 1770086 30272453 := bstep (se 4 (by rfl) ⟨2838042, by rfl⟩ : syracuseStep 30272453 = 5676085) B5676085
theorem B2657249 : Blo 1770086 2657249 := bstep (se 2 (by rfl) ⟨996468, by rfl⟩ : syracuseStep 2657249 = 1992937) B1992937
theorem B2657267 : Blo 1770086 2657267 := bstep (se 1 (by rfl) ⟨1992950, by rfl⟩ : syracuseStep 2657267 = 3985901) B3985901
theorem B4484099 : Blo 1770086 4484099 := bstep (se 1 (by rfl) ⟨3363074, by rfl⟩ : syracuseStep 4484099 = 6726149) B6726149
theorem B2657297 : Blo 1770086 2657297 := bstep (se 2 (by rfl) ⟨996486, by rfl⟩ : syracuseStep 2657297 = 1992973) B1992973
theorem B2657315 : Blo 1770086 2657315 := bstep (se 1 (by rfl) ⟨1992986, by rfl⟩ : syracuseStep 2657315 = 3985973) B3985973
theorem B2657345 : Blo 1770086 2657345 := bstep (se 2 (by rfl) ⟨996504, by rfl⟩ : syracuseStep 2657345 = 1993009) B1993009
theorem B2657363 : Blo 1770086 2657363 := bstep (se 1 (by rfl) ⟨1993022, by rfl⟩ : syracuseStep 2657363 = 3986045) B3986045
theorem B6057059 : Blo 1770086 6057059 := bstep (se 1 (by rfl) ⟨4542794, by rfl⟩ : syracuseStep 6057059 = 9085589) B9085589
theorem B5975153 : Blo 1770086 5975153 := bstep (se 2 (by rfl) ⟨2240682, by rfl⟩ : syracuseStep 5975153 = 4481365) B4481365
theorem B3984497 : Blo 1770086 3984497 := bstep (se 2 (by rfl) ⟨1494186, by rfl⟩ : syracuseStep 3984497 = 2988373) B2988373
theorem B10087537 : Blo 1770086 10087537 := bstep (se 2 (by rfl) ⟨3782826, by rfl⟩ : syracuseStep 10087537 = 7565653) B7565653
theorem B8629361 : Blo 1770086 8629361 := bstep (se 2 (by rfl) ⟨3236010, by rfl⟩ : syracuseStep 8629361 = 6472021) B6472021
theorem B2657393 : Blo 1770086 2657393 := bstep (se 2 (by rfl) ⟨996522, by rfl⟩ : syracuseStep 2657393 = 1993045) B1993045
theorem B3984515 : Blo 1770086 3984515 := bstep (se 1 (by rfl) ⟨2988386, by rfl⟩ : syracuseStep 3984515 = 5976773) B5976773
theorem B2657411 : Blo 1770086 2657411 := bstep (se 1 (by rfl) ⟨1993058, by rfl⟩ : syracuseStep 2657411 = 3986117) B3986117
theorem B9579653 : Blo 1770086 9579653 := bstep (se 4 (by rfl) ⟨898092, by rfl⟩ : syracuseStep 9579653 = 1796185) B1796185
theorem B2657441 : Blo 1770086 2657441 := bstep (se 2 (by rfl) ⟨996540, by rfl⟩ : syracuseStep 2657441 = 1993081) B1993081
theorem B2657459 : Blo 1770086 2657459 := bstep (se 1 (by rfl) ⟨1993094, by rfl⟩ : syracuseStep 2657459 = 3986189) B3986189
theorem B2657489 : Blo 1770086 2657489 := bstep (se 2 (by rfl) ⟨996558, by rfl⟩ : syracuseStep 2657489 = 1993117) B1993117
theorem B2657507 : Blo 1770086 2657507 := bstep (se 1 (by rfl) ⟨1993130, by rfl⟩ : syracuseStep 2657507 = 3986261) B3986261
theorem B2657537 : Blo 1770086 2657537 := bstep (se 2 (by rfl) ⟨996576, by rfl⟩ : syracuseStep 2657537 = 1993153) B1993153
theorem B2657555 : Blo 1770086 2657555 := bstep (se 1 (by rfl) ⟨1993166, by rfl⟩ : syracuseStep 2657555 = 3986333) B3986333
theorem B6720803 : Blo 1770086 6720803 := bstep (se 1 (by rfl) ⟨5040602, by rfl⟩ : syracuseStep 6720803 = 10081205) B10081205
theorem B2657585 : Blo 1770086 2657585 := bstep (se 2 (by rfl) ⟨996594, by rfl⟩ : syracuseStep 2657585 = 1993189) B1993189
theorem B2657603 : Blo 1770086 2657603 := bstep (se 1 (by rfl) ⟨1993202, by rfl⟩ : syracuseStep 2657603 = 3986405) B3986405
theorem B2657633 : Blo 1770086 2657633 := bstep (se 2 (by rfl) ⟨996612, by rfl⟩ : syracuseStep 2657633 = 1993225) B1993225
theorem B2657651 : Blo 1770086 2657651 := bstep (se 1 (by rfl) ⟨1993238, by rfl⟩ : syracuseStep 2657651 = 3986477) B3986477
theorem B3984785 : Blo 1770086 3984785 := bstep (se 2 (by rfl) ⟨1494294, by rfl⟩ : syracuseStep 3984785 = 2988589) B2988589
theorem B2657681 : Blo 1770086 2657681 := bstep (se 2 (by rfl) ⟨996630, by rfl⟩ : syracuseStep 2657681 = 1993261) B1993261
theorem B3984803 : Blo 1770086 3984803 := bstep (se 1 (by rfl) ⟨2988602, by rfl⟩ : syracuseStep 3984803 = 5977205) B5977205
theorem B2657699 : Blo 1770086 2657699 := bstep (se 1 (by rfl) ⟨1993274, by rfl⟩ : syracuseStep 2657699 = 3986549) B3986549
theorem B2657729 : Blo 1770086 2657729 := bstep (se 2 (by rfl) ⟨996648, by rfl⟩ : syracuseStep 2657729 = 1993297) B1993297
theorem B4541891 : Blo 1770086 4541891 := bstep (se 1 (by rfl) ⟨3406418, by rfl⟩ : syracuseStep 4541891 = 6812837) B6812837
theorem B2657747 : Blo 1770086 2657747 := bstep (se 1 (by rfl) ⟨1993310, by rfl⟩ : syracuseStep 2657747 = 3986621) B3986621
theorem B2657777 : Blo 1770086 2657777 := bstep (se 2 (by rfl) ⟨996666, by rfl⟩ : syracuseStep 2657777 = 1993333) B1993333
theorem B2657795 : Blo 1770086 2657795 := bstep (se 1 (by rfl) ⟨1993346, by rfl⟩ : syracuseStep 2657795 = 3986693) B3986693
theorem B15330829 : Blo 1770086 15330829 := bstep (se 3 (by rfl) ⟨2874530, by rfl⟩ : syracuseStep 15330829 = 5749061) B5749061
theorem B2657825 : Blo 1770086 2657825 := bstep (se 2 (by rfl) ⟨996684, by rfl⟩ : syracuseStep 2657825 = 1993369) B1993369
theorem B2657843 : Blo 1770086 2657843 := bstep (se 1 (by rfl) ⟨1993382, by rfl⟩ : syracuseStep 2657843 = 3986765) B3986765
theorem B2657873 : Blo 1770086 2657873 := bstep (se 2 (by rfl) ⟨996702, by rfl⟩ : syracuseStep 2657873 = 1993405) B1993405
theorem B2657891 : Blo 1770086 2657891 := bstep (se 1 (by rfl) ⟨1993418, by rfl⟩ : syracuseStep 2657891 = 3986837) B3986837
theorem B2657921 : Blo 1770086 2657921 := bstep (se 2 (by rfl) ⟨996720, by rfl⟩ : syracuseStep 2657921 = 1993441) B1993441
theorem B5975693 : Blo 1770086 5975693 := bstep (se 3 (by rfl) ⟨1120442, by rfl⟩ : syracuseStep 5975693 = 2240885) B2240885
theorem B2657939 : Blo 1770086 2657939 := bstep (se 1 (by rfl) ⟨1993454, by rfl⟩ : syracuseStep 2657939 = 3986909) B3986909
theorem B3362467 : Blo 1770086 3362467 := bstep (se 1 (by rfl) ⟨2521850, by rfl⟩ : syracuseStep 3362467 = 5043701) B5043701
theorem B5385901 : Blo 1770086 5385901 := bstep (se 3 (by rfl) ⟨1009856, by rfl⟩ : syracuseStep 5385901 = 2019713) B2019713
theorem B3985073 : Blo 1770086 3985073 := bstep (se 2 (by rfl) ⟨1494402, by rfl⟩ : syracuseStep 3985073 = 2988805) B2988805
theorem B2657969 : Blo 1770086 2657969 := bstep (se 2 (by rfl) ⟨996738, by rfl⟩ : syracuseStep 2657969 = 1993477) B1993477
theorem B5975747 : Blo 1770086 5975747 := bstep (se 1 (by rfl) ⟨4481810, by rfl⟩ : syracuseStep 5975747 = 8963621) B8963621
theorem B3985091 : Blo 1770086 3985091 := bstep (se 1 (by rfl) ⟨2988818, by rfl⟩ : syracuseStep 3985091 = 5977637) B5977637
theorem B2657987 : Blo 1770086 2657987 := bstep (se 1 (by rfl) ⟨1993490, by rfl⟩ : syracuseStep 2657987 = 3986981) B3986981
theorem B2658017 : Blo 1770086 2658017 := bstep (se 2 (by rfl) ⟨996756, by rfl⟩ : syracuseStep 2658017 = 1993513) B1993513
theorem B5041901 : Blo 1770086 5041901 := bstep (se 3 (by rfl) ⟨945356, by rfl⟩ : syracuseStep 5041901 = 1890713) B1890713
theorem B2658035 : Blo 1770086 2658035 := bstep (se 1 (by rfl) ⟨1993526, by rfl⟩ : syracuseStep 2658035 = 3987053) B3987053
theorem B2658065 : Blo 1770086 2658065 := bstep (se 2 (by rfl) ⟨996774, by rfl⟩ : syracuseStep 2658065 = 1993549) B1993549
theorem B2658083 : Blo 1770086 2658083 := bstep (se 1 (by rfl) ⟨1993562, by rfl⟩ : syracuseStep 2658083 = 3987125) B3987125
theorem B3362627 : Blo 1770086 3362627 := bstep (se 1 (by rfl) ⟨2521970, by rfl⟩ : syracuseStep 3362627 = 5043941) B5043941
theorem B2658113 : Blo 1770086 2658113 := bstep (se 2 (by rfl) ⟨996792, by rfl⟩ : syracuseStep 2658113 = 1993585) B1993585
theorem B18173765 : Blo 1770086 18173765 := bstep (se 4 (by rfl) ⟨1703790, by rfl⟩ : syracuseStep 18173765 = 3407581) B3407581
theorem B6057827 : Blo 1770086 6057827 := bstep (se 1 (by rfl) ⟨4543370, by rfl⟩ : syracuseStep 6057827 = 9086741) B9086741
theorem B15126385 : Blo 1770086 15126385 := bstep (se 2 (by rfl) ⟨5672394, by rfl⟩ : syracuseStep 15126385 = 11344789) B11344789
theorem B5042083 : Blo 1770086 5042083 := bstep (se 1 (by rfl) ⟨3781562, by rfl⟩ : syracuseStep 5042083 = 7563125) B7563125
theorem B8966051 : Blo 1770086 8966051 := bstep (se 1 (by rfl) ⟨6724538, by rfl⟩ : syracuseStep 8966051 = 13449077) B13449077
theorem B4485041 : Blo 1770086 4485041 := bstep (se 2 (by rfl) ⟨1681890, by rfl⟩ : syracuseStep 4485041 = 3363781) B3363781
theorem B5976017 : Blo 1770086 5976017 := bstep (se 2 (by rfl) ⟨2241006, by rfl⟩ : syracuseStep 5976017 = 4482013) B4482013
theorem B3985361 : Blo 1770086 3985361 := bstep (se 2 (by rfl) ⟨1494510, by rfl⟩ : syracuseStep 3985361 = 2989021) B2989021
theorem B3985379 : Blo 1770086 3985379 := bstep (se 1 (by rfl) ⟨2989034, by rfl⟩ : syracuseStep 3985379 = 5978069) B5978069
theorem B4485091 : Blo 1770086 4485091 := bstep (se 1 (by rfl) ⟨3363818, by rfl⟩ : syracuseStep 4485091 = 6727637) B6727637
theorem B5042243 : Blo 1770086 5042243 := bstep (se 1 (by rfl) ⟨3781682, by rfl⟩ : syracuseStep 5042243 = 7563365) B7563365
theorem B5673037 : Blo 1770086 5673037 := bstep (se 3 (by rfl) ⟨1063694, by rfl⟩ : syracuseStep 5673037 = 2127389) B2127389
theorem B4485233 : Blo 1770086 4485233 := bstep (se 2 (by rfl) ⟨1681962, by rfl⟩ : syracuseStep 4485233 = 3363925) B3363925
theorem B2240723 : Blo 1770086 2240723 := bstep (se 1 (by rfl) ⟨1680542, by rfl⟩ : syracuseStep 2240723 = 3361085) B3361085
theorem B3985649 : Blo 1770086 3985649 := bstep (se 2 (by rfl) ⟨1494618, by rfl⟩ : syracuseStep 3985649 = 2989237) B2989237
theorem B3985667 : Blo 1770086 3985667 := bstep (se 1 (by rfl) ⟨2989250, by rfl⟩ : syracuseStep 3985667 = 5978501) B5978501
theorem B6721805 : Blo 1770086 6721805 := bstep (se 3 (by rfl) ⟨1260338, by rfl⟩ : syracuseStep 6721805 = 2520677) B2520677
theorem B12767501 : Blo 1770086 12767501 := bstep (se 3 (by rfl) ⟨2393906, by rfl⟩ : syracuseStep 12767501 = 4787813) B4787813
theorem B5386513 : Blo 1770086 5386513 := bstep (se 2 (by rfl) ⟨2019942, by rfl⟩ : syracuseStep 5386513 = 4039885) B4039885
theorem B4788497 : Blo 1770086 4788497 := bstep (se 2 (by rfl) ⟨1795686, by rfl⟩ : syracuseStep 4788497 = 3591373) B3591373
theorem B3780913 : Blo 1770086 3780913 := bstep (se 2 (by rfl) ⟨1417842, by rfl⟩ : syracuseStep 3780913 = 2835685) B2835685
theorem B3780931 : Blo 1770086 3780931 := bstep (se 1 (by rfl) ⟨2835698, by rfl⟩ : syracuseStep 3780931 = 5671397) B5671397
theorem B2691443 : Blo 1770086 2691443 := bstep (se 1 (by rfl) ⟨2018582, by rfl⟩ : syracuseStep 2691443 = 4037165) B4037165
theorem B76616077 : Blo 1770086 76616077 := bstep (se 3 (by rfl) ⟨14365514, by rfl⟩ : syracuseStep 76616077 = 28731029) B28731029
theorem B8507825 : Blo 1770086 8507825 := bstep (se 2 (by rfl) ⟨3190434, by rfl⟩ : syracuseStep 8507825 = 6380869) B6380869
theorem B5976557 : Blo 1770086 5976557 := bstep (se 3 (by rfl) ⟨1120604, by rfl⟩ : syracuseStep 5976557 = 2241209) B2241209
theorem B6386161 : Blo 1770086 6386161 := bstep (se 2 (by rfl) ⟨2394810, by rfl⟩ : syracuseStep 6386161 = 4789621) B4789621
theorem B3985937 : Blo 1770086 3985937 := bstep (se 2 (by rfl) ⟨1494726, by rfl⟩ : syracuseStep 3985937 = 2989453) B2989453
theorem B5976611 : Blo 1770086 5976611 := bstep (se 1 (by rfl) ⟨4482458, by rfl⟩ : syracuseStep 5976611 = 8964917) B8964917
theorem B10088995 : Blo 1770086 10088995 := bstep (se 1 (by rfl) ⟨7566746, by rfl⟩ : syracuseStep 10088995 = 15133493) B15133493
theorem B3985955 : Blo 1770086 3985955 := bstep (se 1 (by rfl) ⟨2989466, by rfl⟩ : syracuseStep 3985955 = 5978933) B5978933
theorem B20730421 : Blo 1770086 20730421 := bstep (se 5 (by rfl) ⟨971738, by rfl⟩ : syracuseStep 20730421 = 1943477) B1943477
theorem B19157573 : Blo 1770086 19157573 := bstep (se 4 (by rfl) ⟨1796022, by rfl⟩ : syracuseStep 19157573 = 3592045) B3592045
theorem B10777157 : Blo 1770086 10777157 := bstep (se 4 (by rfl) ⟨1010358, by rfl⟩ : syracuseStep 10777157 = 2020717) B2020717
theorem B3453521 : Blo 1770086 3453521 := bstep (se 2 (by rfl) ⟨1295070, by rfl⟩ : syracuseStep 3453521 = 2590141) B2590141
theorem B13628017 : Blo 1770086 13628017 := bstep (se 2 (by rfl) ⟨5110506, by rfl⟩ : syracuseStep 13628017 = 10221013) B10221013
theorem B8966861 : Blo 1770086 8966861 := bstep (se 3 (by rfl) ⟨1681286, by rfl⟩ : syracuseStep 8966861 = 3362573) B3362573
theorem B46019299 : Blo 1770086 46019299 := bstep (se 1 (by rfl) ⟨34514474, by rfl⟩ : syracuseStep 46019299 = 69028949) B69028949
theorem B5976881 : Blo 1770086 5976881 := bstep (se 2 (by rfl) ⟨2241330, by rfl⟩ : syracuseStep 5976881 = 4482661) B4482661
theorem B3986225 : Blo 1770086 3986225 := bstep (se 2 (by rfl) ⟨1494834, by rfl⟩ : syracuseStep 3986225 = 2989669) B2989669
theorem B3986243 : Blo 1770086 3986243 := bstep (se 1 (by rfl) ⟨2989682, by rfl⟩ : syracuseStep 3986243 = 5979365) B5979365
theorem B3363697 : Blo 1770086 3363697 := bstep (se 2 (by rfl) ⟨1261386, by rfl⟩ : syracuseStep 3363697 = 2522773) B2522773
theorem B2241427 : Blo 1770086 2241427 := bstep (se 1 (by rfl) ⟨1681070, by rfl⟩ : syracuseStep 2241427 = 3362141) B3362141
theorem B2241523 : Blo 1770086 2241523 := bstep (se 1 (by rfl) ⟨1681142, by rfl⟩ : syracuseStep 2241523 = 3362285) B3362285
theorem B43062293 : Blo 1770086 43062293 := bstep (se 6 (by rfl) ⟨1009272, by rfl⟩ : syracuseStep 43062293 = 2018545) B2018545
theorem B2987057 : Blo 1770086 2987057 := bstep (se 2 (by rfl) ⟨1120146, by rfl⟩ : syracuseStep 2987057 = 2240293) B2240293
theorem B10089521 : Blo 1770086 10089521 := bstep (se 2 (by rfl) ⟨3783570, by rfl⟩ : syracuseStep 10089521 = 7567141) B7567141
theorem B3028033 : Blo 1770086 3028033 := bstep (se 2 (by rfl) ⟨1135512, by rfl⟩ : syracuseStep 3028033 = 2271025) B2271025
theorem B3986513 : Blo 1770086 3986513 := bstep (se 2 (by rfl) ⟨1494942, by rfl⟩ : syracuseStep 3986513 = 2989885) B2989885
theorem B3986531 : Blo 1770086 3986531 := bstep (se 1 (by rfl) ⟨2989898, by rfl⟩ : syracuseStep 3986531 = 5979797) B5979797
theorem B5043313 : Blo 1770086 5043313 := bstep (se 2 (by rfl) ⟨1891242, by rfl⟩ : syracuseStep 5043313 = 3782485) B3782485
theorem B2987185 : Blo 1770086 2987185 := bstep (se 2 (by rfl) ⟨1120194, by rfl⟩ : syracuseStep 2987185 = 2240389) B2240389
theorem B4854979 : Blo 1770086 4854979 := bstep (se 1 (by rfl) ⟨3641234, by rfl⟩ : syracuseStep 4854979 = 7282469) B7282469
theorem B45388997 : Blo 1770086 45388997 := bstep (se 4 (by rfl) ⟨4255218, by rfl⟩ : syracuseStep 45388997 = 8510437) B8510437
theorem B2987219 : Blo 1770086 2987219 := bstep (se 1 (by rfl) ⟨2240414, by rfl⟩ : syracuseStep 2987219 = 4480829) B4480829
theorem B5387555 : Blo 1770086 5387555 := bstep (se 1 (by rfl) ⟨4040666, by rfl⟩ : syracuseStep 5387555 = 8081333) B8081333
theorem B5977421 : Blo 1770086 5977421 := bstep (se 3 (by rfl) ⟨1120766, by rfl⟩ : syracuseStep 5977421 = 2241533) B2241533
theorem B2987347 : Blo 1770086 2987347 := bstep (se 1 (by rfl) ⟨2240510, by rfl⟩ : syracuseStep 2987347 = 4481021) B4481021
theorem B3986801 : Blo 1770086 3986801 := bstep (se 2 (by rfl) ⟨1495050, by rfl⟩ : syracuseStep 3986801 = 2990101) B2990101
theorem B5977475 : Blo 1770086 5977475 := bstep (se 1 (by rfl) ⟨4483106, by rfl⟩ : syracuseStep 5977475 = 8966213) B8966213
theorem B3986819 : Blo 1770086 3986819 := bstep (se 1 (by rfl) ⟨2990114, by rfl⟩ : syracuseStep 3986819 = 5980229) B5980229
theorem B2987489 : Blo 1770086 2987489 := bstep (se 2 (by rfl) ⟨1120308, by rfl⟩ : syracuseStep 2987489 = 2240617) B2240617
theorem B2242019 : Blo 1770086 2242019 := bstep (se 1 (by rfl) ⟨1681514, by rfl⟩ : syracuseStep 2242019 = 3363029) B3363029
theorem B2520563 : Blo 1770086 2520563 := bstep (se 1 (by rfl) ⟨1890422, by rfl⟩ : syracuseStep 2520563 = 3780845) B3780845
theorem B4789763 : Blo 1770086 4789763 := bstep (se 1 (by rfl) ⟨3592322, by rfl⟩ : syracuseStep 4789763 = 7184645) B7184645
theorem B2127379 : Blo 1770086 2127379 := bstep (se 1 (by rfl) ⟨1595534, by rfl⟩ : syracuseStep 2127379 = 3191069) B3191069
theorem B36861493 : Blo 1770086 36861493 := bstep (se 5 (by rfl) ⟨1727882, by rfl⟩ : syracuseStep 36861493 = 3455765) B3455765
theorem B2127427 : Blo 1770086 2127427 := bstep (se 1 (by rfl) ⟨1595570, by rfl⟩ : syracuseStep 2127427 = 3191141) B3191141
theorem B2987617 : Blo 1770086 2987617 := bstep (se 2 (by rfl) ⟨1120356, by rfl⟩ : syracuseStep 2987617 = 2240713) B2240713
theorem B19142257 : Blo 1770086 19142257 := bstep (se 2 (by rfl) ⟨7178346, by rfl⟩ : syracuseStep 19142257 = 14356693) B14356693
theorem B2692721 : Blo 1770086 2692721 := bstep (se 2 (by rfl) ⟨1009770, by rfl⟩ : syracuseStep 2692721 = 2019541) B2019541
theorem B2987651 : Blo 1770086 2987651 := bstep (se 1 (by rfl) ⟨2240738, by rfl⟩ : syracuseStep 2987651 = 4481477) B4481477
theorem B5977745 : Blo 1770086 5977745 := bstep (se 2 (by rfl) ⟨2241654, by rfl⟩ : syracuseStep 5977745 = 4483309) B4483309
theorem B3987089 : Blo 1770086 3987089 := bstep (se 2 (by rfl) ⟨1495158, by rfl⟩ : syracuseStep 3987089 = 2990317) B2990317
theorem B3987107 : Blo 1770086 3987107 := bstep (se 1 (by rfl) ⟨2990330, by rfl⟩ : syracuseStep 3987107 = 5980661) B5980661
theorem B2987779 : Blo 1770086 2987779 := bstep (se 1 (by rfl) ⟨2240834, by rfl⟩ : syracuseStep 2987779 = 4481669) B4481669
theorem B2987921 : Blo 1770086 2987921 := bstep (se 2 (by rfl) ⟨1120470, by rfl⟩ : syracuseStep 2987921 = 2240941) B2240941
theorem B5109745 : Blo 1770086 5109745 := bstep (se 2 (by rfl) ⟨1916154, by rfl⟩ : syracuseStep 5109745 = 3832309) B3832309
theorem B2988049 : Blo 1770086 2988049 := bstep (se 2 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 2988049 = 2241037) B2241037
theorem B7182371 : Blo 1770086 7182371 := bstep (se 1 (by rfl) ⟨5386778, by rfl⟩ : syracuseStep 7182371 = 10773557) B10773557
theorem B4544561 : Blo 1770086 4544561 := bstep (se 2 (by rfl) ⟨1704210, by rfl⟩ : syracuseStep 4544561 = 3408421) B3408421
theorem B2988083 : Blo 1770086 2988083 := bstep (se 1 (by rfl) ⟨2241062, by rfl⟩ : syracuseStep 2988083 = 4482125) B4482125
theorem B20183093 : Blo 1770086 20183093 := bstep (se 5 (by rfl) ⟨946082, by rfl⟩ : syracuseStep 20183093 = 1892165) B1892165
theorem B2521201 : Blo 1770086 2521201 := bstep (se 2 (by rfl) ⟨945450, by rfl⟩ : syracuseStep 2521201 = 1890901) B1890901
theorem B5748877 : Blo 1770086 5748877 := bstep (se 3 (by rfl) ⟨1077914, by rfl⟩ : syracuseStep 5748877 = 2155829) B2155829
theorem B2242723 : Blo 1770086 2242723 := bstep (se 1 (by rfl) ⟨1682042, by rfl⟩ : syracuseStep 2242723 = 3364085) B3364085
theorem B5978285 : Blo 1770086 5978285 := bstep (se 3 (by rfl) ⟨1120928, by rfl⟩ : syracuseStep 5978285 = 2241857) B2241857
theorem B2988211 : Blo 1770086 2988211 := bstep (se 1 (by rfl) ⟨2241158, by rfl⟩ : syracuseStep 2988211 = 4482317) B4482317
theorem B22689989 : Blo 1770086 22689989 := bstep (se 4 (by rfl) ⟨2127186, by rfl⟩ : syracuseStep 22689989 = 4254373) B4254373
theorem B2521315 : Blo 1770086 2521315 := bstep (se 1 (by rfl) ⟨1890986, by rfl⟩ : syracuseStep 2521315 = 3781973) B3781973
theorem B5978339 : Blo 1770086 5978339 := bstep (se 1 (by rfl) ⟨4483754, by rfl⟩ : syracuseStep 5978339 = 8967509) B8967509
theorem B16152817 : Blo 1770086 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B5388529 : Blo 1770086 5388529 := bstep (se 2 (by rfl) ⟨2020698, by rfl⟩ : syracuseStep 5388529 = 4041397) B4041397
theorem B2988353 : Blo 1770086 2988353 := bstep (se 2 (by rfl) ⟨1120632, by rfl⟩ : syracuseStep 2988353 = 2241265) B2241265
theorem B6723917 : Blo 1770086 6723917 := bstep (se 3 (by rfl) ⟨1260734, by rfl⟩ : syracuseStep 6723917 = 2521469) B2521469
theorem B5388625 : Blo 1770086 5388625 := bstep (se 2 (by rfl) ⟨2020734, by rfl⟩ : syracuseStep 5388625 = 4041469) B4041469
theorem B5044589 : Blo 1770086 5044589 := bstep (se 3 (by rfl) ⟨945860, by rfl⟩ : syracuseStep 5044589 = 1891721) B1891721
theorem B1890739 : Blo 1770086 1890739 := bstep (se 1 (by rfl) ⟨1418054, by rfl⟩ : syracuseStep 1890739 = 2836109) B2836109
theorem B2988481 : Blo 1770086 2988481 := bstep (se 2 (by rfl) ⟨1120680, by rfl⟩ : syracuseStep 2988481 = 2241361) B2241361
theorem B6380003 : Blo 1770086 6380003 := bstep (se 1 (by rfl) ⟨4785002, by rfl⟩ : syracuseStep 6380003 = 9570005) B9570005
theorem B2988515 : Blo 1770086 2988515 := bstep (se 1 (by rfl) ⟨2241386, by rfl⟩ : syracuseStep 2988515 = 4482773) B4482773
theorem B10090979 : Blo 1770086 10090979 := bstep (se 1 (by rfl) ⟨7568234, by rfl⟩ : syracuseStep 10090979 = 15136469) B15136469
theorem B5978609 : Blo 1770086 5978609 := bstep (se 2 (by rfl) ⟨2241978, by rfl⟩ : syracuseStep 5978609 = 4483957) B4483957
theorem B17258993 : Blo 1770086 17258993 := bstep (se 2 (by rfl) ⟨6472122, by rfl⟩ : syracuseStep 17258993 = 12944245) B12944245
theorem B11352581 : Blo 1770086 11352581 := bstep (se 4 (by rfl) ⟨1064304, by rfl⟩ : syracuseStep 11352581 = 2128609) B2128609
theorem B3783203 : Blo 1770086 3783203 := bstep (se 1 (by rfl) ⟨2837402, by rfl⟩ : syracuseStep 3783203 = 5674805) B5674805
theorem B5044771 : Blo 1770086 5044771 := bstep (se 1 (by rfl) ⟨3783578, by rfl⟩ : syracuseStep 5044771 = 7567157) B7567157
theorem B5044817 : Blo 1770086 5044817 := bstep (se 2 (by rfl) ⟨1891806, by rfl⟩ : syracuseStep 5044817 = 3783613) B3783613
theorem B2988643 : Blo 1770086 2988643 := bstep (se 1 (by rfl) ⟨2241482, by rfl⟩ : syracuseStep 2988643 = 4482965) B4482965
theorem B22706801 : Blo 1770086 22706801 := bstep (se 2 (by rfl) ⟨8515050, by rfl⟩ : syracuseStep 22706801 = 17030101) B17030101
theorem B7568099 : Blo 1770086 7568099 := bstep (se 1 (by rfl) ⟨5676074, by rfl⟩ : syracuseStep 7568099 = 11352149) B11352149
theorem B2988785 : Blo 1770086 2988785 := bstep (se 2 (by rfl) ⟨1120794, by rfl⟩ : syracuseStep 2988785 = 2241589) B2241589
theorem B8510285 : Blo 1770086 8510285 := bstep (se 3 (by rfl) ⟨1595678, by rfl⟩ : syracuseStep 8510285 = 3191357) B3191357
theorem B7183181 : Blo 1770086 7183181 := bstep (se 3 (by rfl) ⟨1346846, by rfl⟩ : syracuseStep 7183181 = 2693693) B2693693
theorem B2988913 : Blo 1770086 2988913 := bstep (se 2 (by rfl) ⟨1120842, by rfl⟩ : syracuseStep 2988913 = 2241685) B2241685
theorem B2988947 : Blo 1770086 2988947 := bstep (se 1 (by rfl) ⟨2241710, by rfl⟩ : syracuseStep 2988947 = 4483421) B4483421
theorem B3783665 : Blo 1770086 3783665 := bstep (se 2 (by rfl) ⟨1418874, by rfl⟩ : syracuseStep 3783665 = 2837749) B2837749
theorem B5979149 : Blo 1770086 5979149 := bstep (se 3 (by rfl) ⟨1121090, by rfl⟩ : syracuseStep 5979149 = 2242181) B2242181
theorem B2989075 : Blo 1770086 2989075 := bstep (se 1 (by rfl) ⟨2241806, by rfl⟩ : syracuseStep 2989075 = 4483613) B4483613
theorem B5979203 : Blo 1770086 5979203 := bstep (se 1 (by rfl) ⟨4484402, by rfl⟩ : syracuseStep 5979203 = 8968805) B8968805
theorem B6724721 : Blo 1770086 6724721 := bstep (se 2 (by rfl) ⟨2521770, by rfl⟩ : syracuseStep 6724721 = 5043541) B5043541
theorem B6061169 : Blo 1770086 6061169 := bstep (se 2 (by rfl) ⟨2272938, by rfl⟩ : syracuseStep 6061169 = 4545877) B4545877
theorem B2989217 : Blo 1770086 2989217 := bstep (se 2 (by rfl) ⟨1120956, by rfl⟩ : syracuseStep 2989217 = 2241913) B2241913
theorem B2989345 : Blo 1770086 2989345 := bstep (se 2 (by rfl) ⟨1121004, by rfl⟩ : syracuseStep 2989345 = 2242009) B2242009
theorem B9706787 : Blo 1770086 9706787 := bstep (se 1 (by rfl) ⟨7280090, by rfl⟩ : syracuseStep 9706787 = 14560181) B14560181
theorem B2989379 : Blo 1770086 2989379 := bstep (se 1 (by rfl) ⟨2242034, by rfl⟩ : syracuseStep 2989379 = 4484069) B4484069
theorem B5979473 : Blo 1770086 5979473 := bstep (se 2 (by rfl) ⟨2242302, by rfl⟩ : syracuseStep 5979473 = 4484605) B4484605
theorem B5750129 : Blo 1770086 5750129 := bstep (se 2 (by rfl) ⟨2156298, by rfl⟩ : syracuseStep 5750129 = 4312597) B4312597
theorem B5676419 : Blo 1770086 5676419 := bstep (se 1 (by rfl) ⟨4257314, by rfl⟩ : syracuseStep 5676419 = 8514629) B8514629
theorem B3030419 : Blo 1770086 3030419 := bstep (se 1 (by rfl) ⟨2272814, by rfl⟩ : syracuseStep 3030419 = 4545629) B4545629
theorem B2989507 : Blo 1770086 2989507 := bstep (se 1 (by rfl) ⟨2242130, by rfl⟩ : syracuseStep 2989507 = 4484261) B4484261
theorem B3030515 : Blo 1770086 3030515 := bstep (se 1 (by rfl) ⟨2272886, by rfl⟩ : syracuseStep 3030515 = 4545773) B4545773
theorem B2522659 : Blo 1770086 2522659 := bstep (se 1 (by rfl) ⟨1891994, by rfl⟩ : syracuseStep 2522659 = 3783989) B3783989
theorem B8969777 : Blo 1770086 8969777 := bstep (se 2 (by rfl) ⟨3363666, by rfl⟩ : syracuseStep 8969777 = 6727333) B6727333
theorem B2989649 : Blo 1770086 2989649 := bstep (se 2 (by rfl) ⟨1121118, by rfl⟩ : syracuseStep 2989649 = 2242237) B2242237
theorem B8961677 : Blo 1770086 8961677 := bstep (se 3 (by rfl) ⟨1680314, by rfl⟩ : syracuseStep 8961677 = 3360629) B3360629
theorem B1892003 : Blo 1770086 1892003 := bstep (se 1 (by rfl) ⟨1419002, by rfl⟩ : syracuseStep 1892003 = 2838005) B2838005
theorem B2989777 : Blo 1770086 2989777 := bstep (se 2 (by rfl) ⟨1121166, by rfl⟩ : syracuseStep 2989777 = 2242333) B2242333
theorem B8077027 : Blo 1770086 8077027 := bstep (se 1 (by rfl) ⟨6057770, by rfl⟩ : syracuseStep 8077027 = 12115541) B12115541
theorem B2989811 : Blo 1770086 2989811 := bstep (se 1 (by rfl) ⟨2242358, by rfl⟩ : syracuseStep 2989811 = 4484717) B4484717
theorem B6725389 : Blo 1770086 6725389 := bstep (se 3 (by rfl) ⟨1261010, by rfl⟩ : syracuseStep 6725389 = 2522021) B2522021
theorem B13451021 : Blo 1770086 13451021 := bstep (se 3 (by rfl) ⟨2522066, by rfl⟩ : syracuseStep 13451021 = 5044133) B5044133
theorem B5980013 : Blo 1770086 5980013 := bstep (se 3 (by rfl) ⟨1121252, by rfl⟩ : syracuseStep 5980013 = 2242505) B2242505
theorem B2989939 : Blo 1770086 2989939 := bstep (se 1 (by rfl) ⟨2242454, by rfl⟩ : syracuseStep 2989939 = 4484909) B4484909
theorem B5980067 : Blo 1770086 5980067 := bstep (se 1 (by rfl) ⟨4485050, by rfl⟩ : syracuseStep 5980067 = 8970101) B8970101
theorem B2990155 : Blo 1770086 2990155 := bstep (se 1 (by rfl) ⟨2242616, by rfl⟩ : syracuseStep 2990155 = 4485233) B4485233
theorem B4481203 : Blo 1770086 4481203 := bstep (se 1 (by rfl) ⟨3360902, by rfl⟩ : syracuseStep 4481203 = 6721805) B6721805
theorem B2990297 : Blo 1770086 2990297 := bstep (se 2 (by rfl) ⟨1121361, by rfl⟩ : syracuseStep 2990297 = 2242723) B2242723
theorem B1794295 : Blo 1770086 1794295 := bstep (se 1 (by rfl) ⟨1345721, by rfl⟩ : syracuseStep 1794295 = 2691443) B2691443
theorem B4481345 : Blo 1770086 4481345 := bstep (se 2 (by rfl) ⟨1680504, by rfl⟩ : syracuseStep 4481345 = 3361009) B3361009
theorem B21537089 : Blo 1770086 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B7184705 : Blo 1770086 7184705 := bstep (se 2 (by rfl) ⟨2694264, by rfl⟩ : syracuseStep 7184705 = 5388529) B5388529
theorem B11346277 : Blo 1770086 11346277 := bstep (se 4 (by rfl) ⟨1063713, by rfl⟩ : syracuseStep 11346277 = 2127427) B2127427
theorem B12771715 : Blo 1770086 12771715 := bstep (se 1 (by rfl) ⟨9578786, by rfl⟩ : syracuseStep 12771715 = 19157573) B19157573
theorem B7184771 : Blo 1770086 7184771 := bstep (se 1 (by rfl) ⟨5388578, by rfl⟩ : syracuseStep 7184771 = 10777157) B10777157
theorem B102154769 : Blo 1770086 102154769 := bstep (se 2 (by rfl) ⟨38308038, by rfl⟩ : syracuseStep 102154769 = 76616077) B76616077
theorem B1770091 : Blo 1770086 1770091 := bstep (se 1 (by rfl) ⟨1327568, by rfl⟩ : syracuseStep 1770091 = 2655137) B2655137
theorem B1770103 : Blo 1770086 1770103 := bstep (se 1 (by rfl) ⟨1327577, by rfl⟩ : syracuseStep 1770103 = 2655155) B2655155
theorem B1770123 : Blo 1770086 1770123 := bstep (se 1 (by rfl) ⟨1327592, by rfl⟩ : syracuseStep 1770123 = 2655185) B2655185
theorem B1770135 : Blo 1770086 1770135 := bstep (se 1 (by rfl) ⟨1327601, by rfl⟩ : syracuseStep 1770135 = 2655203) B2655203
theorem B8077975 : Blo 1770086 8077975 := bstep (se 1 (by rfl) ⟨6058481, by rfl⟩ : syracuseStep 8077975 = 12116963) B12116963
theorem B1770155 : Blo 1770086 1770155 := bstep (se 1 (by rfl) ⟨1327616, by rfl⟩ : syracuseStep 1770155 = 2655233) B2655233
theorem B1770167 : Blo 1770086 1770167 := bstep (se 1 (by rfl) ⟨1327625, by rfl⟩ : syracuseStep 1770167 = 2655251) B2655251
theorem B1991371 : Blo 1770086 1991371 := bstep (se 1 (by rfl) ⟨1493528, by rfl⟩ : syracuseStep 1991371 = 2987057) B2987057
theorem B1770187 : Blo 1770086 1770187 := bstep (se 1 (by rfl) ⟨1327640, by rfl⟩ : syracuseStep 1770187 = 2655281) B2655281
theorem B34046669 : Blo 1770086 34046669 := bstep (se 3 (by rfl) ⟨6383750, by rfl⟩ : syracuseStep 34046669 = 12767501) B12767501
theorem B6726347 : Blo 1770086 6726347 := bstep (se 1 (by rfl) ⟨5044760, by rfl⟩ : syracuseStep 6726347 = 10089521) B10089521
theorem B1770199 : Blo 1770086 1770199 := bstep (se 1 (by rfl) ⟨1327649, by rfl⟩ : syracuseStep 1770199 = 2655299) B2655299
theorem B13451993 : Blo 1770086 13451993 := bstep (se 2 (by rfl) ⟨5044497, by rfl⟩ : syracuseStep 13451993 = 10088995) B10088995
theorem B6726361 : Blo 1770086 6726361 := bstep (se 2 (by rfl) ⟨2522385, by rfl⟩ : syracuseStep 6726361 = 5044771) B5044771
theorem B1770219 : Blo 1770086 1770219 := bstep (se 1 (by rfl) ⟨1327664, by rfl⟩ : syracuseStep 1770219 = 2655329) B2655329
theorem B27640561 : Blo 1770086 27640561 := bstep (se 2 (by rfl) ⟨10365210, by rfl⟩ : syracuseStep 27640561 = 20730421) B20730421
theorem B1770231 : Blo 1770086 1770231 := bstep (se 1 (by rfl) ⟨1327673, by rfl⟩ : syracuseStep 1770231 = 2655347) B2655347
theorem B1770251 : Blo 1770086 1770251 := bstep (se 1 (by rfl) ⟨1327688, by rfl⟩ : syracuseStep 1770251 = 2655377) B2655377
theorem B1770263 : Blo 1770086 1770263 := bstep (se 1 (by rfl) ⟨1327697, by rfl⟩ : syracuseStep 1770263 = 2655395) B2655395
theorem B1770283 : Blo 1770086 1770283 := bstep (se 1 (by rfl) ⟨1327712, by rfl⟩ : syracuseStep 1770283 = 2655425) B2655425
theorem B1991479 : Blo 1770086 1991479 := bstep (se 1 (by rfl) ⟨1493609, by rfl⟩ : syracuseStep 1991479 = 2987219) B2987219
theorem B1770295 : Blo 1770086 1770295 := bstep (se 1 (by rfl) ⟨1327721, by rfl⟩ : syracuseStep 1770295 = 2655443) B2655443
theorem B8971073 : Blo 1770086 8971073 := bstep (se 2 (by rfl) ⟨3364152, by rfl⟩ : syracuseStep 8971073 = 6728305) B6728305
theorem B1770315 : Blo 1770086 1770315 := bstep (se 1 (by rfl) ⟨1327736, by rfl⟩ : syracuseStep 1770315 = 2655473) B2655473
theorem B2392907 : Blo 1770086 2392907 := bstep (se 1 (by rfl) ⟨1794680, by rfl⟩ : syracuseStep 2392907 = 3589361) B3589361
theorem B1770327 : Blo 1770086 1770327 := bstep (se 1 (by rfl) ⟨1327745, by rfl⟩ : syracuseStep 1770327 = 2655491) B2655491
theorem B1770347 : Blo 1770086 1770347 := bstep (se 1 (by rfl) ⟨1327760, by rfl⟩ : syracuseStep 1770347 = 2655521) B2655521
theorem B1770359 : Blo 1770086 1770359 := bstep (se 1 (by rfl) ⟨1327769, by rfl⟩ : syracuseStep 1770359 = 2655539) B2655539
theorem B1770379 : Blo 1770086 1770379 := bstep (se 1 (by rfl) ⟨1327784, by rfl⟩ : syracuseStep 1770379 = 2655569) B2655569
theorem B1770391 : Blo 1770086 1770391 := bstep (se 1 (by rfl) ⟨1327793, by rfl⟩ : syracuseStep 1770391 = 2655587) B2655587
theorem B1770411 : Blo 1770086 1770411 := bstep (se 1 (by rfl) ⟨1327808, by rfl⟩ : syracuseStep 1770411 = 2655617) B2655617
theorem B1770423 : Blo 1770086 1770423 := bstep (se 1 (by rfl) ⟨1327817, by rfl⟩ : syracuseStep 1770423 = 2655635) B2655635
theorem B2655179 : Blo 1770086 2655179 := bstep (se 1 (by rfl) ⟨1991384, by rfl⟩ : syracuseStep 2655179 = 3982769) B3982769
theorem B1770443 : Blo 1770086 1770443 := bstep (se 1 (by rfl) ⟨1327832, by rfl⟩ : syracuseStep 1770443 = 2655665) B2655665
theorem B2655191 : Blo 1770086 2655191 := bstep (se 1 (by rfl) ⟨1991393, by rfl⟩ : syracuseStep 2655191 = 3982787) B3982787
theorem B1770455 : Blo 1770086 1770455 := bstep (se 1 (by rfl) ⟨1327841, by rfl⟩ : syracuseStep 1770455 = 2655683) B2655683
theorem B61359065 : Blo 1770086 61359065 := bstep (se 2 (by rfl) ⟨23009649, by rfl⟩ : syracuseStep 61359065 = 46019299) B46019299
theorem B1991659 : Blo 1770086 1991659 := bstep (se 1 (by rfl) ⟨1493744, by rfl⟩ : syracuseStep 1991659 = 2987489) B2987489
theorem B1770475 : Blo 1770086 1770475 := bstep (se 1 (by rfl) ⟨1327856, by rfl⟩ : syracuseStep 1770475 = 2655713) B2655713
theorem B1770487 : Blo 1770086 1770487 := bstep (se 1 (by rfl) ⟨1327865, by rfl⟩ : syracuseStep 1770487 = 2655731) B2655731
theorem B1770507 : Blo 1770086 1770507 := bstep (se 1 (by rfl) ⟨1327880, by rfl⟩ : syracuseStep 1770507 = 2655761) B2655761
theorem B1770519 : Blo 1770086 1770519 := bstep (se 1 (by rfl) ⟨1327889, by rfl⟩ : syracuseStep 1770519 = 2655779) B2655779
theorem B2655257 : Blo 1770086 2655257 := bstep (se 2 (by rfl) ⟨995721, by rfl⟩ : syracuseStep 2655257 = 1991443) B1991443
theorem B1770539 : Blo 1770086 1770539 := bstep (se 1 (by rfl) ⟨1327904, by rfl⟩ : syracuseStep 1770539 = 2655809) B2655809
theorem B1770551 : Blo 1770086 1770551 := bstep (se 1 (by rfl) ⟨1327913, by rfl⟩ : syracuseStep 1770551 = 2655827) B2655827
theorem B1770571 : Blo 1770086 1770571 := bstep (se 1 (by rfl) ⟨1327928, by rfl⟩ : syracuseStep 1770571 = 2655857) B2655857
theorem B1991767 : Blo 1770086 1991767 := bstep (se 1 (by rfl) ⟨1493825, by rfl⟩ : syracuseStep 1991767 = 2987651) B2987651
theorem B1770583 : Blo 1770086 1770583 := bstep (se 1 (by rfl) ⟨1327937, by rfl⟩ : syracuseStep 1770583 = 2655875) B2655875
theorem B1770603 : Blo 1770086 1770603 := bstep (se 1 (by rfl) ⟨1327952, by rfl⟩ : syracuseStep 1770603 = 2655905) B2655905
theorem B1770615 : Blo 1770086 1770615 := bstep (se 1 (by rfl) ⟨1327961, by rfl⟩ : syracuseStep 1770615 = 2655923) B2655923
theorem B2655371 : Blo 1770086 2655371 := bstep (se 1 (by rfl) ⟨1991528, by rfl⟩ : syracuseStep 2655371 = 3983057) B3983057
theorem B1770635 : Blo 1770086 1770635 := bstep (se 1 (by rfl) ⟨1327976, by rfl⟩ : syracuseStep 1770635 = 2655953) B2655953
theorem B2655383 : Blo 1770086 2655383 := bstep (se 1 (by rfl) ⟨1991537, by rfl⟩ : syracuseStep 2655383 = 3983075) B3983075
theorem B1770647 : Blo 1770086 1770647 := bstep (se 1 (by rfl) ⟨1327985, by rfl⟩ : syracuseStep 1770647 = 2655971) B2655971
theorem B1770667 : Blo 1770086 1770667 := bstep (se 1 (by rfl) ⟨1328000, by rfl⟩ : syracuseStep 1770667 = 2656001) B2656001
theorem B1770679 : Blo 1770086 1770679 := bstep (se 1 (by rfl) ⟨1328009, by rfl⟩ : syracuseStep 1770679 = 2656019) B2656019
theorem B1770699 : Blo 1770086 1770699 := bstep (se 1 (by rfl) ⟨1328024, by rfl⟩ : syracuseStep 1770699 = 2656049) B2656049
theorem B1770711 : Blo 1770086 1770711 := bstep (se 1 (by rfl) ⟨1328033, by rfl⟩ : syracuseStep 1770711 = 2656067) B2656067
theorem B2655449 : Blo 1770086 2655449 := bstep (se 2 (by rfl) ⟨995793, by rfl⟩ : syracuseStep 2655449 = 1991587) B1991587
theorem B1770731 : Blo 1770086 1770731 := bstep (se 1 (by rfl) ⟨1328048, by rfl⟩ : syracuseStep 1770731 = 2656097) B2656097
theorem B1770743 : Blo 1770086 1770743 := bstep (se 1 (by rfl) ⟨1328057, by rfl⟩ : syracuseStep 1770743 = 2656115) B2656115
theorem B1991947 : Blo 1770086 1991947 := bstep (se 1 (by rfl) ⟨1493960, by rfl⟩ : syracuseStep 1991947 = 2987921) B2987921
theorem B1770763 : Blo 1770086 1770763 := bstep (se 1 (by rfl) ⟨1328072, by rfl⟩ : syracuseStep 1770763 = 2656145) B2656145
theorem B1770775 : Blo 1770086 1770775 := bstep (se 1 (by rfl) ⟨1328081, by rfl⟩ : syracuseStep 1770775 = 2656163) B2656163
theorem B1770795 : Blo 1770086 1770795 := bstep (se 1 (by rfl) ⟨1328096, by rfl⟩ : syracuseStep 1770795 = 2656193) B2656193
theorem B1770807 : Blo 1770086 1770807 := bstep (se 1 (by rfl) ⟨1328105, by rfl⟩ : syracuseStep 1770807 = 2656211) B2656211
theorem B30246209 : Blo 1770086 30246209 := bstep (se 2 (by rfl) ⟨11342328, by rfl⟩ : syracuseStep 30246209 = 22684657) B22684657
theorem B2655563 : Blo 1770086 2655563 := bstep (se 1 (by rfl) ⟨1991672, by rfl⟩ : syracuseStep 2655563 = 3983345) B3983345
theorem B1770827 : Blo 1770086 1770827 := bstep (se 1 (by rfl) ⟨1328120, by rfl⟩ : syracuseStep 1770827 = 2656241) B2656241
theorem B2655575 : Blo 1770086 2655575 := bstep (se 1 (by rfl) ⟨1991681, by rfl⟩ : syracuseStep 2655575 = 3983363) B3983363
theorem B1770839 : Blo 1770086 1770839 := bstep (se 1 (by rfl) ⟨1328129, by rfl⟩ : syracuseStep 1770839 = 2656259) B2656259
theorem B2393431 : Blo 1770086 2393431 := bstep (se 1 (by rfl) ⟨1795073, by rfl⟩ : syracuseStep 2393431 = 3590147) B3590147
theorem B1770859 : Blo 1770086 1770859 := bstep (se 1 (by rfl) ⟨1328144, by rfl⟩ : syracuseStep 1770859 = 2656289) B2656289
theorem B1992055 : Blo 1770086 1992055 := bstep (se 1 (by rfl) ⟨1494041, by rfl⟩ : syracuseStep 1992055 = 2988083) B2988083
theorem B1770871 : Blo 1770086 1770871 := bstep (se 1 (by rfl) ⟨1328153, by rfl⟩ : syracuseStep 1770871 = 2656307) B2656307
theorem B8963459 : Blo 1770086 8963459 := bstep (se 1 (by rfl) ⟨6722594, by rfl⟩ : syracuseStep 8963459 = 13445189) B13445189
theorem B1770891 : Blo 1770086 1770891 := bstep (se 1 (by rfl) ⟨1328168, by rfl⟩ : syracuseStep 1770891 = 2656337) B2656337
theorem B1770903 : Blo 1770086 1770903 := bstep (se 1 (by rfl) ⟨1328177, by rfl⟩ : syracuseStep 1770903 = 2656355) B2656355
theorem B2655641 : Blo 1770086 2655641 := bstep (se 2 (by rfl) ⟨995865, by rfl⟩ : syracuseStep 2655641 = 1991731) B1991731
theorem B2393497 : Blo 1770086 2393497 := bstep (se 2 (by rfl) ⟨897561, by rfl⟩ : syracuseStep 2393497 = 1795123) B1795123
theorem B1770923 : Blo 1770086 1770923 := bstep (se 1 (by rfl) ⟨1328192, by rfl⟩ : syracuseStep 1770923 = 2656385) B2656385
theorem B10765747 : Blo 1770086 10765747 := bstep (se 1 (by rfl) ⟨8074310, by rfl⟩ : syracuseStep 10765747 = 16148621) B16148621
theorem B1770935 : Blo 1770086 1770935 := bstep (se 1 (by rfl) ⟨1328201, by rfl⟩ : syracuseStep 1770935 = 2656403) B2656403
theorem B1770955 : Blo 1770086 1770955 := bstep (se 1 (by rfl) ⟨1328216, by rfl⟩ : syracuseStep 1770955 = 2656433) B2656433
theorem B1770967 : Blo 1770086 1770967 := bstep (se 1 (by rfl) ⟨1328225, by rfl⟩ : syracuseStep 1770967 = 2656451) B2656451
theorem B1770987 : Blo 1770086 1770987 := bstep (se 1 (by rfl) ⟨1328240, by rfl⟩ : syracuseStep 1770987 = 2656481) B2656481
theorem B1770999 : Blo 1770086 1770999 := bstep (se 1 (by rfl) ⟨1328249, by rfl⟩ : syracuseStep 1770999 = 2656499) B2656499
theorem B3982859 : Blo 1770086 3982859 := bstep (se 1 (by rfl) ⟨2987144, by rfl⟩ : syracuseStep 3982859 = 5974289) B5974289
theorem B2655755 : Blo 1770086 2655755 := bstep (se 1 (by rfl) ⟨1991816, by rfl⟩ : syracuseStep 2655755 = 3983633) B3983633
theorem B1771019 : Blo 1770086 1771019 := bstep (se 1 (by rfl) ⟨1328264, by rfl⟩ : syracuseStep 1771019 = 2656529) B2656529
theorem B2655767 : Blo 1770086 2655767 := bstep (se 1 (by rfl) ⟨1991825, by rfl⟩ : syracuseStep 2655767 = 3983651) B3983651
theorem B1771031 : Blo 1770086 1771031 := bstep (se 1 (by rfl) ⟨1328273, by rfl⟩ : syracuseStep 1771031 = 2656547) B2656547
theorem B1992235 : Blo 1770086 1992235 := bstep (se 1 (by rfl) ⟨1494176, by rfl⟩ : syracuseStep 1992235 = 2988353) B2988353
theorem B1771051 : Blo 1770086 1771051 := bstep (se 1 (by rfl) ⟨1328288, by rfl⟩ : syracuseStep 1771051 = 2656577) B2656577
theorem B9209389 : Blo 1770086 9209389 := bstep (se 3 (by rfl) ⟨1726760, by rfl⟩ : syracuseStep 9209389 = 3453521) B3453521
theorem B4482611 : Blo 1770086 4482611 := bstep (se 1 (by rfl) ⟨3361958, by rfl⟩ : syracuseStep 4482611 = 6723917) B6723917
theorem B1771063 : Blo 1770086 1771063 := bstep (se 1 (by rfl) ⟨1328297, by rfl⟩ : syracuseStep 1771063 = 2656595) B2656595
theorem B3982913 : Blo 1770086 3982913 := bstep (se 2 (by rfl) ⟨1493592, by rfl⟩ : syracuseStep 3982913 = 2987185) B2987185
theorem B1771083 : Blo 1770086 1771083 := bstep (se 1 (by rfl) ⟨1328312, by rfl⟩ : syracuseStep 1771083 = 2656625) B2656625
theorem B1771095 : Blo 1770086 1771095 := bstep (se 1 (by rfl) ⟨1328321, by rfl⟩ : syracuseStep 1771095 = 2656643) B2656643
theorem B2655833 : Blo 1770086 2655833 := bstep (se 2 (by rfl) ⟨995937, by rfl⟩ : syracuseStep 2655833 = 1991875) B1991875
theorem B6473305 : Blo 1770086 6473305 := bstep (se 2 (by rfl) ⟨2427489, by rfl⟩ : syracuseStep 6473305 = 4854979) B4854979
theorem B1771115 : Blo 1770086 1771115 := bstep (se 1 (by rfl) ⟨1328336, by rfl⟩ : syracuseStep 1771115 = 2656673) B2656673
theorem B1771127 : Blo 1770086 1771127 := bstep (se 1 (by rfl) ⟨1328345, by rfl⟩ : syracuseStep 1771127 = 2656691) B2656691
theorem B1771147 : Blo 1770086 1771147 := bstep (se 1 (by rfl) ⟨1328360, by rfl⟩ : syracuseStep 1771147 = 2656721) B2656721
theorem B1992343 : Blo 1770086 1992343 := bstep (se 1 (by rfl) ⟨1494257, by rfl⟩ : syracuseStep 1992343 = 2988515) B2988515
theorem B1771159 : Blo 1770086 1771159 := bstep (se 1 (by rfl) ⟨1328369, by rfl⟩ : syracuseStep 1771159 = 2656739) B2656739
theorem B6727319 : Blo 1770086 6727319 := bstep (se 1 (by rfl) ⟨5045489, by rfl⟩ : syracuseStep 6727319 = 10090979) B10090979
theorem B1771179 : Blo 1770086 1771179 := bstep (se 1 (by rfl) ⟨1328384, by rfl⟩ : syracuseStep 1771179 = 2656769) B2656769
theorem B1771191 : Blo 1770086 1771191 := bstep (se 1 (by rfl) ⟨1328393, by rfl⟩ : syracuseStep 1771191 = 2656787) B2656787
theorem B2655947 : Blo 1770086 2655947 := bstep (se 1 (by rfl) ⟨1991960, by rfl⟩ : syracuseStep 2655947 = 3983921) B3983921
theorem B1771211 : Blo 1770086 1771211 := bstep (se 1 (by rfl) ⟨1328408, by rfl⟩ : syracuseStep 1771211 = 2656817) B2656817
theorem B2655959 : Blo 1770086 2655959 := bstep (se 1 (by rfl) ⟨1991969, by rfl⟩ : syracuseStep 2655959 = 3983939) B3983939
theorem B1771223 : Blo 1770086 1771223 := bstep (se 1 (by rfl) ⟨1328417, by rfl⟩ : syracuseStep 1771223 = 2656835) B2656835
theorem B1771243 : Blo 1770086 1771243 := bstep (se 1 (by rfl) ⟨1328432, by rfl⟩ : syracuseStep 1771243 = 2656865) B2656865
theorem B1771255 : Blo 1770086 1771255 := bstep (se 1 (by rfl) ⟨1328441, by rfl⟩ : syracuseStep 1771255 = 2656883) B2656883
theorem B28739333 : Blo 1770086 28739333 := bstep (se 4 (by rfl) ⟨2694312, by rfl⟩ : syracuseStep 28739333 = 5388625) B5388625
theorem B3360523 : Blo 1770086 3360523 := bstep (se 1 (by rfl) ⟨2520392, by rfl⟩ : syracuseStep 3360523 = 5040785) B5040785
theorem B1771275 : Blo 1770086 1771275 := bstep (se 1 (by rfl) ⟨1328456, by rfl⟩ : syracuseStep 1771275 = 2656913) B2656913
theorem B3983129 : Blo 1770086 3983129 := bstep (se 2 (by rfl) ⟨1493673, by rfl⟩ : syracuseStep 3983129 = 2987347) B2987347
theorem B2656025 : Blo 1770086 2656025 := bstep (se 2 (by rfl) ⟨996009, by rfl⟩ : syracuseStep 2656025 = 1992019) B1992019
theorem B1771287 : Blo 1770086 1771287 := bstep (se 1 (by rfl) ⟨1328465, by rfl⟩ : syracuseStep 1771287 = 2656931) B2656931
theorem B6383405 : Blo 1770086 6383405 := bstep (se 3 (by rfl) ⟨1196888, by rfl⟩ : syracuseStep 6383405 = 2393777) B2393777
theorem B1771307 : Blo 1770086 1771307 := bstep (se 1 (by rfl) ⟨1328480, by rfl⟩ : syracuseStep 1771307 = 2656961) B2656961
theorem B1771319 : Blo 1770086 1771319 := bstep (se 1 (by rfl) ⟨1328489, by rfl⟩ : syracuseStep 1771319 = 2656979) B2656979
theorem B1992523 : Blo 1770086 1992523 := bstep (se 1 (by rfl) ⟨1494392, by rfl⟩ : syracuseStep 1992523 = 2988785) B2988785
theorem B1771339 : Blo 1770086 1771339 := bstep (se 1 (by rfl) ⟨1328504, by rfl⟩ : syracuseStep 1771339 = 2657009) B2657009
theorem B3360599 : Blo 1770086 3360599 := bstep (se 1 (by rfl) ⟨2520449, by rfl⟩ : syracuseStep 3360599 = 5040899) B5040899
theorem B1771351 : Blo 1770086 1771351 := bstep (se 1 (by rfl) ⟨1328513, by rfl⟩ : syracuseStep 1771351 = 2657027) B2657027
theorem B1771371 : Blo 1770086 1771371 := bstep (se 1 (by rfl) ⟨1328528, by rfl⟩ : syracuseStep 1771371 = 2657057) B2657057
theorem B3983219 : Blo 1770086 3983219 := bstep (se 1 (by rfl) ⟨2987414, by rfl⟩ : syracuseStep 3983219 = 5974829) B5974829
theorem B1771383 : Blo 1770086 1771383 := bstep (se 1 (by rfl) ⟨1328537, by rfl⟩ : syracuseStep 1771383 = 2657075) B2657075
theorem B2656139 : Blo 1770086 2656139 := bstep (se 1 (by rfl) ⟨1992104, by rfl⟩ : syracuseStep 2656139 = 3984209) B3984209
theorem B1771403 : Blo 1770086 1771403 := bstep (se 1 (by rfl) ⟨1328552, by rfl⟩ : syracuseStep 1771403 = 2657105) B2657105
theorem B3983255 : Blo 1770086 3983255 := bstep (se 1 (by rfl) ⟨2987441, by rfl⟩ : syracuseStep 3983255 = 5974883) B5974883
theorem B2656151 : Blo 1770086 2656151 := bstep (se 1 (by rfl) ⟨1992113, by rfl⟩ : syracuseStep 2656151 = 3984227) B3984227
theorem B1771415 : Blo 1770086 1771415 := bstep (se 1 (by rfl) ⟨1328561, by rfl⟩ : syracuseStep 1771415 = 2657123) B2657123
theorem B1771435 : Blo 1770086 1771435 := bstep (se 1 (by rfl) ⟨1328576, by rfl⟩ : syracuseStep 1771435 = 2657153) B2657153
theorem B1992631 : Blo 1770086 1992631 := bstep (se 1 (by rfl) ⟨1494473, by rfl⟩ : syracuseStep 1992631 = 2988947) B2988947
theorem B1771447 : Blo 1770086 1771447 := bstep (se 1 (by rfl) ⟨1328585, by rfl⟩ : syracuseStep 1771447 = 2657171) B2657171
theorem B1771467 : Blo 1770086 1771467 := bstep (se 1 (by rfl) ⟨1328600, by rfl⟩ : syracuseStep 1771467 = 2657201) B2657201
theorem B1771479 : Blo 1770086 1771479 := bstep (se 1 (by rfl) ⟨1328609, by rfl⟩ : syracuseStep 1771479 = 2657219) B2657219
theorem B2656217 : Blo 1770086 2656217 := bstep (se 2 (by rfl) ⟨996081, by rfl⟩ : syracuseStep 2656217 = 1992163) B1992163
theorem B1771499 : Blo 1770086 1771499 := bstep (se 1 (by rfl) ⟨1328624, by rfl⟩ : syracuseStep 1771499 = 2657249) B2657249
theorem B1771511 : Blo 1770086 1771511 := bstep (se 1 (by rfl) ⟨1328633, by rfl⟩ : syracuseStep 1771511 = 2657267) B2657267
theorem B1771531 : Blo 1770086 1771531 := bstep (se 1 (by rfl) ⟨1328648, by rfl⟩ : syracuseStep 1771531 = 2657297) B2657297
theorem B20441105 : Blo 1770086 20441105 := bstep (se 2 (by rfl) ⟨7665414, by rfl⟩ : syracuseStep 20441105 = 15330829) B15330829
theorem B1771543 : Blo 1770086 1771543 := bstep (se 1 (by rfl) ⟨1328657, by rfl⟩ : syracuseStep 1771543 = 2657315) B2657315
theorem B2836505 : Blo 1770086 2836505 := bstep (se 2 (by rfl) ⟨1063689, by rfl⟩ : syracuseStep 2836505 = 2127379) B2127379
theorem B1771563 : Blo 1770086 1771563 := bstep (se 1 (by rfl) ⟨1328672, by rfl⟩ : syracuseStep 1771563 = 2657345) B2657345
theorem B1771575 : Blo 1770086 1771575 := bstep (se 1 (by rfl) ⟨1328681, by rfl⟩ : syracuseStep 1771575 = 2657363) B2657363
theorem B3983435 : Blo 1770086 3983435 := bstep (se 1 (by rfl) ⟨2987576, by rfl⟩ : syracuseStep 3983435 = 5975153) B5975153
theorem B2656331 : Blo 1770086 2656331 := bstep (se 1 (by rfl) ⟨1992248, by rfl⟩ : syracuseStep 2656331 = 3984497) B3984497
theorem B4483147 : Blo 1770086 4483147 := bstep (se 1 (by rfl) ⟨3362360, by rfl⟩ : syracuseStep 4483147 = 6724721) B6724721
theorem B5752907 : Blo 1770086 5752907 := bstep (se 1 (by rfl) ⟨4314680, by rfl⟩ : syracuseStep 5752907 = 8629361) B8629361
theorem B1771595 : Blo 1770086 1771595 := bstep (se 1 (by rfl) ⟨1328696, by rfl⟩ : syracuseStep 1771595 = 2657393) B2657393
theorem B4040779 : Blo 1770086 4040779 := bstep (se 1 (by rfl) ⟨3030584, by rfl⟩ : syracuseStep 4040779 = 6061169) B6061169
theorem B2656343 : Blo 1770086 2656343 := bstep (se 1 (by rfl) ⟨1992257, by rfl⟩ : syracuseStep 2656343 = 3984515) B3984515
theorem B1771607 : Blo 1770086 1771607 := bstep (se 1 (by rfl) ⟨1328705, by rfl⟩ : syracuseStep 1771607 = 2657411) B2657411
theorem B1992811 : Blo 1770086 1992811 := bstep (se 1 (by rfl) ⟨1494608, by rfl⟩ : syracuseStep 1992811 = 2989217) B2989217
theorem B1771627 : Blo 1770086 1771627 := bstep (se 1 (by rfl) ⟨1328720, by rfl⟩ : syracuseStep 1771627 = 2657441) B2657441
theorem B1771639 : Blo 1770086 1771639 := bstep (se 1 (by rfl) ⟨1328729, by rfl⟩ : syracuseStep 1771639 = 2657459) B2657459
theorem B3983489 : Blo 1770086 3983489 := bstep (se 2 (by rfl) ⟨1493808, by rfl⟩ : syracuseStep 3983489 = 2987617) B2987617
theorem B1771659 : Blo 1770086 1771659 := bstep (se 1 (by rfl) ⟨1328744, by rfl⟩ : syracuseStep 1771659 = 2657489) B2657489
theorem B1771671 : Blo 1770086 1771671 := bstep (se 1 (by rfl) ⟨1328753, by rfl⟩ : syracuseStep 1771671 = 2657507) B2657507
theorem B2656409 : Blo 1770086 2656409 := bstep (se 2 (by rfl) ⟨996153, by rfl⟩ : syracuseStep 2656409 = 1992307) B1992307
theorem B1771691 : Blo 1770086 1771691 := bstep (se 1 (by rfl) ⟨1328768, by rfl⟩ : syracuseStep 1771691 = 2657537) B2657537
theorem B1771703 : Blo 1770086 1771703 := bstep (se 1 (by rfl) ⟨1328777, by rfl⟩ : syracuseStep 1771703 = 2657555) B2657555
theorem B1771723 : Blo 1770086 1771723 := bstep (se 1 (by rfl) ⟨1328792, by rfl⟩ : syracuseStep 1771723 = 2657585) B2657585
theorem B19155149 : Blo 1770086 19155149 := bstep (se 3 (by rfl) ⟨3591590, by rfl⟩ : syracuseStep 19155149 = 7183181) B7183181
theorem B1992919 : Blo 1770086 1992919 := bstep (se 1 (by rfl) ⟨1494689, by rfl⟩ : syracuseStep 1992919 = 2989379) B2989379
theorem B1771735 : Blo 1770086 1771735 := bstep (se 1 (by rfl) ⟨1328801, by rfl⟩ : syracuseStep 1771735 = 2657603) B2657603
theorem B4483289 : Blo 1770086 4483289 := bstep (se 2 (by rfl) ⟨1681233, by rfl⟩ : syracuseStep 4483289 = 3362467) B3362467
theorem B1771755 : Blo 1770086 1771755 := bstep (se 1 (by rfl) ⟨1328816, by rfl⟩ : syracuseStep 1771755 = 2657633) B2657633
theorem B1771767 : Blo 1770086 1771767 := bstep (se 1 (by rfl) ⟨1328825, by rfl⟩ : syracuseStep 1771767 = 2657651) B2657651
theorem B2656523 : Blo 1770086 2656523 := bstep (se 1 (by rfl) ⟨1992392, by rfl⟩ : syracuseStep 2656523 = 3984785) B3984785
theorem B1771787 : Blo 1770086 1771787 := bstep (se 1 (by rfl) ⟨1328840, by rfl⟩ : syracuseStep 1771787 = 2657681) B2657681
theorem B2656535 : Blo 1770086 2656535 := bstep (se 1 (by rfl) ⟨1992401, by rfl⟩ : syracuseStep 2656535 = 3984803) B3984803
theorem B1771799 : Blo 1770086 1771799 := bstep (se 1 (by rfl) ⟨1328849, by rfl⟩ : syracuseStep 1771799 = 2657699) B2657699
theorem B1771819 : Blo 1770086 1771819 := bstep (se 1 (by rfl) ⟨1328864, by rfl⟩ : syracuseStep 1771819 = 2657729) B2657729
theorem B1771831 : Blo 1770086 1771831 := bstep (se 1 (by rfl) ⟨1328873, by rfl⟩ : syracuseStep 1771831 = 2657747) B2657747
theorem B1771851 : Blo 1770086 1771851 := bstep (se 1 (by rfl) ⟨1328888, by rfl⟩ : syracuseStep 1771851 = 2657777) B2657777
theorem B1771863 : Blo 1770086 1771863 := bstep (se 1 (by rfl) ⟨1328897, by rfl⟩ : syracuseStep 1771863 = 2657795) B2657795
theorem B3983705 : Blo 1770086 3983705 := bstep (se 2 (by rfl) ⟨1493889, by rfl⟩ : syracuseStep 3983705 = 2987779) B2987779
theorem B2656601 : Blo 1770086 2656601 := bstep (se 2 (by rfl) ⟨996225, by rfl⟩ : syracuseStep 2656601 = 1992451) B1992451
theorem B1771883 : Blo 1770086 1771883 := bstep (se 1 (by rfl) ⟨1328912, by rfl⟩ : syracuseStep 1771883 = 2657825) B2657825
theorem B1771895 : Blo 1770086 1771895 := bstep (se 1 (by rfl) ⟨1328921, by rfl⟩ : syracuseStep 1771895 = 2657843) B2657843
theorem B1993099 : Blo 1770086 1993099 := bstep (se 1 (by rfl) ⟨1494824, by rfl⟩ : syracuseStep 1993099 = 2989649) B2989649
theorem B1771915 : Blo 1770086 1771915 := bstep (se 1 (by rfl) ⟨1328936, by rfl⟩ : syracuseStep 1771915 = 2657873) B2657873
theorem B1771927 : Blo 1770086 1771927 := bstep (se 1 (by rfl) ⟨1328945, by rfl⟩ : syracuseStep 1771927 = 2657891) B2657891
theorem B1771947 : Blo 1770086 1771947 := bstep (se 1 (by rfl) ⟨1328960, by rfl⟩ : syracuseStep 1771947 = 2657921) B2657921
theorem B5974451 : Blo 1770086 5974451 := bstep (se 1 (by rfl) ⟨4480838, by rfl⟩ : syracuseStep 5974451 = 8961677) B8961677
theorem B3983795 : Blo 1770086 3983795 := bstep (se 1 (by rfl) ⟨2987846, by rfl⟩ : syracuseStep 3983795 = 5975693) B5975693
theorem B1771959 : Blo 1770086 1771959 := bstep (se 1 (by rfl) ⟨1328969, by rfl⟩ : syracuseStep 1771959 = 2657939) B2657939
theorem B2656715 : Blo 1770086 2656715 := bstep (se 1 (by rfl) ⟨1992536, by rfl⟩ : syracuseStep 2656715 = 3985073) B3985073
theorem B1771979 : Blo 1770086 1771979 := bstep (se 1 (by rfl) ⟨1328984, by rfl⟩ : syracuseStep 1771979 = 2657969) B2657969
theorem B3983831 : Blo 1770086 3983831 := bstep (se 1 (by rfl) ⟨2987873, by rfl⟩ : syracuseStep 3983831 = 5975747) B5975747
theorem B2656727 : Blo 1770086 2656727 := bstep (se 1 (by rfl) ⟨1992545, by rfl⟩ : syracuseStep 2656727 = 3985091) B3985091
theorem B10226137 : Blo 1770086 10226137 := bstep (se 2 (by rfl) ⟨3834801, by rfl⟩ : syracuseStep 10226137 = 7669603) B7669603
theorem B1771991 : Blo 1770086 1771991 := bstep (se 1 (by rfl) ⟨1328993, by rfl⟩ : syracuseStep 1771991 = 2657987) B2657987
theorem B1772011 : Blo 1770086 1772011 := bstep (se 1 (by rfl) ⟨1329008, by rfl⟩ : syracuseStep 1772011 = 2658017) B2658017
theorem B3361267 : Blo 1770086 3361267 := bstep (se 1 (by rfl) ⟨2520950, by rfl⟩ : syracuseStep 3361267 = 5041901) B5041901
theorem B1993207 : Blo 1770086 1993207 := bstep (se 1 (by rfl) ⟨1494905, by rfl⟩ : syracuseStep 1993207 = 2989811) B2989811
theorem B1772023 : Blo 1770086 1772023 := bstep (se 1 (by rfl) ⟨1329017, by rfl⟩ : syracuseStep 1772023 = 2658035) B2658035
theorem B1772043 : Blo 1770086 1772043 := bstep (se 1 (by rfl) ⟨1329032, by rfl⟩ : syracuseStep 1772043 = 2658065) B2658065
theorem B1772055 : Blo 1770086 1772055 := bstep (se 1 (by rfl) ⟨1329041, by rfl⟩ : syracuseStep 1772055 = 2658083) B2658083
theorem B2656793 : Blo 1770086 2656793 := bstep (se 2 (by rfl) ⟨996297, by rfl⟩ : syracuseStep 2656793 = 1992595) B1992595
theorem B1772075 : Blo 1770086 1772075 := bstep (se 1 (by rfl) ⟨1329056, by rfl⟩ : syracuseStep 1772075 = 2658113) B2658113
theorem B3984011 : Blo 1770086 3984011 := bstep (se 1 (by rfl) ⟨2988008, by rfl⟩ : syracuseStep 3984011 = 5976017) B5976017
theorem B2656907 : Blo 1770086 2656907 := bstep (se 1 (by rfl) ⟨1992680, by rfl⟩ : syracuseStep 2656907 = 3985361) B3985361
theorem B2656919 : Blo 1770086 2656919 := bstep (se 1 (by rfl) ⟨1992689, by rfl⟩ : syracuseStep 2656919 = 3985379) B3985379
theorem B1993387 : Blo 1770086 1993387 := bstep (se 1 (by rfl) ⟨1495040, by rfl⟩ : syracuseStep 1993387 = 2990081) B2990081
theorem B5974721 : Blo 1770086 5974721 := bstep (se 2 (by rfl) ⟨2240520, by rfl⟩ : syracuseStep 5974721 = 4481041) B4481041
theorem B3984065 : Blo 1770086 3984065 := bstep (se 2 (by rfl) ⟨1494024, by rfl⟩ : syracuseStep 3984065 = 2988049) B2988049
theorem B3361495 : Blo 1770086 3361495 := bstep (se 1 (by rfl) ⟨2521121, by rfl⟩ : syracuseStep 3361495 = 5042243) B5042243
theorem B2656985 : Blo 1770086 2656985 := bstep (se 2 (by rfl) ⟨996369, by rfl⟩ : syracuseStep 2656985 = 1992739) B1992739
theorem B7564049 : Blo 1770086 7564049 := bstep (se 2 (by rfl) ⟨2836518, by rfl⟩ : syracuseStep 7564049 = 5673037) B5673037
theorem B1993495 : Blo 1770086 1993495 := bstep (se 1 (by rfl) ⟨1495121, by rfl⟩ : syracuseStep 1993495 = 2990243) B2990243
theorem B3361601 : Blo 1770086 3361601 := bstep (se 2 (by rfl) ⟨1260600, by rfl⟩ : syracuseStep 3361601 = 2521201) B2521201
theorem B40897345 : Blo 1770086 40897345 := bstep (se 2 (by rfl) ⟨15336504, by rfl⟩ : syracuseStep 40897345 = 30673009) B30673009
theorem B2657099 : Blo 1770086 2657099 := bstep (se 1 (by rfl) ⟨1992824, by rfl⟩ : syracuseStep 2657099 = 3985649) B3985649
theorem B2657111 : Blo 1770086 2657111 := bstep (se 1 (by rfl) ⟨1992833, by rfl⟩ : syracuseStep 2657111 = 3985667) B3985667
theorem B3984281 : Blo 1770086 3984281 := bstep (se 2 (by rfl) ⟨1494105, by rfl⟩ : syracuseStep 3984281 = 2988211) B2988211
theorem B2657177 : Blo 1770086 2657177 := bstep (se 2 (by rfl) ⟨996441, by rfl⟩ : syracuseStep 2657177 = 1992883) B1992883
theorem B5671883 : Blo 1770086 5671883 := bstep (se 1 (by rfl) ⟨4253912, by rfl⟩ : syracuseStep 5671883 = 8507825) B8507825
theorem B3361753 : Blo 1770086 3361753 := bstep (se 2 (by rfl) ⟨1260657, by rfl⟩ : syracuseStep 3361753 = 2521315) B2521315
theorem B3984371 : Blo 1770086 3984371 := bstep (se 1 (by rfl) ⟨2988278, by rfl⟩ : syracuseStep 3984371 = 5976557) B5976557
theorem B2657291 : Blo 1770086 2657291 := bstep (se 1 (by rfl) ⟨1992968, by rfl⟩ : syracuseStep 2657291 = 3985937) B3985937
theorem B13446161 : Blo 1770086 13446161 := bstep (se 2 (by rfl) ⟨5042310, by rfl⟩ : syracuseStep 13446161 = 10084621) B10084621
theorem B3984407 : Blo 1770086 3984407 := bstep (se 1 (by rfl) ⟨2988305, by rfl⟩ : syracuseStep 3984407 = 5976611) B5976611
theorem B4484119 : Blo 1770086 4484119 := bstep (se 1 (by rfl) ⟨3363089, by rfl⟩ : syracuseStep 4484119 = 6726179) B6726179
theorem B2657303 : Blo 1770086 2657303 := bstep (se 1 (by rfl) ⟨1992977, by rfl⟩ : syracuseStep 2657303 = 3985955) B3985955
theorem B10775597 : Blo 1770086 10775597 := bstep (se 3 (by rfl) ⟨2020424, by rfl⟩ : syracuseStep 10775597 = 4040849) B4040849
theorem B5041217 : Blo 1770086 5041217 := bstep (se 2 (by rfl) ⟨1890456, by rfl⟩ : syracuseStep 5041217 = 3780913) B3780913
theorem B5041241 : Blo 1770086 5041241 := bstep (se 2 (by rfl) ⟨1890465, by rfl⟩ : syracuseStep 5041241 = 3780931) B3780931
theorem B2657369 : Blo 1770086 2657369 := bstep (se 2 (by rfl) ⟨996513, by rfl⟩ : syracuseStep 2657369 = 1993027) B1993027
theorem B3984587 : Blo 1770086 3984587 := bstep (se 1 (by rfl) ⟨2988440, by rfl⟩ : syracuseStep 3984587 = 5976881) B5976881
theorem B2657483 : Blo 1770086 2657483 := bstep (se 1 (by rfl) ⟨1993112, by rfl⟩ : syracuseStep 2657483 = 3986225) B3986225
theorem B2657495 : Blo 1770086 2657495 := bstep (se 1 (by rfl) ⟨1993121, by rfl⟩ : syracuseStep 2657495 = 3986243) B3986243
theorem B5975261 : Blo 1770086 5975261 := bstep (se 3 (by rfl) ⟨1120361, by rfl⟩ : syracuseStep 5975261 = 2240723) B2240723
theorem B3984641 : Blo 1770086 3984641 := bstep (se 2 (by rfl) ⟨1494240, by rfl⟩ : syracuseStep 3984641 = 2988481) B2988481
theorem B72682757 : Blo 1770086 72682757 := bstep (se 4 (by rfl) ⟨6814008, by rfl⟩ : syracuseStep 72682757 = 13628017) B13628017
theorem B2657561 : Blo 1770086 2657561 := bstep (se 2 (by rfl) ⟨996585, by rfl⟩ : syracuseStep 2657561 = 1993171) B1993171
theorem B6720833 : Blo 1770086 6720833 := bstep (se 2 (by rfl) ⟨2520312, by rfl⟩ : syracuseStep 6720833 = 5040625) B5040625
theorem B8514881 : Blo 1770086 8514881 := bstep (se 2 (by rfl) ⟨3193080, by rfl⟩ : syracuseStep 8514881 = 6386161) B6386161
theorem B5672281 : Blo 1770086 5672281 := bstep (se 2 (by rfl) ⟨2127105, by rfl⟩ : syracuseStep 5672281 = 4254211) B4254211
theorem B4787545 : Blo 1770086 4787545 := bstep (se 2 (by rfl) ⟨1795329, by rfl⟩ : syracuseStep 4787545 = 3590659) B3590659
theorem B28708195 : Blo 1770086 28708195 := bstep (se 1 (by rfl) ⟨21531146, by rfl⟩ : syracuseStep 28708195 = 43062293) B43062293
theorem B10087811 : Blo 1770086 10087811 := bstep (se 1 (by rfl) ⟨7565858, by rfl⟩ : syracuseStep 10087811 = 15131717) B15131717
theorem B2657675 : Blo 1770086 2657675 := bstep (se 1 (by rfl) ⟨1993256, by rfl⟩ : syracuseStep 2657675 = 3986513) B3986513
theorem B2657687 : Blo 1770086 2657687 := bstep (se 1 (by rfl) ⟨1993265, by rfl⟩ : syracuseStep 2657687 = 3986531) B3986531
theorem B4484555 : Blo 1770086 4484555 := bstep (se 1 (by rfl) ⟨3363416, by rfl⟩ : syracuseStep 4484555 = 6726833) B6726833
theorem B3984857 : Blo 1770086 3984857 := bstep (se 2 (by rfl) ⟨1494321, by rfl⟩ : syracuseStep 3984857 = 2988643) B2988643
theorem B2657753 : Blo 1770086 2657753 := bstep (se 2 (by rfl) ⟨996657, by rfl⟩ : syracuseStep 2657753 = 1993315) B1993315
theorem B7564765 : Blo 1770086 7564765 := bstep (se 3 (by rfl) ⟨1418393, by rfl⟩ : syracuseStep 7564765 = 2836787) B2836787
theorem B3984947 : Blo 1770086 3984947 := bstep (se 1 (by rfl) ⟨2988710, by rfl⟩ : syracuseStep 3984947 = 5977421) B5977421
theorem B2657867 : Blo 1770086 2657867 := bstep (se 1 (by rfl) ⟨1993400, by rfl⟩ : syracuseStep 2657867 = 3986801) B3986801
theorem B3984983 : Blo 1770086 3984983 := bstep (se 1 (by rfl) ⟨2988737, by rfl⟩ : syracuseStep 3984983 = 5977475) B5977475
theorem B2657879 : Blo 1770086 2657879 := bstep (se 1 (by rfl) ⟨1993409, by rfl⟩ : syracuseStep 2657879 = 3986819) B3986819
theorem B2657945 : Blo 1770086 2657945 := bstep (se 2 (by rfl) ⟨996729, by rfl⟩ : syracuseStep 2657945 = 1993459) B1993459
theorem B109080269 : Blo 1770086 109080269 := bstep (se 3 (by rfl) ⟨20452550, by rfl⟩ : syracuseStep 109080269 = 40905101) B40905101
theorem B8081117 : Blo 1770086 8081117 := bstep (se 3 (by rfl) ⟨1515209, by rfl⟩ : syracuseStep 8081117 = 3030419) B3030419
theorem B3985163 : Blo 1770086 3985163 := bstep (se 1 (by rfl) ⟨2988872, by rfl⟩ : syracuseStep 3985163 = 5977745) B5977745
theorem B2658059 : Blo 1770086 2658059 := bstep (se 1 (by rfl) ⟨1993544, by rfl⟩ : syracuseStep 2658059 = 3987089) B3987089
theorem B2658071 : Blo 1770086 2658071 := bstep (se 1 (by rfl) ⟨1993553, by rfl⟩ : syracuseStep 2658071 = 3987107) B3987107
theorem B3985217 : Blo 1770086 3985217 := bstep (se 2 (by rfl) ⟨1494456, by rfl⟩ : syracuseStep 3985217 = 2988913) B2988913
theorem B4484929 : Blo 1770086 4484929 := bstep (se 2 (by rfl) ⟨1681848, by rfl⟩ : syracuseStep 4484929 = 3363697) B3363697
theorem B12111709 : Blo 1770086 12111709 := bstep (se 3 (by rfl) ⟨2270945, by rfl⟩ : syracuseStep 12111709 = 4541891) B4541891
theorem B6721501 : Blo 1770086 6721501 := bstep (se 3 (by rfl) ⟨1260281, by rfl⟩ : syracuseStep 6721501 = 2520563) B2520563
theorem B4788247 : Blo 1770086 4788247 := bstep (se 1 (by rfl) ⟨3591185, by rfl⟩ : syracuseStep 4788247 = 7182371) B7182371
theorem B3985433 : Blo 1770086 3985433 := bstep (se 2 (by rfl) ⟨1494537, by rfl⟩ : syracuseStep 3985433 = 2989075) B2989075
theorem B13455395 : Blo 1770086 13455395 := bstep (se 1 (by rfl) ⟨10091546, by rfl⟩ : syracuseStep 13455395 = 20183093) B20183093
theorem B3985523 : Blo 1770086 3985523 := bstep (se 1 (by rfl) ⟨2989142, by rfl⟩ : syracuseStep 3985523 = 5978285) B5978285
theorem B15126659 : Blo 1770086 15126659 := bstep (se 1 (by rfl) ⟨11344994, by rfl⟩ : syracuseStep 15126659 = 22689989) B22689989
theorem B3985559 : Blo 1770086 3985559 := bstep (se 1 (by rfl) ⟨2989169, by rfl⟩ : syracuseStep 3985559 = 5978339) B5978339
theorem B3363059 : Blo 1770086 3363059 := bstep (se 1 (by rfl) ⟨2522294, by rfl⟩ : syracuseStep 3363059 = 5044589) B5044589
theorem B2240779 : Blo 1770086 2240779 := bstep (se 1 (by rfl) ⟨1680584, by rfl⟩ : syracuseStep 2240779 = 3361169) B3361169
theorem B7180589 : Blo 1770086 7180589 := bstep (se 3 (by rfl) ⟨1346360, by rfl⟩ : syracuseStep 7180589 = 2692721) B2692721
theorem B5042483 : Blo 1770086 5042483 := bstep (se 1 (by rfl) ⟨3781862, by rfl⟩ : syracuseStep 5042483 = 7563725) B7563725
theorem B5976395 : Blo 1770086 5976395 := bstep (se 1 (by rfl) ⟨4482296, by rfl⟩ : syracuseStep 5976395 = 8964593) B8964593
theorem B3985739 : Blo 1770086 3985739 := bstep (se 1 (by rfl) ⟨2989304, by rfl⟩ : syracuseStep 3985739 = 5978609) B5978609
theorem B11505995 : Blo 1770086 11505995 := bstep (se 1 (by rfl) ⟨8629496, by rfl⟩ : syracuseStep 11505995 = 17258993) B17258993
theorem B96932213 : Blo 1770086 96932213 := bstep (se 5 (by rfl) ⟨4543697, by rfl⟩ : syracuseStep 96932213 = 9087395) B9087395
theorem B3985793 : Blo 1770086 3985793 := bstep (se 2 (by rfl) ⟨1494672, by rfl⟩ : syracuseStep 3985793 = 2989345) B2989345
theorem B3363211 : Blo 1770086 3363211 := bstep (se 1 (by rfl) ⟨2522408, by rfl⟩ : syracuseStep 3363211 = 5044817) B5044817
theorem B4485527 : Blo 1770086 4485527 := bstep (se 1 (by rfl) ⟨3364145, by rfl⟩ : syracuseStep 4485527 = 6728291) B6728291
theorem B2241047 : Blo 1770086 2241047 := bstep (se 1 (by rfl) ⟨1680785, by rfl⟩ : syracuseStep 2241047 = 3361571) B3361571
theorem B5673523 : Blo 1770086 5673523 := bstep (se 1 (by rfl) ⟨4255142, by rfl⟩ : syracuseStep 5673523 = 8510285) B8510285
theorem B5976665 : Blo 1770086 5976665 := bstep (se 2 (by rfl) ⟨2241249, by rfl⟩ : syracuseStep 5976665 = 4482499) B4482499
theorem B3986009 : Blo 1770086 3986009 := bstep (se 2 (by rfl) ⟨1494753, by rfl⟩ : syracuseStep 3986009 = 2989507) B2989507
theorem B20181635 : Blo 1770086 20181635 := bstep (se 1 (by rfl) ⟨15136226, by rfl⟩ : syracuseStep 20181635 = 30272453) B30272453
theorem B3986099 : Blo 1770086 3986099 := bstep (se 1 (by rfl) ⟨2989574, by rfl⟩ : syracuseStep 3986099 = 5979149) B5979149
theorem B3986135 : Blo 1770086 3986135 := bstep (se 1 (by rfl) ⟨2989601, by rfl⟩ : syracuseStep 3986135 = 5979203) B5979203
theorem B3363545 : Blo 1770086 3363545 := bstep (se 2 (by rfl) ⟨1261329, by rfl⟩ : syracuseStep 3363545 = 2522659) B2522659
theorem B49148657 : Blo 1770086 49148657 := bstep (se 2 (by rfl) ⟨18430746, by rfl⟩ : syracuseStep 49148657 = 36861493) B36861493
theorem B6386435 : Blo 1770086 6386435 := bstep (se 1 (by rfl) ⟨4789826, by rfl⟩ : syracuseStep 6386435 = 9579653) B9579653
theorem B25523009 : Blo 1770086 25523009 := bstep (se 2 (by rfl) ⟨9571128, by rfl⟩ : syracuseStep 25523009 = 19142257) B19142257
theorem B3986315 : Blo 1770086 3986315 := bstep (se 1 (by rfl) ⟨2989736, by rfl⟩ : syracuseStep 3986315 = 5979473) B5979473
theorem B7181201 : Blo 1770086 7181201 := bstep (se 2 (by rfl) ⟨2692950, by rfl⟩ : syracuseStep 7181201 = 5385901) B5385901
theorem B3986369 : Blo 1770086 3986369 := bstep (se 2 (by rfl) ⟨1494888, by rfl⟩ : syracuseStep 3986369 = 2989777) B2989777
theorem B10769369 : Blo 1770086 10769369 := bstep (se 2 (by rfl) ⟨4038513, by rfl⟩ : syracuseStep 10769369 = 8077027) B8077027
theorem B2020343 : Blo 1770086 2020343 := bstep (se 1 (by rfl) ⟨1515257, by rfl⟩ : syracuseStep 2020343 = 3030515) B3030515
theorem B8967185 : Blo 1770086 8967185 := bstep (se 2 (by rfl) ⟨3362694, by rfl⟩ : syracuseStep 8967185 = 6725389) B6725389
theorem B3781657 : Blo 1770086 3781657 := bstep (se 2 (by rfl) ⟨1418121, by rfl⟩ : syracuseStep 3781657 = 2836243) B2836243
theorem B3191833 : Blo 1770086 3191833 := bstep (se 2 (by rfl) ⟨1196937, by rfl⟩ : syracuseStep 3191833 = 2393875) B2393875
theorem B3986585 : Blo 1770086 3986585 := bstep (se 2 (by rfl) ⟨1494969, by rfl⟩ : syracuseStep 3986585 = 2989939) B2989939
theorem B8967347 : Blo 1770086 8967347 := bstep (se 1 (by rfl) ⟨6725510, by rfl⟩ : syracuseStep 8967347 = 13451021) B13451021
theorem B2241751 : Blo 1770086 2241751 := bstep (se 1 (by rfl) ⟨1681313, by rfl⟩ : syracuseStep 2241751 = 3362627) B3362627
theorem B6722777 : Blo 1770086 6722777 := bstep (se 2 (by rfl) ⟨2521041, by rfl⟩ : syracuseStep 6722777 = 5042083) B5042083
theorem B3986675 : Blo 1770086 3986675 := bstep (se 1 (by rfl) ⟨2990006, by rfl⟩ : syracuseStep 3986675 = 5980013) B5980013
theorem B12760325 : Blo 1770086 12760325 := bstep (se 4 (by rfl) ⟨1196280, by rfl⟩ : syracuseStep 12760325 = 2392561) B2392561
theorem B5977367 : Blo 1770086 5977367 := bstep (se 1 (by rfl) ⟨4483025, by rfl⟩ : syracuseStep 5977367 = 8966051) B8966051
theorem B3986711 : Blo 1770086 3986711 := bstep (se 1 (by rfl) ⟨2990033, by rfl⟩ : syracuseStep 3986711 = 5980067) B5980067
theorem B11343149 : Blo 1770086 11343149 := bstep (se 3 (by rfl) ⟨2126840, by rfl⟩ : syracuseStep 11343149 = 4253681) B4253681
theorem B6812993 : Blo 1770086 6812993 := bstep (se 2 (by rfl) ⟨2554872, by rfl⟩ : syracuseStep 6812993 = 5109745) B5109745
theorem B3364183 : Blo 1770086 3364183 := bstep (se 1 (by rfl) ⟨2523137, by rfl⟩ : syracuseStep 3364183 = 5046275) B5046275
theorem B3986891 : Blo 1770086 3986891 := bstep (se 1 (by rfl) ⟨2990168, by rfl⟩ : syracuseStep 3986891 = 5980337) B5980337
theorem B3986945 : Blo 1770086 3986945 := bstep (se 2 (by rfl) ⟨1495104, by rfl⟩ : syracuseStep 3986945 = 2990209) B2990209
theorem B2987543 : Blo 1770086 2987543 := bstep (se 1 (by rfl) ⟨2240657, by rfl⟩ : syracuseStep 2987543 = 4481315) B4481315
theorem B16152157 : Blo 1770086 16152157 := bstep (se 3 (by rfl) ⟨3028529, by rfl⟩ : syracuseStep 16152157 = 6057059) B6057059
theorem B2987671 : Blo 1770086 2987671 := bstep (se 1 (by rfl) ⟨2240753, by rfl⟩ : syracuseStep 2987671 = 4481507) B4481507
theorem B7182017 : Blo 1770086 7182017 := bstep (se 2 (by rfl) ⟨2693256, by rfl⟩ : syracuseStep 7182017 = 5386513) B5386513
theorem B3987161 : Blo 1770086 3987161 := bstep (se 2 (by rfl) ⟨1495185, by rfl⟩ : syracuseStep 3987161 = 2990371) B2990371
theorem B5977907 : Blo 1770086 5977907 := bstep (se 1 (by rfl) ⟨4483430, by rfl⟩ : syracuseStep 5977907 = 8966861) B8966861
theorem B2520985 : Blo 1770086 2520985 := bstep (se 2 (by rfl) ⟨945369, by rfl⟩ : syracuseStep 2520985 = 1890739) B1890739
theorem B12769325 : Blo 1770086 12769325 := bstep (se 3 (by rfl) ⟨2394248, by rfl⟩ : syracuseStep 12769325 = 4788497) B4788497
theorem B5978177 : Blo 1770086 5978177 := bstep (se 2 (by rfl) ⟨2241816, by rfl⟩ : syracuseStep 5978177 = 4483633) B4483633
theorem B30660677 : Blo 1770086 30660677 := bstep (se 4 (by rfl) ⟨2874438, by rfl⟩ : syracuseStep 30660677 = 5748877) B5748877
theorem B14366813 : Blo 1770086 14366813 := bstep (se 3 (by rfl) ⟨2693777, by rfl⟩ : syracuseStep 14366813 = 5387555) B5387555
theorem B30259331 : Blo 1770086 30259331 := bstep (se 1 (by rfl) ⟨22694498, by rfl⟩ : syracuseStep 30259331 = 45388997) B45388997
theorem B1890487 : Blo 1770086 1890487 := bstep (se 1 (by rfl) ⟨1417865, by rfl⟩ : syracuseStep 1890487 = 2835731) B2835731
theorem B2988299 : Blo 1770086 2988299 := bstep (se 1 (by rfl) ⟨2241224, by rfl⟩ : syracuseStep 2988299 = 4482449) B4482449
theorem B3193175 : Blo 1770086 3193175 := bstep (se 1 (by rfl) ⟨2394881, by rfl⟩ : syracuseStep 3193175 = 4789763) B4789763
theorem B15137117 : Blo 1770086 15137117 := bstep (se 3 (by rfl) ⟨2838209, by rfl⟩ : syracuseStep 15137117 = 5676419) B5676419
theorem B2988427 : Blo 1770086 2988427 := bstep (se 1 (by rfl) ⟨2241320, by rfl⟩ : syracuseStep 2988427 = 4482641) B4482641
theorem B9574807 : Blo 1770086 9574807 := bstep (se 1 (by rfl) ⟨7181105, by rfl⟩ : syracuseStep 9574807 = 14362211) B14362211
theorem B2988569 : Blo 1770086 2988569 := bstep (se 2 (by rfl) ⟨1120713, by rfl⟩ : syracuseStep 2988569 = 2241427) B2241427
theorem B17013341 : Blo 1770086 17013341 := bstep (se 3 (by rfl) ⟨3190001, by rfl⟩ : syracuseStep 17013341 = 6380003) B6380003
theorem B5978717 : Blo 1770086 5978717 := bstep (se 3 (by rfl) ⟨1121009, by rfl⟩ : syracuseStep 5978717 = 2242019) B2242019
theorem B2988697 : Blo 1770086 2988697 := bstep (se 2 (by rfl) ⟨1120761, by rfl⟩ : syracuseStep 2988697 = 2241523) B2241523
theorem B3029707 : Blo 1770086 3029707 := bstep (se 1 (by rfl) ⟨2272280, by rfl⟩ : syracuseStep 3029707 = 4544561) B4544561
theorem B4037377 : Blo 1770086 4037377 := bstep (se 2 (by rfl) ⟨1514016, by rfl⟩ : syracuseStep 4037377 = 3028033) B3028033
theorem B6724403 : Blo 1770086 6724403 := bstep (se 1 (by rfl) ⟨5043302, by rfl⟩ : syracuseStep 6724403 = 10086605) B10086605
theorem B6724417 : Blo 1770086 6724417 := bstep (se 2 (by rfl) ⟨2521656, by rfl⟩ : syracuseStep 6724417 = 5043313) B5043313
theorem B13450049 : Blo 1770086 13450049 := bstep (se 2 (by rfl) ⟨5043768, by rfl⟩ : syracuseStep 13450049 = 10087537) B10087537
theorem B1891307 : Blo 1770086 1891307 := bstep (se 1 (by rfl) ⟨1418480, by rfl⟩ : syracuseStep 1891307 = 2836961) B2836961
theorem B7568387 : Blo 1770086 7568387 := bstep (se 1 (by rfl) ⟨5676290, by rfl⟩ : syracuseStep 7568387 = 11352581) B11352581
theorem B2522135 : Blo 1770086 2522135 := bstep (se 1 (by rfl) ⟨1891601, by rfl⟩ : syracuseStep 2522135 = 3783203) B3783203
theorem B8969291 : Blo 1770086 8969291 := bstep (se 1 (by rfl) ⟨6726968, by rfl⟩ : syracuseStep 8969291 = 13453937) B13453937
theorem B15137867 : Blo 1770086 15137867 := bstep (se 1 (by rfl) ⟨11353400, by rfl⟩ : syracuseStep 15137867 = 22706801) B22706801
theorem B5045341 : Blo 1770086 5045341 := bstep (se 3 (by rfl) ⟨946001, by rfl⟩ : syracuseStep 5045341 = 1892003) B1892003
theorem B5045399 : Blo 1770086 5045399 := bstep (se 1 (by rfl) ⟨3784049, by rfl⟩ : syracuseStep 5045399 = 7568099) B7568099
theorem B2989271 : Blo 1770086 2989271 := bstep (se 1 (by rfl) ⟨2241953, by rfl⟩ : syracuseStep 2989271 = 4483907) B4483907
theorem B2522443 : Blo 1770086 2522443 := bstep (se 1 (by rfl) ⟨1891832, by rfl⟩ : syracuseStep 2522443 = 3783665) B3783665
theorem B2989399 : Blo 1770086 2989399 := bstep (se 1 (by rfl) ⟨2242049, by rfl⟩ : syracuseStep 2989399 = 4484099) B4484099
theorem B48463373 : Blo 1770086 48463373 := bstep (se 3 (by rfl) ⟨9086882, by rfl⟩ : syracuseStep 48463373 = 18173765) B18173765
theorem B4480535 : Blo 1770086 4480535 := bstep (se 1 (by rfl) ⟨3360401, by rfl⟩ : syracuseStep 4480535 = 6720803) B6720803
theorem B6471191 : Blo 1770086 6471191 := bstep (se 1 (by rfl) ⟨4853393, by rfl⟩ : syracuseStep 6471191 = 9706787) B9706787
theorem B3833419 : Blo 1770086 3833419 := bstep (se 1 (by rfl) ⟨2875064, by rfl⟩ : syracuseStep 3833419 = 5750129) B5750129
theorem B5979851 : Blo 1770086 5979851 := bstep (se 1 (by rfl) ⟨4484888, by rfl⟩ : syracuseStep 5979851 = 8969777) B8969777
theorem B20168513 : Blo 1770086 20168513 := bstep (se 2 (by rfl) ⟨7563192, by rfl⟩ : syracuseStep 20168513 = 15126385) B15126385
theorem B4038551 : Blo 1770086 4038551 := bstep (se 1 (by rfl) ⟨3028913, by rfl⟩ : syracuseStep 4038551 = 6057827) B6057827
theorem B2990027 : Blo 1770086 2990027 := bstep (se 1 (by rfl) ⟨2242520, by rfl⟩ : syracuseStep 2990027 = 4485041) B4485041
theorem B5980121 : Blo 1770086 5980121 := bstep (se 2 (by rfl) ⟨2242545, by rfl⟩ : syracuseStep 5980121 = 4485091) B4485091
theorem B8970263 : Blo 1770086 8970263 := bstep (se 1 (by rfl) ⟨6727697, by rfl⟩ : syracuseStep 8970263 = 13455395) B13455395
theorem B6725693 : Blo 1770086 6725693 := bstep (se 3 (by rfl) ⟨1261067, by rfl⟩ : syracuseStep 6725693 = 2522135) B2522135
theorem B10084439 : Blo 1770086 10084439 := bstep (se 1 (by rfl) ⟨7563329, by rfl⟩ : syracuseStep 10084439 = 15126659) B15126659
theorem B13443245 : Blo 1770086 13443245 := bstep (se 3 (by rfl) ⟨2520608, by rfl⟩ : syracuseStep 13443245 = 5041217) B5041217
theorem B2990351 : Blo 1770086 2990351 := bstep (se 1 (by rfl) ⟨2242763, by rfl⟩ : syracuseStep 2990351 = 4485527) B4485527
theorem B17015339 : Blo 1770086 17015339 := bstep (se 1 (by rfl) ⟨12761504, by rfl⟩ : syracuseStep 17015339 = 25523009) B25523009
theorem B5980715 : Blo 1770086 5980715 := bstep (se 1 (by rfl) ⟨4485536, by rfl⟩ : syracuseStep 5980715 = 8971073) B8971073
theorem B1770119 : Blo 1770086 1770119 := bstep (se 1 (by rfl) ⟨1327589, by rfl⟩ : syracuseStep 1770119 = 2655179) B2655179
theorem B1770127 : Blo 1770086 1770127 := bstep (se 1 (by rfl) ⟨1327595, by rfl⟩ : syracuseStep 1770127 = 2655191) B2655191
theorem B4481689 : Blo 1770086 4481689 := bstep (se 2 (by rfl) ⟨1680633, by rfl⟩ : syracuseStep 4481689 = 3361267) B3361267
theorem B1770171 : Blo 1770086 1770171 := bstep (se 1 (by rfl) ⟨1327628, by rfl⟩ : syracuseStep 1770171 = 2655257) B2655257
theorem B1770247 : Blo 1770086 1770247 := bstep (se 1 (by rfl) ⟨1327685, by rfl⟩ : syracuseStep 1770247 = 2655371) B2655371
theorem B1770255 : Blo 1770086 1770255 := bstep (se 1 (by rfl) ⟨1327691, by rfl⟩ : syracuseStep 1770255 = 2655383) B2655383
theorem B43082533 : Blo 1770086 43082533 := bstep (se 4 (by rfl) ⟨4038987, by rfl⟩ : syracuseStep 43082533 = 8077975) B8077975
theorem B1770299 : Blo 1770086 1770299 := bstep (se 1 (by rfl) ⟨1327724, by rfl⟩ : syracuseStep 1770299 = 2655449) B2655449
theorem B4481851 : Blo 1770086 4481851 := bstep (se 1 (by rfl) ⟨3361388, by rfl⟩ : syracuseStep 4481851 = 6722777) B6722777
theorem B7562099 : Blo 1770086 7562099 := bstep (se 1 (by rfl) ⟨5671574, by rfl⟩ : syracuseStep 7562099 = 11343149) B11343149
theorem B1770375 : Blo 1770086 1770375 := bstep (se 1 (by rfl) ⟨1327781, by rfl⟩ : syracuseStep 1770375 = 2655563) B2655563
theorem B1770383 : Blo 1770086 1770383 := bstep (se 1 (by rfl) ⟨1327787, by rfl⟩ : syracuseStep 1770383 = 2655575) B2655575
theorem B2655161 : Blo 1770086 2655161 := bstep (se 2 (by rfl) ⟨995685, by rfl⟩ : syracuseStep 2655161 = 1991371) B1991371
theorem B1770427 : Blo 1770086 1770427 := bstep (se 1 (by rfl) ⟨1327820, by rfl⟩ : syracuseStep 1770427 = 2655641) B2655641
theorem B4481993 : Blo 1770086 4481993 := bstep (se 2 (by rfl) ⟨1680747, by rfl⟩ : syracuseStep 4481993 = 3361495) B3361495
theorem B5383169 : Blo 1770086 5383169 := bstep (se 2 (by rfl) ⟨2018688, by rfl⟩ : syracuseStep 5383169 = 4037377) B4037377
theorem B2655239 : Blo 1770086 2655239 := bstep (se 1 (by rfl) ⟨1991429, by rfl⟩ : syracuseStep 2655239 = 3982859) B3982859
theorem B1770503 : Blo 1770086 1770503 := bstep (se 1 (by rfl) ⟨1327877, by rfl⟩ : syracuseStep 1770503 = 2655755) B2655755
theorem B1991695 : Blo 1770086 1991695 := bstep (se 1 (by rfl) ⟨1493771, by rfl⟩ : syracuseStep 1991695 = 2987543) B2987543
theorem B1770511 : Blo 1770086 1770511 := bstep (se 1 (by rfl) ⟨1327883, by rfl⟩ : syracuseStep 1770511 = 2655767) B2655767
theorem B2655275 : Blo 1770086 2655275 := bstep (se 1 (by rfl) ⟨1991456, by rfl⟩ : syracuseStep 2655275 = 3982913) B3982913
theorem B1770555 : Blo 1770086 1770555 := bstep (se 1 (by rfl) ⟨1327916, by rfl⟩ : syracuseStep 1770555 = 2655833) B2655833
theorem B2655305 : Blo 1770086 2655305 := bstep (se 2 (by rfl) ⟨995739, by rfl⟩ : syracuseStep 2655305 = 1991479) B1991479
theorem B1770631 : Blo 1770086 1770631 := bstep (se 1 (by rfl) ⟨1327973, by rfl⟩ : syracuseStep 1770631 = 2655947) B2655947
theorem B1770639 : Blo 1770086 1770639 := bstep (se 1 (by rfl) ⟨1327979, by rfl⟩ : syracuseStep 1770639 = 2655959) B2655959
theorem B2655419 : Blo 1770086 2655419 := bstep (se 1 (by rfl) ⟨1991564, by rfl⟩ : syracuseStep 2655419 = 3983129) B3983129
theorem B1770683 : Blo 1770086 1770683 := bstep (se 1 (by rfl) ⟨1328012, by rfl⟩ : syracuseStep 1770683 = 2656025) B2656025
theorem B2655479 : Blo 1770086 2655479 := bstep (se 1 (by rfl) ⟨1991609, by rfl⟩ : syracuseStep 2655479 = 3983219) B3983219
theorem B1770759 : Blo 1770086 1770759 := bstep (se 1 (by rfl) ⟨1328069, by rfl⟩ : syracuseStep 1770759 = 2656139) B2656139
theorem B2655503 : Blo 1770086 2655503 := bstep (se 1 (by rfl) ⟨1991627, by rfl⟩ : syracuseStep 2655503 = 3983255) B3983255
theorem B1770767 : Blo 1770086 1770767 := bstep (se 1 (by rfl) ⟨1328075, by rfl⟩ : syracuseStep 1770767 = 2656151) B2656151
theorem B4482337 : Blo 1770086 4482337 := bstep (se 2 (by rfl) ⟨1680876, by rfl⟩ : syracuseStep 4482337 = 3361753) B3361753
theorem B9569573 : Blo 1770086 9569573 := bstep (se 4 (by rfl) ⟨897147, by rfl⟩ : syracuseStep 9569573 = 1794295) B1794295
theorem B2655545 : Blo 1770086 2655545 := bstep (se 2 (by rfl) ⟨995829, by rfl⟩ : syracuseStep 2655545 = 1991659) B1991659
theorem B1770811 : Blo 1770086 1770811 := bstep (se 1 (by rfl) ⟨1328108, by rfl⟩ : syracuseStep 1770811 = 2656217) B2656217
theorem B8512883 : Blo 1770086 8512883 := bstep (se 1 (by rfl) ⟨6384662, by rfl⟩ : syracuseStep 8512883 = 12769325) B12769325
theorem B20440451 : Blo 1770086 20440451 := bstep (se 1 (by rfl) ⟨15330338, by rfl⟩ : syracuseStep 20440451 = 30660677) B30660677
theorem B2655623 : Blo 1770086 2655623 := bstep (se 1 (by rfl) ⟨1991717, by rfl⟩ : syracuseStep 2655623 = 3983435) B3983435
theorem B1770887 : Blo 1770086 1770887 := bstep (se 1 (by rfl) ⟨1328165, by rfl⟩ : syracuseStep 1770887 = 2656331) B2656331
theorem B3835271 : Blo 1770086 3835271 := bstep (se 1 (by rfl) ⟨2876453, by rfl⟩ : syracuseStep 3835271 = 5752907) B5752907
theorem B1770895 : Blo 1770086 1770895 := bstep (se 1 (by rfl) ⟨1328171, by rfl⟩ : syracuseStep 1770895 = 2656343) B2656343
theorem B2655659 : Blo 1770086 2655659 := bstep (se 1 (by rfl) ⟨1991744, by rfl⟩ : syracuseStep 2655659 = 3983489) B3983489
theorem B1770939 : Blo 1770086 1770939 := bstep (se 1 (by rfl) ⟨1328204, by rfl⟩ : syracuseStep 1770939 = 2656409) B2656409
theorem B2655689 : Blo 1770086 2655689 := bstep (se 2 (by rfl) ⟨995883, by rfl⟩ : syracuseStep 2655689 = 1991767) B1991767
theorem B6727121 : Blo 1770086 6727121 := bstep (se 2 (by rfl) ⟨2522670, by rfl⟩ : syracuseStep 6727121 = 5045341) B5045341
theorem B1992199 : Blo 1770086 1992199 := bstep (se 1 (by rfl) ⟨1494149, by rfl⟩ : syracuseStep 1992199 = 2988299) B2988299
theorem B1771015 : Blo 1770086 1771015 := bstep (se 1 (by rfl) ⟨1328261, by rfl⟩ : syracuseStep 1771015 = 2656523) B2656523
theorem B1771023 : Blo 1770086 1771023 := bstep (se 1 (by rfl) ⟨1328267, by rfl⟩ : syracuseStep 1771023 = 2656535) B2656535
theorem B2655803 : Blo 1770086 2655803 := bstep (se 1 (by rfl) ⟨1991852, by rfl⟩ : syracuseStep 2655803 = 3983705) B3983705
theorem B1771067 : Blo 1770086 1771067 := bstep (se 1 (by rfl) ⟨1328300, by rfl⟩ : syracuseStep 1771067 = 2656601) B2656601
theorem B3982967 : Blo 1770086 3982967 := bstep (se 1 (by rfl) ⟨2987225, by rfl⟩ : syracuseStep 3982967 = 5974451) B5974451
theorem B2655863 : Blo 1770086 2655863 := bstep (se 1 (by rfl) ⟨1991897, by rfl⟩ : syracuseStep 2655863 = 3983795) B3983795
theorem B1771143 : Blo 1770086 1771143 := bstep (se 1 (by rfl) ⟨1328357, by rfl⟩ : syracuseStep 1771143 = 2656715) B2656715
theorem B2655887 : Blo 1770086 2655887 := bstep (se 1 (by rfl) ⟨1991915, by rfl⟩ : syracuseStep 2655887 = 3983831) B3983831
theorem B1771151 : Blo 1770086 1771151 := bstep (se 1 (by rfl) ⟨1328363, by rfl⟩ : syracuseStep 1771151 = 2656727) B2656727
theorem B2655929 : Blo 1770086 2655929 := bstep (se 2 (by rfl) ⟨995973, by rfl⟩ : syracuseStep 2655929 = 1991947) B1991947
theorem B1992379 : Blo 1770086 1992379 := bstep (se 1 (by rfl) ⟨1494284, by rfl⟩ : syracuseStep 1992379 = 2988569) B2988569
theorem B1771195 : Blo 1770086 1771195 := bstep (se 1 (by rfl) ⟨1328396, by rfl⟩ : syracuseStep 1771195 = 2656793) B2656793
theorem B2656007 : Blo 1770086 2656007 := bstep (se 1 (by rfl) ⟨1992005, by rfl⟩ : syracuseStep 2656007 = 3984011) B3984011
theorem B1771271 : Blo 1770086 1771271 := bstep (se 1 (by rfl) ⟨1328453, by rfl⟩ : syracuseStep 1771271 = 2656907) B2656907
theorem B1771279 : Blo 1770086 1771279 := bstep (se 1 (by rfl) ⟨1328459, by rfl⟩ : syracuseStep 1771279 = 2656919) B2656919
theorem B7563041 : Blo 1770086 7563041 := bstep (se 2 (by rfl) ⟨2836140, by rfl⟩ : syracuseStep 7563041 = 5672281) B5672281
theorem B6383393 : Blo 1770086 6383393 := bstep (se 2 (by rfl) ⟨2393772, by rfl⟩ : syracuseStep 6383393 = 4787545) B4787545
theorem B12764965 : Blo 1770086 12764965 := bstep (se 4 (by rfl) ⟨1196715, by rfl⟩ : syracuseStep 12764965 = 2393431) B2393431
theorem B3983147 : Blo 1770086 3983147 := bstep (se 1 (by rfl) ⟨2987360, by rfl⟩ : syracuseStep 3983147 = 5974721) B5974721
theorem B2656043 : Blo 1770086 2656043 := bstep (se 1 (by rfl) ⟨1992032, by rfl⟩ : syracuseStep 2656043 = 3984065) B3984065
theorem B1771323 : Blo 1770086 1771323 := bstep (se 1 (by rfl) ⟨1328492, by rfl⟩ : syracuseStep 1771323 = 2656985) B2656985
theorem B2656073 : Blo 1770086 2656073 := bstep (se 2 (by rfl) ⟨996027, by rfl⟩ : syracuseStep 2656073 = 1992055) B1992055
theorem B4482935 : Blo 1770086 4482935 := bstep (se 1 (by rfl) ⟨3362201, by rfl⟩ : syracuseStep 4482935 = 6724403) B6724403
theorem B1771399 : Blo 1770086 1771399 := bstep (se 1 (by rfl) ⟨1328549, by rfl⟩ : syracuseStep 1771399 = 2657099) B2657099
theorem B1771407 : Blo 1770086 1771407 := bstep (se 1 (by rfl) ⟨1328555, by rfl⟩ : syracuseStep 1771407 = 2657111) B2657111
theorem B14354329 : Blo 1770086 14354329 := bstep (se 2 (by rfl) ⟨5382873, by rfl⟩ : syracuseStep 14354329 = 10765747) B10765747
theorem B2656187 : Blo 1770086 2656187 := bstep (se 1 (by rfl) ⟨1992140, by rfl⟩ : syracuseStep 2656187 = 3984281) B3984281
theorem B1771451 : Blo 1770086 1771451 := bstep (se 1 (by rfl) ⟨1328588, by rfl⟩ : syracuseStep 1771451 = 2657177) B2657177
theorem B10086353 : Blo 1770086 10086353 := bstep (se 2 (by rfl) ⟨3782382, by rfl⟩ : syracuseStep 10086353 = 7564765) B7564765
theorem B2656247 : Blo 1770086 2656247 := bstep (se 1 (by rfl) ⟨1992185, by rfl⟩ : syracuseStep 2656247 = 3984371) B3984371
theorem B1771527 : Blo 1770086 1771527 := bstep (se 1 (by rfl) ⟨1328645, by rfl⟩ : syracuseStep 1771527 = 2657291) B2657291
theorem B8964107 : Blo 1770086 8964107 := bstep (se 1 (by rfl) ⟨6723080, by rfl⟩ : syracuseStep 8964107 = 13446161) B13446161
theorem B76638221 : Blo 1770086 76638221 := bstep (se 3 (by rfl) ⟨14369666, by rfl⟩ : syracuseStep 76638221 = 28739333) B28739333
theorem B2656271 : Blo 1770086 2656271 := bstep (se 1 (by rfl) ⟨1992203, by rfl⟩ : syracuseStep 2656271 = 3984407) B3984407
theorem B1771535 : Blo 1770086 1771535 := bstep (se 1 (by rfl) ⟨1328651, by rfl⟩ : syracuseStep 1771535 = 2657303) B2657303
theorem B3360827 : Blo 1770086 3360827 := bstep (se 1 (by rfl) ⟨2520620, by rfl⟩ : syracuseStep 3360827 = 5041241) B5041241
theorem B2656313 : Blo 1770086 2656313 := bstep (se 2 (by rfl) ⟨996117, by rfl⟩ : syracuseStep 2656313 = 1992235) B1992235
theorem B1771579 : Blo 1770086 1771579 := bstep (se 1 (by rfl) ⟨1328684, by rfl⟩ : syracuseStep 1771579 = 2657369) B2657369
theorem B2656391 : Blo 1770086 2656391 := bstep (se 1 (by rfl) ⟨1992293, by rfl⟩ : syracuseStep 2656391 = 3984587) B3984587
theorem B1771655 : Blo 1770086 1771655 := bstep (se 1 (by rfl) ⟨1328741, by rfl⟩ : syracuseStep 1771655 = 2657483) B2657483
theorem B1992847 : Blo 1770086 1992847 := bstep (se 1 (by rfl) ⟨1494635, by rfl⟩ : syracuseStep 1992847 = 2989271) B2989271
theorem B1771663 : Blo 1770086 1771663 := bstep (se 1 (by rfl) ⟨1328747, by rfl⟩ : syracuseStep 1771663 = 2657495) B2657495
theorem B3983507 : Blo 1770086 3983507 := bstep (se 1 (by rfl) ⟨2987630, by rfl⟩ : syracuseStep 3983507 = 5975261) B5975261
theorem B2656427 : Blo 1770086 2656427 := bstep (se 1 (by rfl) ⟨1992320, by rfl⟩ : syracuseStep 2656427 = 3984641) B3984641
theorem B8964269 : Blo 1770086 8964269 := bstep (se 3 (by rfl) ⟨1680800, by rfl⟩ : syracuseStep 8964269 = 3361601) B3361601
theorem B1771707 : Blo 1770086 1771707 := bstep (se 1 (by rfl) ⟨1328780, by rfl⟩ : syracuseStep 1771707 = 2657561) B2657561
theorem B3983561 : Blo 1770086 3983561 := bstep (se 2 (by rfl) ⟨1493835, by rfl⟩ : syracuseStep 3983561 = 2987671) B2987671
theorem B2656457 : Blo 1770086 2656457 := bstep (se 2 (by rfl) ⟨996171, by rfl⟩ : syracuseStep 2656457 = 1992343) B1992343
theorem B1771783 : Blo 1770086 1771783 := bstep (se 1 (by rfl) ⟨1328837, by rfl⟩ : syracuseStep 1771783 = 2657675) B2657675
theorem B1771791 : Blo 1770086 1771791 := bstep (se 1 (by rfl) ⟨1328843, by rfl⟩ : syracuseStep 1771791 = 2657687) B2657687
theorem B2656571 : Blo 1770086 2656571 := bstep (se 1 (by rfl) ⟨1992428, by rfl⟩ : syracuseStep 2656571 = 3984857) B3984857
theorem B1771835 : Blo 1770086 1771835 := bstep (se 1 (by rfl) ⟨1328876, by rfl⟩ : syracuseStep 1771835 = 2657753) B2657753
theorem B2656631 : Blo 1770086 2656631 := bstep (se 1 (by rfl) ⟨1992473, by rfl⟩ : syracuseStep 2656631 = 3984947) B3984947
theorem B1771911 : Blo 1770086 1771911 := bstep (se 1 (by rfl) ⟨1328933, by rfl⟩ : syracuseStep 1771911 = 2657867) B2657867
theorem B2656655 : Blo 1770086 2656655 := bstep (se 1 (by rfl) ⟨1992491, by rfl⟩ : syracuseStep 2656655 = 3984983) B3984983
theorem B1771919 : Blo 1770086 1771919 := bstep (se 1 (by rfl) ⟨1328939, by rfl⟩ : syracuseStep 1771919 = 2657879) B2657879
theorem B2656697 : Blo 1770086 2656697 := bstep (se 2 (by rfl) ⟨996261, by rfl⟩ : syracuseStep 2656697 = 1992523) B1992523
theorem B1771963 : Blo 1770086 1771963 := bstep (se 1 (by rfl) ⟨1328972, by rfl⟩ : syracuseStep 1771963 = 2657945) B2657945
theorem B16148945 : Blo 1770086 16148945 := bstep (se 2 (by rfl) ⟨6055854, by rfl⟩ : syracuseStep 16148945 = 12111709) B12111709
theorem B2656775 : Blo 1770086 2656775 := bstep (se 1 (by rfl) ⟨1992581, by rfl⟩ : syracuseStep 2656775 = 3985163) B3985163
theorem B1772039 : Blo 1770086 1772039 := bstep (se 1 (by rfl) ⟨1329029, by rfl⟩ : syracuseStep 1772039 = 2658059) B2658059
theorem B1772047 : Blo 1770086 1772047 := bstep (se 1 (by rfl) ⟨1329035, by rfl⟩ : syracuseStep 1772047 = 2658071) B2658071
theorem B3361313 : Blo 1770086 3361313 := bstep (se 2 (by rfl) ⟨1260492, by rfl⟩ : syracuseStep 3361313 = 2520985) B2520985
theorem B13445675 : Blo 1770086 13445675 := bstep (se 1 (by rfl) ⟨10084256, by rfl⟩ : syracuseStep 13445675 = 20168513) B20168513
theorem B2656811 : Blo 1770086 2656811 := bstep (se 1 (by rfl) ⟨1992608, by rfl⟩ : syracuseStep 2656811 = 3985217) B3985217
theorem B2656841 : Blo 1770086 2656841 := bstep (se 2 (by rfl) ⟨996315, by rfl⟩ : syracuseStep 2656841 = 1992631) B1992631
theorem B1993351 : Blo 1770086 1993351 := bstep (se 1 (by rfl) ⟨1495013, by rfl⟩ : syracuseStep 1993351 = 2990027) B2990027
theorem B2656955 : Blo 1770086 2656955 := bstep (se 1 (by rfl) ⟨1992716, by rfl⟩ : syracuseStep 2656955 = 3985433) B3985433
theorem B6384329 : Blo 1770086 6384329 := bstep (se 2 (by rfl) ⟨2394123, by rfl⟩ : syracuseStep 6384329 = 4788247) B4788247
theorem B7564013 : Blo 1770086 7564013 := bstep (se 3 (by rfl) ⟨1418252, by rfl⟩ : syracuseStep 7564013 = 2836505) B2836505
theorem B2657015 : Blo 1770086 2657015 := bstep (se 1 (by rfl) ⟨1992761, by rfl⟩ : syracuseStep 2657015 = 3985523) B3985523
theorem B2657039 : Blo 1770086 2657039 := bstep (se 1 (by rfl) ⟨1992779, by rfl⟩ : syracuseStep 2657039 = 3985559) B3985559
theorem B2657081 : Blo 1770086 2657081 := bstep (se 2 (by rfl) ⟨996405, by rfl⟩ : syracuseStep 2657081 = 1992811) B1992811
theorem B1993531 : Blo 1770086 1993531 := bstep (se 1 (by rfl) ⟨1495148, by rfl⟩ : syracuseStep 1993531 = 2990297) B2990297
theorem B4787059 : Blo 1770086 4787059 := bstep (se 1 (by rfl) ⟨3590294, by rfl⟩ : syracuseStep 4787059 = 7180589) B7180589
theorem B3361655 : Blo 1770086 3361655 := bstep (se 1 (by rfl) ⟨2521241, by rfl⟩ : syracuseStep 3361655 = 5042483) B5042483
theorem B3984263 : Blo 1770086 3984263 := bstep (se 1 (by rfl) ⟨2988197, by rfl⟩ : syracuseStep 3984263 = 5976395) B5976395
theorem B2657159 : Blo 1770086 2657159 := bstep (se 1 (by rfl) ⟨1992869, by rfl⟩ : syracuseStep 2657159 = 3985739) B3985739
theorem B7670663 : Blo 1770086 7670663 := bstep (se 1 (by rfl) ⟨5752997, by rfl⟩ : syracuseStep 7670663 = 11505995) B11505995
theorem B5974937 : Blo 1770086 5974937 := bstep (se 2 (by rfl) ⟨2240601, by rfl⟩ : syracuseStep 5974937 = 4481203) B4481203
theorem B64621475 : Blo 1770086 64621475 := bstep (se 1 (by rfl) ⟨48466106, by rfl⟩ : syracuseStep 64621475 = 96932213) B96932213
theorem B2657195 : Blo 1770086 2657195 := bstep (se 1 (by rfl) ⟨1992896, by rfl⟩ : syracuseStep 2657195 = 3985793) B3985793
theorem B2657225 : Blo 1770086 2657225 := bstep (se 2 (by rfl) ⟨996459, by rfl⟩ : syracuseStep 2657225 = 1992919) B1992919
theorem B68103179 : Blo 1770086 68103179 := bstep (se 1 (by rfl) ⟨51077384, by rfl⟩ : syracuseStep 68103179 = 102154769) B102154769
theorem B3984443 : Blo 1770086 3984443 := bstep (se 1 (by rfl) ⟨2988332, by rfl⟩ : syracuseStep 3984443 = 5976665) B5976665
theorem B2657339 : Blo 1770086 2657339 := bstep (se 1 (by rfl) ⟨1993004, by rfl⟩ : syracuseStep 2657339 = 3986009) B3986009
theorem B13454423 : Blo 1770086 13454423 := bstep (se 1 (by rfl) ⟨10090817, by rfl⟩ : syracuseStep 13454423 = 20181635) B20181635
theorem B2657399 : Blo 1770086 2657399 := bstep (se 1 (by rfl) ⟨1993049, by rfl⟩ : syracuseStep 2657399 = 3986099) B3986099
theorem B4484231 : Blo 1770086 4484231 := bstep (se 1 (by rfl) ⟨3363173, by rfl⟩ : syracuseStep 4484231 = 6726347) B6726347
theorem B2657423 : Blo 1770086 2657423 := bstep (se 1 (by rfl) ⟨1993067, by rfl⟩ : syracuseStep 2657423 = 3986135) B3986135
theorem B3984569 : Blo 1770086 3984569 := bstep (se 2 (by rfl) ⟨1494213, by rfl⟩ : syracuseStep 3984569 = 2988427) B2988427
theorem B4484281 : Blo 1770086 4484281 := bstep (se 2 (by rfl) ⟨1681605, by rfl⟩ : syracuseStep 4484281 = 3363211) B3363211
theorem B2657465 : Blo 1770086 2657465 := bstep (se 2 (by rfl) ⟨996549, by rfl⟩ : syracuseStep 2657465 = 1993099) B1993099
theorem B12766409 : Blo 1770086 12766409 := bstep (se 2 (by rfl) ⟨4787403, by rfl⟩ : syracuseStep 12766409 = 9574807) B9574807
theorem B2657543 : Blo 1770086 2657543 := bstep (se 1 (by rfl) ⟨1993157, by rfl⟩ : syracuseStep 2657543 = 3986315) B3986315
theorem B4787467 : Blo 1770086 4787467 := bstep (se 1 (by rfl) ⟨3590600, by rfl⟩ : syracuseStep 4787467 = 7181201) B7181201
theorem B13634849 : Blo 1770086 13634849 := bstep (se 2 (by rfl) ⟨5113068, by rfl⟩ : syracuseStep 13634849 = 10226137) B10226137
theorem B2657579 : Blo 1770086 2657579 := bstep (se 1 (by rfl) ⟨1993184, by rfl⟩ : syracuseStep 2657579 = 3986369) B3986369
theorem B40906043 : Blo 1770086 40906043 := bstep (se 1 (by rfl) ⟨30679532, by rfl⟩ : syracuseStep 40906043 = 61359065) B61359065
theorem B2657609 : Blo 1770086 2657609 := bstep (se 2 (by rfl) ⟨996603, by rfl⟩ : syracuseStep 2657609 = 1993207) B1993207
theorem B7564697 : Blo 1770086 7564697 := bstep (se 2 (by rfl) ⟨2836761, by rfl⟩ : syracuseStep 7564697 = 5673523) B5673523
theorem B2657723 : Blo 1770086 2657723 := bstep (se 1 (by rfl) ⟨1993292, by rfl⟩ : syracuseStep 2657723 = 3986585) B3986585
theorem B2657783 : Blo 1770086 2657783 := bstep (se 1 (by rfl) ⟨1993337, by rfl⟩ : syracuseStep 2657783 = 3986675) B3986675
theorem B8506883 : Blo 1770086 8506883 := bstep (se 1 (by rfl) ⟨6380162, by rfl⟩ : syracuseStep 8506883 = 12760325) B12760325
theorem B3984911 : Blo 1770086 3984911 := bstep (se 1 (by rfl) ⟨2988683, by rfl⟩ : syracuseStep 3984911 = 5977367) B5977367
theorem B2657807 : Blo 1770086 2657807 := bstep (se 1 (by rfl) ⟨1993355, by rfl⟩ : syracuseStep 2657807 = 3986711) B3986711
theorem B3984929 : Blo 1770086 3984929 := bstep (se 2 (by rfl) ⟨1494348, by rfl⟩ : syracuseStep 3984929 = 2988697) B2988697
theorem B4541995 : Blo 1770086 4541995 := bstep (se 1 (by rfl) ⟨3406496, by rfl⟩ : syracuseStep 4541995 = 6812993) B6812993
theorem B20164139 : Blo 1770086 20164139 := bstep (se 1 (by rfl) ⟨15123104, by rfl⟩ : syracuseStep 20164139 = 30246209) B30246209
theorem B2657849 : Blo 1770086 2657849 := bstep (se 2 (by rfl) ⟨996693, by rfl⟩ : syracuseStep 2657849 = 1993387) B1993387
theorem B5975639 : Blo 1770086 5975639 := bstep (se 1 (by rfl) ⟨4481729, by rfl⟩ : syracuseStep 5975639 = 8963459) B8963459
theorem B2657927 : Blo 1770086 2657927 := bstep (se 1 (by rfl) ⟨1993445, by rfl⟩ : syracuseStep 2657927 = 3986891) B3986891
theorem B2657963 : Blo 1770086 2657963 := bstep (se 1 (by rfl) ⟨1993472, by rfl⟩ : syracuseStep 2657963 = 3986945) B3986945
theorem B2657993 : Blo 1770086 2657993 := bstep (se 2 (by rfl) ⟨996747, by rfl⟩ : syracuseStep 2657993 = 1993495) B1993495
theorem B16158437 : Blo 1770086 16158437 := bstep (se 4 (by rfl) ⟨1514853, by rfl⟩ : syracuseStep 16158437 = 3029707) B3029707
theorem B8965889 : Blo 1770086 8965889 := bstep (se 2 (by rfl) ⟨3362208, by rfl⟩ : syracuseStep 8965889 = 6724417) B6724417
theorem B54529793 : Blo 1770086 54529793 := bstep (se 2 (by rfl) ⟨20448672, by rfl⟩ : syracuseStep 54529793 = 40897345) B40897345
theorem B4484879 : Blo 1770086 4484879 := bstep (se 1 (by rfl) ⟨3363659, by rfl⟩ : syracuseStep 4484879 = 6727319) B6727319
theorem B4788011 : Blo 1770086 4788011 := bstep (se 1 (by rfl) ⟨3591008, by rfl⟩ : syracuseStep 4788011 = 7182017) B7182017
theorem B2658107 : Blo 1770086 2658107 := bstep (se 1 (by rfl) ⟨1993580, by rfl⟩ : syracuseStep 2658107 = 3987161) B3987161
theorem B3985271 : Blo 1770086 3985271 := bstep (se 1 (by rfl) ⟨2988953, by rfl⟩ : syracuseStep 3985271 = 5977907) B5977907
theorem B2240399 : Blo 1770086 2240399 := bstep (se 1 (by rfl) ⟨1680299, by rfl⟩ : syracuseStep 2240399 = 3360599) B3360599
theorem B13627403 : Blo 1770086 13627403 := bstep (se 1 (by rfl) ⟨10220552, by rfl⟩ : syracuseStep 13627403 = 20441105) B20441105
theorem B5042209 : Blo 1770086 5042209 := bstep (se 2 (by rfl) ⟨1890828, by rfl⟩ : syracuseStep 5042209 = 3781657) B3781657
theorem B4255777 : Blo 1770086 4255777 := bstep (se 2 (by rfl) ⟨1595916, by rfl⟩ : syracuseStep 4255777 = 3191833) B3191833
theorem B3985451 : Blo 1770086 3985451 := bstep (se 1 (by rfl) ⟨2989088, by rfl⟩ : syracuseStep 3985451 = 5978177) B5978177
theorem B5976125 : Blo 1770086 5976125 := bstep (se 3 (by rfl) ⟨1120523, by rfl⟩ : syracuseStep 5976125 = 2241047) B2241047
theorem B17256509 : Blo 1770086 17256509 := bstep (se 3 (by rfl) ⟨3235595, by rfl⟩ : syracuseStep 17256509 = 6471191) B6471191
theorem B20172887 : Blo 1770086 20172887 := bstep (se 1 (by rfl) ⟨15129665, by rfl⟩ : syracuseStep 20172887 = 30259331) B30259331
theorem B11342227 : Blo 1770086 11342227 := bstep (se 1 (by rfl) ⟨8506670, by rfl⟩ : syracuseStep 11342227 = 17013341) B17013341
theorem B3985811 : Blo 1770086 3985811 := bstep (se 1 (by rfl) ⟨2989358, by rfl⟩ : syracuseStep 3985811 = 5978717) B5978717
theorem B3363257 : Blo 1770086 3363257 := bstep (se 2 (by rfl) ⟨1261221, by rfl⟩ : syracuseStep 3363257 = 2522443) B2522443
theorem B3985865 : Blo 1770086 3985865 := bstep (se 2 (by rfl) ⟨1494699, by rfl⟩ : syracuseStep 3985865 = 2989399) B2989399
theorem B4485577 : Blo 1770086 4485577 := bstep (se 2 (by rfl) ⟨1682091, by rfl⟩ : syracuseStep 4485577 = 3364183) B3364183
theorem B38277593 : Blo 1770086 38277593 := bstep (se 2 (by rfl) ⟨14354097, by rfl⟩ : syracuseStep 38277593 = 28708195) B28708195
theorem B5042699 : Blo 1770086 5042699 := bstep (se 1 (by rfl) ⟨3782024, by rfl⟩ : syracuseStep 5042699 = 7564049) B7564049
theorem B3191329 : Blo 1770086 3191329 := bstep (se 2 (by rfl) ⟨1196748, by rfl⟩ : syracuseStep 3191329 = 2393497) B2393497
theorem B8966699 : Blo 1770086 8966699 := bstep (se 1 (by rfl) ⟨6725024, by rfl⟩ : syracuseStep 8966699 = 13450049) B13450049
theorem B3781255 : Blo 1770086 3781255 := bstep (se 1 (by rfl) ⟨2835941, by rfl⟩ : syracuseStep 3781255 = 5671883) B5671883
theorem B3363599 : Blo 1770086 3363599 := bstep (se 1 (by rfl) ⟨2522699, by rfl⟩ : syracuseStep 3363599 = 5045399) B5045399
theorem B8631073 : Blo 1770086 8631073 := bstep (se 2 (by rfl) ⟨3236652, by rfl⟩ : syracuseStep 8631073 = 6473305) B6473305
theorem B2987023 : Blo 1770086 2987023 := bstep (se 1 (by rfl) ⟨2240267, by rfl⟩ : syracuseStep 2987023 = 4480535) B4480535
theorem B3986567 : Blo 1770086 3986567 := bstep (se 1 (by rfl) ⟨2989925, by rfl⟩ : syracuseStep 3986567 = 5979851) B5979851
theorem B5387411 : Blo 1770086 5387411 := bstep (se 1 (by rfl) ⟨4040558, by rfl⟩ : syracuseStep 5387411 = 8081117) B8081117
theorem B28718317 : Blo 1770086 28718317 := bstep (se 3 (by rfl) ⟨5384684, by rfl⟩ : syracuseStep 28718317 = 10769369) B10769369
theorem B2692367 : Blo 1770086 2692367 := bstep (se 1 (by rfl) ⟨2019275, by rfl⟩ : syracuseStep 2692367 = 4038551) B4038551
theorem B5043485 : Blo 1770086 5043485 := bstep (se 3 (by rfl) ⟨945653, by rfl⟩ : syracuseStep 5043485 = 1891307) B1891307
theorem B3986747 : Blo 1770086 3986747 := bstep (se 1 (by rfl) ⟨2990060, by rfl⟩ : syracuseStep 3986747 = 5980121) B5980121
theorem B5387581 : Blo 1770086 5387581 := bstep (se 3 (by rfl) ⟨1010171, by rfl⟩ : syracuseStep 5387581 = 2020343) B2020343
theorem B5977529 : Blo 1770086 5977529 := bstep (se 2 (by rfl) ⟨2241573, by rfl⟩ : syracuseStep 5977529 = 4483147) B4483147
theorem B5387705 : Blo 1770086 5387705 := bstep (se 2 (by rfl) ⟨2020389, by rfl⟩ : syracuseStep 5387705 = 4040779) B4040779
theorem B3986873 : Blo 1770086 3986873 := bstep (se 2 (by rfl) ⟨1495077, by rfl⟩ : syracuseStep 3986873 = 2990155) B2990155
theorem B28734925 : Blo 1770086 28734925 := bstep (se 3 (by rfl) ⟨5387798, by rfl⟩ : syracuseStep 28734925 = 10775597) B10775597
theorem B2987563 : Blo 1770086 2987563 := bstep (se 1 (by rfl) ⟨2240672, by rfl⟩ : syracuseStep 2987563 = 4481345) B4481345
theorem B14358059 : Blo 1770086 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B2520649 : Blo 1770086 2520649 := bstep (se 2 (by rfl) ⟨945243, by rfl⟩ : syracuseStep 2520649 = 1890487) B1890487
theorem B38311501 : Blo 1770086 38311501 := bstep (se 3 (by rfl) ⟨7183406, by rfl⟩ : syracuseStep 38311501 = 14366813) B14366813
theorem B4789847 : Blo 1770086 4789847 := bstep (se 1 (by rfl) ⟨3592385, by rfl⟩ : syracuseStep 4789847 = 7184771) B7184771
theorem B2987705 : Blo 1770086 2987705 := bstep (se 2 (by rfl) ⟨1120389, by rfl⟩ : syracuseStep 2987705 = 2240779) B2240779
theorem B15128369 : Blo 1770086 15128369 := bstep (se 2 (by rfl) ⟨5673138, by rfl⟩ : syracuseStep 15128369 = 11346277) B11346277
theorem B22697779 : Blo 1770086 22697779 := bstep (se 1 (by rfl) ⟨17023334, by rfl⟩ : syracuseStep 22697779 = 34046669) B34046669
theorem B8967995 : Blo 1770086 8967995 := bstep (se 1 (by rfl) ⟨6725996, by rfl⟩ : syracuseStep 8967995 = 13451993) B13451993
theorem B32765771 : Blo 1770086 32765771 := bstep (se 1 (by rfl) ⟨24574328, by rfl⟩ : syracuseStep 32765771 = 49148657) B49148657
theorem B4257623 : Blo 1770086 4257623 := bstep (se 1 (by rfl) ⟨3193217, by rfl⟩ : syracuseStep 4257623 = 6386435) B6386435
theorem B17028953 : Blo 1770086 17028953 := bstep (se 2 (by rfl) ⟨6385857, by rfl⟩ : syracuseStep 17028953 = 12771715) B12771715
theorem B8968157 : Blo 1770086 8968157 := bstep (se 3 (by rfl) ⟨1681529, by rfl⟩ : syracuseStep 8968157 = 3363059) B3363059
theorem B5978123 : Blo 1770086 5978123 := bstep (se 1 (by rfl) ⟨4483592, by rfl⟩ : syracuseStep 5978123 = 8967185) B8967185
theorem B25524341 : Blo 1770086 25524341 := bstep (se 5 (by rfl) ⟨1196453, by rfl⟩ : syracuseStep 25524341 = 2392907) B2392907
theorem B5978231 : Blo 1770086 5978231 := bstep (se 1 (by rfl) ⟨4483673, by rfl⟩ : syracuseStep 5978231 = 8967347) B8967347
theorem B19159213 : Blo 1770086 19159213 := bstep (se 3 (by rfl) ⟨3592352, by rfl⟩ : syracuseStep 19159213 = 7184705) B7184705
theorem B8968481 : Blo 1770086 8968481 := bstep (se 2 (by rfl) ⟨3363180, by rfl⟩ : syracuseStep 8968481 = 6726361) B6726361
theorem B36854081 : Blo 1770086 36854081 := bstep (se 2 (by rfl) ⟨13820280, by rfl⟩ : syracuseStep 36854081 = 27640561) B27640561
theorem B2988407 : Blo 1770086 2988407 := bstep (se 1 (by rfl) ⟨2241305, by rfl⟩ : syracuseStep 2988407 = 4482611) B4482611
theorem B5978825 : Blo 1770086 5978825 := bstep (se 2 (by rfl) ⟨2242059, by rfl⟩ : syracuseStep 5978825 = 4484119) B4484119
theorem B129235661 : Blo 1770086 129235661 := bstep (se 3 (by rfl) ⟨24231686, by rfl⟩ : syracuseStep 129235661 = 48463373) B48463373
theorem B12770099 : Blo 1770086 12770099 := bstep (se 1 (by rfl) ⟨9577574, by rfl⟩ : syracuseStep 12770099 = 19155149) B19155149
theorem B2988859 : Blo 1770086 2988859 := bstep (se 1 (by rfl) ⟨2241644, by rfl⟩ : syracuseStep 2988859 = 4483289) B4483289
theorem B2128783 : Blo 1770086 2128783 := bstep (se 1 (by rfl) ⟨1596587, by rfl⟩ : syracuseStep 2128783 = 3193175) B3193175
theorem B10091411 : Blo 1770086 10091411 := bstep (se 1 (by rfl) ⟨7568558, by rfl⟩ : syracuseStep 10091411 = 15137117) B15137117
theorem B2989001 : Blo 1770086 2989001 := bstep (se 2 (by rfl) ⟨1120875, by rfl⟩ : syracuseStep 2989001 = 2241751) B2241751
theorem B8969453 : Blo 1770086 8969453 := bstep (se 3 (by rfl) ⟨1681772, by rfl⟩ : syracuseStep 8969453 = 3363545) B3363545
theorem B5045591 : Blo 1770086 5045591 := bstep (se 1 (by rfl) ⟨3784193, by rfl⟩ : syracuseStep 5045591 = 7568387) B7568387
theorem B5979527 : Blo 1770086 5979527 := bstep (se 1 (by rfl) ⟨4484645, by rfl⟩ : syracuseStep 5979527 = 8969291) B8969291
theorem B10091911 : Blo 1770086 10091911 := bstep (se 1 (by rfl) ⟨7568933, by rfl⟩ : syracuseStep 10091911 = 15137867) B15137867
theorem B12279185 : Blo 1770086 12279185 := bstep (se 2 (by rfl) ⟨4604694, by rfl⟩ : syracuseStep 12279185 = 9209389) B9209389
theorem B5111225 : Blo 1770086 5111225 := bstep (se 2 (by rfl) ⟨1916709, by rfl⟩ : syracuseStep 5111225 = 3833419) B3833419
theorem B17022413 : Blo 1770086 17022413 := bstep (se 3 (by rfl) ⟨3191702, by rfl⟩ : syracuseStep 17022413 = 6383405) B6383405
theorem B21536209 : Blo 1770086 21536209 := bstep (se 2 (by rfl) ⟨8076078, by rfl⟩ : syracuseStep 21536209 = 16152157) B16152157
theorem B48455171 : Blo 1770086 48455171 := bstep (se 1 (by rfl) ⟨36341378, by rfl⟩ : syracuseStep 48455171 = 72682757) B72682757
theorem B4480555 : Blo 1770086 4480555 := bstep (se 1 (by rfl) ⟨3360416, by rfl⟩ : syracuseStep 4480555 = 6720833) B6720833
theorem B5676587 : Blo 1770086 5676587 := bstep (se 1 (by rfl) ⟨4257440, by rfl⟩ : syracuseStep 5676587 = 8514881) B8514881
theorem B6725207 : Blo 1770086 6725207 := bstep (se 1 (by rfl) ⟨5043905, by rfl⟩ : syracuseStep 6725207 = 10087811) B10087811
theorem B2989703 : Blo 1770086 2989703 := bstep (se 1 (by rfl) ⟨2242277, by rfl⟩ : syracuseStep 2989703 = 4484555) B4484555
theorem B4480697 : Blo 1770086 4480697 := bstep (se 2 (by rfl) ⟨1680261, by rfl⟩ : syracuseStep 4480697 = 3360523) B3360523
theorem B5979905 : Blo 1770086 5979905 := bstep (se 2 (by rfl) ⟨2242464, by rfl⟩ : syracuseStep 5979905 = 4484929) B4484929
theorem B72720179 : Blo 1770086 72720179 := bstep (se 1 (by rfl) ⟨54540134, by rfl⟩ : syracuseStep 72720179 = 109080269) B109080269
theorem B8962001 : Blo 1770086 8962001 := bstep (se 2 (by rfl) ⟨3360750, by rfl⟩ : syracuseStep 8962001 = 6721501) B6721501
theorem B9084935 : Blo 1770086 9084935 := bstep (se 1 (by rfl) ⟨6813701, by rfl⟩ : syracuseStep 9084935 = 13627403) B13627403
theorem B5980175 : Blo 1770086 5980175 := bstep (se 1 (by rfl) ⟨4485131, by rfl⟩ : syracuseStep 5980175 = 8970263) B8970263
theorem B8962163 : Blo 1770086 8962163 := bstep (se 1 (by rfl) ⟨6721622, by rfl⟩ : syracuseStep 8962163 = 13443245) B13443245
theorem B25518395 : Blo 1770086 25518395 := bstep (se 1 (by rfl) ⟨19138796, by rfl⟩ : syracuseStep 25518395 = 38277593) B38277593
theorem B15122969 : Blo 1770086 15122969 := bstep (se 2 (by rfl) ⟨5671113, by rfl⟩ : syracuseStep 15122969 = 11342227) B11342227
theorem B5980769 : Blo 1770086 5980769 := bstep (se 2 (by rfl) ⟨2242788, by rfl⟩ : syracuseStep 5980769 = 4485577) B4485577
theorem B1770107 : Blo 1770086 1770107 := bstep (se 1 (by rfl) ⟨1327580, by rfl⟩ : syracuseStep 1770107 = 2655161) B2655161
theorem B3588779 : Blo 1770086 3588779 := bstep (se 1 (by rfl) ⟨2691584, by rfl⟩ : syracuseStep 3588779 = 5383169) B5383169
theorem B1770159 : Blo 1770086 1770159 := bstep (se 1 (by rfl) ⟨1327619, by rfl⟩ : syracuseStep 1770159 = 2655239) B2655239
theorem B1770183 : Blo 1770086 1770183 := bstep (se 1 (by rfl) ⟨1327637, by rfl⟩ : syracuseStep 1770183 = 2655275) B2655275
theorem B1770203 : Blo 1770086 1770203 := bstep (se 1 (by rfl) ⟨1327652, by rfl⟩ : syracuseStep 1770203 = 2655305) B2655305
theorem B1770279 : Blo 1770086 1770279 := bstep (se 1 (by rfl) ⟨1327709, by rfl⟩ : syracuseStep 1770279 = 2655419) B2655419
theorem B1770319 : Blo 1770086 1770319 := bstep (se 1 (by rfl) ⟨1327739, by rfl⟩ : syracuseStep 1770319 = 2655479) B2655479
theorem B1770335 : Blo 1770086 1770335 := bstep (se 1 (by rfl) ⟨1327751, by rfl⟩ : syracuseStep 1770335 = 2655503) B2655503
theorem B1794911 : Blo 1770086 1794911 := bstep (se 1 (by rfl) ⟨1346183, by rfl⟩ : syracuseStep 1794911 = 2692367) B2692367
theorem B1770363 : Blo 1770086 1770363 := bstep (se 1 (by rfl) ⟨1327772, by rfl⟩ : syracuseStep 1770363 = 2655545) B2655545
theorem B1770415 : Blo 1770086 1770415 := bstep (se 1 (by rfl) ⟨1327811, by rfl⟩ : syracuseStep 1770415 = 2655623) B2655623
theorem B2556847 : Blo 1770086 2556847 := bstep (se 1 (by rfl) ⟨1917635, by rfl⟩ : syracuseStep 2556847 = 3835271) B3835271
theorem B1770439 : Blo 1770086 1770439 := bstep (se 1 (by rfl) ⟨1327829, by rfl⟩ : syracuseStep 1770439 = 2655659) B2655659
theorem B1770459 : Blo 1770086 1770459 := bstep (se 1 (by rfl) ⟨1327844, by rfl⟩ : syracuseStep 1770459 = 2655689) B2655689
theorem B1770535 : Blo 1770086 1770535 := bstep (se 1 (by rfl) ⟨1327901, by rfl⟩ : syracuseStep 1770535 = 2655803) B2655803
theorem B57443377 : Blo 1770086 57443377 := bstep (se 2 (by rfl) ⟨21541266, by rfl⟩ : syracuseStep 57443377 = 43082533) B43082533
theorem B2655311 : Blo 1770086 2655311 := bstep (se 1 (by rfl) ⟨1991483, by rfl⟩ : syracuseStep 2655311 = 3982967) B3982967
theorem B1770575 : Blo 1770086 1770575 := bstep (se 1 (by rfl) ⟨1327931, by rfl⟩ : syracuseStep 1770575 = 2655863) B2655863
theorem B1770591 : Blo 1770086 1770591 := bstep (se 1 (by rfl) ⟨1327943, by rfl⟩ : syracuseStep 1770591 = 2655887) B2655887
theorem B1991803 : Blo 1770086 1991803 := bstep (se 1 (by rfl) ⟨1493852, by rfl⟩ : syracuseStep 1991803 = 2987705) B2987705
theorem B1770619 : Blo 1770086 1770619 := bstep (se 1 (by rfl) ⟨1327964, by rfl⟩ : syracuseStep 1770619 = 2655929) B2655929
theorem B6382745 : Blo 1770086 6382745 := bstep (se 2 (by rfl) ⟨2393529, by rfl⟩ : syracuseStep 6382745 = 4787059) B4787059
theorem B1770671 : Blo 1770086 1770671 := bstep (se 1 (by rfl) ⟨1328003, by rfl⟩ : syracuseStep 1770671 = 2656007) B2656007
theorem B2655431 : Blo 1770086 2655431 := bstep (se 1 (by rfl) ⟨1991573, by rfl⟩ : syracuseStep 2655431 = 3983147) B3983147
theorem B1770695 : Blo 1770086 1770695 := bstep (se 1 (by rfl) ⟨1328021, by rfl⟩ : syracuseStep 1770695 = 2656043) B2656043
theorem B10085579 : Blo 1770086 10085579 := bstep (se 1 (by rfl) ⟨7564184, by rfl⟩ : syracuseStep 10085579 = 15128369) B15128369
theorem B1770715 : Blo 1770086 1770715 := bstep (se 1 (by rfl) ⟨1328036, by rfl⟩ : syracuseStep 1770715 = 2656073) B2656073
theorem B1770791 : Blo 1770086 1770791 := bstep (se 1 (by rfl) ⟨1328093, by rfl⟩ : syracuseStep 1770791 = 2656187) B2656187
theorem B1770831 : Blo 1770086 1770831 := bstep (se 1 (by rfl) ⟨1328123, by rfl⟩ : syracuseStep 1770831 = 2656247) B2656247
theorem B22685021 : Blo 1770086 22685021 := bstep (se 3 (by rfl) ⟨4253441, by rfl⟩ : syracuseStep 22685021 = 8506883) B8506883
theorem B1770847 : Blo 1770086 1770847 := bstep (se 1 (by rfl) ⟨1328135, by rfl⟩ : syracuseStep 1770847 = 2656271) B2656271
theorem B3982697 : Blo 1770086 3982697 := bstep (se 2 (by rfl) ⟨1493511, by rfl⟩ : syracuseStep 3982697 = 2987023) B2987023
theorem B2655593 : Blo 1770086 2655593 := bstep (se 2 (by rfl) ⟨995847, by rfl⟩ : syracuseStep 2655593 = 1991695) B1991695
theorem B1770875 : Blo 1770086 1770875 := bstep (se 1 (by rfl) ⟨1328156, by rfl⟩ : syracuseStep 1770875 = 2656313) B2656313
theorem B17016227 : Blo 1770086 17016227 := bstep (se 1 (by rfl) ⟨12762170, by rfl⟩ : syracuseStep 17016227 = 25524341) B25524341
theorem B1770927 : Blo 1770086 1770927 := bstep (se 1 (by rfl) ⟨1328195, by rfl⟩ : syracuseStep 1770927 = 2656391) B2656391
theorem B2655671 : Blo 1770086 2655671 := bstep (se 1 (by rfl) ⟨1991753, by rfl⟩ : syracuseStep 2655671 = 3983507) B3983507
theorem B1770951 : Blo 1770086 1770951 := bstep (se 1 (by rfl) ⟨1328213, by rfl⟩ : syracuseStep 1770951 = 2656427) B2656427
theorem B2655707 : Blo 1770086 2655707 := bstep (se 1 (by rfl) ⟨1991780, by rfl⟩ : syracuseStep 2655707 = 3983561) B3983561
theorem B1770971 : Blo 1770086 1770971 := bstep (se 1 (by rfl) ⟨1328228, by rfl⟩ : syracuseStep 1770971 = 2656457) B2656457
theorem B1771047 : Blo 1770086 1771047 := bstep (se 1 (by rfl) ⟨1328285, by rfl⟩ : syracuseStep 1771047 = 2656571) B2656571
theorem B24569387 : Blo 1770086 24569387 := bstep (se 1 (by rfl) ⟨18427040, by rfl⟩ : syracuseStep 24569387 = 36854081) B36854081
theorem B1992271 : Blo 1770086 1992271 := bstep (se 1 (by rfl) ⟨1494203, by rfl⟩ : syracuseStep 1992271 = 2988407) B2988407
theorem B1771087 : Blo 1770086 1771087 := bstep (se 1 (by rfl) ⟨1328315, by rfl⟩ : syracuseStep 1771087 = 2656631) B2656631
theorem B1771103 : Blo 1770086 1771103 := bstep (se 1 (by rfl) ⟨1328327, by rfl⟩ : syracuseStep 1771103 = 2656655) B2656655
theorem B1771131 : Blo 1770086 1771131 := bstep (se 1 (by rfl) ⟨1328348, by rfl⟩ : syracuseStep 1771131 = 2656697) B2656697
theorem B10765963 : Blo 1770086 10765963 := bstep (se 1 (by rfl) ⟨8074472, by rfl⟩ : syracuseStep 10765963 = 16148945) B16148945
theorem B38291089 : Blo 1770086 38291089 := bstep (se 2 (by rfl) ⟨14359158, by rfl⟩ : syracuseStep 38291089 = 28718317) B28718317
theorem B1771183 : Blo 1770086 1771183 := bstep (se 1 (by rfl) ⟨1328387, by rfl⟩ : syracuseStep 1771183 = 2656775) B2656775
theorem B8963783 : Blo 1770086 8963783 := bstep (se 1 (by rfl) ⟨6722837, by rfl⟩ : syracuseStep 8963783 = 13445675) B13445675
theorem B1771207 : Blo 1770086 1771207 := bstep (se 1 (by rfl) ⟨1328405, by rfl⟩ : syracuseStep 1771207 = 2656811) B2656811
theorem B1771227 : Blo 1770086 1771227 := bstep (se 1 (by rfl) ⟨1328420, by rfl⟩ : syracuseStep 1771227 = 2656841) B2656841
theorem B1771303 : Blo 1770086 1771303 := bstep (se 1 (by rfl) ⟨1328477, by rfl⟩ : syracuseStep 1771303 = 2656955) B2656955
theorem B86157107 : Blo 1770086 86157107 := bstep (se 1 (by rfl) ⟨64617830, by rfl⟩ : syracuseStep 86157107 = 129235661) B129235661
theorem B1771343 : Blo 1770086 1771343 := bstep (se 1 (by rfl) ⟨1328507, by rfl⟩ : syracuseStep 1771343 = 2657015) B2657015
theorem B1771359 : Blo 1770086 1771359 := bstep (se 1 (by rfl) ⟨1328519, by rfl⟩ : syracuseStep 1771359 = 2657039) B2657039
theorem B1771387 : Blo 1770086 1771387 := bstep (se 1 (by rfl) ⟨1328540, by rfl⟩ : syracuseStep 1771387 = 2657081) B2657081
theorem B8513399 : Blo 1770086 8513399 := bstep (se 1 (by rfl) ⟨6385049, by rfl⟩ : syracuseStep 8513399 = 12770099) B12770099
theorem B2656175 : Blo 1770086 2656175 := bstep (se 1 (by rfl) ⟨1992131, by rfl⟩ : syracuseStep 2656175 = 3984263) B3984263
theorem B1771439 : Blo 1770086 1771439 := bstep (se 1 (by rfl) ⟨1328579, by rfl⟩ : syracuseStep 1771439 = 2657159) B2657159
theorem B5113775 : Blo 1770086 5113775 := bstep (se 1 (by rfl) ⟨3835331, by rfl⟩ : syracuseStep 5113775 = 7670663) B7670663
theorem B6727607 : Blo 1770086 6727607 := bstep (se 1 (by rfl) ⟨5045705, by rfl⟩ : syracuseStep 6727607 = 10091411) B10091411
theorem B3983291 : Blo 1770086 3983291 := bstep (se 1 (by rfl) ⟨2987468, by rfl⟩ : syracuseStep 3983291 = 5974937) B5974937
theorem B28714945 : Blo 1770086 28714945 := bstep (se 2 (by rfl) ⟨10768104, by rfl⟩ : syracuseStep 28714945 = 21536209) B21536209
theorem B1771463 : Blo 1770086 1771463 := bstep (se 1 (by rfl) ⟨1328597, by rfl⟩ : syracuseStep 1771463 = 2657195) B2657195
theorem B1992667 : Blo 1770086 1992667 := bstep (se 1 (by rfl) ⟨1494500, by rfl⟩ : syracuseStep 1992667 = 2989001) B2989001
theorem B1771483 : Blo 1770086 1771483 := bstep (se 1 (by rfl) ⟨1328612, by rfl⟩ : syracuseStep 1771483 = 2657225) B2657225
theorem B45402119 : Blo 1770086 45402119 := bstep (se 1 (by rfl) ⟨34051589, by rfl⟩ : syracuseStep 45402119 = 68103179) B68103179
theorem B2656265 : Blo 1770086 2656265 := bstep (se 2 (by rfl) ⟨996099, by rfl⟩ : syracuseStep 2656265 = 1992199) B1992199
theorem B2656295 : Blo 1770086 2656295 := bstep (se 1 (by rfl) ⟨1992221, by rfl⟩ : syracuseStep 2656295 = 3984443) B3984443
theorem B1771559 : Blo 1770086 1771559 := bstep (se 1 (by rfl) ⟨1328669, by rfl⟩ : syracuseStep 1771559 = 2657339) B2657339
theorem B5974073 : Blo 1770086 5974073 := bstep (se 2 (by rfl) ⟨2240277, by rfl⟩ : syracuseStep 5974073 = 4480555) B4480555
theorem B6055993 : Blo 1770086 6055993 := bstep (se 2 (by rfl) ⟨2270997, by rfl⟩ : syracuseStep 6055993 = 4541995) B4541995
theorem B3983417 : Blo 1770086 3983417 := bstep (se 2 (by rfl) ⟨1493781, by rfl⟩ : syracuseStep 3983417 = 2987563) B2987563
theorem B1771599 : Blo 1770086 1771599 := bstep (se 1 (by rfl) ⟨1328699, by rfl⟩ : syracuseStep 1771599 = 2657399) B2657399
theorem B1771615 : Blo 1770086 1771615 := bstep (se 1 (by rfl) ⟨1328711, by rfl⟩ : syracuseStep 1771615 = 2657423) B2657423
theorem B3360865 : Blo 1770086 3360865 := bstep (se 2 (by rfl) ⟨1260324, by rfl⟩ : syracuseStep 3360865 = 2520649) B2520649
theorem B2656379 : Blo 1770086 2656379 := bstep (se 1 (by rfl) ⟨1992284, by rfl⟩ : syracuseStep 2656379 = 3984569) B3984569
theorem B1771643 : Blo 1770086 1771643 := bstep (se 1 (by rfl) ⟨1328732, by rfl⟩ : syracuseStep 1771643 = 2657465) B2657465
theorem B1771695 : Blo 1770086 1771695 := bstep (se 1 (by rfl) ⟨1328771, by rfl⟩ : syracuseStep 1771695 = 2657543) B2657543
theorem B1771719 : Blo 1770086 1771719 := bstep (se 1 (by rfl) ⟨1328789, by rfl⟩ : syracuseStep 1771719 = 2657579) B2657579
theorem B1771739 : Blo 1770086 1771739 := bstep (se 1 (by rfl) ⟨1328804, by rfl⟩ : syracuseStep 1771739 = 2657609) B2657609
theorem B2656505 : Blo 1770086 2656505 := bstep (se 2 (by rfl) ⟨996189, by rfl⟩ : syracuseStep 2656505 = 1992379) B1992379
theorem B8186123 : Blo 1770086 8186123 := bstep (se 1 (by rfl) ⟨6139592, by rfl⟩ : syracuseStep 8186123 = 12279185) B12279185
theorem B1771815 : Blo 1770086 1771815 := bstep (se 1 (by rfl) ⟨1328861, by rfl⟩ : syracuseStep 1771815 = 2657723) B2657723
theorem B11348275 : Blo 1770086 11348275 := bstep (se 1 (by rfl) ⟨8511206, by rfl⟩ : syracuseStep 11348275 = 17022413) B17022413
theorem B1771855 : Blo 1770086 1771855 := bstep (se 1 (by rfl) ⟨1328891, by rfl⟩ : syracuseStep 1771855 = 2657783) B2657783
theorem B32303447 : Blo 1770086 32303447 := bstep (se 1 (by rfl) ⟨24227585, by rfl⟩ : syracuseStep 32303447 = 48455171) B48455171
theorem B2656607 : Blo 1770086 2656607 := bstep (se 1 (by rfl) ⟨1992455, by rfl⟩ : syracuseStep 2656607 = 3984911) B3984911
theorem B1771871 : Blo 1770086 1771871 := bstep (se 1 (by rfl) ⟨1328903, by rfl⟩ : syracuseStep 1771871 = 2657807) B2657807
theorem B2656619 : Blo 1770086 2656619 := bstep (se 1 (by rfl) ⟨1992464, by rfl⟩ : syracuseStep 2656619 = 3984929) B3984929
theorem B1771899 : Blo 1770086 1771899 := bstep (se 1 (by rfl) ⟨1328924, by rfl⟩ : syracuseStep 1771899 = 2657849) B2657849
theorem B5974397 : Blo 1770086 5974397 := bstep (se 3 (by rfl) ⟨1120199, by rfl⟩ : syracuseStep 5974397 = 2240399) B2240399
theorem B3983759 : Blo 1770086 3983759 := bstep (se 1 (by rfl) ⟨2987819, by rfl⟩ : syracuseStep 3983759 = 5975639) B5975639
theorem B4483471 : Blo 1770086 4483471 := bstep (se 1 (by rfl) ⟨3362603, by rfl⟩ : syracuseStep 4483471 = 6725207) B6725207
theorem B30263705 : Blo 1770086 30263705 := bstep (se 2 (by rfl) ⟨11348889, by rfl⟩ : syracuseStep 30263705 = 22697779) B22697779
theorem B1993135 : Blo 1770086 1993135 := bstep (se 1 (by rfl) ⟨1494851, by rfl⟩ : syracuseStep 1993135 = 2989703) B2989703
theorem B1771951 : Blo 1770086 1771951 := bstep (se 1 (by rfl) ⟨1328963, by rfl⟩ : syracuseStep 1771951 = 2657927) B2657927
theorem B1771975 : Blo 1770086 1771975 := bstep (se 1 (by rfl) ⟨1328981, by rfl⟩ : syracuseStep 1771975 = 2657963) B2657963
theorem B1771995 : Blo 1770086 1771995 := bstep (se 1 (by rfl) ⟨1328996, by rfl⟩ : syracuseStep 1771995 = 2657993) B2657993
theorem B19139105 : Blo 1770086 19139105 := bstep (se 2 (by rfl) ⟨7177164, by rfl⟩ : syracuseStep 19139105 = 14354329) B14354329
theorem B1772071 : Blo 1770086 1772071 := bstep (se 1 (by rfl) ⟨1329053, by rfl⟩ : syracuseStep 1772071 = 2658107) B2658107
theorem B2656847 : Blo 1770086 2656847 := bstep (se 1 (by rfl) ⟨1992635, by rfl⟩ : syracuseStep 2656847 = 3985271) B3985271
theorem B5974667 : Blo 1770086 5974667 := bstep (se 1 (by rfl) ⟨4481000, by rfl⟩ : syracuseStep 5974667 = 8962001) B8962001
theorem B2656967 : Blo 1770086 2656967 := bstep (se 1 (by rfl) ⟨1992725, by rfl⟩ : syracuseStep 2656967 = 3985451) B3985451
theorem B3984083 : Blo 1770086 3984083 := bstep (se 1 (by rfl) ⟨2988062, by rfl⟩ : syracuseStep 3984083 = 5976125) B5976125
theorem B11504339 : Blo 1770086 11504339 := bstep (se 1 (by rfl) ⟨8628254, by rfl⟩ : syracuseStep 11504339 = 17256509) B17256509
theorem B4483795 : Blo 1770086 4483795 := bstep (se 1 (by rfl) ⟨3362846, by rfl⟩ : syracuseStep 4483795 = 6725693) B6725693
theorem B1993567 : Blo 1770086 1993567 := bstep (se 1 (by rfl) ⟨1495175, by rfl⟩ : syracuseStep 1993567 = 2990351) B2990351
theorem B2657129 : Blo 1770086 2657129 := bstep (se 2 (by rfl) ⟨996423, by rfl⟩ : syracuseStep 2657129 = 1992847) B1992847
theorem B25545617 : Blo 1770086 25545617 := bstep (se 2 (by rfl) ⟨9579606, by rfl⟩ : syracuseStep 25545617 = 19159213) B19159213
theorem B2657207 : Blo 1770086 2657207 := bstep (se 1 (by rfl) ⟨1992905, by rfl⟩ : syracuseStep 2657207 = 3985811) B3985811
theorem B2657243 : Blo 1770086 2657243 := bstep (se 1 (by rfl) ⟨1992932, by rfl⟩ : syracuseStep 2657243 = 3985865) B3985865
theorem B3361799 : Blo 1770086 3361799 := bstep (se 1 (by rfl) ⟨2521349, by rfl⟩ : syracuseStep 3361799 = 5042699) B5042699
theorem B4255105 : Blo 1770086 4255105 := bstep (se 2 (by rfl) ⟨1595664, by rfl⟩ : syracuseStep 4255105 = 3191329) B3191329
theorem B36359597 : Blo 1770086 36359597 := bstep (se 3 (by rfl) ⟨6817424, by rfl⟩ : syracuseStep 36359597 = 13634849) B13634849
theorem B2657711 : Blo 1770086 2657711 := bstep (se 1 (by rfl) ⟨1993283, by rfl⟩ : syracuseStep 2657711 = 3986567) B3986567
theorem B3591607 : Blo 1770086 3591607 := bstep (se 1 (by rfl) ⟨2693705, by rfl⟩ : syracuseStep 3591607 = 5387411) B5387411
theorem B5041673 : Blo 1770086 5041673 := bstep (se 2 (by rfl) ⟨1890627, by rfl⟩ : syracuseStep 5041673 = 3781255) B3781255
theorem B2657801 : Blo 1770086 2657801 := bstep (se 2 (by rfl) ⟨996675, by rfl⟩ : syracuseStep 2657801 = 1993351) B1993351
theorem B3362323 : Blo 1770086 3362323 := bstep (se 1 (by rfl) ⟨2521742, by rfl⟩ : syracuseStep 3362323 = 5043485) B5043485
theorem B5975585 : Blo 1770086 5975585 := bstep (se 2 (by rfl) ⟨2240844, by rfl⟩ : syracuseStep 5975585 = 4481689) B4481689
theorem B2657831 : Blo 1770086 2657831 := bstep (se 1 (by rfl) ⟨1993373, by rfl⟩ : syracuseStep 2657831 = 3986747) B3986747
theorem B13454909 : Blo 1770086 13454909 := bstep (se 3 (by rfl) ⟨2522795, by rfl⟩ : syracuseStep 13454909 = 5045591) B5045591
theorem B13626967 : Blo 1770086 13626967 := bstep (se 1 (by rfl) ⟨10220225, by rfl⟩ : syracuseStep 13626967 = 20440451) B20440451
theorem B3985019 : Blo 1770086 3985019 := bstep (se 1 (by rfl) ⟨2988764, by rfl⟩ : syracuseStep 3985019 = 5977529) B5977529
theorem B3591803 : Blo 1770086 3591803 := bstep (se 1 (by rfl) ⟨2693852, by rfl⟩ : syracuseStep 3591803 = 5387705) B5387705
theorem B2657915 : Blo 1770086 2657915 := bstep (se 1 (by rfl) ⟨1993436, by rfl⟩ : syracuseStep 2657915 = 3986873) B3986873
theorem B4484747 : Blo 1770086 4484747 := bstep (se 1 (by rfl) ⟨3363560, by rfl⟩ : syracuseStep 4484747 = 6727121) B6727121
theorem B9572039 : Blo 1770086 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B5975801 : Blo 1770086 5975801 := bstep (se 2 (by rfl) ⟨2240925, by rfl⟩ : syracuseStep 5975801 = 4481851) B4481851
theorem B3985145 : Blo 1770086 3985145 := bstep (se 2 (by rfl) ⟨1494429, by rfl⟩ : syracuseStep 3985145 = 2988859) B2988859
theorem B2658041 : Blo 1770086 2658041 := bstep (se 2 (by rfl) ⟨996765, by rfl⟩ : syracuseStep 2658041 = 1993531) B1993531
theorem B2838377 : Blo 1770086 2838377 := bstep (se 2 (by rfl) ⟨1064391, by rfl⟩ : syracuseStep 2838377 = 2128783) B2128783
theorem B5042027 : Blo 1770086 5042027 := bstep (se 1 (by rfl) ⟨3781520, by rfl⟩ : syracuseStep 5042027 = 7563041) B7563041
theorem B4255595 : Blo 1770086 4255595 := bstep (se 1 (by rfl) ⟨3191696, by rfl⟩ : syracuseStep 4255595 = 6383393) B6383393
theorem B21843847 : Blo 1770086 21843847 := bstep (se 1 (by rfl) ⟨16382885, by rfl⟩ : syracuseStep 21843847 = 32765771) B32765771
theorem B2838415 : Blo 1770086 2838415 := bstep (se 1 (by rfl) ⟨2128811, by rfl⟩ : syracuseStep 2838415 = 4257623) B4257623
theorem B5976071 : Blo 1770086 5976071 := bstep (se 1 (by rfl) ⟨4482053, by rfl⟩ : syracuseStep 5976071 = 8964107) B8964107
theorem B3985415 : Blo 1770086 3985415 := bstep (se 1 (by rfl) ⟨2989061, by rfl⟩ : syracuseStep 3985415 = 5978123) B5978123
theorem B2240551 : Blo 1770086 2240551 := bstep (se 1 (by rfl) ⟨1680413, by rfl⟩ : syracuseStep 2240551 = 3360827) B3360827
theorem B3985487 : Blo 1770086 3985487 := bstep (se 1 (by rfl) ⟨2989115, by rfl⟩ : syracuseStep 3985487 = 5978231) B5978231
theorem B5976179 : Blo 1770086 5976179 := bstep (se 1 (by rfl) ⟨4482134, by rfl⟩ : syracuseStep 5976179 = 8964269) B8964269
theorem B2240875 : Blo 1770086 2240875 := bstep (se 1 (by rfl) ⟨1680656, by rfl⟩ : syracuseStep 2240875 = 3361313) B3361313
theorem B5976449 : Blo 1770086 5976449 := bstep (se 2 (by rfl) ⟨2241168, by rfl⟩ : syracuseStep 5976449 = 4482337) B4482337
theorem B4256219 : Blo 1770086 4256219 := bstep (se 1 (by rfl) ⟨3192164, by rfl⟩ : syracuseStep 4256219 = 6384329) B6384329
theorem B3985883 : Blo 1770086 3985883 := bstep (se 1 (by rfl) ⟨2989412, by rfl⟩ : syracuseStep 3985883 = 5978825) B5978825
theorem B5042675 : Blo 1770086 5042675 := bstep (se 1 (by rfl) ⟨3782006, by rfl⟩ : syracuseStep 5042675 = 7564013) B7564013
theorem B13455881 : Blo 1770086 13455881 := bstep (se 2 (by rfl) ⟨5045955, by rfl⟩ : syracuseStep 13455881 = 10091911) B10091911
theorem B2241103 : Blo 1770086 2241103 := bstep (se 1 (by rfl) ⟨1680827, by rfl⟩ : syracuseStep 2241103 = 3361655) B3361655
theorem B51082001 : Blo 1770086 51082001 := bstep (se 2 (by rfl) ⟨19155750, by rfl⟩ : syracuseStep 51082001 = 38311501) B38311501
theorem B3986351 : Blo 1770086 3986351 := bstep (se 1 (by rfl) ⟨2989763, by rfl⟩ : syracuseStep 3986351 = 5979527) B5979527
theorem B5043131 : Blo 1770086 5043131 := bstep (se 1 (by rfl) ⟨3782348, by rfl⟩ : syracuseStep 5043131 = 7564697) B7564697
theorem B20165597 : Blo 1770086 20165597 := bstep (se 3 (by rfl) ⟨3781049, by rfl⟩ : syracuseStep 20165597 = 7562099) B7562099
theorem B17019953 : Blo 1770086 17019953 := bstep (se 2 (by rfl) ⟨6382482, by rfl⟩ : syracuseStep 17019953 = 12764965) B12764965
theorem B2987131 : Blo 1770086 2987131 := bstep (se 1 (by rfl) ⟨2240348, by rfl⟩ : syracuseStep 2987131 = 4480697) B4480697
theorem B5977259 : Blo 1770086 5977259 := bstep (se 1 (by rfl) ⟨4482944, by rfl⟩ : syracuseStep 5977259 = 8965889) B8965889
theorem B36353195 : Blo 1770086 36353195 := bstep (se 1 (by rfl) ⟨27264896, by rfl⟩ : syracuseStep 36353195 = 54529793) B54529793
theorem B3986603 : Blo 1770086 3986603 := bstep (se 1 (by rfl) ⟨2989952, by rfl⟩ : syracuseStep 3986603 = 5979905) B5979905
theorem B3192007 : Blo 1770086 3192007 := bstep (se 1 (by rfl) ⟨2394005, by rfl⟩ : syracuseStep 3192007 = 4788011) B4788011
theorem B6722945 : Blo 1770086 6722945 := bstep (se 2 (by rfl) ⟨2521104, by rfl⟩ : syracuseStep 6722945 = 5042209) B5042209
theorem B5674369 : Blo 1770086 5674369 := bstep (se 2 (by rfl) ⟨2127888, by rfl⟩ : syracuseStep 5674369 = 4255777) B4255777
theorem B6722959 : Blo 1770086 6722959 := bstep (se 1 (by rfl) ⟨5042219, by rfl⟩ : syracuseStep 6722959 = 10084439) B10084439
theorem B13448591 : Blo 1770086 13448591 := bstep (se 1 (by rfl) ⟨10086443, by rfl⟩ : syracuseStep 13448591 = 20172887) B20172887
theorem B2242171 : Blo 1770086 2242171 := bstep (se 1 (by rfl) ⟨1681628, by rfl⟩ : syracuseStep 2242171 = 3363257) B3363257
theorem B11343559 : Blo 1770086 11343559 := bstep (se 1 (by rfl) ⟨8507669, by rfl⟩ : syracuseStep 11343559 = 17015339) B17015339
theorem B5977799 : Blo 1770086 5977799 := bstep (se 1 (by rfl) ⟨4483349, by rfl⟩ : syracuseStep 5977799 = 8966699) B8966699
theorem B3987143 : Blo 1770086 3987143 := bstep (se 1 (by rfl) ⟨2990357, by rfl⟩ : syracuseStep 3987143 = 5980715) B5980715
theorem B2242399 : Blo 1770086 2242399 := bstep (se 1 (by rfl) ⟨1681799, by rfl⟩ : syracuseStep 2242399 = 3363599) B3363599
theorem B2987995 : Blo 1770086 2987995 := bstep (se 1 (by rfl) ⟨2240996, by rfl⟩ : syracuseStep 2987995 = 4481993) B4481993
theorem B6379715 : Blo 1770086 6379715 := bstep (se 1 (by rfl) ⟨4784786, by rfl⟩ : syracuseStep 6379715 = 9569573) B9569573
theorem B5675255 : Blo 1770086 5675255 := bstep (se 1 (by rfl) ⟨4256441, by rfl⟩ : syracuseStep 5675255 = 8512883) B8512883
theorem B11508097 : Blo 1770086 11508097 := bstep (se 2 (by rfl) ⟨4315536, by rfl⟩ : syracuseStep 11508097 = 8631073) B8631073
theorem B3193231 : Blo 1770086 3193231 := bstep (se 1 (by rfl) ⟨2394923, by rfl⟩ : syracuseStep 3193231 = 4789847) B4789847
theorem B5978663 : Blo 1770086 5978663 := bstep (se 1 (by rfl) ⟨4483997, by rfl⟩ : syracuseStep 5978663 = 8967995) B8967995
theorem B11352635 : Blo 1770086 11352635 := bstep (se 1 (by rfl) ⟨8514476, by rfl⟩ : syracuseStep 11352635 = 17028953) B17028953
theorem B2988623 : Blo 1770086 2988623 := bstep (se 1 (by rfl) ⟨2241467, by rfl⟩ : syracuseStep 2988623 = 4482935) B4482935
theorem B6724235 : Blo 1770086 6724235 := bstep (se 1 (by rfl) ⟨5043176, by rfl⟩ : syracuseStep 6724235 = 10086353) B10086353
theorem B5978771 : Blo 1770086 5978771 := bstep (se 1 (by rfl) ⟨4484078, by rfl⟩ : syracuseStep 5978771 = 8968157) B8968157
theorem B51092147 : Blo 1770086 51092147 := bstep (se 1 (by rfl) ⟨38319110, by rfl⟩ : syracuseStep 51092147 = 76638221) B76638221
theorem B25533157 : Blo 1770086 25533157 := bstep (se 4 (by rfl) ⟨2393733, by rfl⟩ : syracuseStep 25533157 = 4787467) B4787467
theorem B5978987 : Blo 1770086 5978987 := bstep (se 1 (by rfl) ⟨4484240, by rfl⟩ : syracuseStep 5978987 = 8968481) B8968481
theorem B5979041 : Blo 1770086 5979041 := bstep (se 2 (by rfl) ⟨2242140, by rfl⟩ : syracuseStep 5979041 = 4484281) B4484281
theorem B7183441 : Blo 1770086 7183441 := bstep (se 2 (by rfl) ⟨2693790, by rfl⟩ : syracuseStep 7183441 = 5387581) B5387581
theorem B38313233 : Blo 1770086 38313233 := bstep (se 2 (by rfl) ⟨14367462, by rfl⟩ : syracuseStep 38313233 = 28734925) B28734925
theorem B43080983 : Blo 1770086 43080983 := bstep (se 1 (by rfl) ⟨32310737, by rfl⟩ : syracuseStep 43080983 = 64621475) B64621475
theorem B8969615 : Blo 1770086 8969615 := bstep (se 1 (by rfl) ⟨6727211, by rfl⟩ : syracuseStep 8969615 = 13454423) B13454423
theorem B2989487 : Blo 1770086 2989487 := bstep (se 1 (by rfl) ⟨2242115, by rfl⟩ : syracuseStep 2989487 = 4484231) B4484231
theorem B8510939 : Blo 1770086 8510939 := bstep (se 1 (by rfl) ⟨6383204, by rfl⟩ : syracuseStep 8510939 = 12766409) B12766409
theorem B5979635 : Blo 1770086 5979635 := bstep (se 1 (by rfl) ⟨4484726, by rfl⟩ : syracuseStep 5979635 = 8969453) B8969453
theorem B27270695 : Blo 1770086 27270695 := bstep (se 1 (by rfl) ⟨20453021, by rfl⟩ : syracuseStep 27270695 = 40906043) B40906043
theorem B3407483 : Blo 1770086 3407483 := bstep (se 1 (by rfl) ⟨2555612, by rfl⟩ : syracuseStep 3407483 = 5111225) B5111225
theorem B13442759 : Blo 1770086 13442759 := bstep (se 1 (by rfl) ⟨10082069, by rfl⟩ : syracuseStep 13442759 = 20164139) B20164139
theorem B3784391 : Blo 1770086 3784391 := bstep (se 1 (by rfl) ⟨2838293, by rfl⟩ : syracuseStep 3784391 = 5676587) B5676587
theorem B10772291 : Blo 1770086 10772291 := bstep (se 1 (by rfl) ⟨8079218, by rfl⟩ : syracuseStep 10772291 = 16158437) B16158437
theorem B2989919 : Blo 1770086 2989919 := bstep (se 1 (by rfl) ⟨2242439, by rfl⟩ : syracuseStep 2989919 = 4484879) B4484879
theorem B48480119 : Blo 1770086 48480119 := bstep (se 1 (by rfl) ⟨36360089, by rfl⟩ : syracuseStep 48480119 = 72720179) B72720179
theorem B4481153 : Blo 1770086 4481153 := bstep (se 2 (by rfl) ⟨1680432, by rfl⟩ : syracuseStep 4481153 = 3360865) B3360865
theorem B8970587 : Blo 1770086 8970587 := bstep (se 1 (by rfl) ⟨6727940, by rfl⟩ : syracuseStep 8970587 = 13455881) B13455881
theorem B15131033 : Blo 1770086 15131033 := bstep (se 2 (by rfl) ⟨5674137, by rfl⟩ : syracuseStep 15131033 = 11348275) B11348275
theorem B2392519 : Blo 1770086 2392519 := bstep (se 1 (by rfl) ⟨1794389, by rfl⟩ : syracuseStep 2392519 = 3588779) B3588779
theorem B15344129 : Blo 1770086 15344129 := bstep (se 2 (by rfl) ⟨5754048, by rfl⟩ : syracuseStep 15344129 = 11508097) B11508097
theorem B34054667 : Blo 1770086 34054667 := bstep (se 1 (by rfl) ⟨25541000, by rfl⟩ : syracuseStep 34054667 = 51082001) B51082001
theorem B13443731 : Blo 1770086 13443731 := bstep (se 1 (by rfl) ⟨10082798, by rfl⟩ : syracuseStep 13443731 = 20165597) B20165597
theorem B11346635 : Blo 1770086 11346635 := bstep (se 1 (by rfl) ⟨8509976, by rfl⟩ : syracuseStep 11346635 = 17019953) B17019953
theorem B1770207 : Blo 1770086 1770207 := bstep (se 1 (by rfl) ⟨1327655, by rfl⟩ : syracuseStep 1770207 = 2655311) B2655311
theorem B57418469 : Blo 1770086 57418469 := bstep (se 4 (by rfl) ⟨5382981, by rfl⟩ : syracuseStep 57418469 = 10765963) B10765963
theorem B1770287 : Blo 1770086 1770287 := bstep (se 1 (by rfl) ⟨1327715, by rfl⟩ : syracuseStep 1770287 = 2655431) B2655431
theorem B15123347 : Blo 1770086 15123347 := bstep (se 1 (by rfl) ⟨11342510, by rfl⟩ : syracuseStep 15123347 = 22685021) B22685021
theorem B2655131 : Blo 1770086 2655131 := bstep (se 1 (by rfl) ⟨1991348, by rfl⟩ : syracuseStep 2655131 = 3982697) B3982697
theorem B1770395 : Blo 1770086 1770395 := bstep (se 1 (by rfl) ⟨1327796, by rfl⟩ : syracuseStep 1770395 = 2655593) B2655593
theorem B4481963 : Blo 1770086 4481963 := bstep (se 1 (by rfl) ⟨3361472, by rfl⟩ : syracuseStep 4481963 = 6722945) B6722945
theorem B1770447 : Blo 1770086 1770447 := bstep (se 1 (by rfl) ⟨1327835, by rfl⟩ : syracuseStep 1770447 = 2655671) B2655671
theorem B1770471 : Blo 1770086 1770471 := bstep (se 1 (by rfl) ⟨1327853, by rfl⟩ : syracuseStep 1770471 = 2655707) B2655707
theorem B19145717 : Blo 1770086 19145717 := bstep (se 5 (by rfl) ⟨897455, by rfl⟩ : syracuseStep 19145717 = 1794911) B1794911
theorem B3409129 : Blo 1770086 3409129 := bstep (se 2 (by rfl) ⟨1278423, by rfl⟩ : syracuseStep 3409129 = 2556847) B2556847
theorem B1770783 : Blo 1770086 1770783 := bstep (se 1 (by rfl) ⟨1328087, by rfl⟩ : syracuseStep 1770783 = 2656175) B2656175
theorem B3409183 : Blo 1770086 3409183 := bstep (se 1 (by rfl) ⟨2556887, by rfl⟩ : syracuseStep 3409183 = 5113775) B5113775
theorem B2655527 : Blo 1770086 2655527 := bstep (se 1 (by rfl) ⟨1991645, by rfl⟩ : syracuseStep 2655527 = 3983291) B3983291
theorem B1770843 : Blo 1770086 1770843 := bstep (se 1 (by rfl) ⟨1328132, by rfl⟩ : syracuseStep 1770843 = 2656265) B2656265
theorem B1770863 : Blo 1770086 1770863 := bstep (se 1 (by rfl) ⟨1328147, by rfl⟩ : syracuseStep 1770863 = 2656295) B2656295
theorem B3982715 : Blo 1770086 3982715 := bstep (se 1 (by rfl) ⟨2987036, by rfl⟩ : syracuseStep 3982715 = 5974073) B5974073
theorem B2655611 : Blo 1770086 2655611 := bstep (se 1 (by rfl) ⟨1991708, by rfl⟩ : syracuseStep 2655611 = 3983417) B3983417
theorem B1770919 : Blo 1770086 1770919 := bstep (se 1 (by rfl) ⟨1328189, by rfl⟩ : syracuseStep 1770919 = 2656379) B2656379
theorem B9577921 : Blo 1770086 9577921 := bstep (se 2 (by rfl) ⟨3591720, by rfl⟩ : syracuseStep 9577921 = 7183441) B7183441
theorem B4253143 : Blo 1770086 4253143 := bstep (se 1 (by rfl) ⟨3189857, by rfl⟩ : syracuseStep 4253143 = 6379715) B6379715
theorem B3982841 : Blo 1770086 3982841 := bstep (se 2 (by rfl) ⟨1493565, by rfl⟩ : syracuseStep 3982841 = 2987131) B2987131
theorem B2655737 : Blo 1770086 2655737 := bstep (se 2 (by rfl) ⟨995901, by rfl⟩ : syracuseStep 2655737 = 1991803) B1991803
theorem B1771003 : Blo 1770086 1771003 := bstep (se 1 (by rfl) ⟨1328252, by rfl⟩ : syracuseStep 1771003 = 2656505) B2656505
theorem B5457415 : Blo 1770086 5457415 := bstep (se 1 (by rfl) ⟨4093061, by rfl⟩ : syracuseStep 5457415 = 8186123) B8186123
theorem B1771071 : Blo 1770086 1771071 := bstep (se 1 (by rfl) ⟨1328303, by rfl⟩ : syracuseStep 1771071 = 2656607) B2656607
theorem B1771079 : Blo 1770086 1771079 := bstep (se 1 (by rfl) ⟨1328309, by rfl⟩ : syracuseStep 1771079 = 2656619) B2656619
theorem B3982931 : Blo 1770086 3982931 := bstep (se 1 (by rfl) ⟨2987198, by rfl⟩ : syracuseStep 3982931 = 5974397) B5974397
theorem B2655839 : Blo 1770086 2655839 := bstep (se 1 (by rfl) ⟨1991879, by rfl⟩ : syracuseStep 2655839 = 3983759) B3983759
theorem B1992415 : Blo 1770086 1992415 := bstep (se 1 (by rfl) ⟨1494311, by rfl⟩ : syracuseStep 1992415 = 2988623) B2988623
theorem B1771231 : Blo 1770086 1771231 := bstep (se 1 (by rfl) ⟨1328423, by rfl⟩ : syracuseStep 1771231 = 2656847) B2656847
theorem B3983111 : Blo 1770086 3983111 := bstep (se 1 (by rfl) ⟨2987333, by rfl⟩ : syracuseStep 3983111 = 5974667) B5974667
theorem B4482823 : Blo 1770086 4482823 := bstep (se 1 (by rfl) ⟨3362117, by rfl⟩ : syracuseStep 4482823 = 6724235) B6724235
theorem B1771311 : Blo 1770086 1771311 := bstep (se 1 (by rfl) ⟨1328483, by rfl⟩ : syracuseStep 1771311 = 2656967) B2656967
theorem B2656055 : Blo 1770086 2656055 := bstep (se 1 (by rfl) ⟨1992041, by rfl⟩ : syracuseStep 2656055 = 3984083) B3984083
theorem B7669559 : Blo 1770086 7669559 := bstep (se 1 (by rfl) ⟨5752169, by rfl⟩ : syracuseStep 7669559 = 11504339) B11504339
theorem B8963945 : Blo 1770086 8963945 := bstep (se 2 (by rfl) ⟨3361479, by rfl⟩ : syracuseStep 8963945 = 6722959) B6722959
theorem B1771419 : Blo 1770086 1771419 := bstep (se 1 (by rfl) ⟨1328564, by rfl⟩ : syracuseStep 1771419 = 2657129) B2657129
theorem B1771471 : Blo 1770086 1771471 := bstep (se 1 (by rfl) ⟨1328603, by rfl⟩ : syracuseStep 1771471 = 2657207) B2657207
theorem B1771495 : Blo 1770086 1771495 := bstep (se 1 (by rfl) ⟨1328621, by rfl⟩ : syracuseStep 1771495 = 2657243) B2657243
theorem B4483097 : Blo 1770086 4483097 := bstep (se 2 (by rfl) ⟨1681161, by rfl⟩ : syracuseStep 4483097 = 3362323) B3362323
theorem B2656361 : Blo 1770086 2656361 := bstep (se 2 (by rfl) ⟨996135, by rfl⟩ : syracuseStep 2656361 = 1992271) B1992271
theorem B51054785 : Blo 1770086 51054785 := bstep (se 2 (by rfl) ⟨19145544, by rfl⟩ : syracuseStep 51054785 = 38291089) B38291089
theorem B15124745 : Blo 1770086 15124745 := bstep (se 2 (by rfl) ⟨5671779, by rfl⟩ : syracuseStep 15124745 = 11343559) B11343559
theorem B1992991 : Blo 1770086 1992991 := bstep (se 1 (by rfl) ⟨1494743, by rfl⟩ : syracuseStep 1992991 = 2989487) B2989487
theorem B1771807 : Blo 1770086 1771807 := bstep (se 1 (by rfl) ⟨1328855, by rfl⟩ : syracuseStep 1771807 = 2657711) B2657711
theorem B3361115 : Blo 1770086 3361115 := bstep (se 1 (by rfl) ⟨2520836, by rfl⟩ : syracuseStep 3361115 = 5041673) B5041673
theorem B1771867 : Blo 1770086 1771867 := bstep (se 1 (by rfl) ⟨1328900, by rfl⟩ : syracuseStep 1771867 = 2657801) B2657801
theorem B3983723 : Blo 1770086 3983723 := bstep (se 1 (by rfl) ⟨2987792, by rfl⟩ : syracuseStep 3983723 = 5975585) B5975585
theorem B18180463 : Blo 1770086 18180463 := bstep (se 1 (by rfl) ⟨13635347, by rfl⟩ : syracuseStep 18180463 = 27270695) B27270695
theorem B1771887 : Blo 1770086 1771887 := bstep (se 1 (by rfl) ⟨1328915, by rfl⟩ : syracuseStep 1771887 = 2657831) B2657831
theorem B2271655 : Blo 1770086 2271655 := bstep (se 1 (by rfl) ⟨1703741, by rfl⟩ : syracuseStep 2271655 = 3407483) B3407483
theorem B2656679 : Blo 1770086 2656679 := bstep (se 1 (by rfl) ⟨1992509, by rfl⟩ : syracuseStep 2656679 = 3985019) B3985019
theorem B2394535 : Blo 1770086 2394535 := bstep (se 1 (by rfl) ⟨1795901, by rfl⟩ : syracuseStep 2394535 = 3591803) B3591803
theorem B1771943 : Blo 1770086 1771943 := bstep (se 1 (by rfl) ⟨1328957, by rfl⟩ : syracuseStep 1771943 = 2657915) B2657915
theorem B3983867 : Blo 1770086 3983867 := bstep (se 1 (by rfl) ⟨2987900, by rfl⟩ : syracuseStep 3983867 = 5975801) B5975801
theorem B2656763 : Blo 1770086 2656763 := bstep (se 1 (by rfl) ⟨1992572, by rfl⟩ : syracuseStep 2656763 = 3985145) B3985145
theorem B1772027 : Blo 1770086 1772027 := bstep (se 1 (by rfl) ⟨1329020, by rfl⟩ : syracuseStep 1772027 = 2658041) B2658041
theorem B29125129 : Blo 1770086 29125129 := bstep (se 2 (by rfl) ⟨10921923, by rfl⟩ : syracuseStep 29125129 = 21843847) B21843847
theorem B1993279 : Blo 1770086 1993279 := bstep (se 1 (by rfl) ⟨1494959, by rfl⟩ : syracuseStep 1993279 = 2989919) B2989919
theorem B3361351 : Blo 1770086 3361351 := bstep (se 1 (by rfl) ⟨2521013, by rfl⟩ : syracuseStep 3361351 = 5042027) B5042027
theorem B2837063 : Blo 1770086 2837063 := bstep (se 1 (by rfl) ⟨2127797, by rfl⟩ : syracuseStep 2837063 = 4255595) B4255595
theorem B32320079 : Blo 1770086 32320079 := bstep (se 1 (by rfl) ⟨24240059, by rfl⟩ : syracuseStep 32320079 = 48480119) B48480119
theorem B3983993 : Blo 1770086 3983993 := bstep (se 2 (by rfl) ⟨1493997, by rfl⟩ : syracuseStep 3983993 = 2987995) B2987995
theorem B2656889 : Blo 1770086 2656889 := bstep (se 2 (by rfl) ⟨996333, by rfl⟩ : syracuseStep 2656889 = 1992667) B1992667
theorem B6056623 : Blo 1770086 6056623 := bstep (se 1 (by rfl) ⟨4542467, by rfl⟩ : syracuseStep 6056623 = 9084935) B9084935
theorem B3984047 : Blo 1770086 3984047 := bstep (se 1 (by rfl) ⟨2988035, by rfl⟩ : syracuseStep 3984047 = 5976071) B5976071
theorem B2656943 : Blo 1770086 2656943 := bstep (se 1 (by rfl) ⟨1992707, by rfl⟩ : syracuseStep 2656943 = 3985415) B3985415
theorem B2656991 : Blo 1770086 2656991 := bstep (se 1 (by rfl) ⟨1992743, by rfl⟩ : syracuseStep 2656991 = 3985487) B3985487
theorem B5974775 : Blo 1770086 5974775 := bstep (se 1 (by rfl) ⟨4481081, by rfl⟩ : syracuseStep 5974775 = 8962163) B8962163
theorem B3984119 : Blo 1770086 3984119 := bstep (se 1 (by rfl) ⟨2988089, by rfl⟩ : syracuseStep 3984119 = 5976179) B5976179
theorem B3984299 : Blo 1770086 3984299 := bstep (se 1 (by rfl) ⟨2988224, by rfl⟩ : syracuseStep 3984299 = 5976449) B5976449
theorem B2837479 : Blo 1770086 2837479 := bstep (se 1 (by rfl) ⟨2128109, by rfl⟩ : syracuseStep 2837479 = 4256219) B4256219
theorem B2657255 : Blo 1770086 2657255 := bstep (se 1 (by rfl) ⟨1992941, by rfl⟩ : syracuseStep 2657255 = 3985883) B3985883
theorem B2657513 : Blo 1770086 2657513 := bstep (se 2 (by rfl) ⟨996567, by rfl⟩ : syracuseStep 2657513 = 1993135) B1993135
theorem B2657567 : Blo 1770086 2657567 := bstep (se 1 (by rfl) ⟨1993175, by rfl⟩ : syracuseStep 2657567 = 3986351) B3986351
theorem B3362087 : Blo 1770086 3362087 := bstep (se 1 (by rfl) ⟨2521565, by rfl⟩ : syracuseStep 3362087 = 5043131) B5043131
theorem B4255163 : Blo 1770086 4255163 := bstep (se 1 (by rfl) ⟨3191372, by rfl⟩ : syracuseStep 4255163 = 6382745) B6382745
theorem B3984839 : Blo 1770086 3984839 := bstep (se 1 (by rfl) ⟨2988629, by rfl⟩ : syracuseStep 3984839 = 5977259) B5977259
theorem B24235463 : Blo 1770086 24235463 := bstep (se 1 (by rfl) ⟨18176597, by rfl⟩ : syracuseStep 24235463 = 36353195) B36353195
theorem B2657735 : Blo 1770086 2657735 := bstep (se 1 (by rfl) ⟨1993301, by rfl⟩ : syracuseStep 2657735 = 3986603) B3986603
theorem B8965727 : Blo 1770086 8965727 := bstep (se 1 (by rfl) ⟨6724295, by rfl⟩ : syracuseStep 8965727 = 13448591) B13448591
theorem B2658089 : Blo 1770086 2658089 := bstep (se 2 (by rfl) ⟨996783, by rfl⟩ : syracuseStep 2658089 = 1993567) B1993567
theorem B5975855 : Blo 1770086 5975855 := bstep (se 1 (by rfl) ⟨4481891, by rfl⟩ : syracuseStep 5975855 = 8963783) B8963783
theorem B3985199 : Blo 1770086 3985199 := bstep (se 1 (by rfl) ⟨2988899, by rfl⟩ : syracuseStep 3985199 = 5977799) B5977799
theorem B2658095 : Blo 1770086 2658095 := bstep (se 1 (by rfl) ⟨1993571, by rfl⟩ : syracuseStep 2658095 = 3987143) B3987143
theorem B57438071 : Blo 1770086 57438071 := bstep (se 1 (by rfl) ⟨43078553, by rfl⟩ : syracuseStep 57438071 = 86157107) B86157107
theorem B4485071 : Blo 1770086 4485071 := bstep (se 1 (by rfl) ⟨3363803, by rfl⟩ : syracuseStep 4485071 = 6727607) B6727607
theorem B13447133 : Blo 1770086 13447133 := bstep (se 3 (by rfl) ⟨2521337, by rfl⟩ : syracuseStep 13447133 = 5042675) B5042675
theorem B76591169 : Blo 1770086 76591169 := bstep (se 2 (by rfl) ⟨28721688, by rfl⟩ : syracuseStep 76591169 = 57443377) B57443377
theorem B4256009 : Blo 1770086 4256009 := bstep (se 2 (by rfl) ⟨1596003, by rfl⟩ : syracuseStep 4256009 = 3192007) B3192007
theorem B12759403 : Blo 1770086 12759403 := bstep (se 1 (by rfl) ⟨9569552, by rfl⟩ : syracuseStep 12759403 = 19139105) B19139105
theorem B3985775 : Blo 1770086 3985775 := bstep (se 1 (by rfl) ⟨2989331, by rfl⟩ : syracuseStep 3985775 = 5978663) B5978663
theorem B3985847 : Blo 1770086 3985847 := bstep (se 1 (by rfl) ⟨2989385, by rfl⟩ : syracuseStep 3985847 = 5978771) B5978771
theorem B1048293845 : Blo 1770086 1048293845 := bstep (se 7 (by rfl) ⟨12284693, by rfl⟩ : syracuseStep 1048293845 = 24569387) B24569387
theorem B5673473 : Blo 1770086 5673473 := bstep (se 2 (by rfl) ⟨2127552, by rfl⟩ : syracuseStep 5673473 = 4255105) B4255105
theorem B7565825 : Blo 1770086 7565825 := bstep (se 2 (by rfl) ⟨2837184, by rfl⟩ : syracuseStep 7565825 = 5674369) B5674369
theorem B3985991 : Blo 1770086 3985991 := bstep (se 1 (by rfl) ⟨2989493, by rfl⟩ : syracuseStep 3985991 = 5978987) B5978987
theorem B4788809 : Blo 1770086 4788809 := bstep (se 2 (by rfl) ⟨1795803, by rfl⟩ : syracuseStep 4788809 = 3591607) B3591607
theorem B3986027 : Blo 1770086 3986027 := bstep (se 1 (by rfl) ⟨2989520, by rfl⟩ : syracuseStep 3986027 = 5979041) B5979041
theorem B2241199 : Blo 1770086 2241199 := bstep (se 1 (by rfl) ⟨1680899, by rfl⟩ : syracuseStep 2241199 = 3361799) B3361799
theorem B28726109 : Blo 1770086 28726109 := bstep (se 3 (by rfl) ⟨5386145, by rfl⟩ : syracuseStep 28726109 = 10772291) B10772291
theorem B5673959 : Blo 1770086 5673959 := bstep (se 1 (by rfl) ⟨4255469, by rfl⟩ : syracuseStep 5673959 = 8510939) B8510939
theorem B3986423 : Blo 1770086 3986423 := bstep (se 1 (by rfl) ⟨2989817, by rfl⟩ : syracuseStep 3986423 = 5979635) B5979635
theorem B38286593 : Blo 1770086 38286593 := bstep (se 2 (by rfl) ⟨14357472, by rfl⟩ : syracuseStep 38286593 = 28714945) B28714945
theorem B3986783 : Blo 1770086 3986783 := bstep (se 1 (by rfl) ⟨2990087, by rfl⟩ : syracuseStep 3986783 = 5980175) B5980175
theorem B2987401 : Blo 1770086 2987401 := bstep (se 2 (by rfl) ⟨1120275, by rfl⟩ : syracuseStep 2987401 = 2240551) B2240551
theorem B8074657 : Blo 1770086 8074657 := bstep (se 2 (by rfl) ⟨3027996, by rfl⟩ : syracuseStep 8074657 = 6055993) B6055993
theorem B17012263 : Blo 1770086 17012263 := bstep (se 1 (by rfl) ⟨12759197, by rfl⟩ : syracuseStep 17012263 = 25518395) B25518395
theorem B10081979 : Blo 1770086 10081979 := bstep (se 1 (by rfl) ⟨7561484, by rfl⟩ : syracuseStep 10081979 = 15122969) B15122969
theorem B3987179 : Blo 1770086 3987179 := bstep (se 1 (by rfl) ⟨2990384, by rfl⟩ : syracuseStep 3987179 = 5980769) B5980769
theorem B2987833 : Blo 1770086 2987833 := bstep (se 2 (by rfl) ⟨1120437, by rfl⟩ : syracuseStep 2987833 = 2240875) B2240875
theorem B5977961 : Blo 1770086 5977961 := bstep (se 2 (by rfl) ⟨2241735, by rfl⟩ : syracuseStep 5977961 = 4483471) B4483471
theorem B4257641 : Blo 1770086 4257641 := bstep (se 2 (by rfl) ⟨1596615, by rfl⟩ : syracuseStep 4257641 = 3193231) B3193231
theorem B2988137 : Blo 1770086 2988137 := bstep (se 2 (by rfl) ⟨1120551, by rfl⟩ : syracuseStep 2988137 = 2241103) B2241103
theorem B6723719 : Blo 1770086 6723719 := bstep (se 1 (by rfl) ⟨5042789, by rfl⟩ : syracuseStep 6723719 = 10085579) B10085579
theorem B11344151 : Blo 1770086 11344151 := bstep (se 1 (by rfl) ⟨8508113, by rfl⟩ : syracuseStep 11344151 = 17016227) B17016227
theorem B5978393 : Blo 1770086 5978393 := bstep (se 2 (by rfl) ⟨2241897, by rfl⟩ : syracuseStep 5978393 = 4483795) B4483795
theorem B34044209 : Blo 1770086 34044209 := bstep (se 2 (by rfl) ⟨12766578, by rfl⟩ : syracuseStep 34044209 = 25533157) B25533157
theorem B5675599 : Blo 1770086 5675599 := bstep (se 1 (by rfl) ⟨4256699, by rfl⟩ : syracuseStep 5675599 = 8513399) B8513399
theorem B30268079 : Blo 1770086 30268079 := bstep (se 1 (by rfl) ⟨22701059, by rfl⟩ : syracuseStep 30268079 = 45402119) B45402119
theorem B3783503 : Blo 1770086 3783503 := bstep (se 1 (by rfl) ⟨2837627, by rfl⟩ : syracuseStep 3783503 = 5675255) B5675255
theorem B21535631 : Blo 1770086 21535631 := bstep (se 1 (by rfl) ⟨16151723, by rfl⟩ : syracuseStep 21535631 = 32303447) B32303447
theorem B20175803 : Blo 1770086 20175803 := bstep (se 1 (by rfl) ⟨15131852, by rfl⟩ : syracuseStep 20175803 = 30263705) B30263705
theorem B7568423 : Blo 1770086 7568423 := bstep (se 1 (by rfl) ⟨5676317, by rfl⟩ : syracuseStep 7568423 = 11352635) B11352635
theorem B34061431 : Blo 1770086 34061431 := bstep (se 1 (by rfl) ⟨25546073, by rfl⟩ : syracuseStep 34061431 = 51092147) B51092147
theorem B17030411 : Blo 1770086 17030411 := bstep (se 1 (by rfl) ⟨12772808, by rfl⟩ : syracuseStep 17030411 = 25545617) B25545617
theorem B18169289 : Blo 1770086 18169289 := bstep (se 2 (by rfl) ⟨6813483, by rfl⟩ : syracuseStep 18169289 = 13626967) B13626967
theorem B2989561 : Blo 1770086 2989561 := bstep (se 2 (by rfl) ⟨1121085, by rfl⟩ : syracuseStep 2989561 = 2242171) B2242171
theorem B25542155 : Blo 1770086 25542155 := bstep (se 1 (by rfl) ⟨19156616, by rfl⟩ : syracuseStep 25542155 = 38313233) B38313233
theorem B28720655 : Blo 1770086 28720655 := bstep (se 1 (by rfl) ⟨21540491, by rfl⟩ : syracuseStep 28720655 = 43080983) B43080983
theorem B5979743 : Blo 1770086 5979743 := bstep (se 1 (by rfl) ⟨4484807, by rfl⟩ : syracuseStep 5979743 = 8969615) B8969615
theorem B24239731 : Blo 1770086 24239731 := bstep (se 1 (by rfl) ⟨18179798, by rfl⟩ : syracuseStep 24239731 = 36359597) B36359597
theorem B8969939 : Blo 1770086 8969939 := bstep (se 1 (by rfl) ⟨6727454, by rfl⟩ : syracuseStep 8969939 = 13454909) B13454909
theorem B2989831 : Blo 1770086 2989831 := bstep (se 1 (by rfl) ⟨2242373, by rfl⟩ : syracuseStep 2989831 = 4484747) B4484747
theorem B2989865 : Blo 1770086 2989865 := bstep (se 2 (by rfl) ⟨1121199, by rfl⟩ : syracuseStep 2989865 = 2242399) B2242399
theorem B8961839 : Blo 1770086 8961839 := bstep (se 1 (by rfl) ⟨6721379, by rfl⟩ : syracuseStep 8961839 = 13442759) B13442759
theorem B6381359 : Blo 1770086 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B2522927 : Blo 1770086 2522927 := bstep (se 1 (by rfl) ⟨1892195, by rfl⟩ : syracuseStep 2522927 = 3784391) B3784391
theorem B3784553 : Blo 1770086 3784553 := bstep (se 2 (by rfl) ⟨1419207, by rfl⟩ : syracuseStep 3784553 = 2838415) B2838415
theorem B1892251 : Blo 1770086 1892251 := bstep (se 1 (by rfl) ⟨1419188, by rfl⟩ : syracuseStep 1892251 = 2838377) B2838377
theorem B51060779 : Blo 1770086 51060779 := bstep (se 1 (by rfl) ⟨38295584, by rfl⟩ : syracuseStep 51060779 = 76591169) B76591169
theorem B5980391 : Blo 1770086 5980391 := bstep (se 1 (by rfl) ⟨4485293, by rfl⟩ : syracuseStep 5980391 = 8970587) B8970587
theorem B8962487 : Blo 1770086 8962487 := bstep (se 1 (by rfl) ⟨6721865, by rfl⟩ : syracuseStep 8962487 = 13443731) B13443731
theorem B24240617 : Blo 1770086 24240617 := bstep (se 2 (by rfl) ⟨9090231, by rfl⟩ : syracuseStep 24240617 = 18180463) B18180463
theorem B1770087 : Blo 1770086 1770087 := bstep (se 1 (by rfl) ⟨1327565, by rfl⟩ : syracuseStep 1770087 = 2655131) B2655131
theorem B12763811 : Blo 1770086 12763811 := bstep (se 1 (by rfl) ⟨9572858, by rfl⟩ : syracuseStep 12763811 = 19145717) B19145717
theorem B4481801 : Blo 1770086 4481801 := bstep (se 2 (by rfl) ⟨1680675, by rfl⟩ : syracuseStep 4481801 = 3361351) B3361351
theorem B1770351 : Blo 1770086 1770351 := bstep (se 1 (by rfl) ⟨1327763, by rfl⟩ : syracuseStep 1770351 = 2655527) B2655527
theorem B8962973 : Blo 1770086 8962973 := bstep (se 3 (by rfl) ⟨1680557, by rfl⟩ : syracuseStep 8962973 = 3361115) B3361115
theorem B32301989 : Blo 1770086 32301989 := bstep (se 4 (by rfl) ⟨3028311, by rfl⟩ : syracuseStep 32301989 = 6056623) B6056623
theorem B2655143 : Blo 1770086 2655143 := bstep (se 1 (by rfl) ⟨1991357, by rfl⟩ : syracuseStep 2655143 = 3982715) B3982715
theorem B1770407 : Blo 1770086 1770407 := bstep (se 1 (by rfl) ⟨1327805, by rfl⟩ : syracuseStep 1770407 = 2655611) B2655611
theorem B2655227 : Blo 1770086 2655227 := bstep (se 1 (by rfl) ⟨1991420, by rfl⟩ : syracuseStep 2655227 = 3982841) B3982841
theorem B1770491 : Blo 1770086 1770491 := bstep (se 1 (by rfl) ⟨1327868, by rfl⟩ : syracuseStep 1770491 = 2655737) B2655737
theorem B2655287 : Blo 1770086 2655287 := bstep (se 1 (by rfl) ⟨1991465, by rfl⟩ : syracuseStep 2655287 = 3982931) B3982931
theorem B1770559 : Blo 1770086 1770559 := bstep (se 1 (by rfl) ⟨1327919, by rfl⟩ : syracuseStep 1770559 = 2655839) B2655839
theorem B2655407 : Blo 1770086 2655407 := bstep (se 1 (by rfl) ⟨1991555, by rfl⟩ : syracuseStep 2655407 = 3983111) B3983111
theorem B64627901 : Blo 1770086 64627901 := bstep (se 3 (by rfl) ⟨12117731, by rfl⟩ : syracuseStep 64627901 = 24235463) B24235463
theorem B1770703 : Blo 1770086 1770703 := bstep (se 1 (by rfl) ⟨1328027, by rfl⟩ : syracuseStep 1770703 = 2656055) B2656055
theorem B5113039 : Blo 1770086 5113039 := bstep (se 1 (by rfl) ⟨3834779, by rfl⟩ : syracuseStep 5113039 = 7669559) B7669559
theorem B1992091 : Blo 1770086 1992091 := bstep (se 1 (by rfl) ⟨1494068, by rfl⟩ : syracuseStep 1992091 = 2988137) B2988137
theorem B1770907 : Blo 1770086 1770907 := bstep (se 1 (by rfl) ⟨1328180, by rfl⟩ : syracuseStep 1770907 = 2656361) B2656361
theorem B4482479 : Blo 1770086 4482479 := bstep (se 1 (by rfl) ⟨3361859, by rfl⟩ : syracuseStep 4482479 = 6723719) B6723719
theorem B7562767 : Blo 1770086 7562767 := bstep (se 1 (by rfl) ⟨5672075, by rfl⟩ : syracuseStep 7562767 = 11344151) B11344151
theorem B2655815 : Blo 1770086 2655815 := bstep (se 1 (by rfl) ⟨1991861, by rfl⟩ : syracuseStep 2655815 = 3983723) B3983723
theorem B1771119 : Blo 1770086 1771119 := bstep (se 1 (by rfl) ⟨1328339, by rfl⟩ : syracuseStep 1771119 = 2656679) B2656679
theorem B2655911 : Blo 1770086 2655911 := bstep (se 1 (by rfl) ⟨1991933, by rfl⟩ : syracuseStep 2655911 = 3983867) B3983867
theorem B1771175 : Blo 1770086 1771175 := bstep (se 1 (by rfl) ⟨1328381, by rfl⟩ : syracuseStep 1771175 = 2656763) B2656763
theorem B21546719 : Blo 1770086 21546719 := bstep (se 1 (by rfl) ⟨16160039, by rfl⟩ : syracuseStep 21546719 = 32320079) B32320079
theorem B2655995 : Blo 1770086 2655995 := bstep (se 1 (by rfl) ⟨1991996, by rfl⟩ : syracuseStep 2655995 = 3983993) B3983993
theorem B1771259 : Blo 1770086 1771259 := bstep (se 1 (by rfl) ⟨1328444, by rfl⟩ : syracuseStep 1771259 = 2656889) B2656889
theorem B2656031 : Blo 1770086 2656031 := bstep (se 1 (by rfl) ⟨1992023, by rfl⟩ : syracuseStep 2656031 = 3984047) B3984047
theorem B1771295 : Blo 1770086 1771295 := bstep (se 1 (by rfl) ⟨1328471, by rfl⟩ : syracuseStep 1771295 = 2656943) B2656943
theorem B20178719 : Blo 1770086 20178719 := bstep (se 1 (by rfl) ⟨15134039, by rfl⟩ : syracuseStep 20178719 = 30268079) B30268079
theorem B1771327 : Blo 1770086 1771327 := bstep (se 1 (by rfl) ⟨1328495, by rfl⟩ : syracuseStep 1771327 = 2656991) B2656991
theorem B3983183 : Blo 1770086 3983183 := bstep (se 1 (by rfl) ⟨2987387, by rfl⟩ : syracuseStep 3983183 = 5974775) B5974775
theorem B2656079 : Blo 1770086 2656079 := bstep (se 1 (by rfl) ⟨1992059, by rfl⟩ : syracuseStep 2656079 = 3984119) B3984119
theorem B3983201 : Blo 1770086 3983201 := bstep (se 2 (by rfl) ⟨1493700, by rfl⟩ : syracuseStep 3983201 = 2987401) B2987401
theorem B10766209 : Blo 1770086 10766209 := bstep (se 2 (by rfl) ⟨4037328, by rfl⟩ : syracuseStep 10766209 = 8074657) B8074657
theorem B2656199 : Blo 1770086 2656199 := bstep (se 1 (by rfl) ⟨1992149, by rfl⟩ : syracuseStep 2656199 = 3984299) B3984299
theorem B5670857 : Blo 1770086 5670857 := bstep (se 2 (by rfl) ⟨2126571, by rfl⟩ : syracuseStep 5670857 = 4253143) B4253143
theorem B1771503 : Blo 1770086 1771503 := bstep (se 1 (by rfl) ⟨1328627, by rfl⟩ : syracuseStep 1771503 = 2657255) B2657255
theorem B7276553 : Blo 1770086 7276553 := bstep (se 2 (by rfl) ⟨2728707, by rfl⟩ : syracuseStep 7276553 = 5457415) B5457415
theorem B6727805 : Blo 1770086 6727805 := bstep (se 3 (by rfl) ⟨1261463, by rfl⟩ : syracuseStep 6727805 = 2522927) B2522927
theorem B32319641 : Blo 1770086 32319641 := bstep (se 2 (by rfl) ⟨12119865, by rfl⟩ : syracuseStep 32319641 = 24239731) B24239731
theorem B1771675 : Blo 1770086 1771675 := bstep (se 1 (by rfl) ⟨1328756, by rfl⟩ : syracuseStep 1771675 = 2657513) B2657513
theorem B1771711 : Blo 1770086 1771711 := bstep (se 1 (by rfl) ⟨1328783, by rfl⟩ : syracuseStep 1771711 = 2657567) B2657567
theorem B2836775 : Blo 1770086 2836775 := bstep (se 1 (by rfl) ⟨2127581, by rfl⟩ : syracuseStep 2836775 = 4255163) B4255163
theorem B2656553 : Blo 1770086 2656553 := bstep (se 2 (by rfl) ⟨996207, by rfl⟩ : syracuseStep 2656553 = 1992415) B1992415
theorem B2656559 : Blo 1770086 2656559 := bstep (se 1 (by rfl) ⟨1992419, by rfl⟩ : syracuseStep 2656559 = 3984839) B3984839
theorem B1771823 : Blo 1770086 1771823 := bstep (se 1 (by rfl) ⟨1328867, by rfl⟩ : syracuseStep 1771823 = 2657735) B2657735
theorem B19147103 : Blo 1770086 19147103 := bstep (se 1 (by rfl) ⟨14360327, by rfl⟩ : syracuseStep 19147103 = 28720655) B28720655
theorem B3983777 : Blo 1770086 3983777 := bstep (se 2 (by rfl) ⟨1493916, by rfl⟩ : syracuseStep 3983777 = 2987833) B2987833
theorem B1993243 : Blo 1770086 1993243 := bstep (se 1 (by rfl) ⟨1494932, by rfl⟩ : syracuseStep 1993243 = 2989865) B2989865
theorem B1772059 : Blo 1770086 1772059 := bstep (se 1 (by rfl) ⟨1329044, by rfl⟩ : syracuseStep 1772059 = 2658089) B2658089
theorem B5974559 : Blo 1770086 5974559 := bstep (se 1 (by rfl) ⟨4480919, by rfl⟩ : syracuseStep 5974559 = 8961839) B8961839
theorem B4254239 : Blo 1770086 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B3983903 : Blo 1770086 3983903 := bstep (se 1 (by rfl) ⟨2987927, by rfl⟩ : syracuseStep 3983903 = 5975855) B5975855
theorem B2656799 : Blo 1770086 2656799 := bstep (se 1 (by rfl) ⟨1992599, by rfl⟩ : syracuseStep 2656799 = 3985199) B3985199
theorem B1772063 : Blo 1770086 1772063 := bstep (se 1 (by rfl) ⟨1329047, by rfl⟩ : syracuseStep 1772063 = 2658095) B2658095
theorem B38292047 : Blo 1770086 38292047 := bstep (se 1 (by rfl) ⟨28719035, by rfl⟩ : syracuseStep 38292047 = 57438071) B57438071
theorem B8964755 : Blo 1770086 8964755 := bstep (se 1 (by rfl) ⟨6723566, by rfl⟩ : syracuseStep 8964755 = 13447133) B13447133
theorem B2837339 : Blo 1770086 2837339 := bstep (se 1 (by rfl) ⟨2128004, by rfl⟩ : syracuseStep 2837339 = 4256009) B4256009
theorem B2657183 : Blo 1770086 2657183 := bstep (se 1 (by rfl) ⟨1992887, by rfl⟩ : syracuseStep 2657183 = 3985775) B3985775
theorem B10087355 : Blo 1770086 10087355 := bstep (se 1 (by rfl) ⟨7565516, by rfl⟩ : syracuseStep 10087355 = 15131033) B15131033
theorem B2657231 : Blo 1770086 2657231 := bstep (se 1 (by rfl) ⟨1992923, by rfl⟩ : syracuseStep 2657231 = 3985847) B3985847
theorem B698862563 : Blo 1770086 698862563 := bstep (se 1 (by rfl) ⟨524146922, by rfl⟩ : syracuseStep 698862563 = 1048293845) B1048293845
theorem B22703111 : Blo 1770086 22703111 := bstep (se 1 (by rfl) ⟨17027333, by rfl⟩ : syracuseStep 22703111 = 34054667) B34054667
theorem B2657321 : Blo 1770086 2657321 := bstep (se 2 (by rfl) ⟨996495, by rfl⟩ : syracuseStep 2657321 = 1992991) B1992991
theorem B2657327 : Blo 1770086 2657327 := bstep (se 1 (by rfl) ⟨1992995, by rfl⟩ : syracuseStep 2657327 = 3985991) B3985991
theorem B2657351 : Blo 1770086 2657351 := bstep (se 1 (by rfl) ⟨1993013, by rfl⟩ : syracuseStep 2657351 = 3986027) B3986027
theorem B7564423 : Blo 1770086 7564423 := bstep (se 1 (by rfl) ⟨5673317, by rfl⟩ : syracuseStep 7564423 = 11346635) B11346635
theorem B3190025 : Blo 1770086 3190025 := bstep (se 2 (by rfl) ⟨1196259, by rfl⟩ : syracuseStep 3190025 = 2392519) B2392519
theorem B2657615 : Blo 1770086 2657615 := bstep (se 1 (by rfl) ⟨1993211, by rfl⟩ : syracuseStep 2657615 = 3986423) B3986423
theorem B38833505 : Blo 1770086 38833505 := bstep (se 2 (by rfl) ⟨14562564, by rfl⟩ : syracuseStep 38833505 = 29125129) B29125129
theorem B2657705 : Blo 1770086 2657705 := bstep (se 2 (by rfl) ⟨996639, by rfl⟩ : syracuseStep 2657705 = 1993279) B1993279
theorem B8965565 : Blo 1770086 8965565 := bstep (se 3 (by rfl) ⟨1681043, by rfl⟩ : syracuseStep 8965565 = 3362087) B3362087
theorem B2657855 : Blo 1770086 2657855 := bstep (se 1 (by rfl) ⟨1993391, by rfl⟩ : syracuseStep 2657855 = 3986783) B3986783
theorem B6721319 : Blo 1770086 6721319 := bstep (se 1 (by rfl) ⟨5040989, by rfl⟩ : syracuseStep 6721319 = 10081979) B10081979
theorem B2658119 : Blo 1770086 2658119 := bstep (se 1 (by rfl) ⟨1993589, by rfl⟩ : syracuseStep 2658119 = 3987179) B3987179
theorem B5975963 : Blo 1770086 5975963 := bstep (se 1 (by rfl) ⟨4481972, by rfl⟩ : syracuseStep 5975963 = 8963945) B8963945
theorem B3985307 : Blo 1770086 3985307 := bstep (se 1 (by rfl) ⟨2988980, by rfl⟩ : syracuseStep 3985307 = 5977961) B5977961
theorem B3985595 : Blo 1770086 3985595 := bstep (se 1 (by rfl) ⟨2989196, by rfl⟩ : syracuseStep 3985595 = 5978393) B5978393
theorem B7565501 : Blo 1770086 7565501 := bstep (se 3 (by rfl) ⟨1418531, by rfl⟩ : syracuseStep 7565501 = 2837063) B2837063
theorem B22696139 : Blo 1770086 22696139 := bstep (se 1 (by rfl) ⟨17022104, by rfl⟩ : syracuseStep 22696139 = 34044209) B34044209
theorem B14357087 : Blo 1770086 14357087 := bstep (se 1 (by rfl) ⟨10767815, by rfl⟩ : syracuseStep 14357087 = 21535631) B21535631
theorem B3986081 : Blo 1770086 3986081 := bstep (se 2 (by rfl) ⟨1494780, by rfl⟩ : syracuseStep 3986081 = 2989561) B2989561
theorem B12112859 : Blo 1770086 12112859 := bstep (se 1 (by rfl) ⟨9084644, by rfl⟩ : syracuseStep 12112859 = 18169289) B18169289
theorem B17028103 : Blo 1770086 17028103 := bstep (se 1 (by rfl) ⟨12771077, by rfl⟩ : syracuseStep 17028103 = 25542155) B25542155
theorem B5977097 : Blo 1770086 5977097 := bstep (se 2 (by rfl) ⟨2241411, by rfl⟩ : syracuseStep 5977097 = 4482823) B4482823
theorem B3986441 : Blo 1770086 3986441 := bstep (se 2 (by rfl) ⟨1494915, by rfl⟩ : syracuseStep 3986441 = 2989831) B2989831
theorem B5977151 : Blo 1770086 5977151 := bstep (se 1 (by rfl) ⟨4482863, by rfl⟩ : syracuseStep 5977151 = 8965727) B8965727
theorem B3986495 : Blo 1770086 3986495 := bstep (se 1 (by rfl) ⟨2989871, by rfl⟩ : syracuseStep 3986495 = 5979743) B5979743
theorem B2987435 : Blo 1770086 2987435 := bstep (se 1 (by rfl) ⟨2240576, by rfl⟩ : syracuseStep 2987435 = 4481153) B4481153
theorem B3782315 : Blo 1770086 3782315 := bstep (se 1 (by rfl) ⟨2836736, by rfl⟩ : syracuseStep 3782315 = 5673473) B5673473
theorem B5043883 : Blo 1770086 5043883 := bstep (se 1 (by rfl) ⟨3782912, by rfl⟩ : syracuseStep 5043883 = 7565825) B7565825
theorem B10229419 : Blo 1770086 10229419 := bstep (se 1 (by rfl) ⟨7672064, by rfl⟩ : syracuseStep 10229419 = 15344129) B15344129
theorem B3192539 : Blo 1770086 3192539 := bstep (se 1 (by rfl) ⟨2394404, by rfl⟩ : syracuseStep 3192539 = 4788809) B4788809
theorem B17012537 : Blo 1770086 17012537 := bstep (se 2 (by rfl) ⟨6379701, by rfl⟩ : syracuseStep 17012537 = 12759403) B12759403
theorem B38278979 : Blo 1770086 38278979 := bstep (se 1 (by rfl) ⟨28709234, by rfl⟩ : syracuseStep 38278979 = 57418469) B57418469
theorem B3192713 : Blo 1770086 3192713 := bstep (se 2 (by rfl) ⟨1197267, by rfl⟩ : syracuseStep 3192713 = 2394535) B2394535
theorem B19150739 : Blo 1770086 19150739 := bstep (se 1 (by rfl) ⟨14363054, by rfl⟩ : syracuseStep 19150739 = 28726109) B28726109
theorem B10082231 : Blo 1770086 10082231 := bstep (se 1 (by rfl) ⟨7561673, by rfl⟩ : syracuseStep 10082231 = 15123347) B15123347
theorem B2987975 : Blo 1770086 2987975 := bstep (se 1 (by rfl) ⟨2240981, by rfl⟩ : syracuseStep 2987975 = 4481963) B4481963
theorem B3782639 : Blo 1770086 3782639 := bstep (se 1 (by rfl) ⟨2836979, by rfl⟩ : syracuseStep 3782639 = 5673959) B5673959
theorem B7567465 : Blo 1770086 7567465 := bstep (se 2 (by rfl) ⟨2837799, by rfl⟩ : syracuseStep 7567465 = 5675599) B5675599
theorem B25524395 : Blo 1770086 25524395 := bstep (se 1 (by rfl) ⟨19143296, by rfl⟩ : syracuseStep 25524395 = 38286593) B38286593
theorem B2988265 : Blo 1770086 2988265 := bstep (se 2 (by rfl) ⟨1120599, by rfl⟩ : syracuseStep 2988265 = 2241199) B2241199
theorem B3783305 : Blo 1770086 3783305 := bstep (se 2 (by rfl) ⟨1418739, by rfl⟩ : syracuseStep 3783305 = 2837479) B2837479
theorem B2988731 : Blo 1770086 2988731 := bstep (se 1 (by rfl) ⟨2241548, by rfl⟩ : syracuseStep 2988731 = 4483097) B4483097
theorem B34036523 : Blo 1770086 34036523 := bstep (se 1 (by rfl) ⟨25527392, by rfl⟩ : syracuseStep 34036523 = 51054785) B51054785
theorem B45415241 : Blo 1770086 45415241 := bstep (se 2 (by rfl) ⟨17030715, by rfl⟩ : syracuseStep 45415241 = 34061431) B34061431
theorem B10083163 : Blo 1770086 10083163 := bstep (se 1 (by rfl) ⟨7562372, by rfl⟩ : syracuseStep 10083163 = 15124745) B15124745
theorem B4545505 : Blo 1770086 4545505 := bstep (se 2 (by rfl) ⟨1704564, by rfl⟩ : syracuseStep 4545505 = 3409129) B3409129
theorem B4545577 : Blo 1770086 4545577 := bstep (se 2 (by rfl) ⟨1704591, by rfl⟩ : syracuseStep 4545577 = 3409183) B3409183
theorem B2522335 : Blo 1770086 2522335 := bstep (se 1 (by rfl) ⟨1891751, by rfl⟩ : syracuseStep 2522335 = 3783503) B3783503
theorem B12770561 : Blo 1770086 12770561 := bstep (se 2 (by rfl) ⟨4788960, by rfl⟩ : syracuseStep 12770561 = 9577921) B9577921
theorem B13450535 : Blo 1770086 13450535 := bstep (se 1 (by rfl) ⟨10087901, by rfl⟩ : syracuseStep 13450535 = 20175803) B20175803
theorem B5045615 : Blo 1770086 5045615 := bstep (se 1 (by rfl) ⟨3784211, by rfl⟩ : syracuseStep 5045615 = 7568423) B7568423
theorem B22683017 : Blo 1770086 22683017 := bstep (se 2 (by rfl) ⟨8506131, by rfl⟩ : syracuseStep 22683017 = 17012263) B17012263
theorem B11353607 : Blo 1770086 11353607 := bstep (se 1 (by rfl) ⟨8515205, by rfl⟩ : syracuseStep 11353607 = 17030411) B17030411
theorem B12115493 : Blo 1770086 12115493 := bstep (se 4 (by rfl) ⟨1135827, by rfl⟩ : syracuseStep 12115493 = 2271655) B2271655
theorem B11353709 : Blo 1770086 11353709 := bstep (se 3 (by rfl) ⟨2128820, by rfl⟩ : syracuseStep 11353709 = 4257641) B4257641
theorem B5979959 : Blo 1770086 5979959 := bstep (se 1 (by rfl) ⟨4484969, by rfl⟩ : syracuseStep 5979959 = 8969939) B8969939
theorem B2523001 : Blo 1770086 2523001 := bstep (se 2 (by rfl) ⟨946125, by rfl⟩ : syracuseStep 2523001 = 1892251) B1892251
theorem B2523035 : Blo 1770086 2523035 := bstep (se 1 (by rfl) ⟨1892276, by rfl⟩ : syracuseStep 2523035 = 3784553) B3784553
theorem B2990047 : Blo 1770086 2990047 := bstep (se 1 (by rfl) ⟨2242535, by rfl⟩ : syracuseStep 2990047 = 4485071) B4485071
theorem B15130759 : Blo 1770086 15130759 := bstep (se 1 (by rfl) ⟨11348069, by rfl⟩ : syracuseStep 15130759 = 22696139) B22696139
theorem B1770095 : Blo 1770086 1770095 := bstep (se 1 (by rfl) ⟨1327571, by rfl⟩ : syracuseStep 1770095 = 2655143) B2655143
theorem B1770151 : Blo 1770086 1770151 := bstep (se 1 (by rfl) ⟨1327613, by rfl⟩ : syracuseStep 1770151 = 2655227) B2655227
theorem B1770191 : Blo 1770086 1770191 := bstep (se 1 (by rfl) ⟨1327643, by rfl⟩ : syracuseStep 1770191 = 2655287) B2655287
theorem B1770271 : Blo 1770086 1770271 := bstep (se 1 (by rfl) ⟨1327703, by rfl⟩ : syracuseStep 1770271 = 2655407) B2655407
theorem B1991623 : Blo 1770086 1991623 := bstep (se 1 (by rfl) ⟨1493717, by rfl⟩ : syracuseStep 1991623 = 2987435) B2987435
theorem B1770543 : Blo 1770086 1770543 := bstep (se 1 (by rfl) ⟨1327907, by rfl⟩ : syracuseStep 1770543 = 2655815) B2655815
theorem B1770607 : Blo 1770086 1770607 := bstep (se 1 (by rfl) ⟨1327955, by rfl⟩ : syracuseStep 1770607 = 2655911) B2655911
theorem B13444217 : Blo 1770086 13444217 := bstep (se 2 (by rfl) ⟨5041581, by rfl⟩ : syracuseStep 13444217 = 10083163) B10083163
theorem B1770663 : Blo 1770086 1770663 := bstep (se 1 (by rfl) ⟨1327997, by rfl⟩ : syracuseStep 1770663 = 2655995) B2655995
theorem B1770687 : Blo 1770086 1770687 := bstep (se 1 (by rfl) ⟨1328015, by rfl⟩ : syracuseStep 1770687 = 2656031) B2656031
theorem B13452479 : Blo 1770086 13452479 := bstep (se 1 (by rfl) ⟨10089359, by rfl⟩ : syracuseStep 13452479 = 20178719) B20178719
theorem B25519319 : Blo 1770086 25519319 := bstep (se 1 (by rfl) ⟨19139489, by rfl⟩ : syracuseStep 25519319 = 38278979) B38278979
theorem B2655455 : Blo 1770086 2655455 := bstep (se 1 (by rfl) ⟨1991591, by rfl⟩ : syracuseStep 2655455 = 3983183) B3983183
theorem B1770719 : Blo 1770086 1770719 := bstep (se 1 (by rfl) ⟨1328039, by rfl⟩ : syracuseStep 1770719 = 2656079) B2656079
theorem B2655467 : Blo 1770086 2655467 := bstep (se 1 (by rfl) ⟨1991600, by rfl⟩ : syracuseStep 2655467 = 3983201) B3983201
theorem B1991983 : Blo 1770086 1991983 := bstep (se 1 (by rfl) ⟨1493987, by rfl⟩ : syracuseStep 1991983 = 2987975) B2987975
theorem B1770799 : Blo 1770086 1770799 := bstep (se 1 (by rfl) ⟨1328099, by rfl⟩ : syracuseStep 1770799 = 2656199) B2656199
theorem B4851035 : Blo 1770086 4851035 := bstep (se 1 (by rfl) ⟨3638276, by rfl⟩ : syracuseStep 4851035 = 7276553) B7276553
theorem B21546427 : Blo 1770086 21546427 := bstep (se 1 (by rfl) ⟨16159820, by rfl⟩ : syracuseStep 21546427 = 32319641) B32319641
theorem B17016263 : Blo 1770086 17016263 := bstep (se 1 (by rfl) ⟨12762197, by rfl⟩ : syracuseStep 17016263 = 25524395) B25524395
theorem B10085897 : Blo 1770086 10085897 := bstep (se 2 (by rfl) ⟨3782211, by rfl⟩ : syracuseStep 10085897 = 7564423) B7564423
theorem B1771035 : Blo 1770086 1771035 := bstep (se 1 (by rfl) ⟨1328276, by rfl⟩ : syracuseStep 1771035 = 2656553) B2656553
theorem B1771039 : Blo 1770086 1771039 := bstep (se 1 (by rfl) ⟨1328279, by rfl⟩ : syracuseStep 1771039 = 2656559) B2656559
theorem B12764735 : Blo 1770086 12764735 := bstep (se 1 (by rfl) ⟨9573551, by rfl⟩ : syracuseStep 12764735 = 19147103) B19147103
theorem B6817385 : Blo 1770086 6817385 := bstep (se 2 (by rfl) ⟨2556519, by rfl⟩ : syracuseStep 6817385 = 5113039) B5113039
theorem B2655851 : Blo 1770086 2655851 := bstep (se 1 (by rfl) ⟨1991888, by rfl⟩ : syracuseStep 2655851 = 3983777) B3983777
theorem B3983039 : Blo 1770086 3983039 := bstep (se 1 (by rfl) ⟨2987279, by rfl⟩ : syracuseStep 3983039 = 5974559) B5974559
theorem B2655935 : Blo 1770086 2655935 := bstep (se 1 (by rfl) ⟨1991951, by rfl⟩ : syracuseStep 2655935 = 3983903) B3983903
theorem B1771199 : Blo 1770086 1771199 := bstep (se 1 (by rfl) ⟨1328399, by rfl⟩ : syracuseStep 1771199 = 2656799) B2656799
theorem B25528031 : Blo 1770086 25528031 := bstep (se 1 (by rfl) ⟨19146023, by rfl⟩ : syracuseStep 25528031 = 38292047) B38292047
theorem B1992487 : Blo 1770086 1992487 := bstep (se 1 (by rfl) ⟨1494365, by rfl⟩ : syracuseStep 1992487 = 2988731) B2988731
theorem B2656121 : Blo 1770086 2656121 := bstep (se 2 (by rfl) ⟨996045, by rfl⟩ : syracuseStep 2656121 = 1992091) B1992091
theorem B8513437 : Blo 1770086 8513437 := bstep (se 3 (by rfl) ⟨1596269, by rfl⟩ : syracuseStep 8513437 = 3192539) B3192539
theorem B1771455 : Blo 1770086 1771455 := bstep (se 1 (by rfl) ⟨1328591, by rfl⟩ : syracuseStep 1771455 = 2657183) B2657183
theorem B1771487 : Blo 1770086 1771487 := bstep (se 1 (by rfl) ⟨1328615, by rfl⟩ : syracuseStep 1771487 = 2657231) B2657231
theorem B1771547 : Blo 1770086 1771547 := bstep (se 1 (by rfl) ⟨1328660, by rfl⟩ : syracuseStep 1771547 = 2657321) B2657321
theorem B1771551 : Blo 1770086 1771551 := bstep (se 1 (by rfl) ⟨1328663, by rfl⟩ : syracuseStep 1771551 = 2657327) B2657327
theorem B1771567 : Blo 1770086 1771567 := bstep (se 1 (by rfl) ⟨1328675, by rfl⟩ : syracuseStep 1771567 = 2657351) B2657351
theorem B8513707 : Blo 1770086 8513707 := bstep (se 1 (by rfl) ⟨6385280, by rfl⟩ : syracuseStep 8513707 = 12770561) B12770561
theorem B1771743 : Blo 1770086 1771743 := bstep (se 1 (by rfl) ⟨1328807, by rfl⟩ : syracuseStep 1771743 = 2657615) B2657615
theorem B25889003 : Blo 1770086 25889003 := bstep (se 1 (by rfl) ⟨19416752, by rfl⟩ : syracuseStep 25889003 = 38833505) B38833505
theorem B1771803 : Blo 1770086 1771803 := bstep (se 1 (by rfl) ⟨1328852, by rfl⟩ : syracuseStep 1771803 = 2657705) B2657705
theorem B1771903 : Blo 1770086 1771903 := bstep (se 1 (by rfl) ⟨1328927, by rfl⟩ : syracuseStep 1771903 = 2657855) B2657855
theorem B6728093 : Blo 1770086 6728093 := bstep (se 3 (by rfl) ⟨1261517, by rfl⟩ : syracuseStep 6728093 = 2523035) B2523035
theorem B14354945 : Blo 1770086 14354945 := bstep (se 2 (by rfl) ⟨5383104, by rfl⟩ : syracuseStep 14354945 = 10766209) B10766209
theorem B1772079 : Blo 1770086 1772079 := bstep (se 1 (by rfl) ⟨1329059, by rfl⟩ : syracuseStep 1772079 = 2658119) B2658119
theorem B3983975 : Blo 1770086 3983975 := bstep (se 1 (by rfl) ⟨2987981, by rfl⟩ : syracuseStep 3983975 = 5975963) B5975963
theorem B2656871 : Blo 1770086 2656871 := bstep (se 1 (by rfl) ⟨1992653, by rfl⟩ : syracuseStep 2656871 = 3985307) B3985307
theorem B10087037 : Blo 1770086 10087037 := bstep (se 3 (by rfl) ⟨1891319, by rfl⟩ : syracuseStep 10087037 = 3782639) B3782639
theorem B34040519 : Blo 1770086 34040519 := bstep (se 1 (by rfl) ⟨25530389, by rfl⟩ : syracuseStep 34040519 = 51060779) B51060779
theorem B2657063 : Blo 1770086 2657063 := bstep (se 1 (by rfl) ⟨1992797, by rfl⟩ : syracuseStep 2657063 = 3985595) B3985595
theorem B24243077 : Blo 1770086 24243077 := bstep (se 4 (by rfl) ⟨2272788, by rfl⟩ : syracuseStep 24243077 = 4545577) B4545577
theorem B5974991 : Blo 1770086 5974991 := bstep (se 1 (by rfl) ⟨4481243, by rfl⟩ : syracuseStep 5974991 = 8962487) B8962487
theorem B3984353 : Blo 1770086 3984353 := bstep (se 2 (by rfl) ⟨1494132, by rfl⟩ : syracuseStep 3984353 = 2988265) B2988265
theorem B9571391 : Blo 1770086 9571391 := bstep (se 1 (by rfl) ⟨7178543, by rfl⟩ : syracuseStep 9571391 = 14357087) B14357087
theorem B2657387 : Blo 1770086 2657387 := bstep (se 1 (by rfl) ⟨1993040, by rfl⟩ : syracuseStep 2657387 = 3986081) B3986081
theorem B5975315 : Blo 1770086 5975315 := bstep (se 1 (by rfl) ⟨4481486, by rfl⟩ : syracuseStep 5975315 = 8962973) B8962973
theorem B3984731 : Blo 1770086 3984731 := bstep (se 1 (by rfl) ⟨2988548, by rfl⟩ : syracuseStep 3984731 = 5977097) B5977097
theorem B2657627 : Blo 1770086 2657627 := bstep (se 1 (by rfl) ⟨1993220, by rfl⟩ : syracuseStep 2657627 = 3986441) B3986441
theorem B2657657 : Blo 1770086 2657657 := bstep (se 2 (by rfl) ⟨996621, by rfl⟩ : syracuseStep 2657657 = 1993243) B1993243
theorem B3984767 : Blo 1770086 3984767 := bstep (se 1 (by rfl) ⟨2988575, by rfl⟩ : syracuseStep 3984767 = 5977151) B5977151
theorem B2657663 : Blo 1770086 2657663 := bstep (se 1 (by rfl) ⟨1993247, by rfl⟩ : syracuseStep 2657663 = 3986495) B3986495
theorem B43085267 : Blo 1770086 43085267 := bstep (se 1 (by rfl) ⟨32313950, by rfl⟩ : syracuseStep 43085267 = 64627901) B64627901
theorem B14364479 : Blo 1770086 14364479 := bstep (se 1 (by rfl) ⟨10773359, by rfl⟩ : syracuseStep 14364479 = 21546719) B21546719
theorem B11341691 : Blo 1770086 11341691 := bstep (se 1 (by rfl) ⟨8506268, by rfl⟩ : syracuseStep 11341691 = 17012537) B17012537
theorem B12767159 : Blo 1770086 12767159 := bstep (se 1 (by rfl) ⟨9575369, by rfl⟩ : syracuseStep 12767159 = 19150739) B19150739
theorem B6721487 : Blo 1770086 6721487 := bstep (se 1 (by rfl) ⟨5041115, by rfl⟩ : syracuseStep 6721487 = 10082231) B10082231
theorem B22704137 : Blo 1770086 22704137 := bstep (se 2 (by rfl) ⟨8514051, by rfl⟩ : syracuseStep 22704137 = 17028103) B17028103
theorem B4485203 : Blo 1770086 4485203 := bstep (se 1 (by rfl) ⟨3363902, by rfl⟩ : syracuseStep 4485203 = 6727805) B6727805
theorem B3363113 : Blo 1770086 3363113 := bstep (se 2 (by rfl) ⟨1261167, by rfl⟩ : syracuseStep 3363113 = 2522335) B2522335
theorem B10088813 : Blo 1770086 10088813 := bstep (se 3 (by rfl) ⟨1891652, by rfl⟩ : syracuseStep 10088813 = 3783305) B3783305
theorem B5976503 : Blo 1770086 5976503 := bstep (se 1 (by rfl) ⟨4482377, by rfl⟩ : syracuseStep 5976503 = 8964755) B8964755
theorem B465908375 : Blo 1770086 465908375 := bstep (se 1 (by rfl) ⟨349431281, by rfl⟩ : syracuseStep 465908375 = 698862563) B698862563
theorem B15135407 : Blo 1770086 15135407 := bstep (se 1 (by rfl) ⟨11351555, by rfl⟩ : syracuseStep 15135407 = 22703111) B22703111
theorem B2126683 : Blo 1770086 2126683 := bstep (se 1 (by rfl) ⟨1595012, by rfl⟩ : syracuseStep 2126683 = 3190025) B3190025
theorem B8967023 : Blo 1770086 8967023 := bstep (se 1 (by rfl) ⟨6725267, by rfl⟩ : syracuseStep 8967023 = 13450535) B13450535
theorem B3363743 : Blo 1770086 3363743 := bstep (se 1 (by rfl) ⟨2522807, by rfl⟩ : syracuseStep 3363743 = 5045615) B5045615
theorem B5977043 : Blo 1770086 5977043 := bstep (se 1 (by rfl) ⟨4482782, by rfl⟩ : syracuseStep 5977043 = 8965565) B8965565
theorem B3364001 : Blo 1770086 3364001 := bstep (se 2 (by rfl) ⟨1261500, by rfl⟩ : syracuseStep 3364001 = 2523001) B2523001
theorem B3986639 : Blo 1770086 3986639 := bstep (se 1 (by rfl) ⟨2989979, by rfl⟩ : syracuseStep 3986639 = 5979959) B5979959
theorem B3986729 : Blo 1770086 3986729 := bstep (se 2 (by rfl) ⟨1495023, by rfl⟩ : syracuseStep 3986729 = 2990047) B2990047
theorem B5043667 : Blo 1770086 5043667 := bstep (se 1 (by rfl) ⟨3782750, by rfl⟩ : syracuseStep 5043667 = 7565501) B7565501
theorem B10089953 : Blo 1770086 10089953 := bstep (se 2 (by rfl) ⟨3783732, by rfl⟩ : syracuseStep 10089953 = 7567465) B7567465
theorem B3986927 : Blo 1770086 3986927 := bstep (se 1 (by rfl) ⟨2990195, by rfl⟩ : syracuseStep 3986927 = 5980391) B5980391
theorem B16160411 : Blo 1770086 16160411 := bstep (se 1 (by rfl) ⟨12120308, by rfl⟩ : syracuseStep 16160411 = 24240617) B24240617
theorem B8509207 : Blo 1770086 8509207 := bstep (se 1 (by rfl) ⟨6381905, by rfl⟩ : syracuseStep 8509207 = 12763811) B12763811
theorem B2987867 : Blo 1770086 2987867 := bstep (se 1 (by rfl) ⟨2240900, by rfl⟩ : syracuseStep 2987867 = 4481801) B4481801
theorem B21534659 : Blo 1770086 21534659 := bstep (se 1 (by rfl) ⟨16150994, by rfl⟩ : syracuseStep 21534659 = 32301989) B32301989
theorem B54556901 : Blo 1770086 54556901 := bstep (se 4 (by rfl) ⟨5114709, by rfl⟩ : syracuseStep 54556901 = 10229419) B10229419
theorem B2988319 : Blo 1770086 2988319 := bstep (se 1 (by rfl) ⟨2241239, by rfl⟩ : syracuseStep 2988319 = 4482479) B4482479
theorem B2521543 : Blo 1770086 2521543 := bstep (se 1 (by rfl) ⟨1891157, by rfl⟩ : syracuseStep 2521543 = 3782315) B3782315
theorem B2128475 : Blo 1770086 2128475 := bstep (se 1 (by rfl) ⟨1596356, by rfl⟩ : syracuseStep 2128475 = 3192713) B3192713
theorem B6060673 : Blo 1770086 6060673 := bstep (se 2 (by rfl) ⟨2272752, by rfl⟩ : syracuseStep 6060673 = 4545505) B4545505
theorem B11344637 : Blo 1770086 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B1891183 : Blo 1770086 1891183 := bstep (se 1 (by rfl) ⟨1418387, by rfl⟩ : syracuseStep 1891183 = 2836775) B2836775
theorem B22691015 : Blo 1770086 22691015 := bstep (se 1 (by rfl) ⟨17018261, by rfl⟩ : syracuseStep 22691015 = 34036523) B34036523
theorem B30276827 : Blo 1770086 30276827 := bstep (se 1 (by rfl) ⟨22707620, by rfl⟩ : syracuseStep 30276827 = 45415241) B45415241
theorem B1891559 : Blo 1770086 1891559 := bstep (se 1 (by rfl) ⟨1418669, by rfl⟩ : syracuseStep 1891559 = 2837339) B2837339
theorem B6724903 : Blo 1770086 6724903 := bstep (se 1 (by rfl) ⟨5043677, by rfl⟩ : syracuseStep 6724903 = 10087355) B10087355
theorem B10083689 : Blo 1770086 10083689 := bstep (se 2 (by rfl) ⟨3781383, by rfl⟩ : syracuseStep 10083689 = 7562767) B7562767
theorem B6725177 : Blo 1770086 6725177 := bstep (se 2 (by rfl) ⟨2521941, by rfl⟩ : syracuseStep 6725177 = 5043883) B5043883
theorem B15122011 : Blo 1770086 15122011 := bstep (se 1 (by rfl) ⟨11341508, by rfl⟩ : syracuseStep 15122011 = 22683017) B22683017
theorem B7569071 : Blo 1770086 7569071 := bstep (se 1 (by rfl) ⟨5676803, by rfl⟩ : syracuseStep 7569071 = 11353607) B11353607
theorem B8076995 : Blo 1770086 8076995 := bstep (se 1 (by rfl) ⟨6057746, by rfl⟩ : syracuseStep 8076995 = 12115493) B12115493
theorem B7569139 : Blo 1770086 7569139 := bstep (se 1 (by rfl) ⟨5676854, by rfl⟩ : syracuseStep 7569139 = 11353709) B11353709
theorem B15122285 : Blo 1770086 15122285 := bstep (se 3 (by rfl) ⟨2835428, by rfl⟩ : syracuseStep 15122285 = 5670857) B5670857
theorem B4480879 : Blo 1770086 4480879 := bstep (se 1 (by rfl) ⟨3360659, by rfl⟩ : syracuseStep 4480879 = 6721319) B6721319
theorem B32300957 : Blo 1770086 32300957 := bstep (se 3 (by rfl) ⟨6056429, by rfl⟩ : syracuseStep 32300957 = 12112859) B12112859
theorem B2990135 : Blo 1770086 2990135 := bstep (se 1 (by rfl) ⟨2242601, by rfl⟩ : syracuseStep 2990135 = 4485203) B4485203
theorem B6725875 : Blo 1770086 6725875 := bstep (se 1 (by rfl) ⟨5044406, by rfl⟩ : syracuseStep 6725875 = 10088813) B10088813
theorem B8962811 : Blo 1770086 8962811 := bstep (se 1 (by rfl) ⟨6722108, by rfl⟩ : syracuseStep 8962811 = 13444217) B13444217
theorem B1770303 : Blo 1770086 1770303 := bstep (se 1 (by rfl) ⟨1327727, by rfl⟩ : syracuseStep 1770303 = 2655455) B2655455
theorem B1770311 : Blo 1770086 1770311 := bstep (se 1 (by rfl) ⟨1327733, by rfl⟩ : syracuseStep 1770311 = 2655467) B2655467
theorem B6726635 : Blo 1770086 6726635 := bstep (se 1 (by rfl) ⟨5044976, by rfl⟩ : syracuseStep 6726635 = 10089953) B10089953
theorem B1770567 : Blo 1770086 1770567 := bstep (se 1 (by rfl) ⟨1327925, by rfl⟩ : syracuseStep 1770567 = 2655851) B2655851
theorem B10773607 : Blo 1770086 10773607 := bstep (se 1 (by rfl) ⟨8080205, by rfl⟩ : syracuseStep 10773607 = 16160411) B16160411
theorem B2835577 : Blo 1770086 2835577 := bstep (se 2 (by rfl) ⟨1063341, by rfl⟩ : syracuseStep 2835577 = 2126683) B2126683
theorem B2655359 : Blo 1770086 2655359 := bstep (se 1 (by rfl) ⟨1991519, by rfl⟩ : syracuseStep 2655359 = 3983039) B3983039
theorem B1770623 : Blo 1770086 1770623 := bstep (se 1 (by rfl) ⟨1327967, by rfl⟩ : syracuseStep 1770623 = 2655935) B2655935
theorem B1991911 : Blo 1770086 1991911 := bstep (se 1 (by rfl) ⟨1493933, by rfl⟩ : syracuseStep 1991911 = 2987867) B2987867
theorem B1770747 : Blo 1770086 1770747 := bstep (se 1 (by rfl) ⟨1328060, by rfl⟩ : syracuseStep 1770747 = 2656121) B2656121
theorem B2655497 : Blo 1770086 2655497 := bstep (se 2 (by rfl) ⟨995811, by rfl⟩ : syracuseStep 2655497 = 1991623) B1991623
theorem B9569963 : Blo 1770086 9569963 := bstep (se 1 (by rfl) ⟨7177472, by rfl⟩ : syracuseStep 9569963 = 14354945) B14354945
theorem B2655977 : Blo 1770086 2655977 := bstep (se 2 (by rfl) ⟨995991, by rfl⟩ : syracuseStep 2655977 = 1991983) B1991983
theorem B2655983 : Blo 1770086 2655983 := bstep (se 1 (by rfl) ⟨1991987, by rfl⟩ : syracuseStep 2655983 = 3983975) B3983975
theorem B1771247 : Blo 1770086 1771247 := bstep (se 1 (by rfl) ⟨1328435, by rfl⟩ : syracuseStep 1771247 = 2656871) B2656871
theorem B22693679 : Blo 1770086 22693679 := bstep (se 1 (by rfl) ⟨17020259, by rfl⟩ : syracuseStep 22693679 = 34040519) B34040519
theorem B7563091 : Blo 1770086 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B1771375 : Blo 1770086 1771375 := bstep (se 1 (by rfl) ⟨1328531, by rfl⟩ : syracuseStep 1771375 = 2657063) B2657063
theorem B3983327 : Blo 1770086 3983327 := bstep (se 1 (by rfl) ⟨2987495, by rfl⟩ : syracuseStep 3983327 = 5974991) B5974991
theorem B2656235 : Blo 1770086 2656235 := bstep (se 1 (by rfl) ⟨1992176, by rfl⟩ : syracuseStep 2656235 = 3984353) B3984353
theorem B1771591 : Blo 1770086 1771591 := bstep (se 1 (by rfl) ⟨1328693, by rfl⟩ : syracuseStep 1771591 = 2657387) B2657387
theorem B20162681 : Blo 1770086 20162681 := bstep (se 2 (by rfl) ⟨7561005, by rfl⟩ : syracuseStep 20162681 = 15122011) B15122011
theorem B3983543 : Blo 1770086 3983543 := bstep (se 1 (by rfl) ⟨2987657, by rfl⟩ : syracuseStep 3983543 = 5975315) B5975315
theorem B2656487 : Blo 1770086 2656487 := bstep (se 1 (by rfl) ⟨1992365, by rfl⟩ : syracuseStep 2656487 = 3984731) B3984731
theorem B1771751 : Blo 1770086 1771751 := bstep (se 1 (by rfl) ⟨1328813, by rfl⟩ : syracuseStep 1771751 = 2657627) B2657627
theorem B1771771 : Blo 1770086 1771771 := bstep (se 1 (by rfl) ⟨1328828, by rfl⟩ : syracuseStep 1771771 = 2657657) B2657657
theorem B2656511 : Blo 1770086 2656511 := bstep (se 1 (by rfl) ⟨1992383, by rfl⟩ : syracuseStep 2656511 = 3984767) B3984767
theorem B1771775 : Blo 1770086 1771775 := bstep (se 1 (by rfl) ⟨1328831, by rfl⟩ : syracuseStep 1771775 = 2657663) B2657663
theorem B28723511 : Blo 1770086 28723511 := bstep (se 1 (by rfl) ⟨21542633, by rfl⟩ : syracuseStep 28723511 = 43085267) B43085267
theorem B4483451 : Blo 1770086 4483451 := bstep (se 1 (by rfl) ⟨3362588, by rfl⟩ : syracuseStep 4483451 = 6725177) B6725177
theorem B2656649 : Blo 1770086 2656649 := bstep (se 2 (by rfl) ⟨996243, by rfl⟩ : syracuseStep 2656649 = 1992487) B1992487
theorem B5384663 : Blo 1770086 5384663 := bstep (se 1 (by rfl) ⟨4038497, by rfl⟩ : syracuseStep 5384663 = 8076995) B8076995
theorem B5974505 : Blo 1770086 5974505 := bstep (se 2 (by rfl) ⟨2240439, by rfl⟩ : syracuseStep 5974505 = 4480879) B4480879
theorem B3984335 : Blo 1770086 3984335 := bstep (se 1 (by rfl) ⟨2988251, by rfl⟩ : syracuseStep 3984335 = 5976503) B5976503
theorem B3984425 : Blo 1770086 3984425 := bstep (se 2 (by rfl) ⟨1494159, by rfl⟩ : syracuseStep 3984425 = 2988319) B2988319
theorem B3362057 : Blo 1770086 3362057 := bstep (se 2 (by rfl) ⟨1260771, by rfl⟩ : syracuseStep 3362057 = 2521543) B2521543
theorem B3984695 : Blo 1770086 3984695 := bstep (se 1 (by rfl) ⟨2988521, by rfl⟩ : syracuseStep 3984695 = 5977043) B5977043
theorem B2657759 : Blo 1770086 2657759 := bstep (se 1 (by rfl) ⟨1993319, by rfl⟩ : syracuseStep 2657759 = 3986639) B3986639
theorem B8080897 : Blo 1770086 8080897 := bstep (se 2 (by rfl) ⟨3030336, by rfl⟩ : syracuseStep 8080897 = 6060673) B6060673
theorem B2657819 : Blo 1770086 2657819 := bstep (se 1 (by rfl) ⟨1993364, by rfl⟩ : syracuseStep 2657819 = 3986729) B3986729
theorem B2657951 : Blo 1770086 2657951 := bstep (se 1 (by rfl) ⟨1993463, by rfl⟩ : syracuseStep 2657951 = 3986927) B3986927
theorem B17018687 : Blo 1770086 17018687 := bstep (se 1 (by rfl) ⟨12764015, by rfl⟩ : syracuseStep 17018687 = 25528031) B25528031
theorem B14356439 : Blo 1770086 14356439 := bstep (se 1 (by rfl) ⟨10767329, by rfl⟩ : syracuseStep 14356439 = 21534659) B21534659
theorem B4485395 : Blo 1770086 4485395 := bstep (se 1 (by rfl) ⟨3364046, by rfl⟩ : syracuseStep 4485395 = 6728093) B6728093
theorem B8966537 : Blo 1770086 8966537 := bstep (se 2 (by rfl) ⟨3362451, by rfl⟩ : syracuseStep 8966537 = 6724903) B6724903
theorem B15127343 : Blo 1770086 15127343 := bstep (se 1 (by rfl) ⟨11345507, by rfl⟩ : syracuseStep 15127343 = 22691015) B22691015
theorem B6722459 : Blo 1770086 6722459 := bstep (se 1 (by rfl) ⟨5041844, by rfl⟩ : syracuseStep 6722459 = 10083689) B10083689
theorem B86135885 : Blo 1770086 86135885 := bstep (se 3 (by rfl) ⟨16150478, by rfl⟩ : syracuseStep 86135885 = 32300957) B32300957
theorem B11351249 : Blo 1770086 11351249 := bstep (se 2 (by rfl) ⟨4256718, by rfl⟩ : syracuseStep 11351249 = 8513437) B8513437
theorem B10081523 : Blo 1770086 10081523 := bstep (se 1 (by rfl) ⟨7561142, by rfl⟩ : syracuseStep 10081523 = 15122285) B15122285
theorem B15136091 : Blo 1770086 15136091 := bstep (se 1 (by rfl) ⟨11352068, by rfl⟩ : syracuseStep 15136091 = 22704137) B22704137
theorem B20174345 : Blo 1770086 20174345 := bstep (se 2 (by rfl) ⟨7565379, by rfl⟩ : syracuseStep 20174345 = 15130759) B15130759
theorem B2242075 : Blo 1770086 2242075 := bstep (se 1 (by rfl) ⟨1681556, by rfl⟩ : syracuseStep 2242075 = 3363113) B3363113
theorem B11351609 : Blo 1770086 11351609 := bstep (se 2 (by rfl) ⟨4256853, by rfl⟩ : syracuseStep 11351609 = 8513707) B8513707
theorem B310605583 : Blo 1770086 310605583 := bstep (se 1 (by rfl) ⟨232954187, by rfl⟩ : syracuseStep 310605583 = 465908375) B465908375
theorem B10090271 : Blo 1770086 10090271 := bstep (se 1 (by rfl) ⟨7567703, by rfl⟩ : syracuseStep 10090271 = 15135407) B15135407
theorem B5978015 : Blo 1770086 5978015 := bstep (se 1 (by rfl) ⟨4483511, by rfl⟩ : syracuseStep 5978015 = 8967023) B8967023
theorem B5044157 : Blo 1770086 5044157 := bstep (se 3 (by rfl) ⟨945779, by rfl⟩ : syracuseStep 5044157 = 1891559) B1891559
theorem B2242495 : Blo 1770086 2242495 := bstep (se 1 (by rfl) ⟨1681871, by rfl⟩ : syracuseStep 2242495 = 3363743) B3363743
theorem B2242667 : Blo 1770086 2242667 := bstep (se 1 (by rfl) ⟨1682000, by rfl⟩ : syracuseStep 2242667 = 3364001) B3364001
theorem B8968319 : Blo 1770086 8968319 := bstep (se 1 (by rfl) ⟨6726239, by rfl⟩ : syracuseStep 8968319 = 13452479) B13452479
theorem B17012879 : Blo 1770086 17012879 := bstep (se 1 (by rfl) ⟨12759659, by rfl⟩ : syracuseStep 17012879 = 25519319) B25519319
theorem B3234023 : Blo 1770086 3234023 := bstep (se 1 (by rfl) ⟨2425517, by rfl⟩ : syracuseStep 3234023 = 4851035) B4851035
theorem B11344175 : Blo 1770086 11344175 := bstep (se 1 (by rfl) ⟨8508131, by rfl⟩ : syracuseStep 11344175 = 17016263) B17016263
theorem B6723931 : Blo 1770086 6723931 := bstep (se 1 (by rfl) ⟨5042948, by rfl⟩ : syracuseStep 6723931 = 10085897) B10085897
theorem B8509823 : Blo 1770086 8509823 := bstep (se 1 (by rfl) ⟨6382367, by rfl⟩ : syracuseStep 8509823 = 12764735) B12764735
theorem B4544923 : Blo 1770086 4544923 := bstep (se 1 (by rfl) ⟨3408692, by rfl⟩ : syracuseStep 4544923 = 6817385) B6817385
theorem B2521577 : Blo 1770086 2521577 := bstep (se 2 (by rfl) ⟨945591, by rfl⟩ : syracuseStep 2521577 = 1891183) B1891183
theorem B36371267 : Blo 1770086 36371267 := bstep (se 1 (by rfl) ⟨27278450, by rfl⟩ : syracuseStep 36371267 = 54556901) B54556901
theorem B17259335 : Blo 1770086 17259335 := bstep (se 1 (by rfl) ⟨12944501, by rfl⟩ : syracuseStep 17259335 = 25889003) B25889003
theorem B5675933 : Blo 1770086 5675933 := bstep (se 3 (by rfl) ⟨1064237, by rfl⟩ : syracuseStep 5675933 = 2128475) B2128475
theorem B6724691 : Blo 1770086 6724691 := bstep (se 1 (by rfl) ⟨5043518, by rfl⟩ : syracuseStep 6724691 = 10087037) B10087037
theorem B28728569 : Blo 1770086 28728569 := bstep (se 2 (by rfl) ⟨10773213, by rfl⟩ : syracuseStep 28728569 = 21546427) B21546427
theorem B16162051 : Blo 1770086 16162051 := bstep (se 1 (by rfl) ⟨12121538, by rfl⟩ : syracuseStep 16162051 = 24243077) B24243077
theorem B6724889 : Blo 1770086 6724889 := bstep (se 2 (by rfl) ⟨2521833, by rfl⟩ : syracuseStep 6724889 = 5043667) B5043667
theorem B6380927 : Blo 1770086 6380927 := bstep (se 1 (by rfl) ⟨4785695, by rfl⟩ : syracuseStep 6380927 = 9571391) B9571391
theorem B20184551 : Blo 1770086 20184551 := bstep (se 1 (by rfl) ⟨15138413, by rfl⟩ : syracuseStep 20184551 = 30276827) B30276827
theorem B10092185 : Blo 1770086 10092185 := bstep (se 2 (by rfl) ⟨3784569, by rfl⟩ : syracuseStep 10092185 = 7569139) B7569139
theorem B11345609 : Blo 1770086 11345609 := bstep (se 2 (by rfl) ⟨4254603, by rfl⟩ : syracuseStep 11345609 = 8509207) B8509207
theorem B5046047 : Blo 1770086 5046047 := bstep (se 1 (by rfl) ⟨3784535, by rfl⟩ : syracuseStep 5046047 = 7569071) B7569071
theorem B9576319 : Blo 1770086 9576319 := bstep (se 1 (by rfl) ⟨7182239, by rfl⟩ : syracuseStep 9576319 = 14364479) B14364479
theorem B7561127 : Blo 1770086 7561127 := bstep (se 1 (by rfl) ⟨5670845, by rfl⟩ : syracuseStep 7561127 = 11341691) B11341691
theorem B8511439 : Blo 1770086 8511439 := bstep (se 1 (by rfl) ⟨6383579, by rfl⟩ : syracuseStep 8511439 = 12767159) B12767159
theorem B4480991 : Blo 1770086 4480991 := bstep (se 1 (by rfl) ⟨3360743, by rfl⟩ : syracuseStep 4480991 = 6721487) B6721487
theorem B2990263 : Blo 1770086 2990263 := bstep (se 1 (by rfl) ⟨2242697, by rfl⟩ : syracuseStep 2990263 = 4485395) B4485395
theorem B5980445 : Blo 1770086 5980445 := bstep (se 3 (by rfl) ⟨1121333, by rfl⟩ : syracuseStep 5980445 = 2242667) B2242667
theorem B10084895 : Blo 1770086 10084895 := bstep (se 1 (by rfl) ⟨7563671, by rfl⟩ : syracuseStep 10084895 = 15127343) B15127343
theorem B4481639 : Blo 1770086 4481639 := bstep (se 1 (by rfl) ⟨3361229, by rfl⟩ : syracuseStep 4481639 = 6722459) B6722459
theorem B1770239 : Blo 1770086 1770239 := bstep (se 1 (by rfl) ⟨1327679, by rfl⟩ : syracuseStep 1770239 = 2655359) B2655359
theorem B1770331 : Blo 1770086 1770331 := bstep (se 1 (by rfl) ⟨1327748, by rfl⟩ : syracuseStep 1770331 = 2655497) B2655497
theorem B1770651 : Blo 1770086 1770651 := bstep (se 1 (by rfl) ⟨1327988, by rfl⟩ : syracuseStep 1770651 = 2655977) B2655977
theorem B1770655 : Blo 1770086 1770655 := bstep (se 1 (by rfl) ⟨1327991, by rfl⟩ : syracuseStep 1770655 = 2655983) B2655983
theorem B6726847 : Blo 1770086 6726847 := bstep (se 1 (by rfl) ⟨5045135, by rfl⟩ : syracuseStep 6726847 = 10090271) B10090271
theorem B2655551 : Blo 1770086 2655551 := bstep (se 1 (by rfl) ⟨1991663, by rfl⟩ : syracuseStep 2655551 = 3983327) B3983327
theorem B1770823 : Blo 1770086 1770823 := bstep (se 1 (by rfl) ⟨1328117, by rfl⟩ : syracuseStep 1770823 = 2656235) B2656235
theorem B2655695 : Blo 1770086 2655695 := bstep (se 1 (by rfl) ⟨1991771, by rfl⟩ : syracuseStep 2655695 = 3983543) B3983543
theorem B2156015 : Blo 1770086 2156015 := bstep (se 1 (by rfl) ⟨1617011, by rfl⟩ : syracuseStep 2156015 = 3234023) B3234023
theorem B1770991 : Blo 1770086 1770991 := bstep (se 1 (by rfl) ⟨1328243, by rfl⟩ : syracuseStep 1770991 = 2656487) B2656487
theorem B1771007 : Blo 1770086 1771007 := bstep (se 1 (by rfl) ⟨1328255, by rfl⟩ : syracuseStep 1771007 = 2656511) B2656511
theorem B7562783 : Blo 1770086 7562783 := bstep (se 1 (by rfl) ⟨5672087, by rfl⟩ : syracuseStep 7562783 = 11344175) B11344175
theorem B1771099 : Blo 1770086 1771099 := bstep (se 1 (by rfl) ⟨1328324, by rfl⟩ : syracuseStep 1771099 = 2656649) B2656649
theorem B2655881 : Blo 1770086 2655881 := bstep (se 2 (by rfl) ⟨995955, by rfl⟩ : syracuseStep 2655881 = 1991911) B1991911
theorem B3589775 : Blo 1770086 3589775 := bstep (se 1 (by rfl) ⟨2692331, by rfl⟩ : syracuseStep 3589775 = 5384663) B5384663
theorem B3983003 : Blo 1770086 3983003 := bstep (se 1 (by rfl) ⟨2987252, by rfl⟩ : syracuseStep 3983003 = 5974505) B5974505
theorem B30254957 : Blo 1770086 30254957 := bstep (se 3 (by rfl) ⟨5672804, by rfl⟩ : syracuseStep 30254957 = 11345609) B11345609
theorem B2656223 : Blo 1770086 2656223 := bstep (se 1 (by rfl) ⟨1992167, by rfl⟩ : syracuseStep 2656223 = 3984335) B3984335
theorem B10774529 : Blo 1770086 10774529 := bstep (se 2 (by rfl) ⟨4040448, by rfl⟩ : syracuseStep 10774529 = 8080897) B8080897
theorem B2656283 : Blo 1770086 2656283 := bstep (se 1 (by rfl) ⟨1992212, by rfl⟩ : syracuseStep 2656283 = 3984425) B3984425
theorem B4483127 : Blo 1770086 4483127 := bstep (se 1 (by rfl) ⟨3362345, by rfl⟩ : syracuseStep 4483127 = 6724691) B6724691
theorem B4483259 : Blo 1770086 4483259 := bstep (se 1 (by rfl) ⟨3362444, by rfl⟩ : syracuseStep 4483259 = 6724889) B6724889
theorem B2656463 : Blo 1770086 2656463 := bstep (se 1 (by rfl) ⟨1992347, by rfl⟩ : syracuseStep 2656463 = 3984695) B3984695
theorem B4253951 : Blo 1770086 4253951 := bstep (se 1 (by rfl) ⟨3190463, by rfl⟩ : syracuseStep 4253951 = 6380927) B6380927
theorem B1771839 : Blo 1770086 1771839 := bstep (se 1 (by rfl) ⟨1328879, by rfl⟩ : syracuseStep 1771839 = 2657759) B2657759
theorem B1771879 : Blo 1770086 1771879 := bstep (se 1 (by rfl) ⟨1328909, by rfl⟩ : syracuseStep 1771879 = 2657819) B2657819
theorem B414140777 : Blo 1770086 414140777 := bstep (se 2 (by rfl) ⟨155302791, by rfl⟩ : syracuseStep 414140777 = 310605583) B310605583
theorem B6728123 : Blo 1770086 6728123 := bstep (se 1 (by rfl) ⟨5046092, by rfl⟩ : syracuseStep 6728123 = 10092185) B10092185
theorem B1771967 : Blo 1770086 1771967 := bstep (se 1 (by rfl) ⟨1328975, by rfl⟩ : syracuseStep 1771967 = 2657951) B2657951
theorem B11348585 : Blo 1770086 11348585 := bstep (se 2 (by rfl) ⟨4255719, by rfl⟩ : syracuseStep 11348585 = 8511439) B8511439
theorem B5040751 : Blo 1770086 5040751 := bstep (se 1 (by rfl) ⟨3780563, by rfl⟩ : syracuseStep 5040751 = 7561127) B7561127
theorem B9570959 : Blo 1770086 9570959 := bstep (se 1 (by rfl) ⟨7178219, by rfl⟩ : syracuseStep 9570959 = 14356439) B14356439
theorem B1993423 : Blo 1770086 1993423 := bstep (se 1 (by rfl) ⟨1495067, by rfl⟩ : syracuseStep 1993423 = 2990135) B2990135
theorem B8965241 : Blo 1770086 8965241 := bstep (se 2 (by rfl) ⟨3361965, by rfl⟩ : syracuseStep 8965241 = 6723931) B6723931
theorem B5975207 : Blo 1770086 5975207 := bstep (se 1 (by rfl) ⟨4481405, by rfl⟩ : syracuseStep 5975207 = 8962811) B8962811
theorem B4484423 : Blo 1770086 4484423 := bstep (se 1 (by rfl) ⟨3363317, by rfl⟩ : syracuseStep 4484423 = 6726635) B6726635
theorem B6721015 : Blo 1770086 6721015 := bstep (se 1 (by rfl) ⟨5040761, by rfl⟩ : syracuseStep 6721015 = 10081523) B10081523
theorem B3985343 : Blo 1770086 3985343 := bstep (se 1 (by rfl) ⟨2989007, by rfl⟩ : syracuseStep 3985343 = 5978015) B5978015
theorem B3362771 : Blo 1770086 3362771 := bstep (se 1 (by rfl) ⟨2522078, by rfl⟩ : syracuseStep 3362771 = 5044157) B5044157
theorem B11341919 : Blo 1770086 11341919 := bstep (se 1 (by rfl) ⟨8506439, by rfl⟩ : syracuseStep 11341919 = 17012879) B17012879
theorem B14364809 : Blo 1770086 14364809 := bstep (se 2 (by rfl) ⟨5386803, by rfl⟩ : syracuseStep 14364809 = 10773607) B10773607
theorem B3780769 : Blo 1770086 3780769 := bstep (se 2 (by rfl) ⟨1417788, by rfl⟩ : syracuseStep 3780769 = 2835577) B2835577
theorem B19149007 : Blo 1770086 19149007 := bstep (se 1 (by rfl) ⟨14361755, by rfl⟩ : syracuseStep 19149007 = 28723511) B28723511
theorem B5673215 : Blo 1770086 5673215 := bstep (se 1 (by rfl) ⟨4254911, by rfl⟩ : syracuseStep 5673215 = 8509823) B8509823
theorem B21549401 : Blo 1770086 21549401 := bstep (se 2 (by rfl) ⟨8081025, by rfl⟩ : syracuseStep 21549401 = 16162051) B16162051
theorem B11506223 : Blo 1770086 11506223 := bstep (se 1 (by rfl) ⟨8629667, by rfl⟩ : syracuseStep 11506223 = 17259335) B17259335
theorem B2241371 : Blo 1770086 2241371 := bstep (se 1 (by rfl) ⟨1681028, by rfl⟩ : syracuseStep 2241371 = 3362057) B3362057
theorem B13456367 : Blo 1770086 13456367 := bstep (se 1 (by rfl) ⟨10092275, by rfl⟩ : syracuseStep 13456367 = 20184551) B20184551
theorem B12768425 : Blo 1770086 12768425 := bstep (se 2 (by rfl) ⟨4788159, by rfl⟩ : syracuseStep 12768425 = 9576319) B9576319
theorem B3364031 : Blo 1770086 3364031 := bstep (se 1 (by rfl) ⟨2523023, by rfl⟩ : syracuseStep 3364031 = 5046047) B5046047
theorem B2987327 : Blo 1770086 2987327 := bstep (se 1 (by rfl) ⟨2240495, by rfl⟩ : syracuseStep 2987327 = 4480991) B4480991
theorem B5977691 : Blo 1770086 5977691 := bstep (se 1 (by rfl) ⟨4483268, by rfl⟩ : syracuseStep 5977691 = 8966537) B8966537
theorem B8967833 : Blo 1770086 8967833 := bstep (se 2 (by rfl) ⟨3362937, by rfl⟩ : syracuseStep 8967833 = 6725875) B6725875
theorem B6059897 : Blo 1770086 6059897 := bstep (se 2 (by rfl) ⟨2272461, by rfl⟩ : syracuseStep 6059897 = 4544923) B4544923
theorem B57423923 : Blo 1770086 57423923 := bstep (se 1 (by rfl) ⟨43067942, by rfl⟩ : syracuseStep 57423923 = 86135885) B86135885
theorem B7567499 : Blo 1770086 7567499 := bstep (se 1 (by rfl) ⟨5675624, by rfl⟩ : syracuseStep 7567499 = 11351249) B11351249
theorem B10090727 : Blo 1770086 10090727 := bstep (se 1 (by rfl) ⟨7568045, by rfl⟩ : syracuseStep 10090727 = 15136091) B15136091
theorem B13449563 : Blo 1770086 13449563 := bstep (se 1 (by rfl) ⟨10087172, by rfl⟩ : syracuseStep 13449563 = 20174345) B20174345
theorem B7567739 : Blo 1770086 7567739 := bstep (se 1 (by rfl) ⟨5675804, by rfl⟩ : syracuseStep 7567739 = 11351609) B11351609
theorem B6379975 : Blo 1770086 6379975 := bstep (se 1 (by rfl) ⟨4784981, by rfl⟩ : syracuseStep 6379975 = 9569963) B9569963
theorem B15129119 : Blo 1770086 15129119 := bstep (se 1 (by rfl) ⟨11346839, by rfl⟩ : syracuseStep 15129119 = 22693679) B22693679
theorem B6724205 : Blo 1770086 6724205 := bstep (se 3 (by rfl) ⟨1260788, by rfl⟩ : syracuseStep 6724205 = 2521577) B2521577
theorem B13441787 : Blo 1770086 13441787 := bstep (se 1 (by rfl) ⟨10081340, by rfl⟩ : syracuseStep 13441787 = 20162681) B20162681
theorem B5978879 : Blo 1770086 5978879 := bstep (se 1 (by rfl) ⟨4484159, by rfl⟩ : syracuseStep 5978879 = 8968319) B8968319
theorem B2988967 : Blo 1770086 2988967 := bstep (se 1 (by rfl) ⟨2241725, by rfl⟩ : syracuseStep 2988967 = 4483451) B4483451
theorem B24247511 : Blo 1770086 24247511 := bstep (se 1 (by rfl) ⟨18185633, by rfl⟩ : syracuseStep 24247511 = 36371267) B36371267
theorem B3783955 : Blo 1770086 3783955 := bstep (se 1 (by rfl) ⟨2837966, by rfl⟩ : syracuseStep 3783955 = 5675933) B5675933
theorem B2989433 : Blo 1770086 2989433 := bstep (se 2 (by rfl) ⟨1121037, by rfl⟩ : syracuseStep 2989433 = 2242075) B2242075
theorem B19152379 : Blo 1770086 19152379 := bstep (se 1 (by rfl) ⟨14364284, by rfl⟩ : syracuseStep 19152379 = 28728569) B28728569
theorem B10084121 : Blo 1770086 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B11345791 : Blo 1770086 11345791 := bstep (se 1 (by rfl) ⟨8509343, by rfl⟩ : syracuseStep 11345791 = 17018687) B17018687
theorem B2989993 : Blo 1770086 2989993 := bstep (se 2 (by rfl) ⟨1121247, by rfl⟩ : syracuseStep 2989993 = 2242495) B2242495
theorem B7561279 : Blo 1770086 7561279 := bstep (se 1 (by rfl) ⟨5670959, by rfl⟩ : syracuseStep 7561279 = 11341919) B11341919
theorem B9576539 : Blo 1770086 9576539 := bstep (se 1 (by rfl) ⟨7182404, by rfl⟩ : syracuseStep 9576539 = 14364809) B14364809
theorem B8970749 : Blo 1770086 8970749 := bstep (se 3 (by rfl) ⟨1682015, by rfl⟩ : syracuseStep 8970749 = 3364031) B3364031
theorem B8970911 : Blo 1770086 8970911 := bstep (se 1 (by rfl) ⟨6728183, by rfl⟩ : syracuseStep 8970911 = 13456367) B13456367
theorem B8512283 : Blo 1770086 8512283 := bstep (se 1 (by rfl) ⟨6384212, by rfl⟩ : syracuseStep 8512283 = 12768425) B12768425
theorem B1991551 : Blo 1770086 1991551 := bstep (se 1 (by rfl) ⟨1493663, by rfl⟩ : syracuseStep 1991551 = 2987327) B2987327
theorem B1770367 : Blo 1770086 1770367 := bstep (se 1 (by rfl) ⟨1327775, by rfl⟩ : syracuseStep 1770367 = 2655551) B2655551
theorem B1770463 : Blo 1770086 1770463 := bstep (se 1 (by rfl) ⟨1327847, by rfl⟩ : syracuseStep 1770463 = 2655695) B2655695
theorem B1770587 : Blo 1770086 1770587 := bstep (se 1 (by rfl) ⟨1327940, by rfl⟩ : syracuseStep 1770587 = 2655881) B2655881
theorem B2393183 : Blo 1770086 2393183 := bstep (se 1 (by rfl) ⟨1794887, by rfl⟩ : syracuseStep 2393183 = 3589775) B3589775
theorem B2655335 : Blo 1770086 2655335 := bstep (se 1 (by rfl) ⟨1991501, by rfl⟩ : syracuseStep 2655335 = 3983003) B3983003
theorem B20169971 : Blo 1770086 20169971 := bstep (se 1 (by rfl) ⟨15127478, by rfl⟩ : syracuseStep 20169971 = 30254957) B30254957
theorem B4039931 : Blo 1770086 4039931 := bstep (se 1 (by rfl) ⟨3029948, by rfl⟩ : syracuseStep 4039931 = 6059897) B6059897
theorem B1770815 : Blo 1770086 1770815 := bstep (se 1 (by rfl) ⟨1328111, by rfl⟩ : syracuseStep 1770815 = 2656223) B2656223
theorem B1770855 : Blo 1770086 1770855 := bstep (se 1 (by rfl) ⟨1328141, by rfl⟩ : syracuseStep 1770855 = 2656283) B2656283
theorem B38282615 : Blo 1770086 38282615 := bstep (se 1 (by rfl) ⟨28711961, by rfl⟩ : syracuseStep 38282615 = 57423923) B57423923
theorem B1770975 : Blo 1770086 1770975 := bstep (se 1 (by rfl) ⟨1328231, by rfl⟩ : syracuseStep 1770975 = 2656463) B2656463
theorem B6727151 : Blo 1770086 6727151 := bstep (se 1 (by rfl) ⟨5045363, by rfl⟩ : syracuseStep 6727151 = 10090727) B10090727
theorem B2835967 : Blo 1770086 2835967 := bstep (se 1 (by rfl) ⟨2126975, by rfl⟩ : syracuseStep 2835967 = 4253951) B4253951
theorem B10086079 : Blo 1770086 10086079 := bstep (se 1 (by rfl) ⟨7564559, by rfl⟩ : syracuseStep 10086079 = 15129119) B15129119
theorem B4482803 : Blo 1770086 4482803 := bstep (se 1 (by rfl) ⟨3362102, by rfl⟩ : syracuseStep 4482803 = 6724205) B6724205
theorem B25536505 : Blo 1770086 25536505 := bstep (se 2 (by rfl) ⟨9576189, by rfl⟩ : syracuseStep 25536505 = 19152379) B19152379
theorem B3983471 : Blo 1770086 3983471 := bstep (se 1 (by rfl) ⟨2987603, by rfl⟩ : syracuseStep 3983471 = 5975207) B5975207
theorem B16165007 : Blo 1770086 16165007 := bstep (se 1 (by rfl) ⟨12123755, by rfl⟩ : syracuseStep 16165007 = 24247511) B24247511
theorem B1992955 : Blo 1770086 1992955 := bstep (se 1 (by rfl) ⟨1494716, by rfl⟩ : syracuseStep 1992955 = 2989433) B2989433
theorem B2656895 : Blo 1770086 2656895 := bstep (se 1 (by rfl) ⟨1992671, by rfl⟩ : syracuseStep 2656895 = 3985343) B3985343
theorem B5041025 : Blo 1770086 5041025 := bstep (se 2 (by rfl) ⟨1890384, by rfl⟩ : syracuseStep 5041025 = 3780769) B3780769
theorem B8506633 : Blo 1770086 8506633 := bstep (se 2 (by rfl) ⟨3189987, by rfl⟩ : syracuseStep 8506633 = 6379975) B6379975
theorem B6721001 : Blo 1770086 6721001 := bstep (se 2 (by rfl) ⟨2520375, by rfl⟩ : syracuseStep 6721001 = 5040751) B5040751
theorem B2657897 : Blo 1770086 2657897 := bstep (se 2 (by rfl) ⟨996711, by rfl⟩ : syracuseStep 2657897 = 1993423) B1993423
theorem B5041855 : Blo 1770086 5041855 := bstep (se 1 (by rfl) ⟨3781391, by rfl⟩ : syracuseStep 5041855 = 7562783) B7562783
theorem B3985127 : Blo 1770086 3985127 := bstep (se 1 (by rfl) ⟨2988845, by rfl⟩ : syracuseStep 3985127 = 5977691) B5977691
theorem B3985289 : Blo 1770086 3985289 := bstep (se 2 (by rfl) ⟨1494483, by rfl⟩ : syracuseStep 3985289 = 2988967) B2988967
theorem B30683261 : Blo 1770086 30683261 := bstep (se 3 (by rfl) ⟨5753111, by rfl⟩ : syracuseStep 30683261 = 11506223) B11506223
theorem B8966375 : Blo 1770086 8966375 := bstep (se 1 (by rfl) ⟨6724781, by rfl⟩ : syracuseStep 8966375 = 13449563) B13449563
theorem B4485415 : Blo 1770086 4485415 := bstep (se 1 (by rfl) ⟨3364061, by rfl⟩ : syracuseStep 4485415 = 6728123) B6728123
theorem B7565723 : Blo 1770086 7565723 := bstep (se 1 (by rfl) ⟨5674292, by rfl⟩ : syracuseStep 7565723 = 11348585) B11348585
theorem B3985919 : Blo 1770086 3985919 := bstep (se 1 (by rfl) ⟨2989439, by rfl⟩ : syracuseStep 3985919 = 5978879) B5978879
theorem B5976827 : Blo 1770086 5976827 := bstep (se 1 (by rfl) ⟨4482620, by rfl⟩ : syracuseStep 5976827 = 8965241) B8965241
theorem B5976989 : Blo 1770086 5976989 := bstep (se 3 (by rfl) ⟨1120685, by rfl⟩ : syracuseStep 5976989 = 2241371) B2241371
theorem B15127721 : Blo 1770086 15127721 := bstep (se 2 (by rfl) ⟨5672895, by rfl⟩ : syracuseStep 15127721 = 11345791) B11345791
theorem B6722747 : Blo 1770086 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B3986657 : Blo 1770086 3986657 := bstep (se 2 (by rfl) ⟨1494996, by rfl⟩ : syracuseStep 3986657 = 2989993) B2989993
theorem B2241847 : Blo 1770086 2241847 := bstep (se 1 (by rfl) ⟨1681385, by rfl⟩ : syracuseStep 2241847 = 3362771) B3362771
theorem B3782143 : Blo 1770086 3782143 := bstep (se 1 (by rfl) ⟨2836607, by rfl⟩ : syracuseStep 3782143 = 5673215) B5673215
theorem B3986963 : Blo 1770086 3986963 := bstep (se 1 (by rfl) ⟨2990222, by rfl⟩ : syracuseStep 3986963 = 5980445) B5980445
theorem B14366267 : Blo 1770086 14366267 := bstep (se 1 (by rfl) ⟨10774700, by rfl⟩ : syracuseStep 14366267 = 21549401) B21549401
theorem B3987017 : Blo 1770086 3987017 := bstep (se 2 (by rfl) ⟨1495131, by rfl⟩ : syracuseStep 3987017 = 2990263) B2990263
theorem B25532009 : Blo 1770086 25532009 := bstep (se 2 (by rfl) ⟨9574503, by rfl⟩ : syracuseStep 25532009 = 19149007) B19149007
theorem B6723263 : Blo 1770086 6723263 := bstep (se 1 (by rfl) ⟨5042447, by rfl⟩ : syracuseStep 6723263 = 10084895) B10084895
theorem B2987759 : Blo 1770086 2987759 := bstep (se 1 (by rfl) ⟨2240819, by rfl⟩ : syracuseStep 2987759 = 4481639) B4481639
theorem B5978555 : Blo 1770086 5978555 := bstep (se 1 (by rfl) ⟨4483916, by rfl⟩ : syracuseStep 5978555 = 8967833) B8967833
theorem B5749373 : Blo 1770086 5749373 := bstep (se 3 (by rfl) ⟨1078007, by rfl⟩ : syracuseStep 5749373 = 2156015) B2156015
theorem B7183019 : Blo 1770086 7183019 := bstep (se 1 (by rfl) ⟨5387264, by rfl⟩ : syracuseStep 7183019 = 10774529) B10774529
theorem B2988751 : Blo 1770086 2988751 := bstep (se 1 (by rfl) ⟨2241563, by rfl⟩ : syracuseStep 2988751 = 4483127) B4483127
theorem B5044999 : Blo 1770086 5044999 := bstep (se 1 (by rfl) ⟨3783749, by rfl⟩ : syracuseStep 5044999 = 7567499) B7567499
theorem B2988839 : Blo 1770086 2988839 := bstep (se 1 (by rfl) ⟨2241629, by rfl⟩ : syracuseStep 2988839 = 4483259) B4483259
theorem B276093851 : Blo 1770086 276093851 := bstep (se 1 (by rfl) ⟨207070388, by rfl⟩ : syracuseStep 276093851 = 414140777) B414140777
theorem B5045159 : Blo 1770086 5045159 := bstep (se 1 (by rfl) ⟨3783869, by rfl⟩ : syracuseStep 5045159 = 7567739) B7567739
theorem B8969129 : Blo 1770086 8969129 := bstep (se 2 (by rfl) ⟨3363423, by rfl⟩ : syracuseStep 8969129 = 6726847) B6726847
theorem B5045273 : Blo 1770086 5045273 := bstep (se 2 (by rfl) ⟨1891977, by rfl⟩ : syracuseStep 5045273 = 3783955) B3783955
theorem B6380639 : Blo 1770086 6380639 := bstep (se 1 (by rfl) ⟨4785479, by rfl⟩ : syracuseStep 6380639 = 9570959) B9570959
theorem B8961191 : Blo 1770086 8961191 := bstep (se 1 (by rfl) ⟨6720893, by rfl⟩ : syracuseStep 8961191 = 13441787) B13441787
theorem B8961353 : Blo 1770086 8961353 := bstep (se 2 (by rfl) ⟨3360507, by rfl⟩ : syracuseStep 8961353 = 6721015) B6721015
theorem B2989615 : Blo 1770086 2989615 := bstep (se 1 (by rfl) ⟨2242211, by rfl⟩ : syracuseStep 2989615 = 4484423) B4484423
theorem B20455507 : Blo 1770086 20455507 := bstep (se 1 (by rfl) ⟨15341630, by rfl⟩ : syracuseStep 20455507 = 30683261) B30683261
theorem B6381821 : Blo 1770086 6381821 := bstep (se 3 (by rfl) ⟨1196591, by rfl⟩ : syracuseStep 6381821 = 2393183) B2393183
theorem B5980499 : Blo 1770086 5980499 := bstep (se 1 (by rfl) ⟨4485374, by rfl⟩ : syracuseStep 5980499 = 8970749) B8970749
theorem B5980553 : Blo 1770086 5980553 := bstep (se 2 (by rfl) ⟨2242707, by rfl⟩ : syracuseStep 5980553 = 4485415) B4485415
theorem B5980607 : Blo 1770086 5980607 := bstep (se 1 (by rfl) ⟨4485455, by rfl⟩ : syracuseStep 5980607 = 8970911) B8970911
theorem B1770223 : Blo 1770086 1770223 := bstep (se 1 (by rfl) ⟨1327667, by rfl⟩ : syracuseStep 1770223 = 2655335) B2655335
theorem B10085147 : Blo 1770086 10085147 := bstep (se 1 (by rfl) ⟨7563860, by rfl⟩ : syracuseStep 10085147 = 15127721) B15127721
theorem B4481831 : Blo 1770086 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B6726665 : Blo 1770086 6726665 := bstep (se 2 (by rfl) ⟨2522499, by rfl⟩ : syracuseStep 6726665 = 5044999) B5044999
theorem B9577511 : Blo 1770086 9577511 := bstep (se 1 (by rfl) ⟨7183133, by rfl⟩ : syracuseStep 9577511 = 14366267) B14366267
theorem B4482175 : Blo 1770086 4482175 := bstep (se 1 (by rfl) ⟨3361631, by rfl⟩ : syracuseStep 4482175 = 6723263) B6723263
theorem B1991839 : Blo 1770086 1991839 := bstep (se 1 (by rfl) ⟨1493879, by rfl⟩ : syracuseStep 1991839 = 2987759) B2987759
theorem B2655401 : Blo 1770086 2655401 := bstep (se 2 (by rfl) ⟨995775, by rfl⟩ : syracuseStep 2655401 = 1991551) B1991551
theorem B2655647 : Blo 1770086 2655647 := bstep (se 1 (by rfl) ⟨1991735, by rfl⟩ : syracuseStep 2655647 = 3983471) B3983471
theorem B1771263 : Blo 1770086 1771263 := bstep (se 1 (by rfl) ⟨1328447, by rfl⟩ : syracuseStep 1771263 = 2656895) B2656895
theorem B19154717 : Blo 1770086 19154717 := bstep (se 3 (by rfl) ⟨3591509, by rfl⟩ : syracuseStep 19154717 = 7183019) B7183019
theorem B1992559 : Blo 1770086 1992559 := bstep (se 1 (by rfl) ⟨1494419, by rfl⟩ : syracuseStep 1992559 = 2988839) B2988839
theorem B3360683 : Blo 1770086 3360683 := bstep (se 1 (by rfl) ⟨2520512, by rfl⟩ : syracuseStep 3360683 = 5041025) B5041025
theorem B4253759 : Blo 1770086 4253759 := bstep (se 1 (by rfl) ⟨3190319, by rfl⟩ : syracuseStep 4253759 = 6380639) B6380639
theorem B5974127 : Blo 1770086 5974127 := bstep (se 1 (by rfl) ⟨4480595, by rfl⟩ : syracuseStep 5974127 = 8961191) B8961191
theorem B5974235 : Blo 1770086 5974235 := bstep (se 1 (by rfl) ⟨4480676, by rfl⟩ : syracuseStep 5974235 = 8961353) B8961353
theorem B1771931 : Blo 1770086 1771931 := bstep (se 1 (by rfl) ⟨1328948, by rfl⟩ : syracuseStep 1771931 = 2657897) B2657897
theorem B736250269 : Blo 1770086 736250269 := bstep (se 3 (by rfl) ⟨138046925, by rfl⟩ : syracuseStep 736250269 = 276093851) B276093851
theorem B2656751 : Blo 1770086 2656751 := bstep (se 1 (by rfl) ⟨1992563, by rfl⟩ : syracuseStep 2656751 = 3985127) B3985127
theorem B2656859 : Blo 1770086 2656859 := bstep (se 1 (by rfl) ⟨1992644, by rfl⟩ : syracuseStep 2656859 = 3985289) B3985289
theorem B34048673 : Blo 1770086 34048673 := bstep (se 2 (by rfl) ⟨12768252, by rfl⟩ : syracuseStep 34048673 = 25536505) B25536505
theorem B20171429 : Blo 1770086 20171429 := bstep (se 4 (by rfl) ⟨1891071, by rfl⟩ : syracuseStep 20171429 = 3782143) B3782143
theorem B6384359 : Blo 1770086 6384359 := bstep (se 1 (by rfl) ⟨4788269, by rfl⟩ : syracuseStep 6384359 = 9576539) B9576539
theorem B2657273 : Blo 1770086 2657273 := bstep (se 2 (by rfl) ⟨996477, by rfl⟩ : syracuseStep 2657273 = 1992955) B1992955
theorem B2657279 : Blo 1770086 2657279 := bstep (se 1 (by rfl) ⟨1992959, by rfl⟩ : syracuseStep 2657279 = 3985919) B3985919
theorem B3984551 : Blo 1770086 3984551 := bstep (se 1 (by rfl) ⟨2988413, by rfl⟩ : syracuseStep 3984551 = 5976827) B5976827
theorem B3984659 : Blo 1770086 3984659 := bstep (se 1 (by rfl) ⟨2988494, by rfl⟩ : syracuseStep 3984659 = 5976989) B5976989
theorem B2657771 : Blo 1770086 2657771 := bstep (se 1 (by rfl) ⟨1993328, by rfl⟩ : syracuseStep 2657771 = 3986657) B3986657
theorem B13446647 : Blo 1770086 13446647 := bstep (se 1 (by rfl) ⟨10084985, by rfl⟩ : syracuseStep 13446647 = 20169971) B20169971
theorem B25521743 : Blo 1770086 25521743 := bstep (se 1 (by rfl) ⟨19141307, by rfl⟩ : syracuseStep 25521743 = 38282615) B38282615
theorem B3985001 : Blo 1770086 3985001 := bstep (se 2 (by rfl) ⟨1494375, by rfl⟩ : syracuseStep 3985001 = 2988751) B2988751
theorem B4484767 : Blo 1770086 4484767 := bstep (se 1 (by rfl) ⟨3363575, by rfl⟩ : syracuseStep 4484767 = 6727151) B6727151
theorem B2657975 : Blo 1770086 2657975 := bstep (se 1 (by rfl) ⟨1993481, by rfl⟩ : syracuseStep 2657975 = 3986963) B3986963
theorem B2658011 : Blo 1770086 2658011 := bstep (se 1 (by rfl) ⟨1993508, by rfl⟩ : syracuseStep 2658011 = 3987017) B3987017
theorem B10776671 : Blo 1770086 10776671 := bstep (se 1 (by rfl) ⟨8082503, by rfl⟩ : syracuseStep 10776671 = 16165007) B16165007
theorem B3985703 : Blo 1770086 3985703 := bstep (se 1 (by rfl) ⟨2989277, by rfl⟩ : syracuseStep 3985703 = 5978555) B5978555
theorem B11342177 : Blo 1770086 11342177 := bstep (se 2 (by rfl) ⟨4253316, by rfl⟩ : syracuseStep 11342177 = 8506633) B8506633
theorem B3363439 : Blo 1770086 3363439 := bstep (se 1 (by rfl) ⟨2522579, by rfl⟩ : syracuseStep 3363439 = 5045159) B5045159
theorem B3781289 : Blo 1770086 3781289 := bstep (se 2 (by rfl) ⟨1417983, by rfl⟩ : syracuseStep 3781289 = 2835967) B2835967
theorem B3363515 : Blo 1770086 3363515 := bstep (se 1 (by rfl) ⟨2522636, by rfl⟩ : syracuseStep 3363515 = 5045273) B5045273
theorem B3986153 : Blo 1770086 3986153 := bstep (se 2 (by rfl) ⟨1494807, by rfl⟩ : syracuseStep 3986153 = 2989615) B2989615
theorem B6722473 : Blo 1770086 6722473 := bstep (se 2 (by rfl) ⟨2520927, by rfl⟩ : syracuseStep 6722473 = 5041855) B5041855
theorem B13448105 : Blo 1770086 13448105 := bstep (se 2 (by rfl) ⟨5043039, by rfl⟩ : syracuseStep 13448105 = 10086079) B10086079
theorem B10081705 : Blo 1770086 10081705 := bstep (se 2 (by rfl) ⟨3780639, by rfl⟩ : syracuseStep 10081705 = 7561279) B7561279
theorem B5977583 : Blo 1770086 5977583 := bstep (se 1 (by rfl) ⟨4483187, by rfl⟩ : syracuseStep 5977583 = 8966375) B8966375
theorem B5043815 : Blo 1770086 5043815 := bstep (se 1 (by rfl) ⟨3782861, by rfl⟩ : syracuseStep 5043815 = 7565723) B7565723
theorem B5674855 : Blo 1770086 5674855 := bstep (se 1 (by rfl) ⟨4256141, by rfl⟩ : syracuseStep 5674855 = 8512283) B8512283
theorem B2693287 : Blo 1770086 2693287 := bstep (se 1 (by rfl) ⟨2019965, by rfl⟩ : syracuseStep 2693287 = 4039931) B4039931
theorem B17021339 : Blo 1770086 17021339 := bstep (se 1 (by rfl) ⟨12766004, by rfl⟩ : syracuseStep 17021339 = 25532009) B25532009
theorem B2988535 : Blo 1770086 2988535 := bstep (se 1 (by rfl) ⟨2241401, by rfl⟩ : syracuseStep 2988535 = 4482803) B4482803
theorem B2989129 : Blo 1770086 2989129 := bstep (se 2 (by rfl) ⟨1120923, by rfl⟩ : syracuseStep 2989129 = 2241847) B2241847
theorem B3832915 : Blo 1770086 3832915 := bstep (se 1 (by rfl) ⟨2874686, by rfl⟩ : syracuseStep 3832915 = 5749373) B5749373
theorem B5979419 : Blo 1770086 5979419 := bstep (se 1 (by rfl) ⟨4484564, by rfl⟩ : syracuseStep 5979419 = 8969129) B8969129
theorem B4480667 : Blo 1770086 4480667 := bstep (se 1 (by rfl) ⟨3360500, by rfl⟩ : syracuseStep 4480667 = 6721001) B6721001
theorem B7184447 : Blo 1770086 7184447 := bstep (se 1 (by rfl) ⟨5388335, by rfl⟩ : syracuseStep 7184447 = 10776671) B10776671
theorem B7561451 : Blo 1770086 7561451 := bstep (se 1 (by rfl) ⟨5671088, by rfl⟩ : syracuseStep 7561451 = 11342177) B11342177
theorem B1770267 : Blo 1770086 1770267 := bstep (se 1 (by rfl) ⟨1327700, by rfl⟩ : syracuseStep 1770267 = 2655401) B2655401
theorem B1770431 : Blo 1770086 1770431 := bstep (se 1 (by rfl) ⟨1327823, by rfl⟩ : syracuseStep 1770431 = 2655647) B2655647
theorem B8963297 : Blo 1770086 8963297 := bstep (se 2 (by rfl) ⟨3361236, by rfl⟩ : syracuseStep 8963297 = 6722473) B6722473
theorem B2835839 : Blo 1770086 2835839 := bstep (se 1 (by rfl) ⟨2126879, by rfl⟩ : syracuseStep 2835839 = 4253759) B4253759
theorem B3982751 : Blo 1770086 3982751 := bstep (se 1 (by rfl) ⟨2987063, by rfl⟩ : syracuseStep 3982751 = 5974127) B5974127
theorem B3982823 : Blo 1770086 3982823 := bstep (se 1 (by rfl) ⟨2987117, by rfl⟩ : syracuseStep 3982823 = 5974235) B5974235
theorem B2655785 : Blo 1770086 2655785 := bstep (se 2 (by rfl) ⟨995919, by rfl⟩ : syracuseStep 2655785 = 1991839) B1991839
theorem B11347559 : Blo 1770086 11347559 := bstep (se 1 (by rfl) ⟨8510669, by rfl⟩ : syracuseStep 11347559 = 17021339) B17021339
theorem B1771167 : Blo 1770086 1771167 := bstep (se 1 (by rfl) ⟨1328375, by rfl⟩ : syracuseStep 1771167 = 2656751) B2656751
theorem B1771239 : Blo 1770086 1771239 := bstep (se 1 (by rfl) ⟨1328429, by rfl⟩ : syracuseStep 1771239 = 2656859) B2656859
theorem B1771515 : Blo 1770086 1771515 := bstep (se 1 (by rfl) ⟨1328636, by rfl⟩ : syracuseStep 1771515 = 2657273) B2657273
theorem B1771519 : Blo 1770086 1771519 := bstep (se 1 (by rfl) ⟨1328639, by rfl⟩ : syracuseStep 1771519 = 2657279) B2657279
theorem B2656367 : Blo 1770086 2656367 := bstep (se 1 (by rfl) ⟨1992275, by rfl⟩ : syracuseStep 2656367 = 3984551) B3984551
theorem B2656439 : Blo 1770086 2656439 := bstep (se 1 (by rfl) ⟨1992329, by rfl⟩ : syracuseStep 2656439 = 3984659) B3984659
theorem B1771847 : Blo 1770086 1771847 := bstep (se 1 (by rfl) ⟨1328885, by rfl⟩ : syracuseStep 1771847 = 2657771) B2657771
theorem B8964431 : Blo 1770086 8964431 := bstep (se 1 (by rfl) ⟨6723323, by rfl⟩ : syracuseStep 8964431 = 13446647) B13446647
theorem B2656667 : Blo 1770086 2656667 := bstep (se 1 (by rfl) ⟨1992500, by rfl⟩ : syracuseStep 2656667 = 3985001) B3985001
theorem B1771983 : Blo 1770086 1771983 := bstep (se 1 (by rfl) ⟨1328987, by rfl⟩ : syracuseStep 1771983 = 2657975) B2657975
theorem B1772007 : Blo 1770086 1772007 := bstep (se 1 (by rfl) ⟨1329005, by rfl⟩ : syracuseStep 1772007 = 2658011) B2658011
theorem B2656745 : Blo 1770086 2656745 := bstep (se 2 (by rfl) ⟨996279, by rfl⟩ : syracuseStep 2656745 = 1992559) B1992559
theorem B27274009 : Blo 1770086 27274009 := bstep (se 2 (by rfl) ⟨10227753, by rfl⟩ : syracuseStep 27274009 = 20455507) B20455507
theorem B4254547 : Blo 1770086 4254547 := bstep (se 1 (by rfl) ⟨3190910, by rfl⟩ : syracuseStep 4254547 = 6381821) B6381821
theorem B2657135 : Blo 1770086 2657135 := bstep (se 1 (by rfl) ⟨1992851, by rfl⟩ : syracuseStep 2657135 = 3985703) B3985703
theorem B3591049 : Blo 1770086 3591049 := bstep (se 2 (by rfl) ⟨1346643, by rfl⟩ : syracuseStep 3591049 = 2693287) B2693287
theorem B2657435 : Blo 1770086 2657435 := bstep (se 1 (by rfl) ⟨1993076, by rfl⟩ : syracuseStep 2657435 = 3986153) B3986153
theorem B981667025 : Blo 1770086 981667025 := bstep (se 2 (by rfl) ⟨368125134, by rfl⟩ : syracuseStep 981667025 = 736250269) B736250269
theorem B8965403 : Blo 1770086 8965403 := bstep (se 1 (by rfl) ⟨6724052, by rfl⟩ : syracuseStep 8965403 = 13448105) B13448105
theorem B3984713 : Blo 1770086 3984713 := bstep (se 2 (by rfl) ⟨1494267, by rfl⟩ : syracuseStep 3984713 = 2988535) B2988535
theorem B4484443 : Blo 1770086 4484443 := bstep (se 1 (by rfl) ⟨3363332, by rfl⟩ : syracuseStep 4484443 = 6726665) B6726665
theorem B6385007 : Blo 1770086 6385007 := bstep (se 1 (by rfl) ⟨4788755, by rfl⟩ : syracuseStep 6385007 = 9577511) B9577511
theorem B4484585 : Blo 1770086 4484585 := bstep (se 2 (by rfl) ⟨1681719, by rfl⟩ : syracuseStep 4484585 = 3363439) B3363439
theorem B3985055 : Blo 1770086 3985055 := bstep (se 1 (by rfl) ⟨2988791, by rfl⟩ : syracuseStep 3985055 = 5977583) B5977583
theorem B3362543 : Blo 1770086 3362543 := bstep (se 1 (by rfl) ⟨2521907, by rfl⟩ : syracuseStep 3362543 = 5043815) B5043815
theorem B2240455 : Blo 1770086 2240455 := bstep (se 1 (by rfl) ⟨1680341, by rfl⟩ : syracuseStep 2240455 = 3360683) B3360683
theorem B3985505 : Blo 1770086 3985505 := bstep (se 2 (by rfl) ⟨1494564, by rfl⟩ : syracuseStep 3985505 = 2989129) B2989129
theorem B5976233 : Blo 1770086 5976233 := bstep (se 2 (by rfl) ⟨2241087, by rfl⟩ : syracuseStep 5976233 = 4482175) B4482175
theorem B13447619 : Blo 1770086 13447619 := bstep (se 1 (by rfl) ⟨10085714, by rfl⟩ : syracuseStep 13447619 = 20171429) B20171429
theorem B4256239 : Blo 1770086 4256239 := bstep (se 1 (by rfl) ⟨3192179, by rfl⟩ : syracuseStep 4256239 = 6384359) B6384359
theorem B3986279 : Blo 1770086 3986279 := bstep (se 1 (by rfl) ⟨2989709, by rfl⟩ : syracuseStep 3986279 = 5979419) B5979419
theorem B2987111 : Blo 1770086 2987111 := bstep (se 1 (by rfl) ⟨2240333, by rfl⟩ : syracuseStep 2987111 = 4480667) B4480667
theorem B7566473 : Blo 1770086 7566473 := bstep (se 2 (by rfl) ⟨2837427, by rfl⟩ : syracuseStep 7566473 = 5674855) B5674855
theorem B3986999 : Blo 1770086 3986999 := bstep (se 1 (by rfl) ⟨2990249, by rfl⟩ : syracuseStep 3986999 = 5980499) B5980499
theorem B3987035 : Blo 1770086 3987035 := bstep (se 1 (by rfl) ⟨2990276, by rfl⟩ : syracuseStep 3987035 = 5980553) B5980553
theorem B3987071 : Blo 1770086 3987071 := bstep (se 1 (by rfl) ⟨2990303, by rfl⟩ : syracuseStep 3987071 = 5980607) B5980607
theorem B2242343 : Blo 1770086 2242343 := bstep (se 1 (by rfl) ⟨1681757, by rfl⟩ : syracuseStep 2242343 = 3363515) B3363515
theorem B6723431 : Blo 1770086 6723431 := bstep (se 1 (by rfl) ⟨5042573, by rfl⟩ : syracuseStep 6723431 = 10085147) B10085147
theorem B2987887 : Blo 1770086 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B12769811 : Blo 1770086 12769811 := bstep (se 1 (by rfl) ⟨9577358, by rfl⟩ : syracuseStep 12769811 = 19154717) B19154717
theorem B5110553 : Blo 1770086 5110553 := bstep (se 2 (by rfl) ⟨1916457, by rfl⟩ : syracuseStep 5110553 = 3832915) B3832915
theorem B22699115 : Blo 1770086 22699115 := bstep (se 1 (by rfl) ⟨17024336, by rfl⟩ : syracuseStep 22699115 = 34048673) B34048673
theorem B10083437 : Blo 1770086 10083437 := bstep (se 3 (by rfl) ⟨1890644, by rfl⟩ : syracuseStep 10083437 = 3781289) B3781289
theorem B13442273 : Blo 1770086 13442273 := bstep (se 2 (by rfl) ⟨5040852, by rfl⟩ : syracuseStep 13442273 = 10081705) B10081705
theorem B5979689 : Blo 1770086 5979689 := bstep (se 2 (by rfl) ⟨2242383, by rfl⟩ : syracuseStep 5979689 = 4484767) B4484767
theorem B17014495 : Blo 1770086 17014495 := bstep (se 1 (by rfl) ⟨12760871, by rfl⟩ : syracuseStep 17014495 = 25521743) B25521743
theorem B20177261 : Blo 1770086 20177261 := bstep (se 3 (by rfl) ⟨3783236, by rfl⟩ : syracuseStep 20177261 = 7566473) B7566473
theorem B1991407 : Blo 1770086 1991407 := bstep (se 1 (by rfl) ⟨1493555, by rfl⟩ : syracuseStep 1991407 = 2987111) B2987111
theorem B2655167 : Blo 1770086 2655167 := bstep (se 1 (by rfl) ⟨1991375, by rfl⟩ : syracuseStep 2655167 = 3982751) B3982751
theorem B2655215 : Blo 1770086 2655215 := bstep (se 1 (by rfl) ⟨1991411, by rfl⟩ : syracuseStep 2655215 = 3982823) B3982823
theorem B1770523 : Blo 1770086 1770523 := bstep (se 1 (by rfl) ⟨1327892, by rfl⟩ : syracuseStep 1770523 = 2655785) B2655785
theorem B36365345 : Blo 1770086 36365345 := bstep (se 2 (by rfl) ⟨13637004, by rfl⟩ : syracuseStep 36365345 = 27274009) B27274009
theorem B4482287 : Blo 1770086 4482287 := bstep (se 1 (by rfl) ⟨3361715, by rfl⟩ : syracuseStep 4482287 = 6723431) B6723431
theorem B1770911 : Blo 1770086 1770911 := bstep (se 1 (by rfl) ⟨1328183, by rfl⟩ : syracuseStep 1770911 = 2656367) B2656367
theorem B1770959 : Blo 1770086 1770959 := bstep (se 1 (by rfl) ⟨1328219, by rfl⟩ : syracuseStep 1770959 = 2656439) B2656439
theorem B1771111 : Blo 1770086 1771111 := bstep (se 1 (by rfl) ⟨1328333, by rfl⟩ : syracuseStep 1771111 = 2656667) B2656667
theorem B1771163 : Blo 1770086 1771163 := bstep (se 1 (by rfl) ⟨1328372, by rfl⟩ : syracuseStep 1771163 = 2656745) B2656745
theorem B8513207 : Blo 1770086 8513207 := bstep (se 1 (by rfl) ⟨6384905, by rfl⟩ : syracuseStep 8513207 = 12769811) B12769811
theorem B1771423 : Blo 1770086 1771423 := bstep (se 1 (by rfl) ⟨1328567, by rfl⟩ : syracuseStep 1771423 = 2657135) B2657135
theorem B15132743 : Blo 1770086 15132743 := bstep (se 1 (by rfl) ⟨11349557, by rfl⟩ : syracuseStep 15132743 = 22699115) B22699115
theorem B1771623 : Blo 1770086 1771623 := bstep (se 1 (by rfl) ⟨1328717, by rfl⟩ : syracuseStep 1771623 = 2657435) B2657435
theorem B654444683 : Blo 1770086 654444683 := bstep (se 1 (by rfl) ⟨490833512, by rfl⟩ : syracuseStep 654444683 = 981667025) B981667025
theorem B2656475 : Blo 1770086 2656475 := bstep (se 1 (by rfl) ⟨1992356, by rfl⟩ : syracuseStep 2656475 = 3984713) B3984713
theorem B22685993 : Blo 1770086 22685993 := bstep (se 2 (by rfl) ⟨8507247, by rfl⟩ : syracuseStep 22685993 = 17014495) B17014495
theorem B2656703 : Blo 1770086 2656703 := bstep (se 1 (by rfl) ⟨1992527, by rfl⟩ : syracuseStep 2656703 = 3985055) B3985055
theorem B3983849 : Blo 1770086 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B2657003 : Blo 1770086 2657003 := bstep (se 1 (by rfl) ⟨1992752, by rfl⟩ : syracuseStep 2657003 = 3985505) B3985505
theorem B3984155 : Blo 1770086 3984155 := bstep (se 1 (by rfl) ⟨2988116, by rfl⟩ : syracuseStep 3984155 = 5976233) B5976233
theorem B5040967 : Blo 1770086 5040967 := bstep (se 1 (by rfl) ⟨3780725, by rfl⟩ : syracuseStep 5040967 = 7561451) B7561451
theorem B8965079 : Blo 1770086 8965079 := bstep (se 1 (by rfl) ⟨6723809, by rfl⟩ : syracuseStep 8965079 = 13447619) B13447619
theorem B2657519 : Blo 1770086 2657519 := bstep (se 1 (by rfl) ⟨1993139, by rfl⟩ : syracuseStep 2657519 = 3986279) B3986279
theorem B5975531 : Blo 1770086 5975531 := bstep (se 1 (by rfl) ⟨4481648, by rfl⟩ : syracuseStep 5975531 = 8963297) B8963297
theorem B17026685 : Blo 1770086 17026685 := bstep (se 3 (by rfl) ⟨3192503, by rfl⟩ : syracuseStep 17026685 = 6385007) B6385007
theorem B2657999 : Blo 1770086 2657999 := bstep (se 1 (by rfl) ⟨1993499, by rfl⟩ : syracuseStep 2657999 = 3986999) B3986999
theorem B2658023 : Blo 1770086 2658023 := bstep (se 1 (by rfl) ⟨1993517, by rfl⟩ : syracuseStep 2658023 = 3987035) B3987035
theorem B7565039 : Blo 1770086 7565039 := bstep (se 1 (by rfl) ⟨5673779, by rfl⟩ : syracuseStep 7565039 = 11347559) B11347559
theorem B2658047 : Blo 1770086 2658047 := bstep (se 1 (by rfl) ⟨1993535, by rfl⟩ : syracuseStep 2658047 = 3987071) B3987071
theorem B5672729 : Blo 1770086 5672729 := bstep (se 2 (by rfl) ⟨2127273, by rfl⟩ : syracuseStep 5672729 = 4254547) B4254547
theorem B4788065 : Blo 1770086 4788065 := bstep (se 2 (by rfl) ⟨1795524, by rfl⟩ : syracuseStep 4788065 = 3591049) B3591049
theorem B5976287 : Blo 1770086 5976287 := bstep (se 1 (by rfl) ⟨4482215, by rfl⟩ : syracuseStep 5976287 = 8964431) B8964431
theorem B6722291 : Blo 1770086 6722291 := bstep (se 1 (by rfl) ⟨5041718, by rfl⟩ : syracuseStep 6722291 = 10083437) B10083437
theorem B5976935 : Blo 1770086 5976935 := bstep (se 1 (by rfl) ⟨4482701, by rfl⟩ : syracuseStep 5976935 = 8965403) B8965403
theorem B3986459 : Blo 1770086 3986459 := bstep (se 1 (by rfl) ⟨2989844, by rfl⟩ : syracuseStep 3986459 = 5979689) B5979689
theorem B2241695 : Blo 1770086 2241695 := bstep (se 1 (by rfl) ⟨1681271, by rfl⟩ : syracuseStep 2241695 = 3362543) B3362543
theorem B2987273 : Blo 1770086 2987273 := bstep (se 2 (by rfl) ⟨1120227, by rfl⟩ : syracuseStep 2987273 = 2240455) B2240455
theorem B4789631 : Blo 1770086 4789631 := bstep (se 1 (by rfl) ⟨3592223, by rfl⟩ : syracuseStep 4789631 = 7184447) B7184447
theorem B5674985 : Blo 1770086 5674985 := bstep (se 2 (by rfl) ⟨2128119, by rfl⟩ : syracuseStep 5674985 = 4256239) B4256239
theorem B1890559 : Blo 1770086 1890559 := bstep (se 1 (by rfl) ⟨1417919, by rfl⟩ : syracuseStep 1890559 = 2835839) B2835839
theorem B5979257 : Blo 1770086 5979257 := bstep (se 2 (by rfl) ⟨2242221, by rfl⟩ : syracuseStep 5979257 = 4484443) B4484443
theorem B3407035 : Blo 1770086 3407035 := bstep (se 1 (by rfl) ⟨2555276, by rfl⟩ : syracuseStep 3407035 = 5110553) B5110553
theorem B5979581 : Blo 1770086 5979581 := bstep (se 3 (by rfl) ⟨1121171, by rfl⟩ : syracuseStep 5979581 = 2242343) B2242343
theorem B8961515 : Blo 1770086 8961515 := bstep (se 1 (by rfl) ⟨6721136, by rfl⟩ : syracuseStep 8961515 = 13442273) B13442273
theorem B2989723 : Blo 1770086 2989723 := bstep (se 1 (by rfl) ⟨2242292, by rfl⟩ : syracuseStep 2989723 = 4484585) B4484585
theorem B13451507 : Blo 1770086 13451507 := bstep (se 1 (by rfl) ⟨10088630, by rfl⟩ : syracuseStep 13451507 = 20177261) B20177261
theorem B4481527 : Blo 1770086 4481527 := bstep (se 1 (by rfl) ⟨3361145, by rfl⟩ : syracuseStep 4481527 = 6722291) B6722291
theorem B1770111 : Blo 1770086 1770111 := bstep (se 1 (by rfl) ⟨1327583, by rfl⟩ : syracuseStep 1770111 = 2655167) B2655167
theorem B1770143 : Blo 1770086 1770143 := bstep (se 1 (by rfl) ⟨1327607, by rfl⟩ : syracuseStep 1770143 = 2655215) B2655215
theorem B1991515 : Blo 1770086 1991515 := bstep (se 1 (by rfl) ⟨1493636, by rfl⟩ : syracuseStep 1991515 = 2987273) B2987273
theorem B2655209 : Blo 1770086 2655209 := bstep (se 2 (by rfl) ⟨995703, by rfl⟩ : syracuseStep 2655209 = 1991407) B1991407
theorem B1770983 : Blo 1770086 1770983 := bstep (se 1 (by rfl) ⟨1328237, by rfl⟩ : syracuseStep 1770983 = 2656475) B2656475
theorem B15123995 : Blo 1770086 15123995 := bstep (se 1 (by rfl) ⟨11342996, by rfl⟩ : syracuseStep 15123995 = 22685993) B22685993
theorem B1771135 : Blo 1770086 1771135 := bstep (se 1 (by rfl) ⟨1328351, by rfl⟩ : syracuseStep 1771135 = 2656703) B2656703
theorem B2655899 : Blo 1770086 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B1771335 : Blo 1770086 1771335 := bstep (se 1 (by rfl) ⟨1328501, by rfl⟩ : syracuseStep 1771335 = 2657003) B2657003
theorem B2656103 : Blo 1770086 2656103 := bstep (se 1 (by rfl) ⟨1992077, by rfl⟩ : syracuseStep 2656103 = 3984155) B3984155
theorem B1771679 : Blo 1770086 1771679 := bstep (se 1 (by rfl) ⟨1328759, by rfl⟩ : syracuseStep 1771679 = 2657519) B2657519
theorem B5974343 : Blo 1770086 5974343 := bstep (se 1 (by rfl) ⟨4480757, by rfl⟩ : syracuseStep 5974343 = 8961515) B8961515
theorem B3983687 : Blo 1770086 3983687 := bstep (se 1 (by rfl) ⟨2987765, by rfl⟩ : syracuseStep 3983687 = 5975531) B5975531
theorem B1771999 : Blo 1770086 1771999 := bstep (se 1 (by rfl) ⟨1328999, by rfl⟩ : syracuseStep 1771999 = 2657999) B2657999
theorem B1772015 : Blo 1770086 1772015 := bstep (se 1 (by rfl) ⟨1329011, by rfl⟩ : syracuseStep 1772015 = 2658023) B2658023
theorem B1772031 : Blo 1770086 1772031 := bstep (se 1 (by rfl) ⟨1329023, by rfl⟩ : syracuseStep 1772031 = 2658047) B2658047
theorem B3984191 : Blo 1770086 3984191 := bstep (se 1 (by rfl) ⟨2988143, by rfl⟩ : syracuseStep 3984191 = 5976287) B5976287
theorem B3984623 : Blo 1770086 3984623 := bstep (se 1 (by rfl) ⟨2988467, by rfl⟩ : syracuseStep 3984623 = 5976935) B5976935
theorem B2657639 : Blo 1770086 2657639 := bstep (se 1 (by rfl) ⟨1993229, by rfl⟩ : syracuseStep 2657639 = 3986459) B3986459
theorem B24243563 : Blo 1770086 24243563 := bstep (se 1 (by rfl) ⟨18182672, by rfl⟩ : syracuseStep 24243563 = 36365345) B36365345
theorem B6721289 : Blo 1770086 6721289 := bstep (se 2 (by rfl) ⟨2520483, by rfl⟩ : syracuseStep 6721289 = 5040967) B5040967
theorem B10088495 : Blo 1770086 10088495 := bstep (se 1 (by rfl) ⟨7566371, by rfl⟩ : syracuseStep 10088495 = 15132743) B15132743
theorem B4542713 : Blo 1770086 4542713 := bstep (se 2 (by rfl) ⟨1703517, by rfl⟩ : syracuseStep 4542713 = 3407035) B3407035
theorem B5976719 : Blo 1770086 5976719 := bstep (se 1 (by rfl) ⟨4482539, by rfl⟩ : syracuseStep 5976719 = 8965079) B8965079
theorem B3986171 : Blo 1770086 3986171 := bstep (se 1 (by rfl) ⟨2989628, by rfl⟩ : syracuseStep 3986171 = 5979257) B5979257
theorem B3986297 : Blo 1770086 3986297 := bstep (se 2 (by rfl) ⟨1494861, by rfl⟩ : syracuseStep 3986297 = 2989723) B2989723
theorem B3986387 : Blo 1770086 3986387 := bstep (se 1 (by rfl) ⟨2989790, by rfl⟩ : syracuseStep 3986387 = 5979581) B5979581
theorem B11351123 : Blo 1770086 11351123 := bstep (se 1 (by rfl) ⟨8513342, by rfl⟩ : syracuseStep 11351123 = 17026685) B17026685
theorem B5043359 : Blo 1770086 5043359 := bstep (se 1 (by rfl) ⟨3782519, by rfl⟩ : syracuseStep 5043359 = 7565039) B7565039
theorem B3781819 : Blo 1770086 3781819 := bstep (se 1 (by rfl) ⟨2836364, by rfl⟩ : syracuseStep 3781819 = 5672729) B5672729
theorem B3192043 : Blo 1770086 3192043 := bstep (se 1 (by rfl) ⟨2394032, by rfl⟩ : syracuseStep 3192043 = 4788065) B4788065
theorem B5977853 : Blo 1770086 5977853 := bstep (se 3 (by rfl) ⟨1120847, by rfl⟩ : syracuseStep 5977853 = 2241695) B2241695
theorem B2988191 : Blo 1770086 2988191 := bstep (se 1 (by rfl) ⟨2241143, by rfl⟩ : syracuseStep 2988191 = 4482287) B4482287
theorem B3193087 : Blo 1770086 3193087 := bstep (se 1 (by rfl) ⟨2394815, by rfl⟩ : syracuseStep 3193087 = 4789631) B4789631
theorem B5675471 : Blo 1770086 5675471 := bstep (se 1 (by rfl) ⟨4256603, by rfl⟩ : syracuseStep 5675471 = 8513207) B8513207
theorem B3783323 : Blo 1770086 3783323 := bstep (se 1 (by rfl) ⟨2837492, by rfl⟩ : syracuseStep 3783323 = 5674985) B5674985
theorem B10082981 : Blo 1770086 10082981 := bstep (se 4 (by rfl) ⟨945279, by rfl⟩ : syracuseStep 10082981 = 1890559) B1890559
theorem B436296455 : Blo 1770086 436296455 := bstep (se 1 (by rfl) ⟨327222341, by rfl⟩ : syracuseStep 436296455 = 654444683) B654444683
theorem B6725663 : Blo 1770086 6725663 := bstep (se 1 (by rfl) ⟨5044247, by rfl⟩ : syracuseStep 6725663 = 10088495) B10088495
theorem B1770139 : Blo 1770086 1770139 := bstep (se 1 (by rfl) ⟨1327604, by rfl⟩ : syracuseStep 1770139 = 2655209) B2655209
theorem B1770599 : Blo 1770086 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B2655353 : Blo 1770086 2655353 := bstep (se 2 (by rfl) ⟨995757, by rfl⟩ : syracuseStep 2655353 = 1991515) B1991515
theorem B1770735 : Blo 1770086 1770735 := bstep (se 1 (by rfl) ⟨1328051, by rfl⟩ : syracuseStep 1770735 = 2656103) B2656103
theorem B1992127 : Blo 1770086 1992127 := bstep (se 1 (by rfl) ⟨1494095, by rfl⟩ : syracuseStep 1992127 = 2988191) B2988191
theorem B3982895 : Blo 1770086 3982895 := bstep (se 1 (by rfl) ⟨2987171, by rfl⟩ : syracuseStep 3982895 = 5974343) B5974343
theorem B2655791 : Blo 1770086 2655791 := bstep (se 1 (by rfl) ⟨1991843, by rfl⟩ : syracuseStep 2655791 = 3983687) B3983687
theorem B2656127 : Blo 1770086 2656127 := bstep (se 1 (by rfl) ⟨1992095, by rfl⟩ : syracuseStep 2656127 = 3984191) B3984191
theorem B2656415 : Blo 1770086 2656415 := bstep (se 1 (by rfl) ⟨1992311, by rfl⟩ : syracuseStep 2656415 = 3984623) B3984623
theorem B1771759 : Blo 1770086 1771759 := bstep (se 1 (by rfl) ⟨1328819, by rfl⟩ : syracuseStep 1771759 = 2657639) B2657639
theorem B3984479 : Blo 1770086 3984479 := bstep (se 1 (by rfl) ⟨2988359, by rfl⟩ : syracuseStep 3984479 = 5976719) B5976719
theorem B2657447 : Blo 1770086 2657447 := bstep (se 1 (by rfl) ⟨1993085, by rfl⟩ : syracuseStep 2657447 = 3986171) B3986171
theorem B2657531 : Blo 1770086 2657531 := bstep (se 1 (by rfl) ⟨1993148, by rfl⟩ : syracuseStep 2657531 = 3986297) B3986297
theorem B2657591 : Blo 1770086 2657591 := bstep (se 1 (by rfl) ⟨1993193, by rfl⟩ : syracuseStep 2657591 = 3986387) B3986387
theorem B5975369 : Blo 1770086 5975369 := bstep (se 2 (by rfl) ⟨2240763, by rfl⟩ : syracuseStep 5975369 = 4481527) B4481527
theorem B3362239 : Blo 1770086 3362239 := bstep (se 1 (by rfl) ⟨2521679, by rfl⟩ : syracuseStep 3362239 = 5043359) B5043359
theorem B3985235 : Blo 1770086 3985235 := bstep (se 1 (by rfl) ⟨2988926, by rfl⟩ : syracuseStep 3985235 = 5977853) B5977853
theorem B5042425 : Blo 1770086 5042425 := bstep (se 2 (by rfl) ⟨1890909, by rfl⟩ : syracuseStep 5042425 = 3781819) B3781819
theorem B4256057 : Blo 1770086 4256057 := bstep (se 2 (by rfl) ⟨1596021, by rfl⟩ : syracuseStep 4256057 = 3192043) B3192043
theorem B6721987 : Blo 1770086 6721987 := bstep (se 1 (by rfl) ⟨5041490, by rfl⟩ : syracuseStep 6721987 = 10082981) B10082981
theorem B8967671 : Blo 1770086 8967671 := bstep (se 1 (by rfl) ⟨6725753, by rfl⟩ : syracuseStep 8967671 = 13451507) B13451507
theorem B3028475 : Blo 1770086 3028475 := bstep (se 1 (by rfl) ⟨2271356, by rfl⟩ : syracuseStep 3028475 = 4542713) B4542713
theorem B4257449 : Blo 1770086 4257449 := bstep (se 2 (by rfl) ⟨1596543, by rfl⟩ : syracuseStep 4257449 = 3193087) B3193087
theorem B7567415 : Blo 1770086 7567415 := bstep (se 1 (by rfl) ⟨5675561, by rfl⟩ : syracuseStep 7567415 = 11351123) B11351123
theorem B10082663 : Blo 1770086 10082663 := bstep (se 1 (by rfl) ⟨7561997, by rfl⟩ : syracuseStep 10082663 = 15123995) B15123995
theorem B3783647 : Blo 1770086 3783647 := bstep (se 1 (by rfl) ⟨2837735, by rfl⟩ : syracuseStep 3783647 = 5675471) B5675471
theorem B2522215 : Blo 1770086 2522215 := bstep (se 1 (by rfl) ⟨1891661, by rfl⟩ : syracuseStep 2522215 = 3783323) B3783323
theorem B290864303 : Blo 1770086 290864303 := bstep (se 1 (by rfl) ⟨218148227, by rfl⟩ : syracuseStep 290864303 = 436296455) B436296455
theorem B16162375 : Blo 1770086 16162375 := bstep (se 1 (by rfl) ⟨12121781, by rfl⟩ : syracuseStep 16162375 = 24243563) B24243563
theorem B4480859 : Blo 1770086 4480859 := bstep (se 1 (by rfl) ⟨3360644, by rfl⟩ : syracuseStep 4480859 = 6721289) B6721289
theorem B8962649 : Blo 1770086 8962649 := bstep (se 2 (by rfl) ⟨3360993, by rfl⟩ : syracuseStep 8962649 = 6721987) B6721987
theorem B1770235 : Blo 1770086 1770235 := bstep (se 1 (by rfl) ⟨1327676, by rfl⟩ : syracuseStep 1770235 = 2655353) B2655353
theorem B2655263 : Blo 1770086 2655263 := bstep (se 1 (by rfl) ⟨1991447, by rfl⟩ : syracuseStep 2655263 = 3982895) B3982895
theorem B1770527 : Blo 1770086 1770527 := bstep (se 1 (by rfl) ⟨1327895, by rfl⟩ : syracuseStep 1770527 = 2655791) B2655791
theorem B1770751 : Blo 1770086 1770751 := bstep (se 1 (by rfl) ⟨1328063, by rfl⟩ : syracuseStep 1770751 = 2656127) B2656127
theorem B1770943 : Blo 1770086 1770943 := bstep (se 1 (by rfl) ⟨1328207, by rfl⟩ : syracuseStep 1770943 = 2656415) B2656415
theorem B2656169 : Blo 1770086 2656169 := bstep (se 2 (by rfl) ⟨996063, by rfl⟩ : syracuseStep 2656169 = 1992127) B1992127
theorem B4482985 : Blo 1770086 4482985 := bstep (se 2 (by rfl) ⟨1681119, by rfl⟩ : syracuseStep 4482985 = 3362239) B3362239
theorem B2656319 : Blo 1770086 2656319 := bstep (se 1 (by rfl) ⟨1992239, by rfl⟩ : syracuseStep 2656319 = 3984479) B3984479
theorem B1771631 : Blo 1770086 1771631 := bstep (se 1 (by rfl) ⟨1328723, by rfl⟩ : syracuseStep 1771631 = 2657447) B2657447
theorem B1771687 : Blo 1770086 1771687 := bstep (se 1 (by rfl) ⟨1328765, by rfl⟩ : syracuseStep 1771687 = 2657531) B2657531
theorem B1771727 : Blo 1770086 1771727 := bstep (se 1 (by rfl) ⟨1328795, by rfl⟩ : syracuseStep 1771727 = 2657591) B2657591
theorem B3983579 : Blo 1770086 3983579 := bstep (se 1 (by rfl) ⟨2987684, by rfl⟩ : syracuseStep 3983579 = 5975369) B5975369
theorem B2656823 : Blo 1770086 2656823 := bstep (se 1 (by rfl) ⟨1992617, by rfl⟩ : syracuseStep 2656823 = 3985235) B3985235
theorem B4483775 : Blo 1770086 4483775 := bstep (se 1 (by rfl) ⟨3362831, by rfl⟩ : syracuseStep 4483775 = 6725663) B6725663
theorem B2837371 : Blo 1770086 2837371 := bstep (se 1 (by rfl) ⟨2128028, by rfl⟩ : syracuseStep 2837371 = 4256057) B4256057
theorem B2838299 : Blo 1770086 2838299 := bstep (se 1 (by rfl) ⟨2128724, by rfl⟩ : syracuseStep 2838299 = 4257449) B4257449
theorem B3362953 : Blo 1770086 3362953 := bstep (se 2 (by rfl) ⟨1261107, by rfl⟩ : syracuseStep 3362953 = 2522215) B2522215
theorem B6721775 : Blo 1770086 6721775 := bstep (se 1 (by rfl) ⟨5041331, by rfl⟩ : syracuseStep 6721775 = 10082663) B10082663
theorem B21549833 : Blo 1770086 21549833 := bstep (se 2 (by rfl) ⟨8081187, by rfl⟩ : syracuseStep 21549833 = 16162375) B16162375
theorem B193909535 : Blo 1770086 193909535 := bstep (se 1 (by rfl) ⟨145432151, by rfl⟩ : syracuseStep 193909535 = 290864303) B290864303
theorem B2987239 : Blo 1770086 2987239 := bstep (se 1 (by rfl) ⟨2240429, by rfl⟩ : syracuseStep 2987239 = 4480859) B4480859
theorem B6723233 : Blo 1770086 6723233 := bstep (se 2 (by rfl) ⟨2521212, by rfl⟩ : syracuseStep 6723233 = 5042425) B5042425
theorem B5978447 : Blo 1770086 5978447 := bstep (se 1 (by rfl) ⟨4483835, by rfl⟩ : syracuseStep 5978447 = 8967671) B8967671
theorem B8075933 : Blo 1770086 8075933 := bstep (se 3 (by rfl) ⟨1514237, by rfl⟩ : syracuseStep 8075933 = 3028475) B3028475
theorem B5044943 : Blo 1770086 5044943 := bstep (se 1 (by rfl) ⟨3783707, by rfl⟩ : syracuseStep 5044943 = 7567415) B7567415
theorem B2522431 : Blo 1770086 2522431 := bstep (se 1 (by rfl) ⟨1891823, by rfl⟩ : syracuseStep 2522431 = 3783647) B3783647
theorem B4481183 : Blo 1770086 4481183 := bstep (se 1 (by rfl) ⟨3360887, by rfl⟩ : syracuseStep 4481183 = 6721775) B6721775
theorem B1770175 : Blo 1770086 1770175 := bstep (se 1 (by rfl) ⟨1327631, by rfl⟩ : syracuseStep 1770175 = 2655263) B2655263
theorem B4482155 : Blo 1770086 4482155 := bstep (se 1 (by rfl) ⟨3361616, by rfl⟩ : syracuseStep 4482155 = 6723233) B6723233
theorem B1770779 : Blo 1770086 1770779 := bstep (se 1 (by rfl) ⟨1328084, by rfl⟩ : syracuseStep 1770779 = 2656169) B2656169
theorem B1770879 : Blo 1770086 1770879 := bstep (se 1 (by rfl) ⟨1328159, by rfl⟩ : syracuseStep 1770879 = 2656319) B2656319
theorem B2655719 : Blo 1770086 2655719 := bstep (se 1 (by rfl) ⟨1991789, by rfl⟩ : syracuseStep 2655719 = 3983579) B3983579
theorem B3982985 : Blo 1770086 3982985 := bstep (se 2 (by rfl) ⟨1493619, by rfl⟩ : syracuseStep 3982985 = 2987239) B2987239
theorem B13452965 : Blo 1770086 13452965 := bstep (se 4 (by rfl) ⟨1261215, by rfl⟩ : syracuseStep 13452965 = 2522431) B2522431
theorem B1771215 : Blo 1770086 1771215 := bstep (se 1 (by rfl) ⟨1328411, by rfl⟩ : syracuseStep 1771215 = 2656823) B2656823
theorem B5383955 : Blo 1770086 5383955 := bstep (se 1 (by rfl) ⟨4037966, by rfl⟩ : syracuseStep 5383955 = 8075933) B8075933
theorem B4483937 : Blo 1770086 4483937 := bstep (se 2 (by rfl) ⟨1681476, by rfl⟩ : syracuseStep 4483937 = 3362953) B3362953
theorem B5975099 : Blo 1770086 5975099 := bstep (se 1 (by rfl) ⟨4481324, by rfl⟩ : syracuseStep 5975099 = 8962649) B8962649
theorem B129273023 : Blo 1770086 129273023 := bstep (se 1 (by rfl) ⟨96954767, by rfl⟩ : syracuseStep 129273023 = 193909535) B193909535
theorem B3985631 : Blo 1770086 3985631 := bstep (se 1 (by rfl) ⟨2989223, by rfl⟩ : syracuseStep 3985631 = 5978447) B5978447
theorem B3363295 : Blo 1770086 3363295 := bstep (se 1 (by rfl) ⟨2522471, by rfl⟩ : syracuseStep 3363295 = 5044943) B5044943
theorem B5977313 : Blo 1770086 5977313 := bstep (se 2 (by rfl) ⟨2241492, by rfl⟩ : syracuseStep 5977313 = 4482985) B4482985
theorem B14366555 : Blo 1770086 14366555 := bstep (se 1 (by rfl) ⟨10774916, by rfl⟩ : syracuseStep 14366555 = 21549833) B21549833
theorem B3783161 : Blo 1770086 3783161 := bstep (se 2 (by rfl) ⟨1418685, by rfl⟩ : syracuseStep 3783161 = 2837371) B2837371
theorem B2989183 : Blo 1770086 2989183 := bstep (se 1 (by rfl) ⟨2241887, by rfl⟩ : syracuseStep 2989183 = 4483775) B4483775
theorem B7568797 : Blo 1770086 7568797 := bstep (se 3 (by rfl) ⟨1419149, by rfl⟩ : syracuseStep 7568797 = 2838299) B2838299
theorem B1770479 : Blo 1770086 1770479 := bstep (se 1 (by rfl) ⟨1327859, by rfl⟩ : syracuseStep 1770479 = 2655719) B2655719
theorem B2655323 : Blo 1770086 2655323 := bstep (se 1 (by rfl) ⟨1991492, by rfl⟩ : syracuseStep 2655323 = 3982985) B3982985
theorem B3589303 : Blo 1770086 3589303 := bstep (se 1 (by rfl) ⟨2691977, by rfl⟩ : syracuseStep 3589303 = 5383955) B5383955
theorem B9577703 : Blo 1770086 9577703 := bstep (se 1 (by rfl) ⟨7183277, by rfl⟩ : syracuseStep 9577703 = 14366555) B14366555
theorem B3983399 : Blo 1770086 3983399 := bstep (se 1 (by rfl) ⟨2987549, by rfl⟩ : syracuseStep 3983399 = 5975099) B5975099
theorem B86182015 : Blo 1770086 86182015 := bstep (se 1 (by rfl) ⟨64636511, by rfl⟩ : syracuseStep 86182015 = 129273023) B129273023
theorem B2657087 : Blo 1770086 2657087 := bstep (se 1 (by rfl) ⟨1992815, by rfl⟩ : syracuseStep 2657087 = 3985631) B3985631
theorem B4484393 : Blo 1770086 4484393 := bstep (se 2 (by rfl) ⟨1681647, by rfl⟩ : syracuseStep 4484393 = 3363295) B3363295
theorem B3984875 : Blo 1770086 3984875 := bstep (se 1 (by rfl) ⟨2988656, by rfl⟩ : syracuseStep 3984875 = 5977313) B5977313
theorem B3985577 : Blo 1770086 3985577 := bstep (se 2 (by rfl) ⟨1494591, by rfl⟩ : syracuseStep 3985577 = 2989183) B2989183
theorem B2987455 : Blo 1770086 2987455 := bstep (se 1 (by rfl) ⟨2240591, by rfl⟩ : syracuseStep 2987455 = 4481183) B4481183
theorem B2988103 : Blo 1770086 2988103 := bstep (se 1 (by rfl) ⟨2241077, by rfl⟩ : syracuseStep 2988103 = 4482155) B4482155
theorem B8968643 : Blo 1770086 8968643 := bstep (se 1 (by rfl) ⟨6726482, by rfl⟩ : syracuseStep 8968643 = 13452965) B13452965
theorem B2522107 : Blo 1770086 2522107 := bstep (se 1 (by rfl) ⟨1891580, by rfl⟩ : syracuseStep 2522107 = 3783161) B3783161
theorem B10091729 : Blo 1770086 10091729 := bstep (se 2 (by rfl) ⟨3784398, by rfl⟩ : syracuseStep 10091729 = 7568797) B7568797
theorem B2989291 : Blo 1770086 2989291 := bstep (se 1 (by rfl) ⟨2241968, by rfl⟩ : syracuseStep 2989291 = 4483937) B4483937
theorem B114909353 : Blo 1770086 114909353 := bstep (se 2 (by rfl) ⟨43091007, by rfl⟩ : syracuseStep 114909353 = 86182015) B86182015
theorem B1770215 : Blo 1770086 1770215 := bstep (se 1 (by rfl) ⟨1327661, by rfl⟩ : syracuseStep 1770215 = 2655323) B2655323
theorem B2655599 : Blo 1770086 2655599 := bstep (se 1 (by rfl) ⟨1991699, by rfl⟩ : syracuseStep 2655599 = 3983399) B3983399
theorem B4785737 : Blo 1770086 4785737 := bstep (se 2 (by rfl) ⟨1794651, by rfl⟩ : syracuseStep 4785737 = 3589303) B3589303
theorem B1771391 : Blo 1770086 1771391 := bstep (se 1 (by rfl) ⟨1328543, by rfl⟩ : syracuseStep 1771391 = 2657087) B2657087
theorem B3983273 : Blo 1770086 3983273 := bstep (se 2 (by rfl) ⟨1493727, by rfl⟩ : syracuseStep 3983273 = 2987455) B2987455
theorem B2656583 : Blo 1770086 2656583 := bstep (se 1 (by rfl) ⟨1992437, by rfl⟩ : syracuseStep 2656583 = 3984875) B3984875
theorem B3984137 : Blo 1770086 3984137 := bstep (se 2 (by rfl) ⟨1494051, by rfl⟩ : syracuseStep 3984137 = 2988103) B2988103
theorem B2657051 : Blo 1770086 2657051 := bstep (se 1 (by rfl) ⟨1992788, by rfl⟩ : syracuseStep 2657051 = 3985577) B3985577
theorem B6385135 : Blo 1770086 6385135 := bstep (se 1 (by rfl) ⟨4788851, by rfl⟩ : syracuseStep 6385135 = 9577703) B9577703
theorem B3362809 : Blo 1770086 3362809 := bstep (se 2 (by rfl) ⟨1261053, by rfl⟩ : syracuseStep 3362809 = 2522107) B2522107
theorem B3985721 : Blo 1770086 3985721 := bstep (se 2 (by rfl) ⟨1494645, by rfl⟩ : syracuseStep 3985721 = 2989291) B2989291
theorem B5979095 : Blo 1770086 5979095 := bstep (se 1 (by rfl) ⟨4484321, by rfl⟩ : syracuseStep 5979095 = 8968643) B8968643
theorem B2989595 : Blo 1770086 2989595 := bstep (se 1 (by rfl) ⟨2242196, by rfl⟩ : syracuseStep 2989595 = 4484393) B4484393
theorem B6727819 : Blo 1770086 6727819 := bstep (se 1 (by rfl) ⟨5045864, by rfl⟩ : syracuseStep 6727819 = 10091729) B10091729
theorem B8970425 : Blo 1770086 8970425 := bstep (se 2 (by rfl) ⟨3363909, by rfl⟩ : syracuseStep 8970425 = 6727819) B6727819
theorem B1770399 : Blo 1770086 1770399 := bstep (se 1 (by rfl) ⟨1327799, by rfl⟩ : syracuseStep 1770399 = 2655599) B2655599
theorem B2655515 : Blo 1770086 2655515 := bstep (se 1 (by rfl) ⟨1991636, by rfl⟩ : syracuseStep 2655515 = 3983273) B3983273
theorem B1771055 : Blo 1770086 1771055 := bstep (se 1 (by rfl) ⟨1328291, by rfl⟩ : syracuseStep 1771055 = 2656583) B2656583
theorem B2656091 : Blo 1770086 2656091 := bstep (se 1 (by rfl) ⟨1992068, by rfl⟩ : syracuseStep 2656091 = 3984137) B3984137
theorem B1771367 : Blo 1770086 1771367 := bstep (se 1 (by rfl) ⟨1328525, by rfl⟩ : syracuseStep 1771367 = 2657051) B2657051
theorem B8513513 : Blo 1770086 8513513 := bstep (se 2 (by rfl) ⟨3192567, by rfl⟩ : syracuseStep 8513513 = 6385135) B6385135
theorem B1993063 : Blo 1770086 1993063 := bstep (se 1 (by rfl) ⟨1494797, by rfl⟩ : syracuseStep 1993063 = 2989595) B2989595
theorem B4483745 : Blo 1770086 4483745 := bstep (se 2 (by rfl) ⟨1681404, by rfl⟩ : syracuseStep 4483745 = 3362809) B3362809
theorem B76606235 : Blo 1770086 76606235 := bstep (se 1 (by rfl) ⟨57454676, by rfl⟩ : syracuseStep 76606235 = 114909353) B114909353
theorem B2657147 : Blo 1770086 2657147 := bstep (se 1 (by rfl) ⟨1992860, by rfl⟩ : syracuseStep 2657147 = 3985721) B3985721
theorem B3986063 : Blo 1770086 3986063 := bstep (se 1 (by rfl) ⟨2989547, by rfl⟩ : syracuseStep 3986063 = 5979095) B5979095
theorem B12761965 : Blo 1770086 12761965 := bstep (se 3 (by rfl) ⟨2392868, by rfl⟩ : syracuseStep 12761965 = 4785737) B4785737
theorem B5980283 : Blo 1770086 5980283 := bstep (se 1 (by rfl) ⟨4485212, by rfl⟩ : syracuseStep 5980283 = 8970425) B8970425
theorem B1770343 : Blo 1770086 1770343 := bstep (se 1 (by rfl) ⟨1327757, by rfl⟩ : syracuseStep 1770343 = 2655515) B2655515
theorem B1770727 : Blo 1770086 1770727 := bstep (se 1 (by rfl) ⟨1328045, by rfl⟩ : syracuseStep 1770727 = 2656091) B2656091
theorem B51070823 : Blo 1770086 51070823 := bstep (se 1 (by rfl) ⟨38303117, by rfl⟩ : syracuseStep 51070823 = 76606235) B76606235
theorem B1771431 : Blo 1770086 1771431 := bstep (se 1 (by rfl) ⟨1328573, by rfl⟩ : syracuseStep 1771431 = 2657147) B2657147
theorem B2657375 : Blo 1770086 2657375 := bstep (se 1 (by rfl) ⟨1993031, by rfl⟩ : syracuseStep 2657375 = 3986063) B3986063
theorem B2657417 : Blo 1770086 2657417 := bstep (se 2 (by rfl) ⟨996531, by rfl⟩ : syracuseStep 2657417 = 1993063) B1993063
theorem B68063813 : Blo 1770086 68063813 := bstep (se 4 (by rfl) ⟨6380982, by rfl⟩ : syracuseStep 68063813 = 12761965) B12761965
theorem B5675675 : Blo 1770086 5675675 := bstep (se 1 (by rfl) ⟨4256756, by rfl⟩ : syracuseStep 5675675 = 8513513) B8513513
theorem B2989163 : Blo 1770086 2989163 := bstep (se 1 (by rfl) ⟨2241872, by rfl⟩ : syracuseStep 2989163 = 4483745) B4483745
theorem B45375875 : Blo 1770086 45375875 := bstep (se 1 (by rfl) ⟨34031906, by rfl⟩ : syracuseStep 45375875 = 68063813) B68063813
theorem B34047215 : Blo 1770086 34047215 := bstep (se 1 (by rfl) ⟨25535411, by rfl⟩ : syracuseStep 34047215 = 51070823) B51070823
theorem B1771583 : Blo 1770086 1771583 := bstep (se 1 (by rfl) ⟨1328687, by rfl⟩ : syracuseStep 1771583 = 2657375) B2657375
theorem B1992775 : Blo 1770086 1992775 := bstep (se 1 (by rfl) ⟨1494581, by rfl⟩ : syracuseStep 1992775 = 2989163) B2989163
theorem B1771611 : Blo 1770086 1771611 := bstep (se 1 (by rfl) ⟨1328708, by rfl⟩ : syracuseStep 1771611 = 2657417) B2657417
theorem B15135133 : Blo 1770086 15135133 := bstep (se 3 (by rfl) ⟨2837837, by rfl⟩ : syracuseStep 15135133 = 5675675) B5675675
theorem B3986855 : Blo 1770086 3986855 := bstep (se 1 (by rfl) ⟨2990141, by rfl⟩ : syracuseStep 3986855 = 5980283) B5980283
theorem B2657033 : Blo 1770086 2657033 := bstep (se 2 (by rfl) ⟨996387, by rfl⟩ : syracuseStep 2657033 = 1992775) B1992775
theorem B20180177 : Blo 1770086 20180177 := bstep (se 2 (by rfl) ⟨7567566, by rfl⟩ : syracuseStep 20180177 = 15135133) B15135133
theorem B2657903 : Blo 1770086 2657903 := bstep (se 1 (by rfl) ⟨1993427, by rfl⟩ : syracuseStep 2657903 = 3986855) B3986855
theorem B30250583 : Blo 1770086 30250583 := bstep (se 1 (by rfl) ⟨22687937, by rfl⟩ : syracuseStep 30250583 = 45375875) B45375875
theorem B22698143 : Blo 1770086 22698143 := bstep (se 1 (by rfl) ⟨17023607, by rfl⟩ : syracuseStep 22698143 = 34047215) B34047215
theorem B15132095 : Blo 1770086 15132095 := bstep (se 1 (by rfl) ⟨11349071, by rfl⟩ : syracuseStep 15132095 = 22698143) B22698143
theorem B1771355 : Blo 1770086 1771355 := bstep (se 1 (by rfl) ⟨1328516, by rfl⟩ : syracuseStep 1771355 = 2657033) B2657033
theorem B13453451 : Blo 1770086 13453451 := bstep (se 1 (by rfl) ⟨10090088, by rfl⟩ : syracuseStep 13453451 = 20180177) B20180177
theorem B1771935 : Blo 1770086 1771935 := bstep (se 1 (by rfl) ⟨1328951, by rfl⟩ : syracuseStep 1771935 = 2657903) B2657903
theorem B20167055 : Blo 1770086 20167055 := bstep (se 1 (by rfl) ⟨15125291, by rfl⟩ : syracuseStep 20167055 = 30250583) B30250583
theorem B13444703 : Blo 1770086 13444703 := bstep (se 1 (by rfl) ⟨10083527, by rfl⟩ : syracuseStep 13444703 = 20167055) B20167055
theorem B10088063 : Blo 1770086 10088063 := bstep (se 1 (by rfl) ⟨7566047, by rfl⟩ : syracuseStep 10088063 = 15132095) B15132095
theorem B8968967 : Blo 1770086 8968967 := bstep (se 1 (by rfl) ⟨6726725, by rfl⟩ : syracuseStep 8968967 = 13453451) B13453451
theorem B8963135 : Blo 1770086 8963135 := bstep (se 1 (by rfl) ⟨6722351, by rfl⟩ : syracuseStep 8963135 = 13444703) B13444703
theorem B5979311 : Blo 1770086 5979311 := bstep (se 1 (by rfl) ⟨4484483, by rfl⟩ : syracuseStep 5979311 = 8968967) B8968967
theorem B6725375 : Blo 1770086 6725375 := bstep (se 1 (by rfl) ⟨5044031, by rfl⟩ : syracuseStep 6725375 = 10088063) B10088063
theorem B4483583 : Blo 1770086 4483583 := bstep (se 1 (by rfl) ⟨3362687, by rfl⟩ : syracuseStep 4483583 = 6725375) B6725375
theorem B5975423 : Blo 1770086 5975423 := bstep (se 1 (by rfl) ⟨4481567, by rfl⟩ : syracuseStep 5975423 = 8963135) B8963135
theorem B3986207 : Blo 1770086 3986207 := bstep (se 1 (by rfl) ⟨2989655, by rfl⟩ : syracuseStep 3986207 = 5979311) B5979311
theorem B3983615 : Blo 1770086 3983615 := bstep (se 1 (by rfl) ⟨2987711, by rfl⟩ : syracuseStep 3983615 = 5975423) B5975423
theorem B2657471 : Blo 1770086 2657471 := bstep (se 1 (by rfl) ⟨1993103, by rfl⟩ : syracuseStep 2657471 = 3986207) B3986207
theorem B2989055 : Blo 1770086 2989055 := bstep (se 1 (by rfl) ⟨2241791, by rfl⟩ : syracuseStep 2989055 = 4483583) B4483583
theorem B2655743 : Blo 1770086 2655743 := bstep (se 1 (by rfl) ⟨1991807, by rfl⟩ : syracuseStep 2655743 = 3983615) B3983615
theorem B1992703 : Blo 1770086 1992703 := bstep (se 1 (by rfl) ⟨1494527, by rfl⟩ : syracuseStep 1992703 = 2989055) B2989055
theorem B1771647 : Blo 1770086 1771647 := bstep (se 1 (by rfl) ⟨1328735, by rfl⟩ : syracuseStep 1771647 = 2657471) B2657471
theorem B1770495 : Blo 1770086 1770495 := bstep (se 1 (by rfl) ⟨1327871, by rfl⟩ : syracuseStep 1770495 = 2655743) B2655743
theorem B2656937 : Blo 1770086 2656937 := bstep (se 2 (by rfl) ⟨996351, by rfl⟩ : syracuseStep 2656937 = 1992703) B1992703
theorem B1771291 : Blo 1770086 1771291 := bstep (se 1 (by rfl) ⟨1328468, by rfl⟩ : syracuseStep 1771291 = 2656937) B2656937

theorem C0 (j : ℕ) (h1 : 442521 ≤ j) (h2 : j ≤ 443020) : Blo 1770086 (4 * j + 3) := by
  interval_cases j
  · exact B1770087
  · exact B1770091
  · exact B1770095
  · exact B1770099
  · exact B1770103
  · exact B1770107
  · exact B1770111
  · exact B1770115
  · exact B1770119
  · exact B1770123
  · exact B1770127
  · exact B1770131
  · exact B1770135
  · exact B1770139
  · exact B1770143
  · exact B1770147
  · exact B1770151
  · exact B1770155
  · exact B1770159
  · exact B1770163
  · exact B1770167
  · exact B1770171
  · exact B1770175
  · exact B1770179
  · exact B1770183
  · exact B1770187
  · exact B1770191
  · exact B1770195
  · exact B1770199
  · exact B1770203
  · exact B1770207
  · exact B1770211
  · exact B1770215
  · exact B1770219
  · exact B1770223
  · exact B1770227
  · exact B1770231
  · exact B1770235
  · exact B1770239
  · exact B1770243
  · exact B1770247
  · exact B1770251
  · exact B1770255
  · exact B1770259
  · exact B1770263
  · exact B1770267
  · exact B1770271
  · exact B1770275
  · exact B1770279
  · exact B1770283
  · exact B1770287
  · exact B1770291
  · exact B1770295
  · exact B1770299
  · exact B1770303
  · exact B1770307
  · exact B1770311
  · exact B1770315
  · exact B1770319
  · exact B1770323
  · exact B1770327
  · exact B1770331
  · exact B1770335
  · exact B1770339
  · exact B1770343
  · exact B1770347
  · exact B1770351
  · exact B1770355
  · exact B1770359
  · exact B1770363
  · exact B1770367
  · exact B1770371
  · exact B1770375
  · exact B1770379
  · exact B1770383
  · exact B1770387
  · exact B1770391
  · exact B1770395
  · exact B1770399
  · exact B1770403
  · exact B1770407
  · exact B1770411
  · exact B1770415
  · exact B1770419
  · exact B1770423
  · exact B1770427
  · exact B1770431
  · exact B1770435
  · exact B1770439
  · exact B1770443
  · exact B1770447
  · exact B1770451
  · exact B1770455
  · exact B1770459
  · exact B1770463
  · exact B1770467
  · exact B1770471
  · exact B1770475
  · exact B1770479
  · exact B1770483
  · exact B1770487
  · exact B1770491
  · exact B1770495
  · exact B1770499
  · exact B1770503
  · exact B1770507
  · exact B1770511
  · exact B1770515
  · exact B1770519
  · exact B1770523
  · exact B1770527
  · exact B1770531
  · exact B1770535
  · exact B1770539
  · exact B1770543
  · exact B1770547
  · exact B1770551
  · exact B1770555
  · exact B1770559
  · exact B1770563
  · exact B1770567
  · exact B1770571
  · exact B1770575
  · exact B1770579
  · exact B1770583
  · exact B1770587
  · exact B1770591
  · exact B1770595
  · exact B1770599
  · exact B1770603
  · exact B1770607
  · exact B1770611
  · exact B1770615
  · exact B1770619
  · exact B1770623
  · exact B1770627
  · exact B1770631
  · exact B1770635
  · exact B1770639
  · exact B1770643
  · exact B1770647
  · exact B1770651
  · exact B1770655
  · exact B1770659
  · exact B1770663
  · exact B1770667
  · exact B1770671
  · exact B1770675
  · exact B1770679
  · exact B1770683
  · exact B1770687
  · exact B1770691
  · exact B1770695
  · exact B1770699
  · exact B1770703
  · exact B1770707
  · exact B1770711
  · exact B1770715
  · exact B1770719
  · exact B1770723
  · exact B1770727
  · exact B1770731
  · exact B1770735
  · exact B1770739
  · exact B1770743
  · exact B1770747
  · exact B1770751
  · exact B1770755
  · exact B1770759
  · exact B1770763
  · exact B1770767
  · exact B1770771
  · exact B1770775
  · exact B1770779
  · exact B1770783
  · exact B1770787
  · exact B1770791
  · exact B1770795
  · exact B1770799
  · exact B1770803
  · exact B1770807
  · exact B1770811
  · exact B1770815
  · exact B1770819
  · exact B1770823
  · exact B1770827
  · exact B1770831
  · exact B1770835
  · exact B1770839
  · exact B1770843
  · exact B1770847
  · exact B1770851
  · exact B1770855
  · exact B1770859
  · exact B1770863
  · exact B1770867
  · exact B1770871
  · exact B1770875
  · exact B1770879
  · exact B1770883
  · exact B1770887
  · exact B1770891
  · exact B1770895
  · exact B1770899
  · exact B1770903
  · exact B1770907
  · exact B1770911
  · exact B1770915
  · exact B1770919
  · exact B1770923
  · exact B1770927
  · exact B1770931
  · exact B1770935
  · exact B1770939
  · exact B1770943
  · exact B1770947
  · exact B1770951
  · exact B1770955
  · exact B1770959
  · exact B1770963
  · exact B1770967
  · exact B1770971
  · exact B1770975
  · exact B1770979
  · exact B1770983
  · exact B1770987
  · exact B1770991
  · exact B1770995
  · exact B1770999
  · exact B1771003
  · exact B1771007
  · exact B1771011
  · exact B1771015
  · exact B1771019
  · exact B1771023
  · exact B1771027
  · exact B1771031
  · exact B1771035
  · exact B1771039
  · exact B1771043
  · exact B1771047
  · exact B1771051
  · exact B1771055
  · exact B1771059
  · exact B1771063
  · exact B1771067
  · exact B1771071
  · exact B1771075
  · exact B1771079
  · exact B1771083
  · exact B1771087
  · exact B1771091
  · exact B1771095
  · exact B1771099
  · exact B1771103
  · exact B1771107
  · exact B1771111
  · exact B1771115
  · exact B1771119
  · exact B1771123
  · exact B1771127
  · exact B1771131
  · exact B1771135
  · exact B1771139
  · exact B1771143
  · exact B1771147
  · exact B1771151
  · exact B1771155
  · exact B1771159
  · exact B1771163
  · exact B1771167
  · exact B1771171
  · exact B1771175
  · exact B1771179
  · exact B1771183
  · exact B1771187
  · exact B1771191
  · exact B1771195
  · exact B1771199
  · exact B1771203
  · exact B1771207
  · exact B1771211
  · exact B1771215
  · exact B1771219
  · exact B1771223
  · exact B1771227
  · exact B1771231
  · exact B1771235
  · exact B1771239
  · exact B1771243
  · exact B1771247
  · exact B1771251
  · exact B1771255
  · exact B1771259
  · exact B1771263
  · exact B1771267
  · exact B1771271
  · exact B1771275
  · exact B1771279
  · exact B1771283
  · exact B1771287
  · exact B1771291
  · exact B1771295
  · exact B1771299
  · exact B1771303
  · exact B1771307
  · exact B1771311
  · exact B1771315
  · exact B1771319
  · exact B1771323
  · exact B1771327
  · exact B1771331
  · exact B1771335
  · exact B1771339
  · exact B1771343
  · exact B1771347
  · exact B1771351
  · exact B1771355
  · exact B1771359
  · exact B1771363
  · exact B1771367
  · exact B1771371
  · exact B1771375
  · exact B1771379
  · exact B1771383
  · exact B1771387
  · exact B1771391
  · exact B1771395
  · exact B1771399
  · exact B1771403
  · exact B1771407
  · exact B1771411
  · exact B1771415
  · exact B1771419
  · exact B1771423
  · exact B1771427
  · exact B1771431
  · exact B1771435
  · exact B1771439
  · exact B1771443
  · exact B1771447
  · exact B1771451
  · exact B1771455
  · exact B1771459
  · exact B1771463
  · exact B1771467
  · exact B1771471
  · exact B1771475
  · exact B1771479
  · exact B1771483
  · exact B1771487
  · exact B1771491
  · exact B1771495
  · exact B1771499
  · exact B1771503
  · exact B1771507
  · exact B1771511
  · exact B1771515
  · exact B1771519
  · exact B1771523
  · exact B1771527
  · exact B1771531
  · exact B1771535
  · exact B1771539
  · exact B1771543
  · exact B1771547
  · exact B1771551
  · exact B1771555
  · exact B1771559
  · exact B1771563
  · exact B1771567
  · exact B1771571
  · exact B1771575
  · exact B1771579
  · exact B1771583
  · exact B1771587
  · exact B1771591
  · exact B1771595
  · exact B1771599
  · exact B1771603
  · exact B1771607
  · exact B1771611
  · exact B1771615
  · exact B1771619
  · exact B1771623
  · exact B1771627
  · exact B1771631
  · exact B1771635
  · exact B1771639
  · exact B1771643
  · exact B1771647
  · exact B1771651
  · exact B1771655
  · exact B1771659
  · exact B1771663
  · exact B1771667
  · exact B1771671
  · exact B1771675
  · exact B1771679
  · exact B1771683
  · exact B1771687
  · exact B1771691
  · exact B1771695
  · exact B1771699
  · exact B1771703
  · exact B1771707
  · exact B1771711
  · exact B1771715
  · exact B1771719
  · exact B1771723
  · exact B1771727
  · exact B1771731
  · exact B1771735
  · exact B1771739
  · exact B1771743
  · exact B1771747
  · exact B1771751
  · exact B1771755
  · exact B1771759
  · exact B1771763
  · exact B1771767
  · exact B1771771
  · exact B1771775
  · exact B1771779
  · exact B1771783
  · exact B1771787
  · exact B1771791
  · exact B1771795
  · exact B1771799
  · exact B1771803
  · exact B1771807
  · exact B1771811
  · exact B1771815
  · exact B1771819
  · exact B1771823
  · exact B1771827
  · exact B1771831
  · exact B1771835
  · exact B1771839
  · exact B1771843
  · exact B1771847
  · exact B1771851
  · exact B1771855
  · exact B1771859
  · exact B1771863
  · exact B1771867
  · exact B1771871
  · exact B1771875
  · exact B1771879
  · exact B1771883
  · exact B1771887
  · exact B1771891
  · exact B1771895
  · exact B1771899
  · exact B1771903
  · exact B1771907
  · exact B1771911
  · exact B1771915
  · exact B1771919
  · exact B1771923
  · exact B1771927
  · exact B1771931
  · exact B1771935
  · exact B1771939
  · exact B1771943
  · exact B1771947
  · exact B1771951
  · exact B1771955
  · exact B1771959
  · exact B1771963
  · exact B1771967
  · exact B1771971
  · exact B1771975
  · exact B1771979
  · exact B1771983
  · exact B1771987
  · exact B1771991
  · exact B1771995
  · exact B1771999
  · exact B1772003
  · exact B1772007
  · exact B1772011
  · exact B1772015
  · exact B1772019
  · exact B1772023
  · exact B1772027
  · exact B1772031
  · exact B1772035
  · exact B1772039
  · exact B1772043
  · exact B1772047
  · exact B1772051
  · exact B1772055
  · exact B1772059
  · exact B1772063
  · exact B1772067
  · exact B1772071
  · exact B1772075
  · exact B1772079
  · exact B1772083

theorem solution (m : ℕ) (hlo : 1770086 ≤ m) (hhi : m ≤ 1772086) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 442521 ≤ j := by omega
    have hj2 : j ≤ 443020 := by omega
    have hb : Blo 1770086 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
