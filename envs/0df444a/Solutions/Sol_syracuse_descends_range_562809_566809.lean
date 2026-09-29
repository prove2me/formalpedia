-- Prove2me | solution 1 for syracuse_descends_range_562809_566809
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:37.720374+00:00
-- url     : https://prove2.me/submissions/8048eaca-b9c8-48b8-ae78-13a748282685

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


theorem B950285 : Blo 562809 950285 := bbase (se 3 (by rfl) ⟨178178, by rfl⟩ : syracuseStep 950285 = 356357) (by norm_num)
theorem B917525 : Blo 562809 917525 := bbase (se 6 (by rfl) ⟨21504, by rfl⟩ : syracuseStep 917525 = 43009) (by norm_num)
theorem B950413 : Blo 562809 950413 := bbase (se 3 (by rfl) ⟨178202, by rfl⟩ : syracuseStep 950413 = 356405) (by norm_num)
theorem B917669 : Blo 562809 917669 := bbase (se 4 (by rfl) ⟨86031, by rfl⟩ : syracuseStep 917669 = 172063) (by norm_num)
theorem B950501 : Blo 562809 950501 := bbase (se 4 (by rfl) ⟨89109, by rfl⟩ : syracuseStep 950501 = 178219) (by norm_num)
theorem B4817141 : Blo 562809 4817141 := bbase (se 5 (by rfl) ⟨225803, by rfl⟩ : syracuseStep 4817141 = 451607) (by norm_num)
theorem B1900853 : Blo 562809 1900853 := bbase (se 5 (by rfl) ⟨89102, by rfl⟩ : syracuseStep 1900853 = 178205) (by norm_num)
theorem B950629 : Blo 562809 950629 := bbase (se 4 (by rfl) ⟨89121, by rfl⟩ : syracuseStep 950629 = 178243) (by norm_num)
theorem B4882837 : Blo 562809 4882837 := bbase (se 6 (by rfl) ⟨114441, by rfl⟩ : syracuseStep 4882837 = 228883) (by norm_num)
theorem B950717 : Blo 562809 950717 := bbase (se 3 (by rfl) ⟨178259, by rfl⟩ : syracuseStep 950717 = 356519) (by norm_num)
theorem B1147429 : Blo 562809 1147429 := bbase (se 4 (by rfl) ⟨107571, by rfl⟩ : syracuseStep 1147429 = 215143) (by norm_num)
theorem B950845 : Blo 562809 950845 := bbase (se 3 (by rfl) ⟨178283, by rfl⟩ : syracuseStep 950845 = 356567) (by norm_num)
theorem B1016405 : Blo 562809 1016405 := bbase (se 8 (by rfl) ⟨5955, by rfl⟩ : syracuseStep 1016405 = 11911) (by norm_num)
theorem B1147477 : Blo 562809 1147477 := bbase (se 8 (by rfl) ⟨6723, by rfl⟩ : syracuseStep 1147477 = 13447) (by norm_num)
theorem B950933 : Blo 562809 950933 := bbase (se 6 (by rfl) ⟨22287, by rfl⟩ : syracuseStep 950933 = 44575) (by norm_num)
theorem B1016477 : Blo 562809 1016477 := bbase (se 3 (by rfl) ⟨190589, by rfl⟩ : syracuseStep 1016477 = 381179) (by norm_num)
theorem B1901285 : Blo 562809 1901285 := bbase (se 4 (by rfl) ⟨178245, by rfl⟩ : syracuseStep 1901285 = 356491) (by norm_num)
theorem B951061 : Blo 562809 951061 := bbase (se 6 (by rfl) ⟨22290, by rfl⟩ : syracuseStep 951061 = 44581) (by norm_num)
theorem B2851685 : Blo 562809 2851685 := bbase (se 4 (by rfl) ⟨267345, by rfl⟩ : syracuseStep 2851685 = 534691) (by norm_num)
theorem B951149 : Blo 562809 951149 := bbase (se 3 (by rfl) ⟨178340, by rfl⟩ : syracuseStep 951149 = 356681) (by norm_num)
theorem B1835909 : Blo 562809 1835909 := bbase (se 4 (by rfl) ⟨172116, by rfl⟩ : syracuseStep 1835909 = 344233) (by norm_num)
theorem B951277 : Blo 562809 951277 := bbase (se 3 (by rfl) ⟨178364, by rfl⟩ : syracuseStep 951277 = 356729) (by norm_num)
theorem B3441653 : Blo 562809 3441653 := bbase (se 5 (by rfl) ⟨161327, by rfl⟩ : syracuseStep 3441653 = 322655) (by norm_num)
theorem B951365 : Blo 562809 951365 := bbase (se 4 (by rfl) ⟨89190, by rfl⟩ : syracuseStep 951365 = 178381) (by norm_num)
theorem B1901717 : Blo 562809 1901717 := bbase (se 6 (by rfl) ⟨44571, by rfl⟩ : syracuseStep 1901717 = 89143) (by norm_num)
theorem B951493 : Blo 562809 951493 := bbase (se 4 (by rfl) ⟨89202, by rfl⟩ : syracuseStep 951493 = 178405) (by norm_num)
theorem B1606853 : Blo 562809 1606853 := bbase (se 4 (by rfl) ⟨150642, by rfl⟩ : syracuseStep 1606853 = 301285) (by norm_num)
theorem B951581 : Blo 562809 951581 := bbase (se 3 (by rfl) ⟨178421, by rfl⟩ : syracuseStep 951581 = 356843) (by norm_num)
theorem B951709 : Blo 562809 951709 := bbase (se 3 (by rfl) ⟨178445, by rfl⟩ : syracuseStep 951709 = 356891) (by norm_num)
theorem B951797 : Blo 562809 951797 := bbase (se 5 (by rfl) ⟨44615, by rfl⟩ : syracuseStep 951797 = 89231) (by norm_num)
theorem B1934837 : Blo 562809 1934837 := bbase (se 5 (by rfl) ⟨90695, by rfl⟩ : syracuseStep 1934837 = 181391) (by norm_num)
theorem B1902149 : Blo 562809 1902149 := bbase (se 4 (by rfl) ⟨178326, by rfl⟩ : syracuseStep 1902149 = 356653) (by norm_num)
theorem B3212885 : Blo 562809 3212885 := bbase (se 8 (by rfl) ⟨18825, by rfl⟩ : syracuseStep 3212885 = 37651) (by norm_num)
theorem B1148509 : Blo 562809 1148509 := bbase (se 3 (by rfl) ⟨215345, by rfl⟩ : syracuseStep 1148509 = 430691) (by norm_num)
theorem B951925 : Blo 562809 951925 := bbase (se 5 (by rfl) ⟨44621, by rfl⟩ : syracuseStep 951925 = 89243) (by norm_num)
theorem B952013 : Blo 562809 952013 := bbase (se 3 (by rfl) ⟨178502, by rfl⟩ : syracuseStep 952013 = 357005) (by norm_num)
theorem B952141 : Blo 562809 952141 := bbase (se 3 (by rfl) ⟨178526, by rfl⟩ : syracuseStep 952141 = 357053) (by norm_num)
theorem B952229 : Blo 562809 952229 := bbase (se 4 (by rfl) ⟨89271, by rfl⟩ : syracuseStep 952229 = 178543) (by norm_num)
theorem B1902581 : Blo 562809 1902581 := bbase (se 5 (by rfl) ⟨89183, by rfl⟩ : syracuseStep 1902581 = 178367) (by norm_num)
theorem B952357 : Blo 562809 952357 := bbase (se 4 (by rfl) ⟨89283, by rfl⟩ : syracuseStep 952357 = 178567) (by norm_num)
theorem B2852981 : Blo 562809 2852981 := bbase (se 5 (by rfl) ⟨133733, by rfl⟩ : syracuseStep 2852981 = 267467) (by norm_num)
theorem B952445 : Blo 562809 952445 := bbase (se 3 (by rfl) ⟨178583, by rfl⟩ : syracuseStep 952445 = 357167) (by norm_num)
theorem B952573 : Blo 562809 952573 := bbase (se 3 (by rfl) ⟨178607, by rfl⟩ : syracuseStep 952573 = 357215) (by norm_num)
theorem B952661 : Blo 562809 952661 := bbase (se 10 (by rfl) ⟨1395, by rfl⟩ : syracuseStep 952661 = 2791) (by norm_num)
theorem B2754917 : Blo 562809 2754917 := bbase (se 4 (by rfl) ⟨258273, by rfl⟩ : syracuseStep 2754917 = 516547) (by norm_num)
theorem B1903013 : Blo 562809 1903013 := bbase (se 4 (by rfl) ⟨178407, by rfl⟩ : syracuseStep 1903013 = 356815) (by norm_num)
theorem B952789 : Blo 562809 952789 := bbase (se 7 (by rfl) ⟨11165, by rfl⟩ : syracuseStep 952789 = 22331) (by norm_num)
theorem B952877 : Blo 562809 952877 := bbase (se 3 (by rfl) ⟨178664, by rfl⟩ : syracuseStep 952877 = 357329) (by norm_num)
theorem B2722405 : Blo 562809 2722405 := bbase (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) (by norm_num)
theorem B953005 : Blo 562809 953005 := bbase (se 3 (by rfl) ⟨178688, by rfl⟩ : syracuseStep 953005 = 357377) (by norm_num)
theorem B1378997 : Blo 562809 1378997 := bbase (se 5 (by rfl) ⟨64640, by rfl⟩ : syracuseStep 1378997 = 129281) (by norm_num)
theorem B1608437 : Blo 562809 1608437 := bbase (se 5 (by rfl) ⟨75395, by rfl⟩ : syracuseStep 1608437 = 150791) (by norm_num)
theorem B953093 : Blo 562809 953093 := bbase (se 4 (by rfl) ⟨89352, by rfl⟩ : syracuseStep 953093 = 178705) (by norm_num)
theorem B1903445 : Blo 562809 1903445 := bbase (se 9 (by rfl) ⟨5576, by rfl⟩ : syracuseStep 1903445 = 11153) (by norm_num)
theorem B953221 : Blo 562809 953221 := bbase (se 4 (by rfl) ⟨89364, by rfl⟩ : syracuseStep 953221 = 178729) (by norm_num)
theorem B953309 : Blo 562809 953309 := bbase (se 3 (by rfl) ⟨178745, by rfl⟩ : syracuseStep 953309 = 357491) (by norm_num)
theorem B953437 : Blo 562809 953437 := bbase (se 3 (by rfl) ⟨178769, by rfl⟩ : syracuseStep 953437 = 357539) (by norm_num)
theorem B1805429 : Blo 562809 1805429 := bbase (se 5 (by rfl) ⟨84629, by rfl⟩ : syracuseStep 1805429 = 169259) (by norm_num)
theorem B953525 : Blo 562809 953525 := bbase (se 5 (by rfl) ⟨44696, by rfl⟩ : syracuseStep 953525 = 89393) (by norm_num)
theorem B1903877 : Blo 562809 1903877 := bbase (se 4 (by rfl) ⟨178488, by rfl⟩ : syracuseStep 1903877 = 356977) (by norm_num)
theorem B953653 : Blo 562809 953653 := bbase (se 5 (by rfl) ⟨44702, by rfl⟩ : syracuseStep 953653 = 89405) (by norm_num)
theorem B1019245 : Blo 562809 1019245 := bbase (se 3 (by rfl) ⟨191108, by rfl⟩ : syracuseStep 1019245 = 382217) (by norm_num)
theorem B2854277 : Blo 562809 2854277 := bbase (se 4 (by rfl) ⟨267588, by rfl⟩ : syracuseStep 2854277 = 535177) (by norm_num)
theorem B953741 : Blo 562809 953741 := bbase (se 3 (by rfl) ⟨178826, by rfl⟩ : syracuseStep 953741 = 357653) (by norm_num)
theorem B1609109 : Blo 562809 1609109 := bbase (se 6 (by rfl) ⟨37713, by rfl⟩ : syracuseStep 1609109 = 75427) (by norm_num)
theorem B953869 : Blo 562809 953869 := bbase (se 3 (by rfl) ⟨178850, by rfl⟩ : syracuseStep 953869 = 357701) (by norm_num)
theorem B626213 : Blo 562809 626213 := bbase (se 4 (by rfl) ⟨58707, by rfl⟩ : syracuseStep 626213 = 117415) (by norm_num)
theorem B1019461 : Blo 562809 1019461 := bbase (se 4 (by rfl) ⟨95574, by rfl⟩ : syracuseStep 1019461 = 191149) (by norm_num)
theorem B953957 : Blo 562809 953957 := bbase (se 4 (by rfl) ⟨89433, by rfl⟩ : syracuseStep 953957 = 178867) (by norm_num)
theorem B1445485 : Blo 562809 1445485 := bbase (se 3 (by rfl) ⟨271028, by rfl⟩ : syracuseStep 1445485 = 542057) (by norm_num)
theorem B1904309 : Blo 562809 1904309 := bbase (se 5 (by rfl) ⟨89264, by rfl⟩ : syracuseStep 1904309 = 178529) (by norm_num)
theorem B954085 : Blo 562809 954085 := bbase (se 4 (by rfl) ⟨89445, by rfl⟩ : syracuseStep 954085 = 178891) (by norm_num)
theorem B954173 : Blo 562809 954173 := bbase (se 3 (by rfl) ⟨178907, by rfl⟩ : syracuseStep 954173 = 357815) (by norm_num)
theorem B1609541 : Blo 562809 1609541 := bbase (se 4 (by rfl) ⟨150894, by rfl⟩ : syracuseStep 1609541 = 301789) (by norm_num)
theorem B954301 : Blo 562809 954301 := bbase (se 3 (by rfl) ⟨178931, by rfl⟩ : syracuseStep 954301 = 357863) (by norm_num)
theorem B954389 : Blo 562809 954389 := bbase (se 6 (by rfl) ⟨22368, by rfl⟩ : syracuseStep 954389 = 44737) (by norm_num)
theorem B4296725 : Blo 562809 4296725 := bbase (se 6 (by rfl) ⟨100704, by rfl⟩ : syracuseStep 4296725 = 201409) (by norm_num)
theorem B13176917 : Blo 562809 13176917 := bbase (se 8 (by rfl) ⟨77208, by rfl⟩ : syracuseStep 13176917 = 154417) (by norm_num)
theorem B1904741 : Blo 562809 1904741 := bbase (se 4 (by rfl) ⟨178569, by rfl⟩ : syracuseStep 1904741 = 357139) (by norm_num)
theorem B954517 : Blo 562809 954517 := bbase (se 6 (by rfl) ⟨22371, by rfl⟩ : syracuseStep 954517 = 44743) (by norm_num)
theorem B954605 : Blo 562809 954605 := bbase (se 3 (by rfl) ⟨178988, by rfl⟩ : syracuseStep 954605 = 357977) (by norm_num)
theorem B954733 : Blo 562809 954733 := bbase (se 3 (by rfl) ⟨179012, by rfl⟩ : syracuseStep 954733 = 358025) (by norm_num)
theorem B1020269 : Blo 562809 1020269 := bbase (se 3 (by rfl) ⟨191300, by rfl⟩ : syracuseStep 1020269 = 382601) (by norm_num)
theorem B1806725 : Blo 562809 1806725 := bbase (se 4 (by rfl) ⟨169380, by rfl⟩ : syracuseStep 1806725 = 338761) (by norm_num)
theorem B954821 : Blo 562809 954821 := bbase (se 4 (by rfl) ⟨89514, by rfl⟩ : syracuseStep 954821 = 179029) (by norm_num)
theorem B725477 : Blo 562809 725477 := bbase (se 4 (by rfl) ⟨68013, by rfl⟩ : syracuseStep 725477 = 136027) (by norm_num)
theorem B1020413 : Blo 562809 1020413 := bbase (se 3 (by rfl) ⟨191327, by rfl⟩ : syracuseStep 1020413 = 382655) (by norm_num)
theorem B1905173 : Blo 562809 1905173 := bbase (se 6 (by rfl) ⟨44652, by rfl⟩ : syracuseStep 1905173 = 89305) (by norm_num)
theorem B1086005 : Blo 562809 1086005 := bbase (se 5 (by rfl) ⟨50906, by rfl⟩ : syracuseStep 1086005 = 101813) (by norm_num)
theorem B1610293 : Blo 562809 1610293 := bbase (se 5 (by rfl) ⟨75482, by rfl⟩ : syracuseStep 1610293 = 150965) (by norm_num)
theorem B954949 : Blo 562809 954949 := bbase (se 4 (by rfl) ⟨89526, by rfl⟩ : syracuseStep 954949 = 179053) (by norm_num)
theorem B7246421 : Blo 562809 7246421 := bbase (se 8 (by rfl) ⟨42459, by rfl⟩ : syracuseStep 7246421 = 84919) (by norm_num)
theorem B2855573 : Blo 562809 2855573 := bbase (se 6 (by rfl) ⟨66927, by rfl⟩ : syracuseStep 2855573 = 133855) (by norm_num)
theorem B8163989 : Blo 562809 8163989 := bbase (se 6 (by rfl) ⟨191343, by rfl⟩ : syracuseStep 8163989 = 382687) (by norm_num)
theorem B955037 : Blo 562809 955037 := bbase (se 3 (by rfl) ⟨179069, by rfl⟩ : syracuseStep 955037 = 358139) (by norm_num)
theorem B3609269 : Blo 562809 3609269 := bbase (se 5 (by rfl) ⟨169184, by rfl⟩ : syracuseStep 3609269 = 338369) (by norm_num)
theorem B1020629 : Blo 562809 1020629 := bbase (se 7 (by rfl) ⟨11960, by rfl⟩ : syracuseStep 1020629 = 23921) (by norm_num)
theorem B1086221 : Blo 562809 1086221 := bbase (se 3 (by rfl) ⟨203666, by rfl⟩ : syracuseStep 1086221 = 407333) (by norm_num)
theorem B2036501 : Blo 562809 2036501 := bbase (se 6 (by rfl) ⟨47730, by rfl⟩ : syracuseStep 2036501 = 95461) (by norm_num)
theorem B955165 : Blo 562809 955165 := bbase (se 3 (by rfl) ⟨179093, by rfl⟩ : syracuseStep 955165 = 358187) (by norm_num)
theorem B955253 : Blo 562809 955253 := bbase (se 5 (by rfl) ⟨44777, by rfl⟩ : syracuseStep 955253 = 89555) (by norm_num)
theorem B1905605 : Blo 562809 1905605 := bbase (se 4 (by rfl) ⟨178650, by rfl⟩ : syracuseStep 1905605 = 357301) (by norm_num)
theorem B955381 : Blo 562809 955381 := bbase (se 5 (by rfl) ⟨44783, by rfl⟩ : syracuseStep 955381 = 89567) (by norm_num)
theorem B955469 : Blo 562809 955469 := bbase (se 3 (by rfl) ⟨179150, by rfl⟩ : syracuseStep 955469 = 358301) (by norm_num)
theorem B955597 : Blo 562809 955597 := bbase (se 3 (by rfl) ⟨179174, by rfl⟩ : syracuseStep 955597 = 358349) (by norm_num)
theorem B1021133 : Blo 562809 1021133 := bbase (se 3 (by rfl) ⟨191462, by rfl⟩ : syracuseStep 1021133 = 382925) (by norm_num)
theorem B955685 : Blo 562809 955685 := bbase (se 4 (by rfl) ⟨89595, by rfl⟩ : syracuseStep 955685 = 179191) (by norm_num)
theorem B1906037 : Blo 562809 1906037 := bbase (se 5 (by rfl) ⟨89345, by rfl⟩ : syracuseStep 1906037 = 178691) (by norm_num)
theorem B955813 : Blo 562809 955813 := bbase (se 4 (by rfl) ⟨89607, by rfl⟩ : syracuseStep 955813 = 179215) (by norm_num)
theorem B955901 : Blo 562809 955901 := bbase (se 3 (by rfl) ⟨179231, by rfl⟩ : syracuseStep 955901 = 358463) (by norm_num)
theorem B3053173 : Blo 562809 3053173 := bbase (se 5 (by rfl) ⟨143117, by rfl⟩ : syracuseStep 3053173 = 286235) (by norm_num)
theorem B956029 : Blo 562809 956029 := bbase (se 3 (by rfl) ⟨179255, by rfl⟩ : syracuseStep 956029 = 358511) (by norm_num)
theorem B1119949 : Blo 562809 1119949 := bbase (se 3 (by rfl) ⟨209990, by rfl⟩ : syracuseStep 1119949 = 419981) (by norm_num)
theorem B956117 : Blo 562809 956117 := bbase (se 7 (by rfl) ⟨11204, by rfl⟩ : syracuseStep 956117 = 22409) (by norm_num)
theorem B1906469 : Blo 562809 1906469 := bbase (se 4 (by rfl) ⟨178731, by rfl⟩ : syracuseStep 1906469 = 357463) (by norm_num)
theorem B956245 : Blo 562809 956245 := bbase (se 9 (by rfl) ⟨2801, by rfl⟩ : syracuseStep 956245 = 5603) (by norm_num)
theorem B726889 : Blo 562809 726889 := bbase (se 2 (by rfl) ⟨272583, by rfl⟩ : syracuseStep 726889 = 545167) (by norm_num)
theorem B2037653 : Blo 562809 2037653 := bbase (se 6 (by rfl) ⟨47757, by rfl⟩ : syracuseStep 2037653 = 95515) (by norm_num)
theorem B2856869 : Blo 562809 2856869 := bbase (se 4 (by rfl) ⟨267831, by rfl⟩ : syracuseStep 2856869 = 535663) (by norm_num)
theorem B956333 : Blo 562809 956333 := bbase (se 3 (by rfl) ⟨179312, by rfl⟩ : syracuseStep 956333 = 358625) (by norm_num)
theorem B956461 : Blo 562809 956461 := bbase (se 3 (by rfl) ⟨179336, by rfl⟩ : syracuseStep 956461 = 358673) (by norm_num)
theorem B1808581 : Blo 562809 1808581 := bbase (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) (by norm_num)
theorem B1906901 : Blo 562809 1906901 := bbase (se 7 (by rfl) ⟨22346, by rfl⟩ : syracuseStep 1906901 = 44693) (by norm_num)
theorem B2169301 : Blo 562809 2169301 := bbase (se 7 (by rfl) ⟨25421, by rfl⟩ : syracuseStep 2169301 = 50843) (by norm_num)
theorem B1907333 : Blo 562809 1907333 := bbase (se 4 (by rfl) ⟨178812, by rfl⟩ : syracuseStep 1907333 = 357625) (by norm_num)
theorem B1514501 : Blo 562809 1514501 := bbase (se 4 (by rfl) ⟨141984, by rfl⟩ : syracuseStep 1514501 = 283969) (by norm_num)
theorem B1907765 : Blo 562809 1907765 := bbase (se 5 (by rfl) ⟨89426, by rfl⟩ : syracuseStep 1907765 = 178853) (by norm_num)
theorem B2858165 : Blo 562809 2858165 := bbase (se 5 (by rfl) ⟨133976, by rfl⟩ : syracuseStep 2858165 = 267953) (by norm_num)
theorem B1613141 : Blo 562809 1613141 := bbase (se 11 (by rfl) ⟨1181, by rfl⟩ : syracuseStep 1613141 = 2363) (by norm_num)
theorem B2891173 : Blo 562809 2891173 := bbase (se 4 (by rfl) ⟨271047, by rfl⟩ : syracuseStep 2891173 = 542095) (by norm_num)
theorem B1908197 : Blo 562809 1908197 := bbase (se 4 (by rfl) ⟨178893, by rfl⟩ : syracuseStep 1908197 = 357787) (by norm_num)
theorem B1089085 : Blo 562809 1089085 := bbase (se 3 (by rfl) ⟨204203, by rfl⟩ : syracuseStep 1089085 = 408407) (by norm_num)
theorem B1908629 : Blo 562809 1908629 := bbase (se 6 (by rfl) ⟨44733, by rfl⟩ : syracuseStep 1908629 = 89467) (by norm_num)
theorem B2138021 : Blo 562809 2138021 := bbase (se 4 (by rfl) ⟨200439, by rfl⟩ : syracuseStep 2138021 = 400879) (by norm_num)
theorem B1646741 : Blo 562809 1646741 := bbase (se 6 (by rfl) ⟨38595, by rfl⟩ : syracuseStep 1646741 = 77191) (by norm_num)
theorem B2138309 : Blo 562809 2138309 := bbase (se 4 (by rfl) ⟨200466, by rfl⟩ : syracuseStep 2138309 = 400933) (by norm_num)
theorem B1909061 : Blo 562809 1909061 := bbase (se 4 (by rfl) ⟨178974, by rfl⟩ : syracuseStep 1909061 = 357949) (by norm_num)
theorem B1286533 : Blo 562809 1286533 := bbase (se 4 (by rfl) ⟨120612, by rfl⟩ : syracuseStep 1286533 = 241225) (by norm_num)
theorem B2859461 : Blo 562809 2859461 := bbase (se 4 (by rfl) ⟨268074, by rfl⟩ : syracuseStep 2859461 = 536149) (by norm_num)
theorem B664013 : Blo 562809 664013 := bbase (se 3 (by rfl) ⟨124502, by rfl⟩ : syracuseStep 664013 = 249005) (by norm_num)
theorem B1909493 : Blo 562809 1909493 := bbase (se 5 (by rfl) ⟨89507, by rfl⟩ : syracuseStep 1909493 = 179015) (by norm_num)
theorem B5219093 : Blo 562809 5219093 := bbase (se 6 (by rfl) ⟨122322, by rfl⟩ : syracuseStep 5219093 = 244645) (by norm_num)
theorem B1352477 : Blo 562809 1352477 := bbase (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) (by norm_num)
theorem B1909925 : Blo 562809 1909925 := bbase (se 4 (by rfl) ⟨179055, by rfl⟩ : syracuseStep 1909925 = 358111) (by norm_num)
theorem B828613 : Blo 562809 828613 := bbase (se 4 (by rfl) ⟨77682, by rfl⟩ : syracuseStep 828613 = 155365) (by norm_num)
theorem B1353053 : Blo 562809 1353053 := bbase (se 3 (by rfl) ⟨253697, by rfl⟩ : syracuseStep 1353053 = 507395) (by norm_num)
theorem B2139493 : Blo 562809 2139493 := bbase (se 4 (by rfl) ⟨200577, by rfl⟩ : syracuseStep 2139493 = 401155) (by norm_num)
theorem B1222141 : Blo 562809 1222141 := bbase (se 3 (by rfl) ⟨229151, by rfl⟩ : syracuseStep 1222141 = 458303) (by norm_num)
theorem B1910357 : Blo 562809 1910357 := bbase (se 8 (by rfl) ⟨11193, by rfl⟩ : syracuseStep 1910357 = 22387) (by norm_num)
theorem B2139797 : Blo 562809 2139797 := bbase (se 6 (by rfl) ⟨50151, by rfl⟩ : syracuseStep 2139797 = 100303) (by norm_num)
theorem B763597 : Blo 562809 763597 := bbase (se 3 (by rfl) ⟨143174, by rfl⟩ : syracuseStep 763597 = 286349) (by norm_num)
theorem B2860757 : Blo 562809 2860757 := bbase (se 7 (by rfl) ⟨33524, by rfl⟩ : syracuseStep 2860757 = 67049) (by norm_num)
theorem B1910789 : Blo 562809 1910789 := bbase (se 4 (by rfl) ⟨179136, by rfl⟩ : syracuseStep 1910789 = 358273) (by norm_num)
theorem B993485 : Blo 562809 993485 := bbase (se 3 (by rfl) ⟨186278, by rfl⟩ : syracuseStep 993485 = 372557) (by norm_num)
theorem B1812773 : Blo 562809 1812773 := bbase (se 4 (by rfl) ⟨169947, by rfl⟩ : syracuseStep 1812773 = 339895) (by norm_num)
theorem B3909941 : Blo 562809 3909941 := bbase (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) (by norm_num)
theorem B633181 : Blo 562809 633181 := bbase (se 3 (by rfl) ⟨118721, by rfl⟩ : syracuseStep 633181 = 237443) (by norm_num)
theorem B3058037 : Blo 562809 3058037 := bbase (se 5 (by rfl) ⟨143345, by rfl⟩ : syracuseStep 3058037 = 286691) (by norm_num)
theorem B633217 : Blo 562809 633217 := bbase (se 2 (by rfl) ⟨237456, by rfl⟩ : syracuseStep 633217 = 474913) (by norm_num)
theorem B633253 : Blo 562809 633253 := bbase (se 4 (by rfl) ⟨59367, by rfl⟩ : syracuseStep 633253 = 118735) (by norm_num)
theorem B1911221 : Blo 562809 1911221 := bbase (se 5 (by rfl) ⟨89588, by rfl⟩ : syracuseStep 1911221 = 179177) (by norm_num)
theorem B633289 : Blo 562809 633289 := bbase (se 2 (by rfl) ⟨237483, by rfl⟩ : syracuseStep 633289 = 474967) (by norm_num)
theorem B633325 : Blo 562809 633325 := bbase (se 3 (by rfl) ⟨118748, by rfl⟩ : syracuseStep 633325 = 237497) (by norm_num)
theorem B633361 : Blo 562809 633361 := bbase (se 2 (by rfl) ⟨237510, by rfl⟩ : syracuseStep 633361 = 475021) (by norm_num)
theorem B633397 : Blo 562809 633397 := bbase (se 5 (by rfl) ⟨29690, by rfl⟩ : syracuseStep 633397 = 59381) (by norm_num)
theorem B3615317 : Blo 562809 3615317 := bbase (se 8 (by rfl) ⟨21183, by rfl⟩ : syracuseStep 3615317 = 42367) (by norm_num)
theorem B633433 : Blo 562809 633433 := bbase (se 2 (by rfl) ⟨237537, by rfl⟩ : syracuseStep 633433 = 475075) (by norm_num)
theorem B633469 : Blo 562809 633469 := bbase (se 3 (by rfl) ⟨118775, by rfl⟩ : syracuseStep 633469 = 237551) (by norm_num)
theorem B633505 : Blo 562809 633505 := bbase (se 2 (by rfl) ⟨237564, by rfl⟩ : syracuseStep 633505 = 475129) (by norm_num)
theorem B633541 : Blo 562809 633541 := bbase (se 4 (by rfl) ⟨59394, by rfl⟩ : syracuseStep 633541 = 118789) (by norm_num)
theorem B633577 : Blo 562809 633577 := bbase (se 2 (by rfl) ⟨237591, by rfl⟩ : syracuseStep 633577 = 475183) (by norm_num)
theorem B633613 : Blo 562809 633613 := bbase (se 3 (by rfl) ⟨118802, by rfl⟩ : syracuseStep 633613 = 237605) (by norm_num)
theorem B633649 : Blo 562809 633649 := bbase (se 2 (by rfl) ⟨237618, by rfl⟩ : syracuseStep 633649 = 475237) (by norm_num)
theorem B633685 : Blo 562809 633685 := bbase (se 9 (by rfl) ⟨1856, by rfl⟩ : syracuseStep 633685 = 3713) (by norm_num)
theorem B1911653 : Blo 562809 1911653 := bbase (se 4 (by rfl) ⟨179217, by rfl⟩ : syracuseStep 1911653 = 358435) (by norm_num)
theorem B633721 : Blo 562809 633721 := bbase (se 2 (by rfl) ⟨237645, by rfl⟩ : syracuseStep 633721 = 475291) (by norm_num)
theorem B4565909 : Blo 562809 4565909 := bbase (se 6 (by rfl) ⟨107013, by rfl⟩ : syracuseStep 4565909 = 214027) (by norm_num)
theorem B633757 : Blo 562809 633757 := bbase (se 3 (by rfl) ⟨118829, by rfl⟩ : syracuseStep 633757 = 237659) (by norm_num)
theorem B633793 : Blo 562809 633793 := bbase (se 2 (by rfl) ⟨237672, by rfl⟩ : syracuseStep 633793 = 475345) (by norm_num)
theorem B633829 : Blo 562809 633829 := bbase (se 4 (by rfl) ⟨59421, by rfl⟩ : syracuseStep 633829 = 118843) (by norm_num)
theorem B2862053 : Blo 562809 2862053 := bbase (se 4 (by rfl) ⟨268317, by rfl⟩ : syracuseStep 2862053 = 536635) (by norm_num)
theorem B633865 : Blo 562809 633865 := bbase (se 2 (by rfl) ⟨237699, by rfl⟩ : syracuseStep 633865 = 475399) (by norm_num)
theorem B633901 : Blo 562809 633901 := bbase (se 3 (by rfl) ⟨118856, by rfl⟩ : syracuseStep 633901 = 237713) (by norm_num)
theorem B633937 : Blo 562809 633937 := bbase (se 2 (by rfl) ⟨237726, by rfl⟩ : syracuseStep 633937 = 475453) (by norm_num)
theorem B633973 : Blo 562809 633973 := bbase (se 5 (by rfl) ⟨29717, by rfl⟩ : syracuseStep 633973 = 59435) (by norm_num)
theorem B601229 : Blo 562809 601229 := bbase (se 3 (by rfl) ⟨112730, by rfl⟩ : syracuseStep 601229 = 225461) (by norm_num)
theorem B634009 : Blo 562809 634009 := bbase (se 2 (by rfl) ⟨237753, by rfl⟩ : syracuseStep 634009 = 475507) (by norm_num)
theorem B634045 : Blo 562809 634045 := bbase (se 3 (by rfl) ⟨118883, by rfl⟩ : syracuseStep 634045 = 237767) (by norm_num)
theorem B634081 : Blo 562809 634081 := bbase (se 2 (by rfl) ⟨237780, by rfl⟩ : syracuseStep 634081 = 475561) (by norm_num)
theorem B3222773 : Blo 562809 3222773 := bbase (se 5 (by rfl) ⟨151067, by rfl⟩ : syracuseStep 3222773 = 302135) (by norm_num)
theorem B634117 : Blo 562809 634117 := bbase (se 4 (by rfl) ⟨59448, by rfl⟩ : syracuseStep 634117 = 118897) (by norm_num)
theorem B1912085 : Blo 562809 1912085 := bbase (se 6 (by rfl) ⟨44814, by rfl⟩ : syracuseStep 1912085 = 89629) (by norm_num)
theorem B732449 : Blo 562809 732449 := bbase (se 2 (by rfl) ⟨274668, by rfl⟩ : syracuseStep 732449 = 549337) (by norm_num)
theorem B634153 : Blo 562809 634153 := bbase (se 2 (by rfl) ⟨237807, by rfl⟩ : syracuseStep 634153 = 475615) (by norm_num)
theorem B1289525 : Blo 562809 1289525 := bbase (se 5 (by rfl) ⟨60446, by rfl⟩ : syracuseStep 1289525 = 120893) (by norm_num)
theorem B634189 : Blo 562809 634189 := bbase (se 3 (by rfl) ⟨118910, by rfl⟩ : syracuseStep 634189 = 237821) (by norm_num)
theorem B634225 : Blo 562809 634225 := bbase (se 2 (by rfl) ⟨237834, by rfl⟩ : syracuseStep 634225 = 475669) (by norm_num)
theorem B1715573 : Blo 562809 1715573 := bbase (se 5 (by rfl) ⟨80417, by rfl⟩ : syracuseStep 1715573 = 160835) (by norm_num)
theorem B634261 : Blo 562809 634261 := bbase (se 6 (by rfl) ⟨14865, by rfl⟩ : syracuseStep 634261 = 29731) (by norm_num)
theorem B634297 : Blo 562809 634297 := bbase (se 2 (by rfl) ⟨237861, by rfl⟩ : syracuseStep 634297 = 475723) (by norm_num)
theorem B634333 : Blo 562809 634333 := bbase (se 3 (by rfl) ⟨118937, by rfl⟩ : syracuseStep 634333 = 237875) (by norm_num)
theorem B634369 : Blo 562809 634369 := bbase (se 2 (by rfl) ⟨237888, by rfl⟩ : syracuseStep 634369 = 475777) (by norm_num)
theorem B634405 : Blo 562809 634405 := bbase (se 4 (by rfl) ⟨59475, by rfl⟩ : syracuseStep 634405 = 118951) (by norm_num)
theorem B601673 : Blo 562809 601673 := bbase (se 2 (by rfl) ⟨225627, by rfl⟩ : syracuseStep 601673 = 451255) (by norm_num)
theorem B634441 : Blo 562809 634441 := bbase (se 2 (by rfl) ⟨237915, by rfl⟩ : syracuseStep 634441 = 475831) (by norm_num)
theorem B634477 : Blo 562809 634477 := bbase (se 3 (by rfl) ⟨118964, by rfl⟩ : syracuseStep 634477 = 237929) (by norm_num)
theorem B634513 : Blo 562809 634513 := bbase (se 2 (by rfl) ⟨237942, by rfl⟩ : syracuseStep 634513 = 475885) (by norm_num)
theorem B634549 : Blo 562809 634549 := bbase (se 5 (by rfl) ⟨29744, by rfl⟩ : syracuseStep 634549 = 59489) (by norm_num)
theorem B1912517 : Blo 562809 1912517 := bbase (se 4 (by rfl) ⟨179298, by rfl⟩ : syracuseStep 1912517 = 358597) (by norm_num)
theorem B2141909 : Blo 562809 2141909 := bbase (se 7 (by rfl) ⟨25100, by rfl⟩ : syracuseStep 2141909 = 50201) (by norm_num)
theorem B634585 : Blo 562809 634585 := bbase (se 2 (by rfl) ⟨237969, by rfl⟩ : syracuseStep 634585 = 475939) (by norm_num)
theorem B634621 : Blo 562809 634621 := bbase (se 3 (by rfl) ⟨118991, by rfl⟩ : syracuseStep 634621 = 237983) (by norm_num)
theorem B634657 : Blo 562809 634657 := bbase (se 2 (by rfl) ⟨237996, by rfl⟩ : syracuseStep 634657 = 475993) (by norm_num)
theorem B5812021 : Blo 562809 5812021 := bbase (se 5 (by rfl) ⟨272438, by rfl⟩ : syracuseStep 5812021 = 544877) (by norm_num)
theorem B601921 : Blo 562809 601921 := bbase (se 2 (by rfl) ⟨225720, by rfl⟩ : syracuseStep 601921 = 451441) (by norm_num)
theorem B634693 : Blo 562809 634693 := bbase (se 4 (by rfl) ⟨59502, by rfl⟩ : syracuseStep 634693 = 119005) (by norm_num)
theorem B2404181 : Blo 562809 2404181 := bbase (se 9 (by rfl) ⟨7043, by rfl⟩ : syracuseStep 2404181 = 14087) (by norm_num)
theorem B634729 : Blo 562809 634729 := bbase (se 2 (by rfl) ⟨238023, by rfl⟩ : syracuseStep 634729 = 476047) (by norm_num)
theorem B1355629 : Blo 562809 1355629 := bbase (se 3 (by rfl) ⟨254180, by rfl⟩ : syracuseStep 1355629 = 508361) (by norm_num)
theorem B634765 : Blo 562809 634765 := bbase (se 3 (by rfl) ⟨119018, by rfl⟩ : syracuseStep 634765 = 238037) (by norm_num)
theorem B634801 : Blo 562809 634801 := bbase (se 2 (by rfl) ⟨238050, by rfl⟩ : syracuseStep 634801 = 476101) (by norm_num)
theorem B765893 : Blo 562809 765893 := bbase (se 4 (by rfl) ⟨71802, by rfl⟩ : syracuseStep 765893 = 143605) (by norm_num)
theorem B634837 : Blo 562809 634837 := bbase (se 7 (by rfl) ⟨7439, by rfl⟩ : syracuseStep 634837 = 14879) (by norm_num)
theorem B2142197 : Blo 562809 2142197 := bbase (se 5 (by rfl) ⟨100415, by rfl⟩ : syracuseStep 2142197 = 200831) (by norm_num)
theorem B634873 : Blo 562809 634873 := bbase (se 2 (by rfl) ⟨238077, by rfl⟩ : syracuseStep 634873 = 476155) (by norm_num)
theorem B634909 : Blo 562809 634909 := bbase (se 3 (by rfl) ⟨119045, by rfl⟩ : syracuseStep 634909 = 238091) (by norm_num)
theorem B1290293 : Blo 562809 1290293 := bbase (se 5 (by rfl) ⟨60482, by rfl⟩ : syracuseStep 1290293 = 120965) (by norm_num)
theorem B634945 : Blo 562809 634945 := bbase (se 2 (by rfl) ⟨238104, by rfl⟩ : syracuseStep 634945 = 476209) (by norm_num)
theorem B634981 : Blo 562809 634981 := bbase (se 4 (by rfl) ⟨59529, by rfl⟩ : syracuseStep 634981 = 119059) (by norm_num)
theorem B1912949 : Blo 562809 1912949 := bbase (se 5 (by rfl) ⟨89669, by rfl⟩ : syracuseStep 1912949 = 179339) (by norm_num)
theorem B635017 : Blo 562809 635017 := bbase (se 2 (by rfl) ⟨238131, by rfl⟩ : syracuseStep 635017 = 476263) (by norm_num)
theorem B635053 : Blo 562809 635053 := bbase (se 3 (by rfl) ⟨119072, by rfl⟩ : syracuseStep 635053 = 238145) (by norm_num)
theorem B635089 : Blo 562809 635089 := bbase (se 2 (by rfl) ⟨238158, by rfl⟩ : syracuseStep 635089 = 476317) (by norm_num)
theorem B635125 : Blo 562809 635125 := bbase (se 5 (by rfl) ⟨29771, by rfl⟩ : syracuseStep 635125 = 59543) (by norm_num)
theorem B2863349 : Blo 562809 2863349 := bbase (se 5 (by rfl) ⟨134219, by rfl⟩ : syracuseStep 2863349 = 268439) (by norm_num)
theorem B602365 : Blo 562809 602365 := bbase (se 3 (by rfl) ⟨112943, by rfl⟩ : syracuseStep 602365 = 225887) (by norm_num)
theorem B635161 : Blo 562809 635161 := bbase (se 2 (by rfl) ⟨238185, by rfl⟩ : syracuseStep 635161 = 476371) (by norm_num)
theorem B2896181 : Blo 562809 2896181 := bbase (se 5 (by rfl) ⟨135758, by rfl⟩ : syracuseStep 2896181 = 271517) (by norm_num)
theorem B602425 : Blo 562809 602425 := bbase (se 2 (by rfl) ⟨225909, by rfl⟩ : syracuseStep 602425 = 451819) (by norm_num)
theorem B635197 : Blo 562809 635197 := bbase (se 3 (by rfl) ⟨119099, by rfl⟩ : syracuseStep 635197 = 238199) (by norm_num)
theorem B635233 : Blo 562809 635233 := bbase (se 2 (by rfl) ⟨238212, by rfl⟩ : syracuseStep 635233 = 476425) (by norm_num)
theorem B2568581 : Blo 562809 2568581 := bbase (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) (by norm_num)
theorem B635269 : Blo 562809 635269 := bbase (se 4 (by rfl) ⟨59556, by rfl⟩ : syracuseStep 635269 = 119113) (by norm_num)
theorem B635305 : Blo 562809 635305 := bbase (se 2 (by rfl) ⟨238239, by rfl⟩ : syracuseStep 635305 = 476479) (by norm_num)
theorem B635341 : Blo 562809 635341 := bbase (se 3 (by rfl) ⟨119126, by rfl⟩ : syracuseStep 635341 = 238253) (by norm_num)
theorem B635377 : Blo 562809 635377 := bbase (se 2 (by rfl) ⟨238266, by rfl⟩ : syracuseStep 635377 = 476533) (by norm_num)
theorem B635413 : Blo 562809 635413 := bbase (se 6 (by rfl) ⟨14892, by rfl⟩ : syracuseStep 635413 = 29785) (by norm_num)
theorem B635449 : Blo 562809 635449 := bbase (se 2 (by rfl) ⟨238293, by rfl⟩ : syracuseStep 635449 = 476587) (by norm_num)
theorem B635485 : Blo 562809 635485 := bbase (se 3 (by rfl) ⟨119153, by rfl⟩ : syracuseStep 635485 = 238307) (by norm_num)
theorem B602741 : Blo 562809 602741 := bbase (se 5 (by rfl) ⟨28253, by rfl⟩ : syracuseStep 602741 = 56507) (by norm_num)
theorem B635521 : Blo 562809 635521 := bbase (se 2 (by rfl) ⟨238320, by rfl⟩ : syracuseStep 635521 = 476641) (by norm_num)
theorem B635557 : Blo 562809 635557 := bbase (se 4 (by rfl) ⟨59583, by rfl⟩ : syracuseStep 635557 = 119167) (by norm_num)
theorem B635593 : Blo 562809 635593 := bbase (se 2 (by rfl) ⟨238347, by rfl⟩ : syracuseStep 635593 = 476695) (by norm_num)
theorem B635629 : Blo 562809 635629 := bbase (se 3 (by rfl) ⟨119180, by rfl⟩ : syracuseStep 635629 = 238361) (by norm_num)
theorem B635665 : Blo 562809 635665 := bbase (se 2 (by rfl) ⟨238374, by rfl⟩ : syracuseStep 635665 = 476749) (by norm_num)
theorem B635701 : Blo 562809 635701 := bbase (se 5 (by rfl) ⟨29798, by rfl⟩ : syracuseStep 635701 = 59597) (by norm_num)
theorem B635737 : Blo 562809 635737 := bbase (se 2 (by rfl) ⟨238401, by rfl⟩ : syracuseStep 635737 = 476803) (by norm_num)
theorem B635773 : Blo 562809 635773 := bbase (se 3 (by rfl) ⟨119207, by rfl⟩ : syracuseStep 635773 = 238415) (by norm_num)
theorem B635809 : Blo 562809 635809 := bbase (se 2 (by rfl) ⟨238428, by rfl⟩ : syracuseStep 635809 = 476857) (by norm_num)
theorem B635845 : Blo 562809 635845 := bbase (se 4 (by rfl) ⟨59610, by rfl⟩ : syracuseStep 635845 = 119221) (by norm_num)
theorem B635881 : Blo 562809 635881 := bbase (se 2 (by rfl) ⟨238455, by rfl⟩ : syracuseStep 635881 = 476911) (by norm_num)
theorem B635917 : Blo 562809 635917 := bbase (se 3 (by rfl) ⟨119234, by rfl⟩ : syracuseStep 635917 = 238469) (by norm_num)
theorem B1356821 : Blo 562809 1356821 := bbase (se 6 (by rfl) ⟨31800, by rfl⟩ : syracuseStep 1356821 = 63601) (by norm_num)
theorem B603185 : Blo 562809 603185 := bbase (se 2 (by rfl) ⟨226194, by rfl⟩ : syracuseStep 603185 = 452389) (by norm_num)
theorem B635953 : Blo 562809 635953 := bbase (se 2 (by rfl) ⟨238482, by rfl⟩ : syracuseStep 635953 = 476965) (by norm_num)
theorem B1815605 : Blo 562809 1815605 := bbase (se 5 (by rfl) ⟨85106, by rfl⟩ : syracuseStep 1815605 = 170213) (by norm_num)
theorem B635989 : Blo 562809 635989 := bbase (se 8 (by rfl) ⟨3726, by rfl⟩ : syracuseStep 635989 = 7453) (by norm_num)
theorem B603245 : Blo 562809 603245 := bbase (se 3 (by rfl) ⟨113108, by rfl⟩ : syracuseStep 603245 = 226217) (by norm_num)
theorem B636025 : Blo 562809 636025 := bbase (se 2 (by rfl) ⟨238509, by rfl⟩ : syracuseStep 636025 = 477019) (by norm_num)
theorem B2143381 : Blo 562809 2143381 := bbase (se 6 (by rfl) ⟨50235, by rfl⟩ : syracuseStep 2143381 = 100471) (by norm_num)
theorem B636061 : Blo 562809 636061 := bbase (se 3 (by rfl) ⟨119261, by rfl⟩ : syracuseStep 636061 = 238523) (by norm_num)
theorem B636097 : Blo 562809 636097 := bbase (se 2 (by rfl) ⟨238536, by rfl⟩ : syracuseStep 636097 = 477073) (by norm_num)
theorem B1357013 : Blo 562809 1357013 := bbase (se 7 (by rfl) ⟨15902, by rfl⟩ : syracuseStep 1357013 = 31805) (by norm_num)
theorem B636133 : Blo 562809 636133 := bbase (se 4 (by rfl) ⟨59637, by rfl⟩ : syracuseStep 636133 = 119275) (by norm_num)
theorem B570601 : Blo 562809 570601 := bbase (se 2 (by rfl) ⟨213975, by rfl⟩ : syracuseStep 570601 = 427951) (by norm_num)
theorem B603373 : Blo 562809 603373 := bbase (se 3 (by rfl) ⟨113132, by rfl⟩ : syracuseStep 603373 = 226265) (by norm_num)
theorem B636169 : Blo 562809 636169 := bbase (se 2 (by rfl) ⟨238563, by rfl⟩ : syracuseStep 636169 = 477127) (by norm_num)
theorem B636205 : Blo 562809 636205 := bbase (se 3 (by rfl) ⟨119288, by rfl⟩ : syracuseStep 636205 = 238577) (by norm_num)
theorem B636241 : Blo 562809 636241 := bbase (se 2 (by rfl) ⟨238590, by rfl⟩ : syracuseStep 636241 = 477181) (by norm_num)
theorem B636277 : Blo 562809 636277 := bbase (se 5 (by rfl) ⟨29825, by rfl⟩ : syracuseStep 636277 = 59651) (by norm_num)
theorem B636313 : Blo 562809 636313 := bbase (se 2 (by rfl) ⟨238617, by rfl⟩ : syracuseStep 636313 = 477235) (by norm_num)
theorem B2602405 : Blo 562809 2602405 := bbase (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) (by norm_num)
theorem B636349 : Blo 562809 636349 := bbase (se 3 (by rfl) ⟨119315, by rfl⟩ : syracuseStep 636349 = 238631) (by norm_num)
theorem B2143685 : Blo 562809 2143685 := bbase (se 4 (by rfl) ⟨200970, by rfl⟩ : syracuseStep 2143685 = 401941) (by norm_num)
theorem B636385 : Blo 562809 636385 := bbase (se 2 (by rfl) ⟨238644, by rfl⟩ : syracuseStep 636385 = 477289) (by norm_num)
theorem B636421 : Blo 562809 636421 := bbase (se 4 (by rfl) ⟨59664, by rfl⟩ : syracuseStep 636421 = 119329) (by norm_num)
theorem B2864645 : Blo 562809 2864645 := bbase (se 4 (by rfl) ⟨268560, by rfl⟩ : syracuseStep 2864645 = 537121) (by norm_num)
theorem B636457 : Blo 562809 636457 := bbase (se 2 (by rfl) ⟨238671, by rfl⟩ : syracuseStep 636457 = 477343) (by norm_num)
theorem B636493 : Blo 562809 636493 := bbase (se 3 (by rfl) ⟨119342, by rfl⟩ : syracuseStep 636493 = 238685) (by norm_num)
theorem B636529 : Blo 562809 636529 := bbase (se 2 (by rfl) ⟨238698, by rfl⟩ : syracuseStep 636529 = 477397) (by norm_num)
theorem B636565 : Blo 562809 636565 := bbase (se 6 (by rfl) ⟨14919, by rfl⟩ : syracuseStep 636565 = 29839) (by norm_num)
theorem B603817 : Blo 562809 603817 := bbase (se 2 (by rfl) ⟨226431, by rfl⟩ : syracuseStep 603817 = 452863) (by norm_num)
theorem B636601 : Blo 562809 636601 := bbase (se 2 (by rfl) ⟨238725, by rfl⟩ : syracuseStep 636601 = 477451) (by norm_num)
theorem B1717957 : Blo 562809 1717957 := bbase (se 4 (by rfl) ⟨161058, by rfl⟩ : syracuseStep 1717957 = 322117) (by norm_num)
theorem B636637 : Blo 562809 636637 := bbase (se 3 (by rfl) ⟨119369, by rfl⟩ : syracuseStep 636637 = 238739) (by norm_num)
theorem B636673 : Blo 562809 636673 := bbase (se 2 (by rfl) ⟨238752, by rfl⟩ : syracuseStep 636673 = 477505) (by norm_num)
theorem B603937 : Blo 562809 603937 := bbase (se 2 (by rfl) ⟨226476, by rfl⟩ : syracuseStep 603937 = 452953) (by norm_num)
theorem B636709 : Blo 562809 636709 := bbase (se 4 (by rfl) ⟨59691, by rfl⟩ : syracuseStep 636709 = 119383) (by norm_num)
theorem B3094325 : Blo 562809 3094325 := bbase (se 5 (by rfl) ⟨145046, by rfl⟩ : syracuseStep 3094325 = 290093) (by norm_num)
theorem B636745 : Blo 562809 636745 := bbase (se 2 (by rfl) ⟨238779, by rfl⟩ : syracuseStep 636745 = 477559) (by norm_num)
theorem B636781 : Blo 562809 636781 := bbase (se 3 (by rfl) ⟨119396, by rfl⟩ : syracuseStep 636781 = 238793) (by norm_num)
theorem B636817 : Blo 562809 636817 := bbase (se 2 (by rfl) ⟨238806, by rfl⟩ : syracuseStep 636817 = 477613) (by norm_num)
theorem B636853 : Blo 562809 636853 := bbase (se 5 (by rfl) ⟨29852, by rfl⟩ : syracuseStep 636853 = 59705) (by norm_num)
theorem B636889 : Blo 562809 636889 := bbase (se 2 (by rfl) ⟨238833, by rfl⟩ : syracuseStep 636889 = 477667) (by norm_num)
theorem B636925 : Blo 562809 636925 := bbase (se 3 (by rfl) ⟨119423, by rfl⟩ : syracuseStep 636925 = 238847) (by norm_num)
theorem B604189 : Blo 562809 604189 := bbase (se 3 (by rfl) ⟨113285, by rfl⟩ : syracuseStep 604189 = 226571) (by norm_num)
theorem B604193 : Blo 562809 604193 := bbase (se 2 (by rfl) ⟨226572, by rfl⟩ : syracuseStep 604193 = 453145) (by norm_num)
theorem B636961 : Blo 562809 636961 := bbase (se 2 (by rfl) ⟨238860, by rfl⟩ : syracuseStep 636961 = 477721) (by norm_num)
theorem B636997 : Blo 562809 636997 := bbase (se 4 (by rfl) ⟨59718, by rfl⟩ : syracuseStep 636997 = 119437) (by norm_num)
theorem B637033 : Blo 562809 637033 := bbase (se 2 (by rfl) ⟨238887, by rfl⟩ : syracuseStep 637033 = 477775) (by norm_num)
theorem B637069 : Blo 562809 637069 := bbase (se 3 (by rfl) ⟨119450, by rfl⟩ : syracuseStep 637069 = 238901) (by norm_num)
theorem B637105 : Blo 562809 637105 := bbase (se 2 (by rfl) ⟨238914, by rfl⟩ : syracuseStep 637105 = 477829) (by norm_num)
theorem B637141 : Blo 562809 637141 := bbase (se 7 (by rfl) ⟨7466, by rfl⟩ : syracuseStep 637141 = 14933) (by norm_num)
theorem B637177 : Blo 562809 637177 := bbase (se 2 (by rfl) ⟨238941, by rfl⟩ : syracuseStep 637177 = 477883) (by norm_num)
theorem B637213 : Blo 562809 637213 := bbase (se 3 (by rfl) ⟨119477, by rfl⟩ : syracuseStep 637213 = 238955) (by norm_num)
theorem B637249 : Blo 562809 637249 := bbase (se 2 (by rfl) ⟨238968, by rfl⟩ : syracuseStep 637249 = 477937) (by norm_num)
theorem B637285 : Blo 562809 637285 := bbase (se 4 (by rfl) ⟨59745, by rfl⟩ : syracuseStep 637285 = 119491) (by norm_num)
theorem B637321 : Blo 562809 637321 := bbase (se 2 (by rfl) ⟨238995, by rfl⟩ : syracuseStep 637321 = 477991) (by norm_num)
theorem B637357 : Blo 562809 637357 := bbase (se 3 (by rfl) ⟨119504, by rfl⟩ : syracuseStep 637357 = 239009) (by norm_num)
theorem B637393 : Blo 562809 637393 := bbase (se 2 (by rfl) ⟨239022, by rfl⟩ : syracuseStep 637393 = 478045) (by norm_num)
theorem B637429 : Blo 562809 637429 := bbase (se 5 (by rfl) ⟨29879, by rfl⟩ : syracuseStep 637429 = 59759) (by norm_num)
theorem B637465 : Blo 562809 637465 := bbase (se 2 (by rfl) ⟨239049, by rfl⟩ : syracuseStep 637465 = 478099) (by norm_num)
theorem B637501 : Blo 562809 637501 := bbase (se 3 (by rfl) ⟨119531, by rfl⟩ : syracuseStep 637501 = 239063) (by norm_num)
theorem B604757 : Blo 562809 604757 := bbase (se 8 (by rfl) ⟨3543, by rfl⟩ : syracuseStep 604757 = 7087) (by norm_num)
theorem B637537 : Blo 562809 637537 := bbase (se 2 (by rfl) ⟨239076, by rfl⟩ : syracuseStep 637537 = 478153) (by norm_num)
theorem B637573 : Blo 562809 637573 := bbase (se 4 (by rfl) ⟨59772, by rfl⟩ : syracuseStep 637573 = 119545) (by norm_num)
theorem B637609 : Blo 562809 637609 := bbase (se 2 (by rfl) ⟨239103, by rfl⟩ : syracuseStep 637609 = 478207) (by norm_num)
theorem B572081 : Blo 562809 572081 := bbase (se 2 (by rfl) ⟨214530, by rfl⟩ : syracuseStep 572081 = 429061) (by norm_num)
theorem B1522357 : Blo 562809 1522357 := bbase (se 5 (by rfl) ⟨71360, by rfl⟩ : syracuseStep 1522357 = 142721) (by norm_num)
theorem B637645 : Blo 562809 637645 := bbase (se 3 (by rfl) ⟨119558, by rfl⟩ : syracuseStep 637645 = 239117) (by norm_num)
theorem B572117 : Blo 562809 572117 := bbase (se 7 (by rfl) ⟨6704, by rfl⟩ : syracuseStep 572117 = 13409) (by norm_num)
theorem B604945 : Blo 562809 604945 := bbase (se 2 (by rfl) ⟨226854, by rfl⟩ : syracuseStep 604945 = 453709) (by norm_num)
theorem B2865941 : Blo 562809 2865941 := bbase (se 6 (by rfl) ⟨67170, by rfl⟩ : syracuseStep 2865941 = 134341) (by norm_num)
theorem B801581 : Blo 562809 801581 := bbase (se 3 (by rfl) ⟨150296, by rfl⟩ : syracuseStep 801581 = 300593) (by norm_num)
theorem B4078421 : Blo 562809 4078421 := bbase (se 9 (by rfl) ⟨11948, by rfl⟩ : syracuseStep 4078421 = 23897) (by norm_num)
theorem B572341 : Blo 562809 572341 := bbase (se 5 (by rfl) ⟨26828, by rfl⟩ : syracuseStep 572341 = 53657) (by norm_num)
theorem B1391573 : Blo 562809 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B572441 : Blo 562809 572441 := bbase (se 2 (by rfl) ⟨214665, by rfl⟩ : syracuseStep 572441 = 429331) (by norm_num)
theorem B2407477 : Blo 562809 2407477 := bbase (se 5 (by rfl) ⟨112850, by rfl⟩ : syracuseStep 2407477 = 225701) (by norm_num)
theorem B736337 : Blo 562809 736337 := bbase (se 2 (by rfl) ⟨276126, by rfl⟩ : syracuseStep 736337 = 552253) (by norm_num)
theorem B15416405 : Blo 562809 15416405 := bbase (se 8 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 15416405 = 180661) (by norm_num)
theorem B1424749 : Blo 562809 1424749 := bbase (se 3 (by rfl) ⟨267140, by rfl⟩ : syracuseStep 1424749 = 534281) (by norm_num)
theorem B1359301 : Blo 562809 1359301 := bbase (se 4 (by rfl) ⟨127434, by rfl⟩ : syracuseStep 1359301 = 254869) (by norm_num)
theorem B1424861 : Blo 562809 1424861 := bbase (se 3 (by rfl) ⟨267161, by rfl⟩ : syracuseStep 1424861 = 534323) (by norm_num)
theorem B2145797 : Blo 562809 2145797 := bbase (se 4 (by rfl) ⟨201168, by rfl⟩ : syracuseStep 2145797 = 402337) (by norm_num)
theorem B802333 : Blo 562809 802333 := bbase (se 3 (by rfl) ⟨150437, by rfl⟩ : syracuseStep 802333 = 300875) (by norm_num)
theorem B966269 : Blo 562809 966269 := bbase (se 3 (by rfl) ⟨181175, by rfl⟩ : syracuseStep 966269 = 362351) (by norm_num)
theorem B1425053 : Blo 562809 1425053 := bbase (se 3 (by rfl) ⟨267197, by rfl⟩ : syracuseStep 1425053 = 534395) (by norm_num)
theorem B2146085 : Blo 562809 2146085 := bbase (se 4 (by rfl) ⟨201195, by rfl⟩ : syracuseStep 2146085 = 402391) (by norm_num)
theorem B7225301 : Blo 562809 7225301 := bbase (se 7 (by rfl) ⟨84671, by rfl⟩ : syracuseStep 7225301 = 169343) (by norm_num)
theorem B1425397 : Blo 562809 1425397 := bbase (se 5 (by rfl) ⟨66815, by rfl⟩ : syracuseStep 1425397 = 133631) (by norm_num)
theorem B5783573 : Blo 562809 5783573 := bbase (se 6 (by rfl) ⟨135552, by rfl⟩ : syracuseStep 5783573 = 271105) (by norm_num)
theorem B2867237 : Blo 562809 2867237 := bbase (se 4 (by rfl) ⟨268803, by rfl⟩ : syracuseStep 2867237 = 537607) (by norm_num)
theorem B1359965 : Blo 562809 1359965 := bbase (se 3 (by rfl) ⟨254993, by rfl⟩ : syracuseStep 1359965 = 509987) (by norm_num)
theorem B1425509 : Blo 562809 1425509 := bbase (se 4 (by rfl) ⟨133641, by rfl⟩ : syracuseStep 1425509 = 267283) (by norm_num)
theorem B1425701 : Blo 562809 1425701 := bbase (se 4 (by rfl) ⟨133659, by rfl⟩ : syracuseStep 1425701 = 267319) (by norm_num)
theorem B803125 : Blo 562809 803125 := bbase (se 5 (by rfl) ⟨37646, by rfl⟩ : syracuseStep 803125 = 75293) (by norm_num)
theorem B7258517 : Blo 562809 7258517 := bbase (se 6 (by rfl) ⟨170121, by rfl⟩ : syracuseStep 7258517 = 340243) (by norm_num)
theorem B1524197 : Blo 562809 1524197 := bbase (se 4 (by rfl) ⟨142893, by rfl⟩ : syracuseStep 1524197 = 285787) (by norm_num)
theorem B5423669 : Blo 562809 5423669 := bbase (se 5 (by rfl) ⟨254234, by rfl⟩ : syracuseStep 5423669 = 508469) (by norm_num)
theorem B1426045 : Blo 562809 1426045 := bbase (se 3 (by rfl) ⟨267383, by rfl⟩ : syracuseStep 1426045 = 534767) (by norm_num)
theorem B803461 : Blo 562809 803461 := bbase (se 4 (by rfl) ⟨75324, by rfl⟩ : syracuseStep 803461 = 150649) (by norm_num)
theorem B1426157 : Blo 562809 1426157 := bbase (se 3 (by rfl) ⟨267404, by rfl⟩ : syracuseStep 1426157 = 534809) (by norm_num)
theorem B803677 : Blo 562809 803677 := bbase (se 3 (by rfl) ⟨150689, by rfl⟩ : syracuseStep 803677 = 301379) (by norm_num)
theorem B1426349 : Blo 562809 1426349 := bbase (se 3 (by rfl) ⟨267440, by rfl⟩ : syracuseStep 1426349 = 534881) (by norm_num)
theorem B2147269 : Blo 562809 2147269 := bbase (se 4 (by rfl) ⟨201306, by rfl⟩ : syracuseStep 2147269 = 402613) (by norm_num)
theorem B967637 : Blo 562809 967637 := bbase (se 7 (by rfl) ⟨11339, by rfl⟩ : syracuseStep 967637 = 22679) (by norm_num)
theorem B902189 : Blo 562809 902189 := bbase (se 3 (by rfl) ⟨169160, by rfl⟩ : syracuseStep 902189 = 338321) (by norm_num)
theorem B574517 : Blo 562809 574517 := bbase (se 5 (by rfl) ⟨26930, by rfl⟩ : syracuseStep 574517 = 53861) (by norm_num)
theorem B804053 : Blo 562809 804053 := bbase (se 7 (by rfl) ⟨9422, by rfl⟩ : syracuseStep 804053 = 18845) (by norm_num)
theorem B2147573 : Blo 562809 2147573 := bbase (se 5 (by rfl) ⟨100667, by rfl⟩ : syracuseStep 2147573 = 201335) (by norm_num)
theorem B1426693 : Blo 562809 1426693 := bbase (se 4 (by rfl) ⟨133752, by rfl⟩ : syracuseStep 1426693 = 267505) (by norm_num)
theorem B1099045 : Blo 562809 1099045 := bbase (se 4 (by rfl) ⟨103035, by rfl⟩ : syracuseStep 1099045 = 206071) (by norm_num)
theorem B2868533 : Blo 562809 2868533 := bbase (se 5 (by rfl) ⟨134462, by rfl⟩ : syracuseStep 2868533 = 268925) (by norm_num)
theorem B1426805 : Blo 562809 1426805 := bbase (se 5 (by rfl) ⟨66881, by rfl⟩ : syracuseStep 1426805 = 133763) (by norm_num)
theorem B1361357 : Blo 562809 1361357 := bbase (se 3 (by rfl) ⟨255254, by rfl⟩ : syracuseStep 1361357 = 510509) (by norm_num)
theorem B1361453 : Blo 562809 1361453 := bbase (se 3 (by rfl) ⟨255272, by rfl⟩ : syracuseStep 1361453 = 510545) (by norm_num)
theorem B1426997 : Blo 562809 1426997 := bbase (se 5 (by rfl) ⟨66890, by rfl⟩ : syracuseStep 1426997 = 133781) (by norm_num)
theorem B1525301 : Blo 562809 1525301 := bbase (se 5 (by rfl) ⟨71498, by rfl⟩ : syracuseStep 1525301 = 142997) (by norm_num)
theorem B1525429 : Blo 562809 1525429 := bbase (se 5 (by rfl) ⟨71504, by rfl⟩ : syracuseStep 1525429 = 143009) (by norm_num)
theorem B1427341 : Blo 562809 1427341 := bbase (se 3 (by rfl) ⟨267626, by rfl⟩ : syracuseStep 1427341 = 535253) (by norm_num)
theorem B903125 : Blo 562809 903125 := bbase (se 7 (by rfl) ⟨10583, by rfl⟩ : syracuseStep 903125 = 21167) (by norm_num)
theorem B2410469 : Blo 562809 2410469 := bbase (se 4 (by rfl) ⟨225981, by rfl⟩ : syracuseStep 2410469 = 451963) (by norm_num)
theorem B1427453 : Blo 562809 1427453 := bbase (se 3 (by rfl) ⟨267647, by rfl⟩ : syracuseStep 1427453 = 535295) (by norm_num)
theorem B1427645 : Blo 562809 1427645 := bbase (se 3 (by rfl) ⟨267683, by rfl⟩ : syracuseStep 1427645 = 535367) (by norm_num)
theorem B1722725 : Blo 562809 1722725 := bbase (se 4 (by rfl) ⟨161505, by rfl⟩ : syracuseStep 1722725 = 323011) (by norm_num)
theorem B1526165 : Blo 562809 1526165 := bbase (se 6 (by rfl) ⟨35769, by rfl⟩ : syracuseStep 1526165 = 71539) (by norm_num)
theorem B1427989 : Blo 562809 1427989 := bbase (se 6 (by rfl) ⟨33468, by rfl⟩ : syracuseStep 1427989 = 66937) (by norm_num)
theorem B903773 : Blo 562809 903773 := bbase (se 3 (by rfl) ⟨169457, by rfl⟩ : syracuseStep 903773 = 338915) (by norm_num)
theorem B2574949 : Blo 562809 2574949 := bbase (se 4 (by rfl) ⟨241401, by rfl⟩ : syracuseStep 2574949 = 482803) (by norm_num)
theorem B805477 : Blo 562809 805477 := bbase (se 4 (by rfl) ⟨75513, by rfl⟩ : syracuseStep 805477 = 151027) (by norm_num)
theorem B1428101 : Blo 562809 1428101 := bbase (se 4 (by rfl) ⟨133884, by rfl⟩ : syracuseStep 1428101 = 267769) (by norm_num)
theorem B1428293 : Blo 562809 1428293 := bbase (se 4 (by rfl) ⟨133902, by rfl⟩ : syracuseStep 1428293 = 267805) (by norm_num)
theorem B1526597 : Blo 562809 1526597 := bbase (se 4 (by rfl) ⟨143118, by rfl⟩ : syracuseStep 1526597 = 286237) (by norm_num)
theorem B641881 : Blo 562809 641881 := bbase (se 2 (by rfl) ⟨240705, by rfl⟩ : syracuseStep 641881 = 481411) (by norm_num)
theorem B871309 : Blo 562809 871309 := bbase (se 3 (by rfl) ⟨163370, by rfl⟩ : syracuseStep 871309 = 326741) (by norm_num)
theorem B2411477 : Blo 562809 2411477 := bbase (se 7 (by rfl) ⟨28259, by rfl⟩ : syracuseStep 2411477 = 56519) (by norm_num)
theorem B1526933 : Blo 562809 1526933 := bbase (se 6 (by rfl) ⟨35787, by rfl⟩ : syracuseStep 1526933 = 71575) (by norm_num)
theorem B1428637 : Blo 562809 1428637 := bbase (se 3 (by rfl) ⟨267869, by rfl⟩ : syracuseStep 1428637 = 535739) (by norm_num)
theorem B806069 : Blo 562809 806069 := bbase (se 5 (by rfl) ⟨37784, by rfl⟩ : syracuseStep 806069 = 75569) (by norm_num)
theorem B1527029 : Blo 562809 1527029 := bbase (se 5 (by rfl) ⟨71579, by rfl⟩ : syracuseStep 1527029 = 143159) (by norm_num)
theorem B806149 : Blo 562809 806149 := bbase (se 4 (by rfl) ⟨75576, by rfl⟩ : syracuseStep 806149 = 151153) (by norm_num)
theorem B1428749 : Blo 562809 1428749 := bbase (se 3 (by rfl) ⟨267890, by rfl⟩ : syracuseStep 1428749 = 535781) (by norm_num)
theorem B2149685 : Blo 562809 2149685 := bbase (se 5 (by rfl) ⟨100766, by rfl⟩ : syracuseStep 2149685 = 201533) (by norm_num)
theorem B806269 : Blo 562809 806269 := bbase (se 3 (by rfl) ⟨151175, by rfl⟩ : syracuseStep 806269 = 302351) (by norm_num)
theorem B1428941 : Blo 562809 1428941 := bbase (se 3 (by rfl) ⟨267926, by rfl⟩ : syracuseStep 1428941 = 535853) (by norm_num)
theorem B806365 : Blo 562809 806365 := bbase (se 3 (by rfl) ⟨151193, by rfl⟩ : syracuseStep 806365 = 302387) (by norm_num)
theorem B642533 : Blo 562809 642533 := bbase (se 4 (by rfl) ⟨60237, by rfl⟩ : syracuseStep 642533 = 120475) (by norm_num)
theorem B609805 : Blo 562809 609805 := bbase (se 3 (by rfl) ⟨114338, by rfl⟩ : syracuseStep 609805 = 228677) (by norm_num)
theorem B5164597 : Blo 562809 5164597 := bbase (se 5 (by rfl) ⟨242090, by rfl⟩ : syracuseStep 5164597 = 484181) (by norm_num)
theorem B904765 : Blo 562809 904765 := bbase (se 3 (by rfl) ⟨169643, by rfl⟩ : syracuseStep 904765 = 339287) (by norm_num)
theorem B2149973 : Blo 562809 2149973 := bbase (se 8 (by rfl) ⟨12597, by rfl⟩ : syracuseStep 2149973 = 25195) (by norm_num)
theorem B1068653 : Blo 562809 1068653 := bbase (se 3 (by rfl) ⟨200372, by rfl⟩ : syracuseStep 1068653 = 400745) (by norm_num)
theorem B1068805 : Blo 562809 1068805 := bbase (se 4 (by rfl) ⟨100200, by rfl⟩ : syracuseStep 1068805 = 200401) (by norm_num)
theorem B642829 : Blo 562809 642829 := bbase (se 3 (by rfl) ⟨120530, by rfl⟩ : syracuseStep 642829 = 241061) (by norm_num)
theorem B1429285 : Blo 562809 1429285 := bbase (se 4 (by rfl) ⟨133995, by rfl⟩ : syracuseStep 1429285 = 267991) (by norm_num)
theorem B13782869 : Blo 562809 13782869 := bbase (se 9 (by rfl) ⟨40379, by rfl⟩ : syracuseStep 13782869 = 80759) (by norm_num)
theorem B1429397 : Blo 562809 1429397 := bbase (se 6 (by rfl) ⟨33501, by rfl⟩ : syracuseStep 1429397 = 67003) (by norm_num)
theorem B6442901 : Blo 562809 6442901 := bbase (se 6 (by rfl) ⟨151005, by rfl⟩ : syracuseStep 6442901 = 302011) (by norm_num)
theorem B806861 : Blo 562809 806861 := bbase (se 3 (by rfl) ⟨151286, by rfl⟩ : syracuseStep 806861 = 302573) (by norm_num)
theorem B905213 : Blo 562809 905213 := bbase (se 3 (by rfl) ⟨169727, by rfl⟩ : syracuseStep 905213 = 339455) (by norm_num)
theorem B1069109 : Blo 562809 1069109 := bbase (se 5 (by rfl) ⟨50114, by rfl⟩ : syracuseStep 1069109 = 100229) (by norm_num)
theorem B1429589 : Blo 562809 1429589 := bbase (se 8 (by rfl) ⟨8376, by rfl⟩ : syracuseStep 1429589 = 16753) (by norm_num)
theorem B905413 : Blo 562809 905413 := bbase (se 4 (by rfl) ⟨84882, by rfl⟩ : syracuseStep 905413 = 169765) (by norm_num)
theorem B1429933 : Blo 562809 1429933 := bbase (se 3 (by rfl) ⟨268112, by rfl⟩ : syracuseStep 1429933 = 536225) (by norm_num)
theorem B905669 : Blo 562809 905669 := bbase (se 4 (by rfl) ⟨84906, by rfl⟩ : syracuseStep 905669 = 169813) (by norm_num)
theorem B1430045 : Blo 562809 1430045 := bbase (se 3 (by rfl) ⟨268133, by rfl⟩ : syracuseStep 1430045 = 536267) (by norm_num)
theorem B2413253 : Blo 562809 2413253 := bbase (se 4 (by rfl) ⟨226242, by rfl⟩ : syracuseStep 2413253 = 452485) (by norm_num)
theorem B1266389 : Blo 562809 1266389 := bbase (se 7 (by rfl) ⟨14840, by rfl⟩ : syracuseStep 1266389 = 29681) (by norm_num)
theorem B1430237 : Blo 562809 1430237 := bbase (se 3 (by rfl) ⟨268169, by rfl⟩ : syracuseStep 1430237 = 536339) (by norm_num)
theorem B2151157 : Blo 562809 2151157 := bbase (se 5 (by rfl) ⟨100835, by rfl⟩ : syracuseStep 2151157 = 201671) (by norm_num)
theorem B1266461 : Blo 562809 1266461 := bbase (se 3 (by rfl) ⟨237461, by rfl⟩ : syracuseStep 1266461 = 474923) (by norm_num)
theorem B1069861 : Blo 562809 1069861 := bbase (se 4 (by rfl) ⟨100299, by rfl⟩ : syracuseStep 1069861 = 200599) (by norm_num)
theorem B4281173 : Blo 562809 4281173 := bbase (se 9 (by rfl) ⟨12542, by rfl⟩ : syracuseStep 4281173 = 25085) (by norm_num)
theorem B1266533 : Blo 562809 1266533 := bbase (se 4 (by rfl) ⟨118737, by rfl⟩ : syracuseStep 1266533 = 237475) (by norm_num)
theorem B3855221 : Blo 562809 3855221 := bbase (se 5 (by rfl) ⟨180713, by rfl⟩ : syracuseStep 3855221 = 361427) (by norm_num)
theorem B676757 : Blo 562809 676757 := bbase (se 6 (by rfl) ⟨15861, by rfl⟩ : syracuseStep 676757 = 31723) (by norm_num)
theorem B1266605 : Blo 562809 1266605 := bbase (se 3 (by rfl) ⟨237488, by rfl⟩ : syracuseStep 1266605 = 474977) (by norm_num)
theorem B1070005 : Blo 562809 1070005 := bbase (se 5 (by rfl) ⟨50156, by rfl⟩ : syracuseStep 1070005 = 100313) (by norm_num)
theorem B1266677 : Blo 562809 1266677 := bbase (se 5 (by rfl) ⟨59375, by rfl⟩ : syracuseStep 1266677 = 118751) (by norm_num)
theorem B676873 : Blo 562809 676873 := bbase (se 2 (by rfl) ⟨253827, by rfl⟩ : syracuseStep 676873 = 507655) (by norm_num)
theorem B2151461 : Blo 562809 2151461 := bbase (se 4 (by rfl) ⟨201699, by rfl⟩ : syracuseStep 2151461 = 403399) (by norm_num)
theorem B1430581 : Blo 562809 1430581 := bbase (se 5 (by rfl) ⟨67058, by rfl⟩ : syracuseStep 1430581 = 134117) (by norm_num)
theorem B1266749 : Blo 562809 1266749 := bbase (se 3 (by rfl) ⟨237515, by rfl⟩ : syracuseStep 1266749 = 475031) (by norm_num)
theorem B676945 : Blo 562809 676945 := bbase (se 2 (by rfl) ⟨253854, by rfl⟩ : syracuseStep 676945 = 507709) (by norm_num)
theorem B1070165 : Blo 562809 1070165 := bbase (se 8 (by rfl) ⟨6270, by rfl⟩ : syracuseStep 1070165 = 12541) (by norm_num)
theorem B1266821 : Blo 562809 1266821 := bbase (se 4 (by rfl) ⟨118764, by rfl⟩ : syracuseStep 1266821 = 237529) (by norm_num)
theorem B1430693 : Blo 562809 1430693 := bbase (se 4 (by rfl) ⟨134127, by rfl⟩ : syracuseStep 1430693 = 268255) (by norm_num)
theorem B677065 : Blo 562809 677065 := bbase (se 2 (by rfl) ⟨253899, by rfl⟩ : syracuseStep 677065 = 507799) (by norm_num)
theorem B1266893 : Blo 562809 1266893 := bbase (se 3 (by rfl) ⟨237542, by rfl⟩ : syracuseStep 1266893 = 475085) (by norm_num)
theorem B1070309 : Blo 562809 1070309 := bbase (se 4 (by rfl) ⟨100341, by rfl⟩ : syracuseStep 1070309 = 200683) (by norm_num)
theorem B1266965 : Blo 562809 1266965 := bbase (se 6 (by rfl) ⟨29694, by rfl⟩ : syracuseStep 1266965 = 59389) (by norm_num)
theorem B1267037 : Blo 562809 1267037 := bbase (se 3 (by rfl) ⟨237569, by rfl⟩ : syracuseStep 1267037 = 475139) (by norm_num)
theorem B1430885 : Blo 562809 1430885 := bbase (se 4 (by rfl) ⟨134145, by rfl⟩ : syracuseStep 1430885 = 268291) (by norm_num)
theorem B1267109 : Blo 562809 1267109 := bbase (se 4 (by rfl) ⟨118791, by rfl⟩ : syracuseStep 1267109 = 237583) (by norm_num)
theorem B1267181 : Blo 562809 1267181 := bbase (se 3 (by rfl) ⟨237596, by rfl⟩ : syracuseStep 1267181 = 475193) (by norm_num)
theorem B1070597 : Blo 562809 1070597 := bbase (se 4 (by rfl) ⟨100368, by rfl⟩ : syracuseStep 1070597 = 200737) (by norm_num)
theorem B644617 : Blo 562809 644617 := bbase (se 2 (by rfl) ⟨241731, by rfl⟩ : syracuseStep 644617 = 483463) (by norm_num)
theorem B906797 : Blo 562809 906797 := bbase (se 3 (by rfl) ⟨170024, by rfl⟩ : syracuseStep 906797 = 340049) (by norm_num)
theorem B1267253 : Blo 562809 1267253 := bbase (se 5 (by rfl) ⟨59402, by rfl⟩ : syracuseStep 1267253 = 118805) (by norm_num)
theorem B677449 : Blo 562809 677449 := bbase (se 2 (by rfl) ⟨254043, by rfl⟩ : syracuseStep 677449 = 508087) (by norm_num)
theorem B1267325 : Blo 562809 1267325 := bbase (se 3 (by rfl) ⟨237623, by rfl⟩ : syracuseStep 1267325 = 475247) (by norm_num)
theorem B1070749 : Blo 562809 1070749 := bbase (se 3 (by rfl) ⟨200765, by rfl⟩ : syracuseStep 1070749 = 401531) (by norm_num)
theorem B1431229 : Blo 562809 1431229 := bbase (se 3 (by rfl) ⟨268355, by rfl⟩ : syracuseStep 1431229 = 536711) (by norm_num)
theorem B1267397 : Blo 562809 1267397 := bbase (se 4 (by rfl) ⟨118818, by rfl⟩ : syracuseStep 1267397 = 237637) (by norm_num)
theorem B1267469 : Blo 562809 1267469 := bbase (se 3 (by rfl) ⟨237650, by rfl⟩ : syracuseStep 1267469 = 475301) (by norm_num)
theorem B1431341 : Blo 562809 1431341 := bbase (se 3 (by rfl) ⟨268376, by rfl⟩ : syracuseStep 1431341 = 536753) (by norm_num)
theorem B1267541 : Blo 562809 1267541 := bbase (se 9 (by rfl) ⟨3713, by rfl⟩ : syracuseStep 1267541 = 7427) (by norm_num)
theorem B1267613 : Blo 562809 1267613 := bbase (se 3 (by rfl) ⟨237677, by rfl⟩ : syracuseStep 1267613 = 475355) (by norm_num)
theorem B2709413 : Blo 562809 2709413 := bbase (se 4 (by rfl) ⟨254007, by rfl⟩ : syracuseStep 2709413 = 508015) (by norm_num)
theorem B1071053 : Blo 562809 1071053 := bbase (se 3 (by rfl) ⟨200822, by rfl⟩ : syracuseStep 1071053 = 401645) (by norm_num)
theorem B2742229 : Blo 562809 2742229 := bbase (se 7 (by rfl) ⟨32135, by rfl⟩ : syracuseStep 2742229 = 64271) (by norm_num)
theorem B1267685 : Blo 562809 1267685 := bbase (se 4 (by rfl) ⟨118845, by rfl⟩ : syracuseStep 1267685 = 237691) (by norm_num)
theorem B1431533 : Blo 562809 1431533 := bbase (se 3 (by rfl) ⟨268412, by rfl⟩ : syracuseStep 1431533 = 536825) (by norm_num)
theorem B743425 : Blo 562809 743425 := bbase (se 2 (by rfl) ⟨278784, by rfl⟩ : syracuseStep 743425 = 557569) (by norm_num)
theorem B1267757 : Blo 562809 1267757 := bbase (se 3 (by rfl) ⟨237704, by rfl⟩ : syracuseStep 1267757 = 475409) (by norm_num)
theorem B907309 : Blo 562809 907309 := bbase (se 3 (by rfl) ⟨170120, by rfl⟩ : syracuseStep 907309 = 340241) (by norm_num)
theorem B1267829 : Blo 562809 1267829 := bbase (se 5 (by rfl) ⟨59429, by rfl⟩ : syracuseStep 1267829 = 118859) (by norm_num)
theorem B2283653 : Blo 562809 2283653 := bbase (se 4 (by rfl) ⟨214092, by rfl⟩ : syracuseStep 2283653 = 428185) (by norm_num)
theorem B1267901 : Blo 562809 1267901 := bbase (se 3 (by rfl) ⟨237731, by rfl⟩ : syracuseStep 1267901 = 475463) (by norm_num)
theorem B678137 : Blo 562809 678137 := bbase (se 2 (by rfl) ⟨254301, by rfl⟩ : syracuseStep 678137 = 508603) (by norm_num)
theorem B1267973 : Blo 562809 1267973 := bbase (se 4 (by rfl) ⟨118872, by rfl⟩ : syracuseStep 1267973 = 237745) (by norm_num)
theorem B1202501 : Blo 562809 1202501 := bbase (se 4 (by rfl) ⟨112734, by rfl⟩ : syracuseStep 1202501 = 225469) (by norm_num)
theorem B1431877 : Blo 562809 1431877 := bbase (se 4 (by rfl) ⟨134238, by rfl⟩ : syracuseStep 1431877 = 268477) (by norm_num)
theorem B1268045 : Blo 562809 1268045 := bbase (se 3 (by rfl) ⟨237758, by rfl⟩ : syracuseStep 1268045 = 475517) (by norm_num)
theorem B18340181 : Blo 562809 18340181 := bbase (se 10 (by rfl) ⟨26865, by rfl⟩ : syracuseStep 18340181 = 53731) (by norm_num)
theorem B2677093 : Blo 562809 2677093 := bbase (se 4 (by rfl) ⟨250977, by rfl⟩ : syracuseStep 2677093 = 501955) (by norm_num)
theorem B1628549 : Blo 562809 1628549 := bbase (se 4 (by rfl) ⟨152676, by rfl⟩ : syracuseStep 1628549 = 305353) (by norm_num)
theorem B612749 : Blo 562809 612749 := bbase (se 3 (by rfl) ⟨114890, by rfl⟩ : syracuseStep 612749 = 229781) (by norm_num)
theorem B1268117 : Blo 562809 1268117 := bbase (se 6 (by rfl) ⟨29721, by rfl⟩ : syracuseStep 1268117 = 59443) (by norm_num)
theorem B3627413 : Blo 562809 3627413 := bbase (se 6 (by rfl) ⟨85017, by rfl⟩ : syracuseStep 3627413 = 170035) (by norm_num)
theorem B1431989 : Blo 562809 1431989 := bbase (se 5 (by rfl) ⟨67124, by rfl⟩ : syracuseStep 1431989 = 134249) (by norm_num)
theorem B1202645 : Blo 562809 1202645 := bbase (se 7 (by rfl) ⟨14093, by rfl⟩ : syracuseStep 1202645 = 28187) (by norm_num)
theorem B1268189 : Blo 562809 1268189 := bbase (se 3 (by rfl) ⟨237785, by rfl⟩ : syracuseStep 1268189 = 475571) (by norm_num)
theorem B1268261 : Blo 562809 1268261 := bbase (se 4 (by rfl) ⟨118899, by rfl⟩ : syracuseStep 1268261 = 237799) (by norm_num)
theorem B907853 : Blo 562809 907853 := bbase (se 3 (by rfl) ⟨170222, by rfl⟩ : syracuseStep 907853 = 340445) (by norm_num)
theorem B1268333 : Blo 562809 1268333 := bbase (se 3 (by rfl) ⟨237812, by rfl⟩ : syracuseStep 1268333 = 475625) (by norm_num)
theorem B1432181 : Blo 562809 1432181 := bbase (se 5 (by rfl) ⟨67133, by rfl⟩ : syracuseStep 1432181 = 134267) (by norm_num)
theorem B1268405 : Blo 562809 1268405 := bbase (se 5 (by rfl) ⟨59456, by rfl⟩ : syracuseStep 1268405 = 118913) (by norm_num)
theorem B1071805 : Blo 562809 1071805 := bbase (se 3 (by rfl) ⟨200963, by rfl⟩ : syracuseStep 1071805 = 401927) (by norm_num)
theorem B1268477 : Blo 562809 1268477 := bbase (se 3 (by rfl) ⟨237839, by rfl⟩ : syracuseStep 1268477 = 475679) (by norm_num)
theorem B1530661 : Blo 562809 1530661 := bbase (se 4 (by rfl) ⟨143499, by rfl⟩ : syracuseStep 1530661 = 286999) (by norm_num)
theorem B1203005 : Blo 562809 1203005 := bbase (se 3 (by rfl) ⟨225563, by rfl⟩ : syracuseStep 1203005 = 451127) (by norm_num)
theorem B1268549 : Blo 562809 1268549 := bbase (se 4 (by rfl) ⟨118926, by rfl⟩ : syracuseStep 1268549 = 237853) (by norm_num)
theorem B1071949 : Blo 562809 1071949 := bbase (se 3 (by rfl) ⟨200990, by rfl⟩ : syracuseStep 1071949 = 401981) (by norm_num)
theorem B678737 : Blo 562809 678737 := bbase (se 2 (by rfl) ⟨254526, by rfl⟩ : syracuseStep 678737 = 509053) (by norm_num)
theorem B1858405 : Blo 562809 1858405 := bbase (se 4 (by rfl) ⟨174225, by rfl⟩ : syracuseStep 1858405 = 348451) (by norm_num)
theorem B1268621 : Blo 562809 1268621 := bbase (se 3 (by rfl) ⟨237866, by rfl⟩ : syracuseStep 1268621 = 475733) (by norm_num)
theorem B1432525 : Blo 562809 1432525 := bbase (se 3 (by rfl) ⟨268598, by rfl⟩ : syracuseStep 1432525 = 537197) (by norm_num)
theorem B1268693 : Blo 562809 1268693 := bbase (se 7 (by rfl) ⟨14867, by rfl⟩ : syracuseStep 1268693 = 29735) (by norm_num)
theorem B1072109 : Blo 562809 1072109 := bbase (se 3 (by rfl) ⟨201020, by rfl⟩ : syracuseStep 1072109 = 402041) (by norm_num)
theorem B5790709 : Blo 562809 5790709 := bbase (se 5 (by rfl) ⟨271439, by rfl⟩ : syracuseStep 5790709 = 542879) (by norm_num)
theorem B1268765 : Blo 562809 1268765 := bbase (se 3 (by rfl) ⟨237893, by rfl⟩ : syracuseStep 1268765 = 475787) (by norm_num)
theorem B1432637 : Blo 562809 1432637 := bbase (se 3 (by rfl) ⟨268619, by rfl⟩ : syracuseStep 1432637 = 537239) (by norm_num)
theorem B1268837 : Blo 562809 1268837 := bbase (se 4 (by rfl) ⟨118953, by rfl⟩ : syracuseStep 1268837 = 237907) (by norm_num)
theorem B1072253 : Blo 562809 1072253 := bbase (se 3 (by rfl) ⟨201047, by rfl⟩ : syracuseStep 1072253 = 402095) (by norm_num)
theorem B679045 : Blo 562809 679045 := bbase (se 4 (by rfl) ⟨63660, by rfl⟩ : syracuseStep 679045 = 127321) (by norm_num)
theorem B1268909 : Blo 562809 1268909 := bbase (se 3 (by rfl) ⟨237920, by rfl⟩ : syracuseStep 1268909 = 475841) (by norm_num)
theorem B679141 : Blo 562809 679141 := bbase (se 4 (by rfl) ⟨63669, by rfl⟩ : syracuseStep 679141 = 127339) (by norm_num)
theorem B1268981 : Blo 562809 1268981 := bbase (se 5 (by rfl) ⟨59483, by rfl⟩ : syracuseStep 1268981 = 118967) (by norm_num)
theorem B580853 : Blo 562809 580853 := bbase (se 5 (by rfl) ⟨27227, by rfl⟩ : syracuseStep 580853 = 54455) (by norm_num)
theorem B1432829 : Blo 562809 1432829 := bbase (se 3 (by rfl) ⟨268655, by rfl⟩ : syracuseStep 1432829 = 537311) (by norm_num)
theorem B679189 : Blo 562809 679189 := bbase (se 6 (by rfl) ⟨15918, by rfl⟩ : syracuseStep 679189 = 31837) (by norm_num)
theorem B1269053 : Blo 562809 1269053 := bbase (se 3 (by rfl) ⟨237947, by rfl⟩ : syracuseStep 1269053 = 475895) (by norm_num)
theorem B1269125 : Blo 562809 1269125 := bbase (se 4 (by rfl) ⟨118980, by rfl⟩ : syracuseStep 1269125 = 237961) (by norm_num)
theorem B1072541 : Blo 562809 1072541 := bbase (se 3 (by rfl) ⟨201101, by rfl⟩ : syracuseStep 1072541 = 402203) (by norm_num)
theorem B1269197 : Blo 562809 1269197 := bbase (se 3 (by rfl) ⟨237974, by rfl⟩ : syracuseStep 1269197 = 475949) (by norm_num)
theorem B1269269 : Blo 562809 1269269 := bbase (se 6 (by rfl) ⟨29748, by rfl⟩ : syracuseStep 1269269 = 59497) (by norm_num)
theorem B1072693 : Blo 562809 1072693 := bbase (se 5 (by rfl) ⟨50282, by rfl⟩ : syracuseStep 1072693 = 100565) (by norm_num)
theorem B1433173 : Blo 562809 1433173 := bbase (se 8 (by rfl) ⟨8397, by rfl⟩ : syracuseStep 1433173 = 16795) (by norm_num)
theorem B1269341 : Blo 562809 1269341 := bbase (se 3 (by rfl) ⟨238001, by rfl⟩ : syracuseStep 1269341 = 476003) (by norm_num)
theorem B712309 : Blo 562809 712309 := bbase (se 5 (by rfl) ⟨33389, by rfl⟩ : syracuseStep 712309 = 66779) (by norm_num)
theorem B1269413 : Blo 562809 1269413 := bbase (se 4 (by rfl) ⟨119007, by rfl⟩ : syracuseStep 1269413 = 238015) (by norm_num)
theorem B1203893 : Blo 562809 1203893 := bbase (se 5 (by rfl) ⟨56432, by rfl⟩ : syracuseStep 1203893 = 112865) (by norm_num)
theorem B1433285 : Blo 562809 1433285 := bbase (se 4 (by rfl) ⟨134370, by rfl⟩ : syracuseStep 1433285 = 268741) (by norm_num)
theorem B712405 : Blo 562809 712405 := bbase (se 7 (by rfl) ⟨8348, by rfl⟩ : syracuseStep 712405 = 16697) (by norm_num)
theorem B1269485 : Blo 562809 1269485 := bbase (se 3 (by rfl) ⟨238028, by rfl⟩ : syracuseStep 1269485 = 476057) (by norm_num)
theorem B1269557 : Blo 562809 1269557 := bbase (se 5 (by rfl) ⟨59510, by rfl⟩ : syracuseStep 1269557 = 119021) (by norm_num)
theorem B3923797 : Blo 562809 3923797 := bbase (se 9 (by rfl) ⟨11495, by rfl⟩ : syracuseStep 3923797 = 22991) (by norm_num)
theorem B1072997 : Blo 562809 1072997 := bbase (se 4 (by rfl) ⟨100593, by rfl⟩ : syracuseStep 1072997 = 201187) (by norm_num)
theorem B1269629 : Blo 562809 1269629 := bbase (se 3 (by rfl) ⟨238055, by rfl⟩ : syracuseStep 1269629 = 476111) (by norm_num)
theorem B712577 : Blo 562809 712577 := bbase (se 2 (by rfl) ⟨267216, by rfl⟩ : syracuseStep 712577 = 534433) (by norm_num)
theorem B1433477 : Blo 562809 1433477 := bbase (se 4 (by rfl) ⟨134388, by rfl⟩ : syracuseStep 1433477 = 268777) (by norm_num)
theorem B1204141 : Blo 562809 1204141 := bbase (se 3 (by rfl) ⟨225776, by rfl⟩ : syracuseStep 1204141 = 451553) (by norm_num)
theorem B712633 : Blo 562809 712633 := bbase (se 2 (by rfl) ⟨267237, by rfl⟩ : syracuseStep 712633 = 534475) (by norm_num)
theorem B1269701 : Blo 562809 1269701 := bbase (se 4 (by rfl) ⟨119034, by rfl⟩ : syracuseStep 1269701 = 238069) (by norm_num)
theorem B1269773 : Blo 562809 1269773 := bbase (se 3 (by rfl) ⟨238082, by rfl⟩ : syracuseStep 1269773 = 476165) (by norm_num)
theorem B712729 : Blo 562809 712729 := bbase (se 2 (by rfl) ⟨267273, by rfl⟩ : syracuseStep 712729 = 534547) (by norm_num)
theorem B1269845 : Blo 562809 1269845 := bbase (se 8 (by rfl) ⟨7440, by rfl⟩ : syracuseStep 1269845 = 14881) (by norm_num)
theorem B1269917 : Blo 562809 1269917 := bbase (se 3 (by rfl) ⟨238109, by rfl⟩ : syracuseStep 1269917 = 476219) (by norm_num)
theorem B712901 : Blo 562809 712901 := bbase (se 4 (by rfl) ⟨66834, by rfl⟩ : syracuseStep 712901 = 133669) (by norm_num)
theorem B1433821 : Blo 562809 1433821 := bbase (se 3 (by rfl) ⟨268841, by rfl⟩ : syracuseStep 1433821 = 537683) (by norm_num)
theorem B1269989 : Blo 562809 1269989 := bbase (se 4 (by rfl) ⟨119061, by rfl⟩ : syracuseStep 1269989 = 238123) (by norm_num)
theorem B712957 : Blo 562809 712957 := bbase (se 3 (by rfl) ⟨133679, by rfl⟩ : syracuseStep 712957 = 267359) (by norm_num)
theorem B1270061 : Blo 562809 1270061 := bbase (se 3 (by rfl) ⟨238136, by rfl⟩ : syracuseStep 1270061 = 476273) (by norm_num)
theorem B1433933 : Blo 562809 1433933 := bbase (se 3 (by rfl) ⟨268862, by rfl⟩ : syracuseStep 1433933 = 537725) (by norm_num)
theorem B713053 : Blo 562809 713053 := bbase (se 3 (by rfl) ⟨133697, by rfl⟩ : syracuseStep 713053 = 267395) (by norm_num)
theorem B4809077 : Blo 562809 4809077 := bbase (se 5 (by rfl) ⟨225425, by rfl⟩ : syracuseStep 4809077 = 450851) (by norm_num)
theorem B1270133 : Blo 562809 1270133 := bbase (se 5 (by rfl) ⟨59537, by rfl⟩ : syracuseStep 1270133 = 119075) (by norm_num)
theorem B1204645 : Blo 562809 1204645 := bbase (se 4 (by rfl) ⟨112935, by rfl⟩ : syracuseStep 1204645 = 225871) (by norm_num)
theorem B1270205 : Blo 562809 1270205 := bbase (se 3 (by rfl) ⟨238163, by rfl⟩ : syracuseStep 1270205 = 476327) (by norm_num)
theorem B844229 : Blo 562809 844229 := bbase (se 4 (by rfl) ⟨79146, by rfl⟩ : syracuseStep 844229 = 158293) (by norm_num)
theorem B680405 : Blo 562809 680405 := bbase (se 7 (by rfl) ⟨7973, by rfl⟩ : syracuseStep 680405 = 15947) (by norm_num)
theorem B844253 : Blo 562809 844253 := bbase (se 3 (by rfl) ⟨158297, by rfl⟩ : syracuseStep 844253 = 316595) (by norm_num)
theorem B844277 : Blo 562809 844277 := bbase (se 5 (by rfl) ⟨39575, by rfl⟩ : syracuseStep 844277 = 79151) (by norm_num)
theorem B1270277 : Blo 562809 1270277 := bbase (se 4 (by rfl) ⟨119088, by rfl⟩ : syracuseStep 1270277 = 238177) (by norm_num)
theorem B713225 : Blo 562809 713225 := bbase (se 2 (by rfl) ⟨267459, by rfl⟩ : syracuseStep 713225 = 534919) (by norm_num)
theorem B844301 : Blo 562809 844301 := bbase (se 3 (by rfl) ⟨158306, by rfl⟩ : syracuseStep 844301 = 316613) (by norm_num)
theorem B1434125 : Blo 562809 1434125 := bbase (se 3 (by rfl) ⟨268898, by rfl⟩ : syracuseStep 1434125 = 537797) (by norm_num)
theorem B844325 : Blo 562809 844325 := bbase (se 4 (by rfl) ⟨79155, by rfl⟩ : syracuseStep 844325 = 158311) (by norm_num)
theorem B844349 : Blo 562809 844349 := bbase (se 3 (by rfl) ⟨158315, by rfl⟩ : syracuseStep 844349 = 316631) (by norm_num)
theorem B713281 : Blo 562809 713281 := bbase (se 2 (by rfl) ⟨267480, by rfl⟩ : syracuseStep 713281 = 534961) (by norm_num)
theorem B1270349 : Blo 562809 1270349 := bbase (se 3 (by rfl) ⟨238190, by rfl⟩ : syracuseStep 1270349 = 476381) (by norm_num)
theorem B844373 : Blo 562809 844373 := bbase (se 8 (by rfl) ⟨4947, by rfl⟩ : syracuseStep 844373 = 9895) (by norm_num)
theorem B1073749 : Blo 562809 1073749 := bbase (se 8 (by rfl) ⟨6291, by rfl⟩ : syracuseStep 1073749 = 12583) (by norm_num)
theorem B844397 : Blo 562809 844397 := bbase (se 3 (by rfl) ⟨158324, by rfl⟩ : syracuseStep 844397 = 316649) (by norm_num)
theorem B680573 : Blo 562809 680573 := bbase (se 3 (by rfl) ⟨127607, by rfl⟩ : syracuseStep 680573 = 255215) (by norm_num)
theorem B844421 : Blo 562809 844421 := bbase (se 4 (by rfl) ⟨79164, by rfl⟩ : syracuseStep 844421 = 158329) (by norm_num)
theorem B1270421 : Blo 562809 1270421 := bbase (se 6 (by rfl) ⟨29775, by rfl⟩ : syracuseStep 1270421 = 59551) (by norm_num)
theorem B844445 : Blo 562809 844445 := bbase (se 3 (by rfl) ⟨158333, by rfl⟩ : syracuseStep 844445 = 316667) (by norm_num)
theorem B713377 : Blo 562809 713377 := bbase (se 2 (by rfl) ⟨267516, by rfl⟩ : syracuseStep 713377 = 535033) (by norm_num)
theorem B844469 : Blo 562809 844469 := bbase (se 5 (by rfl) ⟨39584, by rfl⟩ : syracuseStep 844469 = 79169) (by norm_num)
theorem B844493 : Blo 562809 844493 := bbase (se 3 (by rfl) ⟨158342, by rfl⟩ : syracuseStep 844493 = 316685) (by norm_num)
theorem B1270493 : Blo 562809 1270493 := bbase (se 3 (by rfl) ⟨238217, by rfl⟩ : syracuseStep 1270493 = 476435) (by norm_num)
theorem B844517 : Blo 562809 844517 := bbase (se 4 (by rfl) ⟨79173, by rfl⟩ : syracuseStep 844517 = 158347) (by norm_num)
theorem B1073893 : Blo 562809 1073893 := bbase (se 4 (by rfl) ⟨100677, by rfl⟩ : syracuseStep 1073893 = 201355) (by norm_num)
theorem B844541 : Blo 562809 844541 := bbase (se 3 (by rfl) ⟨158351, by rfl⟩ : syracuseStep 844541 = 316703) (by norm_num)
theorem B844565 : Blo 562809 844565 := bbase (se 6 (by rfl) ⟨19794, by rfl⟩ : syracuseStep 844565 = 39589) (by norm_num)
theorem B1270565 : Blo 562809 1270565 := bbase (se 4 (by rfl) ⟨119115, by rfl⟩ : syracuseStep 1270565 = 238231) (by norm_num)
theorem B844589 : Blo 562809 844589 := bbase (se 3 (by rfl) ⟨158360, by rfl⟩ : syracuseStep 844589 = 316721) (by norm_num)
theorem B844613 : Blo 562809 844613 := bbase (se 4 (by rfl) ⟨79182, by rfl⟩ : syracuseStep 844613 = 158365) (by norm_num)
theorem B713549 : Blo 562809 713549 := bbase (se 3 (by rfl) ⟨133790, by rfl⟩ : syracuseStep 713549 = 267581) (by norm_num)
theorem B844637 : Blo 562809 844637 := bbase (se 3 (by rfl) ⟨158369, by rfl⟩ : syracuseStep 844637 = 316739) (by norm_num)
theorem B1434469 : Blo 562809 1434469 := bbase (se 4 (by rfl) ⟨134481, by rfl⟩ : syracuseStep 1434469 = 268963) (by norm_num)
theorem B1270637 : Blo 562809 1270637 := bbase (se 3 (by rfl) ⟨238244, by rfl⟩ : syracuseStep 1270637 = 476489) (by norm_num)
theorem B844661 : Blo 562809 844661 := bbase (se 5 (by rfl) ⟨39593, by rfl⟩ : syracuseStep 844661 = 79187) (by norm_num)
theorem B2417525 : Blo 562809 2417525 := bbase (se 5 (by rfl) ⟨113321, by rfl⟩ : syracuseStep 2417525 = 226643) (by norm_num)
theorem B713605 : Blo 562809 713605 := bbase (se 4 (by rfl) ⟨66900, by rfl⟩ : syracuseStep 713605 = 133801) (by norm_num)
theorem B1074053 : Blo 562809 1074053 := bbase (se 4 (by rfl) ⟨100692, by rfl⟩ : syracuseStep 1074053 = 201385) (by norm_num)
theorem B844685 : Blo 562809 844685 := bbase (se 3 (by rfl) ⟨158378, by rfl⟩ : syracuseStep 844685 = 316757) (by norm_num)
theorem B844709 : Blo 562809 844709 := bbase (se 4 (by rfl) ⟨79191, by rfl⟩ : syracuseStep 844709 = 158383) (by norm_num)
theorem B680881 : Blo 562809 680881 := bbase (se 2 (by rfl) ⟨255330, by rfl⟩ : syracuseStep 680881 = 510661) (by norm_num)
theorem B1270709 : Blo 562809 1270709 := bbase (se 5 (by rfl) ⟨59564, by rfl⟩ : syracuseStep 1270709 = 119129) (by norm_num)
theorem B844733 : Blo 562809 844733 := bbase (se 3 (by rfl) ⟨158387, by rfl⟩ : syracuseStep 844733 = 316775) (by norm_num)
theorem B844757 : Blo 562809 844757 := bbase (se 7 (by rfl) ⟨9899, by rfl⟩ : syracuseStep 844757 = 19799) (by norm_num)
theorem B1434581 : Blo 562809 1434581 := bbase (se 7 (by rfl) ⟨16811, by rfl⟩ : syracuseStep 1434581 = 33623) (by norm_num)
theorem B713701 : Blo 562809 713701 := bbase (se 4 (by rfl) ⟨66909, by rfl⟩ : syracuseStep 713701 = 133819) (by norm_num)
theorem B844781 : Blo 562809 844781 := bbase (se 3 (by rfl) ⟨158396, by rfl⟩ : syracuseStep 844781 = 316793) (by norm_num)
theorem B1270781 : Blo 562809 1270781 := bbase (se 3 (by rfl) ⟨238271, by rfl⟩ : syracuseStep 1270781 = 476543) (by norm_num)
theorem B844805 : Blo 562809 844805 := bbase (se 4 (by rfl) ⟨79200, by rfl⟩ : syracuseStep 844805 = 158401) (by norm_num)
theorem B1074197 : Blo 562809 1074197 := bbase (se 6 (by rfl) ⟨25176, by rfl⟩ : syracuseStep 1074197 = 50353) (by norm_num)
theorem B844829 : Blo 562809 844829 := bbase (se 3 (by rfl) ⟨158405, by rfl⟩ : syracuseStep 844829 = 316811) (by norm_num)
theorem B844853 : Blo 562809 844853 := bbase (se 5 (by rfl) ⟨39602, by rfl⟩ : syracuseStep 844853 = 79205) (by norm_num)
theorem B1270853 : Blo 562809 1270853 := bbase (se 4 (by rfl) ⟨119142, by rfl⟩ : syracuseStep 1270853 = 238285) (by norm_num)
theorem B844877 : Blo 562809 844877 := bbase (se 3 (by rfl) ⟨158414, by rfl⟩ : syracuseStep 844877 = 316829) (by norm_num)
theorem B844901 : Blo 562809 844901 := bbase (se 4 (by rfl) ⟨79209, by rfl⟩ : syracuseStep 844901 = 158419) (by norm_num)
theorem B844925 : Blo 562809 844925 := bbase (se 3 (by rfl) ⟨158423, by rfl⟩ : syracuseStep 844925 = 316847) (by norm_num)
theorem B1270925 : Blo 562809 1270925 := bbase (se 3 (by rfl) ⟨238298, by rfl⟩ : syracuseStep 1270925 = 476597) (by norm_num)
theorem B713873 : Blo 562809 713873 := bbase (se 2 (by rfl) ⟨267702, by rfl⟩ : syracuseStep 713873 = 535405) (by norm_num)
theorem B844949 : Blo 562809 844949 := bbase (se 6 (by rfl) ⟨19803, by rfl⟩ : syracuseStep 844949 = 39607) (by norm_num)
theorem B844973 : Blo 562809 844973 := bbase (se 3 (by rfl) ⟨158432, by rfl⟩ : syracuseStep 844973 = 316865) (by norm_num)
theorem B844997 : Blo 562809 844997 := bbase (se 4 (by rfl) ⟨79218, by rfl⟩ : syracuseStep 844997 = 158437) (by norm_num)
theorem B713929 : Blo 562809 713929 := bbase (se 2 (by rfl) ⟨267723, by rfl⟩ : syracuseStep 713929 = 535447) (by norm_num)
theorem B1270997 : Blo 562809 1270997 := bbase (se 7 (by rfl) ⟨14894, by rfl⟩ : syracuseStep 1270997 = 29789) (by norm_num)
theorem B845021 : Blo 562809 845021 := bbase (se 3 (by rfl) ⟨158441, by rfl⟩ : syracuseStep 845021 = 316883) (by norm_num)
theorem B845045 : Blo 562809 845045 := bbase (se 5 (by rfl) ⟨39611, by rfl⟩ : syracuseStep 845045 = 79223) (by norm_num)
theorem B845069 : Blo 562809 845069 := bbase (se 3 (by rfl) ⟨158450, by rfl⟩ : syracuseStep 845069 = 316901) (by norm_num)
theorem B1205533 : Blo 562809 1205533 := bbase (se 3 (by rfl) ⟨226037, by rfl⟩ : syracuseStep 1205533 = 452075) (by norm_num)
theorem B1271069 : Blo 562809 1271069 := bbase (se 3 (by rfl) ⟨238325, by rfl⟩ : syracuseStep 1271069 = 476651) (by norm_num)
theorem B845093 : Blo 562809 845093 := bbase (se 4 (by rfl) ⟨79227, by rfl⟩ : syracuseStep 845093 = 158455) (by norm_num)
theorem B714025 : Blo 562809 714025 := bbase (se 2 (by rfl) ⟨267759, by rfl⟩ : syracuseStep 714025 = 535519) (by norm_num)
theorem B1074485 : Blo 562809 1074485 := bbase (se 5 (by rfl) ⟨50366, by rfl⟩ : syracuseStep 1074485 = 100733) (by norm_num)
theorem B845117 : Blo 562809 845117 := bbase (se 3 (by rfl) ⟨158459, by rfl⟩ : syracuseStep 845117 = 316919) (by norm_num)
theorem B845141 : Blo 562809 845141 := bbase (se 12 (by rfl) ⟨309, by rfl⟩ : syracuseStep 845141 = 619) (by norm_num)
theorem B1271141 : Blo 562809 1271141 := bbase (se 4 (by rfl) ⟨119169, by rfl⟩ : syracuseStep 1271141 = 238339) (by norm_num)
theorem B845165 : Blo 562809 845165 := bbase (se 3 (by rfl) ⟨158468, by rfl⟩ : syracuseStep 845165 = 316937) (by norm_num)
theorem B845189 : Blo 562809 845189 := bbase (se 4 (by rfl) ⟨79236, by rfl⟩ : syracuseStep 845189 = 158473) (by norm_num)
theorem B845213 : Blo 562809 845213 := bbase (se 3 (by rfl) ⟨158477, by rfl⟩ : syracuseStep 845213 = 316955) (by norm_num)
theorem B1271213 : Blo 562809 1271213 := bbase (se 3 (by rfl) ⟨238352, by rfl⟩ : syracuseStep 1271213 = 476705) (by norm_num)
theorem B845237 : Blo 562809 845237 := bbase (se 5 (by rfl) ⟨39620, by rfl⟩ : syracuseStep 845237 = 79241) (by norm_num)
theorem B845261 : Blo 562809 845261 := bbase (se 3 (by rfl) ⟨158486, by rfl⟩ : syracuseStep 845261 = 316973) (by norm_num)
theorem B1074637 : Blo 562809 1074637 := bbase (se 3 (by rfl) ⟨201494, by rfl⟩ : syracuseStep 1074637 = 402989) (by norm_num)
theorem B714197 : Blo 562809 714197 := bbase (se 7 (by rfl) ⟨8369, by rfl⟩ : syracuseStep 714197 = 16739) (by norm_num)
theorem B1926629 : Blo 562809 1926629 := bbase (se 4 (by rfl) ⟨180621, by rfl⟩ : syracuseStep 1926629 = 361243) (by norm_num)
theorem B845285 : Blo 562809 845285 := bbase (se 4 (by rfl) ⟨79245, by rfl⟩ : syracuseStep 845285 = 158491) (by norm_num)
theorem B1271285 : Blo 562809 1271285 := bbase (se 5 (by rfl) ⟨59591, by rfl⟩ : syracuseStep 1271285 = 119183) (by norm_num)
theorem B845309 : Blo 562809 845309 := bbase (se 3 (by rfl) ⟨158495, by rfl⟩ : syracuseStep 845309 = 316991) (by norm_num)
theorem B714253 : Blo 562809 714253 := bbase (se 3 (by rfl) ⟨133922, by rfl⟩ : syracuseStep 714253 = 267845) (by norm_num)
theorem B845333 : Blo 562809 845333 := bbase (se 6 (by rfl) ⟨19812, by rfl⟩ : syracuseStep 845333 = 39625) (by norm_num)
theorem B845357 : Blo 562809 845357 := bbase (se 3 (by rfl) ⟨158504, by rfl⟩ : syracuseStep 845357 = 317009) (by norm_num)
theorem B1271357 : Blo 562809 1271357 := bbase (se 3 (by rfl) ⟨238379, by rfl⟩ : syracuseStep 1271357 = 476759) (by norm_num)
theorem B845381 : Blo 562809 845381 := bbase (se 4 (by rfl) ⟨79254, by rfl⟩ : syracuseStep 845381 = 158509) (by norm_num)
theorem B845405 : Blo 562809 845405 := bbase (se 3 (by rfl) ⟨158513, by rfl⟩ : syracuseStep 845405 = 317027) (by norm_num)
theorem B714349 : Blo 562809 714349 := bbase (se 3 (by rfl) ⟨133940, by rfl⟩ : syracuseStep 714349 = 267881) (by norm_num)
theorem B845429 : Blo 562809 845429 := bbase (se 5 (by rfl) ⟨39629, by rfl⟩ : syracuseStep 845429 = 79259) (by norm_num)
theorem B1271429 : Blo 562809 1271429 := bbase (se 4 (by rfl) ⟨119196, by rfl⟩ : syracuseStep 1271429 = 238393) (by norm_num)
theorem B845453 : Blo 562809 845453 := bbase (se 3 (by rfl) ⟨158522, by rfl⟩ : syracuseStep 845453 = 317045) (by norm_num)
theorem B845477 : Blo 562809 845477 := bbase (se 4 (by rfl) ⟨79263, by rfl⟩ : syracuseStep 845477 = 158527) (by norm_num)
theorem B845501 : Blo 562809 845501 := bbase (se 3 (by rfl) ⟨158531, by rfl⟩ : syracuseStep 845501 = 317063) (by norm_num)
theorem B1271501 : Blo 562809 1271501 := bbase (se 3 (by rfl) ⟨238406, by rfl⟩ : syracuseStep 1271501 = 476813) (by norm_num)
theorem B845525 : Blo 562809 845525 := bbase (se 7 (by rfl) ⟨9908, by rfl⟩ : syracuseStep 845525 = 19817) (by norm_num)
theorem B845549 : Blo 562809 845549 := bbase (se 3 (by rfl) ⟨158540, by rfl⟩ : syracuseStep 845549 = 317081) (by norm_num)
theorem B2713333 : Blo 562809 2713333 := bbase (se 5 (by rfl) ⟨127187, by rfl⟩ : syracuseStep 2713333 = 254375) (by norm_num)
theorem B1074941 : Blo 562809 1074941 := bbase (se 3 (by rfl) ⟨201551, by rfl⟩ : syracuseStep 1074941 = 403103) (by norm_num)
theorem B845573 : Blo 562809 845573 := bbase (se 4 (by rfl) ⟨79272, by rfl⟩ : syracuseStep 845573 = 158545) (by norm_num)
theorem B1206029 : Blo 562809 1206029 := bbase (se 3 (by rfl) ⟨226130, by rfl⟩ : syracuseStep 1206029 = 452261) (by norm_num)
theorem B1271573 : Blo 562809 1271573 := bbase (se 6 (by rfl) ⟨29802, by rfl⟩ : syracuseStep 1271573 = 59605) (by norm_num)
theorem B714521 : Blo 562809 714521 := bbase (se 2 (by rfl) ⟨267945, by rfl⟩ : syracuseStep 714521 = 535891) (by norm_num)
theorem B845597 : Blo 562809 845597 := bbase (se 3 (by rfl) ⟨158549, by rfl⟩ : syracuseStep 845597 = 317099) (by norm_num)
theorem B812837 : Blo 562809 812837 := bbase (se 4 (by rfl) ⟨76203, by rfl⟩ : syracuseStep 812837 = 152407) (by norm_num)
theorem B845621 : Blo 562809 845621 := bbase (se 5 (by rfl) ⟨39638, by rfl⟩ : syracuseStep 845621 = 79277) (by norm_num)
theorem B845645 : Blo 562809 845645 := bbase (se 3 (by rfl) ⟨158558, by rfl⟩ : syracuseStep 845645 = 317117) (by norm_num)
theorem B714577 : Blo 562809 714577 := bbase (se 2 (by rfl) ⟨267966, by rfl⟩ : syracuseStep 714577 = 535933) (by norm_num)
theorem B1271645 : Blo 562809 1271645 := bbase (se 3 (by rfl) ⟨238433, by rfl⟩ : syracuseStep 1271645 = 476867) (by norm_num)
theorem B845669 : Blo 562809 845669 := bbase (se 4 (by rfl) ⟨79281, by rfl⟩ : syracuseStep 845669 = 158563) (by norm_num)
theorem B845693 : Blo 562809 845693 := bbase (se 3 (by rfl) ⟨158567, by rfl⟩ : syracuseStep 845693 = 317135) (by norm_num)
theorem B845717 : Blo 562809 845717 := bbase (se 6 (by rfl) ⟨19821, by rfl⟩ : syracuseStep 845717 = 39643) (by norm_num)
theorem B1271717 : Blo 562809 1271717 := bbase (se 4 (by rfl) ⟨119223, by rfl⟩ : syracuseStep 1271717 = 238447) (by norm_num)
theorem B845741 : Blo 562809 845741 := bbase (se 3 (by rfl) ⟨158576, by rfl⟩ : syracuseStep 845741 = 317153) (by norm_num)
theorem B714673 : Blo 562809 714673 := bbase (se 2 (by rfl) ⟨268002, by rfl⟩ : syracuseStep 714673 = 536005) (by norm_num)
theorem B845765 : Blo 562809 845765 := bbase (se 4 (by rfl) ⟨79290, by rfl⟩ : syracuseStep 845765 = 158581) (by norm_num)
theorem B845789 : Blo 562809 845789 := bbase (se 3 (by rfl) ⟨158585, by rfl⟩ : syracuseStep 845789 = 317171) (by norm_num)
theorem B1271789 : Blo 562809 1271789 := bbase (se 3 (by rfl) ⟨238460, by rfl⟩ : syracuseStep 1271789 = 476921) (by norm_num)
theorem B845813 : Blo 562809 845813 := bbase (se 5 (by rfl) ⟨39647, by rfl⟩ : syracuseStep 845813 = 79295) (by norm_num)
theorem B845837 : Blo 562809 845837 := bbase (se 3 (by rfl) ⟨158594, by rfl⟩ : syracuseStep 845837 = 317189) (by norm_num)
theorem B845861 : Blo 562809 845861 := bbase (se 4 (by rfl) ⟨79299, by rfl⟩ : syracuseStep 845861 = 158599) (by norm_num)
theorem B1271861 : Blo 562809 1271861 := bbase (se 5 (by rfl) ⟨59618, by rfl⟩ : syracuseStep 1271861 = 119237) (by norm_num)
theorem B845885 : Blo 562809 845885 := bbase (se 3 (by rfl) ⟨158603, by rfl⟩ : syracuseStep 845885 = 317207) (by norm_num)
theorem B845909 : Blo 562809 845909 := bbase (se 8 (by rfl) ⟨4956, by rfl⟩ : syracuseStep 845909 = 9913) (by norm_num)
theorem B714845 : Blo 562809 714845 := bbase (se 3 (by rfl) ⟨134033, by rfl⟩ : syracuseStep 714845 = 268067) (by norm_num)
theorem B845933 : Blo 562809 845933 := bbase (se 3 (by rfl) ⟨158612, by rfl⟩ : syracuseStep 845933 = 317225) (by norm_num)
theorem B1271933 : Blo 562809 1271933 := bbase (se 3 (by rfl) ⟨238487, by rfl⟩ : syracuseStep 1271933 = 476975) (by norm_num)
theorem B845957 : Blo 562809 845957 := bbase (se 4 (by rfl) ⟨79308, by rfl⟩ : syracuseStep 845957 = 158617) (by norm_num)
theorem B714901 : Blo 562809 714901 := bbase (se 6 (by rfl) ⟨16755, by rfl⟩ : syracuseStep 714901 = 33511) (by norm_num)
theorem B845981 : Blo 562809 845981 := bbase (se 3 (by rfl) ⟨158621, by rfl⟩ : syracuseStep 845981 = 317243) (by norm_num)
theorem B846005 : Blo 562809 846005 := bbase (se 5 (by rfl) ⟨39656, by rfl⟩ : syracuseStep 846005 = 79313) (by norm_num)
theorem B1272005 : Blo 562809 1272005 := bbase (se 4 (by rfl) ⟨119250, by rfl⟩ : syracuseStep 1272005 = 238501) (by norm_num)
theorem B846029 : Blo 562809 846029 := bbase (se 3 (by rfl) ⟨158630, by rfl⟩ : syracuseStep 846029 = 317261) (by norm_num)
theorem B846053 : Blo 562809 846053 := bbase (se 4 (by rfl) ⟨79317, by rfl⟩ : syracuseStep 846053 = 158635) (by norm_num)
theorem B714997 : Blo 562809 714997 := bbase (se 5 (by rfl) ⟨33515, by rfl⟩ : syracuseStep 714997 = 67031) (by norm_num)
theorem B846077 : Blo 562809 846077 := bbase (se 3 (by rfl) ⟨158639, by rfl⟩ : syracuseStep 846077 = 317279) (by norm_num)
theorem B1272077 : Blo 562809 1272077 := bbase (se 3 (by rfl) ⟨238514, by rfl⟩ : syracuseStep 1272077 = 477029) (by norm_num)
theorem B846101 : Blo 562809 846101 := bbase (se 6 (by rfl) ⟨19830, by rfl⟩ : syracuseStep 846101 = 39661) (by norm_num)
theorem B846125 : Blo 562809 846125 := bbase (se 3 (by rfl) ⟨158648, by rfl⟩ : syracuseStep 846125 = 317297) (by norm_num)
theorem B846149 : Blo 562809 846149 := bbase (se 4 (by rfl) ⟨79326, by rfl⟩ : syracuseStep 846149 = 158653) (by norm_num)
theorem B1272149 : Blo 562809 1272149 := bbase (se 10 (by rfl) ⟨1863, by rfl⟩ : syracuseStep 1272149 = 3727) (by norm_num)
theorem B846173 : Blo 562809 846173 := bbase (se 3 (by rfl) ⟨158657, by rfl⟩ : syracuseStep 846173 = 317315) (by norm_num)
theorem B846197 : Blo 562809 846197 := bbase (se 5 (by rfl) ⟨39665, by rfl⟩ : syracuseStep 846197 = 79331) (by norm_num)
theorem B846221 : Blo 562809 846221 := bbase (se 3 (by rfl) ⟨158666, by rfl⟩ : syracuseStep 846221 = 317333) (by norm_num)
theorem B1272221 : Blo 562809 1272221 := bbase (se 3 (by rfl) ⟨238541, by rfl⟩ : syracuseStep 1272221 = 477083) (by norm_num)
theorem B715169 : Blo 562809 715169 := bbase (se 2 (by rfl) ⟨268188, by rfl⟩ : syracuseStep 715169 = 536377) (by norm_num)
theorem B846245 : Blo 562809 846245 := bbase (se 4 (by rfl) ⟨79335, by rfl⟩ : syracuseStep 846245 = 158671) (by norm_num)
theorem B846269 : Blo 562809 846269 := bbase (se 3 (by rfl) ⟨158675, by rfl⟩ : syracuseStep 846269 = 317351) (by norm_num)
theorem B846293 : Blo 562809 846293 := bbase (se 7 (by rfl) ⟨9917, by rfl⟩ : syracuseStep 846293 = 19835) (by norm_num)
theorem B715225 : Blo 562809 715225 := bbase (se 2 (by rfl) ⟨268209, by rfl⟩ : syracuseStep 715225 = 536419) (by norm_num)
theorem B1272293 : Blo 562809 1272293 := bbase (se 4 (by rfl) ⟨119277, by rfl⟩ : syracuseStep 1272293 = 238555) (by norm_num)
theorem B846317 : Blo 562809 846317 := bbase (se 3 (by rfl) ⟨158684, by rfl⟩ : syracuseStep 846317 = 317369) (by norm_num)
theorem B1075693 : Blo 562809 1075693 := bbase (se 3 (by rfl) ⟨201692, by rfl⟩ : syracuseStep 1075693 = 403385) (by norm_num)
theorem B846341 : Blo 562809 846341 := bbase (se 4 (by rfl) ⟨79344, by rfl⟩ : syracuseStep 846341 = 158689) (by norm_num)
theorem B846365 : Blo 562809 846365 := bbase (se 3 (by rfl) ⟨158693, by rfl⟩ : syracuseStep 846365 = 317387) (by norm_num)
theorem B1272365 : Blo 562809 1272365 := bbase (se 3 (by rfl) ⟨238568, by rfl⟩ : syracuseStep 1272365 = 477137) (by norm_num)
theorem B846389 : Blo 562809 846389 := bbase (se 5 (by rfl) ⟨39674, by rfl⟩ : syracuseStep 846389 = 79349) (by norm_num)
theorem B715321 : Blo 562809 715321 := bbase (se 2 (by rfl) ⟨268245, by rfl⟩ : syracuseStep 715321 = 536491) (by norm_num)
theorem B846413 : Blo 562809 846413 := bbase (se 3 (by rfl) ⟨158702, by rfl⟩ : syracuseStep 846413 = 317405) (by norm_num)
theorem B846437 : Blo 562809 846437 := bbase (se 4 (by rfl) ⟨79353, by rfl⟩ : syracuseStep 846437 = 158707) (by norm_num)
theorem B2419301 : Blo 562809 2419301 := bbase (se 4 (by rfl) ⟨226809, by rfl⟩ : syracuseStep 2419301 = 453619) (by norm_num)
theorem B1272437 : Blo 562809 1272437 := bbase (se 5 (by rfl) ⟨59645, by rfl⟩ : syracuseStep 1272437 = 119291) (by norm_num)
theorem B846461 : Blo 562809 846461 := bbase (se 3 (by rfl) ⟨158711, by rfl⟩ : syracuseStep 846461 = 317423) (by norm_num)
theorem B1075837 : Blo 562809 1075837 := bbase (se 3 (by rfl) ⟨201719, by rfl⟩ : syracuseStep 1075837 = 403439) (by norm_num)
theorem B1206917 : Blo 562809 1206917 := bbase (se 4 (by rfl) ⟨113148, by rfl⟩ : syracuseStep 1206917 = 226297) (by norm_num)
theorem B846485 : Blo 562809 846485 := bbase (se 6 (by rfl) ⟨19839, by rfl⟩ : syracuseStep 846485 = 39679) (by norm_num)
theorem B846509 : Blo 562809 846509 := bbase (se 3 (by rfl) ⟨158720, by rfl⟩ : syracuseStep 846509 = 317441) (by norm_num)
theorem B1272509 : Blo 562809 1272509 := bbase (se 3 (by rfl) ⟨238595, by rfl⟩ : syracuseStep 1272509 = 477191) (by norm_num)
theorem B846533 : Blo 562809 846533 := bbase (se 4 (by rfl) ⟨79362, by rfl⟩ : syracuseStep 846533 = 158725) (by norm_num)
theorem B846557 : Blo 562809 846557 := bbase (se 3 (by rfl) ⟨158729, by rfl⟩ : syracuseStep 846557 = 317459) (by norm_num)
theorem B715493 : Blo 562809 715493 := bbase (se 4 (by rfl) ⟨67077, by rfl⟩ : syracuseStep 715493 = 134155) (by norm_num)
theorem B846581 : Blo 562809 846581 := bbase (se 5 (by rfl) ⟨39683, by rfl⟩ : syracuseStep 846581 = 79367) (by norm_num)
theorem B1207037 : Blo 562809 1207037 := bbase (se 3 (by rfl) ⟨226319, by rfl⟩ : syracuseStep 1207037 = 452639) (by norm_num)
theorem B1272581 : Blo 562809 1272581 := bbase (se 4 (by rfl) ⟨119304, by rfl⟩ : syracuseStep 1272581 = 238609) (by norm_num)
theorem B846605 : Blo 562809 846605 := bbase (se 3 (by rfl) ⟨158738, by rfl⟩ : syracuseStep 846605 = 317477) (by norm_num)
theorem B715549 : Blo 562809 715549 := bbase (se 3 (by rfl) ⟨134165, by rfl⟩ : syracuseStep 715549 = 268331) (by norm_num)
theorem B1075997 : Blo 562809 1075997 := bbase (se 3 (by rfl) ⟨201749, by rfl⟩ : syracuseStep 1075997 = 403499) (by norm_num)
theorem B846629 : Blo 562809 846629 := bbase (se 4 (by rfl) ⟨79371, by rfl⟩ : syracuseStep 846629 = 158743) (by norm_num)
theorem B846653 : Blo 562809 846653 := bbase (se 3 (by rfl) ⟨158747, by rfl⟩ : syracuseStep 846653 = 317495) (by norm_num)
theorem B1272653 : Blo 562809 1272653 := bbase (se 3 (by rfl) ⟨238622, by rfl⟩ : syracuseStep 1272653 = 477245) (by norm_num)
theorem B846677 : Blo 562809 846677 := bbase (se 9 (by rfl) ⟨2480, by rfl⟩ : syracuseStep 846677 = 4961) (by norm_num)
theorem B2419541 : Blo 562809 2419541 := bbase (se 9 (by rfl) ⟨7088, by rfl⟩ : syracuseStep 2419541 = 14177) (by norm_num)
theorem B846701 : Blo 562809 846701 := bbase (se 3 (by rfl) ⟨158756, by rfl⟩ : syracuseStep 846701 = 317513) (by norm_num)
theorem B715645 : Blo 562809 715645 := bbase (se 3 (by rfl) ⟨134183, by rfl⟩ : syracuseStep 715645 = 268367) (by norm_num)
theorem B846725 : Blo 562809 846725 := bbase (se 4 (by rfl) ⟨79380, by rfl⟩ : syracuseStep 846725 = 158761) (by norm_num)
theorem B1272725 : Blo 562809 1272725 := bbase (se 6 (by rfl) ⟨29829, by rfl⟩ : syracuseStep 1272725 = 59659) (by norm_num)
theorem B846749 : Blo 562809 846749 := bbase (se 3 (by rfl) ⟨158765, by rfl⟩ : syracuseStep 846749 = 317531) (by norm_num)
theorem B813997 : Blo 562809 813997 := bbase (se 3 (by rfl) ⟨152624, by rfl⟩ : syracuseStep 813997 = 305249) (by norm_num)
theorem B846773 : Blo 562809 846773 := bbase (se 5 (by rfl) ⟨39692, by rfl⟩ : syracuseStep 846773 = 79385) (by norm_num)
theorem B846797 : Blo 562809 846797 := bbase (se 3 (by rfl) ⟨158774, by rfl⟩ : syracuseStep 846797 = 317549) (by norm_num)
theorem B1272797 : Blo 562809 1272797 := bbase (se 3 (by rfl) ⟨238649, by rfl⟩ : syracuseStep 1272797 = 477299) (by norm_num)
theorem B846821 : Blo 562809 846821 := bbase (se 4 (by rfl) ⟨79389, by rfl⟩ : syracuseStep 846821 = 158779) (by norm_num)
theorem B846845 : Blo 562809 846845 := bbase (se 3 (by rfl) ⟨158783, by rfl⟩ : syracuseStep 846845 = 317567) (by norm_num)
theorem B846869 : Blo 562809 846869 := bbase (se 6 (by rfl) ⟨19848, by rfl⟩ : syracuseStep 846869 = 39697) (by norm_num)
theorem B1272869 : Blo 562809 1272869 := bbase (se 4 (by rfl) ⟨119331, by rfl⟩ : syracuseStep 1272869 = 238663) (by norm_num)
theorem B715817 : Blo 562809 715817 := bbase (se 2 (by rfl) ⟨268431, by rfl⟩ : syracuseStep 715817 = 536863) (by norm_num)
theorem B846893 : Blo 562809 846893 := bbase (se 3 (by rfl) ⟨158792, by rfl⟩ : syracuseStep 846893 = 317585) (by norm_num)
theorem B846917 : Blo 562809 846917 := bbase (se 4 (by rfl) ⟨79398, by rfl⟩ : syracuseStep 846917 = 158797) (by norm_num)
theorem B846941 : Blo 562809 846941 := bbase (se 3 (by rfl) ⟨158801, by rfl⟩ : syracuseStep 846941 = 317603) (by norm_num)
theorem B715873 : Blo 562809 715873 := bbase (se 2 (by rfl) ⟨268452, by rfl⟩ : syracuseStep 715873 = 536905) (by norm_num)
theorem B1272941 : Blo 562809 1272941 := bbase (se 3 (by rfl) ⟨238676, by rfl⟩ : syracuseStep 1272941 = 477353) (by norm_num)
theorem B846965 : Blo 562809 846965 := bbase (se 5 (by rfl) ⟨39701, by rfl⟩ : syracuseStep 846965 = 79403) (by norm_num)
theorem B846989 : Blo 562809 846989 := bbase (se 3 (by rfl) ⟨158810, by rfl⟩ : syracuseStep 846989 = 317621) (by norm_num)
theorem B847013 : Blo 562809 847013 := bbase (se 4 (by rfl) ⟨79407, by rfl⟩ : syracuseStep 847013 = 158815) (by norm_num)
theorem B1273013 : Blo 562809 1273013 := bbase (se 5 (by rfl) ⟨59672, by rfl⟩ : syracuseStep 1273013 = 119345) (by norm_num)
theorem B847037 : Blo 562809 847037 := bbase (se 3 (by rfl) ⟨158819, by rfl⟩ : syracuseStep 847037 = 317639) (by norm_num)
theorem B715969 : Blo 562809 715969 := bbase (se 2 (by rfl) ⟨268488, by rfl⟩ : syracuseStep 715969 = 536977) (by norm_num)
theorem B847061 : Blo 562809 847061 := bbase (se 7 (by rfl) ⟨9926, by rfl⟩ : syracuseStep 847061 = 19853) (by norm_num)
theorem B847085 : Blo 562809 847085 := bbase (se 3 (by rfl) ⟨158828, by rfl⟩ : syracuseStep 847085 = 317657) (by norm_num)
theorem B1273085 : Blo 562809 1273085 := bbase (se 3 (by rfl) ⟨238703, by rfl⟩ : syracuseStep 1273085 = 477407) (by norm_num)
theorem B847109 : Blo 562809 847109 := bbase (se 4 (by rfl) ⟨79416, by rfl⟩ : syracuseStep 847109 = 158833) (by norm_num)
theorem B847133 : Blo 562809 847133 := bbase (se 3 (by rfl) ⟨158837, by rfl⟩ : syracuseStep 847133 = 317675) (by norm_num)
theorem B847157 : Blo 562809 847157 := bbase (se 5 (by rfl) ⟨39710, by rfl⟩ : syracuseStep 847157 = 79421) (by norm_num)
theorem B1273157 : Blo 562809 1273157 := bbase (se 4 (by rfl) ⟨119358, by rfl⟩ : syracuseStep 1273157 = 238717) (by norm_num)
theorem B847181 : Blo 562809 847181 := bbase (se 3 (by rfl) ⟨158846, by rfl⟩ : syracuseStep 847181 = 317693) (by norm_num)
theorem B847205 : Blo 562809 847205 := bbase (se 4 (by rfl) ⟨79425, by rfl⟩ : syracuseStep 847205 = 158851) (by norm_num)
theorem B716141 : Blo 562809 716141 := bbase (se 3 (by rfl) ⟨134276, by rfl⟩ : syracuseStep 716141 = 268553) (by norm_num)
theorem B1207669 : Blo 562809 1207669 := bbase (se 5 (by rfl) ⟨56609, by rfl⟩ : syracuseStep 1207669 = 113219) (by norm_num)
theorem B847229 : Blo 562809 847229 := bbase (se 3 (by rfl) ⟨158855, by rfl⟩ : syracuseStep 847229 = 317711) (by norm_num)
theorem B1273229 : Blo 562809 1273229 := bbase (se 3 (by rfl) ⟨238730, by rfl⟩ : syracuseStep 1273229 = 477461) (by norm_num)
theorem B847253 : Blo 562809 847253 := bbase (se 6 (by rfl) ⟨19857, by rfl⟩ : syracuseStep 847253 = 39715) (by norm_num)
theorem B716197 : Blo 562809 716197 := bbase (se 4 (by rfl) ⟨67143, by rfl⟩ : syracuseStep 716197 = 134287) (by norm_num)
theorem B847277 : Blo 562809 847277 := bbase (se 3 (by rfl) ⟨158864, by rfl⟩ : syracuseStep 847277 = 317729) (by norm_num)
theorem B847301 : Blo 562809 847301 := bbase (se 4 (by rfl) ⟨79434, by rfl⟩ : syracuseStep 847301 = 158869) (by norm_num)
theorem B1273301 : Blo 562809 1273301 := bbase (se 7 (by rfl) ⟨14921, by rfl⟩ : syracuseStep 1273301 = 29843) (by norm_num)
theorem B847325 : Blo 562809 847325 := bbase (se 3 (by rfl) ⟨158873, by rfl⟩ : syracuseStep 847325 = 317747) (by norm_num)
theorem B1633765 : Blo 562809 1633765 := bbase (se 4 (by rfl) ⟨153165, by rfl⟩ : syracuseStep 1633765 = 306331) (by norm_num)
theorem B847349 : Blo 562809 847349 := bbase (se 5 (by rfl) ⟨39719, by rfl⟩ : syracuseStep 847349 = 79439) (by norm_num)
theorem B716293 : Blo 562809 716293 := bbase (se 4 (by rfl) ⟨67152, by rfl⟩ : syracuseStep 716293 = 134305) (by norm_num)
theorem B847373 : Blo 562809 847373 := bbase (se 3 (by rfl) ⟨158882, by rfl⟩ : syracuseStep 847373 = 317765) (by norm_num)
theorem B1273373 : Blo 562809 1273373 := bbase (se 3 (by rfl) ⟨238757, by rfl⟩ : syracuseStep 1273373 = 477515) (by norm_num)
theorem B847397 : Blo 562809 847397 := bbase (se 4 (by rfl) ⟨79443, by rfl⟩ : syracuseStep 847397 = 158887) (by norm_num)
theorem B847421 : Blo 562809 847421 := bbase (se 3 (by rfl) ⟨158891, by rfl⟩ : syracuseStep 847421 = 317783) (by norm_num)
theorem B847445 : Blo 562809 847445 := bbase (se 8 (by rfl) ⟨4965, by rfl⟩ : syracuseStep 847445 = 9931) (by norm_num)
theorem B1273445 : Blo 562809 1273445 := bbase (se 4 (by rfl) ⟨119385, by rfl⟩ : syracuseStep 1273445 = 238771) (by norm_num)
theorem B847469 : Blo 562809 847469 := bbase (se 3 (by rfl) ⟨158900, by rfl⟩ : syracuseStep 847469 = 317801) (by norm_num)
theorem B847493 : Blo 562809 847493 := bbase (se 4 (by rfl) ⟨79452, by rfl⟩ : syracuseStep 847493 = 158905) (by norm_num)
theorem B847517 : Blo 562809 847517 := bbase (se 3 (by rfl) ⟨158909, by rfl⟩ : syracuseStep 847517 = 317819) (by norm_num)
theorem B1273517 : Blo 562809 1273517 := bbase (se 3 (by rfl) ⟨238784, by rfl⟩ : syracuseStep 1273517 = 477569) (by norm_num)
theorem B716465 : Blo 562809 716465 := bbase (se 2 (by rfl) ⟨268674, by rfl⟩ : syracuseStep 716465 = 537349) (by norm_num)
theorem B847541 : Blo 562809 847541 := bbase (se 5 (by rfl) ⟨39728, by rfl⟩ : syracuseStep 847541 = 79457) (by norm_num)
theorem B847565 : Blo 562809 847565 := bbase (se 3 (by rfl) ⟨158918, by rfl⟩ : syracuseStep 847565 = 317837) (by norm_num)
theorem B9662165 : Blo 562809 9662165 := bbase (se 7 (by rfl) ⟨113228, by rfl⟩ : syracuseStep 9662165 = 226457) (by norm_num)
theorem B847589 : Blo 562809 847589 := bbase (se 4 (by rfl) ⟨79461, by rfl⟩ : syracuseStep 847589 = 158923) (by norm_num)
theorem B716521 : Blo 562809 716521 := bbase (se 2 (by rfl) ⟨268695, by rfl⟩ : syracuseStep 716521 = 537391) (by norm_num)
theorem B1273589 : Blo 562809 1273589 := bbase (se 5 (by rfl) ⟨59699, by rfl⟩ : syracuseStep 1273589 = 119399) (by norm_num)
theorem B847613 : Blo 562809 847613 := bbase (se 3 (by rfl) ⟨158927, by rfl⟩ : syracuseStep 847613 = 317855) (by norm_num)
theorem B1306373 : Blo 562809 1306373 := bbase (se 4 (by rfl) ⟨122472, by rfl⟩ : syracuseStep 1306373 = 244945) (by norm_num)
theorem B1470221 : Blo 562809 1470221 := bbase (se 3 (by rfl) ⟨275666, by rfl⟩ : syracuseStep 1470221 = 551333) (by norm_num)
theorem B847637 : Blo 562809 847637 := bbase (se 6 (by rfl) ⟨19866, by rfl⟩ : syracuseStep 847637 = 39733) (by norm_num)
theorem B847661 : Blo 562809 847661 := bbase (se 3 (by rfl) ⟨158936, by rfl⟩ : syracuseStep 847661 = 317873) (by norm_num)
theorem B1273661 : Blo 562809 1273661 := bbase (se 3 (by rfl) ⟨238811, by rfl⟩ : syracuseStep 1273661 = 477623) (by norm_num)
theorem B847685 : Blo 562809 847685 := bbase (se 4 (by rfl) ⟨79470, by rfl⟩ : syracuseStep 847685 = 158941) (by norm_num)
theorem B716617 : Blo 562809 716617 := bbase (se 2 (by rfl) ⟨268731, by rfl⟩ : syracuseStep 716617 = 537463) (by norm_num)
theorem B847709 : Blo 562809 847709 := bbase (se 3 (by rfl) ⟨158945, by rfl⟩ : syracuseStep 847709 = 317891) (by norm_num)
theorem B847733 : Blo 562809 847733 := bbase (se 5 (by rfl) ⟨39737, by rfl⟩ : syracuseStep 847733 = 79475) (by norm_num)
theorem B1273733 : Blo 562809 1273733 := bbase (se 4 (by rfl) ⟨119412, by rfl⟩ : syracuseStep 1273733 = 238825) (by norm_num)
theorem B847757 : Blo 562809 847757 := bbase (se 3 (by rfl) ⟨158954, by rfl⟩ : syracuseStep 847757 = 317909) (by norm_num)
theorem B847781 : Blo 562809 847781 := bbase (se 4 (by rfl) ⟨79479, by rfl⟩ : syracuseStep 847781 = 158959) (by norm_num)
theorem B847805 : Blo 562809 847805 := bbase (se 3 (by rfl) ⟨158963, by rfl⟩ : syracuseStep 847805 = 317927) (by norm_num)
theorem B1273805 : Blo 562809 1273805 := bbase (se 3 (by rfl) ⟨238838, by rfl⟩ : syracuseStep 1273805 = 477677) (by norm_num)
theorem B847829 : Blo 562809 847829 := bbase (se 7 (by rfl) ⟨9935, by rfl⟩ : syracuseStep 847829 = 19871) (by norm_num)
theorem B847853 : Blo 562809 847853 := bbase (se 3 (by rfl) ⟨158972, by rfl⟩ : syracuseStep 847853 = 317945) (by norm_num)
theorem B716789 : Blo 562809 716789 := bbase (se 5 (by rfl) ⟨33599, by rfl⟩ : syracuseStep 716789 = 67199) (by norm_num)
theorem B847877 : Blo 562809 847877 := bbase (se 4 (by rfl) ⟨79488, by rfl⟩ : syracuseStep 847877 = 158977) (by norm_num)
theorem B1273877 : Blo 562809 1273877 := bbase (se 6 (by rfl) ⟨29856, by rfl⟩ : syracuseStep 1273877 = 59713) (by norm_num)
theorem B847901 : Blo 562809 847901 := bbase (se 3 (by rfl) ⟨158981, by rfl⟩ : syracuseStep 847901 = 317963) (by norm_num)
theorem B2289701 : Blo 562809 2289701 := bbase (se 4 (by rfl) ⟨214659, by rfl⟩ : syracuseStep 2289701 = 429319) (by norm_num)
theorem B716845 : Blo 562809 716845 := bbase (se 3 (by rfl) ⟨134408, by rfl⟩ : syracuseStep 716845 = 268817) (by norm_num)
theorem B847925 : Blo 562809 847925 := bbase (se 5 (by rfl) ⟨39746, by rfl⟩ : syracuseStep 847925 = 79493) (by norm_num)
theorem B847949 : Blo 562809 847949 := bbase (se 3 (by rfl) ⟨158990, by rfl⟩ : syracuseStep 847949 = 317981) (by norm_num)
theorem B1273949 : Blo 562809 1273949 := bbase (se 3 (by rfl) ⟨238865, by rfl⟩ : syracuseStep 1273949 = 477731) (by norm_num)
theorem B847973 : Blo 562809 847973 := bbase (se 4 (by rfl) ⟨79497, by rfl⟩ : syracuseStep 847973 = 158995) (by norm_num)
theorem B847997 : Blo 562809 847997 := bbase (se 3 (by rfl) ⟨158999, by rfl⟩ : syracuseStep 847997 = 317999) (by norm_num)
theorem B716941 : Blo 562809 716941 := bbase (se 3 (by rfl) ⟨134426, by rfl⟩ : syracuseStep 716941 = 268853) (by norm_num)
theorem B848021 : Blo 562809 848021 := bbase (se 6 (by rfl) ⟨19875, by rfl⟩ : syracuseStep 848021 = 39751) (by norm_num)
theorem B1274021 : Blo 562809 1274021 := bbase (se 4 (by rfl) ⟨119439, by rfl⟩ : syracuseStep 1274021 = 238879) (by norm_num)
theorem B848045 : Blo 562809 848045 := bbase (se 3 (by rfl) ⟨159008, by rfl⟩ : syracuseStep 848045 = 318017) (by norm_num)
theorem B848069 : Blo 562809 848069 := bbase (se 4 (by rfl) ⟨79506, by rfl⟩ : syracuseStep 848069 = 159013) (by norm_num)
theorem B848093 : Blo 562809 848093 := bbase (se 3 (by rfl) ⟨159017, by rfl⟩ : syracuseStep 848093 = 318035) (by norm_num)
theorem B1208557 : Blo 562809 1208557 := bbase (se 3 (by rfl) ⟨226604, by rfl⟩ : syracuseStep 1208557 = 453209) (by norm_num)
theorem B1274093 : Blo 562809 1274093 := bbase (se 3 (by rfl) ⟨238892, by rfl⟩ : syracuseStep 1274093 = 477785) (by norm_num)
theorem B848117 : Blo 562809 848117 := bbase (se 5 (by rfl) ⟨39755, by rfl⟩ : syracuseStep 848117 = 79511) (by norm_num)
theorem B848141 : Blo 562809 848141 := bbase (se 3 (by rfl) ⟨159026, by rfl⟩ : syracuseStep 848141 = 318053) (by norm_num)
theorem B848165 : Blo 562809 848165 := bbase (se 4 (by rfl) ⟨79515, by rfl⟩ : syracuseStep 848165 = 159031) (by norm_num)
theorem B1274165 : Blo 562809 1274165 := bbase (se 5 (by rfl) ⟨59726, by rfl⟩ : syracuseStep 1274165 = 119453) (by norm_num)
theorem B717113 : Blo 562809 717113 := bbase (se 2 (by rfl) ⟨268917, by rfl⟩ : syracuseStep 717113 = 537835) (by norm_num)
theorem B848189 : Blo 562809 848189 := bbase (se 3 (by rfl) ⟨159035, by rfl⟩ : syracuseStep 848189 = 318071) (by norm_num)
theorem B782669 : Blo 562809 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B3207509 : Blo 562809 3207509 := bbase (se 10 (by rfl) ⟨4698, by rfl⟩ : syracuseStep 3207509 = 9397) (by norm_num)
theorem B848213 : Blo 562809 848213 := bbase (se 10 (by rfl) ⟨1242, by rfl⟩ : syracuseStep 848213 = 2485) (by norm_num)
theorem B1208677 : Blo 562809 1208677 := bbase (se 4 (by rfl) ⟨113313, by rfl⟩ : syracuseStep 1208677 = 226627) (by norm_num)
theorem B848237 : Blo 562809 848237 := bbase (se 3 (by rfl) ⟨159044, by rfl⟩ : syracuseStep 848237 = 318089) (by norm_num)
theorem B717169 : Blo 562809 717169 := bbase (se 2 (by rfl) ⟨268938, by rfl⟩ : syracuseStep 717169 = 537877) (by norm_num)
theorem B1274237 : Blo 562809 1274237 := bbase (se 3 (by rfl) ⟨238919, by rfl⟩ : syracuseStep 1274237 = 477839) (by norm_num)
theorem B848261 : Blo 562809 848261 := bbase (se 4 (by rfl) ⟨79524, by rfl⟩ : syracuseStep 848261 = 159049) (by norm_num)
theorem B848285 : Blo 562809 848285 := bbase (se 3 (by rfl) ⟨159053, by rfl⟩ : syracuseStep 848285 = 318107) (by norm_num)
theorem B4288949 : Blo 562809 4288949 := bbase (se 5 (by rfl) ⟨201044, by rfl⟩ : syracuseStep 4288949 = 402089) (by norm_num)
theorem B848309 : Blo 562809 848309 := bbase (se 5 (by rfl) ⟨39764, by rfl⟩ : syracuseStep 848309 = 79529) (by norm_num)
theorem B1143229 : Blo 562809 1143229 := bbase (se 3 (by rfl) ⟨214355, by rfl⟩ : syracuseStep 1143229 = 428711) (by norm_num)
theorem B1274309 : Blo 562809 1274309 := bbase (se 4 (by rfl) ⟨119466, by rfl⟩ : syracuseStep 1274309 = 238933) (by norm_num)
theorem B848333 : Blo 562809 848333 := bbase (se 3 (by rfl) ⟨159062, by rfl⟩ : syracuseStep 848333 = 318125) (by norm_num)
theorem B717265 : Blo 562809 717265 := bbase (se 2 (by rfl) ⟨268974, by rfl⟩ : syracuseStep 717265 = 537949) (by norm_num)
theorem B848357 : Blo 562809 848357 := bbase (se 4 (by rfl) ⟨79533, by rfl⟩ : syracuseStep 848357 = 159067) (by norm_num)
theorem B1143277 : Blo 562809 1143277 := bbase (se 3 (by rfl) ⟨214364, by rfl⟩ : syracuseStep 1143277 = 428729) (by norm_num)
theorem B1143293 : Blo 562809 1143293 := bbase (se 3 (by rfl) ⟨214367, by rfl⟩ : syracuseStep 1143293 = 428735) (by norm_num)
theorem B848381 : Blo 562809 848381 := bbase (se 3 (by rfl) ⟨159071, by rfl⟩ : syracuseStep 848381 = 318143) (by norm_num)
theorem B1274381 : Blo 562809 1274381 := bbase (se 3 (by rfl) ⟨238946, by rfl⟩ : syracuseStep 1274381 = 477893) (by norm_num)
theorem B848405 : Blo 562809 848405 := bbase (se 6 (by rfl) ⟨19884, by rfl⟩ : syracuseStep 848405 = 39769) (by norm_num)
theorem B1143325 : Blo 562809 1143325 := bbase (se 3 (by rfl) ⟨214373, by rfl⟩ : syracuseStep 1143325 = 428747) (by norm_num)
theorem B848429 : Blo 562809 848429 := bbase (se 3 (by rfl) ⟨159080, by rfl⟩ : syracuseStep 848429 = 318161) (by norm_num)
theorem B848453 : Blo 562809 848453 := bbase (se 4 (by rfl) ⟨79542, by rfl⟩ : syracuseStep 848453 = 159085) (by norm_num)
theorem B1274453 : Blo 562809 1274453 := bbase (se 8 (by rfl) ⟨7467, by rfl⟩ : syracuseStep 1274453 = 14935) (by norm_num)
theorem B848477 : Blo 562809 848477 := bbase (se 3 (by rfl) ⟨159089, by rfl⟩ : syracuseStep 848477 = 318179) (by norm_num)
theorem B1208933 : Blo 562809 1208933 := bbase (se 4 (by rfl) ⟨113337, by rfl⟩ : syracuseStep 1208933 = 226675) (by norm_num)
theorem B848501 : Blo 562809 848501 := bbase (se 5 (by rfl) ⟨39773, by rfl⟩ : syracuseStep 848501 = 79547) (by norm_num)
theorem B848525 : Blo 562809 848525 := bbase (se 3 (by rfl) ⟨159098, by rfl⟩ : syracuseStep 848525 = 318197) (by norm_num)
theorem B1274525 : Blo 562809 1274525 := bbase (se 3 (by rfl) ⟨238973, by rfl⟩ : syracuseStep 1274525 = 477947) (by norm_num)
theorem B848549 : Blo 562809 848549 := bbase (se 4 (by rfl) ⟨79551, by rfl⟩ : syracuseStep 848549 = 159103) (by norm_num)
theorem B848573 : Blo 562809 848573 := bbase (se 3 (by rfl) ⟨159107, by rfl⟩ : syracuseStep 848573 = 318215) (by norm_num)
theorem B848597 : Blo 562809 848597 := bbase (se 7 (by rfl) ⟨9944, by rfl⟩ : syracuseStep 848597 = 19889) (by norm_num)
theorem B1274597 : Blo 562809 1274597 := bbase (se 4 (by rfl) ⟨119493, by rfl⟩ : syracuseStep 1274597 = 238987) (by norm_num)
theorem B848621 : Blo 562809 848621 := bbase (se 3 (by rfl) ⟨159116, by rfl⟩ : syracuseStep 848621 = 318233) (by norm_num)
theorem B848645 : Blo 562809 848645 := bbase (se 4 (by rfl) ⟨79560, by rfl⟩ : syracuseStep 848645 = 159121) (by norm_num)
theorem B848669 : Blo 562809 848669 := bbase (se 3 (by rfl) ⟨159125, by rfl⟩ : syracuseStep 848669 = 318251) (by norm_num)
theorem B1274669 : Blo 562809 1274669 := bbase (se 3 (by rfl) ⟨239000, by rfl⟩ : syracuseStep 1274669 = 478001) (by norm_num)
theorem B848693 : Blo 562809 848693 := bbase (se 5 (by rfl) ⟨39782, by rfl⟩ : syracuseStep 848693 = 79565) (by norm_num)
theorem B848717 : Blo 562809 848717 := bbase (se 3 (by rfl) ⟨159134, by rfl⟩ : syracuseStep 848717 = 318269) (by norm_num)
theorem B848741 : Blo 562809 848741 := bbase (se 4 (by rfl) ⟨79569, by rfl⟩ : syracuseStep 848741 = 159139) (by norm_num)
theorem B1274741 : Blo 562809 1274741 := bbase (se 5 (by rfl) ⟨59753, by rfl⟩ : syracuseStep 1274741 = 119507) (by norm_num)
theorem B848765 : Blo 562809 848765 := bbase (se 3 (by rfl) ⟨159143, by rfl⟩ : syracuseStep 848765 = 318287) (by norm_num)
theorem B848789 : Blo 562809 848789 := bbase (se 6 (by rfl) ⟨19893, by rfl⟩ : syracuseStep 848789 = 39787) (by norm_num)
theorem B848813 : Blo 562809 848813 := bbase (se 3 (by rfl) ⟨159152, by rfl⟩ : syracuseStep 848813 = 318305) (by norm_num)
theorem B1274813 : Blo 562809 1274813 := bbase (se 3 (by rfl) ⟨239027, by rfl⟩ : syracuseStep 1274813 = 478055) (by norm_num)
theorem B848837 : Blo 562809 848837 := bbase (se 4 (by rfl) ⟨79578, by rfl⟩ : syracuseStep 848837 = 159157) (by norm_num)
theorem B848861 : Blo 562809 848861 := bbase (se 3 (by rfl) ⟨159161, by rfl⟩ : syracuseStep 848861 = 318323) (by norm_num)
theorem B848885 : Blo 562809 848885 := bbase (se 5 (by rfl) ⟨39791, by rfl⟩ : syracuseStep 848885 = 79583) (by norm_num)
theorem B1274885 : Blo 562809 1274885 := bbase (se 4 (by rfl) ⟨119520, by rfl⟩ : syracuseStep 1274885 = 239041) (by norm_num)
theorem B848909 : Blo 562809 848909 := bbase (se 3 (by rfl) ⟨159170, by rfl⟩ : syracuseStep 848909 = 318341) (by norm_num)
theorem B848933 : Blo 562809 848933 := bbase (se 4 (by rfl) ⟨79587, by rfl⟩ : syracuseStep 848933 = 159175) (by norm_num)
theorem B848957 : Blo 562809 848957 := bbase (se 3 (by rfl) ⟨159179, by rfl⟩ : syracuseStep 848957 = 318359) (by norm_num)
theorem B1274957 : Blo 562809 1274957 := bbase (se 3 (by rfl) ⟨239054, by rfl⟩ : syracuseStep 1274957 = 478109) (by norm_num)
theorem B848981 : Blo 562809 848981 := bbase (se 8 (by rfl) ⟨4974, by rfl⟩ : syracuseStep 848981 = 9949) (by norm_num)
theorem B849005 : Blo 562809 849005 := bbase (se 3 (by rfl) ⟨159188, by rfl⟩ : syracuseStep 849005 = 318377) (by norm_num)
theorem B849029 : Blo 562809 849029 := bbase (se 4 (by rfl) ⟨79596, by rfl⟩ : syracuseStep 849029 = 159193) (by norm_num)
theorem B1275029 : Blo 562809 1275029 := bbase (se 6 (by rfl) ⟨29883, by rfl⟩ : syracuseStep 1275029 = 59767) (by norm_num)
theorem B849053 : Blo 562809 849053 := bbase (se 3 (by rfl) ⟨159197, by rfl⟩ : syracuseStep 849053 = 318395) (by norm_num)
theorem B849077 : Blo 562809 849077 := bbase (se 5 (by rfl) ⟨39800, by rfl⟩ : syracuseStep 849077 = 79601) (by norm_num)
theorem B849101 : Blo 562809 849101 := bbase (se 3 (by rfl) ⟨159206, by rfl⟩ : syracuseStep 849101 = 318413) (by norm_num)
theorem B1275101 : Blo 562809 1275101 := bbase (se 3 (by rfl) ⟨239081, by rfl⟩ : syracuseStep 1275101 = 478163) (by norm_num)
theorem B849125 : Blo 562809 849125 := bbase (se 4 (by rfl) ⟨79605, by rfl⟩ : syracuseStep 849125 = 159211) (by norm_num)
theorem B849149 : Blo 562809 849149 := bbase (se 3 (by rfl) ⟨159215, by rfl⟩ : syracuseStep 849149 = 318431) (by norm_num)
theorem B1602821 : Blo 562809 1602821 := bbase (se 4 (by rfl) ⟨150264, by rfl⟩ : syracuseStep 1602821 = 300529) (by norm_num)
theorem B849173 : Blo 562809 849173 := bbase (se 6 (by rfl) ⟨19902, by rfl⟩ : syracuseStep 849173 = 39805) (by norm_num)
theorem B1176869 : Blo 562809 1176869 := bbase (se 4 (by rfl) ⟨110331, by rfl⟩ : syracuseStep 1176869 = 220663) (by norm_num)
theorem B1275173 : Blo 562809 1275173 := bbase (se 4 (by rfl) ⟨119547, by rfl⟩ : syracuseStep 1275173 = 239095) (by norm_num)
theorem B849197 : Blo 562809 849197 := bbase (se 3 (by rfl) ⟨159224, by rfl⟩ : syracuseStep 849197 = 318449) (by norm_num)
theorem B849221 : Blo 562809 849221 := bbase (se 4 (by rfl) ⟨79614, by rfl⟩ : syracuseStep 849221 = 159229) (by norm_num)
theorem B849245 : Blo 562809 849245 := bbase (se 3 (by rfl) ⟨159233, by rfl⟩ : syracuseStep 849245 = 318467) (by norm_num)
theorem B1275245 : Blo 562809 1275245 := bbase (se 3 (by rfl) ⟨239108, by rfl⟩ : syracuseStep 1275245 = 478217) (by norm_num)
theorem B849269 : Blo 562809 849269 := bbase (se 5 (by rfl) ⟨39809, by rfl⟩ : syracuseStep 849269 = 79619) (by norm_num)
theorem B849293 : Blo 562809 849293 := bbase (se 3 (by rfl) ⟨159242, by rfl⟩ : syracuseStep 849293 = 318485) (by norm_num)
theorem B849317 : Blo 562809 849317 := bbase (se 4 (by rfl) ⟨79623, by rfl⟩ : syracuseStep 849317 = 159247) (by norm_num)
theorem B1275317 : Blo 562809 1275317 := bbase (se 5 (by rfl) ⟨59780, by rfl⟩ : syracuseStep 1275317 = 119561) (by norm_num)
theorem B849341 : Blo 562809 849341 := bbase (se 3 (by rfl) ⟨159251, by rfl⟩ : syracuseStep 849341 = 318503) (by norm_num)
theorem B849365 : Blo 562809 849365 := bbase (se 7 (by rfl) ⟨9953, by rfl⟩ : syracuseStep 849365 = 19907) (by norm_num)
theorem B1209821 : Blo 562809 1209821 := bbase (se 3 (by rfl) ⟨226841, by rfl⟩ : syracuseStep 1209821 = 453683) (by norm_num)
theorem B849389 : Blo 562809 849389 := bbase (se 3 (by rfl) ⟨159260, by rfl⟩ : syracuseStep 849389 = 318521) (by norm_num)
theorem B1603061 : Blo 562809 1603061 := bbase (se 5 (by rfl) ⟨75143, by rfl⟩ : syracuseStep 1603061 = 150287) (by norm_num)
theorem B3208693 : Blo 562809 3208693 := bbase (se 5 (by rfl) ⟨150407, by rfl⟩ : syracuseStep 3208693 = 300815) (by norm_num)
theorem B849413 : Blo 562809 849413 := bbase (se 4 (by rfl) ⟨79632, by rfl⟩ : syracuseStep 849413 = 159265) (by norm_num)
theorem B849437 : Blo 562809 849437 := bbase (se 3 (by rfl) ⟨159269, by rfl⟩ : syracuseStep 849437 = 318539) (by norm_num)
theorem B849461 : Blo 562809 849461 := bbase (se 5 (by rfl) ⟨39818, by rfl⟩ : syracuseStep 849461 = 79637) (by norm_num)
theorem B849485 : Blo 562809 849485 := bbase (se 3 (by rfl) ⟨159278, by rfl⟩ : syracuseStep 849485 = 318557) (by norm_num)
theorem B849509 : Blo 562809 849509 := bbase (se 4 (by rfl) ⟨79641, by rfl⟩ : syracuseStep 849509 = 159283) (by norm_num)
theorem B849533 : Blo 562809 849533 := bbase (se 3 (by rfl) ⟨159287, by rfl⟩ : syracuseStep 849533 = 318575) (by norm_num)
theorem B2717333 : Blo 562809 2717333 := bbase (se 6 (by rfl) ⟨63687, by rfl⟩ : syracuseStep 2717333 = 127375) (by norm_num)
theorem B849557 : Blo 562809 849557 := bbase (se 6 (by rfl) ⟨19911, by rfl⟩ : syracuseStep 849557 = 39823) (by norm_num)
theorem B849581 : Blo 562809 849581 := bbase (se 3 (by rfl) ⟨159296, by rfl⟩ : syracuseStep 849581 = 318593) (by norm_num)
theorem B1603253 : Blo 562809 1603253 := bbase (se 5 (by rfl) ⟨75152, by rfl⟩ : syracuseStep 1603253 = 150305) (by norm_num)
theorem B849605 : Blo 562809 849605 := bbase (se 4 (by rfl) ⟨79650, by rfl⟩ : syracuseStep 849605 = 159301) (by norm_num)
theorem B1210061 : Blo 562809 1210061 := bbase (se 3 (by rfl) ⟨226886, by rfl⟩ : syracuseStep 1210061 = 453773) (by norm_num)
theorem B849629 : Blo 562809 849629 := bbase (se 3 (by rfl) ⟨159305, by rfl⟩ : syracuseStep 849629 = 318611) (by norm_num)
theorem B849653 : Blo 562809 849653 := bbase (se 5 (by rfl) ⟨39827, by rfl⟩ : syracuseStep 849653 = 79655) (by norm_num)
theorem B849677 : Blo 562809 849677 := bbase (se 3 (by rfl) ⟨159314, by rfl⟩ : syracuseStep 849677 = 318629) (by norm_num)
theorem B2029349 : Blo 562809 2029349 := bbase (se 4 (by rfl) ⟨190251, by rfl⟩ : syracuseStep 2029349 = 380503) (by norm_num)
theorem B849701 : Blo 562809 849701 := bbase (se 4 (by rfl) ⟨79659, by rfl⟩ : syracuseStep 849701 = 159319) (by norm_num)
theorem B3143477 : Blo 562809 3143477 := bbase (se 5 (by rfl) ⟨147350, by rfl⟩ : syracuseStep 3143477 = 294701) (by norm_num)
theorem B849725 : Blo 562809 849725 := bbase (se 3 (by rfl) ⟨159323, by rfl⟩ : syracuseStep 849725 = 318647) (by norm_num)
theorem B849749 : Blo 562809 849749 := bbase (se 9 (by rfl) ⟨2489, by rfl⟩ : syracuseStep 849749 = 4979) (by norm_num)
theorem B849773 : Blo 562809 849773 := bbase (se 3 (by rfl) ⟨159332, by rfl⟩ : syracuseStep 849773 = 318665) (by norm_num)
theorem B1046405 : Blo 562809 1046405 := bbase (se 4 (by rfl) ⟨98100, by rfl⟩ : syracuseStep 1046405 = 196201) (by norm_num)
theorem B849797 : Blo 562809 849797 := bbase (se 4 (by rfl) ⟨79668, by rfl⟩ : syracuseStep 849797 = 159337) (by norm_num)
theorem B849821 : Blo 562809 849821 := bbase (se 3 (by rfl) ⟨159341, by rfl⟩ : syracuseStep 849821 = 318683) (by norm_num)
theorem B2717621 : Blo 562809 2717621 := bbase (se 5 (by rfl) ⟨127388, by rfl⟩ : syracuseStep 2717621 = 254777) (by norm_num)
theorem B849845 : Blo 562809 849845 := bbase (se 5 (by rfl) ⟨39836, by rfl⟩ : syracuseStep 849845 = 79673) (by norm_num)
theorem B849869 : Blo 562809 849869 := bbase (se 3 (by rfl) ⟨159350, by rfl⟩ : syracuseStep 849869 = 318701) (by norm_num)
theorem B849893 : Blo 562809 849893 := bbase (se 4 (by rfl) ⟨79677, by rfl⟩ : syracuseStep 849893 = 159355) (by norm_num)
theorem B849917 : Blo 562809 849917 := bbase (se 3 (by rfl) ⟨159359, by rfl⟩ : syracuseStep 849917 = 318719) (by norm_num)
theorem B849941 : Blo 562809 849941 := bbase (se 6 (by rfl) ⟨19920, by rfl⟩ : syracuseStep 849941 = 39841) (by norm_num)
theorem B849965 : Blo 562809 849965 := bbase (se 3 (by rfl) ⟨159368, by rfl⟩ : syracuseStep 849965 = 318737) (by norm_num)
theorem B849989 : Blo 562809 849989 := bbase (se 4 (by rfl) ⟨79686, by rfl⟩ : syracuseStep 849989 = 159373) (by norm_num)
theorem B850013 : Blo 562809 850013 := bbase (se 3 (by rfl) ⟨159377, by rfl⟩ : syracuseStep 850013 = 318755) (by norm_num)
theorem B850037 : Blo 562809 850037 := bbase (se 5 (by rfl) ⟨39845, by rfl⟩ : syracuseStep 850037 = 79691) (by norm_num)
theorem B850061 : Blo 562809 850061 := bbase (se 3 (by rfl) ⟨159386, by rfl⟩ : syracuseStep 850061 = 318773) (by norm_num)
theorem B850085 : Blo 562809 850085 := bbase (se 4 (by rfl) ⟨79695, by rfl⟩ : syracuseStep 850085 = 159391) (by norm_num)
theorem B850109 : Blo 562809 850109 := bbase (se 3 (by rfl) ⟨159395, by rfl⟩ : syracuseStep 850109 = 318791) (by norm_num)
theorem B850133 : Blo 562809 850133 := bbase (se 7 (by rfl) ⟨9962, by rfl⟩ : syracuseStep 850133 = 19925) (by norm_num)
theorem B817381 : Blo 562809 817381 := bbase (se 4 (by rfl) ⟨76629, by rfl⟩ : syracuseStep 817381 = 153259) (by norm_num)
theorem B850157 : Blo 562809 850157 := bbase (se 3 (by rfl) ⟨159404, by rfl⟩ : syracuseStep 850157 = 318809) (by norm_num)
theorem B850181 : Blo 562809 850181 := bbase (se 4 (by rfl) ⟨79704, by rfl⟩ : syracuseStep 850181 = 159409) (by norm_num)
theorem B6715669 : Blo 562809 6715669 := bbase (se 6 (by rfl) ⟨157398, by rfl⟩ : syracuseStep 6715669 = 314797) (by norm_num)
theorem B850205 : Blo 562809 850205 := bbase (se 3 (by rfl) ⟨159413, by rfl⟩ : syracuseStep 850205 = 318827) (by norm_num)
theorem B686441 : Blo 562809 686441 := bbase (se 2 (by rfl) ⟨257415, by rfl⟩ : syracuseStep 686441 = 514831) (by norm_num)
theorem B981445 : Blo 562809 981445 := bbase (se 4 (by rfl) ⟨92010, by rfl⟩ : syracuseStep 981445 = 184021) (by norm_num)
theorem B1604245 : Blo 562809 1604245 := bbase (se 6 (by rfl) ⟨37599, by rfl⟩ : syracuseStep 1604245 = 75199) (by norm_num)
theorem B916157 : Blo 562809 916157 := bbase (se 3 (by rfl) ⟨171779, by rfl⟩ : syracuseStep 916157 = 343559) (by norm_num)
theorem B1899557 : Blo 562809 1899557 := bbase (se 4 (by rfl) ⟨178083, by rfl⟩ : syracuseStep 1899557 = 356167) (by norm_num)
theorem B916525 : Blo 562809 916525 := bbase (se 3 (by rfl) ⟨171848, by rfl⟩ : syracuseStep 916525 = 343697) (by norm_num)
theorem B1015021 : Blo 562809 1015021 := bbase (se 3 (by rfl) ⟨190316, by rfl⟩ : syracuseStep 1015021 = 380633) (by norm_num)
theorem B1015093 : Blo 562809 1015093 := bbase (se 5 (by rfl) ⟨47582, by rfl⟩ : syracuseStep 1015093 = 95165) (by norm_num)
theorem B3210677 : Blo 562809 3210677 := bbase (se 5 (by rfl) ⟨150500, by rfl⟩ : syracuseStep 3210677 = 301001) (by norm_num)
theorem B1899989 : Blo 562809 1899989 := bbase (se 7 (by rfl) ⟨22265, by rfl⟩ : syracuseStep 1899989 = 44531) (by norm_num)
theorem B5438933 : Blo 562809 5438933 := bbase (se 7 (by rfl) ⟨63737, by rfl⟩ : syracuseStep 5438933 = 127475) (by norm_num)
theorem B949765 : Blo 562809 949765 := bbase (se 4 (by rfl) ⟨89040, by rfl⟩ : syracuseStep 949765 = 178081) (by norm_num)
theorem B4587029 : Blo 562809 4587029 := bbase (se 6 (by rfl) ⟨107508, by rfl⟩ : syracuseStep 4587029 = 215017) (by norm_num)
theorem B2850389 : Blo 562809 2850389 := bbase (se 8 (by rfl) ⟨16701, by rfl⟩ : syracuseStep 2850389 = 33403) (by norm_num)
theorem B949853 : Blo 562809 949853 := bbase (se 3 (by rfl) ⟨178097, by rfl⟩ : syracuseStep 949853 = 356195) (by norm_num)
theorem B917149 : Blo 562809 917149 := bbase (se 3 (by rfl) ⟨171965, by rfl⟩ : syracuseStep 917149 = 343931) (by norm_num)
theorem B949981 : Blo 562809 949981 := bbase (se 3 (by rfl) ⟨178121, by rfl⟩ : syracuseStep 949981 = 356243) (by norm_num)
theorem B1605349 : Blo 562809 1605349 := bbase (se 4 (by rfl) ⟨150501, by rfl⟩ : syracuseStep 1605349 = 301003) (by norm_num)
theorem B950069 : Blo 562809 950069 := bbase (se 5 (by rfl) ⟨44534, by rfl⟩ : syracuseStep 950069 = 89069) (by norm_num)
theorem B1834805 : Blo 562809 1834805 := bbase (se 5 (by rfl) ⟨86006, by rfl⟩ : syracuseStep 1834805 = 172013) (by norm_num)
theorem B1900421 : Blo 562809 1900421 := bbase (se 4 (by rfl) ⟨178164, by rfl⟩ : syracuseStep 1900421 = 356329) (by norm_num)
theorem B950197 : Blo 562809 950197 := bbase (se 5 (by rfl) ⟨44540, by rfl⟩ : syracuseStep 950197 = 89081) (by norm_num)
theorem B3964933 : Blo 562809 3964933 := bstep (se 4 (by rfl) ⟨371712, by rfl⟩ : syracuseStep 3964933 = 743425) B743425
theorem B950305 : Blo 562809 950305 := bstep (se 2 (by rfl) ⟨356364, by rfl⟩ : syracuseStep 950305 = 712729) B712729
theorem B950339 : Blo 562809 950339 := bstep (se 1 (by rfl) ⟨712754, by rfl⟩ : syracuseStep 950339 = 1425509) B1425509
theorem B3211427 : Blo 562809 3211427 := bstep (se 1 (by rfl) ⟨2408570, by rfl⟩ : syracuseStep 3211427 = 4817141) B4817141
theorem B950467 : Blo 562809 950467 := bstep (se 1 (by rfl) ⟨712850, by rfl⟩ : syracuseStep 950467 = 1425701) B1425701
theorem B950609 : Blo 562809 950609 := bstep (se 2 (by rfl) ⟨356478, by rfl⟩ : syracuseStep 950609 = 712957) B712957
theorem B4391309 : Blo 562809 4391309 := bstep (se 3 (by rfl) ⟨823370, by rfl⟩ : syracuseStep 4391309 = 1646741) B1646741
theorem B950737 : Blo 562809 950737 := bstep (se 2 (by rfl) ⟨356526, by rfl⟩ : syracuseStep 950737 = 713053) B713053
theorem B950771 : Blo 562809 950771 := bstep (se 1 (by rfl) ⟨713078, by rfl⟩ : syracuseStep 950771 = 1426157) B1426157
theorem B1901069 : Blo 562809 1901069 := bstep (se 3 (by rfl) ⟨356450, by rfl⟩ : syracuseStep 1901069 = 712901) B712901
theorem B1606193 : Blo 562809 1606193 := bstep (se 2 (by rfl) ⟨602322, by rfl⟩ : syracuseStep 1606193 = 1204645) B1204645
theorem B1901123 : Blo 562809 1901123 := bstep (se 1 (by rfl) ⟨1425842, by rfl⟩ : syracuseStep 1901123 = 2851685) B2851685
theorem B950899 : Blo 562809 950899 := bstep (se 1 (by rfl) ⟨713174, by rfl⟩ : syracuseStep 950899 = 1426349) B1426349
theorem B2294435 : Blo 562809 2294435 := bstep (se 1 (by rfl) ⟨1720826, by rfl⟩ : syracuseStep 2294435 = 3441653) B3441653
theorem B951041 : Blo 562809 951041 := bstep (se 2 (by rfl) ⟨356640, by rfl⟩ : syracuseStep 951041 = 713281) B713281
theorem B1901393 : Blo 562809 1901393 := bstep (se 2 (by rfl) ⟨713022, by rfl⟩ : syracuseStep 1901393 = 1426045) B1426045
theorem B951169 : Blo 562809 951169 := bstep (se 2 (by rfl) ⟨356688, by rfl⟩ : syracuseStep 951169 = 713377) B713377
theorem B951203 : Blo 562809 951203 := bstep (se 1 (by rfl) ⟨713402, by rfl⟩ : syracuseStep 951203 = 1426805) B1426805
theorem B951331 : Blo 562809 951331 := bstep (se 1 (by rfl) ⟨713498, by rfl⟩ : syracuseStep 951331 = 1426997) B1426997
theorem B1016867 : Blo 562809 1016867 := bstep (se 1 (by rfl) ⟨762650, by rfl⟩ : syracuseStep 1016867 = 1525301) B1525301
theorem B951473 : Blo 562809 951473 := bstep (se 2 (by rfl) ⟨356802, by rfl⟩ : syracuseStep 951473 = 713605) B713605
theorem B4359365 : Blo 562809 4359365 := bstep (se 4 (by rfl) ⟨408690, by rfl⟩ : syracuseStep 4359365 = 817381) B817381
theorem B4064525 : Blo 562809 4064525 := bstep (se 3 (by rfl) ⟨762098, by rfl⟩ : syracuseStep 4064525 = 1524197) B1524197
theorem B1934605 : Blo 562809 1934605 := bstep (se 3 (by rfl) ⟨362738, by rfl⟩ : syracuseStep 1934605 = 725477) B725477
theorem B951601 : Blo 562809 951601 := bstep (se 2 (by rfl) ⟨356850, by rfl⟩ : syracuseStep 951601 = 713701) B713701
theorem B1606979 : Blo 562809 1606979 := bstep (se 1 (by rfl) ⟨1205234, by rfl⟩ : syracuseStep 1606979 = 2410469) B2410469
theorem B3048781 : Blo 562809 3048781 := bstep (se 3 (by rfl) ⟨571646, by rfl⟩ : syracuseStep 3048781 = 1143293) B1143293
theorem B951635 : Blo 562809 951635 := bstep (se 1 (by rfl) ⟨713726, by rfl⟩ : syracuseStep 951635 = 1427453) B1427453
theorem B1901933 : Blo 562809 1901933 := bstep (se 3 (by rfl) ⟨356612, by rfl⟩ : syracuseStep 1901933 = 713225) B713225
theorem B1901987 : Blo 562809 1901987 := bstep (se 1 (by rfl) ⟨1426490, by rfl⟩ : syracuseStep 1901987 = 2852981) B2852981
theorem B951763 : Blo 562809 951763 := bstep (se 1 (by rfl) ⟨713822, by rfl⟩ : syracuseStep 951763 = 1427645) B1427645
theorem B1836611 : Blo 562809 1836611 := bstep (se 1 (by rfl) ⟨1377458, by rfl⟩ : syracuseStep 1836611 = 2754917) B2754917
theorem B1148483 : Blo 562809 1148483 := bstep (se 1 (by rfl) ⟨861362, by rfl⟩ : syracuseStep 1148483 = 1722725) B1722725
theorem B951905 : Blo 562809 951905 := bstep (se 2 (by rfl) ⟨356964, by rfl⟩ : syracuseStep 951905 = 713929) B713929
theorem B1017443 : Blo 562809 1017443 := bstep (se 1 (by rfl) ⟨763082, by rfl⟩ : syracuseStep 1017443 = 1526165) B1526165
theorem B1607309 : Blo 562809 1607309 := bstep (se 3 (by rfl) ⟨301370, by rfl⟩ : syracuseStep 1607309 = 602741) B602741
theorem B1902257 : Blo 562809 1902257 := bstep (se 2 (by rfl) ⟨713346, by rfl⟩ : syracuseStep 1902257 = 1426693) B1426693
theorem B1607377 : Blo 562809 1607377 := bstep (se 2 (by rfl) ⟨602766, by rfl⟩ : syracuseStep 1607377 = 1205533) B1205533
theorem B952033 : Blo 562809 952033 := bstep (se 2 (by rfl) ⟨357012, by rfl⟩ : syracuseStep 952033 = 714025) B714025
theorem B952067 : Blo 562809 952067 := bstep (se 1 (by rfl) ⟨714050, by rfl⟩ : syracuseStep 952067 = 1428101) B1428101
theorem B919331 : Blo 562809 919331 := bstep (se 1 (by rfl) ⟨689498, by rfl⟩ : syracuseStep 919331 = 1378997) B1378997
theorem B2852657 : Blo 562809 2852657 := bstep (se 2 (by rfl) ⟨1069746, by rfl⟩ : syracuseStep 2852657 = 2139493) B2139493
theorem B952195 : Blo 562809 952195 := bstep (se 1 (by rfl) ⟨714146, by rfl⟩ : syracuseStep 952195 = 1428293) B1428293
theorem B1017731 : Blo 562809 1017731 := bstep (se 1 (by rfl) ⟨763298, by rfl⟩ : syracuseStep 1017731 = 1526597) B1526597
theorem B1607651 : Blo 562809 1607651 := bstep (se 1 (by rfl) ⟨1205738, by rfl⟩ : syracuseStep 1607651 = 2411477) B2411477
theorem B952337 : Blo 562809 952337 := bstep (se 2 (by rfl) ⟨357126, by rfl⟩ : syracuseStep 952337 = 714253) B714253
theorem B3606605 : Blo 562809 3606605 := bstep (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) B1352477
theorem B1017955 : Blo 562809 1017955 := bstep (se 1 (by rfl) ⟨763466, by rfl⟩ : syracuseStep 1017955 = 1526933) B1526933
theorem B952465 : Blo 562809 952465 := bstep (se 2 (by rfl) ⟨357174, by rfl⟩ : syracuseStep 952465 = 714349) B714349
theorem B1018019 : Blo 562809 1018019 := bstep (se 1 (by rfl) ⟨763514, by rfl⟩ : syracuseStep 1018019 = 1527029) B1527029
theorem B952499 : Blo 562809 952499 := bstep (se 1 (by rfl) ⟨714374, by rfl⟩ : syracuseStep 952499 = 1428749) B1428749
theorem B1902797 : Blo 562809 1902797 := bstep (se 3 (by rfl) ⟨356774, by rfl⟩ : syracuseStep 1902797 = 713549) B713549
theorem B2033905 : Blo 562809 2033905 := bstep (se 2 (by rfl) ⟨762714, by rfl⟩ : syracuseStep 2033905 = 1525429) B1525429
theorem B1902851 : Blo 562809 1902851 := bstep (se 1 (by rfl) ⟨1427138, by rfl⟩ : syracuseStep 1902851 = 2854277) B2854277
theorem B1018129 : Blo 562809 1018129 := bstep (se 2 (by rfl) ⟨381798, by rfl⟩ : syracuseStep 1018129 = 763597) B763597
theorem B952627 : Blo 562809 952627 := bstep (se 1 (by rfl) ⟨714470, by rfl⟩ : syracuseStep 952627 = 1428941) B1428941
theorem B1804685 : Blo 562809 1804685 := bstep (se 3 (by rfl) ⟨338378, by rfl⟩ : syracuseStep 1804685 = 676757) B676757
theorem B952769 : Blo 562809 952769 := bstep (se 2 (by rfl) ⟨357288, by rfl⟩ : syracuseStep 952769 = 714577) B714577
theorem B1903121 : Blo 562809 1903121 := bstep (se 2 (by rfl) ⟨713670, by rfl⟩ : syracuseStep 1903121 = 1427341) B1427341
theorem B952897 : Blo 562809 952897 := bstep (se 2 (by rfl) ⟨357336, by rfl⟩ : syracuseStep 952897 = 714673) B714673
theorem B6097477 : Blo 562809 6097477 := bstep (se 4 (by rfl) ⟨571638, by rfl⟩ : syracuseStep 6097477 = 1143277) B1143277
theorem B952931 : Blo 562809 952931 := bstep (se 1 (by rfl) ⟨714698, by rfl⟩ : syracuseStep 952931 = 1429397) B1429397
theorem B4295267 : Blo 562809 4295267 := bstep (se 1 (by rfl) ⟨3221450, by rfl⟩ : syracuseStep 4295267 = 6442901) B6442901
theorem B8784611 : Blo 562809 8784611 := bstep (se 1 (by rfl) ⟨6588458, by rfl⟩ : syracuseStep 8784611 = 13176917) B13176917
theorem B953059 : Blo 562809 953059 := bstep (se 1 (by rfl) ⟨714794, by rfl⟩ : syracuseStep 953059 = 1429589) B1429589
theorem B1608493 : Blo 562809 1608493 := bstep (se 3 (by rfl) ⟨301592, by rfl⟩ : syracuseStep 1608493 = 603185) B603185
theorem B6097733 : Blo 562809 6097733 := bstep (se 4 (by rfl) ⟨571662, by rfl⟩ : syracuseStep 6097733 = 1143325) B1143325
theorem B953201 : Blo 562809 953201 := bstep (se 2 (by rfl) ⟨357450, by rfl⟩ : syracuseStep 953201 = 714901) B714901
theorem B1608653 : Blo 562809 1608653 := bstep (se 3 (by rfl) ⟨301622, by rfl⟩ : syracuseStep 1608653 = 603245) B603245
theorem B953329 : Blo 562809 953329 := bstep (se 2 (by rfl) ⟨357498, by rfl⟩ : syracuseStep 953329 = 714997) B714997
theorem B953363 : Blo 562809 953363 := bstep (se 1 (by rfl) ⟨715022, by rfl⟩ : syracuseStep 953363 = 1430045) B1430045
theorem B1903661 : Blo 562809 1903661 := bstep (se 3 (by rfl) ⟨356936, by rfl⟩ : syracuseStep 1903661 = 713873) B713873
theorem B1903715 : Blo 562809 1903715 := bstep (se 1 (by rfl) ⟨1427786, by rfl⟩ : syracuseStep 1903715 = 2855573) B2855573
theorem B5442659 : Blo 562809 5442659 := bstep (se 1 (by rfl) ⟨4081994, by rfl⟩ : syracuseStep 5442659 = 8163989) B8163989
theorem B1608835 : Blo 562809 1608835 := bstep (se 1 (by rfl) ⟨1206626, by rfl⟩ : syracuseStep 1608835 = 2413253) B2413253
theorem B953491 : Blo 562809 953491 := bstep (se 1 (by rfl) ⟨715118, by rfl⟩ : syracuseStep 953491 = 1430237) B1430237
theorem B724147 : Blo 562809 724147 := bstep (se 1 (by rfl) ⟨543110, by rfl⟩ : syracuseStep 724147 = 1086221) B1086221
theorem B2723021 : Blo 562809 2723021 := bstep (se 3 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 2723021 = 1021133) B1021133
theorem B2854115 : Blo 562809 2854115 := bstep (se 1 (by rfl) ⟨2140586, by rfl⟩ : syracuseStep 2854115 = 4281173) B4281173
theorem B953633 : Blo 562809 953633 := bstep (se 2 (by rfl) ⟨357612, by rfl⟩ : syracuseStep 953633 = 715225) B715225
theorem B1903985 : Blo 562809 1903985 := bstep (se 2 (by rfl) ⟨713994, by rfl⟩ : syracuseStep 1903985 = 1427989) B1427989
theorem B953761 : Blo 562809 953761 := bstep (se 2 (by rfl) ⟨357660, by rfl⟩ : syracuseStep 953761 = 715321) B715321
theorem B953795 : Blo 562809 953795 := bstep (se 1 (by rfl) ⟨715346, by rfl⟩ : syracuseStep 953795 = 1430693) B1430693
theorem B953923 : Blo 562809 953923 := bstep (se 1 (by rfl) ⟨715442, by rfl⟩ : syracuseStep 953923 = 1430885) B1430885
theorem B954065 : Blo 562809 954065 := bstep (se 2 (by rfl) ⟨357774, by rfl⟩ : syracuseStep 954065 = 715549) B715549
theorem B32476949 : Blo 562809 32476949 := bstep (se 6 (by rfl) ⟨761178, by rfl⟩ : syracuseStep 32476949 = 1522357) B1522357
theorem B855841 : Blo 562809 855841 := bstep (se 2 (by rfl) ⟨320940, by rfl⟩ : syracuseStep 855841 = 641881) B641881
theorem B954193 : Blo 562809 954193 := bstep (se 2 (by rfl) ⟨357822, by rfl⟩ : syracuseStep 954193 = 715645) B715645
theorem B954227 : Blo 562809 954227 := bstep (se 1 (by rfl) ⟨715670, by rfl⟩ : syracuseStep 954227 = 1431341) B1431341
theorem B1904525 : Blo 562809 1904525 := bstep (se 3 (by rfl) ⟨357098, by rfl⟩ : syracuseStep 1904525 = 714197) B714197
theorem B1085329 : Blo 562809 1085329 := bstep (se 2 (by rfl) ⟨406998, by rfl⟩ : syracuseStep 1085329 = 813997) B813997
theorem B1806275 : Blo 562809 1806275 := bstep (se 1 (by rfl) ⟨1354706, by rfl⟩ : syracuseStep 1806275 = 2709413) B2709413
theorem B1904579 : Blo 562809 1904579 := bstep (se 1 (by rfl) ⟨1428434, by rfl⟩ : syracuseStep 1904579 = 2856869) B2856869
theorem B954355 : Blo 562809 954355 := bstep (se 1 (by rfl) ⟨715766, by rfl⟩ : syracuseStep 954355 = 1431533) B1431533
theorem B2854925 : Blo 562809 2854925 := bstep (se 3 (by rfl) ⟨535298, by rfl⟩ : syracuseStep 2854925 = 1070597) B1070597
theorem B954497 : Blo 562809 954497 := bstep (se 2 (by rfl) ⟨357936, by rfl⟩ : syracuseStep 954497 = 715873) B715873
theorem B1904849 : Blo 562809 1904849 := bstep (se 2 (by rfl) ⟨714318, by rfl⟩ : syracuseStep 1904849 = 1428637) B1428637
theorem B12226787 : Blo 562809 12226787 := bstep (se 1 (by rfl) ⟨9170090, by rfl⟩ : syracuseStep 12226787 = 18340181) B18340181
theorem B954625 : Blo 562809 954625 := bstep (se 2 (by rfl) ⟨357984, by rfl⟩ : syracuseStep 954625 = 715969) B715969
theorem B1085699 : Blo 562809 1085699 := bstep (se 1 (by rfl) ⟨814274, by rfl⟩ : syracuseStep 1085699 = 1628549) B1628549
theorem B23892245 : Blo 562809 23892245 := bstep (se 6 (by rfl) ⟨559974, by rfl⟩ : syracuseStep 23892245 = 1119949) B1119949
theorem B954659 : Blo 562809 954659 := bstep (se 1 (by rfl) ⟨715994, by rfl⟩ : syracuseStep 954659 = 1431989) B1431989
theorem B954787 : Blo 562809 954787 := bstep (se 1 (by rfl) ⟨716090, by rfl⟩ : syracuseStep 954787 = 1432181) B1432181
theorem B1610225 : Blo 562809 1610225 := bstep (se 2 (by rfl) ⟨603834, by rfl⟩ : syracuseStep 1610225 = 1207669) B1207669
theorem B954929 : Blo 562809 954929 := bstep (se 2 (by rfl) ⟨358098, by rfl⟩ : syracuseStep 954929 = 716197) B716197
theorem B955057 : Blo 562809 955057 := bstep (se 2 (by rfl) ⟨358146, by rfl⟩ : syracuseStep 955057 = 716293) B716293
theorem B955091 : Blo 562809 955091 := bstep (se 1 (by rfl) ⟨716318, by rfl⟩ : syracuseStep 955091 = 1432637) B1432637
theorem B1905389 : Blo 562809 1905389 := bstep (se 3 (by rfl) ⟨357260, by rfl⟩ : syracuseStep 1905389 = 714521) B714521
theorem B6886129 : Blo 562809 6886129 := bstep (se 2 (by rfl) ⟨2582298, by rfl⟩ : syracuseStep 6886129 = 5164597) B5164597
theorem B2167565 : Blo 562809 2167565 := bstep (se 3 (by rfl) ⟨406418, by rfl⟩ : syracuseStep 2167565 = 812837) B812837
theorem B1905443 : Blo 562809 1905443 := bstep (se 1 (by rfl) ⟨1429082, by rfl⟩ : syracuseStep 1905443 = 2858165) B2858165
theorem B955219 : Blo 562809 955219 := bstep (se 1 (by rfl) ⟨716414, by rfl⟩ : syracuseStep 955219 = 1432829) B1432829
theorem B955361 : Blo 562809 955361 := bstep (se 2 (by rfl) ⟨358260, by rfl⟩ : syracuseStep 955361 = 716521) B716521
theorem B2790413 : Blo 562809 2790413 := bstep (se 3 (by rfl) ⟨523202, by rfl⟩ : syracuseStep 2790413 = 1046405) B1046405
theorem B857105 : Blo 562809 857105 := bstep (se 2 (by rfl) ⟨321414, by rfl⟩ : syracuseStep 857105 = 642829) B642829
theorem B1905713 : Blo 562809 1905713 := bstep (se 2 (by rfl) ⟨714642, by rfl⟩ : syracuseStep 1905713 = 1429285) B1429285
theorem B955489 : Blo 562809 955489 := bstep (se 2 (by rfl) ⟨358308, by rfl⟩ : syracuseStep 955489 = 716617) B716617
theorem B955523 : Blo 562809 955523 := bstep (se 1 (by rfl) ⟨716642, by rfl⟩ : syracuseStep 955523 = 1433285) B1433285
theorem B1807505 : Blo 562809 1807505 := bstep (se 2 (by rfl) ⟨677814, by rfl⟩ : syracuseStep 1807505 = 1355629) B1355629
theorem B955651 : Blo 562809 955651 := bstep (se 1 (by rfl) ⟨716738, by rfl⟩ : syracuseStep 955651 = 1433477) B1433477
theorem B955793 : Blo 562809 955793 := bstep (se 2 (by rfl) ⟨358422, by rfl⟩ : syracuseStep 955793 = 716845) B716845
theorem B1611181 : Blo 562809 1611181 := bstep (se 3 (by rfl) ⟨302096, by rfl⟩ : syracuseStep 1611181 = 604193) B604193
theorem B955921 : Blo 562809 955921 := bstep (se 2 (by rfl) ⟨358470, by rfl⟩ : syracuseStep 955921 = 716941) B716941
theorem B955955 : Blo 562809 955955 := bstep (se 1 (by rfl) ⟨716966, by rfl⟩ : syracuseStep 955955 = 1433933) B1433933
theorem B1906253 : Blo 562809 1906253 := bstep (se 3 (by rfl) ⟨357422, by rfl⟩ : syracuseStep 1906253 = 714845) B714845
theorem B562819 : Blo 562809 562819 := bstep (se 1 (by rfl) ⟨422114, by rfl⟩ : syracuseStep 562819 = 844229) B844229
theorem B1906307 : Blo 562809 1906307 := bstep (se 1 (by rfl) ⟨1429730, by rfl⟩ : syracuseStep 1906307 = 2859461) B2859461
theorem B1611409 : Blo 562809 1611409 := bstep (se 2 (by rfl) ⟨604278, by rfl⟩ : syracuseStep 1611409 = 1208557) B1208557
theorem B562835 : Blo 562809 562835 := bstep (se 1 (by rfl) ⟨422126, by rfl⟩ : syracuseStep 562835 = 844253) B844253
theorem B562851 : Blo 562809 562851 := bstep (se 1 (by rfl) ⟨422138, by rfl⟩ : syracuseStep 562851 = 844277) B844277
theorem B562867 : Blo 562809 562867 := bstep (se 1 (by rfl) ⟨422150, by rfl⟩ : syracuseStep 562867 = 844301) B844301
theorem B956083 : Blo 562809 956083 := bstep (se 1 (by rfl) ⟨717062, by rfl⟩ : syracuseStep 956083 = 1434125) B1434125
theorem B562883 : Blo 562809 562883 := bstep (se 1 (by rfl) ⟨422162, by rfl⟩ : syracuseStep 562883 = 844325) B844325
theorem B562899 : Blo 562809 562899 := bstep (se 1 (by rfl) ⟨422174, by rfl⟩ : syracuseStep 562899 = 844349) B844349
theorem B562915 : Blo 562809 562915 := bstep (se 1 (by rfl) ⟨422186, by rfl⟩ : syracuseStep 562915 = 844373) B844373
theorem B562931 : Blo 562809 562931 := bstep (se 1 (by rfl) ⟨422198, by rfl⟩ : syracuseStep 562931 = 844397) B844397
theorem B562947 : Blo 562809 562947 := bstep (se 1 (by rfl) ⟨422210, by rfl⟩ : syracuseStep 562947 = 844421) B844421
theorem B562963 : Blo 562809 562963 := bstep (se 1 (by rfl) ⟨422222, by rfl⟩ : syracuseStep 562963 = 844445) B844445
theorem B562979 : Blo 562809 562979 := bstep (se 1 (by rfl) ⟨422234, by rfl⟩ : syracuseStep 562979 = 844469) B844469
theorem B1611569 : Blo 562809 1611569 := bstep (se 2 (by rfl) ⟨604338, by rfl⟩ : syracuseStep 1611569 = 1208677) B1208677
theorem B562995 : Blo 562809 562995 := bstep (se 1 (by rfl) ⟨422246, by rfl⟩ : syracuseStep 562995 = 844493) B844493
theorem B956225 : Blo 562809 956225 := bstep (se 2 (by rfl) ⟨358584, by rfl⟩ : syracuseStep 956225 = 717169) B717169
theorem B563011 : Blo 562809 563011 := bstep (se 1 (by rfl) ⟨422258, by rfl⟩ : syracuseStep 563011 = 844517) B844517
theorem B563027 : Blo 562809 563027 := bstep (se 1 (by rfl) ⟨422270, by rfl⟩ : syracuseStep 563027 = 844541) B844541
theorem B563043 : Blo 562809 563043 := bstep (se 1 (by rfl) ⟨422282, by rfl⟩ : syracuseStep 563043 = 844565) B844565
theorem B3479395 : Blo 562809 3479395 := bstep (se 1 (by rfl) ⟨2609546, by rfl⟩ : syracuseStep 3479395 = 5219093) B5219093
theorem B563059 : Blo 562809 563059 := bstep (se 1 (by rfl) ⟨422294, by rfl⟩ : syracuseStep 563059 = 844589) B844589
theorem B563075 : Blo 562809 563075 := bstep (se 1 (by rfl) ⟨422306, by rfl⟩ : syracuseStep 563075 = 844613) B844613
theorem B1906577 : Blo 562809 1906577 := bstep (se 2 (by rfl) ⟨714966, by rfl⟩ : syracuseStep 1906577 = 1429933) B1429933
theorem B563091 : Blo 562809 563091 := bstep (se 1 (by rfl) ⟨422318, by rfl⟩ : syracuseStep 563091 = 844637) B844637
theorem B563107 : Blo 562809 563107 := bstep (se 1 (by rfl) ⟨422330, by rfl⟩ : syracuseStep 563107 = 844661) B844661
theorem B1611683 : Blo 562809 1611683 := bstep (se 1 (by rfl) ⟨1208762, by rfl⟩ : syracuseStep 1611683 = 2417525) B2417525
theorem B563123 : Blo 562809 563123 := bstep (se 1 (by rfl) ⟨422342, by rfl⟩ : syracuseStep 563123 = 844685) B844685
theorem B956353 : Blo 562809 956353 := bstep (se 2 (by rfl) ⟨358632, by rfl⟩ : syracuseStep 956353 = 717265) B717265
theorem B563139 : Blo 562809 563139 := bstep (se 1 (by rfl) ⟨422354, by rfl⟩ : syracuseStep 563139 = 844709) B844709
theorem B563155 : Blo 562809 563155 := bstep (se 1 (by rfl) ⟨422366, by rfl⟩ : syracuseStep 563155 = 844733) B844733
theorem B563171 : Blo 562809 563171 := bstep (se 1 (by rfl) ⟨422378, by rfl⟩ : syracuseStep 563171 = 844757) B844757
theorem B956387 : Blo 562809 956387 := bstep (se 1 (by rfl) ⟨717290, by rfl⟩ : syracuseStep 956387 = 1434581) B1434581
theorem B1808365 : Blo 562809 1808365 := bstep (se 3 (by rfl) ⟨339068, by rfl⟩ : syracuseStep 1808365 = 678137) B678137
theorem B563187 : Blo 562809 563187 := bstep (se 1 (by rfl) ⟨422390, by rfl⟩ : syracuseStep 563187 = 844781) B844781
theorem B563203 : Blo 562809 563203 := bstep (se 1 (by rfl) ⟨422402, by rfl⟩ : syracuseStep 563203 = 844805) B844805
theorem B563219 : Blo 562809 563219 := bstep (se 1 (by rfl) ⟨422414, by rfl⟩ : syracuseStep 563219 = 844829) B844829
theorem B563235 : Blo 562809 563235 := bstep (se 1 (by rfl) ⟨422426, by rfl⟩ : syracuseStep 563235 = 844853) B844853
theorem B563251 : Blo 562809 563251 := bstep (se 1 (by rfl) ⟨422438, by rfl⟩ : syracuseStep 563251 = 844877) B844877
theorem B563267 : Blo 562809 563267 := bstep (se 1 (by rfl) ⟨422450, by rfl⟩ : syracuseStep 563267 = 844901) B844901
theorem B563283 : Blo 562809 563283 := bstep (se 1 (by rfl) ⟨422462, by rfl⟩ : syracuseStep 563283 = 844925) B844925
theorem B563299 : Blo 562809 563299 := bstep (se 1 (by rfl) ⟨422474, by rfl⟩ : syracuseStep 563299 = 844949) B844949
theorem B563315 : Blo 562809 563315 := bstep (se 1 (by rfl) ⟨422486, by rfl⟩ : syracuseStep 563315 = 844973) B844973
theorem B563331 : Blo 562809 563331 := bstep (se 1 (by rfl) ⟨422498, by rfl⟩ : syracuseStep 563331 = 844997) B844997
theorem B563347 : Blo 562809 563347 := bstep (se 1 (by rfl) ⟨422510, by rfl⟩ : syracuseStep 563347 = 845021) B845021
theorem B563363 : Blo 562809 563363 := bstep (se 1 (by rfl) ⟨422522, by rfl⟩ : syracuseStep 563363 = 845045) B845045
theorem B563379 : Blo 562809 563379 := bstep (se 1 (by rfl) ⟨422534, by rfl⟩ : syracuseStep 563379 = 845069) B845069
theorem B563395 : Blo 562809 563395 := bstep (se 1 (by rfl) ⟨422546, by rfl⟩ : syracuseStep 563395 = 845093) B845093
theorem B563411 : Blo 562809 563411 := bstep (se 1 (by rfl) ⟨422558, by rfl⟩ : syracuseStep 563411 = 845117) B845117
theorem B563427 : Blo 562809 563427 := bstep (se 1 (by rfl) ⟨422570, by rfl⟩ : syracuseStep 563427 = 845141) B845141
theorem B563443 : Blo 562809 563443 := bstep (se 1 (by rfl) ⟨422582, by rfl⟩ : syracuseStep 563443 = 845165) B845165
theorem B563459 : Blo 562809 563459 := bstep (se 1 (by rfl) ⟨422594, by rfl⟩ : syracuseStep 563459 = 845189) B845189
theorem B563475 : Blo 562809 563475 := bstep (se 1 (by rfl) ⟨422606, by rfl⟩ : syracuseStep 563475 = 845213) B845213
theorem B563491 : Blo 562809 563491 := bstep (se 1 (by rfl) ⟨422618, by rfl⟩ : syracuseStep 563491 = 845237) B845237
theorem B563507 : Blo 562809 563507 := bstep (se 1 (by rfl) ⟨422630, by rfl⟩ : syracuseStep 563507 = 845261) B845261
theorem B1284419 : Blo 562809 1284419 := bstep (se 1 (by rfl) ⟨963314, by rfl⟩ : syracuseStep 1284419 = 1926629) B1926629
theorem B563523 : Blo 562809 563523 := bstep (se 1 (by rfl) ⟨422642, by rfl⟩ : syracuseStep 563523 = 845285) B845285
theorem B563539 : Blo 562809 563539 := bstep (se 1 (by rfl) ⟨422654, by rfl⟩ : syracuseStep 563539 = 845309) B845309
theorem B563555 : Blo 562809 563555 := bstep (se 1 (by rfl) ⟨422666, by rfl⟩ : syracuseStep 563555 = 845333) B845333
theorem B563571 : Blo 562809 563571 := bstep (se 1 (by rfl) ⟨422678, by rfl⟩ : syracuseStep 563571 = 845357) B845357
theorem B563587 : Blo 562809 563587 := bstep (se 1 (by rfl) ⟨422690, by rfl⟩ : syracuseStep 563587 = 845381) B845381
theorem B563603 : Blo 562809 563603 := bstep (se 1 (by rfl) ⟨422702, by rfl⟩ : syracuseStep 563603 = 845405) B845405
theorem B563619 : Blo 562809 563619 := bstep (se 1 (by rfl) ⟨422714, by rfl⟩ : syracuseStep 563619 = 845429) B845429
theorem B1907117 : Blo 562809 1907117 := bstep (se 3 (by rfl) ⟨357584, by rfl⟩ : syracuseStep 1907117 = 715169) B715169
theorem B563635 : Blo 562809 563635 := bstep (se 1 (by rfl) ⟨422726, by rfl⟩ : syracuseStep 563635 = 845453) B845453
theorem B563651 : Blo 562809 563651 := bstep (se 1 (by rfl) ⟨422738, by rfl⟩ : syracuseStep 563651 = 845477) B845477
theorem B563667 : Blo 562809 563667 := bstep (se 1 (by rfl) ⟨422750, by rfl⟩ : syracuseStep 563667 = 845501) B845501
theorem B563683 : Blo 562809 563683 := bstep (se 1 (by rfl) ⟨422762, by rfl⟩ : syracuseStep 563683 = 845525) B845525
theorem B1907171 : Blo 562809 1907171 := bstep (se 1 (by rfl) ⟨1430378, by rfl⟩ : syracuseStep 1907171 = 2860757) B2860757
theorem B563699 : Blo 562809 563699 := bstep (se 1 (by rfl) ⟨422774, by rfl⟩ : syracuseStep 563699 = 845549) B845549
theorem B563715 : Blo 562809 563715 := bstep (se 1 (by rfl) ⟨422786, by rfl⟩ : syracuseStep 563715 = 845573) B845573
theorem B563731 : Blo 562809 563731 := bstep (se 1 (by rfl) ⟨422798, by rfl⟩ : syracuseStep 563731 = 845597) B845597
theorem B563747 : Blo 562809 563747 := bstep (se 1 (by rfl) ⟨422810, by rfl⟩ : syracuseStep 563747 = 845621) B845621
theorem B563763 : Blo 562809 563763 := bstep (se 1 (by rfl) ⟨422822, by rfl⟩ : syracuseStep 563763 = 845645) B845645
theorem B563779 : Blo 562809 563779 := bstep (se 1 (by rfl) ⟨422834, by rfl⟩ : syracuseStep 563779 = 845669) B845669
theorem B563795 : Blo 562809 563795 := bstep (se 1 (by rfl) ⟨422846, by rfl⟩ : syracuseStep 563795 = 845693) B845693
theorem B563811 : Blo 562809 563811 := bstep (se 1 (by rfl) ⟨422858, by rfl⟩ : syracuseStep 563811 = 845717) B845717
theorem B563827 : Blo 562809 563827 := bstep (se 1 (by rfl) ⟨422870, by rfl⟩ : syracuseStep 563827 = 845741) B845741
theorem B563843 : Blo 562809 563843 := bstep (se 1 (by rfl) ⟨422882, by rfl⟩ : syracuseStep 563843 = 845765) B845765
theorem B563859 : Blo 562809 563859 := bstep (se 1 (by rfl) ⟨422894, by rfl⟩ : syracuseStep 563859 = 845789) B845789
theorem B563875 : Blo 562809 563875 := bstep (se 1 (by rfl) ⟨422906, by rfl⟩ : syracuseStep 563875 = 845813) B845813
theorem B563891 : Blo 562809 563891 := bstep (se 1 (by rfl) ⟨422918, by rfl⟩ : syracuseStep 563891 = 845837) B845837
theorem B563907 : Blo 562809 563907 := bstep (se 1 (by rfl) ⟨422930, by rfl⟩ : syracuseStep 563907 = 845861) B845861
theorem B563923 : Blo 562809 563923 := bstep (se 1 (by rfl) ⟨422942, by rfl⟩ : syracuseStep 563923 = 845885) B845885
theorem B563939 : Blo 562809 563939 := bstep (se 1 (by rfl) ⟨422954, by rfl⟩ : syracuseStep 563939 = 845909) B845909
theorem B1907441 : Blo 562809 1907441 := bstep (se 2 (by rfl) ⟨715290, by rfl⟩ : syracuseStep 1907441 = 1430581) B1430581
theorem B563955 : Blo 562809 563955 := bstep (se 1 (by rfl) ⟨422966, by rfl⟩ : syracuseStep 563955 = 845933) B845933
theorem B563971 : Blo 562809 563971 := bstep (se 1 (by rfl) ⟨422978, by rfl⟩ : syracuseStep 563971 = 845957) B845957
theorem B563987 : Blo 562809 563987 := bstep (se 1 (by rfl) ⟨422990, by rfl⟩ : syracuseStep 563987 = 845981) B845981
theorem B564003 : Blo 562809 564003 := bstep (se 1 (by rfl) ⟨423002, by rfl⟩ : syracuseStep 564003 = 846005) B846005
theorem B564019 : Blo 562809 564019 := bstep (se 1 (by rfl) ⟨423014, by rfl⟩ : syracuseStep 564019 = 846029) B846029
theorem B662323 : Blo 562809 662323 := bstep (se 1 (by rfl) ⟨496742, by rfl⟩ : syracuseStep 662323 = 993485) B993485
theorem B564035 : Blo 562809 564035 := bstep (se 1 (by rfl) ⟨423026, by rfl⟩ : syracuseStep 564035 = 846053) B846053
theorem B564051 : Blo 562809 564051 := bstep (se 1 (by rfl) ⟨423038, by rfl⟩ : syracuseStep 564051 = 846077) B846077
theorem B564067 : Blo 562809 564067 := bstep (se 1 (by rfl) ⟨423050, by rfl⟩ : syracuseStep 564067 = 846101) B846101
theorem B2857841 : Blo 562809 2857841 := bstep (se 2 (by rfl) ⟨1071690, by rfl⟩ : syracuseStep 2857841 = 2143381) B2143381
theorem B564083 : Blo 562809 564083 := bstep (se 1 (by rfl) ⟨423062, by rfl⟩ : syracuseStep 564083 = 846125) B846125
theorem B564099 : Blo 562809 564099 := bstep (se 1 (by rfl) ⟨423074, by rfl⟩ : syracuseStep 564099 = 846149) B846149
theorem B1612685 : Blo 562809 1612685 := bstep (se 3 (by rfl) ⟨302378, by rfl⟩ : syracuseStep 1612685 = 604757) B604757
theorem B564115 : Blo 562809 564115 := bstep (se 1 (by rfl) ⟨423086, by rfl⟩ : syracuseStep 564115 = 846173) B846173
theorem B564131 : Blo 562809 564131 := bstep (se 1 (by rfl) ⟨423098, by rfl⟩ : syracuseStep 564131 = 846197) B846197
theorem B2038691 : Blo 562809 2038691 := bstep (se 1 (by rfl) ⟨1529018, by rfl⟩ : syracuseStep 2038691 = 3058037) B3058037
theorem B564147 : Blo 562809 564147 := bstep (se 1 (by rfl) ⟨423110, by rfl⟩ : syracuseStep 564147 = 846221) B846221
theorem B564163 : Blo 562809 564163 := bstep (se 1 (by rfl) ⟨423122, by rfl⟩ : syracuseStep 564163 = 846245) B846245
theorem B564179 : Blo 562809 564179 := bstep (se 1 (by rfl) ⟨423134, by rfl⟩ : syracuseStep 564179 = 846269) B846269
theorem B760801 : Blo 562809 760801 := bstep (se 2 (by rfl) ⟨285300, by rfl⟩ : syracuseStep 760801 = 570601) B570601
theorem B564195 : Blo 562809 564195 := bstep (se 1 (by rfl) ⟨423146, by rfl⟩ : syracuseStep 564195 = 846293) B846293
theorem B564211 : Blo 562809 564211 := bstep (se 1 (by rfl) ⟨423158, by rfl⟩ : syracuseStep 564211 = 846317) B846317
theorem B564227 : Blo 562809 564227 := bstep (se 1 (by rfl) ⟨423170, by rfl⟩ : syracuseStep 564227 = 846341) B846341
theorem B564243 : Blo 562809 564243 := bstep (se 1 (by rfl) ⟨423182, by rfl⟩ : syracuseStep 564243 = 846365) B846365
theorem B564259 : Blo 562809 564259 := bstep (se 1 (by rfl) ⟨423194, by rfl⟩ : syracuseStep 564259 = 846389) B846389
theorem B564275 : Blo 562809 564275 := bstep (se 1 (by rfl) ⟨423206, by rfl⟩ : syracuseStep 564275 = 846413) B846413
theorem B564291 : Blo 562809 564291 := bstep (se 1 (by rfl) ⟨423218, by rfl⟩ : syracuseStep 564291 = 846437) B846437
theorem B1612867 : Blo 562809 1612867 := bstep (se 1 (by rfl) ⟨1209650, by rfl⟩ : syracuseStep 1612867 = 2419301) B2419301
theorem B564307 : Blo 562809 564307 := bstep (se 1 (by rfl) ⟨423230, by rfl⟩ : syracuseStep 564307 = 846461) B846461
theorem B564323 : Blo 562809 564323 := bstep (se 1 (by rfl) ⟨423242, by rfl⟩ : syracuseStep 564323 = 846485) B846485
theorem B564339 : Blo 562809 564339 := bstep (se 1 (by rfl) ⟨423254, by rfl⟩ : syracuseStep 564339 = 846509) B846509
theorem B564355 : Blo 562809 564355 := bstep (se 1 (by rfl) ⟨423266, by rfl⟩ : syracuseStep 564355 = 846533) B846533
theorem B564371 : Blo 562809 564371 := bstep (se 1 (by rfl) ⟨423278, by rfl⟩ : syracuseStep 564371 = 846557) B846557
theorem B564387 : Blo 562809 564387 := bstep (se 1 (by rfl) ⟨423290, by rfl⟩ : syracuseStep 564387 = 846581) B846581
theorem B564403 : Blo 562809 564403 := bstep (se 1 (by rfl) ⟨423302, by rfl⟩ : syracuseStep 564403 = 846605) B846605
theorem B564419 : Blo 562809 564419 := bstep (se 1 (by rfl) ⟨423314, by rfl⟩ : syracuseStep 564419 = 846629) B846629
theorem B564435 : Blo 562809 564435 := bstep (se 1 (by rfl) ⟨423326, by rfl⟩ : syracuseStep 564435 = 846653) B846653
theorem B564451 : Blo 562809 564451 := bstep (se 1 (by rfl) ⟨423338, by rfl⟩ : syracuseStep 564451 = 846677) B846677
theorem B1613027 : Blo 562809 1613027 := bstep (se 1 (by rfl) ⟨1209770, by rfl⟩ : syracuseStep 1613027 = 2419541) B2419541
theorem B564467 : Blo 562809 564467 := bstep (se 1 (by rfl) ⟨423350, by rfl⟩ : syracuseStep 564467 = 846701) B846701
theorem B564483 : Blo 562809 564483 := bstep (se 1 (by rfl) ⟨423362, by rfl⟩ : syracuseStep 564483 = 846725) B846725
theorem B1907981 : Blo 562809 1907981 := bstep (se 3 (by rfl) ⟨357746, by rfl⟩ : syracuseStep 1907981 = 715493) B715493
theorem B564499 : Blo 562809 564499 := bstep (se 1 (by rfl) ⟨423374, by rfl⟩ : syracuseStep 564499 = 846749) B846749
theorem B564515 : Blo 562809 564515 := bstep (se 1 (by rfl) ⟨423386, by rfl⟩ : syracuseStep 564515 = 846773) B846773
theorem B564531 : Blo 562809 564531 := bstep (se 1 (by rfl) ⟨423398, by rfl⟩ : syracuseStep 564531 = 846797) B846797
theorem B564547 : Blo 562809 564547 := bstep (se 1 (by rfl) ⟨423410, by rfl⟩ : syracuseStep 564547 = 846821) B846821
theorem B1908035 : Blo 562809 1908035 := bstep (se 1 (by rfl) ⟨1431026, by rfl⟩ : syracuseStep 1908035 = 2862053) B2862053
theorem B564563 : Blo 562809 564563 := bstep (se 1 (by rfl) ⟨423422, by rfl⟩ : syracuseStep 564563 = 846845) B846845
theorem B564579 : Blo 562809 564579 := bstep (se 1 (by rfl) ⟨423434, by rfl⟩ : syracuseStep 564579 = 846869) B846869
theorem B564595 : Blo 562809 564595 := bstep (se 1 (by rfl) ⟨423446, by rfl⟩ : syracuseStep 564595 = 846893) B846893
theorem B564611 : Blo 562809 564611 := bstep (se 1 (by rfl) ⟨423458, by rfl⟩ : syracuseStep 564611 = 846917) B846917
theorem B564627 : Blo 562809 564627 := bstep (se 1 (by rfl) ⟨423470, by rfl⟩ : syracuseStep 564627 = 846941) B846941
theorem B564643 : Blo 562809 564643 := bstep (se 1 (by rfl) ⟨423482, by rfl⟩ : syracuseStep 564643 = 846965) B846965
theorem B564659 : Blo 562809 564659 := bstep (se 1 (by rfl) ⟨423494, by rfl⟩ : syracuseStep 564659 = 846989) B846989
theorem B564675 : Blo 562809 564675 := bstep (se 1 (by rfl) ⟨423506, by rfl⟩ : syracuseStep 564675 = 847013) B847013
theorem B2137549 : Blo 562809 2137549 := bstep (se 3 (by rfl) ⟨400790, by rfl⟩ : syracuseStep 2137549 = 801581) B801581
theorem B564691 : Blo 562809 564691 := bstep (se 1 (by rfl) ⟨423518, by rfl⟩ : syracuseStep 564691 = 847037) B847037
theorem B564707 : Blo 562809 564707 := bstep (se 1 (by rfl) ⟨423530, by rfl⟩ : syracuseStep 564707 = 847061) B847061
theorem B4070897 : Blo 562809 4070897 := bstep (se 2 (by rfl) ⟨1526586, by rfl⟩ : syracuseStep 4070897 = 3053173) B3053173
theorem B564723 : Blo 562809 564723 := bstep (se 1 (by rfl) ⟨423542, by rfl⟩ : syracuseStep 564723 = 847085) B847085
theorem B564739 : Blo 562809 564739 := bstep (se 1 (by rfl) ⟨423554, by rfl⟩ : syracuseStep 564739 = 847109) B847109
theorem B564755 : Blo 562809 564755 := bstep (se 1 (by rfl) ⟨423566, by rfl⟩ : syracuseStep 564755 = 847133) B847133
theorem B564771 : Blo 562809 564771 := bstep (se 1 (by rfl) ⟨423578, by rfl⟩ : syracuseStep 564771 = 847157) B847157
theorem B1809965 : Blo 562809 1809965 := bstep (se 3 (by rfl) ⟨339368, by rfl⟩ : syracuseStep 1809965 = 678737) B678737
theorem B564787 : Blo 562809 564787 := bstep (se 1 (by rfl) ⟨423590, by rfl⟩ : syracuseStep 564787 = 847181) B847181
theorem B564803 : Blo 562809 564803 := bstep (se 1 (by rfl) ⟨423602, by rfl⟩ : syracuseStep 564803 = 847205) B847205
theorem B1908305 : Blo 562809 1908305 := bstep (se 2 (by rfl) ⟨715614, by rfl⟩ : syracuseStep 1908305 = 1431229) B1431229
theorem B564819 : Blo 562809 564819 := bstep (se 1 (by rfl) ⟨423614, by rfl⟩ : syracuseStep 564819 = 847229) B847229
theorem B564835 : Blo 562809 564835 := bstep (se 1 (by rfl) ⟨423626, by rfl⟩ : syracuseStep 564835 = 847253) B847253
theorem B564851 : Blo 562809 564851 := bstep (se 1 (by rfl) ⟨423638, by rfl⟩ : syracuseStep 564851 = 847277) B847277
theorem B564867 : Blo 562809 564867 := bstep (se 1 (by rfl) ⟨423650, by rfl⟩ : syracuseStep 564867 = 847301) B847301
theorem B564883 : Blo 562809 564883 := bstep (se 1 (by rfl) ⟨423662, by rfl⟩ : syracuseStep 564883 = 847325) B847325
theorem B564899 : Blo 562809 564899 := bstep (se 1 (by rfl) ⟨423674, by rfl⟩ : syracuseStep 564899 = 847349) B847349
theorem B564915 : Blo 562809 564915 := bstep (se 1 (by rfl) ⟨423686, by rfl⟩ : syracuseStep 564915 = 847373) B847373
theorem B564931 : Blo 562809 564931 := bstep (se 1 (by rfl) ⟨423698, by rfl⟩ : syracuseStep 564931 = 847397) B847397
theorem B564947 : Blo 562809 564947 := bstep (se 1 (by rfl) ⟨423710, by rfl⟩ : syracuseStep 564947 = 847421) B847421
theorem B564963 : Blo 562809 564963 := bstep (se 1 (by rfl) ⟨423722, by rfl⟩ : syracuseStep 564963 = 847445) B847445
theorem B564979 : Blo 562809 564979 := bstep (se 1 (by rfl) ⟨423734, by rfl⟩ : syracuseStep 564979 = 847469) B847469
theorem B564995 : Blo 562809 564995 := bstep (se 1 (by rfl) ⟨423746, by rfl⟩ : syracuseStep 564995 = 847493) B847493
theorem B565011 : Blo 562809 565011 := bstep (se 1 (by rfl) ⟨423758, by rfl⟩ : syracuseStep 565011 = 847517) B847517
theorem B565027 : Blo 562809 565027 := bstep (se 1 (by rfl) ⟨423770, by rfl⟩ : syracuseStep 565027 = 847541) B847541
theorem B565043 : Blo 562809 565043 := bstep (se 1 (by rfl) ⟨423782, by rfl⟩ : syracuseStep 565043 = 847565) B847565
theorem B565059 : Blo 562809 565059 := bstep (se 1 (by rfl) ⟨423794, by rfl⟩ : syracuseStep 565059 = 847589) B847589
theorem B4300613 : Blo 562809 4300613 := bstep (se 4 (by rfl) ⟨403182, by rfl⟩ : syracuseStep 4300613 = 806365) B806365
theorem B565075 : Blo 562809 565075 := bstep (se 1 (by rfl) ⟨423806, by rfl⟩ : syracuseStep 565075 = 847613) B847613
theorem B565091 : Blo 562809 565091 := bstep (se 1 (by rfl) ⟨423818, by rfl⟩ : syracuseStep 565091 = 847637) B847637
theorem B565107 : Blo 562809 565107 := bstep (se 1 (by rfl) ⟨423830, by rfl⟩ : syracuseStep 565107 = 847661) B847661
theorem B565123 : Blo 562809 565123 := bstep (se 1 (by rfl) ⟨423842, by rfl⟩ : syracuseStep 565123 = 847685) B847685
theorem B3710861 : Blo 562809 3710861 := bstep (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) B1391573
theorem B565139 : Blo 562809 565139 := bstep (se 1 (by rfl) ⟨423854, by rfl⟩ : syracuseStep 565139 = 847709) B847709
theorem B565155 : Blo 562809 565155 := bstep (se 1 (by rfl) ⟨423866, by rfl⟩ : syracuseStep 565155 = 847733) B847733
theorem B565171 : Blo 562809 565171 := bstep (se 1 (by rfl) ⟨423878, by rfl⟩ : syracuseStep 565171 = 847757) B847757
theorem B565187 : Blo 562809 565187 := bstep (se 1 (by rfl) ⟨423890, by rfl⟩ : syracuseStep 565187 = 847781) B847781
theorem B565203 : Blo 562809 565203 := bstep (se 1 (by rfl) ⟨423902, by rfl⟩ : syracuseStep 565203 = 847805) B847805
theorem B565219 : Blo 562809 565219 := bstep (se 1 (by rfl) ⟨423914, by rfl⟩ : syracuseStep 565219 = 847829) B847829
theorem B565235 : Blo 562809 565235 := bstep (se 1 (by rfl) ⟨423926, by rfl⟩ : syracuseStep 565235 = 847853) B847853
theorem B565251 : Blo 562809 565251 := bstep (se 1 (by rfl) ⟨423938, by rfl⟩ : syracuseStep 565251 = 847877) B847877
theorem B565267 : Blo 562809 565267 := bstep (se 1 (by rfl) ⟨423950, by rfl⟩ : syracuseStep 565267 = 847901) B847901
theorem B565283 : Blo 562809 565283 := bstep (se 1 (by rfl) ⟨423962, by rfl⟩ : syracuseStep 565283 = 847925) B847925
theorem B860195 : Blo 562809 860195 := bstep (se 1 (by rfl) ⟨645146, by rfl⟩ : syracuseStep 860195 = 1290293) B1290293
theorem B565299 : Blo 562809 565299 := bstep (se 1 (by rfl) ⟨423974, by rfl⟩ : syracuseStep 565299 = 847949) B847949
theorem B565315 : Blo 562809 565315 := bstep (se 1 (by rfl) ⟨423986, by rfl⟩ : syracuseStep 565315 = 847973) B847973
theorem B565331 : Blo 562809 565331 := bstep (se 1 (by rfl) ⟨423998, by rfl⟩ : syracuseStep 565331 = 847997) B847997
theorem B565347 : Blo 562809 565347 := bstep (se 1 (by rfl) ⟨424010, by rfl⟩ : syracuseStep 565347 = 848021) B848021
theorem B1908845 : Blo 562809 1908845 := bstep (se 3 (by rfl) ⟨357908, by rfl⟩ : syracuseStep 1908845 = 715817) B715817
theorem B565363 : Blo 562809 565363 := bstep (se 1 (by rfl) ⟨424022, by rfl⟩ : syracuseStep 565363 = 848045) B848045
theorem B565379 : Blo 562809 565379 := bstep (se 1 (by rfl) ⟨424034, by rfl⟩ : syracuseStep 565379 = 848069) B848069
theorem B565395 : Blo 562809 565395 := bstep (se 1 (by rfl) ⟨424046, by rfl⟩ : syracuseStep 565395 = 848093) B848093
theorem B565411 : Blo 562809 565411 := bstep (se 1 (by rfl) ⟨424058, by rfl⟩ : syracuseStep 565411 = 848117) B848117
theorem B1908899 : Blo 562809 1908899 := bstep (se 1 (by rfl) ⟨1431674, by rfl⟩ : syracuseStep 1908899 = 2863349) B2863349
theorem B565427 : Blo 562809 565427 := bstep (se 1 (by rfl) ⟨424070, by rfl⟩ : syracuseStep 565427 = 848141) B848141
theorem B565443 : Blo 562809 565443 := bstep (se 1 (by rfl) ⟨424082, by rfl⟩ : syracuseStep 565443 = 848165) B848165
theorem B565459 : Blo 562809 565459 := bstep (se 1 (by rfl) ⟨424094, by rfl⟩ : syracuseStep 565459 = 848189) B848189
theorem B2138339 : Blo 562809 2138339 := bstep (se 1 (by rfl) ⟨1603754, by rfl⟩ : syracuseStep 2138339 = 3207509) B3207509
theorem B565475 : Blo 562809 565475 := bstep (se 1 (by rfl) ⟨424106, by rfl⟩ : syracuseStep 565475 = 848213) B848213
theorem B565491 : Blo 562809 565491 := bstep (se 1 (by rfl) ⟨424118, by rfl⟩ : syracuseStep 565491 = 848237) B848237
theorem B1712387 : Blo 562809 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B565507 : Blo 562809 565507 := bstep (se 1 (by rfl) ⟨424130, by rfl⟩ : syracuseStep 565507 = 848261) B848261
theorem B565523 : Blo 562809 565523 := bstep (se 1 (by rfl) ⟨424142, by rfl⟩ : syracuseStep 565523 = 848285) B848285
theorem B2859299 : Blo 562809 2859299 := bstep (se 1 (by rfl) ⟨2144474, by rfl⟩ : syracuseStep 2859299 = 4288949) B4288949
theorem B565539 : Blo 562809 565539 := bstep (se 1 (by rfl) ⟨424154, by rfl⟩ : syracuseStep 565539 = 848309) B848309
theorem B565555 : Blo 562809 565555 := bstep (se 1 (by rfl) ⟨424166, by rfl⟩ : syracuseStep 565555 = 848333) B848333
theorem B565571 : Blo 562809 565571 := bstep (se 1 (by rfl) ⟨424178, by rfl⟩ : syracuseStep 565571 = 848357) B848357
theorem B565587 : Blo 562809 565587 := bstep (se 1 (by rfl) ⟨424190, by rfl⟩ : syracuseStep 565587 = 848381) B848381
theorem B565603 : Blo 562809 565603 := bstep (se 1 (by rfl) ⟨424202, by rfl⟩ : syracuseStep 565603 = 848405) B848405
theorem B8954225 : Blo 562809 8954225 := bstep (se 2 (by rfl) ⟨3357834, by rfl⟩ : syracuseStep 8954225 = 6715669) B6715669
theorem B565619 : Blo 562809 565619 := bstep (se 1 (by rfl) ⟨424214, by rfl⟩ : syracuseStep 565619 = 848429) B848429
theorem B565635 : Blo 562809 565635 := bstep (se 1 (by rfl) ⟨424226, by rfl⟩ : syracuseStep 565635 = 848453) B848453
theorem B3613061 : Blo 562809 3613061 := bstep (se 4 (by rfl) ⟨338724, by rfl⟩ : syracuseStep 3613061 = 677449) B677449
theorem B565651 : Blo 562809 565651 := bstep (se 1 (by rfl) ⟨424238, by rfl⟩ : syracuseStep 565651 = 848477) B848477
theorem B565667 : Blo 562809 565667 := bstep (se 1 (by rfl) ⟨424250, by rfl⟩ : syracuseStep 565667 = 848501) B848501
theorem B1909169 : Blo 562809 1909169 := bstep (se 2 (by rfl) ⟨715938, by rfl⟩ : syracuseStep 1909169 = 1431877) B1431877
theorem B565683 : Blo 562809 565683 := bstep (se 1 (by rfl) ⟨424262, by rfl⟩ : syracuseStep 565683 = 848525) B848525
theorem B565699 : Blo 562809 565699 := bstep (se 1 (by rfl) ⟨424274, by rfl⟩ : syracuseStep 565699 = 848549) B848549
theorem B565715 : Blo 562809 565715 := bstep (se 1 (by rfl) ⟨424286, by rfl⟩ : syracuseStep 565715 = 848573) B848573
theorem B565731 : Blo 562809 565731 := bstep (se 1 (by rfl) ⟨424298, by rfl⟩ : syracuseStep 565731 = 848597) B848597
theorem B565747 : Blo 562809 565747 := bstep (se 1 (by rfl) ⟨424310, by rfl⟩ : syracuseStep 565747 = 848621) B848621
theorem B565763 : Blo 562809 565763 := bstep (se 1 (by rfl) ⟨424322, by rfl⟩ : syracuseStep 565763 = 848645) B848645
theorem B565779 : Blo 562809 565779 := bstep (se 1 (by rfl) ⟨424334, by rfl⟩ : syracuseStep 565779 = 848669) B848669
theorem B565795 : Blo 562809 565795 := bstep (se 1 (by rfl) ⟨424346, by rfl⟩ : syracuseStep 565795 = 848693) B848693
theorem B565811 : Blo 562809 565811 := bstep (se 1 (by rfl) ⟨424358, by rfl⟩ : syracuseStep 565811 = 848717) B848717
theorem B565827 : Blo 562809 565827 := bstep (se 1 (by rfl) ⟨424370, by rfl⟩ : syracuseStep 565827 = 848741) B848741
theorem B565843 : Blo 562809 565843 := bstep (se 1 (by rfl) ⟨424382, by rfl⟩ : syracuseStep 565843 = 848765) B848765
theorem B565859 : Blo 562809 565859 := bstep (se 1 (by rfl) ⟨424394, by rfl⟩ : syracuseStep 565859 = 848789) B848789
theorem B2892401 : Blo 562809 2892401 := bstep (se 2 (by rfl) ⟨1084650, by rfl⟩ : syracuseStep 2892401 = 2169301) B2169301
theorem B565875 : Blo 562809 565875 := bstep (se 1 (by rfl) ⟨424406, by rfl⟩ : syracuseStep 565875 = 848813) B848813
theorem B565891 : Blo 562809 565891 := bstep (se 1 (by rfl) ⟨424418, by rfl⟩ : syracuseStep 565891 = 848837) B848837
theorem B1548941 : Blo 562809 1548941 := bstep (se 3 (by rfl) ⟨290426, by rfl⟩ : syracuseStep 1548941 = 580853) B580853
theorem B565907 : Blo 562809 565907 := bstep (se 1 (by rfl) ⟨424430, by rfl⟩ : syracuseStep 565907 = 848861) B848861
theorem B565923 : Blo 562809 565923 := bstep (se 1 (by rfl) ⟨424442, by rfl⟩ : syracuseStep 565923 = 848885) B848885
theorem B565939 : Blo 562809 565939 := bstep (se 1 (by rfl) ⟨424454, by rfl⟩ : syracuseStep 565939 = 848909) B848909
theorem B565955 : Blo 562809 565955 := bstep (se 1 (by rfl) ⟨424466, by rfl⟩ : syracuseStep 565955 = 848933) B848933
theorem B565971 : Blo 562809 565971 := bstep (se 1 (by rfl) ⟨424478, by rfl⟩ : syracuseStep 565971 = 848957) B848957
theorem B565987 : Blo 562809 565987 := bstep (se 1 (by rfl) ⟨424490, by rfl⟩ : syracuseStep 565987 = 848981) B848981
theorem B566003 : Blo 562809 566003 := bstep (se 1 (by rfl) ⟨424502, by rfl⟩ : syracuseStep 566003 = 849005) B849005
theorem B566019 : Blo 562809 566019 := bstep (se 1 (by rfl) ⟨424514, by rfl⟩ : syracuseStep 566019 = 849029) B849029
theorem B566035 : Blo 562809 566035 := bstep (se 1 (by rfl) ⟨424526, by rfl⟩ : syracuseStep 566035 = 849053) B849053
theorem B566051 : Blo 562809 566051 := bstep (se 1 (by rfl) ⟨424538, by rfl⟩ : syracuseStep 566051 = 849077) B849077
theorem B566067 : Blo 562809 566067 := bstep (se 1 (by rfl) ⟨424550, by rfl⟩ : syracuseStep 566067 = 849101) B849101
theorem B566083 : Blo 562809 566083 := bstep (se 1 (by rfl) ⟨424562, by rfl⟩ : syracuseStep 566083 = 849125) B849125
theorem B566099 : Blo 562809 566099 := bstep (se 1 (by rfl) ⟨424574, by rfl⟩ : syracuseStep 566099 = 849149) B849149
theorem B566115 : Blo 562809 566115 := bstep (se 1 (by rfl) ⟨424586, by rfl⟩ : syracuseStep 566115 = 849173) B849173
theorem B2138993 : Blo 562809 2138993 := bstep (se 2 (by rfl) ⟨802122, by rfl⟩ : syracuseStep 2138993 = 1604245) B1604245
theorem B566131 : Blo 562809 566131 := bstep (se 1 (by rfl) ⟨424598, by rfl⟩ : syracuseStep 566131 = 849197) B849197
theorem B566147 : Blo 562809 566147 := bstep (se 1 (by rfl) ⟨424610, by rfl⟩ : syracuseStep 566147 = 849221) B849221
theorem B3220357 : Blo 562809 3220357 := bstep (se 4 (by rfl) ⟨301908, by rfl⟩ : syracuseStep 3220357 = 603817) B603817
theorem B566163 : Blo 562809 566163 := bstep (se 1 (by rfl) ⟨424622, by rfl⟩ : syracuseStep 566163 = 849245) B849245
theorem B566179 : Blo 562809 566179 := bstep (se 1 (by rfl) ⟨424634, by rfl⟩ : syracuseStep 566179 = 849269) B849269
theorem B566195 : Blo 562809 566195 := bstep (se 1 (by rfl) ⟨424646, by rfl⟩ : syracuseStep 566195 = 849293) B849293
theorem B566211 : Blo 562809 566211 := bstep (se 1 (by rfl) ⟨424658, by rfl⟩ : syracuseStep 566211 = 849317) B849317
theorem B1909709 : Blo 562809 1909709 := bstep (se 3 (by rfl) ⟨358070, by rfl⟩ : syracuseStep 1909709 = 716141) B716141
theorem B566227 : Blo 562809 566227 := bstep (se 1 (by rfl) ⟨424670, by rfl⟩ : syracuseStep 566227 = 849341) B849341
theorem B566243 : Blo 562809 566243 := bstep (se 1 (by rfl) ⟨424682, by rfl⟩ : syracuseStep 566243 = 849365) B849365
theorem B566259 : Blo 562809 566259 := bstep (se 1 (by rfl) ⟨424694, by rfl⟩ : syracuseStep 566259 = 849389) B849389
theorem B1909763 : Blo 562809 1909763 := bstep (se 1 (by rfl) ⟨1432322, by rfl⟩ : syracuseStep 1909763 = 2864645) B2864645
theorem B566275 : Blo 562809 566275 := bstep (se 1 (by rfl) ⟨424706, by rfl⟩ : syracuseStep 566275 = 849413) B849413
theorem B566291 : Blo 562809 566291 := bstep (se 1 (by rfl) ⟨424718, by rfl⟩ : syracuseStep 566291 = 849437) B849437
theorem B566307 : Blo 562809 566307 := bstep (se 1 (by rfl) ⟨424730, by rfl⟩ : syracuseStep 566307 = 849461) B849461
theorem B2040881 : Blo 562809 2040881 := bstep (se 2 (by rfl) ⟨765330, by rfl⟩ : syracuseStep 2040881 = 1530661) B1530661
theorem B566323 : Blo 562809 566323 := bstep (se 1 (by rfl) ⟨424742, by rfl⟩ : syracuseStep 566323 = 849485) B849485
theorem B566339 : Blo 562809 566339 := bstep (se 1 (by rfl) ⟨424754, by rfl⟩ : syracuseStep 566339 = 849509) B849509
theorem B2860109 : Blo 562809 2860109 := bstep (se 3 (by rfl) ⟨536270, by rfl⟩ : syracuseStep 2860109 = 1072541) B1072541
theorem B566355 : Blo 562809 566355 := bstep (se 1 (by rfl) ⟨424766, by rfl⟩ : syracuseStep 566355 = 849533) B849533
theorem B1811555 : Blo 562809 1811555 := bstep (se 1 (by rfl) ⟨1358666, by rfl⟩ : syracuseStep 1811555 = 2717333) B2717333
theorem B566371 : Blo 562809 566371 := bstep (se 1 (by rfl) ⟨424778, by rfl⟩ : syracuseStep 566371 = 849557) B849557
theorem B566387 : Blo 562809 566387 := bstep (se 1 (by rfl) ⟨424790, by rfl⟩ : syracuseStep 566387 = 849581) B849581
theorem B566403 : Blo 562809 566403 := bstep (se 1 (by rfl) ⟨424802, by rfl⟩ : syracuseStep 566403 = 849605) B849605
theorem B566419 : Blo 562809 566419 := bstep (se 1 (by rfl) ⟨424814, by rfl⟩ : syracuseStep 566419 = 849629) B849629
theorem B566435 : Blo 562809 566435 := bstep (se 1 (by rfl) ⟨424826, by rfl⟩ : syracuseStep 566435 = 849653) B849653
theorem B566451 : Blo 562809 566451 := bstep (se 1 (by rfl) ⟨424838, by rfl⟩ : syracuseStep 566451 = 849677) B849677
theorem B1352899 : Blo 562809 1352899 := bstep (se 1 (by rfl) ⟨1014674, by rfl⟩ : syracuseStep 1352899 = 2029349) B2029349
theorem B566467 : Blo 562809 566467 := bstep (se 1 (by rfl) ⟨424850, by rfl⟩ : syracuseStep 566467 = 849701) B849701
theorem B566483 : Blo 562809 566483 := bstep (se 1 (by rfl) ⟨424862, by rfl⟩ : syracuseStep 566483 = 849725) B849725
theorem B566499 : Blo 562809 566499 := bstep (se 1 (by rfl) ⟨424874, by rfl⟩ : syracuseStep 566499 = 849749) B849749
theorem B763121 : Blo 562809 763121 := bstep (se 2 (by rfl) ⟨286170, by rfl⟩ : syracuseStep 763121 = 572341) B572341
theorem B566515 : Blo 562809 566515 := bstep (se 1 (by rfl) ⟨424886, by rfl⟩ : syracuseStep 566515 = 849773) B849773
theorem B566531 : Blo 562809 566531 := bstep (se 1 (by rfl) ⟨424898, by rfl⟩ : syracuseStep 566531 = 849797) B849797
theorem B1713421 : Blo 562809 1713421 := bstep (se 3 (by rfl) ⟨321266, by rfl⟩ : syracuseStep 1713421 = 642533) B642533
theorem B1910033 : Blo 562809 1910033 := bstep (se 2 (by rfl) ⟨716262, by rfl⟩ : syracuseStep 1910033 = 1432525) B1432525
theorem B566547 : Blo 562809 566547 := bstep (se 1 (by rfl) ⟨424910, by rfl⟩ : syracuseStep 566547 = 849821) B849821
theorem B1811747 : Blo 562809 1811747 := bstep (se 1 (by rfl) ⟨1358810, by rfl⟩ : syracuseStep 1811747 = 2717621) B2717621
theorem B566563 : Blo 562809 566563 := bstep (se 1 (by rfl) ⟨424922, by rfl⟩ : syracuseStep 566563 = 849845) B849845
theorem B566579 : Blo 562809 566579 := bstep (se 1 (by rfl) ⟨424934, by rfl⟩ : syracuseStep 566579 = 849869) B849869
theorem B566595 : Blo 562809 566595 := bstep (se 1 (by rfl) ⟨424946, by rfl⟩ : syracuseStep 566595 = 849893) B849893
theorem B566611 : Blo 562809 566611 := bstep (se 1 (by rfl) ⟨424958, by rfl⟩ : syracuseStep 566611 = 849917) B849917
theorem B566627 : Blo 562809 566627 := bstep (se 1 (by rfl) ⟨424970, by rfl⟩ : syracuseStep 566627 = 849941) B849941
theorem B566643 : Blo 562809 566643 := bstep (se 1 (by rfl) ⟨424982, by rfl⟩ : syracuseStep 566643 = 849965) B849965
theorem B566659 : Blo 562809 566659 := bstep (se 1 (by rfl) ⟨424994, by rfl⟩ : syracuseStep 566659 = 849989) B849989
theorem B1222033 : Blo 562809 1222033 := bstep (se 2 (by rfl) ⟨458262, by rfl⟩ : syracuseStep 1222033 = 916525) B916525
theorem B566675 : Blo 562809 566675 := bstep (se 1 (by rfl) ⟨425006, by rfl⟩ : syracuseStep 566675 = 850013) B850013
theorem B566691 : Blo 562809 566691 := bstep (se 1 (by rfl) ⟨425018, by rfl⟩ : syracuseStep 566691 = 850037) B850037
theorem B566707 : Blo 562809 566707 := bstep (se 1 (by rfl) ⟨425030, by rfl⟩ : syracuseStep 566707 = 850061) B850061
theorem B566723 : Blo 562809 566723 := bstep (se 1 (by rfl) ⟨425042, by rfl⟩ : syracuseStep 566723 = 850085) B850085
theorem B566739 : Blo 562809 566739 := bstep (se 1 (by rfl) ⟨425054, by rfl⟩ : syracuseStep 566739 = 850109) B850109
theorem B566755 : Blo 562809 566755 := bstep (se 1 (by rfl) ⟨425066, by rfl⟩ : syracuseStep 566755 = 850133) B850133
theorem B566771 : Blo 562809 566771 := bstep (se 1 (by rfl) ⟨425078, by rfl⟩ : syracuseStep 566771 = 850157) B850157
theorem B566787 : Blo 562809 566787 := bstep (se 1 (by rfl) ⟨425090, by rfl⟩ : syracuseStep 566787 = 850181) B850181
theorem B566803 : Blo 562809 566803 := bstep (se 1 (by rfl) ⟨425102, by rfl⟩ : syracuseStep 566803 = 850205) B850205
theorem B1353361 : Blo 562809 1353361 := bstep (se 2 (by rfl) ⟨507510, by rfl⟩ : syracuseStep 1353361 = 1015021) B1015021
theorem B1353457 : Blo 562809 1353457 := bstep (se 2 (by rfl) ⟨507546, by rfl⟩ : syracuseStep 1353457 = 1015093) B1015093
theorem B1910573 : Blo 562809 1910573 := bstep (se 3 (by rfl) ⟨358232, by rfl⟩ : syracuseStep 1910573 = 716465) B716465
theorem B1910627 : Blo 562809 1910627 := bstep (se 1 (by rfl) ⟨1432970, by rfl⟩ : syracuseStep 1910627 = 2865941) B2865941
theorem B1812401 : Blo 562809 1812401 := bstep (se 2 (by rfl) ⟨679650, by rfl⟩ : syracuseStep 1812401 = 1359301) B1359301
theorem B3483661 : Blo 562809 3483661 := bstep (se 3 (by rfl) ⟨653186, by rfl⟩ : syracuseStep 3483661 = 1306373) B1306373
theorem B1452113 : Blo 562809 1452113 := bstep (se 2 (by rfl) ⟨544542, by rfl⟩ : syracuseStep 1452113 = 1089085) B1089085
theorem B1910897 : Blo 562809 1910897 := bstep (se 2 (by rfl) ⟨716586, by rfl⟩ : syracuseStep 1910897 = 1433173) B1433173
theorem B1222865 : Blo 562809 1222865 := bstep (se 2 (by rfl) ⟨458574, by rfl⟩ : syracuseStep 1222865 = 917149) B917149
theorem B2140451 : Blo 562809 2140451 := bstep (se 1 (by rfl) ⟨1605338, by rfl⟩ : syracuseStep 2140451 = 3210677) B3210677
theorem B2140465 : Blo 562809 2140465 := bstep (se 2 (by rfl) ⟨802674, by rfl⟩ : syracuseStep 2140465 = 1605349) B1605349
theorem B3058019 : Blo 562809 3058019 := bstep (se 1 (by rfl) ⟨2293514, by rfl⟩ : syracuseStep 3058019 = 4587029) B4587029
theorem B633235 : Blo 562809 633235 := bstep (se 1 (by rfl) ⟨474926, by rfl⟩ : syracuseStep 633235 = 949853) B949853
theorem B2042381 : Blo 562809 2042381 := bstep (se 3 (by rfl) ⟨382946, by rfl⟩ : syracuseStep 2042381 = 765893) B765893
theorem B633379 : Blo 562809 633379 := bstep (se 1 (by rfl) ⟨475034, by rfl⟩ : syracuseStep 633379 = 950069) B950069
theorem B1223203 : Blo 562809 1223203 := bstep (se 1 (by rfl) ⟨917402, by rfl⟩ : syracuseStep 1223203 = 1834805) B1834805
theorem B1911437 : Blo 562809 1911437 := bstep (se 3 (by rfl) ⟨358394, by rfl⟩ : syracuseStep 1911437 = 716789) B716789
theorem B633523 : Blo 562809 633523 := bstep (se 1 (by rfl) ⟨475142, by rfl⟩ : syracuseStep 633523 = 950285) B950285
theorem B1911491 : Blo 562809 1911491 := bstep (se 1 (by rfl) ⟨1433618, by rfl⟩ : syracuseStep 1911491 = 2867237) B2867237
theorem B633667 : Blo 562809 633667 := bstep (se 1 (by rfl) ⟨475250, by rfl⟩ : syracuseStep 633667 = 950501) B950501
theorem B3222341 : Blo 562809 3222341 := bstep (se 4 (by rfl) ⟨302094, by rfl⟩ : syracuseStep 3222341 = 604189) B604189
theorem B1911761 : Blo 562809 1911761 := bstep (se 2 (by rfl) ⟨716910, by rfl⟩ : syracuseStep 1911761 = 1433821) B1433821
theorem B633811 : Blo 562809 633811 := bstep (se 1 (by rfl) ⟨475358, by rfl⟩ : syracuseStep 633811 = 950717) B950717
theorem B3615779 : Blo 562809 3615779 := bstep (se 1 (by rfl) ⟨2711834, by rfl⟩ : syracuseStep 3615779 = 5423669) B5423669
theorem B633955 : Blo 562809 633955 := bstep (se 1 (by rfl) ⟨475466, by rfl⟩ : syracuseStep 633955 = 950933) B950933
theorem B634099 : Blo 562809 634099 := bstep (se 1 (by rfl) ⟨475574, by rfl⟩ : syracuseStep 634099 = 951149) B951149
theorem B1223939 : Blo 562809 1223939 := bstep (se 1 (by rfl) ⟨917954, by rfl⟩ : syracuseStep 1223939 = 1835909) B1835909
theorem B634243 : Blo 562809 634243 := bstep (se 1 (by rfl) ⟨475682, by rfl⟩ : syracuseStep 634243 = 951365) B951365
theorem B1912301 : Blo 562809 1912301 := bstep (se 3 (by rfl) ⟨358556, by rfl⟩ : syracuseStep 1912301 = 717113) B717113
theorem B634387 : Blo 562809 634387 := bstep (se 1 (by rfl) ⟨475790, by rfl⟩ : syracuseStep 634387 = 951581) B951581
theorem B1912355 : Blo 562809 1912355 := bstep (se 1 (by rfl) ⟨1434266, by rfl⟩ : syracuseStep 1912355 = 2868533) B2868533
theorem B634531 : Blo 562809 634531 := bstep (se 1 (by rfl) ⟨475898, by rfl⟩ : syracuseStep 634531 = 951797) B951797
theorem B1289891 : Blo 562809 1289891 := bstep (se 1 (by rfl) ⟨967418, by rfl⟩ : syracuseStep 1289891 = 1934837) B1934837
theorem B2141923 : Blo 562809 2141923 := bstep (se 1 (by rfl) ⟨1606442, by rfl⟩ : syracuseStep 2141923 = 3212885) B3212885
theorem B1912625 : Blo 562809 1912625 := bstep (se 2 (by rfl) ⟨717234, by rfl⟩ : syracuseStep 1912625 = 1434469) B1434469
theorem B634675 : Blo 562809 634675 := bstep (se 1 (by rfl) ⟨476006, by rfl⟩ : syracuseStep 634675 = 952013) B952013
theorem B1814413 : Blo 562809 1814413 := bstep (se 3 (by rfl) ⟨340202, by rfl⟩ : syracuseStep 1814413 = 680405) B680405
theorem B2863025 : Blo 562809 2863025 := bstep (se 2 (by rfl) ⟨1073634, by rfl⟩ : syracuseStep 2863025 = 2147269) B2147269
theorem B634819 : Blo 562809 634819 := bstep (se 1 (by rfl) ⟨476114, by rfl⟩ : syracuseStep 634819 = 952229) B952229
theorem B602083 : Blo 562809 602083 := bstep (se 1 (by rfl) ⟨451562, by rfl⟩ : syracuseStep 602083 = 903125) B903125
theorem B634963 : Blo 562809 634963 := bstep (se 1 (by rfl) ⟨476222, by rfl⟩ : syracuseStep 634963 = 952445) B952445
theorem B2896013 : Blo 562809 2896013 := bstep (se 3 (by rfl) ⟨543002, by rfl⟩ : syracuseStep 2896013 = 1086005) B1086005
theorem B635107 : Blo 562809 635107 := bstep (se 1 (by rfl) ⟨476330, by rfl⟩ : syracuseStep 635107 = 952661) B952661
theorem B1814861 : Blo 562809 1814861 := bstep (se 3 (by rfl) ⟨340286, by rfl⟩ : syracuseStep 1814861 = 680573) B680573
theorem B635251 : Blo 562809 635251 := bstep (se 1 (by rfl) ⟨476438, by rfl⟩ : syracuseStep 635251 = 952877) B952877
theorem B602515 : Blo 562809 602515 := bstep (se 1 (by rfl) ⟨451886, by rfl⟩ : syracuseStep 602515 = 903773) B903773
theorem B635395 : Blo 562809 635395 := bstep (se 1 (by rfl) ⟨476546, by rfl⟩ : syracuseStep 635395 = 953093) B953093
theorem B635539 : Blo 562809 635539 := bstep (se 1 (by rfl) ⟨476654, by rfl⟩ : syracuseStep 635539 = 953309) B953309
theorem B6861509 : Blo 562809 6861509 := bstep (se 4 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 6861509 = 1286533) B1286533
theorem B635683 : Blo 562809 635683 := bstep (se 1 (by rfl) ⟨476762, by rfl⟩ : syracuseStep 635683 = 953525) B953525
theorem B635827 : Blo 562809 635827 := bstep (se 1 (by rfl) ⟨476870, by rfl⟩ : syracuseStep 635827 = 953741) B953741
theorem B3617777 : Blo 562809 3617777 := bstep (se 2 (by rfl) ⟨1356666, by rfl⟩ : syracuseStep 3617777 = 2713333) B2713333
theorem B635971 : Blo 562809 635971 := bstep (se 1 (by rfl) ⟨476978, by rfl⟩ : syracuseStep 635971 = 953957) B953957
theorem B636115 : Blo 562809 636115 := bstep (se 1 (by rfl) ⟨477086, by rfl⟩ : syracuseStep 636115 = 954173) B954173
theorem B9188579 : Blo 562809 9188579 := bstep (se 1 (by rfl) ⟨6891434, by rfl⟩ : syracuseStep 9188579 = 13782869) B13782869
theorem B636259 : Blo 562809 636259 := bstep (se 1 (by rfl) ⟨477194, by rfl⟩ : syracuseStep 636259 = 954389) B954389
theorem B2864483 : Blo 562809 2864483 := bstep (se 1 (by rfl) ⟨2148362, by rfl⟩ : syracuseStep 2864483 = 4296725) B4296725
theorem B2405837 : Blo 562809 2405837 := bstep (se 3 (by rfl) ⟨451094, by rfl⟩ : syracuseStep 2405837 = 902189) B902189
theorem B636403 : Blo 562809 636403 := bstep (se 1 (by rfl) ⟨477302, by rfl⟩ : syracuseStep 636403 = 954605) B954605
theorem B603779 : Blo 562809 603779 := bstep (se 1 (by rfl) ⟨452834, by rfl⟩ : syracuseStep 603779 = 905669) B905669
theorem B636547 : Blo 562809 636547 := bstep (se 1 (by rfl) ⟨477410, by rfl⟩ : syracuseStep 636547 = 954821) B954821
theorem B4830947 : Blo 562809 4830947 := bstep (se 1 (by rfl) ⟨3623210, by rfl⟩ : syracuseStep 4830947 = 7246421) B7246421
theorem B636691 : Blo 562809 636691 := bstep (se 1 (by rfl) ⟨477518, by rfl⟩ : syracuseStep 636691 = 955037) B955037
theorem B2406179 : Blo 562809 2406179 := bstep (se 1 (by rfl) ⟨1804634, by rfl⟩ : syracuseStep 2406179 = 3609269) B3609269
theorem B1357667 : Blo 562809 1357667 := bstep (se 1 (by rfl) ⟨1018250, by rfl⟩ : syracuseStep 1357667 = 2036501) B2036501
theorem B2144141 : Blo 562809 2144141 := bstep (se 3 (by rfl) ⟨402026, by rfl⟩ : syracuseStep 2144141 = 804053) B804053
theorem B3618701 : Blo 562809 3618701 := bstep (se 3 (by rfl) ⟨678506, by rfl⟩ : syracuseStep 3618701 = 1357013) B1357013
theorem B2570147 : Blo 562809 2570147 := bstep (se 1 (by rfl) ⟨1927610, by rfl⟩ : syracuseStep 2570147 = 3855221) B3855221
theorem B636835 : Blo 562809 636835 := bstep (se 1 (by rfl) ⟨477626, by rfl⟩ : syracuseStep 636835 = 955253) B955253
theorem B636979 : Blo 562809 636979 := bstep (se 1 (by rfl) ⟨477734, by rfl⟩ : syracuseStep 636979 = 955469) B955469
theorem B2865293 : Blo 562809 2865293 := bstep (se 3 (by rfl) ⟨537242, by rfl⟩ : syracuseStep 2865293 = 1074485) B1074485
theorem B637123 : Blo 562809 637123 := bstep (se 1 (by rfl) ⟨477842, by rfl⟩ : syracuseStep 637123 = 955685) B955685
theorem B637267 : Blo 562809 637267 := bstep (se 1 (by rfl) ⟨477950, by rfl⟩ : syracuseStep 637267 = 955901) B955901
theorem B604531 : Blo 562809 604531 := bstep (se 1 (by rfl) ⟨453398, by rfl⟩ : syracuseStep 604531 = 906797) B906797
theorem B637411 : Blo 562809 637411 := bstep (se 1 (by rfl) ⟨478058, by rfl⟩ : syracuseStep 637411 = 956117) B956117
theorem B1161745 : Blo 562809 1161745 := bstep (se 2 (by rfl) ⟨435654, by rfl⟩ : syracuseStep 1161745 = 871309) B871309
theorem B3226189 : Blo 562809 3226189 := bstep (se 3 (by rfl) ⟨604910, by rfl⟩ : syracuseStep 3226189 = 1209821) B1209821
theorem B1358435 : Blo 562809 1358435 := bstep (se 1 (by rfl) ⟨1018826, by rfl⟩ : syracuseStep 1358435 = 2037653) B2037653
theorem B637555 : Blo 562809 637555 := bstep (se 1 (by rfl) ⟨478166, by rfl⟩ : syracuseStep 637555 = 956333) B956333
theorem B1522435 : Blo 562809 1522435 := bstep (se 1 (by rfl) ⟨1141826, by rfl⟩ : syracuseStep 1522435 = 2283653) B2283653
theorem B801667 : Blo 562809 801667 := bstep (se 1 (by rfl) ⟨601250, by rfl⟩ : syracuseStep 801667 = 1202501) B1202501
theorem B4275341 : Blo 562809 4275341 := bstep (se 3 (by rfl) ⟨801626, by rfl⟩ : syracuseStep 4275341 = 1603253) B1603253
theorem B1358993 : Blo 562809 1358993 := bstep (se 2 (by rfl) ⟨509622, by rfl⟩ : syracuseStep 1358993 = 1019245) B1019245
theorem B802003 : Blo 562809 802003 := bstep (se 1 (by rfl) ⟨601502, by rfl⟩ : syracuseStep 802003 = 1203005) B1203005
theorem B2178353 : Blo 562809 2178353 := bstep (se 2 (by rfl) ⟨816882, by rfl⟩ : syracuseStep 2178353 = 1633765) B1633765
theorem B1359281 : Blo 562809 1359281 := bstep (se 2 (by rfl) ⟨509730, by rfl⟩ : syracuseStep 1359281 = 1019461) B1019461
theorem B1425073 : Blo 562809 1425073 := bstep (se 2 (by rfl) ⟨534402, by rfl⟩ : syracuseStep 1425073 = 1068805) B1068805
theorem B7749361 : Blo 562809 7749361 := bstep (se 2 (by rfl) ⟨2906010, by rfl⟩ : syracuseStep 7749361 = 5812021) B5812021
theorem B802561 : Blo 562809 802561 := bstep (se 2 (by rfl) ⟨300960, by rfl⟩ : syracuseStep 802561 = 601921) B601921
theorem B802595 : Blo 562809 802595 := bstep (se 1 (by rfl) ⟨601946, by rfl⟩ : syracuseStep 802595 = 1203893) B1203893
theorem B1425347 : Blo 562809 1425347 := bstep (se 1 (by rfl) ⟨1069010, by rfl⟩ : syracuseStep 1425347 = 2138021) B2138021
theorem B30883781 : Blo 562809 30883781 := bstep (se 4 (by rfl) ⟨2895354, by rfl⟩ : syracuseStep 30883781 = 5790709) B5790709
theorem B1425539 : Blo 562809 1425539 := bstep (se 1 (by rfl) ⟨1069154, by rfl⟩ : syracuseStep 1425539 = 2138309) B2138309
theorem B803153 : Blo 562809 803153 := bstep (se 2 (by rfl) ⟨301182, by rfl⟩ : syracuseStep 803153 = 602365) B602365
theorem B803233 : Blo 562809 803233 := bstep (se 2 (by rfl) ⟨301212, by rfl⟩ : syracuseStep 803233 = 602425) B602425
theorem B1524305 : Blo 562809 1524305 := bstep (se 2 (by rfl) ⟨571614, by rfl⟩ : syracuseStep 1524305 = 1143229) B1143229
theorem B2147057 : Blo 562809 2147057 := bstep (se 2 (by rfl) ⟨805146, by rfl⟩ : syracuseStep 2147057 = 1610293) B1610293
theorem B902035 : Blo 562809 902035 := bstep (se 1 (by rfl) ⟨676526, by rfl⟩ : syracuseStep 902035 = 1353053) B1353053
theorem B2868209 : Blo 562809 2868209 := bstep (se 2 (by rfl) ⟨1075578, by rfl⟩ : syracuseStep 2868209 = 2151157) B2151157
theorem B1426481 : Blo 562809 1426481 := bstep (se 2 (by rfl) ⟨534930, by rfl⟩ : syracuseStep 1426481 = 1069861) B1069861
theorem B1426531 : Blo 562809 1426531 := bstep (se 1 (by rfl) ⟨1069898, by rfl⟩ : syracuseStep 1426531 = 2139797) B2139797
theorem B804019 : Blo 562809 804019 := bstep (se 1 (by rfl) ⟨603014, by rfl⟩ : syracuseStep 804019 = 1206029) B1206029
theorem B1426673 : Blo 562809 1426673 := bstep (se 2 (by rfl) ⟨535002, by rfl⟩ : syracuseStep 1426673 = 1070005) B1070005
theorem B902497 : Blo 562809 902497 := bstep (se 2 (by rfl) ⟨338436, by rfl⟩ : syracuseStep 902497 = 676873) B676873
theorem B902593 : Blo 562809 902593 := bstep (se 2 (by rfl) ⟨338472, by rfl⟩ : syracuseStep 902593 = 676945) B676945
theorem B2606627 : Blo 562809 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B902753 : Blo 562809 902753 := bstep (se 2 (by rfl) ⟨338532, by rfl⟩ : syracuseStep 902753 = 677065) B677065
theorem B804497 : Blo 562809 804497 := bstep (se 2 (by rfl) ⟨301686, by rfl⟩ : syracuseStep 804497 = 603373) B603373
theorem B2410211 : Blo 562809 2410211 := bstep (se 1 (by rfl) ⟨1807658, by rfl⟩ : syracuseStep 2410211 = 3615317) B3615317
theorem B804611 : Blo 562809 804611 := bstep (se 1 (by rfl) ⟨603458, by rfl⟩ : syracuseStep 804611 = 1206917) B1206917
theorem B1525549 : Blo 562809 1525549 := bstep (se 3 (by rfl) ⟨286040, by rfl⟩ : syracuseStep 1525549 = 572081) B572081
theorem B2443085 : Blo 562809 2443085 := bstep (se 3 (by rfl) ⟨458078, by rfl⟩ : syracuseStep 2443085 = 916157) B916157
theorem B804691 : Blo 562809 804691 := bstep (se 1 (by rfl) ⟨603518, by rfl⟩ : syracuseStep 804691 = 1207037) B1207037
theorem B1525645 : Blo 562809 1525645 := bstep (se 3 (by rfl) ⟨286058, by rfl⟩ : syracuseStep 1525645 = 572117) B572117
theorem B4278257 : Blo 562809 4278257 := bstep (se 2 (by rfl) ⟨1604346, by rfl⟩ : syracuseStep 4278257 = 3208693) B3208693
theorem B2148515 : Blo 562809 2148515 := bstep (se 1 (by rfl) ⟨1611386, by rfl⟩ : syracuseStep 2148515 = 3222773) B3222773
theorem B1427665 : Blo 562809 1427665 := bstep (se 2 (by rfl) ⟨535374, by rfl⟩ : syracuseStep 1427665 = 1070749) B1070749
theorem B805249 : Blo 562809 805249 := bstep (se 2 (by rfl) ⟨301968, by rfl⟩ : syracuseStep 805249 = 603937) B603937
theorem B969185 : Blo 562809 969185 := bstep (se 2 (by rfl) ⟨363444, by rfl⟩ : syracuseStep 969185 = 726889) B726889
theorem B1427939 : Blo 562809 1427939 := bstep (se 1 (by rfl) ⟨1070954, by rfl⟩ : syracuseStep 1427939 = 2141909) B2141909
theorem B6441443 : Blo 562809 6441443 := bstep (se 1 (by rfl) ⟨4831082, by rfl⟩ : syracuseStep 6441443 = 9662165) B9662165
theorem B3656305 : Blo 562809 3656305 := bstep (se 2 (by rfl) ⟨1371114, by rfl⟩ : syracuseStep 3656305 = 2742229) B2742229
theorem B1428131 : Blo 562809 1428131 := bstep (se 1 (by rfl) ⟨1071098, by rfl⟩ : syracuseStep 1428131 = 2142197) B2142197
theorem B1526467 : Blo 562809 1526467 := bstep (se 1 (by rfl) ⟨1144850, by rfl⟩ : syracuseStep 1526467 = 2289701) B2289701
theorem B1526509 : Blo 562809 1526509 := bstep (se 3 (by rfl) ⟨286220, by rfl⟩ : syracuseStep 1526509 = 572441) B572441
theorem B2411441 : Blo 562809 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B805955 : Blo 562809 805955 := bstep (se 1 (by rfl) ⟨604466, by rfl⟩ : syracuseStep 805955 = 1208933) B1208933
theorem B2149517 : Blo 562809 2149517 := bstep (se 3 (by rfl) ⟨403034, by rfl⟩ : syracuseStep 2149517 = 806069) B806069
theorem B28331221 : Blo 562809 28331221 := bstep (se 7 (by rfl) ⟨332006, by rfl⟩ : syracuseStep 28331221 = 664013) B664013
theorem B904547 : Blo 562809 904547 := bstep (se 1 (by rfl) ⟨678410, by rfl⟩ : syracuseStep 904547 = 1356821) B1356821
theorem B1953197 : Blo 562809 1953197 := bstep (se 3 (by rfl) ⟨366224, by rfl⟩ : syracuseStep 1953197 = 732449) B732449
theorem B1068547 : Blo 562809 1068547 := bstep (se 1 (by rfl) ⟨801410, by rfl⟩ : syracuseStep 1068547 = 1602821) B1602821
theorem B1429073 : Blo 562809 1429073 := bstep (se 2 (by rfl) ⟨535902, by rfl⟩ : syracuseStep 1429073 = 1071805) B1071805
theorem B1429123 : Blo 562809 1429123 := bstep (se 1 (by rfl) ⟨1071842, by rfl⟩ : syracuseStep 1429123 = 2143685) B2143685
theorem B1068707 : Blo 562809 1068707 := bstep (se 1 (by rfl) ⟨801530, by rfl⟩ : syracuseStep 1068707 = 1603061) B1603061
theorem B806593 : Blo 562809 806593 := bstep (se 2 (by rfl) ⟨302472, by rfl⟩ : syracuseStep 806593 = 604945) B604945
theorem B1429265 : Blo 562809 1429265 := bstep (se 2 (by rfl) ⟨535974, by rfl⟩ : syracuseStep 1429265 = 1071949) B1071949
theorem B2477873 : Blo 562809 2477873 := bstep (se 2 (by rfl) ⟨929202, by rfl⟩ : syracuseStep 2477873 = 1858405) B1858405
theorem B806707 : Blo 562809 806707 := bstep (se 1 (by rfl) ⟨605030, by rfl⟩ : syracuseStep 806707 = 1210061) B1210061
theorem B905393 : Blo 562809 905393 := bstep (se 2 (by rfl) ⟨339522, by rfl⟩ : syracuseStep 905393 = 679045) B679045
theorem B905521 : Blo 562809 905521 := bstep (se 2 (by rfl) ⟨339570, by rfl⟩ : syracuseStep 905521 = 679141) B679141
theorem B2576717 : Blo 562809 2576717 := bstep (se 3 (by rfl) ⟨483134, by rfl⟩ : syracuseStep 2576717 = 966269) B966269
theorem B905585 : Blo 562809 905585 := bstep (se 2 (by rfl) ⟨339594, by rfl⟩ : syracuseStep 905585 = 679189) B679189
theorem B3854897 : Blo 562809 3854897 := bstep (se 2 (by rfl) ⟨1445586, by rfl⟩ : syracuseStep 3854897 = 2891173) B2891173
theorem B1266353 : Blo 562809 1266353 := bstep (se 2 (by rfl) ⟨474882, by rfl⟩ : syracuseStep 1266353 = 949765) B949765
theorem B1266371 : Blo 562809 1266371 := bstep (se 1 (by rfl) ⟨949778, by rfl⟩ : syracuseStep 1266371 = 1899557) B1899557
theorem B1069777 : Blo 562809 1069777 := bstep (se 2 (by rfl) ⟨401166, by rfl⟩ : syracuseStep 1069777 = 802333) B802333
theorem B10277603 : Blo 562809 10277603 := bstep (se 1 (by rfl) ⟨7708202, by rfl⟩ : syracuseStep 10277603 = 15416405) B15416405
theorem B1430257 : Blo 562809 1430257 := bstep (se 2 (by rfl) ⟨536346, by rfl⟩ : syracuseStep 1430257 = 1072693) B1072693
theorem B1266641 : Blo 562809 1266641 := bstep (se 2 (by rfl) ⟨474990, by rfl⟩ : syracuseStep 1266641 = 949981) B949981
theorem B1266659 : Blo 562809 1266659 := bstep (se 1 (by rfl) ⟨949994, by rfl⟩ : syracuseStep 1266659 = 1899989) B1899989
theorem B3625955 : Blo 562809 3625955 := bstep (se 1 (by rfl) ⟨2719466, by rfl⟩ : syracuseStep 3625955 = 5438933) B5438933
theorem B1430531 : Blo 562809 1430531 := bstep (se 1 (by rfl) ⟨1072898, by rfl⟩ : syracuseStep 1430531 = 2145797) B2145797
theorem B5231729 : Blo 562809 5231729 := bstep (se 2 (by rfl) ⟨1961898, by rfl⟩ : syracuseStep 5231729 = 3923797) B3923797
theorem B1430723 : Blo 562809 1430723 := bstep (se 1 (by rfl) ⟨1073042, by rfl⟩ : syracuseStep 1430723 = 2146085) B2146085
theorem B2151629 : Blo 562809 2151629 := bstep (se 3 (by rfl) ⟨403430, by rfl⟩ : syracuseStep 2151629 = 806861) B806861
theorem B1266929 : Blo 562809 1266929 := bstep (se 2 (by rfl) ⟨475098, by rfl⟩ : syracuseStep 1266929 = 950197) B950197
theorem B1266947 : Blo 562809 1266947 := bstep (se 1 (by rfl) ⟨950210, by rfl⟩ : syracuseStep 1266947 = 1900421) B1900421
theorem B2413901 : Blo 562809 2413901 := bstep (se 3 (by rfl) ⟨452606, by rfl⟩ : syracuseStep 2413901 = 905213) B905213
theorem B15422861 : Blo 562809 15422861 := bstep (se 3 (by rfl) ⟨2891786, by rfl⟩ : syracuseStep 15422861 = 5783573) B5783573
theorem B2446733 : Blo 562809 2446733 := bstep (se 3 (by rfl) ⟨458762, by rfl⟩ : syracuseStep 2446733 = 917525) B917525
theorem B906643 : Blo 562809 906643 := bstep (se 1 (by rfl) ⟨679982, by rfl⟩ : syracuseStep 906643 = 1359965) B1359965
theorem B1267217 : Blo 562809 1267217 := bstep (se 2 (by rfl) ⟨475206, by rfl⟩ : syracuseStep 1267217 = 950413) B950413
theorem B1267235 : Blo 562809 1267235 := bstep (se 1 (by rfl) ⟨950426, by rfl⟩ : syracuseStep 1267235 = 1900853) B1900853
theorem B4839011 : Blo 562809 4839011 := bstep (se 1 (by rfl) ⟨3629258, by rfl⟩ : syracuseStep 4839011 = 7258517) B7258517
theorem B677603 : Blo 562809 677603 := bstep (se 1 (by rfl) ⟨508202, by rfl⟩ : syracuseStep 677603 = 1016405) B1016405
theorem B1070833 : Blo 562809 1070833 := bstep (se 2 (by rfl) ⟨401562, by rfl⟩ : syracuseStep 1070833 = 803125) B803125
theorem B2447117 : Blo 562809 2447117 := bstep (se 3 (by rfl) ⟨458834, by rfl⟩ : syracuseStep 2447117 = 917669) B917669
theorem B677651 : Blo 562809 677651 := bstep (se 1 (by rfl) ⟨508238, by rfl⟩ : syracuseStep 677651 = 1016477) B1016477
theorem B1267505 : Blo 562809 1267505 := bstep (se 2 (by rfl) ⟨475314, by rfl⟩ : syracuseStep 1267505 = 950629) B950629
theorem B1267523 : Blo 562809 1267523 := bstep (se 1 (by rfl) ⟨950642, by rfl⟩ : syracuseStep 1267523 = 1901285) B1901285
theorem B6510449 : Blo 562809 6510449 := bstep (se 2 (by rfl) ⟨2441418, by rfl⟩ : syracuseStep 6510449 = 4882837) B4882837
theorem B645091 : Blo 562809 645091 := bstep (se 1 (by rfl) ⟨483818, by rfl⟩ : syracuseStep 645091 = 967637) B967637
theorem B1267793 : Blo 562809 1267793 := bstep (se 2 (by rfl) ⟨475422, by rfl⟩ : syracuseStep 1267793 = 950845) B950845
theorem B1267811 : Blo 562809 1267811 := bstep (se 1 (by rfl) ⟨950858, by rfl⟩ : syracuseStep 1267811 = 1901717) B1901717
theorem B1431665 : Blo 562809 1431665 := bstep (se 2 (by rfl) ⟨536874, by rfl⟩ : syracuseStep 1431665 = 1073749) B1073749
theorem B1529969 : Blo 562809 1529969 := bstep (se 2 (by rfl) ⟨573738, by rfl⟩ : syracuseStep 1529969 = 1147477) B1147477
theorem B1071235 : Blo 562809 1071235 := bstep (se 1 (by rfl) ⟨803426, by rfl⟩ : syracuseStep 1071235 = 1606853) B1606853
theorem B1431715 : Blo 562809 1431715 := bstep (se 1 (by rfl) ⟨1073786, by rfl⟩ : syracuseStep 1431715 = 2147573) B2147573
theorem B1071281 : Blo 562809 1071281 := bstep (se 2 (by rfl) ⟨401730, by rfl⟩ : syracuseStep 1071281 = 803461) B803461
theorem B2087117 : Blo 562809 2087117 := bstep (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) B782669
theorem B1431857 : Blo 562809 1431857 := bstep (se 2 (by rfl) ⟨536946, by rfl⟩ : syracuseStep 1431857 = 1073893) B1073893
theorem B907571 : Blo 562809 907571 := bstep (se 1 (by rfl) ⟨680678, by rfl⟩ : syracuseStep 907571 = 1361357) B1361357
theorem B1268081 : Blo 562809 1268081 := bstep (se 2 (by rfl) ⟨475530, by rfl⟩ : syracuseStep 1268081 = 951061) B951061
theorem B1268099 : Blo 562809 1268099 := bstep (se 1 (by rfl) ⟨951074, by rfl⟩ : syracuseStep 1268099 = 1902149) B1902149
theorem B1071569 : Blo 562809 1071569 := bstep (se 2 (by rfl) ⟨401838, by rfl⟩ : syracuseStep 1071569 = 803677) B803677
theorem B907841 : Blo 562809 907841 := bstep (se 2 (by rfl) ⟨340440, by rfl⟩ : syracuseStep 907841 = 680881) B680881
theorem B1268369 : Blo 562809 1268369 := bstep (se 2 (by rfl) ⟨475638, by rfl⟩ : syracuseStep 1268369 = 951277) B951277
theorem B1268387 : Blo 562809 1268387 := bstep (se 1 (by rfl) ⟨951290, by rfl⟩ : syracuseStep 1268387 = 1902581) B1902581
theorem B1268657 : Blo 562809 1268657 := bstep (se 2 (by rfl) ⟨475746, by rfl⟩ : syracuseStep 1268657 = 951493) B951493
theorem B1268675 : Blo 562809 1268675 := bstep (se 1 (by rfl) ⟨951506, by rfl⟩ : syracuseStep 1268675 = 1903013) B1903013
theorem B1465393 : Blo 562809 1465393 := bstep (se 2 (by rfl) ⟨549522, by rfl⟩ : syracuseStep 1465393 = 1099045) B1099045
theorem B1072291 : Blo 562809 1072291 := bstep (se 1 (by rfl) ⟨804218, by rfl⟩ : syracuseStep 1072291 = 1608437) B1608437
theorem B14277829 : Blo 562809 14277829 := bstep (se 4 (by rfl) ⟨1338546, by rfl⟩ : syracuseStep 14277829 = 2677093) B2677093
theorem B1268945 : Blo 562809 1268945 := bstep (se 2 (by rfl) ⟨475854, by rfl⟩ : syracuseStep 1268945 = 951709) B951709
theorem B1268963 : Blo 562809 1268963 := bstep (se 1 (by rfl) ⟨951722, by rfl⟩ : syracuseStep 1268963 = 1903445) B1903445
theorem B1432849 : Blo 562809 1432849 := bstep (se 2 (by rfl) ⟨537318, by rfl⟩ : syracuseStep 1432849 = 1074637) B1074637
theorem B1629521 : Blo 562809 1629521 := bstep (se 2 (by rfl) ⟨611070, by rfl⟩ : syracuseStep 1629521 = 1222141) B1222141
theorem B1531345 : Blo 562809 1531345 := bstep (se 2 (by rfl) ⟨574254, by rfl⟩ : syracuseStep 1531345 = 1148509) B1148509
theorem B1269233 : Blo 562809 1269233 := bstep (se 2 (by rfl) ⟨475962, by rfl⟩ : syracuseStep 1269233 = 951925) B951925
theorem B1269251 : Blo 562809 1269251 := bstep (se 1 (by rfl) ⟨951938, by rfl⟩ : syracuseStep 1269251 = 1903877) B1903877
theorem B1433123 : Blo 562809 1433123 := bstep (se 1 (by rfl) ⟨1074842, by rfl⟩ : syracuseStep 1433123 = 2149685) B2149685
theorem B1072739 : Blo 562809 1072739 := bstep (se 1 (by rfl) ⟨804554, by rfl⟩ : syracuseStep 1072739 = 1609109) B1609109
theorem B1433315 : Blo 562809 1433315 := bstep (se 1 (by rfl) ⟨1074986, by rfl⟩ : syracuseStep 1433315 = 2149973) B2149973
theorem B1269521 : Blo 562809 1269521 := bstep (se 2 (by rfl) ⟨476070, by rfl⟩ : syracuseStep 1269521 = 952141) B952141
theorem B1269539 : Blo 562809 1269539 := bstep (se 1 (by rfl) ⟨952154, by rfl⟩ : syracuseStep 1269539 = 1904309) B1904309
theorem B1073027 : Blo 562809 1073027 := bstep (se 1 (by rfl) ⟨804770, by rfl⟩ : syracuseStep 1073027 = 1609541) B1609541
theorem B712739 : Blo 562809 712739 := bstep (se 1 (by rfl) ⟨534554, by rfl⟩ : syracuseStep 712739 = 1069109) B1069109
theorem B1269809 : Blo 562809 1269809 := bstep (se 2 (by rfl) ⟨476178, by rfl⟩ : syracuseStep 1269809 = 952357) B952357
theorem B1269827 : Blo 562809 1269827 := bstep (se 1 (by rfl) ⟨952370, by rfl⟩ : syracuseStep 1269827 = 1904741) B1904741
theorem B1532045 : Blo 562809 1532045 := bstep (se 3 (by rfl) ⟨287258, by rfl⟩ : syracuseStep 1532045 = 574517) B574517
theorem B6119621 : Blo 562809 6119621 := bstep (se 4 (by rfl) ⟨573714, by rfl⟩ : syracuseStep 6119621 = 1147429) B1147429
theorem B680179 : Blo 562809 680179 := bstep (se 1 (by rfl) ⟨510134, by rfl⟩ : syracuseStep 680179 = 1020269) B1020269
theorem B1204483 : Blo 562809 1204483 := bstep (se 1 (by rfl) ⟨903362, by rfl⟩ : syracuseStep 1204483 = 1806725) B1806725
theorem B1270097 : Blo 562809 1270097 := bstep (se 2 (by rfl) ⟨476286, by rfl⟩ : syracuseStep 1270097 = 952573) B952573
theorem B680275 : Blo 562809 680275 := bstep (se 1 (by rfl) ⟨510206, by rfl⟩ : syracuseStep 680275 = 1020413) B1020413
theorem B1270115 : Blo 562809 1270115 := bstep (se 1 (by rfl) ⟨952586, by rfl⟩ : syracuseStep 1270115 = 1905173) B1905173
theorem B844241 : Blo 562809 844241 := bstep (se 2 (by rfl) ⟨316590, by rfl⟩ : syracuseStep 844241 = 633181) B633181
theorem B844259 : Blo 562809 844259 := bstep (se 1 (by rfl) ⟨633194, by rfl⟩ : syracuseStep 844259 = 1266389) B1266389
theorem B680419 : Blo 562809 680419 := bstep (se 1 (by rfl) ⟨510314, by rfl⟩ : syracuseStep 680419 = 1020629) B1020629
theorem B844289 : Blo 562809 844289 := bstep (se 2 (by rfl) ⟨316608, by rfl⟩ : syracuseStep 844289 = 633217) B633217
theorem B844307 : Blo 562809 844307 := bstep (se 1 (by rfl) ⟨633230, by rfl⟩ : syracuseStep 844307 = 1266461) B1266461
theorem B844337 : Blo 562809 844337 := bstep (se 2 (by rfl) ⟨316626, by rfl⟩ : syracuseStep 844337 = 633253) B633253
theorem B13754933 : Blo 562809 13754933 := bstep (se 5 (by rfl) ⟨644762, by rfl⟩ : syracuseStep 13754933 = 1289525) B1289525
theorem B844355 : Blo 562809 844355 := bstep (se 1 (by rfl) ⟨633266, by rfl⟩ : syracuseStep 844355 = 1266533) B1266533
theorem B844385 : Blo 562809 844385 := bstep (se 2 (by rfl) ⟨316644, by rfl⟩ : syracuseStep 844385 = 633289) B633289
theorem B1270385 : Blo 562809 1270385 := bstep (se 2 (by rfl) ⟨476394, by rfl⟩ : syracuseStep 1270385 = 952789) B952789
theorem B844403 : Blo 562809 844403 := bstep (se 1 (by rfl) ⟨633302, by rfl⟩ : syracuseStep 844403 = 1266605) B1266605
theorem B1270403 : Blo 562809 1270403 := bstep (se 1 (by rfl) ⟨952802, by rfl⟩ : syracuseStep 1270403 = 1905605) B1905605
theorem B844433 : Blo 562809 844433 := bstep (se 2 (by rfl) ⟨316662, by rfl⟩ : syracuseStep 844433 = 633325) B633325
theorem B1434257 : Blo 562809 1434257 := bstep (se 2 (by rfl) ⟨537846, by rfl⟩ : syracuseStep 1434257 = 1075693) B1075693
theorem B844451 : Blo 562809 844451 := bstep (se 1 (by rfl) ⟨633338, by rfl⟩ : syracuseStep 844451 = 1266677) B1266677
theorem B844481 : Blo 562809 844481 := bstep (se 2 (by rfl) ⟨316680, by rfl⟩ : syracuseStep 844481 = 633361) B633361
theorem B1434307 : Blo 562809 1434307 := bstep (se 1 (by rfl) ⟨1075730, by rfl⟩ : syracuseStep 1434307 = 2151461) B2151461
theorem B844499 : Blo 562809 844499 := bstep (se 1 (by rfl) ⟨633374, by rfl⟩ : syracuseStep 844499 = 1266749) B1266749
theorem B713443 : Blo 562809 713443 := bstep (se 1 (by rfl) ⟨535082, by rfl⟩ : syracuseStep 713443 = 1070165) B1070165
theorem B844529 : Blo 562809 844529 := bstep (se 2 (by rfl) ⟨316698, by rfl⟩ : syracuseStep 844529 = 633397) B633397
theorem B844547 : Blo 562809 844547 := bstep (se 1 (by rfl) ⟨633410, by rfl⟩ : syracuseStep 844547 = 1266821) B1266821
theorem B3138317 : Blo 562809 3138317 := bstep (se 3 (by rfl) ⟨588434, by rfl⟩ : syracuseStep 3138317 = 1176869) B1176869
theorem B844577 : Blo 562809 844577 := bstep (se 2 (by rfl) ⟨316716, by rfl⟩ : syracuseStep 844577 = 633433) B633433
theorem B3433265 : Blo 562809 3433265 := bstep (se 2 (by rfl) ⟨1287474, by rfl⟩ : syracuseStep 3433265 = 2574949) B2574949
theorem B1073969 : Blo 562809 1073969 := bstep (se 2 (by rfl) ⟨402738, by rfl⟩ : syracuseStep 1073969 = 805477) B805477
theorem B844595 : Blo 562809 844595 := bstep (se 1 (by rfl) ⟨633446, by rfl⟩ : syracuseStep 844595 = 1266893) B1266893
theorem B3629873 : Blo 562809 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B713539 : Blo 562809 713539 := bstep (se 1 (by rfl) ⟨535154, by rfl⟩ : syracuseStep 713539 = 1070309) B1070309
theorem B844625 : Blo 562809 844625 := bstep (se 2 (by rfl) ⟨316734, by rfl⟩ : syracuseStep 844625 = 633469) B633469
theorem B1434449 : Blo 562809 1434449 := bstep (se 2 (by rfl) ⟨537918, by rfl⟩ : syracuseStep 1434449 = 1075837) B1075837
theorem B844643 : Blo 562809 844643 := bstep (se 1 (by rfl) ⟨633482, by rfl⟩ : syracuseStep 844643 = 1266965) B1266965
theorem B844673 : Blo 562809 844673 := bstep (se 2 (by rfl) ⟨316752, by rfl⟩ : syracuseStep 844673 = 633505) B633505
theorem B1270673 : Blo 562809 1270673 := bstep (se 2 (by rfl) ⟨476502, by rfl⟩ : syracuseStep 1270673 = 953005) B953005
theorem B844691 : Blo 562809 844691 := bstep (se 1 (by rfl) ⟨633518, by rfl⟩ : syracuseStep 844691 = 1267037) B1267037
theorem B1270691 : Blo 562809 1270691 := bstep (se 1 (by rfl) ⟨953018, by rfl⟩ : syracuseStep 1270691 = 1906037) B1906037
theorem B844721 : Blo 562809 844721 := bstep (se 2 (by rfl) ⟨316770, by rfl⟩ : syracuseStep 844721 = 633541) B633541
theorem B844739 : Blo 562809 844739 := bstep (se 1 (by rfl) ⟨633554, by rfl⟩ : syracuseStep 844739 = 1267109) B1267109
theorem B844769 : Blo 562809 844769 := bstep (se 2 (by rfl) ⟨316788, by rfl⟩ : syracuseStep 844769 = 633577) B633577
theorem B844787 : Blo 562809 844787 := bstep (se 1 (by rfl) ⟨633590, by rfl⟩ : syracuseStep 844787 = 1267181) B1267181
theorem B844817 : Blo 562809 844817 := bstep (se 2 (by rfl) ⟨316806, by rfl⟩ : syracuseStep 844817 = 633613) B633613
theorem B844835 : Blo 562809 844835 := bstep (se 1 (by rfl) ⟨633626, by rfl⟩ : syracuseStep 844835 = 1267253) B1267253
theorem B844865 : Blo 562809 844865 := bstep (se 2 (by rfl) ⟨316824, by rfl⟩ : syracuseStep 844865 = 633649) B633649
theorem B844883 : Blo 562809 844883 := bstep (se 1 (by rfl) ⟨633662, by rfl⟩ : syracuseStep 844883 = 1267325) B1267325
theorem B844913 : Blo 562809 844913 := bstep (se 2 (by rfl) ⟨316842, by rfl⟩ : syracuseStep 844913 = 633685) B633685
theorem B844931 : Blo 562809 844931 := bstep (se 1 (by rfl) ⟨633698, by rfl⟩ : syracuseStep 844931 = 1267397) B1267397
theorem B844961 : Blo 562809 844961 := bstep (se 2 (by rfl) ⟨316860, by rfl⟩ : syracuseStep 844961 = 633721) B633721
theorem B1270961 : Blo 562809 1270961 := bstep (se 2 (by rfl) ⟨476610, by rfl⟩ : syracuseStep 1270961 = 953221) B953221
theorem B844979 : Blo 562809 844979 := bstep (se 1 (by rfl) ⟨633734, by rfl⟩ : syracuseStep 844979 = 1267469) B1267469
theorem B1270979 : Blo 562809 1270979 := bstep (se 1 (by rfl) ⟨953234, by rfl⟩ : syracuseStep 1270979 = 1906469) B1906469
theorem B845009 : Blo 562809 845009 := bstep (se 2 (by rfl) ⟨316878, by rfl⟩ : syracuseStep 845009 = 633757) B633757
theorem B845027 : Blo 562809 845027 := bstep (se 1 (by rfl) ⟨633770, by rfl⟩ : syracuseStep 845027 = 1267541) B1267541
theorem B845057 : Blo 562809 845057 := bstep (se 2 (by rfl) ⟨316896, by rfl⟩ : syracuseStep 845057 = 633793) B633793
theorem B845075 : Blo 562809 845075 := bstep (se 1 (by rfl) ⟨633806, by rfl⟩ : syracuseStep 845075 = 1267613) B1267613
theorem B845105 : Blo 562809 845105 := bstep (se 2 (by rfl) ⟨316914, by rfl⟩ : syracuseStep 845105 = 633829) B633829
theorem B714035 : Blo 562809 714035 := bstep (se 1 (by rfl) ⟨535526, by rfl⟩ : syracuseStep 714035 = 1071053) B1071053
theorem B845123 : Blo 562809 845123 := bstep (se 1 (by rfl) ⟨633842, by rfl⟩ : syracuseStep 845123 = 1267685) B1267685
theorem B845153 : Blo 562809 845153 := bstep (se 2 (by rfl) ⟨316932, by rfl⟩ : syracuseStep 845153 = 633865) B633865
theorem B845171 : Blo 562809 845171 := bstep (se 1 (by rfl) ⟨633878, by rfl⟩ : syracuseStep 845171 = 1267757) B1267757
theorem B845201 : Blo 562809 845201 := bstep (se 2 (by rfl) ⟨316950, by rfl⟩ : syracuseStep 845201 = 633901) B633901
theorem B845219 : Blo 562809 845219 := bstep (se 1 (by rfl) ⟨633914, by rfl⟩ : syracuseStep 845219 = 1267829) B1267829
theorem B845249 : Blo 562809 845249 := bstep (se 2 (by rfl) ⟨316968, by rfl⟩ : syracuseStep 845249 = 633937) B633937
theorem B3630541 : Blo 562809 3630541 := bstep (se 3 (by rfl) ⟨680726, by rfl⟩ : syracuseStep 3630541 = 1361453) B1361453
theorem B1271249 : Blo 562809 1271249 := bstep (se 2 (by rfl) ⟨476718, by rfl⟩ : syracuseStep 1271249 = 953437) B953437
theorem B845267 : Blo 562809 845267 := bstep (se 1 (by rfl) ⟨633950, by rfl⟩ : syracuseStep 845267 = 1267901) B1267901
theorem B1271267 : Blo 562809 1271267 := bstep (se 1 (by rfl) ⟨953450, by rfl⟩ : syracuseStep 1271267 = 1906901) B1906901
theorem B845297 : Blo 562809 845297 := bstep (se 2 (by rfl) ⟨316986, by rfl⟩ : syracuseStep 845297 = 633973) B633973
theorem B845315 : Blo 562809 845315 := bstep (se 1 (by rfl) ⟨633986, by rfl⟩ : syracuseStep 845315 = 1267973) B1267973
theorem B845345 : Blo 562809 845345 := bstep (se 2 (by rfl) ⟨317004, by rfl⟩ : syracuseStep 845345 = 634009) B634009
theorem B845363 : Blo 562809 845363 := bstep (se 1 (by rfl) ⟨634022, by rfl⟩ : syracuseStep 845363 = 1268045) B1268045
theorem B845393 : Blo 562809 845393 := bstep (se 2 (by rfl) ⟨317022, by rfl⟩ : syracuseStep 845393 = 634045) B634045
theorem B845411 : Blo 562809 845411 := bstep (se 1 (by rfl) ⟨634058, by rfl⟩ : syracuseStep 845411 = 1268117) B1268117
theorem B2418275 : Blo 562809 2418275 := bstep (se 1 (by rfl) ⟨1813706, by rfl⟩ : syracuseStep 2418275 = 3627413) B3627413
theorem B845441 : Blo 562809 845441 := bstep (se 2 (by rfl) ⟨317040, by rfl⟩ : syracuseStep 845441 = 634081) B634081
theorem B845459 : Blo 562809 845459 := bstep (se 1 (by rfl) ⟨634094, by rfl⟩ : syracuseStep 845459 = 1268189) B1268189
theorem B845489 : Blo 562809 845489 := bstep (se 2 (by rfl) ⟨317058, by rfl⟩ : syracuseStep 845489 = 634117) B634117
theorem B1074865 : Blo 562809 1074865 := bstep (se 2 (by rfl) ⟨403074, by rfl⟩ : syracuseStep 1074865 = 806149) B806149
theorem B845507 : Blo 562809 845507 := bstep (se 1 (by rfl) ⟨634130, by rfl⟩ : syracuseStep 845507 = 1268261) B1268261
theorem B845537 : Blo 562809 845537 := bstep (se 2 (by rfl) ⟨317076, by rfl⟩ : syracuseStep 845537 = 634153) B634153
theorem B1271537 : Blo 562809 1271537 := bstep (se 2 (by rfl) ⟨476826, by rfl⟩ : syracuseStep 1271537 = 953653) B953653
theorem B845555 : Blo 562809 845555 := bstep (se 1 (by rfl) ⟨634166, by rfl⟩ : syracuseStep 845555 = 1268333) B1268333
theorem B1271555 : Blo 562809 1271555 := bstep (se 1 (by rfl) ⟨953666, by rfl⟩ : syracuseStep 1271555 = 1907333) B1907333
theorem B845585 : Blo 562809 845585 := bstep (se 2 (by rfl) ⟨317094, by rfl⟩ : syracuseStep 845585 = 634189) B634189
theorem B845603 : Blo 562809 845603 := bstep (se 1 (by rfl) ⟨634202, by rfl⟩ : syracuseStep 845603 = 1268405) B1268405
theorem B845633 : Blo 562809 845633 := bstep (se 2 (by rfl) ⟨317112, by rfl⟩ : syracuseStep 845633 = 634225) B634225
theorem B1075025 : Blo 562809 1075025 := bstep (se 2 (by rfl) ⟨403134, by rfl⟩ : syracuseStep 1075025 = 806269) B806269
theorem B845651 : Blo 562809 845651 := bstep (se 1 (by rfl) ⟨634238, by rfl⟩ : syracuseStep 845651 = 1268477) B1268477
theorem B845681 : Blo 562809 845681 := bstep (se 2 (by rfl) ⟨317130, by rfl⟩ : syracuseStep 845681 = 634261) B634261
theorem B845699 : Blo 562809 845699 := bstep (se 1 (by rfl) ⟨634274, by rfl⟩ : syracuseStep 845699 = 1268549) B1268549
theorem B845729 : Blo 562809 845729 := bstep (se 2 (by rfl) ⟨317148, by rfl⟩ : syracuseStep 845729 = 634297) B634297
theorem B845747 : Blo 562809 845747 := bstep (se 1 (by rfl) ⟨634310, by rfl⟩ : syracuseStep 845747 = 1268621) B1268621
theorem B845777 : Blo 562809 845777 := bstep (se 2 (by rfl) ⟨317166, by rfl⟩ : syracuseStep 845777 = 634333) B634333
theorem B845795 : Blo 562809 845795 := bstep (se 1 (by rfl) ⟨634346, by rfl⟩ : syracuseStep 845795 = 1268693) B1268693
theorem B714739 : Blo 562809 714739 := bstep (se 1 (by rfl) ⟨536054, by rfl⟩ : syracuseStep 714739 = 1072109) B1072109
theorem B845825 : Blo 562809 845825 := bstep (se 2 (by rfl) ⟨317184, by rfl⟩ : syracuseStep 845825 = 634369) B634369
theorem B1009667 : Blo 562809 1009667 := bstep (se 1 (by rfl) ⟨757250, by rfl⟩ : syracuseStep 1009667 = 1514501) B1514501
theorem B813073 : Blo 562809 813073 := bstep (se 2 (by rfl) ⟨304902, by rfl⟩ : syracuseStep 813073 = 609805) B609805
theorem B1271825 : Blo 562809 1271825 := bstep (se 2 (by rfl) ⟨476934, by rfl⟩ : syracuseStep 1271825 = 953869) B953869
theorem B845843 : Blo 562809 845843 := bstep (se 1 (by rfl) ⟨634382, by rfl⟩ : syracuseStep 845843 = 1268765) B1268765
theorem B1271843 : Blo 562809 1271843 := bstep (se 1 (by rfl) ⟨953882, by rfl⟩ : syracuseStep 1271843 = 1907765) B1907765
theorem B845873 : Blo 562809 845873 := bstep (se 2 (by rfl) ⟨317202, by rfl⟩ : syracuseStep 845873 = 634405) B634405
theorem B845891 : Blo 562809 845891 := bstep (se 1 (by rfl) ⟨634418, by rfl⟩ : syracuseStep 845891 = 1268837) B1268837
theorem B1206353 : Blo 562809 1206353 := bstep (se 2 (by rfl) ⟨452382, by rfl⟩ : syracuseStep 1206353 = 904765) B904765
theorem B714835 : Blo 562809 714835 := bstep (se 1 (by rfl) ⟨536126, by rfl⟩ : syracuseStep 714835 = 1072253) B1072253
theorem B845921 : Blo 562809 845921 := bstep (se 2 (by rfl) ⟨317220, by rfl⟩ : syracuseStep 845921 = 634441) B634441
theorem B845939 : Blo 562809 845939 := bstep (se 1 (by rfl) ⟨634454, by rfl⟩ : syracuseStep 845939 = 1268909) B1268909
theorem B1927313 : Blo 562809 1927313 := bstep (se 2 (by rfl) ⟨722742, by rfl⟩ : syracuseStep 1927313 = 1445485) B1445485
theorem B845969 : Blo 562809 845969 := bstep (se 2 (by rfl) ⟨317238, by rfl⟩ : syracuseStep 845969 = 634477) B634477
theorem B845987 : Blo 562809 845987 := bstep (se 1 (by rfl) ⟨634490, by rfl⟩ : syracuseStep 845987 = 1268981) B1268981
theorem B846017 : Blo 562809 846017 := bstep (se 2 (by rfl) ⟨317256, by rfl⟩ : syracuseStep 846017 = 634513) B634513
theorem B846035 : Blo 562809 846035 := bstep (se 1 (by rfl) ⟨634526, by rfl⟩ : syracuseStep 846035 = 1269053) B1269053
theorem B1075427 : Blo 562809 1075427 := bstep (se 1 (by rfl) ⟨806570, by rfl⟩ : syracuseStep 1075427 = 1613141) B1613141
theorem B846065 : Blo 562809 846065 := bstep (se 2 (by rfl) ⟨317274, by rfl⟩ : syracuseStep 846065 = 634549) B634549
theorem B846083 : Blo 562809 846083 := bstep (se 1 (by rfl) ⟨634562, by rfl⟩ : syracuseStep 846083 = 1269125) B1269125
theorem B846113 : Blo 562809 846113 := bstep (se 2 (by rfl) ⟨317292, by rfl⟩ : syracuseStep 846113 = 634585) B634585
theorem B1272113 : Blo 562809 1272113 := bstep (se 2 (by rfl) ⟨477042, by rfl⟩ : syracuseStep 1272113 = 954085) B954085
theorem B846131 : Blo 562809 846131 := bstep (se 1 (by rfl) ⟨634598, by rfl⟩ : syracuseStep 846131 = 1269197) B1269197
theorem B1272131 : Blo 562809 1272131 := bstep (se 1 (by rfl) ⟨954098, by rfl⟩ : syracuseStep 1272131 = 1908197) B1908197
theorem B846161 : Blo 562809 846161 := bstep (se 2 (by rfl) ⟨317310, by rfl⟩ : syracuseStep 846161 = 634621) B634621
theorem B846179 : Blo 562809 846179 := bstep (se 1 (by rfl) ⟨634634, by rfl⟩ : syracuseStep 846179 = 1269269) B1269269
theorem B846209 : Blo 562809 846209 := bstep (se 2 (by rfl) ⟨317328, by rfl⟩ : syracuseStep 846209 = 634657) B634657
theorem B846227 : Blo 562809 846227 := bstep (se 1 (by rfl) ⟨634670, by rfl⟩ : syracuseStep 846227 = 1269341) B1269341
theorem B846257 : Blo 562809 846257 := bstep (se 2 (by rfl) ⟨317346, by rfl⟩ : syracuseStep 846257 = 634693) B634693
theorem B846275 : Blo 562809 846275 := bstep (se 1 (by rfl) ⟨634706, by rfl⟩ : syracuseStep 846275 = 1269413) B1269413
theorem B846305 : Blo 562809 846305 := bstep (se 2 (by rfl) ⟨317364, by rfl⟩ : syracuseStep 846305 = 634729) B634729
theorem B846323 : Blo 562809 846323 := bstep (se 1 (by rfl) ⟨634742, by rfl⟩ : syracuseStep 846323 = 1269485) B1269485
theorem B846353 : Blo 562809 846353 := bstep (se 2 (by rfl) ⟨317382, by rfl⟩ : syracuseStep 846353 = 634765) B634765
theorem B846371 : Blo 562809 846371 := bstep (se 1 (by rfl) ⟨634778, by rfl⟩ : syracuseStep 846371 = 1269557) B1269557
theorem B846401 : Blo 562809 846401 := bstep (se 2 (by rfl) ⟨317400, by rfl⟩ : syracuseStep 846401 = 634801) B634801
theorem B715331 : Blo 562809 715331 := bstep (se 1 (by rfl) ⟨536498, by rfl⟩ : syracuseStep 715331 = 1072997) B1072997
theorem B1272401 : Blo 562809 1272401 := bstep (se 2 (by rfl) ⟨477150, by rfl⟩ : syracuseStep 1272401 = 954301) B954301
theorem B846419 : Blo 562809 846419 := bstep (se 1 (by rfl) ⟨634814, by rfl⟩ : syracuseStep 846419 = 1269629) B1269629
theorem B1272419 : Blo 562809 1272419 := bstep (se 1 (by rfl) ⟨954314, by rfl⟩ : syracuseStep 1272419 = 1908629) B1908629
theorem B846449 : Blo 562809 846449 := bstep (se 2 (by rfl) ⟨317418, by rfl⟩ : syracuseStep 846449 = 634837) B634837
theorem B846467 : Blo 562809 846467 := bstep (se 1 (by rfl) ⟨634850, by rfl⟩ : syracuseStep 846467 = 1269701) B1269701
theorem B846497 : Blo 562809 846497 := bstep (se 2 (by rfl) ⟨317436, by rfl⟩ : syracuseStep 846497 = 634873) B634873
theorem B846515 : Blo 562809 846515 := bstep (se 1 (by rfl) ⟨634886, by rfl⟩ : syracuseStep 846515 = 1269773) B1269773
theorem B846545 : Blo 562809 846545 := bstep (se 2 (by rfl) ⟨317454, by rfl⟩ : syracuseStep 846545 = 634909) B634909
theorem B846563 : Blo 562809 846563 := bstep (se 1 (by rfl) ⟨634922, by rfl⟩ : syracuseStep 846563 = 1269845) B1269845
theorem B846593 : Blo 562809 846593 := bstep (se 2 (by rfl) ⟨317472, by rfl⟩ : syracuseStep 846593 = 634945) B634945
theorem B846611 : Blo 562809 846611 := bstep (se 1 (by rfl) ⟨634958, by rfl⟩ : syracuseStep 846611 = 1269917) B1269917
theorem B846641 : Blo 562809 846641 := bstep (se 2 (by rfl) ⟨317490, by rfl⟩ : syracuseStep 846641 = 634981) B634981
theorem B846659 : Blo 562809 846659 := bstep (se 1 (by rfl) ⟨634994, by rfl⟩ : syracuseStep 846659 = 1269989) B1269989
theorem B846689 : Blo 562809 846689 := bstep (se 2 (by rfl) ⟨317508, by rfl⟩ : syracuseStep 846689 = 635017) B635017
theorem B1272689 : Blo 562809 1272689 := bstep (se 2 (by rfl) ⟨477258, by rfl⟩ : syracuseStep 1272689 = 954517) B954517
theorem B846707 : Blo 562809 846707 := bstep (se 1 (by rfl) ⟨635030, by rfl⟩ : syracuseStep 846707 = 1270061) B1270061
theorem B1272707 : Blo 562809 1272707 := bstep (se 1 (by rfl) ⟨954530, by rfl⟩ : syracuseStep 1272707 = 1909061) B1909061
theorem B846737 : Blo 562809 846737 := bstep (se 2 (by rfl) ⟨317526, by rfl⟩ : syracuseStep 846737 = 635053) B635053
theorem B3206051 : Blo 562809 3206051 := bstep (se 1 (by rfl) ⟨2404538, by rfl⟩ : syracuseStep 3206051 = 4809077) B4809077
theorem B846755 : Blo 562809 846755 := bstep (se 1 (by rfl) ⟨635066, by rfl⟩ : syracuseStep 846755 = 1270133) B1270133
theorem B1207217 : Blo 562809 1207217 := bstep (se 2 (by rfl) ⟨452706, by rfl⟩ : syracuseStep 1207217 = 905413) B905413
theorem B846785 : Blo 562809 846785 := bstep (se 2 (by rfl) ⟨317544, by rfl⟩ : syracuseStep 846785 = 635089) B635089
theorem B846803 : Blo 562809 846803 := bstep (se 1 (by rfl) ⟨635102, by rfl⟩ : syracuseStep 846803 = 1270205) B1270205
theorem B846833 : Blo 562809 846833 := bstep (se 2 (by rfl) ⟨317562, by rfl⟩ : syracuseStep 846833 = 635125) B635125
theorem B846851 : Blo 562809 846851 := bstep (se 1 (by rfl) ⟨635138, by rfl⟩ : syracuseStep 846851 = 1270277) B1270277
theorem B846881 : Blo 562809 846881 := bstep (se 2 (by rfl) ⟨317580, by rfl⟩ : syracuseStep 846881 = 635161) B635161
theorem B846899 : Blo 562809 846899 := bstep (se 1 (by rfl) ⟨635174, by rfl⟩ : syracuseStep 846899 = 1270349) B1270349
theorem B846929 : Blo 562809 846929 := bstep (se 2 (by rfl) ⟨317598, by rfl⟩ : syracuseStep 846929 = 635197) B635197
theorem B846947 : Blo 562809 846947 := bstep (se 1 (by rfl) ⟨635210, by rfl⟩ : syracuseStep 846947 = 1270421) B1270421
theorem B846977 : Blo 562809 846977 := bstep (se 2 (by rfl) ⟨317616, by rfl⟩ : syracuseStep 846977 = 635233) B635233
theorem B1272977 : Blo 562809 1272977 := bstep (se 2 (by rfl) ⟨477366, by rfl⟩ : syracuseStep 1272977 = 954733) B954733
theorem B846995 : Blo 562809 846995 := bstep (se 1 (by rfl) ⟨635246, by rfl⟩ : syracuseStep 846995 = 1270493) B1270493
theorem B1272995 : Blo 562809 1272995 := bstep (se 1 (by rfl) ⟨954746, by rfl⟩ : syracuseStep 1272995 = 1909493) B1909493
theorem B847025 : Blo 562809 847025 := bstep (se 2 (by rfl) ⟨317634, by rfl⟩ : syracuseStep 847025 = 635269) B635269
theorem B847043 : Blo 562809 847043 := bstep (se 1 (by rfl) ⟨635282, by rfl⟩ : syracuseStep 847043 = 1270565) B1270565
theorem B847073 : Blo 562809 847073 := bstep (se 2 (by rfl) ⟨317652, by rfl⟩ : syracuseStep 847073 = 635305) B635305
theorem B847091 : Blo 562809 847091 := bstep (se 1 (by rfl) ⟨635318, by rfl⟩ : syracuseStep 847091 = 1270637) B1270637
theorem B716035 : Blo 562809 716035 := bstep (se 1 (by rfl) ⟨537026, by rfl⟩ : syracuseStep 716035 = 1074053) B1074053
theorem B847121 : Blo 562809 847121 := bstep (se 2 (by rfl) ⟨317670, by rfl⟩ : syracuseStep 847121 = 635341) B635341
theorem B847139 : Blo 562809 847139 := bstep (se 1 (by rfl) ⟨635354, by rfl⟩ : syracuseStep 847139 = 1270709) B1270709
theorem B847169 : Blo 562809 847169 := bstep (se 2 (by rfl) ⟨317688, by rfl⟩ : syracuseStep 847169 = 635377) B635377
theorem B847187 : Blo 562809 847187 := bstep (se 1 (by rfl) ⟨635390, by rfl⟩ : syracuseStep 847187 = 1270781) B1270781
theorem B716131 : Blo 562809 716131 := bstep (se 1 (by rfl) ⟨537098, by rfl⟩ : syracuseStep 716131 = 1074197) B1074197
theorem B847217 : Blo 562809 847217 := bstep (se 2 (by rfl) ⟨317706, by rfl⟩ : syracuseStep 847217 = 635413) B635413
theorem B847235 : Blo 562809 847235 := bstep (se 1 (by rfl) ⟨635426, by rfl⟩ : syracuseStep 847235 = 1270853) B1270853
theorem B847265 : Blo 562809 847265 := bstep (se 2 (by rfl) ⟨317724, by rfl⟩ : syracuseStep 847265 = 635449) B635449
theorem B1273265 : Blo 562809 1273265 := bstep (se 2 (by rfl) ⟨477474, by rfl⟩ : syracuseStep 1273265 = 954949) B954949
theorem B847283 : Blo 562809 847283 := bstep (se 1 (by rfl) ⟨635462, by rfl⟩ : syracuseStep 847283 = 1270925) B1270925
theorem B1273283 : Blo 562809 1273283 := bstep (se 1 (by rfl) ⟨954962, by rfl⟩ : syracuseStep 1273283 = 1909925) B1909925
theorem B847313 : Blo 562809 847313 := bstep (se 2 (by rfl) ⟨317742, by rfl⟩ : syracuseStep 847313 = 635485) B635485
theorem B847331 : Blo 562809 847331 := bstep (se 1 (by rfl) ⟨635498, by rfl⟩ : syracuseStep 847331 = 1270997) B1270997
theorem B847361 : Blo 562809 847361 := bstep (se 2 (by rfl) ⟨317760, by rfl⟩ : syracuseStep 847361 = 635521) B635521
theorem B847379 : Blo 562809 847379 := bstep (se 1 (by rfl) ⟨635534, by rfl⟩ : syracuseStep 847379 = 1271069) B1271069
theorem B847409 : Blo 562809 847409 := bstep (se 2 (by rfl) ⟨317778, by rfl⟩ : syracuseStep 847409 = 635557) B635557
theorem B847427 : Blo 562809 847427 := bstep (se 1 (by rfl) ⟨635570, by rfl⟩ : syracuseStep 847427 = 1271141) B1271141
theorem B847457 : Blo 562809 847457 := bstep (se 2 (by rfl) ⟨317796, by rfl⟩ : syracuseStep 847457 = 635593) B635593
theorem B1830509 : Blo 562809 1830509 := bstep (se 3 (by rfl) ⟨343220, by rfl⟩ : syracuseStep 1830509 = 686441) B686441
theorem B847475 : Blo 562809 847475 := bstep (se 1 (by rfl) ⟨635606, by rfl⟩ : syracuseStep 847475 = 1271213) B1271213
theorem B847505 : Blo 562809 847505 := bstep (se 2 (by rfl) ⟨317814, by rfl⟩ : syracuseStep 847505 = 635629) B635629
theorem B847523 : Blo 562809 847523 := bstep (se 1 (by rfl) ⟨635642, by rfl⟩ : syracuseStep 847523 = 1271285) B1271285
theorem B847553 : Blo 562809 847553 := bstep (se 2 (by rfl) ⟨317832, by rfl⟩ : syracuseStep 847553 = 635665) B635665
theorem B4419269 : Blo 562809 4419269 := bstep (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) B828613
theorem B1633997 : Blo 562809 1633997 := bstep (se 3 (by rfl) ⟨306374, by rfl⟩ : syracuseStep 1633997 = 612749) B612749
theorem B1273553 : Blo 562809 1273553 := bstep (se 2 (by rfl) ⟨477582, by rfl⟩ : syracuseStep 1273553 = 955165) B955165
theorem B847571 : Blo 562809 847571 := bstep (se 1 (by rfl) ⟨635678, by rfl⟩ : syracuseStep 847571 = 1271357) B1271357
theorem B1273571 : Blo 562809 1273571 := bstep (se 1 (by rfl) ⟨955178, by rfl⟩ : syracuseStep 1273571 = 1910357) B1910357
theorem B847601 : Blo 562809 847601 := bstep (se 2 (by rfl) ⟨317850, by rfl⟩ : syracuseStep 847601 = 635701) B635701
theorem B847619 : Blo 562809 847619 := bstep (se 1 (by rfl) ⟨635714, by rfl⟩ : syracuseStep 847619 = 1271429) B1271429
theorem B847649 : Blo 562809 847649 := bstep (se 2 (by rfl) ⟨317868, by rfl⟩ : syracuseStep 847649 = 635737) B635737
theorem B847667 : Blo 562809 847667 := bstep (se 1 (by rfl) ⟨635750, by rfl⟩ : syracuseStep 847667 = 1271501) B1271501
theorem B847697 : Blo 562809 847697 := bstep (se 2 (by rfl) ⟨317886, by rfl⟩ : syracuseStep 847697 = 635773) B635773
theorem B716627 : Blo 562809 716627 := bstep (se 1 (by rfl) ⟨537470, by rfl⟩ : syracuseStep 716627 = 1074941) B1074941
theorem B847715 : Blo 562809 847715 := bstep (se 1 (by rfl) ⟨635786, by rfl⟩ : syracuseStep 847715 = 1271573) B1271573
theorem B847745 : Blo 562809 847745 := bstep (se 2 (by rfl) ⟨317904, by rfl⟩ : syracuseStep 847745 = 635809) B635809
theorem B3207053 : Blo 562809 3207053 := bstep (se 3 (by rfl) ⟨601322, by rfl⟩ : syracuseStep 3207053 = 1202645) B1202645
theorem B847763 : Blo 562809 847763 := bstep (se 1 (by rfl) ⟨635822, by rfl⟩ : syracuseStep 847763 = 1271645) B1271645
theorem B847793 : Blo 562809 847793 := bstep (se 2 (by rfl) ⟨317922, by rfl⟩ : syracuseStep 847793 = 635845) B635845
theorem B847811 : Blo 562809 847811 := bstep (se 1 (by rfl) ⟨635858, by rfl⟩ : syracuseStep 847811 = 1271717) B1271717
theorem B847841 : Blo 562809 847841 := bstep (se 2 (by rfl) ⟨317940, by rfl⟩ : syracuseStep 847841 = 635881) B635881
theorem B1273841 : Blo 562809 1273841 := bstep (se 2 (by rfl) ⟨477690, by rfl⟩ : syracuseStep 1273841 = 955381) B955381
theorem B847859 : Blo 562809 847859 := bstep (se 1 (by rfl) ⟨635894, by rfl⟩ : syracuseStep 847859 = 1271789) B1271789
theorem B1273859 : Blo 562809 1273859 := bstep (se 1 (by rfl) ⟨955394, by rfl⟩ : syracuseStep 1273859 = 1910789) B1910789
theorem B847889 : Blo 562809 847889 := bstep (se 2 (by rfl) ⟨317958, by rfl⟩ : syracuseStep 847889 = 635917) B635917
theorem B847907 : Blo 562809 847907 := bstep (se 1 (by rfl) ⟨635930, by rfl⟩ : syracuseStep 847907 = 1271861) B1271861
theorem B847937 : Blo 562809 847937 := bstep (se 2 (by rfl) ⟨317976, by rfl⟩ : syracuseStep 847937 = 635953) B635953
theorem B847955 : Blo 562809 847955 := bstep (se 1 (by rfl) ⟨635966, by rfl⟩ : syracuseStep 847955 = 1271933) B1271933
theorem B847985 : Blo 562809 847985 := bstep (se 2 (by rfl) ⟨317994, by rfl⟩ : syracuseStep 847985 = 635989) B635989
theorem B848003 : Blo 562809 848003 := bstep (se 1 (by rfl) ⟨636002, by rfl⟩ : syracuseStep 848003 = 1272005) B1272005
theorem B848033 : Blo 562809 848033 := bstep (se 2 (by rfl) ⟨318012, by rfl⟩ : syracuseStep 848033 = 636025) B636025
theorem B848051 : Blo 562809 848051 := bstep (se 1 (by rfl) ⟨636038, by rfl⟩ : syracuseStep 848051 = 1272077) B1272077
theorem B1208515 : Blo 562809 1208515 := bstep (se 1 (by rfl) ⟨906386, by rfl⟩ : syracuseStep 1208515 = 1812773) B1812773
theorem B2420941 : Blo 562809 2420941 := bstep (se 3 (by rfl) ⟨453926, by rfl⟩ : syracuseStep 2420941 = 907853) B907853
theorem B848081 : Blo 562809 848081 := bstep (se 2 (by rfl) ⟨318030, by rfl⟩ : syracuseStep 848081 = 636061) B636061
theorem B848099 : Blo 562809 848099 := bstep (se 1 (by rfl) ⟨636074, by rfl⟩ : syracuseStep 848099 = 1272149) B1272149
theorem B848129 : Blo 562809 848129 := bstep (se 2 (by rfl) ⟨318048, by rfl⟩ : syracuseStep 848129 = 636097) B636097
theorem B1274129 : Blo 562809 1274129 := bstep (se 2 (by rfl) ⟨477798, by rfl⟩ : syracuseStep 1274129 = 955597) B955597
theorem B848147 : Blo 562809 848147 := bstep (se 1 (by rfl) ⟨636110, by rfl⟩ : syracuseStep 848147 = 1272221) B1272221
theorem B1274147 : Blo 562809 1274147 := bstep (se 1 (by rfl) ⟨955610, by rfl⟩ : syracuseStep 1274147 = 1911221) B1911221
theorem B848177 : Blo 562809 848177 := bstep (se 2 (by rfl) ⟨318066, by rfl⟩ : syracuseStep 848177 = 636133) B636133
theorem B848195 : Blo 562809 848195 := bstep (se 1 (by rfl) ⟨636146, by rfl⟩ : syracuseStep 848195 = 1272293) B1272293
theorem B848225 : Blo 562809 848225 := bstep (se 2 (by rfl) ⟨318084, by rfl⟩ : syracuseStep 848225 = 636169) B636169
theorem B848243 : Blo 562809 848243 := bstep (se 1 (by rfl) ⟨636182, by rfl⟩ : syracuseStep 848243 = 1272365) B1272365
theorem B848273 : Blo 562809 848273 := bstep (se 2 (by rfl) ⟨318102, by rfl⟩ : syracuseStep 848273 = 636205) B636205
theorem B848291 : Blo 562809 848291 := bstep (se 1 (by rfl) ⟨636218, by rfl⟩ : syracuseStep 848291 = 1272437) B1272437
theorem B848321 : Blo 562809 848321 := bstep (se 2 (by rfl) ⟨318120, by rfl⟩ : syracuseStep 848321 = 636241) B636241
theorem B848339 : Blo 562809 848339 := bstep (se 1 (by rfl) ⟨636254, by rfl⟩ : syracuseStep 848339 = 1272509) B1272509
theorem B848369 : Blo 562809 848369 := bstep (se 2 (by rfl) ⟨318138, by rfl⟩ : syracuseStep 848369 = 636277) B636277
theorem B848387 : Blo 562809 848387 := bstep (se 1 (by rfl) ⟨636290, by rfl⟩ : syracuseStep 848387 = 1272581) B1272581
theorem B717331 : Blo 562809 717331 := bstep (se 1 (by rfl) ⟨537998, by rfl⟩ : syracuseStep 717331 = 1075997) B1075997
theorem B848417 : Blo 562809 848417 := bstep (se 2 (by rfl) ⟨318156, by rfl⟩ : syracuseStep 848417 = 636313) B636313
theorem B3469873 : Blo 562809 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B1274417 : Blo 562809 1274417 := bstep (se 2 (by rfl) ⟨477906, by rfl⟩ : syracuseStep 1274417 = 955813) B955813
theorem B848435 : Blo 562809 848435 := bstep (se 1 (by rfl) ⟨636326, by rfl⟩ : syracuseStep 848435 = 1272653) B1272653
theorem B1274435 : Blo 562809 1274435 := bstep (se 1 (by rfl) ⟨955826, by rfl⟩ : syracuseStep 1274435 = 1911653) B1911653
theorem B848465 : Blo 562809 848465 := bstep (se 2 (by rfl) ⟨318174, by rfl⟩ : syracuseStep 848465 = 636349) B636349
theorem B3043939 : Blo 562809 3043939 := bstep (se 1 (by rfl) ⟨2282954, by rfl⟩ : syracuseStep 3043939 = 4565909) B4565909
theorem B848483 : Blo 562809 848483 := bstep (se 1 (by rfl) ⟨636362, by rfl⟩ : syracuseStep 848483 = 1272725) B1272725
theorem B848513 : Blo 562809 848513 := bstep (se 2 (by rfl) ⟨318192, by rfl⟩ : syracuseStep 848513 = 636385) B636385
theorem B848531 : Blo 562809 848531 := bstep (se 1 (by rfl) ⟨636398, by rfl⟩ : syracuseStep 848531 = 1272797) B1272797
theorem B848561 : Blo 562809 848561 := bstep (se 2 (by rfl) ⟨318210, by rfl⟩ : syracuseStep 848561 = 636421) B636421
theorem B848579 : Blo 562809 848579 := bstep (se 1 (by rfl) ⟨636434, by rfl⟩ : syracuseStep 848579 = 1272869) B1272869
theorem B848609 : Blo 562809 848609 := bstep (se 2 (by rfl) ⟨318228, by rfl⟩ : syracuseStep 848609 = 636457) B636457
theorem B848627 : Blo 562809 848627 := bstep (se 1 (by rfl) ⟨636470, by rfl⟩ : syracuseStep 848627 = 1272941) B1272941
theorem B848657 : Blo 562809 848657 := bstep (se 2 (by rfl) ⟨318246, by rfl⟩ : syracuseStep 848657 = 636493) B636493
theorem B848675 : Blo 562809 848675 := bstep (se 1 (by rfl) ⟨636506, by rfl⟩ : syracuseStep 848675 = 1273013) B1273013
theorem B848705 : Blo 562809 848705 := bstep (se 2 (by rfl) ⟨318264, by rfl⟩ : syracuseStep 848705 = 636529) B636529
theorem B1274705 : Blo 562809 1274705 := bstep (se 2 (by rfl) ⟨478014, by rfl⟩ : syracuseStep 1274705 = 956029) B956029
theorem B848723 : Blo 562809 848723 := bstep (se 1 (by rfl) ⟨636542, by rfl⟩ : syracuseStep 848723 = 1273085) B1273085
theorem B1274723 : Blo 562809 1274723 := bstep (se 1 (by rfl) ⟨956042, by rfl⟩ : syracuseStep 1274723 = 1912085) B1912085
theorem B848753 : Blo 562809 848753 := bstep (se 2 (by rfl) ⟨318282, by rfl⟩ : syracuseStep 848753 = 636565) B636565
theorem B848771 : Blo 562809 848771 := bstep (se 1 (by rfl) ⟨636578, by rfl⟩ : syracuseStep 848771 = 1273157) B1273157
theorem B848801 : Blo 562809 848801 := bstep (se 2 (by rfl) ⟨318300, by rfl⟩ : syracuseStep 848801 = 636601) B636601
theorem B1143715 : Blo 562809 1143715 := bstep (se 1 (by rfl) ⟨857786, by rfl⟩ : syracuseStep 1143715 = 1715573) B1715573
theorem B2290609 : Blo 562809 2290609 := bstep (se 2 (by rfl) ⟨858978, by rfl⟩ : syracuseStep 2290609 = 1717957) B1717957
theorem B848819 : Blo 562809 848819 := bstep (se 1 (by rfl) ⟨636614, by rfl⟩ : syracuseStep 848819 = 1273229) B1273229
theorem B848849 : Blo 562809 848849 := bstep (se 2 (by rfl) ⟨318318, by rfl⟩ : syracuseStep 848849 = 636637) B636637
theorem B848867 : Blo 562809 848867 := bstep (se 1 (by rfl) ⟨636650, by rfl⟩ : syracuseStep 848867 = 1273301) B1273301
theorem B848897 : Blo 562809 848897 := bstep (se 2 (by rfl) ⟨318336, by rfl⟩ : syracuseStep 848897 = 636673) B636673
theorem B848915 : Blo 562809 848915 := bstep (se 1 (by rfl) ⟨636686, by rfl⟩ : syracuseStep 848915 = 1273373) B1273373
theorem B848945 : Blo 562809 848945 := bstep (se 2 (by rfl) ⟨318354, by rfl⟩ : syracuseStep 848945 = 636709) B636709
theorem B848963 : Blo 562809 848963 := bstep (se 1 (by rfl) ⟨636722, by rfl⟩ : syracuseStep 848963 = 1273445) B1273445
theorem B848993 : Blo 562809 848993 := bstep (se 2 (by rfl) ⟨318372, by rfl⟩ : syracuseStep 848993 = 636745) B636745
theorem B1274993 : Blo 562809 1274993 := bstep (se 2 (by rfl) ⟨478122, by rfl⟩ : syracuseStep 1274993 = 956245) B956245
theorem B849011 : Blo 562809 849011 := bstep (se 1 (by rfl) ⟨636758, by rfl⟩ : syracuseStep 849011 = 1273517) B1273517
theorem B1275011 : Blo 562809 1275011 := bstep (se 1 (by rfl) ⟨956258, by rfl⟩ : syracuseStep 1275011 = 1912517) B1912517
theorem B849041 : Blo 562809 849041 := bstep (se 2 (by rfl) ⟨318390, by rfl⟩ : syracuseStep 849041 = 636781) B636781
theorem B849059 : Blo 562809 849059 := bstep (se 1 (by rfl) ⟨636794, by rfl⟩ : syracuseStep 849059 = 1273589) B1273589
theorem B980147 : Blo 562809 980147 := bstep (se 1 (by rfl) ⟨735110, by rfl⟩ : syracuseStep 980147 = 1470221) B1470221
theorem B849089 : Blo 562809 849089 := bstep (se 2 (by rfl) ⟨318408, by rfl⟩ : syracuseStep 849089 = 636817) B636817
theorem B849107 : Blo 562809 849107 := bstep (se 1 (by rfl) ⟨636830, by rfl⟩ : syracuseStep 849107 = 1273661) B1273661
theorem B1602787 : Blo 562809 1602787 := bstep (se 1 (by rfl) ⟨1202090, by rfl⟩ : syracuseStep 1602787 = 2404181) B2404181
theorem B849137 : Blo 562809 849137 := bstep (se 2 (by rfl) ⟨318426, by rfl⟩ : syracuseStep 849137 = 636853) B636853
theorem B849155 : Blo 562809 849155 := bstep (se 1 (by rfl) ⟨636866, by rfl⟩ : syracuseStep 849155 = 1273733) B1273733
theorem B849185 : Blo 562809 849185 := bstep (se 2 (by rfl) ⟨318444, by rfl⟩ : syracuseStep 849185 = 636889) B636889
theorem B849203 : Blo 562809 849203 := bstep (se 1 (by rfl) ⟨636902, by rfl⟩ : syracuseStep 849203 = 1273805) B1273805
theorem B849233 : Blo 562809 849233 := bstep (se 2 (by rfl) ⟨318462, by rfl⟩ : syracuseStep 849233 = 636925) B636925
theorem B849251 : Blo 562809 849251 := bstep (se 1 (by rfl) ⟨636938, by rfl⟩ : syracuseStep 849251 = 1273877) B1273877
theorem B849281 : Blo 562809 849281 := bstep (se 2 (by rfl) ⟨318480, by rfl⟩ : syracuseStep 849281 = 636961) B636961
theorem B3437957 : Blo 562809 3437957 := bstep (se 4 (by rfl) ⟨322308, by rfl⟩ : syracuseStep 3437957 = 644617) B644617
theorem B1209745 : Blo 562809 1209745 := bstep (se 2 (by rfl) ⟨453654, by rfl⟩ : syracuseStep 1209745 = 907309) B907309
theorem B1275281 : Blo 562809 1275281 := bstep (se 2 (by rfl) ⟨478230, by rfl⟩ : syracuseStep 1275281 = 956461) B956461
theorem B849299 : Blo 562809 849299 := bstep (se 1 (by rfl) ⟨636974, by rfl⟩ : syracuseStep 849299 = 1273949) B1273949
theorem B1275299 : Blo 562809 1275299 := bstep (se 1 (by rfl) ⟨956474, by rfl⟩ : syracuseStep 1275299 = 1912949) B1912949
theorem B849329 : Blo 562809 849329 := bstep (se 2 (by rfl) ⟨318498, by rfl⟩ : syracuseStep 849329 = 636997) B636997
theorem B849347 : Blo 562809 849347 := bstep (se 1 (by rfl) ⟨637010, by rfl⟩ : syracuseStep 849347 = 1274021) B1274021
theorem B849377 : Blo 562809 849377 := bstep (se 2 (by rfl) ⟨318516, by rfl⟩ : syracuseStep 849377 = 637033) B637033
theorem B849395 : Blo 562809 849395 := bstep (se 1 (by rfl) ⟨637046, by rfl⟩ : syracuseStep 849395 = 1274093) B1274093
theorem B849425 : Blo 562809 849425 := bstep (se 2 (by rfl) ⟨318534, by rfl⟩ : syracuseStep 849425 = 637069) B637069
theorem B1930787 : Blo 562809 1930787 := bstep (se 1 (by rfl) ⟨1448090, by rfl⟩ : syracuseStep 1930787 = 2896181) B2896181
theorem B849443 : Blo 562809 849443 := bstep (se 1 (by rfl) ⟨637082, by rfl⟩ : syracuseStep 849443 = 1274165) B1274165
theorem B1963565 : Blo 562809 1963565 := bstep (se 3 (by rfl) ⟨368168, by rfl⟩ : syracuseStep 1963565 = 736337) B736337
theorem B849473 : Blo 562809 849473 := bstep (se 2 (by rfl) ⟨318552, by rfl⟩ : syracuseStep 849473 = 637105) B637105
theorem B849491 : Blo 562809 849491 := bstep (se 1 (by rfl) ⟨637118, by rfl⟩ : syracuseStep 849491 = 1274237) B1274237
theorem B849521 : Blo 562809 849521 := bstep (se 2 (by rfl) ⟨318570, by rfl⟩ : syracuseStep 849521 = 637141) B637141
theorem B849539 : Blo 562809 849539 := bstep (se 1 (by rfl) ⟨637154, by rfl⟩ : syracuseStep 849539 = 1274309) B1274309
theorem B4814477 : Blo 562809 4814477 := bstep (se 3 (by rfl) ⟨902714, by rfl⟩ : syracuseStep 4814477 = 1805429) B1805429
theorem B849569 : Blo 562809 849569 := bstep (se 2 (by rfl) ⟨318588, by rfl⟩ : syracuseStep 849569 = 637177) B637177
theorem B849587 : Blo 562809 849587 := bstep (se 1 (by rfl) ⟨637190, by rfl⟩ : syracuseStep 849587 = 1274381) B1274381
theorem B1603277 : Blo 562809 1603277 := bstep (se 3 (by rfl) ⟨300614, by rfl⟩ : syracuseStep 1603277 = 601229) B601229
theorem B849617 : Blo 562809 849617 := bstep (se 2 (by rfl) ⟨318606, by rfl⟩ : syracuseStep 849617 = 637213) B637213
theorem B849635 : Blo 562809 849635 := bstep (se 1 (by rfl) ⟨637226, by rfl⟩ : syracuseStep 849635 = 1274453) B1274453
theorem B849665 : Blo 562809 849665 := bstep (se 2 (by rfl) ⟨318624, by rfl⟩ : syracuseStep 849665 = 637249) B637249
theorem B849683 : Blo 562809 849683 := bstep (se 1 (by rfl) ⟨637262, by rfl⟩ : syracuseStep 849683 = 1274525) B1274525
theorem B849713 : Blo 562809 849713 := bstep (se 2 (by rfl) ⟨318642, by rfl⟩ : syracuseStep 849713 = 637285) B637285
theorem B849731 : Blo 562809 849731 := bstep (se 1 (by rfl) ⟨637298, by rfl⟩ : syracuseStep 849731 = 1274597) B1274597
theorem B849761 : Blo 562809 849761 := bstep (se 2 (by rfl) ⟨318660, by rfl⟩ : syracuseStep 849761 = 637321) B637321
theorem B849779 : Blo 562809 849779 := bstep (se 1 (by rfl) ⟨637334, by rfl⟩ : syracuseStep 849779 = 1274669) B1274669
theorem B849809 : Blo 562809 849809 := bstep (se 2 (by rfl) ⟨318678, by rfl⟩ : syracuseStep 849809 = 637357) B637357
theorem B849827 : Blo 562809 849827 := bstep (se 1 (by rfl) ⟨637370, by rfl⟩ : syracuseStep 849827 = 1274741) B1274741
theorem B1308593 : Blo 562809 1308593 := bstep (se 2 (by rfl) ⟨490722, by rfl⟩ : syracuseStep 1308593 = 981445) B981445
theorem B849857 : Blo 562809 849857 := bstep (se 2 (by rfl) ⟨318696, by rfl⟩ : syracuseStep 849857 = 637393) B637393
theorem B849875 : Blo 562809 849875 := bstep (se 1 (by rfl) ⟨637406, by rfl⟩ : syracuseStep 849875 = 1274813) B1274813
theorem B849905 : Blo 562809 849905 := bstep (se 2 (by rfl) ⟨318714, by rfl⟩ : syracuseStep 849905 = 637429) B637429
theorem B849923 : Blo 562809 849923 := bstep (se 1 (by rfl) ⟨637442, by rfl⟩ : syracuseStep 849923 = 1274885) B1274885
theorem B849953 : Blo 562809 849953 := bstep (se 2 (by rfl) ⟨318732, by rfl⟩ : syracuseStep 849953 = 637465) B637465
theorem B1210403 : Blo 562809 1210403 := bstep (se 1 (by rfl) ⟨907802, by rfl⟩ : syracuseStep 1210403 = 1815605) B1815605
theorem B849971 : Blo 562809 849971 := bstep (se 1 (by rfl) ⟨637478, by rfl⟩ : syracuseStep 849971 = 1274957) B1274957
theorem B850001 : Blo 562809 850001 := bstep (se 2 (by rfl) ⟨318750, by rfl⟩ : syracuseStep 850001 = 637501) B637501
theorem B850019 : Blo 562809 850019 := bstep (se 1 (by rfl) ⟨637514, by rfl⟩ : syracuseStep 850019 = 1275029) B1275029
theorem B850049 : Blo 562809 850049 := bstep (se 2 (by rfl) ⟨318768, by rfl⟩ : syracuseStep 850049 = 637537) B637537
theorem B850067 : Blo 562809 850067 := bstep (se 1 (by rfl) ⟨637550, by rfl⟩ : syracuseStep 850067 = 1275101) B1275101
theorem B850097 : Blo 562809 850097 := bstep (se 2 (by rfl) ⟨318786, by rfl⟩ : syracuseStep 850097 = 637573) B637573
theorem B850115 : Blo 562809 850115 := bstep (se 1 (by rfl) ⟨637586, by rfl⟩ : syracuseStep 850115 = 1275173) B1275173
theorem B850145 : Blo 562809 850145 := bstep (se 2 (by rfl) ⟨318804, by rfl⟩ : syracuseStep 850145 = 637609) B637609
theorem B850163 : Blo 562809 850163 := bstep (se 1 (by rfl) ⟨637622, by rfl⟩ : syracuseStep 850163 = 1275245) B1275245
theorem B850193 : Blo 562809 850193 := bstep (se 2 (by rfl) ⟨318822, by rfl⟩ : syracuseStep 850193 = 637645) B637645
theorem B850211 : Blo 562809 850211 := bstep (se 1 (by rfl) ⟨637658, by rfl⟩ : syracuseStep 850211 = 1275317) B1275317
theorem B2062883 : Blo 562809 2062883 := bstep (se 1 (by rfl) ⟨1547162, by rfl⟩ : syracuseStep 2062883 = 3094325) B3094325
theorem B2095651 : Blo 562809 2095651 := bstep (se 1 (by rfl) ⟨1571738, by rfl⟩ : syracuseStep 2095651 = 3143477) B3143477
theorem B3209969 : Blo 562809 3209969 := bstep (se 2 (by rfl) ⟨1203738, by rfl⟩ : syracuseStep 3209969 = 2407477) B2407477
theorem B1669901 : Blo 562809 1669901 := bstep (se 3 (by rfl) ⟨313106, by rfl⟩ : syracuseStep 1669901 = 626213) B626213
theorem B1604461 : Blo 562809 1604461 := bstep (se 3 (by rfl) ⟨300836, by rfl⟩ : syracuseStep 1604461 = 601673) B601673
theorem B2849741 : Blo 562809 2849741 := bstep (se 3 (by rfl) ⟨534326, by rfl⟩ : syracuseStep 2849741 = 1068653) B1068653
theorem B1899665 : Blo 562809 1899665 := bstep (se 2 (by rfl) ⟨712374, by rfl⟩ : syracuseStep 1899665 = 1424749) B1424749
theorem B2718947 : Blo 562809 2718947 := bstep (se 1 (by rfl) ⟨2039210, by rfl⟩ : syracuseStep 2718947 = 4078421) B4078421
theorem B949745 : Blo 562809 949745 := bstep (se 2 (by rfl) ⟨356154, by rfl⟩ : syracuseStep 949745 = 712309) B712309
theorem B949873 : Blo 562809 949873 := bstep (se 2 (by rfl) ⟨356202, by rfl⟩ : syracuseStep 949873 = 712405) B712405
theorem B949907 : Blo 562809 949907 := bstep (se 1 (by rfl) ⟨712430, by rfl⟩ : syracuseStep 949907 = 1424861) B1424861
theorem B1900205 : Blo 562809 1900205 := bstep (se 3 (by rfl) ⟨356288, by rfl⟩ : syracuseStep 1900205 = 712577) B712577
theorem B1900259 : Blo 562809 1900259 := bstep (se 1 (by rfl) ⟨1425194, by rfl⟩ : syracuseStep 1900259 = 2850389) B2850389
theorem B950035 : Blo 562809 950035 := bstep (se 1 (by rfl) ⟨712526, by rfl⟩ : syracuseStep 950035 = 1425053) B1425053
theorem B1605521 : Blo 562809 1605521 := bstep (se 2 (by rfl) ⟨602070, by rfl⟩ : syracuseStep 1605521 = 1204141) B1204141
theorem B950177 : Blo 562809 950177 := bstep (se 2 (by rfl) ⟨356316, by rfl⟩ : syracuseStep 950177 = 712633) B712633
theorem B4816867 : Blo 562809 4816867 := bstep (se 1 (by rfl) ⟨3612650, by rfl⟩ : syracuseStep 4816867 = 7225301) B7225301
theorem B1900529 : Blo 562809 1900529 := bstep (se 2 (by rfl) ⟨712698, by rfl⟩ : syracuseStep 1900529 = 1425397) B1425397
theorem B950359 : Blo 562809 950359 := bstep (se 1 (by rfl) ⟨712769, by rfl⟩ : syracuseStep 950359 = 1425539) B1425539
theorem B1900637 : Blo 562809 1900637 := bstep (se 3 (by rfl) ⟨356369, by rfl⟩ : syracuseStep 1900637 = 712739) B712739
theorem B1605977 : Blo 562809 1605977 := bstep (se 2 (by rfl) ⟨602241, by rfl⟩ : syracuseStep 1605977 = 1204483) B1204483
theorem B950987 : Blo 562809 950987 := bstep (se 1 (by rfl) ⟨713240, by rfl⟩ : syracuseStep 950987 = 1426481) B1426481
theorem B951115 : Blo 562809 951115 := bstep (se 1 (by rfl) ⟨713336, by rfl⟩ : syracuseStep 951115 = 1426673) B1426673
theorem B951257 : Blo 562809 951257 := bstep (se 2 (by rfl) ⟨356721, by rfl⟩ : syracuseStep 951257 = 713443) B713443
theorem B951385 : Blo 562809 951385 := bstep (se 2 (by rfl) ⟨356769, by rfl⟩ : syracuseStep 951385 = 713539) B713539
theorem B1606807 : Blo 562809 1606807 := bstep (se 1 (by rfl) ⟨1205105, by rfl⟩ : syracuseStep 1606807 = 2410211) B2410211
theorem B4293809 : Blo 562809 4293809 := bstep (se 2 (by rfl) ⟨1610178, by rfl⟩ : syracuseStep 4293809 = 3220357) B3220357
theorem B1901771 : Blo 562809 1901771 := bstep (se 1 (by rfl) ⟨1426328, by rfl⟩ : syracuseStep 1901771 = 2852657) B2852657
theorem B2852171 : Blo 562809 2852171 := bstep (se 1 (by rfl) ⟨2139128, by rfl⟩ : syracuseStep 2852171 = 4278257) B4278257
theorem B1902041 : Blo 562809 1902041 := bstep (se 2 (by rfl) ⟨713265, by rfl⟩ : syracuseStep 1902041 = 1426531) B1426531
theorem B4064813 : Blo 562809 4064813 := bstep (se 3 (by rfl) ⟨762152, by rfl⟩ : syracuseStep 4064813 = 1524305) B1524305
theorem B1803865 : Blo 562809 1803865 := bstep (se 2 (by rfl) ⟨676449, by rfl⟩ : syracuseStep 1803865 = 1352899) B1352899
theorem B951959 : Blo 562809 951959 := bstep (se 1 (by rfl) ⟨713969, by rfl⟩ : syracuseStep 951959 = 1427939) B1427939
theorem B4294295 : Blo 562809 4294295 := bstep (se 1 (by rfl) ⟨3220721, by rfl⟩ : syracuseStep 4294295 = 6441443) B6441443
theorem B4130509 : Blo 562809 4130509 := bstep (se 3 (by rfl) ⟨774470, by rfl⟩ : syracuseStep 4130509 = 1548941) B1548941
theorem B4065041 : Blo 562809 4065041 := bstep (se 2 (by rfl) ⟨1524390, by rfl⟩ : syracuseStep 4065041 = 3048781) B3048781
theorem B952087 : Blo 562809 952087 := bstep (se 1 (by rfl) ⟨714065, by rfl⟩ : syracuseStep 952087 = 1428131) B1428131
theorem B4065155 : Blo 562809 4065155 := bstep (se 1 (by rfl) ⟨3048866, by rfl⟩ : syracuseStep 4065155 = 6097733) B6097733
theorem B1607627 : Blo 562809 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B1902743 : Blo 562809 1902743 := bstep (se 1 (by rfl) ⟨1427057, by rfl⟩ : syracuseStep 1902743 = 2854115) B2854115
theorem B1804481 : Blo 562809 1804481 := bstep (se 2 (by rfl) ⟨676680, by rfl⟩ : syracuseStep 1804481 = 1353361) B1353361
theorem B1804609 : Blo 562809 1804609 := bstep (se 2 (by rfl) ⟨676728, by rfl⟩ : syracuseStep 1804609 = 1353457) B1353457
theorem B952715 : Blo 562809 952715 := bstep (se 1 (by rfl) ⟨714536, by rfl⟩ : syracuseStep 952715 = 1429073) B1429073
theorem B2034065 : Blo 562809 2034065 := bstep (se 2 (by rfl) ⟨762774, by rfl⟩ : syracuseStep 2034065 = 1525549) B1525549
theorem B952843 : Blo 562809 952843 := bstep (se 1 (by rfl) ⟨714632, by rfl⟩ : syracuseStep 952843 = 1429265) B1429265
theorem B2034193 : Blo 562809 2034193 := bstep (se 2 (by rfl) ⟨762822, by rfl⟩ : syracuseStep 2034193 = 1525645) B1525645
theorem B952985 : Blo 562809 952985 := bstep (se 2 (by rfl) ⟨357369, by rfl⟩ : syracuseStep 952985 = 714739) B714739
theorem B1903283 : Blo 562809 1903283 := bstep (se 1 (by rfl) ⟨1427462, by rfl⟩ : syracuseStep 1903283 = 2854925) B2854925
theorem B1084097 : Blo 562809 1084097 := bstep (se 2 (by rfl) ⟨406536, by rfl⟩ : syracuseStep 1084097 = 813073) B813073
theorem B6195973 : Blo 562809 6195973 := bstep (se 4 (by rfl) ⟨580872, by rfl⟩ : syracuseStep 6195973 = 1161745) B1161745
theorem B953113 : Blo 562809 953113 := bstep (se 2 (by rfl) ⟨357417, by rfl⟩ : syracuseStep 953113 = 714835) B714835
theorem B723799 : Blo 562809 723799 := bstep (se 1 (by rfl) ⟨542849, by rfl⟩ : syracuseStep 723799 = 1085699) B1085699
theorem B15928163 : Blo 562809 15928163 := bstep (se 1 (by rfl) ⟨11946122, by rfl⟩ : syracuseStep 15928163 = 23892245) B23892245
theorem B1903553 : Blo 562809 1903553 := bstep (se 2 (by rfl) ⟨713832, by rfl⟩ : syracuseStep 1903553 = 1427665) B1427665
theorem B2853953 : Blo 562809 2853953 := bstep (se 2 (by rfl) ⟨1070232, by rfl⟩ : syracuseStep 2853953 = 2140465) B2140465
theorem B6851735 : Blo 562809 6851735 := bstep (se 1 (by rfl) ⟨5138801, by rfl⟩ : syracuseStep 6851735 = 10277603) B10277603
theorem B2034989 : Blo 562809 2034989 := bstep (se 3 (by rfl) ⟨381560, by rfl⟩ : syracuseStep 2034989 = 763121) B763121
theorem B953687 : Blo 562809 953687 := bstep (se 1 (by rfl) ⟨715265, by rfl⟩ : syracuseStep 953687 = 1430531) B1430531
theorem B8129969 : Blo 562809 8129969 := bstep (se 2 (by rfl) ⟨3048738, by rfl⟩ : syracuseStep 8129969 = 6097477) B6097477
theorem B953815 : Blo 562809 953815 := bstep (se 1 (by rfl) ⟨715361, by rfl⟩ : syracuseStep 953815 = 1430723) B1430723
theorem B1904093 : Blo 562809 1904093 := bstep (se 3 (by rfl) ⟨357017, by rfl⟩ : syracuseStep 1904093 = 714035) B714035
theorem B2035289 : Blo 562809 2035289 := bstep (se 2 (by rfl) ⟨763233, by rfl⟩ : syracuseStep 2035289 = 1526467) B1526467
theorem B6524621 : Blo 562809 6524621 := bstep (se 3 (by rfl) ⟨1223366, by rfl⟩ : syracuseStep 6524621 = 2446733) B2446733
theorem B954443 : Blo 562809 954443 := bstep (se 1 (by rfl) ⟨715832, by rfl⟩ : syracuseStep 954443 = 1431665) B1431665
theorem B6951005 : Blo 562809 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B954571 : Blo 562809 954571 := bstep (se 1 (by rfl) ⟨715928, by rfl⟩ : syracuseStep 954571 = 1431857) B1431857
theorem B856279 : Blo 562809 856279 := bstep (se 1 (by rfl) ⟨642209, by rfl⟩ : syracuseStep 856279 = 1284419) B1284419
theorem B954713 : Blo 562809 954713 := bstep (se 2 (by rfl) ⟨358017, by rfl⟩ : syracuseStep 954713 = 716035) B716035
theorem B1610077 : Blo 562809 1610077 := bstep (se 3 (by rfl) ⟨301889, by rfl⟩ : syracuseStep 1610077 = 603779) B603779
theorem B954841 : Blo 562809 954841 := bstep (se 2 (by rfl) ⟨358065, by rfl⟩ : syracuseStep 954841 = 716131) B716131
theorem B1905227 : Blo 562809 1905227 := bstep (se 1 (by rfl) ⟨1428920, by rfl⟩ : syracuseStep 1905227 = 2857841) B2857841
theorem B1806941 : Blo 562809 1806941 := bstep (se 3 (by rfl) ⟨338801, by rfl⟩ : syracuseStep 1806941 = 677603) B677603
theorem B1905497 : Blo 562809 1905497 := bstep (se 2 (by rfl) ⟨714561, by rfl⟩ : syracuseStep 1905497 = 1429123) B1429123
theorem B1086347 : Blo 562809 1086347 := bstep (se 1 (by rfl) ⟨814760, by rfl⟩ : syracuseStep 1086347 = 1629521) B1629521
theorem B2855897 : Blo 562809 2855897 := bstep (se 2 (by rfl) ⟨1070961, by rfl⟩ : syracuseStep 2855897 = 2141923) B2141923
theorem B955415 : Blo 562809 955415 := bstep (se 1 (by rfl) ⟨716561, by rfl⟩ : syracuseStep 955415 = 1433123) B1433123
theorem B955543 : Blo 562809 955543 := bstep (se 1 (by rfl) ⟨716657, by rfl⟩ : syracuseStep 955543 = 1433315) B1433315
theorem B2692445 : Blo 562809 2692445 := bstep (se 3 (by rfl) ⟨504833, by rfl⟩ : syracuseStep 2692445 = 1009667) B1009667
theorem B1906199 : Blo 562809 1906199 := bstep (se 1 (by rfl) ⟨1429649, by rfl⟩ : syracuseStep 1906199 = 2859299) B2859299
theorem B3216941 : Blo 562809 3216941 := bstep (se 3 (by rfl) ⟨603176, by rfl⟩ : syracuseStep 3216941 = 1206353) B1206353
theorem B5969483 : Blo 562809 5969483 := bstep (se 1 (by rfl) ⟨4477112, by rfl⟩ : syracuseStep 5969483 = 8954225) B8954225
theorem B1611353 : Blo 562809 1611353 := bstep (se 2 (by rfl) ⟨604257, by rfl⟩ : syracuseStep 1611353 = 1208515) B1208515
theorem B562827 : Blo 562809 562827 := bstep (se 1 (by rfl) ⟨422120, by rfl⟩ : syracuseStep 562827 = 844241) B844241
theorem B562839 : Blo 562809 562839 := bstep (se 1 (by rfl) ⟨422129, by rfl⟩ : syracuseStep 562839 = 844259) B844259
theorem B562859 : Blo 562809 562859 := bstep (se 1 (by rfl) ⟨422144, by rfl⟩ : syracuseStep 562859 = 844289) B844289
theorem B562871 : Blo 562809 562871 := bstep (se 1 (by rfl) ⟨422153, by rfl⟩ : syracuseStep 562871 = 844307) B844307
theorem B562891 : Blo 562809 562891 := bstep (se 1 (by rfl) ⟨422168, by rfl⟩ : syracuseStep 562891 = 844337) B844337
theorem B562903 : Blo 562809 562903 := bstep (se 1 (by rfl) ⟨422177, by rfl⟩ : syracuseStep 562903 = 844355) B844355
theorem B562923 : Blo 562809 562923 := bstep (se 1 (by rfl) ⟨422192, by rfl⟩ : syracuseStep 562923 = 844385) B844385
theorem B562935 : Blo 562809 562935 := bstep (se 1 (by rfl) ⟨422201, by rfl⟩ : syracuseStep 562935 = 844403) B844403
theorem B562955 : Blo 562809 562955 := bstep (se 1 (by rfl) ⟨422216, by rfl⟩ : syracuseStep 562955 = 844433) B844433
theorem B956171 : Blo 562809 956171 := bstep (se 1 (by rfl) ⟨717128, by rfl⟩ : syracuseStep 956171 = 1434257) B1434257
theorem B562967 : Blo 562809 562967 := bstep (se 1 (by rfl) ⟨422225, by rfl⟩ : syracuseStep 562967 = 844451) B844451
theorem B562987 : Blo 562809 562987 := bstep (se 1 (by rfl) ⟨422240, by rfl⟩ : syracuseStep 562987 = 844481) B844481
theorem B562999 : Blo 562809 562999 := bstep (se 1 (by rfl) ⟨422249, by rfl⟩ : syracuseStep 562999 = 844499) B844499
theorem B563019 : Blo 562809 563019 := bstep (se 1 (by rfl) ⟨422264, by rfl⟩ : syracuseStep 563019 = 844529) B844529
theorem B563031 : Blo 562809 563031 := bstep (se 1 (by rfl) ⟨422273, by rfl⟩ : syracuseStep 563031 = 844547) B844547
theorem B563051 : Blo 562809 563051 := bstep (se 1 (by rfl) ⟨422288, by rfl⟩ : syracuseStep 563051 = 844577) B844577
theorem B563063 : Blo 562809 563063 := bstep (se 1 (by rfl) ⟨422297, by rfl⟩ : syracuseStep 563063 = 844595) B844595
theorem B563083 : Blo 562809 563083 := bstep (se 1 (by rfl) ⟨422312, by rfl⟩ : syracuseStep 563083 = 844625) B844625
theorem B956299 : Blo 562809 956299 := bstep (se 1 (by rfl) ⟨717224, by rfl⟩ : syracuseStep 956299 = 1434449) B1434449
theorem B563095 : Blo 562809 563095 := bstep (se 1 (by rfl) ⟨422321, by rfl⟩ : syracuseStep 563095 = 844643) B844643
theorem B563115 : Blo 562809 563115 := bstep (se 1 (by rfl) ⟨422336, by rfl⟩ : syracuseStep 563115 = 844673) B844673
theorem B563127 : Blo 562809 563127 := bstep (se 1 (by rfl) ⟨422345, by rfl⟩ : syracuseStep 563127 = 844691) B844691
theorem B563147 : Blo 562809 563147 := bstep (se 1 (by rfl) ⟨422360, by rfl⟩ : syracuseStep 563147 = 844721) B844721
theorem B563159 : Blo 562809 563159 := bstep (se 1 (by rfl) ⟨422369, by rfl⟩ : syracuseStep 563159 = 844739) B844739
theorem B563179 : Blo 562809 563179 := bstep (se 1 (by rfl) ⟨422384, by rfl⟩ : syracuseStep 563179 = 844769) B844769
theorem B563191 : Blo 562809 563191 := bstep (se 1 (by rfl) ⟨422393, by rfl⟩ : syracuseStep 563191 = 844787) B844787
theorem B563211 : Blo 562809 563211 := bstep (se 1 (by rfl) ⟨422408, by rfl⟩ : syracuseStep 563211 = 844817) B844817
theorem B563223 : Blo 562809 563223 := bstep (se 1 (by rfl) ⟨422417, by rfl⟩ : syracuseStep 563223 = 844835) B844835
theorem B956441 : Blo 562809 956441 := bstep (se 2 (by rfl) ⟨358665, by rfl⟩ : syracuseStep 956441 = 717331) B717331
theorem B563243 : Blo 562809 563243 := bstep (se 1 (by rfl) ⟨422432, by rfl⟩ : syracuseStep 563243 = 844865) B844865
theorem B1906739 : Blo 562809 1906739 := bstep (se 1 (by rfl) ⟨1430054, by rfl⟩ : syracuseStep 1906739 = 2860109) B2860109
theorem B563255 : Blo 562809 563255 := bstep (se 1 (by rfl) ⟨422441, by rfl⟩ : syracuseStep 563255 = 844883) B844883
theorem B4626497 : Blo 562809 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B563275 : Blo 562809 563275 := bstep (se 1 (by rfl) ⟨422456, by rfl⟩ : syracuseStep 563275 = 844913) B844913
theorem B563287 : Blo 562809 563287 := bstep (se 1 (by rfl) ⟨422465, by rfl⟩ : syracuseStep 563287 = 844931) B844931
theorem B563307 : Blo 562809 563307 := bstep (se 1 (by rfl) ⟨422480, by rfl⟩ : syracuseStep 563307 = 844961) B844961
theorem B563319 : Blo 562809 563319 := bstep (se 1 (by rfl) ⟨422489, by rfl⟩ : syracuseStep 563319 = 844979) B844979
theorem B563339 : Blo 562809 563339 := bstep (se 1 (by rfl) ⟨422504, by rfl⟩ : syracuseStep 563339 = 845009) B845009
theorem B563351 : Blo 562809 563351 := bstep (se 1 (by rfl) ⟨422513, by rfl⟩ : syracuseStep 563351 = 845027) B845027
theorem B563371 : Blo 562809 563371 := bstep (se 1 (by rfl) ⟨422528, by rfl⟩ : syracuseStep 563371 = 845057) B845057
theorem B563383 : Blo 562809 563383 := bstep (se 1 (by rfl) ⟨422537, by rfl⟩ : syracuseStep 563383 = 845075) B845075
theorem B563403 : Blo 562809 563403 := bstep (se 1 (by rfl) ⟨422552, by rfl⟩ : syracuseStep 563403 = 845105) B845105
theorem B563415 : Blo 562809 563415 := bstep (se 1 (by rfl) ⟨422561, by rfl⟩ : syracuseStep 563415 = 845123) B845123
theorem B563435 : Blo 562809 563435 := bstep (se 1 (by rfl) ⟨422576, by rfl⟩ : syracuseStep 563435 = 845153) B845153
theorem B563447 : Blo 562809 563447 := bstep (se 1 (by rfl) ⟨422585, by rfl⟩ : syracuseStep 563447 = 845171) B845171
theorem B563467 : Blo 562809 563467 := bstep (se 1 (by rfl) ⟨422600, by rfl⟩ : syracuseStep 563467 = 845201) B845201
theorem B563479 : Blo 562809 563479 := bstep (se 1 (by rfl) ⟨422609, by rfl⟩ : syracuseStep 563479 = 845219) B845219
theorem B563499 : Blo 562809 563499 := bstep (se 1 (by rfl) ⟨422624, by rfl⟩ : syracuseStep 563499 = 845249) B845249
theorem B563511 : Blo 562809 563511 := bstep (se 1 (by rfl) ⟨422633, by rfl⟩ : syracuseStep 563511 = 845267) B845267
theorem B1907009 : Blo 562809 1907009 := bstep (se 2 (by rfl) ⟨715128, by rfl⟩ : syracuseStep 1907009 = 1430257) B1430257
theorem B9181505 : Blo 562809 9181505 := bstep (se 2 (by rfl) ⟨3443064, by rfl⟩ : syracuseStep 9181505 = 6886129) B6886129
theorem B563531 : Blo 562809 563531 := bstep (se 1 (by rfl) ⟨422648, by rfl⟩ : syracuseStep 563531 = 845297) B845297
theorem B563543 : Blo 562809 563543 := bstep (se 1 (by rfl) ⟨422657, by rfl⟩ : syracuseStep 563543 = 845315) B845315
theorem B563563 : Blo 562809 563563 := bstep (se 1 (by rfl) ⟨422672, by rfl⟩ : syracuseStep 563563 = 845345) B845345
theorem B563575 : Blo 562809 563575 := bstep (se 1 (by rfl) ⟨422681, by rfl⟩ : syracuseStep 563575 = 845363) B845363
theorem B563595 : Blo 562809 563595 := bstep (se 1 (by rfl) ⟨422696, by rfl⟩ : syracuseStep 563595 = 845393) B845393
theorem B563607 : Blo 562809 563607 := bstep (se 1 (by rfl) ⟨422705, by rfl⟩ : syracuseStep 563607 = 845411) B845411
theorem B563627 : Blo 562809 563627 := bstep (se 1 (by rfl) ⟨422720, by rfl⟩ : syracuseStep 563627 = 845441) B845441
theorem B563639 : Blo 562809 563639 := bstep (se 1 (by rfl) ⟨422729, by rfl⟩ : syracuseStep 563639 = 845459) B845459
theorem B563659 : Blo 562809 563659 := bstep (se 1 (by rfl) ⟨422744, by rfl⟩ : syracuseStep 563659 = 845489) B845489
theorem B563671 : Blo 562809 563671 := bstep (se 1 (by rfl) ⟨422753, by rfl⟩ : syracuseStep 563671 = 845507) B845507
theorem B563691 : Blo 562809 563691 := bstep (se 1 (by rfl) ⟨422768, by rfl⟩ : syracuseStep 563691 = 845537) B845537
theorem B563703 : Blo 562809 563703 := bstep (se 1 (by rfl) ⟨422777, by rfl⟩ : syracuseStep 563703 = 845555) B845555
theorem B563723 : Blo 562809 563723 := bstep (se 1 (by rfl) ⟨422792, by rfl⟩ : syracuseStep 563723 = 845585) B845585
theorem B563735 : Blo 562809 563735 := bstep (se 1 (by rfl) ⟨422801, by rfl⟩ : syracuseStep 563735 = 845603) B845603
theorem B563755 : Blo 562809 563755 := bstep (se 1 (by rfl) ⟨422816, by rfl⟩ : syracuseStep 563755 = 845633) B845633
theorem B2857517 : Blo 562809 2857517 := bstep (se 3 (by rfl) ⟨535784, by rfl⟩ : syracuseStep 2857517 = 1071569) B1071569
theorem B563767 : Blo 562809 563767 := bstep (se 1 (by rfl) ⟨422825, by rfl⟩ : syracuseStep 563767 = 845651) B845651
theorem B563787 : Blo 562809 563787 := bstep (se 1 (by rfl) ⟨422840, by rfl⟩ : syracuseStep 563787 = 845681) B845681
theorem B563799 : Blo 562809 563799 := bstep (se 1 (by rfl) ⟨422849, by rfl⟩ : syracuseStep 563799 = 845699) B845699
theorem B563819 : Blo 562809 563819 := bstep (se 1 (by rfl) ⟨422864, by rfl⟩ : syracuseStep 563819 = 845729) B845729
theorem B563831 : Blo 562809 563831 := bstep (se 1 (by rfl) ⟨422873, by rfl⟩ : syracuseStep 563831 = 845747) B845747
theorem B563851 : Blo 562809 563851 := bstep (se 1 (by rfl) ⟨422888, by rfl⟩ : syracuseStep 563851 = 845777) B845777
theorem B563863 : Blo 562809 563863 := bstep (se 1 (by rfl) ⟨422897, by rfl⟩ : syracuseStep 563863 = 845795) B845795
theorem B563883 : Blo 562809 563883 := bstep (se 1 (by rfl) ⟨422912, by rfl⟩ : syracuseStep 563883 = 845825) B845825
theorem B563895 : Blo 562809 563895 := bstep (se 1 (by rfl) ⟨422921, by rfl⟩ : syracuseStep 563895 = 845843) B845843
theorem B563915 : Blo 562809 563915 := bstep (se 1 (by rfl) ⟨422936, by rfl⟩ : syracuseStep 563915 = 845873) B845873
theorem B5446349 : Blo 562809 5446349 := bstep (se 3 (by rfl) ⟨1021190, by rfl⟩ : syracuseStep 5446349 = 2042381) B2042381
theorem B563927 : Blo 562809 563927 := bstep (se 1 (by rfl) ⟨422945, by rfl⟩ : syracuseStep 563927 = 845891) B845891
theorem B563947 : Blo 562809 563947 := bstep (se 1 (by rfl) ⟨422960, by rfl⟩ : syracuseStep 563947 = 845921) B845921
theorem B563959 : Blo 562809 563959 := bstep (se 1 (by rfl) ⟨422969, by rfl⟩ : syracuseStep 563959 = 845939) B845939
theorem B1284875 : Blo 562809 1284875 := bstep (se 1 (by rfl) ⟨963656, by rfl⟩ : syracuseStep 1284875 = 1927313) B1927313
theorem B563979 : Blo 562809 563979 := bstep (se 1 (by rfl) ⟨422984, by rfl⟩ : syracuseStep 563979 = 845969) B845969
theorem B563991 : Blo 562809 563991 := bstep (se 1 (by rfl) ⟨422993, by rfl⟩ : syracuseStep 563991 = 845987) B845987
theorem B564011 : Blo 562809 564011 := bstep (se 1 (by rfl) ⟨423008, by rfl⟩ : syracuseStep 564011 = 846017) B846017
theorem B564023 : Blo 562809 564023 := bstep (se 1 (by rfl) ⟨423017, by rfl⟩ : syracuseStep 564023 = 846035) B846035
theorem B564043 : Blo 562809 564043 := bstep (se 1 (by rfl) ⟨423032, by rfl⟩ : syracuseStep 564043 = 846065) B846065
theorem B564055 : Blo 562809 564055 := bstep (se 1 (by rfl) ⟨423041, by rfl⟩ : syracuseStep 564055 = 846083) B846083
theorem B1907549 : Blo 562809 1907549 := bstep (se 3 (by rfl) ⟨357665, by rfl⟩ : syracuseStep 1907549 = 715331) B715331
theorem B564075 : Blo 562809 564075 := bstep (se 1 (by rfl) ⟨423056, by rfl⟩ : syracuseStep 564075 = 846113) B846113
theorem B564087 : Blo 562809 564087 := bstep (se 1 (by rfl) ⟨423065, by rfl⟩ : syracuseStep 564087 = 846131) B846131
theorem B564107 : Blo 562809 564107 := bstep (se 1 (by rfl) ⟨423080, by rfl⟩ : syracuseStep 564107 = 846161) B846161
theorem B564119 : Blo 562809 564119 := bstep (se 1 (by rfl) ⟨423089, by rfl⟩ : syracuseStep 564119 = 846179) B846179
theorem B2038679 : Blo 562809 2038679 := bstep (se 1 (by rfl) ⟨1529009, by rfl⟩ : syracuseStep 2038679 = 3058019) B3058019
theorem B564139 : Blo 562809 564139 := bstep (se 1 (by rfl) ⟨423104, by rfl⟩ : syracuseStep 564139 = 846209) B846209
theorem B564151 : Blo 562809 564151 := bstep (se 1 (by rfl) ⟨423113, by rfl⟩ : syracuseStep 564151 = 846227) B846227
theorem B564171 : Blo 562809 564171 := bstep (se 1 (by rfl) ⟨423128, by rfl⟩ : syracuseStep 564171 = 846257) B846257
theorem B564183 : Blo 562809 564183 := bstep (se 1 (by rfl) ⟨423137, by rfl⟩ : syracuseStep 564183 = 846275) B846275
theorem B2137049 : Blo 562809 2137049 := bstep (se 2 (by rfl) ⟨801393, by rfl⟩ : syracuseStep 2137049 = 1602787) B1602787
theorem B564203 : Blo 562809 564203 := bstep (se 1 (by rfl) ⟨423152, by rfl⟩ : syracuseStep 564203 = 846305) B846305
theorem B564215 : Blo 562809 564215 := bstep (se 1 (by rfl) ⟨423161, by rfl⟩ : syracuseStep 564215 = 846323) B846323
theorem B564235 : Blo 562809 564235 := bstep (se 1 (by rfl) ⟨423176, by rfl⟩ : syracuseStep 564235 = 846353) B846353
theorem B564247 : Blo 562809 564247 := bstep (se 1 (by rfl) ⟨423185, by rfl⟩ : syracuseStep 564247 = 846371) B846371
theorem B564267 : Blo 562809 564267 := bstep (se 1 (by rfl) ⟨423200, by rfl⟩ : syracuseStep 564267 = 846401) B846401
theorem B564279 : Blo 562809 564279 := bstep (se 1 (by rfl) ⟨423209, by rfl⟩ : syracuseStep 564279 = 846419) B846419
theorem B564299 : Blo 562809 564299 := bstep (se 1 (by rfl) ⟨423224, by rfl⟩ : syracuseStep 564299 = 846449) B846449
theorem B564311 : Blo 562809 564311 := bstep (se 1 (by rfl) ⟨423233, by rfl⟩ : syracuseStep 564311 = 846467) B846467
theorem B564331 : Blo 562809 564331 := bstep (se 1 (by rfl) ⟨423248, by rfl⟩ : syracuseStep 564331 = 846497) B846497
theorem B564343 : Blo 562809 564343 := bstep (se 1 (by rfl) ⟨423257, by rfl⟩ : syracuseStep 564343 = 846515) B846515
theorem B564363 : Blo 562809 564363 := bstep (se 1 (by rfl) ⟨423272, by rfl⟩ : syracuseStep 564363 = 846545) B846545
theorem B564375 : Blo 562809 564375 := bstep (se 1 (by rfl) ⟨423281, by rfl⟩ : syracuseStep 564375 = 846563) B846563
theorem B564395 : Blo 562809 564395 := bstep (se 1 (by rfl) ⟨423296, by rfl⟩ : syracuseStep 564395 = 846593) B846593
theorem B564407 : Blo 562809 564407 := bstep (se 1 (by rfl) ⟨423305, by rfl⟩ : syracuseStep 564407 = 846611) B846611
theorem B1612993 : Blo 562809 1612993 := bstep (se 2 (by rfl) ⟨604872, by rfl⟩ : syracuseStep 1612993 = 1209745) B1209745
theorem B564427 : Blo 562809 564427 := bstep (se 1 (by rfl) ⟨423320, by rfl⟩ : syracuseStep 564427 = 846641) B846641
theorem B564439 : Blo 562809 564439 := bstep (se 1 (by rfl) ⟨423329, by rfl⟩ : syracuseStep 564439 = 846659) B846659
theorem B564459 : Blo 562809 564459 := bstep (se 1 (by rfl) ⟨423344, by rfl⟩ : syracuseStep 564459 = 846689) B846689
theorem B564471 : Blo 562809 564471 := bstep (se 1 (by rfl) ⟨423353, by rfl⟩ : syracuseStep 564471 = 846707) B846707
theorem B564491 : Blo 562809 564491 := bstep (se 1 (by rfl) ⟨423368, by rfl⟩ : syracuseStep 564491 = 846737) B846737
theorem B2137367 : Blo 562809 2137367 := bstep (se 1 (by rfl) ⟨1603025, by rfl⟩ : syracuseStep 2137367 = 3206051) B3206051
theorem B564503 : Blo 562809 564503 := bstep (se 1 (by rfl) ⟨423377, by rfl⟩ : syracuseStep 564503 = 846755) B846755
theorem B564523 : Blo 562809 564523 := bstep (se 1 (by rfl) ⟨423392, by rfl⟩ : syracuseStep 564523 = 846785) B846785
theorem B564535 : Blo 562809 564535 := bstep (se 1 (by rfl) ⟨423401, by rfl⟩ : syracuseStep 564535 = 846803) B846803
theorem B564555 : Blo 562809 564555 := bstep (se 1 (by rfl) ⟨423416, by rfl⟩ : syracuseStep 564555 = 846833) B846833
theorem B564567 : Blo 562809 564567 := bstep (se 1 (by rfl) ⟨423425, by rfl⟩ : syracuseStep 564567 = 846851) B846851
theorem B564587 : Blo 562809 564587 := bstep (se 1 (by rfl) ⟨423440, by rfl⟩ : syracuseStep 564587 = 846881) B846881
theorem B564599 : Blo 562809 564599 := bstep (se 1 (by rfl) ⟨423449, by rfl⟩ : syracuseStep 564599 = 846899) B846899
theorem B564619 : Blo 562809 564619 := bstep (se 1 (by rfl) ⟨423464, by rfl⟩ : syracuseStep 564619 = 846929) B846929
theorem B564631 : Blo 562809 564631 := bstep (se 1 (by rfl) ⟨423473, by rfl⟩ : syracuseStep 564631 = 846947) B846947
theorem B564651 : Blo 562809 564651 := bstep (se 1 (by rfl) ⟨423488, by rfl⟩ : syracuseStep 564651 = 846977) B846977
theorem B564663 : Blo 562809 564663 := bstep (se 1 (by rfl) ⟨423497, by rfl⟩ : syracuseStep 564663 = 846995) B846995
theorem B564683 : Blo 562809 564683 := bstep (se 1 (by rfl) ⟨423512, by rfl⟩ : syracuseStep 564683 = 847025) B847025
theorem B564695 : Blo 562809 564695 := bstep (se 1 (by rfl) ⟨423521, by rfl⟩ : syracuseStep 564695 = 847043) B847043
theorem B564715 : Blo 562809 564715 := bstep (se 1 (by rfl) ⟨423536, by rfl⟩ : syracuseStep 564715 = 847073) B847073
theorem B564727 : Blo 562809 564727 := bstep (se 1 (by rfl) ⟨423545, by rfl⟩ : syracuseStep 564727 = 847091) B847091
theorem B564747 : Blo 562809 564747 := bstep (se 1 (by rfl) ⟨423560, by rfl⟩ : syracuseStep 564747 = 847121) B847121
theorem B564759 : Blo 562809 564759 := bstep (se 1 (by rfl) ⟨423569, by rfl⟩ : syracuseStep 564759 = 847139) B847139
theorem B564779 : Blo 562809 564779 := bstep (se 1 (by rfl) ⟨423584, by rfl⟩ : syracuseStep 564779 = 847169) B847169
theorem B564791 : Blo 562809 564791 := bstep (se 1 (by rfl) ⟨423593, by rfl⟩ : syracuseStep 564791 = 847187) B847187
theorem B564811 : Blo 562809 564811 := bstep (se 1 (by rfl) ⟨423608, by rfl⟩ : syracuseStep 564811 = 847217) B847217
theorem B564823 : Blo 562809 564823 := bstep (se 1 (by rfl) ⟨423617, by rfl⟩ : syracuseStep 564823 = 847235) B847235
theorem B564843 : Blo 562809 564843 := bstep (se 1 (by rfl) ⟨423632, by rfl⟩ : syracuseStep 564843 = 847265) B847265
theorem B564855 : Blo 562809 564855 := bstep (se 1 (by rfl) ⟨423641, by rfl⟩ : syracuseStep 564855 = 847283) B847283
theorem B564875 : Blo 562809 564875 := bstep (se 1 (by rfl) ⟨423656, by rfl⟩ : syracuseStep 564875 = 847313) B847313
theorem B564887 : Blo 562809 564887 := bstep (se 1 (by rfl) ⟨423665, by rfl⟩ : syracuseStep 564887 = 847331) B847331
theorem B564907 : Blo 562809 564907 := bstep (se 1 (by rfl) ⟨423680, by rfl⟩ : syracuseStep 564907 = 847361) B847361
theorem B564919 : Blo 562809 564919 := bstep (se 1 (by rfl) ⟨423689, by rfl⟩ : syracuseStep 564919 = 847379) B847379
theorem B564939 : Blo 562809 564939 := bstep (se 1 (by rfl) ⟨423704, by rfl⟩ : syracuseStep 564939 = 847409) B847409
theorem B564951 : Blo 562809 564951 := bstep (se 1 (by rfl) ⟨423713, by rfl⟩ : syracuseStep 564951 = 847427) B847427
theorem B564971 : Blo 562809 564971 := bstep (se 1 (by rfl) ⟨423728, by rfl⟩ : syracuseStep 564971 = 847457) B847457
theorem B1220339 : Blo 562809 1220339 := bstep (se 1 (by rfl) ⟨915254, by rfl⟩ : syracuseStep 1220339 = 1830509) B1830509
theorem B564983 : Blo 562809 564983 := bstep (se 1 (by rfl) ⟨423737, by rfl⟩ : syracuseStep 564983 = 847475) B847475
theorem B565003 : Blo 562809 565003 := bstep (se 1 (by rfl) ⟨423752, by rfl⟩ : syracuseStep 565003 = 847505) B847505
theorem B565015 : Blo 562809 565015 := bstep (se 1 (by rfl) ⟨423761, by rfl⟩ : syracuseStep 565015 = 847523) B847523
theorem B859927 : Blo 562809 859927 := bstep (se 1 (by rfl) ⟨644945, by rfl⟩ : syracuseStep 859927 = 1289891) B1289891
theorem B565035 : Blo 562809 565035 := bstep (se 1 (by rfl) ⟨423776, by rfl⟩ : syracuseStep 565035 = 847553) B847553
theorem B1089331 : Blo 562809 1089331 := bstep (se 1 (by rfl) ⟨816998, by rfl⟩ : syracuseStep 1089331 = 1633997) B1633997
theorem B565047 : Blo 562809 565047 := bstep (se 1 (by rfl) ⟨423785, by rfl⟩ : syracuseStep 565047 = 847571) B847571
theorem B565067 : Blo 562809 565067 := bstep (se 1 (by rfl) ⟨423800, by rfl⟩ : syracuseStep 565067 = 847601) B847601
theorem B565079 : Blo 562809 565079 := bstep (se 1 (by rfl) ⟨423809, by rfl⟩ : syracuseStep 565079 = 847619) B847619
theorem B565099 : Blo 562809 565099 := bstep (se 1 (by rfl) ⟨423824, by rfl⟩ : syracuseStep 565099 = 847649) B847649
theorem B565111 : Blo 562809 565111 := bstep (se 1 (by rfl) ⟨423833, by rfl⟩ : syracuseStep 565111 = 847667) B847667
theorem B565131 : Blo 562809 565131 := bstep (se 1 (by rfl) ⟨423848, by rfl⟩ : syracuseStep 565131 = 847697) B847697
theorem B565143 : Blo 562809 565143 := bstep (se 1 (by rfl) ⟨423857, by rfl⟩ : syracuseStep 565143 = 847715) B847715
theorem B565163 : Blo 562809 565163 := bstep (se 1 (by rfl) ⟨423872, by rfl⟩ : syracuseStep 565163 = 847745) B847745
theorem B2138035 : Blo 562809 2138035 := bstep (se 1 (by rfl) ⟨1603526, by rfl⟩ : syracuseStep 2138035 = 3207053) B3207053
theorem B565175 : Blo 562809 565175 := bstep (se 1 (by rfl) ⟨423881, by rfl⟩ : syracuseStep 565175 = 847763) B847763
theorem B565195 : Blo 562809 565195 := bstep (se 1 (by rfl) ⟨423896, by rfl⟩ : syracuseStep 565195 = 847793) B847793
theorem B1908683 : Blo 562809 1908683 := bstep (se 1 (by rfl) ⟨1431512, by rfl⟩ : syracuseStep 1908683 = 2863025) B2863025
theorem B565207 : Blo 562809 565207 := bstep (se 1 (by rfl) ⟨423905, by rfl⟩ : syracuseStep 565207 = 847811) B847811
theorem B565227 : Blo 562809 565227 := bstep (se 1 (by rfl) ⟨423920, by rfl⟩ : syracuseStep 565227 = 847841) B847841
theorem B565239 : Blo 562809 565239 := bstep (se 1 (by rfl) ⟨423929, by rfl⟩ : syracuseStep 565239 = 847859) B847859
theorem B565259 : Blo 562809 565259 := bstep (se 1 (by rfl) ⟨423944, by rfl⟩ : syracuseStep 565259 = 847889) B847889
theorem B565271 : Blo 562809 565271 := bstep (se 1 (by rfl) ⟨423953, by rfl⟩ : syracuseStep 565271 = 847907) B847907
theorem B565291 : Blo 562809 565291 := bstep (se 1 (by rfl) ⟨423968, by rfl⟩ : syracuseStep 565291 = 847937) B847937
theorem B565303 : Blo 562809 565303 := bstep (se 1 (by rfl) ⟨423977, by rfl⟩ : syracuseStep 565303 = 847955) B847955
theorem B565323 : Blo 562809 565323 := bstep (se 1 (by rfl) ⟨423992, by rfl⟩ : syracuseStep 565323 = 847985) B847985
theorem B565335 : Blo 562809 565335 := bstep (se 1 (by rfl) ⟨424001, by rfl⟩ : syracuseStep 565335 = 848003) B848003
theorem B565355 : Blo 562809 565355 := bstep (se 1 (by rfl) ⟨424016, by rfl⟩ : syracuseStep 565355 = 848033) B848033
theorem B565367 : Blo 562809 565367 := bstep (se 1 (by rfl) ⟨424025, by rfl⟩ : syracuseStep 565367 = 848051) B848051
theorem B565387 : Blo 562809 565387 := bstep (se 1 (by rfl) ⟨424040, by rfl⟩ : syracuseStep 565387 = 848081) B848081
theorem B565399 : Blo 562809 565399 := bstep (se 1 (by rfl) ⟨424049, by rfl⟩ : syracuseStep 565399 = 848099) B848099
theorem B565419 : Blo 562809 565419 := bstep (se 1 (by rfl) ⟨424064, by rfl⟩ : syracuseStep 565419 = 848129) B848129
theorem B565431 : Blo 562809 565431 := bstep (se 1 (by rfl) ⟨424073, by rfl⟩ : syracuseStep 565431 = 848147) B848147
theorem B565451 : Blo 562809 565451 := bstep (se 1 (by rfl) ⟨424088, by rfl⟩ : syracuseStep 565451 = 848177) B848177
theorem B565463 : Blo 562809 565463 := bstep (se 1 (by rfl) ⟨424097, by rfl⟩ : syracuseStep 565463 = 848195) B848195
theorem B1908953 : Blo 562809 1908953 := bstep (se 2 (by rfl) ⟨715857, by rfl⟩ : syracuseStep 1908953 = 1431715) B1431715
theorem B565483 : Blo 562809 565483 := bstep (se 1 (by rfl) ⟨424112, by rfl⟩ : syracuseStep 565483 = 848225) B848225
theorem B565495 : Blo 562809 565495 := bstep (se 1 (by rfl) ⟨424121, by rfl⟩ : syracuseStep 565495 = 848243) B848243
theorem B565515 : Blo 562809 565515 := bstep (se 1 (by rfl) ⟨424136, by rfl⟩ : syracuseStep 565515 = 848273) B848273
theorem B565527 : Blo 562809 565527 := bstep (se 1 (by rfl) ⟨424145, by rfl⟩ : syracuseStep 565527 = 848291) B848291
theorem B565547 : Blo 562809 565547 := bstep (se 1 (by rfl) ⟨424160, by rfl⟩ : syracuseStep 565547 = 848321) B848321
theorem B565559 : Blo 562809 565559 := bstep (se 1 (by rfl) ⟨424169, by rfl⟩ : syracuseStep 565559 = 848339) B848339
theorem B565579 : Blo 562809 565579 := bstep (se 1 (by rfl) ⟨424184, by rfl⟩ : syracuseStep 565579 = 848369) B848369
theorem B565591 : Blo 562809 565591 := bstep (se 1 (by rfl) ⟨424193, by rfl⟩ : syracuseStep 565591 = 848387) B848387
theorem B565611 : Blo 562809 565611 := bstep (se 1 (by rfl) ⟨424208, by rfl⟩ : syracuseStep 565611 = 848417) B848417
theorem B565623 : Blo 562809 565623 := bstep (se 1 (by rfl) ⟨424217, by rfl⟩ : syracuseStep 565623 = 848435) B848435
theorem B565643 : Blo 562809 565643 := bstep (se 1 (by rfl) ⟨424232, by rfl⟩ : syracuseStep 565643 = 848465) B848465
theorem B565655 : Blo 562809 565655 := bstep (se 1 (by rfl) ⟨424241, by rfl⟩ : syracuseStep 565655 = 848483) B848483
theorem B565675 : Blo 562809 565675 := bstep (se 1 (by rfl) ⟨424256, by rfl⟩ : syracuseStep 565675 = 848513) B848513
theorem B565687 : Blo 562809 565687 := bstep (se 1 (by rfl) ⟨424265, by rfl⟩ : syracuseStep 565687 = 848531) B848531
theorem B565707 : Blo 562809 565707 := bstep (se 1 (by rfl) ⟨424280, by rfl⟩ : syracuseStep 565707 = 848561) B848561
theorem B565719 : Blo 562809 565719 := bstep (se 1 (by rfl) ⟨424289, by rfl⟩ : syracuseStep 565719 = 848579) B848579
theorem B565739 : Blo 562809 565739 := bstep (se 1 (by rfl) ⟨424304, by rfl⟩ : syracuseStep 565739 = 848609) B848609
theorem B565751 : Blo 562809 565751 := bstep (se 1 (by rfl) ⟨424313, by rfl⟩ : syracuseStep 565751 = 848627) B848627
theorem B565771 : Blo 562809 565771 := bstep (se 1 (by rfl) ⟨424328, by rfl⟩ : syracuseStep 565771 = 848657) B848657
theorem B565783 : Blo 562809 565783 := bstep (se 1 (by rfl) ⟨424337, by rfl⟩ : syracuseStep 565783 = 848675) B848675
theorem B565803 : Blo 562809 565803 := bstep (se 1 (by rfl) ⟨424352, by rfl⟩ : syracuseStep 565803 = 848705) B848705
theorem B565815 : Blo 562809 565815 := bstep (se 1 (by rfl) ⟨424361, by rfl⟩ : syracuseStep 565815 = 848723) B848723
theorem B565835 : Blo 562809 565835 := bstep (se 1 (by rfl) ⟨424376, by rfl⟩ : syracuseStep 565835 = 848753) B848753
theorem B565847 : Blo 562809 565847 := bstep (se 1 (by rfl) ⟨424385, by rfl⟩ : syracuseStep 565847 = 848771) B848771
theorem B565867 : Blo 562809 565867 := bstep (se 1 (by rfl) ⟨424400, by rfl⟩ : syracuseStep 565867 = 848801) B848801
theorem B565879 : Blo 562809 565879 := bstep (se 1 (by rfl) ⟨424409, by rfl⟩ : syracuseStep 565879 = 848819) B848819
theorem B565899 : Blo 562809 565899 := bstep (se 1 (by rfl) ⟨424424, by rfl⟩ : syracuseStep 565899 = 848849) B848849
theorem B565911 : Blo 562809 565911 := bstep (se 1 (by rfl) ⟨424433, by rfl⟩ : syracuseStep 565911 = 848867) B848867
theorem B565931 : Blo 562809 565931 := bstep (se 1 (by rfl) ⟨424448, by rfl⟩ : syracuseStep 565931 = 848897) B848897
theorem B565943 : Blo 562809 565943 := bstep (se 1 (by rfl) ⟨424457, by rfl⟩ : syracuseStep 565943 = 848915) B848915
theorem B565963 : Blo 562809 565963 := bstep (se 1 (by rfl) ⟨424472, by rfl⟩ : syracuseStep 565963 = 848945) B848945
theorem B565975 : Blo 562809 565975 := bstep (se 1 (by rfl) ⟨424481, by rfl⟩ : syracuseStep 565975 = 848963) B848963
theorem B2794201 : Blo 562809 2794201 := bstep (se 2 (by rfl) ⟨1047825, by rfl⟩ : syracuseStep 2794201 = 2095651) B2095651
theorem B565995 : Blo 562809 565995 := bstep (se 1 (by rfl) ⟨424496, by rfl⟩ : syracuseStep 565995 = 848993) B848993
theorem B566007 : Blo 562809 566007 := bstep (se 1 (by rfl) ⟨424505, by rfl⟩ : syracuseStep 566007 = 849011) B849011
theorem B566027 : Blo 562809 566027 := bstep (se 1 (by rfl) ⟨424520, by rfl⟩ : syracuseStep 566027 = 849041) B849041
theorem B4301585 : Blo 562809 4301585 := bstep (se 2 (by rfl) ⟨1613094, by rfl⟩ : syracuseStep 4301585 = 3226189) B3226189
theorem B566039 : Blo 562809 566039 := bstep (se 1 (by rfl) ⟨424529, by rfl⟩ : syracuseStep 566039 = 849059) B849059
theorem B566059 : Blo 562809 566059 := bstep (se 1 (by rfl) ⟨424544, by rfl⟩ : syracuseStep 566059 = 849089) B849089
theorem B5808941 : Blo 562809 5808941 := bstep (se 3 (by rfl) ⟨1089176, by rfl⟩ : syracuseStep 5808941 = 2178353) B2178353
theorem B566071 : Blo 562809 566071 := bstep (se 1 (by rfl) ⟨424553, by rfl⟩ : syracuseStep 566071 = 849107) B849107
theorem B566091 : Blo 562809 566091 := bstep (se 1 (by rfl) ⟨424568, by rfl⟩ : syracuseStep 566091 = 849137) B849137
theorem B566103 : Blo 562809 566103 := bstep (se 1 (by rfl) ⟨424577, by rfl⟩ : syracuseStep 566103 = 849155) B849155
theorem B566123 : Blo 562809 566123 := bstep (se 1 (by rfl) ⟨424592, by rfl⟩ : syracuseStep 566123 = 849185) B849185
theorem B566135 : Blo 562809 566135 := bstep (se 1 (by rfl) ⟨424601, by rfl⟩ : syracuseStep 566135 = 849203) B849203
theorem B566155 : Blo 562809 566155 := bstep (se 1 (by rfl) ⟨424616, by rfl⟩ : syracuseStep 566155 = 849233) B849233
theorem B1909655 : Blo 562809 1909655 := bstep (se 1 (by rfl) ⟨1432241, by rfl⟩ : syracuseStep 1909655 = 2864483) B2864483
theorem B566167 : Blo 562809 566167 := bstep (se 1 (by rfl) ⟨424625, by rfl⟩ : syracuseStep 566167 = 849251) B849251
theorem B566187 : Blo 562809 566187 := bstep (se 1 (by rfl) ⟨424640, by rfl⟩ : syracuseStep 566187 = 849281) B849281
theorem B566199 : Blo 562809 566199 := bstep (se 1 (by rfl) ⟨424649, by rfl⟩ : syracuseStep 566199 = 849299) B849299
theorem B566219 : Blo 562809 566219 := bstep (se 1 (by rfl) ⟨424664, by rfl⟩ : syracuseStep 566219 = 849329) B849329
theorem B566231 : Blo 562809 566231 := bstep (se 1 (by rfl) ⟨424673, by rfl⟩ : syracuseStep 566231 = 849347) B849347
theorem B566251 : Blo 562809 566251 := bstep (se 1 (by rfl) ⟨424688, by rfl⟩ : syracuseStep 566251 = 849377) B849377
theorem B566263 : Blo 562809 566263 := bstep (se 1 (by rfl) ⟨424697, by rfl⟩ : syracuseStep 566263 = 849395) B849395
theorem B566283 : Blo 562809 566283 := bstep (se 1 (by rfl) ⟨424712, by rfl⟩ : syracuseStep 566283 = 849425) B849425
theorem B1287191 : Blo 562809 1287191 := bstep (se 1 (by rfl) ⟨965393, by rfl⟩ : syracuseStep 1287191 = 1930787) B1930787
theorem B566295 : Blo 562809 566295 := bstep (se 1 (by rfl) ⟨424721, by rfl⟩ : syracuseStep 566295 = 849443) B849443
theorem B566315 : Blo 562809 566315 := bstep (se 1 (by rfl) ⟨424736, by rfl⟩ : syracuseStep 566315 = 849473) B849473
theorem B566327 : Blo 562809 566327 := bstep (se 1 (by rfl) ⟨424745, by rfl⟩ : syracuseStep 566327 = 849491) B849491
theorem B566347 : Blo 562809 566347 := bstep (se 1 (by rfl) ⟨424760, by rfl⟩ : syracuseStep 566347 = 849521) B849521
theorem B566359 : Blo 562809 566359 := bstep (se 1 (by rfl) ⟨424769, by rfl⟩ : syracuseStep 566359 = 849539) B849539
theorem B566379 : Blo 562809 566379 := bstep (se 1 (by rfl) ⟨424784, by rfl⟩ : syracuseStep 566379 = 849569) B849569
theorem B566391 : Blo 562809 566391 := bstep (se 1 (by rfl) ⟨424793, by rfl⟩ : syracuseStep 566391 = 849587) B849587
theorem B566411 : Blo 562809 566411 := bstep (se 1 (by rfl) ⟨424808, by rfl⟩ : syracuseStep 566411 = 849617) B849617
theorem B2139281 : Blo 562809 2139281 := bstep (se 2 (by rfl) ⟨802230, by rfl⟩ : syracuseStep 2139281 = 1604461) B1604461
theorem B3220631 : Blo 562809 3220631 := bstep (se 1 (by rfl) ⟨2415473, by rfl⟩ : syracuseStep 3220631 = 4830947) B4830947
theorem B566423 : Blo 562809 566423 := bstep (se 1 (by rfl) ⟨424817, by rfl⟩ : syracuseStep 566423 = 849635) B849635
theorem B566443 : Blo 562809 566443 := bstep (se 1 (by rfl) ⟨424832, by rfl⟩ : syracuseStep 566443 = 849665) B849665
theorem B566455 : Blo 562809 566455 := bstep (se 1 (by rfl) ⟨424841, by rfl⟩ : syracuseStep 566455 = 849683) B849683
theorem B566475 : Blo 562809 566475 := bstep (se 1 (by rfl) ⟨424856, by rfl⟩ : syracuseStep 566475 = 849713) B849713
theorem B566487 : Blo 562809 566487 := bstep (se 1 (by rfl) ⟨424865, by rfl⟩ : syracuseStep 566487 = 849731) B849731
theorem B566507 : Blo 562809 566507 := bstep (se 1 (by rfl) ⟨424880, by rfl⟩ : syracuseStep 566507 = 849761) B849761
theorem B566519 : Blo 562809 566519 := bstep (se 1 (by rfl) ⟨424889, by rfl⟩ : syracuseStep 566519 = 849779) B849779
theorem B41329925 : Blo 562809 41329925 := bstep (se 4 (by rfl) ⟨3874680, by rfl⟩ : syracuseStep 41329925 = 7749361) B7749361
theorem B566539 : Blo 562809 566539 := bstep (se 1 (by rfl) ⟨424904, by rfl⟩ : syracuseStep 566539 = 849809) B849809
theorem B1713431 : Blo 562809 1713431 := bstep (se 1 (by rfl) ⟨1285073, by rfl⟩ : syracuseStep 1713431 = 2570147) B2570147
theorem B566551 : Blo 562809 566551 := bstep (se 1 (by rfl) ⟨424913, by rfl⟩ : syracuseStep 566551 = 849827) B849827
theorem B566571 : Blo 562809 566571 := bstep (se 1 (by rfl) ⟨424928, by rfl⟩ : syracuseStep 566571 = 849857) B849857
theorem B566583 : Blo 562809 566583 := bstep (se 1 (by rfl) ⟨424937, by rfl⟩ : syracuseStep 566583 = 849875) B849875
theorem B566603 : Blo 562809 566603 := bstep (se 1 (by rfl) ⟨424952, by rfl⟩ : syracuseStep 566603 = 849905) B849905
theorem B566615 : Blo 562809 566615 := bstep (se 1 (by rfl) ⟨424961, by rfl⟩ : syracuseStep 566615 = 849923) B849923
theorem B566635 : Blo 562809 566635 := bstep (se 1 (by rfl) ⟨424976, by rfl⟩ : syracuseStep 566635 = 849953) B849953
theorem B566647 : Blo 562809 566647 := bstep (se 1 (by rfl) ⟨424985, by rfl⟩ : syracuseStep 566647 = 849971) B849971
theorem B566667 : Blo 562809 566667 := bstep (se 1 (by rfl) ⟨425000, by rfl⟩ : syracuseStep 566667 = 850001) B850001
theorem B566679 : Blo 562809 566679 := bstep (se 1 (by rfl) ⟨425009, by rfl⟩ : syracuseStep 566679 = 850019) B850019
theorem B566699 : Blo 562809 566699 := bstep (se 1 (by rfl) ⟨425024, by rfl⟩ : syracuseStep 566699 = 850049) B850049
theorem B1910195 : Blo 562809 1910195 := bstep (se 1 (by rfl) ⟨1432646, by rfl⟩ : syracuseStep 1910195 = 2865293) B2865293
theorem B566711 : Blo 562809 566711 := bstep (se 1 (by rfl) ⟨425033, by rfl⟩ : syracuseStep 566711 = 850067) B850067
theorem B566731 : Blo 562809 566731 := bstep (se 1 (by rfl) ⟨425048, by rfl⟩ : syracuseStep 566731 = 850097) B850097
theorem B4826573 : Blo 562809 4826573 := bstep (se 3 (by rfl) ⟨904982, by rfl⟩ : syracuseStep 4826573 = 1809965) B1809965
theorem B566743 : Blo 562809 566743 := bstep (se 1 (by rfl) ⟨425057, by rfl⟩ : syracuseStep 566743 = 850115) B850115
theorem B566763 : Blo 562809 566763 := bstep (se 1 (by rfl) ⟨425072, by rfl⟩ : syracuseStep 566763 = 850145) B850145
theorem B566775 : Blo 562809 566775 := bstep (se 1 (by rfl) ⟨425081, by rfl⟩ : syracuseStep 566775 = 850163) B850163
theorem B566795 : Blo 562809 566795 := bstep (se 1 (by rfl) ⟨425096, by rfl⟩ : syracuseStep 566795 = 850193) B850193
theorem B566807 : Blo 562809 566807 := bstep (se 1 (by rfl) ⟨425105, by rfl⟩ : syracuseStep 566807 = 850211) B850211
theorem B1910465 : Blo 562809 1910465 := bstep (se 2 (by rfl) ⟨716424, by rfl⟩ : syracuseStep 1910465 = 1432849) B1432849
theorem B2139979 : Blo 562809 2139979 := bstep (se 1 (by rfl) ⟨1604984, by rfl⟩ : syracuseStep 2139979 = 3209969) B3209969
theorem B2041793 : Blo 562809 2041793 := bstep (se 2 (by rfl) ⟨765672, by rfl⟩ : syracuseStep 2041793 = 1531345) B1531345
theorem B2140253 : Blo 562809 2140253 := bstep (se 3 (by rfl) ⟨401297, by rfl⟩ : syracuseStep 2140253 = 802595) B802595
theorem B1812631 : Blo 562809 1812631 := bstep (se 1 (by rfl) ⟨1359473, by rfl⟩ : syracuseStep 1812631 = 2718947) B2718947
theorem B1911005 : Blo 562809 1911005 := bstep (se 3 (by rfl) ⟨358313, by rfl⟩ : syracuseStep 1911005 = 716627) B716627
theorem B633163 : Blo 562809 633163 := bstep (se 1 (by rfl) ⟨474872, by rfl⟩ : syracuseStep 633163 = 949745) B949745
theorem B2861405 : Blo 562809 2861405 := bstep (se 3 (by rfl) ⟨536513, by rfl⟩ : syracuseStep 2861405 = 1073027) B1073027
theorem B633271 : Blo 562809 633271 := bstep (se 1 (by rfl) ⟨474953, by rfl⟩ : syracuseStep 633271 = 949907) B949907
theorem B82356749 : Blo 562809 82356749 := bstep (se 3 (by rfl) ⟨15441890, by rfl⟩ : syracuseStep 82356749 = 30883781) B30883781
theorem B633451 : Blo 562809 633451 := bstep (se 1 (by rfl) ⟨475088, by rfl⟩ : syracuseStep 633451 = 950177) B950177
theorem B21146309 : Blo 562809 21146309 := bstep (se 4 (by rfl) ⟨1982466, by rfl⟩ : syracuseStep 21146309 = 3964933) B3964933
theorem B633559 : Blo 562809 633559 := bstep (se 1 (by rfl) ⟨475169, by rfl⟩ : syracuseStep 633559 = 950339) B950339
theorem B2140951 : Blo 562809 2140951 := bstep (se 1 (by rfl) ⟨1605713, by rfl⟩ : syracuseStep 2140951 = 3211427) B3211427
theorem B633739 : Blo 562809 633739 := bstep (se 1 (by rfl) ⟨475304, by rfl⟩ : syracuseStep 633739 = 950609) B950609
theorem B2927539 : Blo 562809 2927539 := bstep (se 1 (by rfl) ⟨2195654, by rfl⟩ : syracuseStep 2927539 = 4391309) B4391309
theorem B633847 : Blo 562809 633847 := bstep (se 1 (by rfl) ⟨475385, by rfl⟩ : syracuseStep 633847 = 950771) B950771
theorem B634027 : Blo 562809 634027 := bstep (se 1 (by rfl) ⟨475520, by rfl⟩ : syracuseStep 634027 = 951041) B951041
theorem B21769397 : Blo 562809 21769397 := bstep (se 5 (by rfl) ⟨1020440, by rfl⟩ : syracuseStep 21769397 = 2040881) B2040881
theorem B634135 : Blo 562809 634135 := bstep (se 1 (by rfl) ⟨475601, by rfl⟩ : syracuseStep 634135 = 951203) B951203
theorem B1912139 : Blo 562809 1912139 := bstep (se 1 (by rfl) ⟨1434104, by rfl⟩ : syracuseStep 1912139 = 2868209) B2868209
theorem B4566365 : Blo 562809 4566365 := bstep (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) B1712387
theorem B634315 : Blo 562809 634315 := bstep (se 1 (by rfl) ⟨475736, by rfl⟩ : syracuseStep 634315 = 951473) B951473
theorem B2141741 : Blo 562809 2141741 := bstep (se 3 (by rfl) ⟨401576, by rfl⟩ : syracuseStep 2141741 = 803153) B803153
theorem B634423 : Blo 562809 634423 := bstep (se 1 (by rfl) ⟨475817, by rfl⟩ : syracuseStep 634423 = 951635) B951635
theorem B1912409 : Blo 562809 1912409 := bstep (se 2 (by rfl) ⟨717153, by rfl⟩ : syracuseStep 1912409 = 1434307) B1434307
theorem B1224407 : Blo 562809 1224407 := bstep (se 1 (by rfl) ⟨918305, by rfl⟩ : syracuseStep 1224407 = 1836611) B1836611
theorem B765655 : Blo 562809 765655 := bstep (se 1 (by rfl) ⟨574241, by rfl⟩ : syracuseStep 765655 = 1148483) B1148483
theorem B601835 : Blo 562809 601835 := bstep (se 1 (by rfl) ⟨451376, by rfl⟩ : syracuseStep 601835 = 902753) B902753
theorem B634603 : Blo 562809 634603 := bstep (se 1 (by rfl) ⟨475952, by rfl⟩ : syracuseStep 634603 = 951905) B951905
theorem B634711 : Blo 562809 634711 := bstep (se 1 (by rfl) ⟨476033, by rfl⟩ : syracuseStep 634711 = 952067) B952067
theorem B634891 : Blo 562809 634891 := bstep (se 1 (by rfl) ⟨476168, by rfl⟩ : syracuseStep 634891 = 952337) B952337
theorem B2404403 : Blo 562809 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B634999 : Blo 562809 634999 := bstep (se 1 (by rfl) ⟨476249, by rfl⟩ : syracuseStep 634999 = 952499) B952499
theorem B635179 : Blo 562809 635179 := bstep (se 1 (by rfl) ⟨476384, by rfl⟩ : syracuseStep 635179 = 952769) B952769
theorem B635287 : Blo 562809 635287 := bstep (se 1 (by rfl) ⟨476465, by rfl⟩ : syracuseStep 635287 = 952931) B952931
theorem B2863511 : Blo 562809 2863511 := bstep (se 1 (by rfl) ⟨2147633, by rfl⟩ : syracuseStep 2863511 = 4295267) B4295267
theorem B635467 : Blo 562809 635467 := bstep (se 1 (by rfl) ⟨476600, by rfl⟩ : syracuseStep 635467 = 953201) B953201
theorem B635575 : Blo 562809 635575 := bstep (se 1 (by rfl) ⟨476681, by rfl⟩ : syracuseStep 635575 = 953363) B953363
theorem B5780173 : Blo 562809 5780173 := bstep (se 3 (by rfl) ⟨1083782, by rfl⟩ : syracuseStep 5780173 = 2167565) B2167565
theorem B9679661 : Blo 562809 9679661 := bstep (se 3 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 9679661 = 3629873) B3629873
theorem B1815347 : Blo 562809 1815347 := bstep (se 1 (by rfl) ⟨1361510, by rfl⟩ : syracuseStep 1815347 = 2723021) B2723021
theorem B635755 : Blo 562809 635755 := bstep (se 1 (by rfl) ⟨476816, by rfl⟩ : syracuseStep 635755 = 953633) B953633
theorem B2143169 : Blo 562809 2143169 := bstep (se 2 (by rfl) ⟨803688, by rfl⟩ : syracuseStep 2143169 = 1607377) B1607377
theorem B635863 : Blo 562809 635863 := bstep (se 1 (by rfl) ⟨476897, by rfl⟩ : syracuseStep 635863 = 953795) B953795
theorem B636043 : Blo 562809 636043 := bstep (se 1 (by rfl) ⟨477032, by rfl⟩ : syracuseStep 636043 = 954065) B954065
theorem B1651915 : Blo 562809 1651915 := bstep (se 1 (by rfl) ⟨1238936, by rfl⟩ : syracuseStep 1651915 = 2477873) B2477873
theorem B636151 : Blo 562809 636151 := bstep (se 1 (by rfl) ⟨477113, by rfl⟩ : syracuseStep 636151 = 954227) B954227
theorem B636331 : Blo 562809 636331 := bstep (se 1 (by rfl) ⟨477248, by rfl⟩ : syracuseStep 636331 = 954497) B954497
theorem B603595 : Blo 562809 603595 := bstep (se 1 (by rfl) ⟨452696, by rfl⟩ : syracuseStep 603595 = 905393) B905393
theorem B1357273 : Blo 562809 1357273 := bstep (se 2 (by rfl) ⟨508977, by rfl⟩ : syracuseStep 1357273 = 1017955) B1017955
theorem B636439 : Blo 562809 636439 := bstep (se 1 (by rfl) ⟨477329, by rfl⟩ : syracuseStep 636439 = 954659) B954659
theorem B1717811 : Blo 562809 1717811 := bstep (se 1 (by rfl) ⟨1288358, by rfl⟩ : syracuseStep 1717811 = 2576717) B2576717
theorem B1357505 : Blo 562809 1357505 := bstep (se 2 (by rfl) ⟨509064, by rfl⟩ : syracuseStep 1357505 = 1018129) B1018129
theorem B2569931 : Blo 562809 2569931 := bstep (se 1 (by rfl) ⟨1927448, by rfl⟩ : syracuseStep 2569931 = 3854897) B3854897
theorem B636619 : Blo 562809 636619 := bstep (se 1 (by rfl) ⟨477464, by rfl⟩ : syracuseStep 636619 = 954929) B954929
theorem B636727 : Blo 562809 636727 := bstep (se 1 (by rfl) ⟨477545, by rfl⟩ : syracuseStep 636727 = 955091) B955091
theorem B636907 : Blo 562809 636907 := bstep (se 1 (by rfl) ⟨477680, by rfl⟩ : syracuseStep 636907 = 955361) B955361
theorem B571403 : Blo 562809 571403 := bstep (se 1 (by rfl) ⟨428552, by rfl⟩ : syracuseStep 571403 = 857105) B857105
theorem B637015 : Blo 562809 637015 := bstep (se 1 (by rfl) ⟨477761, by rfl⟩ : syracuseStep 637015 = 955523) B955523
theorem B4831325 : Blo 562809 4831325 := bstep (se 3 (by rfl) ⟨905873, by rfl⟩ : syracuseStep 4831325 = 1811747) B1811747
theorem B6437069 : Blo 562809 6437069 := bstep (se 3 (by rfl) ⟨1206950, by rfl⟩ : syracuseStep 6437069 = 2413901) B2413901
theorem B637195 : Blo 562809 637195 := bstep (se 1 (by rfl) ⟨477896, by rfl⟩ : syracuseStep 637195 = 955793) B955793
theorem B637303 : Blo 562809 637303 := bstep (se 1 (by rfl) ⟨477977, by rfl⟩ : syracuseStep 637303 = 955955) B955955
theorem B2144657 : Blo 562809 2144657 := bstep (se 2 (by rfl) ⟨804246, by rfl⟩ : syracuseStep 2144657 = 1608493) B1608493
theorem B3226007 : Blo 562809 3226007 := bstep (se 1 (by rfl) ⟨2419505, by rfl⟩ : syracuseStep 3226007 = 4839011) B4839011
theorem B637483 : Blo 562809 637483 := bstep (se 1 (by rfl) ⟨478112, by rfl⟩ : syracuseStep 637483 = 956225) B956225
theorem B8141381 : Blo 562809 8141381 := bstep (se 4 (by rfl) ⟨763254, by rfl⟩ : syracuseStep 8141381 = 1526509) B1526509
theorem B4340299 : Blo 562809 4340299 := bstep (se 1 (by rfl) ⟨3255224, by rfl⟩ : syracuseStep 4340299 = 6510449) B6510449
theorem B637591 : Blo 562809 637591 := bstep (se 1 (by rfl) ⟨478193, by rfl⟩ : syracuseStep 637591 = 956387) B956387
theorem B1391411 : Blo 562809 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B2145113 : Blo 562809 2145113 := bstep (se 2 (by rfl) ⟨804417, by rfl⟩ : syracuseStep 2145113 = 1608835) B1608835
theorem B605227 : Blo 562809 605227 := bstep (se 1 (by rfl) ⟨453920, by rfl⟩ : syracuseStep 605227 = 907841) B907841
theorem B2145325 : Blo 562809 2145325 := bstep (se 3 (by rfl) ⟨402248, by rfl⟩ : syracuseStep 2145325 = 804497) B804497
theorem B1359127 : Blo 562809 1359127 := bstep (se 1 (by rfl) ⟨1019345, by rfl⟩ : syracuseStep 1359127 = 2038691) B2038691
theorem B1424729 : Blo 562809 1424729 := bstep (se 2 (by rfl) ⟨534273, by rfl⟩ : syracuseStep 1424729 = 1068547) B1068547
theorem B2145629 : Blo 562809 2145629 := bstep (se 3 (by rfl) ⟨402305, by rfl⟩ : syracuseStep 2145629 = 804611) B804611
theorem B3489581 : Blo 562809 3489581 := bstep (se 3 (by rfl) ⟨654296, by rfl⟩ : syracuseStep 3489581 = 1308593) B1308593
theorem B2867075 : Blo 562809 2867075 := bstep (se 1 (by rfl) ⟨2150306, by rfl⟩ : syracuseStep 2867075 = 4300613) B4300613
theorem B2473907 : Blo 562809 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B573463 : Blo 562809 573463 := bstep (se 1 (by rfl) ⟨430097, by rfl⟩ : syracuseStep 573463 = 860195) B860195
theorem B4079747 : Blo 562809 4079747 := bstep (se 1 (by rfl) ⟨3059810, by rfl⟩ : syracuseStep 4079747 = 6119621) B6119621
theorem B1425559 : Blo 562809 1425559 := bstep (se 1 (by rfl) ⟨1069169, by rfl⟩ : syracuseStep 1425559 = 2138339) B2138339
theorem B2408707 : Blo 562809 2408707 := bstep (se 1 (by rfl) ⟨1806530, by rfl⟩ : syracuseStep 2408707 = 3613061) B3613061
theorem B3227921 : Blo 562809 3227921 := bstep (se 2 (by rfl) ⟨1210470, by rfl⟩ : syracuseStep 3227921 = 2420941) B2420941
theorem B4079917 : Blo 562809 4079917 := bstep (se 3 (by rfl) ⟨764984, by rfl⟩ : syracuseStep 4079917 = 1529969) B1529969
theorem B803353 : Blo 562809 803353 := bstep (se 2 (by rfl) ⟨301257, by rfl⟩ : syracuseStep 803353 = 602515) B602515
theorem B1425995 : Blo 562809 1425995 := bstep (se 1 (by rfl) ⟨1069496, by rfl⟩ : syracuseStep 1425995 = 2138993) B2138993
theorem B1426369 : Blo 562809 1426369 := bstep (se 2 (by rfl) ⟨534888, by rfl⟩ : syracuseStep 1426369 = 1069777) B1069777
theorem B1524953 : Blo 562809 1524953 := bstep (se 2 (by rfl) ⟨571857, by rfl⟩ : syracuseStep 1524953 = 1143715) B1143715
theorem B968075 : Blo 562809 968075 := bstep (se 1 (by rfl) ⟨726056, by rfl⟩ : syracuseStep 968075 = 1452113) B1452113
theorem B1426967 : Blo 562809 1426967 := bstep (se 1 (by rfl) ⟨1070225, by rfl⟩ : syracuseStep 1426967 = 2140451) B2140451
theorem B2148227 : Blo 562809 2148227 := bstep (se 1 (by rfl) ⟨1611170, by rfl⟩ : syracuseStep 2148227 = 3222341) B3222341
theorem B2148241 : Blo 562809 2148241 := bstep (se 2 (by rfl) ⟨805590, by rfl⟩ : syracuseStep 2148241 = 1611181) B1611181
theorem B804811 : Blo 562809 804811 := bstep (se 1 (by rfl) ⟨603608, by rfl⟩ : syracuseStep 804811 = 1207217) B1207217
theorem B2410519 : Blo 562809 2410519 := bstep (se 1 (by rfl) ⟨1807889, by rfl⟩ : syracuseStep 2410519 = 3615779) B3615779
theorem B2148545 : Blo 562809 2148545 := bstep (se 2 (by rfl) ⟨805704, by rfl⟩ : syracuseStep 2148545 = 1611409) B1611409
theorem B1427777 : Blo 562809 1427777 := bstep (se 2 (by rfl) ⟨535416, by rfl⟩ : syracuseStep 1427777 = 1070833) B1070833
theorem B4639193 : Blo 562809 4639193 := bstep (se 2 (by rfl) ⟨1739697, by rfl⟩ : syracuseStep 4639193 = 3479395) B3479395
theorem B2411153 : Blo 562809 2411153 := bstep (se 2 (by rfl) ⟨904182, by rfl⟩ : syracuseStep 2411153 = 1808365) B1808365
theorem B1428313 : Blo 562809 1428313 := bstep (se 2 (by rfl) ⟨535617, by rfl⟩ : syracuseStep 1428313 = 1071235) B1071235
theorem B2149213 : Blo 562809 2149213 := bstep (se 3 (by rfl) ⟨402977, by rfl⟩ : syracuseStep 2149213 = 805955) B805955
theorem B7228277 : Blo 562809 7228277 := bstep (se 5 (by rfl) ⟨338825, by rfl⟩ : syracuseStep 7228277 = 677651) B677651
theorem B4574339 : Blo 562809 4574339 := bstep (se 1 (by rfl) ⟨3430754, by rfl⟩ : syracuseStep 4574339 = 6861509) B6861509
theorem B806041 : Blo 562809 806041 := bstep (se 2 (by rfl) ⟨302265, by rfl⟩ : syracuseStep 806041 = 604531) B604531
theorem B2411851 : Blo 562809 2411851 := bstep (se 1 (by rfl) ⟨1808888, by rfl⟩ : syracuseStep 2411851 = 3617777) B3617777
theorem B2412125 : Blo 562809 2412125 := bstep (se 3 (by rfl) ⟨452273, by rfl⟩ : syracuseStep 2412125 = 904547) B904547
theorem B3624749 : Blo 562809 3624749 := bstep (se 3 (by rfl) ⟨679640, by rfl⟩ : syracuseStep 3624749 = 1359281) B1359281
theorem B1068851 : Blo 562809 1068851 := bstep (se 1 (by rfl) ⟨801638, by rfl⟩ : syracuseStep 1068851 = 1603277) B1603277
theorem B1068889 : Blo 562809 1068889 := bstep (se 2 (by rfl) ⟨400833, by rfl⟩ : syracuseStep 1068889 = 801667) B801667
theorem B905111 : Blo 562809 905111 := bstep (se 1 (by rfl) ⟨678833, by rfl⟩ : syracuseStep 905111 = 1357667) B1357667
theorem B1429427 : Blo 562809 1429427 := bstep (se 1 (by rfl) ⟨1072070, by rfl⟩ : syracuseStep 1429427 = 2144141) B2144141
theorem B2412467 : Blo 562809 2412467 := bstep (se 1 (by rfl) ⟨1809350, by rfl⟩ : syracuseStep 2412467 = 3618701) B3618701
theorem B806935 : Blo 562809 806935 := bstep (se 1 (by rfl) ⟨605201, by rfl⟩ : syracuseStep 806935 = 1210403) B1210403
theorem B1953857 : Blo 562809 1953857 := bstep (se 2 (by rfl) ⟨732696, by rfl⟩ : syracuseStep 1953857 = 1465393) B1465393
theorem B2150489 : Blo 562809 2150489 := bstep (se 2 (by rfl) ⟨806433, by rfl⟩ : syracuseStep 2150489 = 1612867) B1612867
theorem B1429721 : Blo 562809 1429721 := bstep (se 2 (by rfl) ⟨536145, by rfl⟩ : syracuseStep 1429721 = 1072291) B1072291
theorem B1069337 : Blo 562809 1069337 := bstep (se 2 (by rfl) ⟨401001, by rfl⟩ : syracuseStep 1069337 = 802003) B802003
theorem B905623 : Blo 562809 905623 := bstep (se 1 (by rfl) ⟨679217, by rfl⟩ : syracuseStep 905623 = 1358435) B1358435
theorem B5788421 : Blo 562809 5788421 := bstep (se 4 (by rfl) ⟨542664, by rfl⟩ : syracuseStep 5788421 = 1085329) B1085329
theorem B1266443 : Blo 562809 1266443 := bstep (se 1 (by rfl) ⟨949832, by rfl⟩ : syracuseStep 1266443 = 1899665) B1899665
theorem B905995 : Blo 562809 905995 := bstep (se 1 (by rfl) ⟨679496, by rfl⟩ : syracuseStep 905995 = 1358993) B1358993
theorem B1266497 : Blo 562809 1266497 := bstep (se 2 (by rfl) ⟨474936, by rfl⟩ : syracuseStep 1266497 = 949873) B949873
theorem B1070081 : Blo 562809 1070081 := bstep (se 2 (by rfl) ⟨401280, by rfl⟩ : syracuseStep 1070081 = 802561) B802561
theorem B1266713 : Blo 562809 1266713 := bstep (se 2 (by rfl) ⟨475017, by rfl⟩ : syracuseStep 1266713 = 950035) B950035
theorem B1266803 : Blo 562809 1266803 := bstep (se 1 (by rfl) ⟨950102, by rfl⟩ : syracuseStep 1266803 = 1900205) B1900205
theorem B1266839 : Blo 562809 1266839 := bstep (se 1 (by rfl) ⟨950129, by rfl⟩ : syracuseStep 1266839 = 1900259) B1900259
theorem B1070347 : Blo 562809 1070347 := bstep (se 1 (by rfl) ⟨802760, by rfl⟩ : syracuseStep 1070347 = 1605521) B1605521
theorem B1267019 : Blo 562809 1267019 := bstep (se 1 (by rfl) ⟨950264, by rfl⟩ : syracuseStep 1267019 = 1900529) B1900529
theorem B1267073 : Blo 562809 1267073 := bstep (se 2 (by rfl) ⟨475152, by rfl⟩ : syracuseStep 1267073 = 950305) B950305
theorem B1267289 : Blo 562809 1267289 := bstep (se 2 (by rfl) ⟨475233, by rfl⟩ : syracuseStep 1267289 = 950467) B950467
theorem B906905 : Blo 562809 906905 := bstep (se 2 (by rfl) ⟨340089, by rfl⟩ : syracuseStep 906905 = 680179) B680179
theorem B1267379 : Blo 562809 1267379 := bstep (se 1 (by rfl) ⟨950534, by rfl⟩ : syracuseStep 1267379 = 1901069) B1901069
theorem B1070795 : Blo 562809 1070795 := bstep (se 1 (by rfl) ⟨803096, by rfl⟩ : syracuseStep 1070795 = 1606193) B1606193
theorem B7722701 : Blo 562809 7722701 := bstep (se 3 (by rfl) ⟨1448006, by rfl⟩ : syracuseStep 7722701 = 2896013) B2896013
theorem B4085453 : Blo 562809 4085453 := bstep (se 3 (by rfl) ⟨766022, by rfl⟩ : syracuseStep 4085453 = 1532045) B1532045
theorem B1267415 : Blo 562809 1267415 := bstep (se 1 (by rfl) ⟨950561, by rfl⟩ : syracuseStep 1267415 = 1901123) B1901123
theorem B1529623 : Blo 562809 1529623 := bstep (se 1 (by rfl) ⟨1147217, by rfl⟩ : syracuseStep 1529623 = 2294435) B2294435
theorem B907033 : Blo 562809 907033 := bstep (se 2 (by rfl) ⟨340137, by rfl⟩ : syracuseStep 907033 = 680275) B680275
theorem B1431371 : Blo 562809 1431371 := bstep (se 1 (by rfl) ⟨1073528, by rfl⟩ : syracuseStep 1431371 = 2147057) B2147057
theorem B1070977 : Blo 562809 1070977 := bstep (se 2 (by rfl) ⟨401616, by rfl⟩ : syracuseStep 1070977 = 803233) B803233
theorem B1267595 : Blo 562809 1267595 := bstep (se 1 (by rfl) ⟨950696, by rfl⟩ : syracuseStep 1267595 = 1901393) B1901393
theorem B1267649 : Blo 562809 1267649 := bstep (se 2 (by rfl) ⟨475368, by rfl⟩ : syracuseStep 1267649 = 950737) B950737
theorem B677911 : Blo 562809 677911 := bstep (se 1 (by rfl) ⟨508433, by rfl⟩ : syracuseStep 677911 = 1016867) B1016867
theorem B2906243 : Blo 562809 2906243 := bstep (se 1 (by rfl) ⟨2179682, by rfl⟩ : syracuseStep 2906243 = 4359365) B4359365
theorem B1267865 : Blo 562809 1267865 := bstep (se 2 (by rfl) ⟨475449, by rfl⟩ : syracuseStep 1267865 = 950899) B950899
theorem B2709683 : Blo 562809 2709683 := bstep (se 1 (by rfl) ⟨2032262, by rfl⟩ : syracuseStep 2709683 = 4064525) B4064525
theorem B1071319 : Blo 562809 1071319 := bstep (se 1 (by rfl) ⟨803489, by rfl⟩ : syracuseStep 1071319 = 1606979) B1606979
theorem B1267955 : Blo 562809 1267955 := bstep (se 1 (by rfl) ⟨950966, by rfl⟩ : syracuseStep 1267955 = 1901933) B1901933
theorem B1267991 : Blo 562809 1267991 := bstep (se 1 (by rfl) ⟨950993, by rfl⟩ : syracuseStep 1267991 = 1901987) B1901987
theorem B2414893 : Blo 562809 2414893 := bstep (se 3 (by rfl) ⟨452792, by rfl⟩ : syracuseStep 2414893 = 905585) B905585
theorem B678295 : Blo 562809 678295 := bstep (se 1 (by rfl) ⟨508721, by rfl⟩ : syracuseStep 678295 = 1017443) B1017443
theorem B1071539 : Blo 562809 1071539 := bstep (se 1 (by rfl) ⟨803654, by rfl⟩ : syracuseStep 1071539 = 1607309) B1607309
theorem B1268171 : Blo 562809 1268171 := bstep (se 1 (by rfl) ⟨951128, by rfl⟩ : syracuseStep 1268171 = 1902257) B1902257
theorem B1268225 : Blo 562809 1268225 := bstep (se 2 (by rfl) ⟨475584, by rfl⟩ : syracuseStep 1268225 = 951169) B951169
theorem B612887 : Blo 562809 612887 := bstep (se 1 (by rfl) ⟨459665, by rfl⟩ : syracuseStep 612887 = 919331) B919331
theorem B1628723 : Blo 562809 1628723 := bstep (se 1 (by rfl) ⟨1221542, by rfl⟩ : syracuseStep 1628723 = 2443085) B2443085
theorem B1071767 : Blo 562809 1071767 := bstep (se 1 (by rfl) ⟨803825, by rfl⟩ : syracuseStep 1071767 = 1607651) B1607651
theorem B1268441 : Blo 562809 1268441 := bstep (se 2 (by rfl) ⟨475665, by rfl⟩ : syracuseStep 1268441 = 951331) B951331
theorem B1432343 : Blo 562809 1432343 := bstep (se 1 (by rfl) ⟨1074257, by rfl⟩ : syracuseStep 1432343 = 2148515) B2148515
theorem B1268531 : Blo 562809 1268531 := bstep (se 1 (by rfl) ⟨951398, by rfl⟩ : syracuseStep 1268531 = 1902797) B1902797
theorem B1268567 : Blo 562809 1268567 := bstep (se 1 (by rfl) ⟨951425, by rfl⟩ : syracuseStep 1268567 = 1902851) B1902851
theorem B1072025 : Blo 562809 1072025 := bstep (se 2 (by rfl) ⟨402009, by rfl⟩ : syracuseStep 1072025 = 804019) B804019
theorem B1268747 : Blo 562809 1268747 := bstep (se 1 (by rfl) ⟨951560, by rfl⟩ : syracuseStep 1268747 = 1903121) B1903121
theorem B2284561 : Blo 562809 2284561 := bstep (se 2 (by rfl) ⟨856710, by rfl⟩ : syracuseStep 2284561 = 1713421) B1713421
theorem B2579473 : Blo 562809 2579473 := bstep (se 2 (by rfl) ⟨967302, by rfl⟩ : syracuseStep 2579473 = 1934605) B1934605
theorem B1268801 : Blo 562809 1268801 := bstep (se 2 (by rfl) ⟨475800, by rfl⟩ : syracuseStep 1268801 = 951601) B951601
theorem B1203329 : Blo 562809 1203329 := bstep (se 2 (by rfl) ⟨451248, by rfl⟩ : syracuseStep 1203329 = 902497) B902497
theorem B5856407 : Blo 562809 5856407 := bstep (se 1 (by rfl) ⟨4392305, by rfl⟩ : syracuseStep 5856407 = 8784611) B8784611
theorem B1629377 : Blo 562809 1629377 := bstep (se 2 (by rfl) ⟨611016, by rfl⟩ : syracuseStep 1629377 = 1222033) B1222033
theorem B4840721 : Blo 562809 4840721 := bstep (se 2 (by rfl) ⟨1815270, by rfl⟩ : syracuseStep 4840721 = 3630541) B3630541
theorem B1269017 : Blo 562809 1269017 := bstep (se 2 (by rfl) ⟨475881, by rfl⟩ : syracuseStep 1269017 = 951763) B951763
theorem B1072435 : Blo 562809 1072435 := bstep (se 1 (by rfl) ⟨804326, by rfl⟩ : syracuseStep 1072435 = 1608653) B1608653
theorem B1269107 : Blo 562809 1269107 := bstep (se 1 (by rfl) ⟨951830, by rfl⟩ : syracuseStep 1269107 = 1903661) B1903661
theorem B1269143 : Blo 562809 1269143 := bstep (se 1 (by rfl) ⟨951857, by rfl⟩ : syracuseStep 1269143 = 1903715) B1903715
theorem B3628439 : Blo 562809 3628439 := bstep (se 1 (by rfl) ⟨2721329, by rfl⟩ : syracuseStep 3628439 = 5442659) B5442659
theorem B1433011 : Blo 562809 1433011 := bstep (se 1 (by rfl) ⟨1074758, by rfl⟩ : syracuseStep 1433011 = 2149517) B2149517
theorem B1433153 : Blo 562809 1433153 := bstep (se 2 (by rfl) ⟨537432, by rfl⟩ : syracuseStep 1433153 = 1074865) B1074865
theorem B1269323 : Blo 562809 1269323 := bstep (se 1 (by rfl) ⟨951992, by rfl⟩ : syracuseStep 1269323 = 1903985) B1903985
theorem B1302131 : Blo 562809 1302131 := bstep (se 1 (by rfl) ⟨976598, by rfl⟩ : syracuseStep 1302131 = 1953197) B1953197
theorem B1269377 : Blo 562809 1269377 := bstep (se 2 (by rfl) ⟨476016, by rfl⟩ : syracuseStep 1269377 = 952033) B952033
theorem B712471 : Blo 562809 712471 := bstep (se 1 (by rfl) ⟨534353, by rfl⟩ : syracuseStep 712471 = 1068707) B1068707
theorem B1072921 : Blo 562809 1072921 := bstep (se 2 (by rfl) ⟨402345, by rfl⟩ : syracuseStep 1072921 = 804691) B804691
theorem B1269593 : Blo 562809 1269593 := bstep (se 2 (by rfl) ⟨476097, by rfl⟩ : syracuseStep 1269593 = 952195) B952195
theorem B21651299 : Blo 562809 21651299 := bstep (se 1 (by rfl) ⟨16238474, by rfl⟩ : syracuseStep 21651299 = 32476949) B32476949
theorem B3628901 : Blo 562809 3628901 := bstep (se 4 (by rfl) ⟨340209, by rfl⟩ : syracuseStep 3628901 = 680419) B680419
theorem B1269683 : Blo 562809 1269683 := bstep (se 1 (by rfl) ⟨952262, by rfl⟩ : syracuseStep 1269683 = 1904525) B1904525
theorem B1204183 : Blo 562809 1204183 := bstep (se 1 (by rfl) ⟨903137, by rfl⟩ : syracuseStep 1204183 = 1806275) B1806275
theorem B1269719 : Blo 562809 1269719 := bstep (se 1 (by rfl) ⟨952289, by rfl⟩ : syracuseStep 1269719 = 1904579) B1904579
theorem B4644881 : Blo 562809 4644881 := bstep (se 2 (by rfl) ⟨1741830, by rfl⟩ : syracuseStep 4644881 = 3483661) B3483661
theorem B1269899 : Blo 562809 1269899 := bstep (se 1 (by rfl) ⟨952424, by rfl⟩ : syracuseStep 1269899 = 1904849) B1904849
theorem B8151191 : Blo 562809 8151191 := bstep (se 1 (by rfl) ⟨6113393, by rfl⟩ : syracuseStep 8151191 = 12226787) B12226787
theorem B1269953 : Blo 562809 1269953 := bstep (se 2 (by rfl) ⟨476232, by rfl⟩ : syracuseStep 1269953 = 952465) B952465
theorem B13951277 : Blo 562809 13951277 := bstep (se 3 (by rfl) ⟨2615864, by rfl⟩ : syracuseStep 13951277 = 5231729) B5231729
theorem B2711873 : Blo 562809 2711873 := bstep (se 2 (by rfl) ⟨1016952, by rfl⟩ : syracuseStep 2711873 = 2033905) B2033905
theorem B1073483 : Blo 562809 1073483 := bstep (se 1 (by rfl) ⟨805112, by rfl⟩ : syracuseStep 1073483 = 1610225) B1610225
theorem B1270169 : Blo 562809 1270169 := bstep (se 2 (by rfl) ⟨476313, by rfl⟩ : syracuseStep 1270169 = 952627) B952627
theorem B844235 : Blo 562809 844235 := bstep (se 1 (by rfl) ⟨633176, by rfl⟩ : syracuseStep 844235 = 1266353) B1266353
theorem B844247 : Blo 562809 844247 := bstep (se 1 (by rfl) ⟨633185, by rfl⟩ : syracuseStep 844247 = 1266371) B1266371
theorem B1270259 : Blo 562809 1270259 := bstep (se 1 (by rfl) ⟨952694, by rfl⟩ : syracuseStep 1270259 = 1905389) B1905389
theorem B1073665 : Blo 562809 1073665 := bstep (se 2 (by rfl) ⟨402624, by rfl⟩ : syracuseStep 1073665 = 805249) B805249
theorem B1270295 : Blo 562809 1270295 := bstep (se 1 (by rfl) ⟨952721, by rfl⟩ : syracuseStep 1270295 = 1905443) B1905443
theorem B844313 : Blo 562809 844313 := bstep (se 2 (by rfl) ⟨316617, by rfl⟩ : syracuseStep 844313 = 633235) B633235
theorem B844427 : Blo 562809 844427 := bstep (se 1 (by rfl) ⟨633320, by rfl⟩ : syracuseStep 844427 = 1266641) B1266641
theorem B844439 : Blo 562809 844439 := bstep (se 1 (by rfl) ⟨633329, by rfl⟩ : syracuseStep 844439 = 1266659) B1266659
theorem B2417303 : Blo 562809 2417303 := bstep (se 1 (by rfl) ⟨1812977, by rfl⟩ : syracuseStep 2417303 = 3625955) B3625955
theorem B1860275 : Blo 562809 1860275 := bstep (se 1 (by rfl) ⟨1395206, by rfl⟩ : syracuseStep 1860275 = 2790413) B2790413
theorem B1270475 : Blo 562809 1270475 := bstep (se 1 (by rfl) ⟨952856, by rfl⟩ : syracuseStep 1270475 = 1905713) B1905713
theorem B844505 : Blo 562809 844505 := bstep (se 2 (by rfl) ⟨316689, by rfl⟩ : syracuseStep 844505 = 633379) B633379
theorem B1630937 : Blo 562809 1630937 := bstep (se 2 (by rfl) ⟨611601, by rfl⟩ : syracuseStep 1630937 = 1223203) B1223203
theorem B1270529 : Blo 562809 1270529 := bstep (se 2 (by rfl) ⟨476448, by rfl⟩ : syracuseStep 1270529 = 952897) B952897
theorem B1205003 : Blo 562809 1205003 := bstep (se 1 (by rfl) ⟨903752, by rfl⟩ : syracuseStep 1205003 = 1807505) B1807505
theorem B1434419 : Blo 562809 1434419 := bstep (se 1 (by rfl) ⟨1075814, by rfl⟩ : syracuseStep 1434419 = 2151629) B2151629
theorem B4875073 : Blo 562809 4875073 := bstep (se 2 (by rfl) ⟨1828152, by rfl⟩ : syracuseStep 4875073 = 3656305) B3656305
theorem B844619 : Blo 562809 844619 := bstep (se 1 (by rfl) ⟨633464, by rfl⟩ : syracuseStep 844619 = 1266929) B1266929
theorem B844631 : Blo 562809 844631 := bstep (se 1 (by rfl) ⟨633473, by rfl⟩ : syracuseStep 844631 = 1266947) B1266947
theorem B844697 : Blo 562809 844697 := bstep (se 2 (by rfl) ⟨316761, by rfl⟩ : syracuseStep 844697 = 633523) B633523
theorem B10281907 : Blo 562809 10281907 := bstep (se 1 (by rfl) ⟨7711430, by rfl⟩ : syracuseStep 10281907 = 15422861) B15422861
theorem B1270745 : Blo 562809 1270745 := bstep (se 2 (by rfl) ⟨476529, by rfl⟩ : syracuseStep 1270745 = 953059) B953059
theorem B844811 : Blo 562809 844811 := bstep (se 1 (by rfl) ⟨633608, by rfl⟩ : syracuseStep 844811 = 1267217) B1267217
theorem B844823 : Blo 562809 844823 := bstep (se 1 (by rfl) ⟨633617, by rfl⟩ : syracuseStep 844823 = 1267235) B1267235
theorem B1270835 : Blo 562809 1270835 := bstep (se 1 (by rfl) ⟨953126, by rfl⟩ : syracuseStep 1270835 = 1906253) B1906253
theorem B1270871 : Blo 562809 1270871 := bstep (se 1 (by rfl) ⟨953153, by rfl⟩ : syracuseStep 1270871 = 1906307) B1906307
theorem B844889 : Blo 562809 844889 := bstep (se 2 (by rfl) ⟨316833, by rfl⟩ : syracuseStep 844889 = 633667) B633667
theorem B1631411 : Blo 562809 1631411 := bstep (se 1 (by rfl) ⟨1223558, by rfl⟩ : syracuseStep 1631411 = 2447117) B2447117
theorem B845003 : Blo 562809 845003 := bstep (se 1 (by rfl) ⟨633752, by rfl⟩ : syracuseStep 845003 = 1267505) B1267505
theorem B1074379 : Blo 562809 1074379 := bstep (se 1 (by rfl) ⟨805784, by rfl⟩ : syracuseStep 1074379 = 1611569) B1611569
theorem B845015 : Blo 562809 845015 := bstep (se 1 (by rfl) ⟨633761, by rfl⟩ : syracuseStep 845015 = 1267523) B1267523
theorem B1271051 : Blo 562809 1271051 := bstep (se 1 (by rfl) ⟨953288, by rfl⟩ : syracuseStep 1271051 = 1906577) B1906577
theorem B1074455 : Blo 562809 1074455 := bstep (se 1 (by rfl) ⟨805841, by rfl⟩ : syracuseStep 1074455 = 1611683) B1611683
theorem B845081 : Blo 562809 845081 := bstep (se 2 (by rfl) ⟨316905, by rfl⟩ : syracuseStep 845081 = 633811) B633811
theorem B1271105 : Blo 562809 1271105 := bstep (se 2 (by rfl) ⟨476664, by rfl⟩ : syracuseStep 1271105 = 953329) B953329
theorem B845195 : Blo 562809 845195 := bstep (se 1 (by rfl) ⟨633896, by rfl⟩ : syracuseStep 845195 = 1267793) B1267793
theorem B845207 : Blo 562809 845207 := bstep (se 1 (by rfl) ⟨633905, by rfl⟩ : syracuseStep 845207 = 1267811) B1267811
theorem B714187 : Blo 562809 714187 := bstep (se 1 (by rfl) ⟨535640, by rfl⟩ : syracuseStep 714187 = 1071281) B1071281
theorem B845273 : Blo 562809 845273 := bstep (se 2 (by rfl) ⟨316977, by rfl⟩ : syracuseStep 845273 = 633955) B633955
theorem B1271321 : Blo 562809 1271321 := bstep (se 2 (by rfl) ⟨476745, by rfl⟩ : syracuseStep 1271321 = 953491) B953491
theorem B845387 : Blo 562809 845387 := bstep (se 1 (by rfl) ⟨634040, by rfl⟩ : syracuseStep 845387 = 1268081) B1268081
theorem B845399 : Blo 562809 845399 := bstep (se 1 (by rfl) ⟨634049, by rfl⟩ : syracuseStep 845399 = 1268099) B1268099
theorem B6448733 : Blo 562809 6448733 := bstep (se 3 (by rfl) ⟨1209137, by rfl⟩ : syracuseStep 6448733 = 2418275) B2418275
theorem B37774961 : Blo 562809 37774961 := bstep (se 2 (by rfl) ⟨14165610, by rfl⟩ : syracuseStep 37774961 = 28331221) B28331221
theorem B1271411 : Blo 562809 1271411 := bstep (se 1 (by rfl) ⟨953558, by rfl⟩ : syracuseStep 1271411 = 1907117) B1907117
theorem B1271447 : Blo 562809 1271447 := bstep (se 1 (by rfl) ⟨953585, by rfl⟩ : syracuseStep 1271447 = 1907171) B1907171
theorem B845465 : Blo 562809 845465 := bstep (se 2 (by rfl) ⟨317049, by rfl⟩ : syracuseStep 845465 = 634099) B634099
theorem B845579 : Blo 562809 845579 := bstep (se 1 (by rfl) ⟨634184, by rfl⟩ : syracuseStep 845579 = 1268369) B1268369
theorem B845591 : Blo 562809 845591 := bstep (se 1 (by rfl) ⟨634193, by rfl⟩ : syracuseStep 845591 = 1268387) B1268387
theorem B1271627 : Blo 562809 1271627 := bstep (se 1 (by rfl) ⟨953720, by rfl⟩ : syracuseStep 1271627 = 1907441) B1907441
theorem B845657 : Blo 562809 845657 := bstep (se 2 (by rfl) ⟨317121, by rfl⟩ : syracuseStep 845657 = 634243) B634243
theorem B1271681 : Blo 562809 1271681 := bstep (se 2 (by rfl) ⟨476880, by rfl⟩ : syracuseStep 1271681 = 953761) B953761
theorem B1075123 : Blo 562809 1075123 := bstep (se 1 (by rfl) ⟨806342, by rfl⟩ : syracuseStep 1075123 = 1612685) B1612685
theorem B845771 : Blo 562809 845771 := bstep (se 1 (by rfl) ⟨634328, by rfl⟩ : syracuseStep 845771 = 1268657) B1268657
theorem B845783 : Blo 562809 845783 := bstep (se 1 (by rfl) ⟨634337, by rfl⟩ : syracuseStep 845783 = 1268675) B1268675
theorem B845849 : Blo 562809 845849 := bstep (se 2 (by rfl) ⟨317193, by rfl⟩ : syracuseStep 845849 = 634387) B634387
theorem B1271897 : Blo 562809 1271897 := bstep (se 2 (by rfl) ⟨476961, by rfl⟩ : syracuseStep 1271897 = 953923) B953923
theorem B4810853 : Blo 562809 4810853 := bstep (se 4 (by rfl) ⟨451017, by rfl⟩ : syracuseStep 4810853 = 902035) B902035
theorem B845963 : Blo 562809 845963 := bstep (se 1 (by rfl) ⟨634472, by rfl⟩ : syracuseStep 845963 = 1268945) B1268945
theorem B845975 : Blo 562809 845975 := bstep (se 1 (by rfl) ⟨634481, by rfl⟩ : syracuseStep 845975 = 1268963) B1268963
theorem B1075351 : Blo 562809 1075351 := bstep (se 1 (by rfl) ⟨806513, by rfl⟩ : syracuseStep 1075351 = 1613027) B1613027
theorem B1271987 : Blo 562809 1271987 := bstep (se 1 (by rfl) ⟨953990, by rfl⟩ : syracuseStep 1271987 = 1907981) B1907981
theorem B1272023 : Blo 562809 1272023 := bstep (se 1 (by rfl) ⟨954017, by rfl⟩ : syracuseStep 1272023 = 1908035) B1908035
theorem B846041 : Blo 562809 846041 := bstep (se 2 (by rfl) ⟨317265, by rfl⟩ : syracuseStep 846041 = 634531) B634531
theorem B1075457 : Blo 562809 1075457 := bstep (se 2 (by rfl) ⟨403296, by rfl⟩ : syracuseStep 1075457 = 806593) B806593
theorem B12216581 : Blo 562809 12216581 := bstep (se 4 (by rfl) ⟨1145304, by rfl⟩ : syracuseStep 12216581 = 2290609) B2290609
theorem B846155 : Blo 562809 846155 := bstep (se 1 (by rfl) ⟨634616, by rfl⟩ : syracuseStep 846155 = 1269233) B1269233
theorem B2713931 : Blo 562809 2713931 := bstep (se 1 (by rfl) ⟨2035448, by rfl⟩ : syracuseStep 2713931 = 4070897) B4070897
theorem B846167 : Blo 562809 846167 := bstep (se 1 (by rfl) ⟨634625, by rfl⟩ : syracuseStep 846167 = 1269251) B1269251
theorem B2713949 : Blo 562809 2713949 := bstep (se 3 (by rfl) ⟨508865, by rfl⟩ : syracuseStep 2713949 = 1017731) B1017731
theorem B1141121 : Blo 562809 1141121 := bstep (se 2 (by rfl) ⟨427920, by rfl⟩ : syracuseStep 1141121 = 855841) B855841
theorem B1272203 : Blo 562809 1272203 := bstep (se 1 (by rfl) ⟨954152, by rfl⟩ : syracuseStep 1272203 = 1908305) B1908305
theorem B715159 : Blo 562809 715159 := bstep (se 1 (by rfl) ⟨536369, by rfl⟩ : syracuseStep 715159 = 1072739) B1072739
theorem B846233 : Blo 562809 846233 := bstep (se 2 (by rfl) ⟨317337, by rfl⟩ : syracuseStep 846233 = 634675) B634675
theorem B1075609 : Blo 562809 1075609 := bstep (se 2 (by rfl) ⟨403353, by rfl⟩ : syracuseStep 1075609 = 806707) B806707
theorem B1272257 : Blo 562809 1272257 := bstep (se 2 (by rfl) ⟨477096, by rfl⟩ : syracuseStep 1272257 = 954193) B954193
theorem B846347 : Blo 562809 846347 := bstep (se 1 (by rfl) ⟨634760, by rfl⟩ : syracuseStep 846347 = 1269521) B1269521
theorem B2419217 : Blo 562809 2419217 := bstep (se 2 (by rfl) ⟨907206, by rfl⟩ : syracuseStep 2419217 = 1814413) B1814413
theorem B846359 : Blo 562809 846359 := bstep (se 1 (by rfl) ⟨634769, by rfl⟩ : syracuseStep 846359 = 1269539) B1269539
theorem B846425 : Blo 562809 846425 := bstep (se 2 (by rfl) ⟨317409, by rfl⟩ : syracuseStep 846425 = 634819) B634819
theorem B1272473 : Blo 562809 1272473 := bstep (se 2 (by rfl) ⟨477177, by rfl⟩ : syracuseStep 1272473 = 954355) B954355
theorem B846539 : Blo 562809 846539 := bstep (se 1 (by rfl) ⟨634904, by rfl⟩ : syracuseStep 846539 = 1269809) B1269809
theorem B846551 : Blo 562809 846551 := bstep (se 1 (by rfl) ⟨634913, by rfl⟩ : syracuseStep 846551 = 1269827) B1269827
theorem B1272563 : Blo 562809 1272563 := bstep (se 1 (by rfl) ⟨954422, by rfl⟩ : syracuseStep 1272563 = 1908845) B1908845
theorem B1272599 : Blo 562809 1272599 := bstep (se 1 (by rfl) ⟨954449, by rfl⟩ : syracuseStep 1272599 = 1908899) B1908899
theorem B846617 : Blo 562809 846617 := bstep (se 2 (by rfl) ⟨317481, by rfl⟩ : syracuseStep 846617 = 634963) B634963
theorem B846731 : Blo 562809 846731 := bstep (se 1 (by rfl) ⟨635048, by rfl⟩ : syracuseStep 846731 = 1270097) B1270097
theorem B846743 : Blo 562809 846743 := bstep (se 1 (by rfl) ⟨635057, by rfl⟩ : syracuseStep 846743 = 1270115) B1270115
theorem B1272779 : Blo 562809 1272779 := bstep (se 1 (by rfl) ⟨954584, by rfl⟩ : syracuseStep 1272779 = 1909169) B1909169
theorem B846809 : Blo 562809 846809 := bstep (se 2 (by rfl) ⟨317553, by rfl⟩ : syracuseStep 846809 = 635107) B635107
theorem B1272833 : Blo 562809 1272833 := bstep (se 2 (by rfl) ⟨477312, by rfl⟩ : syracuseStep 1272833 = 954625) B954625
theorem B9169955 : Blo 562809 9169955 := bstep (se 1 (by rfl) ⟨6877466, by rfl⟩ : syracuseStep 9169955 = 13754933) B13754933
theorem B1207361 : Blo 562809 1207361 := bstep (se 2 (by rfl) ⟨452760, by rfl⟩ : syracuseStep 1207361 = 905521) B905521
theorem B1928267 : Blo 562809 1928267 := bstep (se 1 (by rfl) ⟨1446200, by rfl⟩ : syracuseStep 1928267 = 2892401) B2892401
theorem B846923 : Blo 562809 846923 := bstep (se 1 (by rfl) ⟨635192, by rfl⟩ : syracuseStep 846923 = 1270385) B1270385
theorem B846935 : Blo 562809 846935 := bstep (se 1 (by rfl) ⟨635201, by rfl⟩ : syracuseStep 846935 = 1270403) B1270403
theorem B2714717 : Blo 562809 2714717 := bstep (se 3 (by rfl) ⟨509009, by rfl⟩ : syracuseStep 2714717 = 1018019) B1018019
theorem B847001 : Blo 562809 847001 := bstep (se 2 (by rfl) ⟨317625, by rfl⟩ : syracuseStep 847001 = 635251) B635251
theorem B2092211 : Blo 562809 2092211 := bstep (se 1 (by rfl) ⟨1569158, by rfl⟩ : syracuseStep 2092211 = 3138317) B3138317
theorem B2288843 : Blo 562809 2288843 := bstep (se 1 (by rfl) ⟨1716632, by rfl⟩ : syracuseStep 2288843 = 3433265) B3433265
theorem B715979 : Blo 562809 715979 := bstep (se 1 (by rfl) ⟨536984, by rfl⟩ : syracuseStep 715979 = 1073969) B1073969
theorem B1273049 : Blo 562809 1273049 := bstep (se 2 (by rfl) ⟨477393, by rfl⟩ : syracuseStep 1273049 = 954787) B954787
theorem B847115 : Blo 562809 847115 := bstep (se 1 (by rfl) ⟨635336, by rfl⟩ : syracuseStep 847115 = 1270673) B1270673
theorem B847127 : Blo 562809 847127 := bstep (se 1 (by rfl) ⟨635345, by rfl⟩ : syracuseStep 847127 = 1270691) B1270691
theorem B1273139 : Blo 562809 1273139 := bstep (se 1 (by rfl) ⟨954854, by rfl⟩ : syracuseStep 1273139 = 1909709) B1909709
theorem B1273175 : Blo 562809 1273175 := bstep (se 1 (by rfl) ⟨954881, by rfl⟩ : syracuseStep 1273175 = 1909763) B1909763
theorem B847193 : Blo 562809 847193 := bstep (se 2 (by rfl) ⟨317697, by rfl⟩ : syracuseStep 847193 = 635395) B635395
theorem B1207703 : Blo 562809 1207703 := bstep (se 1 (by rfl) ⟨905777, by rfl⟩ : syracuseStep 1207703 = 1811555) B1811555
theorem B847307 : Blo 562809 847307 := bstep (se 1 (by rfl) ⟨635480, by rfl⟩ : syracuseStep 847307 = 1270961) B1270961
theorem B847319 : Blo 562809 847319 := bstep (se 1 (by rfl) ⟨635489, by rfl⟩ : syracuseStep 847319 = 1270979) B1270979
theorem B4058585 : Blo 562809 4058585 := bstep (se 2 (by rfl) ⟨1521969, by rfl⟩ : syracuseStep 4058585 = 3043939) B3043939
theorem B2420189 : Blo 562809 2420189 := bstep (se 3 (by rfl) ⟨453785, by rfl⟩ : syracuseStep 2420189 = 907571) B907571
theorem B1273355 : Blo 562809 1273355 := bstep (se 1 (by rfl) ⟨955016, by rfl⟩ : syracuseStep 1273355 = 1910033) B1910033
theorem B847385 : Blo 562809 847385 := bstep (se 2 (by rfl) ⟨317769, by rfl⟩ : syracuseStep 847385 = 635539) B635539
theorem B1273409 : Blo 562809 1273409 := bstep (se 2 (by rfl) ⟨477528, by rfl⟩ : syracuseStep 1273409 = 955057) B955057
theorem B3862117 : Blo 562809 3862117 := bstep (se 4 (by rfl) ⟨362073, by rfl⟩ : syracuseStep 3862117 = 724147) B724147
theorem B847499 : Blo 562809 847499 := bstep (se 1 (by rfl) ⟨635624, by rfl⟩ : syracuseStep 847499 = 1271249) B1271249
theorem B847511 : Blo 562809 847511 := bstep (se 1 (by rfl) ⟨635633, by rfl⟩ : syracuseStep 847511 = 1271267) B1271267
theorem B4812493 : Blo 562809 4812493 := bstep (se 3 (by rfl) ⟨902342, by rfl⟩ : syracuseStep 4812493 = 1804685) B1804685
theorem B847577 : Blo 562809 847577 := bstep (se 2 (by rfl) ⟨317841, by rfl⟩ : syracuseStep 847577 = 635683) B635683
theorem B1273625 : Blo 562809 1273625 := bstep (se 2 (by rfl) ⟨477609, by rfl⟩ : syracuseStep 1273625 = 955219) B955219
theorem B847691 : Blo 562809 847691 := bstep (se 1 (by rfl) ⟨635768, by rfl⟩ : syracuseStep 847691 = 1271537) B1271537
theorem B847703 : Blo 562809 847703 := bstep (se 1 (by rfl) ⟨635777, by rfl⟩ : syracuseStep 847703 = 1271555) B1271555
theorem B1273715 : Blo 562809 1273715 := bstep (se 1 (by rfl) ⟨955286, by rfl⟩ : syracuseStep 1273715 = 1910573) B1910573
theorem B716683 : Blo 562809 716683 := bstep (se 1 (by rfl) ⟨537512, by rfl⟩ : syracuseStep 716683 = 1075025) B1075025
theorem B1273751 : Blo 562809 1273751 := bstep (se 1 (by rfl) ⟨955313, by rfl⟩ : syracuseStep 1273751 = 1910627) B1910627
theorem B847769 : Blo 562809 847769 := bstep (se 2 (by rfl) ⟨317913, by rfl⟩ : syracuseStep 847769 = 635827) B635827
theorem B2584493 : Blo 562809 2584493 := bstep (se 3 (by rfl) ⟨484592, by rfl⟩ : syracuseStep 2584493 = 969185) B969185
theorem B1208267 : Blo 562809 1208267 := bstep (se 1 (by rfl) ⟨906200, by rfl⟩ : syracuseStep 1208267 = 1812401) B1812401
theorem B847883 : Blo 562809 847883 := bstep (se 1 (by rfl) ⟨635912, by rfl⟩ : syracuseStep 847883 = 1271825) B1271825
theorem B847895 : Blo 562809 847895 := bstep (se 1 (by rfl) ⟨635921, by rfl⟩ : syracuseStep 847895 = 1271843) B1271843
theorem B1273931 : Blo 562809 1273931 := bstep (se 1 (by rfl) ⟨955448, by rfl⟩ : syracuseStep 1273931 = 1910897) B1910897
theorem B847961 : Blo 562809 847961 := bstep (se 2 (by rfl) ⟨317985, by rfl⟩ : syracuseStep 847961 = 635971) B635971
theorem B1273985 : Blo 562809 1273985 := bstep (se 2 (by rfl) ⟨477744, by rfl⟩ : syracuseStep 1273985 = 955489) B955489
theorem B815243 : Blo 562809 815243 := bstep (se 1 (by rfl) ⟨611432, by rfl⟩ : syracuseStep 815243 = 1222865) B1222865
theorem B716951 : Blo 562809 716951 := bstep (se 1 (by rfl) ⟨537713, by rfl⟩ : syracuseStep 716951 = 1075427) B1075427
theorem B848075 : Blo 562809 848075 := bstep (se 1 (by rfl) ⟨636056, by rfl⟩ : syracuseStep 848075 = 1272113) B1272113
theorem B848087 : Blo 562809 848087 := bstep (se 1 (by rfl) ⟨636065, by rfl⟩ : syracuseStep 848087 = 1272131) B1272131
theorem B848153 : Blo 562809 848153 := bstep (se 2 (by rfl) ⟨318057, by rfl⟩ : syracuseStep 848153 = 636115) B636115
theorem B1274201 : Blo 562809 1274201 := bstep (se 2 (by rfl) ⟨477825, by rfl⟩ : syracuseStep 1274201 = 955651) B955651
theorem B848267 : Blo 562809 848267 := bstep (se 1 (by rfl) ⟨636200, by rfl⟩ : syracuseStep 848267 = 1272401) B1272401
theorem B848279 : Blo 562809 848279 := bstep (se 1 (by rfl) ⟨636209, by rfl⟩ : syracuseStep 848279 = 1272419) B1272419
theorem B1274291 : Blo 562809 1274291 := bstep (se 1 (by rfl) ⟨955718, by rfl⟩ : syracuseStep 1274291 = 1911437) B1911437
theorem B1274327 : Blo 562809 1274327 := bstep (se 1 (by rfl) ⟨955745, by rfl⟩ : syracuseStep 1274327 = 1911491) B1911491
theorem B848345 : Blo 562809 848345 := bstep (se 2 (by rfl) ⟨318129, by rfl⟩ : syracuseStep 848345 = 636259) B636259
theorem B1208857 : Blo 562809 1208857 := bstep (se 2 (by rfl) ⟨453321, by rfl⟩ : syracuseStep 1208857 = 906643) B906643
theorem B848459 : Blo 562809 848459 := bstep (se 1 (by rfl) ⟨636344, by rfl⟩ : syracuseStep 848459 = 1272689) B1272689
theorem B848471 : Blo 562809 848471 := bstep (se 1 (by rfl) ⟨636353, by rfl⟩ : syracuseStep 848471 = 1272707) B1272707
theorem B1274507 : Blo 562809 1274507 := bstep (se 1 (by rfl) ⟨955880, by rfl⟩ : syracuseStep 1274507 = 1911761) B1911761
theorem B848537 : Blo 562809 848537 := bstep (se 2 (by rfl) ⟨318201, by rfl⟩ : syracuseStep 848537 = 636403) B636403
theorem B1274561 : Blo 562809 1274561 := bstep (se 2 (by rfl) ⟨477960, by rfl⟩ : syracuseStep 1274561 = 955921) B955921
theorem B4453069 : Blo 562809 4453069 := bstep (se 3 (by rfl) ⟨834950, by rfl⟩ : syracuseStep 4453069 = 1669901) B1669901
theorem B848651 : Blo 562809 848651 := bstep (se 1 (by rfl) ⟨636488, by rfl⟩ : syracuseStep 848651 = 1272977) B1272977
theorem B848663 : Blo 562809 848663 := bstep (se 1 (by rfl) ⟨636497, by rfl⟩ : syracuseStep 848663 = 1272995) B1272995
theorem B815959 : Blo 562809 815959 := bstep (se 1 (by rfl) ⟨611969, by rfl⟩ : syracuseStep 815959 = 1223939) B1223939
theorem B848729 : Blo 562809 848729 := bstep (se 2 (by rfl) ⟨318273, by rfl⟩ : syracuseStep 848729 = 636547) B636547
theorem B1274777 : Blo 562809 1274777 := bstep (se 2 (by rfl) ⟨478041, by rfl⟩ : syracuseStep 1274777 = 956083) B956083
theorem B848843 : Blo 562809 848843 := bstep (se 1 (by rfl) ⟨636632, by rfl⟩ : syracuseStep 848843 = 1273265) B1273265
theorem B848855 : Blo 562809 848855 := bstep (se 1 (by rfl) ⟨636641, by rfl⟩ : syracuseStep 848855 = 1273283) B1273283
theorem B1274867 : Blo 562809 1274867 := bstep (se 1 (by rfl) ⟨956150, by rfl⟩ : syracuseStep 1274867 = 1912301) B1912301
theorem B4813829 : Blo 562809 4813829 := bstep (se 4 (by rfl) ⟨451296, by rfl⟩ : syracuseStep 4813829 = 902593) B902593
theorem B1274903 : Blo 562809 1274903 := bstep (se 1 (by rfl) ⟨956177, by rfl⟩ : syracuseStep 1274903 = 1912355) B1912355
theorem B848921 : Blo 562809 848921 := bstep (se 2 (by rfl) ⟨318345, by rfl⟩ : syracuseStep 848921 = 636691) B636691
theorem B2946179 : Blo 562809 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B849035 : Blo 562809 849035 := bstep (se 1 (by rfl) ⟨636776, by rfl⟩ : syracuseStep 849035 = 1273553) B1273553
theorem B849047 : Blo 562809 849047 := bstep (se 1 (by rfl) ⟨636785, by rfl⟩ : syracuseStep 849047 = 1273571) B1273571
theorem B1275083 : Blo 562809 1275083 := bstep (se 1 (by rfl) ⟨956312, by rfl⟩ : syracuseStep 1275083 = 1912625) B1912625
theorem B849113 : Blo 562809 849113 := bstep (se 2 (by rfl) ⟨318417, by rfl⟩ : syracuseStep 849113 = 636835) B636835
theorem B1275137 : Blo 562809 1275137 := bstep (se 2 (by rfl) ⟨478176, by rfl⟩ : syracuseStep 1275137 = 956353) B956353
theorem B849227 : Blo 562809 849227 := bstep (se 1 (by rfl) ⟨636920, by rfl⟩ : syracuseStep 849227 = 1273841) B1273841
theorem B849239 : Blo 562809 849239 := bstep (se 1 (by rfl) ⟨636929, by rfl⟩ : syracuseStep 849239 = 1273859) B1273859
theorem B849305 : Blo 562809 849305 := bstep (se 2 (by rfl) ⟨318489, by rfl⟩ : syracuseStep 849305 = 636979) B636979
theorem B849419 : Blo 562809 849419 := bstep (se 1 (by rfl) ⟨637064, by rfl⟩ : syracuseStep 849419 = 1274129) B1274129
theorem B849431 : Blo 562809 849431 := bstep (se 1 (by rfl) ⟨637073, by rfl⟩ : syracuseStep 849431 = 1274147) B1274147
theorem B1209907 : Blo 562809 1209907 := bstep (se 1 (by rfl) ⟨907430, by rfl⟩ : syracuseStep 1209907 = 1814861) B1814861
theorem B849497 : Blo 562809 849497 := bstep (se 2 (by rfl) ⟨318561, by rfl⟩ : syracuseStep 849497 = 637123) B637123
theorem B849611 : Blo 562809 849611 := bstep (se 1 (by rfl) ⟨637208, by rfl⟩ : syracuseStep 849611 = 1274417) B1274417
theorem B849623 : Blo 562809 849623 := bstep (se 1 (by rfl) ⟨637217, by rfl⟩ : syracuseStep 849623 = 1274435) B1274435
theorem B849689 : Blo 562809 849689 := bstep (se 2 (by rfl) ⟨318633, by rfl⟩ : syracuseStep 849689 = 637267) B637267
theorem B849803 : Blo 562809 849803 := bstep (se 1 (by rfl) ⟨637352, by rfl⟩ : syracuseStep 849803 = 1274705) B1274705
theorem B849815 : Blo 562809 849815 := bstep (se 1 (by rfl) ⟨637361, by rfl⟩ : syracuseStep 849815 = 1274723) B1274723
theorem B849881 : Blo 562809 849881 := bstep (se 2 (by rfl) ⟨318705, by rfl⟩ : syracuseStep 849881 = 637411) B637411
theorem B849995 : Blo 562809 849995 := bstep (se 1 (by rfl) ⟨637496, by rfl⟩ : syracuseStep 849995 = 1274993) B1274993
theorem B850007 : Blo 562809 850007 := bstep (se 1 (by rfl) ⟨637505, by rfl⟩ : syracuseStep 850007 = 1275011) B1275011
theorem B653431 : Blo 562809 653431 := bstep (se 1 (by rfl) ⟨490073, by rfl⟩ : syracuseStep 653431 = 980147) B980147
theorem B6125719 : Blo 562809 6125719 := bstep (se 1 (by rfl) ⟨4594289, by rfl⟩ : syracuseStep 6125719 = 9188579) B9188579
theorem B850073 : Blo 562809 850073 := bstep (se 2 (by rfl) ⟨318777, by rfl⟩ : syracuseStep 850073 = 637555) B637555
theorem B2291971 : Blo 562809 2291971 := bstep (se 1 (by rfl) ⟨1718978, by rfl⟩ : syracuseStep 2291971 = 3437957) B3437957
theorem B850187 : Blo 562809 850187 := bstep (se 1 (by rfl) ⟨637640, by rfl⟩ : syracuseStep 850187 = 1275281) B1275281
theorem B850199 : Blo 562809 850199 := bstep (se 1 (by rfl) ⟨637649, by rfl⟩ : syracuseStep 850199 = 1275299) B1275299
theorem B1603891 : Blo 562809 1603891 := bstep (se 1 (by rfl) ⟨1202918, by rfl⟩ : syracuseStep 1603891 = 2405837) B2405837
theorem B2029913 : Blo 562809 2029913 := bstep (se 2 (by rfl) ⟨761217, by rfl⟩ : syracuseStep 2029913 = 1522435) B1522435
theorem B1309043 : Blo 562809 1309043 := bstep (se 1 (by rfl) ⟨981782, by rfl⟩ : syracuseStep 1309043 = 1963565) B1963565
theorem B883097 : Blo 562809 883097 := bstep (se 2 (by rfl) ⟨331161, by rfl⟩ : syracuseStep 883097 = 662323) B662323
theorem B3209651 : Blo 562809 3209651 := bstep (se 1 (by rfl) ⟨2407238, by rfl⟩ : syracuseStep 3209651 = 4814477) B4814477
theorem B1604119 : Blo 562809 1604119 := bstep (se 1 (by rfl) ⟨1203089, by rfl⟩ : syracuseStep 1604119 = 2406179) B2406179
theorem B1014401 : Blo 562809 1014401 := bstep (se 2 (by rfl) ⟨380400, by rfl⟩ : syracuseStep 1014401 = 760801) B760801
theorem B19037105 : Blo 562809 19037105 := bstep (se 2 (by rfl) ⟨7138914, by rfl⟩ : syracuseStep 19037105 = 14277829) B14277829
theorem B1375255 : Blo 562809 1375255 := bstep (se 1 (by rfl) ⟨1031441, by rfl⟩ : syracuseStep 1375255 = 2062883) B2062883
theorem B2850065 : Blo 562809 2850065 := bstep (se 2 (by rfl) ⟨1068774, by rfl⟩ : syracuseStep 2850065 = 2137549) B2137549
theorem B1899827 : Blo 562809 1899827 := bstep (se 1 (by rfl) ⟨1424870, by rfl⟩ : syracuseStep 1899827 = 2849741) B2849741
theorem B2850227 : Blo 562809 2850227 := bstep (se 1 (by rfl) ⟨2137670, by rfl⟩ : syracuseStep 2850227 = 4275341) B4275341
theorem B1900097 : Blo 562809 1900097 := bstep (se 2 (by rfl) ⟨712536, by rfl⟩ : syracuseStep 1900097 = 1425073) B1425073
theorem B3211109 : Blo 562809 3211109 := bstep (se 4 (by rfl) ⟨301041, by rfl⟩ : syracuseStep 3211109 = 602083) B602083
theorem B3440485 : Blo 562809 3440485 := bstep (se 4 (by rfl) ⟨322545, by rfl⟩ : syracuseStep 3440485 = 645091) B645091
theorem B950231 : Blo 562809 950231 := bstep (se 1 (by rfl) ⟨712673, by rfl⟩ : syracuseStep 950231 = 1425347) B1425347
theorem B6422489 : Blo 562809 6422489 := bstep (se 2 (by rfl) ⟨2408433, by rfl⟩ : syracuseStep 6422489 = 4816867) B4816867
theorem B2719831 : Blo 562809 2719831 := bstep (se 1 (by rfl) ⟨2039873, by rfl⟩ : syracuseStep 2719831 = 4079747) B4079747
theorem B1900745 : Blo 562809 1900745 := bstep (se 2 (by rfl) ⟨712779, by rfl⟩ : syracuseStep 1900745 = 1425559) B1425559
theorem B3211609 : Blo 562809 3211609 := bstep (se 2 (by rfl) ⟨1204353, by rfl⟩ : syracuseStep 3211609 = 2408707) B2408707
theorem B950663 : Blo 562809 950663 := bstep (se 1 (by rfl) ⟨712997, by rfl⟩ : syracuseStep 950663 = 1425995) B1425995
theorem B5439889 : Blo 562809 5439889 := bstep (se 2 (by rfl) ⟨2039958, by rfl⟩ : syracuseStep 5439889 = 4079917) B4079917
theorem B1016635 : Blo 562809 1016635 := bstep (se 1 (by rfl) ⟨762476, by rfl⟩ : syracuseStep 1016635 = 1524953) B1524953
theorem B1901447 : Blo 562809 1901447 := bstep (se 1 (by rfl) ⟨1426085, by rfl⟩ : syracuseStep 1901447 = 2852171) B2852171
theorem B951311 : Blo 562809 951311 := bstep (se 1 (by rfl) ⟨713483, by rfl⟩ : syracuseStep 951311 = 1426967) B1426967
theorem B1901825 : Blo 562809 1901825 := bstep (se 2 (by rfl) ⟨713184, by rfl⟩ : syracuseStep 1901825 = 1426369) B1426369
theorem B951851 : Blo 562809 951851 := bstep (se 1 (by rfl) ⟨713888, by rfl⟩ : syracuseStep 951851 = 1427777) B1427777
theorem B1607435 : Blo 562809 1607435 := bstep (se 1 (by rfl) ⟨1205576, by rfl⟩ : syracuseStep 1607435 = 2411153) B2411153
theorem B722731 : Blo 562809 722731 := bstep (se 1 (by rfl) ⟨542048, by rfl⟩ : syracuseStep 722731 = 1084097) B1084097
theorem B10618775 : Blo 562809 10618775 := bstep (se 1 (by rfl) ⟨7964081, by rfl⟩ : syracuseStep 10618775 = 15928163) B15928163
theorem B4818851 : Blo 562809 4818851 := bstep (se 1 (by rfl) ⟨3614138, by rfl⟩ : syracuseStep 4818851 = 7228277) B7228277
theorem B952249 : Blo 562809 952249 := bstep (se 2 (by rfl) ⟨357093, by rfl⟩ : syracuseStep 952249 = 714187) B714187
theorem B3213341 : Blo 562809 3213341 := bstep (se 3 (by rfl) ⟨602501, by rfl⟩ : syracuseStep 3213341 = 1205003) B1205003
theorem B1902635 : Blo 562809 1902635 := bstep (se 1 (by rfl) ⟨1426976, by rfl⟩ : syracuseStep 1902635 = 2853953) B2853953
theorem B3049559 : Blo 562809 3049559 := bstep (se 1 (by rfl) ⟨2287169, by rfl⟩ : syracuseStep 3049559 = 4574339) B4574339
theorem B5507345 : Blo 562809 5507345 := bstep (se 2 (by rfl) ⟨2065254, by rfl⟩ : syracuseStep 5507345 = 4130509) B4130509
theorem B1608083 : Blo 562809 1608083 := bstep (se 1 (by rfl) ⟨1206062, by rfl⟩ : syracuseStep 1608083 = 2412125) B2412125
theorem B2853305 : Blo 562809 2853305 := bstep (se 2 (by rfl) ⟨1069989, by rfl⟩ : syracuseStep 2853305 = 2139979) B2139979
theorem B952951 : Blo 562809 952951 := bstep (se 1 (by rfl) ⟨714713, by rfl⟩ : syracuseStep 952951 = 1429427) B1429427
theorem B1608311 : Blo 562809 1608311 := bstep (se 1 (by rfl) ⟨1206233, by rfl⟩ : syracuseStep 1608311 = 2412467) B2412467
theorem B3214025 : Blo 562809 3214025 := bstep (se 2 (by rfl) ⟨1205259, by rfl⟩ : syracuseStep 3214025 = 2410519) B2410519
theorem B953147 : Blo 562809 953147 := bstep (se 1 (by rfl) ⟨714860, by rfl⟩ : syracuseStep 953147 = 1429721) B1429721
theorem B953545 : Blo 562809 953545 := bstep (se 2 (by rfl) ⟨357579, by rfl⟩ : syracuseStep 953545 = 715159) B715159
theorem B724231 : Blo 562809 724231 := bstep (se 1 (by rfl) ⟨543173, by rfl⟩ : syracuseStep 724231 = 1086347) B1086347
theorem B1903931 : Blo 562809 1903931 := bstep (se 1 (by rfl) ⟨1427948, by rfl⟩ : syracuseStep 1903931 = 2855897) B2855897
theorem B7179853 : Blo 562809 7179853 := bstep (se 3 (by rfl) ⟨1346222, by rfl⟩ : syracuseStep 7179853 = 2692445) B2692445
theorem B8261297 : Blo 562809 8261297 := bstep (se 2 (by rfl) ⟨3097986, by rfl⟩ : syracuseStep 8261297 = 6195973) B6195973
theorem B2854601 : Blo 562809 2854601 := bstep (se 2 (by rfl) ⟨1070475, by rfl⟩ : syracuseStep 2854601 = 2140951) B2140951
theorem B1904417 : Blo 562809 1904417 := bstep (se 2 (by rfl) ⟨714156, by rfl⟩ : syracuseStep 1904417 = 1428313) B1428313
theorem B5148467 : Blo 562809 5148467 := bstep (se 1 (by rfl) ⟨3861350, by rfl⟩ : syracuseStep 5148467 = 7722701) B7722701
theorem B2723635 : Blo 562809 2723635 := bstep (se 1 (by rfl) ⟨2042726, by rfl⟩ : syracuseStep 2723635 = 4085453) B4085453
theorem B954247 : Blo 562809 954247 := bstep (se 1 (by rfl) ⟨715685, by rfl⟩ : syracuseStep 954247 = 1431371) B1431371
theorem B3903385 : Blo 562809 3903385 := bstep (se 2 (by rfl) ⟨1463769, by rfl⟩ : syracuseStep 3903385 = 2927539) B2927539
theorem B3084331 : Blo 562809 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B1937495 : Blo 562809 1937495 := bstep (se 1 (by rfl) ⟨1453121, by rfl⟩ : syracuseStep 1937495 = 2906243) B2906243
theorem B1806455 : Blo 562809 1806455 := bstep (se 1 (by rfl) ⟨1354841, by rfl⟩ : syracuseStep 1806455 = 2709683) B2709683
theorem B1905011 : Blo 562809 1905011 := bstep (se 1 (by rfl) ⟨1428758, by rfl⟩ : syracuseStep 1905011 = 2857517) B2857517
theorem B1085815 : Blo 562809 1085815 := bstep (se 1 (by rfl) ⟨814361, by rfl⟩ : syracuseStep 1085815 = 1628723) B1628723
theorem B3215801 : Blo 562809 3215801 := bstep (se 2 (by rfl) ⟨1205925, by rfl⟩ : syracuseStep 3215801 = 2411851) B2411851
theorem B856583 : Blo 562809 856583 := bstep (se 1 (by rfl) ⟨642437, by rfl⟩ : syracuseStep 856583 = 1284875) B1284875
theorem B954895 : Blo 562809 954895 := bstep (se 1 (by rfl) ⟨716171, by rfl⟩ : syracuseStep 954895 = 1432343) B1432343
theorem B59609621 : Blo 562809 59609621 := bstep (se 6 (by rfl) ⟨1397100, by rfl⟩ : syracuseStep 59609621 = 2794201) B2794201
theorem B3904271 : Blo 562809 3904271 := bstep (se 1 (by rfl) ⟨2928203, by rfl⟩ : syracuseStep 3904271 = 5856407) B5856407
theorem B1086251 : Blo 562809 1086251 := bstep (se 1 (by rfl) ⟨814688, by rfl⟩ : syracuseStep 1086251 = 1629377) B1629377
theorem B5149489 : Blo 562809 5149489 := bstep (se 2 (by rfl) ⟨1931058, by rfl⟩ : syracuseStep 5149489 = 3862117) B3862117
theorem B955435 : Blo 562809 955435 := bstep (se 1 (by rfl) ⟨716576, by rfl⟩ : syracuseStep 955435 = 1433153) B1433153
theorem B955577 : Blo 562809 955577 := bstep (se 2 (by rfl) ⟨358341, by rfl⟩ : syracuseStep 955577 = 716683) B716683
theorem B1807915 : Blo 562809 1807915 := bstep (se 1 (by rfl) ⟨1355936, by rfl⟩ : syracuseStep 1807915 = 2711873) B2711873
theorem B562823 : Blo 562809 562823 := bstep (se 1 (by rfl) ⟨422117, by rfl⟩ : syracuseStep 562823 = 844235) B844235
theorem B562831 : Blo 562809 562831 := bstep (se 1 (by rfl) ⟨422123, by rfl⟩ : syracuseStep 562831 = 844247) B844247
theorem B562875 : Blo 562809 562875 := bstep (se 1 (by rfl) ⟨422156, by rfl⟩ : syracuseStep 562875 = 844313) B844313
theorem B562951 : Blo 562809 562951 := bstep (se 1 (by rfl) ⟨422213, by rfl⟩ : syracuseStep 562951 = 844427) B844427
theorem B562959 : Blo 562809 562959 := bstep (se 1 (by rfl) ⟨422219, by rfl⟩ : syracuseStep 562959 = 844439) B844439
theorem B1611535 : Blo 562809 1611535 := bstep (se 1 (by rfl) ⟨1208651, by rfl⟩ : syracuseStep 1611535 = 2417303) B2417303
theorem B563003 : Blo 562809 563003 := bstep (se 1 (by rfl) ⟨422252, by rfl⟩ : syracuseStep 563003 = 844505) B844505
theorem B1087291 : Blo 562809 1087291 := bstep (se 1 (by rfl) ⟨815468, by rfl⟩ : syracuseStep 1087291 = 1630937) B1630937
theorem B3872627 : Blo 562809 3872627 := bstep (se 1 (by rfl) ⟨2904470, by rfl⟩ : syracuseStep 3872627 = 5808941) B5808941
theorem B956279 : Blo 562809 956279 := bstep (se 1 (by rfl) ⟨717209, by rfl⟩ : syracuseStep 956279 = 1434419) B1434419
theorem B563079 : Blo 562809 563079 := bstep (se 1 (by rfl) ⟨422309, by rfl⟩ : syracuseStep 563079 = 844619) B844619
theorem B563087 : Blo 562809 563087 := bstep (se 1 (by rfl) ⟨422315, by rfl⟩ : syracuseStep 563087 = 844631) B844631
theorem B563131 : Blo 562809 563131 := bstep (se 1 (by rfl) ⟨422348, by rfl⟩ : syracuseStep 563131 = 844697) B844697
theorem B563207 : Blo 562809 563207 := bstep (se 1 (by rfl) ⟨422405, by rfl⟩ : syracuseStep 563207 = 844811) B844811
theorem B563215 : Blo 562809 563215 := bstep (se 1 (by rfl) ⟨422411, by rfl⟩ : syracuseStep 563215 = 844823) B844823
theorem B858127 : Blo 562809 858127 := bstep (se 1 (by rfl) ⟨643595, by rfl⟩ : syracuseStep 858127 = 1287191) B1287191
theorem B1611809 : Blo 562809 1611809 := bstep (se 2 (by rfl) ⟨604428, by rfl⟩ : syracuseStep 1611809 = 1208857) B1208857
theorem B563259 : Blo 562809 563259 := bstep (se 1 (by rfl) ⟨422444, by rfl⟩ : syracuseStep 563259 = 844889) B844889
theorem B1087607 : Blo 562809 1087607 := bstep (se 1 (by rfl) ⟨815705, by rfl⟩ : syracuseStep 1087607 = 1631411) B1631411
theorem B563335 : Blo 562809 563335 := bstep (se 1 (by rfl) ⟨422501, by rfl⟩ : syracuseStep 563335 = 845003) B845003
theorem B563343 : Blo 562809 563343 := bstep (se 1 (by rfl) ⟨422507, by rfl⟩ : syracuseStep 563343 = 845015) B845015
theorem B563387 : Blo 562809 563387 := bstep (se 1 (by rfl) ⟨422540, by rfl⟩ : syracuseStep 563387 = 845081) B845081
theorem B563463 : Blo 562809 563463 := bstep (se 1 (by rfl) ⟨422597, by rfl⟩ : syracuseStep 563463 = 845195) B845195
theorem B563471 : Blo 562809 563471 := bstep (se 1 (by rfl) ⟨422603, by rfl⟩ : syracuseStep 563471 = 845207) B845207
theorem B5937425 : Blo 562809 5937425 := bstep (se 2 (by rfl) ⟨2226534, by rfl⟩ : syracuseStep 5937425 = 4453069) B4453069
theorem B7706897 : Blo 562809 7706897 := bstep (se 2 (by rfl) ⟨2890086, by rfl⟩ : syracuseStep 7706897 = 5780173) B5780173
theorem B3217715 : Blo 562809 3217715 := bstep (se 1 (by rfl) ⟨2413286, by rfl⟩ : syracuseStep 3217715 = 4826573) B4826573
theorem B563515 : Blo 562809 563515 := bstep (se 1 (by rfl) ⟨422636, by rfl⟩ : syracuseStep 563515 = 845273) B845273
theorem B563591 : Blo 562809 563591 := bstep (se 1 (by rfl) ⟨422693, by rfl⟩ : syracuseStep 563591 = 845387) B845387
theorem B563599 : Blo 562809 563599 := bstep (se 1 (by rfl) ⟨422699, by rfl⟩ : syracuseStep 563599 = 845399) B845399
theorem B4299155 : Blo 562809 4299155 := bstep (se 1 (by rfl) ⟨3224366, by rfl⟩ : syracuseStep 4299155 = 6448733) B6448733
theorem B23239061 : Blo 562809 23239061 := bstep (se 6 (by rfl) ⟨544665, by rfl⟩ : syracuseStep 23239061 = 1089331) B1089331
theorem B563643 : Blo 562809 563643 := bstep (se 1 (by rfl) ⟨422732, by rfl⟩ : syracuseStep 563643 = 845465) B845465
theorem B563719 : Blo 562809 563719 := bstep (se 1 (by rfl) ⟨422789, by rfl⟩ : syracuseStep 563719 = 845579) B845579
theorem B563727 : Blo 562809 563727 := bstep (se 1 (by rfl) ⟨422795, by rfl⟩ : syracuseStep 563727 = 845591) B845591
theorem B563771 : Blo 562809 563771 := bstep (se 1 (by rfl) ⟨422828, by rfl⟩ : syracuseStep 563771 = 845657) B845657
theorem B563847 : Blo 562809 563847 := bstep (se 1 (by rfl) ⟨422885, by rfl⟩ : syracuseStep 563847 = 845771) B845771
theorem B563855 : Blo 562809 563855 := bstep (se 1 (by rfl) ⟨422891, by rfl⟩ : syracuseStep 563855 = 845783) B845783
theorem B563899 : Blo 562809 563899 := bstep (se 1 (by rfl) ⟨422924, by rfl⟩ : syracuseStep 563899 = 845849) B845849
theorem B563975 : Blo 562809 563975 := bstep (se 1 (by rfl) ⟨422981, by rfl⟩ : syracuseStep 563975 = 845963) B845963
theorem B563983 : Blo 562809 563983 := bstep (se 1 (by rfl) ⟨422987, by rfl⟩ : syracuseStep 563983 = 845975) B845975
theorem B564027 : Blo 562809 564027 := bstep (se 1 (by rfl) ⟨423020, by rfl⟩ : syracuseStep 564027 = 846041) B846041
theorem B564103 : Blo 562809 564103 := bstep (se 1 (by rfl) ⟨423077, by rfl⟩ : syracuseStep 564103 = 846155) B846155
theorem B1809287 : Blo 562809 1809287 := bstep (se 1 (by rfl) ⟨1356965, by rfl⟩ : syracuseStep 1809287 = 2713931) B2713931
theorem B564111 : Blo 562809 564111 := bstep (se 1 (by rfl) ⟨423083, by rfl⟩ : syracuseStep 564111 = 846167) B846167
theorem B1809299 : Blo 562809 1809299 := bstep (se 1 (by rfl) ⟨1356974, by rfl⟩ : syracuseStep 1809299 = 2713949) B2713949
theorem B1907603 : Blo 562809 1907603 := bstep (se 1 (by rfl) ⟨1430702, by rfl⟩ : syracuseStep 1907603 = 2861405) B2861405
theorem B760747 : Blo 562809 760747 := bstep (se 1 (by rfl) ⟨570560, by rfl⟩ : syracuseStep 760747 = 1141121) B1141121
theorem B2202553 : Blo 562809 2202553 := bstep (se 2 (by rfl) ⟨825957, by rfl⟩ : syracuseStep 2202553 = 1651915) B1651915
theorem B564155 : Blo 562809 564155 := bstep (se 1 (by rfl) ⟨423116, by rfl⟩ : syracuseStep 564155 = 846233) B846233
theorem B564231 : Blo 562809 564231 := bstep (se 1 (by rfl) ⟨423173, by rfl⟩ : syracuseStep 564231 = 846347) B846347
theorem B1612811 : Blo 562809 1612811 := bstep (se 1 (by rfl) ⟨1209608, by rfl⟩ : syracuseStep 1612811 = 2419217) B2419217
theorem B564239 : Blo 562809 564239 := bstep (se 1 (by rfl) ⟨423179, by rfl⟩ : syracuseStep 564239 = 846359) B846359
theorem B564283 : Blo 562809 564283 := bstep (se 1 (by rfl) ⟨423212, by rfl⟩ : syracuseStep 564283 = 846425) B846425
theorem B14097539 : Blo 562809 14097539 := bstep (se 1 (by rfl) ⟨10573154, by rfl⟩ : syracuseStep 14097539 = 21146309) B21146309
theorem B564359 : Blo 562809 564359 := bstep (se 1 (by rfl) ⟨423269, by rfl⟩ : syracuseStep 564359 = 846539) B846539
theorem B564367 : Blo 562809 564367 := bstep (se 1 (by rfl) ⟨423275, by rfl⟩ : syracuseStep 564367 = 846551) B846551
theorem B564411 : Blo 562809 564411 := bstep (se 1 (by rfl) ⟨423308, by rfl⟩ : syracuseStep 564411 = 846617) B846617
theorem B564487 : Blo 562809 564487 := bstep (se 1 (by rfl) ⟨423365, by rfl⟩ : syracuseStep 564487 = 846731) B846731
theorem B564495 : Blo 562809 564495 := bstep (se 1 (by rfl) ⟨423371, by rfl⟩ : syracuseStep 564495 = 846743) B846743
theorem B1809697 : Blo 562809 1809697 := bstep (se 2 (by rfl) ⟨678636, by rfl⟩ : syracuseStep 1809697 = 1357273) B1357273
theorem B564539 : Blo 562809 564539 := bstep (se 1 (by rfl) ⟨423404, by rfl⟩ : syracuseStep 564539 = 846809) B846809
theorem B1285511 : Blo 562809 1285511 := bstep (se 1 (by rfl) ⟨964133, by rfl⟩ : syracuseStep 1285511 = 1928267) B1928267
theorem B564615 : Blo 562809 564615 := bstep (se 1 (by rfl) ⟨423461, by rfl⟩ : syracuseStep 564615 = 846923) B846923
theorem B564623 : Blo 562809 564623 := bstep (se 1 (by rfl) ⟨423467, by rfl⟩ : syracuseStep 564623 = 846935) B846935
theorem B1809811 : Blo 562809 1809811 := bstep (se 1 (by rfl) ⟨1357358, by rfl⟩ : syracuseStep 1809811 = 2714717) B2714717
theorem B1613209 : Blo 562809 1613209 := bstep (se 2 (by rfl) ⟨604953, by rfl⟩ : syracuseStep 1613209 = 1209907) B1209907
theorem B564667 : Blo 562809 564667 := bstep (se 1 (by rfl) ⟨423500, by rfl⟩ : syracuseStep 564667 = 847001) B847001
theorem B564743 : Blo 562809 564743 := bstep (se 1 (by rfl) ⟨423557, by rfl⟩ : syracuseStep 564743 = 847115) B847115
theorem B564751 : Blo 562809 564751 := bstep (se 1 (by rfl) ⟨423563, by rfl⟩ : syracuseStep 564751 = 847127) B847127
theorem B564795 : Blo 562809 564795 := bstep (se 1 (by rfl) ⟨423596, by rfl⟩ : syracuseStep 564795 = 847193) B847193
theorem B564871 : Blo 562809 564871 := bstep (se 1 (by rfl) ⟨423653, by rfl⟩ : syracuseStep 564871 = 847307) B847307
theorem B564879 : Blo 562809 564879 := bstep (se 1 (by rfl) ⟨423659, by rfl⟩ : syracuseStep 564879 = 847319) B847319
theorem B1613459 : Blo 562809 1613459 := bstep (se 1 (by rfl) ⟨1210094, by rfl⟩ : syracuseStep 1613459 = 2420189) B2420189
theorem B564923 : Blo 562809 564923 := bstep (se 1 (by rfl) ⟨423692, by rfl⟩ : syracuseStep 564923 = 847385) B847385
theorem B3219173 : Blo 562809 3219173 := bstep (se 4 (by rfl) ⟨301797, by rfl⟩ : syracuseStep 3219173 = 603595) B603595
theorem B564999 : Blo 562809 564999 := bstep (se 1 (by rfl) ⟨423749, by rfl⟩ : syracuseStep 564999 = 847499) B847499
theorem B565007 : Blo 562809 565007 := bstep (se 1 (by rfl) ⟨423755, by rfl⟩ : syracuseStep 565007 = 847511) B847511
theorem B565051 : Blo 562809 565051 := bstep (se 1 (by rfl) ⟨423788, by rfl⟩ : syracuseStep 565051 = 847577) B847577
theorem B565127 : Blo 562809 565127 := bstep (se 1 (by rfl) ⟨423845, by rfl⟩ : syracuseStep 565127 = 847691) B847691
theorem B565135 : Blo 562809 565135 := bstep (se 1 (by rfl) ⟨423851, by rfl⟩ : syracuseStep 565135 = 847703) B847703
theorem B565179 : Blo 562809 565179 := bstep (se 1 (by rfl) ⟨423884, by rfl⟩ : syracuseStep 565179 = 847769) B847769
theorem B565255 : Blo 562809 565255 := bstep (se 1 (by rfl) ⟨423941, by rfl⟩ : syracuseStep 565255 = 847883) B847883
theorem B565263 : Blo 562809 565263 := bstep (se 1 (by rfl) ⟨423947, by rfl⟩ : syracuseStep 565263 = 847895) B847895
theorem B565307 : Blo 562809 565307 := bstep (se 1 (by rfl) ⟨423980, by rfl⟩ : syracuseStep 565307 = 847961) B847961
theorem B565383 : Blo 562809 565383 := bstep (se 1 (by rfl) ⟨424037, by rfl⟩ : syracuseStep 565383 = 848075) B848075
theorem B565391 : Blo 562809 565391 := bstep (se 1 (by rfl) ⟨424043, by rfl⟩ : syracuseStep 565391 = 848087) B848087
theorem B565435 : Blo 562809 565435 := bstep (se 1 (by rfl) ⟨424076, by rfl⟩ : syracuseStep 565435 = 848153) B848153
theorem B8167625 : Blo 562809 8167625 := bstep (se 2 (by rfl) ⟨3062859, by rfl⟩ : syracuseStep 8167625 = 6125719) B6125719
theorem B565511 : Blo 562809 565511 := bstep (se 1 (by rfl) ⟨424133, by rfl⟩ : syracuseStep 565511 = 848267) B848267
theorem B565519 : Blo 562809 565519 := bstep (se 1 (by rfl) ⟨424139, by rfl⟩ : syracuseStep 565519 = 848279) B848279
theorem B1909007 : Blo 562809 1909007 := bstep (se 1 (by rfl) ⟨1431755, by rfl⟩ : syracuseStep 1909007 = 2863511) B2863511
theorem B565563 : Blo 562809 565563 := bstep (se 1 (by rfl) ⟨424172, by rfl⟩ : syracuseStep 565563 = 848345) B848345
theorem B3055961 : Blo 562809 3055961 := bstep (se 2 (by rfl) ⟨1145985, by rfl⟩ : syracuseStep 3055961 = 2291971) B2291971
theorem B565639 : Blo 562809 565639 := bstep (se 1 (by rfl) ⟨424229, by rfl⟩ : syracuseStep 565639 = 848459) B848459
theorem B565647 : Blo 562809 565647 := bstep (se 1 (by rfl) ⟨424235, by rfl⟩ : syracuseStep 565647 = 848471) B848471
theorem B3219857 : Blo 562809 3219857 := bstep (se 2 (by rfl) ⟨1207446, by rfl⟩ : syracuseStep 3219857 = 2414893) B2414893
theorem B2138521 : Blo 562809 2138521 := bstep (se 2 (by rfl) ⟨801945, by rfl⟩ : syracuseStep 2138521 = 1603891) B1603891
theorem B565691 : Blo 562809 565691 := bstep (se 1 (by rfl) ⟨424268, by rfl⟩ : syracuseStep 565691 = 848537) B848537
theorem B565767 : Blo 562809 565767 := bstep (se 1 (by rfl) ⟨424325, by rfl⟩ : syracuseStep 565767 = 848651) B848651
theorem B565775 : Blo 562809 565775 := bstep (se 1 (by rfl) ⟨424331, by rfl⟩ : syracuseStep 565775 = 848663) B848663
theorem B1909277 : Blo 562809 1909277 := bstep (se 3 (by rfl) ⟨357989, by rfl⟩ : syracuseStep 1909277 = 715979) B715979
theorem B565819 : Blo 562809 565819 := bstep (se 1 (by rfl) ⟨424364, by rfl⟩ : syracuseStep 565819 = 848729) B848729
theorem B565895 : Blo 562809 565895 := bstep (se 1 (by rfl) ⟨424421, by rfl⟩ : syracuseStep 565895 = 848843) B848843
theorem B565903 : Blo 562809 565903 := bstep (se 1 (by rfl) ⟨424427, by rfl⟩ : syracuseStep 565903 = 848855) B848855
theorem B565947 : Blo 562809 565947 := bstep (se 1 (by rfl) ⟨424460, by rfl⟩ : syracuseStep 565947 = 848921) B848921
theorem B2138825 : Blo 562809 2138825 := bstep (se 2 (by rfl) ⟨802059, by rfl⟩ : syracuseStep 2138825 = 1604119) B1604119
theorem B566023 : Blo 562809 566023 := bstep (se 1 (by rfl) ⟨424517, by rfl⟩ : syracuseStep 566023 = 849035) B849035
theorem B566031 : Blo 562809 566031 := bstep (se 1 (by rfl) ⟨424523, by rfl⟩ : syracuseStep 566031 = 849047) B849047
theorem B566075 : Blo 562809 566075 := bstep (se 1 (by rfl) ⟨424556, by rfl⟩ : syracuseStep 566075 = 849113) B849113
theorem B566151 : Blo 562809 566151 := bstep (se 1 (by rfl) ⟨424613, by rfl⟩ : syracuseStep 566151 = 849227) B849227
theorem B566159 : Blo 562809 566159 := bstep (se 1 (by rfl) ⟨424619, by rfl⟩ : syracuseStep 566159 = 849239) B849239
theorem B566203 : Blo 562809 566203 := bstep (se 1 (by rfl) ⟨424652, by rfl⟩ : syracuseStep 566203 = 849305) B849305
theorem B566279 : Blo 562809 566279 := bstep (se 1 (by rfl) ⟨424709, by rfl⟩ : syracuseStep 566279 = 849419) B849419
theorem B566287 : Blo 562809 566287 := bstep (se 1 (by rfl) ⟨424715, by rfl⟩ : syracuseStep 566287 = 849431) B849431
theorem B566331 : Blo 562809 566331 := bstep (se 1 (by rfl) ⟨424748, by rfl⟩ : syracuseStep 566331 = 849497) B849497
theorem B1713287 : Blo 562809 1713287 := bstep (se 1 (by rfl) ⟨1284965, by rfl⟩ : syracuseStep 1713287 = 2569931) B2569931
theorem B566407 : Blo 562809 566407 := bstep (se 1 (by rfl) ⟨424805, by rfl⟩ : syracuseStep 566407 = 849611) B849611
theorem B566415 : Blo 562809 566415 := bstep (se 1 (by rfl) ⟨424811, by rfl⟩ : syracuseStep 566415 = 849623) B849623
theorem B566459 : Blo 562809 566459 := bstep (se 1 (by rfl) ⟨424844, by rfl⟩ : syracuseStep 566459 = 849689) B849689
theorem B566535 : Blo 562809 566535 := bstep (se 1 (by rfl) ⟨424901, by rfl⟩ : syracuseStep 566535 = 849803) B849803
theorem B566543 : Blo 562809 566543 := bstep (se 1 (by rfl) ⟨424907, by rfl⟩ : syracuseStep 566543 = 849815) B849815
theorem B566587 : Blo 562809 566587 := bstep (se 1 (by rfl) ⟨424940, by rfl⟩ : syracuseStep 566587 = 849881) B849881
theorem B566663 : Blo 562809 566663 := bstep (se 1 (by rfl) ⟨424997, by rfl⟩ : syracuseStep 566663 = 849995) B849995
theorem B566671 : Blo 562809 566671 := bstep (se 1 (by rfl) ⟨425003, by rfl⟩ : syracuseStep 566671 = 850007) B850007
theorem B2860433 : Blo 562809 2860433 := bstep (se 2 (by rfl) ⟨1072662, by rfl⟩ : syracuseStep 2860433 = 2145325) B2145325
theorem B3220883 : Blo 562809 3220883 := bstep (se 1 (by rfl) ⟨2415662, by rfl⟩ : syracuseStep 3220883 = 4831325) B4831325
theorem B566715 : Blo 562809 566715 := bstep (se 1 (by rfl) ⟨425036, by rfl⟩ : syracuseStep 566715 = 850073) B850073
theorem B566791 : Blo 562809 566791 := bstep (se 1 (by rfl) ⟨425093, by rfl⟩ : syracuseStep 566791 = 850187) B850187
theorem B566799 : Blo 562809 566799 := bstep (se 1 (by rfl) ⟨425099, by rfl⟩ : syracuseStep 566799 = 850199) B850199
theorem B1353275 : Blo 562809 1353275 := bstep (se 1 (by rfl) ⟨1014956, by rfl⟩ : syracuseStep 1353275 = 2029913) B2029913
theorem B2139767 : Blo 562809 2139767 := bstep (se 1 (by rfl) ⟨1604825, by rfl⟩ : syracuseStep 2139767 = 3209651) B3209651
theorem B1812169 : Blo 562809 1812169 := bstep (se 2 (by rfl) ⟨679563, by rfl⟩ : syracuseStep 1812169 = 1359127) B1359127
theorem B26388341 : Blo 562809 26388341 := bstep (se 5 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 26388341 = 2473907) B2473907
theorem B927607 : Blo 562809 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B1910681 : Blo 562809 1910681 := bstep (se 2 (by rfl) ⟨716505, by rfl⟩ : syracuseStep 1910681 = 1433011) B1433011
theorem B12691403 : Blo 562809 12691403 := bstep (se 1 (by rfl) ⟨9518552, by rfl⟩ : syracuseStep 12691403 = 19037105) B19037105
theorem B2140739 : Blo 562809 2140739 := bstep (se 1 (by rfl) ⟨1605554, by rfl⟩ : syracuseStep 2140739 = 3211109) B3211109
theorem B1911383 : Blo 562809 1911383 := bstep (se 1 (by rfl) ⟨1433537, by rfl⟩ : syracuseStep 1911383 = 2867075) B2867075
theorem B633487 : Blo 562809 633487 := bstep (se 1 (by rfl) ⟨475115, by rfl⟩ : syracuseStep 633487 = 950231) B950231
theorem B3058469 : Blo 562809 3058469 := bstep (se 4 (by rfl) ⟨286731, by rfl⟩ : syracuseStep 3058469 = 573463) B573463
theorem B2173981 : Blo 562809 2173981 := bstep (se 3 (by rfl) ⟨407621, by rfl⟩ : syracuseStep 2173981 = 815243) B815243
theorem B1911869 : Blo 562809 1911869 := bstep (se 3 (by rfl) ⟨358475, by rfl⟩ : syracuseStep 1911869 = 716951) B716951
theorem B633991 : Blo 562809 633991 := bstep (se 1 (by rfl) ⟨475493, by rfl⟩ : syracuseStep 633991 = 950987) B950987
theorem B634171 : Blo 562809 634171 := bstep (se 1 (by rfl) ⟨475628, by rfl⟩ : syracuseStep 634171 = 951257) B951257
theorem B2862539 : Blo 562809 2862539 := bstep (se 1 (by rfl) ⟨2146904, by rfl⟩ : syracuseStep 2862539 = 4293809) B4293809
theorem B634639 : Blo 562809 634639 := bstep (se 1 (by rfl) ⟨475979, by rfl⟩ : syracuseStep 634639 = 951959) B951959
theorem B2862863 : Blo 562809 2862863 := bstep (se 1 (by rfl) ⟨2147147, by rfl⟩ : syracuseStep 2862863 = 4294295) B4294295
theorem B13709209 : Blo 562809 13709209 := bstep (se 2 (by rfl) ⟨5140953, by rfl⟩ : syracuseStep 13709209 = 10281907) B10281907
theorem B2142409 : Blo 562809 2142409 := bstep (se 2 (by rfl) ⟨803403, by rfl⟩ : syracuseStep 2142409 = 1606807) B1606807
theorem B635143 : Blo 562809 635143 := bstep (se 1 (by rfl) ⟨476357, by rfl⟩ : syracuseStep 635143 = 952715) B952715
theorem B1356043 : Blo 562809 1356043 := bstep (se 1 (by rfl) ⟨1017032, by rfl⟩ : syracuseStep 1356043 = 2034065) B2034065
theorem B3092795 : Blo 562809 3092795 := bstep (se 1 (by rfl) ⟨2319596, by rfl⟩ : syracuseStep 3092795 = 4639193) B4639193
theorem B635323 : Blo 562809 635323 := bstep (se 1 (by rfl) ⟨476492, by rfl⟩ : syracuseStep 635323 = 952985) B952985
theorem B4567823 : Blo 562809 4567823 := bstep (se 1 (by rfl) ⟨3425867, by rfl⟩ : syracuseStep 4567823 = 6851735) B6851735
theorem B2405153 : Blo 562809 2405153 := bstep (se 2 (by rfl) ⟨901932, by rfl⟩ : syracuseStep 2405153 = 1803865) B1803865
theorem B4829989 : Blo 562809 4829989 := bstep (se 4 (by rfl) ⟨452811, by rfl⟩ : syracuseStep 4829989 = 905623) B905623
theorem B1356659 : Blo 562809 1356659 := bstep (se 1 (by rfl) ⟨1017494, by rfl⟩ : syracuseStep 1356659 = 2034989) B2034989
theorem B635791 : Blo 562809 635791 := bstep (se 1 (by rfl) ⟨476843, by rfl⟩ : syracuseStep 635791 = 953687) B953687
theorem B5419979 : Blo 562809 5419979 := bstep (se 1 (by rfl) ⟨4064984, by rfl⟩ : syracuseStep 5419979 = 8129969) B8129969
theorem B1356859 : Blo 562809 1356859 := bstep (se 1 (by rfl) ⟨1017644, by rfl⟩ : syracuseStep 1356859 = 2035289) B2035289
theorem B2864321 : Blo 562809 2864321 := bstep (se 2 (by rfl) ⟨1074120, by rfl⟩ : syracuseStep 2864321 = 2148241) B2148241
theorem B603407 : Blo 562809 603407 := bstep (se 1 (by rfl) ⟨452555, by rfl⟩ : syracuseStep 603407 = 905111) B905111
theorem B636295 : Blo 562809 636295 := bstep (se 1 (by rfl) ⟨477221, by rfl⟩ : syracuseStep 636295 = 954443) B954443
theorem B4634003 : Blo 562809 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B636475 : Blo 562809 636475 := bstep (se 1 (by rfl) ⟨477356, by rfl⟩ : syracuseStep 636475 = 954713) B954713
theorem B2406145 : Blo 562809 2406145 := bstep (se 2 (by rfl) ⟨902304, by rfl⟩ : syracuseStep 2406145 = 1804609) B1804609
theorem B636943 : Blo 562809 636943 := bstep (se 1 (by rfl) ⟨477707, by rfl⟩ : syracuseStep 636943 = 955415) B955415
theorem B4569149 : Blo 562809 4569149 := bstep (se 3 (by rfl) ⟨856715, by rfl⟩ : syracuseStep 4569149 = 1713431) B1713431
theorem B2144627 : Blo 562809 2144627 := bstep (se 1 (by rfl) ⟨1608470, by rfl⟩ : syracuseStep 2144627 = 3216941) B3216941
theorem B3979655 : Blo 562809 3979655 := bstep (se 1 (by rfl) ⟨2984741, by rfl⟩ : syracuseStep 3979655 = 5969483) B5969483
theorem B604603 : Blo 562809 604603 := bstep (se 1 (by rfl) ⟨453452, by rfl⟩ : syracuseStep 604603 = 906905) B906905
theorem B2865617 : Blo 562809 2865617 := bstep (se 2 (by rfl) ⟨1074606, by rfl⟩ : syracuseStep 2865617 = 2149213) B2149213
theorem B637447 : Blo 562809 637447 := bstep (se 1 (by rfl) ⟨478085, by rfl⟩ : syracuseStep 637447 = 956171) B956171
theorem B637627 : Blo 562809 637627 := bstep (se 1 (by rfl) ⟨478220, by rfl⟩ : syracuseStep 637627 = 956441) B956441
theorem B4831973 : Blo 562809 4831973 := bstep (se 4 (by rfl) ⟨452997, by rfl⟩ : syracuseStep 4831973 = 905995) B905995
theorem B26000389 : Blo 562809 26000389 := bstep (se 4 (by rfl) ⟨2437536, by rfl⟩ : syracuseStep 26000389 = 4875073) B4875073
theorem B16333973 : Blo 562809 16333973 := bstep (se 6 (by rfl) ⟨382827, by rfl⟩ : syracuseStep 16333973 = 765655) B765655
theorem B1359119 : Blo 562809 1359119 := bstep (se 1 (by rfl) ⟨1019339, by rfl⟩ : syracuseStep 1359119 = 2038679) B2038679
theorem B1424699 : Blo 562809 1424699 := bstep (se 1 (by rfl) ⟨1068524, by rfl⟩ : syracuseStep 1424699 = 2137049) B2137049
theorem B802219 : Blo 562809 802219 := bstep (se 1 (by rfl) ⟨601664, by rfl⟩ : syracuseStep 802219 = 1203329) B1203329
theorem B3227147 : Blo 562809 3227147 := bstep (se 1 (by rfl) ⟨2420360, by rfl⟩ : syracuseStep 3227147 = 4840721) B4840721
theorem B1424911 : Blo 562809 1424911 := bstep (se 1 (by rfl) ⟨1068683, by rfl⟩ : syracuseStep 1424911 = 2137367) B2137367
theorem B868087 : Blo 562809 868087 := bstep (se 1 (by rfl) ⟨651065, by rfl⟩ : syracuseStep 868087 = 1302131) B1302131
theorem B1425185 : Blo 562809 1425185 := bstep (se 2 (by rfl) ⟨534444, by rfl⟩ : syracuseStep 1425185 = 1068889) B1068889
theorem B14434199 : Blo 562809 14434199 := bstep (se 1 (by rfl) ⟨10825649, by rfl⟩ : syracuseStep 14434199 = 21651299) B21651299
theorem B3096587 : Blo 562809 3096587 := bstep (se 1 (by rfl) ⟨2322440, by rfl⟩ : syracuseStep 3096587 = 4644881) B4644881
theorem B1523741 : Blo 562809 1523741 := bstep (se 3 (by rfl) ⟨285701, by rfl⟩ : syracuseStep 1523741 = 571403) B571403
theorem B2146769 : Blo 562809 2146769 := bstep (se 2 (by rfl) ⟨805038, by rfl⟩ : syracuseStep 2146769 = 1610077) B1610077
theorem B2867723 : Blo 562809 2867723 := bstep (se 1 (by rfl) ⟨2150792, by rfl⟩ : syracuseStep 2867723 = 4301585) B4301585
theorem B2867885 : Blo 562809 2867885 := bstep (se 3 (by rfl) ⟨537728, by rfl⟩ : syracuseStep 2867885 = 1075457) B1075457
theorem B1426187 : Blo 562809 1426187 := bstep (se 1 (by rfl) ⟨1069640, by rfl⟩ : syracuseStep 1426187 = 2139281) B2139281
theorem B2147087 : Blo 562809 2147087 := bstep (se 1 (by rfl) ⟨1610315, by rfl⟩ : syracuseStep 2147087 = 3220631) B3220631
theorem B3490781 : Blo 562809 3490781 := bstep (se 3 (by rfl) ⟨654521, by rfl⟩ : syracuseStep 3490781 = 1309043) B1309043
theorem B25183307 : Blo 562809 25183307 := bstep (se 1 (by rfl) ⟨18887480, by rfl⟩ : syracuseStep 25183307 = 37774961) B37774961
theorem B1361195 : Blo 562809 1361195 := bstep (se 1 (by rfl) ⟨1020896, by rfl⟩ : syracuseStep 1361195 = 2041793) B2041793
theorem B1426835 : Blo 562809 1426835 := bstep (se 1 (by rfl) ⟨1070126, by rfl⟩ : syracuseStep 1426835 = 2140253) B2140253
theorem B8144387 : Blo 562809 8144387 := bstep (se 1 (by rfl) ⟨6108290, by rfl⟩ : syracuseStep 8144387 = 12216581) B12216581
theorem B2705069 : Blo 562809 2705069 := bstep (se 3 (by rfl) ⟨507200, by rfl⟩ : syracuseStep 2705069 = 1014401) B1014401
theorem B54904499 : Blo 562809 54904499 := bstep (se 1 (by rfl) ⟨41178374, by rfl⟩ : syracuseStep 54904499 = 82356749) B82356749
theorem B1427129 : Blo 562809 1427129 := bstep (se 2 (by rfl) ⟨535173, by rfl⟩ : syracuseStep 1427129 = 1070347) B1070347
theorem B6113303 : Blo 562809 6113303 := bstep (se 1 (by rfl) ⟨4584977, by rfl⟩ : syracuseStep 6113303 = 9169955) B9169955
theorem B804907 : Blo 562809 804907 := bstep (se 1 (by rfl) ⟨603680, by rfl⟩ : syracuseStep 804907 = 1207361) B1207361
theorem B1394807 : Blo 562809 1394807 := bstep (se 1 (by rfl) ⟨1046105, by rfl⟩ : syracuseStep 1394807 = 2092211) B2092211
theorem B1525895 : Blo 562809 1525895 := bstep (se 1 (by rfl) ⟨1144421, by rfl⟩ : syracuseStep 1525895 = 2288843) B2288843
theorem B805135 : Blo 562809 805135 := bstep (se 1 (by rfl) ⟨603851, by rfl⟩ : syracuseStep 805135 = 1207703) B1207703
theorem B2705723 : Blo 562809 2705723 := bstep (se 1 (by rfl) ⟨2029292, by rfl⟩ : syracuseStep 2705723 = 4058585) B4058585
theorem B1427827 : Blo 562809 1427827 := bstep (se 1 (by rfl) ⟨1070870, by rfl⟩ : syracuseStep 1427827 = 2141741) B2141741
theorem B1427969 : Blo 562809 1427969 := bstep (se 2 (by rfl) ⟨535488, by rfl⟩ : syracuseStep 1427969 = 1070977) B1070977
theorem B1722995 : Blo 562809 1722995 := bstep (se 1 (by rfl) ⟨1292246, by rfl⟩ : syracuseStep 1722995 = 2584493) B2584493
theorem B805511 : Blo 562809 805511 := bstep (se 1 (by rfl) ⟨604133, by rfl⟩ : syracuseStep 805511 = 1208267) B1208267
theorem B903881 : Blo 562809 903881 := bstep (se 2 (by rfl) ⟨338955, by rfl⟩ : syracuseStep 903881 = 677911) B677911
theorem B871241 : Blo 562809 871241 := bstep (se 2 (by rfl) ⟨326715, by rfl⟩ : syracuseStep 871241 = 653431) B653431
theorem B1428425 : Blo 562809 1428425 := bstep (se 2 (by rfl) ⟨535659, by rfl⟩ : syracuseStep 1428425 = 1071319) B1071319
theorem B904393 : Blo 562809 904393 := bstep (se 2 (by rfl) ⟨339147, by rfl⟩ : syracuseStep 904393 = 678295) B678295
theorem B1428779 : Blo 562809 1428779 := bstep (se 1 (by rfl) ⟨1071584, by rfl⟩ : syracuseStep 1428779 = 2143169) B2143169
theorem B5787065 : Blo 562809 5787065 := bstep (se 2 (by rfl) ⟨2170149, by rfl⟩ : syracuseStep 5787065 = 4340299) B4340299
theorem B905003 : Blo 562809 905003 := bstep (se 1 (by rfl) ⟨678752, by rfl⟩ : syracuseStep 905003 = 1357505) B1357505
theorem B806969 : Blo 562809 806969 := bstep (se 2 (by rfl) ⟨302613, by rfl⟩ : syracuseStep 806969 = 605227) B605227
theorem B2150657 : Blo 562809 2150657 := bstep (se 2 (by rfl) ⟨806496, by rfl⟩ : syracuseStep 2150657 = 1612993) B1612993
theorem B1429771 : Blo 562809 1429771 := bstep (se 1 (by rfl) ⟨1072328, by rfl⟩ : syracuseStep 1429771 = 2144657) B2144657
theorem B2150671 : Blo 562809 2150671 := bstep (se 1 (by rfl) ⟨1613003, by rfl⟩ : syracuseStep 2150671 = 3226007) B3226007
theorem B5427587 : Blo 562809 5427587 := bstep (se 1 (by rfl) ⟨4070690, by rfl⟩ : syracuseStep 5427587 = 8141381) B8141381
theorem B1429913 : Blo 562809 1429913 := bstep (se 2 (by rfl) ⟨536217, by rfl⟩ : syracuseStep 1429913 = 1072435) B1072435
theorem B1430075 : Blo 562809 1430075 := bstep (se 1 (by rfl) ⟨1072556, by rfl⟩ : syracuseStep 1430075 = 2145113) B2145113
theorem B3265085 : Blo 562809 3265085 := bstep (se 3 (by rfl) ⟨612203, by rfl⟩ : syracuseStep 3265085 = 1224407) B1224407
theorem B1266551 : Blo 562809 1266551 := bstep (se 1 (by rfl) ⟨949913, by rfl⟩ : syracuseStep 1266551 = 1899827) B1899827
theorem B1430419 : Blo 562809 1430419 := bstep (se 1 (by rfl) ⟨1072814, by rfl⟩ : syracuseStep 1430419 = 2145629) B2145629
theorem B1430561 : Blo 562809 1430561 := bstep (se 2 (by rfl) ⟨536460, by rfl⟩ : syracuseStep 1430561 = 1072921) B1072921
theorem B1266731 : Blo 562809 1266731 := bstep (se 1 (by rfl) ⟨950048, by rfl⟩ : syracuseStep 1266731 = 1900097) B1900097
theorem B4281659 : Blo 562809 4281659 := bstep (se 1 (by rfl) ⟨3211244, by rfl⟩ : syracuseStep 4281659 = 6422489) B6422489
theorem B1267091 : Blo 562809 1267091 := bstep (se 1 (by rfl) ⟨950318, by rfl⟩ : syracuseStep 1267091 = 1900637) B1900637
theorem B1267145 : Blo 562809 1267145 := bstep (se 2 (by rfl) ⟨475179, by rfl⟩ : syracuseStep 1267145 = 950359) B950359
theorem B2151947 : Blo 562809 2151947 := bstep (se 1 (by rfl) ⟨1613960, by rfl⟩ : syracuseStep 2151947 = 3227921) B3227921
theorem B1070651 : Blo 562809 1070651 := bstep (se 1 (by rfl) ⟨802988, by rfl⟩ : syracuseStep 1070651 = 1605977) B1605977
theorem B1431553 : Blo 562809 1431553 := bstep (se 2 (by rfl) ⟨536832, by rfl⟩ : syracuseStep 1431553 = 1073665) B1073665
theorem B1071137 : Blo 562809 1071137 := bstep (se 2 (by rfl) ⟨401676, by rfl⟩ : syracuseStep 1071137 = 803353) B803353
theorem B1267847 : Blo 562809 1267847 := bstep (se 1 (by rfl) ⟨950885, by rfl⟩ : syracuseStep 1267847 = 1901771) B1901771
theorem B645383 : Blo 562809 645383 := bstep (se 1 (by rfl) ⟨484037, by rfl⟩ : syracuseStep 645383 = 968075) B968075
theorem B1268027 : Blo 562809 1268027 := bstep (se 1 (by rfl) ⟨951020, by rfl⟩ : syracuseStep 1268027 = 1902041) B1902041
theorem B2709875 : Blo 562809 2709875 := bstep (se 1 (by rfl) ⟨2032406, by rfl⟩ : syracuseStep 2709875 = 4064813) B4064813
theorem B1268153 : Blo 562809 1268153 := bstep (se 2 (by rfl) ⟨475557, by rfl⟩ : syracuseStep 1268153 = 951115) B951115
theorem B2710027 : Blo 562809 2710027 := bstep (se 1 (by rfl) ⟨2032520, by rfl⟩ : syracuseStep 2710027 = 4065041) B4065041
theorem B2710103 : Blo 562809 2710103 := bstep (se 1 (by rfl) ⟨2032577, by rfl⟩ : syracuseStep 2710103 = 4065155) B4065155
theorem B1432151 : Blo 562809 1432151 := bstep (se 1 (by rfl) ⟨1074113, by rfl⟩ : syracuseStep 1432151 = 2148227) B2148227
theorem B1268495 : Blo 562809 1268495 := bstep (se 1 (by rfl) ⟨951371, by rfl⟩ : syracuseStep 1268495 = 1902743) B1902743
theorem B1268513 : Blo 562809 1268513 := bstep (se 2 (by rfl) ⟨475692, by rfl⟩ : syracuseStep 1268513 = 951385) B951385
theorem B1202987 : Blo 562809 1202987 := bstep (se 1 (by rfl) ⟨902240, by rfl⟩ : syracuseStep 1202987 = 1804481) B1804481
theorem B1432363 : Blo 562809 1432363 := bstep (se 1 (by rfl) ⟨1074272, by rfl⟩ : syracuseStep 1432363 = 2148545) B2148545
theorem B1432505 : Blo 562809 1432505 := bstep (se 2 (by rfl) ⟨537189, by rfl⟩ : syracuseStep 1432505 = 1074379) B1074379
theorem B1268855 : Blo 562809 1268855 := bstep (se 1 (by rfl) ⟨951641, by rfl⟩ : syracuseStep 1268855 = 1903283) B1903283
theorem B1269035 : Blo 562809 1269035 := bstep (se 1 (by rfl) ⟨951776, by rfl⟩ : syracuseStep 1269035 = 1903553) B1903553
theorem B1269395 : Blo 562809 1269395 := bstep (se 1 (by rfl) ⟨952046, by rfl⟩ : syracuseStep 1269395 = 1904093) B1904093
theorem B1269449 : Blo 562809 1269449 := bstep (se 2 (by rfl) ⟨476043, by rfl⟩ : syracuseStep 1269449 = 952087) B952087
theorem B4349747 : Blo 562809 4349747 := bstep (se 1 (by rfl) ⟨3262310, by rfl⟩ : syracuseStep 4349747 = 6524621) B6524621
theorem B2416499 : Blo 562809 2416499 := bstep (se 1 (by rfl) ⟨1812374, by rfl⟩ : syracuseStep 2416499 = 3624749) B3624749
theorem B712567 : Blo 562809 712567 := bstep (se 1 (by rfl) ⟨534425, by rfl⟩ : syracuseStep 712567 = 1068851) B1068851
theorem B1433497 : Blo 562809 1433497 := bstep (se 2 (by rfl) ⟨537561, by rfl⟩ : syracuseStep 1433497 = 1075123) B1075123
theorem B1073081 : Blo 562809 1073081 := bstep (se 2 (by rfl) ⟨402405, by rfl⟩ : syracuseStep 1073081 = 804811) B804811
theorem B1302571 : Blo 562809 1302571 := bstep (se 1 (by rfl) ⟨976928, by rfl⟩ : syracuseStep 1302571 = 1953857) B1953857
theorem B1433659 : Blo 562809 1433659 := bstep (se 1 (by rfl) ⟨1075244, by rfl⟩ : syracuseStep 1433659 = 2150489) B2150489
theorem B712891 : Blo 562809 712891 := bstep (se 1 (by rfl) ⟨534668, by rfl⟩ : syracuseStep 712891 = 1069337) B1069337
theorem B2416841 : Blo 562809 2416841 := bstep (se 2 (by rfl) ⟨906315, by rfl⟩ : syracuseStep 2416841 = 1812631) B1812631
theorem B1433801 : Blo 562809 1433801 := bstep (se 2 (by rfl) ⟨537675, by rfl⟩ : syracuseStep 1433801 = 1075351) B1075351
theorem B1270151 : Blo 562809 1270151 := bstep (se 1 (by rfl) ⟨952613, by rfl⟩ : syracuseStep 1270151 = 1905227) B1905227
theorem B1204627 : Blo 562809 1204627 := bstep (se 1 (by rfl) ⟨903470, by rfl⟩ : syracuseStep 1204627 = 1806941) B1806941
theorem B844217 : Blo 562809 844217 := bstep (se 2 (by rfl) ⟨316581, by rfl⟩ : syracuseStep 844217 = 633163) B633163
theorem B3858947 : Blo 562809 3858947 := bstep (se 1 (by rfl) ⟨2894210, by rfl⟩ : syracuseStep 3858947 = 5788421) B5788421
theorem B844295 : Blo 562809 844295 := bstep (se 1 (by rfl) ⟨633221, by rfl⟩ : syracuseStep 844295 = 1266443) B1266443
theorem B1434145 : Blo 562809 1434145 := bstep (se 2 (by rfl) ⟨537804, by rfl⟩ : syracuseStep 1434145 = 1075609) B1075609
theorem B844331 : Blo 562809 844331 := bstep (se 1 (by rfl) ⟨633248, by rfl⟩ : syracuseStep 844331 = 1266497) B1266497
theorem B1270331 : Blo 562809 1270331 := bstep (se 1 (by rfl) ⟨952748, by rfl⟩ : syracuseStep 1270331 = 1905497) B1905497
theorem B844361 : Blo 562809 844361 := bstep (se 2 (by rfl) ⟨316635, by rfl⟩ : syracuseStep 844361 = 633271) B633271
theorem B713387 : Blo 562809 713387 := bstep (se 1 (by rfl) ⟨535040, by rfl⟩ : syracuseStep 713387 = 1070081) B1070081
theorem B1270457 : Blo 562809 1270457 := bstep (se 2 (by rfl) ⟨476421, by rfl⟩ : syracuseStep 1270457 = 952843) B952843
theorem B844475 : Blo 562809 844475 := bstep (se 1 (by rfl) ⟨633356, by rfl⟩ : syracuseStep 844475 = 1266713) B1266713
theorem B2712257 : Blo 562809 2712257 := bstep (se 2 (by rfl) ⟨1017096, by rfl⟩ : syracuseStep 2712257 = 2034193) B2034193
theorem B844535 : Blo 562809 844535 := bstep (se 1 (by rfl) ⟨633401, by rfl⟩ : syracuseStep 844535 = 1266803) B1266803
theorem B844559 : Blo 562809 844559 := bstep (se 1 (by rfl) ⟨633419, by rfl⟩ : syracuseStep 844559 = 1266839) B1266839
theorem B844601 : Blo 562809 844601 := bstep (se 2 (by rfl) ⟨316725, by rfl⟩ : syracuseStep 844601 = 633451) B633451
theorem B844679 : Blo 562809 844679 := bstep (se 1 (by rfl) ⟨633509, by rfl⟩ : syracuseStep 844679 = 1267019) B1267019
theorem B844715 : Blo 562809 844715 := bstep (se 1 (by rfl) ⟨633536, by rfl⟩ : syracuseStep 844715 = 1267073) B1267073
theorem B844745 : Blo 562809 844745 := bstep (se 2 (by rfl) ⟨316779, by rfl⟩ : syracuseStep 844745 = 633559) B633559
theorem B1270799 : Blo 562809 1270799 := bstep (se 1 (by rfl) ⟨953099, by rfl⟩ : syracuseStep 1270799 = 1906199) B1906199
theorem B1270817 : Blo 562809 1270817 := bstep (se 2 (by rfl) ⟨476556, by rfl⟩ : syracuseStep 1270817 = 953113) B953113
theorem B844859 : Blo 562809 844859 := bstep (se 1 (by rfl) ⟨633644, by rfl⟩ : syracuseStep 844859 = 1267289) B1267289
theorem B1074235 : Blo 562809 1074235 := bstep (se 1 (by rfl) ⟨805676, by rfl⟩ : syracuseStep 1074235 = 1611353) B1611353
theorem B844919 : Blo 562809 844919 := bstep (se 1 (by rfl) ⟨633689, by rfl⟩ : syracuseStep 844919 = 1267379) B1267379
theorem B713863 : Blo 562809 713863 := bstep (se 1 (by rfl) ⟨535397, by rfl⟩ : syracuseStep 713863 = 1070795) B1070795
theorem B844943 : Blo 562809 844943 := bstep (se 1 (by rfl) ⟨633707, by rfl⟩ : syracuseStep 844943 = 1267415) B1267415
theorem B844985 : Blo 562809 844985 := bstep (se 2 (by rfl) ⟨316869, by rfl⟩ : syracuseStep 844985 = 633739) B633739
theorem B845063 : Blo 562809 845063 := bstep (se 1 (by rfl) ⟨633797, by rfl⟩ : syracuseStep 845063 = 1267595) B1267595
theorem B845099 : Blo 562809 845099 := bstep (se 1 (by rfl) ⟨633824, by rfl⟩ : syracuseStep 845099 = 1267649) B1267649
theorem B845129 : Blo 562809 845129 := bstep (se 2 (by rfl) ⟨316923, by rfl⟩ : syracuseStep 845129 = 633847) B633847
theorem B1271159 : Blo 562809 1271159 := bstep (se 1 (by rfl) ⟨953369, by rfl⟩ : syracuseStep 1271159 = 1906739) B1906739
theorem B845243 : Blo 562809 845243 := bstep (se 1 (by rfl) ⟨633932, by rfl⟩ : syracuseStep 845243 = 1267865) B1267865
theorem B845303 : Blo 562809 845303 := bstep (se 1 (by rfl) ⟨633977, by rfl⟩ : syracuseStep 845303 = 1267955) B1267955
theorem B845327 : Blo 562809 845327 := bstep (se 1 (by rfl) ⟨633995, by rfl⟩ : syracuseStep 845327 = 1267991) B1267991
theorem B1074721 : Blo 562809 1074721 := bstep (se 2 (by rfl) ⟨403020, by rfl⟩ : syracuseStep 1074721 = 806041) B806041
theorem B1271339 : Blo 562809 1271339 := bstep (se 1 (by rfl) ⟨953504, by rfl⟩ : syracuseStep 1271339 = 1907009) B1907009
theorem B6121003 : Blo 562809 6121003 := bstep (se 1 (by rfl) ⟨4590752, by rfl⟩ : syracuseStep 6121003 = 9181505) B9181505
theorem B845369 : Blo 562809 845369 := bstep (se 2 (by rfl) ⟨317013, by rfl⟩ : syracuseStep 845369 = 634027) B634027
theorem B714359 : Blo 562809 714359 := bstep (se 1 (by rfl) ⟨535769, by rfl⟩ : syracuseStep 714359 = 1071539) B1071539
theorem B845447 : Blo 562809 845447 := bstep (se 1 (by rfl) ⟨634085, by rfl⟩ : syracuseStep 845447 = 1268171) B1268171
theorem B845483 : Blo 562809 845483 := bstep (se 1 (by rfl) ⟨634112, by rfl⟩ : syracuseStep 845483 = 1268225) B1268225
theorem B845513 : Blo 562809 845513 := bstep (se 2 (by rfl) ⟨317067, by rfl⟩ : syracuseStep 845513 = 634135) B634135
theorem B714511 : Blo 562809 714511 := bstep (se 1 (by rfl) ⟨535883, by rfl⟩ : syracuseStep 714511 = 1071767) B1071767
theorem B3860261 : Blo 562809 3860261 := bstep (se 4 (by rfl) ⟨361899, by rfl⟩ : syracuseStep 3860261 = 723799) B723799
theorem B4351781 : Blo 562809 4351781 := bstep (se 4 (by rfl) ⟨407979, by rfl⟩ : syracuseStep 4351781 = 815959) B815959
theorem B3630899 : Blo 562809 3630899 := bstep (se 1 (by rfl) ⟨2723174, by rfl⟩ : syracuseStep 3630899 = 5446349) B5446349
theorem B845627 : Blo 562809 845627 := bstep (se 1 (by rfl) ⟨634220, by rfl⟩ : syracuseStep 845627 = 1268441) B1268441
theorem B845687 : Blo 562809 845687 := bstep (se 1 (by rfl) ⟨634265, by rfl⟩ : syracuseStep 845687 = 1268531) B1268531
theorem B845711 : Blo 562809 845711 := bstep (se 1 (by rfl) ⟨634283, by rfl⟩ : syracuseStep 845711 = 1268567) B1268567
theorem B1271699 : Blo 562809 1271699 := bstep (se 1 (by rfl) ⟨953774, by rfl⟩ : syracuseStep 1271699 = 1907549) B1907549
theorem B845753 : Blo 562809 845753 := bstep (se 2 (by rfl) ⟨317157, by rfl⟩ : syracuseStep 845753 = 634315) B634315
theorem B714683 : Blo 562809 714683 := bstep (se 1 (by rfl) ⟨536012, by rfl⟩ : syracuseStep 714683 = 1072025) B1072025
theorem B1271753 : Blo 562809 1271753 := bstep (se 2 (by rfl) ⟨476907, by rfl⟩ : syracuseStep 1271753 = 953815) B953815
theorem B845831 : Blo 562809 845831 := bstep (se 1 (by rfl) ⟨634373, by rfl⟩ : syracuseStep 845831 = 1268747) B1268747
theorem B845867 : Blo 562809 845867 := bstep (se 1 (by rfl) ⟨634400, by rfl⟩ : syracuseStep 845867 = 1268801) B1268801
theorem B845897 : Blo 562809 845897 := bstep (se 2 (by rfl) ⟨317211, by rfl⟩ : syracuseStep 845897 = 634423) B634423
theorem B846011 : Blo 562809 846011 := bstep (se 1 (by rfl) ⟨634508, by rfl⟩ : syracuseStep 846011 = 1269017) B1269017
theorem B846071 : Blo 562809 846071 := bstep (se 1 (by rfl) ⟨634553, by rfl⟩ : syracuseStep 846071 = 1269107) B1269107
theorem B846095 : Blo 562809 846095 := bstep (se 1 (by rfl) ⟨634571, by rfl⟩ : syracuseStep 846095 = 1269143) B1269143
theorem B2418959 : Blo 562809 2418959 := bstep (se 1 (by rfl) ⟨1814219, by rfl⟩ : syracuseStep 2418959 = 3628439) B3628439
theorem B6416657 : Blo 562809 6416657 := bstep (se 2 (by rfl) ⟨2406246, by rfl⟩ : syracuseStep 6416657 = 4812493) B4812493
theorem B846137 : Blo 562809 846137 := bstep (se 2 (by rfl) ⟨317301, by rfl⟩ : syracuseStep 846137 = 634603) B634603
theorem B846215 : Blo 562809 846215 := bstep (se 1 (by rfl) ⟨634661, by rfl⟩ : syracuseStep 846215 = 1269323) B1269323
theorem B846251 : Blo 562809 846251 := bstep (se 1 (by rfl) ⟨634688, by rfl⟩ : syracuseStep 846251 = 1269377) B1269377
theorem B846281 : Blo 562809 846281 := bstep (se 2 (by rfl) ⟨317355, by rfl⟩ : syracuseStep 846281 = 634711) B634711
theorem B813559 : Blo 562809 813559 := bstep (se 1 (by rfl) ⟨610169, by rfl⟩ : syracuseStep 813559 = 1220339) B1220339
theorem B4287005 : Blo 562809 4287005 := bstep (se 3 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 4287005 = 1607627) B1607627
theorem B846395 : Blo 562809 846395 := bstep (se 1 (by rfl) ⟨634796, by rfl⟩ : syracuseStep 846395 = 1269593) B1269593
theorem B2419267 : Blo 562809 2419267 := bstep (se 1 (by rfl) ⟨1814450, by rfl⟩ : syracuseStep 2419267 = 3628901) B3628901
theorem B846455 : Blo 562809 846455 := bstep (se 1 (by rfl) ⟨634841, by rfl⟩ : syracuseStep 846455 = 1269683) B1269683
theorem B1272455 : Blo 562809 1272455 := bstep (se 1 (by rfl) ⟨954341, by rfl⟩ : syracuseStep 1272455 = 1908683) B1908683
theorem B846479 : Blo 562809 846479 := bstep (se 1 (by rfl) ⟨634859, by rfl⟩ : syracuseStep 846479 = 1269719) B1269719
theorem B846521 : Blo 562809 846521 := bstep (se 2 (by rfl) ⟨317445, by rfl⟩ : syracuseStep 846521 = 634891) B634891
theorem B1075913 : Blo 562809 1075913 := bstep (se 2 (by rfl) ⟨403467, by rfl⟩ : syracuseStep 1075913 = 806935) B806935
theorem B846599 : Blo 562809 846599 := bstep (se 1 (by rfl) ⟨634949, by rfl⟩ : syracuseStep 846599 = 1269899) B1269899
theorem B5434127 : Blo 562809 5434127 := bstep (se 1 (by rfl) ⟨4075595, by rfl⟩ : syracuseStep 5434127 = 8151191) B8151191
theorem B846635 : Blo 562809 846635 := bstep (se 1 (by rfl) ⟨634976, by rfl⟩ : syracuseStep 846635 = 1269953) B1269953
theorem B1272635 : Blo 562809 1272635 := bstep (se 1 (by rfl) ⟨954476, by rfl⟩ : syracuseStep 1272635 = 1908953) B1908953
theorem B846665 : Blo 562809 846665 := bstep (se 2 (by rfl) ⟨317499, by rfl⟩ : syracuseStep 846665 = 634999) B634999
theorem B9300851 : Blo 562809 9300851 := bstep (se 1 (by rfl) ⟨6975638, by rfl⟩ : syracuseStep 9300851 = 13951277) B13951277
theorem B715655 : Blo 562809 715655 := bstep (se 1 (by rfl) ⟨536741, by rfl⟩ : syracuseStep 715655 = 1073483) B1073483
theorem B1272761 : Blo 562809 1272761 := bstep (se 2 (by rfl) ⟨477285, by rfl⟩ : syracuseStep 1272761 = 954571) B954571
theorem B846779 : Blo 562809 846779 := bstep (se 1 (by rfl) ⟨635084, by rfl⟩ : syracuseStep 846779 = 1270169) B1270169
theorem B1141705 : Blo 562809 1141705 := bstep (se 2 (by rfl) ⟨428139, by rfl⟩ : syracuseStep 1141705 = 856279) B856279
theorem B846839 : Blo 562809 846839 := bstep (se 1 (by rfl) ⟨635129, by rfl⟩ : syracuseStep 846839 = 1270259) B1270259
theorem B846863 : Blo 562809 846863 := bstep (se 1 (by rfl) ⟨635147, by rfl⟩ : syracuseStep 846863 = 1270295) B1270295
theorem B846905 : Blo 562809 846905 := bstep (se 2 (by rfl) ⟨317589, by rfl⟩ : syracuseStep 846905 = 635179) B635179
theorem B1240183 : Blo 562809 1240183 := bstep (se 1 (by rfl) ⟨930137, by rfl⟩ : syracuseStep 1240183 = 1860275) B1860275
theorem B846983 : Blo 562809 846983 := bstep (se 1 (by rfl) ⟨635237, by rfl⟩ : syracuseStep 846983 = 1270475) B1270475
theorem B847019 : Blo 562809 847019 := bstep (se 1 (by rfl) ⟨635264, by rfl⟩ : syracuseStep 847019 = 1270529) B1270529
theorem B847049 : Blo 562809 847049 := bstep (se 2 (by rfl) ⟨317643, by rfl⟩ : syracuseStep 847049 = 635287) B635287
theorem B1273103 : Blo 562809 1273103 := bstep (se 1 (by rfl) ⟨954827, by rfl⟩ : syracuseStep 1273103 = 1909655) B1909655
theorem B1273121 : Blo 562809 1273121 := bstep (se 2 (by rfl) ⟨477420, by rfl⟩ : syracuseStep 1273121 = 954841) B954841
theorem B847163 : Blo 562809 847163 := bstep (se 1 (by rfl) ⟨635372, by rfl⟩ : syracuseStep 847163 = 1270745) B1270745
theorem B847223 : Blo 562809 847223 := bstep (se 1 (by rfl) ⟨635417, by rfl⟩ : syracuseStep 847223 = 1270835) B1270835
theorem B847247 : Blo 562809 847247 := bstep (se 1 (by rfl) ⟨635435, by rfl⟩ : syracuseStep 847247 = 1270871) B1270871
theorem B847289 : Blo 562809 847289 := bstep (se 2 (by rfl) ⟨317733, by rfl⟩ : syracuseStep 847289 = 635467) B635467
theorem B27553283 : Blo 562809 27553283 := bstep (se 1 (by rfl) ⟨20664962, by rfl⟩ : syracuseStep 27553283 = 41329925) B41329925
theorem B847367 : Blo 562809 847367 := bstep (se 1 (by rfl) ⟨635525, by rfl⟩ : syracuseStep 847367 = 1271051) B1271051
theorem B716303 : Blo 562809 716303 := bstep (se 1 (by rfl) ⟨537227, by rfl⟩ : syracuseStep 716303 = 1074455) B1074455
theorem B847403 : Blo 562809 847403 := bstep (se 1 (by rfl) ⟨635552, by rfl⟩ : syracuseStep 847403 = 1271105) B1271105
theorem B847433 : Blo 562809 847433 := bstep (se 2 (by rfl) ⟨317787, by rfl⟩ : syracuseStep 847433 = 635575) B635575
theorem B1273463 : Blo 562809 1273463 := bstep (se 1 (by rfl) ⟨955097, by rfl⟩ : syracuseStep 1273463 = 1910195) B1910195
theorem B847547 : Blo 562809 847547 := bstep (se 1 (by rfl) ⟨635660, by rfl⟩ : syracuseStep 847547 = 1271321) B1271321
theorem B847607 : Blo 562809 847607 := bstep (se 1 (by rfl) ⟨635705, by rfl⟩ : syracuseStep 847607 = 1271411) B1271411
theorem B847631 : Blo 562809 847631 := bstep (se 1 (by rfl) ⟨635723, by rfl⟩ : syracuseStep 847631 = 1271447) B1271447
theorem B1273643 : Blo 562809 1273643 := bstep (se 1 (by rfl) ⟨955232, by rfl⟩ : syracuseStep 1273643 = 1910465) B1910465
theorem B847673 : Blo 562809 847673 := bstep (se 2 (by rfl) ⟨317877, by rfl⟩ : syracuseStep 847673 = 635755) B635755
theorem B847751 : Blo 562809 847751 := bstep (se 1 (by rfl) ⟨635813, by rfl⟩ : syracuseStep 847751 = 1271627) B1271627
theorem B847787 : Blo 562809 847787 := bstep (se 1 (by rfl) ⟨635840, by rfl⟩ : syracuseStep 847787 = 1271681) B1271681
theorem B847817 : Blo 562809 847817 := bstep (se 2 (by rfl) ⟨317931, by rfl⟩ : syracuseStep 847817 = 635863) B635863
theorem B847931 : Blo 562809 847931 := bstep (se 1 (by rfl) ⟨635948, by rfl⟩ : syracuseStep 847931 = 1271897) B1271897
theorem B1634365 : Blo 562809 1634365 := bstep (se 3 (by rfl) ⟨306443, by rfl⟩ : syracuseStep 1634365 = 612887) B612887
theorem B3207235 : Blo 562809 3207235 := bstep (se 1 (by rfl) ⟨2405426, by rfl⟩ : syracuseStep 3207235 = 4810853) B4810853
theorem B847991 : Blo 562809 847991 := bstep (se 1 (by rfl) ⟨635993, by rfl⟩ : syracuseStep 847991 = 1271987) B1271987
theorem B848015 : Blo 562809 848015 := bstep (se 1 (by rfl) ⟨636011, by rfl⟩ : syracuseStep 848015 = 1272023) B1272023
theorem B1274003 : Blo 562809 1274003 := bstep (se 1 (by rfl) ⟨955502, by rfl⟩ : syracuseStep 1274003 = 1911005) B1911005
theorem B848057 : Blo 562809 848057 := bstep (se 2 (by rfl) ⟨318021, by rfl⟩ : syracuseStep 848057 = 636043) B636043
theorem B1274057 : Blo 562809 1274057 := bstep (se 2 (by rfl) ⟨477771, by rfl⟩ : syracuseStep 1274057 = 955543) B955543
theorem B848135 : Blo 562809 848135 := bstep (se 1 (by rfl) ⟨636101, by rfl⟩ : syracuseStep 848135 = 1272203) B1272203
theorem B848171 : Blo 562809 848171 := bstep (se 1 (by rfl) ⟨636128, by rfl⟩ : syracuseStep 848171 = 1272257) B1272257
theorem B848201 : Blo 562809 848201 := bstep (se 2 (by rfl) ⟨318075, by rfl⟩ : syracuseStep 848201 = 636151) B636151
theorem B848315 : Blo 562809 848315 := bstep (se 1 (by rfl) ⟨636236, by rfl⟩ : syracuseStep 848315 = 1272473) B1272473
theorem B848375 : Blo 562809 848375 := bstep (se 1 (by rfl) ⟨636281, by rfl⟩ : syracuseStep 848375 = 1272563) B1272563
theorem B848399 : Blo 562809 848399 := bstep (se 1 (by rfl) ⟨636299, by rfl⟩ : syracuseStep 848399 = 1272599) B1272599
theorem B848441 : Blo 562809 848441 := bstep (se 2 (by rfl) ⟨318165, by rfl⟩ : syracuseStep 848441 = 636331) B636331
theorem B848519 : Blo 562809 848519 := bstep (se 1 (by rfl) ⟨636389, by rfl⟩ : syracuseStep 848519 = 1272779) B1272779
theorem B848555 : Blo 562809 848555 := bstep (se 1 (by rfl) ⟨636416, by rfl⟩ : syracuseStep 848555 = 1272833) B1272833
theorem B848585 : Blo 562809 848585 := bstep (se 2 (by rfl) ⟨318219, by rfl⟩ : syracuseStep 848585 = 636439) B636439
theorem B14512931 : Blo 562809 14512931 := bstep (se 1 (by rfl) ⟨10884698, by rfl⟩ : syracuseStep 14512931 = 21769397) B21769397
theorem B848699 : Blo 562809 848699 := bstep (se 1 (by rfl) ⟨636524, by rfl⟩ : syracuseStep 848699 = 1273049) B1273049
theorem B848759 : Blo 562809 848759 := bstep (se 1 (by rfl) ⟨636569, by rfl⟩ : syracuseStep 848759 = 1273139) B1273139
theorem B1274759 : Blo 562809 1274759 := bstep (se 1 (by rfl) ⟨956069, by rfl⟩ : syracuseStep 1274759 = 1912139) B1912139
theorem B848783 : Blo 562809 848783 := bstep (se 1 (by rfl) ⟨636587, by rfl⟩ : syracuseStep 848783 = 1273175) B1273175
theorem B3044243 : Blo 562809 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B848825 : Blo 562809 848825 := bstep (se 2 (by rfl) ⟨318309, by rfl⟩ : syracuseStep 848825 = 636619) B636619
theorem B848903 : Blo 562809 848903 := bstep (se 1 (by rfl) ⟨636677, by rfl⟩ : syracuseStep 848903 = 1273355) B1273355
theorem B1209377 : Blo 562809 1209377 := bstep (se 2 (by rfl) ⟨453516, by rfl⟩ : syracuseStep 1209377 = 907033) B907033
theorem B848939 : Blo 562809 848939 := bstep (se 1 (by rfl) ⟨636704, by rfl⟩ : syracuseStep 848939 = 1273409) B1273409
theorem B1274939 : Blo 562809 1274939 := bstep (se 1 (by rfl) ⟨956204, by rfl⟩ : syracuseStep 1274939 = 1912409) B1912409
theorem B848969 : Blo 562809 848969 := bstep (se 2 (by rfl) ⟨318363, by rfl⟩ : syracuseStep 848969 = 636727) B636727
theorem B6419573 : Blo 562809 6419573 := bstep (se 5 (by rfl) ⟨300917, by rfl⟩ : syracuseStep 6419573 = 601835) B601835
theorem B1275065 : Blo 562809 1275065 := bstep (se 2 (by rfl) ⟨478149, by rfl⟩ : syracuseStep 1275065 = 956299) B956299
theorem B849083 : Blo 562809 849083 := bstep (se 1 (by rfl) ⟨636812, by rfl⟩ : syracuseStep 849083 = 1273625) B1273625
theorem B849143 : Blo 562809 849143 := bstep (se 1 (by rfl) ⟨636857, by rfl⟩ : syracuseStep 849143 = 1273715) B1273715
theorem B849167 : Blo 562809 849167 := bstep (se 1 (by rfl) ⟨636875, by rfl⟩ : syracuseStep 849167 = 1273751) B1273751
theorem B849209 : Blo 562809 849209 := bstep (se 2 (by rfl) ⟨318453, by rfl⟩ : syracuseStep 849209 = 636907) B636907
theorem B1602935 : Blo 562809 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B849287 : Blo 562809 849287 := bstep (se 1 (by rfl) ⟨636965, by rfl⟩ : syracuseStep 849287 = 1273931) B1273931
theorem B849323 : Blo 562809 849323 := bstep (se 1 (by rfl) ⟨636992, by rfl⟩ : syracuseStep 849323 = 1273985) B1273985
theorem B849353 : Blo 562809 849353 := bstep (se 2 (by rfl) ⟨318507, by rfl⟩ : syracuseStep 849353 = 637015) B637015
theorem B849467 : Blo 562809 849467 := bstep (se 1 (by rfl) ⟨637100, by rfl⟩ : syracuseStep 849467 = 1274201) B1274201
theorem B849527 : Blo 562809 849527 := bstep (se 1 (by rfl) ⟨637145, by rfl⟩ : syracuseStep 849527 = 1274291) B1274291
theorem B849551 : Blo 562809 849551 := bstep (se 1 (by rfl) ⟨637163, by rfl⟩ : syracuseStep 849551 = 1274327) B1274327
theorem B849593 : Blo 562809 849593 := bstep (se 2 (by rfl) ⟨318597, by rfl⟩ : syracuseStep 849593 = 637195) B637195
theorem B849671 : Blo 562809 849671 := bstep (se 1 (by rfl) ⟨637253, by rfl⟩ : syracuseStep 849671 = 1274507) B1274507
theorem B849707 : Blo 562809 849707 := bstep (se 1 (by rfl) ⟨637280, by rfl⟩ : syracuseStep 849707 = 1274561) B1274561
theorem B849737 : Blo 562809 849737 := bstep (se 2 (by rfl) ⟨318651, by rfl⟩ : syracuseStep 849737 = 637303) B637303
theorem B6453107 : Blo 562809 6453107 := bstep (se 1 (by rfl) ⟨4839830, by rfl⟩ : syracuseStep 6453107 = 9679661) B9679661
theorem B1210231 : Blo 562809 1210231 := bstep (se 1 (by rfl) ⟨907673, by rfl⟩ : syracuseStep 1210231 = 1815347) B1815347
theorem B849851 : Blo 562809 849851 := bstep (se 1 (by rfl) ⟨637388, by rfl⟩ : syracuseStep 849851 = 1274777) B1274777
theorem B849911 : Blo 562809 849911 := bstep (se 1 (by rfl) ⟨637433, by rfl⟩ : syracuseStep 849911 = 1274867) B1274867
theorem B3209219 : Blo 562809 3209219 := bstep (se 1 (by rfl) ⟨2406914, by rfl⟩ : syracuseStep 3209219 = 4813829) B4813829
theorem B849935 : Blo 562809 849935 := bstep (se 1 (by rfl) ⟨637451, by rfl⟩ : syracuseStep 849935 = 1274903) B1274903
theorem B849977 : Blo 562809 849977 := bstep (se 2 (by rfl) ⟨318741, by rfl⟩ : syracuseStep 849977 = 637483) B637483
theorem B1964119 : Blo 562809 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B850055 : Blo 562809 850055 := bstep (se 1 (by rfl) ⟨637541, by rfl⟩ : syracuseStep 850055 = 1275083) B1275083
theorem B850091 : Blo 562809 850091 := bstep (se 1 (by rfl) ⟨637568, by rfl⟩ : syracuseStep 850091 = 1275137) B1275137
theorem B850121 : Blo 562809 850121 := bstep (se 2 (by rfl) ⟨318795, by rfl⟩ : syracuseStep 850121 = 637591) B637591
theorem B1145207 : Blo 562809 1145207 := bstep (se 1 (by rfl) ⟨858905, by rfl⟩ : syracuseStep 1145207 = 1717811) B1717811
theorem B3046081 : Blo 562809 3046081 := bstep (se 2 (by rfl) ⟨1142280, by rfl⟩ : syracuseStep 3046081 = 2284561) B2284561
theorem B3439297 : Blo 562809 3439297 := bstep (se 2 (by rfl) ⟨1289736, by rfl⟩ : syracuseStep 3439297 = 2579473) B2579473
theorem B1833673 : Blo 562809 1833673 := bstep (se 2 (by rfl) ⟨687627, by rfl⟩ : syracuseStep 1833673 = 1375255) B1375255
theorem B8157989 : Blo 562809 8157989 := bstep (se 4 (by rfl) ⟨764811, by rfl⟩ : syracuseStep 8157989 = 1529623) B1529623
theorem B4291379 : Blo 562809 4291379 := bstep (se 1 (by rfl) ⟨3218534, by rfl⟩ : syracuseStep 4291379 = 6437069) B6437069
theorem B588731 : Blo 562809 588731 := bstep (se 1 (by rfl) ⟨441548, by rfl⟩ : syracuseStep 588731 = 883097) B883097
theorem B9305549 : Blo 562809 9305549 := bstep (se 3 (by rfl) ⟨1744790, by rfl⟩ : syracuseStep 9305549 = 3489581) B3489581
theorem B1900043 : Blo 562809 1900043 := bstep (se 1 (by rfl) ⟨1425032, by rfl⟩ : syracuseStep 1900043 = 2850065) B2850065
theorem B949819 : Blo 562809 949819 := bstep (se 1 (by rfl) ⟨712364, by rfl⟩ : syracuseStep 949819 = 1424729) B1424729
theorem B1900151 : Blo 562809 1900151 := bstep (se 1 (by rfl) ⟨1425113, by rfl⟩ : syracuseStep 1900151 = 2850227) B2850227
theorem B949961 : Blo 562809 949961 := bstep (se 2 (by rfl) ⟨356235, by rfl⟩ : syracuseStep 949961 = 712471) B712471
theorem B1146569 : Blo 562809 1146569 := bstep (se 2 (by rfl) ⟨429963, by rfl⟩ : syracuseStep 1146569 = 859927) B859927
theorem B4587313 : Blo 562809 4587313 := bstep (se 2 (by rfl) ⟨1720242, by rfl⟩ : syracuseStep 4587313 = 3440485) B3440485
theorem B2850713 : Blo 562809 2850713 := bstep (se 2 (by rfl) ⟨1069017, by rfl⟩ : syracuseStep 2850713 = 2138035) B2138035
theorem B1605577 : Blo 562809 1605577 := bstep (se 2 (by rfl) ⟨602091, by rfl⟩ : syracuseStep 1605577 = 1204183) B1204183
theorem B8257565 : Blo 562809 8257565 := bstep (se 3 (by rfl) ⟨1548293, by rfl⟩ : syracuseStep 8257565 = 3096587) B3096587
theorem B6947045 : Blo 562809 6947045 := bstep (se 4 (by rfl) ⟨651285, by rfl⟩ : syracuseStep 6947045 = 1302571) B1302571
theorem B4292837 : Blo 562809 4292837 := bstep (se 4 (by rfl) ⟨402453, by rfl⟩ : syracuseStep 4292837 = 804907) B804907
theorem B950521 : Blo 562809 950521 := bstep (se 2 (by rfl) ⟨356445, by rfl⟩ : syracuseStep 950521 = 712891) B712891
theorem B16253237 : Blo 562809 16253237 := bstep (se 5 (by rfl) ⟨761870, by rfl⟩ : syracuseStep 16253237 = 1523741) B1523741
theorem B950791 : Blo 562809 950791 := bstep (se 1 (by rfl) ⟨713093, by rfl⟩ : syracuseStep 950791 = 1426187) B1426187
theorem B1606169 : Blo 562809 1606169 := bstep (se 2 (by rfl) ⟨602313, by rfl⟩ : syracuseStep 1606169 = 1204627) B1204627
theorem B2851361 : Blo 562809 2851361 := bstep (se 2 (by rfl) ⟨1069260, by rfl⟩ : syracuseStep 2851361 = 2138521) B2138521
theorem B951223 : Blo 562809 951223 := bstep (se 1 (by rfl) ⟨713417, by rfl⟩ : syracuseStep 951223 = 1426835) B1426835
theorem B1803379 : Blo 562809 1803379 := bstep (se 1 (by rfl) ⟨1352534, by rfl⟩ : syracuseStep 1803379 = 2705069) B2705069
theorem B36602999 : Blo 562809 36602999 := bstep (se 1 (by rfl) ⟨27452249, by rfl⟩ : syracuseStep 36602999 = 54904499) B54904499
theorem B951419 : Blo 562809 951419 := bstep (se 1 (by rfl) ⟨713564, by rfl⟩ : syracuseStep 951419 = 1427129) B1427129
theorem B7079183 : Blo 562809 7079183 := bstep (se 1 (by rfl) ⟨5309387, by rfl⟩ : syracuseStep 7079183 = 10618775) B10618775
theorem B3212567 : Blo 562809 3212567 := bstep (se 1 (by rfl) ⟨2409425, by rfl⟩ : syracuseStep 3212567 = 4818851) B4818851
theorem B2033039 : Blo 562809 2033039 := bstep (se 1 (by rfl) ⟨1524779, by rfl⟩ : syracuseStep 2033039 = 3049559) B3049559
theorem B1017263 : Blo 562809 1017263 := bstep (se 1 (by rfl) ⟨762947, by rfl⟩ : syracuseStep 1017263 = 1525895) B1525895
theorem B951817 : Blo 562809 951817 := bstep (se 2 (by rfl) ⟨356931, by rfl⟩ : syracuseStep 951817 = 713863) B713863
theorem B3671563 : Blo 562809 3671563 := bstep (se 1 (by rfl) ⟨2753672, by rfl⟩ : syracuseStep 3671563 = 5507345) B5507345
theorem B1803815 : Blo 562809 1803815 := bstep (se 1 (by rfl) ⟨1352861, by rfl⟩ : syracuseStep 1803815 = 2705723) B2705723
theorem B1902203 : Blo 562809 1902203 := bstep (se 1 (by rfl) ⟨1426652, by rfl⟩ : syracuseStep 1902203 = 2853305) B2853305
theorem B951979 : Blo 562809 951979 := bstep (se 1 (by rfl) ⟨713984, by rfl⟩ : syracuseStep 951979 = 1427969) B1427969
theorem B1148663 : Blo 562809 1148663 := bstep (se 1 (by rfl) ⟨861497, by rfl⟩ : syracuseStep 1148663 = 1722995) B1722995
theorem B1902365 : Blo 562809 1902365 := bstep (se 3 (by rfl) ⟨356693, by rfl⟩ : syracuseStep 1902365 = 713387) B713387
theorem B952283 : Blo 562809 952283 := bstep (se 1 (by rfl) ⟨714212, by rfl⟩ : syracuseStep 952283 = 1428425) B1428425
theorem B8161337 : Blo 562809 8161337 := bstep (se 2 (by rfl) ⟨3060501, by rfl⟩ : syracuseStep 8161337 = 6121003) B6121003
theorem B952519 : Blo 562809 952519 := bstep (se 1 (by rfl) ⟨714389, by rfl⟩ : syracuseStep 952519 = 1428779) B1428779
theorem B952681 : Blo 562809 952681 := bstep (se 2 (by rfl) ⟨357255, by rfl⟩ : syracuseStep 952681 = 714511) B714511
theorem B5507531 : Blo 562809 5507531 := bstep (se 1 (by rfl) ⟨4130648, by rfl⟩ : syracuseStep 5507531 = 8261297) B8261297
theorem B1903067 : Blo 562809 1903067 := bstep (se 1 (by rfl) ⟨1427300, by rfl⟩ : syracuseStep 1903067 = 2854601) B2854601
theorem B953275 : Blo 562809 953275 := bstep (se 1 (by rfl) ⟨714956, by rfl⟩ : syracuseStep 953275 = 1429913) B1429913
theorem B953383 : Blo 562809 953383 := bstep (se 1 (by rfl) ⟨715037, by rfl⟩ : syracuseStep 953383 = 1430075) B1430075
theorem B1903769 : Blo 562809 1903769 := bstep (se 2 (by rfl) ⟨713913, by rfl⟩ : syracuseStep 1903769 = 1427827) B1427827
theorem B1084745 : Blo 562809 1084745 := bstep (se 2 (by rfl) ⟨406779, by rfl⟩ : syracuseStep 1084745 = 813559) B813559
theorem B953707 : Blo 562809 953707 := bstep (se 1 (by rfl) ⟨715280, by rfl⟩ : syracuseStep 953707 = 1430561) B1430561
theorem B1609085 : Blo 562809 1609085 := bstep (se 3 (by rfl) ⟨301703, by rfl⟩ : syracuseStep 1609085 = 603407) B603407
theorem B2854439 : Blo 562809 2854439 := bstep (se 1 (by rfl) ⟨2140829, by rfl⟩ : syracuseStep 2854439 = 4281659) B4281659
theorem B1806583 : Blo 562809 1806583 := bstep (se 1 (by rfl) ⟨1354937, by rfl⟩ : syracuseStep 1806583 = 2709875) B2709875
theorem B1904957 : Blo 562809 1904957 := bstep (se 3 (by rfl) ⟨357179, by rfl⟩ : syracuseStep 1904957 = 714359) B714359
theorem B954767 : Blo 562809 954767 := bstep (se 1 (by rfl) ⟨716075, by rfl⟩ : syracuseStep 954767 = 1432151) B1432151
theorem B955003 : Blo 562809 955003 := bstep (se 1 (by rfl) ⟨716252, by rfl⟩ : syracuseStep 955003 = 1432505) B1432505
theorem B9573137 : Blo 562809 9573137 := bstep (se 2 (by rfl) ⟨3589926, by rfl⟩ : syracuseStep 9573137 = 7179853) B7179853
theorem B1905821 : Blo 562809 1905821 := bstep (se 3 (by rfl) ⟨357341, by rfl⟩ : syracuseStep 1905821 = 714683) B714683
theorem B1610999 : Blo 562809 1610999 := bstep (se 1 (by rfl) ⟨1208249, by rfl⟩ : syracuseStep 1610999 = 2416499) B2416499
theorem B1611227 : Blo 562809 1611227 := bstep (se 1 (by rfl) ⟨1208420, by rfl⟩ : syracuseStep 1611227 = 2416841) B2416841
theorem B955867 : Blo 562809 955867 := bstep (se 1 (by rfl) ⟨716900, by rfl⟩ : syracuseStep 955867 = 1433801) B1433801
theorem B5445083 : Blo 562809 5445083 := bstep (se 1 (by rfl) ⟨4083812, by rfl⟩ : syracuseStep 5445083 = 8167625) B8167625
theorem B2037307 : Blo 562809 2037307 := bstep (se 1 (by rfl) ⟨1527980, by rfl⟩ : syracuseStep 2037307 = 3055961) B3055961
theorem B2856545 : Blo 562809 2856545 := bstep (se 2 (by rfl) ⟨1071204, by rfl⟩ : syracuseStep 2856545 = 2142409) B2142409
theorem B562811 : Blo 562809 562811 := bstep (se 1 (by rfl) ⟨422108, by rfl⟩ : syracuseStep 562811 = 844217) B844217
theorem B562863 : Blo 562809 562863 := bstep (se 1 (by rfl) ⟨422147, by rfl⟩ : syracuseStep 562863 = 844295) B844295
theorem B1808057 : Blo 562809 1808057 := bstep (se 2 (by rfl) ⟨678021, by rfl⟩ : syracuseStep 1808057 = 1356043) B1356043
theorem B1906361 : Blo 562809 1906361 := bstep (se 2 (by rfl) ⟨714885, by rfl⟩ : syracuseStep 1906361 = 1429771) B1429771
theorem B562887 : Blo 562809 562887 := bstep (se 1 (by rfl) ⟨422165, by rfl⟩ : syracuseStep 562887 = 844331) B844331
theorem B562907 : Blo 562809 562907 := bstep (se 1 (by rfl) ⟨422180, by rfl⟩ : syracuseStep 562907 = 844361) B844361
theorem B562983 : Blo 562809 562983 := bstep (se 1 (by rfl) ⟨422237, by rfl⟩ : syracuseStep 562983 = 844475) B844475
theorem B1808171 : Blo 562809 1808171 := bstep (se 1 (by rfl) ⟨1356128, by rfl⟩ : syracuseStep 1808171 = 2712257) B2712257
theorem B1447753 : Blo 562809 1447753 := bstep (se 2 (by rfl) ⟨542907, by rfl⟩ : syracuseStep 1447753 = 1085815) B1085815
theorem B563023 : Blo 562809 563023 := bstep (se 1 (by rfl) ⟨422267, by rfl⟩ : syracuseStep 563023 = 844535) B844535
theorem B563039 : Blo 562809 563039 := bstep (se 1 (by rfl) ⟨422279, by rfl⟩ : syracuseStep 563039 = 844559) B844559
theorem B563067 : Blo 562809 563067 := bstep (se 1 (by rfl) ⟨422300, by rfl⟩ : syracuseStep 563067 = 844601) B844601
theorem B563119 : Blo 562809 563119 := bstep (se 1 (by rfl) ⟨422339, by rfl⟩ : syracuseStep 563119 = 844679) B844679
theorem B563143 : Blo 562809 563143 := bstep (se 1 (by rfl) ⟨422357, by rfl⟩ : syracuseStep 563143 = 844715) B844715
theorem B563163 : Blo 562809 563163 := bstep (se 1 (by rfl) ⟨422372, by rfl⟩ : syracuseStep 563163 = 844745) B844745
theorem B563239 : Blo 562809 563239 := bstep (se 1 (by rfl) ⟨422429, by rfl⟩ : syracuseStep 563239 = 844859) B844859
theorem B563279 : Blo 562809 563279 := bstep (se 1 (by rfl) ⟨422459, by rfl⟩ : syracuseStep 563279 = 844919) B844919
theorem B563295 : Blo 562809 563295 := bstep (se 1 (by rfl) ⟨422471, by rfl⟩ : syracuseStep 563295 = 844943) B844943
theorem B563323 : Blo 562809 563323 := bstep (se 1 (by rfl) ⟨422492, by rfl⟩ : syracuseStep 563323 = 844985) B844985
theorem B563375 : Blo 562809 563375 := bstep (se 1 (by rfl) ⟨422531, by rfl⟩ : syracuseStep 563375 = 845063) B845063
theorem B563399 : Blo 562809 563399 := bstep (se 1 (by rfl) ⟨422549, by rfl⟩ : syracuseStep 563399 = 845099) B845099
theorem B563419 : Blo 562809 563419 := bstep (se 1 (by rfl) ⟨422564, by rfl⟩ : syracuseStep 563419 = 845129) B845129
theorem B1906955 : Blo 562809 1906955 := bstep (se 1 (by rfl) ⟨1430216, by rfl⟩ : syracuseStep 1906955 = 2860433) B2860433
theorem B563495 : Blo 562809 563495 := bstep (se 1 (by rfl) ⟨422621, by rfl⟩ : syracuseStep 563495 = 845243) B845243
theorem B563535 : Blo 562809 563535 := bstep (se 1 (by rfl) ⟨422651, by rfl⟩ : syracuseStep 563535 = 845303) B845303
theorem B563551 : Blo 562809 563551 := bstep (se 1 (by rfl) ⟨422663, by rfl⟩ : syracuseStep 563551 = 845327) B845327
theorem B563579 : Blo 562809 563579 := bstep (se 1 (by rfl) ⟨422684, by rfl⟩ : syracuseStep 563579 = 845369) B845369
theorem B563631 : Blo 562809 563631 := bstep (se 1 (by rfl) ⟨422723, by rfl⟩ : syracuseStep 563631 = 845447) B845447
theorem B563655 : Blo 562809 563655 := bstep (se 1 (by rfl) ⟨422741, by rfl⟩ : syracuseStep 563655 = 845483) B845483
theorem B563675 : Blo 562809 563675 := bstep (se 1 (by rfl) ⟨422756, by rfl⟩ : syracuseStep 563675 = 845513) B845513
theorem B1907225 : Blo 562809 1907225 := bstep (se 2 (by rfl) ⟨715209, by rfl⟩ : syracuseStep 1907225 = 1430419) B1430419
theorem B563751 : Blo 562809 563751 := bstep (se 1 (by rfl) ⟨422813, by rfl⟩ : syracuseStep 563751 = 845627) B845627
theorem B563791 : Blo 562809 563791 := bstep (se 1 (by rfl) ⟨422843, by rfl⟩ : syracuseStep 563791 = 845687) B845687
theorem B563807 : Blo 562809 563807 := bstep (se 1 (by rfl) ⟨422855, by rfl⟩ : syracuseStep 563807 = 845711) B845711
theorem B563835 : Blo 562809 563835 := bstep (se 1 (by rfl) ⟨422876, by rfl⟩ : syracuseStep 563835 = 845753) B845753
theorem B8460935 : Blo 562809 8460935 := bstep (se 1 (by rfl) ⟨6345701, by rfl⟩ : syracuseStep 8460935 = 12691403) B12691403
theorem B563887 : Blo 562809 563887 := bstep (se 1 (by rfl) ⟨422915, by rfl⟩ : syracuseStep 563887 = 845831) B845831
theorem B563911 : Blo 562809 563911 := bstep (se 1 (by rfl) ⟨422933, by rfl⟩ : syracuseStep 563911 = 845867) B845867
theorem B563931 : Blo 562809 563931 := bstep (se 1 (by rfl) ⟨422948, by rfl⟩ : syracuseStep 563931 = 845897) B845897
theorem B1809145 : Blo 562809 1809145 := bstep (se 2 (by rfl) ⟨678429, by rfl⟩ : syracuseStep 1809145 = 1356859) B1356859
theorem B564007 : Blo 562809 564007 := bstep (se 1 (by rfl) ⟨423005, by rfl⟩ : syracuseStep 564007 = 846011) B846011
theorem B564047 : Blo 562809 564047 := bstep (se 1 (by rfl) ⟨423035, by rfl⟩ : syracuseStep 564047 = 846071) B846071
theorem B564063 : Blo 562809 564063 := bstep (se 1 (by rfl) ⟨423047, by rfl⟩ : syracuseStep 564063 = 846095) B846095
theorem B1612639 : Blo 562809 1612639 := bstep (se 1 (by rfl) ⟨1209479, by rfl⟩ : syracuseStep 1612639 = 2418959) B2418959
theorem B564091 : Blo 562809 564091 := bstep (se 1 (by rfl) ⟨423068, by rfl⟩ : syracuseStep 564091 = 846137) B846137
theorem B564143 : Blo 562809 564143 := bstep (se 1 (by rfl) ⟨423107, by rfl⟩ : syracuseStep 564143 = 846215) B846215
theorem B564167 : Blo 562809 564167 := bstep (se 1 (by rfl) ⟨423125, by rfl⟩ : syracuseStep 564167 = 846251) B846251
theorem B564187 : Blo 562809 564187 := bstep (se 1 (by rfl) ⟨423140, by rfl⟩ : syracuseStep 564187 = 846281) B846281
theorem B2858003 : Blo 562809 2858003 := bstep (se 1 (by rfl) ⟨2143502, by rfl⟩ : syracuseStep 2858003 = 4287005) B4287005
theorem B564263 : Blo 562809 564263 := bstep (se 1 (by rfl) ⟨423197, by rfl⟩ : syracuseStep 564263 = 846395) B846395
theorem B564303 : Blo 562809 564303 := bstep (se 1 (by rfl) ⟨423227, by rfl⟩ : syracuseStep 564303 = 846455) B846455
theorem B564319 : Blo 562809 564319 := bstep (se 1 (by rfl) ⟨423239, by rfl⟩ : syracuseStep 564319 = 846479) B846479
theorem B564347 : Blo 562809 564347 := bstep (se 1 (by rfl) ⟨423260, by rfl⟩ : syracuseStep 564347 = 846521) B846521
theorem B564399 : Blo 562809 564399 := bstep (se 1 (by rfl) ⟨423299, by rfl⟩ : syracuseStep 564399 = 846599) B846599
theorem B2038979 : Blo 562809 2038979 := bstep (se 1 (by rfl) ⟨1529234, by rfl⟩ : syracuseStep 2038979 = 3058469) B3058469
theorem B564423 : Blo 562809 564423 := bstep (se 1 (by rfl) ⟨423317, by rfl⟩ : syracuseStep 564423 = 846635) B846635
theorem B564443 : Blo 562809 564443 := bstep (se 1 (by rfl) ⟨423332, by rfl⟩ : syracuseStep 564443 = 846665) B846665
theorem B6200567 : Blo 562809 6200567 := bstep (se 1 (by rfl) ⟨4650425, by rfl⟩ : syracuseStep 6200567 = 9300851) B9300851
theorem B564519 : Blo 562809 564519 := bstep (se 1 (by rfl) ⟨423389, by rfl⟩ : syracuseStep 564519 = 846779) B846779
theorem B564559 : Blo 562809 564559 := bstep (se 1 (by rfl) ⟨423419, by rfl⟩ : syracuseStep 564559 = 846839) B846839
theorem B564575 : Blo 562809 564575 := bstep (se 1 (by rfl) ⟨423431, by rfl⟩ : syracuseStep 564575 = 846863) B846863
theorem B564603 : Blo 562809 564603 := bstep (se 1 (by rfl) ⟨423452, by rfl⟩ : syracuseStep 564603 = 846905) B846905
theorem B564655 : Blo 562809 564655 := bstep (se 1 (by rfl) ⟨423491, by rfl⟩ : syracuseStep 564655 = 846983) B846983
theorem B564679 : Blo 562809 564679 := bstep (se 1 (by rfl) ⟨423509, by rfl⟩ : syracuseStep 564679 = 847019) B847019
theorem B564699 : Blo 562809 564699 := bstep (se 1 (by rfl) ⟨423524, by rfl⟩ : syracuseStep 564699 = 847049) B847049
theorem B564775 : Blo 562809 564775 := bstep (se 1 (by rfl) ⟨423581, by rfl⟩ : syracuseStep 564775 = 847163) B847163
theorem B564815 : Blo 562809 564815 := bstep (se 1 (by rfl) ⟨423611, by rfl⟩ : syracuseStep 564815 = 847223) B847223
theorem B564831 : Blo 562809 564831 := bstep (se 1 (by rfl) ⟨423623, by rfl⟩ : syracuseStep 564831 = 847247) B847247
theorem B564859 : Blo 562809 564859 := bstep (se 1 (by rfl) ⟨423644, by rfl⟩ : syracuseStep 564859 = 847289) B847289
theorem B1908359 : Blo 562809 1908359 := bstep (se 1 (by rfl) ⟨1431269, by rfl⟩ : syracuseStep 1908359 = 2862539) B2862539
theorem B564911 : Blo 562809 564911 := bstep (se 1 (by rfl) ⟨423683, by rfl⟩ : syracuseStep 564911 = 847367) B847367
theorem B1908413 : Blo 562809 1908413 := bstep (se 3 (by rfl) ⟨357827, by rfl⟩ : syracuseStep 1908413 = 715655) B715655
theorem B564935 : Blo 562809 564935 := bstep (se 1 (by rfl) ⟨423701, by rfl⟩ : syracuseStep 564935 = 847403) B847403
theorem B564955 : Blo 562809 564955 := bstep (se 1 (by rfl) ⟨423716, by rfl⟩ : syracuseStep 564955 = 847433) B847433
theorem B1449721 : Blo 562809 1449721 := bstep (se 2 (by rfl) ⟨543645, by rfl⟩ : syracuseStep 1449721 = 1087291) B1087291
theorem B565031 : Blo 562809 565031 := bstep (se 1 (by rfl) ⟨423773, by rfl⟩ : syracuseStep 565031 = 847547) B847547
theorem B565071 : Blo 562809 565071 := bstep (se 1 (by rfl) ⟨423803, by rfl⟩ : syracuseStep 565071 = 847607) B847607
theorem B565087 : Blo 562809 565087 := bstep (se 1 (by rfl) ⟨423815, by rfl⟩ : syracuseStep 565087 = 847631) B847631
theorem B1908575 : Blo 562809 1908575 := bstep (se 1 (by rfl) ⟨1431431, by rfl⟩ : syracuseStep 1908575 = 2862863) B2862863
theorem B565115 : Blo 562809 565115 := bstep (se 1 (by rfl) ⟨423836, by rfl⟩ : syracuseStep 565115 = 847673) B847673
theorem B565167 : Blo 562809 565167 := bstep (se 1 (by rfl) ⟨423875, by rfl⟩ : syracuseStep 565167 = 847751) B847751
theorem B565191 : Blo 562809 565191 := bstep (se 1 (by rfl) ⟨423893, by rfl⟩ : syracuseStep 565191 = 847787) B847787
theorem B565211 : Blo 562809 565211 := bstep (se 1 (by rfl) ⟨423908, by rfl⟩ : syracuseStep 565211 = 847817) B847817
theorem B1908737 : Blo 562809 1908737 := bstep (se 2 (by rfl) ⟨715776, by rfl⟩ : syracuseStep 1908737 = 1431553) B1431553
theorem B565287 : Blo 562809 565287 := bstep (se 1 (by rfl) ⟨423965, by rfl⟩ : syracuseStep 565287 = 847931) B847931
theorem B565327 : Blo 562809 565327 := bstep (se 1 (by rfl) ⟨423995, by rfl⟩ : syracuseStep 565327 = 847991) B847991
theorem B565343 : Blo 562809 565343 := bstep (se 1 (by rfl) ⟨424007, by rfl⟩ : syracuseStep 565343 = 848015) B848015
theorem B565371 : Blo 562809 565371 := bstep (se 1 (by rfl) ⟨424028, by rfl⟩ : syracuseStep 565371 = 848057) B848057
theorem B565423 : Blo 562809 565423 := bstep (se 1 (by rfl) ⟨424067, by rfl⟩ : syracuseStep 565423 = 848135) B848135
theorem B565447 : Blo 562809 565447 := bstep (se 1 (by rfl) ⟨424085, by rfl⟩ : syracuseStep 565447 = 848171) B848171
theorem B565467 : Blo 562809 565467 := bstep (se 1 (by rfl) ⟨424100, by rfl⟩ : syracuseStep 565467 = 848201) B848201
theorem B565543 : Blo 562809 565543 := bstep (se 1 (by rfl) ⟨424157, by rfl⟩ : syracuseStep 565543 = 848315) B848315
theorem B565583 : Blo 562809 565583 := bstep (se 1 (by rfl) ⟨424187, by rfl⟩ : syracuseStep 565583 = 848375) B848375
theorem B565599 : Blo 562809 565599 := bstep (se 1 (by rfl) ⟨424199, by rfl⟩ : syracuseStep 565599 = 848399) B848399
theorem B565627 : Blo 562809 565627 := bstep (se 1 (by rfl) ⟨424220, by rfl⟩ : syracuseStep 565627 = 848441) B848441
theorem B565679 : Blo 562809 565679 := bstep (se 1 (by rfl) ⟨424259, by rfl⟩ : syracuseStep 565679 = 848519) B848519
theorem B565703 : Blo 562809 565703 := bstep (se 1 (by rfl) ⟨424277, by rfl⟩ : syracuseStep 565703 = 848555) B848555
theorem B565723 : Blo 562809 565723 := bstep (se 1 (by rfl) ⟨424292, by rfl⟩ : syracuseStep 565723 = 848585) B848585
theorem B9675287 : Blo 562809 9675287 := bstep (se 1 (by rfl) ⟨7256465, by rfl⟩ : syracuseStep 9675287 = 14512931) B14512931
theorem B565799 : Blo 562809 565799 := bstep (se 1 (by rfl) ⟨424349, by rfl⟩ : syracuseStep 565799 = 848699) B848699
theorem B565839 : Blo 562809 565839 := bstep (se 1 (by rfl) ⟨424379, by rfl⟩ : syracuseStep 565839 = 848759) B848759
theorem B565855 : Blo 562809 565855 := bstep (se 1 (by rfl) ⟨424391, by rfl⟩ : syracuseStep 565855 = 848783) B848783
theorem B565883 : Blo 562809 565883 := bstep (se 1 (by rfl) ⟨424412, by rfl⟩ : syracuseStep 565883 = 848825) B848825
theorem B3613319 : Blo 562809 3613319 := bstep (se 1 (by rfl) ⟨2709989, by rfl⟩ : syracuseStep 3613319 = 5419979) B5419979
theorem B565935 : Blo 562809 565935 := bstep (se 1 (by rfl) ⟨424451, by rfl⟩ : syracuseStep 565935 = 848903) B848903
theorem B3613369 : Blo 562809 3613369 := bstep (se 2 (by rfl) ⟨1355013, by rfl⟩ : syracuseStep 3613369 = 2710027) B2710027
theorem B565959 : Blo 562809 565959 := bstep (se 1 (by rfl) ⟨424469, by rfl⟩ : syracuseStep 565959 = 848939) B848939
theorem B565979 : Blo 562809 565979 := bstep (se 1 (by rfl) ⟨424484, by rfl⟩ : syracuseStep 565979 = 848969) B848969
theorem B566055 : Blo 562809 566055 := bstep (se 1 (by rfl) ⟨424541, by rfl⟩ : syracuseStep 566055 = 849083) B849083
theorem B1909547 : Blo 562809 1909547 := bstep (se 1 (by rfl) ⟨1432160, by rfl⟩ : syracuseStep 1909547 = 2864321) B2864321
theorem B566095 : Blo 562809 566095 := bstep (se 1 (by rfl) ⟨424571, by rfl⟩ : syracuseStep 566095 = 849143) B849143
theorem B566111 : Blo 562809 566111 := bstep (se 1 (by rfl) ⟨424583, by rfl⟩ : syracuseStep 566111 = 849167) B849167
theorem B566139 : Blo 562809 566139 := bstep (se 1 (by rfl) ⟨424604, by rfl⟩ : syracuseStep 566139 = 849209) B849209
theorem B566191 : Blo 562809 566191 := bstep (se 1 (by rfl) ⟨424643, by rfl⟩ : syracuseStep 566191 = 849287) B849287
theorem B3089335 : Blo 562809 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B566215 : Blo 562809 566215 := bstep (se 1 (by rfl) ⟨424661, by rfl⟩ : syracuseStep 566215 = 849323) B849323
theorem B566235 : Blo 562809 566235 := bstep (se 1 (by rfl) ⟨424676, by rfl⟩ : syracuseStep 566235 = 849353) B849353
theorem B566311 : Blo 562809 566311 := bstep (se 1 (by rfl) ⟨424733, by rfl⟩ : syracuseStep 566311 = 849467) B849467
theorem B1909817 : Blo 562809 1909817 := bstep (se 2 (by rfl) ⟨716181, by rfl⟩ : syracuseStep 1909817 = 1432363) B1432363
theorem B566351 : Blo 562809 566351 := bstep (se 1 (by rfl) ⟨424763, by rfl⟩ : syracuseStep 566351 = 849527) B849527
theorem B566367 : Blo 562809 566367 := bstep (se 1 (by rfl) ⟨424775, by rfl⟩ : syracuseStep 566367 = 849551) B849551
theorem B566395 : Blo 562809 566395 := bstep (se 1 (by rfl) ⟨424796, by rfl⟩ : syracuseStep 566395 = 849593) B849593
theorem B566447 : Blo 562809 566447 := bstep (se 1 (by rfl) ⟨424835, by rfl⟩ : syracuseStep 566447 = 849671) B849671
theorem B566471 : Blo 562809 566471 := bstep (se 1 (by rfl) ⟨424853, by rfl⟩ : syracuseStep 566471 = 849707) B849707
theorem B566491 : Blo 562809 566491 := bstep (se 1 (by rfl) ⟨424868, by rfl⟩ : syracuseStep 566491 = 849737) B849737
theorem B4302071 : Blo 562809 4302071 := bstep (se 1 (by rfl) ⟨3226553, by rfl⟩ : syracuseStep 4302071 = 6453107) B6453107
theorem B4629797 : Blo 562809 4629797 := bstep (se 4 (by rfl) ⟨434043, by rfl⟩ : syracuseStep 4629797 = 868087) B868087
theorem B566567 : Blo 562809 566567 := bstep (se 1 (by rfl) ⟨424925, by rfl⟩ : syracuseStep 566567 = 849851) B849851
theorem B566607 : Blo 562809 566607 := bstep (se 1 (by rfl) ⟨424955, by rfl⟩ : syracuseStep 566607 = 849911) B849911
theorem B2139479 : Blo 562809 2139479 := bstep (se 1 (by rfl) ⟨1604609, by rfl⟩ : syracuseStep 2139479 = 3209219) B3209219
theorem B566623 : Blo 562809 566623 := bstep (se 1 (by rfl) ⟨424967, by rfl⟩ : syracuseStep 566623 = 849935) B849935
theorem B566651 : Blo 562809 566651 := bstep (se 1 (by rfl) ⟨424988, by rfl⟩ : syracuseStep 566651 = 849977) B849977
theorem B1910141 : Blo 562809 1910141 := bstep (se 3 (by rfl) ⟨358151, by rfl⟩ : syracuseStep 1910141 = 716303) B716303
theorem B566703 : Blo 562809 566703 := bstep (se 1 (by rfl) ⟨425027, by rfl⟩ : syracuseStep 566703 = 850055) B850055
theorem B566727 : Blo 562809 566727 := bstep (se 1 (by rfl) ⟨425045, by rfl⟩ : syracuseStep 566727 = 850091) B850091
theorem B566747 : Blo 562809 566747 := bstep (se 1 (by rfl) ⟨425060, by rfl⟩ : syracuseStep 566747 = 850121) B850121
theorem B763471 : Blo 562809 763471 := bstep (se 1 (by rfl) ⟨572603, by rfl⟩ : syracuseStep 763471 = 1145207) B1145207
theorem B14526053 : Blo 562809 14526053 := bstep (se 4 (by rfl) ⟨1361817, by rfl⟩ : syracuseStep 14526053 = 2723635) B2723635
theorem B1910411 : Blo 562809 1910411 := bstep (se 1 (by rfl) ⟨1432808, by rfl⟩ : syracuseStep 1910411 = 2865617) B2865617
theorem B4302557 : Blo 562809 4302557 := bstep (se 3 (by rfl) ⟨806729, by rfl⟩ : syracuseStep 4302557 = 1613459) B1613459
theorem B3221315 : Blo 562809 3221315 := bstep (se 1 (by rfl) ⟨2415986, by rfl⟩ : syracuseStep 3221315 = 4831973) B4831973
theorem B3057517 : Blo 562809 3057517 := bstep (se 3 (by rfl) ⟨573284, by rfl⟩ : syracuseStep 3057517 = 1146569) B1146569
theorem B2860919 : Blo 562809 2860919 := bstep (se 1 (by rfl) ⟨2145689, by rfl⟩ : syracuseStep 2860919 = 4291379) B4291379
theorem B10889315 : Blo 562809 10889315 := bstep (se 1 (by rfl) ⟨8166986, by rfl⟩ : syracuseStep 10889315 = 16333973) B16333973
theorem B6203699 : Blo 562809 6203699 := bstep (se 1 (by rfl) ⟨4652774, by rfl⟩ : syracuseStep 6203699 = 9305549) B9305549
theorem B37234997 : Blo 562809 37234997 := bstep (se 5 (by rfl) ⟨1745390, by rfl⟩ : syracuseStep 37234997 = 3490781) B3490781
theorem B633307 : Blo 562809 633307 := bstep (se 1 (by rfl) ⟨474980, by rfl⟩ : syracuseStep 633307 = 949961) B949961
theorem B1911329 : Blo 562809 1911329 := bstep (se 2 (by rfl) ⟨716748, by rfl⟩ : syracuseStep 1911329 = 1433497) B1433497
theorem B2140769 : Blo 562809 2140769 := bstep (se 2 (by rfl) ⟨802788, by rfl⟩ : syracuseStep 2140769 = 1605577) B1605577
theorem B1911545 : Blo 562809 1911545 := bstep (se 2 (by rfl) ⟨716829, by rfl⟩ : syracuseStep 1911545 = 1433659) B1433659
theorem B633775 : Blo 562809 633775 := bstep (se 1 (by rfl) ⟨475331, by rfl⟩ : syracuseStep 633775 = 950663) B950663
theorem B1911815 : Blo 562809 1911815 := bstep (se 1 (by rfl) ⟨1433861, by rfl⟩ : syracuseStep 1911815 = 2867723) B2867723
theorem B1911923 : Blo 562809 1911923 := bstep (se 1 (by rfl) ⟨1433942, by rfl⟩ : syracuseStep 1911923 = 2867885) B2867885
theorem B7253185 : Blo 562809 7253185 := bstep (se 2 (by rfl) ⟨2719944, by rfl⟩ : syracuseStep 7253185 = 5439889) B5439889
theorem B634207 : Blo 562809 634207 := bstep (se 1 (by rfl) ⟨475655, by rfl⟩ : syracuseStep 634207 = 951311) B951311
theorem B1912193 : Blo 562809 1912193 := bstep (se 2 (by rfl) ⟨717072, by rfl⟩ : syracuseStep 1912193 = 1434145) B1434145
theorem B16788871 : Blo 562809 16788871 := bstep (se 1 (by rfl) ⟨12591653, by rfl⟩ : syracuseStep 16788871 = 25183307) B25183307
theorem B634567 : Blo 562809 634567 := bstep (se 1 (by rfl) ⟨475925, by rfl⟩ : syracuseStep 634567 = 951851) B951851
theorem B1355513 : Blo 562809 1355513 := bstep (se 2 (by rfl) ⟨508317, by rfl⟩ : syracuseStep 1355513 = 1016635) B1016635
theorem B4075535 : Blo 562809 4075535 := bstep (se 1 (by rfl) ⟨3056651, by rfl⟩ : syracuseStep 4075535 = 6113303) B6113303
theorem B2142227 : Blo 562809 2142227 := bstep (se 1 (by rfl) ⟨1606670, by rfl⟩ : syracuseStep 2142227 = 3213341) B3213341
theorem B602587 : Blo 562809 602587 := bstep (se 1 (by rfl) ⟨451940, by rfl⟩ : syracuseStep 602587 = 903881) B903881
theorem B2142683 : Blo 562809 2142683 := bstep (se 1 (by rfl) ⟨1607012, by rfl⟩ : syracuseStep 2142683 = 3214025) B3214025
theorem B635431 : Blo 562809 635431 := bstep (se 1 (by rfl) ⟨476573, by rfl⟩ : syracuseStep 635431 = 953147) B953147
theorem B2896669 : Blo 562809 2896669 := bstep (se 3 (by rfl) ⟨543125, by rfl⟩ : syracuseStep 2896669 = 1086251) B1086251
theorem B3224549 : Blo 562809 3224549 := bstep (se 4 (by rfl) ⟨302301, by rfl⟩ : syracuseStep 3224549 = 604603) B604603
theorem B963641 : Blo 562809 963641 := bstep (se 2 (by rfl) ⟨361365, by rfl⟩ : syracuseStep 963641 = 722731) B722731
theorem B603335 : Blo 562809 603335 := bstep (se 1 (by rfl) ⟨452501, by rfl⟩ : syracuseStep 603335 = 905003) B905003
theorem B1291663 : Blo 562809 1291663 := bstep (se 1 (by rfl) ⟨968747, by rfl⟩ : syracuseStep 1291663 = 1937495) B1937495
theorem B3225005 : Blo 562809 3225005 := bstep (se 3 (by rfl) ⟨604688, by rfl⟩ : syracuseStep 3225005 = 1209377) B1209377
theorem B2143867 : Blo 562809 2143867 := bstep (se 1 (by rfl) ⟨1607900, by rfl⟩ : syracuseStep 2143867 = 3215801) B3215801
theorem B571055 : Blo 562809 571055 := bstep (se 1 (by rfl) ⟨428291, by rfl⟩ : syracuseStep 571055 = 856583) B856583
theorem B2176723 : Blo 562809 2176723 := bstep (se 1 (by rfl) ⟨1632542, by rfl⟩ : syracuseStep 2176723 = 3265085) B3265085
theorem B2602847 : Blo 562809 2602847 := bstep (se 1 (by rfl) ⟨1952135, by rfl⟩ : syracuseStep 2602847 = 3904271) B3904271
theorem B3225689 : Blo 562809 3225689 := bstep (se 2 (by rfl) ⟨1209633, by rfl⟩ : syracuseStep 3225689 = 2419267) B2419267
theorem B637051 : Blo 562809 637051 := bstep (se 1 (by rfl) ⟨477788, by rfl⟩ : syracuseStep 637051 = 955577) B955577
theorem B637519 : Blo 562809 637519 := bstep (se 1 (by rfl) ⟨478139, by rfl⟩ : syracuseStep 637519 = 956279) B956279
theorem B1522273 : Blo 562809 1522273 := bstep (se 2 (by rfl) ⟨570852, by rfl⟩ : syracuseStep 1522273 = 1141705) B1141705
theorem B2898641 : Blo 562809 2898641 := bstep (se 2 (by rfl) ⟨1086990, by rfl⟩ : syracuseStep 2898641 = 2173981) B2173981
theorem B1653577 : Blo 562809 1653577 := bstep (se 2 (by rfl) ⟨620091, by rfl⟩ : syracuseStep 1653577 = 1240183) B1240183
theorem B2145143 : Blo 562809 2145143 := bstep (se 1 (by rfl) ⟨1608857, by rfl⟩ : syracuseStep 2145143 = 3217715) B3217715
theorem B2866103 : Blo 562809 2866103 := bstep (se 1 (by rfl) ⟨2149577, by rfl⟩ : syracuseStep 2866103 = 4299155) B4299155
theorem B965641 : Blo 562809 965641 := bstep (se 2 (by rfl) ⟨362115, by rfl⟩ : syracuseStep 965641 = 724231) B724231
theorem B801991 : Blo 562809 801991 := bstep (se 1 (by rfl) ⟨601493, by rfl⟩ : syracuseStep 801991 = 1202987) B1202987
theorem B2146115 : Blo 562809 2146115 := bstep (se 1 (by rfl) ⟨1609586, by rfl⟩ : syracuseStep 2146115 = 3219173) B3219173
theorem B4112441 : Blo 562809 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B2179153 : Blo 562809 2179153 := bstep (se 2 (by rfl) ⟨817182, by rfl⟩ : syracuseStep 2179153 = 1634365) B1634365
theorem B4276313 : Blo 562809 4276313 := bstep (se 2 (by rfl) ⟨1603617, by rfl⟩ : syracuseStep 4276313 = 3207235) B3207235
theorem B2146571 : Blo 562809 2146571 := bstep (se 1 (by rfl) ⟨1609928, by rfl⟩ : syracuseStep 2146571 = 3219857) B3219857
theorem B3719485 : Blo 562809 3719485 := bstep (se 3 (by rfl) ⟨697403, by rfl⟩ : syracuseStep 3719485 = 1394807) B1394807
theorem B2900285 : Blo 562809 2900285 := bstep (se 3 (by rfl) ⟨543803, by rfl⟩ : syracuseStep 2900285 = 1087607) B1087607
theorem B2572631 : Blo 562809 2572631 := bstep (se 1 (by rfl) ⟨1929473, by rfl⟩ : syracuseStep 2572631 = 3858947) B3858947
theorem B2867561 : Blo 562809 2867561 := bstep (se 2 (by rfl) ⟨1075335, by rfl⟩ : syracuseStep 2867561 = 2150671) B2150671
theorem B1425883 : Blo 562809 1425883 := bstep (se 1 (by rfl) ⟨1069412, by rfl⟩ : syracuseStep 1425883 = 2138825) B2138825
theorem B1721021 : Blo 562809 1721021 := bstep (se 3 (by rfl) ⟨322691, by rfl⟩ : syracuseStep 1721021 = 645383) B645383
theorem B2147255 : Blo 562809 2147255 := bstep (se 1 (by rfl) ⟨1610441, by rfl⟩ : syracuseStep 2147255 = 3220883) B3220883
theorem B902183 : Blo 562809 902183 := bstep (se 1 (by rfl) ⟨676637, by rfl⟩ : syracuseStep 902183 = 1353275) B1353275
theorem B6439985 : Blo 562809 6439985 := bstep (se 2 (by rfl) ⟨2414994, by rfl⟩ : syracuseStep 6439985 = 4829989) B4829989
theorem B6865985 : Blo 562809 6865985 := bstep (se 2 (by rfl) ⟨2574744, by rfl⟩ : syracuseStep 6865985 = 5149489) B5149489
theorem B1426511 : Blo 562809 1426511 := bstep (se 1 (by rfl) ⟨1069883, by rfl⟩ : syracuseStep 1426511 = 2139767) B2139767
theorem B2573507 : Blo 562809 2573507 := bstep (se 1 (by rfl) ⟨1930130, by rfl⟩ : syracuseStep 2573507 = 3860261) B3860261
theorem B2901187 : Blo 562809 2901187 := bstep (se 1 (by rfl) ⟨2175890, by rfl⟩ : syracuseStep 2901187 = 4351781) B4351781
theorem B4277771 : Blo 562809 4277771 := bstep (se 1 (by rfl) ⟨3208328, by rfl⟩ : syracuseStep 4277771 = 6416657) B6416657
theorem B7226941 : Blo 562809 7226941 := bstep (se 3 (by rfl) ⟨1355051, by rfl⟩ : syracuseStep 7226941 = 2710103) B2710103
theorem B2148029 : Blo 562809 2148029 := bstep (se 3 (by rfl) ⟨402755, by rfl⟩ : syracuseStep 2148029 = 805511) B805511
theorem B1427159 : Blo 562809 1427159 := bstep (se 1 (by rfl) ⟨1070369, by rfl⟩ : syracuseStep 1427159 = 2140739) B2140739
theorem B3622751 : Blo 562809 3622751 := bstep (se 1 (by rfl) ⟨2717063, by rfl⟩ : syracuseStep 3622751 = 5434127) B5434127
theorem B2410553 : Blo 562809 2410553 := bstep (se 2 (by rfl) ⟨903957, by rfl⟩ : syracuseStep 2410553 = 1807915) B1807915
theorem B18368855 : Blo 562809 18368855 := bstep (se 1 (by rfl) ⟨13776641, by rfl⟩ : syracuseStep 18368855 = 27553283) B27553283
theorem B2148713 : Blo 562809 2148713 := bstep (se 2 (by rfl) ⟨805767, by rfl⟩ : syracuseStep 2148713 = 1611535) B1611535
theorem B904439 : Blo 562809 904439 := bstep (se 1 (by rfl) ⟨678329, by rfl⟩ : syracuseStep 904439 = 1356659) B1356659
theorem B4279715 : Blo 562809 4279715 := bstep (se 1 (by rfl) ⟨3209786, by rfl⟩ : syracuseStep 4279715 = 6419573) B6419573
theorem B9293237 : Blo 562809 9293237 := bstep (se 5 (by rfl) ⟨435620, by rfl⟩ : syracuseStep 9293237 = 871241) B871241
theorem B1068623 : Blo 562809 1068623 := bstep (se 1 (by rfl) ⟨801467, by rfl⟩ : syracuseStep 1068623 = 1602935) B1602935
theorem B2444897 : Blo 562809 2444897 := bstep (se 2 (by rfl) ⟨916836, by rfl⟩ : syracuseStep 2444897 = 1833673) B1833673
theorem B3428029 : Blo 562809 3428029 := bstep (se 3 (by rfl) ⟨642755, by rfl⟩ : syracuseStep 3428029 = 1285511) B1285511
theorem B2936737 : Blo 562809 2936737 := bstep (se 2 (by rfl) ⟨1101276, by rfl⟩ : syracuseStep 2936737 = 2202553) B2202553
theorem B1429751 : Blo 562809 1429751 := bstep (se 1 (by rfl) ⟨1072313, by rfl⟩ : syracuseStep 1429751 = 2144627) B2144627
theorem B2412929 : Blo 562809 2412929 := bstep (se 2 (by rfl) ⟨904848, by rfl⟩ : syracuseStep 2412929 = 1809697) B1809697
theorem B2413081 : Blo 562809 2413081 := bstep (se 2 (by rfl) ⟨904905, by rfl⟩ : syracuseStep 2413081 = 1809811) B1809811
theorem B2150945 : Blo 562809 2150945 := bstep (se 2 (by rfl) ⟨806604, by rfl⟩ : syracuseStep 2150945 = 1613209) B1613209
theorem B1069625 : Blo 562809 1069625 := bstep (se 2 (by rfl) ⟨401109, by rfl⟩ : syracuseStep 1069625 = 802219) B802219
theorem B1266425 : Blo 562809 1266425 := bstep (se 2 (by rfl) ⟨474909, by rfl⟩ : syracuseStep 1266425 = 949819) B949819
theorem B906079 : Blo 562809 906079 := bstep (se 1 (by rfl) ⟨679559, by rfl⟩ : syracuseStep 906079 = 1359119) B1359119
theorem B1266695 : Blo 562809 1266695 := bstep (se 1 (by rfl) ⟨950021, by rfl⟩ : syracuseStep 1266695 = 1900043) B1900043
theorem B2151431 : Blo 562809 2151431 := bstep (se 1 (by rfl) ⟨1613573, by rfl⟩ : syracuseStep 2151431 = 3227147) B3227147
theorem B6116417 : Blo 562809 6116417 := bstep (se 2 (by rfl) ⟨2293656, by rfl⟩ : syracuseStep 6116417 = 4587313) B4587313
theorem B1266767 : Blo 562809 1266767 := bstep (se 1 (by rfl) ⟨950075, by rfl⟩ : syracuseStep 1266767 = 1900151) B1900151
theorem B9622799 : Blo 562809 9622799 := bstep (se 1 (by rfl) ⟨7217099, by rfl⟩ : syracuseStep 9622799 = 14434199) B14434199
theorem B3626441 : Blo 562809 3626441 := bstep (se 2 (by rfl) ⟨1359915, by rfl⟩ : syracuseStep 3626441 = 2719831) B2719831
theorem B1267163 : Blo 562809 1267163 := bstep (se 1 (by rfl) ⟨950372, by rfl⟩ : syracuseStep 1267163 = 1900745) B1900745
theorem B2151917 : Blo 562809 2151917 := bstep (se 3 (by rfl) ⟨403484, by rfl⟩ : syracuseStep 2151917 = 806969) B806969
theorem B1431179 : Blo 562809 1431179 := bstep (se 1 (by rfl) ⟨1073384, by rfl⟩ : syracuseStep 1431179 = 2146769) B2146769
theorem B4282145 : Blo 562809 4282145 := bstep (se 2 (by rfl) ⟨1605804, by rfl⟩ : syracuseStep 4282145 = 3211609) B3211609
theorem B1431391 : Blo 562809 1431391 := bstep (se 1 (by rfl) ⟨1073543, by rfl⟩ : syracuseStep 1431391 = 2147087) B2147087
theorem B1267631 : Blo 562809 1267631 := bstep (se 1 (by rfl) ⟨950723, by rfl⟩ : syracuseStep 1267631 = 1901447) B1901447
theorem B1267883 : Blo 562809 1267883 := bstep (se 1 (by rfl) ⟨950912, by rfl⟩ : syracuseStep 1267883 = 1901825) B1901825
theorem B907463 : Blo 562809 907463 := bstep (se 1 (by rfl) ⟨680597, by rfl⟩ : syracuseStep 907463 = 1361195) B1361195
theorem B5429591 : Blo 562809 5429591 := bstep (se 1 (by rfl) ⟨4072193, by rfl⟩ : syracuseStep 5429591 = 8144387) B8144387
theorem B14473565 : Blo 562809 14473565 := bstep (se 3 (by rfl) ⟨2713793, by rfl⟩ : syracuseStep 14473565 = 5427587) B5427587
theorem B1071623 : Blo 562809 1071623 := bstep (se 1 (by rfl) ⟨803717, by rfl⟩ : syracuseStep 1071623 = 1607435) B1607435
theorem B1268423 : Blo 562809 1268423 := bstep (se 1 (by rfl) ⟨951317, by rfl⟩ : syracuseStep 1268423 = 1902635) B1902635
theorem B1432313 : Blo 562809 1432313 := bstep (se 2 (by rfl) ⟨537117, by rfl⟩ : syracuseStep 1432313 = 1074235) B1074235
theorem B1072055 : Blo 562809 1072055 := bstep (se 1 (by rfl) ⟨804041, by rfl⟩ : syracuseStep 1072055 = 1608083) B1608083
theorem B1072207 : Blo 562809 1072207 := bstep (se 1 (by rfl) ⟨804155, by rfl⟩ : syracuseStep 1072207 = 1608311) B1608311
theorem B1432961 : Blo 562809 1432961 := bstep (se 2 (by rfl) ⟨537360, by rfl⟩ : syracuseStep 1432961 = 1074721) B1074721
theorem B6413741 : Blo 562809 6413741 := bstep (se 3 (by rfl) ⟨1202576, by rfl⟩ : syracuseStep 6413741 = 2405153) B2405153
theorem B1269287 : Blo 562809 1269287 := bstep (se 1 (by rfl) ⟨951965, by rfl⟩ : syracuseStep 1269287 = 1903931) B1903931
theorem B2416225 : Blo 562809 2416225 := bstep (se 2 (by rfl) ⟨906084, by rfl⟩ : syracuseStep 2416225 = 1812169) B1812169
theorem B3858043 : Blo 562809 3858043 := bstep (se 1 (by rfl) ⟨2893532, by rfl⟩ : syracuseStep 3858043 = 5787065) B5787065
theorem B1236809 : Blo 562809 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B1269611 : Blo 562809 1269611 := bstep (se 1 (by rfl) ⟨952208, by rfl⟩ : syracuseStep 1269611 = 1904417) B1904417
theorem B3432311 : Blo 562809 3432311 := bstep (se 1 (by rfl) ⟨2574233, by rfl⟩ : syracuseStep 3432311 = 5148467) B5148467
theorem B1269665 : Blo 562809 1269665 := bstep (se 2 (by rfl) ⟨476124, by rfl⟩ : syracuseStep 1269665 = 952249) B952249
theorem B1204303 : Blo 562809 1204303 := bstep (se 1 (by rfl) ⟨903227, by rfl⟩ : syracuseStep 1204303 = 1806455) B1806455
theorem B1433771 : Blo 562809 1433771 := bstep (se 1 (by rfl) ⟨1075328, by rfl⟩ : syracuseStep 1433771 = 2150657) B2150657
theorem B1270007 : Blo 562809 1270007 := bstep (se 1 (by rfl) ⟨952505, by rfl⟩ : syracuseStep 1270007 = 1905011) B1905011
theorem B39739747 : Blo 562809 39739747 := bstep (se 1 (by rfl) ⟨29804810, by rfl⟩ : syracuseStep 39739747 = 59609621) B59609621
theorem B1073513 : Blo 562809 1073513 := bstep (se 2 (by rfl) ⟨402567, by rfl⟩ : syracuseStep 1073513 = 805135) B805135
theorem B844367 : Blo 562809 844367 := bstep (se 1 (by rfl) ⟨633275, by rfl⟩ : syracuseStep 844367 = 1266551) B1266551
theorem B844487 : Blo 562809 844487 := bstep (se 1 (by rfl) ⟨633365, by rfl⟩ : syracuseStep 844487 = 1266731) B1266731
theorem B1270601 : Blo 562809 1270601 := bstep (se 2 (by rfl) ⟨476475, by rfl⟩ : syracuseStep 1270601 = 952951) B952951
theorem B844649 : Blo 562809 844649 := bstep (se 2 (by rfl) ⟨316743, by rfl⟩ : syracuseStep 844649 = 633487) B633487
theorem B844727 : Blo 562809 844727 := bstep (se 1 (by rfl) ⟨633545, by rfl⟩ : syracuseStep 844727 = 1267091) B1267091
theorem B844763 : Blo 562809 844763 := bstep (se 1 (by rfl) ⟨633572, by rfl⟩ : syracuseStep 844763 = 1267145) B1267145
theorem B1434631 : Blo 562809 1434631 := bstep (se 1 (by rfl) ⟨1075973, by rfl⟩ : syracuseStep 1434631 = 2151947) B2151947
theorem B713767 : Blo 562809 713767 := bstep (se 1 (by rfl) ⟨535325, by rfl⟩ : syracuseStep 713767 = 1070651) B1070651
theorem B2581751 : Blo 562809 2581751 := bstep (se 1 (by rfl) ⟨1936313, by rfl⟩ : syracuseStep 2581751 = 3872627) B3872627
theorem B714091 : Blo 562809 714091 := bstep (se 1 (by rfl) ⟨535568, by rfl⟩ : syracuseStep 714091 = 1071137) B1071137
theorem B1074539 : Blo 562809 1074539 := bstep (se 1 (by rfl) ⟨805904, by rfl⟩ : syracuseStep 1074539 = 1611809) B1611809
theorem B845231 : Blo 562809 845231 := bstep (se 1 (by rfl) ⟨633923, by rfl⟩ : syracuseStep 845231 = 1267847) B1267847
theorem B845321 : Blo 562809 845321 := bstep (se 2 (by rfl) ⟨316995, by rfl⟩ : syracuseStep 845321 = 633991) B633991
theorem B3958283 : Blo 562809 3958283 := bstep (se 1 (by rfl) ⟨2968712, by rfl⟩ : syracuseStep 3958283 = 5937425) B5937425
theorem B5137931 : Blo 562809 5137931 := bstep (se 1 (by rfl) ⟨3853448, by rfl⟩ : syracuseStep 5137931 = 7706897) B7706897
theorem B845351 : Blo 562809 845351 := bstep (se 1 (by rfl) ⟨634013, by rfl⟩ : syracuseStep 845351 = 1268027) B1268027
theorem B1205857 : Blo 562809 1205857 := bstep (se 2 (by rfl) ⟨452196, by rfl⟩ : syracuseStep 1205857 = 904393) B904393
theorem B1271393 : Blo 562809 1271393 := bstep (se 2 (by rfl) ⟨476772, by rfl⟩ : syracuseStep 1271393 = 953545) B953545
theorem B15492707 : Blo 562809 15492707 := bstep (se 1 (by rfl) ⟨11619530, by rfl⟩ : syracuseStep 15492707 = 23239061) B23239061
theorem B845435 : Blo 562809 845435 := bstep (se 1 (by rfl) ⟨634076, by rfl⟩ : syracuseStep 845435 = 1268153) B1268153
theorem B845561 : Blo 562809 845561 := bstep (se 2 (by rfl) ⟨317085, by rfl⟩ : syracuseStep 845561 = 634171) B634171
theorem B845663 : Blo 562809 845663 := bstep (se 1 (by rfl) ⟨634247, by rfl⟩ : syracuseStep 845663 = 1268495) B1268495
theorem B845675 : Blo 562809 845675 := bstep (se 1 (by rfl) ⟨634256, by rfl⟩ : syracuseStep 845675 = 1268513) B1268513
theorem B1206191 : Blo 562809 1206191 := bstep (se 1 (by rfl) ⟨904643, by rfl⟩ : syracuseStep 1206191 = 1809287) B1809287
theorem B1206199 : Blo 562809 1206199 := bstep (se 1 (by rfl) ⟨904649, by rfl⟩ : syracuseStep 1206199 = 1809299) B1809299
theorem B1271735 : Blo 562809 1271735 := bstep (se 1 (by rfl) ⟨953801, by rfl⟩ : syracuseStep 1271735 = 1907603) B1907603
theorem B1075207 : Blo 562809 1075207 := bstep (se 1 (by rfl) ⟨806405, by rfl⟩ : syracuseStep 1075207 = 1612811) B1612811
theorem B845903 : Blo 562809 845903 := bstep (se 1 (by rfl) ⟨634427, by rfl⟩ : syracuseStep 845903 = 1268855) B1268855
theorem B9398359 : Blo 562809 9398359 := bstep (se 1 (by rfl) ⟨7048769, by rfl⟩ : syracuseStep 9398359 = 14097539) B14097539
theorem B846023 : Blo 562809 846023 := bstep (se 1 (by rfl) ⟨634517, by rfl⟩ : syracuseStep 846023 = 1269035) B1269035
theorem B846185 : Blo 562809 846185 := bstep (se 2 (by rfl) ⟨317319, by rfl⟩ : syracuseStep 846185 = 634639) B634639
theorem B846263 : Blo 562809 846263 := bstep (se 1 (by rfl) ⟨634697, by rfl⟩ : syracuseStep 846263 = 1269395) B1269395
theorem B846299 : Blo 562809 846299 := bstep (se 1 (by rfl) ⟨634724, by rfl⟩ : syracuseStep 846299 = 1269449) B1269449
theorem B1272329 : Blo 562809 1272329 := bstep (se 2 (by rfl) ⟨477123, by rfl⟩ : syracuseStep 1272329 = 954247) B954247
theorem B5204513 : Blo 562809 5204513 := bstep (se 2 (by rfl) ⟨1951692, by rfl⟩ : syracuseStep 5204513 = 3903385) B3903385
theorem B18278945 : Blo 562809 18278945 := bstep (se 2 (by rfl) ⟨6854604, by rfl⟩ : syracuseStep 18278945 = 13709209) B13709209
theorem B715387 : Blo 562809 715387 := bstep (se 1 (by rfl) ⟨536540, by rfl⟩ : syracuseStep 715387 = 1073081) B1073081
theorem B1272671 : Blo 562809 1272671 := bstep (se 1 (by rfl) ⟨954503, by rfl⟩ : syracuseStep 1272671 = 1909007) B1909007
theorem B846767 : Blo 562809 846767 := bstep (se 1 (by rfl) ⟨635075, by rfl⟩ : syracuseStep 846767 = 1270151) B1270151
theorem B846857 : Blo 562809 846857 := bstep (se 2 (by rfl) ⟨317571, by rfl⟩ : syracuseStep 846857 = 635143) B635143
theorem B1272851 : Blo 562809 1272851 := bstep (se 1 (by rfl) ⟨954638, by rfl⟩ : syracuseStep 1272851 = 1909277) B1909277
theorem B846887 : Blo 562809 846887 := bstep (se 1 (by rfl) ⟨635165, by rfl⟩ : syracuseStep 846887 = 1270331) B1270331
theorem B846971 : Blo 562809 846971 := bstep (se 1 (by rfl) ⟨635228, by rfl⟩ : syracuseStep 846971 = 1270457) B1270457
theorem B847097 : Blo 562809 847097 := bstep (se 2 (by rfl) ⟨317661, by rfl⟩ : syracuseStep 847097 = 635323) B635323
theorem B847199 : Blo 562809 847199 := bstep (se 1 (by rfl) ⟨635399, by rfl⟩ : syracuseStep 847199 = 1270799) B1270799
theorem B1273193 : Blo 562809 1273193 := bstep (se 2 (by rfl) ⟨477447, by rfl⟩ : syracuseStep 1273193 = 954895) B954895
theorem B847211 : Blo 562809 847211 := bstep (se 1 (by rfl) ⟨635408, by rfl⟩ : syracuseStep 847211 = 1270817) B1270817
theorem B1142191 : Blo 562809 1142191 := bstep (se 1 (by rfl) ⟨856643, by rfl⟩ : syracuseStep 1142191 = 1713287) B1713287
theorem B847439 : Blo 562809 847439 := bstep (se 1 (by rfl) ⟨635579, by rfl⟩ : syracuseStep 847439 = 1271159) B1271159
theorem B847559 : Blo 562809 847559 := bstep (se 1 (by rfl) ⟨635669, by rfl⟩ : syracuseStep 847559 = 1271339) B1271339
theorem B847721 : Blo 562809 847721 := bstep (se 2 (by rfl) ⟨317895, by rfl⟩ : syracuseStep 847721 = 635791) B635791
theorem B2420599 : Blo 562809 2420599 := bstep (se 1 (by rfl) ⟨1815449, by rfl⟩ : syracuseStep 2420599 = 3630899) B3630899
theorem B17592227 : Blo 562809 17592227 := bstep (se 1 (by rfl) ⟨13194170, by rfl⟩ : syracuseStep 17592227 = 26388341) B26388341
theorem B847799 : Blo 562809 847799 := bstep (se 1 (by rfl) ⟨635849, by rfl⟩ : syracuseStep 847799 = 1271699) B1271699
theorem B1273787 : Blo 562809 1273787 := bstep (se 1 (by rfl) ⟨955340, by rfl⟩ : syracuseStep 1273787 = 1910681) B1910681
theorem B847835 : Blo 562809 847835 := bstep (se 1 (by rfl) ⟨635876, by rfl⟩ : syracuseStep 847835 = 1271753) B1271753
theorem B1273913 : Blo 562809 1273913 := bstep (se 2 (by rfl) ⟨477717, by rfl⟩ : syracuseStep 1273913 = 955435) B955435
theorem B1274255 : Blo 562809 1274255 := bstep (se 1 (by rfl) ⟨955691, by rfl⟩ : syracuseStep 1274255 = 1911383) B1911383
theorem B848303 : Blo 562809 848303 := bstep (se 1 (by rfl) ⟨636227, by rfl⟩ : syracuseStep 848303 = 1272455) B1272455
theorem B717275 : Blo 562809 717275 := bstep (se 1 (by rfl) ⟨537956, by rfl⟩ : syracuseStep 717275 = 1075913) B1075913
theorem B848393 : Blo 562809 848393 := bstep (se 2 (by rfl) ⟨318147, by rfl⟩ : syracuseStep 848393 = 636295) B636295
theorem B848423 : Blo 562809 848423 := bstep (se 1 (by rfl) ⟨636317, by rfl⟩ : syracuseStep 848423 = 1272635) B1272635
theorem B848507 : Blo 562809 848507 := bstep (se 1 (by rfl) ⟨636380, by rfl⟩ : syracuseStep 848507 = 1272761) B1272761
theorem B1274579 : Blo 562809 1274579 := bstep (se 1 (by rfl) ⟨955934, by rfl⟩ : syracuseStep 1274579 = 1911869) B1911869
theorem B848633 : Blo 562809 848633 := bstep (se 2 (by rfl) ⟨318237, by rfl⟩ : syracuseStep 848633 = 636475) B636475
theorem B848735 : Blo 562809 848735 := bstep (se 1 (by rfl) ⟨636551, by rfl⟩ : syracuseStep 848735 = 1273103) B1273103
theorem B848747 : Blo 562809 848747 := bstep (se 1 (by rfl) ⟨636560, by rfl⟩ : syracuseStep 848747 = 1273121) B1273121
theorem B3208193 : Blo 562809 3208193 := bstep (se 2 (by rfl) ⟨1203072, by rfl⟩ : syracuseStep 3208193 = 2406145) B2406145
theorem B848975 : Blo 562809 848975 := bstep (se 1 (by rfl) ⟨636731, by rfl⟩ : syracuseStep 848975 = 1273463) B1273463
theorem B1569949 : Blo 562809 1569949 := bstep (se 3 (by rfl) ⟨294365, by rfl⟩ : syracuseStep 1569949 = 588731) B588731
theorem B849095 : Blo 562809 849095 := bstep (se 1 (by rfl) ⟨636821, by rfl⟩ : syracuseStep 849095 = 1273643) B1273643
theorem B1144169 : Blo 562809 1144169 := bstep (se 2 (by rfl) ⟨429063, by rfl⟩ : syracuseStep 1144169 = 858127) B858127
theorem B849257 : Blo 562809 849257 := bstep (se 2 (by rfl) ⟨318471, by rfl⟩ : syracuseStep 849257 = 636943) B636943
theorem B849335 : Blo 562809 849335 := bstep (se 1 (by rfl) ⟨637001, by rfl⟩ : syracuseStep 849335 = 1274003) B1274003
theorem B2618825 : Blo 562809 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B849371 : Blo 562809 849371 := bstep (se 1 (by rfl) ⟨637028, by rfl⟩ : syracuseStep 849371 = 1274057) B1274057
theorem B2061863 : Blo 562809 2061863 := bstep (se 1 (by rfl) ⟨1546397, by rfl⟩ : syracuseStep 2061863 = 3092795) B3092795
theorem B3045215 : Blo 562809 3045215 := bstep (se 1 (by rfl) ⟨2283911, by rfl⟩ : syracuseStep 3045215 = 4567823) B4567823
theorem B849839 : Blo 562809 849839 := bstep (se 1 (by rfl) ⟨637379, by rfl⟩ : syracuseStep 849839 = 1274759) B1274759
theorem B2029495 : Blo 562809 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B849929 : Blo 562809 849929 := bstep (se 2 (by rfl) ⟨318723, by rfl⟩ : syracuseStep 849929 = 637447) B637447
theorem B849959 : Blo 562809 849959 := bstep (se 1 (by rfl) ⟨637469, by rfl⟩ : syracuseStep 849959 = 1274939) B1274939
theorem B850043 : Blo 562809 850043 := bstep (se 1 (by rfl) ⟨637532, by rfl⟩ : syracuseStep 850043 = 1275065) B1275065
theorem B850169 : Blo 562809 850169 := bstep (se 2 (by rfl) ⟨318813, by rfl⟩ : syracuseStep 850169 = 637627) B637627
theorem B4061441 : Blo 562809 4061441 := bstep (se 2 (by rfl) ⟨1523040, by rfl⟩ : syracuseStep 4061441 = 3046081) B3046081
theorem B4585729 : Blo 562809 4585729 := bstep (se 2 (by rfl) ⟨1719648, by rfl⟩ : syracuseStep 4585729 = 3439297) B3439297
theorem B1014329 : Blo 562809 1014329 := bstep (se 2 (by rfl) ⟨380373, by rfl⟩ : syracuseStep 1014329 = 760747) B760747
theorem B34667185 : Blo 562809 34667185 := bstep (se 2 (by rfl) ⟨13000194, by rfl⟩ : syracuseStep 34667185 = 26000389) B26000389
theorem B3046099 : Blo 562809 3046099 := bstep (se 1 (by rfl) ⟨2284574, by rfl⟩ : syracuseStep 3046099 = 4569149) B4569149
theorem B2653103 : Blo 562809 2653103 := bstep (se 1 (by rfl) ⟨1989827, by rfl⟩ : syracuseStep 2653103 = 3979655) B3979655
theorem B5438659 : Blo 562809 5438659 := bstep (se 1 (by rfl) ⟨4078994, by rfl⟩ : syracuseStep 5438659 = 8157989) B8157989
theorem B6454565 : Blo 562809 6454565 := bstep (se 4 (by rfl) ⟨605115, by rfl⟩ : syracuseStep 6454565 = 1210231) B1210231
theorem B1899881 : Blo 562809 1899881 := bstep (se 2 (by rfl) ⟨712455, by rfl⟩ : syracuseStep 1899881 = 1424911) B1424911
theorem B11599325 : Blo 562809 11599325 := bstep (se 3 (by rfl) ⟨2174873, by rfl⟩ : syracuseStep 11599325 = 4349747) B4349747
theorem B949799 : Blo 562809 949799 := bstep (se 1 (by rfl) ⟨712349, by rfl⟩ : syracuseStep 949799 = 1424699) B1424699
theorem B950089 : Blo 562809 950089 := bstep (se 2 (by rfl) ⟨356283, by rfl⟩ : syracuseStep 950089 = 712567) B712567
theorem B950123 : Blo 562809 950123 := bstep (se 1 (by rfl) ⟨712592, by rfl⟩ : syracuseStep 950123 = 1425185) B1425185
theorem B1900475 : Blo 562809 1900475 := bstep (se 1 (by rfl) ⟨1425356, by rfl⟩ : syracuseStep 1900475 = 2850713) B2850713
theorem B2850875 : Blo 562809 2850875 := bstep (se 1 (by rfl) ⟨2138156, by rfl⟩ : syracuseStep 2850875 = 4276313) B4276313
theorem B22020173 : Blo 562809 22020173 := bstep (se 3 (by rfl) ⟨4128782, by rfl⟩ : syracuseStep 22020173 = 8257565) B8257565
theorem B1605737 : Blo 562809 1605737 := bstep (se 2 (by rfl) ⟨602151, by rfl⟩ : syracuseStep 1605737 = 1204303) B1204303
theorem B1933523 : Blo 562809 1933523 := bstep (se 1 (by rfl) ⟨1450142, by rfl⟩ : syracuseStep 1933523 = 2900285) B2900285
theorem B1900907 : Blo 562809 1900907 := bstep (se 1 (by rfl) ⟨1425680, by rfl⟩ : syracuseStep 1900907 = 2851361) B2851361
theorem B52986329 : Blo 562809 52986329 := bstep (se 2 (by rfl) ⟨19869873, by rfl⟩ : syracuseStep 52986329 = 39739747) B39739747
theorem B1901177 : Blo 562809 1901177 := bstep (se 2 (by rfl) ⟨712941, by rfl⟩ : syracuseStep 1901177 = 1425883) B1425883
theorem B4293323 : Blo 562809 4293323 := bstep (se 1 (by rfl) ⟨3219992, by rfl⟩ : syracuseStep 4293323 = 6439985) B6439985
theorem B951007 : Blo 562809 951007 := bstep (se 1 (by rfl) ⟨713255, by rfl⟩ : syracuseStep 951007 = 1426511) B1426511
theorem B4719455 : Blo 562809 4719455 := bstep (se 1 (by rfl) ⟨3539591, by rfl⟩ : syracuseStep 4719455 = 7079183) B7079183
theorem B4817825 : Blo 562809 4817825 := bstep (se 2 (by rfl) ⟨1806684, by rfl⟩ : syracuseStep 4817825 = 3613369) B3613369
theorem B2851847 : Blo 562809 2851847 := bstep (se 1 (by rfl) ⟨2138885, by rfl⟩ : syracuseStep 2851847 = 4277771) B4277771
theorem B951439 : Blo 562809 951439 := bstep (se 1 (by rfl) ⟨713579, by rfl⟩ : syracuseStep 951439 = 1427159) B1427159
theorem B1607035 : Blo 562809 1607035 := bstep (se 1 (by rfl) ⟨1205276, by rfl⟩ : syracuseStep 1607035 = 2410553) B2410553
theorem B5440891 : Blo 562809 5440891 := bstep (se 1 (by rfl) ⟨4080668, by rfl⟩ : syracuseStep 5440891 = 8161337) B8161337
theorem B951689 : Blo 562809 951689 := bstep (se 2 (by rfl) ⟨356883, by rfl⟩ : syracuseStep 951689 = 713767) B713767
theorem B2852333 : Blo 562809 2852333 := bstep (se 3 (by rfl) ⟨534812, by rfl⟩ : syracuseStep 2852333 = 1069625) B1069625
theorem B3868249 : Blo 562809 3868249 := bstep (se 2 (by rfl) ⟨1450593, by rfl⟩ : syracuseStep 3868249 = 2901187) B2901187
theorem B3671687 : Blo 562809 3671687 := bstep (se 1 (by rfl) ⟨2753765, by rfl⟩ : syracuseStep 3671687 = 5507531) B5507531
theorem B952121 : Blo 562809 952121 := bstep (se 2 (by rfl) ⟨357045, by rfl⟩ : syracuseStep 952121 = 714091) B714091
theorem B4589389 : Blo 562809 4589389 := bstep (se 3 (by rfl) ⟨860510, by rfl⟩ : syracuseStep 4589389 = 1721021) B1721021
theorem B9635921 : Blo 562809 9635921 := bstep (se 2 (by rfl) ⟨3613470, by rfl⟩ : syracuseStep 9635921 = 7226941) B7226941
theorem B723163 : Blo 562809 723163 := bstep (se 1 (by rfl) ⟨542372, by rfl⟩ : syracuseStep 723163 = 1084745) B1084745
theorem B2853143 : Blo 562809 2853143 := bstep (se 1 (by rfl) ⟨2139857, by rfl⟩ : syracuseStep 2853143 = 4279715) B4279715
theorem B6195491 : Blo 562809 6195491 := bstep (se 1 (by rfl) ⟨4646618, by rfl⟩ : syracuseStep 6195491 = 9293237) B9293237
theorem B1902959 : Blo 562809 1902959 := bstep (se 1 (by rfl) ⟨1427219, by rfl⟩ : syracuseStep 1902959 = 2854439) B2854439
theorem B1608265 : Blo 562809 1608265 := bstep (se 2 (by rfl) ⟨603099, by rfl⟩ : syracuseStep 1608265 = 1206199) B1206199
theorem B953167 : Blo 562809 953167 := bstep (se 1 (by rfl) ⟨714875, by rfl⟩ : syracuseStep 953167 = 1429751) B1429751
theorem B1608619 : Blo 562809 1608619 := bstep (se 1 (by rfl) ⟨1206464, by rfl⟩ : syracuseStep 1608619 = 2412929) B2412929
theorem B1608893 : Blo 562809 1608893 := bstep (se 3 (by rfl) ⟨301667, by rfl⟩ : syracuseStep 1608893 = 603335) B603335
theorem B6884669 : Blo 562809 6884669 := bstep (se 3 (by rfl) ⟨1290875, by rfl⟩ : syracuseStep 6884669 = 2581751) B2581751
theorem B953849 : Blo 562809 953849 := bstep (se 2 (by rfl) ⟨357693, by rfl⟩ : syracuseStep 953849 = 715387) B715387
theorem B1904363 : Blo 562809 1904363 := bstep (se 1 (by rfl) ⟨1428272, by rfl⟩ : syracuseStep 1904363 = 2856545) B2856545
theorem B954119 : Blo 562809 954119 := bstep (se 1 (by rfl) ⟨715589, by rfl⟩ : syracuseStep 954119 = 1431179) B1431179
theorem B2854763 : Blo 562809 2854763 := bstep (se 1 (by rfl) ⟨2141072, by rfl⟩ : syracuseStep 2854763 = 4282145) B4282145
theorem B6983533 : Blo 562809 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B9670913 : Blo 562809 9670913 := bstep (se 2 (by rfl) ⟨3626592, by rfl⟩ : syracuseStep 9670913 = 7253185) B7253185
theorem B5640623 : Blo 562809 5640623 := bstep (se 1 (by rfl) ⟨4230467, by rfl⟩ : syracuseStep 5640623 = 8460935) B8460935
theorem B954875 : Blo 562809 954875 := bstep (se 1 (by rfl) ⟨716156, by rfl⟩ : syracuseStep 954875 = 1432313) B1432313
theorem B22385161 : Blo 562809 22385161 := bstep (se 2 (by rfl) ⟨8394435, by rfl⟩ : syracuseStep 22385161 = 16788871) B16788871
theorem B1905335 : Blo 562809 1905335 := bstep (se 1 (by rfl) ⟨1429001, by rfl⟩ : syracuseStep 1905335 = 2858003) B2858003
theorem B4133711 : Blo 562809 4133711 := bstep (se 1 (by rfl) ⟨3100283, by rfl⟩ : syracuseStep 4133711 = 6200567) B6200567
theorem B955307 : Blo 562809 955307 := bstep (se 1 (by rfl) ⟨716480, by rfl⟩ : syracuseStep 955307 = 1432961) B1432961
theorem B3216509 : Blo 562809 3216509 := bstep (se 3 (by rfl) ⟨603095, by rfl⟩ : syracuseStep 3216509 = 1206191) B1206191
theorem B955847 : Blo 562809 955847 := bstep (se 1 (by rfl) ⟨716885, by rfl⟩ : syracuseStep 955847 = 1433771) B1433771
theorem B562911 : Blo 562809 562911 := bstep (se 1 (by rfl) ⟨422183, by rfl⟩ : syracuseStep 562911 = 844367) B844367
theorem B562991 : Blo 562809 562991 := bstep (se 1 (by rfl) ⟨422243, by rfl⟩ : syracuseStep 562991 = 844487) B844487
theorem B563099 : Blo 562809 563099 := bstep (se 1 (by rfl) ⟨422324, by rfl⟩ : syracuseStep 563099 = 844649) B844649
theorem B563151 : Blo 562809 563151 := bstep (se 1 (by rfl) ⟨422363, by rfl⟩ : syracuseStep 563151 = 844727) B844727
theorem B563175 : Blo 562809 563175 := bstep (se 1 (by rfl) ⟨422381, by rfl⟩ : syracuseStep 563175 = 844763) B844763
theorem B3217441 : Blo 562809 3217441 := bstep (se 2 (by rfl) ⟨1206540, by rfl⟩ : syracuseStep 3217441 = 2413081) B2413081
theorem B3086531 : Blo 562809 3086531 := bstep (se 1 (by rfl) ⟨2314898, by rfl⟩ : syracuseStep 3086531 = 4629797) B4629797
theorem B563487 : Blo 562809 563487 := bstep (se 1 (by rfl) ⟨422615, by rfl⟩ : syracuseStep 563487 = 845231) B845231
theorem B563547 : Blo 562809 563547 := bstep (se 1 (by rfl) ⟨422660, by rfl⟩ : syracuseStep 563547 = 845321) B845321
theorem B563567 : Blo 562809 563567 := bstep (se 1 (by rfl) ⟨422675, by rfl⟩ : syracuseStep 563567 = 845351) B845351
theorem B10328471 : Blo 562809 10328471 := bstep (se 1 (by rfl) ⟨7746353, by rfl⟩ : syracuseStep 10328471 = 15492707) B15492707
theorem B563623 : Blo 562809 563623 := bstep (se 1 (by rfl) ⟨422717, by rfl⟩ : syracuseStep 563623 = 845435) B845435
theorem B563707 : Blo 562809 563707 := bstep (se 1 (by rfl) ⟨422780, by rfl⟩ : syracuseStep 563707 = 845561) B845561
theorem B563775 : Blo 562809 563775 := bstep (se 1 (by rfl) ⟨422831, by rfl⟩ : syracuseStep 563775 = 845663) B845663
theorem B563783 : Blo 562809 563783 := bstep (se 1 (by rfl) ⟨422837, by rfl⟩ : syracuseStep 563783 = 845675) B845675
theorem B1907279 : Blo 562809 1907279 := bstep (se 1 (by rfl) ⟨1430459, by rfl⟩ : syracuseStep 1907279 = 2860919) B2860919
theorem B563935 : Blo 562809 563935 := bstep (se 1 (by rfl) ⟨422951, by rfl⟩ : syracuseStep 563935 = 845903) B845903
theorem B564015 : Blo 562809 564015 := bstep (se 1 (by rfl) ⟨423011, by rfl⟩ : syracuseStep 564015 = 846023) B846023
theorem B4135799 : Blo 562809 4135799 := bstep (se 1 (by rfl) ⟨3101849, by rfl⟩ : syracuseStep 4135799 = 6203699) B6203699
theorem B564123 : Blo 562809 564123 := bstep (se 1 (by rfl) ⟨423092, by rfl⟩ : syracuseStep 564123 = 846185) B846185
theorem B564175 : Blo 562809 564175 := bstep (se 1 (by rfl) ⟨423131, by rfl⟩ : syracuseStep 564175 = 846263) B846263
theorem B564199 : Blo 562809 564199 := bstep (se 1 (by rfl) ⟨423149, by rfl⟩ : syracuseStep 564199 = 846299) B846299
theorem B564511 : Blo 562809 564511 := bstep (se 1 (by rfl) ⟨423383, by rfl⟩ : syracuseStep 564511 = 846767) B846767
theorem B564571 : Blo 562809 564571 := bstep (se 1 (by rfl) ⟨423428, by rfl⟩ : syracuseStep 564571 = 846857) B846857
theorem B564591 : Blo 562809 564591 := bstep (se 1 (by rfl) ⟨423443, by rfl⟩ : syracuseStep 564591 = 846887) B846887
theorem B564647 : Blo 562809 564647 := bstep (se 1 (by rfl) ⟨423485, by rfl⟩ : syracuseStep 564647 = 846971) B846971
theorem B2858489 : Blo 562809 2858489 := bstep (se 2 (by rfl) ⟨1071933, by rfl⟩ : syracuseStep 2858489 = 2143867) B2143867
theorem B564731 : Blo 562809 564731 := bstep (se 1 (by rfl) ⟨423548, by rfl⟩ : syracuseStep 564731 = 847097) B847097
theorem B564799 : Blo 562809 564799 := bstep (se 1 (by rfl) ⟨423599, by rfl⟩ : syracuseStep 564799 = 847199) B847199
theorem B564807 : Blo 562809 564807 := bstep (se 1 (by rfl) ⟨423605, by rfl⟩ : syracuseStep 564807 = 847211) B847211
theorem B564959 : Blo 562809 564959 := bstep (se 1 (by rfl) ⟨423719, by rfl⟩ : syracuseStep 564959 = 847439) B847439
theorem B1908521 : Blo 562809 1908521 := bstep (se 2 (by rfl) ⟨715695, by rfl⟩ : syracuseStep 1908521 = 1431391) B1431391
theorem B565039 : Blo 562809 565039 := bstep (se 1 (by rfl) ⟨423779, by rfl⟩ : syracuseStep 565039 = 847559) B847559
theorem B2858813 : Blo 562809 2858813 := bstep (se 3 (by rfl) ⟨536027, by rfl⟩ : syracuseStep 2858813 = 1072055) B1072055
theorem B565147 : Blo 562809 565147 := bstep (se 1 (by rfl) ⟨423860, by rfl⟩ : syracuseStep 565147 = 847721) B847721
theorem B565199 : Blo 562809 565199 := bstep (se 1 (by rfl) ⟨423899, by rfl⟩ : syracuseStep 565199 = 847799) B847799
theorem B565223 : Blo 562809 565223 := bstep (se 1 (by rfl) ⟨423917, by rfl⟩ : syracuseStep 565223 = 847835) B847835
theorem B565535 : Blo 562809 565535 := bstep (se 1 (by rfl) ⟨424151, by rfl⟩ : syracuseStep 565535 = 848303) B848303
theorem B565595 : Blo 562809 565595 := bstep (se 1 (by rfl) ⟨424196, by rfl⟩ : syracuseStep 565595 = 848393) B848393
theorem B565615 : Blo 562809 565615 := bstep (se 1 (by rfl) ⟨424211, by rfl⟩ : syracuseStep 565615 = 848423) B848423
theorem B4071845 : Blo 562809 4071845 := bstep (se 4 (by rfl) ⟨381735, by rfl⟩ : syracuseStep 4071845 = 763471) B763471
theorem B565671 : Blo 562809 565671 := bstep (se 1 (by rfl) ⟨424253, by rfl⟩ : syracuseStep 565671 = 848507) B848507
theorem B565755 : Blo 562809 565755 := bstep (se 1 (by rfl) ⟨424316, by rfl⟩ : syracuseStep 565755 = 848633) B848633
theorem B6431237 : Blo 562809 6431237 := bstep (se 4 (by rfl) ⟨602928, by rfl⟩ : syracuseStep 6431237 = 1205857) B1205857
theorem B565823 : Blo 562809 565823 := bstep (se 1 (by rfl) ⟨424367, by rfl⟩ : syracuseStep 565823 = 848735) B848735
theorem B565831 : Blo 562809 565831 := bstep (se 1 (by rfl) ⟨424373, by rfl⟩ : syracuseStep 565831 = 848747) B848747
theorem B2138795 : Blo 562809 2138795 := bstep (se 1 (by rfl) ⟨1604096, by rfl⟩ : syracuseStep 2138795 = 3208193) B3208193
theorem B565983 : Blo 562809 565983 := bstep (se 1 (by rfl) ⟨424487, by rfl⟩ : syracuseStep 565983 = 848975) B848975
theorem B566063 : Blo 562809 566063 := bstep (se 1 (by rfl) ⟨424547, by rfl⟩ : syracuseStep 566063 = 849095) B849095
theorem B762779 : Blo 562809 762779 := bstep (se 1 (by rfl) ⟨572084, by rfl⟩ : syracuseStep 762779 = 1144169) B1144169
theorem B566171 : Blo 562809 566171 := bstep (se 1 (by rfl) ⟨424628, by rfl⟩ : syracuseStep 566171 = 849257) B849257
theorem B566223 : Blo 562809 566223 := bstep (se 1 (by rfl) ⟨424667, by rfl⟩ : syracuseStep 566223 = 849335) B849335
theorem B566247 : Blo 562809 566247 := bstep (se 1 (by rfl) ⟨424685, by rfl⟩ : syracuseStep 566247 = 849371) B849371
theorem B11609189 : Blo 562809 11609189 := bstep (se 4 (by rfl) ⟨1088361, by rfl⟩ : syracuseStep 11609189 = 2176723) B2176723
theorem B566559 : Blo 562809 566559 := bstep (se 1 (by rfl) ⟨424919, by rfl⟩ : syracuseStep 566559 = 849839) B849839
theorem B566619 : Blo 562809 566619 := bstep (se 1 (by rfl) ⟨424964, by rfl⟩ : syracuseStep 566619 = 849929) B849929
theorem B1287521 : Blo 562809 1287521 := bstep (se 2 (by rfl) ⟨482820, by rfl⟩ : syracuseStep 1287521 = 965641) B965641
theorem B566639 : Blo 562809 566639 := bstep (se 1 (by rfl) ⟨424979, by rfl⟩ : syracuseStep 566639 = 849959) B849959
theorem B566695 : Blo 562809 566695 := bstep (se 1 (by rfl) ⟨425021, by rfl⟩ : syracuseStep 566695 = 850043) B850043
theorem B566779 : Blo 562809 566779 := bstep (se 1 (by rfl) ⟨425084, by rfl⟩ : syracuseStep 566779 = 850169) B850169
theorem B7251545 : Blo 562809 7251545 := bstep (se 2 (by rfl) ⟨2719329, by rfl⟩ : syracuseStep 7251545 = 5438659) B5438659
theorem B1910735 : Blo 562809 1910735 := bstep (se 1 (by rfl) ⟨1433051, by rfl⟩ : syracuseStep 1910735 = 2866103) B2866103
theorem B3614701 : Blo 562809 3614701 := bstep (se 3 (by rfl) ⟨677756, by rfl⟩ : syracuseStep 3614701 = 1355513) B1355513
theorem B3221633 : Blo 562809 3221633 := bstep (se 2 (by rfl) ⟨1208112, by rfl⟩ : syracuseStep 3221633 = 2416225) B2416225
theorem B4303043 : Blo 562809 4303043 := bstep (se 1 (by rfl) ⟨3227282, by rfl⟩ : syracuseStep 4303043 = 6454565) B6454565
theorem B633199 : Blo 562809 633199 := bstep (se 1 (by rfl) ⟨474899, by rfl⟩ : syracuseStep 633199 = 949799) B949799
theorem B633415 : Blo 562809 633415 := bstep (se 1 (by rfl) ⟨475061, by rfl⟩ : syracuseStep 633415 = 950123) B950123
theorem B4631363 : Blo 562809 4631363 := bstep (se 1 (by rfl) ⟨3473522, by rfl⟩ : syracuseStep 4631363 = 6947045) B6947045
theorem B2861891 : Blo 562809 2861891 := bstep (se 1 (by rfl) ⟨2146418, by rfl⟩ : syracuseStep 2861891 = 4292837) B4292837
theorem B1715087 : Blo 562809 1715087 := bstep (se 1 (by rfl) ⟨1286315, by rfl⟩ : syracuseStep 1715087 = 2572631) B2572631
theorem B1911707 : Blo 562809 1911707 := bstep (se 1 (by rfl) ⟨1433780, by rfl⟩ : syracuseStep 1911707 = 2867561) B2867561
theorem B4959313 : Blo 562809 4959313 := bstep (se 2 (by rfl) ⟨1859742, by rfl⟩ : syracuseStep 4959313 = 3719485) B3719485
theorem B634279 : Blo 562809 634279 := bstep (se 1 (by rfl) ⟨475709, by rfl⟩ : syracuseStep 634279 = 951419) B951419
theorem B1715671 : Blo 562809 1715671 := bstep (se 1 (by rfl) ⟨1286753, by rfl⟩ : syracuseStep 1715671 = 2573507) B2573507
theorem B2141711 : Blo 562809 2141711 := bstep (se 1 (by rfl) ⟨1606283, by rfl⟩ : syracuseStep 2141711 = 3212567) B3212567
theorem B2862701 : Blo 562809 2862701 := bstep (se 3 (by rfl) ⟨536756, by rfl⟩ : syracuseStep 2862701 = 1073513) B1073513
theorem B765775 : Blo 562809 765775 := bstep (se 1 (by rfl) ⟨574331, by rfl⟩ : syracuseStep 765775 = 1148663) B1148663
theorem B1912733 : Blo 562809 1912733 := bstep (se 3 (by rfl) ⟨358637, by rfl⟩ : syracuseStep 1912733 = 717275) B717275
theorem B634855 : Blo 562809 634855 := bstep (se 1 (by rfl) ⟨476141, by rfl⟩ : syracuseStep 634855 = 952283) B952283
theorem B1912841 : Blo 562809 1912841 := bstep (se 2 (by rfl) ⟨717315, by rfl⟩ : syracuseStep 1912841 = 1434631) B1434631
theorem B2404505 : Blo 562809 2404505 := bstep (se 2 (by rfl) ⟨901689, by rfl⟩ : syracuseStep 2404505 = 1803379) B1803379
theorem B4895417 : Blo 562809 4895417 := bstep (se 2 (by rfl) ⟨1835781, by rfl⟩ : syracuseStep 4895417 = 3671563) B3671563
theorem B602959 : Blo 562809 602959 := bstep (se 1 (by rfl) ⟨452219, by rfl⟩ : syracuseStep 602959 = 904439) B904439
theorem B4076689 : Blo 562809 4076689 := bstep (se 2 (by rfl) ⟨1528758, by rfl⟩ : syracuseStep 4076689 = 3057517) B3057517
theorem B2405821 : Blo 562809 2405821 := bstep (se 3 (by rfl) ⟨451091, by rfl⟩ : syracuseStep 2405821 = 902183) B902183
theorem B12531145 : Blo 562809 12531145 := bstep (se 2 (by rfl) ⟨4699179, by rfl⟩ : syracuseStep 12531145 = 9398359) B9398359
theorem B636511 : Blo 562809 636511 := bstep (se 1 (by rfl) ⟨477383, by rfl⟩ : syracuseStep 636511 = 954767) B954767
theorem B4077611 : Blo 562809 4077611 := bstep (se 1 (by rfl) ⟨3058208, by rfl⟩ : syracuseStep 4077611 = 6116417) B6116417
theorem B5421437 : Blo 562809 5421437 := bstep (se 3 (by rfl) ⟨1016519, by rfl⟩ : syracuseStep 5421437 = 2033039) B2033039
theorem B3619727 : Blo 562809 3619727 := bstep (se 1 (by rfl) ⟨2714795, by rfl⟩ : syracuseStep 3619727 = 5429591) B5429591
theorem B9649043 : Blo 562809 9649043 := bstep (se 1 (by rfl) ⟨7236782, by rfl⟩ : syracuseStep 9649043 = 14473565) B14473565
theorem B1522813 : Blo 562809 1522813 := bstep (se 3 (by rfl) ⟨285527, by rfl⟩ : syracuseStep 1522813 = 571055) B571055
theorem B4570705 : Blo 562809 4570705 := bstep (se 2 (by rfl) ⟨1714014, by rfl⟩ : syracuseStep 4570705 = 3428029) B3428029
theorem B4275827 : Blo 562809 4275827 := bstep (se 1 (by rfl) ⟨3206870, by rfl⟩ : syracuseStep 4275827 = 6413741) B6413741
theorem B3227465 : Blo 562809 3227465 := bstep (se 2 (by rfl) ⟨1210299, by rfl⟩ : syracuseStep 3227465 = 2420599) B2420599
theorem B3915649 : Blo 562809 3915649 := bstep (se 2 (by rfl) ⟨1468368, by rfl⟩ : syracuseStep 3915649 = 2936737) B2936737
theorem B2408777 : Blo 562809 2408777 := bstep (se 2 (by rfl) ⟨903291, by rfl⟩ : syracuseStep 2408777 = 1806583) B1806583
theorem B2408879 : Blo 562809 2408879 := bstep (se 1 (by rfl) ⟨1806659, by rfl⟩ : syracuseStep 2408879 = 3613319) B3613319
theorem B803449 : Blo 562809 803449 := bstep (se 2 (by rfl) ⟨301293, by rfl⟩ : syracuseStep 803449 = 602587) B602587
theorem B8373061 : Blo 562809 8373061 := bstep (se 4 (by rfl) ⟨784974, by rfl⟩ : syracuseStep 8373061 = 1569949) B1569949
theorem B2868047 : Blo 562809 2868047 := bstep (se 1 (by rfl) ⟨2151035, by rfl⟩ : syracuseStep 2868047 = 4302071) B4302071
theorem B1426319 : Blo 562809 1426319 := bstep (se 1 (by rfl) ⟨1069739, by rfl⟩ : syracuseStep 1426319 = 2139479) B2139479
theorem B2638855 : Blo 562809 2638855 := bstep (se 1 (by rfl) ⟨1979141, by rfl⟩ : syracuseStep 2638855 = 3958283) B3958283
theorem B3425287 : Blo 562809 3425287 := bstep (se 1 (by rfl) ⟨2568965, by rfl⟩ : syracuseStep 3425287 = 5137931) B5137931
theorem B4277285 : Blo 562809 4277285 := bstep (se 4 (by rfl) ⟨400995, by rfl⟩ : syracuseStep 4277285 = 801991) B801991
theorem B9684035 : Blo 562809 9684035 := bstep (se 1 (by rfl) ⟨7263026, by rfl⟩ : syracuseStep 9684035 = 14526053) B14526053
theorem B2868371 : Blo 562809 2868371 := bstep (se 1 (by rfl) ⟨2151278, by rfl⟩ : syracuseStep 2868371 = 4302557) B4302557
theorem B2147543 : Blo 562809 2147543 := bstep (se 1 (by rfl) ⟨1610657, by rfl⟩ : syracuseStep 2147543 = 3221315) B3221315
theorem B7259543 : Blo 562809 7259543 := bstep (se 1 (by rfl) ⟨5444657, by rfl⟩ : syracuseStep 7259543 = 10889315) B10889315
theorem B13878701 : Blo 562809 13878701 := bstep (se 3 (by rfl) ⟨2602256, by rfl⟩ : syracuseStep 13878701 = 5204513) B5204513
theorem B35276309 : Blo 562809 35276309 := bstep (se 6 (by rfl) ⟨826788, by rfl⟩ : syracuseStep 35276309 = 1653577) B1653577
theorem B24823331 : Blo 562809 24823331 := bstep (se 1 (by rfl) ⟨18617498, by rfl⟩ : syracuseStep 24823331 = 37234997) B37234997
theorem B1427179 : Blo 562809 1427179 := bstep (se 1 (by rfl) ⟨1070384, by rfl⟩ : syracuseStep 1427179 = 2140769) B2140769
theorem B1722217 : Blo 562809 1722217 := bstep (se 2 (by rfl) ⟨645831, by rfl⟩ : syracuseStep 1722217 = 1291663) B1291663
theorem B2705993 : Blo 562809 2705993 := bstep (se 2 (by rfl) ⟨1014747, by rfl⟩ : syracuseStep 2705993 = 2029495) B2029495
theorem B1428151 : Blo 562809 1428151 := bstep (se 1 (by rfl) ⟨1071113, by rfl⟩ : syracuseStep 1428151 = 2142227) B2142227
theorem B1428455 : Blo 562809 1428455 := bstep (se 1 (by rfl) ⟨1071341, by rfl⟩ : syracuseStep 1428455 = 2142683) B2142683
theorem B6114305 : Blo 562809 6114305 := bstep (se 2 (by rfl) ⟨2292864, by rfl⟩ : syracuseStep 6114305 = 4585729) B4585729
theorem B2149699 : Blo 562809 2149699 := bstep (se 1 (by rfl) ⟨1612274, by rfl⟩ : syracuseStep 2149699 = 3224549) B3224549
theorem B642427 : Blo 562809 642427 := bstep (se 1 (by rfl) ⟨481820, by rfl⟩ : syracuseStep 642427 = 963641) B963641
theorem B46222913 : Blo 562809 46222913 := bstep (se 2 (by rfl) ⟨17333592, by rfl⟩ : syracuseStep 46222913 = 34667185) B34667185
theorem B2150003 : Blo 562809 2150003 := bstep (se 1 (by rfl) ⟨1612502, by rfl⟩ : syracuseStep 2150003 = 3225005) B3225005
theorem B2412193 : Blo 562809 2412193 := bstep (se 2 (by rfl) ⟨904572, by rfl⟩ : syracuseStep 2412193 = 1809145) B1809145
theorem B2150185 : Blo 562809 2150185 := bstep (se 2 (by rfl) ⟨806319, by rfl⟩ : syracuseStep 2150185 = 1612639) B1612639
theorem B2150459 : Blo 562809 2150459 := bstep (se 1 (by rfl) ⟨1612844, by rfl⟩ : syracuseStep 2150459 = 3225689) B3225689
theorem B1429609 : Blo 562809 1429609 := bstep (se 2 (by rfl) ⟨536103, by rfl⟩ : syracuseStep 1429609 = 1072207) B1072207
theorem B2707627 : Blo 562809 2707627 := bstep (se 1 (by rfl) ⟨2030720, by rfl⟩ : syracuseStep 2707627 = 4061441) B4061441
theorem B676219 : Blo 562809 676219 := bstep (se 1 (by rfl) ⟨507164, by rfl⟩ : syracuseStep 676219 = 1014329) B1014329
theorem B1430095 : Blo 562809 1430095 := bstep (se 1 (by rfl) ⟨1072571, by rfl⟩ : syracuseStep 1430095 = 2145143) B2145143
theorem B3298157 : Blo 562809 3298157 := bstep (se 3 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 3298157 = 1236809) B1236809
theorem B1266587 : Blo 562809 1266587 := bstep (se 1 (by rfl) ⟨949940, by rfl⟩ : syracuseStep 1266587 = 1899881) B1899881
theorem B1266785 : Blo 562809 1266785 := bstep (se 2 (by rfl) ⟨475044, by rfl⟩ : syracuseStep 1266785 = 950089) B950089
theorem B1430743 : Blo 562809 1430743 := bstep (se 1 (by rfl) ⟨1073057, by rfl⟩ : syracuseStep 1430743 = 2146115) B2146115
theorem B1266983 : Blo 562809 1266983 := bstep (se 1 (by rfl) ⟨950237, by rfl⟩ : syracuseStep 1266983 = 1900475) B1900475
theorem B2741627 : Blo 562809 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B10868093 : Blo 562809 10868093 := bstep (se 3 (by rfl) ⟨2037767, by rfl⟩ : syracuseStep 10868093 = 4075535) B4075535
theorem B2905537 : Blo 562809 2905537 := bstep (se 2 (by rfl) ⟨1089576, by rfl⟩ : syracuseStep 2905537 = 2179153) B2179153
theorem B1431047 : Blo 562809 1431047 := bstep (se 1 (by rfl) ⟨1073285, by rfl⟩ : syracuseStep 1431047 = 2146571) B2146571
theorem B10835491 : Blo 562809 10835491 := bstep (se 1 (by rfl) ⟨8126618, by rfl⟩ : syracuseStep 10835491 = 16253237) B16253237
theorem B1267361 : Blo 562809 1267361 := bstep (se 2 (by rfl) ⟨475260, by rfl⟩ : syracuseStep 1267361 = 950521) B950521
theorem B1431503 : Blo 562809 1431503 := bstep (se 1 (by rfl) ⟨1073627, by rfl⟩ : syracuseStep 1431503 = 2147255) B2147255
theorem B1267721 : Blo 562809 1267721 := bstep (se 2 (by rfl) ⟨475395, by rfl⟩ : syracuseStep 1267721 = 950791) B950791
theorem B4577323 : Blo 562809 4577323 := bstep (se 1 (by rfl) ⟨3432992, by rfl⟩ : syracuseStep 4577323 = 6865985) B6865985
theorem B24401999 : Blo 562809 24401999 := bstep (se 1 (by rfl) ⟨18301499, by rfl⟩ : syracuseStep 24401999 = 36602999) B36602999
theorem B678175 : Blo 562809 678175 := bstep (se 1 (by rfl) ⟨508631, by rfl⟩ : syracuseStep 678175 = 1017263) B1017263
theorem B1202543 : Blo 562809 1202543 := bstep (se 1 (by rfl) ⟨901907, by rfl⟩ : syracuseStep 1202543 = 1803815) B1803815
theorem B1268135 : Blo 562809 1268135 := bstep (se 1 (by rfl) ⟨951101, by rfl⟩ : syracuseStep 1268135 = 1902203) B1902203
theorem B1432019 : Blo 562809 1432019 := bstep (se 1 (by rfl) ⟨1074014, by rfl⟩ : syracuseStep 1432019 = 2148029) B2148029
theorem B1268243 : Blo 562809 1268243 := bstep (se 1 (by rfl) ⟨951182, by rfl⟩ : syracuseStep 1268243 = 1902365) B1902365
theorem B2415167 : Blo 562809 2415167 := bstep (se 1 (by rfl) ⟨1811375, by rfl⟩ : syracuseStep 2415167 = 3622751) B3622751
theorem B1268297 : Blo 562809 1268297 := bstep (se 2 (by rfl) ⟨475611, by rfl⟩ : syracuseStep 1268297 = 951223) B951223
theorem B4119113 : Blo 562809 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B4283117 : Blo 562809 4283117 := bstep (se 3 (by rfl) ⟨803084, by rfl⟩ : syracuseStep 4283117 = 1606169) B1606169
theorem B12245903 : Blo 562809 12245903 := bstep (se 1 (by rfl) ⟨9184427, by rfl⟩ : syracuseStep 12245903 = 18368855) B18368855
theorem B1432475 : Blo 562809 1432475 := bstep (se 1 (by rfl) ⟨1074356, by rfl⟩ : syracuseStep 1432475 = 2148713) B2148713
theorem B1268711 : Blo 562809 1268711 := bstep (se 1 (by rfl) ⟨951533, by rfl⟩ : syracuseStep 1268711 = 1903067) B1903067
theorem B1269089 : Blo 562809 1269089 := bstep (se 2 (by rfl) ⟨475908, by rfl⟩ : syracuseStep 1269089 = 951817) B951817
theorem B1269179 : Blo 562809 1269179 := bstep (se 1 (by rfl) ⟨951884, by rfl⟩ : syracuseStep 1269179 = 1903769) B1903769
theorem B1269305 : Blo 562809 1269305 := bstep (se 2 (by rfl) ⟨475989, by rfl⟩ : syracuseStep 1269305 = 951979) B951979
theorem B712415 : Blo 562809 712415 := bstep (se 1 (by rfl) ⟨534311, by rfl⟩ : syracuseStep 712415 = 1068623) B1068623
theorem B1629931 : Blo 562809 1629931 := bstep (se 1 (by rfl) ⟨1222448, by rfl⟩ : syracuseStep 1629931 = 2444897) B2444897
theorem B1433609 : Blo 562809 1433609 := bstep (se 2 (by rfl) ⟨537603, by rfl⟩ : syracuseStep 1433609 = 1075207) B1075207
theorem B1269971 : Blo 562809 1269971 := bstep (se 1 (by rfl) ⟨952478, by rfl⟩ : syracuseStep 1269971 = 1904957) B1904957
theorem B1270025 : Blo 562809 1270025 := bstep (se 2 (by rfl) ⟨476259, by rfl⟩ : syracuseStep 1270025 = 952519) B952519
theorem B1433963 : Blo 562809 1433963 := bstep (se 1 (by rfl) ⟨1075472, by rfl⟩ : syracuseStep 1433963 = 2150945) B2150945
theorem B1270241 : Blo 562809 1270241 := bstep (se 2 (by rfl) ⟨476340, by rfl⟩ : syracuseStep 1270241 = 952681) B952681
theorem B844283 : Blo 562809 844283 := bstep (se 1 (by rfl) ⟨633212, by rfl⟩ : syracuseStep 844283 = 1266425) B1266425
theorem B6382091 : Blo 562809 6382091 := bstep (se 1 (by rfl) ⟨4786568, by rfl⟩ : syracuseStep 6382091 = 9573137) B9573137
theorem B844409 : Blo 562809 844409 := bstep (se 2 (by rfl) ⟨316653, by rfl⟩ : syracuseStep 844409 = 633307) B633307
theorem B844463 : Blo 562809 844463 := bstep (se 1 (by rfl) ⟨633347, by rfl⟩ : syracuseStep 844463 = 1266695) B1266695
theorem B1434287 : Blo 562809 1434287 := bstep (se 1 (by rfl) ⟨1075715, by rfl⟩ : syracuseStep 1434287 = 2151431) B2151431
theorem B844511 : Blo 562809 844511 := bstep (se 1 (by rfl) ⟨633383, by rfl⟩ : syracuseStep 844511 = 1266767) B1266767
theorem B1270547 : Blo 562809 1270547 := bstep (se 1 (by rfl) ⟨952910, by rfl⟩ : syracuseStep 1270547 = 1905821) B1905821
theorem B1073999 : Blo 562809 1073999 := bstep (se 1 (by rfl) ⟨805499, by rfl⟩ : syracuseStep 1073999 = 1610999) B1610999
theorem B6415199 : Blo 562809 6415199 := bstep (se 1 (by rfl) ⟨4811399, by rfl⟩ : syracuseStep 6415199 = 9622799) B9622799
theorem B2417627 : Blo 562809 2417627 := bstep (se 1 (by rfl) ⟨1813220, by rfl⟩ : syracuseStep 2417627 = 3626441) B3626441
theorem B844775 : Blo 562809 844775 := bstep (se 1 (by rfl) ⟨633581, by rfl⟩ : syracuseStep 844775 = 1267163) B1267163
theorem B1074151 : Blo 562809 1074151 := bstep (se 1 (by rfl) ⟨805613, by rfl⟩ : syracuseStep 1074151 = 1611227) B1611227
theorem B3630055 : Blo 562809 3630055 := bstep (se 1 (by rfl) ⟨2722541, by rfl⟩ : syracuseStep 3630055 = 5445083) B5445083
theorem B1434611 : Blo 562809 1434611 := bstep (se 1 (by rfl) ⟨1075958, by rfl⟩ : syracuseStep 1434611 = 2151917) B2151917
theorem B1205371 : Blo 562809 1205371 := bstep (se 1 (by rfl) ⟨904028, by rfl⟩ : syracuseStep 1205371 = 1808057) B1808057
theorem B1270907 : Blo 562809 1270907 := bstep (se 1 (by rfl) ⟨953180, by rfl⟩ : syracuseStep 1270907 = 1906361) B1906361
theorem B1205447 : Blo 562809 1205447 := bstep (se 1 (by rfl) ⟨904085, by rfl⟩ : syracuseStep 1205447 = 1808171) B1808171
theorem B845033 : Blo 562809 845033 := bstep (se 2 (by rfl) ⟨316887, by rfl⟩ : syracuseStep 845033 = 633775) B633775
theorem B1271033 : Blo 562809 1271033 := bstep (se 2 (by rfl) ⟨476637, by rfl⟩ : syracuseStep 1271033 = 953275) B953275
theorem B845087 : Blo 562809 845087 := bstep (se 1 (by rfl) ⟨633815, by rfl⟩ : syracuseStep 845087 = 1267631) B1267631
theorem B1271177 : Blo 562809 1271177 := bstep (se 2 (by rfl) ⟨476691, by rfl⟩ : syracuseStep 1271177 = 953383) B953383
theorem B845255 : Blo 562809 845255 := bstep (se 1 (by rfl) ⟨633941, by rfl⟩ : syracuseStep 845255 = 1267883) B1267883
theorem B1271303 : Blo 562809 1271303 := bstep (se 1 (by rfl) ⟨953477, by rfl⟩ : syracuseStep 1271303 = 1906955) B1906955
theorem B714415 : Blo 562809 714415 := bstep (se 1 (by rfl) ⟨535811, by rfl⟩ : syracuseStep 714415 = 1071623) B1071623
theorem B1271483 : Blo 562809 1271483 := bstep (se 1 (by rfl) ⟨953612, by rfl⟩ : syracuseStep 1271483 = 1907225) B1907225
theorem B845609 : Blo 562809 845609 := bstep (se 2 (by rfl) ⟨317103, by rfl⟩ : syracuseStep 845609 = 634207) B634207
theorem B845615 : Blo 562809 845615 := bstep (se 1 (by rfl) ⟨634211, by rfl⟩ : syracuseStep 845615 = 1268423) B1268423
theorem B1271609 : Blo 562809 1271609 := bstep (se 2 (by rfl) ⟨476853, by rfl⟩ : syracuseStep 1271609 = 953707) B953707
theorem B8120573 : Blo 562809 8120573 := bstep (se 3 (by rfl) ⟨1522607, by rfl⟩ : syracuseStep 8120573 = 3045215) B3045215
theorem B846089 : Blo 562809 846089 := bstep (se 2 (by rfl) ⟨317283, by rfl⟩ : syracuseStep 846089 = 634567) B634567
theorem B846191 : Blo 562809 846191 := bstep (se 1 (by rfl) ⟨634643, by rfl⟩ : syracuseStep 846191 = 1269287) B1269287
theorem B1272239 : Blo 562809 1272239 := bstep (se 1 (by rfl) ⟨954179, by rfl⟩ : syracuseStep 1272239 = 1908359) B1908359
theorem B1272275 : Blo 562809 1272275 := bstep (se 1 (by rfl) ⟨954206, by rfl⟩ : syracuseStep 1272275 = 1908413) B1908413
theorem B1272383 : Blo 562809 1272383 := bstep (se 1 (by rfl) ⟨954287, by rfl⟩ : syracuseStep 1272383 = 1908575) B1908575
theorem B846407 : Blo 562809 846407 := bstep (se 1 (by rfl) ⟨634805, by rfl⟩ : syracuseStep 846407 = 1269611) B1269611
theorem B2288207 : Blo 562809 2288207 := bstep (se 1 (by rfl) ⟨1716155, by rfl⟩ : syracuseStep 2288207 = 3432311) B3432311
theorem B846443 : Blo 562809 846443 := bstep (se 1 (by rfl) ⟨634832, by rfl⟩ : syracuseStep 846443 = 1269665) B1269665
theorem B1272491 : Blo 562809 1272491 := bstep (se 1 (by rfl) ⟨954368, by rfl⟩ : syracuseStep 1272491 = 1908737) B1908737
theorem B846671 : Blo 562809 846671 := bstep (se 1 (by rfl) ⟨635003, by rfl⟩ : syracuseStep 846671 = 1270007) B1270007
theorem B6450191 : Blo 562809 6450191 := bstep (se 1 (by rfl) ⟨4837643, by rfl⟩ : syracuseStep 6450191 = 9675287) B9675287
theorem B2419901 : Blo 562809 2419901 := bstep (se 3 (by rfl) ⟨453731, by rfl⟩ : syracuseStep 2419901 = 907463) B907463
theorem B1273031 : Blo 562809 1273031 := bstep (se 1 (by rfl) ⟨954773, by rfl⟩ : syracuseStep 1273031 = 1909547) B1909547
theorem B847067 : Blo 562809 847067 := bstep (se 1 (by rfl) ⟨635300, by rfl⟩ : syracuseStep 847067 = 1270601) B1270601
theorem B1273211 : Blo 562809 1273211 := bstep (se 1 (by rfl) ⟨954908, by rfl⟩ : syracuseStep 1273211 = 1909817) B1909817
theorem B847241 : Blo 562809 847241 := bstep (se 2 (by rfl) ⟨317715, by rfl⟩ : syracuseStep 847241 = 635431) B635431
theorem B1273337 : Blo 562809 1273337 := bstep (se 2 (by rfl) ⟨477501, by rfl⟩ : syracuseStep 1273337 = 955003) B955003
theorem B716359 : Blo 562809 716359 := bstep (se 1 (by rfl) ⟨537269, by rfl⟩ : syracuseStep 716359 = 1074539) B1074539
theorem B1273427 : Blo 562809 1273427 := bstep (se 1 (by rfl) ⟨955070, by rfl⟩ : syracuseStep 1273427 = 1910141) B1910141
theorem B3862225 : Blo 562809 3862225 := bstep (se 2 (by rfl) ⟨1448334, by rfl⟩ : syracuseStep 3862225 = 2896669) B2896669
theorem B847595 : Blo 562809 847595 := bstep (se 1 (by rfl) ⟨635696, by rfl⟩ : syracuseStep 847595 = 1271393) B1271393
theorem B1273607 : Blo 562809 1273607 := bstep (se 1 (by rfl) ⟨955205, by rfl⟩ : syracuseStep 1273607 = 1910411) B1910411
theorem B1208105 : Blo 562809 1208105 := bstep (se 2 (by rfl) ⟨453039, by rfl⟩ : syracuseStep 1208105 = 906079) B906079
theorem B847823 : Blo 562809 847823 := bstep (se 1 (by rfl) ⟨635867, by rfl⟩ : syracuseStep 847823 = 1271735) B1271735
theorem B848219 : Blo 562809 848219 := bstep (se 1 (by rfl) ⟨636164, by rfl⟩ : syracuseStep 848219 = 1272329) B1272329
theorem B12185963 : Blo 562809 12185963 := bstep (se 1 (by rfl) ⟨9139472, by rfl⟩ : syracuseStep 12185963 = 18278945) B18278945
theorem B1274219 : Blo 562809 1274219 := bstep (se 1 (by rfl) ⟨955664, by rfl⟩ : syracuseStep 1274219 = 1911329) B1911329
theorem B1274363 : Blo 562809 1274363 := bstep (se 1 (by rfl) ⟨955772, by rfl⟩ : syracuseStep 1274363 = 1911545) B1911545
theorem B848447 : Blo 562809 848447 := bstep (se 1 (by rfl) ⟨636335, by rfl⟩ : syracuseStep 848447 = 1272671) B1272671
theorem B1274489 : Blo 562809 1274489 := bstep (se 2 (by rfl) ⟨477933, by rfl⟩ : syracuseStep 1274489 = 955867) B955867
theorem B1274543 : Blo 562809 1274543 := bstep (se 1 (by rfl) ⟨955907, by rfl⟩ : syracuseStep 1274543 = 1911815) B1911815
theorem B848567 : Blo 562809 848567 := bstep (se 1 (by rfl) ⟨636425, by rfl⟩ : syracuseStep 848567 = 1272851) B1272851
theorem B1274615 : Blo 562809 1274615 := bstep (se 1 (by rfl) ⟨955961, by rfl⟩ : syracuseStep 1274615 = 1911923) B1911923
theorem B2716409 : Blo 562809 2716409 := bstep (se 2 (by rfl) ⟨1018653, by rfl⟩ : syracuseStep 2716409 = 2037307) B2037307
theorem B848795 : Blo 562809 848795 := bstep (se 1 (by rfl) ⟨636596, by rfl⟩ : syracuseStep 848795 = 1273193) B1273193
theorem B6091685 : Blo 562809 6091685 := bstep (se 4 (by rfl) ⟨571095, by rfl⟩ : syracuseStep 6091685 = 1142191) B1142191
theorem B1274795 : Blo 562809 1274795 := bstep (se 1 (by rfl) ⟨956096, by rfl⟩ : syracuseStep 1274795 = 1912193) B1912193
theorem B1930337 : Blo 562809 1930337 := bstep (se 2 (by rfl) ⟨723876, by rfl⟩ : syracuseStep 1930337 = 1447753) B1447753
theorem B11728151 : Blo 562809 11728151 := bstep (se 1 (by rfl) ⟨8796113, by rfl⟩ : syracuseStep 11728151 = 17592227) B17592227
theorem B849191 : Blo 562809 849191 := bstep (se 1 (by rfl) ⟨636893, by rfl⟩ : syracuseStep 849191 = 1273787) B1273787
theorem B849275 : Blo 562809 849275 := bstep (se 1 (by rfl) ⟨636956, by rfl⟩ : syracuseStep 849275 = 1273913) B1273913
theorem B849401 : Blo 562809 849401 := bstep (se 2 (by rfl) ⟨318525, by rfl⟩ : syracuseStep 849401 = 637051) B637051
theorem B849503 : Blo 562809 849503 := bstep (se 1 (by rfl) ⟨637127, by rfl⟩ : syracuseStep 849503 = 1274255) B1274255
theorem B849719 : Blo 562809 849719 := bstep (se 1 (by rfl) ⟨637289, by rfl⟩ : syracuseStep 849719 = 1274579) B1274579
theorem B5437277 : Blo 562809 5437277 := bstep (se 3 (by rfl) ⟨1019489, by rfl⟩ : syracuseStep 5437277 = 2038979) B2038979
theorem B850025 : Blo 562809 850025 := bstep (se 2 (by rfl) ⟨318759, by rfl⟩ : syracuseStep 850025 = 637519) B637519
theorem B2029697 : Blo 562809 2029697 := bstep (se 2 (by rfl) ⟨761136, by rfl⟩ : syracuseStep 2029697 = 1522273) B1522273
theorem B4061465 : Blo 562809 4061465 := bstep (se 2 (by rfl) ⟨1523049, by rfl⟩ : syracuseStep 4061465 = 3046099) B3046099
theorem B4290893 : Blo 562809 4290893 := bstep (se 3 (by rfl) ⟨804542, by rfl⟩ : syracuseStep 4290893 = 1609085) B1609085
theorem B1374575 : Blo 562809 1374575 := bstep (se 1 (by rfl) ⟨1030931, by rfl⟩ : syracuseStep 1374575 = 2061863) B2061863
theorem B1735231 : Blo 562809 1735231 := bstep (se 1 (by rfl) ⟨1301423, by rfl⟩ : syracuseStep 1735231 = 2602847) B2602847
theorem B7731845 : Blo 562809 7731845 := bstep (se 4 (by rfl) ⟨724860, by rfl⟩ : syracuseStep 7731845 = 1449721) B1449721
theorem B1932427 : Blo 562809 1932427 := bstep (se 1 (by rfl) ⟨1449320, by rfl⟩ : syracuseStep 1932427 = 2898641) B2898641
theorem B1768735 : Blo 562809 1768735 := bstep (se 1 (by rfl) ⟨1326551, by rfl⟩ : syracuseStep 1768735 = 2653103) B2653103
theorem B5144057 : Blo 562809 5144057 := bstep (se 2 (by rfl) ⟨1929021, by rfl⟩ : syracuseStep 5144057 = 3858043) B3858043
theorem B7732883 : Blo 562809 7732883 := bstep (se 1 (by rfl) ⟨5799662, by rfl⟩ : syracuseStep 7732883 = 11599325) B11599325
theorem B1900583 : Blo 562809 1900583 := bstep (se 1 (by rfl) ⟨1425437, by rfl⟩ : syracuseStep 1900583 = 2850875) B2850875
theorem B14680115 : Blo 562809 14680115 := bstep (se 1 (by rfl) ⟨11010086, by rfl⟩ : syracuseStep 14680115 = 22020173) B22020173
theorem B1605851 : Blo 562809 1605851 := bstep (se 1 (by rfl) ⟨1204388, by rfl⟩ : syracuseStep 1605851 = 2408777) B2408777
theorem B1605919 : Blo 562809 1605919 := bstep (se 1 (by rfl) ⟨1204439, by rfl⟩ : syracuseStep 1605919 = 2408879) B2408879
theorem B35324219 : Blo 562809 35324219 := bstep (se 1 (by rfl) ⟨26493164, by rfl⟩ : syracuseStep 35324219 = 52986329) B52986329
theorem B3146303 : Blo 562809 3146303 := bstep (se 1 (by rfl) ⟨2359727, by rfl⟩ : syracuseStep 3146303 = 4719455) B4719455
theorem B950879 : Blo 562809 950879 := bstep (se 1 (by rfl) ⟨713159, by rfl⟩ : syracuseStep 950879 = 1426319) B1426319
theorem B3211883 : Blo 562809 3211883 := bstep (se 1 (by rfl) ⟨2408912, by rfl⟩ : syracuseStep 3211883 = 4817825) B4817825
theorem B1901231 : Blo 562809 1901231 := bstep (se 1 (by rfl) ⟨1425923, by rfl⟩ : syracuseStep 1901231 = 2851847) B2851847
theorem B2851523 : Blo 562809 2851523 := bstep (se 1 (by rfl) ⟨2138642, by rfl⟩ : syracuseStep 2851523 = 4277285) B4277285
theorem B6456023 : Blo 562809 6456023 := bstep (se 1 (by rfl) ⟨4842017, by rfl⟩ : syracuseStep 6456023 = 9684035) B9684035
theorem B1901555 : Blo 562809 1901555 := bstep (se 1 (by rfl) ⟨1426166, by rfl⟩ : syracuseStep 1901555 = 2852333) B2852333
theorem B16548887 : Blo 562809 16548887 := bstep (se 1 (by rfl) ⟨12411665, by rfl⟩ : syracuseStep 16548887 = 24823331) B24823331
theorem B6423947 : Blo 562809 6423947 := bstep (se 1 (by rfl) ⟨4817960, by rfl⟩ : syracuseStep 6423947 = 9635921) B9635921
theorem B1607161 : Blo 562809 1607161 := bstep (se 2 (by rfl) ⟨602685, by rfl⟩ : syracuseStep 1607161 = 1205371) B1205371
theorem B1902095 : Blo 562809 1902095 := bstep (se 1 (by rfl) ⟨1426571, by rfl⟩ : syracuseStep 1902095 = 2853143) B2853143
theorem B4130327 : Blo 562809 4130327 := bstep (se 1 (by rfl) ⟨3097745, by rfl⟩ : syracuseStep 4130327 = 6195491) B6195491
theorem B1803995 : Blo 562809 1803995 := bstep (se 1 (by rfl) ⟨1352996, by rfl⟩ : syracuseStep 1803995 = 2705993) B2705993
theorem B952303 : Blo 562809 952303 := bstep (se 1 (by rfl) ⟨714227, by rfl⟩ : syracuseStep 952303 = 1428455) B1428455
theorem B4589779 : Blo 562809 4589779 := bstep (se 1 (by rfl) ⟨3442334, by rfl⟩ : syracuseStep 4589779 = 6884669) B6884669
theorem B952553 : Blo 562809 952553 := bstep (se 2 (by rfl) ⟨357207, by rfl⟩ : syracuseStep 952553 = 714415) B714415
theorem B1902905 : Blo 562809 1902905 := bstep (se 2 (by rfl) ⟨713589, by rfl⟩ : syracuseStep 1902905 = 1427179) B1427179
theorem B2034077 : Blo 562809 2034077 := bstep (se 3 (by rfl) ⟨381389, by rfl⟩ : syracuseStep 2034077 = 762779) B762779
theorem B2296289 : Blo 562809 2296289 := bstep (se 2 (by rfl) ⟨861108, by rfl⟩ : syracuseStep 2296289 = 1722217) B1722217
theorem B1903175 : Blo 562809 1903175 := bstep (se 1 (by rfl) ⟨1427381, by rfl⟩ : syracuseStep 1903175 = 2854763) B2854763
theorem B4819601 : Blo 562809 4819601 := bstep (se 2 (by rfl) ⟨1807350, by rfl⟩ : syracuseStep 4819601 = 3614701) B3614701
theorem B3214525 : Blo 562809 3214525 := bstep (se 3 (by rfl) ⟨602723, by rfl⟩ : syracuseStep 3214525 = 1205447) B1205447
theorem B2198771 : Blo 562809 2198771 := bstep (se 1 (by rfl) ⟨1649078, by rfl⟩ : syracuseStep 2198771 = 3298157) B3298157
theorem B1904201 : Blo 562809 1904201 := bstep (se 2 (by rfl) ⟨714075, by rfl⟩ : syracuseStep 1904201 = 1428151) B1428151
theorem B7245395 : Blo 562809 7245395 := bstep (se 1 (by rfl) ⟨5434046, by rfl⟩ : syracuseStep 7245395 = 10868093) B10868093
theorem B7311005 : Blo 562809 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B954031 : Blo 562809 954031 := bstep (se 1 (by rfl) ⟨715523, by rfl⟩ : syracuseStep 954031 = 1431047) B1431047
theorem B954335 : Blo 562809 954335 := bstep (se 1 (by rfl) ⟨715751, by rfl⟩ : syracuseStep 954335 = 1431503) B1431503
theorem B6885647 : Blo 562809 6885647 := bstep (se 1 (by rfl) ⟨5164235, by rfl⟩ : syracuseStep 6885647 = 10328471) B10328471
theorem B954679 : Blo 562809 954679 := bstep (se 1 (by rfl) ⟨716009, by rfl⟩ : syracuseStep 954679 = 1432019) B1432019
theorem B1610111 : Blo 562809 1610111 := bstep (se 1 (by rfl) ⟨1207583, by rfl⟩ : syracuseStep 1610111 = 2415167) B2415167
theorem B2855411 : Blo 562809 2855411 := bstep (se 1 (by rfl) ⟨2141558, by rfl⟩ : syracuseStep 2855411 = 4283117) B4283117
theorem B2757199 : Blo 562809 2757199 := bstep (se 1 (by rfl) ⟨2067899, by rfl⟩ : syracuseStep 2757199 = 4135799) B4135799
theorem B8163935 : Blo 562809 8163935 := bstep (se 1 (by rfl) ⟨6122951, by rfl⟩ : syracuseStep 8163935 = 12245903) B12245903
theorem B954983 : Blo 562809 954983 := bstep (se 1 (by rfl) ⟨716237, by rfl⟩ : syracuseStep 954983 = 1432475) B1432475
theorem B955145 : Blo 562809 955145 := bstep (se 2 (by rfl) ⟨358179, by rfl⟩ : syracuseStep 955145 = 716359) B716359
theorem B3216257 : Blo 562809 3216257 := bstep (se 2 (by rfl) ⟨1206096, by rfl⟩ : syracuseStep 3216257 = 2412193) B2412193
theorem B1905659 : Blo 562809 1905659 := bstep (se 1 (by rfl) ⟨1429244, by rfl⟩ : syracuseStep 1905659 = 2858489) B2858489
theorem B1021033 : Blo 562809 1021033 := bstep (se 2 (by rfl) ⟨382887, by rfl⟩ : syracuseStep 1021033 = 765775) B765775
theorem B9311377 : Blo 562809 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B1905875 : Blo 562809 1905875 := bstep (se 1 (by rfl) ⟨1429406, by rfl⟩ : syracuseStep 1905875 = 2858813) B2858813
theorem B955739 : Blo 562809 955739 := bstep (se 1 (by rfl) ⟨716804, by rfl⟩ : syracuseStep 955739 = 1433609) B1433609
theorem B1906145 : Blo 562809 1906145 := bstep (se 2 (by rfl) ⟨714804, by rfl⟩ : syracuseStep 1906145 = 1429609) B1429609
theorem B3610169 : Blo 562809 3610169 := bstep (se 2 (by rfl) ⟨1353813, by rfl⟩ : syracuseStep 3610169 = 2707627) B2707627
theorem B955975 : Blo 562809 955975 := bstep (se 1 (by rfl) ⟨716981, by rfl⟩ : syracuseStep 955975 = 1433963) B1433963
theorem B562855 : Blo 562809 562855 := bstep (se 1 (by rfl) ⟨422141, by rfl⟩ : syracuseStep 562855 = 844283) B844283
theorem B562939 : Blo 562809 562939 := bstep (se 1 (by rfl) ⟨422204, by rfl⟩ : syracuseStep 562939 = 844409) B844409
theorem B26449669 : Blo 562809 26449669 := bstep (se 4 (by rfl) ⟨2479656, by rfl⟩ : syracuseStep 26449669 = 4959313) B4959313
theorem B562975 : Blo 562809 562975 := bstep (se 1 (by rfl) ⟨422231, by rfl⟩ : syracuseStep 562975 = 844463) B844463
theorem B956191 : Blo 562809 956191 := bstep (se 1 (by rfl) ⟨717143, by rfl⟩ : syracuseStep 956191 = 1434287) B1434287
theorem B563007 : Blo 562809 563007 := bstep (se 1 (by rfl) ⟨422255, by rfl⟩ : syracuseStep 563007 = 844511) B844511
theorem B1611751 : Blo 562809 1611751 := bstep (se 1 (by rfl) ⟨1208813, by rfl⟩ : syracuseStep 1611751 = 2417627) B2417627
theorem B563183 : Blo 562809 563183 := bstep (se 1 (by rfl) ⟨422387, by rfl⟩ : syracuseStep 563183 = 844775) B844775
theorem B956407 : Blo 562809 956407 := bstep (se 1 (by rfl) ⟨717305, by rfl⟩ : syracuseStep 956407 = 1434611) B1434611
theorem B7739459 : Blo 562809 7739459 := bstep (se 1 (by rfl) ⟨5804594, by rfl⟩ : syracuseStep 7739459 = 11609189) B11609189
theorem B1906793 : Blo 562809 1906793 := bstep (se 2 (by rfl) ⟨715047, by rfl⟩ : syracuseStep 1906793 = 1430095) B1430095
theorem B563355 : Blo 562809 563355 := bstep (se 1 (by rfl) ⟨422516, by rfl⟩ : syracuseStep 563355 = 845033) B845033
theorem B563391 : Blo 562809 563391 := bstep (se 1 (by rfl) ⟨422543, by rfl⟩ : syracuseStep 563391 = 845087) B845087
theorem B858347 : Blo 562809 858347 := bstep (se 1 (by rfl) ⟨643760, by rfl⟩ : syracuseStep 858347 = 1287521) B1287521
theorem B563503 : Blo 562809 563503 := bstep (se 1 (by rfl) ⟨422627, by rfl⟩ : syracuseStep 563503 = 845255) B845255
theorem B563739 : Blo 562809 563739 := bstep (se 1 (by rfl) ⟨422804, by rfl⟩ : syracuseStep 563739 = 845609) B845609
theorem B563743 : Blo 562809 563743 := bstep (se 1 (by rfl) ⟨422807, by rfl⟩ : syracuseStep 563743 = 845615) B845615
theorem B5413715 : Blo 562809 5413715 := bstep (se 1 (by rfl) ⟨4060286, by rfl⟩ : syracuseStep 5413715 = 8120573) B8120573
theorem B564059 : Blo 562809 564059 := bstep (se 1 (by rfl) ⟨423044, by rfl⟩ : syracuseStep 564059 = 846089) B846089
theorem B6101885 : Blo 562809 6101885 := bstep (se 3 (by rfl) ⟨1144103, by rfl⟩ : syracuseStep 6101885 = 2288207) B2288207
theorem B564127 : Blo 562809 564127 := bstep (se 1 (by rfl) ⟨423095, by rfl⟩ : syracuseStep 564127 = 846191) B846191
theorem B1907657 : Blo 562809 1907657 := bstep (se 2 (by rfl) ⟨715371, by rfl⟩ : syracuseStep 1907657 = 1430743) B1430743
theorem B564271 : Blo 562809 564271 := bstep (se 1 (by rfl) ⟨423203, by rfl⟩ : syracuseStep 564271 = 846407) B846407
theorem B564295 : Blo 562809 564295 := bstep (se 1 (by rfl) ⟨423221, by rfl⟩ : syracuseStep 564295 = 846443) B846443
theorem B3087575 : Blo 562809 3087575 := bstep (se 1 (by rfl) ⟨2315681, by rfl⟩ : syracuseStep 3087575 = 4631363) B4631363
theorem B1907927 : Blo 562809 1907927 := bstep (se 1 (by rfl) ⟨1430945, by rfl⟩ : syracuseStep 1907927 = 2861891) B2861891
theorem B564447 : Blo 562809 564447 := bstep (se 1 (by rfl) ⟨423335, by rfl⟩ : syracuseStep 564447 = 846671) B846671
theorem B3874049 : Blo 562809 3874049 := bstep (se 2 (by rfl) ⟨1452768, by rfl⟩ : syracuseStep 3874049 = 2905537) B2905537
theorem B4300127 : Blo 562809 4300127 := bstep (se 1 (by rfl) ⟨3225095, by rfl⟩ : syracuseStep 4300127 = 6450191) B6450191
theorem B1613267 : Blo 562809 1613267 := bstep (se 1 (by rfl) ⟨1209950, by rfl⟩ : syracuseStep 1613267 = 2419901) B2419901
theorem B564711 : Blo 562809 564711 := bstep (se 1 (by rfl) ⟨423533, by rfl⟩ : syracuseStep 564711 = 847067) B847067
theorem B564827 : Blo 562809 564827 := bstep (se 1 (by rfl) ⟨423620, by rfl⟩ : syracuseStep 564827 = 847241) B847241
theorem B1908467 : Blo 562809 1908467 := bstep (se 1 (by rfl) ⟨1431350, by rfl⟩ : syracuseStep 1908467 = 2862701) B2862701
theorem B565063 : Blo 562809 565063 := bstep (se 1 (by rfl) ⟨423797, by rfl⟩ : syracuseStep 565063 = 847595) B847595
theorem B13705109 : Blo 562809 13705109 := bstep (se 6 (by rfl) ⟨321213, by rfl⟩ : syracuseStep 13705109 = 642427) B642427
theorem B565215 : Blo 562809 565215 := bstep (se 1 (by rfl) ⟨423911, by rfl⟩ : syracuseStep 565215 = 847823) B847823
theorem B6103097 : Blo 562809 6103097 := bstep (se 2 (by rfl) ⟨2288661, by rfl⟩ : syracuseStep 6103097 = 4577323) B4577323
theorem B565479 : Blo 562809 565479 := bstep (se 1 (by rfl) ⟨424109, by rfl⟩ : syracuseStep 565479 = 848219) B848219
theorem B565631 : Blo 562809 565631 := bstep (se 1 (by rfl) ⟨424223, by rfl⟩ : syracuseStep 565631 = 848447) B848447
theorem B565711 : Blo 562809 565711 := bstep (se 1 (by rfl) ⟨424283, by rfl⟩ : syracuseStep 565711 = 848567) B848567
theorem B1810939 : Blo 562809 1810939 := bstep (se 1 (by rfl) ⟨1358204, by rfl⟩ : syracuseStep 1810939 = 2716409) B2716409
theorem B565863 : Blo 562809 565863 := bstep (se 1 (by rfl) ⟨424397, by rfl⟩ : syracuseStep 565863 = 848795) B848795
theorem B1286891 : Blo 562809 1286891 := bstep (se 1 (by rfl) ⟨965168, by rfl⟩ : syracuseStep 1286891 = 1930337) B1930337
theorem B566127 : Blo 562809 566127 := bstep (se 1 (by rfl) ⟨424595, by rfl⟩ : syracuseStep 566127 = 849191) B849191
theorem B566183 : Blo 562809 566183 := bstep (se 1 (by rfl) ⟨424637, by rfl⟩ : syracuseStep 566183 = 849275) B849275
theorem B566267 : Blo 562809 566267 := bstep (se 1 (by rfl) ⟨424700, by rfl⟩ : syracuseStep 566267 = 849401) B849401
theorem B566335 : Blo 562809 566335 := bstep (se 1 (by rfl) ⟨424751, by rfl⟩ : syracuseStep 566335 = 849503) B849503
theorem B566479 : Blo 562809 566479 := bstep (se 1 (by rfl) ⟨424859, by rfl⟩ : syracuseStep 566479 = 849719) B849719
theorem B566683 : Blo 562809 566683 := bstep (se 1 (by rfl) ⟨425012, by rfl⟩ : syracuseStep 566683 = 850025) B850025
theorem B1353131 : Blo 562809 1353131 := bstep (se 1 (by rfl) ⟨1014848, by rfl⟩ : syracuseStep 1353131 = 2029697) B2029697
theorem B2860595 : Blo 562809 2860595 := bstep (se 1 (by rfl) ⟨2145446, by rfl⟩ : syracuseStep 2860595 = 4290893) B4290893
theorem B3614291 : Blo 562809 3614291 := bstep (se 1 (by rfl) ⟨2710718, by rfl⟩ : syracuseStep 3614291 = 5421437) B5421437
theorem B5154563 : Blo 562809 5154563 := bstep (se 1 (by rfl) ⟨3865922, by rfl⟩ : syracuseStep 5154563 = 7731845) B7731845
theorem B6432695 : Blo 562809 6432695 := bstep (se 1 (by rfl) ⟨4824521, by rfl⟩ : syracuseStep 6432695 = 9649043) B9649043
theorem B2173241 : Blo 562809 2173241 := bstep (se 2 (by rfl) ⟨814965, by rfl⟩ : syracuseStep 2173241 = 1629931) B1629931
theorem B5155255 : Blo 562809 5155255 := bstep (se 1 (by rfl) ⟨3866441, by rfl⟩ : syracuseStep 5155255 = 7732883) B7732883
theorem B5220865 : Blo 562809 5220865 := bstep (se 2 (by rfl) ⟨1957824, by rfl⟩ : syracuseStep 5220865 = 3915649) B3915649
theorem B1289015 : Blo 562809 1289015 := bstep (se 1 (by rfl) ⟨966761, by rfl⟩ : syracuseStep 1289015 = 1933523) B1933523
theorem B2862215 : Blo 562809 2862215 := bstep (se 1 (by rfl) ⟨2146661, by rfl⟩ : syracuseStep 2862215 = 4293323) B4293323
theorem B1912031 : Blo 562809 1912031 := bstep (se 1 (by rfl) ⟨1434023, by rfl⟩ : syracuseStep 1912031 = 2868047) B2868047
theorem B1912247 : Blo 562809 1912247 := bstep (se 1 (by rfl) ⟨1434185, by rfl⟩ : syracuseStep 1912247 = 2868371) B2868371
theorem B634459 : Blo 562809 634459 := bstep (se 1 (by rfl) ⟨475844, by rfl⟩ : syracuseStep 634459 = 951689) B951689
theorem B9252467 : Blo 562809 9252467 := bstep (se 1 (by rfl) ⟨6939350, by rfl⟩ : syracuseStep 9252467 = 13878701) B13878701
theorem B634747 : Blo 562809 634747 := bstep (se 1 (by rfl) ⟨476060, by rfl⟩ : syracuseStep 634747 = 952121) B952121
theorem B3518473 : Blo 562809 3518473 := bstep (se 2 (by rfl) ⟨1319427, by rfl⟩ : syracuseStep 3518473 = 2638855) B2638855
theorem B4567049 : Blo 562809 4567049 := bstep (se 2 (by rfl) ⟨1712643, by rfl⟩ : syracuseStep 4567049 = 3425287) B3425287
theorem B17018909 : Blo 562809 17018909 := bstep (se 3 (by rfl) ⟨3191045, by rfl⟩ : syracuseStep 17018909 = 6382091) B6382091
theorem B3616933 : Blo 562809 3616933 := bstep (se 4 (by rfl) ⟨339087, by rfl⟩ : syracuseStep 3616933 = 678175) B678175
theorem B13054445 : Blo 562809 13054445 := bstep (se 3 (by rfl) ⟨2447708, by rfl⟩ : syracuseStep 13054445 = 4895417) B4895417
theorem B2142713 : Blo 562809 2142713 := bstep (se 2 (by rfl) ⟨803517, by rfl⟩ : syracuseStep 2142713 = 1607035) B1607035
theorem B7254521 : Blo 562809 7254521 := bstep (se 2 (by rfl) ⟨2720445, by rfl⟩ : syracuseStep 7254521 = 5440891) B5440891
theorem B4076203 : Blo 562809 4076203 := bstep (se 1 (by rfl) ⟨3057152, by rfl⟩ : syracuseStep 4076203 = 6114305) B6114305
theorem B5157665 : Blo 562809 5157665 := bstep (se 2 (by rfl) ⟨1934124, by rfl⟩ : syracuseStep 5157665 = 3868249) B3868249
theorem B2863997 : Blo 562809 2863997 := bstep (se 3 (by rfl) ⟨536999, by rfl⟩ : syracuseStep 2863997 = 1073999) B1073999
theorem B11023229 : Blo 562809 11023229 := bstep (se 3 (by rfl) ⟨2066855, by rfl⟩ : syracuseStep 11023229 = 4133711) B4133711
theorem B635899 : Blo 562809 635899 := bstep (se 1 (by rfl) ⟨476924, by rfl⟩ : syracuseStep 635899 = 953849) B953849
theorem B30815275 : Blo 562809 30815275 := bstep (se 1 (by rfl) ⟨23111456, by rfl⟩ : syracuseStep 30815275 = 46222913) B46222913
theorem B636079 : Blo 562809 636079 := bstep (se 1 (by rfl) ⟨477059, by rfl⟩ : syracuseStep 636079 = 954119) B954119
theorem B119387525 : Blo 562809 119387525 := bstep (se 4 (by rfl) ⟨11192580, by rfl⟩ : syracuseStep 119387525 = 22385161) B22385161
theorem B964217 : Blo 562809 964217 := bstep (se 2 (by rfl) ⟨361581, by rfl⟩ : syracuseStep 964217 = 723163) B723163
theorem B636583 : Blo 562809 636583 := bstep (se 1 (by rfl) ⟨477437, by rfl⟩ : syracuseStep 636583 = 954875) B954875
theorem B636871 : Blo 562809 636871 := bstep (se 1 (by rfl) ⟨477653, by rfl⟩ : syracuseStep 636871 = 955307) B955307
theorem B2144339 : Blo 562809 2144339 := bstep (se 1 (by rfl) ⟨1608254, by rfl⟩ : syracuseStep 2144339 = 3216509) B3216509
theorem B2144353 : Blo 562809 2144353 := bstep (se 2 (by rfl) ⟨804132, by rfl⟩ : syracuseStep 2144353 = 1608265) B1608265
theorem B637231 : Blo 562809 637231 := bstep (se 1 (by rfl) ⟨477923, by rfl⟩ : syracuseStep 637231 = 955847) B955847
theorem B2144825 : Blo 562809 2144825 := bstep (se 2 (by rfl) ⟨804309, by rfl⟩ : syracuseStep 2144825 = 1608619) B1608619
theorem B16267999 : Blo 562809 16267999 := bstep (se 1 (by rfl) ⟨12200999, by rfl⟩ : syracuseStep 16267999 = 24401999) B24401999
theorem B801695 : Blo 562809 801695 := bstep (se 1 (by rfl) ⟨601271, by rfl⟩ : syracuseStep 801695 = 1202543) B1202543
theorem B2866265 : Blo 562809 2866265 := bstep (se 2 (by rfl) ⟨1074849, by rfl⟩ : syracuseStep 2866265 = 2149699) B2149699
theorem B2866913 : Blo 562809 2866913 := bstep (se 2 (by rfl) ⟨1075092, by rfl⟩ : syracuseStep 2866913 = 2150185) B2150185
theorem B1425863 : Blo 562809 1425863 := bstep (se 1 (by rfl) ⟨1069397, by rfl⟩ : syracuseStep 1425863 = 2138795) B2138795
theorem B901625 : Blo 562809 901625 := bstep (se 2 (by rfl) ⟨338109, by rfl⟩ : syracuseStep 901625 = 676219) B676219
theorem B4276799 : Blo 562809 4276799 := bstep (se 1 (by rfl) ⟨3207599, by rfl⟩ : syracuseStep 4276799 = 6415199) B6415199
theorem B4834363 : Blo 562809 4834363 := bstep (se 1 (by rfl) ⟨3625772, by rfl⟩ : syracuseStep 4834363 = 7251545) B7251545
theorem B803945 : Blo 562809 803945 := bstep (se 2 (by rfl) ⟨301479, by rfl⟩ : syracuseStep 803945 = 602959) B602959
theorem B2147755 : Blo 562809 2147755 := bstep (se 1 (by rfl) ⟨1610816, by rfl⟩ : syracuseStep 2147755 = 3221633) B3221633
theorem B2868695 : Blo 562809 2868695 := bstep (se 1 (by rfl) ⟨2151521, by rfl⟩ : syracuseStep 2868695 = 4303043) B4303043
theorem B1427807 : Blo 562809 1427807 := bstep (se 1 (by rfl) ⟨1070855, by rfl⟩ : syracuseStep 1427807 = 2141711) B2141711
theorem B805403 : Blo 562809 805403 := bstep (se 1 (by rfl) ⟨604052, by rfl⟩ : syracuseStep 805403 = 1208105) B1208105
theorem B2313641 : Blo 562809 2313641 := bstep (se 2 (by rfl) ⟨867615, by rfl⟩ : syracuseStep 2313641 = 1735231) B1735231
theorem B7818767 : Blo 562809 7818767 := bstep (se 1 (by rfl) ⟨5864075, by rfl⟩ : syracuseStep 7818767 = 11728151) B11728151
theorem B20598533 : Blo 562809 20598533 := bstep (se 4 (by rfl) ⟨1931112, by rfl⟩ : syracuseStep 20598533 = 3862225) B3862225
theorem B3624851 : Blo 562809 3624851 := bstep (se 1 (by rfl) ⟨2718638, by rfl⟩ : syracuseStep 3624851 = 5437277) B5437277
theorem B2576569 : Blo 562809 2576569 := bstep (se 2 (by rfl) ⟨966213, by rfl⟩ : syracuseStep 2576569 = 1932427) B1932427
theorem B2707643 : Blo 562809 2707643 := bstep (se 1 (by rfl) ⟨2030732, by rfl⟩ : syracuseStep 2707643 = 4061465) B4061465
theorem B2413151 : Blo 562809 2413151 := bstep (se 1 (by rfl) ⟨1809863, by rfl⟩ : syracuseStep 2413151 = 3619727) B3619727
theorem B3429371 : Blo 562809 3429371 := bstep (se 1 (by rfl) ⟨2572028, by rfl⟩ : syracuseStep 3429371 = 5144057) B5144057
theorem B2151643 : Blo 562809 2151643 := bstep (se 1 (by rfl) ⟨1613732, by rfl⟩ : syracuseStep 2151643 = 3227465) B3227465
theorem B1070491 : Blo 562809 1070491 := bstep (se 1 (by rfl) ⟨802868, by rfl⟩ : syracuseStep 1070491 = 1605737) B1605737
theorem B1267271 : Blo 562809 1267271 := bstep (se 1 (by rfl) ⟨950453, by rfl⟩ : syracuseStep 1267271 = 1900907) B1900907
theorem B1267451 : Blo 562809 1267451 := bstep (se 1 (by rfl) ⟨950588, by rfl⟩ : syracuseStep 1267451 = 1901177) B1901177
theorem B1431695 : Blo 562809 1431695 := bstep (se 1 (by rfl) ⟨1073771, by rfl⟩ : syracuseStep 1431695 = 2147543) B2147543
theorem B4839695 : Blo 562809 4839695 := bstep (se 1 (by rfl) ⟨3629771, by rfl⟩ : syracuseStep 4839695 = 7259543) B7259543
theorem B1268009 : Blo 562809 1268009 := bstep (se 2 (by rfl) ⟨475503, by rfl⟩ : syracuseStep 1268009 = 951007) B951007
theorem B23517539 : Blo 562809 23517539 := bstep (se 1 (by rfl) ⟨17638154, by rfl⟩ : syracuseStep 23517539 = 35276309) B35276309
theorem B11164081 : Blo 562809 11164081 := bstep (se 2 (by rfl) ⟨4186530, by rfl⟩ : syracuseStep 11164081 = 8373061) B8373061
theorem B1432201 : Blo 562809 1432201 := bstep (se 2 (by rfl) ⟨537075, by rfl⟩ : syracuseStep 1432201 = 1074151) B1074151
theorem B4840073 : Blo 562809 4840073 := bstep (se 2 (by rfl) ⟨1815027, by rfl⟩ : syracuseStep 4840073 = 3630055) B3630055
theorem B1268585 : Blo 562809 1268585 := bstep (se 2 (by rfl) ⟨475719, by rfl⟩ : syracuseStep 1268585 = 951439) B951439
theorem B1268639 : Blo 562809 1268639 := bstep (se 1 (by rfl) ⟨951479, by rfl⟩ : syracuseStep 1268639 = 1902959) B1902959
theorem B1072595 : Blo 562809 1072595 := bstep (se 1 (by rfl) ⟨804446, by rfl⟩ : syracuseStep 1072595 = 1608893) B1608893
theorem B1433335 : Blo 562809 1433335 := bstep (se 1 (by rfl) ⟨1075001, by rfl⟩ : syracuseStep 1433335 = 2150003) B2150003
theorem B6119185 : Blo 562809 6119185 := bstep (se 2 (by rfl) ⟨2294694, by rfl⟩ : syracuseStep 6119185 = 4589389) B4589389
theorem B1269575 : Blo 562809 1269575 := bstep (se 1 (by rfl) ⟨952181, by rfl⟩ : syracuseStep 1269575 = 1904363) B1904363
theorem B1433639 : Blo 562809 1433639 := bstep (se 1 (by rfl) ⟨1075229, by rfl⟩ : syracuseStep 1433639 = 2150459) B2150459
theorem B6447275 : Blo 562809 6447275 := bstep (se 1 (by rfl) ⟨4835456, by rfl⟩ : syracuseStep 6447275 = 9670913) B9670913
theorem B3760415 : Blo 562809 3760415 := bstep (se 1 (by rfl) ⟨2820311, by rfl⟩ : syracuseStep 3760415 = 5640623) B5640623
theorem B1270223 : Blo 562809 1270223 := bstep (se 1 (by rfl) ⟨952667, by rfl⟩ : syracuseStep 1270223 = 1905335) B1905335
theorem B844265 : Blo 562809 844265 := bstep (se 2 (by rfl) ⟨316599, by rfl⟩ : syracuseStep 844265 = 633199) B633199
theorem B844391 : Blo 562809 844391 := bstep (se 1 (by rfl) ⟨633293, by rfl⟩ : syracuseStep 844391 = 1266587) B1266587
theorem B4285061 : Blo 562809 4285061 := bstep (se 4 (by rfl) ⟨401724, by rfl⟩ : syracuseStep 4285061 = 803449) B803449
theorem B844523 : Blo 562809 844523 := bstep (se 1 (by rfl) ⟨633392, by rfl⟩ : syracuseStep 844523 = 1266785) B1266785
theorem B844553 : Blo 562809 844553 := bstep (se 2 (by rfl) ⟨316707, by rfl⟩ : syracuseStep 844553 = 633415) B633415
theorem B844655 : Blo 562809 844655 := bstep (se 1 (by rfl) ⟨633491, by rfl⟩ : syracuseStep 844655 = 1266983) B1266983
theorem B1270889 : Blo 562809 1270889 := bstep (se 2 (by rfl) ⟨476583, by rfl⟩ : syracuseStep 1270889 = 953167) B953167
theorem B844907 : Blo 562809 844907 := bstep (se 1 (by rfl) ⟨633680, by rfl⟩ : syracuseStep 844907 = 1267361) B1267361
theorem B845147 : Blo 562809 845147 := bstep (se 1 (by rfl) ⟨633860, by rfl⟩ : syracuseStep 845147 = 1267721) B1267721
theorem B2057687 : Blo 562809 2057687 := bstep (se 1 (by rfl) ⟨1543265, by rfl⟩ : syracuseStep 2057687 = 3086531) B3086531
theorem B845423 : Blo 562809 845423 := bstep (se 1 (by rfl) ⟨634067, by rfl⟩ : syracuseStep 845423 = 1268135) B1268135
theorem B845495 : Blo 562809 845495 := bstep (se 1 (by rfl) ⟨634121, by rfl⟩ : syracuseStep 845495 = 1268243) B1268243
theorem B9791165 : Blo 562809 9791165 := bstep (se 3 (by rfl) ⟨1835843, by rfl⟩ : syracuseStep 9791165 = 3671687) B3671687
theorem B845531 : Blo 562809 845531 := bstep (se 1 (by rfl) ⟨634148, by rfl⟩ : syracuseStep 845531 = 1268297) B1268297
theorem B2746075 : Blo 562809 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B1271519 : Blo 562809 1271519 := bstep (se 1 (by rfl) ⟨953639, by rfl⟩ : syracuseStep 1271519 = 1907279) B1907279
theorem B845705 : Blo 562809 845705 := bstep (se 2 (by rfl) ⟨317139, by rfl⟩ : syracuseStep 845705 = 634279) B634279
theorem B2287561 : Blo 562809 2287561 := bstep (se 2 (by rfl) ⟨857835, by rfl⟩ : syracuseStep 2287561 = 1715671) B1715671
theorem B845807 : Blo 562809 845807 := bstep (se 1 (by rfl) ⟨634355, by rfl⟩ : syracuseStep 845807 = 1268711) B1268711
theorem B846059 : Blo 562809 846059 := bstep (se 1 (by rfl) ⟨634544, by rfl⟩ : syracuseStep 846059 = 1269089) B1269089
theorem B846119 : Blo 562809 846119 := bstep (se 1 (by rfl) ⟨634589, by rfl⟩ : syracuseStep 846119 = 1269179) B1269179
theorem B846203 : Blo 562809 846203 := bstep (se 1 (by rfl) ⟨634652, by rfl⟩ : syracuseStep 846203 = 1269305) B1269305
theorem B1272347 : Blo 562809 1272347 := bstep (se 1 (by rfl) ⟨954260, by rfl⟩ : syracuseStep 1272347 = 1908521) B1908521
theorem B846473 : Blo 562809 846473 := bstep (se 2 (by rfl) ⟨317427, by rfl⟩ : syracuseStep 846473 = 634855) B634855
theorem B846647 : Blo 562809 846647 := bstep (se 1 (by rfl) ⟨634985, by rfl⟩ : syracuseStep 846647 = 1269971) B1269971
theorem B846683 : Blo 562809 846683 := bstep (se 1 (by rfl) ⟨635012, by rfl⟩ : syracuseStep 846683 = 1270025) B1270025
theorem B2714563 : Blo 562809 2714563 := bstep (se 1 (by rfl) ⟨2035922, by rfl⟩ : syracuseStep 2714563 = 4071845) B4071845
theorem B846827 : Blo 562809 846827 := bstep (se 1 (by rfl) ⟨635120, by rfl⟩ : syracuseStep 846827 = 1270241) B1270241
theorem B4287491 : Blo 562809 4287491 := bstep (se 1 (by rfl) ⟨3215618, by rfl⟩ : syracuseStep 4287491 = 6431237) B6431237
theorem B847031 : Blo 562809 847031 := bstep (se 1 (by rfl) ⟨635273, by rfl⟩ : syracuseStep 847031 = 1270547) B1270547
theorem B847271 : Blo 562809 847271 := bstep (se 1 (by rfl) ⟨635453, by rfl⟩ : syracuseStep 847271 = 1270907) B1270907
theorem B847355 : Blo 562809 847355 := bstep (se 1 (by rfl) ⟨635516, by rfl⟩ : syracuseStep 847355 = 1271033) B1271033
theorem B847451 : Blo 562809 847451 := bstep (se 1 (by rfl) ⟨635588, by rfl⟩ : syracuseStep 847451 = 1271177) B1271177
theorem B3665533 : Blo 562809 3665533 := bstep (se 3 (by rfl) ⟨687287, by rfl⟩ : syracuseStep 3665533 = 1374575) B1374575
theorem B847535 : Blo 562809 847535 := bstep (se 1 (by rfl) ⟨635651, by rfl⟩ : syracuseStep 847535 = 1271303) B1271303
theorem B847655 : Blo 562809 847655 := bstep (se 1 (by rfl) ⟨635741, by rfl⟩ : syracuseStep 847655 = 1271483) B1271483
theorem B847739 : Blo 562809 847739 := bstep (se 1 (by rfl) ⟨635804, by rfl⟩ : syracuseStep 847739 = 1271609) B1271609
theorem B1273823 : Blo 562809 1273823 := bstep (se 1 (by rfl) ⟨955367, by rfl⟩ : syracuseStep 1273823 = 1910735) B1910735
theorem B9433253 : Blo 562809 9433253 := bstep (se 4 (by rfl) ⟨884367, by rfl⟩ : syracuseStep 9433253 = 1768735) B1768735
theorem B5435585 : Blo 562809 5435585 := bstep (se 2 (by rfl) ⟨2038344, by rfl⟩ : syracuseStep 5435585 = 4076689) B4076689
theorem B848159 : Blo 562809 848159 := bstep (se 1 (by rfl) ⟨636119, by rfl⟩ : syracuseStep 848159 = 1272239) B1272239
theorem B848183 : Blo 562809 848183 := bstep (se 1 (by rfl) ⟨636137, by rfl⟩ : syracuseStep 848183 = 1272275) B1272275
theorem B848255 : Blo 562809 848255 := bstep (se 1 (by rfl) ⟨636191, by rfl⟩ : syracuseStep 848255 = 1272383) B1272383
theorem B848327 : Blo 562809 848327 := bstep (se 1 (by rfl) ⟨636245, by rfl⟩ : syracuseStep 848327 = 1272491) B1272491
theorem B3207761 : Blo 562809 3207761 := bstep (se 2 (by rfl) ⟨1202910, by rfl⟩ : syracuseStep 3207761 = 2405821) B2405821
theorem B1143391 : Blo 562809 1143391 := bstep (se 1 (by rfl) ⟨857543, by rfl⟩ : syracuseStep 1143391 = 1715087) B1715087
theorem B16708193 : Blo 562809 16708193 := bstep (se 2 (by rfl) ⟨6265572, by rfl⟩ : syracuseStep 16708193 = 12531145) B12531145
theorem B1274471 : Blo 562809 1274471 := bstep (se 1 (by rfl) ⟨955853, by rfl⟩ : syracuseStep 1274471 = 1911707) B1911707
theorem B14447321 : Blo 562809 14447321 := bstep (se 2 (by rfl) ⟨5417745, by rfl⟩ : syracuseStep 14447321 = 10835491) B10835491
theorem B848681 : Blo 562809 848681 := bstep (se 2 (by rfl) ⟨318255, by rfl⟩ : syracuseStep 848681 = 636511) B636511
theorem B848687 : Blo 562809 848687 := bstep (se 1 (by rfl) ⟨636515, by rfl⟩ : syracuseStep 848687 = 1273031) B1273031
theorem B848807 : Blo 562809 848807 := bstep (se 1 (by rfl) ⟨636605, by rfl⟩ : syracuseStep 848807 = 1273211) B1273211
theorem B848891 : Blo 562809 848891 := bstep (se 1 (by rfl) ⟨636668, by rfl⟩ : syracuseStep 848891 = 1273337) B1273337
theorem B848951 : Blo 562809 848951 := bstep (se 1 (by rfl) ⟨636713, by rfl⟩ : syracuseStep 848951 = 1273427) B1273427
theorem B849071 : Blo 562809 849071 := bstep (se 1 (by rfl) ⟨636803, by rfl⟩ : syracuseStep 849071 = 1273607) B1273607
theorem B1275155 : Blo 562809 1275155 := bstep (se 1 (by rfl) ⟨956366, by rfl⟩ : syracuseStep 1275155 = 1912733) B1912733
theorem B1275227 : Blo 562809 1275227 := bstep (se 1 (by rfl) ⟨956420, by rfl⟩ : syracuseStep 1275227 = 1912841) B1912841
theorem B4289921 : Blo 562809 4289921 := bstep (se 2 (by rfl) ⟨1608720, by rfl⟩ : syracuseStep 4289921 = 3217441) B3217441
theorem B1603003 : Blo 562809 1603003 := bstep (se 1 (by rfl) ⟨1202252, by rfl⟩ : syracuseStep 1603003 = 2404505) B2404505
theorem B8123975 : Blo 562809 8123975 := bstep (se 1 (by rfl) ⟨6092981, by rfl⟩ : syracuseStep 8123975 = 12185963) B12185963
theorem B849479 : Blo 562809 849479 := bstep (se 1 (by rfl) ⟨637109, by rfl⟩ : syracuseStep 849479 = 1274219) B1274219
theorem B849575 : Blo 562809 849575 := bstep (se 1 (by rfl) ⟨637181, by rfl⟩ : syracuseStep 849575 = 1274363) B1274363
theorem B849659 : Blo 562809 849659 := bstep (se 1 (by rfl) ⟨637244, by rfl⟩ : syracuseStep 849659 = 1274489) B1274489
theorem B849695 : Blo 562809 849695 := bstep (se 1 (by rfl) ⟨637271, by rfl⟩ : syracuseStep 849695 = 1274543) B1274543
theorem B849743 : Blo 562809 849743 := bstep (se 1 (by rfl) ⟨637307, by rfl⟩ : syracuseStep 849743 = 1274615) B1274615
theorem B4061123 : Blo 562809 4061123 := bstep (se 1 (by rfl) ⟨3045842, by rfl⟩ : syracuseStep 4061123 = 6091685) B6091685
theorem B849863 : Blo 562809 849863 := bstep (se 1 (by rfl) ⟨637397, by rfl⟩ : syracuseStep 849863 = 1274795) B1274795
theorem B2718407 : Blo 562809 2718407 := bstep (se 1 (by rfl) ⟨2038805, by rfl⟩ : syracuseStep 2718407 = 4077611) B4077611
theorem B2030417 : Blo 562809 2030417 := bstep (se 2 (by rfl) ⟨761406, by rfl⟩ : syracuseStep 2030417 = 1522813) B1522813
theorem B1899773 : Blo 562809 1899773 := bstep (se 3 (by rfl) ⟨356207, by rfl⟩ : syracuseStep 1899773 = 712415) B712415
theorem B6094273 : Blo 562809 6094273 := bstep (se 2 (by rfl) ⟨2285352, by rfl⟩ : syracuseStep 6094273 = 4570705) B4570705
theorem B2850551 : Blo 562809 2850551 := bstep (se 1 (by rfl) ⟨2137913, by rfl⟩ : syracuseStep 2850551 = 4275827) B4275827
theorem B950575 : Blo 562809 950575 := bstep (se 1 (by rfl) ⟨712931, by rfl⟩ : syracuseStep 950575 = 1425863) B1425863
theorem B2851199 : Blo 562809 2851199 := bstep (se 1 (by rfl) ⟨2138399, by rfl⟩ : syracuseStep 2851199 = 4276799) B4276799
theorem B2097535 : Blo 562809 2097535 := bstep (se 1 (by rfl) ⟨1573151, by rfl⟩ : syracuseStep 2097535 = 3146303) B3146303
theorem B1901015 : Blo 562809 1901015 := bstep (se 1 (by rfl) ⟨1425761, by rfl⟩ : syracuseStep 1901015 = 2851523) B2851523
theorem B2753551 : Blo 562809 2753551 := bstep (se 1 (by rfl) ⟨2065163, by rfl⟩ : syracuseStep 2753551 = 4130327) B4130327
theorem B951871 : Blo 562809 951871 := bstep (se 1 (by rfl) ⟨713903, by rfl⟩ : syracuseStep 951871 = 1427807) B1427807
theorem B3213067 : Blo 562809 3213067 := bstep (se 1 (by rfl) ⟨2409800, by rfl⟩ : syracuseStep 3213067 = 4819601) B4819601
theorem B5212511 : Blo 562809 5212511 := bstep (se 1 (by rfl) ⟨3909383, by rfl⟩ : syracuseStep 5212511 = 7818767) B7818767
theorem B13732355 : Blo 562809 13732355 := bstep (se 1 (by rfl) ⟨10299266, by rfl⟩ : syracuseStep 13732355 = 20598533) B20598533
theorem B3050081 : Blo 562809 3050081 := bstep (se 2 (by rfl) ⟨1143780, by rfl⟩ : syracuseStep 3050081 = 2287561) B2287561
theorem B1805095 : Blo 562809 1805095 := bstep (se 1 (by rfl) ⟨1353821, by rfl⟩ : syracuseStep 1805095 = 2707643) B2707643
theorem B4590431 : Blo 562809 4590431 := bstep (se 1 (by rfl) ⟨3442823, by rfl⟩ : syracuseStep 4590431 = 6885647) B6885647
theorem B1903607 : Blo 562809 1903607 := bstep (se 1 (by rfl) ⟨1427705, by rfl⟩ : syracuseStep 1903607 = 2855411) B2855411
theorem B1608767 : Blo 562809 1608767 := bstep (se 1 (by rfl) ⟨1206575, by rfl⟩ : syracuseStep 1608767 = 2413151) B2413151
theorem B5442623 : Blo 562809 5442623 := bstep (se 1 (by rfl) ⟨4081967, by rfl⟩ : syracuseStep 5442623 = 8163935) B8163935
theorem B1273466933 : Blo 562809 1273466933 := bstep (se 5 (by rfl) ⟨59693762, by rfl⟩ : syracuseStep 1273466933 = 119387525) B119387525
theorem B954463 : Blo 562809 954463 := bstep (se 1 (by rfl) ⟨715847, by rfl⟩ : syracuseStep 954463 = 1431695) B1431695
theorem B3609143 : Blo 562809 3609143 := bstep (se 1 (by rfl) ⟨2706857, by rfl⟩ : syracuseStep 3609143 = 5413715) B5413715
theorem B4067923 : Blo 562809 4067923 := bstep (se 1 (by rfl) ⟨3050942, by rfl⟩ : syracuseStep 4067923 = 6101885) B6101885
theorem B4887377 : Blo 562809 4887377 := bstep (se 2 (by rfl) ⟨1832766, by rfl⟩ : syracuseStep 4887377 = 3665533) B3665533
theorem B4691297 : Blo 562809 4691297 := bstep (se 2 (by rfl) ⟨1759236, by rfl⟩ : syracuseStep 4691297 = 3518473) B3518473
theorem B955759 : Blo 562809 955759 := bstep (se 1 (by rfl) ⟨716819, by rfl⟩ : syracuseStep 955759 = 1433639) B1433639
theorem B4068731 : Blo 562809 4068731 := bstep (se 1 (by rfl) ⟨3051548, by rfl⟩ : syracuseStep 4068731 = 6103097) B6103097
theorem B4298183 : Blo 562809 4298183 := bstep (se 1 (by rfl) ⟨3223637, by rfl⟩ : syracuseStep 4298183 = 6447275) B6447275
theorem B4822577 : Blo 562809 4822577 := bstep (se 2 (by rfl) ⟨1808466, by rfl⟩ : syracuseStep 4822577 = 3616933) B3616933
theorem B562843 : Blo 562809 562843 := bstep (se 1 (by rfl) ⟨422132, by rfl⟩ : syracuseStep 562843 = 844265) B844265
theorem B562927 : Blo 562809 562927 := bstep (se 1 (by rfl) ⟨422195, by rfl⟩ : syracuseStep 562927 = 844391) B844391
theorem B2856707 : Blo 562809 2856707 := bstep (se 1 (by rfl) ⟨2142530, by rfl⟩ : syracuseStep 2856707 = 4285061) B4285061
theorem B563015 : Blo 562809 563015 := bstep (se 1 (by rfl) ⟨422261, by rfl⟩ : syracuseStep 563015 = 844523) B844523
theorem B857927 : Blo 562809 857927 := bstep (se 1 (by rfl) ⟨643445, by rfl⟩ : syracuseStep 857927 = 1286891) B1286891
theorem B563035 : Blo 562809 563035 := bstep (se 1 (by rfl) ⟨422276, by rfl⟩ : syracuseStep 563035 = 844553) B844553
theorem B563103 : Blo 562809 563103 := bstep (se 1 (by rfl) ⟨422327, by rfl⟩ : syracuseStep 563103 = 844655) B844655
theorem B563271 : Blo 562809 563271 := bstep (se 1 (by rfl) ⟨422453, by rfl⟩ : syracuseStep 563271 = 844907) B844907
theorem B3676265 : Blo 562809 3676265 := bstep (se 2 (by rfl) ⟨1378599, by rfl⟩ : syracuseStep 3676265 = 2757199) B2757199
theorem B563431 : Blo 562809 563431 := bstep (se 1 (by rfl) ⟨422573, by rfl⟩ : syracuseStep 563431 = 845147) B845147
theorem B1907063 : Blo 562809 1907063 := bstep (se 1 (by rfl) ⟨1430297, by rfl⟩ : syracuseStep 1907063 = 2860595) B2860595
theorem B563615 : Blo 562809 563615 := bstep (se 1 (by rfl) ⟨422711, by rfl⟩ : syracuseStep 563615 = 845423) B845423
theorem B563663 : Blo 562809 563663 := bstep (se 1 (by rfl) ⟨422747, by rfl⟩ : syracuseStep 563663 = 845495) B845495
theorem B563687 : Blo 562809 563687 := bstep (se 1 (by rfl) ⟨422765, by rfl⟩ : syracuseStep 563687 = 845531) B845531
theorem B563803 : Blo 562809 563803 := bstep (se 1 (by rfl) ⟨422852, by rfl⟩ : syracuseStep 563803 = 845705) B845705
theorem B563871 : Blo 562809 563871 := bstep (se 1 (by rfl) ⟨422903, by rfl⟩ : syracuseStep 563871 = 845807) B845807
theorem B564039 : Blo 562809 564039 := bstep (se 1 (by rfl) ⟨423029, by rfl⟩ : syracuseStep 564039 = 846059) B846059
theorem B564079 : Blo 562809 564079 := bstep (se 1 (by rfl) ⟨423059, by rfl⟩ : syracuseStep 564079 = 846119) B846119
theorem B564135 : Blo 562809 564135 := bstep (se 1 (by rfl) ⟨423101, by rfl⟩ : syracuseStep 564135 = 846203) B846203
theorem B564315 : Blo 562809 564315 := bstep (se 1 (by rfl) ⟨423236, by rfl⟩ : syracuseStep 564315 = 846473) B846473
theorem B7249085 : Blo 562809 7249085 := bstep (se 3 (by rfl) ⟨1359203, by rfl⟩ : syracuseStep 7249085 = 2718407) B2718407
theorem B564431 : Blo 562809 564431 := bstep (se 1 (by rfl) ⟨423323, by rfl⟩ : syracuseStep 564431 = 846647) B846647
theorem B859343 : Blo 562809 859343 := bstep (se 1 (by rfl) ⟨644507, by rfl⟩ : syracuseStep 859343 = 1289015) B1289015
theorem B564455 : Blo 562809 564455 := bstep (se 1 (by rfl) ⟨423341, by rfl⟩ : syracuseStep 564455 = 846683) B846683
theorem B2137337 : Blo 562809 2137337 := bstep (se 2 (by rfl) ⟨801501, by rfl⟩ : syracuseStep 2137337 = 1603003) B1603003
theorem B564551 : Blo 562809 564551 := bstep (se 1 (by rfl) ⟨423413, by rfl⟩ : syracuseStep 564551 = 846827) B846827
theorem B2858327 : Blo 562809 2858327 := bstep (se 1 (by rfl) ⟨2143745, by rfl⟩ : syracuseStep 2858327 = 4287491) B4287491
theorem B1908143 : Blo 562809 1908143 := bstep (se 1 (by rfl) ⟨1431107, by rfl⟩ : syracuseStep 1908143 = 2862215) B2862215
theorem B564687 : Blo 562809 564687 := bstep (se 1 (by rfl) ⟨423515, by rfl⟩ : syracuseStep 564687 = 847031) B847031
theorem B564847 : Blo 562809 564847 := bstep (se 1 (by rfl) ⟨423635, by rfl⟩ : syracuseStep 564847 = 847271) B847271
theorem B564903 : Blo 562809 564903 := bstep (se 1 (by rfl) ⟨423677, by rfl⟩ : syracuseStep 564903 = 847355) B847355
theorem B35266225 : Blo 562809 35266225 := bstep (se 2 (by rfl) ⟨13224834, by rfl⟩ : syracuseStep 35266225 = 26449669) B26449669
theorem B564967 : Blo 562809 564967 := bstep (se 1 (by rfl) ⟨423725, by rfl⟩ : syracuseStep 564967 = 847451) B847451
theorem B6168311 : Blo 562809 6168311 := bstep (se 1 (by rfl) ⟨4626233, by rfl⟩ : syracuseStep 6168311 = 9252467) B9252467
theorem B2137853 : Blo 562809 2137853 := bstep (se 3 (by rfl) ⟨400847, by rfl⟩ : syracuseStep 2137853 = 801695) B801695
theorem B565023 : Blo 562809 565023 := bstep (se 1 (by rfl) ⟨423767, by rfl⟩ : syracuseStep 565023 = 847535) B847535
theorem B565103 : Blo 562809 565103 := bstep (se 1 (by rfl) ⟨423827, by rfl⟩ : syracuseStep 565103 = 847655) B847655
theorem B565159 : Blo 562809 565159 := bstep (se 1 (by rfl) ⟨423869, by rfl⟩ : syracuseStep 565159 = 847739) B847739
theorem B11345939 : Blo 562809 11345939 := bstep (se 1 (by rfl) ⟨8509454, by rfl⟩ : syracuseStep 11345939 = 17018909) B17018909
theorem B2859137 : Blo 562809 2859137 := bstep (se 2 (by rfl) ⟨1072176, by rfl⟩ : syracuseStep 2859137 = 2144353) B2144353
theorem B565439 : Blo 562809 565439 := bstep (se 1 (by rfl) ⟨424079, by rfl⟩ : syracuseStep 565439 = 848159) B848159
theorem B565455 : Blo 562809 565455 := bstep (se 1 (by rfl) ⟨424091, by rfl⟩ : syracuseStep 565455 = 848183) B848183
theorem B565503 : Blo 562809 565503 := bstep (se 1 (by rfl) ⟨424127, by rfl⟩ : syracuseStep 565503 = 848255) B848255
theorem B565551 : Blo 562809 565551 := bstep (se 1 (by rfl) ⟨424163, by rfl⟩ : syracuseStep 565551 = 848327) B848327
theorem B2138507 : Blo 562809 2138507 := bstep (se 1 (by rfl) ⟨1603880, by rfl⟩ : syracuseStep 2138507 = 3207761) B3207761
theorem B565787 : Blo 562809 565787 := bstep (se 1 (by rfl) ⟨424340, by rfl⟩ : syracuseStep 565787 = 848681) B848681
theorem B565791 : Blo 562809 565791 := bstep (se 1 (by rfl) ⟨424343, by rfl⟩ : syracuseStep 565791 = 848687) B848687
theorem B14885441 : Blo 562809 14885441 := bstep (se 2 (by rfl) ⟨5582040, by rfl⟩ : syracuseStep 14885441 = 11164081) B11164081
theorem B1909331 : Blo 562809 1909331 := bstep (se 1 (by rfl) ⟨1431998, by rfl⟩ : syracuseStep 1909331 = 2863997) B2863997
theorem B7348819 : Blo 562809 7348819 := bstep (se 1 (by rfl) ⟨5511614, by rfl⟩ : syracuseStep 7348819 = 11023229) B11023229
theorem B565871 : Blo 562809 565871 := bstep (se 1 (by rfl) ⟨424403, by rfl⟩ : syracuseStep 565871 = 848807) B848807
theorem B565927 : Blo 562809 565927 := bstep (se 1 (by rfl) ⟨424445, by rfl⟩ : syracuseStep 565927 = 848891) B848891
theorem B565967 : Blo 562809 565967 := bstep (se 1 (by rfl) ⟨424475, by rfl⟩ : syracuseStep 565967 = 848951) B848951
theorem B566047 : Blo 562809 566047 := bstep (se 1 (by rfl) ⟨424535, by rfl⟩ : syracuseStep 566047 = 849071) B849071
theorem B1909601 : Blo 562809 1909601 := bstep (se 2 (by rfl) ⟨716100, by rfl⟩ : syracuseStep 1909601 = 1432201) B1432201
theorem B2859947 : Blo 562809 2859947 := bstep (se 1 (by rfl) ⟨2144960, by rfl⟩ : syracuseStep 2859947 = 4289921) B4289921
theorem B5415983 : Blo 562809 5415983 := bstep (se 1 (by rfl) ⟨4061987, by rfl⟩ : syracuseStep 5415983 = 8123975) B8123975
theorem B566319 : Blo 562809 566319 := bstep (se 1 (by rfl) ⟨424739, by rfl⟩ : syracuseStep 566319 = 849479) B849479
theorem B6169709 : Blo 562809 6169709 := bstep (se 3 (by rfl) ⟨1156820, by rfl⟩ : syracuseStep 6169709 = 2313641) B2313641
theorem B566383 : Blo 562809 566383 := bstep (se 1 (by rfl) ⟨424787, by rfl⟩ : syracuseStep 566383 = 849575) B849575
theorem B566439 : Blo 562809 566439 := bstep (se 1 (by rfl) ⟨424829, by rfl⟩ : syracuseStep 566439 = 849659) B849659
theorem B566463 : Blo 562809 566463 := bstep (se 1 (by rfl) ⟨424847, by rfl⟩ : syracuseStep 566463 = 849695) B849695
theorem B566495 : Blo 562809 566495 := bstep (se 1 (by rfl) ⟨424871, by rfl⟩ : syracuseStep 566495 = 849743) B849743
theorem B566575 : Blo 562809 566575 := bstep (se 1 (by rfl) ⟨424931, by rfl⟩ : syracuseStep 566575 = 849863) B849863
theorem B1353611 : Blo 562809 1353611 := bstep (se 1 (by rfl) ⟨1015208, by rfl⟩ : syracuseStep 1353611 = 2030417) B2030417
theorem B1910843 : Blo 562809 1910843 := bstep (se 1 (by rfl) ⟨1433132, by rfl⟩ : syracuseStep 1910843 = 2866265) B2866265
theorem B1911113 : Blo 562809 1911113 := bstep (se 2 (by rfl) ⟨716667, by rfl⟩ : syracuseStep 1911113 = 1433335) B1433335
theorem B1911275 : Blo 562809 1911275 := bstep (se 1 (by rfl) ⟨1433456, by rfl⟩ : syracuseStep 1911275 = 2866913) B2866913
theorem B2141225 : Blo 562809 2141225 := bstep (se 2 (by rfl) ⟨802959, by rfl⟩ : syracuseStep 2141225 = 1605919) B1605919
theorem B633919 : Blo 562809 633919 := bstep (se 1 (by rfl) ⟨475439, by rfl⟩ : syracuseStep 633919 = 950879) B950879
theorem B2141255 : Blo 562809 2141255 := bstep (se 1 (by rfl) ⟨1605941, by rfl⟩ : syracuseStep 2141255 = 3211883) B3211883
theorem B4304015 : Blo 562809 4304015 := bstep (se 1 (by rfl) ⟨3228011, by rfl⟩ : syracuseStep 4304015 = 6456023) B6456023
theorem B1912463 : Blo 562809 1912463 := bstep (se 1 (by rfl) ⟨1434347, by rfl⟩ : syracuseStep 1912463 = 2868695) B2868695
theorem B2404333 : Blo 562809 2404333 := bstep (se 3 (by rfl) ⟨450812, by rfl⟩ : syracuseStep 2404333 = 901625) B901625
theorem B635035 : Blo 562809 635035 := bstep (se 1 (by rfl) ⟨476276, by rfl⟩ : syracuseStep 635035 = 952553) B952553
theorem B2863673 : Blo 562809 2863673 := bstep (se 2 (by rfl) ⟨1073877, by rfl⟩ : syracuseStep 2863673 = 2147755) B2147755
theorem B2142881 : Blo 562809 2142881 := bstep (se 2 (by rfl) ⟨803580, by rfl⟩ : syracuseStep 2142881 = 1607161) B1607161
theorem B4830263 : Blo 562809 4830263 := bstep (se 1 (by rfl) ⟨3622697, by rfl⟩ : syracuseStep 4830263 = 7245395) B7245395
theorem B636223 : Blo 562809 636223 := bstep (se 1 (by rfl) ⟨477167, by rfl⟩ : syracuseStep 636223 = 954335) B954335
theorem B2143853 : Blo 562809 2143853 := bstep (se 3 (by rfl) ⟨401972, by rfl⟩ : syracuseStep 2143853 = 803945) B803945
theorem B636655 : Blo 562809 636655 := bstep (se 1 (by rfl) ⟨477491, by rfl⟩ : syracuseStep 636655 = 954983) B954983
theorem B636763 : Blo 562809 636763 := bstep (se 1 (by rfl) ⟨477572, by rfl⟩ : syracuseStep 636763 = 955145) B955145
theorem B2144171 : Blo 562809 2144171 := bstep (se 1 (by rfl) ⟨1608128, by rfl⟩ : syracuseStep 2144171 = 3216257) B3216257
theorem B6961153 : Blo 562809 6961153 := bstep (se 2 (by rfl) ⟨2610432, by rfl⟩ : syracuseStep 6961153 = 5220865) B5220865
theorem B637159 : Blo 562809 637159 := bstep (se 1 (by rfl) ⟨477869, by rfl⟩ : syracuseStep 637159 = 955739) B955739
theorem B2406779 : Blo 562809 2406779 := bstep (se 1 (by rfl) ⟨1805084, by rfl⟩ : syracuseStep 2406779 = 3610169) B3610169
theorem B3619417 : Blo 562809 3619417 := bstep (se 2 (by rfl) ⟨1357281, by rfl⟩ : syracuseStep 3619417 = 2714563) B2714563
theorem B5159639 : Blo 562809 5159639 := bstep (se 1 (by rfl) ⟨3869729, by rfl⟩ : syracuseStep 5159639 = 7739459) B7739459
theorem B572231 : Blo 562809 572231 := bstep (se 1 (by rfl) ⟨429173, by rfl⟩ : syracuseStep 572231 = 858347) B858347
theorem B3226463 : Blo 562809 3226463 := bstep (se 1 (by rfl) ⟨2419847, by rfl⟩ : syracuseStep 3226463 = 4839695) B4839695
theorem B15678359 : Blo 562809 15678359 := bstep (se 1 (by rfl) ⟨11758769, by rfl⟩ : syracuseStep 15678359 = 23517539) B23517539
theorem B3226715 : Blo 562809 3226715 := bstep (se 1 (by rfl) ⟨2420036, by rfl⟩ : syracuseStep 3226715 = 4840073) B4840073
theorem B13745501 : Blo 562809 13745501 := bstep (se 3 (by rfl) ⟨2577281, by rfl⟩ : syracuseStep 13745501 = 5154563) B5154563
theorem B2866751 : Blo 562809 2866751 := bstep (se 1 (by rfl) ⟨2150063, by rfl⟩ : syracuseStep 2866751 = 4300127) B4300127
theorem B2506943 : Blo 562809 2506943 := bstep (se 1 (by rfl) ⟨1880207, by rfl⟩ : syracuseStep 2506943 = 3760415) B3760415
theorem B1524521 : Blo 562809 1524521 := bstep (se 2 (by rfl) ⟨571695, by rfl⟩ : syracuseStep 1524521 = 1143391) B1143391
theorem B902087 : Blo 562809 902087 := bstep (se 1 (by rfl) ⟨676565, by rfl⟩ : syracuseStep 902087 = 1353131) B1353131
theorem B2409527 : Blo 562809 2409527 := bstep (se 1 (by rfl) ⟨1807145, by rfl⟩ : syracuseStep 2409527 = 3614291) B3614291
theorem B5424205 : Blo 562809 5424205 := bstep (se 3 (by rfl) ⟨1017038, by rfl⟩ : syracuseStep 5424205 = 2034077) B2034077
theorem B2147741 : Blo 562809 2147741 := bstep (se 3 (by rfl) ⟨402701, by rfl⟩ : syracuseStep 2147741 = 805403) B805403
theorem B1361377 : Blo 562809 1361377 := bstep (se 2 (by rfl) ⟨510516, by rfl⟩ : syracuseStep 1361377 = 1021033) B1021033
theorem B2868857 : Blo 562809 2868857 := bstep (se 2 (by rfl) ⟨1075821, by rfl⟩ : syracuseStep 2868857 = 2151643) B2151643
theorem B1427321 : Blo 562809 1427321 := bstep (se 2 (by rfl) ⟨535245, by rfl⟩ : syracuseStep 1427321 = 1070491) B1070491
theorem B2149001 : Blo 562809 2149001 := bstep (se 2 (by rfl) ⟨805875, by rfl⟩ : syracuseStep 2149001 = 1611751) B1611751
theorem B3623723 : Blo 562809 3623723 := bstep (se 1 (by rfl) ⟨2717792, by rfl⟩ : syracuseStep 3623723 = 5435585) B5435585
theorem B8702963 : Blo 562809 8702963 := bstep (se 1 (by rfl) ⟨6527222, by rfl⟩ : syracuseStep 8702963 = 13054445) B13054445
theorem B1428475 : Blo 562809 1428475 := bstep (se 1 (by rfl) ⟨1071356, by rfl⟩ : syracuseStep 1428475 = 2142713) B2142713
theorem B4836347 : Blo 562809 4836347 := bstep (se 1 (by rfl) ⟨3627260, by rfl⟩ : syracuseStep 4836347 = 7254521) B7254521
theorem B642811 : Blo 562809 642811 := bstep (se 1 (by rfl) ⟨482108, by rfl⟩ : syracuseStep 642811 = 964217) B964217
theorem B2707415 : Blo 562809 2707415 := bstep (se 1 (by rfl) ⟨2030561, by rfl⟩ : syracuseStep 2707415 = 4061123) B4061123
theorem B1429559 : Blo 562809 1429559 := bstep (se 1 (by rfl) ⟨1072169, by rfl⟩ : syracuseStep 1429559 = 2144339) B2144339
theorem B1429883 : Blo 562809 1429883 := bstep (se 1 (by rfl) ⟨1072412, by rfl⟩ : syracuseStep 1429883 = 2144825) B2144825
theorem B1266515 : Blo 562809 1266515 := bstep (se 1 (by rfl) ⟨949886, by rfl⟩ : syracuseStep 1266515 = 1899773) B1899773
theorem B1267055 : Blo 562809 1267055 := bstep (se 1 (by rfl) ⟨950291, by rfl⟩ : syracuseStep 1267055 = 1900583) B1900583
theorem B9786743 : Blo 562809 9786743 := bstep (se 1 (by rfl) ⟨7340057, by rfl⟩ : syracuseStep 9786743 = 14680115) B14680115
theorem B1070567 : Blo 562809 1070567 := bstep (se 1 (by rfl) ⟨802925, by rfl⟩ : syracuseStep 1070567 = 1605851) B1605851
theorem B1267487 : Blo 562809 1267487 := bstep (se 1 (by rfl) ⟨950615, by rfl⟩ : syracuseStep 1267487 = 1901231) B1901231
theorem B1267703 : Blo 562809 1267703 := bstep (se 1 (by rfl) ⟨950777, by rfl⟩ : syracuseStep 1267703 = 1901555) B1901555
theorem B2414585 : Blo 562809 2414585 := bstep (se 2 (by rfl) ⟨905469, by rfl⟩ : syracuseStep 2414585 = 1810939) B1810939
theorem B94197917 : Blo 562809 94197917 := bstep (se 3 (by rfl) ⟨17662109, by rfl⟩ : syracuseStep 94197917 = 35324219) B35324219
theorem B4282631 : Blo 562809 4282631 := bstep (se 1 (by rfl) ⟨3211973, by rfl⟩ : syracuseStep 4282631 = 6423947) B6423947
theorem B1268063 : Blo 562809 1268063 := bstep (se 1 (by rfl) ⟨951047, by rfl⟩ : syracuseStep 1268063 = 1902095) B1902095
theorem B1202663 : Blo 562809 1202663 := bstep (se 1 (by rfl) ⟨901997, by rfl⟩ : syracuseStep 1202663 = 1803995) B1803995
theorem B6445817 : Blo 562809 6445817 := bstep (se 2 (by rfl) ⟨2417181, by rfl⟩ : syracuseStep 6445817 = 4834363) B4834363
theorem B1268603 : Blo 562809 1268603 := bstep (se 1 (by rfl) ⟨951452, by rfl⟩ : syracuseStep 1268603 = 1902905) B1902905
theorem B1530859 : Blo 562809 1530859 := bstep (se 1 (by rfl) ⟨1148144, by rfl⟩ : syracuseStep 1530859 = 2296289) B2296289
theorem B1268783 : Blo 562809 1268783 := bstep (se 1 (by rfl) ⟨951587, by rfl⟩ : syracuseStep 1268783 = 1903175) B1903175
theorem B1465847 : Blo 562809 1465847 := bstep (se 1 (by rfl) ⟨1099385, by rfl⟩ : syracuseStep 1465847 = 2198771) B2198771
theorem B3661433 : Blo 562809 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B1269467 : Blo 562809 1269467 := bstep (se 1 (by rfl) ⟨952100, by rfl⟩ : syracuseStep 1269467 = 1904201) B1904201
theorem B4874003 : Blo 562809 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B2416567 : Blo 562809 2416567 := bstep (se 1 (by rfl) ⟨1812425, by rfl⟩ : syracuseStep 2416567 = 3624851) B3624851
theorem B1269737 : Blo 562809 1269737 := bstep (se 2 (by rfl) ⟨476151, by rfl⟩ : syracuseStep 1269737 = 952303) B952303
theorem B44130365 : Blo 562809 44130365 := bstep (se 3 (by rfl) ⟨8274443, by rfl⟩ : syracuseStep 44130365 = 16548887) B16548887
theorem B1073407 : Blo 562809 1073407 := bstep (se 1 (by rfl) ⟨805055, by rfl⟩ : syracuseStep 1073407 = 1610111) B1610111
theorem B6119705 : Blo 562809 6119705 := bstep (se 2 (by rfl) ⟨2294889, by rfl⟩ : syracuseStep 6119705 = 4589779) B4589779
theorem B6873673 : Blo 562809 6873673 := bstep (se 2 (by rfl) ⟨2577627, by rfl⟩ : syracuseStep 6873673 = 5155255) B5155255
theorem B2286247 : Blo 562809 2286247 := bstep (se 1 (by rfl) ⟨1714685, by rfl⟩ : syracuseStep 2286247 = 3429371) B3429371
theorem B1270439 : Blo 562809 1270439 := bstep (se 1 (by rfl) ⟨952829, by rfl⟩ : syracuseStep 1270439 = 1905659) B1905659
theorem B1270583 : Blo 562809 1270583 := bstep (se 1 (by rfl) ⟨952937, by rfl⟩ : syracuseStep 1270583 = 1905875) B1905875
theorem B1270763 : Blo 562809 1270763 := bstep (se 1 (by rfl) ⟨953072, by rfl⟩ : syracuseStep 1270763 = 1906145) B1906145
theorem B844847 : Blo 562809 844847 := bstep (se 1 (by rfl) ⟨633635, by rfl⟩ : syracuseStep 844847 = 1267271) B1267271
theorem B844967 : Blo 562809 844967 := bstep (se 1 (by rfl) ⟨633725, by rfl⟩ : syracuseStep 844967 = 1267451) B1267451
theorem B1271195 : Blo 562809 1271195 := bstep (se 1 (by rfl) ⟨953396, by rfl⟩ : syracuseStep 1271195 = 1906793) B1906793
theorem B845339 : Blo 562809 845339 := bstep (se 1 (by rfl) ⟨634004, by rfl⟩ : syracuseStep 845339 = 1268009) B1268009
theorem B4286033 : Blo 562809 4286033 := bstep (se 2 (by rfl) ⟨1607262, by rfl⟩ : syracuseStep 4286033 = 3214525) B3214525
theorem B26109773 : Blo 562809 26109773 := bstep (se 3 (by rfl) ⟨4895582, by rfl⟩ : syracuseStep 26109773 = 9791165) B9791165
theorem B845723 : Blo 562809 845723 := bstep (se 1 (by rfl) ⟨634292, by rfl⟩ : syracuseStep 845723 = 1268585) B1268585
theorem B845759 : Blo 562809 845759 := bstep (se 1 (by rfl) ⟨634319, by rfl⟩ : syracuseStep 845759 = 1268639) B1268639
theorem B1271771 : Blo 562809 1271771 := bstep (se 1 (by rfl) ⟨953828, by rfl⟩ : syracuseStep 1271771 = 1907657) B1907657
theorem B845945 : Blo 562809 845945 := bstep (se 2 (by rfl) ⟨317229, by rfl⟩ : syracuseStep 845945 = 634459) B634459
theorem B2058383 : Blo 562809 2058383 := bstep (se 1 (by rfl) ⟨1543787, by rfl⟩ : syracuseStep 2058383 = 3087575) B3087575
theorem B1271951 : Blo 562809 1271951 := bstep (se 1 (by rfl) ⟨953963, by rfl⟩ : syracuseStep 1271951 = 1907927) B1907927
theorem B2582699 : Blo 562809 2582699 := bstep (se 1 (by rfl) ⟨1937024, by rfl⟩ : syracuseStep 2582699 = 3874049) B3874049
theorem B1272041 : Blo 562809 1272041 := bstep (se 2 (by rfl) ⟨477015, by rfl⟩ : syracuseStep 1272041 = 954031) B954031
theorem B715063 : Blo 562809 715063 := bstep (se 1 (by rfl) ⟨536297, by rfl⟩ : syracuseStep 715063 = 1072595) B1072595
theorem B1075511 : Blo 562809 1075511 := bstep (se 1 (by rfl) ⟨806633, by rfl⟩ : syracuseStep 1075511 = 1613267) B1613267
theorem B1272311 : Blo 562809 1272311 := bstep (se 1 (by rfl) ⟨954233, by rfl⟩ : syracuseStep 1272311 = 1908467) B1908467
theorem B846329 : Blo 562809 846329 := bstep (se 2 (by rfl) ⟨317373, by rfl⟩ : syracuseStep 846329 = 634747) B634747
theorem B846383 : Blo 562809 846383 := bstep (se 1 (by rfl) ⟨634787, by rfl⟩ : syracuseStep 846383 = 1269575) B1269575
theorem B9136739 : Blo 562809 9136739 := bstep (se 1 (by rfl) ⟨6852554, by rfl⟩ : syracuseStep 9136739 = 13705109) B13705109
theorem B3435425 : Blo 562809 3435425 := bstep (se 2 (by rfl) ⟨1288284, by rfl⟩ : syracuseStep 3435425 = 2576569) B2576569
theorem B846815 : Blo 562809 846815 := bstep (se 1 (by rfl) ⟨635111, by rfl⟩ : syracuseStep 846815 = 1270223) B1270223
theorem B1272905 : Blo 562809 1272905 := bstep (se 2 (by rfl) ⟨477339, by rfl⟩ : syracuseStep 1272905 = 954679) B954679
theorem B847259 : Blo 562809 847259 := bstep (se 1 (by rfl) ⟨635444, by rfl⟩ : syracuseStep 847259 = 1270889) B1270889
theorem B5795309 : Blo 562809 5795309 := bstep (se 3 (by rfl) ⟨1086620, by rfl⟩ : syracuseStep 5795309 = 2173241) B2173241
theorem B5434937 : Blo 562809 5434937 := bstep (se 2 (by rfl) ⟨2038101, by rfl⟩ : syracuseStep 5434937 = 4076203) B4076203
theorem B1371791 : Blo 562809 1371791 := bstep (se 1 (by rfl) ⟨1028843, by rfl⟩ : syracuseStep 1371791 = 2057687) B2057687
theorem B847679 : Blo 562809 847679 := bstep (se 1 (by rfl) ⟨635759, by rfl⟩ : syracuseStep 847679 = 1271519) B1271519
theorem B4288463 : Blo 562809 4288463 := bstep (se 1 (by rfl) ⟨3216347, by rfl⟩ : syracuseStep 4288463 = 6432695) B6432695
theorem B847865 : Blo 562809 847865 := bstep (se 2 (by rfl) ⟨317949, by rfl⟩ : syracuseStep 847865 = 635899) B635899
theorem B41087033 : Blo 562809 41087033 := bstep (se 2 (by rfl) ⟨15407637, by rfl⟩ : syracuseStep 41087033 = 30815275) B30815275
theorem B12415169 : Blo 562809 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B848105 : Blo 562809 848105 := bstep (se 2 (by rfl) ⟨318039, by rfl⟩ : syracuseStep 848105 = 636079) B636079
theorem B848231 : Blo 562809 848231 := bstep (se 1 (by rfl) ⟨636173, by rfl⟩ : syracuseStep 848231 = 1272347) B1272347
theorem B1274633 : Blo 562809 1274633 := bstep (se 2 (by rfl) ⟨477987, by rfl⟩ : syracuseStep 1274633 = 955975) B955975
theorem B1274687 : Blo 562809 1274687 := bstep (se 1 (by rfl) ⟨956015, by rfl⟩ : syracuseStep 1274687 = 1912031) B1912031
theorem B848777 : Blo 562809 848777 := bstep (se 2 (by rfl) ⟨318291, by rfl⟩ : syracuseStep 848777 = 636583) B636583
theorem B1274831 : Blo 562809 1274831 := bstep (se 1 (by rfl) ⟨956123, by rfl⟩ : syracuseStep 1274831 = 1912247) B1912247
theorem B1274921 : Blo 562809 1274921 := bstep (se 2 (by rfl) ⟨478095, by rfl⟩ : syracuseStep 1274921 = 956191) B956191
theorem B849161 : Blo 562809 849161 := bstep (se 2 (by rfl) ⟨318435, by rfl⟩ : syracuseStep 849161 = 636871) B636871
theorem B849215 : Blo 562809 849215 := bstep (se 1 (by rfl) ⟨636911, by rfl⟩ : syracuseStep 849215 = 1273823) B1273823
theorem B1275209 : Blo 562809 1275209 := bstep (se 2 (by rfl) ⟨478203, by rfl⟩ : syracuseStep 1275209 = 956407) B956407
theorem B3044699 : Blo 562809 3044699 := bstep (se 1 (by rfl) ⟨2283524, by rfl⟩ : syracuseStep 3044699 = 4567049) B4567049
theorem B6288835 : Blo 562809 6288835 := bstep (se 1 (by rfl) ⟨4716626, by rfl⟩ : syracuseStep 6288835 = 9433253) B9433253
theorem B849641 : Blo 562809 849641 := bstep (se 2 (by rfl) ⟨318615, by rfl⟩ : syracuseStep 849641 = 637231) B637231
theorem B11138795 : Blo 562809 11138795 := bstep (se 1 (by rfl) ⟨8354096, by rfl⟩ : syracuseStep 11138795 = 16708193) B16708193
theorem B849647 : Blo 562809 849647 := bstep (se 1 (by rfl) ⟨637235, by rfl⟩ : syracuseStep 849647 = 1274471) B1274471
theorem B9631547 : Blo 562809 9631547 := bstep (se 1 (by rfl) ⟨7223660, by rfl⟩ : syracuseStep 9631547 = 14447321) B14447321
theorem B3438443 : Blo 562809 3438443 := bstep (se 1 (by rfl) ⟨2578832, by rfl⟩ : syracuseStep 3438443 = 5157665) B5157665
theorem B850103 : Blo 562809 850103 := bstep (se 1 (by rfl) ⟨637577, by rfl⟩ : syracuseStep 850103 = 1275155) B1275155
theorem B850151 : Blo 562809 850151 := bstep (se 1 (by rfl) ⟨637613, by rfl⟩ : syracuseStep 850151 = 1275227) B1275227
theorem B21690665 : Blo 562809 21690665 := bstep (se 2 (by rfl) ⟨8133999, by rfl⟩ : syracuseStep 21690665 = 16267999) B16267999
theorem B8125697 : Blo 562809 8125697 := bstep (se 2 (by rfl) ⟨3047136, by rfl⟩ : syracuseStep 8125697 = 6094273) B6094273
theorem B8158913 : Blo 562809 8158913 := bstep (se 2 (by rfl) ⟨3059592, by rfl⟩ : syracuseStep 8158913 = 6119185) B6119185
theorem B1900367 : Blo 562809 1900367 := bstep (se 1 (by rfl) ⟨1425275, by rfl⟩ : syracuseStep 1900367 = 2850551) B2850551
theorem B1900799 : Blo 562809 1900799 := bstep (se 1 (by rfl) ⟨1425599, by rfl⟩ : syracuseStep 1900799 = 2851199) B2851199
theorem B6685181 : Blo 562809 6685181 := bstep (se 3 (by rfl) ⟨1253471, by rfl⟩ : syracuseStep 6685181 = 2506943) B2506943
theorem B9798425 : Blo 562809 9798425 := bstep (se 2 (by rfl) ⟨3674409, by rfl⟩ : syracuseStep 9798425 = 7348819) B7348819
theorem B3048329 : Blo 562809 3048329 := bstep (se 2 (by rfl) ⟨1143123, by rfl⟩ : syracuseStep 3048329 = 2286247) B2286247
theorem B951547 : Blo 562809 951547 := bstep (se 1 (by rfl) ⟨713660, by rfl⟩ : syracuseStep 951547 = 1427321) B1427321
theorem B3671401 : Blo 562809 3671401 := bstep (se 2 (by rfl) ⟨1376775, by rfl⟩ : syracuseStep 3671401 = 2753551) B2753551
theorem B3475007 : Blo 562809 3475007 := bstep (se 1 (by rfl) ⟨2606255, by rfl⟩ : syracuseStep 3475007 = 5212511) B5212511
theorem B2033387 : Blo 562809 2033387 := bstep (se 1 (by rfl) ⟨1525040, by rfl⟩ : syracuseStep 2033387 = 3050081) B3050081
theorem B5801975 : Blo 562809 5801975 := bstep (se 1 (by rfl) ⟨4351481, by rfl⟩ : syracuseStep 5801975 = 8702963) B8702963
theorem B4065389 : Blo 562809 4065389 := bstep (se 3 (by rfl) ⟨762260, by rfl⟩ : syracuseStep 4065389 = 1524521) B1524521
theorem B1804943 : Blo 562809 1804943 := bstep (se 1 (by rfl) ⟨1353707, by rfl⟩ : syracuseStep 1804943 = 2707415) B2707415
theorem B953039 : Blo 562809 953039 := bstep (se 1 (by rfl) ⟨714779, by rfl⟩ : syracuseStep 953039 = 1429559) B1429559
theorem B6425405 : Blo 562809 6425405 := bstep (se 3 (by rfl) ⟨1204763, by rfl⟩ : syracuseStep 6425405 = 2409527) B2409527
theorem B953255 : Blo 562809 953255 := bstep (se 1 (by rfl) ⟨714941, by rfl⟩ : syracuseStep 953255 = 1429883) B1429883
theorem B953417 : Blo 562809 953417 := bstep (se 2 (by rfl) ⟨357531, by rfl⟩ : syracuseStep 953417 = 715063) B715063
theorem B6524495 : Blo 562809 6524495 := bstep (se 1 (by rfl) ⟨4893371, by rfl⟩ : syracuseStep 6524495 = 9786743) B9786743
theorem B10849949 : Blo 562809 10849949 := bstep (se 3 (by rfl) ⟨2034365, by rfl⟩ : syracuseStep 10849949 = 4068731) B4068731
theorem B3215051 : Blo 562809 3215051 := bstep (se 1 (by rfl) ⟨2411288, by rfl⟩ : syracuseStep 3215051 = 4822577) B4822577
theorem B1904471 : Blo 562809 1904471 := bstep (se 1 (by rfl) ⟨1428353, by rfl⟩ : syracuseStep 1904471 = 2856707) B2856707
theorem B1904633 : Blo 562809 1904633 := bstep (se 2 (by rfl) ⟨714237, by rfl⟩ : syracuseStep 1904633 = 1428475) B1428475
theorem B1609723 : Blo 562809 1609723 := bstep (se 1 (by rfl) ⟨1207292, by rfl⟩ : syracuseStep 1609723 = 2414585) B2414585
theorem B2855087 : Blo 562809 2855087 := bstep (se 1 (by rfl) ⟨2141315, by rfl⟩ : syracuseStep 2855087 = 4282631) B4282631
theorem B4297211 : Blo 562809 4297211 := bstep (se 1 (by rfl) ⟨3222908, by rfl⟩ : syracuseStep 4297211 = 6445817) B6445817
theorem B1905551 : Blo 562809 1905551 := bstep (se 1 (by rfl) ⟨1429163, by rfl⟩ : syracuseStep 1905551 = 2858327) B2858327
theorem B857081 : Blo 562809 857081 := bstep (se 2 (by rfl) ⟨321405, by rfl⟩ : syracuseStep 857081 = 642811) B642811
theorem B3609629 : Blo 562809 3609629 := bstep (se 3 (by rfl) ⟨676805, by rfl⟩ : syracuseStep 3609629 = 1353611) B1353611
theorem B3249335 : Blo 562809 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B1906091 : Blo 562809 1906091 := bstep (se 1 (by rfl) ⟨1429568, by rfl⟩ : syracuseStep 1906091 = 2859137) B2859137
theorem B6887197 : Blo 562809 6887197 := bstep (se 3 (by rfl) ⟨1291349, by rfl⟩ : syracuseStep 6887197 = 2582699) B2582699
theorem B1906631 : Blo 562809 1906631 := bstep (se 1 (by rfl) ⟨1429973, by rfl⟩ : syracuseStep 1906631 = 2859947) B2859947
theorem B563231 : Blo 562809 563231 := bstep (se 1 (by rfl) ⟨422423, by rfl⟩ : syracuseStep 563231 = 844847) B844847
theorem B3610655 : Blo 562809 3610655 := bstep (se 1 (by rfl) ⟨2707991, by rfl⟩ : syracuseStep 3610655 = 5415983) B5415983
theorem B563311 : Blo 562809 563311 := bstep (se 1 (by rfl) ⟨422483, by rfl⟩ : syracuseStep 563311 = 844967) B844967
theorem B563559 : Blo 562809 563559 := bstep (se 1 (by rfl) ⟨422669, by rfl⟩ : syracuseStep 563559 = 845339) B845339
theorem B2857355 : Blo 562809 2857355 := bstep (se 1 (by rfl) ⟨2143016, by rfl⟩ : syracuseStep 2857355 = 4286033) B4286033
theorem B17406515 : Blo 562809 17406515 := bstep (se 1 (by rfl) ⟨13054886, by rfl⟩ : syracuseStep 17406515 = 26109773) B26109773
theorem B563815 : Blo 562809 563815 := bstep (se 1 (by rfl) ⟨422861, by rfl⟩ : syracuseStep 563815 = 845723) B845723
theorem B563839 : Blo 562809 563839 := bstep (se 1 (by rfl) ⟨422879, by rfl⟩ : syracuseStep 563839 = 845759) B845759
theorem B563963 : Blo 562809 563963 := bstep (se 1 (by rfl) ⟨422972, by rfl⟩ : syracuseStep 563963 = 845945) B845945
theorem B564219 : Blo 562809 564219 := bstep (se 1 (by rfl) ⟨423164, by rfl⟩ : syracuseStep 564219 = 846329) B846329
theorem B564255 : Blo 562809 564255 := bstep (se 1 (by rfl) ⟨423191, by rfl⟩ : syracuseStep 564255 = 846383) B846383
theorem B564543 : Blo 562809 564543 := bstep (se 1 (by rfl) ⟨423407, by rfl⟩ : syracuseStep 564543 = 846815) B846815
theorem B564839 : Blo 562809 564839 := bstep (se 1 (by rfl) ⟨423629, by rfl⟩ : syracuseStep 564839 = 847259) B847259
theorem B565119 : Blo 562809 565119 := bstep (se 1 (by rfl) ⟨423839, by rfl⟩ : syracuseStep 565119 = 847679) B847679
theorem B2858975 : Blo 562809 2858975 := bstep (se 1 (by rfl) ⟨2144231, by rfl⟩ : syracuseStep 2858975 = 4288463) B4288463
theorem B565243 : Blo 562809 565243 := bstep (se 1 (by rfl) ⟨423932, by rfl⟩ : syracuseStep 565243 = 847865) B847865
theorem B9281537 : Blo 562809 9281537 := bstep (se 2 (by rfl) ⟨3480576, by rfl⟩ : syracuseStep 9281537 = 6961153) B6961153
theorem B565403 : Blo 562809 565403 := bstep (se 1 (by rfl) ⟨424052, by rfl⟩ : syracuseStep 565403 = 848105) B848105
theorem B565487 : Blo 562809 565487 := bstep (se 1 (by rfl) ⟨424115, by rfl⟩ : syracuseStep 565487 = 848231) B848231
theorem B1909115 : Blo 562809 1909115 := bstep (se 1 (by rfl) ⟨1431836, by rfl⟩ : syracuseStep 1909115 = 2863673) B2863673
theorem B565851 : Blo 562809 565851 := bstep (se 1 (by rfl) ⟨424388, by rfl⟩ : syracuseStep 565851 = 848777) B848777
theorem B3220175 : Blo 562809 3220175 := bstep (se 1 (by rfl) ⟨2415131, by rfl⟩ : syracuseStep 3220175 = 4830263) B4830263
theorem B4825889 : Blo 562809 4825889 := bstep (se 2 (by rfl) ⟨1809708, by rfl⟩ : syracuseStep 4825889 = 3619417) B3619417
theorem B566107 : Blo 562809 566107 := bstep (se 1 (by rfl) ⟨424580, by rfl⟩ : syracuseStep 566107 = 849161) B849161
theorem B566143 : Blo 562809 566143 := bstep (se 1 (by rfl) ⟨424607, by rfl⟩ : syracuseStep 566143 = 849215) B849215
theorem B566427 : Blo 562809 566427 := bstep (se 1 (by rfl) ⟨424820, by rfl⟩ : syracuseStep 566427 = 849641) B849641
theorem B566431 : Blo 562809 566431 := bstep (se 1 (by rfl) ⟨424823, by rfl⟩ : syracuseStep 566431 = 849647) B849647
theorem B2041145 : Blo 562809 2041145 := bstep (se 2 (by rfl) ⟨765429, by rfl⟩ : syracuseStep 2041145 = 1530859) B1530859
theorem B566735 : Blo 562809 566735 := bstep (se 1 (by rfl) ⟨425051, by rfl⟩ : syracuseStep 566735 = 850103) B850103
theorem B566767 : Blo 562809 566767 := bstep (se 1 (by rfl) ⟨425075, by rfl⟩ : syracuseStep 566767 = 850151) B850151
theorem B14460443 : Blo 562809 14460443 := bstep (se 1 (by rfl) ⟨10845332, by rfl⟩ : syracuseStep 14460443 = 21690665) B21690665
theorem B5417131 : Blo 562809 5417131 := bstep (se 1 (by rfl) ⟨4062848, by rfl⟩ : syracuseStep 5417131 = 8125697) B8125697
theorem B1911167 : Blo 562809 1911167 := bstep (se 1 (by rfl) ⟨1433375, by rfl⟩ : syracuseStep 1911167 = 2866751) B2866751
theorem B3222089 : Blo 562809 3222089 := bstep (se 2 (by rfl) ⟨1208283, by rfl⟩ : syracuseStep 3222089 = 2416567) B2416567
theorem B2796713 : Blo 562809 2796713 := bstep (se 2 (by rfl) ⟨1048767, by rfl⟩ : syracuseStep 2796713 = 2097535) B2097535
theorem B601391 : Blo 562809 601391 := bstep (se 1 (by rfl) ⟨451043, by rfl⟩ : syracuseStep 601391 = 902087) B902087
theorem B1912571 : Blo 562809 1912571 := bstep (se 1 (by rfl) ⟨1434428, by rfl⟩ : syracuseStep 1912571 = 2868857) B2868857
theorem B9154903 : Blo 562809 9154903 := bstep (se 1 (by rfl) ⟨6866177, by rfl⟩ : syracuseStep 9154903 = 13732355) B13732355
theorem B3060287 : Blo 562809 3060287 := bstep (se 1 (by rfl) ⟨2295215, by rfl⟩ : syracuseStep 3060287 = 4590431) B4590431
theorem B1815169 : Blo 562809 1815169 := bstep (se 2 (by rfl) ⟨680688, by rfl⟩ : syracuseStep 1815169 = 1361377) B1361377
theorem B3224231 : Blo 562809 3224231 := bstep (se 1 (by rfl) ⟨2418173, by rfl⟩ : syracuseStep 3224231 = 4836347) B4836347
theorem B2406095 : Blo 562809 2406095 := bstep (se 1 (by rfl) ⟨1804571, by rfl⟩ : syracuseStep 2406095 = 3609143) B3609143
theorem B3258251 : Blo 562809 3258251 := bstep (se 1 (by rfl) ⟨2443688, by rfl⟩ : syracuseStep 3258251 = 4887377) B4887377
theorem B3127531 : Blo 562809 3127531 := bstep (se 1 (by rfl) ⟨2345648, by rfl⟩ : syracuseStep 3127531 = 4691297) B4691297
theorem B2865455 : Blo 562809 2865455 := bstep (se 1 (by rfl) ⟨2149091, by rfl⟩ : syracuseStep 2865455 = 4298183) B4298183
theorem B571951 : Blo 562809 571951 := bstep (se 1 (by rfl) ⟨428963, by rfl⟩ : syracuseStep 571951 = 857927) B857927
theorem B62798611 : Blo 562809 62798611 := bstep (se 1 (by rfl) ⟨47098958, by rfl⟩ : syracuseStep 62798611 = 94197917) B94197917
theorem B801775 : Blo 562809 801775 := bstep (se 1 (by rfl) ⟨601331, by rfl⟩ : syracuseStep 801775 = 1202663) B1202663
theorem B4832723 : Blo 562809 4832723 := bstep (se 1 (by rfl) ⟨3624542, by rfl⟩ : syracuseStep 4832723 = 7249085) B7249085
theorem B1424891 : Blo 562809 1424891 := bstep (se 1 (by rfl) ⟨1068668, by rfl⟩ : syracuseStep 1424891 = 2137337) B2137337
theorem B2440955 : Blo 562809 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B4112207 : Blo 562809 4112207 := bstep (se 1 (by rfl) ⟨3084155, by rfl⟩ : syracuseStep 4112207 = 6168311) B6168311
theorem B1425235 : Blo 562809 1425235 := bstep (se 1 (by rfl) ⟨1068926, by rfl⟩ : syracuseStep 1425235 = 2137853) B2137853
theorem B4079803 : Blo 562809 4079803 := bstep (se 1 (by rfl) ⟨3059852, by rfl⟩ : syracuseStep 4079803 = 6119705) B6119705
theorem B1425671 : Blo 562809 1425671 := bstep (se 1 (by rfl) ⟨1069253, by rfl⟩ : syracuseStep 1425671 = 2138507) B2138507
theorem B5489021 : Blo 562809 5489021 := bstep (se 3 (by rfl) ⟨1029191, by rfl⟩ : syracuseStep 5489021 = 2058383) B2058383
theorem B4113139 : Blo 562809 4113139 := bstep (se 1 (by rfl) ⟨3084854, by rfl⟩ : syracuseStep 4113139 = 6169709) B6169709
theorem B5423897 : Blo 562809 5423897 := bstep (se 2 (by rfl) ⟨2033961, by rfl⟩ : syracuseStep 5423897 = 4067923) B4067923
theorem B24364637 : Blo 562809 24364637 := bstep (se 3 (by rfl) ⟨4568369, by rfl⟩ : syracuseStep 24364637 = 9136739) B9136739
theorem B1427483 : Blo 562809 1427483 := bstep (se 1 (by rfl) ⟨1070612, by rfl⟩ : syracuseStep 1427483 = 2141225) B2141225
theorem B1427503 : Blo 562809 1427503 := bstep (se 1 (by rfl) ⟨1070627, by rfl⟩ : syracuseStep 1427503 = 2141255) B2141255
theorem B2869343 : Blo 562809 2869343 := bstep (se 1 (by rfl) ⟨2152007, by rfl⟩ : syracuseStep 2869343 = 4304015) B4304015
theorem B1525949 : Blo 562809 1525949 := bstep (se 3 (by rfl) ⟨286115, by rfl⟩ : syracuseStep 1525949 = 572231) B572231
theorem B3623291 : Blo 562809 3623291 := bstep (se 1 (by rfl) ⟨2717468, by rfl⟩ : syracuseStep 3623291 = 5434937) B5434937
theorem B8276779 : Blo 562809 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B1428587 : Blo 562809 1428587 := bstep (se 1 (by rfl) ⟨1071440, by rfl⟩ : syracuseStep 1428587 = 2142881) B2142881
theorem B1429235 : Blo 562809 1429235 := bstep (se 1 (by rfl) ⟨1071926, by rfl⟩ : syracuseStep 1429235 = 2143853) B2143853
theorem B7425863 : Blo 562809 7425863 := bstep (se 1 (by rfl) ⟨5569397, by rfl⟩ : syracuseStep 7425863 = 11138795) B11138795
theorem B1429447 : Blo 562809 1429447 := bstep (se 1 (by rfl) ⟨1072085, by rfl⟩ : syracuseStep 1429447 = 2144171) B2144171
theorem B2150975 : Blo 562809 2150975 := bstep (se 1 (by rfl) ⟨1613231, by rfl⟩ : syracuseStep 2150975 = 3226463) B3226463
theorem B2151143 : Blo 562809 2151143 := bstep (se 1 (by rfl) ⟨1613357, by rfl⟩ : syracuseStep 2151143 = 3226715) B3226715
theorem B9163667 : Blo 562809 9163667 := bstep (se 1 (by rfl) ⟨6872750, by rfl⟩ : syracuseStep 9163667 = 13745501) B13745501
theorem B1266911 : Blo 562809 1266911 := bstep (se 1 (by rfl) ⟨950183, by rfl⟩ : syracuseStep 1266911 = 1900367) B1900367
theorem B1267343 : Blo 562809 1267343 := bstep (se 1 (by rfl) ⟨950507, by rfl⟩ : syracuseStep 1267343 = 1901015) B1901015
theorem B1431209 : Blo 562809 1431209 := bstep (se 2 (by rfl) ⟨536703, by rfl⟩ : syracuseStep 1431209 = 1073407) B1073407
theorem B1267433 : Blo 562809 1267433 := bstep (se 2 (by rfl) ⟨475287, by rfl⟩ : syracuseStep 1267433 = 950575) B950575
theorem B9164897 : Blo 562809 9164897 := bstep (se 2 (by rfl) ⟨3436836, by rfl⟩ : syracuseStep 9164897 = 6873673) B6873673
theorem B1431827 : Blo 562809 1431827 := bstep (se 1 (by rfl) ⟨1073870, by rfl⟩ : syracuseStep 1431827 = 2147741) B2147741
theorem B7232273 : Blo 562809 7232273 := bstep (se 2 (by rfl) ⟨2712102, by rfl⟩ : syracuseStep 7232273 = 5424205) B5424205
theorem B1432667 : Blo 562809 1432667 := bstep (se 1 (by rfl) ⟨1074500, by rfl⟩ : syracuseStep 1432667 = 2149001) B2149001
theorem B2415815 : Blo 562809 2415815 := bstep (se 1 (by rfl) ⟨1811861, by rfl⟩ : syracuseStep 2415815 = 3623723) B3623723
theorem B1269071 : Blo 562809 1269071 := bstep (se 1 (by rfl) ⟨951803, by rfl⟩ : syracuseStep 1269071 = 1903607) B1903607
theorem B1072511 : Blo 562809 1072511 := bstep (se 1 (by rfl) ⟨804383, by rfl⟩ : syracuseStep 1072511 = 1608767) B1608767
theorem B3628415 : Blo 562809 3628415 := bstep (se 1 (by rfl) ⟨2721311, by rfl⟩ : syracuseStep 3628415 = 5442623) B5442623
theorem B1269161 : Blo 562809 1269161 := bstep (se 2 (by rfl) ⟨475935, by rfl⟩ : syracuseStep 1269161 = 951871) B951871
theorem B4284089 : Blo 562809 4284089 := bstep (se 2 (by rfl) ⟨1606533, by rfl⟩ : syracuseStep 4284089 = 3213067) B3213067
theorem B848977955 : Blo 562809 848977955 := bstep (se 1 (by rfl) ⟨636733466, by rfl⟩ : syracuseStep 848977955 = 1273466933) B1273466933
theorem B844343 : Blo 562809 844343 := bstep (se 1 (by rfl) ⟨633257, by rfl⟩ : syracuseStep 844343 = 1266515) B1266515
theorem B844703 : Blo 562809 844703 := bstep (se 1 (by rfl) ⟨633527, by rfl⟩ : syracuseStep 844703 = 1267055) B1267055
theorem B713711 : Blo 562809 713711 := bstep (se 1 (by rfl) ⟨535283, by rfl⟩ : syracuseStep 713711 = 1070567) B1070567
theorem B844991 : Blo 562809 844991 := bstep (se 1 (by rfl) ⟨633743, by rfl⟩ : syracuseStep 844991 = 1267487) B1267487
theorem B845135 : Blo 562809 845135 := bstep (se 1 (by rfl) ⟨633851, by rfl⟩ : syracuseStep 845135 = 1267703) B1267703
theorem B2450843 : Blo 562809 2450843 := bstep (se 1 (by rfl) ⟨1838132, by rfl⟩ : syracuseStep 2450843 = 3676265) B3676265
theorem B845225 : Blo 562809 845225 := bstep (se 2 (by rfl) ⟨316959, by rfl⟩ : syracuseStep 845225 = 633919) B633919
theorem B9627173 : Blo 562809 9627173 := bstep (se 4 (by rfl) ⟨902547, by rfl⟩ : syracuseStep 9627173 = 1805095) B1805095
theorem B845375 : Blo 562809 845375 := bstep (se 1 (by rfl) ⟨634031, by rfl⟩ : syracuseStep 845375 = 1268063) B1268063
theorem B1271375 : Blo 562809 1271375 := bstep (se 1 (by rfl) ⟨953531, by rfl⟩ : syracuseStep 1271375 = 1907063) B1907063
theorem B845735 : Blo 562809 845735 := bstep (se 1 (by rfl) ⟨634301, by rfl⟩ : syracuseStep 845735 = 1268603) B1268603
theorem B845855 : Blo 562809 845855 := bstep (se 1 (by rfl) ⟨634391, by rfl⟩ : syracuseStep 845855 = 1268783) B1268783
theorem B1272095 : Blo 562809 1272095 := bstep (se 1 (by rfl) ⟨954071, by rfl⟩ : syracuseStep 1272095 = 1908143) B1908143
theorem B977231 : Blo 562809 977231 := bstep (se 1 (by rfl) ⟨732923, by rfl⟩ : syracuseStep 977231 = 1465847) B1465847
theorem B846311 : Blo 562809 846311 := bstep (se 1 (by rfl) ⟨634733, by rfl⟩ : syracuseStep 846311 = 1269467) B1269467
theorem B3205777 : Blo 562809 3205777 := bstep (se 2 (by rfl) ⟨1202166, by rfl⟩ : syracuseStep 3205777 = 2404333) B2404333
theorem B846491 : Blo 562809 846491 := bstep (se 1 (by rfl) ⟨634868, by rfl⟩ : syracuseStep 846491 = 1269737) B1269737
theorem B7563959 : Blo 562809 7563959 := bstep (se 1 (by rfl) ⟨5672969, by rfl⟩ : syracuseStep 7563959 = 11345939) B11345939
theorem B29420243 : Blo 562809 29420243 := bstep (se 1 (by rfl) ⟨22065182, by rfl⟩ : syracuseStep 29420243 = 44130365) B44130365
theorem B1272617 : Blo 562809 1272617 := bstep (se 2 (by rfl) ⟨477231, by rfl⟩ : syracuseStep 1272617 = 954463) B954463
theorem B846713 : Blo 562809 846713 := bstep (se 2 (by rfl) ⟨317517, by rfl⟩ : syracuseStep 846713 = 635035) B635035
theorem B9923627 : Blo 562809 9923627 := bstep (se 1 (by rfl) ⟨7442720, by rfl⟩ : syracuseStep 9923627 = 14885441) B14885441
theorem B1272887 : Blo 562809 1272887 := bstep (se 1 (by rfl) ⟨954665, by rfl⟩ : syracuseStep 1272887 = 1909331) B1909331
theorem B846959 : Blo 562809 846959 := bstep (se 1 (by rfl) ⟨635219, by rfl⟩ : syracuseStep 846959 = 1270439) B1270439
theorem B847055 : Blo 562809 847055 := bstep (se 1 (by rfl) ⟨635291, by rfl⟩ : syracuseStep 847055 = 1270583) B1270583
theorem B1273067 : Blo 562809 1273067 := bstep (se 1 (by rfl) ⟨954800, by rfl⟩ : syracuseStep 1273067 = 1909601) B1909601
theorem B847175 : Blo 562809 847175 := bstep (se 1 (by rfl) ⟨635381, by rfl⟩ : syracuseStep 847175 = 1270763) B1270763
theorem B847463 : Blo 562809 847463 := bstep (se 1 (by rfl) ⟨635597, by rfl⟩ : syracuseStep 847463 = 1271195) B1271195
theorem B847847 : Blo 562809 847847 := bstep (se 1 (by rfl) ⟨635885, by rfl⟩ : syracuseStep 847847 = 1271771) B1271771
theorem B1273895 : Blo 562809 1273895 := bstep (se 1 (by rfl) ⟨955421, by rfl⟩ : syracuseStep 1273895 = 1910843) B1910843
theorem B847967 : Blo 562809 847967 := bstep (se 1 (by rfl) ⟨635975, by rfl⟩ : syracuseStep 847967 = 1271951) B1271951
theorem B848027 : Blo 562809 848027 := bstep (se 1 (by rfl) ⟨636020, by rfl⟩ : syracuseStep 848027 = 1272041) B1272041
theorem B717007 : Blo 562809 717007 := bstep (se 1 (by rfl) ⟨537755, by rfl⟩ : syracuseStep 717007 = 1075511) B1075511
theorem B1274075 : Blo 562809 1274075 := bstep (se 1 (by rfl) ⟨955556, by rfl⟩ : syracuseStep 1274075 = 1911113) B1911113
theorem B1274183 : Blo 562809 1274183 := bstep (se 1 (by rfl) ⟨955637, by rfl⟩ : syracuseStep 1274183 = 1911275) B1911275
theorem B848207 : Blo 562809 848207 := bstep (se 1 (by rfl) ⟨636155, by rfl⟩ : syracuseStep 848207 = 1272311) B1272311
theorem B848297 : Blo 562809 848297 := bstep (se 2 (by rfl) ⟨318111, by rfl⟩ : syracuseStep 848297 = 636223) B636223
theorem B1274345 : Blo 562809 1274345 := bstep (se 2 (by rfl) ⟨477879, by rfl⟩ : syracuseStep 1274345 = 955759) B955759
theorem B8385113 : Blo 562809 8385113 := bstep (se 2 (by rfl) ⟨3144417, by rfl⟩ : syracuseStep 8385113 = 6288835) B6288835
theorem B2290283 : Blo 562809 2290283 := bstep (se 1 (by rfl) ⟨1717712, by rfl⟩ : syracuseStep 2290283 = 3435425) B3435425
theorem B848603 : Blo 562809 848603 := bstep (se 1 (by rfl) ⟨636452, by rfl⟩ : syracuseStep 848603 = 1272905) B1272905
theorem B848873 : Blo 562809 848873 := bstep (se 2 (by rfl) ⟨318327, by rfl⟩ : syracuseStep 848873 = 636655) B636655
theorem B3863539 : Blo 562809 3863539 := bstep (se 1 (by rfl) ⟨2897654, by rfl⟩ : syracuseStep 3863539 = 5795309) B5795309
theorem B914527 : Blo 562809 914527 := bstep (se 1 (by rfl) ⟨685895, by rfl⟩ : syracuseStep 914527 = 1371791) B1371791
theorem B1274975 : Blo 562809 1274975 := bstep (se 1 (by rfl) ⟨956231, by rfl⟩ : syracuseStep 1274975 = 1912463) B1912463
theorem B849017 : Blo 562809 849017 := bstep (se 2 (by rfl) ⟨318381, by rfl⟩ : syracuseStep 849017 = 636763) B636763
theorem B27391355 : Blo 562809 27391355 := bstep (se 1 (by rfl) ⟨20543516, by rfl⟩ : syracuseStep 27391355 = 41087033) B41087033
theorem B849545 : Blo 562809 849545 := bstep (se 2 (by rfl) ⟨318579, by rfl⟩ : syracuseStep 849545 = 637159) B637159
theorem B849755 : Blo 562809 849755 := bstep (se 1 (by rfl) ⟨637316, by rfl⟩ : syracuseStep 849755 = 1274633) B1274633
theorem B2291581 : Blo 562809 2291581 := bstep (se 3 (by rfl) ⟨429671, by rfl⟩ : syracuseStep 2291581 = 859343) B859343
theorem B849791 : Blo 562809 849791 := bstep (se 1 (by rfl) ⟨637343, by rfl⟩ : syracuseStep 849791 = 1274687) B1274687
theorem B849887 : Blo 562809 849887 := bstep (se 1 (by rfl) ⟨637415, by rfl⟩ : syracuseStep 849887 = 1274831) B1274831
theorem B849947 : Blo 562809 849947 := bstep (se 1 (by rfl) ⟨637460, by rfl⟩ : syracuseStep 849947 = 1274921) B1274921
theorem B850139 : Blo 562809 850139 := bstep (se 1 (by rfl) ⟨637604, by rfl⟩ : syracuseStep 850139 = 1275209) B1275209
theorem B2029799 : Blo 562809 2029799 := bstep (se 1 (by rfl) ⟨1522349, by rfl⟩ : syracuseStep 2029799 = 3044699) B3044699
theorem B6421031 : Blo 562809 6421031 := bstep (se 1 (by rfl) ⟨4815773, by rfl⟩ : syracuseStep 6421031 = 9631547) B9631547
theorem B2292295 : Blo 562809 2292295 := bstep (se 1 (by rfl) ⟨1719221, by rfl⟩ : syracuseStep 2292295 = 3438443) B3438443
theorem B1604519 : Blo 562809 1604519 := bstep (se 1 (by rfl) ⟨1203389, by rfl⟩ : syracuseStep 1604519 = 2406779) B2406779
theorem B3439759 : Blo 562809 3439759 := bstep (se 1 (by rfl) ⟨2579819, by rfl⟩ : syracuseStep 3439759 = 5159639) B5159639
theorem B10452239 : Blo 562809 10452239 := bstep (se 1 (by rfl) ⟨7839179, by rfl⟩ : syracuseStep 10452239 = 15678359) B15678359
theorem B47021633 : Blo 562809 47021633 := bstep (se 2 (by rfl) ⟨17633112, by rfl⟩ : syracuseStep 47021633 = 35266225) B35266225
theorem B5439275 : Blo 562809 5439275 := bstep (se 1 (by rfl) ⟨4079456, by rfl⟩ : syracuseStep 5439275 = 8158913) B8158913
theorem B950447 : Blo 562809 950447 := bstep (se 1 (by rfl) ⟨712835, by rfl⟩ : syracuseStep 950447 = 1425671) B1425671
theorem B5439737 : Blo 562809 5439737 := bstep (se 2 (by rfl) ⟨2039901, by rfl⟩ : syracuseStep 5439737 = 4079803) B4079803
theorem B4456787 : Blo 562809 4456787 := bstep (se 1 (by rfl) ⟨3342590, by rfl⟩ : syracuseStep 4456787 = 6685181) B6685181
theorem B2032219 : Blo 562809 2032219 := bstep (se 1 (by rfl) ⟨1524164, by rfl⟩ : syracuseStep 2032219 = 3048329) B3048329
theorem B3867983 : Blo 562809 3867983 := bstep (se 1 (by rfl) ⟨2900987, by rfl⟩ : syracuseStep 3867983 = 5801975) B5801975
theorem B951655 : Blo 562809 951655 := bstep (se 1 (by rfl) ⟨713741, by rfl⟩ : syracuseStep 951655 = 1427483) B1427483
theorem B1017299 : Blo 562809 1017299 := bstep (se 1 (by rfl) ⟨762974, by rfl⟩ : syracuseStep 1017299 = 1525949) B1525949
theorem B952391 : Blo 562809 952391 := bstep (se 1 (by rfl) ⟨714293, by rfl⟩ : syracuseStep 952391 = 1428587) B1428587
theorem B952823 : Blo 562809 952823 := bstep (se 1 (by rfl) ⟨714617, by rfl⟩ : syracuseStep 952823 = 1429235) B1429235
theorem B4950575 : Blo 562809 4950575 := bstep (se 1 (by rfl) ⟨3712931, by rfl⟩ : syracuseStep 4950575 = 7425863) B7425863
theorem B1903229 : Blo 562809 1903229 := bstep (se 3 (by rfl) ⟨356855, by rfl⟩ : syracuseStep 1903229 = 713711) B713711
theorem B1903337 : Blo 562809 1903337 := bstep (se 2 (by rfl) ⟨713751, by rfl⟩ : syracuseStep 1903337 = 1427503) B1427503
theorem B1903391 : Blo 562809 1903391 := bstep (se 1 (by rfl) ⟨1427543, by rfl⟩ : syracuseStep 1903391 = 2855087) B2855087
theorem B3050405 : Blo 562809 3050405 := bstep (se 4 (by rfl) ⟨285975, by rfl⟩ : syracuseStep 3050405 = 571951) B571951
theorem B954139 : Blo 562809 954139 := bstep (se 1 (by rfl) ⟨715604, by rfl⟩ : syracuseStep 954139 = 1431209) B1431209
theorem B954551 : Blo 562809 954551 := bstep (se 1 (by rfl) ⟨715913, by rfl⟩ : syracuseStep 954551 = 1431827) B1431827
theorem B1904903 : Blo 562809 1904903 := bstep (se 1 (by rfl) ⟨1428677, by rfl⟩ : syracuseStep 1904903 = 2857355) B2857355
theorem B11604343 : Blo 562809 11604343 := bstep (se 1 (by rfl) ⟨8703257, by rfl⟩ : syracuseStep 11604343 = 17406515) B17406515
theorem B4821515 : Blo 562809 4821515 := bstep (se 1 (by rfl) ⟨3616136, by rfl⟩ : syracuseStep 4821515 = 7232273) B7232273
theorem B955111 : Blo 562809 955111 := bstep (se 1 (by rfl) ⟨716333, by rfl⟩ : syracuseStep 955111 = 1432667) B1432667
theorem B1610543 : Blo 562809 1610543 := bstep (se 1 (by rfl) ⟨1207907, by rfl⟩ : syracuseStep 1610543 = 2415815) B2415815
theorem B2856059 : Blo 562809 2856059 := bstep (se 1 (by rfl) ⟨2142044, by rfl⟩ : syracuseStep 2856059 = 4284089) B4284089
theorem B1905929 : Blo 562809 1905929 := bstep (se 2 (by rfl) ⟨714723, by rfl⟩ : syracuseStep 1905929 = 1429447) B1429447
theorem B1905983 : Blo 562809 1905983 := bstep (se 1 (by rfl) ⟨1429487, by rfl⟩ : syracuseStep 1905983 = 2858975) B2858975
theorem B956009 : Blo 562809 956009 := bstep (se 2 (by rfl) ⟨358503, by rfl⟩ : syracuseStep 956009 = 717007) B717007
theorem B562895 : Blo 562809 562895 := bstep (se 1 (by rfl) ⟨422171, by rfl⟩ : syracuseStep 562895 = 844343) B844343
theorem B3217259 : Blo 562809 3217259 := bstep (se 1 (by rfl) ⟨2412944, by rfl⟩ : syracuseStep 3217259 = 4825889) B4825889
theorem B563135 : Blo 562809 563135 := bstep (se 1 (by rfl) ⟨422351, by rfl⟩ : syracuseStep 563135 = 844703) B844703
theorem B563327 : Blo 562809 563327 := bstep (se 1 (by rfl) ⟨422495, by rfl⟩ : syracuseStep 563327 = 844991) B844991
theorem B563423 : Blo 562809 563423 := bstep (se 1 (by rfl) ⟨422567, by rfl⟩ : syracuseStep 563423 = 845135) B845135
theorem B563483 : Blo 562809 563483 := bstep (se 1 (by rfl) ⟨422612, by rfl⟩ : syracuseStep 563483 = 845225) B845225
theorem B9640295 : Blo 562809 9640295 := bstep (se 1 (by rfl) ⟨7230221, by rfl⟩ : syracuseStep 9640295 = 14460443) B14460443
theorem B563583 : Blo 562809 563583 := bstep (se 1 (by rfl) ⟨422687, by rfl⟩ : syracuseStep 563583 = 845375) B845375
theorem B563823 : Blo 562809 563823 := bstep (se 1 (by rfl) ⟨422867, by rfl⟩ : syracuseStep 563823 = 845735) B845735
theorem B5151385 : Blo 562809 5151385 := bstep (se 2 (by rfl) ⟨1931769, by rfl⟩ : syracuseStep 5151385 = 3863539) B3863539
theorem B563903 : Blo 562809 563903 := bstep (se 1 (by rfl) ⟨422927, by rfl⟩ : syracuseStep 563903 = 845855) B845855
theorem B1219369 : Blo 562809 1219369 := bstep (se 2 (by rfl) ⟨457263, by rfl⟩ : syracuseStep 1219369 = 914527) B914527
theorem B564207 : Blo 562809 564207 := bstep (se 1 (by rfl) ⟨423155, by rfl⟩ : syracuseStep 564207 = 846311) B846311
theorem B564327 : Blo 562809 564327 := bstep (se 1 (by rfl) ⟨423245, by rfl⟩ : syracuseStep 564327 = 846491) B846491
theorem B564475 : Blo 562809 564475 := bstep (se 1 (by rfl) ⟨423356, by rfl⟩ : syracuseStep 564475 = 846713) B846713
theorem B564639 : Blo 562809 564639 := bstep (se 1 (by rfl) ⟨423479, by rfl⟩ : syracuseStep 564639 = 846959) B846959
theorem B564703 : Blo 562809 564703 := bstep (se 1 (by rfl) ⟨423527, by rfl⟩ : syracuseStep 564703 = 847055) B847055
theorem B564783 : Blo 562809 564783 := bstep (se 1 (by rfl) ⟨423587, by rfl⟩ : syracuseStep 564783 = 847175) B847175
theorem B9182929 : Blo 562809 9182929 := bstep (se 2 (by rfl) ⟨3443598, by rfl⟩ : syracuseStep 9182929 = 6887197) B6887197
theorem B564975 : Blo 562809 564975 := bstep (se 1 (by rfl) ⟨423731, by rfl⟩ : syracuseStep 564975 = 847463) B847463
theorem B3055441 : Blo 562809 3055441 := bstep (se 2 (by rfl) ⟨1145790, by rfl⟩ : syracuseStep 3055441 = 2291581) B2291581
theorem B565231 : Blo 562809 565231 := bstep (se 1 (by rfl) ⟨423923, by rfl⟩ : syracuseStep 565231 = 847847) B847847
theorem B565311 : Blo 562809 565311 := bstep (se 1 (by rfl) ⟨423983, by rfl⟩ : syracuseStep 565311 = 847967) B847967
theorem B565351 : Blo 562809 565351 := bstep (se 1 (by rfl) ⟨424013, by rfl⟩ : syracuseStep 565351 = 848027) B848027
theorem B565471 : Blo 562809 565471 := bstep (se 1 (by rfl) ⟨424103, by rfl⟩ : syracuseStep 565471 = 848207) B848207
theorem B565531 : Blo 562809 565531 := bstep (se 1 (by rfl) ⟨424148, by rfl⟩ : syracuseStep 565531 = 848297) B848297
theorem B4170041 : Blo 562809 4170041 := bstep (se 2 (by rfl) ⟨1563765, by rfl⟩ : syracuseStep 4170041 = 3127531) B3127531
theorem B2040191 : Blo 562809 2040191 := bstep (se 1 (by rfl) ⟨1530143, by rfl⟩ : syracuseStep 2040191 = 3060287) B3060287
theorem B565735 : Blo 562809 565735 := bstep (se 1 (by rfl) ⟨424301, by rfl⟩ : syracuseStep 565735 = 848603) B848603
theorem B565915 : Blo 562809 565915 := bstep (se 1 (by rfl) ⟨424436, by rfl⟩ : syracuseStep 565915 = 848873) B848873
theorem B566011 : Blo 562809 566011 := bstep (se 1 (by rfl) ⟨424508, by rfl⟩ : syracuseStep 566011 = 849017) B849017
theorem B3056393 : Blo 562809 3056393 := bstep (se 2 (by rfl) ⟨1146147, by rfl⟩ : syracuseStep 3056393 = 2292295) B2292295
theorem B18260903 : Blo 562809 18260903 := bstep (se 1 (by rfl) ⟨13695677, by rfl⟩ : syracuseStep 18260903 = 27391355) B27391355
theorem B83731481 : Blo 562809 83731481 := bstep (se 2 (by rfl) ⟨31399305, by rfl⟩ : syracuseStep 83731481 = 62798611) B62798611
theorem B566363 : Blo 562809 566363 := bstep (se 1 (by rfl) ⟨424772, by rfl⟩ : syracuseStep 566363 = 849545) B849545
theorem B566503 : Blo 562809 566503 := bstep (se 1 (by rfl) ⟨424877, by rfl⟩ : syracuseStep 566503 = 849755) B849755
theorem B566527 : Blo 562809 566527 := bstep (se 1 (by rfl) ⟨424895, by rfl⟩ : syracuseStep 566527 = 849791) B849791
theorem B2172167 : Blo 562809 2172167 := bstep (se 1 (by rfl) ⟨1629125, by rfl⟩ : syracuseStep 2172167 = 3258251) B3258251
theorem B566591 : Blo 562809 566591 := bstep (se 1 (by rfl) ⟨424943, by rfl⟩ : syracuseStep 566591 = 849887) B849887
theorem B566631 : Blo 562809 566631 := bstep (se 1 (by rfl) ⟨424973, by rfl⟩ : syracuseStep 566631 = 849947) B849947
theorem B566759 : Blo 562809 566759 := bstep (se 1 (by rfl) ⟨425069, by rfl⟩ : syracuseStep 566759 = 850139) B850139
theorem B1353199 : Blo 562809 1353199 := bstep (se 1 (by rfl) ⟨1014899, by rfl⟩ : syracuseStep 1353199 = 2029799) B2029799
theorem B1910303 : Blo 562809 1910303 := bstep (se 1 (by rfl) ⟨1432727, by rfl⟩ : syracuseStep 1910303 = 2865455) B2865455
theorem B3221815 : Blo 562809 3221815 := bstep (se 1 (by rfl) ⟨2416361, by rfl⟩ : syracuseStep 3221815 = 4832723) B4832723
theorem B3615931 : Blo 562809 3615931 := bstep (se 1 (by rfl) ⟨2711948, by rfl⟩ : syracuseStep 3615931 = 5423897) B5423897
theorem B6532283 : Blo 562809 6532283 := bstep (se 1 (by rfl) ⟨4899212, by rfl⟩ : syracuseStep 6532283 = 9798425) B9798425
theorem B5484185 : Blo 562809 5484185 := bstep (se 2 (by rfl) ⟨2056569, by rfl⟩ : syracuseStep 5484185 = 4113139) B4113139
theorem B1355591 : Blo 562809 1355591 := bstep (se 1 (by rfl) ⟨1016693, by rfl⟩ : syracuseStep 1355591 = 2033387) B2033387
theorem B1912895 : Blo 562809 1912895 := bstep (se 1 (by rfl) ⟨1434671, by rfl⟩ : syracuseStep 1912895 = 2869343) B2869343
theorem B635359 : Blo 562809 635359 := bstep (se 1 (by rfl) ⟨476519, by rfl⟩ : syracuseStep 635359 = 953039) B953039
theorem B4895201 : Blo 562809 4895201 := bstep (se 2 (by rfl) ⟨1835700, by rfl⟩ : syracuseStep 4895201 = 3671401) B3671401
theorem B635503 : Blo 562809 635503 := bstep (se 1 (by rfl) ⟨476627, by rfl⟩ : syracuseStep 635503 = 953255) B953255
theorem B635611 : Blo 562809 635611 := bstep (se 1 (by rfl) ⟨476708, by rfl⟩ : syracuseStep 635611 = 953417) B953417
theorem B2143367 : Blo 562809 2143367 := bstep (se 1 (by rfl) ⟨1607525, by rfl⟩ : syracuseStep 2143367 = 3215051) B3215051
theorem B7222841 : Blo 562809 7222841 := bstep (se 2 (by rfl) ⟨2708565, by rfl⟩ : syracuseStep 7222841 = 5417131) B5417131
theorem B2864807 : Blo 562809 2864807 := bstep (se 1 (by rfl) ⟨2148605, by rfl⟩ : syracuseStep 2864807 = 4297211) B4297211
theorem B8664893 : Blo 562809 8664893 := bstep (se 3 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 8664893 = 3249335) B3249335
theorem B6109111 : Blo 562809 6109111 := bstep (se 1 (by rfl) ⟨4581833, by rfl⟩ : syracuseStep 6109111 = 9163667) B9163667
theorem B2406419 : Blo 562809 2406419 := bstep (se 1 (by rfl) ⟨1804814, by rfl⟩ : syracuseStep 2406419 = 3609629) B3609629
theorem B4274369 : Blo 562809 4274369 := bstep (se 2 (by rfl) ⟨1602888, by rfl⟩ : syracuseStep 4274369 = 3205777) B3205777
theorem B2407103 : Blo 562809 2407103 := bstep (se 1 (by rfl) ⟨1805327, by rfl⟩ : syracuseStep 2407103 = 3610655) B3610655
theorem B6109931 : Blo 562809 6109931 := bstep (se 1 (by rfl) ⟨4582448, by rfl⟩ : syracuseStep 6109931 = 9164897) B9164897
theorem B2146297 : Blo 562809 2146297 := bstep (se 2 (by rfl) ⟨804861, by rfl⟩ : syracuseStep 2146297 = 1609723) B1609723
theorem B565985303 : Blo 562809 565985303 := bstep (se 1 (by rfl) ⟨424488977, by rfl⟩ : syracuseStep 565985303 = 848977955) B848977955
theorem B12206537 : Blo 562809 12206537 := bstep (se 2 (by rfl) ⟨4577451, by rfl⟩ : syracuseStep 12206537 = 9154903) B9154903
theorem B2146783 : Blo 562809 2146783 := bstep (se 1 (by rfl) ⟨1610087, by rfl⟩ : syracuseStep 2146783 = 3220175) B3220175
theorem B1360763 : Blo 562809 1360763 := bstep (se 1 (by rfl) ⟨1020572, by rfl⟩ : syracuseStep 1360763 = 2041145) B2041145
theorem B2148059 : Blo 562809 2148059 := bstep (se 1 (by rfl) ⟨1611044, by rfl⟩ : syracuseStep 2148059 = 3222089) B3222089
theorem B19613495 : Blo 562809 19613495 := bstep (se 1 (by rfl) ⟨14710121, by rfl⟩ : syracuseStep 19613495 = 29420243) B29420243
theorem B5590075 : Blo 562809 5590075 := bstep (se 1 (by rfl) ⟨4192556, by rfl⟩ : syracuseStep 5590075 = 8385113) B8385113
theorem B1526855 : Blo 562809 1526855 := bstep (se 1 (by rfl) ⟨1145141, by rfl⟩ : syracuseStep 1526855 = 2290283) B2290283
theorem B2149487 : Blo 562809 2149487 := bstep (se 1 (by rfl) ⟨1612115, by rfl⟩ : syracuseStep 2149487 = 3224231) B3224231
theorem B1069033 : Blo 562809 1069033 := bstep (se 2 (by rfl) ⟨400887, by rfl⟩ : syracuseStep 1069033 = 801775) B801775
theorem B4280687 : Blo 562809 4280687 := bstep (se 1 (by rfl) ⟨3210515, by rfl⟩ : syracuseStep 4280687 = 6421031) B6421031
theorem B1069679 : Blo 562809 1069679 := bstep (se 1 (by rfl) ⟨802259, by rfl⟩ : syracuseStep 1069679 = 1604519) B1604519
theorem B6968159 : Blo 562809 6968159 := bstep (se 1 (by rfl) ⟨5226119, by rfl⟩ : syracuseStep 6968159 = 10452239) B10452239
theorem B31347755 : Blo 562809 31347755 := bstep (se 1 (by rfl) ⟨23510816, by rfl⟩ : syracuseStep 31347755 = 47021633) B47021633
theorem B1627303 : Blo 562809 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B3626183 : Blo 562809 3626183 := bstep (se 1 (by rfl) ⟨2719637, by rfl⟩ : syracuseStep 3626183 = 5439275) B5439275
theorem B2741471 : Blo 562809 2741471 := bstep (se 1 (by rfl) ⟨2056103, by rfl⟩ : syracuseStep 2741471 = 4112207) B4112207
theorem B1267199 : Blo 562809 1267199 := bstep (se 1 (by rfl) ⟨950399, by rfl⟩ : syracuseStep 1267199 = 1900799) B1900799
theorem B3659347 : Blo 562809 3659347 := bstep (se 1 (by rfl) ⟨2744510, by rfl⟩ : syracuseStep 3659347 = 5489021) B5489021
theorem B2316671 : Blo 562809 2316671 := bstep (se 1 (by rfl) ⟨1737503, by rfl⟩ : syracuseStep 2316671 = 3475007) B3475007
theorem B16243091 : Blo 562809 16243091 := bstep (se 1 (by rfl) ⟨12182318, by rfl⟩ : syracuseStep 16243091 = 24364637) B24364637
theorem B2710259 : Blo 562809 2710259 := bstep (se 1 (by rfl) ⟨2032694, by rfl⟩ : syracuseStep 2710259 = 4065389) B4065389
theorem B2415527 : Blo 562809 2415527 := bstep (se 1 (by rfl) ⟨1811645, by rfl⟩ : syracuseStep 2415527 = 3623291) B3623291
theorem B1268729 : Blo 562809 1268729 := bstep (se 2 (by rfl) ⟨475773, by rfl⟩ : syracuseStep 1268729 = 951547) B951547
theorem B1203295 : Blo 562809 1203295 := bstep (se 1 (by rfl) ⟨902471, by rfl⟩ : syracuseStep 1203295 = 1804943) B1804943
theorem B4283603 : Blo 562809 4283603 := bstep (se 1 (by rfl) ⟨3212702, by rfl⟩ : syracuseStep 4283603 = 6425405) B6425405
theorem B4349663 : Blo 562809 4349663 := bstep (se 1 (by rfl) ⟨3262247, by rfl⟩ : syracuseStep 4349663 = 6524495) B6524495
theorem B7233299 : Blo 562809 7233299 := bstep (se 1 (by rfl) ⟨5424974, by rfl⟩ : syracuseStep 7233299 = 10849949) B10849949
theorem B1269647 : Blo 562809 1269647 := bstep (se 1 (by rfl) ⟨952235, by rfl⟩ : syracuseStep 1269647 = 1904471) B1904471
theorem B2285549 : Blo 562809 2285549 := bstep (se 3 (by rfl) ⟨428540, by rfl⟩ : syracuseStep 2285549 = 857081) B857081
theorem B1269755 : Blo 562809 1269755 := bstep (se 1 (by rfl) ⟨952316, by rfl⟩ : syracuseStep 1269755 = 1904633) B1904633
theorem B1433983 : Blo 562809 1433983 := bstep (se 1 (by rfl) ⟨1075487, by rfl⟩ : syracuseStep 1433983 = 2150975) B2150975
theorem B1434095 : Blo 562809 1434095 := bstep (se 1 (by rfl) ⟨1075571, by rfl⟩ : syracuseStep 1434095 = 2151143) B2151143
theorem B1270367 : Blo 562809 1270367 := bstep (se 1 (by rfl) ⟨952775, by rfl⟩ : syracuseStep 1270367 = 1905551) B1905551
theorem B844607 : Blo 562809 844607 := bstep (se 1 (by rfl) ⟨633455, by rfl⟩ : syracuseStep 844607 = 1266911) B1266911
theorem B1270727 : Blo 562809 1270727 := bstep (se 1 (by rfl) ⟨953045, by rfl⟩ : syracuseStep 1270727 = 1906091) B1906091
theorem B11035705 : Blo 562809 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B844895 : Blo 562809 844895 := bstep (se 1 (by rfl) ⟨633671, by rfl⟩ : syracuseStep 844895 = 1267343) B1267343
theorem B844955 : Blo 562809 844955 := bstep (se 1 (by rfl) ⟨633716, by rfl⟩ : syracuseStep 844955 = 1267433) B1267433
theorem B1271087 : Blo 562809 1271087 := bstep (se 1 (by rfl) ⟨953315, by rfl⟩ : syracuseStep 1271087 = 1906631) B1906631
theorem B846047 : Blo 562809 846047 := bstep (se 1 (by rfl) ⟨634535, by rfl⟩ : syracuseStep 846047 = 1269071) B1269071
theorem B715007 : Blo 562809 715007 := bstep (se 1 (by rfl) ⟨536255, by rfl⟩ : syracuseStep 715007 = 1072511) B1072511
theorem B2418943 : Blo 562809 2418943 := bstep (se 1 (by rfl) ⟨1814207, by rfl⟩ : syracuseStep 2418943 = 3628415) B3628415
theorem B846107 : Blo 562809 846107 := bstep (se 1 (by rfl) ⟨634580, by rfl⟩ : syracuseStep 846107 = 1269161) B1269161
theorem B6187691 : Blo 562809 6187691 := bstep (se 1 (by rfl) ⟨4640768, by rfl⟩ : syracuseStep 6187691 = 9281537) B9281537
theorem B1272743 : Blo 562809 1272743 := bstep (se 1 (by rfl) ⟨954557, by rfl⟩ : syracuseStep 1272743 = 1909115) B1909115
theorem B2420225 : Blo 562809 2420225 := bstep (se 2 (by rfl) ⟨907584, by rfl⟩ : syracuseStep 2420225 = 1815169) B1815169
theorem B1633895 : Blo 562809 1633895 := bstep (se 1 (by rfl) ⟨1225421, by rfl⟩ : syracuseStep 1633895 = 2450843) B2450843
theorem B6418115 : Blo 562809 6418115 := bstep (se 1 (by rfl) ⟨4813586, by rfl⟩ : syracuseStep 6418115 = 9627173) B9627173
theorem B847583 : Blo 562809 847583 := bstep (se 1 (by rfl) ⟨635687, by rfl⟩ : syracuseStep 847583 = 1271375) B1271375
theorem B848063 : Blo 562809 848063 := bstep (se 1 (by rfl) ⟨636047, by rfl⟩ : syracuseStep 848063 = 1272095) B1272095
theorem B651487 : Blo 562809 651487 := bstep (se 1 (by rfl) ⟨488615, by rfl⟩ : syracuseStep 651487 = 977231) B977231
theorem B1274111 : Blo 562809 1274111 := bstep (se 1 (by rfl) ⟨955583, by rfl⟩ : syracuseStep 1274111 = 1911167) B1911167
theorem B5042639 : Blo 562809 5042639 := bstep (se 1 (by rfl) ⟨3781979, by rfl⟩ : syracuseStep 5042639 = 7563959) B7563959
theorem B848411 : Blo 562809 848411 := bstep (se 1 (by rfl) ⟨636308, by rfl⟩ : syracuseStep 848411 = 1272617) B1272617
theorem B6615751 : Blo 562809 6615751 := bstep (se 1 (by rfl) ⟨4961813, by rfl⟩ : syracuseStep 6615751 = 9923627) B9923627
theorem B848591 : Blo 562809 848591 := bstep (se 1 (by rfl) ⟨636443, by rfl⟩ : syracuseStep 848591 = 1272887) B1272887
theorem B1864475 : Blo 562809 1864475 := bstep (se 1 (by rfl) ⟨1398356, by rfl⟩ : syracuseStep 1864475 = 2796713) B2796713
theorem B848711 : Blo 562809 848711 := bstep (se 1 (by rfl) ⟨636533, by rfl⟩ : syracuseStep 848711 = 1273067) B1273067
theorem B1275047 : Blo 562809 1275047 := bstep (se 1 (by rfl) ⟨956285, by rfl⟩ : syracuseStep 1275047 = 1912571) B1912571
theorem B849263 : Blo 562809 849263 := bstep (se 1 (by rfl) ⟨636947, by rfl⟩ : syracuseStep 849263 = 1273895) B1273895
theorem B849383 : Blo 562809 849383 := bstep (se 1 (by rfl) ⟨637037, by rfl⟩ : syracuseStep 849383 = 1274075) B1274075
theorem B849455 : Blo 562809 849455 := bstep (se 1 (by rfl) ⟨637091, by rfl⟩ : syracuseStep 849455 = 1274183) B1274183
theorem B849563 : Blo 562809 849563 := bstep (se 1 (by rfl) ⟨637172, by rfl⟩ : syracuseStep 849563 = 1274345) B1274345
theorem B849983 : Blo 562809 849983 := bstep (se 1 (by rfl) ⟨637487, by rfl⟩ : syracuseStep 849983 = 1274975) B1274975
theorem B1603709 : Blo 562809 1603709 := bstep (se 3 (by rfl) ⟨300695, by rfl⟩ : syracuseStep 1603709 = 601391) B601391
theorem B1604063 : Blo 562809 1604063 := bstep (se 1 (by rfl) ⟨1203047, by rfl⟩ : syracuseStep 1604063 = 2406095) B2406095
theorem B4586345 : Blo 562809 4586345 := bstep (se 2 (by rfl) ⟨1719879, by rfl⟩ : syracuseStep 4586345 = 3439759) B3439759
theorem B949927 : Blo 562809 949927 := bstep (se 1 (by rfl) ⟨712445, by rfl⟩ : syracuseStep 949927 = 1424891) B1424891
theorem B1900313 : Blo 562809 1900313 := bstep (se 2 (by rfl) ⟨712617, by rfl⟩ : syracuseStep 1900313 = 1425235) B1425235
theorem B377323535 : Blo 562809 377323535 := bstep (se 1 (by rfl) ⟨282992651, by rfl⟩ : syracuseStep 377323535 = 565985303) B565985303
theorem B16286453 : Blo 562809 16286453 := bstep (se 5 (by rfl) ⟨763427, by rfl⟩ : syracuseStep 16286453 = 1526855) B1526855
theorem B13075663 : Blo 562809 13075663 := bstep (se 1 (by rfl) ⟨9806747, by rfl⟩ : syracuseStep 13075663 = 19613495) B19613495
theorem B14714273 : Blo 562809 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B2033603 : Blo 562809 2033603 := bstep (se 1 (by rfl) ⟨1525202, by rfl⟩ : syracuseStep 2033603 = 3050405) B3050405
theorem B1804265 : Blo 562809 1804265 := bstep (se 2 (by rfl) ⟨676599, by rfl⟩ : syracuseStep 1804265 = 1353199) B1353199
theorem B4294781 : Blo 562809 4294781 := bstep (se 3 (by rfl) ⟨805271, by rfl⟩ : syracuseStep 4294781 = 1610543) B1610543
theorem B2853791 : Blo 562809 2853791 := bstep (se 1 (by rfl) ⟨2140343, by rfl⟩ : syracuseStep 2853791 = 4280687) B4280687
theorem B3214343 : Blo 562809 3214343 := bstep (se 1 (by rfl) ⟨2410757, by rfl⟩ : syracuseStep 3214343 = 4821515) B4821515
theorem B4295753 : Blo 562809 4295753 := bstep (se 2 (by rfl) ⟨1610907, by rfl⟩ : syracuseStep 4295753 = 3221815) B3221815
theorem B1904039 : Blo 562809 1904039 := bstep (se 1 (by rfl) ⟨1428029, by rfl⟩ : syracuseStep 1904039 = 2856059) B2856059
theorem B6426863 : Blo 562809 6426863 := bstep (se 1 (by rfl) ⟨4820147, by rfl⟩ : syracuseStep 6426863 = 9640295) B9640295
theorem B4821241 : Blo 562809 4821241 := bstep (se 2 (by rfl) ⟨1807965, by rfl⟩ : syracuseStep 4821241 = 3615931) B3615931
theorem B1544447 : Blo 562809 1544447 := bstep (se 1 (by rfl) ⟨1158335, by rfl⟩ : syracuseStep 1544447 = 2316671) B2316671
theorem B1806839 : Blo 562809 1806839 := bstep (se 1 (by rfl) ⟨1355129, by rfl⟩ : syracuseStep 1806839 = 2710259) B2710259
theorem B1610351 : Blo 562809 1610351 := bstep (se 1 (by rfl) ⟨1207763, by rfl⟩ : syracuseStep 1610351 = 2415527) B2415527
theorem B2855735 : Blo 562809 2855735 := bstep (se 1 (by rfl) ⟨2141801, by rfl⟩ : syracuseStep 2855735 = 4283603) B4283603
theorem B4822199 : Blo 562809 4822199 := bstep (se 1 (by rfl) ⟨3616649, by rfl⟩ : syracuseStep 4822199 = 7233299) B7233299
theorem B956063 : Blo 562809 956063 := bstep (se 1 (by rfl) ⟨717047, by rfl⟩ : syracuseStep 956063 = 1434095) B1434095
theorem B15472457 : Blo 562809 15472457 := bstep (se 2 (by rfl) ⟨5802171, by rfl⟩ : syracuseStep 15472457 = 11604343) B11604343
theorem B563071 : Blo 562809 563071 := bstep (se 1 (by rfl) ⟨422303, by rfl⟩ : syracuseStep 563071 = 844607) B844607
theorem B1906685 : Blo 562809 1906685 := bstep (se 3 (by rfl) ⟨357503, by rfl⟩ : syracuseStep 1906685 = 715007) B715007
theorem B563263 : Blo 562809 563263 := bstep (se 1 (by rfl) ⟨422447, by rfl⟩ : syracuseStep 563263 = 844895) B844895
theorem B563303 : Blo 562809 563303 := bstep (se 1 (by rfl) ⟨422477, by rfl⟩ : syracuseStep 563303 = 844955) B844955
theorem B1448111 : Blo 562809 1448111 := bstep (se 1 (by rfl) ⟨1086083, by rfl⟩ : syracuseStep 1448111 = 2172167) B2172167
theorem B8821001 : Blo 562809 8821001 := bstep (se 2 (by rfl) ⟨3307875, by rfl⟩ : syracuseStep 8821001 = 6615751) B6615751
theorem B564031 : Blo 562809 564031 := bstep (se 1 (by rfl) ⟨423023, by rfl⟩ : syracuseStep 564031 = 846047) B846047
theorem B564071 : Blo 562809 564071 := bstep (se 1 (by rfl) ⟨423053, by rfl⟩ : syracuseStep 564071 = 846107) B846107
theorem B2169737 : Blo 562809 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B16293149 : Blo 562809 16293149 := bstep (se 3 (by rfl) ⟨3054965, by rfl⟩ : syracuseStep 16293149 = 6109931) B6109931
theorem B1613483 : Blo 562809 1613483 := bstep (se 1 (by rfl) ⟨1210112, by rfl⟩ : syracuseStep 1613483 = 2420225) B2420225
theorem B1089263 : Blo 562809 1089263 := bstep (se 1 (by rfl) ⟨816947, by rfl⟩ : syracuseStep 1089263 = 1633895) B1633895
theorem B565055 : Blo 562809 565055 := bstep (se 1 (by rfl) ⟨423791, by rfl⟩ : syracuseStep 565055 = 847583) B847583
theorem B565375 : Blo 562809 565375 := bstep (se 1 (by rfl) ⟨424031, by rfl⟩ : syracuseStep 565375 = 848063) B848063
theorem B565607 : Blo 562809 565607 := bstep (se 1 (by rfl) ⟨424205, by rfl⟩ : syracuseStep 565607 = 848411) B848411
theorem B565727 : Blo 562809 565727 := bstep (se 1 (by rfl) ⟨424295, by rfl⟩ : syracuseStep 565727 = 848591) B848591
theorem B565807 : Blo 562809 565807 := bstep (se 1 (by rfl) ⟨424355, by rfl⟩ : syracuseStep 565807 = 848711) B848711
theorem B566175 : Blo 562809 566175 := bstep (se 1 (by rfl) ⟨424631, by rfl⟩ : syracuseStep 566175 = 849263) B849263
theorem B566255 : Blo 562809 566255 := bstep (se 1 (by rfl) ⟨424691, by rfl⟩ : syracuseStep 566255 = 849383) B849383
theorem B566303 : Blo 562809 566303 := bstep (se 1 (by rfl) ⟨424727, by rfl⟩ : syracuseStep 566303 = 849455) B849455
theorem B566375 : Blo 562809 566375 := bstep (se 1 (by rfl) ⟨424781, by rfl⟩ : syracuseStep 566375 = 849563) B849563
theorem B1909871 : Blo 562809 1909871 := bstep (se 1 (by rfl) ⟨1432403, by rfl⟩ : syracuseStep 1909871 = 2864807) B2864807
theorem B5776595 : Blo 562809 5776595 := bstep (se 1 (by rfl) ⟨4332446, by rfl⟩ : syracuseStep 5776595 = 8664893) B8664893
theorem B566655 : Blo 562809 566655 := bstep (se 1 (by rfl) ⟨424991, by rfl⟩ : syracuseStep 566655 = 849983) B849983
theorem B3057563 : Blo 562809 3057563 := bstep (se 1 (by rfl) ⟨2293172, by rfl⟩ : syracuseStep 3057563 = 4586345) B4586345
theorem B4073921 : Blo 562809 4073921 := bstep (se 2 (by rfl) ⟨1527720, by rfl⟩ : syracuseStep 4073921 = 3055441) B3055441
theorem B2861729 : Blo 562809 2861729 := bstep (se 2 (by rfl) ⟨1073148, by rfl⟩ : syracuseStep 2861729 = 2146297) B2146297
theorem B633631 : Blo 562809 633631 := bstep (se 1 (by rfl) ⟨475223, by rfl⟩ : syracuseStep 633631 = 950447) B950447
theorem B8137691 : Blo 562809 8137691 := bstep (se 1 (by rfl) ⟨6103268, by rfl⟩ : syracuseStep 8137691 = 12206537) B12206537
theorem B1911977 : Blo 562809 1911977 := bstep (se 2 (by rfl) ⟨716991, by rfl⟩ : syracuseStep 1911977 = 1433983) B1433983
theorem B2862377 : Blo 562809 2862377 := bstep (se 2 (by rfl) ⟨1073391, by rfl⟩ : syracuseStep 2862377 = 2146783) B2146783
theorem B13447037 : Blo 562809 13447037 := bstep (se 3 (by rfl) ⟨2521319, by rfl⟩ : syracuseStep 13447037 = 5042639) B5042639
theorem B13053869 : Blo 562809 13053869 := bstep (se 3 (by rfl) ⟨2447600, by rfl⟩ : syracuseStep 13053869 = 4895201) B4895201
theorem B634927 : Blo 562809 634927 := bstep (se 1 (by rfl) ⟨476195, by rfl⟩ : syracuseStep 634927 = 952391) B952391
theorem B635215 : Blo 562809 635215 := bstep (se 1 (by rfl) ⟨476411, by rfl⟩ : syracuseStep 635215 = 952823) B952823
theorem B636367 : Blo 562809 636367 := bstep (se 1 (by rfl) ⟨477275, by rfl⟩ : syracuseStep 636367 = 954551) B954551
theorem B3225257 : Blo 562809 3225257 := bstep (se 2 (by rfl) ⟨1209471, by rfl⟩ : syracuseStep 3225257 = 2418943) B2418943
theorem B637339 : Blo 562809 637339 := bstep (se 1 (by rfl) ⟨478004, by rfl⟩ : syracuseStep 637339 = 956009) B956009
theorem B2144839 : Blo 562809 2144839 := bstep (se 1 (by rfl) ⟨1608629, by rfl⟩ : syracuseStep 2144839 = 3217259) B3217259
theorem B7453433 : Blo 562809 7453433 := bstep (se 2 (by rfl) ⟨2795037, by rfl⟩ : syracuseStep 7453433 = 5590075) B5590075
theorem B10828727 : Blo 562809 10828727 := bstep (se 1 (by rfl) ⟨8121545, by rfl⟩ : syracuseStep 10828727 = 16243091) B16243091
theorem B2899775 : Blo 562809 2899775 := bstep (se 1 (by rfl) ⟨2174831, by rfl⟩ : syracuseStep 2899775 = 4349663) B4349663
theorem B1425377 : Blo 562809 1425377 := bstep (se 2 (by rfl) ⟨534516, by rfl⟩ : syracuseStep 1425377 = 1069033) B1069033
theorem B1523699 : Blo 562809 1523699 := bstep (se 1 (by rfl) ⟨1142774, by rfl⟩ : syracuseStep 1523699 = 2285549) B2285549
theorem B1360127 : Blo 562809 1360127 := bstep (se 1 (by rfl) ⟨1020095, by rfl⟩ : syracuseStep 1360127 = 2040191) B2040191
theorem B868649 : Blo 562809 868649 := bstep (se 2 (by rfl) ⟨325743, by rfl⟩ : syracuseStep 868649 = 651487) B651487
theorem B12173935 : Blo 562809 12173935 := bstep (se 1 (by rfl) ⟨9130451, by rfl⟩ : syracuseStep 12173935 = 18260903) B18260903
theorem B55820987 : Blo 562809 55820987 := bstep (se 1 (by rfl) ⟨41865740, by rfl⟩ : syracuseStep 55820987 = 83731481) B83731481
theorem B3656123 : Blo 562809 3656123 := bstep (se 1 (by rfl) ⟨2742092, by rfl⟩ : syracuseStep 3656123 = 5484185) B5484185
theorem B4278743 : Blo 562809 4278743 := bstep (se 1 (by rfl) ⟨3209057, by rfl⟩ : syracuseStep 4278743 = 6418115) B6418115
theorem B903727 : Blo 562809 903727 := bstep (se 1 (by rfl) ⟨677795, by rfl⟩ : syracuseStep 903727 = 1355591) B1355591
theorem B8145481 : Blo 562809 8145481 := bstep (se 2 (by rfl) ⟨3054555, by rfl⟩ : syracuseStep 8145481 = 6109111) B6109111
theorem B17419421 : Blo 562809 17419421 := bstep (se 3 (by rfl) ⟨3266141, by rfl⟩ : syracuseStep 17419421 = 6532283) B6532283
theorem B1428911 : Blo 562809 1428911 := bstep (se 1 (by rfl) ⟨1071683, by rfl⟩ : syracuseStep 1428911 = 2143367) B2143367
theorem B6868513 : Blo 562809 6868513 := bstep (se 2 (by rfl) ⟨2575692, by rfl⟩ : syracuseStep 6868513 = 5151385) B5151385
theorem B1625825 : Blo 562809 1625825 := bstep (se 2 (by rfl) ⟨609684, by rfl⟩ : syracuseStep 1625825 = 1219369) B1219369
theorem B1069139 : Blo 562809 1069139 := bstep (se 1 (by rfl) ⟨801854, by rfl⟩ : syracuseStep 1069139 = 1603709) B1603709
theorem B1069375 : Blo 562809 1069375 := bstep (se 1 (by rfl) ⟨802031, by rfl⟩ : syracuseStep 1069375 = 1604063) B1604063
theorem B1266569 : Blo 562809 1266569 := bstep (se 2 (by rfl) ⟨474963, by rfl⟩ : syracuseStep 1266569 = 949927) B949927
theorem B12243905 : Blo 562809 12243905 := bstep (se 2 (by rfl) ⟨4591464, by rfl⟩ : syracuseStep 12243905 = 9182929) B9182929
theorem B1266875 : Blo 562809 1266875 := bstep (se 1 (by rfl) ⟨950156, by rfl⟩ : syracuseStep 1266875 = 1900313) B1900313
theorem B3626491 : Blo 562809 3626491 := bstep (se 1 (by rfl) ⟨2719868, by rfl⟩ : syracuseStep 3626491 = 5439737) B5439737
theorem B907175 : Blo 562809 907175 := bstep (se 1 (by rfl) ⟨680381, by rfl⟩ : syracuseStep 907175 = 1360763) B1360763
theorem B2709625 : Blo 562809 2709625 := bstep (se 2 (by rfl) ⟨1016109, by rfl⟩ : syracuseStep 2709625 = 2032219) B2032219
theorem B2578655 : Blo 562809 2578655 := bstep (se 1 (by rfl) ⟨1933991, by rfl⟩ : syracuseStep 2578655 = 3867983) B3867983
theorem B1432039 : Blo 562809 1432039 := bstep (se 1 (by rfl) ⟨1074029, by rfl⟩ : syracuseStep 1432039 = 2148059) B2148059
theorem B3300383 : Blo 562809 3300383 := bstep (se 1 (by rfl) ⟨2475287, by rfl⟩ : syracuseStep 3300383 = 4950575) B4950575
theorem B1268819 : Blo 562809 1268819 := bstep (se 1 (by rfl) ⟨951614, by rfl⟩ : syracuseStep 1268819 = 1903229) B1903229
theorem B1268873 : Blo 562809 1268873 := bstep (se 2 (by rfl) ⟨475827, by rfl⟩ : syracuseStep 1268873 = 951655) B951655
theorem B1268891 : Blo 562809 1268891 := bstep (se 1 (by rfl) ⟨951668, by rfl⟩ : syracuseStep 1268891 = 1903337) B1903337
theorem B1268927 : Blo 562809 1268927 := bstep (se 1 (by rfl) ⟨951695, by rfl⟩ : syracuseStep 1268927 = 1903391) B1903391
theorem B8150381 : Blo 562809 8150381 := bstep (se 3 (by rfl) ⟨1528196, by rfl⟩ : syracuseStep 8150381 = 3056393) B3056393
theorem B1432991 : Blo 562809 1432991 := bstep (se 1 (by rfl) ⟨1074743, by rfl⟩ : syracuseStep 1432991 = 2149487) B2149487
theorem B1269935 : Blo 562809 1269935 := bstep (se 1 (by rfl) ⟨952451, by rfl⟩ : syracuseStep 1269935 = 1904903) B1904903
theorem B713119 : Blo 562809 713119 := bstep (se 1 (by rfl) ⟨534839, by rfl⟩ : syracuseStep 713119 = 1069679) B1069679
theorem B4645439 : Blo 562809 4645439 := bstep (se 1 (by rfl) ⟨3484079, by rfl⟩ : syracuseStep 4645439 = 6968159) B6968159
theorem B20898503 : Blo 562809 20898503 := bstep (se 1 (by rfl) ⟨15673877, by rfl⟩ : syracuseStep 20898503 = 31347755) B31347755
theorem B2417455 : Blo 562809 2417455 := bstep (se 1 (by rfl) ⟨1813091, by rfl⟩ : syracuseStep 2417455 = 3626183) B3626183
theorem B1827647 : Blo 562809 1827647 := bstep (se 1 (by rfl) ⟨1370735, by rfl⟩ : syracuseStep 1827647 = 2741471) B2741471
theorem B1270619 : Blo 562809 1270619 := bstep (se 1 (by rfl) ⟨952964, by rfl⟩ : syracuseStep 1270619 = 1905929) B1905929
theorem B47539061 : Blo 562809 47539061 := bstep (se 5 (by rfl) ⟨2228393, by rfl⟩ : syracuseStep 47539061 = 4456787) B4456787
theorem B1270655 : Blo 562809 1270655 := bstep (se 1 (by rfl) ⟨952991, by rfl⟩ : syracuseStep 1270655 = 1905983) B1905983
theorem B844799 : Blo 562809 844799 := bstep (se 1 (by rfl) ⟨633599, by rfl⟩ : syracuseStep 844799 = 1267199) B1267199
theorem B2712797 : Blo 562809 2712797 := bstep (se 3 (by rfl) ⟨508649, by rfl⟩ : syracuseStep 2712797 = 1017299) B1017299
theorem B845819 : Blo 562809 845819 := bstep (se 1 (by rfl) ⟨634364, by rfl⟩ : syracuseStep 845819 = 1268729) B1268729
theorem B1272185 : Blo 562809 1272185 := bstep (se 2 (by rfl) ⟨477069, by rfl⟩ : syracuseStep 1272185 = 954139) B954139
theorem B846431 : Blo 562809 846431 := bstep (se 1 (by rfl) ⟨634823, by rfl⟩ : syracuseStep 846431 = 1269647) B1269647
theorem B846503 : Blo 562809 846503 := bstep (se 1 (by rfl) ⟨634877, by rfl⟩ : syracuseStep 846503 = 1269755) B1269755
theorem B2780027 : Blo 562809 2780027 := bstep (se 1 (by rfl) ⟨2085020, by rfl⟩ : syracuseStep 2780027 = 4170041) B4170041
theorem B846911 : Blo 562809 846911 := bstep (se 1 (by rfl) ⟨635183, by rfl⟩ : syracuseStep 846911 = 1270367) B1270367
theorem B847145 : Blo 562809 847145 := bstep (se 2 (by rfl) ⟨317679, by rfl⟩ : syracuseStep 847145 = 635359) B635359
theorem B847151 : Blo 562809 847151 := bstep (se 1 (by rfl) ⟨635363, by rfl⟩ : syracuseStep 847151 = 1270727) B1270727
theorem B847337 : Blo 562809 847337 := bstep (se 2 (by rfl) ⟨317751, by rfl⟩ : syracuseStep 847337 = 635503) B635503
theorem B847391 : Blo 562809 847391 := bstep (se 1 (by rfl) ⟨635543, by rfl⟩ : syracuseStep 847391 = 1271087) B1271087
theorem B847481 : Blo 562809 847481 := bstep (se 2 (by rfl) ⟨317805, by rfl⟩ : syracuseStep 847481 = 635611) B635611
theorem B1273481 : Blo 562809 1273481 := bstep (se 2 (by rfl) ⟨477555, by rfl⟩ : syracuseStep 1273481 = 955111) B955111
theorem B1273535 : Blo 562809 1273535 := bstep (se 1 (by rfl) ⟨955151, by rfl⟩ : syracuseStep 1273535 = 1910303) B1910303
theorem B4125127 : Blo 562809 4125127 := bstep (se 1 (by rfl) ⟨3093845, by rfl⟩ : syracuseStep 4125127 = 6187691) B6187691
theorem B848495 : Blo 562809 848495 := bstep (se 1 (by rfl) ⟨636371, by rfl⟩ : syracuseStep 848495 = 1272743) B1272743
theorem B4879129 : Blo 562809 4879129 := bstep (se 2 (by rfl) ⟨1829673, by rfl⟩ : syracuseStep 4879129 = 3659347) B3659347
theorem B1275263 : Blo 562809 1275263 := bstep (se 1 (by rfl) ⟨956447, by rfl⟩ : syracuseStep 1275263 = 1912895) B1912895
theorem B849407 : Blo 562809 849407 := bstep (se 1 (by rfl) ⟨637055, by rfl⟩ : syracuseStep 849407 = 1274111) B1274111
theorem B1242983 : Blo 562809 1242983 := bstep (se 1 (by rfl) ⟨932237, by rfl⟩ : syracuseStep 1242983 = 1864475) B1864475
theorem B850031 : Blo 562809 850031 := bstep (se 1 (by rfl) ⟨637523, by rfl⟩ : syracuseStep 850031 = 1275047) B1275047
theorem B4815227 : Blo 562809 4815227 := bstep (se 1 (by rfl) ⟨3611420, by rfl⟩ : syracuseStep 4815227 = 7222841) B7222841
theorem B1604279 : Blo 562809 1604279 := bstep (se 1 (by rfl) ⟨1203209, by rfl⟩ : syracuseStep 1604279 = 2406419) B2406419
theorem B1604393 : Blo 562809 1604393 := bstep (se 2 (by rfl) ⟨601647, by rfl⟩ : syracuseStep 1604393 = 1203295) B1203295
theorem B2849579 : Blo 562809 2849579 := bstep (se 1 (by rfl) ⟨2137184, by rfl⟩ : syracuseStep 2849579 = 4274369) B4274369
theorem B1604735 : Blo 562809 1604735 := bstep (se 1 (by rfl) ⟨1203551, by rfl⟩ : syracuseStep 1604735 = 2407103) B2407103
theorem B2851037 : Blo 562809 2851037 := bstep (se 3 (by rfl) ⟨534569, by rfl⟩ : syracuseStep 2851037 = 1069139) B1069139
theorem B950825 : Blo 562809 950825 := bstep (se 2 (by rfl) ⟨356559, by rfl⟩ : syracuseStep 950825 = 713119) B713119
theorem B17434217 : Blo 562809 17434217 := bstep (se 2 (by rfl) ⟨6537831, by rfl⟩ : syracuseStep 17434217 = 13075663) B13075663
theorem B2852495 : Blo 562809 2852495 := bstep (se 1 (by rfl) ⟨2139371, by rfl⟩ : syracuseStep 2852495 = 4278743) B4278743
theorem B1902527 : Blo 562809 1902527 := bstep (se 1 (by rfl) ⟨1426895, by rfl⟩ : syracuseStep 1902527 = 2853791) B2853791
theorem B952607 : Blo 562809 952607 := bstep (se 1 (by rfl) ⟨714455, by rfl⟩ : syracuseStep 952607 = 1428911) B1428911
theorem B1083883 : Blo 562809 1083883 := bstep (se 1 (by rfl) ⟨812912, by rfl⟩ : syracuseStep 1083883 = 1625825) B1625825
theorem B1903823 : Blo 562809 1903823 := bstep (se 1 (by rfl) ⟨1427867, by rfl⟩ : syracuseStep 1903823 = 2855735) B2855735
theorem B8162603 : Blo 562809 8162603 := bstep (se 1 (by rfl) ⟨6121952, by rfl⟩ : syracuseStep 8162603 = 12243905) B12243905
theorem B3214799 : Blo 562809 3214799 := bstep (se 1 (by rfl) ⟨2411099, by rfl⟩ : syracuseStep 3214799 = 4822199) B4822199
theorem B1446491 : Blo 562809 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B2200255 : Blo 562809 2200255 := bstep (se 1 (by rfl) ⟨1650191, by rfl⟩ : syracuseStep 2200255 = 3300383) B3300383
theorem B3314621 : Blo 562809 3314621 := bstep (se 3 (by rfl) ⟨621491, by rfl⟩ : syracuseStep 3314621 = 1242983) B1242983
theorem B955327 : Blo 562809 955327 := bstep (se 1 (by rfl) ⟨716495, by rfl⟩ : syracuseStep 955327 = 1432991) B1432991
theorem B726175 : Blo 562809 726175 := bstep (se 1 (by rfl) ⟨544631, by rfl⟩ : syracuseStep 726175 = 1089263) B1089263
theorem B6428321 : Blo 562809 6428321 := bstep (se 2 (by rfl) ⟨2410620, by rfl⟩ : syracuseStep 6428321 = 4821241) B4821241
theorem B13932335 : Blo 562809 13932335 := bstep (se 1 (by rfl) ⟨10449251, by rfl⟩ : syracuseStep 13932335 = 20898503) B20898503
theorem B1218431 : Blo 562809 1218431 := bstep (se 1 (by rfl) ⟨913823, by rfl⟩ : syracuseStep 1218431 = 1827647) B1827647
theorem B31692707 : Blo 562809 31692707 := bstep (se 1 (by rfl) ⟨23769530, by rfl⟩ : syracuseStep 31692707 = 47539061) B47539061
theorem B563199 : Blo 562809 563199 := bstep (se 1 (by rfl) ⟨422399, by rfl⟩ : syracuseStep 563199 = 844799) B844799
theorem B1808531 : Blo 562809 1808531 := bstep (se 1 (by rfl) ⟨1356398, by rfl⟩ : syracuseStep 1808531 = 2712797) B2712797
theorem B2038375 : Blo 562809 2038375 := bstep (se 1 (by rfl) ⟨1528781, by rfl⟩ : syracuseStep 2038375 = 3057563) B3057563
theorem B563879 : Blo 562809 563879 := bstep (se 1 (by rfl) ⟨422909, by rfl⟩ : syracuseStep 563879 = 845819) B845819
theorem B564287 : Blo 562809 564287 := bstep (se 1 (by rfl) ⟨423215, by rfl⟩ : syracuseStep 564287 = 846431) B846431
theorem B1907819 : Blo 562809 1907819 := bstep (se 1 (by rfl) ⟨1430864, by rfl⟩ : syracuseStep 1907819 = 2861729) B2861729
theorem B564335 : Blo 562809 564335 := bstep (se 1 (by rfl) ⟨423251, by rfl⟩ : syracuseStep 564335 = 846503) B846503
theorem B564607 : Blo 562809 564607 := bstep (se 1 (by rfl) ⟨423455, by rfl⟩ : syracuseStep 564607 = 846911) B846911
theorem B564763 : Blo 562809 564763 := bstep (se 1 (by rfl) ⟨423572, by rfl⟩ : syracuseStep 564763 = 847145) B847145
theorem B1908251 : Blo 562809 1908251 := bstep (se 1 (by rfl) ⟨1431188, by rfl⟩ : syracuseStep 1908251 = 2862377) B2862377
theorem B564767 : Blo 562809 564767 := bstep (se 1 (by rfl) ⟨423575, by rfl⟩ : syracuseStep 564767 = 847151) B847151
theorem B564891 : Blo 562809 564891 := bstep (se 1 (by rfl) ⟨423668, by rfl⟩ : syracuseStep 564891 = 847337) B847337
theorem B564927 : Blo 562809 564927 := bstep (se 1 (by rfl) ⟨423695, by rfl⟩ : syracuseStep 564927 = 847391) B847391
theorem B564987 : Blo 562809 564987 := bstep (se 1 (by rfl) ⟨423740, by rfl⟩ : syracuseStep 564987 = 847481) B847481
theorem B3612833 : Blo 562809 3612833 := bstep (se 2 (by rfl) ⟨1354812, by rfl⟩ : syracuseStep 3612833 = 2709625) B2709625
theorem B565663 : Blo 562809 565663 := bstep (se 1 (by rfl) ⟨424247, by rfl⟩ : syracuseStep 565663 = 848495) B848495
theorem B1909385 : Blo 562809 1909385 := bstep (se 2 (by rfl) ⟨716019, by rfl⟩ : syracuseStep 1909385 = 1432039) B1432039
theorem B2859785 : Blo 562809 2859785 := bstep (se 2 (by rfl) ⟨1072419, by rfl⟩ : syracuseStep 2859785 = 2144839) B2144839
theorem B566271 : Blo 562809 566271 := bstep (se 1 (by rfl) ⟨424703, by rfl⟩ : syracuseStep 566271 = 849407) B849407
theorem B566687 : Blo 562809 566687 := bstep (se 1 (by rfl) ⟨425015, by rfl⟩ : syracuseStep 566687 = 850031) B850031
theorem B7219151 : Blo 562809 7219151 := bstep (se 1 (by rfl) ⟨5414363, by rfl⟩ : syracuseStep 7219151 = 10828727) B10828727
theorem B35858765 : Blo 562809 35858765 := bstep (se 3 (by rfl) ⟨6723518, by rfl⟩ : syracuseStep 35858765 = 13447037) B13447037
theorem B10857635 : Blo 562809 10857635 := bstep (se 1 (by rfl) ⟨8143226, by rfl⟩ : syracuseStep 10857635 = 16286453) B16286453
theorem B16231913 : Blo 562809 16231913 := bstep (se 2 (by rfl) ⟨6086967, by rfl⟩ : syracuseStep 16231913 = 12173935) B12173935
theorem B9809515 : Blo 562809 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B3223273 : Blo 562809 3223273 := bstep (se 2 (by rfl) ⟨1208727, by rfl⟩ : syracuseStep 3223273 = 2417455) B2417455
theorem B1355735 : Blo 562809 1355735 := bstep (se 1 (by rfl) ⟨1016801, by rfl⟩ : syracuseStep 1355735 = 2033603) B2033603
theorem B2863187 : Blo 562809 2863187 := bstep (se 1 (by rfl) ⟨2147390, by rfl⟩ : syracuseStep 2863187 = 4294781) B4294781
theorem B2437415 : Blo 562809 2437415 := bstep (se 1 (by rfl) ⟨1828061, by rfl⟩ : syracuseStep 2437415 = 3656123) B3656123
theorem B2142895 : Blo 562809 2142895 := bstep (se 1 (by rfl) ⟨1607171, by rfl⟩ : syracuseStep 2142895 = 3214343) B3214343
theorem B2863835 : Blo 562809 2863835 := bstep (se 1 (by rfl) ⟨2147876, by rfl⟩ : syracuseStep 2863835 = 4295753) B4295753
theorem B1029631 : Blo 562809 1029631 := bstep (se 1 (by rfl) ⟨772223, by rfl⟩ : syracuseStep 1029631 = 1544447) B1544447
theorem B10860641 : Blo 562809 10860641 := bstep (se 2 (by rfl) ⟨4072740, by rfl⟩ : syracuseStep 10860641 = 8145481) B8145481
theorem B637375 : Blo 562809 637375 := bstep (se 1 (by rfl) ⟨478031, by rfl⟩ : syracuseStep 637375 = 956063) B956063
theorem B604783 : Blo 562809 604783 := bstep (se 1 (by rfl) ⟨453587, by rfl⟩ : syracuseStep 604783 = 907175) B907175
theorem B965407 : Blo 562809 965407 := bstep (se 1 (by rfl) ⟨724055, by rfl⟩ : syracuseStep 965407 = 1448111) B1448111
theorem B1719103 : Blo 562809 1719103 := bstep (se 1 (by rfl) ⟨1289327, by rfl⟩ : syracuseStep 1719103 = 2578655) B2578655
theorem B5880667 : Blo 562809 5880667 := bstep (se 1 (by rfl) ⟨4410500, by rfl⟩ : syracuseStep 5880667 = 8821001) B8821001
theorem B9158017 : Blo 562809 9158017 := bstep (se 2 (by rfl) ⟨3434256, by rfl⟩ : syracuseStep 9158017 = 6868513) B6868513
theorem B10862099 : Blo 562809 10862099 := bstep (se 1 (by rfl) ⟨8146574, by rfl⟩ : syracuseStep 10862099 = 16293149) B16293149
theorem B3096959 : Blo 562809 3096959 := bstep (se 1 (by rfl) ⟨2322719, by rfl⟩ : syracuseStep 3096959 = 4645439) B4645439
theorem B1425833 : Blo 562809 1425833 := bstep (se 2 (by rfl) ⟨534687, by rfl⟩ : syracuseStep 1425833 = 1069375) B1069375
theorem B3851063 : Blo 562809 3851063 := bstep (se 1 (by rfl) ⟨2888297, by rfl⟩ : syracuseStep 3851063 = 5776595) B5776595
theorem B6505505 : Blo 562809 6505505 := bstep (se 2 (by rfl) ⟨2439564, by rfl⟩ : syracuseStep 6505505 = 4879129) B4879129
theorem B1853351 : Blo 562809 1853351 := bstep (se 1 (by rfl) ⟨1390013, by rfl⟩ : syracuseStep 1853351 = 2780027) B2780027
theorem B5425127 : Blo 562809 5425127 := bstep (se 1 (by rfl) ⟨4068845, by rfl⟩ : syracuseStep 5425127 = 8137691) B8137691
theorem B4835321 : Blo 562809 4835321 := bstep (se 2 (by rfl) ⟨1813245, by rfl⟩ : syracuseStep 4835321 = 3626491) B3626491
theorem B8702579 : Blo 562809 8702579 := bstep (se 1 (by rfl) ⟨6526934, by rfl⟩ : syracuseStep 8702579 = 13053869) B13053869
theorem B46451789 : Blo 562809 46451789 := bstep (se 3 (by rfl) ⟨8709710, by rfl⟩ : syracuseStep 46451789 = 17419421) B17419421
theorem B2150171 : Blo 562809 2150171 := bstep (se 1 (by rfl) ⟨1612628, by rfl⟩ : syracuseStep 2150171 = 3225257) B3225257
theorem B1069519 : Blo 562809 1069519 := bstep (se 1 (by rfl) ⟨802139, by rfl⟩ : syracuseStep 1069519 = 1604279) B1604279
theorem B4968955 : Blo 562809 4968955 := bstep (se 1 (by rfl) ⟨3726716, by rfl⟩ : syracuseStep 4968955 = 7453433) B7453433
theorem B1069595 : Blo 562809 1069595 := bstep (se 1 (by rfl) ⟨802196, by rfl⟩ : syracuseStep 1069595 = 1604393) B1604393
theorem B1069823 : Blo 562809 1069823 := bstep (se 1 (by rfl) ⟨802367, by rfl⟩ : syracuseStep 1069823 = 1604735) B1604735
theorem B251549023 : Blo 562809 251549023 := bstep (se 1 (by rfl) ⟨188661767, by rfl⟩ : syracuseStep 251549023 = 377323535) B377323535
theorem B906751 : Blo 562809 906751 := bstep (se 1 (by rfl) ⟨680063, by rfl⟩ : syracuseStep 906751 = 1360127) B1360127
theorem B37213991 : Blo 562809 37213991 := bstep (se 1 (by rfl) ⟨27910493, by rfl⟩ : syracuseStep 37213991 = 55820987) B55820987
theorem B1202843 : Blo 562809 1202843 := bstep (se 1 (by rfl) ⟨902132, by rfl⟩ : syracuseStep 1202843 = 1804265) B1804265
theorem B1269359 : Blo 562809 1269359 := bstep (se 1 (by rfl) ⟨952019, by rfl⟩ : syracuseStep 1269359 = 1904039) B1904039
theorem B4284575 : Blo 562809 4284575 := bstep (se 1 (by rfl) ⟨3213431, by rfl⟩ : syracuseStep 4284575 = 6426863) B6426863
theorem B1204559 : Blo 562809 1204559 := bstep (se 1 (by rfl) ⟨903419, by rfl⟩ : syracuseStep 1204559 = 1806839) B1806839
theorem B1073567 : Blo 562809 1073567 := bstep (se 1 (by rfl) ⟨805175, by rfl⟩ : syracuseStep 1073567 = 1610351) B1610351
theorem B9265589 : Blo 562809 9265589 := bstep (se 5 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 9265589 = 868649) B868649
theorem B844379 : Blo 562809 844379 := bstep (se 1 (by rfl) ⟨633284, by rfl⟩ : syracuseStep 844379 = 1266569) B1266569
theorem B1204969 : Blo 562809 1204969 := bstep (se 2 (by rfl) ⟨451863, by rfl⟩ : syracuseStep 1204969 = 903727) B903727
theorem B844583 : Blo 562809 844583 := bstep (se 1 (by rfl) ⟨633437, by rfl⟩ : syracuseStep 844583 = 1266875) B1266875
theorem B844841 : Blo 562809 844841 := bstep (se 2 (by rfl) ⟨316815, by rfl⟩ : syracuseStep 844841 = 633631) B633631
theorem B10314971 : Blo 562809 10314971 := bstep (se 1 (by rfl) ⟨7736228, by rfl⟩ : syracuseStep 10314971 = 15472457) B15472457
theorem B1271123 : Blo 562809 1271123 := bstep (se 1 (by rfl) ⟨953342, by rfl⟩ : syracuseStep 1271123 = 1906685) B1906685
theorem B845879 : Blo 562809 845879 := bstep (se 1 (by rfl) ⟨634409, by rfl⟩ : syracuseStep 845879 = 1268819) B1268819
theorem B845915 : Blo 562809 845915 := bstep (se 1 (by rfl) ⟨634436, by rfl⟩ : syracuseStep 845915 = 1268873) B1268873
theorem B845927 : Blo 562809 845927 := bstep (se 1 (by rfl) ⟨634445, by rfl⟩ : syracuseStep 845927 = 1268891) B1268891
theorem B845951 : Blo 562809 845951 := bstep (se 1 (by rfl) ⟨634463, by rfl⟩ : syracuseStep 845951 = 1268927) B1268927
theorem B5433587 : Blo 562809 5433587 := bstep (se 1 (by rfl) ⟨4075190, by rfl⟩ : syracuseStep 5433587 = 8150381) B8150381
theorem B1075655 : Blo 562809 1075655 := bstep (se 1 (by rfl) ⟨806741, by rfl⟩ : syracuseStep 1075655 = 1613483) B1613483
theorem B846569 : Blo 562809 846569 := bstep (se 2 (by rfl) ⟨317463, by rfl⟩ : syracuseStep 846569 = 634927) B634927
theorem B846623 : Blo 562809 846623 := bstep (se 1 (by rfl) ⟨634967, by rfl⟩ : syracuseStep 846623 = 1269935) B1269935
theorem B846953 : Blo 562809 846953 := bstep (se 2 (by rfl) ⟨317607, by rfl⟩ : syracuseStep 846953 = 635215) B635215
theorem B847079 : Blo 562809 847079 := bstep (se 1 (by rfl) ⟨635309, by rfl⟩ : syracuseStep 847079 = 1270619) B1270619
theorem B847103 : Blo 562809 847103 := bstep (se 1 (by rfl) ⟨635327, by rfl⟩ : syracuseStep 847103 = 1270655) B1270655
theorem B5500169 : Blo 562809 5500169 := bstep (se 2 (by rfl) ⟨2062563, by rfl⟩ : syracuseStep 5500169 = 4125127) B4125127
theorem B1273247 : Blo 562809 1273247 := bstep (se 1 (by rfl) ⟨954935, by rfl⟩ : syracuseStep 1273247 = 1909871) B1909871
theorem B848123 : Blo 562809 848123 := bstep (se 1 (by rfl) ⟨636092, by rfl⟩ : syracuseStep 848123 = 1272185) B1272185
theorem B2715947 : Blo 562809 2715947 := bstep (se 1 (by rfl) ⟨2036960, by rfl⟩ : syracuseStep 2715947 = 4073921) B4073921
theorem B848489 : Blo 562809 848489 := bstep (se 2 (by rfl) ⟨318183, by rfl⟩ : syracuseStep 848489 = 636367) B636367
theorem B1274651 : Blo 562809 1274651 := bstep (se 1 (by rfl) ⟨955988, by rfl⟩ : syracuseStep 1274651 = 1911977) B1911977
theorem B848987 : Blo 562809 848987 := bstep (se 1 (by rfl) ⟨636740, by rfl⟩ : syracuseStep 848987 = 1273481) B1273481
theorem B849023 : Blo 562809 849023 := bstep (se 1 (by rfl) ⟨636767, by rfl⟩ : syracuseStep 849023 = 1273535) B1273535
theorem B849785 : Blo 562809 849785 := bstep (se 2 (by rfl) ⟨318669, by rfl⟩ : syracuseStep 849785 = 637339) B637339
theorem B850175 : Blo 562809 850175 := bstep (se 1 (by rfl) ⟨637631, by rfl⟩ : syracuseStep 850175 = 1275263) B1275263
theorem B3210151 : Blo 562809 3210151 := bstep (se 1 (by rfl) ⟨2407613, by rfl⟩ : syracuseStep 3210151 = 4815227) B4815227
theorem B1899719 : Blo 562809 1899719 := bstep (se 1 (by rfl) ⟨1424789, by rfl⟩ : syracuseStep 1899719 = 2849579) B2849579
theorem B1933183 : Blo 562809 1933183 := bstep (se 1 (by rfl) ⟨1449887, by rfl⟩ : syracuseStep 1933183 = 2899775) B2899775
theorem B950251 : Blo 562809 950251 := bstep (se 1 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 950251 = 1425377) B1425377
theorem B1015799 : Blo 562809 1015799 := bstep (se 1 (by rfl) ⟨761849, by rfl⟩ : syracuseStep 1015799 = 1523699) B1523699
theorem B1900691 : Blo 562809 1900691 := bstep (se 1 (by rfl) ⟨1425518, by rfl⟩ : syracuseStep 1900691 = 2851037) B2851037
theorem B950555 : Blo 562809 950555 := bstep (se 1 (by rfl) ⟨712916, by rfl⟩ : syracuseStep 950555 = 1425833) B1425833
theorem B1606625 : Blo 562809 1606625 := bstep (se 2 (by rfl) ⟨602484, by rfl⟩ : syracuseStep 1606625 = 1204969) B1204969
theorem B8258557 : Blo 562809 8258557 := bstep (se 3 (by rfl) ⟨1548479, by rfl⟩ : syracuseStep 8258557 = 3096959) B3096959
theorem B1901663 : Blo 562809 1901663 := bstep (se 1 (by rfl) ⟨1426247, by rfl⟩ : syracuseStep 1901663 = 2852495) B2852495
theorem B5801719 : Blo 562809 5801719 := bstep (se 1 (by rfl) ⟨4351289, by rfl⟩ : syracuseStep 5801719 = 8702579) B8702579
theorem B30967859 : Blo 562809 30967859 := bstep (se 1 (by rfl) ⟨23225894, by rfl⟩ : syracuseStep 30967859 = 46451789) B46451789
theorem B5441735 : Blo 562809 5441735 := bstep (se 1 (by rfl) ⟨4081301, by rfl⟩ : syracuseStep 5441735 = 8162603) B8162603
theorem B1445177 : Blo 562809 1445177 := bstep (se 2 (by rfl) ⟨541941, by rfl⟩ : syracuseStep 1445177 = 1083883) B1083883
theorem B24809327 : Blo 562809 24809327 := bstep (se 1 (by rfl) ⟨18606995, by rfl⟩ : syracuseStep 24809327 = 37213991) B37213991
theorem B4297697 : Blo 562809 4297697 := bstep (se 2 (by rfl) ⟨1611636, by rfl⟩ : syracuseStep 4297697 = 3223273) B3223273
theorem B2856383 : Blo 562809 2856383 := bstep (se 1 (by rfl) ⟨2142287, by rfl⟩ : syracuseStep 2856383 = 4284575) B4284575
theorem B562919 : Blo 562809 562919 := bstep (se 1 (by rfl) ⟨422189, by rfl⟩ : syracuseStep 562919 = 844379) B844379
theorem B1906523 : Blo 562809 1906523 := bstep (se 1 (by rfl) ⟨1429892, by rfl⟩ : syracuseStep 1906523 = 2859785) B2859785
theorem B563055 : Blo 562809 563055 := bstep (se 1 (by rfl) ⟨422291, by rfl⟩ : syracuseStep 563055 = 844583) B844583
theorem B6625273 : Blo 562809 6625273 := bstep (se 2 (by rfl) ⟨2484477, by rfl⟩ : syracuseStep 6625273 = 4968955) B4968955
theorem B563227 : Blo 562809 563227 := bstep (se 1 (by rfl) ⟨422420, by rfl⟩ : syracuseStep 563227 = 844841) B844841
theorem B3872933 : Blo 562809 3872933 := bstep (se 4 (by rfl) ⟨363087, by rfl⟩ : syracuseStep 3872933 = 726175) B726175
theorem B2857193 : Blo 562809 2857193 := bstep (se 2 (by rfl) ⟨1071447, by rfl⟩ : syracuseStep 2857193 = 2142895) B2142895
theorem B563919 : Blo 562809 563919 := bstep (se 1 (by rfl) ⟨422939, by rfl⟩ : syracuseStep 563919 = 845879) B845879
theorem B563943 : Blo 562809 563943 := bstep (se 1 (by rfl) ⟨422957, by rfl⟩ : syracuseStep 563943 = 845915) B845915
theorem B563951 : Blo 562809 563951 := bstep (se 1 (by rfl) ⟨422963, by rfl⟩ : syracuseStep 563951 = 845927) B845927
theorem B563967 : Blo 562809 563967 := bstep (se 1 (by rfl) ⟨422975, by rfl⟩ : syracuseStep 563967 = 845951) B845951
theorem B564379 : Blo 562809 564379 := bstep (se 1 (by rfl) ⟨423284, by rfl⟩ : syracuseStep 564379 = 846569) B846569
theorem B564415 : Blo 562809 564415 := bstep (se 1 (by rfl) ⟨423311, by rfl⟩ : syracuseStep 564415 = 846623) B846623
theorem B564635 : Blo 562809 564635 := bstep (se 1 (by rfl) ⟨423476, by rfl⟩ : syracuseStep 564635 = 846953) B846953
theorem B564719 : Blo 562809 564719 := bstep (se 1 (by rfl) ⟨423539, by rfl⟩ : syracuseStep 564719 = 847079) B847079
theorem B564735 : Blo 562809 564735 := bstep (se 1 (by rfl) ⟨423551, by rfl⟩ : syracuseStep 564735 = 847103) B847103
theorem B10821275 : Blo 562809 10821275 := bstep (se 1 (by rfl) ⟨8115956, by rfl⟩ : syracuseStep 10821275 = 16231913) B16231913
theorem B1908791 : Blo 562809 1908791 := bstep (se 1 (by rfl) ⟨1431593, by rfl⟩ : syracuseStep 1908791 = 2863187) B2863187
theorem B565415 : Blo 562809 565415 := bstep (se 1 (by rfl) ⟨424061, by rfl⟩ : syracuseStep 565415 = 848123) B848123
theorem B1810631 : Blo 562809 1810631 := bstep (se 1 (by rfl) ⟨1357973, by rfl⟩ : syracuseStep 1810631 = 2715947) B2715947
theorem B565659 : Blo 562809 565659 := bstep (se 1 (by rfl) ⟨424244, by rfl⟩ : syracuseStep 565659 = 848489) B848489
theorem B1909223 : Blo 562809 1909223 := bstep (se 1 (by rfl) ⟨1431917, by rfl⟩ : syracuseStep 1909223 = 2863835) B2863835
theorem B565991 : Blo 562809 565991 := bstep (se 1 (by rfl) ⟨424493, by rfl⟩ : syracuseStep 565991 = 848987) B848987
theorem B566015 : Blo 562809 566015 := bstep (se 1 (by rfl) ⟨424511, by rfl⟩ : syracuseStep 566015 = 849023) B849023
theorem B1287209 : Blo 562809 1287209 := bstep (se 2 (by rfl) ⟨482703, by rfl⟩ : syracuseStep 1287209 = 965407) B965407
theorem B7840889 : Blo 562809 7840889 := bstep (se 2 (by rfl) ⟨2940333, by rfl⟩ : syracuseStep 7840889 = 5880667) B5880667
theorem B566523 : Blo 562809 566523 := bstep (se 1 (by rfl) ⟨424892, by rfl⟩ : syracuseStep 566523 = 849785) B849785
theorem B566783 : Blo 562809 566783 := bstep (se 1 (by rfl) ⟨425087, by rfl⟩ : syracuseStep 566783 = 850175) B850175
theorem B3615293 : Blo 562809 3615293 := bstep (se 3 (by rfl) ⟨677867, by rfl⟩ : syracuseStep 3615293 = 1355735) B1355735
theorem B633883 : Blo 562809 633883 := bstep (se 1 (by rfl) ⟨475412, by rfl⟩ : syracuseStep 633883 = 950825) B950825
theorem B2567375 : Blo 562809 2567375 := bstep (se 1 (by rfl) ⟨1925531, by rfl⟩ : syracuseStep 2567375 = 3851063) B3851063
theorem B4337003 : Blo 562809 4337003 := bstep (se 1 (by rfl) ⟨3252752, by rfl⟩ : syracuseStep 4337003 = 6505505) B6505505
theorem B3616751 : Blo 562809 3616751 := bstep (se 1 (by rfl) ⟨2712563, by rfl⟩ : syracuseStep 3616751 = 5425127) B5425127
theorem B3223547 : Blo 562809 3223547 := bstep (se 1 (by rfl) ⟨2417660, by rfl⟩ : syracuseStep 3223547 = 4835321) B4835321
theorem B635071 : Blo 562809 635071 := bstep (se 1 (by rfl) ⟨476303, by rfl⟩ : syracuseStep 635071 = 952607) B952607
theorem B2143199 : Blo 562809 2143199 := bstep (se 1 (by rfl) ⟨1607399, by rfl⟩ : syracuseStep 2143199 = 3214799) B3214799
theorem B964327 : Blo 562809 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B2209747 : Blo 562809 2209747 := bstep (se 1 (by rfl) ⟨1657310, by rfl⟩ : syracuseStep 2209747 = 3314621) B3314621
theorem B46938773 : Blo 562809 46938773 := bstep (se 6 (by rfl) ⟨1100127, by rfl⟩ : syracuseStep 46938773 = 2200255) B2200255
theorem B801895 : Blo 562809 801895 := bstep (se 1 (by rfl) ⟨601421, by rfl⟩ : syracuseStep 801895 = 1202843) B1202843
theorem B2408555 : Blo 562809 2408555 := bstep (se 1 (by rfl) ⟨1806416, by rfl⟩ : syracuseStep 2408555 = 3612833) B3612833
theorem B803039 : Blo 562809 803039 := bstep (se 1 (by rfl) ⟨602279, by rfl⟩ : syracuseStep 803039 = 1204559) B1204559
theorem B6177059 : Blo 562809 6177059 := bstep (se 1 (by rfl) ⟨4632794, by rfl⟩ : syracuseStep 6177059 = 9265589) B9265589
theorem B1426025 : Blo 562809 1426025 := bstep (se 2 (by rfl) ⟨534759, by rfl⟩ : syracuseStep 1426025 = 1069519) B1069519
theorem B3622391 : Blo 562809 3622391 := bstep (se 1 (by rfl) ⟨2716793, by rfl⟩ : syracuseStep 3622391 = 5433587) B5433587
theorem B23905843 : Blo 562809 23905843 := bstep (se 1 (by rfl) ⟨17929382, by rfl⟩ : syracuseStep 23905843 = 35858765) B35858765
theorem B335398697 : Blo 562809 335398697 := bstep (se 2 (by rfl) ⟨125774511, by rfl⟩ : syracuseStep 335398697 = 251549023) B251549023
theorem B1624943 : Blo 562809 1624943 := bstep (se 1 (by rfl) ⟨1218707, by rfl⟩ : syracuseStep 1624943 = 2437415) B2437415
theorem B52317413 : Blo 562809 52317413 := bstep (se 4 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 52317413 = 9809515) B9809515
theorem B806377 : Blo 562809 806377 := bstep (se 2 (by rfl) ⟨302391, by rfl⟩ : syracuseStep 806377 = 604783) B604783
theorem B4280201 : Blo 562809 4280201 := bstep (se 2 (by rfl) ⟨1605075, by rfl⟩ : syracuseStep 4280201 = 3210151) B3210151
theorem B12210689 : Blo 562809 12210689 := bstep (se 2 (by rfl) ⟨4579008, by rfl⟩ : syracuseStep 12210689 = 9158017) B9158017
theorem B1266479 : Blo 562809 1266479 := bstep (se 1 (by rfl) ⟨949859, by rfl⟩ : syracuseStep 1266479 = 1899719) B1899719
theorem B2577577 : Blo 562809 2577577 := bstep (se 2 (by rfl) ⟨966591, by rfl⟩ : syracuseStep 2577577 = 1933183) B1933183
theorem B1267001 : Blo 562809 1267001 := bstep (se 2 (by rfl) ⟨475125, by rfl⟩ : syracuseStep 1267001 = 950251) B950251
theorem B2708797 : Blo 562809 2708797 := bstep (se 3 (by rfl) ⟨507899, by rfl⟩ : syracuseStep 2708797 = 1015799) B1015799
theorem B1235567 : Blo 562809 1235567 := bstep (se 1 (by rfl) ⟨926675, by rfl⟩ : syracuseStep 1235567 = 1853351) B1853351
theorem B1268351 : Blo 562809 1268351 := bstep (se 1 (by rfl) ⟨951263, by rfl⟩ : syracuseStep 1268351 = 1902527) B1902527
theorem B1269215 : Blo 562809 1269215 := bstep (se 1 (by rfl) ⟨951911, by rfl⟩ : syracuseStep 1269215 = 1903823) B1903823
theorem B1433447 : Blo 562809 1433447 := bstep (se 1 (by rfl) ⟨1075085, by rfl⟩ : syracuseStep 1433447 = 2150171) B2150171
theorem B713063 : Blo 562809 713063 := bstep (se 1 (by rfl) ⟨534797, by rfl⟩ : syracuseStep 713063 = 1069595) B1069595
theorem B713215 : Blo 562809 713215 := bstep (se 1 (by rfl) ⟨534911, by rfl⟩ : syracuseStep 713215 = 1069823) B1069823
theorem B4285547 : Blo 562809 4285547 := bstep (se 1 (by rfl) ⟨3214160, by rfl⟩ : syracuseStep 4285547 = 6428321) B6428321
theorem B812287 : Blo 562809 812287 := bstep (se 1 (by rfl) ⟨609215, by rfl⟩ : syracuseStep 812287 = 1218431) B1218431
theorem B21128471 : Blo 562809 21128471 := bstep (se 1 (by rfl) ⟨15846353, by rfl⟩ : syracuseStep 21128471 = 31692707) B31692707
theorem B1205687 : Blo 562809 1205687 := bstep (se 1 (by rfl) ⟨904265, by rfl⟩ : syracuseStep 1205687 = 1808531) B1808531
theorem B46491245 : Blo 562809 46491245 := bstep (se 3 (by rfl) ⟨8717108, by rfl⟩ : syracuseStep 46491245 = 17434217) B17434217
theorem B1271879 : Blo 562809 1271879 := bstep (se 1 (by rfl) ⟨953909, by rfl⟩ : syracuseStep 1271879 = 1907819) B1907819
theorem B37152893 : Blo 562809 37152893 := bstep (se 3 (by rfl) ⟨6966167, by rfl⟩ : syracuseStep 37152893 = 13932335) B13932335
theorem B1272167 : Blo 562809 1272167 := bstep (se 1 (by rfl) ⟨954125, by rfl⟩ : syracuseStep 1272167 = 1908251) B1908251
theorem B846239 : Blo 562809 846239 := bstep (se 1 (by rfl) ⟨634679, by rfl⟩ : syracuseStep 846239 = 1269359) B1269359
theorem B715711 : Blo 562809 715711 := bstep (se 1 (by rfl) ⟨536783, by rfl⟩ : syracuseStep 715711 = 1073567) B1073567
theorem B1272923 : Blo 562809 1272923 := bstep (se 1 (by rfl) ⟨954692, by rfl⟩ : syracuseStep 1272923 = 1909385) B1909385
theorem B6876647 : Blo 562809 6876647 := bstep (se 1 (by rfl) ⟨5157485, by rfl⟩ : syracuseStep 6876647 = 10314971) B10314971
theorem B847415 : Blo 562809 847415 := bstep (se 1 (by rfl) ⟨635561, by rfl⟩ : syracuseStep 847415 = 1271123) B1271123
theorem B1273769 : Blo 562809 1273769 := bstep (se 2 (by rfl) ⟨477663, by rfl⟩ : syracuseStep 1273769 = 955327) B955327
theorem B4812767 : Blo 562809 4812767 := bstep (se 1 (by rfl) ⟨3609575, by rfl⟩ : syracuseStep 4812767 = 7219151) B7219151
theorem B717103 : Blo 562809 717103 := bstep (se 1 (by rfl) ⟨537827, by rfl⟩ : syracuseStep 717103 = 1075655) B1075655
theorem B1372841 : Blo 562809 1372841 := bstep (se 2 (by rfl) ⟨514815, by rfl⟩ : syracuseStep 1372841 = 1029631) B1029631
theorem B1209001 : Blo 562809 1209001 := bstep (se 2 (by rfl) ⟨453375, by rfl⟩ : syracuseStep 1209001 = 906751) B906751
theorem B7238423 : Blo 562809 7238423 := bstep (se 1 (by rfl) ⟨5428817, by rfl⟩ : syracuseStep 7238423 = 10857635) B10857635
theorem B3666779 : Blo 562809 3666779 := bstep (se 1 (by rfl) ⟨2750084, by rfl⟩ : syracuseStep 3666779 = 5500169) B5500169
theorem B848831 : Blo 562809 848831 := bstep (se 1 (by rfl) ⟨636623, by rfl⟩ : syracuseStep 848831 = 1273247) B1273247
theorem B849767 : Blo 562809 849767 := bstep (se 1 (by rfl) ⟨637325, by rfl⟩ : syracuseStep 849767 = 1274651) B1274651
theorem B849833 : Blo 562809 849833 := bstep (se 2 (by rfl) ⟨318687, by rfl⟩ : syracuseStep 849833 = 637375) B637375
theorem B2717833 : Blo 562809 2717833 := bstep (se 2 (by rfl) ⟨1019187, by rfl⟩ : syracuseStep 2717833 = 2038375) B2038375
theorem B2292137 : Blo 562809 2292137 := bstep (se 2 (by rfl) ⟨859551, by rfl⟩ : syracuseStep 2292137 = 1719103) B1719103
theorem B7240427 : Blo 562809 7240427 := bstep (se 1 (by rfl) ⟨5430320, by rfl⟩ : syracuseStep 7240427 = 10860641) B10860641
theorem B7241399 : Blo 562809 7241399 := bstep (se 1 (by rfl) ⟨5431049, by rfl⟩ : syracuseStep 7241399 = 10862099) B10862099
theorem B1605703 : Blo 562809 1605703 := bstep (se 1 (by rfl) ⟨1204277, by rfl⟩ : syracuseStep 1605703 = 2408555) B2408555
theorem B950683 : Blo 562809 950683 := bstep (se 1 (by rfl) ⟨713012, by rfl⟩ : syracuseStep 950683 = 1426025) B1426025
theorem B950953 : Blo 562809 950953 := bstep (se 2 (by rfl) ⟨356607, by rfl⟩ : syracuseStep 950953 = 713215) B713215
theorem B1901501 : Blo 562809 1901501 := bstep (se 3 (by rfl) ⟨356531, by rfl⟩ : syracuseStep 1901501 = 713063) B713063
theorem B11011409 : Blo 562809 11011409 := bstep (se 2 (by rfl) ⟨4129278, by rfl⟩ : syracuseStep 11011409 = 8258557) B8258557
theorem B20645239 : Blo 562809 20645239 := bstep (se 1 (by rfl) ⟨15483929, by rfl⟩ : syracuseStep 20645239 = 30967859) B30967859
theorem B1083295 : Blo 562809 1083295 := bstep (se 1 (by rfl) ⟨812471, by rfl⟩ : syracuseStep 1083295 = 1624943) B1624943
theorem B7735625 : Blo 562809 7735625 := bstep (se 2 (by rfl) ⟨2900859, by rfl⟩ : syracuseStep 7735625 = 5801719) B5801719
theorem B2853467 : Blo 562809 2853467 := bstep (se 1 (by rfl) ⟨2140100, by rfl⟩ : syracuseStep 2853467 = 4280201) B4280201
theorem B1904255 : Blo 562809 1904255 := bstep (se 1 (by rfl) ⟨1428191, by rfl⟩ : syracuseStep 1904255 = 2856383) B2856383
theorem B954281 : Blo 562809 954281 := bstep (se 2 (by rfl) ⟨357855, by rfl⟩ : syracuseStep 954281 = 715711) B715711
theorem B1904795 : Blo 562809 1904795 := bstep (se 1 (by rfl) ⟨1428596, by rfl⟩ : syracuseStep 1904795 = 2857193) B2857193
theorem B823711 : Blo 562809 823711 := bstep (se 1 (by rfl) ⟨617783, by rfl⟩ : syracuseStep 823711 = 1235567) B1235567
theorem B7214183 : Blo 562809 7214183 := bstep (se 1 (by rfl) ⟨5410637, by rfl⟩ : syracuseStep 7214183 = 10821275) B10821275
theorem B955631 : Blo 562809 955631 := bstep (se 1 (by rfl) ⟨716723, by rfl⟩ : syracuseStep 955631 = 1433447) B1433447
theorem B956137 : Blo 562809 956137 := bstep (se 2 (by rfl) ⟨358551, by rfl⟩ : syracuseStep 956137 = 717103) B717103
theorem B2857031 : Blo 562809 2857031 := bstep (se 1 (by rfl) ⟨2142773, by rfl⟩ : syracuseStep 2857031 = 4285547) B4285547
theorem B1612001 : Blo 562809 1612001 := bstep (se 2 (by rfl) ⟨604500, by rfl⟩ : syracuseStep 1612001 = 1209001) B1209001
theorem B4332197 : Blo 562809 4332197 := bstep (se 4 (by rfl) ⟨406143, by rfl⟩ : syracuseStep 4332197 = 812287) B812287
theorem B564159 : Blo 562809 564159 := bstep (se 1 (by rfl) ⟨423119, by rfl⟩ : syracuseStep 564159 = 846239) B846239
theorem B3611729 : Blo 562809 3611729 := bstep (se 2 (by rfl) ⟨1354398, by rfl⟩ : syracuseStep 3611729 = 2708797) B2708797
theorem B1711583 : Blo 562809 1711583 := bstep (se 1 (by rfl) ⟨1283687, by rfl⟩ : syracuseStep 1711583 = 2567375) B2567375
theorem B2891335 : Blo 562809 2891335 := bstep (se 1 (by rfl) ⟨2168501, by rfl⟩ : syracuseStep 2891335 = 4337003) B4337003
theorem B1285769 : Blo 562809 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B564943 : Blo 562809 564943 := bstep (se 1 (by rfl) ⟨423707, by rfl⟩ : syracuseStep 564943 = 847415) B847415
theorem B4825615 : Blo 562809 4825615 := bstep (se 1 (by rfl) ⟨3619211, by rfl⟩ : syracuseStep 4825615 = 7238423) B7238423
theorem B565887 : Blo 562809 565887 := bstep (se 1 (by rfl) ⟨424415, by rfl⟩ : syracuseStep 565887 = 848831) B848831
theorem B566511 : Blo 562809 566511 := bstep (se 1 (by rfl) ⟨424883, by rfl⟩ : syracuseStep 566511 = 849767) B849767
theorem B566555 : Blo 562809 566555 := bstep (se 1 (by rfl) ⟨424916, by rfl⟩ : syracuseStep 566555 = 849833) B849833
theorem B4826951 : Blo 562809 4826951 := bstep (se 1 (by rfl) ⟨3620213, by rfl⟩ : syracuseStep 4826951 = 7240427) B7240427
theorem B4827599 : Blo 562809 4827599 := bstep (se 1 (by rfl) ⟨3620699, by rfl⟩ : syracuseStep 4827599 = 7241399) B7241399
theorem B9644669 : Blo 562809 9644669 := bstep (se 3 (by rfl) ⟨1808375, by rfl⟩ : syracuseStep 9644669 = 3616751) B3616751
theorem B633703 : Blo 562809 633703 := bstep (se 1 (by rfl) ⟨475277, by rfl⟩ : syracuseStep 633703 = 950555) B950555
theorem B4828349 : Blo 562809 4828349 := bstep (se 3 (by rfl) ⟨905315, by rfl⟩ : syracuseStep 4828349 = 1810631) B1810631
theorem B2141437 : Blo 562809 2141437 := bstep (se 3 (by rfl) ⟨401519, by rfl⟩ : syracuseStep 2141437 = 803039) B803039
theorem B34878275 : Blo 562809 34878275 := bstep (se 1 (by rfl) ⟨26158706, by rfl⟩ : syracuseStep 34878275 = 52317413) B52317413
theorem B963451 : Blo 562809 963451 := bstep (se 1 (by rfl) ⟨722588, by rfl⟩ : syracuseStep 963451 = 1445177) B1445177
theorem B8140459 : Blo 562809 8140459 := bstep (se 1 (by rfl) ⟨6105344, by rfl⟩ : syracuseStep 8140459 = 12210689) B12210689
theorem B2865131 : Blo 562809 2865131 := bstep (se 1 (by rfl) ⟨2148848, by rfl⟩ : syracuseStep 2865131 = 4297697) B4297697
theorem B5227259 : Blo 562809 5227259 := bstep (se 1 (by rfl) ⟨3920444, by rfl⟩ : syracuseStep 5227259 = 7840889) B7840889
theorem B803791 : Blo 562809 803791 := bstep (se 1 (by rfl) ⟨602843, by rfl⟩ : syracuseStep 803791 = 1205687) B1205687
theorem B188565077 : Blo 562809 188565077 := bstep (se 8 (by rfl) ⟨1104873, by rfl⟩ : syracuseStep 188565077 = 2209747) B2209747
theorem B2410195 : Blo 562809 2410195 := bstep (se 1 (by rfl) ⟨1807646, by rfl⟩ : syracuseStep 2410195 = 3615293) B3615293
theorem B8833697 : Blo 562809 8833697 := bstep (se 2 (by rfl) ⟨3312636, by rfl⟩ : syracuseStep 8833697 = 6625273) B6625273
theorem B2149031 : Blo 562809 2149031 := bstep (se 1 (by rfl) ⟨1611773, by rfl⟩ : syracuseStep 2149031 = 3223547) B3223547
theorem B3623777 : Blo 562809 3623777 := bstep (se 2 (by rfl) ⟨1358916, by rfl⟩ : syracuseStep 3623777 = 2717833) B2717833
theorem B2444519 : Blo 562809 2444519 := bstep (se 1 (by rfl) ⟨1833389, by rfl⟩ : syracuseStep 2444519 = 3666779) B3666779
theorem B1428799 : Blo 562809 1428799 := bstep (se 1 (by rfl) ⟨1071599, by rfl⟩ : syracuseStep 1428799 = 2143199) B2143199
theorem B1069193 : Blo 562809 1069193 := bstep (se 2 (by rfl) ⟨400947, by rfl⟩ : syracuseStep 1069193 = 801895) B801895
theorem B1528091 : Blo 562809 1528091 := bstep (se 1 (by rfl) ⟨1146068, by rfl⟩ : syracuseStep 1528091 = 2292137) B2292137
theorem B1267127 : Blo 562809 1267127 := bstep (se 1 (by rfl) ⟨950345, by rfl⟩ : syracuseStep 1267127 = 1900691) B1900691
theorem B4118039 : Blo 562809 4118039 := bstep (se 1 (by rfl) ⟨3088529, by rfl⟩ : syracuseStep 4118039 = 6177059) B6177059
theorem B1071083 : Blo 562809 1071083 := bstep (se 1 (by rfl) ⟨803312, by rfl⟩ : syracuseStep 1071083 = 1606625) B1606625
theorem B1267775 : Blo 562809 1267775 := bstep (se 1 (by rfl) ⟨950831, by rfl⟩ : syracuseStep 1267775 = 1901663) B1901663
theorem B2414927 : Blo 562809 2414927 := bstep (se 1 (by rfl) ⟨1811195, by rfl⟩ : syracuseStep 2414927 = 3622391) B3622391
theorem B223599131 : Blo 562809 223599131 := bstep (se 1 (by rfl) ⟨167699348, by rfl⟩ : syracuseStep 223599131 = 335398697) B335398697
theorem B3627823 : Blo 562809 3627823 := bstep (se 1 (by rfl) ⟨2720867, by rfl⟩ : syracuseStep 3627823 = 5441735) B5441735
theorem B16539551 : Blo 562809 16539551 := bstep (se 1 (by rfl) ⟨12404663, by rfl⟩ : syracuseStep 16539551 = 24809327) B24809327
theorem B3432557 : Blo 562809 3432557 := bstep (se 3 (by rfl) ⟨643604, by rfl⟩ : syracuseStep 3432557 = 1287209) B1287209
theorem B844319 : Blo 562809 844319 := bstep (se 1 (by rfl) ⟨633239, by rfl⟩ : syracuseStep 844319 = 1266479) B1266479
theorem B844667 : Blo 562809 844667 := bstep (se 1 (by rfl) ⟨633500, by rfl⟩ : syracuseStep 844667 = 1267001) B1267001
theorem B1271015 : Blo 562809 1271015 := bstep (se 1 (by rfl) ⟨953261, by rfl⟩ : syracuseStep 1271015 = 1906523) B1906523
theorem B845177 : Blo 562809 845177 := bstep (se 2 (by rfl) ⟨316941, by rfl⟩ : syracuseStep 845177 = 633883) B633883
theorem B2581955 : Blo 562809 2581955 := bstep (se 1 (by rfl) ⟨1936466, by rfl⟩ : syracuseStep 2581955 = 3872933) B3872933
theorem B845567 : Blo 562809 845567 := bstep (se 1 (by rfl) ⟨634175, by rfl⟩ : syracuseStep 845567 = 1268351) B1268351
theorem B1075169 : Blo 562809 1075169 := bstep (se 2 (by rfl) ⟨403188, by rfl⟩ : syracuseStep 1075169 = 806377) B806377
theorem B846143 : Blo 562809 846143 := bstep (se 1 (by rfl) ⟨634607, by rfl⟩ : syracuseStep 846143 = 1269215) B1269215
theorem B1272527 : Blo 562809 1272527 := bstep (se 1 (by rfl) ⟨954395, by rfl⟩ : syracuseStep 1272527 = 1908791) B1908791
theorem B846761 : Blo 562809 846761 := bstep (se 2 (by rfl) ⟨317535, by rfl⟩ : syracuseStep 846761 = 635071) B635071
theorem B1272815 : Blo 562809 1272815 := bstep (se 1 (by rfl) ⟨954611, by rfl⟩ : syracuseStep 1272815 = 1909223) B1909223
theorem B14085647 : Blo 562809 14085647 := bstep (se 1 (by rfl) ⟨10564235, by rfl⟩ : syracuseStep 14085647 = 21128471) B21128471
theorem B30994163 : Blo 562809 30994163 := bstep (se 1 (by rfl) ⟨23245622, by rfl⟩ : syracuseStep 30994163 = 46491245) B46491245
theorem B847919 : Blo 562809 847919 := bstep (se 1 (by rfl) ⟨635939, by rfl⟩ : syracuseStep 847919 = 1271879) B1271879
theorem B24768595 : Blo 562809 24768595 := bstep (se 1 (by rfl) ⟨18576446, by rfl⟩ : syracuseStep 24768595 = 37152893) B37152893
theorem B3436769 : Blo 562809 3436769 := bstep (se 2 (by rfl) ⟨1288788, by rfl⟩ : syracuseStep 3436769 = 2577577) B2577577
theorem B848111 : Blo 562809 848111 := bstep (se 1 (by rfl) ⟨636083, by rfl⟩ : syracuseStep 848111 = 1272167) B1272167
theorem B848615 : Blo 562809 848615 := bstep (se 1 (by rfl) ⟨636461, by rfl⟩ : syracuseStep 848615 = 1272923) B1272923
theorem B4584431 : Blo 562809 4584431 := bstep (se 1 (by rfl) ⟨3438323, by rfl⟩ : syracuseStep 4584431 = 6876647) B6876647
theorem B849179 : Blo 562809 849179 := bstep (se 1 (by rfl) ⟨636884, by rfl⟩ : syracuseStep 849179 = 1273769) B1273769
theorem B3208511 : Blo 562809 3208511 := bstep (se 1 (by rfl) ⟨2406383, by rfl⟩ : syracuseStep 3208511 = 4812767) B4812767
theorem B127497829 : Blo 562809 127497829 := bstep (se 4 (by rfl) ⟨11952921, by rfl⟩ : syracuseStep 127497829 = 23905843) B23905843
theorem B915227 : Blo 562809 915227 := bstep (se 1 (by rfl) ⟨686420, by rfl⟩ : syracuseStep 915227 = 1372841) B1372841
theorem B31292515 : Blo 562809 31292515 := bstep (se 1 (by rfl) ⟨23469386, by rfl⟩ : syracuseStep 31292515 = 46938773) B46938773
theorem B7340939 : Blo 562809 7340939 := bstep (se 1 (by rfl) ⟨5505704, by rfl⟩ : syracuseStep 7340939 = 11011409) B11011409
theorem B1902311 : Blo 562809 1902311 := bstep (se 1 (by rfl) ⟨1426733, by rfl⟩ : syracuseStep 1902311 = 2853467) B2853467
theorem B27526985 : Blo 562809 27526985 := bstep (se 2 (by rfl) ⟨10322619, by rfl⟩ : syracuseStep 27526985 = 20645239) B20645239
theorem B3213593 : Blo 562809 3213593 := bstep (se 2 (by rfl) ⟨1205097, by rfl⟩ : syracuseStep 3213593 = 2410195) B2410195
theorem B1018727 : Blo 562809 1018727 := bstep (se 1 (by rfl) ⟨764045, by rfl⟩ : syracuseStep 1018727 = 1528091) B1528091
theorem B1904687 : Blo 562809 1904687 := bstep (se 1 (by rfl) ⟨1428515, by rfl⟩ : syracuseStep 1904687 = 2857031) B2857031
theorem B1609951 : Blo 562809 1609951 := bstep (se 1 (by rfl) ⟨1207463, by rfl⟩ : syracuseStep 1609951 = 2414927) B2414927
theorem B2855249 : Blo 562809 2855249 := bstep (se 2 (by rfl) ⟨1070718, by rfl⟩ : syracuseStep 2855249 = 2141437) B2141437
theorem B149066087 : Blo 562809 149066087 := bstep (se 1 (by rfl) ⟨111799565, by rfl⟩ : syracuseStep 149066087 = 223599131) B223599131
theorem B1905065 : Blo 562809 1905065 := bstep (se 2 (by rfl) ⟨714399, by rfl⟩ : syracuseStep 1905065 = 1428799) B1428799
theorem B2888131 : Blo 562809 2888131 := bstep (se 1 (by rfl) ⟨2166098, by rfl⟩ : syracuseStep 2888131 = 4332197) B4332197
theorem B857179 : Blo 562809 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B2856221 : Blo 562809 2856221 := bstep (se 3 (by rfl) ⟨535541, by rfl⟩ : syracuseStep 2856221 = 1071083) B1071083
theorem B562879 : Blo 562809 562879 := bstep (se 1 (by rfl) ⟨422159, by rfl⟩ : syracuseStep 562879 = 844319) B844319
theorem B563111 : Blo 562809 563111 := bstep (se 1 (by rfl) ⟨422333, by rfl⟩ : syracuseStep 563111 = 844667) B844667
theorem B4298669 : Blo 562809 4298669 := bstep (se 3 (by rfl) ⟨806000, by rfl⟩ : syracuseStep 4298669 = 1612001) B1612001
theorem B563451 : Blo 562809 563451 := bstep (se 1 (by rfl) ⟨422588, by rfl⟩ : syracuseStep 563451 = 845177) B845177
theorem B1284601 : Blo 562809 1284601 := bstep (se 2 (by rfl) ⟨481725, by rfl⟩ : syracuseStep 1284601 = 963451) B963451
theorem B563711 : Blo 562809 563711 := bstep (se 1 (by rfl) ⟨422783, by rfl⟩ : syracuseStep 563711 = 845567) B845567
theorem B3217967 : Blo 562809 3217967 := bstep (se 1 (by rfl) ⟨2413475, by rfl⟩ : syracuseStep 3217967 = 4826951) B4826951
theorem B564095 : Blo 562809 564095 := bstep (se 1 (by rfl) ⟨423071, by rfl⟩ : syracuseStep 564095 = 846143) B846143
theorem B3218399 : Blo 562809 3218399 := bstep (se 1 (by rfl) ⟨2413799, by rfl⟩ : syracuseStep 3218399 = 4827599) B4827599
theorem B6429779 : Blo 562809 6429779 := bstep (se 1 (by rfl) ⟨4822334, by rfl⟩ : syracuseStep 6429779 = 9644669) B9644669
theorem B564507 : Blo 562809 564507 := bstep (se 1 (by rfl) ⟨423380, by rfl⟩ : syracuseStep 564507 = 846761) B846761
theorem B3218899 : Blo 562809 3218899 := bstep (se 1 (by rfl) ⟨2414174, by rfl⟩ : syracuseStep 3218899 = 4828349) B4828349
theorem B10853945 : Blo 562809 10853945 := bstep (se 2 (by rfl) ⟨4070229, by rfl⟩ : syracuseStep 10853945 = 8140459) B8140459
theorem B565279 : Blo 562809 565279 := bstep (se 1 (by rfl) ⟨423959, by rfl⟩ : syracuseStep 565279 = 847919) B847919
theorem B565407 : Blo 562809 565407 := bstep (se 1 (by rfl) ⟨424055, by rfl⟩ : syracuseStep 565407 = 848111) B848111
theorem B565743 : Blo 562809 565743 := bstep (se 1 (by rfl) ⟨424307, by rfl⟩ : syracuseStep 565743 = 848615) B848615
theorem B3056287 : Blo 562809 3056287 := bstep (se 1 (by rfl) ⟨2292215, by rfl⟩ : syracuseStep 3056287 = 4584431) B4584431
theorem B566119 : Blo 562809 566119 := bstep (se 1 (by rfl) ⟨424589, by rfl⟩ : syracuseStep 566119 = 849179) B849179
theorem B2139007 : Blo 562809 2139007 := bstep (se 1 (by rfl) ⟨1604255, by rfl⟩ : syracuseStep 2139007 = 3208511) B3208511
theorem B1910087 : Blo 562809 1910087 := bstep (se 1 (by rfl) ⟨1432565, by rfl⟩ : syracuseStep 1910087 = 2865131) B2865131
theorem B41723353 : Blo 562809 41723353 := bstep (se 2 (by rfl) ⟨15646257, by rfl⟩ : syracuseStep 41723353 = 31292515) B31292515
theorem B5777573 : Blo 562809 5777573 := bstep (se 4 (by rfl) ⟨541647, by rfl⟩ : syracuseStep 5777573 = 1083295) B1083295
theorem B2140937 : Blo 562809 2140937 := bstep (se 2 (by rfl) ⟨802851, by rfl⟩ : syracuseStep 2140937 = 1605703) B1605703
theorem B9153485 : Blo 562809 9153485 := bstep (se 3 (by rfl) ⟨1716278, by rfl⟩ : syracuseStep 9153485 = 3432557) B3432557
theorem B132099173 : Blo 562809 132099173 := bstep (se 4 (by rfl) ⟨12384297, by rfl⟩ : syracuseStep 132099173 = 24768595) B24768595
theorem B6434153 : Blo 562809 6434153 := bstep (se 2 (by rfl) ⟨2412807, by rfl⟩ : syracuseStep 6434153 = 4825615) B4825615
theorem B125710051 : Blo 562809 125710051 := bstep (se 1 (by rfl) ⟨94282538, by rfl⟩ : syracuseStep 125710051 = 188565077) B188565077
theorem B5157083 : Blo 562809 5157083 := bstep (se 1 (by rfl) ⟨3867812, by rfl⟩ : syracuseStep 5157083 = 7735625) B7735625
theorem B636187 : Blo 562809 636187 := bstep (se 1 (by rfl) ⟨477140, by rfl⟩ : syracuseStep 636187 = 954281) B954281
theorem B637087 : Blo 562809 637087 := bstep (se 1 (by rfl) ⟨477815, by rfl⟩ : syracuseStep 637087 = 955631) B955631
theorem B2407819 : Blo 562809 2407819 := bstep (se 1 (by rfl) ⟨1805864, by rfl⟩ : syracuseStep 2407819 = 3611729) B3611729
theorem B11026367 : Blo 562809 11026367 := bstep (se 1 (by rfl) ⟨8269775, by rfl⟩ : syracuseStep 11026367 = 16539551) B16539551
theorem B1098281 : Blo 562809 1098281 := bstep (se 2 (by rfl) ⟨411855, by rfl⟩ : syracuseStep 1098281 = 823711) B823711
theorem B1721303 : Blo 562809 1721303 := bstep (se 1 (by rfl) ⟨1290977, by rfl⟩ : syracuseStep 1721303 = 2581955) B2581955
theorem B9390431 : Blo 562809 9390431 := bstep (se 1 (by rfl) ⟨7042823, by rfl⟩ : syracuseStep 9390431 = 14085647) B14085647
theorem B20662775 : Blo 562809 20662775 := bstep (se 1 (by rfl) ⟨15497081, by rfl⟩ : syracuseStep 20662775 = 30994163) B30994163
theorem B55757429 : Blo 562809 55757429 := bstep (se 5 (by rfl) ⟨2613629, by rfl⟩ : syracuseStep 55757429 = 5227259) B5227259
theorem B23252183 : Blo 562809 23252183 := bstep (se 1 (by rfl) ⟨17439137, by rfl⟩ : syracuseStep 23252183 = 34878275) B34878275
theorem B4837097 : Blo 562809 4837097 := bstep (se 2 (by rfl) ⟨1813911, by rfl⟩ : syracuseStep 4837097 = 3627823) B3627823
theorem B610151 : Blo 562809 610151 := bstep (se 1 (by rfl) ⟨457613, by rfl⟩ : syracuseStep 610151 = 915227) B915227
theorem B3855113 : Blo 562809 3855113 := bstep (se 2 (by rfl) ⟨1445667, by rfl⟩ : syracuseStep 3855113 = 2891335) B2891335
theorem B1267577 : Blo 562809 1267577 := bstep (se 2 (by rfl) ⟨475341, by rfl⟩ : syracuseStep 1267577 = 950683) B950683
theorem B1267667 : Blo 562809 1267667 := bstep (se 1 (by rfl) ⟨950750, by rfl⟩ : syracuseStep 1267667 = 1901501) B1901501
theorem B1267937 : Blo 562809 1267937 := bstep (se 2 (by rfl) ⟨475476, by rfl⟩ : syracuseStep 1267937 = 950953) B950953
theorem B1071721 : Blo 562809 1071721 := bstep (se 2 (by rfl) ⟨401895, by rfl⟩ : syracuseStep 1071721 = 803791) B803791
theorem B5889131 : Blo 562809 5889131 := bstep (se 1 (by rfl) ⟨4416848, by rfl⟩ : syracuseStep 5889131 = 8833697) B8833697
theorem B1432687 : Blo 562809 1432687 := bstep (se 1 (by rfl) ⟨1074515, by rfl⟩ : syracuseStep 1432687 = 2149031) B2149031
theorem B2415851 : Blo 562809 2415851 := bstep (se 1 (by rfl) ⟨1811888, by rfl⟩ : syracuseStep 2415851 = 3623777) B3623777
theorem B1269503 : Blo 562809 1269503 := bstep (se 1 (by rfl) ⟨952127, by rfl⟩ : syracuseStep 1269503 = 1904255) B1904255
theorem B712795 : Blo 562809 712795 := bstep (se 1 (by rfl) ⟨534596, by rfl⟩ : syracuseStep 712795 = 1069193) B1069193
theorem B1269863 : Blo 562809 1269863 := bstep (se 1 (by rfl) ⟨952397, by rfl⟩ : syracuseStep 1269863 = 1904795) B1904795
theorem B4809455 : Blo 562809 4809455 := bstep (se 1 (by rfl) ⟨3607091, by rfl⟩ : syracuseStep 4809455 = 7214183) B7214183
theorem B844751 : Blo 562809 844751 := bstep (se 1 (by rfl) ⟨633563, by rfl⟩ : syracuseStep 844751 = 1267127) B1267127
theorem B2745359 : Blo 562809 2745359 := bstep (se 1 (by rfl) ⟨2059019, by rfl⟩ : syracuseStep 2745359 = 4118039) B4118039
theorem B844937 : Blo 562809 844937 := bstep (se 2 (by rfl) ⟨316851, by rfl⟩ : syracuseStep 844937 = 633703) B633703
theorem B845183 : Blo 562809 845183 := bstep (se 1 (by rfl) ⟨633887, by rfl⟩ : syracuseStep 845183 = 1267775) B1267775
theorem B1141055 : Blo 562809 1141055 := bstep (se 1 (by rfl) ⟨855791, by rfl⟩ : syracuseStep 1141055 = 1711583) B1711583
theorem B847343 : Blo 562809 847343 := bstep (se 1 (by rfl) ⟨635507, by rfl⟩ : syracuseStep 847343 = 1271015) B1271015
theorem B716779 : Blo 562809 716779 := bstep (se 1 (by rfl) ⟨537584, by rfl⟩ : syracuseStep 716779 = 1075169) B1075169
theorem B848351 : Blo 562809 848351 := bstep (se 1 (by rfl) ⟨636263, by rfl⟩ : syracuseStep 848351 = 1272527) B1272527
theorem B848543 : Blo 562809 848543 := bstep (se 1 (by rfl) ⟨636407, by rfl⟩ : syracuseStep 848543 = 1272815) B1272815
theorem B169997105 : Blo 562809 169997105 := bstep (se 2 (by rfl) ⟨63748914, by rfl⟩ : syracuseStep 169997105 = 127497829) B127497829
theorem B1274849 : Blo 562809 1274849 := bstep (se 2 (by rfl) ⟨478068, by rfl⟩ : syracuseStep 1274849 = 956137) B956137
theorem B2291179 : Blo 562809 2291179 := bstep (se 1 (by rfl) ⟨1718384, by rfl⟩ : syracuseStep 2291179 = 3436769) B3436769
theorem B6518717 : Blo 562809 6518717 := bstep (se 3 (by rfl) ⟨1222259, by rfl⟩ : syracuseStep 6518717 = 2444519) B2444519
theorem B950393 : Blo 562809 950393 := bstep (se 2 (by rfl) ⟨356397, by rfl⟩ : syracuseStep 950393 = 712795) B712795
theorem B1147535 : Blo 562809 1147535 := bstep (se 1 (by rfl) ⟨860651, by rfl⟩ : syracuseStep 1147535 = 1721303) B1721303
theorem B397509565 : Blo 562809 397509565 := bstep (se 3 (by rfl) ⟨74533043, by rfl⟩ : syracuseStep 397509565 = 149066087) B149066087
theorem B2852009 : Blo 562809 2852009 := bstep (se 2 (by rfl) ⟨1069503, by rfl⟩ : syracuseStep 2852009 = 2139007) B2139007
theorem B18351323 : Blo 562809 18351323 := bstep (se 1 (by rfl) ⟨13763492, by rfl⟩ : syracuseStep 18351323 = 27526985) B27526985
theorem B6260287 : Blo 562809 6260287 := bstep (se 1 (by rfl) ⟨4695215, by rfl⟩ : syracuseStep 6260287 = 9390431) B9390431
theorem B15501455 : Blo 562809 15501455 := bstep (se 1 (by rfl) ⟨11626091, by rfl⟩ : syracuseStep 15501455 = 23252183) B23252183
theorem B1903499 : Blo 562809 1903499 := bstep (se 1 (by rfl) ⟨1427624, by rfl⟩ : syracuseStep 1903499 = 2855249) B2855249
theorem B1904147 : Blo 562809 1904147 := bstep (se 1 (by rfl) ⟨1428110, by rfl⟩ : syracuseStep 1904147 = 2856221) B2856221
theorem B1610567 : Blo 562809 1610567 := bstep (se 1 (by rfl) ⟨1207925, by rfl⟩ : syracuseStep 1610567 = 2415851) B2415851
theorem B167613401 : Blo 562809 167613401 := bstep (se 2 (by rfl) ⟨62855025, by rfl⟩ : syracuseStep 167613401 = 125710051) B125710051
theorem B955705 : Blo 562809 955705 := bstep (se 2 (by rfl) ⟨358389, by rfl⟩ : syracuseStep 955705 = 716779) B716779
theorem B15406861 : Blo 562809 15406861 := bstep (se 3 (by rfl) ⟨2888786, by rfl⟩ : syracuseStep 15406861 = 5777573) B5777573
theorem B563167 : Blo 562809 563167 := bstep (se 1 (by rfl) ⟨422375, by rfl⟩ : syracuseStep 563167 = 844751) B844751
theorem B563291 : Blo 562809 563291 := bstep (se 1 (by rfl) ⟨422468, by rfl⟩ : syracuseStep 563291 = 844937) B844937
theorem B563455 : Blo 562809 563455 := bstep (se 1 (by rfl) ⟨422591, by rfl⟩ : syracuseStep 563455 = 845183) B845183
theorem B760703 : Blo 562809 760703 := bstep (se 1 (by rfl) ⟨570527, by rfl⟩ : syracuseStep 760703 = 1141055) B1141055
theorem B6102323 : Blo 562809 6102323 := bstep (se 1 (by rfl) ⟨4576742, by rfl⟩ : syracuseStep 6102323 = 9153485) B9153485
theorem B3054905 : Blo 562809 3054905 := bstep (se 2 (by rfl) ⟨1145589, by rfl⟩ : syracuseStep 3054905 = 2291179) B2291179
theorem B564895 : Blo 562809 564895 := bstep (se 1 (by rfl) ⟨423671, by rfl⟩ : syracuseStep 564895 = 847343) B847343
theorem B565567 : Blo 562809 565567 := bstep (se 1 (by rfl) ⟨424175, by rfl⟩ : syracuseStep 565567 = 848351) B848351
theorem B565695 : Blo 562809 565695 := bstep (se 1 (by rfl) ⟨424271, by rfl⟩ : syracuseStep 565695 = 848543) B848543
theorem B1712801 : Blo 562809 1712801 := bstep (se 2 (by rfl) ⟨642300, by rfl⟩ : syracuseStep 1712801 = 1284601) B1284601
theorem B1910249 : Blo 562809 1910249 := bstep (se 2 (by rfl) ⟨716343, by rfl⟩ : syracuseStep 1910249 = 1432687) B1432687
theorem B7350911 : Blo 562809 7350911 := bstep (se 1 (by rfl) ⟨5513183, by rfl⟩ : syracuseStep 7350911 = 11026367) B11026367
theorem B732187 : Blo 562809 732187 := bstep (se 1 (by rfl) ⟨549140, by rfl⟩ : syracuseStep 732187 = 1098281) B1098281
theorem B4893959 : Blo 562809 4893959 := bstep (se 1 (by rfl) ⟨3670469, by rfl⟩ : syracuseStep 4893959 = 7340939) B7340939
theorem B4075049 : Blo 562809 4075049 := bstep (se 2 (by rfl) ⟨1528143, by rfl⟩ : syracuseStep 4075049 = 3056287) B3056287
theorem B2142395 : Blo 562809 2142395 := bstep (se 1 (by rfl) ⟨1606796, by rfl⟩ : syracuseStep 2142395 = 3213593) B3213593
theorem B13775183 : Blo 562809 13775183 := bstep (se 1 (by rfl) ⟨10331387, by rfl⟩ : syracuseStep 13775183 = 20662775) B20662775
theorem B37171619 : Blo 562809 37171619 := bstep (se 1 (by rfl) ⟨27878714, by rfl⟩ : syracuseStep 37171619 = 55757429) B55757429
theorem B3224731 : Blo 562809 3224731 := bstep (se 1 (by rfl) ⟨2418548, by rfl⟩ : syracuseStep 3224731 = 4837097) B4837097
theorem B2570075 : Blo 562809 2570075 := bstep (se 1 (by rfl) ⟨1927556, by rfl⟩ : syracuseStep 2570075 = 3855113) B3855113
theorem B2865779 : Blo 562809 2865779 := bstep (se 1 (by rfl) ⟨2149334, by rfl⟩ : syracuseStep 2865779 = 4298669) B4298669
theorem B2145311 : Blo 562809 2145311 := bstep (se 1 (by rfl) ⟨1608983, by rfl⟩ : syracuseStep 2145311 = 3217967) B3217967
theorem B2145599 : Blo 562809 2145599 := bstep (se 1 (by rfl) ⟨1609199, by rfl⟩ : syracuseStep 2145599 = 3218399) B3218399
theorem B2146601 : Blo 562809 2146601 := bstep (se 2 (by rfl) ⟨804975, by rfl⟩ : syracuseStep 2146601 = 1609951) B1609951
theorem B3850841 : Blo 562809 3850841 := bstep (se 2 (by rfl) ⟨1444065, by rfl⟩ : syracuseStep 3850841 = 2888131) B2888131
theorem B1427291 : Blo 562809 1427291 := bstep (se 1 (by rfl) ⟨1070468, by rfl⟩ : syracuseStep 1427291 = 2140937) B2140937
theorem B88066115 : Blo 562809 88066115 := bstep (se 1 (by rfl) ⟨66049586, by rfl⟩ : syracuseStep 88066115 = 132099173) B132099173
theorem B113331403 : Blo 562809 113331403 := bstep (se 1 (by rfl) ⟨84998552, by rfl⟩ : syracuseStep 113331403 = 169997105) B169997105
theorem B1428961 : Blo 562809 1428961 := bstep (se 2 (by rfl) ⟨535860, by rfl⟩ : syracuseStep 1428961 = 1071721) B1071721
theorem B4345811 : Blo 562809 4345811 := bstep (se 1 (by rfl) ⟨3259358, by rfl⟩ : syracuseStep 4345811 = 6518717) B6518717
theorem B1627069 : Blo 562809 1627069 := bstep (se 3 (by rfl) ⟨305075, by rfl⟩ : syracuseStep 1627069 = 610151) B610151
theorem B1268207 : Blo 562809 1268207 := bstep (se 1 (by rfl) ⟨951155, by rfl⟩ : syracuseStep 1268207 = 1902311) B1902311
theorem B679151 : Blo 562809 679151 := bstep (se 1 (by rfl) ⟨509363, by rfl⟩ : syracuseStep 679151 = 1018727) B1018727
theorem B55631137 : Blo 562809 55631137 := bstep (se 2 (by rfl) ⟨20861676, by rfl⟩ : syracuseStep 55631137 = 41723353) B41723353
theorem B1269791 : Blo 562809 1269791 := bstep (se 1 (by rfl) ⟨952343, by rfl⟩ : syracuseStep 1269791 = 1904687) B1904687
theorem B1270043 : Blo 562809 1270043 := bstep (se 1 (by rfl) ⟨952532, by rfl⟩ : syracuseStep 1270043 = 1905065) B1905065
theorem B845051 : Blo 562809 845051 := bstep (se 1 (by rfl) ⟨633788, by rfl⟩ : syracuseStep 845051 = 1267577) B1267577
theorem B845111 : Blo 562809 845111 := bstep (se 1 (by rfl) ⟨633833, by rfl⟩ : syracuseStep 845111 = 1267667) B1267667
theorem B845291 : Blo 562809 845291 := bstep (se 1 (by rfl) ⟨633968, by rfl⟩ : syracuseStep 845291 = 1267937) B1267937
theorem B4286519 : Blo 562809 4286519 := bstep (se 1 (by rfl) ⟨3214889, by rfl⟩ : syracuseStep 4286519 = 6429779) B6429779
theorem B3926087 : Blo 562809 3926087 := bstep (se 1 (by rfl) ⟨2944565, by rfl⟩ : syracuseStep 3926087 = 5889131) B5889131
theorem B7235963 : Blo 562809 7235963 := bstep (se 1 (by rfl) ⟨5426972, by rfl⟩ : syracuseStep 7235963 = 10853945) B10853945
theorem B846335 : Blo 562809 846335 := bstep (se 1 (by rfl) ⟨634751, by rfl⟩ : syracuseStep 846335 = 1269503) B1269503
theorem B846575 : Blo 562809 846575 := bstep (se 1 (by rfl) ⟨634931, by rfl⟩ : syracuseStep 846575 = 1269863) B1269863
theorem B3206303 : Blo 562809 3206303 := bstep (se 1 (by rfl) ⟨2404727, by rfl⟩ : syracuseStep 3206303 = 4809455) B4809455
theorem B1830239 : Blo 562809 1830239 := bstep (se 1 (by rfl) ⟨1372679, by rfl⟩ : syracuseStep 1830239 = 2745359) B2745359
theorem B1273391 : Blo 562809 1273391 := bstep (se 1 (by rfl) ⟨955043, by rfl⟩ : syracuseStep 1273391 = 1910087) B1910087
theorem B1142905 : Blo 562809 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B848249 : Blo 562809 848249 := bstep (se 2 (by rfl) ⟨318093, by rfl⟩ : syracuseStep 848249 = 636187) B636187
theorem B4289435 : Blo 562809 4289435 := bstep (se 1 (by rfl) ⟨3217076, by rfl⟩ : syracuseStep 4289435 = 6434153) B6434153
theorem B3438055 : Blo 562809 3438055 := bstep (se 1 (by rfl) ⟨2578541, by rfl⟩ : syracuseStep 3438055 = 5157083) B5157083
theorem B849449 : Blo 562809 849449 := bstep (se 2 (by rfl) ⟨318543, by rfl⟩ : syracuseStep 849449 = 637087) B637087
theorem B849899 : Blo 562809 849899 := bstep (se 1 (by rfl) ⟨637424, by rfl⟩ : syracuseStep 849899 = 1274849) B1274849
theorem B3210425 : Blo 562809 3210425 := bstep (se 2 (by rfl) ⟨1203909, by rfl⟩ : syracuseStep 3210425 = 2407819) B2407819
theorem B4291865 : Blo 562809 4291865 := bstep (se 2 (by rfl) ⟨1609449, by rfl⟩ : syracuseStep 4291865 = 3218899) B3218899
theorem B1901339 : Blo 562809 1901339 := bstep (se 1 (by rfl) ⟨1426004, by rfl⟩ : syracuseStep 1901339 = 2852009) B2852009
theorem B951527 : Blo 562809 951527 := bstep (se 1 (by rfl) ⟨713645, by rfl⟩ : syracuseStep 951527 = 1427291) B1427291
theorem B111742267 : Blo 562809 111742267 := bstep (se 1 (by rfl) ⟨83806700, by rfl⟩ : syracuseStep 111742267 = 167613401) B167613401
theorem B1905281 : Blo 562809 1905281 := bstep (se 2 (by rfl) ⟨714480, by rfl⟩ : syracuseStep 1905281 = 1428961) B1428961
theorem B4068215 : Blo 562809 4068215 := bstep (se 1 (by rfl) ⟨3051161, by rfl⟩ : syracuseStep 4068215 = 6102323) B6102323
theorem B2036603 : Blo 562809 2036603 := bstep (se 1 (by rfl) ⟨1527452, by rfl⟩ : syracuseStep 2036603 = 3054905) B3054905
theorem B563367 : Blo 562809 563367 := bstep (se 1 (by rfl) ⟨422525, by rfl⟩ : syracuseStep 563367 = 845051) B845051
theorem B563407 : Blo 562809 563407 := bstep (se 1 (by rfl) ⟨422555, by rfl⟩ : syracuseStep 563407 = 845111) B845111
theorem B563527 : Blo 562809 563527 := bstep (se 1 (by rfl) ⟨422645, by rfl⟩ : syracuseStep 563527 = 845291) B845291
theorem B2169425 : Blo 562809 2169425 := bstep (se 2 (by rfl) ⟨813534, by rfl⟩ : syracuseStep 2169425 = 1627069) B1627069
theorem B2857679 : Blo 562809 2857679 := bstep (se 1 (by rfl) ⟨2143259, by rfl⟩ : syracuseStep 2857679 = 4286519) B4286519
theorem B4299641 : Blo 562809 4299641 := bstep (se 2 (by rfl) ⟨1612365, by rfl⟩ : syracuseStep 4299641 = 3224731) B3224731
theorem B4823975 : Blo 562809 4823975 := bstep (se 1 (by rfl) ⟨3617981, by rfl⟩ : syracuseStep 4823975 = 7235963) B7235963
theorem B564223 : Blo 562809 564223 := bstep (se 1 (by rfl) ⟨423167, by rfl⟩ : syracuseStep 564223 = 846335) B846335
theorem B564383 : Blo 562809 564383 := bstep (se 1 (by rfl) ⟨423287, by rfl⟩ : syracuseStep 564383 = 846575) B846575
theorem B2137535 : Blo 562809 2137535 := bstep (se 1 (by rfl) ⟨1603151, by rfl⟩ : syracuseStep 2137535 = 3206303) B3206303
theorem B1220159 : Blo 562809 1220159 := bstep (se 1 (by rfl) ⟨915119, by rfl⟩ : syracuseStep 1220159 = 1830239) B1830239
theorem B9183455 : Blo 562809 9183455 := bstep (se 1 (by rfl) ⟨6887591, by rfl⟩ : syracuseStep 9183455 = 13775183) B13775183
theorem B565499 : Blo 562809 565499 := bstep (se 1 (by rfl) ⟨424124, by rfl⟩ : syracuseStep 565499 = 848249) B848249
theorem B24781079 : Blo 562809 24781079 := bstep (se 1 (by rfl) ⟨18585809, by rfl⟩ : syracuseStep 24781079 = 37171619) B37171619
theorem B2859623 : Blo 562809 2859623 := bstep (se 1 (by rfl) ⟨2144717, by rfl⟩ : syracuseStep 2859623 = 4289435) B4289435
theorem B1811069 : Blo 562809 1811069 := bstep (se 3 (by rfl) ⟨339575, by rfl⟩ : syracuseStep 1811069 = 679151) B679151
theorem B566299 : Blo 562809 566299 := bstep (se 1 (by rfl) ⟨424724, by rfl⟩ : syracuseStep 566299 = 849449) B849449
theorem B1713383 : Blo 562809 1713383 := bstep (se 1 (by rfl) ⟨1285037, by rfl⟩ : syracuseStep 1713383 = 2570075) B2570075
theorem B566599 : Blo 562809 566599 := bstep (se 1 (by rfl) ⟨424949, by rfl⟩ : syracuseStep 566599 = 849899) B849899
theorem B1910519 : Blo 562809 1910519 := bstep (se 1 (by rfl) ⟨1432889, by rfl⟩ : syracuseStep 1910519 = 2865779) B2865779
theorem B2140283 : Blo 562809 2140283 := bstep (se 1 (by rfl) ⟨1605212, by rfl⟩ : syracuseStep 2140283 = 3210425) B3210425
theorem B2861243 : Blo 562809 2861243 := bstep (se 1 (by rfl) ⟨2145932, by rfl⟩ : syracuseStep 2861243 = 4291865) B4291865
theorem B633595 : Blo 562809 633595 := bstep (se 1 (by rfl) ⟨475196, by rfl⟩ : syracuseStep 633595 = 950393) B950393
theorem B2567227 : Blo 562809 2567227 := bstep (se 1 (by rfl) ⟨1925420, by rfl⟩ : syracuseStep 2567227 = 3850841) B3850841
theorem B765023 : Blo 562809 765023 := bstep (se 1 (by rfl) ⟨573767, by rfl⟩ : syracuseStep 765023 = 1147535) B1147535
theorem B12234215 : Blo 562809 12234215 := bstep (se 1 (by rfl) ⟨9175661, by rfl⟩ : syracuseStep 12234215 = 18351323) B18351323
theorem B10334303 : Blo 562809 10334303 := bstep (se 1 (by rfl) ⟨7750727, by rfl⟩ : syracuseStep 10334303 = 15501455) B15501455
theorem B2897207 : Blo 562809 2897207 := bstep (se 1 (by rfl) ⟨2172905, by rfl⟩ : syracuseStep 2897207 = 4345811) B4345811
theorem B151108537 : Blo 562809 151108537 := bstep (se 2 (by rfl) ⟨56665701, by rfl⟩ : syracuseStep 151108537 = 113331403) B113331403
theorem B1523873 : Blo 562809 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B4900607 : Blo 562809 4900607 := bstep (se 1 (by rfl) ⟨3675455, by rfl⟩ : syracuseStep 4900607 = 7350911) B7350911
theorem B3262639 : Blo 562809 3262639 := bstep (se 1 (by rfl) ⟨2446979, by rfl⟩ : syracuseStep 3262639 = 4893959) B4893959
theorem B1428263 : Blo 562809 1428263 := bstep (se 1 (by rfl) ⟨1071197, by rfl⟩ : syracuseStep 1428263 = 2142395) B2142395
theorem B8114165 : Blo 562809 8114165 := bstep (se 5 (by rfl) ⟨380351, by rfl⟩ : syracuseStep 8114165 = 760703) B760703
theorem B74174849 : Blo 562809 74174849 := bstep (se 2 (by rfl) ⟨27815568, by rfl⟩ : syracuseStep 74174849 = 55631137) B55631137
theorem B1430207 : Blo 562809 1430207 := bstep (se 1 (by rfl) ⟨1072655, by rfl⟩ : syracuseStep 1430207 = 2145311) B2145311
theorem B1430399 : Blo 562809 1430399 := bstep (se 1 (by rfl) ⟨1072799, by rfl⟩ : syracuseStep 1430399 = 2145599) B2145599
theorem B1431067 : Blo 562809 1431067 := bstep (se 1 (by rfl) ⟨1073300, by rfl⟩ : syracuseStep 1431067 = 2146601) B2146601
theorem B530012753 : Blo 562809 530012753 := bstep (se 2 (by rfl) ⟨198754782, by rfl⟩ : syracuseStep 530012753 = 397509565) B397509565
theorem B58710743 : Blo 562809 58710743 := bstep (se 1 (by rfl) ⟨44033057, by rfl⟩ : syracuseStep 58710743 = 88066115) B88066115
theorem B1268999 : Blo 562809 1268999 := bstep (se 1 (by rfl) ⟨951749, by rfl⟩ : syracuseStep 1268999 = 1903499) B1903499
theorem B8347049 : Blo 562809 8347049 := bstep (se 2 (by rfl) ⟨3130143, by rfl⟩ : syracuseStep 8347049 = 6260287) B6260287
theorem B1269431 : Blo 562809 1269431 := bstep (se 1 (by rfl) ⟨952073, by rfl⟩ : syracuseStep 1269431 = 1904147) B1904147
theorem B1073711 : Blo 562809 1073711 := bstep (se 1 (by rfl) ⟨805283, by rfl⟩ : syracuseStep 1073711 = 1610567) B1610567
theorem B976249 : Blo 562809 976249 := bstep (se 2 (by rfl) ⟨366093, by rfl⟩ : syracuseStep 976249 = 732187) B732187
theorem B845471 : Blo 562809 845471 := bstep (se 1 (by rfl) ⟨634103, by rfl⟩ : syracuseStep 845471 = 1268207) B1268207
theorem B846527 : Blo 562809 846527 := bstep (se 1 (by rfl) ⟨634895, by rfl⟩ : syracuseStep 846527 = 1269791) B1269791
theorem B846695 : Blo 562809 846695 := bstep (se 1 (by rfl) ⟨635021, by rfl⟩ : syracuseStep 846695 = 1270043) B1270043
theorem B1141867 : Blo 562809 1141867 := bstep (se 1 (by rfl) ⟨856400, by rfl⟩ : syracuseStep 1141867 = 1712801) B1712801
theorem B1273499 : Blo 562809 1273499 := bstep (se 1 (by rfl) ⟨955124, by rfl⟩ : syracuseStep 1273499 = 1910249) B1910249
theorem B2617391 : Blo 562809 2617391 := bstep (se 1 (by rfl) ⟨1963043, by rfl⟩ : syracuseStep 2617391 = 3926087) B3926087
theorem B1274273 : Blo 562809 1274273 := bstep (se 2 (by rfl) ⟨477852, by rfl⟩ : syracuseStep 1274273 = 955705) B955705
theorem B4584073 : Blo 562809 4584073 := bstep (se 2 (by rfl) ⟨1719027, by rfl⟩ : syracuseStep 4584073 = 3438055) B3438055
theorem B20542481 : Blo 562809 20542481 := bstep (se 2 (by rfl) ⟨7703430, by rfl⟩ : syracuseStep 20542481 = 15406861) B15406861
theorem B2716699 : Blo 562809 2716699 := bstep (se 1 (by rfl) ⟨2037524, by rfl⟩ : syracuseStep 2716699 = 4075049) B4075049
theorem B848927 : Blo 562809 848927 := bstep (se 1 (by rfl) ⟨636695, by rfl⟩ : syracuseStep 848927 = 1273391) B1273391
theorem B1015915 : Blo 562809 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B6979709 : Blo 562809 6979709 := bstep (se 3 (by rfl) ⟨1308695, by rfl⟩ : syracuseStep 6979709 = 2617391) B2617391
theorem B952175 : Blo 562809 952175 := bstep (se 1 (by rfl) ⟨714131, by rfl⟩ : syracuseStep 952175 = 1428263) B1428263
theorem B5409443 : Blo 562809 5409443 := bstep (se 1 (by rfl) ⟨4057082, by rfl⟩ : syracuseStep 5409443 = 8114165) B8114165
theorem B49449899 : Blo 562809 49449899 := bstep (se 1 (by rfl) ⟨37087424, by rfl⟩ : syracuseStep 49449899 = 74174849) B74174849
theorem B953471 : Blo 562809 953471 := bstep (se 1 (by rfl) ⟨715103, by rfl⟩ : syracuseStep 953471 = 1430207) B1430207
theorem B953599 : Blo 562809 953599 := bstep (se 1 (by rfl) ⟨715199, by rfl⟩ : syracuseStep 953599 = 1430399) B1430399
theorem B1446283 : Blo 562809 1446283 := bstep (se 1 (by rfl) ⟨1084712, by rfl⟩ : syracuseStep 1446283 = 2169425) B2169425
theorem B353341835 : Blo 562809 353341835 := bstep (se 1 (by rfl) ⟨265006376, by rfl⟩ : syracuseStep 353341835 = 530012753) B530012753
theorem B1905119 : Blo 562809 1905119 := bstep (se 1 (by rfl) ⟨1428839, by rfl⟩ : syracuseStep 1905119 = 2857679) B2857679
theorem B3215983 : Blo 562809 3215983 := bstep (se 1 (by rfl) ⟨2411987, by rfl⟩ : syracuseStep 3215983 = 4823975) B4823975
theorem B16520719 : Blo 562809 16520719 := bstep (se 1 (by rfl) ⟨12390539, by rfl⟩ : syracuseStep 16520719 = 24781079) B24781079
theorem B1906415 : Blo 562809 1906415 := bstep (se 1 (by rfl) ⟨1429811, by rfl⟩ : syracuseStep 1906415 = 2859623) B2859623
theorem B563647 : Blo 562809 563647 := bstep (se 1 (by rfl) ⟨422735, by rfl⟩ : syracuseStep 563647 = 845471) B845471
theorem B1907495 : Blo 562809 1907495 := bstep (se 1 (by rfl) ⟨1430621, by rfl⟩ : syracuseStep 1907495 = 2861243) B2861243
theorem B564351 : Blo 562809 564351 := bstep (se 1 (by rfl) ⟨423263, by rfl⟩ : syracuseStep 564351 = 846527) B846527
theorem B564463 : Blo 562809 564463 := bstep (se 1 (by rfl) ⟨423347, by rfl⟩ : syracuseStep 564463 = 846695) B846695
theorem B1908089 : Blo 562809 1908089 := bstep (se 2 (by rfl) ⟨715533, by rfl⟩ : syracuseStep 1908089 = 1431067) B1431067
theorem B6889535 : Blo 562809 6889535 := bstep (se 1 (by rfl) ⟨5167151, by rfl⟩ : syracuseStep 6889535 = 10334303) B10334303
theorem B2040061 : Blo 562809 2040061 := bstep (se 3 (by rfl) ⟨382511, by rfl⟩ : syracuseStep 2040061 = 765023) B765023
theorem B565951 : Blo 562809 565951 := bstep (se 1 (by rfl) ⟨424463, by rfl⟩ : syracuseStep 565951 = 848927) B848927
theorem B634351 : Blo 562809 634351 := bstep (se 1 (by rfl) ⟨475763, by rfl⟩ : syracuseStep 634351 = 951527) B951527
theorem B1357735 : Blo 562809 1357735 := bstep (se 1 (by rfl) ⟨1018301, by rfl⟩ : syracuseStep 1357735 = 2036603) B2036603
theorem B3422969 : Blo 562809 3422969 := bstep (se 2 (by rfl) ⟨1283613, by rfl⟩ : syracuseStep 3422969 = 2567227) B2567227
theorem B1522489 : Blo 562809 1522489 := bstep (se 2 (by rfl) ⟨570933, by rfl⟩ : syracuseStep 1522489 = 1141867) B1141867
theorem B39140495 : Blo 562809 39140495 := bstep (se 1 (by rfl) ⟨29355371, by rfl⟩ : syracuseStep 39140495 = 58710743) B58710743
theorem B2866427 : Blo 562809 2866427 := bstep (se 1 (by rfl) ⟨2149820, by rfl⟩ : syracuseStep 2866427 = 4299641) B4299641
theorem B1425023 : Blo 562809 1425023 := bstep (se 1 (by rfl) ⟨1068767, by rfl⟩ : syracuseStep 1425023 = 2137535) B2137535
theorem B6112097 : Blo 562809 6112097 := bstep (se 2 (by rfl) ⟨2292036, by rfl⟩ : syracuseStep 6112097 = 4584073) B4584073
theorem B3622265 : Blo 562809 3622265 := bstep (se 2 (by rfl) ⟨1358349, by rfl⟩ : syracuseStep 3622265 = 2716699) B2716699
theorem B1426855 : Blo 562809 1426855 := bstep (se 1 (by rfl) ⟨1070141, by rfl⟩ : syracuseStep 1426855 = 2140283) B2140283
theorem B201478049 : Blo 562809 201478049 := bstep (se 2 (by rfl) ⟨75554268, by rfl⟩ : syracuseStep 201478049 = 151108537) B151108537
theorem B1267559 : Blo 562809 1267559 := bstep (se 1 (by rfl) ⟨950669, by rfl⟩ : syracuseStep 1267559 = 1901339) B1901339
theorem B3267071 : Blo 562809 3267071 := bstep (se 1 (by rfl) ⟨2450303, by rfl⟩ : syracuseStep 3267071 = 4900607) B4900607
theorem B1301665 : Blo 562809 1301665 := bstep (se 2 (by rfl) ⟨488124, by rfl⟩ : syracuseStep 1301665 = 976249) B976249
theorem B4350185 : Blo 562809 4350185 := bstep (se 2 (by rfl) ⟨1631319, by rfl⟩ : syracuseStep 4350185 = 3262639) B3262639
theorem B1270187 : Blo 562809 1270187 := bstep (se 1 (by rfl) ⟨952640, by rfl⟩ : syracuseStep 1270187 = 1905281) B1905281
theorem B2712143 : Blo 562809 2712143 := bstep (se 1 (by rfl) ⟨2034107, by rfl⟩ : syracuseStep 2712143 = 4068215) B4068215
theorem B844793 : Blo 562809 844793 := bstep (se 2 (by rfl) ⟨316797, by rfl⟩ : syracuseStep 844793 = 633595) B633595
theorem B148989689 : Blo 562809 148989689 := bstep (se 2 (by rfl) ⟨55871133, by rfl⟩ : syracuseStep 148989689 = 111742267) B111742267
theorem B845999 : Blo 562809 845999 := bstep (se 1 (by rfl) ⟨634499, by rfl⟩ : syracuseStep 845999 = 1268999) B1268999
theorem B5564699 : Blo 562809 5564699 := bstep (se 1 (by rfl) ⟨4173524, by rfl⟩ : syracuseStep 5564699 = 8347049) B8347049
theorem B813439 : Blo 562809 813439 := bstep (se 1 (by rfl) ⟨610079, by rfl⟩ : syracuseStep 813439 = 1220159) B1220159
theorem B846287 : Blo 562809 846287 := bstep (se 1 (by rfl) ⟨634715, by rfl⟩ : syracuseStep 846287 = 1269431) B1269431
theorem B6122303 : Blo 562809 6122303 := bstep (se 1 (by rfl) ⟨4591727, by rfl⟩ : syracuseStep 6122303 = 9183455) B9183455
theorem B715807 : Blo 562809 715807 := bstep (se 1 (by rfl) ⟨536855, by rfl⟩ : syracuseStep 715807 = 1073711) B1073711
theorem B1207379 : Blo 562809 1207379 := bstep (se 1 (by rfl) ⟨905534, by rfl⟩ : syracuseStep 1207379 = 1811069) B1811069
theorem B1142255 : Blo 562809 1142255 := bstep (se 1 (by rfl) ⟨856691, by rfl⟩ : syracuseStep 1142255 = 1713383) B1713383
theorem B1273679 : Blo 562809 1273679 := bstep (se 1 (by rfl) ⟨955259, by rfl⟩ : syracuseStep 1273679 = 1910519) B1910519
theorem B8156143 : Blo 562809 8156143 := bstep (se 1 (by rfl) ⟨6117107, by rfl⟩ : syracuseStep 8156143 = 12234215) B12234215
theorem B848999 : Blo 562809 848999 := bstep (se 1 (by rfl) ⟨636749, by rfl⟩ : syracuseStep 848999 = 1273499) B1273499
theorem B849515 : Blo 562809 849515 := bstep (se 1 (by rfl) ⟨637136, by rfl⟩ : syracuseStep 849515 = 1274273) B1274273
theorem B13694987 : Blo 562809 13694987 := bstep (se 1 (by rfl) ⟨10271240, by rfl⟩ : syracuseStep 13694987 = 20542481) B20542481
theorem B1931471 : Blo 562809 1931471 := bstep (se 1 (by rfl) ⟨1448603, by rfl⟩ : syracuseStep 1931471 = 2897207) B2897207
theorem B4653139 : Blo 562809 4653139 := bstep (se 1 (by rfl) ⟨3489854, by rfl⟩ : syracuseStep 4653139 = 6979709) B6979709
theorem B2720081 : Blo 562809 2720081 := bstep (se 2 (by rfl) ⟨1020030, by rfl⟩ : syracuseStep 2720081 = 2040061) B2040061
theorem B3606295 : Blo 562809 3606295 := bstep (se 1 (by rfl) ⟨2704721, by rfl⟩ : syracuseStep 3606295 = 5409443) B5409443
theorem B1902473 : Blo 562809 1902473 := bstep (se 2 (by rfl) ⟨713427, by rfl⟩ : syracuseStep 1902473 = 1426855) B1426855
theorem B32966599 : Blo 562809 32966599 := bstep (se 1 (by rfl) ⟨24724949, by rfl⟩ : syracuseStep 32966599 = 49449899) B49449899
theorem B134318699 : Blo 562809 134318699 := bstep (se 1 (by rfl) ⟨100739024, by rfl⟩ : syracuseStep 134318699 = 201478049) B201478049
theorem B1084585 : Blo 562809 1084585 := bstep (se 2 (by rfl) ⟨406719, by rfl⟩ : syracuseStep 1084585 = 813439) B813439
theorem B954409 : Blo 562809 954409 := bstep (se 2 (by rfl) ⟨357903, by rfl⟩ : syracuseStep 954409 = 715807) B715807
theorem B4593023 : Blo 562809 4593023 := bstep (se 1 (by rfl) ⟨3444767, by rfl⟩ : syracuseStep 4593023 = 6889535) B6889535
theorem B1808095 : Blo 562809 1808095 := bstep (se 1 (by rfl) ⟨1356071, by rfl⟩ : syracuseStep 1808095 = 2712143) B2712143
theorem B563195 : Blo 562809 563195 := bstep (se 1 (by rfl) ⟨422396, by rfl⟩ : syracuseStep 563195 = 844793) B844793
theorem B99326459 : Blo 562809 99326459 := bstep (se 1 (by rfl) ⟨74494844, by rfl⟩ : syracuseStep 99326459 = 148989689) B148989689
theorem B563999 : Blo 562809 563999 := bstep (se 1 (by rfl) ⟨422999, by rfl⟩ : syracuseStep 563999 = 845999) B845999
theorem B3709799 : Blo 562809 3709799 := bstep (se 1 (by rfl) ⟨2782349, by rfl⟩ : syracuseStep 3709799 = 5564699) B5564699
theorem B564191 : Blo 562809 564191 := bstep (se 1 (by rfl) ⟨423143, by rfl⟩ : syracuseStep 564191 = 846287) B846287
theorem B22027625 : Blo 562809 22027625 := bstep (se 2 (by rfl) ⟨8260359, by rfl⟩ : syracuseStep 22027625 = 16520719) B16520719
theorem B1810313 : Blo 562809 1810313 := bstep (se 2 (by rfl) ⟨678867, by rfl⟩ : syracuseStep 1810313 = 1357735) B1357735
theorem B565999 : Blo 562809 565999 := bstep (se 1 (by rfl) ⟨424499, by rfl⟩ : syracuseStep 565999 = 848999) B848999
theorem B566343 : Blo 562809 566343 := bstep (se 1 (by rfl) ⟨424757, by rfl⟩ : syracuseStep 566343 = 849515) B849515
theorem B1287647 : Blo 562809 1287647 := bstep (se 1 (by rfl) ⟨965735, by rfl⟩ : syracuseStep 1287647 = 1931471) B1931471
theorem B26093663 : Blo 562809 26093663 := bstep (se 1 (by rfl) ⟨19570247, by rfl⟩ : syracuseStep 26093663 = 39140495) B39140495
theorem B1910951 : Blo 562809 1910951 := bstep (se 1 (by rfl) ⟨1433213, by rfl⟩ : syracuseStep 1910951 = 2866427) B2866427
theorem B1354553 : Blo 562809 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B4074731 : Blo 562809 4074731 := bstep (se 1 (by rfl) ⟨3056048, by rfl⟩ : syracuseStep 4074731 = 6112097) B6112097
theorem B634783 : Blo 562809 634783 := bstep (se 1 (by rfl) ⟨476087, by rfl⟩ : syracuseStep 634783 = 952175) B952175
theorem B635647 : Blo 562809 635647 := bstep (se 1 (by rfl) ⟨476735, by rfl⟩ : syracuseStep 635647 = 953471) B953471
theorem B2178047 : Blo 562809 2178047 := bstep (se 1 (by rfl) ⟨1633535, by rfl⟩ : syracuseStep 2178047 = 3267071) B3267071
theorem B2900123 : Blo 562809 2900123 := bstep (se 1 (by rfl) ⟨2175092, by rfl⟩ : syracuseStep 2900123 = 4350185) B4350185
theorem B4081535 : Blo 562809 4081535 := bstep (se 1 (by rfl) ⟨3061151, by rfl⟩ : syracuseStep 4081535 = 6122303) B6122303
theorem B804919 : Blo 562809 804919 := bstep (se 1 (by rfl) ⟨603689, by rfl⟩ : syracuseStep 804919 = 1207379) B1207379
theorem B9129991 : Blo 562809 9129991 := bstep (se 1 (by rfl) ⟨6847493, by rfl⟩ : syracuseStep 9129991 = 13694987) B13694987
theorem B2281979 : Blo 562809 2281979 := bstep (se 1 (by rfl) ⟨1711484, by rfl⟩ : syracuseStep 2281979 = 3422969) B3422969
theorem B2414843 : Blo 562809 2414843 := bstep (se 1 (by rfl) ⟨1811132, by rfl⟩ : syracuseStep 2414843 = 3622265) B3622265
theorem B235561223 : Blo 562809 235561223 := bstep (se 1 (by rfl) ⟨176670917, by rfl⟩ : syracuseStep 235561223 = 353341835) B353341835
theorem B1270079 : Blo 562809 1270079 := bstep (se 1 (by rfl) ⟨952559, by rfl⟩ : syracuseStep 1270079 = 1905119) B1905119
theorem B1270943 : Blo 562809 1270943 := bstep (se 1 (by rfl) ⟨953207, by rfl⟩ : syracuseStep 1270943 = 1906415) B1906415
theorem B845039 : Blo 562809 845039 := bstep (se 1 (by rfl) ⟨633779, by rfl⟩ : syracuseStep 845039 = 1267559) B1267559
theorem B1271465 : Blo 562809 1271465 := bstep (se 2 (by rfl) ⟨476799, by rfl⟩ : syracuseStep 1271465 = 953599) B953599
theorem B1271663 : Blo 562809 1271663 := bstep (se 1 (by rfl) ⟨953747, by rfl⟩ : syracuseStep 1271663 = 1907495) B1907495
theorem B845801 : Blo 562809 845801 := bstep (se 2 (by rfl) ⟨317175, by rfl⟩ : syracuseStep 845801 = 634351) B634351
theorem B1272059 : Blo 562809 1272059 := bstep (se 1 (by rfl) ⟨954044, by rfl⟩ : syracuseStep 1272059 = 1908089) B1908089
theorem B846791 : Blo 562809 846791 := bstep (se 1 (by rfl) ⟨635093, by rfl⟩ : syracuseStep 846791 = 1270187) B1270187
theorem B1928377 : Blo 562809 1928377 := bstep (se 2 (by rfl) ⟨723141, by rfl⟩ : syracuseStep 1928377 = 1446283) B1446283
theorem B4287977 : Blo 562809 4287977 := bstep (se 2 (by rfl) ⟨1607991, by rfl⟩ : syracuseStep 4287977 = 3215983) B3215983
theorem B10874857 : Blo 562809 10874857 := bstep (se 2 (by rfl) ⟨4078071, by rfl⟩ : syracuseStep 10874857 = 8156143) B8156143
theorem B849119 : Blo 562809 849119 := bstep (se 1 (by rfl) ⟨636839, by rfl⟩ : syracuseStep 849119 = 1273679) B1273679
theorem B2029985 : Blo 562809 2029985 := bstep (se 2 (by rfl) ⟨761244, by rfl⟩ : syracuseStep 2029985 = 1522489) B1522489
theorem B3046013 : Blo 562809 3046013 := bstep (se 3 (by rfl) ⟨571127, by rfl⟩ : syracuseStep 3046013 = 1142255) B1142255
theorem B1735553 : Blo 562809 1735553 := bstep (se 2 (by rfl) ⟨650832, by rfl⟩ : syracuseStep 1735553 = 1301665) B1301665
theorem B950015 : Blo 562809 950015 := bstep (se 1 (by rfl) ⟨712511, by rfl⟩ : syracuseStep 950015 = 1425023) B1425023
theorem B1933415 : Blo 562809 1933415 := bstep (se 1 (by rfl) ⟨1450061, by rfl⟩ : syracuseStep 1933415 = 2900123) B2900123
theorem B628163261 : Blo 562809 628163261 := bstep (se 3 (by rfl) ⟨117780611, by rfl⟩ : syracuseStep 628163261 = 235561223) B235561223
theorem B2721023 : Blo 562809 2721023 := bstep (se 1 (by rfl) ⟨2040767, by rfl⟩ : syracuseStep 2721023 = 4081535) B4081535
theorem B1609895 : Blo 562809 1609895 := bstep (se 1 (by rfl) ⟨1207421, by rfl⟩ : syracuseStep 1609895 = 2414843) B2414843
theorem B1446113 : Blo 562809 1446113 := bstep (se 2 (by rfl) ⟨542292, by rfl⟩ : syracuseStep 1446113 = 1084585) B1084585
theorem B14685083 : Blo 562809 14685083 := bstep (se 1 (by rfl) ⟨11013812, by rfl⟩ : syracuseStep 14685083 = 22027625) B22027625
theorem B563359 : Blo 562809 563359 := bstep (se 1 (by rfl) ⟨422519, by rfl⟩ : syracuseStep 563359 = 845039) B845039
theorem B858431 : Blo 562809 858431 := bstep (se 1 (by rfl) ⟨643823, by rfl⟩ : syracuseStep 858431 = 1287647) B1287647
theorem B563867 : Blo 562809 563867 := bstep (se 1 (by rfl) ⟨422900, by rfl⟩ : syracuseStep 563867 = 845801) B845801
theorem B264870557 : Blo 562809 264870557 := bstep (se 3 (by rfl) ⟨49663229, by rfl⟩ : syracuseStep 264870557 = 99326459) B99326459
theorem B564527 : Blo 562809 564527 := bstep (se 1 (by rfl) ⟨423395, by rfl⟩ : syracuseStep 564527 = 846791) B846791
theorem B2858651 : Blo 562809 2858651 := bstep (se 1 (by rfl) ⟨2143988, by rfl⟩ : syracuseStep 2858651 = 4287977) B4287977
theorem B4628141 : Blo 562809 4628141 := bstep (se 3 (by rfl) ⟨867776, by rfl⟩ : syracuseStep 4628141 = 1735553) B1735553
theorem B5808125 : Blo 562809 5808125 := bstep (se 3 (by rfl) ⟨1089023, by rfl⟩ : syracuseStep 5808125 = 2178047) B2178047
theorem B566079 : Blo 562809 566079 := bstep (se 1 (by rfl) ⟨424559, by rfl⟩ : syracuseStep 566079 = 849119) B849119
theorem B1353323 : Blo 562809 1353323 := bstep (se 1 (by rfl) ⟨1014992, by rfl⟩ : syracuseStep 1353323 = 2029985) B2029985
theorem B633343 : Blo 562809 633343 := bstep (se 1 (by rfl) ⟨475007, by rfl⟩ : syracuseStep 633343 = 950015) B950015
theorem B6204185 : Blo 562809 6204185 := bstep (se 2 (by rfl) ⟨2326569, by rfl⟩ : syracuseStep 6204185 = 4653139) B4653139
theorem B7253549 : Blo 562809 7253549 := bstep (se 3 (by rfl) ⟨1360040, by rfl⟩ : syracuseStep 7253549 = 2720081) B2720081
theorem B43955465 : Blo 562809 43955465 := bstep (se 2 (by rfl) ⟨16483299, by rfl⟩ : syracuseStep 43955465 = 32966599) B32966599
theorem B3062015 : Blo 562809 3062015 := bstep (se 1 (by rfl) ⟨2296511, by rfl⟩ : syracuseStep 3062015 = 4593023) B4593023
theorem B2473199 : Blo 562809 2473199 := bstep (se 1 (by rfl) ⟨1854899, by rfl⟩ : syracuseStep 2473199 = 3709799) B3709799
theorem B14499809 : Blo 562809 14499809 := bstep (se 2 (by rfl) ⟨5437428, by rfl⟩ : syracuseStep 14499809 = 10874857) B10874857
theorem B12173321 : Blo 562809 12173321 := bstep (se 2 (by rfl) ⟨4564995, by rfl⟩ : syracuseStep 12173321 = 9129991) B9129991
theorem B903035 : Blo 562809 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B2410793 : Blo 562809 2410793 := bstep (se 2 (by rfl) ⟨904047, by rfl⟩ : syracuseStep 2410793 = 1808095) B1808095
theorem B1268315 : Blo 562809 1268315 := bstep (se 1 (by rfl) ⟨951236, by rfl⟩ : syracuseStep 1268315 = 1902473) B1902473
theorem B6085277 : Blo 562809 6085277 := bstep (se 3 (by rfl) ⟨1140989, by rfl⟩ : syracuseStep 6085277 = 2281979) B2281979
theorem B89545799 : Blo 562809 89545799 := bstep (se 1 (by rfl) ⟨67159349, by rfl⟩ : syracuseStep 89545799 = 134318699) B134318699
theorem B4808393 : Blo 562809 4808393 := bstep (se 2 (by rfl) ⟨1803147, by rfl⟩ : syracuseStep 4808393 = 3606295) B3606295
theorem B1073225 : Blo 562809 1073225 := bstep (se 2 (by rfl) ⟨402459, by rfl⟩ : syracuseStep 1073225 = 804919) B804919
theorem B846377 : Blo 562809 846377 := bstep (se 2 (by rfl) ⟨317391, by rfl⟩ : syracuseStep 846377 = 634783) B634783
theorem B1206875 : Blo 562809 1206875 := bstep (se 1 (by rfl) ⟨905156, by rfl⟩ : syracuseStep 1206875 = 1810313) B1810313
theorem B1272545 : Blo 562809 1272545 := bstep (se 2 (by rfl) ⟨477204, by rfl⟩ : syracuseStep 1272545 = 954409) B954409
theorem B846719 : Blo 562809 846719 := bstep (se 1 (by rfl) ⟨635039, by rfl⟩ : syracuseStep 846719 = 1270079) B1270079
theorem B847295 : Blo 562809 847295 := bstep (se 1 (by rfl) ⟨635471, by rfl⟩ : syracuseStep 847295 = 1270943) B1270943
theorem B10284677 : Blo 562809 10284677 := bstep (se 4 (by rfl) ⟨964188, by rfl⟩ : syracuseStep 10284677 = 1928377) B1928377
theorem B847529 : Blo 562809 847529 := bstep (se 2 (by rfl) ⟨317823, by rfl⟩ : syracuseStep 847529 = 635647) B635647
theorem B847643 : Blo 562809 847643 := bstep (se 1 (by rfl) ⟨635732, by rfl⟩ : syracuseStep 847643 = 1271465) B1271465
theorem B847775 : Blo 562809 847775 := bstep (se 1 (by rfl) ⟨635831, by rfl⟩ : syracuseStep 847775 = 1271663) B1271663
theorem B17395775 : Blo 562809 17395775 := bstep (se 1 (by rfl) ⟨13046831, by rfl⟩ : syracuseStep 17395775 = 26093663) B26093663
theorem B1273967 : Blo 562809 1273967 := bstep (se 1 (by rfl) ⟨955475, by rfl⟩ : syracuseStep 1273967 = 1910951) B1910951
theorem B848039 : Blo 562809 848039 := bstep (se 1 (by rfl) ⟨636029, by rfl⟩ : syracuseStep 848039 = 1272059) B1272059
theorem B2716487 : Blo 562809 2716487 := bstep (se 1 (by rfl) ⟨2037365, by rfl⟩ : syracuseStep 2716487 = 4074731) B4074731
theorem B2030675 : Blo 562809 2030675 := bstep (se 1 (by rfl) ⟨1523006, by rfl⟩ : syracuseStep 2030675 = 3046013) B3046013
theorem B418775507 : Blo 562809 418775507 := bstep (se 1 (by rfl) ⟨314081630, by rfl⟩ : syracuseStep 418775507 = 628163261) B628163261
theorem B1607195 : Blo 562809 1607195 := bstep (se 1 (by rfl) ⟨1205396, by rfl⟩ : syracuseStep 1607195 = 2410793) B2410793
theorem B117214573 : Blo 562809 117214573 := bstep (se 3 (by rfl) ⟨21977732, by rfl⟩ : syracuseStep 117214573 = 43955465) B43955465
theorem B1905767 : Blo 562809 1905767 := bstep (se 1 (by rfl) ⟨1429325, by rfl⟩ : syracuseStep 1905767 = 2858651) B2858651
theorem B3085427 : Blo 562809 3085427 := bstep (se 1 (by rfl) ⟨2314070, by rfl⟩ : syracuseStep 3085427 = 4628141) B4628141
theorem B3872083 : Blo 562809 3872083 := bstep (se 1 (by rfl) ⟨2904062, by rfl⟩ : syracuseStep 3872083 = 5808125) B5808125
theorem B564251 : Blo 562809 564251 := bstep (se 1 (by rfl) ⟨423188, by rfl⟩ : syracuseStep 564251 = 846377) B846377
theorem B4136123 : Blo 562809 4136123 := bstep (se 1 (by rfl) ⟨3102092, by rfl⟩ : syracuseStep 4136123 = 6204185) B6204185
theorem B564479 : Blo 562809 564479 := bstep (se 1 (by rfl) ⟨423359, by rfl⟩ : syracuseStep 564479 = 846719) B846719
theorem B564863 : Blo 562809 564863 := bstep (se 1 (by rfl) ⟨423647, by rfl⟩ : syracuseStep 564863 = 847295) B847295
theorem B6856451 : Blo 562809 6856451 := bstep (se 1 (by rfl) ⟨5142338, by rfl⟩ : syracuseStep 6856451 = 10284677) B10284677
theorem B565019 : Blo 562809 565019 := bstep (se 1 (by rfl) ⟨423764, by rfl⟩ : syracuseStep 565019 = 847529) B847529
theorem B565095 : Blo 562809 565095 := bstep (se 1 (by rfl) ⟨423821, by rfl⟩ : syracuseStep 565095 = 847643) B847643
theorem B565183 : Blo 562809 565183 := bstep (se 1 (by rfl) ⟨423887, by rfl⟩ : syracuseStep 565183 = 847775) B847775
theorem B565359 : Blo 562809 565359 := bstep (se 1 (by rfl) ⟨424019, by rfl⟩ : syracuseStep 565359 = 848039) B848039
theorem B5415133 : Blo 562809 5415133 := bstep (se 3 (by rfl) ⟨1015337, by rfl⟩ : syracuseStep 5415133 = 2030675) B2030675
theorem B1810991 : Blo 562809 1810991 := bstep (se 1 (by rfl) ⟨1358243, by rfl⟩ : syracuseStep 1810991 = 2716487) B2716487
theorem B2041343 : Blo 562809 2041343 := bstep (se 1 (by rfl) ⟨1531007, by rfl⟩ : syracuseStep 2041343 = 3062015) B3062015
theorem B1648799 : Blo 562809 1648799 := bstep (se 1 (by rfl) ⟨1236599, by rfl⟩ : syracuseStep 1648799 = 2473199) B2473199
theorem B1288943 : Blo 562809 1288943 := bstep (se 1 (by rfl) ⟨966707, by rfl⟩ : syracuseStep 1288943 = 1933415) B1933415
theorem B1814015 : Blo 562809 1814015 := bstep (se 1 (by rfl) ⟨1360511, by rfl⟩ : syracuseStep 1814015 = 2721023) B2721023
theorem B964075 : Blo 562809 964075 := bstep (se 1 (by rfl) ⟨723056, by rfl⟩ : syracuseStep 964075 = 1446113) B1446113
theorem B2408093 : Blo 562809 2408093 := bstep (se 3 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 2408093 = 903035) B903035
theorem B902215 : Blo 562809 902215 := bstep (se 1 (by rfl) ⟨676661, by rfl⟩ : syracuseStep 902215 = 1353323) B1353323
theorem B804583 : Blo 562809 804583 := bstep (se 1 (by rfl) ⟨603437, by rfl⟩ : syracuseStep 804583 = 1206875) B1206875
theorem B4835699 : Blo 562809 4835699 := bstep (se 1 (by rfl) ⟨3626774, by rfl⟩ : syracuseStep 4835699 = 7253549) B7253549
theorem B8115547 : Blo 562809 8115547 := bstep (se 1 (by rfl) ⟨6086660, by rfl⟩ : syracuseStep 8115547 = 12173321) B12173321
theorem B1073263 : Blo 562809 1073263 := bstep (se 1 (by rfl) ⟨804947, by rfl⟩ : syracuseStep 1073263 = 1609895) B1609895
theorem B9790055 : Blo 562809 9790055 := bstep (se 1 (by rfl) ⟨7342541, by rfl⟩ : syracuseStep 9790055 = 14685083) B14685083
theorem B844457 : Blo 562809 844457 := bstep (se 2 (by rfl) ⟨316671, by rfl⟩ : syracuseStep 844457 = 633343) B633343
theorem B845543 : Blo 562809 845543 := bstep (se 1 (by rfl) ⟨634157, by rfl⟩ : syracuseStep 845543 = 1268315) B1268315
theorem B4056851 : Blo 562809 4056851 := bstep (se 1 (by rfl) ⟨3042638, by rfl⟩ : syracuseStep 4056851 = 6085277) B6085277
theorem B176580371 : Blo 562809 176580371 := bstep (se 1 (by rfl) ⟨132435278, by rfl⟩ : syracuseStep 176580371 = 264870557) B264870557
theorem B59697199 : Blo 562809 59697199 := bstep (se 1 (by rfl) ⟨44772899, by rfl⟩ : syracuseStep 59697199 = 89545799) B89545799
theorem B3205595 : Blo 562809 3205595 := bstep (se 1 (by rfl) ⟨2404196, by rfl⟩ : syracuseStep 3205595 = 4808393) B4808393
theorem B715483 : Blo 562809 715483 := bstep (se 1 (by rfl) ⟨536612, by rfl⟩ : syracuseStep 715483 = 1073225) B1073225
theorem B2289149 : Blo 562809 2289149 := bstep (se 3 (by rfl) ⟨429215, by rfl⟩ : syracuseStep 2289149 = 858431) B858431
theorem B848363 : Blo 562809 848363 := bstep (se 1 (by rfl) ⟨636272, by rfl⟩ : syracuseStep 848363 = 1272545) B1272545
theorem B11597183 : Blo 562809 11597183 := bstep (se 1 (by rfl) ⟨8697887, by rfl⟩ : syracuseStep 11597183 = 17395775) B17395775
theorem B849311 : Blo 562809 849311 := bstep (se 1 (by rfl) ⟨636983, by rfl⟩ : syracuseStep 849311 = 1273967) B1273967
theorem B9666539 : Blo 562809 9666539 := bstep (se 1 (by rfl) ⟨7249904, by rfl⟩ : syracuseStep 9666539 = 14499809) B14499809
theorem B279183671 : Blo 562809 279183671 := bstep (se 1 (by rfl) ⟨209387753, by rfl⟩ : syracuseStep 279183671 = 418775507) B418775507
theorem B79596265 : Blo 562809 79596265 := bstep (se 2 (by rfl) ⟨29848599, by rfl⟩ : syracuseStep 79596265 = 59697199) B59697199
theorem B953977 : Blo 562809 953977 := bstep (se 2 (by rfl) ⟨357741, by rfl⟩ : syracuseStep 953977 = 715483) B715483
theorem B10818269 : Blo 562809 10818269 := bstep (se 3 (by rfl) ⟨2028425, by rfl⟩ : syracuseStep 10818269 = 4056851) B4056851
theorem B470880989 : Blo 562809 470880989 := bstep (se 3 (by rfl) ⟨88290185, by rfl⟩ : syracuseStep 470880989 = 176580371) B176580371
theorem B2757415 : Blo 562809 2757415 := bstep (se 1 (by rfl) ⟨2068061, by rfl⟩ : syracuseStep 2757415 = 4136123) B4136123
theorem B6526703 : Blo 562809 6526703 := bstep (se 1 (by rfl) ⟨4895027, by rfl⟩ : syracuseStep 6526703 = 9790055) B9790055
theorem B562971 : Blo 562809 562971 := bstep (se 1 (by rfl) ⟨422228, by rfl⟩ : syracuseStep 562971 = 844457) B844457
theorem B563695 : Blo 562809 563695 := bstep (se 1 (by rfl) ⟨422771, by rfl⟩ : syracuseStep 563695 = 845543) B845543
theorem B2137063 : Blo 562809 2137063 := bstep (se 1 (by rfl) ⟨1602797, by rfl⟩ : syracuseStep 2137063 = 3205595) B3205595
theorem B10820729 : Blo 562809 10820729 := bstep (se 2 (by rfl) ⟨4057773, by rfl⟩ : syracuseStep 10820729 = 8115547) B8115547
theorem B859295 : Blo 562809 859295 := bstep (se 1 (by rfl) ⟨644471, by rfl⟩ : syracuseStep 859295 = 1288943) B1288943
theorem B1285433 : Blo 562809 1285433 := bstep (se 2 (by rfl) ⟨482037, by rfl⟩ : syracuseStep 1285433 = 964075) B964075
theorem B565575 : Blo 562809 565575 := bstep (se 1 (by rfl) ⟨424181, by rfl⟩ : syracuseStep 565575 = 848363) B848363
theorem B566207 : Blo 562809 566207 := bstep (se 1 (by rfl) ⟨424655, by rfl⟩ : syracuseStep 566207 = 849311) B849311
theorem B7220177 : Blo 562809 7220177 := bstep (se 2 (by rfl) ⟨2707566, by rfl⟩ : syracuseStep 7220177 = 5415133) B5415133
theorem B3223799 : Blo 562809 3223799 := bstep (se 1 (by rfl) ⟨2417849, by rfl⟩ : syracuseStep 3223799 = 4835699) B4835699
theorem B156286097 : Blo 562809 156286097 := bstep (se 2 (by rfl) ⟨58607286, by rfl⟩ : syracuseStep 156286097 = 117214573) B117214573
theorem B4570967 : Blo 562809 4570967 := bstep (se 1 (by rfl) ⟨3428225, by rfl⟩ : syracuseStep 4570967 = 6856451) B6856451
theorem B1360895 : Blo 562809 1360895 := bstep (se 1 (by rfl) ⟨1020671, by rfl⟩ : syracuseStep 1360895 = 2041343) B2041343
theorem B1099199 : Blo 562809 1099199 := bstep (se 1 (by rfl) ⟨824399, by rfl⟩ : syracuseStep 1099199 = 1648799) B1648799
theorem B5162777 : Blo 562809 5162777 := bstep (se 2 (by rfl) ⟨1936041, by rfl⟩ : syracuseStep 5162777 = 3872083) B3872083
theorem B1526099 : Blo 562809 1526099 := bstep (se 1 (by rfl) ⟨1144574, by rfl⟩ : syracuseStep 1526099 = 2289149) B2289149
theorem B6444359 : Blo 562809 6444359 := bstep (se 1 (by rfl) ⟨4833269, by rfl⟩ : syracuseStep 6444359 = 9666539) B9666539
theorem B1431017 : Blo 562809 1431017 := bstep (se 2 (by rfl) ⟨536631, by rfl⟩ : syracuseStep 1431017 = 1073263) B1073263
theorem B1071463 : Blo 562809 1071463 := bstep (se 1 (by rfl) ⟨803597, by rfl⟩ : syracuseStep 1071463 = 1607195) B1607195
theorem B1202953 : Blo 562809 1202953 := bstep (se 2 (by rfl) ⟨451107, by rfl⟩ : syracuseStep 1202953 = 902215) B902215
theorem B1072777 : Blo 562809 1072777 := bstep (se 2 (by rfl) ⟨402291, by rfl⟩ : syracuseStep 1072777 = 804583) B804583
theorem B1270511 : Blo 562809 1270511 := bstep (se 1 (by rfl) ⟨952883, by rfl⟩ : syracuseStep 1270511 = 1905767) B1905767
theorem B2056951 : Blo 562809 2056951 := bstep (se 1 (by rfl) ⟨1542713, by rfl⟩ : syracuseStep 2056951 = 3085427) B3085427
theorem B1207327 : Blo 562809 1207327 := bstep (se 1 (by rfl) ⟨905495, by rfl⟩ : syracuseStep 1207327 = 1810991) B1810991
theorem B1209343 : Blo 562809 1209343 := bstep (se 1 (by rfl) ⟨907007, by rfl⟩ : syracuseStep 1209343 = 1814015) B1814015
theorem B7731455 : Blo 562809 7731455 := bstep (se 1 (by rfl) ⟨5798591, by rfl⟩ : syracuseStep 7731455 = 11597183) B11597183
theorem B1605395 : Blo 562809 1605395 := bstep (se 1 (by rfl) ⟨1204046, by rfl⟩ : syracuseStep 1605395 = 2408093) B2408093
theorem B186122447 : Blo 562809 186122447 := bstep (se 1 (by rfl) ⟨139591835, by rfl⟩ : syracuseStep 186122447 = 279183671) B279183671
theorem B3441851 : Blo 562809 3441851 := bstep (se 1 (by rfl) ⟨2581388, by rfl⟩ : syracuseStep 3441851 = 5162777) B5162777
theorem B7212179 : Blo 562809 7212179 := bstep (se 1 (by rfl) ⟨5409134, by rfl⟩ : syracuseStep 7212179 = 10818269) B10818269
theorem B313920659 : Blo 562809 313920659 := bstep (se 1 (by rfl) ⟨235440494, by rfl⟩ : syracuseStep 313920659 = 470880989) B470880989
theorem B4296239 : Blo 562809 4296239 := bstep (se 1 (by rfl) ⟨3222179, by rfl⟩ : syracuseStep 4296239 = 6444359) B6444359
theorem B954011 : Blo 562809 954011 := bstep (se 1 (by rfl) ⟨715508, by rfl⟩ : syracuseStep 954011 = 1431017) B1431017
theorem B1609769 : Blo 562809 1609769 := bstep (se 2 (by rfl) ⟨603663, by rfl⟩ : syracuseStep 1609769 = 1207327) B1207327
theorem B17404541 : Blo 562809 17404541 := bstep (se 3 (by rfl) ⟨3263351, by rfl⟩ : syracuseStep 17404541 = 6526703) B6526703
theorem B7213819 : Blo 562809 7213819 := bstep (se 1 (by rfl) ⟨5410364, by rfl⟩ : syracuseStep 7213819 = 10820729) B10820729
theorem B856955 : Blo 562809 856955 := bstep (se 1 (by rfl) ⟨642716, by rfl⟩ : syracuseStep 856955 = 1285433) B1285433
theorem B4069597 : Blo 562809 4069597 := bstep (se 3 (by rfl) ⟨763049, by rfl⟩ : syracuseStep 4069597 = 1526099) B1526099
theorem B3676553 : Blo 562809 3676553 := bstep (se 2 (by rfl) ⟨1378707, by rfl⟩ : syracuseStep 3676553 = 2757415) B2757415
theorem B1612457 : Blo 562809 1612457 := bstep (se 2 (by rfl) ⟨604671, by rfl⟩ : syracuseStep 1612457 = 1209343) B1209343
theorem B2931197 : Blo 562809 2931197 := bstep (se 3 (by rfl) ⟨549599, by rfl⟩ : syracuseStep 2931197 = 1099199) B1099199
theorem B2149199 : Blo 562809 2149199 := bstep (se 1 (by rfl) ⟨1611899, by rfl⟩ : syracuseStep 2149199 = 3223799) B3223799
theorem B1428617 : Blo 562809 1428617 := bstep (se 2 (by rfl) ⟨535731, by rfl⟩ : syracuseStep 1428617 = 1071463) B1071463
theorem B104190731 : Blo 562809 104190731 := bstep (se 1 (by rfl) ⟨78143048, by rfl⟩ : syracuseStep 104190731 = 156286097) B156286097
theorem B1430369 : Blo 562809 1430369 := bstep (se 2 (by rfl) ⟨536388, by rfl⟩ : syracuseStep 1430369 = 1072777) B1072777
theorem B1070263 : Blo 562809 1070263 := bstep (se 1 (by rfl) ⟨802697, by rfl⟩ : syracuseStep 1070263 = 1605395) B1605395
theorem B2742601 : Blo 562809 2742601 := bstep (se 2 (by rfl) ⟨1028475, by rfl⟩ : syracuseStep 2742601 = 2056951) B2056951
theorem B82468853 : Blo 562809 82468853 := bstep (se 5 (by rfl) ⟨3865727, by rfl⟩ : syracuseStep 82468853 = 7731455) B7731455
theorem B3629053 : Blo 562809 3629053 := bstep (se 3 (by rfl) ⟨680447, by rfl⟩ : syracuseStep 3629053 = 1360895) B1360895
theorem B106128353 : Blo 562809 106128353 := bstep (se 2 (by rfl) ⟨39798132, by rfl⟩ : syracuseStep 106128353 = 79596265) B79596265
theorem B1271969 : Blo 562809 1271969 := bstep (se 2 (by rfl) ⟨476988, by rfl⟩ : syracuseStep 1271969 = 953977) B953977
theorem B847007 : Blo 562809 847007 := bstep (se 1 (by rfl) ⟨635255, by rfl⟩ : syracuseStep 847007 = 1270511) B1270511
theorem B4813451 : Blo 562809 4813451 := bstep (se 1 (by rfl) ⟨3610088, by rfl⟩ : syracuseStep 4813451 = 7220177) B7220177
theorem B2291453 : Blo 562809 2291453 := bstep (se 3 (by rfl) ⟨429647, by rfl⟩ : syracuseStep 2291453 = 859295) B859295
theorem B1603937 : Blo 562809 1603937 := bstep (se 2 (by rfl) ⟨601476, by rfl⟩ : syracuseStep 1603937 = 1202953) B1202953
theorem B2849417 : Blo 562809 2849417 := bstep (se 2 (by rfl) ⟨1068531, by rfl⟩ : syracuseStep 2849417 = 2137063) B2137063
theorem B3047311 : Blo 562809 3047311 := bstep (se 1 (by rfl) ⟨2285483, by rfl⟩ : syracuseStep 3047311 = 4570967) B4570967
theorem B2294567 : Blo 562809 2294567 := bstep (se 1 (by rfl) ⟨1720925, by rfl⟩ : syracuseStep 2294567 = 3441851) B3441851
theorem B952411 : Blo 562809 952411 := bstep (se 1 (by rfl) ⟨714308, by rfl⟩ : syracuseStep 952411 = 1428617) B1428617
theorem B11603027 : Blo 562809 11603027 := bstep (se 1 (by rfl) ⟨8702270, by rfl⟩ : syracuseStep 11603027 = 17404541) B17404541
theorem B953579 : Blo 562809 953579 := bstep (se 1 (by rfl) ⟨715184, by rfl⟩ : syracuseStep 953579 = 1430369) B1430369
theorem B31266101 : Blo 562809 31266101 := bstep (se 5 (by rfl) ⟨1465598, by rfl⟩ : syracuseStep 31266101 = 2931197) B2931197
theorem B564671 : Blo 562809 564671 := bstep (se 1 (by rfl) ⟨423503, by rfl⟩ : syracuseStep 564671 = 847007) B847007
theorem B2864159 : Blo 562809 2864159 := bstep (se 1 (by rfl) ⟨2148119, by rfl⟩ : syracuseStep 2864159 = 4296239) B4296239
theorem B636007 : Blo 562809 636007 := bstep (se 1 (by rfl) ⟨477005, by rfl⟩ : syracuseStep 636007 = 954011) B954011
theorem B571303 : Blo 562809 571303 := bstep (se 1 (by rfl) ⟨428477, by rfl⟩ : syracuseStep 571303 = 856955) B856955
theorem B9618425 : Blo 562809 9618425 := bstep (se 2 (by rfl) ⟨3606909, by rfl⟩ : syracuseStep 9618425 = 7213819) B7213819
theorem B1427017 : Blo 562809 1427017 := bstep (se 2 (by rfl) ⟨535131, by rfl⟩ : syracuseStep 1427017 = 1070263) B1070263
theorem B5426129 : Blo 562809 5426129 := bstep (se 2 (by rfl) ⟨2034798, by rfl⟩ : syracuseStep 5426129 = 4069597) B4069597
theorem B3656801 : Blo 562809 3656801 := bstep (se 2 (by rfl) ⟨1371300, by rfl⟩ : syracuseStep 3656801 = 2742601) B2742601
theorem B1527635 : Blo 562809 1527635 := bstep (se 1 (by rfl) ⟨1145726, by rfl⟩ : syracuseStep 1527635 = 2291453) B2291453
theorem B1069291 : Blo 562809 1069291 := bstep (se 1 (by rfl) ⟨801968, by rfl⟩ : syracuseStep 1069291 = 1603937) B1603937
theorem B4838737 : Blo 562809 4838737 := bstep (se 2 (by rfl) ⟨1814526, by rfl⟩ : syracuseStep 4838737 = 3629053) B3629053
theorem B124081631 : Blo 562809 124081631 := bstep (se 1 (by rfl) ⟨93061223, by rfl⟩ : syracuseStep 124081631 = 186122447) B186122447
theorem B1432799 : Blo 562809 1432799 := bstep (se 1 (by rfl) ⟨1074599, by rfl⟩ : syracuseStep 1432799 = 2149199) B2149199
theorem B4808119 : Blo 562809 4808119 := bstep (se 1 (by rfl) ⟨3606089, by rfl⟩ : syracuseStep 4808119 = 7212179) B7212179
theorem B209280439 : Blo 562809 209280439 := bstep (se 1 (by rfl) ⟨156960329, by rfl⟩ : syracuseStep 209280439 = 313920659) B313920659
theorem B283008941 : Blo 562809 283008941 := bstep (se 3 (by rfl) ⟨53064176, by rfl⟩ : syracuseStep 283008941 = 106128353) B106128353
theorem B1073179 : Blo 562809 1073179 := bstep (se 1 (by rfl) ⟨804884, by rfl⟩ : syracuseStep 1073179 = 1609769) B1609769
theorem B69460487 : Blo 562809 69460487 := bstep (se 1 (by rfl) ⟨52095365, by rfl⟩ : syracuseStep 69460487 = 104190731) B104190731
theorem B2451035 : Blo 562809 2451035 := bstep (se 1 (by rfl) ⟨1838276, by rfl⟩ : syracuseStep 2451035 = 3676553) B3676553
theorem B1074971 : Blo 562809 1074971 := bstep (se 1 (by rfl) ⟨806228, by rfl⟩ : syracuseStep 1074971 = 1612457) B1612457
theorem B54979235 : Blo 562809 54979235 := bstep (se 1 (by rfl) ⟨41234426, by rfl⟩ : syracuseStep 54979235 = 82468853) B82468853
theorem B847979 : Blo 562809 847979 := bstep (se 1 (by rfl) ⟨635984, by rfl⟩ : syracuseStep 847979 = 1271969) B1271969
theorem B3208967 : Blo 562809 3208967 := bstep (se 1 (by rfl) ⟨2406725, by rfl⟩ : syracuseStep 3208967 = 4813451) B4813451
theorem B1899611 : Blo 562809 1899611 := bstep (se 1 (by rfl) ⟨1424708, by rfl⟩ : syracuseStep 1899611 = 2849417) B2849417
theorem B4063081 : Blo 562809 4063081 := bstep (se 2 (by rfl) ⟨1523655, by rfl⟩ : syracuseStep 4063081 = 3047311) B3047311
theorem B7735351 : Blo 562809 7735351 := bstep (se 1 (by rfl) ⟨5801513, by rfl⟩ : syracuseStep 7735351 = 11603027) B11603027
theorem B1902689 : Blo 562809 1902689 := bstep (se 2 (by rfl) ⟨713508, by rfl⟩ : syracuseStep 1902689 = 1427017) B1427017
theorem B1018423 : Blo 562809 1018423 := bstep (se 1 (by rfl) ⟨763817, by rfl⟩ : syracuseStep 1018423 = 1527635) B1527635
theorem B20844067 : Blo 562809 20844067 := bstep (se 1 (by rfl) ⟨15633050, by rfl⟩ : syracuseStep 20844067 = 31266101) B31266101
theorem B955199 : Blo 562809 955199 := bstep (se 1 (by rfl) ⟨716399, by rfl⟩ : syracuseStep 955199 = 1432799) B1432799
theorem B46306991 : Blo 562809 46306991 := bstep (se 1 (by rfl) ⟨34730243, by rfl⟩ : syracuseStep 46306991 = 69460487) B69460487
theorem B761737 : Blo 562809 761737 := bstep (se 2 (by rfl) ⟨285651, by rfl⟩ : syracuseStep 761737 = 571303) B571303
theorem B565319 : Blo 562809 565319 := bstep (se 1 (by rfl) ⟨423989, by rfl⟩ : syracuseStep 565319 = 847979) B847979
theorem B1909439 : Blo 562809 1909439 := bstep (se 1 (by rfl) ⟨1432079, by rfl⟩ : syracuseStep 1909439 = 2864159) B2864159
theorem B2139311 : Blo 562809 2139311 := bstep (se 1 (by rfl) ⟨1604483, by rfl⟩ : syracuseStep 2139311 = 3208967) B3208967
theorem B5417441 : Blo 562809 5417441 := bstep (se 2 (by rfl) ⟨2031540, by rfl⟩ : syracuseStep 5417441 = 4063081) B4063081
theorem B3617419 : Blo 562809 3617419 := bstep (se 1 (by rfl) ⟨2713064, by rfl⟩ : syracuseStep 3617419 = 5426129) B5426129
theorem B2437867 : Blo 562809 2437867 := bstep (se 1 (by rfl) ⟨1828400, by rfl⟩ : syracuseStep 2437867 = 3656801) B3656801
theorem B635719 : Blo 562809 635719 := bstep (se 1 (by rfl) ⟨476789, by rfl⟩ : syracuseStep 635719 = 953579) B953579
theorem B82721087 : Blo 562809 82721087 := bstep (se 1 (by rfl) ⟨62040815, by rfl⟩ : syracuseStep 82721087 = 124081631) B124081631
theorem B2866589 : Blo 562809 2866589 := bstep (se 3 (by rfl) ⟨537485, by rfl⟩ : syracuseStep 2866589 = 1074971) B1074971
theorem B1425721 : Blo 562809 1425721 := bstep (se 2 (by rfl) ⟨534645, by rfl⟩ : syracuseStep 1425721 = 1069291) B1069291
theorem B36652823 : Blo 562809 36652823 := bstep (se 1 (by rfl) ⟨27489617, by rfl⟩ : syracuseStep 36652823 = 54979235) B54979235
theorem B6410825 : Blo 562809 6410825 := bstep (se 2 (by rfl) ⟨2404059, by rfl⟩ : syracuseStep 6410825 = 4808119) B4808119
theorem B279040585 : Blo 562809 279040585 := bstep (se 2 (by rfl) ⟨104640219, by rfl⟩ : syracuseStep 279040585 = 209280439) B209280439
theorem B1266407 : Blo 562809 1266407 := bstep (se 1 (by rfl) ⟨949805, by rfl⟩ : syracuseStep 1266407 = 1899611) B1899611
theorem B1430905 : Blo 562809 1430905 := bstep (se 2 (by rfl) ⟨536589, by rfl⟩ : syracuseStep 1430905 = 1073179) B1073179
theorem B1529711 : Blo 562809 1529711 := bstep (se 1 (by rfl) ⟨1147283, by rfl⟩ : syracuseStep 1529711 = 2294567) B2294567
theorem B6412283 : Blo 562809 6412283 := bstep (se 1 (by rfl) ⟨4809212, by rfl⟩ : syracuseStep 6412283 = 9618425) B9618425
theorem B1269881 : Blo 562809 1269881 := bstep (se 2 (by rfl) ⟨476205, by rfl⟩ : syracuseStep 1269881 = 952411) B952411
theorem B188672627 : Blo 562809 188672627 := bstep (se 1 (by rfl) ⟨141504470, by rfl⟩ : syracuseStep 188672627 = 283008941) B283008941
theorem B1634023 : Blo 562809 1634023 := bstep (se 1 (by rfl) ⟨1225517, by rfl⟩ : syracuseStep 1634023 = 2451035) B2451035
theorem B848009 : Blo 562809 848009 := bstep (se 2 (by rfl) ⟨318003, by rfl⟩ : syracuseStep 848009 = 636007) B636007
theorem B6451649 : Blo 562809 6451649 := bstep (se 2 (by rfl) ⟨2419368, by rfl⟩ : syracuseStep 6451649 = 4838737) B4838737
theorem B1900961 : Blo 562809 1900961 := bstep (se 2 (by rfl) ⟨712860, by rfl⟩ : syracuseStep 1900961 = 1425721) B1425721
theorem B30871327 : Blo 562809 30871327 := bstep (se 1 (by rfl) ⟨23153495, by rfl⟩ : syracuseStep 30871327 = 46306991) B46306991
theorem B1019807 : Blo 562809 1019807 := bstep (se 1 (by rfl) ⟨764855, by rfl⟩ : syracuseStep 1019807 = 1529711) B1529711
theorem B27792089 : Blo 562809 27792089 := bstep (se 2 (by rfl) ⟨10422033, by rfl⟩ : syracuseStep 27792089 = 20844067) B20844067
theorem B372054113 : Blo 562809 372054113 := bstep (se 2 (by rfl) ⟨139520292, by rfl⟩ : syracuseStep 372054113 = 279040585) B279040585
theorem B4823225 : Blo 562809 4823225 := bstep (se 2 (by rfl) ⟨1808709, by rfl⟩ : syracuseStep 4823225 = 3617419) B3617419
theorem B3611627 : Blo 562809 3611627 := bstep (se 1 (by rfl) ⟨2708720, by rfl⟩ : syracuseStep 3611627 = 5417441) B5417441
theorem B1907873 : Blo 562809 1907873 := bstep (se 2 (by rfl) ⟨715452, by rfl⟩ : syracuseStep 1907873 = 1430905) B1430905
theorem B565339 : Blo 562809 565339 := bstep (se 1 (by rfl) ⟨424004, by rfl⟩ : syracuseStep 565339 = 848009) B848009
theorem B4301099 : Blo 562809 4301099 := bstep (se 1 (by rfl) ⟨3225824, by rfl⟩ : syracuseStep 4301099 = 6451649) B6451649
theorem B1911059 : Blo 562809 1911059 := bstep (se 1 (by rfl) ⟨1433294, by rfl⟩ : syracuseStep 1911059 = 2866589) B2866589
theorem B4273883 : Blo 562809 4273883 := bstep (se 1 (by rfl) ⟨3205412, by rfl⟩ : syracuseStep 4273883 = 6410825) B6410825
theorem B636799 : Blo 562809 636799 := bstep (se 1 (by rfl) ⟨477599, by rfl⟩ : syracuseStep 636799 = 955199) B955199
theorem B1357897 : Blo 562809 1357897 := bstep (se 2 (by rfl) ⟨509211, by rfl⟩ : syracuseStep 1357897 = 1018423) B1018423
theorem B4274855 : Blo 562809 4274855 := bstep (se 1 (by rfl) ⟨3206141, by rfl⟩ : syracuseStep 4274855 = 6412283) B6412283
theorem B2178697 : Blo 562809 2178697 := bstep (se 2 (by rfl) ⟨817011, by rfl⟩ : syracuseStep 2178697 = 1634023) B1634023
theorem B1426207 : Blo 562809 1426207 := bstep (se 1 (by rfl) ⟨1069655, by rfl⟩ : syracuseStep 1426207 = 2139311) B2139311
theorem B125781751 : Blo 562809 125781751 := bstep (se 1 (by rfl) ⟨94336313, by rfl⟩ : syracuseStep 125781751 = 188672627) B188672627
theorem B24435215 : Blo 562809 24435215 := bstep (se 1 (by rfl) ⟨18326411, by rfl⟩ : syracuseStep 24435215 = 36652823) B36652823
theorem B1268459 : Blo 562809 1268459 := bstep (se 1 (by rfl) ⟨951344, by rfl⟩ : syracuseStep 1268459 = 1902689) B1902689
theorem B10313801 : Blo 562809 10313801 := bstep (se 2 (by rfl) ⟨3867675, by rfl⟩ : syracuseStep 10313801 = 7735351) B7735351
theorem B844271 : Blo 562809 844271 := bstep (se 1 (by rfl) ⟨633203, by rfl⟩ : syracuseStep 844271 = 1266407) B1266407
theorem B13001957 : Blo 562809 13001957 := bstep (se 4 (by rfl) ⟨1218933, by rfl⟩ : syracuseStep 13001957 = 2437867) B2437867
theorem B846587 : Blo 562809 846587 := bstep (se 1 (by rfl) ⟨634940, by rfl⟩ : syracuseStep 846587 = 1269881) B1269881
theorem B1272959 : Blo 562809 1272959 := bstep (se 1 (by rfl) ⟨954719, by rfl⟩ : syracuseStep 1272959 = 1909439) B1909439
theorem B847625 : Blo 562809 847625 := bstep (se 2 (by rfl) ⟨317859, by rfl⟩ : syracuseStep 847625 = 635719) B635719
theorem B55147391 : Blo 562809 55147391 := bstep (se 1 (by rfl) ⟨41360543, by rfl⟩ : syracuseStep 55147391 = 82721087) B82721087
theorem B1015649 : Blo 562809 1015649 := bstep (se 2 (by rfl) ⟨380868, by rfl⟩ : syracuseStep 1015649 = 761737) B761737
theorem B1901609 : Blo 562809 1901609 := bstep (se 2 (by rfl) ⟨713103, by rfl⟩ : syracuseStep 1901609 = 1426207) B1426207
theorem B167709001 : Blo 562809 167709001 := bstep (se 2 (by rfl) ⟨62890875, by rfl⟩ : syracuseStep 167709001 = 125781751) B125781751
theorem B3215483 : Blo 562809 3215483 := bstep (se 1 (by rfl) ⟨2411612, by rfl⟩ : syracuseStep 3215483 = 4823225) B4823225
theorem B16290143 : Blo 562809 16290143 := bstep (se 1 (by rfl) ⟨12217607, by rfl⟩ : syracuseStep 16290143 = 24435215) B24435215
theorem B41161769 : Blo 562809 41161769 := bstep (se 2 (by rfl) ⟨15435663, by rfl⟩ : syracuseStep 41161769 = 30871327) B30871327
theorem B562847 : Blo 562809 562847 := bstep (se 1 (by rfl) ⟨422135, by rfl⟩ : syracuseStep 562847 = 844271) B844271
theorem B564391 : Blo 562809 564391 := bstep (se 1 (by rfl) ⟨423293, by rfl⟩ : syracuseStep 564391 = 846587) B846587
theorem B565083 : Blo 562809 565083 := bstep (se 1 (by rfl) ⟨423812, by rfl⟩ : syracuseStep 565083 = 847625) B847625
theorem B1810529 : Blo 562809 1810529 := bstep (se 2 (by rfl) ⟨678948, by rfl⟩ : syracuseStep 1810529 = 1357897) B1357897
theorem B18528059 : Blo 562809 18528059 := bstep (se 1 (by rfl) ⟨13896044, by rfl⟩ : syracuseStep 18528059 = 27792089) B27792089
theorem B248036075 : Blo 562809 248036075 := bstep (se 1 (by rfl) ⟨186027056, by rfl⟩ : syracuseStep 248036075 = 372054113) B372054113
theorem B2407751 : Blo 562809 2407751 := bstep (se 1 (by rfl) ⟨1805813, by rfl⟩ : syracuseStep 2407751 = 3611627) B3611627
theorem B2867399 : Blo 562809 2867399 := bstep (se 1 (by rfl) ⟨2150549, by rfl⟩ : syracuseStep 2867399 = 4301099) B4301099
theorem B8667971 : Blo 562809 8667971 := bstep (se 1 (by rfl) ⟨6500978, by rfl⟩ : syracuseStep 8667971 = 13001957) B13001957
theorem B2904929 : Blo 562809 2904929 := bstep (se 2 (by rfl) ⟨1089348, by rfl⟩ : syracuseStep 2904929 = 2178697) B2178697
theorem B677099 : Blo 562809 677099 := bstep (se 1 (by rfl) ⟨507824, by rfl⟩ : syracuseStep 677099 = 1015649) B1015649
theorem B1267307 : Blo 562809 1267307 := bstep (se 1 (by rfl) ⟨950480, by rfl⟩ : syracuseStep 1267307 = 1900961) B1900961
theorem B679871 : Blo 562809 679871 := bstep (se 1 (by rfl) ⟨509903, by rfl⟩ : syracuseStep 679871 = 1019807) B1019807
theorem B845639 : Blo 562809 845639 := bstep (se 1 (by rfl) ⟨634229, by rfl⟩ : syracuseStep 845639 = 1268459) B1268459
theorem B1271915 : Blo 562809 1271915 := bstep (se 1 (by rfl) ⟨953936, by rfl⟩ : syracuseStep 1271915 = 1907873) B1907873
theorem B6875867 : Blo 562809 6875867 := bstep (se 1 (by rfl) ⟨5156900, by rfl⟩ : syracuseStep 6875867 = 10313801) B10313801
theorem B1274039 : Blo 562809 1274039 := bstep (se 1 (by rfl) ⟨955529, by rfl⟩ : syracuseStep 1274039 = 1911059) B1911059
theorem B848639 : Blo 562809 848639 := bstep (se 1 (by rfl) ⟨636479, by rfl⟩ : syracuseStep 848639 = 1272959) B1272959
theorem B849065 : Blo 562809 849065 := bstep (se 2 (by rfl) ⟨318399, by rfl⟩ : syracuseStep 849065 = 636799) B636799
theorem B2849255 : Blo 562809 2849255 := bstep (se 1 (by rfl) ⟨2136941, by rfl⟩ : syracuseStep 2849255 = 4273883) B4273883
theorem B2849903 : Blo 562809 2849903 := bstep (se 1 (by rfl) ⟨2137427, by rfl⟩ : syracuseStep 2849903 = 4274855) B4274855
theorem B36764927 : Blo 562809 36764927 := bstep (se 1 (by rfl) ⟨27573695, by rfl⟩ : syracuseStep 36764927 = 55147391) B55147391
theorem B223612001 : Blo 562809 223612001 := bstep (se 2 (by rfl) ⟨83854500, by rfl⟩ : syracuseStep 223612001 = 167709001) B167709001
theorem B1936619 : Blo 562809 1936619 := bstep (se 1 (by rfl) ⟨1452464, by rfl⟩ : syracuseStep 1936619 = 2904929) B2904929
theorem B1805597 : Blo 562809 1805597 := bstep (se 3 (by rfl) ⟨338549, by rfl⟩ : syracuseStep 1805597 = 677099) B677099
theorem B563759 : Blo 562809 563759 := bstep (se 1 (by rfl) ⟨422819, by rfl⟩ : syracuseStep 563759 = 845639) B845639
theorem B565759 : Blo 562809 565759 := bstep (se 1 (by rfl) ⟨424319, by rfl⟩ : syracuseStep 565759 = 848639) B848639
theorem B566043 : Blo 562809 566043 := bstep (se 1 (by rfl) ⟨424532, by rfl⟩ : syracuseStep 566043 = 849065) B849065
theorem B165357383 : Blo 562809 165357383 := bstep (se 1 (by rfl) ⟨124018037, by rfl⟩ : syracuseStep 165357383 = 248036075) B248036075
theorem B1812989 : Blo 562809 1812989 := bstep (se 3 (by rfl) ⟨339935, by rfl⟩ : syracuseStep 1812989 = 679871) B679871
theorem B1911599 : Blo 562809 1911599 := bstep (se 1 (by rfl) ⟨1433699, by rfl⟩ : syracuseStep 1911599 = 2867399) B2867399
theorem B5778647 : Blo 562809 5778647 := bstep (se 1 (by rfl) ⟨4333985, by rfl⟩ : syracuseStep 5778647 = 8667971) B8667971
theorem B2143655 : Blo 562809 2143655 := bstep (se 1 (by rfl) ⟨1607741, by rfl⟩ : syracuseStep 2143655 = 3215483) B3215483
theorem B10860095 : Blo 562809 10860095 := bstep (se 1 (by rfl) ⟨8145071, by rfl⟩ : syracuseStep 10860095 = 16290143) B16290143
theorem B27441179 : Blo 562809 27441179 := bstep (se 1 (by rfl) ⟨20580884, by rfl⟩ : syracuseStep 27441179 = 41161769) B41161769
theorem B1267739 : Blo 562809 1267739 := bstep (se 1 (by rfl) ⟨950804, by rfl⟩ : syracuseStep 1267739 = 1901609) B1901609
theorem B844871 : Blo 562809 844871 := bstep (se 1 (by rfl) ⟨633653, by rfl⟩ : syracuseStep 844871 = 1267307) B1267307
theorem B49408157 : Blo 562809 49408157 := bstep (se 3 (by rfl) ⟨9264029, by rfl⟩ : syracuseStep 49408157 = 18528059) B18528059
theorem B1207019 : Blo 562809 1207019 := bstep (se 1 (by rfl) ⟨905264, by rfl⟩ : syracuseStep 1207019 = 1810529) B1810529
theorem B847943 : Blo 562809 847943 := bstep (se 1 (by rfl) ⟨635957, by rfl⟩ : syracuseStep 847943 = 1271915) B1271915
theorem B4583911 : Blo 562809 4583911 := bstep (se 1 (by rfl) ⟨3437933, by rfl⟩ : syracuseStep 4583911 = 6875867) B6875867
theorem B849359 : Blo 562809 849359 := bstep (se 1 (by rfl) ⟨637019, by rfl⟩ : syracuseStep 849359 = 1274039) B1274039
theorem B1899503 : Blo 562809 1899503 := bstep (se 1 (by rfl) ⟨1424627, by rfl⟩ : syracuseStep 1899503 = 2849255) B2849255
theorem B1899935 : Blo 562809 1899935 := bstep (se 1 (by rfl) ⟨1424951, by rfl⟩ : syracuseStep 1899935 = 2849903) B2849903
theorem B24509951 : Blo 562809 24509951 := bstep (se 1 (by rfl) ⟨18382463, by rfl⟩ : syracuseStep 24509951 = 36764927) B36764927
theorem B1605167 : Blo 562809 1605167 := bstep (se 1 (by rfl) ⟨1203875, by rfl⟩ : syracuseStep 1605167 = 2407751) B2407751
theorem B563247 : Blo 562809 563247 := bstep (se 1 (by rfl) ⟨422435, by rfl⟩ : syracuseStep 563247 = 844871) B844871
theorem B3218717 : Blo 562809 3218717 := bstep (se 3 (by rfl) ⟨603509, by rfl⟩ : syracuseStep 3218717 = 1207019) B1207019
theorem B565295 : Blo 562809 565295 := bstep (se 1 (by rfl) ⟨423971, by rfl⟩ : syracuseStep 565295 = 847943) B847943
theorem B566239 : Blo 562809 566239 := bstep (se 1 (by rfl) ⟨424679, by rfl⟩ : syracuseStep 566239 = 849359) B849359
theorem B18294119 : Blo 562809 18294119 := bstep (se 1 (by rfl) ⟨13720589, by rfl⟩ : syracuseStep 18294119 = 27441179) B27441179
theorem B149074667 : Blo 562809 149074667 := bstep (se 1 (by rfl) ⟨111806000, by rfl⟩ : syracuseStep 149074667 = 223612001) B223612001
theorem B1291079 : Blo 562809 1291079 := bstep (se 1 (by rfl) ⟨968309, by rfl⟩ : syracuseStep 1291079 = 1936619) B1936619
theorem B6111881 : Blo 562809 6111881 := bstep (se 2 (by rfl) ⟨2291955, by rfl⟩ : syracuseStep 6111881 = 4583911) B4583911
theorem B4834637 : Blo 562809 4834637 := bstep (se 3 (by rfl) ⟨906494, by rfl⟩ : syracuseStep 4834637 = 1812989) B1812989
theorem B3852431 : Blo 562809 3852431 := bstep (se 1 (by rfl) ⟨2889323, by rfl⟩ : syracuseStep 3852431 = 5778647) B5778647
theorem B1429103 : Blo 562809 1429103 := bstep (se 1 (by rfl) ⟨1071827, by rfl⟩ : syracuseStep 1429103 = 2143655) B2143655
theorem B1266335 : Blo 562809 1266335 := bstep (se 1 (by rfl) ⟨949751, by rfl⟩ : syracuseStep 1266335 = 1899503) B1899503
theorem B1266623 : Blo 562809 1266623 := bstep (se 1 (by rfl) ⟨949967, by rfl⟩ : syracuseStep 1266623 = 1899935) B1899935
theorem B16339967 : Blo 562809 16339967 := bstep (se 1 (by rfl) ⟨12254975, by rfl⟩ : syracuseStep 16339967 = 24509951) B24509951
theorem B1070111 : Blo 562809 1070111 := bstep (se 1 (by rfl) ⟨802583, by rfl⟩ : syracuseStep 1070111 = 1605167) B1605167
theorem B1203731 : Blo 562809 1203731 := bstep (se 1 (by rfl) ⟨902798, by rfl⟩ : syracuseStep 1203731 = 1805597) B1805597
theorem B845159 : Blo 562809 845159 := bstep (se 1 (by rfl) ⟨633869, by rfl⟩ : syracuseStep 845159 = 1267739) B1267739
theorem B440953021 : Blo 562809 440953021 := bstep (se 3 (by rfl) ⟨82678691, by rfl⟩ : syracuseStep 440953021 = 165357383) B165357383
theorem B131755085 : Blo 562809 131755085 := bstep (se 3 (by rfl) ⟨24704078, by rfl⟩ : syracuseStep 131755085 = 49408157) B49408157
theorem B1274399 : Blo 562809 1274399 := bstep (se 1 (by rfl) ⟨955799, by rfl⟩ : syracuseStep 1274399 = 1911599) B1911599
theorem B7240063 : Blo 562809 7240063 := bstep (se 1 (by rfl) ⟨5430047, by rfl⟩ : syracuseStep 7240063 = 10860095) B10860095
theorem B952735 : Blo 562809 952735 := bstep (se 1 (by rfl) ⟨714551, by rfl⟩ : syracuseStep 952735 = 1429103) B1429103
theorem B2853629 : Blo 562809 2853629 := bstep (se 3 (by rfl) ⟨535055, by rfl⟩ : syracuseStep 2853629 = 1070111) B1070111
theorem B563439 : Blo 562809 563439 := bstep (se 1 (by rfl) ⟨422579, by rfl⟩ : syracuseStep 563439 = 845159) B845159
theorem B12196079 : Blo 562809 12196079 := bstep (se 1 (by rfl) ⟨9147059, by rfl⟩ : syracuseStep 12196079 = 18294119) B18294119
theorem B860719 : Blo 562809 860719 := bstep (se 1 (by rfl) ⟨645539, by rfl⟩ : syracuseStep 860719 = 1291079) B1291079
theorem B4074587 : Blo 562809 4074587 := bstep (se 1 (by rfl) ⟨3055940, by rfl⟩ : syracuseStep 4074587 = 6111881) B6111881
theorem B3223091 : Blo 562809 3223091 := bstep (se 1 (by rfl) ⟨2417318, by rfl⟩ : syracuseStep 3223091 = 4834637) B4834637
theorem B2568287 : Blo 562809 2568287 := bstep (se 1 (by rfl) ⟨1926215, by rfl⟩ : syracuseStep 2568287 = 3852431) B3852431
theorem B587937361 : Blo 562809 587937361 := bstep (se 2 (by rfl) ⟨220476510, by rfl⟩ : syracuseStep 587937361 = 440953021) B440953021
theorem B10893311 : Blo 562809 10893311 := bstep (se 1 (by rfl) ⟨8169983, by rfl⟩ : syracuseStep 10893311 = 16339967) B16339967
theorem B2145811 : Blo 562809 2145811 := bstep (se 1 (by rfl) ⟨1609358, by rfl⟩ : syracuseStep 2145811 = 3218717) B3218717
theorem B802487 : Blo 562809 802487 := bstep (se 1 (by rfl) ⟨601865, by rfl⟩ : syracuseStep 802487 = 1203731) B1203731
theorem B87836723 : Blo 562809 87836723 := bstep (se 1 (by rfl) ⟨65877542, by rfl⟩ : syracuseStep 87836723 = 131755085) B131755085
theorem B9653417 : Blo 562809 9653417 := bstep (se 2 (by rfl) ⟨3620031, by rfl⟩ : syracuseStep 9653417 = 7240063) B7240063
theorem B844223 : Blo 562809 844223 := bstep (se 1 (by rfl) ⟨633167, by rfl⟩ : syracuseStep 844223 = 1266335) B1266335
theorem B844415 : Blo 562809 844415 := bstep (se 1 (by rfl) ⟨633311, by rfl⟩ : syracuseStep 844415 = 1266623) B1266623
theorem B849599 : Blo 562809 849599 := bstep (se 1 (by rfl) ⟨637199, by rfl⟩ : syracuseStep 849599 = 1274399) B1274399
theorem B99383111 : Blo 562809 99383111 := bstep (se 1 (by rfl) ⟨74537333, by rfl⟩ : syracuseStep 99383111 = 149074667) B149074667
theorem B1147625 : Blo 562809 1147625 := bstep (se 2 (by rfl) ⟨430359, by rfl⟩ : syracuseStep 1147625 = 860719) B860719
theorem B58557815 : Blo 562809 58557815 := bstep (se 1 (by rfl) ⟨43918361, by rfl⟩ : syracuseStep 58557815 = 87836723) B87836723
theorem B1902419 : Blo 562809 1902419 := bstep (se 1 (by rfl) ⟨1426814, by rfl⟩ : syracuseStep 1902419 = 2853629) B2853629
theorem B8130719 : Blo 562809 8130719 := bstep (se 1 (by rfl) ⟨6098039, by rfl⟩ : syracuseStep 8130719 = 12196079) B12196079
theorem B562815 : Blo 562809 562815 := bstep (se 1 (by rfl) ⟨422111, by rfl⟩ : syracuseStep 562815 = 844223) B844223
theorem B562943 : Blo 562809 562943 := bstep (se 1 (by rfl) ⟨422207, by rfl⟩ : syracuseStep 562943 = 844415) B844415
theorem B783916481 : Blo 562809 783916481 := bstep (se 2 (by rfl) ⟨293968680, by rfl⟩ : syracuseStep 783916481 = 587937361) B587937361
theorem B1712191 : Blo 562809 1712191 := bstep (se 1 (by rfl) ⟨1284143, by rfl⟩ : syracuseStep 1712191 = 2568287) B2568287
theorem B566399 : Blo 562809 566399 := bstep (se 1 (by rfl) ⟨424799, by rfl⟩ : syracuseStep 566399 = 849599) B849599
theorem B2139965 : Blo 562809 2139965 := bstep (se 3 (by rfl) ⟨401243, by rfl⟩ : syracuseStep 2139965 = 802487) B802487
theorem B2861081 : Blo 562809 2861081 := bstep (se 2 (by rfl) ⟨1072905, by rfl⟩ : syracuseStep 2861081 = 2145811) B2145811
theorem B6435611 : Blo 562809 6435611 := bstep (se 1 (by rfl) ⟨4826708, by rfl⟩ : syracuseStep 6435611 = 9653417) B9653417
theorem B2148727 : Blo 562809 2148727 := bstep (se 1 (by rfl) ⟨1611545, by rfl⟩ : syracuseStep 2148727 = 3223091) B3223091
theorem B7262207 : Blo 562809 7262207 := bstep (se 1 (by rfl) ⟨5446655, by rfl⟩ : syracuseStep 7262207 = 10893311) B10893311
theorem B1270313 : Blo 562809 1270313 := bstep (se 2 (by rfl) ⟨476367, by rfl⟩ : syracuseStep 1270313 = 952735) B952735
theorem B2716391 : Blo 562809 2716391 := bstep (se 1 (by rfl) ⟨2037293, by rfl⟩ : syracuseStep 2716391 = 4074587) B4074587
theorem B66255407 : Blo 562809 66255407 := bstep (se 1 (by rfl) ⟨49691555, by rfl⟩ : syracuseStep 66255407 = 99383111) B99383111
theorem B1907387 : Blo 562809 1907387 := bstep (se 1 (by rfl) ⟨1430540, by rfl⟩ : syracuseStep 1907387 = 2861081) B2861081
theorem B1810927 : Blo 562809 1810927 := bstep (se 1 (by rfl) ⟨1358195, by rfl⟩ : syracuseStep 1810927 = 2716391) B2716391
theorem B765083 : Blo 562809 765083 := bstep (se 1 (by rfl) ⟨573812, by rfl⟩ : syracuseStep 765083 = 1147625) B1147625
theorem B39038543 : Blo 562809 39038543 := bstep (se 1 (by rfl) ⟨29278907, by rfl⟩ : syracuseStep 39038543 = 58557815) B58557815
theorem B5420479 : Blo 562809 5420479 := bstep (se 1 (by rfl) ⟨4065359, by rfl⟩ : syracuseStep 5420479 = 8130719) B8130719
theorem B2864969 : Blo 562809 2864969 := bstep (se 2 (by rfl) ⟨1074363, by rfl⟩ : syracuseStep 2864969 = 2148727) B2148727
theorem B1426643 : Blo 562809 1426643 := bstep (se 1 (by rfl) ⟨1069982, by rfl⟩ : syracuseStep 1426643 = 2139965) B2139965
theorem B2282921 : Blo 562809 2282921 := bstep (se 2 (by rfl) ⟨856095, by rfl⟩ : syracuseStep 2282921 = 1712191) B1712191
theorem B1268279 : Blo 562809 1268279 := bstep (se 1 (by rfl) ⟨951209, by rfl⟩ : syracuseStep 1268279 = 1902419) B1902419
theorem B4841471 : Blo 562809 4841471 := bstep (se 1 (by rfl) ⟨3631103, by rfl⟩ : syracuseStep 4841471 = 7262207) B7262207
theorem B522610987 : Blo 562809 522610987 := bstep (se 1 (by rfl) ⟨391958240, by rfl⟩ : syracuseStep 522610987 = 783916481) B783916481
theorem B846875 : Blo 562809 846875 := bstep (se 1 (by rfl) ⟨635156, by rfl⟩ : syracuseStep 846875 = 1270313) B1270313
theorem B4290407 : Blo 562809 4290407 := bstep (se 1 (by rfl) ⟨3217805, by rfl⟩ : syracuseStep 4290407 = 6435611) B6435611
theorem B44170271 : Blo 562809 44170271 := bstep (se 1 (by rfl) ⟨33127703, by rfl⟩ : syracuseStep 44170271 = 66255407) B66255407
theorem B951095 : Blo 562809 951095 := bstep (se 1 (by rfl) ⟨713321, by rfl⟩ : syracuseStep 951095 = 1426643) B1426643
theorem B696814649 : Blo 562809 696814649 := bstep (se 2 (by rfl) ⟨261305493, by rfl⟩ : syracuseStep 696814649 = 522610987) B522610987
theorem B564583 : Blo 562809 564583 := bstep (se 1 (by rfl) ⟨423437, by rfl⟩ : syracuseStep 564583 = 846875) B846875
theorem B26025695 : Blo 562809 26025695 := bstep (se 1 (by rfl) ⟨19519271, by rfl⟩ : syracuseStep 26025695 = 39038543) B39038543
theorem B2040221 : Blo 562809 2040221 := bstep (se 3 (by rfl) ⟨382541, by rfl⟩ : syracuseStep 2040221 = 765083) B765083
theorem B1909979 : Blo 562809 1909979 := bstep (se 1 (by rfl) ⟨1432484, by rfl⟩ : syracuseStep 1909979 = 2864969) B2864969
theorem B2860271 : Blo 562809 2860271 := bstep (se 1 (by rfl) ⟨2145203, by rfl⟩ : syracuseStep 2860271 = 4290407) B4290407
theorem B1521947 : Blo 562809 1521947 := bstep (se 1 (by rfl) ⟨1141460, by rfl⟩ : syracuseStep 1521947 = 2282921) B2282921
theorem B3227647 : Blo 562809 3227647 := bstep (se 1 (by rfl) ⟨2420735, by rfl⟩ : syracuseStep 3227647 = 4841471) B4841471
theorem B7227305 : Blo 562809 7227305 := bstep (se 2 (by rfl) ⟨2710239, by rfl⟩ : syracuseStep 7227305 = 5420479) B5420479
theorem B29446847 : Blo 562809 29446847 := bstep (se 1 (by rfl) ⟨22085135, by rfl⟩ : syracuseStep 29446847 = 44170271) B44170271
theorem B2414569 : Blo 562809 2414569 := bstep (se 2 (by rfl) ⟨905463, by rfl⟩ : syracuseStep 2414569 = 1810927) B1810927
theorem B845519 : Blo 562809 845519 := bstep (se 1 (by rfl) ⟨634139, by rfl⟩ : syracuseStep 845519 = 1268279) B1268279
theorem B1271591 : Blo 562809 1271591 := bstep (se 1 (by rfl) ⟨953693, by rfl⟩ : syracuseStep 1271591 = 1907387) B1907387
theorem B4818203 : Blo 562809 4818203 := bstep (se 1 (by rfl) ⟨3613652, by rfl⟩ : syracuseStep 4818203 = 7227305) B7227305
theorem B19631231 : Blo 562809 19631231 := bstep (se 1 (by rfl) ⟨14723423, by rfl⟩ : syracuseStep 19631231 = 29446847) B29446847
theorem B1906847 : Blo 562809 1906847 := bstep (se 1 (by rfl) ⟨1430135, by rfl⟩ : syracuseStep 1906847 = 2860271) B2860271
theorem B563679 : Blo 562809 563679 := bstep (se 1 (by rfl) ⟨422759, by rfl⟩ : syracuseStep 563679 = 845519) B845519
theorem B3219425 : Blo 562809 3219425 := bstep (se 2 (by rfl) ⟨1207284, by rfl⟩ : syracuseStep 3219425 = 2414569) B2414569
theorem B4303529 : Blo 562809 4303529 := bstep (se 2 (by rfl) ⟨1613823, by rfl⟩ : syracuseStep 4303529 = 3227647) B3227647
theorem B634063 : Blo 562809 634063 := bstep (se 1 (by rfl) ⟨475547, by rfl⟩ : syracuseStep 634063 = 951095) B951095
theorem B17350463 : Blo 562809 17350463 := bstep (se 1 (by rfl) ⟨13012847, by rfl⟩ : syracuseStep 17350463 = 26025695) B26025695
theorem B1360147 : Blo 562809 1360147 := bstep (se 1 (by rfl) ⟨1020110, by rfl⟩ : syracuseStep 1360147 = 2040221) B2040221
theorem B464543099 : Blo 562809 464543099 := bstep (se 1 (by rfl) ⟨348407324, by rfl⟩ : syracuseStep 464543099 = 696814649) B696814649
theorem B4058525 : Blo 562809 4058525 := bstep (se 3 (by rfl) ⟨760973, by rfl⟩ : syracuseStep 4058525 = 1521947) B1521947
theorem B1273319 : Blo 562809 1273319 := bstep (se 1 (by rfl) ⟨954989, by rfl⟩ : syracuseStep 1273319 = 1909979) B1909979
theorem B847727 : Blo 562809 847727 := bstep (se 1 (by rfl) ⟨635795, by rfl⟩ : syracuseStep 847727 = 1271591) B1271591
theorem B3212135 : Blo 562809 3212135 := bstep (se 1 (by rfl) ⟨2409101, by rfl⟩ : syracuseStep 3212135 = 4818203) B4818203
theorem B309695399 : Blo 562809 309695399 := bstep (se 1 (by rfl) ⟨232271549, by rfl⟩ : syracuseStep 309695399 = 464543099) B464543099
theorem B565151 : Blo 562809 565151 := bstep (se 1 (by rfl) ⟨423863, by rfl⟩ : syracuseStep 565151 = 847727) B847727
theorem B10822733 : Blo 562809 10822733 := bstep (se 3 (by rfl) ⟨2029262, by rfl⟩ : syracuseStep 10822733 = 4058525) B4058525
theorem B1813529 : Blo 562809 1813529 := bstep (se 2 (by rfl) ⟨680073, by rfl⟩ : syracuseStep 1813529 = 1360147) B1360147
theorem B13087487 : Blo 562809 13087487 := bstep (se 1 (by rfl) ⟨9815615, by rfl⟩ : syracuseStep 13087487 = 19631231) B19631231
theorem B2146283 : Blo 562809 2146283 := bstep (se 1 (by rfl) ⟨1609712, by rfl⟩ : syracuseStep 2146283 = 3219425) B3219425
theorem B2869019 : Blo 562809 2869019 := bstep (se 1 (by rfl) ⟨2151764, by rfl⟩ : syracuseStep 2869019 = 4303529) B4303529
theorem B1271231 : Blo 562809 1271231 := bstep (se 1 (by rfl) ⟨953423, by rfl⟩ : syracuseStep 1271231 = 1906847) B1906847
theorem B845417 : Blo 562809 845417 := bstep (se 2 (by rfl) ⟨317031, by rfl⟩ : syracuseStep 845417 = 634063) B634063
theorem B848879 : Blo 562809 848879 := bstep (se 1 (by rfl) ⟨636659, by rfl⟩ : syracuseStep 848879 = 1273319) B1273319
theorem B11566975 : Blo 562809 11566975 := bstep (se 1 (by rfl) ⟨8675231, by rfl⟩ : syracuseStep 11566975 = 17350463) B17350463
theorem B7215155 : Blo 562809 7215155 := bstep (se 1 (by rfl) ⟨5411366, by rfl⟩ : syracuseStep 7215155 = 10822733) B10822733
theorem B563611 : Blo 562809 563611 := bstep (se 1 (by rfl) ⟨422708, by rfl⟩ : syracuseStep 563611 = 845417) B845417
theorem B8724991 : Blo 562809 8724991 := bstep (se 1 (by rfl) ⟨6543743, by rfl⟩ : syracuseStep 8724991 = 13087487) B13087487
theorem B565919 : Blo 562809 565919 := bstep (se 1 (by rfl) ⟨424439, by rfl⟩ : syracuseStep 565919 = 848879) B848879
theorem B2141423 : Blo 562809 2141423 := bstep (se 1 (by rfl) ⟨1606067, by rfl⟩ : syracuseStep 2141423 = 3212135) B3212135
theorem B1912679 : Blo 562809 1912679 := bstep (se 1 (by rfl) ⟨1434509, by rfl⟩ : syracuseStep 1912679 = 2869019) B2869019
theorem B15422633 : Blo 562809 15422633 := bstep (se 2 (by rfl) ⟨5783487, by rfl⟩ : syracuseStep 15422633 = 11566975) B11566975
theorem B1430855 : Blo 562809 1430855 := bstep (se 1 (by rfl) ⟨1073141, by rfl⟩ : syracuseStep 1430855 = 2146283) B2146283
theorem B206463599 : Blo 562809 206463599 := bstep (se 1 (by rfl) ⟨154847699, by rfl⟩ : syracuseStep 206463599 = 309695399) B309695399
theorem B847487 : Blo 562809 847487 := bstep (se 1 (by rfl) ⟨635615, by rfl⟩ : syracuseStep 847487 = 1271231) B1271231
theorem B1209019 : Blo 562809 1209019 := bstep (se 1 (by rfl) ⟨906764, by rfl⟩ : syracuseStep 1209019 = 1813529) B1813529
theorem B11633321 : Blo 562809 11633321 := bstep (se 2 (by rfl) ⟨4362495, by rfl⟩ : syracuseStep 11633321 = 8724991) B8724991
theorem B953903 : Blo 562809 953903 := bstep (se 1 (by rfl) ⟨715427, by rfl⟩ : syracuseStep 953903 = 1430855) B1430855
theorem B1612025 : Blo 562809 1612025 := bstep (se 2 (by rfl) ⟨604509, by rfl⟩ : syracuseStep 1612025 = 1209019) B1209019
theorem B564991 : Blo 562809 564991 := bstep (se 1 (by rfl) ⟨423743, by rfl⟩ : syracuseStep 564991 = 847487) B847487
theorem B137642399 : Blo 562809 137642399 := bstep (se 1 (by rfl) ⟨103231799, by rfl⟩ : syracuseStep 137642399 = 206463599) B206463599
theorem B1427615 : Blo 562809 1427615 := bstep (se 1 (by rfl) ⟨1070711, by rfl⟩ : syracuseStep 1427615 = 2141423) B2141423
theorem B10281755 : Blo 562809 10281755 := bstep (se 1 (by rfl) ⟨7711316, by rfl⟩ : syracuseStep 10281755 = 15422633) B15422633
theorem B4810103 : Blo 562809 4810103 := bstep (se 1 (by rfl) ⟨3607577, by rfl⟩ : syracuseStep 4810103 = 7215155) B7215155
theorem B1275119 : Blo 562809 1275119 := bstep (se 1 (by rfl) ⟨956339, by rfl⟩ : syracuseStep 1275119 = 1912679) B1912679
theorem B951743 : Blo 562809 951743 := bstep (se 1 (by rfl) ⟨713807, by rfl⟩ : syracuseStep 951743 = 1427615) B1427615
theorem B6854503 : Blo 562809 6854503 := bstep (se 1 (by rfl) ⟨5140877, by rfl⟩ : syracuseStep 6854503 = 10281755) B10281755
theorem B91761599 : Blo 562809 91761599 := bstep (se 1 (by rfl) ⟨68821199, by rfl⟩ : syracuseStep 91761599 = 137642399) B137642399
theorem B635935 : Blo 562809 635935 := bstep (se 1 (by rfl) ⟨476951, by rfl⟩ : syracuseStep 635935 = 953903) B953903
theorem B7755547 : Blo 562809 7755547 := bstep (se 1 (by rfl) ⟨5816660, by rfl⟩ : syracuseStep 7755547 = 11633321) B11633321
theorem B1074683 : Blo 562809 1074683 := bstep (se 1 (by rfl) ⟨806012, by rfl⟩ : syracuseStep 1074683 = 1612025) B1612025
theorem B3206735 : Blo 562809 3206735 := bstep (se 1 (by rfl) ⟨2405051, by rfl⟩ : syracuseStep 3206735 = 4810103) B4810103
theorem B850079 : Blo 562809 850079 := bstep (se 1 (by rfl) ⟨637559, by rfl⟩ : syracuseStep 850079 = 1275119) B1275119
theorem B2137823 : Blo 562809 2137823 := bstep (se 1 (by rfl) ⟨1603367, by rfl⟩ : syracuseStep 2137823 = 3206735) B3206735
theorem B566719 : Blo 562809 566719 := bstep (se 1 (by rfl) ⟨425039, by rfl⟩ : syracuseStep 566719 = 850079) B850079
theorem B634495 : Blo 562809 634495 := bstep (se 1 (by rfl) ⟨475871, by rfl⟩ : syracuseStep 634495 = 951743) B951743
theorem B10340729 : Blo 562809 10340729 := bstep (se 2 (by rfl) ⟨3877773, by rfl⟩ : syracuseStep 10340729 = 7755547) B7755547
theorem B716455 : Blo 562809 716455 := bstep (se 1 (by rfl) ⟨537341, by rfl⟩ : syracuseStep 716455 = 1074683) B1074683
theorem B847913 : Blo 562809 847913 := bstep (se 2 (by rfl) ⟨317967, by rfl⟩ : syracuseStep 847913 = 635935) B635935
theorem B61174399 : Blo 562809 61174399 := bstep (se 1 (by rfl) ⟨45880799, by rfl⟩ : syracuseStep 61174399 = 91761599) B91761599
theorem B9139337 : Blo 562809 9139337 := bstep (se 2 (by rfl) ⟨3427251, by rfl⟩ : syracuseStep 9139337 = 6854503) B6854503
theorem B955273 : Blo 562809 955273 := bstep (se 2 (by rfl) ⟨358227, by rfl⟩ : syracuseStep 955273 = 716455) B716455
theorem B81565865 : Blo 562809 81565865 := bstep (se 2 (by rfl) ⟨30587199, by rfl⟩ : syracuseStep 81565865 = 61174399) B61174399
theorem B565275 : Blo 562809 565275 := bstep (se 1 (by rfl) ⟨423956, by rfl⟩ : syracuseStep 565275 = 847913) B847913
theorem B6893819 : Blo 562809 6893819 := bstep (se 1 (by rfl) ⟨5170364, by rfl⟩ : syracuseStep 6893819 = 10340729) B10340729
theorem B1425215 : Blo 562809 1425215 := bstep (se 1 (by rfl) ⟨1068911, by rfl⟩ : syracuseStep 1425215 = 2137823) B2137823
theorem B845993 : Blo 562809 845993 := bstep (se 2 (by rfl) ⟨317247, by rfl⟩ : syracuseStep 845993 = 634495) B634495
theorem B6092891 : Blo 562809 6092891 := bstep (se 1 (by rfl) ⟨4569668, by rfl⟩ : syracuseStep 6092891 = 9139337) B9139337
theorem B563995 : Blo 562809 563995 := bstep (se 1 (by rfl) ⟨422996, by rfl⟩ : syracuseStep 563995 = 845993) B845993
theorem B4595879 : Blo 562809 4595879 := bstep (se 1 (by rfl) ⟨3446909, by rfl⟩ : syracuseStep 4595879 = 6893819) B6893819
theorem B54377243 : Blo 562809 54377243 := bstep (se 1 (by rfl) ⟨40782932, by rfl⟩ : syracuseStep 54377243 = 81565865) B81565865
theorem B1273697 : Blo 562809 1273697 := bstep (se 2 (by rfl) ⟨477636, by rfl⟩ : syracuseStep 1273697 = 955273) B955273
theorem B4061927 : Blo 562809 4061927 := bstep (se 1 (by rfl) ⟨3046445, by rfl⟩ : syracuseStep 4061927 = 6092891) B6092891
theorem B950143 : Blo 562809 950143 := bstep (se 1 (by rfl) ⟨712607, by rfl⟩ : syracuseStep 950143 = 1425215) B1425215
theorem B36251495 : Blo 562809 36251495 := bstep (se 1 (by rfl) ⟨27188621, by rfl⟩ : syracuseStep 36251495 = 54377243) B54377243
theorem B3063919 : Blo 562809 3063919 := bstep (se 1 (by rfl) ⟨2297939, by rfl⟩ : syracuseStep 3063919 = 4595879) B4595879
theorem B2707951 : Blo 562809 2707951 := bstep (se 1 (by rfl) ⟨2030963, by rfl⟩ : syracuseStep 2707951 = 4061927) B4061927
theorem B1266857 : Blo 562809 1266857 := bstep (se 2 (by rfl) ⟨475071, by rfl⟩ : syracuseStep 1266857 = 950143) B950143
theorem B849131 : Blo 562809 849131 := bstep (se 1 (by rfl) ⟨636848, by rfl⟩ : syracuseStep 849131 = 1273697) B1273697
theorem B3610601 : Blo 562809 3610601 := bstep (se 2 (by rfl) ⟨1353975, by rfl⟩ : syracuseStep 3610601 = 2707951) B2707951
theorem B566087 : Blo 562809 566087 := bstep (se 1 (by rfl) ⟨424565, by rfl⟩ : syracuseStep 566087 = 849131) B849131
theorem B24167663 : Blo 562809 24167663 := bstep (se 1 (by rfl) ⟨18125747, by rfl⟩ : syracuseStep 24167663 = 36251495) B36251495
theorem B4085225 : Blo 562809 4085225 := bstep (se 2 (by rfl) ⟨1531959, by rfl⟩ : syracuseStep 4085225 = 3063919) B3063919
theorem B844571 : Blo 562809 844571 := bstep (se 1 (by rfl) ⟨633428, by rfl⟩ : syracuseStep 844571 = 1266857) B1266857
theorem B2723483 : Blo 562809 2723483 := bstep (se 1 (by rfl) ⟨2042612, by rfl⟩ : syracuseStep 2723483 = 4085225) B4085225
theorem B563047 : Blo 562809 563047 := bstep (se 1 (by rfl) ⟨422285, by rfl⟩ : syracuseStep 563047 = 844571) B844571
theorem B2407067 : Blo 562809 2407067 := bstep (se 1 (by rfl) ⟨1805300, by rfl⟩ : syracuseStep 2407067 = 3610601) B3610601
theorem B16111775 : Blo 562809 16111775 := bstep (se 1 (by rfl) ⟨12083831, by rfl⟩ : syracuseStep 16111775 = 24167663) B24167663
theorem B1815655 : Blo 562809 1815655 := bstep (se 1 (by rfl) ⟨1361741, by rfl⟩ : syracuseStep 1815655 = 2723483) B2723483
theorem B10741183 : Blo 562809 10741183 := bstep (se 1 (by rfl) ⟨8055887, by rfl⟩ : syracuseStep 10741183 = 16111775) B16111775
theorem B1604711 : Blo 562809 1604711 := bstep (se 1 (by rfl) ⟨1203533, by rfl⟩ : syracuseStep 1604711 = 2407067) B2407067
theorem B57286309 : Blo 562809 57286309 := bstep (se 4 (by rfl) ⟨5370591, by rfl⟩ : syracuseStep 57286309 = 10741183) B10741183
theorem B4279229 : Blo 562809 4279229 := bstep (se 3 (by rfl) ⟨802355, by rfl⟩ : syracuseStep 4279229 = 1604711) B1604711
theorem B2420873 : Blo 562809 2420873 := bstep (se 2 (by rfl) ⟨907827, by rfl⟩ : syracuseStep 2420873 = 1815655) B1815655
theorem B2852819 : Blo 562809 2852819 := bstep (se 1 (by rfl) ⟨2139614, by rfl⟩ : syracuseStep 2852819 = 4279229) B4279229
theorem B1613915 : Blo 562809 1613915 := bstep (se 1 (by rfl) ⟨1210436, by rfl⟩ : syracuseStep 1613915 = 2420873) B2420873
theorem B76381745 : Blo 562809 76381745 := bstep (se 2 (by rfl) ⟨28643154, by rfl⟩ : syracuseStep 76381745 = 57286309) B57286309
theorem B1901879 : Blo 562809 1901879 := bstep (se 1 (by rfl) ⟨1426409, by rfl⟩ : syracuseStep 1901879 = 2852819) B2852819
theorem B1075943 : Blo 562809 1075943 := bstep (se 1 (by rfl) ⟨806957, by rfl⟩ : syracuseStep 1075943 = 1613915) B1613915
theorem B203684653 : Blo 562809 203684653 := bstep (se 3 (by rfl) ⟨38190872, by rfl⟩ : syracuseStep 203684653 = 76381745) B76381745
theorem B2869181 : Blo 562809 2869181 := bstep (se 3 (by rfl) ⟨537971, by rfl⟩ : syracuseStep 2869181 = 1075943) B1075943
theorem B1267919 : Blo 562809 1267919 := bstep (se 1 (by rfl) ⟨950939, by rfl⟩ : syracuseStep 1267919 = 1901879) B1901879
theorem B271579537 : Blo 562809 271579537 := bstep (se 2 (by rfl) ⟨101842326, by rfl⟩ : syracuseStep 271579537 = 203684653) B203684653
theorem B1912787 : Blo 562809 1912787 := bstep (se 1 (by rfl) ⟨1434590, by rfl⟩ : syracuseStep 1912787 = 2869181) B2869181
theorem B362106049 : Blo 562809 362106049 := bstep (se 2 (by rfl) ⟨135789768, by rfl⟩ : syracuseStep 362106049 = 271579537) B271579537
theorem B845279 : Blo 562809 845279 := bstep (se 1 (by rfl) ⟨633959, by rfl⟩ : syracuseStep 845279 = 1267919) B1267919
theorem B482808065 : Blo 562809 482808065 := bstep (se 2 (by rfl) ⟨181053024, by rfl⟩ : syracuseStep 482808065 = 362106049) B362106049
theorem B563519 : Blo 562809 563519 := bstep (se 1 (by rfl) ⟨422639, by rfl⟩ : syracuseStep 563519 = 845279) B845279
theorem B1275191 : Blo 562809 1275191 := bstep (se 1 (by rfl) ⟨956393, by rfl⟩ : syracuseStep 1275191 = 1912787) B1912787
theorem B5149952693 : Blo 562809 5149952693 := bstep (se 5 (by rfl) ⟨241404032, by rfl⟩ : syracuseStep 5149952693 = 482808065) B482808065
theorem B850127 : Blo 562809 850127 := bstep (se 1 (by rfl) ⟨637595, by rfl⟩ : syracuseStep 850127 = 1275191) B1275191
theorem B3433301795 : Blo 562809 3433301795 := bstep (se 1 (by rfl) ⟨2574976346, by rfl⟩ : syracuseStep 3433301795 = 5149952693) B5149952693
theorem B566751 : Blo 562809 566751 := bstep (se 1 (by rfl) ⟨425063, by rfl⟩ : syracuseStep 566751 = 850127) B850127
theorem B2288867863 : Blo 562809 2288867863 := bstep (se 1 (by rfl) ⟨1716650897, by rfl⟩ : syracuseStep 2288867863 = 3433301795) B3433301795
theorem B3051823817 : Blo 562809 3051823817 := bstep (se 2 (by rfl) ⟨1144433931, by rfl⟩ : syracuseStep 3051823817 = 2288867863) B2288867863
theorem B8138196845 : Blo 562809 8138196845 := bstep (se 3 (by rfl) ⟨1525911908, by rfl⟩ : syracuseStep 8138196845 = 3051823817) B3051823817
theorem B5425464563 : Blo 562809 5425464563 := bstep (se 1 (by rfl) ⟨4069098422, by rfl⟩ : syracuseStep 5425464563 = 8138196845) B8138196845
theorem B3616976375 : Blo 562809 3616976375 := bstep (se 1 (by rfl) ⟨2712732281, by rfl⟩ : syracuseStep 3616976375 = 5425464563) B5425464563
theorem B2411317583 : Blo 562809 2411317583 := bstep (se 1 (by rfl) ⟨1808488187, by rfl⟩ : syracuseStep 2411317583 = 3616976375) B3616976375
theorem B1607545055 : Blo 562809 1607545055 := bstep (se 1 (by rfl) ⟨1205658791, by rfl⟩ : syracuseStep 1607545055 = 2411317583) B2411317583
theorem B1071696703 : Blo 562809 1071696703 := bstep (se 1 (by rfl) ⟨803772527, by rfl⟩ : syracuseStep 1071696703 = 1607545055) B1607545055
theorem B1428928937 : Blo 562809 1428928937 := bstep (se 2 (by rfl) ⟨535848351, by rfl⟩ : syracuseStep 1428928937 = 1071696703) B1071696703
theorem B952619291 : Blo 562809 952619291 := bstep (se 1 (by rfl) ⟨714464468, by rfl⟩ : syracuseStep 952619291 = 1428928937) B1428928937
theorem B635079527 : Blo 562809 635079527 := bstep (se 1 (by rfl) ⟨476309645, by rfl⟩ : syracuseStep 635079527 = 952619291) B952619291
theorem B423386351 : Blo 562809 423386351 := bstep (se 1 (by rfl) ⟨317539763, by rfl⟩ : syracuseStep 423386351 = 635079527) B635079527
theorem B282257567 : Blo 562809 282257567 := bstep (se 1 (by rfl) ⟨211693175, by rfl⟩ : syracuseStep 282257567 = 423386351) B423386351
theorem B188171711 : Blo 562809 188171711 := bstep (se 1 (by rfl) ⟨141128783, by rfl⟩ : syracuseStep 188171711 = 282257567) B282257567
theorem B125447807 : Blo 562809 125447807 := bstep (se 1 (by rfl) ⟨94085855, by rfl⟩ : syracuseStep 125447807 = 188171711) B188171711
theorem B83631871 : Blo 562809 83631871 := bstep (se 1 (by rfl) ⟨62723903, by rfl⟩ : syracuseStep 83631871 = 125447807) B125447807
theorem B446036645 : Blo 562809 446036645 := bstep (se 4 (by rfl) ⟨41815935, by rfl⟩ : syracuseStep 446036645 = 83631871) B83631871
theorem B297357763 : Blo 562809 297357763 := bstep (se 1 (by rfl) ⟨223018322, by rfl⟩ : syracuseStep 297357763 = 446036645) B446036645
theorem B396477017 : Blo 562809 396477017 := bstep (se 2 (by rfl) ⟨148678881, by rfl⟩ : syracuseStep 396477017 = 297357763) B297357763
theorem B264318011 : Blo 562809 264318011 := bstep (se 1 (by rfl) ⟨198238508, by rfl⟩ : syracuseStep 264318011 = 396477017) B396477017
theorem B176212007 : Blo 562809 176212007 := bstep (se 1 (by rfl) ⟨132159005, by rfl⟩ : syracuseStep 176212007 = 264318011) B264318011
theorem B117474671 : Blo 562809 117474671 := bstep (se 1 (by rfl) ⟨88106003, by rfl⟩ : syracuseStep 117474671 = 176212007) B176212007
theorem B313265789 : Blo 562809 313265789 := bstep (se 3 (by rfl) ⟨58737335, by rfl⟩ : syracuseStep 313265789 = 117474671) B117474671
theorem B208843859 : Blo 562809 208843859 := bstep (se 1 (by rfl) ⟨156632894, by rfl⟩ : syracuseStep 208843859 = 313265789) B313265789
theorem B139229239 : Blo 562809 139229239 := bstep (se 1 (by rfl) ⟨104421929, by rfl⟩ : syracuseStep 139229239 = 208843859) B208843859
theorem B185638985 : Blo 562809 185638985 := bstep (se 2 (by rfl) ⟨69614619, by rfl⟩ : syracuseStep 185638985 = 139229239) B139229239
theorem B123759323 : Blo 562809 123759323 := bstep (se 1 (by rfl) ⟨92819492, by rfl⟩ : syracuseStep 123759323 = 185638985) B185638985
theorem B82506215 : Blo 562809 82506215 := bstep (se 1 (by rfl) ⟨61879661, by rfl⟩ : syracuseStep 82506215 = 123759323) B123759323
theorem B55004143 : Blo 562809 55004143 := bstep (se 1 (by rfl) ⟨41253107, by rfl⟩ : syracuseStep 55004143 = 82506215) B82506215
theorem B73338857 : Blo 562809 73338857 := bstep (se 2 (by rfl) ⟨27502071, by rfl⟩ : syracuseStep 73338857 = 55004143) B55004143
theorem B48892571 : Blo 562809 48892571 := bstep (se 1 (by rfl) ⟨36669428, by rfl⟩ : syracuseStep 48892571 = 73338857) B73338857
theorem B32595047 : Blo 562809 32595047 := bstep (se 1 (by rfl) ⟨24446285, by rfl⟩ : syracuseStep 32595047 = 48892571) B48892571
theorem B21730031 : Blo 562809 21730031 := bstep (se 1 (by rfl) ⟨16297523, by rfl⟩ : syracuseStep 21730031 = 32595047) B32595047
theorem B14486687 : Blo 562809 14486687 := bstep (se 1 (by rfl) ⟨10865015, by rfl⟩ : syracuseStep 14486687 = 21730031) B21730031
theorem B9657791 : Blo 562809 9657791 := bstep (se 1 (by rfl) ⟨7243343, by rfl⟩ : syracuseStep 9657791 = 14486687) B14486687
theorem B6438527 : Blo 562809 6438527 := bstep (se 1 (by rfl) ⟨4828895, by rfl⟩ : syracuseStep 6438527 = 9657791) B9657791
theorem B4292351 : Blo 562809 4292351 := bstep (se 1 (by rfl) ⟨3219263, by rfl⟩ : syracuseStep 4292351 = 6438527) B6438527
theorem B2861567 : Blo 562809 2861567 := bstep (se 1 (by rfl) ⟨2146175, by rfl⟩ : syracuseStep 2861567 = 4292351) B4292351
theorem B1907711 : Blo 562809 1907711 := bstep (se 1 (by rfl) ⟨1430783, by rfl⟩ : syracuseStep 1907711 = 2861567) B2861567
theorem B1271807 : Blo 562809 1271807 := bstep (se 1 (by rfl) ⟨953855, by rfl⟩ : syracuseStep 1271807 = 1907711) B1907711
theorem B847871 : Blo 562809 847871 := bstep (se 1 (by rfl) ⟨635903, by rfl⟩ : syracuseStep 847871 = 1271807) B1271807
theorem B565247 : Blo 562809 565247 := bstep (se 1 (by rfl) ⟨423935, by rfl⟩ : syracuseStep 565247 = 847871) B847871

theorem C0 (j : ℕ) (h1 : 140702 ≤ j) (h2 : j ≤ 141401) : Blo 562809 (4 * j + 3) := by
  interval_cases j
  · exact B562811
  · exact B562815
  · exact B562819
  · exact B562823
  · exact B562827
  · exact B562831
  · exact B562835
  · exact B562839
  · exact B562843
  · exact B562847
  · exact B562851
  · exact B562855
  · exact B562859
  · exact B562863
  · exact B562867
  · exact B562871
  · exact B562875
  · exact B562879
  · exact B562883
  · exact B562887
  · exact B562891
  · exact B562895
  · exact B562899
  · exact B562903
  · exact B562907
  · exact B562911
  · exact B562915
  · exact B562919
  · exact B562923
  · exact B562927
  · exact B562931
  · exact B562935
  · exact B562939
  · exact B562943
  · exact B562947
  · exact B562951
  · exact B562955
  · exact B562959
  · exact B562963
  · exact B562967
  · exact B562971
  · exact B562975
  · exact B562979
  · exact B562983
  · exact B562987
  · exact B562991
  · exact B562995
  · exact B562999
  · exact B563003
  · exact B563007
  · exact B563011
  · exact B563015
  · exact B563019
  · exact B563023
  · exact B563027
  · exact B563031
  · exact B563035
  · exact B563039
  · exact B563043
  · exact B563047
  · exact B563051
  · exact B563055
  · exact B563059
  · exact B563063
  · exact B563067
  · exact B563071
  · exact B563075
  · exact B563079
  · exact B563083
  · exact B563087
  · exact B563091
  · exact B563095
  · exact B563099
  · exact B563103
  · exact B563107
  · exact B563111
  · exact B563115
  · exact B563119
  · exact B563123
  · exact B563127
  · exact B563131
  · exact B563135
  · exact B563139
  · exact B563143
  · exact B563147
  · exact B563151
  · exact B563155
  · exact B563159
  · exact B563163
  · exact B563167
  · exact B563171
  · exact B563175
  · exact B563179
  · exact B563183
  · exact B563187
  · exact B563191
  · exact B563195
  · exact B563199
  · exact B563203
  · exact B563207
  · exact B563211
  · exact B563215
  · exact B563219
  · exact B563223
  · exact B563227
  · exact B563231
  · exact B563235
  · exact B563239
  · exact B563243
  · exact B563247
  · exact B563251
  · exact B563255
  · exact B563259
  · exact B563263
  · exact B563267
  · exact B563271
  · exact B563275
  · exact B563279
  · exact B563283
  · exact B563287
  · exact B563291
  · exact B563295
  · exact B563299
  · exact B563303
  · exact B563307
  · exact B563311
  · exact B563315
  · exact B563319
  · exact B563323
  · exact B563327
  · exact B563331
  · exact B563335
  · exact B563339
  · exact B563343
  · exact B563347
  · exact B563351
  · exact B563355
  · exact B563359
  · exact B563363
  · exact B563367
  · exact B563371
  · exact B563375
  · exact B563379
  · exact B563383
  · exact B563387
  · exact B563391
  · exact B563395
  · exact B563399
  · exact B563403
  · exact B563407
  · exact B563411
  · exact B563415
  · exact B563419
  · exact B563423
  · exact B563427
  · exact B563431
  · exact B563435
  · exact B563439
  · exact B563443
  · exact B563447
  · exact B563451
  · exact B563455
  · exact B563459
  · exact B563463
  · exact B563467
  · exact B563471
  · exact B563475
  · exact B563479
  · exact B563483
  · exact B563487
  · exact B563491
  · exact B563495
  · exact B563499
  · exact B563503
  · exact B563507
  · exact B563511
  · exact B563515
  · exact B563519
  · exact B563523
  · exact B563527
  · exact B563531
  · exact B563535
  · exact B563539
  · exact B563543
  · exact B563547
  · exact B563551
  · exact B563555
  · exact B563559
  · exact B563563
  · exact B563567
  · exact B563571
  · exact B563575
  · exact B563579
  · exact B563583
  · exact B563587
  · exact B563591
  · exact B563595
  · exact B563599
  · exact B563603
  · exact B563607
  · exact B563611
  · exact B563615
  · exact B563619
  · exact B563623
  · exact B563627
  · exact B563631
  · exact B563635
  · exact B563639
  · exact B563643
  · exact B563647
  · exact B563651
  · exact B563655
  · exact B563659
  · exact B563663
  · exact B563667
  · exact B563671
  · exact B563675
  · exact B563679
  · exact B563683
  · exact B563687
  · exact B563691
  · exact B563695
  · exact B563699
  · exact B563703
  · exact B563707
  · exact B563711
  · exact B563715
  · exact B563719
  · exact B563723
  · exact B563727
  · exact B563731
  · exact B563735
  · exact B563739
  · exact B563743
  · exact B563747
  · exact B563751
  · exact B563755
  · exact B563759
  · exact B563763
  · exact B563767
  · exact B563771
  · exact B563775
  · exact B563779
  · exact B563783
  · exact B563787
  · exact B563791
  · exact B563795
  · exact B563799
  · exact B563803
  · exact B563807
  · exact B563811
  · exact B563815
  · exact B563819
  · exact B563823
  · exact B563827
  · exact B563831
  · exact B563835
  · exact B563839
  · exact B563843
  · exact B563847
  · exact B563851
  · exact B563855
  · exact B563859
  · exact B563863
  · exact B563867
  · exact B563871
  · exact B563875
  · exact B563879
  · exact B563883
  · exact B563887
  · exact B563891
  · exact B563895
  · exact B563899
  · exact B563903
  · exact B563907
  · exact B563911
  · exact B563915
  · exact B563919
  · exact B563923
  · exact B563927
  · exact B563931
  · exact B563935
  · exact B563939
  · exact B563943
  · exact B563947
  · exact B563951
  · exact B563955
  · exact B563959
  · exact B563963
  · exact B563967
  · exact B563971
  · exact B563975
  · exact B563979
  · exact B563983
  · exact B563987
  · exact B563991
  · exact B563995
  · exact B563999
  · exact B564003
  · exact B564007
  · exact B564011
  · exact B564015
  · exact B564019
  · exact B564023
  · exact B564027
  · exact B564031
  · exact B564035
  · exact B564039
  · exact B564043
  · exact B564047
  · exact B564051
  · exact B564055
  · exact B564059
  · exact B564063
  · exact B564067
  · exact B564071
  · exact B564075
  · exact B564079
  · exact B564083
  · exact B564087
  · exact B564091
  · exact B564095
  · exact B564099
  · exact B564103
  · exact B564107
  · exact B564111
  · exact B564115
  · exact B564119
  · exact B564123
  · exact B564127
  · exact B564131
  · exact B564135
  · exact B564139
  · exact B564143
  · exact B564147
  · exact B564151
  · exact B564155
  · exact B564159
  · exact B564163
  · exact B564167
  · exact B564171
  · exact B564175
  · exact B564179
  · exact B564183
  · exact B564187
  · exact B564191
  · exact B564195
  · exact B564199
  · exact B564203
  · exact B564207
  · exact B564211
  · exact B564215
  · exact B564219
  · exact B564223
  · exact B564227
  · exact B564231
  · exact B564235
  · exact B564239
  · exact B564243
  · exact B564247
  · exact B564251
  · exact B564255
  · exact B564259
  · exact B564263
  · exact B564267
  · exact B564271
  · exact B564275
  · exact B564279
  · exact B564283
  · exact B564287
  · exact B564291
  · exact B564295
  · exact B564299
  · exact B564303
  · exact B564307
  · exact B564311
  · exact B564315
  · exact B564319
  · exact B564323
  · exact B564327
  · exact B564331
  · exact B564335
  · exact B564339
  · exact B564343
  · exact B564347
  · exact B564351
  · exact B564355
  · exact B564359
  · exact B564363
  · exact B564367
  · exact B564371
  · exact B564375
  · exact B564379
  · exact B564383
  · exact B564387
  · exact B564391
  · exact B564395
  · exact B564399
  · exact B564403
  · exact B564407
  · exact B564411
  · exact B564415
  · exact B564419
  · exact B564423
  · exact B564427
  · exact B564431
  · exact B564435
  · exact B564439
  · exact B564443
  · exact B564447
  · exact B564451
  · exact B564455
  · exact B564459
  · exact B564463
  · exact B564467
  · exact B564471
  · exact B564475
  · exact B564479
  · exact B564483
  · exact B564487
  · exact B564491
  · exact B564495
  · exact B564499
  · exact B564503
  · exact B564507
  · exact B564511
  · exact B564515
  · exact B564519
  · exact B564523
  · exact B564527
  · exact B564531
  · exact B564535
  · exact B564539
  · exact B564543
  · exact B564547
  · exact B564551
  · exact B564555
  · exact B564559
  · exact B564563
  · exact B564567
  · exact B564571
  · exact B564575
  · exact B564579
  · exact B564583
  · exact B564587
  · exact B564591
  · exact B564595
  · exact B564599
  · exact B564603
  · exact B564607
  · exact B564611
  · exact B564615
  · exact B564619
  · exact B564623
  · exact B564627
  · exact B564631
  · exact B564635
  · exact B564639
  · exact B564643
  · exact B564647
  · exact B564651
  · exact B564655
  · exact B564659
  · exact B564663
  · exact B564667
  · exact B564671
  · exact B564675
  · exact B564679
  · exact B564683
  · exact B564687
  · exact B564691
  · exact B564695
  · exact B564699
  · exact B564703
  · exact B564707
  · exact B564711
  · exact B564715
  · exact B564719
  · exact B564723
  · exact B564727
  · exact B564731
  · exact B564735
  · exact B564739
  · exact B564743
  · exact B564747
  · exact B564751
  · exact B564755
  · exact B564759
  · exact B564763
  · exact B564767
  · exact B564771
  · exact B564775
  · exact B564779
  · exact B564783
  · exact B564787
  · exact B564791
  · exact B564795
  · exact B564799
  · exact B564803
  · exact B564807
  · exact B564811
  · exact B564815
  · exact B564819
  · exact B564823
  · exact B564827
  · exact B564831
  · exact B564835
  · exact B564839
  · exact B564843
  · exact B564847
  · exact B564851
  · exact B564855
  · exact B564859
  · exact B564863
  · exact B564867
  · exact B564871
  · exact B564875
  · exact B564879
  · exact B564883
  · exact B564887
  · exact B564891
  · exact B564895
  · exact B564899
  · exact B564903
  · exact B564907
  · exact B564911
  · exact B564915
  · exact B564919
  · exact B564923
  · exact B564927
  · exact B564931
  · exact B564935
  · exact B564939
  · exact B564943
  · exact B564947
  · exact B564951
  · exact B564955
  · exact B564959
  · exact B564963
  · exact B564967
  · exact B564971
  · exact B564975
  · exact B564979
  · exact B564983
  · exact B564987
  · exact B564991
  · exact B564995
  · exact B564999
  · exact B565003
  · exact B565007
  · exact B565011
  · exact B565015
  · exact B565019
  · exact B565023
  · exact B565027
  · exact B565031
  · exact B565035
  · exact B565039
  · exact B565043
  · exact B565047
  · exact B565051
  · exact B565055
  · exact B565059
  · exact B565063
  · exact B565067
  · exact B565071
  · exact B565075
  · exact B565079
  · exact B565083
  · exact B565087
  · exact B565091
  · exact B565095
  · exact B565099
  · exact B565103
  · exact B565107
  · exact B565111
  · exact B565115
  · exact B565119
  · exact B565123
  · exact B565127
  · exact B565131
  · exact B565135
  · exact B565139
  · exact B565143
  · exact B565147
  · exact B565151
  · exact B565155
  · exact B565159
  · exact B565163
  · exact B565167
  · exact B565171
  · exact B565175
  · exact B565179
  · exact B565183
  · exact B565187
  · exact B565191
  · exact B565195
  · exact B565199
  · exact B565203
  · exact B565207
  · exact B565211
  · exact B565215
  · exact B565219
  · exact B565223
  · exact B565227
  · exact B565231
  · exact B565235
  · exact B565239
  · exact B565243
  · exact B565247
  · exact B565251
  · exact B565255
  · exact B565259
  · exact B565263
  · exact B565267
  · exact B565271
  · exact B565275
  · exact B565279
  · exact B565283
  · exact B565287
  · exact B565291
  · exact B565295
  · exact B565299
  · exact B565303
  · exact B565307
  · exact B565311
  · exact B565315
  · exact B565319
  · exact B565323
  · exact B565327
  · exact B565331
  · exact B565335
  · exact B565339
  · exact B565343
  · exact B565347
  · exact B565351
  · exact B565355
  · exact B565359
  · exact B565363
  · exact B565367
  · exact B565371
  · exact B565375
  · exact B565379
  · exact B565383
  · exact B565387
  · exact B565391
  · exact B565395
  · exact B565399
  · exact B565403
  · exact B565407
  · exact B565411
  · exact B565415
  · exact B565419
  · exact B565423
  · exact B565427
  · exact B565431
  · exact B565435
  · exact B565439
  · exact B565443
  · exact B565447
  · exact B565451
  · exact B565455
  · exact B565459
  · exact B565463
  · exact B565467
  · exact B565471
  · exact B565475
  · exact B565479
  · exact B565483
  · exact B565487
  · exact B565491
  · exact B565495
  · exact B565499
  · exact B565503
  · exact B565507
  · exact B565511
  · exact B565515
  · exact B565519
  · exact B565523
  · exact B565527
  · exact B565531
  · exact B565535
  · exact B565539
  · exact B565543
  · exact B565547
  · exact B565551
  · exact B565555
  · exact B565559
  · exact B565563
  · exact B565567
  · exact B565571
  · exact B565575
  · exact B565579
  · exact B565583
  · exact B565587
  · exact B565591
  · exact B565595
  · exact B565599
  · exact B565603
  · exact B565607

theorem C1 (j : ℕ) (h1 : 141402 ≤ j) (h2 : j ≤ 141701) : Blo 562809 (4 * j + 3) := by
  interval_cases j
  · exact B565611
  · exact B565615
  · exact B565619
  · exact B565623
  · exact B565627
  · exact B565631
  · exact B565635
  · exact B565639
  · exact B565643
  · exact B565647
  · exact B565651
  · exact B565655
  · exact B565659
  · exact B565663
  · exact B565667
  · exact B565671
  · exact B565675
  · exact B565679
  · exact B565683
  · exact B565687
  · exact B565691
  · exact B565695
  · exact B565699
  · exact B565703
  · exact B565707
  · exact B565711
  · exact B565715
  · exact B565719
  · exact B565723
  · exact B565727
  · exact B565731
  · exact B565735
  · exact B565739
  · exact B565743
  · exact B565747
  · exact B565751
  · exact B565755
  · exact B565759
  · exact B565763
  · exact B565767
  · exact B565771
  · exact B565775
  · exact B565779
  · exact B565783
  · exact B565787
  · exact B565791
  · exact B565795
  · exact B565799
  · exact B565803
  · exact B565807
  · exact B565811
  · exact B565815
  · exact B565819
  · exact B565823
  · exact B565827
  · exact B565831
  · exact B565835
  · exact B565839
  · exact B565843
  · exact B565847
  · exact B565851
  · exact B565855
  · exact B565859
  · exact B565863
  · exact B565867
  · exact B565871
  · exact B565875
  · exact B565879
  · exact B565883
  · exact B565887
  · exact B565891
  · exact B565895
  · exact B565899
  · exact B565903
  · exact B565907
  · exact B565911
  · exact B565915
  · exact B565919
  · exact B565923
  · exact B565927
  · exact B565931
  · exact B565935
  · exact B565939
  · exact B565943
  · exact B565947
  · exact B565951
  · exact B565955
  · exact B565959
  · exact B565963
  · exact B565967
  · exact B565971
  · exact B565975
  · exact B565979
  · exact B565983
  · exact B565987
  · exact B565991
  · exact B565995
  · exact B565999
  · exact B566003
  · exact B566007
  · exact B566011
  · exact B566015
  · exact B566019
  · exact B566023
  · exact B566027
  · exact B566031
  · exact B566035
  · exact B566039
  · exact B566043
  · exact B566047
  · exact B566051
  · exact B566055
  · exact B566059
  · exact B566063
  · exact B566067
  · exact B566071
  · exact B566075
  · exact B566079
  · exact B566083
  · exact B566087
  · exact B566091
  · exact B566095
  · exact B566099
  · exact B566103
  · exact B566107
  · exact B566111
  · exact B566115
  · exact B566119
  · exact B566123
  · exact B566127
  · exact B566131
  · exact B566135
  · exact B566139
  · exact B566143
  · exact B566147
  · exact B566151
  · exact B566155
  · exact B566159
  · exact B566163
  · exact B566167
  · exact B566171
  · exact B566175
  · exact B566179
  · exact B566183
  · exact B566187
  · exact B566191
  · exact B566195
  · exact B566199
  · exact B566203
  · exact B566207
  · exact B566211
  · exact B566215
  · exact B566219
  · exact B566223
  · exact B566227
  · exact B566231
  · exact B566235
  · exact B566239
  · exact B566243
  · exact B566247
  · exact B566251
  · exact B566255
  · exact B566259
  · exact B566263
  · exact B566267
  · exact B566271
  · exact B566275
  · exact B566279
  · exact B566283
  · exact B566287
  · exact B566291
  · exact B566295
  · exact B566299
  · exact B566303
  · exact B566307
  · exact B566311
  · exact B566315
  · exact B566319
  · exact B566323
  · exact B566327
  · exact B566331
  · exact B566335
  · exact B566339
  · exact B566343
  · exact B566347
  · exact B566351
  · exact B566355
  · exact B566359
  · exact B566363
  · exact B566367
  · exact B566371
  · exact B566375
  · exact B566379
  · exact B566383
  · exact B566387
  · exact B566391
  · exact B566395
  · exact B566399
  · exact B566403
  · exact B566407
  · exact B566411
  · exact B566415
  · exact B566419
  · exact B566423
  · exact B566427
  · exact B566431
  · exact B566435
  · exact B566439
  · exact B566443
  · exact B566447
  · exact B566451
  · exact B566455
  · exact B566459
  · exact B566463
  · exact B566467
  · exact B566471
  · exact B566475
  · exact B566479
  · exact B566483
  · exact B566487
  · exact B566491
  · exact B566495
  · exact B566499
  · exact B566503
  · exact B566507
  · exact B566511
  · exact B566515
  · exact B566519
  · exact B566523
  · exact B566527
  · exact B566531
  · exact B566535
  · exact B566539
  · exact B566543
  · exact B566547
  · exact B566551
  · exact B566555
  · exact B566559
  · exact B566563
  · exact B566567
  · exact B566571
  · exact B566575
  · exact B566579
  · exact B566583
  · exact B566587
  · exact B566591
  · exact B566595
  · exact B566599
  · exact B566603
  · exact B566607
  · exact B566611
  · exact B566615
  · exact B566619
  · exact B566623
  · exact B566627
  · exact B566631
  · exact B566635
  · exact B566639
  · exact B566643
  · exact B566647
  · exact B566651
  · exact B566655
  · exact B566659
  · exact B566663
  · exact B566667
  · exact B566671
  · exact B566675
  · exact B566679
  · exact B566683
  · exact B566687
  · exact B566691
  · exact B566695
  · exact B566699
  · exact B566703
  · exact B566707
  · exact B566711
  · exact B566715
  · exact B566719
  · exact B566723
  · exact B566727
  · exact B566731
  · exact B566735
  · exact B566739
  · exact B566743
  · exact B566747
  · exact B566751
  · exact B566755
  · exact B566759
  · exact B566763
  · exact B566767
  · exact B566771
  · exact B566775
  · exact B566779
  · exact B566783
  · exact B566787
  · exact B566791
  · exact B566795
  · exact B566799
  · exact B566803
  · exact B566807

theorem solution (m : ℕ) (hlo : 562809 ≤ m) (hhi : m ≤ 566809) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 140702 ≤ j := by omega
    have hj2 : j ≤ 141701 := by omega
    have hb : Blo 562809 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 141402 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
