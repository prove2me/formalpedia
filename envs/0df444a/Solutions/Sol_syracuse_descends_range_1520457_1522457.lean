-- Prove2me | solution 1 for syracuse_descends_range_1520457_1522457
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:04:26.444524+00:00
-- url     : https://prove2.me/submissions/ecb24bd8-2820-45a1-bf0f-79104a7ab373

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


theorem B1712137 : Blo 1520457 1712137 := bbase (se 2 (by rfl) ⟨642051, by rfl⟩ : syracuseStep 1712137 = 1284103) (by norm_num)
theorem B1925137 : Blo 1520457 1925137 := bbase (se 2 (by rfl) ⟨721926, by rfl⟩ : syracuseStep 1925137 = 1443853) (by norm_num)
theorem B11706389 : Blo 1520457 11706389 := bbase (se 6 (by rfl) ⟨274368, by rfl⟩ : syracuseStep 11706389 = 548737) (by norm_num)
theorem B3424301 : Blo 1520457 3424301 := bbase (se 3 (by rfl) ⟨642056, by rfl⟩ : syracuseStep 3424301 = 1284113) (by norm_num)
theorem B1712173 : Blo 1520457 1712173 := bbase (se 3 (by rfl) ⟨321032, by rfl⟩ : syracuseStep 1712173 = 642065) (by norm_num)
theorem B4333621 : Blo 1520457 4333621 := bbase (se 5 (by rfl) ⟨203138, by rfl⟩ : syracuseStep 4333621 = 406277) (by norm_num)
theorem B1712209 : Blo 1520457 1712209 := bbase (se 2 (by rfl) ⟨642078, by rfl⟩ : syracuseStep 1712209 = 1284157) (by norm_num)
theorem B3850325 : Blo 1520457 3850325 := bbase (se 8 (by rfl) ⟨22560, by rfl⟩ : syracuseStep 3850325 = 45121) (by norm_num)
theorem B3424373 : Blo 1520457 3424373 := bbase (se 5 (by rfl) ⟨160517, by rfl⟩ : syracuseStep 3424373 = 321035) (by norm_num)
theorem B1712245 : Blo 1520457 1712245 := bbase (se 5 (by rfl) ⟨80261, by rfl⟩ : syracuseStep 1712245 = 160523) (by norm_num)
theorem B21921941 : Blo 1520457 21921941 := bbase (se 6 (by rfl) ⟨513795, by rfl⟩ : syracuseStep 21921941 = 1027591) (by norm_num)
theorem B5136533 : Blo 1520457 5136533 := bbase (se 6 (by rfl) ⟨120387, by rfl⟩ : syracuseStep 5136533 = 240775) (by norm_num)
theorem B1712281 : Blo 1520457 1712281 := bbase (se 2 (by rfl) ⟨642105, by rfl⟩ : syracuseStep 1712281 = 1284211) (by norm_num)
theorem B1925309 : Blo 1520457 1925309 := bbase (se 3 (by rfl) ⟨360995, by rfl⟩ : syracuseStep 1925309 = 721991) (by norm_num)
theorem B3424445 : Blo 1520457 3424445 := bbase (se 3 (by rfl) ⟨642083, by rfl⟩ : syracuseStep 3424445 = 1284167) (by norm_num)
theorem B1712317 : Blo 1520457 1712317 := bbase (se 3 (by rfl) ⟨321059, by rfl⟩ : syracuseStep 1712317 = 642119) (by norm_num)
theorem B6496469 : Blo 1520457 6496469 := bbase (se 7 (by rfl) ⟨76130, by rfl⟩ : syracuseStep 6496469 = 152261) (by norm_num)
theorem B1712353 : Blo 1520457 1712353 := bbase (se 2 (by rfl) ⟨642132, by rfl⟩ : syracuseStep 1712353 = 1284265) (by norm_num)
theorem B1925365 : Blo 1520457 1925365 := bbase (se 5 (by rfl) ⟨90251, by rfl⟩ : syracuseStep 1925365 = 180503) (by norm_num)
theorem B3424517 : Blo 1520457 3424517 := bbase (se 4 (by rfl) ⟨321048, by rfl⟩ : syracuseStep 3424517 = 642097) (by norm_num)
theorem B1712389 : Blo 1520457 1712389 := bbase (se 4 (by rfl) ⟨160536, by rfl⟩ : syracuseStep 1712389 = 321073) (by norm_num)
theorem B3850517 : Blo 1520457 3850517 := bbase (se 6 (by rfl) ⟨90246, by rfl⟩ : syracuseStep 3850517 = 180493) (by norm_num)
theorem B1712425 : Blo 1520457 1712425 := bbase (se 2 (by rfl) ⟨642159, by rfl⟩ : syracuseStep 1712425 = 1284319) (by norm_num)
theorem B8667445 : Blo 1520457 8667445 := bbase (se 5 (by rfl) ⟨406286, by rfl⟩ : syracuseStep 8667445 = 812573) (by norm_num)
theorem B15835445 : Blo 1520457 15835445 := bbase (se 5 (by rfl) ⟨742286, by rfl⟩ : syracuseStep 15835445 = 1484573) (by norm_num)
theorem B3424589 : Blo 1520457 3424589 := bbase (se 3 (by rfl) ⟨642110, by rfl⟩ : syracuseStep 3424589 = 1284221) (by norm_num)
theorem B1712461 : Blo 1520457 1712461 := bbase (se 3 (by rfl) ⟨321086, by rfl⟩ : syracuseStep 1712461 = 642173) (by norm_num)
theorem B1925461 : Blo 1520457 1925461 := bbase (se 10 (by rfl) ⟨2820, by rfl⟩ : syracuseStep 1925461 = 5641) (by norm_num)
theorem B1712497 : Blo 1520457 1712497 := bbase (se 2 (by rfl) ⟨642186, by rfl⟩ : syracuseStep 1712497 = 1284373) (by norm_num)
theorem B14614901 : Blo 1520457 14614901 := bbase (se 5 (by rfl) ⟨685073, by rfl⟩ : syracuseStep 14614901 = 1370147) (by norm_num)
theorem B3424661 : Blo 1520457 3424661 := bbase (se 6 (by rfl) ⟨80265, by rfl⟩ : syracuseStep 3424661 = 160531) (by norm_num)
theorem B1712533 : Blo 1520457 1712533 := bbase (se 6 (by rfl) ⟨40137, by rfl⟩ : syracuseStep 1712533 = 80275) (by norm_num)
theorem B1712569 : Blo 1520457 1712569 := bbase (se 2 (by rfl) ⟨642213, by rfl⟩ : syracuseStep 1712569 = 1284427) (by norm_num)
theorem B7315925 : Blo 1520457 7315925 := bbase (se 7 (by rfl) ⟨85733, by rfl⟩ : syracuseStep 7315925 = 171467) (by norm_num)
theorem B3424733 : Blo 1520457 3424733 := bbase (se 3 (by rfl) ⟨642137, by rfl⟩ : syracuseStep 3424733 = 1284275) (by norm_num)
theorem B1712605 : Blo 1520457 1712605 := bbase (se 3 (by rfl) ⟨321113, by rfl⟩ : syracuseStep 1712605 = 642227) (by norm_num)
theorem B6496757 : Blo 1520457 6496757 := bbase (se 5 (by rfl) ⟨304535, by rfl⟩ : syracuseStep 6496757 = 609071) (by norm_num)
theorem B1925633 : Blo 1520457 1925633 := bbase (se 2 (by rfl) ⟨722112, by rfl⟩ : syracuseStep 1925633 = 1444225) (by norm_num)
theorem B1712641 : Blo 1520457 1712641 := bbase (se 2 (by rfl) ⟨642240, by rfl⟩ : syracuseStep 1712641 = 1284481) (by norm_num)
theorem B3424805 : Blo 1520457 3424805 := bbase (se 4 (by rfl) ⟨321075, by rfl⟩ : syracuseStep 3424805 = 642151) (by norm_num)
theorem B1712677 : Blo 1520457 1712677 := bbase (se 4 (by rfl) ⟨160563, by rfl⟩ : syracuseStep 1712677 = 321127) (by norm_num)
theorem B3654197 : Blo 1520457 3654197 := bbase (se 5 (by rfl) ⟨171290, by rfl⟩ : syracuseStep 3654197 = 342581) (by norm_num)
theorem B1925689 : Blo 1520457 1925689 := bbase (se 2 (by rfl) ⟨722133, by rfl⟩ : syracuseStep 1925689 = 1444267) (by norm_num)
theorem B5136965 : Blo 1520457 5136965 := bbase (se 4 (by rfl) ⟨481590, by rfl⟩ : syracuseStep 5136965 = 963181) (by norm_num)
theorem B1712713 : Blo 1520457 1712713 := bbase (se 2 (by rfl) ⟨642267, by rfl⟩ : syracuseStep 1712713 = 1284535) (by norm_num)
theorem B11559509 : Blo 1520457 11559509 := bbase (se 8 (by rfl) ⟨67731, by rfl⟩ : syracuseStep 11559509 = 135463) (by norm_num)
theorem B3850861 : Blo 1520457 3850861 := bbase (se 3 (by rfl) ⟨722036, by rfl⟩ : syracuseStep 3850861 = 1444073) (by norm_num)
theorem B3424877 : Blo 1520457 3424877 := bbase (se 3 (by rfl) ⟨642164, by rfl⟩ : syracuseStep 3424877 = 1284329) (by norm_num)
theorem B1712749 : Blo 1520457 1712749 := bbase (se 3 (by rfl) ⟨321140, by rfl⟩ : syracuseStep 1712749 = 642281) (by norm_num)
theorem B1852045 : Blo 1520457 1852045 := bbase (se 3 (by rfl) ⟨347258, by rfl⟩ : syracuseStep 1852045 = 694517) (by norm_num)
theorem B1925785 : Blo 1520457 1925785 := bbase (se 2 (by rfl) ⟨722169, by rfl⟩ : syracuseStep 1925785 = 1444339) (by norm_num)
theorem B3424949 : Blo 1520457 3424949 := bbase (se 5 (by rfl) ⟨160544, by rfl⟩ : syracuseStep 3424949 = 321089) (by norm_num)
theorem B52675285 : Blo 1520457 52675285 := bbase (se 7 (by rfl) ⟨617288, by rfl⟩ : syracuseStep 52675285 = 1234577) (by norm_num)
theorem B3850973 : Blo 1520457 3850973 := bbase (se 3 (by rfl) ⟨722057, by rfl⟩ : syracuseStep 3850973 = 1444115) (by norm_num)
theorem B4113125 : Blo 1520457 4113125 := bbase (se 4 (by rfl) ⟨385605, by rfl⟩ : syracuseStep 4113125 = 771211) (by norm_num)
theorem B4629221 : Blo 1520457 4629221 := bbase (se 4 (by rfl) ⟨433989, by rfl⟩ : syracuseStep 4629221 = 867979) (by norm_num)
theorem B1827569 : Blo 1520457 1827569 := bbase (se 2 (by rfl) ⟨685338, by rfl⟩ : syracuseStep 1827569 = 1370677) (by norm_num)
theorem B3654389 : Blo 1520457 3654389 := bbase (se 5 (by rfl) ⟨171299, by rfl⟩ : syracuseStep 3654389 = 342599) (by norm_num)
theorem B3425021 : Blo 1520457 3425021 := bbase (se 3 (by rfl) ⟨642191, by rfl⟩ : syracuseStep 3425021 = 1284383) (by norm_num)
theorem B4875029 : Blo 1520457 4875029 := bbase (se 6 (by rfl) ⟨114258, by rfl⟩ : syracuseStep 4875029 = 228517) (by norm_num)
theorem B7701317 : Blo 1520457 7701317 := bbase (se 4 (by rfl) ⟨721998, by rfl⟩ : syracuseStep 7701317 = 1443997) (by norm_num)
theorem B1925957 : Blo 1520457 1925957 := bbase (se 4 (by rfl) ⟨180558, by rfl⟩ : syracuseStep 1925957 = 361117) (by norm_num)
theorem B3425093 : Blo 1520457 3425093 := bbase (se 4 (by rfl) ⟨321102, by rfl⟩ : syracuseStep 3425093 = 642205) (by norm_num)
theorem B1926013 : Blo 1520457 1926013 := bbase (se 3 (by rfl) ⟨361127, by rfl⟩ : syracuseStep 1926013 = 722255) (by norm_num)
theorem B3425165 : Blo 1520457 3425165 := bbase (se 3 (by rfl) ⟨642218, by rfl⟩ : syracuseStep 3425165 = 1284437) (by norm_num)
theorem B4875157 : Blo 1520457 4875157 := bbase (se 6 (by rfl) ⟨114261, by rfl⟩ : syracuseStep 4875157 = 228523) (by norm_num)
theorem B3851165 : Blo 1520457 3851165 := bbase (se 3 (by rfl) ⟨722093, by rfl⟩ : syracuseStep 3851165 = 1444187) (by norm_num)
theorem B3425237 : Blo 1520457 3425237 := bbase (se 7 (by rfl) ⟨40139, by rfl⟩ : syracuseStep 3425237 = 80279) (by norm_num)
theorem B1926109 : Blo 1520457 1926109 := bbase (se 3 (by rfl) ⟨361145, by rfl⟩ : syracuseStep 1926109 = 722291) (by norm_num)
theorem B6251509 : Blo 1520457 6251509 := bbase (se 5 (by rfl) ⟨293039, by rfl⟩ : syracuseStep 6251509 = 586079) (by norm_num)
theorem B11551733 : Blo 1520457 11551733 := bbase (se 5 (by rfl) ⟨541487, by rfl⟩ : syracuseStep 11551733 = 1082975) (by norm_num)
theorem B5137397 : Blo 1520457 5137397 := bbase (se 5 (by rfl) ⟨240815, by rfl⟩ : syracuseStep 5137397 = 481631) (by norm_num)
theorem B3425309 : Blo 1520457 3425309 := bbase (se 3 (by rfl) ⟨642245, by rfl⟩ : syracuseStep 3425309 = 1284491) (by norm_num)
theorem B1827905 : Blo 1520457 1827905 := bbase (se 2 (by rfl) ⟨685464, by rfl⟩ : syracuseStep 1827905 = 1370929) (by norm_num)
theorem B3425381 : Blo 1520457 3425381 := bbase (se 4 (by rfl) ⟨321129, by rfl⟩ : syracuseStep 3425381 = 642259) (by norm_num)
theorem B1541233 : Blo 1520457 1541233 := bbase (se 2 (by rfl) ⟨577962, by rfl⟩ : syracuseStep 1541233 = 1155925) (by norm_num)
theorem B4334725 : Blo 1520457 4334725 := bbase (se 4 (by rfl) ⟨406380, by rfl⟩ : syracuseStep 4334725 = 812761) (by norm_num)
theorem B1541257 : Blo 1520457 1541257 := bbase (se 2 (by rfl) ⟨577971, by rfl⟩ : syracuseStep 1541257 = 1155943) (by norm_num)
theorem B1926281 : Blo 1520457 1926281 := bbase (se 2 (by rfl) ⟨722355, by rfl⟩ : syracuseStep 1926281 = 1444711) (by norm_num)
theorem B3425453 : Blo 1520457 3425453 := bbase (se 3 (by rfl) ⟨642272, by rfl⟩ : syracuseStep 3425453 = 1284545) (by norm_num)
theorem B1828021 : Blo 1520457 1828021 := bbase (se 5 (by rfl) ⟨85688, by rfl⟩ : syracuseStep 1828021 = 171377) (by norm_num)
theorem B1926337 : Blo 1520457 1926337 := bbase (se 2 (by rfl) ⟨722376, by rfl⟩ : syracuseStep 1926337 = 1444753) (by norm_num)
theorem B15623381 : Blo 1520457 15623381 := bbase (se 7 (by rfl) ⟨183086, by rfl⟩ : syracuseStep 15623381 = 366173) (by norm_num)
theorem B6497509 : Blo 1520457 6497509 := bbase (se 4 (by rfl) ⟨609141, by rfl⟩ : syracuseStep 6497509 = 1218283) (by norm_num)
theorem B3851509 : Blo 1520457 3851509 := bbase (se 5 (by rfl) ⟨180539, by rfl⟩ : syracuseStep 3851509 = 361079) (by norm_num)
theorem B3425525 : Blo 1520457 3425525 := bbase (se 5 (by rfl) ⟨160571, by rfl⟩ : syracuseStep 3425525 = 321143) (by norm_num)
theorem B1828093 : Blo 1520457 1828093 := bbase (se 3 (by rfl) ⟨342767, by rfl⟩ : syracuseStep 1828093 = 685535) (by norm_num)
theorem B1828117 : Blo 1520457 1828117 := bbase (se 6 (by rfl) ⟨42846, by rfl⟩ : syracuseStep 1828117 = 85693) (by norm_num)
theorem B1926433 : Blo 1520457 1926433 := bbase (se 2 (by rfl) ⟨722412, by rfl⟩ : syracuseStep 1926433 = 1444825) (by norm_num)
theorem B3654965 : Blo 1520457 3654965 := bbase (se 5 (by rfl) ⟨171326, by rfl⟩ : syracuseStep 3654965 = 342653) (by norm_num)
theorem B3851621 : Blo 1520457 3851621 := bbase (se 4 (by rfl) ⟨361089, by rfl⟩ : syracuseStep 3851621 = 722179) (by norm_num)
theorem B1828261 : Blo 1520457 1828261 := bbase (se 4 (by rfl) ⟨171399, by rfl⟩ : syracuseStep 1828261 = 342799) (by norm_num)
theorem B5137829 : Blo 1520457 5137829 := bbase (se 4 (by rfl) ⟨481671, by rfl⟩ : syracuseStep 5137829 = 963343) (by norm_num)
theorem B1541549 : Blo 1520457 1541549 := bbase (se 3 (by rfl) ⟨289040, by rfl⟩ : syracuseStep 1541549 = 578081) (by norm_num)
theorem B1926605 : Blo 1520457 1926605 := bbase (se 3 (by rfl) ⟨361238, by rfl⟩ : syracuseStep 1926605 = 722477) (by norm_num)
theorem B1926661 : Blo 1520457 1926661 := bbase (se 4 (by rfl) ⟨180624, by rfl⟩ : syracuseStep 1926661 = 361249) (by norm_num)
theorem B3851813 : Blo 1520457 3851813 := bbase (se 4 (by rfl) ⟨361107, by rfl⟩ : syracuseStep 3851813 = 722215) (by norm_num)
theorem B1926757 : Blo 1520457 1926757 := bbase (se 4 (by rfl) ⟨180633, by rfl⟩ : syracuseStep 1926757 = 361267) (by norm_num)
theorem B1623673 : Blo 1520457 1623673 := bbase (se 2 (by rfl) ⟨608877, by rfl⟩ : syracuseStep 1623673 = 1217755) (by norm_num)
theorem B27829909 : Blo 1520457 27829909 := bbase (se 6 (by rfl) ⟨652263, by rfl⟩ : syracuseStep 27829909 = 1304527) (by norm_num)
theorem B3655349 : Blo 1520457 3655349 := bbase (se 5 (by rfl) ⟨171344, by rfl⟩ : syracuseStep 3655349 = 342689) (by norm_num)
theorem B1623745 : Blo 1520457 1623745 := bbase (se 2 (by rfl) ⟨608904, by rfl⟩ : syracuseStep 1623745 = 1217809) (by norm_num)
theorem B2344661 : Blo 1520457 2344661 := bbase (se 7 (by rfl) ⟨27476, by rfl⟩ : syracuseStep 2344661 = 54953) (by norm_num)
theorem B2565877 : Blo 1520457 2565877 := bbase (se 5 (by rfl) ⟨120275, by rfl⟩ : syracuseStep 2565877 = 240551) (by norm_num)
theorem B7309045 : Blo 1520457 7309045 := bbase (se 5 (by rfl) ⟨342611, by rfl⟩ : syracuseStep 7309045 = 685223) (by norm_num)
theorem B5777189 : Blo 1520457 5777189 := bbase (se 4 (by rfl) ⟨541611, by rfl⟩ : syracuseStep 5777189 = 1083223) (by norm_num)
theorem B1951537 : Blo 1520457 1951537 := bbase (se 2 (by rfl) ⟨731826, by rfl⟩ : syracuseStep 1951537 = 1463653) (by norm_num)
theorem B2565965 : Blo 1520457 2565965 := bbase (se 3 (by rfl) ⟨481118, by rfl⟩ : syracuseStep 2565965 = 962237) (by norm_num)
theorem B5138261 : Blo 1520457 5138261 := bbase (se 9 (by rfl) ⟨15053, by rfl⟩ : syracuseStep 5138261 = 30107) (by norm_num)
theorem B1623925 : Blo 1520457 1623925 := bbase (se 5 (by rfl) ⟨76121, by rfl⟩ : syracuseStep 1623925 = 152243) (by norm_num)
theorem B3852157 : Blo 1520457 3852157 := bbase (se 3 (by rfl) ⟨722279, by rfl⟩ : syracuseStep 3852157 = 1444559) (by norm_num)
theorem B6498245 : Blo 1520457 6498245 := bbase (se 4 (by rfl) ⟨609210, by rfl⟩ : syracuseStep 6498245 = 1218421) (by norm_num)
theorem B2566093 : Blo 1520457 2566093 := bbase (se 3 (by rfl) ⟨481142, by rfl⟩ : syracuseStep 2566093 = 962285) (by norm_num)
theorem B2779085 : Blo 1520457 2779085 := bbase (se 3 (by rfl) ⟨521078, by rfl⟩ : syracuseStep 2779085 = 1042157) (by norm_num)
theorem B3852269 : Blo 1520457 3852269 := bbase (se 3 (by rfl) ⟨722300, by rfl⟩ : syracuseStep 3852269 = 1444601) (by norm_num)
theorem B2566181 : Blo 1520457 2566181 := bbase (se 4 (by rfl) ⟨240579, by rfl⟩ : syracuseStep 2566181 = 481159) (by norm_num)
theorem B5777477 : Blo 1520457 5777477 := bbase (se 4 (by rfl) ⟨541638, by rfl⟩ : syracuseStep 5777477 = 1083277) (by norm_num)
theorem B7702613 : Blo 1520457 7702613 := bbase (se 8 (by rfl) ⟨45132, by rfl⟩ : syracuseStep 7702613 = 90265) (by norm_num)
theorem B1853585 : Blo 1520457 1853585 := bbase (se 2 (by rfl) ⟨695094, by rfl⟩ : syracuseStep 1853585 = 1390189) (by norm_num)
theorem B2566309 : Blo 1520457 2566309 := bbase (se 4 (by rfl) ⟨240591, by rfl⟩ : syracuseStep 2566309 = 481183) (by norm_num)
theorem B3852461 : Blo 1520457 3852461 := bbase (se 3 (by rfl) ⟨722336, by rfl⟩ : syracuseStep 3852461 = 1444673) (by norm_num)
theorem B2164925 : Blo 1520457 2164925 := bbase (se 3 (by rfl) ⟨405923, by rfl⟩ : syracuseStep 2164925 = 811847) (by norm_num)
theorem B12503285 : Blo 1520457 12503285 := bbase (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) (by norm_num)
theorem B8669429 : Blo 1520457 8669429 := bbase (se 5 (by rfl) ⟨406379, by rfl⟩ : syracuseStep 8669429 = 812759) (by norm_num)
theorem B2566397 : Blo 1520457 2566397 := bbase (se 3 (by rfl) ⟨481199, by rfl⟩ : syracuseStep 2566397 = 962399) (by norm_num)
theorem B2165005 : Blo 1520457 2165005 := bbase (se 3 (by rfl) ⟨405938, by rfl⟩ : syracuseStep 2165005 = 811877) (by norm_num)
theorem B1624369 : Blo 1520457 1624369 := bbase (se 2 (by rfl) ⟨609138, by rfl⟩ : syracuseStep 1624369 = 1218277) (by norm_num)
theorem B13347125 : Blo 1520457 13347125 := bbase (se 5 (by rfl) ⟨625646, by rfl⟩ : syracuseStep 13347125 = 1251293) (by norm_num)
theorem B2566525 : Blo 1520457 2566525 := bbase (se 3 (by rfl) ⟨481223, by rfl⟩ : syracuseStep 2566525 = 962447) (by norm_num)
theorem B2165125 : Blo 1520457 2165125 := bbase (se 4 (by rfl) ⟨202980, by rfl⟩ : syracuseStep 2165125 = 405961) (by norm_num)
theorem B1624493 : Blo 1520457 1624493 := bbase (se 3 (by rfl) ⟨304592, by rfl⟩ : syracuseStep 1624493 = 609185) (by norm_num)
theorem B2927029 : Blo 1520457 2927029 := bbase (se 5 (by rfl) ⟨137204, by rfl⟩ : syracuseStep 2927029 = 274409) (by norm_num)
theorem B2566613 : Blo 1520457 2566613 := bbase (se 7 (by rfl) ⟨30077, by rfl⟩ : syracuseStep 2566613 = 60155) (by norm_num)
theorem B2165221 : Blo 1520457 2165221 := bbase (se 4 (by rfl) ⟨202989, by rfl⟩ : syracuseStep 2165221 = 405979) (by norm_num)
theorem B3901925 : Blo 1520457 3901925 := bbase (se 4 (by rfl) ⟨365805, by rfl⟩ : syracuseStep 3901925 = 731611) (by norm_num)
theorem B9882101 : Blo 1520457 9882101 := bbase (se 5 (by rfl) ⟨463223, by rfl⟩ : syracuseStep 9882101 = 926447) (by norm_num)
theorem B3852805 : Blo 1520457 3852805 := bbase (se 4 (by rfl) ⟨361200, by rfl⟩ : syracuseStep 3852805 = 722401) (by norm_num)
theorem B2566741 : Blo 1520457 2566741 := bbase (se 8 (by rfl) ⟨15039, by rfl⟩ : syracuseStep 2566741 = 30079) (by norm_num)
theorem B3852917 : Blo 1520457 3852917 := bbase (se 5 (by rfl) ⟨180605, by rfl⟩ : syracuseStep 3852917 = 361211) (by norm_num)
theorem B6941333 : Blo 1520457 6941333 := bbase (se 6 (by rfl) ⟨162687, by rfl⟩ : syracuseStep 6941333 = 325375) (by norm_num)
theorem B1624745 : Blo 1520457 1624745 := bbase (se 2 (by rfl) ⟨609279, by rfl⟩ : syracuseStep 1624745 = 1218559) (by norm_num)
theorem B2566829 : Blo 1520457 2566829 := bbase (se 3 (by rfl) ⟨481280, by rfl⟩ : syracuseStep 2566829 = 962561) (by norm_num)
theorem B2566957 : Blo 1520457 2566957 := bbase (se 3 (by rfl) ⟨481304, by rfl⟩ : syracuseStep 2566957 = 962609) (by norm_num)
theorem B3853109 : Blo 1520457 3853109 := bbase (se 5 (by rfl) ⟨180614, by rfl⟩ : syracuseStep 3853109 = 361229) (by norm_num)
theorem B2567045 : Blo 1520457 2567045 := bbase (se 4 (by rfl) ⟨240660, by rfl⟩ : syracuseStep 2567045 = 481321) (by norm_num)
theorem B2165717 : Blo 1520457 2165717 := bbase (se 7 (by rfl) ⟨25379, by rfl⟩ : syracuseStep 2165717 = 50759) (by norm_num)
theorem B21933013 : Blo 1520457 21933013 := bbase (se 7 (by rfl) ⟨257027, by rfl⟩ : syracuseStep 21933013 = 514055) (by norm_num)
theorem B2567173 : Blo 1520457 2567173 := bbase (se 4 (by rfl) ⟨240672, by rfl⟩ : syracuseStep 2567173 = 481345) (by norm_num)
theorem B2886749 : Blo 1520457 2886749 := bbase (se 3 (by rfl) ⟨541265, by rfl⟩ : syracuseStep 2886749 = 1082531) (by norm_num)
theorem B2567261 : Blo 1520457 2567261 := bbase (se 3 (by rfl) ⟨481361, by rfl⟩ : syracuseStep 2567261 = 962723) (by norm_num)
theorem B1625189 : Blo 1520457 1625189 := bbase (se 4 (by rfl) ⟨152361, by rfl⟩ : syracuseStep 1625189 = 304723) (by norm_num)
theorem B3468413 : Blo 1520457 3468413 := bbase (se 3 (by rfl) ⟨650327, by rfl⟩ : syracuseStep 3468413 = 1300655) (by norm_num)
theorem B3853453 : Blo 1520457 3853453 := bbase (se 3 (by rfl) ⟨722522, by rfl⟩ : syracuseStep 3853453 = 1445045) (by norm_num)
theorem B2567389 : Blo 1520457 2567389 := bbase (se 3 (by rfl) ⟨481385, by rfl⟩ : syracuseStep 2567389 = 962771) (by norm_num)
theorem B5778661 : Blo 1520457 5778661 := bbase (se 4 (by rfl) ⟨541749, by rfl⟩ : syracuseStep 5778661 = 1083499) (by norm_num)
theorem B2280701 : Blo 1520457 2280701 := bbase (se 3 (by rfl) ⟨427631, by rfl⟩ : syracuseStep 2280701 = 855263) (by norm_num)
theorem B3853565 : Blo 1520457 3853565 := bbase (se 3 (by rfl) ⟨722543, by rfl⟩ : syracuseStep 3853565 = 1445087) (by norm_num)
theorem B2280725 : Blo 1520457 2280725 := bbase (se 6 (by rfl) ⟨53454, by rfl⟩ : syracuseStep 2280725 = 106909) (by norm_num)
theorem B2280749 : Blo 1520457 2280749 := bbase (se 3 (by rfl) ⟨427640, by rfl⟩ : syracuseStep 2280749 = 855281) (by norm_num)
theorem B2567477 : Blo 1520457 2567477 := bbase (se 5 (by rfl) ⟨120350, by rfl⟩ : syracuseStep 2567477 = 240701) (by norm_num)
theorem B2280773 : Blo 1520457 2280773 := bbase (se 4 (by rfl) ⟨213822, by rfl⟩ : syracuseStep 2280773 = 427645) (by norm_num)
theorem B2280797 : Blo 1520457 2280797 := bbase (se 3 (by rfl) ⟨427649, by rfl⟩ : syracuseStep 2280797 = 855299) (by norm_num)
theorem B1625437 : Blo 1520457 1625437 := bbase (se 3 (by rfl) ⟨304769, by rfl⟩ : syracuseStep 1625437 = 609539) (by norm_num)
theorem B7703909 : Blo 1520457 7703909 := bbase (se 4 (by rfl) ⟨722241, by rfl⟩ : syracuseStep 7703909 = 1444483) (by norm_num)
theorem B2280821 : Blo 1520457 2280821 := bbase (se 5 (by rfl) ⟨106913, by rfl⟩ : syracuseStep 2280821 = 213827) (by norm_num)
theorem B8228213 : Blo 1520457 8228213 := bbase (se 5 (by rfl) ⟨385697, by rfl⟩ : syracuseStep 8228213 = 771395) (by norm_num)
theorem B2280845 : Blo 1520457 2280845 := bbase (se 3 (by rfl) ⟨427658, by rfl⟩ : syracuseStep 2280845 = 855317) (by norm_num)
theorem B3657109 : Blo 1520457 3657109 := bbase (se 6 (by rfl) ⟨85713, by rfl⟩ : syracuseStep 3657109 = 171427) (by norm_num)
theorem B2280869 : Blo 1520457 2280869 := bbase (se 4 (by rfl) ⟨213831, by rfl⟩ : syracuseStep 2280869 = 427663) (by norm_num)
theorem B2567605 : Blo 1520457 2567605 := bbase (se 5 (by rfl) ⟨120356, by rfl⟩ : syracuseStep 2567605 = 240713) (by norm_num)
theorem B2280893 : Blo 1520457 2280893 := bbase (se 3 (by rfl) ⟨427667, by rfl⟩ : syracuseStep 2280893 = 855335) (by norm_num)
theorem B2280917 : Blo 1520457 2280917 := bbase (se 7 (by rfl) ⟨26729, by rfl⟩ : syracuseStep 2280917 = 53459) (by norm_num)
theorem B5852645 : Blo 1520457 5852645 := bbase (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) (by norm_num)
theorem B2280941 : Blo 1520457 2280941 := bbase (se 3 (by rfl) ⟨427676, by rfl⟩ : syracuseStep 2280941 = 855353) (by norm_num)
theorem B2166269 : Blo 1520457 2166269 := bbase (se 3 (by rfl) ⟨406175, by rfl⟩ : syracuseStep 2166269 = 812351) (by norm_num)
theorem B5131781 : Blo 1520457 5131781 := bbase (se 4 (by rfl) ⟨481104, by rfl⟩ : syracuseStep 5131781 = 962209) (by norm_num)
theorem B2280965 : Blo 1520457 2280965 := bbase (se 4 (by rfl) ⟨213840, by rfl⟩ : syracuseStep 2280965 = 427681) (by norm_num)
theorem B2567693 : Blo 1520457 2567693 := bbase (se 3 (by rfl) ⟨481442, by rfl⟩ : syracuseStep 2567693 = 962885) (by norm_num)
theorem B5778965 : Blo 1520457 5778965 := bbase (se 6 (by rfl) ⟨135444, by rfl⟩ : syracuseStep 5778965 = 270889) (by norm_num)
theorem B2280989 : Blo 1520457 2280989 := bbase (se 3 (by rfl) ⟨427685, by rfl⟩ : syracuseStep 2280989 = 855371) (by norm_num)
theorem B2436637 : Blo 1520457 2436637 := bbase (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) (by norm_num)
theorem B3247661 : Blo 1520457 3247661 := bbase (se 3 (by rfl) ⟨608936, by rfl⟩ : syracuseStep 3247661 = 1217873) (by norm_num)
theorem B2281013 : Blo 1520457 2281013 := bbase (se 5 (by rfl) ⟨106922, by rfl⟩ : syracuseStep 2281013 = 213845) (by norm_num)
theorem B2928197 : Blo 1520457 2928197 := bbase (se 4 (by rfl) ⟨274518, by rfl⟩ : syracuseStep 2928197 = 549037) (by norm_num)
theorem B2281037 : Blo 1520457 2281037 := bbase (se 3 (by rfl) ⟨427694, by rfl⟩ : syracuseStep 2281037 = 855389) (by norm_num)
theorem B2281061 : Blo 1520457 2281061 := bbase (se 4 (by rfl) ⟨213849, by rfl⟩ : syracuseStep 2281061 = 427699) (by norm_num)
theorem B10407541 : Blo 1520457 10407541 := bbase (se 5 (by rfl) ⟨487853, by rfl⟩ : syracuseStep 10407541 = 975707) (by norm_num)
theorem B2281085 : Blo 1520457 2281085 := bbase (se 3 (by rfl) ⟨427703, by rfl⟩ : syracuseStep 2281085 = 855407) (by norm_num)
theorem B2567821 : Blo 1520457 2567821 := bbase (se 3 (by rfl) ⟨481466, by rfl⟩ : syracuseStep 2567821 = 962933) (by norm_num)
theorem B2281109 : Blo 1520457 2281109 := bbase (se 6 (by rfl) ⟨53463, by rfl⟩ : syracuseStep 2281109 = 106927) (by norm_num)
theorem B2281133 : Blo 1520457 2281133 := bbase (se 3 (by rfl) ⟨427712, by rfl⟩ : syracuseStep 2281133 = 855425) (by norm_num)
theorem B10972853 : Blo 1520457 10972853 := bbase (se 5 (by rfl) ⟨514352, by rfl⟩ : syracuseStep 10972853 = 1028705) (by norm_num)
theorem B2281157 : Blo 1520457 2281157 := bbase (se 4 (by rfl) ⟨213858, by rfl⟩ : syracuseStep 2281157 = 427717) (by norm_num)
theorem B2281181 : Blo 1520457 2281181 := bbase (se 3 (by rfl) ⟨427721, by rfl⟩ : syracuseStep 2281181 = 855443) (by norm_num)
theorem B2567909 : Blo 1520457 2567909 := bbase (se 4 (by rfl) ⟨240741, by rfl⟩ : syracuseStep 2567909 = 481483) (by norm_num)
theorem B2281205 : Blo 1520457 2281205 := bbase (se 5 (by rfl) ⟨106931, by rfl⟩ : syracuseStep 2281205 = 213863) (by norm_num)
theorem B5484293 : Blo 1520457 5484293 := bbase (se 4 (by rfl) ⟨514152, by rfl⟩ : syracuseStep 5484293 = 1028305) (by norm_num)
theorem B2281229 : Blo 1520457 2281229 := bbase (se 3 (by rfl) ⟨427730, by rfl⟩ : syracuseStep 2281229 = 855461) (by norm_num)
theorem B2281253 : Blo 1520457 2281253 := bbase (se 4 (by rfl) ⟨213867, by rfl⟩ : syracuseStep 2281253 = 427735) (by norm_num)
theorem B2281277 : Blo 1520457 2281277 := bbase (se 3 (by rfl) ⟨427739, by rfl⟩ : syracuseStep 2281277 = 855479) (by norm_num)
theorem B6254405 : Blo 1520457 6254405 := bbase (se 4 (by rfl) ⟨586350, by rfl⟩ : syracuseStep 6254405 = 1172701) (by norm_num)
theorem B2887501 : Blo 1520457 2887501 := bbase (se 3 (by rfl) ⟨541406, by rfl⟩ : syracuseStep 2887501 = 1082813) (by norm_num)
theorem B2281301 : Blo 1520457 2281301 := bbase (se 9 (by rfl) ⟨6683, by rfl⟩ : syracuseStep 2281301 = 13367) (by norm_num)
theorem B2568037 : Blo 1520457 2568037 := bbase (se 4 (by rfl) ⟨240753, by rfl⟩ : syracuseStep 2568037 = 481507) (by norm_num)
theorem B2281325 : Blo 1520457 2281325 := bbase (se 3 (by rfl) ⟨427748, by rfl⟩ : syracuseStep 2281325 = 855497) (by norm_num)
theorem B2281349 : Blo 1520457 2281349 := bbase (se 4 (by rfl) ⟨213876, by rfl⟩ : syracuseStep 2281349 = 427753) (by norm_num)
theorem B3248029 : Blo 1520457 3248029 := bbase (se 3 (by rfl) ⟨609005, by rfl⟩ : syracuseStep 3248029 = 1218011) (by norm_num)
theorem B2281373 : Blo 1520457 2281373 := bbase (se 3 (by rfl) ⟨427757, by rfl⟩ : syracuseStep 2281373 = 855515) (by norm_num)
theorem B5132213 : Blo 1520457 5132213 := bbase (se 5 (by rfl) ⟨240572, by rfl⟩ : syracuseStep 5132213 = 481145) (by norm_num)
theorem B2281397 : Blo 1520457 2281397 := bbase (se 5 (by rfl) ⟨106940, by rfl⟩ : syracuseStep 2281397 = 213881) (by norm_num)
theorem B2568125 : Blo 1520457 2568125 := bbase (se 3 (by rfl) ⟨481523, by rfl⟩ : syracuseStep 2568125 = 963047) (by norm_num)
theorem B2281421 : Blo 1520457 2281421 := bbase (se 3 (by rfl) ⟨427766, by rfl⟩ : syracuseStep 2281421 = 855533) (by norm_num)
theorem B2887645 : Blo 1520457 2887645 := bbase (se 3 (by rfl) ⟨541433, by rfl⟩ : syracuseStep 2887645 = 1082867) (by norm_num)
theorem B2281445 : Blo 1520457 2281445 := bbase (se 4 (by rfl) ⟨213885, by rfl⟩ : syracuseStep 2281445 = 427771) (by norm_num)
theorem B2281469 : Blo 1520457 2281469 := bbase (se 3 (by rfl) ⟨427775, by rfl⟩ : syracuseStep 2281469 = 855551) (by norm_num)
theorem B2281493 : Blo 1520457 2281493 := bbase (se 6 (by rfl) ⟨53472, by rfl⟩ : syracuseStep 2281493 = 106945) (by norm_num)
theorem B5484581 : Blo 1520457 5484581 := bbase (se 4 (by rfl) ⟨514179, by rfl⟩ : syracuseStep 5484581 = 1028359) (by norm_num)
theorem B2281517 : Blo 1520457 2281517 := bbase (se 3 (by rfl) ⟨427784, by rfl⟩ : syracuseStep 2281517 = 855569) (by norm_num)
theorem B2568253 : Blo 1520457 2568253 := bbase (se 3 (by rfl) ⟨481547, by rfl⟩ : syracuseStep 2568253 = 963095) (by norm_num)
theorem B2281541 : Blo 1520457 2281541 := bbase (se 4 (by rfl) ⟨213894, by rfl⟩ : syracuseStep 2281541 = 427789) (by norm_num)
theorem B3518549 : Blo 1520457 3518549 := bbase (se 8 (by rfl) ⟨20616, by rfl⟩ : syracuseStep 3518549 = 41233) (by norm_num)
theorem B2281565 : Blo 1520457 2281565 := bbase (se 3 (by rfl) ⟨427793, by rfl⟩ : syracuseStep 2281565 = 855587) (by norm_num)
theorem B2281589 : Blo 1520457 2281589 := bbase (se 5 (by rfl) ⟨106949, by rfl⟩ : syracuseStep 2281589 = 213899) (by norm_num)
theorem B2887805 : Blo 1520457 2887805 := bbase (se 3 (by rfl) ⟨541463, by rfl⟩ : syracuseStep 2887805 = 1082927) (by norm_num)
theorem B2281613 : Blo 1520457 2281613 := bbase (se 3 (by rfl) ⟨427802, by rfl⟩ : syracuseStep 2281613 = 855605) (by norm_num)
theorem B2568341 : Blo 1520457 2568341 := bbase (se 6 (by rfl) ⟨60195, by rfl⟩ : syracuseStep 2568341 = 120391) (by norm_num)
theorem B2281637 : Blo 1520457 2281637 := bbase (se 4 (by rfl) ⟨213903, by rfl⟩ : syracuseStep 2281637 = 427807) (by norm_num)
theorem B2281661 : Blo 1520457 2281661 := bbase (se 3 (by rfl) ⟨427811, by rfl⟩ : syracuseStep 2281661 = 855623) (by norm_num)
theorem B2437309 : Blo 1520457 2437309 := bbase (se 3 (by rfl) ⟨456995, by rfl⟩ : syracuseStep 2437309 = 913991) (by norm_num)
theorem B2281685 : Blo 1520457 2281685 := bbase (se 7 (by rfl) ⟨26738, by rfl⟩ : syracuseStep 2281685 = 53477) (by norm_num)
theorem B29241557 : Blo 1520457 29241557 := bbase (se 7 (by rfl) ⟨342674, by rfl⟩ : syracuseStep 29241557 = 685349) (by norm_num)
theorem B2438309 : Blo 1520457 2438309 := bbase (se 4 (by rfl) ⟨228591, by rfl⟩ : syracuseStep 2438309 = 457183) (by norm_num)
theorem B2281709 : Blo 1520457 2281709 := bbase (se 3 (by rfl) ⟨427820, by rfl⟩ : syracuseStep 2281709 = 855641) (by norm_num)
theorem B2167021 : Blo 1520457 2167021 := bbase (se 3 (by rfl) ⟨406316, by rfl⟩ : syracuseStep 2167021 = 812633) (by norm_num)
theorem B2281733 : Blo 1520457 2281733 := bbase (se 4 (by rfl) ⟨213912, by rfl⟩ : syracuseStep 2281733 = 427825) (by norm_num)
theorem B2887949 : Blo 1520457 2887949 := bbase (se 3 (by rfl) ⟨541490, by rfl⟩ : syracuseStep 2887949 = 1082981) (by norm_num)
theorem B2568469 : Blo 1520457 2568469 := bbase (se 6 (by rfl) ⟨60198, by rfl⟩ : syracuseStep 2568469 = 120397) (by norm_num)
theorem B2281757 : Blo 1520457 2281757 := bbase (se 3 (by rfl) ⟨427829, by rfl⟩ : syracuseStep 2281757 = 855659) (by norm_num)
theorem B2601269 : Blo 1520457 2601269 := bbase (se 5 (by rfl) ⟨121934, by rfl⟩ : syracuseStep 2601269 = 243869) (by norm_num)
theorem B2281781 : Blo 1520457 2281781 := bbase (se 5 (by rfl) ⟨106958, by rfl⟩ : syracuseStep 2281781 = 213917) (by norm_num)
theorem B2281805 : Blo 1520457 2281805 := bbase (se 3 (by rfl) ⟨427838, by rfl⟩ : syracuseStep 2281805 = 855677) (by norm_num)
theorem B9744725 : Blo 1520457 9744725 := bbase (se 10 (by rfl) ⟨14274, by rfl⟩ : syracuseStep 9744725 = 28549) (by norm_num)
theorem B5132645 : Blo 1520457 5132645 := bbase (se 4 (by rfl) ⟨481185, by rfl⟩ : syracuseStep 5132645 = 962371) (by norm_num)
theorem B2281829 : Blo 1520457 2281829 := bbase (se 4 (by rfl) ⟨213921, by rfl⟩ : syracuseStep 2281829 = 427843) (by norm_num)
theorem B2568557 : Blo 1520457 2568557 := bbase (se 3 (by rfl) ⟨481604, by rfl⟩ : syracuseStep 2568557 = 963209) (by norm_num)
theorem B2281853 : Blo 1520457 2281853 := bbase (se 3 (by rfl) ⟨427847, by rfl⟩ : syracuseStep 2281853 = 855695) (by norm_num)
theorem B2281877 : Blo 1520457 2281877 := bbase (se 6 (by rfl) ⟨53481, by rfl⟩ : syracuseStep 2281877 = 106963) (by norm_num)
theorem B2281901 : Blo 1520457 2281901 := bbase (se 3 (by rfl) ⟨427856, by rfl⟩ : syracuseStep 2281901 = 855713) (by norm_num)
theorem B2281925 : Blo 1520457 2281925 := bbase (se 4 (by rfl) ⟨213930, by rfl⟩ : syracuseStep 2281925 = 427861) (by norm_num)
theorem B13005269 : Blo 1520457 13005269 := bbase (se 7 (by rfl) ⟨152405, by rfl⟩ : syracuseStep 13005269 = 304811) (by norm_num)
theorem B2281949 : Blo 1520457 2281949 := bbase (se 3 (by rfl) ⟨427865, by rfl⟩ : syracuseStep 2281949 = 855731) (by norm_num)
theorem B2568685 : Blo 1520457 2568685 := bbase (se 3 (by rfl) ⟨481628, by rfl⟩ : syracuseStep 2568685 = 963257) (by norm_num)
theorem B2281973 : Blo 1520457 2281973 := bbase (se 5 (by rfl) ⟨106967, by rfl⟩ : syracuseStep 2281973 = 213935) (by norm_num)
theorem B2281997 : Blo 1520457 2281997 := bbase (se 3 (by rfl) ⟨427874, by rfl⟩ : syracuseStep 2281997 = 855749) (by norm_num)
theorem B2282021 : Blo 1520457 2282021 := bbase (se 4 (by rfl) ⟨213939, by rfl⟩ : syracuseStep 2282021 = 427879) (by norm_num)
theorem B2888237 : Blo 1520457 2888237 := bbase (se 3 (by rfl) ⟨541544, by rfl⟩ : syracuseStep 2888237 = 1083089) (by norm_num)
theorem B2282045 : Blo 1520457 2282045 := bbase (se 3 (by rfl) ⟨427883, by rfl⟩ : syracuseStep 2282045 = 855767) (by norm_num)
theorem B2568773 : Blo 1520457 2568773 := bbase (se 4 (by rfl) ⟨240822, by rfl⟩ : syracuseStep 2568773 = 481645) (by norm_num)
theorem B2282069 : Blo 1520457 2282069 := bbase (se 8 (by rfl) ⟨13371, by rfl⟩ : syracuseStep 2282069 = 26743) (by norm_num)
theorem B12997205 : Blo 1520457 12997205 := bbase (se 8 (by rfl) ⟨76155, by rfl⟩ : syracuseStep 12997205 = 152311) (by norm_num)
theorem B2282093 : Blo 1520457 2282093 := bbase (se 3 (by rfl) ⟨427892, by rfl⟩ : syracuseStep 2282093 = 855785) (by norm_num)
theorem B7705205 : Blo 1520457 7705205 := bbase (se 5 (by rfl) ⟨361181, by rfl⟩ : syracuseStep 7705205 = 722363) (by norm_num)
theorem B2282117 : Blo 1520457 2282117 := bbase (se 4 (by rfl) ⟨213948, by rfl⟩ : syracuseStep 2282117 = 427897) (by norm_num)
theorem B2282141 : Blo 1520457 2282141 := bbase (se 3 (by rfl) ⟨427901, by rfl⟩ : syracuseStep 2282141 = 855803) (by norm_num)
theorem B2282165 : Blo 1520457 2282165 := bbase (se 5 (by rfl) ⟨106976, by rfl⟩ : syracuseStep 2282165 = 213953) (by norm_num)
theorem B2888389 : Blo 1520457 2888389 := bbase (se 4 (by rfl) ⟨270786, by rfl⟩ : syracuseStep 2888389 = 541573) (by norm_num)
theorem B2568901 : Blo 1520457 2568901 := bbase (se 4 (by rfl) ⟨240834, by rfl⟩ : syracuseStep 2568901 = 481669) (by norm_num)
theorem B2282189 : Blo 1520457 2282189 := bbase (se 3 (by rfl) ⟨427910, by rfl⟩ : syracuseStep 2282189 = 855821) (by norm_num)
theorem B2282213 : Blo 1520457 2282213 := bbase (se 4 (by rfl) ⟨213957, by rfl⟩ : syracuseStep 2282213 = 427915) (by norm_num)
theorem B2282237 : Blo 1520457 2282237 := bbase (se 3 (by rfl) ⟨427919, by rfl⟩ : syracuseStep 2282237 = 855839) (by norm_num)
theorem B5133077 : Blo 1520457 5133077 := bbase (se 6 (by rfl) ⟨120306, by rfl⟩ : syracuseStep 5133077 = 240613) (by norm_num)
theorem B2282261 : Blo 1520457 2282261 := bbase (se 6 (by rfl) ⟨53490, by rfl⟩ : syracuseStep 2282261 = 106981) (by norm_num)
theorem B2568989 : Blo 1520457 2568989 := bbase (se 3 (by rfl) ⟨481685, by rfl⟩ : syracuseStep 2568989 = 963371) (by norm_num)
theorem B2282285 : Blo 1520457 2282285 := bbase (se 3 (by rfl) ⟨427928, by rfl⟩ : syracuseStep 2282285 = 855857) (by norm_num)
theorem B2282309 : Blo 1520457 2282309 := bbase (se 4 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 2282309 = 427933) (by norm_num)
theorem B2282333 : Blo 1520457 2282333 := bbase (se 3 (by rfl) ⟨427937, by rfl⟩ : syracuseStep 2282333 = 855875) (by norm_num)
theorem B2282357 : Blo 1520457 2282357 := bbase (se 5 (by rfl) ⟨106985, by rfl⟩ : syracuseStep 2282357 = 213971) (by norm_num)
theorem B7811957 : Blo 1520457 7811957 := bbase (se 5 (by rfl) ⟨366185, by rfl⟩ : syracuseStep 7811957 = 732371) (by norm_num)
theorem B3421061 : Blo 1520457 3421061 := bbase (se 4 (by rfl) ⟨320724, by rfl⟩ : syracuseStep 3421061 = 641449) (by norm_num)
theorem B2282381 : Blo 1520457 2282381 := bbase (se 3 (by rfl) ⟨427946, by rfl⟩ : syracuseStep 2282381 = 855893) (by norm_num)
theorem B2569117 : Blo 1520457 2569117 := bbase (se 3 (by rfl) ⟨481709, by rfl⟩ : syracuseStep 2569117 = 963419) (by norm_num)
theorem B2282405 : Blo 1520457 2282405 := bbase (se 4 (by rfl) ⟨213975, by rfl⟩ : syracuseStep 2282405 = 427951) (by norm_num)
theorem B2282429 : Blo 1520457 2282429 := bbase (se 3 (by rfl) ⟨427955, by rfl⟩ : syracuseStep 2282429 = 855911) (by norm_num)
theorem B3421133 : Blo 1520457 3421133 := bbase (se 3 (by rfl) ⟨641462, by rfl⟩ : syracuseStep 3421133 = 1282925) (by norm_num)
theorem B2282453 : Blo 1520457 2282453 := bbase (se 7 (by rfl) ⟨26747, by rfl⟩ : syracuseStep 2282453 = 53495) (by norm_num)
theorem B2282477 : Blo 1520457 2282477 := bbase (se 3 (by rfl) ⟨427964, by rfl⟩ : syracuseStep 2282477 = 855929) (by norm_num)
theorem B2888693 : Blo 1520457 2888693 := bbase (se 5 (by rfl) ⟨135407, by rfl⟩ : syracuseStep 2888693 = 270815) (by norm_num)
theorem B2929645 : Blo 1520457 2929645 := bbase (se 3 (by rfl) ⟨549308, by rfl⟩ : syracuseStep 2929645 = 1098617) (by norm_num)
theorem B2282501 : Blo 1520457 2282501 := bbase (se 4 (by rfl) ⟨213984, by rfl⟩ : syracuseStep 2282501 = 427969) (by norm_num)
theorem B7697429 : Blo 1520457 7697429 := bbase (se 6 (by rfl) ⟨180408, by rfl⟩ : syracuseStep 7697429 = 360817) (by norm_num)
theorem B3421205 : Blo 1520457 3421205 := bbase (se 6 (by rfl) ⟨80184, by rfl⟩ : syracuseStep 3421205 = 160369) (by norm_num)
theorem B2282525 : Blo 1520457 2282525 := bbase (se 3 (by rfl) ⟨427973, by rfl⟩ : syracuseStep 2282525 = 855947) (by norm_num)
theorem B2282549 : Blo 1520457 2282549 := bbase (se 5 (by rfl) ⟨106994, by rfl⟩ : syracuseStep 2282549 = 213989) (by norm_num)
theorem B2282573 : Blo 1520457 2282573 := bbase (se 3 (by rfl) ⟨427982, by rfl⟩ : syracuseStep 2282573 = 855965) (by norm_num)
theorem B3421277 : Blo 1520457 3421277 := bbase (se 3 (by rfl) ⟨641489, by rfl⟩ : syracuseStep 3421277 = 1282979) (by norm_num)
theorem B2282597 : Blo 1520457 2282597 := bbase (se 4 (by rfl) ⟨213993, by rfl⟩ : syracuseStep 2282597 = 427987) (by norm_num)
theorem B2282621 : Blo 1520457 2282621 := bbase (se 3 (by rfl) ⟨427991, by rfl⟩ : syracuseStep 2282621 = 855983) (by norm_num)
theorem B2282645 : Blo 1520457 2282645 := bbase (se 6 (by rfl) ⟨53499, by rfl⟩ : syracuseStep 2282645 = 106999) (by norm_num)
theorem B3421349 : Blo 1520457 3421349 := bbase (se 4 (by rfl) ⟨320751, by rfl⟩ : syracuseStep 3421349 = 641503) (by norm_num)
theorem B2471077 : Blo 1520457 2471077 := bbase (se 4 (by rfl) ⟨231663, by rfl⟩ : syracuseStep 2471077 = 463327) (by norm_num)
theorem B6501541 : Blo 1520457 6501541 := bbase (se 4 (by rfl) ⟨609519, by rfl⟩ : syracuseStep 6501541 = 1219039) (by norm_num)
theorem B2282669 : Blo 1520457 2282669 := bbase (se 3 (by rfl) ⟨428000, by rfl⟩ : syracuseStep 2282669 = 856001) (by norm_num)
theorem B5133509 : Blo 1520457 5133509 := bbase (se 4 (by rfl) ⟨481266, by rfl⟩ : syracuseStep 5133509 = 962533) (by norm_num)
theorem B2282693 : Blo 1520457 2282693 := bbase (se 4 (by rfl) ⟨214002, by rfl⟩ : syracuseStep 2282693 = 428005) (by norm_num)
theorem B2282717 : Blo 1520457 2282717 := bbase (se 3 (by rfl) ⟨428009, by rfl⟩ : syracuseStep 2282717 = 856019) (by norm_num)
theorem B3421421 : Blo 1520457 3421421 := bbase (se 3 (by rfl) ⟨641516, by rfl⟩ : syracuseStep 3421421 = 1283033) (by norm_num)
theorem B2282741 : Blo 1520457 2282741 := bbase (se 5 (by rfl) ⟨107003, by rfl⟩ : syracuseStep 2282741 = 214007) (by norm_num)
theorem B2282765 : Blo 1520457 2282765 := bbase (se 3 (by rfl) ⟨428018, by rfl⟩ : syracuseStep 2282765 = 856037) (by norm_num)
theorem B2282789 : Blo 1520457 2282789 := bbase (se 4 (by rfl) ⟨214011, by rfl⟩ : syracuseStep 2282789 = 428023) (by norm_num)
theorem B3421493 : Blo 1520457 3421493 := bbase (se 5 (by rfl) ⟨160382, by rfl⟩ : syracuseStep 3421493 = 320765) (by norm_num)
theorem B2282813 : Blo 1520457 2282813 := bbase (se 3 (by rfl) ⟨428027, by rfl⟩ : syracuseStep 2282813 = 856055) (by norm_num)
theorem B2282837 : Blo 1520457 2282837 := bbase (se 15 (by rfl) ⟨104, by rfl⟩ : syracuseStep 2282837 = 209) (by norm_num)
theorem B4330853 : Blo 1520457 4330853 := bbase (se 4 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 4330853 = 812035) (by norm_num)
theorem B2282861 : Blo 1520457 2282861 := bbase (se 3 (by rfl) ⟨428036, by rfl⟩ : syracuseStep 2282861 = 856073) (by norm_num)
theorem B3421565 : Blo 1520457 3421565 := bbase (se 3 (by rfl) ⟨641543, by rfl⟩ : syracuseStep 3421565 = 1283087) (by norm_num)
theorem B3249533 : Blo 1520457 3249533 := bbase (se 3 (by rfl) ⟨609287, by rfl⟩ : syracuseStep 3249533 = 1218575) (by norm_num)
theorem B2282885 : Blo 1520457 2282885 := bbase (se 4 (by rfl) ⟨214020, by rfl⟩ : syracuseStep 2282885 = 428041) (by norm_num)
theorem B2282909 : Blo 1520457 2282909 := bbase (se 3 (by rfl) ⟨428045, by rfl⟩ : syracuseStep 2282909 = 856091) (by norm_num)
theorem B2282933 : Blo 1520457 2282933 := bbase (se 5 (by rfl) ⟨107012, by rfl⟩ : syracuseStep 2282933 = 214025) (by norm_num)
theorem B3421637 : Blo 1520457 3421637 := bbase (se 4 (by rfl) ⟨320778, by rfl⟩ : syracuseStep 3421637 = 641557) (by norm_num)
theorem B2282957 : Blo 1520457 2282957 := bbase (se 3 (by rfl) ⟨428054, by rfl⟩ : syracuseStep 2282957 = 856109) (by norm_num)
theorem B1734097 : Blo 1520457 1734097 := bbase (se 2 (by rfl) ⟨650286, by rfl⟩ : syracuseStep 1734097 = 1300573) (by norm_num)
theorem B16455125 : Blo 1520457 16455125 := bbase (se 7 (by rfl) ⟨192833, by rfl⟩ : syracuseStep 16455125 = 385667) (by norm_num)
theorem B2282981 : Blo 1520457 2282981 := bbase (se 4 (by rfl) ⟨214029, by rfl⟩ : syracuseStep 2282981 = 428059) (by norm_num)
theorem B2283005 : Blo 1520457 2283005 := bbase (se 3 (by rfl) ⟨428063, by rfl⟩ : syracuseStep 2283005 = 856127) (by norm_num)
theorem B3421709 : Blo 1520457 3421709 := bbase (se 3 (by rfl) ⟨641570, by rfl⟩ : syracuseStep 3421709 = 1283141) (by norm_num)
theorem B3249677 : Blo 1520457 3249677 := bbase (se 3 (by rfl) ⟨609314, by rfl⟩ : syracuseStep 3249677 = 1218629) (by norm_num)
theorem B2283029 : Blo 1520457 2283029 := bbase (se 6 (by rfl) ⟨53508, by rfl⟩ : syracuseStep 2283029 = 107017) (by norm_num)
theorem B2283053 : Blo 1520457 2283053 := bbase (se 3 (by rfl) ⟨428072, by rfl⟩ : syracuseStep 2283053 = 856145) (by norm_num)
theorem B2283077 : Blo 1520457 2283077 := bbase (se 4 (by rfl) ⟨214038, by rfl⟩ : syracuseStep 2283077 = 428077) (by norm_num)
theorem B3421781 : Blo 1520457 3421781 := bbase (se 8 (by rfl) ⟨20049, by rfl⟩ : syracuseStep 3421781 = 40099) (by norm_num)
theorem B2283101 : Blo 1520457 2283101 := bbase (se 3 (by rfl) ⟨428081, by rfl⟩ : syracuseStep 2283101 = 856163) (by norm_num)
theorem B2602597 : Blo 1520457 2602597 := bbase (se 4 (by rfl) ⟨243993, by rfl⟩ : syracuseStep 2602597 = 487987) (by norm_num)
theorem B5133941 : Blo 1520457 5133941 := bbase (se 5 (by rfl) ⟨240653, by rfl⟩ : syracuseStep 5133941 = 481307) (by norm_num)
theorem B2283125 : Blo 1520457 2283125 := bbase (se 5 (by rfl) ⟨107021, by rfl⟩ : syracuseStep 2283125 = 214043) (by norm_num)
theorem B2283149 : Blo 1520457 2283149 := bbase (se 3 (by rfl) ⟨428090, by rfl⟩ : syracuseStep 2283149 = 856181) (by norm_num)
theorem B3421853 : Blo 1520457 3421853 := bbase (se 3 (by rfl) ⟨641597, by rfl⟩ : syracuseStep 3421853 = 1283195) (by norm_num)
theorem B2283173 : Blo 1520457 2283173 := bbase (se 4 (by rfl) ⟨214047, by rfl⟩ : syracuseStep 2283173 = 428095) (by norm_num)
theorem B2283197 : Blo 1520457 2283197 := bbase (se 3 (by rfl) ⟨428099, by rfl⟩ : syracuseStep 2283197 = 856199) (by norm_num)
theorem B2283221 : Blo 1520457 2283221 := bbase (se 7 (by rfl) ⟨26756, by rfl⟩ : syracuseStep 2283221 = 53513) (by norm_num)
theorem B3421925 : Blo 1520457 3421925 := bbase (se 4 (by rfl) ⟨320805, by rfl⟩ : syracuseStep 3421925 = 641611) (by norm_num)
theorem B2889445 : Blo 1520457 2889445 := bbase (se 4 (by rfl) ⟨270885, by rfl⟩ : syracuseStep 2889445 = 541771) (by norm_num)
theorem B2283245 : Blo 1520457 2283245 := bbase (se 3 (by rfl) ⟨428108, by rfl⟩ : syracuseStep 2283245 = 856217) (by norm_num)
theorem B1734385 : Blo 1520457 1734385 := bbase (se 2 (by rfl) ⟨650394, by rfl⟩ : syracuseStep 1734385 = 1300789) (by norm_num)
theorem B2283269 : Blo 1520457 2283269 := bbase (se 4 (by rfl) ⟨214056, by rfl⟩ : syracuseStep 2283269 = 428113) (by norm_num)
theorem B2283293 : Blo 1520457 2283293 := bbase (se 3 (by rfl) ⟨428117, by rfl⟩ : syracuseStep 2283293 = 856235) (by norm_num)
theorem B3421997 : Blo 1520457 3421997 := bbase (se 3 (by rfl) ⟨641624, by rfl⟩ : syracuseStep 3421997 = 1283249) (by norm_num)
theorem B2283317 : Blo 1520457 2283317 := bbase (se 5 (by rfl) ⟨107030, by rfl⟩ : syracuseStep 2283317 = 214061) (by norm_num)
theorem B2283341 : Blo 1520457 2283341 := bbase (se 3 (by rfl) ⟨428126, by rfl⟩ : syracuseStep 2283341 = 856253) (by norm_num)
theorem B7313237 : Blo 1520457 7313237 := bbase (se 9 (by rfl) ⟨21425, by rfl⟩ : syracuseStep 7313237 = 42851) (by norm_num)
theorem B3471205 : Blo 1520457 3471205 := bbase (se 4 (by rfl) ⟨325425, by rfl⟩ : syracuseStep 3471205 = 650851) (by norm_num)
theorem B2283365 : Blo 1520457 2283365 := bbase (se 4 (by rfl) ⟨214065, by rfl⟩ : syracuseStep 2283365 = 428131) (by norm_num)
theorem B3422069 : Blo 1520457 3422069 := bbase (se 5 (by rfl) ⟨160409, by rfl⟩ : syracuseStep 3422069 = 320819) (by norm_num)
theorem B3250037 : Blo 1520457 3250037 := bbase (se 5 (by rfl) ⟨152345, by rfl⟩ : syracuseStep 3250037 = 304691) (by norm_num)
theorem B2889589 : Blo 1520457 2889589 := bbase (se 5 (by rfl) ⟨135449, by rfl⟩ : syracuseStep 2889589 = 270899) (by norm_num)
theorem B2283389 : Blo 1520457 2283389 := bbase (se 3 (by rfl) ⟨428135, by rfl⟩ : syracuseStep 2283389 = 856271) (by norm_num)
theorem B7706501 : Blo 1520457 7706501 := bbase (se 4 (by rfl) ⟨722484, by rfl⟩ : syracuseStep 7706501 = 1444969) (by norm_num)
theorem B2283413 : Blo 1520457 2283413 := bbase (se 6 (by rfl) ⟨53517, by rfl⟩ : syracuseStep 2283413 = 107035) (by norm_num)
theorem B2283437 : Blo 1520457 2283437 := bbase (se 3 (by rfl) ⟨428144, by rfl⟩ : syracuseStep 2283437 = 856289) (by norm_num)
theorem B3422141 : Blo 1520457 3422141 := bbase (se 3 (by rfl) ⟨641651, by rfl⟩ : syracuseStep 3422141 = 1283303) (by norm_num)
theorem B2283461 : Blo 1520457 2283461 := bbase (se 4 (by rfl) ⟨214074, by rfl⟩ : syracuseStep 2283461 = 428149) (by norm_num)
theorem B2283485 : Blo 1520457 2283485 := bbase (se 3 (by rfl) ⟨428153, by rfl⟩ : syracuseStep 2283485 = 856307) (by norm_num)
theorem B5773301 : Blo 1520457 5773301 := bbase (se 5 (by rfl) ⟨270623, by rfl⟩ : syracuseStep 5773301 = 541247) (by norm_num)
theorem B2283509 : Blo 1520457 2283509 := bbase (se 5 (by rfl) ⟨107039, by rfl⟩ : syracuseStep 2283509 = 214079) (by norm_num)
theorem B3422213 : Blo 1520457 3422213 := bbase (se 4 (by rfl) ⟨320832, by rfl⟩ : syracuseStep 3422213 = 641665) (by norm_num)
theorem B2283533 : Blo 1520457 2283533 := bbase (se 3 (by rfl) ⟨428162, by rfl⟩ : syracuseStep 2283533 = 856325) (by norm_num)
theorem B2889749 : Blo 1520457 2889749 := bbase (se 6 (by rfl) ⟨67728, by rfl⟩ : syracuseStep 2889749 = 135457) (by norm_num)
theorem B5134373 : Blo 1520457 5134373 := bbase (se 4 (by rfl) ⟨481347, by rfl⟩ : syracuseStep 5134373 = 962695) (by norm_num)
theorem B5486629 : Blo 1520457 5486629 := bbase (se 4 (by rfl) ⟨514371, by rfl⟩ : syracuseStep 5486629 = 1028743) (by norm_num)
theorem B2283557 : Blo 1520457 2283557 := bbase (se 4 (by rfl) ⟨214083, by rfl⟩ : syracuseStep 2283557 = 428167) (by norm_num)
theorem B2283581 : Blo 1520457 2283581 := bbase (se 3 (by rfl) ⟨428171, by rfl⟩ : syracuseStep 2283581 = 856343) (by norm_num)
theorem B3422285 : Blo 1520457 3422285 := bbase (se 3 (by rfl) ⟨641678, by rfl⟩ : syracuseStep 3422285 = 1283357) (by norm_num)
theorem B2283605 : Blo 1520457 2283605 := bbase (se 8 (by rfl) ⟨13380, by rfl⟩ : syracuseStep 2283605 = 26761) (by norm_num)
theorem B2283629 : Blo 1520457 2283629 := bbase (se 3 (by rfl) ⟨428180, by rfl⟩ : syracuseStep 2283629 = 856361) (by norm_num)
theorem B2283653 : Blo 1520457 2283653 := bbase (se 4 (by rfl) ⟨214092, by rfl⟩ : syracuseStep 2283653 = 428185) (by norm_num)
theorem B3422357 : Blo 1520457 3422357 := bbase (se 6 (by rfl) ⟨80211, by rfl⟩ : syracuseStep 3422357 = 160423) (by norm_num)
theorem B2283677 : Blo 1520457 2283677 := bbase (se 3 (by rfl) ⟨428189, by rfl⟩ : syracuseStep 2283677 = 856379) (by norm_num)
theorem B2889893 : Blo 1520457 2889893 := bbase (se 4 (by rfl) ⟨270927, by rfl⟩ : syracuseStep 2889893 = 541855) (by norm_num)
theorem B5486773 : Blo 1520457 5486773 := bbase (se 5 (by rfl) ⟨257192, by rfl⟩ : syracuseStep 5486773 = 514385) (by norm_num)
theorem B3422429 : Blo 1520457 3422429 := bbase (se 3 (by rfl) ⟨641705, by rfl⟩ : syracuseStep 3422429 = 1283411) (by norm_num)
theorem B2742493 : Blo 1520457 2742493 := bbase (se 3 (by rfl) ⟨514217, by rfl⟩ : syracuseStep 2742493 = 1028435) (by norm_num)
theorem B1759477 : Blo 1520457 1759477 := bbase (se 5 (by rfl) ⟨82475, by rfl⟩ : syracuseStep 1759477 = 164951) (by norm_num)
theorem B5773589 : Blo 1520457 5773589 := bbase (se 6 (by rfl) ⟨135318, by rfl⟩ : syracuseStep 5773589 = 270637) (by norm_num)
theorem B7698725 : Blo 1520457 7698725 := bbase (se 4 (by rfl) ⟨721755, by rfl⟩ : syracuseStep 7698725 = 1443511) (by norm_num)
theorem B3422501 : Blo 1520457 3422501 := bbase (se 4 (by rfl) ⟨320859, by rfl⟩ : syracuseStep 3422501 = 641719) (by norm_num)
theorem B5486933 : Blo 1520457 5486933 := bbase (se 10 (by rfl) ⟨8037, by rfl⟩ : syracuseStep 5486933 = 16075) (by norm_num)
theorem B3422573 : Blo 1520457 3422573 := bbase (se 3 (by rfl) ⟨641732, by rfl⟩ : syracuseStep 3422573 = 1283465) (by norm_num)
theorem B1710517 : Blo 1520457 1710517 := bbase (se 5 (by rfl) ⟨80180, by rfl⟩ : syracuseStep 1710517 = 160361) (by norm_num)
theorem B3422645 : Blo 1520457 3422645 := bbase (se 5 (by rfl) ⟨160436, by rfl⟩ : syracuseStep 3422645 = 320873) (by norm_num)
theorem B2890181 : Blo 1520457 2890181 := bbase (se 4 (by rfl) ⟨270954, by rfl⟩ : syracuseStep 2890181 = 541909) (by norm_num)
theorem B5134805 : Blo 1520457 5134805 := bbase (se 7 (by rfl) ⟨60173, by rfl⟩ : syracuseStep 5134805 = 120347) (by norm_num)
theorem B1710553 : Blo 1520457 1710553 := bbase (se 2 (by rfl) ⟨641457, by rfl⟩ : syracuseStep 1710553 = 1282915) (by norm_num)
theorem B4110821 : Blo 1520457 4110821 := bbase (se 4 (by rfl) ⟨385389, by rfl⟩ : syracuseStep 4110821 = 770779) (by norm_num)
theorem B1710589 : Blo 1520457 1710589 := bbase (se 3 (by rfl) ⟨320735, by rfl⟩ : syracuseStep 1710589 = 641471) (by norm_num)
theorem B3422717 : Blo 1520457 3422717 := bbase (se 3 (by rfl) ⟨641759, by rfl⟩ : syracuseStep 3422717 = 1283519) (by norm_num)
theorem B2742781 : Blo 1520457 2742781 := bbase (se 3 (by rfl) ⟨514271, by rfl⟩ : syracuseStep 2742781 = 1028543) (by norm_num)
theorem B4332037 : Blo 1520457 4332037 := bbase (se 4 (by rfl) ⟨406128, by rfl⟩ : syracuseStep 4332037 = 812257) (by norm_num)
theorem B1710625 : Blo 1520457 1710625 := bbase (se 2 (by rfl) ⟨641484, by rfl⟩ : syracuseStep 1710625 = 1282969) (by norm_num)
theorem B1710661 : Blo 1520457 1710661 := bbase (se 4 (by rfl) ⟨160374, by rfl⟩ : syracuseStep 1710661 = 320749) (by norm_num)
theorem B4872773 : Blo 1520457 4872773 := bbase (se 4 (by rfl) ⟨456822, by rfl⟩ : syracuseStep 4872773 = 913645) (by norm_num)
theorem B3422789 : Blo 1520457 3422789 := bbase (se 4 (by rfl) ⟨320886, by rfl⟩ : syracuseStep 3422789 = 641773) (by norm_num)
theorem B1710697 : Blo 1520457 1710697 := bbase (se 2 (by rfl) ⟨641511, by rfl⟩ : syracuseStep 1710697 = 1283023) (by norm_num)
theorem B3906173 : Blo 1520457 3906173 := bbase (se 3 (by rfl) ⟨732407, by rfl⟩ : syracuseStep 3906173 = 1464815) (by norm_num)
theorem B1710733 : Blo 1520457 1710733 := bbase (se 3 (by rfl) ⟨320762, by rfl⟩ : syracuseStep 1710733 = 641525) (by norm_num)
theorem B3422861 : Blo 1520457 3422861 := bbase (se 3 (by rfl) ⟨641786, by rfl⟩ : syracuseStep 3422861 = 1283573) (by norm_num)
theorem B4332197 : Blo 1520457 4332197 := bbase (se 4 (by rfl) ⟨406143, by rfl⟩ : syracuseStep 4332197 = 812287) (by norm_num)
theorem B1710769 : Blo 1520457 1710769 := bbase (se 2 (by rfl) ⟨641538, by rfl⟩ : syracuseStep 1710769 = 1283077) (by norm_num)
theorem B3848917 : Blo 1520457 3848917 := bbase (se 7 (by rfl) ⟨45104, by rfl⟩ : syracuseStep 3848917 = 90209) (by norm_num)
theorem B1710805 : Blo 1520457 1710805 := bbase (se 7 (by rfl) ⟨20048, by rfl⟩ : syracuseStep 1710805 = 40097) (by norm_num)
theorem B6937301 : Blo 1520457 6937301 := bbase (se 7 (by rfl) ⟨81296, by rfl⟩ : syracuseStep 6937301 = 162593) (by norm_num)
theorem B3422933 : Blo 1520457 3422933 := bbase (se 7 (by rfl) ⟨40112, by rfl⟩ : syracuseStep 3422933 = 80225) (by norm_num)
theorem B3250925 : Blo 1520457 3250925 := bbase (se 3 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 3250925 = 1219097) (by norm_num)
theorem B1710841 : Blo 1520457 1710841 := bbase (se 2 (by rfl) ⟨641565, by rfl⟩ : syracuseStep 1710841 = 1283131) (by norm_num)
theorem B1710877 : Blo 1520457 1710877 := bbase (se 3 (by rfl) ⟨320789, by rfl⟩ : syracuseStep 1710877 = 641579) (by norm_num)
theorem B3423005 : Blo 1520457 3423005 := bbase (se 3 (by rfl) ⟨641813, by rfl⟩ : syracuseStep 3423005 = 1283627) (by norm_num)
theorem B1710913 : Blo 1520457 1710913 := bbase (se 2 (by rfl) ⟨641592, by rfl⟩ : syracuseStep 1710913 = 1283185) (by norm_num)
theorem B3849029 : Blo 1520457 3849029 := bbase (se 4 (by rfl) ⟨360846, by rfl⟩ : syracuseStep 3849029 = 721693) (by norm_num)
theorem B1710949 : Blo 1520457 1710949 := bbase (se 4 (by rfl) ⟨160401, by rfl⟩ : syracuseStep 1710949 = 320803) (by norm_num)
theorem B3423077 : Blo 1520457 3423077 := bbase (se 4 (by rfl) ⟨320913, by rfl⟩ : syracuseStep 3423077 = 641827) (by norm_num)
theorem B1735553 : Blo 1520457 1735553 := bbase (se 2 (by rfl) ⟨650832, by rfl⟩ : syracuseStep 1735553 = 1301665) (by norm_num)
theorem B5135237 : Blo 1520457 5135237 := bbase (se 4 (by rfl) ⟨481428, by rfl⟩ : syracuseStep 5135237 = 962857) (by norm_num)
theorem B1710985 : Blo 1520457 1710985 := bbase (se 2 (by rfl) ⟨641619, by rfl⟩ : syracuseStep 1710985 = 1283239) (by norm_num)
theorem B4111253 : Blo 1520457 4111253 := bbase (se 6 (by rfl) ⟨96357, by rfl⟩ : syracuseStep 4111253 = 192715) (by norm_num)
theorem B4332437 : Blo 1520457 4332437 := bbase (se 6 (by rfl) ⟨101541, by rfl⟩ : syracuseStep 4332437 = 203083) (by norm_num)
theorem B1711021 : Blo 1520457 1711021 := bbase (se 3 (by rfl) ⟨320816, by rfl⟩ : syracuseStep 1711021 = 641633) (by norm_num)
theorem B3423149 : Blo 1520457 3423149 := bbase (se 3 (by rfl) ⟨641840, by rfl⟩ : syracuseStep 3423149 = 1283681) (by norm_num)
theorem B1711057 : Blo 1520457 1711057 := bbase (se 2 (by rfl) ⟨641646, by rfl⟩ : syracuseStep 1711057 = 1283293) (by norm_num)
theorem B3251173 : Blo 1520457 3251173 := bbase (se 4 (by rfl) ⟨304797, by rfl⟩ : syracuseStep 3251173 = 609595) (by norm_num)
theorem B1711093 : Blo 1520457 1711093 := bbase (se 5 (by rfl) ⟨80207, by rfl⟩ : syracuseStep 1711093 = 160415) (by norm_num)
theorem B3423221 : Blo 1520457 3423221 := bbase (se 5 (by rfl) ⟨160463, by rfl⟩ : syracuseStep 3423221 = 320927) (by norm_num)
theorem B3849221 : Blo 1520457 3849221 := bbase (se 4 (by rfl) ⟨360864, by rfl⟩ : syracuseStep 3849221 = 721729) (by norm_num)
theorem B1711129 : Blo 1520457 1711129 := bbase (se 2 (by rfl) ⟨641673, by rfl⟩ : syracuseStep 1711129 = 1283347) (by norm_num)
theorem B1711165 : Blo 1520457 1711165 := bbase (se 3 (by rfl) ⟨320843, by rfl⟩ : syracuseStep 1711165 = 641687) (by norm_num)
theorem B3423293 : Blo 1520457 3423293 := bbase (se 3 (by rfl) ⟨641867, by rfl⟩ : syracuseStep 3423293 = 1283735) (by norm_num)
theorem B2743357 : Blo 1520457 2743357 := bbase (se 3 (by rfl) ⟨514379, by rfl⟩ : syracuseStep 2743357 = 1028759) (by norm_num)
theorem B4332629 : Blo 1520457 4332629 := bbase (se 8 (by rfl) ⟨25386, by rfl⟩ : syracuseStep 4332629 = 50773) (by norm_num)
theorem B1711201 : Blo 1520457 1711201 := bbase (se 2 (by rfl) ⟨641700, by rfl⟩ : syracuseStep 1711201 = 1283401) (by norm_num)
theorem B1711237 : Blo 1520457 1711237 := bbase (se 4 (by rfl) ⟨160428, by rfl⟩ : syracuseStep 1711237 = 320857) (by norm_num)
theorem B3423365 : Blo 1520457 3423365 := bbase (se 4 (by rfl) ⟨320940, by rfl⟩ : syracuseStep 3423365 = 641881) (by norm_num)
theorem B4168837 : Blo 1520457 4168837 := bbase (se 4 (by rfl) ⟨390828, by rfl⟩ : syracuseStep 4168837 = 781657) (by norm_num)
theorem B8666261 : Blo 1520457 8666261 := bbase (se 6 (by rfl) ⟨203115, by rfl⟩ : syracuseStep 8666261 = 406231) (by norm_num)
theorem B1711273 : Blo 1520457 1711273 := bbase (se 2 (by rfl) ⟨641727, by rfl⟩ : syracuseStep 1711273 = 1283455) (by norm_num)
theorem B1711309 : Blo 1520457 1711309 := bbase (se 3 (by rfl) ⟨320870, by rfl⟩ : syracuseStep 1711309 = 641741) (by norm_num)
theorem B3423437 : Blo 1520457 3423437 := bbase (se 3 (by rfl) ⟨641894, by rfl⟩ : syracuseStep 3423437 = 1283789) (by norm_num)
theorem B1924337 : Blo 1520457 1924337 := bbase (se 2 (by rfl) ⟨721626, by rfl⟩ : syracuseStep 1924337 = 1443253) (by norm_num)
theorem B1711345 : Blo 1520457 1711345 := bbase (se 2 (by rfl) ⟨641754, by rfl⟩ : syracuseStep 1711345 = 1283509) (by norm_num)
theorem B9747701 : Blo 1520457 9747701 := bbase (se 5 (by rfl) ⟨456923, by rfl⟩ : syracuseStep 9747701 = 913847) (by norm_num)
theorem B1711381 : Blo 1520457 1711381 := bbase (se 6 (by rfl) ⟨40110, by rfl⟩ : syracuseStep 1711381 = 80221) (by norm_num)
theorem B3423509 : Blo 1520457 3423509 := bbase (se 6 (by rfl) ⟨80238, by rfl⟩ : syracuseStep 3423509 = 160477) (by norm_num)
theorem B1924393 : Blo 1520457 1924393 := bbase (se 2 (by rfl) ⟨721647, by rfl⟩ : syracuseStep 1924393 = 1443295) (by norm_num)
theorem B5135669 : Blo 1520457 5135669 := bbase (se 5 (by rfl) ⟨240734, by rfl⟩ : syracuseStep 5135669 = 481469) (by norm_num)
theorem B1711417 : Blo 1520457 1711417 := bbase (se 2 (by rfl) ⟨641781, by rfl⟩ : syracuseStep 1711417 = 1283563) (by norm_num)
theorem B1711453 : Blo 1520457 1711453 := bbase (se 3 (by rfl) ⟨320897, by rfl⟩ : syracuseStep 1711453 = 641795) (by norm_num)
theorem B3849565 : Blo 1520457 3849565 := bbase (se 3 (by rfl) ⟨721793, by rfl⟩ : syracuseStep 3849565 = 1443587) (by norm_num)
theorem B3423581 : Blo 1520457 3423581 := bbase (se 3 (by rfl) ⟨641921, by rfl⟩ : syracuseStep 3423581 = 1283843) (by norm_num)
theorem B1711489 : Blo 1520457 1711489 := bbase (se 2 (by rfl) ⟨641808, by rfl⟩ : syracuseStep 1711489 = 1283617) (by norm_num)
theorem B1924489 : Blo 1520457 1924489 := bbase (se 2 (by rfl) ⟨721683, by rfl⟩ : syracuseStep 1924489 = 1443367) (by norm_num)
theorem B1711525 : Blo 1520457 1711525 := bbase (se 4 (by rfl) ⟨160455, by rfl⟩ : syracuseStep 1711525 = 320911) (by norm_num)
theorem B3423653 : Blo 1520457 3423653 := bbase (se 4 (by rfl) ⟨320967, by rfl⟩ : syracuseStep 3423653 = 641935) (by norm_num)
theorem B5774773 : Blo 1520457 5774773 := bbase (se 5 (by rfl) ⟨270692, by rfl⟩ : syracuseStep 5774773 = 541385) (by norm_num)
theorem B1711561 : Blo 1520457 1711561 := bbase (se 2 (by rfl) ⟨641835, by rfl⟩ : syracuseStep 1711561 = 1283671) (by norm_num)
theorem B3849677 : Blo 1520457 3849677 := bbase (se 3 (by rfl) ⟨721814, by rfl⟩ : syracuseStep 3849677 = 1443629) (by norm_num)
theorem B1711597 : Blo 1520457 1711597 := bbase (se 3 (by rfl) ⟨320924, by rfl⟩ : syracuseStep 1711597 = 641849) (by norm_num)
theorem B3423725 : Blo 1520457 3423725 := bbase (se 3 (by rfl) ⟨641948, by rfl⟩ : syracuseStep 3423725 = 1283897) (by norm_num)
theorem B1711633 : Blo 1520457 1711633 := bbase (se 2 (by rfl) ⟨641862, by rfl⟩ : syracuseStep 1711633 = 1283725) (by norm_num)
theorem B1924661 : Blo 1520457 1924661 := bbase (se 5 (by rfl) ⟨90218, by rfl⟩ : syracuseStep 1924661 = 180437) (by norm_num)
theorem B7700021 : Blo 1520457 7700021 := bbase (se 5 (by rfl) ⟨360938, by rfl⟩ : syracuseStep 7700021 = 721877) (by norm_num)
theorem B1711669 : Blo 1520457 1711669 := bbase (se 5 (by rfl) ⟨80234, by rfl⟩ : syracuseStep 1711669 = 160469) (by norm_num)
theorem B3423797 : Blo 1520457 3423797 := bbase (se 5 (by rfl) ⟨160490, by rfl⟩ : syracuseStep 3423797 = 320981) (by norm_num)
theorem B4628053 : Blo 1520457 4628053 := bbase (se 8 (by rfl) ⟨27117, by rfl⟩ : syracuseStep 4628053 = 54235) (by norm_num)
theorem B1711705 : Blo 1520457 1711705 := bbase (se 2 (by rfl) ⟨641889, by rfl⟩ : syracuseStep 1711705 = 1283779) (by norm_num)
theorem B1924717 : Blo 1520457 1924717 := bbase (se 3 (by rfl) ⟨360884, by rfl⟩ : syracuseStep 1924717 = 721769) (by norm_num)
theorem B1711741 : Blo 1520457 1711741 := bbase (se 3 (by rfl) ⟨320951, by rfl⟩ : syracuseStep 1711741 = 641903) (by norm_num)
theorem B3423869 : Blo 1520457 3423869 := bbase (se 3 (by rfl) ⟨641975, by rfl⟩ : syracuseStep 3423869 = 1283951) (by norm_num)
theorem B3849869 : Blo 1520457 3849869 := bbase (se 3 (by rfl) ⟨721850, by rfl⟩ : syracuseStep 3849869 = 1443701) (by norm_num)
theorem B1711777 : Blo 1520457 1711777 := bbase (se 2 (by rfl) ⟨641916, by rfl⟩ : syracuseStep 1711777 = 1283833) (by norm_num)
theorem B1711813 : Blo 1520457 1711813 := bbase (se 4 (by rfl) ⟨160482, by rfl⟩ : syracuseStep 1711813 = 320965) (by norm_num)
theorem B3423941 : Blo 1520457 3423941 := bbase (se 4 (by rfl) ⟨320994, by rfl⟩ : syracuseStep 3423941 = 641989) (by norm_num)
theorem B1924813 : Blo 1520457 1924813 := bbase (se 3 (by rfl) ⟨360902, by rfl⟩ : syracuseStep 1924813 = 721805) (by norm_num)
theorem B5775077 : Blo 1520457 5775077 := bbase (se 4 (by rfl) ⟨541413, by rfl⟩ : syracuseStep 5775077 = 1082827) (by norm_num)
theorem B5136101 : Blo 1520457 5136101 := bbase (se 4 (by rfl) ⟨481509, by rfl⟩ : syracuseStep 5136101 = 963019) (by norm_num)
theorem B1711849 : Blo 1520457 1711849 := bbase (se 2 (by rfl) ⟨641943, by rfl⟩ : syracuseStep 1711849 = 1283887) (by norm_num)
theorem B1711885 : Blo 1520457 1711885 := bbase (se 3 (by rfl) ⟨320978, by rfl⟩ : syracuseStep 1711885 = 641957) (by norm_num)
theorem B3424013 : Blo 1520457 3424013 := bbase (se 3 (by rfl) ⟨642002, by rfl⟩ : syracuseStep 3424013 = 1284005) (by norm_num)
theorem B1711921 : Blo 1520457 1711921 := bbase (se 2 (by rfl) ⟨641970, by rfl⟩ : syracuseStep 1711921 = 1283941) (by norm_num)
theorem B1711957 : Blo 1520457 1711957 := bbase (se 9 (by rfl) ⟨5015, by rfl⟩ : syracuseStep 1711957 = 10031) (by norm_num)
theorem B3424085 : Blo 1520457 3424085 := bbase (se 9 (by rfl) ⟨10031, by rfl⟩ : syracuseStep 3424085 = 20063) (by norm_num)
theorem B1924985 : Blo 1520457 1924985 := bbase (se 2 (by rfl) ⟨721869, by rfl⟩ : syracuseStep 1924985 = 1443739) (by norm_num)
theorem B1711993 : Blo 1520457 1711993 := bbase (se 2 (by rfl) ⟨641997, by rfl⟩ : syracuseStep 1711993 = 1283995) (by norm_num)
theorem B1712029 : Blo 1520457 1712029 := bbase (se 3 (by rfl) ⟨321005, by rfl⟩ : syracuseStep 1712029 = 642011) (by norm_num)
theorem B3424157 : Blo 1520457 3424157 := bbase (se 3 (by rfl) ⟨642029, by rfl⟩ : syracuseStep 3424157 = 1284059) (by norm_num)
theorem B1925041 : Blo 1520457 1925041 := bbase (se 2 (by rfl) ⟨721890, by rfl⟩ : syracuseStep 1925041 = 1443781) (by norm_num)
theorem B8339381 : Blo 1520457 8339381 := bbase (se 5 (by rfl) ⟨390908, by rfl⟩ : syracuseStep 8339381 = 781817) (by norm_num)
theorem B1712065 : Blo 1520457 1712065 := bbase (se 2 (by rfl) ⟨642024, by rfl⟩ : syracuseStep 1712065 = 1284049) (by norm_num)
theorem B3653581 : Blo 1520457 3653581 := bbase (se 3 (by rfl) ⟨685046, by rfl⟩ : syracuseStep 3653581 = 1370093) (by norm_num)
theorem B1646557 : Blo 1520457 1646557 := bbase (se 3 (by rfl) ⟨308729, by rfl⟩ : syracuseStep 1646557 = 617459) (by norm_num)
theorem B3850213 : Blo 1520457 3850213 := bbase (se 4 (by rfl) ⟨360957, by rfl⟩ : syracuseStep 3850213 = 721915) (by norm_num)
theorem B1712101 : Blo 1520457 1712101 := bbase (se 4 (by rfl) ⟨160509, by rfl⟩ : syracuseStep 1712101 = 321019) (by norm_num)
theorem B3424229 : Blo 1520457 3424229 := bbase (se 4 (by rfl) ⟨321021, by rfl⟩ : syracuseStep 3424229 = 642043) (by norm_num)
theorem B6168565 : Blo 1520457 6168565 := bbase (se 5 (by rfl) ⟨289151, by rfl⟩ : syracuseStep 6168565 = 578303) (by norm_num)
theorem B7315505 : Blo 1520457 7315505 := bstep (se 2 (by rfl) ⟨2743314, by rfl⟩ : syracuseStep 7315505 = 5486629) B5486629
theorem B3424337 : Blo 1520457 3424337 := bstep (se 2 (by rfl) ⟨1284126, by rfl⟩ : syracuseStep 3424337 = 2568253) B2568253
theorem B1925203 : Blo 1520457 1925203 := bstep (se 1 (by rfl) ⟨1443902, by rfl⟩ : syracuseStep 1925203 = 2887805) B2887805
theorem B3424355 : Blo 1520457 3424355 := bstep (se 1 (by rfl) ⟨2568266, by rfl⟩ : syracuseStep 3424355 = 5136533) B5136533
theorem B1712227 : Blo 1520457 1712227 := bstep (se 1 (by rfl) ⟨1284170, by rfl⟩ : syracuseStep 1712227 = 2568341) B2568341
theorem B4874413 : Blo 1520457 4874413 := bstep (se 3 (by rfl) ⟨913952, by rfl⟩ : syracuseStep 4874413 = 1827905) B1827905
theorem B1925299 : Blo 1520457 1925299 := bstep (se 1 (by rfl) ⟨1443974, by rfl⟩ : syracuseStep 1925299 = 2887949) B2887949
theorem B7315697 : Blo 1520457 7315697 := bstep (se 2 (by rfl) ⟨2743386, by rfl⟩ : syracuseStep 7315697 = 5486773) B5486773
theorem B1712371 : Blo 1520457 1712371 := bstep (se 1 (by rfl) ⟨1284278, by rfl⟩ : syracuseStep 1712371 = 2568557) B2568557
theorem B4333837 : Blo 1520457 4333837 := bstep (se 3 (by rfl) ⟨812594, by rfl⟩ : syracuseStep 4333837 = 1625189) B1625189
theorem B5136749 : Blo 1520457 5136749 := bstep (se 3 (by rfl) ⟨963140, by rfl⟩ : syracuseStep 5136749 = 1926281) B1926281
theorem B3424625 : Blo 1520457 3424625 := bstep (se 2 (by rfl) ⟨1284234, by rfl⟩ : syracuseStep 3424625 = 2568469) B2568469
theorem B3424643 : Blo 1520457 3424643 := bstep (se 1 (by rfl) ⟨2568482, by rfl⟩ : syracuseStep 3424643 = 5136965) B5136965
theorem B1712515 : Blo 1520457 1712515 := bstep (se 1 (by rfl) ⟨1284386, by rfl⟩ : syracuseStep 1712515 = 2568773) B2568773
theorem B58458509 : Blo 1520457 58458509 := bstep (se 3 (by rfl) ⟨10960970, by rfl⟩ : syracuseStep 58458509 = 21921941) B21921941
theorem B5136803 : Blo 1520457 5136803 := bstep (se 1 (by rfl) ⟨3852602, by rfl⟩ : syracuseStep 5136803 = 7705205) B7705205
theorem B1712659 : Blo 1520457 1712659 := bstep (se 1 (by rfl) ⟨1284494, by rfl⟩ : syracuseStep 1712659 = 2568989) B2568989
theorem B3424913 : Blo 1520457 3424913 := bstep (se 2 (by rfl) ⟨1284342, by rfl⟩ : syracuseStep 3424913 = 2568685) B2568685
theorem B7701155 : Blo 1520457 7701155 := bstep (se 1 (by rfl) ⟨5775866, by rfl⟩ : syracuseStep 7701155 = 11551733) B11551733
theorem B1925795 : Blo 1520457 1925795 := bstep (se 1 (by rfl) ⟨1444346, by rfl⟩ : syracuseStep 1925795 = 2888693) B2888693
theorem B3424931 : Blo 1520457 3424931 := bstep (se 1 (by rfl) ⟨2568698, by rfl⟩ : syracuseStep 3424931 = 5137397) B5137397
theorem B5776049 : Blo 1520457 5776049 := bstep (se 2 (by rfl) ⟨2166018, by rfl⟩ : syracuseStep 5776049 = 4332037) B4332037
theorem B5137073 : Blo 1520457 5137073 := bstep (se 2 (by rfl) ⟨1926402, by rfl⟩ : syracuseStep 5137073 = 3852805) B3852805
theorem B79086293 : Blo 1520457 79086293 := bstep (se 7 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 79086293 = 1853585) B1853585
theorem B25985933 : Blo 1520457 25985933 := bstep (se 3 (by rfl) ⟨4872362, by rfl⟩ : syracuseStep 25985933 = 9744725) B9744725
theorem B3851185 : Blo 1520457 3851185 := bstep (se 2 (by rfl) ⟨1444194, by rfl⟩ : syracuseStep 3851185 = 2888389) B2888389
theorem B3425201 : Blo 1520457 3425201 := bstep (se 2 (by rfl) ⟨1284450, by rfl⟩ : syracuseStep 3425201 = 2568901) B2568901
theorem B3425219 : Blo 1520457 3425219 := bstep (se 1 (by rfl) ⟨2568914, by rfl⟩ : syracuseStep 3425219 = 5137829) B5137829
theorem B10970083 : Blo 1520457 10970083 := bstep (se 1 (by rfl) ⟨8227562, by rfl⟩ : syracuseStep 10970083 = 16455125) B16455125
theorem B8659973 : Blo 1520457 8659973 := bstep (se 4 (by rfl) ⟨811872, by rfl⟩ : syracuseStep 8659973 = 1623745) B1623745
theorem B3851459 : Blo 1520457 3851459 := bstep (se 1 (by rfl) ⟨2888594, by rfl⟩ : syracuseStep 3851459 = 5777189) B5777189
theorem B5137613 : Blo 1520457 5137613 := bstep (se 3 (by rfl) ⟨963302, by rfl⟩ : syracuseStep 5137613 = 1926605) B1926605
theorem B3425489 : Blo 1520457 3425489 := bstep (se 2 (by rfl) ⟨1284558, by rfl⟩ : syracuseStep 3425489 = 2569117) B2569117
theorem B4875491 : Blo 1520457 4875491 := bstep (se 1 (by rfl) ⟨3656618, by rfl⟩ : syracuseStep 4875491 = 7313237) B7313237
theorem B3425507 : Blo 1520457 3425507 := bstep (se 1 (by rfl) ⟨2569130, by rfl⟩ : syracuseStep 3425507 = 5138261) B5138261
theorem B5137667 : Blo 1520457 5137667 := bstep (se 1 (by rfl) ⟨3853250, by rfl⟩ : syracuseStep 5137667 = 7706501) B7706501
theorem B4334897 : Blo 1520457 4334897 := bstep (se 2 (by rfl) ⟨1625586, by rfl⟩ : syracuseStep 4334897 = 3251173) B3251173
theorem B1852723 : Blo 1520457 1852723 := bstep (se 1 (by rfl) ⟨1389542, by rfl⟩ : syracuseStep 1852723 = 2779085) B2779085
theorem B5776717 : Blo 1520457 5776717 := bstep (se 3 (by rfl) ⟨1083134, by rfl⟩ : syracuseStep 5776717 = 2166269) B2166269
theorem B1926499 : Blo 1520457 1926499 := bstep (se 1 (by rfl) ⟨1444874, by rfl⟩ : syracuseStep 1926499 = 2889749) B2889749
theorem B3851651 : Blo 1520457 3851651 := bstep (se 1 (by rfl) ⟨2888738, by rfl⟩ : syracuseStep 3851651 = 5777477) B5777477
theorem B1926595 : Blo 1520457 1926595 := bstep (se 1 (by rfl) ⟨1444946, by rfl⟩ : syracuseStep 1926595 = 2889893) B2889893
theorem B8660429 : Blo 1520457 8660429 := bstep (se 3 (by rfl) ⟨1623830, by rfl⟩ : syracuseStep 8660429 = 3247661) B3247661
theorem B7701965 : Blo 1520457 7701965 := bstep (se 3 (by rfl) ⟨1444118, by rfl⟩ : syracuseStep 7701965 = 2888237) B2888237
theorem B5137937 : Blo 1520457 5137937 := bstep (se 2 (by rfl) ⟨1926726, by rfl⟩ : syracuseStep 5137937 = 3853453) B3853453
theorem B8898083 : Blo 1520457 8898083 := bstep (se 1 (by rfl) ⟨6673562, by rfl⟩ : syracuseStep 8898083 = 13347125) B13347125
theorem B8668721 : Blo 1520457 8668721 := bstep (se 2 (by rfl) ⟨3250770, by rfl⟩ : syracuseStep 8668721 = 6501541) B6501541
theorem B6588067 : Blo 1520457 6588067 := bstep (se 1 (by rfl) ⟨4941050, by rfl⟩ : syracuseStep 6588067 = 9882101) B9882101
theorem B2565857 : Blo 1520457 2565857 := bstep (se 2 (by rfl) ⟨962196, by rfl⟩ : syracuseStep 2565857 = 1924393) B1924393
theorem B2565985 : Blo 1520457 2565985 := bstep (se 2 (by rfl) ⟨962244, by rfl⟩ : syracuseStep 2565985 = 1924489) B1924489
theorem B4876145 : Blo 1520457 4876145 := bstep (se 2 (by rfl) ⟨1828554, by rfl⟩ : syracuseStep 4876145 = 3657109) B3657109
theorem B2566019 : Blo 1520457 2566019 := bstep (se 1 (by rfl) ⟨1924514, by rfl⟩ : syracuseStep 2566019 = 3849029) B3849029
theorem B2312129 : Blo 1520457 2312129 := bstep (se 2 (by rfl) ⟨867048, by rfl⟩ : syracuseStep 2312129 = 1734097) B1734097
theorem B2566147 : Blo 1520457 2566147 := bstep (se 1 (by rfl) ⟨1924610, by rfl⟩ : syracuseStep 2566147 = 3849221) B3849221
theorem B2312275 : Blo 1520457 2312275 := bstep (se 1 (by rfl) ⟨1734206, by rfl⟩ : syracuseStep 2312275 = 3468413) B3468413
theorem B5777507 : Blo 1520457 5777507 := bstep (se 1 (by rfl) ⟨4333130, by rfl⟩ : syracuseStep 5777507 = 8666261) B8666261
theorem B6170737 : Blo 1520457 6170737 := bstep (se 2 (by rfl) ⟨2314026, by rfl⟩ : syracuseStep 6170737 = 4628053) B4628053
theorem B2566289 : Blo 1520457 2566289 := bstep (se 2 (by rfl) ⟨962358, by rfl⟩ : syracuseStep 2566289 = 1924717) B1924717
theorem B2164897 : Blo 1520457 2164897 := bstep (se 2 (by rfl) ⟨811836, by rfl⟩ : syracuseStep 2164897 = 1623673) B1623673
theorem B6498467 : Blo 1520457 6498467 := bstep (se 1 (by rfl) ⟨4873850, by rfl⟩ : syracuseStep 6498467 = 9747701) B9747701
theorem B9750725 : Blo 1520457 9750725 := bstep (se 4 (by rfl) ⟨914130, by rfl⟩ : syracuseStep 9750725 = 1828261) B1828261
theorem B2566417 : Blo 1520457 2566417 := bstep (se 2 (by rfl) ⟨962406, by rfl⟩ : syracuseStep 2566417 = 1924813) B1924813
theorem B3852593 : Blo 1520457 3852593 := bstep (se 2 (by rfl) ⟨1444722, by rfl⟩ : syracuseStep 3852593 = 2889445) B2889445
theorem B2566451 : Blo 1520457 2566451 := bstep (se 1 (by rfl) ⟨1924838, by rfl⟩ : syracuseStep 2566451 = 3849677) B3849677
theorem B2312513 : Blo 1520457 2312513 := bstep (se 2 (by rfl) ⟨867192, by rfl⟩ : syracuseStep 2312513 = 1734385) B1734385
theorem B3901763 : Blo 1520457 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B3852643 : Blo 1520457 3852643 := bstep (se 1 (by rfl) ⟨2889482, by rfl⟩ : syracuseStep 3852643 = 5778965) B5778965
theorem B1952131 : Blo 1520457 1952131 := bstep (se 1 (by rfl) ⟨1464098, by rfl⟩ : syracuseStep 1952131 = 2928197) B2928197
theorem B2566579 : Blo 1520457 2566579 := bstep (se 1 (by rfl) ⟨1924934, by rfl⟩ : syracuseStep 2566579 = 3849869) B3849869
theorem B2165233 : Blo 1520457 2165233 := bstep (se 2 (by rfl) ⟨811962, by rfl⟩ : syracuseStep 2165233 = 1623925) B1623925
theorem B3852785 : Blo 1520457 3852785 := bstep (se 2 (by rfl) ⟨1444794, by rfl⟩ : syracuseStep 3852785 = 2889589) B2889589
theorem B3656195 : Blo 1520457 3656195 := bstep (se 1 (by rfl) ⟨2742146, by rfl⟩ : syracuseStep 3656195 = 5484293) B5484293
theorem B2566721 : Blo 1520457 2566721 := bstep (se 2 (by rfl) ⟨962520, by rfl⟩ : syracuseStep 2566721 = 1925041) B1925041
theorem B2566849 : Blo 1520457 2566849 := bstep (se 2 (by rfl) ⟨962568, by rfl⟩ : syracuseStep 2566849 = 1925137) B1925137
theorem B3656387 : Blo 1520457 3656387 := bstep (se 1 (by rfl) ⟨2742290, by rfl⟩ : syracuseStep 3656387 = 5484581) B5484581
theorem B2566883 : Blo 1520457 2566883 := bstep (se 1 (by rfl) ⟨1925162, by rfl⟩ : syracuseStep 2566883 = 3850325) B3850325
theorem B2345699 : Blo 1520457 2345699 := bstep (se 1 (by rfl) ⟨1759274, by rfl⟩ : syracuseStep 2345699 = 3518549) B3518549
theorem B5778161 : Blo 1520457 5778161 := bstep (se 2 (by rfl) ⟨2166810, by rfl⟩ : syracuseStep 5778161 = 4333621) B4333621
theorem B2567011 : Blo 1520457 2567011 := bstep (se 1 (by rfl) ⟨1925258, by rfl⟩ : syracuseStep 2567011 = 3850517) B3850517
theorem B11553677 : Blo 1520457 11553677 := bstep (se 3 (by rfl) ⟨2166314, by rfl⟩ : syracuseStep 11553677 = 4332629) B4332629
theorem B9743267 : Blo 1520457 9743267 := bstep (se 1 (by rfl) ⟨7307450, by rfl⟩ : syracuseStep 9743267 = 14614901) B14614901
theorem B3656657 : Blo 1520457 3656657 := bstep (se 2 (by rfl) ⟨1371246, by rfl⟩ : syracuseStep 3656657 = 2742493) B2742493
theorem B8670179 : Blo 1520457 8670179 := bstep (se 1 (by rfl) ⟨6502634, by rfl⟩ : syracuseStep 8670179 = 13005269) B13005269
theorem B2567153 : Blo 1520457 2567153 := bstep (se 2 (by rfl) ⟨962682, by rfl⟩ : syracuseStep 2567153 = 1925365) B1925365
theorem B2345969 : Blo 1520457 2345969 := bstep (se 2 (by rfl) ⟨879738, by rfl⟩ : syracuseStep 2345969 = 1759477) B1759477
theorem B2886673 : Blo 1520457 2886673 := bstep (se 2 (by rfl) ⟨1082502, by rfl⟩ : syracuseStep 2886673 = 2165005) B2165005
theorem B2436131 : Blo 1520457 2436131 := bstep (se 1 (by rfl) ⟨1827098, by rfl⟩ : syracuseStep 2436131 = 3654197) B3654197
theorem B2165825 : Blo 1520457 2165825 := bstep (se 2 (by rfl) ⟨812184, by rfl⟩ : syracuseStep 2165825 = 1624369) B1624369
theorem B2567281 : Blo 1520457 2567281 := bstep (se 2 (by rfl) ⟨962730, by rfl⟩ : syracuseStep 2567281 = 1925461) B1925461
theorem B2567315 : Blo 1520457 2567315 := bstep (se 1 (by rfl) ⟨1925486, by rfl⟩ : syracuseStep 2567315 = 3850973) B3850973
theorem B2436259 : Blo 1520457 2436259 := bstep (se 1 (by rfl) ⟨1827194, by rfl⟩ : syracuseStep 2436259 = 3654389) B3654389
theorem B2886833 : Blo 1520457 2886833 := bstep (se 2 (by rfl) ⟨1082562, by rfl⟩ : syracuseStep 2886833 = 2165125) B2165125
theorem B2280689 : Blo 1520457 2280689 := bstep (se 2 (by rfl) ⟨855258, by rfl⟩ : syracuseStep 2280689 = 1710517) B1710517
theorem B3902705 : Blo 1520457 3902705 := bstep (se 2 (by rfl) ⟨1463514, by rfl⟩ : syracuseStep 3902705 = 2927029) B2927029
theorem B2280707 : Blo 1520457 2280707 := bstep (se 1 (by rfl) ⟨1710530, by rfl⟩ : syracuseStep 2280707 = 3421061) B3421061
theorem B2567443 : Blo 1520457 2567443 := bstep (se 1 (by rfl) ⟨1925582, by rfl⟩ : syracuseStep 2567443 = 3851165) B3851165
theorem B2280737 : Blo 1520457 2280737 := bstep (se 2 (by rfl) ⟨855276, by rfl⟩ : syracuseStep 2280737 = 1710553) B1710553
theorem B5131565 : Blo 1520457 5131565 := bstep (se 3 (by rfl) ⟨962168, by rfl⟩ : syracuseStep 5131565 = 1924337) B1924337
theorem B2280755 : Blo 1520457 2280755 := bstep (se 1 (by rfl) ⟨1710566, by rfl⟩ : syracuseStep 2280755 = 3421133) B3421133
theorem B2280785 : Blo 1520457 2280785 := bstep (se 2 (by rfl) ⟨855294, by rfl⟩ : syracuseStep 2280785 = 1710589) B1710589
theorem B3657041 : Blo 1520457 3657041 := bstep (se 2 (by rfl) ⟨1371390, by rfl⟩ : syracuseStep 3657041 = 2742781) B2742781
theorem B5131619 : Blo 1520457 5131619 := bstep (se 1 (by rfl) ⟨3848714, by rfl⟩ : syracuseStep 5131619 = 7697429) B7697429
theorem B2280803 : Blo 1520457 2280803 := bstep (se 1 (by rfl) ⟨1710602, by rfl⟩ : syracuseStep 2280803 = 3421205) B3421205
theorem B2280833 : Blo 1520457 2280833 := bstep (se 2 (by rfl) ⟨855312, by rfl⟩ : syracuseStep 2280833 = 1710625) B1710625
theorem B8220037 : Blo 1520457 8220037 := bstep (se 4 (by rfl) ⟨770628, by rfl⟩ : syracuseStep 8220037 = 1541257) B1541257
theorem B2280851 : Blo 1520457 2280851 := bstep (se 1 (by rfl) ⟨1710638, by rfl⟩ : syracuseStep 2280851 = 3421277) B3421277
theorem B2567585 : Blo 1520457 2567585 := bstep (se 2 (by rfl) ⟨962844, by rfl⟩ : syracuseStep 2567585 = 1925689) B1925689
theorem B2280881 : Blo 1520457 2280881 := bstep (se 2 (by rfl) ⟨855330, by rfl⟩ : syracuseStep 2280881 = 1710661) B1710661
theorem B2280899 : Blo 1520457 2280899 := bstep (se 1 (by rfl) ⟨1710674, by rfl⟩ : syracuseStep 2280899 = 3421349) B3421349
theorem B2280929 : Blo 1520457 2280929 := bstep (se 2 (by rfl) ⟨855348, by rfl⟩ : syracuseStep 2280929 = 1710697) B1710697
theorem B2280947 : Blo 1520457 2280947 := bstep (se 1 (by rfl) ⟨1710710, by rfl⟩ : syracuseStep 2280947 = 3421421) B3421421
theorem B2280977 : Blo 1520457 2280977 := bstep (se 2 (by rfl) ⟨855366, by rfl⟩ : syracuseStep 2280977 = 1710733) B1710733
theorem B2567713 : Blo 1520457 2567713 := bstep (se 2 (by rfl) ⟨962892, by rfl⟩ : syracuseStep 2567713 = 1925785) B1925785
theorem B2280995 : Blo 1520457 2280995 := bstep (se 1 (by rfl) ⟨1710746, by rfl⟩ : syracuseStep 2280995 = 3421493) B3421493
theorem B2436643 : Blo 1520457 2436643 := bstep (se 1 (by rfl) ⟨1827482, by rfl⟩ : syracuseStep 2436643 = 3654965) B3654965
theorem B2281025 : Blo 1520457 2281025 := bstep (se 2 (by rfl) ⟨855384, by rfl⟩ : syracuseStep 2281025 = 1710769) B1710769
theorem B2887235 : Blo 1520457 2887235 := bstep (se 1 (by rfl) ⟨2165426, by rfl⟩ : syracuseStep 2887235 = 4330853) B4330853
theorem B2567747 : Blo 1520457 2567747 := bstep (se 1 (by rfl) ⟨1925810, by rfl⟩ : syracuseStep 2567747 = 3851621) B3851621
theorem B2281043 : Blo 1520457 2281043 := bstep (se 1 (by rfl) ⟨1710782, by rfl⟩ : syracuseStep 2281043 = 3421565) B3421565
theorem B2166355 : Blo 1520457 2166355 := bstep (se 1 (by rfl) ⟨1624766, by rfl⟩ : syracuseStep 2166355 = 3249533) B3249533
theorem B5131889 : Blo 1520457 5131889 := bstep (se 2 (by rfl) ⟨1924458, by rfl⟩ : syracuseStep 5131889 = 3848917) B3848917
theorem B2281073 : Blo 1520457 2281073 := bstep (se 2 (by rfl) ⟨855402, by rfl⟩ : syracuseStep 2281073 = 1710805) B1710805
theorem B70233713 : Blo 1520457 70233713 := bstep (se 2 (by rfl) ⟨26337642, by rfl⟩ : syracuseStep 70233713 = 52675285) B52675285
theorem B2281091 : Blo 1520457 2281091 := bstep (se 1 (by rfl) ⟨1710818, by rfl⟩ : syracuseStep 2281091 = 3421637) B3421637
theorem B2281121 : Blo 1520457 2281121 := bstep (se 2 (by rfl) ⟨855420, by rfl⟩ : syracuseStep 2281121 = 1710841) B1710841
theorem B2281139 : Blo 1520457 2281139 := bstep (se 1 (by rfl) ⟨1710854, by rfl⟩ : syracuseStep 2281139 = 3421709) B3421709
theorem B2567875 : Blo 1520457 2567875 := bstep (se 1 (by rfl) ⟨1925906, by rfl⟩ : syracuseStep 2567875 = 3851813) B3851813
theorem B2281169 : Blo 1520457 2281169 := bstep (se 2 (by rfl) ⟨855438, by rfl⟩ : syracuseStep 2281169 = 1710877) B1710877
theorem B2281187 : Blo 1520457 2281187 := bstep (se 1 (by rfl) ⟨1710890, by rfl⟩ : syracuseStep 2281187 = 3421781) B3421781
theorem B2281217 : Blo 1520457 2281217 := bstep (se 2 (by rfl) ⟨855456, by rfl⟩ : syracuseStep 2281217 = 1710913) B1710913
theorem B2281235 : Blo 1520457 2281235 := bstep (se 1 (by rfl) ⟨1710926, by rfl⟩ : syracuseStep 2281235 = 3421853) B3421853
theorem B2436899 : Blo 1520457 2436899 := bstep (se 1 (by rfl) ⟨1827674, by rfl⟩ : syracuseStep 2436899 = 3655349) B3655349
theorem B2281265 : Blo 1520457 2281265 := bstep (se 2 (by rfl) ⟨855474, by rfl⟩ : syracuseStep 2281265 = 1710949) B1710949
theorem B2281283 : Blo 1520457 2281283 := bstep (se 1 (by rfl) ⟨1710962, by rfl⟩ : syracuseStep 2281283 = 3421925) B3421925
theorem B2568017 : Blo 1520457 2568017 := bstep (se 2 (by rfl) ⟨963006, by rfl⟩ : syracuseStep 2568017 = 1926013) B1926013
theorem B2281313 : Blo 1520457 2281313 := bstep (se 2 (by rfl) ⟨855492, by rfl⟩ : syracuseStep 2281313 = 1710985) B1710985
theorem B6500209 : Blo 1520457 6500209 := bstep (se 2 (by rfl) ⟨2437578, by rfl⟩ : syracuseStep 6500209 = 4875157) B4875157
theorem B2281331 : Blo 1520457 2281331 := bstep (se 1 (by rfl) ⟨1710998, by rfl⟩ : syracuseStep 2281331 = 3421997) B3421997
theorem B19509133 : Blo 1520457 19509133 := bstep (se 3 (by rfl) ⟨3657962, by rfl⟩ : syracuseStep 19509133 = 7315925) B7315925
theorem B2281361 : Blo 1520457 2281361 := bstep (se 2 (by rfl) ⟨855510, by rfl⟩ : syracuseStep 2281361 = 1711021) B1711021
theorem B2281379 : Blo 1520457 2281379 := bstep (se 1 (by rfl) ⟨1711034, by rfl⟩ : syracuseStep 2281379 = 3422069) B3422069
theorem B2166691 : Blo 1520457 2166691 := bstep (se 1 (by rfl) ⟨1625018, by rfl⟩ : syracuseStep 2166691 = 3250037) B3250037
theorem B2281409 : Blo 1520457 2281409 := bstep (se 2 (by rfl) ⟨855528, by rfl⟩ : syracuseStep 2281409 = 1711057) B1711057
theorem B2568145 : Blo 1520457 2568145 := bstep (se 2 (by rfl) ⟨963054, by rfl⟩ : syracuseStep 2568145 = 1926109) B1926109
theorem B2281427 : Blo 1520457 2281427 := bstep (se 1 (by rfl) ⟨1711070, by rfl⟩ : syracuseStep 2281427 = 3422141) B3422141
theorem B2281457 : Blo 1520457 2281457 := bstep (se 2 (by rfl) ⟨855546, by rfl⟩ : syracuseStep 2281457 = 1711093) B1711093
theorem B8335345 : Blo 1520457 8335345 := bstep (se 2 (by rfl) ⟨3125754, by rfl⟩ : syracuseStep 8335345 = 6251509) B6251509
theorem B2568179 : Blo 1520457 2568179 := bstep (se 1 (by rfl) ⟨1926134, by rfl⟩ : syracuseStep 2568179 = 3852269) B3852269
theorem B2281475 : Blo 1520457 2281475 := bstep (se 1 (by rfl) ⟨1711106, by rfl⟩ : syracuseStep 2281475 = 3422213) B3422213
theorem B2281505 : Blo 1520457 2281505 := bstep (se 2 (by rfl) ⟨855564, by rfl⟩ : syracuseStep 2281505 = 1711129) B1711129
theorem B2281523 : Blo 1520457 2281523 := bstep (se 1 (by rfl) ⟨1711142, by rfl⟩ : syracuseStep 2281523 = 3422285) B3422285
theorem B2281553 : Blo 1520457 2281553 := bstep (se 2 (by rfl) ⟨855582, by rfl⟩ : syracuseStep 2281553 = 1711165) B1711165
theorem B3657809 : Blo 1520457 3657809 := bstep (se 2 (by rfl) ⟨1371678, by rfl⟩ : syracuseStep 3657809 = 2743357) B2743357
theorem B2281571 : Blo 1520457 2281571 := bstep (se 1 (by rfl) ⟨1711178, by rfl⟩ : syracuseStep 2281571 = 3422357) B3422357
theorem B2568307 : Blo 1520457 2568307 := bstep (se 1 (by rfl) ⟨1926230, by rfl⟩ : syracuseStep 2568307 = 3852461) B3852461
theorem B2281601 : Blo 1520457 2281601 := bstep (se 2 (by rfl) ⟨855600, by rfl⟩ : syracuseStep 2281601 = 1711201) B1711201
theorem B5132429 : Blo 1520457 5132429 := bstep (se 3 (by rfl) ⟨962330, by rfl⟩ : syracuseStep 5132429 = 1924661) B1924661
theorem B2281619 : Blo 1520457 2281619 := bstep (se 1 (by rfl) ⟨1711214, by rfl⟩ : syracuseStep 2281619 = 3422429) B3422429
theorem B8335523 : Blo 1520457 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B5779619 : Blo 1520457 5779619 := bstep (se 1 (by rfl) ⟨4334714, by rfl⟩ : syracuseStep 5779619 = 8669429) B8669429
theorem B2281649 : Blo 1520457 2281649 := bstep (se 2 (by rfl) ⟨855618, by rfl⟩ : syracuseStep 2281649 = 1711237) B1711237
theorem B5558449 : Blo 1520457 5558449 := bstep (se 2 (by rfl) ⟨2084418, by rfl⟩ : syracuseStep 5558449 = 4168837) B4168837
theorem B5779633 : Blo 1520457 5779633 := bstep (se 2 (by rfl) ⟨2167362, by rfl⟩ : syracuseStep 5779633 = 4334725) B4334725
theorem B5132483 : Blo 1520457 5132483 := bstep (se 1 (by rfl) ⟨3849362, by rfl⟩ : syracuseStep 5132483 = 7698725) B7698725
theorem B2281667 : Blo 1520457 2281667 := bstep (se 1 (by rfl) ⟨1711250, by rfl⟩ : syracuseStep 2281667 = 3422501) B3422501
theorem B2281697 : Blo 1520457 2281697 := bstep (se 2 (by rfl) ⟨855636, by rfl⟩ : syracuseStep 2281697 = 1711273) B1711273
theorem B3657955 : Blo 1520457 3657955 := bstep (se 1 (by rfl) ⟨2743466, by rfl⟩ : syracuseStep 3657955 = 5486933) B5486933
theorem B2437361 : Blo 1520457 2437361 := bstep (se 2 (by rfl) ⟨914010, by rfl⟩ : syracuseStep 2437361 = 1828021) B1828021
theorem B2281715 : Blo 1520457 2281715 := bstep (se 1 (by rfl) ⟨1711286, by rfl⟩ : syracuseStep 2281715 = 3422573) B3422573
theorem B2568449 : Blo 1520457 2568449 := bstep (se 2 (by rfl) ⟨963168, by rfl⟩ : syracuseStep 2568449 = 1926337) B1926337
theorem B2281745 : Blo 1520457 2281745 := bstep (se 2 (by rfl) ⟨855654, by rfl⟩ : syracuseStep 2281745 = 1711309) B1711309
theorem B2281763 : Blo 1520457 2281763 := bstep (se 1 (by rfl) ⟨1711322, by rfl⟩ : syracuseStep 2281763 = 3422645) B3422645
theorem B8663345 : Blo 1520457 8663345 := bstep (se 2 (by rfl) ⟨3248754, by rfl⟩ : syracuseStep 8663345 = 6497509) B6497509
theorem B7704881 : Blo 1520457 7704881 := bstep (se 2 (by rfl) ⟨2889330, by rfl⟩ : syracuseStep 7704881 = 5778661) B5778661
theorem B2281793 : Blo 1520457 2281793 := bstep (se 2 (by rfl) ⟨855672, by rfl⟩ : syracuseStep 2281793 = 1711345) B1711345
theorem B2601283 : Blo 1520457 2601283 := bstep (se 1 (by rfl) ⟨1950962, by rfl⟩ : syracuseStep 2601283 = 3901925) B3901925
theorem B2740547 : Blo 1520457 2740547 := bstep (se 1 (by rfl) ⟨2055410, by rfl⟩ : syracuseStep 2740547 = 4110821) B4110821
theorem B2437457 : Blo 1520457 2437457 := bstep (se 2 (by rfl) ⟨914046, by rfl⟩ : syracuseStep 2437457 = 1828093) B1828093
theorem B2281811 : Blo 1520457 2281811 := bstep (se 1 (by rfl) ⟨1711358, by rfl⟩ : syracuseStep 2281811 = 3422717) B3422717
theorem B2281841 : Blo 1520457 2281841 := bstep (se 2 (by rfl) ⟨855690, by rfl⟩ : syracuseStep 2281841 = 1711381) B1711381
theorem B2437489 : Blo 1520457 2437489 := bstep (se 2 (by rfl) ⟨914058, by rfl⟩ : syracuseStep 2437489 = 1828117) B1828117
theorem B2568577 : Blo 1520457 2568577 := bstep (se 2 (by rfl) ⟨963216, by rfl⟩ : syracuseStep 2568577 = 1926433) B1926433
theorem B3248515 : Blo 1520457 3248515 := bstep (se 1 (by rfl) ⟨2436386, by rfl⟩ : syracuseStep 3248515 = 4872773) B4872773
theorem B2281859 : Blo 1520457 2281859 := bstep (se 1 (by rfl) ⟨1711394, by rfl⟩ : syracuseStep 2281859 = 3422789) B3422789
theorem B18510221 : Blo 1520457 18510221 := bstep (se 3 (by rfl) ⟨3470666, by rfl⟩ : syracuseStep 18510221 = 6941333) B6941333
theorem B2281889 : Blo 1520457 2281889 := bstep (se 2 (by rfl) ⟨855708, by rfl⟩ : syracuseStep 2281889 = 1711417) B1711417
theorem B2568611 : Blo 1520457 2568611 := bstep (se 1 (by rfl) ⟨1926458, by rfl⟩ : syracuseStep 2568611 = 3852917) B3852917
theorem B2281907 : Blo 1520457 2281907 := bstep (se 1 (by rfl) ⟨1711430, by rfl⟩ : syracuseStep 2281907 = 3422861) B3422861
theorem B2888131 : Blo 1520457 2888131 := bstep (se 1 (by rfl) ⟨2166098, by rfl⟩ : syracuseStep 2888131 = 4332197) B4332197
theorem B5132753 : Blo 1520457 5132753 := bstep (se 2 (by rfl) ⟨1924782, by rfl⟩ : syracuseStep 5132753 = 3849565) B3849565
theorem B2281937 : Blo 1520457 2281937 := bstep (se 2 (by rfl) ⟨855726, by rfl⟩ : syracuseStep 2281937 = 1711453) B1711453
theorem B2167249 : Blo 1520457 2167249 := bstep (se 2 (by rfl) ⟨812718, by rfl⟩ : syracuseStep 2167249 = 1625437) B1625437
theorem B4624867 : Blo 1520457 4624867 := bstep (se 1 (by rfl) ⟨3468650, by rfl⟩ : syracuseStep 4624867 = 6937301) B6937301
theorem B2281955 : Blo 1520457 2281955 := bstep (se 1 (by rfl) ⟨1711466, by rfl⟩ : syracuseStep 2281955 = 3422933) B3422933
theorem B2167283 : Blo 1520457 2167283 := bstep (se 1 (by rfl) ⟨1625462, by rfl⟩ : syracuseStep 2167283 = 3250925) B3250925
theorem B2281985 : Blo 1520457 2281985 := bstep (se 2 (by rfl) ⟨855744, by rfl⟩ : syracuseStep 2281985 = 1711489) B1711489
theorem B2282003 : Blo 1520457 2282003 := bstep (se 1 (by rfl) ⟨1711502, by rfl⟩ : syracuseStep 2282003 = 3423005) B3423005
theorem B2568739 : Blo 1520457 2568739 := bstep (se 1 (by rfl) ⟨1926554, by rfl⟩ : syracuseStep 2568739 = 3853109) B3853109
theorem B2282033 : Blo 1520457 2282033 := bstep (se 2 (by rfl) ⟨855762, by rfl⟩ : syracuseStep 2282033 = 1711525) B1711525
theorem B2282051 : Blo 1520457 2282051 := bstep (se 1 (by rfl) ⟨1711538, by rfl⟩ : syracuseStep 2282051 = 3423077) B3423077
theorem B2282081 : Blo 1520457 2282081 := bstep (se 2 (by rfl) ⟨855780, by rfl⟩ : syracuseStep 2282081 = 1711561) B1711561
theorem B2740835 : Blo 1520457 2740835 := bstep (se 1 (by rfl) ⟨2055626, by rfl⟩ : syracuseStep 2740835 = 4111253) B4111253
theorem B2888291 : Blo 1520457 2888291 := bstep (se 1 (by rfl) ⟨2166218, by rfl⟩ : syracuseStep 2888291 = 4332437) B4332437
theorem B2282099 : Blo 1520457 2282099 := bstep (se 1 (by rfl) ⟨1711574, by rfl⟩ : syracuseStep 2282099 = 3423149) B3423149
theorem B2282129 : Blo 1520457 2282129 := bstep (se 2 (by rfl) ⟨855798, by rfl⟩ : syracuseStep 2282129 = 1711597) B1711597
theorem B2282147 : Blo 1520457 2282147 := bstep (se 1 (by rfl) ⟨1711610, by rfl⟩ : syracuseStep 2282147 = 3423221) B3423221
theorem B2568881 : Blo 1520457 2568881 := bstep (se 2 (by rfl) ⟨963330, by rfl⟩ : syracuseStep 2568881 = 1926661) B1926661
theorem B2282177 : Blo 1520457 2282177 := bstep (se 2 (by rfl) ⟨855816, by rfl⟩ : syracuseStep 2282177 = 1711633) B1711633
theorem B3248849 : Blo 1520457 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B2282195 : Blo 1520457 2282195 := bstep (se 1 (by rfl) ⟨1711646, by rfl⟩ : syracuseStep 2282195 = 3423293) B3423293
theorem B2282225 : Blo 1520457 2282225 := bstep (se 2 (by rfl) ⟨855834, by rfl⟩ : syracuseStep 2282225 = 1711669) B1711669
theorem B2282243 : Blo 1520457 2282243 := bstep (se 1 (by rfl) ⟨1711682, by rfl⟩ : syracuseStep 2282243 = 3423365) B3423365
theorem B2282273 : Blo 1520457 2282273 := bstep (se 2 (by rfl) ⟨855852, by rfl⟩ : syracuseStep 2282273 = 1711705) B1711705
theorem B3470129 : Blo 1520457 3470129 := bstep (se 2 (by rfl) ⟨1301298, by rfl⟩ : syracuseStep 3470129 = 2602597) B2602597
theorem B2569009 : Blo 1520457 2569009 := bstep (se 2 (by rfl) ⟨963378, by rfl⟩ : syracuseStep 2569009 = 1926757) B1926757
theorem B2282291 : Blo 1520457 2282291 := bstep (se 1 (by rfl) ⟨1711718, by rfl⟩ : syracuseStep 2282291 = 3423437) B3423437
theorem B2282321 : Blo 1520457 2282321 := bstep (se 2 (by rfl) ⟨855870, by rfl⟩ : syracuseStep 2282321 = 1711741) B1711741
theorem B1520467 : Blo 1520457 1520467 := bstep (se 1 (by rfl) ⟨1140350, by rfl⟩ : syracuseStep 1520467 = 2280701) B2280701
theorem B2569043 : Blo 1520457 2569043 := bstep (se 1 (by rfl) ⟨1926782, by rfl⟩ : syracuseStep 2569043 = 3853565) B3853565
theorem B1520483 : Blo 1520457 1520483 := bstep (se 1 (by rfl) ⟨1140362, by rfl⟩ : syracuseStep 1520483 = 2280725) B2280725
theorem B2282339 : Blo 1520457 2282339 := bstep (se 1 (by rfl) ⟨1711754, by rfl⟩ : syracuseStep 2282339 = 3423509) B3423509
theorem B37106545 : Blo 1520457 37106545 := bstep (se 2 (by rfl) ⟨13914954, by rfl⟩ : syracuseStep 37106545 = 27829909) B27829909
theorem B1520499 : Blo 1520457 1520499 := bstep (se 1 (by rfl) ⟨1140374, by rfl⟩ : syracuseStep 1520499 = 2280749) B2280749
theorem B2282369 : Blo 1520457 2282369 := bstep (se 2 (by rfl) ⟨855888, by rfl⟩ : syracuseStep 2282369 = 1711777) B1711777
theorem B1520515 : Blo 1520457 1520515 := bstep (se 1 (by rfl) ⟨1140386, by rfl⟩ : syracuseStep 1520515 = 2280773) B2280773
theorem B1520531 : Blo 1520457 1520531 := bstep (se 1 (by rfl) ⟨1140398, by rfl⟩ : syracuseStep 1520531 = 2280797) B2280797
theorem B2282387 : Blo 1520457 2282387 := bstep (se 1 (by rfl) ⟨1711790, by rfl⟩ : syracuseStep 2282387 = 3423581) B3423581
theorem B1520547 : Blo 1520457 1520547 := bstep (se 1 (by rfl) ⟨1140410, by rfl⟩ : syracuseStep 1520547 = 2280821) B2280821
theorem B5485475 : Blo 1520457 5485475 := bstep (se 1 (by rfl) ⟨4114106, by rfl⟩ : syracuseStep 5485475 = 8228213) B8228213
theorem B2282417 : Blo 1520457 2282417 := bstep (se 2 (by rfl) ⟨855906, by rfl⟩ : syracuseStep 2282417 = 1711813) B1711813
theorem B1520563 : Blo 1520457 1520563 := bstep (se 1 (by rfl) ⟨1140422, by rfl⟩ : syracuseStep 1520563 = 2280845) B2280845
theorem B1520579 : Blo 1520457 1520579 := bstep (se 1 (by rfl) ⟨1140434, by rfl⟩ : syracuseStep 1520579 = 2280869) B2280869
theorem B2282435 : Blo 1520457 2282435 := bstep (se 1 (by rfl) ⟨1711826, by rfl⟩ : syracuseStep 2282435 = 3423653) B3423653
theorem B1520595 : Blo 1520457 1520595 := bstep (se 1 (by rfl) ⟨1140446, by rfl⟩ : syracuseStep 1520595 = 2280893) B2280893
theorem B2282465 : Blo 1520457 2282465 := bstep (se 2 (by rfl) ⟨855924, by rfl⟩ : syracuseStep 2282465 = 1711849) B1711849
theorem B1520611 : Blo 1520457 1520611 := bstep (se 1 (by rfl) ⟨1140458, by rfl⟩ : syracuseStep 1520611 = 2280917) B2280917
theorem B5133293 : Blo 1520457 5133293 := bstep (se 3 (by rfl) ⟨962492, by rfl⟩ : syracuseStep 5133293 = 1924985) B1924985
theorem B3421169 : Blo 1520457 3421169 := bstep (se 2 (by rfl) ⟨1282938, by rfl⟩ : syracuseStep 3421169 = 2565877) B2565877
theorem B9745393 : Blo 1520457 9745393 := bstep (se 2 (by rfl) ⟨3654522, by rfl⟩ : syracuseStep 9745393 = 7309045) B7309045
theorem B1520627 : Blo 1520457 1520627 := bstep (se 1 (by rfl) ⟨1140470, by rfl⟩ : syracuseStep 1520627 = 2280941) B2280941
theorem B2282483 : Blo 1520457 2282483 := bstep (se 1 (by rfl) ⟨1711862, by rfl⟩ : syracuseStep 2282483 = 3423725) B3423725
theorem B3421187 : Blo 1520457 3421187 := bstep (se 1 (by rfl) ⟨2565890, by rfl⟩ : syracuseStep 3421187 = 5131781) B5131781
theorem B1520643 : Blo 1520457 1520643 := bstep (se 1 (by rfl) ⟨1140482, by rfl⟩ : syracuseStep 1520643 = 2280965) B2280965
theorem B2282513 : Blo 1520457 2282513 := bstep (se 2 (by rfl) ⟨855942, by rfl⟩ : syracuseStep 2282513 = 1711885) B1711885
theorem B1520659 : Blo 1520457 1520659 := bstep (se 1 (by rfl) ⟨1140494, by rfl⟩ : syracuseStep 1520659 = 2280989) B2280989
theorem B1520675 : Blo 1520457 1520675 := bstep (se 1 (by rfl) ⟨1140506, by rfl⟩ : syracuseStep 1520675 = 2281013) B2281013
theorem B5133347 : Blo 1520457 5133347 := bstep (se 1 (by rfl) ⟨3850010, by rfl⟩ : syracuseStep 5133347 = 7700021) B7700021
theorem B2282531 : Blo 1520457 2282531 := bstep (se 1 (by rfl) ⟨1711898, by rfl⟩ : syracuseStep 2282531 = 3423797) B3423797
theorem B1520691 : Blo 1520457 1520691 := bstep (se 1 (by rfl) ⟨1140518, by rfl⟩ : syracuseStep 1520691 = 2281037) B2281037
theorem B2602049 : Blo 1520457 2602049 := bstep (se 2 (by rfl) ⟨975768, by rfl⟩ : syracuseStep 2602049 = 1951537) B1951537
theorem B2282561 : Blo 1520457 2282561 := bstep (se 2 (by rfl) ⟨855960, by rfl⟩ : syracuseStep 2282561 = 1711921) B1711921
theorem B1520707 : Blo 1520457 1520707 := bstep (se 1 (by rfl) ⟨1140530, by rfl⟩ : syracuseStep 1520707 = 2281061) B2281061
theorem B1520723 : Blo 1520457 1520723 := bstep (se 1 (by rfl) ⟨1140542, by rfl⟩ : syracuseStep 1520723 = 2281085) B2281085
theorem B2282579 : Blo 1520457 2282579 := bstep (se 1 (by rfl) ⟨1711934, by rfl⟩ : syracuseStep 2282579 = 3423869) B3423869
theorem B1520739 : Blo 1520457 1520739 := bstep (se 1 (by rfl) ⟨1140554, by rfl⟩ : syracuseStep 1520739 = 2281109) B2281109
theorem B2282609 : Blo 1520457 2282609 := bstep (se 2 (by rfl) ⟨855978, by rfl⟩ : syracuseStep 2282609 = 1711957) B1711957
theorem B1520755 : Blo 1520457 1520755 := bstep (se 1 (by rfl) ⟨1140566, by rfl⟩ : syracuseStep 1520755 = 2281133) B2281133
theorem B1520771 : Blo 1520457 1520771 := bstep (se 1 (by rfl) ⟨1140578, by rfl⟩ : syracuseStep 1520771 = 2281157) B2281157
theorem B2282627 : Blo 1520457 2282627 := bstep (se 1 (by rfl) ⟨1711970, by rfl⟩ : syracuseStep 2282627 = 3423941) B3423941
theorem B1520787 : Blo 1520457 1520787 := bstep (se 1 (by rfl) ⟨1140590, by rfl⟩ : syracuseStep 1520787 = 2281181) B2281181
theorem B2282657 : Blo 1520457 2282657 := bstep (se 2 (by rfl) ⟨855996, by rfl⟩ : syracuseStep 2282657 = 1711993) B1711993
theorem B1520803 : Blo 1520457 1520803 := bstep (se 1 (by rfl) ⟨1140602, by rfl⟩ : syracuseStep 1520803 = 2281205) B2281205
theorem B1520819 : Blo 1520457 1520819 := bstep (se 1 (by rfl) ⟨1140614, by rfl⟩ : syracuseStep 1520819 = 2281229) B2281229
theorem B2282675 : Blo 1520457 2282675 := bstep (se 1 (by rfl) ⟨1712006, by rfl⟩ : syracuseStep 2282675 = 3424013) B3424013
theorem B1520835 : Blo 1520457 1520835 := bstep (se 1 (by rfl) ⟨1140626, by rfl⟩ : syracuseStep 1520835 = 2281253) B2281253
theorem B11547845 : Blo 1520457 11547845 := bstep (se 4 (by rfl) ⟨1082610, by rfl⟩ : syracuseStep 11547845 = 2165221) B2165221
theorem B4330705 : Blo 1520457 4330705 := bstep (se 2 (by rfl) ⟨1624014, by rfl⟩ : syracuseStep 4330705 = 3248029) B3248029
theorem B2282705 : Blo 1520457 2282705 := bstep (se 2 (by rfl) ⟨856014, by rfl⟩ : syracuseStep 2282705 = 1712029) B1712029
theorem B1520851 : Blo 1520457 1520851 := bstep (se 1 (by rfl) ⟨1140638, by rfl⟩ : syracuseStep 1520851 = 2281277) B2281277
theorem B1520867 : Blo 1520457 1520867 := bstep (se 1 (by rfl) ⟨1140650, by rfl⟩ : syracuseStep 1520867 = 2281301) B2281301
theorem B2282723 : Blo 1520457 2282723 := bstep (se 1 (by rfl) ⟨1712042, by rfl⟩ : syracuseStep 2282723 = 3424085) B3424085
theorem B1520883 : Blo 1520457 1520883 := bstep (se 1 (by rfl) ⟨1140662, by rfl⟩ : syracuseStep 1520883 = 2281325) B2281325
theorem B2282753 : Blo 1520457 2282753 := bstep (se 2 (by rfl) ⟨856032, by rfl⟩ : syracuseStep 2282753 = 1712065) B1712065
theorem B1520899 : Blo 1520457 1520899 := bstep (se 1 (by rfl) ⟨1140674, by rfl⟩ : syracuseStep 1520899 = 2281349) B2281349
theorem B4871441 : Blo 1520457 4871441 := bstep (se 2 (by rfl) ⟨1826790, by rfl⟩ : syracuseStep 4871441 = 3653581) B3653581
theorem B3421457 : Blo 1520457 3421457 := bstep (se 2 (by rfl) ⟨1283046, by rfl⟩ : syracuseStep 3421457 = 2566093) B2566093
theorem B1520915 : Blo 1520457 1520915 := bstep (se 1 (by rfl) ⟨1140686, by rfl⟩ : syracuseStep 1520915 = 2281373) B2281373
theorem B2282771 : Blo 1520457 2282771 := bstep (se 1 (by rfl) ⟨1712078, by rfl⟩ : syracuseStep 2282771 = 3424157) B3424157
theorem B3421475 : Blo 1520457 3421475 := bstep (se 1 (by rfl) ⟨2566106, by rfl⟩ : syracuseStep 3421475 = 5132213) B5132213
theorem B1520931 : Blo 1520457 1520931 := bstep (se 1 (by rfl) ⟨1140698, by rfl⟩ : syracuseStep 1520931 = 2281397) B2281397
theorem B5559587 : Blo 1520457 5559587 := bstep (se 1 (by rfl) ⟨4169690, by rfl⟩ : syracuseStep 5559587 = 8339381) B8339381
theorem B5133617 : Blo 1520457 5133617 := bstep (se 2 (by rfl) ⟨1925106, by rfl⟩ : syracuseStep 5133617 = 3850213) B3850213
theorem B2282801 : Blo 1520457 2282801 := bstep (se 2 (by rfl) ⟨856050, by rfl⟩ : syracuseStep 2282801 = 1712101) B1712101
theorem B1520947 : Blo 1520457 1520947 := bstep (se 1 (by rfl) ⟨1140710, by rfl⟩ : syracuseStep 1520947 = 2281421) B2281421
theorem B1520963 : Blo 1520457 1520963 := bstep (se 1 (by rfl) ⟨1140722, by rfl⟩ : syracuseStep 1520963 = 2281445) B2281445
theorem B2282819 : Blo 1520457 2282819 := bstep (se 1 (by rfl) ⟨1712114, by rfl⟩ : syracuseStep 2282819 = 3424229) B3424229
theorem B1520979 : Blo 1520457 1520979 := bstep (se 1 (by rfl) ⟨1140734, by rfl⟩ : syracuseStep 1520979 = 2281469) B2281469
theorem B2282849 : Blo 1520457 2282849 := bstep (se 2 (by rfl) ⟨856068, by rfl⟩ : syracuseStep 2282849 = 1712137) B1712137
theorem B7804259 : Blo 1520457 7804259 := bstep (se 1 (by rfl) ⟨5853194, by rfl⟩ : syracuseStep 7804259 = 11706389) B11706389
theorem B1520995 : Blo 1520457 1520995 := bstep (se 1 (by rfl) ⟨1140746, by rfl⟩ : syracuseStep 1520995 = 2281493) B2281493
theorem B1521011 : Blo 1520457 1521011 := bstep (se 1 (by rfl) ⟨1140758, by rfl⟩ : syracuseStep 1521011 = 2281517) B2281517
theorem B2282867 : Blo 1520457 2282867 := bstep (se 1 (by rfl) ⟨1712150, by rfl⟩ : syracuseStep 2282867 = 3424301) B3424301
theorem B1521027 : Blo 1520457 1521027 := bstep (se 1 (by rfl) ⟨1140770, by rfl⟩ : syracuseStep 1521027 = 2281541) B2281541
theorem B2282897 : Blo 1520457 2282897 := bstep (se 2 (by rfl) ⟨856086, by rfl⟩ : syracuseStep 2282897 = 1712173) B1712173
theorem B1521043 : Blo 1520457 1521043 := bstep (se 1 (by rfl) ⟨1140782, by rfl⟩ : syracuseStep 1521043 = 2281565) B2281565
theorem B1521059 : Blo 1520457 1521059 := bstep (se 1 (by rfl) ⟨1140794, by rfl⟩ : syracuseStep 1521059 = 2281589) B2281589
theorem B2282915 : Blo 1520457 2282915 := bstep (se 1 (by rfl) ⟨1712186, by rfl⟩ : syracuseStep 2282915 = 3424373) B3424373
theorem B1521075 : Blo 1520457 1521075 := bstep (se 1 (by rfl) ⟨1140806, by rfl⟩ : syracuseStep 1521075 = 2281613) B2281613
theorem B2282945 : Blo 1520457 2282945 := bstep (se 2 (by rfl) ⟨856104, by rfl⟩ : syracuseStep 2282945 = 1712209) B1712209
theorem B1521091 : Blo 1520457 1521091 := bstep (se 1 (by rfl) ⟨1140818, by rfl⟩ : syracuseStep 1521091 = 2281637) B2281637
theorem B1521107 : Blo 1520457 1521107 := bstep (se 1 (by rfl) ⟨1140830, by rfl⟩ : syracuseStep 1521107 = 2281661) B2281661
theorem B2282963 : Blo 1520457 2282963 := bstep (se 1 (by rfl) ⟨1712222, by rfl⟩ : syracuseStep 2282963 = 3424445) B3424445
theorem B4330979 : Blo 1520457 4330979 := bstep (se 1 (by rfl) ⟨3248234, by rfl⟩ : syracuseStep 4330979 = 6496469) B6496469
theorem B1521123 : Blo 1520457 1521123 := bstep (se 1 (by rfl) ⟨1140842, by rfl⟩ : syracuseStep 1521123 = 2281685) B2281685
theorem B19494371 : Blo 1520457 19494371 := bstep (se 1 (by rfl) ⟨14620778, by rfl⟩ : syracuseStep 19494371 = 29241557) B29241557
theorem B2282993 : Blo 1520457 2282993 := bstep (se 2 (by rfl) ⟨856122, by rfl⟩ : syracuseStep 2282993 = 1712245) B1712245
theorem B1521139 : Blo 1520457 1521139 := bstep (se 1 (by rfl) ⟨1140854, by rfl⟩ : syracuseStep 1521139 = 2281709) B2281709
theorem B1521155 : Blo 1520457 1521155 := bstep (se 1 (by rfl) ⟨1140866, by rfl⟩ : syracuseStep 1521155 = 2281733) B2281733
theorem B2283011 : Blo 1520457 2283011 := bstep (se 1 (by rfl) ⟨1712258, by rfl⟩ : syracuseStep 2283011 = 3424517) B3424517
theorem B1521171 : Blo 1520457 1521171 := bstep (se 1 (by rfl) ⟨1140878, by rfl⟩ : syracuseStep 1521171 = 2281757) B2281757
theorem B2283041 : Blo 1520457 2283041 := bstep (se 2 (by rfl) ⟨856140, by rfl⟩ : syracuseStep 2283041 = 1712281) B1712281
theorem B1734179 : Blo 1520457 1734179 := bstep (se 1 (by rfl) ⟨1300634, by rfl⟩ : syracuseStep 1734179 = 2601269) B2601269
theorem B1521187 : Blo 1520457 1521187 := bstep (se 1 (by rfl) ⟨1140890, by rfl⟩ : syracuseStep 1521187 = 2281781) B2281781
theorem B10556963 : Blo 1520457 10556963 := bstep (se 1 (by rfl) ⟨7917722, by rfl⟩ : syracuseStep 10556963 = 15835445) B15835445
theorem B3421745 : Blo 1520457 3421745 := bstep (se 2 (by rfl) ⟨1283154, by rfl⟩ : syracuseStep 3421745 = 2566309) B2566309
theorem B1521203 : Blo 1520457 1521203 := bstep (se 1 (by rfl) ⟨1140902, by rfl⟩ : syracuseStep 1521203 = 2281805) B2281805
theorem B2283059 : Blo 1520457 2283059 := bstep (se 1 (by rfl) ⟨1712294, by rfl⟩ : syracuseStep 2283059 = 3424589) B3424589
theorem B3421763 : Blo 1520457 3421763 := bstep (se 1 (by rfl) ⟨2566322, by rfl⟩ : syracuseStep 3421763 = 5132645) B5132645
theorem B1521219 : Blo 1520457 1521219 := bstep (se 1 (by rfl) ⟨1140914, by rfl⟩ : syracuseStep 1521219 = 2281829) B2281829
theorem B2283089 : Blo 1520457 2283089 := bstep (se 2 (by rfl) ⟨856158, by rfl⟩ : syracuseStep 2283089 = 1712317) B1712317
theorem B1521235 : Blo 1520457 1521235 := bstep (se 1 (by rfl) ⟨1140926, by rfl⟩ : syracuseStep 1521235 = 2281853) B2281853
theorem B1521251 : Blo 1520457 1521251 := bstep (se 1 (by rfl) ⟨1140938, by rfl⟩ : syracuseStep 1521251 = 2281877) B2281877
theorem B2283107 : Blo 1520457 2283107 := bstep (se 1 (by rfl) ⟨1712330, by rfl⟩ : syracuseStep 2283107 = 3424661) B3424661
theorem B1521267 : Blo 1520457 1521267 := bstep (se 1 (by rfl) ⟨1140950, by rfl⟩ : syracuseStep 1521267 = 2281901) B2281901
theorem B2283137 : Blo 1520457 2283137 := bstep (se 2 (by rfl) ⟨856176, by rfl⟩ : syracuseStep 2283137 = 1712353) B1712353
theorem B1521283 : Blo 1520457 1521283 := bstep (se 1 (by rfl) ⟨1140962, by rfl⟩ : syracuseStep 1521283 = 2281925) B2281925
theorem B2889361 : Blo 1520457 2889361 := bstep (se 2 (by rfl) ⟨1083510, by rfl⟩ : syracuseStep 2889361 = 2167021) B2167021
theorem B1521299 : Blo 1520457 1521299 := bstep (se 1 (by rfl) ⟨1140974, by rfl⟩ : syracuseStep 1521299 = 2281949) B2281949
theorem B2283155 : Blo 1520457 2283155 := bstep (se 1 (by rfl) ⟨1712366, by rfl⟩ : syracuseStep 2283155 = 3424733) B3424733
theorem B4331171 : Blo 1520457 4331171 := bstep (se 1 (by rfl) ⟨3248378, by rfl⟩ : syracuseStep 4331171 = 6496757) B6496757
theorem B1521315 : Blo 1520457 1521315 := bstep (se 1 (by rfl) ⟨1140986, by rfl⟩ : syracuseStep 1521315 = 2281973) B2281973
theorem B2283185 : Blo 1520457 2283185 := bstep (se 2 (by rfl) ⟨856194, by rfl⟩ : syracuseStep 2283185 = 1712389) B1712389
theorem B1521331 : Blo 1520457 1521331 := bstep (se 1 (by rfl) ⟨1140998, by rfl⟩ : syracuseStep 1521331 = 2281997) B2281997
theorem B1521347 : Blo 1520457 1521347 := bstep (se 1 (by rfl) ⟨1141010, by rfl⟩ : syracuseStep 1521347 = 2282021) B2282021
theorem B2283203 : Blo 1520457 2283203 := bstep (se 1 (by rfl) ⟨1712402, by rfl⟩ : syracuseStep 2283203 = 3424805) B3424805
theorem B1521363 : Blo 1520457 1521363 := bstep (se 1 (by rfl) ⟨1141022, by rfl⟩ : syracuseStep 1521363 = 2282045) B2282045
theorem B2283233 : Blo 1520457 2283233 := bstep (se 2 (by rfl) ⟨856212, by rfl⟩ : syracuseStep 2283233 = 1712425) B1712425
theorem B1521379 : Blo 1520457 1521379 := bstep (se 1 (by rfl) ⟨1141034, by rfl⟩ : syracuseStep 1521379 = 2282069) B2282069
theorem B8664803 : Blo 1520457 8664803 := bstep (se 1 (by rfl) ⟨6498602, by rfl⟩ : syracuseStep 8664803 = 12997205) B12997205
theorem B7706339 : Blo 1520457 7706339 := bstep (se 1 (by rfl) ⟨5779754, by rfl⟩ : syracuseStep 7706339 = 11559509) B11559509
theorem B11556593 : Blo 1520457 11556593 := bstep (se 2 (by rfl) ⟨4333722, by rfl⟩ : syracuseStep 11556593 = 8667445) B8667445
theorem B1521395 : Blo 1520457 1521395 := bstep (se 1 (by rfl) ⟨1141046, by rfl⟩ : syracuseStep 1521395 = 2282093) B2282093
theorem B2283251 : Blo 1520457 2283251 := bstep (se 1 (by rfl) ⟨1712438, by rfl⟩ : syracuseStep 2283251 = 3424877) B3424877
theorem B1521411 : Blo 1520457 1521411 := bstep (se 1 (by rfl) ⟨1141058, by rfl⟩ : syracuseStep 1521411 = 2282117) B2282117
theorem B6502157 : Blo 1520457 6502157 := bstep (se 3 (by rfl) ⟨1219154, by rfl⟩ : syracuseStep 6502157 = 2438309) B2438309
theorem B2283281 : Blo 1520457 2283281 := bstep (se 2 (by rfl) ⟨856230, by rfl⟩ : syracuseStep 2283281 = 1712461) B1712461
theorem B1521427 : Blo 1520457 1521427 := bstep (se 1 (by rfl) ⟨1141070, by rfl⟩ : syracuseStep 1521427 = 2282141) B2282141
theorem B1521443 : Blo 1520457 1521443 := bstep (se 1 (by rfl) ⟨1141082, by rfl⟩ : syracuseStep 1521443 = 2282165) B2282165
theorem B2283299 : Blo 1520457 2283299 := bstep (se 1 (by rfl) ⟨1712474, by rfl⟩ : syracuseStep 2283299 = 3424949) B3424949
theorem B1521459 : Blo 1520457 1521459 := bstep (se 1 (by rfl) ⟨1141094, by rfl⟩ : syracuseStep 1521459 = 2282189) B2282189
theorem B1521475 : Blo 1520457 1521475 := bstep (se 1 (by rfl) ⟨1141106, by rfl⟩ : syracuseStep 1521475 = 2282213) B2282213
theorem B2742083 : Blo 1520457 2742083 := bstep (se 1 (by rfl) ⟨2056562, by rfl⟩ : syracuseStep 2742083 = 4113125) B4113125
theorem B2283329 : Blo 1520457 2283329 := bstep (se 2 (by rfl) ⟨856248, by rfl⟩ : syracuseStep 2283329 = 1712497) B1712497
theorem B3086147 : Blo 1520457 3086147 := bstep (se 1 (by rfl) ⟨2314610, by rfl⟩ : syracuseStep 3086147 = 4629221) B4629221
theorem B5773133 : Blo 1520457 5773133 := bstep (se 3 (by rfl) ⟨1082462, by rfl⟩ : syracuseStep 5773133 = 2164925) B2164925
theorem B5134157 : Blo 1520457 5134157 := bstep (se 3 (by rfl) ⟨962654, by rfl⟩ : syracuseStep 5134157 = 1925309) B1925309
theorem B3422033 : Blo 1520457 3422033 := bstep (se 2 (by rfl) ⟨1283262, by rfl⟩ : syracuseStep 3422033 = 2566525) B2566525
theorem B1521491 : Blo 1520457 1521491 := bstep (se 1 (by rfl) ⟨1141118, by rfl⟩ : syracuseStep 1521491 = 2282237) B2282237
theorem B2283347 : Blo 1520457 2283347 := bstep (se 1 (by rfl) ⟨1712510, by rfl⟩ : syracuseStep 2283347 = 3425021) B3425021
theorem B3422051 : Blo 1520457 3422051 := bstep (se 1 (by rfl) ⟨2566538, by rfl⟩ : syracuseStep 3422051 = 5133077) B5133077
theorem B1521507 : Blo 1520457 1521507 := bstep (se 1 (by rfl) ⟨1141130, by rfl⟩ : syracuseStep 1521507 = 2282261) B2282261
theorem B3250019 : Blo 1520457 3250019 := bstep (se 1 (by rfl) ⟨2437514, by rfl⟩ : syracuseStep 3250019 = 4875029) B4875029
theorem B2283377 : Blo 1520457 2283377 := bstep (se 2 (by rfl) ⟨856266, by rfl⟩ : syracuseStep 2283377 = 1712533) B1712533
theorem B1521523 : Blo 1520457 1521523 := bstep (se 1 (by rfl) ⟨1141142, by rfl⟩ : syracuseStep 1521523 = 2282285) B2282285
theorem B5134211 : Blo 1520457 5134211 := bstep (se 1 (by rfl) ⟨3850658, by rfl⟩ : syracuseStep 5134211 = 7701317) B7701317
theorem B1521539 : Blo 1520457 1521539 := bstep (se 1 (by rfl) ⟨1141154, by rfl⟩ : syracuseStep 1521539 = 2282309) B2282309
theorem B2283395 : Blo 1520457 2283395 := bstep (se 1 (by rfl) ⟨1712546, by rfl⟩ : syracuseStep 2283395 = 3425093) B3425093
theorem B41662349 : Blo 1520457 41662349 := bstep (se 3 (by rfl) ⟨7811690, by rfl⟩ : syracuseStep 41662349 = 15623381) B15623381
theorem B1521555 : Blo 1520457 1521555 := bstep (se 1 (by rfl) ⟨1141166, by rfl⟩ : syracuseStep 1521555 = 2282333) B2282333
theorem B2283425 : Blo 1520457 2283425 := bstep (se 2 (by rfl) ⟨856284, by rfl⟩ : syracuseStep 2283425 = 1712569) B1712569
theorem B1521571 : Blo 1520457 1521571 := bstep (se 1 (by rfl) ⟨1141178, by rfl⟩ : syracuseStep 1521571 = 2282357) B2282357
theorem B5207971 : Blo 1520457 5207971 := bstep (se 1 (by rfl) ⟨3905978, by rfl⟩ : syracuseStep 5207971 = 7811957) B7811957
theorem B1521587 : Blo 1520457 1521587 := bstep (se 1 (by rfl) ⟨1141190, by rfl⟩ : syracuseStep 1521587 = 2282381) B2282381
theorem B2283443 : Blo 1520457 2283443 := bstep (se 1 (by rfl) ⟨1712582, by rfl⟩ : syracuseStep 2283443 = 3425165) B3425165
theorem B1521603 : Blo 1520457 1521603 := bstep (se 1 (by rfl) ⟨1141202, by rfl⟩ : syracuseStep 1521603 = 2282405) B2282405
theorem B2283473 : Blo 1520457 2283473 := bstep (se 2 (by rfl) ⟨856302, by rfl⟩ : syracuseStep 2283473 = 1712605) B1712605
theorem B1521619 : Blo 1520457 1521619 := bstep (se 1 (by rfl) ⟨1141214, by rfl⟩ : syracuseStep 1521619 = 2282429) B2282429
theorem B1521635 : Blo 1520457 1521635 := bstep (se 1 (by rfl) ⟨1141226, by rfl⟩ : syracuseStep 1521635 = 2282453) B2282453
theorem B2283491 : Blo 1520457 2283491 := bstep (se 1 (by rfl) ⟨1712618, by rfl⟩ : syracuseStep 2283491 = 3425237) B3425237
theorem B1521651 : Blo 1520457 1521651 := bstep (se 1 (by rfl) ⟨1141238, by rfl⟩ : syracuseStep 1521651 = 2282477) B2282477
theorem B2283521 : Blo 1520457 2283521 := bstep (se 2 (by rfl) ⟨856320, by rfl⟩ : syracuseStep 2283521 = 1712641) B1712641
theorem B1521667 : Blo 1520457 1521667 := bstep (se 1 (by rfl) ⟨1141250, by rfl⟩ : syracuseStep 1521667 = 2282501) B2282501
theorem B1521683 : Blo 1520457 1521683 := bstep (se 1 (by rfl) ⟨1141262, by rfl⟩ : syracuseStep 1521683 = 2282525) B2282525
theorem B2283539 : Blo 1520457 2283539 := bstep (se 1 (by rfl) ⟨1712654, by rfl⟩ : syracuseStep 2283539 = 3425309) B3425309
theorem B1521699 : Blo 1520457 1521699 := bstep (se 1 (by rfl) ⟨1141274, by rfl⟩ : syracuseStep 1521699 = 2282549) B2282549
theorem B2283569 : Blo 1520457 2283569 := bstep (se 2 (by rfl) ⟨856338, by rfl⟩ : syracuseStep 2283569 = 1712677) B1712677
theorem B1521715 : Blo 1520457 1521715 := bstep (se 1 (by rfl) ⟨1141286, by rfl⟩ : syracuseStep 1521715 = 2282573) B2282573
theorem B1521731 : Blo 1520457 1521731 := bstep (se 1 (by rfl) ⟨1141298, by rfl⟩ : syracuseStep 1521731 = 2282597) B2282597
theorem B2283587 : Blo 1520457 2283587 := bstep (se 1 (by rfl) ⟨1712690, by rfl⟩ : syracuseStep 2283587 = 3425381) B3425381
theorem B9877573 : Blo 1520457 9877573 := bstep (se 4 (by rfl) ⟨926022, by rfl⟩ : syracuseStep 9877573 = 1852045) B1852045
theorem B1521747 : Blo 1520457 1521747 := bstep (se 1 (by rfl) ⟨1141310, by rfl⟩ : syracuseStep 1521747 = 2282621) B2282621
theorem B1521763 : Blo 1520457 1521763 := bstep (se 1 (by rfl) ⟨1141322, by rfl⟩ : syracuseStep 1521763 = 2282645) B2282645
theorem B2283617 : Blo 1520457 2283617 := bstep (se 2 (by rfl) ⟨856356, by rfl⟩ : syracuseStep 2283617 = 1712713) B1712713
theorem B3422321 : Blo 1520457 3422321 := bstep (se 2 (by rfl) ⟨1283370, by rfl⟩ : syracuseStep 3422321 = 2566741) B2566741
theorem B1521779 : Blo 1520457 1521779 := bstep (se 1 (by rfl) ⟨1141334, by rfl⟩ : syracuseStep 1521779 = 2282669) B2282669
theorem B2283635 : Blo 1520457 2283635 := bstep (se 1 (by rfl) ⟨1712726, by rfl⟩ : syracuseStep 2283635 = 3425453) B3425453
theorem B3422339 : Blo 1520457 3422339 := bstep (se 1 (by rfl) ⟨2566754, by rfl⟩ : syracuseStep 3422339 = 5133509) B5133509
theorem B1521795 : Blo 1520457 1521795 := bstep (se 1 (by rfl) ⟨1141346, by rfl⟩ : syracuseStep 1521795 = 2282693) B2282693
theorem B5134481 : Blo 1520457 5134481 := bstep (se 2 (by rfl) ⟨1925430, by rfl⟩ : syracuseStep 5134481 = 3850861) B3850861
theorem B1521811 : Blo 1520457 1521811 := bstep (se 1 (by rfl) ⟨1141358, by rfl⟩ : syracuseStep 1521811 = 2282717) B2282717
theorem B2283665 : Blo 1520457 2283665 := bstep (se 2 (by rfl) ⟨856374, by rfl⟩ : syracuseStep 2283665 = 1712749) B1712749
theorem B1521827 : Blo 1520457 1521827 := bstep (se 1 (by rfl) ⟨1141370, by rfl⟩ : syracuseStep 1521827 = 2282741) B2282741
theorem B2283683 : Blo 1520457 2283683 := bstep (se 1 (by rfl) ⟨1712762, by rfl⟩ : syracuseStep 2283683 = 3425525) B3425525
theorem B1521843 : Blo 1520457 1521843 := bstep (se 1 (by rfl) ⟨1141382, by rfl⟩ : syracuseStep 1521843 = 2282765) B2282765
theorem B1521859 : Blo 1520457 1521859 := bstep (se 1 (by rfl) ⟨1141394, by rfl⟩ : syracuseStep 1521859 = 2282789) B2282789
theorem B13179077 : Blo 1520457 13179077 := bstep (se 4 (by rfl) ⟨1235538, by rfl⟩ : syracuseStep 13179077 = 2471077) B2471077
theorem B1521875 : Blo 1520457 1521875 := bstep (se 1 (by rfl) ⟨1141406, by rfl⟩ : syracuseStep 1521875 = 2282813) B2282813
theorem B1521891 : Blo 1520457 1521891 := bstep (se 1 (by rfl) ⟨1141418, by rfl⟩ : syracuseStep 1521891 = 2282837) B2282837
theorem B1521907 : Blo 1520457 1521907 := bstep (se 1 (by rfl) ⟨1141430, by rfl⟩ : syracuseStep 1521907 = 2282861) B2282861
theorem B1521923 : Blo 1520457 1521923 := bstep (se 1 (by rfl) ⟨1141442, by rfl⟩ : syracuseStep 1521923 = 2282885) B2282885
theorem B1521939 : Blo 1520457 1521939 := bstep (se 1 (by rfl) ⟨1141454, by rfl⟩ : syracuseStep 1521939 = 2282909) B2282909
theorem B1521955 : Blo 1520457 1521955 := bstep (se 1 (by rfl) ⟨1141466, by rfl⟩ : syracuseStep 1521955 = 2282933) B2282933
theorem B1521971 : Blo 1520457 1521971 := bstep (se 1 (by rfl) ⟨1141478, by rfl⟩ : syracuseStep 1521971 = 2282957) B2282957
theorem B1521987 : Blo 1520457 1521987 := bstep (se 1 (by rfl) ⟨1141490, by rfl⟩ : syracuseStep 1521987 = 2282981) B2282981
theorem B12998981 : Blo 1520457 12998981 := bstep (se 4 (by rfl) ⟨1218654, by rfl⟩ : syracuseStep 12998981 = 2437309) B2437309
theorem B1522003 : Blo 1520457 1522003 := bstep (se 1 (by rfl) ⟨1141502, by rfl⟩ : syracuseStep 1522003 = 2283005) B2283005
theorem B1522019 : Blo 1520457 1522019 := bstep (se 1 (by rfl) ⟨1141514, by rfl⟩ : syracuseStep 1522019 = 2283029) B2283029
theorem B1522035 : Blo 1520457 1522035 := bstep (se 1 (by rfl) ⟨1141526, by rfl⟩ : syracuseStep 1522035 = 2283053) B2283053
theorem B1522051 : Blo 1520457 1522051 := bstep (se 1 (by rfl) ⟨1141538, by rfl⟩ : syracuseStep 1522051 = 2283077) B2283077
theorem B3422609 : Blo 1520457 3422609 := bstep (se 2 (by rfl) ⟨1283478, by rfl⟩ : syracuseStep 3422609 = 2566957) B2566957
theorem B1522067 : Blo 1520457 1522067 := bstep (se 1 (by rfl) ⟨1141550, by rfl⟩ : syracuseStep 1522067 = 2283101) B2283101
theorem B3422627 : Blo 1520457 3422627 := bstep (se 1 (by rfl) ⟨2566970, by rfl⟩ : syracuseStep 3422627 = 5133941) B5133941
theorem B1522083 : Blo 1520457 1522083 := bstep (se 1 (by rfl) ⟨1141562, by rfl⟩ : syracuseStep 1522083 = 2283125) B2283125
theorem B1522099 : Blo 1520457 1522099 := bstep (se 1 (by rfl) ⟨1141574, by rfl⟩ : syracuseStep 1522099 = 2283149) B2283149
theorem B1522115 : Blo 1520457 1522115 := bstep (se 1 (by rfl) ⟨1141586, by rfl⟩ : syracuseStep 1522115 = 2283173) B2283173
theorem B4110797 : Blo 1520457 4110797 := bstep (se 3 (by rfl) ⟨770774, by rfl⟩ : syracuseStep 4110797 = 1541549) B1541549
theorem B4331981 : Blo 1520457 4331981 := bstep (se 3 (by rfl) ⟨812246, by rfl⟩ : syracuseStep 4331981 = 1624493) B1624493
theorem B1522131 : Blo 1520457 1522131 := bstep (se 1 (by rfl) ⟨1141598, by rfl⟩ : syracuseStep 1522131 = 2283197) B2283197
theorem B1563107 : Blo 1520457 1563107 := bstep (se 1 (by rfl) ⟨1172330, by rfl⟩ : syracuseStep 1563107 = 2344661) B2344661
theorem B1522147 : Blo 1520457 1522147 := bstep (se 1 (by rfl) ⟨1141610, by rfl⟩ : syracuseStep 1522147 = 2283221) B2283221
theorem B1522163 : Blo 1520457 1522163 := bstep (se 1 (by rfl) ⟨1141622, by rfl⟩ : syracuseStep 1522163 = 2283245) B2283245
theorem B1522179 : Blo 1520457 1522179 := bstep (se 1 (by rfl) ⟨1141634, by rfl⟩ : syracuseStep 1522179 = 2283269) B2283269
theorem B7707149 : Blo 1520457 7707149 := bstep (se 3 (by rfl) ⟨1445090, by rfl⟩ : syracuseStep 7707149 = 2890181) B2890181
theorem B1522195 : Blo 1520457 1522195 := bstep (se 1 (by rfl) ⟨1141646, by rfl⟩ : syracuseStep 1522195 = 2283293) B2283293
theorem B1522211 : Blo 1520457 1522211 := bstep (se 1 (by rfl) ⟨1141658, by rfl⟩ : syracuseStep 1522211 = 2283317) B2283317
theorem B1710643 : Blo 1520457 1710643 := bstep (se 1 (by rfl) ⟨1282982, by rfl⟩ : syracuseStep 1710643 = 2565965) B2565965
theorem B1522227 : Blo 1520457 1522227 := bstep (se 1 (by rfl) ⟨1141670, by rfl⟩ : syracuseStep 1522227 = 2283341) B2283341
theorem B1522243 : Blo 1520457 1522243 := bstep (se 1 (by rfl) ⟨1141682, by rfl⟩ : syracuseStep 1522243 = 2283365) B2283365
theorem B1522259 : Blo 1520457 1522259 := bstep (se 1 (by rfl) ⟨1141694, by rfl⟩ : syracuseStep 1522259 = 2283389) B2283389
theorem B1522275 : Blo 1520457 1522275 := bstep (se 1 (by rfl) ⟨1141706, by rfl⟩ : syracuseStep 1522275 = 2283413) B2283413
theorem B29244017 : Blo 1520457 29244017 := bstep (se 2 (by rfl) ⟨10966506, by rfl⟩ : syracuseStep 29244017 = 21933013) B21933013
theorem B1522291 : Blo 1520457 1522291 := bstep (se 1 (by rfl) ⟨1141718, by rfl⟩ : syracuseStep 1522291 = 2283437) B2283437
theorem B4332163 : Blo 1520457 4332163 := bstep (se 1 (by rfl) ⟨3249122, by rfl⟩ : syracuseStep 4332163 = 6498245) B6498245
theorem B1522307 : Blo 1520457 1522307 := bstep (se 1 (by rfl) ⟨1141730, by rfl⟩ : syracuseStep 1522307 = 2283461) B2283461
theorem B3906193 : Blo 1520457 3906193 := bstep (se 2 (by rfl) ⟨1464822, by rfl⟩ : syracuseStep 3906193 = 2929645) B2929645
theorem B1522323 : Blo 1520457 1522323 := bstep (se 1 (by rfl) ⟨1141742, by rfl⟩ : syracuseStep 1522323 = 2283485) B2283485
theorem B3848867 : Blo 1520457 3848867 := bstep (se 1 (by rfl) ⟨2886650, by rfl⟩ : syracuseStep 3848867 = 5773301) B5773301
theorem B1522339 : Blo 1520457 1522339 := bstep (se 1 (by rfl) ⟨1141754, by rfl⟩ : syracuseStep 1522339 = 2283509) B2283509
theorem B5135021 : Blo 1520457 5135021 := bstep (se 3 (by rfl) ⟨962816, by rfl⟩ : syracuseStep 5135021 = 1925633) B1925633
theorem B3422897 : Blo 1520457 3422897 := bstep (se 2 (by rfl) ⟨1283586, by rfl⟩ : syracuseStep 3422897 = 2567173) B2567173
theorem B1522355 : Blo 1520457 1522355 := bstep (se 1 (by rfl) ⟨1141766, by rfl⟩ : syracuseStep 1522355 = 2283533) B2283533
theorem B1710787 : Blo 1520457 1710787 := bstep (se 1 (by rfl) ⟨1283090, by rfl⟩ : syracuseStep 1710787 = 2566181) B2566181
theorem B3422915 : Blo 1520457 3422915 := bstep (se 1 (by rfl) ⟨2567186, by rfl⟩ : syracuseStep 3422915 = 5134373) B5134373
theorem B1522371 : Blo 1520457 1522371 := bstep (se 1 (by rfl) ⟨1141778, by rfl⟩ : syracuseStep 1522371 = 2283557) B2283557
theorem B8665805 : Blo 1520457 8665805 := bstep (se 3 (by rfl) ⟨1624838, by rfl⟩ : syracuseStep 8665805 = 3249677) B3249677
theorem B1522387 : Blo 1520457 1522387 := bstep (se 1 (by rfl) ⟨1141790, by rfl⟩ : syracuseStep 1522387 = 2283581) B2283581
theorem B5135075 : Blo 1520457 5135075 := bstep (se 1 (by rfl) ⟨3851306, by rfl⟩ : syracuseStep 5135075 = 7702613) B7702613
theorem B1522403 : Blo 1520457 1522403 := bstep (se 1 (by rfl) ⟨1141802, by rfl⟩ : syracuseStep 1522403 = 2283605) B2283605
theorem B1522419 : Blo 1520457 1522419 := bstep (se 1 (by rfl) ⟨1141814, by rfl⟩ : syracuseStep 1522419 = 2283629) B2283629
theorem B1522435 : Blo 1520457 1522435 := bstep (se 1 (by rfl) ⟨1141826, by rfl⟩ : syracuseStep 1522435 = 2283653) B2283653
theorem B1522451 : Blo 1520457 1522451 := bstep (se 1 (by rfl) ⟨1141838, by rfl⟩ : syracuseStep 1522451 = 2283677) B2283677
theorem B2054977 : Blo 1520457 2054977 := bstep (se 2 (by rfl) ⟨770616, by rfl⟩ : syracuseStep 2054977 = 1541233) B1541233
theorem B1710931 : Blo 1520457 1710931 := bstep (se 1 (by rfl) ⟨1283198, by rfl⟩ : syracuseStep 1710931 = 2566397) B2566397
theorem B3849059 : Blo 1520457 3849059 := bstep (se 1 (by rfl) ⟨2886794, by rfl⟩ : syracuseStep 3849059 = 5773589) B5773589
theorem B3423185 : Blo 1520457 3423185 := bstep (se 2 (by rfl) ⟨1283694, by rfl⟩ : syracuseStep 3423185 = 2567389) B2567389
theorem B1711075 : Blo 1520457 1711075 := bstep (se 1 (by rfl) ⟨1283306, by rfl⟩ : syracuseStep 1711075 = 2566613) B2566613
theorem B3423203 : Blo 1520457 3423203 := bstep (se 1 (by rfl) ⟨2567402, by rfl⟩ : syracuseStep 3423203 = 5134805) B5134805
theorem B5135345 : Blo 1520457 5135345 := bstep (se 2 (by rfl) ⟨1925754, by rfl⟩ : syracuseStep 5135345 = 3851509) B3851509
theorem B2604115 : Blo 1520457 2604115 := bstep (se 1 (by rfl) ⟨1953086, by rfl⟩ : syracuseStep 2604115 = 3906173) B3906173
theorem B4332653 : Blo 1520457 4332653 := bstep (se 3 (by rfl) ⟨812372, by rfl⟩ : syracuseStep 4332653 = 1624745) B1624745
theorem B1711219 : Blo 1520457 1711219 := bstep (se 1 (by rfl) ⟨1283414, by rfl⟩ : syracuseStep 1711219 = 2566829) B2566829
theorem B7699697 : Blo 1520457 7699697 := bstep (se 2 (by rfl) ⟨2887386, by rfl⟩ : syracuseStep 7699697 = 5774773) B5774773
theorem B3423473 : Blo 1520457 3423473 := bstep (se 2 (by rfl) ⟨1283802, by rfl⟩ : syracuseStep 3423473 = 2567605) B2567605
theorem B1711363 : Blo 1520457 1711363 := bstep (se 1 (by rfl) ⟨1283522, by rfl⟩ : syracuseStep 1711363 = 2567045) B2567045
theorem B3423491 : Blo 1520457 3423491 := bstep (se 1 (by rfl) ⟨2567618, by rfl⟩ : syracuseStep 3423491 = 5135237) B5135237
theorem B4873517 : Blo 1520457 4873517 := bstep (se 3 (by rfl) ⟨913784, by rfl⟩ : syracuseStep 4873517 = 1827569) B1827569
theorem B1924499 : Blo 1520457 1924499 := bstep (se 1 (by rfl) ⟨1443374, by rfl⟩ : syracuseStep 1924499 = 2886749) B2886749
theorem B1711507 : Blo 1520457 1711507 := bstep (se 1 (by rfl) ⟨1283630, by rfl⟩ : syracuseStep 1711507 = 2567261) B2567261
theorem B13876721 : Blo 1520457 13876721 := bstep (se 2 (by rfl) ⟨5203770, by rfl⟩ : syracuseStep 13876721 = 10407541) B10407541
theorem B5135885 : Blo 1520457 5135885 := bstep (se 3 (by rfl) ⟨962978, by rfl⟩ : syracuseStep 5135885 = 1925957) B1925957
theorem B3423761 : Blo 1520457 3423761 := bstep (se 2 (by rfl) ⟨1283910, by rfl⟩ : syracuseStep 3423761 = 2567821) B2567821
theorem B1711651 : Blo 1520457 1711651 := bstep (se 1 (by rfl) ⟨1283738, by rfl⟩ : syracuseStep 1711651 = 2567477) B2567477
theorem B3423779 : Blo 1520457 3423779 := bstep (se 1 (by rfl) ⟨2567834, by rfl⟩ : syracuseStep 3423779 = 5135669) B5135669
theorem B5135939 : Blo 1520457 5135939 := bstep (se 1 (by rfl) ⟨3851954, by rfl⟩ : syracuseStep 5135939 = 7703909) B7703909
theorem B4628141 : Blo 1520457 4628141 := bstep (se 3 (by rfl) ⟨867776, by rfl⟩ : syracuseStep 4628141 = 1735553) B1735553
theorem B1711795 : Blo 1520457 1711795 := bstep (se 1 (by rfl) ⟨1283846, by rfl⟩ : syracuseStep 1711795 = 2567693) B2567693
theorem B3850001 : Blo 1520457 3850001 := bstep (se 2 (by rfl) ⟨1443750, by rfl⟩ : syracuseStep 3850001 = 2887501) B2887501
theorem B7315235 : Blo 1520457 7315235 := bstep (se 1 (by rfl) ⟨5486426, by rfl⟩ : syracuseStep 7315235 = 10972853) B10972853
theorem B3424049 : Blo 1520457 3424049 := bstep (se 2 (by rfl) ⟨1284018, by rfl⟩ : syracuseStep 3424049 = 2568037) B2568037
theorem B4628273 : Blo 1520457 4628273 := bstep (se 2 (by rfl) ⟨1735602, by rfl⟩ : syracuseStep 4628273 = 3471205) B3471205
theorem B3850051 : Blo 1520457 3850051 := bstep (se 1 (by rfl) ⟨2887538, by rfl⟩ : syracuseStep 3850051 = 5775077) B5775077
theorem B1711939 : Blo 1520457 1711939 := bstep (se 1 (by rfl) ⟨1283954, by rfl⟩ : syracuseStep 1711939 = 2567909) B2567909
theorem B8781637 : Blo 1520457 8781637 := bstep (se 4 (by rfl) ⟨823278, by rfl⟩ : syracuseStep 8781637 = 1646557) B1646557
theorem B3424067 : Blo 1520457 3424067 := bstep (se 1 (by rfl) ⟨2568050, by rfl⟩ : syracuseStep 3424067 = 5136101) B5136101
theorem B5136209 : Blo 1520457 5136209 := bstep (se 2 (by rfl) ⟨1926078, by rfl⟩ : syracuseStep 5136209 = 3852157) B3852157
theorem B4169603 : Blo 1520457 4169603 := bstep (se 1 (by rfl) ⟨3127202, by rfl⟩ : syracuseStep 4169603 = 6254405) B6254405
theorem B5775245 : Blo 1520457 5775245 := bstep (se 3 (by rfl) ⟨1082858, by rfl⟩ : syracuseStep 5775245 = 2165717) B2165717
theorem B3850193 : Blo 1520457 3850193 := bstep (se 2 (by rfl) ⟨1443822, by rfl⟩ : syracuseStep 3850193 = 2887645) B2887645
theorem B1712083 : Blo 1520457 1712083 := bstep (se 1 (by rfl) ⟨1284062, by rfl⟩ : syracuseStep 1712083 = 2568125) B2568125
theorem B8224753 : Blo 1520457 8224753 := bstep (se 2 (by rfl) ⟨3084282, by rfl⟩ : syracuseStep 8224753 = 6168565) B6168565
theorem B3424409 : Blo 1520457 3424409 := bstep (se 2 (by rfl) ⟨1284153, by rfl⟩ : syracuseStep 3424409 = 2568307) B2568307
theorem B1712299 : Blo 1520457 1712299 := bstep (se 1 (by rfl) ⟨1284224, by rfl⟩ : syracuseStep 1712299 = 2568449) B2568449
theorem B5775533 : Blo 1520457 5775533 := bstep (se 3 (by rfl) ⟨1082912, by rfl⟩ : syracuseStep 5775533 = 2165825) B2165825
theorem B6938797 : Blo 1520457 6938797 := bstep (se 3 (by rfl) ⟨1301024, by rfl⟩ : syracuseStep 6938797 = 2602049) B2602049
theorem B5775563 : Blo 1520457 5775563 := bstep (se 1 (by rfl) ⟨4331672, by rfl⟩ : syracuseStep 5775563 = 8663345) B8663345
theorem B5136587 : Blo 1520457 5136587 := bstep (se 1 (by rfl) ⟨3852440, by rfl⟩ : syracuseStep 5136587 = 7704881) B7704881
theorem B1827031 : Blo 1520457 1827031 := bstep (se 1 (by rfl) ⟨1370273, by rfl⟩ : syracuseStep 1827031 = 2740547) B2740547
theorem B3424499 : Blo 1520457 3424499 := bstep (se 1 (by rfl) ⟨2568374, by rfl⟩ : syracuseStep 3424499 = 5136749) B5136749
theorem B3424535 : Blo 1520457 3424535 := bstep (se 1 (by rfl) ⟨2568401, by rfl⟩ : syracuseStep 3424535 = 5136803) B5136803
theorem B1712407 : Blo 1520457 1712407 := bstep (se 1 (by rfl) ⟨1284305, by rfl⟩ : syracuseStep 1712407 = 2568611) B2568611
theorem B18497909 : Blo 1520457 18497909 := bstep (se 5 (by rfl) ⟨867089, by rfl⟩ : syracuseStep 18497909 = 1734179) B1734179
theorem B1925527 : Blo 1520457 1925527 := bstep (se 1 (by rfl) ⟨1444145, by rfl⟩ : syracuseStep 1925527 = 2888291) B2888291
theorem B3850699 : Blo 1520457 3850699 := bstep (se 1 (by rfl) ⟨2888024, by rfl⟩ : syracuseStep 3850699 = 5776049) B5776049
theorem B3424715 : Blo 1520457 3424715 := bstep (se 1 (by rfl) ⟨2568536, by rfl⟩ : syracuseStep 3424715 = 5137073) B5137073
theorem B1712587 : Blo 1520457 1712587 := bstep (se 1 (by rfl) ⟨1284440, by rfl⟩ : syracuseStep 1712587 = 2568881) B2568881
theorem B5136857 : Blo 1520457 5136857 := bstep (se 2 (by rfl) ⟨1926321, by rfl⟩ : syracuseStep 5136857 = 3852643) B3852643
theorem B52724195 : Blo 1520457 52724195 := bstep (se 1 (by rfl) ⟨39543146, by rfl⟩ : syracuseStep 52724195 = 79086293) B79086293
theorem B3424769 : Blo 1520457 3424769 := bstep (se 2 (by rfl) ⟨1284288, by rfl⟩ : syracuseStep 3424769 = 2568577) B2568577
theorem B1712695 : Blo 1520457 1712695 := bstep (se 1 (by rfl) ⟨1284521, by rfl⟩ : syracuseStep 1712695 = 2569043) B2569043
theorem B3850841 : Blo 1520457 3850841 := bstep (se 2 (by rfl) ⟨1444065, by rfl⟩ : syracuseStep 3850841 = 2888131) B2888131
theorem B3424985 : Blo 1520457 3424985 := bstep (se 2 (by rfl) ⟨1284369, by rfl⟩ : syracuseStep 3424985 = 2568739) B2568739
theorem B3425075 : Blo 1520457 3425075 := bstep (se 1 (by rfl) ⟨2568806, by rfl⟩ : syracuseStep 3425075 = 5137613) B5137613
theorem B3425111 : Blo 1520457 3425111 := bstep (se 1 (by rfl) ⟨2568833, by rfl⟩ : syracuseStep 3425111 = 5137667) B5137667
theorem B5776217 : Blo 1520457 5776217 := bstep (se 2 (by rfl) ⟨2166081, by rfl⟩ : syracuseStep 5776217 = 4332163) B4332163
theorem B5202839 : Blo 1520457 5202839 := bstep (se 1 (by rfl) ⟨3902129, by rfl⟩ : syracuseStep 5202839 = 7804259) B7804259
theorem B3425291 : Blo 1520457 3425291 := bstep (se 1 (by rfl) ⟨2568968, by rfl⟩ : syracuseStep 3425291 = 5137937) B5137937
theorem B5932055 : Blo 1520457 5932055 := bstep (se 1 (by rfl) ⟨4449041, by rfl⟩ : syracuseStep 5932055 = 8898083) B8898083
theorem B7037975 : Blo 1520457 7037975 := bstep (se 1 (by rfl) ⟨5278481, by rfl⟩ : syracuseStep 7037975 = 10556963) B10556963
theorem B3425345 : Blo 1520457 3425345 := bstep (se 2 (by rfl) ⟨1284504, by rfl⟩ : syracuseStep 3425345 = 2569009) B2569009
theorem B5776535 : Blo 1520457 5776535 := bstep (se 1 (by rfl) ⟨4332401, by rfl⟩ : syracuseStep 5776535 = 8664803) B8664803
theorem B5137559 : Blo 1520457 5137559 := bstep (se 1 (by rfl) ⟨3853169, by rfl⟩ : syracuseStep 5137559 = 7706339) B7706339
theorem B4334771 : Blo 1520457 4334771 := bstep (se 1 (by rfl) ⟨3251078, by rfl⟩ : syracuseStep 4334771 = 6502157) B6502157
theorem B10962125 : Blo 1520457 10962125 := bstep (se 3 (by rfl) ⟨2055398, by rfl⟩ : syracuseStep 10962125 = 4110797) B4110797
theorem B1828055 : Blo 1520457 1828055 := bstep (se 1 (by rfl) ⟨1371041, by rfl⟩ : syracuseStep 1828055 = 2742083) B2742083
theorem B12993857 : Blo 1520457 12993857 := bstep (se 2 (by rfl) ⟨4872696, by rfl⟩ : syracuseStep 12993857 = 9745393) B9745393
theorem B3851671 : Blo 1520457 3851671 := bstep (se 1 (by rfl) ⟨2888753, by rfl⟩ : syracuseStep 3851671 = 5777507) B5777507
theorem B1541675 : Blo 1520457 1541675 := bstep (se 1 (by rfl) ⟨1156256, by rfl⟩ : syracuseStep 1541675 = 2312513) B2312513
theorem B7308893 : Blo 1520457 7308893 := bstep (se 3 (by rfl) ⟨1370417, by rfl⟩ : syracuseStep 7308893 = 2740835) B2740835
theorem B9881189 : Blo 1520457 9881189 := bstep (se 4 (by rfl) ⟨926361, by rfl⟩ : syracuseStep 9881189 = 1852723) B1852723
theorem B5138099 : Blo 1520457 5138099 := bstep (se 1 (by rfl) ⟨3853574, by rfl⟩ : syracuseStep 5138099 = 7707149) B7707149
theorem B7702289 : Blo 1520457 7702289 := bstep (se 2 (by rfl) ⟨2888358, by rfl⟩ : syracuseStep 7702289 = 5776717) B5776717
theorem B2565911 : Blo 1520457 2565911 := bstep (se 1 (by rfl) ⟨1924433, by rfl⟩ : syracuseStep 2565911 = 3848867) B3848867
theorem B5777203 : Blo 1520457 5777203 := bstep (se 1 (by rfl) ⟨4332902, by rfl⟩ : syracuseStep 5777203 = 8665805) B8665805
theorem B3852107 : Blo 1520457 3852107 := bstep (se 1 (by rfl) ⟨2889080, by rfl⟩ : syracuseStep 3852107 = 5778161) B5778161
theorem B9750365 : Blo 1520457 9750365 := bstep (se 3 (by rfl) ⟨1828193, by rfl⟩ : syracuseStep 9750365 = 3656387) B3656387
theorem B2566039 : Blo 1520457 2566039 := bstep (se 1 (by rfl) ⟨1924529, by rfl⟩ : syracuseStep 2566039 = 3849059) B3849059
theorem B7702451 : Blo 1520457 7702451 := bstep (se 1 (by rfl) ⟨5776838, by rfl⟩ : syracuseStep 7702451 = 11553677) B11553677
theorem B1624087 : Blo 1520457 1624087 := bstep (se 1 (by rfl) ⟨1218065, by rfl⟩ : syracuseStep 1624087 = 2436131) B2436131
theorem B6498397 : Blo 1520457 6498397 := bstep (se 3 (by rfl) ⟨1218449, by rfl⟩ : syracuseStep 6498397 = 2436899) B2436899
theorem B3852481 : Blo 1520457 3852481 := bstep (se 2 (by rfl) ⟨1444680, by rfl⟩ : syracuseStep 3852481 = 2889361) B2889361
theorem B8784089 : Blo 1520457 8784089 := bstep (se 2 (by rfl) ⟨3294033, by rfl⟩ : syracuseStep 8784089 = 6588067) B6588067
theorem B9251147 : Blo 1520457 9251147 := bstep (se 1 (by rfl) ⟨6938360, by rfl⟩ : syracuseStep 9251147 = 13876721) B13876721
theorem B11118941 : Blo 1520457 11118941 := bstep (se 3 (by rfl) ⟨2084801, by rfl⟩ : syracuseStep 11118941 = 4169603) B4169603
theorem B16673141 : Blo 1520457 16673141 := bstep (se 5 (by rfl) ⟨781553, by rfl⟩ : syracuseStep 16673141 = 1563107) B1563107
theorem B11708849 : Blo 1520457 11708849 := bstep (se 2 (by rfl) ⟨4390818, by rfl⟩ : syracuseStep 11708849 = 8781637) B8781637
theorem B2566667 : Blo 1520457 2566667 := bstep (se 1 (by rfl) ⟨1925000, by rfl⟩ : syracuseStep 2566667 = 3850001) B3850001
theorem B26012177 : Blo 1520457 26012177 := bstep (se 2 (by rfl) ⟨9754566, by rfl⟩ : syracuseStep 26012177 = 19509133) B19509133
theorem B4876823 : Blo 1520457 4876823 := bstep (se 1 (by rfl) ⟨3657617, by rfl⟩ : syracuseStep 4876823 = 7315235) B7315235
theorem B2566795 : Blo 1520457 2566795 := bstep (se 1 (by rfl) ⟨1925096, by rfl⟩ : syracuseStep 2566795 = 3850193) B3850193
theorem B4877003 : Blo 1520457 4877003 := bstep (se 1 (by rfl) ⟨3657752, by rfl⟩ : syracuseStep 4877003 = 7315505) B7315505
theorem B5557015 : Blo 1520457 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B3853079 : Blo 1520457 3853079 := bstep (se 1 (by rfl) ⟨2889809, by rfl⟩ : syracuseStep 3853079 = 5779619) B5779619
theorem B3083033 : Blo 1520457 3083033 := bstep (se 2 (by rfl) ⟨1156137, by rfl⟩ : syracuseStep 3083033 = 2312275) B2312275
theorem B2566937 : Blo 1520457 2566937 := bstep (se 2 (by rfl) ⟨962601, by rfl⟩ : syracuseStep 2566937 = 1925203) B1925203
theorem B8227649 : Blo 1520457 8227649 := bstep (se 2 (by rfl) ⟨3085368, by rfl⟩ : syracuseStep 8227649 = 6170737) B6170737
theorem B1624907 : Blo 1520457 1624907 := bstep (se 1 (by rfl) ⟨1218680, by rfl⟩ : syracuseStep 1624907 = 2437361) B2437361
theorem B4877131 : Blo 1520457 4877131 := bstep (se 1 (by rfl) ⟨3657848, by rfl⟩ : syracuseStep 4877131 = 7315697) B7315697
theorem B2886529 : Blo 1520457 2886529 := bstep (se 2 (by rfl) ⟨1082448, by rfl⟩ : syracuseStep 2886529 = 2164897) B2164897
theorem B6499217 : Blo 1520457 6499217 := bstep (se 2 (by rfl) ⟨2437206, by rfl⟩ : syracuseStep 6499217 = 4874413) B4874413
theorem B2567065 : Blo 1520457 2567065 := bstep (se 2 (by rfl) ⟨962649, by rfl⟩ : syracuseStep 2567065 = 1925299) B1925299
theorem B38972339 : Blo 1520457 38972339 := bstep (se 1 (by rfl) ⟨29229254, by rfl⟩ : syracuseStep 38972339 = 58458509) B58458509
theorem B4877273 : Blo 1520457 4877273 := bstep (se 2 (by rfl) ⟨1828977, by rfl⟩ : syracuseStep 4877273 = 3657955) B3657955
theorem B5778449 : Blo 1520457 5778449 := bstep (se 2 (by rfl) ⟨2166918, by rfl⟩ : syracuseStep 5778449 = 4333837) B4333837
theorem B3468377 : Blo 1520457 3468377 := bstep (se 2 (by rfl) ⟨1300641, by rfl⟩ : syracuseStep 3468377 = 2601283) B2601283
theorem B2313419 : Blo 1520457 2313419 := bstep (se 1 (by rfl) ⟨1735064, by rfl⟩ : syracuseStep 2313419 = 3470129) B3470129
theorem B3656983 : Blo 1520457 3656983 := bstep (se 1 (by rfl) ⟨2742737, by rfl⟩ : syracuseStep 3656983 = 5485475) B5485475
theorem B2886977 : Blo 1520457 2886977 := bstep (se 2 (by rfl) ⟨1082616, by rfl⟩ : syracuseStep 2886977 = 2165233) B2165233
theorem B2280779 : Blo 1520457 2280779 := bstep (se 1 (by rfl) ⟨1710584, by rfl⟩ : syracuseStep 2280779 = 3421169) B3421169
theorem B2280791 : Blo 1520457 2280791 := bstep (se 1 (by rfl) ⟨1710593, by rfl⟩ : syracuseStep 2280791 = 3421187) B3421187
theorem B2280857 : Blo 1520457 2280857 := bstep (se 2 (by rfl) ⟨855321, by rfl⟩ : syracuseStep 2280857 = 1710643) B1710643
theorem B2567639 : Blo 1520457 2567639 := bstep (se 1 (by rfl) ⟨1925729, by rfl⟩ : syracuseStep 2567639 = 3851459) B3851459
theorem B3247627 : Blo 1520457 3247627 := bstep (se 1 (by rfl) ⟨2435720, by rfl⟩ : syracuseStep 3247627 = 4871441) B4871441
theorem B2280971 : Blo 1520457 2280971 := bstep (se 1 (by rfl) ⟨1710728, by rfl⟩ : syracuseStep 2280971 = 3421457) B3421457
theorem B2280983 : Blo 1520457 2280983 := bstep (se 1 (by rfl) ⟨1710737, by rfl⟩ : syracuseStep 2280983 = 3421475) B3421475
theorem B3706391 : Blo 1520457 3706391 := bstep (se 1 (by rfl) ⟨2779793, by rfl⟩ : syracuseStep 3706391 = 5559587) B5559587
theorem B6499885 : Blo 1520457 6499885 := bstep (se 3 (by rfl) ⟨1218728, by rfl⟩ : syracuseStep 6499885 = 2437457) B2437457
theorem B2567767 : Blo 1520457 2567767 := bstep (se 1 (by rfl) ⟨1925825, by rfl⟩ : syracuseStep 2567767 = 3851651) B3851651
theorem B2281049 : Blo 1520457 2281049 := bstep (se 2 (by rfl) ⟨855393, by rfl⟩ : syracuseStep 2281049 = 1710787) B1710787
theorem B2887319 : Blo 1520457 2887319 := bstep (se 1 (by rfl) ⟨2165489, by rfl⟩ : syracuseStep 2887319 = 4330979) B4330979
theorem B12996247 : Blo 1520457 12996247 := bstep (se 1 (by rfl) ⟨9747185, by rfl⟩ : syracuseStep 12996247 = 19494371) B19494371
theorem B2281163 : Blo 1520457 2281163 := bstep (se 1 (by rfl) ⟨1710872, by rfl⟩ : syracuseStep 2281163 = 3421745) B3421745
theorem B5779147 : Blo 1520457 5779147 := bstep (se 1 (by rfl) ⟨4334360, by rfl⟩ : syracuseStep 5779147 = 8668721) B8668721
theorem B49360589 : Blo 1520457 49360589 := bstep (se 3 (by rfl) ⟨9255110, by rfl⟩ : syracuseStep 49360589 = 18510221) B18510221
theorem B2281175 : Blo 1520457 2281175 := bstep (se 1 (by rfl) ⟨1710881, by rfl⟩ : syracuseStep 2281175 = 3421763) B3421763
theorem B5131997 : Blo 1520457 5131997 := bstep (se 3 (by rfl) ⟨962249, by rfl⟩ : syracuseStep 5131997 = 1924499) B1924499
theorem B2281241 : Blo 1520457 2281241 := bstep (se 2 (by rfl) ⟨855465, by rfl⟩ : syracuseStep 2281241 = 1710931) B1710931
theorem B49475393 : Blo 1520457 49475393 := bstep (se 2 (by rfl) ⟨18553272, by rfl⟩ : syracuseStep 49475393 = 37106545) B37106545
theorem B7704395 : Blo 1520457 7704395 := bstep (se 1 (by rfl) ⟨5778296, by rfl⟩ : syracuseStep 7704395 = 11556593) B11556593
theorem B2281355 : Blo 1520457 2281355 := bstep (se 1 (by rfl) ⟨1711016, by rfl⟩ : syracuseStep 2281355 = 3422033) B3422033
theorem B2281367 : Blo 1520457 2281367 := bstep (se 1 (by rfl) ⟨1711025, by rfl⟩ : syracuseStep 2281367 = 3422051) B3422051
theorem B2166679 : Blo 1520457 2166679 := bstep (se 1 (by rfl) ⟨1625009, by rfl⟩ : syracuseStep 2166679 = 3250019) B3250019
theorem B27774899 : Blo 1520457 27774899 := bstep (se 1 (by rfl) ⟨20831174, by rfl⟩ : syracuseStep 27774899 = 41662349) B41662349
theorem B2281433 : Blo 1520457 2281433 := bstep (se 2 (by rfl) ⟨855537, by rfl⟩ : syracuseStep 2281433 = 1711075) B1711075
theorem B14626777 : Blo 1520457 14626777 := bstep (se 2 (by rfl) ⟨5485041, by rfl⟩ : syracuseStep 14626777 = 10970083) B10970083
theorem B5779421 : Blo 1520457 5779421 := bstep (se 3 (by rfl) ⟨1083641, by rfl⟩ : syracuseStep 5779421 = 2167283) B2167283
theorem B2281547 : Blo 1520457 2281547 := bstep (se 1 (by rfl) ⟨1711160, by rfl⟩ : syracuseStep 2281547 = 3422321) B3422321
theorem B2281559 : Blo 1520457 2281559 := bstep (se 1 (by rfl) ⟨1711169, by rfl⟩ : syracuseStep 2281559 = 3422339) B3422339
theorem B6500483 : Blo 1520457 6500483 := bstep (se 1 (by rfl) ⟨4875362, by rfl⟩ : syracuseStep 6500483 = 9750725) B9750725
theorem B8786051 : Blo 1520457 8786051 := bstep (se 1 (by rfl) ⟨6589538, by rfl⟩ : syracuseStep 8786051 = 13179077) B13179077
theorem B2281625 : Blo 1520457 2281625 := bstep (se 2 (by rfl) ⟨855609, by rfl⟩ : syracuseStep 2281625 = 1711219) B1711219
theorem B2568395 : Blo 1520457 2568395 := bstep (se 1 (by rfl) ⟨1926296, by rfl⟩ : syracuseStep 2568395 = 3852593) B3852593
theorem B2601175 : Blo 1520457 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B3248345 : Blo 1520457 3248345 := bstep (se 2 (by rfl) ⟨1218129, by rfl⟩ : syracuseStep 3248345 = 2436259) B2436259
theorem B2281739 : Blo 1520457 2281739 := bstep (se 1 (by rfl) ⟨1711304, by rfl⟩ : syracuseStep 2281739 = 3422609) B3422609
theorem B2281751 : Blo 1520457 2281751 := bstep (se 1 (by rfl) ⟨1711313, by rfl⟩ : syracuseStep 2281751 = 3422627) B3422627
theorem B2887987 : Blo 1520457 2887987 := bstep (se 1 (by rfl) ⟨2165990, by rfl⟩ : syracuseStep 2887987 = 4331981) B4331981
theorem B2568523 : Blo 1520457 2568523 := bstep (se 1 (by rfl) ⟨1926392, by rfl⟩ : syracuseStep 2568523 = 3852785) B3852785
theorem B2437463 : Blo 1520457 2437463 := bstep (se 1 (by rfl) ⟨1828097, by rfl⟩ : syracuseStep 2437463 = 3656195) B3656195
theorem B2281817 : Blo 1520457 2281817 := bstep (se 2 (by rfl) ⟨855681, by rfl⟩ : syracuseStep 2281817 = 1711363) B1711363
theorem B2281931 : Blo 1520457 2281931 := bstep (se 1 (by rfl) ⟨1711448, by rfl⟩ : syracuseStep 2281931 = 3422897) B3422897
theorem B2281943 : Blo 1520457 2281943 := bstep (se 1 (by rfl) ⟨1711457, by rfl⟩ : syracuseStep 2281943 = 3422915) B3422915
theorem B2568665 : Blo 1520457 2568665 := bstep (se 2 (by rfl) ⟨963249, by rfl⟩ : syracuseStep 2568665 = 1926499) B1926499
theorem B2282009 : Blo 1520457 2282009 := bstep (se 2 (by rfl) ⟨855753, by rfl⟩ : syracuseStep 2282009 = 1711507) B1711507
theorem B8663597 : Blo 1520457 8663597 := bstep (se 3 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 8663597 = 3248849) B3248849
theorem B2568793 : Blo 1520457 2568793 := bstep (se 2 (by rfl) ⟨963297, by rfl⟩ : syracuseStep 2568793 = 1926595) B1926595
theorem B6255197 : Blo 1520457 6255197 := bstep (se 3 (by rfl) ⟨1172849, by rfl⟩ : syracuseStep 6255197 = 2345699) B2345699
theorem B2282123 : Blo 1520457 2282123 := bstep (se 1 (by rfl) ⟨1711592, by rfl⟩ : syracuseStep 2282123 = 3423185) B3423185
theorem B2437771 : Blo 1520457 2437771 := bstep (se 1 (by rfl) ⟨1828328, by rfl⟩ : syracuseStep 2437771 = 3656657) B3656657
theorem B2282135 : Blo 1520457 2282135 := bstep (se 1 (by rfl) ⟨1711601, by rfl⟩ : syracuseStep 2282135 = 3423203) B3423203
theorem B5780119 : Blo 1520457 5780119 := bstep (se 1 (by rfl) ⟨4335089, by rfl⟩ : syracuseStep 5780119 = 8670179) B8670179
theorem B3248857 : Blo 1520457 3248857 := bstep (se 2 (by rfl) ⟨1218321, by rfl⟩ : syracuseStep 3248857 = 2436643) B2436643
theorem B2282201 : Blo 1520457 2282201 := bstep (se 2 (by rfl) ⟨855825, by rfl⟩ : syracuseStep 2282201 = 1711651) B1711651
theorem B2888435 : Blo 1520457 2888435 := bstep (se 1 (by rfl) ⟨2166326, by rfl⟩ : syracuseStep 2888435 = 4332653) B4332653
theorem B2888473 : Blo 1520457 2888473 := bstep (se 2 (by rfl) ⟨1083177, by rfl⟩ : syracuseStep 2888473 = 2166355) B2166355
theorem B12342061 : Blo 1520457 12342061 := bstep (se 3 (by rfl) ⟨2314136, by rfl⟩ : syracuseStep 12342061 = 4628273) B4628273
theorem B1520459 : Blo 1520457 1520459 := bstep (se 1 (by rfl) ⟨1140344, by rfl⟩ : syracuseStep 1520459 = 2280689) B2280689
theorem B5133131 : Blo 1520457 5133131 := bstep (se 1 (by rfl) ⟨3849848, by rfl⟩ : syracuseStep 5133131 = 7699697) B7699697
theorem B2601803 : Blo 1520457 2601803 := bstep (se 1 (by rfl) ⟨1951352, by rfl⟩ : syracuseStep 2601803 = 3902705) B3902705
theorem B2282315 : Blo 1520457 2282315 := bstep (se 1 (by rfl) ⟨1711736, by rfl⟩ : syracuseStep 2282315 = 3423473) B3423473
theorem B1520471 : Blo 1520457 1520471 := bstep (se 1 (by rfl) ⟨1140353, by rfl⟩ : syracuseStep 1520471 = 2280707) B2280707
theorem B2282327 : Blo 1520457 2282327 := bstep (se 1 (by rfl) ⟨1711745, by rfl⟩ : syracuseStep 2282327 = 3423491) B3423491
theorem B8229725 : Blo 1520457 8229725 := bstep (se 3 (by rfl) ⟨1543073, by rfl⟩ : syracuseStep 8229725 = 3086147) B3086147
theorem B1520491 : Blo 1520457 1520491 := bstep (se 1 (by rfl) ⟨1140368, by rfl⟩ : syracuseStep 1520491 = 2280737) B2280737
theorem B3421043 : Blo 1520457 3421043 := bstep (se 1 (by rfl) ⟨2565782, by rfl⟩ : syracuseStep 3421043 = 5131565) B5131565
theorem B3249011 : Blo 1520457 3249011 := bstep (se 1 (by rfl) ⟨2436758, by rfl⟩ : syracuseStep 3249011 = 4873517) B4873517
theorem B1520503 : Blo 1520457 1520503 := bstep (se 1 (by rfl) ⟨1140377, by rfl⟩ : syracuseStep 1520503 = 2280755) B2280755
theorem B1520523 : Blo 1520457 1520523 := bstep (se 1 (by rfl) ⟨1140392, by rfl⟩ : syracuseStep 1520523 = 2280785) B2280785
theorem B2438027 : Blo 1520457 2438027 := bstep (se 1 (by rfl) ⟨1828520, by rfl⟩ : syracuseStep 2438027 = 3657041) B3657041
theorem B3421079 : Blo 1520457 3421079 := bstep (se 1 (by rfl) ⟨2565809, by rfl⟩ : syracuseStep 3421079 = 5131619) B5131619
theorem B1520535 : Blo 1520457 1520535 := bstep (se 1 (by rfl) ⟨1140401, by rfl⟩ : syracuseStep 1520535 = 2280803) B2280803
theorem B2282393 : Blo 1520457 2282393 := bstep (se 2 (by rfl) ⟨855897, by rfl⟩ : syracuseStep 2282393 = 1711795) B1711795
theorem B1520555 : Blo 1520457 1520555 := bstep (se 1 (by rfl) ⟨1140416, by rfl⟩ : syracuseStep 1520555 = 2280833) B2280833
theorem B1520567 : Blo 1520457 1520567 := bstep (se 1 (by rfl) ⟨1140425, by rfl⟩ : syracuseStep 1520567 = 2280851) B2280851
theorem B1520587 : Blo 1520457 1520587 := bstep (se 1 (by rfl) ⟨1140440, by rfl⟩ : syracuseStep 1520587 = 2280881) B2280881
theorem B1520599 : Blo 1520457 1520599 := bstep (se 1 (by rfl) ⟨1140449, by rfl⟩ : syracuseStep 1520599 = 2280899) B2280899
theorem B1520619 : Blo 1520457 1520619 := bstep (se 1 (by rfl) ⟨1140464, by rfl⟩ : syracuseStep 1520619 = 2280929) B2280929
theorem B1520631 : Blo 1520457 1520631 := bstep (se 1 (by rfl) ⟨1140473, by rfl⟩ : syracuseStep 1520631 = 2280947) B2280947
theorem B1520651 : Blo 1520457 1520651 := bstep (se 1 (by rfl) ⟨1140488, by rfl⟩ : syracuseStep 1520651 = 2280977) B2280977
theorem B2282507 : Blo 1520457 2282507 := bstep (se 1 (by rfl) ⟨1711880, by rfl⟩ : syracuseStep 2282507 = 3423761) B3423761
theorem B1520663 : Blo 1520457 1520663 := bstep (se 1 (by rfl) ⟨1140497, by rfl⟩ : syracuseStep 1520663 = 2280995) B2280995
theorem B2282519 : Blo 1520457 2282519 := bstep (se 1 (by rfl) ⟨1711889, by rfl⟩ : syracuseStep 2282519 = 3423779) B3423779
theorem B1520683 : Blo 1520457 1520683 := bstep (se 1 (by rfl) ⟨1140512, by rfl⟩ : syracuseStep 1520683 = 2281025) B2281025
theorem B1520695 : Blo 1520457 1520695 := bstep (se 1 (by rfl) ⟨1140521, by rfl⟩ : syracuseStep 1520695 = 2281043) B2281043
theorem B3421259 : Blo 1520457 3421259 := bstep (se 1 (by rfl) ⟨2565944, by rfl⟩ : syracuseStep 3421259 = 5131889) B5131889
theorem B1520715 : Blo 1520457 1520715 := bstep (se 1 (by rfl) ⟨1140536, by rfl⟩ : syracuseStep 1520715 = 2281073) B2281073
theorem B46822475 : Blo 1520457 46822475 := bstep (se 1 (by rfl) ⟨35116856, by rfl⟩ : syracuseStep 46822475 = 70233713) B70233713
theorem B1520727 : Blo 1520457 1520727 := bstep (se 1 (by rfl) ⟨1140545, by rfl⟩ : syracuseStep 1520727 = 2281091) B2281091
theorem B5133401 : Blo 1520457 5133401 := bstep (se 2 (by rfl) ⟨1925025, by rfl⟩ : syracuseStep 5133401 = 3850051) B3850051
theorem B2282585 : Blo 1520457 2282585 := bstep (se 2 (by rfl) ⟨855969, by rfl⟩ : syracuseStep 2282585 = 1711939) B1711939
theorem B1520747 : Blo 1520457 1520747 := bstep (se 1 (by rfl) ⟨1140560, by rfl⟩ : syracuseStep 1520747 = 2281121) B2281121
theorem B3085427 : Blo 1520457 3085427 := bstep (se 1 (by rfl) ⟨2314070, by rfl⟩ : syracuseStep 3085427 = 4628141) B4628141
theorem B1520759 : Blo 1520457 1520759 := bstep (se 1 (by rfl) ⟨1140569, by rfl⟩ : syracuseStep 1520759 = 2281139) B2281139
theorem B3421313 : Blo 1520457 3421313 := bstep (se 2 (by rfl) ⟨1282992, by rfl⟩ : syracuseStep 3421313 = 2565985) B2565985
theorem B1520779 : Blo 1520457 1520779 := bstep (se 1 (by rfl) ⟨1140584, by rfl⟩ : syracuseStep 1520779 = 2281169) B2281169
theorem B1520791 : Blo 1520457 1520791 := bstep (se 1 (by rfl) ⟨1140593, by rfl⟩ : syracuseStep 1520791 = 2281187) B2281187
theorem B1520811 : Blo 1520457 1520811 := bstep (se 1 (by rfl) ⟨1140608, by rfl⟩ : syracuseStep 1520811 = 2281217) B2281217
theorem B6165677 : Blo 1520457 6165677 := bstep (se 3 (by rfl) ⟨1156064, by rfl⟩ : syracuseStep 6165677 = 2312129) B2312129
theorem B1520823 : Blo 1520457 1520823 := bstep (se 1 (by rfl) ⟨1140617, by rfl⟩ : syracuseStep 1520823 = 2281235) B2281235
theorem B1520843 : Blo 1520457 1520843 := bstep (se 1 (by rfl) ⟨1140632, by rfl⟩ : syracuseStep 1520843 = 2281265) B2281265
theorem B2282699 : Blo 1520457 2282699 := bstep (se 1 (by rfl) ⟨1712024, by rfl⟩ : syracuseStep 2282699 = 3424049) B3424049
theorem B1520855 : Blo 1520457 1520855 := bstep (se 1 (by rfl) ⟨1140641, by rfl⟩ : syracuseStep 1520855 = 2281283) B2281283
theorem B2282711 : Blo 1520457 2282711 := bstep (se 1 (by rfl) ⟨1712033, by rfl⟩ : syracuseStep 2282711 = 3424067) B3424067
theorem B2888921 : Blo 1520457 2888921 := bstep (se 2 (by rfl) ⟨1083345, by rfl⟩ : syracuseStep 2888921 = 2166691) B2166691
theorem B6943961 : Blo 1520457 6943961 := bstep (se 2 (by rfl) ⟨2603985, by rfl⟩ : syracuseStep 6943961 = 5207971) B5207971
theorem B1520875 : Blo 1520457 1520875 := bstep (se 1 (by rfl) ⟨1140656, by rfl⟩ : syracuseStep 1520875 = 2281313) B2281313
theorem B1520887 : Blo 1520457 1520887 := bstep (se 1 (by rfl) ⟨1140665, by rfl⟩ : syracuseStep 1520887 = 2281331) B2281331
theorem B1520907 : Blo 1520457 1520907 := bstep (se 1 (by rfl) ⟨1140680, by rfl⟩ : syracuseStep 1520907 = 2281361) B2281361
theorem B1520919 : Blo 1520457 1520919 := bstep (se 1 (by rfl) ⟨1140689, by rfl⟩ : syracuseStep 1520919 = 2281379) B2281379
theorem B2282777 : Blo 1520457 2282777 := bstep (se 2 (by rfl) ⟨856041, by rfl⟩ : syracuseStep 2282777 = 1712083) B1712083
theorem B1520939 : Blo 1520457 1520939 := bstep (se 1 (by rfl) ⟨1140704, by rfl⟩ : syracuseStep 1520939 = 2281409) B2281409
theorem B6255917 : Blo 1520457 6255917 := bstep (se 3 (by rfl) ⟨1172984, by rfl⟩ : syracuseStep 6255917 = 2345969) B2345969
theorem B1520951 : Blo 1520457 1520951 := bstep (se 1 (by rfl) ⟨1140713, by rfl⟩ : syracuseStep 1520951 = 2281427) B2281427
theorem B11113793 : Blo 1520457 11113793 := bstep (se 2 (by rfl) ⟨4167672, by rfl⟩ : syracuseStep 11113793 = 8335345) B8335345
theorem B10966337 : Blo 1520457 10966337 := bstep (se 2 (by rfl) ⟨4112376, by rfl⟩ : syracuseStep 10966337 = 8224753) B8224753
theorem B1520971 : Blo 1520457 1520971 := bstep (se 1 (by rfl) ⟨1140728, by rfl⟩ : syracuseStep 1520971 = 2281457) B2281457
theorem B1520983 : Blo 1520457 1520983 := bstep (se 1 (by rfl) ⟨1140737, by rfl⟩ : syracuseStep 1520983 = 2281475) B2281475
theorem B3421529 : Blo 1520457 3421529 := bstep (se 2 (by rfl) ⟨1283073, by rfl⟩ : syracuseStep 3421529 = 2566147) B2566147
theorem B1521003 : Blo 1520457 1521003 := bstep (se 1 (by rfl) ⟨1140752, by rfl⟩ : syracuseStep 1521003 = 2281505) B2281505
theorem B1521015 : Blo 1520457 1521015 := bstep (se 1 (by rfl) ⟨1140761, by rfl⟩ : syracuseStep 1521015 = 2281523) B2281523
theorem B1521035 : Blo 1520457 1521035 := bstep (se 1 (by rfl) ⟨1140776, by rfl⟩ : syracuseStep 1521035 = 2281553) B2281553
theorem B2282891 : Blo 1520457 2282891 := bstep (se 1 (by rfl) ⟨1712168, by rfl⟩ : syracuseStep 2282891 = 3424337) B3424337
theorem B1521047 : Blo 1520457 1521047 := bstep (se 1 (by rfl) ⟨1140785, by rfl⟩ : syracuseStep 1521047 = 2281571) B2281571
theorem B2282903 : Blo 1520457 2282903 := bstep (se 1 (by rfl) ⟨1712177, by rfl⟩ : syracuseStep 2282903 = 3424355) B3424355
theorem B1521067 : Blo 1520457 1521067 := bstep (se 1 (by rfl) ⟨1140800, by rfl⟩ : syracuseStep 1521067 = 2281601) B2281601
theorem B13170097 : Blo 1520457 13170097 := bstep (se 2 (by rfl) ⟨4938786, by rfl⟩ : syracuseStep 13170097 = 9877573) B9877573
theorem B3421619 : Blo 1520457 3421619 := bstep (se 1 (by rfl) ⟨2566214, by rfl⟩ : syracuseStep 3421619 = 5132429) B5132429
theorem B1521079 : Blo 1520457 1521079 := bstep (se 1 (by rfl) ⟨1140809, by rfl⟩ : syracuseStep 1521079 = 2281619) B2281619
theorem B1521099 : Blo 1520457 1521099 := bstep (se 1 (by rfl) ⟨1140824, by rfl⟩ : syracuseStep 1521099 = 2281649) B2281649
theorem B3421655 : Blo 1520457 3421655 := bstep (se 1 (by rfl) ⟨2566241, by rfl⟩ : syracuseStep 3421655 = 5132483) B5132483
theorem B1521111 : Blo 1520457 1521111 := bstep (se 1 (by rfl) ⟨1140833, by rfl⟩ : syracuseStep 1521111 = 2281667) B2281667
theorem B2282969 : Blo 1520457 2282969 := bstep (se 2 (by rfl) ⟨856113, by rfl⟩ : syracuseStep 2282969 = 1712227) B1712227
theorem B1521131 : Blo 1520457 1521131 := bstep (se 1 (by rfl) ⟨1140848, by rfl⟩ : syracuseStep 1521131 = 2281697) B2281697
theorem B1521143 : Blo 1520457 1521143 := bstep (se 1 (by rfl) ⟨1140857, by rfl⟩ : syracuseStep 1521143 = 2281715) B2281715
theorem B1521163 : Blo 1520457 1521163 := bstep (se 1 (by rfl) ⟨1140872, by rfl⟩ : syracuseStep 1521163 = 2281745) B2281745
theorem B1521175 : Blo 1520457 1521175 := bstep (se 1 (by rfl) ⟨1140881, by rfl⟩ : syracuseStep 1521175 = 2281763) B2281763
theorem B1521195 : Blo 1520457 1521195 := bstep (se 1 (by rfl) ⟨1140896, by rfl⟩ : syracuseStep 1521195 = 2281793) B2281793
theorem B9754157 : Blo 1520457 9754157 := bstep (se 3 (by rfl) ⟨1828904, by rfl⟩ : syracuseStep 9754157 = 3657809) B3657809
theorem B1521207 : Blo 1520457 1521207 := bstep (se 1 (by rfl) ⟨1140905, by rfl⟩ : syracuseStep 1521207 = 2281811) B2281811
theorem B7411265 : Blo 1520457 7411265 := bstep (se 2 (by rfl) ⟨2779224, by rfl⟩ : syracuseStep 7411265 = 5558449) B5558449
theorem B7706177 : Blo 1520457 7706177 := bstep (se 2 (by rfl) ⟨2889816, by rfl⟩ : syracuseStep 7706177 = 5779633) B5779633
theorem B1521227 : Blo 1520457 1521227 := bstep (se 1 (by rfl) ⟨1140920, by rfl⟩ : syracuseStep 1521227 = 2281841) B2281841
theorem B2283083 : Blo 1520457 2283083 := bstep (se 1 (by rfl) ⟨1712312, by rfl⟩ : syracuseStep 2283083 = 3424625) B3424625
theorem B166581845 : Blo 1520457 166581845 := bstep (se 8 (by rfl) ⟨976065, by rfl⟩ : syracuseStep 166581845 = 1952131) B1952131
theorem B1521239 : Blo 1520457 1521239 := bstep (se 1 (by rfl) ⟨1140929, by rfl⟩ : syracuseStep 1521239 = 2281859) B2281859
theorem B2283095 : Blo 1520457 2283095 := bstep (se 1 (by rfl) ⟨1712321, by rfl⟩ : syracuseStep 2283095 = 3424643) B3424643
theorem B1521259 : Blo 1520457 1521259 := bstep (se 1 (by rfl) ⟨1140944, by rfl⟩ : syracuseStep 1521259 = 2281889) B2281889
theorem B1521271 : Blo 1520457 1521271 := bstep (se 1 (by rfl) ⟨1140953, by rfl⟩ : syracuseStep 1521271 = 2281907) B2281907
theorem B3421835 : Blo 1520457 3421835 := bstep (se 1 (by rfl) ⟨2566376, by rfl⟩ : syracuseStep 3421835 = 5132753) B5132753
theorem B1521291 : Blo 1520457 1521291 := bstep (se 1 (by rfl) ⟨1140968, by rfl⟩ : syracuseStep 1521291 = 2281937) B2281937
theorem B1521303 : Blo 1520457 1521303 := bstep (se 1 (by rfl) ⟨1140977, by rfl⟩ : syracuseStep 1521303 = 2281955) B2281955
theorem B2283161 : Blo 1520457 2283161 := bstep (se 2 (by rfl) ⟨856185, by rfl⟩ : syracuseStep 2283161 = 1712371) B1712371
theorem B1521323 : Blo 1520457 1521323 := bstep (se 1 (by rfl) ⟨1140992, by rfl⟩ : syracuseStep 1521323 = 2281985) B2281985
theorem B1521335 : Blo 1520457 1521335 := bstep (se 1 (by rfl) ⟨1141001, by rfl⟩ : syracuseStep 1521335 = 2282003) B2282003
theorem B3421889 : Blo 1520457 3421889 := bstep (se 2 (by rfl) ⟨1283208, by rfl⟩ : syracuseStep 3421889 = 2566417) B2566417
theorem B1521355 : Blo 1520457 1521355 := bstep (se 1 (by rfl) ⟨1141016, by rfl⟩ : syracuseStep 1521355 = 2282033) B2282033
theorem B1521367 : Blo 1520457 1521367 := bstep (se 1 (by rfl) ⟨1141025, by rfl⟩ : syracuseStep 1521367 = 2282051) B2282051
theorem B1521387 : Blo 1520457 1521387 := bstep (se 1 (by rfl) ⟨1141040, by rfl⟩ : syracuseStep 1521387 = 2282081) B2282081
theorem B1521399 : Blo 1520457 1521399 := bstep (se 1 (by rfl) ⟨1141049, by rfl⟩ : syracuseStep 1521399 = 2282099) B2282099
theorem B1521419 : Blo 1520457 1521419 := bstep (se 1 (by rfl) ⟨1141064, by rfl⟩ : syracuseStep 1521419 = 2282129) B2282129
theorem B2283275 : Blo 1520457 2283275 := bstep (se 1 (by rfl) ⟨1712456, by rfl⟩ : syracuseStep 2283275 = 3424913) B3424913
theorem B5134103 : Blo 1520457 5134103 := bstep (se 1 (by rfl) ⟨3850577, by rfl⟩ : syracuseStep 5134103 = 7701155) B7701155
theorem B1521431 : Blo 1520457 1521431 := bstep (se 1 (by rfl) ⟨1141073, by rfl⟩ : syracuseStep 1521431 = 2282147) B2282147
theorem B2283287 : Blo 1520457 2283287 := bstep (se 1 (by rfl) ⟨1712465, by rfl⟩ : syracuseStep 2283287 = 3424931) B3424931
theorem B1521451 : Blo 1520457 1521451 := bstep (se 1 (by rfl) ⟨1141088, by rfl⟩ : syracuseStep 1521451 = 2282177) B2282177
theorem B1521463 : Blo 1520457 1521463 := bstep (se 1 (by rfl) ⟨1141097, by rfl⟩ : syracuseStep 1521463 = 2282195) B2282195
theorem B3249985 : Blo 1520457 3249985 := bstep (se 2 (by rfl) ⟨1218744, by rfl⟩ : syracuseStep 3249985 = 2437489) B2437489
theorem B1521483 : Blo 1520457 1521483 := bstep (se 1 (by rfl) ⟨1141112, by rfl⟩ : syracuseStep 1521483 = 2282225) B2282225
theorem B1521495 : Blo 1520457 1521495 := bstep (se 1 (by rfl) ⟨1141121, by rfl⟩ : syracuseStep 1521495 = 2282243) B2282243
theorem B2283353 : Blo 1520457 2283353 := bstep (se 2 (by rfl) ⟨856257, by rfl⟩ : syracuseStep 2283353 = 1712515) B1712515
theorem B1521515 : Blo 1520457 1521515 := bstep (se 1 (by rfl) ⟨1141136, by rfl⟩ : syracuseStep 1521515 = 2282273) B2282273
theorem B1521527 : Blo 1520457 1521527 := bstep (se 1 (by rfl) ⟨1141145, by rfl⟩ : syracuseStep 1521527 = 2282291) B2282291
theorem B1521547 : Blo 1520457 1521547 := bstep (se 1 (by rfl) ⟨1141160, by rfl⟩ : syracuseStep 1521547 = 2282321) B2282321
theorem B1521559 : Blo 1520457 1521559 := bstep (se 1 (by rfl) ⟨1141169, by rfl⟩ : syracuseStep 1521559 = 2282339) B2282339
theorem B3422105 : Blo 1520457 3422105 := bstep (se 2 (by rfl) ⟨1283289, by rfl⟩ : syracuseStep 3422105 = 2566579) B2566579
theorem B1521579 : Blo 1520457 1521579 := bstep (se 1 (by rfl) ⟨1141184, by rfl⟩ : syracuseStep 1521579 = 2282369) B2282369
theorem B17323955 : Blo 1520457 17323955 := bstep (se 1 (by rfl) ⟨12992966, by rfl⟩ : syracuseStep 17323955 = 25985933) B25985933
theorem B1521591 : Blo 1520457 1521591 := bstep (se 1 (by rfl) ⟨1141193, by rfl⟩ : syracuseStep 1521591 = 2282387) B2282387
theorem B2889665 : Blo 1520457 2889665 := bstep (se 2 (by rfl) ⟨1083624, by rfl⟩ : syracuseStep 2889665 = 2167249) B2167249
theorem B1521611 : Blo 1520457 1521611 := bstep (se 1 (by rfl) ⟨1141208, by rfl⟩ : syracuseStep 1521611 = 2282417) B2282417
theorem B2283467 : Blo 1520457 2283467 := bstep (se 1 (by rfl) ⟨1712600, by rfl⟩ : syracuseStep 2283467 = 3425201) B3425201
theorem B1521623 : Blo 1520457 1521623 := bstep (se 1 (by rfl) ⟨1141217, by rfl⟩ : syracuseStep 1521623 = 2282435) B2282435
theorem B2283479 : Blo 1520457 2283479 := bstep (se 1 (by rfl) ⟨1712609, by rfl⟩ : syracuseStep 2283479 = 3425219) B3425219
theorem B1521643 : Blo 1520457 1521643 := bstep (se 1 (by rfl) ⟨1141232, by rfl⟩ : syracuseStep 1521643 = 2282465) B2282465
theorem B3422195 : Blo 1520457 3422195 := bstep (se 1 (by rfl) ⟨2566646, by rfl⟩ : syracuseStep 3422195 = 5133293) B5133293
theorem B1521655 : Blo 1520457 1521655 := bstep (se 1 (by rfl) ⟨1141241, by rfl⟩ : syracuseStep 1521655 = 2282483) B2282483
theorem B5773315 : Blo 1520457 5773315 := bstep (se 1 (by rfl) ⟨4329986, by rfl⟩ : syracuseStep 5773315 = 8659973) B8659973
theorem B1521675 : Blo 1520457 1521675 := bstep (se 1 (by rfl) ⟨1141256, by rfl⟩ : syracuseStep 1521675 = 2282513) B2282513
theorem B3422231 : Blo 1520457 3422231 := bstep (se 1 (by rfl) ⟨2566673, by rfl⟩ : syracuseStep 3422231 = 5133347) B5133347
theorem B1521687 : Blo 1520457 1521687 := bstep (se 1 (by rfl) ⟨1141265, by rfl⟩ : syracuseStep 1521687 = 2282531) B2282531
theorem B2283545 : Blo 1520457 2283545 := bstep (se 2 (by rfl) ⟨856329, by rfl⟩ : syracuseStep 2283545 = 1712659) B1712659
theorem B1521707 : Blo 1520457 1521707 := bstep (se 1 (by rfl) ⟨1141280, by rfl⟩ : syracuseStep 1521707 = 2282561) B2282561
theorem B1521719 : Blo 1520457 1521719 := bstep (se 1 (by rfl) ⟨1141289, by rfl⟩ : syracuseStep 1521719 = 2282579) B2282579
theorem B1521739 : Blo 1520457 1521739 := bstep (se 1 (by rfl) ⟨1141304, by rfl⟩ : syracuseStep 1521739 = 2282609) B2282609
theorem B1521751 : Blo 1520457 1521751 := bstep (se 1 (by rfl) ⟨1141313, by rfl⟩ : syracuseStep 1521751 = 2282627) B2282627
theorem B1521771 : Blo 1520457 1521771 := bstep (se 1 (by rfl) ⟨1141328, by rfl⟩ : syracuseStep 1521771 = 2282657) B2282657
theorem B1521783 : Blo 1520457 1521783 := bstep (se 1 (by rfl) ⟨1141337, by rfl⟩ : syracuseStep 1521783 = 2282675) B2282675
theorem B7698563 : Blo 1520457 7698563 := bstep (se 1 (by rfl) ⟨5773922, by rfl⟩ : syracuseStep 7698563 = 11547845) B11547845
theorem B1521803 : Blo 1520457 1521803 := bstep (se 1 (by rfl) ⟨1141352, by rfl⟩ : syracuseStep 1521803 = 2282705) B2282705
theorem B2283659 : Blo 1520457 2283659 := bstep (se 1 (by rfl) ⟨1712744, by rfl⟩ : syracuseStep 2283659 = 3425489) B3425489
theorem B1521815 : Blo 1520457 1521815 := bstep (se 1 (by rfl) ⟨1141361, by rfl⟩ : syracuseStep 1521815 = 2282723) B2282723
theorem B3250327 : Blo 1520457 3250327 := bstep (se 1 (by rfl) ⟨2437745, by rfl⟩ : syracuseStep 3250327 = 4875491) B4875491
theorem B2283671 : Blo 1520457 2283671 := bstep (se 1 (by rfl) ⟨1712753, by rfl⟩ : syracuseStep 2283671 = 3425507) B3425507
theorem B1521835 : Blo 1520457 1521835 := bstep (se 1 (by rfl) ⟨1141376, by rfl⟩ : syracuseStep 1521835 = 2282753) B2282753
theorem B1521847 : Blo 1520457 1521847 := bstep (se 1 (by rfl) ⟨1141385, by rfl⟩ : syracuseStep 1521847 = 2282771) B2282771
theorem B5208257 : Blo 1520457 5208257 := bstep (se 2 (by rfl) ⟨1953096, by rfl⟩ : syracuseStep 5208257 = 3906193) B3906193
theorem B3422411 : Blo 1520457 3422411 := bstep (se 1 (by rfl) ⟨2566808, by rfl⟩ : syracuseStep 3422411 = 5133617) B5133617
theorem B1521867 : Blo 1520457 1521867 := bstep (se 1 (by rfl) ⟨1141400, by rfl⟩ : syracuseStep 1521867 = 2282801) B2282801
theorem B2889931 : Blo 1520457 2889931 := bstep (se 1 (by rfl) ⟨2167448, by rfl⟩ : syracuseStep 2889931 = 4334897) B4334897
theorem B1521879 : Blo 1520457 1521879 := bstep (se 1 (by rfl) ⟨1141409, by rfl⟩ : syracuseStep 1521879 = 2282819) B2282819
theorem B1521899 : Blo 1520457 1521899 := bstep (se 1 (by rfl) ⟨1141424, by rfl⟩ : syracuseStep 1521899 = 2282849) B2282849
theorem B1521911 : Blo 1520457 1521911 := bstep (se 1 (by rfl) ⟨1141433, by rfl⟩ : syracuseStep 1521911 = 2282867) B2282867
theorem B3422465 : Blo 1520457 3422465 := bstep (se 2 (by rfl) ⟨1283424, by rfl⟩ : syracuseStep 3422465 = 2566849) B2566849
theorem B1521931 : Blo 1520457 1521931 := bstep (se 1 (by rfl) ⟨1141448, by rfl⟩ : syracuseStep 1521931 = 2282897) B2282897
theorem B1521943 : Blo 1520457 1521943 := bstep (se 1 (by rfl) ⟨1141457, by rfl⟩ : syracuseStep 1521943 = 2282915) B2282915
theorem B1521963 : Blo 1520457 1521963 := bstep (se 1 (by rfl) ⟨1141472, by rfl⟩ : syracuseStep 1521963 = 2282945) B2282945
theorem B5773619 : Blo 1520457 5773619 := bstep (se 1 (by rfl) ⟨4330214, by rfl⟩ : syracuseStep 5773619 = 8660429) B8660429
theorem B5134643 : Blo 1520457 5134643 := bstep (se 1 (by rfl) ⟨3850982, by rfl⟩ : syracuseStep 5134643 = 7701965) B7701965
theorem B1521975 : Blo 1520457 1521975 := bstep (se 1 (by rfl) ⟨1141481, by rfl⟩ : syracuseStep 1521975 = 2282963) B2282963
theorem B1521995 : Blo 1520457 1521995 := bstep (se 1 (by rfl) ⟨1141496, by rfl⟩ : syracuseStep 1521995 = 2282993) B2282993
theorem B1522007 : Blo 1520457 1522007 := bstep (se 1 (by rfl) ⟨1141505, by rfl⟩ : syracuseStep 1522007 = 2283011) B2283011
theorem B1522027 : Blo 1520457 1522027 := bstep (se 1 (by rfl) ⟨1141520, by rfl⟩ : syracuseStep 1522027 = 2283041) B2283041
theorem B1522039 : Blo 1520457 1522039 := bstep (se 1 (by rfl) ⟨1141529, by rfl⟩ : syracuseStep 1522039 = 2283059) B2283059
theorem B1522059 : Blo 1520457 1522059 := bstep (se 1 (by rfl) ⟨1141544, by rfl⟩ : syracuseStep 1522059 = 2283089) B2283089
theorem B1522071 : Blo 1520457 1522071 := bstep (se 1 (by rfl) ⟨1141553, by rfl⟩ : syracuseStep 1522071 = 2283107) B2283107
theorem B1522091 : Blo 1520457 1522091 := bstep (se 1 (by rfl) ⟨1141568, by rfl⟩ : syracuseStep 1522091 = 2283137) B2283137
theorem B1522103 : Blo 1520457 1522103 := bstep (se 1 (by rfl) ⟨1141577, by rfl⟩ : syracuseStep 1522103 = 2283155) B2283155
theorem B1522123 : Blo 1520457 1522123 := bstep (se 1 (by rfl) ⟨1141592, by rfl⟩ : syracuseStep 1522123 = 2283185) B2283185
theorem B1522135 : Blo 1520457 1522135 := bstep (se 1 (by rfl) ⟨1141601, by rfl⟩ : syracuseStep 1522135 = 2283203) B2283203
theorem B3422681 : Blo 1520457 3422681 := bstep (se 2 (by rfl) ⟨1283505, by rfl⟩ : syracuseStep 3422681 = 2567011) B2567011
theorem B1710571 : Blo 1520457 1710571 := bstep (se 1 (by rfl) ⟨1282928, by rfl⟩ : syracuseStep 1710571 = 2565857) B2565857
theorem B1522155 : Blo 1520457 1522155 := bstep (se 1 (by rfl) ⟨1141616, by rfl⟩ : syracuseStep 1522155 = 2283233) B2283233
theorem B1522167 : Blo 1520457 1522167 := bstep (se 1 (by rfl) ⟨1141625, by rfl⟩ : syracuseStep 1522167 = 2283251) B2283251
theorem B1522187 : Blo 1520457 1522187 := bstep (se 1 (by rfl) ⟨1141640, by rfl⟩ : syracuseStep 1522187 = 2283281) B2283281
theorem B1522199 : Blo 1520457 1522199 := bstep (se 1 (by rfl) ⟨1141649, by rfl⟩ : syracuseStep 1522199 = 2283299) B2283299
theorem B1522219 : Blo 1520457 1522219 := bstep (se 1 (by rfl) ⟨1141664, by rfl⟩ : syracuseStep 1522219 = 2283329) B2283329
theorem B3848755 : Blo 1520457 3848755 := bstep (se 1 (by rfl) ⟨2886566, by rfl⟩ : syracuseStep 3848755 = 5773133) B5773133
theorem B3422771 : Blo 1520457 3422771 := bstep (se 1 (by rfl) ⟨2567078, by rfl⟩ : syracuseStep 3422771 = 5134157) B5134157
theorem B1522231 : Blo 1520457 1522231 := bstep (se 1 (by rfl) ⟨1141673, by rfl⟩ : syracuseStep 1522231 = 2283347) B2283347
theorem B5134913 : Blo 1520457 5134913 := bstep (se 2 (by rfl) ⟨1925592, by rfl⟩ : syracuseStep 5134913 = 3851185) B3851185
theorem B3250763 : Blo 1520457 3250763 := bstep (se 1 (by rfl) ⟨2438072, by rfl⟩ : syracuseStep 3250763 = 4876145) B4876145
theorem B1522251 : Blo 1520457 1522251 := bstep (se 1 (by rfl) ⟨1141688, by rfl⟩ : syracuseStep 1522251 = 2283377) B2283377
theorem B1710679 : Blo 1520457 1710679 := bstep (se 1 (by rfl) ⟨1283009, by rfl⟩ : syracuseStep 1710679 = 2566019) B2566019
theorem B3422807 : Blo 1520457 3422807 := bstep (se 1 (by rfl) ⟨2567105, by rfl⟩ : syracuseStep 3422807 = 5134211) B5134211
theorem B1522263 : Blo 1520457 1522263 := bstep (se 1 (by rfl) ⟨1141697, by rfl⟩ : syracuseStep 1522263 = 2283395) B2283395
theorem B1522283 : Blo 1520457 1522283 := bstep (se 1 (by rfl) ⟨1141712, by rfl⟩ : syracuseStep 1522283 = 2283425) B2283425
theorem B1522295 : Blo 1520457 1522295 := bstep (se 1 (by rfl) ⟨1141721, by rfl⟩ : syracuseStep 1522295 = 2283443) B2283443
theorem B1522315 : Blo 1520457 1522315 := bstep (se 1 (by rfl) ⟨1141736, by rfl⟩ : syracuseStep 1522315 = 2283473) B2283473
theorem B1522327 : Blo 1520457 1522327 := bstep (se 1 (by rfl) ⟨1141745, by rfl⟩ : syracuseStep 1522327 = 2283491) B2283491
theorem B1522347 : Blo 1520457 1522347 := bstep (se 1 (by rfl) ⟨1141760, by rfl⟩ : syracuseStep 1522347 = 2283521) B2283521
theorem B1522359 : Blo 1520457 1522359 := bstep (se 1 (by rfl) ⟨1141769, by rfl⟩ : syracuseStep 1522359 = 2283539) B2283539
theorem B3848897 : Blo 1520457 3848897 := bstep (se 2 (by rfl) ⟨1443336, by rfl⟩ : syracuseStep 3848897 = 2886673) B2886673
theorem B1522379 : Blo 1520457 1522379 := bstep (se 1 (by rfl) ⟨1141784, by rfl⟩ : syracuseStep 1522379 = 2283569) B2283569
theorem B1522391 : Blo 1520457 1522391 := bstep (se 1 (by rfl) ⟨1141793, by rfl⟩ : syracuseStep 1522391 = 2283587) B2283587
theorem B1522411 : Blo 1520457 1522411 := bstep (se 1 (by rfl) ⟨1141808, by rfl⟩ : syracuseStep 1522411 = 2283617) B2283617
theorem B1522423 : Blo 1520457 1522423 := bstep (se 1 (by rfl) ⟨1141817, by rfl⟩ : syracuseStep 1522423 = 2283635) B2283635
theorem B1710859 : Blo 1520457 1710859 := bstep (se 1 (by rfl) ⟨1283144, by rfl⟩ : syracuseStep 1710859 = 2566289) B2566289
theorem B3422987 : Blo 1520457 3422987 := bstep (se 1 (by rfl) ⟨2567240, by rfl⟩ : syracuseStep 3422987 = 5134481) B5134481
theorem B1522443 : Blo 1520457 1522443 := bstep (se 1 (by rfl) ⟨1141832, by rfl⟩ : syracuseStep 1522443 = 2283665) B2283665
theorem B4332311 : Blo 1520457 4332311 := bstep (se 1 (by rfl) ⟨3249233, by rfl⟩ : syracuseStep 4332311 = 6498467) B6498467
theorem B1522455 : Blo 1520457 1522455 := bstep (se 1 (by rfl) ⟨1141841, by rfl⟩ : syracuseStep 1522455 = 2283683) B2283683
theorem B3472153 : Blo 1520457 3472153 := bstep (se 2 (by rfl) ⟨1302057, by rfl⟩ : syracuseStep 3472153 = 2604115) B2604115
theorem B3423041 : Blo 1520457 3423041 := bstep (se 2 (by rfl) ⟨1283640, by rfl⟩ : syracuseStep 3423041 = 2567281) B2567281
theorem B1710967 : Blo 1520457 1710967 := bstep (se 1 (by rfl) ⟨1283225, by rfl⟩ : syracuseStep 1710967 = 2566451) B2566451
theorem B8665987 : Blo 1520457 8665987 := bstep (se 1 (by rfl) ⟨6499490, by rfl⟩ : syracuseStep 8665987 = 12998981) B12998981
theorem B5774273 : Blo 1520457 5774273 := bstep (se 2 (by rfl) ⟨2165352, by rfl⟩ : syracuseStep 5774273 = 4330705) B4330705
theorem B10959877 : Blo 1520457 10959877 := bstep (se 4 (by rfl) ⟨1027488, by rfl⟩ : syracuseStep 10959877 = 2054977) B2054977
theorem B3423257 : Blo 1520457 3423257 := bstep (se 2 (by rfl) ⟨1283721, by rfl⟩ : syracuseStep 3423257 = 2567443) B2567443
theorem B1711147 : Blo 1520457 1711147 := bstep (se 1 (by rfl) ⟨1283360, by rfl⟩ : syracuseStep 1711147 = 2566721) B2566721
theorem B19496011 : Blo 1520457 19496011 := bstep (se 1 (by rfl) ⟨14622008, by rfl⟩ : syracuseStep 19496011 = 29244017) B29244017
theorem B11549789 : Blo 1520457 11549789 := bstep (se 3 (by rfl) ⟨2165585, by rfl⟩ : syracuseStep 11549789 = 4331171) B4331171
theorem B5135453 : Blo 1520457 5135453 := bstep (se 3 (by rfl) ⟨962897, by rfl⟩ : syracuseStep 5135453 = 1925795) B1925795
theorem B3423347 : Blo 1520457 3423347 := bstep (se 1 (by rfl) ⟨2567510, by rfl⟩ : syracuseStep 3423347 = 5135021) B5135021
theorem B1711255 : Blo 1520457 1711255 := bstep (se 1 (by rfl) ⟨1283441, by rfl⟩ : syracuseStep 1711255 = 2566883) B2566883
theorem B3423383 : Blo 1520457 3423383 := bstep (se 1 (by rfl) ⟨2567537, by rfl⟩ : syracuseStep 3423383 = 5135075) B5135075
theorem B10960049 : Blo 1520457 10960049 := bstep (se 2 (by rfl) ⟨4110018, by rfl⟩ : syracuseStep 10960049 = 8220037) B8220037
theorem B6495511 : Blo 1520457 6495511 := bstep (se 1 (by rfl) ⟨4871633, by rfl⟩ : syracuseStep 6495511 = 9743267) B9743267
theorem B1711435 : Blo 1520457 1711435 := bstep (se 1 (by rfl) ⟨1283576, by rfl⟩ : syracuseStep 1711435 = 2567153) B2567153
theorem B3423563 : Blo 1520457 3423563 := bstep (se 1 (by rfl) ⟨2567672, by rfl⟩ : syracuseStep 3423563 = 5135345) B5135345
theorem B17325413 : Blo 1520457 17325413 := bstep (se 4 (by rfl) ⟨1624257, by rfl⟩ : syracuseStep 17325413 = 3248515) B3248515
theorem B3423617 : Blo 1520457 3423617 := bstep (se 2 (by rfl) ⟨1283856, by rfl⟩ : syracuseStep 3423617 = 2567713) B2567713
theorem B1711543 : Blo 1520457 1711543 := bstep (se 1 (by rfl) ⟨1283657, by rfl⟩ : syracuseStep 1711543 = 2567315) B2567315
theorem B1924555 : Blo 1520457 1924555 := bstep (se 1 (by rfl) ⟨1443416, by rfl⟩ : syracuseStep 1924555 = 2886833) B2886833
theorem B3423833 : Blo 1520457 3423833 := bstep (se 2 (by rfl) ⟨1283937, by rfl⟩ : syracuseStep 3423833 = 2567875) B2567875
theorem B1711723 : Blo 1520457 1711723 := bstep (se 1 (by rfl) ⟨1283792, by rfl⟩ : syracuseStep 1711723 = 2567585) B2567585
theorem B3423923 : Blo 1520457 3423923 := bstep (se 1 (by rfl) ⟨2567942, by rfl⟩ : syracuseStep 3423923 = 5135885) B5135885
theorem B1924823 : Blo 1520457 1924823 := bstep (se 1 (by rfl) ⟨1443617, by rfl⟩ : syracuseStep 1924823 = 2887235) B2887235
theorem B1711831 : Blo 1520457 1711831 := bstep (se 1 (by rfl) ⟨1283873, by rfl⟩ : syracuseStep 1711831 = 2567747) B2567747
theorem B3423959 : Blo 1520457 3423959 := bstep (se 1 (by rfl) ⟨2567969, by rfl⟩ : syracuseStep 3423959 = 5135939) B5135939
theorem B8666945 : Blo 1520457 8666945 := bstep (se 2 (by rfl) ⟨3250104, by rfl⟩ : syracuseStep 8666945 = 6500209) B6500209
theorem B24665957 : Blo 1520457 24665957 := bstep (se 4 (by rfl) ⟨2312433, by rfl⟩ : syracuseStep 24665957 = 4624867) B4624867
theorem B1712011 : Blo 1520457 1712011 := bstep (se 1 (by rfl) ⟨1284008, by rfl⟩ : syracuseStep 1712011 = 2568017) B2568017
theorem B3424139 : Blo 1520457 3424139 := bstep (se 1 (by rfl) ⟨2568104, by rfl⟩ : syracuseStep 3424139 = 5136209) B5136209
theorem B3850163 : Blo 1520457 3850163 := bstep (se 1 (by rfl) ⟨2887622, by rfl⟩ : syracuseStep 3850163 = 5775245) B5775245
theorem B3424193 : Blo 1520457 3424193 := bstep (se 2 (by rfl) ⟨1284072, by rfl⟩ : syracuseStep 3424193 = 2568145) B2568145
theorem B1712119 : Blo 1520457 1712119 := bstep (se 1 (by rfl) ⟨1284089, by rfl⟩ : syracuseStep 1712119 = 2568179) B2568179
theorem B18767933 : Blo 1520457 18767933 := bstep (se 3 (by rfl) ⟨3518987, by rfl⟩ : syracuseStep 18767933 = 7037975) B7037975
theorem B4333655 : Blo 1520457 4333655 := bstep (se 1 (by rfl) ⟨3250241, by rfl⟩ : syracuseStep 4333655 = 6500483) B6500483
theorem B5857367 : Blo 1520457 5857367 := bstep (se 1 (by rfl) ⟨4393025, by rfl⟩ : syracuseStep 5857367 = 8786051) B8786051
theorem B3850355 : Blo 1520457 3850355 := bstep (se 1 (by rfl) ⟨2887766, by rfl⟩ : syracuseStep 3850355 = 5775533) B5775533
theorem B3850375 : Blo 1520457 3850375 := bstep (se 1 (by rfl) ⟨2887781, by rfl⟩ : syracuseStep 3850375 = 5775563) B5775563
theorem B3424391 : Blo 1520457 3424391 := bstep (se 1 (by rfl) ⟨2568293, by rfl⟩ : syracuseStep 3424391 = 5136587) B5136587
theorem B1712263 : Blo 1520457 1712263 := bstep (se 1 (by rfl) ⟨1284197, by rfl⟩ : syracuseStep 1712263 = 2568395) B2568395
theorem B4333769 : Blo 1520457 4333769 := bstep (se 2 (by rfl) ⟨1625163, by rfl⟩ : syracuseStep 4333769 = 3250327) B3250327
theorem B9249005 : Blo 1520457 9249005 := bstep (se 3 (by rfl) ⟨1734188, by rfl⟩ : syracuseStep 9249005 = 3468377) B3468377
theorem B5136641 : Blo 1520457 5136641 := bstep (se 2 (by rfl) ⟨1926240, by rfl⟩ : syracuseStep 5136641 = 3852481) B3852481
theorem B3424571 : Blo 1520457 3424571 := bstep (se 1 (by rfl) ⟨2568428, by rfl⟩ : syracuseStep 3424571 = 5136857) B5136857
theorem B1712443 : Blo 1520457 1712443 := bstep (se 1 (by rfl) ⟨1284332, by rfl⟩ : syracuseStep 1712443 = 2568665) B2568665
theorem B5775731 : Blo 1520457 5775731 := bstep (se 1 (by rfl) ⟨4331798, by rfl⟩ : syracuseStep 5775731 = 8663597) B8663597
theorem B4170131 : Blo 1520457 4170131 := bstep (se 1 (by rfl) ⟨3127598, by rfl⟩ : syracuseStep 4170131 = 6255197) B6255197
theorem B3850649 : Blo 1520457 3850649 := bstep (se 2 (by rfl) ⟨1443993, by rfl⟩ : syracuseStep 3850649 = 2887987) B2887987
theorem B3424697 : Blo 1520457 3424697 := bstep (se 2 (by rfl) ⟨1284261, by rfl⟩ : syracuseStep 3424697 = 2568523) B2568523
theorem B16441805 : Blo 1520457 16441805 := bstep (se 3 (by rfl) ⟨3082838, by rfl⟩ : syracuseStep 16441805 = 6165677) B6165677
theorem B1925623 : Blo 1520457 1925623 := bstep (se 1 (by rfl) ⟨1444217, by rfl⟩ : syracuseStep 1925623 = 2888435) B2888435
theorem B6169117 : Blo 1520457 6169117 := bstep (se 3 (by rfl) ⟨1156709, by rfl⟩ : syracuseStep 6169117 = 2313419) B2313419
theorem B3850811 : Blo 1520457 3850811 := bstep (se 1 (by rfl) ⟨2888108, by rfl⟩ : syracuseStep 3850811 = 5776217) B5776217
theorem B4874813 : Blo 1520457 4874813 := bstep (se 3 (by rfl) ⟨914027, by rfl⟩ : syracuseStep 4874813 = 1828055) B1828055
theorem B2056951 : Blo 1520457 2056951 := bstep (se 1 (by rfl) ⟨1542713, by rfl⟩ : syracuseStep 2056951 = 3085427) B3085427
theorem B3851023 : Blo 1520457 3851023 := bstep (se 1 (by rfl) ⟨2888267, by rfl⟩ : syracuseStep 3851023 = 5776535) B5776535
theorem B3425039 : Blo 1520457 3425039 := bstep (se 1 (by rfl) ⟨2568779, by rfl⟩ : syracuseStep 3425039 = 5137559) B5137559
theorem B3425057 : Blo 1520457 3425057 := bstep (se 2 (by rfl) ⟨1284396, by rfl⟩ : syracuseStep 3425057 = 2568793) B2568793
theorem B7308083 : Blo 1520457 7308083 := bstep (se 1 (by rfl) ⟨5481062, by rfl⟩ : syracuseStep 7308083 = 10962125) B10962125
theorem B1925947 : Blo 1520457 1925947 := bstep (se 1 (by rfl) ⟨1444460, by rfl⟩ : syracuseStep 1925947 = 2888921) B2888921
theorem B4629307 : Blo 1520457 4629307 := bstep (se 1 (by rfl) ⟨3471980, by rfl⟩ : syracuseStep 4629307 = 6943961) B6943961
theorem B4170611 : Blo 1520457 4170611 := bstep (se 1 (by rfl) ⟨3127958, by rfl⟩ : syracuseStep 4170611 = 6255917) B6255917
theorem B3851297 : Blo 1520457 3851297 := bstep (se 2 (by rfl) ⟨1444236, by rfl⟩ : syracuseStep 3851297 = 2888473) B2888473
theorem B4940843 : Blo 1520457 4940843 := bstep (se 1 (by rfl) ⟨3705632, by rfl⟩ : syracuseStep 4940843 = 7411265) B7411265
theorem B5137451 : Blo 1520457 5137451 := bstep (se 1 (by rfl) ⟨3853088, by rfl⟩ : syracuseStep 5137451 = 7706177) B7706177
theorem B6587459 : Blo 1520457 6587459 := bstep (se 1 (by rfl) ⟨4940594, by rfl⟩ : syracuseStep 6587459 = 9881189) B9881189
theorem B3425399 : Blo 1520457 3425399 := bstep (se 1 (by rfl) ⟨2569049, by rfl⟩ : syracuseStep 3425399 = 5138099) B5138099
theorem B1926443 : Blo 1520457 1926443 := bstep (se 1 (by rfl) ⟨1444832, by rfl⟩ : syracuseStep 1926443 = 2889665) B2889665
theorem B25994681 : Blo 1520457 25994681 := bstep (se 2 (by rfl) ⟨9748005, by rfl⟩ : syracuseStep 25994681 = 19496011) B19496011
theorem B8660681 : Blo 1520457 8660681 := bstep (se 2 (by rfl) ⟨3247755, by rfl⟩ : syracuseStep 8660681 = 6495511) B6495511
theorem B4875977 : Blo 1520457 4875977 := bstep (se 2 (by rfl) ⟨1828491, by rfl⟩ : syracuseStep 4875977 = 3656983) B3656983
theorem B2565931 : Blo 1520457 2565931 := bstep (se 1 (by rfl) ⟨1924448, by rfl⟩ : syracuseStep 2565931 = 3848897) B3848897
theorem B2566073 : Blo 1520457 2566073 := bstep (se 2 (by rfl) ⟨962277, by rfl⟩ : syracuseStep 2566073 = 1924555) B1924555
theorem B3852299 : Blo 1520457 3852299 := bstep (se 1 (by rfl) ⟨2889224, by rfl⟩ : syracuseStep 3852299 = 5778449) B5778449
theorem B17328329 : Blo 1520457 17328329 := bstep (se 2 (by rfl) ⟨6498123, by rfl⟩ : syracuseStep 17328329 = 12996247) B12996247
theorem B70240517 : Blo 1520457 70240517 := bstep (se 4 (by rfl) ⟨6585048, by rfl⟩ : syracuseStep 70240517 = 13170097) B13170097
theorem B7702937 : Blo 1520457 7702937 := bstep (se 2 (by rfl) ⟨2888601, by rfl⟩ : syracuseStep 7702937 = 5777203) B5777203
theorem B5777963 : Blo 1520457 5777963 := bstep (se 1 (by rfl) ⟨4333472, by rfl⟩ : syracuseStep 5777963 = 8666945) B8666945
theorem B32983595 : Blo 1520457 32983595 := bstep (se 1 (by rfl) ⟨24737696, by rfl⟩ : syracuseStep 32983595 = 49475393) B49475393
theorem B16443971 : Blo 1520457 16443971 := bstep (se 1 (by rfl) ⟨12332978, by rfl⟩ : syracuseStep 16443971 = 24665957) B24665957
theorem B2566775 : Blo 1520457 2566775 := bstep (se 1 (by rfl) ⟨1925081, by rfl⟩ : syracuseStep 2566775 = 3850163) B3850163
theorem B18516599 : Blo 1520457 18516599 := bstep (se 1 (by rfl) ⟨13887449, by rfl⟩ : syracuseStep 18516599 = 27774899) B27774899
theorem B3852947 : Blo 1520457 3852947 := bstep (se 1 (by rfl) ⟨2889710, by rfl⟩ : syracuseStep 3852947 = 5779421) B5779421
theorem B2165449 : Blo 1520457 2165449 := bstep (se 2 (by rfl) ⟨812043, by rfl⟩ : syracuseStep 2165449 = 1624087) B1624087
theorem B2165563 : Blo 1520457 2165563 := bstep (se 1 (by rfl) ⟨1624172, by rfl⟩ : syracuseStep 2165563 = 3248345) B3248345
theorem B9251729 : Blo 1520457 9251729 := bstep (se 2 (by rfl) ⟨3469398, by rfl⟩ : syracuseStep 9251729 = 6938797) B6938797
theorem B12331939 : Blo 1520457 12331939 := bstep (se 1 (by rfl) ⟨9248954, by rfl⟩ : syracuseStep 12331939 = 18497909) B18497909
theorem B3853241 : Blo 1520457 3853241 := bstep (se 2 (by rfl) ⟨1444965, by rfl⟩ : syracuseStep 3853241 = 2889931) B2889931
theorem B3468233 : Blo 1520457 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B2436041 : Blo 1520457 2436041 := bstep (se 2 (by rfl) ⟨913515, by rfl⟩ : syracuseStep 2436041 = 1827031) B1827031
theorem B2567227 : Blo 1520457 2567227 := bstep (se 1 (by rfl) ⟨1925420, by rfl⟩ : syracuseStep 2567227 = 3850841) B3850841
theorem B13888685 : Blo 1520457 13888685 := bstep (se 3 (by rfl) ⟨2604128, by rfl⟩ : syracuseStep 13888685 = 5208257) B5208257
theorem B2567369 : Blo 1520457 2567369 := bstep (se 2 (by rfl) ⟨962763, by rfl⟩ : syracuseStep 2567369 = 1925527) B1925527
theorem B2280695 : Blo 1520457 2280695 := bstep (se 1 (by rfl) ⟨1710521, by rfl⟩ : syracuseStep 2280695 = 3421043) B3421043
theorem B1625351 : Blo 1520457 1625351 := bstep (se 1 (by rfl) ⟨1219013, by rfl⟩ : syracuseStep 1625351 = 2438027) B2438027
theorem B2280719 : Blo 1520457 2280719 := bstep (se 1 (by rfl) ⟨1710539, by rfl⟩ : syracuseStep 2280719 = 3421079) B3421079
theorem B2280761 : Blo 1520457 2280761 := bstep (se 2 (by rfl) ⟨855285, by rfl⟩ : syracuseStep 2280761 = 1710571) B1710571
theorem B2280839 : Blo 1520457 2280839 := bstep (se 1 (by rfl) ⟨1710629, by rfl⟩ : syracuseStep 2280839 = 3421259) B3421259
theorem B31214983 : Blo 1520457 31214983 := bstep (se 1 (by rfl) ⟨23411237, by rfl⟩ : syracuseStep 31214983 = 46822475) B46822475
theorem B5131673 : Blo 1520457 5131673 := bstep (se 2 (by rfl) ⟨1924377, by rfl⟩ : syracuseStep 5131673 = 3848755) B3848755
theorem B2280875 : Blo 1520457 2280875 := bstep (se 1 (by rfl) ⟨1710656, by rfl⟩ : syracuseStep 2280875 = 3421313) B3421313
theorem B2280905 : Blo 1520457 2280905 := bstep (se 2 (by rfl) ⟨855339, by rfl⟩ : syracuseStep 2280905 = 1710679) B1710679
theorem B8662571 : Blo 1520457 8662571 := bstep (se 1 (by rfl) ⟨6496928, by rfl⟩ : syracuseStep 8662571 = 12993857) B12993857
theorem B7409195 : Blo 1520457 7409195 := bstep (se 1 (by rfl) ⟨5556896, by rfl⟩ : syracuseStep 7409195 = 11113793) B11113793
theorem B7310891 : Blo 1520457 7310891 := bstep (se 1 (by rfl) ⟨5483168, by rfl⟩ : syracuseStep 7310891 = 10966337) B10966337
theorem B2281019 : Blo 1520457 2281019 := bstep (se 1 (by rfl) ⟨1710764, by rfl⟩ : syracuseStep 2281019 = 3421529) B3421529
theorem B6499901 : Blo 1520457 6499901 := bstep (se 3 (by rfl) ⟨1218731, by rfl⟩ : syracuseStep 6499901 = 2437463) B2437463
theorem B2281079 : Blo 1520457 2281079 := bstep (se 1 (by rfl) ⟨1710809, by rfl⟩ : syracuseStep 2281079 = 3421619) B3421619
theorem B44461709 : Blo 1520457 44461709 := bstep (se 3 (by rfl) ⟨8336570, by rfl⟩ : syracuseStep 44461709 = 16673141) B16673141
theorem B2281103 : Blo 1520457 2281103 := bstep (se 1 (by rfl) ⟨1710827, by rfl⟩ : syracuseStep 2281103 = 3421655) B3421655
theorem B2281145 : Blo 1520457 2281145 := bstep (se 2 (by rfl) ⟨855429, by rfl⟩ : syracuseStep 2281145 = 1710859) B1710859
theorem B111054563 : Blo 1520457 111054563 := bstep (se 1 (by rfl) ⟨83290922, by rfl⟩ : syracuseStep 111054563 = 166581845) B166581845
theorem B2281223 : Blo 1520457 2281223 := bstep (se 1 (by rfl) ⟨1710917, by rfl⟩ : syracuseStep 2281223 = 3421835) B3421835
theorem B2281259 : Blo 1520457 2281259 := bstep (se 1 (by rfl) ⟨1710944, by rfl⟩ : syracuseStep 2281259 = 3421889) B3421889
theorem B2281289 : Blo 1520457 2281289 := bstep (se 2 (by rfl) ⟨855483, by rfl⟩ : syracuseStep 2281289 = 1710967) B1710967
theorem B11554649 : Blo 1520457 11554649 := bstep (se 2 (by rfl) ⟨4332993, by rfl⟩ : syracuseStep 11554649 = 8665987) B8665987
theorem B2568071 : Blo 1520457 2568071 := bstep (se 1 (by rfl) ⟨1926053, by rfl⟩ : syracuseStep 2568071 = 3852107) B3852107
theorem B6500243 : Blo 1520457 6500243 := bstep (se 1 (by rfl) ⟨4875182, by rfl⟩ : syracuseStep 6500243 = 9750365) B9750365
theorem B2281403 : Blo 1520457 2281403 := bstep (se 1 (by rfl) ⟨1711052, by rfl⟩ : syracuseStep 2281403 = 3422105) B3422105
theorem B2281463 : Blo 1520457 2281463 := bstep (se 1 (by rfl) ⟨1711097, by rfl⟩ : syracuseStep 2281463 = 3422195) B3422195
theorem B2281487 : Blo 1520457 2281487 := bstep (se 1 (by rfl) ⟨1711115, by rfl⟩ : syracuseStep 2281487 = 3422231) B3422231
theorem B2281529 : Blo 1520457 2281529 := bstep (se 2 (by rfl) ⟨855573, by rfl⟩ : syracuseStep 2281529 = 1711147) B1711147
theorem B5132375 : Blo 1520457 5132375 := bstep (se 1 (by rfl) ⟨3849281, by rfl⟩ : syracuseStep 5132375 = 7698563) B7698563
theorem B18518149 : Blo 1520457 18518149 := bstep (se 4 (by rfl) ⟨1736076, by rfl⟩ : syracuseStep 18518149 = 3472153) B3472153
theorem B2281607 : Blo 1520457 2281607 := bstep (se 1 (by rfl) ⟨1711205, by rfl⟩ : syracuseStep 2281607 = 3422411) B3422411
theorem B2281643 : Blo 1520457 2281643 := bstep (se 1 (by rfl) ⟨1711232, by rfl⟩ : syracuseStep 2281643 = 3422465) B3422465
theorem B2281673 : Blo 1520457 2281673 := bstep (se 2 (by rfl) ⟨855627, by rfl⟩ : syracuseStep 2281673 = 1711255) B1711255
theorem B2281787 : Blo 1520457 2281787 := bstep (se 1 (by rfl) ⟨1711340, by rfl⟩ : syracuseStep 2281787 = 3422681) B3422681
theorem B2281847 : Blo 1520457 2281847 := bstep (se 1 (by rfl) ⟨1711385, by rfl⟩ : syracuseStep 2281847 = 3422771) B3422771
theorem B2167175 : Blo 1520457 2167175 := bstep (se 1 (by rfl) ⟨1625381, by rfl⟩ : syracuseStep 2167175 = 3250763) B3250763
theorem B2281871 : Blo 1520457 2281871 := bstep (se 1 (by rfl) ⟨1711403, by rfl⟩ : syracuseStep 2281871 = 3422807) B3422807
theorem B2281913 : Blo 1520457 2281913 := bstep (se 2 (by rfl) ⟨855717, by rfl⟩ : syracuseStep 2281913 = 1711435) B1711435
theorem B2281991 : Blo 1520457 2281991 := bstep (se 1 (by rfl) ⟨1711493, by rfl⟩ : syracuseStep 2281991 = 3422987) B3422987
theorem B2888207 : Blo 1520457 2888207 := bstep (se 1 (by rfl) ⟨2166155, by rfl⟩ : syracuseStep 2888207 = 4332311) B4332311
theorem B2568719 : Blo 1520457 2568719 := bstep (se 1 (by rfl) ⟨1926539, by rfl⟩ : syracuseStep 2568719 = 3853079) B3853079
theorem B2282027 : Blo 1520457 2282027 := bstep (se 1 (by rfl) ⟨1711520, by rfl⟩ : syracuseStep 2282027 = 3423041) B3423041
theorem B5485099 : Blo 1520457 5485099 := bstep (se 1 (by rfl) ⟨4113824, by rfl⟩ : syracuseStep 5485099 = 8227649) B8227649
theorem B5132861 : Blo 1520457 5132861 := bstep (se 3 (by rfl) ⟨962411, by rfl⟩ : syracuseStep 5132861 = 1924823) B1924823
theorem B2282057 : Blo 1520457 2282057 := bstep (se 2 (by rfl) ⟨855771, by rfl⟩ : syracuseStep 2282057 = 1711543) B1711543
theorem B25981559 : Blo 1520457 25981559 := bstep (se 1 (by rfl) ⟨19486169, by rfl⟩ : syracuseStep 25981559 = 38972339) B38972339
theorem B4330169 : Blo 1520457 4330169 := bstep (se 2 (by rfl) ⟨1623813, by rfl⟩ : syracuseStep 4330169 = 3247627) B3247627
theorem B2282171 : Blo 1520457 2282171 := bstep (se 1 (by rfl) ⟨1711628, by rfl⟩ : syracuseStep 2282171 = 3423257) B3423257
theorem B8221421 : Blo 1520457 8221421 := bstep (se 3 (by rfl) ⟨1541516, by rfl⟩ : syracuseStep 8221421 = 3083033) B3083033
theorem B2282231 : Blo 1520457 2282231 := bstep (se 1 (by rfl) ⟨1711673, by rfl⟩ : syracuseStep 2282231 = 3423347) B3423347
theorem B2282255 : Blo 1520457 2282255 := bstep (se 1 (by rfl) ⟨1711691, by rfl⟩ : syracuseStep 2282255 = 3423383) B3423383
theorem B11555621 : Blo 1520457 11555621 := bstep (se 4 (by rfl) ⟨1083339, by rfl⟩ : syracuseStep 11555621 = 2166679) B2166679
theorem B2282297 : Blo 1520457 2282297 := bstep (se 2 (by rfl) ⟨855861, by rfl⟩ : syracuseStep 2282297 = 1711723) B1711723
theorem B1520519 : Blo 1520457 1520519 := bstep (se 1 (by rfl) ⟨1140389, by rfl⟩ : syracuseStep 1520519 = 2280779) B2280779
theorem B2282375 : Blo 1520457 2282375 := bstep (se 1 (by rfl) ⟨1711781, by rfl⟩ : syracuseStep 2282375 = 3423563) B3423563
theorem B1520527 : Blo 1520457 1520527 := bstep (se 1 (by rfl) ⟨1140395, by rfl⟩ : syracuseStep 1520527 = 2280791) B2280791
theorem B2282411 : Blo 1520457 2282411 := bstep (se 1 (by rfl) ⟨1711808, by rfl⟩ : syracuseStep 2282411 = 3423617) B3423617
theorem B7705529 : Blo 1520457 7705529 := bstep (se 2 (by rfl) ⟨2889573, by rfl⟩ : syracuseStep 7705529 = 5779147) B5779147
theorem B1520571 : Blo 1520457 1520571 := bstep (se 1 (by rfl) ⟨1140428, by rfl⟩ : syracuseStep 1520571 = 2280857) B2280857
theorem B2282441 : Blo 1520457 2282441 := bstep (se 2 (by rfl) ⟨855915, by rfl⟩ : syracuseStep 2282441 = 1711831) B1711831
theorem B8664029 : Blo 1520457 8664029 := bstep (se 3 (by rfl) ⟨1624505, by rfl⟩ : syracuseStep 8664029 = 3249011) B3249011
theorem B1520647 : Blo 1520457 1520647 := bstep (se 1 (by rfl) ⟨1140485, by rfl⟩ : syracuseStep 1520647 = 2280971) B2280971
theorem B1520655 : Blo 1520457 1520655 := bstep (se 1 (by rfl) ⟨1140491, by rfl⟩ : syracuseStep 1520655 = 2280983) B2280983
theorem B2470927 : Blo 1520457 2470927 := bstep (se 1 (by rfl) ⟨1853195, by rfl⟩ : syracuseStep 2470927 = 3706391) B3706391
theorem B17331245 : Blo 1520457 17331245 := bstep (se 3 (by rfl) ⟨3249608, by rfl⟩ : syracuseStep 17331245 = 6499217) B6499217
theorem B1520699 : Blo 1520457 1520699 := bstep (se 1 (by rfl) ⟨1140524, by rfl⟩ : syracuseStep 1520699 = 2281049) B2281049
theorem B2282555 : Blo 1520457 2282555 := bstep (se 1 (by rfl) ⟨1711916, by rfl⟩ : syracuseStep 2282555 = 3423833) B3423833
theorem B13874237 : Blo 1520457 13874237 := bstep (se 3 (by rfl) ⟨2601419, by rfl⟩ : syracuseStep 13874237 = 5202839) B5202839
theorem B2282615 : Blo 1520457 2282615 := bstep (se 1 (by rfl) ⟨1711961, by rfl⟩ : syracuseStep 2282615 = 3423923) B3423923
theorem B1520775 : Blo 1520457 1520775 := bstep (se 1 (by rfl) ⟨1140581, by rfl⟩ : syracuseStep 1520775 = 2281163) B2281163
theorem B1520783 : Blo 1520457 1520783 := bstep (se 1 (by rfl) ⟨1140587, by rfl⟩ : syracuseStep 1520783 = 2281175) B2281175
theorem B2282639 : Blo 1520457 2282639 := bstep (se 1 (by rfl) ⟨1711979, by rfl⟩ : syracuseStep 2282639 = 3423959) B3423959
theorem B3421331 : Blo 1520457 3421331 := bstep (se 1 (by rfl) ⟨2565998, by rfl⟩ : syracuseStep 3421331 = 5131997) B5131997
theorem B2282681 : Blo 1520457 2282681 := bstep (se 2 (by rfl) ⟨856005, by rfl⟩ : syracuseStep 2282681 = 1712011) B1712011
theorem B1520827 : Blo 1520457 1520827 := bstep (se 1 (by rfl) ⟨1140620, by rfl⟩ : syracuseStep 1520827 = 2281241) B2281241
theorem B3421385 : Blo 1520457 3421385 := bstep (se 2 (by rfl) ⟨1283019, by rfl⟩ : syracuseStep 3421385 = 2566039) B2566039
theorem B1520903 : Blo 1520457 1520903 := bstep (se 1 (by rfl) ⟨1140677, by rfl⟩ : syracuseStep 1520903 = 2281355) B2281355
theorem B2282759 : Blo 1520457 2282759 := bstep (se 1 (by rfl) ⟨1712069, by rfl⟩ : syracuseStep 2282759 = 3424139) B3424139
theorem B1520911 : Blo 1520457 1520911 := bstep (se 1 (by rfl) ⟨1140683, by rfl⟩ : syracuseStep 1520911 = 2281367) B2281367
theorem B19502369 : Blo 1520457 19502369 := bstep (se 2 (by rfl) ⟨7313388, by rfl⟩ : syracuseStep 19502369 = 14626777) B14626777
theorem B2282795 : Blo 1520457 2282795 := bstep (se 1 (by rfl) ⟨1712096, by rfl⟩ : syracuseStep 2282795 = 3424193) B3424193
theorem B1520955 : Blo 1520457 1520955 := bstep (se 1 (by rfl) ⟨1140716, by rfl⟩ : syracuseStep 1520955 = 2281433) B2281433
theorem B2282825 : Blo 1520457 2282825 := bstep (se 2 (by rfl) ⟨856059, by rfl⟩ : syracuseStep 2282825 = 1712119) B1712119
theorem B7697753 : Blo 1520457 7697753 := bstep (se 2 (by rfl) ⟨2886657, by rfl⟩ : syracuseStep 7697753 = 5773315) B5773315
theorem B1521031 : Blo 1520457 1521031 := bstep (se 1 (by rfl) ⟨1140773, by rfl⟩ : syracuseStep 1521031 = 2281547) B2281547
theorem B1521039 : Blo 1520457 1521039 := bstep (se 1 (by rfl) ⟨1140779, by rfl⟩ : syracuseStep 1521039 = 2281559) B2281559
theorem B1521083 : Blo 1520457 1521083 := bstep (se 1 (by rfl) ⟨1140812, by rfl⟩ : syracuseStep 1521083 = 2281625) B2281625
theorem B2282939 : Blo 1520457 2282939 := bstep (se 1 (by rfl) ⟨1712204, by rfl⟩ : syracuseStep 2282939 = 3424409) B3424409
theorem B8664529 : Blo 1520457 8664529 := bstep (se 2 (by rfl) ⟨3249198, by rfl⟩ : syracuseStep 8664529 = 6498397) B6498397
theorem B2282999 : Blo 1520457 2282999 := bstep (se 1 (by rfl) ⟨1712249, by rfl⟩ : syracuseStep 2282999 = 3424499) B3424499
theorem B1521159 : Blo 1520457 1521159 := bstep (se 1 (by rfl) ⟨1140869, by rfl⟩ : syracuseStep 1521159 = 2281739) B2281739
theorem B1521167 : Blo 1520457 1521167 := bstep (se 1 (by rfl) ⟨1140875, by rfl⟩ : syracuseStep 1521167 = 2281751) B2281751
theorem B2283023 : Blo 1520457 2283023 := bstep (se 1 (by rfl) ⟨1712267, by rfl⟩ : syracuseStep 2283023 = 3424535) B3424535
theorem B2283065 : Blo 1520457 2283065 := bstep (se 2 (by rfl) ⟨856149, by rfl⟩ : syracuseStep 2283065 = 1712299) B1712299
theorem B1521211 : Blo 1520457 1521211 := bstep (se 1 (by rfl) ⟨1140908, by rfl⟩ : syracuseStep 1521211 = 2281817) B2281817
theorem B1521287 : Blo 1520457 1521287 := bstep (se 1 (by rfl) ⟨1140965, by rfl⟩ : syracuseStep 1521287 = 2281931) B2281931
theorem B2283143 : Blo 1520457 2283143 := bstep (se 1 (by rfl) ⟨1712357, by rfl⟩ : syracuseStep 2283143 = 3424715) B3424715
theorem B1521295 : Blo 1520457 1521295 := bstep (se 1 (by rfl) ⟨1140971, by rfl⟩ : syracuseStep 1521295 = 2281943) B2281943
theorem B35149463 : Blo 1520457 35149463 := bstep (se 1 (by rfl) ⟨26362097, by rfl⟩ : syracuseStep 35149463 = 52724195) B52724195
theorem B2283179 : Blo 1520457 2283179 := bstep (se 1 (by rfl) ⟨1712384, by rfl⟩ : syracuseStep 2283179 = 3424769) B3424769
theorem B1521339 : Blo 1520457 1521339 := bstep (se 1 (by rfl) ⟨1141004, by rfl⟩ : syracuseStep 1521339 = 2282009) B2282009
theorem B2283209 : Blo 1520457 2283209 := bstep (se 2 (by rfl) ⟨856203, by rfl⟩ : syracuseStep 2283209 = 1712407) B1712407
theorem B1521415 : Blo 1520457 1521415 := bstep (se 1 (by rfl) ⟨1141061, by rfl⟩ : syracuseStep 1521415 = 2282123) B2282123
theorem B1521423 : Blo 1520457 1521423 := bstep (se 1 (by rfl) ⟨1141067, by rfl⟩ : syracuseStep 1521423 = 2282135) B2282135
theorem B1521467 : Blo 1520457 1521467 := bstep (se 1 (by rfl) ⟨1141100, by rfl⟩ : syracuseStep 1521467 = 2282201) B2282201
theorem B2283323 : Blo 1520457 2283323 := bstep (se 1 (by rfl) ⟨1712492, by rfl⟩ : syracuseStep 2283323 = 3424985) B3424985
theorem B2283383 : Blo 1520457 2283383 := bstep (se 1 (by rfl) ⟨1712537, by rfl⟩ : syracuseStep 2283383 = 3425075) B3425075
theorem B3422087 : Blo 1520457 3422087 := bstep (se 1 (by rfl) ⟨2566565, by rfl⟩ : syracuseStep 3422087 = 5133131) B5133131
theorem B1734535 : Blo 1520457 1734535 := bstep (se 1 (by rfl) ⟨1300901, by rfl⟩ : syracuseStep 1734535 = 2601803) B2601803
theorem B1521543 : Blo 1520457 1521543 := bstep (se 1 (by rfl) ⟨1141157, by rfl⟩ : syracuseStep 1521543 = 2282315) B2282315
theorem B1521551 : Blo 1520457 1521551 := bstep (se 1 (by rfl) ⟨1141163, by rfl⟩ : syracuseStep 1521551 = 2282327) B2282327
theorem B2283407 : Blo 1520457 2283407 := bstep (se 1 (by rfl) ⟨1712555, by rfl⟩ : syracuseStep 2283407 = 3425111) B3425111
theorem B5486483 : Blo 1520457 5486483 := bstep (se 1 (by rfl) ⟨4114862, by rfl⟩ : syracuseStep 5486483 = 8229725) B8229725
theorem B5134265 : Blo 1520457 5134265 := bstep (se 2 (by rfl) ⟨1925349, by rfl⟩ : syracuseStep 5134265 = 3850699) B3850699
theorem B2283449 : Blo 1520457 2283449 := bstep (se 2 (by rfl) ⟨856293, by rfl⟩ : syracuseStep 2283449 = 1712587) B1712587
theorem B1521595 : Blo 1520457 1521595 := bstep (se 1 (by rfl) ⟨1141196, by rfl⟩ : syracuseStep 1521595 = 2282393) B2282393
theorem B1521671 : Blo 1520457 1521671 := bstep (se 1 (by rfl) ⟨1141253, by rfl⟩ : syracuseStep 1521671 = 2282507) B2282507
theorem B2283527 : Blo 1520457 2283527 := bstep (se 1 (by rfl) ⟨1712645, by rfl⟩ : syracuseStep 2283527 = 3425291) B3425291
theorem B3954703 : Blo 1520457 3954703 := bstep (se 1 (by rfl) ⟨2966027, by rfl⟩ : syracuseStep 3954703 = 5932055) B5932055
theorem B1521679 : Blo 1520457 1521679 := bstep (se 1 (by rfl) ⟨1141259, by rfl⟩ : syracuseStep 1521679 = 2282519) B2282519
theorem B2283563 : Blo 1520457 2283563 := bstep (se 1 (by rfl) ⟨1712672, by rfl⟩ : syracuseStep 2283563 = 3425345) B3425345
theorem B3422267 : Blo 1520457 3422267 := bstep (se 1 (by rfl) ⟨2566700, by rfl⟩ : syracuseStep 3422267 = 5133401) B5133401
theorem B1521723 : Blo 1520457 1521723 := bstep (se 1 (by rfl) ⟨1141292, by rfl⟩ : syracuseStep 1521723 = 2282585) B2282585
theorem B2283593 : Blo 1520457 2283593 := bstep (se 2 (by rfl) ⟨856347, by rfl⟩ : syracuseStep 2283593 = 1712695) B1712695
theorem B2889847 : Blo 1520457 2889847 := bstep (se 1 (by rfl) ⟨2167385, by rfl⟩ : syracuseStep 2889847 = 4334771) B4334771
theorem B1521799 : Blo 1520457 1521799 := bstep (se 1 (by rfl) ⟨1141349, by rfl⟩ : syracuseStep 1521799 = 2282699) B2282699
theorem B1521807 : Blo 1520457 1521807 := bstep (se 1 (by rfl) ⟨1141355, by rfl⟩ : syracuseStep 1521807 = 2282711) B2282711
theorem B3422393 : Blo 1520457 3422393 := bstep (se 2 (by rfl) ⟨1283397, by rfl⟩ : syracuseStep 3422393 = 2566795) B2566795
theorem B3250361 : Blo 1520457 3250361 := bstep (se 2 (by rfl) ⟨1218885, by rfl⟩ : syracuseStep 3250361 = 2437771) B2437771
theorem B1521851 : Blo 1520457 1521851 := bstep (se 1 (by rfl) ⟨1141388, by rfl⟩ : syracuseStep 1521851 = 2282777) B2282777
theorem B7706825 : Blo 1520457 7706825 := bstep (se 2 (by rfl) ⟨2890059, by rfl⟩ : syracuseStep 7706825 = 5780119) B5780119
theorem B1521927 : Blo 1520457 1521927 := bstep (se 1 (by rfl) ⟨1141445, by rfl⟩ : syracuseStep 1521927 = 2282891) B2282891
theorem B1521935 : Blo 1520457 1521935 := bstep (se 1 (by rfl) ⟨1141451, by rfl⟩ : syracuseStep 1521935 = 2282903) B2282903
theorem B4331809 : Blo 1520457 4331809 := bstep (se 2 (by rfl) ⟨1624428, by rfl⟩ : syracuseStep 4331809 = 3248857) B3248857
theorem B1521979 : Blo 1520457 1521979 := bstep (se 1 (by rfl) ⟨1141484, by rfl⟩ : syracuseStep 1521979 = 2282969) B2282969
theorem B6502771 : Blo 1520457 6502771 := bstep (se 1 (by rfl) ⟨4877078, by rfl⟩ : syracuseStep 6502771 = 9754157) B9754157
theorem B1522055 : Blo 1520457 1522055 := bstep (se 1 (by rfl) ⟨1141541, by rfl⟩ : syracuseStep 1522055 = 2283083) B2283083
theorem B1522063 : Blo 1520457 1522063 := bstep (se 1 (by rfl) ⟨1141547, by rfl⟩ : syracuseStep 1522063 = 2283095) B2283095
theorem B16456081 : Blo 1520457 16456081 := bstep (se 2 (by rfl) ⟨6171030, by rfl⟩ : syracuseStep 16456081 = 12342061) B12342061
theorem B4872595 : Blo 1520457 4872595 := bstep (se 1 (by rfl) ⟨3654446, by rfl⟩ : syracuseStep 4872595 = 7308893) B7308893
theorem B6502841 : Blo 1520457 6502841 := bstep (se 2 (by rfl) ⟨2438565, by rfl⟩ : syracuseStep 6502841 = 4877131) B4877131
theorem B1522107 : Blo 1520457 1522107 := bstep (se 1 (by rfl) ⟨1141580, by rfl⟩ : syracuseStep 1522107 = 2283161) B2283161
theorem B3848705 : Blo 1520457 3848705 := bstep (se 2 (by rfl) ⟨1443264, by rfl⟩ : syracuseStep 3848705 = 2886529) B2886529
theorem B1522183 : Blo 1520457 1522183 := bstep (se 1 (by rfl) ⟨1141637, by rfl⟩ : syracuseStep 1522183 = 2283275) B2283275
theorem B5134859 : Blo 1520457 5134859 := bstep (se 1 (by rfl) ⟨3851144, by rfl⟩ : syracuseStep 5134859 = 7702289) B7702289
theorem B1710607 : Blo 1520457 1710607 := bstep (se 1 (by rfl) ⟨1282955, by rfl⟩ : syracuseStep 1710607 = 2565911) B2565911
theorem B3422735 : Blo 1520457 3422735 := bstep (se 1 (by rfl) ⟨2567051, by rfl⟩ : syracuseStep 3422735 = 5134103) B5134103
theorem B1522191 : Blo 1520457 1522191 := bstep (se 1 (by rfl) ⟨1141643, by rfl⟩ : syracuseStep 1522191 = 2283287) B2283287
theorem B3422753 : Blo 1520457 3422753 := bstep (se 2 (by rfl) ⟨1283532, by rfl⟩ : syracuseStep 3422753 = 2567065) B2567065
theorem B1522235 : Blo 1520457 1522235 := bstep (se 1 (by rfl) ⟨1141676, by rfl⟩ : syracuseStep 1522235 = 2283353) B2283353
theorem B11549303 : Blo 1520457 11549303 := bstep (se 1 (by rfl) ⟨8661977, by rfl⟩ : syracuseStep 11549303 = 17323955) B17323955
theorem B5134967 : Blo 1520457 5134967 := bstep (se 1 (by rfl) ⟨3851225, by rfl⟩ : syracuseStep 5134967 = 7702451) B7702451
theorem B1522311 : Blo 1520457 1522311 := bstep (se 1 (by rfl) ⟨1141733, by rfl⟩ : syracuseStep 1522311 = 2283467) B2283467
theorem B1522319 : Blo 1520457 1522319 := bstep (se 1 (by rfl) ⟨1141739, by rfl⟩ : syracuseStep 1522319 = 2283479) B2283479
theorem B14613169 : Blo 1520457 14613169 := bstep (se 2 (by rfl) ⟨5479938, by rfl⟩ : syracuseStep 14613169 = 10959877) B10959877
theorem B1522363 : Blo 1520457 1522363 := bstep (se 1 (by rfl) ⟨1141772, by rfl⟩ : syracuseStep 1522363 = 2283545) B2283545
theorem B1522439 : Blo 1520457 1522439 := bstep (se 1 (by rfl) ⟨1141829, by rfl⟩ : syracuseStep 1522439 = 2283659) B2283659
theorem B1522447 : Blo 1520457 1522447 := bstep (se 1 (by rfl) ⟨1141835, by rfl⟩ : syracuseStep 1522447 = 2283671) B2283671
theorem B4111133 : Blo 1520457 4111133 := bstep (se 3 (by rfl) ⟨770837, by rfl⟩ : syracuseStep 4111133 = 1541675) B1541675
theorem B29637413 : Blo 1520457 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B5856059 : Blo 1520457 5856059 := bstep (se 1 (by rfl) ⟨4392044, by rfl⟩ : syracuseStep 5856059 = 8784089) B8784089
theorem B3849079 : Blo 1520457 3849079 := bstep (se 1 (by rfl) ⟨2886809, by rfl⟩ : syracuseStep 3849079 = 5773619) B5773619
theorem B3423095 : Blo 1520457 3423095 := bstep (se 1 (by rfl) ⟨2567321, by rfl⟩ : syracuseStep 3423095 = 5134643) B5134643
theorem B6167431 : Blo 1520457 6167431 := bstep (se 1 (by rfl) ⟨4625573, by rfl⟩ : syracuseStep 6167431 = 9251147) B9251147
theorem B7412627 : Blo 1520457 7412627 := bstep (se 1 (by rfl) ⟨5559470, by rfl⟩ : syracuseStep 7412627 = 11118941) B11118941
theorem B7805899 : Blo 1520457 7805899 := bstep (se 1 (by rfl) ⟨5854424, by rfl⟩ : syracuseStep 7805899 = 11708849) B11708849
theorem B1711111 : Blo 1520457 1711111 := bstep (se 1 (by rfl) ⟨1283333, by rfl⟩ : syracuseStep 1711111 = 2566667) B2566667
theorem B17341451 : Blo 1520457 17341451 := bstep (se 1 (by rfl) ⟨13006088, by rfl⟩ : syracuseStep 17341451 = 26012177) B26012177
theorem B3251215 : Blo 1520457 3251215 := bstep (se 1 (by rfl) ⟨2438411, by rfl⟩ : syracuseStep 3251215 = 4876823) B4876823
theorem B3423275 : Blo 1520457 3423275 := bstep (se 1 (by rfl) ⟨2567456, by rfl⟩ : syracuseStep 3423275 = 5134913) B5134913
theorem B3251335 : Blo 1520457 3251335 := bstep (se 1 (by rfl) ⟨2438501, by rfl⟩ : syracuseStep 3251335 = 4877003) B4877003
theorem B1711291 : Blo 1520457 1711291 := bstep (se 1 (by rfl) ⟨1283468, by rfl⟩ : syracuseStep 1711291 = 2566937) B2566937
theorem B5135561 : Blo 1520457 5135561 := bstep (se 2 (by rfl) ⟨1925835, by rfl⟩ : syracuseStep 5135561 = 3851671) B3851671
theorem B3849515 : Blo 1520457 3849515 := bstep (se 1 (by rfl) ⟨2887136, by rfl⟩ : syracuseStep 3849515 = 5774273) B5774273
theorem B3251515 : Blo 1520457 3251515 := bstep (se 1 (by rfl) ⟨2438636, by rfl⟩ : syracuseStep 3251515 = 4877273) B4877273
theorem B8666513 : Blo 1520457 8666513 := bstep (se 2 (by rfl) ⟨3249942, by rfl⟩ : syracuseStep 8666513 = 6499885) B6499885
theorem B7699859 : Blo 1520457 7699859 := bstep (se 1 (by rfl) ⟨5774894, by rfl⟩ : syracuseStep 7699859 = 11549789) B11549789
theorem B3423635 : Blo 1520457 3423635 := bstep (se 1 (by rfl) ⟨2567726, by rfl⟩ : syracuseStep 3423635 = 5135453) B5135453
theorem B3423689 : Blo 1520457 3423689 := bstep (se 2 (by rfl) ⟨1283883, by rfl⟩ : syracuseStep 3423689 = 2567767) B2567767
theorem B7306699 : Blo 1520457 7306699 := bstep (se 1 (by rfl) ⟨5480024, by rfl⟩ : syracuseStep 7306699 = 10960049) B10960049
theorem B4333085 : Blo 1520457 4333085 := bstep (se 3 (by rfl) ⟨812453, by rfl⟩ : syracuseStep 4333085 = 1624907) B1624907
theorem B1924651 : Blo 1520457 1924651 := bstep (se 1 (by rfl) ⟨1443488, by rfl⟩ : syracuseStep 1924651 = 2886977) B2886977
theorem B11550275 : Blo 1520457 11550275 := bstep (se 1 (by rfl) ⟨8662706, by rfl⟩ : syracuseStep 11550275 = 17325413) B17325413
theorem B1711759 : Blo 1520457 1711759 := bstep (se 1 (by rfl) ⟨1283819, by rfl⟩ : syracuseStep 1711759 = 2567639) B2567639
theorem B4333313 : Blo 1520457 4333313 := bstep (se 2 (by rfl) ⟨1624992, by rfl⟩ : syracuseStep 4333313 = 3249985) B3249985
theorem B1924879 : Blo 1520457 1924879 := bstep (se 1 (by rfl) ⟨1443659, by rfl⟩ : syracuseStep 1924879 = 2887319) B2887319
theorem B32907059 : Blo 1520457 32907059 := bstep (se 1 (by rfl) ⟨24680294, by rfl⟩ : syracuseStep 32907059 = 49360589) B49360589
theorem B5136263 : Blo 1520457 5136263 := bstep (se 1 (by rfl) ⟨3852197, by rfl⟩ : syracuseStep 5136263 = 7704395) B7704395
theorem B3424427 : Blo 1520457 3424427 := bstep (se 1 (by rfl) ⟨2568320, by rfl⟩ : syracuseStep 3424427 = 5136641) B5136641
theorem B24690865 : Blo 1520457 24690865 := bstep (se 2 (by rfl) ⟨9259074, by rfl⟩ : syracuseStep 24690865 = 18518149) B18518149
theorem B3850487 : Blo 1520457 3850487 := bstep (se 1 (by rfl) ⟨2887865, by rfl⟩ : syracuseStep 3850487 = 5775731) B5775731
theorem B10961203 : Blo 1520457 10961203 := bstep (se 1 (by rfl) ⟨8220902, by rfl⟩ : syracuseStep 10961203 = 16441805) B16441805
theorem B1925471 : Blo 1520457 1925471 := bstep (se 1 (by rfl) ⟨1444103, by rfl⟩ : syracuseStep 1925471 = 2888207) B2888207
theorem B1712479 : Blo 1520457 1712479 := bstep (se 1 (by rfl) ⟨1284359, by rfl⟩ : syracuseStep 1712479 = 2568719) B2568719
theorem B5775745 : Blo 1520457 5775745 := bstep (se 2 (by rfl) ⟨2165904, by rfl⟩ : syracuseStep 5775745 = 4331809) B4331809
theorem B5480947 : Blo 1520457 5480947 := bstep (se 1 (by rfl) ⟨4110710, by rfl⟩ : syracuseStep 5480947 = 8221421) B8221421
theorem B6496793 : Blo 1520457 6496793 := bstep (se 2 (by rfl) ⟨2436297, by rfl⟩ : syracuseStep 6496793 = 4872595) B4872595
theorem B5137019 : Blo 1520457 5137019 := bstep (se 1 (by rfl) ⟨3852764, by rfl⟩ : syracuseStep 5137019 = 7705529) B7705529
theorem B5776019 : Blo 1520457 5776019 := bstep (se 1 (by rfl) ⟨4332014, by rfl⟩ : syracuseStep 5776019 = 8664029) B8664029
theorem B3424967 : Blo 1520457 3424967 := bstep (se 1 (by rfl) ⟨2568725, by rfl⟩ : syracuseStep 3424967 = 5137451) B5137451
theorem B8225489 : Blo 1520457 8225489 := bstep (se 2 (by rfl) ⟨3084558, by rfl⟩ : syracuseStep 8225489 = 6169117) B6169117
theorem B9249491 : Blo 1520457 9249491 := bstep (se 1 (by rfl) ⟨6937118, by rfl⟩ : syracuseStep 9249491 = 13874237) B13874237
theorem B4391639 : Blo 1520457 4391639 := bstep (se 1 (by rfl) ⟨3293729, by rfl⟩ : syracuseStep 4391639 = 6587459) B6587459
theorem B5137181 : Blo 1520457 5137181 := bstep (se 3 (by rfl) ⟨963221, by rfl⟩ : syracuseStep 5137181 = 1926443) B1926443
theorem B13001579 : Blo 1520457 13001579 := bstep (se 1 (by rfl) ⟨9751184, by rfl⟩ : syracuseStep 13001579 = 19502369) B19502369
theorem B16442585 : Blo 1520457 16442585 := bstep (se 2 (by rfl) ⟨6165969, by rfl⟩ : syracuseStep 16442585 = 12331939) B12331939
theorem B3294569 : Blo 1520457 3294569 := bstep (se 2 (by rfl) ⟨1235463, by rfl⟩ : syracuseStep 3294569 = 2470927) B2470927
theorem B4334953 : Blo 1520457 4334953 := bstep (se 2 (by rfl) ⟨1625607, by rfl⟩ : syracuseStep 4334953 = 3251215) B3251215
theorem B11552219 : Blo 1520457 11552219 := bstep (se 1 (by rfl) ⟨8664164, by rfl⟩ : syracuseStep 11552219 = 17328329) B17328329
theorem B5137883 : Blo 1520457 5137883 := bstep (se 1 (by rfl) ⟨3853412, by rfl⟩ : syracuseStep 5137883 = 7706825) B7706825
theorem B46827011 : Blo 1520457 46827011 := bstep (se 1 (by rfl) ⟨35120258, by rfl⟩ : syracuseStep 46827011 = 70240517) B70240517
theorem B4335113 : Blo 1520457 4335113 := bstep (se 2 (by rfl) ⟨1625667, by rfl⟩ : syracuseStep 4335113 = 3251335) B3251335
theorem B4335227 : Blo 1520457 4335227 := bstep (se 1 (by rfl) ⟨3251420, by rfl⟩ : syracuseStep 4335227 = 6502841) B6502841
theorem B2565803 : Blo 1520457 2565803 := bstep (se 1 (by rfl) ⟨1924352, by rfl⟩ : syracuseStep 2565803 = 3848705) B3848705
theorem B3851975 : Blo 1520457 3851975 := bstep (se 1 (by rfl) ⟨2888981, by rfl⟩ : syracuseStep 3851975 = 5777963) B5777963
theorem B21989063 : Blo 1520457 21989063 := bstep (se 1 (by rfl) ⟨16491797, by rfl⟩ : syracuseStep 21989063 = 32983595) B32983595
theorem B10962647 : Blo 1520457 10962647 := bstep (se 1 (by rfl) ⟨8221985, by rfl⟩ : syracuseStep 10962647 = 16443971) B16443971
theorem B4335353 : Blo 1520457 4335353 := bstep (se 2 (by rfl) ⟨1625757, by rfl⟩ : syracuseStep 4335353 = 3251515) B3251515
theorem B13002605 : Blo 1520457 13002605 := bstep (se 3 (by rfl) ⟨2437988, by rfl⟩ : syracuseStep 13002605 = 4875977) B4875977
theorem B4941751 : Blo 1520457 4941751 := bstep (se 1 (by rfl) ⟨3706313, by rfl⟩ : syracuseStep 4941751 = 7412627) B7412627
theorem B9742265 : Blo 1520457 9742265 := bstep (se 2 (by rfl) ⟨3653349, by rfl⟩ : syracuseStep 9742265 = 7306699) B7306699
theorem B11552705 : Blo 1520457 11552705 := bstep (se 2 (by rfl) ⟨4332264, by rfl⟩ : syracuseStep 11552705 = 8664529) B8664529
theorem B2312155 : Blo 1520457 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B11560967 : Blo 1520457 11560967 := bstep (se 1 (by rfl) ⟨8670725, by rfl⟩ : syracuseStep 11560967 = 17341451) B17341451
theorem B2566201 : Blo 1520457 2566201 := bstep (se 2 (by rfl) ⟨962325, by rfl⟩ : syracuseStep 2566201 = 1924651) B1924651
theorem B10963021 : Blo 1520457 10963021 := bstep (se 3 (by rfl) ⟨2055566, by rfl⟩ : syracuseStep 10963021 = 4111133) B4111133
theorem B9259123 : Blo 1520457 9259123 := bstep (se 1 (by rfl) ⟨6944342, by rfl⟩ : syracuseStep 9259123 = 13888685) B13888685
theorem B2566343 : Blo 1520457 2566343 := bstep (se 1 (by rfl) ⟨1924757, by rfl⟩ : syracuseStep 2566343 = 3849515) B3849515
theorem B5777675 : Blo 1520457 5777675 := bstep (se 1 (by rfl) ⟨4333256, by rfl⟩ : syracuseStep 5777675 = 8666513) B8666513
theorem B2566505 : Blo 1520457 2566505 := bstep (se 2 (by rfl) ⟨962439, by rfl⟩ : syracuseStep 2566505 = 1924879) B1924879
theorem B29641139 : Blo 1520457 29641139 := bstep (se 1 (by rfl) ⟨22230854, by rfl⟩ : syracuseStep 29641139 = 44461709) B44461709
theorem B2312713 : Blo 1520457 2312713 := bstep (se 2 (by rfl) ⟨867267, by rfl⟩ : syracuseStep 2312713 = 1734535) B1734535
theorem B7703099 : Blo 1520457 7703099 := bstep (se 1 (by rfl) ⟨5777324, by rfl⟩ : syracuseStep 7703099 = 11554649) B11554649
theorem B12511955 : Blo 1520457 12511955 := bstep (se 1 (by rfl) ⟨9383966, by rfl⟩ : syracuseStep 12511955 = 18767933) B18767933
theorem B17337077 : Blo 1520457 17337077 := bstep (se 5 (by rfl) ⟨812675, by rfl⟩ : syracuseStep 17337077 = 1625351) B1625351
theorem B2566903 : Blo 1520457 2566903 := bstep (se 1 (by rfl) ⟨1925177, by rfl⟩ : syracuseStep 2566903 = 3850355) B3850355
theorem B13175581 : Blo 1520457 13175581 := bstep (se 3 (by rfl) ⟨2470421, by rfl⟩ : syracuseStep 13175581 = 4940843) B4940843
theorem B3853129 : Blo 1520457 3853129 := bstep (se 2 (by rfl) ⟨1444923, by rfl⟩ : syracuseStep 3853129 = 2889847) B2889847
theorem B2780087 : Blo 1520457 2780087 := bstep (se 1 (by rfl) ⟨2085065, by rfl⟩ : syracuseStep 2780087 = 4170131) B4170131
theorem B2567099 : Blo 1520457 2567099 := bstep (se 1 (by rfl) ⟨1925324, by rfl⟩ : syracuseStep 2567099 = 3850649) B3850649
theorem B2567207 : Blo 1520457 2567207 := bstep (se 1 (by rfl) ⟨1925405, by rfl⟩ : syracuseStep 2567207 = 3850811) B3850811
theorem B17321039 : Blo 1520457 17321039 := bstep (se 1 (by rfl) ⟨12990779, by rfl⟩ : syracuseStep 17321039 = 25981559) B25981559
theorem B2886779 : Blo 1520457 2886779 := bstep (se 1 (by rfl) ⟨2165084, by rfl⟩ : syracuseStep 2886779 = 4330169) B4330169
theorem B8670361 : Blo 1520457 8670361 := bstep (se 2 (by rfl) ⟨3251385, by rfl⟩ : syracuseStep 8670361 = 6502771) B6502771
theorem B21941441 : Blo 1520457 21941441 := bstep (se 2 (by rfl) ⟨8228040, by rfl⟩ : syracuseStep 21941441 = 16456081) B16456081
theorem B7703747 : Blo 1520457 7703747 := bstep (se 1 (by rfl) ⟨5777810, by rfl⟩ : syracuseStep 7703747 = 11555621) B11555621
theorem B2780407 : Blo 1520457 2780407 := bstep (se 1 (by rfl) ⟨2085305, by rfl⟩ : syracuseStep 2780407 = 4170611) B4170611
theorem B2567497 : Blo 1520457 2567497 := bstep (se 2 (by rfl) ⟨962811, by rfl⟩ : syracuseStep 2567497 = 1925623) B1925623
theorem B2280809 : Blo 1520457 2280809 := bstep (se 2 (by rfl) ⟨855303, by rfl⟩ : syracuseStep 2280809 = 1710607) B1710607
theorem B2567531 : Blo 1520457 2567531 := bstep (se 1 (by rfl) ⟨1925648, by rfl⟩ : syracuseStep 2567531 = 3851297) B3851297
theorem B11554163 : Blo 1520457 11554163 := bstep (se 1 (by rfl) ⟨8665622, by rfl⟩ : syracuseStep 11554163 = 17331245) B17331245
theorem B2280887 : Blo 1520457 2280887 := bstep (se 1 (by rfl) ⟨1710665, by rfl⟩ : syracuseStep 2280887 = 3421331) B3421331
theorem B2280923 : Blo 1520457 2280923 := bstep (se 1 (by rfl) ⟨1710692, by rfl⟩ : syracuseStep 2280923 = 3421385) B3421385
theorem B5131835 : Blo 1520457 5131835 := bstep (se 1 (by rfl) ⟨3848876, by rfl⟩ : syracuseStep 5131835 = 7697753) B7697753
theorem B19484225 : Blo 1520457 19484225 := bstep (se 2 (by rfl) ⟨7306584, by rfl⟩ : syracuseStep 19484225 = 14613169) B14613169
theorem B2887265 : Blo 1520457 2887265 := bstep (se 2 (by rfl) ⟨1082724, by rfl⟩ : syracuseStep 2887265 = 2165449) B2165449
theorem B17329787 : Blo 1520457 17329787 := bstep (se 1 (by rfl) ⟨12997340, by rfl⟩ : syracuseStep 17329787 = 25994681) B25994681
theorem B5779133 : Blo 1520457 5779133 := bstep (se 3 (by rfl) ⟨1083587, by rfl⟩ : syracuseStep 5779133 = 2167175) B2167175
theorem B2887417 : Blo 1520457 2887417 := bstep (se 2 (by rfl) ⟨1082781, by rfl⟩ : syracuseStep 2887417 = 2165563) B2165563
theorem B2567929 : Blo 1520457 2567929 := bstep (se 2 (by rfl) ⟨962973, by rfl⟩ : syracuseStep 2567929 = 1925947) B1925947
theorem B6172409 : Blo 1520457 6172409 := bstep (se 2 (by rfl) ⟨2314653, by rfl⟩ : syracuseStep 6172409 = 4629307) B4629307
theorem B23432975 : Blo 1520457 23432975 := bstep (se 1 (by rfl) ⟨17574731, by rfl⟩ : syracuseStep 23432975 = 35149463) B35149463
theorem B5132105 : Blo 1520457 5132105 := bstep (se 2 (by rfl) ⟨1924539, by rfl⟩ : syracuseStep 5132105 = 3849079) B3849079
theorem B2281391 : Blo 1520457 2281391 := bstep (se 1 (by rfl) ⟨1711043, by rfl⟩ : syracuseStep 2281391 = 3422087) B3422087
theorem B3657655 : Blo 1520457 3657655 := bstep (se 1 (by rfl) ⟨2743241, by rfl⟩ : syracuseStep 3657655 = 5486483) B5486483
theorem B10407865 : Blo 1520457 10407865 := bstep (se 2 (by rfl) ⟨3902949, by rfl⟩ : syracuseStep 10407865 = 7805899) B7805899
theorem B2568199 : Blo 1520457 2568199 := bstep (se 1 (by rfl) ⟨1926149, by rfl⟩ : syracuseStep 2568199 = 3852299) B3852299
theorem B2281481 : Blo 1520457 2281481 := bstep (se 2 (by rfl) ⟨855555, by rfl⟩ : syracuseStep 2281481 = 1711111) B1711111
theorem B2281511 : Blo 1520457 2281511 := bstep (se 1 (by rfl) ⟨1711133, by rfl⟩ : syracuseStep 2281511 = 3422267) B3422267
theorem B2281595 : Blo 1520457 2281595 := bstep (se 1 (by rfl) ⟨1711196, by rfl⟩ : syracuseStep 2281595 = 3422393) B3422393
theorem B2166907 : Blo 1520457 2166907 := bstep (se 1 (by rfl) ⟨1625180, by rfl⟩ : syracuseStep 2166907 = 3250361) B3250361
theorem B2281721 : Blo 1520457 2281721 := bstep (se 2 (by rfl) ⟨855645, by rfl⟩ : syracuseStep 2281721 = 1711291) B1711291
theorem B2281823 : Blo 1520457 2281823 := bstep (se 1 (by rfl) ⟨1711367, by rfl⟩ : syracuseStep 2281823 = 3422735) B3422735
theorem B2281835 : Blo 1520457 2281835 := bstep (se 1 (by rfl) ⟨1711376, by rfl⟩ : syracuseStep 2281835 = 3422753) B3422753
theorem B2568631 : Blo 1520457 2568631 := bstep (se 1 (by rfl) ⟨1926473, by rfl⟩ : syracuseStep 2568631 = 3852947) B3852947
theorem B41619977 : Blo 1520457 41619977 := bstep (se 2 (by rfl) ⟨15607491, by rfl⟩ : syracuseStep 41619977 = 31214983) B31214983
theorem B3904039 : Blo 1520457 3904039 := bstep (se 1 (by rfl) ⟨2928029, by rfl⟩ : syracuseStep 3904039 = 5856059) B5856059
theorem B2282063 : Blo 1520457 2282063 := bstep (se 1 (by rfl) ⟨1711547, by rfl⟩ : syracuseStep 2282063 = 3423095) B3423095
theorem B2568827 : Blo 1520457 2568827 := bstep (se 1 (by rfl) ⟨1926620, by rfl⟩ : syracuseStep 2568827 = 3853241) B3853241
theorem B2282183 : Blo 1520457 2282183 := bstep (se 1 (by rfl) ⟨1711637, by rfl⟩ : syracuseStep 2282183 = 3423275) B3423275
theorem B1520463 : Blo 1520457 1520463 := bstep (se 1 (by rfl) ⟨1140347, by rfl⟩ : syracuseStep 1520463 = 2280695) B2280695
theorem B1520479 : Blo 1520457 1520479 := bstep (se 1 (by rfl) ⟨1140359, by rfl⟩ : syracuseStep 1520479 = 2280719) B2280719
theorem B2282345 : Blo 1520457 2282345 := bstep (se 2 (by rfl) ⟨855879, by rfl⟩ : syracuseStep 2282345 = 1711759) B1711759
theorem B1520507 : Blo 1520457 1520507 := bstep (se 1 (by rfl) ⟨1140380, by rfl⟩ : syracuseStep 1520507 = 2280761) B2280761
theorem B1520559 : Blo 1520457 1520559 := bstep (se 1 (by rfl) ⟨1140419, by rfl⟩ : syracuseStep 1520559 = 2280839) B2280839
theorem B5133239 : Blo 1520457 5133239 := bstep (se 1 (by rfl) ⟨3849929, by rfl⟩ : syracuseStep 5133239 = 7699859) B7699859
theorem B2282423 : Blo 1520457 2282423 := bstep (se 1 (by rfl) ⟨1711817, by rfl⟩ : syracuseStep 2282423 = 3423635) B3423635
theorem B3421115 : Blo 1520457 3421115 := bstep (se 1 (by rfl) ⟨2565836, by rfl⟩ : syracuseStep 3421115 = 5131673) B5131673
theorem B1520583 : Blo 1520457 1520583 := bstep (se 1 (by rfl) ⟨1140437, by rfl⟩ : syracuseStep 1520583 = 2280875) B2280875
theorem B1520603 : Blo 1520457 1520603 := bstep (se 1 (by rfl) ⟨1140452, by rfl⟩ : syracuseStep 1520603 = 2280905) B2280905
theorem B2282459 : Blo 1520457 2282459 := bstep (se 1 (by rfl) ⟨1711844, by rfl⟩ : syracuseStep 2282459 = 3423689) B3423689
theorem B2888723 : Blo 1520457 2888723 := bstep (se 1 (by rfl) ⟨2166542, by rfl⟩ : syracuseStep 2888723 = 4333085) B4333085
theorem B1520679 : Blo 1520457 1520679 := bstep (se 1 (by rfl) ⟨1140509, by rfl⟩ : syracuseStep 1520679 = 2281019) B2281019
theorem B3421241 : Blo 1520457 3421241 := bstep (se 2 (by rfl) ⟨1282965, by rfl⟩ : syracuseStep 3421241 = 2565931) B2565931
theorem B1520719 : Blo 1520457 1520719 := bstep (se 1 (by rfl) ⟨1140539, by rfl⟩ : syracuseStep 1520719 = 2281079) B2281079
theorem B1520735 : Blo 1520457 1520735 := bstep (se 1 (by rfl) ⟨1140551, by rfl⟩ : syracuseStep 1520735 = 2281103) B2281103
theorem B1520763 : Blo 1520457 1520763 := bstep (se 1 (by rfl) ⟨1140572, by rfl⟩ : syracuseStep 1520763 = 2281145) B2281145
theorem B74036375 : Blo 1520457 74036375 := bstep (se 1 (by rfl) ⟨55527281, by rfl⟩ : syracuseStep 74036375 = 111054563) B111054563
theorem B2888875 : Blo 1520457 2888875 := bstep (se 1 (by rfl) ⟨2166656, by rfl⟩ : syracuseStep 2888875 = 4333313) B4333313
theorem B1520815 : Blo 1520457 1520815 := bstep (se 1 (by rfl) ⟨1140611, by rfl⟩ : syracuseStep 1520815 = 2281223) B2281223
theorem B1520839 : Blo 1520457 1520839 := bstep (se 1 (by rfl) ⟨1140629, by rfl⟩ : syracuseStep 1520839 = 2281259) B2281259
theorem B1520859 : Blo 1520457 1520859 := bstep (se 1 (by rfl) ⟨1140644, by rfl⟩ : syracuseStep 1520859 = 2281289) B2281289
theorem B1520935 : Blo 1520457 1520935 := bstep (se 1 (by rfl) ⟨1140701, by rfl⟩ : syracuseStep 1520935 = 2281403) B2281403
theorem B1520975 : Blo 1520457 1520975 := bstep (se 1 (by rfl) ⟨1140731, by rfl⟩ : syracuseStep 1520975 = 2281463) B2281463
theorem B1520991 : Blo 1520457 1520991 := bstep (se 1 (by rfl) ⟨1140743, by rfl⟩ : syracuseStep 1520991 = 2281487) B2281487
theorem B5272937 : Blo 1520457 5272937 := bstep (se 2 (by rfl) ⟨1977351, by rfl⟩ : syracuseStep 5272937 = 3954703) B3954703
theorem B1521019 : Blo 1520457 1521019 := bstep (se 1 (by rfl) ⟨1140764, by rfl⟩ : syracuseStep 1521019 = 2281529) B2281529
theorem B3421583 : Blo 1520457 3421583 := bstep (se 1 (by rfl) ⟨2566187, by rfl⟩ : syracuseStep 3421583 = 5132375) B5132375
theorem B2889103 : Blo 1520457 2889103 := bstep (se 1 (by rfl) ⟨2166827, by rfl⟩ : syracuseStep 2889103 = 4333655) B4333655
theorem B1521071 : Blo 1520457 1521071 := bstep (se 1 (by rfl) ⟨1140803, by rfl⟩ : syracuseStep 1521071 = 2281607) B2281607
theorem B2282927 : Blo 1520457 2282927 := bstep (se 1 (by rfl) ⟨1712195, by rfl⟩ : syracuseStep 2282927 = 3424391) B3424391
theorem B1521095 : Blo 1520457 1521095 := bstep (se 1 (by rfl) ⟨1140821, by rfl⟩ : syracuseStep 1521095 = 2281643) B2281643
theorem B1521115 : Blo 1520457 1521115 := bstep (se 1 (by rfl) ⟨1140836, by rfl⟩ : syracuseStep 1521115 = 2281673) B2281673
theorem B2889179 : Blo 1520457 2889179 := bstep (se 1 (by rfl) ⟨2166884, by rfl⟩ : syracuseStep 2889179 = 4333769) B4333769
theorem B6166003 : Blo 1520457 6166003 := bstep (se 1 (by rfl) ⟨4624502, by rfl⟩ : syracuseStep 6166003 = 9249005) B9249005
theorem B5133833 : Blo 1520457 5133833 := bstep (se 2 (by rfl) ⟨1925187, by rfl⟩ : syracuseStep 5133833 = 3850375) B3850375
theorem B2283017 : Blo 1520457 2283017 := bstep (se 2 (by rfl) ⟨856131, by rfl⟩ : syracuseStep 2283017 = 1712263) B1712263
theorem B1521191 : Blo 1520457 1521191 := bstep (se 1 (by rfl) ⟨1140893, by rfl⟩ : syracuseStep 1521191 = 2281787) B2281787
theorem B2283047 : Blo 1520457 2283047 := bstep (se 1 (by rfl) ⟨1712285, by rfl⟩ : syracuseStep 2283047 = 3424571) B3424571
theorem B15619645 : Blo 1520457 15619645 := bstep (se 3 (by rfl) ⟨2928683, by rfl⟩ : syracuseStep 15619645 = 5857367) B5857367
theorem B1521231 : Blo 1520457 1521231 := bstep (se 1 (by rfl) ⟨1140923, by rfl⟩ : syracuseStep 1521231 = 2281847) B2281847
theorem B1521247 : Blo 1520457 1521247 := bstep (se 1 (by rfl) ⟨1140935, by rfl⟩ : syracuseStep 1521247 = 2281871) B2281871
theorem B1521275 : Blo 1520457 1521275 := bstep (se 1 (by rfl) ⟨1140956, by rfl⟩ : syracuseStep 1521275 = 2281913) B2281913
theorem B2283131 : Blo 1520457 2283131 := bstep (se 1 (by rfl) ⟨1712348, by rfl⟩ : syracuseStep 2283131 = 3424697) B3424697
theorem B1521327 : Blo 1520457 1521327 := bstep (se 1 (by rfl) ⟨1140995, by rfl⟩ : syracuseStep 1521327 = 2281991) B2281991
theorem B1521351 : Blo 1520457 1521351 := bstep (se 1 (by rfl) ⟨1141013, by rfl⟩ : syracuseStep 1521351 = 2282027) B2282027
theorem B3421907 : Blo 1520457 3421907 := bstep (se 1 (by rfl) ⟨2566430, by rfl⟩ : syracuseStep 3421907 = 5132861) B5132861
theorem B3249875 : Blo 1520457 3249875 := bstep (se 1 (by rfl) ⟨2437406, by rfl⟩ : syracuseStep 3249875 = 4874813) B4874813
theorem B1521371 : Blo 1520457 1521371 := bstep (se 1 (by rfl) ⟨1141028, by rfl⟩ : syracuseStep 1521371 = 2282057) B2282057
theorem B2283257 : Blo 1520457 2283257 := bstep (se 2 (by rfl) ⟨856221, by rfl⟩ : syracuseStep 2283257 = 1712443) B1712443
theorem B1521447 : Blo 1520457 1521447 := bstep (se 1 (by rfl) ⟨1141085, by rfl⟩ : syracuseStep 1521447 = 2282171) B2282171
theorem B1521487 : Blo 1520457 1521487 := bstep (se 1 (by rfl) ⟨1141115, by rfl⟩ : syracuseStep 1521487 = 2282231) B2282231
theorem B1521503 : Blo 1520457 1521503 := bstep (se 1 (by rfl) ⟨1141127, by rfl⟩ : syracuseStep 1521503 = 2282255) B2282255
theorem B2283359 : Blo 1520457 2283359 := bstep (se 1 (by rfl) ⟨1712519, by rfl⟩ : syracuseStep 2283359 = 3425039) B3425039
theorem B2283371 : Blo 1520457 2283371 := bstep (se 1 (by rfl) ⟨1712528, by rfl⟩ : syracuseStep 2283371 = 3425057) B3425057
theorem B1521531 : Blo 1520457 1521531 := bstep (se 1 (by rfl) ⟨1141148, by rfl⟩ : syracuseStep 1521531 = 2282297) B2282297
theorem B1521583 : Blo 1520457 1521583 := bstep (se 1 (by rfl) ⟨1141187, by rfl⟩ : syracuseStep 1521583 = 2282375) B2282375
theorem B1521607 : Blo 1520457 1521607 := bstep (se 1 (by rfl) ⟨1141205, by rfl⟩ : syracuseStep 1521607 = 2282411) B2282411
theorem B1521627 : Blo 1520457 1521627 := bstep (se 1 (by rfl) ⟨1141220, by rfl⟩ : syracuseStep 1521627 = 2282441) B2282441
theorem B1521703 : Blo 1520457 1521703 := bstep (se 1 (by rfl) ⟨1141277, by rfl⟩ : syracuseStep 1521703 = 2282555) B2282555
theorem B7313465 : Blo 1520457 7313465 := bstep (se 2 (by rfl) ⟨2742549, by rfl⟩ : syracuseStep 7313465 = 5485099) B5485099
theorem B1521743 : Blo 1520457 1521743 := bstep (se 1 (by rfl) ⟨1141307, by rfl⟩ : syracuseStep 1521743 = 2282615) B2282615
theorem B2283599 : Blo 1520457 2283599 := bstep (se 1 (by rfl) ⟨1712699, by rfl⟩ : syracuseStep 2283599 = 3425399) B3425399
theorem B1521759 : Blo 1520457 1521759 := bstep (se 1 (by rfl) ⟨1141319, by rfl⟩ : syracuseStep 1521759 = 2282639) B2282639
theorem B1521787 : Blo 1520457 1521787 := bstep (se 1 (by rfl) ⟨1141340, by rfl⟩ : syracuseStep 1521787 = 2282681) B2282681
theorem B1521839 : Blo 1520457 1521839 := bstep (se 1 (by rfl) ⟨1141379, by rfl⟩ : syracuseStep 1521839 = 2282759) B2282759
theorem B1521863 : Blo 1520457 1521863 := bstep (se 1 (by rfl) ⟨1141397, by rfl⟩ : syracuseStep 1521863 = 2282795) B2282795
theorem B1521883 : Blo 1520457 1521883 := bstep (se 1 (by rfl) ⟨1141412, by rfl⟩ : syracuseStep 1521883 = 2282825) B2282825
theorem B1521959 : Blo 1520457 1521959 := bstep (se 1 (by rfl) ⟨1141469, by rfl⟩ : syracuseStep 1521959 = 2282939) B2282939
theorem B2742601 : Blo 1520457 2742601 := bstep (se 2 (by rfl) ⟨1028475, by rfl⟩ : syracuseStep 2742601 = 2056951) B2056951
theorem B1521999 : Blo 1520457 1521999 := bstep (se 1 (by rfl) ⟨1141499, by rfl⟩ : syracuseStep 1521999 = 2282999) B2282999
theorem B1522015 : Blo 1520457 1522015 := bstep (se 1 (by rfl) ⟨1141511, by rfl⟩ : syracuseStep 1522015 = 2283023) B2283023
theorem B5134697 : Blo 1520457 5134697 := bstep (se 2 (by rfl) ⟨1925511, by rfl⟩ : syracuseStep 5134697 = 3851023) B3851023
theorem B1522043 : Blo 1520457 1522043 := bstep (se 1 (by rfl) ⟨1141532, by rfl⟩ : syracuseStep 1522043 = 2283065) B2283065
theorem B1522095 : Blo 1520457 1522095 := bstep (se 1 (by rfl) ⟨1141571, by rfl⟩ : syracuseStep 1522095 = 2283143) B2283143
theorem B1522119 : Blo 1520457 1522119 := bstep (se 1 (by rfl) ⟨1141589, by rfl⟩ : syracuseStep 1522119 = 2283179) B2283179
theorem B5773787 : Blo 1520457 5773787 := bstep (se 1 (by rfl) ⟨4330340, by rfl⟩ : syracuseStep 5773787 = 8660681) B8660681
theorem B1522139 : Blo 1520457 1522139 := bstep (se 1 (by rfl) ⟨1141604, by rfl⟩ : syracuseStep 1522139 = 2283209) B2283209
theorem B8223241 : Blo 1520457 8223241 := bstep (se 2 (by rfl) ⟨3083715, by rfl⟩ : syracuseStep 8223241 = 6167431) B6167431
theorem B1522215 : Blo 1520457 1522215 := bstep (se 1 (by rfl) ⟨1141661, by rfl⟩ : syracuseStep 1522215 = 2283323) B2283323
theorem B1522255 : Blo 1520457 1522255 := bstep (se 1 (by rfl) ⟨1141691, by rfl⟩ : syracuseStep 1522255 = 2283383) B2283383
theorem B1522271 : Blo 1520457 1522271 := bstep (se 1 (by rfl) ⟨1141703, by rfl⟩ : syracuseStep 1522271 = 2283407) B2283407
theorem B1710715 : Blo 1520457 1710715 := bstep (se 1 (by rfl) ⟨1283036, by rfl⟩ : syracuseStep 1710715 = 2566073) B2566073
theorem B3422843 : Blo 1520457 3422843 := bstep (se 1 (by rfl) ⟨2567132, by rfl⟩ : syracuseStep 3422843 = 5134265) B5134265
theorem B1522299 : Blo 1520457 1522299 := bstep (se 1 (by rfl) ⟨1141724, by rfl⟩ : syracuseStep 1522299 = 2283449) B2283449
theorem B1522351 : Blo 1520457 1522351 := bstep (se 1 (by rfl) ⟨1141763, by rfl⟩ : syracuseStep 1522351 = 2283527) B2283527
theorem B1522375 : Blo 1520457 1522375 := bstep (se 1 (by rfl) ⟨1141781, by rfl⟩ : syracuseStep 1522375 = 2283563) B2283563
theorem B1522395 : Blo 1520457 1522395 := bstep (se 1 (by rfl) ⟨1141796, by rfl⟩ : syracuseStep 1522395 = 2283593) B2283593
theorem B3422969 : Blo 1520457 3422969 := bstep (se 2 (by rfl) ⟨1283613, by rfl⟩ : syracuseStep 3422969 = 2567227) B2567227
theorem B5135291 : Blo 1520457 5135291 := bstep (se 1 (by rfl) ⟨3851468, by rfl⟩ : syracuseStep 5135291 = 7702937) B7702937
theorem B3423239 : Blo 1520457 3423239 := bstep (se 1 (by rfl) ⟨2567429, by rfl⟩ : syracuseStep 3423239 = 5134859) B5134859
theorem B7699535 : Blo 1520457 7699535 := bstep (se 1 (by rfl) ⟨5774651, by rfl⟩ : syracuseStep 7699535 = 11549303) B11549303
theorem B1711183 : Blo 1520457 1711183 := bstep (se 1 (by rfl) ⟨1283387, by rfl⟩ : syracuseStep 1711183 = 2566775) B2566775
theorem B3423311 : Blo 1520457 3423311 := bstep (se 1 (by rfl) ⟨2567483, by rfl⟩ : syracuseStep 3423311 = 5134967) B5134967
theorem B12344399 : Blo 1520457 12344399 := bstep (se 1 (by rfl) ⟨9258299, by rfl⟩ : syracuseStep 12344399 = 18516599) B18516599
theorem B19758275 : Blo 1520457 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B6167819 : Blo 1520457 6167819 := bstep (se 1 (by rfl) ⟨4625864, by rfl⟩ : syracuseStep 6167819 = 9251729) B9251729
theorem B1711579 : Blo 1520457 1711579 := bstep (se 1 (by rfl) ⟨1283684, by rfl⟩ : syracuseStep 1711579 = 2567369) B2567369
theorem B3423707 : Blo 1520457 3423707 := bstep (se 1 (by rfl) ⟨2567780, by rfl⟩ : syracuseStep 3423707 = 5135561) B5135561
theorem B19488221 : Blo 1520457 19488221 := bstep (se 3 (by rfl) ⟨3654041, by rfl⟩ : syracuseStep 19488221 = 7308083) B7308083
theorem B5775047 : Blo 1520457 5775047 := bstep (se 1 (by rfl) ⟨4331285, by rfl⟩ : syracuseStep 5775047 = 8662571) B8662571
theorem B4939463 : Blo 1520457 4939463 := bstep (se 1 (by rfl) ⟨3704597, by rfl⟩ : syracuseStep 4939463 = 7409195) B7409195
theorem B4873927 : Blo 1520457 4873927 := bstep (se 1 (by rfl) ⟨3655445, by rfl⟩ : syracuseStep 4873927 = 7310891) B7310891
theorem B4333267 : Blo 1520457 4333267 := bstep (se 1 (by rfl) ⟨3249950, by rfl⟩ : syracuseStep 4333267 = 6499901) B6499901
theorem B7700183 : Blo 1520457 7700183 := bstep (se 1 (by rfl) ⟨5775137, by rfl⟩ : syracuseStep 7700183 = 11550275) B11550275
theorem B6496109 : Blo 1520457 6496109 := bstep (se 3 (by rfl) ⟨1218020, by rfl⟩ : syracuseStep 6496109 = 2436041) B2436041
theorem B21938039 : Blo 1520457 21938039 := bstep (se 1 (by rfl) ⟨16453529, by rfl⟩ : syracuseStep 21938039 = 32907059) B32907059
theorem B1712047 : Blo 1520457 1712047 := bstep (se 1 (by rfl) ⟨1284035, by rfl⟩ : syracuseStep 1712047 = 2568071) B2568071
theorem B3424175 : Blo 1520457 3424175 := bstep (se 1 (by rfl) ⟨2568131, by rfl⟩ : syracuseStep 3424175 = 5136263) B5136263
theorem B4333495 : Blo 1520457 4333495 := bstep (se 1 (by rfl) ⟨3250121, by rfl⟩ : syracuseStep 4333495 = 6500243) B6500243
theorem B3424265 : Blo 1520457 3424265 := bstep (se 2 (by rfl) ⟨1284099, by rfl⟩ : syracuseStep 3424265 = 2568199) B2568199
theorem B12345497 : Blo 1520457 12345497 := bstep (se 2 (by rfl) ⟨4629561, by rfl⟩ : syracuseStep 12345497 = 9259123) B9259123
theorem B27746651 : Blo 1520457 27746651 := bstep (se 1 (by rfl) ⟨20809988, by rfl⟩ : syracuseStep 27746651 = 41619977) B41619977
theorem B14614937 : Blo 1520457 14614937 := bstep (se 2 (by rfl) ⟨5480601, by rfl⟩ : syracuseStep 14614937 = 10961203) B10961203
theorem B3424679 : Blo 1520457 3424679 := bstep (se 1 (by rfl) ⟨2568509, by rfl⟩ : syracuseStep 3424679 = 5137019) B5137019
theorem B1712551 : Blo 1520457 1712551 := bstep (se 1 (by rfl) ⟨1284413, by rfl⟩ : syracuseStep 1712551 = 2568827) B2568827
theorem B3850679 : Blo 1520457 3850679 := bstep (se 1 (by rfl) ⟨2888009, by rfl⟩ : syracuseStep 3850679 = 5776019) B5776019
theorem B7700993 : Blo 1520457 7700993 := bstep (se 2 (by rfl) ⟨2887872, by rfl⟩ : syracuseStep 7700993 = 5775745) B5775745
theorem B3424787 : Blo 1520457 3424787 := bstep (se 1 (by rfl) ⟨2568590, by rfl⟩ : syracuseStep 3424787 = 5137181) B5137181
theorem B8667719 : Blo 1520457 8667719 := bstep (se 1 (by rfl) ⟨6500789, by rfl⟩ : syracuseStep 8667719 = 13001579) B13001579
theorem B3424841 : Blo 1520457 3424841 := bstep (se 2 (by rfl) ⟨1284315, by rfl⟩ : syracuseStep 3424841 = 2568631) B2568631
theorem B7307929 : Blo 1520457 7307929 := bstep (se 2 (by rfl) ⟨2740473, by rfl⟩ : syracuseStep 7307929 = 5480947) B5480947
theorem B49357583 : Blo 1520457 49357583 := bstep (se 1 (by rfl) ⟨37018187, by rfl⟩ : syracuseStep 49357583 = 74036375) B74036375
theorem B10961723 : Blo 1520457 10961723 := bstep (se 1 (by rfl) ⟨8221292, by rfl⟩ : syracuseStep 10961723 = 16442585) B16442585
theorem B3515291 : Blo 1520457 3515291 := bstep (se 1 (by rfl) ⟨2636468, by rfl⟩ : syracuseStep 3515291 = 5272937) B5272937
theorem B2196379 : Blo 1520457 2196379 := bstep (se 1 (by rfl) ⟨1647284, by rfl⟩ : syracuseStep 2196379 = 3294569) B3294569
theorem B7701479 : Blo 1520457 7701479 := bstep (se 1 (by rfl) ⟨5776109, by rfl⟩ : syracuseStep 7701479 = 11552219) B11552219
theorem B1926119 : Blo 1520457 1926119 := bstep (se 1 (by rfl) ⟨1444589, by rfl⟩ : syracuseStep 1926119 = 2889179) B2889179
theorem B3425255 : Blo 1520457 3425255 := bstep (se 1 (by rfl) ⟨2568941, by rfl⟩ : syracuseStep 3425255 = 5137883) B5137883
theorem B5137505 : Blo 1520457 5137505 := bstep (se 2 (by rfl) ⟨1926564, by rfl⟩ : syracuseStep 5137505 = 3853129) B3853129
theorem B7308431 : Blo 1520457 7308431 := bstep (se 1 (by rfl) ⟨5481323, by rfl⟩ : syracuseStep 7308431 = 10962647) B10962647
theorem B8668403 : Blo 1520457 8668403 := bstep (se 1 (by rfl) ⟨6501302, by rfl⟩ : syracuseStep 8668403 = 13002605) B13002605
theorem B7701803 : Blo 1520457 7701803 := bstep (se 1 (by rfl) ⟨5776352, by rfl⟩ : syracuseStep 7701803 = 11552705) B11552705
theorem B124872029 : Blo 1520457 124872029 := bstep (se 3 (by rfl) ⟨23413505, by rfl⟩ : syracuseStep 124872029 = 46827011) B46827011
theorem B4875643 : Blo 1520457 4875643 := bstep (se 1 (by rfl) ⟨3656732, by rfl⟩ : syracuseStep 4875643 = 7313465) B7313465
theorem B3851783 : Blo 1520457 3851783 := bstep (se 1 (by rfl) ⟨2888837, by rfl⟩ : syracuseStep 3851783 = 5777675) B5777675
theorem B11560481 : Blo 1520457 11560481 := bstep (se 2 (by rfl) ⟨4335180, by rfl⟩ : syracuseStep 11560481 = 8670361) B8670361
theorem B3851833 : Blo 1520457 3851833 := bstep (se 2 (by rfl) ⟨1444437, by rfl⟩ : syracuseStep 3851833 = 2888875) B2888875
theorem B19760759 : Blo 1520457 19760759 := bstep (se 1 (by rfl) ⟨14820569, by rfl⟩ : syracuseStep 19760759 = 29641139) B29641139
theorem B3852137 : Blo 1520457 3852137 := bstep (se 2 (by rfl) ⟨1444551, by rfl⟩ : syracuseStep 3852137 = 2889103) B2889103
theorem B16459757 : Blo 1520457 16459757 := bstep (se 3 (by rfl) ⟨3086204, by rfl⟩ : syracuseStep 16459757 = 6172409) B6172409
theorem B20826193 : Blo 1520457 20826193 := bstep (se 2 (by rfl) ⟨7809822, by rfl⟩ : syracuseStep 20826193 = 15619645) B15619645
theorem B7702775 : Blo 1520457 7702775 := bstep (se 1 (by rfl) ⟨5777081, by rfl⟩ : syracuseStep 7702775 = 11554163) B11554163
theorem B6498569 : Blo 1520457 6498569 := bstep (se 2 (by rfl) ⟨2436963, by rfl⟩ : syracuseStep 6498569 = 4873927) B4873927
theorem B5777689 : Blo 1520457 5777689 := bstep (se 2 (by rfl) ⟨2166633, by rfl⟩ : syracuseStep 5777689 = 4333267) B4333267
theorem B19507493 : Blo 1520457 19507493 := bstep (se 4 (by rfl) ⟨1828827, by rfl⟩ : syracuseStep 19507493 = 3657655) B3657655
theorem B11553191 : Blo 1520457 11553191 := bstep (se 1 (by rfl) ⟨8664893, by rfl⟩ : syracuseStep 11553191 = 17329787) B17329787
theorem B3852755 : Blo 1520457 3852755 := bstep (se 1 (by rfl) ⟨2889566, by rfl⟩ : syracuseStep 3852755 = 5779133) B5779133
theorem B5777993 : Blo 1520457 5777993 := bstep (se 2 (by rfl) ⟨2166747, by rfl⟩ : syracuseStep 5777993 = 4333495) B4333495
theorem B6589001 : Blo 1520457 6589001 := bstep (se 2 (by rfl) ⟨2470875, by rfl⟩ : syracuseStep 6589001 = 4941751) B4941751
theorem B14625359 : Blo 1520457 14625359 := bstep (se 1 (by rfl) ⟨10969019, by rfl⟩ : syracuseStep 14625359 = 21938039) B21938039
theorem B3082873 : Blo 1520457 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B7703261 : Blo 1520457 7703261 := bstep (se 3 (by rfl) ⟨1444361, by rfl⟩ : syracuseStep 7703261 = 2888723) B2888723
theorem B14617361 : Blo 1520457 14617361 := bstep (se 2 (by rfl) ⟨5481510, by rfl⟩ : syracuseStep 14617361 = 10963021) B10963021
theorem B2566991 : Blo 1520457 2566991 := bstep (se 1 (by rfl) ⟨1925243, by rfl⟩ : syracuseStep 2566991 = 3850487) B3850487
theorem B3656801 : Blo 1520457 3656801 := bstep (se 2 (by rfl) ⟨1371300, by rfl⟩ : syracuseStep 3656801 = 2742601) B2742601
theorem B5483659 : Blo 1520457 5483659 := bstep (se 1 (by rfl) ⟨4112744, by rfl⟩ : syracuseStep 5483659 = 8225489) B8225489
theorem B2927759 : Blo 1520457 2927759 := bstep (se 1 (by rfl) ⟨2195819, by rfl⟩ : syracuseStep 2927759 = 4391639) B4391639
theorem B2280743 : Blo 1520457 2280743 := bstep (se 1 (by rfl) ⟨1710557, by rfl⟩ : syracuseStep 2280743 = 3421115) B3421115
theorem B3083617 : Blo 1520457 3083617 := bstep (se 2 (by rfl) ⟨1156356, by rfl⟩ : syracuseStep 3083617 = 2312713) B2312713
theorem B10964321 : Blo 1520457 10964321 := bstep (se 2 (by rfl) ⟨4111620, by rfl⟩ : syracuseStep 10964321 = 8223241) B8223241
theorem B2280827 : Blo 1520457 2280827 := bstep (se 1 (by rfl) ⟨1710620, by rfl⟩ : syracuseStep 2280827 = 3421241) B3421241
theorem B5205385 : Blo 1520457 5205385 := bstep (se 2 (by rfl) ⟨1952019, by rfl⟩ : syracuseStep 5205385 = 3904039) B3904039
theorem B2280953 : Blo 1520457 2280953 := bstep (se 2 (by rfl) ⟨855357, by rfl⟩ : syracuseStep 2280953 = 1710715) B1710715
theorem B2281055 : Blo 1520457 2281055 := bstep (se 1 (by rfl) ⟨1710791, by rfl⟩ : syracuseStep 2281055 = 3421583) B3421583
theorem B17567441 : Blo 1520457 17567441 := bstep (se 2 (by rfl) ⟨6587790, by rfl⟩ : syracuseStep 17567441 = 13175581) B13175581
theorem B2567983 : Blo 1520457 2567983 := bstep (se 1 (by rfl) ⟨1925987, by rfl⟩ : syracuseStep 2567983 = 3851975) B3851975
theorem B14659375 : Blo 1520457 14659375 := bstep (se 1 (by rfl) ⟨10994531, by rfl⟩ : syracuseStep 14659375 = 21989063) B21989063
theorem B2281271 : Blo 1520457 2281271 := bstep (se 1 (by rfl) ⟨1710953, by rfl⟩ : syracuseStep 2281271 = 3421907) B3421907
theorem B2166583 : Blo 1520457 2166583 := bstep (se 1 (by rfl) ⟨1624937, by rfl⟩ : syracuseStep 2166583 = 3249875) B3249875
theorem B2281577 : Blo 1520457 2281577 := bstep (se 2 (by rfl) ⟨855591, by rfl⟩ : syracuseStep 2281577 = 1711183) B1711183
theorem B3707209 : Blo 1520457 3707209 := bstep (se 2 (by rfl) ⟨1390203, by rfl⟩ : syracuseStep 3707209 = 2780407) B2780407
theorem B2281895 : Blo 1520457 2281895 := bstep (se 1 (by rfl) ⟨1711421, by rfl⟩ : syracuseStep 2281895 = 3422843) B3422843
theorem B5779937 : Blo 1520457 5779937 := bstep (se 2 (by rfl) ⟨2167476, by rfl⟩ : syracuseStep 5779937 = 4334953) B4334953
theorem B2281979 : Blo 1520457 2281979 := bstep (se 1 (by rfl) ⟨1711484, by rfl⟩ : syracuseStep 2281979 = 3422969) B3422969
theorem B2282105 : Blo 1520457 2282105 := bstep (se 2 (by rfl) ⟨855789, by rfl⟩ : syracuseStep 2282105 = 1711579) B1711579
theorem B8221337 : Blo 1520457 8221337 := bstep (se 2 (by rfl) ⟨3083001, by rfl⟩ : syracuseStep 8221337 = 6166003) B6166003
theorem B2282159 : Blo 1520457 2282159 := bstep (se 1 (by rfl) ⟨1711619, by rfl⟩ : syracuseStep 2282159 = 3423239) B3423239
theorem B11547359 : Blo 1520457 11547359 := bstep (se 1 (by rfl) ⟨8660519, by rfl⟩ : syracuseStep 11547359 = 17321039) B17321039
theorem B5133023 : Blo 1520457 5133023 := bstep (se 1 (by rfl) ⟨3849767, by rfl⟩ : syracuseStep 5133023 = 7699535) B7699535
theorem B2282207 : Blo 1520457 2282207 := bstep (se 1 (by rfl) ⟨1711655, by rfl⟩ : syracuseStep 2282207 = 3423311) B3423311
theorem B8229599 : Blo 1520457 8229599 := bstep (se 1 (by rfl) ⟨6172199, by rfl⟩ : syracuseStep 8229599 = 12344399) B12344399
theorem B14627627 : Blo 1520457 14627627 := bstep (se 1 (by rfl) ⟨10970720, by rfl⟩ : syracuseStep 14627627 = 21941441) B21941441
theorem B1520539 : Blo 1520457 1520539 := bstep (se 1 (by rfl) ⟨1140404, by rfl⟩ : syracuseStep 1520539 = 2280809) B2280809
theorem B1520591 : Blo 1520457 1520591 := bstep (se 1 (by rfl) ⟨1140443, by rfl⟩ : syracuseStep 1520591 = 2280887) B2280887
theorem B1520615 : Blo 1520457 1520615 := bstep (se 1 (by rfl) ⟨1140461, by rfl⟩ : syracuseStep 1520615 = 2280923) B2280923
theorem B2282471 : Blo 1520457 2282471 := bstep (se 1 (by rfl) ⟨1711853, by rfl⟩ : syracuseStep 2282471 = 3423707) B3423707
theorem B3421223 : Blo 1520457 3421223 := bstep (se 1 (by rfl) ⟨2565917, by rfl⟩ : syracuseStep 3421223 = 5131835) B5131835
theorem B12989483 : Blo 1520457 12989483 := bstep (se 1 (by rfl) ⟨9742112, by rfl⟩ : syracuseStep 12989483 = 19484225) B19484225
theorem B5133455 : Blo 1520457 5133455 := bstep (se 1 (by rfl) ⟨3850091, by rfl⟩ : syracuseStep 5133455 = 7700183) B7700183
theorem B3421403 : Blo 1520457 3421403 := bstep (se 1 (by rfl) ⟨2566052, by rfl⟩ : syracuseStep 3421403 = 5132105) B5132105
theorem B2282729 : Blo 1520457 2282729 := bstep (se 2 (by rfl) ⟨856023, by rfl⟩ : syracuseStep 2282729 = 1712047) B1712047
theorem B4330739 : Blo 1520457 4330739 := bstep (se 1 (by rfl) ⟨3248054, by rfl⟩ : syracuseStep 4330739 = 6496109) B6496109
theorem B1520927 : Blo 1520457 1520927 := bstep (se 1 (by rfl) ⟨1140695, by rfl⟩ : syracuseStep 1520927 = 2281391) B2281391
theorem B2282783 : Blo 1520457 2282783 := bstep (se 1 (by rfl) ⟨1712087, by rfl⟩ : syracuseStep 2282783 = 3424175) B3424175
theorem B1520987 : Blo 1520457 1520987 := bstep (se 1 (by rfl) ⟨1140740, by rfl⟩ : syracuseStep 1520987 = 2281481) B2281481
theorem B1521007 : Blo 1520457 1521007 := bstep (se 1 (by rfl) ⟨1140755, by rfl⟩ : syracuseStep 1521007 = 2281511) B2281511
theorem B3421601 : Blo 1520457 3421601 := bstep (se 2 (by rfl) ⟨1283100, by rfl⟩ : syracuseStep 3421601 = 2566201) B2566201
theorem B1521063 : Blo 1520457 1521063 := bstep (se 1 (by rfl) ⟨1140797, by rfl⟩ : syracuseStep 1521063 = 2281595) B2281595
theorem B2282951 : Blo 1520457 2282951 := bstep (se 1 (by rfl) ⟨1712213, by rfl⟩ : syracuseStep 2282951 = 3424427) B3424427
theorem B2889209 : Blo 1520457 2889209 := bstep (se 2 (by rfl) ⟨1083453, by rfl⟩ : syracuseStep 2889209 = 2166907) B2166907
theorem B1521147 : Blo 1520457 1521147 := bstep (se 1 (by rfl) ⟨1140860, by rfl⟩ : syracuseStep 1521147 = 2281721) B2281721
theorem B1521215 : Blo 1520457 1521215 := bstep (se 1 (by rfl) ⟨1140911, by rfl⟩ : syracuseStep 1521215 = 2281823) B2281823
theorem B1521223 : Blo 1520457 1521223 := bstep (se 1 (by rfl) ⟨1140917, by rfl⟩ : syracuseStep 1521223 = 2281835) B2281835
theorem B32921153 : Blo 1520457 32921153 := bstep (se 2 (by rfl) ⟨12345432, by rfl⟩ : syracuseStep 32921153 = 24690865) B24690865
theorem B7698077 : Blo 1520457 7698077 := bstep (se 3 (by rfl) ⟨1443389, by rfl⟩ : syracuseStep 7698077 = 2886779) B2886779
theorem B4331195 : Blo 1520457 4331195 := bstep (se 1 (by rfl) ⟨3248396, by rfl⟩ : syracuseStep 4331195 = 6496793) B6496793
theorem B1521375 : Blo 1520457 1521375 := bstep (se 1 (by rfl) ⟨1141031, by rfl⟩ : syracuseStep 1521375 = 2282063) B2282063
theorem B2283305 : Blo 1520457 2283305 := bstep (se 2 (by rfl) ⟨856239, by rfl⟩ : syracuseStep 2283305 = 1712479) B1712479
theorem B1521455 : Blo 1520457 1521455 := bstep (se 1 (by rfl) ⟨1141091, by rfl⟩ : syracuseStep 1521455 = 2282183) B2282183
theorem B2283311 : Blo 1520457 2283311 := bstep (se 1 (by rfl) ⟨1712483, by rfl⟩ : syracuseStep 2283311 = 3424967) B3424967
theorem B6166327 : Blo 1520457 6166327 := bstep (se 1 (by rfl) ⟨4624745, by rfl⟩ : syracuseStep 6166327 = 9249491) B9249491
theorem B1521563 : Blo 1520457 1521563 := bstep (se 1 (by rfl) ⟨1141172, by rfl⟩ : syracuseStep 1521563 = 2282345) B2282345
theorem B3422159 : Blo 1520457 3422159 := bstep (se 1 (by rfl) ⟨2566619, by rfl⟩ : syracuseStep 3422159 = 5133239) B5133239
theorem B1521615 : Blo 1520457 1521615 := bstep (se 1 (by rfl) ⟨1141211, by rfl⟩ : syracuseStep 1521615 = 2282423) B2282423
theorem B1521639 : Blo 1520457 1521639 := bstep (se 1 (by rfl) ⟨1141229, by rfl⟩ : syracuseStep 1521639 = 2282459) B2282459
theorem B5134589 : Blo 1520457 5134589 := bstep (se 3 (by rfl) ⟨962735, by rfl⟩ : syracuseStep 5134589 = 1925471) B1925471
theorem B1521951 : Blo 1520457 1521951 := bstep (se 1 (by rfl) ⟨1141463, by rfl⟩ : syracuseStep 1521951 = 2282927) B2282927
theorem B3422537 : Blo 1520457 3422537 := bstep (se 2 (by rfl) ⟨1283451, by rfl⟩ : syracuseStep 3422537 = 2566903) B2566903
theorem B3422555 : Blo 1520457 3422555 := bstep (se 1 (by rfl) ⟨2566916, by rfl⟩ : syracuseStep 3422555 = 5133833) B5133833
theorem B1522011 : Blo 1520457 1522011 := bstep (se 1 (by rfl) ⟨1141508, by rfl⟩ : syracuseStep 1522011 = 2283017) B2283017
theorem B2890075 : Blo 1520457 2890075 := bstep (se 1 (by rfl) ⟨2167556, by rfl⟩ : syracuseStep 2890075 = 4335113) B4335113
theorem B1522031 : Blo 1520457 1522031 := bstep (se 1 (by rfl) ⟨1141523, by rfl⟩ : syracuseStep 1522031 = 2283047) B2283047
theorem B1522087 : Blo 1520457 1522087 := bstep (se 1 (by rfl) ⟨1141565, by rfl⟩ : syracuseStep 1522087 = 2283131) B2283131
theorem B2890151 : Blo 1520457 2890151 := bstep (se 1 (by rfl) ⟨2167613, by rfl⟩ : syracuseStep 2890151 = 4335227) B4335227
theorem B1710535 : Blo 1520457 1710535 := bstep (se 1 (by rfl) ⟨1282901, by rfl⟩ : syracuseStep 1710535 = 2565803) B2565803
theorem B1522171 : Blo 1520457 1522171 := bstep (se 1 (by rfl) ⟨1141628, by rfl⟩ : syracuseStep 1522171 = 2283257) B2283257
theorem B2890235 : Blo 1520457 2890235 := bstep (se 1 (by rfl) ⟨2167676, by rfl⟩ : syracuseStep 2890235 = 4335353) B4335353
theorem B1522239 : Blo 1520457 1522239 := bstep (se 1 (by rfl) ⟨1141679, by rfl⟩ : syracuseStep 1522239 = 2283359) B2283359
theorem B1522247 : Blo 1520457 1522247 := bstep (se 1 (by rfl) ⟨1141685, by rfl⟩ : syracuseStep 1522247 = 2283371) B2283371
theorem B6494843 : Blo 1520457 6494843 := bstep (se 1 (by rfl) ⟨4871132, by rfl⟩ : syracuseStep 6494843 = 9742265) B9742265
theorem B7707311 : Blo 1520457 7707311 := bstep (se 1 (by rfl) ⟨5780483, by rfl⟩ : syracuseStep 7707311 = 11560967) B11560967
theorem B1522399 : Blo 1520457 1522399 := bstep (se 1 (by rfl) ⟨1141799, by rfl⟩ : syracuseStep 1522399 = 2283599) B2283599
theorem B1710895 : Blo 1520457 1710895 := bstep (se 1 (by rfl) ⟨1283171, by rfl⟩ : syracuseStep 1710895 = 2566343) B2566343
theorem B1711003 : Blo 1520457 1711003 := bstep (se 1 (by rfl) ⟨1283252, by rfl⟩ : syracuseStep 1711003 = 2566505) B2566505
theorem B3423131 : Blo 1520457 3423131 := bstep (se 1 (by rfl) ⟨2567348, by rfl⟩ : syracuseStep 3423131 = 5134697) B5134697
theorem B7699373 : Blo 1520457 7699373 := bstep (se 3 (by rfl) ⟨1443632, by rfl⟩ : syracuseStep 7699373 = 2887265) B2887265
theorem B3849191 : Blo 1520457 3849191 := bstep (se 1 (by rfl) ⟨2886893, by rfl⟩ : syracuseStep 3849191 = 5773787) B5773787
theorem B5135399 : Blo 1520457 5135399 := bstep (se 1 (by rfl) ⟨3851549, by rfl⟩ : syracuseStep 5135399 = 7703099) B7703099
theorem B3423329 : Blo 1520457 3423329 := bstep (se 2 (by rfl) ⟨1283748, by rfl⟩ : syracuseStep 3423329 = 2567497) B2567497
theorem B11558051 : Blo 1520457 11558051 := bstep (se 1 (by rfl) ⟨8668538, by rfl⟩ : syracuseStep 11558051 = 17337077) B17337077
theorem B33365213 : Blo 1520457 33365213 := bstep (se 3 (by rfl) ⟨6255977, by rfl⟩ : syracuseStep 33365213 = 12511955) B12511955
theorem B1711399 : Blo 1520457 1711399 := bstep (se 1 (by rfl) ⟨1283549, by rfl⟩ : syracuseStep 1711399 = 2567099) B2567099
theorem B3423527 : Blo 1520457 3423527 := bstep (se 1 (by rfl) ⟨2567645, by rfl⟩ : syracuseStep 3423527 = 5135291) B5135291
theorem B1711471 : Blo 1520457 1711471 := bstep (se 1 (by rfl) ⟨1283603, by rfl⟩ : syracuseStep 1711471 = 2567207) B2567207
theorem B13172183 : Blo 1520457 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B5135831 : Blo 1520457 5135831 := bstep (se 1 (by rfl) ⟨3851873, by rfl⟩ : syracuseStep 5135831 = 7703747) B7703747
theorem B4111879 : Blo 1520457 4111879 := bstep (se 1 (by rfl) ⟨3083909, by rfl⟩ : syracuseStep 4111879 = 6167819) B6167819
theorem B1711687 : Blo 1520457 1711687 := bstep (se 1 (by rfl) ⟨1283765, by rfl⟩ : syracuseStep 1711687 = 2567531) B2567531
theorem B12992147 : Blo 1520457 12992147 := bstep (se 1 (by rfl) ⟨9744110, by rfl⟩ : syracuseStep 12992147 = 19488221) B19488221
theorem B3849889 : Blo 1520457 3849889 := bstep (se 2 (by rfl) ⟨1443708, by rfl⟩ : syracuseStep 3849889 = 2887417) B2887417
theorem B3423905 : Blo 1520457 3423905 := bstep (se 2 (by rfl) ⟨1283964, by rfl⟩ : syracuseStep 3423905 = 2567929) B2567929
theorem B3850031 : Blo 1520457 3850031 := bstep (se 1 (by rfl) ⟨2887523, by rfl⟩ : syracuseStep 3850031 = 5775047) B5775047
theorem B3292975 : Blo 1520457 3292975 := bstep (se 1 (by rfl) ⟨2469731, by rfl⟩ : syracuseStep 3292975 = 4939463) B4939463
theorem B7413565 : Blo 1520457 7413565 := bstep (se 3 (by rfl) ⟨1390043, by rfl⟩ : syracuseStep 7413565 = 2780087) B2780087
theorem B15621983 : Blo 1520457 15621983 := bstep (se 1 (by rfl) ⟨11716487, by rfl⟩ : syracuseStep 15621983 = 23432975) B23432975
theorem B13877153 : Blo 1520457 13877153 := bstep (se 2 (by rfl) ⟨5203932, by rfl⟩ : syracuseStep 13877153 = 10407865) B10407865
theorem B18497767 : Blo 1520457 18497767 := bstep (se 1 (by rfl) ⟨13873325, by rfl⟩ : syracuseStep 18497767 = 27746651) B27746651
theorem B7807357 : Blo 1520457 7807357 := bstep (se 3 (by rfl) ⟨1463879, by rfl⟩ : syracuseStep 7807357 = 2927759) B2927759
theorem B5480891 : Blo 1520457 5480891 := bstep (se 1 (by rfl) ⟨4110668, by rfl⟩ : syracuseStep 5480891 = 8221337) B8221337
theorem B7307815 : Blo 1520457 7307815 := bstep (se 1 (by rfl) ⟨5480861, by rfl⟩ : syracuseStep 7307815 = 10961723) B10961723
theorem B2343527 : Blo 1520457 2343527 := bstep (se 1 (by rfl) ⟨1757645, by rfl⟩ : syracuseStep 2343527 = 3515291) B3515291
theorem B8659655 : Blo 1520457 8659655 := bstep (se 1 (by rfl) ⟨6494741, by rfl⟩ : syracuseStep 8659655 = 12989483) B12989483
theorem B3425003 : Blo 1520457 3425003 := bstep (se 1 (by rfl) ⟨2568752, by rfl⟩ : syracuseStep 3425003 = 5137505) B5137505
theorem B83248019 : Blo 1520457 83248019 := bstep (se 1 (by rfl) ⟨62436014, by rfl⟩ : syracuseStep 83248019 = 124872029) B124872029
theorem B21947435 : Blo 1520457 21947435 := bstep (se 1 (by rfl) ⟨16460576, by rfl⟩ : syracuseStep 21947435 = 32921153) B32921153
theorem B13173839 : Blo 1520457 13173839 := bstep (se 1 (by rfl) ⟨9880379, by rfl⟩ : syracuseStep 13173839 = 19760759) B19760759
theorem B7702127 : Blo 1520457 7702127 := bstep (se 1 (by rfl) ⟨5776595, by rfl⟩ : syracuseStep 7702127 = 11553191) B11553191
theorem B1926767 : Blo 1520457 1926767 := bstep (se 1 (by rfl) ⟨1445075, by rfl⟩ : syracuseStep 1926767 = 2890151) B2890151
theorem B17319581 : Blo 1520457 17319581 := bstep (se 3 (by rfl) ⟨3247421, by rfl⟩ : syracuseStep 17319581 = 6494843) B6494843
theorem B1926823 : Blo 1520457 1926823 := bstep (se 1 (by rfl) ⟨1445117, by rfl⟩ : syracuseStep 1926823 = 2890235) B2890235
theorem B3851995 : Blo 1520457 3851995 := bstep (se 1 (by rfl) ⟨2888996, by rfl⟩ : syracuseStep 3851995 = 5777993) B5777993
theorem B4392667 : Blo 1520457 4392667 := bstep (se 1 (by rfl) ⟨3294500, by rfl⟩ : syracuseStep 4392667 = 6589001) B6589001
theorem B9750239 : Blo 1520457 9750239 := bstep (se 1 (by rfl) ⟨7312679, by rfl⟩ : syracuseStep 9750239 = 14625359) B14625359
theorem B5138207 : Blo 1520457 5138207 := bstep (se 1 (by rfl) ⟨3853655, by rfl⟩ : syracuseStep 5138207 = 7707311) B7707311
theorem B6940513 : Blo 1520457 6940513 := bstep (se 2 (by rfl) ⟨2602692, by rfl⟩ : syracuseStep 6940513 = 5205385) B5205385
theorem B26003429 : Blo 1520457 26003429 := bstep (se 4 (by rfl) ⟨2437821, by rfl⟩ : syracuseStep 26003429 = 4875643) B4875643
theorem B2566127 : Blo 1520457 2566127 := bstep (se 1 (by rfl) ⟨1924595, by rfl⟩ : syracuseStep 2566127 = 3849191) B3849191
theorem B5482505 : Blo 1520457 5482505 := bstep (se 2 (by rfl) ⟨2055939, by rfl⟩ : syracuseStep 5482505 = 4111879) B4111879
theorem B22243475 : Blo 1520457 22243475 := bstep (se 1 (by rfl) ⟨16682606, by rfl⟩ : syracuseStep 22243475 = 33365213) B33365213
theorem B7309547 : Blo 1520457 7309547 := bstep (se 1 (by rfl) ⟨5482160, by rfl⟩ : syracuseStep 7309547 = 10964321) B10964321
theorem B8661431 : Blo 1520457 8661431 := bstep (se 1 (by rfl) ⟨6496073, by rfl⟩ : syracuseStep 8661431 = 12992147) B12992147
theorem B2566687 : Blo 1520457 2566687 := bstep (se 1 (by rfl) ⟨1925015, by rfl⟩ : syracuseStep 2566687 = 3850031) B3850031
theorem B10414655 : Blo 1520457 10414655 := bstep (se 1 (by rfl) ⟨7810991, by rfl⟩ : syracuseStep 10414655 = 15621983) B15621983
theorem B9251435 : Blo 1520457 9251435 := bstep (se 1 (by rfl) ⟨6938576, by rfl⟩ : syracuseStep 9251435 = 13877153) B13877153
theorem B9743291 : Blo 1520457 9743291 := bstep (se 1 (by rfl) ⟨7307468, by rfl⟩ : syracuseStep 9743291 = 14614937) B14614937
theorem B2567119 : Blo 1520457 2567119 := bstep (se 1 (by rfl) ⟨1925339, by rfl⟩ : syracuseStep 2567119 = 3850679) B3850679
theorem B3853291 : Blo 1520457 3853291 := bstep (se 1 (by rfl) ⟨2889968, by rfl⟩ : syracuseStep 3853291 = 5779937) B5779937
theorem B7703585 : Blo 1520457 7703585 := bstep (se 2 (by rfl) ⟨2888844, by rfl⟩ : syracuseStep 7703585 = 5777689) B5777689
theorem B5778479 : Blo 1520457 5778479 := bstep (se 1 (by rfl) ⟨4333859, by rfl⟩ : syracuseStep 5778479 = 8667719) B8667719
theorem B4942945 : Blo 1520457 4942945 := bstep (se 2 (by rfl) ⟨1853604, by rfl⟩ : syracuseStep 4942945 = 3707209) B3707209
theorem B3853433 : Blo 1520457 3853433 := bstep (se 2 (by rfl) ⟨1445037, by rfl⟩ : syracuseStep 3853433 = 2890075) B2890075
theorem B9751751 : Blo 1520457 9751751 := bstep (se 1 (by rfl) ⟨7313813, by rfl⟩ : syracuseStep 9751751 = 14627627) B14627627
theorem B2280713 : Blo 1520457 2280713 := bstep (se 2 (by rfl) ⟨855267, by rfl⟩ : syracuseStep 2280713 = 1710535) B1710535
theorem B2280815 : Blo 1520457 2280815 := bstep (se 1 (by rfl) ⟨1710611, by rfl⟩ : syracuseStep 2280815 = 3421223) B3421223
theorem B2280935 : Blo 1520457 2280935 := bstep (se 1 (by rfl) ⟨1710701, by rfl⟩ : syracuseStep 2280935 = 3421403) B3421403
theorem B2887159 : Blo 1520457 2887159 := bstep (se 1 (by rfl) ⟨2165369, by rfl⟩ : syracuseStep 2887159 = 4330739) B4330739
theorem B5778935 : Blo 1520457 5778935 := bstep (se 1 (by rfl) ⟨4334201, by rfl⟩ : syracuseStep 5778935 = 8668403) B8668403
theorem B9743905 : Blo 1520457 9743905 := bstep (se 2 (by rfl) ⟨3653964, by rfl⟩ : syracuseStep 9743905 = 7307929) B7307929
theorem B2281067 : Blo 1520457 2281067 := bstep (se 1 (by rfl) ⟨1710800, by rfl⟩ : syracuseStep 2281067 = 3421601) B3421601
theorem B2567855 : Blo 1520457 2567855 := bstep (se 1 (by rfl) ⟨1925891, by rfl⟩ : syracuseStep 2567855 = 3851783) B3851783
theorem B2281193 : Blo 1520457 2281193 := bstep (se 2 (by rfl) ⟨855447, by rfl⟩ : syracuseStep 2281193 = 1710895) B1710895
theorem B5132051 : Blo 1520457 5132051 := bstep (se 1 (by rfl) ⟨3849038, by rfl⟩ : syracuseStep 5132051 = 7698077) B7698077
theorem B2887463 : Blo 1520457 2887463 := bstep (se 1 (by rfl) ⟨2165597, by rfl⟩ : syracuseStep 2887463 = 4331195) B4331195
theorem B2281337 : Blo 1520457 2281337 := bstep (se 2 (by rfl) ⟨855501, by rfl⟩ : syracuseStep 2281337 = 1711003) B1711003
theorem B2928505 : Blo 1520457 2928505 := bstep (se 2 (by rfl) ⟨1098189, by rfl⟩ : syracuseStep 2928505 = 2196379) B2196379
theorem B2568091 : Blo 1520457 2568091 := bstep (se 1 (by rfl) ⟨1926068, by rfl⟩ : syracuseStep 2568091 = 3852137) B3852137
theorem B2281439 : Blo 1520457 2281439 := bstep (se 1 (by rfl) ⟨1711079, by rfl⟩ : syracuseStep 2281439 = 3422159) B3422159
theorem B7704557 : Blo 1520457 7704557 := bstep (se 3 (by rfl) ⟨1444604, by rfl⟩ : syracuseStep 7704557 = 2889209) B2889209
theorem B10973171 : Blo 1520457 10973171 := bstep (se 1 (by rfl) ⟨8229878, by rfl⟩ : syracuseStep 10973171 = 16459757) B16459757
theorem B7311545 : Blo 1520457 7311545 := bstep (se 2 (by rfl) ⟨2741829, by rfl⟩ : syracuseStep 7311545 = 5483659) B5483659
theorem B13004995 : Blo 1520457 13004995 := bstep (se 1 (by rfl) ⟨9753746, by rfl⟩ : syracuseStep 13004995 = 19507493) B19507493
theorem B2281691 : Blo 1520457 2281691 := bstep (se 1 (by rfl) ⟨1711268, by rfl⟩ : syracuseStep 2281691 = 3422537) B3422537
theorem B2281703 : Blo 1520457 2281703 := bstep (se 1 (by rfl) ⟨1711277, by rfl⟩ : syracuseStep 2281703 = 3422555) B3422555
theorem B2568503 : Blo 1520457 2568503 := bstep (se 1 (by rfl) ⟨1926377, by rfl⟩ : syracuseStep 2568503 = 3852755) B3852755
theorem B2281865 : Blo 1520457 2281865 := bstep (se 2 (by rfl) ⟨855699, by rfl⟩ : syracuseStep 2281865 = 1711399) B1711399
theorem B2281961 : Blo 1520457 2281961 := bstep (se 2 (by rfl) ⟨855735, by rfl⟩ : syracuseStep 2281961 = 1711471) B1711471
theorem B5486399 : Blo 1520457 5486399 := bstep (se 1 (by rfl) ⟨4114799, by rfl⟩ : syracuseStep 5486399 = 8229599) B8229599
theorem B9744907 : Blo 1520457 9744907 := bstep (se 1 (by rfl) ⟨7308680, by rfl⟩ : syracuseStep 9744907 = 14617361) B14617361
theorem B2282087 : Blo 1520457 2282087 := bstep (se 1 (by rfl) ⟨1711565, by rfl⟩ : syracuseStep 2282087 = 3423131) B3423131
theorem B5132915 : Blo 1520457 5132915 := bstep (se 1 (by rfl) ⟨3849686, by rfl⟩ : syracuseStep 5132915 = 7699373) B7699373
theorem B2282219 : Blo 1520457 2282219 := bstep (se 1 (by rfl) ⟨1711664, by rfl⟩ : syracuseStep 2282219 = 3423329) B3423329
theorem B2437867 : Blo 1520457 2437867 := bstep (se 1 (by rfl) ⟨1828400, by rfl⟩ : syracuseStep 2437867 = 3656801) B3656801
theorem B2282249 : Blo 1520457 2282249 := bstep (se 2 (by rfl) ⟨855843, by rfl⟩ : syracuseStep 2282249 = 1711687) B1711687
theorem B7705367 : Blo 1520457 7705367 := bstep (se 1 (by rfl) ⟨5779025, by rfl⟩ : syracuseStep 7705367 = 11558051) B11558051
theorem B1520495 : Blo 1520457 1520495 := bstep (se 1 (by rfl) ⟨1140371, by rfl⟩ : syracuseStep 1520495 = 2280743) B2280743
theorem B2282351 : Blo 1520457 2282351 := bstep (se 1 (by rfl) ⟨1711763, by rfl⟩ : syracuseStep 2282351 = 3423527) B3423527
theorem B5133185 : Blo 1520457 5133185 := bstep (se 2 (by rfl) ⟨1924944, by rfl⟩ : syracuseStep 5133185 = 3849889) B3849889
theorem B1520551 : Blo 1520457 1520551 := bstep (se 1 (by rfl) ⟨1140413, by rfl⟩ : syracuseStep 1520551 = 2280827) B2280827
theorem B1520635 : Blo 1520457 1520635 := bstep (se 1 (by rfl) ⟨1140476, by rfl⟩ : syracuseStep 1520635 = 2280953) B2280953
theorem B1520703 : Blo 1520457 1520703 := bstep (se 1 (by rfl) ⟨1140527, by rfl⟩ : syracuseStep 1520703 = 2281055) B2281055
theorem B8221769 : Blo 1520457 8221769 := bstep (se 2 (by rfl) ⟨3083163, by rfl⟩ : syracuseStep 8221769 = 6166327) B6166327
theorem B2888777 : Blo 1520457 2888777 := bstep (se 2 (by rfl) ⟨1083291, by rfl⟩ : syracuseStep 2888777 = 2166583) B2166583
theorem B9884753 : Blo 1520457 9884753 := bstep (se 2 (by rfl) ⟨3706782, by rfl⟩ : syracuseStep 9884753 = 7413565) B7413565
theorem B2282603 : Blo 1520457 2282603 := bstep (se 1 (by rfl) ⟨1711952, by rfl⟩ : syracuseStep 2282603 = 3423905) B3423905
theorem B11711627 : Blo 1520457 11711627 := bstep (se 1 (by rfl) ⟨8783720, by rfl⟩ : syracuseStep 11711627 = 17567441) B17567441
theorem B1520847 : Blo 1520457 1520847 := bstep (se 1 (by rfl) ⟨1140635, by rfl⟩ : syracuseStep 1520847 = 2281271) B2281271
theorem B2282843 : Blo 1520457 2282843 := bstep (se 1 (by rfl) ⟨1712132, by rfl⟩ : syracuseStep 2282843 = 3424265) B3424265
theorem B1521051 : Blo 1520457 1521051 := bstep (se 1 (by rfl) ⟨1140788, by rfl⟩ : syracuseStep 1521051 = 2281577) B2281577
theorem B8230331 : Blo 1520457 8230331 := bstep (se 1 (by rfl) ⟨6172748, by rfl⟩ : syracuseStep 8230331 = 12345497) B12345497
theorem B27768257 : Blo 1520457 27768257 := bstep (se 2 (by rfl) ⟨10413096, by rfl⟩ : syracuseStep 27768257 = 20826193) B20826193
theorem B1521263 : Blo 1520457 1521263 := bstep (se 1 (by rfl) ⟨1140947, by rfl⟩ : syracuseStep 1521263 = 2281895) B2281895
theorem B2283119 : Blo 1520457 2283119 := bstep (se 1 (by rfl) ⟨1712339, by rfl⟩ : syracuseStep 2283119 = 3424679) B3424679
theorem B1521319 : Blo 1520457 1521319 := bstep (se 1 (by rfl) ⟨1140989, by rfl⟩ : syracuseStep 1521319 = 2281979) B2281979
theorem B5133995 : Blo 1520457 5133995 := bstep (se 1 (by rfl) ⟨3850496, by rfl⟩ : syracuseStep 5133995 = 7700993) B7700993
theorem B2283191 : Blo 1520457 2283191 := bstep (se 1 (by rfl) ⟨1712393, by rfl⟩ : syracuseStep 2283191 = 3424787) B3424787
theorem B2283227 : Blo 1520457 2283227 := bstep (se 1 (by rfl) ⟨1712420, by rfl⟩ : syracuseStep 2283227 = 3424841) B3424841
theorem B1521403 : Blo 1520457 1521403 := bstep (se 1 (by rfl) ⟨1141052, by rfl⟩ : syracuseStep 1521403 = 2282105) B2282105
theorem B1521439 : Blo 1520457 1521439 := bstep (se 1 (by rfl) ⟨1141079, by rfl⟩ : syracuseStep 1521439 = 2282159) B2282159
theorem B7698239 : Blo 1520457 7698239 := bstep (se 1 (by rfl) ⟨5773679, by rfl⟩ : syracuseStep 7698239 = 11547359) B11547359
theorem B3422015 : Blo 1520457 3422015 := bstep (se 1 (by rfl) ⟨2566511, by rfl⟩ : syracuseStep 3422015 = 5133023) B5133023
theorem B1521471 : Blo 1520457 1521471 := bstep (se 1 (by rfl) ⟨1141103, by rfl⟩ : syracuseStep 1521471 = 2282207) B2282207
theorem B32905055 : Blo 1520457 32905055 := bstep (se 1 (by rfl) ⟨24678791, by rfl⟩ : syracuseStep 32905055 = 49357583) B49357583
theorem B2283401 : Blo 1520457 2283401 := bstep (se 2 (by rfl) ⟨856275, by rfl⟩ : syracuseStep 2283401 = 1712551) B1712551
theorem B5134319 : Blo 1520457 5134319 := bstep (se 1 (by rfl) ⟨3850739, by rfl⟩ : syracuseStep 5134319 = 7701479) B7701479
theorem B1521647 : Blo 1520457 1521647 := bstep (se 1 (by rfl) ⟨1141235, by rfl⟩ : syracuseStep 1521647 = 2282471) B2282471
theorem B2283503 : Blo 1520457 2283503 := bstep (se 1 (by rfl) ⟨1712627, by rfl⟩ : syracuseStep 2283503 = 3425255) B3425255
theorem B4872287 : Blo 1520457 4872287 := bstep (se 1 (by rfl) ⟨3654215, by rfl⟩ : syracuseStep 4872287 = 7308431) B7308431
theorem B3422303 : Blo 1520457 3422303 := bstep (se 1 (by rfl) ⟨2566727, by rfl⟩ : syracuseStep 3422303 = 5133455) B5133455
theorem B1521819 : Blo 1520457 1521819 := bstep (se 1 (by rfl) ⟨1141364, by rfl⟩ : syracuseStep 1521819 = 2282729) B2282729
theorem B4110497 : Blo 1520457 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B1521855 : Blo 1520457 1521855 := bstep (se 1 (by rfl) ⟨1141391, by rfl⟩ : syracuseStep 1521855 = 2282783) B2282783
theorem B5134535 : Blo 1520457 5134535 := bstep (se 1 (by rfl) ⟨3850901, by rfl⟩ : syracuseStep 5134535 = 7701803) B7701803
theorem B1521967 : Blo 1520457 1521967 := bstep (se 1 (by rfl) ⟨1141475, by rfl⟩ : syracuseStep 1521967 = 2282951) B2282951
theorem B7706987 : Blo 1520457 7706987 := bstep (se 1 (by rfl) ⟨5780240, by rfl⟩ : syracuseStep 7706987 = 11560481) B11560481
theorem B1522203 : Blo 1520457 1522203 := bstep (se 1 (by rfl) ⟨1141652, by rfl⟩ : syracuseStep 1522203 = 2283305) B2283305
theorem B1522207 : Blo 1520457 1522207 := bstep (se 1 (by rfl) ⟨1141655, by rfl⟩ : syracuseStep 1522207 = 2283311) B2283311
theorem B5135183 : Blo 1520457 5135183 := bstep (se 1 (by rfl) ⟨3851387, by rfl⟩ : syracuseStep 5135183 = 7702775) B7702775
theorem B3423059 : Blo 1520457 3423059 := bstep (se 1 (by rfl) ⟨2567294, by rfl⟩ : syracuseStep 3423059 = 5134589) B5134589
theorem B4332379 : Blo 1520457 4332379 := bstep (se 1 (by rfl) ⟨3249284, by rfl⟩ : syracuseStep 4332379 = 6498569) B6498569
theorem B4111489 : Blo 1520457 4111489 := bstep (se 2 (by rfl) ⟨1541808, by rfl⟩ : syracuseStep 4111489 = 3083617) B3083617
theorem B5135507 : Blo 1520457 5135507 := bstep (se 1 (by rfl) ⟨3851630, by rfl⟩ : syracuseStep 5135507 = 7703261) B7703261
theorem B1711327 : Blo 1520457 1711327 := bstep (se 1 (by rfl) ⟨1283495, by rfl⟩ : syracuseStep 1711327 = 2566991) B2566991
theorem B3423599 : Blo 1520457 3423599 := bstep (se 1 (by rfl) ⟨2567699, by rfl⟩ : syracuseStep 3423599 = 5135399) B5135399
theorem B5135777 : Blo 1520457 5135777 := bstep (se 2 (by rfl) ⟨1925916, by rfl⟩ : syracuseStep 5135777 = 3851833) B3851833
theorem B8781455 : Blo 1520457 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B3423887 : Blo 1520457 3423887 := bstep (se 1 (by rfl) ⟨2567915, by rfl⟩ : syracuseStep 3423887 = 5135831) B5135831
theorem B4390633 : Blo 1520457 4390633 := bstep (se 2 (by rfl) ⟨1646487, by rfl⟩ : syracuseStep 4390633 = 3292975) B3292975
theorem B3423977 : Blo 1520457 3423977 := bstep (se 2 (by rfl) ⟨1283991, by rfl⟩ : syracuseStep 3423977 = 2567983) B2567983
theorem B19545833 : Blo 1520457 19545833 := bstep (se 2 (by rfl) ⟨7329687, by rfl⟩ : syracuseStep 19545833 = 14659375) B14659375
theorem B5136317 : Blo 1520457 5136317 := bstep (se 3 (by rfl) ⟨963059, by rfl⟩ : syracuseStep 5136317 = 1926119) B1926119
theorem B4874363 : Blo 1520457 4874363 := bstep (se 1 (by rfl) ⟨3655772, by rfl⟩ : syracuseStep 4874363 = 7311545) B7311545
theorem B1712335 : Blo 1520457 1712335 := bstep (se 1 (by rfl) ⟨1284251, by rfl⟩ : syracuseStep 1712335 = 2568503) B2568503
theorem B3653927 : Blo 1520457 3653927 := bstep (se 1 (by rfl) ⟨2740445, by rfl⟩ : syracuseStep 3653927 = 5480891) B5480891
theorem B5136911 : Blo 1520457 5136911 := bstep (se 1 (by rfl) ⟨3852683, by rfl⟩ : syracuseStep 5136911 = 7705367) B7705367
theorem B12993209 : Blo 1520457 12993209 := bstep (se 2 (by rfl) ⟨4872453, by rfl⟩ : syracuseStep 12993209 = 9744907) B9744907
theorem B14631623 : Blo 1520457 14631623 := bstep (se 1 (by rfl) ⟨10973717, by rfl⟩ : syracuseStep 14631623 = 21947435) B21947435
theorem B5481179 : Blo 1520457 5481179 := bstep (se 1 (by rfl) ⟨4110884, by rfl⟩ : syracuseStep 5481179 = 8221769) B8221769
theorem B1925851 : Blo 1520457 1925851 := bstep (se 1 (by rfl) ⟨1444388, by rfl⟩ : syracuseStep 1925851 = 2888777) B2888777
theorem B8782559 : Blo 1520457 8782559 := bstep (se 1 (by rfl) ⟨6586919, by rfl⟩ : syracuseStep 8782559 = 13173839) B13173839
theorem B7807751 : Blo 1520457 7807751 := bstep (se 1 (by rfl) ⟨5855813, by rfl⟩ : syracuseStep 7807751 = 11711627) B11711627
theorem B5776505 : Blo 1520457 5776505 := bstep (se 2 (by rfl) ⟨2166189, by rfl⟩ : syracuseStep 5776505 = 4332379) B4332379
theorem B3425471 : Blo 1520457 3425471 := bstep (se 1 (by rfl) ⟨2569103, by rfl⟩ : syracuseStep 3425471 = 5138207) B5138207
theorem B13001957 : Blo 1520457 13001957 := bstep (se 4 (by rfl) ⟨1218933, by rfl⟩ : syracuseStep 13001957 = 2437867) B2437867
theorem B5137721 : Blo 1520457 5137721 := bstep (se 2 (by rfl) ⟨1926645, by rfl⟩ : syracuseStep 5137721 = 3853291) B3853291
theorem B17335619 : Blo 1520457 17335619 := bstep (se 1 (by rfl) ⟨13001714, by rfl⟩ : syracuseStep 17335619 = 26003429) B26003429
theorem B14828983 : Blo 1520457 14828983 := bstep (se 1 (by rfl) ⟨11121737, by rfl⟩ : syracuseStep 14828983 = 22243475) B22243475
theorem B5137991 : Blo 1520457 5137991 := bstep (se 1 (by rfl) ⟨3853493, by rfl⟩ : syracuseStep 5137991 = 7706987) B7706987
theorem B5138045 : Blo 1520457 5138045 := bstep (se 3 (by rfl) ⟨963383, by rfl⟩ : syracuseStep 5138045 = 1926767) B1926767
theorem B3852319 : Blo 1520457 3852319 := bstep (se 1 (by rfl) ⟨2889239, by rfl⟩ : syracuseStep 3852319 = 5778479) B5778479
theorem B87746813 : Blo 1520457 87746813 := bstep (se 3 (by rfl) ⟨16452527, by rfl⟩ : syracuseStep 87746813 = 32905055) B32905055
theorem B3852623 : Blo 1520457 3852623 := bstep (se 1 (by rfl) ⟨2889467, by rfl⟩ : syracuseStep 3852623 = 5778935) B5778935
theorem B9743753 : Blo 1520457 9743753 := bstep (se 2 (by rfl) ⟨3653907, by rfl⟩ : syracuseStep 9743753 = 7307815) B7307815
theorem B6589835 : Blo 1520457 6589835 := bstep (se 1 (by rfl) ⟨4942376, by rfl⟩ : syracuseStep 6589835 = 9884753) B9884753
theorem B11546387 : Blo 1520457 11546387 := bstep (se 1 (by rfl) ⟨8659790, by rfl⟩ : syracuseStep 11546387 = 17319581) B17319581
theorem B6500159 : Blo 1520457 6500159 := bstep (se 1 (by rfl) ⟨4875119, by rfl⟩ : syracuseStep 6500159 = 9750239) B9750239
theorem B5132159 : Blo 1520457 5132159 := bstep (se 1 (by rfl) ⟨3849119, by rfl⟩ : syracuseStep 5132159 = 7698239) B7698239
theorem B2281343 : Blo 1520457 2281343 := bstep (se 1 (by rfl) ⟨1711007, by rfl⟩ : syracuseStep 2281343 = 3422015) B3422015
theorem B3657599 : Blo 1520457 3657599 := bstep (se 1 (by rfl) ⟨2743199, by rfl⟩ : syracuseStep 3657599 = 5486399) B5486399
theorem B3248191 : Blo 1520457 3248191 := bstep (se 1 (by rfl) ⟨2436143, by rfl⟩ : syracuseStep 3248191 = 4872287) B4872287
theorem B2281535 : Blo 1520457 2281535 := bstep (se 1 (by rfl) ⟨1711151, by rfl⟩ : syracuseStep 2281535 = 3422303) B3422303
theorem B2740331 : Blo 1520457 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B6590593 : Blo 1520457 6590593 := bstep (se 2 (by rfl) ⟨2471472, by rfl⟩ : syracuseStep 6590593 = 4942945) B4942945
theorem B2281769 : Blo 1520457 2281769 := bstep (se 2 (by rfl) ⟨855663, by rfl⟩ : syracuseStep 2281769 = 1711327) B1711327
theorem B6943103 : Blo 1520457 6943103 := bstep (se 1 (by rfl) ⟨5207327, by rfl⟩ : syracuseStep 6943103 = 10414655) B10414655
theorem B2282039 : Blo 1520457 2282039 := bstep (se 1 (by rfl) ⟨1711529, by rfl⟩ : syracuseStep 2282039 = 3423059) B3423059
theorem B2568955 : Blo 1520457 2568955 := bstep (se 1 (by rfl) ⟨1926716, by rfl⟩ : syracuseStep 2568955 = 3853433) B3853433
theorem B6501167 : Blo 1520457 6501167 := bstep (se 1 (by rfl) ⟨4875875, by rfl⟩ : syracuseStep 6501167 = 9751751) B9751751
theorem B1520475 : Blo 1520457 1520475 := bstep (se 1 (by rfl) ⟨1140356, by rfl⟩ : syracuseStep 1520475 = 2280713) B2280713
theorem B2569097 : Blo 1520457 2569097 := bstep (se 2 (by rfl) ⟨963411, by rfl⟩ : syracuseStep 2569097 = 1926823) B1926823
theorem B1520543 : Blo 1520457 1520543 := bstep (se 1 (by rfl) ⟨1140407, by rfl⟩ : syracuseStep 1520543 = 2280815) B2280815
theorem B2282399 : Blo 1520457 2282399 := bstep (se 1 (by rfl) ⟨1711799, by rfl⟩ : syracuseStep 2282399 = 3423599) B3423599
theorem B5854177 : Blo 1520457 5854177 := bstep (se 2 (by rfl) ⟨2195316, by rfl⟩ : syracuseStep 5854177 = 4390633) B4390633
theorem B1520623 : Blo 1520457 1520623 := bstep (se 1 (by rfl) ⟨1140467, by rfl⟩ : syracuseStep 1520623 = 2280935) B2280935
theorem B1520711 : Blo 1520457 1520711 := bstep (se 1 (by rfl) ⟨1140533, by rfl⟩ : syracuseStep 1520711 = 2281067) B2281067
theorem B5854303 : Blo 1520457 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B2282591 : Blo 1520457 2282591 := bstep (se 1 (by rfl) ⟨1711943, by rfl⟩ : syracuseStep 2282591 = 3423887) B3423887
theorem B9254017 : Blo 1520457 9254017 := bstep (se 2 (by rfl) ⟨3470256, by rfl⟩ : syracuseStep 9254017 = 6940513) B6940513
theorem B1520795 : Blo 1520457 1520795 := bstep (se 1 (by rfl) ⟨1140596, by rfl⟩ : syracuseStep 1520795 = 2281193) B2281193
theorem B2282651 : Blo 1520457 2282651 := bstep (se 1 (by rfl) ⟨1711988, by rfl⟩ : syracuseStep 2282651 = 3423977) B3423977
theorem B13030555 : Blo 1520457 13030555 := bstep (se 1 (by rfl) ⟨9772916, by rfl⟩ : syracuseStep 13030555 = 19545833) B19545833
theorem B3904673 : Blo 1520457 3904673 := bstep (se 2 (by rfl) ⟨1464252, by rfl⟩ : syracuseStep 3904673 = 2928505) B2928505
theorem B3421367 : Blo 1520457 3421367 := bstep (se 1 (by rfl) ⟨2566025, by rfl⟩ : syracuseStep 3421367 = 5132051) B5132051
theorem B1520891 : Blo 1520457 1520891 := bstep (se 1 (by rfl) ⟨1140668, by rfl⟩ : syracuseStep 1520891 = 2281337) B2281337
theorem B1520959 : Blo 1520457 1520959 := bstep (se 1 (by rfl) ⟨1140719, by rfl⟩ : syracuseStep 1520959 = 2281439) B2281439
theorem B14620013 : Blo 1520457 14620013 := bstep (se 3 (by rfl) ⟨2741252, by rfl⟩ : syracuseStep 14620013 = 5482505) B5482505
theorem B1521127 : Blo 1520457 1521127 := bstep (se 1 (by rfl) ⟨1140845, by rfl⟩ : syracuseStep 1521127 = 2281691) B2281691
theorem B1521135 : Blo 1520457 1521135 := bstep (se 1 (by rfl) ⟨1140851, by rfl⟩ : syracuseStep 1521135 = 2281703) B2281703
theorem B17339993 : Blo 1520457 17339993 := bstep (se 2 (by rfl) ⟨6502497, by rfl⟩ : syracuseStep 17339993 = 13004995) B13004995
theorem B1521243 : Blo 1520457 1521243 := bstep (se 1 (by rfl) ⟨1140932, by rfl⟩ : syracuseStep 1521243 = 2281865) B2281865
theorem B24663689 : Blo 1520457 24663689 := bstep (se 2 (by rfl) ⟨9248883, by rfl⟩ : syracuseStep 24663689 = 18497767) B18497767
theorem B1521307 : Blo 1520457 1521307 := bstep (se 1 (by rfl) ⟨1140980, by rfl⟩ : syracuseStep 1521307 = 2281961) B2281961
theorem B1562351 : Blo 1520457 1562351 := bstep (se 1 (by rfl) ⟨1171763, by rfl⟩ : syracuseStep 1562351 = 2343527) B2343527
theorem B1521391 : Blo 1520457 1521391 := bstep (se 1 (by rfl) ⟨1141043, by rfl⟩ : syracuseStep 1521391 = 2282087) B2282087
theorem B3421943 : Blo 1520457 3421943 := bstep (se 1 (by rfl) ⟨2566457, by rfl⟩ : syracuseStep 3421943 = 5132915) B5132915
theorem B5773103 : Blo 1520457 5773103 := bstep (se 1 (by rfl) ⟨4329827, by rfl⟩ : syracuseStep 5773103 = 8659655) B8659655
theorem B1521479 : Blo 1520457 1521479 := bstep (se 1 (by rfl) ⟨1141109, by rfl⟩ : syracuseStep 1521479 = 2282219) B2282219
theorem B2283335 : Blo 1520457 2283335 := bstep (se 1 (by rfl) ⟨1712501, by rfl⟩ : syracuseStep 2283335 = 3425003) B3425003
theorem B10409809 : Blo 1520457 10409809 := bstep (se 2 (by rfl) ⟨3903678, by rfl⟩ : syracuseStep 10409809 = 7807357) B7807357
theorem B1521499 : Blo 1520457 1521499 := bstep (se 1 (by rfl) ⟨1141124, by rfl⟩ : syracuseStep 1521499 = 2282249) B2282249
theorem B1521567 : Blo 1520457 1521567 := bstep (se 1 (by rfl) ⟨1141175, by rfl⟩ : syracuseStep 1521567 = 2282351) B2282351
theorem B3422123 : Blo 1520457 3422123 := bstep (se 1 (by rfl) ⟨2566592, by rfl⟩ : syracuseStep 3422123 = 5133185) B5133185
theorem B55498679 : Blo 1520457 55498679 := bstep (se 1 (by rfl) ⟨41624009, by rfl⟩ : syracuseStep 55498679 = 83248019) B83248019
theorem B21927941 : Blo 1520457 21927941 := bstep (se 4 (by rfl) ⟨2055744, by rfl⟩ : syracuseStep 21927941 = 4111489) B4111489
theorem B3422249 : Blo 1520457 3422249 := bstep (se 2 (by rfl) ⟨1283343, by rfl⟩ : syracuseStep 3422249 = 2566687) B2566687
theorem B1521735 : Blo 1520457 1521735 := bstep (se 1 (by rfl) ⟨1141301, by rfl⟩ : syracuseStep 1521735 = 2282603) B2282603
theorem B1521895 : Blo 1520457 1521895 := bstep (se 1 (by rfl) ⟨1141421, by rfl⟩ : syracuseStep 1521895 = 2282843) B2282843
theorem B5486887 : Blo 1520457 5486887 := bstep (se 1 (by rfl) ⟨4115165, by rfl⟩ : syracuseStep 5486887 = 8230331) B8230331
theorem B18512171 : Blo 1520457 18512171 := bstep (se 1 (by rfl) ⟨13884128, by rfl⟩ : syracuseStep 18512171 = 27768257) B27768257
theorem B5134751 : Blo 1520457 5134751 := bstep (se 1 (by rfl) ⟨3851063, by rfl⟩ : syracuseStep 5134751 = 7702127) B7702127
theorem B1522079 : Blo 1520457 1522079 := bstep (se 1 (by rfl) ⟨1141559, by rfl⟩ : syracuseStep 1522079 = 2283119) B2283119
theorem B3422663 : Blo 1520457 3422663 := bstep (se 1 (by rfl) ⟨2566997, by rfl⟩ : syracuseStep 3422663 = 5133995) B5133995
theorem B1522127 : Blo 1520457 1522127 := bstep (se 1 (by rfl) ⟨1141595, by rfl⟩ : syracuseStep 1522127 = 2283191) B2283191
theorem B1522151 : Blo 1520457 1522151 := bstep (se 1 (by rfl) ⟨1141613, by rfl⟩ : syracuseStep 1522151 = 2283227) B2283227
theorem B1522267 : Blo 1520457 1522267 := bstep (se 1 (by rfl) ⟨1141700, by rfl⟩ : syracuseStep 1522267 = 2283401) B2283401
theorem B3422825 : Blo 1520457 3422825 := bstep (se 2 (by rfl) ⟨1283559, by rfl⟩ : syracuseStep 3422825 = 2567119) B2567119
theorem B1710751 : Blo 1520457 1710751 := bstep (se 1 (by rfl) ⟨1283063, by rfl⟩ : syracuseStep 1710751 = 2566127) B2566127
theorem B3422879 : Blo 1520457 3422879 := bstep (se 1 (by rfl) ⟨2567159, by rfl⟩ : syracuseStep 3422879 = 5134319) B5134319
theorem B1522335 : Blo 1520457 1522335 := bstep (se 1 (by rfl) ⟨1141751, by rfl⟩ : syracuseStep 1522335 = 2283503) B2283503
theorem B3423023 : Blo 1520457 3423023 := bstep (se 1 (by rfl) ⟨2567267, by rfl⟩ : syracuseStep 3423023 = 5134535) B5134535
theorem B4873031 : Blo 1520457 4873031 := bstep (se 1 (by rfl) ⟨3654773, by rfl⟩ : syracuseStep 4873031 = 7309547) B7309547
theorem B5774287 : Blo 1520457 5774287 := bstep (se 1 (by rfl) ⟨4330715, by rfl⟩ : syracuseStep 5774287 = 8661431) B8661431
theorem B6167623 : Blo 1520457 6167623 := bstep (se 1 (by rfl) ⟨4625717, by rfl⟩ : syracuseStep 6167623 = 9251435) B9251435
theorem B7315447 : Blo 1520457 7315447 := bstep (se 1 (by rfl) ⟨5486585, by rfl⟩ : syracuseStep 7315447 = 10973171) B10973171
theorem B3423455 : Blo 1520457 3423455 := bstep (se 1 (by rfl) ⟨2567591, by rfl⟩ : syracuseStep 3423455 = 5135183) B5135183
theorem B6495527 : Blo 1520457 6495527 := bstep (se 1 (by rfl) ⟨4871645, by rfl⟩ : syracuseStep 6495527 = 9743291) B9743291
theorem B3849545 : Blo 1520457 3849545 := bstep (se 2 (by rfl) ⟨1443579, by rfl⟩ : syracuseStep 3849545 = 2887159) B2887159
theorem B5135723 : Blo 1520457 5135723 := bstep (se 1 (by rfl) ⟨3851792, by rfl⟩ : syracuseStep 5135723 = 7703585) B7703585
theorem B12991873 : Blo 1520457 12991873 := bstep (se 2 (by rfl) ⟨4871952, by rfl⟩ : syracuseStep 12991873 = 9743905) B9743905
theorem B3423671 : Blo 1520457 3423671 := bstep (se 1 (by rfl) ⟨2567753, by rfl⟩ : syracuseStep 3423671 = 5135507) B5135507
theorem B3423851 : Blo 1520457 3423851 := bstep (se 1 (by rfl) ⟨2567888, by rfl⟩ : syracuseStep 3423851 = 5135777) B5135777
theorem B5135993 : Blo 1520457 5135993 := bstep (se 2 (by rfl) ⟨1925997, by rfl⟩ : syracuseStep 5135993 = 3851995) B3851995
theorem B5856889 : Blo 1520457 5856889 := bstep (se 2 (by rfl) ⟨2196333, by rfl⟩ : syracuseStep 5856889 = 4392667) B4392667
theorem B1711903 : Blo 1520457 1711903 := bstep (se 1 (by rfl) ⟨1283927, by rfl⟩ : syracuseStep 1711903 = 2567855) B2567855
theorem B1924975 : Blo 1520457 1924975 := bstep (se 1 (by rfl) ⟨1443731, by rfl⟩ : syracuseStep 1924975 = 2887463) B2887463
theorem B3424121 : Blo 1520457 3424121 := bstep (se 2 (by rfl) ⟨1284045, by rfl⟩ : syracuseStep 3424121 = 2568091) B2568091
theorem B3424211 : Blo 1520457 3424211 := bstep (se 1 (by rfl) ⟨2568158, by rfl⟩ : syracuseStep 3424211 = 5136317) B5136317
theorem B5136371 : Blo 1520457 5136371 := bstep (se 1 (by rfl) ⟨3852278, by rfl⟩ : syracuseStep 5136371 = 7704557) B7704557
theorem B5136425 : Blo 1520457 5136425 := bstep (se 2 (by rfl) ⟨1926159, by rfl⟩ : syracuseStep 5136425 = 3852319) B3852319
theorem B1826887 : Blo 1520457 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B4628735 : Blo 1520457 4628735 := bstep (se 1 (by rfl) ⟨3471551, by rfl⟩ : syracuseStep 4628735 = 6943103) B6943103
theorem B3424607 : Blo 1520457 3424607 := bstep (se 1 (by rfl) ⟨2568455, by rfl⟩ : syracuseStep 3424607 = 5136911) B5136911
theorem B7315849 : Blo 1520457 7315849 := bstep (se 2 (by rfl) ⟨2743443, by rfl⟩ : syracuseStep 7315849 = 5486887) B5486887
theorem B10412461 : Blo 1520457 10412461 := bstep (se 3 (by rfl) ⟨1952336, by rfl⟩ : syracuseStep 10412461 = 3904673) B3904673
theorem B3424247 : Blo 1520457 3424247 := bstep (se 1 (by rfl) ⟨2568185, by rfl⟩ : syracuseStep 3424247 = 5136371) B5136371
theorem B3654119 : Blo 1520457 3654119 := bstep (se 1 (by rfl) ⟨2740589, by rfl⟩ : syracuseStep 3654119 = 5481179) B5481179
theorem B4334111 : Blo 1520457 4334111 := bstep (se 1 (by rfl) ⟨3250583, by rfl⟩ : syracuseStep 4334111 = 6501167) B6501167
theorem B1712731 : Blo 1520457 1712731 := bstep (se 1 (by rfl) ⟨1284548, by rfl⟩ : syracuseStep 1712731 = 2569097) B2569097
theorem B3851003 : Blo 1520457 3851003 := bstep (se 1 (by rfl) ⟨2888252, by rfl⟩ : syracuseStep 3851003 = 5776505) B5776505
theorem B8667971 : Blo 1520457 8667971 := bstep (se 1 (by rfl) ⟨6500978, by rfl⟩ : syracuseStep 8667971 = 13001957) B13001957
theorem B3425147 : Blo 1520457 3425147 := bstep (se 1 (by rfl) ⟨2568860, by rfl⟩ : syracuseStep 3425147 = 5137721) B5137721
theorem B3425273 : Blo 1520457 3425273 := bstep (se 2 (by rfl) ⟨1284477, by rfl⟩ : syracuseStep 3425273 = 2568955) B2568955
theorem B3425327 : Blo 1520457 3425327 := bstep (se 1 (by rfl) ⟨2568995, by rfl⟩ : syracuseStep 3425327 = 5137991) B5137991
theorem B11559995 : Blo 1520457 11559995 := bstep (se 1 (by rfl) ⟨8669996, by rfl⟩ : syracuseStep 11559995 = 17339993) B17339993
theorem B3425363 : Blo 1520457 3425363 := bstep (se 1 (by rfl) ⟨2569022, by rfl⟩ : syracuseStep 3425363 = 5138045) B5138045
theorem B16442459 : Blo 1520457 16442459 := bstep (se 1 (by rfl) ⟨12331844, by rfl⟩ : syracuseStep 16442459 = 24663689) B24663689
theorem B12338689 : Blo 1520457 12338689 := bstep (se 2 (by rfl) ⟨4627008, by rfl⟩ : syracuseStep 12338689 = 9254017) B9254017
theorem B7809185 : Blo 1520457 7809185 := bstep (se 2 (by rfl) ⟨2928444, by rfl⟩ : syracuseStep 7809185 = 5856889) B5856889
theorem B2566363 : Blo 1520457 2566363 := bstep (se 1 (by rfl) ⟨1924772, by rfl⟩ : syracuseStep 2566363 = 3849545) B3849545
theorem B4393223 : Blo 1520457 4393223 := bstep (se 1 (by rfl) ⟨3294917, by rfl⟩ : syracuseStep 4393223 = 6589835) B6589835
theorem B79087909 : Blo 1520457 79087909 := bstep (se 4 (by rfl) ⟨7414491, by rfl⟩ : syracuseStep 79087909 = 14828983) B14828983
theorem B13879745 : Blo 1520457 13879745 := bstep (se 2 (by rfl) ⟨5204904, by rfl⟩ : syracuseStep 13879745 = 10409809) B10409809
theorem B2566633 : Blo 1520457 2566633 := bstep (se 2 (by rfl) ⟨962487, by rfl⟩ : syracuseStep 2566633 = 1924975) B1924975
theorem B16665077 : Blo 1520457 16665077 := bstep (se 5 (by rfl) ⟨781175, by rfl⟩ : syracuseStep 16665077 = 1562351) B1562351
theorem B2435951 : Blo 1520457 2435951 := bstep (se 1 (by rfl) ⟨1826963, by rfl⟩ : syracuseStep 2435951 = 3653927) B3653927
theorem B8662139 : Blo 1520457 8662139 := bstep (se 1 (by rfl) ⟨6496604, by rfl⟩ : syracuseStep 8662139 = 12993209) B12993209
theorem B5205167 : Blo 1520457 5205167 := bstep (se 1 (by rfl) ⟨3903875, by rfl⟩ : syracuseStep 5205167 = 7807751) B7807751
theorem B2280911 : Blo 1520457 2280911 := bstep (se 1 (by rfl) ⟨1710683, by rfl⟩ : syracuseStep 2280911 = 3421367) B3421367
theorem B2281001 : Blo 1520457 2281001 := bstep (se 2 (by rfl) ⟨855375, by rfl⟩ : syracuseStep 2281001 = 1710751) B1710751
theorem B2567801 : Blo 1520457 2567801 := bstep (se 2 (by rfl) ⟨962925, by rfl⟩ : syracuseStep 2567801 = 1925851) B1925851
theorem B2281295 : Blo 1520457 2281295 := bstep (se 1 (by rfl) ⟨1710971, by rfl⟩ : syracuseStep 2281295 = 3421943) B3421943
theorem B2281415 : Blo 1520457 2281415 := bstep (se 1 (by rfl) ⟨1711061, by rfl⟩ : syracuseStep 2281415 = 3422123) B3422123
theorem B36999119 : Blo 1520457 36999119 := bstep (se 1 (by rfl) ⟨27749339, by rfl⟩ : syracuseStep 36999119 = 55498679) B55498679
theorem B14618627 : Blo 1520457 14618627 := bstep (se 1 (by rfl) ⟨10963970, by rfl⟩ : syracuseStep 14618627 = 21927941) B21927941
theorem B2281499 : Blo 1520457 2281499 := bstep (se 1 (by rfl) ⟨1711124, by rfl⟩ : syracuseStep 2281499 = 3422249) B3422249
theorem B12341447 : Blo 1520457 12341447 := bstep (se 1 (by rfl) ⟨9256085, by rfl⟩ : syracuseStep 12341447 = 18512171) B18512171
theorem B2568415 : Blo 1520457 2568415 := bstep (se 1 (by rfl) ⟨1926311, by rfl⟩ : syracuseStep 2568415 = 3852623) B3852623
theorem B2281775 : Blo 1520457 2281775 := bstep (se 1 (by rfl) ⟨1711331, by rfl⟩ : syracuseStep 2281775 = 3422663) B3422663
theorem B2281883 : Blo 1520457 2281883 := bstep (se 1 (by rfl) ⟨1711412, by rfl⟩ : syracuseStep 2281883 = 3422825) B3422825
theorem B2281919 : Blo 1520457 2281919 := bstep (se 1 (by rfl) ⟨1711439, by rfl⟩ : syracuseStep 2281919 = 3422879) B3422879
theorem B17322497 : Blo 1520457 17322497 := bstep (se 2 (by rfl) ⟨6495936, by rfl⟩ : syracuseStep 17322497 = 12991873) B12991873
theorem B2282015 : Blo 1520457 2282015 := bstep (se 1 (by rfl) ⟨1711511, by rfl⟩ : syracuseStep 2282015 = 3423023) B3423023
theorem B3248687 : Blo 1520457 3248687 := bstep (se 1 (by rfl) ⟨2436515, by rfl⟩ : syracuseStep 3248687 = 4873031) B4873031
theorem B2282303 : Blo 1520457 2282303 := bstep (se 1 (by rfl) ⟨1711727, by rfl⟩ : syracuseStep 2282303 = 3423455) B3423455
theorem B4330351 : Blo 1520457 4330351 := bstep (se 1 (by rfl) ⟨3247763, by rfl⟩ : syracuseStep 4330351 = 6495527) B6495527
theorem B2282447 : Blo 1520457 2282447 := bstep (se 1 (by rfl) ⟨1711835, by rfl⟩ : syracuseStep 2282447 = 3423671) B3423671
theorem B2282537 : Blo 1520457 2282537 := bstep (se 2 (by rfl) ⟨855951, by rfl⟩ : syracuseStep 2282537 = 1711903) B1711903
theorem B2282567 : Blo 1520457 2282567 := bstep (se 1 (by rfl) ⟨1711925, by rfl⟩ : syracuseStep 2282567 = 3423851) B3423851
theorem B7697591 : Blo 1520457 7697591 := bstep (se 1 (by rfl) ⟨5773193, by rfl⟩ : syracuseStep 7697591 = 11546387) B11546387
theorem B2282747 : Blo 1520457 2282747 := bstep (se 1 (by rfl) ⟨1712060, by rfl⟩ : syracuseStep 2282747 = 3424121) B3424121
theorem B3421439 : Blo 1520457 3421439 := bstep (se 1 (by rfl) ⟨2566079, by rfl⟩ : syracuseStep 3421439 = 5132159) B5132159
theorem B1520895 : Blo 1520457 1520895 := bstep (se 1 (by rfl) ⟨1140671, by rfl⟩ : syracuseStep 1520895 = 2281343) B2281343
theorem B2438399 : Blo 1520457 2438399 := bstep (se 1 (by rfl) ⟨1828799, by rfl⟩ : syracuseStep 2438399 = 3657599) B3657599
theorem B2282807 : Blo 1520457 2282807 := bstep (se 1 (by rfl) ⟨1712105, by rfl⟩ : syracuseStep 2282807 = 3424211) B3424211
theorem B9753929 : Blo 1520457 9753929 := bstep (se 2 (by rfl) ⟨3657723, by rfl⟩ : syracuseStep 9753929 = 7315447) B7315447
theorem B1521023 : Blo 1520457 1521023 := bstep (se 1 (by rfl) ⟨1140767, by rfl⟩ : syracuseStep 1521023 = 2281535) B2281535
theorem B3249575 : Blo 1520457 3249575 := bstep (se 1 (by rfl) ⟨2437181, by rfl⟩ : syracuseStep 3249575 = 4874363) B4874363
theorem B4330921 : Blo 1520457 4330921 := bstep (se 2 (by rfl) ⟨1624095, by rfl⟩ : syracuseStep 4330921 = 3248191) B3248191
theorem B8787457 : Blo 1520457 8787457 := bstep (se 2 (by rfl) ⟨3295296, by rfl⟩ : syracuseStep 8787457 = 6590593) B6590593
theorem B1521179 : Blo 1520457 1521179 := bstep (se 1 (by rfl) ⟨1140884, by rfl⟩ : syracuseStep 1521179 = 2281769) B2281769
theorem B2283113 : Blo 1520457 2283113 := bstep (se 2 (by rfl) ⟨856167, by rfl⟩ : syracuseStep 2283113 = 1712335) B1712335
theorem B1521359 : Blo 1520457 1521359 := bstep (se 1 (by rfl) ⟨1141019, by rfl⟩ : syracuseStep 1521359 = 2282039) B2282039
theorem B9754415 : Blo 1520457 9754415 := bstep (se 1 (by rfl) ⟨7315811, by rfl⟩ : syracuseStep 9754415 = 14631623) B14631623
theorem B5855039 : Blo 1520457 5855039 := bstep (se 1 (by rfl) ⟨4391279, by rfl⟩ : syracuseStep 5855039 = 8782559) B8782559
theorem B1521599 : Blo 1520457 1521599 := bstep (se 1 (by rfl) ⟨1141199, by rfl⟩ : syracuseStep 1521599 = 2282399) B2282399
theorem B1521727 : Blo 1520457 1521727 := bstep (se 1 (by rfl) ⟨1141295, by rfl⟩ : syracuseStep 1521727 = 2282591) B2282591
theorem B1521767 : Blo 1520457 1521767 := bstep (se 1 (by rfl) ⟨1141325, by rfl⟩ : syracuseStep 1521767 = 2282651) B2282651
theorem B2283647 : Blo 1520457 2283647 := bstep (se 1 (by rfl) ⟨1712735, by rfl⟩ : syracuseStep 2283647 = 3425471) B3425471
theorem B11557079 : Blo 1520457 11557079 := bstep (se 1 (by rfl) ⟨8667809, by rfl⟩ : syracuseStep 11557079 = 17335619) B17335619
theorem B9746675 : Blo 1520457 9746675 := bstep (se 1 (by rfl) ⟨7310006, by rfl⟩ : syracuseStep 9746675 = 14620013) B14620013
theorem B3848735 : Blo 1520457 3848735 := bstep (se 1 (by rfl) ⟨2886551, by rfl⟩ : syracuseStep 3848735 = 5773103) B5773103
theorem B1522223 : Blo 1520457 1522223 := bstep (se 1 (by rfl) ⟨1141667, by rfl⟩ : syracuseStep 1522223 = 2283335) B2283335
theorem B7699049 : Blo 1520457 7699049 := bstep (se 2 (by rfl) ⟨2887143, by rfl⟩ : syracuseStep 7699049 = 5774287) B5774287
theorem B7805569 : Blo 1520457 7805569 := bstep (se 2 (by rfl) ⟨2927088, by rfl⟩ : syracuseStep 7805569 = 5854177) B5854177
theorem B8223497 : Blo 1520457 8223497 := bstep (se 2 (by rfl) ⟨3083811, by rfl⟩ : syracuseStep 8223497 = 6167623) B6167623
theorem B7805737 : Blo 1520457 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B58497875 : Blo 1520457 58497875 := bstep (se 1 (by rfl) ⟨43873406, by rfl⟩ : syracuseStep 58497875 = 87746813) B87746813
theorem B17374073 : Blo 1520457 17374073 := bstep (se 2 (by rfl) ⟨6515277, by rfl⟩ : syracuseStep 17374073 = 13030555) B13030555
theorem B3423167 : Blo 1520457 3423167 := bstep (se 1 (by rfl) ⟨2567375, by rfl⟩ : syracuseStep 3423167 = 5134751) B5134751
theorem B3423815 : Blo 1520457 3423815 := bstep (se 1 (by rfl) ⟨2567861, by rfl⟩ : syracuseStep 3423815 = 5135723) B5135723
theorem B6495835 : Blo 1520457 6495835 := bstep (se 1 (by rfl) ⟨4871876, by rfl⟩ : syracuseStep 6495835 = 9743753) B9743753
theorem B3423995 : Blo 1520457 3423995 := bstep (se 1 (by rfl) ⟨2567996, by rfl⟩ : syracuseStep 3423995 = 5135993) B5135993
theorem B4333439 : Blo 1520457 4333439 := bstep (se 1 (by rfl) ⟨3250079, by rfl⟩ : syracuseStep 4333439 = 6500159) B6500159
theorem B3424283 : Blo 1520457 3424283 := bstep (se 1 (by rfl) ⟨2568212, by rfl⟩ : syracuseStep 3424283 = 5136425) B5136425
theorem B3424553 : Blo 1520457 3424553 := bstep (se 2 (by rfl) ⟨1284207, by rfl⟩ : syracuseStep 3424553 = 2568415) B2568415
theorem B10961639 : Blo 1520457 10961639 := bstep (se 1 (by rfl) ⟨8221229, by rfl⟩ : syracuseStep 10961639 = 16442459) B16442459
theorem B6497783 : Blo 1520457 6497783 := bstep (se 1 (by rfl) ⟨4873337, by rfl⟩ : syracuseStep 6497783 = 9746675) B9746675
theorem B11110051 : Blo 1520457 11110051 := bstep (se 1 (by rfl) ⟨8332538, by rfl⟩ : syracuseStep 11110051 = 16665077) B16665077
theorem B2565823 : Blo 1520457 2565823 := bstep (se 1 (by rfl) ⟨1924367, by rfl⟩ : syracuseStep 2565823 = 3848735) B3848735
theorem B5482331 : Blo 1520457 5482331 := bstep (se 1 (by rfl) ⟨4111748, by rfl⟩ : syracuseStep 5482331 = 8223497) B8223497
theorem B16451585 : Blo 1520457 16451585 := bstep (se 2 (by rfl) ⟨6169344, by rfl⟩ : syracuseStep 16451585 = 12338689) B12338689
theorem B11716609 : Blo 1520457 11716609 := bstep (se 2 (by rfl) ⟨4393728, by rfl⟩ : syracuseStep 11716609 = 8787457) B8787457
theorem B8661113 : Blo 1520457 8661113 := bstep (se 2 (by rfl) ⟨3247917, by rfl⟩ : syracuseStep 8661113 = 6495835) B6495835
theorem B2435849 : Blo 1520457 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B8227631 : Blo 1520457 8227631 := bstep (se 1 (by rfl) ⟨6170723, by rfl⟩ : syracuseStep 8227631 = 12341447) B12341447
theorem B2436079 : Blo 1520457 2436079 := bstep (se 1 (by rfl) ⟨1827059, by rfl⟩ : syracuseStep 2436079 = 3654119) B3654119
theorem B2165791 : Blo 1520457 2165791 := bstep (se 1 (by rfl) ⟨1624343, by rfl⟩ : syracuseStep 2165791 = 3248687) B3248687
theorem B105450545 : Blo 1520457 105450545 := bstep (se 2 (by rfl) ⟨39543954, by rfl⟩ : syracuseStep 105450545 = 79087909) B79087909
theorem B2567335 : Blo 1520457 2567335 := bstep (se 1 (by rfl) ⟨1925501, by rfl⟩ : syracuseStep 2567335 = 3851003) B3851003
theorem B5778647 : Blo 1520457 5778647 := bstep (se 1 (by rfl) ⟨4333985, by rfl⟩ : syracuseStep 5778647 = 8667971) B8667971
theorem B5131727 : Blo 1520457 5131727 := bstep (se 1 (by rfl) ⟨3848795, by rfl⟩ : syracuseStep 5131727 = 7697591) B7697591
theorem B2280959 : Blo 1520457 2280959 := bstep (se 1 (by rfl) ⟨1710719, by rfl⟩ : syracuseStep 2280959 = 3421439) B3421439
theorem B1625599 : Blo 1520457 1625599 := bstep (se 1 (by rfl) ⟨1219199, by rfl⟩ : syracuseStep 1625599 = 2438399) B2438399
theorem B10407425 : Blo 1520457 10407425 := bstep (se 2 (by rfl) ⟨3902784, by rfl⟩ : syracuseStep 10407425 = 7805569) B7805569
theorem B2166383 : Blo 1520457 2166383 := bstep (se 1 (by rfl) ⟨1624787, by rfl⟩ : syracuseStep 2166383 = 3249575) B3249575
theorem B10407649 : Blo 1520457 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B5206123 : Blo 1520457 5206123 := bstep (se 1 (by rfl) ⟨3904592, by rfl⟩ : syracuseStep 5206123 = 7809185) B7809185
theorem B7704719 : Blo 1520457 7704719 := bstep (se 1 (by rfl) ⟨5778539, by rfl⟩ : syracuseStep 7704719 = 11557079) B11557079
theorem B2928815 : Blo 1520457 2928815 := bstep (se 1 (by rfl) ⟨2196611, by rfl⟩ : syracuseStep 2928815 = 4393223) B4393223
theorem B9253163 : Blo 1520457 9253163 := bstep (se 1 (by rfl) ⟨6939872, by rfl⟩ : syracuseStep 9253163 = 13879745) B13879745
theorem B5132699 : Blo 1520457 5132699 := bstep (se 1 (by rfl) ⟨3849524, by rfl⟩ : syracuseStep 5132699 = 7699049) B7699049
theorem B38998583 : Blo 1520457 38998583 := bstep (se 1 (by rfl) ⟨29248937, by rfl⟩ : syracuseStep 38998583 = 58497875) B58497875
theorem B2282111 : Blo 1520457 2282111 := bstep (se 1 (by rfl) ⟨1711583, by rfl⟩ : syracuseStep 2282111 = 3423167) B3423167
theorem B3470111 : Blo 1520457 3470111 := bstep (se 1 (by rfl) ⟨2602583, by rfl⟩ : syracuseStep 3470111 = 5205167) B5205167
theorem B1520607 : Blo 1520457 1520607 := bstep (se 1 (by rfl) ⟨1140455, by rfl⟩ : syracuseStep 1520607 = 2280911) B2280911
theorem B46330861 : Blo 1520457 46330861 := bstep (se 3 (by rfl) ⟨8687036, by rfl⟩ : syracuseStep 46330861 = 17374073) B17374073
theorem B1520667 : Blo 1520457 1520667 := bstep (se 1 (by rfl) ⟨1140500, by rfl⟩ : syracuseStep 1520667 = 2281001) B2281001
theorem B2282543 : Blo 1520457 2282543 := bstep (se 1 (by rfl) ⟨1711907, by rfl⟩ : syracuseStep 2282543 = 3423815) B3423815
theorem B2282663 : Blo 1520457 2282663 := bstep (se 1 (by rfl) ⟨1711997, by rfl⟩ : syracuseStep 2282663 = 3423995) B3423995
theorem B1520863 : Blo 1520457 1520863 := bstep (se 1 (by rfl) ⟨1140647, by rfl⟩ : syracuseStep 1520863 = 2281295) B2281295
theorem B2888959 : Blo 1520457 2888959 := bstep (se 1 (by rfl) ⟨2166719, by rfl⟩ : syracuseStep 2888959 = 4333439) B4333439
theorem B1520943 : Blo 1520457 1520943 := bstep (se 1 (by rfl) ⟨1140707, by rfl⟩ : syracuseStep 1520943 = 2281415) B2281415
theorem B2282831 : Blo 1520457 2282831 := bstep (se 1 (by rfl) ⟨1712123, by rfl⟩ : syracuseStep 2282831 = 3424247) B3424247
theorem B9745751 : Blo 1520457 9745751 := bstep (se 1 (by rfl) ⟨7309313, by rfl⟩ : syracuseStep 9745751 = 14618627) B14618627
theorem B1520999 : Blo 1520457 1520999 := bstep (se 1 (by rfl) ⟨1140749, by rfl⟩ : syracuseStep 1520999 = 2281499) B2281499
theorem B3085823 : Blo 1520457 3085823 := bstep (se 1 (by rfl) ⟨2314367, by rfl⟩ : syracuseStep 3085823 = 4628735) B4628735
theorem B1521183 : Blo 1520457 1521183 := bstep (se 1 (by rfl) ⟨1140887, by rfl⟩ : syracuseStep 1521183 = 2281775) B2281775
theorem B2283071 : Blo 1520457 2283071 := bstep (se 1 (by rfl) ⟨1712303, by rfl⟩ : syracuseStep 2283071 = 3424607) B3424607
theorem B1521255 : Blo 1520457 1521255 := bstep (se 1 (by rfl) ⟨1140941, by rfl⟩ : syracuseStep 1521255 = 2281883) B2281883
theorem B3421817 : Blo 1520457 3421817 := bstep (se 2 (by rfl) ⟨1283181, by rfl⟩ : syracuseStep 3421817 = 2566363) B2566363
theorem B1521279 : Blo 1520457 1521279 := bstep (se 1 (by rfl) ⟨1140959, by rfl⟩ : syracuseStep 1521279 = 2281919) B2281919
theorem B11548331 : Blo 1520457 11548331 := bstep (se 1 (by rfl) ⟨8661248, by rfl⟩ : syracuseStep 11548331 = 17322497) B17322497
theorem B1521343 : Blo 1520457 1521343 := bstep (se 1 (by rfl) ⟨1141007, by rfl⟩ : syracuseStep 1521343 = 2282015) B2282015
theorem B2889407 : Blo 1520457 2889407 := bstep (se 1 (by rfl) ⟨2167055, by rfl⟩ : syracuseStep 2889407 = 4334111) B4334111
theorem B9754465 : Blo 1520457 9754465 := bstep (se 2 (by rfl) ⟨3657924, by rfl⟩ : syracuseStep 9754465 = 7315849) B7315849
theorem B1521535 : Blo 1520457 1521535 := bstep (se 1 (by rfl) ⟨1141151, by rfl⟩ : syracuseStep 1521535 = 2282303) B2282303
theorem B13883281 : Blo 1520457 13883281 := bstep (se 2 (by rfl) ⟨5206230, by rfl⟩ : syracuseStep 13883281 = 10412461) B10412461
theorem B2283431 : Blo 1520457 2283431 := bstep (se 1 (by rfl) ⟨1712573, by rfl⟩ : syracuseStep 2283431 = 3425147) B3425147
theorem B1521631 : Blo 1520457 1521631 := bstep (se 1 (by rfl) ⟨1141223, by rfl⟩ : syracuseStep 1521631 = 2282447) B2282447
theorem B3422177 : Blo 1520457 3422177 := bstep (se 2 (by rfl) ⟨1283316, by rfl⟩ : syracuseStep 3422177 = 2566633) B2566633
theorem B62453749 : Blo 1520457 62453749 := bstep (se 5 (by rfl) ⟨2927519, by rfl⟩ : syracuseStep 62453749 = 5855039) B5855039
theorem B2283515 : Blo 1520457 2283515 := bstep (se 1 (by rfl) ⟨1712636, by rfl⟩ : syracuseStep 2283515 = 3425273) B3425273
theorem B1521691 : Blo 1520457 1521691 := bstep (se 1 (by rfl) ⟨1141268, by rfl⟩ : syracuseStep 1521691 = 2282537) B2282537
theorem B2283551 : Blo 1520457 2283551 := bstep (se 1 (by rfl) ⟨1712663, by rfl⟩ : syracuseStep 2283551 = 3425327) B3425327
theorem B7706663 : Blo 1520457 7706663 := bstep (se 1 (by rfl) ⟨5779997, by rfl⟩ : syracuseStep 7706663 = 11559995) B11559995
theorem B1521711 : Blo 1520457 1521711 := bstep (se 1 (by rfl) ⟨1141283, by rfl⟩ : syracuseStep 1521711 = 2282567) B2282567
theorem B2283575 : Blo 1520457 2283575 := bstep (se 1 (by rfl) ⟨1712681, by rfl⟩ : syracuseStep 2283575 = 3425363) B3425363
theorem B2283641 : Blo 1520457 2283641 := bstep (se 2 (by rfl) ⟨856365, by rfl⟩ : syracuseStep 2283641 = 1712731) B1712731
theorem B1521831 : Blo 1520457 1521831 := bstep (se 1 (by rfl) ⟨1141373, by rfl⟩ : syracuseStep 1521831 = 2282747) B2282747
theorem B1521871 : Blo 1520457 1521871 := bstep (se 1 (by rfl) ⟨1141403, by rfl⟩ : syracuseStep 1521871 = 2282807) B2282807
theorem B6502619 : Blo 1520457 6502619 := bstep (se 1 (by rfl) ⟨4876964, by rfl⟩ : syracuseStep 6502619 = 9753929) B9753929
theorem B1522075 : Blo 1520457 1522075 := bstep (se 1 (by rfl) ⟨1141556, by rfl⟩ : syracuseStep 1522075 = 2283113) B2283113
theorem B5773801 : Blo 1520457 5773801 := bstep (se 2 (by rfl) ⟨2165175, by rfl⟩ : syracuseStep 5773801 = 4330351) B4330351
theorem B6502943 : Blo 1520457 6502943 := bstep (se 1 (by rfl) ⟨4877207, by rfl⟩ : syracuseStep 6502943 = 9754415) B9754415
theorem B1522431 : Blo 1520457 1522431 := bstep (se 1 (by rfl) ⟨1141823, by rfl⟩ : syracuseStep 1522431 = 2283647) B2283647
theorem B5774561 : Blo 1520457 5774561 := bstep (se 2 (by rfl) ⟨2165460, by rfl⟩ : syracuseStep 5774561 = 4330921) B4330921
theorem B5774759 : Blo 1520457 5774759 := bstep (se 1 (by rfl) ⟨4331069, by rfl⟩ : syracuseStep 5774759 = 8662139) B8662139
theorem B6495869 : Blo 1520457 6495869 := bstep (se 3 (by rfl) ⟨1217975, by rfl⟩ : syracuseStep 6495869 = 2435951) B2435951
theorem B1711867 : Blo 1520457 1711867 := bstep (se 1 (by rfl) ⟨1283900, by rfl⟩ : syracuseStep 1711867 = 2567801) B2567801
theorem B98664317 : Blo 1520457 98664317 := bstep (se 3 (by rfl) ⟨18499559, by rfl⟩ : syracuseStep 98664317 = 36999119) B36999119
theorem B15622145 : Blo 1520457 15622145 := bstep (se 2 (by rfl) ⟨5858304, by rfl⟩ : syracuseStep 15622145 = 11716609) B11716609
theorem B5136479 : Blo 1520457 5136479 := bstep (se 1 (by rfl) ⟨3852359, by rfl⟩ : syracuseStep 5136479 = 7704719) B7704719
theorem B7307759 : Blo 1520457 7307759 := bstep (se 1 (by rfl) ⟨5480819, by rfl⟩ : syracuseStep 7307759 = 10961639) B10961639
theorem B24675101 : Blo 1520457 24675101 := bstep (se 3 (by rfl) ⟨4626581, by rfl⟩ : syracuseStep 24675101 = 9253163) B9253163
theorem B6497167 : Blo 1520457 6497167 := bstep (se 1 (by rfl) ⟨4872875, by rfl⟩ : syracuseStep 6497167 = 9745751) B9745751
theorem B1926271 : Blo 1520457 1926271 := bstep (se 1 (by rfl) ⟨1444703, by rfl⟩ : syracuseStep 1926271 = 2889407) B2889407
theorem B3654887 : Blo 1520457 3654887 := bstep (se 1 (by rfl) ⟨2741165, by rfl⟩ : syracuseStep 3654887 = 5482331) B5482331
theorem B5137775 : Blo 1520457 5137775 := bstep (se 1 (by rfl) ⟨3853331, by rfl⟩ : syracuseStep 5137775 = 7706663) B7706663
theorem B4335079 : Blo 1520457 4335079 := bstep (se 1 (by rfl) ⟨3251309, by rfl⟩ : syracuseStep 4335079 = 6502619) B6502619
theorem B5777021 : Blo 1520457 5777021 := bstep (se 3 (by rfl) ⟨1083191, by rfl⟩ : syracuseStep 5777021 = 2166383) B2166383
theorem B3851945 : Blo 1520457 3851945 := bstep (se 2 (by rfl) ⟨1444479, by rfl⟩ : syracuseStep 3851945 = 2888959) B2888959
theorem B4335295 : Blo 1520457 4335295 := bstep (se 1 (by rfl) ⟨3251471, by rfl⟩ : syracuseStep 4335295 = 6502943) B6502943
theorem B1623899 : Blo 1520457 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B3852431 : Blo 1520457 3852431 := bstep (se 1 (by rfl) ⟨2889323, by rfl⟩ : syracuseStep 3852431 = 5778647) B5778647
theorem B14813401 : Blo 1520457 14813401 := bstep (se 2 (by rfl) ⟨5555025, by rfl⟩ : syracuseStep 14813401 = 11110051) B11110051
theorem B65776211 : Blo 1520457 65776211 := bstep (se 1 (by rfl) ⟨49332158, by rfl⟩ : syracuseStep 65776211 = 98664317) B98664317
theorem B8669861 : Blo 1520457 8669861 := bstep (se 4 (by rfl) ⟨812799, by rfl⟩ : syracuseStep 8669861 = 1625599) B1625599
theorem B1952543 : Blo 1520457 1952543 := bstep (se 1 (by rfl) ⟨1464407, by rfl⟩ : syracuseStep 1952543 = 2928815) B2928815
theorem B281201453 : Blo 1520457 281201453 := bstep (se 3 (by rfl) ⟨52725272, by rfl⟩ : syracuseStep 281201453 = 105450545) B105450545
theorem B6941497 : Blo 1520457 6941497 := bstep (se 2 (by rfl) ⟨2603061, by rfl⟩ : syracuseStep 6941497 = 5206123) B5206123
theorem B2313407 : Blo 1520457 2313407 := bstep (se 1 (by rfl) ⟨1735055, by rfl⟩ : syracuseStep 2313407 = 3470111) B3470111
theorem B2281211 : Blo 1520457 2281211 := bstep (se 1 (by rfl) ⟨1710908, by rfl⟩ : syracuseStep 2281211 = 3421817) B3421817
theorem B3248105 : Blo 1520457 3248105 := bstep (se 2 (by rfl) ⟨1218039, by rfl⟩ : syracuseStep 3248105 = 2436079) B2436079
theorem B2281451 : Blo 1520457 2281451 := bstep (se 1 (by rfl) ⟨1711088, by rfl⟩ : syracuseStep 2281451 = 3422177) B3422177
theorem B8228861 : Blo 1520457 8228861 := bstep (se 3 (by rfl) ⟨1542911, by rfl⟩ : syracuseStep 8228861 = 3085823) B3085823
theorem B2887721 : Blo 1520457 2887721 := bstep (se 2 (by rfl) ⟨1082895, by rfl⟩ : syracuseStep 2887721 = 2165791) B2165791
theorem B5485087 : Blo 1520457 5485087 := bstep (se 1 (by rfl) ⟨4113815, by rfl⟩ : syracuseStep 5485087 = 8227631) B8227631
theorem B74044165 : Blo 1520457 74044165 := bstep (se 4 (by rfl) ⟨6941640, by rfl⟩ : syracuseStep 74044165 = 13883281) B13883281
theorem B3421097 : Blo 1520457 3421097 := bstep (se 2 (by rfl) ⟨1282911, by rfl⟩ : syracuseStep 3421097 = 2565823) B2565823
theorem B3421151 : Blo 1520457 3421151 := bstep (se 1 (by rfl) ⟨2565863, by rfl⟩ : syracuseStep 3421151 = 5131727) B5131727
theorem B2282489 : Blo 1520457 2282489 := bstep (se 2 (by rfl) ⟨855933, by rfl⟩ : syracuseStep 2282489 = 1711867) B1711867
theorem B1520639 : Blo 1520457 1520639 := bstep (se 1 (by rfl) ⟨1140479, by rfl⟩ : syracuseStep 1520639 = 2280959) B2280959
theorem B4330579 : Blo 1520457 4330579 := bstep (se 1 (by rfl) ⟨3247934, by rfl⟩ : syracuseStep 4330579 = 6495869) B6495869
theorem B13005953 : Blo 1520457 13005953 := bstep (se 2 (by rfl) ⟨4877232, by rfl⟩ : syracuseStep 13005953 = 9754465) B9754465
theorem B2282855 : Blo 1520457 2282855 := bstep (se 1 (by rfl) ⟨1712141, by rfl⟩ : syracuseStep 2282855 = 3424283) B3424283
theorem B2283035 : Blo 1520457 2283035 := bstep (se 1 (by rfl) ⟨1712276, by rfl⟩ : syracuseStep 2283035 = 3424553) B3424553
theorem B3421799 : Blo 1520457 3421799 := bstep (se 1 (by rfl) ⟨2566349, by rfl⟩ : syracuseStep 3421799 = 5132699) B5132699
theorem B25999055 : Blo 1520457 25999055 := bstep (se 1 (by rfl) ⟨19499291, by rfl⟩ : syracuseStep 25999055 = 38998583) B38998583
theorem B1521407 : Blo 1520457 1521407 := bstep (se 1 (by rfl) ⟨1141055, by rfl⟩ : syracuseStep 1521407 = 2282111) B2282111
theorem B7698401 : Blo 1520457 7698401 := bstep (se 2 (by rfl) ⟨2886900, by rfl⟩ : syracuseStep 7698401 = 5773801) B5773801
theorem B1521695 : Blo 1520457 1521695 := bstep (se 1 (by rfl) ⟨1141271, by rfl⟩ : syracuseStep 1521695 = 2282543) B2282543
theorem B1521775 : Blo 1520457 1521775 := bstep (se 1 (by rfl) ⟨1141331, by rfl⟩ : syracuseStep 1521775 = 2282663) B2282663
theorem B1521887 : Blo 1520457 1521887 := bstep (se 1 (by rfl) ⟨1141415, by rfl⟩ : syracuseStep 1521887 = 2282831) B2282831
theorem B4331855 : Blo 1520457 4331855 := bstep (se 1 (by rfl) ⟨3248891, by rfl⟩ : syracuseStep 4331855 = 6497783) B6497783
theorem B1522047 : Blo 1520457 1522047 := bstep (se 1 (by rfl) ⟨1141535, by rfl⟩ : syracuseStep 1522047 = 2283071) B2283071
theorem B7698887 : Blo 1520457 7698887 := bstep (se 1 (by rfl) ⟨5774165, by rfl⟩ : syracuseStep 7698887 = 11548331) B11548331
theorem B1522287 : Blo 1520457 1522287 := bstep (se 1 (by rfl) ⟨1141715, by rfl⟩ : syracuseStep 1522287 = 2283431) B2283431
theorem B61774481 : Blo 1520457 61774481 := bstep (se 2 (by rfl) ⟨23165430, by rfl⟩ : syracuseStep 61774481 = 46330861) B46330861
theorem B1522343 : Blo 1520457 1522343 := bstep (se 1 (by rfl) ⟨1141757, by rfl⟩ : syracuseStep 1522343 = 2283515) B2283515
theorem B10967723 : Blo 1520457 10967723 := bstep (se 1 (by rfl) ⟨8225792, by rfl⟩ : syracuseStep 10967723 = 16451585) B16451585
theorem B27753133 : Blo 1520457 27753133 := bstep (se 3 (by rfl) ⟨5203712, by rfl⟩ : syracuseStep 27753133 = 10407425) B10407425
theorem B1522367 : Blo 1520457 1522367 := bstep (se 1 (by rfl) ⟨1141775, by rfl⟩ : syracuseStep 1522367 = 2283551) B2283551
theorem B1522383 : Blo 1520457 1522383 := bstep (se 1 (by rfl) ⟨1141787, by rfl⟩ : syracuseStep 1522383 = 2283575) B2283575
theorem B5774075 : Blo 1520457 5774075 := bstep (se 1 (by rfl) ⟨4330556, by rfl⟩ : syracuseStep 5774075 = 8661113) B8661113
theorem B1522427 : Blo 1520457 1522427 := bstep (se 1 (by rfl) ⟨1141820, by rfl⟩ : syracuseStep 1522427 = 2283641) B2283641
theorem B3423113 : Blo 1520457 3423113 := bstep (se 2 (by rfl) ⟨1283667, by rfl⟩ : syracuseStep 3423113 = 2567335) B2567335
theorem B3849707 : Blo 1520457 3849707 := bstep (se 1 (by rfl) ⟨2887280, by rfl⟩ : syracuseStep 3849707 = 5774561) B5774561
theorem B3849839 : Blo 1520457 3849839 := bstep (se 1 (by rfl) ⟨2887379, by rfl⟩ : syracuseStep 3849839 = 5774759) B5774759
theorem B13876865 : Blo 1520457 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B83271665 : Blo 1520457 83271665 := bstep (se 2 (by rfl) ⟨31226874, by rfl⟩ : syracuseStep 83271665 = 62453749) B62453749
theorem B1925147 : Blo 1520457 1925147 := bstep (se 1 (by rfl) ⟨1443860, by rfl⟩ : syracuseStep 1925147 = 2887721) B2887721
theorem B3424319 : Blo 1520457 3424319 := bstep (se 1 (by rfl) ⟨2568239, by rfl⟩ : syracuseStep 3424319 = 5136479) B5136479
theorem B19751201 : Blo 1520457 19751201 := bstep (se 2 (by rfl) ⟨7406700, by rfl⟩ : syracuseStep 19751201 = 14813401) B14813401
theorem B16450067 : Blo 1520457 16450067 := bstep (se 1 (by rfl) ⟨12337550, by rfl⟩ : syracuseStep 16450067 = 24675101) B24675101
theorem B37004177 : Blo 1520457 37004177 := bstep (se 2 (by rfl) ⟨13876566, by rfl⟩ : syracuseStep 37004177 = 27753133) B27753133
theorem B3425183 : Blo 1520457 3425183 := bstep (se 1 (by rfl) ⟨2568887, by rfl⟩ : syracuseStep 3425183 = 5137775) B5137775
theorem B3851347 : Blo 1520457 3851347 := bstep (se 1 (by rfl) ⟨2888510, by rfl⟩ : syracuseStep 3851347 = 5777021) B5777021
theorem B41182987 : Blo 1520457 41182987 := bstep (se 1 (by rfl) ⟨30887240, by rfl⟩ : syracuseStep 41182987 = 61774481) B61774481
theorem B187467635 : Blo 1520457 187467635 := bstep (se 1 (by rfl) ⟨140600726, by rfl⟩ : syracuseStep 187467635 = 281201453) B281201453
theorem B1542271 : Blo 1520457 1542271 := bstep (se 1 (by rfl) ⟨1156703, by rfl⟩ : syracuseStep 1542271 = 2313407) B2313407
theorem B2566471 : Blo 1520457 2566471 := bstep (se 1 (by rfl) ⟨1924853, by rfl⟩ : syracuseStep 2566471 = 3849707) B3849707
theorem B2566559 : Blo 1520457 2566559 := bstep (se 1 (by rfl) ⟨1924919, by rfl⟩ : syracuseStep 2566559 = 3849839) B3849839
theorem B9251243 : Blo 1520457 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B8661613 : Blo 1520457 8661613 := bstep (se 3 (by rfl) ⟨1624052, by rfl⟩ : syracuseStep 8661613 = 3248105) B3248105
theorem B10414763 : Blo 1520457 10414763 := bstep (se 1 (by rfl) ⟨7811072, by rfl⟩ : syracuseStep 10414763 = 15622145) B15622145
theorem B2280731 : Blo 1520457 2280731 := bstep (se 1 (by rfl) ⟨1710548, by rfl⟩ : syracuseStep 2280731 = 3421097) B3421097
theorem B2280767 : Blo 1520457 2280767 := bstep (se 1 (by rfl) ⟨1710575, by rfl⟩ : syracuseStep 2280767 = 3421151) B3421151
theorem B8670635 : Blo 1520457 8670635 := bstep (se 1 (by rfl) ⟨6502976, by rfl⟩ : syracuseStep 8670635 = 13005953) B13005953
theorem B98725553 : Blo 1520457 98725553 := bstep (se 2 (by rfl) ⟨37022082, by rfl⟩ : syracuseStep 98725553 = 74044165) B74044165
theorem B2281199 : Blo 1520457 2281199 := bstep (se 1 (by rfl) ⟨1710899, by rfl⟩ : syracuseStep 2281199 = 3421799) B3421799
theorem B2567963 : Blo 1520457 2567963 := bstep (se 1 (by rfl) ⟨1925972, by rfl⟩ : syracuseStep 2567963 = 3851945) B3851945
theorem B8662889 : Blo 1520457 8662889 := bstep (se 2 (by rfl) ⟨3248583, by rfl⟩ : syracuseStep 8662889 = 6497167) B6497167
theorem B5132267 : Blo 1520457 5132267 := bstep (se 1 (by rfl) ⟨3849200, by rfl⟩ : syracuseStep 5132267 = 7698401) B7698401
theorem B2568287 : Blo 1520457 2568287 := bstep (se 1 (by rfl) ⟨1926215, by rfl⟩ : syracuseStep 2568287 = 3852431) B3852431
theorem B2568361 : Blo 1520457 2568361 := bstep (se 2 (by rfl) ⟨963135, by rfl⟩ : syracuseStep 2568361 = 1926271) B1926271
theorem B2887903 : Blo 1520457 2887903 := bstep (se 1 (by rfl) ⟨2165927, by rfl⟩ : syracuseStep 2887903 = 4331855) B4331855
theorem B5132591 : Blo 1520457 5132591 := bstep (se 1 (by rfl) ⟨3849443, by rfl⟩ : syracuseStep 5132591 = 7698887) B7698887
theorem B5779907 : Blo 1520457 5779907 := bstep (se 1 (by rfl) ⟨4334930, by rfl⟩ : syracuseStep 5779907 = 8669861) B8669861
theorem B7311815 : Blo 1520457 7311815 := bstep (se 1 (by rfl) ⟨5483861, by rfl⟩ : syracuseStep 7311815 = 10967723) B10967723
theorem B2282075 : Blo 1520457 2282075 := bstep (se 1 (by rfl) ⟨1711556, by rfl⟩ : syracuseStep 2282075 = 3423113) B3423113
theorem B5780105 : Blo 1520457 5780105 := bstep (se 2 (by rfl) ⟨2167539, by rfl⟩ : syracuseStep 5780105 = 4335079) B4335079
theorem B5206781 : Blo 1520457 5206781 := bstep (se 3 (by rfl) ⟨976271, by rfl⟩ : syracuseStep 5206781 = 1952543) B1952543
theorem B4330397 : Blo 1520457 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B5780393 : Blo 1520457 5780393 := bstep (se 2 (by rfl) ⟨2167647, by rfl⟩ : syracuseStep 5780393 = 4335295) B4335295
theorem B1520807 : Blo 1520457 1520807 := bstep (se 1 (by rfl) ⟨1140605, by rfl⟩ : syracuseStep 1520807 = 2281211) B2281211
theorem B1520967 : Blo 1520457 1520967 := bstep (se 1 (by rfl) ⟨1140725, by rfl⟩ : syracuseStep 1520967 = 2281451) B2281451
theorem B55514443 : Blo 1520457 55514443 := bstep (se 1 (by rfl) ⟨41635832, by rfl⟩ : syracuseStep 55514443 = 83271665) B83271665
theorem B5485907 : Blo 1520457 5485907 := bstep (se 1 (by rfl) ⟨4114430, by rfl⟩ : syracuseStep 5485907 = 8228861) B8228861
theorem B4871839 : Blo 1520457 4871839 := bstep (se 1 (by rfl) ⟨3653879, by rfl⟩ : syracuseStep 4871839 = 7307759) B7307759
theorem B1521659 : Blo 1520457 1521659 := bstep (se 1 (by rfl) ⟨1141244, by rfl⟩ : syracuseStep 1521659 = 2282489) B2282489
theorem B7313449 : Blo 1520457 7313449 := bstep (se 2 (by rfl) ⟨2742543, by rfl⟩ : syracuseStep 7313449 = 5485087) B5485087
theorem B1521903 : Blo 1520457 1521903 := bstep (se 1 (by rfl) ⟨1141427, by rfl⟩ : syracuseStep 1521903 = 2282855) B2282855
theorem B1522023 : Blo 1520457 1522023 := bstep (se 1 (by rfl) ⟨1141517, by rfl⟩ : syracuseStep 1522023 = 2283035) B2283035
theorem B9255329 : Blo 1520457 9255329 := bstep (se 2 (by rfl) ⟨3470748, by rfl⟩ : syracuseStep 9255329 = 6941497) B6941497
theorem B17332703 : Blo 1520457 17332703 := bstep (se 1 (by rfl) ⟨12999527, by rfl⟩ : syracuseStep 17332703 = 25999055) B25999055
theorem B5774105 : Blo 1520457 5774105 := bstep (se 2 (by rfl) ⟨2165289, by rfl⟩ : syracuseStep 5774105 = 4330579) B4330579
theorem B43850807 : Blo 1520457 43850807 := bstep (se 1 (by rfl) ⟨32888105, by rfl⟩ : syracuseStep 43850807 = 65776211) B65776211
theorem B3849383 : Blo 1520457 3849383 := bstep (se 1 (by rfl) ⟨2887037, by rfl⟩ : syracuseStep 3849383 = 5774075) B5774075
theorem B38985461 : Blo 1520457 38985461 := bstep (se 5 (by rfl) ⟨1827443, by rfl⟩ : syracuseStep 38985461 = 3654887) B3654887
theorem B1712191 : Blo 1520457 1712191 := bstep (se 1 (by rfl) ⟨1284143, by rfl⟩ : syracuseStep 1712191 = 2568287) B2568287
theorem B2056361 : Blo 1520457 2056361 := bstep (se 2 (by rfl) ⟨771135, by rfl⟩ : syracuseStep 2056361 = 1542271) B1542271
theorem B3424481 : Blo 1520457 3424481 := bstep (se 2 (by rfl) ⟨1284180, by rfl⟩ : syracuseStep 3424481 = 2568361) B2568361
theorem B3850537 : Blo 1520457 3850537 := bstep (se 2 (by rfl) ⟨1443951, by rfl⟩ : syracuseStep 3850537 = 2887903) B2887903
theorem B4874543 : Blo 1520457 4874543 := bstep (se 1 (by rfl) ⟨3655907, by rfl⟩ : syracuseStep 4874543 = 7311815) B7311815
theorem B124978423 : Blo 1520457 124978423 := bstep (se 1 (by rfl) ⟨93733817, by rfl⟩ : syracuseStep 124978423 = 187467635) B187467635
theorem B6170219 : Blo 1520457 6170219 := bstep (se 1 (by rfl) ⟨4627664, by rfl⟩ : syracuseStep 6170219 = 9255329) B9255329
theorem B2566255 : Blo 1520457 2566255 := bstep (se 1 (by rfl) ⟨1924691, by rfl⟩ : syracuseStep 2566255 = 3849383) B3849383
theorem B65817035 : Blo 1520457 65817035 := bstep (se 1 (by rfl) ⟨49362776, by rfl⟩ : syracuseStep 65817035 = 98725553) B98725553
theorem B9751265 : Blo 1520457 9751265 := bstep (se 2 (by rfl) ⟨3656724, by rfl⟩ : syracuseStep 9751265 = 7313449) B7313449
theorem B13167467 : Blo 1520457 13167467 := bstep (se 1 (by rfl) ⟨9875600, by rfl⟩ : syracuseStep 13167467 = 19751201) B19751201
theorem B3853271 : Blo 1520457 3853271 := bstep (se 1 (by rfl) ⟨2889953, by rfl⟩ : syracuseStep 3853271 = 5779907) B5779907
theorem B3853403 : Blo 1520457 3853403 := bstep (se 1 (by rfl) ⟨2890052, by rfl⟩ : syracuseStep 3853403 = 5780105) B5780105
theorem B24669451 : Blo 1520457 24669451 := bstep (se 1 (by rfl) ⟨18502088, by rfl⟩ : syracuseStep 24669451 = 37004177) B37004177
theorem B2886931 : Blo 1520457 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B3853595 : Blo 1520457 3853595 := bstep (se 1 (by rfl) ⟨2890196, by rfl⟩ : syracuseStep 3853595 = 5780393) B5780393
theorem B11555135 : Blo 1520457 11555135 := bstep (se 1 (by rfl) ⟨8666351, by rfl⟩ : syracuseStep 11555135 = 17332703) B17332703
theorem B74019257 : Blo 1520457 74019257 := bstep (se 2 (by rfl) ⟨27757221, by rfl⟩ : syracuseStep 74019257 = 55514443) B55514443
theorem B6943175 : Blo 1520457 6943175 := bstep (se 1 (by rfl) ⟨5207381, by rfl⟩ : syracuseStep 6943175 = 10414763) B10414763
theorem B29233871 : Blo 1520457 29233871 := bstep (se 1 (by rfl) ⟨21925403, by rfl⟩ : syracuseStep 29233871 = 43850807) B43850807
theorem B1520487 : Blo 1520457 1520487 := bstep (se 1 (by rfl) ⟨1140365, by rfl⟩ : syracuseStep 1520487 = 2280731) B2280731
theorem B1520511 : Blo 1520457 1520511 := bstep (se 1 (by rfl) ⟨1140383, by rfl⟩ : syracuseStep 1520511 = 2280767) B2280767
theorem B5780423 : Blo 1520457 5780423 := bstep (se 1 (by rfl) ⟨4335317, by rfl⟩ : syracuseStep 5780423 = 8670635) B8670635
theorem B1520799 : Blo 1520457 1520799 := bstep (se 1 (by rfl) ⟨1140599, by rfl⟩ : syracuseStep 1520799 = 2281199) B2281199
theorem B25990307 : Blo 1520457 25990307 := bstep (se 1 (by rfl) ⟨19492730, by rfl⟩ : syracuseStep 25990307 = 38985461) B38985461
theorem B3421511 : Blo 1520457 3421511 := bstep (se 1 (by rfl) ⟨2566133, by rfl⟩ : syracuseStep 3421511 = 5132267) B5132267
theorem B2282879 : Blo 1520457 2282879 := bstep (se 1 (by rfl) ⟨1712159, by rfl⟩ : syracuseStep 2282879 = 3424319) B3424319
theorem B5133725 : Blo 1520457 5133725 := bstep (se 3 (by rfl) ⟨962573, by rfl⟩ : syracuseStep 5133725 = 1925147) B1925147
theorem B3421727 : Blo 1520457 3421727 := bstep (se 1 (by rfl) ⟨2566295, by rfl⟩ : syracuseStep 3421727 = 5132591) B5132591
theorem B1521383 : Blo 1520457 1521383 := bstep (se 1 (by rfl) ⟨1141037, by rfl⟩ : syracuseStep 1521383 = 2282075) B2282075
theorem B3421961 : Blo 1520457 3421961 := bstep (se 2 (by rfl) ⟨1283235, by rfl⟩ : syracuseStep 3421961 = 2566471) B2566471
theorem B3471187 : Blo 1520457 3471187 := bstep (se 1 (by rfl) ⟨2603390, by rfl⟩ : syracuseStep 3471187 = 5206781) B5206781
theorem B2283455 : Blo 1520457 2283455 := bstep (se 1 (by rfl) ⟨1712591, by rfl⟩ : syracuseStep 2283455 = 3425183) B3425183
theorem B11548817 : Blo 1520457 11548817 := bstep (se 2 (by rfl) ⟨4330806, by rfl⟩ : syracuseStep 11548817 = 8661613) B8661613
theorem B14629085 : Blo 1520457 14629085 := bstep (se 3 (by rfl) ⟨2742953, by rfl⟩ : syracuseStep 14629085 = 5485907) B5485907
theorem B43866845 : Blo 1520457 43866845 := bstep (se 3 (by rfl) ⟨8225033, by rfl⟩ : syracuseStep 43866845 = 16450067) B16450067
theorem B5135129 : Blo 1520457 5135129 := bstep (se 2 (by rfl) ⟨1925673, by rfl⟩ : syracuseStep 5135129 = 3851347) B3851347
theorem B1711039 : Blo 1520457 1711039 := bstep (se 1 (by rfl) ⟨1283279, by rfl⟩ : syracuseStep 1711039 = 2566559) B2566559
theorem B6167495 : Blo 1520457 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B3849403 : Blo 1520457 3849403 := bstep (se 1 (by rfl) ⟨2887052, by rfl⟩ : syracuseStep 3849403 = 5774105) B5774105
theorem B6495785 : Blo 1520457 6495785 := bstep (se 2 (by rfl) ⟨2435919, by rfl⟩ : syracuseStep 6495785 = 4871839) B4871839
theorem B54910649 : Blo 1520457 54910649 := bstep (se 2 (by rfl) ⟨20591493, by rfl⟩ : syracuseStep 54910649 = 41182987) B41182987
theorem B1711975 : Blo 1520457 1711975 := bstep (se 1 (by rfl) ⟨1283981, by rfl⟩ : syracuseStep 1711975 = 2567963) B2567963
theorem B5775259 : Blo 1520457 5775259 := bstep (se 1 (by rfl) ⟨4331444, by rfl⟩ : syracuseStep 5775259 = 8662889) B8662889
theorem B4628783 : Blo 1520457 4628783 := bstep (se 1 (by rfl) ⟨3471587, by rfl⟩ : syracuseStep 4628783 = 6943175) B6943175
theorem B19489247 : Blo 1520457 19489247 := bstep (se 1 (by rfl) ⟨14616935, by rfl⟩ : syracuseStep 19489247 = 29233871) B29233871
theorem B17326871 : Blo 1520457 17326871 := bstep (se 1 (by rfl) ⟨12995153, by rfl⟩ : syracuseStep 17326871 = 25990307) B25990307
theorem B4113479 : Blo 1520457 4113479 := bstep (se 1 (by rfl) ⟨3085109, by rfl⟩ : syracuseStep 4113479 = 6170219) B6170219
theorem B43878023 : Blo 1520457 43878023 := bstep (se 1 (by rfl) ⟨32908517, by rfl⟩ : syracuseStep 43878023 = 65817035) B65817035
theorem B32892601 : Blo 1520457 32892601 := bstep (se 2 (by rfl) ⟨12334725, by rfl⟩ : syracuseStep 32892601 = 24669451) B24669451
theorem B7703423 : Blo 1520457 7703423 := bstep (se 1 (by rfl) ⟨5777567, by rfl⟩ : syracuseStep 7703423 = 11555135) B11555135
theorem B5483629 : Blo 1520457 5483629 := bstep (se 3 (by rfl) ⟨1028180, by rfl⟩ : syracuseStep 5483629 = 2056361) B2056361
theorem B3853615 : Blo 1520457 3853615 := bstep (se 1 (by rfl) ⟨2890211, by rfl⟩ : syracuseStep 3853615 = 5780423) B5780423
theorem B2281007 : Blo 1520457 2281007 := bstep (se 1 (by rfl) ⟨1710755, by rfl⟩ : syracuseStep 2281007 = 3421511) B3421511
theorem B2281151 : Blo 1520457 2281151 := bstep (se 1 (by rfl) ⟨1710863, by rfl⟩ : syracuseStep 2281151 = 3421727) B3421727
theorem B2281307 : Blo 1520457 2281307 := bstep (se 1 (by rfl) ⟨1710980, by rfl⟩ : syracuseStep 2281307 = 3421961) B3421961
theorem B2281385 : Blo 1520457 2281385 := bstep (se 2 (by rfl) ⟨855519, by rfl⟩ : syracuseStep 2281385 = 1711039) B1711039
theorem B9752723 : Blo 1520457 9752723 := bstep (se 1 (by rfl) ⟨7314542, by rfl⟩ : syracuseStep 9752723 = 14629085) B14629085
theorem B5132537 : Blo 1520457 5132537 := bstep (se 2 (by rfl) ⟨1924701, by rfl⟩ : syracuseStep 5132537 = 3849403) B3849403
theorem B166637897 : Blo 1520457 166637897 := bstep (se 2 (by rfl) ⟨62489211, by rfl⟩ : syracuseStep 166637897 = 124978423) B124978423
theorem B6500843 : Blo 1520457 6500843 := bstep (se 1 (by rfl) ⟨4875632, by rfl⟩ : syracuseStep 6500843 = 9751265) B9751265
theorem B8778311 : Blo 1520457 8778311 := bstep (se 1 (by rfl) ⟨6583733, by rfl⟩ : syracuseStep 8778311 = 13167467) B13167467
theorem B2568847 : Blo 1520457 2568847 := bstep (se 1 (by rfl) ⟨1926635, by rfl⟩ : syracuseStep 2568847 = 3853271) B3853271
theorem B2568935 : Blo 1520457 2568935 := bstep (se 1 (by rfl) ⟨1926701, by rfl⟩ : syracuseStep 2568935 = 3853403) B3853403
theorem B2569063 : Blo 1520457 2569063 := bstep (se 1 (by rfl) ⟨1926797, by rfl⟩ : syracuseStep 2569063 = 3853595) B3853595
theorem B4330523 : Blo 1520457 4330523 := bstep (se 1 (by rfl) ⟨3247892, by rfl⟩ : syracuseStep 4330523 = 6495785) B6495785
theorem B36607099 : Blo 1520457 36607099 := bstep (se 1 (by rfl) ⟨27455324, by rfl⟩ : syracuseStep 36607099 = 54910649) B54910649
theorem B2282633 : Blo 1520457 2282633 := bstep (se 2 (by rfl) ⟨855987, by rfl⟩ : syracuseStep 2282633 = 1711975) B1711975
theorem B2282921 : Blo 1520457 2282921 := bstep (se 2 (by rfl) ⟨856095, by rfl⟩ : syracuseStep 2282921 = 1712191) B1712191
theorem B3421673 : Blo 1520457 3421673 := bstep (se 2 (by rfl) ⟨1283127, by rfl⟩ : syracuseStep 3421673 = 2566255) B2566255
theorem B2282987 : Blo 1520457 2282987 := bstep (se 1 (by rfl) ⟨1712240, by rfl⟩ : syracuseStep 2282987 = 3424481) B3424481
theorem B3249695 : Blo 1520457 3249695 := bstep (se 1 (by rfl) ⟨2437271, by rfl⟩ : syracuseStep 3249695 = 4874543) B4874543
theorem B49346171 : Blo 1520457 49346171 := bstep (se 1 (by rfl) ⟨37009628, by rfl⟩ : syracuseStep 49346171 = 74019257) B74019257
theorem B5134049 : Blo 1520457 5134049 := bstep (se 2 (by rfl) ⟨1925268, by rfl⟩ : syracuseStep 5134049 = 3850537) B3850537
theorem B1521919 : Blo 1520457 1521919 := bstep (se 1 (by rfl) ⟨1141439, by rfl⟩ : syracuseStep 1521919 = 2282879) B2282879
theorem B3422483 : Blo 1520457 3422483 := bstep (se 1 (by rfl) ⟨2566862, by rfl⟩ : syracuseStep 3422483 = 5133725) B5133725
theorem B1522303 : Blo 1520457 1522303 := bstep (se 1 (by rfl) ⟨1141727, by rfl⟩ : syracuseStep 1522303 = 2283455) B2283455
theorem B7699211 : Blo 1520457 7699211 := bstep (se 1 (by rfl) ⟨5774408, by rfl⟩ : syracuseStep 7699211 = 11548817) B11548817
theorem B3849241 : Blo 1520457 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B29244563 : Blo 1520457 29244563 := bstep (se 1 (by rfl) ⟨21933422, by rfl⟩ : syracuseStep 29244563 = 43866845) B43866845
theorem B3423419 : Blo 1520457 3423419 := bstep (se 1 (by rfl) ⟨2567564, by rfl⟩ : syracuseStep 3423419 = 5135129) B5135129
theorem B4111663 : Blo 1520457 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B4628249 : Blo 1520457 4628249 := bstep (se 2 (by rfl) ⟨1735593, by rfl⟩ : syracuseStep 4628249 = 3471187) B3471187
theorem B7700345 : Blo 1520457 7700345 := bstep (se 2 (by rfl) ⟨2887629, by rfl⟩ : syracuseStep 7700345 = 5775259) B5775259
theorem B111091931 : Blo 1520457 111091931 := bstep (se 1 (by rfl) ⟨83318948, by rfl⟩ : syracuseStep 111091931 = 166637897) B166637897
theorem B12992831 : Blo 1520457 12992831 := bstep (se 1 (by rfl) ⟨9744623, by rfl⟩ : syracuseStep 12992831 = 19489247) B19489247
theorem B4333895 : Blo 1520457 4333895 := bstep (se 1 (by rfl) ⟨3250421, by rfl⟩ : syracuseStep 4333895 = 6500843) B6500843
theorem B1712623 : Blo 1520457 1712623 := bstep (se 1 (by rfl) ⟨1284467, by rfl⟩ : syracuseStep 1712623 = 2568935) B2568935
theorem B11551247 : Blo 1520457 11551247 := bstep (se 1 (by rfl) ⟨8663435, by rfl⟩ : syracuseStep 11551247 = 17326871) B17326871
theorem B29246021 : Blo 1520457 29246021 := bstep (se 4 (by rfl) ⟨2741814, by rfl⟩ : syracuseStep 29246021 = 5483629) B5483629
theorem B3425129 : Blo 1520457 3425129 := bstep (se 2 (by rfl) ⟨1284423, by rfl⟩ : syracuseStep 3425129 = 2568847) B2568847
theorem B3425417 : Blo 1520457 3425417 := bstep (se 2 (by rfl) ⟨1284531, by rfl⟩ : syracuseStep 3425417 = 2569063) B2569063
theorem B48809465 : Blo 1520457 48809465 := bstep (se 2 (by rfl) ⟨18303549, by rfl⟩ : syracuseStep 48809465 = 36607099) B36607099
theorem B5482217 : Blo 1520457 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B5138153 : Blo 1520457 5138153 := bstep (se 2 (by rfl) ⟨1926807, by rfl⟩ : syracuseStep 5138153 = 3853615) B3853615
theorem B5852207 : Blo 1520457 5852207 := bstep (se 1 (by rfl) ⟨4389155, by rfl⟩ : syracuseStep 5852207 = 8778311) B8778311
theorem B2887015 : Blo 1520457 2887015 := bstep (se 1 (by rfl) ⟨2165261, by rfl⟩ : syracuseStep 2887015 = 4330523) B4330523
theorem B2281115 : Blo 1520457 2281115 := bstep (se 1 (by rfl) ⟨1710836, by rfl⟩ : syracuseStep 2281115 = 3421673) B3421673
theorem B2166463 : Blo 1520457 2166463 := bstep (se 1 (by rfl) ⟨1624847, by rfl⟩ : syracuseStep 2166463 = 3249695) B3249695
theorem B5132321 : Blo 1520457 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B2281655 : Blo 1520457 2281655 := bstep (se 1 (by rfl) ⟨1711241, by rfl⟩ : syracuseStep 2281655 = 3422483) B3422483
theorem B5132807 : Blo 1520457 5132807 := bstep (se 1 (by rfl) ⟨3849605, by rfl⟩ : syracuseStep 5132807 = 7699211) B7699211
theorem B2282279 : Blo 1520457 2282279 := bstep (se 1 (by rfl) ⟨1711709, by rfl⟩ : syracuseStep 2282279 = 3423419) B3423419
theorem B43856801 : Blo 1520457 43856801 := bstep (se 2 (by rfl) ⟨16446300, by rfl⟩ : syracuseStep 43856801 = 32892601) B32892601
theorem B1520671 : Blo 1520457 1520671 := bstep (se 1 (by rfl) ⟨1140503, by rfl⟩ : syracuseStep 1520671 = 2281007) B2281007
theorem B1520767 : Blo 1520457 1520767 := bstep (se 1 (by rfl) ⟨1140575, by rfl⟩ : syracuseStep 1520767 = 2281151) B2281151
theorem B3085499 : Blo 1520457 3085499 := bstep (se 1 (by rfl) ⟨2314124, by rfl⟩ : syracuseStep 3085499 = 4628249) B4628249
theorem B1520871 : Blo 1520457 1520871 := bstep (se 1 (by rfl) ⟨1140653, by rfl⟩ : syracuseStep 1520871 = 2281307) B2281307
theorem B5133563 : Blo 1520457 5133563 := bstep (se 1 (by rfl) ⟨3850172, by rfl⟩ : syracuseStep 5133563 = 7700345) B7700345
theorem B1520923 : Blo 1520457 1520923 := bstep (se 1 (by rfl) ⟨1140692, by rfl⟩ : syracuseStep 1520923 = 2281385) B2281385
theorem B6501815 : Blo 1520457 6501815 := bstep (se 1 (by rfl) ⟨4876361, by rfl⟩ : syracuseStep 6501815 = 9752723) B9752723
theorem B3421691 : Blo 1520457 3421691 := bstep (se 1 (by rfl) ⟨2566268, by rfl⟩ : syracuseStep 3421691 = 5132537) B5132537
theorem B2742319 : Blo 1520457 2742319 := bstep (se 1 (by rfl) ⟨2056739, by rfl⟩ : syracuseStep 2742319 = 4113479) B4113479
theorem B1521755 : Blo 1520457 1521755 := bstep (se 1 (by rfl) ⟨1141316, by rfl⟩ : syracuseStep 1521755 = 2282633) B2282633
theorem B12343421 : Blo 1520457 12343421 := bstep (se 3 (by rfl) ⟨2314391, by rfl⟩ : syracuseStep 12343421 = 4628783) B4628783
theorem B1521947 : Blo 1520457 1521947 := bstep (se 1 (by rfl) ⟨1141460, by rfl⟩ : syracuseStep 1521947 = 2282921) B2282921
theorem B1521991 : Blo 1520457 1521991 := bstep (se 1 (by rfl) ⟨1141493, by rfl⟩ : syracuseStep 1521991 = 2282987) B2282987
theorem B32897447 : Blo 1520457 32897447 := bstep (se 1 (by rfl) ⟨24673085, by rfl⟩ : syracuseStep 32897447 = 49346171) B49346171
theorem B29252015 : Blo 1520457 29252015 := bstep (se 1 (by rfl) ⟨21939011, by rfl⟩ : syracuseStep 29252015 = 43878023) B43878023
theorem B3422699 : Blo 1520457 3422699 := bstep (se 1 (by rfl) ⟨2567024, by rfl⟩ : syracuseStep 3422699 = 5134049) B5134049
theorem B5135615 : Blo 1520457 5135615 := bstep (se 1 (by rfl) ⟨3851711, by rfl⟩ : syracuseStep 5135615 = 7703423) B7703423
theorem B19496375 : Blo 1520457 19496375 := bstep (se 1 (by rfl) ⟨14622281, by rfl⟩ : syracuseStep 19496375 = 29244563) B29244563
theorem B15605885 : Blo 1520457 15605885 := bstep (se 3 (by rfl) ⟨2926103, by rfl⟩ : syracuseStep 15605885 = 5852207) B5852207
theorem B7700831 : Blo 1520457 7700831 := bstep (se 1 (by rfl) ⟨5775623, by rfl⟩ : syracuseStep 7700831 = 11551247) B11551247
theorem B19497347 : Blo 1520457 19497347 := bstep (se 1 (by rfl) ⟨14623010, by rfl⟩ : syracuseStep 19497347 = 29246021) B29246021
theorem B29237867 : Blo 1520457 29237867 := bstep (se 1 (by rfl) ⟨21928400, by rfl⟩ : syracuseStep 29237867 = 43856801) B43856801
theorem B2056999 : Blo 1520457 2056999 := bstep (se 1 (by rfl) ⟨1542749, by rfl⟩ : syracuseStep 2056999 = 3085499) B3085499
theorem B4334543 : Blo 1520457 4334543 := bstep (se 1 (by rfl) ⟨3250907, by rfl⟩ : syracuseStep 4334543 = 6501815) B6501815
theorem B32539643 : Blo 1520457 32539643 := bstep (se 1 (by rfl) ⟨24404732, by rfl⟩ : syracuseStep 32539643 = 48809465) B48809465
theorem B3654811 : Blo 1520457 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B3425435 : Blo 1520457 3425435 := bstep (se 1 (by rfl) ⟨2569076, by rfl⟩ : syracuseStep 3425435 = 5138153) B5138153
theorem B21931631 : Blo 1520457 21931631 := bstep (se 1 (by rfl) ⟨16448723, by rfl⟩ : syracuseStep 21931631 = 32897447) B32897447
theorem B3656425 : Blo 1520457 3656425 := bstep (se 2 (by rfl) ⟨1371159, by rfl⟩ : syracuseStep 3656425 = 2742319) B2742319
theorem B8661887 : Blo 1520457 8661887 := bstep (se 1 (by rfl) ⟨6496415, by rfl⟩ : syracuseStep 8661887 = 12992831) B12992831
theorem B2281127 : Blo 1520457 2281127 := bstep (se 1 (by rfl) ⟨1710845, by rfl⟩ : syracuseStep 2281127 = 3421691) B3421691
theorem B8228947 : Blo 1520457 8228947 := bstep (se 1 (by rfl) ⟨6171710, by rfl⟩ : syracuseStep 8228947 = 12343421) B12343421
theorem B19501343 : Blo 1520457 19501343 := bstep (se 1 (by rfl) ⟨14626007, by rfl⟩ : syracuseStep 19501343 = 29252015) B29252015
theorem B2281799 : Blo 1520457 2281799 := bstep (se 1 (by rfl) ⟨1711349, by rfl⟩ : syracuseStep 2281799 = 3422699) B3422699
theorem B2888617 : Blo 1520457 2888617 := bstep (se 2 (by rfl) ⟨1083231, by rfl⟩ : syracuseStep 2888617 = 2166463) B2166463
theorem B12997583 : Blo 1520457 12997583 := bstep (se 1 (by rfl) ⟨9748187, by rfl⟩ : syracuseStep 12997583 = 19496375) B19496375
theorem B1520743 : Blo 1520457 1520743 := bstep (se 1 (by rfl) ⟨1140557, by rfl⟩ : syracuseStep 1520743 = 2281115) B2281115
theorem B3421547 : Blo 1520457 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B1521103 : Blo 1520457 1521103 := bstep (se 1 (by rfl) ⟨1140827, by rfl⟩ : syracuseStep 1521103 = 2281655) B2281655
theorem B74061287 : Blo 1520457 74061287 := bstep (se 1 (by rfl) ⟨55545965, by rfl⟩ : syracuseStep 74061287 = 111091931) B111091931
theorem B2889263 : Blo 1520457 2889263 := bstep (se 1 (by rfl) ⟨2166947, by rfl⟩ : syracuseStep 2889263 = 4333895) B4333895
theorem B3421871 : Blo 1520457 3421871 := bstep (se 1 (by rfl) ⟨2566403, by rfl⟩ : syracuseStep 3421871 = 5132807) B5132807
theorem B1521519 : Blo 1520457 1521519 := bstep (se 1 (by rfl) ⟨1141139, by rfl⟩ : syracuseStep 1521519 = 2282279) B2282279
theorem B2283419 : Blo 1520457 2283419 := bstep (se 1 (by rfl) ⟨1712564, by rfl⟩ : syracuseStep 2283419 = 3425129) B3425129
theorem B2283497 : Blo 1520457 2283497 := bstep (se 2 (by rfl) ⟨856311, by rfl⟩ : syracuseStep 2283497 = 1712623) B1712623
theorem B2283611 : Blo 1520457 2283611 := bstep (se 1 (by rfl) ⟨1712708, by rfl⟩ : syracuseStep 2283611 = 3425417) B3425417
theorem B3422375 : Blo 1520457 3422375 := bstep (se 1 (by rfl) ⟨2566781, by rfl⟩ : syracuseStep 3422375 = 5133563) B5133563
theorem B3849353 : Blo 1520457 3849353 := bstep (se 2 (by rfl) ⟨1443507, by rfl⟩ : syracuseStep 3849353 = 2887015) B2887015
theorem B3423743 : Blo 1520457 3423743 := bstep (se 1 (by rfl) ⟨2567807, by rfl⟩ : syracuseStep 3423743 = 5135615) B5135615
theorem B13000895 : Blo 1520457 13000895 := bstep (se 1 (by rfl) ⟨9750671, by rfl⟩ : syracuseStep 13000895 = 19501343) B19501343
theorem B41615693 : Blo 1520457 41615693 := bstep (se 3 (by rfl) ⟨7802942, by rfl⟩ : syracuseStep 41615693 = 15605885) B15605885
theorem B21693095 : Blo 1520457 21693095 := bstep (se 1 (by rfl) ⟨16269821, by rfl⟩ : syracuseStep 21693095 = 32539643) B32539643
theorem B4875233 : Blo 1520457 4875233 := bstep (se 2 (by rfl) ⟨1828212, by rfl⟩ : syracuseStep 4875233 = 3656425) B3656425
theorem B49374191 : Blo 1520457 49374191 := bstep (se 1 (by rfl) ⟨37030643, by rfl⟩ : syracuseStep 49374191 = 74061287) B74061287
theorem B1926175 : Blo 1520457 1926175 := bstep (se 1 (by rfl) ⟨1444631, by rfl⟩ : syracuseStep 1926175 = 2889263) B2889263
theorem B3851489 : Blo 1520457 3851489 := bstep (se 2 (by rfl) ⟨1444308, by rfl⟩ : syracuseStep 3851489 = 2888617) B2888617
theorem B2566235 : Blo 1520457 2566235 := bstep (se 1 (by rfl) ⟨1924676, by rfl⟩ : syracuseStep 2566235 = 3849353) B3849353
theorem B10971929 : Blo 1520457 10971929 := bstep (se 2 (by rfl) ⟨4114473, by rfl⟩ : syracuseStep 10971929 = 8228947) B8228947
theorem B19491911 : Blo 1520457 19491911 := bstep (se 1 (by rfl) ⟨14618933, by rfl⟩ : syracuseStep 19491911 = 29237867) B29237867
theorem B2281031 : Blo 1520457 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B2281247 : Blo 1520457 2281247 := bstep (se 1 (by rfl) ⟨1710935, by rfl⟩ : syracuseStep 2281247 = 3421871) B3421871
theorem B2281583 : Blo 1520457 2281583 := bstep (se 1 (by rfl) ⟨1711187, by rfl⟩ : syracuseStep 2281583 = 3422375) B3422375
theorem B2282495 : Blo 1520457 2282495 := bstep (se 1 (by rfl) ⟨1711871, by rfl⟩ : syracuseStep 2282495 = 3423743) B3423743
theorem B1520751 : Blo 1520457 1520751 := bstep (se 1 (by rfl) ⟨1140563, by rfl⟩ : syracuseStep 1520751 = 2281127) B2281127
theorem B1521199 : Blo 1520457 1521199 := bstep (se 1 (by rfl) ⟨1140899, by rfl⟩ : syracuseStep 1521199 = 2281799) B2281799
theorem B5133887 : Blo 1520457 5133887 := bstep (se 1 (by rfl) ⟨3850415, by rfl⟩ : syracuseStep 5133887 = 7700831) B7700831
theorem B12998231 : Blo 1520457 12998231 := bstep (se 1 (by rfl) ⟨9748673, by rfl⟩ : syracuseStep 12998231 = 19497347) B19497347
theorem B8665055 : Blo 1520457 8665055 := bstep (se 1 (by rfl) ⟨6498791, by rfl⟩ : syracuseStep 8665055 = 12997583) B12997583
theorem B2889695 : Blo 1520457 2889695 := bstep (se 1 (by rfl) ⟨2167271, by rfl⟩ : syracuseStep 2889695 = 4334543) B4334543
theorem B2283623 : Blo 1520457 2283623 := bstep (se 1 (by rfl) ⟨1712717, by rfl⟩ : syracuseStep 2283623 = 3425435) B3425435
theorem B2742665 : Blo 1520457 2742665 := bstep (se 2 (by rfl) ⟨1028499, by rfl⟩ : syracuseStep 2742665 = 2056999) B2056999
theorem B14621087 : Blo 1520457 14621087 := bstep (se 1 (by rfl) ⟨10965815, by rfl⟩ : syracuseStep 14621087 = 21931631) B21931631
theorem B1522279 : Blo 1520457 1522279 := bstep (se 1 (by rfl) ⟨1141709, by rfl⟩ : syracuseStep 1522279 = 2283419) B2283419
theorem B1522331 : Blo 1520457 1522331 := bstep (se 1 (by rfl) ⟨1141748, by rfl⟩ : syracuseStep 1522331 = 2283497) B2283497
theorem B1522407 : Blo 1520457 1522407 := bstep (se 1 (by rfl) ⟨1141805, by rfl⟩ : syracuseStep 1522407 = 2283611) B2283611
theorem B4873081 : Blo 1520457 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B5774591 : Blo 1520457 5774591 := bstep (se 1 (by rfl) ⟨4330943, by rfl⟩ : syracuseStep 5774591 = 8661887) B8661887
theorem B8667263 : Blo 1520457 8667263 := bstep (se 1 (by rfl) ⟨6500447, by rfl⟩ : syracuseStep 8667263 = 13000895) B13000895
theorem B32916127 : Blo 1520457 32916127 := bstep (se 1 (by rfl) ⟨24687095, by rfl⟩ : syracuseStep 32916127 = 49374191) B49374191
theorem B6497441 : Blo 1520457 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B5776703 : Blo 1520457 5776703 := bstep (se 1 (by rfl) ⟨4332527, by rfl⟩ : syracuseStep 5776703 = 8665055) B8665055
theorem B12994607 : Blo 1520457 12994607 := bstep (se 1 (by rfl) ⟨9745955, by rfl⟩ : syracuseStep 12994607 = 19491911) B19491911
theorem B14462063 : Blo 1520457 14462063 := bstep (se 1 (by rfl) ⟨10846547, by rfl⟩ : syracuseStep 14462063 = 21693095) B21693095
theorem B2567659 : Blo 1520457 2567659 := bstep (se 1 (by rfl) ⟨1925744, by rfl⟩ : syracuseStep 2567659 = 3851489) B3851489
theorem B2568233 : Blo 1520457 2568233 := bstep (se 2 (by rfl) ⟨963087, by rfl⟩ : syracuseStep 2568233 = 1926175) B1926175
theorem B1520687 : Blo 1520457 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B1520831 : Blo 1520457 1520831 := bstep (se 1 (by rfl) ⟨1140623, by rfl⟩ : syracuseStep 1520831 = 2281247) B2281247
theorem B7705853 : Blo 1520457 7705853 := bstep (se 3 (by rfl) ⟨1444847, by rfl⟩ : syracuseStep 7705853 = 2889695) B2889695
theorem B1521055 : Blo 1520457 1521055 := bstep (se 1 (by rfl) ⟨1140791, by rfl⟩ : syracuseStep 1521055 = 2281583) B2281583
theorem B27743795 : Blo 1520457 27743795 := bstep (se 1 (by rfl) ⟨20807846, by rfl⟩ : syracuseStep 27743795 = 41615693) B41615693
theorem B1521663 : Blo 1520457 1521663 := bstep (se 1 (by rfl) ⟨1141247, by rfl⟩ : syracuseStep 1521663 = 2282495) B2282495
theorem B7313773 : Blo 1520457 7313773 := bstep (se 3 (by rfl) ⟨1371332, by rfl⟩ : syracuseStep 7313773 = 2742665) B2742665
theorem B3422591 : Blo 1520457 3422591 := bstep (se 1 (by rfl) ⟨2566943, by rfl⟩ : syracuseStep 3422591 = 5133887) B5133887
theorem B8665487 : Blo 1520457 8665487 := bstep (se 1 (by rfl) ⟨6499115, by rfl⟩ : syracuseStep 8665487 = 12998231) B12998231
theorem B1710823 : Blo 1520457 1710823 := bstep (se 1 (by rfl) ⟨1283117, by rfl⟩ : syracuseStep 1710823 = 2566235) B2566235
theorem B1522415 : Blo 1520457 1522415 := bstep (se 1 (by rfl) ⟨1141811, by rfl⟩ : syracuseStep 1522415 = 2283623) B2283623
theorem B9747391 : Blo 1520457 9747391 := bstep (se 1 (by rfl) ⟨7310543, by rfl⟩ : syracuseStep 9747391 = 14621087) B14621087
theorem B7314619 : Blo 1520457 7314619 := bstep (se 1 (by rfl) ⟨5485964, by rfl⟩ : syracuseStep 7314619 = 10971929) B10971929
theorem B3849727 : Blo 1520457 3849727 := bstep (se 1 (by rfl) ⟨2887295, by rfl⟩ : syracuseStep 3849727 = 5774591) B5774591
theorem B13000621 : Blo 1520457 13000621 := bstep (se 3 (by rfl) ⟨2437616, by rfl⟩ : syracuseStep 13000621 = 4875233) B4875233
theorem B1712155 : Blo 1520457 1712155 := bstep (se 1 (by rfl) ⟨1284116, by rfl⟩ : syracuseStep 1712155 = 2568233) B2568233
theorem B5137235 : Blo 1520457 5137235 := bstep (se 1 (by rfl) ⟨3852926, by rfl⟩ : syracuseStep 5137235 = 7705853) B7705853
theorem B3851135 : Blo 1520457 3851135 := bstep (se 1 (by rfl) ⟨2888351, by rfl⟩ : syracuseStep 3851135 = 5776703) B5776703
theorem B5776991 : Blo 1520457 5776991 := bstep (se 1 (by rfl) ⟨4332743, by rfl⟩ : syracuseStep 5776991 = 8665487) B8665487
theorem B5778175 : Blo 1520457 5778175 := bstep (se 1 (by rfl) ⟨4333631, by rfl⟩ : syracuseStep 5778175 = 8667263) B8667263
theorem B9751697 : Blo 1520457 9751697 := bstep (se 2 (by rfl) ⟨3656886, by rfl⟩ : syracuseStep 9751697 = 7313773) B7313773
theorem B43888169 : Blo 1520457 43888169 := bstep (se 2 (by rfl) ⟨16458063, by rfl⟩ : syracuseStep 43888169 = 32916127) B32916127
theorem B2281097 : Blo 1520457 2281097 := bstep (se 2 (by rfl) ⟨855411, by rfl⟩ : syracuseStep 2281097 = 1710823) B1710823
theorem B12996521 : Blo 1520457 12996521 := bstep (se 2 (by rfl) ⟨4873695, by rfl⟩ : syracuseStep 12996521 = 9747391) B9747391
theorem B8663071 : Blo 1520457 8663071 := bstep (se 1 (by rfl) ⟨6497303, by rfl⟩ : syracuseStep 8663071 = 12994607) B12994607
theorem B9752825 : Blo 1520457 9752825 := bstep (se 2 (by rfl) ⟨3657309, by rfl⟩ : syracuseStep 9752825 = 7314619) B7314619
theorem B2281727 : Blo 1520457 2281727 := bstep (se 1 (by rfl) ⟨1711295, by rfl⟩ : syracuseStep 2281727 = 3422591) B3422591
theorem B5132969 : Blo 1520457 5132969 := bstep (se 2 (by rfl) ⟨1924863, by rfl⟩ : syracuseStep 5132969 = 3849727) B3849727
theorem B4331627 : Blo 1520457 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B18495863 : Blo 1520457 18495863 := bstep (se 1 (by rfl) ⟨13871897, by rfl⟩ : syracuseStep 18495863 = 27743795) B27743795
theorem B3423545 : Blo 1520457 3423545 := bstep (se 2 (by rfl) ⟨1283829, by rfl⟩ : syracuseStep 3423545 = 2567659) B2567659
theorem B9641375 : Blo 1520457 9641375 := bstep (se 1 (by rfl) ⟨7231031, by rfl⟩ : syracuseStep 9641375 = 14462063) B14462063
theorem B17334161 : Blo 1520457 17334161 := bstep (se 2 (by rfl) ⟨6500310, by rfl⟩ : syracuseStep 17334161 = 13000621) B13000621
theorem B11550761 : Blo 1520457 11550761 := bstep (se 2 (by rfl) ⟨4331535, by rfl⟩ : syracuseStep 11550761 = 8663071) B8663071
theorem B3424823 : Blo 1520457 3424823 := bstep (se 1 (by rfl) ⟨2568617, by rfl⟩ : syracuseStep 3424823 = 5137235) B5137235
theorem B3851327 : Blo 1520457 3851327 := bstep (se 1 (by rfl) ⟨2888495, by rfl⟩ : syracuseStep 3851327 = 5776991) B5776991
theorem B12330575 : Blo 1520457 12330575 := bstep (se 1 (by rfl) ⟨9247931, by rfl⟩ : syracuseStep 12330575 = 18495863) B18495863
theorem B2567423 : Blo 1520457 2567423 := bstep (se 1 (by rfl) ⟨1925567, by rfl⟩ : syracuseStep 2567423 = 3851135) B3851135
theorem B7704233 : Blo 1520457 7704233 := bstep (se 2 (by rfl) ⟨2889087, by rfl⟩ : syracuseStep 7704233 = 5778175) B5778175
theorem B2887751 : Blo 1520457 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B6501131 : Blo 1520457 6501131 := bstep (se 1 (by rfl) ⟨4875848, by rfl⟩ : syracuseStep 6501131 = 9751697) B9751697
theorem B2282363 : Blo 1520457 2282363 := bstep (se 1 (by rfl) ⟨1711772, by rfl⟩ : syracuseStep 2282363 = 3423545) B3423545
theorem B6427583 : Blo 1520457 6427583 := bstep (se 1 (by rfl) ⟨4820687, by rfl⟩ : syracuseStep 6427583 = 9641375) B9641375
theorem B29258779 : Blo 1520457 29258779 := bstep (se 1 (by rfl) ⟨21944084, by rfl⟩ : syracuseStep 29258779 = 43888169) B43888169
theorem B1520731 : Blo 1520457 1520731 := bstep (se 1 (by rfl) ⟨1140548, by rfl⟩ : syracuseStep 1520731 = 2281097) B2281097
theorem B11556107 : Blo 1520457 11556107 := bstep (se 1 (by rfl) ⟨8667080, by rfl⟩ : syracuseStep 11556107 = 17334161) B17334161
theorem B8664347 : Blo 1520457 8664347 := bstep (se 1 (by rfl) ⟨6498260, by rfl⟩ : syracuseStep 8664347 = 12996521) B12996521
theorem B2282873 : Blo 1520457 2282873 := bstep (se 2 (by rfl) ⟨856077, by rfl⟩ : syracuseStep 2282873 = 1712155) B1712155
theorem B1521151 : Blo 1520457 1521151 := bstep (se 1 (by rfl) ⟨1140863, by rfl⟩ : syracuseStep 1521151 = 2281727) B2281727
theorem B6501883 : Blo 1520457 6501883 := bstep (se 1 (by rfl) ⟨4876412, by rfl⟩ : syracuseStep 6501883 = 9752825) B9752825
theorem B3421979 : Blo 1520457 3421979 := bstep (se 1 (by rfl) ⟨2566484, by rfl⟩ : syracuseStep 3421979 = 5132969) B5132969
theorem B7700507 : Blo 1520457 7700507 := bstep (se 1 (by rfl) ⟨5775380, by rfl⟩ : syracuseStep 7700507 = 11550761) B11550761
theorem B7700669 : Blo 1520457 7700669 := bstep (se 3 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 7700669 = 2887751) B2887751
theorem B4334087 : Blo 1520457 4334087 := bstep (se 1 (by rfl) ⟨3250565, by rfl⟩ : syracuseStep 4334087 = 6501131) B6501131
theorem B4285055 : Blo 1520457 4285055 := bstep (se 1 (by rfl) ⟨3213791, by rfl⟩ : syracuseStep 4285055 = 6427583) B6427583
theorem B5776231 : Blo 1520457 5776231 := bstep (se 1 (by rfl) ⟨4332173, by rfl⟩ : syracuseStep 5776231 = 8664347) B8664347
theorem B39011705 : Blo 1520457 39011705 := bstep (se 2 (by rfl) ⟨14629389, by rfl⟩ : syracuseStep 39011705 = 29258779) B29258779
theorem B8669177 : Blo 1520457 8669177 := bstep (se 2 (by rfl) ⟨3250941, by rfl⟩ : syracuseStep 8669177 = 6501883) B6501883
theorem B2567551 : Blo 1520457 2567551 := bstep (se 1 (by rfl) ⟨1925663, by rfl⟩ : syracuseStep 2567551 = 3851327) B3851327
theorem B7704071 : Blo 1520457 7704071 := bstep (se 1 (by rfl) ⟨5778053, by rfl⟩ : syracuseStep 7704071 = 11556107) B11556107
theorem B8220383 : Blo 1520457 8220383 := bstep (se 1 (by rfl) ⟨6165287, by rfl⟩ : syracuseStep 8220383 = 12330575) B12330575
theorem B2281319 : Blo 1520457 2281319 := bstep (se 1 (by rfl) ⟨1710989, by rfl⟩ : syracuseStep 2281319 = 3421979) B3421979
theorem B2283215 : Blo 1520457 2283215 := bstep (se 1 (by rfl) ⟨1712411, by rfl⟩ : syracuseStep 2283215 = 3424823) B3424823
theorem B1521575 : Blo 1520457 1521575 := bstep (se 1 (by rfl) ⟨1141181, by rfl⟩ : syracuseStep 1521575 = 2282363) B2282363
theorem B1521915 : Blo 1520457 1521915 := bstep (se 1 (by rfl) ⟨1141436, by rfl⟩ : syracuseStep 1521915 = 2282873) B2282873
theorem B1711615 : Blo 1520457 1711615 := bstep (se 1 (by rfl) ⟨1283711, by rfl⟩ : syracuseStep 1711615 = 2567423) B2567423
theorem B5136155 : Blo 1520457 5136155 := bstep (se 1 (by rfl) ⟨3852116, by rfl⟩ : syracuseStep 5136155 = 7704233) B7704233
theorem B7701641 : Blo 1520457 7701641 := bstep (se 2 (by rfl) ⟨2888115, by rfl⟩ : syracuseStep 7701641 = 5776231) B5776231
theorem B5779451 : Blo 1520457 5779451 := bstep (se 1 (by rfl) ⟨4334588, by rfl⟩ : syracuseStep 5779451 = 8669177) B8669177
theorem B2282153 : Blo 1520457 2282153 := bstep (se 2 (by rfl) ⟨855807, by rfl⟩ : syracuseStep 2282153 = 1711615) B1711615
theorem B1520879 : Blo 1520457 1520879 := bstep (se 1 (by rfl) ⟨1140659, by rfl⟩ : syracuseStep 1520879 = 2281319) B2281319
theorem B5133671 : Blo 1520457 5133671 := bstep (se 1 (by rfl) ⟨3850253, by rfl⟩ : syracuseStep 5133671 = 7700507) B7700507
theorem B5133779 : Blo 1520457 5133779 := bstep (se 1 (by rfl) ⟨3850334, by rfl⟩ : syracuseStep 5133779 = 7700669) B7700669
theorem B2856703 : Blo 1520457 2856703 := bstep (se 1 (by rfl) ⟨2142527, by rfl⟩ : syracuseStep 2856703 = 4285055) B4285055
theorem B26007803 : Blo 1520457 26007803 := bstep (se 1 (by rfl) ⟨19505852, by rfl⟩ : syracuseStep 26007803 = 39011705) B39011705
theorem B1522143 : Blo 1520457 1522143 := bstep (se 1 (by rfl) ⟨1141607, by rfl⟩ : syracuseStep 1522143 = 2283215) B2283215
theorem B11557565 : Blo 1520457 11557565 := bstep (se 3 (by rfl) ⟨2167043, by rfl⟩ : syracuseStep 11557565 = 4334087) B4334087
theorem B3423401 : Blo 1520457 3423401 := bstep (se 2 (by rfl) ⟨1283775, by rfl⟩ : syracuseStep 3423401 = 2567551) B2567551
theorem B5136047 : Blo 1520457 5136047 := bstep (se 1 (by rfl) ⟨3852035, by rfl⟩ : syracuseStep 5136047 = 7704071) B7704071
theorem B5480255 : Blo 1520457 5480255 := bstep (se 1 (by rfl) ⟨4110191, by rfl⟩ : syracuseStep 5480255 = 8220383) B8220383
theorem B3424103 : Blo 1520457 3424103 := bstep (se 1 (by rfl) ⟨2568077, by rfl⟩ : syracuseStep 3424103 = 5136155) B5136155
theorem B3852967 : Blo 1520457 3852967 := bstep (se 1 (by rfl) ⟨2889725, by rfl⟩ : syracuseStep 3852967 = 5779451) B5779451
theorem B17338535 : Blo 1520457 17338535 := bstep (se 1 (by rfl) ⟨13003901, by rfl⟩ : syracuseStep 17338535 = 26007803) B26007803
theorem B7705043 : Blo 1520457 7705043 := bstep (se 1 (by rfl) ⟨5778782, by rfl⟩ : syracuseStep 7705043 = 11557565) B11557565
theorem B2282267 : Blo 1520457 2282267 := bstep (se 1 (by rfl) ⟨1711700, by rfl⟩ : syracuseStep 2282267 = 3423401) B3423401
theorem B2282735 : Blo 1520457 2282735 := bstep (se 1 (by rfl) ⟨1712051, by rfl⟩ : syracuseStep 2282735 = 3424103) B3424103
theorem B1521435 : Blo 1520457 1521435 := bstep (se 1 (by rfl) ⟨1141076, by rfl⟩ : syracuseStep 1521435 = 2282153) B2282153
theorem B5134427 : Blo 1520457 5134427 := bstep (se 1 (by rfl) ⟨3850820, by rfl⟩ : syracuseStep 5134427 = 7701641) B7701641
theorem B3422447 : Blo 1520457 3422447 := bstep (se 1 (by rfl) ⟨2566835, by rfl⟩ : syracuseStep 3422447 = 5133671) B5133671
theorem B3422519 : Blo 1520457 3422519 := bstep (se 1 (by rfl) ⟨2566889, by rfl⟩ : syracuseStep 3422519 = 5133779) B5133779
theorem B14614013 : Blo 1520457 14614013 := bstep (se 3 (by rfl) ⟨2740127, by rfl⟩ : syracuseStep 14614013 = 5480255) B5480255
theorem B3808937 : Blo 1520457 3808937 := bstep (se 2 (by rfl) ⟨1428351, by rfl⟩ : syracuseStep 3808937 = 2856703) B2856703
theorem B3424031 : Blo 1520457 3424031 := bstep (se 1 (by rfl) ⟨2568023, by rfl⟩ : syracuseStep 3424031 = 5136047) B5136047
theorem B11559023 : Blo 1520457 11559023 := bstep (se 1 (by rfl) ⟨8669267, by rfl⟩ : syracuseStep 11559023 = 17338535) B17338535
theorem B5136695 : Blo 1520457 5136695 := bstep (se 1 (by rfl) ⟨3852521, by rfl⟩ : syracuseStep 5136695 = 7705043) B7705043
theorem B5137289 : Blo 1520457 5137289 := bstep (se 2 (by rfl) ⟨1926483, by rfl⟩ : syracuseStep 5137289 = 3852967) B3852967
theorem B9742675 : Blo 1520457 9742675 := bstep (se 1 (by rfl) ⟨7307006, by rfl⟩ : syracuseStep 9742675 = 14614013) B14614013
theorem B2281631 : Blo 1520457 2281631 := bstep (se 1 (by rfl) ⟨1711223, by rfl⟩ : syracuseStep 2281631 = 3422447) B3422447
theorem B2281679 : Blo 1520457 2281679 := bstep (se 1 (by rfl) ⟨1711259, by rfl⟩ : syracuseStep 2281679 = 3422519) B3422519
theorem B2282687 : Blo 1520457 2282687 := bstep (se 1 (by rfl) ⟨1712015, by rfl⟩ : syracuseStep 2282687 = 3424031) B3424031
theorem B1521511 : Blo 1520457 1521511 := bstep (se 1 (by rfl) ⟨1141133, by rfl⟩ : syracuseStep 1521511 = 2282267) B2282267
theorem B1521823 : Blo 1520457 1521823 := bstep (se 1 (by rfl) ⟨1141367, by rfl⟩ : syracuseStep 1521823 = 2282735) B2282735
theorem B3422951 : Blo 1520457 3422951 := bstep (se 1 (by rfl) ⟨2567213, by rfl⟩ : syracuseStep 3422951 = 5134427) B5134427
theorem B2539291 : Blo 1520457 2539291 := bstep (se 1 (by rfl) ⟨1904468, by rfl⟩ : syracuseStep 2539291 = 3808937) B3808937
theorem B3424463 : Blo 1520457 3424463 := bstep (se 1 (by rfl) ⟨2568347, by rfl⟩ : syracuseStep 3424463 = 5136695) B5136695
theorem B3424859 : Blo 1520457 3424859 := bstep (se 1 (by rfl) ⟨2568644, by rfl⟩ : syracuseStep 3424859 = 5137289) B5137289
theorem B3385721 : Blo 1520457 3385721 := bstep (se 2 (by rfl) ⟨1269645, by rfl⟩ : syracuseStep 3385721 = 2539291) B2539291
theorem B2281967 : Blo 1520457 2281967 := bstep (se 1 (by rfl) ⟨1711475, by rfl⟩ : syracuseStep 2281967 = 3422951) B3422951
theorem B7706015 : Blo 1520457 7706015 := bstep (se 1 (by rfl) ⟨5779511, by rfl⟩ : syracuseStep 7706015 = 11559023) B11559023
theorem B1521087 : Blo 1520457 1521087 := bstep (se 1 (by rfl) ⟨1140815, by rfl⟩ : syracuseStep 1521087 = 2281631) B2281631
theorem B1521119 : Blo 1520457 1521119 := bstep (se 1 (by rfl) ⟨1140839, by rfl⟩ : syracuseStep 1521119 = 2281679) B2281679
theorem B12990233 : Blo 1520457 12990233 := bstep (se 2 (by rfl) ⟨4871337, by rfl⟩ : syracuseStep 12990233 = 9742675) B9742675
theorem B1521791 : Blo 1520457 1521791 := bstep (se 1 (by rfl) ⟨1141343, by rfl⟩ : syracuseStep 1521791 = 2282687) B2282687
theorem B5137343 : Blo 1520457 5137343 := bstep (se 1 (by rfl) ⟨3853007, by rfl⟩ : syracuseStep 5137343 = 7706015) B7706015
theorem B8660155 : Blo 1520457 8660155 := bstep (se 1 (by rfl) ⟨6495116, by rfl⟩ : syracuseStep 8660155 = 12990233) B12990233
theorem B2257147 : Blo 1520457 2257147 := bstep (se 1 (by rfl) ⟨1692860, by rfl⟩ : syracuseStep 2257147 = 3385721) B3385721
theorem B2282975 : Blo 1520457 2282975 := bstep (se 1 (by rfl) ⟨1712231, by rfl⟩ : syracuseStep 2282975 = 3424463) B3424463
theorem B1521311 : Blo 1520457 1521311 := bstep (se 1 (by rfl) ⟨1140983, by rfl⟩ : syracuseStep 1521311 = 2281967) B2281967
theorem B2283239 : Blo 1520457 2283239 := bstep (se 1 (by rfl) ⟨1712429, by rfl⟩ : syracuseStep 2283239 = 3424859) B3424859
theorem B3424895 : Blo 1520457 3424895 := bstep (se 1 (by rfl) ⟨2568671, by rfl⟩ : syracuseStep 3424895 = 5137343) B5137343
theorem B3009529 : Blo 1520457 3009529 := bstep (se 2 (by rfl) ⟨1128573, by rfl⟩ : syracuseStep 3009529 = 2257147) B2257147
theorem B11546873 : Blo 1520457 11546873 := bstep (se 2 (by rfl) ⟨4330077, by rfl⟩ : syracuseStep 11546873 = 8660155) B8660155
theorem B1521983 : Blo 1520457 1521983 := bstep (se 1 (by rfl) ⟨1141487, by rfl⟩ : syracuseStep 1521983 = 2282975) B2282975
theorem B1522159 : Blo 1520457 1522159 := bstep (se 1 (by rfl) ⟨1141619, by rfl⟩ : syracuseStep 1522159 = 2283239) B2283239
theorem B7697915 : Blo 1520457 7697915 := bstep (se 1 (by rfl) ⟨5773436, by rfl⟩ : syracuseStep 7697915 = 11546873) B11546873
theorem B2283263 : Blo 1520457 2283263 := bstep (se 1 (by rfl) ⟨1712447, by rfl⟩ : syracuseStep 2283263 = 3424895) B3424895
theorem B4012705 : Blo 1520457 4012705 := bstep (se 2 (by rfl) ⟨1504764, by rfl⟩ : syracuseStep 4012705 = 3009529) B3009529
theorem B5350273 : Blo 1520457 5350273 := bstep (se 2 (by rfl) ⟨2006352, by rfl⟩ : syracuseStep 5350273 = 4012705) B4012705
theorem B5131943 : Blo 1520457 5131943 := bstep (se 1 (by rfl) ⟨3848957, by rfl⟩ : syracuseStep 5131943 = 7697915) B7697915
theorem B1522175 : Blo 1520457 1522175 := bstep (se 1 (by rfl) ⟨1141631, by rfl⟩ : syracuseStep 1522175 = 2283263) B2283263
theorem B28534789 : Blo 1520457 28534789 := bstep (se 4 (by rfl) ⟨2675136, by rfl⟩ : syracuseStep 28534789 = 5350273) B5350273
theorem B3421295 : Blo 1520457 3421295 := bstep (se 1 (by rfl) ⟨2565971, by rfl⟩ : syracuseStep 3421295 = 5131943) B5131943
theorem B38046385 : Blo 1520457 38046385 := bstep (se 2 (by rfl) ⟨14267394, by rfl⟩ : syracuseStep 38046385 = 28534789) B28534789
theorem B2280863 : Blo 1520457 2280863 := bstep (se 1 (by rfl) ⟨1710647, by rfl⟩ : syracuseStep 2280863 = 3421295) B3421295
theorem B50728513 : Blo 1520457 50728513 := bstep (se 2 (by rfl) ⟨19023192, by rfl⟩ : syracuseStep 50728513 = 38046385) B38046385
theorem B1520575 : Blo 1520457 1520575 := bstep (se 1 (by rfl) ⟨1140431, by rfl⟩ : syracuseStep 1520575 = 2280863) B2280863
theorem B67638017 : Blo 1520457 67638017 := bstep (se 2 (by rfl) ⟨25364256, by rfl⟩ : syracuseStep 67638017 = 50728513) B50728513
theorem B45092011 : Blo 1520457 45092011 := bstep (se 1 (by rfl) ⟨33819008, by rfl⟩ : syracuseStep 45092011 = 67638017) B67638017
theorem B60122681 : Blo 1520457 60122681 := bstep (se 2 (by rfl) ⟨22546005, by rfl⟩ : syracuseStep 60122681 = 45092011) B45092011
theorem B40081787 : Blo 1520457 40081787 := bstep (se 1 (by rfl) ⟨30061340, by rfl⟩ : syracuseStep 40081787 = 60122681) B60122681
theorem B26721191 : Blo 1520457 26721191 := bstep (se 1 (by rfl) ⟨20040893, by rfl⟩ : syracuseStep 26721191 = 40081787) B40081787
theorem B17814127 : Blo 1520457 17814127 := bstep (se 1 (by rfl) ⟨13360595, by rfl⟩ : syracuseStep 17814127 = 26721191) B26721191
theorem B23752169 : Blo 1520457 23752169 := bstep (se 2 (by rfl) ⟨8907063, by rfl⟩ : syracuseStep 23752169 = 17814127) B17814127
theorem B15834779 : Blo 1520457 15834779 := bstep (se 1 (by rfl) ⟨11876084, by rfl⟩ : syracuseStep 15834779 = 23752169) B23752169
theorem B10556519 : Blo 1520457 10556519 := bstep (se 1 (by rfl) ⟨7917389, by rfl⟩ : syracuseStep 10556519 = 15834779) B15834779
theorem B112602869 : Blo 1520457 112602869 := bstep (se 5 (by rfl) ⟨5278259, by rfl⟩ : syracuseStep 112602869 = 10556519) B10556519
theorem B75068579 : Blo 1520457 75068579 := bstep (se 1 (by rfl) ⟨56301434, by rfl⟩ : syracuseStep 75068579 = 112602869) B112602869
theorem B200182877 : Blo 1520457 200182877 := bstep (se 3 (by rfl) ⟨37534289, by rfl⟩ : syracuseStep 200182877 = 75068579) B75068579
theorem B133455251 : Blo 1520457 133455251 := bstep (se 1 (by rfl) ⟨100091438, by rfl⟩ : syracuseStep 133455251 = 200182877) B200182877
theorem B88970167 : Blo 1520457 88970167 := bstep (se 1 (by rfl) ⟨66727625, by rfl⟩ : syracuseStep 88970167 = 133455251) B133455251
theorem B118626889 : Blo 1520457 118626889 := bstep (se 2 (by rfl) ⟨44485083, by rfl⟩ : syracuseStep 118626889 = 88970167) B88970167
theorem B158169185 : Blo 1520457 158169185 := bstep (se 2 (by rfl) ⟨59313444, by rfl⟩ : syracuseStep 158169185 = 118626889) B118626889
theorem B105446123 : Blo 1520457 105446123 := bstep (se 1 (by rfl) ⟨79084592, by rfl⟩ : syracuseStep 105446123 = 158169185) B158169185
theorem B70297415 : Blo 1520457 70297415 := bstep (se 1 (by rfl) ⟨52723061, by rfl⟩ : syracuseStep 70297415 = 105446123) B105446123
theorem B46864943 : Blo 1520457 46864943 := bstep (se 1 (by rfl) ⟨35148707, by rfl⟩ : syracuseStep 46864943 = 70297415) B70297415
theorem B31243295 : Blo 1520457 31243295 := bstep (se 1 (by rfl) ⟨23432471, by rfl⟩ : syracuseStep 31243295 = 46864943) B46864943
theorem B20828863 : Blo 1520457 20828863 := bstep (se 1 (by rfl) ⟨15621647, by rfl⟩ : syracuseStep 20828863 = 31243295) B31243295
theorem B27771817 : Blo 1520457 27771817 := bstep (se 2 (by rfl) ⟨10414431, by rfl⟩ : syracuseStep 27771817 = 20828863) B20828863
theorem B37029089 : Blo 1520457 37029089 := bstep (se 2 (by rfl) ⟨13885908, by rfl⟩ : syracuseStep 37029089 = 27771817) B27771817
theorem B24686059 : Blo 1520457 24686059 := bstep (se 1 (by rfl) ⟨18514544, by rfl⟩ : syracuseStep 24686059 = 37029089) B37029089
theorem B32914745 : Blo 1520457 32914745 := bstep (se 2 (by rfl) ⟨12343029, by rfl⟩ : syracuseStep 32914745 = 24686059) B24686059
theorem B21943163 : Blo 1520457 21943163 := bstep (se 1 (by rfl) ⟨16457372, by rfl⟩ : syracuseStep 21943163 = 32914745) B32914745
theorem B14628775 : Blo 1520457 14628775 := bstep (se 1 (by rfl) ⟨10971581, by rfl⟩ : syracuseStep 14628775 = 21943163) B21943163
theorem B19505033 : Blo 1520457 19505033 := bstep (se 2 (by rfl) ⟨7314387, by rfl⟩ : syracuseStep 19505033 = 14628775) B14628775
theorem B13003355 : Blo 1520457 13003355 := bstep (se 1 (by rfl) ⟨9752516, by rfl⟩ : syracuseStep 13003355 = 19505033) B19505033
theorem B8668903 : Blo 1520457 8668903 := bstep (se 1 (by rfl) ⟨6501677, by rfl⟩ : syracuseStep 8668903 = 13003355) B13003355
theorem B11558537 : Blo 1520457 11558537 := bstep (se 2 (by rfl) ⟨4334451, by rfl⟩ : syracuseStep 11558537 = 8668903) B8668903
theorem B7705691 : Blo 1520457 7705691 := bstep (se 1 (by rfl) ⟨5779268, by rfl⟩ : syracuseStep 7705691 = 11558537) B11558537
theorem B5137127 : Blo 1520457 5137127 := bstep (se 1 (by rfl) ⟨3852845, by rfl⟩ : syracuseStep 5137127 = 7705691) B7705691
theorem B3424751 : Blo 1520457 3424751 := bstep (se 1 (by rfl) ⟨2568563, by rfl⟩ : syracuseStep 3424751 = 5137127) B5137127
theorem B2283167 : Blo 1520457 2283167 := bstep (se 1 (by rfl) ⟨1712375, by rfl⟩ : syracuseStep 2283167 = 3424751) B3424751
theorem B1522111 : Blo 1520457 1522111 := bstep (se 1 (by rfl) ⟨1141583, by rfl⟩ : syracuseStep 1522111 = 2283167) B2283167

theorem C0 (j : ℕ) (h1 : 380114 ≤ j) (h2 : j ≤ 380613) : Blo 1520457 (4 * j + 3) := by
  interval_cases j
  · exact B1520459
  · exact B1520463
  · exact B1520467
  · exact B1520471
  · exact B1520475
  · exact B1520479
  · exact B1520483
  · exact B1520487
  · exact B1520491
  · exact B1520495
  · exact B1520499
  · exact B1520503
  · exact B1520507
  · exact B1520511
  · exact B1520515
  · exact B1520519
  · exact B1520523
  · exact B1520527
  · exact B1520531
  · exact B1520535
  · exact B1520539
  · exact B1520543
  · exact B1520547
  · exact B1520551
  · exact B1520555
  · exact B1520559
  · exact B1520563
  · exact B1520567
  · exact B1520571
  · exact B1520575
  · exact B1520579
  · exact B1520583
  · exact B1520587
  · exact B1520591
  · exact B1520595
  · exact B1520599
  · exact B1520603
  · exact B1520607
  · exact B1520611
  · exact B1520615
  · exact B1520619
  · exact B1520623
  · exact B1520627
  · exact B1520631
  · exact B1520635
  · exact B1520639
  · exact B1520643
  · exact B1520647
  · exact B1520651
  · exact B1520655
  · exact B1520659
  · exact B1520663
  · exact B1520667
  · exact B1520671
  · exact B1520675
  · exact B1520679
  · exact B1520683
  · exact B1520687
  · exact B1520691
  · exact B1520695
  · exact B1520699
  · exact B1520703
  · exact B1520707
  · exact B1520711
  · exact B1520715
  · exact B1520719
  · exact B1520723
  · exact B1520727
  · exact B1520731
  · exact B1520735
  · exact B1520739
  · exact B1520743
  · exact B1520747
  · exact B1520751
  · exact B1520755
  · exact B1520759
  · exact B1520763
  · exact B1520767
  · exact B1520771
  · exact B1520775
  · exact B1520779
  · exact B1520783
  · exact B1520787
  · exact B1520791
  · exact B1520795
  · exact B1520799
  · exact B1520803
  · exact B1520807
  · exact B1520811
  · exact B1520815
  · exact B1520819
  · exact B1520823
  · exact B1520827
  · exact B1520831
  · exact B1520835
  · exact B1520839
  · exact B1520843
  · exact B1520847
  · exact B1520851
  · exact B1520855
  · exact B1520859
  · exact B1520863
  · exact B1520867
  · exact B1520871
  · exact B1520875
  · exact B1520879
  · exact B1520883
  · exact B1520887
  · exact B1520891
  · exact B1520895
  · exact B1520899
  · exact B1520903
  · exact B1520907
  · exact B1520911
  · exact B1520915
  · exact B1520919
  · exact B1520923
  · exact B1520927
  · exact B1520931
  · exact B1520935
  · exact B1520939
  · exact B1520943
  · exact B1520947
  · exact B1520951
  · exact B1520955
  · exact B1520959
  · exact B1520963
  · exact B1520967
  · exact B1520971
  · exact B1520975
  · exact B1520979
  · exact B1520983
  · exact B1520987
  · exact B1520991
  · exact B1520995
  · exact B1520999
  · exact B1521003
  · exact B1521007
  · exact B1521011
  · exact B1521015
  · exact B1521019
  · exact B1521023
  · exact B1521027
  · exact B1521031
  · exact B1521035
  · exact B1521039
  · exact B1521043
  · exact B1521047
  · exact B1521051
  · exact B1521055
  · exact B1521059
  · exact B1521063
  · exact B1521067
  · exact B1521071
  · exact B1521075
  · exact B1521079
  · exact B1521083
  · exact B1521087
  · exact B1521091
  · exact B1521095
  · exact B1521099
  · exact B1521103
  · exact B1521107
  · exact B1521111
  · exact B1521115
  · exact B1521119
  · exact B1521123
  · exact B1521127
  · exact B1521131
  · exact B1521135
  · exact B1521139
  · exact B1521143
  · exact B1521147
  · exact B1521151
  · exact B1521155
  · exact B1521159
  · exact B1521163
  · exact B1521167
  · exact B1521171
  · exact B1521175
  · exact B1521179
  · exact B1521183
  · exact B1521187
  · exact B1521191
  · exact B1521195
  · exact B1521199
  · exact B1521203
  · exact B1521207
  · exact B1521211
  · exact B1521215
  · exact B1521219
  · exact B1521223
  · exact B1521227
  · exact B1521231
  · exact B1521235
  · exact B1521239
  · exact B1521243
  · exact B1521247
  · exact B1521251
  · exact B1521255
  · exact B1521259
  · exact B1521263
  · exact B1521267
  · exact B1521271
  · exact B1521275
  · exact B1521279
  · exact B1521283
  · exact B1521287
  · exact B1521291
  · exact B1521295
  · exact B1521299
  · exact B1521303
  · exact B1521307
  · exact B1521311
  · exact B1521315
  · exact B1521319
  · exact B1521323
  · exact B1521327
  · exact B1521331
  · exact B1521335
  · exact B1521339
  · exact B1521343
  · exact B1521347
  · exact B1521351
  · exact B1521355
  · exact B1521359
  · exact B1521363
  · exact B1521367
  · exact B1521371
  · exact B1521375
  · exact B1521379
  · exact B1521383
  · exact B1521387
  · exact B1521391
  · exact B1521395
  · exact B1521399
  · exact B1521403
  · exact B1521407
  · exact B1521411
  · exact B1521415
  · exact B1521419
  · exact B1521423
  · exact B1521427
  · exact B1521431
  · exact B1521435
  · exact B1521439
  · exact B1521443
  · exact B1521447
  · exact B1521451
  · exact B1521455
  · exact B1521459
  · exact B1521463
  · exact B1521467
  · exact B1521471
  · exact B1521475
  · exact B1521479
  · exact B1521483
  · exact B1521487
  · exact B1521491
  · exact B1521495
  · exact B1521499
  · exact B1521503
  · exact B1521507
  · exact B1521511
  · exact B1521515
  · exact B1521519
  · exact B1521523
  · exact B1521527
  · exact B1521531
  · exact B1521535
  · exact B1521539
  · exact B1521543
  · exact B1521547
  · exact B1521551
  · exact B1521555
  · exact B1521559
  · exact B1521563
  · exact B1521567
  · exact B1521571
  · exact B1521575
  · exact B1521579
  · exact B1521583
  · exact B1521587
  · exact B1521591
  · exact B1521595
  · exact B1521599
  · exact B1521603
  · exact B1521607
  · exact B1521611
  · exact B1521615
  · exact B1521619
  · exact B1521623
  · exact B1521627
  · exact B1521631
  · exact B1521635
  · exact B1521639
  · exact B1521643
  · exact B1521647
  · exact B1521651
  · exact B1521655
  · exact B1521659
  · exact B1521663
  · exact B1521667
  · exact B1521671
  · exact B1521675
  · exact B1521679
  · exact B1521683
  · exact B1521687
  · exact B1521691
  · exact B1521695
  · exact B1521699
  · exact B1521703
  · exact B1521707
  · exact B1521711
  · exact B1521715
  · exact B1521719
  · exact B1521723
  · exact B1521727
  · exact B1521731
  · exact B1521735
  · exact B1521739
  · exact B1521743
  · exact B1521747
  · exact B1521751
  · exact B1521755
  · exact B1521759
  · exact B1521763
  · exact B1521767
  · exact B1521771
  · exact B1521775
  · exact B1521779
  · exact B1521783
  · exact B1521787
  · exact B1521791
  · exact B1521795
  · exact B1521799
  · exact B1521803
  · exact B1521807
  · exact B1521811
  · exact B1521815
  · exact B1521819
  · exact B1521823
  · exact B1521827
  · exact B1521831
  · exact B1521835
  · exact B1521839
  · exact B1521843
  · exact B1521847
  · exact B1521851
  · exact B1521855
  · exact B1521859
  · exact B1521863
  · exact B1521867
  · exact B1521871
  · exact B1521875
  · exact B1521879
  · exact B1521883
  · exact B1521887
  · exact B1521891
  · exact B1521895
  · exact B1521899
  · exact B1521903
  · exact B1521907
  · exact B1521911
  · exact B1521915
  · exact B1521919
  · exact B1521923
  · exact B1521927
  · exact B1521931
  · exact B1521935
  · exact B1521939
  · exact B1521943
  · exact B1521947
  · exact B1521951
  · exact B1521955
  · exact B1521959
  · exact B1521963
  · exact B1521967
  · exact B1521971
  · exact B1521975
  · exact B1521979
  · exact B1521983
  · exact B1521987
  · exact B1521991
  · exact B1521995
  · exact B1521999
  · exact B1522003
  · exact B1522007
  · exact B1522011
  · exact B1522015
  · exact B1522019
  · exact B1522023
  · exact B1522027
  · exact B1522031
  · exact B1522035
  · exact B1522039
  · exact B1522043
  · exact B1522047
  · exact B1522051
  · exact B1522055
  · exact B1522059
  · exact B1522063
  · exact B1522067
  · exact B1522071
  · exact B1522075
  · exact B1522079
  · exact B1522083
  · exact B1522087
  · exact B1522091
  · exact B1522095
  · exact B1522099
  · exact B1522103
  · exact B1522107
  · exact B1522111
  · exact B1522115
  · exact B1522119
  · exact B1522123
  · exact B1522127
  · exact B1522131
  · exact B1522135
  · exact B1522139
  · exact B1522143
  · exact B1522147
  · exact B1522151
  · exact B1522155
  · exact B1522159
  · exact B1522163
  · exact B1522167
  · exact B1522171
  · exact B1522175
  · exact B1522179
  · exact B1522183
  · exact B1522187
  · exact B1522191
  · exact B1522195
  · exact B1522199
  · exact B1522203
  · exact B1522207
  · exact B1522211
  · exact B1522215
  · exact B1522219
  · exact B1522223
  · exact B1522227
  · exact B1522231
  · exact B1522235
  · exact B1522239
  · exact B1522243
  · exact B1522247
  · exact B1522251
  · exact B1522255
  · exact B1522259
  · exact B1522263
  · exact B1522267
  · exact B1522271
  · exact B1522275
  · exact B1522279
  · exact B1522283
  · exact B1522287
  · exact B1522291
  · exact B1522295
  · exact B1522299
  · exact B1522303
  · exact B1522307
  · exact B1522311
  · exact B1522315
  · exact B1522319
  · exact B1522323
  · exact B1522327
  · exact B1522331
  · exact B1522335
  · exact B1522339
  · exact B1522343
  · exact B1522347
  · exact B1522351
  · exact B1522355
  · exact B1522359
  · exact B1522363
  · exact B1522367
  · exact B1522371
  · exact B1522375
  · exact B1522379
  · exact B1522383
  · exact B1522387
  · exact B1522391
  · exact B1522395
  · exact B1522399
  · exact B1522403
  · exact B1522407
  · exact B1522411
  · exact B1522415
  · exact B1522419
  · exact B1522423
  · exact B1522427
  · exact B1522431
  · exact B1522435
  · exact B1522439
  · exact B1522443
  · exact B1522447
  · exact B1522451
  · exact B1522455

theorem solution (m : ℕ) (hlo : 1520457 ≤ m) (hhi : m ≤ 1522457) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 380114 ≤ j := by omega
    have hj2 : j ≤ 380613 := by omega
    have hb : Blo 1520457 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
