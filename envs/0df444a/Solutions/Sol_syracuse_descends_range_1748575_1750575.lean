-- Prove2me | solution 1 for syracuse_descends_range_1748575_1750575
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:36:03.811329+00:00
-- url     : https://prove2.me/submissions/d8d0d88e-a8f7-44b5-9b64-de69620aa5de

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


theorem B44335189 : Blo 1748575 44335189 := bbase (se 8 (by rfl) ⟨259776, by rfl⟩ : syracuseStep 44335189 = 519553) (by norm_num)
theorem B1867865 : Blo 1748575 1867865 := bbase (se 2 (by rfl) ⟨700449, by rfl⟩ : syracuseStep 1867865 = 1400899) (by norm_num)
theorem B7471237 : Blo 1748575 7471237 := bbase (se 4 (by rfl) ⟨700428, by rfl⟩ : syracuseStep 7471237 = 1400857) (by norm_num)
theorem B14180629 : Blo 1748575 14180629 := bbase (se 6 (by rfl) ⟨332358, by rfl⟩ : syracuseStep 14180629 = 664717) (by norm_num)
theorem B2801957 : Blo 1748575 2801957 := bbase (se 4 (by rfl) ⟨262683, by rfl⟩ : syracuseStep 2801957 = 525367) (by norm_num)
theorem B5906789 : Blo 1748575 5906789 := bbase (se 4 (by rfl) ⟨553761, by rfl⟩ : syracuseStep 5906789 = 1107523) (by norm_num)
theorem B3596653 : Blo 1748575 3596653 := bbase (se 3 (by rfl) ⟨674372, by rfl⟩ : syracuseStep 3596653 = 1348745) (by norm_num)
theorem B3547525 : Blo 1748575 3547525 := bbase (se 4 (by rfl) ⟨332580, by rfl⟩ : syracuseStep 3547525 = 665161) (by norm_num)
theorem B2245001 : Blo 1748575 2245001 := bbase (se 2 (by rfl) ⟨841875, by rfl⟩ : syracuseStep 2245001 = 1683751) (by norm_num)
theorem B4981189 : Blo 1748575 4981189 := bbase (se 4 (by rfl) ⟨466986, by rfl⟩ : syracuseStep 4981189 = 933973) (by norm_num)
theorem B14942677 : Blo 1748575 14942677 := bbase (se 7 (by rfl) ⟨175109, by rfl⟩ : syracuseStep 14942677 = 350219) (by norm_num)
theorem B5603813 : Blo 1748575 5603813 := bbase (se 4 (by rfl) ⟨525357, by rfl⟩ : syracuseStep 5603813 = 1050715) (by norm_num)
theorem B8856053 : Blo 1748575 8856053 := bbase (se 5 (by rfl) ⟨415127, by rfl⟩ : syracuseStep 8856053 = 830255) (by norm_num)
theorem B6644213 : Blo 1748575 6644213 := bbase (se 5 (by rfl) ⟨311447, by rfl⟩ : syracuseStep 6644213 = 622895) (by norm_num)
theorem B4203053 : Blo 1748575 4203053 := bbase (se 3 (by rfl) ⟨788072, by rfl⟩ : syracuseStep 4203053 = 1576145) (by norm_num)
theorem B2490925 : Blo 1748575 2490925 := bbase (se 3 (by rfl) ⟨467048, by rfl⟩ : syracuseStep 2490925 = 934097) (by norm_num)
theorem B3367565 : Blo 1748575 3367565 := bbase (se 3 (by rfl) ⟨631418, by rfl⟩ : syracuseStep 3367565 = 1262837) (by norm_num)
theorem B5604005 : Blo 1748575 5604005 := bbase (se 4 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 5604005 = 1050751) (by norm_num)
theorem B3736277 : Blo 1748575 3736277 := bbase (se 7 (by rfl) ⟨43784, by rfl⟩ : syracuseStep 3736277 = 87569) (by norm_num)
theorem B2802413 : Blo 1748575 2802413 := bbase (se 3 (by rfl) ⟨525452, by rfl⟩ : syracuseStep 2802413 = 1050905) (by norm_num)
theorem B6644501 : Blo 1748575 6644501 := bbase (se 6 (by rfl) ⟨155730, by rfl⟩ : syracuseStep 6644501 = 311461) (by norm_num)
theorem B5907221 : Blo 1748575 5907221 := bbase (se 6 (by rfl) ⟨138450, by rfl⟩ : syracuseStep 5907221 = 276901) (by norm_num)
theorem B2769733 : Blo 1748575 2769733 := bbase (se 4 (by rfl) ⟨259662, by rfl⟩ : syracuseStep 2769733 = 519325) (by norm_num)
theorem B1868617 : Blo 1748575 1868617 := bbase (se 2 (by rfl) ⟨700731, by rfl⟩ : syracuseStep 1868617 = 1401463) (by norm_num)
theorem B4203397 : Blo 1748575 4203397 := bbase (se 4 (by rfl) ⟨394068, by rfl⟩ : syracuseStep 4203397 = 788137) (by norm_num)
theorem B1868689 : Blo 1748575 1868689 := bbase (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) (by norm_num)
theorem B16810901 : Blo 1748575 16810901 := bbase (se 6 (by rfl) ⟨394005, by rfl⟩ : syracuseStep 16810901 = 788011) (by norm_num)
theorem B2802637 : Blo 1748575 2802637 := bbase (se 3 (by rfl) ⟨525494, by rfl⟩ : syracuseStep 2802637 = 1050989) (by norm_num)
theorem B2802701 : Blo 1748575 2802701 := bbase (se 3 (by rfl) ⟨525506, by rfl⟩ : syracuseStep 2802701 = 1051013) (by norm_num)
theorem B1967161 : Blo 1748575 1967161 := bbase (se 2 (by rfl) ⟨737685, by rfl⟩ : syracuseStep 1967161 = 1475371) (by norm_num)
theorem B1868869 : Blo 1748575 1868869 := bbase (se 4 (by rfl) ⟨175206, by rfl⟩ : syracuseStep 1868869 = 350413) (by norm_num)
theorem B1967197 : Blo 1748575 1967197 := bbase (se 3 (by rfl) ⟨368849, by rfl⟩ : syracuseStep 1967197 = 737699) (by norm_num)
theorem B4203629 : Blo 1748575 4203629 := bbase (se 3 (by rfl) ⟨788180, by rfl⟩ : syracuseStep 4203629 = 1576361) (by norm_num)
theorem B2491517 : Blo 1748575 2491517 := bbase (se 3 (by rfl) ⟨467159, by rfl⟩ : syracuseStep 2491517 = 934319) (by norm_num)
theorem B1967233 : Blo 1748575 1967233 := bbase (se 2 (by rfl) ⟨737712, by rfl⟩ : syracuseStep 1967233 = 1475425) (by norm_num)
theorem B2802829 : Blo 1748575 2802829 := bbase (se 3 (by rfl) ⟨525530, by rfl⟩ : syracuseStep 2802829 = 1051061) (by norm_num)
theorem B1967269 : Blo 1748575 1967269 := bbase (se 4 (by rfl) ⟨184431, by rfl⟩ : syracuseStep 1967269 = 368863) (by norm_num)
theorem B12608693 : Blo 1748575 12608693 := bbase (se 5 (by rfl) ⟨591032, by rfl⟩ : syracuseStep 12608693 = 1182065) (by norm_num)
theorem B5907653 : Blo 1748575 5907653 := bbase (se 4 (by rfl) ⟨553842, by rfl⟩ : syracuseStep 5907653 = 1107685) (by norm_num)
theorem B1967305 : Blo 1748575 1967305 := bbase (se 2 (by rfl) ⟨737739, by rfl⟩ : syracuseStep 1967305 = 1475479) (by norm_num)
theorem B2491597 : Blo 1748575 2491597 := bbase (se 3 (by rfl) ⟨467174, by rfl⟩ : syracuseStep 2491597 = 934349) (by norm_num)
theorem B2213077 : Blo 1748575 2213077 := bbase (se 7 (by rfl) ⟨25934, by rfl⟩ : syracuseStep 2213077 = 51869) (by norm_num)
theorem B1967341 : Blo 1748575 1967341 := bbase (se 3 (by rfl) ⟨368876, by rfl⟩ : syracuseStep 1967341 = 737753) (by norm_num)
theorem B1967377 : Blo 1748575 1967377 := bbase (se 2 (by rfl) ⟨737766, by rfl⟩ : syracuseStep 1967377 = 1475533) (by norm_num)
theorem B4203821 : Blo 1748575 4203821 := bbase (se 3 (by rfl) ⟨788216, by rfl⟩ : syracuseStep 4203821 = 1576433) (by norm_num)
theorem B2213173 : Blo 1748575 2213173 := bbase (se 5 (by rfl) ⟨103742, by rfl⟩ : syracuseStep 2213173 = 207485) (by norm_num)
theorem B1967413 : Blo 1748575 1967413 := bbase (se 5 (by rfl) ⟨92222, by rfl⟩ : syracuseStep 1967413 = 184445) (by norm_num)
theorem B2491717 : Blo 1748575 2491717 := bbase (se 4 (by rfl) ⟨233598, by rfl⟩ : syracuseStep 2491717 = 467197) (by norm_num)
theorem B1967449 : Blo 1748575 1967449 := bbase (se 2 (by rfl) ⟨737793, by rfl⟩ : syracuseStep 1967449 = 1475587) (by norm_num)
theorem B1967485 : Blo 1748575 1967485 := bbase (se 3 (by rfl) ⟨368903, by rfl⟩ : syracuseStep 1967485 = 737807) (by norm_num)
theorem B2622869 : Blo 1748575 2622869 := bbase (se 6 (by rfl) ⟨61473, by rfl⟩ : syracuseStep 2622869 = 122947) (by norm_num)
theorem B1967521 : Blo 1748575 1967521 := bbase (se 2 (by rfl) ⟨737820, by rfl⟩ : syracuseStep 1967521 = 1475641) (by norm_num)
theorem B2491813 : Blo 1748575 2491813 := bbase (se 4 (by rfl) ⟨233607, by rfl⟩ : syracuseStep 2491813 = 467215) (by norm_num)
theorem B2622893 : Blo 1748575 2622893 := bbase (se 3 (by rfl) ⟨491792, by rfl⟩ : syracuseStep 2622893 = 983585) (by norm_num)
theorem B2622917 : Blo 1748575 2622917 := bbase (se 4 (by rfl) ⟨245898, by rfl⟩ : syracuseStep 2622917 = 491797) (by norm_num)
theorem B1967557 : Blo 1748575 1967557 := bbase (se 4 (by rfl) ⟨184458, by rfl⟩ : syracuseStep 1967557 = 368917) (by norm_num)
theorem B3737029 : Blo 1748575 3737029 := bbase (se 4 (by rfl) ⟨350346, by rfl⟩ : syracuseStep 3737029 = 700693) (by norm_num)
theorem B2622941 : Blo 1748575 2622941 := bbase (se 3 (by rfl) ⟨491801, by rfl⟩ : syracuseStep 2622941 = 983603) (by norm_num)
theorem B2213345 : Blo 1748575 2213345 := bbase (se 2 (by rfl) ⟨830004, by rfl⟩ : syracuseStep 2213345 = 1660009) (by norm_num)
theorem B1967593 : Blo 1748575 1967593 := bbase (se 2 (by rfl) ⟨737847, by rfl⟩ : syracuseStep 1967593 = 1475695) (by norm_num)
theorem B2622965 : Blo 1748575 2622965 := bbase (se 5 (by rfl) ⟨122951, by rfl⟩ : syracuseStep 2622965 = 245903) (by norm_num)
theorem B1869313 : Blo 1748575 1869313 := bbase (se 2 (by rfl) ⟨700992, by rfl⟩ : syracuseStep 1869313 = 1401985) (by norm_num)
theorem B2622989 : Blo 1748575 2622989 := bbase (se 3 (by rfl) ⟨491810, by rfl⟩ : syracuseStep 2622989 = 983621) (by norm_num)
theorem B1967629 : Blo 1748575 1967629 := bbase (se 3 (by rfl) ⟨368930, by rfl⟩ : syracuseStep 1967629 = 737861) (by norm_num)
theorem B2213401 : Blo 1748575 2213401 := bbase (se 2 (by rfl) ⟨830025, by rfl⟩ : syracuseStep 2213401 = 1660051) (by norm_num)
theorem B2623013 : Blo 1748575 2623013 := bbase (se 4 (by rfl) ⟨245907, by rfl⟩ : syracuseStep 2623013 = 491815) (by norm_num)
theorem B1967665 : Blo 1748575 1967665 := bbase (se 2 (by rfl) ⟨737874, by rfl⟩ : syracuseStep 1967665 = 1475749) (by norm_num)
theorem B2623037 : Blo 1748575 2623037 := bbase (se 3 (by rfl) ⟨491819, by rfl⟩ : syracuseStep 2623037 = 983639) (by norm_num)
theorem B4204109 : Blo 1748575 4204109 := bbase (se 3 (by rfl) ⟨788270, by rfl⟩ : syracuseStep 4204109 = 1576541) (by norm_num)
theorem B2623061 : Blo 1748575 2623061 := bbase (se 8 (by rfl) ⟨15369, by rfl⟩ : syracuseStep 2623061 = 30739) (by norm_num)
theorem B1967701 : Blo 1748575 1967701 := bbase (se 8 (by rfl) ⟨11529, by rfl⟩ : syracuseStep 1967701 = 23059) (by norm_num)
theorem B3737173 : Blo 1748575 3737173 := bbase (se 8 (by rfl) ⟨21897, by rfl⟩ : syracuseStep 3737173 = 43795) (by norm_num)
theorem B3368549 : Blo 1748575 3368549 := bbase (se 4 (by rfl) ⟨315801, by rfl⟩ : syracuseStep 3368549 = 631603) (by norm_num)
theorem B2623085 : Blo 1748575 2623085 := bbase (se 3 (by rfl) ⟨491828, by rfl⟩ : syracuseStep 2623085 = 983657) (by norm_num)
theorem B5908085 : Blo 1748575 5908085 := bbase (se 5 (by rfl) ⟨276941, by rfl⟩ : syracuseStep 5908085 = 553883) (by norm_num)
theorem B1967737 : Blo 1748575 1967737 := bbase (se 2 (by rfl) ⟨737901, by rfl⟩ : syracuseStep 1967737 = 1475803) (by norm_num)
theorem B2213497 : Blo 1748575 2213497 := bbase (se 2 (by rfl) ⟨830061, by rfl⟩ : syracuseStep 2213497 = 1660123) (by norm_num)
theorem B2950789 : Blo 1748575 2950789 := bbase (se 4 (by rfl) ⟨276636, by rfl⟩ : syracuseStep 2950789 = 553273) (by norm_num)
theorem B2623109 : Blo 1748575 2623109 := bbase (se 4 (by rfl) ⟨245916, by rfl⟩ : syracuseStep 2623109 = 491833) (by norm_num)
theorem B2623133 : Blo 1748575 2623133 := bbase (se 3 (by rfl) ⟨491837, by rfl⟩ : syracuseStep 2623133 = 983675) (by norm_num)
theorem B1967773 : Blo 1748575 1967773 := bbase (se 3 (by rfl) ⟨368957, by rfl⟩ : syracuseStep 1967773 = 737915) (by norm_num)
theorem B2623157 : Blo 1748575 2623157 := bbase (se 5 (by rfl) ⟨122960, by rfl⟩ : syracuseStep 2623157 = 245921) (by norm_num)
theorem B1967809 : Blo 1748575 1967809 := bbase (se 2 (by rfl) ⟨737928, by rfl⟩ : syracuseStep 1967809 = 1475857) (by norm_num)
theorem B2623181 : Blo 1748575 2623181 := bbase (se 3 (by rfl) ⟨491846, by rfl⟩ : syracuseStep 2623181 = 983693) (by norm_num)
theorem B2950877 : Blo 1748575 2950877 := bbase (se 3 (by rfl) ⟨553289, by rfl⟩ : syracuseStep 2950877 = 1106579) (by norm_num)
theorem B2623205 : Blo 1748575 2623205 := bbase (se 4 (by rfl) ⟨245925, by rfl⟩ : syracuseStep 2623205 = 491851) (by norm_num)
theorem B1967845 : Blo 1748575 1967845 := bbase (se 4 (by rfl) ⟨184485, by rfl⟩ : syracuseStep 1967845 = 368971) (by norm_num)
theorem B2623229 : Blo 1748575 2623229 := bbase (se 3 (by rfl) ⟨491855, by rfl⟩ : syracuseStep 2623229 = 983711) (by norm_num)
theorem B8857349 : Blo 1748575 8857349 := bbase (se 4 (by rfl) ⟨830376, by rfl⟩ : syracuseStep 8857349 = 1660753) (by norm_num)
theorem B1967881 : Blo 1748575 1967881 := bbase (se 2 (by rfl) ⟨737955, by rfl⟩ : syracuseStep 1967881 = 1475911) (by norm_num)
theorem B2623253 : Blo 1748575 2623253 := bbase (se 6 (by rfl) ⟨61482, by rfl⟩ : syracuseStep 2623253 = 122965) (by norm_num)
theorem B2213669 : Blo 1748575 2213669 := bbase (se 4 (by rfl) ⟨207531, by rfl⟩ : syracuseStep 2213669 = 415063) (by norm_num)
theorem B2623277 : Blo 1748575 2623277 := bbase (se 3 (by rfl) ⟨491864, by rfl⟩ : syracuseStep 2623277 = 983729) (by norm_num)
theorem B1967917 : Blo 1748575 1967917 := bbase (se 3 (by rfl) ⟨368984, by rfl⟩ : syracuseStep 1967917 = 737969) (by norm_num)
theorem B2623301 : Blo 1748575 2623301 := bbase (se 4 (by rfl) ⟨245934, by rfl⟩ : syracuseStep 2623301 = 491869) (by norm_num)
theorem B1967953 : Blo 1748575 1967953 := bbase (se 2 (by rfl) ⟨737982, by rfl⟩ : syracuseStep 1967953 = 1475965) (by norm_num)
theorem B2951005 : Blo 1748575 2951005 := bbase (se 3 (by rfl) ⟨553313, by rfl⟩ : syracuseStep 2951005 = 1106627) (by norm_num)
theorem B2623325 : Blo 1748575 2623325 := bbase (se 3 (by rfl) ⟨491873, by rfl⟩ : syracuseStep 2623325 = 983747) (by norm_num)
theorem B2213725 : Blo 1748575 2213725 := bbase (se 3 (by rfl) ⟨415073, by rfl⟩ : syracuseStep 2213725 = 830147) (by norm_num)
theorem B2623349 : Blo 1748575 2623349 := bbase (se 5 (by rfl) ⟨122969, by rfl⟩ : syracuseStep 2623349 = 245939) (by norm_num)
theorem B1967989 : Blo 1748575 1967989 := bbase (se 5 (by rfl) ⟨92249, by rfl⟩ : syracuseStep 1967989 = 184499) (by norm_num)
theorem B2623373 : Blo 1748575 2623373 := bbase (se 3 (by rfl) ⟨491882, by rfl⟩ : syracuseStep 2623373 = 983765) (by norm_num)
theorem B2992021 : Blo 1748575 2992021 := bbase (se 6 (by rfl) ⟨70125, by rfl⟩ : syracuseStep 2992021 = 140251) (by norm_num)
theorem B2492309 : Blo 1748575 2492309 := bbase (se 6 (by rfl) ⟨58413, by rfl⟩ : syracuseStep 2492309 = 116827) (by norm_num)
theorem B1968025 : Blo 1748575 1968025 := bbase (se 2 (by rfl) ⟨738009, by rfl⟩ : syracuseStep 1968025 = 1476019) (by norm_num)
theorem B2623397 : Blo 1748575 2623397 := bbase (se 4 (by rfl) ⟨245943, by rfl⟩ : syracuseStep 2623397 = 491887) (by norm_num)
theorem B8406949 : Blo 1748575 8406949 := bbase (se 4 (by rfl) ⟨788151, by rfl⟩ : syracuseStep 8406949 = 1576303) (by norm_num)
theorem B2951093 : Blo 1748575 2951093 := bbase (se 5 (by rfl) ⟨138332, by rfl⟩ : syracuseStep 2951093 = 276665) (by norm_num)
theorem B5187509 : Blo 1748575 5187509 := bbase (se 5 (by rfl) ⟨243164, by rfl⟩ : syracuseStep 5187509 = 486329) (by norm_num)
theorem B6645685 : Blo 1748575 6645685 := bbase (se 5 (by rfl) ⟨311516, by rfl⟩ : syracuseStep 6645685 = 623033) (by norm_num)
theorem B2623421 : Blo 1748575 2623421 := bbase (se 3 (by rfl) ⟨491891, by rfl⟩ : syracuseStep 2623421 = 983783) (by norm_num)
theorem B2213821 : Blo 1748575 2213821 := bbase (se 3 (by rfl) ⟨415091, by rfl⟩ : syracuseStep 2213821 = 830183) (by norm_num)
theorem B1968061 : Blo 1748575 1968061 := bbase (se 3 (by rfl) ⟨369011, by rfl⟩ : syracuseStep 1968061 = 738023) (by norm_num)
theorem B3737549 : Blo 1748575 3737549 := bbase (se 3 (by rfl) ⟨700790, by rfl⟩ : syracuseStep 3737549 = 1401581) (by norm_num)
theorem B2623445 : Blo 1748575 2623445 := bbase (se 7 (by rfl) ⟨30743, by rfl⟩ : syracuseStep 2623445 = 61487) (by norm_num)
theorem B14378965 : Blo 1748575 14378965 := bbase (se 7 (by rfl) ⟨168503, by rfl⟩ : syracuseStep 14378965 = 337007) (by norm_num)
theorem B1968097 : Blo 1748575 1968097 := bbase (se 2 (by rfl) ⟨738036, by rfl⟩ : syracuseStep 1968097 = 1476073) (by norm_num)
theorem B2623469 : Blo 1748575 2623469 := bbase (se 3 (by rfl) ⟨491900, by rfl⟩ : syracuseStep 2623469 = 983801) (by norm_num)
theorem B3319805 : Blo 1748575 3319805 := bbase (se 3 (by rfl) ⟨622463, by rfl⟩ : syracuseStep 3319805 = 1244927) (by norm_num)
theorem B2623493 : Blo 1748575 2623493 := bbase (se 4 (by rfl) ⟨245952, by rfl⟩ : syracuseStep 2623493 = 491905) (by norm_num)
theorem B1968133 : Blo 1748575 1968133 := bbase (se 4 (by rfl) ⟨184512, by rfl⟩ : syracuseStep 1968133 = 369025) (by norm_num)
theorem B2623517 : Blo 1748575 2623517 := bbase (se 3 (by rfl) ⟨491909, by rfl⟩ : syracuseStep 2623517 = 983819) (by norm_num)
theorem B1968169 : Blo 1748575 1968169 := bbase (se 2 (by rfl) ⟨738063, by rfl⟩ : syracuseStep 1968169 = 1476127) (by norm_num)
theorem B2951221 : Blo 1748575 2951221 := bbase (se 5 (by rfl) ⟨138338, by rfl⟩ : syracuseStep 2951221 = 276677) (by norm_num)
theorem B2623541 : Blo 1748575 2623541 := bbase (se 5 (by rfl) ⟨122978, by rfl⟩ : syracuseStep 2623541 = 245957) (by norm_num)
theorem B2623565 : Blo 1748575 2623565 := bbase (se 3 (by rfl) ⟨491918, by rfl⟩ : syracuseStep 2623565 = 983837) (by norm_num)
theorem B1968205 : Blo 1748575 1968205 := bbase (se 3 (by rfl) ⟨369038, by rfl⟩ : syracuseStep 1968205 = 738077) (by norm_num)
theorem B2623589 : Blo 1748575 2623589 := bbase (se 4 (by rfl) ⟨245961, by rfl⟩ : syracuseStep 2623589 = 491923) (by norm_num)
theorem B2213993 : Blo 1748575 2213993 := bbase (se 2 (by rfl) ⟨830247, by rfl⟩ : syracuseStep 2213993 = 1660495) (by norm_num)
theorem B1968241 : Blo 1748575 1968241 := bbase (se 2 (by rfl) ⟨738090, by rfl⟩ : syracuseStep 1968241 = 1476181) (by norm_num)
theorem B8308853 : Blo 1748575 8308853 := bbase (se 5 (by rfl) ⟨389477, by rfl⟩ : syracuseStep 8308853 = 778955) (by norm_num)
theorem B2623613 : Blo 1748575 2623613 := bbase (se 3 (by rfl) ⟨491927, by rfl⟩ : syracuseStep 2623613 = 983855) (by norm_num)
theorem B3934349 : Blo 1748575 3934349 := bbase (se 3 (by rfl) ⟨737690, by rfl⟩ : syracuseStep 3934349 = 1475381) (by norm_num)
theorem B2951309 : Blo 1748575 2951309 := bbase (se 3 (by rfl) ⟨553370, by rfl⟩ : syracuseStep 2951309 = 1106741) (by norm_num)
theorem B3319957 : Blo 1748575 3319957 := bbase (se 6 (by rfl) ⟨77811, by rfl⟩ : syracuseStep 3319957 = 155623) (by norm_num)
theorem B2623637 : Blo 1748575 2623637 := bbase (se 6 (by rfl) ⟨61491, by rfl⟩ : syracuseStep 2623637 = 122983) (by norm_num)
theorem B1968277 : Blo 1748575 1968277 := bbase (se 6 (by rfl) ⟨46131, by rfl⟩ : syracuseStep 1968277 = 92263) (by norm_num)
theorem B2214049 : Blo 1748575 2214049 := bbase (se 2 (by rfl) ⟨830268, by rfl⟩ : syracuseStep 2214049 = 1660537) (by norm_num)
theorem B2623661 : Blo 1748575 2623661 := bbase (se 3 (by rfl) ⟨491936, by rfl⟩ : syracuseStep 2623661 = 983873) (by norm_num)
theorem B1968313 : Blo 1748575 1968313 := bbase (se 2 (by rfl) ⟨738117, by rfl⟩ : syracuseStep 1968313 = 1476235) (by norm_num)
theorem B2623685 : Blo 1748575 2623685 := bbase (se 4 (by rfl) ⟨245970, by rfl⟩ : syracuseStep 2623685 = 491941) (by norm_num)
theorem B3934421 : Blo 1748575 3934421 := bbase (se 7 (by rfl) ⟨46106, by rfl⟩ : syracuseStep 3934421 = 92213) (by norm_num)
theorem B2623709 : Blo 1748575 2623709 := bbase (se 3 (by rfl) ⟨491945, by rfl⟩ : syracuseStep 2623709 = 983891) (by norm_num)
theorem B1968349 : Blo 1748575 1968349 := bbase (se 3 (by rfl) ⟨369065, by rfl⟩ : syracuseStep 1968349 = 738131) (by norm_num)
theorem B6645989 : Blo 1748575 6645989 := bbase (se 4 (by rfl) ⟨623061, by rfl⟩ : syracuseStep 6645989 = 1246123) (by norm_num)
theorem B2623733 : Blo 1748575 2623733 := bbase (se 5 (by rfl) ⟨122987, by rfl⟩ : syracuseStep 2623733 = 245975) (by norm_num)
theorem B2214145 : Blo 1748575 2214145 := bbase (se 2 (by rfl) ⟨830304, by rfl⟩ : syracuseStep 2214145 = 1660609) (by norm_num)
theorem B1968385 : Blo 1748575 1968385 := bbase (se 2 (by rfl) ⟨738144, by rfl⟩ : syracuseStep 1968385 = 1476289) (by norm_num)
theorem B2951437 : Blo 1748575 2951437 := bbase (se 3 (by rfl) ⟨553394, by rfl⟩ : syracuseStep 2951437 = 1106789) (by norm_num)
theorem B2623757 : Blo 1748575 2623757 := bbase (se 3 (by rfl) ⟨491954, by rfl⟩ : syracuseStep 2623757 = 983909) (by norm_num)
theorem B3934493 : Blo 1748575 3934493 := bbase (se 3 (by rfl) ⟨737717, by rfl⟩ : syracuseStep 3934493 = 1475435) (by norm_num)
theorem B2623781 : Blo 1748575 2623781 := bbase (se 4 (by rfl) ⟨245979, by rfl⟩ : syracuseStep 2623781 = 491959) (by norm_num)
theorem B1968421 : Blo 1748575 1968421 := bbase (se 4 (by rfl) ⟨184539, by rfl⟩ : syracuseStep 1968421 = 369079) (by norm_num)
theorem B2623805 : Blo 1748575 2623805 := bbase (se 3 (by rfl) ⟨491963, by rfl⟩ : syracuseStep 2623805 = 983927) (by norm_num)
theorem B3737917 : Blo 1748575 3737917 := bbase (se 3 (by rfl) ⟨700859, by rfl⟩ : syracuseStep 3737917 = 1401719) (by norm_num)
theorem B1968457 : Blo 1748575 1968457 := bbase (se 2 (by rfl) ⟨738171, by rfl⟩ : syracuseStep 1968457 = 1476343) (by norm_num)
theorem B2623829 : Blo 1748575 2623829 := bbase (se 10 (by rfl) ⟨3843, by rfl⟩ : syracuseStep 2623829 = 7687) (by norm_num)
theorem B2804053 : Blo 1748575 2804053 := bbase (se 10 (by rfl) ⟨4107, by rfl⟩ : syracuseStep 2804053 = 8215) (by norm_num)
theorem B3934565 : Blo 1748575 3934565 := bbase (se 4 (by rfl) ⟨368865, by rfl⟩ : syracuseStep 3934565 = 737731) (by norm_num)
theorem B2951525 : Blo 1748575 2951525 := bbase (se 4 (by rfl) ⟨276705, by rfl⟩ : syracuseStep 2951525 = 553411) (by norm_num)
theorem B2623853 : Blo 1748575 2623853 := bbase (se 3 (by rfl) ⟨491972, by rfl⟩ : syracuseStep 2623853 = 983945) (by norm_num)
theorem B1968493 : Blo 1748575 1968493 := bbase (se 3 (by rfl) ⟨369092, by rfl⟩ : syracuseStep 1968493 = 738185) (by norm_num)
theorem B2623877 : Blo 1748575 2623877 := bbase (se 4 (by rfl) ⟨245988, by rfl⟩ : syracuseStep 2623877 = 491977) (by norm_num)
theorem B1968529 : Blo 1748575 1968529 := bbase (se 2 (by rfl) ⟨738198, by rfl⟩ : syracuseStep 1968529 = 1476397) (by norm_num)
theorem B12954005 : Blo 1748575 12954005 := bbase (se 6 (by rfl) ⟨303609, by rfl⟩ : syracuseStep 12954005 = 607219) (by norm_num)
theorem B14944661 : Blo 1748575 14944661 := bbase (se 6 (by rfl) ⟨350265, by rfl⟩ : syracuseStep 14944661 = 700531) (by norm_num)
theorem B2623901 : Blo 1748575 2623901 := bbase (se 3 (by rfl) ⟨491981, by rfl⟩ : syracuseStep 2623901 = 983963) (by norm_num)
theorem B3934637 : Blo 1748575 3934637 := bbase (se 3 (by rfl) ⟨737744, by rfl⟩ : syracuseStep 3934637 = 1475489) (by norm_num)
theorem B2214317 : Blo 1748575 2214317 := bbase (se 3 (by rfl) ⟨415184, by rfl⟩ : syracuseStep 2214317 = 830369) (by norm_num)
theorem B2623925 : Blo 1748575 2623925 := bbase (se 5 (by rfl) ⟨122996, by rfl⟩ : syracuseStep 2623925 = 245993) (by norm_num)
theorem B1968565 : Blo 1748575 1968565 := bbase (se 5 (by rfl) ⟨92276, by rfl⟩ : syracuseStep 1968565 = 184553) (by norm_num)
theorem B3320261 : Blo 1748575 3320261 := bbase (se 4 (by rfl) ⟨311274, by rfl⟩ : syracuseStep 3320261 = 622549) (by norm_num)
theorem B2623949 : Blo 1748575 2623949 := bbase (se 3 (by rfl) ⟨491990, by rfl⟩ : syracuseStep 2623949 = 983981) (by norm_num)
theorem B1968601 : Blo 1748575 1968601 := bbase (se 2 (by rfl) ⟨738225, by rfl⟩ : syracuseStep 1968601 = 1476451) (by norm_num)
theorem B2951653 : Blo 1748575 2951653 := bbase (se 4 (by rfl) ⟨276717, by rfl⟩ : syracuseStep 2951653 = 553435) (by norm_num)
theorem B2623973 : Blo 1748575 2623973 := bbase (se 4 (by rfl) ⟨245997, by rfl⟩ : syracuseStep 2623973 = 491995) (by norm_num)
theorem B2214373 : Blo 1748575 2214373 := bbase (se 4 (by rfl) ⟨207597, by rfl⟩ : syracuseStep 2214373 = 415195) (by norm_num)
theorem B7096805 : Blo 1748575 7096805 := bbase (se 4 (by rfl) ⟨665325, by rfl⟩ : syracuseStep 7096805 = 1330651) (by norm_num)
theorem B3934709 : Blo 1748575 3934709 := bbase (se 5 (by rfl) ⟨184439, by rfl⟩ : syracuseStep 3934709 = 368879) (by norm_num)
theorem B2623997 : Blo 1748575 2623997 := bbase (se 3 (by rfl) ⟨491999, by rfl⟩ : syracuseStep 2623997 = 983999) (by norm_num)
theorem B1968637 : Blo 1748575 1968637 := bbase (se 3 (by rfl) ⟨369119, by rfl⟩ : syracuseStep 1968637 = 738239) (by norm_num)
theorem B6302213 : Blo 1748575 6302213 := bbase (se 4 (by rfl) ⟨590832, by rfl⟩ : syracuseStep 6302213 = 1181665) (by norm_num)
theorem B2624021 : Blo 1748575 2624021 := bbase (se 6 (by rfl) ⟨61500, by rfl⟩ : syracuseStep 2624021 = 123001) (by norm_num)
theorem B1968673 : Blo 1748575 1968673 := bbase (se 2 (by rfl) ⟨738252, by rfl⟩ : syracuseStep 1968673 = 1476505) (by norm_num)
theorem B4426285 : Blo 1748575 4426285 := bbase (se 3 (by rfl) ⟨829928, by rfl⟩ : syracuseStep 4426285 = 1659857) (by norm_num)
theorem B2624045 : Blo 1748575 2624045 := bbase (se 3 (by rfl) ⟨492008, by rfl⟩ : syracuseStep 2624045 = 984017) (by norm_num)
theorem B3934781 : Blo 1748575 3934781 := bbase (se 3 (by rfl) ⟨737771, by rfl⟩ : syracuseStep 3934781 = 1475543) (by norm_num)
theorem B2951741 : Blo 1748575 2951741 := bbase (se 3 (by rfl) ⟨553451, by rfl⟩ : syracuseStep 2951741 = 1106903) (by norm_num)
theorem B2624069 : Blo 1748575 2624069 := bbase (se 4 (by rfl) ⟨246006, by rfl⟩ : syracuseStep 2624069 = 492013) (by norm_num)
theorem B2214469 : Blo 1748575 2214469 := bbase (se 4 (by rfl) ⟨207606, by rfl⟩ : syracuseStep 2214469 = 415213) (by norm_num)
theorem B1968709 : Blo 1748575 1968709 := bbase (se 4 (by rfl) ⟨184566, by rfl⟩ : syracuseStep 1968709 = 369133) (by norm_num)
theorem B2624093 : Blo 1748575 2624093 := bbase (se 3 (by rfl) ⟨492017, by rfl⟩ : syracuseStep 2624093 = 984035) (by norm_num)
theorem B1968745 : Blo 1748575 1968745 := bbase (se 2 (by rfl) ⟨738279, by rfl⟩ : syracuseStep 1968745 = 1476559) (by norm_num)
theorem B2624117 : Blo 1748575 2624117 := bbase (se 5 (by rfl) ⟨123005, by rfl⟩ : syracuseStep 2624117 = 246011) (by norm_num)
theorem B3934853 : Blo 1748575 3934853 := bbase (se 4 (by rfl) ⟨368892, by rfl⟩ : syracuseStep 3934853 = 737785) (by norm_num)
theorem B2624141 : Blo 1748575 2624141 := bbase (se 3 (by rfl) ⟨492026, by rfl⟩ : syracuseStep 2624141 = 984053) (by norm_num)
theorem B1968781 : Blo 1748575 1968781 := bbase (se 3 (by rfl) ⟨369146, by rfl⟩ : syracuseStep 1968781 = 738293) (by norm_num)
theorem B4426397 : Blo 1748575 4426397 := bbase (se 3 (by rfl) ⟨829949, by rfl⟩ : syracuseStep 4426397 = 1659899) (by norm_num)
theorem B2624165 : Blo 1748575 2624165 := bbase (se 4 (by rfl) ⟨246015, by rfl⟩ : syracuseStep 2624165 = 492031) (by norm_num)
theorem B1968817 : Blo 1748575 1968817 := bbase (se 2 (by rfl) ⟨738306, by rfl⟩ : syracuseStep 1968817 = 1476613) (by norm_num)
theorem B2951869 : Blo 1748575 2951869 := bbase (se 3 (by rfl) ⟨553475, by rfl⟩ : syracuseStep 2951869 = 1106951) (by norm_num)
theorem B2624189 : Blo 1748575 2624189 := bbase (se 3 (by rfl) ⟨492035, by rfl⟩ : syracuseStep 2624189 = 984071) (by norm_num)
theorem B3934925 : Blo 1748575 3934925 := bbase (se 3 (by rfl) ⟨737798, by rfl⟩ : syracuseStep 3934925 = 1475597) (by norm_num)
theorem B2624213 : Blo 1748575 2624213 := bbase (se 7 (by rfl) ⟨30752, by rfl⟩ : syracuseStep 2624213 = 61505) (by norm_num)
theorem B1968853 : Blo 1748575 1968853 := bbase (se 7 (by rfl) ⟨23072, by rfl⟩ : syracuseStep 1968853 = 46145) (by norm_num)
theorem B2624237 : Blo 1748575 2624237 := bbase (se 3 (by rfl) ⟨492044, by rfl⟩ : syracuseStep 2624237 = 984089) (by norm_num)
theorem B2214641 : Blo 1748575 2214641 := bbase (se 2 (by rfl) ⟨830490, by rfl⟩ : syracuseStep 2214641 = 1660981) (by norm_num)
theorem B1968889 : Blo 1748575 1968889 := bbase (se 2 (by rfl) ⟨738333, by rfl⟩ : syracuseStep 1968889 = 1476667) (by norm_num)
theorem B2624261 : Blo 1748575 2624261 := bbase (se 4 (by rfl) ⟨246024, by rfl⟩ : syracuseStep 2624261 = 492049) (by norm_num)
theorem B3934997 : Blo 1748575 3934997 := bbase (se 6 (by rfl) ⟨92226, by rfl⟩ : syracuseStep 3934997 = 184453) (by norm_num)
theorem B2951957 : Blo 1748575 2951957 := bbase (se 6 (by rfl) ⟨69186, by rfl⟩ : syracuseStep 2951957 = 138373) (by norm_num)
theorem B2624285 : Blo 1748575 2624285 := bbase (se 3 (by rfl) ⟨492053, by rfl⟩ : syracuseStep 2624285 = 984107) (by norm_num)
theorem B1968925 : Blo 1748575 1968925 := bbase (se 3 (by rfl) ⟨369173, by rfl⟩ : syracuseStep 1968925 = 738347) (by norm_num)
theorem B2214697 : Blo 1748575 2214697 := bbase (se 2 (by rfl) ⟨830511, by rfl⟩ : syracuseStep 2214697 = 1661023) (by norm_num)
theorem B2624309 : Blo 1748575 2624309 := bbase (se 5 (by rfl) ⟨123014, by rfl⟩ : syracuseStep 2624309 = 246029) (by norm_num)
theorem B1968961 : Blo 1748575 1968961 := bbase (se 2 (by rfl) ⟨738360, by rfl⟩ : syracuseStep 1968961 = 1476721) (by norm_num)
theorem B2624333 : Blo 1748575 2624333 := bbase (se 3 (by rfl) ⟨492062, by rfl⟩ : syracuseStep 2624333 = 984125) (by norm_num)
theorem B4426589 : Blo 1748575 4426589 := bbase (se 3 (by rfl) ⟨829985, by rfl⟩ : syracuseStep 4426589 = 1659971) (by norm_num)
theorem B3935069 : Blo 1748575 3935069 := bbase (se 3 (by rfl) ⟨737825, by rfl⟩ : syracuseStep 3935069 = 1475651) (by norm_num)
theorem B2624357 : Blo 1748575 2624357 := bbase (se 4 (by rfl) ⟨246033, by rfl⟩ : syracuseStep 2624357 = 492067) (by norm_num)
theorem B1968997 : Blo 1748575 1968997 := bbase (se 4 (by rfl) ⟨184593, by rfl⟩ : syracuseStep 1968997 = 369187) (by norm_num)
theorem B2624381 : Blo 1748575 2624381 := bbase (se 3 (by rfl) ⟨492071, by rfl⟩ : syracuseStep 2624381 = 984143) (by norm_num)
theorem B2214793 : Blo 1748575 2214793 := bbase (se 2 (by rfl) ⟨830547, by rfl⟩ : syracuseStep 2214793 = 1661095) (by norm_num)
theorem B1969033 : Blo 1748575 1969033 := bbase (se 2 (by rfl) ⟨738387, by rfl⟩ : syracuseStep 1969033 = 1476775) (by norm_num)
theorem B2952085 : Blo 1748575 2952085 := bbase (se 6 (by rfl) ⟨69189, by rfl⟩ : syracuseStep 2952085 = 138379) (by norm_num)
theorem B2624405 : Blo 1748575 2624405 := bbase (se 6 (by rfl) ⟨61509, by rfl⟩ : syracuseStep 2624405 = 123019) (by norm_num)
theorem B3935141 : Blo 1748575 3935141 := bbase (se 4 (by rfl) ⟨368919, by rfl⟩ : syracuseStep 3935141 = 737839) (by norm_num)
theorem B2624429 : Blo 1748575 2624429 := bbase (se 3 (by rfl) ⟨492080, by rfl⟩ : syracuseStep 2624429 = 984161) (by norm_num)
theorem B1969069 : Blo 1748575 1969069 := bbase (se 3 (by rfl) ⟨369200, by rfl⟩ : syracuseStep 1969069 = 738401) (by norm_num)
theorem B2624453 : Blo 1748575 2624453 := bbase (se 4 (by rfl) ⟨246042, by rfl⟩ : syracuseStep 2624453 = 492085) (by norm_num)
theorem B1969105 : Blo 1748575 1969105 := bbase (se 2 (by rfl) ⟨738414, by rfl⟩ : syracuseStep 1969105 = 1476829) (by norm_num)
theorem B2624477 : Blo 1748575 2624477 := bbase (se 3 (by rfl) ⟨492089, by rfl⟩ : syracuseStep 2624477 = 984179) (by norm_num)
theorem B3935213 : Blo 1748575 3935213 := bbase (se 3 (by rfl) ⟨737852, by rfl⟩ : syracuseStep 3935213 = 1475705) (by norm_num)
theorem B2952173 : Blo 1748575 2952173 := bbase (se 3 (by rfl) ⟨553532, by rfl⟩ : syracuseStep 2952173 = 1107065) (by norm_num)
theorem B2624501 : Blo 1748575 2624501 := bbase (se 5 (by rfl) ⟨123023, by rfl⟩ : syracuseStep 2624501 = 246047) (by norm_num)
theorem B1969141 : Blo 1748575 1969141 := bbase (se 5 (by rfl) ⟨92303, by rfl⟩ : syracuseStep 1969141 = 184607) (by norm_num)
theorem B2624525 : Blo 1748575 2624525 := bbase (se 3 (by rfl) ⟨492098, by rfl⟩ : syracuseStep 2624525 = 984197) (by norm_num)
theorem B9964565 : Blo 1748575 9964565 := bbase (se 6 (by rfl) ⟨233544, by rfl⟩ : syracuseStep 9964565 = 467089) (by norm_num)
theorem B8858645 : Blo 1748575 8858645 := bbase (se 6 (by rfl) ⟨207624, by rfl⟩ : syracuseStep 8858645 = 415249) (by norm_num)
theorem B1969177 : Blo 1748575 1969177 := bbase (se 2 (by rfl) ⟨738441, by rfl⟩ : syracuseStep 1969177 = 1476883) (by norm_num)
theorem B2624549 : Blo 1748575 2624549 := bbase (se 4 (by rfl) ⟨246051, by rfl⟩ : syracuseStep 2624549 = 492103) (by norm_num)
theorem B3935285 : Blo 1748575 3935285 := bbase (se 5 (by rfl) ⟨184466, by rfl⟩ : syracuseStep 3935285 = 368933) (by norm_num)
theorem B2214965 : Blo 1748575 2214965 := bbase (se 5 (by rfl) ⟨103826, by rfl⟩ : syracuseStep 2214965 = 207653) (by norm_num)
theorem B2624573 : Blo 1748575 2624573 := bbase (se 3 (by rfl) ⟨492107, by rfl⟩ : syracuseStep 2624573 = 984215) (by norm_num)
theorem B1969213 : Blo 1748575 1969213 := bbase (se 3 (by rfl) ⟨369227, by rfl⟩ : syracuseStep 1969213 = 738455) (by norm_num)
theorem B2624597 : Blo 1748575 2624597 := bbase (se 8 (by rfl) ⟨15378, by rfl⟩ : syracuseStep 2624597 = 30757) (by norm_num)
theorem B1969249 : Blo 1748575 1969249 := bbase (se 2 (by rfl) ⟨738468, by rfl⟩ : syracuseStep 1969249 = 1476937) (by norm_num)
theorem B2952301 : Blo 1748575 2952301 := bbase (se 3 (by rfl) ⟨553556, by rfl⟩ : syracuseStep 2952301 = 1107113) (by norm_num)
theorem B2624621 : Blo 1748575 2624621 := bbase (se 3 (by rfl) ⟨492116, by rfl⟩ : syracuseStep 2624621 = 984233) (by norm_num)
theorem B2215021 : Blo 1748575 2215021 := bbase (se 3 (by rfl) ⟨415316, by rfl⟩ : syracuseStep 2215021 = 830633) (by norm_num)
theorem B15961205 : Blo 1748575 15961205 := bbase (se 5 (by rfl) ⟨748181, by rfl⟩ : syracuseStep 15961205 = 1496363) (by norm_num)
theorem B3935357 : Blo 1748575 3935357 := bbase (se 3 (by rfl) ⟨737879, by rfl⟩ : syracuseStep 3935357 = 1475759) (by norm_num)
theorem B2624645 : Blo 1748575 2624645 := bbase (se 4 (by rfl) ⟨246060, by rfl⟩ : syracuseStep 2624645 = 492121) (by norm_num)
theorem B1969285 : Blo 1748575 1969285 := bbase (se 4 (by rfl) ⟨184620, by rfl⟩ : syracuseStep 1969285 = 369241) (by norm_num)
theorem B1772689 : Blo 1748575 1772689 := bbase (se 2 (by rfl) ⟨664758, by rfl⟩ : syracuseStep 1772689 = 1329517) (by norm_num)
theorem B2624669 : Blo 1748575 2624669 := bbase (se 3 (by rfl) ⟨492125, by rfl⟩ : syracuseStep 2624669 = 984251) (by norm_num)
theorem B1969321 : Blo 1748575 1969321 := bbase (se 2 (by rfl) ⟨738495, by rfl⟩ : syracuseStep 1969321 = 1476991) (by norm_num)
theorem B4426933 : Blo 1748575 4426933 := bbase (se 5 (by rfl) ⟨207512, by rfl⟩ : syracuseStep 4426933 = 415025) (by norm_num)
theorem B3321013 : Blo 1748575 3321013 := bbase (se 5 (by rfl) ⟨155672, by rfl⟩ : syracuseStep 3321013 = 311345) (by norm_num)
theorem B2624693 : Blo 1748575 2624693 := bbase (se 5 (by rfl) ⟨123032, by rfl⟩ : syracuseStep 2624693 = 246065) (by norm_num)
theorem B3935429 : Blo 1748575 3935429 := bbase (se 4 (by rfl) ⟨368946, by rfl⟩ : syracuseStep 3935429 = 737893) (by norm_num)
theorem B2952389 : Blo 1748575 2952389 := bbase (se 4 (by rfl) ⟨276786, by rfl⟩ : syracuseStep 2952389 = 553573) (by norm_num)
theorem B2624717 : Blo 1748575 2624717 := bbase (se 3 (by rfl) ⟨492134, by rfl⟩ : syracuseStep 2624717 = 984269) (by norm_num)
theorem B2215117 : Blo 1748575 2215117 := bbase (se 3 (by rfl) ⟨415334, by rfl⟩ : syracuseStep 2215117 = 830669) (by norm_num)
theorem B1969357 : Blo 1748575 1969357 := bbase (se 3 (by rfl) ⟨369254, by rfl⟩ : syracuseStep 1969357 = 738509) (by norm_num)
theorem B2624741 : Blo 1748575 2624741 := bbase (se 4 (by rfl) ⟨246069, by rfl⟩ : syracuseStep 2624741 = 492139) (by norm_num)
theorem B4984037 : Blo 1748575 4984037 := bbase (se 4 (by rfl) ⟨467253, by rfl⟩ : syracuseStep 4984037 = 934507) (by norm_num)
theorem B1969393 : Blo 1748575 1969393 := bbase (se 2 (by rfl) ⟨738522, by rfl⟩ : syracuseStep 1969393 = 1477045) (by norm_num)
theorem B2624765 : Blo 1748575 2624765 := bbase (se 3 (by rfl) ⟨492143, by rfl⟩ : syracuseStep 2624765 = 984287) (by norm_num)
theorem B3935501 : Blo 1748575 3935501 := bbase (se 3 (by rfl) ⟨737906, by rfl⟩ : syracuseStep 3935501 = 1475813) (by norm_num)
theorem B2624789 : Blo 1748575 2624789 := bbase (se 6 (by rfl) ⟨61518, by rfl⟩ : syracuseStep 2624789 = 123037) (by norm_num)
theorem B5901605 : Blo 1748575 5901605 := bbase (se 4 (by rfl) ⟨553275, by rfl⟩ : syracuseStep 5901605 = 1106551) (by norm_num)
theorem B4427045 : Blo 1748575 4427045 := bbase (se 4 (by rfl) ⟨415035, by rfl⟩ : syracuseStep 4427045 = 830071) (by norm_num)
theorem B2624813 : Blo 1748575 2624813 := bbase (se 3 (by rfl) ⟨492152, by rfl⟩ : syracuseStep 2624813 = 984305) (by norm_num)
theorem B3321157 : Blo 1748575 3321157 := bbase (se 4 (by rfl) ⟨311358, by rfl⟩ : syracuseStep 3321157 = 622717) (by norm_num)
theorem B2952517 : Blo 1748575 2952517 := bbase (se 4 (by rfl) ⟨276798, by rfl⟩ : syracuseStep 2952517 = 553597) (by norm_num)
theorem B2624837 : Blo 1748575 2624837 := bbase (se 4 (by rfl) ⟨246078, by rfl⟩ : syracuseStep 2624837 = 492157) (by norm_num)
theorem B3935573 : Blo 1748575 3935573 := bbase (se 11 (by rfl) ⟨2882, by rfl⟩ : syracuseStep 3935573 = 5765) (by norm_num)
theorem B2624861 : Blo 1748575 2624861 := bbase (se 3 (by rfl) ⟨492161, by rfl⟩ : syracuseStep 2624861 = 984323) (by norm_num)
theorem B2624885 : Blo 1748575 2624885 := bbase (se 5 (by rfl) ⟨123041, by rfl⟩ : syracuseStep 2624885 = 246083) (by norm_num)
theorem B2215289 : Blo 1748575 2215289 := bbase (se 2 (by rfl) ⟨830733, by rfl⟩ : syracuseStep 2215289 = 1661467) (by norm_num)
theorem B2624909 : Blo 1748575 2624909 := bbase (se 3 (by rfl) ⟨492170, by rfl⟩ : syracuseStep 2624909 = 984341) (by norm_num)
theorem B3935645 : Blo 1748575 3935645 := bbase (se 3 (by rfl) ⟨737933, by rfl⟩ : syracuseStep 3935645 = 1475867) (by norm_num)
theorem B2952605 : Blo 1748575 2952605 := bbase (se 3 (by rfl) ⟨553613, by rfl⟩ : syracuseStep 2952605 = 1107227) (by norm_num)
theorem B2624933 : Blo 1748575 2624933 := bbase (se 4 (by rfl) ⟨246087, by rfl⟩ : syracuseStep 2624933 = 492175) (by norm_num)
theorem B2215345 : Blo 1748575 2215345 := bbase (se 2 (by rfl) ⟨830754, by rfl⟩ : syracuseStep 2215345 = 1661509) (by norm_num)
theorem B2624957 : Blo 1748575 2624957 := bbase (se 3 (by rfl) ⟨492179, by rfl⟩ : syracuseStep 2624957 = 984359) (by norm_num)
theorem B19926485 : Blo 1748575 19926485 := bbase (se 7 (by rfl) ⟨233513, by rfl⟩ : syracuseStep 19926485 = 467027) (by norm_num)
theorem B2624981 : Blo 1748575 2624981 := bbase (se 7 (by rfl) ⟨30761, by rfl⟩ : syracuseStep 2624981 = 61523) (by norm_num)
theorem B4427237 : Blo 1748575 4427237 := bbase (se 4 (by rfl) ⟨415053, by rfl⟩ : syracuseStep 4427237 = 830107) (by norm_num)
theorem B3935717 : Blo 1748575 3935717 := bbase (se 4 (by rfl) ⟨368973, by rfl⟩ : syracuseStep 3935717 = 737947) (by norm_num)
theorem B3321317 : Blo 1748575 3321317 := bbase (se 4 (by rfl) ⟨311373, by rfl⟩ : syracuseStep 3321317 = 622747) (by norm_num)
theorem B2625005 : Blo 1748575 2625005 := bbase (se 3 (by rfl) ⟨492188, by rfl⟩ : syracuseStep 2625005 = 984377) (by norm_num)
theorem B2625029 : Blo 1748575 2625029 := bbase (se 4 (by rfl) ⟨246096, by rfl⟩ : syracuseStep 2625029 = 492193) (by norm_num)
theorem B2215441 : Blo 1748575 2215441 := bbase (se 2 (by rfl) ⟨830790, by rfl⟩ : syracuseStep 2215441 = 1661581) (by norm_num)
theorem B2952733 : Blo 1748575 2952733 := bbase (se 3 (by rfl) ⟨553637, by rfl⟩ : syracuseStep 2952733 = 1107275) (by norm_num)
theorem B2625053 : Blo 1748575 2625053 := bbase (se 3 (by rfl) ⟨492197, by rfl⟩ : syracuseStep 2625053 = 984395) (by norm_num)
theorem B3935789 : Blo 1748575 3935789 := bbase (se 3 (by rfl) ⟨737960, by rfl⟩ : syracuseStep 3935789 = 1475921) (by norm_num)
theorem B2625077 : Blo 1748575 2625077 := bbase (se 5 (by rfl) ⟨123050, by rfl⟩ : syracuseStep 2625077 = 246101) (by norm_num)
theorem B2993717 : Blo 1748575 2993717 := bbase (se 5 (by rfl) ⟨140330, by rfl⟩ : syracuseStep 2993717 = 280661) (by norm_num)
theorem B2625101 : Blo 1748575 2625101 := bbase (se 3 (by rfl) ⟨492206, by rfl⟩ : syracuseStep 2625101 = 984413) (by norm_num)
theorem B2625125 : Blo 1748575 2625125 := bbase (se 4 (by rfl) ⟨246105, by rfl⟩ : syracuseStep 2625125 = 492211) (by norm_num)
theorem B2993773 : Blo 1748575 2993773 := bbase (se 3 (by rfl) ⟨561332, by rfl⟩ : syracuseStep 2993773 = 1122665) (by norm_num)
theorem B3935861 : Blo 1748575 3935861 := bbase (se 5 (by rfl) ⟨184493, by rfl⟩ : syracuseStep 3935861 = 368987) (by norm_num)
theorem B3321461 : Blo 1748575 3321461 := bbase (se 5 (by rfl) ⟨155693, by rfl⟩ : syracuseStep 3321461 = 311387) (by norm_num)
theorem B2952821 : Blo 1748575 2952821 := bbase (se 5 (by rfl) ⟨138413, by rfl⟩ : syracuseStep 2952821 = 276827) (by norm_num)
theorem B2625149 : Blo 1748575 2625149 := bbase (se 3 (by rfl) ⟨492215, by rfl⟩ : syracuseStep 2625149 = 984431) (by norm_num)
theorem B3239573 : Blo 1748575 3239573 := bbase (se 6 (by rfl) ⟨75927, by rfl⟩ : syracuseStep 3239573 = 151855) (by norm_num)
theorem B2625173 : Blo 1748575 2625173 := bbase (se 6 (by rfl) ⟨61527, by rfl⟩ : syracuseStep 2625173 = 123055) (by norm_num)
theorem B2625197 : Blo 1748575 2625197 := bbase (se 3 (by rfl) ⟨492224, by rfl⟩ : syracuseStep 2625197 = 984449) (by norm_num)
theorem B3935933 : Blo 1748575 3935933 := bbase (se 3 (by rfl) ⟨737987, by rfl⟩ : syracuseStep 3935933 = 1475975) (by norm_num)
theorem B2625221 : Blo 1748575 2625221 := bbase (se 4 (by rfl) ⟨246114, by rfl⟩ : syracuseStep 2625221 = 492229) (by norm_num)
theorem B5902037 : Blo 1748575 5902037 := bbase (se 7 (by rfl) ⟨69164, by rfl⟩ : syracuseStep 5902037 = 138329) (by norm_num)
theorem B2625245 : Blo 1748575 2625245 := bbase (se 3 (by rfl) ⟨492233, by rfl⟩ : syracuseStep 2625245 = 984467) (by norm_num)
theorem B3837685 : Blo 1748575 3837685 := bbase (se 5 (by rfl) ⟨179891, by rfl⟩ : syracuseStep 3837685 = 359783) (by norm_num)
theorem B2952949 : Blo 1748575 2952949 := bbase (se 5 (by rfl) ⟨138419, by rfl⟩ : syracuseStep 2952949 = 276839) (by norm_num)
theorem B2625269 : Blo 1748575 2625269 := bbase (se 5 (by rfl) ⟨123059, by rfl⟩ : syracuseStep 2625269 = 246119) (by norm_num)
theorem B3936005 : Blo 1748575 3936005 := bbase (se 4 (by rfl) ⟨369000, by rfl⟩ : syracuseStep 3936005 = 738001) (by norm_num)
theorem B2625293 : Blo 1748575 2625293 := bbase (se 3 (by rfl) ⟨492242, by rfl⟩ : syracuseStep 2625293 = 984485) (by norm_num)
theorem B2625317 : Blo 1748575 2625317 := bbase (se 4 (by rfl) ⟨246123, by rfl⟩ : syracuseStep 2625317 = 492247) (by norm_num)
theorem B4427581 : Blo 1748575 4427581 := bbase (se 3 (by rfl) ⟨830171, by rfl⟩ : syracuseStep 4427581 = 1660343) (by norm_num)
theorem B2625341 : Blo 1748575 2625341 := bbase (se 3 (by rfl) ⟨492251, by rfl⟩ : syracuseStep 2625341 = 984503) (by norm_num)
theorem B3936077 : Blo 1748575 3936077 := bbase (se 3 (by rfl) ⟨738014, by rfl⟩ : syracuseStep 3936077 = 1476029) (by norm_num)
theorem B2953037 : Blo 1748575 2953037 := bbase (se 3 (by rfl) ⟨553694, by rfl⟩ : syracuseStep 2953037 = 1107389) (by norm_num)
theorem B2625365 : Blo 1748575 2625365 := bbase (se 9 (by rfl) ⟨7691, by rfl⟩ : syracuseStep 2625365 = 15383) (by norm_num)
theorem B4730725 : Blo 1748575 4730725 := bbase (se 4 (by rfl) ⟨443505, by rfl⟩ : syracuseStep 4730725 = 887011) (by norm_num)
theorem B2625389 : Blo 1748575 2625389 := bbase (se 3 (by rfl) ⟨492260, by rfl⟩ : syracuseStep 2625389 = 984521) (by norm_num)
theorem B2625413 : Blo 1748575 2625413 := bbase (se 4 (by rfl) ⟨246132, by rfl⟩ : syracuseStep 2625413 = 492265) (by norm_num)
theorem B3936149 : Blo 1748575 3936149 := bbase (se 6 (by rfl) ⟨92253, by rfl⟩ : syracuseStep 3936149 = 184507) (by norm_num)
theorem B3321749 : Blo 1748575 3321749 := bbase (se 6 (by rfl) ⟨77853, by rfl⟩ : syracuseStep 3321749 = 155707) (by norm_num)
theorem B2625437 : Blo 1748575 2625437 := bbase (se 3 (by rfl) ⟨492269, by rfl⟩ : syracuseStep 2625437 = 984539) (by norm_num)
theorem B4427693 : Blo 1748575 4427693 := bbase (se 3 (by rfl) ⟨830192, by rfl⟩ : syracuseStep 4427693 = 1660385) (by norm_num)
theorem B7983029 : Blo 1748575 7983029 := bbase (se 5 (by rfl) ⟨374204, by rfl⟩ : syracuseStep 7983029 = 748409) (by norm_num)
theorem B2625461 : Blo 1748575 2625461 := bbase (se 5 (by rfl) ⟨123068, by rfl⟩ : syracuseStep 2625461 = 246137) (by norm_num)
theorem B2953165 : Blo 1748575 2953165 := bbase (se 3 (by rfl) ⟨553718, by rfl⟩ : syracuseStep 2953165 = 1107437) (by norm_num)
theorem B2625485 : Blo 1748575 2625485 := bbase (se 3 (by rfl) ⟨492278, by rfl⟩ : syracuseStep 2625485 = 984557) (by norm_num)
theorem B3936221 : Blo 1748575 3936221 := bbase (se 3 (by rfl) ⟨738041, by rfl⟩ : syracuseStep 3936221 = 1476083) (by norm_num)
theorem B2625509 : Blo 1748575 2625509 := bbase (se 4 (by rfl) ⟨246141, by rfl⟩ : syracuseStep 2625509 = 492283) (by norm_num)
theorem B2625533 : Blo 1748575 2625533 := bbase (se 3 (by rfl) ⟨492287, by rfl⟩ : syracuseStep 2625533 = 984575) (by norm_num)
theorem B2625557 : Blo 1748575 2625557 := bbase (se 6 (by rfl) ⟨61536, by rfl⟩ : syracuseStep 2625557 = 123073) (by norm_num)
theorem B3936293 : Blo 1748575 3936293 := bbase (se 4 (by rfl) ⟨369027, by rfl⟩ : syracuseStep 3936293 = 738055) (by norm_num)
theorem B2953253 : Blo 1748575 2953253 := bbase (se 4 (by rfl) ⟨276867, by rfl⟩ : syracuseStep 2953253 = 553735) (by norm_num)
theorem B3321901 : Blo 1748575 3321901 := bbase (se 3 (by rfl) ⟨622856, by rfl⟩ : syracuseStep 3321901 = 1245713) (by norm_num)
theorem B2625581 : Blo 1748575 2625581 := bbase (se 3 (by rfl) ⟨492296, by rfl⟩ : syracuseStep 2625581 = 984593) (by norm_num)
theorem B2625605 : Blo 1748575 2625605 := bbase (se 4 (by rfl) ⟨246150, by rfl⟩ : syracuseStep 2625605 = 492301) (by norm_num)
theorem B2625629 : Blo 1748575 2625629 := bbase (se 3 (by rfl) ⟨492305, by rfl⟩ : syracuseStep 2625629 = 984611) (by norm_num)
theorem B8982629 : Blo 1748575 8982629 := bbase (se 4 (by rfl) ⟨842121, by rfl⟩ : syracuseStep 8982629 = 1684243) (by norm_num)
theorem B4427885 : Blo 1748575 4427885 := bbase (se 3 (by rfl) ⟨830228, by rfl⟩ : syracuseStep 4427885 = 1660457) (by norm_num)
theorem B3936365 : Blo 1748575 3936365 := bbase (se 3 (by rfl) ⟨738068, by rfl⟩ : syracuseStep 3936365 = 1476137) (by norm_num)
theorem B2625653 : Blo 1748575 2625653 := bbase (se 5 (by rfl) ⟨123077, by rfl⟩ : syracuseStep 2625653 = 246155) (by norm_num)
theorem B5902469 : Blo 1748575 5902469 := bbase (se 4 (by rfl) ⟨553356, by rfl⟩ : syracuseStep 5902469 = 1106713) (by norm_num)
theorem B2625677 : Blo 1748575 2625677 := bbase (se 3 (by rfl) ⟨492314, by rfl⟩ : syracuseStep 2625677 = 984629) (by norm_num)
theorem B2953381 : Blo 1748575 2953381 := bbase (se 4 (by rfl) ⟨276879, by rfl⟩ : syracuseStep 2953381 = 553759) (by norm_num)
theorem B2625701 : Blo 1748575 2625701 := bbase (se 4 (by rfl) ⟨246159, by rfl⟩ : syracuseStep 2625701 = 492319) (by norm_num)
theorem B3936437 : Blo 1748575 3936437 := bbase (se 5 (by rfl) ⟨184520, by rfl⟩ : syracuseStep 3936437 = 369041) (by norm_num)
theorem B5607605 : Blo 1748575 5607605 := bbase (se 5 (by rfl) ⟨262856, by rfl⟩ : syracuseStep 5607605 = 525713) (by norm_num)
theorem B2625725 : Blo 1748575 2625725 := bbase (se 3 (by rfl) ⟨492323, by rfl⟩ : syracuseStep 2625725 = 984647) (by norm_num)
theorem B2625749 : Blo 1748575 2625749 := bbase (se 7 (by rfl) ⟨30770, by rfl⟩ : syracuseStep 2625749 = 61541) (by norm_num)
theorem B2625773 : Blo 1748575 2625773 := bbase (se 3 (by rfl) ⟨492332, by rfl⟩ : syracuseStep 2625773 = 984665) (by norm_num)
theorem B3936509 : Blo 1748575 3936509 := bbase (se 3 (by rfl) ⟨738095, by rfl⟩ : syracuseStep 3936509 = 1476191) (by norm_num)
theorem B2953469 : Blo 1748575 2953469 := bbase (se 3 (by rfl) ⟨553775, by rfl⟩ : syracuseStep 2953469 = 1107551) (by norm_num)
theorem B2625797 : Blo 1748575 2625797 := bbase (se 4 (by rfl) ⟨246168, by rfl⟩ : syracuseStep 2625797 = 492337) (by norm_num)
theorem B2625821 : Blo 1748575 2625821 := bbase (se 3 (by rfl) ⟨492341, by rfl⟩ : syracuseStep 2625821 = 984683) (by norm_num)
theorem B8859941 : Blo 1748575 8859941 := bbase (se 4 (by rfl) ⟨830619, by rfl⟩ : syracuseStep 8859941 = 1661239) (by norm_num)
theorem B2625845 : Blo 1748575 2625845 := bbase (se 5 (by rfl) ⟨123086, by rfl⟩ : syracuseStep 2625845 = 246173) (by norm_num)
theorem B3936581 : Blo 1748575 3936581 := bbase (se 4 (by rfl) ⟨369054, by rfl⟩ : syracuseStep 3936581 = 738109) (by norm_num)
theorem B3322205 : Blo 1748575 3322205 := bbase (se 3 (by rfl) ⟨622913, by rfl⟩ : syracuseStep 3322205 = 1245827) (by norm_num)
theorem B2953597 : Blo 1748575 2953597 := bbase (se 3 (by rfl) ⟨553799, by rfl⟩ : syracuseStep 2953597 = 1107599) (by norm_num)
theorem B3936653 : Blo 1748575 3936653 := bbase (se 3 (by rfl) ⟨738122, by rfl⟩ : syracuseStep 3936653 = 1476245) (by norm_num)
theorem B1798573 : Blo 1748575 1798573 := bbase (se 3 (by rfl) ⟨337232, by rfl⟩ : syracuseStep 1798573 = 674465) (by norm_num)
theorem B4428229 : Blo 1748575 4428229 := bbase (se 4 (by rfl) ⟨415146, by rfl⟩ : syracuseStep 4428229 = 830293) (by norm_num)
theorem B3936725 : Blo 1748575 3936725 := bbase (se 7 (by rfl) ⟨46133, by rfl⟩ : syracuseStep 3936725 = 92267) (by norm_num)
theorem B2953685 : Blo 1748575 2953685 := bbase (se 7 (by rfl) ⟨34613, by rfl⟩ : syracuseStep 2953685 = 69227) (by norm_num)
theorem B3936797 : Blo 1748575 3936797 := bbase (se 3 (by rfl) ⟨738149, by rfl⟩ : syracuseStep 3936797 = 1476299) (by norm_num)
theorem B5902901 : Blo 1748575 5902901 := bbase (se 5 (by rfl) ⟨276698, by rfl⟩ : syracuseStep 5902901 = 553397) (by norm_num)
theorem B4428341 : Blo 1748575 4428341 := bbase (se 5 (by rfl) ⟨207578, by rfl⟩ : syracuseStep 4428341 = 415157) (by norm_num)
theorem B1995337 : Blo 1748575 1995337 := bbase (se 2 (by rfl) ⟨748251, by rfl⟩ : syracuseStep 1995337 = 1496503) (by norm_num)
theorem B2953813 : Blo 1748575 2953813 := bbase (se 8 (by rfl) ⟨17307, by rfl⟩ : syracuseStep 2953813 = 34615) (by norm_num)
theorem B3936869 : Blo 1748575 3936869 := bbase (se 4 (by rfl) ⟨369081, by rfl⟩ : syracuseStep 3936869 = 738163) (by norm_num)
theorem B3936941 : Blo 1748575 3936941 := bbase (se 3 (by rfl) ⟨738176, by rfl⟩ : syracuseStep 3936941 = 1476353) (by norm_num)
theorem B2953901 : Blo 1748575 2953901 := bbase (se 3 (by rfl) ⟨553856, by rfl⟩ : syracuseStep 2953901 = 1107713) (by norm_num)
theorem B8852165 : Blo 1748575 8852165 := bbase (se 4 (by rfl) ⟨829890, by rfl⟩ : syracuseStep 8852165 = 1659781) (by norm_num)
theorem B6640325 : Blo 1748575 6640325 := bbase (se 4 (by rfl) ⟨622530, by rfl⟩ : syracuseStep 6640325 = 1245061) (by norm_num)
theorem B4428533 : Blo 1748575 4428533 := bbase (se 5 (by rfl) ⟨207587, by rfl⟩ : syracuseStep 4428533 = 415175) (by norm_num)
theorem B3937013 : Blo 1748575 3937013 := bbase (se 5 (by rfl) ⟨184547, by rfl⟩ : syracuseStep 3937013 = 369095) (by norm_num)
theorem B2954029 : Blo 1748575 2954029 := bbase (se 3 (by rfl) ⟨553880, by rfl⟩ : syracuseStep 2954029 = 1107761) (by norm_num)
theorem B3937085 : Blo 1748575 3937085 := bbase (se 3 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 3937085 = 1476407) (by norm_num)
theorem B2102117 : Blo 1748575 2102117 := bbase (se 4 (by rfl) ⟨197073, by rfl⟩ : syracuseStep 2102117 = 394147) (by norm_num)
theorem B3937157 : Blo 1748575 3937157 := bbase (se 4 (by rfl) ⟨369108, by rfl⟩ : syracuseStep 3937157 = 738217) (by norm_num)
theorem B34075541 : Blo 1748575 34075541 := bbase (se 6 (by rfl) ⟨798645, by rfl⟩ : syracuseStep 34075541 = 1597291) (by norm_num)
theorem B3937229 : Blo 1748575 3937229 := bbase (se 3 (by rfl) ⟨738230, by rfl⟩ : syracuseStep 3937229 = 1476461) (by norm_num)
theorem B6640613 : Blo 1748575 6640613 := bbase (se 4 (by rfl) ⟨622557, by rfl⟩ : syracuseStep 6640613 = 1245115) (by norm_num)
theorem B5903333 : Blo 1748575 5903333 := bbase (se 4 (by rfl) ⟨553437, by rfl⟩ : syracuseStep 5903333 = 1106875) (by norm_num)
theorem B3937301 : Blo 1748575 3937301 := bbase (se 6 (by rfl) ⟨92280, by rfl⟩ : syracuseStep 3937301 = 184561) (by norm_num)
theorem B7476245 : Blo 1748575 7476245 := bbase (se 6 (by rfl) ⟨175224, by rfl⟩ : syracuseStep 7476245 = 350449) (by norm_num)
theorem B4428877 : Blo 1748575 4428877 := bbase (se 3 (by rfl) ⟨830414, by rfl⟩ : syracuseStep 4428877 = 1660829) (by norm_num)
theorem B3322957 : Blo 1748575 3322957 := bbase (se 3 (by rfl) ⟨623054, by rfl⟩ : syracuseStep 3322957 = 1246109) (by norm_num)
theorem B3937373 : Blo 1748575 3937373 := bbase (se 3 (by rfl) ⟨738257, by rfl⟩ : syracuseStep 3937373 = 1476515) (by norm_num)
theorem B17036405 : Blo 1748575 17036405 := bbase (se 5 (by rfl) ⟨798581, by rfl⟩ : syracuseStep 17036405 = 1597163) (by norm_num)
theorem B3937445 : Blo 1748575 3937445 := bbase (se 4 (by rfl) ⟨369135, by rfl⟩ : syracuseStep 3937445 = 738271) (by norm_num)
theorem B3151021 : Blo 1748575 3151021 := bbase (se 3 (by rfl) ⟨590816, by rfl⟩ : syracuseStep 3151021 = 1181633) (by norm_num)
theorem B2102449 : Blo 1748575 2102449 := bbase (se 2 (by rfl) ⟨788418, by rfl⟩ : syracuseStep 2102449 = 1576837) (by norm_num)
theorem B1995953 : Blo 1748575 1995953 := bbase (se 2 (by rfl) ⟨748482, by rfl⟩ : syracuseStep 1995953 = 1496965) (by norm_num)
theorem B4428989 : Blo 1748575 4428989 := bbase (se 3 (by rfl) ⟨830435, by rfl⟩ : syracuseStep 4428989 = 1660871) (by norm_num)
theorem B6304981 : Blo 1748575 6304981 := bbase (se 7 (by rfl) ⟨73886, by rfl⟩ : syracuseStep 6304981 = 147773) (by norm_num)
theorem B3323101 : Blo 1748575 3323101 := bbase (se 3 (by rfl) ⟨623081, by rfl⟩ : syracuseStep 3323101 = 1246163) (by norm_num)
theorem B3937517 : Blo 1748575 3937517 := bbase (se 3 (by rfl) ⟨738284, by rfl⟩ : syracuseStep 3937517 = 1476569) (by norm_num)
theorem B3937589 : Blo 1748575 3937589 := bbase (se 5 (by rfl) ⟨184574, by rfl⟩ : syracuseStep 3937589 = 369149) (by norm_num)
theorem B7476533 : Blo 1748575 7476533 := bbase (se 5 (by rfl) ⟨350462, by rfl⟩ : syracuseStep 7476533 = 700925) (by norm_num)
theorem B2102593 : Blo 1748575 2102593 := bbase (se 2 (by rfl) ⟨788472, by rfl⟩ : syracuseStep 2102593 = 1576945) (by norm_num)
theorem B2364757 : Blo 1748575 2364757 := bbase (se 14 (by rfl) ⟨216, by rfl⟩ : syracuseStep 2364757 = 433) (by norm_num)
theorem B4429181 : Blo 1748575 4429181 := bbase (se 3 (by rfl) ⟨830471, by rfl⟩ : syracuseStep 4429181 = 1660943) (by norm_num)
theorem B3937661 : Blo 1748575 3937661 := bbase (se 3 (by rfl) ⟨738311, by rfl⟩ : syracuseStep 3937661 = 1476623) (by norm_num)
theorem B3323261 : Blo 1748575 3323261 := bbase (se 3 (by rfl) ⟨623111, by rfl⟩ : syracuseStep 3323261 = 1246223) (by norm_num)
theorem B3151237 : Blo 1748575 3151237 := bbase (se 4 (by rfl) ⟨295428, by rfl⟩ : syracuseStep 3151237 = 590857) (by norm_num)
theorem B5903765 : Blo 1748575 5903765 := bbase (se 6 (by rfl) ⟨138369, by rfl⟩ : syracuseStep 5903765 = 276739) (by norm_num)
theorem B14382517 : Blo 1748575 14382517 := bbase (se 5 (by rfl) ⟨674180, by rfl⟩ : syracuseStep 14382517 = 1348361) (by norm_num)
theorem B1996213 : Blo 1748575 1996213 := bbase (se 5 (by rfl) ⟨93572, by rfl⟩ : syracuseStep 1996213 = 187145) (by norm_num)
theorem B3937733 : Blo 1748575 3937733 := bbase (se 4 (by rfl) ⟨369162, by rfl⟩ : syracuseStep 3937733 = 738325) (by norm_num)
theorem B3937805 : Blo 1748575 3937805 := bbase (se 3 (by rfl) ⟨738338, by rfl⟩ : syracuseStep 3937805 = 1476677) (by norm_num)
theorem B8861237 : Blo 1748575 8861237 := bbase (se 5 (by rfl) ⟨415370, by rfl⟩ : syracuseStep 8861237 = 830741) (by norm_num)
theorem B3937877 : Blo 1748575 3937877 := bbase (se 8 (by rfl) ⟨23073, by rfl⟩ : syracuseStep 3937877 = 46147) (by norm_num)
theorem B40416853 : Blo 1748575 40416853 := bbase (se 8 (by rfl) ⟨236817, by rfl⟩ : syracuseStep 40416853 = 473635) (by norm_num)
theorem B3642989 : Blo 1748575 3642989 := bbase (se 3 (by rfl) ⟨683060, by rfl⟩ : syracuseStep 3642989 = 1366121) (by norm_num)
theorem B3937949 : Blo 1748575 3937949 := bbase (se 3 (by rfl) ⟨738365, by rfl⟩ : syracuseStep 3937949 = 1476731) (by norm_num)
theorem B4429525 : Blo 1748575 4429525 := bbase (se 7 (by rfl) ⟨51908, by rfl⟩ : syracuseStep 4429525 = 103817) (by norm_num)
theorem B3938021 : Blo 1748575 3938021 := bbase (se 4 (by rfl) ⟨369189, by rfl⟩ : syracuseStep 3938021 = 738379) (by norm_num)
theorem B3938093 : Blo 1748575 3938093 := bbase (se 3 (by rfl) ⟨738392, by rfl⟩ : syracuseStep 3938093 = 1476785) (by norm_num)
theorem B5904197 : Blo 1748575 5904197 := bbase (se 4 (by rfl) ⟨553518, by rfl⟩ : syracuseStep 5904197 = 1107037) (by norm_num)
theorem B4429637 : Blo 1748575 4429637 := bbase (se 4 (by rfl) ⟨415278, by rfl⟩ : syracuseStep 4429637 = 830557) (by norm_num)
theorem B3938165 : Blo 1748575 3938165 := bbase (se 5 (by rfl) ⟨184601, by rfl⟩ : syracuseStep 3938165 = 369203) (by norm_num)
theorem B3938237 : Blo 1748575 3938237 := bbase (se 3 (by rfl) ⟨738419, by rfl⟩ : syracuseStep 3938237 = 1476839) (by norm_num)
theorem B8853461 : Blo 1748575 8853461 := bbase (se 7 (by rfl) ⟨103751, by rfl⟩ : syracuseStep 8853461 = 207503) (by norm_num)
theorem B25221077 : Blo 1748575 25221077 := bbase (se 7 (by rfl) ⟨295559, by rfl⟩ : syracuseStep 25221077 = 591119) (by norm_num)
theorem B8402933 : Blo 1748575 8402933 := bbase (se 5 (by rfl) ⟨393887, by rfl⟩ : syracuseStep 8402933 = 787775) (by norm_num)
theorem B3545093 : Blo 1748575 3545093 := bbase (se 4 (by rfl) ⟨332352, by rfl⟩ : syracuseStep 3545093 = 664705) (by norm_num)
theorem B4429829 : Blo 1748575 4429829 := bbase (se 4 (by rfl) ⟨415296, by rfl⟩ : syracuseStep 4429829 = 830593) (by norm_num)
theorem B5683205 : Blo 1748575 5683205 := bbase (se 4 (by rfl) ⟨532800, by rfl⟩ : syracuseStep 5683205 = 1065601) (by norm_num)
theorem B8411141 : Blo 1748575 8411141 := bbase (se 4 (by rfl) ⟨788544, by rfl⟩ : syracuseStep 8411141 = 1577089) (by norm_num)
theorem B3938309 : Blo 1748575 3938309 := bbase (se 4 (by rfl) ⟨369216, by rfl⟩ : syracuseStep 3938309 = 738433) (by norm_num)
theorem B5322773 : Blo 1748575 5322773 := bbase (se 6 (by rfl) ⟨124752, by rfl⟩ : syracuseStep 5322773 = 249505) (by norm_num)
theorem B7477285 : Blo 1748575 7477285 := bbase (se 4 (by rfl) ⟨700995, by rfl⟩ : syracuseStep 7477285 = 1401991) (by norm_num)
theorem B3938381 : Blo 1748575 3938381 := bbase (se 3 (by rfl) ⟨738446, by rfl⟩ : syracuseStep 3938381 = 1476893) (by norm_num)
theorem B3545189 : Blo 1748575 3545189 := bbase (se 4 (by rfl) ⟨332361, by rfl⟩ : syracuseStep 3545189 = 664723) (by norm_num)
theorem B6641797 : Blo 1748575 6641797 := bbase (se 4 (by rfl) ⟨622668, by rfl⟩ : syracuseStep 6641797 = 1245337) (by norm_num)
theorem B3938453 : Blo 1748575 3938453 := bbase (se 6 (by rfl) ⟨92307, by rfl⟩ : syracuseStep 3938453 = 184615) (by norm_num)
theorem B3938525 : Blo 1748575 3938525 := bbase (se 3 (by rfl) ⟨738473, by rfl⟩ : syracuseStep 3938525 = 1476947) (by norm_num)
theorem B3152117 : Blo 1748575 3152117 := bbase (se 5 (by rfl) ⟨147755, by rfl⟩ : syracuseStep 3152117 = 295511) (by norm_num)
theorem B5904629 : Blo 1748575 5904629 := bbase (se 5 (by rfl) ⟨276779, by rfl⟩ : syracuseStep 5904629 = 553559) (by norm_num)
theorem B24254741 : Blo 1748575 24254741 := bbase (se 6 (by rfl) ⟨568470, by rfl⟩ : syracuseStep 24254741 = 1136941) (by norm_num)
theorem B31930645 : Blo 1748575 31930645 := bbase (se 6 (by rfl) ⟨748374, by rfl⟩ : syracuseStep 31930645 = 1496749) (by norm_num)
theorem B3938597 : Blo 1748575 3938597 := bbase (se 4 (by rfl) ⟨369243, by rfl⟩ : syracuseStep 3938597 = 738487) (by norm_num)
theorem B4430173 : Blo 1748575 4430173 := bbase (se 3 (by rfl) ⟨830657, by rfl⟩ : syracuseStep 4430173 = 1661315) (by norm_num)
theorem B3938669 : Blo 1748575 3938669 := bbase (se 3 (by rfl) ⟨738500, by rfl⟩ : syracuseStep 3938669 = 1477001) (by norm_num)
theorem B13285781 : Blo 1748575 13285781 := bbase (se 6 (by rfl) ⟨311385, by rfl⟩ : syracuseStep 13285781 = 622771) (by norm_num)
theorem B6642101 : Blo 1748575 6642101 := bbase (se 5 (by rfl) ⟨311348, by rfl⟩ : syracuseStep 6642101 = 622697) (by norm_num)
theorem B3938741 : Blo 1748575 3938741 := bbase (se 5 (by rfl) ⟨184628, by rfl⟩ : syracuseStep 3938741 = 369257) (by norm_num)
theorem B3152333 : Blo 1748575 3152333 := bbase (se 3 (by rfl) ⟨591062, by rfl⟩ : syracuseStep 3152333 = 1182125) (by norm_num)
theorem B4430285 : Blo 1748575 4430285 := bbase (se 3 (by rfl) ⟨830678, by rfl⟩ : syracuseStep 4430285 = 1661357) (by norm_num)
theorem B2021857 : Blo 1748575 2021857 := bbase (se 2 (by rfl) ⟨758196, by rfl⟩ : syracuseStep 2021857 = 1516393) (by norm_num)
theorem B8526325 : Blo 1748575 8526325 := bbase (se 5 (by rfl) ⟨399671, by rfl⟩ : syracuseStep 8526325 = 799343) (by norm_num)
theorem B5323333 : Blo 1748575 5323333 := bbase (se 4 (by rfl) ⟨499062, by rfl⟩ : syracuseStep 5323333 = 998125) (by norm_num)
theorem B2021965 : Blo 1748575 2021965 := bbase (se 3 (by rfl) ⟨379118, by rfl⟩ : syracuseStep 2021965 = 758237) (by norm_num)
theorem B4430477 : Blo 1748575 4430477 := bbase (se 3 (by rfl) ⟨830714, by rfl⟩ : syracuseStep 4430477 = 1661429) (by norm_num)
theorem B5905061 : Blo 1748575 5905061 := bbase (se 4 (by rfl) ⟨553599, by rfl⟩ : syracuseStep 5905061 = 1107199) (by norm_num)
theorem B3152621 : Blo 1748575 3152621 := bbase (se 3 (by rfl) ⟨591116, by rfl⟩ : syracuseStep 3152621 = 1182233) (by norm_num)
theorem B5602069 : Blo 1748575 5602069 := bbase (se 6 (by rfl) ⟨131298, by rfl⟩ : syracuseStep 5602069 = 262597) (by norm_num)
theorem B4430821 : Blo 1748575 4430821 := bbase (se 4 (by rfl) ⟨415389, by rfl⟩ : syracuseStep 4430821 = 830779) (by norm_num)
theorem B3734525 : Blo 1748575 3734525 := bbase (se 3 (by rfl) ⟨700223, by rfl⟩ : syracuseStep 3734525 = 1400447) (by norm_num)
theorem B2022413 : Blo 1748575 2022413 := bbase (se 3 (by rfl) ⟨379202, by rfl⟩ : syracuseStep 2022413 = 758405) (by norm_num)
theorem B9460757 : Blo 1748575 9460757 := bbase (se 6 (by rfl) ⟨221736, by rfl⟩ : syracuseStep 9460757 = 443473) (by norm_num)
theorem B18922517 : Blo 1748575 18922517 := bbase (se 6 (by rfl) ⟨443496, by rfl⟩ : syracuseStep 18922517 = 886993) (by norm_num)
theorem B5905493 : Blo 1748575 5905493 := bbase (se 8 (by rfl) ⟨34602, by rfl⟩ : syracuseStep 5905493 = 69205) (by norm_num)
theorem B4430933 : Blo 1748575 4430933 := bbase (se 8 (by rfl) ⟨25962, by rfl⟩ : syracuseStep 4430933 = 51925) (by norm_num)
theorem B7470245 : Blo 1748575 7470245 := bbase (se 4 (by rfl) ⟨700335, by rfl⟩ : syracuseStep 7470245 = 1400671) (by norm_num)
theorem B8404181 : Blo 1748575 8404181 := bbase (se 7 (by rfl) ⟨98486, by rfl⟩ : syracuseStep 8404181 = 196973) (by norm_num)
theorem B8854757 : Blo 1748575 8854757 := bbase (se 4 (by rfl) ⟨830133, by rfl⟩ : syracuseStep 8854757 = 1660267) (by norm_num)
theorem B7093493 : Blo 1748575 7093493 := bbase (se 5 (by rfl) ⟨332507, by rfl⟩ : syracuseStep 7093493 = 665015) (by norm_num)
theorem B4431125 : Blo 1748575 4431125 := bbase (se 6 (by rfl) ⟨103854, by rfl⟩ : syracuseStep 4431125 = 207709) (by norm_num)
theorem B4980005 : Blo 1748575 4980005 := bbase (se 4 (by rfl) ⟨466875, by rfl⟩ : syracuseStep 4980005 = 933751) (by norm_num)
theorem B2800997 : Blo 1748575 2800997 := bbase (se 4 (by rfl) ⟨262593, by rfl⟩ : syracuseStep 2800997 = 525187) (by norm_num)
theorem B4046269 : Blo 1748575 4046269 := bbase (se 3 (by rfl) ⟨758675, by rfl⟩ : syracuseStep 4046269 = 1517351) (by norm_num)
theorem B3988997 : Blo 1748575 3988997 := bbase (se 4 (by rfl) ⟨373968, by rfl⟩ : syracuseStep 3988997 = 747937) (by norm_num)
theorem B5905925 : Blo 1748575 5905925 := bbase (se 4 (by rfl) ⟨553680, by rfl⟩ : syracuseStep 5905925 = 1107361) (by norm_num)
theorem B2801189 : Blo 1748575 2801189 := bbase (se 4 (by rfl) ⟨262611, by rfl⟩ : syracuseStep 2801189 = 525223) (by norm_num)
theorem B11214389 : Blo 1748575 11214389 := bbase (se 5 (by rfl) ⟨525674, by rfl⟩ : syracuseStep 11214389 = 1051349) (by norm_num)
theorem B3595877 : Blo 1748575 3595877 := bbase (se 4 (by rfl) ⟨337113, by rfl⟩ : syracuseStep 3595877 = 674227) (by norm_num)
theorem B1867421 : Blo 1748575 1867421 := bbase (se 3 (by rfl) ⟨350141, by rfl⟩ : syracuseStep 1867421 = 700283) (by norm_num)
theorem B2801317 : Blo 1748575 2801317 := bbase (se 4 (by rfl) ⟨262623, by rfl⟩ : syracuseStep 2801317 = 525247) (by norm_num)
theorem B4980437 : Blo 1748575 4980437 := bbase (se 7 (by rfl) ⟨58364, by rfl⟩ : syracuseStep 4980437 = 116729) (by norm_num)
theorem B3546845 : Blo 1748575 3546845 := bbase (se 3 (by rfl) ⟨665033, by rfl⟩ : syracuseStep 3546845 = 1330067) (by norm_num)
theorem B1867493 : Blo 1748575 1867493 := bbase (se 4 (by rfl) ⟨175077, by rfl⟩ : syracuseStep 1867493 = 350155) (by norm_num)
theorem B3153637 : Blo 1748575 3153637 := bbase (se 4 (by rfl) ⟨295653, by rfl⟩ : syracuseStep 3153637 = 591307) (by norm_num)
theorem B3735389 : Blo 1748575 3735389 := bbase (se 3 (by rfl) ⟨700385, by rfl⟩ : syracuseStep 3735389 = 1400771) (by norm_num)
theorem B4202389 : Blo 1748575 4202389 := bbase (se 6 (by rfl) ⟨98493, by rfl⟩ : syracuseStep 4202389 = 196987) (by norm_num)
theorem B24600469 : Blo 1748575 24600469 := bbase (se 6 (by rfl) ⟨576573, by rfl⟩ : syracuseStep 24600469 = 1153147) (by norm_num)
theorem B9723797 : Blo 1748575 9723797 := bbase (se 6 (by rfl) ⟨227901, by rfl⟩ : syracuseStep 9723797 = 455803) (by norm_num)
theorem B1867681 : Blo 1748575 1867681 := bbase (se 2 (by rfl) ⟨700380, by rfl⟩ : syracuseStep 1867681 = 1400761) (by norm_num)
theorem B5906357 : Blo 1748575 5906357 := bbase (se 5 (by rfl) ⟨276860, by rfl⟩ : syracuseStep 5906357 = 553721) (by norm_num)
theorem B4202437 : Blo 1748575 4202437 := bbase (se 4 (by rfl) ⟨393978, by rfl⟩ : syracuseStep 4202437 = 787957) (by norm_num)
theorem B3735533 : Blo 1748575 3735533 := bbase (se 3 (by rfl) ⟨700412, by rfl⟩ : syracuseStep 3735533 = 1400825) (by norm_num)
theorem B9453581 : Blo 1748575 9453581 := bstep (se 3 (by rfl) ⟨1772546, by rfl⟩ : syracuseStep 9453581 = 3545093) B3545093
theorem B9969713 : Blo 1748575 9969713 := bstep (se 2 (by rfl) ⟨3738642, by rfl⟩ : syracuseStep 9969713 = 7477285) B7477285
theorem B5988419 : Blo 1748575 5988419 := bstep (se 1 (by rfl) ⟨4491314, by rfl⟩ : syracuseStep 5988419 = 8982629) B8982629
theorem B59113585 : Blo 1748575 59113585 := bstep (se 2 (by rfl) ⟨22167594, by rfl⟩ : syracuseStep 59113585 = 44335189) B44335189
theorem B5906573 : Blo 1748575 5906573 := bstep (se 3 (by rfl) ⟨1107482, by rfl⟩ : syracuseStep 5906573 = 2214965) B2214965
theorem B9961649 : Blo 1748575 9961649 := bstep (se 2 (by rfl) ⟨3735618, by rfl⟩ : syracuseStep 9961649 = 7471237) B7471237
theorem B8855729 : Blo 1748575 8855729 := bstep (se 2 (by rfl) ⟨3320898, by rfl⟩ : syracuseStep 8855729 = 6641797) B6641797
theorem B5906627 : Blo 1748575 5906627 := bstep (se 1 (by rfl) ⟨4429970, by rfl⟩ : syracuseStep 5906627 = 8859941) B8859941
theorem B4980973 : Blo 1748575 4980973 := bstep (se 3 (by rfl) ⟨933932, by rfl⟩ : syracuseStep 4980973 = 1867865) B1867865
theorem B3735875 : Blo 1748575 3735875 := bstep (se 1 (by rfl) ⟨2801906, by rfl⟩ : syracuseStep 3735875 = 5603813) B5603813
theorem B6644045 : Blo 1748575 6644045 := bstep (se 3 (by rfl) ⟨1245758, by rfl⟩ : syracuseStep 6644045 = 2491517) B2491517
theorem B18907505 : Blo 1748575 18907505 := bstep (se 2 (by rfl) ⟨7090314, by rfl⟩ : syracuseStep 18907505 = 14180629) B14180629
theorem B42574193 : Blo 1748575 42574193 := bstep (se 2 (by rfl) ⟨15965322, by rfl⟩ : syracuseStep 42574193 = 31930645) B31930645
theorem B2802035 : Blo 1748575 2802035 := bstep (se 1 (by rfl) ⟨2101526, by rfl⟩ : syracuseStep 2802035 = 4203053) B4203053
theorem B2245043 : Blo 1748575 2245043 := bstep (se 1 (by rfl) ⟨1683782, by rfl⟩ : syracuseStep 2245043 = 3367565) B3367565
theorem B5906897 : Blo 1748575 5906897 := bstep (se 2 (by rfl) ⟨2215086, by rfl⟩ : syracuseStep 5906897 = 4430173) B4430173
theorem B2490851 : Blo 1748575 2490851 := bstep (se 1 (by rfl) ⟨1868138, by rfl⟩ : syracuseStep 2490851 = 3736277) B3736277
theorem B1868275 : Blo 1748575 1868275 := bstep (se 1 (by rfl) ⟨1401206, by rfl⟩ : syracuseStep 1868275 = 2802413) B2802413
theorem B22717027 : Blo 1748575 22717027 := bstep (se 1 (by rfl) ⟨17037770, by rfl⟩ : syracuseStep 22717027 = 34075541) B34075541
theorem B11207267 : Blo 1748575 11207267 := bstep (se 1 (by rfl) ⟨8405450, by rfl⟩ : syracuseStep 11207267 = 16810901) B16810901
theorem B19923569 : Blo 1748575 19923569 := bstep (se 2 (by rfl) ⟨7471338, by rfl⟩ : syracuseStep 19923569 = 14942677) B14942677
theorem B2802419 : Blo 1748575 2802419 := bstep (se 1 (by rfl) ⟨2101814, by rfl⟩ : syracuseStep 2802419 = 4203629) B4203629
theorem B8405795 : Blo 1748575 8405795 := bstep (se 1 (by rfl) ⟨6304346, by rfl⟩ : syracuseStep 8405795 = 12608693) B12608693
theorem B2802547 : Blo 1748575 2802547 := bstep (se 1 (by rfl) ⟨2101910, by rfl⟩ : syracuseStep 2802547 = 4203821) B4203821
theorem B5907437 : Blo 1748575 5907437 := bstep (se 3 (by rfl) ⟨1107644, by rfl⟩ : syracuseStep 5907437 = 2215289) B2215289
theorem B5907491 : Blo 1748575 5907491 := bstep (se 1 (by rfl) ⟨4430618, by rfl⟩ : syracuseStep 5907491 = 8861237) B8861237
theorem B37815349 : Blo 1748575 37815349 := bstep (se 5 (by rfl) ⟨1772594, by rfl⟩ : syracuseStep 37815349 = 3545189) B3545189
theorem B22422581 : Blo 1748575 22422581 := bstep (se 5 (by rfl) ⟨1051058, by rfl⟩ : syracuseStep 22422581 = 2102117) B2102117
theorem B2245699 : Blo 1748575 2245699 := bstep (se 1 (by rfl) ⟨1684274, by rfl⟩ : syracuseStep 2245699 = 3368549) B3368549
theorem B2491489 : Blo 1748575 2491489 := bstep (se 2 (by rfl) ⟨934308, by rfl⟩ : syracuseStep 2491489 = 1868617) B1868617
theorem B1967251 : Blo 1748575 1967251 := bstep (se 1 (by rfl) ⟨1475438, by rfl⟩ : syracuseStep 1967251 = 2950877) B2950877
theorem B16819397 : Blo 1748575 16819397 := bstep (se 4 (by rfl) ⟨1576818, by rfl⟩ : syracuseStep 16819397 = 3153637) B3153637
theorem B3736849 : Blo 1748575 3736849 := bstep (se 2 (by rfl) ⟨1401318, by rfl⟩ : syracuseStep 3736849 = 2802637) B2802637
theorem B1967395 : Blo 1748575 1967395 := bstep (se 1 (by rfl) ⟨1475546, by rfl⟩ : syracuseStep 1967395 = 2951093) B2951093
theorem B3458339 : Blo 1748575 3458339 := bstep (se 1 (by rfl) ⟨2593754, by rfl⟩ : syracuseStep 3458339 = 5187509) B5187509
theorem B5907761 : Blo 1748575 5907761 := bstep (se 2 (by rfl) ⟨2215410, by rfl⟩ : syracuseStep 5907761 = 4430821) B4430821
theorem B3548515 : Blo 1748575 3548515 := bstep (se 1 (by rfl) ⟨2661386, by rfl⟩ : syracuseStep 3548515 = 5322773) B5322773
theorem B2622881 : Blo 1748575 2622881 := bstep (se 2 (by rfl) ⟨983580, by rfl⟩ : syracuseStep 2622881 = 1967161) B1967161
theorem B2491825 : Blo 1748575 2491825 := bstep (se 2 (by rfl) ⟨934434, by rfl⟩ : syracuseStep 2491825 = 1868869) B1868869
theorem B2622899 : Blo 1748575 2622899 := bstep (se 1 (by rfl) ⟨1967174, by rfl⟩ : syracuseStep 2622899 = 3934349) B3934349
theorem B1967539 : Blo 1748575 1967539 := bstep (se 1 (by rfl) ⟨1475654, by rfl⟩ : syracuseStep 1967539 = 2951309) B2951309
theorem B2622929 : Blo 1748575 2622929 := bstep (se 2 (by rfl) ⟨983598, by rfl⟩ : syracuseStep 2622929 = 1967197) B1967197
theorem B2622947 : Blo 1748575 2622947 := bstep (se 1 (by rfl) ⟨1967210, by rfl⟩ : syracuseStep 2622947 = 3934421) B3934421
theorem B2622977 : Blo 1748575 2622977 := bstep (se 2 (by rfl) ⟨983616, by rfl⟩ : syracuseStep 2622977 = 1967233) B1967233
theorem B3737105 : Blo 1748575 3737105 := bstep (se 2 (by rfl) ⟨1401414, by rfl⟩ : syracuseStep 3737105 = 2802829) B2802829
theorem B2622995 : Blo 1748575 2622995 := bstep (se 1 (by rfl) ⟨1967246, by rfl⟩ : syracuseStep 2622995 = 3934493) B3934493
theorem B2623025 : Blo 1748575 2623025 := bstep (se 2 (by rfl) ⟨983634, by rfl⟩ : syracuseStep 2623025 = 1967269) B1967269
theorem B2803265 : Blo 1748575 2803265 := bstep (se 2 (by rfl) ⟨1051224, by rfl⟩ : syracuseStep 2803265 = 2102449) B2102449
theorem B2623043 : Blo 1748575 2623043 := bstep (se 1 (by rfl) ⟨1967282, by rfl⟩ : syracuseStep 2623043 = 3934565) B3934565
theorem B1967683 : Blo 1748575 1967683 := bstep (se 1 (by rfl) ⟨1475762, by rfl⟩ : syracuseStep 1967683 = 2951525) B2951525
theorem B2623073 : Blo 1748575 2623073 := bstep (se 2 (by rfl) ⟨983652, by rfl⟩ : syracuseStep 2623073 = 1967305) B1967305
theorem B8636003 : Blo 1748575 8636003 := bstep (se 1 (by rfl) ⟨6477002, by rfl⟩ : syracuseStep 8636003 = 12954005) B12954005
theorem B9963107 : Blo 1748575 9963107 := bstep (se 1 (by rfl) ⟨7472330, by rfl⟩ : syracuseStep 9963107 = 14944661) B14944661
theorem B8857187 : Blo 1748575 8857187 := bstep (se 1 (by rfl) ⟨6642890, by rfl⟩ : syracuseStep 8857187 = 13285781) B13285781
theorem B2950769 : Blo 1748575 2950769 := bstep (se 2 (by rfl) ⟨1106538, by rfl⟩ : syracuseStep 2950769 = 2213077) B2213077
theorem B8406641 : Blo 1748575 8406641 := bstep (se 2 (by rfl) ⟨3152490, by rfl⟩ : syracuseStep 8406641 = 6304981) B6304981
theorem B2623091 : Blo 1748575 2623091 := bstep (se 1 (by rfl) ⟨1967318, by rfl⟩ : syracuseStep 2623091 = 3934637) B3934637
theorem B2213507 : Blo 1748575 2213507 := bstep (se 1 (by rfl) ⟨1660130, by rfl⟩ : syracuseStep 2213507 = 3320261) B3320261
theorem B2623121 : Blo 1748575 2623121 := bstep (se 2 (by rfl) ⟨983670, by rfl⟩ : syracuseStep 2623121 = 1967341) B1967341
theorem B2623139 : Blo 1748575 2623139 := bstep (se 1 (by rfl) ⟨1967354, by rfl⟩ : syracuseStep 2623139 = 3934709) B3934709
theorem B2623169 : Blo 1748575 2623169 := bstep (se 2 (by rfl) ⟨983688, by rfl⟩ : syracuseStep 2623169 = 1967377) B1967377
theorem B14771909 : Blo 1748575 14771909 := bstep (se 4 (by rfl) ⟨1384866, by rfl⟩ : syracuseStep 14771909 = 2769733) B2769733
theorem B2623187 : Blo 1748575 2623187 := bstep (se 1 (by rfl) ⟨1967390, by rfl⟩ : syracuseStep 2623187 = 3934781) B3934781
theorem B1967827 : Blo 1748575 1967827 := bstep (se 1 (by rfl) ⟨1475870, by rfl⟩ : syracuseStep 1967827 = 2951741) B2951741
theorem B2950897 : Blo 1748575 2950897 := bstep (se 2 (by rfl) ⟨1106586, by rfl⟩ : syracuseStep 2950897 = 2213173) B2213173
theorem B2623217 : Blo 1748575 2623217 := bstep (se 2 (by rfl) ⟨983706, by rfl⟩ : syracuseStep 2623217 = 1967413) B1967413
theorem B2803457 : Blo 1748575 2803457 := bstep (se 2 (by rfl) ⟨1051296, by rfl⟩ : syracuseStep 2803457 = 2102593) B2102593
theorem B2623235 : Blo 1748575 2623235 := bstep (se 1 (by rfl) ⟨1967426, by rfl⟩ : syracuseStep 2623235 = 3934853) B3934853
theorem B14944013 : Blo 1748575 14944013 := bstep (se 3 (by rfl) ⟨2802002, by rfl⟩ : syracuseStep 14944013 = 5604005) B5604005
theorem B2950931 : Blo 1748575 2950931 := bstep (se 1 (by rfl) ⟨2213198, by rfl⟩ : syracuseStep 2950931 = 4426397) B4426397
theorem B2623265 : Blo 1748575 2623265 := bstep (se 2 (by rfl) ⟨983724, by rfl⟩ : syracuseStep 2623265 = 1967449) B1967449
theorem B2623283 : Blo 1748575 2623283 := bstep (se 1 (by rfl) ⟨1967462, by rfl⟩ : syracuseStep 2623283 = 3934925) B3934925
theorem B2623313 : Blo 1748575 2623313 := bstep (se 2 (by rfl) ⟨983742, by rfl⟩ : syracuseStep 2623313 = 1967485) B1967485
theorem B2623331 : Blo 1748575 2623331 := bstep (se 1 (by rfl) ⟨1967498, by rfl⟩ : syracuseStep 2623331 = 3934997) B3934997
theorem B1967971 : Blo 1748575 1967971 := bstep (se 1 (by rfl) ⟨1475978, by rfl⟩ : syracuseStep 1967971 = 2951957) B2951957
theorem B2623361 : Blo 1748575 2623361 := bstep (se 2 (by rfl) ⟨983760, by rfl⟩ : syracuseStep 2623361 = 1967521) B1967521
theorem B2951059 : Blo 1748575 2951059 := bstep (se 1 (by rfl) ⟨2213294, by rfl⟩ : syracuseStep 2951059 = 4426589) B4426589
theorem B2623379 : Blo 1748575 2623379 := bstep (se 1 (by rfl) ⟨1967534, by rfl⟩ : syracuseStep 2623379 = 3935069) B3935069
theorem B2623409 : Blo 1748575 2623409 := bstep (se 2 (by rfl) ⟨983778, by rfl⟩ : syracuseStep 2623409 = 1967557) B1967557
theorem B4982705 : Blo 1748575 4982705 := bstep (se 2 (by rfl) ⟨1868514, by rfl⟩ : syracuseStep 4982705 = 3737029) B3737029
theorem B2623427 : Blo 1748575 2623427 := bstep (se 1 (by rfl) ⟨1967570, by rfl⟩ : syracuseStep 2623427 = 3935141) B3935141
theorem B8406989 : Blo 1748575 8406989 := bstep (se 3 (by rfl) ⟨1576310, by rfl⟩ : syracuseStep 8406989 = 3152621) B3152621
theorem B2623457 : Blo 1748575 2623457 := bstep (se 2 (by rfl) ⟨983796, by rfl⟩ : syracuseStep 2623457 = 1967593) B1967593
theorem B2623475 : Blo 1748575 2623475 := bstep (se 1 (by rfl) ⟨1967606, by rfl⟩ : syracuseStep 2623475 = 3935213) B3935213
theorem B1968115 : Blo 1748575 1968115 := bstep (se 1 (by rfl) ⟨1476086, by rfl⟩ : syracuseStep 1968115 = 2952173) B2952173
theorem B2492417 : Blo 1748575 2492417 := bstep (se 2 (by rfl) ⟨934656, by rfl⟩ : syracuseStep 2492417 = 1869313) B1869313
theorem B2623505 : Blo 1748575 2623505 := bstep (se 2 (by rfl) ⟨983814, by rfl⟩ : syracuseStep 2623505 = 1967629) B1967629
theorem B43132949 : Blo 1748575 43132949 := bstep (se 6 (by rfl) ⟨1010928, by rfl⟩ : syracuseStep 43132949 = 2021857) B2021857
theorem B2951201 : Blo 1748575 2951201 := bstep (se 2 (by rfl) ⟨1106700, by rfl⟩ : syracuseStep 2951201 = 2213401) B2213401
theorem B2623523 : Blo 1748575 2623523 := bstep (se 1 (by rfl) ⟨1967642, by rfl⟩ : syracuseStep 2623523 = 3935285) B3935285
theorem B2623553 : Blo 1748575 2623553 := bstep (se 2 (by rfl) ⟨983832, by rfl⟩ : syracuseStep 2623553 = 1967665) B1967665
theorem B2623571 : Blo 1748575 2623571 := bstep (se 1 (by rfl) ⟨1967678, by rfl⟩ : syracuseStep 2623571 = 3935357) B3935357
theorem B2623601 : Blo 1748575 2623601 := bstep (se 2 (by rfl) ⟨983850, by rfl⟩ : syracuseStep 2623601 = 1967701) B1967701
theorem B4982897 : Blo 1748575 4982897 := bstep (se 2 (by rfl) ⟨1868586, by rfl⟩ : syracuseStep 4982897 = 3737173) B3737173
theorem B53889137 : Blo 1748575 53889137 := bstep (se 2 (by rfl) ⟨20208426, by rfl⟩ : syracuseStep 53889137 = 40416853) B40416853
theorem B2623619 : Blo 1748575 2623619 := bstep (se 1 (by rfl) ⟨1967714, by rfl⟩ : syracuseStep 2623619 = 3935429) B3935429
theorem B1968259 : Blo 1748575 1968259 := bstep (se 1 (by rfl) ⟨1476194, by rfl⟩ : syracuseStep 1968259 = 2952389) B2952389
theorem B3991697 : Blo 1748575 3991697 := bstep (se 2 (by rfl) ⟨1496886, by rfl⟩ : syracuseStep 3991697 = 2993773) B2993773
theorem B2951329 : Blo 1748575 2951329 := bstep (se 2 (by rfl) ⟨1106748, by rfl⟩ : syracuseStep 2951329 = 2213497) B2213497
theorem B2623649 : Blo 1748575 2623649 := bstep (se 2 (by rfl) ⟨983868, by rfl⟩ : syracuseStep 2623649 = 1967737) B1967737
theorem B4728995 : Blo 1748575 4728995 := bstep (se 1 (by rfl) ⟨3546746, by rfl⟩ : syracuseStep 4728995 = 7093493) B7093493
theorem B3934385 : Blo 1748575 3934385 := bstep (se 2 (by rfl) ⟨1475394, by rfl⟩ : syracuseStep 3934385 = 2950789) B2950789
theorem B2623667 : Blo 1748575 2623667 := bstep (se 1 (by rfl) ⟨1967750, by rfl⟩ : syracuseStep 2623667 = 3935501) B3935501
theorem B3934403 : Blo 1748575 3934403 := bstep (se 1 (by rfl) ⟨2950802, by rfl⟩ : syracuseStep 3934403 = 5901605) B5901605
theorem B3320003 : Blo 1748575 3320003 := bstep (se 1 (by rfl) ⟨2490002, by rfl⟩ : syracuseStep 3320003 = 4980005) B4980005
theorem B2951363 : Blo 1748575 2951363 := bstep (se 1 (by rfl) ⟨2213522, by rfl⟩ : syracuseStep 2951363 = 4427045) B4427045
theorem B13289669 : Blo 1748575 13289669 := bstep (se 4 (by rfl) ⟨1245906, by rfl⟩ : syracuseStep 13289669 = 2491813) B2491813
theorem B2623697 : Blo 1748575 2623697 := bstep (se 2 (by rfl) ⟨983886, by rfl⟩ : syracuseStep 2623697 = 1967773) B1967773
theorem B2623715 : Blo 1748575 2623715 := bstep (se 1 (by rfl) ⟨1967786, by rfl⟩ : syracuseStep 2623715 = 3935573) B3935573
theorem B2623745 : Blo 1748575 2623745 := bstep (se 2 (by rfl) ⟨983904, by rfl⟩ : syracuseStep 2623745 = 1967809) B1967809
theorem B2623763 : Blo 1748575 2623763 := bstep (se 1 (by rfl) ⟨1967822, by rfl⟩ : syracuseStep 2623763 = 3935645) B3935645
theorem B1968403 : Blo 1748575 1968403 := bstep (se 1 (by rfl) ⟨1476302, by rfl⟩ : syracuseStep 1968403 = 2952605) B2952605
theorem B2623793 : Blo 1748575 2623793 := bstep (se 2 (by rfl) ⟨983922, by rfl⟩ : syracuseStep 2623793 = 1967845) B1967845
theorem B2951491 : Blo 1748575 2951491 := bstep (se 1 (by rfl) ⟨2213618, by rfl⟩ : syracuseStep 2951491 = 4427237) B4427237
theorem B2623811 : Blo 1748575 2623811 := bstep (se 1 (by rfl) ⟨1967858, by rfl⟩ : syracuseStep 2623811 = 3935717) B3935717
theorem B2214211 : Blo 1748575 2214211 := bstep (se 1 (by rfl) ⟨1660658, by rfl⟩ : syracuseStep 2214211 = 3321317) B3321317
theorem B2623841 : Blo 1748575 2623841 := bstep (se 2 (by rfl) ⟨983940, by rfl⟩ : syracuseStep 2623841 = 1967881) B1967881
theorem B2623859 : Blo 1748575 2623859 := bstep (se 1 (by rfl) ⟨1967894, by rfl⟩ : syracuseStep 2623859 = 3935789) B3935789
theorem B8857997 : Blo 1748575 8857997 := bstep (se 3 (by rfl) ⟨1660874, by rfl⟩ : syracuseStep 8857997 = 3321749) B3321749
theorem B6646157 : Blo 1748575 6646157 := bstep (se 3 (by rfl) ⟨1246154, by rfl⟩ : syracuseStep 6646157 = 2492309) B2492309
theorem B2623889 : Blo 1748575 2623889 := bstep (se 2 (by rfl) ⟨983958, by rfl⟩ : syracuseStep 2623889 = 1967917) B1967917
theorem B2623907 : Blo 1748575 2623907 := bstep (se 1 (by rfl) ⟨1967930, by rfl⟩ : syracuseStep 2623907 = 3935861) B3935861
theorem B2214307 : Blo 1748575 2214307 := bstep (se 1 (by rfl) ⟨1660730, by rfl⟩ : syracuseStep 2214307 = 3321461) B3321461
theorem B1968547 : Blo 1748575 1968547 := bstep (se 1 (by rfl) ⟨1476410, by rfl⟩ : syracuseStep 1968547 = 2952821) B2952821
theorem B2623937 : Blo 1748575 2623937 := bstep (se 2 (by rfl) ⟨983976, by rfl⟩ : syracuseStep 2623937 = 1967953) B1967953
theorem B76687813 : Blo 1748575 76687813 := bstep (se 4 (by rfl) ⟨7189482, by rfl⟩ : syracuseStep 76687813 = 14378965) B14378965
theorem B3934673 : Blo 1748575 3934673 := bstep (se 2 (by rfl) ⟨1475502, by rfl⟩ : syracuseStep 3934673 = 2951005) B2951005
theorem B2951633 : Blo 1748575 2951633 := bstep (se 2 (by rfl) ⟨1106862, by rfl⟩ : syracuseStep 2951633 = 2213725) B2213725
theorem B2623955 : Blo 1748575 2623955 := bstep (se 1 (by rfl) ⟨1967966, by rfl⟩ : syracuseStep 2623955 = 3935933) B3935933
theorem B3934691 : Blo 1748575 3934691 := bstep (se 1 (by rfl) ⟨2951018, by rfl⟩ : syracuseStep 3934691 = 5902037) B5902037
theorem B3320291 : Blo 1748575 3320291 := bstep (se 1 (by rfl) ⟨2490218, by rfl⟩ : syracuseStep 3320291 = 4980437) B4980437
theorem B2623985 : Blo 1748575 2623985 := bstep (se 2 (by rfl) ⟨983994, by rfl⟩ : syracuseStep 2623985 = 1967989) B1967989
theorem B2624003 : Blo 1748575 2624003 := bstep (se 1 (by rfl) ⟨1968002, by rfl⟩ : syracuseStep 2624003 = 3936005) B3936005
theorem B2624033 : Blo 1748575 2624033 := bstep (se 2 (by rfl) ⟨984012, by rfl⟩ : syracuseStep 2624033 = 1968025) B1968025
theorem B11209265 : Blo 1748575 11209265 := bstep (se 2 (by rfl) ⟨4203474, by rfl⟩ : syracuseStep 11209265 = 8406949) B8406949
theorem B2624051 : Blo 1748575 2624051 := bstep (se 1 (by rfl) ⟨1968038, by rfl⟩ : syracuseStep 2624051 = 3936077) B3936077
theorem B1968691 : Blo 1748575 1968691 := bstep (se 1 (by rfl) ⟨1476518, by rfl⟩ : syracuseStep 1968691 = 2953037) B2953037
theorem B2951761 : Blo 1748575 2951761 := bstep (se 2 (by rfl) ⟨1106910, by rfl⟩ : syracuseStep 2951761 = 2213821) B2213821
theorem B2624081 : Blo 1748575 2624081 := bstep (se 2 (by rfl) ⟨984030, by rfl⟩ : syracuseStep 2624081 = 1968061) B1968061
theorem B2624099 : Blo 1748575 2624099 := bstep (se 1 (by rfl) ⟨1968074, by rfl⟩ : syracuseStep 2624099 = 3936149) B3936149
theorem B6482531 : Blo 1748575 6482531 := bstep (se 1 (by rfl) ⟨4861898, by rfl⟩ : syracuseStep 6482531 = 9723797) B9723797
theorem B2951795 : Blo 1748575 2951795 := bstep (se 1 (by rfl) ⟨2213846, by rfl⟩ : syracuseStep 2951795 = 4427693) B4427693
theorem B2624129 : Blo 1748575 2624129 := bstep (se 2 (by rfl) ⟨984048, by rfl⟩ : syracuseStep 2624129 = 1968097) B1968097
theorem B2624147 : Blo 1748575 2624147 := bstep (se 1 (by rfl) ⟨1968110, by rfl⟩ : syracuseStep 2624147 = 3936221) B3936221
theorem B2624177 : Blo 1748575 2624177 := bstep (se 2 (by rfl) ⟨984066, by rfl⟩ : syracuseStep 2624177 = 1968133) B1968133
theorem B2624195 : Blo 1748575 2624195 := bstep (se 1 (by rfl) ⟨1968146, by rfl⟩ : syracuseStep 2624195 = 3936293) B3936293
theorem B1968835 : Blo 1748575 1968835 := bstep (se 1 (by rfl) ⟨1476626, by rfl⟩ : syracuseStep 1968835 = 2953253) B2953253
theorem B5393101 : Blo 1748575 5393101 := bstep (se 3 (by rfl) ⟨1011206, by rfl⟩ : syracuseStep 5393101 = 2022413) B2022413
theorem B7473869 : Blo 1748575 7473869 := bstep (se 3 (by rfl) ⟨1401350, by rfl⟩ : syracuseStep 7473869 = 2802701) B2802701
theorem B2624225 : Blo 1748575 2624225 := bstep (se 2 (by rfl) ⟨984084, by rfl⟩ : syracuseStep 2624225 = 1968169) B1968169
theorem B3934961 : Blo 1748575 3934961 := bstep (se 2 (by rfl) ⟨1475610, by rfl⟩ : syracuseStep 3934961 = 2951221) B2951221
theorem B2951923 : Blo 1748575 2951923 := bstep (se 1 (by rfl) ⟨2213942, by rfl⟩ : syracuseStep 2951923 = 4427885) B4427885
theorem B2624243 : Blo 1748575 2624243 := bstep (se 1 (by rfl) ⟨1968182, by rfl⟩ : syracuseStep 2624243 = 3936365) B3936365
theorem B3934979 : Blo 1748575 3934979 := bstep (se 1 (by rfl) ⟨2951234, by rfl⟩ : syracuseStep 3934979 = 5902469) B5902469
theorem B2624273 : Blo 1748575 2624273 := bstep (se 2 (by rfl) ⟨984102, by rfl⟩ : syracuseStep 2624273 = 1968205) B1968205
theorem B2624291 : Blo 1748575 2624291 := bstep (se 1 (by rfl) ⟨1968218, by rfl⟩ : syracuseStep 2624291 = 3936437) B3936437
theorem B3738403 : Blo 1748575 3738403 := bstep (se 1 (by rfl) ⟨2803802, by rfl⟩ : syracuseStep 3738403 = 5607605) B5607605
theorem B2624321 : Blo 1748575 2624321 := bstep (se 2 (by rfl) ⟨984120, by rfl⟩ : syracuseStep 2624321 = 1968241) B1968241
theorem B2624339 : Blo 1748575 2624339 := bstep (se 1 (by rfl) ⟨1968254, by rfl⟩ : syracuseStep 2624339 = 3936509) B3936509
theorem B1968979 : Blo 1748575 1968979 := bstep (se 1 (by rfl) ⟨1476734, by rfl⟩ : syracuseStep 1968979 = 2953469) B2953469
theorem B4426609 : Blo 1748575 4426609 := bstep (se 2 (by rfl) ⟨1659978, by rfl⟩ : syracuseStep 4426609 = 3319957) B3319957
theorem B2624369 : Blo 1748575 2624369 := bstep (se 2 (by rfl) ⟨984138, by rfl⟩ : syracuseStep 2624369 = 1968277) B1968277
theorem B2952065 : Blo 1748575 2952065 := bstep (se 2 (by rfl) ⟨1107024, by rfl⟩ : syracuseStep 2952065 = 2214049) B2214049
theorem B2624387 : Blo 1748575 2624387 := bstep (se 1 (by rfl) ⟨1968290, by rfl⟩ : syracuseStep 2624387 = 3936581) B3936581
theorem B2214803 : Blo 1748575 2214803 := bstep (se 1 (by rfl) ⟨1661102, by rfl⟩ : syracuseStep 2214803 = 3322205) B3322205
theorem B2624417 : Blo 1748575 2624417 := bstep (se 2 (by rfl) ⟨984156, by rfl⟩ : syracuseStep 2624417 = 1968313) B1968313
theorem B2624435 : Blo 1748575 2624435 := bstep (se 1 (by rfl) ⟨1968326, by rfl⟩ : syracuseStep 2624435 = 3936653) B3936653
theorem B2624465 : Blo 1748575 2624465 := bstep (se 2 (by rfl) ⟨984174, by rfl⟩ : syracuseStep 2624465 = 1968349) B1968349
theorem B2624483 : Blo 1748575 2624483 := bstep (se 1 (by rfl) ⟨1968362, by rfl⟩ : syracuseStep 2624483 = 3936725) B3936725
theorem B1969123 : Blo 1748575 1969123 := bstep (se 1 (by rfl) ⟨1476842, by rfl⟩ : syracuseStep 1969123 = 2953685) B2953685
theorem B2952193 : Blo 1748575 2952193 := bstep (se 2 (by rfl) ⟨1107072, by rfl⟩ : syracuseStep 2952193 = 2214145) B2214145
theorem B2624513 : Blo 1748575 2624513 := bstep (se 2 (by rfl) ⟨984192, by rfl⟩ : syracuseStep 2624513 = 1968385) B1968385
theorem B3935249 : Blo 1748575 3935249 := bstep (se 2 (by rfl) ⟨1475718, by rfl⟩ : syracuseStep 3935249 = 2951437) B2951437
theorem B2624531 : Blo 1748575 2624531 := bstep (se 1 (by rfl) ⟨1968398, by rfl⟩ : syracuseStep 2624531 = 3936797) B3936797
theorem B3935267 : Blo 1748575 3935267 := bstep (se 1 (by rfl) ⟨2951450, by rfl⟩ : syracuseStep 3935267 = 5902901) B5902901
theorem B2952227 : Blo 1748575 2952227 := bstep (se 1 (by rfl) ⟨2214170, by rfl⟩ : syracuseStep 2952227 = 4428341) B4428341
theorem B2624561 : Blo 1748575 2624561 := bstep (se 2 (by rfl) ⟨984210, by rfl⟩ : syracuseStep 2624561 = 1968421) B1968421
theorem B29887541 : Blo 1748575 29887541 := bstep (se 5 (by rfl) ⟨1400978, by rfl⟩ : syracuseStep 29887541 = 2801957) B2801957
theorem B2624579 : Blo 1748575 2624579 := bstep (se 1 (by rfl) ⟨1968434, by rfl⟩ : syracuseStep 2624579 = 3936869) B3936869
theorem B10783813 : Blo 1748575 10783813 := bstep (se 4 (by rfl) ⟨1010982, by rfl⟩ : syracuseStep 10783813 = 2021965) B2021965
theorem B4983889 : Blo 1748575 4983889 := bstep (se 2 (by rfl) ⟨1868958, by rfl⟩ : syracuseStep 4983889 = 3737917) B3737917
theorem B2624609 : Blo 1748575 2624609 := bstep (se 2 (by rfl) ⟨984228, by rfl⟩ : syracuseStep 2624609 = 1968457) B1968457
theorem B3738737 : Blo 1748575 3738737 := bstep (se 2 (by rfl) ⟨1402026, by rfl⟩ : syracuseStep 3738737 = 2804053) B2804053
theorem B2624627 : Blo 1748575 2624627 := bstep (se 1 (by rfl) ⟨1968470, by rfl⟩ : syracuseStep 2624627 = 3936941) B3936941
theorem B1969267 : Blo 1748575 1969267 := bstep (se 1 (by rfl) ⟨1476950, by rfl⟩ : syracuseStep 1969267 = 2953901) B2953901
theorem B5901443 : Blo 1748575 5901443 := bstep (se 1 (by rfl) ⟨4426082, by rfl⟩ : syracuseStep 5901443 = 8852165) B8852165
theorem B4426883 : Blo 1748575 4426883 := bstep (se 1 (by rfl) ⟨3320162, by rfl⟩ : syracuseStep 4426883 = 6640325) B6640325
theorem B2624657 : Blo 1748575 2624657 := bstep (se 2 (by rfl) ⟨984246, by rfl⟩ : syracuseStep 2624657 = 1968493) B1968493
theorem B4795537 : Blo 1748575 4795537 := bstep (se 2 (by rfl) ⟨1798326, by rfl⟩ : syracuseStep 4795537 = 3596653) B3596653
theorem B2952355 : Blo 1748575 2952355 := bstep (se 1 (by rfl) ⟨2214266, by rfl⟩ : syracuseStep 2952355 = 4428533) B4428533
theorem B2624675 : Blo 1748575 2624675 := bstep (se 1 (by rfl) ⟨1968506, by rfl⟩ : syracuseStep 2624675 = 3937013) B3937013
theorem B4730033 : Blo 1748575 4730033 := bstep (se 2 (by rfl) ⟨1773762, by rfl⟩ : syracuseStep 4730033 = 3547525) B3547525
theorem B2624705 : Blo 1748575 2624705 := bstep (se 2 (by rfl) ⟨984264, by rfl⟩ : syracuseStep 2624705 = 1968529) B1968529
theorem B2624723 : Blo 1748575 2624723 := bstep (se 1 (by rfl) ⟨1968542, by rfl⟩ : syracuseStep 2624723 = 3937085) B3937085
theorem B2624753 : Blo 1748575 2624753 := bstep (se 2 (by rfl) ⟨984282, by rfl⟩ : syracuseStep 2624753 = 1968565) B1968565
theorem B2624771 : Blo 1748575 2624771 := bstep (se 1 (by rfl) ⟨1968578, by rfl⟩ : syracuseStep 2624771 = 3937157) B3937157
theorem B2624801 : Blo 1748575 2624801 := bstep (se 2 (by rfl) ⟨984300, by rfl⟩ : syracuseStep 2624801 = 1968601) B1968601
theorem B3935537 : Blo 1748575 3935537 := bstep (se 2 (by rfl) ⟨1475826, by rfl⟩ : syracuseStep 3935537 = 2951653) B2951653
theorem B2952497 : Blo 1748575 2952497 := bstep (se 2 (by rfl) ⟨1107186, by rfl⟩ : syracuseStep 2952497 = 2214373) B2214373
theorem B2624819 : Blo 1748575 2624819 := bstep (se 1 (by rfl) ⟨1968614, by rfl⟩ : syracuseStep 2624819 = 3937229) B3937229
theorem B4427075 : Blo 1748575 4427075 := bstep (se 1 (by rfl) ⟨3320306, by rfl⟩ : syracuseStep 4427075 = 6640613) B6640613
theorem B3935555 : Blo 1748575 3935555 := bstep (se 1 (by rfl) ⟨2951666, by rfl⟩ : syracuseStep 3935555 = 5903333) B5903333
theorem B2624849 : Blo 1748575 2624849 := bstep (se 2 (by rfl) ⟨984318, by rfl⟩ : syracuseStep 2624849 = 1968637) B1968637
theorem B2624867 : Blo 1748575 2624867 := bstep (se 1 (by rfl) ⟨1968650, by rfl⟩ : syracuseStep 2624867 = 3937301) B3937301
theorem B4984163 : Blo 1748575 4984163 := bstep (se 1 (by rfl) ⟨3738122, by rfl⟩ : syracuseStep 4984163 = 7476245) B7476245
theorem B2624897 : Blo 1748575 2624897 := bstep (se 2 (by rfl) ⟨984336, by rfl⟩ : syracuseStep 2624897 = 1968673) B1968673
theorem B5901713 : Blo 1748575 5901713 := bstep (se 2 (by rfl) ⟨2213142, by rfl⟩ : syracuseStep 5901713 = 4426285) B4426285
theorem B3321233 : Blo 1748575 3321233 := bstep (se 2 (by rfl) ⟨1245462, by rfl⟩ : syracuseStep 3321233 = 2490925) B2490925
theorem B2624915 : Blo 1748575 2624915 := bstep (se 1 (by rfl) ⟨1968686, by rfl⟩ : syracuseStep 2624915 = 3937373) B3937373
theorem B11357603 : Blo 1748575 11357603 := bstep (se 1 (by rfl) ⟨8518202, by rfl⟩ : syracuseStep 11357603 = 17036405) B17036405
theorem B2952625 : Blo 1748575 2952625 := bstep (se 2 (by rfl) ⟨1107234, by rfl⟩ : syracuseStep 2952625 = 2214469) B2214469
theorem B2624945 : Blo 1748575 2624945 := bstep (se 2 (by rfl) ⟨984354, by rfl⟩ : syracuseStep 2624945 = 1968709) B1968709
theorem B7097777 : Blo 1748575 7097777 := bstep (se 2 (by rfl) ⟨2661666, by rfl⟩ : syracuseStep 7097777 = 5323333) B5323333
theorem B2624963 : Blo 1748575 2624963 := bstep (se 1 (by rfl) ⟨1968722, by rfl⟩ : syracuseStep 2624963 = 3937445) B3937445
theorem B2952659 : Blo 1748575 2952659 := bstep (se 1 (by rfl) ⟨2214494, by rfl⟩ : syracuseStep 2952659 = 4428989) B4428989
theorem B2624993 : Blo 1748575 2624993 := bstep (se 2 (by rfl) ⟨984372, by rfl⟩ : syracuseStep 2624993 = 1968745) B1968745
theorem B2625011 : Blo 1748575 2625011 := bstep (se 1 (by rfl) ⟨1968758, by rfl⟩ : syracuseStep 2625011 = 3937517) B3937517
theorem B2625041 : Blo 1748575 2625041 := bstep (se 2 (by rfl) ⟨984390, by rfl⟩ : syracuseStep 2625041 = 1968781) B1968781
theorem B2625059 : Blo 1748575 2625059 := bstep (se 1 (by rfl) ⟨1968794, by rfl⟩ : syracuseStep 2625059 = 3937589) B3937589
theorem B4984355 : Blo 1748575 4984355 := bstep (se 1 (by rfl) ⟨3738266, by rfl⟩ : syracuseStep 4984355 = 7476533) B7476533
theorem B2625089 : Blo 1748575 2625089 := bstep (se 2 (by rfl) ⟨984408, by rfl⟩ : syracuseStep 2625089 = 1968817) B1968817
theorem B3935825 : Blo 1748575 3935825 := bstep (se 2 (by rfl) ⟨1475934, by rfl⟩ : syracuseStep 3935825 = 2951869) B2951869
theorem B2952787 : Blo 1748575 2952787 := bstep (se 1 (by rfl) ⟨2214590, by rfl⟩ : syracuseStep 2952787 = 4429181) B4429181
theorem B2625107 : Blo 1748575 2625107 := bstep (se 1 (by rfl) ⟨1968830, by rfl⟩ : syracuseStep 2625107 = 3937661) B3937661
theorem B2215507 : Blo 1748575 2215507 := bstep (se 1 (by rfl) ⟨1661630, by rfl⟩ : syracuseStep 2215507 = 3323261) B3323261
theorem B1748579 : Blo 1748575 1748579 := bstep (se 1 (by rfl) ⟨1311434, by rfl⟩ : syracuseStep 1748579 = 2622869) B2622869
theorem B3935843 : Blo 1748575 3935843 := bstep (se 1 (by rfl) ⟨2951882, by rfl⟩ : syracuseStep 3935843 = 5903765) B5903765
theorem B2625137 : Blo 1748575 2625137 := bstep (se 2 (by rfl) ⟨984426, by rfl⟩ : syracuseStep 2625137 = 1968853) B1968853
theorem B1748595 : Blo 1748575 1748595 := bstep (se 1 (by rfl) ⟨1311446, by rfl⟩ : syracuseStep 1748595 = 2622893) B2622893
theorem B1748611 : Blo 1748575 1748611 := bstep (se 1 (by rfl) ⟨1311458, by rfl⟩ : syracuseStep 1748611 = 2622917) B2622917
theorem B2625155 : Blo 1748575 2625155 := bstep (se 1 (by rfl) ⟨1968866, by rfl⟩ : syracuseStep 2625155 = 3937733) B3937733
theorem B1748627 : Blo 1748575 1748627 := bstep (se 1 (by rfl) ⟨1311470, by rfl⟩ : syracuseStep 1748627 = 2622941) B2622941
theorem B2625185 : Blo 1748575 2625185 := bstep (se 2 (by rfl) ⟨984444, by rfl⟩ : syracuseStep 2625185 = 1968889) B1968889
theorem B1748643 : Blo 1748575 1748643 := bstep (se 1 (by rfl) ⟨1311482, by rfl⟩ : syracuseStep 1748643 = 2622965) B2622965
theorem B1748659 : Blo 1748575 1748659 := bstep (se 1 (by rfl) ⟨1311494, by rfl⟩ : syracuseStep 1748659 = 2622989) B2622989
theorem B2625203 : Blo 1748575 2625203 := bstep (se 1 (by rfl) ⟨1968902, by rfl⟩ : syracuseStep 2625203 = 3937805) B3937805
theorem B1748675 : Blo 1748575 1748675 := bstep (se 1 (by rfl) ⟨1311506, by rfl⟩ : syracuseStep 1748675 = 2623013) B2623013
theorem B2625233 : Blo 1748575 2625233 := bstep (se 2 (by rfl) ⟨984462, by rfl⟩ : syracuseStep 2625233 = 1968925) B1968925
theorem B1748691 : Blo 1748575 1748691 := bstep (se 1 (by rfl) ⟨1311518, by rfl⟩ : syracuseStep 1748691 = 2623037) B2623037
theorem B2952929 : Blo 1748575 2952929 := bstep (se 2 (by rfl) ⟨1107348, by rfl⟩ : syracuseStep 2952929 = 2214697) B2214697
theorem B1748707 : Blo 1748575 1748707 := bstep (se 1 (by rfl) ⟨1311530, by rfl⟩ : syracuseStep 1748707 = 2623061) B2623061
theorem B2625251 : Blo 1748575 2625251 := bstep (se 1 (by rfl) ⟨1968938, by rfl⟩ : syracuseStep 2625251 = 3937877) B3937877
theorem B1748723 : Blo 1748575 1748723 := bstep (se 1 (by rfl) ⟨1311542, by rfl⟩ : syracuseStep 1748723 = 2623085) B2623085
theorem B2625281 : Blo 1748575 2625281 := bstep (se 2 (by rfl) ⟨984480, by rfl⟩ : syracuseStep 2625281 = 1968961) B1968961
theorem B1748739 : Blo 1748575 1748739 := bstep (se 1 (by rfl) ⟨1311554, by rfl⟩ : syracuseStep 1748739 = 2623109) B2623109
theorem B1748755 : Blo 1748575 1748755 := bstep (se 1 (by rfl) ⟨1311566, by rfl⟩ : syracuseStep 1748755 = 2623133) B2623133
theorem B2625299 : Blo 1748575 2625299 := bstep (se 1 (by rfl) ⟨1968974, by rfl⟩ : syracuseStep 2625299 = 3937949) B3937949
theorem B1748771 : Blo 1748575 1748771 := bstep (se 1 (by rfl) ⟨1311578, by rfl⟩ : syracuseStep 1748771 = 2623157) B2623157
theorem B2625329 : Blo 1748575 2625329 := bstep (se 2 (by rfl) ⟨984498, by rfl⟩ : syracuseStep 2625329 = 1968997) B1968997
theorem B1748787 : Blo 1748575 1748787 := bstep (se 1 (by rfl) ⟨1311590, by rfl⟩ : syracuseStep 1748787 = 2623181) B2623181
theorem B1748803 : Blo 1748575 1748803 := bstep (se 1 (by rfl) ⟨1311602, by rfl⟩ : syracuseStep 1748803 = 2623205) B2623205
theorem B2625347 : Blo 1748575 2625347 := bstep (se 1 (by rfl) ⟨1969010, by rfl⟩ : syracuseStep 2625347 = 3938021) B3938021
theorem B1748819 : Blo 1748575 1748819 := bstep (se 1 (by rfl) ⟨1311614, by rfl⟩ : syracuseStep 1748819 = 2623229) B2623229
theorem B2953057 : Blo 1748575 2953057 := bstep (se 2 (by rfl) ⟨1107396, by rfl⟩ : syracuseStep 2953057 = 2214793) B2214793
theorem B2625377 : Blo 1748575 2625377 := bstep (se 2 (by rfl) ⟨984516, by rfl⟩ : syracuseStep 2625377 = 1969033) B1969033
theorem B1748835 : Blo 1748575 1748835 := bstep (se 1 (by rfl) ⟨1311626, by rfl⟩ : syracuseStep 1748835 = 2623253) B2623253
theorem B3936113 : Blo 1748575 3936113 := bstep (se 2 (by rfl) ⟨1476042, by rfl⟩ : syracuseStep 3936113 = 2952085) B2952085
theorem B1748851 : Blo 1748575 1748851 := bstep (se 1 (by rfl) ⟨1311638, by rfl⟩ : syracuseStep 1748851 = 2623277) B2623277
theorem B2625395 : Blo 1748575 2625395 := bstep (se 1 (by rfl) ⟨1969046, by rfl⟩ : syracuseStep 2625395 = 3938093) B3938093
theorem B1748867 : Blo 1748575 1748867 := bstep (se 1 (by rfl) ⟨1311650, by rfl⟩ : syracuseStep 1748867 = 2623301) B2623301
theorem B3936131 : Blo 1748575 3936131 := bstep (se 1 (by rfl) ⟨2952098, by rfl⟩ : syracuseStep 3936131 = 5904197) B5904197
theorem B2953091 : Blo 1748575 2953091 := bstep (se 1 (by rfl) ⟨2214818, by rfl⟩ : syracuseStep 2953091 = 4429637) B4429637
theorem B2625425 : Blo 1748575 2625425 := bstep (se 2 (by rfl) ⟨984534, by rfl⟩ : syracuseStep 2625425 = 1969069) B1969069
theorem B1748883 : Blo 1748575 1748883 := bstep (se 1 (by rfl) ⟨1311662, by rfl⟩ : syracuseStep 1748883 = 2623325) B2623325
theorem B1748899 : Blo 1748575 1748899 := bstep (se 1 (by rfl) ⟨1311674, by rfl⟩ : syracuseStep 1748899 = 2623349) B2623349
theorem B2625443 : Blo 1748575 2625443 := bstep (se 1 (by rfl) ⟨1969082, by rfl⟩ : syracuseStep 2625443 = 3938165) B3938165
theorem B5902253 : Blo 1748575 5902253 := bstep (se 3 (by rfl) ⟨1106672, by rfl⟩ : syracuseStep 5902253 = 2213345) B2213345
theorem B1748915 : Blo 1748575 1748915 := bstep (se 1 (by rfl) ⟨1311686, by rfl⟩ : syracuseStep 1748915 = 2623373) B2623373
theorem B2625473 : Blo 1748575 2625473 := bstep (se 2 (by rfl) ⟨984552, by rfl⟩ : syracuseStep 2625473 = 1969105) B1969105
theorem B1748931 : Blo 1748575 1748931 := bstep (se 1 (by rfl) ⟨1311698, by rfl⟩ : syracuseStep 1748931 = 2623397) B2623397
theorem B1748947 : Blo 1748575 1748947 := bstep (se 1 (by rfl) ⟨1311710, by rfl⟩ : syracuseStep 1748947 = 2623421) B2623421
theorem B2625491 : Blo 1748575 2625491 := bstep (se 1 (by rfl) ⟨1969118, by rfl⟩ : syracuseStep 2625491 = 3938237) B3938237
theorem B5902307 : Blo 1748575 5902307 := bstep (se 1 (by rfl) ⟨4426730, by rfl⟩ : syracuseStep 5902307 = 8853461) B8853461
theorem B1748963 : Blo 1748575 1748963 := bstep (se 1 (by rfl) ⟨1311722, by rfl⟩ : syracuseStep 1748963 = 2623445) B2623445
theorem B16814051 : Blo 1748575 16814051 := bstep (se 1 (by rfl) ⟨12610538, by rfl⟩ : syracuseStep 16814051 = 25221077) B25221077
theorem B1748979 : Blo 1748575 1748979 := bstep (se 1 (by rfl) ⟨1311734, by rfl⟩ : syracuseStep 1748979 = 2623469) B2623469
theorem B2625521 : Blo 1748575 2625521 := bstep (se 2 (by rfl) ⟨984570, by rfl⟩ : syracuseStep 2625521 = 1969141) B1969141
theorem B1748995 : Blo 1748575 1748995 := bstep (se 1 (by rfl) ⟨1311746, by rfl⟩ : syracuseStep 1748995 = 2623493) B2623493
theorem B2953219 : Blo 1748575 2953219 := bstep (se 1 (by rfl) ⟨2214914, by rfl⟩ : syracuseStep 2953219 = 4429829) B4429829
theorem B3788803 : Blo 1748575 3788803 := bstep (se 1 (by rfl) ⟨2841602, by rfl⟩ : syracuseStep 3788803 = 5683205) B5683205
theorem B5607427 : Blo 1748575 5607427 := bstep (se 1 (by rfl) ⟨4205570, by rfl⟩ : syracuseStep 5607427 = 8411141) B8411141
theorem B2625539 : Blo 1748575 2625539 := bstep (se 1 (by rfl) ⟨1969154, by rfl⟩ : syracuseStep 2625539 = 3938309) B3938309
theorem B1749011 : Blo 1748575 1749011 := bstep (se 1 (by rfl) ⟨1311758, by rfl⟩ : syracuseStep 1749011 = 2623517) B2623517
theorem B2625569 : Blo 1748575 2625569 := bstep (se 2 (by rfl) ⟨984588, by rfl⟩ : syracuseStep 2625569 = 1969177) B1969177
theorem B1749027 : Blo 1748575 1749027 := bstep (se 1 (by rfl) ⟨1311770, by rfl⟩ : syracuseStep 1749027 = 2623541) B2623541
theorem B1749043 : Blo 1748575 1749043 := bstep (se 1 (by rfl) ⟨1311782, by rfl⟩ : syracuseStep 1749043 = 2623565) B2623565
theorem B2625587 : Blo 1748575 2625587 := bstep (se 1 (by rfl) ⟨1969190, by rfl⟩ : syracuseStep 2625587 = 3938381) B3938381
theorem B1749059 : Blo 1748575 1749059 := bstep (se 1 (by rfl) ⟨1311794, by rfl⟩ : syracuseStep 1749059 = 2623589) B2623589
theorem B2625617 : Blo 1748575 2625617 := bstep (se 2 (by rfl) ⟨984606, by rfl⟩ : syracuseStep 2625617 = 1969213) B1969213
theorem B1749075 : Blo 1748575 1749075 := bstep (se 1 (by rfl) ⟨1311806, by rfl⟩ : syracuseStep 1749075 = 2623613) B2623613
theorem B1749091 : Blo 1748575 1749091 := bstep (se 1 (by rfl) ⟨1311818, by rfl⟩ : syracuseStep 1749091 = 2623637) B2623637
theorem B2625635 : Blo 1748575 2625635 := bstep (se 1 (by rfl) ⟨1969226, by rfl⟩ : syracuseStep 2625635 = 3938453) B3938453
theorem B1749107 : Blo 1748575 1749107 := bstep (se 1 (by rfl) ⟨1311830, by rfl⟩ : syracuseStep 1749107 = 2623661) B2623661
theorem B1749123 : Blo 1748575 1749123 := bstep (se 1 (by rfl) ⟨1311842, by rfl⟩ : syracuseStep 1749123 = 2623685) B2623685
theorem B2625665 : Blo 1748575 2625665 := bstep (se 2 (by rfl) ⟨984624, by rfl⟩ : syracuseStep 2625665 = 1969249) B1969249
theorem B7983245 : Blo 1748575 7983245 := bstep (se 3 (by rfl) ⟨1496858, by rfl⟩ : syracuseStep 7983245 = 2993717) B2993717
theorem B29905037 : Blo 1748575 29905037 := bstep (se 3 (by rfl) ⟨5607194, by rfl⟩ : syracuseStep 29905037 = 11214389) B11214389
theorem B3936401 : Blo 1748575 3936401 := bstep (se 2 (by rfl) ⟨1476150, by rfl⟩ : syracuseStep 3936401 = 2952301) B2952301
theorem B2953361 : Blo 1748575 2953361 := bstep (se 2 (by rfl) ⟨1107510, by rfl⟩ : syracuseStep 2953361 = 2215021) B2215021
theorem B1749139 : Blo 1748575 1749139 := bstep (se 1 (by rfl) ⟨1311854, by rfl⟩ : syracuseStep 1749139 = 2623709) B2623709
theorem B2625683 : Blo 1748575 2625683 := bstep (se 1 (by rfl) ⟨1969262, by rfl⟩ : syracuseStep 2625683 = 3938525) B3938525
theorem B1749155 : Blo 1748575 1749155 := bstep (se 1 (by rfl) ⟨1311866, by rfl⟩ : syracuseStep 1749155 = 2623733) B2623733
theorem B2101411 : Blo 1748575 2101411 := bstep (se 1 (by rfl) ⟨1576058, by rfl⟩ : syracuseStep 2101411 = 3152117) B3152117
theorem B3936419 : Blo 1748575 3936419 := bstep (se 1 (by rfl) ⟨2952314, by rfl⟩ : syracuseStep 3936419 = 5904629) B5904629
theorem B2625713 : Blo 1748575 2625713 := bstep (se 2 (by rfl) ⟨984642, by rfl⟩ : syracuseStep 2625713 = 1969285) B1969285
theorem B1749171 : Blo 1748575 1749171 := bstep (se 1 (by rfl) ⟨1311878, by rfl⟩ : syracuseStep 1749171 = 2623757) B2623757
theorem B2363585 : Blo 1748575 2363585 := bstep (se 2 (by rfl) ⟨886344, by rfl⟩ : syracuseStep 2363585 = 1772689) B1772689
theorem B1749187 : Blo 1748575 1749187 := bstep (se 1 (by rfl) ⟨1311890, by rfl⟩ : syracuseStep 1749187 = 2623781) B2623781
theorem B2625731 : Blo 1748575 2625731 := bstep (se 1 (by rfl) ⟨1969298, by rfl⟩ : syracuseStep 2625731 = 3938597) B3938597
theorem B11210957 : Blo 1748575 11210957 := bstep (se 3 (by rfl) ⟨2102054, by rfl⟩ : syracuseStep 11210957 = 4204109) B4204109
theorem B1749203 : Blo 1748575 1749203 := bstep (se 1 (by rfl) ⟨1311902, by rfl⟩ : syracuseStep 1749203 = 2623805) B2623805
theorem B2625761 : Blo 1748575 2625761 := bstep (se 2 (by rfl) ⟨984660, by rfl⟩ : syracuseStep 2625761 = 1969321) B1969321
theorem B1749219 : Blo 1748575 1749219 := bstep (se 1 (by rfl) ⟨1311914, by rfl⟩ : syracuseStep 1749219 = 2623829) B2623829
theorem B5902577 : Blo 1748575 5902577 := bstep (se 2 (by rfl) ⟨2213466, by rfl⟩ : syracuseStep 5902577 = 4426933) B4426933
theorem B1749235 : Blo 1748575 1749235 := bstep (se 1 (by rfl) ⟨1311926, by rfl⟩ : syracuseStep 1749235 = 2623853) B2623853
theorem B4428017 : Blo 1748575 4428017 := bstep (se 2 (by rfl) ⟨1660506, by rfl⟩ : syracuseStep 4428017 = 3321013) B3321013
theorem B2625779 : Blo 1748575 2625779 := bstep (se 1 (by rfl) ⟨1969334, by rfl⟩ : syracuseStep 2625779 = 3938669) B3938669
theorem B1749251 : Blo 1748575 1749251 := bstep (se 1 (by rfl) ⟨1311938, by rfl⟩ : syracuseStep 1749251 = 2623877) B2623877
theorem B1749267 : Blo 1748575 1749267 := bstep (se 1 (by rfl) ⟨1311950, by rfl⟩ : syracuseStep 1749267 = 2623901) B2623901
theorem B3322129 : Blo 1748575 3322129 := bstep (se 2 (by rfl) ⟨1245798, by rfl⟩ : syracuseStep 3322129 = 2491597) B2491597
theorem B2953489 : Blo 1748575 2953489 := bstep (se 2 (by rfl) ⟨1107558, by rfl⟩ : syracuseStep 2953489 = 2215117) B2215117
theorem B2625809 : Blo 1748575 2625809 := bstep (se 2 (by rfl) ⟨984678, by rfl⟩ : syracuseStep 2625809 = 1969357) B1969357
theorem B1749283 : Blo 1748575 1749283 := bstep (se 1 (by rfl) ⟨1311962, by rfl⟩ : syracuseStep 1749283 = 2623925) B2623925
theorem B4428067 : Blo 1748575 4428067 := bstep (se 1 (by rfl) ⟨3321050, by rfl⟩ : syracuseStep 4428067 = 6642101) B6642101
theorem B2625827 : Blo 1748575 2625827 := bstep (se 1 (by rfl) ⟨1969370, by rfl⟩ : syracuseStep 2625827 = 3938741) B3938741
theorem B1749299 : Blo 1748575 1749299 := bstep (se 1 (by rfl) ⟨1311974, by rfl⟩ : syracuseStep 1749299 = 2623949) B2623949
theorem B2101555 : Blo 1748575 2101555 := bstep (se 1 (by rfl) ⟨1576166, by rfl⟩ : syracuseStep 2101555 = 3152333) B3152333
theorem B2953523 : Blo 1748575 2953523 := bstep (se 1 (by rfl) ⟨2215142, by rfl⟩ : syracuseStep 2953523 = 4430285) B4430285
theorem B2625857 : Blo 1748575 2625857 := bstep (se 2 (by rfl) ⟨984696, by rfl⟩ : syracuseStep 2625857 = 1969393) B1969393
theorem B1749315 : Blo 1748575 1749315 := bstep (se 1 (by rfl) ⟨1311986, by rfl⟩ : syracuseStep 1749315 = 2623973) B2623973
theorem B4731203 : Blo 1748575 4731203 := bstep (se 1 (by rfl) ⟨3548402, by rfl⟩ : syracuseStep 4731203 = 7096805) B7096805
theorem B1749331 : Blo 1748575 1749331 := bstep (se 1 (by rfl) ⟨1311998, by rfl⟩ : syracuseStep 1749331 = 2623997) B2623997
theorem B1749347 : Blo 1748575 1749347 := bstep (se 1 (by rfl) ⟨1312010, by rfl⟩ : syracuseStep 1749347 = 2624021) B2624021
theorem B1749363 : Blo 1748575 1749363 := bstep (se 1 (by rfl) ⟨1312022, by rfl⟩ : syracuseStep 1749363 = 2624045) B2624045
theorem B1749379 : Blo 1748575 1749379 := bstep (se 1 (by rfl) ⟨1312034, by rfl⟩ : syracuseStep 1749379 = 2624069) B2624069
theorem B8638861 : Blo 1748575 8638861 := bstep (se 3 (by rfl) ⟨1619786, by rfl⟩ : syracuseStep 8638861 = 3239573) B3239573
theorem B1749395 : Blo 1748575 1749395 := bstep (se 1 (by rfl) ⟨1312046, by rfl⟩ : syracuseStep 1749395 = 2624093) B2624093
theorem B1749411 : Blo 1748575 1749411 := bstep (se 1 (by rfl) ⟨1312058, by rfl⟩ : syracuseStep 1749411 = 2624117) B2624117
theorem B4428209 : Blo 1748575 4428209 := bstep (se 2 (by rfl) ⟨1660578, by rfl⟩ : syracuseStep 4428209 = 3321157) B3321157
theorem B3936689 : Blo 1748575 3936689 := bstep (se 2 (by rfl) ⟨1476258, by rfl⟩ : syracuseStep 3936689 = 2952517) B2952517
theorem B1749427 : Blo 1748575 1749427 := bstep (se 1 (by rfl) ⟨1312070, by rfl⟩ : syracuseStep 1749427 = 2624141) B2624141
theorem B3322289 : Blo 1748575 3322289 := bstep (se 2 (by rfl) ⟨1245858, by rfl⟩ : syracuseStep 3322289 = 2491717) B2491717
theorem B2953651 : Blo 1748575 2953651 := bstep (se 1 (by rfl) ⟨2215238, by rfl⟩ : syracuseStep 2953651 = 4430477) B4430477
theorem B1749443 : Blo 1748575 1749443 := bstep (se 1 (by rfl) ⟨1312082, by rfl⟩ : syracuseStep 1749443 = 2624165) B2624165
theorem B3936707 : Blo 1748575 3936707 := bstep (se 1 (by rfl) ⟨2952530, by rfl⟩ : syracuseStep 3936707 = 5905061) B5905061
theorem B12612037 : Blo 1748575 12612037 := bstep (se 4 (by rfl) ⟨1182378, by rfl⟩ : syracuseStep 12612037 = 2364757) B2364757
theorem B1749459 : Blo 1748575 1749459 := bstep (se 1 (by rfl) ⟨1312094, by rfl⟩ : syracuseStep 1749459 = 2624189) B2624189
theorem B1749475 : Blo 1748575 1749475 := bstep (se 1 (by rfl) ⟨1312106, by rfl⟩ : syracuseStep 1749475 = 2624213) B2624213
theorem B1749491 : Blo 1748575 1749491 := bstep (se 1 (by rfl) ⟨1312118, by rfl⟩ : syracuseStep 1749491 = 2624237) B2624237
theorem B1749507 : Blo 1748575 1749507 := bstep (se 1 (by rfl) ⟨1312130, by rfl⟩ : syracuseStep 1749507 = 2624261) B2624261
theorem B1749523 : Blo 1748575 1749523 := bstep (se 1 (by rfl) ⟨1312142, by rfl⟩ : syracuseStep 1749523 = 2624285) B2624285
theorem B1749539 : Blo 1748575 1749539 := bstep (se 1 (by rfl) ⟨1312154, by rfl⟩ : syracuseStep 1749539 = 2624309) B2624309
theorem B1749555 : Blo 1748575 1749555 := bstep (se 1 (by rfl) ⟨1312166, by rfl⟩ : syracuseStep 1749555 = 2624333) B2624333
theorem B1749571 : Blo 1748575 1749571 := bstep (se 1 (by rfl) ⟨1312178, by rfl⟩ : syracuseStep 1749571 = 2624357) B2624357
theorem B2953793 : Blo 1748575 2953793 := bstep (se 2 (by rfl) ⟨1107672, by rfl⟩ : syracuseStep 2953793 = 2215345) B2215345
theorem B5395025 : Blo 1748575 5395025 := bstep (se 2 (by rfl) ⟨2023134, by rfl⟩ : syracuseStep 5395025 = 4046269) B4046269
theorem B1749587 : Blo 1748575 1749587 := bstep (se 1 (by rfl) ⟨1312190, by rfl⟩ : syracuseStep 1749587 = 2624381) B2624381
theorem B1749603 : Blo 1748575 1749603 := bstep (se 1 (by rfl) ⟨1312202, by rfl⟩ : syracuseStep 1749603 = 2624405) B2624405
theorem B1749619 : Blo 1748575 1749619 := bstep (se 1 (by rfl) ⟨1312214, by rfl⟩ : syracuseStep 1749619 = 2624429) B2624429
theorem B1749635 : Blo 1748575 1749635 := bstep (se 1 (by rfl) ⟨1312226, by rfl⟩ : syracuseStep 1749635 = 2624453) B2624453
theorem B1749651 : Blo 1748575 1749651 := bstep (se 1 (by rfl) ⟨1312238, by rfl⟩ : syracuseStep 1749651 = 2624477) B2624477
theorem B1749667 : Blo 1748575 1749667 := bstep (se 1 (by rfl) ⟨1312250, by rfl⟩ : syracuseStep 1749667 = 2624501) B2624501
theorem B1749683 : Blo 1748575 1749683 := bstep (se 1 (by rfl) ⟨1312262, by rfl⟩ : syracuseStep 1749683 = 2624525) B2624525
theorem B2953921 : Blo 1748575 2953921 := bstep (se 2 (by rfl) ⟨1107720, by rfl⟩ : syracuseStep 2953921 = 2215441) B2215441
theorem B1749699 : Blo 1748575 1749699 := bstep (se 1 (by rfl) ⟨1312274, by rfl⟩ : syracuseStep 1749699 = 2624549) B2624549
theorem B22418117 : Blo 1748575 22418117 := bstep (se 4 (by rfl) ⟨2101698, by rfl⟩ : syracuseStep 22418117 = 4203397) B4203397
theorem B3936977 : Blo 1748575 3936977 := bstep (se 2 (by rfl) ⟨1476366, by rfl⟩ : syracuseStep 3936977 = 2952733) B2952733
theorem B1749715 : Blo 1748575 1749715 := bstep (se 1 (by rfl) ⟨1312286, by rfl⟩ : syracuseStep 1749715 = 2624573) B2624573
theorem B1749731 : Blo 1748575 1749731 := bstep (se 1 (by rfl) ⟨1312298, by rfl⟩ : syracuseStep 1749731 = 2624597) B2624597
theorem B3936995 : Blo 1748575 3936995 := bstep (se 1 (by rfl) ⟨2952746, by rfl⟩ : syracuseStep 3936995 = 5905493) B5905493
theorem B2953955 : Blo 1748575 2953955 := bstep (se 1 (by rfl) ⟨2215466, by rfl⟩ : syracuseStep 2953955 = 4430933) B4430933
theorem B1749747 : Blo 1748575 1749747 := bstep (se 1 (by rfl) ⟨1312310, by rfl⟩ : syracuseStep 1749747 = 2624621) B2624621
theorem B1749763 : Blo 1748575 1749763 := bstep (se 1 (by rfl) ⟨1312322, by rfl⟩ : syracuseStep 1749763 = 2624645) B2624645
theorem B9966341 : Blo 1748575 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B5903117 : Blo 1748575 5903117 := bstep (se 3 (by rfl) ⟨1106834, by rfl⟩ : syracuseStep 5903117 = 2213669) B2213669
theorem B1749779 : Blo 1748575 1749779 := bstep (se 1 (by rfl) ⟨1312334, by rfl⟩ : syracuseStep 1749779 = 2624669) B2624669
theorem B1749795 : Blo 1748575 1749795 := bstep (se 1 (by rfl) ⟨1312346, by rfl⟩ : syracuseStep 1749795 = 2624693) B2624693
theorem B1749811 : Blo 1748575 1749811 := bstep (se 1 (by rfl) ⟨1312358, by rfl⟩ : syracuseStep 1749811 = 2624717) B2624717
theorem B5903171 : Blo 1748575 5903171 := bstep (se 1 (by rfl) ⟨4427378, by rfl⟩ : syracuseStep 5903171 = 8854757) B8854757
theorem B1749827 : Blo 1748575 1749827 := bstep (se 1 (by rfl) ⟨1312370, by rfl⟩ : syracuseStep 1749827 = 2624741) B2624741
theorem B3322691 : Blo 1748575 3322691 := bstep (se 1 (by rfl) ⟨2492018, by rfl⟩ : syracuseStep 3322691 = 4984037) B4984037
theorem B1749843 : Blo 1748575 1749843 := bstep (se 1 (by rfl) ⟨1312382, by rfl⟩ : syracuseStep 1749843 = 2624765) B2624765
theorem B1749859 : Blo 1748575 1749859 := bstep (se 1 (by rfl) ⟨1312394, by rfl⟩ : syracuseStep 1749859 = 2624789) B2624789
theorem B2954083 : Blo 1748575 2954083 := bstep (se 1 (by rfl) ⟨2215562, by rfl⟩ : syracuseStep 2954083 = 4431125) B4431125
theorem B1749875 : Blo 1748575 1749875 := bstep (se 1 (by rfl) ⟨1312406, by rfl⟩ : syracuseStep 1749875 = 2624813) B2624813
theorem B1749891 : Blo 1748575 1749891 := bstep (se 1 (by rfl) ⟨1312418, by rfl⟩ : syracuseStep 1749891 = 2624837) B2624837
theorem B1749907 : Blo 1748575 1749907 := bstep (se 1 (by rfl) ⟨1312430, by rfl⟩ : syracuseStep 1749907 = 2624861) B2624861
theorem B1749923 : Blo 1748575 1749923 := bstep (se 1 (by rfl) ⟨1312442, by rfl⟩ : syracuseStep 1749923 = 2624885) B2624885
theorem B1749939 : Blo 1748575 1749939 := bstep (se 1 (by rfl) ⟨1312454, by rfl⟩ : syracuseStep 1749939 = 2624909) B2624909
theorem B1749955 : Blo 1748575 1749955 := bstep (se 1 (by rfl) ⟨1312466, by rfl⟩ : syracuseStep 1749955 = 2624933) B2624933
theorem B1749971 : Blo 1748575 1749971 := bstep (se 1 (by rfl) ⟨1312478, by rfl⟩ : syracuseStep 1749971 = 2624957) B2624957
theorem B13284323 : Blo 1748575 13284323 := bstep (se 1 (by rfl) ⟨9963242, by rfl⟩ : syracuseStep 13284323 = 19926485) B19926485
theorem B1749987 : Blo 1748575 1749987 := bstep (se 1 (by rfl) ⟨1312490, by rfl⟩ : syracuseStep 1749987 = 2624981) B2624981
theorem B5116913 : Blo 1748575 5116913 := bstep (se 2 (by rfl) ⟨1918842, by rfl⟩ : syracuseStep 5116913 = 3837685) B3837685
theorem B3937265 : Blo 1748575 3937265 := bstep (se 2 (by rfl) ⟨1476474, by rfl⟩ : syracuseStep 3937265 = 2952949) B2952949
theorem B1750003 : Blo 1748575 1750003 := bstep (se 1 (by rfl) ⟨1312502, by rfl⟩ : syracuseStep 1750003 = 2625005) B2625005
theorem B2659331 : Blo 1748575 2659331 := bstep (se 1 (by rfl) ⟨1994498, by rfl⟩ : syracuseStep 2659331 = 3988997) B3988997
theorem B3937283 : Blo 1748575 3937283 := bstep (se 1 (by rfl) ⟨2952962, by rfl⟩ : syracuseStep 3937283 = 5905925) B5905925
theorem B1750019 : Blo 1748575 1750019 := bstep (se 1 (by rfl) ⟨1312514, by rfl⟩ : syracuseStep 1750019 = 2625029) B2625029
theorem B1750035 : Blo 1748575 1750035 := bstep (se 1 (by rfl) ⟨1312526, by rfl⟩ : syracuseStep 1750035 = 2625053) B2625053
theorem B1750051 : Blo 1748575 1750051 := bstep (se 1 (by rfl) ⟨1312538, by rfl⟩ : syracuseStep 1750051 = 2625077) B2625077
theorem B1750067 : Blo 1748575 1750067 := bstep (se 1 (by rfl) ⟨1312550, by rfl⟩ : syracuseStep 1750067 = 2625101) B2625101
theorem B2397251 : Blo 1748575 2397251 := bstep (se 1 (by rfl) ⟨1797938, by rfl⟩ : syracuseStep 2397251 = 3595877) B3595877
theorem B1750083 : Blo 1748575 1750083 := bstep (se 1 (by rfl) ⟨1312562, by rfl⟩ : syracuseStep 1750083 = 2625125) B2625125
theorem B5903441 : Blo 1748575 5903441 := bstep (se 2 (by rfl) ⟨2213790, by rfl⟩ : syracuseStep 5903441 = 4427581) B4427581
theorem B1750099 : Blo 1748575 1750099 := bstep (se 1 (by rfl) ⟨1312574, by rfl⟩ : syracuseStep 1750099 = 2625149) B2625149
theorem B1750115 : Blo 1748575 1750115 := bstep (se 1 (by rfl) ⟨1312586, by rfl⟩ : syracuseStep 1750115 = 2625173) B2625173
theorem B1750131 : Blo 1748575 1750131 := bstep (se 1 (by rfl) ⟨1312598, by rfl⟩ : syracuseStep 1750131 = 2625197) B2625197
theorem B1750147 : Blo 1748575 1750147 := bstep (se 1 (by rfl) ⟨1312610, by rfl⟩ : syracuseStep 1750147 = 2625221) B2625221
theorem B2364563 : Blo 1748575 2364563 := bstep (se 1 (by rfl) ⟨1773422, by rfl⟩ : syracuseStep 2364563 = 3546845) B3546845
theorem B1750163 : Blo 1748575 1750163 := bstep (se 1 (by rfl) ⟨1312622, by rfl⟩ : syracuseStep 1750163 = 2625245) B2625245
theorem B1750179 : Blo 1748575 1750179 := bstep (se 1 (by rfl) ⟨1312634, by rfl⟩ : syracuseStep 1750179 = 2625269) B2625269
theorem B1750195 : Blo 1748575 1750195 := bstep (se 1 (by rfl) ⟨1312646, by rfl⟩ : syracuseStep 1750195 = 2625293) B2625293
theorem B1750211 : Blo 1748575 1750211 := bstep (se 1 (by rfl) ⟨1312658, by rfl⟩ : syracuseStep 1750211 = 2625317) B2625317
theorem B9966797 : Blo 1748575 9966797 := bstep (se 3 (by rfl) ⟨1868774, by rfl⟩ : syracuseStep 9966797 = 3737549) B3737549
theorem B1750227 : Blo 1748575 1750227 := bstep (se 1 (by rfl) ⟨1312670, by rfl⟩ : syracuseStep 1750227 = 2625341) B2625341
theorem B1750243 : Blo 1748575 1750243 := bstep (se 1 (by rfl) ⟨1312682, by rfl⟩ : syracuseStep 1750243 = 2625365) B2625365
theorem B8860913 : Blo 1748575 8860913 := bstep (se 2 (by rfl) ⟨3322842, by rfl⟩ : syracuseStep 8860913 = 6645685) B6645685
theorem B1750259 : Blo 1748575 1750259 := bstep (se 1 (by rfl) ⟨1312694, by rfl⟩ : syracuseStep 1750259 = 2625389) B2625389
theorem B1750275 : Blo 1748575 1750275 := bstep (se 1 (by rfl) ⟨1312706, by rfl⟩ : syracuseStep 1750275 = 2625413) B2625413
theorem B3937553 : Blo 1748575 3937553 := bstep (se 2 (by rfl) ⟨1476582, by rfl⟩ : syracuseStep 3937553 = 2953165) B2953165
theorem B1750291 : Blo 1748575 1750291 := bstep (se 1 (by rfl) ⟨1312718, by rfl⟩ : syracuseStep 1750291 = 2625437) B2625437
theorem B3937571 : Blo 1748575 3937571 := bstep (se 1 (by rfl) ⟨2953178, by rfl⟩ : syracuseStep 3937571 = 5906357) B5906357
theorem B5322019 : Blo 1748575 5322019 := bstep (se 1 (by rfl) ⟨3991514, by rfl⟩ : syracuseStep 5322019 = 7983029) B7983029
theorem B1750307 : Blo 1748575 1750307 := bstep (se 1 (by rfl) ⟨1312730, by rfl⟩ : syracuseStep 1750307 = 2625461) B2625461
theorem B1750323 : Blo 1748575 1750323 := bstep (se 1 (by rfl) ⟨1312742, by rfl⟩ : syracuseStep 1750323 = 2625485) B2625485
theorem B1750339 : Blo 1748575 1750339 := bstep (se 1 (by rfl) ⟨1312754, by rfl⟩ : syracuseStep 1750339 = 2625509) B2625509
theorem B9958733 : Blo 1748575 9958733 := bstep (se 3 (by rfl) ⟨1867262, by rfl⟩ : syracuseStep 9958733 = 3734525) B3734525
theorem B8852813 : Blo 1748575 8852813 := bstep (se 3 (by rfl) ⟨1659902, by rfl⟩ : syracuseStep 8852813 = 3319805) B3319805
theorem B1750355 : Blo 1748575 1750355 := bstep (se 1 (by rfl) ⟨1312766, by rfl⟩ : syracuseStep 1750355 = 2625533) B2625533
theorem B1750371 : Blo 1748575 1750371 := bstep (se 1 (by rfl) ⟨1312778, by rfl⟩ : syracuseStep 1750371 = 2625557) B2625557
theorem B1750387 : Blo 1748575 1750387 := bstep (se 1 (by rfl) ⟨1312790, by rfl⟩ : syracuseStep 1750387 = 2625581) B2625581
theorem B1750403 : Blo 1748575 1750403 := bstep (se 1 (by rfl) ⟨1312802, by rfl⟩ : syracuseStep 1750403 = 2625605) B2625605
theorem B25228685 : Blo 1748575 25228685 := bstep (se 3 (by rfl) ⟨4730378, by rfl⟩ : syracuseStep 25228685 = 9460757) B9460757
theorem B4429201 : Blo 1748575 4429201 := bstep (se 2 (by rfl) ⟨1660950, by rfl⟩ : syracuseStep 4429201 = 3321901) B3321901
theorem B1750419 : Blo 1748575 1750419 := bstep (se 1 (by rfl) ⟨1312814, by rfl⟩ : syracuseStep 1750419 = 2625629) B2625629
theorem B1750435 : Blo 1748575 1750435 := bstep (se 1 (by rfl) ⟨1312826, by rfl⟩ : syracuseStep 1750435 = 2625653) B2625653
theorem B1750451 : Blo 1748575 1750451 := bstep (se 1 (by rfl) ⟨1312838, by rfl⟩ : syracuseStep 1750451 = 2625677) B2625677
theorem B1750467 : Blo 1748575 1750467 := bstep (se 1 (by rfl) ⟨1312850, by rfl⟩ : syracuseStep 1750467 = 2625701) B2625701
theorem B1750483 : Blo 1748575 1750483 := bstep (se 1 (by rfl) ⟨1312862, by rfl⟩ : syracuseStep 1750483 = 2625725) B2625725
theorem B1750499 : Blo 1748575 1750499 := bstep (se 1 (by rfl) ⟨1312874, by rfl⟩ : syracuseStep 1750499 = 2625749) B2625749
theorem B1750515 : Blo 1748575 1750515 := bstep (se 1 (by rfl) ⟨1312886, by rfl⟩ : syracuseStep 1750515 = 2625773) B2625773
theorem B1750531 : Blo 1748575 1750531 := bstep (se 1 (by rfl) ⟨1312898, by rfl⟩ : syracuseStep 1750531 = 2625797) B2625797
theorem B1750547 : Blo 1748575 1750547 := bstep (se 1 (by rfl) ⟨1312910, by rfl⟩ : syracuseStep 1750547 = 2625821) B2625821
theorem B1750563 : Blo 1748575 1750563 := bstep (se 1 (by rfl) ⟨1312922, by rfl⟩ : syracuseStep 1750563 = 2625845) B2625845
theorem B3937841 : Blo 1748575 3937841 := bstep (se 2 (by rfl) ⟨1476690, by rfl⟩ : syracuseStep 3937841 = 2953381) B2953381
theorem B3937859 : Blo 1748575 3937859 := bstep (se 1 (by rfl) ⟨2953394, by rfl⟩ : syracuseStep 3937859 = 5906789) B5906789
theorem B5903981 : Blo 1748575 5903981 := bstep (se 3 (by rfl) ⟨1106996, by rfl⟩ : syracuseStep 5903981 = 2213993) B2213993
theorem B5904035 : Blo 1748575 5904035 := bstep (se 1 (by rfl) ⟨4428026, by rfl⟩ : syracuseStep 5904035 = 8856053) B8856053
theorem B4429475 : Blo 1748575 4429475 := bstep (se 1 (by rfl) ⟨3322106, by rfl⟩ : syracuseStep 4429475 = 6644213) B6644213
theorem B19920653 : Blo 1748575 19920653 := bstep (se 3 (by rfl) ⟨3735122, by rfl⟩ : syracuseStep 19920653 = 7470245) B7470245
theorem B3938129 : Blo 1748575 3938129 := bstep (se 2 (by rfl) ⟨1476798, by rfl⟩ : syracuseStep 3938129 = 2953597) B2953597
theorem B4429667 : Blo 1748575 4429667 := bstep (se 1 (by rfl) ⟨3322250, by rfl⟩ : syracuseStep 4429667 = 6644501) B6644501
theorem B3938147 : Blo 1748575 3938147 := bstep (se 1 (by rfl) ⟨2953610, by rfl⟩ : syracuseStep 3938147 = 5907221) B5907221
theorem B2398097 : Blo 1748575 2398097 := bstep (se 2 (by rfl) ⟨899286, by rfl⟩ : syracuseStep 2398097 = 1798573) B1798573
theorem B6641585 : Blo 1748575 6641585 := bstep (se 2 (by rfl) ⟨2490594, by rfl⟩ : syracuseStep 6641585 = 4981189) B4981189
theorem B5904305 : Blo 1748575 5904305 := bstep (se 2 (by rfl) ⟨2214114, by rfl⟩ : syracuseStep 5904305 = 4428229) B4428229
theorem B11368433 : Blo 1748575 11368433 := bstep (se 2 (by rfl) ⟨4263162, by rfl⟩ : syracuseStep 11368433 = 8526325) B8526325
theorem B2660449 : Blo 1748575 2660449 := bstep (se 2 (by rfl) ⟨997668, by rfl⟩ : syracuseStep 2660449 = 1995337) B1995337
theorem B3938417 : Blo 1748575 3938417 := bstep (se 2 (by rfl) ⟨1476906, by rfl⟩ : syracuseStep 3938417 = 2953813) B2953813
theorem B3938435 : Blo 1748575 3938435 := bstep (se 1 (by rfl) ⟨2953826, by rfl⟩ : syracuseStep 3938435 = 5907653) B5907653
theorem B5986669 : Blo 1748575 5986669 := bstep (se 3 (by rfl) ⟨1122500, by rfl⟩ : syracuseStep 5986669 = 2245001) B2245001
theorem B7469425 : Blo 1748575 7469425 := bstep (se 2 (by rfl) ⟨2801034, by rfl⟩ : syracuseStep 7469425 = 5602069) B5602069
theorem B3938705 : Blo 1748575 3938705 := bstep (se 2 (by rfl) ⟨1477014, by rfl⟩ : syracuseStep 3938705 = 2954029) B2954029
theorem B3938723 : Blo 1748575 3938723 := bstep (se 1 (by rfl) ⟨2954042, by rfl⟩ : syracuseStep 3938723 = 5908085) B5908085
theorem B5904845 : Blo 1748575 5904845 := bstep (se 3 (by rfl) ⟨1107158, by rfl⟩ : syracuseStep 5904845 = 2214317) B2214317
theorem B5904899 : Blo 1748575 5904899 := bstep (se 1 (by rfl) ⟨4428674, by rfl⟩ : syracuseStep 5904899 = 8857349) B8857349
theorem B88627765 : Blo 1748575 88627765 := bstep (se 5 (by rfl) ⟨4154426, by rfl⟩ : syracuseStep 88627765 = 8308853) B8308853
theorem B5601955 : Blo 1748575 5601955 := bstep (se 1 (by rfl) ⟨4201466, by rfl⟩ : syracuseStep 5601955 = 8402933) B8402933
theorem B5905169 : Blo 1748575 5905169 := bstep (se 2 (by rfl) ⟨2214438, by rfl⟩ : syracuseStep 5905169 = 4428877) B4428877
theorem B4430609 : Blo 1748575 4430609 := bstep (se 2 (by rfl) ⟨1661478, by rfl⟩ : syracuseStep 4430609 = 3322957) B3322957
theorem B4430659 : Blo 1748575 4430659 := bstep (se 1 (by rfl) ⟨3322994, by rfl⟩ : syracuseStep 4430659 = 6645989) B6645989
theorem B16169827 : Blo 1748575 16169827 := bstep (se 1 (by rfl) ⟨12127370, by rfl⟩ : syracuseStep 16169827 = 24254741) B24254741
theorem B4201361 : Blo 1748575 4201361 := bstep (se 2 (by rfl) ⟨1575510, by rfl⟩ : syracuseStep 4201361 = 3151021) B3151021
theorem B9714637 : Blo 1748575 9714637 := bstep (se 3 (by rfl) ⟨1821494, by rfl⟩ : syracuseStep 9714637 = 3642989) B3642989
theorem B4430801 : Blo 1748575 4430801 := bstep (se 2 (by rfl) ⟨1661550, by rfl⟩ : syracuseStep 4430801 = 3323101) B3323101
theorem B4201475 : Blo 1748575 4201475 := bstep (se 1 (by rfl) ⟨3151106, by rfl⟩ : syracuseStep 4201475 = 6302213) B6302213
theorem B4979789 : Blo 1748575 4979789 := bstep (se 3 (by rfl) ⟨933710, by rfl⟩ : syracuseStep 4979789 = 1867421) B1867421
theorem B4201649 : Blo 1748575 4201649 := bstep (se 2 (by rfl) ⟨1575618, by rfl⟩ : syracuseStep 4201649 = 3151237) B3151237
theorem B21290165 : Blo 1748575 21290165 := bstep (se 5 (by rfl) ⟨997976, by rfl⟩ : syracuseStep 21290165 = 1995953) B1995953
theorem B19176689 : Blo 1748575 19176689 := bstep (se 2 (by rfl) ⟨7191258, by rfl⟩ : syracuseStep 19176689 = 14382517) B14382517
theorem B2661617 : Blo 1748575 2661617 := bstep (se 2 (by rfl) ⟨998106, by rfl⟩ : syracuseStep 2661617 = 1996213) B1996213
theorem B4979981 : Blo 1748575 4979981 := bstep (se 3 (by rfl) ⟨933746, by rfl⟩ : syracuseStep 4979981 = 1867493) B1867493
theorem B5905709 : Blo 1748575 5905709 := bstep (se 3 (by rfl) ⟨1107320, by rfl⟩ : syracuseStep 5905709 = 2214641) B2214641
theorem B6643043 : Blo 1748575 6643043 := bstep (se 1 (by rfl) ⟨4982282, by rfl⟩ : syracuseStep 6643043 = 9964565) B9964565
theorem B5905763 : Blo 1748575 5905763 := bstep (se 1 (by rfl) ⟨4429322, by rfl⟩ : syracuseStep 5905763 = 8858645) B8858645
theorem B12615011 : Blo 1748575 12615011 := bstep (se 1 (by rfl) ⟨9461258, by rfl⟩ : syracuseStep 12615011 = 18922517) B18922517
theorem B10640803 : Blo 1748575 10640803 := bstep (se 1 (by rfl) ⟨7980602, by rfl⟩ : syracuseStep 10640803 = 15961205) B15961205
theorem B15957445 : Blo 1748575 15957445 := bstep (se 4 (by rfl) ⟨1496010, by rfl⟩ : syracuseStep 15957445 = 2992021) B2992021
theorem B5602787 : Blo 1748575 5602787 := bstep (se 1 (by rfl) ⟨4202090, by rfl⟩ : syracuseStep 5602787 = 8404181) B8404181
theorem B9960965 : Blo 1748575 9960965 := bstep (se 4 (by rfl) ⟨933840, by rfl⟩ : syracuseStep 9960965 = 1867681) B1867681
theorem B3735089 : Blo 1748575 3735089 := bstep (se 2 (by rfl) ⟨1400658, by rfl⟩ : syracuseStep 3735089 = 2801317) B2801317
theorem B1867331 : Blo 1748575 1867331 := bstep (se 1 (by rfl) ⟨1400498, by rfl⟩ : syracuseStep 1867331 = 2800997) B2800997
theorem B5906033 : Blo 1748575 5906033 := bstep (se 2 (by rfl) ⟨2214762, by rfl⟩ : syracuseStep 5906033 = 4429525) B4429525
theorem B1867459 : Blo 1748575 1867459 := bstep (se 1 (by rfl) ⟨1400594, by rfl⟩ : syracuseStep 1867459 = 2801189) B2801189
theorem B6307633 : Blo 1748575 6307633 := bstep (se 2 (by rfl) ⟨2365362, by rfl⟩ : syracuseStep 6307633 = 4730725) B4730725
theorem B5603185 : Blo 1748575 5603185 := bstep (se 2 (by rfl) ⟨2101194, by rfl⟩ : syracuseStep 5603185 = 4202389) B4202389
theorem B32800625 : Blo 1748575 32800625 := bstep (se 2 (by rfl) ⟨12300234, by rfl⟩ : syracuseStep 32800625 = 24600469) B24600469
theorem B2490259 : Blo 1748575 2490259 := bstep (se 1 (by rfl) ⟨1867694, by rfl⟩ : syracuseStep 2490259 = 3735389) B3735389
theorem B5603249 : Blo 1748575 5603249 := bstep (se 2 (by rfl) ⟨2101218, by rfl⟩ : syracuseStep 5603249 = 4202437) B4202437
theorem B2490355 : Blo 1748575 2490355 := bstep (se 1 (by rfl) ⟨1867766, by rfl⟩ : syracuseStep 2490355 = 3735533) B3735533
theorem B3547265 : Blo 1748575 3547265 := bstep (se 2 (by rfl) ⟨1330224, by rfl⟩ : syracuseStep 3547265 = 2660449) B2660449
theorem B2490583 : Blo 1748575 2490583 := bstep (se 1 (by rfl) ⟨1867937, by rfl⟩ : syracuseStep 2490583 = 3735875) B3735875
theorem B3154135 : Blo 1748575 3154135 := bstep (se 1 (by rfl) ⟨2365601, by rfl⟩ : syracuseStep 3154135 = 4731203) B4731203
theorem B2801881 : Blo 1748575 2801881 := bstep (se 2 (by rfl) ⟨1050705, by rfl⟩ : syracuseStep 2801881 = 2101411) B2101411
theorem B1868023 : Blo 1748575 1868023 := bstep (se 1 (by rfl) ⟨1401017, by rfl⟩ : syracuseStep 1868023 = 2802035) B2802035
theorem B13287725 : Blo 1748575 13287725 := bstep (se 3 (by rfl) ⟨2491448, by rfl⟩ : syracuseStep 13287725 = 4982897) B4982897
theorem B9969965 : Blo 1748575 9969965 := bstep (se 3 (by rfl) ⟨1869368, by rfl⟩ : syracuseStep 9969965 = 3738737) B3738737
theorem B3596683 : Blo 1748575 3596683 := bstep (se 1 (by rfl) ⟨2697512, by rfl⟩ : syracuseStep 3596683 = 5395025) B5395025
theorem B7471511 : Blo 1748575 7471511 := bstep (se 1 (by rfl) ⟨5603633, by rfl⟩ : syracuseStep 7471511 = 11207267) B11207267
theorem B1868279 : Blo 1748575 1868279 := bstep (se 1 (by rfl) ⟨1401209, by rfl⟩ : syracuseStep 1868279 = 2802419) B2802419
theorem B6644227 : Blo 1748575 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B11518481 : Blo 1748575 11518481 := bstep (se 2 (by rfl) ⟨4319430, by rfl⟩ : syracuseStep 11518481 = 8638861) B8638861
theorem B8856215 : Blo 1748575 8856215 := bstep (se 1 (by rfl) ⟨6642161, by rfl⟩ : syracuseStep 8856215 = 13284323) B13284323
theorem B13279949 : Blo 1748575 13279949 := bstep (se 3 (by rfl) ⟨2489990, by rfl⟩ : syracuseStep 13279949 = 4979981) B4979981
theorem B118170353 : Blo 1748575 118170353 := bstep (se 2 (by rfl) ⟨44313882, by rfl⟩ : syracuseStep 118170353 = 88627765) B88627765
theorem B6644531 : Blo 1748575 6644531 := bstep (se 1 (by rfl) ⟨4983398, by rfl⟩ : syracuseStep 6644531 = 9966797) B9966797
theorem B5907275 : Blo 1748575 5907275 := bstep (se 1 (by rfl) ⟨4430456, by rfl⟩ : syracuseStep 5907275 = 8860913) B8860913
theorem B2491403 : Blo 1748575 2491403 := bstep (se 1 (by rfl) ⟨1868552, by rfl⟩ : syracuseStep 2491403 = 3737105) B3737105
theorem B1868843 : Blo 1748575 1868843 := bstep (se 1 (by rfl) ⟨1401632, by rfl⟩ : syracuseStep 1868843 = 2803265) B2803265
theorem B1967179 : Blo 1748575 1967179 := bstep (se 1 (by rfl) ⟨1475384, by rfl⟩ : syracuseStep 1967179 = 2950769) B2950769
theorem B5604427 : Blo 1748575 5604427 := bstep (se 1 (by rfl) ⟨4203320, by rfl⟩ : syracuseStep 5604427 = 8406641) B8406641
theorem B5907545 : Blo 1748575 5907545 := bstep (se 2 (by rfl) ⟨2215329, by rfl⟩ : syracuseStep 5907545 = 4430659) B4430659
theorem B9847939 : Blo 1748575 9847939 := bstep (se 1 (by rfl) ⟨7385954, by rfl⟩ : syracuseStep 9847939 = 14771909) B14771909
theorem B3736729 : Blo 1748575 3736729 := bstep (se 2 (by rfl) ⟨1401273, by rfl⟩ : syracuseStep 3736729 = 2802547) B2802547
theorem B13280435 : Blo 1748575 13280435 := bstep (se 1 (by rfl) ⟨9960326, by rfl⟩ : syracuseStep 13280435 = 19920653) B19920653
theorem B9962675 : Blo 1748575 9962675 := bstep (se 1 (by rfl) ⟨7472006, by rfl⟩ : syracuseStep 9962675 = 14944013) B14944013
theorem B1967287 : Blo 1748575 1967287 := bstep (se 1 (by rfl) ⟨1475465, by rfl⟩ : syracuseStep 1967287 = 2950931) B2950931
theorem B5604659 : Blo 1748575 5604659 := bstep (se 1 (by rfl) ⟨4203494, by rfl⟩ : syracuseStep 5604659 = 8406989) B8406989
theorem B7578955 : Blo 1748575 7578955 := bstep (se 1 (by rfl) ⟨5684216, by rfl⟩ : syracuseStep 7578955 = 11368433) B11368433
theorem B28755299 : Blo 1748575 28755299 := bstep (se 1 (by rfl) ⟨21566474, by rfl⟩ : syracuseStep 28755299 = 43132949) B43132949
theorem B1967467 : Blo 1748575 1967467 := bstep (se 1 (by rfl) ⟨1475600, by rfl⟩ : syracuseStep 1967467 = 2951201) B2951201
theorem B14378417 : Blo 1748575 14378417 := bstep (se 2 (by rfl) ⟨5391906, by rfl⟩ : syracuseStep 14378417 = 10783813) B10783813
theorem B6645185 : Blo 1748575 6645185 := bstep (se 2 (by rfl) ⟨2491944, by rfl⟩ : syracuseStep 6645185 = 4983889) B4983889
theorem B2622923 : Blo 1748575 2622923 := bstep (se 1 (by rfl) ⟨1967192, by rfl⟩ : syracuseStep 2622923 = 3934385) B3934385
theorem B2622935 : Blo 1748575 2622935 := bstep (se 1 (by rfl) ⟨1967201, by rfl⟩ : syracuseStep 2622935 = 3934403) B3934403
theorem B2213335 : Blo 1748575 2213335 := bstep (se 1 (by rfl) ⟨1660001, by rfl⟩ : syracuseStep 2213335 = 3320003) B3320003
theorem B1967575 : Blo 1748575 1967575 := bstep (se 1 (by rfl) ⟨1475681, by rfl⟩ : syracuseStep 1967575 = 2951363) B2951363
theorem B2623001 : Blo 1748575 2623001 := bstep (se 2 (by rfl) ⟨983625, by rfl⟩ : syracuseStep 2623001 = 1967251) B1967251
theorem B11208293 : Blo 1748575 11208293 := bstep (se 4 (by rfl) ⟨1050777, by rfl⟩ : syracuseStep 11208293 = 2101555) B2101555
theorem B2623115 : Blo 1748575 2623115 := bstep (se 1 (by rfl) ⟨1967336, by rfl⟩ : syracuseStep 2623115 = 3934673) B3934673
theorem B1967755 : Blo 1748575 1967755 := bstep (se 1 (by rfl) ⟨1475816, by rfl⟩ : syracuseStep 1967755 = 2951633) B2951633
theorem B2623127 : Blo 1748575 2623127 := bstep (se 1 (by rfl) ⟨1967345, by rfl⟩ : syracuseStep 2623127 = 3934691) B3934691
theorem B4982465 : Blo 1748575 4982465 := bstep (se 2 (by rfl) ⟨1868424, by rfl⟩ : syracuseStep 4982465 = 3736849) B3736849
theorem B7472843 : Blo 1748575 7472843 := bstep (se 1 (by rfl) ⟨5604632, by rfl⟩ : syracuseStep 7472843 = 11209265) B11209265
theorem B2623193 : Blo 1748575 2623193 := bstep (se 2 (by rfl) ⟨983697, by rfl⟩ : syracuseStep 2623193 = 1967395) B1967395
theorem B7096025 : Blo 1748575 7096025 := bstep (se 2 (by rfl) ⟨2661009, by rfl⟩ : syracuseStep 7096025 = 5322019) B5322019
theorem B1967863 : Blo 1748575 1967863 := bstep (se 1 (by rfl) ⟨1475897, by rfl⟩ : syracuseStep 1967863 = 2951795) B2951795
theorem B4982579 : Blo 1748575 4982579 := bstep (se 1 (by rfl) ⟨3736934, by rfl⟩ : syracuseStep 4982579 = 7473869) B7473869
theorem B2623307 : Blo 1748575 2623307 := bstep (se 1 (by rfl) ⟨1967480, by rfl⟩ : syracuseStep 2623307 = 3934961) B3934961
theorem B2623319 : Blo 1748575 2623319 := bstep (se 1 (by rfl) ⟨1967489, by rfl⟩ : syracuseStep 2623319 = 3934979) B3934979
theorem B2623385 : Blo 1748575 2623385 := bstep (se 2 (by rfl) ⟨983769, by rfl⟩ : syracuseStep 2623385 = 1967539) B1967539
theorem B1968043 : Blo 1748575 1968043 := bstep (se 1 (by rfl) ⟨1476032, by rfl⟩ : syracuseStep 1968043 = 2952065) B2952065
theorem B21276593 : Blo 1748575 21276593 := bstep (se 2 (by rfl) ⟨7978722, by rfl⟩ : syracuseStep 21276593 = 15957445) B15957445
theorem B2623499 : Blo 1748575 2623499 := bstep (se 1 (by rfl) ⟨1967624, by rfl⟩ : syracuseStep 2623499 = 3935249) B3935249
theorem B2623511 : Blo 1748575 2623511 := bstep (se 1 (by rfl) ⟨1967633, by rfl⟩ : syracuseStep 2623511 = 3935267) B3935267
theorem B1968151 : Blo 1748575 1968151 := bstep (se 1 (by rfl) ⟨1476113, by rfl⟩ : syracuseStep 1968151 = 2952227) B2952227
theorem B19925027 : Blo 1748575 19925027 := bstep (se 1 (by rfl) ⟨14943770, by rfl⟩ : syracuseStep 19925027 = 29887541) B29887541
theorem B3319859 : Blo 1748575 3319859 := bstep (se 1 (by rfl) ⟨2489894, by rfl⟩ : syracuseStep 3319859 = 4979789) B4979789
theorem B3934295 : Blo 1748575 3934295 := bstep (se 1 (by rfl) ⟨2950721, by rfl⟩ : syracuseStep 3934295 = 5901443) B5901443
theorem B2951255 : Blo 1748575 2951255 := bstep (se 1 (by rfl) ⟨2213441, by rfl⟩ : syracuseStep 2951255 = 4426883) B4426883
theorem B2623577 : Blo 1748575 2623577 := bstep (se 2 (by rfl) ⟨983841, by rfl⟩ : syracuseStep 2623577 = 1967683) B1967683
theorem B22415453 : Blo 1748575 22415453 := bstep (se 3 (by rfl) ⟨4202897, by rfl⟩ : syracuseStep 22415453 = 8405795) B8405795
theorem B2623691 : Blo 1748575 2623691 := bstep (se 1 (by rfl) ⟨1967768, by rfl⟩ : syracuseStep 2623691 = 3935537) B3935537
theorem B1968331 : Blo 1748575 1968331 := bstep (se 1 (by rfl) ⟨1476248, by rfl⟩ : syracuseStep 1968331 = 2952497) B2952497
theorem B2951383 : Blo 1748575 2951383 := bstep (se 1 (by rfl) ⟨2213537, by rfl⟩ : syracuseStep 2951383 = 4427075) B4427075
theorem B2623703 : Blo 1748575 2623703 := bstep (se 1 (by rfl) ⟨1967777, by rfl⟩ : syracuseStep 2623703 = 3935555) B3935555
theorem B3934475 : Blo 1748575 3934475 := bstep (se 1 (by rfl) ⟨2950856, by rfl⟩ : syracuseStep 3934475 = 5901713) B5901713
theorem B2214155 : Blo 1748575 2214155 := bstep (se 1 (by rfl) ⟨1660616, by rfl⟩ : syracuseStep 2214155 = 3321233) B3321233
theorem B7571735 : Blo 1748575 7571735 := bstep (se 1 (by rfl) ⟨5678801, by rfl⟩ : syracuseStep 7571735 = 11357603) B11357603
theorem B2623769 : Blo 1748575 2623769 := bstep (se 2 (by rfl) ⟨983913, by rfl⟩ : syracuseStep 2623769 = 1967827) B1967827
theorem B1968439 : Blo 1748575 1968439 := bstep (se 1 (by rfl) ⟨1476329, by rfl⟩ : syracuseStep 1968439 = 2952659) B2952659
theorem B3934529 : Blo 1748575 3934529 := bstep (se 2 (by rfl) ⟨1475448, by rfl⟩ : syracuseStep 3934529 = 2950897) B2950897
theorem B2623883 : Blo 1748575 2623883 := bstep (se 1 (by rfl) ⟨1967912, by rfl⟩ : syracuseStep 2623883 = 3935825) B3935825
theorem B2623895 : Blo 1748575 2623895 := bstep (se 1 (by rfl) ⟨1967921, by rfl⟩ : syracuseStep 2623895 = 3935843) B3935843
theorem B2623961 : Blo 1748575 2623961 := bstep (se 2 (by rfl) ⟨983985, by rfl⟩ : syracuseStep 2623961 = 1967971) B1967971
theorem B1968619 : Blo 1748575 1968619 := bstep (se 1 (by rfl) ⟨1476464, by rfl⟩ : syracuseStep 1968619 = 2952929) B2952929
theorem B3934745 : Blo 1748575 3934745 := bstep (se 2 (by rfl) ⟨1475529, by rfl⟩ : syracuseStep 3934745 = 2951059) B2951059
theorem B3320345 : Blo 1748575 3320345 := bstep (se 2 (by rfl) ⟨1245129, by rfl⟩ : syracuseStep 3320345 = 2490259) B2490259
theorem B2624075 : Blo 1748575 2624075 := bstep (se 1 (by rfl) ⟨1968056, by rfl⟩ : syracuseStep 2624075 = 3936113) B3936113
theorem B21867083 : Blo 1748575 21867083 := bstep (se 1 (by rfl) ⟨16400312, by rfl⟩ : syracuseStep 21867083 = 32800625) B32800625
theorem B2624087 : Blo 1748575 2624087 := bstep (se 1 (by rfl) ⟨1968065, by rfl⟩ : syracuseStep 2624087 = 3936131) B3936131
theorem B1968727 : Blo 1748575 1968727 := bstep (se 1 (by rfl) ⟨1476545, by rfl⟩ : syracuseStep 1968727 = 2953091) B2953091
theorem B13281893 : Blo 1748575 13281893 := bstep (se 4 (by rfl) ⟨1245177, by rfl⟩ : syracuseStep 13281893 = 2490355) B2490355
theorem B9964133 : Blo 1748575 9964133 := bstep (se 4 (by rfl) ⟨934137, by rfl⟩ : syracuseStep 9964133 = 1868275) B1868275
theorem B3934835 : Blo 1748575 3934835 := bstep (se 1 (by rfl) ⟨2951126, by rfl⟩ : syracuseStep 3934835 = 5902253) B5902253
theorem B3934871 : Blo 1748575 3934871 := bstep (se 1 (by rfl) ⟨2951153, by rfl⟩ : syracuseStep 3934871 = 5902307) B5902307
theorem B11209367 : Blo 1748575 11209367 := bstep (se 1 (by rfl) ⟨8407025, by rfl⟩ : syracuseStep 11209367 = 16814051) B16814051
theorem B2624153 : Blo 1748575 2624153 := bstep (se 2 (by rfl) ⟨984057, by rfl⟩ : syracuseStep 2624153 = 1968115) B1968115
theorem B6646445 : Blo 1748575 6646445 := bstep (se 3 (by rfl) ⟨1246208, by rfl⟩ : syracuseStep 6646445 = 2492417) B2492417
theorem B6302387 : Blo 1748575 6302387 := bstep (se 1 (by rfl) ⟨4726790, by rfl⟩ : syracuseStep 6302387 = 9453581) B9453581
theorem B6646475 : Blo 1748575 6646475 := bstep (se 1 (by rfl) ⟨4984856, by rfl⟩ : syracuseStep 6646475 = 9969713) B9969713
theorem B3992279 : Blo 1748575 3992279 := bstep (se 1 (by rfl) ⟨2994209, by rfl⟩ : syracuseStep 3992279 = 5988419) B5988419
theorem B2624267 : Blo 1748575 2624267 := bstep (se 1 (by rfl) ⟨1968200, by rfl⟩ : syracuseStep 2624267 = 3936401) B3936401
theorem B1968907 : Blo 1748575 1968907 := bstep (se 1 (by rfl) ⟨1476680, by rfl⟩ : syracuseStep 1968907 = 2953361) B2953361
theorem B2624279 : Blo 1748575 2624279 := bstep (se 1 (by rfl) ⟨1968209, by rfl⟩ : syracuseStep 2624279 = 3936419) B3936419
theorem B7473971 : Blo 1748575 7473971 := bstep (se 1 (by rfl) ⟨5605478, by rfl⟩ : syracuseStep 7473971 = 11210957) B11210957
theorem B78818113 : Blo 1748575 78818113 := bstep (se 2 (by rfl) ⟨29556792, by rfl⟩ : syracuseStep 78818113 = 59113585) B59113585
theorem B3935051 : Blo 1748575 3935051 := bstep (se 1 (by rfl) ⟨2951288, by rfl⟩ : syracuseStep 3935051 = 5902577) B5902577
theorem B2952011 : Blo 1748575 2952011 := bstep (se 1 (by rfl) ⟨2214008, by rfl⟩ : syracuseStep 2952011 = 4428017) B4428017
theorem B2624345 : Blo 1748575 2624345 := bstep (se 2 (by rfl) ⟨984129, by rfl⟩ : syracuseStep 2624345 = 1968259) B1968259
theorem B1969015 : Blo 1748575 1969015 := bstep (se 1 (by rfl) ⟨1476761, by rfl⟩ : syracuseStep 1969015 = 2953523) B2953523
theorem B3935105 : Blo 1748575 3935105 := bstep (se 2 (by rfl) ⟨1475664, by rfl⟩ : syracuseStep 3935105 = 2951329) B2951329
theorem B2952139 : Blo 1748575 2952139 := bstep (se 1 (by rfl) ⟨2214104, by rfl⟩ : syracuseStep 2952139 = 4428209) B4428209
theorem B2624459 : Blo 1748575 2624459 := bstep (se 1 (by rfl) ⟨1968344, by rfl⟩ : syracuseStep 2624459 = 3936689) B3936689
theorem B2214859 : Blo 1748575 2214859 := bstep (se 1 (by rfl) ⟨1661144, by rfl⟩ : syracuseStep 2214859 = 3322289) B3322289
theorem B2624471 : Blo 1748575 2624471 := bstep (se 1 (by rfl) ⟨1968353, by rfl⟩ : syracuseStep 2624471 = 3936707) B3936707
theorem B2624537 : Blo 1748575 2624537 := bstep (se 2 (by rfl) ⟨984201, by rfl⟩ : syracuseStep 2624537 = 1968403) B1968403
theorem B1969195 : Blo 1748575 1969195 := bstep (se 1 (by rfl) ⟨1476896, by rfl⟩ : syracuseStep 1969195 = 2953793) B2953793
theorem B13282379 : Blo 1748575 13282379 := bstep (se 1 (by rfl) ⟨9961784, by rfl⟩ : syracuseStep 13282379 = 19923569) B19923569
theorem B3935321 : Blo 1748575 3935321 := bstep (se 2 (by rfl) ⟨1475745, by rfl⟩ : syracuseStep 3935321 = 2951491) B2951491
theorem B2952281 : Blo 1748575 2952281 := bstep (se 2 (by rfl) ⟨1107105, by rfl⟩ : syracuseStep 2952281 = 2214211) B2214211
theorem B14945411 : Blo 1748575 14945411 := bstep (se 1 (by rfl) ⟨11209058, by rfl⟩ : syracuseStep 14945411 = 22418117) B22418117
theorem B2624651 : Blo 1748575 2624651 := bstep (se 1 (by rfl) ⟨1968488, by rfl⟩ : syracuseStep 2624651 = 3936977) B3936977
theorem B7982225 : Blo 1748575 7982225 := bstep (se 2 (by rfl) ⟨2993334, by rfl⟩ : syracuseStep 7982225 = 5986669) B5986669
theorem B2624663 : Blo 1748575 2624663 := bstep (se 1 (by rfl) ⟨1968497, by rfl⟩ : syracuseStep 2624663 = 3936995) B3936995
theorem B1969303 : Blo 1748575 1969303 := bstep (se 1 (by rfl) ⟨1476977, by rfl⟩ : syracuseStep 1969303 = 2953955) B2953955
theorem B6302893 : Blo 1748575 6302893 := bstep (se 3 (by rfl) ⟨1181792, by rfl⟩ : syracuseStep 6302893 = 2363585) B2363585
theorem B3935411 : Blo 1748575 3935411 := bstep (se 1 (by rfl) ⟨2951558, by rfl⟩ : syracuseStep 3935411 = 5903117) B5903117
theorem B3935447 : Blo 1748575 3935447 := bstep (se 1 (by rfl) ⟨2951585, by rfl⟩ : syracuseStep 3935447 = 5903171) B5903171
theorem B2215127 : Blo 1748575 2215127 := bstep (se 1 (by rfl) ⟨1661345, by rfl⟩ : syracuseStep 2215127 = 3322691) B3322691
theorem B2952409 : Blo 1748575 2952409 := bstep (se 2 (by rfl) ⟨1107153, by rfl⟩ : syracuseStep 2952409 = 2214307) B2214307
theorem B2624729 : Blo 1748575 2624729 := bstep (se 2 (by rfl) ⟨984273, by rfl⟩ : syracuseStep 2624729 = 1968547) B1968547
theorem B51137837 : Blo 1748575 51137837 := bstep (se 3 (by rfl) ⟨9588344, by rfl⟩ : syracuseStep 51137837 = 19176689) B19176689
theorem B7097645 : Blo 1748575 7097645 := bstep (se 3 (by rfl) ⟨1330808, by rfl⟩ : syracuseStep 7097645 = 2661617) B2661617
theorem B2624843 : Blo 1748575 2624843 := bstep (se 1 (by rfl) ⟨1968632, by rfl⟩ : syracuseStep 2624843 = 3937265) B3937265
theorem B2624855 : Blo 1748575 2624855 := bstep (se 1 (by rfl) ⟨1968641, by rfl⟩ : syracuseStep 2624855 = 3937283) B3937283
theorem B3935627 : Blo 1748575 3935627 := bstep (se 1 (by rfl) ⟨2951720, by rfl⟩ : syracuseStep 3935627 = 5903441) B5903441
theorem B2624921 : Blo 1748575 2624921 := bstep (se 2 (by rfl) ⟨984345, by rfl⟩ : syracuseStep 2624921 = 1968691) B1968691
theorem B3935681 : Blo 1748575 3935681 := bstep (se 2 (by rfl) ⟨1475880, by rfl⟩ : syracuseStep 3935681 = 2951761) B2951761
theorem B2625035 : Blo 1748575 2625035 := bstep (se 1 (by rfl) ⟨1968776, by rfl⟩ : syracuseStep 2625035 = 3937553) B3937553
theorem B2305559 : Blo 1748575 2305559 := bstep (se 1 (by rfl) ⟨1729169, by rfl⟩ : syracuseStep 2305559 = 3458339) B3458339
theorem B2625047 : Blo 1748575 2625047 := bstep (se 1 (by rfl) ⟨1968785, by rfl⟩ : syracuseStep 2625047 = 3937571) B3937571
theorem B6639155 : Blo 1748575 6639155 := bstep (se 1 (by rfl) ⟨4979366, by rfl⟩ : syracuseStep 6639155 = 9958733) B9958733
theorem B5901875 : Blo 1748575 5901875 := bstep (se 1 (by rfl) ⟨4426406, by rfl⟩ : syracuseStep 5901875 = 8852813) B8852813
theorem B2625113 : Blo 1748575 2625113 := bstep (se 2 (by rfl) ⟨984417, by rfl⟩ : syracuseStep 2625113 = 1968835) B1968835
theorem B1748587 : Blo 1748575 1748587 := bstep (se 1 (by rfl) ⟨1311440, by rfl⟩ : syracuseStep 1748587 = 2622881) B2622881
theorem B1748599 : Blo 1748575 1748599 := bstep (se 1 (by rfl) ⟨1311449, by rfl⟩ : syracuseStep 1748599 = 2622899) B2622899
theorem B1748619 : Blo 1748575 1748619 := bstep (se 1 (by rfl) ⟨1311464, by rfl⟩ : syracuseStep 1748619 = 2622929) B2622929
theorem B1748631 : Blo 1748575 1748631 := bstep (se 1 (by rfl) ⟨1311473, by rfl⟩ : syracuseStep 1748631 = 2622947) B2622947
theorem B3935897 : Blo 1748575 3935897 := bstep (se 2 (by rfl) ⟨1475961, by rfl⟩ : syracuseStep 3935897 = 2951923) B2951923
theorem B1748651 : Blo 1748575 1748651 := bstep (se 1 (by rfl) ⟨1311488, by rfl⟩ : syracuseStep 1748651 = 2622977) B2622977
theorem B1748663 : Blo 1748575 1748663 := bstep (se 1 (by rfl) ⟨1311497, by rfl⟩ : syracuseStep 1748663 = 2622995) B2622995
theorem B1748683 : Blo 1748575 1748683 := bstep (se 1 (by rfl) ⟨1311512, by rfl⟩ : syracuseStep 1748683 = 2623025) B2623025
theorem B67276493 : Blo 1748575 67276493 := bstep (se 3 (by rfl) ⟨12614342, by rfl⟩ : syracuseStep 67276493 = 25228685) B25228685
theorem B2625227 : Blo 1748575 2625227 := bstep (se 1 (by rfl) ⟨1968920, by rfl⟩ : syracuseStep 2625227 = 3937841) B3937841
theorem B1748695 : Blo 1748575 1748695 := bstep (se 1 (by rfl) ⟨1311521, by rfl⟩ : syracuseStep 1748695 = 2623043) B2623043
theorem B2625239 : Blo 1748575 2625239 := bstep (se 1 (by rfl) ⟨1968929, by rfl⟩ : syracuseStep 2625239 = 3937859) B3937859
theorem B1748715 : Blo 1748575 1748715 := bstep (se 1 (by rfl) ⟨1311536, by rfl⟩ : syracuseStep 1748715 = 2623073) B2623073
theorem B3935987 : Blo 1748575 3935987 := bstep (se 1 (by rfl) ⟨2951990, by rfl⟩ : syracuseStep 3935987 = 5903981) B5903981
theorem B1748727 : Blo 1748575 1748727 := bstep (se 1 (by rfl) ⟨1311545, by rfl⟩ : syracuseStep 1748727 = 2623091) B2623091
theorem B1748747 : Blo 1748575 1748747 := bstep (se 1 (by rfl) ⟨1311560, by rfl⟩ : syracuseStep 1748747 = 2623121) B2623121
theorem B1748759 : Blo 1748575 1748759 := bstep (se 1 (by rfl) ⟨1311569, by rfl⟩ : syracuseStep 1748759 = 2623139) B2623139
theorem B3936023 : Blo 1748575 3936023 := bstep (se 1 (by rfl) ⟨2952017, by rfl⟩ : syracuseStep 3936023 = 5904035) B5904035
theorem B2952983 : Blo 1748575 2952983 := bstep (se 1 (by rfl) ⟨2214737, by rfl⟩ : syracuseStep 2952983 = 4429475) B4429475
theorem B2625305 : Blo 1748575 2625305 := bstep (se 2 (by rfl) ⟨984489, by rfl⟩ : syracuseStep 2625305 = 1968979) B1968979
theorem B1748779 : Blo 1748575 1748779 := bstep (se 1 (by rfl) ⟨1311584, by rfl⟩ : syracuseStep 1748779 = 2623169) B2623169
theorem B1748791 : Blo 1748575 1748791 := bstep (se 1 (by rfl) ⟨1311593, by rfl⟩ : syracuseStep 1748791 = 2623187) B2623187
theorem B5902145 : Blo 1748575 5902145 := bstep (se 2 (by rfl) ⟨2213304, by rfl⟩ : syracuseStep 5902145 = 4426609) B4426609
theorem B1748811 : Blo 1748575 1748811 := bstep (se 1 (by rfl) ⟨1311608, by rfl⟩ : syracuseStep 1748811 = 2623217) B2623217
theorem B1748823 : Blo 1748575 1748823 := bstep (se 1 (by rfl) ⟨1311617, by rfl⟩ : syracuseStep 1748823 = 2623235) B2623235
theorem B1748843 : Blo 1748575 1748843 := bstep (se 1 (by rfl) ⟨1311632, by rfl⟩ : syracuseStep 1748843 = 2623265) B2623265
theorem B1748855 : Blo 1748575 1748855 := bstep (se 1 (by rfl) ⟨1311641, by rfl⟩ : syracuseStep 1748855 = 2623283) B2623283
theorem B1748875 : Blo 1748575 1748875 := bstep (se 1 (by rfl) ⟨1311656, by rfl⟩ : syracuseStep 1748875 = 2623313) B2623313
theorem B2625419 : Blo 1748575 2625419 := bstep (se 1 (by rfl) ⟨1969064, by rfl⟩ : syracuseStep 2625419 = 3938129) B3938129
theorem B1748887 : Blo 1748575 1748887 := bstep (se 1 (by rfl) ⟨1311665, by rfl⟩ : syracuseStep 1748887 = 2623331) B2623331
theorem B2953111 : Blo 1748575 2953111 := bstep (se 1 (by rfl) ⟨2214833, by rfl⟩ : syracuseStep 2953111 = 4429667) B4429667
theorem B2625431 : Blo 1748575 2625431 := bstep (se 1 (by rfl) ⟨1969073, by rfl⟩ : syracuseStep 2625431 = 3938147) B3938147
theorem B1748907 : Blo 1748575 1748907 := bstep (se 1 (by rfl) ⟨1311680, by rfl⟩ : syracuseStep 1748907 = 2623361) B2623361
theorem B1748919 : Blo 1748575 1748919 := bstep (se 1 (by rfl) ⟨1311689, by rfl⟩ : syracuseStep 1748919 = 2623379) B2623379
theorem B1748939 : Blo 1748575 1748939 := bstep (se 1 (by rfl) ⟨1311704, by rfl⟩ : syracuseStep 1748939 = 2623409) B2623409
theorem B4427723 : Blo 1748575 4427723 := bstep (se 1 (by rfl) ⟨3320792, by rfl⟩ : syracuseStep 4427723 = 6641585) B6641585
theorem B3936203 : Blo 1748575 3936203 := bstep (se 1 (by rfl) ⟨2952152, by rfl⟩ : syracuseStep 3936203 = 5904305) B5904305
theorem B3321803 : Blo 1748575 3321803 := bstep (se 1 (by rfl) ⟨2491352, by rfl⟩ : syracuseStep 3321803 = 4982705) B4982705
theorem B1748951 : Blo 1748575 1748951 := bstep (se 1 (by rfl) ⟨1311713, by rfl⟩ : syracuseStep 1748951 = 2623427) B2623427
theorem B2625497 : Blo 1748575 2625497 := bstep (se 2 (by rfl) ⟨984561, by rfl⟩ : syracuseStep 2625497 = 1969123) B1969123
theorem B1748971 : Blo 1748575 1748971 := bstep (se 1 (by rfl) ⟨1311728, by rfl⟩ : syracuseStep 1748971 = 2623457) B2623457
theorem B1748983 : Blo 1748575 1748983 := bstep (se 1 (by rfl) ⟨1311737, by rfl⟩ : syracuseStep 1748983 = 2623475) B2623475
theorem B3936257 : Blo 1748575 3936257 := bstep (se 2 (by rfl) ⟨1476096, by rfl⟩ : syracuseStep 3936257 = 2952193) B2952193
theorem B1749003 : Blo 1748575 1749003 := bstep (se 1 (by rfl) ⟨1311752, by rfl⟩ : syracuseStep 1749003 = 2623505) B2623505
theorem B1749015 : Blo 1748575 1749015 := bstep (se 1 (by rfl) ⟨1311761, by rfl⟩ : syracuseStep 1749015 = 2623523) B2623523
theorem B1749035 : Blo 1748575 1749035 := bstep (se 1 (by rfl) ⟨1311776, by rfl⟩ : syracuseStep 1749035 = 2623553) B2623553
theorem B1749047 : Blo 1748575 1749047 := bstep (se 1 (by rfl) ⟨1311785, by rfl⟩ : syracuseStep 1749047 = 2623571) B2623571
theorem B1749067 : Blo 1748575 1749067 := bstep (se 1 (by rfl) ⟨1311800, by rfl⟩ : syracuseStep 1749067 = 2623601) B2623601
theorem B35926091 : Blo 1748575 35926091 := bstep (se 1 (by rfl) ⟨26944568, by rfl⟩ : syracuseStep 35926091 = 53889137) B53889137
theorem B2625611 : Blo 1748575 2625611 := bstep (se 1 (by rfl) ⟨1969208, by rfl⟩ : syracuseStep 2625611 = 3938417) B3938417
theorem B1749079 : Blo 1748575 1749079 := bstep (se 1 (by rfl) ⟨1311809, by rfl⟩ : syracuseStep 1749079 = 2623619) B2623619
theorem B2625623 : Blo 1748575 2625623 := bstep (se 1 (by rfl) ⟨1969217, by rfl⟩ : syracuseStep 2625623 = 3938435) B3938435
theorem B2994265 : Blo 1748575 2994265 := bstep (se 2 (by rfl) ⟨1122849, by rfl⟩ : syracuseStep 2994265 = 2245699) B2245699
theorem B13291613 : Blo 1748575 13291613 := bstep (se 3 (by rfl) ⟨2492177, by rfl⟩ : syracuseStep 13291613 = 4984355) B4984355
theorem B1749099 : Blo 1748575 1749099 := bstep (se 1 (by rfl) ⟨1311824, by rfl⟩ : syracuseStep 1749099 = 2623649) B2623649
theorem B1749111 : Blo 1748575 1749111 := bstep (se 1 (by rfl) ⟨1311833, by rfl⟩ : syracuseStep 1749111 = 2623667) B2623667
theorem B3321985 : Blo 1748575 3321985 := bstep (se 2 (by rfl) ⟨1245744, by rfl⟩ : syracuseStep 3321985 = 2491489) B2491489
theorem B8859779 : Blo 1748575 8859779 := bstep (se 1 (by rfl) ⟨6644834, by rfl⟩ : syracuseStep 8859779 = 13289669) B13289669
theorem B1749131 : Blo 1748575 1749131 := bstep (se 1 (by rfl) ⟨1311848, by rfl⟩ : syracuseStep 1749131 = 2623697) B2623697
theorem B1749143 : Blo 1748575 1749143 := bstep (se 1 (by rfl) ⟨1311857, by rfl⟩ : syracuseStep 1749143 = 2623715) B2623715
theorem B2625689 : Blo 1748575 2625689 := bstep (se 2 (by rfl) ⟨984633, by rfl⟩ : syracuseStep 2625689 = 1969267) B1969267
theorem B1749163 : Blo 1748575 1749163 := bstep (se 1 (by rfl) ⟨1311872, by rfl⟩ : syracuseStep 1749163 = 2623745) B2623745
theorem B1749175 : Blo 1748575 1749175 := bstep (se 1 (by rfl) ⟨1311881, by rfl⟩ : syracuseStep 1749175 = 2623763) B2623763
theorem B6394049 : Blo 1748575 6394049 := bstep (se 2 (by rfl) ⟨2397768, by rfl⟩ : syracuseStep 6394049 = 4795537) B4795537
theorem B1749195 : Blo 1748575 1749195 := bstep (se 1 (by rfl) ⟨1311896, by rfl⟩ : syracuseStep 1749195 = 2623793) B2623793
theorem B1749207 : Blo 1748575 1749207 := bstep (se 1 (by rfl) ⟨1311905, by rfl⟩ : syracuseStep 1749207 = 2623811) B2623811
theorem B3936473 : Blo 1748575 3936473 := bstep (se 2 (by rfl) ⟨1476177, by rfl⟩ : syracuseStep 3936473 = 2952355) B2952355
theorem B1749227 : Blo 1748575 1749227 := bstep (se 1 (by rfl) ⟨1311920, by rfl⟩ : syracuseStep 1749227 = 2623841) B2623841
theorem B1749239 : Blo 1748575 1749239 := bstep (se 1 (by rfl) ⟨1311929, by rfl⟩ : syracuseStep 1749239 = 2623859) B2623859
theorem B1749259 : Blo 1748575 1749259 := bstep (se 1 (by rfl) ⟨1311944, by rfl⟩ : syracuseStep 1749259 = 2623889) B2623889
theorem B2625803 : Blo 1748575 2625803 := bstep (se 1 (by rfl) ⟨1969352, by rfl⟩ : syracuseStep 2625803 = 3938705) B3938705
theorem B1749271 : Blo 1748575 1749271 := bstep (se 1 (by rfl) ⟨1311953, by rfl⟩ : syracuseStep 1749271 = 2623907) B2623907
theorem B2625815 : Blo 1748575 2625815 := bstep (se 1 (by rfl) ⟨1969361, by rfl⟩ : syracuseStep 2625815 = 3938723) B3938723
theorem B1749291 : Blo 1748575 1749291 := bstep (se 1 (by rfl) ⟨1311968, by rfl⟩ : syracuseStep 1749291 = 2623937) B2623937
theorem B3936563 : Blo 1748575 3936563 := bstep (se 1 (by rfl) ⟨2952422, by rfl⟩ : syracuseStep 3936563 = 5904845) B5904845
theorem B1749303 : Blo 1748575 1749303 := bstep (se 1 (by rfl) ⟨1311977, by rfl⟩ : syracuseStep 1749303 = 2623955) B2623955
theorem B1749323 : Blo 1748575 1749323 := bstep (se 1 (by rfl) ⟨1311992, by rfl⟩ : syracuseStep 1749323 = 2623985) B2623985
theorem B1749335 : Blo 1748575 1749335 := bstep (se 1 (by rfl) ⟨1312001, by rfl⟩ : syracuseStep 1749335 = 2624003) B2624003
theorem B3936599 : Blo 1748575 3936599 := bstep (se 1 (by rfl) ⟨2952449, by rfl⟩ : syracuseStep 3936599 = 5904899) B5904899
theorem B5902685 : Blo 1748575 5902685 := bstep (se 3 (by rfl) ⟨1106753, by rfl⟩ : syracuseStep 5902685 = 2213507) B2213507
theorem B1749355 : Blo 1748575 1749355 := bstep (se 1 (by rfl) ⟨1312016, by rfl⟩ : syracuseStep 1749355 = 2624033) B2624033
theorem B1749367 : Blo 1748575 1749367 := bstep (se 1 (by rfl) ⟨1312025, by rfl⟩ : syracuseStep 1749367 = 2624051) B2624051
theorem B1749387 : Blo 1748575 1749387 := bstep (se 1 (by rfl) ⟨1312040, by rfl⟩ : syracuseStep 1749387 = 2624081) B2624081
theorem B1749399 : Blo 1748575 1749399 := bstep (se 1 (by rfl) ⟨1312049, by rfl⟩ : syracuseStep 1749399 = 2624099) B2624099
theorem B4321687 : Blo 1748575 4321687 := bstep (se 1 (by rfl) ⟨3241265, by rfl⟩ : syracuseStep 4321687 = 6482531) B6482531
theorem B1749419 : Blo 1748575 1749419 := bstep (se 1 (by rfl) ⟨1312064, by rfl⟩ : syracuseStep 1749419 = 2624129) B2624129
theorem B1749431 : Blo 1748575 1749431 := bstep (se 1 (by rfl) ⟨1312073, by rfl⟩ : syracuseStep 1749431 = 2624147) B2624147
theorem B1749451 : Blo 1748575 1749451 := bstep (se 1 (by rfl) ⟨1312088, by rfl⟩ : syracuseStep 1749451 = 2624177) B2624177
theorem B1749463 : Blo 1748575 1749463 := bstep (se 1 (by rfl) ⟨1312097, by rfl⟩ : syracuseStep 1749463 = 2624195) B2624195
theorem B4731353 : Blo 1748575 4731353 := bstep (se 2 (by rfl) ⟨1774257, by rfl⟩ : syracuseStep 4731353 = 3548515) B3548515
theorem B1749483 : Blo 1748575 1749483 := bstep (se 1 (by rfl) ⟨1312112, by rfl⟩ : syracuseStep 1749483 = 2624225) B2624225
theorem B1749495 : Blo 1748575 1749495 := bstep (se 1 (by rfl) ⟨1312121, by rfl⟩ : syracuseStep 1749495 = 2624243) B2624243
theorem B1749515 : Blo 1748575 1749515 := bstep (se 1 (by rfl) ⟨1312136, by rfl⟩ : syracuseStep 1749515 = 2624273) B2624273
theorem B3936779 : Blo 1748575 3936779 := bstep (se 1 (by rfl) ⟨2952584, by rfl⟩ : syracuseStep 3936779 = 5905169) B5905169
theorem B2953739 : Blo 1748575 2953739 := bstep (se 1 (by rfl) ⟨2215304, by rfl⟩ : syracuseStep 2953739 = 4430609) B4430609
theorem B1749527 : Blo 1748575 1749527 := bstep (se 1 (by rfl) ⟨1312145, by rfl⟩ : syracuseStep 1749527 = 2624291) B2624291
theorem B1749547 : Blo 1748575 1749547 := bstep (se 1 (by rfl) ⟨1312160, by rfl⟩ : syracuseStep 1749547 = 2624321) B2624321
theorem B1749559 : Blo 1748575 1749559 := bstep (se 1 (by rfl) ⟨1312169, by rfl⟩ : syracuseStep 1749559 = 2624339) B2624339
theorem B3936833 : Blo 1748575 3936833 := bstep (se 2 (by rfl) ⟨1476312, by rfl⟩ : syracuseStep 3936833 = 2952625) B2952625
theorem B3322433 : Blo 1748575 3322433 := bstep (se 2 (by rfl) ⟨1245912, by rfl⟩ : syracuseStep 3322433 = 2491825) B2491825
theorem B1749579 : Blo 1748575 1749579 := bstep (se 1 (by rfl) ⟨1312184, by rfl⟩ : syracuseStep 1749579 = 2624369) B2624369
theorem B1749591 : Blo 1748575 1749591 := bstep (se 1 (by rfl) ⟨1312193, by rfl⟩ : syracuseStep 1749591 = 2624387) B2624387
theorem B1749611 : Blo 1748575 1749611 := bstep (se 1 (by rfl) ⟨1312208, by rfl⟩ : syracuseStep 1749611 = 2624417) B2624417
theorem B1749623 : Blo 1748575 1749623 := bstep (se 1 (by rfl) ⟨1312217, by rfl⟩ : syracuseStep 1749623 = 2624435) B2624435
theorem B1749643 : Blo 1748575 1749643 := bstep (se 1 (by rfl) ⟨1312232, by rfl⟩ : syracuseStep 1749643 = 2624465) B2624465
theorem B2953867 : Blo 1748575 2953867 := bstep (se 1 (by rfl) ⟨2215400, by rfl⟩ : syracuseStep 2953867 = 4430801) B4430801
theorem B1749655 : Blo 1748575 1749655 := bstep (se 1 (by rfl) ⟨1312241, by rfl⟩ : syracuseStep 1749655 = 2624483) B2624483
theorem B1749675 : Blo 1748575 1749675 := bstep (se 1 (by rfl) ⟨1312256, by rfl⟩ : syracuseStep 1749675 = 2624513) B2624513
theorem B7475885 : Blo 1748575 7475885 := bstep (se 3 (by rfl) ⟨1401728, by rfl⟩ : syracuseStep 7475885 = 2803457) B2803457
theorem B1749687 : Blo 1748575 1749687 := bstep (se 1 (by rfl) ⟨1312265, by rfl⟩ : syracuseStep 1749687 = 2624531) B2624531
theorem B1749707 : Blo 1748575 1749707 := bstep (se 1 (by rfl) ⟨1312280, by rfl⟩ : syracuseStep 1749707 = 2624561) B2624561
theorem B1749719 : Blo 1748575 1749719 := bstep (se 1 (by rfl) ⟨1312289, by rfl⟩ : syracuseStep 1749719 = 2624579) B2624579
theorem B1749739 : Blo 1748575 1749739 := bstep (se 1 (by rfl) ⟨1312304, by rfl⟩ : syracuseStep 1749739 = 2624609) B2624609
theorem B1749751 : Blo 1748575 1749751 := bstep (se 1 (by rfl) ⟨1312313, by rfl⟩ : syracuseStep 1749751 = 2624627) B2624627
theorem B1749771 : Blo 1748575 1749771 := bstep (se 1 (by rfl) ⟨1312328, by rfl⟩ : syracuseStep 1749771 = 2624657) B2624657
theorem B1749783 : Blo 1748575 1749783 := bstep (se 1 (by rfl) ⟨1312337, by rfl⟩ : syracuseStep 1749783 = 2624675) B2624675
theorem B3937049 : Blo 1748575 3937049 := bstep (se 2 (by rfl) ⟨1476393, by rfl⟩ : syracuseStep 3937049 = 2952787) B2952787
theorem B2954009 : Blo 1748575 2954009 := bstep (se 2 (by rfl) ⟨1107753, by rfl⟩ : syracuseStep 2954009 = 2215507) B2215507
theorem B14193443 : Blo 1748575 14193443 := bstep (se 1 (by rfl) ⟨10645082, by rfl⟩ : syracuseStep 14193443 = 21290165) B21290165
theorem B1749803 : Blo 1748575 1749803 := bstep (se 1 (by rfl) ⟨1312352, by rfl⟩ : syracuseStep 1749803 = 2624705) B2624705
theorem B1749815 : Blo 1748575 1749815 := bstep (se 1 (by rfl) ⟨1312361, by rfl⟩ : syracuseStep 1749815 = 2624723) B2624723
theorem B1749835 : Blo 1748575 1749835 := bstep (se 1 (by rfl) ⟨1312376, by rfl⟩ : syracuseStep 1749835 = 2624753) B2624753
theorem B1749847 : Blo 1748575 1749847 := bstep (se 1 (by rfl) ⟨1312385, by rfl⟩ : syracuseStep 1749847 = 2624771) B2624771
theorem B1749867 : Blo 1748575 1749867 := bstep (se 1 (by rfl) ⟨1312400, by rfl⟩ : syracuseStep 1749867 = 2624801) B2624801
theorem B3937139 : Blo 1748575 3937139 := bstep (se 1 (by rfl) ⟨2952854, by rfl⟩ : syracuseStep 3937139 = 5905709) B5905709
theorem B1749879 : Blo 1748575 1749879 := bstep (se 1 (by rfl) ⟨1312409, by rfl⟩ : syracuseStep 1749879 = 2624819) B2624819
theorem B1749899 : Blo 1748575 1749899 := bstep (se 1 (by rfl) ⟨1312424, by rfl⟩ : syracuseStep 1749899 = 2624849) B2624849
theorem B4428695 : Blo 1748575 4428695 := bstep (se 1 (by rfl) ⟨3321521, by rfl⟩ : syracuseStep 4428695 = 6643043) B6643043
theorem B3937175 : Blo 1748575 3937175 := bstep (se 1 (by rfl) ⟨2952881, by rfl⟩ : syracuseStep 3937175 = 5905763) B5905763
theorem B1749911 : Blo 1748575 1749911 := bstep (se 1 (by rfl) ⟨1312433, by rfl⟩ : syracuseStep 1749911 = 2624867) B2624867
theorem B8410007 : Blo 1748575 8410007 := bstep (se 1 (by rfl) ⟨6307505, by rfl⟩ : syracuseStep 8410007 = 12615011) B12615011
theorem B3322775 : Blo 1748575 3322775 := bstep (se 1 (by rfl) ⟨2492081, by rfl⟩ : syracuseStep 3322775 = 4984163) B4984163
theorem B1749931 : Blo 1748575 1749931 := bstep (se 1 (by rfl) ⟨1312448, by rfl⟩ : syracuseStep 1749931 = 2624897) B2624897
theorem B1749943 : Blo 1748575 1749943 := bstep (se 1 (by rfl) ⟨1312457, by rfl⟩ : syracuseStep 1749943 = 2624915) B2624915
theorem B1749963 : Blo 1748575 1749963 := bstep (se 1 (by rfl) ⟨1312472, by rfl⟩ : syracuseStep 1749963 = 2624945) B2624945
theorem B4731851 : Blo 1748575 4731851 := bstep (se 1 (by rfl) ⟨3548888, by rfl⟩ : syracuseStep 4731851 = 7097777) B7097777
theorem B1749975 : Blo 1748575 1749975 := bstep (se 1 (by rfl) ⟨1312481, by rfl⟩ : syracuseStep 1749975 = 2624963) B2624963
theorem B1749995 : Blo 1748575 1749995 := bstep (se 1 (by rfl) ⟨1312496, by rfl⟩ : syracuseStep 1749995 = 2624993) B2624993
theorem B1750007 : Blo 1748575 1750007 := bstep (se 1 (by rfl) ⟨1312505, by rfl⟩ : syracuseStep 1750007 = 2625011) B2625011
theorem B6640643 : Blo 1748575 6640643 := bstep (se 1 (by rfl) ⟨4980482, by rfl⟩ : syracuseStep 6640643 = 9960965) B9960965
theorem B1750027 : Blo 1748575 1750027 := bstep (se 1 (by rfl) ⟨1312520, by rfl⟩ : syracuseStep 1750027 = 2625041) B2625041
theorem B1750039 : Blo 1748575 1750039 := bstep (se 1 (by rfl) ⟨1312529, by rfl⟩ : syracuseStep 1750039 = 2625059) B2625059
theorem B1750059 : Blo 1748575 1750059 := bstep (se 1 (by rfl) ⟨1312544, by rfl⟩ : syracuseStep 1750059 = 2625089) B2625089
theorem B6394925 : Blo 1748575 6394925 := bstep (se 3 (by rfl) ⟨1199048, by rfl⟩ : syracuseStep 6394925 = 2398097) B2398097
theorem B1750071 : Blo 1748575 1750071 := bstep (se 1 (by rfl) ⟨1312553, by rfl⟩ : syracuseStep 1750071 = 2625107) B2625107
theorem B8410177 : Blo 1748575 8410177 := bstep (se 2 (by rfl) ⟨3153816, by rfl⟩ : syracuseStep 8410177 = 6307633) B6307633
theorem B51811397 : Blo 1748575 51811397 := bstep (se 4 (by rfl) ⟨4857318, by rfl⟩ : syracuseStep 51811397 = 9714637) B9714637
theorem B3937355 : Blo 1748575 3937355 := bstep (se 1 (by rfl) ⟨2953016, by rfl⟩ : syracuseStep 3937355 = 5906033) B5906033
theorem B1750091 : Blo 1748575 1750091 := bstep (se 1 (by rfl) ⟨1312568, by rfl⟩ : syracuseStep 1750091 = 2625137) B2625137
theorem B1750103 : Blo 1748575 1750103 := bstep (se 1 (by rfl) ⟨1312577, by rfl⟩ : syracuseStep 1750103 = 2625155) B2625155
theorem B1750123 : Blo 1748575 1750123 := bstep (se 1 (by rfl) ⟨1312592, by rfl⟩ : syracuseStep 1750123 = 2625185) B2625185
theorem B1750135 : Blo 1748575 1750135 := bstep (se 1 (by rfl) ⟨1312601, by rfl⟩ : syracuseStep 1750135 = 2625203) B2625203
theorem B3937409 : Blo 1748575 3937409 := bstep (se 2 (by rfl) ⟨1476528, by rfl⟩ : syracuseStep 3937409 = 2953057) B2953057
theorem B1750155 : Blo 1748575 1750155 := bstep (se 1 (by rfl) ⟨1312616, by rfl⟩ : syracuseStep 1750155 = 2625233) B2625233
theorem B1750167 : Blo 1748575 1750167 := bstep (se 1 (by rfl) ⟨1312625, by rfl⟩ : syracuseStep 1750167 = 2625251) B2625251
theorem B1750187 : Blo 1748575 1750187 := bstep (se 1 (by rfl) ⟨1312640, by rfl⟩ : syracuseStep 1750187 = 2625281) B2625281
theorem B54580405 : Blo 1748575 54580405 := bstep (se 5 (by rfl) ⟨2558456, by rfl⟩ : syracuseStep 54580405 = 5116913) B5116913
theorem B1750199 : Blo 1748575 1750199 := bstep (se 1 (by rfl) ⟨1312649, by rfl⟩ : syracuseStep 1750199 = 2625299) B2625299
theorem B1750219 : Blo 1748575 1750219 := bstep (se 1 (by rfl) ⟨1312664, by rfl⟩ : syracuseStep 1750219 = 2625329) B2625329
theorem B1750231 : Blo 1748575 1750231 := bstep (se 1 (by rfl) ⟨1312673, by rfl⟩ : syracuseStep 1750231 = 2625347) B2625347
theorem B1750251 : Blo 1748575 1750251 := bstep (se 1 (by rfl) ⟨1312688, by rfl⟩ : syracuseStep 1750251 = 2625377) B2625377
theorem B1750263 : Blo 1748575 1750263 := bstep (se 1 (by rfl) ⟨1312697, by rfl⟩ : syracuseStep 1750263 = 2625395) B2625395
theorem B1750283 : Blo 1748575 1750283 := bstep (se 1 (by rfl) ⟨1312712, by rfl⟩ : syracuseStep 1750283 = 2625425) B2625425
theorem B1750295 : Blo 1748575 1750295 := bstep (se 1 (by rfl) ⟨1312721, by rfl⟩ : syracuseStep 1750295 = 2625443) B2625443
theorem B1750315 : Blo 1748575 1750315 := bstep (se 1 (by rfl) ⟨1312736, by rfl⟩ : syracuseStep 1750315 = 2625473) B2625473
theorem B1750327 : Blo 1748575 1750327 := bstep (se 1 (by rfl) ⟨1312745, by rfl⟩ : syracuseStep 1750327 = 2625491) B2625491
theorem B1750347 : Blo 1748575 1750347 := bstep (se 1 (by rfl) ⟨1312760, by rfl⟩ : syracuseStep 1750347 = 2625521) B2625521
theorem B1750359 : Blo 1748575 1750359 := bstep (se 1 (by rfl) ⟨1312769, by rfl⟩ : syracuseStep 1750359 = 2625539) B2625539
theorem B3937625 : Blo 1748575 3937625 := bstep (se 2 (by rfl) ⟨1476609, by rfl⟩ : syracuseStep 3937625 = 2953219) B2953219
theorem B5051737 : Blo 1748575 5051737 := bstep (se 2 (by rfl) ⟨1894401, by rfl⟩ : syracuseStep 5051737 = 3788803) B3788803
theorem B7476569 : Blo 1748575 7476569 := bstep (se 2 (by rfl) ⟨2803713, by rfl⟩ : syracuseStep 7476569 = 5607427) B5607427
theorem B11203933 : Blo 1748575 11203933 := bstep (se 3 (by rfl) ⟨2100737, by rfl⟩ : syracuseStep 11203933 = 4201475) B4201475
theorem B7091549 : Blo 1748575 7091549 := bstep (se 3 (by rfl) ⟨1329665, by rfl⟩ : syracuseStep 7091549 = 2659331) B2659331
theorem B1750379 : Blo 1748575 1750379 := bstep (se 1 (by rfl) ⟨1312784, by rfl⟩ : syracuseStep 1750379 = 2625569) B2625569
theorem B1750391 : Blo 1748575 1750391 := bstep (se 1 (by rfl) ⟨1312793, by rfl⟩ : syracuseStep 1750391 = 2625587) B2625587
theorem B1750411 : Blo 1748575 1750411 := bstep (se 1 (by rfl) ⟨1312808, by rfl⟩ : syracuseStep 1750411 = 2625617) B2625617
theorem B1750423 : Blo 1748575 1750423 := bstep (se 1 (by rfl) ⟨1312817, by rfl⟩ : syracuseStep 1750423 = 2625635) B2625635
theorem B1750443 : Blo 1748575 1750443 := bstep (se 1 (by rfl) ⟨1312832, by rfl⟩ : syracuseStep 1750443 = 2625665) B2625665
theorem B3937715 : Blo 1748575 3937715 := bstep (se 1 (by rfl) ⟨2953286, by rfl⟩ : syracuseStep 3937715 = 5906573) B5906573
theorem B19936691 : Blo 1748575 19936691 := bstep (se 1 (by rfl) ⟨14952518, by rfl⟩ : syracuseStep 19936691 = 29905037) B29905037
theorem B1750455 : Blo 1748575 1750455 := bstep (se 1 (by rfl) ⟨1312841, by rfl⟩ : syracuseStep 1750455 = 2625683) B2625683
theorem B6641099 : Blo 1748575 6641099 := bstep (se 1 (by rfl) ⟨4980824, by rfl⟩ : syracuseStep 6641099 = 9961649) B9961649
theorem B5903819 : Blo 1748575 5903819 := bstep (se 1 (by rfl) ⟨4427864, by rfl⟩ : syracuseStep 5903819 = 8855729) B8855729
theorem B1750475 : Blo 1748575 1750475 := bstep (se 1 (by rfl) ⟨1312856, by rfl⟩ : syracuseStep 1750475 = 2625713) B2625713
theorem B102282709 : Blo 1748575 102282709 := bstep (se 7 (by rfl) ⟨1198625, by rfl⟩ : syracuseStep 102282709 = 2397251) B2397251
theorem B3937751 : Blo 1748575 3937751 := bstep (se 1 (by rfl) ⟨2953313, by rfl⟩ : syracuseStep 3937751 = 5906627) B5906627
theorem B1750487 : Blo 1748575 1750487 := bstep (se 1 (by rfl) ⟨1312865, by rfl⟩ : syracuseStep 1750487 = 2625731) B2625731
theorem B1750507 : Blo 1748575 1750507 := bstep (se 1 (by rfl) ⟨1312880, by rfl⟩ : syracuseStep 1750507 = 2625761) B2625761
theorem B1750519 : Blo 1748575 1750519 := bstep (se 1 (by rfl) ⟨1312889, by rfl⟩ : syracuseStep 1750519 = 2625779) B2625779
theorem B1750539 : Blo 1748575 1750539 := bstep (se 1 (by rfl) ⟨1312904, by rfl⟩ : syracuseStep 1750539 = 2625809) B2625809
theorem B1750551 : Blo 1748575 1750551 := bstep (se 1 (by rfl) ⟨1312913, by rfl⟩ : syracuseStep 1750551 = 2625827) B2625827
theorem B1750571 : Blo 1748575 1750571 := bstep (se 1 (by rfl) ⟨1312928, by rfl⟩ : syracuseStep 1750571 = 2625857) B2625857
theorem B4429363 : Blo 1748575 4429363 := bstep (se 1 (by rfl) ⟨3322022, by rfl⟩ : syracuseStep 4429363 = 6644045) B6644045
theorem B12605003 : Blo 1748575 12605003 := bstep (se 1 (by rfl) ⟨9453752, by rfl⟩ : syracuseStep 12605003 = 18907505) B18907505
theorem B28382795 : Blo 1748575 28382795 := bstep (se 1 (by rfl) ⟨21287096, by rfl⟩ : syracuseStep 28382795 = 42574193) B42574193
theorem B3937931 : Blo 1748575 3937931 := bstep (se 1 (by rfl) ⟨2953448, by rfl⟩ : syracuseStep 3937931 = 5906897) B5906897
theorem B6641297 : Blo 1748575 6641297 := bstep (se 2 (by rfl) ⟨2490486, by rfl⟩ : syracuseStep 6641297 = 4980973) B4980973
theorem B4429505 : Blo 1748575 4429505 := bstep (se 2 (by rfl) ⟨1661064, by rfl⟩ : syracuseStep 4429505 = 3322129) B3322129
theorem B3937985 : Blo 1748575 3937985 := bstep (se 2 (by rfl) ⟨1476744, by rfl⟩ : syracuseStep 3937985 = 2953489) B2953489
theorem B21288653 : Blo 1748575 21288653 := bstep (se 3 (by rfl) ⟨3991622, by rfl⟩ : syracuseStep 21288653 = 7983245) B7983245
theorem B5904089 : Blo 1748575 5904089 := bstep (se 2 (by rfl) ⟨2214033, by rfl⟩ : syracuseStep 5904089 = 4428067) B4428067
theorem B6305501 : Blo 1748575 6305501 := bstep (se 3 (by rfl) ⟨1182281, by rfl⟩ : syracuseStep 6305501 = 2364563) B2364563
theorem B12613421 : Blo 1748575 12613421 := bstep (se 3 (by rfl) ⟨2365016, by rfl⟩ : syracuseStep 12613421 = 4730033) B4730033
theorem B9959233 : Blo 1748575 9959233 := bstep (se 2 (by rfl) ⟨3734712, by rfl⟩ : syracuseStep 9959233 = 7469425) B7469425
theorem B121157477 : Blo 1748575 121157477 := bstep (se 4 (by rfl) ⟨11358513, by rfl⟩ : syracuseStep 121157477 = 22717027) B22717027
theorem B3938201 : Blo 1748575 3938201 := bstep (se 2 (by rfl) ⟨1476825, by rfl⟩ : syracuseStep 3938201 = 2953651) B2953651
theorem B16816049 : Blo 1748575 16816049 := bstep (se 2 (by rfl) ⟨6306018, by rfl⟩ : syracuseStep 16816049 = 12612037) B12612037
theorem B3938291 : Blo 1748575 3938291 := bstep (se 1 (by rfl) ⟨2953718, by rfl⟩ : syracuseStep 3938291 = 5907437) B5907437
theorem B3938327 : Blo 1748575 3938327 := bstep (se 1 (by rfl) ⟨2953745, by rfl⟩ : syracuseStep 3938327 = 5907491) B5907491
theorem B14948387 : Blo 1748575 14948387 := bstep (se 1 (by rfl) ⟨11211290, by rfl⟩ : syracuseStep 14948387 = 22422581) B22422581
theorem B11212931 : Blo 1748575 11212931 := bstep (se 1 (by rfl) ⟨8409698, by rfl⟩ : syracuseStep 11212931 = 16819397) B16819397
theorem B3938507 : Blo 1748575 3938507 := bstep (se 1 (by rfl) ⟨2953880, by rfl⟩ : syracuseStep 3938507 = 5907761) B5907761
theorem B7469273 : Blo 1748575 7469273 := bstep (se 2 (by rfl) ⟨2800977, by rfl⟩ : syracuseStep 7469273 = 5601955) B5601955
theorem B3938561 : Blo 1748575 3938561 := bstep (se 2 (by rfl) ⟨1476960, by rfl⟩ : syracuseStep 3938561 = 2953921) B2953921
theorem B7190801 : Blo 1748575 7190801 := bstep (se 2 (by rfl) ⟨2696550, by rfl⟩ : syracuseStep 7190801 = 5393101) B5393101
theorem B5757335 : Blo 1748575 5757335 := bstep (se 1 (by rfl) ⟨4318001, by rfl⟩ : syracuseStep 5757335 = 8636003) B8636003
theorem B6642071 : Blo 1748575 6642071 := bstep (se 1 (by rfl) ⟨4981553, by rfl⟩ : syracuseStep 6642071 = 9963107) B9963107
theorem B5904791 : Blo 1748575 5904791 := bstep (se 1 (by rfl) ⟨4428593, by rfl⟩ : syracuseStep 5904791 = 8857187) B8857187
theorem B21559769 : Blo 1748575 21559769 := bstep (se 2 (by rfl) ⟨8084913, by rfl⟩ : syracuseStep 21559769 = 16169827) B16169827
theorem B3938777 : Blo 1748575 3938777 := bstep (se 2 (by rfl) ⟨1477041, by rfl⟩ : syracuseStep 3938777 = 2954083) B2954083
theorem B5986781 : Blo 1748575 5986781 := bstep (se 3 (by rfl) ⟨1122521, by rfl⟩ : syracuseStep 5986781 = 2245043) B2245043
theorem B8854109 : Blo 1748575 8854109 := bstep (se 3 (by rfl) ⟨1660145, by rfl⟩ : syracuseStep 8854109 = 3320291) B3320291
theorem B6642269 : Blo 1748575 6642269 := bstep (se 3 (by rfl) ⟨1245425, by rfl⟩ : syracuseStep 6642269 = 2490851) B2490851
theorem B50420465 : Blo 1748575 50420465 := bstep (se 2 (by rfl) ⟨18907674, by rfl⟩ : syracuseStep 50420465 = 37815349) B37815349
theorem B2661131 : Blo 1748575 2661131 := bstep (se 1 (by rfl) ⟨1995848, by rfl⟩ : syracuseStep 2661131 = 3991697) B3991697
theorem B3152663 : Blo 1748575 3152663 := bstep (se 1 (by rfl) ⟨2364497, by rfl⟩ : syracuseStep 3152663 = 4728995) B4728995
theorem B4979549 : Blo 1748575 4979549 := bstep (se 3 (by rfl) ⟨933665, by rfl⟩ : syracuseStep 4979549 = 1867331) B1867331
theorem B19938149 : Blo 1748575 19938149 := bstep (se 4 (by rfl) ⟨1869201, by rfl⟩ : syracuseStep 19938149 = 3738403) B3738403
theorem B5905331 : Blo 1748575 5905331 := bstep (se 1 (by rfl) ⟨4428998, by rfl⟩ : syracuseStep 5905331 = 8857997) B8857997
theorem B4430771 : Blo 1748575 4430771 := bstep (se 1 (by rfl) ⟨3323078, by rfl⟩ : syracuseStep 4430771 = 6646157) B6646157
theorem B5905601 : Blo 1748575 5905601 := bstep (se 2 (by rfl) ⟨2214600, by rfl⟩ : syracuseStep 5905601 = 4429201) B4429201
theorem B14187737 : Blo 1748575 14187737 := bstep (se 2 (by rfl) ⟨5320401, by rfl⟩ : syracuseStep 14187737 = 10640803) B10640803
theorem B2800907 : Blo 1748575 2800907 := bstep (se 1 (by rfl) ⟨2100680, by rfl⟩ : syracuseStep 2800907 = 4201361) B4201361
theorem B2801099 : Blo 1748575 2801099 := bstep (se 1 (by rfl) ⟨2100824, by rfl⟩ : syracuseStep 2801099 = 4201649) B4201649
theorem B2489945 : Blo 1748575 2489945 := bstep (se 2 (by rfl) ⟨933729, by rfl⟩ : syracuseStep 2489945 = 1867459) B1867459
theorem B3735191 : Blo 1748575 3735191 := bstep (se 1 (by rfl) ⟨2801393, by rfl⟩ : syracuseStep 3735191 = 5602787) B5602787
theorem B409001669 : Blo 1748575 409001669 := bstep (se 4 (by rfl) ⟨38343906, by rfl⟩ : syracuseStep 409001669 = 76687813) B76687813
theorem B2490059 : Blo 1748575 2490059 := bstep (se 1 (by rfl) ⟨1867544, by rfl⟩ : syracuseStep 2490059 = 3735089) B3735089
theorem B5906141 : Blo 1748575 5906141 := bstep (se 3 (by rfl) ⟨1107401, by rfl⟩ : syracuseStep 5906141 = 2214803) B2214803
theorem B7470913 : Blo 1748575 7470913 := bstep (se 2 (by rfl) ⟨2801592, by rfl⟩ : syracuseStep 7470913 = 5603185) B5603185
theorem B3735499 : Blo 1748575 3735499 := bstep (se 1 (by rfl) ⟨2801624, by rfl⟩ : syracuseStep 3735499 = 5603249) B5603249
theorem B6643741 : Blo 1748575 6643741 := bstep (se 3 (by rfl) ⟨1245701, by rfl⟩ : syracuseStep 6643741 = 2491403) B2491403
theorem B5906519 : Blo 1748575 5906519 := bstep (se 1 (by rfl) ⟨4429889, by rfl⟩ : syracuseStep 5906519 = 8859779) B8859779
theorem B33628405 : Blo 1748575 33628405 := bstep (se 5 (by rfl) ⟨1576331, by rfl⟩ : syracuseStep 33628405 = 3152663) B3152663
theorem B4981007 : Blo 1748575 4981007 := bstep (se 1 (by rfl) ⟨3735755, by rfl⟩ : syracuseStep 4981007 = 7471511) B7471511
theorem B3735841 : Blo 1748575 3735841 := bstep (se 2 (by rfl) ⟨1400940, by rfl⟩ : syracuseStep 3735841 = 2801881) B2801881
theorem B3154235 : Blo 1748575 3154235 := bstep (se 1 (by rfl) ⟨2365676, by rfl⟩ : syracuseStep 3154235 = 4731353) B4731353
theorem B2490697 : Blo 1748575 2490697 := bstep (se 2 (by rfl) ⟨934011, by rfl⟩ : syracuseStep 2490697 = 1868023) B1868023
theorem B9462295 : Blo 1748575 9462295 := bstep (se 1 (by rfl) ⟨7096721, by rfl⟩ : syracuseStep 9462295 = 14193443) B14193443
theorem B5907005 : Blo 1748575 5907005 := bstep (se 3 (by rfl) ⟨1107563, by rfl⟩ : syracuseStep 5907005 = 2215127) B2215127
theorem B3154567 : Blo 1748575 3154567 := bstep (se 1 (by rfl) ⟨2365925, by rfl⟩ : syracuseStep 3154567 = 4731851) B4731851
theorem B3736439 : Blo 1748575 3736439 := bstep (se 1 (by rfl) ⟨2802329, by rfl⟩ : syracuseStep 3736439 = 5604659) B5604659
theorem B4727699 : Blo 1748575 4727699 := bstep (se 1 (by rfl) ⟨3545774, by rfl⟩ : syracuseStep 4727699 = 7091549) B7091549
theorem B19170199 : Blo 1748575 19170199 := bstep (se 1 (by rfl) ⟨14377649, by rfl⟩ : syracuseStep 19170199 = 28755299) B28755299
theorem B9585611 : Blo 1748575 9585611 := bstep (se 1 (by rfl) ⟨7189208, by rfl⟩ : syracuseStep 9585611 = 14378417) B14378417
theorem B98370517 : Blo 1748575 98370517 := bstep (se 7 (by rfl) ⟨1152779, by rfl⟩ : syracuseStep 98370517 = 2305559) B2305559
theorem B7472195 : Blo 1748575 7472195 := bstep (se 1 (by rfl) ⟨5604146, by rfl⟩ : syracuseStep 7472195 = 11208293) B11208293
theorem B4981895 : Blo 1748575 4981895 := bstep (se 1 (by rfl) ⟨3736421, by rfl⟩ : syracuseStep 4981895 = 7472843) B7472843
theorem B4203667 : Blo 1748575 4203667 := bstep (se 1 (by rfl) ⟨3152750, by rfl⟩ : syracuseStep 4203667 = 6305501) B6305501
theorem B4982077 : Blo 1748575 4982077 := bstep (se 3 (by rfl) ⟨934139, by rfl⟩ : syracuseStep 4982077 = 1868279) B1868279
theorem B2213239 : Blo 1748575 2213239 := bstep (se 1 (by rfl) ⟨1659929, by rfl⟩ : syracuseStep 2213239 = 3319859) B3319859
theorem B2622863 : Blo 1748575 2622863 := bstep (se 1 (by rfl) ⟨1967147, by rfl⟩ : syracuseStep 2622863 = 3934295) B3934295
theorem B1967503 : Blo 1748575 1967503 := bstep (se 1 (by rfl) ⟨1475627, by rfl⟩ : syracuseStep 1967503 = 2951255) B2951255
theorem B14943635 : Blo 1748575 14943635 := bstep (se 1 (by rfl) ⟨11207726, by rfl⟩ : syracuseStep 14943635 = 22415453) B22415453
theorem B2622905 : Blo 1748575 2622905 := bstep (se 2 (by rfl) ⟨983589, by rfl⟩ : syracuseStep 2622905 = 1967179) B1967179
theorem B7472569 : Blo 1748575 7472569 := bstep (se 2 (by rfl) ⟨2802213, by rfl⟩ : syracuseStep 7472569 = 5604427) B5604427
theorem B2622983 : Blo 1748575 2622983 := bstep (se 1 (by rfl) ⟨1967237, by rfl⟩ : syracuseStep 2622983 = 3934475) B3934475
theorem B4793867 : Blo 1748575 4793867 := bstep (se 1 (by rfl) ⟨3595400, by rfl⟩ : syracuseStep 4793867 = 7190801) B7190801
theorem B5047823 : Blo 1748575 5047823 := bstep (se 1 (by rfl) ⟨3785867, by rfl⟩ : syracuseStep 5047823 = 7571735) B7571735
theorem B4982305 : Blo 1748575 4982305 := bstep (se 2 (by rfl) ⟨1868364, by rfl⟩ : syracuseStep 4982305 = 3736729) B3736729
theorem B2623019 : Blo 1748575 2623019 := bstep (se 1 (by rfl) ⟨1967264, by rfl⟩ : syracuseStep 2623019 = 3934529) B3934529
theorem B2623049 : Blo 1748575 2623049 := bstep (se 2 (by rfl) ⟨983643, by rfl⟩ : syracuseStep 2623049 = 1967287) B1967287
theorem B3991187 : Blo 1748575 3991187 := bstep (se 1 (by rfl) ⟨2993390, by rfl⟩ : syracuseStep 3991187 = 5986781) B5986781
theorem B2623163 : Blo 1748575 2623163 := bstep (se 1 (by rfl) ⟨1967372, by rfl⟩ : syracuseStep 2623163 = 3934745) B3934745
theorem B2213563 : Blo 1748575 2213563 := bstep (se 1 (by rfl) ⟨1660172, by rfl⟩ : syracuseStep 2213563 = 3320345) B3320345
theorem B2623223 : Blo 1748575 2623223 := bstep (se 1 (by rfl) ⟨1967417, by rfl⟩ : syracuseStep 2623223 = 3934835) B3934835
theorem B2623247 : Blo 1748575 2623247 := bstep (se 1 (by rfl) ⟨1967435, by rfl⟩ : syracuseStep 2623247 = 3934871) B3934871
theorem B7472911 : Blo 1748575 7472911 := bstep (se 1 (by rfl) ⟨5604683, by rfl⟩ : syracuseStep 7472911 = 11209367) B11209367
theorem B6735649 : Blo 1748575 6735649 := bstep (se 2 (by rfl) ⟨2525868, by rfl⟩ : syracuseStep 6735649 = 5051737) B5051737
theorem B2623289 : Blo 1748575 2623289 := bstep (se 2 (by rfl) ⟨983733, by rfl⟩ : syracuseStep 2623289 = 1967467) B1967467
theorem B33613643 : Blo 1748575 33613643 := bstep (se 1 (by rfl) ⟨25210232, by rfl⟩ : syracuseStep 33613643 = 50420465) B50420465
theorem B4982647 : Blo 1748575 4982647 := bstep (se 1 (by rfl) ⟨3736985, by rfl⟩ : syracuseStep 4982647 = 7473971) B7473971
theorem B1968007 : Blo 1748575 1968007 := bstep (se 1 (by rfl) ⟨1476005, by rfl⟩ : syracuseStep 1968007 = 2952011) B2952011
theorem B2623367 : Blo 1748575 2623367 := bstep (se 1 (by rfl) ⟨1967525, by rfl⟩ : syracuseStep 2623367 = 3935051) B3935051
theorem B3319699 : Blo 1748575 3319699 := bstep (se 1 (by rfl) ⟨2489774, by rfl⟩ : syracuseStep 3319699 = 4979549) B4979549
theorem B2623403 : Blo 1748575 2623403 := bstep (se 1 (by rfl) ⟨1967552, by rfl⟩ : syracuseStep 2623403 = 3935105) B3935105
theorem B2951113 : Blo 1748575 2951113 := bstep (se 2 (by rfl) ⟨1106667, by rfl⟩ : syracuseStep 2951113 = 2213335) B2213335
theorem B2623433 : Blo 1748575 2623433 := bstep (se 2 (by rfl) ⟨983787, by rfl⟩ : syracuseStep 2623433 = 1967575) B1967575
theorem B7096349 : Blo 1748575 7096349 := bstep (se 3 (by rfl) ⟨1330565, by rfl⟩ : syracuseStep 7096349 = 2661131) B2661131
theorem B2623547 : Blo 1748575 2623547 := bstep (se 1 (by rfl) ⟨1967660, by rfl⟩ : syracuseStep 2623547 = 3935321) B3935321
theorem B1968187 : Blo 1748575 1968187 := bstep (se 1 (by rfl) ⟨1476140, by rfl⟩ : syracuseStep 1968187 = 2952281) B2952281
theorem B9963607 : Blo 1748575 9963607 := bstep (se 1 (by rfl) ⟨7472705, by rfl⟩ : syracuseStep 9963607 = 14945411) B14945411
theorem B2623607 : Blo 1748575 2623607 := bstep (se 1 (by rfl) ⟨1967705, by rfl⟩ : syracuseStep 2623607 = 3935411) B3935411
theorem B2623631 : Blo 1748575 2623631 := bstep (se 1 (by rfl) ⟨1967723, by rfl⟩ : syracuseStep 2623631 = 3935447) B3935447
theorem B2623673 : Blo 1748575 2623673 := bstep (se 2 (by rfl) ⟨983877, by rfl⟩ : syracuseStep 2623673 = 1967755) B1967755
theorem B2623751 : Blo 1748575 2623751 := bstep (se 1 (by rfl) ⟨1967813, by rfl⟩ : syracuseStep 2623751 = 3935627) B3935627
theorem B2623787 : Blo 1748575 2623787 := bstep (se 1 (by rfl) ⟨1967840, by rfl⟩ : syracuseStep 2623787 = 3935681) B3935681
theorem B2623817 : Blo 1748575 2623817 := bstep (se 2 (by rfl) ⟨983931, by rfl⟩ : syracuseStep 2623817 = 1967863) B1967863
theorem B4426103 : Blo 1748575 4426103 := bstep (se 1 (by rfl) ⟨3319577, by rfl⟩ : syracuseStep 4426103 = 6639155) B6639155
theorem B3934583 : Blo 1748575 3934583 := bstep (se 1 (by rfl) ⟨2950937, by rfl⟩ : syracuseStep 3934583 = 5901875) B5901875
theorem B2623931 : Blo 1748575 2623931 := bstep (se 1 (by rfl) ⟨1967948, by rfl⟩ : syracuseStep 2623931 = 3935897) B3935897
theorem B2623991 : Blo 1748575 2623991 := bstep (se 1 (by rfl) ⟨1967993, by rfl⟩ : syracuseStep 2623991 = 3935987) B3935987
theorem B2624015 : Blo 1748575 2624015 := bstep (se 1 (by rfl) ⟨1968011, by rfl⟩ : syracuseStep 2624015 = 3936023) B3936023
theorem B1968655 : Blo 1748575 1968655 := bstep (se 1 (by rfl) ⟨1476491, by rfl⟩ : syracuseStep 1968655 = 2952983) B2952983
theorem B3934763 : Blo 1748575 3934763 := bstep (se 1 (by rfl) ⟨2951072, by rfl⟩ : syracuseStep 3934763 = 5902145) B5902145
theorem B2624057 : Blo 1748575 2624057 := bstep (se 2 (by rfl) ⟨984021, by rfl⟩ : syracuseStep 2624057 = 1968043) B1968043
theorem B2951815 : Blo 1748575 2951815 := bstep (se 1 (by rfl) ⟨2213861, by rfl⟩ : syracuseStep 2951815 = 4427723) B4427723
theorem B2624135 : Blo 1748575 2624135 := bstep (se 1 (by rfl) ⟨1968101, by rfl⟩ : syracuseStep 2624135 = 3936203) B3936203
theorem B2214535 : Blo 1748575 2214535 := bstep (se 1 (by rfl) ⟨1660901, by rfl⟩ : syracuseStep 2214535 = 3321803) B3321803
theorem B2624171 : Blo 1748575 2624171 := bstep (se 1 (by rfl) ⟨1968128, by rfl⟩ : syracuseStep 2624171 = 3936257) B3936257
theorem B2624201 : Blo 1748575 2624201 := bstep (se 2 (by rfl) ⟨984075, by rfl⟩ : syracuseStep 2624201 = 1968151) B1968151
theorem B4983581 : Blo 1748575 4983581 := bstep (se 3 (by rfl) ⟨934421, by rfl⟩ : syracuseStep 4983581 = 1868843) B1868843
theorem B4262699 : Blo 1748575 4262699 := bstep (se 1 (by rfl) ⟨3197024, by rfl⟩ : syracuseStep 4262699 = 6394049) B6394049
theorem B2624315 : Blo 1748575 2624315 := bstep (se 1 (by rfl) ⟨1968236, by rfl⟩ : syracuseStep 2624315 = 3936473) B3936473
theorem B8858483 : Blo 1748575 8858483 := bstep (se 1 (by rfl) ⟨6643862, by rfl⟩ : syracuseStep 8858483 = 13287725) B13287725
theorem B6646643 : Blo 1748575 6646643 := bstep (se 1 (by rfl) ⟨4984982, by rfl⟩ : syracuseStep 6646643 = 9969965) B9969965
theorem B2624375 : Blo 1748575 2624375 := bstep (se 1 (by rfl) ⟨1968281, by rfl⟩ : syracuseStep 2624375 = 3936563) B3936563
theorem B2624399 : Blo 1748575 2624399 := bstep (se 1 (by rfl) ⟨1968299, by rfl⟩ : syracuseStep 2624399 = 3936599) B3936599
theorem B3935123 : Blo 1748575 3935123 := bstep (se 1 (by rfl) ⟨2951342, by rfl⟩ : syracuseStep 3935123 = 5902685) B5902685
theorem B2624441 : Blo 1748575 2624441 := bstep (se 2 (by rfl) ⟨984165, by rfl⟩ : syracuseStep 2624441 = 1968331) B1968331
theorem B3935177 : Blo 1748575 3935177 := bstep (se 2 (by rfl) ⟨1475691, by rfl⟩ : syracuseStep 3935177 = 2951383) B2951383
theorem B3320777 : Blo 1748575 3320777 := bstep (se 2 (by rfl) ⟨1245291, by rfl⟩ : syracuseStep 3320777 = 2490583) B2490583
theorem B4205513 : Blo 1748575 4205513 := bstep (se 2 (by rfl) ⟨1577067, by rfl⟩ : syracuseStep 4205513 = 3154135) B3154135
theorem B2624519 : Blo 1748575 2624519 := bstep (se 1 (by rfl) ⟨1968389, by rfl⟩ : syracuseStep 2624519 = 3936779) B3936779
theorem B1969159 : Blo 1748575 1969159 := bstep (se 1 (by rfl) ⟨1476869, by rfl⟩ : syracuseStep 1969159 = 2953739) B2953739
theorem B2624555 : Blo 1748575 2624555 := bstep (se 1 (by rfl) ⟨1968416, by rfl⟩ : syracuseStep 2624555 = 3936833) B3936833
theorem B2214955 : Blo 1748575 2214955 := bstep (se 1 (by rfl) ⟨1661216, by rfl⟩ : syracuseStep 2214955 = 3322433) B3322433
theorem B2624585 : Blo 1748575 2624585 := bstep (se 2 (by rfl) ⟨984219, by rfl⟩ : syracuseStep 2624585 = 1968439) B1968439
theorem B4983923 : Blo 1748575 4983923 := bstep (se 1 (by rfl) ⟨3737942, by rfl⟩ : syracuseStep 4983923 = 7475885) B7475885
theorem B15969413 : Blo 1748575 15969413 := bstep (se 4 (by rfl) ⟨1497132, by rfl⟩ : syracuseStep 15969413 = 2994265) B2994265
theorem B4795577 : Blo 1748575 4795577 := bstep (se 2 (by rfl) ⟨1798341, by rfl⟩ : syracuseStep 4795577 = 3596683) B3596683
theorem B2624699 : Blo 1748575 2624699 := bstep (se 1 (by rfl) ⟨1968524, by rfl⟩ : syracuseStep 2624699 = 3937049) B3937049
theorem B1969339 : Blo 1748575 1969339 := bstep (se 1 (by rfl) ⟨1477004, by rfl⟩ : syracuseStep 1969339 = 2954009) B2954009
theorem B5762249 : Blo 1748575 5762249 := bstep (se 2 (by rfl) ⟨2160843, by rfl⟩ : syracuseStep 5762249 = 4321687) B4321687
theorem B2624759 : Blo 1748575 2624759 := bstep (se 1 (by rfl) ⟨1968569, by rfl⟩ : syracuseStep 2624759 = 3937139) B3937139
theorem B2952463 : Blo 1748575 2952463 := bstep (se 1 (by rfl) ⟨2214347, by rfl⟩ : syracuseStep 2952463 = 4428695) B4428695
theorem B2624783 : Blo 1748575 2624783 := bstep (se 1 (by rfl) ⟨1968587, by rfl⟩ : syracuseStep 2624783 = 3937175) B3937175
theorem B5606671 : Blo 1748575 5606671 := bstep (se 1 (by rfl) ⟨4205003, by rfl⟩ : syracuseStep 5606671 = 8410007) B8410007
theorem B2215183 : Blo 1748575 2215183 := bstep (se 1 (by rfl) ⟨1661387, by rfl⟩ : syracuseStep 2215183 = 3322775) B3322775
theorem B2624825 : Blo 1748575 2624825 := bstep (se 2 (by rfl) ⟨984309, by rfl⟩ : syracuseStep 2624825 = 1968619) B1968619
theorem B4427095 : Blo 1748575 4427095 := bstep (se 1 (by rfl) ⟨3320321, by rfl⟩ : syracuseStep 4427095 = 6640643) B6640643
theorem B8858969 : Blo 1748575 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B4263283 : Blo 1748575 4263283 := bstep (se 1 (by rfl) ⟨3197462, by rfl⟩ : syracuseStep 4263283 = 6394925) B6394925
theorem B34540931 : Blo 1748575 34540931 := bstep (se 1 (by rfl) ⟨25905698, by rfl⟩ : syracuseStep 34540931 = 51811397) B51811397
theorem B2624903 : Blo 1748575 2624903 := bstep (se 1 (by rfl) ⟨1968677, by rfl⟩ : syracuseStep 2624903 = 3937355) B3937355
theorem B2624939 : Blo 1748575 2624939 := bstep (se 1 (by rfl) ⟨1968704, by rfl⟩ : syracuseStep 2624939 = 3937409) B3937409
theorem B2624969 : Blo 1748575 2624969 := bstep (se 2 (by rfl) ⟨984363, by rfl⟩ : syracuseStep 2624969 = 1968727) B1968727
theorem B2625083 : Blo 1748575 2625083 := bstep (se 1 (by rfl) ⟨1968812, by rfl⟩ : syracuseStep 2625083 = 3937625) B3937625
theorem B4984379 : Blo 1748575 4984379 := bstep (se 1 (by rfl) ⟨3738284, by rfl⟩ : syracuseStep 4984379 = 7476569) B7476569
theorem B2625143 : Blo 1748575 2625143 := bstep (se 1 (by rfl) ⟨1968857, by rfl⟩ : syracuseStep 2625143 = 3937715) B3937715
theorem B13291127 : Blo 1748575 13291127 := bstep (se 1 (by rfl) ⟨9968345, by rfl⟩ : syracuseStep 13291127 = 19936691) B19936691
theorem B1748615 : Blo 1748575 1748615 := bstep (se 1 (by rfl) ⟨1311461, by rfl⟩ : syracuseStep 1748615 = 2622923) B2622923
theorem B4427399 : Blo 1748575 4427399 := bstep (se 1 (by rfl) ⟨3320549, by rfl⟩ : syracuseStep 4427399 = 6641099) B6641099
theorem B3935879 : Blo 1748575 3935879 := bstep (se 1 (by rfl) ⟨2951909, by rfl⟩ : syracuseStep 3935879 = 5903819) B5903819
theorem B1748623 : Blo 1748575 1748623 := bstep (se 1 (by rfl) ⟨1311467, by rfl⟩ : syracuseStep 1748623 = 2622935) B2622935
theorem B2625167 : Blo 1748575 2625167 := bstep (se 1 (by rfl) ⟨1968875, by rfl⟩ : syracuseStep 2625167 = 3937751) B3937751
theorem B2625209 : Blo 1748575 2625209 := bstep (se 2 (by rfl) ⟨984453, by rfl⟩ : syracuseStep 2625209 = 1968907) B1968907
theorem B1748667 : Blo 1748575 1748667 := bstep (se 1 (by rfl) ⟨1311500, by rfl⟩ : syracuseStep 1748667 = 2623001) B2623001
theorem B1748743 : Blo 1748575 1748743 := bstep (se 1 (by rfl) ⟨1311557, by rfl⟩ : syracuseStep 1748743 = 2623115) B2623115
theorem B2625287 : Blo 1748575 2625287 := bstep (se 1 (by rfl) ⟨1968965, by rfl⟩ : syracuseStep 2625287 = 3937931) B3937931
theorem B4427531 : Blo 1748575 4427531 := bstep (se 1 (by rfl) ⟨3320648, by rfl⟩ : syracuseStep 4427531 = 6641297) B6641297
theorem B1748751 : Blo 1748575 1748751 := bstep (se 1 (by rfl) ⟨1311563, by rfl⟩ : syracuseStep 1748751 = 2623127) B2623127
theorem B3321643 : Blo 1748575 3321643 := bstep (se 1 (by rfl) ⟨2491232, by rfl⟩ : syracuseStep 3321643 = 4982465) B4982465
theorem B2953003 : Blo 1748575 2953003 := bstep (se 1 (by rfl) ⟨2214752, by rfl⟩ : syracuseStep 2953003 = 4429505) B4429505
theorem B2625323 : Blo 1748575 2625323 := bstep (se 1 (by rfl) ⟨1968992, by rfl⟩ : syracuseStep 2625323 = 3937985) B3937985
theorem B14192435 : Blo 1748575 14192435 := bstep (se 1 (by rfl) ⟨10644326, by rfl⟩ : syracuseStep 14192435 = 21288653) B21288653
theorem B1748795 : Blo 1748575 1748795 := bstep (se 1 (by rfl) ⟨1311596, by rfl⟩ : syracuseStep 1748795 = 2623193) B2623193
theorem B3936059 : Blo 1748575 3936059 := bstep (se 1 (by rfl) ⟨2952044, by rfl⟩ : syracuseStep 3936059 = 5904089) B5904089
theorem B4730683 : Blo 1748575 4730683 := bstep (se 1 (by rfl) ⟨3548012, by rfl⟩ : syracuseStep 4730683 = 7096025) B7096025
theorem B2625353 : Blo 1748575 2625353 := bstep (se 2 (by rfl) ⟨984507, by rfl⟩ : syracuseStep 2625353 = 1969015) B1969015
theorem B8408947 : Blo 1748575 8408947 := bstep (se 1 (by rfl) ⟨6306710, by rfl⟩ : syracuseStep 8408947 = 12613421) B12613421
theorem B3321719 : Blo 1748575 3321719 := bstep (se 1 (by rfl) ⟨2491289, by rfl⟩ : syracuseStep 3321719 = 4982579) B4982579
theorem B1748871 : Blo 1748575 1748871 := bstep (se 1 (by rfl) ⟨1311653, by rfl⟩ : syracuseStep 1748871 = 2623307) B2623307
theorem B1748879 : Blo 1748575 1748879 := bstep (se 1 (by rfl) ⟨1311659, by rfl⟩ : syracuseStep 1748879 = 2623319) B2623319
theorem B3936185 : Blo 1748575 3936185 := bstep (se 2 (by rfl) ⟨1476069, by rfl⟩ : syracuseStep 3936185 = 2952139) B2952139
theorem B2953145 : Blo 1748575 2953145 := bstep (se 2 (by rfl) ⟨1107429, by rfl⟩ : syracuseStep 2953145 = 2214859) B2214859
theorem B1748923 : Blo 1748575 1748923 := bstep (se 1 (by rfl) ⟨1311692, by rfl⟩ : syracuseStep 1748923 = 2623385) B2623385
theorem B2625467 : Blo 1748575 2625467 := bstep (se 1 (by rfl) ⟨1969100, by rfl⟩ : syracuseStep 2625467 = 3938201) B3938201
theorem B14184395 : Blo 1748575 14184395 := bstep (se 1 (by rfl) ⟨10638296, by rfl⟩ : syracuseStep 14184395 = 21276593) B21276593
theorem B11210699 : Blo 1748575 11210699 := bstep (se 1 (by rfl) ⟨8408024, by rfl⟩ : syracuseStep 11210699 = 16816049) B16816049
theorem B2625527 : Blo 1748575 2625527 := bstep (se 1 (by rfl) ⟨1969145, by rfl⟩ : syracuseStep 2625527 = 3938291) B3938291
theorem B1748999 : Blo 1748575 1748999 := bstep (se 1 (by rfl) ⟨1311749, by rfl⟩ : syracuseStep 1748999 = 2623499) B2623499
theorem B1749007 : Blo 1748575 1749007 := bstep (se 1 (by rfl) ⟨1311755, by rfl⟩ : syracuseStep 1749007 = 2623511) B2623511
theorem B2625551 : Blo 1748575 2625551 := bstep (se 1 (by rfl) ⟨1969163, by rfl⟩ : syracuseStep 2625551 = 3938327) B3938327
theorem B13283351 : Blo 1748575 13283351 := bstep (se 1 (by rfl) ⟨9962513, by rfl⟩ : syracuseStep 13283351 = 19925027) B19925027
theorem B9965591 : Blo 1748575 9965591 := bstep (se 1 (by rfl) ⟨7474193, by rfl⟩ : syracuseStep 9965591 = 14948387) B14948387
theorem B30715949 : Blo 1748575 30715949 := bstep (se 3 (by rfl) ⟨5759240, by rfl⟩ : syracuseStep 30715949 = 11518481) B11518481
theorem B1749051 : Blo 1748575 1749051 := bstep (se 1 (by rfl) ⟨1311788, by rfl⟩ : syracuseStep 1749051 = 2623577) B2623577
theorem B2625593 : Blo 1748575 2625593 := bstep (se 2 (by rfl) ⟨984597, by rfl⟩ : syracuseStep 2625593 = 1969195) B1969195
theorem B7475287 : Blo 1748575 7475287 := bstep (se 1 (by rfl) ⟨5606465, by rfl⟩ : syracuseStep 7475287 = 11212931) B11212931
theorem B1749127 : Blo 1748575 1749127 := bstep (se 1 (by rfl) ⟨1311845, by rfl⟩ : syracuseStep 1749127 = 2623691) B2623691
theorem B2625671 : Blo 1748575 2625671 := bstep (se 1 (by rfl) ⟨1969253, by rfl⟩ : syracuseStep 2625671 = 3938507) B3938507
theorem B1749135 : Blo 1748575 1749135 := bstep (se 1 (by rfl) ⟨1311851, by rfl⟩ : syracuseStep 1749135 = 2623703) B2623703
theorem B2625707 : Blo 1748575 2625707 := bstep (se 1 (by rfl) ⟨1969280, by rfl⟩ : syracuseStep 2625707 = 3938561) B3938561
theorem B1749179 : Blo 1748575 1749179 := bstep (se 1 (by rfl) ⟨1311884, by rfl⟩ : syracuseStep 1749179 = 2623769) B2623769
theorem B2625737 : Blo 1748575 2625737 := bstep (se 2 (by rfl) ⟨984651, by rfl⟩ : syracuseStep 2625737 = 1969303) B1969303
theorem B6639853 : Blo 1748575 6639853 := bstep (se 3 (by rfl) ⟨1244972, by rfl⟩ : syracuseStep 6639853 = 2489945) B2489945
theorem B72773873 : Blo 1748575 72773873 := bstep (se 2 (by rfl) ⟨27290202, by rfl⟩ : syracuseStep 72773873 = 54580405) B54580405
theorem B1749255 : Blo 1748575 1749255 := bstep (se 1 (by rfl) ⟨1311941, by rfl⟩ : syracuseStep 1749255 = 2623883) B2623883
theorem B3838223 : Blo 1748575 3838223 := bstep (se 1 (by rfl) ⟨2878667, by rfl⟩ : syracuseStep 3838223 = 5757335) B5757335
theorem B1749263 : Blo 1748575 1749263 := bstep (se 1 (by rfl) ⟨1311947, by rfl⟩ : syracuseStep 1749263 = 2623895) B2623895
theorem B4428047 : Blo 1748575 4428047 := bstep (se 1 (by rfl) ⟨3321035, by rfl⟩ : syracuseStep 4428047 = 6642071) B6642071
theorem B3936527 : Blo 1748575 3936527 := bstep (se 1 (by rfl) ⟨2952395, by rfl⟩ : syracuseStep 3936527 = 5904791) B5904791
theorem B3936545 : Blo 1748575 3936545 := bstep (se 2 (by rfl) ⟨1476204, by rfl⟩ : syracuseStep 3936545 = 2952409) B2952409
theorem B14373179 : Blo 1748575 14373179 := bstep (se 1 (by rfl) ⟨10779884, by rfl⟩ : syracuseStep 14373179 = 21559769) B21559769
theorem B1749307 : Blo 1748575 1749307 := bstep (se 1 (by rfl) ⟨1311980, by rfl⟩ : syracuseStep 1749307 = 2623961) B2623961
theorem B2625851 : Blo 1748575 2625851 := bstep (se 1 (by rfl) ⟨1969388, by rfl⟩ : syracuseStep 2625851 = 3938777) B3938777
theorem B1749383 : Blo 1748575 1749383 := bstep (se 1 (by rfl) ⟨1312037, by rfl⟩ : syracuseStep 1749383 = 2624075) B2624075
theorem B14578055 : Blo 1748575 14578055 := bstep (se 1 (by rfl) ⟨10933541, by rfl⟩ : syracuseStep 14578055 = 21867083) B21867083
theorem B1749391 : Blo 1748575 1749391 := bstep (se 1 (by rfl) ⟨1312043, by rfl⟩ : syracuseStep 1749391 = 2624087) B2624087
theorem B5902739 : Blo 1748575 5902739 := bstep (se 1 (by rfl) ⟨4427054, by rfl⟩ : syracuseStep 5902739 = 8854109) B8854109
theorem B4428179 : Blo 1748575 4428179 := bstep (se 1 (by rfl) ⟨3321134, by rfl⟩ : syracuseStep 4428179 = 6642269) B6642269
theorem B10105273 : Blo 1748575 10105273 := bstep (se 2 (by rfl) ⟨3789477, by rfl⟩ : syracuseStep 10105273 = 7578955) B7578955
theorem B1749435 : Blo 1748575 1749435 := bstep (se 1 (by rfl) ⟨1312076, by rfl⟩ : syracuseStep 1749435 = 2624153) B2624153
theorem B14938577 : Blo 1748575 14938577 := bstep (se 2 (by rfl) ⟨5601966, by rfl⟩ : syracuseStep 14938577 = 11203933) B11203933
theorem B16806365 : Blo 1748575 16806365 := bstep (se 3 (by rfl) ⟨3151193, by rfl⟩ : syracuseStep 16806365 = 6302387) B6302387
theorem B1749511 : Blo 1748575 1749511 := bstep (se 1 (by rfl) ⟨1312133, by rfl⟩ : syracuseStep 1749511 = 2624267) B2624267
theorem B1749519 : Blo 1748575 1749519 := bstep (se 1 (by rfl) ⟨1312139, by rfl⟩ : syracuseStep 1749519 = 2624279) B2624279
theorem B6640157 : Blo 1748575 6640157 := bstep (se 3 (by rfl) ⟨1245029, by rfl⟩ : syracuseStep 6640157 = 2490059) B2490059
theorem B1749563 : Blo 1748575 1749563 := bstep (se 1 (by rfl) ⟨1312172, by rfl⟩ : syracuseStep 1749563 = 2624345) B2624345
theorem B10646077 : Blo 1748575 10646077 := bstep (se 3 (by rfl) ⟨1996139, by rfl⟩ : syracuseStep 10646077 = 3992279) B3992279
theorem B13292099 : Blo 1748575 13292099 := bstep (se 1 (by rfl) ⟨9969074, by rfl⟩ : syracuseStep 13292099 = 19938149) B19938149
theorem B136376945 : Blo 1748575 136376945 := bstep (se 2 (by rfl) ⟨51141354, by rfl⟩ : syracuseStep 136376945 = 102282709) B102282709
theorem B3936887 : Blo 1748575 3936887 := bstep (se 1 (by rfl) ⟨2952665, by rfl⟩ : syracuseStep 3936887 = 5905331) B5905331
theorem B2953847 : Blo 1748575 2953847 := bstep (se 1 (by rfl) ⟨2215385, by rfl⟩ : syracuseStep 2953847 = 4430771) B4430771
theorem B1749639 : Blo 1748575 1749639 := bstep (se 1 (by rfl) ⟨1312229, by rfl⟩ : syracuseStep 1749639 = 2624459) B2624459
theorem B1749647 : Blo 1748575 1749647 := bstep (se 1 (by rfl) ⟨1312235, by rfl⟩ : syracuseStep 1749647 = 2624471) B2624471
theorem B1749691 : Blo 1748575 1749691 := bstep (se 1 (by rfl) ⟨1312268, by rfl⟩ : syracuseStep 1749691 = 2624537) B2624537
theorem B1749767 : Blo 1748575 1749767 := bstep (se 1 (by rfl) ⟨1312325, by rfl⟩ : syracuseStep 1749767 = 2624651) B2624651
theorem B5321483 : Blo 1748575 5321483 := bstep (se 1 (by rfl) ⟨3991112, by rfl⟩ : syracuseStep 5321483 = 7982225) B7982225
theorem B1749775 : Blo 1748575 1749775 := bstep (se 1 (by rfl) ⟨1312331, by rfl⟩ : syracuseStep 1749775 = 2624663) B2624663
theorem B3937067 : Blo 1748575 3937067 := bstep (se 1 (by rfl) ⟨2952800, by rfl⟩ : syracuseStep 3937067 = 5905601) B5905601
theorem B9458491 : Blo 1748575 9458491 := bstep (se 1 (by rfl) ⟨7093868, by rfl⟩ : syracuseStep 9458491 = 14187737) B14187737
theorem B1749819 : Blo 1748575 1749819 := bstep (se 1 (by rfl) ⟨1312364, by rfl⟩ : syracuseStep 1749819 = 2624729) B2624729
theorem B34091891 : Blo 1748575 34091891 := bstep (se 1 (by rfl) ⟨25568918, by rfl⟩ : syracuseStep 34091891 = 51137837) B51137837
theorem B4731763 : Blo 1748575 4731763 := bstep (se 1 (by rfl) ⟨3548822, by rfl⟩ : syracuseStep 4731763 = 7097645) B7097645
theorem B1749895 : Blo 1748575 1749895 := bstep (se 1 (by rfl) ⟨1312421, by rfl⟩ : syracuseStep 1749895 = 2624843) B2624843
theorem B1749903 : Blo 1748575 1749903 := bstep (se 1 (by rfl) ⟨1312427, by rfl⟩ : syracuseStep 1749903 = 2624855) B2624855
theorem B1749947 : Blo 1748575 1749947 := bstep (se 1 (by rfl) ⟨1312460, by rfl⟩ : syracuseStep 1749947 = 2624921) B2624921
theorem B1750023 : Blo 1748575 1750023 := bstep (se 1 (by rfl) ⟨1312517, by rfl⟩ : syracuseStep 1750023 = 2625035) B2625035
theorem B1750031 : Blo 1748575 1750031 := bstep (se 1 (by rfl) ⟨1312523, by rfl⟩ : syracuseStep 1750031 = 2625047) B2625047
theorem B1750075 : Blo 1748575 1750075 := bstep (se 1 (by rfl) ⟨1312556, by rfl⟩ : syracuseStep 1750075 = 2625113) B2625113
theorem B272667779 : Blo 1748575 272667779 := bstep (se 1 (by rfl) ⟨204500834, by rfl⟩ : syracuseStep 272667779 = 409001669) B409001669
theorem B1750151 : Blo 1748575 1750151 := bstep (se 1 (by rfl) ⟨1312613, by rfl⟩ : syracuseStep 1750151 = 2625227) B2625227
theorem B1750159 : Blo 1748575 1750159 := bstep (se 1 (by rfl) ⟨1312619, by rfl⟩ : syracuseStep 1750159 = 2625239) B2625239
theorem B3937427 : Blo 1748575 3937427 := bstep (se 1 (by rfl) ⟨2953070, by rfl⟩ : syracuseStep 3937427 = 5906141) B5906141
theorem B1750203 : Blo 1748575 1750203 := bstep (se 1 (by rfl) ⟨1312652, by rfl⟩ : syracuseStep 1750203 = 2625305) B2625305
theorem B3937481 : Blo 1748575 3937481 := bstep (se 2 (by rfl) ⟨1476555, by rfl⟩ : syracuseStep 3937481 = 2953111) B2953111
theorem B1750279 : Blo 1748575 1750279 := bstep (se 1 (by rfl) ⟨1312709, by rfl⟩ : syracuseStep 1750279 = 2625419) B2625419
theorem B1750287 : Blo 1748575 1750287 := bstep (se 1 (by rfl) ⟨1312715, by rfl⟩ : syracuseStep 1750287 = 2625431) B2625431
theorem B1750331 : Blo 1748575 1750331 := bstep (se 1 (by rfl) ⟨1312748, by rfl⟩ : syracuseStep 1750331 = 2625497) B2625497
theorem B23950727 : Blo 1748575 23950727 := bstep (se 1 (by rfl) ⟨17963045, by rfl⟩ : syracuseStep 23950727 = 35926091) B35926091
theorem B1750407 : Blo 1748575 1750407 := bstep (se 1 (by rfl) ⟨1312805, by rfl⟩ : syracuseStep 1750407 = 2625611) B2625611
theorem B1750415 : Blo 1748575 1750415 := bstep (se 1 (by rfl) ⟨1312811, by rfl⟩ : syracuseStep 1750415 = 2625623) B2625623
theorem B8861075 : Blo 1748575 8861075 := bstep (se 1 (by rfl) ⟨6645806, by rfl⟩ : syracuseStep 8861075 = 13291613) B13291613
theorem B1750459 : Blo 1748575 1750459 := bstep (se 1 (by rfl) ⟨1312844, by rfl⟩ : syracuseStep 1750459 = 2625689) B2625689
theorem B4429313 : Blo 1748575 4429313 := bstep (se 2 (by rfl) ⟨1660992, by rfl⟩ : syracuseStep 4429313 = 3321985) B3321985
theorem B1750535 : Blo 1748575 1750535 := bstep (se 1 (by rfl) ⟨1312901, by rfl⟩ : syracuseStep 1750535 = 2625803) B2625803
theorem B1750543 : Blo 1748575 1750543 := bstep (se 1 (by rfl) ⟨1312907, by rfl⟩ : syracuseStep 1750543 = 2625815) B2625815
theorem B5904143 : Blo 1748575 5904143 := bstep (se 1 (by rfl) ⟨4428107, by rfl⟩ : syracuseStep 5904143 = 8856215) B8856215
theorem B8853299 : Blo 1748575 8853299 := bstep (se 1 (by rfl) ⟨6639974, by rfl⟩ : syracuseStep 8853299 = 13279949) B13279949
theorem B78780235 : Blo 1748575 78780235 := bstep (se 1 (by rfl) ⟨59085176, by rfl⟩ : syracuseStep 78780235 = 118170353) B118170353
theorem B4429687 : Blo 1748575 4429687 := bstep (se 1 (by rfl) ⟨3322265, by rfl⟩ : syracuseStep 4429687 = 6644531) B6644531
theorem B3938183 : Blo 1748575 3938183 := bstep (se 1 (by rfl) ⟨2953637, by rfl⟩ : syracuseStep 3938183 = 5907275) B5907275
theorem B5904413 : Blo 1748575 5904413 := bstep (se 3 (by rfl) ⟨1107077, by rfl⟩ : syracuseStep 5904413 = 2214155) B2214155
theorem B3938363 : Blo 1748575 3938363 := bstep (se 1 (by rfl) ⟨2953772, by rfl⟩ : syracuseStep 3938363 = 5907545) B5907545
theorem B8853623 : Blo 1748575 8853623 := bstep (se 1 (by rfl) ⟨6640217, by rfl⟩ : syracuseStep 8853623 = 13280435) B13280435
theorem B6641783 : Blo 1748575 6641783 := bstep (se 1 (by rfl) ⟨4981337, by rfl⟩ : syracuseStep 6641783 = 9962675) B9962675
theorem B3938489 : Blo 1748575 3938489 := bstep (se 2 (by rfl) ⟨1476933, by rfl⟩ : syracuseStep 3938489 = 2953867) B2953867
theorem B4430123 : Blo 1748575 4430123 := bstep (se 1 (by rfl) ⟨3322592, by rfl⟩ : syracuseStep 4430123 = 6645185) B6645185
theorem B8403335 : Blo 1748575 8403335 := bstep (se 1 (by rfl) ⟨6302501, by rfl⟩ : syracuseStep 8403335 = 12605003) B12605003
theorem B18921863 : Blo 1748575 18921863 := bstep (se 1 (by rfl) ⟨14191397, by rfl⟩ : syracuseStep 18921863 = 28382795) B28382795
theorem B7469597 : Blo 1748575 7469597 := bstep (se 3 (by rfl) ⟨1400549, by rfl⟩ : syracuseStep 7469597 = 2801099) B2801099
theorem B80771651 : Blo 1748575 80771651 := bstep (se 1 (by rfl) ⟨60578738, by rfl⟩ : syracuseStep 80771651 = 121157477) B121157477
theorem B37837493 : Blo 1748575 37837493 := bstep (se 5 (by rfl) ⟨1773632, by rfl⟩ : syracuseStep 37837493 = 3547265) B3547265
theorem B11213569 : Blo 1748575 11213569 := bstep (se 2 (by rfl) ⟨4205088, by rfl⟩ : syracuseStep 11213569 = 8410177) B8410177
theorem B4979515 : Blo 1748575 4979515 := bstep (se 1 (by rfl) ⟨3734636, by rfl⟩ : syracuseStep 4979515 = 7469273) B7469273
theorem B13130585 : Blo 1748575 13130585 := bstep (se 2 (by rfl) ⟨4923969, by rfl⟩ : syracuseStep 13130585 = 9847939) B9847939
theorem B8403857 : Blo 1748575 8403857 := bstep (se 2 (by rfl) ⟨3151446, by rfl⟩ : syracuseStep 8403857 = 6302893) B6302893
theorem B420363269 : Blo 1748575 420363269 := bstep (se 4 (by rfl) ⟨39409056, by rfl⟩ : syracuseStep 420363269 = 78818113) B78818113
theorem B9960509 : Blo 1748575 9960509 := bstep (se 3 (by rfl) ⟨1867595, by rfl⟩ : syracuseStep 9960509 = 3735191) B3735191
theorem B8854595 : Blo 1748575 8854595 := bstep (se 1 (by rfl) ⟨6640946, by rfl⟩ : syracuseStep 8854595 = 13281893) B13281893
theorem B6642755 : Blo 1748575 6642755 := bstep (se 1 (by rfl) ⟨4982066, by rfl⟩ : syracuseStep 6642755 = 9964133) B9964133
theorem B4430963 : Blo 1748575 4430963 := bstep (se 1 (by rfl) ⟨3323222, by rfl⟩ : syracuseStep 4430963 = 6646445) B6646445
theorem B4430983 : Blo 1748575 4430983 := bstep (se 1 (by rfl) ⟨3323237, by rfl⟩ : syracuseStep 4430983 = 6646475) B6646475
theorem B8854919 : Blo 1748575 8854919 := bstep (se 1 (by rfl) ⟨6641189, by rfl⟩ : syracuseStep 8854919 = 13282379) B13282379
theorem B5905817 : Blo 1748575 5905817 := bstep (se 2 (by rfl) ⟨2214681, by rfl⟩ : syracuseStep 5905817 = 4429363) B4429363
theorem B1867271 : Blo 1748575 1867271 := bstep (se 1 (by rfl) ⟨1400453, by rfl⟩ : syracuseStep 1867271 = 2800907) B2800907
theorem B13278977 : Blo 1748575 13278977 := bstep (se 2 (by rfl) ⟨4979616, by rfl⟩ : syracuseStep 13278977 = 9959233) B9959233
theorem B9961217 : Blo 1748575 9961217 := bstep (se 2 (by rfl) ⟨3735456, by rfl⟩ : syracuseStep 9961217 = 7470913) B7470913
theorem B44850995 : Blo 1748575 44850995 := bstep (se 1 (by rfl) ⟨33638246, by rfl⟩ : syracuseStep 44850995 = 67276493) B67276493
theorem B4980665 : Blo 1748575 4980665 := bstep (se 2 (by rfl) ⟨1867749, by rfl⟩ : syracuseStep 4980665 = 3735499) B3735499
theorem B8855567 : Blo 1748575 8855567 := bstep (se 1 (by rfl) ⟨6641675, by rfl⟩ : syracuseStep 8855567 = 13283351) B13283351
theorem B6643727 : Blo 1748575 6643727 := bstep (se 1 (by rfl) ⟨4982795, by rfl⟩ : syracuseStep 6643727 = 9965591) B9965591
theorem B4981121 : Blo 1748575 4981121 := bstep (se 2 (by rfl) ⟨1867920, by rfl⟩ : syracuseStep 4981121 = 3735841) B3735841
theorem B3547655 : Blo 1748575 3547655 := bstep (se 1 (by rfl) ⟨2660741, by rfl⟩ : syracuseStep 3547655 = 5321483) B5321483
theorem B2490959 : Blo 1748575 2490959 := bstep (se 1 (by rfl) ⟨1868219, by rfl⟩ : syracuseStep 2490959 = 3736439) B3736439
theorem B6390407 : Blo 1748575 6390407 := bstep (se 1 (by rfl) ⟨4792805, by rfl⟩ : syracuseStep 6390407 = 9585611) B9585611
theorem B12616393 : Blo 1748575 12616393 := bstep (se 2 (by rfl) ⟨4731147, by rfl⟩ : syracuseStep 12616393 = 9462295) B9462295
theorem B4981463 : Blo 1748575 4981463 := bstep (se 1 (by rfl) ⟨3736097, by rfl⟩ : syracuseStep 4981463 = 7472195) B7472195
theorem B15967151 : Blo 1748575 15967151 := bstep (se 1 (by rfl) ⟨11975363, by rfl⟩ : syracuseStep 15967151 = 23950727) B23950727
theorem B9962423 : Blo 1748575 9962423 := bstep (se 1 (by rfl) ⟨7471817, by rfl⟩ : syracuseStep 9962423 = 14943635) B14943635
theorem B5907383 : Blo 1748575 5907383 := bstep (se 1 (by rfl) ⟨4430537, by rfl⟩ : syracuseStep 5907383 = 8861075) B8861075
theorem B14951425 : Blo 1748575 14951425 := bstep (se 2 (by rfl) ⟨5606784, by rfl⟩ : syracuseStep 14951425 = 11213569) B11213569
theorem B3195911 : Blo 1748575 3195911 := bstep (se 1 (by rfl) ⟨2396933, by rfl⟩ : syracuseStep 3195911 = 4793867) B4793867
theorem B6309017 : Blo 1748575 6309017 := bstep (se 2 (by rfl) ⟨2365881, by rfl⟩ : syracuseStep 6309017 = 4731763) B4731763
theorem B25560265 : Blo 1748575 25560265 := bstep (se 2 (by rfl) ⟨9585099, by rfl⟩ : syracuseStep 25560265 = 19170199) B19170199
theorem B5907977 : Blo 1748575 5907977 := bstep (se 2 (by rfl) ⟨2215491, by rfl⟩ : syracuseStep 5907977 = 4430983) B4430983
theorem B5604889 : Blo 1748575 5604889 := bstep (se 2 (by rfl) ⟨2101833, by rfl⟩ : syracuseStep 5604889 = 4203667) B4203667
theorem B2950735 : Blo 1748575 2950735 := bstep (se 1 (by rfl) ⟨2213051, by rfl⟩ : syracuseStep 2950735 = 4426103) B4426103
theorem B2623055 : Blo 1748575 2623055 := bstep (se 1 (by rfl) ⟨1967291, by rfl⟩ : syracuseStep 2623055 = 3934583) B3934583
theorem B2623175 : Blo 1748575 2623175 := bstep (se 1 (by rfl) ⟨1967381, by rfl⟩ : syracuseStep 2623175 = 3934763) B3934763
theorem B53847767 : Blo 1748575 53847767 := bstep (se 1 (by rfl) ⟨40385825, by rfl⟩ : syracuseStep 53847767 = 80771651) B80771651
theorem B25224995 : Blo 1748575 25224995 := bstep (se 1 (by rfl) ⟨18918746, by rfl⟩ : syracuseStep 25224995 = 37837493) B37837493
theorem B2950985 : Blo 1748575 2950985 := bstep (se 2 (by rfl) ⟨1106619, by rfl⟩ : syracuseStep 2950985 = 2213239) B2213239
theorem B2623337 : Blo 1748575 2623337 := bstep (se 2 (by rfl) ⟨983751, by rfl⟩ : syracuseStep 2623337 = 1967503) B1967503
theorem B9963425 : Blo 1748575 9963425 := bstep (se 2 (by rfl) ⟨3736284, by rfl⟩ : syracuseStep 9963425 = 7472569) B7472569
theorem B2623415 : Blo 1748575 2623415 := bstep (se 1 (by rfl) ⟨1967561, by rfl⟩ : syracuseStep 2623415 = 3935123) B3935123
theorem B2623451 : Blo 1748575 2623451 := bstep (se 1 (by rfl) ⟨1967588, by rfl⟩ : syracuseStep 2623451 = 3935177) B3935177
theorem B2803675 : Blo 1748575 2803675 := bstep (se 1 (by rfl) ⟨2102756, by rfl⟩ : syracuseStep 2803675 = 4205513) B4205513
theorem B280242179 : Blo 1748575 280242179 := bstep (se 1 (by rfl) ⟨210181634, by rfl⟩ : syracuseStep 280242179 = 420363269) B420363269
theorem B3197051 : Blo 1748575 3197051 := bstep (se 1 (by rfl) ⟨2397788, by rfl⟩ : syracuseStep 3197051 = 4795577) B4795577
theorem B2951417 : Blo 1748575 2951417 := bstep (se 2 (by rfl) ⟨1106781, by rfl⟩ : syracuseStep 2951417 = 2213563) B2213563
theorem B9963881 : Blo 1748575 9963881 := bstep (se 2 (by rfl) ⟨3736455, by rfl⟩ : syracuseStep 9963881 = 7472911) B7472911
theorem B8980865 : Blo 1748575 8980865 := bstep (se 2 (by rfl) ⟨3367824, by rfl⟩ : syracuseStep 8980865 = 6735649) B6735649
theorem B2951599 : Blo 1748575 2951599 := bstep (se 1 (by rfl) ⟨2213699, by rfl⟩ : syracuseStep 2951599 = 4427399) B4427399
theorem B2623919 : Blo 1748575 2623919 := bstep (se 1 (by rfl) ⟨1967939, by rfl⟩ : syracuseStep 2623919 = 3935879) B3935879
theorem B105040313 : Blo 1748575 105040313 := bstep (se 2 (by rfl) ⟨39390117, by rfl⟩ : syracuseStep 105040313 = 78780235) B78780235
theorem B2951687 : Blo 1748575 2951687 := bstep (se 1 (by rfl) ⟨2213765, by rfl⟩ : syracuseStep 2951687 = 4427531) B4427531
theorem B2624009 : Blo 1748575 2624009 := bstep (se 2 (by rfl) ⟨984003, by rfl⟩ : syracuseStep 2624009 = 1968007) B1968007
theorem B4426265 : Blo 1748575 4426265 := bstep (se 2 (by rfl) ⟨1659849, by rfl⟩ : syracuseStep 4426265 = 3319699) B3319699
theorem B2624039 : Blo 1748575 2624039 := bstep (se 1 (by rfl) ⟨1968029, by rfl⟩ : syracuseStep 2624039 = 3936059) B3936059
theorem B2214479 : Blo 1748575 2214479 := bstep (se 1 (by rfl) ⟨1660859, by rfl⟩ : syracuseStep 2214479 = 3321719) B3321719
theorem B3934817 : Blo 1748575 3934817 := bstep (se 2 (by rfl) ⟨1475556, by rfl⟩ : syracuseStep 3934817 = 2951113) B2951113
theorem B3320443 : Blo 1748575 3320443 := bstep (se 1 (by rfl) ⟨2490332, by rfl⟩ : syracuseStep 3320443 = 4980665) B4980665
theorem B2624123 : Blo 1748575 2624123 := bstep (se 1 (by rfl) ⟨1968092, by rfl⟩ : syracuseStep 2624123 = 3936185) B3936185
theorem B1968763 : Blo 1748575 1968763 := bstep (se 1 (by rfl) ⟨1476572, by rfl⟩ : syracuseStep 1968763 = 2953145) B2953145
theorem B9456263 : Blo 1748575 9456263 := bstep (se 1 (by rfl) ⟨7092197, by rfl⟩ : syracuseStep 9456263 = 14184395) B14184395
theorem B7473799 : Blo 1748575 7473799 := bstep (se 1 (by rfl) ⟨5605349, by rfl⟩ : syracuseStep 7473799 = 11210699) B11210699
theorem B8858321 : Blo 1748575 8858321 := bstep (se 2 (by rfl) ⟨3321870, by rfl⟩ : syracuseStep 8858321 = 6643741) B6643741
theorem B2624249 : Blo 1748575 2624249 := bstep (se 2 (by rfl) ⟨984093, by rfl⟩ : syracuseStep 2624249 = 1968187) B1968187
theorem B48515915 : Blo 1748575 48515915 := bstep (se 1 (by rfl) ⟨36386936, by rfl⟩ : syracuseStep 48515915 = 72773873) B72773873
theorem B3320671 : Blo 1748575 3320671 := bstep (se 1 (by rfl) ⟨2490503, by rfl⟩ : syracuseStep 3320671 = 4981007) B4981007
theorem B2952031 : Blo 1748575 2952031 := bstep (se 1 (by rfl) ⟨2214023, by rfl⟩ : syracuseStep 2952031 = 4428047) B4428047
theorem B2624351 : Blo 1748575 2624351 := bstep (se 1 (by rfl) ⟨1968263, by rfl⟩ : syracuseStep 2624351 = 3936527) B3936527
theorem B2624363 : Blo 1748575 2624363 := bstep (se 1 (by rfl) ⟨1968272, by rfl⟩ : syracuseStep 2624363 = 3936545) B3936545
theorem B9718703 : Blo 1748575 9718703 := bstep (se 1 (by rfl) ⟨7289027, by rfl⟩ : syracuseStep 9718703 = 14578055) B14578055
theorem B3935159 : Blo 1748575 3935159 := bstep (se 1 (by rfl) ⟨2951369, by rfl⟩ : syracuseStep 3935159 = 5902739) B5902739
theorem B2952119 : Blo 1748575 2952119 := bstep (se 1 (by rfl) ⟨2214089, by rfl⟩ : syracuseStep 2952119 = 4428179) B4428179
theorem B44837873 : Blo 1748575 44837873 := bstep (se 2 (by rfl) ⟨16814202, by rfl⟩ : syracuseStep 44837873 = 33628405) B33628405
theorem B4426771 : Blo 1748575 4426771 := bstep (se 1 (by rfl) ⟨3320078, by rfl⟩ : syracuseStep 4426771 = 6640157) B6640157
theorem B90917963 : Blo 1748575 90917963 := bstep (se 1 (by rfl) ⟨68188472, by rfl⟩ : syracuseStep 90917963 = 136376945) B136376945
theorem B2624591 : Blo 1748575 2624591 := bstep (se 1 (by rfl) ⟨1968443, by rfl⟩ : syracuseStep 2624591 = 3936887) B3936887
theorem B1969231 : Blo 1748575 1969231 := bstep (se 1 (by rfl) ⟨1476923, by rfl⟩ : syracuseStep 1969231 = 2953847) B2953847
theorem B3320929 : Blo 1748575 3320929 := bstep (se 2 (by rfl) ⟨1245348, by rfl⟩ : syracuseStep 3320929 = 2490697) B2490697
theorem B2624711 : Blo 1748575 2624711 := bstep (se 1 (by rfl) ⟨1968533, by rfl⟩ : syracuseStep 2624711 = 3937067) B3937067
theorem B22727927 : Blo 1748575 22727927 := bstep (se 1 (by rfl) ⟨17045945, by rfl⟩ : syracuseStep 22727927 = 34091891) B34091891
theorem B2624873 : Blo 1748575 2624873 := bstep (se 2 (by rfl) ⟨984327, by rfl⟩ : syracuseStep 2624873 = 1968655) B1968655
theorem B10235261 : Blo 1748575 10235261 := bstep (se 3 (by rfl) ⟨1919111, by rfl⟩ : syracuseStep 10235261 = 3838223) B3838223
theorem B3321263 : Blo 1748575 3321263 := bstep (se 1 (by rfl) ⟨2490947, by rfl⟩ : syracuseStep 3321263 = 4981895) B4981895
theorem B2624951 : Blo 1748575 2624951 := bstep (se 1 (by rfl) ⟨1968713, by rfl⟩ : syracuseStep 2624951 = 3937427) B3937427
theorem B2624987 : Blo 1748575 2624987 := bstep (se 1 (by rfl) ⟨1968740, by rfl⟩ : syracuseStep 2624987 = 3937481) B3937481
theorem B3935753 : Blo 1748575 3935753 := bstep (se 2 (by rfl) ⟨1475907, by rfl⟩ : syracuseStep 3935753 = 2951815) B2951815
theorem B2952713 : Blo 1748575 2952713 := bstep (se 2 (by rfl) ⟨1107267, by rfl⟩ : syracuseStep 2952713 = 2214535) B2214535
theorem B4206089 : Blo 1748575 4206089 := bstep (se 2 (by rfl) ⟨1577283, by rfl⟩ : syracuseStep 4206089 = 3154567) B3154567
theorem B1748575 : Blo 1748575 1748575 := bstep (se 1 (by rfl) ⟨1311431, by rfl⟩ : syracuseStep 1748575 = 2622863) B2622863
theorem B1748603 : Blo 1748575 1748603 := bstep (se 1 (by rfl) ⟨1311452, by rfl⟩ : syracuseStep 1748603 = 2622905) B2622905
theorem B2952875 : Blo 1748575 2952875 := bstep (se 1 (by rfl) ⟨2214656, by rfl⟩ : syracuseStep 2952875 = 4429313) B4429313
theorem B1748655 : Blo 1748575 1748655 := bstep (se 1 (by rfl) ⟨1311491, by rfl⟩ : syracuseStep 1748655 = 2622983) B2622983
theorem B1748679 : Blo 1748575 1748679 := bstep (se 1 (by rfl) ⟨1311509, by rfl⟩ : syracuseStep 1748679 = 2623019) B2623019
theorem B1748699 : Blo 1748575 1748699 := bstep (se 1 (by rfl) ⟨1311524, by rfl⟩ : syracuseStep 1748699 = 2623049) B2623049
theorem B6639353 : Blo 1748575 6639353 := bstep (se 2 (by rfl) ⟨2489757, by rfl⟩ : syracuseStep 6639353 = 4979515) B4979515
theorem B12611321 : Blo 1748575 12611321 := bstep (se 2 (by rfl) ⟨4729245, by rfl⟩ : syracuseStep 12611321 = 9458491) B9458491
theorem B1748775 : Blo 1748575 1748775 := bstep (se 1 (by rfl) ⟨1311581, by rfl⟩ : syracuseStep 1748775 = 2623163) B2623163
theorem B1748815 : Blo 1748575 1748815 := bstep (se 1 (by rfl) ⟨1311611, by rfl⟩ : syracuseStep 1748815 = 2623223) B2623223
theorem B1748831 : Blo 1748575 1748831 := bstep (se 1 (by rfl) ⟨1311623, by rfl⟩ : syracuseStep 1748831 = 2623247) B2623247
theorem B3936095 : Blo 1748575 3936095 := bstep (se 1 (by rfl) ⟨2952071, by rfl⟩ : syracuseStep 3936095 = 5904143) B5904143
theorem B5902199 : Blo 1748575 5902199 := bstep (se 1 (by rfl) ⟨4426649, by rfl⟩ : syracuseStep 5902199 = 8853299) B8853299
theorem B1748859 : Blo 1748575 1748859 := bstep (se 1 (by rfl) ⟨1311644, by rfl⟩ : syracuseStep 1748859 = 2623289) B2623289
theorem B22409095 : Blo 1748575 22409095 := bstep (se 1 (by rfl) ⟨16806821, by rfl⟩ : syracuseStep 22409095 = 33613643) B33613643
theorem B1748911 : Blo 1748575 1748911 := bstep (se 1 (by rfl) ⟨1311683, by rfl⟩ : syracuseStep 1748911 = 2623367) B2623367
theorem B2625455 : Blo 1748575 2625455 := bstep (se 1 (by rfl) ⟨1969091, by rfl⟩ : syracuseStep 2625455 = 3938183) B3938183
theorem B1748935 : Blo 1748575 1748935 := bstep (se 1 (by rfl) ⟨1311701, by rfl⟩ : syracuseStep 1748935 = 2623403) B2623403
theorem B1748955 : Blo 1748575 1748955 := bstep (se 1 (by rfl) ⟨1311716, by rfl⟩ : syracuseStep 1748955 = 2623433) B2623433
theorem B2625545 : Blo 1748575 2625545 := bstep (se 2 (by rfl) ⟨984579, by rfl⟩ : syracuseStep 2625545 = 1969159) B1969159
theorem B3936275 : Blo 1748575 3936275 := bstep (se 1 (by rfl) ⟨2952206, by rfl⟩ : syracuseStep 3936275 = 5904413) B5904413
theorem B4730899 : Blo 1748575 4730899 := bstep (se 1 (by rfl) ⟨3548174, by rfl⟩ : syracuseStep 4730899 = 7096349) B7096349
theorem B1749031 : Blo 1748575 1749031 := bstep (se 1 (by rfl) ⟨1311773, by rfl⟩ : syracuseStep 1749031 = 2623547) B2623547
theorem B2625575 : Blo 1748575 2625575 := bstep (se 1 (by rfl) ⟨1969181, by rfl⟩ : syracuseStep 2625575 = 3938363) B3938363
theorem B2953273 : Blo 1748575 2953273 := bstep (se 2 (by rfl) ⟨1107477, by rfl⟩ : syracuseStep 2953273 = 2214955) B2214955
theorem B5902415 : Blo 1748575 5902415 := bstep (se 1 (by rfl) ⟨4426811, by rfl⟩ : syracuseStep 5902415 = 8853623) B8853623
theorem B1749071 : Blo 1748575 1749071 := bstep (se 1 (by rfl) ⟨1311803, by rfl⟩ : syracuseStep 1749071 = 2623607) B2623607
theorem B4427855 : Blo 1748575 4427855 := bstep (se 1 (by rfl) ⟨3320891, by rfl⟩ : syracuseStep 4427855 = 6641783) B6641783
theorem B1749087 : Blo 1748575 1749087 := bstep (se 1 (by rfl) ⟨1311815, by rfl⟩ : syracuseStep 1749087 = 2623631) B2623631
theorem B1749115 : Blo 1748575 1749115 := bstep (se 1 (by rfl) ⟨1311836, by rfl⟩ : syracuseStep 1749115 = 2623673) B2623673
theorem B2625659 : Blo 1748575 2625659 := bstep (se 1 (by rfl) ⟨1969244, by rfl⟩ : syracuseStep 2625659 = 3938489) B3938489
theorem B1749167 : Blo 1748575 1749167 := bstep (se 1 (by rfl) ⟨1311875, by rfl⟩ : syracuseStep 1749167 = 2623751) B2623751
theorem B1749191 : Blo 1748575 1749191 := bstep (se 1 (by rfl) ⟨1311893, by rfl⟩ : syracuseStep 1749191 = 2623787) B2623787
theorem B2953415 : Blo 1748575 2953415 := bstep (se 1 (by rfl) ⟨2215061, by rfl⟩ : syracuseStep 2953415 = 4430123) B4430123
theorem B1749211 : Blo 1748575 1749211 := bstep (se 1 (by rfl) ⟨1311908, by rfl⟩ : syracuseStep 1749211 = 2623817) B2623817
theorem B2625785 : Blo 1748575 2625785 := bstep (se 2 (by rfl) ⟨984669, by rfl⟩ : syracuseStep 2625785 = 1969339) B1969339
theorem B1749287 : Blo 1748575 1749287 := bstep (se 1 (by rfl) ⟨1311965, by rfl⟩ : syracuseStep 1749287 = 2623931) B2623931
theorem B1749327 : Blo 1748575 1749327 := bstep (se 1 (by rfl) ⟨1311995, by rfl⟩ : syracuseStep 1749327 = 2623991) B2623991
theorem B1749343 : Blo 1748575 1749343 := bstep (se 1 (by rfl) ⟨1312007, by rfl⟩ : syracuseStep 1749343 = 2624015) B2624015
theorem B3936617 : Blo 1748575 3936617 := bstep (se 2 (by rfl) ⟨1476231, by rfl⟩ : syracuseStep 3936617 = 2952463) B2952463
theorem B7475561 : Blo 1748575 7475561 := bstep (se 2 (by rfl) ⟨2803335, by rfl⟩ : syracuseStep 7475561 = 5606671) B5606671
theorem B2953577 : Blo 1748575 2953577 := bstep (se 2 (by rfl) ⟨1107591, by rfl⟩ : syracuseStep 2953577 = 2215183) B2215183
theorem B1749371 : Blo 1748575 1749371 := bstep (se 1 (by rfl) ⟨1312028, by rfl⟩ : syracuseStep 1749371 = 2624057) B2624057
theorem B1749423 : Blo 1748575 1749423 := bstep (se 1 (by rfl) ⟨1312067, by rfl⟩ : syracuseStep 1749423 = 2624135) B2624135
theorem B1749447 : Blo 1748575 1749447 := bstep (se 1 (by rfl) ⟨1312085, by rfl⟩ : syracuseStep 1749447 = 2624171) B2624171
theorem B5902793 : Blo 1748575 5902793 := bstep (se 2 (by rfl) ⟨2213547, by rfl⟩ : syracuseStep 5902793 = 4427095) B4427095
theorem B1749467 : Blo 1748575 1749467 := bstep (se 1 (by rfl) ⟨1312100, by rfl⟩ : syracuseStep 1749467 = 2624201) B2624201
theorem B3322387 : Blo 1748575 3322387 := bstep (se 1 (by rfl) ⟨2491790, by rfl⟩ : syracuseStep 3322387 = 4983581) B4983581
theorem B1749543 : Blo 1748575 1749543 := bstep (se 1 (by rfl) ⟨1312157, by rfl⟩ : syracuseStep 1749543 = 2624315) B2624315
theorem B8753723 : Blo 1748575 8753723 := bstep (se 1 (by rfl) ⟨6565292, by rfl⟩ : syracuseStep 8753723 = 13130585) B13130585
theorem B1749583 : Blo 1748575 1749583 := bstep (se 1 (by rfl) ⟨1312187, by rfl⟩ : syracuseStep 1749583 = 2624375) B2624375
theorem B1749599 : Blo 1748575 1749599 := bstep (se 1 (by rfl) ⟨1312199, by rfl⟩ : syracuseStep 1749599 = 2624399) B2624399
theorem B22737509 : Blo 1748575 22737509 := bstep (se 4 (by rfl) ⟨2131641, by rfl⟩ : syracuseStep 22737509 = 4263283) B4263283
theorem B1749627 : Blo 1748575 1749627 := bstep (se 1 (by rfl) ⟨1312220, by rfl⟩ : syracuseStep 1749627 = 2624441) B2624441
theorem B1749679 : Blo 1748575 1749679 := bstep (se 1 (by rfl) ⟨1312259, by rfl⟩ : syracuseStep 1749679 = 2624519) B2624519
theorem B1749703 : Blo 1748575 1749703 := bstep (se 1 (by rfl) ⟨1312277, by rfl⟩ : syracuseStep 1749703 = 2624555) B2624555
theorem B6640339 : Blo 1748575 6640339 := bstep (se 1 (by rfl) ⟨4980254, by rfl⟩ : syracuseStep 6640339 = 9960509) B9960509
theorem B5903063 : Blo 1748575 5903063 := bstep (se 1 (by rfl) ⟨4427297, by rfl⟩ : syracuseStep 5903063 = 8854595) B8854595
theorem B4428503 : Blo 1748575 4428503 := bstep (se 1 (by rfl) ⟨3321377, by rfl⟩ : syracuseStep 4428503 = 6642755) B6642755
theorem B1749723 : Blo 1748575 1749723 := bstep (se 1 (by rfl) ⟨1312292, by rfl⟩ : syracuseStep 1749723 = 2624585) B2624585
theorem B3322615 : Blo 1748575 3322615 := bstep (se 1 (by rfl) ⟨2491961, by rfl⟩ : syracuseStep 3322615 = 4983923) B4983923
theorem B2953975 : Blo 1748575 2953975 := bstep (se 1 (by rfl) ⟨2215481, by rfl⟩ : syracuseStep 2953975 = 4430963) B4430963
theorem B10646275 : Blo 1748575 10646275 := bstep (se 1 (by rfl) ⟨7984706, by rfl⟩ : syracuseStep 10646275 = 15969413) B15969413
theorem B1749799 : Blo 1748575 1749799 := bstep (se 1 (by rfl) ⟨1312349, by rfl⟩ : syracuseStep 1749799 = 2624699) B2624699
theorem B1749839 : Blo 1748575 1749839 := bstep (se 1 (by rfl) ⟨1312379, by rfl⟩ : syracuseStep 1749839 = 2624759) B2624759
theorem B1749855 : Blo 1748575 1749855 := bstep (se 1 (by rfl) ⟨1312391, by rfl⟩ : syracuseStep 1749855 = 2624783) B2624783
theorem B1749883 : Blo 1748575 1749883 := bstep (se 1 (by rfl) ⟨1312412, by rfl⟩ : syracuseStep 1749883 = 2624825) B2624825
theorem B5903279 : Blo 1748575 5903279 := bstep (se 1 (by rfl) ⟨4427459, by rfl⟩ : syracuseStep 5903279 = 8854919) B8854919
theorem B1749935 : Blo 1748575 1749935 := bstep (se 1 (by rfl) ⟨1312451, by rfl⟩ : syracuseStep 1749935 = 2624903) B2624903
theorem B3937211 : Blo 1748575 3937211 := bstep (se 1 (by rfl) ⟨2952908, by rfl⟩ : syracuseStep 3937211 = 5905817) B5905817
theorem B1749959 : Blo 1748575 1749959 := bstep (se 1 (by rfl) ⟨1312469, by rfl⟩ : syracuseStep 1749959 = 2624939) B2624939
theorem B1749979 : Blo 1748575 1749979 := bstep (se 1 (by rfl) ⟨1312484, by rfl⟩ : syracuseStep 1749979 = 2624969) B2624969
theorem B1750055 : Blo 1748575 1750055 := bstep (se 1 (by rfl) ⟨1312541, by rfl⟩ : syracuseStep 1750055 = 2625083) B2625083
theorem B3322919 : Blo 1748575 3322919 := bstep (se 1 (by rfl) ⟨2492189, by rfl⟩ : syracuseStep 3322919 = 4984379) B4984379
theorem B4428857 : Blo 1748575 4428857 := bstep (se 2 (by rfl) ⟨1660821, by rfl⟩ : syracuseStep 4428857 = 3321643) B3321643
theorem B3937337 : Blo 1748575 3937337 := bstep (se 2 (by rfl) ⟨1476501, by rfl⟩ : syracuseStep 3937337 = 2953003) B2953003
theorem B1750095 : Blo 1748575 1750095 := bstep (se 1 (by rfl) ⟨1312571, by rfl⟩ : syracuseStep 1750095 = 2625143) B2625143
theorem B8860751 : Blo 1748575 8860751 := bstep (se 1 (by rfl) ⟨6645563, by rfl⟩ : syracuseStep 8860751 = 13291127) B13291127
theorem B1750111 : Blo 1748575 1750111 := bstep (se 1 (by rfl) ⟨1312583, by rfl⟩ : syracuseStep 1750111 = 2625167) B2625167
theorem B1750139 : Blo 1748575 1750139 := bstep (se 1 (by rfl) ⟨1312604, by rfl⟩ : syracuseStep 1750139 = 2625209) B2625209
theorem B11211929 : Blo 1748575 11211929 := bstep (se 2 (by rfl) ⟨4204473, by rfl⟩ : syracuseStep 11211929 = 8408947) B8408947
theorem B8852651 : Blo 1748575 8852651 := bstep (se 1 (by rfl) ⟨6639488, by rfl⟩ : syracuseStep 8852651 = 13278977) B13278977
theorem B6640811 : Blo 1748575 6640811 := bstep (se 1 (by rfl) ⟨4980608, by rfl⟩ : syracuseStep 6640811 = 9961217) B9961217
theorem B1750191 : Blo 1748575 1750191 := bstep (se 1 (by rfl) ⟨1312643, by rfl⟩ : syracuseStep 1750191 = 2625287) B2625287
theorem B1750215 : Blo 1748575 1750215 := bstep (se 1 (by rfl) ⟨1312661, by rfl⟩ : syracuseStep 1750215 = 2625323) B2625323
theorem B1750235 : Blo 1748575 1750235 := bstep (se 1 (by rfl) ⟨1312676, by rfl⟩ : syracuseStep 1750235 = 2625353) B2625353
theorem B1750311 : Blo 1748575 1750311 := bstep (se 1 (by rfl) ⟨1312733, by rfl⟩ : syracuseStep 1750311 = 2625467) B2625467
theorem B1750351 : Blo 1748575 1750351 := bstep (se 1 (by rfl) ⟨1312763, by rfl⟩ : syracuseStep 1750351 = 2625527) B2625527
theorem B1750367 : Blo 1748575 1750367 := bstep (se 1 (by rfl) ⟨1312775, by rfl⟩ : syracuseStep 1750367 = 2625551) B2625551
theorem B20477299 : Blo 1748575 20477299 := bstep (se 1 (by rfl) ⟨15357974, by rfl⟩ : syracuseStep 20477299 = 30715949) B30715949
theorem B1750395 : Blo 1748575 1750395 := bstep (se 1 (by rfl) ⟨1312796, by rfl⟩ : syracuseStep 1750395 = 2625593) B2625593
theorem B3937679 : Blo 1748575 3937679 := bstep (se 1 (by rfl) ⟨2953259, by rfl⟩ : syracuseStep 3937679 = 5906519) B5906519
theorem B1750447 : Blo 1748575 1750447 := bstep (se 1 (by rfl) ⟨1312835, by rfl⟩ : syracuseStep 1750447 = 2625671) B2625671
theorem B1750471 : Blo 1748575 1750471 := bstep (se 1 (by rfl) ⟨1312853, by rfl⟩ : syracuseStep 1750471 = 2625707) B2625707
theorem B13284809 : Blo 1748575 13284809 := bstep (se 2 (by rfl) ⟨4981803, by rfl⟩ : syracuseStep 13284809 = 9963607) B9963607
theorem B9967049 : Blo 1748575 9967049 := bstep (se 2 (by rfl) ⟨3737643, by rfl⟩ : syracuseStep 9967049 = 7475287) B7475287
theorem B1750491 : Blo 1748575 1750491 := bstep (se 1 (by rfl) ⟨1312868, by rfl⟩ : syracuseStep 1750491 = 2625737) B2625737
theorem B9582119 : Blo 1748575 9582119 := bstep (se 1 (by rfl) ⟨7186589, by rfl⟩ : syracuseStep 9582119 = 14373179) B14373179
theorem B1750567 : Blo 1748575 1750567 := bstep (se 1 (by rfl) ⟨1312925, by rfl⟩ : syracuseStep 1750567 = 2625851) B2625851
theorem B9959051 : Blo 1748575 9959051 := bstep (se 1 (by rfl) ⟨7469288, by rfl⟩ : syracuseStep 9959051 = 14938577) B14938577
theorem B8853137 : Blo 1748575 8853137 := bstep (se 2 (by rfl) ⟨3319926, by rfl⟩ : syracuseStep 8853137 = 6639853) B6639853
theorem B11204243 : Blo 1748575 11204243 := bstep (se 1 (by rfl) ⟨8403182, by rfl⟩ : syracuseStep 11204243 = 16806365) B16806365
theorem B3938003 : Blo 1748575 3938003 := bstep (se 1 (by rfl) ⟨2953502, by rfl⟩ : syracuseStep 3938003 = 5907005) B5907005
theorem B8861399 : Blo 1748575 8861399 := bstep (se 1 (by rfl) ⟨6646049, by rfl⟩ : syracuseStep 8861399 = 13292099) B13292099
theorem B13473697 : Blo 1748575 13473697 := bstep (se 2 (by rfl) ⟨5052636, by rfl⟩ : syracuseStep 13473697 = 10105273) B10105273
theorem B3151799 : Blo 1748575 3151799 := bstep (se 1 (by rfl) ⟨2363849, by rfl⟩ : syracuseStep 3151799 = 4727699) B4727699
theorem B14194769 : Blo 1748575 14194769 := bstep (se 2 (by rfl) ⟨5323038, by rfl⟩ : syracuseStep 14194769 = 10646077) B10646077
theorem B181778519 : Blo 1748575 181778519 := bstep (se 1 (by rfl) ⟨136333889, by rfl⟩ : syracuseStep 181778519 = 272667779) B272667779
theorem B8411293 : Blo 1748575 8411293 := bstep (se 3 (by rfl) ⟨1577117, by rfl⟩ : syracuseStep 8411293 = 3154235) B3154235
theorem B3365215 : Blo 1748575 3365215 := bstep (se 1 (by rfl) ⟨2523911, by rfl⟩ : syracuseStep 3365215 = 5047823) B5047823
theorem B2660791 : Blo 1748575 2660791 := bstep (se 1 (by rfl) ⟨1995593, by rfl⟩ : syracuseStep 2660791 = 3991187) B3991187
theorem B131160689 : Blo 1748575 131160689 := bstep (se 2 (by rfl) ⟨49185258, by rfl⟩ : syracuseStep 131160689 = 98370517) B98370517
theorem B4979389 : Blo 1748575 4979389 := bstep (se 3 (by rfl) ⟨933635, by rfl⟩ : syracuseStep 4979389 = 1867271) B1867271
theorem B5602223 : Blo 1748575 5602223 := bstep (se 1 (by rfl) ⟨4201667, by rfl⟩ : syracuseStep 5602223 = 8403335) B8403335
theorem B12614575 : Blo 1748575 12614575 := bstep (se 1 (by rfl) ⟨9460931, by rfl⟩ : syracuseStep 12614575 = 18921863) B18921863
theorem B4979731 : Blo 1748575 4979731 := bstep (se 1 (by rfl) ⟨3734798, by rfl⟩ : syracuseStep 4979731 = 7469597) B7469597
theorem B6642769 : Blo 1748575 6642769 := bstep (se 2 (by rfl) ⟨2491038, by rfl⟩ : syracuseStep 6642769 = 4982077) B4982077
theorem B2841799 : Blo 1748575 2841799 := bstep (se 1 (by rfl) ⟨2131349, by rfl⟩ : syracuseStep 2841799 = 4262699) B4262699
theorem B5905655 : Blo 1748575 5905655 := bstep (se 1 (by rfl) ⟨4429241, by rfl⟩ : syracuseStep 5905655 = 8858483) B8858483
theorem B4431095 : Blo 1748575 4431095 := bstep (se 1 (by rfl) ⟨3323321, by rfl⟩ : syracuseStep 4431095 = 6646643) B6646643
theorem B5602571 : Blo 1748575 5602571 := bstep (se 1 (by rfl) ⟨4201928, by rfl⟩ : syracuseStep 5602571 = 8403857) B8403857
theorem B6643073 : Blo 1748575 6643073 := bstep (se 2 (by rfl) ⟨2491152, by rfl⟩ : syracuseStep 6643073 = 4982305) B4982305
theorem B3841499 : Blo 1748575 3841499 := bstep (se 1 (by rfl) ⟨2881124, by rfl⟩ : syracuseStep 3841499 = 5762249) B5762249
theorem B5905979 : Blo 1748575 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B23027287 : Blo 1748575 23027287 := bstep (se 1 (by rfl) ⟨17270465, by rfl⟩ : syracuseStep 23027287 = 34540931) B34540931
theorem B6307577 : Blo 1748575 6307577 := bstep (se 2 (by rfl) ⟨2365341, by rfl⟩ : syracuseStep 6307577 = 4730683) B4730683
theorem B6643529 : Blo 1748575 6643529 := bstep (se 2 (by rfl) ⟨2491323, by rfl⟩ : syracuseStep 6643529 = 4982647) B4982647
theorem B5906249 : Blo 1748575 5906249 := bstep (se 2 (by rfl) ⟨2214843, by rfl⟩ : syracuseStep 5906249 = 4429687) B4429687
theorem B8855405 : Blo 1748575 8855405 := bstep (se 3 (by rfl) ⟨1660388, by rfl⟩ : syracuseStep 8855405 = 3320777) B3320777
theorem B29900663 : Blo 1748575 29900663 := bstep (se 1 (by rfl) ⟨22425497, by rfl⟩ : syracuseStep 29900663 = 44850995) B44850995
theorem B9461623 : Blo 1748575 9461623 := bstep (se 1 (by rfl) ⟨7096217, by rfl⟩ : syracuseStep 9461623 = 14192435) B14192435
theorem B6307865 : Blo 1748575 6307865 := bstep (se 2 (by rfl) ⟨2365449, by rfl⟩ : syracuseStep 6307865 = 4730899) B4730899
theorem B11215057 : Blo 1748575 11215057 := bstep (se 2 (by rfl) ⟨4205646, by rfl⟩ : syracuseStep 11215057 = 8411293) B8411293
theorem B4260271 : Blo 1748575 4260271 := bstep (se 1 (by rfl) ⟨3195203, by rfl⟩ : syracuseStep 4260271 = 6390407) B6390407
theorem B3547721 : Blo 1748575 3547721 := bstep (se 2 (by rfl) ⟨1330395, by rfl⟩ : syracuseStep 3547721 = 2660791) B2660791
theorem B2130607 : Blo 1748575 2130607 := bstep (se 1 (by rfl) ⟨1597955, by rfl⟩ : syracuseStep 2130607 = 3195911) B3195911
theorem B5907167 : Blo 1748575 5907167 := bstep (se 1 (by rfl) ⟨4430375, by rfl⟩ : syracuseStep 5907167 = 8860751) B8860751
theorem B8856539 : Blo 1748575 8856539 := bstep (se 1 (by rfl) ⟨6642404, by rfl⟩ : syracuseStep 8856539 = 13284809) B13284809
theorem B6644699 : Blo 1748575 6644699 := bstep (se 1 (by rfl) ⟨4983524, by rfl⟩ : syracuseStep 6644699 = 9967049) B9967049
theorem B8856701 : Blo 1748575 8856701 := bstep (se 3 (by rfl) ⟨1660631, by rfl⟩ : syracuseStep 8856701 = 3321263) B3321263
theorem B35898511 : Blo 1748575 35898511 := bstep (se 1 (by rfl) ⟨26923883, by rfl⟩ : syracuseStep 35898511 = 53847767) B53847767
theorem B5907599 : Blo 1748575 5907599 := bstep (se 1 (by rfl) ⟨4430699, by rfl⟩ : syracuseStep 5907599 = 8861399) B8861399
theorem B1967323 : Blo 1748575 1967323 := bstep (se 1 (by rfl) ⟨1475492, by rfl⟩ : syracuseStep 1967323 = 2950985) B2950985
theorem B16819433 : Blo 1748575 16819433 := bstep (se 2 (by rfl) ⟨6307287, by rfl⟩ : syracuseStep 16819433 = 12614575) B12614575
theorem B186828119 : Blo 1748575 186828119 := bstep (se 1 (by rfl) ⟨140121089, by rfl⟩ : syracuseStep 186828119 = 280242179) B280242179
theorem B121185679 : Blo 1748575 121185679 := bstep (se 1 (by rfl) ⟨90889259, by rfl⟩ : syracuseStep 121185679 = 181778519) B181778519
theorem B2131367 : Blo 1748575 2131367 := bstep (se 1 (by rfl) ⟨1598525, by rfl⟩ : syracuseStep 2131367 = 3197051) B3197051
theorem B8857025 : Blo 1748575 8857025 := bstep (se 2 (by rfl) ⟨3321384, by rfl⟩ : syracuseStep 8857025 = 6642769) B6642769
theorem B1967611 : Blo 1748575 1967611 := bstep (se 1 (by rfl) ⟨1475708, by rfl⟩ : syracuseStep 1967611 = 2951417) B2951417
theorem B34080353 : Blo 1748575 34080353 := bstep (se 2 (by rfl) ⟨12780132, by rfl⟩ : syracuseStep 34080353 = 25560265) B25560265
theorem B70026875 : Blo 1748575 70026875 := bstep (se 1 (by rfl) ⟨52520156, by rfl⟩ : syracuseStep 70026875 = 105040313) B105040313
theorem B1967791 : Blo 1748575 1967791 := bstep (se 1 (by rfl) ⟨1475843, by rfl⟩ : syracuseStep 1967791 = 2951687) B2951687
theorem B2950843 : Blo 1748575 2950843 := bstep (se 1 (by rfl) ⟨2213132, by rfl⟩ : syracuseStep 2950843 = 4426265) B4426265
theorem B2623211 : Blo 1748575 2623211 := bstep (se 1 (by rfl) ⟨1967408, by rfl⟩ : syracuseStep 2623211 = 3934817) B3934817
theorem B32343943 : Blo 1748575 32343943 := bstep (se 1 (by rfl) ⟨24257957, by rfl⟩ : syracuseStep 32343943 = 48515915) B48515915
theorem B2623439 : Blo 1748575 2623439 := bstep (se 1 (by rfl) ⟨1967579, by rfl⟩ : syracuseStep 2623439 = 3935159) B3935159
theorem B1968079 : Blo 1748575 1968079 := bstep (se 1 (by rfl) ⟨1476059, by rfl⟩ : syracuseStep 1968079 = 2952119) B2952119
theorem B7473185 : Blo 1748575 7473185 := bstep (se 2 (by rfl) ⟨2802444, by rfl⟩ : syracuseStep 7473185 = 5604889) B5604889
theorem B3934313 : Blo 1748575 3934313 := bstep (se 2 (by rfl) ⟨1475367, by rfl⟩ : syracuseStep 3934313 = 2950735) B2950735
theorem B2623835 : Blo 1748575 2623835 := bstep (se 1 (by rfl) ⟨1967876, by rfl⟩ : syracuseStep 2623835 = 3935753) B3935753
theorem B1968475 : Blo 1748575 1968475 := bstep (se 1 (by rfl) ⟨1476356, by rfl⟩ : syracuseStep 1968475 = 2952713) B2952713
theorem B2804059 : Blo 1748575 2804059 := bstep (se 1 (by rfl) ⟨2103044, by rfl⟩ : syracuseStep 2804059 = 4206089) B4206089
theorem B1968583 : Blo 1748575 1968583 := bstep (se 1 (by rfl) ⟨1476437, by rfl⟩ : syracuseStep 1968583 = 2952875) B2952875
theorem B4426235 : Blo 1748575 4426235 := bstep (se 1 (by rfl) ⟨3319676, by rfl⟩ : syracuseStep 4426235 = 6639353) B6639353
theorem B8407547 : Blo 1748575 8407547 := bstep (se 1 (by rfl) ⟨6305660, by rfl⟩ : syracuseStep 8407547 = 12611321) B12611321
theorem B4205051 : Blo 1748575 4205051 := bstep (se 1 (by rfl) ⟨3153788, by rfl⟩ : syracuseStep 4205051 = 6307577) B6307577
theorem B29878793 : Blo 1748575 29878793 := bstep (se 2 (by rfl) ⟨11204547, by rfl⟩ : syracuseStep 29878793 = 22409095) B22409095
theorem B2624063 : Blo 1748575 2624063 := bstep (se 1 (by rfl) ⟨1968047, by rfl⟩ : syracuseStep 2624063 = 3936095) B3936095
theorem B3934799 : Blo 1748575 3934799 := bstep (se 1 (by rfl) ⟨2951099, by rfl⟩ : syracuseStep 3934799 = 5902199) B5902199
theorem B19933775 : Blo 1748575 19933775 := bstep (se 1 (by rfl) ⟨14950331, by rfl⟩ : syracuseStep 19933775 = 29900663) B29900663
theorem B3738233 : Blo 1748575 3738233 := bstep (se 2 (by rfl) ⟨1401837, by rfl⟩ : syracuseStep 3738233 = 2803675) B2803675
theorem B2624183 : Blo 1748575 2624183 := bstep (se 1 (by rfl) ⟨1968137, by rfl⟩ : syracuseStep 2624183 = 3936275) B3936275
theorem B3934943 : Blo 1748575 3934943 := bstep (se 1 (by rfl) ⟨2951207, by rfl⟩ : syracuseStep 3934943 = 5902415) B5902415
theorem B2951903 : Blo 1748575 2951903 := bstep (se 1 (by rfl) ⟨2213927, by rfl⟩ : syracuseStep 2951903 = 4427855) B4427855
theorem B1968943 : Blo 1748575 1968943 := bstep (se 1 (by rfl) ⟨1476707, by rfl⟩ : syracuseStep 1968943 = 2953415) B2953415
theorem B2624411 : Blo 1748575 2624411 := bstep (se 1 (by rfl) ⟨1968308, by rfl⟩ : syracuseStep 2624411 = 3936617) B3936617
theorem B4983707 : Blo 1748575 4983707 := bstep (se 1 (by rfl) ⟨3737780, by rfl⟩ : syracuseStep 4983707 = 7475561) B7475561
theorem B1969051 : Blo 1748575 1969051 := bstep (se 1 (by rfl) ⟨1476788, by rfl⟩ : syracuseStep 1969051 = 2953577) B2953577
theorem B3320747 : Blo 1748575 3320747 := bstep (se 1 (by rfl) ⟨2490560, by rfl⟩ : syracuseStep 3320747 = 4981121) B4981121
theorem B3935195 : Blo 1748575 3935195 := bstep (se 1 (by rfl) ⟨2951396, by rfl⟩ : syracuseStep 3935195 = 5902793) B5902793
theorem B5835815 : Blo 1748575 5835815 := bstep (se 1 (by rfl) ⟨4376861, by rfl⟩ : syracuseStep 5835815 = 8753723) B8753723
theorem B15158339 : Blo 1748575 15158339 := bstep (se 1 (by rfl) ⟨11368754, by rfl⟩ : syracuseStep 15158339 = 22737509) B22737509
theorem B3935375 : Blo 1748575 3935375 := bstep (se 1 (by rfl) ⟨2951531, by rfl⟩ : syracuseStep 3935375 = 5903063) B5903063
theorem B3320975 : Blo 1748575 3320975 := bstep (se 1 (by rfl) ⟨2490731, by rfl⟩ : syracuseStep 3320975 = 4981463) B4981463
theorem B2952335 : Blo 1748575 2952335 := bstep (se 1 (by rfl) ⟨2214251, by rfl⟩ : syracuseStep 2952335 = 4428503) B4428503
theorem B3935465 : Blo 1748575 3935465 := bstep (se 2 (by rfl) ⟨1475799, by rfl⟩ : syracuseStep 3935465 = 2951599) B2951599
theorem B3935519 : Blo 1748575 3935519 := bstep (se 1 (by rfl) ⟨2951639, by rfl⟩ : syracuseStep 3935519 = 5903279) B5903279
theorem B10644767 : Blo 1748575 10644767 := bstep (se 1 (by rfl) ⟨7983575, by rfl⟩ : syracuseStep 10644767 = 15967151) B15967151
theorem B2624807 : Blo 1748575 2624807 := bstep (se 1 (by rfl) ⟨1968605, by rfl⟩ : syracuseStep 2624807 = 3937211) B3937211
theorem B2215279 : Blo 1748575 2215279 := bstep (se 1 (by rfl) ⟨1661459, by rfl⟩ : syracuseStep 2215279 = 3322919) B3322919
theorem B2952571 : Blo 1748575 2952571 := bstep (se 1 (by rfl) ⟨2214428, by rfl⟩ : syracuseStep 2952571 = 4428857) B4428857
theorem B2624891 : Blo 1748575 2624891 := bstep (se 1 (by rfl) ⟨1968668, by rfl⟩ : syracuseStep 2624891 = 3937337) B3937337
theorem B7474619 : Blo 1748575 7474619 := bstep (se 1 (by rfl) ⟨5605964, by rfl⟩ : syracuseStep 7474619 = 11211929) B11211929
theorem B4206011 : Blo 1748575 4206011 := bstep (se 1 (by rfl) ⟨3154508, by rfl⟩ : syracuseStep 4206011 = 6309017) B6309017
theorem B5901767 : Blo 1748575 5901767 := bstep (se 1 (by rfl) ⟨4426325, by rfl⟩ : syracuseStep 5901767 = 8852651) B8852651
theorem B4427207 : Blo 1748575 4427207 := bstep (se 1 (by rfl) ⟨3320405, by rfl⟩ : syracuseStep 4427207 = 6640811) B6640811
theorem B4427257 : Blo 1748575 4427257 := bstep (se 2 (by rfl) ⟨1660221, by rfl⟩ : syracuseStep 4427257 = 3320443) B3320443
theorem B2625017 : Blo 1748575 2625017 := bstep (se 2 (by rfl) ⟨984381, by rfl⟩ : syracuseStep 2625017 = 1968763) B1968763
theorem B9965065 : Blo 1748575 9965065 := bstep (se 2 (by rfl) ⟨3736899, by rfl⟩ : syracuseStep 9965065 = 7473799) B7473799
theorem B6639185 : Blo 1748575 6639185 := bstep (se 2 (by rfl) ⟨2489694, by rfl⟩ : syracuseStep 6639185 = 4979389) B4979389
theorem B2625119 : Blo 1748575 2625119 := bstep (se 1 (by rfl) ⟨1968839, by rfl⟩ : syracuseStep 2625119 = 3937679) B3937679
theorem B16821857 : Blo 1748575 16821857 := bstep (se 2 (by rfl) ⟨6308196, by rfl⟩ : syracuseStep 16821857 = 12616393) B12616393
theorem B1748703 : Blo 1748575 1748703 := bstep (se 1 (by rfl) ⟨1311527, by rfl⟩ : syracuseStep 1748703 = 2623055) B2623055
theorem B6639367 : Blo 1748575 6639367 := bstep (se 1 (by rfl) ⟨4979525, by rfl⟩ : syracuseStep 6639367 = 9959051) B9959051
theorem B5902091 : Blo 1748575 5902091 := bstep (se 1 (by rfl) ⟨4426568, by rfl⟩ : syracuseStep 5902091 = 8853137) B8853137
theorem B4427561 : Blo 1748575 4427561 := bstep (se 2 (by rfl) ⟨1660335, by rfl⟩ : syracuseStep 4427561 = 3320671) B3320671
theorem B3936041 : Blo 1748575 3936041 := bstep (se 2 (by rfl) ⟨1476015, by rfl⟩ : syracuseStep 3936041 = 2952031) B2952031
theorem B1748783 : Blo 1748575 1748783 := bstep (se 1 (by rfl) ⟨1311587, by rfl⟩ : syracuseStep 1748783 = 2623175) B2623175
theorem B2625335 : Blo 1748575 2625335 := bstep (se 1 (by rfl) ⟨1969001, by rfl⟩ : syracuseStep 2625335 = 3938003) B3938003
theorem B1748891 : Blo 1748575 1748891 := bstep (se 1 (by rfl) ⟨1311668, by rfl⟩ : syracuseStep 1748891 = 2623337) B2623337
theorem B1748943 : Blo 1748575 1748943 := bstep (se 1 (by rfl) ⟨1311707, by rfl⟩ : syracuseStep 1748943 = 2623415) B2623415
theorem B2101199 : Blo 1748575 2101199 := bstep (se 1 (by rfl) ⟨1575899, by rfl⟩ : syracuseStep 2101199 = 3151799) B3151799
theorem B1748967 : Blo 1748575 1748967 := bstep (se 1 (by rfl) ⟨1311725, by rfl⟩ : syracuseStep 1748967 = 2623451) B2623451
theorem B19935233 : Blo 1748575 19935233 := bstep (se 2 (by rfl) ⟨7475712, by rfl⟩ : syracuseStep 19935233 = 14951425) B14951425
theorem B6639641 : Blo 1748575 6639641 := bstep (se 2 (by rfl) ⟨2489865, by rfl⟩ : syracuseStep 6639641 = 4979731) B4979731
theorem B5902361 : Blo 1748575 5902361 := bstep (se 2 (by rfl) ⟨2213385, by rfl⟩ : syracuseStep 5902361 = 4426771) B4426771
theorem B2625641 : Blo 1748575 2625641 := bstep (se 2 (by rfl) ⟨984615, by rfl⟩ : syracuseStep 2625641 = 1969231) B1969231
theorem B4427905 : Blo 1748575 4427905 := bstep (se 2 (by rfl) ⟨1660464, by rfl⟩ : syracuseStep 4427905 = 3320929) B3320929
theorem B3789065 : Blo 1748575 3789065 := bstep (se 2 (by rfl) ⟨1420899, by rfl⟩ : syracuseStep 3789065 = 2841799) B2841799
theorem B1749279 : Blo 1748575 1749279 := bstep (se 1 (by rfl) ⟨1311959, by rfl⟩ : syracuseStep 1749279 = 2623919) B2623919
theorem B1749339 : Blo 1748575 1749339 := bstep (se 1 (by rfl) ⟨1312004, by rfl⟩ : syracuseStep 1749339 = 2624009) B2624009
theorem B1749359 : Blo 1748575 1749359 := bstep (se 1 (by rfl) ⟨1312019, by rfl⟩ : syracuseStep 1749359 = 2624039) B2624039
theorem B1749415 : Blo 1748575 1749415 := bstep (se 1 (by rfl) ⟨1312061, by rfl⟩ : syracuseStep 1749415 = 2624123) B2624123
theorem B6304175 : Blo 1748575 6304175 := bstep (se 1 (by rfl) ⟨4728131, by rfl⟩ : syracuseStep 6304175 = 9456263) B9456263
theorem B1749499 : Blo 1748575 1749499 := bstep (se 1 (by rfl) ⟨1312124, by rfl⟩ : syracuseStep 1749499 = 2624249) B2624249
theorem B1749567 : Blo 1748575 1749567 := bstep (se 1 (by rfl) ⟨1312175, by rfl⟩ : syracuseStep 1749567 = 2624351) B2624351
theorem B1749575 : Blo 1748575 1749575 := bstep (se 1 (by rfl) ⟨1312181, by rfl⟩ : syracuseStep 1749575 = 2624363) B2624363
theorem B1749727 : Blo 1748575 1749727 := bstep (se 1 (by rfl) ⟨1312295, by rfl⟩ : syracuseStep 1749727 = 2624591) B2624591
theorem B1749807 : Blo 1748575 1749807 := bstep (se 1 (by rfl) ⟨1312355, by rfl⟩ : syracuseStep 1749807 = 2624711) B2624711
theorem B15151951 : Blo 1748575 15151951 := bstep (se 1 (by rfl) ⟨11363963, by rfl⟩ : syracuseStep 15151951 = 22727927) B22727927
theorem B3937103 : Blo 1748575 3937103 := bstep (se 1 (by rfl) ⟨2952827, by rfl⟩ : syracuseStep 3937103 = 5905655) B5905655
theorem B2954063 : Blo 1748575 2954063 := bstep (se 1 (by rfl) ⟨2215547, by rfl⟩ : syracuseStep 2954063 = 4431095) B4431095
theorem B1749915 : Blo 1748575 1749915 := bstep (se 1 (by rfl) ⟨1312436, by rfl⟩ : syracuseStep 1749915 = 2624873) B2624873
theorem B4428715 : Blo 1748575 4428715 := bstep (se 1 (by rfl) ⟨3321536, by rfl⟩ : syracuseStep 4428715 = 6643073) B6643073
theorem B1749967 : Blo 1748575 1749967 := bstep (se 1 (by rfl) ⟨1312475, by rfl⟩ : syracuseStep 1749967 = 2624951) B2624951
theorem B1749991 : Blo 1748575 1749991 := bstep (se 1 (by rfl) ⟨1312493, by rfl⟩ : syracuseStep 1749991 = 2624987) B2624987
theorem B2560999 : Blo 1748575 2560999 := bstep (se 1 (by rfl) ⟨1920749, by rfl⟩ : syracuseStep 2560999 = 3841499) B3841499
theorem B3937319 : Blo 1748575 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B14939261 : Blo 1748575 14939261 := bstep (se 3 (by rfl) ⟨2801111, by rfl⟩ : syracuseStep 14939261 = 5602223) B5602223
theorem B4429019 : Blo 1748575 4429019 := bstep (se 1 (by rfl) ⟨3321764, by rfl⟩ : syracuseStep 4429019 = 6643529) B6643529
theorem B3937499 : Blo 1748575 3937499 := bstep (se 1 (by rfl) ⟨2953124, by rfl⟩ : syracuseStep 3937499 = 5906249) B5906249
theorem B5903603 : Blo 1748575 5903603 := bstep (se 1 (by rfl) ⟨4427702, by rfl⟩ : syracuseStep 5903603 = 8855405) B8855405
theorem B1750303 : Blo 1748575 1750303 := bstep (se 1 (by rfl) ⟨1312727, by rfl⟩ : syracuseStep 1750303 = 2625455) B2625455
theorem B1750363 : Blo 1748575 1750363 := bstep (se 1 (by rfl) ⟨1312772, by rfl⟩ : syracuseStep 1750363 = 2625545) B2625545
theorem B5903711 : Blo 1748575 5903711 := bstep (se 1 (by rfl) ⟨4427783, by rfl⟩ : syracuseStep 5903711 = 8855567) B8855567
theorem B4429151 : Blo 1748575 4429151 := bstep (se 1 (by rfl) ⟨3321863, by rfl⟩ : syracuseStep 4429151 = 6643727) B6643727
theorem B1750383 : Blo 1748575 1750383 := bstep (se 1 (by rfl) ⟨1312787, by rfl⟩ : syracuseStep 1750383 = 2625575) B2625575
theorem B3937697 : Blo 1748575 3937697 := bstep (se 2 (by rfl) ⟨1476636, by rfl⟩ : syracuseStep 3937697 = 2953273) B2953273
theorem B1750439 : Blo 1748575 1750439 := bstep (se 1 (by rfl) ⟨1312829, by rfl⟩ : syracuseStep 1750439 = 2625659) B2625659
theorem B1750523 : Blo 1748575 1750523 := bstep (se 1 (by rfl) ⟨1312892, by rfl⟩ : syracuseStep 1750523 = 2625785) B2625785
theorem B37852717 : Blo 1748575 37852717 := bstep (se 3 (by rfl) ⟨7097384, by rfl⟩ : syracuseStep 37852717 = 14194769) B14194769
theorem B2365103 : Blo 1748575 2365103 := bstep (se 1 (by rfl) ⟨1773827, by rfl⟩ : syracuseStep 2365103 = 3547655) B3547655
theorem B6641615 : Blo 1748575 6641615 := bstep (se 1 (by rfl) ⟨4981211, by rfl⟩ : syracuseStep 6641615 = 9962423) B9962423
theorem B3938255 : Blo 1748575 3938255 := bstep (se 1 (by rfl) ⟨2953691, by rfl⟩ : syracuseStep 3938255 = 5907383) B5907383
theorem B4429849 : Blo 1748575 4429849 := bstep (se 2 (by rfl) ⟨1661193, by rfl⟩ : syracuseStep 4429849 = 3322387) B3322387
theorem B8853785 : Blo 1748575 8853785 := bstep (se 2 (by rfl) ⟨3320169, by rfl⟩ : syracuseStep 8853785 = 6640339) B6640339
theorem B4430153 : Blo 1748575 4430153 := bstep (se 2 (by rfl) ⟨1661307, by rfl⟩ : syracuseStep 4430153 = 3322615) B3322615
theorem B3938633 : Blo 1748575 3938633 := bstep (se 2 (by rfl) ⟨1476987, by rfl⟩ : syracuseStep 3938633 = 2953975) B2953975
theorem B14195033 : Blo 1748575 14195033 := bstep (se 2 (by rfl) ⟨5323137, by rfl⟩ : syracuseStep 14195033 = 10646275) B10646275
theorem B3938651 : Blo 1748575 3938651 := bstep (se 1 (by rfl) ⟨2953988, by rfl⟩ : syracuseStep 3938651 = 5907977) B5907977
theorem B6388079 : Blo 1748575 6388079 := bstep (se 1 (by rfl) ⟨4791059, by rfl⟩ : syracuseStep 6388079 = 9582119) B9582119
theorem B7469495 : Blo 1748575 7469495 := bstep (se 1 (by rfl) ⟨5602121, by rfl⟩ : syracuseStep 7469495 = 11204243) B11204243
theorem B16816663 : Blo 1748575 16816663 := bstep (se 1 (by rfl) ⟨12612497, by rfl⟩ : syracuseStep 16816663 = 25224995) B25224995
theorem B6642283 : Blo 1748575 6642283 := bstep (se 1 (by rfl) ⟨4981712, by rfl⟩ : syracuseStep 6642283 = 9963425) B9963425
theorem B6642557 : Blo 1748575 6642557 := bstep (se 3 (by rfl) ⟨1245479, by rfl⟩ : syracuseStep 6642557 = 2490959) B2490959
theorem B5905277 : Blo 1748575 5905277 := bstep (se 3 (by rfl) ⟨1107239, by rfl⟩ : syracuseStep 5905277 = 2214479) B2214479
theorem B6642587 : Blo 1748575 6642587 := bstep (se 1 (by rfl) ⟨4981940, by rfl⟩ : syracuseStep 6642587 = 9963881) B9963881
theorem B5987243 : Blo 1748575 5987243 := bstep (se 1 (by rfl) ⟨4490432, by rfl⟩ : syracuseStep 5987243 = 8980865) B8980865
theorem B87440459 : Blo 1748575 87440459 := bstep (se 1 (by rfl) ⟨65580344, by rfl⟩ : syracuseStep 87440459 = 131160689) B131160689
theorem B5905547 : Blo 1748575 5905547 := bstep (se 1 (by rfl) ⟨4429160, by rfl⟩ : syracuseStep 5905547 = 8858321) B8858321
theorem B27303065 : Blo 1748575 27303065 := bstep (se 2 (by rfl) ⟨10238649, by rfl⟩ : syracuseStep 27303065 = 20477299) B20477299
theorem B17947813 : Blo 1748575 17947813 := bstep (se 4 (by rfl) ⟨1682607, by rfl⟩ : syracuseStep 17947813 = 3365215) B3365215
theorem B6479135 : Blo 1748575 6479135 := bstep (se 1 (by rfl) ⟨4859351, by rfl⟩ : syracuseStep 6479135 = 9718703) B9718703
theorem B29891915 : Blo 1748575 29891915 := bstep (se 1 (by rfl) ⟨22418936, by rfl⟩ : syracuseStep 29891915 = 44837873) B44837873
theorem B60611975 : Blo 1748575 60611975 := bstep (se 1 (by rfl) ⟨45458981, by rfl⟩ : syracuseStep 60611975 = 90917963) B90917963
theorem B30703049 : Blo 1748575 30703049 := bstep (se 2 (by rfl) ⟨11513643, by rfl⟩ : syracuseStep 30703049 = 23027287) B23027287
theorem B3735047 : Blo 1748575 3735047 := bstep (se 1 (by rfl) ⟨2801285, by rfl⟩ : syracuseStep 3735047 = 5602571) B5602571
theorem B6823507 : Blo 1748575 6823507 := bstep (se 1 (by rfl) ⟨5117630, by rfl⟩ : syracuseStep 6823507 = 10235261) B10235261
theorem B12615497 : Blo 1748575 12615497 := bstep (se 2 (by rfl) ⟨4730811, by rfl⟩ : syracuseStep 12615497 = 9461623) B9461623
theorem B17964929 : Blo 1748575 17964929 := bstep (se 2 (by rfl) ⟨6736848, by rfl⟩ : syracuseStep 17964929 = 13473697) B13473697
theorem B5906465 : Blo 1748575 5906465 := bstep (se 2 (by rfl) ⟨2214924, by rfl⟩ : syracuseStep 5906465 = 4429849) B4429849
theorem B4202783 : Blo 1748575 4202783 := bstep (se 1 (by rfl) ⟨3152087, by rfl⟩ : syracuseStep 4202783 = 6304175) B6304175
theorem B22422217 : Blo 1748575 22422217 := bstep (se 2 (by rfl) ⟨8408331, by rfl⟩ : syracuseStep 22422217 = 16816663) B16816663
theorem B8856377 : Blo 1748575 8856377 := bstep (se 2 (by rfl) ⟨3321141, by rfl⟩ : syracuseStep 8856377 = 6642283) B6642283
theorem B124552079 : Blo 1748575 124552079 := bstep (se 1 (by rfl) ⟨93414059, by rfl⟩ : syracuseStep 124552079 = 186828119) B186828119
theorem B11363237 : Blo 1748575 11363237 := bstep (se 4 (by rfl) ⟨1065303, by rfl⟩ : syracuseStep 11363237 = 2130607) B2130607
theorem B20202601 : Blo 1748575 20202601 := bstep (se 2 (by rfl) ⟨7575975, by rfl⟩ : syracuseStep 20202601 = 15151951) B15151951
theorem B19932317 : Blo 1748575 19932317 := bstep (se 3 (by rfl) ⟨3737309, by rfl⟩ : syracuseStep 19932317 = 7474619) B7474619
theorem B4982123 : Blo 1748575 4982123 := bstep (se 1 (by rfl) ⟨3736592, by rfl⟩ : syracuseStep 4982123 = 7473185) B7473185
theorem B2622875 : Blo 1748575 2622875 := bstep (se 1 (by rfl) ⟨1967156, by rfl⟩ : syracuseStep 2622875 = 3934313) B3934313
theorem B23930417 : Blo 1748575 23930417 := bstep (se 2 (by rfl) ⟨8973906, by rfl⟩ : syracuseStep 23930417 = 17947813) B17947813
theorem B9463355 : Blo 1748575 9463355 := bstep (se 1 (by rfl) ⟨7097516, by rfl⟩ : syracuseStep 9463355 = 14195033) B14195033
theorem B2623097 : Blo 1748575 2623097 := bstep (se 2 (by rfl) ⟨983661, by rfl⟩ : syracuseStep 2623097 = 1967323) B1967323
theorem B2950823 : Blo 1748575 2950823 := bstep (se 1 (by rfl) ⟨2213117, by rfl⟩ : syracuseStep 2950823 = 4426235) B4426235
theorem B5605031 : Blo 1748575 5605031 := bstep (se 1 (by rfl) ⟨4203773, by rfl⟩ : syracuseStep 5605031 = 8407547) B8407547
theorem B2803367 : Blo 1748575 2803367 := bstep (se 1 (by rfl) ⟨2102525, by rfl⟩ : syracuseStep 2803367 = 4205051) B4205051
theorem B2623199 : Blo 1748575 2623199 := bstep (se 1 (by rfl) ⟨1967399, by rfl⟩ : syracuseStep 2623199 = 3934799) B3934799
theorem B13289183 : Blo 1748575 13289183 := bstep (se 1 (by rfl) ⟨9966887, by rfl⟩ : syracuseStep 13289183 = 19933775) B19933775
theorem B2492155 : Blo 1748575 2492155 := bstep (se 1 (by rfl) ⟨1869116, by rfl⟩ : syracuseStep 2492155 = 3738233) B3738233
theorem B1967935 : Blo 1748575 1967935 := bstep (se 1 (by rfl) ⟨1475951, by rfl⟩ : syracuseStep 1967935 = 2951903) B2951903
theorem B2623295 : Blo 1748575 2623295 := bstep (se 1 (by rfl) ⟨1967471, by rfl⟩ : syracuseStep 2623295 = 3934943) B3934943
theorem B161580905 : Blo 1748575 161580905 := bstep (se 2 (by rfl) ⟨60592839, by rfl⟩ : syracuseStep 161580905 = 121185679) B121185679
theorem B2213831 : Blo 1748575 2213831 := bstep (se 1 (by rfl) ⟨1660373, by rfl⟩ : syracuseStep 2213831 = 3320747) B3320747
theorem B2623463 : Blo 1748575 2623463 := bstep (se 1 (by rfl) ⟨1967597, by rfl⟩ : syracuseStep 2623463 = 3935195) B3935195
theorem B2623481 : Blo 1748575 2623481 := bstep (se 2 (by rfl) ⟨983805, by rfl⟩ : syracuseStep 2623481 = 1967611) B1967611
theorem B2623583 : Blo 1748575 2623583 := bstep (se 1 (by rfl) ⟨1967687, by rfl⟩ : syracuseStep 2623583 = 3935375) B3935375
theorem B2213983 : Blo 1748575 2213983 := bstep (se 1 (by rfl) ⟨1660487, by rfl⟩ : syracuseStep 2213983 = 3320975) B3320975
theorem B1968223 : Blo 1748575 1968223 := bstep (se 1 (by rfl) ⟨1476167, by rfl⟩ : syracuseStep 1968223 = 2952335) B2952335
theorem B2623643 : Blo 1748575 2623643 := bstep (se 1 (by rfl) ⟨1967732, by rfl⟩ : syracuseStep 2623643 = 3935465) B3935465
theorem B2623679 : Blo 1748575 2623679 := bstep (se 1 (by rfl) ⟨1967759, by rfl⟩ : syracuseStep 2623679 = 3935519) B3935519
theorem B4319423 : Blo 1748575 4319423 := bstep (se 1 (by rfl) ⟨3239567, by rfl⟩ : syracuseStep 4319423 = 6479135) B6479135
theorem B7096511 : Blo 1748575 7096511 := bstep (se 1 (by rfl) ⟨5322383, by rfl⟩ : syracuseStep 7096511 = 10644767) B10644767
theorem B2623721 : Blo 1748575 2623721 := bstep (se 2 (by rfl) ⟨983895, by rfl⟩ : syracuseStep 2623721 = 1967791) B1967791
theorem B3934457 : Blo 1748575 3934457 := bstep (se 2 (by rfl) ⟨1475421, by rfl⟩ : syracuseStep 3934457 = 2950843) B2950843
theorem B3934511 : Blo 1748575 3934511 := bstep (se 1 (by rfl) ⟨2950883, by rfl⟩ : syracuseStep 3934511 = 5901767) B5901767
theorem B2951471 : Blo 1748575 2951471 := bstep (se 1 (by rfl) ⟨2213603, by rfl⟩ : syracuseStep 2951471 = 4427207) B4427207
theorem B4426123 : Blo 1748575 4426123 := bstep (se 1 (by rfl) ⟨3319592, by rfl⟩ : syracuseStep 4426123 = 6639185) B6639185
theorem B3934727 : Blo 1748575 3934727 := bstep (se 1 (by rfl) ⟨2951045, by rfl⟩ : syracuseStep 3934727 = 5902091) B5902091
theorem B43125257 : Blo 1748575 43125257 := bstep (se 2 (by rfl) ⟨16171971, by rfl⟩ : syracuseStep 43125257 = 32343943) B32343943
theorem B2951707 : Blo 1748575 2951707 := bstep (se 1 (by rfl) ⟨2213780, by rfl⟩ : syracuseStep 2951707 = 4427561) B4427561
theorem B2624027 : Blo 1748575 2624027 := bstep (se 1 (by rfl) ⟨1968020, by rfl⟩ : syracuseStep 2624027 = 3936041) B3936041
theorem B2624105 : Blo 1748575 2624105 := bstep (se 2 (by rfl) ⟨984039, by rfl⟩ : syracuseStep 2624105 = 1968079) B1968079
theorem B13290155 : Blo 1748575 13290155 := bstep (se 1 (by rfl) ⟨9967616, by rfl⟩ : syracuseStep 13290155 = 19935233) B19935233
theorem B4426427 : Blo 1748575 4426427 := bstep (se 1 (by rfl) ⟨3319820, by rfl⟩ : syracuseStep 4426427 = 6639641) B6639641
theorem B3934907 : Blo 1748575 3934907 := bstep (se 1 (by rfl) ⟨2951180, by rfl⟩ : syracuseStep 3934907 = 5902361) B5902361
theorem B4205243 : Blo 1748575 4205243 := bstep (se 1 (by rfl) ⟨3153932, by rfl⟩ : syracuseStep 4205243 = 6307865) B6307865
theorem B14953409 : Blo 1748575 14953409 := bstep (se 2 (by rfl) ⟨5607528, by rfl⟩ : syracuseStep 14953409 = 11215057) B11215057
theorem B2624633 : Blo 1748575 2624633 := bstep (se 2 (by rfl) ⟨984237, by rfl⟩ : syracuseStep 2624633 = 1968475) B1968475
theorem B3738745 : Blo 1748575 3738745 := bstep (se 2 (by rfl) ⟨1402029, by rfl⟩ : syracuseStep 3738745 = 2804059) B2804059
theorem B2624735 : Blo 1748575 2624735 := bstep (se 1 (by rfl) ⟨1968551, by rfl⟩ : syracuseStep 2624735 = 3937103) B3937103
theorem B1969375 : Blo 1748575 1969375 := bstep (se 1 (by rfl) ⟨1477031, by rfl⟩ : syracuseStep 1969375 = 2954063) B2954063
theorem B5680361 : Blo 1748575 5680361 := bstep (se 2 (by rfl) ⟨2130135, by rfl⟩ : syracuseStep 5680361 = 4260271) B4260271
theorem B2624777 : Blo 1748575 2624777 := bstep (se 2 (by rfl) ⟨984291, by rfl⟩ : syracuseStep 2624777 = 1968583) B1968583
theorem B10104173 : Blo 1748575 10104173 := bstep (se 3 (by rfl) ⟨1894532, by rfl⟩ : syracuseStep 10104173 = 3789065) B3789065
theorem B2624879 : Blo 1748575 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B2952679 : Blo 1748575 2952679 := bstep (se 1 (by rfl) ⟨2214509, by rfl⟩ : syracuseStep 2952679 = 4429019) B4429019
theorem B2624999 : Blo 1748575 2624999 := bstep (se 1 (by rfl) ⟨1968749, by rfl⟩ : syracuseStep 2624999 = 3937499) B3937499
theorem B3935735 : Blo 1748575 3935735 := bstep (se 1 (by rfl) ⟨2951801, by rfl⟩ : syracuseStep 3935735 = 5903603) B5903603
theorem B3935807 : Blo 1748575 3935807 := bstep (se 1 (by rfl) ⟨2951855, by rfl⟩ : syracuseStep 3935807 = 5903711) B5903711
theorem B2952767 : Blo 1748575 2952767 := bstep (se 1 (by rfl) ⟨2214575, by rfl⟩ : syracuseStep 2952767 = 4429151) B4429151
theorem B2625131 : Blo 1748575 2625131 := bstep (se 1 (by rfl) ⟨1968848, by rfl⟩ : syracuseStep 2625131 = 3937697) B3937697
theorem B17034877 : Blo 1748575 17034877 := bstep (se 3 (by rfl) ⟨3194039, by rfl⟩ : syracuseStep 17034877 = 6388079) B6388079
theorem B2625257 : Blo 1748575 2625257 := bstep (se 2 (by rfl) ⟨984471, by rfl⟩ : syracuseStep 2625257 = 1968943) B1968943
theorem B22720235 : Blo 1748575 22720235 := bstep (se 1 (by rfl) ⟨17040176, by rfl⟩ : syracuseStep 22720235 = 34080353) B34080353
theorem B1748807 : Blo 1748575 1748807 := bstep (se 1 (by rfl) ⟨1311605, by rfl⟩ : syracuseStep 1748807 = 2623211) B2623211
theorem B2625401 : Blo 1748575 2625401 := bstep (se 2 (by rfl) ⟨984525, by rfl⟩ : syracuseStep 2625401 = 1969051) B1969051
theorem B1748959 : Blo 1748575 1748959 := bstep (se 1 (by rfl) ⟨1311719, by rfl⟩ : syracuseStep 1748959 = 2623439) B2623439
theorem B4427743 : Blo 1748575 4427743 := bstep (se 1 (by rfl) ⟨3320807, by rfl⟩ : syracuseStep 4427743 = 6641615) B6641615
theorem B2625503 : Blo 1748575 2625503 := bstep (se 1 (by rfl) ⟨1969127, by rfl⟩ : syracuseStep 2625503 = 3938255) B3938255
theorem B5902523 : Blo 1748575 5902523 := bstep (se 1 (by rfl) ⟨4426892, by rfl⟩ : syracuseStep 5902523 = 8853785) B8853785
theorem B2953435 : Blo 1748575 2953435 := bstep (se 1 (by rfl) ⟨2215076, by rfl⟩ : syracuseStep 2953435 = 4430153) B4430153
theorem B2625755 : Blo 1748575 2625755 := bstep (se 1 (by rfl) ⟨1969316, by rfl⟩ : syracuseStep 2625755 = 3938633) B3938633
theorem B1749223 : Blo 1748575 1749223 := bstep (se 1 (by rfl) ⟨1311917, by rfl⟩ : syracuseStep 1749223 = 2623835) B2623835
theorem B2625767 : Blo 1748575 2625767 := bstep (se 1 (by rfl) ⟨1969325, by rfl⟩ : syracuseStep 2625767 = 3938651) B3938651
theorem B19919195 : Blo 1748575 19919195 := bstep (se 1 (by rfl) ⟨14939396, by rfl⟩ : syracuseStep 19919195 = 29878793) B29878793
theorem B1749375 : Blo 1748575 1749375 := bstep (se 1 (by rfl) ⟨1312031, by rfl⟩ : syracuseStep 1749375 = 2624063) B2624063
theorem B1749455 : Blo 1748575 1749455 := bstep (se 1 (by rfl) ⟨1312091, by rfl⟩ : syracuseStep 1749455 = 2624183) B2624183
theorem B2953705 : Blo 1748575 2953705 := bstep (se 2 (by rfl) ⟨1107639, by rfl⟩ : syracuseStep 2953705 = 2215279) B2215279
theorem B3936761 : Blo 1748575 3936761 := bstep (se 2 (by rfl) ⟨1476285, by rfl⟩ : syracuseStep 3936761 = 2952571) B2952571
theorem B4428371 : Blo 1748575 4428371 := bstep (se 1 (by rfl) ⟨3321278, by rfl⟩ : syracuseStep 4428371 = 6642557) B6642557
theorem B3936851 : Blo 1748575 3936851 := bstep (se 1 (by rfl) ⟨2952638, by rfl⟩ : syracuseStep 3936851 = 5905277) B5905277
theorem B4428391 : Blo 1748575 4428391 := bstep (se 1 (by rfl) ⟨3321293, by rfl⟩ : syracuseStep 4428391 = 6642587) B6642587
theorem B1749607 : Blo 1748575 1749607 := bstep (se 1 (by rfl) ⟨1312205, by rfl⟩ : syracuseStep 1749607 = 2624411) B2624411
theorem B3322471 : Blo 1748575 3322471 := bstep (se 1 (by rfl) ⟨2491853, by rfl⟩ : syracuseStep 3322471 = 4983707) B4983707
theorem B44864117 : Blo 1748575 44864117 := bstep (se 5 (by rfl) ⟨2103005, by rfl⟩ : syracuseStep 44864117 = 4206011) B4206011
theorem B5903009 : Blo 1748575 5903009 := bstep (se 2 (by rfl) ⟨2213628, by rfl⟩ : syracuseStep 5903009 = 4427257) B4427257
theorem B10105559 : Blo 1748575 10105559 := bstep (se 1 (by rfl) ⟨7579169, by rfl⟩ : syracuseStep 10105559 = 15158339) B15158339
theorem B3937031 : Blo 1748575 3937031 := bstep (se 1 (by rfl) ⟨2952773, by rfl⟩ : syracuseStep 3937031 = 5905547) B5905547
theorem B9098009 : Blo 1748575 9098009 := bstep (se 2 (by rfl) ⟨3411753, by rfl⟩ : syracuseStep 9098009 = 6823507) B6823507
theorem B1749871 : Blo 1748575 1749871 := bstep (se 1 (by rfl) ⟨1312403, by rfl⟩ : syracuseStep 1749871 = 2624807) B2624807
theorem B19927943 : Blo 1748575 19927943 := bstep (se 1 (by rfl) ⟨14945957, by rfl⟩ : syracuseStep 19927943 = 29891915) B29891915
theorem B1749927 : Blo 1748575 1749927 := bstep (se 1 (by rfl) ⟨1312445, by rfl⟩ : syracuseStep 1749927 = 2624891) B2624891
theorem B40407983 : Blo 1748575 40407983 := bstep (se 1 (by rfl) ⟨30305987, by rfl⟩ : syracuseStep 40407983 = 60611975) B60611975
theorem B20468699 : Blo 1748575 20468699 := bstep (se 1 (by rfl) ⟨15351524, by rfl⟩ : syracuseStep 20468699 = 30703049) B30703049
theorem B1750011 : Blo 1748575 1750011 := bstep (se 1 (by rfl) ⟨1312508, by rfl⟩ : syracuseStep 1750011 = 2625017) B2625017
theorem B8852489 : Blo 1748575 8852489 := bstep (se 2 (by rfl) ⟨3319683, by rfl⟩ : syracuseStep 8852489 = 6639367) B6639367
theorem B1750079 : Blo 1748575 1750079 := bstep (se 1 (by rfl) ⟨1312559, by rfl⟩ : syracuseStep 1750079 = 2625119) B2625119
theorem B1750223 : Blo 1748575 1750223 := bstep (se 1 (by rfl) ⟨1312667, by rfl⟩ : syracuseStep 1750223 = 2625335) B2625335
theorem B8410331 : Blo 1748575 8410331 := bstep (se 1 (by rfl) ⟨6307748, by rfl⟩ : syracuseStep 8410331 = 12615497) B12615497
theorem B1750427 : Blo 1748575 1750427 := bstep (se 1 (by rfl) ⟨1312820, by rfl⟩ : syracuseStep 1750427 = 2625641) B2625641
theorem B5903873 : Blo 1748575 5903873 := bstep (se 2 (by rfl) ⟨2213952, by rfl⟩ : syracuseStep 5903873 = 4427905) B4427905
theorem B233174557 : Blo 1748575 233174557 := bstep (se 3 (by rfl) ⟨43720229, by rfl⟩ : syracuseStep 233174557 = 87440459) B87440459
theorem B2365147 : Blo 1748575 2365147 := bstep (se 1 (by rfl) ⟨1773860, by rfl⟩ : syracuseStep 2365147 = 3547721) B3547721
theorem B3938111 : Blo 1748575 3938111 := bstep (se 1 (by rfl) ⟨2953583, by rfl⟩ : syracuseStep 3938111 = 5907167) B5907167
theorem B5904359 : Blo 1748575 5904359 := bstep (se 1 (by rfl) ⟨4428269, by rfl⟩ : syracuseStep 5904359 = 8856539) B8856539
theorem B4429799 : Blo 1748575 4429799 := bstep (se 1 (by rfl) ⟨3322349, by rfl⟩ : syracuseStep 4429799 = 6644699) B6644699
theorem B9959507 : Blo 1748575 9959507 := bstep (se 1 (by rfl) ⟨7469630, by rfl⟩ : syracuseStep 9959507 = 14939261) B14939261
theorem B5904467 : Blo 1748575 5904467 := bstep (se 1 (by rfl) ⟨4428350, by rfl⟩ : syracuseStep 5904467 = 8856701) B8856701
theorem B3938399 : Blo 1748575 3938399 := bstep (se 1 (by rfl) ⟨2953799, by rfl⟩ : syracuseStep 3938399 = 5907599) B5907599
theorem B11212955 : Blo 1748575 11212955 := bstep (se 1 (by rfl) ⟨8409716, by rfl⟩ : syracuseStep 11212955 = 16819433) B16819433
theorem B5904683 : Blo 1748575 5904683 := bstep (se 1 (by rfl) ⟨4428512, by rfl⟩ : syracuseStep 5904683 = 8857025) B8857025
theorem B46684583 : Blo 1748575 46684583 := bstep (se 1 (by rfl) ⟨35013437, by rfl⟩ : syracuseStep 46684583 = 70026875) B70026875
theorem B5683645 : Blo 1748575 5683645 := bstep (se 3 (by rfl) ⟨1065683, by rfl⟩ : syracuseStep 5683645 = 2131367) B2131367
theorem B5904953 : Blo 1748575 5904953 := bstep (se 2 (by rfl) ⟨2214357, by rfl⟩ : syracuseStep 5904953 = 4428715) B4428715
theorem B3414665 : Blo 1748575 3414665 := bstep (se 2 (by rfl) ⟨1280499, by rfl⟩ : syracuseStep 3414665 = 2560999) B2560999
theorem B47864681 : Blo 1748575 47864681 := bstep (se 2 (by rfl) ⟨17949255, by rfl⟩ : syracuseStep 47864681 = 35898511) B35898511
theorem B4979663 : Blo 1748575 4979663 := bstep (se 1 (by rfl) ⟨3734747, by rfl⟩ : syracuseStep 4979663 = 7469495) B7469495
theorem B6306941 : Blo 1748575 6306941 := bstep (se 3 (by rfl) ⟨1182551, by rfl⟩ : syracuseStep 6306941 = 2365103) B2365103
theorem B13286753 : Blo 1748575 13286753 := bstep (se 2 (by rfl) ⟨4982532, by rfl⟩ : syracuseStep 13286753 = 9965065) B9965065
theorem B3890543 : Blo 1748575 3890543 := bstep (se 1 (by rfl) ⟨2917907, by rfl⟩ : syracuseStep 3890543 = 5835815) B5835815
theorem B50470289 : Blo 1748575 50470289 := bstep (se 2 (by rfl) ⟨18926358, by rfl⟩ : syracuseStep 50470289 = 37852717) B37852717
theorem B18202043 : Blo 1748575 18202043 := bstep (se 1 (by rfl) ⟨13651532, by rfl⟩ : syracuseStep 18202043 = 27303065) B27303065
theorem B47906477 : Blo 1748575 47906477 := bstep (se 3 (by rfl) ⟨8982464, by rfl⟩ : syracuseStep 47906477 = 17964929) B17964929
theorem B2490031 : Blo 1748575 2490031 := bstep (se 1 (by rfl) ⟨1867523, by rfl⟩ : syracuseStep 2490031 = 3735047) B3735047
theorem B11214571 : Blo 1748575 11214571 := bstep (se 1 (by rfl) ⟨8410928, by rfl⟩ : syracuseStep 11214571 = 16821857) B16821857
theorem B15965981 : Blo 1748575 15965981 := bstep (se 3 (by rfl) ⟨2993621, by rfl⟩ : syracuseStep 15965981 = 5987243) B5987243
theorem B5603197 : Blo 1748575 5603197 := bstep (se 3 (by rfl) ⟨1050599, by rfl⟩ : syracuseStep 5603197 = 2101199) B2101199
theorem B2801855 : Blo 1748575 2801855 := bstep (se 1 (by rfl) ⟨2101391, by rfl⟩ : syracuseStep 2801855 = 4202783) B4202783
theorem B13279463 : Blo 1748575 13279463 := bstep (se 1 (by rfl) ⟨9959597, by rfl⟩ : syracuseStep 13279463 = 19919195) B19919195
theorem B16818509 : Blo 1748575 16818509 := bstep (se 3 (by rfl) ⟨3153470, by rfl⟩ : syracuseStep 16818509 = 6306941) B6306941
theorem B29909411 : Blo 1748575 29909411 := bstep (se 1 (by rfl) ⟨22432058, by rfl⟩ : syracuseStep 29909411 = 44864117) B44864117
theorem B18924029 : Blo 1748575 18924029 := bstep (se 3 (by rfl) ⟨3548255, by rfl⟩ : syracuseStep 18924029 = 7096511) B7096511
theorem B7578193 : Blo 1748575 7578193 := bstep (se 2 (by rfl) ⟨2841822, by rfl⟩ : syracuseStep 7578193 = 5683645) B5683645
theorem B83034719 : Blo 1748575 83034719 := bstep (se 1 (by rfl) ⟨62276039, by rfl⟩ : syracuseStep 83034719 = 124552079) B124552079
theorem B13288211 : Blo 1748575 13288211 := bstep (se 1 (by rfl) ⟨9966158, by rfl⟩ : syracuseStep 13288211 = 19932317) B19932317
theorem B6308903 : Blo 1748575 6308903 := bstep (se 1 (by rfl) ⟨4731677, by rfl⟩ : syracuseStep 6308903 = 9463355) B9463355
theorem B1967215 : Blo 1748575 1967215 := bstep (se 1 (by rfl) ⟨1475411, by rfl⟩ : syracuseStep 1967215 = 2950823) B2950823
theorem B3736687 : Blo 1748575 3736687 := bstep (se 1 (by rfl) ⟨2802515, by rfl⟩ : syracuseStep 3736687 = 5605031) B5605031
theorem B115000685 : Blo 1748575 115000685 := bstep (se 3 (by rfl) ⟨21562628, by rfl⟩ : syracuseStep 115000685 = 43125257) B43125257
theorem B26936801 : Blo 1748575 26936801 := bstep (se 2 (by rfl) ⟨10101300, by rfl⟩ : syracuseStep 26936801 = 20202601) B20202601
theorem B2622971 : Blo 1748575 2622971 := bstep (se 1 (by rfl) ⟨1967228, by rfl⟩ : syracuseStep 2622971 = 3934457) B3934457
theorem B2623007 : Blo 1748575 2623007 := bstep (se 1 (by rfl) ⟨1967255, by rfl⟩ : syracuseStep 2623007 = 3934511) B3934511
theorem B1967647 : Blo 1748575 1967647 := bstep (se 1 (by rfl) ⟨1475735, by rfl⟩ : syracuseStep 1967647 = 2951471) B2951471
theorem B31123055 : Blo 1748575 31123055 := bstep (se 1 (by rfl) ⟨23342291, by rfl⟩ : syracuseStep 31123055 = 46684583) B46684583
theorem B2623151 : Blo 1748575 2623151 := bstep (se 1 (by rfl) ⟨1967363, by rfl⟩ : syracuseStep 2623151 = 3934727) B3934727
theorem B2950951 : Blo 1748575 2950951 := bstep (se 1 (by rfl) ⟨2213213, by rfl⟩ : syracuseStep 2950951 = 4426427) B4426427
theorem B2623271 : Blo 1748575 2623271 := bstep (se 1 (by rfl) ⟨1967453, by rfl⟩ : syracuseStep 2623271 = 3934907) B3934907
theorem B2803495 : Blo 1748575 2803495 := bstep (se 1 (by rfl) ⟨2102621, by rfl⟩ : syracuseStep 2803495 = 4205243) B4205243
theorem B31909787 : Blo 1748575 31909787 := bstep (se 1 (by rfl) ⟨23932340, by rfl⟩ : syracuseStep 31909787 = 47864681) B47864681
theorem B3319775 : Blo 1748575 3319775 := bstep (se 1 (by rfl) ⟨2489831, by rfl⟩ : syracuseStep 3319775 = 4979663) B4979663
theorem B3786907 : Blo 1748575 3786907 := bstep (se 1 (by rfl) ⟨2840180, by rfl⟩ : syracuseStep 3786907 = 5680361) B5680361
theorem B3320041 : Blo 1748575 3320041 := bstep (se 2 (by rfl) ⟨1245015, by rfl⟩ : syracuseStep 3320041 = 2490031) B2490031
theorem B8857835 : Blo 1748575 8857835 := bstep (se 1 (by rfl) ⟨6643376, by rfl⟩ : syracuseStep 8857835 = 13286753) B13286753
theorem B6736115 : Blo 1748575 6736115 := bstep (se 1 (by rfl) ⟨5052086, by rfl⟩ : syracuseStep 6736115 = 10104173) B10104173
theorem B33646859 : Blo 1748575 33646859 := bstep (se 1 (by rfl) ⟨25235144, by rfl⟩ : syracuseStep 33646859 = 50470289) B50470289
theorem B12134695 : Blo 1748575 12134695 := bstep (se 1 (by rfl) ⟨9101021, by rfl⟩ : syracuseStep 12134695 = 18202043) B18202043
theorem B14952761 : Blo 1748575 14952761 := bstep (se 2 (by rfl) ⟨5607285, by rfl⟩ : syracuseStep 14952761 = 11214571) B11214571
theorem B2623823 : Blo 1748575 2623823 := bstep (se 1 (by rfl) ⟨1967867, by rfl⟩ : syracuseStep 2623823 = 3935735) B3935735
theorem B2623871 : Blo 1748575 2623871 := bstep (se 1 (by rfl) ⟨1967903, by rfl⟩ : syracuseStep 2623871 = 3935807) B3935807
theorem B1968511 : Blo 1748575 1968511 := bstep (se 1 (by rfl) ⟨1476383, by rfl⟩ : syracuseStep 1968511 = 2952767) B2952767
theorem B2623913 : Blo 1748575 2623913 := bstep (se 2 (by rfl) ⟨983967, by rfl⟩ : syracuseStep 2623913 = 1967935) B1967935
theorem B10643987 : Blo 1748575 10643987 := bstep (se 1 (by rfl) ⟨7982990, by rfl⟩ : syracuseStep 10643987 = 15965981) B15965981
theorem B3935015 : Blo 1748575 3935015 := bstep (se 1 (by rfl) ⟨2951261, by rfl⟩ : syracuseStep 3935015 = 5902523) B5902523
theorem B2951977 : Blo 1748575 2951977 := bstep (se 2 (by rfl) ⟨1106991, by rfl⟩ : syracuseStep 2951977 = 2213983) B2213983
theorem B2624297 : Blo 1748575 2624297 := bstep (se 2 (by rfl) ⟨984111, by rfl⟩ : syracuseStep 2624297 = 1968223) B1968223
theorem B1243597637 : Blo 1748575 1243597637 := bstep (se 4 (by rfl) ⟨116587278, by rfl⟩ : syracuseStep 1243597637 = 233174557) B233174557
theorem B2624507 : Blo 1748575 2624507 := bstep (se 1 (by rfl) ⟨1968380, by rfl⟩ : syracuseStep 2624507 = 3936761) B3936761
theorem B2952247 : Blo 1748575 2952247 := bstep (se 1 (by rfl) ⟨2214185, by rfl⟩ : syracuseStep 2952247 = 4428371) B4428371
theorem B2624567 : Blo 1748575 2624567 := bstep (se 1 (by rfl) ⟨1968425, by rfl⟩ : syracuseStep 2624567 = 3936851) B3936851
theorem B3935339 : Blo 1748575 3935339 := bstep (se 1 (by rfl) ⟨2951504, by rfl⟩ : syracuseStep 3935339 = 5903009) B5903009
theorem B2624687 : Blo 1748575 2624687 := bstep (se 1 (by rfl) ⟨1968515, by rfl⟩ : syracuseStep 2624687 = 3937031) B3937031
theorem B5901497 : Blo 1748575 5901497 := bstep (se 2 (by rfl) ⟨2213061, by rfl⟩ : syracuseStep 5901497 = 4426123) B4426123
theorem B6065339 : Blo 1748575 6065339 := bstep (se 1 (by rfl) ⟨4549004, by rfl⟩ : syracuseStep 6065339 = 9098009) B9098009
theorem B26938655 : Blo 1748575 26938655 := bstep (se 1 (by rfl) ⟨20203991, by rfl⟩ : syracuseStep 26938655 = 40407983) B40407983
theorem B5901659 : Blo 1748575 5901659 := bstep (se 1 (by rfl) ⟨4426244, by rfl⟩ : syracuseStep 5901659 = 8852489) B8852489
theorem B3935609 : Blo 1748575 3935609 := bstep (se 2 (by rfl) ⟨1475853, by rfl⟩ : syracuseStep 3935609 = 2951707) B2951707
theorem B3321415 : Blo 1748575 3321415 := bstep (se 1 (by rfl) ⟨2491061, by rfl⟩ : syracuseStep 3321415 = 4982123) B4982123
theorem B29896289 : Blo 1748575 29896289 := bstep (se 2 (by rfl) ⟨11211108, by rfl⟩ : syracuseStep 29896289 = 22422217) B22422217
theorem B1748583 : Blo 1748575 1748583 := bstep (se 1 (by rfl) ⟨1311437, by rfl⟩ : syracuseStep 1748583 = 2622875) B2622875
theorem B3935915 : Blo 1748575 3935915 := bstep (se 1 (by rfl) ⟨2951936, by rfl⟩ : syracuseStep 3935915 = 5903873) B5903873
theorem B15953611 : Blo 1748575 15953611 := bstep (se 1 (by rfl) ⟨11965208, by rfl⟩ : syracuseStep 15953611 = 23930417) B23930417
theorem B1748731 : Blo 1748575 1748731 := bstep (se 1 (by rfl) ⟨1311548, by rfl⟩ : syracuseStep 1748731 = 2623097) B2623097
theorem B1748799 : Blo 1748575 1748799 := bstep (se 1 (by rfl) ⟨1311599, by rfl⟩ : syracuseStep 1748799 = 2623199) B2623199
theorem B8859455 : Blo 1748575 8859455 := bstep (se 1 (by rfl) ⟨6644591, by rfl⟩ : syracuseStep 8859455 = 13289183) B13289183
theorem B1748863 : Blo 1748575 1748863 := bstep (se 1 (by rfl) ⟨1311647, by rfl⟩ : syracuseStep 1748863 = 2623295) B2623295
theorem B2625407 : Blo 1748575 2625407 := bstep (se 1 (by rfl) ⟨1969055, by rfl⟩ : syracuseStep 2625407 = 3938111) B3938111
theorem B107720603 : Blo 1748575 107720603 := bstep (se 1 (by rfl) ⟨80790452, by rfl⟩ : syracuseStep 107720603 = 161580905) B161580905
theorem B1748975 : Blo 1748575 1748975 := bstep (se 1 (by rfl) ⟨1311731, by rfl⟩ : syracuseStep 1748975 = 2623463) B2623463
theorem B3936239 : Blo 1748575 3936239 := bstep (se 1 (by rfl) ⟨2952179, by rfl⟩ : syracuseStep 3936239 = 5904359) B5904359
theorem B2953199 : Blo 1748575 2953199 := bstep (se 1 (by rfl) ⟨2214899, by rfl⟩ : syracuseStep 2953199 = 4429799) B4429799
theorem B1748987 : Blo 1748575 1748987 := bstep (se 1 (by rfl) ⟨1311740, by rfl⟩ : syracuseStep 1748987 = 2623481) B2623481
theorem B6639671 : Blo 1748575 6639671 := bstep (se 1 (by rfl) ⟨4979753, by rfl⟩ : syracuseStep 6639671 = 9959507) B9959507
theorem B3936311 : Blo 1748575 3936311 := bstep (se 1 (by rfl) ⟨2952233, by rfl⟩ : syracuseStep 3936311 = 5904467) B5904467
theorem B1749055 : Blo 1748575 1749055 := bstep (se 1 (by rfl) ⟨1311791, by rfl⟩ : syracuseStep 1749055 = 2623583) B2623583
theorem B2625599 : Blo 1748575 2625599 := bstep (se 1 (by rfl) ⟨1969199, by rfl⟩ : syracuseStep 2625599 = 3938399) B3938399
theorem B1749095 : Blo 1748575 1749095 := bstep (se 1 (by rfl) ⟨1311821, by rfl⟩ : syracuseStep 1749095 = 2623643) B2623643
theorem B7475303 : Blo 1748575 7475303 := bstep (se 1 (by rfl) ⟨5606477, by rfl⟩ : syracuseStep 7475303 = 11212955) B11212955
theorem B1749119 : Blo 1748575 1749119 := bstep (se 1 (by rfl) ⟨1311839, by rfl⟩ : syracuseStep 1749119 = 2623679) B2623679
theorem B2879615 : Blo 1748575 2879615 := bstep (se 1 (by rfl) ⟨2159711, by rfl⟩ : syracuseStep 2879615 = 4319423) B4319423
theorem B1749147 : Blo 1748575 1749147 := bstep (se 1 (by rfl) ⟨1311860, by rfl⟩ : syracuseStep 1749147 = 2623721) B2623721
theorem B4984993 : Blo 1748575 4984993 := bstep (se 2 (by rfl) ⟨1869372, by rfl⟩ : syracuseStep 4984993 = 3738745) B3738745
theorem B3936455 : Blo 1748575 3936455 := bstep (se 1 (by rfl) ⟨2952341, by rfl⟩ : syracuseStep 3936455 = 5904683) B5904683
theorem B2625833 : Blo 1748575 2625833 := bstep (se 2 (by rfl) ⟨984687, by rfl⟩ : syracuseStep 2625833 = 1969375) B1969375
theorem B1749351 : Blo 1748575 1749351 := bstep (se 1 (by rfl) ⟨1312013, by rfl⟩ : syracuseStep 1749351 = 2624027) B2624027
theorem B3936635 : Blo 1748575 3936635 := bstep (se 1 (by rfl) ⟨2952476, by rfl⟩ : syracuseStep 3936635 = 5904953) B5904953
theorem B1749403 : Blo 1748575 1749403 := bstep (se 1 (by rfl) ⟨1312052, by rfl⟩ : syracuseStep 1749403 = 2624105) B2624105
theorem B7475645 : Blo 1748575 7475645 := bstep (se 3 (by rfl) ⟨1401683, by rfl⟩ : syracuseStep 7475645 = 2803367) B2803367
theorem B8860103 : Blo 1748575 8860103 := bstep (se 1 (by rfl) ⟨6645077, by rfl⟩ : syracuseStep 8860103 = 13290155) B13290155
theorem B3936905 : Blo 1748575 3936905 := bstep (se 2 (by rfl) ⟨1476339, by rfl⟩ : syracuseStep 3936905 = 2952679) B2952679
theorem B1749755 : Blo 1748575 1749755 := bstep (se 1 (by rfl) ⟨1312316, by rfl⟩ : syracuseStep 1749755 = 2624633) B2624633
theorem B1749823 : Blo 1748575 1749823 := bstep (se 1 (by rfl) ⟨1312367, by rfl⟩ : syracuseStep 1749823 = 2624735) B2624735
theorem B22713169 : Blo 1748575 22713169 := bstep (se 2 (by rfl) ⟨8517438, by rfl⟩ : syracuseStep 22713169 = 17034877) B17034877
theorem B1749851 : Blo 1748575 1749851 := bstep (se 1 (by rfl) ⟨1312388, by rfl⟩ : syracuseStep 1749851 = 2624777) B2624777
theorem B1749919 : Blo 1748575 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B1749999 : Blo 1748575 1749999 := bstep (se 1 (by rfl) ⟨1312499, by rfl⟩ : syracuseStep 1749999 = 2624999) B2624999
theorem B3322873 : Blo 1748575 3322873 := bstep (se 2 (by rfl) ⟨1246077, by rfl⟩ : syracuseStep 3322873 = 2492155) B2492155
theorem B1750087 : Blo 1748575 1750087 := bstep (se 1 (by rfl) ⟨1312565, by rfl⟩ : syracuseStep 1750087 = 2625131) B2625131
theorem B31937651 : Blo 1748575 31937651 := bstep (se 1 (by rfl) ⟨23953238, by rfl⟩ : syracuseStep 31937651 = 47906477) B47906477
theorem B1750171 : Blo 1748575 1750171 := bstep (se 1 (by rfl) ⟨1312628, by rfl⟩ : syracuseStep 1750171 = 2625257) B2625257
theorem B5903549 : Blo 1748575 5903549 := bstep (se 3 (by rfl) ⟨1106915, by rfl⟩ : syracuseStep 5903549 = 2213831) B2213831
theorem B1750267 : Blo 1748575 1750267 := bstep (se 1 (by rfl) ⟨1312700, by rfl⟩ : syracuseStep 1750267 = 2625401) B2625401
theorem B5903657 : Blo 1748575 5903657 := bstep (se 2 (by rfl) ⟨2213871, by rfl⟩ : syracuseStep 5903657 = 4427743) B4427743
theorem B6737039 : Blo 1748575 6737039 := bstep (se 1 (by rfl) ⟨5052779, by rfl⟩ : syracuseStep 6737039 = 10105559) B10105559
theorem B1750335 : Blo 1748575 1750335 := bstep (se 1 (by rfl) ⟨1312751, by rfl⟩ : syracuseStep 1750335 = 2625503) B2625503
theorem B3937643 : Blo 1748575 3937643 := bstep (se 1 (by rfl) ⟨2953232, by rfl⟩ : syracuseStep 3937643 = 5906465) B5906465
theorem B1750503 : Blo 1748575 1750503 := bstep (se 1 (by rfl) ⟨1312877, by rfl⟩ : syracuseStep 1750503 = 2625755) B2625755
theorem B1750511 : Blo 1748575 1750511 := bstep (se 1 (by rfl) ⟨1312883, by rfl⟩ : syracuseStep 1750511 = 2625767) B2625767
theorem B3937913 : Blo 1748575 3937913 := bstep (se 2 (by rfl) ⟨1476717, by rfl⟩ : syracuseStep 3937913 = 2953435) B2953435
theorem B5904251 : Blo 1748575 5904251 := bstep (se 1 (by rfl) ⟨4428188, by rfl⟩ : syracuseStep 5904251 = 8856377) B8856377
theorem B22427549 : Blo 1748575 22427549 := bstep (se 3 (by rfl) ⟨4205165, by rfl⟩ : syracuseStep 22427549 = 8410331) B8410331
theorem B13285295 : Blo 1748575 13285295 := bstep (se 1 (by rfl) ⟨9963971, by rfl⟩ : syracuseStep 13285295 = 19927943) B19927943
theorem B7575491 : Blo 1748575 7575491 := bstep (se 1 (by rfl) ⟨5681618, by rfl⟩ : syracuseStep 7575491 = 11363237) B11363237
theorem B3938273 : Blo 1748575 3938273 := bstep (se 2 (by rfl) ⟨1476852, by rfl⟩ : syracuseStep 3938273 = 2953705) B2953705
theorem B13645799 : Blo 1748575 13645799 := bstep (se 1 (by rfl) ⟨10234349, by rfl⟩ : syracuseStep 13645799 = 20468699) B20468699
theorem B5904521 : Blo 1748575 5904521 := bstep (se 2 (by rfl) ⟨2214195, by rfl⟩ : syracuseStep 5904521 = 4428391) B4428391
theorem B4429961 : Blo 1748575 4429961 := bstep (se 2 (by rfl) ⟨1661235, by rfl⟩ : syracuseStep 4429961 = 3322471) B3322471
theorem B41499125 : Blo 1748575 41499125 := bstep (se 5 (by rfl) ⟨1945271, by rfl⟩ : syracuseStep 41499125 = 3890543) B3890543
theorem B2276443 : Blo 1748575 2276443 := bstep (se 1 (by rfl) ⟨1707332, by rfl⟩ : syracuseStep 2276443 = 3414665) B3414665
theorem B60587293 : Blo 1748575 60587293 := bstep (se 3 (by rfl) ⟨11360117, by rfl⟩ : syracuseStep 60587293 = 22720235) B22720235
theorem B9968939 : Blo 1748575 9968939 := bstep (se 1 (by rfl) ⟨7476704, by rfl⟩ : syracuseStep 9968939 = 14953409) B14953409
theorem B3153529 : Blo 1748575 3153529 := bstep (se 2 (by rfl) ⟨1182573, by rfl⟩ : syracuseStep 3153529 = 2365147) B2365147
theorem B7470929 : Blo 1748575 7470929 := bstep (se 2 (by rfl) ⟨2801598, by rfl⟩ : syracuseStep 7470929 = 5603197) B5603197
theorem B1867903 : Blo 1748575 1867903 := bstep (se 1 (by rfl) ⟨1400927, by rfl⟩ : syracuseStep 1867903 = 2801855) B2801855
theorem B19939607 : Blo 1748575 19939607 := bstep (se 1 (by rfl) ⟨14954705, by rfl⟩ : syracuseStep 19939607 = 29909411) B29909411
theorem B5906735 : Blo 1748575 5906735 := bstep (se 1 (by rfl) ⟨4430051, by rfl⟩ : syracuseStep 5906735 = 8860103) B8860103
theorem B12616019 : Blo 1748575 12616019 := bstep (se 1 (by rfl) ⟨9462014, by rfl⟩ : syracuseStep 12616019 = 18924029) B18924029
theorem B16179593 : Blo 1748575 16179593 := bstep (se 2 (by rfl) ⟨6067347, by rfl⟩ : syracuseStep 16179593 = 12134695) B12134695
theorem B12141029 : Blo 1748575 12141029 := bstep (se 4 (by rfl) ⟨1138221, by rfl⟩ : syracuseStep 12141029 = 2276443) B2276443
theorem B21291767 : Blo 1748575 21291767 := bstep (se 1 (by rfl) ⟨15968825, by rfl⟩ : syracuseStep 21291767 = 31937651) B31937651
theorem B17957867 : Blo 1748575 17957867 := bstep (se 1 (by rfl) ⟨13468400, by rfl⟩ : syracuseStep 17957867 = 26936801) B26936801
theorem B14951699 : Blo 1748575 14951699 := bstep (se 1 (by rfl) ⟨11213774, by rfl⟩ : syracuseStep 14951699 = 22427549) B22427549
theorem B8856863 : Blo 1748575 8856863 := bstep (se 1 (by rfl) ⟨6642647, by rfl⟩ : syracuseStep 8856863 = 13285295) B13285295
theorem B2213183 : Blo 1748575 2213183 := bstep (se 1 (by rfl) ⟨1659887, by rfl⟩ : syracuseStep 2213183 = 3319775) B3319775
theorem B2622953 : Blo 1748575 2622953 := bstep (se 2 (by rfl) ⟨983607, by rfl⟩ : syracuseStep 2622953 = 1967215) B1967215
theorem B4982249 : Blo 1748575 4982249 := bstep (se 2 (by rfl) ⟨1868343, by rfl⟩ : syracuseStep 4982249 = 3736687) B3736687
theorem B4490743 : Blo 1748575 4490743 := bstep (se 1 (by rfl) ⟨3368057, by rfl⟩ : syracuseStep 4490743 = 6736115) B6736115
theorem B22431239 : Blo 1748575 22431239 := bstep (se 1 (by rfl) ⟨16823429, by rfl⟩ : syracuseStep 22431239 = 33646859) B33646859
theorem B82994813 : Blo 1748575 82994813 := bstep (se 3 (by rfl) ⟨15561527, by rfl⟩ : syracuseStep 82994813 = 31123055) B31123055
theorem B27666083 : Blo 1748575 27666083 := bstep (se 1 (by rfl) ⟨20749562, by rfl⟩ : syracuseStep 27666083 = 41499125) B41499125
theorem B80783057 : Blo 1748575 80783057 := bstep (se 2 (by rfl) ⟨30293646, by rfl⟩ : syracuseStep 80783057 = 60587293) B60587293
theorem B2623343 : Blo 1748575 2623343 := bstep (se 1 (by rfl) ⟨1967507, by rfl⟩ : syracuseStep 2623343 = 3935015) B3935015
theorem B829065091 : Blo 1748575 829065091 := bstep (se 1 (by rfl) ⟨621798818, by rfl⟩ : syracuseStep 829065091 = 1243597637) B1243597637
theorem B2623529 : Blo 1748575 2623529 := bstep (se 2 (by rfl) ⟨983823, by rfl⟩ : syracuseStep 2623529 = 1967647) B1967647
theorem B2623559 : Blo 1748575 2623559 := bstep (se 1 (by rfl) ⟨1967669, by rfl⟩ : syracuseStep 2623559 = 3935339) B3935339
theorem B4491359 : Blo 1748575 4491359 := bstep (se 1 (by rfl) ⟨3368519, by rfl⟩ : syracuseStep 4491359 = 6737039) B6737039
theorem B3934331 : Blo 1748575 3934331 := bstep (se 1 (by rfl) ⟨2950748, by rfl⟩ : syracuseStep 3934331 = 5901497) B5901497
theorem B4204705 : Blo 1748575 4204705 := bstep (se 2 (by rfl) ⟨1576764, by rfl⟩ : syracuseStep 4204705 = 3153529) B3153529
theorem B17959103 : Blo 1748575 17959103 := bstep (se 1 (by rfl) ⟨13469327, by rfl⟩ : syracuseStep 17959103 = 26938655) B26938655
theorem B6645959 : Blo 1748575 6645959 := bstep (se 1 (by rfl) ⟨4984469, by rfl⟩ : syracuseStep 6645959 = 9968939) B9968939
theorem B3934439 : Blo 1748575 3934439 := bstep (se 1 (by rfl) ⟨2950829, by rfl⟩ : syracuseStep 3934439 = 5901659) B5901659
theorem B2623739 : Blo 1748575 2623739 := bstep (se 1 (by rfl) ⟨1967804, by rfl⟩ : syracuseStep 2623739 = 3935609) B3935609
theorem B3934601 : Blo 1748575 3934601 := bstep (se 2 (by rfl) ⟨1475475, by rfl⟩ : syracuseStep 3934601 = 2950951) B2950951
theorem B3737993 : Blo 1748575 3737993 := bstep (se 2 (by rfl) ⟨1401747, by rfl⟩ : syracuseStep 3737993 = 2803495) B2803495
theorem B2623943 : Blo 1748575 2623943 := bstep (se 1 (by rfl) ⟨1967957, by rfl⟩ : syracuseStep 2623943 = 3935915) B3935915
theorem B71813735 : Blo 1748575 71813735 := bstep (se 1 (by rfl) ⟨53860301, by rfl⟩ : syracuseStep 71813735 = 107720603) B107720603
theorem B2624159 : Blo 1748575 2624159 := bstep (se 1 (by rfl) ⟨1968119, by rfl⟩ : syracuseStep 2624159 = 3936239) B3936239
theorem B1968799 : Blo 1748575 1968799 := bstep (se 1 (by rfl) ⟨1476599, by rfl⟩ : syracuseStep 1968799 = 2953199) B2953199
theorem B4426447 : Blo 1748575 4426447 := bstep (se 1 (by rfl) ⟨3319835, by rfl⟩ : syracuseStep 4426447 = 6639671) B6639671
theorem B2624207 : Blo 1748575 2624207 := bstep (se 1 (by rfl) ⟨1968155, by rfl⟩ : syracuseStep 2624207 = 3936311) B3936311
theorem B4983535 : Blo 1748575 4983535 := bstep (se 1 (by rfl) ⟨3737651, by rfl⟩ : syracuseStep 4983535 = 7475303) B7475303
theorem B2624303 : Blo 1748575 2624303 := bstep (se 1 (by rfl) ⟨1968227, by rfl⟩ : syracuseStep 2624303 = 3936455) B3936455
theorem B5049209 : Blo 1748575 5049209 := bstep (se 2 (by rfl) ⟨1893453, by rfl⟩ : syracuseStep 5049209 = 3786907) B3786907
theorem B6646657 : Blo 1748575 6646657 := bstep (se 2 (by rfl) ⟨2492496, by rfl⟩ : syracuseStep 6646657 = 4984993) B4984993
theorem B2624423 : Blo 1748575 2624423 := bstep (se 1 (by rfl) ⟨1968317, by rfl⟩ : syracuseStep 2624423 = 3936635) B3936635
theorem B4983763 : Blo 1748575 4983763 := bstep (se 1 (by rfl) ⟨3737822, by rfl⟩ : syracuseStep 4983763 = 7475645) B7475645
theorem B4426721 : Blo 1748575 4426721 := bstep (se 2 (by rfl) ⟨1660020, by rfl⟩ : syracuseStep 4426721 = 3320041) B3320041
theorem B7678973 : Blo 1748575 7678973 := bstep (se 3 (by rfl) ⟨1439807, by rfl⟩ : syracuseStep 7678973 = 2879615) B2879615
theorem B55356479 : Blo 1748575 55356479 := bstep (se 1 (by rfl) ⟨41517359, by rfl⟩ : syracuseStep 55356479 = 83034719) B83034719
theorem B2624603 : Blo 1748575 2624603 := bstep (se 1 (by rfl) ⟨1968452, by rfl⟩ : syracuseStep 2624603 = 3936905) B3936905
theorem B16174237 : Blo 1748575 16174237 := bstep (se 3 (by rfl) ⟨3032669, by rfl⟩ : syracuseStep 16174237 = 6065339) B6065339
theorem B2624681 : Blo 1748575 2624681 := bstep (se 2 (by rfl) ⟨984255, by rfl⟩ : syracuseStep 2624681 = 1968511) B1968511
theorem B8858807 : Blo 1748575 8858807 := bstep (se 1 (by rfl) ⟨6644105, by rfl⟩ : syracuseStep 8858807 = 13288211) B13288211
theorem B4205935 : Blo 1748575 4205935 := bstep (se 1 (by rfl) ⟨3154451, by rfl⟩ : syracuseStep 4205935 = 6308903) B6308903
theorem B10104257 : Blo 1748575 10104257 := bstep (se 2 (by rfl) ⟨3789096, by rfl⟩ : syracuseStep 10104257 = 7578193) B7578193
theorem B3935699 : Blo 1748575 3935699 := bstep (se 1 (by rfl) ⟨2951774, by rfl⟩ : syracuseStep 3935699 = 5903549) B5903549
theorem B3935771 : Blo 1748575 3935771 := bstep (se 1 (by rfl) ⟨2951828, by rfl⟩ : syracuseStep 3935771 = 5903657) B5903657
theorem B2625095 : Blo 1748575 2625095 := bstep (se 1 (by rfl) ⟨1968821, by rfl⟩ : syracuseStep 2625095 = 3937643) B3937643
theorem B1748647 : Blo 1748575 1748647 := bstep (se 1 (by rfl) ⟨1311485, by rfl⟩ : syracuseStep 1748647 = 2622971) B2622971
theorem B1748671 : Blo 1748575 1748671 := bstep (se 1 (by rfl) ⟨1311503, by rfl⟩ : syracuseStep 1748671 = 2623007) B2623007
theorem B3935969 : Blo 1748575 3935969 := bstep (se 2 (by rfl) ⟨1475988, by rfl⟩ : syracuseStep 3935969 = 2951977) B2951977
theorem B2625275 : Blo 1748575 2625275 := bstep (se 1 (by rfl) ⟨1968956, by rfl⟩ : syracuseStep 2625275 = 3937913) B3937913
theorem B1748767 : Blo 1748575 1748767 := bstep (se 1 (by rfl) ⟨1311575, by rfl⟩ : syracuseStep 1748767 = 2623151) B2623151
theorem B1748847 : Blo 1748575 1748847 := bstep (se 1 (by rfl) ⟨1311635, by rfl⟩ : syracuseStep 1748847 = 2623271) B2623271
theorem B3936167 : Blo 1748575 3936167 := bstep (se 1 (by rfl) ⟨2952125, by rfl⟩ : syracuseStep 3936167 = 5904251) B5904251
theorem B2625515 : Blo 1748575 2625515 := bstep (se 1 (by rfl) ⟨1969136, by rfl⟩ : syracuseStep 2625515 = 3938273) B3938273
theorem B9097199 : Blo 1748575 9097199 := bstep (se 1 (by rfl) ⟨6822899, by rfl⟩ : syracuseStep 9097199 = 13645799) B13645799
theorem B3936329 : Blo 1748575 3936329 := bstep (se 2 (by rfl) ⟨1476123, by rfl⟩ : syracuseStep 3936329 = 2952247) B2952247
theorem B3936347 : Blo 1748575 3936347 := bstep (se 1 (by rfl) ⟨2952260, by rfl⟩ : syracuseStep 3936347 = 5904521) B5904521
theorem B2953307 : Blo 1748575 2953307 := bstep (se 1 (by rfl) ⟨2214980, by rfl⟩ : syracuseStep 2953307 = 4429961) B4429961
theorem B1749215 : Blo 1748575 1749215 := bstep (se 1 (by rfl) ⟨1311911, by rfl⟩ : syracuseStep 1749215 = 2623823) B2623823
theorem B1749247 : Blo 1748575 1749247 := bstep (se 1 (by rfl) ⟨1311935, by rfl⟩ : syracuseStep 1749247 = 2623871) B2623871
theorem B1749275 : Blo 1748575 1749275 := bstep (se 1 (by rfl) ⟨1311956, by rfl⟩ : syracuseStep 1749275 = 2623913) B2623913
theorem B1749531 : Blo 1748575 1749531 := bstep (se 1 (by rfl) ⟨1312148, by rfl⟩ : syracuseStep 1749531 = 2624297) B2624297
theorem B1749671 : Blo 1748575 1749671 := bstep (se 1 (by rfl) ⟨1312253, by rfl⟩ : syracuseStep 1749671 = 2624507) B2624507
theorem B1749711 : Blo 1748575 1749711 := bstep (se 1 (by rfl) ⟨1312283, by rfl⟩ : syracuseStep 1749711 = 2624567) B2624567
theorem B4428553 : Blo 1748575 4428553 := bstep (se 2 (by rfl) ⟨1660707, by rfl⟩ : syracuseStep 4428553 = 3321415) B3321415
theorem B1749791 : Blo 1748575 1749791 := bstep (se 1 (by rfl) ⟨1312343, by rfl⟩ : syracuseStep 1749791 = 2624687) B2624687
theorem B21271481 : Blo 1748575 21271481 := bstep (se 2 (by rfl) ⟨7976805, by rfl⟩ : syracuseStep 21271481 = 15953611) B15953611
theorem B1750271 : Blo 1748575 1750271 := bstep (se 1 (by rfl) ⟨1312703, by rfl⟩ : syracuseStep 1750271 = 2625407) B2625407
theorem B1750399 : Blo 1748575 1750399 := bstep (se 1 (by rfl) ⟨1312799, by rfl⟩ : syracuseStep 1750399 = 2625599) B2625599
theorem B8852975 : Blo 1748575 8852975 := bstep (se 1 (by rfl) ⟨6639731, by rfl⟩ : syracuseStep 8852975 = 13279463) B13279463
theorem B1750555 : Blo 1748575 1750555 := bstep (se 1 (by rfl) ⟨1312916, by rfl⟩ : syracuseStep 1750555 = 2625833) B2625833
theorem B11212339 : Blo 1748575 11212339 := bstep (se 1 (by rfl) ⟨8409254, by rfl⟩ : syracuseStep 11212339 = 16818509) B16818509
theorem B76667123 : Blo 1748575 76667123 := bstep (se 1 (by rfl) ⟨57500342, by rfl⟩ : syracuseStep 76667123 = 115000685) B115000685
theorem B30284225 : Blo 1748575 30284225 := bstep (se 2 (by rfl) ⟨11356584, by rfl⟩ : syracuseStep 30284225 = 22713169) B22713169
theorem B21273191 : Blo 1748575 21273191 := bstep (se 1 (by rfl) ⟨15954893, by rfl⟩ : syracuseStep 21273191 = 31909787) B31909787
theorem B4430497 : Blo 1748575 4430497 := bstep (se 2 (by rfl) ⟨1661436, by rfl⟩ : syracuseStep 4430497 = 3322873) B3322873
theorem B28383965 : Blo 1748575 28383965 := bstep (se 3 (by rfl) ⟨5321993, by rfl⟩ : syracuseStep 28383965 = 10643987) B10643987
theorem B5905223 : Blo 1748575 5905223 := bstep (se 1 (by rfl) ⟨4428917, by rfl⟩ : syracuseStep 5905223 = 8857835) B8857835
theorem B9968507 : Blo 1748575 9968507 := bstep (se 1 (by rfl) ⟨7476380, by rfl⟩ : syracuseStep 9968507 = 14952761) B14952761
theorem B19930859 : Blo 1748575 19930859 := bstep (se 1 (by rfl) ⟨14948144, by rfl⟩ : syracuseStep 19930859 = 29896289) B29896289
theorem B20201309 : Blo 1748575 20201309 := bstep (se 3 (by rfl) ⟨3787745, by rfl⟩ : syracuseStep 20201309 = 7575491) B7575491
theorem B5906303 : Blo 1748575 5906303 := bstep (se 1 (by rfl) ⟨4429727, by rfl⟩ : syracuseStep 5906303 = 8859455) B8859455
theorem B4980619 : Blo 1748575 4980619 := bstep (se 1 (by rfl) ⟨3735464, by rfl⟩ : syracuseStep 4980619 = 7470929) B7470929
theorem B8094019 : Blo 1748575 8094019 := bstep (se 1 (by rfl) ⟨6070514, by rfl⟩ : syracuseStep 8094019 = 12141029) B12141029
theorem B14180987 : Blo 1748575 14180987 := bstep (se 1 (by rfl) ⟨10635740, by rfl⟩ : syracuseStep 14180987 = 21271481) B21271481
theorem B9962149 : Blo 1748575 9962149 := bstep (se 4 (by rfl) ⟨933951, by rfl⟩ : syracuseStep 9962149 = 1867903) B1867903
theorem B5907329 : Blo 1748575 5907329 := bstep (se 2 (by rfl) ⟨2215248, by rfl⟩ : syracuseStep 5907329 = 4430497) B4430497
theorem B6644713 : Blo 1748575 6644713 := bstep (se 2 (by rfl) ⟨2491767, by rfl⟩ : syracuseStep 6644713 = 4983535) B4983535
theorem B55329875 : Blo 1748575 55329875 := bstep (se 1 (by rfl) ⟨41497406, by rfl⟩ : syracuseStep 55329875 = 82994813) B82994813
theorem B53855371 : Blo 1748575 53855371 := bstep (se 1 (by rfl) ⟨40391528, by rfl⟩ : syracuseStep 53855371 = 80783057) B80783057
theorem B6645017 : Blo 1748575 6645017 := bstep (se 2 (by rfl) ⟨2491881, by rfl⟩ : syracuseStep 6645017 = 4983763) B4983763
theorem B2622887 : Blo 1748575 2622887 := bstep (se 1 (by rfl) ⟨1967165, by rfl⟩ : syracuseStep 2622887 = 3934331) B3934331
theorem B2622959 : Blo 1748575 2622959 := bstep (se 1 (by rfl) ⟨1967219, by rfl⟩ : syracuseStep 2622959 = 3934439) B3934439
theorem B51111415 : Blo 1748575 51111415 := bstep (se 1 (by rfl) ⟨38333561, by rfl⟩ : syracuseStep 51111415 = 76667123) B76667123
theorem B2623067 : Blo 1748575 2623067 := bstep (se 1 (by rfl) ⟨1967300, by rfl⟩ : syracuseStep 2623067 = 3934601) B3934601
theorem B14182127 : Blo 1748575 14182127 := bstep (se 1 (by rfl) ⟨10636595, by rfl⟩ : syracuseStep 14182127 = 21273191) B21273191
theorem B47875823 : Blo 1748575 47875823 := bstep (se 1 (by rfl) ⟨35906867, by rfl⟩ : syracuseStep 47875823 = 71813735) B71813735
theorem B6645671 : Blo 1748575 6645671 := bstep (se 1 (by rfl) ⟨4984253, by rfl⟩ : syracuseStep 6645671 = 9968507) B9968507
theorem B2951147 : Blo 1748575 2951147 := bstep (se 1 (by rfl) ⟨2213360, by rfl⟩ : syracuseStep 2951147 = 4426721) B4426721
theorem B6736171 : Blo 1748575 6736171 := bstep (se 1 (by rfl) ⟨5052128, by rfl⟩ : syracuseStep 6736171 = 10104257) B10104257
theorem B2623799 : Blo 1748575 2623799 := bstep (se 1 (by rfl) ⟨1967849, by rfl⟩ : syracuseStep 2623799 = 3935699) B3935699
theorem B2623847 : Blo 1748575 2623847 := bstep (se 1 (by rfl) ⟨1967885, by rfl⟩ : syracuseStep 2623847 = 3935771) B3935771
theorem B2623979 : Blo 1748575 2623979 := bstep (se 1 (by rfl) ⟨1967984, by rfl⟩ : syracuseStep 2623979 = 3935969) B3935969
theorem B2624111 : Blo 1748575 2624111 := bstep (se 1 (by rfl) ⟨1968083, by rfl⟩ : syracuseStep 2624111 = 3936167) B3936167
theorem B6064799 : Blo 1748575 6064799 := bstep (se 1 (by rfl) ⟨4548599, by rfl⟩ : syracuseStep 6064799 = 9097199) B9097199
theorem B2624219 : Blo 1748575 2624219 := bstep (se 1 (by rfl) ⟨1968164, by rfl⟩ : syracuseStep 2624219 = 3936329) B3936329
theorem B2624231 : Blo 1748575 2624231 := bstep (se 1 (by rfl) ⟨1968173, by rfl⟩ : syracuseStep 2624231 = 3936347) B3936347
theorem B1968871 : Blo 1748575 1968871 := bstep (se 1 (by rfl) ⟨1476653, by rfl⟩ : syracuseStep 1968871 = 2953307) B2953307
theorem B5606273 : Blo 1748575 5606273 := bstep (se 2 (by rfl) ⟨2102352, by rfl⟩ : syracuseStep 5606273 = 4204705) B4204705
theorem B5901821 : Blo 1748575 5901821 := bstep (se 3 (by rfl) ⟨1106591, by rfl⟩ : syracuseStep 5901821 = 2213183) B2213183
theorem B2625065 : Blo 1748575 2625065 := bstep (se 2 (by rfl) ⟨984399, by rfl⟩ : syracuseStep 2625065 = 1968799) B1968799
theorem B5901929 : Blo 1748575 5901929 := bstep (se 2 (by rfl) ⟨2213223, by rfl⟩ : syracuseStep 5901929 = 4426447) B4426447
theorem B1748635 : Blo 1748575 1748635 := bstep (se 1 (by rfl) ⟨1311476, by rfl⟩ : syracuseStep 1748635 = 2622953) B2622953
theorem B3321499 : Blo 1748575 3321499 := bstep (se 1 (by rfl) ⟨2491124, by rfl⟩ : syracuseStep 3321499 = 4982249) B4982249
theorem B5901983 : Blo 1748575 5901983 := bstep (se 1 (by rfl) ⟨4426487, by rfl⟩ : syracuseStep 5901983 = 8852975) B8852975
theorem B14954159 : Blo 1748575 14954159 := bstep (se 1 (by rfl) ⟨11215619, by rfl⟩ : syracuseStep 14954159 = 22431239) B22431239
theorem B1748895 : Blo 1748575 1748895 := bstep (se 1 (by rfl) ⟨1311671, by rfl⟩ : syracuseStep 1748895 = 2623343) B2623343
theorem B1749019 : Blo 1748575 1749019 := bstep (se 1 (by rfl) ⟨1311764, by rfl⟩ : syracuseStep 1749019 = 2623529) B2623529
theorem B1749039 : Blo 1748575 1749039 := bstep (se 1 (by rfl) ⟨1311779, by rfl⟩ : syracuseStep 1749039 = 2623559) B2623559
theorem B2994239 : Blo 1748575 2994239 := bstep (se 1 (by rfl) ⟨2245679, by rfl⟩ : syracuseStep 2994239 = 4491359) B4491359
theorem B11972735 : Blo 1748575 11972735 := bstep (se 1 (by rfl) ⟨8979551, by rfl⟩ : syracuseStep 11972735 = 17959103) B17959103
theorem B1749159 : Blo 1748575 1749159 := bstep (se 1 (by rfl) ⟨1311869, by rfl⟩ : syracuseStep 1749159 = 2623739) B2623739
theorem B21565649 : Blo 1748575 21565649 := bstep (se 2 (by rfl) ⟨8087118, by rfl⟩ : syracuseStep 21565649 = 16174237) B16174237
theorem B20189483 : Blo 1748575 20189483 := bstep (se 1 (by rfl) ⟨15142112, by rfl⟩ : syracuseStep 20189483 = 30284225) B30284225
theorem B1749295 : Blo 1748575 1749295 := bstep (se 1 (by rfl) ⟨1311971, by rfl⟩ : syracuseStep 1749295 = 2623943) B2623943
theorem B1749439 : Blo 1748575 1749439 := bstep (se 1 (by rfl) ⟨1312079, by rfl⟩ : syracuseStep 1749439 = 2624159) B2624159
theorem B1749471 : Blo 1748575 1749471 := bstep (se 1 (by rfl) ⟨1312103, by rfl⟩ : syracuseStep 1749471 = 2624207) B2624207
theorem B5607913 : Blo 1748575 5607913 := bstep (se 2 (by rfl) ⟨2102967, by rfl⟩ : syracuseStep 5607913 = 4205935) B4205935
theorem B1749535 : Blo 1748575 1749535 := bstep (se 1 (by rfl) ⟨1312151, by rfl⟩ : syracuseStep 1749535 = 2624303) B2624303
theorem B3936815 : Blo 1748575 3936815 := bstep (se 1 (by rfl) ⟨2952611, by rfl⟩ : syracuseStep 3936815 = 5905223) B5905223
theorem B1749615 : Blo 1748575 1749615 := bstep (se 1 (by rfl) ⟨1312211, by rfl⟩ : syracuseStep 1749615 = 2624423) B2624423
theorem B1749735 : Blo 1748575 1749735 := bstep (se 1 (by rfl) ⟨1312301, by rfl⟩ : syracuseStep 1749735 = 2624603) B2624603
theorem B1749787 : Blo 1748575 1749787 := bstep (se 1 (by rfl) ⟨1312340, by rfl⟩ : syracuseStep 1749787 = 2624681) B2624681
theorem B1750063 : Blo 1748575 1750063 := bstep (se 1 (by rfl) ⟨1312547, by rfl⟩ : syracuseStep 1750063 = 2625095) B2625095
theorem B191550581 : Blo 1748575 191550581 := bstep (se 5 (by rfl) ⟨8978933, by rfl⟩ : syracuseStep 191550581 = 17957867) B17957867
theorem B1750183 : Blo 1748575 1750183 := bstep (se 1 (by rfl) ⟨1312637, by rfl⟩ : syracuseStep 1750183 = 2625275) B2625275
theorem B6640825 : Blo 1748575 6640825 := bstep (se 2 (by rfl) ⟨2490309, by rfl⟩ : syracuseStep 6640825 = 4980619) B4980619
theorem B3937535 : Blo 1748575 3937535 := bstep (se 1 (by rfl) ⟨2953151, by rfl⟩ : syracuseStep 3937535 = 5906303) B5906303
theorem B1750343 : Blo 1748575 1750343 := bstep (se 1 (by rfl) ⟨1312757, by rfl⟩ : syracuseStep 1750343 = 2625515) B2625515
theorem B20477261 : Blo 1748575 20477261 := bstep (se 3 (by rfl) ⟨3839486, by rfl⟩ : syracuseStep 20477261 = 7678973) B7678973
theorem B13293071 : Blo 1748575 13293071 := bstep (se 1 (by rfl) ⟨9969803, by rfl⟩ : syracuseStep 13293071 = 19939607) B19939607
theorem B3937823 : Blo 1748575 3937823 := bstep (se 1 (by rfl) ⟨2953367, by rfl⟩ : syracuseStep 3937823 = 5906735) B5906735
theorem B8410679 : Blo 1748575 8410679 := bstep (se 1 (by rfl) ⟨6308009, by rfl⟩ : syracuseStep 8410679 = 12616019) B12616019
theorem B14194511 : Blo 1748575 14194511 := bstep (se 1 (by rfl) ⟨10645883, by rfl⟩ : syracuseStep 14194511 = 21291767) B21291767
theorem B9967799 : Blo 1748575 9967799 := bstep (se 1 (by rfl) ⟨7475849, by rfl⟩ : syracuseStep 9967799 = 14951699) B14951699
theorem B5904575 : Blo 1748575 5904575 := bstep (se 1 (by rfl) ⟨4428431, by rfl⟩ : syracuseStep 5904575 = 8856863) B8856863
theorem B5904737 : Blo 1748575 5904737 := bstep (se 2 (by rfl) ⟨2214276, by rfl⟩ : syracuseStep 5904737 = 4428553) B4428553
theorem B43145581 : Blo 1748575 43145581 := bstep (se 3 (by rfl) ⟨8089796, by rfl⟩ : syracuseStep 43145581 = 16179593) B16179593
theorem B9967981 : Blo 1748575 9967981 := bstep (se 3 (by rfl) ⟨1868996, by rfl⟩ : syracuseStep 9967981 = 3737993) B3737993
theorem B8862209 : Blo 1748575 8862209 := bstep (se 2 (by rfl) ⟨3323328, by rfl⟩ : syracuseStep 8862209 = 6646657) B6646657
theorem B4430639 : Blo 1748575 4430639 := bstep (se 1 (by rfl) ⟨3322979, by rfl⟩ : syracuseStep 4430639 = 6645959) B6645959
theorem B73776221 : Blo 1748575 73776221 := bstep (se 3 (by rfl) ⟨13833041, by rfl⟩ : syracuseStep 73776221 = 27666083) B27666083
theorem B18922643 : Blo 1748575 18922643 := bstep (se 1 (by rfl) ⟨14191982, by rfl⟩ : syracuseStep 18922643 = 28383965) B28383965
theorem B3366139 : Blo 1748575 3366139 := bstep (se 1 (by rfl) ⟨2524604, by rfl⟩ : syracuseStep 3366139 = 5049209) B5049209
theorem B5987657 : Blo 1748575 5987657 := bstep (se 2 (by rfl) ⟨2245371, by rfl⟩ : syracuseStep 5987657 = 4490743) B4490743
theorem B36904319 : Blo 1748575 36904319 := bstep (se 1 (by rfl) ⟨27678239, by rfl⟩ : syracuseStep 36904319 = 55356479) B55356479
theorem B14949785 : Blo 1748575 14949785 := bstep (se 2 (by rfl) ⟨5606169, by rfl⟩ : syracuseStep 14949785 = 11212339) B11212339
theorem B5905871 : Blo 1748575 5905871 := bstep (se 1 (by rfl) ⟨4429403, by rfl⟩ : syracuseStep 5905871 = 8858807) B8858807
theorem B13287239 : Blo 1748575 13287239 := bstep (se 1 (by rfl) ⟨9965429, by rfl⟩ : syracuseStep 13287239 = 19930859) B19930859
theorem B1105420121 : Blo 1748575 1105420121 := bstep (se 2 (by rfl) ⟨414532545, by rfl⟩ : syracuseStep 1105420121 = 829065091) B829065091
theorem B13467539 : Blo 1748575 13467539 := bstep (se 1 (by rfl) ⟨10100654, by rfl⟩ : syracuseStep 13467539 = 20201309) B20201309
theorem B14377099 : Blo 1748575 14377099 := bstep (se 1 (by rfl) ⟨10782824, by rfl⟩ : syracuseStep 14377099 = 21565649) B21565649
theorem B13459655 : Blo 1748575 13459655 := bstep (se 1 (by rfl) ⟨10094741, by rfl⟩ : syracuseStep 13459655 = 20189483) B20189483
theorem B9453991 : Blo 1748575 9453991 := bstep (se 1 (by rfl) ⟨7090493, by rfl⟩ : syracuseStep 9453991 = 14180987) B14180987
theorem B9454751 : Blo 1748575 9454751 := bstep (se 1 (by rfl) ⟨7091063, by rfl⟩ : syracuseStep 9454751 = 14182127) B14182127
theorem B31917215 : Blo 1748575 31917215 := bstep (se 1 (by rfl) ⟨23937911, by rfl⟩ : syracuseStep 31917215 = 47875823) B47875823
theorem B9463007 : Blo 1748575 9463007 := bstep (se 1 (by rfl) ⟨7097255, by rfl⟩ : syracuseStep 9463007 = 14194511) B14194511
theorem B1967431 : Blo 1748575 1967431 := bstep (se 1 (by rfl) ⟨1475573, by rfl⟩ : syracuseStep 1967431 = 2951147) B2951147
theorem B6645199 : Blo 1748575 6645199 := bstep (se 1 (by rfl) ⟨4983899, by rfl⟩ : syracuseStep 6645199 = 9967799) B9967799
theorem B5908139 : Blo 1748575 5908139 := bstep (se 1 (by rfl) ⟨4431104, by rfl⟩ : syracuseStep 5908139 = 8862209) B8862209
theorem B16172797 : Blo 1748575 16172797 := bstep (se 3 (by rfl) ⟨3032399, by rfl⟩ : syracuseStep 16172797 = 6064799) B6064799
theorem B3737515 : Blo 1748575 3737515 := bstep (se 1 (by rfl) ⟨2803136, by rfl⟩ : syracuseStep 3737515 = 5606273) B5606273
theorem B3991771 : Blo 1748575 3991771 := bstep (se 1 (by rfl) ⟨2993828, by rfl⟩ : syracuseStep 3991771 = 5987657) B5987657
theorem B24602879 : Blo 1748575 24602879 := bstep (se 1 (by rfl) ⟨18452159, by rfl⟩ : syracuseStep 24602879 = 36904319) B36904319
theorem B3934547 : Blo 1748575 3934547 := bstep (se 1 (by rfl) ⟨2950910, by rfl⟩ : syracuseStep 3934547 = 5901821) B5901821
theorem B3934619 : Blo 1748575 3934619 := bstep (se 1 (by rfl) ⟨2950964, by rfl⟩ : syracuseStep 3934619 = 5901929) B5901929
theorem B3934655 : Blo 1748575 3934655 := bstep (se 1 (by rfl) ⟨2950991, by rfl⟩ : syracuseStep 3934655 = 5901983) B5901983
theorem B8858159 : Blo 1748575 8858159 := bstep (se 1 (by rfl) ⟨6643619, by rfl⟩ : syracuseStep 8858159 = 13287239) B13287239
theorem B736946747 : Blo 1748575 736946747 := bstep (se 1 (by rfl) ⟨552710060, by rfl⟩ : syracuseStep 736946747 = 1105420121) B1105420121
theorem B7981823 : Blo 1748575 7981823 := bstep (se 1 (by rfl) ⟨5986367, by rfl⟩ : syracuseStep 7981823 = 11972735) B11972735
theorem B2624543 : Blo 1748575 2624543 := bstep (se 1 (by rfl) ⟨1968407, by rfl⟩ : syracuseStep 2624543 = 3936815) B3936815
theorem B8981561 : Blo 1748575 8981561 := bstep (se 2 (by rfl) ⟨3368085, by rfl⟩ : syracuseStep 8981561 = 6736171) B6736171
theorem B10792025 : Blo 1748575 10792025 := bstep (se 2 (by rfl) ⟨4047009, by rfl⟩ : syracuseStep 10792025 = 8094019) B8094019
theorem B57527441 : Blo 1748575 57527441 := bstep (se 2 (by rfl) ⟨21572790, by rfl⟩ : syracuseStep 57527441 = 43145581) B43145581
theorem B13290641 : Blo 1748575 13290641 := bstep (se 2 (by rfl) ⟨4983990, by rfl⟩ : syracuseStep 13290641 = 9967981) B9967981
theorem B127700387 : Blo 1748575 127700387 := bstep (se 1 (by rfl) ⟨95775290, by rfl⟩ : syracuseStep 127700387 = 191550581) B191550581
theorem B2625023 : Blo 1748575 2625023 := bstep (se 1 (by rfl) ⟨1968767, by rfl⟩ : syracuseStep 2625023 = 3937535) B3937535
theorem B13282865 : Blo 1748575 13282865 := bstep (se 2 (by rfl) ⟨4981074, by rfl⟩ : syracuseStep 13282865 = 9962149) B9962149
theorem B13651507 : Blo 1748575 13651507 := bstep (se 1 (by rfl) ⟨10238630, by rfl⟩ : syracuseStep 13651507 = 20477261) B20477261
theorem B1748591 : Blo 1748575 1748591 := bstep (se 1 (by rfl) ⟨1311443, by rfl⟩ : syracuseStep 1748591 = 2622887) B2622887
theorem B2625161 : Blo 1748575 2625161 := bstep (se 2 (by rfl) ⟨984435, by rfl⟩ : syracuseStep 2625161 = 1968871) B1968871
theorem B1748639 : Blo 1748575 1748639 := bstep (se 1 (by rfl) ⟨1311479, by rfl⟩ : syracuseStep 1748639 = 2622959) B2622959
theorem B2625215 : Blo 1748575 2625215 := bstep (se 1 (by rfl) ⟨1968911, by rfl⟩ : syracuseStep 2625215 = 3937823) B3937823
theorem B5607119 : Blo 1748575 5607119 := bstep (se 1 (by rfl) ⟨4205339, by rfl⟩ : syracuseStep 5607119 = 8410679) B8410679
theorem B1748711 : Blo 1748575 1748711 := bstep (se 1 (by rfl) ⟨1311533, by rfl⟩ : syracuseStep 1748711 = 2623067) B2623067
theorem B8859617 : Blo 1748575 8859617 := bstep (se 2 (by rfl) ⟨3322356, by rfl⟩ : syracuseStep 8859617 = 6644713) B6644713
theorem B3936383 : Blo 1748575 3936383 := bstep (se 1 (by rfl) ⟨2952287, by rfl⟩ : syracuseStep 3936383 = 5904575) B5904575
theorem B71807161 : Blo 1748575 71807161 := bstep (se 2 (by rfl) ⟨26927685, by rfl⟩ : syracuseStep 71807161 = 53855371) B53855371
theorem B1749199 : Blo 1748575 1749199 := bstep (se 1 (by rfl) ⟨1311899, by rfl⟩ : syracuseStep 1749199 = 2623799) B2623799
theorem B3936491 : Blo 1748575 3936491 := bstep (se 1 (by rfl) ⟨2952368, by rfl⟩ : syracuseStep 3936491 = 5904737) B5904737
theorem B1749231 : Blo 1748575 1749231 := bstep (se 1 (by rfl) ⟨1311923, by rfl⟩ : syracuseStep 1749231 = 2623847) B2623847
theorem B1749319 : Blo 1748575 1749319 := bstep (se 1 (by rfl) ⟨1311989, by rfl⟩ : syracuseStep 1749319 = 2623979) B2623979
theorem B1749407 : Blo 1748575 1749407 := bstep (se 1 (by rfl) ⟨1312055, by rfl⟩ : syracuseStep 1749407 = 2624111) B2624111
theorem B1749479 : Blo 1748575 1749479 := bstep (se 1 (by rfl) ⟨1312109, by rfl⟩ : syracuseStep 1749479 = 2624219) B2624219
theorem B1749487 : Blo 1748575 1749487 := bstep (se 1 (by rfl) ⟨1312115, by rfl⟩ : syracuseStep 1749487 = 2624231) B2624231
theorem B2953759 : Blo 1748575 2953759 := bstep (se 1 (by rfl) ⟨2215319, by rfl⟩ : syracuseStep 2953759 = 4430639) B4430639
theorem B4428665 : Blo 1748575 4428665 := bstep (se 2 (by rfl) ⟨1660749, by rfl⟩ : syracuseStep 4428665 = 3321499) B3321499
theorem B9966523 : Blo 1748575 9966523 := bstep (se 1 (by rfl) ⟨7474892, by rfl⟩ : syracuseStep 9966523 = 14949785) B14949785
theorem B3937247 : Blo 1748575 3937247 := bstep (se 1 (by rfl) ⟨2952935, by rfl⟩ : syracuseStep 3937247 = 5905871) B5905871
theorem B1750043 : Blo 1748575 1750043 := bstep (se 1 (by rfl) ⟨1312532, by rfl⟩ : syracuseStep 1750043 = 2625065) B2625065
theorem B1996159 : Blo 1748575 1996159 := bstep (se 1 (by rfl) ⟨1497119, by rfl⟩ : syracuseStep 1996159 = 2994239) B2994239
theorem B3938219 : Blo 1748575 3938219 := bstep (se 1 (by rfl) ⟨2953664, by rfl⟩ : syracuseStep 3938219 = 5907329) B5907329
theorem B7477217 : Blo 1748575 7477217 := bstep (se 2 (by rfl) ⟨2803956, by rfl⟩ : syracuseStep 7477217 = 5607913) B5607913
theorem B36886583 : Blo 1748575 36886583 := bstep (se 1 (by rfl) ⟨27664937, by rfl⟩ : syracuseStep 36886583 = 55329875) B55329875
theorem B4430011 : Blo 1748575 4430011 := bstep (se 1 (by rfl) ⟨3322508, by rfl⟩ : syracuseStep 4430011 = 6645017) B6645017
theorem B786946357 : Blo 1748575 786946357 := bstep (se 5 (by rfl) ⟨36888110, by rfl⟩ : syracuseStep 786946357 = 73776221) B73776221
theorem B8862047 : Blo 1748575 8862047 := bstep (se 1 (by rfl) ⟨6646535, by rfl⟩ : syracuseStep 8862047 = 13293071) B13293071
theorem B4430447 : Blo 1748575 4430447 := bstep (se 1 (by rfl) ⟨3322835, by rfl⟩ : syracuseStep 4430447 = 6645671) B6645671
theorem B8854433 : Blo 1748575 8854433 := bstep (se 2 (by rfl) ⟨3320412, by rfl⟩ : syracuseStep 8854433 = 6640825) B6640825
theorem B68148553 : Blo 1748575 68148553 := bstep (se 2 (by rfl) ⟨25555707, by rfl⟩ : syracuseStep 68148553 = 51111415) B51111415
theorem B12615095 : Blo 1748575 12615095 := bstep (se 1 (by rfl) ⟨9461321, by rfl⟩ : syracuseStep 12615095 = 18922643) B18922643
theorem B9969439 : Blo 1748575 9969439 := bstep (se 1 (by rfl) ⟨7477079, by rfl⟩ : syracuseStep 9969439 = 14954159) B14954159
theorem B71810965 : Blo 1748575 71810965 := bstep (se 6 (by rfl) ⟨1683069, by rfl⟩ : syracuseStep 71810965 = 3366139) B3366139
theorem B8978359 : Blo 1748575 8978359 := bstep (se 1 (by rfl) ⟨6733769, by rfl⟩ : syracuseStep 8978359 = 13467539) B13467539
theorem B19169465 : Blo 1748575 19169465 := bstep (se 2 (by rfl) ⟨7188549, by rfl⟩ : syracuseStep 19169465 = 14377099) B14377099
theorem B5906681 : Blo 1748575 5906681 := bstep (se 2 (by rfl) ⟨2215005, by rfl⟩ : syracuseStep 5906681 = 4430011) B4430011
theorem B13288697 : Blo 1748575 13288697 := bstep (se 2 (by rfl) ⟨4983261, by rfl⟩ : syracuseStep 13288697 = 9966523) B9966523
theorem B2623031 : Blo 1748575 2623031 := bstep (se 1 (by rfl) ⟨1967273, by rfl⟩ : syracuseStep 2623031 = 3934547) B3934547
theorem B5908031 : Blo 1748575 5908031 := bstep (se 1 (by rfl) ⟨4431023, by rfl⟩ : syracuseStep 5908031 = 8862047) B8862047
theorem B2623079 : Blo 1748575 2623079 := bstep (se 1 (by rfl) ⟨1967309, by rfl⟩ : syracuseStep 2623079 = 3934619) B3934619
theorem B2623103 : Blo 1748575 2623103 := bstep (se 1 (by rfl) ⟨1967327, by rfl⟩ : syracuseStep 2623103 = 3934655) B3934655
theorem B2623241 : Blo 1748575 2623241 := bstep (se 2 (by rfl) ⟨983715, by rfl⟩ : syracuseStep 2623241 = 1967431) B1967431
theorem B7194683 : Blo 1748575 7194683 := bstep (se 1 (by rfl) ⟨5396012, by rfl⟩ : syracuseStep 7194683 = 10792025) B10792025
theorem B85133591 : Blo 1748575 85133591 := bstep (se 1 (by rfl) ⟨63850193, by rfl⟩ : syracuseStep 85133591 = 127700387) B127700387
theorem B21563729 : Blo 1748575 21563729 := bstep (se 2 (by rfl) ⟨8086398, by rfl⟩ : syracuseStep 21563729 = 16172797) B16172797
theorem B3738079 : Blo 1748575 3738079 := bstep (se 1 (by rfl) ⟨2803559, by rfl⟩ : syracuseStep 3738079 = 5607119) B5607119
theorem B4983353 : Blo 1748575 4983353 := bstep (se 2 (by rfl) ⟨1868757, by rfl⟩ : syracuseStep 4983353 = 3737515) B3737515
theorem B11971145 : Blo 1748575 11971145 := bstep (se 2 (by rfl) ⟨4489179, by rfl⟩ : syracuseStep 11971145 = 8978359) B8978359
theorem B2624255 : Blo 1748575 2624255 := bstep (se 1 (by rfl) ⟨1968191, by rfl⟩ : syracuseStep 2624255 = 3936383) B3936383
theorem B2624327 : Blo 1748575 2624327 := bstep (se 1 (by rfl) ⟨1968245, by rfl⟩ : syracuseStep 2624327 = 3936491) B3936491
theorem B95742881 : Blo 1748575 95742881 := bstep (se 2 (by rfl) ⟨35903580, by rfl⟩ : syracuseStep 95742881 = 71807161) B71807161
theorem B35892413 : Blo 1748575 35892413 := bstep (se 3 (by rfl) ⟨6729827, by rfl⟩ : syracuseStep 35892413 = 13459655) B13459655
theorem B2952443 : Blo 1748575 2952443 := bstep (se 1 (by rfl) ⟨2214332, by rfl⟩ : syracuseStep 2952443 = 4428665) B4428665
theorem B25234685 : Blo 1748575 25234685 := bstep (se 3 (by rfl) ⟨4731503, by rfl⟩ : syracuseStep 25234685 = 9463007) B9463007
theorem B2624831 : Blo 1748575 2624831 := bstep (se 1 (by rfl) ⟨1968623, by rfl⟩ : syracuseStep 2624831 = 3937247) B3937247
theorem B6303167 : Blo 1748575 6303167 := bstep (se 1 (by rfl) ⟨4727375, by rfl⟩ : syracuseStep 6303167 = 9454751) B9454751
theorem B21278143 : Blo 1748575 21278143 := bstep (se 1 (by rfl) ⟨15958607, by rfl⟩ : syracuseStep 21278143 = 31917215) B31917215
theorem B2625479 : Blo 1748575 2625479 := bstep (se 1 (by rfl) ⟨1969109, by rfl⟩ : syracuseStep 2625479 = 3938219) B3938219
theorem B4984811 : Blo 1748575 4984811 := bstep (se 1 (by rfl) ⟨3738608, by rfl⟩ : syracuseStep 4984811 = 7477217) B7477217
theorem B2953631 : Blo 1748575 2953631 := bstep (se 1 (by rfl) ⟨2215223, by rfl⟩ : syracuseStep 2953631 = 4430447) B4430447
theorem B5321215 : Blo 1748575 5321215 := bstep (se 1 (by rfl) ⟨3990911, by rfl⟩ : syracuseStep 5321215 = 7981823) B7981823
theorem B8860265 : Blo 1748575 8860265 := bstep (se 2 (by rfl) ⟨3322599, by rfl⟩ : syracuseStep 8860265 = 6645199) B6645199
theorem B5902955 : Blo 1748575 5902955 := bstep (se 1 (by rfl) ⟨4427216, by rfl⟩ : syracuseStep 5902955 = 8854433) B8854433
theorem B1749695 : Blo 1748575 1749695 := bstep (se 1 (by rfl) ⟨1312271, by rfl⟩ : syracuseStep 1749695 = 2624543) B2624543
theorem B38351627 : Blo 1748575 38351627 := bstep (se 1 (by rfl) ⟨28763720, by rfl⟩ : syracuseStep 38351627 = 57527441) B57527441
theorem B8860427 : Blo 1748575 8860427 := bstep (se 1 (by rfl) ⟨6645320, by rfl⟩ : syracuseStep 8860427 = 13290641) B13290641
theorem B8410063 : Blo 1748575 8410063 := bstep (se 1 (by rfl) ⟨6307547, by rfl⟩ : syracuseStep 8410063 = 12615095) B12615095
theorem B1750015 : Blo 1748575 1750015 := bstep (se 1 (by rfl) ⟨1312511, by rfl⟩ : syracuseStep 1750015 = 2625023) B2625023
theorem B13292585 : Blo 1748575 13292585 := bstep (se 2 (by rfl) ⟨4984719, by rfl⟩ : syracuseStep 13292585 = 9969439) B9969439
theorem B1750107 : Blo 1748575 1750107 := bstep (se 1 (by rfl) ⟨1312580, by rfl⟩ : syracuseStep 1750107 = 2625161) B2625161
theorem B1750143 : Blo 1748575 1750143 := bstep (se 1 (by rfl) ⟨1312607, by rfl⟩ : syracuseStep 1750143 = 2625215) B2625215
theorem B5322361 : Blo 1748575 5322361 := bstep (se 2 (by rfl) ⟨1995885, by rfl⟩ : syracuseStep 5322361 = 3991771) B3991771
theorem B1049261809 : Blo 1748575 1049261809 := bstep (se 2 (by rfl) ⟨393473178, by rfl⟩ : syracuseStep 1049261809 = 786946357) B786946357
theorem B12605321 : Blo 1748575 12605321 := bstep (se 2 (by rfl) ⟨4726995, by rfl⟩ : syracuseStep 12605321 = 9453991) B9453991
theorem B65607677 : Blo 1748575 65607677 := bstep (se 3 (by rfl) ⟨12301439, by rfl⟩ : syracuseStep 65607677 = 24602879) B24602879
theorem B3938345 : Blo 1748575 3938345 := bstep (se 2 (by rfl) ⟨1476879, by rfl⟩ : syracuseStep 3938345 = 2953759) B2953759
theorem B3938759 : Blo 1748575 3938759 := bstep (se 1 (by rfl) ⟨2954069, by rfl⟩ : syracuseStep 3938759 = 5908139) B5908139
theorem B24591055 : Blo 1748575 24591055 := bstep (se 1 (by rfl) ⟨18443291, by rfl⟩ : syracuseStep 24591055 = 36886583) B36886583
theorem B5905439 : Blo 1748575 5905439 := bstep (se 1 (by rfl) ⟨4429079, by rfl⟩ : syracuseStep 5905439 = 8858159) B8858159
theorem B491297831 : Blo 1748575 491297831 := bstep (se 1 (by rfl) ⟨368473373, by rfl⟩ : syracuseStep 491297831 = 736946747) B736946747
theorem B90864737 : Blo 1748575 90864737 := bstep (se 2 (by rfl) ⟨34074276, by rfl⟩ : syracuseStep 90864737 = 68148553) B68148553
theorem B2661545 : Blo 1748575 2661545 := bstep (se 2 (by rfl) ⟨998079, by rfl⟩ : syracuseStep 2661545 = 1996159) B1996159
theorem B5987707 : Blo 1748575 5987707 := bstep (se 1 (by rfl) ⟨4490780, by rfl⟩ : syracuseStep 5987707 = 8981561) B8981561
theorem B18202009 : Blo 1748575 18202009 := bstep (se 2 (by rfl) ⟨6825753, by rfl⟩ : syracuseStep 18202009 = 13651507) B13651507
theorem B8855243 : Blo 1748575 8855243 := bstep (se 1 (by rfl) ⟨6641432, by rfl⟩ : syracuseStep 8855243 = 13282865) B13282865
theorem B95747953 : Blo 1748575 95747953 := bstep (se 2 (by rfl) ⟨35905482, by rfl⟩ : syracuseStep 95747953 = 71810965) B71810965
theorem B5906411 : Blo 1748575 5906411 := bstep (se 1 (by rfl) ⟨4429808, by rfl⟩ : syracuseStep 5906411 = 8859617) B8859617
theorem B5906843 : Blo 1748575 5906843 := bstep (se 1 (by rfl) ⟨4430132, by rfl⟩ : syracuseStep 5906843 = 8860265) B8860265
theorem B51118573 : Blo 1748575 51118573 := bstep (se 3 (by rfl) ⟨9584732, by rfl⟩ : syracuseStep 51118573 = 19169465) B19169465
theorem B25567751 : Blo 1748575 25567751 := bstep (se 1 (by rfl) ⟨19175813, by rfl⟩ : syracuseStep 25567751 = 38351627) B38351627
theorem B5906951 : Blo 1748575 5906951 := bstep (se 1 (by rfl) ⟨4430213, by rfl⟩ : syracuseStep 5906951 = 8860427) B8860427
theorem B7094953 : Blo 1748575 7094953 := bstep (se 2 (by rfl) ⟨2660607, by rfl⟩ : syracuseStep 7094953 = 5321215) B5321215
theorem B43738451 : Blo 1748575 43738451 := bstep (se 1 (by rfl) ⟨32803838, by rfl⟩ : syracuseStep 43738451 = 65607677) B65607677
theorem B56755727 : Blo 1748575 56755727 := bstep (se 1 (by rfl) ⟨42566795, by rfl⟩ : syracuseStep 56755727 = 85133591) B85133591
theorem B7980763 : Blo 1748575 7980763 := bstep (se 1 (by rfl) ⟨5985572, by rfl⟩ : syracuseStep 7980763 = 11971145) B11971145
theorem B28370857 : Blo 1748575 28370857 := bstep (se 2 (by rfl) ⟨10639071, by rfl⟩ : syracuseStep 28370857 = 21278143) B21278143
theorem B7096481 : Blo 1748575 7096481 := bstep (se 2 (by rfl) ⟨2661180, by rfl⟩ : syracuseStep 7096481 = 5322361) B5322361
theorem B1968295 : Blo 1748575 1968295 := bstep (se 1 (by rfl) ⟨1476221, by rfl⟩ : syracuseStep 1968295 = 2952443) B2952443
theorem B1399015745 : Blo 1748575 1399015745 := bstep (se 2 (by rfl) ⟨524630904, by rfl⟩ : syracuseStep 1399015745 = 1049261809) B1049261809
theorem B33614189 : Blo 1748575 33614189 := bstep (se 3 (by rfl) ⟨6302660, by rfl⟩ : syracuseStep 33614189 = 12605321) B12605321
theorem B1969087 : Blo 1748575 1969087 := bstep (se 1 (by rfl) ⟨1476815, by rfl⟩ : syracuseStep 1969087 = 2953631) B2953631
theorem B3935303 : Blo 1748575 3935303 := bstep (se 1 (by rfl) ⟨2951477, by rfl⟩ : syracuseStep 3935303 = 5902955) B5902955
theorem B7097453 : Blo 1748575 7097453 := bstep (se 3 (by rfl) ⟨1330772, by rfl⟩ : syracuseStep 7097453 = 2661545) B2661545
theorem B4984105 : Blo 1748575 4984105 := bstep (se 2 (by rfl) ⟨1869039, by rfl⟩ : syracuseStep 4984105 = 3738079) B3738079
theorem B8859131 : Blo 1748575 8859131 := bstep (se 1 (by rfl) ⟨6644348, by rfl⟩ : syracuseStep 8859131 = 13288697) B13288697
theorem B32788073 : Blo 1748575 32788073 := bstep (se 2 (by rfl) ⟨12295527, by rfl⟩ : syracuseStep 32788073 = 24591055) B24591055
theorem B1748687 : Blo 1748575 1748687 := bstep (se 1 (by rfl) ⟨1311515, by rfl⟩ : syracuseStep 1748687 = 2623031) B2623031
theorem B1748719 : Blo 1748575 1748719 := bstep (se 1 (by rfl) ⟨1311539, by rfl⟩ : syracuseStep 1748719 = 2623079) B2623079
theorem B1748735 : Blo 1748575 1748735 := bstep (se 1 (by rfl) ⟨1311551, by rfl⟩ : syracuseStep 1748735 = 2623103) B2623103
theorem B1748827 : Blo 1748575 1748827 := bstep (se 1 (by rfl) ⟨1311620, by rfl⟩ : syracuseStep 1748827 = 2623241) B2623241
theorem B2625563 : Blo 1748575 2625563 := bstep (se 1 (by rfl) ⟨1969172, by rfl⟩ : syracuseStep 2625563 = 3938345) B3938345
theorem B4796455 : Blo 1748575 4796455 := bstep (se 1 (by rfl) ⟨3597341, by rfl⟩ : syracuseStep 4796455 = 7194683) B7194683
theorem B2625839 : Blo 1748575 2625839 := bstep (se 1 (by rfl) ⟨1969379, by rfl⟩ : syracuseStep 2625839 = 3938759) B3938759
theorem B3322235 : Blo 1748575 3322235 := bstep (se 1 (by rfl) ⟨2491676, by rfl⟩ : syracuseStep 3322235 = 4983353) B4983353
theorem B1749503 : Blo 1748575 1749503 := bstep (se 1 (by rfl) ⟨1312127, by rfl⟩ : syracuseStep 1749503 = 2624255) B2624255
theorem B24269345 : Blo 1748575 24269345 := bstep (se 2 (by rfl) ⟨9101004, by rfl⟩ : syracuseStep 24269345 = 18202009) B18202009
theorem B1749551 : Blo 1748575 1749551 := bstep (se 1 (by rfl) ⟨1312163, by rfl⟩ : syracuseStep 1749551 = 2624327) B2624327
theorem B63828587 : Blo 1748575 63828587 := bstep (se 1 (by rfl) ⟨47871440, by rfl⟩ : syracuseStep 63828587 = 95742881) B95742881
theorem B3936959 : Blo 1748575 3936959 := bstep (se 1 (by rfl) ⟨2952719, by rfl⟩ : syracuseStep 3936959 = 5905439) B5905439
theorem B60576491 : Blo 1748575 60576491 := bstep (se 1 (by rfl) ⟨45432368, by rfl⟩ : syracuseStep 60576491 = 90864737) B90864737
theorem B16823123 : Blo 1748575 16823123 := bstep (se 1 (by rfl) ⟨12617342, by rfl⟩ : syracuseStep 16823123 = 25234685) B25234685
theorem B1749887 : Blo 1748575 1749887 := bstep (se 1 (by rfl) ⟨1312415, by rfl⟩ : syracuseStep 1749887 = 2624831) B2624831
theorem B5903495 : Blo 1748575 5903495 := bstep (se 1 (by rfl) ⟨4427621, by rfl⟩ : syracuseStep 5903495 = 8855243) B8855243
theorem B1750319 : Blo 1748575 1750319 := bstep (se 1 (by rfl) ⟨1312739, by rfl⟩ : syracuseStep 1750319 = 2625479) B2625479
theorem B3937607 : Blo 1748575 3937607 := bstep (se 1 (by rfl) ⟨2953205, by rfl⟩ : syracuseStep 3937607 = 5906411) B5906411
theorem B3323207 : Blo 1748575 3323207 := bstep (se 1 (by rfl) ⟨2492405, by rfl⟩ : syracuseStep 3323207 = 4984811) B4984811
theorem B3937787 : Blo 1748575 3937787 := bstep (se 1 (by rfl) ⟨2953340, by rfl⟩ : syracuseStep 3937787 = 5906681) B5906681
theorem B8861723 : Blo 1748575 8861723 := bstep (se 1 (by rfl) ⟨6646292, by rfl⟩ : syracuseStep 8861723 = 13292585) B13292585
theorem B3938687 : Blo 1748575 3938687 := bstep (se 1 (by rfl) ⟨2954015, by rfl⟩ : syracuseStep 3938687 = 5908031) B5908031
theorem B11213417 : Blo 1748575 11213417 := bstep (se 2 (by rfl) ⟨4205031, by rfl⟩ : syracuseStep 11213417 = 8410063) B8410063
theorem B14375819 : Blo 1748575 14375819 := bstep (se 1 (by rfl) ⟨10781864, by rfl⟩ : syracuseStep 14375819 = 21563729) B21563729
theorem B327531887 : Blo 1748575 327531887 := bstep (se 1 (by rfl) ⟨245648915, by rfl⟩ : syracuseStep 327531887 = 491297831) B491297831
theorem B23928275 : Blo 1748575 23928275 := bstep (se 1 (by rfl) ⟨17946206, by rfl⟩ : syracuseStep 23928275 = 35892413) B35892413
theorem B4202111 : Blo 1748575 4202111 := bstep (se 1 (by rfl) ⟨3151583, by rfl⟩ : syracuseStep 4202111 = 6303167) B6303167
theorem B127663937 : Blo 1748575 127663937 := bstep (se 2 (by rfl) ⟨47873976, by rfl⟩ : syracuseStep 127663937 = 95747953) B95747953
theorem B127737749 : Blo 1748575 127737749 := bstep (se 6 (by rfl) ⟨2993853, by rfl⟩ : syracuseStep 127737749 = 5987707) B5987707
theorem B16179563 : Blo 1748575 16179563 := bstep (se 1 (by rfl) ⟨12134672, by rfl⟩ : syracuseStep 16179563 = 24269345) B24269345
theorem B11215415 : Blo 1748575 11215415 := bstep (se 1 (by rfl) ⟨8411561, by rfl⟩ : syracuseStep 11215415 = 16823123) B16823123
theorem B68158097 : Blo 1748575 68158097 := bstep (se 2 (by rfl) ⟨25559286, by rfl⟩ : syracuseStep 68158097 = 51118573) B51118573
theorem B5907815 : Blo 1748575 5907815 := bstep (se 1 (by rfl) ⟨4430861, by rfl⟩ : syracuseStep 5907815 = 8861723) B8861723
theorem B932677163 : Blo 1748575 932677163 := bstep (se 1 (by rfl) ⟨699507872, by rfl⟩ : syracuseStep 932677163 = 1399015745) B1399015745
theorem B6645473 : Blo 1748575 6645473 := bstep (se 2 (by rfl) ⟨2492052, by rfl⟩ : syracuseStep 6645473 = 4984105) B4984105
theorem B2623535 : Blo 1748575 2623535 := bstep (se 1 (by rfl) ⟨1967651, by rfl⟩ : syracuseStep 2623535 = 3935303) B3935303
theorem B15952183 : Blo 1748575 15952183 := bstep (se 1 (by rfl) ⟨11964137, by rfl⟩ : syracuseStep 15952183 = 23928275) B23928275
theorem B21858715 : Blo 1748575 21858715 := bstep (se 1 (by rfl) ⟨16394036, by rfl⟩ : syracuseStep 21858715 = 32788073) B32788073
theorem B85109291 : Blo 1748575 85109291 := bstep (se 1 (by rfl) ⟨63831968, by rfl⟩ : syracuseStep 85109291 = 127663937) B127663937
theorem B85158499 : Blo 1748575 85158499 := bstep (se 1 (by rfl) ⟨63868874, by rfl⟩ : syracuseStep 85158499 = 127737749) B127737749
theorem B2624393 : Blo 1748575 2624393 := bstep (se 2 (by rfl) ⟨984147, by rfl⟩ : syracuseStep 2624393 = 1968295) B1968295
theorem B42552391 : Blo 1748575 42552391 := bstep (se 1 (by rfl) ⟨31914293, by rfl⟩ : syracuseStep 42552391 = 63828587) B63828587
theorem B2624639 : Blo 1748575 2624639 := bstep (se 1 (by rfl) ⟨1968479, by rfl⟩ : syracuseStep 2624639 = 3936959) B3936959
theorem B3935663 : Blo 1748575 3935663 := bstep (se 1 (by rfl) ⟨2951747, by rfl⟩ : syracuseStep 3935663 = 5903495) B5903495
theorem B2625071 : Blo 1748575 2625071 := bstep (se 1 (by rfl) ⟨1968803, by rfl⟩ : syracuseStep 2625071 = 3937607) B3937607
theorem B29158967 : Blo 1748575 29158967 := bstep (se 1 (by rfl) ⟨21869225, by rfl⟩ : syracuseStep 29158967 = 43738451) B43738451
theorem B8859293 : Blo 1748575 8859293 := bstep (se 3 (by rfl) ⟨1661117, by rfl⟩ : syracuseStep 8859293 = 3322235) B3322235
theorem B2625191 : Blo 1748575 2625191 := bstep (se 1 (by rfl) ⟨1968893, by rfl⟩ : syracuseStep 2625191 = 3937787) B3937787
theorem B2625449 : Blo 1748575 2625449 := bstep (se 2 (by rfl) ⟨984543, by rfl⟩ : syracuseStep 2625449 = 1969087) B1969087
theorem B4730987 : Blo 1748575 4730987 := bstep (se 1 (by rfl) ⟨3548240, by rfl⟩ : syracuseStep 4730987 = 7096481) B7096481
theorem B22409459 : Blo 1748575 22409459 := bstep (se 1 (by rfl) ⟨16807094, by rfl⟩ : syracuseStep 22409459 = 33614189) B33614189
theorem B2625791 : Blo 1748575 2625791 := bstep (se 1 (by rfl) ⟨1969343, by rfl⟩ : syracuseStep 2625791 = 3938687) B3938687
theorem B7475611 : Blo 1748575 7475611 := bstep (se 1 (by rfl) ⟨5606708, by rfl⟩ : syracuseStep 7475611 = 11213417) B11213417
theorem B4731635 : Blo 1748575 4731635 := bstep (se 1 (by rfl) ⟨3548726, by rfl⟩ : syracuseStep 4731635 = 7097453) B7097453
theorem B218354591 : Blo 1748575 218354591 := bstep (se 1 (by rfl) ⟨163765943, by rfl⟩ : syracuseStep 218354591 = 327531887) B327531887
theorem B37827809 : Blo 1748575 37827809 := bstep (se 2 (by rfl) ⟨14185428, by rfl⟩ : syracuseStep 37827809 = 28370857) B28370857
theorem B1750375 : Blo 1748575 1750375 := bstep (se 1 (by rfl) ⟨1312781, by rfl⟩ : syracuseStep 1750375 = 2625563) B2625563
theorem B6395273 : Blo 1748575 6395273 := bstep (se 2 (by rfl) ⟨2398227, by rfl⟩ : syracuseStep 6395273 = 4796455) B4796455
theorem B1750559 : Blo 1748575 1750559 := bstep (se 1 (by rfl) ⟨1312919, by rfl⟩ : syracuseStep 1750559 = 2625839) B2625839
theorem B3937895 : Blo 1748575 3937895 := bstep (se 1 (by rfl) ⟨2953421, by rfl⟩ : syracuseStep 3937895 = 5906843) B5906843
theorem B17045167 : Blo 1748575 17045167 := bstep (se 1 (by rfl) ⟨12783875, by rfl⟩ : syracuseStep 17045167 = 25567751) B25567751
theorem B3937967 : Blo 1748575 3937967 := bstep (se 1 (by rfl) ⟨2953475, by rfl⟩ : syracuseStep 3937967 = 5906951) B5906951
theorem B40384327 : Blo 1748575 40384327 := bstep (se 1 (by rfl) ⟨30288245, by rfl⟩ : syracuseStep 40384327 = 60576491) B60576491
theorem B8861885 : Blo 1748575 8861885 := bstep (se 3 (by rfl) ⟨1661603, by rfl⟩ : syracuseStep 8861885 = 3323207) B3323207
theorem B9459937 : Blo 1748575 9459937 := bstep (se 2 (by rfl) ⟨3547476, by rfl⟩ : syracuseStep 9459937 = 7094953) B7094953
theorem B37837151 : Blo 1748575 37837151 := bstep (se 1 (by rfl) ⟨28377863, by rfl⟩ : syracuseStep 37837151 = 56755727) B56755727
theorem B9583879 : Blo 1748575 9583879 := bstep (se 1 (by rfl) ⟨7187909, by rfl⟩ : syracuseStep 9583879 = 14375819) B14375819
theorem B10641017 : Blo 1748575 10641017 := bstep (se 2 (by rfl) ⟨3990381, by rfl⟩ : syracuseStep 10641017 = 7980763) B7980763
theorem B5906087 : Blo 1748575 5906087 := bstep (se 1 (by rfl) ⟨4429565, by rfl⟩ : syracuseStep 5906087 = 8859131) B8859131
theorem B2801407 : Blo 1748575 2801407 := bstep (se 1 (by rfl) ⟨2101055, by rfl⟩ : syracuseStep 2801407 = 4202111) B4202111
theorem B3153991 : Blo 1748575 3153991 := bstep (se 1 (by rfl) ⟨2365493, by rfl⟩ : syracuseStep 3153991 = 4730987) B4730987
theorem B5907923 : Blo 1748575 5907923 := bstep (se 1 (by rfl) ⟨4430942, by rfl⟩ : syracuseStep 5907923 = 8861885) B8861885
theorem B25224767 : Blo 1748575 25224767 := bstep (se 1 (by rfl) ⟨18918575, by rfl⟩ : syracuseStep 25224767 = 37837151) B37837151
theorem B56739527 : Blo 1748575 56739527 := bstep (se 1 (by rfl) ⟨42554645, by rfl⟩ : syracuseStep 56739527 = 85109291) B85109291
theorem B12617693 : Blo 1748575 12617693 := bstep (se 3 (by rfl) ⟨2365817, by rfl⟩ : syracuseStep 12617693 = 4731635) B4731635
theorem B22726889 : Blo 1748575 22726889 := bstep (se 2 (by rfl) ⟨8522583, by rfl⟩ : syracuseStep 22726889 = 17045167) B17045167
theorem B2623775 : Blo 1748575 2623775 := bstep (se 1 (by rfl) ⟨1967831, by rfl⟩ : syracuseStep 2623775 = 3935663) B3935663
theorem B113544665 : Blo 1748575 113544665 := bstep (se 2 (by rfl) ⟨42579249, by rfl⟩ : syracuseStep 113544665 = 85158499) B85158499
theorem B25218539 : Blo 1748575 25218539 := bstep (se 1 (by rfl) ⟨18913904, by rfl⟩ : syracuseStep 25218539 = 37827809) B37827809
theorem B4263515 : Blo 1748575 4263515 := bstep (se 1 (by rfl) ⟨3197636, by rfl⟩ : syracuseStep 4263515 = 6395273) B6395273
theorem B621784775 : Blo 1748575 621784775 := bstep (se 1 (by rfl) ⟨466338581, by rfl⟩ : syracuseStep 621784775 = 932677163) B932677163
theorem B2625263 : Blo 1748575 2625263 := bstep (se 1 (by rfl) ⟨1968947, by rfl⟩ : syracuseStep 2625263 = 3937895) B3937895
theorem B2625311 : Blo 1748575 2625311 := bstep (se 1 (by rfl) ⟨1968983, by rfl⟩ : syracuseStep 2625311 = 3937967) B3937967
theorem B1749023 : Blo 1748575 1749023 := bstep (se 1 (by rfl) ⟨1311767, by rfl⟩ : syracuseStep 1749023 = 2623535) B2623535
theorem B85078309 : Blo 1748575 85078309 := bstep (se 4 (by rfl) ⟨7976091, by rfl⟩ : syracuseStep 85078309 = 15952183) B15952183
theorem B1749595 : Blo 1748575 1749595 := bstep (se 1 (by rfl) ⟨1312196, by rfl⟩ : syracuseStep 1749595 = 2624393) B2624393
theorem B1749759 : Blo 1748575 1749759 := bstep (se 1 (by rfl) ⟨1312319, by rfl⟩ : syracuseStep 1749759 = 2624639) B2624639
theorem B1750047 : Blo 1748575 1750047 := bstep (se 1 (by rfl) ⟨1312535, by rfl⟩ : syracuseStep 1750047 = 2625071) B2625071
theorem B3937391 : Blo 1748575 3937391 := bstep (se 1 (by rfl) ⟨2953043, by rfl⟩ : syracuseStep 3937391 = 5906087) B5906087
theorem B1750127 : Blo 1748575 1750127 := bstep (se 1 (by rfl) ⟨1312595, by rfl⟩ : syracuseStep 1750127 = 2625191) B2625191
theorem B1750299 : Blo 1748575 1750299 := bstep (se 1 (by rfl) ⟨1312724, by rfl⟩ : syracuseStep 1750299 = 2625449) B2625449
theorem B14939639 : Blo 1748575 14939639 := bstep (se 1 (by rfl) ⟨11204729, by rfl⟩ : syracuseStep 14939639 = 22409459) B22409459
theorem B1750527 : Blo 1748575 1750527 := bstep (se 1 (by rfl) ⟨1312895, by rfl⟩ : syracuseStep 1750527 = 2625791) B2625791
theorem B10786375 : Blo 1748575 10786375 := bstep (se 1 (by rfl) ⟨8089781, by rfl⟩ : syracuseStep 10786375 = 16179563) B16179563
theorem B12613249 : Blo 1748575 12613249 := bstep (se 2 (by rfl) ⟨4729968, by rfl⟩ : syracuseStep 12613249 = 9459937) B9459937
theorem B7476943 : Blo 1748575 7476943 := bstep (se 1 (by rfl) ⟨5607707, by rfl⟩ : syracuseStep 7476943 = 11215415) B11215415
theorem B45438731 : Blo 1748575 45438731 := bstep (se 1 (by rfl) ⟨34079048, by rfl⟩ : syracuseStep 45438731 = 68158097) B68158097
theorem B29144953 : Blo 1748575 29144953 := bstep (se 2 (by rfl) ⟨10929357, by rfl⟩ : syracuseStep 29144953 = 21858715) B21858715
theorem B9967481 : Blo 1748575 9967481 := bstep (se 2 (by rfl) ⟨3737805, by rfl⟩ : syracuseStep 9967481 = 7475611) B7475611
theorem B145569727 : Blo 1748575 145569727 := bstep (se 1 (by rfl) ⟨109177295, by rfl⟩ : syracuseStep 145569727 = 218354591) B218354591
theorem B3938543 : Blo 1748575 3938543 := bstep (se 1 (by rfl) ⟨2953907, by rfl⟩ : syracuseStep 3938543 = 5907815) B5907815
theorem B4430315 : Blo 1748575 4430315 := bstep (se 1 (by rfl) ⟨3322736, by rfl⟩ : syracuseStep 4430315 = 6645473) B6645473
theorem B56736521 : Blo 1748575 56736521 := bstep (se 2 (by rfl) ⟨21276195, by rfl⟩ : syracuseStep 56736521 = 42552391) B42552391
theorem B77757245 : Blo 1748575 77757245 := bstep (se 3 (by rfl) ⟨14579483, by rfl⟩ : syracuseStep 77757245 = 29158967) B29158967
theorem B28376045 : Blo 1748575 28376045 := bstep (se 3 (by rfl) ⟨5320508, by rfl⟩ : syracuseStep 28376045 = 10641017) B10641017
theorem B12778505 : Blo 1748575 12778505 := bstep (se 2 (by rfl) ⟨4791939, by rfl⟩ : syracuseStep 12778505 = 9583879) B9583879
theorem B3735209 : Blo 1748575 3735209 := bstep (se 2 (by rfl) ⟨1400703, by rfl⟩ : syracuseStep 3735209 = 2801407) B2801407
theorem B53845769 : Blo 1748575 53845769 := bstep (se 2 (by rfl) ⟨20192163, by rfl⟩ : syracuseStep 53845769 = 40384327) B40384327
theorem B5906195 : Blo 1748575 5906195 := bstep (se 1 (by rfl) ⟨4429646, by rfl⟩ : syracuseStep 5906195 = 8859293) B8859293
theorem B6644987 : Blo 1748575 6644987 := bstep (se 1 (by rfl) ⟨4983740, by rfl⟩ : syracuseStep 6644987 = 9967481) B9967481
theorem B37824347 : Blo 1748575 37824347 := bstep (se 1 (by rfl) ⟨28368260, by rfl⟩ : syracuseStep 37824347 = 56736521) B56736521
theorem B18917363 : Blo 1748575 18917363 := bstep (se 1 (by rfl) ⟨14188022, by rfl⟩ : syracuseStep 18917363 = 28376045) B28376045
theorem B75696443 : Blo 1748575 75696443 := bstep (se 1 (by rfl) ⟨56772332, by rfl⟩ : syracuseStep 75696443 = 113544665) B113544665
theorem B16812359 : Blo 1748575 16812359 := bstep (se 1 (by rfl) ⟨12609269, by rfl⟩ : syracuseStep 16812359 = 25218539) B25218539
theorem B4205321 : Blo 1748575 4205321 := bstep (se 2 (by rfl) ⟨1576995, by rfl⟩ : syracuseStep 4205321 = 3153991) B3153991
theorem B113437745 : Blo 1748575 113437745 := bstep (se 2 (by rfl) ⟨42539154, by rfl⟩ : syracuseStep 113437745 = 85078309) B85078309
theorem B2624927 : Blo 1748575 2624927 := bstep (se 1 (by rfl) ⟨1968695, by rfl⟩ : syracuseStep 2624927 = 3937391) B3937391
theorem B37826351 : Blo 1748575 37826351 := bstep (se 1 (by rfl) ⟨28369763, by rfl⟩ : syracuseStep 37826351 = 56739527) B56739527
theorem B15151259 : Blo 1748575 15151259 := bstep (se 1 (by rfl) ⟨11363444, by rfl⟩ : syracuseStep 15151259 = 22726889) B22726889
theorem B2625695 : Blo 1748575 2625695 := bstep (se 1 (by rfl) ⟨1969271, by rfl⟩ : syracuseStep 2625695 = 3938543) B3938543
theorem B1749183 : Blo 1748575 1749183 := bstep (se 1 (by rfl) ⟨1311887, by rfl⟩ : syracuseStep 1749183 = 2623775) B2623775
theorem B2953543 : Blo 1748575 2953543 := bstep (se 1 (by rfl) ⟨2215157, by rfl⟩ : syracuseStep 2953543 = 4430315) B4430315
theorem B155439749 : Blo 1748575 155439749 := bstep (se 4 (by rfl) ⟨14572476, by rfl⟩ : syracuseStep 155439749 = 29144953) B29144953
theorem B14381833 : Blo 1748575 14381833 := bstep (se 2 (by rfl) ⟨5393187, by rfl⟩ : syracuseStep 14381833 = 10786375) B10786375
theorem B1750175 : Blo 1748575 1750175 := bstep (se 1 (by rfl) ⟨1312631, by rfl⟩ : syracuseStep 1750175 = 2625263) B2625263
theorem B3937463 : Blo 1748575 3937463 := bstep (se 1 (by rfl) ⟨2953097, by rfl⟩ : syracuseStep 3937463 = 5906195) B5906195
theorem B1750207 : Blo 1748575 1750207 := bstep (se 1 (by rfl) ⟨1312655, by rfl⟩ : syracuseStep 1750207 = 2625311) B2625311
theorem B3938615 : Blo 1748575 3938615 := bstep (se 1 (by rfl) ⟨2953961, by rfl⟩ : syracuseStep 3938615 = 5907923) B5907923
theorem B9959759 : Blo 1748575 9959759 := bstep (se 1 (by rfl) ⟨7469819, by rfl⟩ : syracuseStep 9959759 = 14939639) B14939639
theorem B16816511 : Blo 1748575 16816511 := bstep (se 1 (by rfl) ⟨12612383, by rfl⟩ : syracuseStep 16816511 = 25224767) B25224767
theorem B30292487 : Blo 1748575 30292487 := bstep (se 1 (by rfl) ⟨22719365, by rfl⟩ : syracuseStep 30292487 = 45438731) B45438731
theorem B8411795 : Blo 1748575 8411795 := bstep (se 1 (by rfl) ⟨6308846, by rfl⟩ : syracuseStep 8411795 = 12617693) B12617693
theorem B51838163 : Blo 1748575 51838163 := bstep (se 1 (by rfl) ⟨38878622, by rfl⟩ : syracuseStep 51838163 = 77757245) B77757245
theorem B8519003 : Blo 1748575 8519003 := bstep (se 1 (by rfl) ⟨6389252, by rfl⟩ : syracuseStep 8519003 = 12778505) B12778505
theorem B16817665 : Blo 1748575 16817665 := bstep (se 2 (by rfl) ⟨6306624, by rfl⟩ : syracuseStep 16817665 = 12613249) B12613249
theorem B9969257 : Blo 1748575 9969257 := bstep (se 2 (by rfl) ⟨3738471, by rfl⟩ : syracuseStep 9969257 = 7476943) B7476943
theorem B776371877 : Blo 1748575 776371877 := bstep (se 4 (by rfl) ⟨72784863, by rfl⟩ : syracuseStep 776371877 = 145569727) B145569727
theorem B2842343 : Blo 1748575 2842343 := bstep (se 1 (by rfl) ⟨2131757, by rfl⟩ : syracuseStep 2842343 = 4263515) B4263515
theorem B2490139 : Blo 1748575 2490139 := bstep (se 1 (by rfl) ⟨1867604, by rfl⟩ : syracuseStep 2490139 = 3735209) B3735209
theorem B414523183 : Blo 1748575 414523183 := bstep (se 1 (by rfl) ⟨310892387, by rfl⟩ : syracuseStep 414523183 = 621784775) B621784775
theorem B35897179 : Blo 1748575 35897179 := bstep (se 1 (by rfl) ⟨26922884, by rfl⟩ : syracuseStep 35897179 = 53845769) B53845769
theorem B40403357 : Blo 1748575 40403357 := bstep (se 3 (by rfl) ⟨7575629, by rfl⟩ : syracuseStep 40403357 = 15151259) B15151259
theorem B25216231 : Blo 1748575 25216231 := bstep (se 1 (by rfl) ⟨18912173, by rfl⟩ : syracuseStep 25216231 = 37824347) B37824347
theorem B50464295 : Blo 1748575 50464295 := bstep (se 1 (by rfl) ⟨37848221, by rfl⟩ : syracuseStep 50464295 = 75696443) B75696443
theorem B11208239 : Blo 1748575 11208239 := bstep (se 1 (by rfl) ⟨8406179, by rfl⟩ : syracuseStep 11208239 = 16812359) B16812359
theorem B20194991 : Blo 1748575 20194991 := bstep (se 1 (by rfl) ⟨15146243, by rfl⟩ : syracuseStep 20194991 = 30292487) B30292487
theorem B2803547 : Blo 1748575 2803547 := bstep (se 1 (by rfl) ⟨2102660, by rfl⟩ : syracuseStep 2803547 = 4205321) B4205321
theorem B22423553 : Blo 1748575 22423553 := bstep (se 2 (by rfl) ⟨8408832, by rfl⟩ : syracuseStep 22423553 = 16817665) B16817665
theorem B5679335 : Blo 1748575 5679335 := bstep (se 1 (by rfl) ⟨4259501, by rfl⟩ : syracuseStep 5679335 = 8519003) B8519003
theorem B3320185 : Blo 1748575 3320185 := bstep (se 2 (by rfl) ⟨1245069, by rfl⟩ : syracuseStep 3320185 = 2490139) B2490139
theorem B6646171 : Blo 1748575 6646171 := bstep (se 1 (by rfl) ⟨4984628, by rfl⟩ : syracuseStep 6646171 = 9969257) B9969257
theorem B517581251 : Blo 1748575 517581251 := bstep (se 1 (by rfl) ⟨388185938, by rfl⟩ : syracuseStep 517581251 = 776371877) B776371877
theorem B1894895 : Blo 1748575 1894895 := bstep (se 1 (by rfl) ⟨1421171, by rfl⟩ : syracuseStep 1894895 = 2842343) B2842343
theorem B25217567 : Blo 1748575 25217567 := bstep (se 1 (by rfl) ⟨18913175, by rfl⟩ : syracuseStep 25217567 = 37826351) B37826351
theorem B2624975 : Blo 1748575 2624975 := bstep (se 1 (by rfl) ⟨1968731, by rfl⟩ : syracuseStep 2624975 = 3937463) B3937463
theorem B12611575 : Blo 1748575 12611575 := bstep (se 1 (by rfl) ⟨9458681, by rfl⟩ : syracuseStep 12611575 = 18917363) B18917363
theorem B2625743 : Blo 1748575 2625743 := bstep (se 1 (by rfl) ⟨1969307, by rfl⟩ : syracuseStep 2625743 = 3938615) B3938615
theorem B6639839 : Blo 1748575 6639839 := bstep (se 1 (by rfl) ⟨4979879, by rfl⟩ : syracuseStep 6639839 = 9959759) B9959759
theorem B11211007 : Blo 1748575 11211007 := bstep (se 1 (by rfl) ⟨8408255, by rfl⟩ : syracuseStep 11211007 = 16816511) B16816511
theorem B5607863 : Blo 1748575 5607863 := bstep (se 1 (by rfl) ⟨4205897, by rfl⟩ : syracuseStep 5607863 = 8411795) B8411795
theorem B75625163 : Blo 1748575 75625163 := bstep (se 1 (by rfl) ⟨56718872, by rfl⟩ : syracuseStep 75625163 = 113437745) B113437745
theorem B34558775 : Blo 1748575 34558775 := bstep (se 1 (by rfl) ⟨25919081, by rfl⟩ : syracuseStep 34558775 = 51838163) B51838163
theorem B1749951 : Blo 1748575 1749951 := bstep (se 1 (by rfl) ⟨1312463, by rfl⟩ : syracuseStep 1749951 = 2624927) B2624927
theorem B47862905 : Blo 1748575 47862905 := bstep (se 2 (by rfl) ⟨17948589, by rfl⟩ : syracuseStep 47862905 = 35897179) B35897179
theorem B1750463 : Blo 1748575 1750463 := bstep (se 1 (by rfl) ⟨1312847, by rfl⟩ : syracuseStep 1750463 = 2625695) B2625695
theorem B103626499 : Blo 1748575 103626499 := bstep (se 1 (by rfl) ⟨77719874, by rfl⟩ : syracuseStep 103626499 = 155439749) B155439749
theorem B3938057 : Blo 1748575 3938057 := bstep (se 2 (by rfl) ⟨1476771, by rfl⟩ : syracuseStep 3938057 = 2953543) B2953543
theorem B4429991 : Blo 1748575 4429991 := bstep (se 1 (by rfl) ⟨3322493, by rfl⟩ : syracuseStep 4429991 = 6644987) B6644987
theorem B19175777 : Blo 1748575 19175777 := bstep (se 2 (by rfl) ⟨7190916, by rfl⟩ : syracuseStep 19175777 = 14381833) B14381833
theorem B552697577 : Blo 1748575 552697577 := bstep (se 2 (by rfl) ⟨207261591, by rfl⟩ : syracuseStep 552697577 = 414523183) B414523183
theorem B26935571 : Blo 1748575 26935571 := bstep (se 1 (by rfl) ⟨20201678, by rfl⟩ : syracuseStep 26935571 = 40403357) B40403357
theorem B7472159 : Blo 1748575 7472159 := bstep (se 1 (by rfl) ⟨5604119, by rfl⟩ : syracuseStep 7472159 = 11208239) B11208239
theorem B1869031 : Blo 1748575 1869031 := bstep (se 1 (by rfl) ⟨1401773, by rfl⟩ : syracuseStep 1869031 = 2803547) B2803547
theorem B33621641 : Blo 1748575 33621641 := bstep (se 2 (by rfl) ⟨12608115, by rfl⟩ : syracuseStep 33621641 = 25216231) B25216231
theorem B16811711 : Blo 1748575 16811711 := bstep (se 1 (by rfl) ⟨12608783, by rfl⟩ : syracuseStep 16811711 = 25217567) B25217567
theorem B138168665 : Blo 1748575 138168665 := bstep (se 2 (by rfl) ⟨51813249, by rfl⟩ : syracuseStep 138168665 = 103626499) B103626499
theorem B20212213 : Blo 1748575 20212213 := bstep (se 5 (by rfl) ⟨947447, by rfl⟩ : syracuseStep 20212213 = 1894895) B1894895
theorem B4426559 : Blo 1748575 4426559 := bstep (se 1 (by rfl) ⟨3319919, by rfl⟩ : syracuseStep 4426559 = 6639839) B6639839
theorem B3738575 : Blo 1748575 3738575 := bstep (se 1 (by rfl) ⟨2803931, by rfl⟩ : syracuseStep 3738575 = 5607863) B5607863
theorem B127634413 : Blo 1748575 127634413 := bstep (se 3 (by rfl) ⟨23931452, by rfl⟩ : syracuseStep 127634413 = 47862905) B47862905
theorem B50416775 : Blo 1748575 50416775 := bstep (se 1 (by rfl) ⟨37812581, by rfl⟩ : syracuseStep 50416775 = 75625163) B75625163
theorem B4426913 : Blo 1748575 4426913 := bstep (se 2 (by rfl) ⟨1660092, by rfl⟩ : syracuseStep 4426913 = 3320185) B3320185
theorem B23039183 : Blo 1748575 23039183 := bstep (se 1 (by rfl) ⟨17279387, by rfl⟩ : syracuseStep 23039183 = 34558775) B34558775
theorem B13463327 : Blo 1748575 13463327 := bstep (se 1 (by rfl) ⟨10097495, by rfl⟩ : syracuseStep 13463327 = 20194991) B20194991
theorem B2625371 : Blo 1748575 2625371 := bstep (se 1 (by rfl) ⟨1969028, by rfl⟩ : syracuseStep 2625371 = 3938057) B3938057
theorem B2953327 : Blo 1748575 2953327 := bstep (se 1 (by rfl) ⟨2214995, by rfl⟩ : syracuseStep 2953327 = 4429991) B4429991
theorem B12783851 : Blo 1748575 12783851 := bstep (se 1 (by rfl) ⟨9587888, by rfl⟩ : syracuseStep 12783851 = 19175777) B19175777
theorem B1749983 : Blo 1748575 1749983 := bstep (se 1 (by rfl) ⟨1312487, by rfl⟩ : syracuseStep 1749983 = 2624975) B2624975
theorem B368465051 : Blo 1748575 368465051 := bstep (se 1 (by rfl) ⟨276348788, by rfl⟩ : syracuseStep 368465051 = 552697577) B552697577
theorem B16815433 : Blo 1748575 16815433 := bstep (se 2 (by rfl) ⟨6305787, by rfl⟩ : syracuseStep 16815433 = 12611575) B12611575
theorem B1750495 : Blo 1748575 1750495 := bstep (se 1 (by rfl) ⟨1312871, by rfl⟩ : syracuseStep 1750495 = 2625743) B2625743
theorem B14948009 : Blo 1748575 14948009 := bstep (se 2 (by rfl) ⟨5605503, by rfl⟩ : syracuseStep 14948009 = 11211007) B11211007
theorem B8861561 : Blo 1748575 8861561 := bstep (se 2 (by rfl) ⟨3323085, by rfl⟩ : syracuseStep 8861561 = 6646171) B6646171
theorem B15144893 : Blo 1748575 15144893 := bstep (se 3 (by rfl) ⟨2839667, by rfl⟩ : syracuseStep 15144893 = 5679335) B5679335
theorem B33642863 : Blo 1748575 33642863 := bstep (se 1 (by rfl) ⟨25232147, by rfl⟩ : syracuseStep 33642863 = 50464295) B50464295
theorem B14949035 : Blo 1748575 14949035 := bstep (se 1 (by rfl) ⟨11211776, by rfl⟩ : syracuseStep 14949035 = 22423553) B22423553
theorem B345054167 : Blo 1748575 345054167 := bstep (se 1 (by rfl) ⟨258790625, by rfl⟩ : syracuseStep 345054167 = 517581251) B517581251
theorem B17957047 : Blo 1748575 17957047 := bstep (se 1 (by rfl) ⟨13467785, by rfl⟩ : syracuseStep 17957047 = 26935571) B26935571
theorem B4981439 : Blo 1748575 4981439 := bstep (se 1 (by rfl) ⟨3736079, by rfl⟩ : syracuseStep 4981439 = 7472159) B7472159
theorem B22414427 : Blo 1748575 22414427 := bstep (se 1 (by rfl) ⟨16810820, by rfl⟩ : syracuseStep 22414427 = 33621641) B33621641
theorem B11207807 : Blo 1748575 11207807 := bstep (se 1 (by rfl) ⟨8405855, by rfl⟩ : syracuseStep 11207807 = 16811711) B16811711
theorem B5907707 : Blo 1748575 5907707 := bstep (se 1 (by rfl) ⟨4430780, by rfl⟩ : syracuseStep 5907707 = 8861561) B8861561
theorem B92112443 : Blo 1748575 92112443 := bstep (se 1 (by rfl) ⟨69084332, by rfl⟩ : syracuseStep 92112443 = 138168665) B138168665
theorem B2492041 : Blo 1748575 2492041 := bstep (se 2 (by rfl) ⟨934515, by rfl⟩ : syracuseStep 2492041 = 1869031) B1869031
theorem B2951039 : Blo 1748575 2951039 := bstep (se 1 (by rfl) ⟨2213279, by rfl⟩ : syracuseStep 2951039 = 4426559) B4426559
theorem B2492383 : Blo 1748575 2492383 := bstep (se 1 (by rfl) ⟨1869287, by rfl⟩ : syracuseStep 2492383 = 3738575) B3738575
theorem B2951275 : Blo 1748575 2951275 := bstep (se 1 (by rfl) ⟨2213456, by rfl⟩ : syracuseStep 2951275 = 4426913) B4426913
theorem B8522567 : Blo 1748575 8522567 := bstep (se 1 (by rfl) ⟨6391925, by rfl⟩ : syracuseStep 8522567 = 12783851) B12783851
theorem B9965339 : Blo 1748575 9965339 := bstep (se 1 (by rfl) ⟨7474004, by rfl⟩ : syracuseStep 9965339 = 14948009) B14948009
theorem B10096595 : Blo 1748575 10096595 := bstep (se 1 (by rfl) ⟨7572446, by rfl⟩ : syracuseStep 10096595 = 15144893) B15144893
theorem B9966023 : Blo 1748575 9966023 := bstep (se 1 (by rfl) ⟨7474517, by rfl⟩ : syracuseStep 9966023 = 14949035) B14949035
theorem B230036111 : Blo 1748575 230036111 := bstep (se 1 (by rfl) ⟨172527083, by rfl⟩ : syracuseStep 230036111 = 345054167) B345054167
theorem B8975551 : Blo 1748575 8975551 := bstep (se 1 (by rfl) ⟨6731663, by rfl⟩ : syracuseStep 8975551 = 13463327) B13463327
theorem B1750247 : Blo 1748575 1750247 := bstep (se 1 (by rfl) ⟨1312685, by rfl⟩ : syracuseStep 1750247 = 2625371) B2625371
theorem B3937769 : Blo 1748575 3937769 := bstep (se 2 (by rfl) ⟨1476663, by rfl⟩ : syracuseStep 3937769 = 2953327) B2953327
theorem B26949617 : Blo 1748575 26949617 := bstep (se 2 (by rfl) ⟨10106106, by rfl⟩ : syracuseStep 26949617 = 20212213) B20212213
theorem B245643367 : Blo 1748575 245643367 := bstep (se 1 (by rfl) ⟨184232525, by rfl⟩ : syracuseStep 245643367 = 368465051) B368465051
theorem B170179217 : Blo 1748575 170179217 := bstep (se 2 (by rfl) ⟨63817206, by rfl⟩ : syracuseStep 170179217 = 127634413) B127634413
theorem B22428575 : Blo 1748575 22428575 := bstep (se 1 (by rfl) ⟨16821431, by rfl⟩ : syracuseStep 22428575 = 33642863) B33642863
theorem B22420577 : Blo 1748575 22420577 := bstep (se 2 (by rfl) ⟨8407716, by rfl⟩ : syracuseStep 22420577 = 16815433) B16815433
theorem B33611183 : Blo 1748575 33611183 := bstep (se 1 (by rfl) ⟨25208387, by rfl⟩ : syracuseStep 33611183 = 50416775) B50416775
theorem B15359455 : Blo 1748575 15359455 := bstep (se 1 (by rfl) ⟨11519591, by rfl⟩ : syracuseStep 15359455 = 23039183) B23039183
theorem B327524489 : Blo 1748575 327524489 := bstep (se 2 (by rfl) ⟨122821683, by rfl⟩ : syracuseStep 327524489 = 245643367) B245643367
theorem B6644015 : Blo 1748575 6644015 := bstep (se 1 (by rfl) ⟨4983011, by rfl⟩ : syracuseStep 6644015 = 9966023) B9966023
theorem B14942951 : Blo 1748575 14942951 := bstep (se 1 (by rfl) ⟨11207213, by rfl⟩ : syracuseStep 14942951 = 22414427) B22414427
theorem B7471871 : Blo 1748575 7471871 := bstep (se 1 (by rfl) ⟨5603903, by rfl⟩ : syracuseStep 7471871 = 11207807) B11207807
theorem B61408295 : Blo 1748575 61408295 := bstep (se 1 (by rfl) ⟨46056221, by rfl⟩ : syracuseStep 61408295 = 92112443) B92112443
theorem B1967359 : Blo 1748575 1967359 := bstep (se 1 (by rfl) ⟨1475519, by rfl⟩ : syracuseStep 1967359 = 2951039) B2951039
theorem B17966411 : Blo 1748575 17966411 := bstep (se 1 (by rfl) ⟨13474808, by rfl⟩ : syracuseStep 17966411 = 26949617) B26949617
theorem B113452811 : Blo 1748575 113452811 := bstep (se 1 (by rfl) ⟨85089608, by rfl⟩ : syracuseStep 113452811 = 170179217) B170179217
theorem B14952383 : Blo 1748575 14952383 := bstep (se 1 (by rfl) ⟨11214287, by rfl⟩ : syracuseStep 14952383 = 22428575) B22428575
theorem B22407455 : Blo 1748575 22407455 := bstep (se 1 (by rfl) ⟨16805591, by rfl⟩ : syracuseStep 22407455 = 33611183) B33611183
theorem B3935033 : Blo 1748575 3935033 := bstep (se 2 (by rfl) ⟨1475637, by rfl⟩ : syracuseStep 3935033 = 2951275) B2951275
theorem B153357407 : Blo 1748575 153357407 := bstep (se 1 (by rfl) ⟨115018055, by rfl⟩ : syracuseStep 153357407 = 230036111) B230036111
theorem B2625179 : Blo 1748575 2625179 := bstep (se 1 (by rfl) ⟨1968884, by rfl⟩ : syracuseStep 2625179 = 3937769) B3937769
theorem B13283837 : Blo 1748575 13283837 := bstep (se 3 (by rfl) ⟨2490719, by rfl⟩ : syracuseStep 13283837 = 4981439) B4981439
theorem B5681711 : Blo 1748575 5681711 := bstep (se 1 (by rfl) ⟨4261283, by rfl⟩ : syracuseStep 5681711 = 8522567) B8522567
theorem B14947051 : Blo 1748575 14947051 := bstep (se 1 (by rfl) ⟨11210288, by rfl⟩ : syracuseStep 14947051 = 22420577) B22420577
theorem B3322721 : Blo 1748575 3322721 := bstep (se 2 (by rfl) ⟨1246020, by rfl⟩ : syracuseStep 3322721 = 2492041) B2492041
theorem B3323177 : Blo 1748575 3323177 := bstep (se 2 (by rfl) ⟨1246191, by rfl⟩ : syracuseStep 3323177 = 2492383) B2492383
theorem B6731063 : Blo 1748575 6731063 := bstep (se 1 (by rfl) ⟨5048297, by rfl⟩ : syracuseStep 6731063 = 10096595) B10096595
theorem B23942729 : Blo 1748575 23942729 := bstep (se 2 (by rfl) ⟨8978523, by rfl⟩ : syracuseStep 23942729 = 17957047) B17957047
theorem B3938471 : Blo 1748575 3938471 := bstep (se 1 (by rfl) ⟨2953853, by rfl⟩ : syracuseStep 3938471 = 5907707) B5907707
theorem B11967401 : Blo 1748575 11967401 := bstep (se 2 (by rfl) ⟨4487775, by rfl⟩ : syracuseStep 11967401 = 8975551) B8975551
theorem B20479273 : Blo 1748575 20479273 := bstep (se 2 (by rfl) ⟨7679727, by rfl⟩ : syracuseStep 20479273 = 15359455) B15359455
theorem B6643559 : Blo 1748575 6643559 := bstep (se 1 (by rfl) ⟨4982669, by rfl⟩ : syracuseStep 6643559 = 9965339) B9965339
theorem B218349659 : Blo 1748575 218349659 := bstep (se 1 (by rfl) ⟨163762244, by rfl⟩ : syracuseStep 218349659 = 327524489) B327524489
theorem B8855891 : Blo 1748575 8855891 := bstep (se 1 (by rfl) ⟨6641918, by rfl⟩ : syracuseStep 8855891 = 13283837) B13283837
theorem B9961967 : Blo 1748575 9961967 := bstep (se 1 (by rfl) ⟨7471475, by rfl⟩ : syracuseStep 9961967 = 14942951) B14942951
theorem B4981247 : Blo 1748575 4981247 := bstep (se 1 (by rfl) ⟨3735935, by rfl⟩ : syracuseStep 4981247 = 7471871) B7471871
theorem B11977607 : Blo 1748575 11977607 := bstep (se 1 (by rfl) ⟨8983205, by rfl⟩ : syracuseStep 11977607 = 17966411) B17966411
theorem B2623145 : Blo 1748575 2623145 := bstep (se 2 (by rfl) ⟨983679, by rfl⟩ : syracuseStep 2623145 = 1967359) B1967359
theorem B2623355 : Blo 1748575 2623355 := bstep (se 1 (by rfl) ⟨1967516, by rfl⟩ : syracuseStep 2623355 = 3935033) B3935033
theorem B102238271 : Blo 1748575 102238271 := bstep (se 1 (by rfl) ⟨76678703, by rfl⟩ : syracuseStep 102238271 = 153357407) B153357407
theorem B3787807 : Blo 1748575 3787807 := bstep (se 1 (by rfl) ⟨2840855, by rfl⟩ : syracuseStep 3787807 = 5681711) B5681711
theorem B40938863 : Blo 1748575 40938863 := bstep (se 1 (by rfl) ⟨30704147, by rfl⟩ : syracuseStep 40938863 = 61408295) B61408295
theorem B2215451 : Blo 1748575 2215451 := bstep (se 1 (by rfl) ⟨1661588, by rfl⟩ : syracuseStep 2215451 = 3323177) B3323177
theorem B2625647 : Blo 1748575 2625647 := bstep (se 1 (by rfl) ⟨1969235, by rfl⟩ : syracuseStep 2625647 = 3938471) B3938471
theorem B14938303 : Blo 1748575 14938303 := bstep (se 1 (by rfl) ⟨11203727, by rfl⟩ : syracuseStep 14938303 = 22407455) B22407455
theorem B8860589 : Blo 1748575 8860589 := bstep (se 3 (by rfl) ⟨1661360, by rfl⟩ : syracuseStep 8860589 = 3322721) B3322721
theorem B1750119 : Blo 1748575 1750119 := bstep (se 1 (by rfl) ⟨1312589, by rfl⟩ : syracuseStep 1750119 = 2625179) B2625179
theorem B4429039 : Blo 1748575 4429039 := bstep (se 1 (by rfl) ⟨3321779, by rfl⟩ : syracuseStep 4429039 = 6643559) B6643559
theorem B4429343 : Blo 1748575 4429343 := bstep (se 1 (by rfl) ⟨3322007, by rfl⟩ : syracuseStep 4429343 = 6644015) B6644015
theorem B4487375 : Blo 1748575 4487375 := bstep (se 1 (by rfl) ⟨3365531, by rfl⟩ : syracuseStep 4487375 = 6731063) B6731063
theorem B19929401 : Blo 1748575 19929401 := bstep (se 2 (by rfl) ⟨7473525, by rfl⟩ : syracuseStep 19929401 = 14947051) B14947051
theorem B75635207 : Blo 1748575 75635207 := bstep (se 1 (by rfl) ⟨56726405, by rfl⟩ : syracuseStep 75635207 = 113452811) B113452811
theorem B9968255 : Blo 1748575 9968255 := bstep (se 1 (by rfl) ⟨7476191, by rfl⟩ : syracuseStep 9968255 = 14952383) B14952383
theorem B63847277 : Blo 1748575 63847277 := bstep (se 3 (by rfl) ⟨11971364, by rfl⟩ : syracuseStep 63847277 = 23942729) B23942729
theorem B109222789 : Blo 1748575 109222789 := bstep (se 4 (by rfl) ⟨10239636, by rfl⟩ : syracuseStep 109222789 = 20479273) B20479273
theorem B7978267 : Blo 1748575 7978267 := bstep (se 1 (by rfl) ⟨5983700, by rfl⟩ : syracuseStep 7978267 = 11967401) B11967401
theorem B5907059 : Blo 1748575 5907059 := bstep (se 1 (by rfl) ⟨4430294, by rfl⟩ : syracuseStep 5907059 = 8860589) B8860589
theorem B145630385 : Blo 1748575 145630385 := bstep (se 2 (by rfl) ⟨54611394, by rfl⟩ : syracuseStep 145630385 = 109222789) B109222789
theorem B68158847 : Blo 1748575 68158847 := bstep (se 1 (by rfl) ⟨51119135, by rfl⟩ : syracuseStep 68158847 = 102238271) B102238271
theorem B5907869 : Blo 1748575 5907869 := bstep (se 3 (by rfl) ⟨1107725, by rfl⟩ : syracuseStep 5907869 = 2215451) B2215451
theorem B2991583 : Blo 1748575 2991583 := bstep (se 1 (by rfl) ⟨2243687, by rfl⟩ : syracuseStep 2991583 = 4487375) B4487375
theorem B50423471 : Blo 1748575 50423471 := bstep (se 1 (by rfl) ⟨37817603, by rfl⟩ : syracuseStep 50423471 = 75635207) B75635207
theorem B6645503 : Blo 1748575 6645503 := bstep (se 1 (by rfl) ⟨4984127, by rfl⟩ : syracuseStep 6645503 = 9968255) B9968255
theorem B145566439 : Blo 1748575 145566439 := bstep (se 1 (by rfl) ⟨109174829, by rfl⟩ : syracuseStep 145566439 = 218349659) B218349659
theorem B19917737 : Blo 1748575 19917737 := bstep (se 2 (by rfl) ⟨7469151, by rfl⟩ : syracuseStep 19917737 = 14938303) B14938303
theorem B3320831 : Blo 1748575 3320831 := bstep (se 1 (by rfl) ⟨2490623, by rfl⟩ : syracuseStep 3320831 = 4981247) B4981247
theorem B109170301 : Blo 1748575 109170301 := bstep (se 3 (by rfl) ⟨20469431, by rfl⟩ : syracuseStep 109170301 = 40938863) B40938863
theorem B2952895 : Blo 1748575 2952895 := bstep (se 1 (by rfl) ⟨2214671, by rfl⟩ : syracuseStep 2952895 = 4429343) B4429343
theorem B1748763 : Blo 1748575 1748763 := bstep (se 1 (by rfl) ⟨1311572, by rfl⟩ : syracuseStep 1748763 = 2623145) B2623145
theorem B1748903 : Blo 1748575 1748903 := bstep (se 1 (by rfl) ⟨1311677, by rfl⟩ : syracuseStep 1748903 = 2623355) B2623355
theorem B5050409 : Blo 1748575 5050409 := bstep (se 2 (by rfl) ⟨1893903, by rfl⟩ : syracuseStep 5050409 = 3787807) B3787807
theorem B10637689 : Blo 1748575 10637689 := bstep (se 2 (by rfl) ⟨3989133, by rfl⟩ : syracuseStep 10637689 = 7978267) B7978267
theorem B1750431 : Blo 1748575 1750431 := bstep (se 1 (by rfl) ⟨1312823, by rfl⟩ : syracuseStep 1750431 = 2625647) B2625647
theorem B5903927 : Blo 1748575 5903927 := bstep (se 1 (by rfl) ⟨4427945, by rfl⟩ : syracuseStep 5903927 = 8855891) B8855891
theorem B6641311 : Blo 1748575 6641311 := bstep (se 1 (by rfl) ⟨4980983, by rfl⟩ : syracuseStep 6641311 = 9961967) B9961967
theorem B7985071 : Blo 1748575 7985071 := bstep (se 1 (by rfl) ⟨5988803, by rfl⟩ : syracuseStep 7985071 = 11977607) B11977607
theorem B13286267 : Blo 1748575 13286267 := bstep (se 1 (by rfl) ⟨9964700, by rfl⟩ : syracuseStep 13286267 = 19929401) B19929401
theorem B5905385 : Blo 1748575 5905385 := bstep (se 2 (by rfl) ⟨2214519, by rfl⟩ : syracuseStep 5905385 = 4429039) B4429039
theorem B42564851 : Blo 1748575 42564851 := bstep (se 1 (by rfl) ⟨31923638, by rfl⟩ : syracuseStep 42564851 = 63847277) B63847277
theorem B13467757 : Blo 1748575 13467757 := bstep (se 3 (by rfl) ⟨2525204, by rfl⟩ : syracuseStep 13467757 = 5050409) B5050409
theorem B8857511 : Blo 1748575 8857511 := bstep (se 1 (by rfl) ⟨6643133, by rfl⟩ : syracuseStep 8857511 = 13286267) B13286267
theorem B2213887 : Blo 1748575 2213887 := bstep (se 1 (by rfl) ⟨1660415, by rfl⟩ : syracuseStep 2213887 = 3320831) B3320831
theorem B14183585 : Blo 1748575 14183585 := bstep (se 2 (by rfl) ⟨5318844, by rfl⟩ : syracuseStep 14183585 = 10637689) B10637689
theorem B97086923 : Blo 1748575 97086923 := bstep (se 1 (by rfl) ⟨72815192, by rfl⟩ : syracuseStep 97086923 = 145630385) B145630385
theorem B3935951 : Blo 1748575 3935951 := bstep (se 1 (by rfl) ⟨2951963, by rfl⟩ : syracuseStep 3935951 = 5903927) B5903927
theorem B33615647 : Blo 1748575 33615647 := bstep (se 1 (by rfl) ⟨25211735, by rfl⟩ : syracuseStep 33615647 = 50423471) B50423471
theorem B3936923 : Blo 1748575 3936923 := bstep (se 1 (by rfl) ⟨2952692, by rfl⟩ : syracuseStep 3936923 = 5905385) B5905385
theorem B145560401 : Blo 1748575 145560401 := bstep (se 2 (by rfl) ⟨54585150, by rfl⟩ : syracuseStep 145560401 = 109170301) B109170301
theorem B3937193 : Blo 1748575 3937193 := bstep (se 2 (by rfl) ⟨1476447, by rfl⟩ : syracuseStep 3937193 = 2952895) B2952895
theorem B10646761 : Blo 1748575 10646761 := bstep (se 2 (by rfl) ⟨3992535, by rfl⟩ : syracuseStep 10646761 = 7985071) B7985071
theorem B3938039 : Blo 1748575 3938039 := bstep (se 1 (by rfl) ⟨2953529, by rfl⟩ : syracuseStep 3938039 = 5907059) B5907059
theorem B45439231 : Blo 1748575 45439231 := bstep (se 1 (by rfl) ⟨34079423, by rfl⟩ : syracuseStep 45439231 = 68158847) B68158847
theorem B3938579 : Blo 1748575 3938579 := bstep (se 1 (by rfl) ⟨2953934, by rfl⟩ : syracuseStep 3938579 = 5907869) B5907869
theorem B4430335 : Blo 1748575 4430335 := bstep (se 1 (by rfl) ⟨3322751, by rfl⟩ : syracuseStep 4430335 = 6645503) B6645503
theorem B776354341 : Blo 1748575 776354341 := bstep (se 4 (by rfl) ⟨72783219, by rfl⟩ : syracuseStep 776354341 = 145566439) B145566439
theorem B13278491 : Blo 1748575 13278491 := bstep (se 1 (by rfl) ⟨9958868, by rfl⟩ : syracuseStep 13278491 = 19917737) B19917737
theorem B3988777 : Blo 1748575 3988777 := bstep (se 2 (by rfl) ⟨1495791, by rfl⟩ : syracuseStep 3988777 = 2991583) B2991583
theorem B28376567 : Blo 1748575 28376567 := bstep (se 1 (by rfl) ⟨21282425, by rfl⟩ : syracuseStep 28376567 = 42564851) B42564851
theorem B8855081 : Blo 1748575 8855081 := bstep (se 2 (by rfl) ⟨3320655, by rfl⟩ : syracuseStep 8855081 = 6641311) B6641311
theorem B17957009 : Blo 1748575 17957009 := bstep (se 2 (by rfl) ⟨6733878, by rfl⟩ : syracuseStep 17957009 = 13467757) B13467757
theorem B5907113 : Blo 1748575 5907113 := bstep (se 2 (by rfl) ⟨2215167, by rfl⟩ : syracuseStep 5907113 = 4430335) B4430335
theorem B5318369 : Blo 1748575 5318369 := bstep (se 2 (by rfl) ⟨1994388, by rfl⟩ : syracuseStep 5318369 = 3988777) B3988777
theorem B9455723 : Blo 1748575 9455723 := bstep (se 1 (by rfl) ⟨7091792, by rfl⟩ : syracuseStep 9455723 = 14183585) B14183585
theorem B18917711 : Blo 1748575 18917711 := bstep (se 1 (by rfl) ⟨14188283, by rfl⟩ : syracuseStep 18917711 = 28376567) B28376567
theorem B2623967 : Blo 1748575 2623967 := bstep (se 1 (by rfl) ⟨1967975, by rfl⟩ : syracuseStep 2623967 = 3935951) B3935951
theorem B2951849 : Blo 1748575 2951849 := bstep (se 2 (by rfl) ⟨1106943, by rfl⟩ : syracuseStep 2951849 = 2213887) B2213887
theorem B2624615 : Blo 1748575 2624615 := bstep (se 1 (by rfl) ⟨1968461, by rfl⟩ : syracuseStep 2624615 = 3936923) B3936923
theorem B2624795 : Blo 1748575 2624795 := bstep (se 1 (by rfl) ⟨1968596, by rfl⟩ : syracuseStep 2624795 = 3937193) B3937193
theorem B2625359 : Blo 1748575 2625359 := bstep (se 1 (by rfl) ⟨1969019, by rfl⟩ : syracuseStep 2625359 = 3938039) B3938039
theorem B2625719 : Blo 1748575 2625719 := bstep (se 1 (by rfl) ⟨1969289, by rfl⟩ : syracuseStep 2625719 = 3938579) B3938579
theorem B8852327 : Blo 1748575 8852327 := bstep (se 1 (by rfl) ⟨6639245, by rfl⟩ : syracuseStep 8852327 = 13278491) B13278491
theorem B5903387 : Blo 1748575 5903387 := bstep (se 1 (by rfl) ⟨4427540, by rfl⟩ : syracuseStep 5903387 = 8855081) B8855081
theorem B22410431 : Blo 1748575 22410431 := bstep (se 1 (by rfl) ⟨16807823, by rfl⟩ : syracuseStep 22410431 = 33615647) B33615647
theorem B60585641 : Blo 1748575 60585641 := bstep (se 2 (by rfl) ⟨22719615, by rfl⟩ : syracuseStep 60585641 = 45439231) B45439231
theorem B97040267 : Blo 1748575 97040267 := bstep (se 1 (by rfl) ⟨72780200, by rfl⟩ : syracuseStep 97040267 = 145560401) B145560401
theorem B1035139121 : Blo 1748575 1035139121 := bstep (se 2 (by rfl) ⟨388177170, by rfl⟩ : syracuseStep 1035139121 = 776354341) B776354341
theorem B5905007 : Blo 1748575 5905007 := bstep (se 1 (by rfl) ⟨4428755, by rfl⟩ : syracuseStep 5905007 = 8857511) B8857511
theorem B14195681 : Blo 1748575 14195681 := bstep (se 2 (by rfl) ⟨5323380, by rfl⟩ : syracuseStep 14195681 = 10646761) B10646761
theorem B64724615 : Blo 1748575 64724615 := bstep (se 1 (by rfl) ⟨48543461, by rfl⟩ : syracuseStep 64724615 = 97086923) B97086923
theorem B64693511 : Blo 1748575 64693511 := bstep (se 1 (by rfl) ⟨48520133, by rfl⟩ : syracuseStep 64693511 = 97040267) B97040267
theorem B1967899 : Blo 1748575 1967899 := bstep (se 1 (by rfl) ⟨1475924, by rfl⟩ : syracuseStep 1967899 = 2951849) B2951849
theorem B9463787 : Blo 1748575 9463787 := bstep (se 1 (by rfl) ⟨7097840, by rfl⟩ : syracuseStep 9463787 = 14195681) B14195681
theorem B43149743 : Blo 1748575 43149743 := bstep (se 1 (by rfl) ⟨32362307, by rfl⟩ : syracuseStep 43149743 = 64724615) B64724615
theorem B47885357 : Blo 1748575 47885357 := bstep (se 3 (by rfl) ⟨8978504, by rfl⟩ : syracuseStep 47885357 = 17957009) B17957009
theorem B5901551 : Blo 1748575 5901551 := bstep (se 1 (by rfl) ⟨4426163, by rfl⟩ : syracuseStep 5901551 = 8852327) B8852327
theorem B3935591 : Blo 1748575 3935591 := bstep (se 1 (by rfl) ⟨2951693, by rfl⟩ : syracuseStep 3935591 = 5903387) B5903387
theorem B40390427 : Blo 1748575 40390427 := bstep (se 1 (by rfl) ⟨30292820, by rfl⟩ : syracuseStep 40390427 = 60585641) B60585641
theorem B6303815 : Blo 1748575 6303815 := bstep (se 1 (by rfl) ⟨4727861, by rfl⟩ : syracuseStep 6303815 = 9455723) B9455723
theorem B12611807 : Blo 1748575 12611807 := bstep (se 1 (by rfl) ⟨9458855, by rfl⟩ : syracuseStep 12611807 = 18917711) B18917711
theorem B1749311 : Blo 1748575 1749311 := bstep (se 1 (by rfl) ⟨1311983, by rfl⟩ : syracuseStep 1749311 = 2623967) B2623967
theorem B3936671 : Blo 1748575 3936671 := bstep (se 1 (by rfl) ⟨2952503, by rfl⟩ : syracuseStep 3936671 = 5905007) B5905007
theorem B1749743 : Blo 1748575 1749743 := bstep (se 1 (by rfl) ⟨1312307, by rfl⟩ : syracuseStep 1749743 = 2624615) B2624615
theorem B1749863 : Blo 1748575 1749863 := bstep (se 1 (by rfl) ⟨1312397, by rfl⟩ : syracuseStep 1749863 = 2624795) B2624795
theorem B1750239 : Blo 1748575 1750239 := bstep (se 1 (by rfl) ⟨1312679, by rfl⟩ : syracuseStep 1750239 = 2625359) B2625359
theorem B1750479 : Blo 1748575 1750479 := bstep (se 1 (by rfl) ⟨1312859, by rfl⟩ : syracuseStep 1750479 = 2625719) B2625719
theorem B3938075 : Blo 1748575 3938075 := bstep (se 1 (by rfl) ⟨2953556, by rfl⟩ : syracuseStep 3938075 = 5907113) B5907113
theorem B14940287 : Blo 1748575 14940287 := bstep (se 1 (by rfl) ⟨11205215, by rfl⟩ : syracuseStep 14940287 = 22410431) B22410431
theorem B3545579 : Blo 1748575 3545579 := bstep (se 1 (by rfl) ⟨2659184, by rfl⟩ : syracuseStep 3545579 = 5318369) B5318369
theorem B690092747 : Blo 1748575 690092747 := bstep (se 1 (by rfl) ⟨517569560, by rfl⟩ : syracuseStep 690092747 = 1035139121) B1035139121
theorem B4202543 : Blo 1748575 4202543 := bstep (se 1 (by rfl) ⟨3151907, by rfl⟩ : syracuseStep 4202543 = 6303815) B6303815
theorem B9454877 : Blo 1748575 9454877 := bstep (se 3 (by rfl) ⟨1772789, by rfl⟩ : syracuseStep 9454877 = 3545579) B3545579
theorem B6309191 : Blo 1748575 6309191 := bstep (se 1 (by rfl) ⟨4731893, by rfl⟩ : syracuseStep 6309191 = 9463787) B9463787
theorem B3934367 : Blo 1748575 3934367 := bstep (se 1 (by rfl) ⟨2950775, by rfl⟩ : syracuseStep 3934367 = 5901551) B5901551
theorem B2623727 : Blo 1748575 2623727 := bstep (se 1 (by rfl) ⟨1967795, by rfl⟩ : syracuseStep 2623727 = 3935591) B3935591
theorem B2623865 : Blo 1748575 2623865 := bstep (se 2 (by rfl) ⟨983949, by rfl⟩ : syracuseStep 2623865 = 1967899) B1967899
theorem B8407871 : Blo 1748575 8407871 := bstep (se 1 (by rfl) ⟨6305903, by rfl⟩ : syracuseStep 8407871 = 12611807) B12611807
theorem B2624447 : Blo 1748575 2624447 := bstep (se 1 (by rfl) ⟨1968335, by rfl⟩ : syracuseStep 2624447 = 3936671) B3936671
theorem B2625383 : Blo 1748575 2625383 := bstep (se 1 (by rfl) ⟨1969037, by rfl⟩ : syracuseStep 2625383 = 3938075) B3938075
theorem B28766495 : Blo 1748575 28766495 := bstep (se 1 (by rfl) ⟨21574871, by rfl⟩ : syracuseStep 28766495 = 43149743) B43149743
theorem B43129007 : Blo 1748575 43129007 := bstep (se 1 (by rfl) ⟨32346755, by rfl⟩ : syracuseStep 43129007 = 64693511) B64693511
theorem B9960191 : Blo 1748575 9960191 := bstep (se 1 (by rfl) ⟨7470143, by rfl⟩ : syracuseStep 9960191 = 14940287) B14940287
theorem B460061831 : Blo 1748575 460061831 := bstep (se 1 (by rfl) ⟨345046373, by rfl⟩ : syracuseStep 460061831 = 690092747) B690092747
theorem B31923571 : Blo 1748575 31923571 := bstep (se 1 (by rfl) ⟨23942678, by rfl⟩ : syracuseStep 31923571 = 47885357) B47885357
theorem B107707805 : Blo 1748575 107707805 := bstep (se 3 (by rfl) ⟨20195213, by rfl⟩ : syracuseStep 107707805 = 40390427) B40390427
theorem B11206781 : Blo 1748575 11206781 := bstep (se 3 (by rfl) ⟨2101271, by rfl⟩ : syracuseStep 11206781 = 4202543) B4202543
theorem B19177663 : Blo 1748575 19177663 := bstep (se 1 (by rfl) ⟨14383247, by rfl⟩ : syracuseStep 19177663 = 28766495) B28766495
theorem B2622911 : Blo 1748575 2622911 := bstep (se 1 (by rfl) ⟨1967183, by rfl⟩ : syracuseStep 2622911 = 3934367) B3934367
theorem B5605247 : Blo 1748575 5605247 := bstep (se 1 (by rfl) ⟨4203935, by rfl⟩ : syracuseStep 5605247 = 8407871) B8407871
theorem B71805203 : Blo 1748575 71805203 := bstep (se 1 (by rfl) ⟨53853902, by rfl⟩ : syracuseStep 71805203 = 107707805) B107707805
theorem B6303251 : Blo 1748575 6303251 := bstep (se 1 (by rfl) ⟨4727438, by rfl⟩ : syracuseStep 6303251 = 9454877) B9454877
theorem B1749151 : Blo 1748575 1749151 := bstep (se 1 (by rfl) ⟨1311863, by rfl⟩ : syracuseStep 1749151 = 2623727) B2623727
theorem B1749243 : Blo 1748575 1749243 := bstep (se 1 (by rfl) ⟨1311932, by rfl⟩ : syracuseStep 1749243 = 2623865) B2623865
theorem B6640127 : Blo 1748575 6640127 := bstep (se 1 (by rfl) ⟨4980095, by rfl⟩ : syracuseStep 6640127 = 9960191) B9960191
theorem B1749631 : Blo 1748575 1749631 := bstep (se 1 (by rfl) ⟨1312223, by rfl⟩ : syracuseStep 1749631 = 2624447) B2624447
theorem B1750255 : Blo 1748575 1750255 := bstep (se 1 (by rfl) ⟨1312691, by rfl⟩ : syracuseStep 1750255 = 2625383) B2625383
theorem B16824509 : Blo 1748575 16824509 := bstep (se 3 (by rfl) ⟨3154595, by rfl⟩ : syracuseStep 16824509 = 6309191) B6309191
theorem B28752671 : Blo 1748575 28752671 := bstep (se 1 (by rfl) ⟨21564503, by rfl⟩ : syracuseStep 28752671 = 43129007) B43129007
theorem B42564761 : Blo 1748575 42564761 := bstep (se 2 (by rfl) ⟨15961785, by rfl⟩ : syracuseStep 42564761 = 31923571) B31923571
theorem B306707887 : Blo 1748575 306707887 := bstep (se 1 (by rfl) ⟨230030915, by rfl⟩ : syracuseStep 306707887 = 460061831) B460061831
theorem B7471187 : Blo 1748575 7471187 := bstep (se 1 (by rfl) ⟨5603390, by rfl⟩ : syracuseStep 7471187 = 11206781) B11206781
theorem B11216339 : Blo 1748575 11216339 := bstep (se 1 (by rfl) ⟨8412254, by rfl⟩ : syracuseStep 11216339 = 16824509) B16824509
theorem B25570217 : Blo 1748575 25570217 := bstep (se 2 (by rfl) ⟨9588831, by rfl⟩ : syracuseStep 25570217 = 19177663) B19177663
theorem B4426751 : Blo 1748575 4426751 := bstep (se 1 (by rfl) ⟨3320063, by rfl⟩ : syracuseStep 4426751 = 6640127) B6640127
theorem B1748607 : Blo 1748575 1748607 := bstep (se 1 (by rfl) ⟨1311455, by rfl⟩ : syracuseStep 1748607 = 2622911) B2622911
theorem B47870135 : Blo 1748575 47870135 := bstep (se 1 (by rfl) ⟨35902601, by rfl⟩ : syracuseStep 47870135 = 71805203) B71805203
theorem B1635775397 : Blo 1748575 1635775397 := bstep (se 4 (by rfl) ⟨153353943, by rfl⟩ : syracuseStep 1635775397 = 306707887) B306707887
theorem B14947325 : Blo 1748575 14947325 := bstep (se 3 (by rfl) ⟨2802623, by rfl⟩ : syracuseStep 14947325 = 5605247) B5605247
theorem B19168447 : Blo 1748575 19168447 := bstep (se 1 (by rfl) ⟨14376335, by rfl⟩ : syracuseStep 19168447 = 28752671) B28752671
theorem B28376507 : Blo 1748575 28376507 := bstep (se 1 (by rfl) ⟨21282380, by rfl⟩ : syracuseStep 28376507 = 42564761) B42564761
theorem B4202167 : Blo 1748575 4202167 := bstep (se 1 (by rfl) ⟨3151625, by rfl⟩ : syracuseStep 4202167 = 6303251) B6303251
theorem B4980791 : Blo 1748575 4980791 := bstep (se 1 (by rfl) ⟨3735593, by rfl⟩ : syracuseStep 4980791 = 7471187) B7471187
theorem B2951167 : Blo 1748575 2951167 := bstep (se 1 (by rfl) ⟨2213375, by rfl⟩ : syracuseStep 2951167 = 4426751) B4426751
theorem B18917671 : Blo 1748575 18917671 := bstep (se 1 (by rfl) ⟨14188253, by rfl⟩ : syracuseStep 18917671 = 28376507) B28376507
theorem B9964883 : Blo 1748575 9964883 := bstep (se 1 (by rfl) ⟨7473662, by rfl⟩ : syracuseStep 9964883 = 14947325) B14947325
theorem B31913423 : Blo 1748575 31913423 := bstep (se 1 (by rfl) ⟨23935067, by rfl⟩ : syracuseStep 31913423 = 47870135) B47870135
theorem B1090516931 : Blo 1748575 1090516931 := bstep (se 1 (by rfl) ⟨817887698, by rfl⟩ : syracuseStep 1090516931 = 1635775397) B1635775397
theorem B7477559 : Blo 1748575 7477559 := bstep (se 1 (by rfl) ⟨5608169, by rfl⟩ : syracuseStep 7477559 = 11216339) B11216339
theorem B25557929 : Blo 1748575 25557929 := bstep (se 2 (by rfl) ⟨9584223, by rfl⟩ : syracuseStep 25557929 = 19168447) B19168447
theorem B17046811 : Blo 1748575 17046811 := bstep (se 1 (by rfl) ⟨12785108, by rfl⟩ : syracuseStep 17046811 = 25570217) B25570217
theorem B5602889 : Blo 1748575 5602889 := bstep (se 2 (by rfl) ⟨2101083, by rfl⟩ : syracuseStep 5602889 = 4202167) B4202167
theorem B25223561 : Blo 1748575 25223561 := bstep (se 2 (by rfl) ⟨9458835, by rfl⟩ : syracuseStep 25223561 = 18917671) B18917671
theorem B21275615 : Blo 1748575 21275615 := bstep (se 1 (by rfl) ⟨15956711, by rfl⟩ : syracuseStep 21275615 = 31913423) B31913423
theorem B3934889 : Blo 1748575 3934889 := bstep (se 2 (by rfl) ⟨1475583, by rfl⟩ : syracuseStep 3934889 = 2951167) B2951167
theorem B3320527 : Blo 1748575 3320527 := bstep (se 1 (by rfl) ⟨2490395, by rfl⟩ : syracuseStep 3320527 = 4980791) B4980791
theorem B727011287 : Blo 1748575 727011287 := bstep (se 1 (by rfl) ⟨545258465, by rfl⟩ : syracuseStep 727011287 = 1090516931) B1090516931
theorem B4985039 : Blo 1748575 4985039 := bstep (se 1 (by rfl) ⟨3738779, by rfl⟩ : syracuseStep 4985039 = 7477559) B7477559
theorem B22729081 : Blo 1748575 22729081 := bstep (se 2 (by rfl) ⟨8523405, by rfl⟩ : syracuseStep 22729081 = 17046811) B17046811
theorem B14941037 : Blo 1748575 14941037 := bstep (se 3 (by rfl) ⟨2801444, by rfl⟩ : syracuseStep 14941037 = 5602889) B5602889
theorem B17038619 : Blo 1748575 17038619 := bstep (se 1 (by rfl) ⟨12778964, by rfl⟩ : syracuseStep 17038619 = 25557929) B25557929
theorem B6643255 : Blo 1748575 6643255 := bstep (se 1 (by rfl) ⟨4982441, by rfl⟩ : syracuseStep 6643255 = 9964883) B9964883
theorem B2623259 : Blo 1748575 2623259 := bstep (se 1 (by rfl) ⟨1967444, by rfl⟩ : syracuseStep 2623259 = 3934889) B3934889
theorem B8857673 : Blo 1748575 8857673 := bstep (se 2 (by rfl) ⟨3321627, by rfl⟩ : syracuseStep 8857673 = 6643255) B6643255
theorem B484674191 : Blo 1748575 484674191 := bstep (se 1 (by rfl) ⟨363505643, by rfl⟩ : syracuseStep 484674191 = 727011287) B727011287
theorem B30305441 : Blo 1748575 30305441 := bstep (se 2 (by rfl) ⟨11364540, by rfl⟩ : syracuseStep 30305441 = 22729081) B22729081
theorem B14183743 : Blo 1748575 14183743 := bstep (se 1 (by rfl) ⟨10637807, by rfl⟩ : syracuseStep 14183743 = 21275615) B21275615
theorem B4427369 : Blo 1748575 4427369 := bstep (se 2 (by rfl) ⟨1660263, by rfl⟩ : syracuseStep 4427369 = 3320527) B3320527
theorem B11359079 : Blo 1748575 11359079 := bstep (se 1 (by rfl) ⟨8519309, by rfl⟩ : syracuseStep 11359079 = 17038619) B17038619
theorem B3323359 : Blo 1748575 3323359 := bstep (se 1 (by rfl) ⟨2492519, by rfl⟩ : syracuseStep 3323359 = 4985039) B4985039
theorem B16815707 : Blo 1748575 16815707 := bstep (se 1 (by rfl) ⟨12611780, by rfl⟩ : syracuseStep 16815707 = 25223561) B25223561
theorem B9960691 : Blo 1748575 9960691 := bstep (se 1 (by rfl) ⟨7470518, by rfl⟩ : syracuseStep 9960691 = 14941037) B14941037
theorem B13280921 : Blo 1748575 13280921 := bstep (se 2 (by rfl) ⟨4980345, by rfl⟩ : syracuseStep 13280921 = 9960691) B9960691
theorem B20203627 : Blo 1748575 20203627 := bstep (se 1 (by rfl) ⟨15152720, by rfl⟩ : syracuseStep 20203627 = 30305441) B30305441
theorem B2951579 : Blo 1748575 2951579 := bstep (se 1 (by rfl) ⟨2213684, by rfl⟩ : syracuseStep 2951579 = 4427369) B4427369
theorem B7572719 : Blo 1748575 7572719 := bstep (se 1 (by rfl) ⟨5679539, by rfl⟩ : syracuseStep 7572719 = 11359079) B11359079
theorem B11210471 : Blo 1748575 11210471 := bstep (se 1 (by rfl) ⟨8407853, by rfl⟩ : syracuseStep 11210471 = 16815707) B16815707
theorem B1748839 : Blo 1748575 1748839 := bstep (se 1 (by rfl) ⟨1311629, by rfl⟩ : syracuseStep 1748839 = 2623259) B2623259
theorem B18911657 : Blo 1748575 18911657 := bstep (se 2 (by rfl) ⟨7091871, by rfl⟩ : syracuseStep 18911657 = 14183743) B14183743
theorem B5905115 : Blo 1748575 5905115 := bstep (se 1 (by rfl) ⟨4428836, by rfl⟩ : syracuseStep 5905115 = 8857673) B8857673
theorem B323116127 : Blo 1748575 323116127 := bstep (se 1 (by rfl) ⟨242337095, by rfl⟩ : syracuseStep 323116127 = 484674191) B484674191
theorem B4431145 : Blo 1748575 4431145 := bstep (se 2 (by rfl) ⟨1661679, by rfl⟩ : syracuseStep 4431145 = 3323359) B3323359
theorem B12607771 : Blo 1748575 12607771 := bstep (se 1 (by rfl) ⟨9455828, by rfl⟩ : syracuseStep 12607771 = 18911657) B18911657
theorem B1967719 : Blo 1748575 1967719 := bstep (se 1 (by rfl) ⟨1475789, by rfl⟩ : syracuseStep 1967719 = 2951579) B2951579
theorem B5908193 : Blo 1748575 5908193 := bstep (se 2 (by rfl) ⟨2215572, by rfl⟩ : syracuseStep 5908193 = 4431145) B4431145
theorem B215410751 : Blo 1748575 215410751 := bstep (se 1 (by rfl) ⟨161558063, by rfl⟩ : syracuseStep 215410751 = 323116127) B323116127
theorem B5048479 : Blo 1748575 5048479 := bstep (se 1 (by rfl) ⟨3786359, by rfl⟩ : syracuseStep 5048479 = 7572719) B7572719
theorem B7473647 : Blo 1748575 7473647 := bstep (se 1 (by rfl) ⟨5605235, by rfl⟩ : syracuseStep 7473647 = 11210471) B11210471
theorem B26938169 : Blo 1748575 26938169 := bstep (se 2 (by rfl) ⟨10101813, by rfl⟩ : syracuseStep 26938169 = 20203627) B20203627
theorem B3936743 : Blo 1748575 3936743 := bstep (se 1 (by rfl) ⟨2952557, by rfl⟩ : syracuseStep 3936743 = 5905115) B5905115
theorem B8853947 : Blo 1748575 8853947 := bstep (se 1 (by rfl) ⟨6640460, by rfl⟩ : syracuseStep 8853947 = 13280921) B13280921
theorem B16810361 : Blo 1748575 16810361 := bstep (se 2 (by rfl) ⟨6303885, by rfl⟩ : syracuseStep 16810361 = 12607771) B12607771
theorem B143607167 : Blo 1748575 143607167 := bstep (se 1 (by rfl) ⟨107705375, by rfl⟩ : syracuseStep 143607167 = 215410751) B215410751
theorem B4982431 : Blo 1748575 4982431 := bstep (se 1 (by rfl) ⟨3736823, by rfl⟩ : syracuseStep 4982431 = 7473647) B7473647
theorem B17958779 : Blo 1748575 17958779 := bstep (se 1 (by rfl) ⟨13469084, by rfl⟩ : syracuseStep 17958779 = 26938169) B26938169
theorem B2623625 : Blo 1748575 2623625 := bstep (se 2 (by rfl) ⟨983859, by rfl⟩ : syracuseStep 2623625 = 1967719) B1967719
theorem B2624495 : Blo 1748575 2624495 := bstep (se 1 (by rfl) ⟨1968371, by rfl⟩ : syracuseStep 2624495 = 3936743) B3936743
theorem B5902631 : Blo 1748575 5902631 := bstep (se 1 (by rfl) ⟨4426973, by rfl⟩ : syracuseStep 5902631 = 8853947) B8853947
theorem B6731305 : Blo 1748575 6731305 := bstep (se 2 (by rfl) ⟨2524239, by rfl⟩ : syracuseStep 6731305 = 5048479) B5048479
theorem B3938795 : Blo 1748575 3938795 := bstep (se 1 (by rfl) ⟨2954096, by rfl⟩ : syracuseStep 3938795 = 5908193) B5908193
theorem B11206907 : Blo 1748575 11206907 := bstep (se 1 (by rfl) ⟨8405180, by rfl⟩ : syracuseStep 11206907 = 16810361) B16810361
theorem B3935087 : Blo 1748575 3935087 := bstep (se 1 (by rfl) ⟨2951315, by rfl⟩ : syracuseStep 3935087 = 5902631) B5902631
theorem B143601173 : Blo 1748575 143601173 := bstep (se 6 (by rfl) ⟨3365652, by rfl⟩ : syracuseStep 143601173 = 6731305) B6731305
theorem B11972519 : Blo 1748575 11972519 := bstep (se 1 (by rfl) ⟨8979389, by rfl⟩ : syracuseStep 11972519 = 17958779) B17958779
theorem B1749083 : Blo 1748575 1749083 := bstep (se 1 (by rfl) ⟨1311812, by rfl⟩ : syracuseStep 1749083 = 2623625) B2623625
theorem B2625863 : Blo 1748575 2625863 := bstep (se 1 (by rfl) ⟨1969397, by rfl⟩ : syracuseStep 2625863 = 3938795) B3938795
theorem B1749663 : Blo 1748575 1749663 := bstep (se 1 (by rfl) ⟨1312247, by rfl⟩ : syracuseStep 1749663 = 2624495) B2624495
theorem B95738111 : Blo 1748575 95738111 := bstep (se 1 (by rfl) ⟨71803583, by rfl⟩ : syracuseStep 95738111 = 143607167) B143607167
theorem B6643241 : Blo 1748575 6643241 := bstep (se 2 (by rfl) ⟨2491215, by rfl⟩ : syracuseStep 6643241 = 4982431) B4982431
theorem B7471271 : Blo 1748575 7471271 := bstep (se 1 (by rfl) ⟨5603453, by rfl⟩ : syracuseStep 7471271 = 11206907) B11206907
theorem B63825407 : Blo 1748575 63825407 := bstep (se 1 (by rfl) ⟨47869055, by rfl⟩ : syracuseStep 63825407 = 95738111) B95738111
theorem B2623391 : Blo 1748575 2623391 := bstep (se 1 (by rfl) ⟨1967543, by rfl⟩ : syracuseStep 2623391 = 3935087) B3935087
theorem B95734115 : Blo 1748575 95734115 := bstep (se 1 (by rfl) ⟨71800586, by rfl⟩ : syracuseStep 95734115 = 143601173) B143601173
theorem B7981679 : Blo 1748575 7981679 := bstep (se 1 (by rfl) ⟨5986259, by rfl⟩ : syracuseStep 7981679 = 11972519) B11972519
theorem B4428827 : Blo 1748575 4428827 := bstep (se 1 (by rfl) ⟨3321620, by rfl⟩ : syracuseStep 4428827 = 6643241) B6643241
theorem B1750575 : Blo 1748575 1750575 := bstep (se 1 (by rfl) ⟨1312931, by rfl⟩ : syracuseStep 1750575 = 2625863) B2625863
theorem B4980847 : Blo 1748575 4980847 := bstep (se 1 (by rfl) ⟨3735635, by rfl⟩ : syracuseStep 4980847 = 7471271) B7471271
theorem B42550271 : Blo 1748575 42550271 := bstep (se 1 (by rfl) ⟨31912703, by rfl⟩ : syracuseStep 42550271 = 63825407) B63825407
theorem B21284477 : Blo 1748575 21284477 := bstep (se 3 (by rfl) ⟨3990839, by rfl⟩ : syracuseStep 21284477 = 7981679) B7981679
theorem B2952551 : Blo 1748575 2952551 := bstep (se 1 (by rfl) ⟨2214413, by rfl⟩ : syracuseStep 2952551 = 4428827) B4428827
theorem B1748927 : Blo 1748575 1748927 := bstep (se 1 (by rfl) ⟨1311695, by rfl⟩ : syracuseStep 1748927 = 2623391) B2623391
theorem B63822743 : Blo 1748575 63822743 := bstep (se 1 (by rfl) ⟨47867057, by rfl⟩ : syracuseStep 63822743 = 95734115) B95734115
theorem B14189651 : Blo 1748575 14189651 := bstep (se 1 (by rfl) ⟨10642238, by rfl⟩ : syracuseStep 14189651 = 21284477) B21284477
theorem B1968367 : Blo 1748575 1968367 := bstep (se 1 (by rfl) ⟨1476275, by rfl⟩ : syracuseStep 1968367 = 2952551) B2952551
theorem B6641129 : Blo 1748575 6641129 := bstep (se 2 (by rfl) ⟨2490423, by rfl⟩ : syracuseStep 6641129 = 4980847) B4980847
theorem B28366847 : Blo 1748575 28366847 := bstep (se 1 (by rfl) ⟨21275135, by rfl⟩ : syracuseStep 28366847 = 42550271) B42550271
theorem B42548495 : Blo 1748575 42548495 := bstep (se 1 (by rfl) ⟨31911371, by rfl⟩ : syracuseStep 42548495 = 63822743) B63822743
theorem B2624489 : Blo 1748575 2624489 := bstep (se 2 (by rfl) ⟨984183, by rfl⟩ : syracuseStep 2624489 = 1968367) B1968367
theorem B113462653 : Blo 1748575 113462653 := bstep (se 3 (by rfl) ⟨21274247, by rfl⟩ : syracuseStep 113462653 = 42548495) B42548495
theorem B4427419 : Blo 1748575 4427419 := bstep (se 1 (by rfl) ⟨3320564, by rfl⟩ : syracuseStep 4427419 = 6641129) B6641129
theorem B18911231 : Blo 1748575 18911231 := bstep (se 1 (by rfl) ⟨14183423, by rfl⟩ : syracuseStep 18911231 = 28366847) B28366847
theorem B9459767 : Blo 1748575 9459767 := bstep (se 1 (by rfl) ⟨7094825, by rfl⟩ : syracuseStep 9459767 = 14189651) B14189651
theorem B12607487 : Blo 1748575 12607487 := bstep (se 1 (by rfl) ⟨9455615, by rfl⟩ : syracuseStep 12607487 = 18911231) B18911231
theorem B151283537 : Blo 1748575 151283537 := bstep (se 2 (by rfl) ⟨56731326, by rfl⟩ : syracuseStep 151283537 = 113462653) B113462653
theorem B1749659 : Blo 1748575 1749659 := bstep (se 1 (by rfl) ⟨1312244, by rfl⟩ : syracuseStep 1749659 = 2624489) B2624489
theorem B5903225 : Blo 1748575 5903225 := bstep (se 2 (by rfl) ⟨2213709, by rfl⟩ : syracuseStep 5903225 = 4427419) B4427419
theorem B6306511 : Blo 1748575 6306511 := bstep (se 1 (by rfl) ⟨4729883, by rfl⟩ : syracuseStep 6306511 = 9459767) B9459767
theorem B8404991 : Blo 1748575 8404991 := bstep (se 1 (by rfl) ⟨6303743, by rfl⟩ : syracuseStep 8404991 = 12607487) B12607487
theorem B3935483 : Blo 1748575 3935483 := bstep (se 1 (by rfl) ⟨2951612, by rfl⟩ : syracuseStep 3935483 = 5903225) B5903225
theorem B8408681 : Blo 1748575 8408681 := bstep (se 2 (by rfl) ⟨3153255, by rfl⟩ : syracuseStep 8408681 = 6306511) B6306511
theorem B100855691 : Blo 1748575 100855691 := bstep (se 1 (by rfl) ⟨75641768, by rfl⟩ : syracuseStep 100855691 = 151283537) B151283537
theorem B2623655 : Blo 1748575 2623655 := bstep (se 1 (by rfl) ⟨1967741, by rfl⟩ : syracuseStep 2623655 = 3935483) B3935483
theorem B5605787 : Blo 1748575 5605787 := bstep (se 1 (by rfl) ⟨4204340, by rfl⟩ : syracuseStep 5605787 = 8408681) B8408681
theorem B5603327 : Blo 1748575 5603327 := bstep (se 1 (by rfl) ⟨4202495, by rfl⟩ : syracuseStep 5603327 = 8404991) B8404991
theorem B67237127 : Blo 1748575 67237127 := bstep (se 1 (by rfl) ⟨50427845, by rfl⟩ : syracuseStep 67237127 = 100855691) B100855691
theorem B3737191 : Blo 1748575 3737191 := bstep (se 1 (by rfl) ⟨2802893, by rfl⟩ : syracuseStep 3737191 = 5605787) B5605787
theorem B3735551 : Blo 1748575 3735551 := bstep (se 1 (by rfl) ⟨2801663, by rfl⟩ : syracuseStep 3735551 = 5603327) B5603327
theorem B1749103 : Blo 1748575 1749103 := bstep (se 1 (by rfl) ⟨1311827, by rfl⟩ : syracuseStep 1749103 = 2623655) B2623655
theorem B44824751 : Blo 1748575 44824751 := bstep (se 1 (by rfl) ⟨33618563, by rfl⟩ : syracuseStep 44824751 = 67237127) B67237127
theorem B4982921 : Blo 1748575 4982921 := bstep (se 2 (by rfl) ⟨1868595, by rfl⟩ : syracuseStep 4982921 = 3737191) B3737191
theorem B29883167 : Blo 1748575 29883167 := bstep (se 1 (by rfl) ⟨22412375, by rfl⟩ : syracuseStep 29883167 = 44824751) B44824751
theorem B2490367 : Blo 1748575 2490367 := bstep (se 1 (by rfl) ⟨1867775, by rfl⟩ : syracuseStep 2490367 = 3735551) B3735551
theorem B3320489 : Blo 1748575 3320489 := bstep (se 2 (by rfl) ⟨1245183, by rfl⟩ : syracuseStep 3320489 = 2490367) B2490367
theorem B3321947 : Blo 1748575 3321947 := bstep (se 1 (by rfl) ⟨2491460, by rfl⟩ : syracuseStep 3321947 = 4982921) B4982921
theorem B19922111 : Blo 1748575 19922111 := bstep (se 1 (by rfl) ⟨14941583, by rfl⟩ : syracuseStep 19922111 = 29883167) B29883167
theorem B2213659 : Blo 1748575 2213659 := bstep (se 1 (by rfl) ⟨1660244, by rfl⟩ : syracuseStep 2213659 = 3320489) B3320489
theorem B13281407 : Blo 1748575 13281407 := bstep (se 1 (by rfl) ⟨9961055, by rfl⟩ : syracuseStep 13281407 = 19922111) B19922111
theorem B2214631 : Blo 1748575 2214631 := bstep (se 1 (by rfl) ⟨1660973, by rfl⟩ : syracuseStep 2214631 = 3321947) B3321947
theorem B2951545 : Blo 1748575 2951545 := bstep (se 2 (by rfl) ⟨1106829, by rfl⟩ : syracuseStep 2951545 = 2213659) B2213659
theorem B2952841 : Blo 1748575 2952841 := bstep (se 2 (by rfl) ⟨1107315, by rfl⟩ : syracuseStep 2952841 = 2214631) B2214631
theorem B8854271 : Blo 1748575 8854271 := bstep (se 1 (by rfl) ⟨6640703, by rfl⟩ : syracuseStep 8854271 = 13281407) B13281407
theorem B3935393 : Blo 1748575 3935393 := bstep (se 2 (by rfl) ⟨1475772, by rfl⟩ : syracuseStep 3935393 = 2951545) B2951545
theorem B5902847 : Blo 1748575 5902847 := bstep (se 1 (by rfl) ⟨4427135, by rfl⟩ : syracuseStep 5902847 = 8854271) B8854271
theorem B3937121 : Blo 1748575 3937121 := bstep (se 2 (by rfl) ⟨1476420, by rfl⟩ : syracuseStep 3937121 = 2952841) B2952841
theorem B2623595 : Blo 1748575 2623595 := bstep (se 1 (by rfl) ⟨1967696, by rfl⟩ : syracuseStep 2623595 = 3935393) B3935393
theorem B3935231 : Blo 1748575 3935231 := bstep (se 1 (by rfl) ⟨2951423, by rfl⟩ : syracuseStep 3935231 = 5902847) B5902847
theorem B2624747 : Blo 1748575 2624747 := bstep (se 1 (by rfl) ⟨1968560, by rfl⟩ : syracuseStep 2624747 = 3937121) B3937121
theorem B2623487 : Blo 1748575 2623487 := bstep (se 1 (by rfl) ⟨1967615, by rfl⟩ : syracuseStep 2623487 = 3935231) B3935231
theorem B1749063 : Blo 1748575 1749063 := bstep (se 1 (by rfl) ⟨1311797, by rfl⟩ : syracuseStep 1749063 = 2623595) B2623595
theorem B1749831 : Blo 1748575 1749831 := bstep (se 1 (by rfl) ⟨1312373, by rfl⟩ : syracuseStep 1749831 = 2624747) B2624747
theorem B1748991 : Blo 1748575 1748991 := bstep (se 1 (by rfl) ⟨1311743, by rfl⟩ : syracuseStep 1748991 = 2623487) B2623487

theorem C0 (j : ℕ) (h1 : 437143 ≤ j) (h2 : j ≤ 437643) : Blo 1748575 (4 * j + 3) := by
  interval_cases j
  · exact B1748575
  · exact B1748579
  · exact B1748583
  · exact B1748587
  · exact B1748591
  · exact B1748595
  · exact B1748599
  · exact B1748603
  · exact B1748607
  · exact B1748611
  · exact B1748615
  · exact B1748619
  · exact B1748623
  · exact B1748627
  · exact B1748631
  · exact B1748635
  · exact B1748639
  · exact B1748643
  · exact B1748647
  · exact B1748651
  · exact B1748655
  · exact B1748659
  · exact B1748663
  · exact B1748667
  · exact B1748671
  · exact B1748675
  · exact B1748679
  · exact B1748683
  · exact B1748687
  · exact B1748691
  · exact B1748695
  · exact B1748699
  · exact B1748703
  · exact B1748707
  · exact B1748711
  · exact B1748715
  · exact B1748719
  · exact B1748723
  · exact B1748727
  · exact B1748731
  · exact B1748735
  · exact B1748739
  · exact B1748743
  · exact B1748747
  · exact B1748751
  · exact B1748755
  · exact B1748759
  · exact B1748763
  · exact B1748767
  · exact B1748771
  · exact B1748775
  · exact B1748779
  · exact B1748783
  · exact B1748787
  · exact B1748791
  · exact B1748795
  · exact B1748799
  · exact B1748803
  · exact B1748807
  · exact B1748811
  · exact B1748815
  · exact B1748819
  · exact B1748823
  · exact B1748827
  · exact B1748831
  · exact B1748835
  · exact B1748839
  · exact B1748843
  · exact B1748847
  · exact B1748851
  · exact B1748855
  · exact B1748859
  · exact B1748863
  · exact B1748867
  · exact B1748871
  · exact B1748875
  · exact B1748879
  · exact B1748883
  · exact B1748887
  · exact B1748891
  · exact B1748895
  · exact B1748899
  · exact B1748903
  · exact B1748907
  · exact B1748911
  · exact B1748915
  · exact B1748919
  · exact B1748923
  · exact B1748927
  · exact B1748931
  · exact B1748935
  · exact B1748939
  · exact B1748943
  · exact B1748947
  · exact B1748951
  · exact B1748955
  · exact B1748959
  · exact B1748963
  · exact B1748967
  · exact B1748971
  · exact B1748975
  · exact B1748979
  · exact B1748983
  · exact B1748987
  · exact B1748991
  · exact B1748995
  · exact B1748999
  · exact B1749003
  · exact B1749007
  · exact B1749011
  · exact B1749015
  · exact B1749019
  · exact B1749023
  · exact B1749027
  · exact B1749031
  · exact B1749035
  · exact B1749039
  · exact B1749043
  · exact B1749047
  · exact B1749051
  · exact B1749055
  · exact B1749059
  · exact B1749063
  · exact B1749067
  · exact B1749071
  · exact B1749075
  · exact B1749079
  · exact B1749083
  · exact B1749087
  · exact B1749091
  · exact B1749095
  · exact B1749099
  · exact B1749103
  · exact B1749107
  · exact B1749111
  · exact B1749115
  · exact B1749119
  · exact B1749123
  · exact B1749127
  · exact B1749131
  · exact B1749135
  · exact B1749139
  · exact B1749143
  · exact B1749147
  · exact B1749151
  · exact B1749155
  · exact B1749159
  · exact B1749163
  · exact B1749167
  · exact B1749171
  · exact B1749175
  · exact B1749179
  · exact B1749183
  · exact B1749187
  · exact B1749191
  · exact B1749195
  · exact B1749199
  · exact B1749203
  · exact B1749207
  · exact B1749211
  · exact B1749215
  · exact B1749219
  · exact B1749223
  · exact B1749227
  · exact B1749231
  · exact B1749235
  · exact B1749239
  · exact B1749243
  · exact B1749247
  · exact B1749251
  · exact B1749255
  · exact B1749259
  · exact B1749263
  · exact B1749267
  · exact B1749271
  · exact B1749275
  · exact B1749279
  · exact B1749283
  · exact B1749287
  · exact B1749291
  · exact B1749295
  · exact B1749299
  · exact B1749303
  · exact B1749307
  · exact B1749311
  · exact B1749315
  · exact B1749319
  · exact B1749323
  · exact B1749327
  · exact B1749331
  · exact B1749335
  · exact B1749339
  · exact B1749343
  · exact B1749347
  · exact B1749351
  · exact B1749355
  · exact B1749359
  · exact B1749363
  · exact B1749367
  · exact B1749371
  · exact B1749375
  · exact B1749379
  · exact B1749383
  · exact B1749387
  · exact B1749391
  · exact B1749395
  · exact B1749399
  · exact B1749403
  · exact B1749407
  · exact B1749411
  · exact B1749415
  · exact B1749419
  · exact B1749423
  · exact B1749427
  · exact B1749431
  · exact B1749435
  · exact B1749439
  · exact B1749443
  · exact B1749447
  · exact B1749451
  · exact B1749455
  · exact B1749459
  · exact B1749463
  · exact B1749467
  · exact B1749471
  · exact B1749475
  · exact B1749479
  · exact B1749483
  · exact B1749487
  · exact B1749491
  · exact B1749495
  · exact B1749499
  · exact B1749503
  · exact B1749507
  · exact B1749511
  · exact B1749515
  · exact B1749519
  · exact B1749523
  · exact B1749527
  · exact B1749531
  · exact B1749535
  · exact B1749539
  · exact B1749543
  · exact B1749547
  · exact B1749551
  · exact B1749555
  · exact B1749559
  · exact B1749563
  · exact B1749567
  · exact B1749571
  · exact B1749575
  · exact B1749579
  · exact B1749583
  · exact B1749587
  · exact B1749591
  · exact B1749595
  · exact B1749599
  · exact B1749603
  · exact B1749607
  · exact B1749611
  · exact B1749615
  · exact B1749619
  · exact B1749623
  · exact B1749627
  · exact B1749631
  · exact B1749635
  · exact B1749639
  · exact B1749643
  · exact B1749647
  · exact B1749651
  · exact B1749655
  · exact B1749659
  · exact B1749663
  · exact B1749667
  · exact B1749671
  · exact B1749675
  · exact B1749679
  · exact B1749683
  · exact B1749687
  · exact B1749691
  · exact B1749695
  · exact B1749699
  · exact B1749703
  · exact B1749707
  · exact B1749711
  · exact B1749715
  · exact B1749719
  · exact B1749723
  · exact B1749727
  · exact B1749731
  · exact B1749735
  · exact B1749739
  · exact B1749743
  · exact B1749747
  · exact B1749751
  · exact B1749755
  · exact B1749759
  · exact B1749763
  · exact B1749767
  · exact B1749771
  · exact B1749775
  · exact B1749779
  · exact B1749783
  · exact B1749787
  · exact B1749791
  · exact B1749795
  · exact B1749799
  · exact B1749803
  · exact B1749807
  · exact B1749811
  · exact B1749815
  · exact B1749819
  · exact B1749823
  · exact B1749827
  · exact B1749831
  · exact B1749835
  · exact B1749839
  · exact B1749843
  · exact B1749847
  · exact B1749851
  · exact B1749855
  · exact B1749859
  · exact B1749863
  · exact B1749867
  · exact B1749871
  · exact B1749875
  · exact B1749879
  · exact B1749883
  · exact B1749887
  · exact B1749891
  · exact B1749895
  · exact B1749899
  · exact B1749903
  · exact B1749907
  · exact B1749911
  · exact B1749915
  · exact B1749919
  · exact B1749923
  · exact B1749927
  · exact B1749931
  · exact B1749935
  · exact B1749939
  · exact B1749943
  · exact B1749947
  · exact B1749951
  · exact B1749955
  · exact B1749959
  · exact B1749963
  · exact B1749967
  · exact B1749971
  · exact B1749975
  · exact B1749979
  · exact B1749983
  · exact B1749987
  · exact B1749991
  · exact B1749995
  · exact B1749999
  · exact B1750003
  · exact B1750007
  · exact B1750011
  · exact B1750015
  · exact B1750019
  · exact B1750023
  · exact B1750027
  · exact B1750031
  · exact B1750035
  · exact B1750039
  · exact B1750043
  · exact B1750047
  · exact B1750051
  · exact B1750055
  · exact B1750059
  · exact B1750063
  · exact B1750067
  · exact B1750071
  · exact B1750075
  · exact B1750079
  · exact B1750083
  · exact B1750087
  · exact B1750091
  · exact B1750095
  · exact B1750099
  · exact B1750103
  · exact B1750107
  · exact B1750111
  · exact B1750115
  · exact B1750119
  · exact B1750123
  · exact B1750127
  · exact B1750131
  · exact B1750135
  · exact B1750139
  · exact B1750143
  · exact B1750147
  · exact B1750151
  · exact B1750155
  · exact B1750159
  · exact B1750163
  · exact B1750167
  · exact B1750171
  · exact B1750175
  · exact B1750179
  · exact B1750183
  · exact B1750187
  · exact B1750191
  · exact B1750195
  · exact B1750199
  · exact B1750203
  · exact B1750207
  · exact B1750211
  · exact B1750215
  · exact B1750219
  · exact B1750223
  · exact B1750227
  · exact B1750231
  · exact B1750235
  · exact B1750239
  · exact B1750243
  · exact B1750247
  · exact B1750251
  · exact B1750255
  · exact B1750259
  · exact B1750263
  · exact B1750267
  · exact B1750271
  · exact B1750275
  · exact B1750279
  · exact B1750283
  · exact B1750287
  · exact B1750291
  · exact B1750295
  · exact B1750299
  · exact B1750303
  · exact B1750307
  · exact B1750311
  · exact B1750315
  · exact B1750319
  · exact B1750323
  · exact B1750327
  · exact B1750331
  · exact B1750335
  · exact B1750339
  · exact B1750343
  · exact B1750347
  · exact B1750351
  · exact B1750355
  · exact B1750359
  · exact B1750363
  · exact B1750367
  · exact B1750371
  · exact B1750375
  · exact B1750379
  · exact B1750383
  · exact B1750387
  · exact B1750391
  · exact B1750395
  · exact B1750399
  · exact B1750403
  · exact B1750407
  · exact B1750411
  · exact B1750415
  · exact B1750419
  · exact B1750423
  · exact B1750427
  · exact B1750431
  · exact B1750435
  · exact B1750439
  · exact B1750443
  · exact B1750447
  · exact B1750451
  · exact B1750455
  · exact B1750459
  · exact B1750463
  · exact B1750467
  · exact B1750471
  · exact B1750475
  · exact B1750479
  · exact B1750483
  · exact B1750487
  · exact B1750491
  · exact B1750495
  · exact B1750499
  · exact B1750503
  · exact B1750507
  · exact B1750511
  · exact B1750515
  · exact B1750519
  · exact B1750523
  · exact B1750527
  · exact B1750531
  · exact B1750535
  · exact B1750539
  · exact B1750543
  · exact B1750547
  · exact B1750551
  · exact B1750555
  · exact B1750559
  · exact B1750563
  · exact B1750567
  · exact B1750571
  · exact B1750575

theorem solution (m : ℕ) (hlo : 1748575 ≤ m) (hhi : m ≤ 1750575) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 437143 ≤ j := by omega
    have hj2 : j ≤ 437643 := by omega
    have hb : Blo 1748575 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
