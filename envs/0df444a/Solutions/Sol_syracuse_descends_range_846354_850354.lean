-- Prove2me | solution 1 for syracuse_descends_range_846354_850354
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:56.146906+00:00
-- url     : https://prove2.me/submissions/f1411571-c362-4a64-9011-7601f3817073

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


theorem B917525 : Blo 846354 917525 := bbase (se 6 (by rfl) ⟨21504, by rfl⟩ : syracuseStep 917525 = 43009) (by norm_num)
theorem B917669 : Blo 846354 917669 := bbase (se 4 (by rfl) ⟨86031, by rfl⟩ : syracuseStep 917669 = 172063) (by norm_num)
theorem B4292837 : Blo 846354 4292837 := bbase (se 4 (by rfl) ⟨402453, by rfl⟩ : syracuseStep 4292837 = 804907) (by norm_num)
theorem B1147429 : Blo 846354 1147429 := bbase (se 4 (by rfl) ⟨107571, by rfl⟩ : syracuseStep 1147429 = 215143) (by norm_num)
theorem B1147477 : Blo 846354 1147477 := bbase (se 8 (by rfl) ⟨6723, by rfl⟩ : syracuseStep 1147477 = 13447) (by norm_num)
theorem B7832213 : Blo 846354 7832213 := bbase (se 6 (by rfl) ⟨183567, by rfl⟩ : syracuseStep 7832213 = 367135) (by norm_num)
theorem B918301 : Blo 846354 918301 := bbase (se 3 (by rfl) ⟨172181, by rfl⟩ : syracuseStep 918301 = 344363) (by norm_num)
theorem B3441653 : Blo 846354 3441653 := bbase (se 5 (by rfl) ⟨161327, by rfl⟩ : syracuseStep 3441653 = 322655) (by norm_num)
theorem B1016885 : Blo 846354 1016885 := bbase (se 5 (by rfl) ⟨47666, by rfl⟩ : syracuseStep 1016885 = 95333) (by norm_num)
theorem B1606853 : Blo 846354 1606853 := bbase (se 4 (by rfl) ⟨150642, by rfl⟩ : syracuseStep 1606853 = 301285) (by norm_num)
theorem B1017145 : Blo 846354 1017145 := bbase (se 2 (by rfl) ⟨381429, by rfl⟩ : syracuseStep 1017145 = 762859) (by norm_num)
theorem B1017193 : Blo 846354 1017193 := bbase (se 2 (by rfl) ⟨381447, by rfl⟩ : syracuseStep 1017193 = 762895) (by norm_num)
theorem B1607141 : Blo 846354 1607141 := bbase (se 4 (by rfl) ⟨150669, by rfl⟩ : syracuseStep 1607141 = 301339) (by norm_num)
theorem B4294133 : Blo 846354 4294133 := bbase (se 5 (by rfl) ⟨201287, by rfl⟩ : syracuseStep 4294133 = 402575) (by norm_num)
theorem B1934837 : Blo 846354 1934837 := bbase (se 5 (by rfl) ⟨90695, by rfl⟩ : syracuseStep 1934837 = 181391) (by norm_num)
theorem B4589045 : Blo 846354 4589045 := bbase (se 5 (by rfl) ⟨215111, by rfl⟩ : syracuseStep 4589045 = 430223) (by norm_num)
theorem B1607293 : Blo 846354 1607293 := bbase (se 3 (by rfl) ⟨301367, by rfl⟩ : syracuseStep 1607293 = 602735) (by norm_num)
theorem B9176789 : Blo 846354 9176789 := bbase (se 7 (by rfl) ⟨107540, by rfl⟩ : syracuseStep 9176789 = 215081) (by norm_num)
theorem B2721509 : Blo 846354 2721509 := bbase (se 4 (by rfl) ⟨255141, by rfl⟩ : syracuseStep 2721509 = 510283) (by norm_num)
theorem B952177 : Blo 846354 952177 := bbase (se 2 (by rfl) ⟨357066, by rfl⟩ : syracuseStep 952177 = 714133) (by norm_num)
theorem B952213 : Blo 846354 952213 := bbase (se 6 (by rfl) ⟨22317, by rfl⟩ : syracuseStep 952213 = 44635) (by norm_num)
theorem B1607597 : Blo 846354 1607597 := bbase (se 3 (by rfl) ⟨301424, by rfl⟩ : syracuseStep 1607597 = 602849) (by norm_num)
theorem B952249 : Blo 846354 952249 := bbase (se 2 (by rfl) ⟨357093, by rfl⟩ : syracuseStep 952249 = 714187) (by norm_num)
theorem B1148861 : Blo 846354 1148861 := bbase (se 3 (by rfl) ⟨215411, by rfl⟩ : syracuseStep 1148861 = 430823) (by norm_num)
theorem B952285 : Blo 846354 952285 := bbase (se 3 (by rfl) ⟨178553, by rfl⟩ : syracuseStep 952285 = 357107) (by norm_num)
theorem B952321 : Blo 846354 952321 := bbase (se 2 (by rfl) ⟨357120, by rfl⟩ : syracuseStep 952321 = 714241) (by norm_num)
theorem B1017865 : Blo 846354 1017865 := bbase (se 2 (by rfl) ⟨381699, by rfl⟩ : syracuseStep 1017865 = 763399) (by norm_num)
theorem B952357 : Blo 846354 952357 := bbase (se 4 (by rfl) ⟨89283, by rfl⟩ : syracuseStep 952357 = 178567) (by norm_num)
theorem B952393 : Blo 846354 952393 := bbase (se 2 (by rfl) ⟨357147, by rfl⟩ : syracuseStep 952393 = 714295) (by norm_num)
theorem B952429 : Blo 846354 952429 := bbase (se 3 (by rfl) ⟨178580, by rfl⟩ : syracuseStep 952429 = 357161) (by norm_num)
theorem B952465 : Blo 846354 952465 := bbase (se 2 (by rfl) ⟨357174, by rfl⟩ : syracuseStep 952465 = 714349) (by norm_num)
theorem B952501 : Blo 846354 952501 := bbase (se 5 (by rfl) ⟨44648, by rfl⟩ : syracuseStep 952501 = 89297) (by norm_num)
theorem B952537 : Blo 846354 952537 := bbase (se 2 (by rfl) ⟨357201, by rfl⟩ : syracuseStep 952537 = 714403) (by norm_num)
theorem B2033885 : Blo 846354 2033885 := bbase (se 3 (by rfl) ⟨381353, by rfl⟩ : syracuseStep 2033885 = 762707) (by norm_num)
theorem B952573 : Blo 846354 952573 := bbase (se 3 (by rfl) ⟨178607, by rfl⟩ : syracuseStep 952573 = 357215) (by norm_num)
theorem B952609 : Blo 846354 952609 := bbase (se 2 (by rfl) ⟨357228, by rfl⟩ : syracuseStep 952609 = 714457) (by norm_num)
theorem B952645 : Blo 846354 952645 := bbase (se 4 (by rfl) ⟨89310, by rfl⟩ : syracuseStep 952645 = 178621) (by norm_num)
theorem B952681 : Blo 846354 952681 := bbase (se 2 (by rfl) ⟨357255, by rfl⟩ : syracuseStep 952681 = 714511) (by norm_num)
theorem B952717 : Blo 846354 952717 := bbase (se 3 (by rfl) ⟨178634, by rfl⟩ : syracuseStep 952717 = 357269) (by norm_num)
theorem B2034077 : Blo 846354 2034077 := bbase (se 3 (by rfl) ⟨381389, by rfl⟩ : syracuseStep 2034077 = 762779) (by norm_num)
theorem B952753 : Blo 846354 952753 := bbase (se 2 (by rfl) ⟨357282, by rfl⟩ : syracuseStep 952753 = 714565) (by norm_num)
theorem B952789 : Blo 846354 952789 := bbase (se 7 (by rfl) ⟨11165, by rfl⟩ : syracuseStep 952789 = 22331) (by norm_num)
theorem B952825 : Blo 846354 952825 := bbase (se 2 (by rfl) ⟨357309, by rfl⟩ : syracuseStep 952825 = 714619) (by norm_num)
theorem B920089 : Blo 846354 920089 := bbase (se 2 (by rfl) ⟨345033, by rfl⟩ : syracuseStep 920089 = 690067) (by norm_num)
theorem B952861 : Blo 846354 952861 := bbase (se 3 (by rfl) ⟨178661, by rfl⟩ : syracuseStep 952861 = 357323) (by norm_num)
theorem B952897 : Blo 846354 952897 := bbase (se 2 (by rfl) ⟨357336, by rfl⟩ : syracuseStep 952897 = 714673) (by norm_num)
theorem B952933 : Blo 846354 952933 := bbase (se 4 (by rfl) ⟨89337, by rfl⟩ : syracuseStep 952933 = 178675) (by norm_num)
theorem B2722405 : Blo 846354 2722405 := bbase (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) (by norm_num)
theorem B952969 : Blo 846354 952969 := bbase (se 2 (by rfl) ⟨357363, by rfl⟩ : syracuseStep 952969 = 714727) (by norm_num)
theorem B7244437 : Blo 846354 7244437 := bbase (se 6 (by rfl) ⟨169791, by rfl⟩ : syracuseStep 7244437 = 339583) (by norm_num)
theorem B1608349 : Blo 846354 1608349 := bbase (se 3 (by rfl) ⟨301565, by rfl⟩ : syracuseStep 1608349 = 603131) (by norm_num)
theorem B953005 : Blo 846354 953005 := bbase (se 3 (by rfl) ⟨178688, by rfl⟩ : syracuseStep 953005 = 357377) (by norm_num)
theorem B953041 : Blo 846354 953041 := bbase (se 2 (by rfl) ⟨357390, by rfl⟩ : syracuseStep 953041 = 714781) (by norm_num)
theorem B953077 : Blo 846354 953077 := bbase (se 5 (by rfl) ⟨44675, by rfl⟩ : syracuseStep 953077 = 89351) (by norm_num)
theorem B4295429 : Blo 846354 4295429 := bbase (se 4 (by rfl) ⟨402696, by rfl⟩ : syracuseStep 4295429 = 805393) (by norm_num)
theorem B953113 : Blo 846354 953113 := bbase (se 2 (by rfl) ⟨357417, by rfl⟩ : syracuseStep 953113 = 714835) (by norm_num)
theorem B1608493 : Blo 846354 1608493 := bbase (se 3 (by rfl) ⟨301592, by rfl⟩ : syracuseStep 1608493 = 603185) (by norm_num)
theorem B953149 : Blo 846354 953149 := bbase (se 3 (by rfl) ⟨178715, by rfl⟩ : syracuseStep 953149 = 357431) (by norm_num)
theorem B3869525 : Blo 846354 3869525 := bbase (se 9 (by rfl) ⟨11336, by rfl⟩ : syracuseStep 3869525 = 22673) (by norm_num)
theorem B953185 : Blo 846354 953185 := bbase (se 2 (by rfl) ⟨357444, by rfl⟩ : syracuseStep 953185 = 714889) (by norm_num)
theorem B953221 : Blo 846354 953221 := bbase (se 4 (by rfl) ⟨89364, by rfl⟩ : syracuseStep 953221 = 178729) (by norm_num)
theorem B953257 : Blo 846354 953257 := bbase (se 2 (by rfl) ⟨357471, by rfl⟩ : syracuseStep 953257 = 714943) (by norm_num)
theorem B1608653 : Blo 846354 1608653 := bbase (se 3 (by rfl) ⟨301622, by rfl⟩ : syracuseStep 1608653 = 603245) (by norm_num)
theorem B953293 : Blo 846354 953293 := bbase (se 3 (by rfl) ⟨178742, by rfl⟩ : syracuseStep 953293 = 357485) (by norm_num)
theorem B953329 : Blo 846354 953329 := bbase (se 2 (by rfl) ⟨357498, by rfl⟩ : syracuseStep 953329 = 714997) (by norm_num)
theorem B1018865 : Blo 846354 1018865 := bbase (se 2 (by rfl) ⟨382074, by rfl⟩ : syracuseStep 1018865 = 764149) (by norm_num)
theorem B2722805 : Blo 846354 2722805 := bbase (se 5 (by rfl) ⟨127631, by rfl⟩ : syracuseStep 2722805 = 255263) (by norm_num)
theorem B953365 : Blo 846354 953365 := bbase (se 6 (by rfl) ⟨22344, by rfl⟩ : syracuseStep 953365 = 44689) (by norm_num)
theorem B953401 : Blo 846354 953401 := bbase (se 2 (by rfl) ⟨357525, by rfl⟩ : syracuseStep 953401 = 715051) (by norm_num)
theorem B1018937 : Blo 846354 1018937 := bbase (se 2 (by rfl) ⟨382101, by rfl⟩ : syracuseStep 1018937 = 764203) (by norm_num)
theorem B1608797 : Blo 846354 1608797 := bbase (se 3 (by rfl) ⟨301649, by rfl⟩ : syracuseStep 1608797 = 603299) (by norm_num)
theorem B953437 : Blo 846354 953437 := bbase (se 3 (by rfl) ⟨178769, by rfl⟩ : syracuseStep 953437 = 357539) (by norm_num)
theorem B953473 : Blo 846354 953473 := bbase (se 2 (by rfl) ⟨357552, by rfl⟩ : syracuseStep 953473 = 715105) (by norm_num)
theorem B953509 : Blo 846354 953509 := bbase (se 4 (by rfl) ⟨89391, by rfl⟩ : syracuseStep 953509 = 178783) (by norm_num)
theorem B953545 : Blo 846354 953545 := bbase (se 2 (by rfl) ⟨357579, by rfl⟩ : syracuseStep 953545 = 715159) (by norm_num)
theorem B953581 : Blo 846354 953581 := bbase (se 3 (by rfl) ⟨178796, by rfl⟩ : syracuseStep 953581 = 357593) (by norm_num)
theorem B953617 : Blo 846354 953617 := bbase (se 2 (by rfl) ⟨357606, by rfl⟩ : syracuseStep 953617 = 715213) (by norm_num)
theorem B953653 : Blo 846354 953653 := bbase (se 5 (by rfl) ⟨44702, by rfl⟩ : syracuseStep 953653 = 89405) (by norm_num)
theorem B4820309 : Blo 846354 4820309 := bbase (se 11 (by rfl) ⟨3530, by rfl⟩ : syracuseStep 4820309 = 7061) (by norm_num)
theorem B953689 : Blo 846354 953689 := bbase (se 2 (by rfl) ⟨357633, by rfl⟩ : syracuseStep 953689 = 715267) (by norm_num)
theorem B1019245 : Blo 846354 1019245 := bbase (se 3 (by rfl) ⟨191108, by rfl⟩ : syracuseStep 1019245 = 382217) (by norm_num)
theorem B1609085 : Blo 846354 1609085 := bbase (se 3 (by rfl) ⟨301703, by rfl⟩ : syracuseStep 1609085 = 603407) (by norm_num)
theorem B953725 : Blo 846354 953725 := bbase (se 3 (by rfl) ⟨178823, by rfl⟩ : syracuseStep 953725 = 357647) (by norm_num)
theorem B953761 : Blo 846354 953761 := bbase (se 2 (by rfl) ⟨357660, by rfl⟩ : syracuseStep 953761 = 715321) (by norm_num)
theorem B953797 : Blo 846354 953797 := bbase (se 4 (by rfl) ⟨89418, by rfl⟩ : syracuseStep 953797 = 178837) (by norm_num)
theorem B953833 : Blo 846354 953833 := bbase (se 2 (by rfl) ⟨357687, by rfl⟩ : syracuseStep 953833 = 715375) (by norm_num)
theorem B953869 : Blo 846354 953869 := bbase (se 3 (by rfl) ⟨178850, by rfl⟩ : syracuseStep 953869 = 357701) (by norm_num)
theorem B1609237 : Blo 846354 1609237 := bbase (se 6 (by rfl) ⟨37716, by rfl⟩ : syracuseStep 1609237 = 75433) (by norm_num)
theorem B1019413 : Blo 846354 1019413 := bbase (se 6 (by rfl) ⟨23892, by rfl⟩ : syracuseStep 1019413 = 47785) (by norm_num)
theorem B953905 : Blo 846354 953905 := bbase (se 2 (by rfl) ⟨357714, by rfl⟩ : syracuseStep 953905 = 715429) (by norm_num)
theorem B1019461 : Blo 846354 1019461 := bbase (se 4 (by rfl) ⟨95574, by rfl⟩ : syracuseStep 1019461 = 191149) (by norm_num)
theorem B953941 : Blo 846354 953941 := bbase (se 8 (by rfl) ⟨5589, by rfl⟩ : syracuseStep 953941 = 11179) (by norm_num)
theorem B953977 : Blo 846354 953977 := bbase (se 2 (by rfl) ⟨357741, by rfl⟩ : syracuseStep 953977 = 715483) (by norm_num)
theorem B3214997 : Blo 846354 3214997 := bbase (se 6 (by rfl) ⟨75351, by rfl⟩ : syracuseStep 3214997 = 150703) (by norm_num)
theorem B954013 : Blo 846354 954013 := bbase (se 3 (by rfl) ⟨178877, by rfl⟩ : syracuseStep 954013 = 357755) (by norm_num)
theorem B3051173 : Blo 846354 3051173 := bbase (se 4 (by rfl) ⟨286047, by rfl⟩ : syracuseStep 3051173 = 572095) (by norm_num)
theorem B1019557 : Blo 846354 1019557 := bbase (se 4 (by rfl) ⟨95583, by rfl⟩ : syracuseStep 1019557 = 191167) (by norm_num)
theorem B1904309 : Blo 846354 1904309 := bbase (se 5 (by rfl) ⟨89264, by rfl⟩ : syracuseStep 1904309 = 178529) (by norm_num)
theorem B954049 : Blo 846354 954049 := bbase (se 2 (by rfl) ⟨357768, by rfl⟩ : syracuseStep 954049 = 715537) (by norm_num)
theorem B954085 : Blo 846354 954085 := bbase (se 4 (by rfl) ⟨89445, by rfl⟩ : syracuseStep 954085 = 178891) (by norm_num)
theorem B1904381 : Blo 846354 1904381 := bbase (se 3 (by rfl) ⟨357071, by rfl⟩ : syracuseStep 1904381 = 714143) (by norm_num)
theorem B954121 : Blo 846354 954121 := bbase (se 2 (by rfl) ⟨357795, by rfl⟩ : syracuseStep 954121 = 715591) (by norm_num)
theorem B954157 : Blo 846354 954157 := bbase (se 3 (by rfl) ⟨178904, by rfl⟩ : syracuseStep 954157 = 357809) (by norm_num)
theorem B1904453 : Blo 846354 1904453 := bbase (se 4 (by rfl) ⟨178542, by rfl⟩ : syracuseStep 1904453 = 357085) (by norm_num)
theorem B1609541 : Blo 846354 1609541 := bbase (se 4 (by rfl) ⟨150894, by rfl⟩ : syracuseStep 1609541 = 301789) (by norm_num)
theorem B954193 : Blo 846354 954193 := bbase (se 2 (by rfl) ⟨357822, by rfl⟩ : syracuseStep 954193 = 715645) (by norm_num)
theorem B954229 : Blo 846354 954229 := bbase (se 5 (by rfl) ⟨44729, by rfl⟩ : syracuseStep 954229 = 89459) (by norm_num)
theorem B1904525 : Blo 846354 1904525 := bbase (se 3 (by rfl) ⟨357098, by rfl⟩ : syracuseStep 1904525 = 714197) (by norm_num)
theorem B954265 : Blo 846354 954265 := bbase (se 2 (by rfl) ⟨357849, by rfl⟩ : syracuseStep 954265 = 715699) (by norm_num)
theorem B3215285 : Blo 846354 3215285 := bbase (se 5 (by rfl) ⟨150716, by rfl⟩ : syracuseStep 3215285 = 301433) (by norm_num)
theorem B954301 : Blo 846354 954301 := bbase (se 3 (by rfl) ⟨178931, by rfl⟩ : syracuseStep 954301 = 357863) (by norm_num)
theorem B1904597 : Blo 846354 1904597 := bbase (se 7 (by rfl) ⟨22319, by rfl⟩ : syracuseStep 1904597 = 44639) (by norm_num)
theorem B954337 : Blo 846354 954337 := bbase (se 2 (by rfl) ⟨357876, by rfl⟩ : syracuseStep 954337 = 715753) (by norm_num)
theorem B954373 : Blo 846354 954373 := bbase (se 4 (by rfl) ⟨89472, by rfl⟩ : syracuseStep 954373 = 178945) (by norm_num)
theorem B4296725 : Blo 846354 4296725 := bbase (se 6 (by rfl) ⟨100704, by rfl⟩ : syracuseStep 4296725 = 201409) (by norm_num)
theorem B1904669 : Blo 846354 1904669 := bbase (se 3 (by rfl) ⟨357125, by rfl⟩ : syracuseStep 1904669 = 714251) (by norm_num)
theorem B954409 : Blo 846354 954409 := bbase (se 2 (by rfl) ⟨357903, by rfl⟩ : syracuseStep 954409 = 715807) (by norm_num)
theorem B954445 : Blo 846354 954445 := bbase (se 3 (by rfl) ⟨178958, by rfl⟩ : syracuseStep 954445 = 357917) (by norm_num)
theorem B1904741 : Blo 846354 1904741 := bbase (se 4 (by rfl) ⟨178569, by rfl⟩ : syracuseStep 1904741 = 357139) (by norm_num)
theorem B954481 : Blo 846354 954481 := bbase (se 2 (by rfl) ⟨357930, by rfl⟩ : syracuseStep 954481 = 715861) (by norm_num)
theorem B954517 : Blo 846354 954517 := bbase (se 6 (by rfl) ⟨22371, by rfl⟩ : syracuseStep 954517 = 44743) (by norm_num)
theorem B1904813 : Blo 846354 1904813 := bbase (se 3 (by rfl) ⟨357152, by rfl⟩ : syracuseStep 1904813 = 714305) (by norm_num)
theorem B954553 : Blo 846354 954553 := bbase (se 2 (by rfl) ⟨357957, by rfl⟩ : syracuseStep 954553 = 715915) (by norm_num)
theorem B954589 : Blo 846354 954589 := bbase (se 3 (by rfl) ⟨178985, by rfl⟩ : syracuseStep 954589 = 357971) (by norm_num)
theorem B1020133 : Blo 846354 1020133 := bbase (se 4 (by rfl) ⟨95637, by rfl⟩ : syracuseStep 1020133 = 191275) (by norm_num)
theorem B1904885 : Blo 846354 1904885 := bbase (se 5 (by rfl) ⟨89291, by rfl⟩ : syracuseStep 1904885 = 178583) (by norm_num)
theorem B954625 : Blo 846354 954625 := bbase (se 2 (by rfl) ⟨357984, by rfl⟩ : syracuseStep 954625 = 715969) (by norm_num)
theorem B954661 : Blo 846354 954661 := bbase (se 4 (by rfl) ⟨89499, by rfl⟩ : syracuseStep 954661 = 178999) (by norm_num)
theorem B1904957 : Blo 846354 1904957 := bbase (se 3 (by rfl) ⟨357179, by rfl⟩ : syracuseStep 1904957 = 714359) (by norm_num)
theorem B2036029 : Blo 846354 2036029 := bbase (se 3 (by rfl) ⟨381755, by rfl⟩ : syracuseStep 2036029 = 763511) (by norm_num)
theorem B954697 : Blo 846354 954697 := bbase (se 2 (by rfl) ⟨358011, by rfl⟩ : syracuseStep 954697 = 716023) (by norm_num)
theorem B954733 : Blo 846354 954733 := bbase (se 3 (by rfl) ⟨179012, by rfl⟩ : syracuseStep 954733 = 358025) (by norm_num)
theorem B1905029 : Blo 846354 1905029 := bbase (se 4 (by rfl) ⟨178596, by rfl⟩ : syracuseStep 1905029 = 357193) (by norm_num)
theorem B954769 : Blo 846354 954769 := bbase (se 2 (by rfl) ⟨358038, by rfl⟩ : syracuseStep 954769 = 716077) (by norm_num)
theorem B954805 : Blo 846354 954805 := bbase (se 5 (by rfl) ⟨44756, by rfl⟩ : syracuseStep 954805 = 89513) (by norm_num)
theorem B1905101 : Blo 846354 1905101 := bbase (se 3 (by rfl) ⟨357206, by rfl⟩ : syracuseStep 1905101 = 714413) (by norm_num)
theorem B954841 : Blo 846354 954841 := bbase (se 2 (by rfl) ⟨358065, by rfl⟩ : syracuseStep 954841 = 716131) (by norm_num)
theorem B954877 : Blo 846354 954877 := bbase (se 3 (by rfl) ⟨179039, by rfl⟩ : syracuseStep 954877 = 358079) (by norm_num)
theorem B1905173 : Blo 846354 1905173 := bbase (se 6 (by rfl) ⟨44652, by rfl⟩ : syracuseStep 1905173 = 89305) (by norm_num)
theorem B954913 : Blo 846354 954913 := bbase (se 2 (by rfl) ⟨358092, by rfl⟩ : syracuseStep 954913 = 716185) (by norm_num)
theorem B1086005 : Blo 846354 1086005 := bbase (se 5 (by rfl) ⟨50906, by rfl⟩ : syracuseStep 1086005 = 101813) (by norm_num)
theorem B1610293 : Blo 846354 1610293 := bbase (se 5 (by rfl) ⟨75482, by rfl⟩ : syracuseStep 1610293 = 150965) (by norm_num)
theorem B954949 : Blo 846354 954949 := bbase (se 4 (by rfl) ⟨89526, by rfl⟩ : syracuseStep 954949 = 179053) (by norm_num)
theorem B7246421 : Blo 846354 7246421 := bbase (se 8 (by rfl) ⟨42459, by rfl⟩ : syracuseStep 7246421 = 84919) (by norm_num)
theorem B1905245 : Blo 846354 1905245 := bbase (se 3 (by rfl) ⟨357233, by rfl⟩ : syracuseStep 1905245 = 714467) (by norm_num)
theorem B954985 : Blo 846354 954985 := bbase (se 2 (by rfl) ⟨358119, by rfl⟩ : syracuseStep 954985 = 716239) (by norm_num)
theorem B955021 : Blo 846354 955021 := bbase (se 3 (by rfl) ⟨179066, by rfl⟩ : syracuseStep 955021 = 358133) (by norm_num)
theorem B11604629 : Blo 846354 11604629 := bbase (se 6 (by rfl) ⟨271983, by rfl⟩ : syracuseStep 11604629 = 543967) (by norm_num)
theorem B8163989 : Blo 846354 8163989 := bbase (se 6 (by rfl) ⟨191343, by rfl⟩ : syracuseStep 8163989 = 382687) (by norm_num)
theorem B1905317 : Blo 846354 1905317 := bbase (se 4 (by rfl) ⟨178623, by rfl⟩ : syracuseStep 1905317 = 357247) (by norm_num)
theorem B955057 : Blo 846354 955057 := bbase (se 2 (by rfl) ⟨358146, by rfl⟩ : syracuseStep 955057 = 716293) (by norm_num)
theorem B1610437 : Blo 846354 1610437 := bbase (se 4 (by rfl) ⟨150978, by rfl⟩ : syracuseStep 1610437 = 301957) (by norm_num)
theorem B6427349 : Blo 846354 6427349 := bbase (se 7 (by rfl) ⟨75320, by rfl⟩ : syracuseStep 6427349 = 150641) (by norm_num)
theorem B955093 : Blo 846354 955093 := bbase (se 7 (by rfl) ⟨11192, by rfl⟩ : syracuseStep 955093 = 22385) (by norm_num)
theorem B1905389 : Blo 846354 1905389 := bbase (se 3 (by rfl) ⟨357260, by rfl⟩ : syracuseStep 1905389 = 714521) (by norm_num)
theorem B955129 : Blo 846354 955129 := bbase (se 2 (by rfl) ⟨358173, by rfl⟩ : syracuseStep 955129 = 716347) (by norm_num)
theorem B955165 : Blo 846354 955165 := bbase (se 3 (by rfl) ⟨179093, by rfl⟩ : syracuseStep 955165 = 358187) (by norm_num)
theorem B1905461 : Blo 846354 1905461 := bbase (se 5 (by rfl) ⟨89318, by rfl⟩ : syracuseStep 1905461 = 178637) (by norm_num)
theorem B955201 : Blo 846354 955201 := bbase (se 2 (by rfl) ⟨358200, by rfl⟩ : syracuseStep 955201 = 716401) (by norm_num)
theorem B3674965 : Blo 846354 3674965 := bbase (se 9 (by rfl) ⟨10766, by rfl⟩ : syracuseStep 3674965 = 21533) (by norm_num)
theorem B1610597 : Blo 846354 1610597 := bbase (se 4 (by rfl) ⟨150993, by rfl⟩ : syracuseStep 1610597 = 301987) (by norm_num)
theorem B955237 : Blo 846354 955237 := bbase (se 4 (by rfl) ⟨89553, by rfl⟩ : syracuseStep 955237 = 179107) (by norm_num)
theorem B1905533 : Blo 846354 1905533 := bbase (se 3 (by rfl) ⟨357287, by rfl⟩ : syracuseStep 1905533 = 714575) (by norm_num)
theorem B955273 : Blo 846354 955273 := bbase (se 2 (by rfl) ⟨358227, by rfl⟩ : syracuseStep 955273 = 716455) (by norm_num)
theorem B955309 : Blo 846354 955309 := bbase (se 3 (by rfl) ⟨179120, by rfl⟩ : syracuseStep 955309 = 358241) (by norm_num)
theorem B1905605 : Blo 846354 1905605 := bbase (se 4 (by rfl) ⟨178650, by rfl⟩ : syracuseStep 1905605 = 357301) (by norm_num)
theorem B955345 : Blo 846354 955345 := bbase (se 2 (by rfl) ⟨358254, by rfl⟩ : syracuseStep 955345 = 716509) (by norm_num)
theorem B1741805 : Blo 846354 1741805 := bbase (se 3 (by rfl) ⟨326588, by rfl⟩ : syracuseStep 1741805 = 653177) (by norm_num)
theorem B1610741 : Blo 846354 1610741 := bbase (se 5 (by rfl) ⟨75503, by rfl⟩ : syracuseStep 1610741 = 151007) (by norm_num)
theorem B955381 : Blo 846354 955381 := bbase (se 5 (by rfl) ⟨44783, by rfl⟩ : syracuseStep 955381 = 89567) (by norm_num)
theorem B1905677 : Blo 846354 1905677 := bbase (se 3 (by rfl) ⟨357314, by rfl⟩ : syracuseStep 1905677 = 714629) (by norm_num)
theorem B955417 : Blo 846354 955417 := bbase (se 2 (by rfl) ⟨358281, by rfl⟩ : syracuseStep 955417 = 716563) (by norm_num)
theorem B955453 : Blo 846354 955453 := bbase (se 3 (by rfl) ⟨179147, by rfl⟩ : syracuseStep 955453 = 358295) (by norm_num)
theorem B1905749 : Blo 846354 1905749 := bbase (se 8 (by rfl) ⟨11166, by rfl⟩ : syracuseStep 1905749 = 22333) (by norm_num)
theorem B3216469 : Blo 846354 3216469 := bbase (se 8 (by rfl) ⟨18846, by rfl⟩ : syracuseStep 3216469 = 37693) (by norm_num)
theorem B955489 : Blo 846354 955489 := bbase (se 2 (by rfl) ⟨358308, by rfl⟩ : syracuseStep 955489 = 716617) (by norm_num)
theorem B955525 : Blo 846354 955525 := bbase (se 4 (by rfl) ⟨89580, by rfl⟩ : syracuseStep 955525 = 179161) (by norm_num)
theorem B1905821 : Blo 846354 1905821 := bbase (se 3 (by rfl) ⟨357341, by rfl⟩ : syracuseStep 1905821 = 714683) (by norm_num)
theorem B955561 : Blo 846354 955561 := bbase (se 2 (by rfl) ⟨358335, by rfl⟩ : syracuseStep 955561 = 716671) (by norm_num)
theorem B955597 : Blo 846354 955597 := bbase (se 3 (by rfl) ⟨179174, by rfl⟩ : syracuseStep 955597 = 358349) (by norm_num)
theorem B1021133 : Blo 846354 1021133 := bbase (se 3 (by rfl) ⟨191462, by rfl⟩ : syracuseStep 1021133 = 382925) (by norm_num)
theorem B1905893 : Blo 846354 1905893 := bbase (se 4 (by rfl) ⟨178677, by rfl⟩ : syracuseStep 1905893 = 357355) (by norm_num)
theorem B955633 : Blo 846354 955633 := bbase (se 2 (by rfl) ⟨358362, by rfl⟩ : syracuseStep 955633 = 716725) (by norm_num)
theorem B2036981 : Blo 846354 2036981 := bbase (se 5 (by rfl) ⟨95483, by rfl⟩ : syracuseStep 2036981 = 190967) (by norm_num)
theorem B1021181 : Blo 846354 1021181 := bbase (se 3 (by rfl) ⟨191471, by rfl⟩ : syracuseStep 1021181 = 382943) (by norm_num)
theorem B1611029 : Blo 846354 1611029 := bbase (se 6 (by rfl) ⟨37758, by rfl⟩ : syracuseStep 1611029 = 75517) (by norm_num)
theorem B955669 : Blo 846354 955669 := bbase (se 6 (by rfl) ⟨22398, by rfl⟩ : syracuseStep 955669 = 44797) (by norm_num)
theorem B4298021 : Blo 846354 4298021 := bbase (se 4 (by rfl) ⟨402939, by rfl⟩ : syracuseStep 4298021 = 805879) (by norm_num)
theorem B1905965 : Blo 846354 1905965 := bbase (se 3 (by rfl) ⟨357368, by rfl⟩ : syracuseStep 1905965 = 714737) (by norm_num)
theorem B2037037 : Blo 846354 2037037 := bbase (se 3 (by rfl) ⟨381944, by rfl⟩ : syracuseStep 2037037 = 763889) (by norm_num)
theorem B955705 : Blo 846354 955705 := bbase (se 2 (by rfl) ⟨358389, by rfl⟩ : syracuseStep 955705 = 716779) (by norm_num)
theorem B955741 : Blo 846354 955741 := bbase (se 3 (by rfl) ⟨179201, by rfl⟩ : syracuseStep 955741 = 358403) (by norm_num)
theorem B1906037 : Blo 846354 1906037 := bbase (se 5 (by rfl) ⟨89345, by rfl⟩ : syracuseStep 1906037 = 178691) (by norm_num)
theorem B955777 : Blo 846354 955777 := bbase (se 2 (by rfl) ⟨358416, by rfl⟩ : syracuseStep 955777 = 716833) (by norm_num)
theorem B3216773 : Blo 846354 3216773 := bbase (se 4 (by rfl) ⟨301572, by rfl⟩ : syracuseStep 3216773 = 603145) (by norm_num)
theorem B955813 : Blo 846354 955813 := bbase (se 4 (by rfl) ⟨89607, by rfl⟩ : syracuseStep 955813 = 179215) (by norm_num)
theorem B1611181 : Blo 846354 1611181 := bbase (se 3 (by rfl) ⟨302096, by rfl⟩ : syracuseStep 1611181 = 604193) (by norm_num)
theorem B1906109 : Blo 846354 1906109 := bbase (se 3 (by rfl) ⟨357395, by rfl⟩ : syracuseStep 1906109 = 714791) (by norm_num)
theorem B955849 : Blo 846354 955849 := bbase (se 2 (by rfl) ⟨358443, by rfl⟩ : syracuseStep 955849 = 716887) (by norm_num)
theorem B955885 : Blo 846354 955885 := bbase (se 3 (by rfl) ⟨179228, by rfl⟩ : syracuseStep 955885 = 358457) (by norm_num)
theorem B4822517 : Blo 846354 4822517 := bbase (se 5 (by rfl) ⟨226055, by rfl⟩ : syracuseStep 4822517 = 452111) (by norm_num)
theorem B1906181 : Blo 846354 1906181 := bbase (se 4 (by rfl) ⟨178704, by rfl⟩ : syracuseStep 1906181 = 357409) (by norm_num)
theorem B955921 : Blo 846354 955921 := bbase (se 2 (by rfl) ⟨358470, by rfl⟩ : syracuseStep 955921 = 716941) (by norm_num)
theorem B955957 : Blo 846354 955957 := bbase (se 5 (by rfl) ⟨44810, by rfl⟩ : syracuseStep 955957 = 89621) (by norm_num)
theorem B1906253 : Blo 846354 1906253 := bbase (se 3 (by rfl) ⟨357422, by rfl⟩ : syracuseStep 1906253 = 714845) (by norm_num)
theorem B955993 : Blo 846354 955993 := bbase (se 2 (by rfl) ⟨358497, by rfl⟩ : syracuseStep 955993 = 716995) (by norm_num)
theorem B1939061 : Blo 846354 1939061 := bbase (se 5 (by rfl) ⟨90893, by rfl⟩ : syracuseStep 1939061 = 181787) (by norm_num)
theorem B956029 : Blo 846354 956029 := bbase (se 3 (by rfl) ⟨179255, by rfl⟩ : syracuseStep 956029 = 358511) (by norm_num)
theorem B1906325 : Blo 846354 1906325 := bbase (se 6 (by rfl) ⟨44679, by rfl⟩ : syracuseStep 1906325 = 89359) (by norm_num)
theorem B956065 : Blo 846354 956065 := bbase (se 2 (by rfl) ⟨358524, by rfl⟩ : syracuseStep 956065 = 717049) (by norm_num)
theorem B2037413 : Blo 846354 2037413 := bbase (se 4 (by rfl) ⟨191007, by rfl⟩ : syracuseStep 2037413 = 382015) (by norm_num)
theorem B956101 : Blo 846354 956101 := bbase (se 4 (by rfl) ⟨89634, by rfl⟩ : syracuseStep 956101 = 179269) (by norm_num)
theorem B1119949 : Blo 846354 1119949 := bbase (se 3 (by rfl) ⟨209990, by rfl⟩ : syracuseStep 1119949 = 419981) (by norm_num)
theorem B1906397 : Blo 846354 1906397 := bbase (se 3 (by rfl) ⟨357449, by rfl⟩ : syracuseStep 1906397 = 714899) (by norm_num)
theorem B1611485 : Blo 846354 1611485 := bbase (se 3 (by rfl) ⟨302153, by rfl⟩ : syracuseStep 1611485 = 604307) (by norm_num)
theorem B956137 : Blo 846354 956137 := bbase (se 2 (by rfl) ⟨358551, by rfl⟩ : syracuseStep 956137 = 717103) (by norm_num)
theorem B956173 : Blo 846354 956173 := bbase (se 3 (by rfl) ⟨179282, by rfl⟩ : syracuseStep 956173 = 358565) (by norm_num)
theorem B1906469 : Blo 846354 1906469 := bbase (se 4 (by rfl) ⟨178731, by rfl⟩ : syracuseStep 1906469 = 357463) (by norm_num)
theorem B956209 : Blo 846354 956209 := bbase (se 2 (by rfl) ⟨358578, by rfl⟩ : syracuseStep 956209 = 717157) (by norm_num)
theorem B956245 : Blo 846354 956245 := bbase (se 9 (by rfl) ⟨2801, by rfl⟩ : syracuseStep 956245 = 5603) (by norm_num)
theorem B1906541 : Blo 846354 1906541 := bbase (se 3 (by rfl) ⟨357476, by rfl⟩ : syracuseStep 1906541 = 714953) (by norm_num)
theorem B956281 : Blo 846354 956281 := bbase (se 2 (by rfl) ⟨358605, by rfl⟩ : syracuseStep 956281 = 717211) (by norm_num)
theorem B1087381 : Blo 846354 1087381 := bbase (se 6 (by rfl) ⟨25485, by rfl⟩ : syracuseStep 1087381 = 50971) (by norm_num)
theorem B2037653 : Blo 846354 2037653 := bbase (se 6 (by rfl) ⟨47757, by rfl⟩ : syracuseStep 2037653 = 95515) (by norm_num)
theorem B956317 : Blo 846354 956317 := bbase (se 3 (by rfl) ⟨179309, by rfl⟩ : syracuseStep 956317 = 358619) (by norm_num)
theorem B2856869 : Blo 846354 2856869 := bbase (se 4 (by rfl) ⟨267831, by rfl⟩ : syracuseStep 2856869 = 535663) (by norm_num)
theorem B1906613 : Blo 846354 1906613 := bbase (se 5 (by rfl) ⟨89372, by rfl⟩ : syracuseStep 1906613 = 178745) (by norm_num)
theorem B956353 : Blo 846354 956353 := bbase (se 2 (by rfl) ⟨358632, by rfl⟩ : syracuseStep 956353 = 717265) (by norm_num)
theorem B5806037 : Blo 846354 5806037 := bbase (se 7 (by rfl) ⟨68039, by rfl⟩ : syracuseStep 5806037 = 136079) (by norm_num)
theorem B956389 : Blo 846354 956389 := bbase (se 4 (by rfl) ⟨89661, by rfl⟩ : syracuseStep 956389 = 179323) (by norm_num)
theorem B1906685 : Blo 846354 1906685 := bbase (se 3 (by rfl) ⟨357503, by rfl⟩ : syracuseStep 1906685 = 715007) (by norm_num)
theorem B956425 : Blo 846354 956425 := bbase (se 2 (by rfl) ⟨358659, by rfl⟩ : syracuseStep 956425 = 717319) (by norm_num)
theorem B956461 : Blo 846354 956461 := bbase (se 3 (by rfl) ⟨179336, by rfl⟩ : syracuseStep 956461 = 358673) (by norm_num)
theorem B1906757 : Blo 846354 1906757 := bbase (se 4 (by rfl) ⟨178758, by rfl⟩ : syracuseStep 1906757 = 357517) (by norm_num)
theorem B956497 : Blo 846354 956497 := bbase (se 2 (by rfl) ⟨358686, by rfl⟩ : syracuseStep 956497 = 717373) (by norm_num)
theorem B3479669 : Blo 846354 3479669 := bbase (se 5 (by rfl) ⟨163109, by rfl⟩ : syracuseStep 3479669 = 326219) (by norm_num)
theorem B956533 : Blo 846354 956533 := bbase (se 5 (by rfl) ⟨44837, by rfl⟩ : syracuseStep 956533 = 89675) (by norm_num)
theorem B1906829 : Blo 846354 1906829 := bbase (se 3 (by rfl) ⟨357530, by rfl⟩ : syracuseStep 1906829 = 715061) (by norm_num)
theorem B956569 : Blo 846354 956569 := bbase (se 2 (by rfl) ⟨358713, by rfl⟩ : syracuseStep 956569 = 717427) (by norm_num)
theorem B956605 : Blo 846354 956605 := bbase (se 3 (by rfl) ⟨179363, by rfl⟩ : syracuseStep 956605 = 358727) (by norm_num)
theorem B1808581 : Blo 846354 1808581 := bbase (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) (by norm_num)
theorem B1906901 : Blo 846354 1906901 := bbase (se 7 (by rfl) ⟨22346, by rfl⟩ : syracuseStep 1906901 = 44693) (by norm_num)
theorem B956641 : Blo 846354 956641 := bbase (se 2 (by rfl) ⟨358740, by rfl⟩ : syracuseStep 956641 = 717481) (by norm_num)
theorem B1448165 : Blo 846354 1448165 := bbase (se 4 (by rfl) ⟨135765, by rfl⟩ : syracuseStep 1448165 = 271531) (by norm_num)
theorem B1906973 : Blo 846354 1906973 := bbase (se 3 (by rfl) ⟨357557, by rfl⟩ : syracuseStep 1906973 = 715115) (by norm_num)
theorem B2857301 : Blo 846354 2857301 := bbase (se 10 (by rfl) ⟨4185, by rfl⟩ : syracuseStep 2857301 = 8371) (by norm_num)
theorem B1907045 : Blo 846354 1907045 := bbase (se 4 (by rfl) ⟨178785, by rfl⟩ : syracuseStep 1907045 = 357571) (by norm_num)
theorem B1087873 : Blo 846354 1087873 := bbase (se 2 (by rfl) ⟨407952, by rfl⟩ : syracuseStep 1087873 = 815905) (by norm_num)
theorem B1907117 : Blo 846354 1907117 := bbase (se 3 (by rfl) ⟨357584, by rfl⟩ : syracuseStep 1907117 = 715169) (by norm_num)
theorem B1612237 : Blo 846354 1612237 := bbase (se 3 (by rfl) ⟨302294, by rfl⟩ : syracuseStep 1612237 = 604589) (by norm_num)
theorem B1907189 : Blo 846354 1907189 := bbase (se 5 (by rfl) ⟨89399, by rfl⟩ : syracuseStep 1907189 = 178799) (by norm_num)
theorem B4299317 : Blo 846354 4299317 := bbase (se 5 (by rfl) ⟨201530, by rfl⟩ : syracuseStep 4299317 = 403061) (by norm_num)
theorem B1907261 : Blo 846354 1907261 := bbase (se 3 (by rfl) ⟨357611, by rfl⟩ : syracuseStep 1907261 = 715223) (by norm_num)
theorem B1612381 : Blo 846354 1612381 := bbase (se 3 (by rfl) ⟨302321, by rfl⟩ : syracuseStep 1612381 = 604643) (by norm_num)
theorem B1907333 : Blo 846354 1907333 := bbase (se 4 (by rfl) ⟨178812, by rfl⟩ : syracuseStep 1907333 = 357625) (by norm_num)
theorem B1907405 : Blo 846354 1907405 := bbase (se 3 (by rfl) ⟨357638, by rfl⟩ : syracuseStep 1907405 = 715277) (by norm_num)
theorem B1612541 : Blo 846354 1612541 := bbase (se 3 (by rfl) ⟨302351, by rfl⟩ : syracuseStep 1612541 = 604703) (by norm_num)
theorem B2857733 : Blo 846354 2857733 := bbase (se 4 (by rfl) ⟨267912, by rfl⟩ : syracuseStep 2857733 = 535825) (by norm_num)
theorem B1907477 : Blo 846354 1907477 := bbase (se 6 (by rfl) ⟨44706, by rfl⟩ : syracuseStep 1907477 = 89413) (by norm_num)
theorem B4070213 : Blo 846354 4070213 := bbase (se 4 (by rfl) ⟨381582, by rfl⟩ : syracuseStep 4070213 = 763165) (by norm_num)
theorem B1907549 : Blo 846354 1907549 := bbase (se 3 (by rfl) ⟨357665, by rfl⟩ : syracuseStep 1907549 = 715331) (by norm_num)
theorem B1612685 : Blo 846354 1612685 := bbase (se 3 (by rfl) ⟨302378, by rfl⟩ : syracuseStep 1612685 = 604757) (by norm_num)
theorem B1907621 : Blo 846354 1907621 := bbase (se 4 (by rfl) ⟨178839, by rfl⟩ : syracuseStep 1907621 = 357679) (by norm_num)
theorem B1907693 : Blo 846354 1907693 := bbase (se 3 (by rfl) ⟨357692, by rfl⟩ : syracuseStep 1907693 = 715385) (by norm_num)
theorem B1514501 : Blo 846354 1514501 := bbase (se 4 (by rfl) ⟨141984, by rfl⟩ : syracuseStep 1514501 = 283969) (by norm_num)
theorem B1907765 : Blo 846354 1907765 := bbase (se 5 (by rfl) ⟨89426, by rfl⟩ : syracuseStep 1907765 = 178853) (by norm_num)
theorem B5446709 : Blo 846354 5446709 := bbase (se 5 (by rfl) ⟨255314, by rfl⟩ : syracuseStep 5446709 = 510629) (by norm_num)
theorem B1809469 : Blo 846354 1809469 := bbase (se 3 (by rfl) ⟨339275, by rfl⟩ : syracuseStep 1809469 = 678551) (by norm_num)
theorem B1907837 : Blo 846354 1907837 := bbase (se 3 (by rfl) ⟨357719, by rfl⟩ : syracuseStep 1907837 = 715439) (by norm_num)
theorem B1612973 : Blo 846354 1612973 := bbase (se 3 (by rfl) ⟨302432, by rfl⟩ : syracuseStep 1612973 = 604865) (by norm_num)
theorem B2858165 : Blo 846354 2858165 := bbase (se 5 (by rfl) ⟨133976, by rfl⟩ : syracuseStep 2858165 = 267953) (by norm_num)
theorem B1907909 : Blo 846354 1907909 := bbase (se 4 (by rfl) ⟨178866, by rfl⟩ : syracuseStep 1907909 = 357733) (by norm_num)
theorem B1907981 : Blo 846354 1907981 := bbase (se 3 (by rfl) ⟨357746, by rfl⟩ : syracuseStep 1907981 = 715493) (by norm_num)
theorem B1613125 : Blo 846354 1613125 := bbase (se 4 (by rfl) ⟨151230, by rfl⟩ : syracuseStep 1613125 = 302461) (by norm_num)
theorem B859469 : Blo 846354 859469 := bbase (se 3 (by rfl) ⟨161150, by rfl⟩ : syracuseStep 859469 = 322301) (by norm_num)
theorem B1908053 : Blo 846354 1908053 := bbase (se 11 (by rfl) ⟨1397, by rfl⟩ : syracuseStep 1908053 = 2795) (by norm_num)
theorem B1908125 : Blo 846354 1908125 := bbase (se 3 (by rfl) ⟨357773, by rfl⟩ : syracuseStep 1908125 = 715547) (by norm_num)
theorem B3218885 : Blo 846354 3218885 := bbase (se 4 (by rfl) ⟨301770, by rfl⟩ : syracuseStep 3218885 = 603541) (by norm_num)
theorem B1908197 : Blo 846354 1908197 := bbase (se 4 (by rfl) ⟨178893, by rfl⟩ : syracuseStep 1908197 = 357787) (by norm_num)
theorem B1809965 : Blo 846354 1809965 := bbase (se 3 (by rfl) ⟨339368, by rfl⟩ : syracuseStep 1809965 = 678737) (by norm_num)
theorem B1908269 : Blo 846354 1908269 := bbase (se 3 (by rfl) ⟨357800, by rfl⟩ : syracuseStep 1908269 = 715601) (by norm_num)
theorem B6889013 : Blo 846354 6889013 := bbase (se 5 (by rfl) ⟨322922, by rfl⟩ : syracuseStep 6889013 = 645845) (by norm_num)
theorem B2858597 : Blo 846354 2858597 := bbase (se 4 (by rfl) ⟨267993, by rfl⟩ : syracuseStep 2858597 = 535987) (by norm_num)
theorem B1908341 : Blo 846354 1908341 := bbase (se 5 (by rfl) ⟨89453, by rfl⟩ : syracuseStep 1908341 = 178907) (by norm_num)
theorem B1613429 : Blo 846354 1613429 := bbase (se 5 (by rfl) ⟨75629, by rfl⟩ : syracuseStep 1613429 = 151259) (by norm_num)
theorem B1908413 : Blo 846354 1908413 := bbase (se 3 (by rfl) ⟨357827, by rfl⟩ : syracuseStep 1908413 = 715655) (by norm_num)
theorem B3219173 : Blo 846354 3219173 := bbase (se 4 (by rfl) ⟨301797, by rfl⟩ : syracuseStep 3219173 = 603595) (by norm_num)
theorem B1908485 : Blo 846354 1908485 := bbase (se 4 (by rfl) ⟨178920, by rfl⟩ : syracuseStep 1908485 = 357841) (by norm_num)
theorem B4300613 : Blo 846354 4300613 := bbase (se 4 (by rfl) ⟨403182, by rfl⟩ : syracuseStep 4300613 = 806365) (by norm_num)
theorem B1908557 : Blo 846354 1908557 := bbase (se 3 (by rfl) ⟨357854, by rfl⟩ : syracuseStep 1908557 = 715709) (by norm_num)
theorem B1908629 : Blo 846354 1908629 := bbase (se 6 (by rfl) ⟨44733, by rfl⟩ : syracuseStep 1908629 = 89467) (by norm_num)
theorem B1908701 : Blo 846354 1908701 := bbase (se 3 (by rfl) ⟨357881, by rfl⟩ : syracuseStep 1908701 = 715763) (by norm_num)
theorem B1089505 : Blo 846354 1089505 := bbase (se 2 (by rfl) ⟨408564, by rfl⟩ : syracuseStep 1089505 = 817129) (by norm_num)
theorem B2859029 : Blo 846354 2859029 := bbase (se 6 (by rfl) ⟨67008, by rfl⟩ : syracuseStep 2859029 = 134017) (by norm_num)
theorem B1908773 : Blo 846354 1908773 := bbase (se 4 (by rfl) ⟨178947, by rfl⟩ : syracuseStep 1908773 = 357895) (by norm_num)
theorem B1908845 : Blo 846354 1908845 := bbase (se 3 (by rfl) ⟨357908, by rfl⟩ : syracuseStep 1908845 = 715817) (by norm_num)
theorem B1908917 : Blo 846354 1908917 := bbase (se 5 (by rfl) ⟨89480, by rfl⟩ : syracuseStep 1908917 = 178961) (by norm_num)
theorem B1908989 : Blo 846354 1908989 := bbase (se 3 (by rfl) ⟨357935, by rfl⟩ : syracuseStep 1908989 = 715871) (by norm_num)
theorem B1909061 : Blo 846354 1909061 := bbase (se 4 (by rfl) ⟨178974, by rfl⟩ : syracuseStep 1909061 = 357949) (by norm_num)
theorem B1614181 : Blo 846354 1614181 := bbase (se 4 (by rfl) ⟨151329, by rfl⟩ : syracuseStep 1614181 = 302659) (by norm_num)
theorem B1810829 : Blo 846354 1810829 := bbase (se 3 (by rfl) ⟨339530, by rfl⟩ : syracuseStep 1810829 = 679061) (by norm_num)
theorem B1909133 : Blo 846354 1909133 := bbase (se 3 (by rfl) ⟨357962, by rfl⟩ : syracuseStep 1909133 = 715925) (by norm_num)
theorem B4071845 : Blo 846354 4071845 := bbase (se 4 (by rfl) ⟨381735, by rfl⟩ : syracuseStep 4071845 = 763471) (by norm_num)
theorem B2859461 : Blo 846354 2859461 := bbase (se 4 (by rfl) ⟨268074, by rfl⟩ : syracuseStep 2859461 = 536149) (by norm_num)
theorem B1909205 : Blo 846354 1909205 := bbase (se 7 (by rfl) ⟨22373, by rfl⟩ : syracuseStep 1909205 = 44747) (by norm_num)
theorem B1614325 : Blo 846354 1614325 := bbase (se 5 (by rfl) ⟨75671, by rfl⟩ : syracuseStep 1614325 = 151343) (by norm_num)
theorem B1810973 : Blo 846354 1810973 := bbase (se 3 (by rfl) ⟨339557, by rfl⟩ : syracuseStep 1810973 = 679115) (by norm_num)
theorem B1909277 : Blo 846354 1909277 := bbase (se 3 (by rfl) ⟨357989, by rfl⟩ : syracuseStep 1909277 = 715979) (by norm_num)
theorem B1909349 : Blo 846354 1909349 := bbase (se 4 (by rfl) ⟨179001, by rfl⟩ : syracuseStep 1909349 = 358003) (by norm_num)
theorem B1909421 : Blo 846354 1909421 := bbase (se 3 (by rfl) ⟨358016, by rfl⟩ : syracuseStep 1909421 = 716033) (by norm_num)
theorem B1909493 : Blo 846354 1909493 := bbase (se 5 (by rfl) ⟨89507, by rfl⟩ : syracuseStep 1909493 = 179015) (by norm_num)
theorem B5219093 : Blo 846354 5219093 := bbase (se 6 (by rfl) ⟨122322, by rfl⟩ : syracuseStep 5219093 = 244645) (by norm_num)
theorem B1909565 : Blo 846354 1909565 := bbase (se 3 (by rfl) ⟨358043, by rfl⟩ : syracuseStep 1909565 = 716087) (by norm_num)
theorem B2859893 : Blo 846354 2859893 := bbase (se 5 (by rfl) ⟨134057, by rfl⟩ : syracuseStep 2859893 = 268115) (by norm_num)
theorem B3220357 : Blo 846354 3220357 := bbase (se 4 (by rfl) ⟨301908, by rfl⟩ : syracuseStep 3220357 = 603817) (by norm_num)
theorem B1909637 : Blo 846354 1909637 := bbase (se 4 (by rfl) ⟨179028, by rfl⟩ : syracuseStep 1909637 = 358057) (by norm_num)
theorem B2171845 : Blo 846354 2171845 := bbase (se 4 (by rfl) ⟨203610, by rfl⟩ : syracuseStep 2171845 = 407221) (by norm_num)
theorem B1909709 : Blo 846354 1909709 := bbase (se 3 (by rfl) ⟨358070, by rfl⟩ : syracuseStep 1909709 = 716141) (by norm_num)
theorem B2040805 : Blo 846354 2040805 := bbase (se 4 (by rfl) ⟨191325, by rfl⟩ : syracuseStep 2040805 = 382651) (by norm_num)
theorem B1909781 : Blo 846354 1909781 := bbase (se 6 (by rfl) ⟨44760, by rfl⟩ : syracuseStep 1909781 = 89521) (by norm_num)
theorem B4301909 : Blo 846354 4301909 := bbase (se 8 (by rfl) ⟨25206, by rfl⟩ : syracuseStep 4301909 = 50413) (by norm_num)
theorem B1909853 : Blo 846354 1909853 := bbase (se 3 (by rfl) ⟨358097, by rfl⟩ : syracuseStep 1909853 = 716195) (by norm_num)
theorem B1909925 : Blo 846354 1909925 := bbase (se 4 (by rfl) ⟨179055, by rfl⟩ : syracuseStep 1909925 = 358111) (by norm_num)
theorem B3220661 : Blo 846354 3220661 := bbase (se 5 (by rfl) ⟨150968, by rfl⟩ : syracuseStep 3220661 = 301937) (by norm_num)
theorem B1909997 : Blo 846354 1909997 := bbase (se 3 (by rfl) ⟨358124, by rfl⟩ : syracuseStep 1909997 = 716249) (by norm_num)
theorem B3056885 : Blo 846354 3056885 := bbase (se 5 (by rfl) ⟨143291, by rfl⟩ : syracuseStep 3056885 = 286583) (by norm_num)
theorem B1811717 : Blo 846354 1811717 := bbase (se 4 (by rfl) ⟨169848, by rfl⟩ : syracuseStep 1811717 = 339697) (by norm_num)
theorem B2860325 : Blo 846354 2860325 := bbase (se 4 (by rfl) ⟨268155, by rfl⟩ : syracuseStep 2860325 = 536311) (by norm_num)
theorem B1910069 : Blo 846354 1910069 := bbase (se 5 (by rfl) ⟨89534, by rfl⟩ : syracuseStep 1910069 = 179069) (by norm_num)
theorem B1910141 : Blo 846354 1910141 := bbase (se 3 (by rfl) ⟨358151, by rfl⟩ : syracuseStep 1910141 = 716303) (by norm_num)
theorem B1910213 : Blo 846354 1910213 := bbase (se 4 (by rfl) ⟨179082, by rfl⟩ : syracuseStep 1910213 = 358165) (by norm_num)
theorem B4957685 : Blo 846354 4957685 := bbase (se 5 (by rfl) ⟨232391, by rfl⟩ : syracuseStep 4957685 = 464783) (by norm_num)
theorem B1910285 : Blo 846354 1910285 := bbase (se 3 (by rfl) ⟨358178, by rfl⟩ : syracuseStep 1910285 = 716357) (by norm_num)
theorem B1910357 : Blo 846354 1910357 := bbase (se 8 (by rfl) ⟨11193, by rfl⟩ : syracuseStep 1910357 = 22387) (by norm_num)
theorem B1910429 : Blo 846354 1910429 := bbase (se 3 (by rfl) ⟨358205, by rfl⟩ : syracuseStep 1910429 = 716411) (by norm_num)
theorem B2860757 : Blo 846354 2860757 := bbase (se 7 (by rfl) ⟨33524, by rfl⟩ : syracuseStep 2860757 = 67049) (by norm_num)
theorem B1910501 : Blo 846354 1910501 := bbase (se 4 (by rfl) ⟨179109, by rfl⟩ : syracuseStep 1910501 = 358219) (by norm_num)
theorem B1910573 : Blo 846354 1910573 := bbase (se 3 (by rfl) ⟨358232, by rfl⟩ : syracuseStep 1910573 = 716465) (by norm_num)
theorem B1910645 : Blo 846354 1910645 := bbase (se 5 (by rfl) ⟨89561, by rfl⟩ : syracuseStep 1910645 = 179123) (by norm_num)
theorem B1910717 : Blo 846354 1910717 := bbase (se 3 (by rfl) ⟨358259, by rfl⟩ : syracuseStep 1910717 = 716519) (by norm_num)
theorem B1812469 : Blo 846354 1812469 := bbase (se 5 (by rfl) ⟨84959, by rfl⟩ : syracuseStep 1812469 = 169919) (by norm_num)
theorem B1910789 : Blo 846354 1910789 := bbase (se 4 (by rfl) ⟨179136, by rfl⟩ : syracuseStep 1910789 = 358273) (by norm_num)
theorem B1910861 : Blo 846354 1910861 := bbase (se 3 (by rfl) ⟨358286, by rfl⟩ : syracuseStep 1910861 = 716573) (by norm_num)
theorem B3057749 : Blo 846354 3057749 := bbase (se 8 (by rfl) ⟨17916, by rfl⟩ : syracuseStep 3057749 = 35833) (by norm_num)
theorem B2861189 : Blo 846354 2861189 := bbase (se 4 (by rfl) ⟨268236, by rfl⟩ : syracuseStep 2861189 = 536473) (by norm_num)
theorem B1812613 : Blo 846354 1812613 := bbase (se 4 (by rfl) ⟨169932, by rfl⟩ : syracuseStep 1812613 = 339865) (by norm_num)
theorem B1910933 : Blo 846354 1910933 := bbase (se 6 (by rfl) ⟨44787, by rfl⟩ : syracuseStep 1910933 = 89575) (by norm_num)
theorem B1911005 : Blo 846354 1911005 := bbase (se 3 (by rfl) ⟨358313, by rfl⟩ : syracuseStep 1911005 = 716627) (by norm_num)
theorem B1911077 : Blo 846354 1911077 := bbase (se 4 (by rfl) ⟨179163, by rfl⟩ : syracuseStep 1911077 = 358327) (by norm_num)
theorem B2042189 : Blo 846354 2042189 := bbase (se 3 (by rfl) ⟨382910, by rfl⟩ : syracuseStep 2042189 = 765821) (by norm_num)
theorem B4303205 : Blo 846354 4303205 := bbase (se 4 (by rfl) ⟨403425, by rfl⟩ : syracuseStep 4303205 = 806851) (by norm_num)
theorem B1911149 : Blo 846354 1911149 := bbase (se 3 (by rfl) ⟨358340, by rfl⟩ : syracuseStep 1911149 = 716681) (by norm_num)
theorem B3058037 : Blo 846354 3058037 := bbase (se 5 (by rfl) ⟨143345, by rfl⟩ : syracuseStep 3058037 = 286691) (by norm_num)
theorem B1911221 : Blo 846354 1911221 := bbase (se 5 (by rfl) ⟨89588, by rfl⟩ : syracuseStep 1911221 = 179177) (by norm_num)
theorem B1812989 : Blo 846354 1812989 := bbase (se 3 (by rfl) ⟨339935, by rfl⟩ : syracuseStep 1812989 = 679871) (by norm_num)
theorem B1911293 : Blo 846354 1911293 := bbase (se 3 (by rfl) ⟨358367, by rfl⟩ : syracuseStep 1911293 = 716735) (by norm_num)
theorem B2042381 : Blo 846354 2042381 := bbase (se 3 (by rfl) ⟨382946, by rfl⟩ : syracuseStep 2042381 = 765893) (by norm_num)
theorem B2861621 : Blo 846354 2861621 := bbase (se 5 (by rfl) ⟨134138, by rfl⟩ : syracuseStep 2861621 = 268277) (by norm_num)
theorem B1911365 : Blo 846354 1911365 := bbase (se 4 (by rfl) ⟨179190, by rfl⟩ : syracuseStep 1911365 = 358381) (by norm_num)
theorem B3615317 : Blo 846354 3615317 := bbase (se 8 (by rfl) ⟨21183, by rfl⟩ : syracuseStep 3615317 = 42367) (by norm_num)
theorem B1911437 : Blo 846354 1911437 := bbase (se 3 (by rfl) ⟨358394, by rfl⟩ : syracuseStep 1911437 = 716789) (by norm_num)
theorem B1911509 : Blo 846354 1911509 := bbase (se 7 (by rfl) ⟨22400, by rfl⟩ : syracuseStep 1911509 = 44801) (by norm_num)
theorem B1911581 : Blo 846354 1911581 := bbase (se 3 (by rfl) ⟨358421, by rfl⟩ : syracuseStep 1911581 = 716843) (by norm_num)
theorem B3058469 : Blo 846354 3058469 := bbase (se 4 (by rfl) ⟨286731, by rfl⟩ : syracuseStep 3058469 = 573463) (by norm_num)
theorem B1911653 : Blo 846354 1911653 := bbase (se 4 (by rfl) ⟨179217, by rfl⟩ : syracuseStep 1911653 = 358435) (by norm_num)
theorem B1813357 : Blo 846354 1813357 := bbase (se 3 (by rfl) ⟨340004, by rfl⟩ : syracuseStep 1813357 = 680009) (by norm_num)
theorem B1911725 : Blo 846354 1911725 := bbase (se 3 (by rfl) ⟨358448, by rfl⟩ : syracuseStep 1911725 = 716897) (by norm_num)
theorem B2862053 : Blo 846354 2862053 := bbase (se 4 (by rfl) ⟨268317, by rfl⟩ : syracuseStep 2862053 = 536635) (by norm_num)
theorem B1911797 : Blo 846354 1911797 := bbase (se 5 (by rfl) ⟨89615, by rfl⟩ : syracuseStep 1911797 = 179231) (by norm_num)
theorem B2173981 : Blo 846354 2173981 := bbase (se 3 (by rfl) ⟨407621, by rfl⟩ : syracuseStep 2173981 = 815243) (by norm_num)
theorem B1911869 : Blo 846354 1911869 := bbase (se 3 (by rfl) ⟨358475, by rfl⟩ : syracuseStep 1911869 = 716951) (by norm_num)
theorem B1911941 : Blo 846354 1911941 := bbase (se 4 (by rfl) ⟨179244, by rfl⟩ : syracuseStep 1911941 = 358489) (by norm_num)
theorem B1912013 : Blo 846354 1912013 := bbase (se 3 (by rfl) ⟨358502, by rfl⟩ : syracuseStep 1912013 = 717005) (by norm_num)
theorem B3222773 : Blo 846354 3222773 := bbase (se 5 (by rfl) ⟨151067, by rfl⟩ : syracuseStep 3222773 = 302135) (by norm_num)
theorem B1912085 : Blo 846354 1912085 := bbase (se 6 (by rfl) ⟨44814, by rfl⟩ : syracuseStep 1912085 = 89629) (by norm_num)
theorem B1289525 : Blo 846354 1289525 := bbase (se 5 (by rfl) ⟨60446, by rfl⟩ : syracuseStep 1289525 = 120893) (by norm_num)
theorem B1912157 : Blo 846354 1912157 := bbase (se 3 (by rfl) ⟨358529, by rfl⟩ : syracuseStep 1912157 = 717059) (by norm_num)
theorem B2862485 : Blo 846354 2862485 := bbase (se 6 (by rfl) ⟨67089, by rfl⟩ : syracuseStep 2862485 = 134179) (by norm_num)
theorem B1912229 : Blo 846354 1912229 := bbase (se 4 (by rfl) ⟨179271, by rfl⟩ : syracuseStep 1912229 = 358543) (by norm_num)
theorem B1224157 : Blo 846354 1224157 := bbase (se 3 (by rfl) ⟨229529, by rfl⟩ : syracuseStep 1224157 = 459059) (by norm_num)
theorem B1912301 : Blo 846354 1912301 := bbase (se 3 (by rfl) ⟨358556, by rfl⟩ : syracuseStep 1912301 = 717113) (by norm_num)
theorem B3223061 : Blo 846354 3223061 := bbase (se 6 (by rfl) ⟨75540, by rfl⟩ : syracuseStep 3223061 = 151081) (by norm_num)
theorem B1912373 : Blo 846354 1912373 := bbase (se 5 (by rfl) ⟨89642, by rfl⟩ : syracuseStep 1912373 = 179285) (by norm_num)
theorem B4304501 : Blo 846354 4304501 := bbase (se 5 (by rfl) ⟨201773, by rfl⟩ : syracuseStep 4304501 = 403547) (by norm_num)
theorem B1912445 : Blo 846354 1912445 := bbase (se 3 (by rfl) ⟨358583, by rfl⟩ : syracuseStep 1912445 = 717167) (by norm_num)
theorem B1912517 : Blo 846354 1912517 := bbase (se 4 (by rfl) ⟨179298, by rfl⟩ : syracuseStep 1912517 = 358597) (by norm_num)
theorem B10333909 : Blo 846354 10333909 := bbase (se 7 (by rfl) ⟨121100, by rfl⟩ : syracuseStep 10333909 = 242201) (by norm_num)
theorem B1912589 : Blo 846354 1912589 := bbase (se 3 (by rfl) ⟨358610, by rfl⟩ : syracuseStep 1912589 = 717221) (by norm_num)
theorem B2862917 : Blo 846354 2862917 := bbase (se 4 (by rfl) ⟨268398, by rfl⟩ : syracuseStep 2862917 = 536797) (by norm_num)
theorem B1912661 : Blo 846354 1912661 := bbase (se 9 (by rfl) ⟨5603, by rfl⟩ : syracuseStep 1912661 = 11207) (by norm_num)
theorem B1290133 : Blo 846354 1290133 := bbase (se 6 (by rfl) ⟨30237, by rfl⟩ : syracuseStep 1290133 = 60475) (by norm_num)
theorem B1912733 : Blo 846354 1912733 := bbase (se 3 (by rfl) ⟨358637, by rfl⟩ : syracuseStep 1912733 = 717275) (by norm_num)
theorem B1224661 : Blo 846354 1224661 := bbase (se 7 (by rfl) ⟨14351, by rfl⟩ : syracuseStep 1224661 = 28703) (by norm_num)
theorem B1912805 : Blo 846354 1912805 := bbase (se 4 (by rfl) ⟨179325, by rfl⟩ : syracuseStep 1912805 = 358651) (by norm_num)
theorem B1912877 : Blo 846354 1912877 := bbase (se 3 (by rfl) ⟨358664, by rfl⟩ : syracuseStep 1912877 = 717329) (by norm_num)
theorem B1912949 : Blo 846354 1912949 := bbase (se 5 (by rfl) ⟨89669, by rfl⟩ : syracuseStep 1912949 = 179339) (by norm_num)
theorem B2142389 : Blo 846354 2142389 := bbase (se 5 (by rfl) ⟨100424, by rfl⟩ : syracuseStep 2142389 = 200849) (by norm_num)
theorem B1913021 : Blo 846354 1913021 := bbase (se 3 (by rfl) ⟨358691, by rfl⟩ : syracuseStep 1913021 = 717383) (by norm_num)
theorem B2863349 : Blo 846354 2863349 := bbase (se 5 (by rfl) ⟨134219, by rfl⟩ : syracuseStep 2863349 = 268439) (by norm_num)
theorem B1913093 : Blo 846354 1913093 := bbase (se 4 (by rfl) ⟨179352, by rfl⟩ : syracuseStep 1913093 = 358705) (by norm_num)
theorem B1454357 : Blo 846354 1454357 := bbase (se 6 (by rfl) ⟨34086, by rfl⟩ : syracuseStep 1454357 = 68173) (by norm_num)
theorem B6435125 : Blo 846354 6435125 := bbase (se 5 (by rfl) ⟨301646, by rfl⟩ : syracuseStep 6435125 = 603293) (by norm_num)
theorem B1814861 : Blo 846354 1814861 := bbase (se 3 (by rfl) ⟨340286, by rfl⟩ : syracuseStep 1814861 = 680573) (by norm_num)
theorem B1913165 : Blo 846354 1913165 := bbase (se 3 (by rfl) ⟨358718, by rfl⟩ : syracuseStep 1913165 = 717437) (by norm_num)
theorem B1913237 : Blo 846354 1913237 := bbase (se 6 (by rfl) ⟨44841, by rfl⟩ : syracuseStep 1913237 = 89683) (by norm_num)
theorem B1815005 : Blo 846354 1815005 := bbase (se 3 (by rfl) ⟨340313, by rfl⟩ : syracuseStep 1815005 = 680627) (by norm_num)
theorem B2142733 : Blo 846354 2142733 := bbase (se 3 (by rfl) ⟨401762, by rfl⟩ : syracuseStep 2142733 = 803525) (by norm_num)
theorem B2142845 : Blo 846354 2142845 := bbase (se 3 (by rfl) ⟨401783, by rfl⟩ : syracuseStep 2142845 = 803567) (by norm_num)
theorem B2863781 : Blo 846354 2863781 := bbase (se 4 (by rfl) ⟨268479, by rfl⟩ : syracuseStep 2863781 = 536959) (by norm_num)
theorem B3224245 : Blo 846354 3224245 := bbase (se 5 (by rfl) ⟨151136, by rfl⟩ : syracuseStep 3224245 = 302273) (by norm_num)
theorem B2143037 : Blo 846354 2143037 := bbase (se 3 (by rfl) ⟨401819, by rfl⟩ : syracuseStep 2143037 = 803639) (by norm_num)
theorem B1815365 : Blo 846354 1815365 := bbase (se 4 (by rfl) ⟨170190, by rfl⟩ : syracuseStep 1815365 = 340381) (by norm_num)
theorem B3060661 : Blo 846354 3060661 := bbase (se 5 (by rfl) ⟨143468, by rfl⟩ : syracuseStep 3060661 = 286937) (by norm_num)
theorem B3224549 : Blo 846354 3224549 := bbase (se 4 (by rfl) ⟨302301, by rfl⟩ : syracuseStep 3224549 = 604603) (by norm_num)
theorem B1356821 : Blo 846354 1356821 := bbase (se 6 (by rfl) ⟨31800, by rfl⟩ : syracuseStep 1356821 = 63601) (by norm_num)
theorem B2864213 : Blo 846354 2864213 := bbase (se 8 (by rfl) ⟨16782, by rfl⟩ : syracuseStep 2864213 = 33565) (by norm_num)
theorem B2143381 : Blo 846354 2143381 := bbase (se 6 (by rfl) ⟨50235, by rfl⟩ : syracuseStep 2143381 = 100471) (by norm_num)
theorem B1717453 : Blo 846354 1717453 := bbase (se 3 (by rfl) ⟨322022, by rfl⟩ : syracuseStep 1717453 = 644045) (by norm_num)
theorem B1357013 : Blo 846354 1357013 := bbase (se 7 (by rfl) ⟨15902, by rfl⟩ : syracuseStep 1357013 = 31805) (by norm_num)
theorem B2143493 : Blo 846354 2143493 := bbase (se 4 (by rfl) ⟨200952, by rfl⟩ : syracuseStep 2143493 = 401905) (by norm_num)
theorem B2143685 : Blo 846354 2143685 := bbase (se 4 (by rfl) ⟨200970, by rfl⟩ : syracuseStep 2143685 = 401941) (by norm_num)
theorem B2864645 : Blo 846354 2864645 := bbase (se 4 (by rfl) ⟨268560, by rfl⟩ : syracuseStep 2864645 = 537121) (by norm_num)
theorem B5879317 : Blo 846354 5879317 := bbase (se 6 (by rfl) ⟨137796, by rfl⟩ : syracuseStep 5879317 = 275593) (by norm_num)
theorem B2144029 : Blo 846354 2144029 := bbase (se 3 (by rfl) ⟨402005, by rfl⟩ : syracuseStep 2144029 = 804011) (by norm_num)
theorem B3094325 : Blo 846354 3094325 := bbase (se 5 (by rfl) ⟨145046, by rfl⟩ : syracuseStep 3094325 = 290093) (by norm_num)
theorem B2144141 : Blo 846354 2144141 := bbase (se 3 (by rfl) ⟨402026, by rfl⟩ : syracuseStep 2144141 = 804053) (by norm_num)
theorem B2865077 : Blo 846354 2865077 := bbase (se 5 (by rfl) ⟨134300, by rfl⟩ : syracuseStep 2865077 = 268601) (by norm_num)
theorem B2144333 : Blo 846354 2144333 := bbase (se 3 (by rfl) ⟨402062, by rfl⟩ : syracuseStep 2144333 = 804125) (by norm_num)
theorem B2865509 : Blo 846354 2865509 := bbase (se 4 (by rfl) ⟨268641, by rfl⟩ : syracuseStep 2865509 = 537283) (by norm_num)
theorem B1227125 : Blo 846354 1227125 := bbase (se 5 (by rfl) ⟨57521, by rfl⟩ : syracuseStep 1227125 = 115043) (by norm_num)
theorem B2144677 : Blo 846354 2144677 := bbase (se 4 (by rfl) ⟨201063, by rfl⟩ : syracuseStep 2144677 = 402127) (by norm_num)
theorem B2144789 : Blo 846354 2144789 := bbase (se 6 (by rfl) ⟨50268, by rfl⟩ : syracuseStep 2144789 = 100537) (by norm_num)
theorem B3619349 : Blo 846354 3619349 := bbase (se 6 (by rfl) ⟨84828, by rfl⟩ : syracuseStep 3619349 = 169657) (by norm_num)
theorem B1358461 : Blo 846354 1358461 := bbase (se 3 (by rfl) ⟨254711, by rfl⟩ : syracuseStep 1358461 = 509423) (by norm_num)
theorem B2144981 : Blo 846354 2144981 := bbase (se 7 (by rfl) ⟨25136, by rfl⟩ : syracuseStep 2144981 = 50273) (by norm_num)
theorem B2865941 : Blo 846354 2865941 := bbase (se 6 (by rfl) ⟨67170, by rfl⟩ : syracuseStep 2865941 = 134341) (by norm_num)
theorem B4078421 : Blo 846354 4078421 := bbase (se 9 (by rfl) ⟨11948, by rfl⟩ : syracuseStep 4078421 = 23897) (by norm_num)
theorem B2178085 : Blo 846354 2178085 := bbase (se 4 (by rfl) ⟨204195, by rfl⟩ : syracuseStep 2178085 = 408391) (by norm_num)
theorem B3226661 : Blo 846354 3226661 := bbase (se 4 (by rfl) ⟨302499, by rfl⟩ : syracuseStep 3226661 = 604999) (by norm_num)
theorem B2145325 : Blo 846354 2145325 := bbase (se 3 (by rfl) ⟨402248, by rfl⟩ : syracuseStep 2145325 = 804497) (by norm_num)
theorem B4832405 : Blo 846354 4832405 := bbase (se 6 (by rfl) ⟨113259, by rfl⟩ : syracuseStep 4832405 = 226519) (by norm_num)
theorem B16333973 : Blo 846354 16333973 := bbase (se 6 (by rfl) ⟨382827, by rfl⟩ : syracuseStep 16333973 = 765655) (by norm_num)
theorem B2145437 : Blo 846354 2145437 := bbase (se 3 (by rfl) ⟨402269, by rfl⟩ : syracuseStep 2145437 = 804539) (by norm_num)
theorem B2866373 : Blo 846354 2866373 := bbase (se 4 (by rfl) ⟨268722, by rfl⟩ : syracuseStep 2866373 = 537445) (by norm_num)
theorem B3226949 : Blo 846354 3226949 := bbase (se 4 (by rfl) ⟨302526, by rfl⟩ : syracuseStep 3226949 = 605053) (by norm_num)
theorem B2145629 : Blo 846354 2145629 := bbase (se 3 (by rfl) ⟨402305, by rfl⟩ : syracuseStep 2145629 = 804611) (by norm_num)
theorem B3096181 : Blo 846354 3096181 := bbase (se 5 (by rfl) ⟨145133, by rfl⟩ : syracuseStep 3096181 = 290267) (by norm_num)
theorem B2866805 : Blo 846354 2866805 := bbase (se 5 (by rfl) ⟨134381, by rfl⟩ : syracuseStep 2866805 = 268763) (by norm_num)
theorem B2178701 : Blo 846354 2178701 := bbase (se 3 (by rfl) ⟨408506, by rfl⟩ : syracuseStep 2178701 = 817013) (by norm_num)
theorem B2145973 : Blo 846354 2145973 := bbase (se 5 (by rfl) ⟨100592, by rfl⟩ : syracuseStep 2145973 = 201185) (by norm_num)
theorem B2146085 : Blo 846354 2146085 := bbase (se 4 (by rfl) ⟨201195, by rfl⟩ : syracuseStep 2146085 = 402391) (by norm_num)
theorem B3260341 : Blo 846354 3260341 := bbase (se 5 (by rfl) ⟨152828, by rfl⟩ : syracuseStep 3260341 = 305657) (by norm_num)
theorem B2146277 : Blo 846354 2146277 := bbase (se 4 (by rfl) ⟨201213, by rfl⟩ : syracuseStep 2146277 = 402427) (by norm_num)
theorem B1359845 : Blo 846354 1359845 := bbase (se 4 (by rfl) ⟨127485, by rfl⟩ : syracuseStep 1359845 = 254971) (by norm_num)
theorem B2867237 : Blo 846354 2867237 := bbase (se 4 (by rfl) ⟨268803, by rfl⟩ : syracuseStep 2867237 = 537607) (by norm_num)
theorem B2900053 : Blo 846354 2900053 := bbase (se 8 (by rfl) ⟨16992, by rfl⟩ : syracuseStep 2900053 = 33985) (by norm_num)
theorem B1360037 : Blo 846354 1360037 := bbase (se 4 (by rfl) ⟨127503, by rfl⟩ : syracuseStep 1360037 = 255007) (by norm_num)
theorem B3621125 : Blo 846354 3621125 := bbase (se 4 (by rfl) ⟨339480, by rfl⟩ : syracuseStep 3621125 = 678961) (by norm_num)
theorem B2146621 : Blo 846354 2146621 := bbase (se 3 (by rfl) ⟨402491, by rfl⟩ : syracuseStep 2146621 = 804983) (by norm_num)
theorem B7258517 : Blo 846354 7258517 := bbase (se 6 (by rfl) ⟨170121, by rfl⟩ : syracuseStep 7258517 = 340243) (by norm_num)
theorem B2146733 : Blo 846354 2146733 := bbase (se 3 (by rfl) ⟨402512, by rfl⟩ : syracuseStep 2146733 = 805025) (by norm_num)
theorem B2867669 : Blo 846354 2867669 := bbase (se 7 (by rfl) ⟨33605, by rfl⟩ : syracuseStep 2867669 = 67211) (by norm_num)
theorem B3228133 : Blo 846354 3228133 := bbase (se 4 (by rfl) ⟨302637, by rfl⟩ : syracuseStep 3228133 = 605275) (by norm_num)
theorem B5423669 : Blo 846354 5423669 := bbase (se 5 (by rfl) ⟨254234, by rfl⟩ : syracuseStep 5423669 = 508469) (by norm_num)
theorem B2146925 : Blo 846354 2146925 := bbase (se 3 (by rfl) ⟨402548, by rfl⟩ : syracuseStep 2146925 = 805097) (by norm_num)
theorem B1721021 : Blo 846354 1721021 := bbase (se 3 (by rfl) ⟨322691, by rfl⟩ : syracuseStep 1721021 = 645383) (by norm_num)
theorem B3228437 : Blo 846354 3228437 := bbase (se 6 (by rfl) ⟨75666, by rfl⟩ : syracuseStep 3228437 = 151333) (by norm_num)
theorem B2868101 : Blo 846354 2868101 := bbase (se 4 (by rfl) ⟨268884, by rfl⟩ : syracuseStep 2868101 = 537769) (by norm_num)
theorem B1033097 : Blo 846354 1033097 := bbase (se 2 (by rfl) ⟨387411, by rfl⟩ : syracuseStep 1033097 = 774823) (by norm_num)
theorem B2147269 : Blo 846354 2147269 := bbase (se 4 (by rfl) ⟨201306, by rfl⟩ : syracuseStep 2147269 = 402613) (by norm_num)
theorem B1033177 : Blo 846354 1033177 := bbase (se 2 (by rfl) ⟨387441, by rfl⟩ : syracuseStep 1033177 = 774883) (by norm_num)
theorem B2147381 : Blo 846354 2147381 := bbase (se 5 (by rfl) ⟨100658, by rfl⟩ : syracuseStep 2147381 = 201317) (by norm_num)
theorem B3261653 : Blo 846354 3261653 := bbase (se 7 (by rfl) ⟨38222, by rfl⟩ : syracuseStep 3261653 = 76445) (by norm_num)
theorem B3622117 : Blo 846354 3622117 := bbase (se 4 (by rfl) ⟨339573, by rfl⟩ : syracuseStep 3622117 = 679147) (by norm_num)
theorem B2147573 : Blo 846354 2147573 := bbase (se 5 (by rfl) ⟨100667, by rfl⟩ : syracuseStep 2147573 = 201335) (by norm_num)
theorem B2868533 : Blo 846354 2868533 := bbase (se 5 (by rfl) ⟨134462, by rfl⟩ : syracuseStep 2868533 = 268925) (by norm_num)
theorem B1361357 : Blo 846354 1361357 := bbase (se 3 (by rfl) ⟨255254, by rfl⟩ : syracuseStep 1361357 = 510509) (by norm_num)
theorem B1361453 : Blo 846354 1361453 := bbase (se 3 (by rfl) ⟨255272, by rfl⟩ : syracuseStep 1361453 = 510545) (by norm_num)
theorem B2147917 : Blo 846354 2147917 := bbase (se 3 (by rfl) ⟨402734, by rfl⟩ : syracuseStep 2147917 = 805469) (by norm_num)
theorem B1361485 : Blo 846354 1361485 := bbase (se 3 (by rfl) ⟨255278, by rfl⟩ : syracuseStep 1361485 = 510557) (by norm_num)
theorem B2410165 : Blo 846354 2410165 := bbase (se 5 (by rfl) ⟨112976, by rfl⟩ : syracuseStep 2410165 = 225953) (by norm_num)
theorem B1525429 : Blo 846354 1525429 := bbase (se 5 (by rfl) ⟨71504, by rfl⟩ : syracuseStep 1525429 = 143009) (by norm_num)
theorem B2148029 : Blo 846354 2148029 := bbase (se 3 (by rfl) ⟨402755, by rfl⟩ : syracuseStep 2148029 = 805511) (by norm_num)
theorem B1722053 : Blo 846354 1722053 := bbase (se 4 (by rfl) ⟨161442, by rfl⟩ : syracuseStep 1722053 = 322885) (by norm_num)
theorem B2868965 : Blo 846354 2868965 := bbase (se 4 (by rfl) ⟨268965, by rfl⟩ : syracuseStep 2868965 = 537931) (by norm_num)
theorem B1525501 : Blo 846354 1525501 := bbase (se 3 (by rfl) ⟨286031, by rfl⟩ : syracuseStep 1525501 = 572063) (by norm_num)
theorem B2148221 : Blo 846354 2148221 := bbase (se 3 (by rfl) ⟨402791, by rfl⟩ : syracuseStep 2148221 = 805583) (by norm_num)
theorem B1525645 : Blo 846354 1525645 := bbase (se 3 (by rfl) ⟨286058, by rfl⟩ : syracuseStep 1525645 = 572117) (by norm_num)
theorem B1034285 : Blo 846354 1034285 := bbase (se 3 (by rfl) ⟨193928, by rfl⟩ : syracuseStep 1034285 = 387857) (by norm_num)
theorem B2869397 : Blo 846354 2869397 := bbase (se 6 (by rfl) ⟨67251, by rfl⟩ : syracuseStep 2869397 = 134503) (by norm_num)
theorem B2148565 : Blo 846354 2148565 := bbase (se 7 (by rfl) ⟨25178, by rfl⟩ : syracuseStep 2148565 = 50357) (by norm_num)
theorem B2148677 : Blo 846354 2148677 := bbase (se 4 (by rfl) ⟨201438, by rfl⟩ : syracuseStep 2148677 = 402877) (by norm_num)
theorem B2148869 : Blo 846354 2148869 := bbase (se 4 (by rfl) ⟨201456, by rfl⟩ : syracuseStep 2148869 = 402913) (by norm_num)
theorem B2869829 : Blo 846354 2869829 := bbase (se 4 (by rfl) ⟨269046, by rfl⟩ : syracuseStep 2869829 = 538093) (by norm_num)
theorem B903889 : Blo 846354 903889 := bbase (se 2 (by rfl) ⟨338958, by rfl⟩ : syracuseStep 903889 = 677917) (by norm_num)
theorem B1526509 : Blo 846354 1526509 := bbase (se 3 (by rfl) ⟨286220, by rfl⟩ : syracuseStep 1526509 = 572441) (by norm_num)
theorem B1428293 : Blo 846354 1428293 := bbase (se 4 (by rfl) ⟨133902, by rfl⟩ : syracuseStep 1428293 = 267805) (by norm_num)
theorem B1526597 : Blo 846354 1526597 := bbase (se 4 (by rfl) ⟨143118, by rfl⟩ : syracuseStep 1526597 = 286237) (by norm_num)
theorem B871241 : Blo 846354 871241 := bbase (se 2 (by rfl) ⟨326715, by rfl⟩ : syracuseStep 871241 = 653431) (by norm_num)
theorem B2149213 : Blo 846354 2149213 := bbase (se 3 (by rfl) ⟨402977, by rfl⟩ : syracuseStep 2149213 = 805955) (by norm_num)
theorem B969617 : Blo 846354 969617 := bbase (se 2 (by rfl) ⟨363606, by rfl⟩ : syracuseStep 969617 = 727213) (by norm_num)
theorem B8145845 : Blo 846354 8145845 := bbase (se 5 (by rfl) ⟨381836, by rfl⟩ : syracuseStep 8145845 = 763673) (by norm_num)
theorem B1428421 : Blo 846354 1428421 := bbase (se 4 (by rfl) ⟨133914, by rfl⟩ : syracuseStep 1428421 = 267829) (by norm_num)
theorem B2149325 : Blo 846354 2149325 := bbase (se 3 (by rfl) ⟨402998, by rfl⟩ : syracuseStep 2149325 = 805997) (by norm_num)
theorem B1428509 : Blo 846354 1428509 := bbase (se 3 (by rfl) ⟨267845, by rfl⟩ : syracuseStep 1428509 = 535691) (by norm_num)
theorem B904321 : Blo 846354 904321 := bbase (se 2 (by rfl) ⟨339120, by rfl⟩ : syracuseStep 904321 = 678241) (by norm_num)
theorem B2149517 : Blo 846354 2149517 := bbase (se 3 (by rfl) ⟨403034, by rfl⟩ : syracuseStep 2149517 = 806069) (by norm_num)
theorem B2411669 : Blo 846354 2411669 := bbase (se 6 (by rfl) ⟨56523, by rfl⟩ : syracuseStep 2411669 = 113047) (by norm_num)
theorem B1428637 : Blo 846354 1428637 := bbase (se 3 (by rfl) ⟨267869, by rfl⟩ : syracuseStep 1428637 = 535739) (by norm_num)
theorem B904393 : Blo 846354 904393 := bbase (se 2 (by rfl) ⟨339147, by rfl⟩ : syracuseStep 904393 = 678295) (by norm_num)
theorem B28331221 : Blo 846354 28331221 := bbase (se 7 (by rfl) ⟨332006, by rfl⟩ : syracuseStep 28331221 = 664013) (by norm_num)
theorem B1428725 : Blo 846354 1428725 := bbase (se 5 (by rfl) ⟨66971, by rfl⟩ : syracuseStep 1428725 = 133943) (by norm_num)
theorem B1527029 : Blo 846354 1527029 := bbase (se 5 (by rfl) ⟨71579, by rfl⟩ : syracuseStep 1527029 = 143159) (by norm_num)
theorem B1428853 : Blo 846354 1428853 := bbase (se 5 (by rfl) ⟨66977, by rfl⟩ : syracuseStep 1428853 = 133955) (by norm_num)
theorem B1428941 : Blo 846354 1428941 := bbase (se 3 (by rfl) ⟨267926, by rfl⟩ : syracuseStep 1428941 = 535853) (by norm_num)
theorem B2149861 : Blo 846354 2149861 := bbase (se 4 (by rfl) ⟨201549, by rfl⟩ : syracuseStep 2149861 = 403099) (by norm_num)
theorem B1527317 : Blo 846354 1527317 := bbase (se 6 (by rfl) ⟨35796, by rfl⟩ : syracuseStep 1527317 = 71593) (by norm_num)
theorem B5164597 : Blo 846354 5164597 := bbase (se 5 (by rfl) ⟨242090, by rfl⟩ : syracuseStep 5164597 = 484181) (by norm_num)
theorem B904765 : Blo 846354 904765 := bbase (se 3 (by rfl) ⟨169643, by rfl⟩ : syracuseStep 904765 = 339287) (by norm_num)
theorem B1429069 : Blo 846354 1429069 := bbase (se 3 (by rfl) ⟨267950, by rfl⟩ : syracuseStep 1429069 = 535901) (by norm_num)
theorem B2149973 : Blo 846354 2149973 := bbase (se 8 (by rfl) ⟨12597, by rfl⟩ : syracuseStep 2149973 = 25195) (by norm_num)
theorem B1429157 : Blo 846354 1429157 := bbase (se 4 (by rfl) ⟨133983, by rfl⟩ : syracuseStep 1429157 = 267967) (by norm_num)
theorem B2150165 : Blo 846354 2150165 := bbase (se 6 (by rfl) ⟨50394, by rfl⟩ : syracuseStep 2150165 = 100789) (by norm_num)
theorem B1429285 : Blo 846354 1429285 := bbase (se 4 (by rfl) ⟨133995, by rfl⟩ : syracuseStep 1429285 = 267991) (by norm_num)
theorem B1429373 : Blo 846354 1429373 := bbase (se 3 (by rfl) ⟨268007, by rfl⟩ : syracuseStep 1429373 = 536015) (by norm_num)
theorem B6442901 : Blo 846354 6442901 := bbase (se 6 (by rfl) ⟨151005, by rfl⟩ : syracuseStep 6442901 = 302011) (by norm_num)
theorem B905141 : Blo 846354 905141 := bbase (se 5 (by rfl) ⟨42428, by rfl⟩ : syracuseStep 905141 = 84857) (by norm_num)
theorem B1429501 : Blo 846354 1429501 := bbase (se 3 (by rfl) ⟨268031, by rfl⟩ : syracuseStep 1429501 = 536063) (by norm_num)
theorem B905213 : Blo 846354 905213 := bbase (se 3 (by rfl) ⟨169727, by rfl⟩ : syracuseStep 905213 = 339455) (by norm_num)
theorem B1429589 : Blo 846354 1429589 := bbase (se 8 (by rfl) ⟨8376, by rfl⟩ : syracuseStep 1429589 = 16753) (by norm_num)
theorem B2150509 : Blo 846354 2150509 := bbase (se 3 (by rfl) ⟨403220, by rfl⟩ : syracuseStep 2150509 = 806441) (by norm_num)
theorem B905401 : Blo 846354 905401 := bbase (se 2 (by rfl) ⟨339525, by rfl⟩ : syracuseStep 905401 = 679051) (by norm_num)
theorem B1429717 : Blo 846354 1429717 := bbase (se 7 (by rfl) ⟨16754, by rfl⟩ : syracuseStep 1429717 = 33509) (by norm_num)
theorem B2150621 : Blo 846354 2150621 := bbase (se 3 (by rfl) ⟨403241, by rfl⟩ : syracuseStep 2150621 = 806483) (by norm_num)
theorem B1429805 : Blo 846354 1429805 := bbase (se 3 (by rfl) ⟨268088, by rfl⟩ : syracuseStep 1429805 = 536177) (by norm_num)
theorem B905585 : Blo 846354 905585 := bbase (se 2 (by rfl) ⟨339594, by rfl⟩ : syracuseStep 905585 = 679189) (by norm_num)
theorem B2150813 : Blo 846354 2150813 := bbase (se 3 (by rfl) ⟨403277, by rfl⟩ : syracuseStep 2150813 = 806555) (by norm_num)
theorem B1429933 : Blo 846354 1429933 := bbase (se 3 (by rfl) ⟨268112, by rfl⟩ : syracuseStep 1429933 = 536225) (by norm_num)
theorem B1430021 : Blo 846354 1430021 := bbase (se 4 (by rfl) ⟨134064, by rfl⟩ : syracuseStep 1430021 = 268129) (by norm_num)
theorem B2904661 : Blo 846354 2904661 := bbase (se 8 (by rfl) ⟨17019, by rfl⟩ : syracuseStep 2904661 = 34039) (by norm_num)
theorem B24498773 : Blo 846354 24498773 := bbase (se 8 (by rfl) ⟨143547, by rfl⟩ : syracuseStep 24498773 = 287095) (by norm_num)
theorem B1430149 : Blo 846354 1430149 := bbase (se 4 (by rfl) ⟨134076, by rfl⟩ : syracuseStep 1430149 = 268153) (by norm_num)
theorem B3265157 : Blo 846354 3265157 := bbase (se 4 (by rfl) ⟨306108, by rfl⟩ : syracuseStep 3265157 = 612217) (by norm_num)
theorem B2413253 : Blo 846354 2413253 := bbase (se 4 (by rfl) ⟨226242, by rfl⟩ : syracuseStep 2413253 = 452485) (by norm_num)
theorem B1430237 : Blo 846354 1430237 := bbase (se 3 (by rfl) ⟨268169, by rfl⟩ : syracuseStep 1430237 = 536339) (by norm_num)
theorem B873181 : Blo 846354 873181 := bbase (se 3 (by rfl) ⟨163721, by rfl⟩ : syracuseStep 873181 = 327443) (by norm_num)
theorem B2151157 : Blo 846354 2151157 := bbase (se 5 (by rfl) ⟨100835, by rfl⟩ : syracuseStep 2151157 = 201671) (by norm_num)
theorem B1430365 : Blo 846354 1430365 := bbase (se 3 (by rfl) ⟨268193, by rfl⟩ : syracuseStep 1430365 = 536387) (by norm_num)
theorem B2151269 : Blo 846354 2151269 := bbase (se 4 (by rfl) ⟨201681, by rfl⟩ : syracuseStep 2151269 = 403363) (by norm_num)
theorem B1430453 : Blo 846354 1430453 := bbase (se 5 (by rfl) ⟨67052, by rfl⟩ : syracuseStep 1430453 = 134105) (by norm_num)
theorem B2151461 : Blo 846354 2151461 := bbase (se 4 (by rfl) ⟨201699, by rfl⟩ : syracuseStep 2151461 = 403399) (by norm_num)
theorem B1430581 : Blo 846354 1430581 := bbase (se 5 (by rfl) ⟨67058, by rfl⟩ : syracuseStep 1430581 = 134117) (by norm_num)
theorem B906337 : Blo 846354 906337 := bbase (se 2 (by rfl) ⟨339876, by rfl⟩ : syracuseStep 906337 = 679753) (by norm_num)
theorem B1430669 : Blo 846354 1430669 := bbase (se 3 (by rfl) ⟨268250, by rfl⟩ : syracuseStep 1430669 = 536501) (by norm_num)
theorem B906409 : Blo 846354 906409 := bbase (se 2 (by rfl) ⟨339903, by rfl⟩ : syracuseStep 906409 = 679807) (by norm_num)
theorem B1430797 : Blo 846354 1430797 := bbase (se 3 (by rfl) ⟨268274, by rfl⟩ : syracuseStep 1430797 = 536549) (by norm_num)
theorem B11621717 : Blo 846354 11621717 := bbase (se 18 (by rfl) ⟨66, by rfl⟩ : syracuseStep 11621717 = 133) (by norm_num)
theorem B906589 : Blo 846354 906589 := bbase (se 3 (by rfl) ⟨169985, by rfl⟩ : syracuseStep 906589 = 339971) (by norm_num)
theorem B2413925 : Blo 846354 2413925 := bbase (se 4 (by rfl) ⟨226305, by rfl⟩ : syracuseStep 2413925 = 452611) (by norm_num)
theorem B1430885 : Blo 846354 1430885 := bbase (se 4 (by rfl) ⟨134145, by rfl⟩ : syracuseStep 1430885 = 268291) (by norm_num)
theorem B2151805 : Blo 846354 2151805 := bbase (se 3 (by rfl) ⟨403463, by rfl⟩ : syracuseStep 2151805 = 806927) (by norm_num)
theorem B1431013 : Blo 846354 1431013 := bbase (se 4 (by rfl) ⟨134157, by rfl⟩ : syracuseStep 1431013 = 268315) (by norm_num)
theorem B2151917 : Blo 846354 2151917 := bbase (se 3 (by rfl) ⟨403484, by rfl⟩ : syracuseStep 2151917 = 806969) (by norm_num)
theorem B1431101 : Blo 846354 1431101 := bbase (se 3 (by rfl) ⟨268331, by rfl⟩ : syracuseStep 1431101 = 536663) (by norm_num)
theorem B2479781 : Blo 846354 2479781 := bbase (se 4 (by rfl) ⟨232479, by rfl⟩ : syracuseStep 2479781 = 464959) (by norm_num)
theorem B2152109 : Blo 846354 2152109 := bbase (se 3 (by rfl) ⟨403520, by rfl⟩ : syracuseStep 2152109 = 807041) (by norm_num)
theorem B1431229 : Blo 846354 1431229 := bbase (se 3 (by rfl) ⟨268355, by rfl⟩ : syracuseStep 1431229 = 536711) (by norm_num)
theorem B14669525 : Blo 846354 14669525 := bbase (se 7 (by rfl) ⟨171908, by rfl⟩ : syracuseStep 14669525 = 343817) (by norm_num)
theorem B2414357 : Blo 846354 2414357 := bbase (se 6 (by rfl) ⟨56586, by rfl⟩ : syracuseStep 2414357 = 113173) (by norm_num)
theorem B1431317 : Blo 846354 1431317 := bbase (se 6 (by rfl) ⟨33546, by rfl⟩ : syracuseStep 1431317 = 67093) (by norm_num)
theorem B907033 : Blo 846354 907033 := bbase (se 2 (by rfl) ⟨340137, by rfl⟩ : syracuseStep 907033 = 680275) (by norm_num)
theorem B1431445 : Blo 846354 1431445 := bbase (se 6 (by rfl) ⟨33549, by rfl⟩ : syracuseStep 1431445 = 67099) (by norm_num)
theorem B907157 : Blo 846354 907157 := bbase (se 6 (by rfl) ⟨21261, by rfl⟩ : syracuseStep 907157 = 42523) (by norm_num)
theorem B1431533 : Blo 846354 1431533 := bbase (se 3 (by rfl) ⟨268412, by rfl⟩ : syracuseStep 1431533 = 536825) (by norm_num)
theorem B2152453 : Blo 846354 2152453 := bbase (se 4 (by rfl) ⟨201792, by rfl⟩ : syracuseStep 2152453 = 403585) (by norm_num)
theorem B1529941 : Blo 846354 1529941 := bbase (se 8 (by rfl) ⟨8964, by rfl⟩ : syracuseStep 1529941 = 17929) (by norm_num)
theorem B1431661 : Blo 846354 1431661 := bbase (se 3 (by rfl) ⟨268436, by rfl⟩ : syracuseStep 1431661 = 536873) (by norm_num)
theorem B3627125 : Blo 846354 3627125 := bbase (se 5 (by rfl) ⟨170021, by rfl⟩ : syracuseStep 3627125 = 340043) (by norm_num)
theorem B1071245 : Blo 846354 1071245 := bbase (se 3 (by rfl) ⟨200858, by rfl⟩ : syracuseStep 1071245 = 401717) (by norm_num)
theorem B907409 : Blo 846354 907409 := bbase (se 2 (by rfl) ⟨340278, by rfl⟩ : syracuseStep 907409 = 680557) (by norm_num)
theorem B1857725 : Blo 846354 1857725 := bbase (se 3 (by rfl) ⟨348323, by rfl⟩ : syracuseStep 1857725 = 696647) (by norm_num)
theorem B1071301 : Blo 846354 1071301 := bbase (se 4 (by rfl) ⟨100434, by rfl⟩ : syracuseStep 1071301 = 200869) (by norm_num)
theorem B1431749 : Blo 846354 1431749 := bbase (se 4 (by rfl) ⟨134226, by rfl⟩ : syracuseStep 1431749 = 268453) (by norm_num)
theorem B1530085 : Blo 846354 1530085 := bbase (se 4 (by rfl) ⟨143445, by rfl⟩ : syracuseStep 1530085 = 286891) (by norm_num)
theorem B1071397 : Blo 846354 1071397 := bbase (se 4 (by rfl) ⟨100443, by rfl⟩ : syracuseStep 1071397 = 200887) (by norm_num)
theorem B1431877 : Blo 846354 1431877 := bbase (se 4 (by rfl) ⟨134238, by rfl⟩ : syracuseStep 1431877 = 268477) (by norm_num)
theorem B18340181 : Blo 846354 18340181 := bbase (se 10 (by rfl) ⟨26865, by rfl⟩ : syracuseStep 18340181 = 53731) (by norm_num)
theorem B3627413 : Blo 846354 3627413 := bbase (se 6 (by rfl) ⟨85017, by rfl⟩ : syracuseStep 3627413 = 170035) (by norm_num)
theorem B1431965 : Blo 846354 1431965 := bbase (se 3 (by rfl) ⟨268493, by rfl⟩ : syracuseStep 1431965 = 536987) (by norm_num)
theorem B1071569 : Blo 846354 1071569 := bbase (se 2 (by rfl) ⟨401838, by rfl⟩ : syracuseStep 1071569 = 803677) (by norm_num)
theorem B2415109 : Blo 846354 2415109 := bbase (se 4 (by rfl) ⟨226416, by rfl⟩ : syracuseStep 2415109 = 452833) (by norm_num)
theorem B1071625 : Blo 846354 1071625 := bbase (se 2 (by rfl) ⟨401859, by rfl⟩ : syracuseStep 1071625 = 803719) (by norm_num)
theorem B1432093 : Blo 846354 1432093 := bbase (se 3 (by rfl) ⟨268517, by rfl⟩ : syracuseStep 1432093 = 537035) (by norm_num)
theorem B907853 : Blo 846354 907853 := bbase (se 3 (by rfl) ⟨170222, by rfl⟩ : syracuseStep 907853 = 340445) (by norm_num)
theorem B1071721 : Blo 846354 1071721 := bbase (se 2 (by rfl) ⟨401895, by rfl⟩ : syracuseStep 1071721 = 803791) (by norm_num)
theorem B1432181 : Blo 846354 1432181 := bbase (se 5 (by rfl) ⟨67133, by rfl⟩ : syracuseStep 1432181 = 134267) (by norm_num)
theorem B2906741 : Blo 846354 2906741 := bbase (se 5 (by rfl) ⟨136253, by rfl⟩ : syracuseStep 2906741 = 272507) (by norm_num)
theorem B6543989 : Blo 846354 6543989 := bbase (se 5 (by rfl) ⟨306749, by rfl⟩ : syracuseStep 6543989 = 613499) (by norm_num)
theorem B1399445 : Blo 846354 1399445 := bbase (se 6 (by rfl) ⟨32799, by rfl⟩ : syracuseStep 1399445 = 65599) (by norm_num)
theorem B1432309 : Blo 846354 1432309 := bbase (se 5 (by rfl) ⟨67139, by rfl⟩ : syracuseStep 1432309 = 134279) (by norm_num)
theorem B1071893 : Blo 846354 1071893 := bbase (se 6 (by rfl) ⟨25122, by rfl⟩ : syracuseStep 1071893 = 50245) (by norm_num)
theorem B1530661 : Blo 846354 1530661 := bbase (se 4 (by rfl) ⟨143499, by rfl⟩ : syracuseStep 1530661 = 286999) (by norm_num)
theorem B1071949 : Blo 846354 1071949 := bbase (se 3 (by rfl) ⟨200990, by rfl⟩ : syracuseStep 1071949 = 401981) (by norm_num)
theorem B1432397 : Blo 846354 1432397 := bbase (se 3 (by rfl) ⟨268574, by rfl⟩ : syracuseStep 1432397 = 537149) (by norm_num)
theorem B1858405 : Blo 846354 1858405 := bbase (se 4 (by rfl) ⟨174225, by rfl⟩ : syracuseStep 1858405 = 348451) (by norm_num)
theorem B1072045 : Blo 846354 1072045 := bbase (se 3 (by rfl) ⟨201008, by rfl⟩ : syracuseStep 1072045 = 402017) (by norm_num)
theorem B1432525 : Blo 846354 1432525 := bbase (se 3 (by rfl) ⟨268598, by rfl⟩ : syracuseStep 1432525 = 537197) (by norm_num)
theorem B4840469 : Blo 846354 4840469 := bbase (se 6 (by rfl) ⟨113448, by rfl⟩ : syracuseStep 4840469 = 226897) (by norm_num)
theorem B1432613 : Blo 846354 1432613 := bbase (se 4 (by rfl) ⟨134307, by rfl⟩ : syracuseStep 1432613 = 268615) (by norm_num)
theorem B1072217 : Blo 846354 1072217 := bbase (se 2 (by rfl) ⟨402081, by rfl⟩ : syracuseStep 1072217 = 804163) (by norm_num)
theorem B3628165 : Blo 846354 3628165 := bbase (se 4 (by rfl) ⟨340140, by rfl⟩ : syracuseStep 3628165 = 680281) (by norm_num)
theorem B1072273 : Blo 846354 1072273 := bbase (se 2 (by rfl) ⟨402102, by rfl⟩ : syracuseStep 1072273 = 804205) (by norm_num)
theorem B1531037 : Blo 846354 1531037 := bbase (se 3 (by rfl) ⟨287069, by rfl⟩ : syracuseStep 1531037 = 574139) (by norm_num)
theorem B1432741 : Blo 846354 1432741 := bbase (se 4 (by rfl) ⟨134319, by rfl⟩ : syracuseStep 1432741 = 268639) (by norm_num)
theorem B1072369 : Blo 846354 1072369 := bbase (se 2 (by rfl) ⟨402138, by rfl⟩ : syracuseStep 1072369 = 804277) (by norm_num)
theorem B1432829 : Blo 846354 1432829 := bbase (se 3 (by rfl) ⟨268655, by rfl⟩ : syracuseStep 1432829 = 537311) (by norm_num)
theorem B1432957 : Blo 846354 1432957 := bbase (se 3 (by rfl) ⟨268679, by rfl⟩ : syracuseStep 1432957 = 537359) (by norm_num)
theorem B1072541 : Blo 846354 1072541 := bbase (se 3 (by rfl) ⟨201101, by rfl⟩ : syracuseStep 1072541 = 402203) (by norm_num)
theorem B1531325 : Blo 846354 1531325 := bbase (se 3 (by rfl) ⟨287123, by rfl⟩ : syracuseStep 1531325 = 574247) (by norm_num)
theorem B1072597 : Blo 846354 1072597 := bbase (se 7 (by rfl) ⟨12569, by rfl⟩ : syracuseStep 1072597 = 25139) (by norm_num)
theorem B1433045 : Blo 846354 1433045 := bbase (se 7 (by rfl) ⟨16793, by rfl⟩ : syracuseStep 1433045 = 33587) (by norm_num)
theorem B3431909 : Blo 846354 3431909 := bbase (se 4 (by rfl) ⟨321741, by rfl⟩ : syracuseStep 3431909 = 643483) (by norm_num)
theorem B1072693 : Blo 846354 1072693 := bbase (se 5 (by rfl) ⟨50282, by rfl⟩ : syracuseStep 1072693 = 100565) (by norm_num)
theorem B1531469 : Blo 846354 1531469 := bbase (se 3 (by rfl) ⟨287150, by rfl⟩ : syracuseStep 1531469 = 574301) (by norm_num)
theorem B1433173 : Blo 846354 1433173 := bbase (se 8 (by rfl) ⟨8397, by rfl⟩ : syracuseStep 1433173 = 16795) (by norm_num)
theorem B1433261 : Blo 846354 1433261 := bbase (se 3 (by rfl) ⟨268736, by rfl⟩ : syracuseStep 1433261 = 537473) (by norm_num)
theorem B1072865 : Blo 846354 1072865 := bbase (se 2 (by rfl) ⟨402324, by rfl⟩ : syracuseStep 1072865 = 804649) (by norm_num)
theorem B1072921 : Blo 846354 1072921 := bbase (se 2 (by rfl) ⟨402345, by rfl⟩ : syracuseStep 1072921 = 804691) (by norm_num)
theorem B1269533 : Blo 846354 1269533 := bbase (se 3 (by rfl) ⟨238037, by rfl⟩ : syracuseStep 1269533 = 476075) (by norm_num)
theorem B1433389 : Blo 846354 1433389 := bbase (se 3 (by rfl) ⟨268760, by rfl⟩ : syracuseStep 1433389 = 537521) (by norm_num)
theorem B1269557 : Blo 846354 1269557 := bbase (se 5 (by rfl) ⟨59510, by rfl⟩ : syracuseStep 1269557 = 119021) (by norm_num)
theorem B1269581 : Blo 846354 1269581 := bbase (se 3 (by rfl) ⟨238046, by rfl⟩ : syracuseStep 1269581 = 476093) (by norm_num)
theorem B3923797 : Blo 846354 3923797 := bbase (se 9 (by rfl) ⟨11495, by rfl⟩ : syracuseStep 3923797 = 22991) (by norm_num)
theorem B1269605 : Blo 846354 1269605 := bbase (se 4 (by rfl) ⟨119025, by rfl⟩ : syracuseStep 1269605 = 238051) (by norm_num)
theorem B3628901 : Blo 846354 3628901 := bbase (se 4 (by rfl) ⟨340209, by rfl⟩ : syracuseStep 3628901 = 680419) (by norm_num)
theorem B1073017 : Blo 846354 1073017 := bbase (se 2 (by rfl) ⟨402381, by rfl⟩ : syracuseStep 1073017 = 804763) (by norm_num)
theorem B1269629 : Blo 846354 1269629 := bbase (se 3 (by rfl) ⟨238055, by rfl⟩ : syracuseStep 1269629 = 476111) (by norm_num)
theorem B1433477 : Blo 846354 1433477 := bbase (se 4 (by rfl) ⟨134388, by rfl⟩ : syracuseStep 1433477 = 268777) (by norm_num)
theorem B1269653 : Blo 846354 1269653 := bbase (se 6 (by rfl) ⟨29757, by rfl⟩ : syracuseStep 1269653 = 59515) (by norm_num)
theorem B1269677 : Blo 846354 1269677 := bbase (se 3 (by rfl) ⟨238064, by rfl⟩ : syracuseStep 1269677 = 476129) (by norm_num)
theorem B1269701 : Blo 846354 1269701 := bbase (se 4 (by rfl) ⟨119034, by rfl⟩ : syracuseStep 1269701 = 238069) (by norm_num)
theorem B1269725 : Blo 846354 1269725 := bbase (se 3 (by rfl) ⟨238073, by rfl⟩ : syracuseStep 1269725 = 476147) (by norm_num)
theorem B1269749 : Blo 846354 1269749 := bbase (se 5 (by rfl) ⟨59519, by rfl⟩ : syracuseStep 1269749 = 119039) (by norm_num)
theorem B1433605 : Blo 846354 1433605 := bbase (se 4 (by rfl) ⟨134400, by rfl⟩ : syracuseStep 1433605 = 268801) (by norm_num)
theorem B1269773 : Blo 846354 1269773 := bbase (se 3 (by rfl) ⟨238082, by rfl⟩ : syracuseStep 1269773 = 476165) (by norm_num)
theorem B1269797 : Blo 846354 1269797 := bbase (se 4 (by rfl) ⟨119043, by rfl⟩ : syracuseStep 1269797 = 238087) (by norm_num)
theorem B1073189 : Blo 846354 1073189 := bbase (se 4 (by rfl) ⟨100611, by rfl⟩ : syracuseStep 1073189 = 201223) (by norm_num)
theorem B1269821 : Blo 846354 1269821 := bbase (se 3 (by rfl) ⟨238091, by rfl⟩ : syracuseStep 1269821 = 476183) (by norm_num)
theorem B1269845 : Blo 846354 1269845 := bbase (se 8 (by rfl) ⟨7440, by rfl⟩ : syracuseStep 1269845 = 14881) (by norm_num)
theorem B1073245 : Blo 846354 1073245 := bbase (se 3 (by rfl) ⟨201233, by rfl⟩ : syracuseStep 1073245 = 402467) (by norm_num)
theorem B1433693 : Blo 846354 1433693 := bbase (se 3 (by rfl) ⟨268817, by rfl⟩ : syracuseStep 1433693 = 537635) (by norm_num)
theorem B1269869 : Blo 846354 1269869 := bbase (se 3 (by rfl) ⟨238100, by rfl⟩ : syracuseStep 1269869 = 476201) (by norm_num)
theorem B1269893 : Blo 846354 1269893 := bbase (se 4 (by rfl) ⟨119052, by rfl⟩ : syracuseStep 1269893 = 238105) (by norm_num)
theorem B1532045 : Blo 846354 1532045 := bbase (se 3 (by rfl) ⟨287258, by rfl⟩ : syracuseStep 1532045 = 574517) (by norm_num)
theorem B1269917 : Blo 846354 1269917 := bbase (se 3 (by rfl) ⟨238109, by rfl⟩ : syracuseStep 1269917 = 476219) (by norm_num)
theorem B1269941 : Blo 846354 1269941 := bbase (se 5 (by rfl) ⟨59528, by rfl⟩ : syracuseStep 1269941 = 119057) (by norm_num)
theorem B4841653 : Blo 846354 4841653 := bbase (se 5 (by rfl) ⟨226952, by rfl⟩ : syracuseStep 4841653 = 453905) (by norm_num)
theorem B1073341 : Blo 846354 1073341 := bbase (se 3 (by rfl) ⟨201251, by rfl⟩ : syracuseStep 1073341 = 402503) (by norm_num)
theorem B1269965 : Blo 846354 1269965 := bbase (se 3 (by rfl) ⟨238118, by rfl⟩ : syracuseStep 1269965 = 476237) (by norm_num)
theorem B1433821 : Blo 846354 1433821 := bbase (se 3 (by rfl) ⟨268841, by rfl⟩ : syracuseStep 1433821 = 537683) (by norm_num)
theorem B1269989 : Blo 846354 1269989 := bbase (se 4 (by rfl) ⟨119061, by rfl⟩ : syracuseStep 1269989 = 238123) (by norm_num)
theorem B1270013 : Blo 846354 1270013 := bbase (se 3 (by rfl) ⟨238127, by rfl⟩ : syracuseStep 1270013 = 476255) (by norm_num)
theorem B1270037 : Blo 846354 1270037 := bbase (se 6 (by rfl) ⟨29766, by rfl⟩ : syracuseStep 1270037 = 59533) (by norm_num)
theorem B1270061 : Blo 846354 1270061 := bbase (se 3 (by rfl) ⟨238136, by rfl⟩ : syracuseStep 1270061 = 476273) (by norm_num)
theorem B1433909 : Blo 846354 1433909 := bbase (se 5 (by rfl) ⟨67214, by rfl⟩ : syracuseStep 1433909 = 134429) (by norm_num)
theorem B1270085 : Blo 846354 1270085 := bbase (se 4 (by rfl) ⟨119070, by rfl⟩ : syracuseStep 1270085 = 238141) (by norm_num)
theorem B1270109 : Blo 846354 1270109 := bbase (se 3 (by rfl) ⟨238145, by rfl⟩ : syracuseStep 1270109 = 476291) (by norm_num)
theorem B1073513 : Blo 846354 1073513 := bbase (se 2 (by rfl) ⟨402567, by rfl⟩ : syracuseStep 1073513 = 805135) (by norm_num)
theorem B1270133 : Blo 846354 1270133 := bbase (se 5 (by rfl) ⟨59537, by rfl⟩ : syracuseStep 1270133 = 119075) (by norm_num)
theorem B1270157 : Blo 846354 1270157 := bbase (se 3 (by rfl) ⟨238154, by rfl⟩ : syracuseStep 1270157 = 476309) (by norm_num)
theorem B1073569 : Blo 846354 1073569 := bbase (se 2 (by rfl) ⟨402588, by rfl⟩ : syracuseStep 1073569 = 805177) (by norm_num)
theorem B1270181 : Blo 846354 1270181 := bbase (se 4 (by rfl) ⟨119079, by rfl⟩ : syracuseStep 1270181 = 238159) (by norm_num)
theorem B1434037 : Blo 846354 1434037 := bbase (se 5 (by rfl) ⟨67220, by rfl⟩ : syracuseStep 1434037 = 134441) (by norm_num)
theorem B1270205 : Blo 846354 1270205 := bbase (se 3 (by rfl) ⟨238163, by rfl⟩ : syracuseStep 1270205 = 476327) (by norm_num)
theorem B1270229 : Blo 846354 1270229 := bbase (se 7 (by rfl) ⟨14885, by rfl⟩ : syracuseStep 1270229 = 29771) (by norm_num)
theorem B1270253 : Blo 846354 1270253 := bbase (se 3 (by rfl) ⟨238172, by rfl⟩ : syracuseStep 1270253 = 476345) (by norm_num)
theorem B1073665 : Blo 846354 1073665 := bbase (se 2 (by rfl) ⟨402624, by rfl⟩ : syracuseStep 1073665 = 805249) (by norm_num)
theorem B1270277 : Blo 846354 1270277 := bbase (se 4 (by rfl) ⟨119088, by rfl⟩ : syracuseStep 1270277 = 238177) (by norm_num)
theorem B1434125 : Blo 846354 1434125 := bbase (se 3 (by rfl) ⟨268898, by rfl⟩ : syracuseStep 1434125 = 537797) (by norm_num)
theorem B1270301 : Blo 846354 1270301 := bbase (se 3 (by rfl) ⟨238181, by rfl⟩ : syracuseStep 1270301 = 476363) (by norm_num)
theorem B1270325 : Blo 846354 1270325 := bbase (se 5 (by rfl) ⟨59546, by rfl⟩ : syracuseStep 1270325 = 119093) (by norm_num)
theorem B1270349 : Blo 846354 1270349 := bbase (se 3 (by rfl) ⟨238190, by rfl⟩ : syracuseStep 1270349 = 476381) (by norm_num)
theorem B1270373 : Blo 846354 1270373 := bbase (se 4 (by rfl) ⟨119097, by rfl⟩ : syracuseStep 1270373 = 238195) (by norm_num)
theorem B1270397 : Blo 846354 1270397 := bbase (se 3 (by rfl) ⟨238199, by rfl⟩ : syracuseStep 1270397 = 476399) (by norm_num)
theorem B4285061 : Blo 846354 4285061 := bbase (se 4 (by rfl) ⟨401724, by rfl⟩ : syracuseStep 4285061 = 803449) (by norm_num)
theorem B1434253 : Blo 846354 1434253 := bbase (se 3 (by rfl) ⟨268922, by rfl⟩ : syracuseStep 1434253 = 537845) (by norm_num)
theorem B1270421 : Blo 846354 1270421 := bbase (se 6 (by rfl) ⟨29775, by rfl⟩ : syracuseStep 1270421 = 59551) (by norm_num)
theorem B1270445 : Blo 846354 1270445 := bbase (se 3 (by rfl) ⟨238208, by rfl⟩ : syracuseStep 1270445 = 476417) (by norm_num)
theorem B1073837 : Blo 846354 1073837 := bbase (se 3 (by rfl) ⟨201344, by rfl⟩ : syracuseStep 1073837 = 402689) (by norm_num)
theorem B1270469 : Blo 846354 1270469 := bbase (se 4 (by rfl) ⟨119106, by rfl⟩ : syracuseStep 1270469 = 238213) (by norm_num)
theorem B1270493 : Blo 846354 1270493 := bbase (se 3 (by rfl) ⟨238217, by rfl⟩ : syracuseStep 1270493 = 476435) (by norm_num)
theorem B1073893 : Blo 846354 1073893 := bbase (se 4 (by rfl) ⟨100677, by rfl⟩ : syracuseStep 1073893 = 201355) (by norm_num)
theorem B1434341 : Blo 846354 1434341 := bbase (se 4 (by rfl) ⟨134469, by rfl⟩ : syracuseStep 1434341 = 268939) (by norm_num)
theorem B1270517 : Blo 846354 1270517 := bbase (se 5 (by rfl) ⟨59555, by rfl⟩ : syracuseStep 1270517 = 119111) (by norm_num)
theorem B1270541 : Blo 846354 1270541 := bbase (se 3 (by rfl) ⟨238226, by rfl⟩ : syracuseStep 1270541 = 476453) (by norm_num)
theorem B1270565 : Blo 846354 1270565 := bbase (se 4 (by rfl) ⟨119115, by rfl⟩ : syracuseStep 1270565 = 238231) (by norm_num)
theorem B1270589 : Blo 846354 1270589 := bbase (se 3 (by rfl) ⟨238235, by rfl⟩ : syracuseStep 1270589 = 476471) (by norm_num)
theorem B1073989 : Blo 846354 1073989 := bbase (se 4 (by rfl) ⟨100686, by rfl⟩ : syracuseStep 1073989 = 201373) (by norm_num)
theorem B1270613 : Blo 846354 1270613 := bbase (se 9 (by rfl) ⟨3722, by rfl⟩ : syracuseStep 1270613 = 7445) (by norm_num)
theorem B1434469 : Blo 846354 1434469 := bbase (se 4 (by rfl) ⟨134481, by rfl⟩ : syracuseStep 1434469 = 268963) (by norm_num)
theorem B2909029 : Blo 846354 2909029 := bbase (se 4 (by rfl) ⟨272721, by rfl⟩ : syracuseStep 2909029 = 545443) (by norm_num)
theorem B1270637 : Blo 846354 1270637 := bbase (se 3 (by rfl) ⟨238244, by rfl⟩ : syracuseStep 1270637 = 476489) (by norm_num)
theorem B3433349 : Blo 846354 3433349 := bbase (se 4 (by rfl) ⟨321876, by rfl⟩ : syracuseStep 3433349 = 643753) (by norm_num)
theorem B1270661 : Blo 846354 1270661 := bbase (se 4 (by rfl) ⟨119124, by rfl⟩ : syracuseStep 1270661 = 238249) (by norm_num)
theorem B1270685 : Blo 846354 1270685 := bbase (se 3 (by rfl) ⟨238253, by rfl⟩ : syracuseStep 1270685 = 476507) (by norm_num)
theorem B1270709 : Blo 846354 1270709 := bbase (se 5 (by rfl) ⟨59564, by rfl⟩ : syracuseStep 1270709 = 119129) (by norm_num)
theorem B1434557 : Blo 846354 1434557 := bbase (se 3 (by rfl) ⟨268979, by rfl⟩ : syracuseStep 1434557 = 537959) (by norm_num)
theorem B1270733 : Blo 846354 1270733 := bbase (se 3 (by rfl) ⟨238262, by rfl⟩ : syracuseStep 1270733 = 476525) (by norm_num)
theorem B1270757 : Blo 846354 1270757 := bbase (se 4 (by rfl) ⟨119133, by rfl⟩ : syracuseStep 1270757 = 238267) (by norm_num)
theorem B1074161 : Blo 846354 1074161 := bbase (se 2 (by rfl) ⟨402810, by rfl⟩ : syracuseStep 1074161 = 805621) (by norm_num)
theorem B1270781 : Blo 846354 1270781 := bbase (se 3 (by rfl) ⟨238271, by rfl⟩ : syracuseStep 1270781 = 476543) (by norm_num)
theorem B1270805 : Blo 846354 1270805 := bbase (se 6 (by rfl) ⟨29784, by rfl⟩ : syracuseStep 1270805 = 59569) (by norm_num)
theorem B1074217 : Blo 846354 1074217 := bbase (se 2 (by rfl) ⟨402831, by rfl⟩ : syracuseStep 1074217 = 805663) (by norm_num)
theorem B1270829 : Blo 846354 1270829 := bbase (se 3 (by rfl) ⟨238280, by rfl⟩ : syracuseStep 1270829 = 476561) (by norm_num)
theorem B1434685 : Blo 846354 1434685 := bbase (se 3 (by rfl) ⟨269003, by rfl⟩ : syracuseStep 1434685 = 538007) (by norm_num)
theorem B1270853 : Blo 846354 1270853 := bbase (se 4 (by rfl) ⟨119142, by rfl⟩ : syracuseStep 1270853 = 238285) (by norm_num)
theorem B1270877 : Blo 846354 1270877 := bbase (se 3 (by rfl) ⟨238289, by rfl⟩ : syracuseStep 1270877 = 476579) (by norm_num)
theorem B1270901 : Blo 846354 1270901 := bbase (se 5 (by rfl) ⟨59573, by rfl⟩ : syracuseStep 1270901 = 119147) (by norm_num)
theorem B1074313 : Blo 846354 1074313 := bbase (se 2 (by rfl) ⟨402867, by rfl⟩ : syracuseStep 1074313 = 805735) (by norm_num)
theorem B1270925 : Blo 846354 1270925 := bbase (se 3 (by rfl) ⟨238298, by rfl⟩ : syracuseStep 1270925 = 476597) (by norm_num)
theorem B1434773 : Blo 846354 1434773 := bbase (se 6 (by rfl) ⟨33627, by rfl⟩ : syracuseStep 1434773 = 67255) (by norm_num)
theorem B1270949 : Blo 846354 1270949 := bbase (se 4 (by rfl) ⟨119151, by rfl⟩ : syracuseStep 1270949 = 238303) (by norm_num)
theorem B6120629 : Blo 846354 6120629 := bbase (se 5 (by rfl) ⟨286904, by rfl⟩ : syracuseStep 6120629 = 573809) (by norm_num)
theorem B1270973 : Blo 846354 1270973 := bbase (se 3 (by rfl) ⟨238307, by rfl⟩ : syracuseStep 1270973 = 476615) (by norm_num)
theorem B1270997 : Blo 846354 1270997 := bbase (se 7 (by rfl) ⟨14894, by rfl⟩ : syracuseStep 1270997 = 29789) (by norm_num)
theorem B1271021 : Blo 846354 1271021 := bbase (se 3 (by rfl) ⟨238316, by rfl⟩ : syracuseStep 1271021 = 476633) (by norm_num)
theorem B1271045 : Blo 846354 1271045 := bbase (se 4 (by rfl) ⟨119160, by rfl⟩ : syracuseStep 1271045 = 238321) (by norm_num)
theorem B1434901 : Blo 846354 1434901 := bbase (se 6 (by rfl) ⟨33630, by rfl⟩ : syracuseStep 1434901 = 67261) (by norm_num)
theorem B1205533 : Blo 846354 1205533 := bbase (se 3 (by rfl) ⟨226037, by rfl⟩ : syracuseStep 1205533 = 452075) (by norm_num)
theorem B1271069 : Blo 846354 1271069 := bbase (se 3 (by rfl) ⟨238325, by rfl⟩ : syracuseStep 1271069 = 476651) (by norm_num)
theorem B2417957 : Blo 846354 2417957 := bbase (se 4 (by rfl) ⟨226683, by rfl⟩ : syracuseStep 2417957 = 453367) (by norm_num)
theorem B1271093 : Blo 846354 1271093 := bbase (se 5 (by rfl) ⟨59582, by rfl⟩ : syracuseStep 1271093 = 119165) (by norm_num)
theorem B1074485 : Blo 846354 1074485 := bbase (se 5 (by rfl) ⟨50366, by rfl⟩ : syracuseStep 1074485 = 100733) (by norm_num)
theorem B1271117 : Blo 846354 1271117 := bbase (se 3 (by rfl) ⟨238334, by rfl⟩ : syracuseStep 1271117 = 476669) (by norm_num)
theorem B1271141 : Blo 846354 1271141 := bbase (se 4 (by rfl) ⟨119169, by rfl⟩ : syracuseStep 1271141 = 238339) (by norm_num)
theorem B1074541 : Blo 846354 1074541 := bbase (se 3 (by rfl) ⟨201476, by rfl⟩ : syracuseStep 1074541 = 402953) (by norm_num)
theorem B1271165 : Blo 846354 1271165 := bbase (se 3 (by rfl) ⟨238343, by rfl⟩ : syracuseStep 1271165 = 476687) (by norm_num)
theorem B1271189 : Blo 846354 1271189 := bbase (se 6 (by rfl) ⟨29793, by rfl⟩ : syracuseStep 1271189 = 59587) (by norm_num)
theorem B1271213 : Blo 846354 1271213 := bbase (se 3 (by rfl) ⟨238352, by rfl⟩ : syracuseStep 1271213 = 476705) (by norm_num)
theorem B7333301 : Blo 846354 7333301 := bbase (se 5 (by rfl) ⟨343748, by rfl⟩ : syracuseStep 7333301 = 687497) (by norm_num)
theorem B1271237 : Blo 846354 1271237 := bbase (se 4 (by rfl) ⟨119178, by rfl⟩ : syracuseStep 1271237 = 238357) (by norm_num)
theorem B1074637 : Blo 846354 1074637 := bbase (se 3 (by rfl) ⟨201494, by rfl⟩ : syracuseStep 1074637 = 402989) (by norm_num)
theorem B1271261 : Blo 846354 1271261 := bbase (se 3 (by rfl) ⟨238361, by rfl⟩ : syracuseStep 1271261 = 476723) (by norm_num)
theorem B1271285 : Blo 846354 1271285 := bbase (se 5 (by rfl) ⟨59591, by rfl⟩ : syracuseStep 1271285 = 119183) (by norm_num)
theorem B1271309 : Blo 846354 1271309 := bbase (se 3 (by rfl) ⟨238370, by rfl⟩ : syracuseStep 1271309 = 476741) (by norm_num)
theorem B1271333 : Blo 846354 1271333 := bbase (se 4 (by rfl) ⟨119187, by rfl⟩ : syracuseStep 1271333 = 238375) (by norm_num)
theorem B1271357 : Blo 846354 1271357 := bbase (se 3 (by rfl) ⟨238379, by rfl⟩ : syracuseStep 1271357 = 476759) (by norm_num)
theorem B1271381 : Blo 846354 1271381 := bbase (se 8 (by rfl) ⟨7449, by rfl⟩ : syracuseStep 1271381 = 14899) (by norm_num)
theorem B1205869 : Blo 846354 1205869 := bbase (se 3 (by rfl) ⟨226100, by rfl⟩ : syracuseStep 1205869 = 452201) (by norm_num)
theorem B1271405 : Blo 846354 1271405 := bbase (se 3 (by rfl) ⟨238388, by rfl⟩ : syracuseStep 1271405 = 476777) (by norm_num)
theorem B1074809 : Blo 846354 1074809 := bbase (se 2 (by rfl) ⟨403053, by rfl⟩ : syracuseStep 1074809 = 806107) (by norm_num)
theorem B1271429 : Blo 846354 1271429 := bbase (se 4 (by rfl) ⟨119196, by rfl⟩ : syracuseStep 1271429 = 238393) (by norm_num)
theorem B1271453 : Blo 846354 1271453 := bbase (se 3 (by rfl) ⟨238397, by rfl⟩ : syracuseStep 1271453 = 476795) (by norm_num)
theorem B1074865 : Blo 846354 1074865 := bbase (se 2 (by rfl) ⟨403074, by rfl⟩ : syracuseStep 1074865 = 806149) (by norm_num)
theorem B1271477 : Blo 846354 1271477 := bbase (se 5 (by rfl) ⟨59600, by rfl⟩ : syracuseStep 1271477 = 119201) (by norm_num)
theorem B1271501 : Blo 846354 1271501 := bbase (se 3 (by rfl) ⟨238406, by rfl⟩ : syracuseStep 1271501 = 476813) (by norm_num)
theorem B1271525 : Blo 846354 1271525 := bbase (se 4 (by rfl) ⟨119205, by rfl⟩ : syracuseStep 1271525 = 238411) (by norm_num)
theorem B2713333 : Blo 846354 2713333 := bbase (se 5 (by rfl) ⟨127187, by rfl⟩ : syracuseStep 2713333 = 254375) (by norm_num)
theorem B1271549 : Blo 846354 1271549 := bbase (se 3 (by rfl) ⟨238415, by rfl⟩ : syracuseStep 1271549 = 476831) (by norm_num)
theorem B1074961 : Blo 846354 1074961 := bbase (se 2 (by rfl) ⟨403110, by rfl⟩ : syracuseStep 1074961 = 806221) (by norm_num)
theorem B1271573 : Blo 846354 1271573 := bbase (se 6 (by rfl) ⟨29802, by rfl⟩ : syracuseStep 1271573 = 59605) (by norm_num)
theorem B4351781 : Blo 846354 4351781 := bbase (se 4 (by rfl) ⟨407979, by rfl⟩ : syracuseStep 4351781 = 815959) (by norm_num)
theorem B1271597 : Blo 846354 1271597 := bbase (se 3 (by rfl) ⟨238424, by rfl⟩ : syracuseStep 1271597 = 476849) (by norm_num)
theorem B4581173 : Blo 846354 4581173 := bbase (se 5 (by rfl) ⟨214742, by rfl⟩ : syracuseStep 4581173 = 429485) (by norm_num)
theorem B1206085 : Blo 846354 1206085 := bbase (se 4 (by rfl) ⟨113070, by rfl⟩ : syracuseStep 1206085 = 226141) (by norm_num)
theorem B1271621 : Blo 846354 1271621 := bbase (se 4 (by rfl) ⟨119214, by rfl⟩ : syracuseStep 1271621 = 238429) (by norm_num)
theorem B1271645 : Blo 846354 1271645 := bbase (se 3 (by rfl) ⟨238433, by rfl⟩ : syracuseStep 1271645 = 476867) (by norm_num)
theorem B1271669 : Blo 846354 1271669 := bbase (se 5 (by rfl) ⟨59609, by rfl⟩ : syracuseStep 1271669 = 119219) (by norm_num)
theorem B1271693 : Blo 846354 1271693 := bbase (se 3 (by rfl) ⟨238442, by rfl⟩ : syracuseStep 1271693 = 476885) (by norm_num)
theorem B4286357 : Blo 846354 4286357 := bbase (se 6 (by rfl) ⟨100461, by rfl⟩ : syracuseStep 4286357 = 200923) (by norm_num)
theorem B14903189 : Blo 846354 14903189 := bbase (se 6 (by rfl) ⟨349293, by rfl⟩ : syracuseStep 14903189 = 698587) (by norm_num)
theorem B1271717 : Blo 846354 1271717 := bbase (se 4 (by rfl) ⟨119223, by rfl⟩ : syracuseStep 1271717 = 238447) (by norm_num)
theorem B1271741 : Blo 846354 1271741 := bbase (se 3 (by rfl) ⟨238451, by rfl⟩ : syracuseStep 1271741 = 476903) (by norm_num)
theorem B1075133 : Blo 846354 1075133 := bbase (se 3 (by rfl) ⟨201587, by rfl⟩ : syracuseStep 1075133 = 403175) (by norm_num)
theorem B1468373 : Blo 846354 1468373 := bbase (se 7 (by rfl) ⟨17207, by rfl⟩ : syracuseStep 1468373 = 34415) (by norm_num)
theorem B1271765 : Blo 846354 1271765 := bbase (se 7 (by rfl) ⟨14903, by rfl⟩ : syracuseStep 1271765 = 29807) (by norm_num)
theorem B1271789 : Blo 846354 1271789 := bbase (se 3 (by rfl) ⟨238460, by rfl⟩ : syracuseStep 1271789 = 476921) (by norm_num)
theorem B2713589 : Blo 846354 2713589 := bbase (se 5 (by rfl) ⟨127199, by rfl⟩ : syracuseStep 2713589 = 254399) (by norm_num)
theorem B1075189 : Blo 846354 1075189 := bbase (se 5 (by rfl) ⟨50399, by rfl⟩ : syracuseStep 1075189 = 100799) (by norm_num)
theorem B1271813 : Blo 846354 1271813 := bbase (se 4 (by rfl) ⟨119232, by rfl⟩ : syracuseStep 1271813 = 238465) (by norm_num)
theorem B1271837 : Blo 846354 1271837 := bbase (se 3 (by rfl) ⟨238469, by rfl⟩ : syracuseStep 1271837 = 476939) (by norm_num)
theorem B1271861 : Blo 846354 1271861 := bbase (se 5 (by rfl) ⟨59618, by rfl⟩ : syracuseStep 1271861 = 119237) (by norm_num)
theorem B1271885 : Blo 846354 1271885 := bbase (se 3 (by rfl) ⟨238478, by rfl⟩ : syracuseStep 1271885 = 476957) (by norm_num)
theorem B3434581 : Blo 846354 3434581 := bbase (se 8 (by rfl) ⟨20124, by rfl⟩ : syracuseStep 3434581 = 40249) (by norm_num)
theorem B1075285 : Blo 846354 1075285 := bbase (se 8 (by rfl) ⟨6300, by rfl⟩ : syracuseStep 1075285 = 12601) (by norm_num)
theorem B1271909 : Blo 846354 1271909 := bbase (se 4 (by rfl) ⟨119241, by rfl⟩ : syracuseStep 1271909 = 238483) (by norm_num)
theorem B1271933 : Blo 846354 1271933 := bbase (se 3 (by rfl) ⟨238487, by rfl⟩ : syracuseStep 1271933 = 476975) (by norm_num)
theorem B1271957 : Blo 846354 1271957 := bbase (se 6 (by rfl) ⟨29811, by rfl⟩ : syracuseStep 1271957 = 59623) (by norm_num)
theorem B1271981 : Blo 846354 1271981 := bbase (se 3 (by rfl) ⟨238496, by rfl⟩ : syracuseStep 1271981 = 476993) (by norm_num)
theorem B1206461 : Blo 846354 1206461 := bbase (se 3 (by rfl) ⟨226211, by rfl⟩ : syracuseStep 1206461 = 452423) (by norm_num)
theorem B1272005 : Blo 846354 1272005 := bbase (se 4 (by rfl) ⟨119250, by rfl⟩ : syracuseStep 1272005 = 238501) (by norm_num)
theorem B1272029 : Blo 846354 1272029 := bbase (se 3 (by rfl) ⟨238505, by rfl⟩ : syracuseStep 1272029 = 477011) (by norm_num)
theorem B1272053 : Blo 846354 1272053 := bbase (se 5 (by rfl) ⟨59627, by rfl⟩ : syracuseStep 1272053 = 119255) (by norm_num)
theorem B1075457 : Blo 846354 1075457 := bbase (se 2 (by rfl) ⟨403296, by rfl⟩ : syracuseStep 1075457 = 806593) (by norm_num)
theorem B1272077 : Blo 846354 1272077 := bbase (se 3 (by rfl) ⟨238514, by rfl⟩ : syracuseStep 1272077 = 477029) (by norm_num)
theorem B1272101 : Blo 846354 1272101 := bbase (se 4 (by rfl) ⟨119259, by rfl⟩ : syracuseStep 1272101 = 238519) (by norm_num)
theorem B1075513 : Blo 846354 1075513 := bbase (se 2 (by rfl) ⟨403317, by rfl⟩ : syracuseStep 1075513 = 806635) (by norm_num)
theorem B1272125 : Blo 846354 1272125 := bbase (se 3 (by rfl) ⟨238523, by rfl⟩ : syracuseStep 1272125 = 477047) (by norm_num)
theorem B1272149 : Blo 846354 1272149 := bbase (se 10 (by rfl) ⟨1863, by rfl⟩ : syracuseStep 1272149 = 3727) (by norm_num)
theorem B1272173 : Blo 846354 1272173 := bbase (se 3 (by rfl) ⟨238532, by rfl⟩ : syracuseStep 1272173 = 477065) (by norm_num)
theorem B1272197 : Blo 846354 1272197 := bbase (se 4 (by rfl) ⟨119268, by rfl⟩ : syracuseStep 1272197 = 238537) (by norm_num)
theorem B1075609 : Blo 846354 1075609 := bbase (se 2 (by rfl) ⟨403353, by rfl⟩ : syracuseStep 1075609 = 806707) (by norm_num)
theorem B1272221 : Blo 846354 1272221 := bbase (se 3 (by rfl) ⟨238541, by rfl⟩ : syracuseStep 1272221 = 477083) (by norm_num)
theorem B1272245 : Blo 846354 1272245 := bbase (se 5 (by rfl) ⟨59636, by rfl⟩ : syracuseStep 1272245 = 119273) (by norm_num)
theorem B2419141 : Blo 846354 2419141 := bbase (se 4 (by rfl) ⟨226794, by rfl⟩ : syracuseStep 2419141 = 453589) (by norm_num)
theorem B1272269 : Blo 846354 1272269 := bbase (se 3 (by rfl) ⟨238550, by rfl⟩ : syracuseStep 1272269 = 477101) (by norm_num)
theorem B1272293 : Blo 846354 1272293 := bbase (se 4 (by rfl) ⟨119277, by rfl⟩ : syracuseStep 1272293 = 238555) (by norm_num)
theorem B1272317 : Blo 846354 1272317 := bbase (se 3 (by rfl) ⟨238559, by rfl⟩ : syracuseStep 1272317 = 477119) (by norm_num)
theorem B1272341 : Blo 846354 1272341 := bbase (se 6 (by rfl) ⟨29820, by rfl⟩ : syracuseStep 1272341 = 59641) (by norm_num)
theorem B1272365 : Blo 846354 1272365 := bbase (se 3 (by rfl) ⟨238568, by rfl⟩ : syracuseStep 1272365 = 477137) (by norm_num)
theorem B1272389 : Blo 846354 1272389 := bbase (se 4 (by rfl) ⟨119286, by rfl⟩ : syracuseStep 1272389 = 238573) (by norm_num)
theorem B1075781 : Blo 846354 1075781 := bbase (se 4 (by rfl) ⟨100854, by rfl⟩ : syracuseStep 1075781 = 201709) (by norm_num)
theorem B1272413 : Blo 846354 1272413 := bbase (se 3 (by rfl) ⟨238577, by rfl⟩ : syracuseStep 1272413 = 477155) (by norm_num)
theorem B2419301 : Blo 846354 2419301 := bbase (se 4 (by rfl) ⟨226809, by rfl⟩ : syracuseStep 2419301 = 453619) (by norm_num)
theorem B1272437 : Blo 846354 1272437 := bbase (se 5 (by rfl) ⟨59645, by rfl⟩ : syracuseStep 1272437 = 119291) (by norm_num)
theorem B1075837 : Blo 846354 1075837 := bbase (se 3 (by rfl) ⟨201719, by rfl⟩ : syracuseStep 1075837 = 403439) (by norm_num)
theorem B1272461 : Blo 846354 1272461 := bbase (se 3 (by rfl) ⟨238586, by rfl⟩ : syracuseStep 1272461 = 477173) (by norm_num)
theorem B1272485 : Blo 846354 1272485 := bbase (se 4 (by rfl) ⟨119295, by rfl⟩ : syracuseStep 1272485 = 238591) (by norm_num)
theorem B1272509 : Blo 846354 1272509 := bbase (se 3 (by rfl) ⟨238595, by rfl⟩ : syracuseStep 1272509 = 477191) (by norm_num)
theorem B1272533 : Blo 846354 1272533 := bbase (se 7 (by rfl) ⟨14912, by rfl⟩ : syracuseStep 1272533 = 29825) (by norm_num)
theorem B1075933 : Blo 846354 1075933 := bbase (se 3 (by rfl) ⟨201737, by rfl⟩ : syracuseStep 1075933 = 403475) (by norm_num)
theorem B1305317 : Blo 846354 1305317 := bbase (se 4 (by rfl) ⟨122373, by rfl⟩ : syracuseStep 1305317 = 244747) (by norm_num)
theorem B1272557 : Blo 846354 1272557 := bbase (se 3 (by rfl) ⟨238604, by rfl⟩ : syracuseStep 1272557 = 477209) (by norm_num)
theorem B1272581 : Blo 846354 1272581 := bbase (se 4 (by rfl) ⟨119304, by rfl⟩ : syracuseStep 1272581 = 238609) (by norm_num)
theorem B1272605 : Blo 846354 1272605 := bbase (se 3 (by rfl) ⟨238613, by rfl⟩ : syracuseStep 1272605 = 477227) (by norm_num)
theorem B1272629 : Blo 846354 1272629 := bbase (se 5 (by rfl) ⟨59654, by rfl⟩ : syracuseStep 1272629 = 119309) (by norm_num)
theorem B1272653 : Blo 846354 1272653 := bbase (se 3 (by rfl) ⟨238622, by rfl⟩ : syracuseStep 1272653 = 477245) (by norm_num)
theorem B2419541 : Blo 846354 2419541 := bbase (se 9 (by rfl) ⟨7088, by rfl⟩ : syracuseStep 2419541 = 14177) (by norm_num)
theorem B1272677 : Blo 846354 1272677 := bbase (se 4 (by rfl) ⟨119313, by rfl⟩ : syracuseStep 1272677 = 238627) (by norm_num)
theorem B1272701 : Blo 846354 1272701 := bbase (se 3 (by rfl) ⟨238631, by rfl⟩ : syracuseStep 1272701 = 477263) (by norm_num)
theorem B1076105 : Blo 846354 1076105 := bbase (se 2 (by rfl) ⟨403539, by rfl⟩ : syracuseStep 1076105 = 807079) (by norm_num)
theorem B1272725 : Blo 846354 1272725 := bbase (se 6 (by rfl) ⟨29829, by rfl⟩ : syracuseStep 1272725 = 59659) (by norm_num)
theorem B1272749 : Blo 846354 1272749 := bbase (se 3 (by rfl) ⟨238640, by rfl⟩ : syracuseStep 1272749 = 477281) (by norm_num)
theorem B1076161 : Blo 846354 1076161 := bbase (se 2 (by rfl) ⟨403560, by rfl⟩ : syracuseStep 1076161 = 807121) (by norm_num)
theorem B1272773 : Blo 846354 1272773 := bbase (se 4 (by rfl) ⟨119322, by rfl⟩ : syracuseStep 1272773 = 238645) (by norm_num)
theorem B1272797 : Blo 846354 1272797 := bbase (se 3 (by rfl) ⟨238649, by rfl⟩ : syracuseStep 1272797 = 477299) (by norm_num)
theorem B3435493 : Blo 846354 3435493 := bbase (se 4 (by rfl) ⟨322077, by rfl⟩ : syracuseStep 3435493 = 644155) (by norm_num)
theorem B1272821 : Blo 846354 1272821 := bbase (se 5 (by rfl) ⟨59663, by rfl⟩ : syracuseStep 1272821 = 119327) (by norm_num)
theorem B1272845 : Blo 846354 1272845 := bbase (se 3 (by rfl) ⟨238658, by rfl⟩ : syracuseStep 1272845 = 477317) (by norm_num)
theorem B15494165 : Blo 846354 15494165 := bbase (se 6 (by rfl) ⟨363144, by rfl⟩ : syracuseStep 15494165 = 726289) (by norm_num)
theorem B2419733 : Blo 846354 2419733 := bbase (se 6 (by rfl) ⟨56712, by rfl⟩ : syracuseStep 2419733 = 113425) (by norm_num)
theorem B1272869 : Blo 846354 1272869 := bbase (se 4 (by rfl) ⟨119331, by rfl⟩ : syracuseStep 1272869 = 238663) (by norm_num)
theorem B1272893 : Blo 846354 1272893 := bbase (se 3 (by rfl) ⟨238667, by rfl⟩ : syracuseStep 1272893 = 477335) (by norm_num)
theorem B3632197 : Blo 846354 3632197 := bbase (se 4 (by rfl) ⟨340518, by rfl⟩ : syracuseStep 3632197 = 681037) (by norm_num)
theorem B1272917 : Blo 846354 1272917 := bbase (se 8 (by rfl) ⟨7458, by rfl⟩ : syracuseStep 1272917 = 14917) (by norm_num)
theorem B1272941 : Blo 846354 1272941 := bbase (se 3 (by rfl) ⟨238676, by rfl⟩ : syracuseStep 1272941 = 477353) (by norm_num)
theorem B945265 : Blo 846354 945265 := bbase (se 2 (by rfl) ⟨354474, by rfl⟩ : syracuseStep 945265 = 708949) (by norm_num)
theorem B1272965 : Blo 846354 1272965 := bbase (se 4 (by rfl) ⟨119340, by rfl⟩ : syracuseStep 1272965 = 238681) (by norm_num)
theorem B1272989 : Blo 846354 1272989 := bbase (se 3 (by rfl) ⟨238685, by rfl⟩ : syracuseStep 1272989 = 477371) (by norm_num)
theorem B4287653 : Blo 846354 4287653 := bbase (se 4 (by rfl) ⟨401967, by rfl⟩ : syracuseStep 4287653 = 803935) (by norm_num)
theorem B1273013 : Blo 846354 1273013 := bbase (se 5 (by rfl) ⟨59672, by rfl⟩ : syracuseStep 1273013 = 119345) (by norm_num)
theorem B2288837 : Blo 846354 2288837 := bbase (se 4 (by rfl) ⟨214578, by rfl⟩ : syracuseStep 2288837 = 429157) (by norm_num)
theorem B1273037 : Blo 846354 1273037 := bbase (se 3 (by rfl) ⟨238694, by rfl⟩ : syracuseStep 1273037 = 477389) (by norm_num)
theorem B1273061 : Blo 846354 1273061 := bbase (se 4 (by rfl) ⟨119349, by rfl⟩ : syracuseStep 1273061 = 238699) (by norm_num)
theorem B5434613 : Blo 846354 5434613 := bbase (se 5 (by rfl) ⟨254747, by rfl⟩ : syracuseStep 5434613 = 509495) (by norm_num)
theorem B1273085 : Blo 846354 1273085 := bbase (se 3 (by rfl) ⟨238703, by rfl⟩ : syracuseStep 1273085 = 477407) (by norm_num)
theorem B1273109 : Blo 846354 1273109 := bbase (se 6 (by rfl) ⟨29838, by rfl⟩ : syracuseStep 1273109 = 59677) (by norm_num)
theorem B1273133 : Blo 846354 1273133 := bbase (se 3 (by rfl) ⟨238712, by rfl⟩ : syracuseStep 1273133 = 477425) (by norm_num)
theorem B1273157 : Blo 846354 1273157 := bbase (se 4 (by rfl) ⟨119358, by rfl⟩ : syracuseStep 1273157 = 238717) (by norm_num)
theorem B1273181 : Blo 846354 1273181 := bbase (se 3 (by rfl) ⟨238721, by rfl⟩ : syracuseStep 1273181 = 477443) (by norm_num)
theorem B1273205 : Blo 846354 1273205 := bbase (se 5 (by rfl) ⟨59681, by rfl⟩ : syracuseStep 1273205 = 119363) (by norm_num)
theorem B1273229 : Blo 846354 1273229 := bbase (se 3 (by rfl) ⟨238730, by rfl⟩ : syracuseStep 1273229 = 477461) (by norm_num)
theorem B1273253 : Blo 846354 1273253 := bbase (se 4 (by rfl) ⟨119367, by rfl⟩ : syracuseStep 1273253 = 238735) (by norm_num)
theorem B1273277 : Blo 846354 1273277 := bbase (se 3 (by rfl) ⟨238739, by rfl⟩ : syracuseStep 1273277 = 477479) (by norm_num)
theorem B1273301 : Blo 846354 1273301 := bbase (se 7 (by rfl) ⟨14921, by rfl⟩ : syracuseStep 1273301 = 29843) (by norm_num)
theorem B1633765 : Blo 846354 1633765 := bbase (se 4 (by rfl) ⟨153165, by rfl⟩ : syracuseStep 1633765 = 306331) (by norm_num)
theorem B1273325 : Blo 846354 1273325 := bbase (se 3 (by rfl) ⟨238748, by rfl⟩ : syracuseStep 1273325 = 477497) (by norm_num)
theorem B6450677 : Blo 846354 6450677 := bbase (se 5 (by rfl) ⟨302375, by rfl⟩ : syracuseStep 6450677 = 604751) (by norm_num)
theorem B1273349 : Blo 846354 1273349 := bbase (se 4 (by rfl) ⟨119376, by rfl⟩ : syracuseStep 1273349 = 238753) (by norm_num)
theorem B1273373 : Blo 846354 1273373 := bbase (se 3 (by rfl) ⟨238757, by rfl⟩ : syracuseStep 1273373 = 477515) (by norm_num)
theorem B1273397 : Blo 846354 1273397 := bbase (se 5 (by rfl) ⟨59690, by rfl⟩ : syracuseStep 1273397 = 119381) (by norm_num)
theorem B1207885 : Blo 846354 1207885 := bbase (se 3 (by rfl) ⟨226478, by rfl⟩ : syracuseStep 1207885 = 452957) (by norm_num)
theorem B1273421 : Blo 846354 1273421 := bbase (se 3 (by rfl) ⟨238766, by rfl⟩ : syracuseStep 1273421 = 477533) (by norm_num)
theorem B3862117 : Blo 846354 3862117 := bbase (se 4 (by rfl) ⟨362073, by rfl⟩ : syracuseStep 3862117 = 724147) (by norm_num)
theorem B1273445 : Blo 846354 1273445 := bbase (se 4 (by rfl) ⟨119385, by rfl⟩ : syracuseStep 1273445 = 238771) (by norm_num)
theorem B1273469 : Blo 846354 1273469 := bbase (se 3 (by rfl) ⟨238775, by rfl⟩ : syracuseStep 1273469 = 477551) (by norm_num)
theorem B1273493 : Blo 846354 1273493 := bbase (se 6 (by rfl) ⟨29847, by rfl⟩ : syracuseStep 1273493 = 59695) (by norm_num)
theorem B1273517 : Blo 846354 1273517 := bbase (se 3 (by rfl) ⟨238784, by rfl⟩ : syracuseStep 1273517 = 477569) (by norm_num)
theorem B1273541 : Blo 846354 1273541 := bbase (se 4 (by rfl) ⟨119394, by rfl⟩ : syracuseStep 1273541 = 238789) (by norm_num)
theorem B4419269 : Blo 846354 4419269 := bbase (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) (by norm_num)
theorem B1633997 : Blo 846354 1633997 := bbase (se 3 (by rfl) ⟨306374, by rfl⟩ : syracuseStep 1633997 = 612749) (by norm_num)
theorem B9662165 : Blo 846354 9662165 := bbase (se 7 (by rfl) ⟨113228, by rfl⟩ : syracuseStep 9662165 = 226457) (by norm_num)
theorem B1273565 : Blo 846354 1273565 := bbase (se 3 (by rfl) ⟨238793, by rfl⟩ : syracuseStep 1273565 = 477587) (by norm_num)
theorem B1273589 : Blo 846354 1273589 := bbase (se 5 (by rfl) ⟨59699, by rfl⟩ : syracuseStep 1273589 = 119399) (by norm_num)
theorem B1273613 : Blo 846354 1273613 := bbase (se 3 (by rfl) ⟨238802, by rfl⟩ : syracuseStep 1273613 = 477605) (by norm_num)
theorem B1273637 : Blo 846354 1273637 := bbase (se 4 (by rfl) ⟨119403, by rfl⟩ : syracuseStep 1273637 = 238807) (by norm_num)
theorem B1273661 : Blo 846354 1273661 := bbase (se 3 (by rfl) ⟨238811, by rfl⟩ : syracuseStep 1273661 = 477623) (by norm_num)
theorem B1273685 : Blo 846354 1273685 := bbase (se 9 (by rfl) ⟨3731, by rfl⟩ : syracuseStep 1273685 = 7463) (by norm_num)
theorem B1273709 : Blo 846354 1273709 := bbase (se 3 (by rfl) ⟨238820, by rfl⟩ : syracuseStep 1273709 = 477641) (by norm_num)
theorem B1273733 : Blo 846354 1273733 := bbase (se 4 (by rfl) ⟨119412, by rfl⟩ : syracuseStep 1273733 = 238825) (by norm_num)
theorem B1273757 : Blo 846354 1273757 := bbase (se 3 (by rfl) ⟨238829, by rfl⟩ : syracuseStep 1273757 = 477659) (by norm_num)
theorem B1273781 : Blo 846354 1273781 := bbase (se 5 (by rfl) ⟨59708, by rfl⟩ : syracuseStep 1273781 = 119417) (by norm_num)
theorem B1273805 : Blo 846354 1273805 := bbase (se 3 (by rfl) ⟨238838, by rfl⟩ : syracuseStep 1273805 = 477677) (by norm_num)
theorem B1273829 : Blo 846354 1273829 := bbase (se 4 (by rfl) ⟨119421, by rfl⟩ : syracuseStep 1273829 = 238843) (by norm_num)
theorem B2420725 : Blo 846354 2420725 := bbase (se 5 (by rfl) ⟨113471, by rfl⟩ : syracuseStep 2420725 = 226943) (by norm_num)
theorem B1273853 : Blo 846354 1273853 := bbase (se 3 (by rfl) ⟨238847, by rfl⟩ : syracuseStep 1273853 = 477695) (by norm_num)
theorem B1273877 : Blo 846354 1273877 := bbase (se 6 (by rfl) ⟨29856, by rfl⟩ : syracuseStep 1273877 = 59713) (by norm_num)
theorem B2289701 : Blo 846354 2289701 := bbase (se 4 (by rfl) ⟨214659, by rfl⟩ : syracuseStep 2289701 = 429319) (by norm_num)
theorem B2617381 : Blo 846354 2617381 := bbase (se 4 (by rfl) ⟨245379, by rfl⟩ : syracuseStep 2617381 = 490759) (by norm_num)
theorem B1273901 : Blo 846354 1273901 := bbase (se 3 (by rfl) ⟨238856, by rfl⟩ : syracuseStep 1273901 = 477713) (by norm_num)
theorem B1634365 : Blo 846354 1634365 := bbase (se 3 (by rfl) ⟨306443, by rfl⟩ : syracuseStep 1634365 = 612887) (by norm_num)
theorem B1273925 : Blo 846354 1273925 := bbase (se 4 (by rfl) ⟨119430, by rfl⟩ : syracuseStep 1273925 = 238861) (by norm_num)
theorem B1273949 : Blo 846354 1273949 := bbase (se 3 (by rfl) ⟨238865, by rfl⟩ : syracuseStep 1273949 = 477731) (by norm_num)
theorem B1273973 : Blo 846354 1273973 := bbase (se 5 (by rfl) ⟨59717, by rfl⟩ : syracuseStep 1273973 = 119435) (by norm_num)
theorem B1273997 : Blo 846354 1273997 := bbase (se 3 (by rfl) ⟨238874, by rfl⟩ : syracuseStep 1273997 = 477749) (by norm_num)
theorem B1208477 : Blo 846354 1208477 := bbase (se 3 (by rfl) ⟨226589, by rfl⟩ : syracuseStep 1208477 = 453179) (by norm_num)
theorem B1274021 : Blo 846354 1274021 := bbase (se 4 (by rfl) ⟨119439, by rfl⟩ : syracuseStep 1274021 = 238879) (by norm_num)
theorem B1274045 : Blo 846354 1274045 := bbase (se 3 (by rfl) ⟨238883, by rfl⟩ : syracuseStep 1274045 = 477767) (by norm_num)
theorem B1274069 : Blo 846354 1274069 := bbase (se 7 (by rfl) ⟨14930, by rfl⟩ : syracuseStep 1274069 = 29861) (by norm_num)
theorem B1208557 : Blo 846354 1208557 := bbase (se 3 (by rfl) ⟨226604, by rfl⟩ : syracuseStep 1208557 = 453209) (by norm_num)
theorem B1274093 : Blo 846354 1274093 := bbase (se 3 (by rfl) ⟨238892, by rfl⟩ : syracuseStep 1274093 = 477785) (by norm_num)
theorem B1274117 : Blo 846354 1274117 := bbase (se 4 (by rfl) ⟨119448, by rfl⟩ : syracuseStep 1274117 = 238897) (by norm_num)
theorem B1274141 : Blo 846354 1274141 := bbase (se 3 (by rfl) ⟨238901, by rfl⟩ : syracuseStep 1274141 = 477803) (by norm_num)
theorem B1274165 : Blo 846354 1274165 := bbase (se 5 (by rfl) ⟨59726, by rfl⟩ : syracuseStep 1274165 = 119453) (by norm_num)
theorem B1274189 : Blo 846354 1274189 := bbase (se 3 (by rfl) ⟨238910, by rfl⟩ : syracuseStep 1274189 = 477821) (by norm_num)
theorem B10875221 : Blo 846354 10875221 := bbase (se 10 (by rfl) ⟨15930, by rfl⟩ : syracuseStep 10875221 = 31861) (by norm_num)
theorem B1208677 : Blo 846354 1208677 := bbase (se 4 (by rfl) ⟨113313, by rfl⟩ : syracuseStep 1208677 = 226627) (by norm_num)
theorem B1274213 : Blo 846354 1274213 := bbase (se 4 (by rfl) ⟨119457, by rfl⟩ : syracuseStep 1274213 = 238915) (by norm_num)
theorem B1274237 : Blo 846354 1274237 := bbase (se 3 (by rfl) ⟨238919, by rfl⟩ : syracuseStep 1274237 = 477839) (by norm_num)
theorem B1274261 : Blo 846354 1274261 := bbase (se 6 (by rfl) ⟨29865, by rfl⟩ : syracuseStep 1274261 = 59731) (by norm_num)
theorem B1274285 : Blo 846354 1274285 := bbase (se 3 (by rfl) ⟨238928, by rfl⟩ : syracuseStep 1274285 = 477857) (by norm_num)
theorem B4288949 : Blo 846354 4288949 := bbase (se 5 (by rfl) ⟨201044, by rfl⟩ : syracuseStep 4288949 = 402089) (by norm_num)
theorem B1208773 : Blo 846354 1208773 := bbase (se 4 (by rfl) ⟨113322, by rfl⟩ : syracuseStep 1208773 = 226645) (by norm_num)
theorem B1274309 : Blo 846354 1274309 := bbase (se 4 (by rfl) ⟨119466, by rfl⟩ : syracuseStep 1274309 = 238933) (by norm_num)
theorem B1274333 : Blo 846354 1274333 := bbase (se 3 (by rfl) ⟨238937, by rfl⟩ : syracuseStep 1274333 = 477875) (by norm_num)
theorem B1274357 : Blo 846354 1274357 := bbase (se 5 (by rfl) ⟨59735, by rfl⟩ : syracuseStep 1274357 = 119471) (by norm_num)
theorem B1274381 : Blo 846354 1274381 := bbase (se 3 (by rfl) ⟨238946, by rfl⟩ : syracuseStep 1274381 = 477893) (by norm_num)
theorem B1274405 : Blo 846354 1274405 := bbase (se 4 (by rfl) ⟨119475, by rfl⟩ : syracuseStep 1274405 = 238951) (by norm_num)
theorem B1274429 : Blo 846354 1274429 := bbase (se 3 (by rfl) ⟨238955, by rfl⟩ : syracuseStep 1274429 = 477911) (by norm_num)
theorem B1274453 : Blo 846354 1274453 := bbase (se 8 (by rfl) ⟨7467, by rfl⟩ : syracuseStep 1274453 = 14935) (by norm_num)
theorem B1274477 : Blo 846354 1274477 := bbase (se 3 (by rfl) ⟨238964, by rfl⟩ : syracuseStep 1274477 = 477929) (by norm_num)
theorem B1274501 : Blo 846354 1274501 := bbase (se 4 (by rfl) ⟨119484, by rfl⟩ : syracuseStep 1274501 = 238969) (by norm_num)
theorem B1274525 : Blo 846354 1274525 := bbase (se 3 (by rfl) ⟨238973, by rfl⟩ : syracuseStep 1274525 = 477947) (by norm_num)
theorem B5501621 : Blo 846354 5501621 := bbase (se 5 (by rfl) ⟨257888, by rfl⟩ : syracuseStep 5501621 = 515777) (by norm_num)
theorem B1274549 : Blo 846354 1274549 := bbase (se 5 (by rfl) ⟨59744, by rfl⟩ : syracuseStep 1274549 = 119489) (by norm_num)
theorem B2716357 : Blo 846354 2716357 := bbase (se 4 (by rfl) ⟨254658, by rfl⟩ : syracuseStep 2716357 = 509317) (by norm_num)
theorem B1274573 : Blo 846354 1274573 := bbase (se 3 (by rfl) ⟨238982, by rfl⟩ : syracuseStep 1274573 = 477965) (by norm_num)
theorem B1274597 : Blo 846354 1274597 := bbase (se 4 (by rfl) ⟨119493, by rfl⟩ : syracuseStep 1274597 = 238987) (by norm_num)
theorem B2585317 : Blo 846354 2585317 := bbase (se 4 (by rfl) ⟨242373, by rfl⟩ : syracuseStep 2585317 = 484747) (by norm_num)
theorem B3863285 : Blo 846354 3863285 := bbase (se 5 (by rfl) ⟨181091, by rfl⟩ : syracuseStep 3863285 = 362183) (by norm_num)
theorem B1274621 : Blo 846354 1274621 := bbase (se 3 (by rfl) ⟨238991, by rfl⟩ : syracuseStep 1274621 = 477983) (by norm_num)
theorem B1274645 : Blo 846354 1274645 := bbase (se 6 (by rfl) ⟨29874, by rfl⟩ : syracuseStep 1274645 = 59749) (by norm_num)
theorem B1274669 : Blo 846354 1274669 := bbase (se 3 (by rfl) ⟨239000, by rfl⟩ : syracuseStep 1274669 = 478001) (by norm_num)
theorem B1274693 : Blo 846354 1274693 := bbase (se 4 (by rfl) ⟨119502, by rfl⟩ : syracuseStep 1274693 = 239005) (by norm_num)
theorem B1274717 : Blo 846354 1274717 := bbase (se 3 (by rfl) ⟨239009, by rfl⟩ : syracuseStep 1274717 = 478019) (by norm_num)
theorem B1274741 : Blo 846354 1274741 := bbase (se 5 (by rfl) ⟨59753, by rfl⟩ : syracuseStep 1274741 = 119507) (by norm_num)
theorem B1274765 : Blo 846354 1274765 := bbase (se 3 (by rfl) ⟨239018, by rfl⟩ : syracuseStep 1274765 = 478037) (by norm_num)
theorem B1274789 : Blo 846354 1274789 := bbase (se 4 (by rfl) ⟨119511, by rfl⟩ : syracuseStep 1274789 = 239023) (by norm_num)
theorem B1209269 : Blo 846354 1209269 := bbase (se 5 (by rfl) ⟨56684, by rfl⟩ : syracuseStep 1209269 = 113369) (by norm_num)
theorem B1274813 : Blo 846354 1274813 := bbase (se 3 (by rfl) ⟨239027, by rfl⟩ : syracuseStep 1274813 = 478055) (by norm_num)
theorem B1274837 : Blo 846354 1274837 := bbase (se 7 (by rfl) ⟨14939, by rfl⟩ : syracuseStep 1274837 = 29879) (by norm_num)
theorem B1274861 : Blo 846354 1274861 := bbase (se 3 (by rfl) ⟨239036, by rfl⟩ : syracuseStep 1274861 = 478073) (by norm_num)
theorem B1274885 : Blo 846354 1274885 := bbase (se 4 (by rfl) ⟨119520, by rfl⟩ : syracuseStep 1274885 = 239041) (by norm_num)
theorem B1274909 : Blo 846354 1274909 := bbase (se 3 (by rfl) ⟨239045, by rfl⟩ : syracuseStep 1274909 = 478091) (by norm_num)
theorem B1274933 : Blo 846354 1274933 := bbase (se 5 (by rfl) ⟨59762, by rfl⟩ : syracuseStep 1274933 = 119525) (by norm_num)
theorem B1274957 : Blo 846354 1274957 := bbase (se 3 (by rfl) ⟨239054, by rfl⟩ : syracuseStep 1274957 = 478109) (by norm_num)
theorem B1274981 : Blo 846354 1274981 := bbase (se 4 (by rfl) ⟨119529, by rfl⟩ : syracuseStep 1274981 = 239059) (by norm_num)
theorem B1275005 : Blo 846354 1275005 := bbase (se 3 (by rfl) ⟨239063, by rfl⟩ : syracuseStep 1275005 = 478127) (by norm_num)
theorem B1275029 : Blo 846354 1275029 := bbase (se 6 (by rfl) ⟨29883, by rfl⟩ : syracuseStep 1275029 = 59767) (by norm_num)
theorem B1275053 : Blo 846354 1275053 := bbase (se 3 (by rfl) ⟨239072, by rfl⟩ : syracuseStep 1275053 = 478145) (by norm_num)
theorem B1275077 : Blo 846354 1275077 := bbase (se 4 (by rfl) ⟨119538, by rfl⟩ : syracuseStep 1275077 = 239077) (by norm_num)
theorem B1275101 : Blo 846354 1275101 := bbase (se 3 (by rfl) ⟨239081, by rfl⟩ : syracuseStep 1275101 = 478163) (by norm_num)
theorem B1275125 : Blo 846354 1275125 := bbase (se 5 (by rfl) ⟨59771, by rfl⟩ : syracuseStep 1275125 = 119543) (by norm_num)
theorem B1307909 : Blo 846354 1307909 := bbase (se 4 (by rfl) ⟨122616, by rfl⟩ : syracuseStep 1307909 = 245233) (by norm_num)
theorem B1275149 : Blo 846354 1275149 := bbase (se 3 (by rfl) ⟨239090, by rfl⟩ : syracuseStep 1275149 = 478181) (by norm_num)
theorem B1176869 : Blo 846354 1176869 := bbase (se 4 (by rfl) ⟨110331, by rfl⟩ : syracuseStep 1176869 = 220663) (by norm_num)
theorem B1275173 : Blo 846354 1275173 := bbase (se 4 (by rfl) ⟨119547, by rfl⟩ : syracuseStep 1275173 = 239095) (by norm_num)
theorem B1275197 : Blo 846354 1275197 := bbase (se 3 (by rfl) ⟨239099, by rfl⟩ : syracuseStep 1275197 = 478199) (by norm_num)
theorem B1275221 : Blo 846354 1275221 := bbase (se 13 (by rfl) ⟨233, by rfl⟩ : syracuseStep 1275221 = 467) (by norm_num)
theorem B1275245 : Blo 846354 1275245 := bbase (se 3 (by rfl) ⟨239108, by rfl⟩ : syracuseStep 1275245 = 478217) (by norm_num)
theorem B3437957 : Blo 846354 3437957 := bbase (se 4 (by rfl) ⟨322308, by rfl⟩ : syracuseStep 3437957 = 644617) (by norm_num)
theorem B1275269 : Blo 846354 1275269 := bbase (se 4 (by rfl) ⟨119556, by rfl⟩ : syracuseStep 1275269 = 239113) (by norm_num)
theorem B1275293 : Blo 846354 1275293 := bbase (se 3 (by rfl) ⟨239117, by rfl⟩ : syracuseStep 1275293 = 478235) (by norm_num)
theorem B1275317 : Blo 846354 1275317 := bbase (se 5 (by rfl) ⟨59780, by rfl⟩ : syracuseStep 1275317 = 119561) (by norm_num)
theorem B1275341 : Blo 846354 1275341 := bbase (se 3 (by rfl) ⟨239126, by rfl⟩ : syracuseStep 1275341 = 478253) (by norm_num)
theorem B1209821 : Blo 846354 1209821 := bbase (se 3 (by rfl) ⟨226841, by rfl⟩ : syracuseStep 1209821 = 453683) (by norm_num)
theorem B1275365 : Blo 846354 1275365 := bbase (se 4 (by rfl) ⟨119565, by rfl⟩ : syracuseStep 1275365 = 239131) (by norm_num)
theorem B1275389 : Blo 846354 1275389 := bbase (se 3 (by rfl) ⟨239135, by rfl⟩ : syracuseStep 1275389 = 478271) (by norm_num)
theorem B1275413 : Blo 846354 1275413 := bbase (se 6 (by rfl) ⟨29892, by rfl⟩ : syracuseStep 1275413 = 59785) (by norm_num)
theorem B2291237 : Blo 846354 2291237 := bbase (se 4 (by rfl) ⟨214803, by rfl⟩ : syracuseStep 2291237 = 429607) (by norm_num)
theorem B1963565 : Blo 846354 1963565 := bbase (se 3 (by rfl) ⟨368168, by rfl⟩ : syracuseStep 1963565 = 736337) (by norm_num)
theorem B1275437 : Blo 846354 1275437 := bbase (se 3 (by rfl) ⟨239144, by rfl⟩ : syracuseStep 1275437 = 478289) (by norm_num)
theorem B2094653 : Blo 846354 2094653 := bbase (se 3 (by rfl) ⟨392747, by rfl⟩ : syracuseStep 2094653 = 785495) (by norm_num)
theorem B1275461 : Blo 846354 1275461 := bbase (se 4 (by rfl) ⟨119574, by rfl⟩ : syracuseStep 1275461 = 239149) (by norm_num)
theorem B1275485 : Blo 846354 1275485 := bbase (se 3 (by rfl) ⟨239153, by rfl⟩ : syracuseStep 1275485 = 478307) (by norm_num)
theorem B1275509 : Blo 846354 1275509 := bbase (se 5 (by rfl) ⟨59789, by rfl⟩ : syracuseStep 1275509 = 119579) (by norm_num)
theorem B4290245 : Blo 846354 4290245 := bbase (se 4 (by rfl) ⟨402210, by rfl⟩ : syracuseStep 4290245 = 804421) (by norm_num)
theorem B1046405 : Blo 846354 1046405 := bbase (se 4 (by rfl) ⟨98100, by rfl⟩ : syracuseStep 1046405 = 196201) (by norm_num)
theorem B1964213 : Blo 846354 1964213 := bbase (se 5 (by rfl) ⟨92072, by rfl⟩ : syracuseStep 1964213 = 184145) (by norm_num)
theorem B1210573 : Blo 846354 1210573 := bbase (se 3 (by rfl) ⟨226982, by rfl⟩ : syracuseStep 1210573 = 453965) (by norm_num)
theorem B1472813 : Blo 846354 1472813 := bbase (se 3 (by rfl) ⟨276152, by rfl⟩ : syracuseStep 1472813 = 552305) (by norm_num)
theorem B1833293 : Blo 846354 1833293 := bbase (se 3 (by rfl) ⟨343742, by rfl⟩ : syracuseStep 1833293 = 687485) (by norm_num)
theorem B2292533 : Blo 846354 2292533 := bbase (se 5 (by rfl) ⟨107462, by rfl⟩ : syracuseStep 2292533 = 214925) (by norm_num)
theorem B4291541 : Blo 846354 4291541 := bbase (se 7 (by rfl) ⟨50291, by rfl⟩ : syracuseStep 4291541 = 100583) (by norm_num)
theorem B2948069 : Blo 846354 2948069 := bbase (se 4 (by rfl) ⟨276381, by rfl⟩ : syracuseStep 2948069 = 552763) (by norm_num)
theorem B916525 : Blo 846354 916525 := bbase (se 3 (by rfl) ⟨171848, by rfl⟩ : syracuseStep 916525 = 343697) (by norm_num)
theorem B2292965 : Blo 846354 2292965 := bbase (se 4 (by rfl) ⟨214965, by rfl⟩ : syracuseStep 2292965 = 429931) (by norm_num)
theorem B3865877 : Blo 846354 3865877 := bbase (se 6 (by rfl) ⟨90606, by rfl⟩ : syracuseStep 3865877 = 181213) (by norm_num)
theorem B3440485 : Blo 846354 3440485 := bbase (se 4 (by rfl) ⟨322545, by rfl⟩ : syracuseStep 3440485 = 645091) (by norm_num)
theorem B3669877 : Blo 846354 3669877 := bbase (se 5 (by rfl) ⟨172025, by rfl⟩ : syracuseStep 3669877 = 344051) (by norm_num)
theorem B3866737 : Blo 846354 3866737 := bstep (se 2 (by rfl) ⟨1450026, by rfl⟩ : syracuseStep 3866737 = 2900053) B2900053
theorem B6455537 : Blo 846354 6455537 := bstep (se 2 (by rfl) ⟨2420826, by rfl⟩ : syracuseStep 6455537 = 4841653) B4841653
theorem B18317765 : Blo 846354 18317765 := bstep (se 4 (by rfl) ⟨1717290, by rfl⟩ : syracuseStep 18317765 = 3434581) B3434581
theorem B2294435 : Blo 846354 2294435 := bstep (se 1 (by rfl) ⟨1720826, by rfl⟩ : syracuseStep 2294435 = 3441653) B3441653
theorem B1148035 : Blo 846354 1148035 := bstep (se 1 (by rfl) ⟨861026, by rfl⟩ : syracuseStep 1148035 = 1722053) B1722053
theorem B4293809 : Blo 846354 4293809 := bstep (se 2 (by rfl) ⟨1610178, by rfl⟩ : syracuseStep 4293809 = 3220357) B3220357
theorem B5440709 : Blo 846354 5440709 := bstep (se 4 (by rfl) ⟨510066, by rfl⟩ : syracuseStep 5440709 = 1020133) B1020133
theorem B1377569 : Blo 846354 1377569 := bstep (se 2 (by rfl) ⟨516588, by rfl⟩ : syracuseStep 1377569 = 1033177) B1033177
theorem B2721073 : Blo 846354 2721073 := bstep (se 2 (by rfl) ⟨1020402, by rfl⟩ : syracuseStep 2721073 = 2040805) B2040805
theorem B1607377 : Blo 846354 1607377 := bstep (se 2 (by rfl) ⟨602766, by rfl⟩ : syracuseStep 1607377 = 1205533) B1205533
theorem B4589389 : Blo 846354 4589389 := bstep (se 3 (by rfl) ⟨860510, by rfl⟩ : syracuseStep 4589389 = 1721021) B1721021
theorem B952195 : Blo 846354 952195 := bstep (se 1 (by rfl) ⟨714146, by rfl⟩ : syracuseStep 952195 = 1428293) B1428293
theorem B1017731 : Blo 846354 1017731 := bstep (se 1 (by rfl) ⟨763298, by rfl⟩ : syracuseStep 1017731 = 1526597) B1526597
theorem B5801989 : Blo 846354 5801989 := bstep (se 4 (by rfl) ⟨543936, by rfl⟩ : syracuseStep 5801989 = 1087873) B1087873
theorem B952339 : Blo 846354 952339 := bstep (se 1 (by rfl) ⟨714254, by rfl⟩ : syracuseStep 952339 = 1428509) B1428509
theorem B1607779 : Blo 846354 1607779 := bstep (se 1 (by rfl) ⟨1205834, by rfl⟩ : syracuseStep 1607779 = 2411669) B2411669
theorem B1607825 : Blo 846354 1607825 := bstep (se 2 (by rfl) ⟨602934, by rfl⟩ : syracuseStep 1607825 = 1205869) B1205869
theorem B952483 : Blo 846354 952483 := bstep (se 1 (by rfl) ⟨714362, by rfl⟩ : syracuseStep 952483 = 1428725) B1428725
theorem B1018019 : Blo 846354 1018019 := bstep (se 1 (by rfl) ⟨763514, by rfl⟩ : syracuseStep 1018019 = 1527029) B1527029
theorem B3213539 : Blo 846354 3213539 := bstep (se 1 (by rfl) ⟨2410154, by rfl⟩ : syracuseStep 3213539 = 4820309) B4820309
theorem B3213553 : Blo 846354 3213553 := bstep (se 2 (by rfl) ⟨1205082, by rfl⟩ : syracuseStep 3213553 = 2410165) B2410165
theorem B2033905 : Blo 846354 2033905 := bstep (se 2 (by rfl) ⟨762714, by rfl⟩ : syracuseStep 2033905 = 1525429) B1525429
theorem B952627 : Blo 846354 952627 := bstep (se 1 (by rfl) ⟨714470, by rfl⟩ : syracuseStep 952627 = 1428941) B1428941
theorem B2034001 : Blo 846354 2034001 := bstep (se 2 (by rfl) ⟨762750, by rfl⟩ : syracuseStep 2034001 = 1525501) B1525501
theorem B1018211 : Blo 846354 1018211 := bstep (se 1 (by rfl) ⟨763658, by rfl⟩ : syracuseStep 1018211 = 1527317) B1527317
theorem B1608113 : Blo 846354 1608113 := bstep (se 2 (by rfl) ⟨603042, by rfl⟩ : syracuseStep 1608113 = 1206085) B1206085
theorem B2034115 : Blo 846354 2034115 := bstep (se 1 (by rfl) ⟨1525586, by rfl⟩ : syracuseStep 2034115 = 3051173) B3051173
theorem B952771 : Blo 846354 952771 := bstep (se 1 (by rfl) ⟨714578, by rfl⟩ : syracuseStep 952771 = 1429157) B1429157
theorem B2034193 : Blo 846354 2034193 := bstep (se 2 (by rfl) ⟨762822, by rfl⟩ : syracuseStep 2034193 = 1525645) B1525645
theorem B952915 : Blo 846354 952915 := bstep (se 1 (by rfl) ⟨714686, by rfl⟩ : syracuseStep 952915 = 1429373) B1429373
theorem B4295267 : Blo 846354 4295267 := bstep (se 1 (by rfl) ⟨3221450, by rfl⟩ : syracuseStep 4295267 = 6442901) B6442901
theorem B953059 : Blo 846354 953059 := bstep (se 1 (by rfl) ⟨714794, by rfl⟩ : syracuseStep 953059 = 1429589) B1429589
theorem B953203 : Blo 846354 953203 := bstep (se 1 (by rfl) ⟨714902, by rfl⟩ : syracuseStep 953203 = 1429805) B1429805
theorem B953347 : Blo 846354 953347 := bstep (se 1 (by rfl) ⟨715010, by rfl⟩ : syracuseStep 953347 = 1430021) B1430021
theorem B7736419 : Blo 846354 7736419 := bstep (se 1 (by rfl) ⟨5802314, by rfl⟩ : syracuseStep 7736419 = 11604629) B11604629
theorem B5442659 : Blo 846354 5442659 := bstep (se 1 (by rfl) ⟨4081994, by rfl⟩ : syracuseStep 5442659 = 8163989) B8163989
theorem B1608835 : Blo 846354 1608835 := bstep (se 1 (by rfl) ⟨1206626, by rfl⟩ : syracuseStep 1608835 = 2413253) B2413253
theorem B953491 : Blo 846354 953491 := bstep (se 1 (by rfl) ⟨715118, by rfl⟩ : syracuseStep 953491 = 1430237) B1430237
theorem B2723021 : Blo 846354 2723021 := bstep (se 3 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 2723021 = 1021133) B1021133
theorem B953635 : Blo 846354 953635 := bstep (se 1 (by rfl) ⟨715226, by rfl⟩ : syracuseStep 953635 = 1430453) B1430453
theorem B2723149 : Blo 846354 2723149 := bstep (se 3 (by rfl) ⟨510590, by rfl⟩ : syracuseStep 2723149 = 1021181) B1021181
theorem B4296077 : Blo 846354 4296077 := bstep (se 3 (by rfl) ⟨805514, by rfl⟩ : syracuseStep 4296077 = 1611029) B1611029
theorem B953779 : Blo 846354 953779 := bstep (se 1 (by rfl) ⟨715334, by rfl⟩ : syracuseStep 953779 = 1430669) B1430669
theorem B1609283 : Blo 846354 1609283 := bstep (se 1 (by rfl) ⟨1206962, by rfl⟩ : syracuseStep 1609283 = 2413925) B2413925
theorem B953923 : Blo 846354 953923 := bstep (se 1 (by rfl) ⟨715442, by rfl⟩ : syracuseStep 953923 = 1430885) B1430885
theorem B3215011 : Blo 846354 3215011 := bstep (se 1 (by rfl) ⟨2411258, by rfl⟩ : syracuseStep 3215011 = 4822517) B4822517
theorem B954067 : Blo 846354 954067 := bstep (se 1 (by rfl) ⟨715550, by rfl⟩ : syracuseStep 954067 = 1431101) B1431101
theorem B4820741 : Blo 846354 4820741 := bstep (se 4 (by rfl) ⟨451944, by rfl⟩ : syracuseStep 4820741 = 903889) B903889
theorem B1609571 : Blo 846354 1609571 := bstep (se 1 (by rfl) ⟨1207178, by rfl⟩ : syracuseStep 1609571 = 2414357) B2414357
theorem B954211 : Blo 846354 954211 := bstep (se 1 (by rfl) ⟨715658, by rfl⟩ : syracuseStep 954211 = 1431317) B1431317
theorem B1904561 : Blo 846354 1904561 := bstep (se 2 (by rfl) ⟨714210, by rfl⟩ : syracuseStep 1904561 = 1428421) B1428421
theorem B1904579 : Blo 846354 1904579 := bstep (se 1 (by rfl) ⟨1428434, by rfl⟩ : syracuseStep 1904579 = 2856869) B2856869
theorem B954355 : Blo 846354 954355 := bstep (se 1 (by rfl) ⟨715766, by rfl⟩ : syracuseStep 954355 = 1431533) B1431533
theorem B954499 : Blo 846354 954499 := bstep (se 1 (by rfl) ⟨715874, by rfl⟩ : syracuseStep 954499 = 1431749) B1431749
theorem B1904849 : Blo 846354 1904849 := bstep (se 2 (by rfl) ⟨714318, by rfl⟩ : syracuseStep 1904849 = 1428637) B1428637
theorem B1904867 : Blo 846354 1904867 := bstep (se 1 (by rfl) ⟨1428650, by rfl⟩ : syracuseStep 1904867 = 2857301) B2857301
theorem B12226787 : Blo 846354 12226787 := bstep (se 1 (by rfl) ⟨9170090, by rfl⟩ : syracuseStep 12226787 = 18340181) B18340181
theorem B954643 : Blo 846354 954643 := bstep (se 1 (by rfl) ⟨715982, by rfl⟩ : syracuseStep 954643 = 1431965) B1431965
theorem B23892245 : Blo 846354 23892245 := bstep (se 6 (by rfl) ⟨559974, by rfl⟩ : syracuseStep 23892245 = 1119949) B1119949
theorem B954787 : Blo 846354 954787 := bstep (se 1 (by rfl) ⟨716090, by rfl⟩ : syracuseStep 954787 = 1432181) B1432181
theorem B1937827 : Blo 846354 1937827 := bstep (se 1 (by rfl) ⟨1453370, by rfl⟩ : syracuseStep 1937827 = 2906741) B2906741
theorem B4362659 : Blo 846354 4362659 := bstep (se 1 (by rfl) ⟨3271994, by rfl⟩ : syracuseStep 4362659 = 6543989) B6543989
theorem B1905137 : Blo 846354 1905137 := bstep (se 2 (by rfl) ⟨714426, by rfl⟩ : syracuseStep 1905137 = 1428853) B1428853
theorem B1905155 : Blo 846354 1905155 := bstep (se 1 (by rfl) ⟨1428866, by rfl⟩ : syracuseStep 1905155 = 2857733) B2857733
theorem B954931 : Blo 846354 954931 := bstep (se 1 (by rfl) ⟨716198, by rfl⟩ : syracuseStep 954931 = 1432397) B1432397
theorem B955075 : Blo 846354 955075 := bstep (se 1 (by rfl) ⟨716306, by rfl⟩ : syracuseStep 955075 = 1432613) B1432613
theorem B6886129 : Blo 846354 6886129 := bstep (se 2 (by rfl) ⟨2582298, by rfl⟩ : syracuseStep 6886129 = 5164597) B5164597
theorem B1905425 : Blo 846354 1905425 := bstep (se 2 (by rfl) ⟨714534, by rfl⟩ : syracuseStep 1905425 = 1429069) B1429069
theorem B1610513 : Blo 846354 1610513 := bstep (se 2 (by rfl) ⟨603942, by rfl⟩ : syracuseStep 1610513 = 1207885) B1207885
theorem B1020691 : Blo 846354 1020691 := bstep (se 1 (by rfl) ⟨765518, by rfl⟩ : syracuseStep 1020691 = 1531037) B1531037
theorem B1905443 : Blo 846354 1905443 := bstep (se 1 (by rfl) ⟨1429082, by rfl⟩ : syracuseStep 1905443 = 2858165) B2858165
theorem B5149489 : Blo 846354 5149489 := bstep (se 2 (by rfl) ⟨1931058, by rfl⟩ : syracuseStep 5149489 = 3862117) B3862117
theorem B955219 : Blo 846354 955219 := bstep (se 1 (by rfl) ⟨716414, by rfl⟩ : syracuseStep 955219 = 1432829) B1432829
theorem B955363 : Blo 846354 955363 := bstep (se 1 (by rfl) ⟨716522, by rfl⟩ : syracuseStep 955363 = 1433045) B1433045
theorem B2790413 : Blo 846354 2790413 := bstep (se 3 (by rfl) ⟨523202, by rfl⟩ : syracuseStep 2790413 = 1046405) B1046405
theorem B4592675 : Blo 846354 4592675 := bstep (se 1 (by rfl) ⟨3444506, by rfl⟩ : syracuseStep 4592675 = 6889013) B6889013
theorem B1905713 : Blo 846354 1905713 := bstep (se 2 (by rfl) ⟨714642, by rfl⟩ : syracuseStep 1905713 = 1429285) B1429285
theorem B1020979 : Blo 846354 1020979 := bstep (se 1 (by rfl) ⟨765734, by rfl⟩ : syracuseStep 1020979 = 1531469) B1531469
theorem B1905731 : Blo 846354 1905731 := bstep (se 1 (by rfl) ⟨1429298, by rfl⟩ : syracuseStep 1905731 = 2858597) B2858597
theorem B955507 : Blo 846354 955507 := bstep (se 1 (by rfl) ⟨716630, by rfl⟩ : syracuseStep 955507 = 1433261) B1433261
theorem B955651 : Blo 846354 955651 := bstep (se 1 (by rfl) ⟨716738, by rfl⟩ : syracuseStep 955651 = 1433477) B1433477
theorem B1906001 : Blo 846354 1906001 := bstep (se 2 (by rfl) ⟨714750, by rfl⟩ : syracuseStep 1906001 = 1429501) B1429501
theorem B1906019 : Blo 846354 1906019 := bstep (se 1 (by rfl) ⟨1429514, by rfl⟩ : syracuseStep 1906019 = 2859029) B2859029
theorem B955795 : Blo 846354 955795 := bstep (se 1 (by rfl) ⟨716846, by rfl⟩ : syracuseStep 955795 = 1433693) B1433693
theorem B955939 : Blo 846354 955939 := bstep (se 1 (by rfl) ⟨716954, by rfl⟩ : syracuseStep 955939 = 1433909) B1433909
theorem B1906289 : Blo 846354 1906289 := bstep (se 2 (by rfl) ⟨714858, by rfl⟩ : syracuseStep 1906289 = 1429717) B1429717
theorem B1906307 : Blo 846354 1906307 := bstep (se 1 (by rfl) ⟨1429730, by rfl⟩ : syracuseStep 1906307 = 2859461) B2859461
theorem B1611409 : Blo 846354 1611409 := bstep (se 2 (by rfl) ⟨604278, by rfl⟩ : syracuseStep 1611409 = 1208557) B1208557
theorem B956083 : Blo 846354 956083 := bstep (se 1 (by rfl) ⟨717062, by rfl⟩ : syracuseStep 956083 = 1434125) B1434125
theorem B2856653 : Blo 846354 2856653 := bstep (se 3 (by rfl) ⟨535622, by rfl⟩ : syracuseStep 2856653 = 1071245) B1071245
theorem B2856707 : Blo 846354 2856707 := bstep (se 1 (by rfl) ⟨2142530, by rfl⟩ : syracuseStep 2856707 = 4285061) B4285061
theorem B1611569 : Blo 846354 1611569 := bstep (se 2 (by rfl) ⟨604338, by rfl⟩ : syracuseStep 1611569 = 1208677) B1208677
theorem B956227 : Blo 846354 956227 := bstep (se 1 (by rfl) ⟨717170, by rfl⟩ : syracuseStep 956227 = 1434341) B1434341
theorem B3217229 : Blo 846354 3217229 := bstep (se 3 (by rfl) ⟨603230, by rfl⟩ : syracuseStep 3217229 = 1206461) B1206461
theorem B3479395 : Blo 846354 3479395 := bstep (se 1 (by rfl) ⟨2609546, by rfl⟩ : syracuseStep 3479395 = 5219093) B5219093
theorem B1906577 : Blo 846354 1906577 := bstep (se 2 (by rfl) ⟨714966, by rfl⟩ : syracuseStep 1906577 = 1429933) B1429933
theorem B1906595 : Blo 846354 1906595 := bstep (se 1 (by rfl) ⟨1429946, by rfl⟩ : syracuseStep 1906595 = 2859893) B2859893
theorem B956371 : Blo 846354 956371 := bstep (se 1 (by rfl) ⟨717278, by rfl⟩ : syracuseStep 956371 = 1434557) B1434557
theorem B2856977 : Blo 846354 2856977 := bstep (se 2 (by rfl) ⟨1071366, by rfl⟩ : syracuseStep 2856977 = 2142733) B2142733
theorem B956515 : Blo 846354 956515 := bstep (se 1 (by rfl) ⟨717386, by rfl⟩ : syracuseStep 956515 = 1434773) B1434773
theorem B3872881 : Blo 846354 3872881 := bstep (se 2 (by rfl) ⟨1452330, by rfl⟩ : syracuseStep 3872881 = 2904661) B2904661
theorem B2037923 : Blo 846354 2037923 := bstep (se 1 (by rfl) ⟨1528442, by rfl⟩ : syracuseStep 2037923 = 3056885) B3056885
theorem B1906865 : Blo 846354 1906865 := bstep (se 2 (by rfl) ⟨715074, by rfl⟩ : syracuseStep 1906865 = 1430149) B1430149
theorem B1906883 : Blo 846354 1906883 := bstep (se 1 (by rfl) ⟨1430162, by rfl⟩ : syracuseStep 1906883 = 2860325) B2860325
theorem B1611971 : Blo 846354 1611971 := bstep (se 1 (by rfl) ⟨1208978, by rfl⟩ : syracuseStep 1611971 = 2417957) B2417957
theorem B4888781 : Blo 846354 4888781 := bstep (se 3 (by rfl) ⟨916646, by rfl⟩ : syracuseStep 4888781 = 1833293) B1833293
theorem B4298993 : Blo 846354 4298993 := bstep (se 2 (by rfl) ⟨1612122, by rfl⟩ : syracuseStep 4298993 = 3224245) B3224245
theorem B4888867 : Blo 846354 4888867 := bstep (se 1 (by rfl) ⟨3666650, by rfl⟩ : syracuseStep 4888867 = 7333301) B7333301
theorem B3447089 : Blo 846354 3447089 := bstep (se 2 (by rfl) ⟨1292658, by rfl⟩ : syracuseStep 3447089 = 2585317) B2585317
theorem B1907153 : Blo 846354 1907153 := bstep (se 2 (by rfl) ⟨715182, by rfl⟩ : syracuseStep 1907153 = 1430365) B1430365
theorem B1907171 : Blo 846354 1907171 := bstep (se 1 (by rfl) ⟨1430378, by rfl⟩ : syracuseStep 1907171 = 2860757) B2860757
theorem B3054115 : Blo 846354 3054115 := bstep (se 1 (by rfl) ⟨2290586, by rfl⟩ : syracuseStep 3054115 = 4581173) B4581173
theorem B2857517 : Blo 846354 2857517 := bstep (se 3 (by rfl) ⟨535784, by rfl⟩ : syracuseStep 2857517 = 1071569) B1071569
theorem B2857571 : Blo 846354 2857571 := bstep (se 1 (by rfl) ⟨2143178, by rfl⟩ : syracuseStep 2857571 = 4286357) B4286357
theorem B9935459 : Blo 846354 9935459 := bstep (se 1 (by rfl) ⟨7451594, by rfl⟩ : syracuseStep 9935459 = 14903189) B14903189
theorem B1809059 : Blo 846354 1809059 := bstep (se 1 (by rfl) ⟨1356794, by rfl⟩ : syracuseStep 1809059 = 2713589) B2713589
theorem B5446349 : Blo 846354 5446349 := bstep (se 3 (by rfl) ⟨1021190, by rfl⟩ : syracuseStep 5446349 = 2042381) B2042381
theorem B2038499 : Blo 846354 2038499 := bstep (se 1 (by rfl) ⟨1528874, by rfl⟩ : syracuseStep 2038499 = 3057749) B3057749
theorem B1907441 : Blo 846354 1907441 := bstep (se 2 (by rfl) ⟨715290, by rfl⟩ : syracuseStep 1907441 = 1430581) B1430581
theorem B1907459 : Blo 846354 1907459 := bstep (se 1 (by rfl) ⟨1430594, by rfl⟩ : syracuseStep 1907459 = 2861189) B2861189
theorem B2857841 : Blo 846354 2857841 := bstep (se 2 (by rfl) ⟨1071690, by rfl⟩ : syracuseStep 2857841 = 2143381) B2143381
theorem B2038691 : Blo 846354 2038691 := bstep (se 1 (by rfl) ⟨1529018, by rfl⟩ : syracuseStep 2038691 = 3058037) B3058037
theorem B1907729 : Blo 846354 1907729 := bstep (se 2 (by rfl) ⟨715398, by rfl⟩ : syracuseStep 1907729 = 1430797) B1430797
theorem B1907747 : Blo 846354 1907747 := bstep (se 1 (by rfl) ⟨1430810, by rfl⟩ : syracuseStep 1907747 = 2861621) B2861621
theorem B1612867 : Blo 846354 1612867 := bstep (se 1 (by rfl) ⟨1209650, by rfl⟩ : syracuseStep 1612867 = 2419301) B2419301
theorem B2038979 : Blo 846354 2038979 := bstep (se 1 (by rfl) ⟨1529234, by rfl⟩ : syracuseStep 2038979 = 3058469) B3058469
theorem B1613027 : Blo 846354 1613027 := bstep (se 1 (by rfl) ⟨1209770, by rfl⟩ : syracuseStep 1613027 = 2419541) B2419541
theorem B1908017 : Blo 846354 1908017 := bstep (se 2 (by rfl) ⟨715506, by rfl⟩ : syracuseStep 1908017 = 1431013) B1431013
theorem B1908035 : Blo 846354 1908035 := bstep (se 1 (by rfl) ⟨1431026, by rfl⟩ : syracuseStep 1908035 = 2862053) B2862053
theorem B10329443 : Blo 846354 10329443 := bstep (se 1 (by rfl) ⟨7747082, by rfl⟩ : syracuseStep 10329443 = 15494165) B15494165
theorem B7839089 : Blo 846354 7839089 := bstep (se 2 (by rfl) ⟨2939658, by rfl⟩ : syracuseStep 7839089 = 5879317) B5879317
theorem B2858381 : Blo 846354 2858381 := bstep (se 3 (by rfl) ⟨535946, by rfl⟩ : syracuseStep 2858381 = 1071893) B1071893
theorem B2858435 : Blo 846354 2858435 := bstep (se 1 (by rfl) ⟨2143826, by rfl⟩ : syracuseStep 2858435 = 4287653) B4287653
theorem B1908305 : Blo 846354 1908305 := bstep (se 2 (by rfl) ⟨715614, by rfl⟩ : syracuseStep 1908305 = 1431229) B1431229
theorem B1908323 : Blo 846354 1908323 := bstep (se 1 (by rfl) ⟨1431242, by rfl⟩ : syracuseStep 1908323 = 2862485) B2862485
theorem B4300451 : Blo 846354 4300451 := bstep (se 1 (by rfl) ⟨3225338, by rfl⟩ : syracuseStep 4300451 = 6450677) B6450677
theorem B2858705 : Blo 846354 2858705 := bstep (se 2 (by rfl) ⟨1072014, by rfl⟩ : syracuseStep 2858705 = 2144029) B2144029
theorem B1089331 : Blo 846354 1089331 := bstep (se 1 (by rfl) ⟨816998, by rfl⟩ : syracuseStep 1089331 = 1633997) B1633997
theorem B1449841 : Blo 846354 1449841 := bstep (se 2 (by rfl) ⟨543690, by rfl⟩ : syracuseStep 1449841 = 1087381) B1087381
theorem B1908593 : Blo 846354 1908593 := bstep (se 2 (by rfl) ⟨715722, by rfl⟩ : syracuseStep 1908593 = 1431445) B1431445
theorem B1908611 : Blo 846354 1908611 := bstep (se 1 (by rfl) ⟨1431458, by rfl⟩ : syracuseStep 1908611 = 2862917) B2862917
theorem B2039921 : Blo 846354 2039921 := bstep (se 2 (by rfl) ⟨764970, by rfl⟩ : syracuseStep 2039921 = 1529941) B1529941
theorem B1908881 : Blo 846354 1908881 := bstep (se 2 (by rfl) ⟨715830, by rfl⟩ : syracuseStep 1908881 = 1431661) B1431661
theorem B1908899 : Blo 846354 1908899 := bstep (se 1 (by rfl) ⟨1431674, by rfl⟩ : syracuseStep 1908899 = 2863349) B2863349
theorem B7250147 : Blo 846354 7250147 := bstep (se 1 (by rfl) ⟨5437610, by rfl⟩ : syracuseStep 7250147 = 10875221) B10875221
theorem B2859245 : Blo 846354 2859245 := bstep (se 3 (by rfl) ⟨536108, by rfl⟩ : syracuseStep 2859245 = 1072217) B1072217
theorem B1614097 : Blo 846354 1614097 := bstep (se 2 (by rfl) ⟨605286, by rfl⟩ : syracuseStep 1614097 = 1210573) B1210573
theorem B2859299 : Blo 846354 2859299 := bstep (se 1 (by rfl) ⟨2144474, by rfl⟩ : syracuseStep 2859299 = 4288949) B4288949
theorem B2040113 : Blo 846354 2040113 := bstep (se 2 (by rfl) ⟨765042, by rfl⟩ : syracuseStep 2040113 = 1530085) B1530085
theorem B1909169 : Blo 846354 1909169 := bstep (se 2 (by rfl) ⟨715938, by rfl⟩ : syracuseStep 1909169 = 1431877) B1431877
theorem B1909187 : Blo 846354 1909187 := bstep (se 1 (by rfl) ⟨1431890, by rfl⟩ : syracuseStep 1909187 = 2863781) B2863781
theorem B4301261 : Blo 846354 4301261 := bstep (se 3 (by rfl) ⟨806486, by rfl⟩ : syracuseStep 4301261 = 1612973) B1612973
theorem B2859569 : Blo 846354 2859569 := bstep (se 2 (by rfl) ⟨1072338, by rfl⟩ : syracuseStep 2859569 = 2144677) B2144677
theorem B3220145 : Blo 846354 3220145 := bstep (se 2 (by rfl) ⟨1207554, by rfl⟩ : syracuseStep 3220145 = 2415109) B2415109
theorem B1909457 : Blo 846354 1909457 := bstep (se 2 (by rfl) ⟨716046, by rfl⟩ : syracuseStep 1909457 = 1432093) B1432093
theorem B1909475 : Blo 846354 1909475 := bstep (se 1 (by rfl) ⟨1432106, by rfl⟩ : syracuseStep 1909475 = 2864213) B2864213
theorem B1811281 : Blo 846354 1811281 := bstep (se 2 (by rfl) ⟨679230, by rfl⟩ : syracuseStep 1811281 = 1358461) B1358461
theorem B1909745 : Blo 846354 1909745 := bstep (se 2 (by rfl) ⟨716154, by rfl⟩ : syracuseStep 1909745 = 1432309) B1432309
theorem B1909763 : Blo 846354 1909763 := bstep (se 1 (by rfl) ⟨1432322, by rfl⟩ : syracuseStep 1909763 = 2864645) B2864645
theorem B2040881 : Blo 846354 2040881 := bstep (se 2 (by rfl) ⟨765330, by rfl⟩ : syracuseStep 2040881 = 1530661) B1530661
theorem B2860109 : Blo 846354 2860109 := bstep (se 3 (by rfl) ⟨536270, by rfl⟩ : syracuseStep 2860109 = 1072541) B1072541
theorem B2860163 : Blo 846354 2860163 := bstep (se 1 (by rfl) ⟨2145122, by rfl⟩ : syracuseStep 2860163 = 4290245) B4290245
theorem B1910033 : Blo 846354 1910033 := bstep (se 2 (by rfl) ⟨716262, by rfl⟩ : syracuseStep 1910033 = 1432525) B1432525
theorem B1910051 : Blo 846354 1910051 := bstep (se 1 (by rfl) ⟨1432538, by rfl⟩ : syracuseStep 1910051 = 2865077) B2865077
theorem B1222033 : Blo 846354 1222033 := bstep (se 2 (by rfl) ⟨458262, by rfl⟩ : syracuseStep 1222033 = 916525) B916525
theorem B2860433 : Blo 846354 2860433 := bstep (se 2 (by rfl) ⟨1072662, by rfl⟩ : syracuseStep 2860433 = 2145325) B2145325
theorem B11019701 : Blo 846354 11019701 := bstep (se 5 (by rfl) ⟨516548, by rfl⟩ : syracuseStep 11019701 = 1033097) B1033097
theorem B4826573 : Blo 846354 4826573 := bstep (se 3 (by rfl) ⟨904982, by rfl⟩ : syracuseStep 4826573 = 1809965) B1809965
theorem B1910321 : Blo 846354 1910321 := bstep (se 2 (by rfl) ⟨716370, by rfl⟩ : syracuseStep 1910321 = 1432741) B1432741
theorem B1910339 : Blo 846354 1910339 := bstep (se 1 (by rfl) ⟨1432754, by rfl⟩ : syracuseStep 1910339 = 2865509) B2865509
theorem B1910609 : Blo 846354 1910609 := bstep (se 2 (by rfl) ⟨716478, by rfl⟩ : syracuseStep 1910609 = 1432957) B1432957
theorem B1910627 : Blo 846354 1910627 := bstep (se 1 (by rfl) ⟨1432970, by rfl⟩ : syracuseStep 1910627 = 2865941) B2865941
theorem B2860973 : Blo 846354 2860973 := bstep (se 3 (by rfl) ⟨536432, by rfl⟩ : syracuseStep 2860973 = 1072865) B1072865
theorem B2861027 : Blo 846354 2861027 := bstep (se 1 (by rfl) ⟨2145770, by rfl⟩ : syracuseStep 2861027 = 4291541) B4291541
theorem B3221603 : Blo 846354 3221603 := bstep (se 1 (by rfl) ⟨2416202, by rfl⟩ : syracuseStep 3221603 = 4832405) B4832405
theorem B10889315 : Blo 846354 10889315 := bstep (se 1 (by rfl) ⟨8166986, by rfl⟩ : syracuseStep 10889315 = 16333973) B16333973
theorem B1910897 : Blo 846354 1910897 := bstep (se 2 (by rfl) ⟨716586, by rfl⟩ : syracuseStep 1910897 = 1433173) B1433173
theorem B1910915 : Blo 846354 1910915 := bstep (se 1 (by rfl) ⟨1433186, by rfl⟩ : syracuseStep 1910915 = 2866373) B2866373
theorem B2861297 : Blo 846354 2861297 := bstep (se 2 (by rfl) ⟨1072986, by rfl⟩ : syracuseStep 2861297 = 2145973) B2145973
theorem B1911185 : Blo 846354 1911185 := bstep (se 2 (by rfl) ⟨716694, by rfl⟩ : syracuseStep 1911185 = 1433389) B1433389
theorem B1911203 : Blo 846354 1911203 := bstep (se 1 (by rfl) ⟨1433402, by rfl⟩ : syracuseStep 1911203 = 2866805) B2866805
theorem B1452467 : Blo 846354 1452467 := bstep (se 1 (by rfl) ⟨1089350, by rfl⟩ : syracuseStep 1452467 = 2178701) B2178701
theorem B4893169 : Blo 846354 4893169 := bstep (se 2 (by rfl) ⟨1834938, by rfl⟩ : syracuseStep 4893169 = 3669877) B3669877
theorem B1452673 : Blo 846354 1452673 := bstep (se 2 (by rfl) ⟨544752, by rfl⟩ : syracuseStep 1452673 = 1089505) B1089505
theorem B1911473 : Blo 846354 1911473 := bstep (se 2 (by rfl) ⟨716802, by rfl⟩ : syracuseStep 1911473 = 1433605) B1433605
theorem B1911491 : Blo 846354 1911491 := bstep (se 1 (by rfl) ⟨1433618, by rfl⟩ : syracuseStep 1911491 = 2867237) B2867237
theorem B2861837 : Blo 846354 2861837 := bstep (se 3 (by rfl) ⟨536594, by rfl⟩ : syracuseStep 2861837 = 1073189) B1073189
theorem B2861891 : Blo 846354 2861891 := bstep (se 1 (by rfl) ⟨2146418, by rfl⟩ : syracuseStep 2861891 = 4292837) B4292837
theorem B1911761 : Blo 846354 1911761 := bstep (se 2 (by rfl) ⟨716910, by rfl⟩ : syracuseStep 1911761 = 1433821) B1433821
theorem B1911779 : Blo 846354 1911779 := bstep (se 1 (by rfl) ⟨1433834, by rfl⟩ : syracuseStep 1911779 = 2867669) B2867669
theorem B3615779 : Blo 846354 3615779 := bstep (se 1 (by rfl) ⟨2711834, by rfl⟩ : syracuseStep 3615779 = 5423669) B5423669
theorem B3222605 : Blo 846354 3222605 := bstep (se 3 (by rfl) ⟨604238, by rfl⟩ : syracuseStep 3222605 = 1208477) B1208477
theorem B2862161 : Blo 846354 2862161 := bstep (se 2 (by rfl) ⟨1073310, by rfl⟩ : syracuseStep 2862161 = 2146621) B2146621
theorem B5221475 : Blo 846354 5221475 := bstep (se 1 (by rfl) ⟨3916106, by rfl⟩ : syracuseStep 5221475 = 7832213) B7832213
theorem B1912049 : Blo 846354 1912049 := bstep (se 2 (by rfl) ⟨717018, by rfl⟩ : syracuseStep 1912049 = 1434037) B1434037
theorem B1912067 : Blo 846354 1912067 := bstep (se 1 (by rfl) ⟨1434050, by rfl⟩ : syracuseStep 1912067 = 2868101) B2868101
theorem B4304177 : Blo 846354 4304177 := bstep (se 2 (by rfl) ⟨1614066, by rfl⟩ : syracuseStep 4304177 = 3228133) B3228133
theorem B2174435 : Blo 846354 2174435 := bstep (se 1 (by rfl) ⟨1630826, by rfl⟩ : syracuseStep 2174435 = 3261653) B3261653
theorem B1912337 : Blo 846354 1912337 := bstep (se 2 (by rfl) ⟨717126, by rfl⟩ : syracuseStep 1912337 = 1434253) B1434253
theorem B1912355 : Blo 846354 1912355 := bstep (se 1 (by rfl) ⟨1434266, by rfl⟩ : syracuseStep 1912355 = 2868533) B2868533
theorem B2862701 : Blo 846354 2862701 := bstep (se 3 (by rfl) ⟨536756, by rfl⟩ : syracuseStep 2862701 = 1073513) B1073513
theorem B4828805 : Blo 846354 4828805 := bstep (se 4 (by rfl) ⟨452700, by rfl⟩ : syracuseStep 4828805 = 905401) B905401
theorem B1289891 : Blo 846354 1289891 := bstep (se 1 (by rfl) ⟨967418, by rfl⟩ : syracuseStep 1289891 = 1934837) B1934837
theorem B2862755 : Blo 846354 2862755 := bstep (se 1 (by rfl) ⟨2147066, by rfl⟩ : syracuseStep 2862755 = 4294133) B4294133
theorem B3059363 : Blo 846354 3059363 := bstep (se 1 (by rfl) ⟨2294522, by rfl⟩ : syracuseStep 3059363 = 4589045) B4589045
theorem B1224401 : Blo 846354 1224401 := bstep (se 2 (by rfl) ⟨459150, by rfl⟩ : syracuseStep 1224401 = 918301) B918301
theorem B1912625 : Blo 846354 1912625 := bstep (se 2 (by rfl) ⟨717234, by rfl⟩ : syracuseStep 1912625 = 1434469) B1434469
theorem B3878705 : Blo 846354 3878705 := bstep (se 2 (by rfl) ⟨1454514, by rfl⟩ : syracuseStep 3878705 = 2909029) B2909029
theorem B1814339 : Blo 846354 1814339 := bstep (se 1 (by rfl) ⟨1360754, by rfl⟩ : syracuseStep 1814339 = 2721509) B2721509
theorem B1912643 : Blo 846354 1912643 := bstep (se 1 (by rfl) ⟨1434482, by rfl⟩ : syracuseStep 1912643 = 2868965) B2868965
theorem B2895793 : Blo 846354 2895793 := bstep (se 2 (by rfl) ⟨1085922, by rfl⟩ : syracuseStep 2895793 = 2171845) B2171845
theorem B2863025 : Blo 846354 2863025 := bstep (se 2 (by rfl) ⟨1073634, by rfl⟩ : syracuseStep 2863025 = 2147269) B2147269
theorem B1912913 : Blo 846354 1912913 := bstep (se 2 (by rfl) ⟨717342, by rfl⟩ : syracuseStep 1912913 = 1434685) B1434685
theorem B1912931 : Blo 846354 1912931 := bstep (se 1 (by rfl) ⟨1434698, by rfl⟩ : syracuseStep 1912931 = 2869397) B2869397
theorem B2896013 : Blo 846354 2896013 := bstep (se 3 (by rfl) ⟨543002, by rfl⟩ : syracuseStep 2896013 = 1086005) B1086005
theorem B1355923 : Blo 846354 1355923 := bstep (se 1 (by rfl) ⟨1016942, by rfl⟩ : syracuseStep 1355923 = 2033885) B2033885
theorem B4829489 : Blo 846354 4829489 := bstep (se 2 (by rfl) ⟨1811058, by rfl⟩ : syracuseStep 4829489 = 3622117) B3622117
theorem B1913201 : Blo 846354 1913201 := bstep (se 2 (by rfl) ⟨717450, by rfl⟩ : syracuseStep 1913201 = 1434901) B1434901
theorem B1913219 : Blo 846354 1913219 := bstep (se 1 (by rfl) ⟨1434914, by rfl⟩ : syracuseStep 1913219 = 2869829) B2869829
theorem B1356193 : Blo 846354 1356193 := bstep (se 2 (by rfl) ⟨508572, by rfl⟩ : syracuseStep 1356193 = 1017145) B1017145
theorem B2863565 : Blo 846354 2863565 := bstep (se 3 (by rfl) ⟨536918, by rfl⟩ : syracuseStep 2863565 = 1073837) B1073837
theorem B1356257 : Blo 846354 1356257 := bstep (se 2 (by rfl) ⟨508596, by rfl⟩ : syracuseStep 1356257 = 1017193) B1017193
theorem B2863619 : Blo 846354 2863619 := bstep (se 1 (by rfl) ⟨2147714, by rfl⟩ : syracuseStep 2863619 = 4295429) B4295429
theorem B1815203 : Blo 846354 1815203 := bstep (se 1 (by rfl) ⟨1361402, by rfl⟩ : syracuseStep 1815203 = 2722805) B2722805
theorem B2863889 : Blo 846354 2863889 := bstep (se 2 (by rfl) ⟨1073958, by rfl⟩ : syracuseStep 2863889 = 2147917) B2147917
theorem B1815313 : Blo 846354 1815313 := bstep (se 2 (by rfl) ⟨680742, by rfl⟩ : syracuseStep 1815313 = 1361485) B1361485
theorem B2143057 : Blo 846354 2143057 := bstep (se 2 (by rfl) ⟨803646, by rfl⟩ : syracuseStep 2143057 = 1607293) B1607293
theorem B3617777 : Blo 846354 3617777 := bstep (se 2 (by rfl) ⟨1356666, by rfl⟩ : syracuseStep 3617777 = 2713333) B2713333
theorem B2143331 : Blo 846354 2143331 := bstep (se 1 (by rfl) ⟨1607498, by rfl⟩ : syracuseStep 2143331 = 3214997) B3214997
theorem B3224717 : Blo 846354 3224717 := bstep (se 3 (by rfl) ⟨604634, by rfl⟩ : syracuseStep 3224717 = 1209269) B1209269
theorem B2143523 : Blo 846354 2143523 := bstep (se 1 (by rfl) ⟨1607642, by rfl⟩ : syracuseStep 2143523 = 3215285) B3215285
theorem B2864429 : Blo 846354 2864429 := bstep (se 3 (by rfl) ⟨537080, by rfl⟩ : syracuseStep 2864429 = 1074161) B1074161
theorem B2864483 : Blo 846354 2864483 := bstep (se 1 (by rfl) ⟨2148362, by rfl⟩ : syracuseStep 2864483 = 4296725) B4296725
theorem B2864753 : Blo 846354 2864753 := bstep (se 2 (by rfl) ⟨1074282, by rfl⟩ : syracuseStep 2864753 = 2148565) B2148565
theorem B4830947 : Blo 846354 4830947 := bstep (se 1 (by rfl) ⟨3623210, by rfl⟩ : syracuseStep 4830947 = 7246421) B7246421
theorem B16332515 : Blo 846354 16332515 := bstep (se 1 (by rfl) ⟨12249386, by rfl⟩ : syracuseStep 16332515 = 24498773) B24498773
theorem B3618701 : Blo 846354 3618701 := bstep (se 3 (by rfl) ⟨678506, by rfl⟩ : syracuseStep 3618701 = 1357013) B1357013
theorem B3225521 : Blo 846354 3225521 := bstep (se 2 (by rfl) ⟨1209570, by rfl⟩ : syracuseStep 3225521 = 2419141) B2419141
theorem B2865293 : Blo 846354 2865293 := bstep (se 3 (by rfl) ⟨537242, by rfl⟩ : syracuseStep 2865293 = 1074485) B1074485
theorem B1357987 : Blo 846354 1357987 := bstep (se 1 (by rfl) ⟨1018490, by rfl⟩ : syracuseStep 1357987 = 2036981) B2036981
theorem B2865347 : Blo 846354 2865347 := bstep (se 1 (by rfl) ⟨2149010, by rfl⟩ : syracuseStep 2865347 = 4298021) B4298021
theorem B2144465 : Blo 846354 2144465 := bstep (se 2 (by rfl) ⟨804174, by rfl⟩ : syracuseStep 2144465 = 1608349) B1608349
theorem B7747811 : Blo 846354 7747811 := bstep (se 1 (by rfl) ⟨5810858, by rfl⟩ : syracuseStep 7747811 = 11621717) B11621717
theorem B2144515 : Blo 846354 2144515 := bstep (se 1 (by rfl) ⟨1608386, by rfl⟩ : syracuseStep 2144515 = 3216773) B3216773
theorem B2144657 : Blo 846354 2144657 := bstep (se 2 (by rfl) ⟨804246, by rfl⟩ : syracuseStep 2144657 = 1608493) B1608493
theorem B1292707 : Blo 846354 1292707 := bstep (se 1 (by rfl) ⟨969530, by rfl⟩ : syracuseStep 1292707 = 1939061) B1939061
theorem B2865617 : Blo 846354 2865617 := bstep (se 2 (by rfl) ⟨1074606, by rfl⟩ : syracuseStep 2865617 = 2149213) B2149213
theorem B8141381 : Blo 846354 8141381 := bstep (se 4 (by rfl) ⟨763254, by rfl⟩ : syracuseStep 8141381 = 1526509) B1526509
theorem B3226189 : Blo 846354 3226189 := bstep (se 3 (by rfl) ⟨604910, by rfl⟩ : syracuseStep 3226189 = 1209821) B1209821
theorem B1358435 : Blo 846354 1358435 := bstep (se 1 (by rfl) ⟨1018826, by rfl⟩ : syracuseStep 1358435 = 2037653) B2037653
theorem B2898641 : Blo 846354 2898641 := bstep (se 2 (by rfl) ⟨1086990, by rfl⟩ : syracuseStep 2898641 = 2173981) B2173981
theorem B1260353 : Blo 846354 1260353 := bstep (se 2 (by rfl) ⟨472632, by rfl⟩ : syracuseStep 1260353 = 945265) B945265
theorem B965443 : Blo 846354 965443 := bstep (se 1 (by rfl) ⟨724082, by rfl⟩ : syracuseStep 965443 = 1448165) B1448165
theorem B2866157 : Blo 846354 2866157 := bstep (se 3 (by rfl) ⟨537404, by rfl⟩ : syracuseStep 2866157 = 1074809) B1074809
theorem B2866211 : Blo 846354 2866211 := bstep (se 1 (by rfl) ⟨2149658, by rfl⟩ : syracuseStep 2866211 = 4299317) B4299317
theorem B932963 : Blo 846354 932963 := bstep (se 1 (by rfl) ⟨699722, by rfl⟩ : syracuseStep 932963 = 1399445) B1399445
theorem B1358993 : Blo 846354 1358993 := bstep (se 2 (by rfl) ⟨509622, by rfl⟩ : syracuseStep 1358993 = 1019245) B1019245
theorem B2178353 : Blo 846354 2178353 := bstep (se 2 (by rfl) ⟨816882, by rfl⟩ : syracuseStep 2178353 = 1633765) B1633765
theorem B2866481 : Blo 846354 2866481 := bstep (se 2 (by rfl) ⟨1074930, by rfl⟩ : syracuseStep 2866481 = 2149861) B2149861
theorem B3226979 : Blo 846354 3226979 := bstep (se 1 (by rfl) ⟨2420234, by rfl⟩ : syracuseStep 3226979 = 4840469) B4840469
theorem B2145649 : Blo 846354 2145649 := bstep (se 2 (by rfl) ⟨804618, by rfl⟩ : syracuseStep 2145649 = 1609237) B1609237
theorem B1359217 : Blo 846354 1359217 := bstep (se 2 (by rfl) ⟨509706, by rfl⟩ : syracuseStep 1359217 = 1019413) B1019413
theorem B1359281 : Blo 846354 1359281 := bstep (se 2 (by rfl) ⟨509730, by rfl⟩ : syracuseStep 1359281 = 1019461) B1019461
theorem B1359409 : Blo 846354 1359409 := bstep (se 2 (by rfl) ⟨509778, by rfl⟩ : syracuseStep 1359409 = 1019557) B1019557
theorem B13778545 : Blo 846354 13778545 := bstep (se 2 (by rfl) ⟨5166954, by rfl⟩ : syracuseStep 13778545 = 10333909) B10333909
theorem B2145923 : Blo 846354 2145923 := bstep (se 1 (by rfl) ⟨1609442, by rfl⟩ : syracuseStep 2145923 = 3218885) B3218885
theorem B2146115 : Blo 846354 2146115 := bstep (se 1 (by rfl) ⟨1609586, by rfl⟩ : syracuseStep 2146115 = 3219173) B3219173
theorem B2867021 : Blo 846354 2867021 := bstep (se 3 (by rfl) ⟨537566, by rfl⟩ : syracuseStep 2867021 = 1075133) B1075133
theorem B3063629 : Blo 846354 3063629 := bstep (se 3 (by rfl) ⟨574430, by rfl⟩ : syracuseStep 3063629 = 1148861) B1148861
theorem B2867075 : Blo 846354 2867075 := bstep (se 1 (by rfl) ⟨2150306, by rfl⟩ : syracuseStep 2867075 = 4300613) B4300613
theorem B3915661 : Blo 846354 3915661 := bstep (se 3 (by rfl) ⟨734186, by rfl⟩ : syracuseStep 3915661 = 1468373) B1468373
theorem B15482765 : Blo 846354 15482765 := bstep (se 3 (by rfl) ⟨2903018, by rfl⟩ : syracuseStep 15482765 = 5806037) B5806037
theorem B3227633 : Blo 846354 3227633 := bstep (se 2 (by rfl) ⟨1210362, by rfl⟩ : syracuseStep 3227633 = 2420725) B2420725
theorem B3489841 : Blo 846354 3489841 := bstep (se 2 (by rfl) ⟨1308690, by rfl⟩ : syracuseStep 3489841 = 2617381) B2617381
theorem B2179153 : Blo 846354 2179153 := bstep (se 2 (by rfl) ⟨817182, by rfl⟩ : syracuseStep 2179153 = 1634365) B1634365
theorem B2867345 : Blo 846354 2867345 := bstep (se 2 (by rfl) ⟨1075254, by rfl⟩ : syracuseStep 2867345 = 2150509) B2150509
theorem B9650501 : Blo 846354 9650501 := bstep (se 4 (by rfl) ⟨904734, by rfl⟩ : syracuseStep 9650501 = 1809469) B1809469
theorem B2867885 : Blo 846354 2867885 := bstep (se 3 (by rfl) ⟨537728, by rfl⟩ : syracuseStep 2867885 = 1075457) B1075457
theorem B2867939 : Blo 846354 2867939 := bstep (se 1 (by rfl) ⟨2150954, by rfl⟩ : syracuseStep 2867939 = 4301909) B4301909
theorem B2147057 : Blo 846354 2147057 := bstep (se 2 (by rfl) ⟨805146, by rfl⟩ : syracuseStep 2147057 = 1610293) B1610293
theorem B2147107 : Blo 846354 2147107 := bstep (se 1 (by rfl) ⟨1610330, by rfl⟩ : syracuseStep 2147107 = 3220661) B3220661
theorem B4080419 : Blo 846354 4080419 := bstep (se 1 (by rfl) ⟨3060314, by rfl⟩ : syracuseStep 4080419 = 6120629) B6120629
theorem B4834181 : Blo 846354 4834181 := bstep (se 4 (by rfl) ⟨453204, by rfl⟩ : syracuseStep 4834181 = 906409) B906409
theorem B3621809 : Blo 846354 3621809 := bstep (se 2 (by rfl) ⟨1358178, by rfl⟩ : syracuseStep 3621809 = 2716357) B2716357
theorem B2147249 : Blo 846354 2147249 := bstep (se 2 (by rfl) ⟨805218, by rfl⟩ : syracuseStep 2147249 = 1610437) B1610437
theorem B1164241 : Blo 846354 1164241 := bstep (se 2 (by rfl) ⟨436590, by rfl⟩ : syracuseStep 1164241 = 873181) B873181
theorem B2868209 : Blo 846354 2868209 := bstep (se 2 (by rfl) ⟨1075578, by rfl⟩ : syracuseStep 2868209 = 2151157) B2151157
theorem B9159749 : Blo 846354 9159749 := bstep (se 4 (by rfl) ⟨858726, by rfl⟩ : syracuseStep 9159749 = 1717453) B1717453
theorem B5424205 : Blo 846354 5424205 := bstep (se 3 (by rfl) ⟨1017038, by rfl⟩ : syracuseStep 5424205 = 2034077) B2034077
theorem B4899953 : Blo 846354 4899953 := bstep (se 2 (by rfl) ⟨1837482, by rfl⟩ : syracuseStep 4899953 = 3674965) B3674965
theorem B2901187 : Blo 846354 2901187 := bstep (se 1 (by rfl) ⟨2175890, by rfl⟩ : syracuseStep 2901187 = 4351781) B4351781
theorem B4080881 : Blo 846354 4080881 := bstep (se 2 (by rfl) ⟨1530330, by rfl⟩ : syracuseStep 4080881 = 3060661) B3060661
theorem B4834637 : Blo 846354 4834637 := bstep (se 3 (by rfl) ⟨906494, by rfl⟩ : syracuseStep 4834637 = 1812989) B1812989
theorem B2868749 : Blo 846354 2868749 := bstep (se 3 (by rfl) ⟨537890, by rfl⟩ : syracuseStep 2868749 = 1075781) B1075781
theorem B1361459 : Blo 846354 1361459 := bstep (se 1 (by rfl) ⟨1021094, by rfl⟩ : syracuseStep 1361459 = 2042189) B2042189
theorem B2868803 : Blo 846354 2868803 := bstep (se 1 (by rfl) ⟨2151602, by rfl⟩ : syracuseStep 2868803 = 4303205) B4303205
theorem B2410211 : Blo 846354 2410211 := bstep (se 1 (by rfl) ⟨1807658, by rfl⟩ : syracuseStep 2410211 = 3615317) B3615317
theorem B870211 : Blo 846354 870211 := bstep (se 1 (by rfl) ⟨652658, by rfl⟩ : syracuseStep 870211 = 1305317) B1305317
theorem B2869073 : Blo 846354 2869073 := bstep (se 2 (by rfl) ⟨1075902, by rfl⟩ : syracuseStep 2869073 = 2151805) B2151805
theorem B2148241 : Blo 846354 2148241 := bstep (se 2 (by rfl) ⟨805590, by rfl⟩ : syracuseStep 2148241 = 1611181) B1611181
theorem B1525891 : Blo 846354 1525891 := bstep (se 1 (by rfl) ⟨1144418, by rfl⟩ : syracuseStep 1525891 = 2288837) B2288837
theorem B3623075 : Blo 846354 3623075 := bstep (se 1 (by rfl) ⟨2717306, by rfl⟩ : syracuseStep 3623075 = 5434613) B5434613
theorem B2148515 : Blo 846354 2148515 := bstep (se 1 (by rfl) ⟨1611386, by rfl⟩ : syracuseStep 2148515 = 3222773) B3222773
theorem B2148707 : Blo 846354 2148707 := bstep (se 1 (by rfl) ⟨1611530, by rfl⟩ : syracuseStep 2148707 = 3223061) B3223061
theorem B2869613 : Blo 846354 2869613 := bstep (se 3 (by rfl) ⟨538052, by rfl⟩ : syracuseStep 2869613 = 1076105) B1076105
theorem B2869667 : Blo 846354 2869667 := bstep (se 1 (by rfl) ⟨2152250, by rfl⟩ : syracuseStep 2869667 = 4304501) B4304501
theorem B6441443 : Blo 846354 6441443 := bstep (se 1 (by rfl) ⟨4831082, by rfl⟩ : syracuseStep 6441443 = 9662165) B9662165
theorem B2869937 : Blo 846354 2869937 := bstep (se 2 (by rfl) ⟨1076226, by rfl⟩ : syracuseStep 2869937 = 2152453) B2152453
theorem B1526467 : Blo 846354 1526467 := bstep (se 1 (by rfl) ⟨1144850, by rfl⟩ : syracuseStep 1526467 = 2289701) B2289701
theorem B1428259 : Blo 846354 1428259 := bstep (se 1 (by rfl) ⟨1071194, by rfl⟩ : syracuseStep 1428259 = 2142389) B2142389
theorem B969571 : Blo 846354 969571 := bstep (se 1 (by rfl) ⟨727178, by rfl⟩ : syracuseStep 969571 = 1454357) B1454357
theorem B1428401 : Blo 846354 1428401 := bstep (se 2 (by rfl) ⟨535650, by rfl⟩ : syracuseStep 1428401 = 1071301) B1071301
theorem B2411441 : Blo 846354 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B1428529 : Blo 846354 1428529 := bstep (se 2 (by rfl) ⟨535698, by rfl⟩ : syracuseStep 1428529 = 1071397) B1071397
theorem B1428563 : Blo 846354 1428563 := bstep (se 1 (by rfl) ⟨1071422, by rfl⟩ : syracuseStep 1428563 = 2142845) B2142845
theorem B2575523 : Blo 846354 2575523 := bstep (se 1 (by rfl) ⟨1931642, by rfl⟩ : syracuseStep 2575523 = 3863285) B3863285
theorem B1428691 : Blo 846354 1428691 := bstep (se 1 (by rfl) ⟨1071518, by rfl⟩ : syracuseStep 1428691 = 2143037) B2143037
theorem B2149649 : Blo 846354 2149649 := bstep (se 2 (by rfl) ⟨806118, by rfl⟩ : syracuseStep 2149649 = 1612237) B1612237
theorem B2149699 : Blo 846354 2149699 := bstep (se 1 (by rfl) ⟨1612274, by rfl⟩ : syracuseStep 2149699 = 3224549) B3224549
theorem B1428833 : Blo 846354 1428833 := bstep (se 2 (by rfl) ⟨535812, by rfl⟩ : syracuseStep 1428833 = 1071625) B1071625
theorem B904547 : Blo 846354 904547 := bstep (se 1 (by rfl) ⟨678410, by rfl⟩ : syracuseStep 904547 = 1356821) B1356821
theorem B9293237 : Blo 846354 9293237 := bstep (se 5 (by rfl) ⟨435620, by rfl⟩ : syracuseStep 9293237 = 871241) B871241
theorem B2149841 : Blo 846354 2149841 := bstep (se 2 (by rfl) ⟨806190, by rfl⟩ : syracuseStep 2149841 = 1612381) B1612381
theorem B1428961 : Blo 846354 1428961 := bstep (se 2 (by rfl) ⟨535860, by rfl⟩ : syracuseStep 1428961 = 1071721) B1071721
theorem B1428995 : Blo 846354 1428995 := bstep (se 1 (by rfl) ⟨1071746, by rfl⟩ : syracuseStep 1428995 = 2143493) B2143493
theorem B871939 : Blo 846354 871939 := bstep (se 1 (by rfl) ⟨653954, by rfl⟩ : syracuseStep 871939 = 1307909) B1307909
theorem B1429123 : Blo 846354 1429123 := bstep (se 1 (by rfl) ⟨1071842, by rfl⟩ : syracuseStep 1429123 = 2143685) B2143685
theorem B1527491 : Blo 846354 1527491 := bstep (se 1 (by rfl) ⟨1145618, by rfl⟩ : syracuseStep 1527491 = 2291237) B2291237
theorem B1396435 : Blo 846354 1396435 := bstep (se 1 (by rfl) ⟨1047326, by rfl⟩ : syracuseStep 1396435 = 2094653) B2094653
theorem B1429265 : Blo 846354 1429265 := bstep (se 2 (by rfl) ⟨535974, by rfl⟩ : syracuseStep 1429265 = 1071949) B1071949
theorem B2477873 : Blo 846354 2477873 := bstep (se 2 (by rfl) ⟨929202, by rfl⟩ : syracuseStep 2477873 = 1858405) B1858405
theorem B4083533 : Blo 846354 4083533 := bstep (se 3 (by rfl) ⟨765662, by rfl⟩ : syracuseStep 4083533 = 1531325) B1531325
theorem B1429393 : Blo 846354 1429393 := bstep (se 2 (by rfl) ⟨536022, by rfl⟩ : syracuseStep 1429393 = 1072045) B1072045
theorem B1429427 : Blo 846354 1429427 := bstep (se 1 (by rfl) ⟨1072070, by rfl⟩ : syracuseStep 1429427 = 2144141) B2144141
theorem B2904113 : Blo 846354 2904113 := bstep (se 2 (by rfl) ⟨1089042, by rfl⟩ : syracuseStep 2904113 = 2178085) B2178085
theorem B1429555 : Blo 846354 1429555 := bstep (se 1 (by rfl) ⟨1072166, by rfl⟩ : syracuseStep 1429555 = 2144333) B2144333
theorem B4837553 : Blo 846354 4837553 := bstep (se 2 (by rfl) ⟨1814082, by rfl⟩ : syracuseStep 4837553 = 3628165) B3628165
theorem B1429697 : Blo 846354 1429697 := bstep (se 2 (by rfl) ⟨536136, by rfl⟩ : syracuseStep 1429697 = 1072273) B1072273
theorem B1429825 : Blo 846354 1429825 := bstep (se 2 (by rfl) ⟨536184, by rfl⟩ : syracuseStep 1429825 = 1072369) B1072369
theorem B1429859 : Blo 846354 1429859 := bstep (se 1 (by rfl) ⟨1072394, by rfl⟩ : syracuseStep 1429859 = 2144789) B2144789
theorem B2412899 : Blo 846354 2412899 := bstep (se 1 (by rfl) ⟨1809674, by rfl⟩ : syracuseStep 2412899 = 3619349) B3619349
theorem B2150833 : Blo 846354 2150833 := bstep (se 2 (by rfl) ⟨806562, by rfl⟩ : syracuseStep 2150833 = 1613125) B1613125
theorem B1429987 : Blo 846354 1429987 := bstep (se 1 (by rfl) ⟨1072490, by rfl⟩ : syracuseStep 1429987 = 2144981) B2144981
theorem B1528355 : Blo 846354 1528355 := bstep (se 1 (by rfl) ⟨1146266, by rfl⟩ : syracuseStep 1528355 = 2292533) B2292533
theorem B1430129 : Blo 846354 1430129 := bstep (se 2 (by rfl) ⟨536298, by rfl⟩ : syracuseStep 1430129 = 1072597) B1072597
theorem B2151107 : Blo 846354 2151107 := bstep (se 1 (by rfl) ⟨1613330, by rfl⟩ : syracuseStep 2151107 = 3226661) B3226661
theorem B1430257 : Blo 846354 1430257 := bstep (se 2 (by rfl) ⟨536346, by rfl⟩ : syracuseStep 1430257 = 1072693) B1072693
theorem B1430291 : Blo 846354 1430291 := bstep (se 1 (by rfl) ⟨1072718, by rfl⟩ : syracuseStep 1430291 = 2145437) B2145437
theorem B1528643 : Blo 846354 1528643 := bstep (se 1 (by rfl) ⟨1146482, by rfl⟩ : syracuseStep 1528643 = 2292965) B2292965
theorem B2577251 : Blo 846354 2577251 := bstep (se 1 (by rfl) ⟨1932938, by rfl⟩ : syracuseStep 2577251 = 3865877) B3865877
theorem B2151299 : Blo 846354 2151299 := bstep (se 1 (by rfl) ⟨1613474, by rfl⟩ : syracuseStep 2151299 = 3226949) B3226949
theorem B1430419 : Blo 846354 1430419 := bstep (se 1 (by rfl) ⟨1072814, by rfl⟩ : syracuseStep 1430419 = 2145629) B2145629
theorem B1430561 : Blo 846354 1430561 := bstep (se 2 (by rfl) ⟨536460, by rfl⟩ : syracuseStep 1430561 = 1072921) B1072921
theorem B5231729 : Blo 846354 5231729 := bstep (se 2 (by rfl) ⟨1961898, by rfl⟩ : syracuseStep 5231729 = 3923797) B3923797
theorem B2413709 : Blo 846354 2413709 := bstep (se 3 (by rfl) ⟨452570, by rfl⟩ : syracuseStep 2413709 = 905141) B905141
theorem B1430689 : Blo 846354 1430689 := bstep (se 2 (by rfl) ⟨536508, by rfl⟩ : syracuseStep 1430689 = 1073017) B1073017
theorem B1430723 : Blo 846354 1430723 := bstep (se 1 (by rfl) ⟨1073042, by rfl⟩ : syracuseStep 1430723 = 2146085) B2146085
theorem B4347121 : Blo 846354 4347121 := bstep (se 2 (by rfl) ⟨1630170, by rfl⟩ : syracuseStep 4347121 = 3260341) B3260341
theorem B1430851 : Blo 846354 1430851 := bstep (se 1 (by rfl) ⟨1073138, by rfl⟩ : syracuseStep 1430851 = 2146277) B2146277
theorem B906563 : Blo 846354 906563 := bstep (se 1 (by rfl) ⟨679922, by rfl⟩ : syracuseStep 906563 = 1359845) B1359845
theorem B2413901 : Blo 846354 2413901 := bstep (se 3 (by rfl) ⟨452606, by rfl⟩ : syracuseStep 2413901 = 905213) B905213
theorem B5428613 : Blo 846354 5428613 := bstep (se 4 (by rfl) ⟨508932, by rfl⟩ : syracuseStep 5428613 = 1017865) B1017865
theorem B2446733 : Blo 846354 2446733 := bstep (se 3 (by rfl) ⟨458762, by rfl⟩ : syracuseStep 2446733 = 917525) B917525
theorem B1430993 : Blo 846354 1430993 := bstep (se 2 (by rfl) ⟨536622, by rfl⟩ : syracuseStep 1430993 = 1073245) B1073245
theorem B1431121 : Blo 846354 1431121 := bstep (se 2 (by rfl) ⟨536670, by rfl⟩ : syracuseStep 1431121 = 1073341) B1073341
theorem B4839011 : Blo 846354 4839011 := bstep (se 1 (by rfl) ⟨3629258, by rfl⟩ : syracuseStep 4839011 = 7258517) B7258517
theorem B1431155 : Blo 846354 1431155 := bstep (se 1 (by rfl) ⟨1073366, by rfl⟩ : syracuseStep 1431155 = 2146733) B2146733
theorem B4085453 : Blo 846354 4085453 := bstep (se 3 (by rfl) ⟨766022, by rfl⟩ : syracuseStep 4085453 = 1532045) B1532045
theorem B1431283 : Blo 846354 1431283 := bstep (se 1 (by rfl) ⟨1073462, by rfl⟩ : syracuseStep 1431283 = 2146925) B2146925
theorem B2447117 : Blo 846354 2447117 := bstep (se 3 (by rfl) ⟨458834, by rfl⟩ : syracuseStep 2447117 = 917669) B917669
theorem B3626765 : Blo 846354 3626765 := bstep (se 3 (by rfl) ⟨680018, by rfl⟩ : syracuseStep 3626765 = 1360037) B1360037
theorem B2152241 : Blo 846354 2152241 := bstep (se 2 (by rfl) ⟨807090, by rfl⟩ : syracuseStep 2152241 = 1614181) B1614181
theorem B11032373 : Blo 846354 11032373 := bstep (se 5 (by rfl) ⟨517142, by rfl⟩ : syracuseStep 11032373 = 1034285) B1034285
theorem B2152291 : Blo 846354 2152291 := bstep (se 1 (by rfl) ⟨1614218, by rfl⟩ : syracuseStep 2152291 = 3228437) B3228437
theorem B1431425 : Blo 846354 1431425 := bstep (se 2 (by rfl) ⟨536784, by rfl⟩ : syracuseStep 1431425 = 1073569) B1073569
theorem B2152433 : Blo 846354 2152433 := bstep (se 2 (by rfl) ⟨807162, by rfl⟩ : syracuseStep 2152433 = 1614325) B1614325
theorem B1431553 : Blo 846354 1431553 := bstep (se 2 (by rfl) ⟨536832, by rfl⟩ : syracuseStep 1431553 = 1073665) B1073665
theorem B9656333 : Blo 846354 9656333 := bstep (se 3 (by rfl) ⟨1810562, by rfl⟩ : syracuseStep 9656333 = 3621125) B3621125
theorem B1431587 : Blo 846354 1431587 := bstep (se 1 (by rfl) ⟨1073690, by rfl⟩ : syracuseStep 1431587 = 2147381) B2147381
theorem B1529969 : Blo 846354 1529969 := bstep (se 2 (by rfl) ⟨573738, by rfl⟩ : syracuseStep 1529969 = 1147477) B1147477
theorem B1071235 : Blo 846354 1071235 := bstep (se 1 (by rfl) ⟨803426, by rfl⟩ : syracuseStep 1071235 = 1606853) B1606853
theorem B1431715 : Blo 846354 1431715 := bstep (se 1 (by rfl) ⟨1073786, by rfl⟩ : syracuseStep 1431715 = 2147573) B2147573
theorem B2414893 : Blo 846354 2414893 := bstep (se 3 (by rfl) ⟨452792, by rfl⟩ : syracuseStep 2414893 = 905585) B905585
theorem B1431857 : Blo 846354 1431857 := bstep (se 2 (by rfl) ⟨536946, by rfl⟩ : syracuseStep 1431857 = 1073893) B1073893
theorem B907571 : Blo 846354 907571 := bstep (se 1 (by rfl) ⟨680678, by rfl⟩ : syracuseStep 907571 = 1361357) B1361357
theorem B1431985 : Blo 846354 1431985 := bstep (se 2 (by rfl) ⟨536994, by rfl⟩ : syracuseStep 1431985 = 1073989) B1073989
theorem B1432019 : Blo 846354 1432019 := bstep (se 1 (by rfl) ⟨1074014, by rfl⟩ : syracuseStep 1432019 = 2148029) B2148029
theorem B6117859 : Blo 846354 6117859 := bstep (se 1 (by rfl) ⟨4588394, by rfl⟩ : syracuseStep 6117859 = 9176789) B9176789
theorem B4840013 : Blo 846354 4840013 := bstep (se 3 (by rfl) ⟨907502, by rfl⟩ : syracuseStep 4840013 = 1815005) B1815005
theorem B1432147 : Blo 846354 1432147 := bstep (se 1 (by rfl) ⟨1074110, by rfl⟩ : syracuseStep 1432147 = 2148221) B2148221
theorem B1071731 : Blo 846354 1071731 := bstep (se 1 (by rfl) ⟨803798, by rfl⟩ : syracuseStep 1071731 = 1607597) B1607597
theorem B1432289 : Blo 846354 1432289 := bstep (se 2 (by rfl) ⟨537108, by rfl⟩ : syracuseStep 1432289 = 1074217) B1074217
theorem B1432417 : Blo 846354 1432417 := bstep (se 2 (by rfl) ⟨537156, by rfl⟩ : syracuseStep 1432417 = 1074313) B1074313
theorem B1432451 : Blo 846354 1432451 := bstep (se 1 (by rfl) ⟨1074338, by rfl⟩ : syracuseStep 1432451 = 2148677) B2148677
theorem B1432579 : Blo 846354 1432579 := bstep (se 1 (by rfl) ⟨1074434, by rfl⟩ : syracuseStep 1432579 = 2148869) B2148869
theorem B8707085 : Blo 846354 8707085 := bstep (se 3 (by rfl) ⟨1632578, by rfl⟩ : syracuseStep 8707085 = 3265157) B3265157
theorem B14670989 : Blo 846354 14670989 := bstep (se 3 (by rfl) ⟨2750810, by rfl⟩ : syracuseStep 14670989 = 5501621) B5501621
theorem B1432721 : Blo 846354 1432721 := bstep (se 2 (by rfl) ⟨537270, by rfl⟩ : syracuseStep 1432721 = 1074541) B1074541
theorem B2579683 : Blo 846354 2579683 := bstep (se 1 (by rfl) ⟨1934762, by rfl⟩ : syracuseStep 2579683 = 3869525) B3869525
theorem B1432849 : Blo 846354 1432849 := bstep (se 2 (by rfl) ⟨537318, by rfl⟩ : syracuseStep 1432849 = 1074637) B1074637
theorem B5430563 : Blo 846354 5430563 := bstep (se 1 (by rfl) ⟨4072922, by rfl⟩ : syracuseStep 5430563 = 8145845) B8145845
theorem B1072435 : Blo 846354 1072435 := bstep (se 1 (by rfl) ⟨804326, by rfl⟩ : syracuseStep 1072435 = 1608653) B1608653
theorem B1432883 : Blo 846354 1432883 := bstep (se 1 (by rfl) ⟨1074662, by rfl⟩ : syracuseStep 1432883 = 2149325) B2149325
theorem B1072531 : Blo 846354 1072531 := bstep (se 1 (by rfl) ⟨804398, by rfl⟩ : syracuseStep 1072531 = 1608797) B1608797
theorem B1433011 : Blo 846354 1433011 := bstep (se 1 (by rfl) ⟨1074758, by rfl⟩ : syracuseStep 1433011 = 2149517) B2149517
theorem B1433153 : Blo 846354 1433153 := bstep (se 2 (by rfl) ⟨537432, by rfl⟩ : syracuseStep 1433153 = 1074865) B1074865
theorem B1433281 : Blo 846354 1433281 := bstep (se 2 (by rfl) ⟨537480, by rfl⟩ : syracuseStep 1433281 = 1074961) B1074961
theorem B6446789 : Blo 846354 6446789 := bstep (se 4 (by rfl) ⟨604386, by rfl⟩ : syracuseStep 6446789 = 1208773) B1208773
theorem B1433315 : Blo 846354 1433315 := bstep (se 1 (by rfl) ⟨1074986, by rfl⟩ : syracuseStep 1433315 = 2149973) B2149973
theorem B1269539 : Blo 846354 1269539 := bstep (se 1 (by rfl) ⟨952154, by rfl⟩ : syracuseStep 1269539 = 1904309) B1904309
theorem B1269569 : Blo 846354 1269569 := bstep (se 2 (by rfl) ⟨476088, by rfl⟩ : syracuseStep 1269569 = 952177) B952177
theorem B1269587 : Blo 846354 1269587 := bstep (se 1 (by rfl) ⟨952190, by rfl⟩ : syracuseStep 1269587 = 1904381) B1904381
theorem B1433443 : Blo 846354 1433443 := bstep (se 1 (by rfl) ⟨1075082, by rfl⟩ : syracuseStep 1433443 = 2150165) B2150165
theorem B1269617 : Blo 846354 1269617 := bstep (se 2 (by rfl) ⟨476106, by rfl⟩ : syracuseStep 1269617 = 952213) B952213
theorem B1269635 : Blo 846354 1269635 := bstep (se 1 (by rfl) ⟨952226, by rfl⟩ : syracuseStep 1269635 = 1904453) B1904453
theorem B1073027 : Blo 846354 1073027 := bstep (se 1 (by rfl) ⟨804770, by rfl⟩ : syracuseStep 1073027 = 1609541) B1609541
theorem B1269665 : Blo 846354 1269665 := bstep (se 2 (by rfl) ⟨476124, by rfl⟩ : syracuseStep 1269665 = 952249) B952249
theorem B1269683 : Blo 846354 1269683 := bstep (se 1 (by rfl) ⟨952262, by rfl⟩ : syracuseStep 1269683 = 1904525) B1904525
theorem B1269713 : Blo 846354 1269713 := bstep (se 2 (by rfl) ⟨476142, by rfl⟩ : syracuseStep 1269713 = 952285) B952285
theorem B1269731 : Blo 846354 1269731 := bstep (se 1 (by rfl) ⟨952298, by rfl⟩ : syracuseStep 1269731 = 1904597) B1904597
theorem B2416625 : Blo 846354 2416625 := bstep (se 2 (by rfl) ⟨906234, by rfl⟩ : syracuseStep 2416625 = 1812469) B1812469
theorem B1433585 : Blo 846354 1433585 := bstep (se 2 (by rfl) ⟨537594, by rfl⟩ : syracuseStep 1433585 = 1075189) B1075189
theorem B1269761 : Blo 846354 1269761 := bstep (se 2 (by rfl) ⟨476160, by rfl⟩ : syracuseStep 1269761 = 952321) B952321
theorem B1269779 : Blo 846354 1269779 := bstep (se 1 (by rfl) ⟨952334, by rfl⟩ : syracuseStep 1269779 = 1904669) B1904669
theorem B1269809 : Blo 846354 1269809 := bstep (se 2 (by rfl) ⟨476178, by rfl⟩ : syracuseStep 1269809 = 952357) B952357
theorem B1269827 : Blo 846354 1269827 := bstep (se 1 (by rfl) ⟨952370, by rfl⟩ : syracuseStep 1269827 = 1904741) B1904741
theorem B1269857 : Blo 846354 1269857 := bstep (se 2 (by rfl) ⟨476196, by rfl⟩ : syracuseStep 1269857 = 952393) B952393
theorem B1433713 : Blo 846354 1433713 := bstep (se 2 (by rfl) ⟨537642, by rfl⟩ : syracuseStep 1433713 = 1075285) B1075285
theorem B1269875 : Blo 846354 1269875 := bstep (se 1 (by rfl) ⟨952406, by rfl⟩ : syracuseStep 1269875 = 1904813) B1904813
theorem B4907141 : Blo 846354 4907141 := bstep (se 4 (by rfl) ⟨460044, by rfl⟩ : syracuseStep 4907141 = 920089) B920089
theorem B2711693 : Blo 846354 2711693 := bstep (se 3 (by rfl) ⟨508442, by rfl⟩ : syracuseStep 2711693 = 1016885) B1016885
theorem B1269905 : Blo 846354 1269905 := bstep (se 2 (by rfl) ⟨476214, by rfl⟩ : syracuseStep 1269905 = 952429) B952429
theorem B1433747 : Blo 846354 1433747 := bstep (se 1 (by rfl) ⟨1075310, by rfl⟩ : syracuseStep 1433747 = 2150621) B2150621
theorem B1269923 : Blo 846354 1269923 := bstep (se 1 (by rfl) ⟨952442, by rfl⟩ : syracuseStep 1269923 = 1904885) B1904885
theorem B2416817 : Blo 846354 2416817 := bstep (se 2 (by rfl) ⟨906306, by rfl⟩ : syracuseStep 2416817 = 1812613) B1812613
theorem B1269953 : Blo 846354 1269953 := bstep (se 2 (by rfl) ⟨476232, by rfl⟩ : syracuseStep 1269953 = 952465) B952465
theorem B6119621 : Blo 846354 6119621 := bstep (se 4 (by rfl) ⟨573714, by rfl⟩ : syracuseStep 6119621 = 1147429) B1147429
theorem B1269971 : Blo 846354 1269971 := bstep (se 1 (by rfl) ⟨952478, by rfl⟩ : syracuseStep 1269971 = 1904957) B1904957
theorem B1270001 : Blo 846354 1270001 := bstep (se 2 (by rfl) ⟨476250, by rfl⟩ : syracuseStep 1270001 = 952501) B952501
theorem B1270019 : Blo 846354 1270019 := bstep (se 1 (by rfl) ⟨952514, by rfl⟩ : syracuseStep 1270019 = 1905029) B1905029
theorem B1433875 : Blo 846354 1433875 := bstep (se 1 (by rfl) ⟨1075406, by rfl⟩ : syracuseStep 1433875 = 2150813) B2150813
theorem B1270049 : Blo 846354 1270049 := bstep (se 2 (by rfl) ⟨476268, by rfl⟩ : syracuseStep 1270049 = 952537) B952537
theorem B1270067 : Blo 846354 1270067 := bstep (se 1 (by rfl) ⟨952550, by rfl⟩ : syracuseStep 1270067 = 1905101) B1905101
theorem B1270097 : Blo 846354 1270097 := bstep (se 2 (by rfl) ⟨476286, by rfl⟩ : syracuseStep 1270097 = 952573) B952573
theorem B1270115 : Blo 846354 1270115 := bstep (se 1 (by rfl) ⟨952586, by rfl⟩ : syracuseStep 1270115 = 1905173) B1905173
theorem B1270145 : Blo 846354 1270145 := bstep (se 2 (by rfl) ⟨476304, by rfl⟩ : syracuseStep 1270145 = 952609) B952609
theorem B1270163 : Blo 846354 1270163 := bstep (se 1 (by rfl) ⟨952622, by rfl⟩ : syracuseStep 1270163 = 1905245) B1905245
theorem B1434017 : Blo 846354 1434017 := bstep (se 2 (by rfl) ⟨537756, by rfl⟩ : syracuseStep 1434017 = 1075513) B1075513
theorem B1270193 : Blo 846354 1270193 := bstep (se 2 (by rfl) ⟨476322, by rfl⟩ : syracuseStep 1270193 = 952645) B952645
theorem B1270211 : Blo 846354 1270211 := bstep (se 1 (by rfl) ⟨952658, by rfl⟩ : syracuseStep 1270211 = 1905317) B1905317
theorem B1270241 : Blo 846354 1270241 := bstep (se 2 (by rfl) ⟨476340, by rfl⟩ : syracuseStep 1270241 = 952681) B952681
theorem B4284899 : Blo 846354 4284899 := bstep (se 1 (by rfl) ⟨3213674, by rfl⟩ : syracuseStep 4284899 = 6427349) B6427349
theorem B1270259 : Blo 846354 1270259 := bstep (se 1 (by rfl) ⟨952694, by rfl⟩ : syracuseStep 1270259 = 1905389) B1905389
theorem B1270289 : Blo 846354 1270289 := bstep (se 2 (by rfl) ⟨476358, by rfl⟩ : syracuseStep 1270289 = 952717) B952717
theorem B1434145 : Blo 846354 1434145 := bstep (se 2 (by rfl) ⟨537804, by rfl⟩ : syracuseStep 1434145 = 1075609) B1075609
theorem B1270307 : Blo 846354 1270307 := bstep (se 1 (by rfl) ⟨952730, by rfl⟩ : syracuseStep 1270307 = 1905461) B1905461
theorem B13754933 : Blo 846354 13754933 := bstep (se 5 (by rfl) ⟨644762, by rfl⟩ : syracuseStep 13754933 = 1289525) B1289525
theorem B1270337 : Blo 846354 1270337 := bstep (se 2 (by rfl) ⟨476376, by rfl⟩ : syracuseStep 1270337 = 952753) B952753
theorem B1073731 : Blo 846354 1073731 := bstep (se 1 (by rfl) ⟨805298, by rfl⟩ : syracuseStep 1073731 = 1610597) B1610597
theorem B1434179 : Blo 846354 1434179 := bstep (se 1 (by rfl) ⟨1075634, by rfl⟩ : syracuseStep 1434179 = 2151269) B2151269
theorem B1270355 : Blo 846354 1270355 := bstep (se 1 (by rfl) ⟨952766, by rfl⟩ : syracuseStep 1270355 = 1905533) B1905533
theorem B1270385 : Blo 846354 1270385 := bstep (se 2 (by rfl) ⟨476394, by rfl⟩ : syracuseStep 1270385 = 952789) B952789
theorem B1270403 : Blo 846354 1270403 := bstep (se 1 (by rfl) ⟨952802, by rfl⟩ : syracuseStep 1270403 = 1905605) B1905605
theorem B1270433 : Blo 846354 1270433 := bstep (se 2 (by rfl) ⟨476412, by rfl⟩ : syracuseStep 1270433 = 952825) B952825
theorem B1073827 : Blo 846354 1073827 := bstep (se 1 (by rfl) ⟨805370, by rfl⟩ : syracuseStep 1073827 = 1610741) B1610741
theorem B1270451 : Blo 846354 1270451 := bstep (se 1 (by rfl) ⟨952838, by rfl⟩ : syracuseStep 1270451 = 1905677) B1905677
theorem B1434307 : Blo 846354 1434307 := bstep (se 1 (by rfl) ⟨1075730, by rfl⟩ : syracuseStep 1434307 = 2151461) B2151461
theorem B1270481 : Blo 846354 1270481 := bstep (se 2 (by rfl) ⟨476430, by rfl⟩ : syracuseStep 1270481 = 952861) B952861
theorem B1270499 : Blo 846354 1270499 := bstep (se 1 (by rfl) ⟨952874, by rfl⟩ : syracuseStep 1270499 = 1905749) B1905749
theorem B1270529 : Blo 846354 1270529 := bstep (se 2 (by rfl) ⟨476448, by rfl⟩ : syracuseStep 1270529 = 952897) B952897
theorem B3138317 : Blo 846354 3138317 := bstep (se 3 (by rfl) ⟨588434, by rfl⟩ : syracuseStep 3138317 = 1176869) B1176869
theorem B1270547 : Blo 846354 1270547 := bstep (se 1 (by rfl) ⟨952910, by rfl⟩ : syracuseStep 1270547 = 1905821) B1905821
theorem B1270577 : Blo 846354 1270577 := bstep (se 2 (by rfl) ⟨476466, by rfl⟩ : syracuseStep 1270577 = 952933) B952933
theorem B3629873 : Blo 846354 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B1270595 : Blo 846354 1270595 := bstep (se 1 (by rfl) ⟨952946, by rfl⟩ : syracuseStep 1270595 = 1905893) B1905893
theorem B1434449 : Blo 846354 1434449 := bstep (se 2 (by rfl) ⟨537918, by rfl⟩ : syracuseStep 1434449 = 1075837) B1075837
theorem B1270625 : Blo 846354 1270625 := bstep (se 2 (by rfl) ⟨476484, by rfl⟩ : syracuseStep 1270625 = 952969) B952969
theorem B9659249 : Blo 846354 9659249 := bstep (se 2 (by rfl) ⟨3622218, by rfl⟩ : syracuseStep 9659249 = 7244437) B7244437
theorem B1270643 : Blo 846354 1270643 := bstep (se 1 (by rfl) ⟨952982, by rfl⟩ : syracuseStep 1270643 = 1905965) B1905965
theorem B1270673 : Blo 846354 1270673 := bstep (se 2 (by rfl) ⟨476502, by rfl⟩ : syracuseStep 1270673 = 953005) B953005
theorem B1270691 : Blo 846354 1270691 := bstep (se 1 (by rfl) ⟨953018, by rfl⟩ : syracuseStep 1270691 = 1906037) B1906037
theorem B1270721 : Blo 846354 1270721 := bstep (se 2 (by rfl) ⟨476520, by rfl⟩ : syracuseStep 1270721 = 953041) B953041
theorem B1434577 : Blo 846354 1434577 := bstep (se 2 (by rfl) ⟨537966, by rfl⟩ : syracuseStep 1434577 = 1075933) B1075933
theorem B1270739 : Blo 846354 1270739 := bstep (se 1 (by rfl) ⟨953054, by rfl⟩ : syracuseStep 1270739 = 1906109) B1906109
theorem B1270769 : Blo 846354 1270769 := bstep (se 2 (by rfl) ⟨476538, by rfl⟩ : syracuseStep 1270769 = 953077) B953077
theorem B1434611 : Blo 846354 1434611 := bstep (se 1 (by rfl) ⟨1075958, by rfl⟩ : syracuseStep 1434611 = 2151917) B2151917
theorem B1270787 : Blo 846354 1270787 := bstep (se 1 (by rfl) ⟨953090, by rfl⟩ : syracuseStep 1270787 = 1906181) B1906181
theorem B1270817 : Blo 846354 1270817 := bstep (se 2 (by rfl) ⟨476556, by rfl⟩ : syracuseStep 1270817 = 953113) B953113
theorem B1270835 : Blo 846354 1270835 := bstep (se 1 (by rfl) ⟨953126, by rfl⟩ : syracuseStep 1270835 = 1906253) B1906253
theorem B1270865 : Blo 846354 1270865 := bstep (se 2 (by rfl) ⟨476574, by rfl⟩ : syracuseStep 1270865 = 953149) B953149
theorem B1270883 : Blo 846354 1270883 := bstep (se 1 (by rfl) ⟨953162, by rfl⟩ : syracuseStep 1270883 = 1906325) B1906325
theorem B1434739 : Blo 846354 1434739 := bstep (se 1 (by rfl) ⟨1076054, by rfl⟩ : syracuseStep 1434739 = 2152109) B2152109
theorem B1270913 : Blo 846354 1270913 := bstep (se 2 (by rfl) ⟨476592, by rfl⟩ : syracuseStep 1270913 = 953185) B953185
theorem B2417809 : Blo 846354 2417809 := bstep (se 2 (by rfl) ⟨906678, by rfl⟩ : syracuseStep 2417809 = 1813357) B1813357
theorem B1270931 : Blo 846354 1270931 := bstep (se 1 (by rfl) ⟨953198, by rfl⟩ : syracuseStep 1270931 = 1906397) B1906397
theorem B1074323 : Blo 846354 1074323 := bstep (se 1 (by rfl) ⟨805742, by rfl⟩ : syracuseStep 1074323 = 1611485) B1611485
theorem B1270961 : Blo 846354 1270961 := bstep (se 2 (by rfl) ⟨476610, by rfl⟩ : syracuseStep 1270961 = 953221) B953221
theorem B1270979 : Blo 846354 1270979 := bstep (se 1 (by rfl) ⟨953234, by rfl⟩ : syracuseStep 1270979 = 1906469) B1906469
theorem B1271009 : Blo 846354 1271009 := bstep (se 2 (by rfl) ⟨476628, by rfl⟩ : syracuseStep 1271009 = 953257) B953257
theorem B1271027 : Blo 846354 1271027 := bstep (se 1 (by rfl) ⟨953270, by rfl⟩ : syracuseStep 1271027 = 1906541) B1906541
theorem B1434881 : Blo 846354 1434881 := bstep (se 2 (by rfl) ⟨538080, by rfl⟩ : syracuseStep 1434881 = 1076161) B1076161
theorem B4285709 : Blo 846354 4285709 := bstep (se 3 (by rfl) ⟨803570, by rfl⟩ : syracuseStep 4285709 = 1607141) B1607141
theorem B1271057 : Blo 846354 1271057 := bstep (se 2 (by rfl) ⟨476646, by rfl⟩ : syracuseStep 1271057 = 953293) B953293
theorem B1271075 : Blo 846354 1271075 := bstep (se 1 (by rfl) ⟨953306, by rfl⟩ : syracuseStep 1271075 = 1906613) B1906613
theorem B4580657 : Blo 846354 4580657 := bstep (se 2 (by rfl) ⟨1717746, by rfl⟩ : syracuseStep 4580657 = 3435493) B3435493
theorem B1271105 : Blo 846354 1271105 := bstep (se 2 (by rfl) ⟨476664, by rfl⟩ : syracuseStep 1271105 = 953329) B953329
theorem B1271123 : Blo 846354 1271123 := bstep (se 1 (by rfl) ⟨953342, by rfl⟩ : syracuseStep 1271123 = 1906685) B1906685
theorem B1271153 : Blo 846354 1271153 := bstep (se 2 (by rfl) ⟨476682, by rfl⟩ : syracuseStep 1271153 = 953365) B953365
theorem B1271171 : Blo 846354 1271171 := bstep (se 1 (by rfl) ⟨953378, by rfl⟩ : syracuseStep 1271171 = 1906757) B1906757
theorem B1271201 : Blo 846354 1271201 := bstep (se 2 (by rfl) ⟨476700, by rfl⟩ : syracuseStep 1271201 = 953401) B953401
theorem B2319779 : Blo 846354 2319779 := bstep (se 1 (by rfl) ⟨1739834, by rfl⟩ : syracuseStep 2319779 = 3479669) B3479669
theorem B2418083 : Blo 846354 2418083 := bstep (se 1 (by rfl) ⟨1813562, by rfl⟩ : syracuseStep 2418083 = 3627125) B3627125
theorem B4842929 : Blo 846354 4842929 := bstep (se 2 (by rfl) ⟨1816098, by rfl⟩ : syracuseStep 4842929 = 3632197) B3632197
theorem B1271219 : Blo 846354 1271219 := bstep (se 1 (by rfl) ⟨953414, by rfl⟩ : syracuseStep 1271219 = 1906829) B1906829
theorem B3630541 : Blo 846354 3630541 := bstep (se 3 (by rfl) ⟨680726, by rfl⟩ : syracuseStep 3630541 = 1361453) B1361453
theorem B1271249 : Blo 846354 1271249 := bstep (se 2 (by rfl) ⟨476718, by rfl⟩ : syracuseStep 1271249 = 953437) B953437
theorem B1238483 : Blo 846354 1238483 := bstep (se 1 (by rfl) ⟨928862, by rfl⟩ : syracuseStep 1238483 = 1857725) B1857725
theorem B1271267 : Blo 846354 1271267 := bstep (se 1 (by rfl) ⟨953450, by rfl⟩ : syracuseStep 1271267 = 1906901) B1906901
theorem B1205761 : Blo 846354 1205761 := bstep (se 2 (by rfl) ⟨452160, by rfl⟩ : syracuseStep 1205761 = 904321) B904321
theorem B1271297 : Blo 846354 1271297 := bstep (se 2 (by rfl) ⟨476736, by rfl⟩ : syracuseStep 1271297 = 953473) B953473
theorem B1271315 : Blo 846354 1271315 := bstep (se 1 (by rfl) ⟨953486, by rfl⟩ : syracuseStep 1271315 = 1906973) B1906973
theorem B1271345 : Blo 846354 1271345 := bstep (se 2 (by rfl) ⟨476754, by rfl⟩ : syracuseStep 1271345 = 953509) B953509
theorem B1271363 : Blo 846354 1271363 := bstep (se 1 (by rfl) ⟨953522, by rfl⟩ : syracuseStep 1271363 = 1907045) B1907045
theorem B1205857 : Blo 846354 1205857 := bstep (se 2 (by rfl) ⟨452196, by rfl⟩ : syracuseStep 1205857 = 904393) B904393
theorem B1271393 : Blo 846354 1271393 := bstep (se 2 (by rfl) ⟨476772, by rfl⟩ : syracuseStep 1271393 = 953545) B953545
theorem B2418275 : Blo 846354 2418275 := bstep (se 1 (by rfl) ⟨1813706, by rfl⟩ : syracuseStep 2418275 = 3627413) B3627413
theorem B37774961 : Blo 846354 37774961 := bstep (se 2 (by rfl) ⟨14165610, by rfl⟩ : syracuseStep 37774961 = 28331221) B28331221
theorem B1271411 : Blo 846354 1271411 := bstep (se 1 (by rfl) ⟨953558, by rfl⟩ : syracuseStep 1271411 = 1907117) B1907117
theorem B1271441 : Blo 846354 1271441 := bstep (se 2 (by rfl) ⟨476790, by rfl⟩ : syracuseStep 1271441 = 953581) B953581
theorem B1271459 : Blo 846354 1271459 := bstep (se 1 (by rfl) ⟨953594, by rfl⟩ : syracuseStep 1271459 = 1907189) B1907189
theorem B1271489 : Blo 846354 1271489 := bstep (se 2 (by rfl) ⟨476808, by rfl⟩ : syracuseStep 1271489 = 953617) B953617
theorem B1271507 : Blo 846354 1271507 := bstep (se 1 (by rfl) ⟨953630, by rfl⟩ : syracuseStep 1271507 = 1907261) B1907261
theorem B1271537 : Blo 846354 1271537 := bstep (se 2 (by rfl) ⟨476826, by rfl⟩ : syracuseStep 1271537 = 953653) B953653
theorem B1271555 : Blo 846354 1271555 := bstep (se 1 (by rfl) ⟨953666, by rfl⟩ : syracuseStep 1271555 = 1907333) B1907333
theorem B6612749 : Blo 846354 6612749 := bstep (se 3 (by rfl) ⟨1239890, by rfl⟩ : syracuseStep 6612749 = 2479781) B2479781
theorem B5433101 : Blo 846354 5433101 := bstep (se 3 (by rfl) ⟨1018706, by rfl⟩ : syracuseStep 5433101 = 2037413) B2037413
theorem B1271585 : Blo 846354 1271585 := bstep (se 2 (by rfl) ⟨476844, by rfl⟩ : syracuseStep 1271585 = 953689) B953689
theorem B1271603 : Blo 846354 1271603 := bstep (se 1 (by rfl) ⟨953702, by rfl⟩ : syracuseStep 1271603 = 1907405) B1907405
theorem B1271633 : Blo 846354 1271633 := bstep (se 2 (by rfl) ⟨476862, by rfl⟩ : syracuseStep 1271633 = 953725) B953725
theorem B1075027 : Blo 846354 1075027 := bstep (se 1 (by rfl) ⟨806270, by rfl⟩ : syracuseStep 1075027 = 1612541) B1612541
theorem B1271651 : Blo 846354 1271651 := bstep (se 1 (by rfl) ⟨953738, by rfl⟩ : syracuseStep 1271651 = 1907477) B1907477
theorem B1271681 : Blo 846354 1271681 := bstep (se 2 (by rfl) ⟨476880, by rfl⟩ : syracuseStep 1271681 = 953761) B953761
theorem B2713475 : Blo 846354 2713475 := bstep (se 1 (by rfl) ⟨2035106, by rfl⟩ : syracuseStep 2713475 = 4070213) B4070213
theorem B39118733 : Blo 846354 39118733 := bstep (se 3 (by rfl) ⟨7334762, by rfl⟩ : syracuseStep 39118733 = 14669525) B14669525
theorem B1271699 : Blo 846354 1271699 := bstep (se 1 (by rfl) ⟨953774, by rfl⟩ : syracuseStep 1271699 = 1907549) B1907549
theorem B1271729 : Blo 846354 1271729 := bstep (se 2 (by rfl) ⟨476898, by rfl⟩ : syracuseStep 1271729 = 953797) B953797
theorem B1075123 : Blo 846354 1075123 := bstep (se 1 (by rfl) ⟨806342, by rfl⟩ : syracuseStep 1075123 = 1612685) B1612685
theorem B1271747 : Blo 846354 1271747 := bstep (se 1 (by rfl) ⟨953810, by rfl⟩ : syracuseStep 1271747 = 1907621) B1907621
theorem B1632209 : Blo 846354 1632209 := bstep (se 2 (by rfl) ⟨612078, by rfl⟩ : syracuseStep 1632209 = 1224157) B1224157
theorem B1271777 : Blo 846354 1271777 := bstep (se 2 (by rfl) ⟨476916, by rfl⟩ : syracuseStep 1271777 = 953833) B953833
theorem B1271795 : Blo 846354 1271795 := bstep (se 1 (by rfl) ⟨953846, by rfl⟩ : syracuseStep 1271795 = 1907693) B1907693
theorem B1009667 : Blo 846354 1009667 := bstep (se 1 (by rfl) ⟨757250, by rfl⟩ : syracuseStep 1009667 = 1514501) B1514501
theorem B1271825 : Blo 846354 1271825 := bstep (se 2 (by rfl) ⟨476934, by rfl⟩ : syracuseStep 1271825 = 953869) B953869
theorem B1271843 : Blo 846354 1271843 := bstep (se 1 (by rfl) ⟨953882, by rfl⟩ : syracuseStep 1271843 = 1907765) B1907765
theorem B3631139 : Blo 846354 3631139 := bstep (se 1 (by rfl) ⟨2723354, by rfl⟩ : syracuseStep 3631139 = 5446709) B5446709
theorem B1271873 : Blo 846354 1271873 := bstep (se 2 (by rfl) ⟨476952, by rfl⟩ : syracuseStep 1271873 = 953905) B953905
theorem B1206353 : Blo 846354 1206353 := bstep (se 2 (by rfl) ⟨452382, by rfl⟩ : syracuseStep 1206353 = 904765) B904765
theorem B1271891 : Blo 846354 1271891 := bstep (se 1 (by rfl) ⟨953918, by rfl⟩ : syracuseStep 1271891 = 1907837) B1907837
theorem B1271921 : Blo 846354 1271921 := bstep (se 2 (by rfl) ⟨476970, by rfl⟩ : syracuseStep 1271921 = 953941) B953941
theorem B1271939 : Blo 846354 1271939 := bstep (se 1 (by rfl) ⟨953954, by rfl⟩ : syracuseStep 1271939 = 1907909) B1907909
theorem B1271969 : Blo 846354 1271969 := bstep (se 2 (by rfl) ⟨476988, by rfl⟩ : syracuseStep 1271969 = 953977) B953977
theorem B1271987 : Blo 846354 1271987 := bstep (se 1 (by rfl) ⟨953990, by rfl⟩ : syracuseStep 1271987 = 1907981) B1907981
theorem B1272017 : Blo 846354 1272017 := bstep (se 2 (by rfl) ⟨477006, by rfl⟩ : syracuseStep 1272017 = 954013) B954013
theorem B1272035 : Blo 846354 1272035 := bstep (se 1 (by rfl) ⟨954026, by rfl⟩ : syracuseStep 1272035 = 1908053) B1908053
theorem B1272065 : Blo 846354 1272065 := bstep (se 2 (by rfl) ⟨477024, by rfl⟩ : syracuseStep 1272065 = 954049) B954049
theorem B1272083 : Blo 846354 1272083 := bstep (se 1 (by rfl) ⟨954062, by rfl⟩ : syracuseStep 1272083 = 1908125) B1908125
theorem B1272113 : Blo 846354 1272113 := bstep (se 2 (by rfl) ⟨477042, by rfl⟩ : syracuseStep 1272113 = 954085) B954085
theorem B2287939 : Blo 846354 2287939 := bstep (se 1 (by rfl) ⟨1715954, by rfl⟩ : syracuseStep 2287939 = 3431909) B3431909
theorem B1272131 : Blo 846354 1272131 := bstep (se 1 (by rfl) ⟨954098, by rfl⟩ : syracuseStep 1272131 = 1908197) B1908197
theorem B1272161 : Blo 846354 1272161 := bstep (se 2 (by rfl) ⟨477060, by rfl⟩ : syracuseStep 1272161 = 954121) B954121
theorem B1272179 : Blo 846354 1272179 := bstep (se 1 (by rfl) ⟨954134, by rfl⟩ : syracuseStep 1272179 = 1908269) B1908269
theorem B2419085 : Blo 846354 2419085 := bstep (se 3 (by rfl) ⟨453578, by rfl⟩ : syracuseStep 2419085 = 907157) B907157
theorem B1272209 : Blo 846354 1272209 := bstep (se 2 (by rfl) ⟨477078, by rfl⟩ : syracuseStep 1272209 = 954157) B954157
theorem B1272227 : Blo 846354 1272227 := bstep (se 1 (by rfl) ⟨954170, by rfl⟩ : syracuseStep 1272227 = 1908341) B1908341
theorem B1075619 : Blo 846354 1075619 := bstep (se 1 (by rfl) ⟨806714, by rfl⟩ : syracuseStep 1075619 = 1613429) B1613429
theorem B1272257 : Blo 846354 1272257 := bstep (se 2 (by rfl) ⟨477096, by rfl⟩ : syracuseStep 1272257 = 954193) B954193
theorem B1272275 : Blo 846354 1272275 := bstep (se 1 (by rfl) ⟨954206, by rfl⟩ : syracuseStep 1272275 = 1908413) B1908413
theorem B1272305 : Blo 846354 1272305 := bstep (se 2 (by rfl) ⟨477114, by rfl⟩ : syracuseStep 1272305 = 954229) B954229
theorem B1272323 : Blo 846354 1272323 := bstep (se 1 (by rfl) ⟨954242, by rfl⟩ : syracuseStep 1272323 = 1908485) B1908485
theorem B846355 : Blo 846354 846355 := bstep (se 1 (by rfl) ⟨634766, by rfl⟩ : syracuseStep 846355 = 1269533) B1269533
theorem B1272353 : Blo 846354 1272353 := bstep (se 2 (by rfl) ⟨477132, by rfl⟩ : syracuseStep 1272353 = 954265) B954265
theorem B846371 : Blo 846354 846371 := bstep (se 1 (by rfl) ⟨634778, by rfl⟩ : syracuseStep 846371 = 1269557) B1269557
theorem B846387 : Blo 846354 846387 := bstep (se 1 (by rfl) ⟨634790, by rfl⟩ : syracuseStep 846387 = 1269581) B1269581
theorem B1272371 : Blo 846354 1272371 := bstep (se 1 (by rfl) ⟨954278, by rfl⟩ : syracuseStep 1272371 = 1908557) B1908557
theorem B846403 : Blo 846354 846403 := bstep (se 1 (by rfl) ⟨634802, by rfl⟩ : syracuseStep 846403 = 1269605) B1269605
theorem B2419267 : Blo 846354 2419267 := bstep (se 1 (by rfl) ⟨1814450, by rfl⟩ : syracuseStep 2419267 = 3628901) B3628901
theorem B1272401 : Blo 846354 1272401 := bstep (se 2 (by rfl) ⟨477150, by rfl⟩ : syracuseStep 1272401 = 954301) B954301
theorem B846419 : Blo 846354 846419 := bstep (se 1 (by rfl) ⟨634814, by rfl⟩ : syracuseStep 846419 = 1269629) B1269629
theorem B846435 : Blo 846354 846435 := bstep (se 1 (by rfl) ⟨634826, by rfl⟩ : syracuseStep 846435 = 1269653) B1269653
theorem B1272419 : Blo 846354 1272419 := bstep (se 1 (by rfl) ⟨954314, by rfl⟩ : syracuseStep 1272419 = 1908629) B1908629
theorem B1632881 : Blo 846354 1632881 := bstep (se 2 (by rfl) ⟨612330, by rfl⟩ : syracuseStep 1632881 = 1224661) B1224661
theorem B846451 : Blo 846354 846451 := bstep (se 1 (by rfl) ⟨634838, by rfl⟩ : syracuseStep 846451 = 1269677) B1269677
theorem B1272449 : Blo 846354 1272449 := bstep (se 2 (by rfl) ⟨477168, by rfl⟩ : syracuseStep 1272449 = 954337) B954337
theorem B846467 : Blo 846354 846467 := bstep (se 1 (by rfl) ⟨634850, by rfl⟩ : syracuseStep 846467 = 1269701) B1269701
theorem B846483 : Blo 846354 846483 := bstep (se 1 (by rfl) ⟨634862, by rfl⟩ : syracuseStep 846483 = 1269725) B1269725
theorem B1272467 : Blo 846354 1272467 := bstep (se 1 (by rfl) ⟨954350, by rfl⟩ : syracuseStep 1272467 = 1908701) B1908701
theorem B846499 : Blo 846354 846499 := bstep (se 1 (by rfl) ⟨634874, by rfl⟩ : syracuseStep 846499 = 1269749) B1269749
theorem B1272497 : Blo 846354 1272497 := bstep (se 2 (by rfl) ⟨477186, by rfl⟩ : syracuseStep 1272497 = 954373) B954373
theorem B846515 : Blo 846354 846515 := bstep (se 1 (by rfl) ⟨634886, by rfl⟩ : syracuseStep 846515 = 1269773) B1269773
theorem B846531 : Blo 846354 846531 := bstep (se 1 (by rfl) ⟨634898, by rfl⟩ : syracuseStep 846531 = 1269797) B1269797
theorem B1272515 : Blo 846354 1272515 := bstep (se 1 (by rfl) ⟨954386, by rfl⟩ : syracuseStep 1272515 = 1908773) B1908773
theorem B846547 : Blo 846354 846547 := bstep (se 1 (by rfl) ⟨634910, by rfl⟩ : syracuseStep 846547 = 1269821) B1269821
theorem B1272545 : Blo 846354 1272545 := bstep (se 2 (by rfl) ⟨477204, by rfl⟩ : syracuseStep 1272545 = 954409) B954409
theorem B846563 : Blo 846354 846563 := bstep (se 1 (by rfl) ⟨634922, by rfl⟩ : syracuseStep 846563 = 1269845) B1269845
theorem B846579 : Blo 846354 846579 := bstep (se 1 (by rfl) ⟨634934, by rfl⟩ : syracuseStep 846579 = 1269869) B1269869
theorem B1272563 : Blo 846354 1272563 := bstep (se 1 (by rfl) ⟨954422, by rfl⟩ : syracuseStep 1272563 = 1908845) B1908845
theorem B846595 : Blo 846354 846595 := bstep (se 1 (by rfl) ⟨634946, by rfl⟩ : syracuseStep 846595 = 1269893) B1269893
theorem B1272593 : Blo 846354 1272593 := bstep (se 2 (by rfl) ⟨477222, by rfl⟩ : syracuseStep 1272593 = 954445) B954445
theorem B846611 : Blo 846354 846611 := bstep (se 1 (by rfl) ⟨634958, by rfl⟩ : syracuseStep 846611 = 1269917) B1269917
theorem B846627 : Blo 846354 846627 := bstep (se 1 (by rfl) ⟨634970, by rfl⟩ : syracuseStep 846627 = 1269941) B1269941
theorem B1272611 : Blo 846354 1272611 := bstep (se 1 (by rfl) ⟨954458, by rfl⟩ : syracuseStep 1272611 = 1908917) B1908917
theorem B846643 : Blo 846354 846643 := bstep (se 1 (by rfl) ⟨634982, by rfl⟩ : syracuseStep 846643 = 1269965) B1269965
theorem B1272641 : Blo 846354 1272641 := bstep (se 2 (by rfl) ⟨477240, by rfl⟩ : syracuseStep 1272641 = 954481) B954481
theorem B846659 : Blo 846354 846659 := bstep (se 1 (by rfl) ⟨634994, by rfl⟩ : syracuseStep 846659 = 1269989) B1269989
theorem B846675 : Blo 846354 846675 := bstep (se 1 (by rfl) ⟨635006, by rfl⟩ : syracuseStep 846675 = 1270013) B1270013
theorem B1272659 : Blo 846354 1272659 := bstep (se 1 (by rfl) ⟨954494, by rfl⟩ : syracuseStep 1272659 = 1908989) B1908989
theorem B846691 : Blo 846354 846691 := bstep (se 1 (by rfl) ⟨635018, by rfl⟩ : syracuseStep 846691 = 1270037) B1270037
theorem B1272689 : Blo 846354 1272689 := bstep (se 2 (by rfl) ⟨477258, by rfl⟩ : syracuseStep 1272689 = 954517) B954517
theorem B846707 : Blo 846354 846707 := bstep (se 1 (by rfl) ⟨635030, by rfl⟩ : syracuseStep 846707 = 1270061) B1270061
theorem B846723 : Blo 846354 846723 := bstep (se 1 (by rfl) ⟨635042, by rfl⟩ : syracuseStep 846723 = 1270085) B1270085
theorem B1272707 : Blo 846354 1272707 := bstep (se 1 (by rfl) ⟨954530, by rfl⟩ : syracuseStep 1272707 = 1909061) B1909061
theorem B846739 : Blo 846354 846739 := bstep (se 1 (by rfl) ⟨635054, by rfl⟩ : syracuseStep 846739 = 1270109) B1270109
theorem B1272737 : Blo 846354 1272737 := bstep (se 2 (by rfl) ⟨477276, by rfl⟩ : syracuseStep 1272737 = 954553) B954553
theorem B846755 : Blo 846354 846755 := bstep (se 1 (by rfl) ⟨635066, by rfl⟩ : syracuseStep 846755 = 1270133) B1270133
theorem B846771 : Blo 846354 846771 := bstep (se 1 (by rfl) ⟨635078, by rfl⟩ : syracuseStep 846771 = 1270157) B1270157
theorem B1207219 : Blo 846354 1207219 := bstep (se 1 (by rfl) ⟨905414, by rfl⟩ : syracuseStep 1207219 = 1810829) B1810829
theorem B1272755 : Blo 846354 1272755 := bstep (se 1 (by rfl) ⟨954566, by rfl⟩ : syracuseStep 1272755 = 1909133) B1909133
theorem B846787 : Blo 846354 846787 := bstep (se 1 (by rfl) ⟨635090, by rfl⟩ : syracuseStep 846787 = 1270181) B1270181
theorem B2714563 : Blo 846354 2714563 := bstep (se 1 (by rfl) ⟨2035922, by rfl⟩ : syracuseStep 2714563 = 4071845) B4071845
theorem B1272785 : Blo 846354 1272785 := bstep (se 2 (by rfl) ⟨477294, by rfl⟩ : syracuseStep 1272785 = 954589) B954589
theorem B846803 : Blo 846354 846803 := bstep (se 1 (by rfl) ⟨635102, by rfl⟩ : syracuseStep 846803 = 1270205) B1270205
theorem B846819 : Blo 846354 846819 := bstep (se 1 (by rfl) ⟨635114, by rfl⟩ : syracuseStep 846819 = 1270229) B1270229
theorem B1272803 : Blo 846354 1272803 := bstep (se 1 (by rfl) ⟨954602, by rfl⟩ : syracuseStep 1272803 = 1909205) B1909205
theorem B846835 : Blo 846354 846835 := bstep (se 1 (by rfl) ⟨635126, by rfl⟩ : syracuseStep 846835 = 1270253) B1270253
theorem B1272833 : Blo 846354 1272833 := bstep (se 2 (by rfl) ⟨477312, by rfl⟩ : syracuseStep 1272833 = 954625) B954625
theorem B846851 : Blo 846354 846851 := bstep (se 1 (by rfl) ⟨635138, by rfl⟩ : syracuseStep 846851 = 1270277) B1270277
theorem B846867 : Blo 846354 846867 := bstep (se 1 (by rfl) ⟨635150, by rfl⟩ : syracuseStep 846867 = 1270301) B1270301
theorem B1207315 : Blo 846354 1207315 := bstep (se 1 (by rfl) ⟨905486, by rfl⟩ : syracuseStep 1207315 = 1810973) B1810973
theorem B1272851 : Blo 846354 1272851 := bstep (se 1 (by rfl) ⟨954638, by rfl⟩ : syracuseStep 1272851 = 1909277) B1909277
theorem B846883 : Blo 846354 846883 := bstep (se 1 (by rfl) ⟨635162, by rfl⟩ : syracuseStep 846883 = 1270325) B1270325
theorem B2419757 : Blo 846354 2419757 := bstep (se 3 (by rfl) ⟨453704, by rfl⟩ : syracuseStep 2419757 = 907409) B907409
theorem B1272881 : Blo 846354 1272881 := bstep (se 2 (by rfl) ⟨477330, by rfl⟩ : syracuseStep 1272881 = 954661) B954661
theorem B846899 : Blo 846354 846899 := bstep (se 1 (by rfl) ⟨635174, by rfl⟩ : syracuseStep 846899 = 1270349) B1270349
theorem B846915 : Blo 846354 846915 := bstep (se 1 (by rfl) ⟨635186, by rfl⟩ : syracuseStep 846915 = 1270373) B1270373
theorem B1272899 : Blo 846354 1272899 := bstep (se 1 (by rfl) ⟨954674, by rfl⟩ : syracuseStep 1272899 = 1909349) B1909349
theorem B2714705 : Blo 846354 2714705 := bstep (se 2 (by rfl) ⟨1018014, by rfl⟩ : syracuseStep 2714705 = 2036029) B2036029
theorem B846931 : Blo 846354 846931 := bstep (se 1 (by rfl) ⟨635198, by rfl⟩ : syracuseStep 846931 = 1270397) B1270397
theorem B1272929 : Blo 846354 1272929 := bstep (se 2 (by rfl) ⟨477348, by rfl⟩ : syracuseStep 1272929 = 954697) B954697
theorem B846947 : Blo 846354 846947 := bstep (se 1 (by rfl) ⟨635210, by rfl⟩ : syracuseStep 846947 = 1270421) B1270421
theorem B846963 : Blo 846354 846963 := bstep (se 1 (by rfl) ⟨635222, by rfl⟩ : syracuseStep 846963 = 1270445) B1270445
theorem B1272947 : Blo 846354 1272947 := bstep (se 1 (by rfl) ⟨954710, by rfl⟩ : syracuseStep 1272947 = 1909421) B1909421
theorem B846979 : Blo 846354 846979 := bstep (se 1 (by rfl) ⟨635234, by rfl⟩ : syracuseStep 846979 = 1270469) B1270469
theorem B1272977 : Blo 846354 1272977 := bstep (se 2 (by rfl) ⟨477366, by rfl⟩ : syracuseStep 1272977 = 954733) B954733
theorem B846995 : Blo 846354 846995 := bstep (se 1 (by rfl) ⟨635246, by rfl⟩ : syracuseStep 846995 = 1270493) B1270493
theorem B847011 : Blo 846354 847011 := bstep (se 1 (by rfl) ⟨635258, by rfl⟩ : syracuseStep 847011 = 1270517) B1270517
theorem B1272995 : Blo 846354 1272995 := bstep (se 1 (by rfl) ⟨954746, by rfl⟩ : syracuseStep 1272995 = 1909493) B1909493
theorem B847027 : Blo 846354 847027 := bstep (se 1 (by rfl) ⟨635270, by rfl⟩ : syracuseStep 847027 = 1270541) B1270541
theorem B1273025 : Blo 846354 1273025 := bstep (se 2 (by rfl) ⟨477384, by rfl⟩ : syracuseStep 1273025 = 954769) B954769
theorem B847043 : Blo 846354 847043 := bstep (se 1 (by rfl) ⟨635282, by rfl⟩ : syracuseStep 847043 = 1270565) B1270565
theorem B847059 : Blo 846354 847059 := bstep (se 1 (by rfl) ⟨635294, by rfl⟩ : syracuseStep 847059 = 1270589) B1270589
theorem B1273043 : Blo 846354 1273043 := bstep (se 1 (by rfl) ⟨954782, by rfl⟩ : syracuseStep 1273043 = 1909565) B1909565
theorem B847075 : Blo 846354 847075 := bstep (se 1 (by rfl) ⟨635306, by rfl⟩ : syracuseStep 847075 = 1270613) B1270613
theorem B1273073 : Blo 846354 1273073 := bstep (se 2 (by rfl) ⟨477402, by rfl⟩ : syracuseStep 1273073 = 954805) B954805
theorem B847091 : Blo 846354 847091 := bstep (se 1 (by rfl) ⟨635318, by rfl⟩ : syracuseStep 847091 = 1270637) B1270637
theorem B2288899 : Blo 846354 2288899 := bstep (se 1 (by rfl) ⟨1716674, by rfl⟩ : syracuseStep 2288899 = 3433349) B3433349
theorem B847107 : Blo 846354 847107 := bstep (se 1 (by rfl) ⟨635330, by rfl⟩ : syracuseStep 847107 = 1270661) B1270661
theorem B1273091 : Blo 846354 1273091 := bstep (se 1 (by rfl) ⟨954818, by rfl⟩ : syracuseStep 1273091 = 1909637) B1909637
theorem B847123 : Blo 846354 847123 := bstep (se 1 (by rfl) ⟨635342, by rfl⟩ : syracuseStep 847123 = 1270685) B1270685
theorem B1273121 : Blo 846354 1273121 := bstep (se 2 (by rfl) ⟨477420, by rfl⟩ : syracuseStep 1273121 = 954841) B954841
theorem B847139 : Blo 846354 847139 := bstep (se 1 (by rfl) ⟨635354, by rfl⟩ : syracuseStep 847139 = 1270709) B1270709
theorem B847155 : Blo 846354 847155 := bstep (se 1 (by rfl) ⟨635366, by rfl⟩ : syracuseStep 847155 = 1270733) B1270733
theorem B1273139 : Blo 846354 1273139 := bstep (se 1 (by rfl) ⟨954854, by rfl⟩ : syracuseStep 1273139 = 1909709) B1909709
theorem B847171 : Blo 846354 847171 := bstep (se 1 (by rfl) ⟨635378, by rfl⟩ : syracuseStep 847171 = 1270757) B1270757
theorem B1273169 : Blo 846354 1273169 := bstep (se 2 (by rfl) ⟨477438, by rfl⟩ : syracuseStep 1273169 = 954877) B954877
theorem B847187 : Blo 846354 847187 := bstep (se 1 (by rfl) ⟨635390, by rfl⟩ : syracuseStep 847187 = 1270781) B1270781
theorem B847203 : Blo 846354 847203 := bstep (se 1 (by rfl) ⟨635402, by rfl⟩ : syracuseStep 847203 = 1270805) B1270805
theorem B1273187 : Blo 846354 1273187 := bstep (se 1 (by rfl) ⟨954890, by rfl⟩ : syracuseStep 1273187 = 1909781) B1909781
theorem B847219 : Blo 846354 847219 := bstep (se 1 (by rfl) ⟨635414, by rfl⟩ : syracuseStep 847219 = 1270829) B1270829
theorem B1273217 : Blo 846354 1273217 := bstep (se 2 (by rfl) ⟨477456, by rfl⟩ : syracuseStep 1273217 = 954913) B954913
theorem B847235 : Blo 846354 847235 := bstep (se 1 (by rfl) ⟨635426, by rfl⟩ : syracuseStep 847235 = 1270853) B1270853
theorem B847251 : Blo 846354 847251 := bstep (se 1 (by rfl) ⟨635438, by rfl⟩ : syracuseStep 847251 = 1270877) B1270877
theorem B1273235 : Blo 846354 1273235 := bstep (se 1 (by rfl) ⟨954926, by rfl⟩ : syracuseStep 1273235 = 1909853) B1909853
theorem B847267 : Blo 846354 847267 := bstep (se 1 (by rfl) ⟨635450, by rfl⟩ : syracuseStep 847267 = 1270901) B1270901
theorem B1273265 : Blo 846354 1273265 := bstep (se 2 (by rfl) ⟨477474, by rfl⟩ : syracuseStep 1273265 = 954949) B954949
theorem B847283 : Blo 846354 847283 := bstep (se 1 (by rfl) ⟨635462, by rfl⟩ : syracuseStep 847283 = 1270925) B1270925
theorem B847299 : Blo 846354 847299 := bstep (se 1 (by rfl) ⟨635474, by rfl⟩ : syracuseStep 847299 = 1270949) B1270949
theorem B1273283 : Blo 846354 1273283 := bstep (se 1 (by rfl) ⟨954962, by rfl⟩ : syracuseStep 1273283 = 1909925) B1909925
theorem B847315 : Blo 846354 847315 := bstep (se 1 (by rfl) ⟨635486, by rfl⟩ : syracuseStep 847315 = 1270973) B1270973
theorem B1273313 : Blo 846354 1273313 := bstep (se 2 (by rfl) ⟨477492, by rfl⟩ : syracuseStep 1273313 = 954985) B954985
theorem B847331 : Blo 846354 847331 := bstep (se 1 (by rfl) ⟨635498, by rfl⟩ : syracuseStep 847331 = 1270997) B1270997
theorem B847347 : Blo 846354 847347 := bstep (se 1 (by rfl) ⟨635510, by rfl⟩ : syracuseStep 847347 = 1271021) B1271021
theorem B1273331 : Blo 846354 1273331 := bstep (se 1 (by rfl) ⟨954998, by rfl⟩ : syracuseStep 1273331 = 1909997) B1909997
theorem B847363 : Blo 846354 847363 := bstep (se 1 (by rfl) ⟨635522, by rfl⟩ : syracuseStep 847363 = 1271045) B1271045
theorem B1207811 : Blo 846354 1207811 := bstep (se 1 (by rfl) ⟨905858, by rfl⟩ : syracuseStep 1207811 = 1811717) B1811717
theorem B1273361 : Blo 846354 1273361 := bstep (se 2 (by rfl) ⟨477510, by rfl⟩ : syracuseStep 1273361 = 955021) B955021
theorem B847379 : Blo 846354 847379 := bstep (se 1 (by rfl) ⟨635534, by rfl⟩ : syracuseStep 847379 = 1271069) B1271069
theorem B847395 : Blo 846354 847395 := bstep (se 1 (by rfl) ⟨635546, by rfl⟩ : syracuseStep 847395 = 1271093) B1271093
theorem B1273379 : Blo 846354 1273379 := bstep (se 1 (by rfl) ⟨955034, by rfl⟩ : syracuseStep 1273379 = 1910069) B1910069
theorem B847411 : Blo 846354 847411 := bstep (se 1 (by rfl) ⟨635558, by rfl⟩ : syracuseStep 847411 = 1271117) B1271117
theorem B1273409 : Blo 846354 1273409 := bstep (se 2 (by rfl) ⟨477528, by rfl⟩ : syracuseStep 1273409 = 955057) B955057
theorem B847427 : Blo 846354 847427 := bstep (se 1 (by rfl) ⟨635570, by rfl⟩ : syracuseStep 847427 = 1271141) B1271141
theorem B847443 : Blo 846354 847443 := bstep (se 1 (by rfl) ⟨635582, by rfl⟩ : syracuseStep 847443 = 1271165) B1271165
theorem B1273427 : Blo 846354 1273427 := bstep (se 1 (by rfl) ⟨955070, by rfl⟩ : syracuseStep 1273427 = 1910141) B1910141
theorem B847459 : Blo 846354 847459 := bstep (se 1 (by rfl) ⟨635594, by rfl⟩ : syracuseStep 847459 = 1271189) B1271189
theorem B1273457 : Blo 846354 1273457 := bstep (se 2 (by rfl) ⟨477546, by rfl⟩ : syracuseStep 1273457 = 955093) B955093
theorem B847475 : Blo 846354 847475 := bstep (se 1 (by rfl) ⟨635606, by rfl⟩ : syracuseStep 847475 = 1271213) B1271213
theorem B847491 : Blo 846354 847491 := bstep (se 1 (by rfl) ⟨635618, by rfl⟩ : syracuseStep 847491 = 1271237) B1271237
theorem B1273475 : Blo 846354 1273475 := bstep (se 1 (by rfl) ⟨955106, by rfl⟩ : syracuseStep 1273475 = 1910213) B1910213
theorem B3272333 : Blo 846354 3272333 := bstep (se 3 (by rfl) ⟨613562, by rfl⟩ : syracuseStep 3272333 = 1227125) B1227125
theorem B847507 : Blo 846354 847507 := bstep (se 1 (by rfl) ⟨635630, by rfl⟩ : syracuseStep 847507 = 1271261) B1271261
theorem B1273505 : Blo 846354 1273505 := bstep (se 2 (by rfl) ⟨477564, by rfl⟩ : syracuseStep 1273505 = 955129) B955129
theorem B3305123 : Blo 846354 3305123 := bstep (se 1 (by rfl) ⟨2478842, by rfl⟩ : syracuseStep 3305123 = 4957685) B4957685
theorem B847523 : Blo 846354 847523 := bstep (se 1 (by rfl) ⟨635642, by rfl⟩ : syracuseStep 847523 = 1271285) B1271285
theorem B847539 : Blo 846354 847539 := bstep (se 1 (by rfl) ⟨635654, by rfl⟩ : syracuseStep 847539 = 1271309) B1271309
theorem B1273523 : Blo 846354 1273523 := bstep (se 1 (by rfl) ⟨955142, by rfl⟩ : syracuseStep 1273523 = 1910285) B1910285
theorem B847555 : Blo 846354 847555 := bstep (se 1 (by rfl) ⟨635666, by rfl⟩ : syracuseStep 847555 = 1271333) B1271333
theorem B1273553 : Blo 846354 1273553 := bstep (se 2 (by rfl) ⟨477582, by rfl⟩ : syracuseStep 1273553 = 955165) B955165
theorem B847571 : Blo 846354 847571 := bstep (se 1 (by rfl) ⟨635678, by rfl⟩ : syracuseStep 847571 = 1271357) B1271357
theorem B847587 : Blo 846354 847587 := bstep (se 1 (by rfl) ⟨635690, by rfl⟩ : syracuseStep 847587 = 1271381) B1271381
theorem B1273571 : Blo 846354 1273571 := bstep (se 1 (by rfl) ⟨955178, by rfl⟩ : syracuseStep 1273571 = 1910357) B1910357
theorem B847603 : Blo 846354 847603 := bstep (se 1 (by rfl) ⟨635702, by rfl⟩ : syracuseStep 847603 = 1271405) B1271405
theorem B1273601 : Blo 846354 1273601 := bstep (se 2 (by rfl) ⟨477600, by rfl⟩ : syracuseStep 1273601 = 955201) B955201
theorem B847619 : Blo 846354 847619 := bstep (se 1 (by rfl) ⟨635714, by rfl⟩ : syracuseStep 847619 = 1271429) B1271429
theorem B847635 : Blo 846354 847635 := bstep (se 1 (by rfl) ⟨635726, by rfl⟩ : syracuseStep 847635 = 1271453) B1271453
theorem B1273619 : Blo 846354 1273619 := bstep (se 1 (by rfl) ⟨955214, by rfl⟩ : syracuseStep 1273619 = 1910429) B1910429
theorem B847651 : Blo 846354 847651 := bstep (se 1 (by rfl) ⟨635738, by rfl⟩ : syracuseStep 847651 = 1271477) B1271477
theorem B1273649 : Blo 846354 1273649 := bstep (se 2 (by rfl) ⟨477618, by rfl⟩ : syracuseStep 1273649 = 955237) B955237
theorem B847667 : Blo 846354 847667 := bstep (se 1 (by rfl) ⟨635750, by rfl⟩ : syracuseStep 847667 = 1271501) B1271501
theorem B847683 : Blo 846354 847683 := bstep (se 1 (by rfl) ⟨635762, by rfl⟩ : syracuseStep 847683 = 1271525) B1271525
theorem B1273667 : Blo 846354 1273667 := bstep (se 1 (by rfl) ⟨955250, by rfl⟩ : syracuseStep 1273667 = 1910501) B1910501
theorem B847699 : Blo 846354 847699 := bstep (se 1 (by rfl) ⟨635774, by rfl⟩ : syracuseStep 847699 = 1271549) B1271549
theorem B1273697 : Blo 846354 1273697 := bstep (se 2 (by rfl) ⟨477636, by rfl⟩ : syracuseStep 1273697 = 955273) B955273
theorem B847715 : Blo 846354 847715 := bstep (se 1 (by rfl) ⟨635786, by rfl⟩ : syracuseStep 847715 = 1271573) B1271573
theorem B847731 : Blo 846354 847731 := bstep (se 1 (by rfl) ⟨635798, by rfl⟩ : syracuseStep 847731 = 1271597) B1271597
theorem B1273715 : Blo 846354 1273715 := bstep (se 1 (by rfl) ⟨955286, by rfl⟩ : syracuseStep 1273715 = 1910573) B1910573
theorem B847747 : Blo 846354 847747 := bstep (se 1 (by rfl) ⟨635810, by rfl⟩ : syracuseStep 847747 = 1271621) B1271621
theorem B1273745 : Blo 846354 1273745 := bstep (se 2 (by rfl) ⟨477654, by rfl⟩ : syracuseStep 1273745 = 955309) B955309
theorem B847763 : Blo 846354 847763 := bstep (se 1 (by rfl) ⟨635822, by rfl⟩ : syracuseStep 847763 = 1271645) B1271645
theorem B847779 : Blo 846354 847779 := bstep (se 1 (by rfl) ⟨635834, by rfl⟩ : syracuseStep 847779 = 1271669) B1271669
theorem B1273763 : Blo 846354 1273763 := bstep (se 1 (by rfl) ⟨955322, by rfl⟩ : syracuseStep 1273763 = 1910645) B1910645
theorem B847795 : Blo 846354 847795 := bstep (se 1 (by rfl) ⟨635846, by rfl⟩ : syracuseStep 847795 = 1271693) B1271693
theorem B1273793 : Blo 846354 1273793 := bstep (se 2 (by rfl) ⟨477672, by rfl⟩ : syracuseStep 1273793 = 955345) B955345
theorem B847811 : Blo 846354 847811 := bstep (se 1 (by rfl) ⟨635858, by rfl⟩ : syracuseStep 847811 = 1271717) B1271717
theorem B847827 : Blo 846354 847827 := bstep (se 1 (by rfl) ⟨635870, by rfl⟩ : syracuseStep 847827 = 1271741) B1271741
theorem B1273811 : Blo 846354 1273811 := bstep (se 1 (by rfl) ⟨955358, by rfl⟩ : syracuseStep 1273811 = 1910717) B1910717
theorem B847843 : Blo 846354 847843 := bstep (se 1 (by rfl) ⟨635882, by rfl⟩ : syracuseStep 847843 = 1271765) B1271765
theorem B1273841 : Blo 846354 1273841 := bstep (se 2 (by rfl) ⟨477690, by rfl⟩ : syracuseStep 1273841 = 955381) B955381
theorem B847859 : Blo 846354 847859 := bstep (se 1 (by rfl) ⟨635894, by rfl⟩ : syracuseStep 847859 = 1271789) B1271789
theorem B847875 : Blo 846354 847875 := bstep (se 1 (by rfl) ⟨635906, by rfl⟩ : syracuseStep 847875 = 1271813) B1271813
theorem B1273859 : Blo 846354 1273859 := bstep (se 1 (by rfl) ⟨955394, by rfl⟩ : syracuseStep 1273859 = 1910789) B1910789
theorem B847891 : Blo 846354 847891 := bstep (se 1 (by rfl) ⟨635918, by rfl⟩ : syracuseStep 847891 = 1271837) B1271837
theorem B1273889 : Blo 846354 1273889 := bstep (se 2 (by rfl) ⟨477708, by rfl⟩ : syracuseStep 1273889 = 955417) B955417
theorem B847907 : Blo 846354 847907 := bstep (se 1 (by rfl) ⟨635930, by rfl⟩ : syracuseStep 847907 = 1271861) B1271861
theorem B847923 : Blo 846354 847923 := bstep (se 1 (by rfl) ⟨635942, by rfl⟩ : syracuseStep 847923 = 1271885) B1271885
theorem B1273907 : Blo 846354 1273907 := bstep (se 1 (by rfl) ⟨955430, by rfl⟩ : syracuseStep 1273907 = 1910861) B1910861
theorem B847939 : Blo 846354 847939 := bstep (se 1 (by rfl) ⟨635954, by rfl⟩ : syracuseStep 847939 = 1271909) B1271909
theorem B1273937 : Blo 846354 1273937 := bstep (se 2 (by rfl) ⟨477726, by rfl⟩ : syracuseStep 1273937 = 955453) B955453
theorem B847955 : Blo 846354 847955 := bstep (se 1 (by rfl) ⟨635966, by rfl⟩ : syracuseStep 847955 = 1271933) B1271933
theorem B847971 : Blo 846354 847971 := bstep (se 1 (by rfl) ⟨635978, by rfl⟩ : syracuseStep 847971 = 1271957) B1271957
theorem B1273955 : Blo 846354 1273955 := bstep (se 1 (by rfl) ⟨955466, by rfl⟩ : syracuseStep 1273955 = 1910933) B1910933
theorem B4288625 : Blo 846354 4288625 := bstep (se 2 (by rfl) ⟨1608234, by rfl⟩ : syracuseStep 4288625 = 3216469) B3216469
theorem B847987 : Blo 846354 847987 := bstep (se 1 (by rfl) ⟨635990, by rfl⟩ : syracuseStep 847987 = 1271981) B1271981
theorem B1208449 : Blo 846354 1208449 := bstep (se 2 (by rfl) ⟨453168, by rfl⟩ : syracuseStep 1208449 = 906337) B906337
theorem B1273985 : Blo 846354 1273985 := bstep (se 2 (by rfl) ⟨477744, by rfl⟩ : syracuseStep 1273985 = 955489) B955489
theorem B848003 : Blo 846354 848003 := bstep (se 1 (by rfl) ⟨636002, by rfl⟩ : syracuseStep 848003 = 1272005) B1272005
theorem B848019 : Blo 846354 848019 := bstep (se 1 (by rfl) ⟨636014, by rfl⟩ : syracuseStep 848019 = 1272029) B1272029
theorem B1274003 : Blo 846354 1274003 := bstep (se 1 (by rfl) ⟨955502, by rfl⟩ : syracuseStep 1274003 = 1911005) B1911005
theorem B848035 : Blo 846354 848035 := bstep (se 1 (by rfl) ⟨636026, by rfl⟩ : syracuseStep 848035 = 1272053) B1272053
theorem B1274033 : Blo 846354 1274033 := bstep (se 2 (by rfl) ⟨477762, by rfl⟩ : syracuseStep 1274033 = 955525) B955525
theorem B848051 : Blo 846354 848051 := bstep (se 1 (by rfl) ⟨636038, by rfl⟩ : syracuseStep 848051 = 1272077) B1272077
theorem B848067 : Blo 846354 848067 := bstep (se 1 (by rfl) ⟨636050, by rfl⟩ : syracuseStep 848067 = 1272101) B1272101
theorem B1274051 : Blo 846354 1274051 := bstep (se 1 (by rfl) ⟨955538, by rfl⟩ : syracuseStep 1274051 = 1911077) B1911077
theorem B2420941 : Blo 846354 2420941 := bstep (se 3 (by rfl) ⟨453926, by rfl⟩ : syracuseStep 2420941 = 907853) B907853
theorem B848083 : Blo 846354 848083 := bstep (se 1 (by rfl) ⟨636062, by rfl⟩ : syracuseStep 848083 = 1272125) B1272125
theorem B1274081 : Blo 846354 1274081 := bstep (se 2 (by rfl) ⟨477780, by rfl⟩ : syracuseStep 1274081 = 955561) B955561
theorem B848099 : Blo 846354 848099 := bstep (se 1 (by rfl) ⟨636074, by rfl⟩ : syracuseStep 848099 = 1272149) B1272149
theorem B848115 : Blo 846354 848115 := bstep (se 1 (by rfl) ⟨636086, by rfl⟩ : syracuseStep 848115 = 1272173) B1272173
theorem B1274099 : Blo 846354 1274099 := bstep (se 1 (by rfl) ⟨955574, by rfl⟩ : syracuseStep 1274099 = 1911149) B1911149
theorem B848131 : Blo 846354 848131 := bstep (se 1 (by rfl) ⟨636098, by rfl⟩ : syracuseStep 848131 = 1272197) B1272197
theorem B1274129 : Blo 846354 1274129 := bstep (se 2 (by rfl) ⟨477798, by rfl⟩ : syracuseStep 1274129 = 955597) B955597
theorem B848147 : Blo 846354 848147 := bstep (se 1 (by rfl) ⟨636110, by rfl⟩ : syracuseStep 848147 = 1272221) B1272221
theorem B848163 : Blo 846354 848163 := bstep (se 1 (by rfl) ⟨636122, by rfl⟩ : syracuseStep 848163 = 1272245) B1272245
theorem B1274147 : Blo 846354 1274147 := bstep (se 1 (by rfl) ⟨955610, by rfl⟩ : syracuseStep 1274147 = 1911221) B1911221
theorem B848179 : Blo 846354 848179 := bstep (se 1 (by rfl) ⟨636134, by rfl⟩ : syracuseStep 848179 = 1272269) B1272269
theorem B1274177 : Blo 846354 1274177 := bstep (se 2 (by rfl) ⟨477816, by rfl⟩ : syracuseStep 1274177 = 955633) B955633
theorem B848195 : Blo 846354 848195 := bstep (se 1 (by rfl) ⟨636146, by rfl⟩ : syracuseStep 848195 = 1272293) B1272293
theorem B848211 : Blo 846354 848211 := bstep (se 1 (by rfl) ⟨636158, by rfl⟩ : syracuseStep 848211 = 1272317) B1272317
theorem B1274195 : Blo 846354 1274195 := bstep (se 1 (by rfl) ⟨955646, by rfl⟩ : syracuseStep 1274195 = 1911293) B1911293
theorem B848227 : Blo 846354 848227 := bstep (se 1 (by rfl) ⟨636170, by rfl⟩ : syracuseStep 848227 = 1272341) B1272341
theorem B1274225 : Blo 846354 1274225 := bstep (se 2 (by rfl) ⟨477834, by rfl⟩ : syracuseStep 1274225 = 955669) B955669
theorem B848243 : Blo 846354 848243 := bstep (se 1 (by rfl) ⟨636182, by rfl⟩ : syracuseStep 848243 = 1272365) B1272365
theorem B848259 : Blo 846354 848259 := bstep (se 1 (by rfl) ⟨636194, by rfl⟩ : syracuseStep 848259 = 1272389) B1272389
theorem B1274243 : Blo 846354 1274243 := bstep (se 1 (by rfl) ⟨955682, by rfl⟩ : syracuseStep 1274243 = 1911365) B1911365
theorem B2716049 : Blo 846354 2716049 := bstep (se 2 (by rfl) ⟨1018518, by rfl⟩ : syracuseStep 2716049 = 2037037) B2037037
theorem B848275 : Blo 846354 848275 := bstep (se 1 (by rfl) ⟨636206, by rfl⟩ : syracuseStep 848275 = 1272413) B1272413
theorem B1274273 : Blo 846354 1274273 := bstep (se 2 (by rfl) ⟨477852, by rfl⟩ : syracuseStep 1274273 = 955705) B955705
theorem B848291 : Blo 846354 848291 := bstep (se 1 (by rfl) ⟨636218, by rfl⟩ : syracuseStep 848291 = 1272437) B1272437
theorem B848307 : Blo 846354 848307 := bstep (se 1 (by rfl) ⟨636230, by rfl⟩ : syracuseStep 848307 = 1272461) B1272461
theorem B1274291 : Blo 846354 1274291 := bstep (se 1 (by rfl) ⟨955718, by rfl⟩ : syracuseStep 1274291 = 1911437) B1911437
theorem B848323 : Blo 846354 848323 := bstep (se 1 (by rfl) ⟨636242, by rfl⟩ : syracuseStep 848323 = 1272485) B1272485
theorem B1208785 : Blo 846354 1208785 := bstep (se 2 (by rfl) ⟨453294, by rfl⟩ : syracuseStep 1208785 = 906589) B906589
theorem B1274321 : Blo 846354 1274321 := bstep (se 2 (by rfl) ⟨477870, by rfl⟩ : syracuseStep 1274321 = 955741) B955741
theorem B848339 : Blo 846354 848339 := bstep (se 1 (by rfl) ⟨636254, by rfl⟩ : syracuseStep 848339 = 1272509) B1272509
theorem B848355 : Blo 846354 848355 := bstep (se 1 (by rfl) ⟨636266, by rfl⟩ : syracuseStep 848355 = 1272533) B1272533
theorem B1274339 : Blo 846354 1274339 := bstep (se 1 (by rfl) ⟨955754, by rfl⟩ : syracuseStep 1274339 = 1911509) B1911509
theorem B848371 : Blo 846354 848371 := bstep (se 1 (by rfl) ⟨636278, by rfl⟩ : syracuseStep 848371 = 1272557) B1272557
theorem B1274369 : Blo 846354 1274369 := bstep (se 2 (by rfl) ⟨477888, by rfl⟩ : syracuseStep 1274369 = 955777) B955777
theorem B848387 : Blo 846354 848387 := bstep (se 1 (by rfl) ⟨636290, by rfl⟩ : syracuseStep 848387 = 1272581) B1272581
theorem B848403 : Blo 846354 848403 := bstep (se 1 (by rfl) ⟨636302, by rfl⟩ : syracuseStep 848403 = 1272605) B1272605
theorem B1274387 : Blo 846354 1274387 := bstep (se 1 (by rfl) ⟨955790, by rfl⟩ : syracuseStep 1274387 = 1911581) B1911581
theorem B848419 : Blo 846354 848419 := bstep (se 1 (by rfl) ⟨636314, by rfl⟩ : syracuseStep 848419 = 1272629) B1272629
theorem B1274417 : Blo 846354 1274417 := bstep (se 2 (by rfl) ⟨477906, by rfl⟩ : syracuseStep 1274417 = 955813) B955813
theorem B848435 : Blo 846354 848435 := bstep (se 1 (by rfl) ⟨636326, by rfl⟩ : syracuseStep 848435 = 1272653) B1272653
theorem B848451 : Blo 846354 848451 := bstep (se 1 (by rfl) ⟨636338, by rfl⟩ : syracuseStep 848451 = 1272677) B1272677
theorem B1274435 : Blo 846354 1274435 := bstep (se 1 (by rfl) ⟨955826, by rfl⟩ : syracuseStep 1274435 = 1911653) B1911653
theorem B848467 : Blo 846354 848467 := bstep (se 1 (by rfl) ⟨636350, by rfl⟩ : syracuseStep 848467 = 1272701) B1272701
theorem B1274465 : Blo 846354 1274465 := bstep (se 2 (by rfl) ⟨477924, by rfl⟩ : syracuseStep 1274465 = 955849) B955849
theorem B848483 : Blo 846354 848483 := bstep (se 1 (by rfl) ⟨636362, by rfl⟩ : syracuseStep 848483 = 1272725) B1272725
theorem B848499 : Blo 846354 848499 := bstep (se 1 (by rfl) ⟨636374, by rfl⟩ : syracuseStep 848499 = 1272749) B1272749
theorem B1274483 : Blo 846354 1274483 := bstep (se 1 (by rfl) ⟨955862, by rfl⟩ : syracuseStep 1274483 = 1911725) B1911725
theorem B848515 : Blo 846354 848515 := bstep (se 1 (by rfl) ⟨636386, by rfl⟩ : syracuseStep 848515 = 1272773) B1272773
theorem B1274513 : Blo 846354 1274513 := bstep (se 2 (by rfl) ⟨477942, by rfl⟩ : syracuseStep 1274513 = 955885) B955885
theorem B848531 : Blo 846354 848531 := bstep (se 1 (by rfl) ⟨636398, by rfl⟩ : syracuseStep 848531 = 1272797) B1272797
theorem B848547 : Blo 846354 848547 := bstep (se 1 (by rfl) ⟨636410, by rfl⟩ : syracuseStep 848547 = 1272821) B1272821
theorem B1274531 : Blo 846354 1274531 := bstep (se 1 (by rfl) ⟨955898, by rfl⟩ : syracuseStep 1274531 = 1911797) B1911797
theorem B848563 : Blo 846354 848563 := bstep (se 1 (by rfl) ⟨636422, by rfl⟩ : syracuseStep 848563 = 1272845) B1272845
theorem B1274561 : Blo 846354 1274561 := bstep (se 2 (by rfl) ⟨477960, by rfl⟩ : syracuseStep 1274561 = 955921) B955921
theorem B848579 : Blo 846354 848579 := bstep (se 1 (by rfl) ⟨636434, by rfl⟩ : syracuseStep 848579 = 1272869) B1272869
theorem B848595 : Blo 846354 848595 := bstep (se 1 (by rfl) ⟨636446, by rfl⟩ : syracuseStep 848595 = 1272893) B1272893
theorem B1274579 : Blo 846354 1274579 := bstep (se 1 (by rfl) ⟨955934, by rfl⟩ : syracuseStep 1274579 = 1911869) B1911869
theorem B848611 : Blo 846354 848611 := bstep (se 1 (by rfl) ⟨636458, by rfl⟩ : syracuseStep 848611 = 1272917) B1272917
theorem B1274609 : Blo 846354 1274609 := bstep (se 2 (by rfl) ⟨477978, by rfl⟩ : syracuseStep 1274609 = 955957) B955957
theorem B848627 : Blo 846354 848627 := bstep (se 1 (by rfl) ⟨636470, by rfl⟩ : syracuseStep 848627 = 1272941) B1272941
theorem B848643 : Blo 846354 848643 := bstep (se 1 (by rfl) ⟨636482, by rfl⟩ : syracuseStep 848643 = 1272965) B1272965
theorem B1274627 : Blo 846354 1274627 := bstep (se 1 (by rfl) ⟨955970, by rfl⟩ : syracuseStep 1274627 = 1911941) B1911941
theorem B848659 : Blo 846354 848659 := bstep (se 1 (by rfl) ⟨636494, by rfl⟩ : syracuseStep 848659 = 1272989) B1272989
theorem B1274657 : Blo 846354 1274657 := bstep (se 2 (by rfl) ⟨477996, by rfl⟩ : syracuseStep 1274657 = 955993) B955993
theorem B848675 : Blo 846354 848675 := bstep (se 1 (by rfl) ⟨636506, by rfl⟩ : syracuseStep 848675 = 1273013) B1273013
theorem B848691 : Blo 846354 848691 := bstep (se 1 (by rfl) ⟨636518, by rfl⟩ : syracuseStep 848691 = 1273037) B1273037
theorem B1274675 : Blo 846354 1274675 := bstep (se 1 (by rfl) ⟨956006, by rfl⟩ : syracuseStep 1274675 = 1912013) B1912013
theorem B848707 : Blo 846354 848707 := bstep (se 1 (by rfl) ⟨636530, by rfl⟩ : syracuseStep 848707 = 1273061) B1273061
theorem B1274705 : Blo 846354 1274705 := bstep (se 2 (by rfl) ⟨478014, by rfl⟩ : syracuseStep 1274705 = 956029) B956029
theorem B848723 : Blo 846354 848723 := bstep (se 1 (by rfl) ⟨636542, by rfl⟩ : syracuseStep 848723 = 1273085) B1273085
theorem B848739 : Blo 846354 848739 := bstep (se 1 (by rfl) ⟨636554, by rfl⟩ : syracuseStep 848739 = 1273109) B1273109
theorem B1274723 : Blo 846354 1274723 := bstep (se 1 (by rfl) ⟨956042, by rfl⟩ : syracuseStep 1274723 = 1912085) B1912085
theorem B848755 : Blo 846354 848755 := bstep (se 1 (by rfl) ⟨636566, by rfl⟩ : syracuseStep 848755 = 1273133) B1273133
theorem B1274753 : Blo 846354 1274753 := bstep (se 2 (by rfl) ⟨478032, by rfl⟩ : syracuseStep 1274753 = 956065) B956065
theorem B848771 : Blo 846354 848771 := bstep (se 1 (by rfl) ⟨636578, by rfl⟩ : syracuseStep 848771 = 1273157) B1273157
theorem B848787 : Blo 846354 848787 := bstep (se 1 (by rfl) ⟨636590, by rfl⟩ : syracuseStep 848787 = 1273181) B1273181
theorem B1274771 : Blo 846354 1274771 := bstep (se 1 (by rfl) ⟨956078, by rfl⟩ : syracuseStep 1274771 = 1912157) B1912157
theorem B848803 : Blo 846354 848803 := bstep (se 1 (by rfl) ⟨636602, by rfl⟩ : syracuseStep 848803 = 1273205) B1273205
theorem B1274801 : Blo 846354 1274801 := bstep (se 2 (by rfl) ⟨478050, by rfl⟩ : syracuseStep 1274801 = 956101) B956101
theorem B848819 : Blo 846354 848819 := bstep (se 1 (by rfl) ⟨636614, by rfl⟩ : syracuseStep 848819 = 1273229) B1273229
theorem B848835 : Blo 846354 848835 := bstep (se 1 (by rfl) ⟨636626, by rfl⟩ : syracuseStep 848835 = 1273253) B1273253
theorem B1274819 : Blo 846354 1274819 := bstep (se 1 (by rfl) ⟨956114, by rfl⟩ : syracuseStep 1274819 = 1912229) B1912229
theorem B848851 : Blo 846354 848851 := bstep (se 1 (by rfl) ⟨636638, by rfl⟩ : syracuseStep 848851 = 1273277) B1273277
theorem B1274849 : Blo 846354 1274849 := bstep (se 2 (by rfl) ⟨478068, by rfl⟩ : syracuseStep 1274849 = 956137) B956137
theorem B848867 : Blo 846354 848867 := bstep (se 1 (by rfl) ⟨636650, by rfl⟩ : syracuseStep 848867 = 1273301) B1273301
theorem B848883 : Blo 846354 848883 := bstep (se 1 (by rfl) ⟨636662, by rfl⟩ : syracuseStep 848883 = 1273325) B1273325
theorem B1274867 : Blo 846354 1274867 := bstep (se 1 (by rfl) ⟨956150, by rfl⟩ : syracuseStep 1274867 = 1912301) B1912301
theorem B848899 : Blo 846354 848899 := bstep (se 1 (by rfl) ⟨636674, by rfl⟩ : syracuseStep 848899 = 1273349) B1273349
theorem B1274897 : Blo 846354 1274897 := bstep (se 2 (by rfl) ⟨478086, by rfl⟩ : syracuseStep 1274897 = 956173) B956173
theorem B848915 : Blo 846354 848915 := bstep (se 1 (by rfl) ⟨636686, by rfl⟩ : syracuseStep 848915 = 1273373) B1273373
theorem B1209377 : Blo 846354 1209377 := bstep (se 2 (by rfl) ⟨453516, by rfl⟩ : syracuseStep 1209377 = 907033) B907033
theorem B848931 : Blo 846354 848931 := bstep (se 1 (by rfl) ⟨636698, by rfl⟩ : syracuseStep 848931 = 1273397) B1273397
theorem B1274915 : Blo 846354 1274915 := bstep (se 1 (by rfl) ⟨956186, by rfl⟩ : syracuseStep 1274915 = 1912373) B1912373
theorem B2585645 : Blo 846354 2585645 := bstep (se 3 (by rfl) ⟨484808, by rfl⟩ : syracuseStep 2585645 = 969617) B969617
theorem B848947 : Blo 846354 848947 := bstep (se 1 (by rfl) ⟨636710, by rfl⟩ : syracuseStep 848947 = 1273421) B1273421
theorem B1274945 : Blo 846354 1274945 := bstep (se 2 (by rfl) ⟨478104, by rfl⟩ : syracuseStep 1274945 = 956209) B956209
theorem B848963 : Blo 846354 848963 := bstep (se 1 (by rfl) ⟨636722, by rfl⟩ : syracuseStep 848963 = 1273445) B1273445
theorem B848979 : Blo 846354 848979 := bstep (se 1 (by rfl) ⟨636734, by rfl⟩ : syracuseStep 848979 = 1273469) B1273469
theorem B1274963 : Blo 846354 1274963 := bstep (se 1 (by rfl) ⟨956222, by rfl⟩ : syracuseStep 1274963 = 1912445) B1912445
theorem B848995 : Blo 846354 848995 := bstep (se 1 (by rfl) ⟨636746, by rfl⟩ : syracuseStep 848995 = 1273493) B1273493
theorem B1274993 : Blo 846354 1274993 := bstep (se 2 (by rfl) ⟨478122, by rfl⟩ : syracuseStep 1274993 = 956245) B956245
theorem B849011 : Blo 846354 849011 := bstep (se 1 (by rfl) ⟨636758, by rfl⟩ : syracuseStep 849011 = 1273517) B1273517
theorem B849027 : Blo 846354 849027 := bstep (se 1 (by rfl) ⟨636770, by rfl⟩ : syracuseStep 849027 = 1273541) B1273541
theorem B2946179 : Blo 846354 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B1275011 : Blo 846354 1275011 := bstep (se 1 (by rfl) ⟨956258, by rfl⟩ : syracuseStep 1275011 = 1912517) B1912517
theorem B849043 : Blo 846354 849043 := bstep (se 1 (by rfl) ⟨636782, by rfl⟩ : syracuseStep 849043 = 1273565) B1273565
theorem B1275041 : Blo 846354 1275041 := bstep (se 2 (by rfl) ⟨478140, by rfl⟩ : syracuseStep 1275041 = 956281) B956281
theorem B849059 : Blo 846354 849059 := bstep (se 1 (by rfl) ⟨636794, by rfl⟩ : syracuseStep 849059 = 1273589) B1273589
theorem B849075 : Blo 846354 849075 := bstep (se 1 (by rfl) ⟨636806, by rfl⟩ : syracuseStep 849075 = 1273613) B1273613
theorem B1275059 : Blo 846354 1275059 := bstep (se 1 (by rfl) ⟨956294, by rfl⟩ : syracuseStep 1275059 = 1912589) B1912589
theorem B849091 : Blo 846354 849091 := bstep (se 1 (by rfl) ⟨636818, by rfl⟩ : syracuseStep 849091 = 1273637) B1273637
theorem B1275089 : Blo 846354 1275089 := bstep (se 2 (by rfl) ⟨478158, by rfl⟩ : syracuseStep 1275089 = 956317) B956317
theorem B849107 : Blo 846354 849107 := bstep (se 1 (by rfl) ⟨636830, by rfl⟩ : syracuseStep 849107 = 1273661) B1273661
theorem B849123 : Blo 846354 849123 := bstep (se 1 (by rfl) ⟨636842, by rfl⟩ : syracuseStep 849123 = 1273685) B1273685
theorem B1275107 : Blo 846354 1275107 := bstep (se 1 (by rfl) ⟨956330, by rfl⟩ : syracuseStep 1275107 = 1912661) B1912661
theorem B849139 : Blo 846354 849139 := bstep (se 1 (by rfl) ⟨636854, by rfl⟩ : syracuseStep 849139 = 1273709) B1273709
theorem B1275137 : Blo 846354 1275137 := bstep (se 2 (by rfl) ⟨478176, by rfl⟩ : syracuseStep 1275137 = 956353) B956353
theorem B849155 : Blo 846354 849155 := bstep (se 1 (by rfl) ⟨636866, by rfl⟩ : syracuseStep 849155 = 1273733) B1273733
theorem B849171 : Blo 846354 849171 := bstep (se 1 (by rfl) ⟨636878, by rfl⟩ : syracuseStep 849171 = 1273757) B1273757
theorem B1275155 : Blo 846354 1275155 := bstep (se 1 (by rfl) ⟨956366, by rfl⟩ : syracuseStep 1275155 = 1912733) B1912733
theorem B849187 : Blo 846354 849187 := bstep (se 1 (by rfl) ⟨636890, by rfl⟩ : syracuseStep 849187 = 1273781) B1273781
theorem B2716973 : Blo 846354 2716973 := bstep (se 3 (by rfl) ⟨509432, by rfl⟩ : syracuseStep 2716973 = 1018865) B1018865
theorem B1275185 : Blo 846354 1275185 := bstep (se 2 (by rfl) ⟨478194, by rfl⟩ : syracuseStep 1275185 = 956389) B956389
theorem B849203 : Blo 846354 849203 := bstep (se 1 (by rfl) ⟨636902, by rfl⟩ : syracuseStep 849203 = 1273805) B1273805
theorem B849219 : Blo 846354 849219 := bstep (se 1 (by rfl) ⟨636914, by rfl⟩ : syracuseStep 849219 = 1273829) B1273829
theorem B1275203 : Blo 846354 1275203 := bstep (se 1 (by rfl) ⟨956402, by rfl⟩ : syracuseStep 1275203 = 1912805) B1912805
theorem B849235 : Blo 846354 849235 := bstep (se 1 (by rfl) ⟨636926, by rfl⟩ : syracuseStep 849235 = 1273853) B1273853
theorem B1275233 : Blo 846354 1275233 := bstep (se 2 (by rfl) ⟨478212, by rfl⟩ : syracuseStep 1275233 = 956425) B956425
theorem B849251 : Blo 846354 849251 := bstep (se 1 (by rfl) ⟨636938, by rfl⟩ : syracuseStep 849251 = 1273877) B1273877
theorem B849267 : Blo 846354 849267 := bstep (se 1 (by rfl) ⟨636950, by rfl⟩ : syracuseStep 849267 = 1273901) B1273901
theorem B1275251 : Blo 846354 1275251 := bstep (se 1 (by rfl) ⟨956438, by rfl⟩ : syracuseStep 1275251 = 1912877) B1912877
theorem B849283 : Blo 846354 849283 := bstep (se 1 (by rfl) ⟨636962, by rfl⟩ : syracuseStep 849283 = 1273925) B1273925
theorem B6452621 : Blo 846354 6452621 := bstep (se 3 (by rfl) ⟨1209866, by rfl⟩ : syracuseStep 6452621 = 2419733) B2419733
theorem B1275281 : Blo 846354 1275281 := bstep (se 2 (by rfl) ⟨478230, by rfl⟩ : syracuseStep 1275281 = 956461) B956461
theorem B849299 : Blo 846354 849299 := bstep (se 1 (by rfl) ⟨636974, by rfl⟩ : syracuseStep 849299 = 1273949) B1273949
theorem B849315 : Blo 846354 849315 := bstep (se 1 (by rfl) ⟨636986, by rfl⟩ : syracuseStep 849315 = 1273973) B1273973
theorem B1275299 : Blo 846354 1275299 := bstep (se 1 (by rfl) ⟨956474, by rfl⟩ : syracuseStep 1275299 = 1912949) B1912949
theorem B849331 : Blo 846354 849331 := bstep (se 1 (by rfl) ⟨636998, by rfl⟩ : syracuseStep 849331 = 1273997) B1273997
theorem B1275329 : Blo 846354 1275329 := bstep (se 2 (by rfl) ⟨478248, by rfl⟩ : syracuseStep 1275329 = 956497) B956497
theorem B849347 : Blo 846354 849347 := bstep (se 1 (by rfl) ⟨637010, by rfl⟩ : syracuseStep 849347 = 1274021) B1274021
theorem B849363 : Blo 846354 849363 := bstep (se 1 (by rfl) ⟨637022, by rfl⟩ : syracuseStep 849363 = 1274045) B1274045
theorem B1275347 : Blo 846354 1275347 := bstep (se 1 (by rfl) ⟨956510, by rfl⟩ : syracuseStep 1275347 = 1913021) B1913021
theorem B849379 : Blo 846354 849379 := bstep (se 1 (by rfl) ⟨637034, by rfl⟩ : syracuseStep 849379 = 1274069) B1274069
theorem B2717165 : Blo 846354 2717165 := bstep (se 3 (by rfl) ⟨509468, by rfl⟩ : syracuseStep 2717165 = 1018937) B1018937
theorem B1275377 : Blo 846354 1275377 := bstep (se 2 (by rfl) ⟨478266, by rfl⟩ : syracuseStep 1275377 = 956533) B956533
theorem B849395 : Blo 846354 849395 := bstep (se 1 (by rfl) ⟨637046, by rfl⟩ : syracuseStep 849395 = 1274093) B1274093
theorem B849411 : Blo 846354 849411 := bstep (se 1 (by rfl) ⟨637058, by rfl⟩ : syracuseStep 849411 = 1274117) B1274117
theorem B1275395 : Blo 846354 1275395 := bstep (se 1 (by rfl) ⟨956546, by rfl⟩ : syracuseStep 1275395 = 1913093) B1913093
theorem B849427 : Blo 846354 849427 := bstep (se 1 (by rfl) ⟨637070, by rfl⟩ : syracuseStep 849427 = 1274141) B1274141
theorem B1275425 : Blo 846354 1275425 := bstep (se 2 (by rfl) ⟨478284, by rfl⟩ : syracuseStep 1275425 = 956569) B956569
theorem B4290083 : Blo 846354 4290083 := bstep (se 1 (by rfl) ⟨3217562, by rfl⟩ : syracuseStep 4290083 = 6435125) B6435125
theorem B849443 : Blo 846354 849443 := bstep (se 1 (by rfl) ⟨637082, by rfl⟩ : syracuseStep 849443 = 1274165) B1274165
theorem B849459 : Blo 846354 849459 := bstep (se 1 (by rfl) ⟨637094, by rfl⟩ : syracuseStep 849459 = 1274189) B1274189
theorem B1209907 : Blo 846354 1209907 := bstep (se 1 (by rfl) ⟨907430, by rfl⟩ : syracuseStep 1209907 = 1814861) B1814861
theorem B1275443 : Blo 846354 1275443 := bstep (se 1 (by rfl) ⟨956582, by rfl⟩ : syracuseStep 1275443 = 1913165) B1913165
theorem B849475 : Blo 846354 849475 := bstep (se 1 (by rfl) ⟨637106, by rfl⟩ : syracuseStep 849475 = 1274213) B1274213
theorem B1275473 : Blo 846354 1275473 := bstep (se 2 (by rfl) ⟨478302, by rfl⟩ : syracuseStep 1275473 = 956605) B956605
theorem B849491 : Blo 846354 849491 := bstep (se 1 (by rfl) ⟨637118, by rfl⟩ : syracuseStep 849491 = 1274237) B1274237
theorem B849507 : Blo 846354 849507 := bstep (se 1 (by rfl) ⟨637130, by rfl⟩ : syracuseStep 849507 = 1274261) B1274261
theorem B1275491 : Blo 846354 1275491 := bstep (se 1 (by rfl) ⟨956618, by rfl⟩ : syracuseStep 1275491 = 1913237) B1913237
theorem B849523 : Blo 846354 849523 := bstep (se 1 (by rfl) ⟨637142, by rfl⟩ : syracuseStep 849523 = 1274285) B1274285
theorem B1275521 : Blo 846354 1275521 := bstep (se 2 (by rfl) ⟨478320, by rfl⟩ : syracuseStep 1275521 = 956641) B956641
theorem B849539 : Blo 846354 849539 := bstep (se 1 (by rfl) ⟨637154, by rfl⟩ : syracuseStep 849539 = 1274309) B1274309
theorem B849555 : Blo 846354 849555 := bstep (se 1 (by rfl) ⟨637166, by rfl⟩ : syracuseStep 849555 = 1274333) B1274333
theorem B849571 : Blo 846354 849571 := bstep (se 1 (by rfl) ⟨637178, by rfl⟩ : syracuseStep 849571 = 1274357) B1274357
theorem B849587 : Blo 846354 849587 := bstep (se 1 (by rfl) ⟨637190, by rfl⟩ : syracuseStep 849587 = 1274381) B1274381
theorem B849603 : Blo 846354 849603 := bstep (se 1 (by rfl) ⟨637202, by rfl⟩ : syracuseStep 849603 = 1274405) B1274405
theorem B849619 : Blo 846354 849619 := bstep (se 1 (by rfl) ⟨637214, by rfl⟩ : syracuseStep 849619 = 1274429) B1274429
theorem B849635 : Blo 846354 849635 := bstep (se 1 (by rfl) ⟨637226, by rfl⟩ : syracuseStep 849635 = 1274453) B1274453
theorem B849651 : Blo 846354 849651 := bstep (se 1 (by rfl) ⟨637238, by rfl⟩ : syracuseStep 849651 = 1274477) B1274477
theorem B849667 : Blo 846354 849667 := bstep (se 1 (by rfl) ⟨637250, by rfl⟩ : syracuseStep 849667 = 1274501) B1274501
theorem B849683 : Blo 846354 849683 := bstep (se 1 (by rfl) ⟨637262, by rfl⟩ : syracuseStep 849683 = 1274525) B1274525
theorem B849699 : Blo 846354 849699 := bstep (se 1 (by rfl) ⟨637274, by rfl⟩ : syracuseStep 849699 = 1274549) B1274549
theorem B849715 : Blo 846354 849715 := bstep (se 1 (by rfl) ⟨637286, by rfl⟩ : syracuseStep 849715 = 1274573) B1274573
theorem B849731 : Blo 846354 849731 := bstep (se 1 (by rfl) ⟨637298, by rfl⟩ : syracuseStep 849731 = 1274597) B1274597
theorem B849747 : Blo 846354 849747 := bstep (se 1 (by rfl) ⟨637310, by rfl⟩ : syracuseStep 849747 = 1274621) B1274621
theorem B849763 : Blo 846354 849763 := bstep (se 1 (by rfl) ⟨637322, by rfl⟩ : syracuseStep 849763 = 1274645) B1274645
theorem B849779 : Blo 846354 849779 := bstep (se 1 (by rfl) ⟨637334, by rfl⟩ : syracuseStep 849779 = 1274669) B1274669
theorem B849795 : Blo 846354 849795 := bstep (se 1 (by rfl) ⟨637346, by rfl⟩ : syracuseStep 849795 = 1274693) B1274693
theorem B1210243 : Blo 846354 1210243 := bstep (se 1 (by rfl) ⟨907682, by rfl⟩ : syracuseStep 1210243 = 1815365) B1815365
theorem B849811 : Blo 846354 849811 := bstep (se 1 (by rfl) ⟨637358, by rfl⟩ : syracuseStep 849811 = 1274717) B1274717
theorem B849827 : Blo 846354 849827 := bstep (se 1 (by rfl) ⟨637370, by rfl⟩ : syracuseStep 849827 = 1274741) B1274741
theorem B849843 : Blo 846354 849843 := bstep (se 1 (by rfl) ⟨637382, by rfl⟩ : syracuseStep 849843 = 1274765) B1274765
theorem B849859 : Blo 846354 849859 := bstep (se 1 (by rfl) ⟨637394, by rfl⟩ : syracuseStep 849859 = 1274789) B1274789
theorem B849875 : Blo 846354 849875 := bstep (se 1 (by rfl) ⟨637406, by rfl⟩ : syracuseStep 849875 = 1274813) B1274813
theorem B849891 : Blo 846354 849891 := bstep (se 1 (by rfl) ⟨637418, by rfl⟩ : syracuseStep 849891 = 1274837) B1274837
theorem B849907 : Blo 846354 849907 := bstep (se 1 (by rfl) ⟨637430, by rfl⟩ : syracuseStep 849907 = 1274861) B1274861
theorem B849923 : Blo 846354 849923 := bstep (se 1 (by rfl) ⟨637442, by rfl⟩ : syracuseStep 849923 = 1274885) B1274885
theorem B849939 : Blo 846354 849939 := bstep (se 1 (by rfl) ⟨637454, by rfl⟩ : syracuseStep 849939 = 1274909) B1274909
theorem B849955 : Blo 846354 849955 := bstep (se 1 (by rfl) ⟨637466, by rfl⟩ : syracuseStep 849955 = 1274933) B1274933
theorem B849971 : Blo 846354 849971 := bstep (se 1 (by rfl) ⟨637478, by rfl⟩ : syracuseStep 849971 = 1274957) B1274957
theorem B849987 : Blo 846354 849987 := bstep (se 1 (by rfl) ⟨637490, by rfl⟩ : syracuseStep 849987 = 1274981) B1274981
theorem B850003 : Blo 846354 850003 := bstep (se 1 (by rfl) ⟨637502, by rfl⟩ : syracuseStep 850003 = 1275005) B1275005
theorem B850019 : Blo 846354 850019 := bstep (se 1 (by rfl) ⟨637514, by rfl⟩ : syracuseStep 850019 = 1275029) B1275029
theorem B850035 : Blo 846354 850035 := bstep (se 1 (by rfl) ⟨637526, by rfl⟩ : syracuseStep 850035 = 1275053) B1275053
theorem B850051 : Blo 846354 850051 := bstep (se 1 (by rfl) ⟨637538, by rfl⟩ : syracuseStep 850051 = 1275077) B1275077
theorem B850067 : Blo 846354 850067 := bstep (se 1 (by rfl) ⟨637550, by rfl⟩ : syracuseStep 850067 = 1275101) B1275101
theorem B850083 : Blo 846354 850083 := bstep (se 1 (by rfl) ⟨637562, by rfl⟩ : syracuseStep 850083 = 1275125) B1275125
theorem B850099 : Blo 846354 850099 := bstep (se 1 (by rfl) ⟨637574, by rfl⟩ : syracuseStep 850099 = 1275149) B1275149
theorem B850115 : Blo 846354 850115 := bstep (se 1 (by rfl) ⟨637586, by rfl⟩ : syracuseStep 850115 = 1275173) B1275173
theorem B2291917 : Blo 846354 2291917 := bstep (se 3 (by rfl) ⟨429734, by rfl⟩ : syracuseStep 2291917 = 859469) B859469
theorem B850131 : Blo 846354 850131 := bstep (se 1 (by rfl) ⟨637598, by rfl⟩ : syracuseStep 850131 = 1275197) B1275197
theorem B850147 : Blo 846354 850147 := bstep (se 1 (by rfl) ⟨637610, by rfl⟩ : syracuseStep 850147 = 1275221) B1275221
theorem B850163 : Blo 846354 850163 := bstep (se 1 (by rfl) ⟨637622, by rfl⟩ : syracuseStep 850163 = 1275245) B1275245
theorem B2291971 : Blo 846354 2291971 := bstep (se 1 (by rfl) ⟨1718978, by rfl⟩ : syracuseStep 2291971 = 3437957) B3437957
theorem B850179 : Blo 846354 850179 := bstep (se 1 (by rfl) ⟨637634, by rfl⟩ : syracuseStep 850179 = 1275269) B1275269
theorem B850195 : Blo 846354 850195 := bstep (se 1 (by rfl) ⟨637646, by rfl⟩ : syracuseStep 850195 = 1275293) B1275293
theorem B850211 : Blo 846354 850211 := bstep (se 1 (by rfl) ⟨637658, by rfl⟩ : syracuseStep 850211 = 1275317) B1275317
theorem B850227 : Blo 846354 850227 := bstep (se 1 (by rfl) ⟨637670, by rfl⟩ : syracuseStep 850227 = 1275341) B1275341
theorem B850243 : Blo 846354 850243 := bstep (se 1 (by rfl) ⟨637682, by rfl⟩ : syracuseStep 850243 = 1275365) B1275365
theorem B4290893 : Blo 846354 4290893 := bstep (se 3 (by rfl) ⟨804542, by rfl⟩ : syracuseStep 4290893 = 1609085) B1609085
theorem B850259 : Blo 846354 850259 := bstep (se 1 (by rfl) ⟨637694, by rfl⟩ : syracuseStep 850259 = 1275389) B1275389
theorem B850275 : Blo 846354 850275 := bstep (se 1 (by rfl) ⟨637706, by rfl⟩ : syracuseStep 850275 = 1275413) B1275413
theorem B1309043 : Blo 846354 1309043 := bstep (se 1 (by rfl) ⟨981782, by rfl⟩ : syracuseStep 1309043 = 1963565) B1963565
theorem B850291 : Blo 846354 850291 := bstep (se 1 (by rfl) ⟨637718, by rfl⟩ : syracuseStep 850291 = 1275437) B1275437
theorem B850307 : Blo 846354 850307 := bstep (se 1 (by rfl) ⟨637730, by rfl⟩ : syracuseStep 850307 = 1275461) B1275461
theorem B850323 : Blo 846354 850323 := bstep (se 1 (by rfl) ⟨637742, by rfl⟩ : syracuseStep 850323 = 1275485) B1275485
theorem B850339 : Blo 846354 850339 := bstep (se 1 (by rfl) ⟨637754, by rfl⟩ : syracuseStep 850339 = 1275509) B1275509
theorem B2062883 : Blo 846354 2062883 := bstep (se 1 (by rfl) ⟨1547162, by rfl⟩ : syracuseStep 2062883 = 3094325) B3094325
theorem B1309475 : Blo 846354 1309475 := bstep (se 1 (by rfl) ⟨982106, by rfl⟩ : syracuseStep 1309475 = 1964213) B1964213
theorem B981875 : Blo 846354 981875 := bstep (se 1 (by rfl) ⟨736406, by rfl⟩ : syracuseStep 981875 = 1472813) B1472813
theorem B2718947 : Blo 846354 2718947 := bstep (se 1 (by rfl) ⟨2039210, by rfl⟩ : syracuseStep 2718947 = 4078421) B4078421
theorem B1965379 : Blo 846354 1965379 := bstep (se 1 (by rfl) ⟨1474034, by rfl⟩ : syracuseStep 1965379 = 2948069) B2948069
theorem B6880709 : Blo 846354 6880709 := bstep (se 4 (by rfl) ⟨645066, by rfl⟩ : syracuseStep 6880709 = 1290133) B1290133
theorem B4128241 : Blo 846354 4128241 := bstep (se 2 (by rfl) ⟨1548090, by rfl⟩ : syracuseStep 4128241 = 3096181) B3096181
theorem B4587313 : Blo 846354 4587313 := bstep (se 2 (by rfl) ⟨1720242, by rfl⟩ : syracuseStep 4587313 = 3440485) B3440485
theorem B18579253 : Blo 846354 18579253 := bstep (se 5 (by rfl) ⟨870902, by rfl⟩ : syracuseStep 18579253 = 1741805) B1741805
theorem B4653121 : Blo 846354 4653121 := bstep (se 2 (by rfl) ⟨1744920, by rfl⟩ : syracuseStep 4653121 = 3489841) B3489841
theorem B2720279 : Blo 846354 2720279 := bstep (se 1 (by rfl) ⟨2040209, by rfl⟩ : syracuseStep 2720279 = 4080419) B4080419
theorem B2720587 : Blo 846354 2720587 := bstep (se 1 (by rfl) ⟨2040440, by rfl⟩ : syracuseStep 2720587 = 4080881) B4080881
theorem B918379 : Blo 846354 918379 := bstep (se 1 (by rfl) ⟨688784, by rfl⟩ : syracuseStep 918379 = 1377569) B1377569
theorem B7242797 : Blo 846354 7242797 := bstep (se 3 (by rfl) ⟨1358024, by rfl⟩ : syracuseStep 7242797 = 2716049) B2716049
theorem B1606807 : Blo 846354 1606807 := bstep (se 1 (by rfl) ⟨1205105, by rfl⟩ : syracuseStep 1606807 = 2410211) B2410211
theorem B3868249 : Blo 846354 3868249 := bstep (se 2 (by rfl) ⟨1450593, by rfl⟩ : syracuseStep 3868249 = 2901187) B2901187
theorem B4294295 : Blo 846354 4294295 := bstep (se 1 (by rfl) ⟨3220721, by rfl⟩ : syracuseStep 4294295 = 6441443) B6441443
theorem B952267 : Blo 846354 952267 := bstep (se 1 (by rfl) ⟨714200, by rfl⟩ : syracuseStep 952267 = 1428401) B1428401
theorem B1607627 : Blo 846354 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B1607681 : Blo 846354 1607681 := bstep (se 2 (by rfl) ⟨602880, by rfl⟩ : syracuseStep 1607681 = 1205761) B1205761
theorem B952375 : Blo 846354 952375 := bstep (se 1 (by rfl) ⟨714281, by rfl⟩ : syracuseStep 952375 = 1428563) B1428563
theorem B952555 : Blo 846354 952555 := bstep (se 1 (by rfl) ⟨714416, by rfl⟩ : syracuseStep 952555 = 1428833) B1428833
theorem B6195491 : Blo 846354 6195491 := bstep (se 1 (by rfl) ⟨4646618, by rfl⟩ : syracuseStep 6195491 = 9293237) B9293237
theorem B952663 : Blo 846354 952663 := bstep (se 1 (by rfl) ⟨714497, by rfl⟩ : syracuseStep 952663 = 1428995) B1428995
theorem B10848613 : Blo 846354 10848613 := bstep (se 4 (by rfl) ⟨1017057, by rfl⟩ : syracuseStep 10848613 = 2034115) B2034115
theorem B1018327 : Blo 846354 1018327 := bstep (se 1 (by rfl) ⟨763745, by rfl⟩ : syracuseStep 1018327 = 1527491) B1527491
theorem B3213827 : Blo 846354 3213827 := bstep (se 1 (by rfl) ⟨2410370, by rfl⟩ : syracuseStep 3213827 = 4820741) B4820741
theorem B952843 : Blo 846354 952843 := bstep (se 1 (by rfl) ⟨714632, by rfl⟩ : syracuseStep 952843 = 1429265) B1429265
theorem B2722355 : Blo 846354 2722355 := bstep (se 1 (by rfl) ⟨2041766, by rfl⟩ : syracuseStep 2722355 = 4083533) B4083533
theorem B952951 : Blo 846354 952951 := bstep (se 1 (by rfl) ⟨714713, by rfl⟩ : syracuseStep 952951 = 1429427) B1429427
theorem B7735985 : Blo 846354 7735985 := bstep (se 2 (by rfl) ⟨2900994, by rfl⟩ : syracuseStep 7735985 = 5801989) B5801989
theorem B953131 : Blo 846354 953131 := bstep (se 1 (by rfl) ⟨714848, by rfl⟩ : syracuseStep 953131 = 1429697) B1429697
theorem B2034521 : Blo 846354 2034521 := bstep (se 2 (by rfl) ⟨762945, by rfl⟩ : syracuseStep 2034521 = 1525891) B1525891
theorem B15928163 : Blo 846354 15928163 := bstep (se 1 (by rfl) ⟨11946122, by rfl⟩ : syracuseStep 15928163 = 23892245) B23892245
theorem B953239 : Blo 846354 953239 := bstep (se 1 (by rfl) ⟨714929, by rfl⟩ : syracuseStep 953239 = 1429859) B1429859
theorem B1608599 : Blo 846354 1608599 := bstep (se 1 (by rfl) ⟨1206449, by rfl⟩ : syracuseStep 1608599 = 2412899) B2412899
theorem B1018903 : Blo 846354 1018903 := bstep (se 1 (by rfl) ⟨764177, by rfl⟩ : syracuseStep 1018903 = 1528355) B1528355
theorem B953419 : Blo 846354 953419 := bstep (se 1 (by rfl) ⟨715064, by rfl⟩ : syracuseStep 953419 = 1430129) B1430129
theorem B3050585 : Blo 846354 3050585 := bstep (se 2 (by rfl) ⟨1143969, by rfl⟩ : syracuseStep 3050585 = 2287939) B2287939
theorem B953527 : Blo 846354 953527 := bstep (se 1 (by rfl) ⟨715145, by rfl⟩ : syracuseStep 953527 = 1430291) B1430291
theorem B6524225 : Blo 846354 6524225 := bstep (se 2 (by rfl) ⟨2446584, by rfl⟩ : syracuseStep 6524225 = 4893169) B4893169
theorem B953707 : Blo 846354 953707 := bstep (se 1 (by rfl) ⟨715280, by rfl⟩ : syracuseStep 953707 = 1430561) B1430561
theorem B1609139 : Blo 846354 1609139 := bstep (se 1 (by rfl) ⟨1206854, by rfl⟩ : syracuseStep 1609139 = 2413709) B2413709
theorem B953815 : Blo 846354 953815 := bstep (se 1 (by rfl) ⟨715361, by rfl⟩ : syracuseStep 953815 = 1430723) B1430723
theorem B2035289 : Blo 846354 2035289 := bstep (se 2 (by rfl) ⟨763233, by rfl⟩ : syracuseStep 2035289 = 1526467) B1526467
theorem B953995 : Blo 846354 953995 := bstep (se 1 (by rfl) ⟨715496, by rfl⟩ : syracuseStep 953995 = 1430993) B1430993
theorem B6524621 : Blo 846354 6524621 := bstep (se 3 (by rfl) ⟨1223366, by rfl⟩ : syracuseStep 6524621 = 2446733) B2446733
theorem B1904345 : Blo 846354 1904345 := bstep (se 2 (by rfl) ⟨714129, by rfl⟩ : syracuseStep 1904345 = 1428259) B1428259
theorem B954103 : Blo 846354 954103 := bstep (se 1 (by rfl) ⟨715577, by rfl⟩ : syracuseStep 954103 = 1431155) B1431155
theorem B1904435 : Blo 846354 1904435 := bstep (se 1 (by rfl) ⟨1428326, by rfl⟩ : syracuseStep 1904435 = 2856653) B2856653
theorem B2723635 : Blo 846354 2723635 := bstep (se 1 (by rfl) ⟨2042726, by rfl⟩ : syracuseStep 2723635 = 4085453) B4085453
theorem B1904471 : Blo 846354 1904471 := bstep (se 1 (by rfl) ⟨1428353, by rfl⟩ : syracuseStep 1904471 = 2856707) B2856707
theorem B1609625 : Blo 846354 1609625 := bstep (se 2 (by rfl) ⟨603609, by rfl⟩ : syracuseStep 1609625 = 1207219) B1207219
theorem B954283 : Blo 846354 954283 := bstep (se 1 (by rfl) ⟨715712, by rfl⟩ : syracuseStep 954283 = 1431425) B1431425
theorem B7245773 : Blo 846354 7245773 := bstep (se 3 (by rfl) ⟨1358582, by rfl⟩ : syracuseStep 7245773 = 2717165) B2717165
theorem B1904651 : Blo 846354 1904651 := bstep (se 1 (by rfl) ⟨1428488, by rfl⟩ : syracuseStep 1904651 = 2856977) B2856977
theorem B954391 : Blo 846354 954391 := bstep (se 1 (by rfl) ⟨715793, by rfl⟩ : syracuseStep 954391 = 1431587) B1431587
theorem B1904705 : Blo 846354 1904705 := bstep (se 2 (by rfl) ⟨714264, by rfl⟩ : syracuseStep 1904705 = 1428529) B1428529
theorem B5443685 : Blo 846354 5443685 := bstep (se 4 (by rfl) ⟨510345, by rfl⟩ : syracuseStep 5443685 = 1020691) B1020691
theorem B954571 : Blo 846354 954571 := bstep (se 1 (by rfl) ⟨715928, by rfl⟩ : syracuseStep 954571 = 1431857) B1431857
theorem B2298059 : Blo 846354 2298059 := bstep (se 1 (by rfl) ⟨1723544, by rfl⟩ : syracuseStep 2298059 = 3447089) B3447089
theorem B1904921 : Blo 846354 1904921 := bstep (se 2 (by rfl) ⟨714345, by rfl⟩ : syracuseStep 1904921 = 1428691) B1428691
theorem B954679 : Blo 846354 954679 := bstep (se 1 (by rfl) ⟨716009, by rfl⟩ : syracuseStep 954679 = 1432019) B1432019
theorem B3051865 : Blo 846354 3051865 := bstep (se 2 (by rfl) ⟨1144449, by rfl⟩ : syracuseStep 3051865 = 2288899) B2288899
theorem B1905011 : Blo 846354 1905011 := bstep (se 1 (by rfl) ⟨1428758, by rfl⟩ : syracuseStep 1905011 = 2857517) B2857517
theorem B1905047 : Blo 846354 1905047 := bstep (se 1 (by rfl) ⟨1428785, by rfl⟩ : syracuseStep 1905047 = 2857571) B2857571
theorem B6623639 : Blo 846354 6623639 := bstep (se 1 (by rfl) ⟨4967729, by rfl⟩ : syracuseStep 6623639 = 9935459) B9935459
theorem B954859 : Blo 846354 954859 := bstep (se 1 (by rfl) ⟨716144, by rfl⟩ : syracuseStep 954859 = 1432289) B1432289
theorem B1905227 : Blo 846354 1905227 := bstep (se 1 (by rfl) ⟨1428920, by rfl⟩ : syracuseStep 1905227 = 2857841) B2857841
theorem B954967 : Blo 846354 954967 := bstep (se 1 (by rfl) ⟨716225, by rfl⟩ : syracuseStep 954967 = 1432451) B1432451
theorem B1905281 : Blo 846354 1905281 := bstep (se 2 (by rfl) ⟨714480, by rfl⟩ : syracuseStep 1905281 = 1428961) B1428961
theorem B5804723 : Blo 846354 5804723 := bstep (se 1 (by rfl) ⟨4353542, by rfl⟩ : syracuseStep 5804723 = 8707085) B8707085
theorem B955147 : Blo 846354 955147 := bstep (se 1 (by rfl) ⟨716360, by rfl⟩ : syracuseStep 955147 = 1432721) B1432721
theorem B1905497 : Blo 846354 1905497 := bstep (se 2 (by rfl) ⟨714561, by rfl⟩ : syracuseStep 1905497 = 1429123) B1429123
theorem B955255 : Blo 846354 955255 := bstep (se 1 (by rfl) ⟨716441, by rfl⟩ : syracuseStep 955255 = 1432883) B1432883
theorem B6886295 : Blo 846354 6886295 := bstep (se 1 (by rfl) ⟨5164721, by rfl⟩ : syracuseStep 6886295 = 10329443) B10329443
theorem B1905587 : Blo 846354 1905587 := bstep (se 1 (by rfl) ⟨1429190, by rfl⟩ : syracuseStep 1905587 = 2858381) B2858381
theorem B1905623 : Blo 846354 1905623 := bstep (se 1 (by rfl) ⟨1429217, by rfl⟩ : syracuseStep 1905623 = 2858435) B2858435
theorem B955435 : Blo 846354 955435 := bstep (se 1 (by rfl) ⟨716576, by rfl⟩ : syracuseStep 955435 = 1433153) B1433153
theorem B4297859 : Blo 846354 4297859 := bstep (se 1 (by rfl) ⟨3223394, by rfl⟩ : syracuseStep 4297859 = 6446789) B6446789
theorem B1905803 : Blo 846354 1905803 := bstep (se 1 (by rfl) ⟨1429352, by rfl⟩ : syracuseStep 1905803 = 2858705) B2858705
theorem B955543 : Blo 846354 955543 := bstep (se 1 (by rfl) ⟨716657, by rfl⟩ : syracuseStep 955543 = 1433315) B1433315
theorem B1905857 : Blo 846354 1905857 := bstep (se 2 (by rfl) ⟨714696, by rfl⟩ : syracuseStep 1905857 = 1429393) B1429393
theorem B1611083 : Blo 846354 1611083 := bstep (se 1 (by rfl) ⟨1208312, by rfl⟩ : syracuseStep 1611083 = 2416625) B2416625
theorem B955723 : Blo 846354 955723 := bstep (se 1 (by rfl) ⟨716792, by rfl⟩ : syracuseStep 955723 = 1433585) B1433585
theorem B2692445 : Blo 846354 2692445 := bstep (se 3 (by rfl) ⟨504833, by rfl⟩ : syracuseStep 2692445 = 1009667) B1009667
theorem B1906073 : Blo 846354 1906073 := bstep (se 2 (by rfl) ⟨714777, by rfl⟩ : syracuseStep 1906073 = 1429555) B1429555
theorem B1807795 : Blo 846354 1807795 := bstep (se 1 (by rfl) ⟨1355846, by rfl⟩ : syracuseStep 1807795 = 2711693) B2711693
theorem B955831 : Blo 846354 955831 := bstep (se 1 (by rfl) ⟨716873, by rfl⟩ : syracuseStep 955831 = 1433747) B1433747
theorem B1906163 : Blo 846354 1906163 := bstep (se 1 (by rfl) ⟨1429622, by rfl⟩ : syracuseStep 1906163 = 2859245) B2859245
theorem B1611265 : Blo 846354 1611265 := bstep (se 2 (by rfl) ⟨604224, by rfl⟩ : syracuseStep 1611265 = 1208449) B1208449
theorem B1906199 : Blo 846354 1906199 := bstep (se 1 (by rfl) ⟨1429649, by rfl⟩ : syracuseStep 1906199 = 2859299) B2859299
theorem B3216941 : Blo 846354 3216941 := bstep (se 3 (by rfl) ⟨603176, by rfl⟩ : syracuseStep 3216941 = 1206353) B1206353
theorem B956011 : Blo 846354 956011 := bstep (se 1 (by rfl) ⟨717008, by rfl⟩ : syracuseStep 956011 = 1434017) B1434017
theorem B2856599 : Blo 846354 2856599 := bstep (se 1 (by rfl) ⟨2142449, by rfl⟩ : syracuseStep 2856599 = 4284899) B4284899
theorem B1906379 : Blo 846354 1906379 := bstep (se 1 (by rfl) ⟨1429784, by rfl⟩ : syracuseStep 1906379 = 2859569) B2859569
theorem B956119 : Blo 846354 956119 := bstep (se 1 (by rfl) ⟨717089, by rfl⟩ : syracuseStep 956119 = 1434179) B1434179
theorem B1906433 : Blo 846354 1906433 := bstep (se 2 (by rfl) ⟨714912, by rfl⟩ : syracuseStep 1906433 = 1429825) B1429825
theorem B1808257 : Blo 846354 1808257 := bstep (se 2 (by rfl) ⟨678096, by rfl⟩ : syracuseStep 1808257 = 1356193) B1356193
theorem B956299 : Blo 846354 956299 := bstep (se 1 (by rfl) ⟨717224, by rfl⟩ : syracuseStep 956299 = 1434449) B1434449
theorem B1611713 : Blo 846354 1611713 := bstep (se 2 (by rfl) ⟨604392, by rfl⟩ : syracuseStep 1611713 = 1208785) B1208785
theorem B1906649 : Blo 846354 1906649 := bstep (se 2 (by rfl) ⟨714993, by rfl⟩ : syracuseStep 1906649 = 1429987) B1429987
theorem B956407 : Blo 846354 956407 := bstep (se 1 (by rfl) ⟨717305, by rfl⟩ : syracuseStep 956407 = 1434611) B1434611
theorem B1906739 : Blo 846354 1906739 := bstep (se 1 (by rfl) ⟨1430054, by rfl⟩ : syracuseStep 1906739 = 2860109) B2860109
theorem B1906775 : Blo 846354 1906775 := bstep (se 1 (by rfl) ⟨1430081, by rfl⟩ : syracuseStep 1906775 = 2860163) B2860163
theorem B956587 : Blo 846354 956587 := bstep (se 1 (by rfl) ⟨717440, by rfl⟩ : syracuseStep 956587 = 1434881) B1434881
theorem B2857139 : Blo 846354 2857139 := bstep (se 1 (by rfl) ⟨2142854, by rfl⟩ : syracuseStep 2857139 = 4285709) B4285709
theorem B3053771 : Blo 846354 3053771 := bstep (se 1 (by rfl) ⟨2290328, by rfl⟩ : syracuseStep 3053771 = 4580657) B4580657
theorem B1906955 : Blo 846354 1906955 := bstep (se 1 (by rfl) ⟨1430216, by rfl⟩ : syracuseStep 1906955 = 2860433) B2860433
theorem B1612055 : Blo 846354 1612055 := bstep (se 1 (by rfl) ⟨1209041, by rfl⟩ : syracuseStep 1612055 = 2418083) B2418083
theorem B7346467 : Blo 846354 7346467 := bstep (se 1 (by rfl) ⟨5509850, by rfl⟩ : syracuseStep 7346467 = 11019701) B11019701
theorem B3217715 : Blo 846354 3217715 := bstep (se 1 (by rfl) ⟨2413286, by rfl⟩ : syracuseStep 3217715 = 4826573) B4826573
theorem B1907009 : Blo 846354 1907009 := bstep (se 2 (by rfl) ⟨715128, by rfl⟩ : syracuseStep 1907009 = 1430257) B1430257
theorem B9181505 : Blo 846354 9181505 := bstep (se 2 (by rfl) ⟨3443064, by rfl⟩ : syracuseStep 9181505 = 6886129) B6886129
theorem B23239061 : Blo 846354 23239061 := bstep (se 6 (by rfl) ⟨544665, by rfl⟩ : syracuseStep 23239061 = 1089331) B1089331
theorem B2857409 : Blo 846354 2857409 := bstep (se 2 (by rfl) ⟨1071528, by rfl⟩ : syracuseStep 2857409 = 2143057) B2143057
theorem B1907225 : Blo 846354 1907225 := bstep (se 2 (by rfl) ⟨715209, by rfl⟩ : syracuseStep 1907225 = 1430419) B1430419
theorem B1808983 : Blo 846354 1808983 := bstep (se 1 (by rfl) ⟨1356737, by rfl⟩ : syracuseStep 1808983 = 2713475) B2713475
theorem B1907315 : Blo 846354 1907315 := bstep (se 1 (by rfl) ⟨1430486, by rfl⟩ : syracuseStep 1907315 = 2860973) B2860973
theorem B1907351 : Blo 846354 1907351 := bstep (se 1 (by rfl) ⟨1430513, by rfl⟩ : syracuseStep 1907351 = 2861027) B2861027
theorem B1907531 : Blo 846354 1907531 := bstep (se 1 (by rfl) ⟨1430648, by rfl⟩ : syracuseStep 1907531 = 2861297) B2861297
theorem B1907585 : Blo 846354 1907585 := bstep (se 2 (by rfl) ⟨715344, by rfl⟩ : syracuseStep 1907585 = 1430689) B1430689
theorem B1612723 : Blo 846354 1612723 := bstep (se 1 (by rfl) ⟨1209542, by rfl⟩ : syracuseStep 1612723 = 2419085) B2419085
theorem B2857949 : Blo 846354 2857949 := bstep (se 3 (by rfl) ⟨535865, by rfl⟩ : syracuseStep 2857949 = 1071731) B1071731
theorem B1088587 : Blo 846354 1088587 := bstep (se 1 (by rfl) ⟨816440, by rfl⟩ : syracuseStep 1088587 = 1632881) B1632881
theorem B1907801 : Blo 846354 1907801 := bstep (se 2 (by rfl) ⟨715425, by rfl⟩ : syracuseStep 1907801 = 1430851) B1430851
theorem B4824157 : Blo 846354 4824157 := bstep (se 3 (by rfl) ⟨904529, by rfl⟩ : syracuseStep 4824157 = 1809059) B1809059
theorem B1907891 : Blo 846354 1907891 := bstep (se 1 (by rfl) ⟨1430918, by rfl⟩ : syracuseStep 1907891 = 2861837) B2861837
theorem B1907927 : Blo 846354 1907927 := bstep (se 1 (by rfl) ⟨1430945, by rfl⟩ : syracuseStep 1907927 = 2861891) B2861891
theorem B1613171 : Blo 846354 1613171 := bstep (se 1 (by rfl) ⟨1209878, by rfl⟩ : syracuseStep 1613171 = 2419757) B2419757
theorem B1809803 : Blo 846354 1809803 := bstep (se 1 (by rfl) ⟨1357352, by rfl⟩ : syracuseStep 1809803 = 2714705) B2714705
theorem B1908107 : Blo 846354 1908107 := bstep (se 1 (by rfl) ⟨1431080, by rfl⟩ : syracuseStep 1908107 = 2862161) B2862161
theorem B3480983 : Blo 846354 3480983 := bstep (se 1 (by rfl) ⟨2610737, by rfl⟩ : syracuseStep 3480983 = 5221475) B5221475
theorem B1613209 : Blo 846354 1613209 := bstep (se 2 (by rfl) ⟨604953, by rfl⟩ : syracuseStep 1613209 = 1209907) B1209907
theorem B1908161 : Blo 846354 1908161 := bstep (se 2 (by rfl) ⟨715560, by rfl⟩ : syracuseStep 1908161 = 1431121) B1431121
theorem B61971925 : Blo 846354 61971925 := bstep (se 7 (by rfl) ⟨726233, by rfl⟩ : syracuseStep 61971925 = 1452467) B1452467
theorem B1449623 : Blo 846354 1449623 := bstep (se 1 (by rfl) ⟨1087217, by rfl⟩ : syracuseStep 1449623 = 2174435) B2174435
theorem B1908377 : Blo 846354 1908377 := bstep (se 2 (by rfl) ⟨715641, by rfl⟩ : syracuseStep 1908377 = 1431283) B1431283
theorem B1908467 : Blo 846354 1908467 := bstep (se 1 (by rfl) ⟨1431350, by rfl⟩ : syracuseStep 1908467 = 2862701) B2862701
theorem B3219203 : Blo 846354 3219203 := bstep (se 1 (by rfl) ⟨2414402, by rfl⟩ : syracuseStep 3219203 = 4828805) B4828805
theorem B2203415 : Blo 846354 2203415 := bstep (se 1 (by rfl) ⟨1652561, by rfl⟩ : syracuseStep 2203415 = 3305123) B3305123
theorem B1908503 : Blo 846354 1908503 := bstep (se 1 (by rfl) ⟨1431377, by rfl⟩ : syracuseStep 1908503 = 2862755) B2862755
theorem B859927 : Blo 846354 859927 := bstep (se 1 (by rfl) ⟨644945, by rfl⟩ : syracuseStep 859927 = 1289891) B1289891
theorem B2039575 : Blo 846354 2039575 := bstep (se 1 (by rfl) ⟨1529681, by rfl⟩ : syracuseStep 2039575 = 3059363) B3059363
theorem B1613657 : Blo 846354 1613657 := bstep (se 2 (by rfl) ⟨605121, by rfl⟩ : syracuseStep 1613657 = 1210243) B1210243
theorem B1908683 : Blo 846354 1908683 := bstep (se 1 (by rfl) ⟨1431512, by rfl⟩ : syracuseStep 1908683 = 2863025) B2863025
theorem B1908737 : Blo 846354 1908737 := bstep (se 2 (by rfl) ⟨715776, by rfl⟩ : syracuseStep 1908737 = 1431553) B1431553
theorem B2859083 : Blo 846354 2859083 := bstep (se 1 (by rfl) ⟨2144312, by rfl⟩ : syracuseStep 2859083 = 4288625) B4288625
theorem B3219659 : Blo 846354 3219659 := bstep (se 1 (by rfl) ⟨2414744, by rfl⟩ : syracuseStep 3219659 = 4829489) B4829489
theorem B1810649 : Blo 846354 1810649 := bstep (se 2 (by rfl) ⟨678993, by rfl⟩ : syracuseStep 1810649 = 1357987) B1357987
theorem B1908953 : Blo 846354 1908953 := bstep (se 2 (by rfl) ⟨715857, by rfl⟩ : syracuseStep 1908953 = 1431715) B1431715
theorem B3055889 : Blo 846354 3055889 := bstep (se 2 (by rfl) ⟨1145958, by rfl⟩ : syracuseStep 3055889 = 2291917) B2291917
theorem B1909043 : Blo 846354 1909043 := bstep (se 1 (by rfl) ⟨1431782, by rfl⟩ : syracuseStep 1909043 = 2863565) B2863565
theorem B1909079 : Blo 846354 1909079 := bstep (se 1 (by rfl) ⟨1431809, by rfl⟩ : syracuseStep 1909079 = 2863619) B2863619
theorem B2859353 : Blo 846354 2859353 := bstep (se 2 (by rfl) ⟨1072257, by rfl⟩ : syracuseStep 2859353 = 2144515) B2144515
theorem B3055961 : Blo 846354 3055961 := bstep (se 2 (by rfl) ⟨1145985, by rfl⟩ : syracuseStep 3055961 = 2291971) B2291971
theorem B3219857 : Blo 846354 3219857 := bstep (se 2 (by rfl) ⟨1207446, by rfl⟩ : syracuseStep 3219857 = 2414893) B2414893
theorem B6431237 : Blo 846354 6431237 := bstep (se 4 (by rfl) ⟨602928, by rfl⟩ : syracuseStep 6431237 = 1205857) B1205857
theorem B1909259 : Blo 846354 1909259 := bstep (se 1 (by rfl) ⟨1431944, by rfl⟩ : syracuseStep 1909259 = 2863889) B2863889
theorem B1909313 : Blo 846354 1909313 := bstep (se 2 (by rfl) ⟨715992, by rfl⟩ : syracuseStep 1909313 = 1431985) B1431985
theorem B4072153 : Blo 846354 4072153 := bstep (se 2 (by rfl) ⟨1527057, by rfl⟩ : syracuseStep 4072153 = 3054115) B3054115
theorem B4301585 : Blo 846354 4301585 := bstep (se 2 (by rfl) ⟨1613094, by rfl⟩ : syracuseStep 4301585 = 3226189) B3226189
theorem B1909529 : Blo 846354 1909529 := bstep (se 2 (by rfl) ⟨716073, by rfl⟩ : syracuseStep 1909529 = 1432147) B1432147
theorem B5808941 : Blo 846354 5808941 := bstep (se 3 (by rfl) ⟨1089176, by rfl⟩ : syracuseStep 5808941 = 2178353) B2178353
theorem B1811315 : Blo 846354 1811315 := bstep (se 1 (by rfl) ⟨1358486, by rfl⟩ : syracuseStep 1811315 = 2716973) B2716973
theorem B1909619 : Blo 846354 1909619 := bstep (se 1 (by rfl) ⟨1432214, by rfl⟩ : syracuseStep 1909619 = 2864429) B2864429
theorem B1909655 : Blo 846354 1909655 := bstep (se 1 (by rfl) ⟨1432241, by rfl⟩ : syracuseStep 1909655 = 2864483) B2864483
theorem B4301747 : Blo 846354 4301747 := bstep (se 1 (by rfl) ⟨3226310, by rfl⟩ : syracuseStep 4301747 = 6452621) B6452621
theorem B2860055 : Blo 846354 2860055 := bstep (se 1 (by rfl) ⟨2145041, by rfl⟩ : syracuseStep 2860055 = 4290083) B4290083
theorem B1909835 : Blo 846354 1909835 := bstep (se 1 (by rfl) ⟨1432376, by rfl⟩ : syracuseStep 1909835 = 2864753) B2864753
theorem B1287257 : Blo 846354 1287257 := bstep (se 2 (by rfl) ⟨482721, by rfl⟩ : syracuseStep 1287257 = 965443) B965443
theorem B1909889 : Blo 846354 1909889 := bstep (se 2 (by rfl) ⟨716208, by rfl⟩ : syracuseStep 1909889 = 1432417) B1432417
theorem B3220631 : Blo 846354 3220631 := bstep (se 1 (by rfl) ⟨2415473, by rfl⟩ : syracuseStep 3220631 = 4830947) B4830947
theorem B10888343 : Blo 846354 10888343 := bstep (se 1 (by rfl) ⟨8166257, by rfl⟩ : syracuseStep 10888343 = 16332515) B16332515
theorem B1910105 : Blo 846354 1910105 := bstep (se 2 (by rfl) ⟨716289, by rfl⟩ : syracuseStep 1910105 = 1432579) B1432579
theorem B3220829 : Blo 846354 3220829 := bstep (se 3 (by rfl) ⟨603905, by rfl⟩ : syracuseStep 3220829 = 1207811) B1207811
theorem B1910195 : Blo 846354 1910195 := bstep (se 1 (by rfl) ⟨1432646, by rfl⟩ : syracuseStep 1910195 = 2865293) B2865293
theorem B1910231 : Blo 846354 1910231 := bstep (se 1 (by rfl) ⟨1432673, by rfl⟩ : syracuseStep 1910231 = 2865347) B2865347
theorem B2860595 : Blo 846354 2860595 := bstep (se 1 (by rfl) ⟨2145446, by rfl⟩ : syracuseStep 2860595 = 4290893) B4290893
theorem B1910411 : Blo 846354 1910411 := bstep (se 1 (by rfl) ⟨1432808, by rfl⟩ : syracuseStep 1910411 = 2865617) B2865617
theorem B1910465 : Blo 846354 1910465 := bstep (se 2 (by rfl) ⟨716424, by rfl⟩ : syracuseStep 1910465 = 1432849) B1432849
theorem B8726221 : Blo 846354 8726221 := bstep (se 3 (by rfl) ⟨1636166, by rfl⟩ : syracuseStep 8726221 = 3272333) B3272333
theorem B2860865 : Blo 846354 2860865 := bstep (se 2 (by rfl) ⟨1072824, by rfl⟩ : syracuseStep 2860865 = 2145649) B2145649
theorem B1812289 : Blo 846354 1812289 := bstep (se 2 (by rfl) ⟨679608, by rfl⟩ : syracuseStep 1812289 = 1359217) B1359217
theorem B1910681 : Blo 846354 1910681 := bstep (se 2 (by rfl) ⟨716505, by rfl⟩ : syracuseStep 1910681 = 1433011) B1433011
theorem B1910771 : Blo 846354 1910771 := bstep (se 1 (by rfl) ⟨1433078, by rfl⟩ : syracuseStep 1910771 = 2866157) B2866157
theorem B1910807 : Blo 846354 1910807 := bstep (se 1 (by rfl) ⟨1433105, by rfl⟩ : syracuseStep 1910807 = 2866211) B2866211
theorem B1812545 : Blo 846354 1812545 := bstep (se 2 (by rfl) ⟨679704, by rfl⟩ : syracuseStep 1812545 = 1359409) B1359409
theorem B1812631 : Blo 846354 1812631 := bstep (se 1 (by rfl) ⟨1359473, by rfl⟩ : syracuseStep 1812631 = 2718947) B2718947
theorem B17410229 : Blo 846354 17410229 := bstep (se 5 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 17410229 = 1632209) B1632209
theorem B1910987 : Blo 846354 1910987 := bstep (se 1 (by rfl) ⟨1433240, by rfl⟩ : syracuseStep 1910987 = 2866481) B2866481
theorem B1911041 : Blo 846354 1911041 := bstep (se 2 (by rfl) ⟨716640, by rfl⟩ : syracuseStep 1911041 = 1433281) B1433281
theorem B15444229 : Blo 846354 15444229 := bstep (se 4 (by rfl) ⟨1447896, by rfl⟩ : syracuseStep 15444229 = 2895793) B2895793
theorem B2861405 : Blo 846354 2861405 := bstep (se 3 (by rfl) ⟨536513, by rfl⟩ : syracuseStep 2861405 = 1073027) B1073027
theorem B1911257 : Blo 846354 1911257 := bstep (se 2 (by rfl) ⟨716721, by rfl⟩ : syracuseStep 1911257 = 1433443) B1433443
theorem B5220881 : Blo 846354 5220881 := bstep (se 2 (by rfl) ⟨1957830, by rfl⟩ : syracuseStep 5220881 = 3915661) B3915661
theorem B1911347 : Blo 846354 1911347 := bstep (se 1 (by rfl) ⟨1433510, by rfl⟩ : syracuseStep 1911347 = 2867021) B2867021
theorem B2042419 : Blo 846354 2042419 := bstep (se 1 (by rfl) ⟨1531814, by rfl⟩ : syracuseStep 2042419 = 3063629) B3063629
theorem B1911383 : Blo 846354 1911383 := bstep (se 1 (by rfl) ⟨1433537, by rfl⟩ : syracuseStep 1911383 = 2867075) B2867075
theorem B1911563 : Blo 846354 1911563 := bstep (se 1 (by rfl) ⟨1433672, by rfl⟩ : syracuseStep 1911563 = 2867345) B2867345
theorem B7744301 : Blo 846354 7744301 := bstep (se 3 (by rfl) ⟨1452056, by rfl⟩ : syracuseStep 7744301 = 2904113) B2904113
theorem B1911617 : Blo 846354 1911617 := bstep (se 2 (by rfl) ⟨716856, by rfl⟩ : syracuseStep 1911617 = 1433713) B1433713
theorem B5155649 : Blo 846354 5155649 := bstep (se 2 (by rfl) ⟨1933368, by rfl⟩ : syracuseStep 5155649 = 3866737) B3866737
theorem B4303691 : Blo 846354 4303691 := bstep (se 1 (by rfl) ⟨3227768, by rfl⟩ : syracuseStep 4303691 = 6455537) B6455537
theorem B6433667 : Blo 846354 6433667 := bstep (se 1 (by rfl) ⟨4825250, by rfl⟩ : syracuseStep 6433667 = 9650501) B9650501
theorem B1911833 : Blo 846354 1911833 := bstep (se 2 (by rfl) ⟨716937, by rfl⟩ : syracuseStep 1911833 = 1433875) B1433875
theorem B1911923 : Blo 846354 1911923 := bstep (se 1 (by rfl) ⟨1433942, by rfl⟩ : syracuseStep 1911923 = 2867885) B2867885
theorem B1911959 : Blo 846354 1911959 := bstep (se 1 (by rfl) ⟨1433969, by rfl⟩ : syracuseStep 1911959 = 2867939) B2867939
theorem B21769397 : Blo 846354 21769397 := bstep (se 5 (by rfl) ⟨1020440, by rfl⟩ : syracuseStep 21769397 = 2040881) B2040881
theorem B3222787 : Blo 846354 3222787 := bstep (se 1 (by rfl) ⟨2417090, by rfl⟩ : syracuseStep 3222787 = 4834181) B4834181
theorem B1912139 : Blo 846354 1912139 := bstep (se 1 (by rfl) ⟨1434104, by rfl⟩ : syracuseStep 1912139 = 2868209) B2868209
theorem B1912193 : Blo 846354 1912193 := bstep (se 2 (by rfl) ⟨717072, by rfl⟩ : syracuseStep 1912193 = 1434145) B1434145
theorem B6106499 : Blo 846354 6106499 := bstep (se 1 (by rfl) ⟨4579874, by rfl⟩ : syracuseStep 6106499 = 9159749) B9159749
theorem B2862539 : Blo 846354 2862539 := bstep (se 1 (by rfl) ⟨2146904, by rfl⟩ : syracuseStep 2862539 = 4293809) B4293809
theorem B3223091 : Blo 846354 3223091 := bstep (se 1 (by rfl) ⟨2417318, by rfl⟩ : syracuseStep 3223091 = 4834637) B4834637
theorem B1912409 : Blo 846354 1912409 := bstep (se 2 (by rfl) ⟨717153, by rfl⟩ : syracuseStep 1912409 = 1434307) B1434307
theorem B1912499 : Blo 846354 1912499 := bstep (se 1 (by rfl) ⟨1434374, by rfl⟩ : syracuseStep 1912499 = 2868749) B2868749
theorem B1912535 : Blo 846354 1912535 := bstep (se 1 (by rfl) ⟨1434401, by rfl⟩ : syracuseStep 1912535 = 2868803) B2868803
theorem B2862809 : Blo 846354 2862809 := bstep (se 2 (by rfl) ⟨1073553, by rfl⟩ : syracuseStep 2862809 = 2147107) B2147107
theorem B1912715 : Blo 846354 1912715 := bstep (se 1 (by rfl) ⟨1434536, by rfl⟩ : syracuseStep 1912715 = 2869073) B2869073
theorem B1552321 : Blo 846354 1552321 := bstep (se 2 (by rfl) ⟨582120, by rfl⟩ : syracuseStep 1552321 = 1164241) B1164241
theorem B1912769 : Blo 846354 1912769 := bstep (se 2 (by rfl) ⟨717288, by rfl⟩ : syracuseStep 1912769 = 1434577) B1434577
theorem B2142359 : Blo 846354 2142359 := bstep (se 1 (by rfl) ⟨1606769, by rfl⟩ : syracuseStep 2142359 = 3213539) B3213539
theorem B1912985 : Blo 846354 1912985 := bstep (se 2 (by rfl) ⟨717369, by rfl⟩ : syracuseStep 1912985 = 1434739) B1434739
theorem B3223745 : Blo 846354 3223745 := bstep (se 2 (by rfl) ⟨1208904, by rfl⟩ : syracuseStep 3223745 = 2417809) B2417809
theorem B1913075 : Blo 846354 1913075 := bstep (se 1 (by rfl) ⟨1434806, by rfl⟩ : syracuseStep 1913075 = 2869613) B2869613
theorem B1913111 : Blo 846354 1913111 := bstep (se 1 (by rfl) ⟨1434833, by rfl⟩ : syracuseStep 1913111 = 2869667) B2869667
theorem B2863511 : Blo 846354 2863511 := bstep (se 1 (by rfl) ⟨2147633, by rfl⟩ : syracuseStep 2863511 = 4295267) B4295267
theorem B1913291 : Blo 846354 1913291 := bstep (se 1 (by rfl) ⟨1434968, by rfl⟩ : syracuseStep 1913291 = 2869937) B2869937
theorem B9679661 : Blo 846354 9679661 := bstep (se 3 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 9679661 = 3629873) B3629873
theorem B1815347 : Blo 846354 1815347 := bstep (se 1 (by rfl) ⟨1361510, by rfl⟩ : syracuseStep 1815347 = 2723021) B2723021
theorem B4076381 : Blo 846354 4076381 := bstep (se 3 (by rfl) ⟨764321, by rfl⟩ : syracuseStep 4076381 = 1528643) B1528643
theorem B2864051 : Blo 846354 2864051 := bstep (se 1 (by rfl) ⟨2148038, by rfl⟩ : syracuseStep 2864051 = 4296077) B4296077
theorem B2143169 : Blo 846354 2143169 := bstep (se 2 (by rfl) ⟨803688, by rfl⟩ : syracuseStep 2143169 = 1607377) B1607377
theorem B1160281 : Blo 846354 1160281 := bstep (se 2 (by rfl) ⟨435105, by rfl⟩ : syracuseStep 1160281 = 870211) B870211
theorem B2864321 : Blo 846354 2864321 := bstep (se 2 (by rfl) ⟨1074120, by rfl⟩ : syracuseStep 2864321 = 2148241) B2148241
theorem B1651915 : Blo 846354 1651915 := bstep (se 1 (by rfl) ⟨1238936, by rfl⟩ : syracuseStep 1651915 = 2477873) B2477873
theorem B3225005 : Blo 846354 3225005 := bstep (se 3 (by rfl) ⟨604688, by rfl⟩ : syracuseStep 3225005 = 1209377) B1209377
theorem B3225035 : Blo 846354 3225035 := bstep (se 1 (by rfl) ⟨2418776, by rfl⟩ : syracuseStep 3225035 = 4837553) B4837553
theorem B2143705 : Blo 846354 2143705 := bstep (se 2 (by rfl) ⟨803889, by rfl⟩ : syracuseStep 2143705 = 1607779) B1607779
theorem B2864861 : Blo 846354 2864861 := bstep (se 3 (by rfl) ⟨537161, by rfl⟩ : syracuseStep 2864861 = 1074323) B1074323
theorem B1718167 : Blo 846354 1718167 := bstep (se 1 (by rfl) ⟨1288625, by rfl⟩ : syracuseStep 1718167 = 2577251) B2577251
theorem B7747589 : Blo 846354 7747589 := bstep (se 4 (by rfl) ⟨726336, by rfl⟩ : syracuseStep 7747589 = 1452673) B1452673
theorem B3061783 : Blo 846354 3061783 := bstep (se 1 (by rfl) ⟨2296337, by rfl⟩ : syracuseStep 3061783 = 4592675) B4592675
theorem B3225689 : Blo 846354 3225689 := bstep (se 2 (by rfl) ⟨1209633, by rfl⟩ : syracuseStep 3225689 = 2419267) B2419267
theorem B6437069 : Blo 846354 6437069 := bstep (se 3 (by rfl) ⟨1206950, by rfl⟩ : syracuseStep 6437069 = 2413901) B2413901
theorem B3619075 : Blo 846354 3619075 := bstep (se 1 (by rfl) ⟨2714306, by rfl⟩ : syracuseStep 3619075 = 5428613) B5428613
theorem B3226007 : Blo 846354 3226007 := bstep (se 1 (by rfl) ⟨2419505, by rfl⟩ : syracuseStep 3226007 = 4839011) B4839011
theorem B1292761 : Blo 846354 1292761 := bstep (se 2 (by rfl) ⟨484785, by rfl⟩ : syracuseStep 1292761 = 969571) B969571
theorem B2144819 : Blo 846354 2144819 := bstep (se 1 (by rfl) ⟨1608614, by rfl⟩ : syracuseStep 2144819 = 3217229) B3217229
theorem B3619417 : Blo 846354 3619417 := bstep (se 2 (by rfl) ⟨1357281, by rfl⟩ : syracuseStep 3619417 = 2714563) B2714563
theorem B6437555 : Blo 846354 6437555 := bstep (se 1 (by rfl) ⟨4828166, by rfl⟩ : syracuseStep 6437555 = 9656333) B9656333
theorem B1358615 : Blo 846354 1358615 := bstep (se 1 (by rfl) ⟨1018961, by rfl⟩ : syracuseStep 1358615 = 2037923) B2037923
theorem B3259187 : Blo 846354 3259187 := bstep (se 1 (by rfl) ⟨2444390, by rfl⟩ : syracuseStep 3259187 = 4888781) B4888781
theorem B2865995 : Blo 846354 2865995 := bstep (se 1 (by rfl) ⟨2149496, by rfl⟩ : syracuseStep 2865995 = 4298993) B4298993
theorem B2145113 : Blo 846354 2145113 := bstep (se 2 (by rfl) ⟨804417, by rfl⟩ : syracuseStep 2145113 = 1608835) B1608835
theorem B3226675 : Blo 846354 3226675 := bstep (se 1 (by rfl) ⟨2420006, by rfl⟩ : syracuseStep 3226675 = 4840013) B4840013
theorem B2866265 : Blo 846354 2866265 := bstep (se 2 (by rfl) ⟨1074849, by rfl⟩ : syracuseStep 2866265 = 2149699) B2149699
theorem B1358999 : Blo 846354 1358999 := bstep (se 1 (by rfl) ⟨1019249, by rfl⟩ : syracuseStep 1358999 = 2038499) B2038499
theorem B1359127 : Blo 846354 1359127 := bstep (se 1 (by rfl) ⟨1019345, by rfl⟩ : syracuseStep 1359127 = 2038691) B2038691
theorem B1162585 : Blo 846354 1162585 := bstep (se 2 (by rfl) ⟨435969, by rfl⟩ : syracuseStep 1162585 = 871939) B871939
theorem B9780659 : Blo 846354 9780659 := bstep (se 1 (by rfl) ⟨7335494, by rfl⟩ : syracuseStep 9780659 = 14670989) B14670989
theorem B3620375 : Blo 846354 3620375 := bstep (se 1 (by rfl) ⟨2715281, by rfl⟩ : syracuseStep 3620375 = 5430563) B5430563
theorem B5226059 : Blo 846354 5226059 := bstep (se 1 (by rfl) ⟨3919544, by rfl⟩ : syracuseStep 5226059 = 7839089) B7839089
theorem B2866967 : Blo 846354 2866967 := bstep (se 1 (by rfl) ⟨2150225, by rfl⟩ : syracuseStep 2866967 = 4300451) B4300451
theorem B1359947 : Blo 846354 1359947 := bstep (se 1 (by rfl) ⟨1019960, by rfl⟩ : syracuseStep 1359947 = 2039921) B2039921
theorem B6439013 : Blo 846354 6439013 := bstep (se 4 (by rfl) ⟨603657, by rfl⟩ : syracuseStep 6439013 = 1207315) B1207315
theorem B4079747 : Blo 846354 4079747 := bstep (se 1 (by rfl) ⟨3059810, by rfl⟩ : syracuseStep 4079747 = 6119621) B6119621
theorem B4833431 : Blo 846354 4833431 := bstep (se 1 (by rfl) ⟨3625073, by rfl⟩ : syracuseStep 4833431 = 7250147) B7250147
theorem B1360075 : Blo 846354 1360075 := bstep (se 1 (by rfl) ⟨1020056, by rfl⟩ : syracuseStep 1360075 = 2040113) B2040113
theorem B3227921 : Blo 846354 3227921 := bstep (se 2 (by rfl) ⟨1210470, by rfl⟩ : syracuseStep 3227921 = 2420941) B2420941
theorem B4079917 : Blo 846354 4079917 := bstep (se 3 (by rfl) ⟨764984, by rfl⟩ : syracuseStep 4079917 = 1529969) B1529969
theorem B2867507 : Blo 846354 2867507 := bstep (se 1 (by rfl) ⟨2150630, by rfl⟩ : syracuseStep 2867507 = 4301261) B4301261
theorem B2146763 : Blo 846354 2146763 := bstep (se 1 (by rfl) ⟨1610072, by rfl⟩ : syracuseStep 2146763 = 3220145) B3220145
theorem B2867777 : Blo 846354 2867777 := bstep (se 2 (by rfl) ⟨1075416, by rfl⟩ : syracuseStep 2867777 = 2150833) B2150833
theorem B6439499 : Blo 846354 6439499 := bstep (se 1 (by rfl) ⟨4829624, by rfl⟩ : syracuseStep 6439499 = 9659249) B9659249
theorem B3228619 : Blo 846354 3228619 := bstep (se 1 (by rfl) ⟨2421464, by rfl⟩ : syracuseStep 3228619 = 4842929) B4842929
theorem B3490781 : Blo 846354 3490781 := bstep (se 3 (by rfl) ⟨654521, by rfl⟩ : syracuseStep 3490781 = 1309043) B1309043
theorem B6865985 : Blo 846354 6865985 := bstep (se 2 (by rfl) ⟨2574744, by rfl⟩ : syracuseStep 6865985 = 5149489) B5149489
theorem B25183307 : Blo 846354 25183307 := bstep (se 1 (by rfl) ⟨18887480, by rfl⟩ : syracuseStep 25183307 = 37774961) B37774961
theorem B2868317 : Blo 846354 2868317 := bstep (se 3 (by rfl) ⟨537809, by rfl⟩ : syracuseStep 2868317 = 1075619) B1075619
theorem B4408499 : Blo 846354 4408499 := bstep (se 1 (by rfl) ⟨3306374, by rfl⟩ : syracuseStep 4408499 = 6612749) B6612749
theorem B3622067 : Blo 846354 3622067 := bstep (se 1 (by rfl) ⟨2716550, by rfl⟩ : syracuseStep 3622067 = 5433101) B5433101
theorem B2147735 : Blo 846354 2147735 := bstep (se 1 (by rfl) ⟨1610801, by rfl⟩ : syracuseStep 2147735 = 3221603) B3221603
theorem B7259543 : Blo 846354 7259543 := bstep (se 1 (by rfl) ⟨5444657, by rfl⟩ : syracuseStep 7259543 = 10889315) B10889315
theorem B1361305 : Blo 846354 1361305 := bstep (se 2 (by rfl) ⟨510489, by rfl⟩ : syracuseStep 1361305 = 1020979) B1020979
theorem B2410519 : Blo 846354 2410519 := bstep (se 1 (by rfl) ⟨1807889, by rfl⟩ : syracuseStep 2410519 = 3615779) B3615779
theorem B2148403 : Blo 846354 2148403 := bstep (se 1 (by rfl) ⟨1611302, by rfl⟩ : syracuseStep 2148403 = 3222605) B3222605
theorem B3360941 : Blo 846354 3360941 := bstep (se 3 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 3360941 = 1260353) B1260353
theorem B2148545 : Blo 846354 2148545 := bstep (se 2 (by rfl) ⟨805704, by rfl⟩ : syracuseStep 2148545 = 1611409) B1611409
theorem B2869451 : Blo 846354 2869451 := bstep (se 1 (by rfl) ⟨2152088, by rfl⟩ : syracuseStep 2869451 = 4304177) B4304177
theorem B4639193 : Blo 846354 4639193 := bstep (se 2 (by rfl) ⟨1739697, by rfl⟩ : syracuseStep 4639193 = 3479395) B3479395
theorem B2869721 : Blo 846354 2869721 := bstep (se 2 (by rfl) ⟨1076145, by rfl⟩ : syracuseStep 2869721 = 2152291) B2152291
theorem B5163841 : Blo 846354 5163841 := bstep (se 2 (by rfl) ⟨1936440, by rfl⟩ : syracuseStep 5163841 = 3872881) B3872881
theorem B1428313 : Blo 846354 1428313 := bstep (se 2 (by rfl) ⟨535617, by rfl⟩ : syracuseStep 1428313 = 1071235) B1071235
theorem B904171 : Blo 846354 904171 := bstep (se 1 (by rfl) ⟨678128, by rfl⟩ : syracuseStep 904171 = 1356257) B1356257
theorem B6868061 : Blo 846354 6868061 := bstep (se 3 (by rfl) ⟨1287761, by rfl⟩ : syracuseStep 6868061 = 2575523) B2575523
theorem B1723609 : Blo 846354 1723609 := bstep (se 2 (by rfl) ⟨646353, by rfl⟩ : syracuseStep 1723609 = 1292707) B1292707
theorem B2411851 : Blo 846354 2411851 := bstep (se 1 (by rfl) ⟨1808888, by rfl⟩ : syracuseStep 2411851 = 3617777) B3617777
theorem B1723763 : Blo 846354 1723763 := bstep (se 1 (by rfl) ⟨1292822, by rfl⟩ : syracuseStep 1723763 = 2585645) B2585645
theorem B1428887 : Blo 846354 1428887 := bstep (se 1 (by rfl) ⟨1071665, by rfl⟩ : syracuseStep 1428887 = 2143331) B2143331
theorem B2149811 : Blo 846354 2149811 := bstep (se 1 (by rfl) ⟨1612358, by rfl⟩ : syracuseStep 2149811 = 3224717) B3224717
theorem B1429015 : Blo 846354 1429015 := bstep (se 1 (by rfl) ⟨1071761, by rfl⟩ : syracuseStep 1429015 = 2143523) B2143523
theorem B2412125 : Blo 846354 2412125 := bstep (se 3 (by rfl) ⟨452273, by rfl⟩ : syracuseStep 2412125 = 904547) B904547
theorem B3624749 : Blo 846354 3624749 := bstep (se 3 (by rfl) ⟨679640, by rfl⟩ : syracuseStep 3624749 = 1359281) B1359281
theorem B2412467 : Blo 846354 2412467 := bstep (se 1 (by rfl) ⟨1809350, by rfl⟩ : syracuseStep 2412467 = 3618701) B3618701
theorem B2150347 : Blo 846354 2150347 := bstep (se 1 (by rfl) ⟨1612760, by rfl⟩ : syracuseStep 2150347 = 3225521) B3225521
theorem B2150489 : Blo 846354 2150489 := bstep (se 2 (by rfl) ⟨806433, by rfl⟩ : syracuseStep 2150489 = 1612867) B1612867
theorem B1429643 : Blo 846354 1429643 := bstep (se 1 (by rfl) ⟨1072232, by rfl⟩ : syracuseStep 1429643 = 2144465) B2144465
theorem B5165207 : Blo 846354 5165207 := bstep (se 1 (by rfl) ⟨3873905, by rfl⟩ : syracuseStep 5165207 = 7747811) B7747811
theorem B1429771 : Blo 846354 1429771 := bstep (se 1 (by rfl) ⟨1072328, by rfl⟩ : syracuseStep 1429771 = 2144657) B2144657
theorem B5427587 : Blo 846354 5427587 := bstep (se 1 (by rfl) ⟨4070690, by rfl⟩ : syracuseStep 5427587 = 8141381) B8141381
theorem B905623 : Blo 846354 905623 := bstep (se 1 (by rfl) ⟨679217, by rfl⟩ : syracuseStep 905623 = 1358435) B1358435
theorem B1429913 : Blo 846354 1429913 := bstep (se 2 (by rfl) ⟨536217, by rfl⟩ : syracuseStep 1429913 = 1072435) B1072435
theorem B872983 : Blo 846354 872983 := bstep (se 1 (by rfl) ⟨654737, by rfl⟩ : syracuseStep 872983 = 1309475) B1309475
theorem B1430041 : Blo 846354 1430041 := bstep (se 2 (by rfl) ⟨536265, by rfl⟩ : syracuseStep 1430041 = 1072531) B1072531
theorem B3265069 : Blo 846354 3265069 := bstep (se 3 (by rfl) ⟨612200, by rfl⟩ : syracuseStep 3265069 = 1224401) B1224401
theorem B905995 : Blo 846354 905995 := bstep (se 1 (by rfl) ⟨679496, by rfl⟩ : syracuseStep 905995 = 1358993) B1358993
theorem B10343213 : Blo 846354 10343213 := bstep (se 3 (by rfl) ⟨1939352, by rfl⟩ : syracuseStep 10343213 = 3878705) B3878705
theorem B18371393 : Blo 846354 18371393 := bstep (se 2 (by rfl) ⟨6889272, by rfl⟩ : syracuseStep 18371393 = 13778545) B13778545
theorem B4838237 : Blo 846354 4838237 := bstep (se 3 (by rfl) ⟨907169, by rfl⟩ : syracuseStep 4838237 = 1814339) B1814339
theorem B2151319 : Blo 846354 2151319 := bstep (se 1 (by rfl) ⟨1613489, by rfl⟩ : syracuseStep 2151319 = 3226979) B3226979
theorem B6116417 : Blo 846354 6116417 := bstep (se 2 (by rfl) ⟨2293656, by rfl⟩ : syracuseStep 6116417 = 4587313) B4587313
theorem B1430615 : Blo 846354 1430615 := bstep (se 1 (by rfl) ⟨1072961, by rfl⟩ : syracuseStep 1430615 = 2145923) B2145923
theorem B1430743 : Blo 846354 1430743 := bstep (se 1 (by rfl) ⟨1073057, by rfl⟩ : syracuseStep 1430743 = 2146115) B2146115
theorem B2151755 : Blo 846354 2151755 := bstep (se 1 (by rfl) ⟨1613816, by rfl⟩ : syracuseStep 2151755 = 3227633) B3227633
theorem B2905537 : Blo 846354 2905537 := bstep (se 2 (by rfl) ⟨1089576, by rfl⟩ : syracuseStep 2905537 = 2179153) B2179153
theorem B12211843 : Blo 846354 12211843 := bstep (se 1 (by rfl) ⟨9158882, by rfl⟩ : syracuseStep 12211843 = 18317765) B18317765
theorem B2152129 : Blo 846354 2152129 := bstep (se 2 (by rfl) ⟨807048, by rfl⟩ : syracuseStep 2152129 = 1614097) B1614097
theorem B7722701 : Blo 846354 7722701 := bstep (se 3 (by rfl) ⟨1448006, by rfl⟩ : syracuseStep 7722701 = 2896013) B2896013
theorem B1529623 : Blo 846354 1529623 := bstep (se 1 (by rfl) ⟨1147217, by rfl⟩ : syracuseStep 1529623 = 2294435) B2294435
theorem B6444845 : Blo 846354 6444845 := bstep (se 3 (by rfl) ⟨1208408, by rfl⟩ : syracuseStep 6444845 = 2416817) B2416817
theorem B1431371 : Blo 846354 1431371 := bstep (se 1 (by rfl) ⟨1073528, by rfl⟩ : syracuseStep 1431371 = 2147057) B2147057
theorem B2414539 : Blo 846354 2414539 := bstep (se 1 (by rfl) ⟨1810904, by rfl⟩ : syracuseStep 2414539 = 3621809) B3621809
theorem B1431499 : Blo 846354 1431499 := bstep (se 1 (by rfl) ⟨1073624, by rfl⟩ : syracuseStep 1431499 = 2147249) B2147249
theorem B1431641 : Blo 846354 1431641 := bstep (se 2 (by rfl) ⟨536865, by rfl⟩ : syracuseStep 1431641 = 1073731) B1073731
theorem B7231589 : Blo 846354 7231589 := bstep (se 4 (by rfl) ⟨677961, by rfl⟩ : syracuseStep 7231589 = 1355923) B1355923
theorem B1431769 : Blo 846354 1431769 := bstep (se 2 (by rfl) ⟨536913, by rfl⟩ : syracuseStep 1431769 = 1073827) B1073827
theorem B2415041 : Blo 846354 2415041 := bstep (se 2 (by rfl) ⟨905640, by rfl⟩ : syracuseStep 2415041 = 1811281) B1811281
theorem B1071883 : Blo 846354 1071883 := bstep (se 1 (by rfl) ⟨803912, by rfl⟩ : syracuseStep 1071883 = 1607825) B1607825
theorem B7232273 : Blo 846354 7232273 := bstep (se 2 (by rfl) ⟨2712102, by rfl⟩ : syracuseStep 7232273 = 5424205) B5424205
theorem B2415383 : Blo 846354 2415383 := bstep (se 1 (by rfl) ⟨1811537, by rfl⟩ : syracuseStep 2415383 = 3623075) B3623075
theorem B1432343 : Blo 846354 1432343 := bstep (se 1 (by rfl) ⟨1074257, by rfl⟩ : syracuseStep 1432343 = 2148515) B2148515
theorem B1530713 : Blo 846354 1530713 := bstep (se 2 (by rfl) ⟨574017, by rfl⟩ : syracuseStep 1530713 = 1148035) B1148035
theorem B1432471 : Blo 846354 1432471 := bstep (se 1 (by rfl) ⟨1074353, by rfl⟩ : syracuseStep 1432471 = 2148707) B2148707
theorem B3628097 : Blo 846354 3628097 := bstep (se 2 (by rfl) ⟨1360536, by rfl⟩ : syracuseStep 3628097 = 2721073) B2721073
theorem B1629377 : Blo 846354 1629377 := bstep (se 2 (by rfl) ⟨611016, by rfl⟩ : syracuseStep 1629377 = 1222033) B1222033
theorem B4840721 : Blo 846354 4840721 := bstep (se 2 (by rfl) ⟨1815270, by rfl⟩ : syracuseStep 4840721 = 3630541) B3630541
theorem B3628439 : Blo 846354 3628439 := bstep (se 1 (by rfl) ⟨2721329, by rfl⟩ : syracuseStep 3628439 = 5442659) B5442659
theorem B1433099 : Blo 846354 1433099 := bstep (se 1 (by rfl) ⟨1074824, by rfl⟩ : syracuseStep 1433099 = 2149649) B2149649
theorem B1433227 : Blo 846354 1433227 := bstep (se 1 (by rfl) ⟨1074920, by rfl⟩ : syracuseStep 1433227 = 2149841) B2149841
theorem B1072855 : Blo 846354 1072855 := bstep (se 1 (by rfl) ⟨804641, by rfl⟩ : syracuseStep 1072855 = 1609283) B1609283
theorem B6119185 : Blo 846354 6119185 := bstep (se 2 (by rfl) ⟨2294694, by rfl⟩ : syracuseStep 6119185 = 4589389) B4589389
theorem B1433369 : Blo 846354 1433369 := bstep (se 2 (by rfl) ⟨537513, by rfl⟩ : syracuseStep 1433369 = 1075027) B1075027
theorem B1269593 : Blo 846354 1269593 := bstep (se 2 (by rfl) ⟨476097, by rfl⟩ : syracuseStep 1269593 = 952195) B952195
theorem B1433497 : Blo 846354 1433497 := bstep (se 2 (by rfl) ⟨537561, by rfl⟩ : syracuseStep 1433497 = 1075123) B1075123
theorem B1269707 : Blo 846354 1269707 := bstep (se 1 (by rfl) ⟨952280, by rfl⟩ : syracuseStep 1269707 = 1904561) B1904561
theorem B1269719 : Blo 846354 1269719 := bstep (se 1 (by rfl) ⟨952289, by rfl⟩ : syracuseStep 1269719 = 1904579) B1904579
theorem B1269785 : Blo 846354 1269785 := bstep (se 2 (by rfl) ⟨476169, by rfl⟩ : syracuseStep 1269785 = 952339) B952339
theorem B1269899 : Blo 846354 1269899 := bstep (se 1 (by rfl) ⟨952424, by rfl⟩ : syracuseStep 1269899 = 1904849) B1904849
theorem B1269911 : Blo 846354 1269911 := bstep (se 1 (by rfl) ⟨952433, by rfl⟩ : syracuseStep 1269911 = 1904867) B1904867
theorem B8151191 : Blo 846354 8151191 := bstep (se 1 (by rfl) ⟨6113393, by rfl⟩ : syracuseStep 8151191 = 12226787) B12226787
theorem B1269977 : Blo 846354 1269977 := bstep (se 2 (by rfl) ⟨476241, by rfl⟩ : syracuseStep 1269977 = 952483) B952483
theorem B2908439 : Blo 846354 2908439 := bstep (se 1 (by rfl) ⟨2181329, by rfl⟩ : syracuseStep 2908439 = 4362659) B4362659
theorem B13951277 : Blo 846354 13951277 := bstep (se 3 (by rfl) ⟨2615864, by rfl⟩ : syracuseStep 13951277 = 5231729) B5231729
theorem B13066541 : Blo 846354 13066541 := bstep (se 3 (by rfl) ⟨2449976, by rfl⟩ : syracuseStep 13066541 = 4899953) B4899953
theorem B4284737 : Blo 846354 4284737 := bstep (se 2 (by rfl) ⟨1606776, by rfl⟩ : syracuseStep 4284737 = 3213553) B3213553
theorem B2711873 : Blo 846354 2711873 := bstep (se 2 (by rfl) ⟨1016952, by rfl⟩ : syracuseStep 2711873 = 2033905) B2033905
theorem B1270091 : Blo 846354 1270091 := bstep (se 1 (by rfl) ⟨952568, by rfl⟩ : syracuseStep 1270091 = 1905137) B1905137
theorem B1270103 : Blo 846354 1270103 := bstep (se 1 (by rfl) ⟨952577, by rfl⟩ : syracuseStep 1270103 = 1905155) B1905155
theorem B1270169 : Blo 846354 1270169 := bstep (se 2 (by rfl) ⟨476313, by rfl⟩ : syracuseStep 1270169 = 952627) B952627
theorem B2712001 : Blo 846354 2712001 := bstep (se 2 (by rfl) ⟨1017000, by rfl⟩ : syracuseStep 2712001 = 2034001) B2034001
theorem B1434071 : Blo 846354 1434071 := bstep (se 1 (by rfl) ⟨1075553, by rfl⟩ : syracuseStep 1434071 = 2151107) B2151107
theorem B1270283 : Blo 846354 1270283 := bstep (se 1 (by rfl) ⟨952712, by rfl⟩ : syracuseStep 1270283 = 1905425) B1905425
theorem B1073675 : Blo 846354 1073675 := bstep (se 1 (by rfl) ⟨805256, by rfl⟩ : syracuseStep 1073675 = 1610513) B1610513
theorem B14508557 : Blo 846354 14508557 := bstep (se 3 (by rfl) ⟨2720354, by rfl⟩ : syracuseStep 14508557 = 5440709) B5440709
theorem B1270295 : Blo 846354 1270295 := bstep (se 1 (by rfl) ⟨952721, by rfl⟩ : syracuseStep 1270295 = 1905443) B1905443
theorem B1434199 : Blo 846354 1434199 := bstep (se 1 (by rfl) ⟨1075649, by rfl⟩ : syracuseStep 1434199 = 2151299) B2151299
theorem B1270361 : Blo 846354 1270361 := bstep (se 2 (by rfl) ⟨476385, by rfl⟩ : syracuseStep 1270361 = 952771) B952771
theorem B1860275 : Blo 846354 1860275 := bstep (se 1 (by rfl) ⟨1395206, by rfl⟩ : syracuseStep 1860275 = 2790413) B2790413
theorem B2712257 : Blo 846354 2712257 := bstep (se 2 (by rfl) ⟨1017096, by rfl⟩ : syracuseStep 2712257 = 2034193) B2034193
theorem B1270475 : Blo 846354 1270475 := bstep (se 1 (by rfl) ⟨952856, by rfl⟩ : syracuseStep 1270475 = 1905713) B1905713
theorem B1270487 : Blo 846354 1270487 := bstep (se 1 (by rfl) ⟨952865, by rfl⟩ : syracuseStep 1270487 = 1905731) B1905731
theorem B1270553 : Blo 846354 1270553 := bstep (se 2 (by rfl) ⟨476457, by rfl⟩ : syracuseStep 1270553 = 952915) B952915
theorem B2417501 : Blo 846354 2417501 := bstep (se 3 (by rfl) ⟨453281, by rfl⟩ : syracuseStep 2417501 = 906563) B906563
theorem B1270667 : Blo 846354 1270667 := bstep (se 1 (by rfl) ⟨953000, by rfl⟩ : syracuseStep 1270667 = 1906001) B1906001
theorem B1270679 : Blo 846354 1270679 := bstep (se 1 (by rfl) ⟨953009, by rfl⟩ : syracuseStep 1270679 = 1906019) B1906019
theorem B1270745 : Blo 846354 1270745 := bstep (se 2 (by rfl) ⟨476529, by rfl⟩ : syracuseStep 1270745 = 953059) B953059
theorem B1270859 : Blo 846354 1270859 := bstep (se 1 (by rfl) ⟨953144, by rfl⟩ : syracuseStep 1270859 = 1906289) B1906289
theorem B1270871 : Blo 846354 1270871 := bstep (se 1 (by rfl) ⟨953153, by rfl⟩ : syracuseStep 1270871 = 1906307) B1906307
theorem B6186077 : Blo 846354 6186077 := bstep (se 3 (by rfl) ⟨1159889, by rfl⟩ : syracuseStep 6186077 = 2319779) B2319779
theorem B1270937 : Blo 846354 1270937 := bstep (se 2 (by rfl) ⟨476601, by rfl⟩ : syracuseStep 1270937 = 953203) B953203
theorem B1631411 : Blo 846354 1631411 := bstep (se 1 (by rfl) ⟨1223558, by rfl⟩ : syracuseStep 1631411 = 2447117) B2447117
theorem B2417843 : Blo 846354 2417843 := bstep (se 1 (by rfl) ⟨1813382, by rfl⟩ : syracuseStep 2417843 = 3626765) B3626765
theorem B1074379 : Blo 846354 1074379 := bstep (se 1 (by rfl) ⟨805784, by rfl⟩ : syracuseStep 1074379 = 1611569) B1611569
theorem B1434827 : Blo 846354 1434827 := bstep (se 1 (by rfl) ⟨1076120, by rfl⟩ : syracuseStep 1434827 = 2152241) B2152241
theorem B3302621 : Blo 846354 3302621 := bstep (se 3 (by rfl) ⟨619241, by rfl⟩ : syracuseStep 3302621 = 1238483) B1238483
theorem B1271051 : Blo 846354 1271051 := bstep (se 1 (by rfl) ⟨953288, by rfl⟩ : syracuseStep 1271051 = 1906577) B1906577
theorem B1271063 : Blo 846354 1271063 := bstep (se 1 (by rfl) ⟨953297, by rfl⟩ : syracuseStep 1271063 = 1906595) B1906595
theorem B1434955 : Blo 846354 1434955 := bstep (se 1 (by rfl) ⟨1076216, by rfl⟩ : syracuseStep 1434955 = 2152433) B2152433
theorem B1271129 : Blo 846354 1271129 := bstep (se 2 (by rfl) ⟨476673, by rfl⟩ : syracuseStep 1271129 = 953347) B953347
theorem B1271243 : Blo 846354 1271243 := bstep (se 1 (by rfl) ⟨953432, by rfl⟩ : syracuseStep 1271243 = 1906865) B1906865
theorem B1271255 : Blo 846354 1271255 := bstep (se 1 (by rfl) ⟨953441, by rfl⟩ : syracuseStep 1271255 = 1906883) B1906883
theorem B1074647 : Blo 846354 1074647 := bstep (se 1 (by rfl) ⟨805985, by rfl⟩ : syracuseStep 1074647 = 1611971) B1611971
theorem B10315225 : Blo 846354 10315225 := bstep (se 2 (by rfl) ⟨3868209, by rfl⟩ : syracuseStep 10315225 = 7736419) B7736419
theorem B3630557 : Blo 846354 3630557 := bstep (se 3 (by rfl) ⟨680729, by rfl⟩ : syracuseStep 3630557 = 1361459) B1361459
theorem B1271321 : Blo 846354 1271321 := bstep (se 2 (by rfl) ⟨476745, by rfl⟩ : syracuseStep 1271321 = 953491) B953491
theorem B6448733 : Blo 846354 6448733 := bstep (se 3 (by rfl) ⟨1209137, by rfl⟩ : syracuseStep 6448733 = 2418275) B2418275
theorem B1271435 : Blo 846354 1271435 := bstep (se 1 (by rfl) ⟨953576, by rfl⟩ : syracuseStep 1271435 = 1907153) B1907153
theorem B1271447 : Blo 846354 1271447 := bstep (se 1 (by rfl) ⟨953585, by rfl⟩ : syracuseStep 1271447 = 1907171) B1907171
theorem B1271513 : Blo 846354 1271513 := bstep (se 2 (by rfl) ⟨476817, by rfl⟩ : syracuseStep 1271513 = 953635) B953635
theorem B3630865 : Blo 846354 3630865 := bstep (se 2 (by rfl) ⟨1361574, by rfl⟩ : syracuseStep 3630865 = 2723149) B2723149
theorem B3630899 : Blo 846354 3630899 := bstep (se 1 (by rfl) ⟨2723174, by rfl⟩ : syracuseStep 3630899 = 5446349) B5446349
theorem B1271627 : Blo 846354 1271627 := bstep (se 1 (by rfl) ⟨953720, by rfl⟩ : syracuseStep 1271627 = 1907441) B1907441
theorem B1271639 : Blo 846354 1271639 := bstep (se 1 (by rfl) ⟨953729, by rfl⟩ : syracuseStep 1271639 = 1907459) B1907459
theorem B1271705 : Blo 846354 1271705 := bstep (se 2 (by rfl) ⟨476889, by rfl⟩ : syracuseStep 1271705 = 953779) B953779
theorem B1271819 : Blo 846354 1271819 := bstep (se 1 (by rfl) ⟨953864, by rfl⟩ : syracuseStep 1271819 = 1907729) B1907729
theorem B1271831 : Blo 846354 1271831 := bstep (se 1 (by rfl) ⟨953873, by rfl⟩ : syracuseStep 1271831 = 1907747) B1907747
theorem B1271897 : Blo 846354 1271897 := bstep (se 2 (by rfl) ⟨476961, by rfl⟩ : syracuseStep 1271897 = 953923) B953923
theorem B29419661 : Blo 846354 29419661 := bstep (se 3 (by rfl) ⟨5516186, by rfl⟩ : syracuseStep 29419661 = 11032373) B11032373
theorem B1075351 : Blo 846354 1075351 := bstep (se 1 (by rfl) ⟨806513, by rfl⟩ : syracuseStep 1075351 = 1613027) B1613027
theorem B1272011 : Blo 846354 1272011 := bstep (se 1 (by rfl) ⟨954008, by rfl⟩ : syracuseStep 1272011 = 1908017) B1908017
theorem B1272023 : Blo 846354 1272023 := bstep (se 1 (by rfl) ⟨954017, by rfl⟩ : syracuseStep 1272023 = 1908035) B1908035
theorem B4286681 : Blo 846354 4286681 := bstep (se 2 (by rfl) ⟨1607505, by rfl⟩ : syracuseStep 4286681 = 3215011) B3215011
theorem B1272089 : Blo 846354 1272089 := bstep (se 2 (by rfl) ⟨477033, by rfl⟩ : syracuseStep 1272089 = 954067) B954067
theorem B1861913 : Blo 846354 1861913 := bstep (se 2 (by rfl) ⟨698217, by rfl⟩ : syracuseStep 1861913 = 1396435) B1396435
theorem B2713949 : Blo 846354 2713949 := bstep (se 3 (by rfl) ⟨508865, by rfl⟩ : syracuseStep 2713949 = 1017731) B1017731
theorem B1272203 : Blo 846354 1272203 := bstep (se 1 (by rfl) ⟨954152, by rfl⟩ : syracuseStep 1272203 = 1908305) B1908305
theorem B1272215 : Blo 846354 1272215 := bstep (se 1 (by rfl) ⟨954161, by rfl⟩ : syracuseStep 1272215 = 1908323) B1908323
theorem B1272281 : Blo 846354 1272281 := bstep (se 2 (by rfl) ⟨477105, by rfl⟩ : syracuseStep 1272281 = 954211) B954211
theorem B846359 : Blo 846354 846359 := bstep (se 1 (by rfl) ⟨634769, by rfl⟩ : syracuseStep 846359 = 1269539) B1269539
theorem B846379 : Blo 846354 846379 := bstep (se 1 (by rfl) ⟨634784, by rfl⟩ : syracuseStep 846379 = 1269569) B1269569
theorem B846391 : Blo 846354 846391 := bstep (se 1 (by rfl) ⟨634793, by rfl⟩ : syracuseStep 846391 = 1269587) B1269587
theorem B846411 : Blo 846354 846411 := bstep (se 1 (by rfl) ⟨634808, by rfl⟩ : syracuseStep 846411 = 1269617) B1269617
theorem B1272395 : Blo 846354 1272395 := bstep (se 1 (by rfl) ⟨954296, by rfl⟩ : syracuseStep 1272395 = 1908593) B1908593
theorem B846423 : Blo 846354 846423 := bstep (se 1 (by rfl) ⟨634817, by rfl⟩ : syracuseStep 846423 = 1269635) B1269635
theorem B1272407 : Blo 846354 1272407 := bstep (se 1 (by rfl) ⟨954305, by rfl⟩ : syracuseStep 1272407 = 1908611) B1908611
theorem B846443 : Blo 846354 846443 := bstep (se 1 (by rfl) ⟨634832, by rfl⟩ : syracuseStep 846443 = 1269665) B1269665
theorem B846455 : Blo 846354 846455 := bstep (se 1 (by rfl) ⟨634841, by rfl⟩ : syracuseStep 846455 = 1269683) B1269683
theorem B846475 : Blo 846354 846475 := bstep (se 1 (by rfl) ⟨634856, by rfl⟩ : syracuseStep 846475 = 1269713) B1269713
theorem B846487 : Blo 846354 846487 := bstep (se 1 (by rfl) ⟨634865, by rfl⟩ : syracuseStep 846487 = 1269731) B1269731
theorem B1272473 : Blo 846354 1272473 := bstep (se 2 (by rfl) ⟨477177, by rfl⟩ : syracuseStep 1272473 = 954355) B954355
theorem B846507 : Blo 846354 846507 := bstep (se 1 (by rfl) ⟨634880, by rfl⟩ : syracuseStep 846507 = 1269761) B1269761
theorem B846519 : Blo 846354 846519 := bstep (se 1 (by rfl) ⟨634889, by rfl⟩ : syracuseStep 846519 = 1269779) B1269779
theorem B846539 : Blo 846354 846539 := bstep (se 1 (by rfl) ⟨634904, by rfl⟩ : syracuseStep 846539 = 1269809) B1269809
theorem B846551 : Blo 846354 846551 := bstep (se 1 (by rfl) ⟨634913, by rfl⟩ : syracuseStep 846551 = 1269827) B1269827
theorem B846571 : Blo 846354 846571 := bstep (se 1 (by rfl) ⟨634928, by rfl⟩ : syracuseStep 846571 = 1269857) B1269857
theorem B846583 : Blo 846354 846583 := bstep (se 1 (by rfl) ⟨634937, by rfl⟩ : syracuseStep 846583 = 1269875) B1269875
theorem B3271427 : Blo 846354 3271427 := bstep (se 1 (by rfl) ⟨2453570, by rfl⟩ : syracuseStep 3271427 = 4907141) B4907141
theorem B846603 : Blo 846354 846603 := bstep (se 1 (by rfl) ⟨634952, by rfl⟩ : syracuseStep 846603 = 1269905) B1269905
theorem B1272587 : Blo 846354 1272587 := bstep (se 1 (by rfl) ⟨954440, by rfl⟩ : syracuseStep 1272587 = 1908881) B1908881
theorem B846615 : Blo 846354 846615 := bstep (se 1 (by rfl) ⟨634961, by rfl⟩ : syracuseStep 846615 = 1269923) B1269923
theorem B1272599 : Blo 846354 1272599 := bstep (se 1 (by rfl) ⟨954449, by rfl⟩ : syracuseStep 1272599 = 1908899) B1908899
theorem B846635 : Blo 846354 846635 := bstep (se 1 (by rfl) ⟨634976, by rfl⟩ : syracuseStep 846635 = 1269953) B1269953
theorem B846647 : Blo 846354 846647 := bstep (se 1 (by rfl) ⟨634985, by rfl⟩ : syracuseStep 846647 = 1269971) B1269971
theorem B846667 : Blo 846354 846667 := bstep (se 1 (by rfl) ⟨635000, by rfl⟩ : syracuseStep 846667 = 1270001) B1270001
theorem B846679 : Blo 846354 846679 := bstep (se 1 (by rfl) ⟨635009, by rfl⟩ : syracuseStep 846679 = 1270019) B1270019
theorem B1272665 : Blo 846354 1272665 := bstep (se 2 (by rfl) ⟨477249, by rfl⟩ : syracuseStep 1272665 = 954499) B954499
theorem B846699 : Blo 846354 846699 := bstep (se 1 (by rfl) ⟨635024, by rfl⟩ : syracuseStep 846699 = 1270049) B1270049
theorem B846711 : Blo 846354 846711 := bstep (se 1 (by rfl) ⟨635033, by rfl⟩ : syracuseStep 846711 = 1270067) B1270067
theorem B846731 : Blo 846354 846731 := bstep (se 1 (by rfl) ⟨635048, by rfl⟩ : syracuseStep 846731 = 1270097) B1270097
theorem B846743 : Blo 846354 846743 := bstep (se 1 (by rfl) ⟨635057, by rfl⟩ : syracuseStep 846743 = 1270115) B1270115
theorem B846763 : Blo 846354 846763 := bstep (se 1 (by rfl) ⟨635072, by rfl⟩ : syracuseStep 846763 = 1270145) B1270145
theorem B846775 : Blo 846354 846775 := bstep (se 1 (by rfl) ⟨635081, by rfl⟩ : syracuseStep 846775 = 1270163) B1270163
theorem B846795 : Blo 846354 846795 := bstep (se 1 (by rfl) ⟨635096, by rfl⟩ : syracuseStep 846795 = 1270193) B1270193
theorem B1272779 : Blo 846354 1272779 := bstep (se 1 (by rfl) ⟨954584, by rfl⟩ : syracuseStep 1272779 = 1909169) B1909169
theorem B846807 : Blo 846354 846807 := bstep (se 1 (by rfl) ⟨635105, by rfl⟩ : syracuseStep 846807 = 1270211) B1270211
theorem B1272791 : Blo 846354 1272791 := bstep (se 1 (by rfl) ⟨954593, by rfl⟩ : syracuseStep 1272791 = 1909187) B1909187
theorem B846827 : Blo 846354 846827 := bstep (se 1 (by rfl) ⟨635120, by rfl⟩ : syracuseStep 846827 = 1270241) B1270241
theorem B846839 : Blo 846354 846839 := bstep (se 1 (by rfl) ⟨635129, by rfl⟩ : syracuseStep 846839 = 1270259) B1270259
theorem B846859 : Blo 846354 846859 := bstep (se 1 (by rfl) ⟨635144, by rfl⟩ : syracuseStep 846859 = 1270289) B1270289
theorem B846871 : Blo 846354 846871 := bstep (se 1 (by rfl) ⟨635153, by rfl⟩ : syracuseStep 846871 = 1270307) B1270307
theorem B1272857 : Blo 846354 1272857 := bstep (se 2 (by rfl) ⟨477321, by rfl⟩ : syracuseStep 1272857 = 954643) B954643
theorem B9169955 : Blo 846354 9169955 := bstep (se 1 (by rfl) ⟨6877466, by rfl⟩ : syracuseStep 9169955 = 13754933) B13754933
theorem B846891 : Blo 846354 846891 := bstep (se 1 (by rfl) ⟨635168, by rfl⟩ : syracuseStep 846891 = 1270337) B1270337
theorem B846903 : Blo 846354 846903 := bstep (se 1 (by rfl) ⟨635177, by rfl⟩ : syracuseStep 846903 = 1270355) B1270355
theorem B846923 : Blo 846354 846923 := bstep (se 1 (by rfl) ⟨635192, by rfl⟩ : syracuseStep 846923 = 1270385) B1270385
theorem B846935 : Blo 846354 846935 := bstep (se 1 (by rfl) ⟨635201, by rfl⟩ : syracuseStep 846935 = 1270403) B1270403
theorem B2714717 : Blo 846354 2714717 := bstep (se 3 (by rfl) ⟨509009, by rfl⟩ : syracuseStep 2714717 = 1018019) B1018019
theorem B846955 : Blo 846354 846955 := bstep (se 1 (by rfl) ⟨635216, by rfl⟩ : syracuseStep 846955 = 1270433) B1270433
theorem B846967 : Blo 846354 846967 := bstep (se 1 (by rfl) ⟨635225, by rfl⟩ : syracuseStep 846967 = 1270451) B1270451
theorem B846987 : Blo 846354 846987 := bstep (se 1 (by rfl) ⟨635240, by rfl⟩ : syracuseStep 846987 = 1270481) B1270481
theorem B1272971 : Blo 846354 1272971 := bstep (se 1 (by rfl) ⟨954728, by rfl⟩ : syracuseStep 1272971 = 1909457) B1909457
theorem B846999 : Blo 846354 846999 := bstep (se 1 (by rfl) ⟨635249, by rfl⟩ : syracuseStep 846999 = 1270499) B1270499
theorem B1272983 : Blo 846354 1272983 := bstep (se 1 (by rfl) ⟨954737, by rfl⟩ : syracuseStep 1272983 = 1909475) B1909475
theorem B847019 : Blo 846354 847019 := bstep (se 1 (by rfl) ⟨635264, by rfl⟩ : syracuseStep 847019 = 1270529) B1270529
theorem B2092211 : Blo 846354 2092211 := bstep (se 1 (by rfl) ⟨1569158, by rfl⟩ : syracuseStep 2092211 = 3138317) B3138317
theorem B847031 : Blo 846354 847031 := bstep (se 1 (by rfl) ⟨635273, by rfl⟩ : syracuseStep 847031 = 1270547) B1270547
theorem B847051 : Blo 846354 847051 := bstep (se 1 (by rfl) ⟨635288, by rfl⟩ : syracuseStep 847051 = 1270577) B1270577
theorem B847063 : Blo 846354 847063 := bstep (se 1 (by rfl) ⟨635297, by rfl⟩ : syracuseStep 847063 = 1270595) B1270595
theorem B1273049 : Blo 846354 1273049 := bstep (se 2 (by rfl) ⟨477393, by rfl⟩ : syracuseStep 1273049 = 954787) B954787
theorem B2583769 : Blo 846354 2583769 := bstep (se 2 (by rfl) ⟨968913, by rfl⟩ : syracuseStep 2583769 = 1937827) B1937827
theorem B847083 : Blo 846354 847083 := bstep (se 1 (by rfl) ⟨635312, by rfl⟩ : syracuseStep 847083 = 1270625) B1270625
theorem B847095 : Blo 846354 847095 := bstep (se 1 (by rfl) ⟨635321, by rfl⟩ : syracuseStep 847095 = 1270643) B1270643
theorem B847115 : Blo 846354 847115 := bstep (se 1 (by rfl) ⟨635336, by rfl⟩ : syracuseStep 847115 = 1270673) B1270673
theorem B847127 : Blo 846354 847127 := bstep (se 1 (by rfl) ⟨635345, by rfl⟩ : syracuseStep 847127 = 1270691) B1270691
theorem B847147 : Blo 846354 847147 := bstep (se 1 (by rfl) ⟨635360, by rfl⟩ : syracuseStep 847147 = 1270721) B1270721
theorem B847159 : Blo 846354 847159 := bstep (se 1 (by rfl) ⟨635369, by rfl⟩ : syracuseStep 847159 = 1270739) B1270739
theorem B847179 : Blo 846354 847179 := bstep (se 1 (by rfl) ⟨635384, by rfl⟩ : syracuseStep 847179 = 1270769) B1270769
theorem B1273163 : Blo 846354 1273163 := bstep (se 1 (by rfl) ⟨954872, by rfl⟩ : syracuseStep 1273163 = 1909745) B1909745
theorem B847191 : Blo 846354 847191 := bstep (se 1 (by rfl) ⟨635393, by rfl⟩ : syracuseStep 847191 = 1270787) B1270787
theorem B1273175 : Blo 846354 1273175 := bstep (se 1 (by rfl) ⟨954881, by rfl⟩ : syracuseStep 1273175 = 1909763) B1909763
theorem B847211 : Blo 846354 847211 := bstep (se 1 (by rfl) ⟨635408, by rfl⟩ : syracuseStep 847211 = 1270817) B1270817
theorem B847223 : Blo 846354 847223 := bstep (se 1 (by rfl) ⟨635417, by rfl⟩ : syracuseStep 847223 = 1270835) B1270835
theorem B847243 : Blo 846354 847243 := bstep (se 1 (by rfl) ⟨635432, by rfl⟩ : syracuseStep 847243 = 1270865) B1270865
theorem B847255 : Blo 846354 847255 := bstep (se 1 (by rfl) ⟨635441, by rfl⟩ : syracuseStep 847255 = 1270883) B1270883
theorem B1273241 : Blo 846354 1273241 := bstep (se 2 (by rfl) ⟨477465, by rfl⟩ : syracuseStep 1273241 = 954931) B954931
theorem B847275 : Blo 846354 847275 := bstep (se 1 (by rfl) ⟨635456, by rfl⟩ : syracuseStep 847275 = 1270913) B1270913
theorem B847287 : Blo 846354 847287 := bstep (se 1 (by rfl) ⟨635465, by rfl⟩ : syracuseStep 847287 = 1270931) B1270931
theorem B847307 : Blo 846354 847307 := bstep (se 1 (by rfl) ⟨635480, by rfl⟩ : syracuseStep 847307 = 1270961) B1270961
theorem B847319 : Blo 846354 847319 := bstep (se 1 (by rfl) ⟨635489, by rfl⟩ : syracuseStep 847319 = 1270979) B1270979
theorem B2420189 : Blo 846354 2420189 := bstep (se 3 (by rfl) ⟨453785, by rfl⟩ : syracuseStep 2420189 = 907571) B907571
theorem B847339 : Blo 846354 847339 := bstep (se 1 (by rfl) ⟨635504, by rfl⟩ : syracuseStep 847339 = 1271009) B1271009
theorem B847351 : Blo 846354 847351 := bstep (se 1 (by rfl) ⟨635513, by rfl⟩ : syracuseStep 847351 = 1271027) B1271027
theorem B847371 : Blo 846354 847371 := bstep (se 1 (by rfl) ⟨635528, by rfl⟩ : syracuseStep 847371 = 1271057) B1271057
theorem B1273355 : Blo 846354 1273355 := bstep (se 1 (by rfl) ⟨955016, by rfl⟩ : syracuseStep 1273355 = 1910033) B1910033
theorem B847383 : Blo 846354 847383 := bstep (se 1 (by rfl) ⟨635537, by rfl⟩ : syracuseStep 847383 = 1271075) B1271075
theorem B1273367 : Blo 846354 1273367 := bstep (se 1 (by rfl) ⟨955025, by rfl⟩ : syracuseStep 1273367 = 1910051) B1910051
theorem B847403 : Blo 846354 847403 := bstep (se 1 (by rfl) ⟨635552, by rfl⟩ : syracuseStep 847403 = 1271105) B1271105
theorem B847415 : Blo 846354 847415 := bstep (se 1 (by rfl) ⟨635561, by rfl⟩ : syracuseStep 847415 = 1271123) B1271123
theorem B847435 : Blo 846354 847435 := bstep (se 1 (by rfl) ⟨635576, by rfl⟩ : syracuseStep 847435 = 1271153) B1271153
theorem B847447 : Blo 846354 847447 := bstep (se 1 (by rfl) ⟨635585, by rfl⟩ : syracuseStep 847447 = 1271171) B1271171
theorem B1273433 : Blo 846354 1273433 := bstep (se 2 (by rfl) ⟨477537, by rfl⟩ : syracuseStep 1273433 = 955075) B955075
theorem B2715229 : Blo 846354 2715229 := bstep (se 3 (by rfl) ⟨509105, by rfl⟩ : syracuseStep 2715229 = 1018211) B1018211
theorem B847467 : Blo 846354 847467 := bstep (se 1 (by rfl) ⟨635600, by rfl⟩ : syracuseStep 847467 = 1271201) B1271201
theorem B847479 : Blo 846354 847479 := bstep (se 1 (by rfl) ⟨635609, by rfl⟩ : syracuseStep 847479 = 1271219) B1271219
theorem B847499 : Blo 846354 847499 := bstep (se 1 (by rfl) ⟨635624, by rfl⟩ : syracuseStep 847499 = 1271249) B1271249
theorem B847511 : Blo 846354 847511 := bstep (se 1 (by rfl) ⟨635633, by rfl⟩ : syracuseStep 847511 = 1271267) B1271267
theorem B847531 : Blo 846354 847531 := bstep (se 1 (by rfl) ⟨635648, by rfl⟩ : syracuseStep 847531 = 1271297) B1271297
theorem B847543 : Blo 846354 847543 := bstep (se 1 (by rfl) ⟨635657, by rfl⟩ : syracuseStep 847543 = 1271315) B1271315
theorem B2420417 : Blo 846354 2420417 := bstep (se 2 (by rfl) ⟨907656, by rfl⟩ : syracuseStep 2420417 = 1815313) B1815313
theorem B847563 : Blo 846354 847563 := bstep (se 1 (by rfl) ⟨635672, by rfl⟩ : syracuseStep 847563 = 1271345) B1271345
theorem B1273547 : Blo 846354 1273547 := bstep (se 1 (by rfl) ⟨955160, by rfl⟩ : syracuseStep 1273547 = 1910321) B1910321
theorem B1273559 : Blo 846354 1273559 := bstep (se 1 (by rfl) ⟨955169, by rfl⟩ : syracuseStep 1273559 = 1910339) B1910339
theorem B847575 : Blo 846354 847575 := bstep (se 1 (by rfl) ⟨635681, by rfl⟩ : syracuseStep 847575 = 1271363) B1271363
theorem B847595 : Blo 846354 847595 := bstep (se 1 (by rfl) ⟨635696, by rfl⟩ : syracuseStep 847595 = 1271393) B1271393
theorem B847607 : Blo 846354 847607 := bstep (se 1 (by rfl) ⟨635705, by rfl⟩ : syracuseStep 847607 = 1271411) B1271411
theorem B847627 : Blo 846354 847627 := bstep (se 1 (by rfl) ⟨635720, by rfl⟩ : syracuseStep 847627 = 1271441) B1271441
theorem B847639 : Blo 846354 847639 := bstep (se 1 (by rfl) ⟨635729, by rfl⟩ : syracuseStep 847639 = 1271459) B1271459
theorem B1273625 : Blo 846354 1273625 := bstep (se 2 (by rfl) ⟨477609, by rfl⟩ : syracuseStep 1273625 = 955219) B955219
theorem B847659 : Blo 846354 847659 := bstep (se 1 (by rfl) ⟨635744, by rfl⟩ : syracuseStep 847659 = 1271489) B1271489
theorem B4288301 : Blo 846354 4288301 := bstep (se 3 (by rfl) ⟨804056, by rfl⟩ : syracuseStep 4288301 = 1608113) B1608113
theorem B847671 : Blo 846354 847671 := bstep (se 1 (by rfl) ⟨635753, by rfl⟩ : syracuseStep 847671 = 1271507) B1271507
theorem B847691 : Blo 846354 847691 := bstep (se 1 (by rfl) ⟨635768, by rfl⟩ : syracuseStep 847691 = 1271537) B1271537
theorem B847703 : Blo 846354 847703 := bstep (se 1 (by rfl) ⟨635777, by rfl⟩ : syracuseStep 847703 = 1271555) B1271555
theorem B847723 : Blo 846354 847723 := bstep (se 1 (by rfl) ⟨635792, by rfl⟩ : syracuseStep 847723 = 1271585) B1271585
theorem B847735 : Blo 846354 847735 := bstep (se 1 (by rfl) ⟨635801, by rfl⟩ : syracuseStep 847735 = 1271603) B1271603
theorem B847755 : Blo 846354 847755 := bstep (se 1 (by rfl) ⟨635816, by rfl⟩ : syracuseStep 847755 = 1271633) B1271633
theorem B1273739 : Blo 846354 1273739 := bstep (se 1 (by rfl) ⟨955304, by rfl⟩ : syracuseStep 1273739 = 1910609) B1910609
theorem B847767 : Blo 846354 847767 := bstep (se 1 (by rfl) ⟨635825, by rfl⟩ : syracuseStep 847767 = 1271651) B1271651
theorem B1273751 : Blo 846354 1273751 := bstep (se 1 (by rfl) ⟨955313, by rfl⟩ : syracuseStep 1273751 = 1910627) B1910627
theorem B847787 : Blo 846354 847787 := bstep (se 1 (by rfl) ⟨635840, by rfl⟩ : syracuseStep 847787 = 1271681) B1271681
theorem B26079155 : Blo 846354 26079155 := bstep (se 1 (by rfl) ⟨19559366, by rfl⟩ : syracuseStep 26079155 = 39118733) B39118733
theorem B847799 : Blo 846354 847799 := bstep (se 1 (by rfl) ⟨635849, by rfl⟩ : syracuseStep 847799 = 1271699) B1271699
theorem B847819 : Blo 846354 847819 := bstep (se 1 (by rfl) ⟨635864, by rfl⟩ : syracuseStep 847819 = 1271729) B1271729
theorem B847831 : Blo 846354 847831 := bstep (se 1 (by rfl) ⟨635873, by rfl⟩ : syracuseStep 847831 = 1271747) B1271747
theorem B1273817 : Blo 846354 1273817 := bstep (se 2 (by rfl) ⟨477681, by rfl⟩ : syracuseStep 1273817 = 955363) B955363
theorem B847851 : Blo 846354 847851 := bstep (se 1 (by rfl) ⟨635888, by rfl⟩ : syracuseStep 847851 = 1271777) B1271777
theorem B847863 : Blo 846354 847863 := bstep (se 1 (by rfl) ⟨635897, by rfl⟩ : syracuseStep 847863 = 1271795) B1271795
theorem B847883 : Blo 846354 847883 := bstep (se 1 (by rfl) ⟨635912, by rfl⟩ : syracuseStep 847883 = 1271825) B1271825
theorem B847895 : Blo 846354 847895 := bstep (se 1 (by rfl) ⟨635921, by rfl⟩ : syracuseStep 847895 = 1271843) B1271843
theorem B2420759 : Blo 846354 2420759 := bstep (se 1 (by rfl) ⟨1815569, by rfl⟩ : syracuseStep 2420759 = 3631139) B3631139
theorem B847915 : Blo 846354 847915 := bstep (se 1 (by rfl) ⟨635936, by rfl⟩ : syracuseStep 847915 = 1271873) B1271873
theorem B847927 : Blo 846354 847927 := bstep (se 1 (by rfl) ⟨635945, by rfl⟩ : syracuseStep 847927 = 1271891) B1271891
theorem B847947 : Blo 846354 847947 := bstep (se 1 (by rfl) ⟨635960, by rfl⟩ : syracuseStep 847947 = 1271921) B1271921
theorem B1273931 : Blo 846354 1273931 := bstep (se 1 (by rfl) ⟨955448, by rfl⟩ : syracuseStep 1273931 = 1910897) B1910897
theorem B847959 : Blo 846354 847959 := bstep (se 1 (by rfl) ⟨635969, by rfl⟩ : syracuseStep 847959 = 1271939) B1271939
theorem B1273943 : Blo 846354 1273943 := bstep (se 1 (by rfl) ⟨955457, by rfl⟩ : syracuseStep 1273943 = 1910915) B1910915
theorem B847979 : Blo 846354 847979 := bstep (se 1 (by rfl) ⟨635984, by rfl⟩ : syracuseStep 847979 = 1271969) B1271969
theorem B847991 : Blo 846354 847991 := bstep (se 1 (by rfl) ⟨635993, by rfl⟩ : syracuseStep 847991 = 1271987) B1271987
theorem B848011 : Blo 846354 848011 := bstep (se 1 (by rfl) ⟨636008, by rfl⟩ : syracuseStep 848011 = 1272017) B1272017
theorem B848023 : Blo 846354 848023 := bstep (se 1 (by rfl) ⟨636017, by rfl⟩ : syracuseStep 848023 = 1272035) B1272035
theorem B1274009 : Blo 846354 1274009 := bstep (se 2 (by rfl) ⟨477753, by rfl⟩ : syracuseStep 1274009 = 955507) B955507
theorem B848043 : Blo 846354 848043 := bstep (se 1 (by rfl) ⟨636032, by rfl⟩ : syracuseStep 848043 = 1272065) B1272065
theorem B848055 : Blo 846354 848055 := bstep (se 1 (by rfl) ⟨636041, by rfl⟩ : syracuseStep 848055 = 1272083) B1272083
theorem B848075 : Blo 846354 848075 := bstep (se 1 (by rfl) ⟨636056, by rfl⟩ : syracuseStep 848075 = 1272113) B1272113
theorem B848087 : Blo 846354 848087 := bstep (se 1 (by rfl) ⟨636065, by rfl⟩ : syracuseStep 848087 = 1272131) B1272131
theorem B848107 : Blo 846354 848107 := bstep (se 1 (by rfl) ⟨636080, by rfl⟩ : syracuseStep 848107 = 1272161) B1272161
theorem B848119 : Blo 846354 848119 := bstep (se 1 (by rfl) ⟨636089, by rfl⟩ : syracuseStep 848119 = 1272179) B1272179
theorem B848139 : Blo 846354 848139 := bstep (se 1 (by rfl) ⟨636104, by rfl⟩ : syracuseStep 848139 = 1272209) B1272209
theorem B1274123 : Blo 846354 1274123 := bstep (se 1 (by rfl) ⟨955592, by rfl⟩ : syracuseStep 1274123 = 1911185) B1911185
theorem B848151 : Blo 846354 848151 := bstep (se 1 (by rfl) ⟨636113, by rfl⟩ : syracuseStep 848151 = 1272227) B1272227
theorem B1274135 : Blo 846354 1274135 := bstep (se 1 (by rfl) ⟨955601, by rfl⟩ : syracuseStep 1274135 = 1911203) B1911203
theorem B848171 : Blo 846354 848171 := bstep (se 1 (by rfl) ⟨636128, by rfl⟩ : syracuseStep 848171 = 1272257) B1272257
theorem B848183 : Blo 846354 848183 := bstep (se 1 (by rfl) ⟨636137, by rfl⟩ : syracuseStep 848183 = 1272275) B1272275
theorem B5796161 : Blo 846354 5796161 := bstep (se 2 (by rfl) ⟨2173560, by rfl⟩ : syracuseStep 5796161 = 4347121) B4347121
theorem B848203 : Blo 846354 848203 := bstep (se 1 (by rfl) ⟨636152, by rfl⟩ : syracuseStep 848203 = 1272305) B1272305
theorem B848215 : Blo 846354 848215 := bstep (se 1 (by rfl) ⟨636161, by rfl⟩ : syracuseStep 848215 = 1272323) B1272323
theorem B1274201 : Blo 846354 1274201 := bstep (se 2 (by rfl) ⟨477825, by rfl⟩ : syracuseStep 1274201 = 955651) B955651
theorem B848235 : Blo 846354 848235 := bstep (se 1 (by rfl) ⟨636176, by rfl⟩ : syracuseStep 848235 = 1272353) B1272353
theorem B848247 : Blo 846354 848247 := bstep (se 1 (by rfl) ⟨636185, by rfl⟩ : syracuseStep 848247 = 1272371) B1272371
theorem B848267 : Blo 846354 848267 := bstep (se 1 (by rfl) ⟨636200, by rfl⟩ : syracuseStep 848267 = 1272401) B1272401
theorem B848279 : Blo 846354 848279 := bstep (se 1 (by rfl) ⟨636209, by rfl⟩ : syracuseStep 848279 = 1272419) B1272419
theorem B848299 : Blo 846354 848299 := bstep (se 1 (by rfl) ⟨636224, by rfl⟩ : syracuseStep 848299 = 1272449) B1272449
theorem B848311 : Blo 846354 848311 := bstep (se 1 (by rfl) ⟨636233, by rfl⟩ : syracuseStep 848311 = 1272467) B1272467
theorem B848331 : Blo 846354 848331 := bstep (se 1 (by rfl) ⟨636248, by rfl⟩ : syracuseStep 848331 = 1272497) B1272497
theorem B1274315 : Blo 846354 1274315 := bstep (se 1 (by rfl) ⟨955736, by rfl⟩ : syracuseStep 1274315 = 1911473) B1911473
theorem B848343 : Blo 846354 848343 := bstep (se 1 (by rfl) ⟨636257, by rfl⟩ : syracuseStep 848343 = 1272515) B1272515
theorem B1274327 : Blo 846354 1274327 := bstep (se 1 (by rfl) ⟨955745, by rfl⟩ : syracuseStep 1274327 = 1911491) B1911491
theorem B848363 : Blo 846354 848363 := bstep (se 1 (by rfl) ⟨636272, by rfl⟩ : syracuseStep 848363 = 1272545) B1272545
theorem B848375 : Blo 846354 848375 := bstep (se 1 (by rfl) ⟨636281, by rfl⟩ : syracuseStep 848375 = 1272563) B1272563
theorem B848395 : Blo 846354 848395 := bstep (se 1 (by rfl) ⟨636296, by rfl⟩ : syracuseStep 848395 = 1272593) B1272593
theorem B848407 : Blo 846354 848407 := bstep (se 1 (by rfl) ⟨636305, by rfl⟩ : syracuseStep 848407 = 1272611) B1272611
theorem B1274393 : Blo 846354 1274393 := bstep (se 2 (by rfl) ⟨477897, by rfl⟩ : syracuseStep 1274393 = 955795) B955795
theorem B848427 : Blo 846354 848427 := bstep (se 1 (by rfl) ⟨636320, by rfl⟩ : syracuseStep 848427 = 1272641) B1272641
theorem B848439 : Blo 846354 848439 := bstep (se 1 (by rfl) ⟨636329, by rfl⟩ : syracuseStep 848439 = 1272659) B1272659
theorem B848459 : Blo 846354 848459 := bstep (se 1 (by rfl) ⟨636344, by rfl⟩ : syracuseStep 848459 = 1272689) B1272689
theorem B848471 : Blo 846354 848471 := bstep (se 1 (by rfl) ⟨636353, by rfl⟩ : syracuseStep 848471 = 1272707) B1272707
theorem B848491 : Blo 846354 848491 := bstep (se 1 (by rfl) ⟨636368, by rfl⟩ : syracuseStep 848491 = 1272737) B1272737
theorem B848503 : Blo 846354 848503 := bstep (se 1 (by rfl) ⟨636377, by rfl⟩ : syracuseStep 848503 = 1272755) B1272755
theorem B848523 : Blo 846354 848523 := bstep (se 1 (by rfl) ⟨636392, by rfl⟩ : syracuseStep 848523 = 1272785) B1272785
theorem B1274507 : Blo 846354 1274507 := bstep (se 1 (by rfl) ⟨955880, by rfl⟩ : syracuseStep 1274507 = 1911761) B1911761
theorem B848535 : Blo 846354 848535 := bstep (se 1 (by rfl) ⟨636401, by rfl⟩ : syracuseStep 848535 = 1272803) B1272803
theorem B1274519 : Blo 846354 1274519 := bstep (se 1 (by rfl) ⟨955889, by rfl⟩ : syracuseStep 1274519 = 1911779) B1911779
theorem B848555 : Blo 846354 848555 := bstep (se 1 (by rfl) ⟨636416, by rfl⟩ : syracuseStep 848555 = 1272833) B1272833
theorem B848567 : Blo 846354 848567 := bstep (se 1 (by rfl) ⟨636425, by rfl⟩ : syracuseStep 848567 = 1272851) B1272851
theorem B848587 : Blo 846354 848587 := bstep (se 1 (by rfl) ⟨636440, by rfl⟩ : syracuseStep 848587 = 1272881) B1272881
theorem B848599 : Blo 846354 848599 := bstep (se 1 (by rfl) ⟨636449, by rfl⟩ : syracuseStep 848599 = 1272899) B1272899
theorem B1274585 : Blo 846354 1274585 := bstep (se 2 (by rfl) ⟨477969, by rfl⟩ : syracuseStep 1274585 = 955939) B955939
theorem B848619 : Blo 846354 848619 := bstep (se 1 (by rfl) ⟨636464, by rfl⟩ : syracuseStep 848619 = 1272929) B1272929
theorem B848631 : Blo 846354 848631 := bstep (se 1 (by rfl) ⟨636473, by rfl⟩ : syracuseStep 848631 = 1272947) B1272947
theorem B848651 : Blo 846354 848651 := bstep (se 1 (by rfl) ⟨636488, by rfl⟩ : syracuseStep 848651 = 1272977) B1272977
theorem B848663 : Blo 846354 848663 := bstep (se 1 (by rfl) ⟨636497, by rfl⟩ : syracuseStep 848663 = 1272995) B1272995
theorem B848683 : Blo 846354 848683 := bstep (se 1 (by rfl) ⟨636512, by rfl⟩ : syracuseStep 848683 = 1273025) B1273025
theorem B848695 : Blo 846354 848695 := bstep (se 1 (by rfl) ⟨636521, by rfl⟩ : syracuseStep 848695 = 1273043) B1273043
theorem B848715 : Blo 846354 848715 := bstep (se 1 (by rfl) ⟨636536, by rfl⟩ : syracuseStep 848715 = 1273073) B1273073
theorem B1274699 : Blo 846354 1274699 := bstep (se 1 (by rfl) ⟨956024, by rfl⟩ : syracuseStep 1274699 = 1912049) B1912049
theorem B848727 : Blo 846354 848727 := bstep (se 1 (by rfl) ⟨636545, by rfl⟩ : syracuseStep 848727 = 1273091) B1273091
theorem B1274711 : Blo 846354 1274711 := bstep (se 1 (by rfl) ⟨956033, by rfl⟩ : syracuseStep 1274711 = 1912067) B1912067
theorem B848747 : Blo 846354 848747 := bstep (se 1 (by rfl) ⟨636560, by rfl⟩ : syracuseStep 848747 = 1273121) B1273121
theorem B848759 : Blo 846354 848759 := bstep (se 1 (by rfl) ⟨636569, by rfl⟩ : syracuseStep 848759 = 1273139) B1273139
theorem B848779 : Blo 846354 848779 := bstep (se 1 (by rfl) ⟨636584, by rfl⟩ : syracuseStep 848779 = 1273169) B1273169
theorem B848791 : Blo 846354 848791 := bstep (se 1 (by rfl) ⟨636593, by rfl⟩ : syracuseStep 848791 = 1273187) B1273187
theorem B1274777 : Blo 846354 1274777 := bstep (se 2 (by rfl) ⟨478041, by rfl⟩ : syracuseStep 1274777 = 956083) B956083
theorem B848811 : Blo 846354 848811 := bstep (se 1 (by rfl) ⟨636608, by rfl⟩ : syracuseStep 848811 = 1273217) B1273217
theorem B848823 : Blo 846354 848823 := bstep (se 1 (by rfl) ⟨636617, by rfl⟩ : syracuseStep 848823 = 1273235) B1273235
theorem B848843 : Blo 846354 848843 := bstep (se 1 (by rfl) ⟨636632, by rfl⟩ : syracuseStep 848843 = 1273265) B1273265
theorem B848855 : Blo 846354 848855 := bstep (se 1 (by rfl) ⟨636641, by rfl⟩ : syracuseStep 848855 = 1273283) B1273283
theorem B2618333 : Blo 846354 2618333 := bstep (se 3 (by rfl) ⟨490937, by rfl⟩ : syracuseStep 2618333 = 981875) B981875
theorem B848875 : Blo 846354 848875 := bstep (se 1 (by rfl) ⟨636656, by rfl⟩ : syracuseStep 848875 = 1273313) B1273313
theorem B848887 : Blo 846354 848887 := bstep (se 1 (by rfl) ⟨636665, by rfl⟩ : syracuseStep 848887 = 1273331) B1273331
theorem B848907 : Blo 846354 848907 := bstep (se 1 (by rfl) ⟨636680, by rfl⟩ : syracuseStep 848907 = 1273361) B1273361
theorem B1274891 : Blo 846354 1274891 := bstep (se 1 (by rfl) ⟨956168, by rfl⟩ : syracuseStep 1274891 = 1912337) B1912337
theorem B848919 : Blo 846354 848919 := bstep (se 1 (by rfl) ⟨636689, by rfl⟩ : syracuseStep 848919 = 1273379) B1273379
theorem B1274903 : Blo 846354 1274903 := bstep (se 1 (by rfl) ⟨956177, by rfl⟩ : syracuseStep 1274903 = 1912355) B1912355
theorem B848939 : Blo 846354 848939 := bstep (se 1 (by rfl) ⟨636704, by rfl⟩ : syracuseStep 848939 = 1273409) B1273409
theorem B848951 : Blo 846354 848951 := bstep (se 1 (by rfl) ⟨636713, by rfl⟩ : syracuseStep 848951 = 1273427) B1273427
theorem B848971 : Blo 846354 848971 := bstep (se 1 (by rfl) ⟨636728, by rfl⟩ : syracuseStep 848971 = 1273457) B1273457
theorem B848983 : Blo 846354 848983 := bstep (se 1 (by rfl) ⟨636737, by rfl⟩ : syracuseStep 848983 = 1273475) B1273475
theorem B1274969 : Blo 846354 1274969 := bstep (se 2 (by rfl) ⟨478113, by rfl⟩ : syracuseStep 1274969 = 956227) B956227
theorem B849003 : Blo 846354 849003 := bstep (se 1 (by rfl) ⟨636752, by rfl⟩ : syracuseStep 849003 = 1273505) B1273505
theorem B849015 : Blo 846354 849015 := bstep (se 1 (by rfl) ⟨636761, by rfl⟩ : syracuseStep 849015 = 1273523) B1273523
theorem B849035 : Blo 846354 849035 := bstep (se 1 (by rfl) ⟨636776, by rfl⟩ : syracuseStep 849035 = 1273553) B1273553
theorem B849047 : Blo 846354 849047 := bstep (se 1 (by rfl) ⟨636785, by rfl⟩ : syracuseStep 849047 = 1273571) B1273571
theorem B849067 : Blo 846354 849067 := bstep (se 1 (by rfl) ⟨636800, by rfl⟩ : syracuseStep 849067 = 1273601) B1273601
theorem B849079 : Blo 846354 849079 := bstep (se 1 (by rfl) ⟨636809, by rfl⟩ : syracuseStep 849079 = 1273619) B1273619
theorem B849099 : Blo 846354 849099 := bstep (se 1 (by rfl) ⟨636824, by rfl⟩ : syracuseStep 849099 = 1273649) B1273649
theorem B1275083 : Blo 846354 1275083 := bstep (se 1 (by rfl) ⟨956312, by rfl⟩ : syracuseStep 1275083 = 1912625) B1912625
theorem B849111 : Blo 846354 849111 := bstep (se 1 (by rfl) ⟨636833, by rfl⟩ : syracuseStep 849111 = 1273667) B1273667
theorem B1275095 : Blo 846354 1275095 := bstep (se 1 (by rfl) ⟨956321, by rfl⟩ : syracuseStep 1275095 = 1912643) B1912643
theorem B849131 : Blo 846354 849131 := bstep (se 1 (by rfl) ⟨636848, by rfl⟩ : syracuseStep 849131 = 1273697) B1273697
theorem B849143 : Blo 846354 849143 := bstep (se 1 (by rfl) ⟨636857, by rfl⟩ : syracuseStep 849143 = 1273715) B1273715
theorem B849163 : Blo 846354 849163 := bstep (se 1 (by rfl) ⟨636872, by rfl⟩ : syracuseStep 849163 = 1273745) B1273745
theorem B849175 : Blo 846354 849175 := bstep (se 1 (by rfl) ⟨636881, by rfl⟩ : syracuseStep 849175 = 1273763) B1273763
theorem B1275161 : Blo 846354 1275161 := bstep (se 2 (by rfl) ⟨478185, by rfl⟩ : syracuseStep 1275161 = 956371) B956371
theorem B849195 : Blo 846354 849195 := bstep (se 1 (by rfl) ⟨636896, by rfl⟩ : syracuseStep 849195 = 1273793) B1273793
theorem B849207 : Blo 846354 849207 := bstep (se 1 (by rfl) ⟨636905, by rfl⟩ : syracuseStep 849207 = 1273811) B1273811
theorem B849227 : Blo 846354 849227 := bstep (se 1 (by rfl) ⟨636920, by rfl⟩ : syracuseStep 849227 = 1273841) B1273841
theorem B849239 : Blo 846354 849239 := bstep (se 1 (by rfl) ⟨636929, by rfl⟩ : syracuseStep 849239 = 1273859) B1273859
theorem B849259 : Blo 846354 849259 := bstep (se 1 (by rfl) ⟨636944, by rfl⟩ : syracuseStep 849259 = 1273889) B1273889
theorem B849271 : Blo 846354 849271 := bstep (se 1 (by rfl) ⟨636953, by rfl⟩ : syracuseStep 849271 = 1273907) B1273907
theorem B849291 : Blo 846354 849291 := bstep (se 1 (by rfl) ⟨636968, by rfl⟩ : syracuseStep 849291 = 1273937) B1273937
theorem B1275275 : Blo 846354 1275275 := bstep (se 1 (by rfl) ⟨956456, by rfl⟩ : syracuseStep 1275275 = 1912913) B1912913
theorem B849303 : Blo 846354 849303 := bstep (se 1 (by rfl) ⟨636977, by rfl⟩ : syracuseStep 849303 = 1273955) B1273955
theorem B1275287 : Blo 846354 1275287 := bstep (se 1 (by rfl) ⟨956465, by rfl⟩ : syracuseStep 1275287 = 1912931) B1912931
theorem B849323 : Blo 846354 849323 := bstep (se 1 (by rfl) ⟨636992, by rfl⟩ : syracuseStep 849323 = 1273985) B1273985
theorem B849335 : Blo 846354 849335 := bstep (se 1 (by rfl) ⟨637001, by rfl⟩ : syracuseStep 849335 = 1274003) B1274003
theorem B849355 : Blo 846354 849355 := bstep (se 1 (by rfl) ⟨637016, by rfl⟩ : syracuseStep 849355 = 1274033) B1274033
theorem B849367 : Blo 846354 849367 := bstep (se 1 (by rfl) ⟨637025, by rfl⟩ : syracuseStep 849367 = 1274051) B1274051
theorem B1275353 : Blo 846354 1275353 := bstep (se 2 (by rfl) ⟨478257, by rfl⟩ : syracuseStep 1275353 = 956515) B956515
theorem B849387 : Blo 846354 849387 := bstep (se 1 (by rfl) ⟨637040, by rfl⟩ : syracuseStep 849387 = 1274081) B1274081
theorem B849399 : Blo 846354 849399 := bstep (se 1 (by rfl) ⟨637049, by rfl⟩ : syracuseStep 849399 = 1274099) B1274099
theorem B849419 : Blo 846354 849419 := bstep (se 1 (by rfl) ⟨637064, by rfl⟩ : syracuseStep 849419 = 1274129) B1274129
theorem B849431 : Blo 846354 849431 := bstep (se 1 (by rfl) ⟨637073, by rfl⟩ : syracuseStep 849431 = 1274147) B1274147
theorem B849451 : Blo 846354 849451 := bstep (se 1 (by rfl) ⟨637088, by rfl⟩ : syracuseStep 849451 = 1274177) B1274177
theorem B849463 : Blo 846354 849463 := bstep (se 1 (by rfl) ⟨637097, by rfl⟩ : syracuseStep 849463 = 1274195) B1274195
theorem B849483 : Blo 846354 849483 := bstep (se 1 (by rfl) ⟨637112, by rfl⟩ : syracuseStep 849483 = 1274225) B1274225
theorem B1275467 : Blo 846354 1275467 := bstep (se 1 (by rfl) ⟨956600, by rfl⟩ : syracuseStep 1275467 = 1913201) B1913201
theorem B849495 : Blo 846354 849495 := bstep (se 1 (by rfl) ⟨637121, by rfl⟩ : syracuseStep 849495 = 1274243) B1274243
theorem B1275479 : Blo 846354 1275479 := bstep (se 1 (by rfl) ⟨956609, by rfl⟩ : syracuseStep 1275479 = 1913219) B1913219
theorem B2487901 : Blo 846354 2487901 := bstep (se 3 (by rfl) ⟨466481, by rfl⟩ : syracuseStep 2487901 = 932963) B932963
theorem B849515 : Blo 846354 849515 := bstep (se 1 (by rfl) ⟨637136, by rfl⟩ : syracuseStep 849515 = 1274273) B1274273
theorem B849527 : Blo 846354 849527 := bstep (se 1 (by rfl) ⟨637145, by rfl⟩ : syracuseStep 849527 = 1274291) B1274291
theorem B849547 : Blo 846354 849547 := bstep (se 1 (by rfl) ⟨637160, by rfl⟩ : syracuseStep 849547 = 1274321) B1274321
theorem B849559 : Blo 846354 849559 := bstep (se 1 (by rfl) ⟨637169, by rfl⟩ : syracuseStep 849559 = 1274339) B1274339
theorem B849579 : Blo 846354 849579 := bstep (se 1 (by rfl) ⟨637184, by rfl⟩ : syracuseStep 849579 = 1274369) B1274369
theorem B849591 : Blo 846354 849591 := bstep (se 1 (by rfl) ⟨637193, by rfl⟩ : syracuseStep 849591 = 1274387) B1274387
theorem B849611 : Blo 846354 849611 := bstep (se 1 (by rfl) ⟨637208, by rfl⟩ : syracuseStep 849611 = 1274417) B1274417
theorem B849623 : Blo 846354 849623 := bstep (se 1 (by rfl) ⟨637217, by rfl⟩ : syracuseStep 849623 = 1274435) B1274435
theorem B6518489 : Blo 846354 6518489 := bstep (se 2 (by rfl) ⟨2444433, by rfl⟩ : syracuseStep 6518489 = 4888867) B4888867
theorem B849643 : Blo 846354 849643 := bstep (se 1 (by rfl) ⟨637232, by rfl⟩ : syracuseStep 849643 = 1274465) B1274465
theorem B849655 : Blo 846354 849655 := bstep (se 1 (by rfl) ⟨637241, by rfl⟩ : syracuseStep 849655 = 1274483) B1274483
theorem B849675 : Blo 846354 849675 := bstep (se 1 (by rfl) ⟨637256, by rfl⟩ : syracuseStep 849675 = 1274513) B1274513
theorem B849687 : Blo 846354 849687 := bstep (se 1 (by rfl) ⟨637265, by rfl⟩ : syracuseStep 849687 = 1274531) B1274531
theorem B1210135 : Blo 846354 1210135 := bstep (se 1 (by rfl) ⟨907601, by rfl⟩ : syracuseStep 1210135 = 1815203) B1815203
theorem B849707 : Blo 846354 849707 := bstep (se 1 (by rfl) ⟨637280, by rfl⟩ : syracuseStep 849707 = 1274561) B1274561
theorem B849719 : Blo 846354 849719 := bstep (se 1 (by rfl) ⟨637289, by rfl⟩ : syracuseStep 849719 = 1274579) B1274579
theorem B849739 : Blo 846354 849739 := bstep (se 1 (by rfl) ⟨637304, by rfl⟩ : syracuseStep 849739 = 1274609) B1274609
theorem B849751 : Blo 846354 849751 := bstep (se 1 (by rfl) ⟨637313, by rfl⟩ : syracuseStep 849751 = 1274627) B1274627
theorem B5437277 : Blo 846354 5437277 := bstep (se 3 (by rfl) ⟨1019489, by rfl⟩ : syracuseStep 5437277 = 2038979) B2038979
theorem B849771 : Blo 846354 849771 := bstep (se 1 (by rfl) ⟨637328, by rfl⟩ : syracuseStep 849771 = 1274657) B1274657
theorem B849783 : Blo 846354 849783 := bstep (se 1 (by rfl) ⟨637337, by rfl⟩ : syracuseStep 849783 = 1274675) B1274675
theorem B849803 : Blo 846354 849803 := bstep (se 1 (by rfl) ⟨637352, by rfl⟩ : syracuseStep 849803 = 1274705) B1274705
theorem B849815 : Blo 846354 849815 := bstep (se 1 (by rfl) ⟨637361, by rfl⟩ : syracuseStep 849815 = 1274723) B1274723
theorem B849835 : Blo 846354 849835 := bstep (se 1 (by rfl) ⟨637376, by rfl⟩ : syracuseStep 849835 = 1274753) B1274753
theorem B849847 : Blo 846354 849847 := bstep (se 1 (by rfl) ⟨637385, by rfl⟩ : syracuseStep 849847 = 1274771) B1274771
theorem B849867 : Blo 846354 849867 := bstep (se 1 (by rfl) ⟨637400, by rfl⟩ : syracuseStep 849867 = 1274801) B1274801
theorem B849879 : Blo 846354 849879 := bstep (se 1 (by rfl) ⟨637409, by rfl⟩ : syracuseStep 849879 = 1274819) B1274819
theorem B8157145 : Blo 846354 8157145 := bstep (se 2 (by rfl) ⟨3058929, by rfl⟩ : syracuseStep 8157145 = 6117859) B6117859
theorem B849899 : Blo 846354 849899 := bstep (se 1 (by rfl) ⟨637424, by rfl⟩ : syracuseStep 849899 = 1274849) B1274849
theorem B849911 : Blo 846354 849911 := bstep (se 1 (by rfl) ⟨637433, by rfl⟩ : syracuseStep 849911 = 1274867) B1274867
theorem B849931 : Blo 846354 849931 := bstep (se 1 (by rfl) ⟨637448, by rfl⟩ : syracuseStep 849931 = 1274897) B1274897
theorem B849943 : Blo 846354 849943 := bstep (se 1 (by rfl) ⟨637457, by rfl⟩ : syracuseStep 849943 = 1274915) B1274915
theorem B849963 : Blo 846354 849963 := bstep (se 1 (by rfl) ⟨637472, by rfl⟩ : syracuseStep 849963 = 1274945) B1274945
theorem B849975 : Blo 846354 849975 := bstep (se 1 (by rfl) ⟨637481, by rfl⟩ : syracuseStep 849975 = 1274963) B1274963
theorem B849995 : Blo 846354 849995 := bstep (se 1 (by rfl) ⟨637496, by rfl⟩ : syracuseStep 849995 = 1274993) B1274993
theorem B1964119 : Blo 846354 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B850007 : Blo 846354 850007 := bstep (se 1 (by rfl) ⟨637505, by rfl⟩ : syracuseStep 850007 = 1275011) B1275011
theorem B850027 : Blo 846354 850027 := bstep (se 1 (by rfl) ⟨637520, by rfl⟩ : syracuseStep 850027 = 1275041) B1275041
theorem B850039 : Blo 846354 850039 := bstep (se 1 (by rfl) ⟨637529, by rfl⟩ : syracuseStep 850039 = 1275059) B1275059
theorem B850059 : Blo 846354 850059 := bstep (se 1 (by rfl) ⟨637544, by rfl⟩ : syracuseStep 850059 = 1275089) B1275089
theorem B850071 : Blo 846354 850071 := bstep (se 1 (by rfl) ⟨637553, by rfl⟩ : syracuseStep 850071 = 1275107) B1275107
theorem B850091 : Blo 846354 850091 := bstep (se 1 (by rfl) ⟨637568, by rfl⟩ : syracuseStep 850091 = 1275137) B1275137
theorem B850103 : Blo 846354 850103 := bstep (se 1 (by rfl) ⟨637577, by rfl⟩ : syracuseStep 850103 = 1275155) B1275155
theorem B850123 : Blo 846354 850123 := bstep (se 1 (by rfl) ⟨637592, by rfl⟩ : syracuseStep 850123 = 1275185) B1275185
theorem B850135 : Blo 846354 850135 := bstep (se 1 (by rfl) ⟨637601, by rfl⟩ : syracuseStep 850135 = 1275203) B1275203
theorem B850155 : Blo 846354 850155 := bstep (se 1 (by rfl) ⟨637616, by rfl⟩ : syracuseStep 850155 = 1275233) B1275233
theorem B850167 : Blo 846354 850167 := bstep (se 1 (by rfl) ⟨637625, by rfl⟩ : syracuseStep 850167 = 1275251) B1275251
theorem B850187 : Blo 846354 850187 := bstep (se 1 (by rfl) ⟨637640, by rfl⟩ : syracuseStep 850187 = 1275281) B1275281
theorem B850199 : Blo 846354 850199 := bstep (se 1 (by rfl) ⟨637649, by rfl⟩ : syracuseStep 850199 = 1275299) B1275299
theorem B850219 : Blo 846354 850219 := bstep (se 1 (by rfl) ⟨637664, by rfl⟩ : syracuseStep 850219 = 1275329) B1275329
theorem B850231 : Blo 846354 850231 := bstep (se 1 (by rfl) ⟨637673, by rfl⟩ : syracuseStep 850231 = 1275347) B1275347
theorem B850251 : Blo 846354 850251 := bstep (se 1 (by rfl) ⟨637688, by rfl⟩ : syracuseStep 850251 = 1275377) B1275377
theorem B850263 : Blo 846354 850263 := bstep (se 1 (by rfl) ⟨637697, by rfl⟩ : syracuseStep 850263 = 1275395) B1275395
theorem B850283 : Blo 846354 850283 := bstep (se 1 (by rfl) ⟨637712, by rfl⟩ : syracuseStep 850283 = 1275425) B1275425
theorem B850295 : Blo 846354 850295 := bstep (se 1 (by rfl) ⟨637721, by rfl⟩ : syracuseStep 850295 = 1275443) B1275443
theorem B850315 : Blo 846354 850315 := bstep (se 1 (by rfl) ⟨637736, by rfl⟩ : syracuseStep 850315 = 1275473) B1275473
theorem B850327 : Blo 846354 850327 := bstep (se 1 (by rfl) ⟨637745, by rfl⟩ : syracuseStep 850327 = 1275491) B1275491
theorem B850347 : Blo 846354 850347 := bstep (se 1 (by rfl) ⟨637760, by rfl⟩ : syracuseStep 850347 = 1275521) B1275521
theorem B3439577 : Blo 846354 3439577 := bstep (se 2 (by rfl) ⟨1289841, by rfl⟩ : syracuseStep 3439577 = 2579683) B2579683
theorem B1375255 : Blo 846354 1375255 := bstep (se 1 (by rfl) ⟨1031441, by rfl⟩ : syracuseStep 1375255 = 2062883) B2062883
theorem B2620505 : Blo 846354 2620505 := bstep (se 2 (by rfl) ⟨982689, by rfl⟩ : syracuseStep 2620505 = 1965379) B1965379
theorem B1932427 : Blo 846354 1932427 := bstep (se 1 (by rfl) ⟨1449320, by rfl⟩ : syracuseStep 1932427 = 2898641) B2898641
theorem B5504321 : Blo 846354 5504321 := bstep (se 2 (by rfl) ⟨2064120, by rfl⟩ : syracuseStep 5504321 = 4128241) B4128241
theorem B4292189 : Blo 846354 4292189 := bstep (se 3 (by rfl) ⟨804785, by rfl⟩ : syracuseStep 4292189 = 1609571) B1609571
theorem B4587139 : Blo 846354 4587139 := bstep (se 1 (by rfl) ⟨3440354, by rfl⟩ : syracuseStep 4587139 = 6880709) B6880709
theorem B24772337 : Blo 846354 24772337 := bstep (se 2 (by rfl) ⟨9289626, by rfl⟩ : syracuseStep 24772337 = 18579253) B18579253
theorem B1933121 : Blo 846354 1933121 := bstep (se 2 (by rfl) ⟨724920, by rfl⟩ : syracuseStep 1933121 = 1449841) B1449841
theorem B10321843 : Blo 846354 10321843 := bstep (se 1 (by rfl) ⟨7741382, by rfl⟩ : syracuseStep 10321843 = 15482765) B15482765
theorem B4292675 : Blo 846354 4292675 := bstep (se 1 (by rfl) ⟨3219506, by rfl⟩ : syracuseStep 4292675 = 6439013) B6439013
theorem B2719831 : Blo 846354 2719831 := bstep (se 1 (by rfl) ⟨2039873, by rfl⟩ : syracuseStep 2719831 = 4079747) B4079747
theorem B4292999 : Blo 846354 4292999 := bstep (se 1 (by rfl) ⟨3219749, by rfl⟩ : syracuseStep 4292999 = 6439499) B6439499
theorem B5439889 : Blo 846354 5439889 := bstep (se 2 (by rfl) ⟨2039958, by rfl⟩ : syracuseStep 5439889 = 4079917) B4079917
theorem B4130327 : Blo 846354 4130327 := bstep (se 1 (by rfl) ⟨3097745, by rfl⟩ : syracuseStep 4130327 = 6195491) B6195491
theorem B10618775 : Blo 846354 10618775 := bstep (se 1 (by rfl) ⟨7964081, by rfl⟩ : syracuseStep 10618775 = 15928163) B15928163
theorem B2033723 : Blo 846354 2033723 := bstep (se 1 (by rfl) ⟨1525292, by rfl⟩ : syracuseStep 2033723 = 3050585) B3050585
theorem B1149175 : Blo 846354 1149175 := bstep (se 1 (by rfl) ⟨861881, by rfl⟩ : syracuseStep 1149175 = 1723763) B1723763
theorem B952591 : Blo 846354 952591 := bstep (se 1 (by rfl) ⟨714443, by rfl⟩ : syracuseStep 952591 = 1428887) B1428887
theorem B11634961 : Blo 846354 11634961 := bstep (se 2 (by rfl) ⟨4363110, by rfl⟩ : syracuseStep 11634961 = 8726221) B8726221
theorem B35227957 : Blo 846354 35227957 := bstep (se 5 (by rfl) ⟨1651310, by rfl⟩ : syracuseStep 35227957 = 3302621) B3302621
theorem B1608083 : Blo 846354 1608083 := bstep (se 1 (by rfl) ⟨1206062, by rfl⟩ : syracuseStep 1608083 = 2412125) B2412125
theorem B1608311 : Blo 846354 1608311 := bstep (se 1 (by rfl) ⟨1206233, by rfl⟩ : syracuseStep 1608311 = 2412467) B2412467
theorem B3214025 : Blo 846354 3214025 := bstep (se 2 (by rfl) ⟨1205259, by rfl⟩ : syracuseStep 3214025 = 2410519) B2410519
theorem B953095 : Blo 846354 953095 := bstep (se 1 (by rfl) ⟨714821, by rfl⟩ : syracuseStep 953095 = 1429643) B1429643
theorem B3443471 : Blo 846354 3443471 := bstep (se 1 (by rfl) ⟨2582603, by rfl⟩ : syracuseStep 3443471 = 5165207) B5165207
theorem B953275 : Blo 846354 953275 := bstep (se 1 (by rfl) ⟨714956, by rfl⟩ : syracuseStep 953275 = 1429913) B1429913
theorem B4590863 : Blo 846354 4590863 := bstep (se 1 (by rfl) ⟨3443147, by rfl⟩ : syracuseStep 4590863 = 6886295) B6886295
theorem B953743 : Blo 846354 953743 := bstep (se 1 (by rfl) ⟨715307, by rfl⟩ : syracuseStep 953743 = 1430615) B1430615
theorem B2723225 : Blo 846354 2723225 := bstep (se 2 (by rfl) ⟨1021209, by rfl⟩ : syracuseStep 2723225 = 2042419) B2042419
theorem B7179853 : Blo 846354 7179853 := bstep (se 3 (by rfl) ⟨1346222, by rfl⟩ : syracuseStep 7179853 = 2692445) B2692445
theorem B6885121 : Blo 846354 6885121 := bstep (se 2 (by rfl) ⟨2581920, by rfl⟩ : syracuseStep 6885121 = 5163841) B5163841
theorem B1904399 : Blo 846354 1904399 := bstep (se 1 (by rfl) ⟨1428299, by rfl⟩ : syracuseStep 1904399 = 2856599) B2856599
theorem B1904417 : Blo 846354 1904417 := bstep (se 2 (by rfl) ⟨714156, by rfl⟩ : syracuseStep 1904417 = 1428313) B1428313
theorem B5148467 : Blo 846354 5148467 := bstep (se 1 (by rfl) ⟨3861350, by rfl⟩ : syracuseStep 5148467 = 7722701) B7722701
theorem B4296563 : Blo 846354 4296563 := bstep (se 1 (by rfl) ⟨3222422, by rfl⟩ : syracuseStep 4296563 = 6444845) B6444845
theorem B954247 : Blo 846354 954247 := bstep (se 1 (by rfl) ⟨715685, by rfl⟩ : syracuseStep 954247 = 1431371) B1431371
theorem B954427 : Blo 846354 954427 := bstep (se 1 (by rfl) ⟨715820, by rfl⟩ : syracuseStep 954427 = 1431641) B1431641
theorem B4821059 : Blo 846354 4821059 := bstep (se 1 (by rfl) ⟨3615794, by rfl⟩ : syracuseStep 4821059 = 7231589) B7231589
theorem B1904759 : Blo 846354 1904759 := bstep (se 1 (by rfl) ⟨1428569, by rfl⟩ : syracuseStep 1904759 = 2857139) B2857139
theorem B2035847 : Blo 846354 2035847 := bstep (se 1 (by rfl) ⟨1526885, by rfl⟩ : syracuseStep 2035847 = 3053771) B3053771
theorem B3445025 : Blo 846354 3445025 := bstep (se 2 (by rfl) ⟨1291884, by rfl⟩ : syracuseStep 3445025 = 2583769) B2583769
theorem B2298145 : Blo 846354 2298145 := bstep (se 2 (by rfl) ⟨861804, by rfl⟩ : syracuseStep 2298145 = 1723609) B1723609
theorem B1904939 : Blo 846354 1904939 := bstep (se 1 (by rfl) ⟨1428704, by rfl⟩ : syracuseStep 1904939 = 2857409) B2857409
theorem B1610027 : Blo 846354 1610027 := bstep (se 1 (by rfl) ⟨1207520, by rfl⟩ : syracuseStep 1610027 = 2415041) B2415041
theorem B4297049 : Blo 846354 4297049 := bstep (se 2 (by rfl) ⟨1611393, by rfl⟩ : syracuseStep 4297049 = 3222787) B3222787
theorem B3215801 : Blo 846354 3215801 := bstep (se 2 (by rfl) ⟨1205925, by rfl⟩ : syracuseStep 3215801 = 2411851) B2411851
theorem B4821515 : Blo 846354 4821515 := bstep (se 1 (by rfl) ⟨3616136, by rfl⟩ : syracuseStep 4821515 = 7232273) B7232273
theorem B1610255 : Blo 846354 1610255 := bstep (se 1 (by rfl) ⟨1207691, by rfl⟩ : syracuseStep 1610255 = 2415383) B2415383
theorem B954895 : Blo 846354 954895 := bstep (se 1 (by rfl) ⟨716171, by rfl⟩ : syracuseStep 954895 = 1432343) B1432343
theorem B1020475 : Blo 846354 1020475 := bstep (se 1 (by rfl) ⟨765356, by rfl⟩ : syracuseStep 1020475 = 1530713) B1530713
theorem B1905299 : Blo 846354 1905299 := bstep (se 1 (by rfl) ⟨1428974, by rfl⟩ : syracuseStep 1905299 = 2857949) B2857949
theorem B1905353 : Blo 846354 1905353 := bstep (se 2 (by rfl) ⟨714507, by rfl⟩ : syracuseStep 1905353 = 1429015) B1429015
theorem B1086251 : Blo 846354 1086251 := bstep (se 1 (by rfl) ⟨814688, by rfl⟩ : syracuseStep 1086251 = 1629377) B1629377
theorem B955399 : Blo 846354 955399 := bstep (se 1 (by rfl) ⟨716549, by rfl⟩ : syracuseStep 955399 = 1433099) B1433099
theorem B955579 : Blo 846354 955579 := bstep (se 1 (by rfl) ⟨716684, by rfl⟩ : syracuseStep 955579 = 1433369) B1433369
theorem B2069761 : Blo 846354 2069761 := bstep (se 2 (by rfl) ⟨776160, by rfl⟩ : syracuseStep 2069761 = 1552321) B1552321
theorem B1906055 : Blo 846354 1906055 := bstep (se 1 (by rfl) ⟨1429541, by rfl⟩ : syracuseStep 1906055 = 2859083) B2859083
theorem B2037259 : Blo 846354 2037259 := bstep (se 1 (by rfl) ⟨1527944, by rfl⟩ : syracuseStep 2037259 = 3055889) B3055889
theorem B1938959 : Blo 846354 1938959 := bstep (se 1 (by rfl) ⟨1454219, by rfl⟩ : syracuseStep 1938959 = 2908439) B2908439
theorem B2856491 : Blo 846354 2856491 := bstep (se 1 (by rfl) ⟨2142368, by rfl⟩ : syracuseStep 2856491 = 4284737) B4284737
theorem B1807915 : Blo 846354 1807915 := bstep (se 1 (by rfl) ⟨1355936, by rfl⟩ : syracuseStep 1807915 = 2711873) B2711873
theorem B1906235 : Blo 846354 1906235 := bstep (se 1 (by rfl) ⟨1429676, by rfl⟩ : syracuseStep 1906235 = 2859353) B2859353
theorem B2037307 : Blo 846354 2037307 := bstep (se 1 (by rfl) ⟨1527980, by rfl⟩ : syracuseStep 2037307 = 3055961) B3055961
theorem B956047 : Blo 846354 956047 := bstep (se 1 (by rfl) ⟨717035, by rfl⟩ : syracuseStep 956047 = 1434071) B1434071
theorem B9672371 : Blo 846354 9672371 := bstep (se 1 (by rfl) ⟨7254278, by rfl⟩ : syracuseStep 9672371 = 14508557) B14508557
theorem B1906361 : Blo 846354 1906361 := bstep (se 2 (by rfl) ⟨714885, by rfl⟩ : syracuseStep 1906361 = 1429771) B1429771
theorem B4069153 : Blo 846354 4069153 := bstep (se 2 (by rfl) ⟨1525932, by rfl⟩ : syracuseStep 4069153 = 3051865) B3051865
theorem B1808171 : Blo 846354 1808171 := bstep (se 1 (by rfl) ⟨1356128, by rfl⟩ : syracuseStep 1808171 = 2712257) B2712257
theorem B3872627 : Blo 846354 3872627 := bstep (se 1 (by rfl) ⟨2904470, by rfl⟩ : syracuseStep 3872627 = 5808941) B5808941
theorem B1611667 : Blo 846354 1611667 := bstep (se 1 (by rfl) ⟨1208750, by rfl⟩ : syracuseStep 1611667 = 2417501) B2417501
theorem B1906703 : Blo 846354 1906703 := bstep (se 1 (by rfl) ⟨1430027, by rfl⟩ : syracuseStep 1906703 = 2860055) B2860055
theorem B1906721 : Blo 846354 1906721 := bstep (se 2 (by rfl) ⟨715020, by rfl⟩ : syracuseStep 1906721 = 1430041) B1430041
theorem B1087607 : Blo 846354 1087607 := bstep (se 1 (by rfl) ⟨815705, by rfl⟩ : syracuseStep 1087607 = 1631411) B1631411
theorem B1611895 : Blo 846354 1611895 := bstep (se 1 (by rfl) ⟨1208921, by rfl⟩ : syracuseStep 1611895 = 2417843) B2417843
theorem B956551 : Blo 846354 956551 := bstep (se 1 (by rfl) ⟨717413, by rfl⟩ : syracuseStep 956551 = 1434827) B1434827
theorem B1907063 : Blo 846354 1907063 := bstep (se 1 (by rfl) ⟨1430297, by rfl⟩ : syracuseStep 1907063 = 2860595) B2860595
theorem B4299155 : Blo 846354 4299155 := bstep (se 1 (by rfl) ⟨3224366, by rfl⟩ : syracuseStep 4299155 = 6448733) B6448733
theorem B1907243 : Blo 846354 1907243 := bstep (se 1 (by rfl) ⟨1430432, by rfl⟩ : syracuseStep 1907243 = 2860865) B2860865
theorem B1547041 : Blo 846354 1547041 := bstep (se 2 (by rfl) ⟨580140, by rfl⟩ : syracuseStep 1547041 = 1160281) B1160281
theorem B11606819 : Blo 846354 11606819 := bstep (se 1 (by rfl) ⟨8705114, by rfl⟩ : syracuseStep 11606819 = 17410229) B17410229
theorem B2857787 : Blo 846354 2857787 := bstep (se 1 (by rfl) ⟨2143340, by rfl⟩ : syracuseStep 2857787 = 4286681) B4286681
theorem B1809299 : Blo 846354 1809299 := bstep (se 1 (by rfl) ⟨1356974, by rfl⟩ : syracuseStep 1809299 = 2713949) B2713949
theorem B1907603 : Blo 846354 1907603 := bstep (se 1 (by rfl) ⟨1430702, by rfl⟩ : syracuseStep 1907603 = 2861405) B2861405
theorem B2202553 : Blo 846354 2202553 := bstep (se 2 (by rfl) ⟨825957, by rfl⟩ : syracuseStep 2202553 = 1651915) B1651915
theorem B1907657 : Blo 846354 1907657 := bstep (se 2 (by rfl) ⟨715371, by rfl⟩ : syracuseStep 1907657 = 1430743) B1430743
theorem B3480587 : Blo 846354 3480587 := bstep (se 1 (by rfl) ⟨2610440, by rfl⟩ : syracuseStep 3480587 = 5220881) B5220881
theorem B6200453 : Blo 846354 6200453 := bstep (se 4 (by rfl) ⟨581292, by rfl⟩ : syracuseStep 6200453 = 1162585) B1162585
theorem B3874049 : Blo 846354 3874049 := bstep (se 2 (by rfl) ⟨1452768, by rfl⟩ : syracuseStep 3874049 = 2905537) B2905537
theorem B2858273 : Blo 846354 2858273 := bstep (se 2 (by rfl) ⟨1071852, by rfl⟩ : syracuseStep 2858273 = 2143705) B2143705
theorem B1809811 : Blo 846354 1809811 := bstep (se 1 (by rfl) ⟨1357358, by rfl⟩ : syracuseStep 1809811 = 2714717) B2714717
theorem B3317201 : Blo 846354 3317201 := bstep (se 2 (by rfl) ⟨1243950, by rfl⟩ : syracuseStep 3317201 = 2487901) B2487901
theorem B4070999 : Blo 846354 4070999 := bstep (se 1 (by rfl) ⟨3053249, by rfl⟩ : syracuseStep 4070999 = 6106499) B6106499
theorem B1908359 : Blo 846354 1908359 := bstep (se 1 (by rfl) ⟨1431269, by rfl⟩ : syracuseStep 1908359 = 2862539) B2862539
theorem B1613459 : Blo 846354 1613459 := bstep (se 1 (by rfl) ⟨1210094, by rfl⟩ : syracuseStep 1613459 = 2420189) B2420189
theorem B1613513 : Blo 846354 1613513 := bstep (se 2 (by rfl) ⟨605067, by rfl⟩ : syracuseStep 1613513 = 1210135) B1210135
theorem B1613611 : Blo 846354 1613611 := bstep (se 1 (by rfl) ⟨1210208, by rfl⟩ : syracuseStep 1613611 = 2420417) B2420417
theorem B1908539 : Blo 846354 1908539 := bstep (se 1 (by rfl) ⟨1431404, by rfl⟩ : syracuseStep 1908539 = 2862809) B2862809
theorem B2858867 : Blo 846354 2858867 := bstep (se 1 (by rfl) ⟨2144150, by rfl⟩ : syracuseStep 2858867 = 4288301) B4288301
theorem B3219385 : Blo 846354 3219385 := bstep (se 2 (by rfl) ⟨1207269, by rfl⟩ : syracuseStep 3219385 = 2414539) B2414539
theorem B1908665 : Blo 846354 1908665 := bstep (se 2 (by rfl) ⟨715749, by rfl⟩ : syracuseStep 1908665 = 1431499) B1431499
theorem B1613839 : Blo 846354 1613839 := bstep (se 1 (by rfl) ⟨1210379, by rfl⟩ : syracuseStep 1613839 = 2420759) B2420759
theorem B1909007 : Blo 846354 1909007 := bstep (se 1 (by rfl) ⟨1431755, by rfl⟩ : syracuseStep 1909007 = 2863511) B2863511
theorem B1909025 : Blo 846354 1909025 := bstep (se 2 (by rfl) ⟨715884, by rfl⟩ : syracuseStep 1909025 = 1431769) B1431769
theorem B4825433 : Blo 846354 4825433 := bstep (se 2 (by rfl) ⟨1809537, by rfl⟩ : syracuseStep 4825433 = 3619075) B3619075
theorem B1909367 : Blo 846354 1909367 := bstep (se 1 (by rfl) ⟨1432025, by rfl⟩ : syracuseStep 1909367 = 2864051) B2864051
theorem B1745555 : Blo 846354 1745555 := bstep (se 1 (by rfl) ⟨1309166, by rfl⟩ : syracuseStep 1745555 = 2618333) B2618333
theorem B4825889 : Blo 846354 4825889 := bstep (se 2 (by rfl) ⟨1809708, by rfl⟩ : syracuseStep 4825889 = 3619417) B3619417
theorem B1909547 : Blo 846354 1909547 := bstep (se 1 (by rfl) ⟨1432160, by rfl⟩ : syracuseStep 1909547 = 2864321) B2864321
theorem B4826141 : Blo 846354 4826141 := bstep (se 3 (by rfl) ⟨904901, by rfl⟩ : syracuseStep 4826141 = 1809803) B1809803
theorem B1909907 : Blo 846354 1909907 := bstep (se 1 (by rfl) ⟨1432430, by rfl⟩ : syracuseStep 1909907 = 2864861) B2864861
theorem B1909961 : Blo 846354 1909961 := bstep (se 2 (by rfl) ⟨716235, by rfl⟩ : syracuseStep 1909961 = 1432471) B1432471
theorem B4302233 : Blo 846354 4302233 := bstep (se 2 (by rfl) ⟨1613337, by rfl⟩ : syracuseStep 4302233 = 3226675) B3226675
theorem B1451449 : Blo 846354 1451449 := bstep (se 2 (by rfl) ⟨544293, by rfl⟩ : syracuseStep 1451449 = 1088587) B1088587
theorem B6432209 : Blo 846354 6432209 := bstep (se 2 (by rfl) ⟨2412078, by rfl⟩ : syracuseStep 6432209 = 4824157) B4824157
theorem B13936157 : Blo 846354 13936157 := bstep (se 3 (by rfl) ⟨2613029, by rfl⟩ : syracuseStep 13936157 = 5226059) B5226059
theorem B14526053 : Blo 846354 14526053 := bstep (se 4 (by rfl) ⟨1361817, by rfl⟩ : syracuseStep 14526053 = 2723635) B2723635
theorem B1812169 : Blo 846354 1812169 := bstep (se 2 (by rfl) ⟨679563, by rfl⟩ : syracuseStep 1812169 = 1359127) B1359127
theorem B2172791 : Blo 846354 2172791 := bstep (se 1 (by rfl) ⟨1629593, by rfl⟩ : syracuseStep 2172791 = 3259187) B3259187
theorem B1910663 : Blo 846354 1910663 := bstep (se 1 (by rfl) ⟨1432997, by rfl⟩ : syracuseStep 1910663 = 2865995) B2865995
theorem B1910843 : Blo 846354 1910843 := bstep (se 1 (by rfl) ⟨1433132, by rfl⟩ : syracuseStep 1910843 = 2866265) B2866265
theorem B1747003 : Blo 846354 1747003 := bstep (se 1 (by rfl) ⟨1310252, by rfl⟩ : syracuseStep 1747003 = 2620505) B2620505
theorem B1910969 : Blo 846354 1910969 := bstep (se 2 (by rfl) ⟨716613, by rfl⟩ : syracuseStep 1910969 = 1433227) B1433227
theorem B37234997 : Blo 846354 37234997 := bstep (se 5 (by rfl) ⟨1745390, by rfl⟩ : syracuseStep 37234997 = 3490781) B3490781
theorem B2861459 : Blo 846354 2861459 := bstep (se 1 (by rfl) ⟨2146094, by rfl⟩ : syracuseStep 2861459 = 4292189) B4292189
theorem B1911311 : Blo 846354 1911311 := bstep (se 1 (by rfl) ⟨1433483, by rfl⟩ : syracuseStep 1911311 = 2866967) B2866967
theorem B1911329 : Blo 846354 1911329 := bstep (se 2 (by rfl) ⟨716748, by rfl⟩ : syracuseStep 1911329 = 1433497) B1433497
theorem B1288747 : Blo 846354 1288747 := bstep (se 1 (by rfl) ⟨966560, by rfl⟩ : syracuseStep 1288747 = 1933121) B1933121
theorem B6204161 : Blo 846354 6204161 := bstep (se 2 (by rfl) ⟨2326560, by rfl⟩ : syracuseStep 6204161 = 4653121) B4653121
theorem B3222287 : Blo 846354 3222287 := bstep (se 1 (by rfl) ⟨2416715, by rfl⟩ : syracuseStep 3222287 = 4833431) B4833431
theorem B16329509 : Blo 846354 16329509 := bstep (se 4 (by rfl) ⟨1530891, by rfl⟩ : syracuseStep 16329509 = 3061783) B3061783
theorem B1911671 : Blo 846354 1911671 := bstep (se 1 (by rfl) ⟨1433753, by rfl⟩ : syracuseStep 1911671 = 2867507) B2867507
theorem B1813433 : Blo 846354 1813433 := bstep (se 2 (by rfl) ⟨680037, by rfl⟩ : syracuseStep 1813433 = 1360075) B1360075
theorem B1813519 : Blo 846354 1813519 := bstep (se 1 (by rfl) ⟨1360139, by rfl⟩ : syracuseStep 1813519 = 2720279) B2720279
theorem B1911851 : Blo 846354 1911851 := bstep (se 1 (by rfl) ⟨1433888, by rfl⟩ : syracuseStep 1911851 = 2867777) B2867777
theorem B3616001 : Blo 846354 3616001 := bstep (se 2 (by rfl) ⟨1356000, by rfl⟩ : syracuseStep 3616001 = 2712001) B2712001
theorem B4828531 : Blo 846354 4828531 := bstep (se 1 (by rfl) ⟨3621398, by rfl⟩ : syracuseStep 4828531 = 7242797) B7242797
theorem B16788871 : Blo 846354 16788871 := bstep (se 1 (by rfl) ⟨12591653, by rfl⟩ : syracuseStep 16788871 = 25183307) B25183307
theorem B1912211 : Blo 846354 1912211 := bstep (se 1 (by rfl) ⟨1434158, by rfl⟩ : syracuseStep 1912211 = 2868317) B2868317
theorem B1912265 : Blo 846354 1912265 := bstep (se 2 (by rfl) ⟨717099, by rfl⟩ : syracuseStep 1912265 = 1434199) B1434199
theorem B2862863 : Blo 846354 2862863 := bstep (se 1 (by rfl) ⟨2147147, by rfl⟩ : syracuseStep 2862863 = 4294295) B4294295
theorem B1224505 : Blo 846354 1224505 := bstep (se 2 (by rfl) ⟨459189, by rfl⟩ : syracuseStep 1224505 = 918379) B918379
theorem B4304825 : Blo 846354 4304825 := bstep (se 2 (by rfl) ⟨1614309, by rfl⟩ : syracuseStep 4304825 = 3228619) B3228619
theorem B2863133 : Blo 846354 2863133 := bstep (se 3 (by rfl) ⟨536837, by rfl⟩ : syracuseStep 2863133 = 1073675) B1073675
theorem B2240627 : Blo 846354 2240627 := bstep (se 1 (by rfl) ⟨1680470, by rfl⟩ : syracuseStep 2240627 = 3360941) B3360941
theorem B1912967 : Blo 846354 1912967 := bstep (se 1 (by rfl) ⟨1434725, by rfl⟩ : syracuseStep 1912967 = 2869451) B2869451
theorem B2142409 : Blo 846354 2142409 := bstep (se 2 (by rfl) ⟨803403, by rfl⟩ : syracuseStep 2142409 = 1606807) B1606807
theorem B3092795 : Blo 846354 3092795 := bstep (se 1 (by rfl) ⟨2319596, by rfl⟩ : syracuseStep 3092795 = 4639193) B4639193
theorem B1913147 : Blo 846354 1913147 := bstep (se 1 (by rfl) ⟨1434860, by rfl⟩ : syracuseStep 1913147 = 2869721) B2869721
theorem B2142551 : Blo 846354 2142551 := bstep (se 1 (by rfl) ⟨1606913, by rfl⟩ : syracuseStep 2142551 = 3213827) B3213827
theorem B1814903 : Blo 846354 1814903 := bstep (se 1 (by rfl) ⟨1361177, by rfl⟩ : syracuseStep 1814903 = 2722355) B2722355
theorem B1913273 : Blo 846354 1913273 := bstep (se 2 (by rfl) ⟨717477, by rfl⟩ : syracuseStep 1913273 = 1434955) B1434955
theorem B5157323 : Blo 846354 5157323 := bstep (se 1 (by rfl) ⟨3867992, by rfl⟩ : syracuseStep 5157323 = 7735985) B7735985
theorem B15479261 : Blo 846354 15479261 := bstep (se 3 (by rfl) ⟨2902361, by rfl⟩ : syracuseStep 15479261 = 5804723) B5804723
theorem B1356347 : Blo 846354 1356347 := bstep (se 1 (by rfl) ⟨1017260, by rfl⟩ : syracuseStep 1356347 = 2034521) B2034521
theorem B5157665 : Blo 846354 5157665 := bstep (se 2 (by rfl) ⟨1934124, by rfl⟩ : syracuseStep 5157665 = 3868249) B3868249
theorem B4829989 : Blo 846354 4829989 := bstep (se 4 (by rfl) ⟨452811, by rfl⟩ : syracuseStep 4829989 = 905623) B905623
theorem B1356859 : Blo 846354 1356859 := bstep (se 1 (by rfl) ⟨1017644, by rfl⟩ : syracuseStep 1356859 = 2035289) B2035289
theorem B4830515 : Blo 846354 4830515 := bstep (se 1 (by rfl) ⟨3622886, by rfl⟩ : syracuseStep 4830515 = 7245773) B7245773
theorem B2864537 : Blo 846354 2864537 := bstep (se 2 (by rfl) ⟨1074201, by rfl⟩ : syracuseStep 2864537 = 2148403) B2148403
theorem B20592305 : Blo 846354 20592305 := bstep (se 2 (by rfl) ⟨7722114, by rfl⟩ : syracuseStep 20592305 = 15444229) B15444229
theorem B14464817 : Blo 846354 14464817 := bstep (se 2 (by rfl) ⟨5424306, by rfl⟩ : syracuseStep 14464817 = 10848613) B10848613
theorem B6895475 : Blo 846354 6895475 := bstep (se 1 (by rfl) ⟨5171606, by rfl⟩ : syracuseStep 6895475 = 10343213) B10343213
theorem B3225491 : Blo 846354 3225491 := bstep (se 1 (by rfl) ⟨2419118, by rfl⟩ : syracuseStep 3225491 = 4838237) B4838237
theorem B1357769 : Blo 846354 1357769 := bstep (se 2 (by rfl) ⟨509163, by rfl⟩ : syracuseStep 1357769 = 1018327) B1018327
theorem B4077611 : Blo 846354 4077611 := bstep (se 1 (by rfl) ⟨3058208, by rfl⟩ : syracuseStep 4077611 = 6116417) B6116417
theorem B2865239 : Blo 846354 2865239 := bstep (se 1 (by rfl) ⟨2148929, by rfl⟩ : syracuseStep 2865239 = 4297859) B4297859
theorem B2144627 : Blo 846354 2144627 := bstep (se 1 (by rfl) ⟨1608470, by rfl⟩ : syracuseStep 2144627 = 3216941) B3216941
theorem B2865725 : Blo 846354 2865725 := bstep (se 3 (by rfl) ⟨537323, by rfl⟩ : syracuseStep 2865725 = 1074647) B1074647
theorem B1358537 : Blo 846354 1358537 := bstep (se 2 (by rfl) ⟨509451, by rfl⟩ : syracuseStep 1358537 = 1018903) B1018903
theorem B4831973 : Blo 846354 4831973 := bstep (se 4 (by rfl) ⟨452997, by rfl⟩ : syracuseStep 4831973 = 905995) B905995
theorem B2145143 : Blo 846354 2145143 := bstep (se 1 (by rfl) ⟨1608857, by rfl⟩ : syracuseStep 2145143 = 3217715) B3217715
theorem B17382637 : Blo 846354 17382637 := bstep (se 3 (by rfl) ⟨3259244, by rfl⟩ : syracuseStep 17382637 = 6518489) B6518489
theorem B3620305 : Blo 846354 3620305 := bstep (se 2 (by rfl) ⟨1357614, by rfl⟩ : syracuseStep 3620305 = 2715229) B2715229
theorem B3227147 : Blo 846354 3227147 := bstep (se 1 (by rfl) ⟨2420360, by rfl⟩ : syracuseStep 3227147 = 4840721) B4840721
theorem B966415 : Blo 846354 966415 := bstep (se 1 (by rfl) ⟨724811, by rfl⟩ : syracuseStep 966415 = 1449623) B1449623
theorem B2146135 : Blo 846354 2146135 := bstep (se 1 (by rfl) ⟨1609601, by rfl⟩ : syracuseStep 2146135 = 3219203) B3219203
theorem B2867129 : Blo 846354 2867129 := bstep (se 2 (by rfl) ⟨1075173, by rfl⟩ : syracuseStep 2867129 = 2150347) B2150347
theorem B2146439 : Blo 846354 2146439 := bstep (se 1 (by rfl) ⟨1609829, by rfl⟩ : syracuseStep 2146439 = 3219659) B3219659
theorem B2146571 : Blo 846354 2146571 := bstep (se 1 (by rfl) ⟨1609928, by rfl⟩ : syracuseStep 2146571 = 3219857) B3219857
theorem B2867723 : Blo 846354 2867723 := bstep (se 1 (by rfl) ⟨2150792, by rfl⟩ : syracuseStep 2867723 = 4301585) B4301585
theorem B2867831 : Blo 846354 2867831 := bstep (se 1 (by rfl) ⟨2150873, by rfl⟩ : syracuseStep 2867831 = 4301747) B4301747
theorem B1163977 : Blo 846354 1163977 := bstep (se 2 (by rfl) ⟨436491, by rfl⟩ : syracuseStep 1163977 = 872983) B872983
theorem B2147087 : Blo 846354 2147087 := bstep (se 1 (by rfl) ⟨1610315, by rfl⟩ : syracuseStep 2147087 = 3220631) B3220631
theorem B7258895 : Blo 846354 7258895 := bstep (se 1 (by rfl) ⟨5444171, by rfl⟩ : syracuseStep 7258895 = 10888343) B10888343
theorem B2147219 : Blo 846354 2147219 := bstep (se 1 (by rfl) ⟨1610414, by rfl⟩ : syracuseStep 2147219 = 3220829) B3220829
theorem B2868425 : Blo 846354 2868425 := bstep (se 2 (by rfl) ⟨1075659, by rfl⟩ : syracuseStep 2868425 = 2151319) B2151319
theorem B19613107 : Blo 846354 19613107 := bstep (se 1 (by rfl) ⟨14709830, by rfl⟩ : syracuseStep 19613107 = 29419661) B29419661
theorem B2180951 : Blo 846354 2180951 := bstep (se 1 (by rfl) ⟨1635713, by rfl⟩ : syracuseStep 2180951 = 3271427) B3271427
theorem B5162867 : Blo 846354 5162867 := bstep (se 1 (by rfl) ⟨3872150, by rfl⟩ : syracuseStep 5162867 = 7744301) B7744301
theorem B2869127 : Blo 846354 2869127 := bstep (se 1 (by rfl) ⟨2151845, by rfl⟩ : syracuseStep 2869127 = 4303691) B4303691
theorem B2410393 : Blo 846354 2410393 := bstep (se 2 (by rfl) ⟨903897, by rfl⟩ : syracuseStep 2410393 = 1807795) B1807795
theorem B2148353 : Blo 846354 2148353 := bstep (se 2 (by rfl) ⟨805632, by rfl⟩ : syracuseStep 2148353 = 1611265) B1611265
theorem B6113303 : Blo 846354 6113303 := bstep (se 1 (by rfl) ⟨4584977, by rfl⟩ : syracuseStep 6113303 = 9169955) B9169955
theorem B1394807 : Blo 846354 1394807 := bstep (se 1 (by rfl) ⟨1046105, by rfl⟩ : syracuseStep 1394807 = 2092211) B2092211
theorem B7260293 : Blo 846354 7260293 := bstep (se 4 (by rfl) ⟨680652, by rfl⟩ : syracuseStep 7260293 = 1361305) B1361305
theorem B2869505 : Blo 846354 2869505 := bstep (se 2 (by rfl) ⟨1076064, by rfl⟩ : syracuseStep 2869505 = 2152129) B2152129
theorem B2148727 : Blo 846354 2148727 := bstep (se 1 (by rfl) ⟨1611545, by rfl⟩ : syracuseStep 2148727 = 3223091) B3223091
theorem B2411009 : Blo 846354 2411009 := bstep (se 2 (by rfl) ⟨904128, by rfl⟩ : syracuseStep 2411009 = 1808257) B1808257
theorem B17386103 : Blo 846354 17386103 := bstep (se 1 (by rfl) ⟨13039577, by rfl⟩ : syracuseStep 17386103 = 26079155) B26079155
theorem B1428239 : Blo 846354 1428239 := bstep (se 1 (by rfl) ⟨1071179, by rfl⟩ : syracuseStep 1428239 = 2142359) B2142359
theorem B2149163 : Blo 846354 2149163 := bstep (se 1 (by rfl) ⟨1611872, by rfl⟩ : syracuseStep 2149163 = 3223745) B3223745
theorem B1723681 : Blo 846354 1723681 := bstep (se 2 (by rfl) ⟨646380, by rfl⟩ : syracuseStep 1723681 = 1292761) B1292761
theorem B1428779 : Blo 846354 1428779 := bstep (se 1 (by rfl) ⟨1071584, by rfl⟩ : syracuseStep 1428779 = 2143169) B2143169
theorem B2411977 : Blo 846354 2411977 := bstep (se 2 (by rfl) ⟨904491, by rfl⟩ : syracuseStep 2411977 = 1808983) B1808983
theorem B2150003 : Blo 846354 2150003 := bstep (se 1 (by rfl) ⟨1612502, by rfl⟩ : syracuseStep 2150003 = 3225005) B3225005
theorem B2150023 : Blo 846354 2150023 := bstep (se 1 (by rfl) ⟨1612517, by rfl⟩ : syracuseStep 2150023 = 3225035) B3225035
theorem B1429177 : Blo 846354 1429177 := bstep (se 2 (by rfl) ⟨535941, by rfl⟩ : syracuseStep 1429177 = 1071883) B1071883
theorem B3624851 : Blo 846354 3624851 := bstep (se 1 (by rfl) ⟨2718638, by rfl⟩ : syracuseStep 3624851 = 5437277) B5437277
theorem B2150297 : Blo 846354 2150297 := bstep (se 2 (by rfl) ⟨806361, by rfl⟩ : syracuseStep 2150297 = 1612723) B1612723
theorem B5165059 : Blo 846354 5165059 := bstep (se 1 (by rfl) ⟨3873794, by rfl⟩ : syracuseStep 5165059 = 7747589) B7747589
theorem B2150459 : Blo 846354 2150459 := bstep (se 1 (by rfl) ⟨1612844, by rfl⟩ : syracuseStep 2150459 = 3225689) B3225689
theorem B2576569 : Blo 846354 2576569 := bstep (se 2 (by rfl) ⟨966213, by rfl⟩ : syracuseStep 2576569 = 1932427) B1932427
theorem B2150671 : Blo 846354 2150671 := bstep (se 1 (by rfl) ⟨1613003, by rfl⟩ : syracuseStep 2150671 = 3226007) B3226007
theorem B1429879 : Blo 846354 1429879 := bstep (se 1 (by rfl) ⟨1072409, by rfl⟩ : syracuseStep 1429879 = 2144819) B2144819
theorem B905743 : Blo 846354 905743 := bstep (se 1 (by rfl) ⟨679307, by rfl⟩ : syracuseStep 905743 = 1358615) B1358615
theorem B2150945 : Blo 846354 2150945 := bstep (se 2 (by rfl) ⟨806604, by rfl⟩ : syracuseStep 2150945 = 1613209) B1613209
theorem B1430075 : Blo 846354 1430075 := bstep (se 1 (by rfl) ⟨1072556, by rfl⟩ : syracuseStep 1430075 = 2145113) B2145113
theorem B82629233 : Blo 846354 82629233 := bstep (se 2 (by rfl) ⟨30985962, by rfl⟩ : syracuseStep 82629233 = 61971925) B61971925
theorem B905999 : Blo 846354 905999 := bstep (se 1 (by rfl) ⟨679499, by rfl⟩ : syracuseStep 905999 = 1358999) B1358999
theorem B6116185 : Blo 846354 6116185 := bstep (se 2 (by rfl) ⟨2293569, by rfl⟩ : syracuseStep 6116185 = 4587139) B4587139
theorem B1430473 : Blo 846354 1430473 := bstep (se 2 (by rfl) ⟨536427, by rfl⟩ : syracuseStep 1430473 = 1072855) B1072855
theorem B2413583 : Blo 846354 2413583 := bstep (se 1 (by rfl) ⟨1810187, by rfl⟩ : syracuseStep 2413583 = 3620375) B3620375
theorem B2151947 : Blo 846354 2151947 := bstep (se 1 (by rfl) ⟨1613960, by rfl⟩ : syracuseStep 2151947 = 3227921) B3227921
theorem B3626525 : Blo 846354 3626525 := bstep (se 3 (by rfl) ⟨679973, by rfl⟩ : syracuseStep 3626525 = 1359947) B1359947
theorem B1431175 : Blo 846354 1431175 := bstep (se 1 (by rfl) ⟨1073381, by rfl⟩ : syracuseStep 1431175 = 2146763) B2146763
theorem B4577323 : Blo 846354 4577323 := bstep (se 1 (by rfl) ⟨3432992, by rfl⟩ : syracuseStep 4577323 = 6865985) B6865985
theorem B2938999 : Blo 846354 2938999 := bstep (se 1 (by rfl) ⟨2204249, by rfl⟩ : syracuseStep 2938999 = 4408499) B4408499
theorem B2414711 : Blo 846354 2414711 := bstep (se 1 (by rfl) ⟨1811033, by rfl⟩ : syracuseStep 2414711 = 3622067) B3622067
theorem B1431823 : Blo 846354 1431823 := bstep (se 1 (by rfl) ⟨1073867, by rfl⟩ : syracuseStep 1431823 = 2147735) B2147735
theorem B4839695 : Blo 846354 4839695 := bstep (se 1 (by rfl) ⟨3629771, by rfl⟩ : syracuseStep 4839695 = 7259543) B7259543
theorem B5429537 : Blo 846354 5429537 := bstep (se 2 (by rfl) ⟨2036076, by rfl⟩ : syracuseStep 5429537 = 4072153) B4072153
theorem B14473565 : Blo 846354 14473565 := bstep (se 3 (by rfl) ⟨2713793, by rfl⟩ : syracuseStep 14473565 = 5427587) B5427587
theorem B3627449 : Blo 846354 3627449 := bstep (se 2 (by rfl) ⟨1360293, by rfl⟩ : syracuseStep 3627449 = 2720587) B2720587
theorem B1071787 : Blo 846354 1071787 := bstep (se 1 (by rfl) ⟨803840, by rfl⟩ : syracuseStep 1071787 = 1607681) B1607681
theorem B1432363 : Blo 846354 1432363 := bstep (se 1 (by rfl) ⟨1074272, by rfl⟩ : syracuseStep 1432363 = 2148545) B2148545
theorem B1432505 : Blo 846354 1432505 := bstep (se 2 (by rfl) ⟨537189, by rfl⟩ : syracuseStep 1432505 = 1074379) B1074379
theorem B13753633 : Blo 846354 13753633 := bstep (se 2 (by rfl) ⟨5157612, by rfl⟩ : syracuseStep 13753633 = 10315225) B10315225
theorem B4578707 : Blo 846354 4578707 := bstep (se 1 (by rfl) ⟨3434030, by rfl⟩ : syracuseStep 4578707 = 6868061) B6868061
theorem B4349483 : Blo 846354 4349483 := bstep (se 1 (by rfl) ⟨3262112, by rfl⟩ : syracuseStep 4349483 = 6524225) B6524225
theorem B1072759 : Blo 846354 1072759 := bstep (se 1 (by rfl) ⟨804569, by rfl⟩ : syracuseStep 1072759 = 1609139) B1609139
theorem B1433207 : Blo 846354 1433207 := bstep (se 1 (by rfl) ⟨1074905, by rfl⟩ : syracuseStep 1433207 = 2149811) B2149811
theorem B4841153 : Blo 846354 4841153 := bstep (se 2 (by rfl) ⟨1815432, by rfl⟩ : syracuseStep 4841153 = 3630865) B3630865
theorem B2416385 : Blo 846354 2416385 := bstep (se 2 (by rfl) ⟨906144, by rfl⟩ : syracuseStep 2416385 = 1812289) B1812289
theorem B4349747 : Blo 846354 4349747 := bstep (se 1 (by rfl) ⟨3262310, by rfl⟩ : syracuseStep 4349747 = 6524621) B6524621
theorem B1269563 : Blo 846354 1269563 := bstep (se 1 (by rfl) ⟨952172, by rfl⟩ : syracuseStep 1269563 = 1904345) B1904345
theorem B2416499 : Blo 846354 2416499 := bstep (se 1 (by rfl) ⟨1812374, by rfl⟩ : syracuseStep 2416499 = 3624749) B3624749
theorem B1269623 : Blo 846354 1269623 := bstep (se 1 (by rfl) ⟨952217, by rfl⟩ : syracuseStep 1269623 = 1904435) B1904435
theorem B1269647 : Blo 846354 1269647 := bstep (se 1 (by rfl) ⟨952235, by rfl⟩ : syracuseStep 1269647 = 1904471) B1904471
theorem B1269689 : Blo 846354 1269689 := bstep (se 2 (by rfl) ⟨476133, by rfl⟩ : syracuseStep 1269689 = 952267) B952267
theorem B1073083 : Blo 846354 1073083 := bstep (se 1 (by rfl) ⟨804812, by rfl⟩ : syracuseStep 1073083 = 1609625) B1609625
theorem B1269767 : Blo 846354 1269767 := bstep (se 1 (by rfl) ⟨952325, by rfl⟩ : syracuseStep 1269767 = 1904651) B1904651
theorem B1269803 : Blo 846354 1269803 := bstep (se 1 (by rfl) ⟨952352, by rfl⟩ : syracuseStep 1269803 = 1904705) B1904705
theorem B1433659 : Blo 846354 1433659 := bstep (se 1 (by rfl) ⟨1075244, by rfl⟩ : syracuseStep 1433659 = 2150489) B2150489
theorem B3629123 : Blo 846354 3629123 := bstep (se 1 (by rfl) ⟨2721842, by rfl⟩ : syracuseStep 3629123 = 5443685) B5443685
theorem B1269833 : Blo 846354 1269833 := bstep (se 2 (by rfl) ⟨476187, by rfl⟩ : syracuseStep 1269833 = 952375) B952375
theorem B1532039 : Blo 846354 1532039 := bstep (se 1 (by rfl) ⟨1149029, by rfl⟩ : syracuseStep 1532039 = 2298059) B2298059
theorem B1269947 : Blo 846354 1269947 := bstep (se 1 (by rfl) ⟨952460, by rfl⟩ : syracuseStep 1269947 = 1904921) B1904921
theorem B2416841 : Blo 846354 2416841 := bstep (se 2 (by rfl) ⟨906315, by rfl⟩ : syracuseStep 2416841 = 1812631) B1812631
theorem B1433801 : Blo 846354 1433801 := bstep (se 2 (by rfl) ⟨537675, by rfl⟩ : syracuseStep 1433801 = 1075351) B1075351
theorem B3432685 : Blo 846354 3432685 := bstep (se 3 (by rfl) ⟨643628, by rfl⟩ : syracuseStep 3432685 = 1287257) B1287257
theorem B1270007 : Blo 846354 1270007 := bstep (se 1 (by rfl) ⟨952505, by rfl⟩ : syracuseStep 1270007 = 1905011) B1905011
theorem B1270031 : Blo 846354 1270031 := bstep (se 1 (by rfl) ⟨952523, by rfl⟩ : syracuseStep 1270031 = 1905047) B1905047
theorem B4415759 : Blo 846354 4415759 := bstep (se 1 (by rfl) ⟨3311819, by rfl⟩ : syracuseStep 4415759 = 6623639) B6623639
theorem B1270073 : Blo 846354 1270073 := bstep (se 2 (by rfl) ⟨476277, by rfl⟩ : syracuseStep 1270073 = 952555) B952555
theorem B1270151 : Blo 846354 1270151 := bstep (se 1 (by rfl) ⟨952613, by rfl⟩ : syracuseStep 1270151 = 1905227) B1905227
theorem B1270187 : Blo 846354 1270187 := bstep (se 1 (by rfl) ⟨952640, by rfl⟩ : syracuseStep 1270187 = 1905281) B1905281
theorem B1270217 : Blo 846354 1270217 := bstep (se 2 (by rfl) ⟨476331, by rfl⟩ : syracuseStep 1270217 = 952663) B952663
theorem B12247595 : Blo 846354 12247595 := bstep (se 1 (by rfl) ⟨9185696, by rfl⟩ : syracuseStep 12247595 = 18371393) B18371393
theorem B1270331 : Blo 846354 1270331 := bstep (se 1 (by rfl) ⟨952748, by rfl⟩ : syracuseStep 1270331 = 1905497) B1905497
theorem B1270391 : Blo 846354 1270391 := bstep (se 1 (by rfl) ⟨952793, by rfl⟩ : syracuseStep 1270391 = 1905587) B1905587
theorem B1270415 : Blo 846354 1270415 := bstep (se 1 (by rfl) ⟨952811, by rfl⟩ : syracuseStep 1270415 = 1905623) B1905623
theorem B1270457 : Blo 846354 1270457 := bstep (se 2 (by rfl) ⟨476421, by rfl⟩ : syracuseStep 1270457 = 952843) B952843
theorem B1270535 : Blo 846354 1270535 := bstep (se 1 (by rfl) ⟨952901, by rfl⟩ : syracuseStep 1270535 = 1905803) B1905803
theorem B1270571 : Blo 846354 1270571 := bstep (se 1 (by rfl) ⟨952928, by rfl⟩ : syracuseStep 1270571 = 1905857) B1905857
theorem B1270601 : Blo 846354 1270601 := bstep (se 2 (by rfl) ⟨476475, by rfl⟩ : syracuseStep 1270601 = 952951) B952951
theorem B1074055 : Blo 846354 1074055 := bstep (se 1 (by rfl) ⟨805541, by rfl⟩ : syracuseStep 1074055 = 1611083) B1611083
theorem B1434503 : Blo 846354 1434503 := bstep (se 1 (by rfl) ⟨1075877, by rfl⟩ : syracuseStep 1434503 = 2151755) B2151755
theorem B1270715 : Blo 846354 1270715 := bstep (se 1 (by rfl) ⟨953036, by rfl⟩ : syracuseStep 1270715 = 1906073) B1906073
theorem B1270775 : Blo 846354 1270775 := bstep (se 1 (by rfl) ⟨953081, by rfl⟩ : syracuseStep 1270775 = 1906163) B1906163
theorem B1270799 : Blo 846354 1270799 := bstep (se 1 (by rfl) ⟨953099, by rfl⟩ : syracuseStep 1270799 = 1906199) B1906199
theorem B1270841 : Blo 846354 1270841 := bstep (se 2 (by rfl) ⟨476565, by rfl⟩ : syracuseStep 1270841 = 953131) B953131
theorem B1270919 : Blo 846354 1270919 := bstep (se 1 (by rfl) ⟨953189, by rfl⟩ : syracuseStep 1270919 = 1906379) B1906379
theorem B1270955 : Blo 846354 1270955 := bstep (se 1 (by rfl) ⟨953216, by rfl⟩ : syracuseStep 1270955 = 1906433) B1906433
theorem B1270985 : Blo 846354 1270985 := bstep (se 2 (by rfl) ⟨476619, by rfl⟩ : syracuseStep 1270985 = 953239) B953239
theorem B1074475 : Blo 846354 1074475 := bstep (se 1 (by rfl) ⟨805856, by rfl⟩ : syracuseStep 1074475 = 1611713) B1611713
theorem B1205561 : Blo 846354 1205561 := bstep (se 2 (by rfl) ⟨452085, by rfl⟩ : syracuseStep 1205561 = 904171) B904171
theorem B1271099 : Blo 846354 1271099 := bstep (se 1 (by rfl) ⟨953324, by rfl⟩ : syracuseStep 1271099 = 1906649) B1906649
theorem B1271159 : Blo 846354 1271159 := bstep (se 1 (by rfl) ⟨953369, by rfl⟩ : syracuseStep 1271159 = 1906739) B1906739
theorem B1271183 : Blo 846354 1271183 := bstep (se 1 (by rfl) ⟨953387, by rfl⟩ : syracuseStep 1271183 = 1906775) B1906775
theorem B1271225 : Blo 846354 1271225 := bstep (se 2 (by rfl) ⟨476709, by rfl⟩ : syracuseStep 1271225 = 953419) B953419
theorem B1271303 : Blo 846354 1271303 := bstep (se 1 (by rfl) ⟨953477, by rfl⟩ : syracuseStep 1271303 = 1906955) B1906955
theorem B1074703 : Blo 846354 1074703 := bstep (se 1 (by rfl) ⟨806027, by rfl⟩ : syracuseStep 1074703 = 1612055) B1612055
theorem B1271339 : Blo 846354 1271339 := bstep (se 1 (by rfl) ⟨953504, by rfl⟩ : syracuseStep 1271339 = 1907009) B1907009
theorem B6121003 : Blo 846354 6121003 := bstep (se 1 (by rfl) ⟨4590752, by rfl⟩ : syracuseStep 6121003 = 9181505) B9181505
theorem B1271369 : Blo 846354 1271369 := bstep (se 2 (by rfl) ⟨476763, by rfl⟩ : syracuseStep 1271369 = 953527) B953527
theorem B15492707 : Blo 846354 15492707 := bstep (se 1 (by rfl) ⟨11619530, by rfl⟩ : syracuseStep 15492707 = 23239061) B23239061
theorem B1271483 : Blo 846354 1271483 := bstep (se 1 (by rfl) ⟨953612, by rfl⟩ : syracuseStep 1271483 = 1907225) B1907225
theorem B1271543 : Blo 846354 1271543 := bstep (se 1 (by rfl) ⟨953657, by rfl⟩ : syracuseStep 1271543 = 1907315) B1907315
theorem B1271567 : Blo 846354 1271567 := bstep (se 1 (by rfl) ⟨953675, by rfl⟩ : syracuseStep 1271567 = 1907351) B1907351
theorem B1271609 : Blo 846354 1271609 := bstep (se 2 (by rfl) ⟨476853, by rfl⟩ : syracuseStep 1271609 = 953707) B953707
theorem B1271687 : Blo 846354 1271687 := bstep (se 1 (by rfl) ⟨953765, by rfl⟩ : syracuseStep 1271687 = 1907531) B1907531
theorem B1271723 : Blo 846354 1271723 := bstep (se 1 (by rfl) ⟨953792, by rfl⟩ : syracuseStep 1271723 = 1907585) B1907585
theorem B1271753 : Blo 846354 1271753 := bstep (se 2 (by rfl) ⟨476907, by rfl⟩ : syracuseStep 1271753 = 953815) B953815
theorem B2418731 : Blo 846354 2418731 := bstep (se 1 (by rfl) ⟨1814048, by rfl⟩ : syracuseStep 2418731 = 3628097) B3628097
theorem B1271867 : Blo 846354 1271867 := bstep (se 1 (by rfl) ⟨953900, by rfl⟩ : syracuseStep 1271867 = 1907801) B1907801
theorem B1271927 : Blo 846354 1271927 := bstep (se 1 (by rfl) ⟨953945, by rfl⟩ : syracuseStep 1271927 = 1907891) B1907891
theorem B1271951 : Blo 846354 1271951 := bstep (se 1 (by rfl) ⟨953963, by rfl⟩ : syracuseStep 1271951 = 1907927) B1907927
theorem B1271993 : Blo 846354 1271993 := bstep (se 2 (by rfl) ⟨476997, by rfl⟩ : syracuseStep 1271993 = 953995) B953995
theorem B1075447 : Blo 846354 1075447 := bstep (se 1 (by rfl) ⟨806585, by rfl⟩ : syracuseStep 1075447 = 1613171) B1613171
theorem B1272071 : Blo 846354 1272071 := bstep (se 1 (by rfl) ⟨954053, by rfl⟩ : syracuseStep 1272071 = 1908107) B1908107
theorem B2320655 : Blo 846354 2320655 := bstep (se 1 (by rfl) ⟨1740491, by rfl⟩ : syracuseStep 2320655 = 3480983) B3480983
theorem B2418959 : Blo 846354 2418959 := bstep (se 1 (by rfl) ⟨1814219, by rfl⟩ : syracuseStep 2418959 = 3628439) B3628439
theorem B1272107 : Blo 846354 1272107 := bstep (se 1 (by rfl) ⟨954080, by rfl⟩ : syracuseStep 1272107 = 1908161) B1908161
theorem B1272137 : Blo 846354 1272137 := bstep (se 2 (by rfl) ⟨477051, by rfl⟩ : syracuseStep 1272137 = 954103) B954103
theorem B1272251 : Blo 846354 1272251 := bstep (se 1 (by rfl) ⟨954188, by rfl⟩ : syracuseStep 1272251 = 1908377) B1908377
theorem B1272311 : Blo 846354 1272311 := bstep (se 1 (by rfl) ⟨954233, by rfl⟩ : syracuseStep 1272311 = 1908467) B1908467
theorem B1468943 : Blo 846354 1468943 := bstep (se 1 (by rfl) ⟨1101707, by rfl⟩ : syracuseStep 1468943 = 2203415) B2203415
theorem B1272335 : Blo 846354 1272335 := bstep (se 1 (by rfl) ⟨954251, by rfl⟩ : syracuseStep 1272335 = 1908503) B1908503
theorem B4287005 : Blo 846354 4287005 := bstep (se 3 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 4287005 = 1607627) B1607627
theorem B1272377 : Blo 846354 1272377 := bstep (se 2 (by rfl) ⟨477141, by rfl⟩ : syracuseStep 1272377 = 954283) B954283
theorem B846395 : Blo 846354 846395 := bstep (se 1 (by rfl) ⟨634796, by rfl⟩ : syracuseStep 846395 = 1269593) B1269593
theorem B1075771 : Blo 846354 1075771 := bstep (se 1 (by rfl) ⟨806828, by rfl⟩ : syracuseStep 1075771 = 1613657) B1613657
theorem B846471 : Blo 846354 846471 := bstep (se 1 (by rfl) ⟨634853, by rfl⟩ : syracuseStep 846471 = 1269707) B1269707
theorem B1272455 : Blo 846354 1272455 := bstep (se 1 (by rfl) ⟨954341, by rfl⟩ : syracuseStep 1272455 = 1908683) B1908683
theorem B846479 : Blo 846354 846479 := bstep (se 1 (by rfl) ⟨634859, by rfl⟩ : syracuseStep 846479 = 1269719) B1269719
theorem B1272491 : Blo 846354 1272491 := bstep (se 1 (by rfl) ⟨954368, by rfl⟩ : syracuseStep 1272491 = 1908737) B1908737
theorem B846523 : Blo 846354 846523 := bstep (se 1 (by rfl) ⟨634892, by rfl⟩ : syracuseStep 846523 = 1269785) B1269785
theorem B1272521 : Blo 846354 1272521 := bstep (se 2 (by rfl) ⟨477195, by rfl⟩ : syracuseStep 1272521 = 954391) B954391
theorem B846599 : Blo 846354 846599 := bstep (se 1 (by rfl) ⟨634949, by rfl⟩ : syracuseStep 846599 = 1269899) B1269899
theorem B846607 : Blo 846354 846607 := bstep (se 1 (by rfl) ⟨634955, by rfl⟩ : syracuseStep 846607 = 1269911) B1269911
theorem B5434127 : Blo 846354 5434127 := bstep (se 1 (by rfl) ⟨4075595, by rfl⟩ : syracuseStep 5434127 = 8151191) B8151191
theorem B846651 : Blo 846354 846651 := bstep (se 1 (by rfl) ⟨634988, by rfl⟩ : syracuseStep 846651 = 1269977) B1269977
theorem B1207099 : Blo 846354 1207099 := bstep (se 1 (by rfl) ⟨905324, by rfl⟩ : syracuseStep 1207099 = 1810649) B1810649
theorem B1272635 : Blo 846354 1272635 := bstep (se 1 (by rfl) ⟨954476, by rfl⟩ : syracuseStep 1272635 = 1908953) B1908953
theorem B8711027 : Blo 846354 8711027 := bstep (se 1 (by rfl) ⟨6533270, by rfl⟩ : syracuseStep 8711027 = 13066541) B13066541
theorem B9300851 : Blo 846354 9300851 := bstep (se 1 (by rfl) ⟨6975638, by rfl⟩ : syracuseStep 9300851 = 13951277) B13951277
theorem B1272695 : Blo 846354 1272695 := bstep (se 1 (by rfl) ⟨954521, by rfl⟩ : syracuseStep 1272695 = 1909043) B1909043
theorem B846727 : Blo 846354 846727 := bstep (se 1 (by rfl) ⟨635045, by rfl⟩ : syracuseStep 846727 = 1270091) B1270091
theorem B846735 : Blo 846354 846735 := bstep (se 1 (by rfl) ⟨635051, by rfl⟩ : syracuseStep 846735 = 1270103) B1270103
theorem B1272719 : Blo 846354 1272719 := bstep (se 1 (by rfl) ⟨954539, by rfl⟩ : syracuseStep 1272719 = 1909079) B1909079
theorem B1272761 : Blo 846354 1272761 := bstep (se 2 (by rfl) ⟨477285, by rfl⟩ : syracuseStep 1272761 = 954571) B954571
theorem B846779 : Blo 846354 846779 := bstep (se 1 (by rfl) ⟨635084, by rfl⟩ : syracuseStep 846779 = 1270169) B1270169
theorem B4287491 : Blo 846354 4287491 := bstep (se 1 (by rfl) ⟨3215618, by rfl⟩ : syracuseStep 4287491 = 6431237) B6431237
theorem B846855 : Blo 846354 846855 := bstep (se 1 (by rfl) ⟨635141, by rfl⟩ : syracuseStep 846855 = 1270283) B1270283
theorem B1272839 : Blo 846354 1272839 := bstep (se 1 (by rfl) ⟨954629, by rfl⟩ : syracuseStep 1272839 = 1909259) B1909259
theorem B846863 : Blo 846354 846863 := bstep (se 1 (by rfl) ⟨635147, by rfl⟩ : syracuseStep 846863 = 1270295) B1270295
theorem B1272875 : Blo 846354 1272875 := bstep (se 1 (by rfl) ⟨954656, by rfl⟩ : syracuseStep 1272875 = 1909313) B1909313
theorem B846907 : Blo 846354 846907 := bstep (se 1 (by rfl) ⟨635180, by rfl⟩ : syracuseStep 846907 = 1270361) B1270361
theorem B1272905 : Blo 846354 1272905 := bstep (se 2 (by rfl) ⟨477339, by rfl⟩ : syracuseStep 1272905 = 954679) B954679
theorem B1240183 : Blo 846354 1240183 := bstep (se 1 (by rfl) ⟨930137, by rfl⟩ : syracuseStep 1240183 = 1860275) B1860275
theorem B846983 : Blo 846354 846983 := bstep (se 1 (by rfl) ⟨635237, by rfl⟩ : syracuseStep 846983 = 1270475) B1270475
theorem B846991 : Blo 846354 846991 := bstep (se 1 (by rfl) ⟨635243, by rfl⟩ : syracuseStep 846991 = 1270487) B1270487
theorem B847035 : Blo 846354 847035 := bstep (se 1 (by rfl) ⟨635276, by rfl⟩ : syracuseStep 847035 = 1270553) B1270553
theorem B1273019 : Blo 846354 1273019 := bstep (se 1 (by rfl) ⟨954764, by rfl⟩ : syracuseStep 1273019 = 1909529) B1909529
theorem B1207543 : Blo 846354 1207543 := bstep (se 1 (by rfl) ⟨905657, by rfl⟩ : syracuseStep 1207543 = 1811315) B1811315
theorem B1273079 : Blo 846354 1273079 := bstep (se 1 (by rfl) ⟨954809, by rfl⟩ : syracuseStep 1273079 = 1909619) B1909619
theorem B847111 : Blo 846354 847111 := bstep (se 1 (by rfl) ⟨635333, by rfl⟩ : syracuseStep 847111 = 1270667) B1270667
theorem B847119 : Blo 846354 847119 := bstep (se 1 (by rfl) ⟨635339, by rfl⟩ : syracuseStep 847119 = 1270679) B1270679
theorem B1273103 : Blo 846354 1273103 := bstep (se 1 (by rfl) ⟨954827, by rfl⟩ : syracuseStep 1273103 = 1909655) B1909655
theorem B1273145 : Blo 846354 1273145 := bstep (se 2 (by rfl) ⟨477429, by rfl⟩ : syracuseStep 1273145 = 954859) B954859
theorem B847163 : Blo 846354 847163 := bstep (se 1 (by rfl) ⟨635372, by rfl⟩ : syracuseStep 847163 = 1270745) B1270745
theorem B847239 : Blo 846354 847239 := bstep (se 1 (by rfl) ⟨635429, by rfl⟩ : syracuseStep 847239 = 1270859) B1270859
theorem B1273223 : Blo 846354 1273223 := bstep (se 1 (by rfl) ⟨954917, by rfl⟩ : syracuseStep 1273223 = 1909835) B1909835
theorem B847247 : Blo 846354 847247 := bstep (se 1 (by rfl) ⟨635435, by rfl⟩ : syracuseStep 847247 = 1270871) B1270871
theorem B4353425 : Blo 846354 4353425 := bstep (se 2 (by rfl) ⟨1632534, by rfl⟩ : syracuseStep 4353425 = 3265069) B3265069
theorem B4124051 : Blo 846354 4124051 := bstep (se 1 (by rfl) ⟨3093038, by rfl⟩ : syracuseStep 4124051 = 6186077) B6186077
theorem B1273259 : Blo 846354 1273259 := bstep (se 1 (by rfl) ⟨954944, by rfl⟩ : syracuseStep 1273259 = 1909889) B1909889
theorem B847291 : Blo 846354 847291 := bstep (se 1 (by rfl) ⟨635468, by rfl⟩ : syracuseStep 847291 = 1270937) B1270937
theorem B1273289 : Blo 846354 1273289 := bstep (se 2 (by rfl) ⟨477483, by rfl⟩ : syracuseStep 1273289 = 954967) B954967
theorem B847367 : Blo 846354 847367 := bstep (se 1 (by rfl) ⟨635525, by rfl⟩ : syracuseStep 847367 = 1271051) B1271051
theorem B847375 : Blo 846354 847375 := bstep (se 1 (by rfl) ⟨635531, by rfl⟩ : syracuseStep 847375 = 1271063) B1271063
theorem B847419 : Blo 846354 847419 := bstep (se 1 (by rfl) ⟨635564, by rfl⟩ : syracuseStep 847419 = 1271129) B1271129
theorem B1273403 : Blo 846354 1273403 := bstep (se 1 (by rfl) ⟨955052, by rfl⟩ : syracuseStep 1273403 = 1910105) B1910105
theorem B1273463 : Blo 846354 1273463 := bstep (se 1 (by rfl) ⟨955097, by rfl⟩ : syracuseStep 1273463 = 1910195) B1910195
theorem B847495 : Blo 846354 847495 := bstep (se 1 (by rfl) ⟨635621, by rfl⟩ : syracuseStep 847495 = 1271243) B1271243
theorem B847503 : Blo 846354 847503 := bstep (se 1 (by rfl) ⟨635627, by rfl⟩ : syracuseStep 847503 = 1271255) B1271255
theorem B1273487 : Blo 846354 1273487 := bstep (se 1 (by rfl) ⟨955115, by rfl⟩ : syracuseStep 1273487 = 1910231) B1910231
theorem B2420371 : Blo 846354 2420371 := bstep (se 1 (by rfl) ⟨1815278, by rfl⟩ : syracuseStep 2420371 = 3630557) B3630557
theorem B1273529 : Blo 846354 1273529 := bstep (se 2 (by rfl) ⟨477573, by rfl⟩ : syracuseStep 1273529 = 955147) B955147
theorem B847547 : Blo 846354 847547 := bstep (se 1 (by rfl) ⟨635660, by rfl⟩ : syracuseStep 847547 = 1271321) B1271321
theorem B847623 : Blo 846354 847623 := bstep (se 1 (by rfl) ⟨635717, by rfl⟩ : syracuseStep 847623 = 1271435) B1271435
theorem B1273607 : Blo 846354 1273607 := bstep (se 1 (by rfl) ⟨955205, by rfl⟩ : syracuseStep 1273607 = 1910411) B1910411
theorem B847631 : Blo 846354 847631 := bstep (se 1 (by rfl) ⟨635723, by rfl⟩ : syracuseStep 847631 = 1271447) B1271447
theorem B1273643 : Blo 846354 1273643 := bstep (se 1 (by rfl) ⟨955232, by rfl⟩ : syracuseStep 1273643 = 1910465) B1910465
theorem B847675 : Blo 846354 847675 := bstep (se 1 (by rfl) ⟨635756, by rfl⟩ : syracuseStep 847675 = 1271513) B1271513
theorem B1273673 : Blo 846354 1273673 := bstep (se 2 (by rfl) ⟨477627, by rfl⟩ : syracuseStep 1273673 = 955255) B955255
theorem B2420599 : Blo 846354 2420599 := bstep (se 1 (by rfl) ⟨1815449, by rfl⟩ : syracuseStep 2420599 = 3630899) B3630899
theorem B847751 : Blo 846354 847751 := bstep (se 1 (by rfl) ⟨635813, by rfl⟩ : syracuseStep 847751 = 1271627) B1271627
theorem B847759 : Blo 846354 847759 := bstep (se 1 (by rfl) ⟨635819, by rfl⟩ : syracuseStep 847759 = 1271639) B1271639
theorem B847803 : Blo 846354 847803 := bstep (se 1 (by rfl) ⟨635852, by rfl⟩ : syracuseStep 847803 = 1271705) B1271705
theorem B1273787 : Blo 846354 1273787 := bstep (se 1 (by rfl) ⟨955340, by rfl⟩ : syracuseStep 1273787 = 1910681) B1910681
theorem B1273847 : Blo 846354 1273847 := bstep (se 1 (by rfl) ⟨955385, by rfl⟩ : syracuseStep 1273847 = 1910771) B1910771
theorem B847879 : Blo 846354 847879 := bstep (se 1 (by rfl) ⟨635909, by rfl⟩ : syracuseStep 847879 = 1271819) B1271819
theorem B847887 : Blo 846354 847887 := bstep (se 1 (by rfl) ⟨635915, by rfl⟩ : syracuseStep 847887 = 1271831) B1271831
theorem B1273871 : Blo 846354 1273871 := bstep (se 1 (by rfl) ⟨955403, by rfl⟩ : syracuseStep 1273871 = 1910807) B1910807
theorem B1208363 : Blo 846354 1208363 := bstep (se 1 (by rfl) ⟨906272, by rfl⟩ : syracuseStep 1208363 = 1812545) B1812545
theorem B1273913 : Blo 846354 1273913 := bstep (se 2 (by rfl) ⟨477717, by rfl⟩ : syracuseStep 1273913 = 955435) B955435
theorem B847931 : Blo 846354 847931 := bstep (se 1 (by rfl) ⟨635948, by rfl⟩ : syracuseStep 847931 = 1271897) B1271897
theorem B1273991 : Blo 846354 1273991 := bstep (se 1 (by rfl) ⟨955493, by rfl⟩ : syracuseStep 1273991 = 1910987) B1910987
theorem B848007 : Blo 846354 848007 := bstep (se 1 (by rfl) ⟨636005, by rfl⟩ : syracuseStep 848007 = 1272011) B1272011
theorem B848015 : Blo 846354 848015 := bstep (se 1 (by rfl) ⟨636011, by rfl⟩ : syracuseStep 848015 = 1272023) B1272023
theorem B1274027 : Blo 846354 1274027 := bstep (se 1 (by rfl) ⟨955520, by rfl⟩ : syracuseStep 1274027 = 1911041) B1911041
theorem B848059 : Blo 846354 848059 := bstep (se 1 (by rfl) ⟨636044, by rfl⟩ : syracuseStep 848059 = 1272089) B1272089
theorem B1241275 : Blo 846354 1241275 := bstep (se 1 (by rfl) ⟨930956, by rfl⟩ : syracuseStep 1241275 = 1861913) B1861913
theorem B1274057 : Blo 846354 1274057 := bstep (se 2 (by rfl) ⟨477771, by rfl⟩ : syracuseStep 1274057 = 955543) B955543
theorem B848135 : Blo 846354 848135 := bstep (se 1 (by rfl) ⟨636101, by rfl⟩ : syracuseStep 848135 = 1272203) B1272203
theorem B848143 : Blo 846354 848143 := bstep (se 1 (by rfl) ⟨636107, by rfl⟩ : syracuseStep 848143 = 1272215) B1272215
theorem B848187 : Blo 846354 848187 := bstep (se 1 (by rfl) ⟨636140, by rfl⟩ : syracuseStep 848187 = 1272281) B1272281
theorem B1274171 : Blo 846354 1274171 := bstep (se 1 (by rfl) ⟨955628, by rfl⟩ : syracuseStep 1274171 = 1911257) B1911257
theorem B1274231 : Blo 846354 1274231 := bstep (se 1 (by rfl) ⟨955673, by rfl⟩ : syracuseStep 1274231 = 1911347) B1911347
theorem B848263 : Blo 846354 848263 := bstep (se 1 (by rfl) ⟨636197, by rfl⟩ : syracuseStep 848263 = 1272395) B1272395
theorem B848271 : Blo 846354 848271 := bstep (se 1 (by rfl) ⟨636203, by rfl⟩ : syracuseStep 848271 = 1272407) B1272407
theorem B1274255 : Blo 846354 1274255 := bstep (se 1 (by rfl) ⟨955691, by rfl⟩ : syracuseStep 1274255 = 1911383) B1911383
theorem B1274297 : Blo 846354 1274297 := bstep (se 2 (by rfl) ⟨477861, by rfl⟩ : syracuseStep 1274297 = 955723) B955723
theorem B848315 : Blo 846354 848315 := bstep (se 1 (by rfl) ⟨636236, by rfl⟩ : syracuseStep 848315 = 1272473) B1272473
theorem B848391 : Blo 846354 848391 := bstep (se 1 (by rfl) ⟨636293, by rfl⟩ : syracuseStep 848391 = 1272587) B1272587
theorem B1274375 : Blo 846354 1274375 := bstep (se 1 (by rfl) ⟨955781, by rfl⟩ : syracuseStep 1274375 = 1911563) B1911563
theorem B848399 : Blo 846354 848399 := bstep (se 1 (by rfl) ⟨636299, by rfl⟩ : syracuseStep 848399 = 1272599) B1272599
theorem B3437099 : Blo 846354 3437099 := bstep (se 1 (by rfl) ⟨2577824, by rfl⟩ : syracuseStep 3437099 = 5155649) B5155649
theorem B1274411 : Blo 846354 1274411 := bstep (se 1 (by rfl) ⟨955808, by rfl⟩ : syracuseStep 1274411 = 1911617) B1911617
theorem B848443 : Blo 846354 848443 := bstep (se 1 (by rfl) ⟨636332, by rfl⟩ : syracuseStep 848443 = 1272665) B1272665
theorem B1274441 : Blo 846354 1274441 := bstep (se 2 (by rfl) ⟨477915, by rfl⟩ : syracuseStep 1274441 = 955831) B955831
theorem B4289111 : Blo 846354 4289111 := bstep (se 1 (by rfl) ⟨3216833, by rfl⟩ : syracuseStep 4289111 = 6433667) B6433667
theorem B848519 : Blo 846354 848519 := bstep (se 1 (by rfl) ⟨636389, by rfl⟩ : syracuseStep 848519 = 1272779) B1272779
theorem B848527 : Blo 846354 848527 := bstep (se 1 (by rfl) ⟨636395, by rfl⟩ : syracuseStep 848527 = 1272791) B1272791
theorem B848571 : Blo 846354 848571 := bstep (se 1 (by rfl) ⟨636428, by rfl⟩ : syracuseStep 848571 = 1272857) B1272857
theorem B1274555 : Blo 846354 1274555 := bstep (se 1 (by rfl) ⟨955916, by rfl⟩ : syracuseStep 1274555 = 1911833) B1911833
theorem B1274615 : Blo 846354 1274615 := bstep (se 1 (by rfl) ⟨955961, by rfl⟩ : syracuseStep 1274615 = 1911923) B1911923
theorem B848647 : Blo 846354 848647 := bstep (se 1 (by rfl) ⟨636485, by rfl⟩ : syracuseStep 848647 = 1272971) B1272971
theorem B848655 : Blo 846354 848655 := bstep (se 1 (by rfl) ⟨636491, by rfl⟩ : syracuseStep 848655 = 1272983) B1272983
theorem B1274639 : Blo 846354 1274639 := bstep (se 1 (by rfl) ⟨955979, by rfl⟩ : syracuseStep 1274639 = 1911959) B1911959
theorem B14512931 : Blo 846354 14512931 := bstep (se 1 (by rfl) ⟨10884698, by rfl⟩ : syracuseStep 14512931 = 21769397) B21769397
theorem B1274681 : Blo 846354 1274681 := bstep (se 2 (by rfl) ⟨478005, by rfl⟩ : syracuseStep 1274681 = 956011) B956011
theorem B848699 : Blo 846354 848699 := bstep (se 1 (by rfl) ⟨636524, by rfl⟩ : syracuseStep 848699 = 1273049) B1273049
theorem B16282457 : Blo 846354 16282457 := bstep (se 2 (by rfl) ⟨6105921, by rfl⟩ : syracuseStep 16282457 = 12211843) B12211843
theorem B848775 : Blo 846354 848775 := bstep (se 1 (by rfl) ⟨636581, by rfl⟩ : syracuseStep 848775 = 1273163) B1273163
theorem B1274759 : Blo 846354 1274759 := bstep (se 1 (by rfl) ⟨956069, by rfl⟩ : syracuseStep 1274759 = 1912139) B1912139
theorem B848783 : Blo 846354 848783 := bstep (se 1 (by rfl) ⟨636587, by rfl⟩ : syracuseStep 848783 = 1273175) B1273175
theorem B1274795 : Blo 846354 1274795 := bstep (se 1 (by rfl) ⟨956096, by rfl⟩ : syracuseStep 1274795 = 1912193) B1912193
theorem B848827 : Blo 846354 848827 := bstep (se 1 (by rfl) ⟨636620, by rfl⟩ : syracuseStep 848827 = 1273241) B1273241
theorem B1274825 : Blo 846354 1274825 := bstep (se 2 (by rfl) ⟨478059, by rfl⟩ : syracuseStep 1274825 = 956119) B956119
theorem B848903 : Blo 846354 848903 := bstep (se 1 (by rfl) ⟨636677, by rfl⟩ : syracuseStep 848903 = 1273355) B1273355
theorem B848911 : Blo 846354 848911 := bstep (se 1 (by rfl) ⟨636683, by rfl⟩ : syracuseStep 848911 = 1273367) B1273367
theorem B848955 : Blo 846354 848955 := bstep (se 1 (by rfl) ⟨636716, by rfl⟩ : syracuseStep 848955 = 1273433) B1273433
theorem B1274939 : Blo 846354 1274939 := bstep (se 1 (by rfl) ⟨956204, by rfl⟩ : syracuseStep 1274939 = 1912409) B1912409
theorem B4289597 : Blo 846354 4289597 := bstep (se 3 (by rfl) ⟨804299, by rfl⟩ : syracuseStep 4289597 = 1608599) B1608599
theorem B1274999 : Blo 846354 1274999 := bstep (se 1 (by rfl) ⟨956249, by rfl⟩ : syracuseStep 1274999 = 1912499) B1912499
theorem B849031 : Blo 846354 849031 := bstep (se 1 (by rfl) ⟨636773, by rfl⟩ : syracuseStep 849031 = 1273547) B1273547
theorem B849039 : Blo 846354 849039 := bstep (se 1 (by rfl) ⟨636779, by rfl⟩ : syracuseStep 849039 = 1273559) B1273559
theorem B1275023 : Blo 846354 1275023 := bstep (se 1 (by rfl) ⟨956267, by rfl⟩ : syracuseStep 1275023 = 1912535) B1912535
theorem B1275065 : Blo 846354 1275065 := bstep (se 2 (by rfl) ⟨478149, by rfl⟩ : syracuseStep 1275065 = 956299) B956299
theorem B849083 : Blo 846354 849083 := bstep (se 1 (by rfl) ⟨636812, by rfl⟩ : syracuseStep 849083 = 1273625) B1273625
theorem B2290889 : Blo 846354 2290889 := bstep (se 2 (by rfl) ⟨859083, by rfl⟩ : syracuseStep 2290889 = 1718167) B1718167
theorem B849159 : Blo 846354 849159 := bstep (se 1 (by rfl) ⟨636869, by rfl⟩ : syracuseStep 849159 = 1273739) B1273739
theorem B1275143 : Blo 846354 1275143 := bstep (se 1 (by rfl) ⟨956357, by rfl⟩ : syracuseStep 1275143 = 1912715) B1912715
theorem B849167 : Blo 846354 849167 := bstep (se 1 (by rfl) ⟨636875, by rfl⟩ : syracuseStep 849167 = 1273751) B1273751
theorem B10876193 : Blo 846354 10876193 := bstep (se 2 (by rfl) ⟨4078572, by rfl⟩ : syracuseStep 10876193 = 8157145) B8157145
theorem B1275179 : Blo 846354 1275179 := bstep (se 1 (by rfl) ⟨956384, by rfl⟩ : syracuseStep 1275179 = 1912769) B1912769
theorem B849211 : Blo 846354 849211 := bstep (se 1 (by rfl) ⟨636908, by rfl⟩ : syracuseStep 849211 = 1273817) B1273817
theorem B1275209 : Blo 846354 1275209 := bstep (se 2 (by rfl) ⟨478203, by rfl⟩ : syracuseStep 1275209 = 956407) B956407
theorem B849287 : Blo 846354 849287 := bstep (se 1 (by rfl) ⟨636965, by rfl⟩ : syracuseStep 849287 = 1273931) B1273931
theorem B849295 : Blo 846354 849295 := bstep (se 1 (by rfl) ⟨636971, by rfl⟩ : syracuseStep 849295 = 1273943) B1273943
theorem B849339 : Blo 846354 849339 := bstep (se 1 (by rfl) ⟨637004, by rfl⟩ : syracuseStep 849339 = 1274009) B1274009
theorem B1275323 : Blo 846354 1275323 := bstep (se 1 (by rfl) ⟨956492, by rfl⟩ : syracuseStep 1275323 = 1912985) B1912985
theorem B2618825 : Blo 846354 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B1275383 : Blo 846354 1275383 := bstep (se 1 (by rfl) ⟨956537, by rfl⟩ : syracuseStep 1275383 = 1913075) B1913075
theorem B849415 : Blo 846354 849415 := bstep (se 1 (by rfl) ⟨637061, by rfl⟩ : syracuseStep 849415 = 1274123) B1274123
theorem B849423 : Blo 846354 849423 := bstep (se 1 (by rfl) ⟨637067, by rfl⟩ : syracuseStep 849423 = 1274135) B1274135
theorem B1275407 : Blo 846354 1275407 := bstep (se 1 (by rfl) ⟨956555, by rfl⟩ : syracuseStep 1275407 = 1913111) B1913111
theorem B3864107 : Blo 846354 3864107 := bstep (se 1 (by rfl) ⟨2898080, by rfl⟩ : syracuseStep 3864107 = 5796161) B5796161
theorem B1275449 : Blo 846354 1275449 := bstep (se 2 (by rfl) ⟨478293, by rfl⟩ : syracuseStep 1275449 = 956587) B956587
theorem B849467 : Blo 846354 849467 := bstep (se 1 (by rfl) ⟨637100, by rfl⟩ : syracuseStep 849467 = 1274201) B1274201
theorem B849543 : Blo 846354 849543 := bstep (se 1 (by rfl) ⟨637157, by rfl⟩ : syracuseStep 849543 = 1274315) B1274315
theorem B1275527 : Blo 846354 1275527 := bstep (se 1 (by rfl) ⟨956645, by rfl⟩ : syracuseStep 1275527 = 1913291) B1913291
theorem B849551 : Blo 846354 849551 := bstep (se 1 (by rfl) ⟨637163, by rfl⟩ : syracuseStep 849551 = 1274327) B1274327
theorem B849595 : Blo 846354 849595 := bstep (se 1 (by rfl) ⟨637196, by rfl⟩ : syracuseStep 849595 = 1274393) B1274393
theorem B9795289 : Blo 846354 9795289 := bstep (se 2 (by rfl) ⟨3673233, by rfl⟩ : syracuseStep 9795289 = 7346467) B7346467
theorem B849671 : Blo 846354 849671 := bstep (se 1 (by rfl) ⟨637253, by rfl⟩ : syracuseStep 849671 = 1274507) B1274507
theorem B849679 : Blo 846354 849679 := bstep (se 1 (by rfl) ⟨637259, by rfl⟩ : syracuseStep 849679 = 1274519) B1274519
theorem B849723 : Blo 846354 849723 := bstep (se 1 (by rfl) ⟨637292, by rfl⟩ : syracuseStep 849723 = 1274585) B1274585
theorem B6453107 : Blo 846354 6453107 := bstep (se 1 (by rfl) ⟨4839830, by rfl⟩ : syracuseStep 6453107 = 9679661) B9679661
theorem B1210231 : Blo 846354 1210231 := bstep (se 1 (by rfl) ⟨907673, by rfl⟩ : syracuseStep 1210231 = 1815347) B1815347
theorem B849799 : Blo 846354 849799 := bstep (se 1 (by rfl) ⟨637349, by rfl⟩ : syracuseStep 849799 = 1274699) B1274699
theorem B849807 : Blo 846354 849807 := bstep (se 1 (by rfl) ⟨637355, by rfl⟩ : syracuseStep 849807 = 1274711) B1274711
theorem B2717587 : Blo 846354 2717587 := bstep (se 1 (by rfl) ⟨2038190, by rfl⟩ : syracuseStep 2717587 = 4076381) B4076381
theorem B849851 : Blo 846354 849851 := bstep (se 1 (by rfl) ⟨637388, by rfl⟩ : syracuseStep 849851 = 1274777) B1274777
theorem B849927 : Blo 846354 849927 := bstep (se 1 (by rfl) ⟨637445, by rfl⟩ : syracuseStep 849927 = 1274891) B1274891
theorem B849935 : Blo 846354 849935 := bstep (se 1 (by rfl) ⟨637451, by rfl⟩ : syracuseStep 849935 = 1274903) B1274903
theorem B849979 : Blo 846354 849979 := bstep (se 1 (by rfl) ⟨637484, by rfl⟩ : syracuseStep 849979 = 1274969) B1274969
theorem B850055 : Blo 846354 850055 := bstep (se 1 (by rfl) ⟨637541, by rfl⟩ : syracuseStep 850055 = 1275083) B1275083
theorem B850063 : Blo 846354 850063 := bstep (se 1 (by rfl) ⟨637547, by rfl⟩ : syracuseStep 850063 = 1275095) B1275095
theorem B850107 : Blo 846354 850107 := bstep (se 1 (by rfl) ⟨637580, by rfl⟩ : syracuseStep 850107 = 1275161) B1275161
theorem B850183 : Blo 846354 850183 := bstep (se 1 (by rfl) ⟨637637, by rfl⟩ : syracuseStep 850183 = 1275275) B1275275
theorem B850191 : Blo 846354 850191 := bstep (se 1 (by rfl) ⟨637643, by rfl⟩ : syracuseStep 850191 = 1275287) B1275287
theorem B850235 : Blo 846354 850235 := bstep (se 1 (by rfl) ⟨637676, by rfl⟩ : syracuseStep 850235 = 1275353) B1275353
theorem B850311 : Blo 846354 850311 := bstep (se 1 (by rfl) ⟨637733, by rfl⟩ : syracuseStep 850311 = 1275467) B1275467
theorem B850319 : Blo 846354 850319 := bstep (se 1 (by rfl) ⟨637739, by rfl⟩ : syracuseStep 850319 = 1275479) B1275479
theorem B1833673 : Blo 846354 1833673 := bstep (se 2 (by rfl) ⟨687627, by rfl⟩ : syracuseStep 1833673 = 1375255) B1375255
theorem B8157989 : Blo 846354 8157989 := bstep (se 4 (by rfl) ⟨764811, by rfl⟩ : syracuseStep 8157989 = 1529623) B1529623
theorem B4291379 : Blo 846354 4291379 := bstep (se 1 (by rfl) ⟨3218534, by rfl⟩ : syracuseStep 4291379 = 6437069) B6437069
theorem B4291703 : Blo 846354 4291703 := bstep (se 1 (by rfl) ⟨3218777, by rfl⟩ : syracuseStep 4291703 = 6437555) B6437555
theorem B2293051 : Blo 846354 2293051 := bstep (se 1 (by rfl) ⟨1719788, by rfl⟩ : syracuseStep 2293051 = 3439577) B3439577
theorem B3669547 : Blo 846354 3669547 := bstep (se 1 (by rfl) ⟨2752160, by rfl⟩ : syracuseStep 3669547 = 5504321) B5504321
theorem B6520439 : Blo 846354 6520439 := bstep (se 1 (by rfl) ⟨4890329, by rfl⟩ : syracuseStep 6520439 = 9780659) B9780659
theorem B8158913 : Blo 846354 8158913 := bstep (se 2 (by rfl) ⟨3059592, by rfl⟩ : syracuseStep 8158913 = 6119185) B6119185
theorem B1146569 : Blo 846354 1146569 := bstep (se 2 (by rfl) ⟨429963, by rfl⟩ : syracuseStep 1146569 = 859927) B859927
theorem B2719433 : Blo 846354 2719433 := bstep (se 2 (by rfl) ⟨1019787, by rfl⟩ : syracuseStep 2719433 = 2039575) B2039575
theorem B16514891 : Blo 846354 16514891 := bstep (se 1 (by rfl) ⟨12386168, by rfl⟩ : syracuseStep 16514891 = 24772337) B24772337
theorem B13762457 : Blo 846354 13762457 := bstep (se 2 (by rfl) ⟨5160921, by rfl⟩ : syracuseStep 13762457 = 10321843) B10321843
theorem B2753551 : Blo 846354 2753551 := bstep (se 1 (by rfl) ⟨2065163, by rfl⟩ : syracuseStep 2753551 = 4130327) B4130327
theorem B3441911 : Blo 846354 3441911 := bstep (se 1 (by rfl) ⟨2581433, by rfl⟩ : syracuseStep 3441911 = 5162867) B5162867
theorem B7079183 : Blo 846354 7079183 := bstep (se 1 (by rfl) ⟨5309387, by rfl⟩ : syracuseStep 7079183 = 10618775) B10618775
theorem B1607339 : Blo 846354 1607339 := bstep (se 1 (by rfl) ⟨1205504, by rfl⟩ : syracuseStep 1607339 = 2411009) B2411009
theorem B952159 : Blo 846354 952159 := bstep (se 1 (by rfl) ⟨714119, by rfl⟩ : syracuseStep 952159 = 1428239) B1428239
theorem B2295647 : Blo 846354 2295647 := bstep (se 1 (by rfl) ⟨1721735, by rfl⟩ : syracuseStep 2295647 = 3443471) B3443471
theorem B26150809 : Blo 846354 26150809 := bstep (se 2 (by rfl) ⟨9806553, by rfl⟩ : syracuseStep 26150809 = 19613107) B19613107
theorem B1935265 : Blo 846354 1935265 := bstep (se 2 (by rfl) ⟨725724, by rfl⟩ : syracuseStep 1935265 = 1451449) B1451449
theorem B8161337 : Blo 846354 8161337 := bstep (se 2 (by rfl) ⟨3060501, by rfl⟩ : syracuseStep 8161337 = 6121003) B6121003
theorem B952519 : Blo 846354 952519 := bstep (se 1 (by rfl) ⟨714389, by rfl⟩ : syracuseStep 952519 = 1428779) B1428779
theorem B3213857 : Blo 846354 3213857 := bstep (se 2 (by rfl) ⟨1205196, by rfl⟩ : syracuseStep 3213857 = 2410393) B2410393
theorem B3214039 : Blo 846354 3214039 := bstep (se 1 (by rfl) ⟨2410529, by rfl⟩ : syracuseStep 3214039 = 4821059) B4821059
theorem B2329337 : Blo 846354 2329337 := bstep (se 2 (by rfl) ⟨873501, by rfl⟩ : syracuseStep 2329337 = 1747003) B1747003
theorem B3214343 : Blo 846354 3214343 := bstep (se 1 (by rfl) ⟨2410757, by rfl⟩ : syracuseStep 3214343 = 4821515) B4821515
theorem B953383 : Blo 846354 953383 := bstep (se 1 (by rfl) ⟨715037, by rfl⟩ : syracuseStep 953383 = 1430075) B1430075
theorem B55086155 : Blo 846354 55086155 := bstep (se 1 (by rfl) ⟨41314616, by rfl⟩ : syracuseStep 55086155 = 82629233) B82629233
theorem B1609055 : Blo 846354 1609055 := bstep (se 1 (by rfl) ⟨1206791, by rfl⟩ : syracuseStep 1609055 = 2413583) B2413583
theorem B3214829 : Blo 846354 3214829 := bstep (se 3 (by rfl) ⟨602780, by rfl⟩ : syracuseStep 3214829 = 1205561) B1205561
theorem B1904327 : Blo 846354 1904327 := bstep (se 1 (by rfl) ⟨1428245, by rfl⟩ : syracuseStep 1904327 = 2856491) B2856491
theorem B1609465 : Blo 846354 1609465 := bstep (se 2 (by rfl) ⟨603549, by rfl⟩ : syracuseStep 1609465 = 1207099) B1207099
theorem B6983533 : Blo 846354 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B26480533 : Blo 846354 26480533 := bstep (se 6 (by rfl) ⟨620637, by rfl⟩ : syracuseStep 26480533 = 1241275) B1241275
theorem B1609807 : Blo 846354 1609807 := bstep (se 1 (by rfl) ⟨1207355, by rfl⟩ : syracuseStep 1609807 = 2414711) B2414711
theorem B1610057 : Blo 846354 1610057 := bstep (se 2 (by rfl) ⟨603771, by rfl⟩ : syracuseStep 1610057 = 1207543) B1207543
theorem B2298241 : Blo 846354 2298241 := bstep (se 2 (by rfl) ⟨861840, by rfl⟩ : syracuseStep 2298241 = 1723681) B1723681
theorem B22385161 : Blo 846354 22385161 := bstep (se 2 (by rfl) ⟨8394435, by rfl⟩ : syracuseStep 22385161 = 16788871) B16788871
theorem B1905191 : Blo 846354 1905191 := bstep (se 1 (by rfl) ⟨1428893, by rfl⟩ : syracuseStep 1905191 = 2857787) B2857787
theorem B3215969 : Blo 846354 3215969 := bstep (se 2 (by rfl) ⟨1205988, by rfl⟩ : syracuseStep 3215969 = 2411977) B2411977
theorem B955003 : Blo 846354 955003 := bstep (se 1 (by rfl) ⟨716252, by rfl⟩ : syracuseStep 955003 = 1432505) B1432505
theorem B4133635 : Blo 846354 4133635 := bstep (se 1 (by rfl) ⟨3100226, by rfl⟩ : syracuseStep 4133635 = 6200453) B6200453
theorem B9573137 : Blo 846354 9573137 := bstep (se 2 (by rfl) ⟨3589926, by rfl⟩ : syracuseStep 9573137 = 7179853) B7179853
theorem B1905515 : Blo 846354 1905515 := bstep (se 1 (by rfl) ⟨1429136, by rfl⟩ : syracuseStep 1905515 = 2858273) B2858273
theorem B1905569 : Blo 846354 1905569 := bstep (se 2 (by rfl) ⟨714588, by rfl⟩ : syracuseStep 1905569 = 1429177) B1429177
theorem B9180161 : Blo 846354 9180161 := bstep (se 2 (by rfl) ⟨3442560, by rfl⟩ : syracuseStep 9180161 = 6885121) B6885121
theorem B955471 : Blo 846354 955471 := bstep (se 1 (by rfl) ⟨716603, by rfl⟩ : syracuseStep 955471 = 1433207) B1433207
theorem B1610923 : Blo 846354 1610923 := bstep (se 1 (by rfl) ⟨1208192, by rfl⟩ : syracuseStep 1610923 = 2416385) B2416385
theorem B1905911 : Blo 846354 1905911 := bstep (se 1 (by rfl) ⟨1429433, by rfl⟩ : syracuseStep 1905911 = 2858867) B2858867
theorem B1610999 : Blo 846354 1610999 := bstep (se 1 (by rfl) ⟨1208249, by rfl⟩ : syracuseStep 1610999 = 2416499) B2416499
theorem B6886745 : Blo 846354 6886745 := bstep (se 2 (by rfl) ⟨2582529, by rfl⟩ : syracuseStep 6886745 = 5165059) B5165059
theorem B1611227 : Blo 846354 1611227 := bstep (se 1 (by rfl) ⟨1208420, by rfl⟩ : syracuseStep 1611227 = 2416841) B2416841
theorem B955867 : Blo 846354 955867 := bstep (se 1 (by rfl) ⟨716900, by rfl⟩ : syracuseStep 955867 = 1433801) B1433801
theorem B3216955 : Blo 846354 3216955 := bstep (se 1 (by rfl) ⟨2412716, by rfl⟩ : syracuseStep 3216955 = 4825433) B4825433
theorem B2856545 : Blo 846354 2856545 := bstep (se 2 (by rfl) ⟨1071204, by rfl⟩ : syracuseStep 2856545 = 2142409) B2142409
theorem B8165063 : Blo 846354 8165063 := bstep (se 1 (by rfl) ⟨6123797, by rfl⟩ : syracuseStep 8165063 = 12247595) B12247595
theorem B1906505 : Blo 846354 1906505 := bstep (se 2 (by rfl) ⟨714939, by rfl⟩ : syracuseStep 1906505 = 1429879) B1429879
theorem B3217259 : Blo 846354 3217259 := bstep (se 1 (by rfl) ⟨2412944, by rfl⟩ : syracuseStep 3217259 = 4825889) B4825889
theorem B956335 : Blo 846354 956335 := bstep (se 1 (by rfl) ⟨717251, by rfl⟩ : syracuseStep 956335 = 1434503) B1434503
theorem B3217427 : Blo 846354 3217427 := bstep (se 1 (by rfl) ⟨2413070, by rfl⟩ : syracuseStep 3217427 = 4826141) B4826141
theorem B10328471 : Blo 846354 10328471 := bstep (se 1 (by rfl) ⟨7746353, by rfl⟩ : syracuseStep 10328471 = 15492707) B15492707
theorem B1448527 : Blo 846354 1448527 := bstep (se 1 (by rfl) ⟨1086395, by rfl⟩ : syracuseStep 1448527 = 2172791) B2172791
theorem B1907297 : Blo 846354 1907297 := bstep (se 2 (by rfl) ⟨715236, by rfl⟩ : syracuseStep 1907297 = 1430473) B1430473
theorem B1612487 : Blo 846354 1612487 := bstep (se 1 (by rfl) ⟨1209365, by rfl⟩ : syracuseStep 1612487 = 2418731) B2418731
theorem B1809145 : Blo 846354 1809145 := bstep (se 2 (by rfl) ⟨678429, by rfl⟩ : syracuseStep 1809145 = 1356859) B1356859
theorem B1612639 : Blo 846354 1612639 := bstep (se 1 (by rfl) ⟨1209479, by rfl⟩ : syracuseStep 1612639 = 2418959) B2418959
theorem B18619253 : Blo 846354 18619253 := bstep (se 5 (by rfl) ⟨872777, by rfl⟩ : syracuseStep 18619253 = 1745555) B1745555
theorem B1907639 : Blo 846354 1907639 := bstep (se 1 (by rfl) ⟨1430729, by rfl⟩ : syracuseStep 1907639 = 2861459) B2861459
theorem B2759681 : Blo 846354 2759681 := bstep (se 2 (by rfl) ⟨1034880, by rfl⟩ : syracuseStep 2759681 = 2069761) B2069761
theorem B2858003 : Blo 846354 2858003 := bstep (se 1 (by rfl) ⟨2143502, by rfl⟩ : syracuseStep 2858003 = 4287005) B4287005
theorem B4136107 : Blo 846354 4136107 := bstep (se 1 (by rfl) ⟨3102080, by rfl⟩ : syracuseStep 4136107 = 6204161) B6204161
theorem B10886339 : Blo 846354 10886339 := bstep (se 1 (by rfl) ⟨8164754, by rfl⟩ : syracuseStep 10886339 = 16329509) B16329509
theorem B6200567 : Blo 846354 6200567 := bstep (se 1 (by rfl) ⟨4650425, by rfl⟩ : syracuseStep 6200567 = 9300851) B9300851
theorem B5807351 : Blo 846354 5807351 := bstep (se 1 (by rfl) ⟨4355513, by rfl⟩ : syracuseStep 5807351 = 8711027) B8711027
theorem B2858327 : Blo 846354 2858327 := bstep (se 1 (by rfl) ⟨2143745, by rfl⟩ : syracuseStep 2858327 = 4287491) B4287491
theorem B14491061 : Blo 846354 14491061 := bstep (se 5 (by rfl) ⟨679268, by rfl⟩ : syracuseStep 14491061 = 1358537) B1358537
theorem B1908233 : Blo 846354 1908233 := bstep (se 2 (by rfl) ⟨715587, by rfl⟩ : syracuseStep 1908233 = 1431175) B1431175
theorem B1908575 : Blo 846354 1908575 := bstep (se 1 (by rfl) ⟨1431431, by rfl⟩ : syracuseStep 1908575 = 2862863) B2862863
theorem B1908755 : Blo 846354 1908755 := bstep (se 1 (by rfl) ⟨1431566, by rfl⟩ : syracuseStep 1908755 = 2863133) B2863133
theorem B6103097 : Blo 846354 6103097 := bstep (se 2 (by rfl) ⟨2288661, by rfl⟩ : syracuseStep 6103097 = 4577323) B4577323
theorem B1909097 : Blo 846354 1909097 := bstep (se 2 (by rfl) ⟨715911, by rfl⟩ : syracuseStep 1909097 = 1431823) B1431823
theorem B2859407 : Blo 846354 2859407 := bstep (se 1 (by rfl) ⟨2144555, by rfl⟩ : syracuseStep 2859407 = 4289111) B4289111
theorem B9675287 : Blo 846354 9675287 := bstep (se 1 (by rfl) ⟨7256465, by rfl⟩ : syracuseStep 9675287 = 14512931) B14512931
theorem B10854971 : Blo 846354 10854971 := bstep (se 1 (by rfl) ⟨8141228, by rfl⟩ : syracuseStep 10854971 = 16282457) B16282457
theorem B2859731 : Blo 846354 2859731 := bstep (se 1 (by rfl) ⟨2144798, by rfl⟩ : syracuseStep 2859731 = 4289597) B4289597
theorem B7250795 : Blo 846354 7250795 := bstep (se 1 (by rfl) ⟨5438096, by rfl⟩ : syracuseStep 7250795 = 10876193) B10876193
theorem B3220343 : Blo 846354 3220343 := bstep (se 1 (by rfl) ⟨2415257, by rfl⟩ : syracuseStep 3220343 = 4830515) B4830515
theorem B1909691 : Blo 846354 1909691 := bstep (se 1 (by rfl) ⟨1432268, by rfl⟩ : syracuseStep 1909691 = 2864537) B2864537
theorem B1909817 : Blo 846354 1909817 := bstep (se 2 (by rfl) ⟨716181, by rfl⟩ : syracuseStep 1909817 = 1432363) B1432363
theorem B9643211 : Blo 846354 9643211 := bstep (se 1 (by rfl) ⟨7232408, by rfl⟩ : syracuseStep 9643211 = 14464817) B14464817
theorem B4302071 : Blo 846354 4302071 := bstep (se 1 (by rfl) ⟨3226553, by rfl⟩ : syracuseStep 4302071 = 6453107) B6453107
theorem B4596983 : Blo 846354 4596983 := bstep (se 1 (by rfl) ⟨3447737, by rfl⟩ : syracuseStep 4596983 = 6895475) B6895475
theorem B1910159 : Blo 846354 1910159 := bstep (se 1 (by rfl) ⟨1432619, by rfl⟩ : syracuseStep 1910159 = 2865239) B2865239
theorem B23176849 : Blo 846354 23176849 := bstep (se 2 (by rfl) ⟨8691318, by rfl⟩ : syracuseStep 23176849 = 17382637) B17382637
theorem B1910483 : Blo 846354 1910483 := bstep (se 1 (by rfl) ⟨1432862, by rfl⟩ : syracuseStep 1910483 = 2865725) B2865725
theorem B4302557 : Blo 846354 4302557 := bstep (se 3 (by rfl) ⟨806729, by rfl⟩ : syracuseStep 4302557 = 1613459) B1613459
theorem B3057401 : Blo 846354 3057401 := bstep (se 2 (by rfl) ⟨1146525, by rfl⟩ : syracuseStep 3057401 = 2293051) B2293051
theorem B3221315 : Blo 846354 3221315 := bstep (se 1 (by rfl) ⟨2415986, by rfl⟩ : syracuseStep 3221315 = 4831973) B4831973
theorem B3057517 : Blo 846354 3057517 := bstep (se 3 (by rfl) ⟨573284, by rfl⟩ : syracuseStep 3057517 = 1146569) B1146569
theorem B2860919 : Blo 846354 2860919 := bstep (se 1 (by rfl) ⟨2145689, by rfl⟩ : syracuseStep 2860919 = 4291379) B4291379
theorem B4827073 : Blo 846354 4827073 := bstep (se 2 (by rfl) ⟨1810152, by rfl⟩ : syracuseStep 4827073 = 3620305) B3620305
theorem B4892729 : Blo 846354 4892729 := bstep (se 2 (by rfl) ⟨1834773, by rfl⟩ : syracuseStep 4892729 = 3669547) B3669547
theorem B2861135 : Blo 846354 2861135 := bstep (se 1 (by rfl) ⟨2145851, by rfl⟩ : syracuseStep 2861135 = 4291703) B4291703
theorem B1288553 : Blo 846354 1288553 := bstep (se 2 (by rfl) ⟨483207, by rfl⟩ : syracuseStep 1288553 = 966415) B966415
theorem B2861513 : Blo 846354 2861513 := bstep (se 2 (by rfl) ⟨1073067, by rfl⟩ : syracuseStep 2861513 = 2146135) B2146135
theorem B1812955 : Blo 846354 1812955 := bstep (se 1 (by rfl) ⟨1359716, by rfl⟩ : syracuseStep 1812955 = 2719433) B2719433
theorem B1911419 : Blo 846354 1911419 := bstep (se 1 (by rfl) ⟨1433564, by rfl⟩ : syracuseStep 1911419 = 2867129) B2867129
theorem B2861783 : Blo 846354 2861783 := bstep (se 1 (by rfl) ⟨2146337, by rfl⟩ : syracuseStep 2861783 = 4292675) B4292675
theorem B1911545 : Blo 846354 1911545 := bstep (se 2 (by rfl) ⟨716829, by rfl⟩ : syracuseStep 1911545 = 1433659) B1433659
theorem B3222301 : Blo 846354 3222301 := bstep (se 3 (by rfl) ⟨604181, by rfl⟩ : syracuseStep 3222301 = 1208363) B1208363
theorem B2861999 : Blo 846354 2861999 := bstep (se 1 (by rfl) ⟨2146499, by rfl⟩ : syracuseStep 2861999 = 4292999) B4292999
theorem B5975005 : Blo 846354 5975005 := bstep (se 3 (by rfl) ⟨1120313, by rfl⟩ : syracuseStep 5975005 = 2240627) B2240627
theorem B1911815 : Blo 846354 1911815 := bstep (se 1 (by rfl) ⟨1433861, by rfl⟩ : syracuseStep 1911815 = 2867723) B2867723
theorem B1911887 : Blo 846354 1911887 := bstep (se 1 (by rfl) ⟨1433915, by rfl⟩ : syracuseStep 1911887 = 2867831) B2867831
theorem B7253185 : Blo 846354 7253185 := bstep (se 2 (by rfl) ⟨2719944, by rfl⟩ : syracuseStep 7253185 = 5439889) B5439889
theorem B9186733 : Blo 846354 9186733 := bstep (se 3 (by rfl) ⟨1722512, by rfl⟩ : syracuseStep 9186733 = 3445025) B3445025
theorem B1912283 : Blo 846354 1912283 := bstep (se 1 (by rfl) ⟨1434212, by rfl⟩ : syracuseStep 1912283 = 2868425) B2868425
theorem B1453967 : Blo 846354 1453967 := bstep (se 1 (by rfl) ⟨1090475, by rfl⟩ : syracuseStep 1453967 = 2180951) B2180951
theorem B1912751 : Blo 846354 1912751 := bstep (se 1 (by rfl) ⟨1434563, by rfl⟩ : syracuseStep 1912751 = 2869127) B2869127
theorem B4075535 : Blo 846354 4075535 := bstep (se 1 (by rfl) ⟨3056651, by rfl⟩ : syracuseStep 4075535 = 6113303) B6113303
theorem B1355815 : Blo 846354 1355815 := bstep (se 1 (by rfl) ⟨1016861, by rfl⟩ : syracuseStep 1355815 = 2033723) B2033723
theorem B1913003 : Blo 846354 1913003 := bstep (se 1 (by rfl) ⟨1434752, by rfl⟩ : syracuseStep 1913003 = 2869505) B2869505
theorem B2142683 : Blo 846354 2142683 := bstep (se 1 (by rfl) ⟨1607012, by rfl⟩ : syracuseStep 2142683 = 3214025) B3214025
theorem B2896669 : Blo 846354 2896669 := bstep (se 3 (by rfl) ⟨543125, by rfl⟩ : syracuseStep 2896669 = 1086251) B1086251
theorem B3060575 : Blo 846354 3060575 := bstep (se 1 (by rfl) ⟨2295431, by rfl⟩ : syracuseStep 3060575 = 4590863) B4590863
theorem B2864375 : Blo 846354 2864375 := bstep (se 1 (by rfl) ⟨2148281, by rfl⟩ : syracuseStep 2864375 = 4296563) B4296563
theorem B1357231 : Blo 846354 1357231 := bstep (se 1 (by rfl) ⟨1017923, by rfl⟩ : syracuseStep 1357231 = 2035847) B2035847
theorem B2864699 : Blo 846354 2864699 := bstep (se 1 (by rfl) ⟨2148524, by rfl⟩ : syracuseStep 2864699 = 4297049) B4297049
theorem B2143867 : Blo 846354 2143867 := bstep (se 1 (by rfl) ⟨1607900, by rfl⟩ : syracuseStep 2143867 = 3215801) B3215801
theorem B15513281 : Blo 846354 15513281 := bstep (se 2 (by rfl) ⟨5817480, by rfl⟩ : syracuseStep 15513281 = 11634961) B11634961
theorem B46970609 : Blo 846354 46970609 := bstep (se 2 (by rfl) ⟨17613978, by rfl⟩ : syracuseStep 46970609 = 35227957) B35227957
theorem B2864969 : Blo 846354 2864969 := bstep (se 2 (by rfl) ⟨1074363, by rfl⟩ : syracuseStep 2864969 = 2148727) B2148727
theorem B1718329 : Blo 846354 1718329 := bstep (se 2 (by rfl) ⟨644373, by rfl⟩ : syracuseStep 1718329 = 1288747) B1288747
theorem B1292639 : Blo 846354 1292639 := bstep (se 1 (by rfl) ⟨969479, by rfl⟩ : syracuseStep 1292639 = 1938959) B1938959
theorem B6207877 : Blo 846354 6207877 := bstep (se 4 (by rfl) ⟨581988, by rfl⟩ : syracuseStep 6207877 = 1163977) B1163977
theorem B1653577 : Blo 846354 1653577 := bstep (se 2 (by rfl) ⟨620091, by rfl⟩ : syracuseStep 1653577 = 1240183) B1240183
theorem B3226463 : Blo 846354 3226463 := bstep (se 1 (by rfl) ⟨2419847, by rfl⟩ : syracuseStep 3226463 = 4839695) B4839695
theorem B3619691 : Blo 846354 3619691 := bstep (se 1 (by rfl) ⟨2714768, by rfl⟩ : syracuseStep 3619691 = 5429537) B5429537
theorem B9649043 : Blo 846354 9649043 := bstep (se 1 (by rfl) ⟨7236782, by rfl⟩ : syracuseStep 9649043 = 14473565) B14473565
theorem B2866103 : Blo 846354 2866103 := bstep (se 1 (by rfl) ⟨2149577, by rfl⟩ : syracuseStep 2866103 = 4299155) B4299155
theorem B6438041 : Blo 846354 6438041 := bstep (se 2 (by rfl) ⟨2414265, by rfl⟩ : syracuseStep 6438041 = 4828531) B4828531
theorem B2866697 : Blo 846354 2866697 := bstep (se 2 (by rfl) ⟨1075011, by rfl⟩ : syracuseStep 2866697 = 2150023) B2150023
theorem B3227161 : Blo 846354 3227161 := bstep (se 2 (by rfl) ⟨1210185, by rfl⟩ : syracuseStep 3227161 = 2420371) B2420371
theorem B2211467 : Blo 846354 2211467 := bstep (se 1 (by rfl) ⟨1658600, by rfl⟩ : syracuseStep 2211467 = 3317201) B3317201
theorem B2899655 : Blo 846354 2899655 := bstep (se 1 (by rfl) ⟨2174741, by rfl⟩ : syracuseStep 2899655 = 4349483) B4349483
theorem B3227435 : Blo 846354 3227435 := bstep (se 1 (by rfl) ⟨2420576, by rfl⟩ : syracuseStep 3227435 = 4841153) B4841153
theorem B3227465 : Blo 846354 3227465 := bstep (se 2 (by rfl) ⟨1210299, by rfl⟩ : syracuseStep 3227465 = 2420599) B2420599
theorem B3719485 : Blo 846354 3719485 := bstep (se 3 (by rfl) ⟨697403, by rfl⟩ : syracuseStep 3719485 = 1394807) B1394807
theorem B2900285 : Blo 846354 2900285 := bstep (se 3 (by rfl) ⟨543803, by rfl⟩ : syracuseStep 2900285 = 1087607) B1087607
theorem B2867561 : Blo 846354 2867561 := bstep (se 2 (by rfl) ⟨1075335, by rfl⟩ : syracuseStep 2867561 = 2150671) B2150671
theorem B3064193 : Blo 846354 3064193 := bstep (se 2 (by rfl) ⟨1149072, by rfl⟩ : syracuseStep 3064193 = 2298145) B2298145
theorem B1360633 : Blo 846354 1360633 := bstep (se 2 (by rfl) ⟨510237, by rfl⟩ : syracuseStep 1360633 = 1020475) B1020475
theorem B2868155 : Blo 846354 2868155 := bstep (se 1 (by rfl) ⟨2151116, by rfl⟩ : syracuseStep 2868155 = 4302233) B4302233
theorem B9290771 : Blo 846354 9290771 := bstep (se 1 (by rfl) ⟨6968078, by rfl⟩ : syracuseStep 9290771 = 13936157) B13936157
theorem B6439985 : Blo 846354 6439985 := bstep (se 2 (by rfl) ⟨2414994, by rfl⟩ : syracuseStep 6439985 = 4829989) B4829989
theorem B9684035 : Blo 846354 9684035 := bstep (se 1 (by rfl) ⟨7263026, by rfl⟩ : syracuseStep 9684035 = 14526053) B14526053
theorem B24823331 : Blo 846354 24823331 := bstep (se 1 (by rfl) ⟨18617498, by rfl⟩ : syracuseStep 24823331 = 37234997) B37234997
theorem B3622751 : Blo 846354 3622751 := bstep (se 1 (by rfl) ⟨2717063, by rfl⟩ : syracuseStep 3622751 = 5434127) B5434127
theorem B2148191 : Blo 846354 2148191 := bstep (se 1 (by rfl) ⟨1611143, by rfl⟩ : syracuseStep 2148191 = 3222287) B3222287
theorem B2410553 : Blo 846354 2410553 := bstep (se 2 (by rfl) ⟨903957, by rfl⟩ : syracuseStep 2410553 = 1807915) B1807915
theorem B30951517 : Blo 846354 30951517 := bstep (se 3 (by rfl) ⟨5803409, by rfl⟩ : syracuseStep 30951517 = 11606819) B11606819
theorem B2410667 : Blo 846354 2410667 := bstep (se 1 (by rfl) ⟨1808000, by rfl⟩ : syracuseStep 2410667 = 3616001) B3616001
theorem B2902283 : Blo 846354 2902283 := bstep (se 1 (by rfl) ⟨2176712, by rfl⟩ : syracuseStep 2902283 = 4353425) B4353425
theorem B13060385 : Blo 846354 13060385 := bstep (se 2 (by rfl) ⟨4897644, by rfl⟩ : syracuseStep 13060385 = 9795289) B9795289
theorem B5425537 : Blo 846354 5425537 := bstep (se 2 (by rfl) ⟨2034576, by rfl⟩ : syracuseStep 5425537 = 4069153) B4069153
theorem B4835821 : Blo 846354 4835821 := bstep (se 3 (by rfl) ⟨906716, by rfl⟩ : syracuseStep 4835821 = 1813433) B1813433
theorem B3623449 : Blo 846354 3623449 := bstep (se 2 (by rfl) ⟨1358793, by rfl⟩ : syracuseStep 3623449 = 2717587) B2717587
theorem B2148889 : Blo 846354 2148889 := bstep (se 2 (by rfl) ⟨805833, by rfl⟩ : syracuseStep 2148889 = 1611667) B1611667
theorem B2869883 : Blo 846354 2869883 := bstep (se 1 (by rfl) ⟨2152412, by rfl⟩ : syracuseStep 2869883 = 4304825) B4304825
theorem B3918665 : Blo 846354 3918665 := bstep (se 2 (by rfl) ⟨1469499, by rfl⟩ : syracuseStep 3918665 = 2938999) B2938999
theorem B2149193 : Blo 846354 2149193 := bstep (se 2 (by rfl) ⟨805947, by rfl⟩ : syracuseStep 2149193 = 1611895) B1611895
theorem B1428367 : Blo 846354 1428367 := bstep (se 1 (by rfl) ⟨1071275, by rfl⟩ : syracuseStep 1428367 = 2142551) B2142551
theorem B904231 : Blo 846354 904231 := bstep (se 1 (by rfl) ⟨678173, by rfl⟩ : syracuseStep 904231 = 1356347) B1356347
theorem B1527259 : Blo 846354 1527259 := bstep (se 1 (by rfl) ⟨1145444, by rfl⟩ : syracuseStep 1527259 = 2290889) B2290889
theorem B1429049 : Blo 846354 1429049 := bstep (se 2 (by rfl) ⟨535893, by rfl⟩ : syracuseStep 1429049 = 1071787) B1071787
theorem B2444897 : Blo 846354 2444897 := bstep (se 2 (by rfl) ⟨916836, by rfl⟩ : syracuseStep 2444897 = 1833673) B1833673
theorem B2576071 : Blo 846354 2576071 := bstep (se 1 (by rfl) ⟨1932053, by rfl⟩ : syracuseStep 2576071 = 3864107) B3864107
theorem B12209885 : Blo 846354 12209885 := bstep (se 3 (by rfl) ⟨2289353, by rfl⟩ : syracuseStep 12209885 = 4578707) B4578707
theorem B7261933 : Blo 846354 7261933 := bstep (se 3 (by rfl) ⟨1361612, by rfl⟩ : syracuseStep 7261933 = 2723225) B2723225
theorem B2936737 : Blo 846354 2936737 := bstep (se 2 (by rfl) ⟨1101276, by rfl⟩ : syracuseStep 2936737 = 2202553) B2202553
theorem B2150327 : Blo 846354 2150327 := bstep (se 1 (by rfl) ⟨1612745, by rfl⟩ : syracuseStep 2150327 = 3225491) B3225491
theorem B905179 : Blo 846354 905179 := bstep (se 1 (by rfl) ⟨678884, by rfl⟩ : syracuseStep 905179 = 1357769) B1357769
theorem B1429751 : Blo 846354 1429751 := bstep (se 1 (by rfl) ⟨1072313, by rfl⟩ : syracuseStep 1429751 = 2144627) B2144627
theorem B18338177 : Blo 846354 18338177 := bstep (se 2 (by rfl) ⟨6876816, by rfl⟩ : syracuseStep 18338177 = 13753633) B13753633
theorem B2413081 : Blo 846354 2413081 := bstep (se 2 (by rfl) ⟨904905, by rfl⟩ : syracuseStep 2413081 = 1809811) B1809811
theorem B1430095 : Blo 846354 1430095 := bstep (se 1 (by rfl) ⟨1072571, by rfl⟩ : syracuseStep 1430095 = 2145143) B2145143
theorem B1430345 : Blo 846354 1430345 := bstep (se 2 (by rfl) ⟨536379, by rfl⟩ : syracuseStep 1430345 = 1072759) B1072759
theorem B2151431 : Blo 846354 2151431 := bstep (se 1 (by rfl) ⟨1613573, by rfl⟩ : syracuseStep 2151431 = 3227147) B3227147
theorem B2151481 : Blo 846354 2151481 := bstep (se 2 (by rfl) ⟨806805, by rfl⟩ : syracuseStep 2151481 = 1613611) B1613611
theorem B4346959 : Blo 846354 4346959 := bstep (se 1 (by rfl) ⟨3260219, by rfl⟩ : syracuseStep 4346959 = 6520439) B6520439
theorem B1430777 : Blo 846354 1430777 := bstep (se 2 (by rfl) ⟨536541, by rfl⟩ : syracuseStep 1430777 = 1073083) B1073083
theorem B2151785 : Blo 846354 2151785 := bstep (se 2 (by rfl) ⟨806919, by rfl⟩ : syracuseStep 2151785 = 1613839) B1613839
theorem B1430959 : Blo 846354 1430959 := bstep (se 1 (by rfl) ⟨1073219, by rfl⟩ : syracuseStep 1430959 = 2146439) B2146439
theorem B3626441 : Blo 846354 3626441 := bstep (se 2 (by rfl) ⟨1359915, by rfl⟩ : syracuseStep 3626441 = 2719831) B2719831
theorem B1431047 : Blo 846354 1431047 := bstep (se 1 (by rfl) ⟨1073285, by rfl⟩ : syracuseStep 1431047 = 2146571) B2146571
theorem B4576913 : Blo 846354 4576913 := bstep (se 2 (by rfl) ⟨1716342, by rfl⟩ : syracuseStep 4576913 = 3432685) B3432685
theorem B4085437 : Blo 846354 4085437 := bstep (se 3 (by rfl) ⟨766019, by rfl⟩ : syracuseStep 4085437 = 1532039) B1532039
theorem B1431391 : Blo 846354 1431391 := bstep (se 1 (by rfl) ⟨1073543, by rfl⟩ : syracuseStep 1431391 = 2147087) B2147087
theorem B4839263 : Blo 846354 4839263 := bstep (se 1 (by rfl) ⟨3629447, by rfl⟩ : syracuseStep 4839263 = 7258895) B7258895
theorem B1431479 : Blo 846354 1431479 := bstep (se 1 (by rfl) ⟨1073609, by rfl⟩ : syracuseStep 1431479 = 2147219) B2147219
theorem B1432073 : Blo 846354 1432073 := bstep (se 2 (by rfl) ⟨537027, by rfl⟩ : syracuseStep 1432073 = 1074055) B1074055
theorem B1432235 : Blo 846354 1432235 := bstep (se 1 (by rfl) ⟨1074176, by rfl⟩ : syracuseStep 1432235 = 2148353) B2148353
theorem B4840195 : Blo 846354 4840195 := bstep (se 1 (by rfl) ⟨3630146, by rfl⟩ : syracuseStep 4840195 = 7260293) B7260293
theorem B1072055 : Blo 846354 1072055 := bstep (se 1 (by rfl) ⟨804041, by rfl⟩ : syracuseStep 1072055 = 1608083) B1608083
theorem B1432633 : Blo 846354 1432633 := bstep (se 2 (by rfl) ⟨537237, by rfl⟩ : syracuseStep 1432633 = 1074475) B1074475
theorem B11590735 : Blo 846354 11590735 := bstep (se 1 (by rfl) ⟨8693051, by rfl⟩ : syracuseStep 11590735 = 17386103) B17386103
theorem B1072207 : Blo 846354 1072207 := bstep (se 1 (by rfl) ⟨804155, by rfl⟩ : syracuseStep 1072207 = 1608311) B1608311
theorem B1432775 : Blo 846354 1432775 := bstep (se 1 (by rfl) ⟨1074581, by rfl⟩ : syracuseStep 1432775 = 2149163) B2149163
theorem B1432937 : Blo 846354 1432937 := bstep (se 2 (by rfl) ⟨537351, by rfl⟩ : syracuseStep 1432937 = 1074703) B1074703
theorem B2415997 : Blo 846354 2415997 := bstep (se 3 (by rfl) ⟨452999, by rfl⟩ : syracuseStep 2415997 = 905999) B905999
theorem B2416225 : Blo 846354 2416225 := bstep (se 2 (by rfl) ⟨906084, by rfl⟩ : syracuseStep 2416225 = 1812169) B1812169
theorem B1433335 : Blo 846354 1433335 := bstep (se 1 (by rfl) ⟨1075001, by rfl⟩ : syracuseStep 1433335 = 2150003) B2150003
theorem B1269599 : Blo 846354 1269599 := bstep (se 1 (by rfl) ⟨952199, by rfl⟩ : syracuseStep 1269599 = 1904399) B1904399
theorem B1269611 : Blo 846354 1269611 := bstep (se 1 (by rfl) ⟨952208, by rfl⟩ : syracuseStep 1269611 = 1904417) B1904417
theorem B3432311 : Blo 846354 3432311 := bstep (se 1 (by rfl) ⟨2574233, by rfl⟩ : syracuseStep 3432311 = 5148467) B5148467
theorem B2416567 : Blo 846354 2416567 := bstep (se 1 (by rfl) ⟨1812425, by rfl⟩ : syracuseStep 2416567 = 3624851) B3624851
theorem B1433531 : Blo 846354 1433531 := bstep (se 1 (by rfl) ⟨1075148, by rfl⟩ : syracuseStep 1433531 = 2150297) B2150297
theorem B1433639 : Blo 846354 1433639 := bstep (se 1 (by rfl) ⟨1075229, by rfl⟩ : syracuseStep 1433639 = 2150459) B2150459
theorem B1269839 : Blo 846354 1269839 := bstep (se 1 (by rfl) ⟨952379, by rfl⟩ : syracuseStep 1269839 = 1904759) B1904759
theorem B1269959 : Blo 846354 1269959 := bstep (se 1 (by rfl) ⟨952469, by rfl⟩ : syracuseStep 1269959 = 1904939) B1904939
theorem B1073351 : Blo 846354 1073351 := bstep (se 1 (by rfl) ⟨805013, by rfl⟩ : syracuseStep 1073351 = 1610027) B1610027
theorem B1433929 : Blo 846354 1433929 := bstep (se 2 (by rfl) ⟨537723, by rfl⟩ : syracuseStep 1433929 = 1075447) B1075447
theorem B1532233 : Blo 846354 1532233 := bstep (se 2 (by rfl) ⟨574587, by rfl⟩ : syracuseStep 1532233 = 1149175) B1149175
theorem B1073503 : Blo 846354 1073503 := bstep (se 1 (by rfl) ⟨805127, by rfl⟩ : syracuseStep 1073503 = 1610255) B1610255
theorem B1270121 : Blo 846354 1270121 := bstep (se 2 (by rfl) ⟨476295, by rfl⟩ : syracuseStep 1270121 = 952591) B952591
theorem B1433963 : Blo 846354 1433963 := bstep (se 1 (by rfl) ⟨1075472, by rfl⟩ : syracuseStep 1433963 = 2150945) B2150945
theorem B1270199 : Blo 846354 1270199 := bstep (se 1 (by rfl) ⟨952649, by rfl⟩ : syracuseStep 1270199 = 1905299) B1905299
theorem B1270235 : Blo 846354 1270235 := bstep (se 1 (by rfl) ⟨952676, by rfl⟩ : syracuseStep 1270235 = 1905353) B1905353
theorem B1434361 : Blo 846354 1434361 := bstep (se 2 (by rfl) ⟨537885, by rfl⟩ : syracuseStep 1434361 = 1075771) B1075771
theorem B1270703 : Blo 846354 1270703 := bstep (se 1 (by rfl) ⟨953027, by rfl⟩ : syracuseStep 1270703 = 1906055) B1906055
theorem B1434631 : Blo 846354 1434631 := bstep (se 1 (by rfl) ⟨1075973, by rfl⟩ : syracuseStep 1434631 = 2151947) B2151947
theorem B1270793 : Blo 846354 1270793 := bstep (se 2 (by rfl) ⟨476547, by rfl⟩ : syracuseStep 1270793 = 953095) B953095
theorem B2417683 : Blo 846354 2417683 := bstep (se 1 (by rfl) ⟨1813262, by rfl⟩ : syracuseStep 2417683 = 3626525) B3626525
theorem B1270823 : Blo 846354 1270823 := bstep (se 1 (by rfl) ⟨953117, by rfl⟩ : syracuseStep 1270823 = 1906235) B1906235
theorem B6448247 : Blo 846354 6448247 := bstep (se 1 (by rfl) ⟨4836185, by rfl⟩ : syracuseStep 6448247 = 9672371) B9672371
theorem B1270907 : Blo 846354 1270907 := bstep (se 1 (by rfl) ⟨953180, by rfl⟩ : syracuseStep 1270907 = 1906361) B1906361
theorem B1205447 : Blo 846354 1205447 := bstep (se 1 (by rfl) ⟨904085, by rfl⟩ : syracuseStep 1205447 = 1808171) B1808171
theorem B2581751 : Blo 846354 2581751 := bstep (se 1 (by rfl) ⟨1936313, by rfl⟩ : syracuseStep 2581751 = 3872627) B3872627
theorem B1271033 : Blo 846354 1271033 := bstep (se 2 (by rfl) ⟨476637, by rfl⟩ : syracuseStep 1271033 = 953275) B953275
theorem B1271135 : Blo 846354 1271135 := bstep (se 1 (by rfl) ⟨953351, by rfl⟩ : syracuseStep 1271135 = 1906703) B1906703
theorem B2418025 : Blo 846354 2418025 := bstep (se 2 (by rfl) ⟨906759, by rfl⟩ : syracuseStep 2418025 = 1813519) B1813519
theorem B1271147 : Blo 846354 1271147 := bstep (se 1 (by rfl) ⟨953360, by rfl⟩ : syracuseStep 1271147 = 1906721) B1906721
theorem B1271375 : Blo 846354 1271375 := bstep (se 1 (by rfl) ⟨953531, by rfl⟩ : syracuseStep 1271375 = 1907063) B1907063
theorem B2418299 : Blo 846354 2418299 := bstep (se 1 (by rfl) ⟨1813724, by rfl⟩ : syracuseStep 2418299 = 3627449) B3627449
theorem B1271495 : Blo 846354 1271495 := bstep (se 1 (by rfl) ⟨953621, by rfl⟩ : syracuseStep 1271495 = 1907243) B1907243
theorem B1271657 : Blo 846354 1271657 := bstep (se 2 (by rfl) ⟨476871, by rfl⟩ : syracuseStep 1271657 = 953743) B953743
theorem B1206199 : Blo 846354 1206199 := bstep (se 1 (by rfl) ⟨904649, by rfl⟩ : syracuseStep 1206199 = 1809299) B1809299
theorem B1271735 : Blo 846354 1271735 := bstep (se 1 (by rfl) ⟨953801, by rfl⟩ : syracuseStep 1271735 = 1907603) B1907603
theorem B1271771 : Blo 846354 1271771 := bstep (se 1 (by rfl) ⟨953828, by rfl⟩ : syracuseStep 1271771 = 1907657) B1907657
theorem B2320391 : Blo 846354 2320391 := bstep (se 1 (by rfl) ⟨1740293, by rfl⟩ : syracuseStep 2320391 = 3480587) B3480587
theorem B2582699 : Blo 846354 2582699 := bstep (se 1 (by rfl) ⟨1937024, by rfl⟩ : syracuseStep 2582699 = 3874049) B3874049
theorem B2713999 : Blo 846354 2713999 := bstep (se 1 (by rfl) ⟨2035499, by rfl⟩ : syracuseStep 2713999 = 4070999) B4070999
theorem B1632673 : Blo 846354 1632673 := bstep (se 2 (by rfl) ⟨612252, by rfl⟩ : syracuseStep 1632673 = 1224505) B1224505
theorem B1272239 : Blo 846354 1272239 := bstep (se 1 (by rfl) ⟨954179, by rfl⟩ : syracuseStep 1272239 = 1908359) B1908359
theorem B1075675 : Blo 846354 1075675 := bstep (se 1 (by rfl) ⟨806756, by rfl⟩ : syracuseStep 1075675 = 1613513) B1613513
theorem B1272329 : Blo 846354 1272329 := bstep (se 2 (by rfl) ⟨477123, by rfl⟩ : syracuseStep 1272329 = 954247) B954247
theorem B846375 : Blo 846354 846375 := bstep (se 1 (by rfl) ⟨634781, by rfl⟩ : syracuseStep 846375 = 1269563) B1269563
theorem B1272359 : Blo 846354 1272359 := bstep (se 1 (by rfl) ⟨954269, by rfl⟩ : syracuseStep 1272359 = 1908539) B1908539
theorem B846415 : Blo 846354 846415 := bstep (se 1 (by rfl) ⟨634811, by rfl⟩ : syracuseStep 846415 = 1269623) B1269623
theorem B846431 : Blo 846354 846431 := bstep (se 1 (by rfl) ⟨634823, by rfl⟩ : syracuseStep 846431 = 1269647) B1269647
theorem B846459 : Blo 846354 846459 := bstep (se 1 (by rfl) ⟨634844, by rfl⟩ : syracuseStep 846459 = 1269689) B1269689
theorem B1272443 : Blo 846354 1272443 := bstep (se 1 (by rfl) ⟨954332, by rfl⟩ : syracuseStep 1272443 = 1908665) B1908665
theorem B846511 : Blo 846354 846511 := bstep (se 1 (by rfl) ⟨634883, by rfl⟩ : syracuseStep 846511 = 1269767) B1269767
theorem B846535 : Blo 846354 846535 := bstep (se 1 (by rfl) ⟨634901, by rfl⟩ : syracuseStep 846535 = 1269803) B1269803
theorem B2419415 : Blo 846354 2419415 := bstep (se 1 (by rfl) ⟨1814561, by rfl⟩ : syracuseStep 2419415 = 3629123) B3629123
theorem B846555 : Blo 846354 846555 := bstep (se 1 (by rfl) ⟨634916, by rfl⟩ : syracuseStep 846555 = 1269833) B1269833
theorem B1272569 : Blo 846354 1272569 := bstep (se 2 (by rfl) ⟨477213, by rfl⟩ : syracuseStep 1272569 = 954427) B954427
theorem B846631 : Blo 846354 846631 := bstep (se 1 (by rfl) ⟨634973, by rfl⟩ : syracuseStep 846631 = 1269947) B1269947
theorem B846671 : Blo 846354 846671 := bstep (se 1 (by rfl) ⟨635003, by rfl⟩ : syracuseStep 846671 = 1270007) B1270007
theorem B846687 : Blo 846354 846687 := bstep (se 1 (by rfl) ⟨635015, by rfl⟩ : syracuseStep 846687 = 1270031) B1270031
theorem B1272671 : Blo 846354 1272671 := bstep (se 1 (by rfl) ⟨954503, by rfl⟩ : syracuseStep 1272671 = 1909007) B1909007
theorem B2943839 : Blo 846354 2943839 := bstep (se 1 (by rfl) ⟨2207879, by rfl⟩ : syracuseStep 2943839 = 4415759) B4415759
theorem B1272683 : Blo 846354 1272683 := bstep (se 1 (by rfl) ⟨954512, by rfl⟩ : syracuseStep 1272683 = 1909025) B1909025
theorem B846715 : Blo 846354 846715 := bstep (se 1 (by rfl) ⟨635036, by rfl⟩ : syracuseStep 846715 = 1270073) B1270073
theorem B3435425 : Blo 846354 3435425 := bstep (se 2 (by rfl) ⟨1288284, by rfl⟩ : syracuseStep 3435425 = 2576569) B2576569
theorem B846767 : Blo 846354 846767 := bstep (se 1 (by rfl) ⟨635075, by rfl⟩ : syracuseStep 846767 = 1270151) B1270151
theorem B846791 : Blo 846354 846791 := bstep (se 1 (by rfl) ⟨635093, by rfl⟩ : syracuseStep 846791 = 1270187) B1270187
theorem B846811 : Blo 846354 846811 := bstep (se 1 (by rfl) ⟨635108, by rfl⟩ : syracuseStep 846811 = 1270217) B1270217
theorem B846887 : Blo 846354 846887 := bstep (se 1 (by rfl) ⟨635165, by rfl⟩ : syracuseStep 846887 = 1270331) B1270331
theorem B846927 : Blo 846354 846927 := bstep (se 1 (by rfl) ⟨635195, by rfl⟩ : syracuseStep 846927 = 1270391) B1270391
theorem B1272911 : Blo 846354 1272911 := bstep (se 1 (by rfl) ⟨954683, by rfl⟩ : syracuseStep 1272911 = 1909367) B1909367
theorem B846943 : Blo 846354 846943 := bstep (se 1 (by rfl) ⟨635207, by rfl⟩ : syracuseStep 846943 = 1270415) B1270415
theorem B846971 : Blo 846354 846971 := bstep (se 1 (by rfl) ⟨635228, by rfl⟩ : syracuseStep 846971 = 1270457) B1270457
theorem B847023 : Blo 846354 847023 := bstep (se 1 (by rfl) ⟨635267, by rfl⟩ : syracuseStep 847023 = 1270535) B1270535
theorem B847047 : Blo 846354 847047 := bstep (se 1 (by rfl) ⟨635285, by rfl⟩ : syracuseStep 847047 = 1270571) B1270571
theorem B1273031 : Blo 846354 1273031 := bstep (se 1 (by rfl) ⟨954773, by rfl⟩ : syracuseStep 1273031 = 1909547) B1909547
theorem B847067 : Blo 846354 847067 := bstep (se 1 (by rfl) ⟨635300, by rfl⟩ : syracuseStep 847067 = 1270601) B1270601
theorem B847143 : Blo 846354 847143 := bstep (se 1 (by rfl) ⟨635357, by rfl⟩ : syracuseStep 847143 = 1270715) B1270715
theorem B847183 : Blo 846354 847183 := bstep (se 1 (by rfl) ⟨635387, by rfl⟩ : syracuseStep 847183 = 1270775) B1270775
theorem B847199 : Blo 846354 847199 := bstep (se 1 (by rfl) ⟨635399, by rfl⟩ : syracuseStep 847199 = 1270799) B1270799
theorem B1207657 : Blo 846354 1207657 := bstep (se 2 (by rfl) ⟨452871, by rfl⟩ : syracuseStep 1207657 = 905743) B905743
theorem B1273193 : Blo 846354 1273193 := bstep (se 2 (by rfl) ⟨477447, by rfl⟩ : syracuseStep 1273193 = 954895) B954895
theorem B847227 : Blo 846354 847227 := bstep (se 1 (by rfl) ⟨635420, by rfl⟩ : syracuseStep 847227 = 1270841) B1270841
theorem B6188413 : Blo 846354 6188413 := bstep (se 3 (by rfl) ⟨1160327, by rfl⟩ : syracuseStep 6188413 = 2320655) B2320655
theorem B847279 : Blo 846354 847279 := bstep (se 1 (by rfl) ⟨635459, by rfl⟩ : syracuseStep 847279 = 1270919) B1270919
theorem B1273271 : Blo 846354 1273271 := bstep (se 1 (by rfl) ⟨954953, by rfl⟩ : syracuseStep 1273271 = 1909907) B1909907
theorem B847303 : Blo 846354 847303 := bstep (se 1 (by rfl) ⟨635477, by rfl⟩ : syracuseStep 847303 = 1270955) B1270955
theorem B847323 : Blo 846354 847323 := bstep (se 1 (by rfl) ⟨635492, by rfl⟩ : syracuseStep 847323 = 1270985) B1270985
theorem B1273307 : Blo 846354 1273307 := bstep (se 1 (by rfl) ⟨954980, by rfl⟩ : syracuseStep 1273307 = 1909961) B1909961
theorem B847399 : Blo 846354 847399 := bstep (se 1 (by rfl) ⟨635549, by rfl⟩ : syracuseStep 847399 = 1271099) B1271099
theorem B847439 : Blo 846354 847439 := bstep (se 1 (by rfl) ⟨635579, by rfl⟩ : syracuseStep 847439 = 1271159) B1271159
theorem B847455 : Blo 846354 847455 := bstep (se 1 (by rfl) ⟨635591, by rfl⟩ : syracuseStep 847455 = 1271183) B1271183
theorem B847483 : Blo 846354 847483 := bstep (se 1 (by rfl) ⟨635612, by rfl⟩ : syracuseStep 847483 = 1271225) B1271225
theorem B4288139 : Blo 846354 4288139 := bstep (se 1 (by rfl) ⟨3216104, by rfl⟩ : syracuseStep 4288139 = 6432209) B6432209
theorem B847535 : Blo 846354 847535 := bstep (se 1 (by rfl) ⟨635651, by rfl⟩ : syracuseStep 847535 = 1271303) B1271303
theorem B847559 : Blo 846354 847559 := bstep (se 1 (by rfl) ⟨635669, by rfl⟩ : syracuseStep 847559 = 1271339) B1271339
theorem B847579 : Blo 846354 847579 := bstep (se 1 (by rfl) ⟨635684, by rfl⟩ : syracuseStep 847579 = 1271369) B1271369
theorem B8154913 : Blo 846354 8154913 := bstep (se 2 (by rfl) ⟨3058092, by rfl⟩ : syracuseStep 8154913 = 6116185) B6116185
theorem B847655 : Blo 846354 847655 := bstep (se 1 (by rfl) ⟨635741, by rfl⟩ : syracuseStep 847655 = 1271483) B1271483
theorem B847695 : Blo 846354 847695 := bstep (se 1 (by rfl) ⟨635771, by rfl⟩ : syracuseStep 847695 = 1271543) B1271543
theorem B847711 : Blo 846354 847711 := bstep (se 1 (by rfl) ⟨635783, by rfl⟩ : syracuseStep 847711 = 1271567) B1271567
theorem B847739 : Blo 846354 847739 := bstep (se 1 (by rfl) ⟨635804, by rfl⟩ : syracuseStep 847739 = 1271609) B1271609
theorem B847791 : Blo 846354 847791 := bstep (se 1 (by rfl) ⟨635843, by rfl⟩ : syracuseStep 847791 = 1271687) B1271687
theorem B1273775 : Blo 846354 1273775 := bstep (se 1 (by rfl) ⟨955331, by rfl⟩ : syracuseStep 1273775 = 1910663) B1910663
theorem B847815 : Blo 846354 847815 := bstep (se 1 (by rfl) ⟨635861, by rfl⟩ : syracuseStep 847815 = 1271723) B1271723
theorem B847835 : Blo 846354 847835 := bstep (se 1 (by rfl) ⟨635876, by rfl⟩ : syracuseStep 847835 = 1271753) B1271753
theorem B1273865 : Blo 846354 1273865 := bstep (se 2 (by rfl) ⟨477699, by rfl⟩ : syracuseStep 1273865 = 955399) B955399
theorem B847911 : Blo 846354 847911 := bstep (se 1 (by rfl) ⟨635933, by rfl⟩ : syracuseStep 847911 = 1271867) B1271867
theorem B1273895 : Blo 846354 1273895 := bstep (se 1 (by rfl) ⟨955421, by rfl⟩ : syracuseStep 1273895 = 1910843) B1910843
theorem B847951 : Blo 846354 847951 := bstep (se 1 (by rfl) ⟨635963, by rfl⟩ : syracuseStep 847951 = 1271927) B1271927
theorem B847967 : Blo 846354 847967 := bstep (se 1 (by rfl) ⟨635975, by rfl⟩ : syracuseStep 847967 = 1271951) B1271951
theorem B847995 : Blo 846354 847995 := bstep (se 1 (by rfl) ⟨635996, by rfl⟩ : syracuseStep 847995 = 1271993) B1271993
theorem B1273979 : Blo 846354 1273979 := bstep (se 1 (by rfl) ⟨955484, by rfl⟩ : syracuseStep 1273979 = 1910969) B1910969
theorem B848047 : Blo 846354 848047 := bstep (se 1 (by rfl) ⟨636035, by rfl⟩ : syracuseStep 848047 = 1272071) B1272071
theorem B848071 : Blo 846354 848071 := bstep (se 1 (by rfl) ⟨636053, by rfl⟩ : syracuseStep 848071 = 1272107) B1272107
theorem B848091 : Blo 846354 848091 := bstep (se 1 (by rfl) ⟨636068, by rfl⟩ : syracuseStep 848091 = 1272137) B1272137
theorem B1274105 : Blo 846354 1274105 := bstep (se 2 (by rfl) ⟨477789, by rfl⟩ : syracuseStep 1274105 = 955579) B955579
theorem B848167 : Blo 846354 848167 := bstep (se 1 (by rfl) ⟨636125, by rfl⟩ : syracuseStep 848167 = 1272251) B1272251
theorem B848207 : Blo 846354 848207 := bstep (se 1 (by rfl) ⟨636155, by rfl⟩ : syracuseStep 848207 = 1272311) B1272311
theorem B979295 : Blo 846354 979295 := bstep (se 1 (by rfl) ⟨734471, by rfl⟩ : syracuseStep 979295 = 1468943) B1468943
theorem B848223 : Blo 846354 848223 := bstep (se 1 (by rfl) ⟨636167, by rfl⟩ : syracuseStep 848223 = 1272335) B1272335
theorem B1274207 : Blo 846354 1274207 := bstep (se 1 (by rfl) ⟨955655, by rfl⟩ : syracuseStep 1274207 = 1911311) B1911311
theorem B1274219 : Blo 846354 1274219 := bstep (se 1 (by rfl) ⟨955664, by rfl⟩ : syracuseStep 1274219 = 1911329) B1911329
theorem B848251 : Blo 846354 848251 := bstep (se 1 (by rfl) ⟨636188, by rfl⟩ : syracuseStep 848251 = 1272377) B1272377
theorem B848303 : Blo 846354 848303 := bstep (se 1 (by rfl) ⟨636227, by rfl⟩ : syracuseStep 848303 = 1272455) B1272455
theorem B848327 : Blo 846354 848327 := bstep (se 1 (by rfl) ⟨636245, by rfl⟩ : syracuseStep 848327 = 1272491) B1272491
theorem B848347 : Blo 846354 848347 := bstep (se 1 (by rfl) ⟨636260, by rfl⟩ : syracuseStep 848347 = 1272521) B1272521
theorem B848423 : Blo 846354 848423 := bstep (se 1 (by rfl) ⟨636317, by rfl⟩ : syracuseStep 848423 = 1272635) B1272635
theorem B848463 : Blo 846354 848463 := bstep (se 1 (by rfl) ⟨636347, by rfl⟩ : syracuseStep 848463 = 1272695) B1272695
theorem B1274447 : Blo 846354 1274447 := bstep (se 1 (by rfl) ⟨955835, by rfl⟩ : syracuseStep 1274447 = 1911671) B1911671
theorem B848479 : Blo 846354 848479 := bstep (se 1 (by rfl) ⟨636359, by rfl⟩ : syracuseStep 848479 = 1272719) B1272719
theorem B848507 : Blo 846354 848507 := bstep (se 1 (by rfl) ⟨636380, by rfl⟩ : syracuseStep 848507 = 1272761) B1272761
theorem B848559 : Blo 846354 848559 := bstep (se 1 (by rfl) ⟨636419, by rfl⟩ : syracuseStep 848559 = 1272839) B1272839
theorem B2716345 : Blo 846354 2716345 := bstep (se 2 (by rfl) ⟨1018629, by rfl⟩ : syracuseStep 2716345 = 2037259) B2037259
theorem B848583 : Blo 846354 848583 := bstep (se 1 (by rfl) ⟨636437, by rfl⟩ : syracuseStep 848583 = 1272875) B1272875
theorem B1274567 : Blo 846354 1274567 := bstep (se 1 (by rfl) ⟨955925, by rfl⟩ : syracuseStep 1274567 = 1911851) B1911851
theorem B848603 : Blo 846354 848603 := bstep (se 1 (by rfl) ⟨636452, by rfl⟩ : syracuseStep 848603 = 1272905) B1272905
theorem B2716409 : Blo 846354 2716409 := bstep (se 2 (by rfl) ⟨1018653, by rfl⟩ : syracuseStep 2716409 = 2037307) B2037307
theorem B848679 : Blo 846354 848679 := bstep (se 1 (by rfl) ⟨636509, by rfl⟩ : syracuseStep 848679 = 1273019) B1273019
theorem B848719 : Blo 846354 848719 := bstep (se 1 (by rfl) ⟨636539, by rfl⟩ : syracuseStep 848719 = 1273079) B1273079
theorem B848735 : Blo 846354 848735 := bstep (se 1 (by rfl) ⟨636551, by rfl⟩ : syracuseStep 848735 = 1273103) B1273103
theorem B1274729 : Blo 846354 1274729 := bstep (se 2 (by rfl) ⟨478023, by rfl⟩ : syracuseStep 1274729 = 956047) B956047
theorem B848763 : Blo 846354 848763 := bstep (se 1 (by rfl) ⟨636572, by rfl⟩ : syracuseStep 848763 = 1273145) B1273145
theorem B848815 : Blo 846354 848815 := bstep (se 1 (by rfl) ⟨636611, by rfl⟩ : syracuseStep 848815 = 1273223) B1273223
theorem B2749367 : Blo 846354 2749367 := bstep (se 1 (by rfl) ⟨2062025, by rfl⟩ : syracuseStep 2749367 = 4124051) B4124051
theorem B1274807 : Blo 846354 1274807 := bstep (se 1 (by rfl) ⟨956105, by rfl⟩ : syracuseStep 1274807 = 1912211) B1912211
theorem B848839 : Blo 846354 848839 := bstep (se 1 (by rfl) ⟨636629, by rfl⟩ : syracuseStep 848839 = 1273259) B1273259
theorem B848859 : Blo 846354 848859 := bstep (se 1 (by rfl) ⟨636644, by rfl⟩ : syracuseStep 848859 = 1273289) B1273289
theorem B1274843 : Blo 846354 1274843 := bstep (se 1 (by rfl) ⟨956132, by rfl⟩ : syracuseStep 1274843 = 1912265) B1912265
theorem B848935 : Blo 846354 848935 := bstep (se 1 (by rfl) ⟨636701, by rfl⟩ : syracuseStep 848935 = 1273403) B1273403
theorem B848975 : Blo 846354 848975 := bstep (se 1 (by rfl) ⟨636731, by rfl⟩ : syracuseStep 848975 = 1273463) B1273463
theorem B848991 : Blo 846354 848991 := bstep (se 1 (by rfl) ⟨636743, by rfl⟩ : syracuseStep 848991 = 1273487) B1273487
theorem B849019 : Blo 846354 849019 := bstep (se 1 (by rfl) ⟨636764, by rfl⟩ : syracuseStep 849019 = 1273529) B1273529
theorem B849071 : Blo 846354 849071 := bstep (se 1 (by rfl) ⟨636803, by rfl⟩ : syracuseStep 849071 = 1273607) B1273607
theorem B849095 : Blo 846354 849095 := bstep (se 1 (by rfl) ⟨636821, by rfl⟩ : syracuseStep 849095 = 1273643) B1273643
theorem B849115 : Blo 846354 849115 := bstep (se 1 (by rfl) ⟨636836, by rfl⟩ : syracuseStep 849115 = 1273673) B1273673
theorem B849191 : Blo 846354 849191 := bstep (se 1 (by rfl) ⟨636893, by rfl⟩ : syracuseStep 849191 = 1273787) B1273787
theorem B849231 : Blo 846354 849231 := bstep (se 1 (by rfl) ⟨636923, by rfl⟩ : syracuseStep 849231 = 1273847) B1273847
theorem B849247 : Blo 846354 849247 := bstep (se 1 (by rfl) ⟨636935, by rfl⟩ : syracuseStep 849247 = 1273871) B1273871
theorem B849275 : Blo 846354 849275 := bstep (se 1 (by rfl) ⟨636956, by rfl⟩ : syracuseStep 849275 = 1273913) B1273913
theorem B849327 : Blo 846354 849327 := bstep (se 1 (by rfl) ⟨636995, by rfl⟩ : syracuseStep 849327 = 1273991) B1273991
theorem B1275311 : Blo 846354 1275311 := bstep (se 1 (by rfl) ⟨956483, by rfl⟩ : syracuseStep 1275311 = 1912967) B1912967
theorem B849351 : Blo 846354 849351 := bstep (se 1 (by rfl) ⟨637013, by rfl⟩ : syracuseStep 849351 = 1274027) B1274027
theorem B849371 : Blo 846354 849371 := bstep (se 1 (by rfl) ⟨637028, by rfl⟩ : syracuseStep 849371 = 1274057) B1274057
theorem B1275401 : Blo 846354 1275401 := bstep (se 2 (by rfl) ⟨478275, by rfl⟩ : syracuseStep 1275401 = 956551) B956551
theorem B2061863 : Blo 846354 2061863 := bstep (se 1 (by rfl) ⟨1546397, by rfl⟩ : syracuseStep 2061863 = 3092795) B3092795
theorem B849447 : Blo 846354 849447 := bstep (se 1 (by rfl) ⟨637085, by rfl⟩ : syracuseStep 849447 = 1274171) B1274171
theorem B1275431 : Blo 846354 1275431 := bstep (se 1 (by rfl) ⟨956573, by rfl⟩ : syracuseStep 1275431 = 1913147) B1913147
theorem B849487 : Blo 846354 849487 := bstep (se 1 (by rfl) ⟨637115, by rfl⟩ : syracuseStep 849487 = 1274231) B1274231
theorem B1209935 : Blo 846354 1209935 := bstep (se 1 (by rfl) ⟨907451, by rfl⟩ : syracuseStep 1209935 = 1814903) B1814903
theorem B849503 : Blo 846354 849503 := bstep (se 1 (by rfl) ⟨637127, by rfl⟩ : syracuseStep 849503 = 1274255) B1274255
theorem B849531 : Blo 846354 849531 := bstep (se 1 (by rfl) ⟨637148, by rfl⟩ : syracuseStep 849531 = 1274297) B1274297
theorem B1275515 : Blo 846354 1275515 := bstep (se 1 (by rfl) ⟨956636, by rfl⟩ : syracuseStep 1275515 = 1913273) B1913273
theorem B3438215 : Blo 846354 3438215 := bstep (se 1 (by rfl) ⟨2578661, by rfl⟩ : syracuseStep 3438215 = 5157323) B5157323
theorem B10319507 : Blo 846354 10319507 := bstep (se 1 (by rfl) ⟨7739630, by rfl⟩ : syracuseStep 10319507 = 15479261) B15479261
theorem B849583 : Blo 846354 849583 := bstep (se 1 (by rfl) ⟨637187, by rfl⟩ : syracuseStep 849583 = 1274375) B1274375
theorem B2291399 : Blo 846354 2291399 := bstep (se 1 (by rfl) ⟨1718549, by rfl⟩ : syracuseStep 2291399 = 3437099) B3437099
theorem B849607 : Blo 846354 849607 := bstep (se 1 (by rfl) ⟨637205, by rfl⟩ : syracuseStep 849607 = 1274411) B1274411
theorem B849627 : Blo 846354 849627 := bstep (se 1 (by rfl) ⟨637220, by rfl⟩ : syracuseStep 849627 = 1274441) B1274441
theorem B849703 : Blo 846354 849703 := bstep (se 1 (by rfl) ⟨637277, by rfl⟩ : syracuseStep 849703 = 1274555) B1274555
theorem B849743 : Blo 846354 849743 := bstep (se 1 (by rfl) ⟨637307, by rfl⟩ : syracuseStep 849743 = 1274615) B1274615
theorem B849759 : Blo 846354 849759 := bstep (se 1 (by rfl) ⟨637319, by rfl⟩ : syracuseStep 849759 = 1274639) B1274639
theorem B3438443 : Blo 846354 3438443 := bstep (se 1 (by rfl) ⟨2578832, by rfl⟩ : syracuseStep 3438443 = 5157665) B5157665
theorem B849787 : Blo 846354 849787 := bstep (se 1 (by rfl) ⟨637340, by rfl⟩ : syracuseStep 849787 = 1274681) B1274681
theorem B849839 : Blo 846354 849839 := bstep (se 1 (by rfl) ⟨637379, by rfl⟩ : syracuseStep 849839 = 1274759) B1274759
theorem B849863 : Blo 846354 849863 := bstep (se 1 (by rfl) ⟨637397, by rfl⟩ : syracuseStep 849863 = 1274795) B1274795
theorem B849883 : Blo 846354 849883 := bstep (se 1 (by rfl) ⟨637412, by rfl⟩ : syracuseStep 849883 = 1274825) B1274825
theorem B849959 : Blo 846354 849959 := bstep (se 1 (by rfl) ⟨637469, by rfl⟩ : syracuseStep 849959 = 1274939) B1274939
theorem B849999 : Blo 846354 849999 := bstep (se 1 (by rfl) ⟨637499, by rfl⟩ : syracuseStep 849999 = 1274999) B1274999
theorem B850015 : Blo 846354 850015 := bstep (se 1 (by rfl) ⟨637511, by rfl⟩ : syracuseStep 850015 = 1275023) B1275023
theorem B850043 : Blo 846354 850043 := bstep (se 1 (by rfl) ⟨637532, by rfl⟩ : syracuseStep 850043 = 1275065) B1275065
theorem B850095 : Blo 846354 850095 := bstep (se 1 (by rfl) ⟨637571, by rfl⟩ : syracuseStep 850095 = 1275143) B1275143
theorem B850119 : Blo 846354 850119 := bstep (se 1 (by rfl) ⟨637589, by rfl⟩ : syracuseStep 850119 = 1275179) B1275179
theorem B850139 : Blo 846354 850139 := bstep (se 1 (by rfl) ⟨637604, by rfl⟩ : syracuseStep 850139 = 1275209) B1275209
theorem B850215 : Blo 846354 850215 := bstep (se 1 (by rfl) ⟨637661, by rfl⟩ : syracuseStep 850215 = 1275323) B1275323
theorem B850255 : Blo 846354 850255 := bstep (se 1 (by rfl) ⟨637691, by rfl⟩ : syracuseStep 850255 = 1275383) B1275383
theorem B850271 : Blo 846354 850271 := bstep (se 1 (by rfl) ⟨637703, by rfl⟩ : syracuseStep 850271 = 1275407) B1275407
theorem B850299 : Blo 846354 850299 := bstep (se 1 (by rfl) ⟨637724, by rfl⟩ : syracuseStep 850299 = 1275449) B1275449
theorem B2062721 : Blo 846354 2062721 := bstep (se 2 (by rfl) ⟨773520, by rfl⟩ : syracuseStep 2062721 = 1547041) B1547041
theorem B850351 : Blo 846354 850351 := bstep (se 1 (by rfl) ⟨637763, by rfl⟩ : syracuseStep 850351 = 1275527) B1275527
theorem B13728203 : Blo 846354 13728203 := bstep (se 1 (by rfl) ⟨10296152, by rfl⟩ : syracuseStep 13728203 = 20592305) B20592305
theorem B2718407 : Blo 846354 2718407 := bstep (se 1 (by rfl) ⟨2038805, by rfl⟩ : syracuseStep 2718407 = 4077611) B4077611
theorem B5438659 : Blo 846354 5438659 := bstep (se 1 (by rfl) ⟨4078994, by rfl⟩ : syracuseStep 5438659 = 8157989) B8157989
theorem B6454565 : Blo 846354 6454565 := bstep (se 4 (by rfl) ⟨605115, by rfl⟩ : syracuseStep 6454565 = 1210231) B1210231
theorem B11599325 : Blo 846354 11599325 := bstep (se 3 (by rfl) ⟨2174873, by rfl⟩ : syracuseStep 11599325 = 4349747) B4349747
theorem B5439275 : Blo 846354 5439275 := bstep (se 1 (by rfl) ⟨4079456, by rfl⟩ : syracuseStep 5439275 = 8158913) B8158913
theorem B11009927 : Blo 846354 11009927 := bstep (se 1 (by rfl) ⟨8257445, by rfl⟩ : syracuseStep 11009927 = 16514891) B16514891
theorem B4292513 : Blo 846354 4292513 := bstep (se 2 (by rfl) ⟨1609692, by rfl⟩ : syracuseStep 4292513 = 3219385) B3219385
theorem B9174971 : Blo 846354 9174971 := bstep (se 1 (by rfl) ⟨6881228, by rfl⟩ : syracuseStep 9174971 = 13762457) B13762457
theorem B1933523 : Blo 846354 1933523 := bstep (se 1 (by rfl) ⟨1450142, by rfl⟩ : syracuseStep 1933523 = 2900285) B2900285
theorem B6193847 : Blo 846354 6193847 := bstep (se 1 (by rfl) ⟨4645385, by rfl⟩ : syracuseStep 6193847 = 9290771) B9290771
theorem B4293323 : Blo 846354 4293323 := bstep (se 1 (by rfl) ⟨3219992, by rfl⟩ : syracuseStep 4293323 = 6439985) B6439985
theorem B6456023 : Blo 846354 6456023 := bstep (se 1 (by rfl) ⟨4842017, by rfl⟩ : syracuseStep 6456023 = 9684035) B9684035
theorem B4719455 : Blo 846354 4719455 := bstep (se 1 (by rfl) ⟨3539591, by rfl⟩ : syracuseStep 4719455 = 7079183) B7079183
theorem B4293485 : Blo 846354 4293485 := bstep (se 3 (by rfl) ⟨805028, by rfl⟩ : syracuseStep 4293485 = 1610057) B1610057
theorem B16548887 : Blo 846354 16548887 := bstep (se 1 (by rfl) ⟨12411665, by rfl⟩ : syracuseStep 16548887 = 24823331) B24823331
theorem B3671401 : Blo 846354 3671401 := bstep (se 2 (by rfl) ⟨1376775, by rfl⟩ : syracuseStep 3671401 = 2753551) B2753551
theorem B1607035 : Blo 846354 1607035 := bstep (se 1 (by rfl) ⟨1205276, by rfl⟩ : syracuseStep 1607035 = 2410553) B2410553
theorem B5440891 : Blo 846354 5440891 := bstep (se 1 (by rfl) ⟨4080668, by rfl⟩ : syracuseStep 5440891 = 8161337) B8161337
theorem B1607111 : Blo 846354 1607111 := bstep (se 1 (by rfl) ⟨1205333, by rfl⟩ : syracuseStep 1607111 = 2410667) B2410667
theorem B1934855 : Blo 846354 1934855 := bstep (se 1 (by rfl) ⟨1451141, by rfl⟩ : syracuseStep 1934855 = 2902283) B2902283
theorem B30902465 : Blo 846354 30902465 := bstep (se 2 (by rfl) ⟨11588424, by rfl⟩ : syracuseStep 30902465 = 23176849) B23176849
theorem B952699 : Blo 846354 952699 := bstep (se 1 (by rfl) ⟨714524, by rfl⟩ : syracuseStep 952699 = 1429049) B1429049
theorem B34867745 : Blo 846354 34867745 := bstep (se 2 (by rfl) ⟨13075404, by rfl⟩ : syracuseStep 34867745 = 26150809) B26150809
theorem B1608265 : Blo 846354 1608265 := bstep (se 2 (by rfl) ⟨603099, by rfl⟩ : syracuseStep 1608265 = 1206199) B1206199
theorem B953167 : Blo 846354 953167 := bstep (se 1 (by rfl) ⟨714875, by rfl⟩ : syracuseStep 953167 = 1429751) B1429751
theorem B12225451 : Blo 846354 12225451 := bstep (se 1 (by rfl) ⟨9169088, by rfl⟩ : syracuseStep 12225451 = 18338177) B18338177
theorem B3214525 : Blo 846354 3214525 := bstep (se 3 (by rfl) ⟨602723, by rfl⟩ : syracuseStep 3214525 = 1205447) B1205447
theorem B953563 : Blo 846354 953563 := bstep (se 1 (by rfl) ⟨715172, by rfl⟩ : syracuseStep 953563 = 1430345) B1430345
theorem B9178429 : Blo 846354 9178429 := bstep (se 3 (by rfl) ⟨1720955, by rfl⟩ : syracuseStep 9178429 = 3441911) B3441911
theorem B6884669 : Blo 846354 6884669 := bstep (se 3 (by rfl) ⟨1290875, by rfl⟩ : syracuseStep 6884669 = 2581751) B2581751
theorem B953851 : Blo 846354 953851 := bstep (se 1 (by rfl) ⟨715388, by rfl⟩ : syracuseStep 953851 = 1430777) B1430777
theorem B4591163 : Blo 846354 4591163 := bstep (se 1 (by rfl) ⟨3443372, by rfl⟩ : syracuseStep 4591163 = 6886745) B6886745
theorem B954031 : Blo 846354 954031 := bstep (se 1 (by rfl) ⟨715523, by rfl⟩ : syracuseStep 954031 = 1431047) B1431047
theorem B4296401 : Blo 846354 4296401 := bstep (se 2 (by rfl) ⟨1611150, by rfl⟩ : syracuseStep 4296401 = 3222301) B3222301
theorem B1904363 : Blo 846354 1904363 := bstep (se 1 (by rfl) ⟨1428272, by rfl⟩ : syracuseStep 1904363 = 2856545) B2856545
theorem B3051275 : Blo 846354 3051275 := bstep (se 1 (by rfl) ⟨2288456, by rfl⟩ : syracuseStep 3051275 = 4576913) B4576913
theorem B5443375 : Blo 846354 5443375 := bstep (se 1 (by rfl) ⟨4082531, by rfl⟩ : syracuseStep 5443375 = 8165063) B8165063
theorem B1904489 : Blo 846354 1904489 := bstep (se 2 (by rfl) ⟨714183, by rfl⟩ : syracuseStep 1904489 = 1428367) B1428367
theorem B954319 : Blo 846354 954319 := bstep (se 1 (by rfl) ⟨715739, by rfl⟩ : syracuseStep 954319 = 1431479) B1431479
theorem B7966673 : Blo 846354 7966673 := bstep (se 2 (by rfl) ⟨2987502, by rfl⟩ : syracuseStep 7966673 = 5975005) B5975005
theorem B9670913 : Blo 846354 9670913 := bstep (se 2 (by rfl) ⟨3626592, by rfl⟩ : syracuseStep 9670913 = 7253185) B7253185
theorem B6885647 : Blo 846354 6885647 := bstep (se 1 (by rfl) ⟨5164235, by rfl⟩ : syracuseStep 6885647 = 10328471) B10328471
theorem B954715 : Blo 846354 954715 := bstep (se 1 (by rfl) ⟨716036, by rfl⟩ : syracuseStep 954715 = 1432073) B1432073
theorem B954823 : Blo 846354 954823 := bstep (se 1 (by rfl) ⟨716117, by rfl⟩ : syracuseStep 954823 = 1432235) B1432235
theorem B1610209 : Blo 846354 1610209 := bstep (se 2 (by rfl) ⟨603828, by rfl⟩ : syracuseStep 1610209 = 1207657) B1207657
theorem B2036345 : Blo 846354 2036345 := bstep (se 2 (by rfl) ⟨763629, by rfl⟩ : syracuseStep 2036345 = 1527259) B1527259
theorem B1905335 : Blo 846354 1905335 := bstep (se 1 (by rfl) ⟨1429001, by rfl⟩ : syracuseStep 1905335 = 2858003) B2858003
theorem B955183 : Blo 846354 955183 := bstep (se 1 (by rfl) ⟨716387, by rfl⟩ : syracuseStep 955183 = 1432775) B1432775
theorem B4133711 : Blo 846354 4133711 := bstep (se 1 (by rfl) ⟨3100283, by rfl⟩ : syracuseStep 4133711 = 6200567) B6200567
theorem B3871567 : Blo 846354 3871567 := bstep (se 1 (by rfl) ⟨2903675, by rfl⟩ : syracuseStep 3871567 = 5807351) B5807351
theorem B1905551 : Blo 846354 1905551 := bstep (se 1 (by rfl) ⟨1429163, by rfl⟩ : syracuseStep 1905551 = 2858327) B2858327
theorem B955291 : Blo 846354 955291 := bstep (se 1 (by rfl) ⟨716468, by rfl⟩ : syracuseStep 955291 = 1432937) B1432937
theorem B9311377 : Blo 846354 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B955687 : Blo 846354 955687 := bstep (se 1 (by rfl) ⟨716765, by rfl⟩ : syracuseStep 955687 = 1433531) B1433531
theorem B955759 : Blo 846354 955759 := bstep (se 1 (by rfl) ⟨716819, by rfl⟩ : syracuseStep 955759 = 1433639) B1433639
theorem B4068731 : Blo 846354 4068731 := bstep (se 1 (by rfl) ⟨3051548, by rfl⟩ : syracuseStep 4068731 = 6103097) B6103097
theorem B1807753 : Blo 846354 1807753 := bstep (se 2 (by rfl) ⟨677907, by rfl⟩ : syracuseStep 1807753 = 1355815) B1355815
theorem B13047277 : Blo 846354 13047277 := bstep (se 3 (by rfl) ⟨2446364, by rfl⟩ : syracuseStep 13047277 = 4892729) B4892729
theorem B955975 : Blo 846354 955975 := bstep (se 1 (by rfl) ⟨716981, by rfl⟩ : syracuseStep 955975 = 1433963) B1433963
theorem B1906271 : Blo 846354 1906271 := bstep (se 1 (by rfl) ⟨1429703, by rfl⟩ : syracuseStep 1906271 = 2859407) B2859407
theorem B6887197 : Blo 846354 6887197 := bstep (se 3 (by rfl) ⟨1291349, by rfl⟩ : syracuseStep 6887197 = 2582699) B2582699
theorem B1906487 : Blo 846354 1906487 := bstep (se 1 (by rfl) ⟨1429865, by rfl⟩ : syracuseStep 1906487 = 2859731) B2859731
theorem B3217441 : Blo 846354 3217441 := bstep (se 2 (by rfl) ⟨1206540, by rfl⟩ : syracuseStep 3217441 = 2413081) B2413081
theorem B4298831 : Blo 846354 4298831 := bstep (se 1 (by rfl) ⟨3224123, by rfl⟩ : syracuseStep 4298831 = 6448247) B6448247
theorem B1906793 : Blo 846354 1906793 := bstep (se 2 (by rfl) ⟨715047, by rfl⟩ : syracuseStep 1906793 = 1430095) B1430095
theorem B6428807 : Blo 846354 6428807 := bstep (se 1 (by rfl) ⟨4821605, by rfl⟩ : syracuseStep 6428807 = 9643211) B9643211
theorem B3447037 : Blo 846354 3447037 := bstep (se 3 (by rfl) ⟨646319, by rfl⟩ : syracuseStep 3447037 = 1292639) B1292639
theorem B1612199 : Blo 846354 1612199 := bstep (se 1 (by rfl) ⟨1209149, by rfl⟩ : syracuseStep 1612199 = 2418299) B2418299
theorem B2038267 : Blo 846354 2038267 := bstep (se 1 (by rfl) ⟨1528700, by rfl⟩ : syracuseStep 2038267 = 3057401) B3057401
theorem B1907279 : Blo 846354 1907279 := bstep (se 1 (by rfl) ⟨1430459, by rfl⟩ : syracuseStep 1907279 = 2860919) B2860919
theorem B1907423 : Blo 846354 1907423 := bstep (se 1 (by rfl) ⟨1430567, by rfl⟩ : syracuseStep 1907423 = 2861135) B2861135
theorem B1907675 : Blo 846354 1907675 := bstep (se 1 (by rfl) ⟨1430756, by rfl⟩ : syracuseStep 1907675 = 2861513) B2861513
theorem B1907855 : Blo 846354 1907855 := bstep (se 1 (by rfl) ⟨1430891, by rfl⟩ : syracuseStep 1907855 = 2861783) B2861783
theorem B1612943 : Blo 846354 1612943 := bstep (se 1 (by rfl) ⟨1209707, by rfl⟩ : syracuseStep 1612943 = 2419415) B2419415
theorem B7249085 : Blo 846354 7249085 := bstep (se 3 (by rfl) ⟨1359203, by rfl⟩ : syracuseStep 7249085 = 2718407) B2718407
theorem B4299965 : Blo 846354 4299965 := bstep (se 3 (by rfl) ⟨806243, by rfl⟩ : syracuseStep 4299965 = 1612487) B1612487
theorem B1809641 : Blo 846354 1809641 := bstep (se 2 (by rfl) ⟨678615, by rfl⟩ : syracuseStep 1809641 = 1357231) B1357231
theorem B1907945 : Blo 846354 1907945 := bstep (se 2 (by rfl) ⟨715479, by rfl⟩ : syracuseStep 1907945 = 1430959) B1430959
theorem B1907999 : Blo 846354 1907999 := bstep (se 1 (by rfl) ⟨1430999, by rfl⟩ : syracuseStep 1907999 = 2861999) B2861999
theorem B2858489 : Blo 846354 2858489 := bstep (se 2 (by rfl) ⟨1071933, by rfl⟩ : syracuseStep 2858489 = 2143867) B2143867
theorem B5447249 : Blo 846354 5447249 := bstep (se 2 (by rfl) ⟨2042718, by rfl⟩ : syracuseStep 5447249 = 4085437) B4085437
theorem B2858759 : Blo 846354 2858759 := bstep (se 1 (by rfl) ⟨2144069, by rfl⟩ : syracuseStep 2858759 = 4288139) B4288139
theorem B1908521 : Blo 846354 1908521 := bstep (se 2 (by rfl) ⟨715695, by rfl⟩ : syracuseStep 1908521 = 1431391) B1431391
theorem B2858813 : Blo 846354 2858813 := bstep (se 3 (by rfl) ⟨536027, by rfl⟩ : syracuseStep 2858813 = 1072055) B1072055
theorem B1810939 : Blo 846354 1810939 := bstep (se 1 (by rfl) ⟨1358204, by rfl⟩ : syracuseStep 1810939 = 2716409) B2716409
theorem B2040383 : Blo 846354 2040383 := bstep (se 1 (by rfl) ⟨1530287, by rfl⟩ : syracuseStep 2040383 = 3060575) B3060575
theorem B1909583 : Blo 846354 1909583 := bstep (se 1 (by rfl) ⟨1432187, by rfl⟩ : syracuseStep 1909583 = 2864375) B2864375
theorem B1909799 : Blo 846354 1909799 := bstep (se 1 (by rfl) ⟨1432349, by rfl⟩ : syracuseStep 1909799 = 2864699) B2864699
theorem B1909979 : Blo 846354 1909979 := bstep (se 1 (by rfl) ⟨1432484, by rfl⟩ : syracuseStep 1909979 = 2864969) B2864969
theorem B1910177 : Blo 846354 1910177 := bstep (se 2 (by rfl) ⟨716316, by rfl⟩ : syracuseStep 1910177 = 1432633) B1432633
theorem B5514809 : Blo 846354 5514809 := bstep (se 2 (by rfl) ⟨2068053, by rfl⟩ : syracuseStep 5514809 = 4136107) B4136107
theorem B7251545 : Blo 846354 7251545 := bstep (se 2 (by rfl) ⟨2719329, by rfl⟩ : syracuseStep 7251545 = 5438659) B5438659
theorem B9152135 : Blo 846354 9152135 := bstep (se 1 (by rfl) ⟨6864101, by rfl⟩ : syracuseStep 9152135 = 13728203) B13728203
theorem B3221329 : Blo 846354 3221329 := bstep (se 2 (by rfl) ⟨1207998, by rfl⟩ : syracuseStep 3221329 = 2415997) B2415997
theorem B6432695 : Blo 846354 6432695 := bstep (se 1 (by rfl) ⟨4824521, by rfl⟩ : syracuseStep 6432695 = 9649043) B9649043
theorem B1910735 : Blo 846354 1910735 := bstep (se 1 (by rfl) ⟨1433051, by rfl⟩ : syracuseStep 1910735 = 2866103) B2866103
theorem B4302881 : Blo 846354 4302881 := bstep (se 2 (by rfl) ⟨1613580, by rfl⟩ : syracuseStep 4302881 = 3227161) B3227161
theorem B3221633 : Blo 846354 3221633 := bstep (se 2 (by rfl) ⟨1208112, by rfl⟩ : syracuseStep 3221633 = 2416225) B2416225
theorem B4303043 : Blo 846354 4303043 := bstep (se 1 (by rfl) ⟨3227282, by rfl⟩ : syracuseStep 4303043 = 6454565) B6454565
theorem B1911113 : Blo 846354 1911113 := bstep (se 2 (by rfl) ⟨716667, by rfl⟩ : syracuseStep 1911113 = 1433335) B1433335
theorem B1911131 : Blo 846354 1911131 := bstep (se 1 (by rfl) ⟨1433348, by rfl⟩ : syracuseStep 1911131 = 2866697) B2866697
theorem B3222089 : Blo 846354 3222089 := bstep (se 2 (by rfl) ⟨1208283, by rfl⟩ : syracuseStep 3222089 = 2416567) B2416567
theorem B2861675 : Blo 846354 2861675 := bstep (se 1 (by rfl) ⟨2146256, by rfl⟩ : syracuseStep 2861675 = 4292513) B4292513
theorem B1911707 : Blo 846354 1911707 := bstep (se 1 (by rfl) ⟨1433780, by rfl⟩ : syracuseStep 1911707 = 2867561) B2867561
theorem B2042795 : Blo 846354 2042795 := bstep (se 1 (by rfl) ⟨1532096, by rfl⟩ : syracuseStep 2042795 = 3064193) B3064193
theorem B4959313 : Blo 846354 4959313 := bstep (se 2 (by rfl) ⟨1859742, by rfl⟩ : syracuseStep 4959313 = 3719485) B3719485
theorem B1911905 : Blo 846354 1911905 := bstep (se 2 (by rfl) ⟨716964, by rfl⟩ : syracuseStep 1911905 = 1433929) B1433929
theorem B2042977 : Blo 846354 2042977 := bstep (se 2 (by rfl) ⟨766116, by rfl⟩ : syracuseStep 2042977 = 1532233) B1532233
theorem B2862269 : Blo 846354 2862269 := bstep (se 3 (by rfl) ⟨536675, by rfl⟩ : syracuseStep 2862269 = 1073351) B1073351
theorem B1912103 : Blo 846354 1912103 := bstep (se 1 (by rfl) ⟨1434077, by rfl⟩ : syracuseStep 1912103 = 2868155) B2868155
theorem B1814177 : Blo 846354 1814177 := bstep (se 2 (by rfl) ⟨680316, by rfl⟩ : syracuseStep 1814177 = 1360633) B1360633
theorem B1912481 : Blo 846354 1912481 := bstep (se 2 (by rfl) ⟨717180, by rfl⟩ : syracuseStep 1912481 = 1434361) B1434361
theorem B1912841 : Blo 846354 1912841 := bstep (se 2 (by rfl) ⟨717315, by rfl⟩ : syracuseStep 1912841 = 1434631) B1434631
theorem B3223577 : Blo 846354 3223577 := bstep (se 2 (by rfl) ⟨1208841, by rfl⟩ : syracuseStep 3223577 = 2417683) B2417683
theorem B2142571 : Blo 846354 2142571 := bstep (se 1 (by rfl) ⟨1606928, by rfl⟩ : syracuseStep 2142571 = 3213857) B3213857
theorem B1913255 : Blo 846354 1913255 := bstep (se 1 (by rfl) ⟨1434941, by rfl⟩ : syracuseStep 1913255 = 2869883) B2869883
theorem B3224033 : Blo 846354 3224033 := bstep (se 2 (by rfl) ⟨1209012, by rfl⟩ : syracuseStep 3224033 = 2418025) B2418025
theorem B2142895 : Blo 846354 2142895 := bstep (se 1 (by rfl) ⟨1607171, by rfl⟩ : syracuseStep 2142895 = 3214343) B3214343
theorem B2143219 : Blo 846354 2143219 := bstep (se 1 (by rfl) ⟨1607414, by rfl⟩ : syracuseStep 2143219 = 3214829) B3214829
theorem B4076689 : Blo 846354 4076689 := bstep (se 2 (by rfl) ⟨1528758, by rfl⟩ : syracuseStep 4076689 = 3057517) B3057517
theorem B8139923 : Blo 846354 8139923 := bstep (se 1 (by rfl) ⟨6104942, by rfl⟩ : syracuseStep 8139923 = 12209885) B12209885
theorem B6436097 : Blo 846354 6436097 := bstep (se 2 (by rfl) ⟨2413536, by rfl⟩ : syracuseStep 6436097 = 4827073) B4827073
theorem B119387525 : Blo 846354 119387525 := bstep (se 4 (by rfl) ⟨11192580, by rfl⟩ : syracuseStep 119387525 = 22385161) B22385161
theorem B41268689 : Blo 846354 41268689 := bstep (se 2 (by rfl) ⟨15475758, by rfl⟩ : syracuseStep 41268689 = 30951517) B30951517
theorem B2143979 : Blo 846354 2143979 := bstep (se 1 (by rfl) ⟨1607984, by rfl⟩ : syracuseStep 2143979 = 3215969) B3215969
theorem B3618665 : Blo 846354 3618665 := bstep (se 2 (by rfl) ⟨1356999, by rfl⟩ : syracuseStep 3618665 = 2713999) B2713999
theorem B2176897 : Blo 846354 2176897 := bstep (se 2 (by rfl) ⟨816336, by rfl⟩ : syracuseStep 2176897 = 1632673) B1632673
theorem B4831265 : Blo 846354 4831265 := bstep (se 2 (by rfl) ⟨1811724, by rfl⟩ : syracuseStep 4831265 = 3623449) B3623449
theorem B2865185 : Blo 846354 2865185 := bstep (se 2 (by rfl) ⟨1074444, by rfl⟩ : syracuseStep 2865185 = 2148889) B2148889
theorem B3226175 : Blo 846354 3226175 := bstep (se 1 (by rfl) ⟨2419631, by rfl⟩ : syracuseStep 3226175 = 4839263) B4839263
theorem B2144839 : Blo 846354 2144839 := bstep (se 1 (by rfl) ⟨1608629, by rfl⟩ : syracuseStep 2144839 = 3217259) B3217259
theorem B2144951 : Blo 846354 2144951 := bstep (se 1 (by rfl) ⟨1608713, by rfl⟩ : syracuseStep 2144951 = 3217427) B3217427
theorem B3226493 : Blo 846354 3226493 := bstep (se 3 (by rfl) ⟨604967, by rfl⟩ : syracuseStep 3226493 = 1209935) B1209935
theorem B125254957 : Blo 846354 125254957 := bstep (se 3 (by rfl) ⟨23485304, by rfl⟩ : syracuseStep 125254957 = 46970609) B46970609
theorem B7257559 : Blo 846354 7257559 := bstep (se 1 (by rfl) ⟨5443169, by rfl⟩ : syracuseStep 7257559 = 10886339) B10886339
theorem B9682577 : Blo 846354 9682577 := bstep (se 2 (by rfl) ⟨3630966, by rfl⟩ : syracuseStep 9682577 = 7261933) B7261933
theorem B2145953 : Blo 846354 2145953 := bstep (se 2 (by rfl) ⟨804732, by rfl⟩ : syracuseStep 2145953 = 1609465) B1609465
theorem B35307377 : Blo 846354 35307377 := bstep (se 2 (by rfl) ⟨13240266, by rfl⟩ : syracuseStep 35307377 = 26480533) B26480533
theorem B3915649 : Blo 846354 3915649 := bstep (se 2 (by rfl) ⟨1468368, by rfl⟩ : syracuseStep 3915649 = 2936737) B2936737
theorem B2146409 : Blo 846354 2146409 := bstep (se 2 (by rfl) ⟨804903, by rfl⟩ : syracuseStep 2146409 = 1609807) B1609807
theorem B3064321 : Blo 846354 3064321 := bstep (se 2 (by rfl) ⟨1149120, by rfl⟩ : syracuseStep 3064321 = 2298241) B2298241
theorem B4833863 : Blo 846354 4833863 := bstep (se 1 (by rfl) ⟨3625397, by rfl⟩ : syracuseStep 4833863 = 7250795) B7250795
theorem B2146895 : Blo 846354 2146895 := bstep (se 1 (by rfl) ⟨1610171, by rfl⟩ : syracuseStep 2146895 = 3220343) B3220343
theorem B2868047 : Blo 846354 2868047 := bstep (se 1 (by rfl) ⟨2151035, by rfl⟩ : syracuseStep 2868047 = 4302071) B4302071
theorem B3064655 : Blo 846354 3064655 := bstep (se 1 (by rfl) ⟨2298491, by rfl⟩ : syracuseStep 3064655 = 4596983) B4596983
theorem B3621793 : Blo 846354 3621793 := bstep (se 2 (by rfl) ⟨1358172, by rfl⟩ : syracuseStep 3621793 = 2716345) B2716345
theorem B2868371 : Blo 846354 2868371 := bstep (se 1 (by rfl) ⟨2151278, by rfl⟩ : syracuseStep 2868371 = 4302557) B4302557
theorem B2147543 : Blo 846354 2147543 := bstep (se 1 (by rfl) ⟨1610657, by rfl⟩ : syracuseStep 2147543 = 3221315) B3221315
theorem B2868641 : Blo 846354 2868641 := bstep (se 2 (by rfl) ⟨1075740, by rfl⟩ : syracuseStep 2868641 = 2151481) B2151481
theorem B35276309 : Blo 846354 35276309 := bstep (se 6 (by rfl) ⟨826788, by rfl⟩ : syracuseStep 35276309 = 1653577) B1653577
theorem B2147897 : Blo 846354 2147897 := bstep (se 2 (by rfl) ⟨805461, by rfl⟩ : syracuseStep 2147897 = 1610923) B1610923
theorem B6211565 : Blo 846354 6211565 := bstep (se 3 (by rfl) ⟨1164668, by rfl⟩ : syracuseStep 6211565 = 2329337) B2329337
theorem B969311 : Blo 846354 969311 := bstep (se 1 (by rfl) ⟨726983, by rfl⟩ : syracuseStep 969311 = 1453967) B1453967
theorem B7359149 : Blo 846354 7359149 := bstep (se 3 (by rfl) ⟨1379840, by rfl⟩ : syracuseStep 7359149 = 2759681) B2759681
theorem B1428455 : Blo 846354 1428455 := bstep (se 1 (by rfl) ⟨1071341, by rfl⟩ : syracuseStep 1428455 = 2142683) B2142683
theorem B8277169 : Blo 846354 8277169 := bstep (se 2 (by rfl) ⟨3103938, by rfl⟩ : syracuseStep 8277169 = 6207877) B6207877
theorem B2412193 : Blo 846354 2412193 := bstep (se 2 (by rfl) ⟨904572, by rfl⟩ : syracuseStep 2412193 = 1809145) B1809145
theorem B2150185 : Blo 846354 2150185 := bstep (se 2 (by rfl) ⟨806319, by rfl⟩ : syracuseStep 2150185 = 1612639) B1612639
theorem B10342187 : Blo 846354 10342187 := bstep (se 1 (by rfl) ⟨7756640, by rfl⟩ : syracuseStep 10342187 = 15513281) B15513281
theorem B1527599 : Blo 846354 1527599 := bstep (se 1 (by rfl) ⟨1145699, by rfl⟩ : syracuseStep 1527599 = 2291399) B2291399
theorem B15454313 : Blo 846354 15454313 := bstep (se 2 (by rfl) ⟨5795367, by rfl⟩ : syracuseStep 15454313 = 11590735) B11590735
theorem B1429609 : Blo 846354 1429609 := bstep (se 2 (by rfl) ⟨536103, by rfl⟩ : syracuseStep 1429609 = 1072207) B1072207
theorem B2150975 : Blo 846354 2150975 := bstep (se 1 (by rfl) ⟨1613231, by rfl⟩ : syracuseStep 2150975 = 3226463) B3226463
theorem B2413127 : Blo 846354 2413127 := bstep (se 1 (by rfl) ⟨1809845, by rfl⟩ : syracuseStep 2413127 = 3619691) B3619691
theorem B3626183 : Blo 846354 3626183 := bstep (se 1 (by rfl) ⟨2719637, by rfl⟩ : syracuseStep 3626183 = 5439275) B5439275
theorem B2151623 : Blo 846354 2151623 := bstep (se 1 (by rfl) ⟨1613717, by rfl⟩ : syracuseStep 2151623 = 3227435) B3227435
theorem B2151643 : Blo 846354 2151643 := bstep (se 1 (by rfl) ⟨1613732, by rfl⟩ : syracuseStep 2151643 = 3227465) B3227465
theorem B6116647 : Blo 846354 6116647 := bstep (se 1 (by rfl) ⟨4587485, by rfl⟩ : syracuseStep 6116647 = 9174971) B9174971
theorem B10868093 : Blo 846354 10868093 := bstep (se 3 (by rfl) ⟨2037767, by rfl⟩ : syracuseStep 10868093 = 4075535) B4075535
theorem B1431337 : Blo 846354 1431337 := bstep (se 2 (by rfl) ⟨536751, by rfl⟩ : syracuseStep 1431337 = 1073503) B1073503
theorem B2611453 : Blo 846354 2611453 := bstep (se 3 (by rfl) ⟨489647, by rfl⟩ : syracuseStep 2611453 = 979295) B979295
theorem B1071559 : Blo 846354 1071559 := bstep (se 1 (by rfl) ⟨803669, by rfl⟩ : syracuseStep 1071559 = 1607339) B1607339
theorem B2415167 : Blo 846354 2415167 := bstep (se 1 (by rfl) ⟨1811375, by rfl⟩ : syracuseStep 2415167 = 3622751) B3622751
theorem B1432127 : Blo 846354 1432127 := bstep (se 1 (by rfl) ⟨1074095, by rfl⟩ : syracuseStep 1432127 = 2148191) B2148191
theorem B1530431 : Blo 846354 1530431 := bstep (se 1 (by rfl) ⟨1147823, by rfl⟩ : syracuseStep 1530431 = 2295647) B2295647
theorem B8706923 : Blo 846354 8706923 := bstep (se 1 (by rfl) ⟨6530192, by rfl⟩ : syracuseStep 8706923 = 13060385) B13060385
theorem B2612443 : Blo 846354 2612443 := bstep (se 1 (by rfl) ⟨1959332, by rfl⟩ : syracuseStep 2612443 = 3918665) B3918665
theorem B1432795 : Blo 846354 1432795 := bstep (se 1 (by rfl) ⟨1074596, by rfl⟩ : syracuseStep 1432795 = 2149193) B2149193
theorem B36724103 : Blo 846354 36724103 := bstep (se 1 (by rfl) ⟨27543077, by rfl⟩ : syracuseStep 36724103 = 55086155) B55086155
theorem B1072703 : Blo 846354 1072703 := bstep (se 1 (by rfl) ⟨804527, by rfl⟩ : syracuseStep 1072703 = 1609055) B1609055
theorem B1629931 : Blo 846354 1629931 := bstep (se 1 (by rfl) ⟨1222448, by rfl⟩ : syracuseStep 1629931 = 2444897) B2444897
theorem B1269545 : Blo 846354 1269545 := bstep (se 2 (by rfl) ⟨476079, by rfl⟩ : syracuseStep 1269545 = 952159) B952159
theorem B1269551 : Blo 846354 1269551 := bstep (se 1 (by rfl) ⟨952163, by rfl⟩ : syracuseStep 1269551 = 1904327) B1904327
theorem B2580353 : Blo 846354 2580353 := bstep (se 2 (by rfl) ⟨967632, by rfl⟩ : syracuseStep 2580353 = 1935265) B1935265
theorem B1433551 : Blo 846354 1433551 := bstep (se 1 (by rfl) ⟨1075163, by rfl⟩ : syracuseStep 1433551 = 2150327) B2150327
theorem B1270025 : Blo 846354 1270025 := bstep (se 2 (by rfl) ⟨476259, by rfl⟩ : syracuseStep 1270025 = 952519) B952519
theorem B1270127 : Blo 846354 1270127 := bstep (se 1 (by rfl) ⟨952595, by rfl⟩ : syracuseStep 1270127 = 1905191) B1905191
theorem B7234049 : Blo 846354 7234049 := bstep (se 2 (by rfl) ⟨2712768, by rfl⟩ : syracuseStep 7234049 = 5425537) B5425537
theorem B6382091 : Blo 846354 6382091 := bstep (se 1 (by rfl) ⟨4786568, by rfl⟩ : syracuseStep 6382091 = 9573137) B9573137
theorem B1270343 : Blo 846354 1270343 := bstep (se 1 (by rfl) ⟨952757, by rfl⟩ : syracuseStep 1270343 = 1905515) B1905515
theorem B1270379 : Blo 846354 1270379 := bstep (se 1 (by rfl) ⟨952784, by rfl⟩ : syracuseStep 1270379 = 1905569) B1905569
theorem B2417273 : Blo 846354 2417273 := bstep (se 2 (by rfl) ⟨906477, by rfl⟩ : syracuseStep 2417273 = 1812955) B1812955
theorem B1434233 : Blo 846354 1434233 := bstep (se 2 (by rfl) ⟨537837, by rfl⟩ : syracuseStep 1434233 = 1075675) B1075675
theorem B6447761 : Blo 846354 6447761 := bstep (se 2 (by rfl) ⟨2417910, by rfl⟩ : syracuseStep 6447761 = 4835821) B4835821
theorem B6120107 : Blo 846354 6120107 := bstep (se 1 (by rfl) ⟨4590080, by rfl⟩ : syracuseStep 6120107 = 9180161) B9180161
theorem B1434287 : Blo 846354 1434287 := bstep (se 1 (by rfl) ⟨1075715, by rfl⟩ : syracuseStep 1434287 = 2151431) B2151431
theorem B1270607 : Blo 846354 1270607 := bstep (se 1 (by rfl) ⟨952955, by rfl⟩ : syracuseStep 1270607 = 1905911) B1905911
theorem B1073999 : Blo 846354 1073999 := bstep (se 1 (by rfl) ⟨805499, by rfl⟩ : syracuseStep 1073999 = 1610999) B1610999
theorem B1434523 : Blo 846354 1434523 := bstep (se 1 (by rfl) ⟨1075892, by rfl⟩ : syracuseStep 1434523 = 2151785) B2151785
theorem B4285385 : Blo 846354 4285385 := bstep (se 2 (by rfl) ⟨1607019, by rfl⟩ : syracuseStep 4285385 = 3214039) B3214039
theorem B2417627 : Blo 846354 2417627 := bstep (se 1 (by rfl) ⟨1813220, by rfl⟩ : syracuseStep 2417627 = 3626441) B3626441
theorem B1074151 : Blo 846354 1074151 := bstep (se 1 (by rfl) ⟨805613, by rfl⟩ : syracuseStep 1074151 = 1611227) B1611227
theorem B1271003 : Blo 846354 1271003 := bstep (se 1 (by rfl) ⟨953252, by rfl⟩ : syracuseStep 1271003 = 1906505) B1906505
theorem B22046053 : Blo 846354 22046053 := bstep (se 4 (by rfl) ⟨2066817, by rfl⟩ : syracuseStep 22046053 = 4133635) B4133635
theorem B1205641 : Blo 846354 1205641 := bstep (se 2 (by rfl) ⟨452115, by rfl⟩ : syracuseStep 1205641 = 904231) B904231
theorem B1271177 : Blo 846354 1271177 := bstep (se 2 (by rfl) ⟨476691, by rfl⟩ : syracuseStep 1271177 = 953383) B953383
theorem B1271531 : Blo 846354 1271531 := bstep (se 1 (by rfl) ⟨953648, by rfl⟩ : syracuseStep 1271531 = 1907297) B1907297
theorem B8251217 : Blo 846354 8251217 := bstep (se 2 (by rfl) ⟨3094206, by rfl⟩ : syracuseStep 8251217 = 6188413) B6188413
theorem B12248977 : Blo 846354 12248977 := bstep (se 2 (by rfl) ⟨4593366, by rfl⟩ : syracuseStep 12248977 = 9186733) B9186733
theorem B12412835 : Blo 846354 12412835 := bstep (se 1 (by rfl) ⟨9309626, by rfl⟩ : syracuseStep 12412835 = 18619253) B18619253
theorem B1271759 : Blo 846354 1271759 := bstep (se 1 (by rfl) ⟨953819, by rfl⟩ : syracuseStep 1271759 = 1907639) B1907639
theorem B3434761 : Blo 846354 3434761 := bstep (se 2 (by rfl) ⟨1288035, by rfl⟩ : syracuseStep 3434761 = 2576071) B2576071
theorem B9660707 : Blo 846354 9660707 := bstep (se 1 (by rfl) ⟨7245530, by rfl⟩ : syracuseStep 9660707 = 14491061) B14491061
theorem B1272155 : Blo 846354 1272155 := bstep (se 1 (by rfl) ⟨954116, by rfl⟩ : syracuseStep 1272155 = 1908233) B1908233
theorem B10873217 : Blo 846354 10873217 := bstep (se 2 (by rfl) ⟨4077456, by rfl⟩ : syracuseStep 10873217 = 8154913) B8154913
theorem B846399 : Blo 846354 846399 := bstep (se 1 (by rfl) ⟨634799, by rfl⟩ : syracuseStep 846399 = 1269599) B1269599
theorem B1272383 : Blo 846354 1272383 := bstep (se 1 (by rfl) ⟨954287, by rfl⟩ : syracuseStep 1272383 = 1908575) B1908575
theorem B846407 : Blo 846354 846407 := bstep (se 1 (by rfl) ⟨634805, by rfl⟩ : syracuseStep 846407 = 1269611) B1269611
theorem B2288207 : Blo 846354 2288207 := bstep (se 1 (by rfl) ⟨1716155, by rfl⟩ : syracuseStep 2288207 = 3432311) B3432311
theorem B1206905 : Blo 846354 1206905 := bstep (se 2 (by rfl) ⟨452589, by rfl⟩ : syracuseStep 1206905 = 905179) B905179
theorem B1272503 : Blo 846354 1272503 := bstep (se 1 (by rfl) ⟨954377, by rfl⟩ : syracuseStep 1272503 = 1908755) B1908755
theorem B6187709 : Blo 846354 6187709 := bstep (se 3 (by rfl) ⟨1160195, by rfl⟩ : syracuseStep 6187709 = 2320391) B2320391
theorem B846559 : Blo 846354 846559 := bstep (se 1 (by rfl) ⟨634919, by rfl⟩ : syracuseStep 846559 = 1269839) B1269839
theorem B846639 : Blo 846354 846639 := bstep (se 1 (by rfl) ⟨634979, by rfl⟩ : syracuseStep 846639 = 1269959) B1269959
theorem B846747 : Blo 846354 846747 := bstep (se 1 (by rfl) ⟨635060, by rfl⟩ : syracuseStep 846747 = 1270121) B1270121
theorem B1272731 : Blo 846354 1272731 := bstep (se 1 (by rfl) ⟨954548, by rfl⟩ : syracuseStep 1272731 = 1909097) B1909097
theorem B846799 : Blo 846354 846799 := bstep (se 1 (by rfl) ⟨635099, by rfl⟩ : syracuseStep 846799 = 1270199) B1270199
theorem B846823 : Blo 846354 846823 := bstep (se 1 (by rfl) ⟨635117, by rfl⟩ : syracuseStep 846823 = 1270235) B1270235
theorem B6450191 : Blo 846354 6450191 := bstep (se 1 (by rfl) ⟨4837643, by rfl⟩ : syracuseStep 6450191 = 9675287) B9675287
theorem B7236647 : Blo 846354 7236647 := bstep (se 1 (by rfl) ⟨5427485, by rfl⟩ : syracuseStep 7236647 = 10854971) B10854971
theorem B847135 : Blo 846354 847135 := bstep (se 1 (by rfl) ⟨635351, by rfl⟩ : syracuseStep 847135 = 1270703) B1270703
theorem B1273127 : Blo 846354 1273127 := bstep (se 1 (by rfl) ⟨954845, by rfl⟩ : syracuseStep 1273127 = 1909691) B1909691
theorem B847195 : Blo 846354 847195 := bstep (se 1 (by rfl) ⟨635396, by rfl⟩ : syracuseStep 847195 = 1270793) B1270793
theorem B847215 : Blo 846354 847215 := bstep (se 1 (by rfl) ⟨635411, by rfl⟩ : syracuseStep 847215 = 1270823) B1270823
theorem B1273211 : Blo 846354 1273211 := bstep (se 1 (by rfl) ⟨954908, by rfl⟩ : syracuseStep 1273211 = 1909817) B1909817
theorem B847271 : Blo 846354 847271 := bstep (se 1 (by rfl) ⟨635453, by rfl⟩ : syracuseStep 847271 = 1270907) B1270907
theorem B1273337 : Blo 846354 1273337 := bstep (se 2 (by rfl) ⟨477501, by rfl⟩ : syracuseStep 1273337 = 955003) B955003
theorem B847355 : Blo 846354 847355 := bstep (se 1 (by rfl) ⟨635516, by rfl⟩ : syracuseStep 847355 = 1271033) B1271033
theorem B847423 : Blo 846354 847423 := bstep (se 1 (by rfl) ⟨635567, by rfl⟩ : syracuseStep 847423 = 1271135) B1271135
theorem B847431 : Blo 846354 847431 := bstep (se 1 (by rfl) ⟨635573, by rfl⟩ : syracuseStep 847431 = 1271147) B1271147
theorem B1273439 : Blo 846354 1273439 := bstep (se 1 (by rfl) ⟨955079, by rfl⟩ : syracuseStep 1273439 = 1910159) B1910159
theorem B3436141 : Blo 846354 3436141 := bstep (se 3 (by rfl) ⟨644276, by rfl⟩ : syracuseStep 3436141 = 1288553) B1288553
theorem B3862225 : Blo 846354 3862225 := bstep (se 2 (by rfl) ⟨1448334, by rfl⟩ : syracuseStep 3862225 = 2896669) B2896669
theorem B847583 : Blo 846354 847583 := bstep (se 1 (by rfl) ⟨635687, by rfl⟩ : syracuseStep 847583 = 1271375) B1271375
theorem B847663 : Blo 846354 847663 := bstep (se 1 (by rfl) ⟨635747, by rfl⟩ : syracuseStep 847663 = 1271495) B1271495
theorem B1273655 : Blo 846354 1273655 := bstep (se 1 (by rfl) ⟨955241, by rfl⟩ : syracuseStep 1273655 = 1910483) B1910483
theorem B847771 : Blo 846354 847771 := bstep (se 1 (by rfl) ⟨635828, by rfl⟩ : syracuseStep 847771 = 1271657) B1271657
theorem B847823 : Blo 846354 847823 := bstep (se 1 (by rfl) ⟨635867, by rfl⟩ : syracuseStep 847823 = 1271735) B1271735
theorem B847847 : Blo 846354 847847 := bstep (se 1 (by rfl) ⟨635885, by rfl⟩ : syracuseStep 847847 = 1271771) B1271771
theorem B5795945 : Blo 846354 5795945 := bstep (se 2 (by rfl) ⟨2173479, by rfl⟩ : syracuseStep 5795945 = 4346959) B4346959
theorem B1273961 : Blo 846354 1273961 := bstep (se 2 (by rfl) ⟨477735, by rfl⟩ : syracuseStep 1273961 = 955471) B955471
theorem B23588981 : Blo 846354 23588981 := bstep (se 5 (by rfl) ⟨1105733, by rfl⟩ : syracuseStep 23588981 = 2211467) B2211467
theorem B848159 : Blo 846354 848159 := bstep (se 1 (by rfl) ⟨636119, by rfl⟩ : syracuseStep 848159 = 1272239) B1272239
theorem B848219 : Blo 846354 848219 := bstep (se 1 (by rfl) ⟨636164, by rfl⟩ : syracuseStep 848219 = 1272329) B1272329
theorem B848239 : Blo 846354 848239 := bstep (se 1 (by rfl) ⟨636179, by rfl⟩ : syracuseStep 848239 = 1272359) B1272359
theorem B848295 : Blo 846354 848295 := bstep (se 1 (by rfl) ⟨636221, by rfl⟩ : syracuseStep 848295 = 1272443) B1272443
theorem B1274279 : Blo 846354 1274279 := bstep (se 1 (by rfl) ⟨955709, by rfl⟩ : syracuseStep 1274279 = 1911419) B1911419
theorem B848379 : Blo 846354 848379 := bstep (se 1 (by rfl) ⟨636284, by rfl⟩ : syracuseStep 848379 = 1272569) B1272569
theorem B1274363 : Blo 846354 1274363 := bstep (se 1 (by rfl) ⟨955772, by rfl⟩ : syracuseStep 1274363 = 1911545) B1911545
theorem B848447 : Blo 846354 848447 := bstep (se 1 (by rfl) ⟨636335, by rfl⟩ : syracuseStep 848447 = 1272671) B1272671
theorem B1962559 : Blo 846354 1962559 := bstep (se 1 (by rfl) ⟨1471919, by rfl⟩ : syracuseStep 1962559 = 2943839) B2943839
theorem B848455 : Blo 846354 848455 := bstep (se 1 (by rfl) ⟨636341, by rfl⟩ : syracuseStep 848455 = 1272683) B1272683
theorem B2290283 : Blo 846354 2290283 := bstep (se 1 (by rfl) ⟨1717712, by rfl⟩ : syracuseStep 2290283 = 3435425) B3435425
theorem B1274489 : Blo 846354 1274489 := bstep (se 2 (by rfl) ⟨477933, by rfl⟩ : syracuseStep 1274489 = 955867) B955867
theorem B1274543 : Blo 846354 1274543 := bstep (se 1 (by rfl) ⟨955907, by rfl⟩ : syracuseStep 1274543 = 1911815) B1911815
theorem B848607 : Blo 846354 848607 := bstep (se 1 (by rfl) ⟨636455, by rfl⟩ : syracuseStep 848607 = 1272911) B1272911
theorem B1274591 : Blo 846354 1274591 := bstep (se 1 (by rfl) ⟨955943, by rfl⟩ : syracuseStep 1274591 = 1911887) B1911887
theorem B4289273 : Blo 846354 4289273 := bstep (se 2 (by rfl) ⟨1608477, by rfl⟩ : syracuseStep 4289273 = 3216955) B3216955
theorem B848687 : Blo 846354 848687 := bstep (se 1 (by rfl) ⟨636515, by rfl⟩ : syracuseStep 848687 = 1273031) B1273031
theorem B848795 : Blo 846354 848795 := bstep (se 1 (by rfl) ⟨636596, by rfl⟩ : syracuseStep 848795 = 1273193) B1273193
theorem B848847 : Blo 846354 848847 := bstep (se 1 (by rfl) ⟨636635, by rfl⟩ : syracuseStep 848847 = 1273271) B1273271
theorem B848871 : Blo 846354 848871 := bstep (se 1 (by rfl) ⟨636653, by rfl⟩ : syracuseStep 848871 = 1273307) B1273307
theorem B1274855 : Blo 846354 1274855 := bstep (se 1 (by rfl) ⟨956141, by rfl⟩ : syracuseStep 1274855 = 1912283) B1912283
theorem B1275113 : Blo 846354 1275113 := bstep (se 2 (by rfl) ⟨478167, by rfl⟩ : syracuseStep 1275113 = 956335) B956335
theorem B849183 : Blo 846354 849183 := bstep (se 1 (by rfl) ⟨636887, by rfl⟩ : syracuseStep 849183 = 1273775) B1273775
theorem B1275167 : Blo 846354 1275167 := bstep (se 1 (by rfl) ⟨956375, by rfl⟩ : syracuseStep 1275167 = 1912751) B1912751
theorem B849243 : Blo 846354 849243 := bstep (se 1 (by rfl) ⟨636932, by rfl⟩ : syracuseStep 849243 = 1273865) B1273865
theorem B849263 : Blo 846354 849263 := bstep (se 1 (by rfl) ⟨636947, by rfl⟩ : syracuseStep 849263 = 1273895) B1273895
theorem B2291105 : Blo 846354 2291105 := bstep (se 2 (by rfl) ⟨859164, by rfl⟩ : syracuseStep 2291105 = 1718329) B1718329
theorem B849319 : Blo 846354 849319 := bstep (se 1 (by rfl) ⟨636989, by rfl⟩ : syracuseStep 849319 = 1273979) B1273979
theorem B1275335 : Blo 846354 1275335 := bstep (se 1 (by rfl) ⟨956501, by rfl⟩ : syracuseStep 1275335 = 1913003) B1913003
theorem B849403 : Blo 846354 849403 := bstep (se 1 (by rfl) ⟨637052, by rfl⟩ : syracuseStep 849403 = 1274105) B1274105
theorem B849471 : Blo 846354 849471 := bstep (se 1 (by rfl) ⟨637103, by rfl⟩ : syracuseStep 849471 = 1274207) B1274207
theorem B849479 : Blo 846354 849479 := bstep (se 1 (by rfl) ⟨637109, by rfl⟩ : syracuseStep 849479 = 1274219) B1274219
theorem B849631 : Blo 846354 849631 := bstep (se 1 (by rfl) ⟨637223, by rfl⟩ : syracuseStep 849631 = 1274447) B1274447
theorem B849711 : Blo 846354 849711 := bstep (se 1 (by rfl) ⟨637283, by rfl⟩ : syracuseStep 849711 = 1274567) B1274567
theorem B849819 : Blo 846354 849819 := bstep (se 1 (by rfl) ⟨637364, by rfl⟩ : syracuseStep 849819 = 1274729) B1274729
theorem B1832911 : Blo 846354 1832911 := bstep (se 1 (by rfl) ⟨1374683, by rfl⟩ : syracuseStep 1832911 = 2749367) B2749367
theorem B849871 : Blo 846354 849871 := bstep (se 1 (by rfl) ⟨637403, by rfl⟩ : syracuseStep 849871 = 1274807) B1274807
theorem B849895 : Blo 846354 849895 := bstep (se 1 (by rfl) ⟨637421, by rfl⟩ : syracuseStep 849895 = 1274843) B1274843
theorem B1931369 : Blo 846354 1931369 := bstep (se 2 (by rfl) ⟨724263, by rfl⟩ : syracuseStep 1931369 = 1448527) B1448527
theorem B850207 : Blo 846354 850207 := bstep (se 1 (by rfl) ⟨637655, by rfl⟩ : syracuseStep 850207 = 1275311) B1275311
theorem B6453593 : Blo 846354 6453593 := bstep (se 2 (by rfl) ⟨2420097, by rfl⟩ : syracuseStep 6453593 = 4840195) B4840195
theorem B850267 : Blo 846354 850267 := bstep (se 1 (by rfl) ⟨637700, by rfl⟩ : syracuseStep 850267 = 1275401) B1275401
theorem B1374575 : Blo 846354 1374575 := bstep (se 1 (by rfl) ⟨1030931, by rfl⟩ : syracuseStep 1374575 = 2061863) B2061863
theorem B850287 : Blo 846354 850287 := bstep (se 1 (by rfl) ⟨637715, by rfl⟩ : syracuseStep 850287 = 1275431) B1275431
theorem B850343 : Blo 846354 850343 := bstep (se 1 (by rfl) ⟨637757, by rfl⟩ : syracuseStep 850343 = 1275515) B1275515
theorem B2292143 : Blo 846354 2292143 := bstep (se 1 (by rfl) ⟨1719107, by rfl⟩ : syracuseStep 2292143 = 3438215) B3438215
theorem B6879671 : Blo 846354 6879671 := bstep (se 1 (by rfl) ⟨5159753, by rfl⟩ : syracuseStep 6879671 = 10319507) B10319507
theorem B2292295 : Blo 846354 2292295 := bstep (se 1 (by rfl) ⟨1719221, by rfl⟩ : syracuseStep 2292295 = 3438443) B3438443
theorem B1375147 : Blo 846354 1375147 := bstep (se 1 (by rfl) ⟨1031360, by rfl⟩ : syracuseStep 1375147 = 2062721) B2062721
theorem B4292027 : Blo 846354 4292027 := bstep (se 1 (by rfl) ⟨3219020, by rfl⟩ : syracuseStep 4292027 = 6438041) B6438041
theorem B7732883 : Blo 846354 7732883 := bstep (se 1 (by rfl) ⟨5799662, by rfl⟩ : syracuseStep 7732883 = 11599325) B11599325
theorem B1933103 : Blo 846354 1933103 := bstep (se 1 (by rfl) ⟨1449827, by rfl⟩ : syracuseStep 1933103 = 2899655) B2899655
theorem B7339951 : Blo 846354 7339951 := bstep (se 1 (by rfl) ⟨5504963, by rfl⟩ : syracuseStep 7339951 = 11009927) B11009927
theorem B4129231 : Blo 846354 4129231 := bstep (se 1 (by rfl) ⟨3096923, by rfl⟩ : syracuseStep 4129231 = 6193847) B6193847
theorem B3146303 : Blo 846354 3146303 := bstep (se 1 (by rfl) ⟨2359727, by rfl⟩ : syracuseStep 3146303 = 4719455) B4719455
theorem B29394737 : Blo 846354 29394737 := bstep (se 2 (by rfl) ⟨11023026, by rfl⟩ : syracuseStep 29394737 = 22046053) B22046053
theorem B1607521 : Blo 846354 1607521 := bstep (se 2 (by rfl) ⟨602820, by rfl⟩ : syracuseStep 1607521 = 1205641) B1205641
theorem B952303 : Blo 846354 952303 := bstep (se 1 (by rfl) ⟨714227, by rfl⟩ : syracuseStep 952303 = 1428455) B1428455
theorem B4589779 : Blo 846354 4589779 := bstep (se 1 (by rfl) ⟨3442334, by rfl⟩ : syracuseStep 4589779 = 6884669) B6884669
theorem B4295105 : Blo 846354 4295105 := bstep (se 2 (by rfl) ⟨1610664, by rfl⟩ : syracuseStep 4295105 = 3221329) B3221329
theorem B5311115 : Blo 846354 5311115 := bstep (se 1 (by rfl) ⟨3983336, by rfl⟩ : syracuseStep 5311115 = 7966673) B7966673
theorem B4590431 : Blo 846354 4590431 := bstep (se 1 (by rfl) ⟨3442823, by rfl⟩ : syracuseStep 4590431 = 6885647) B6885647
theorem B1608751 : Blo 846354 1608751 := bstep (se 1 (by rfl) ⟨1206563, by rfl⟩ : syracuseStep 1608751 = 2413127) B2413127
theorem B7245395 : Blo 846354 7245395 := bstep (se 1 (by rfl) ⟨5434046, by rfl⟩ : syracuseStep 7245395 = 10868093) B10868093
theorem B10849949 : Blo 846354 10849949 := bstep (se 3 (by rfl) ⟨2034365, by rfl⟩ : syracuseStep 10849949 = 4068731) B4068731
theorem B1273466933 : Blo 846354 1273466933 := bstep (se 5 (by rfl) ⟨59693762, by rfl⟩ : syracuseStep 1273466933 = 119387525) B119387525
theorem B2723969 : Blo 846354 2723969 := bstep (se 2 (by rfl) ⟨1021488, by rfl⟩ : syracuseStep 2723969 = 2042977) B2042977
theorem B1610111 : Blo 846354 1610111 := bstep (se 1 (by rfl) ⟨1207583, by rfl⟩ : syracuseStep 1610111 = 2415167) B2415167
theorem B954751 : Blo 846354 954751 := bstep (se 1 (by rfl) ⟨716063, by rfl⟩ : syracuseStep 954751 = 1432127) B1432127
theorem B1020287 : Blo 846354 1020287 := bstep (se 1 (by rfl) ⟨765215, by rfl⟩ : syracuseStep 1020287 = 1530431) B1530431
theorem B20648357 : Blo 846354 20648357 := bstep (se 4 (by rfl) ⟨1935783, by rfl⟩ : syracuseStep 20648357 = 3871567) B3871567
theorem B5804615 : Blo 846354 5804615 := bstep (se 1 (by rfl) ⟨4353461, by rfl⟩ : syracuseStep 5804615 = 8706923) B8706923
theorem B3216257 : Blo 846354 3216257 := bstep (se 2 (by rfl) ⟨1206096, by rfl⟩ : syracuseStep 3216257 = 2412193) B2412193
theorem B24482735 : Blo 846354 24482735 := bstep (se 1 (by rfl) ⟨18362051, by rfl⟩ : syracuseStep 24482735 = 36724103) B36724103
theorem B1905659 : Blo 846354 1905659 := bstep (se 1 (by rfl) ⟨1429244, by rfl⟩ : syracuseStep 1905659 = 2858489) B2858489
theorem B1905839 : Blo 846354 1905839 := bstep (se 1 (by rfl) ⟨1429379, by rfl⟩ : syracuseStep 1905839 = 2858759) B2858759
theorem B1905875 : Blo 846354 1905875 := bstep (se 1 (by rfl) ⟨1429406, by rfl⟩ : syracuseStep 1905875 = 2858813) B2858813
theorem B1906145 : Blo 846354 1906145 := bstep (se 2 (by rfl) ⟨714804, by rfl⟩ : syracuseStep 1906145 = 1429609) B1429609
theorem B5150317 : Blo 846354 5150317 := bstep (se 3 (by rfl) ⟨965684, by rfl⟩ : syracuseStep 5150317 = 1931369) B1931369
theorem B4822699 : Blo 846354 4822699 := bstep (se 1 (by rfl) ⟨3617024, by rfl⟩ : syracuseStep 4822699 = 7234049) B7234049
theorem B1611515 : Blo 846354 1611515 := bstep (se 1 (by rfl) ⟨1208636, by rfl⟩ : syracuseStep 1611515 = 2417273) B2417273
theorem B956155 : Blo 846354 956155 := bstep (se 1 (by rfl) ⟨717116, by rfl⟩ : syracuseStep 956155 = 1434233) B1434233
theorem B26449669 : Blo 846354 26449669 := bstep (se 4 (by rfl) ⟨2479656, by rfl⟩ : syracuseStep 26449669 = 4959313) B4959313
theorem B4298507 : Blo 846354 4298507 := bstep (se 1 (by rfl) ⟨3223880, by rfl⟩ : syracuseStep 4298507 = 6447761) B6447761
theorem B956191 : Blo 846354 956191 := bstep (se 1 (by rfl) ⟨717143, by rfl⟩ : syracuseStep 956191 = 1434287) B1434287
theorem B2856761 : Blo 846354 2856761 := bstep (se 2 (by rfl) ⟨1071285, by rfl⟩ : syracuseStep 2856761 = 2142571) B2142571
theorem B58824629 : Blo 846354 58824629 := bstep (se 5 (by rfl) ⟨2757404, by rfl⟩ : syracuseStep 58824629 = 5514809) B5514809
theorem B2856923 : Blo 846354 2856923 := bstep (se 1 (by rfl) ⟨2142692, by rfl⟩ : syracuseStep 2856923 = 4285385) B4285385
theorem B1611751 : Blo 846354 1611751 := bstep (se 1 (by rfl) ⟨1208813, by rfl⟩ : syracuseStep 1611751 = 2417627) B2417627
theorem B2857193 : Blo 846354 2857193 := bstep (se 2 (by rfl) ⟨1071447, by rfl⟩ : syracuseStep 2857193 = 2142895) B2142895
theorem B6101423 : Blo 846354 6101423 := bstep (se 1 (by rfl) ⟨4576067, by rfl⟩ : syracuseStep 6101423 = 9152135) B9152135
theorem B2857625 : Blo 846354 2857625 := bstep (se 2 (by rfl) ⟨1071609, by rfl⟩ : syracuseStep 2857625 = 2143219) B2143219
theorem B6101885 : Blo 846354 6101885 := bstep (se 3 (by rfl) ⟨1144103, by rfl⟩ : syracuseStep 6101885 = 2288207) B2288207
theorem B7248811 : Blo 846354 7248811 := bstep (se 1 (by rfl) ⟨5436608, by rfl⟩ : syracuseStep 7248811 = 10873217) B10873217
theorem B3218413 : Blo 846354 3218413 := bstep (se 3 (by rfl) ⟨603452, by rfl⟩ : syracuseStep 3218413 = 1206905) B1206905
theorem B1907783 : Blo 846354 1907783 := bstep (se 1 (by rfl) ⟨1430837, by rfl⟩ : syracuseStep 1907783 = 2861675) B2861675
theorem B4300127 : Blo 846354 4300127 := bstep (se 1 (by rfl) ⟨3225095, by rfl⟩ : syracuseStep 4300127 = 6450191) B6450191
theorem B4824431 : Blo 846354 4824431 := bstep (se 1 (by rfl) ⟨3618323, by rfl⟩ : syracuseStep 4824431 = 7236647) B7236647
theorem B1908179 : Blo 846354 1908179 := bstep (se 1 (by rfl) ⟨1431134, by rfl⟩ : syracuseStep 1908179 = 2862269) B2862269
theorem B9182929 : Blo 846354 9182929 := bstep (se 2 (by rfl) ⟨3443598, by rfl⟩ : syracuseStep 9182929 = 6887197) B6887197
theorem B1908449 : Blo 846354 1908449 := bstep (se 2 (by rfl) ⟨715668, by rfl⟩ : syracuseStep 1908449 = 1431337) B1431337
theorem B3481937 : Blo 846354 3481937 := bstep (se 2 (by rfl) ⟨1305726, by rfl⟩ : syracuseStep 3481937 = 2611453) B2611453
theorem B4596049 : Blo 846354 4596049 := bstep (se 2 (by rfl) ⟨1723518, by rfl⟩ : syracuseStep 4596049 = 3447037) B3447037
theorem B2859515 : Blo 846354 2859515 := bstep (se 1 (by rfl) ⟨2144636, by rfl⟩ : syracuseStep 2859515 = 4289273) B4289273
theorem B2859785 : Blo 846354 2859785 := bstep (se 2 (by rfl) ⟨1072419, by rfl⟩ : syracuseStep 2859785 = 2144839) B2144839
theorem B3056393 : Blo 846354 3056393 := bstep (se 2 (by rfl) ⟨1146147, by rfl⟩ : syracuseStep 3056393 = 2292295) B2292295
theorem B3220843 : Blo 846354 3220843 := bstep (se 1 (by rfl) ⟨2415632, by rfl⟩ : syracuseStep 3220843 = 4831265) B4831265
theorem B1910123 : Blo 846354 1910123 := bstep (se 1 (by rfl) ⟨1432592, by rfl⟩ : syracuseStep 1910123 = 2865185) B2865185
theorem B2860541 : Blo 846354 2860541 := bstep (se 3 (by rfl) ⟨536351, by rfl⟩ : syracuseStep 2860541 = 1072703) B1072703
theorem B4302395 : Blo 846354 4302395 := bstep (se 1 (by rfl) ⟨3226796, by rfl⟩ : syracuseStep 4302395 = 6453593) B6453593
theorem B3483257 : Blo 846354 3483257 := bstep (se 2 (by rfl) ⟨1306221, by rfl⟩ : syracuseStep 3483257 = 2612443) B2612443
theorem B1910393 : Blo 846354 1910393 := bstep (se 2 (by rfl) ⟨716397, by rfl⟩ : syracuseStep 1910393 = 1432795) B1432795
theorem B9676745 : Blo 846354 9676745 := bstep (se 2 (by rfl) ⟨3628779, by rfl⟩ : syracuseStep 9676745 = 7257559) B7257559
theorem B8136733 : Blo 846354 8136733 := bstep (se 3 (by rfl) ⟨1525637, by rfl⟩ : syracuseStep 8136733 = 3051275) B3051275
theorem B5154941 : Blo 846354 5154941 := bstep (se 3 (by rfl) ⟨966551, by rfl⟩ : syracuseStep 5154941 = 1933103) B1933103
theorem B4073597 : Blo 846354 4073597 := bstep (se 3 (by rfl) ⟨763799, by rfl⟩ : syracuseStep 4073597 = 1527599) B1527599
theorem B2861351 : Blo 846354 2861351 := bstep (se 1 (by rfl) ⟨2146013, by rfl⟩ : syracuseStep 2861351 = 4292027) B4292027
theorem B2173241 : Blo 846354 2173241 := bstep (se 2 (by rfl) ⟨814965, by rfl⟩ : syracuseStep 2173241 = 1629931) B1629931
theorem B9775525 : Blo 846354 9775525 := bstep (se 4 (by rfl) ⟨916455, by rfl⟩ : syracuseStep 9775525 = 1832911) B1832911
theorem B5155255 : Blo 846354 5155255 := bstep (se 1 (by rfl) ⟨3866441, by rfl⟩ : syracuseStep 5155255 = 7732883) B7732883
theorem B5220865 : Blo 846354 5220865 := bstep (se 2 (by rfl) ⟨1957824, by rfl⟩ : syracuseStep 5220865 = 3915649) B3915649
theorem B23538251 : Blo 846354 23538251 := bstep (se 1 (by rfl) ⟨17653688, by rfl⟩ : syracuseStep 23538251 = 35307377) B35307377
theorem B1911401 : Blo 846354 1911401 := bstep (se 2 (by rfl) ⟨716775, by rfl⟩ : syracuseStep 1911401 = 1433551) B1433551
theorem B1289015 : Blo 846354 1289015 := bstep (se 1 (by rfl) ⟨966761, by rfl⟩ : syracuseStep 1289015 = 1933523) B1933523
theorem B3222575 : Blo 846354 3222575 := bstep (se 1 (by rfl) ⟨2416931, by rfl⟩ : syracuseStep 3222575 = 4833863) B4833863
theorem B2862215 : Blo 846354 2862215 := bstep (se 1 (by rfl) ⟨2146661, by rfl⟩ : syracuseStep 2862215 = 4293323) B4293323
theorem B4304015 : Blo 846354 4304015 := bstep (se 1 (by rfl) ⟨3228011, by rfl⟩ : syracuseStep 4304015 = 6456023) B6456023
theorem B1912031 : Blo 846354 1912031 := bstep (se 1 (by rfl) ⟨1434023, by rfl⟩ : syracuseStep 1912031 = 2868047) B2868047
theorem B2043103 : Blo 846354 2043103 := bstep (se 1 (by rfl) ⟨1532327, by rfl⟩ : syracuseStep 2043103 = 3064655) B3064655
theorem B2862323 : Blo 846354 2862323 := bstep (se 1 (by rfl) ⟨2146742, by rfl⟩ : syracuseStep 2862323 = 4293485) B4293485
theorem B1912247 : Blo 846354 1912247 := bstep (se 1 (by rfl) ⟨1434185, by rfl⟩ : syracuseStep 1912247 = 2868371) B2868371
theorem B1912427 : Blo 846354 1912427 := bstep (se 1 (by rfl) ⟨1434320, by rfl⟩ : syracuseStep 1912427 = 2868641) B2868641
theorem B1289903 : Blo 846354 1289903 := bstep (se 1 (by rfl) ⟨967427, by rfl⟩ : syracuseStep 1289903 = 1934855) B1934855
theorem B1912697 : Blo 846354 1912697 := bstep (se 2 (by rfl) ⟨717261, by rfl⟩ : syracuseStep 1912697 = 1434523) B1434523
theorem B4829057 : Blo 846354 4829057 := bstep (se 2 (by rfl) ⟨1810896, by rfl⟩ : syracuseStep 4829057 = 3621793) B3621793
theorem B4141043 : Blo 846354 4141043 := bstep (se 1 (by rfl) ⟨3105782, by rfl⟩ : syracuseStep 4141043 = 6211565) B6211565
theorem B17018909 : Blo 846354 17018909 := bstep (se 3 (by rfl) ⟨3191045, by rfl⟩ : syracuseStep 17018909 = 6382091) B6382091
theorem B23245163 : Blo 846354 23245163 := bstep (se 1 (by rfl) ⟨17433872, by rfl⟩ : syracuseStep 23245163 = 34867745) B34867745
theorem B4895201 : Blo 846354 4895201 := bstep (se 2 (by rfl) ⟨1835700, by rfl⟩ : syracuseStep 4895201 = 3671401) B3671401
theorem B2142713 : Blo 846354 2142713 := bstep (se 2 (by rfl) ⟨803517, by rfl⟩ : syracuseStep 2142713 = 1607035) B1607035
theorem B7254521 : Blo 846354 7254521 := bstep (se 2 (by rfl) ⟨2720445, by rfl⟩ : syracuseStep 7254521 = 5440891) B5440891
theorem B2863997 : Blo 846354 2863997 := bstep (se 3 (by rfl) ⟨536999, by rfl⟩ : syracuseStep 2863997 = 1073999) B1073999
theorem B11023229 : Blo 846354 11023229 := bstep (se 3 (by rfl) ⟨2066855, by rfl⟩ : syracuseStep 11023229 = 4133711) B4133711
theorem B3060775 : Blo 846354 3060775 := bstep (se 1 (by rfl) ⟨2295581, by rfl⟩ : syracuseStep 3060775 = 4591163) B4591163
theorem B2864267 : Blo 846354 2864267 := bstep (se 1 (by rfl) ⟨2148200, by rfl⟩ : syracuseStep 2864267 = 4296401) B4296401
theorem B16331969 : Blo 846354 16331969 := bstep (se 2 (by rfl) ⟨6124488, by rfl⟩ : syracuseStep 16331969 = 12248977) B12248977
theorem B6894791 : Blo 846354 6894791 := bstep (se 1 (by rfl) ⟨5171093, by rfl⟩ : syracuseStep 6894791 = 10342187) B10342187
theorem B10302875 : Blo 846354 10302875 := bstep (se 1 (by rfl) ⟨7727156, by rfl⟩ : syracuseStep 10302875 = 15454313) B15454313
theorem B10466981 : Blo 846354 10466981 := bstep (se 4 (by rfl) ⟨981279, by rfl⟩ : syracuseStep 10466981 = 1962559) B1962559
theorem B2144353 : Blo 846354 2144353 := bstep (se 2 (by rfl) ⟨804132, by rfl⟩ : syracuseStep 2144353 = 1608265) B1608265
theorem B6109613 : Blo 846354 6109613 := bstep (se 3 (by rfl) ⟨1145552, by rfl⟩ : syracuseStep 6109613 = 2291105) B2291105
theorem B16300601 : Blo 846354 16300601 := bstep (se 2 (by rfl) ⟨6112725, by rfl⟩ : syracuseStep 16300601 = 12225451) B12225451
theorem B2865887 : Blo 846354 2865887 := bstep (se 1 (by rfl) ⟨2149415, by rfl⟩ : syracuseStep 2865887 = 4298831) B4298831
theorem B12237905 : Blo 846354 12237905 := bstep (se 2 (by rfl) ⟨4589214, by rfl⟩ : syracuseStep 12237905 = 9178429) B9178429
theorem B4832723 : Blo 846354 4832723 := bstep (se 1 (by rfl) ⟨3624542, by rfl⟩ : syracuseStep 4832723 = 7249085) B7249085
theorem B2866643 : Blo 846354 2866643 := bstep (se 1 (by rfl) ⟨2149982, by rfl⟩ : syracuseStep 2866643 = 4299965) B4299965
theorem B2866913 : Blo 846354 2866913 := bstep (se 2 (by rfl) ⟨1075092, by rfl⟩ : syracuseStep 2866913 = 2150185) B2150185
theorem B7257833 : Blo 846354 7257833 := bstep (se 2 (by rfl) ⟨2721687, by rfl⟩ : syracuseStep 7257833 = 5443375) B5443375
theorem B1720235 : Blo 846354 1720235 := bstep (se 1 (by rfl) ⟨1290176, by rfl⟩ : syracuseStep 1720235 = 2580353) B2580353
theorem B1360255 : Blo 846354 1360255 := bstep (se 1 (by rfl) ⟨1020191, by rfl⟩ : syracuseStep 1360255 = 2040383) B2040383
theorem B4080071 : Blo 846354 4080071 := bstep (se 1 (by rfl) ⟨3060053, by rfl⟩ : syracuseStep 4080071 = 6120107) B6120107
theorem B2146945 : Blo 846354 2146945 := bstep (se 2 (by rfl) ⟨805104, by rfl⟩ : syracuseStep 2146945 = 1610209) B1610209
theorem B4834363 : Blo 846354 4834363 := bstep (se 1 (by rfl) ⟨3625772, by rfl⟩ : syracuseStep 4834363 = 7251545) B7251545
theorem B6112381 : Blo 846354 6112381 := bstep (se 3 (by rfl) ⟨1146071, by rfl⟩ : syracuseStep 6112381 = 2292143) B2292143
theorem B8275223 : Blo 846354 8275223 := bstep (se 1 (by rfl) ⟨6206417, by rfl⟩ : syracuseStep 8275223 = 12412835) B12412835
theorem B2868587 : Blo 846354 2868587 := bstep (se 1 (by rfl) ⟨2151440, by rfl⟩ : syracuseStep 2868587 = 4302881) B4302881
theorem B2147755 : Blo 846354 2147755 := bstep (se 1 (by rfl) ⟨1610816, by rfl⟩ : syracuseStep 2147755 = 3221633) B3221633
theorem B2868695 : Blo 846354 2868695 := bstep (se 1 (by rfl) ⟨2151521, by rfl⟩ : syracuseStep 2868695 = 4303043) B4303043
theorem B6440471 : Blo 846354 6440471 := bstep (se 1 (by rfl) ⟨4830353, by rfl⟩ : syracuseStep 6440471 = 9660707) B9660707
theorem B2868857 : Blo 846354 2868857 := bstep (se 2 (by rfl) ⟨1075821, by rfl⟩ : syracuseStep 2868857 = 2151643) B2151643
theorem B2148059 : Blo 846354 2148059 := bstep (se 1 (by rfl) ⟨1611044, by rfl⟩ : syracuseStep 2148059 = 3222089) B3222089
theorem B16500557 : Blo 846354 16500557 := bstep (se 3 (by rfl) ⟨3093854, by rfl⟩ : syracuseStep 16500557 = 6187709) B6187709
theorem B2410337 : Blo 846354 2410337 := bstep (se 2 (by rfl) ⟨903876, by rfl⟩ : syracuseStep 2410337 = 1807753) B1807753
theorem B1361863 : Blo 846354 1361863 := bstep (se 1 (by rfl) ⟨1021397, by rfl⟩ : syracuseStep 1361863 = 2042795) B2042795
theorem B2902529 : Blo 846354 2902529 := bstep (se 2 (by rfl) ⟨1088448, by rfl⟩ : syracuseStep 2902529 = 2176897) B2176897
theorem B2149051 : Blo 846354 2149051 := bstep (se 1 (by rfl) ⟨1611788, by rfl⟩ : syracuseStep 2149051 = 3223577) B3223577
theorem B2149355 : Blo 846354 2149355 := bstep (se 1 (by rfl) ⟨1612016, by rfl⟩ : syracuseStep 2149355 = 3224033) B3224033
theorem B1526855 : Blo 846354 1526855 := bstep (se 1 (by rfl) ⟨1145141, by rfl⟩ : syracuseStep 1526855 = 2290283) B2290283
theorem B1428745 : Blo 846354 1428745 := bstep (se 2 (by rfl) ⟨535779, by rfl⟩ : syracuseStep 1428745 = 1071559) B1071559
theorem B5426615 : Blo 846354 5426615 := bstep (se 1 (by rfl) ⟨4069961, by rfl⟩ : syracuseStep 5426615 = 8139923) B8139923
theorem B27512459 : Blo 846354 27512459 := bstep (se 1 (by rfl) ⟨20634344, by rfl⟩ : syracuseStep 27512459 = 41268689) B41268689
theorem B20598533 : Blo 846354 20598533 := bstep (se 4 (by rfl) ⟨1931112, by rfl⟩ : syracuseStep 20598533 = 3862225) B3862225
theorem B1429319 : Blo 846354 1429319 := bstep (se 1 (by rfl) ⟨1071989, by rfl⟩ : syracuseStep 1429319 = 2143979) B2143979
theorem B2412443 : Blo 846354 2412443 := bstep (se 1 (by rfl) ⟨1809332, by rfl⟩ : syracuseStep 2412443 = 3618665) B3618665
theorem B2150783 : Blo 846354 2150783 := bstep (se 1 (by rfl) ⟨1613087, by rfl⟩ : syracuseStep 2150783 = 3226175) B3226175
theorem B167006609 : Blo 846354 167006609 := bstep (se 2 (by rfl) ⟨62627478, by rfl⟩ : syracuseStep 167006609 = 125254957) B125254957
theorem B4837805 : Blo 846354 4837805 := bstep (se 3 (by rfl) ⟨907088, by rfl⟩ : syracuseStep 4837805 = 1814177) B1814177
theorem B1429967 : Blo 846354 1429967 := bstep (se 1 (by rfl) ⟨1072475, by rfl⟩ : syracuseStep 1429967 = 2144951) B2144951
theorem B2150995 : Blo 846354 2150995 := bstep (se 1 (by rfl) ⟨1613246, by rfl⟩ : syracuseStep 2150995 = 3226493) B3226493
theorem B1430635 : Blo 846354 1430635 := bstep (se 1 (by rfl) ⟨1072976, by rfl⟩ : syracuseStep 1430635 = 2145953) B2145953
theorem B9786601 : Blo 846354 9786601 := bstep (se 2 (by rfl) ⟨3669975, by rfl⟩ : syracuseStep 9786601 = 7339951) B7339951
theorem B1430939 : Blo 846354 1430939 := bstep (se 1 (by rfl) ⟨1073204, by rfl⟩ : syracuseStep 1430939 = 2146409) B2146409
theorem B1431263 : Blo 846354 1431263 := bstep (se 1 (by rfl) ⟨1073447, by rfl⟩ : syracuseStep 1431263 = 2146895) B2146895
theorem B2414585 : Blo 846354 2414585 := bstep (se 2 (by rfl) ⟨905469, by rfl⟩ : syracuseStep 2414585 = 1810939) B1810939
theorem B4085761 : Blo 846354 4085761 := bstep (se 2 (by rfl) ⟨1532160, by rfl⟩ : syracuseStep 4085761 = 3064321) B3064321
theorem B1431695 : Blo 846354 1431695 := bstep (se 1 (by rfl) ⟨1073771, by rfl⟩ : syracuseStep 1431695 = 2147543) B2147543
theorem B1071407 : Blo 846354 1071407 := bstep (se 1 (by rfl) ⟨803555, by rfl⟩ : syracuseStep 1071407 = 1607111) B1607111
theorem B23517539 : Blo 846354 23517539 := bstep (se 1 (by rfl) ⟨17638154, by rfl⟩ : syracuseStep 23517539 = 35276309) B35276309
theorem B1431931 : Blo 846354 1431931 := bstep (se 1 (by rfl) ⟨1073948, by rfl⟩ : syracuseStep 1431931 = 2147897) B2147897
theorem B1432201 : Blo 846354 1432201 := bstep (se 2 (by rfl) ⟨537075, by rfl⟩ : syracuseStep 1432201 = 1074151) B1074151
theorem B20601643 : Blo 846354 20601643 := bstep (se 1 (by rfl) ⟨15451232, by rfl⟩ : syracuseStep 20601643 = 30902465) B30902465
theorem B5430253 : Blo 846354 5430253 := bstep (se 3 (by rfl) ⟨1018172, by rfl⟩ : syracuseStep 5430253 = 2036345) B2036345
theorem B4906099 : Blo 846354 4906099 := bstep (se 1 (by rfl) ⟨3679574, by rfl⟩ : syracuseStep 4906099 = 7359149) B7359149
theorem B1269575 : Blo 846354 1269575 := bstep (se 1 (by rfl) ⟨952181, by rfl⟩ : syracuseStep 1269575 = 1904363) B1904363
theorem B1269659 : Blo 846354 1269659 := bstep (se 1 (by rfl) ⟨952244, by rfl⟩ : syracuseStep 1269659 = 1904489) B1904489
theorem B10870757 : Blo 846354 10870757 := bstep (se 4 (by rfl) ⟨1019133, by rfl⟩ : syracuseStep 10870757 = 2038267) B2038267
theorem B44130365 : Blo 846354 44130365 := bstep (se 3 (by rfl) ⟨8274443, by rfl⟩ : syracuseStep 44130365 = 16548887) B16548887
theorem B6447275 : Blo 846354 6447275 := bstep (se 1 (by rfl) ⟨4835456, by rfl⟩ : syracuseStep 6447275 = 9670913) B9670913
theorem B4579681 : Blo 846354 4579681 := bstep (se 2 (by rfl) ⟨1717380, by rfl⟩ : syracuseStep 4579681 = 3434761) B3434761
theorem B1433983 : Blo 846354 1433983 := bstep (se 1 (by rfl) ⟨1075487, by rfl⟩ : syracuseStep 1433983 = 2150975) B2150975
theorem B1270223 : Blo 846354 1270223 := bstep (se 1 (by rfl) ⟨952667, by rfl⟩ : syracuseStep 1270223 = 1905335) B1905335
theorem B1270265 : Blo 846354 1270265 := bstep (se 2 (by rfl) ⟨476349, by rfl⟩ : syracuseStep 1270265 = 952699) B952699
theorem B1270367 : Blo 846354 1270367 := bstep (se 1 (by rfl) ⟨952775, by rfl⟩ : syracuseStep 1270367 = 1905551) B1905551
theorem B2417455 : Blo 846354 2417455 := bstep (se 1 (by rfl) ⟨1813091, by rfl⟩ : syracuseStep 2417455 = 3626183) B3626183
theorem B1434415 : Blo 846354 1434415 := bstep (se 1 (by rfl) ⟨1075811, by rfl⟩ : syracuseStep 1434415 = 2151623) B2151623
theorem B1270847 : Blo 846354 1270847 := bstep (se 1 (by rfl) ⟨953135, by rfl⟩ : syracuseStep 1270847 = 1906271) B1906271
theorem B1270889 : Blo 846354 1270889 := bstep (se 2 (by rfl) ⟨476583, by rfl⟩ : syracuseStep 1270889 = 953167) B953167
theorem B1270991 : Blo 846354 1270991 := bstep (se 1 (by rfl) ⟨953243, by rfl⟩ : syracuseStep 1270991 = 1906487) B1906487
theorem B1271195 : Blo 846354 1271195 := bstep (se 1 (by rfl) ⟨953396, by rfl⟩ : syracuseStep 1271195 = 1906793) B1906793
theorem B4285871 : Blo 846354 4285871 := bstep (se 1 (by rfl) ⟨3214403, by rfl⟩ : syracuseStep 4285871 = 6428807) B6428807
theorem B11036225 : Blo 846354 11036225 := bstep (se 2 (by rfl) ⟨4138584, by rfl⟩ : syracuseStep 11036225 = 8277169) B8277169
theorem B4286033 : Blo 846354 4286033 := bstep (se 2 (by rfl) ⟨1607262, by rfl⟩ : syracuseStep 4286033 = 3214525) B3214525
theorem B1074799 : Blo 846354 1074799 := bstep (se 1 (by rfl) ⟨806099, by rfl⟩ : syracuseStep 1074799 = 1612199) B1612199
theorem B1271417 : Blo 846354 1271417 := bstep (se 2 (by rfl) ⟨476781, by rfl⟩ : syracuseStep 1271417 = 953563) B953563
theorem B1271519 : Blo 846354 1271519 := bstep (se 1 (by rfl) ⟨953639, by rfl⟩ : syracuseStep 1271519 = 1907279) B1907279
theorem B1271615 : Blo 846354 1271615 := bstep (se 1 (by rfl) ⟨953711, by rfl⟩ : syracuseStep 1271615 = 1907423) B1907423
theorem B1271783 : Blo 846354 1271783 := bstep (se 1 (by rfl) ⟨953837, by rfl⟩ : syracuseStep 1271783 = 1907675) B1907675
theorem B1271801 : Blo 846354 1271801 := bstep (se 2 (by rfl) ⟨476925, by rfl⟩ : syracuseStep 1271801 = 953851) B953851
theorem B1271903 : Blo 846354 1271903 := bstep (se 1 (by rfl) ⟨953927, by rfl⟩ : syracuseStep 1271903 = 1907855) B1907855
theorem B1075295 : Blo 846354 1075295 := bstep (se 1 (by rfl) ⟨806471, by rfl⟩ : syracuseStep 1075295 = 1612943) B1612943
theorem B4581521 : Blo 846354 4581521 := bstep (se 2 (by rfl) ⟨1718070, by rfl⟩ : syracuseStep 4581521 = 3436141) B3436141
theorem B1206427 : Blo 846354 1206427 := bstep (se 1 (by rfl) ⟨904820, by rfl⟩ : syracuseStep 1206427 = 1809641) B1809641
theorem B1271963 : Blo 846354 1271963 := bstep (se 1 (by rfl) ⟨953972, by rfl⟩ : syracuseStep 1271963 = 1907945) B1907945
theorem B1271999 : Blo 846354 1271999 := bstep (se 1 (by rfl) ⟨953999, by rfl⟩ : syracuseStep 1271999 = 1907999) B1907999
theorem B1272041 : Blo 846354 1272041 := bstep (se 2 (by rfl) ⟨477015, by rfl⟩ : syracuseStep 1272041 = 954031) B954031
theorem B3631499 : Blo 846354 3631499 := bstep (se 1 (by rfl) ⟨2723624, by rfl⟩ : syracuseStep 3631499 = 5447249) B5447249
theorem B846363 : Blo 846354 846363 := bstep (se 1 (by rfl) ⟨634772, by rfl⟩ : syracuseStep 846363 = 1269545) B1269545
theorem B1272347 : Blo 846354 1272347 := bstep (se 1 (by rfl) ⟨954260, by rfl⟩ : syracuseStep 1272347 = 1908521) B1908521
theorem B846367 : Blo 846354 846367 := bstep (se 1 (by rfl) ⟨634775, by rfl⟩ : syracuseStep 846367 = 1269551) B1269551
theorem B1272425 : Blo 846354 1272425 := bstep (se 2 (by rfl) ⟨477159, by rfl⟩ : syracuseStep 1272425 = 954319) B954319
theorem B846683 : Blo 846354 846683 := bstep (se 1 (by rfl) ⟨635012, by rfl⟩ : syracuseStep 846683 = 1270025) B1270025
theorem B846751 : Blo 846354 846751 := bstep (se 1 (by rfl) ⟨635063, by rfl⟩ : syracuseStep 846751 = 1270127) B1270127
theorem B846895 : Blo 846354 846895 := bstep (se 1 (by rfl) ⟨635171, by rfl⟩ : syracuseStep 846895 = 1270343) B1270343
theorem B846919 : Blo 846354 846919 := bstep (se 1 (by rfl) ⟨635189, by rfl⟩ : syracuseStep 846919 = 1270379) B1270379
theorem B1272953 : Blo 846354 1272953 := bstep (se 2 (by rfl) ⟨477357, by rfl⟩ : syracuseStep 1272953 = 954715) B954715
theorem B847071 : Blo 846354 847071 := bstep (se 1 (by rfl) ⟨635303, by rfl⟩ : syracuseStep 847071 = 1270607) B1270607
theorem B1273055 : Blo 846354 1273055 := bstep (se 1 (by rfl) ⟨954791, by rfl⟩ : syracuseStep 1273055 = 1909583) B1909583
theorem B1273097 : Blo 846354 1273097 := bstep (se 2 (by rfl) ⟨477411, by rfl⟩ : syracuseStep 1273097 = 954823) B954823
theorem B1273199 : Blo 846354 1273199 := bstep (se 1 (by rfl) ⟨954899, by rfl⟩ : syracuseStep 1273199 = 1909799) B1909799
theorem B1273319 : Blo 846354 1273319 := bstep (se 1 (by rfl) ⟨954989, by rfl⟩ : syracuseStep 1273319 = 1909979) B1909979
theorem B847335 : Blo 846354 847335 := bstep (se 1 (by rfl) ⟨635501, by rfl⟩ : syracuseStep 847335 = 1271003) B1271003
theorem B847451 : Blo 846354 847451 := bstep (se 1 (by rfl) ⟨635588, by rfl⟩ : syracuseStep 847451 = 1271177) B1271177
theorem B1273451 : Blo 846354 1273451 := bstep (se 1 (by rfl) ⟨955088, by rfl⟩ : syracuseStep 1273451 = 1910177) B1910177
theorem B3665533 : Blo 846354 3665533 := bstep (se 3 (by rfl) ⟨687287, by rfl⟩ : syracuseStep 3665533 = 1374575) B1374575
theorem B1273577 : Blo 846354 1273577 := bstep (se 2 (by rfl) ⟨477591, by rfl⟩ : syracuseStep 1273577 = 955183) B955183
theorem B847687 : Blo 846354 847687 := bstep (se 1 (by rfl) ⟨635765, by rfl⟩ : syracuseStep 847687 = 1271531) B1271531
theorem B1273721 : Blo 846354 1273721 := bstep (se 2 (by rfl) ⟨477645, by rfl⟩ : syracuseStep 1273721 = 955291) B955291
theorem B5500811 : Blo 846354 5500811 := bstep (se 1 (by rfl) ⟨4125608, by rfl⟩ : syracuseStep 5500811 = 8251217) B8251217
theorem B4288463 : Blo 846354 4288463 := bstep (se 1 (by rfl) ⟨3216347, by rfl⟩ : syracuseStep 4288463 = 6432695) B6432695
theorem B847839 : Blo 846354 847839 := bstep (se 1 (by rfl) ⟨635879, by rfl⟩ : syracuseStep 847839 = 1271759) B1271759
theorem B1273823 : Blo 846354 1273823 := bstep (se 1 (by rfl) ⟨955367, by rfl⟩ : syracuseStep 1273823 = 1910735) B1910735
theorem B5435585 : Blo 846354 5435585 := bstep (se 2 (by rfl) ⟨2038344, by rfl⟩ : syracuseStep 5435585 = 4076689) B4076689
theorem B12415169 : Blo 846354 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B1274075 : Blo 846354 1274075 := bstep (se 1 (by rfl) ⟨955556, by rfl⟩ : syracuseStep 1274075 = 1911113) B1911113
theorem B848103 : Blo 846354 848103 := bstep (se 1 (by rfl) ⟨636077, by rfl⟩ : syracuseStep 848103 = 1272155) B1272155
theorem B1274087 : Blo 846354 1274087 := bstep (se 1 (by rfl) ⟨955565, by rfl⟩ : syracuseStep 1274087 = 1911131) B1911131
theorem B2584829 : Blo 846354 2584829 := bstep (se 3 (by rfl) ⟨484655, by rfl⟩ : syracuseStep 2584829 = 969311) B969311
theorem B848255 : Blo 846354 848255 := bstep (se 1 (by rfl) ⟨636191, by rfl⟩ : syracuseStep 848255 = 1272383) B1272383
theorem B8155529 : Blo 846354 8155529 := bstep (se 2 (by rfl) ⟨3058323, by rfl⟩ : syracuseStep 8155529 = 6116647) B6116647
theorem B1274249 : Blo 846354 1274249 := bstep (se 2 (by rfl) ⟨477843, by rfl⟩ : syracuseStep 1274249 = 955687) B955687
theorem B848335 : Blo 846354 848335 := bstep (se 1 (by rfl) ⟨636251, by rfl⟩ : syracuseStep 848335 = 1272503) B1272503
theorem B1274345 : Blo 846354 1274345 := bstep (se 2 (by rfl) ⟨477879, by rfl⟩ : syracuseStep 1274345 = 955759) B955759
theorem B848487 : Blo 846354 848487 := bstep (se 1 (by rfl) ⟨636365, by rfl⟩ : syracuseStep 848487 = 1272731) B1272731
theorem B1274471 : Blo 846354 1274471 := bstep (se 1 (by rfl) ⟨955853, by rfl⟩ : syracuseStep 1274471 = 1911707) B1911707
theorem B17396369 : Blo 846354 17396369 := bstep (se 2 (by rfl) ⟨6523638, by rfl⟩ : syracuseStep 17396369 = 13047277) B13047277
theorem B1274603 : Blo 846354 1274603 := bstep (se 1 (by rfl) ⟨955952, by rfl⟩ : syracuseStep 1274603 = 1911905) B1911905
theorem B1274633 : Blo 846354 1274633 := bstep (se 2 (by rfl) ⟨477987, by rfl⟩ : syracuseStep 1274633 = 955975) B955975
theorem B848751 : Blo 846354 848751 := bstep (se 1 (by rfl) ⟨636563, by rfl⟩ : syracuseStep 848751 = 1273127) B1273127
theorem B1274735 : Blo 846354 1274735 := bstep (se 1 (by rfl) ⟨956051, by rfl⟩ : syracuseStep 1274735 = 1912103) B1912103
theorem B848807 : Blo 846354 848807 := bstep (se 1 (by rfl) ⟨636605, by rfl⟩ : syracuseStep 848807 = 1273211) B1273211
theorem B848891 : Blo 846354 848891 := bstep (se 1 (by rfl) ⟨636668, by rfl⟩ : syracuseStep 848891 = 1273337) B1273337
theorem B848959 : Blo 846354 848959 := bstep (se 1 (by rfl) ⟨636719, by rfl⟩ : syracuseStep 848959 = 1273439) B1273439
theorem B1274987 : Blo 846354 1274987 := bstep (se 1 (by rfl) ⟨956240, by rfl⟩ : syracuseStep 1274987 = 1912481) B1912481
theorem B849103 : Blo 846354 849103 := bstep (se 1 (by rfl) ⟨636827, by rfl⟩ : syracuseStep 849103 = 1273655) B1273655
theorem B1275227 : Blo 846354 1275227 := bstep (se 1 (by rfl) ⟨956420, by rfl⟩ : syracuseStep 1275227 = 1912841) B1912841
theorem B4289921 : Blo 846354 4289921 := bstep (se 2 (by rfl) ⟨1608720, by rfl⟩ : syracuseStep 4289921 = 3217441) B3217441
theorem B3863963 : Blo 846354 3863963 := bstep (se 1 (by rfl) ⟨2897972, by rfl⟩ : syracuseStep 3863963 = 5795945) B5795945
theorem B849307 : Blo 846354 849307 := bstep (se 1 (by rfl) ⟨636980, by rfl⟩ : syracuseStep 849307 = 1273961) B1273961
theorem B15725987 : Blo 846354 15725987 := bstep (se 1 (by rfl) ⟨11794490, by rfl⟩ : syracuseStep 15725987 = 23588981) B23588981
theorem B849519 : Blo 846354 849519 := bstep (se 1 (by rfl) ⟨637139, by rfl⟩ : syracuseStep 849519 = 1274279) B1274279
theorem B1275503 : Blo 846354 1275503 := bstep (se 1 (by rfl) ⟨956627, by rfl⟩ : syracuseStep 1275503 = 1913255) B1913255
theorem B849575 : Blo 846354 849575 := bstep (se 1 (by rfl) ⟨637181, by rfl⟩ : syracuseStep 849575 = 1274363) B1274363
theorem B849659 : Blo 846354 849659 := bstep (se 1 (by rfl) ⟨637244, by rfl⟩ : syracuseStep 849659 = 1274489) B1274489
theorem B849695 : Blo 846354 849695 := bstep (se 1 (by rfl) ⟨637271, by rfl⟩ : syracuseStep 849695 = 1274543) B1274543
theorem B849727 : Blo 846354 849727 := bstep (se 1 (by rfl) ⟨637295, by rfl⟩ : syracuseStep 849727 = 1274591) B1274591
theorem B849903 : Blo 846354 849903 := bstep (se 1 (by rfl) ⟨637427, by rfl⟩ : syracuseStep 849903 = 1274855) B1274855
theorem B850075 : Blo 846354 850075 := bstep (se 1 (by rfl) ⟨637556, by rfl⟩ : syracuseStep 850075 = 1275113) B1275113
theorem B4290731 : Blo 846354 4290731 := bstep (se 1 (by rfl) ⟨3218048, by rfl⟩ : syracuseStep 4290731 = 6436097) B6436097
theorem B850111 : Blo 846354 850111 := bstep (se 1 (by rfl) ⟨637583, by rfl⟩ : syracuseStep 850111 = 1275167) B1275167
theorem B850223 : Blo 846354 850223 := bstep (se 1 (by rfl) ⟨637667, by rfl⟩ : syracuseStep 850223 = 1275335) B1275335
theorem B1833529 : Blo 846354 1833529 := bstep (se 2 (by rfl) ⟨687573, by rfl⟩ : syracuseStep 1833529 = 1375147) B1375147
theorem B4586447 : Blo 846354 4586447 := bstep (se 1 (by rfl) ⟨3439835, by rfl⟩ : syracuseStep 4586447 = 6879671) B6879671
theorem B6455051 : Blo 846354 6455051 := bstep (se 1 (by rfl) ⟨4841288, by rfl⟩ : syracuseStep 6455051 = 9682577) B9682577
theorem B2097535 : Blo 846354 2097535 := bstep (se 1 (by rfl) ⟨1573151, by rfl⟩ : syracuseStep 2097535 = 3146303) B3146303
theorem B6128065 : Blo 846354 6128065 := bstep (se 2 (by rfl) ⟨2298024, by rfl⟩ : syracuseStep 6128065 = 4596049) B4596049
theorem B5505641 : Blo 846354 5505641 := bstep (se 2 (by rfl) ⟨2064615, by rfl⟩ : syracuseStep 5505641 = 4129231) B4129231
theorem B16286453 : Blo 846354 16286453 := bstep (se 5 (by rfl) ⟨763427, by rfl⟩ : syracuseStep 16286453 = 1526855) B1526855
theorem B2720765 : Blo 846354 2720765 := bstep (se 3 (by rfl) ⟨510143, by rfl⟩ : syracuseStep 2720765 = 1020287) B1020287
theorem B4293647 : Blo 846354 4293647 := bstep (se 1 (by rfl) ⟨3220235, by rfl⟩ : syracuseStep 4293647 = 6440471) B6440471
theorem B10880189 : Blo 846354 10880189 := bstep (se 3 (by rfl) ⟨2040035, by rfl⟩ : syracuseStep 10880189 = 4080071) B4080071
theorem B19596491 : Blo 846354 19596491 := bstep (se 1 (by rfl) ⟨14697368, by rfl⟩ : syracuseStep 19596491 = 29394737) B29394737
theorem B1606891 : Blo 846354 1606891 := bstep (se 1 (by rfl) ⟨1205168, by rfl⟩ : syracuseStep 1606891 = 2410337) B2410337
theorem B1935019 : Blo 846354 1935019 := bstep (se 1 (by rfl) ⟨1451264, by rfl⟩ : syracuseStep 1935019 = 2902529) B2902529
theorem B3540743 : Blo 846354 3540743 := bstep (se 1 (by rfl) ⟨2655557, by rfl⟩ : syracuseStep 3540743 = 5311115) B5311115
theorem B4294457 : Blo 846354 4294457 := bstep (se 2 (by rfl) ⟨1610421, by rfl⟩ : syracuseStep 4294457 = 3220843) B3220843
theorem B13732355 : Blo 846354 13732355 := bstep (se 1 (by rfl) ⟨10299266, by rfl⟩ : syracuseStep 13732355 = 20598533) B20598533
theorem B952879 : Blo 846354 952879 := bstep (se 1 (by rfl) ⟨714659, by rfl⟩ : syracuseStep 952879 = 1429319) B1429319
theorem B10848977 : Blo 846354 10848977 := bstep (se 2 (by rfl) ⟨4068366, by rfl⟩ : syracuseStep 10848977 = 8136733) B8136733
theorem B1608569 : Blo 846354 1608569 := bstep (se 2 (by rfl) ⟨603213, by rfl⟩ : syracuseStep 1608569 = 1206427) B1206427
theorem B13765571 : Blo 846354 13765571 := bstep (se 1 (by rfl) ⟨10324178, by rfl⟩ : syracuseStep 13765571 = 20648357) B20648357
theorem B953311 : Blo 846354 953311 := bstep (se 1 (by rfl) ⟨714983, by rfl⟩ : syracuseStep 953311 = 1429967) B1429967
theorem B3869743 : Blo 846354 3869743 := bstep (se 1 (by rfl) ⟨2902307, by rfl⟩ : syracuseStep 3869743 = 5804615) B5804615
theorem B16321823 : Blo 846354 16321823 := bstep (se 1 (by rfl) ⟨12241367, by rfl⟩ : syracuseStep 16321823 = 24482735) B24482735
theorem B953959 : Blo 846354 953959 := bstep (se 1 (by rfl) ⟨715469, by rfl⟩ : syracuseStep 953959 = 1430939) B1430939
theorem B954175 : Blo 846354 954175 := bstep (se 1 (by rfl) ⟨715631, by rfl⟩ : syracuseStep 954175 = 1431263) B1431263
theorem B1904507 : Blo 846354 1904507 := bstep (se 1 (by rfl) ⟨1428380, by rfl⟩ : syracuseStep 1904507 = 2856761) B2856761
theorem B1904615 : Blo 846354 1904615 := bstep (se 1 (by rfl) ⟨1428461, by rfl⟩ : syracuseStep 1904615 = 2856923) B2856923
theorem B1609723 : Blo 846354 1609723 := bstep (se 1 (by rfl) ⟨1207292, by rfl⟩ : syracuseStep 1609723 = 2414585) B2414585
theorem B954463 : Blo 846354 954463 := bstep (se 1 (by rfl) ⟨715847, by rfl⟩ : syracuseStep 954463 = 1431695) B1431695
theorem B1904795 : Blo 846354 1904795 := bstep (se 1 (by rfl) ⟨1428596, by rfl⟩ : syracuseStep 1904795 = 2857193) B2857193
theorem B4067615 : Blo 846354 4067615 := bstep (se 1 (by rfl) ⟨3050711, by rfl⟩ : syracuseStep 4067615 = 6101423) B6101423
theorem B2724137 : Blo 846354 2724137 := bstep (se 2 (by rfl) ⟨1021551, by rfl⟩ : syracuseStep 2724137 = 2043103) B2043103
theorem B1904993 : Blo 846354 1904993 := bstep (se 2 (by rfl) ⟨714372, by rfl⟩ : syracuseStep 1904993 = 1428745) B1428745
theorem B1905083 : Blo 846354 1905083 := bstep (se 1 (by rfl) ⟨1428812, by rfl⟩ : syracuseStep 1905083 = 2857625) B2857625
theorem B4067923 : Blo 846354 4067923 := bstep (se 1 (by rfl) ⟨3050942, by rfl⟩ : syracuseStep 4067923 = 6101885) B6101885
theorem B4297373 : Blo 846354 4297373 := bstep (se 3 (by rfl) ⟨805757, by rfl⟩ : syracuseStep 4297373 = 1611515) B1611515
theorem B4887377 : Blo 846354 4887377 := bstep (se 2 (by rfl) ⟨1832766, by rfl⟩ : syracuseStep 4887377 = 3665533) B3665533
theorem B3216287 : Blo 846354 3216287 := bstep (se 1 (by rfl) ⟨2412215, by rfl⟩ : syracuseStep 3216287 = 4824431) B4824431
theorem B7247171 : Blo 846354 7247171 := bstep (se 1 (by rfl) ⟨5435378, by rfl⟩ : syracuseStep 7247171 = 10870757) B10870757
theorem B4298183 : Blo 846354 4298183 := bstep (se 1 (by rfl) ⟨3223637, by rfl⟩ : syracuseStep 4298183 = 6447275) B6447275
theorem B1906343 : Blo 846354 1906343 := bstep (se 1 (by rfl) ⟨1429757, by rfl⟩ : syracuseStep 1906343 = 2859515) B2859515
theorem B1906523 : Blo 846354 1906523 := bstep (se 1 (by rfl) ⟨1429892, by rfl⟩ : syracuseStep 1906523 = 2859785) B2859785
theorem B2857085 : Blo 846354 2857085 := bstep (se 3 (by rfl) ⟨535703, by rfl⟩ : syracuseStep 2857085 = 1071407) B1071407
theorem B2857247 : Blo 846354 2857247 := bstep (se 1 (by rfl) ⟨2142935, by rfl⟩ : syracuseStep 2857247 = 4285871) B4285871
theorem B1907027 : Blo 846354 1907027 := bstep (se 1 (by rfl) ⟨1430270, by rfl⟩ : syracuseStep 1907027 = 2860541) B2860541
theorem B2857355 : Blo 846354 2857355 := bstep (se 1 (by rfl) ⟨2143016, by rfl⟩ : syracuseStep 2857355 = 4286033) B4286033
theorem B3054347 : Blo 846354 3054347 := bstep (se 1 (by rfl) ⟨2290760, by rfl⟩ : syracuseStep 3054347 = 4581521) B4581521
theorem B1907513 : Blo 846354 1907513 := bstep (se 2 (by rfl) ⟨715317, by rfl⟩ : syracuseStep 1907513 = 1430635) B1430635
theorem B1907567 : Blo 846354 1907567 := bstep (se 1 (by rfl) ⟨1430675, by rfl⟩ : syracuseStep 1907567 = 2861351) B2861351
theorem B859343 : Blo 846354 859343 := bstep (se 1 (by rfl) ⟨644507, by rfl⟩ : syracuseStep 859343 = 1289015) B1289015
theorem B1908143 : Blo 846354 1908143 := bstep (se 1 (by rfl) ⟨1431107, by rfl⟩ : syracuseStep 1908143 = 2862215) B2862215
theorem B1908215 : Blo 846354 1908215 := bstep (se 1 (by rfl) ⟨1431161, by rfl⟩ : syracuseStep 1908215 = 2862323) B2862323
theorem B6430265 : Blo 846354 6430265 := bstep (se 2 (by rfl) ⟨2411349, by rfl⟩ : syracuseStep 6430265 = 4822699) B4822699
theorem B35266225 : Blo 846354 35266225 := bstep (se 2 (by rfl) ⟨13224834, by rfl⟩ : syracuseStep 35266225 = 26449669) B26449669
theorem B3219371 : Blo 846354 3219371 := bstep (se 1 (by rfl) ⟨2414528, by rfl⟩ : syracuseStep 3219371 = 4829057) B4829057
theorem B2858975 : Blo 846354 2858975 := bstep (se 1 (by rfl) ⟨2144231, by rfl⟩ : syracuseStep 2858975 = 4288463) B4288463
theorem B2760695 : Blo 846354 2760695 := bstep (se 1 (by rfl) ⟨2070521, by rfl⟩ : syracuseStep 2760695 = 4141043) B4141043
theorem B5447681 : Blo 846354 5447681 := bstep (se 2 (by rfl) ⟨2042880, by rfl⟩ : syracuseStep 5447681 = 4085761) B4085761
theorem B11345939 : Blo 846354 11345939 := bstep (se 1 (by rfl) ⟨8509454, by rfl⟩ : syracuseStep 11345939 = 17018909) B17018909
theorem B2859137 : Blo 846354 2859137 := bstep (se 2 (by rfl) ⟨1072176, by rfl⟩ : syracuseStep 2859137 = 2144353) B2144353
theorem B1909241 : Blo 846354 1909241 := bstep (se 2 (by rfl) ⟨715965, by rfl⟩ : syracuseStep 1909241 = 1431931) B1431931
theorem B1909331 : Blo 846354 1909331 := bstep (se 1 (by rfl) ⟨1431998, by rfl⟩ : syracuseStep 1909331 = 2863997) B2863997
theorem B7348819 : Blo 846354 7348819 := bstep (se 1 (by rfl) ⟨5511614, by rfl⟩ : syracuseStep 7348819 = 11023229) B11023229
theorem B1909511 : Blo 846354 1909511 := bstep (se 1 (by rfl) ⟨1432133, by rfl⟩ : syracuseStep 1909511 = 2864267) B2864267
theorem B10887979 : Blo 846354 10887979 := bstep (se 1 (by rfl) ⟨8165984, by rfl⟩ : syracuseStep 10887979 = 16331969) B16331969
theorem B4596527 : Blo 846354 4596527 := bstep (se 1 (by rfl) ⟨3447395, by rfl⟩ : syracuseStep 4596527 = 6894791) B6894791
theorem B1909601 : Blo 846354 1909601 := bstep (se 2 (by rfl) ⟨716100, by rfl⟩ : syracuseStep 1909601 = 1432201) B1432201
theorem B2859947 : Blo 846354 2859947 := bstep (se 1 (by rfl) ⟨2144960, by rfl⟩ : syracuseStep 2859947 = 4289921) B4289921
theorem B27468857 : Blo 846354 27468857 := bstep (se 2 (by rfl) ⟨10300821, by rfl⟩ : syracuseStep 27468857 = 20601643) B20601643
theorem B2860487 : Blo 846354 2860487 := bstep (se 1 (by rfl) ⟨2145365, by rfl⟩ : syracuseStep 2860487 = 4290731) B4290731
theorem B4073075 : Blo 846354 4073075 := bstep (se 1 (by rfl) ⟨3054806, by rfl⟩ : syracuseStep 4073075 = 6109613) B6109613
theorem B1910591 : Blo 846354 1910591 := bstep (se 1 (by rfl) ⟨1432943, by rfl⟩ : syracuseStep 1910591 = 2865887) B2865887
theorem B3057631 : Blo 846354 3057631 := bstep (se 1 (by rfl) ⟨2293223, by rfl⟩ : syracuseStep 3057631 = 4586447) B4586447
theorem B3221815 : Blo 846354 3221815 := bstep (se 1 (by rfl) ⟨2416361, by rfl⟩ : syracuseStep 3221815 = 4832723) B4832723
theorem B1911095 : Blo 846354 1911095 := bstep (se 1 (by rfl) ⟨1433321, by rfl⟩ : syracuseStep 1911095 = 2866643) B2866643
theorem B6433181 : Blo 846354 6433181 := bstep (se 3 (by rfl) ⟨1206221, by rfl⟩ : syracuseStep 6433181 = 2412443) B2412443
theorem B1911275 : Blo 846354 1911275 := bstep (se 1 (by rfl) ⟨1433456, by rfl⟩ : syracuseStep 1911275 = 2866913) B2866913
theorem B4303367 : Blo 846354 4303367 := bstep (se 1 (by rfl) ⟨3227525, by rfl⟩ : syracuseStep 4303367 = 6455051) B6455051
theorem B6106241 : Blo 846354 6106241 := bstep (se 2 (by rfl) ⟨2289840, by rfl⟩ : syracuseStep 6106241 = 4579681) B4579681
theorem B1813673 : Blo 846354 1813673 := bstep (se 2 (by rfl) ⟨680127, by rfl⟩ : syracuseStep 1813673 = 1360255) B1360255
theorem B1911977 : Blo 846354 1911977 := bstep (se 2 (by rfl) ⟨716991, by rfl⟩ : syracuseStep 1911977 = 1433983) B1433983
theorem B6892877 : Blo 846354 6892877 := bstep (se 3 (by rfl) ⟨1292414, by rfl⟩ : syracuseStep 6892877 = 2584829) B2584829
theorem B2862593 : Blo 846354 2862593 := bstep (se 2 (by rfl) ⟨1073472, by rfl⟩ : syracuseStep 2862593 = 2146945) B2146945
theorem B5516815 : Blo 846354 5516815 := bstep (se 1 (by rfl) ⟨4137611, by rfl⟩ : syracuseStep 5516815 = 8275223) B8275223
theorem B1912391 : Blo 846354 1912391 := bstep (se 1 (by rfl) ⟨1434293, by rfl⟩ : syracuseStep 1912391 = 2868587) B2868587
theorem B1912463 : Blo 846354 1912463 := bstep (se 1 (by rfl) ⟨1434347, by rfl⟩ : syracuseStep 1912463 = 2868695) B2868695
theorem B3223273 : Blo 846354 3223273 := bstep (se 2 (by rfl) ⟨1208727, by rfl⟩ : syracuseStep 3223273 = 2417455) B2417455
theorem B1912553 : Blo 846354 1912553 := bstep (se 2 (by rfl) ⟨717207, by rfl⟩ : syracuseStep 1912553 = 1434415) B1434415
theorem B1912571 : Blo 846354 1912571 := bstep (se 1 (by rfl) ⟨1434428, by rfl⟩ : syracuseStep 1912571 = 2868857) B2868857
theorem B13053869 : Blo 846354 13053869 := bstep (se 3 (by rfl) ⟨2447600, by rfl⟩ : syracuseStep 13053869 = 4895201) B4895201
theorem B2863403 : Blo 846354 2863403 := bstep (se 1 (by rfl) ⟨2147552, by rfl⟩ : syracuseStep 2863403 = 4295105) B4295105
theorem B2863673 : Blo 846354 2863673 := bstep (se 2 (by rfl) ⟨1073877, by rfl⟩ : syracuseStep 2863673 = 2147755) B2147755
theorem B3060287 : Blo 846354 3060287 := bstep (se 1 (by rfl) ⟨2295215, by rfl⟩ : syracuseStep 3060287 = 4590431) B4590431
theorem B3617743 : Blo 846354 3617743 := bstep (se 1 (by rfl) ⟨2713307, by rfl⟩ : syracuseStep 3617743 = 5426615) B5426615
theorem B4830263 : Blo 846354 4830263 := bstep (se 1 (by rfl) ⟨3622697, by rfl⟩ : syracuseStep 4830263 = 7245395) B7245395
theorem B2143361 : Blo 846354 2143361 := bstep (se 2 (by rfl) ⟨803760, by rfl⟩ : syracuseStep 2143361 = 1607521) B1607521
theorem B3225203 : Blo 846354 3225203 := bstep (se 1 (by rfl) ⟨2418902, by rfl⟩ : syracuseStep 3225203 = 4837805) B4837805
theorem B2144171 : Blo 846354 2144171 := bstep (se 1 (by rfl) ⟨1608128, by rfl⟩ : syracuseStep 2144171 = 3216257) B3216257
theorem B6961153 : Blo 846354 6961153 := bstep (se 2 (by rfl) ⟨2610432, by rfl⟩ : syracuseStep 6961153 = 5220865) B5220865
theorem B2865401 : Blo 846354 2865401 := bstep (se 2 (by rfl) ⟨1074525, by rfl⟩ : syracuseStep 2865401 = 2149051) B2149051
theorem B2865671 : Blo 846354 2865671 := bstep (se 1 (by rfl) ⟨2149253, by rfl⟩ : syracuseStep 2865671 = 4298507) B4298507
theorem B2145001 : Blo 846354 2145001 := bstep (se 2 (by rfl) ⟨804375, by rfl⟩ : syracuseStep 2145001 = 1608751) B1608751
theorem B15678359 : Blo 846354 15678359 := bstep (se 1 (by rfl) ⟨11758769, by rfl⟩ : syracuseStep 15678359 = 23517539) B23517539
theorem B9288685 : Blo 846354 9288685 := bstep (se 3 (by rfl) ⟨1741628, by rfl⟩ : syracuseStep 9288685 = 3483257) B3483257
theorem B2866751 : Blo 846354 2866751 := bstep (se 1 (by rfl) ⟨2150063, by rfl⟩ : syracuseStep 2866751 = 4300127) B4300127
theorem B2867453 : Blo 846354 2867453 := bstep (se 3 (by rfl) ⟨537647, by rfl⟩ : syracuseStep 2867453 = 1075295) B1075295
theorem B26165861 : Blo 846354 26165861 := bstep (se 4 (by rfl) ⟨2453049, by rfl⟩ : syracuseStep 26165861 = 4906099) B4906099
theorem B2867993 : Blo 846354 2867993 := bstep (se 2 (by rfl) ⟨1075497, by rfl⟩ : syracuseStep 2867993 = 2150995) B2150995
theorem B2868263 : Blo 846354 2868263 := bstep (se 1 (by rfl) ⟨2151197, by rfl⟩ : syracuseStep 2868263 = 4302395) B4302395
theorem B7357483 : Blo 846354 7357483 := bstep (se 1 (by rfl) ⟨5518112, by rfl⟩ : syracuseStep 7357483 = 11036225) B11036225
theorem B4081033 : Blo 846354 4081033 := bstep (se 2 (by rfl) ⟨1530387, by rfl⟩ : syracuseStep 4081033 = 3060775) B3060775
theorem B2148383 : Blo 846354 2148383 := bstep (se 1 (by rfl) ⟨1611287, by rfl⟩ : syracuseStep 2148383 = 3222575) B3222575
theorem B2869343 : Blo 846354 2869343 := bstep (se 1 (by rfl) ⟨2152007, by rfl⟩ : syracuseStep 2869343 = 4304015) B4304015
theorem B6867089 : Blo 846354 6867089 := bstep (se 2 (by rfl) ⟨2575158, by rfl⟩ : syracuseStep 6867089 = 5150317) B5150317
theorem B2149001 : Blo 846354 2149001 := bstep (se 2 (by rfl) ⟨805875, by rfl⟩ : syracuseStep 2149001 = 1611751) B1611751
theorem B8276779 : Blo 846354 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B3623723 : Blo 846354 3623723 := bstep (se 1 (by rfl) ⟨2717792, by rfl⟩ : syracuseStep 3623723 = 5435585) B5435585
theorem B1428475 : Blo 846354 1428475 := bstep (se 1 (by rfl) ⟨1071356, by rfl⟩ : syracuseStep 1428475 = 2142713) B2142713
theorem B4836347 : Blo 846354 4836347 := bstep (se 1 (by rfl) ⟨3627260, by rfl⟩ : syracuseStep 4836347 = 7254521) B7254521
theorem B2444705 : Blo 846354 2444705 := bstep (se 2 (by rfl) ⟨916764, by rfl⟩ : syracuseStep 2444705 = 1833529) B1833529
theorem B6868583 : Blo 846354 6868583 := bstep (se 1 (by rfl) ⟨5151437, by rfl⟩ : syracuseStep 6868583 = 10302875) B10302875
theorem B2575975 : Blo 846354 2575975 := bstep (se 1 (by rfl) ⟨1931981, by rfl⟩ : syracuseStep 2575975 = 3863963) B3863963
theorem B10867067 : Blo 846354 10867067 := bstep (se 1 (by rfl) ⟨8150300, by rfl⟩ : syracuseStep 10867067 = 16300601) B16300601
theorem B12243905 : Blo 846354 12243905 := bstep (se 2 (by rfl) ⟨4591464, by rfl⟩ : syracuseStep 12243905 = 9182929) B9182929
theorem B7263269 : Blo 846354 7263269 := bstep (se 4 (by rfl) ⟨680931, by rfl⟩ : syracuseStep 7263269 = 1361863) B1361863
theorem B4838555 : Blo 846354 4838555 := bstep (se 1 (by rfl) ⟨3628916, by rfl⟩ : syracuseStep 4838555 = 7257833) B7257833
theorem B7263917 : Blo 846354 7263917 := bstep (se 3 (by rfl) ⟨1361984, by rfl⟩ : syracuseStep 7263917 = 2723969) B2723969
theorem B1432039 : Blo 846354 1432039 := bstep (se 1 (by rfl) ⟨1074029, by rfl⟩ : syracuseStep 1432039 = 2148059) B2148059
theorem B11000371 : Blo 846354 11000371 := bstep (se 1 (by rfl) ⟨8250278, by rfl⟩ : syracuseStep 11000371 = 16500557) B16500557
theorem B6445817 : Blo 846354 6445817 := bstep (se 2 (by rfl) ⟨2417181, by rfl⟩ : syracuseStep 6445817 = 4834363) B4834363
theorem B8149841 : Blo 846354 8149841 := bstep (se 2 (by rfl) ⟨3056190, by rfl⟩ : syracuseStep 8149841 = 6112381) B6112381
theorem B1432903 : Blo 846354 1432903 := bstep (se 1 (by rfl) ⟨1074677, by rfl⟩ : syracuseStep 1432903 = 2149355) B2149355
theorem B8150381 : Blo 846354 8150381 := bstep (se 3 (by rfl) ⟨1528196, by rfl⟩ : syracuseStep 8150381 = 3056393) B3056393
theorem B1433065 : Blo 846354 1433065 := bstep (se 2 (by rfl) ⟨537399, by rfl⟩ : syracuseStep 1433065 = 1074799) B1074799
theorem B18341639 : Blo 846354 18341639 := bstep (se 1 (by rfl) ⟨13756229, by rfl⟩ : syracuseStep 18341639 = 27512459) B27512459
theorem B7233299 : Blo 846354 7233299 := bstep (se 1 (by rfl) ⟨5424974, by rfl⟩ : syracuseStep 7233299 = 10849949) B10849949
theorem B1269737 : Blo 846354 1269737 := bstep (se 2 (by rfl) ⟨476151, by rfl⟩ : syracuseStep 1269737 = 952303) B952303
theorem B848977955 : Blo 846354 848977955 := bstep (se 1 (by rfl) ⟨636733466, by rfl⟩ : syracuseStep 848977955 = 1273466933) B1273466933
theorem B1073407 : Blo 846354 1073407 := bstep (se 1 (by rfl) ⟨805055, by rfl⟩ : syracuseStep 1073407 = 1610111) B1610111
theorem B1433855 : Blo 846354 1433855 := bstep (se 1 (by rfl) ⟨1075391, by rfl⟩ : syracuseStep 1433855 = 2150783) B2150783
theorem B111337739 : Blo 846354 111337739 := bstep (se 1 (by rfl) ⟨83503304, by rfl⟩ : syracuseStep 111337739 = 167006609) B167006609
theorem B6119705 : Blo 846354 6119705 := bstep (se 2 (by rfl) ⟨2294889, by rfl⟩ : syracuseStep 6119705 = 4589779) B4589779
theorem B13034033 : Blo 846354 13034033 := bstep (se 2 (by rfl) ⟨4887762, by rfl⟩ : syracuseStep 13034033 = 9775525) B9775525
theorem B6873673 : Blo 846354 6873673 := bstep (se 2 (by rfl) ⟨2577627, by rfl⟩ : syracuseStep 6873673 = 5155255) B5155255
theorem B1270439 : Blo 846354 1270439 := bstep (se 1 (by rfl) ⟨952829, by rfl⟩ : syracuseStep 1270439 = 1905659) B1905659
theorem B1270559 : Blo 846354 1270559 := bstep (se 1 (by rfl) ⟨952919, by rfl⟩ : syracuseStep 1270559 = 1905839) B1905839
theorem B1270583 : Blo 846354 1270583 := bstep (se 1 (by rfl) ⟨952937, by rfl⟩ : syracuseStep 1270583 = 1905875) B1905875
theorem B1270763 : Blo 846354 1270763 := bstep (se 1 (by rfl) ⟨953072, by rfl⟩ : syracuseStep 1270763 = 1906145) B1906145
theorem B39216419 : Blo 846354 39216419 := bstep (se 1 (by rfl) ⟨29412314, by rfl⟩ : syracuseStep 39216419 = 58824629) B58824629
theorem B1271855 : Blo 846354 1271855 := bstep (se 1 (by rfl) ⟨953891, by rfl⟩ : syracuseStep 1271855 = 1907783) B1907783
theorem B1272119 : Blo 846354 1272119 := bstep (se 1 (by rfl) ⟨954089, by rfl⟩ : syracuseStep 1272119 = 1908179) B1908179
theorem B1272299 : Blo 846354 1272299 := bstep (se 1 (by rfl) ⟨954224, by rfl⟩ : syracuseStep 1272299 = 1908449) B1908449
theorem B846383 : Blo 846354 846383 := bstep (se 1 (by rfl) ⟨634787, by rfl⟩ : syracuseStep 846383 = 1269575) B1269575
theorem B846439 : Blo 846354 846439 := bstep (se 1 (by rfl) ⟨634829, by rfl⟩ : syracuseStep 846439 = 1269659) B1269659
theorem B29420243 : Blo 846354 29420243 := bstep (se 1 (by rfl) ⟨22065182, by rfl⟩ : syracuseStep 29420243 = 44130365) B44130365
theorem B2321291 : Blo 846354 2321291 := bstep (se 1 (by rfl) ⟨1740968, by rfl⟩ : syracuseStep 2321291 = 3481937) B3481937
theorem B846815 : Blo 846354 846815 := bstep (se 1 (by rfl) ⟨635111, by rfl⟩ : syracuseStep 846815 = 1270223) B1270223
theorem B846843 : Blo 846354 846843 := bstep (se 1 (by rfl) ⟨635132, by rfl⟩ : syracuseStep 846843 = 1270265) B1270265
theorem B846911 : Blo 846354 846911 := bstep (se 1 (by rfl) ⟨635183, by rfl⟩ : syracuseStep 846911 = 1270367) B1270367
theorem B1273001 : Blo 846354 1273001 := bstep (se 2 (by rfl) ⟨477375, by rfl⟩ : syracuseStep 1273001 = 954751) B954751
theorem B847231 : Blo 846354 847231 := bstep (se 1 (by rfl) ⟨635423, by rfl⟩ : syracuseStep 847231 = 1270847) B1270847
theorem B847259 : Blo 846354 847259 := bstep (se 1 (by rfl) ⟨635444, by rfl⟩ : syracuseStep 847259 = 1270889) B1270889
theorem B847327 : Blo 846354 847327 := bstep (se 1 (by rfl) ⟨635495, by rfl⟩ : syracuseStep 847327 = 1270991) B1270991
theorem B5795309 : Blo 846354 5795309 := bstep (se 3 (by rfl) ⟨1086620, by rfl⟩ : syracuseStep 5795309 = 2173241) B2173241
theorem B1273415 : Blo 846354 1273415 := bstep (se 1 (by rfl) ⟨955061, by rfl⟩ : syracuseStep 1273415 = 1910123) B1910123
theorem B847463 : Blo 846354 847463 := bstep (se 1 (by rfl) ⟨635597, by rfl⟩ : syracuseStep 847463 = 1271195) B1271195
theorem B847611 : Blo 846354 847611 := bstep (se 1 (by rfl) ⟨635708, by rfl⟩ : syracuseStep 847611 = 1271417) B1271417
theorem B1273595 : Blo 846354 1273595 := bstep (se 1 (by rfl) ⟨955196, by rfl⟩ : syracuseStep 1273595 = 1910393) B1910393
theorem B847679 : Blo 846354 847679 := bstep (se 1 (by rfl) ⟨635759, by rfl⟩ : syracuseStep 847679 = 1271519) B1271519
theorem B847743 : Blo 846354 847743 := bstep (se 1 (by rfl) ⟨635807, by rfl⟩ : syracuseStep 847743 = 1271615) B1271615
theorem B52195205 : Blo 846354 52195205 := bstep (se 4 (by rfl) ⟨4893300, by rfl⟩ : syracuseStep 52195205 = 9786601) B9786601
theorem B6451163 : Blo 846354 6451163 := bstep (se 1 (by rfl) ⟨4838372, by rfl⟩ : syracuseStep 6451163 = 9676745) B9676745
theorem B847855 : Blo 846354 847855 := bstep (se 1 (by rfl) ⟨635891, by rfl⟩ : syracuseStep 847855 = 1271783) B1271783
theorem B847867 : Blo 846354 847867 := bstep (se 1 (by rfl) ⟨635900, by rfl⟩ : syracuseStep 847867 = 1271801) B1271801
theorem B847935 : Blo 846354 847935 := bstep (se 1 (by rfl) ⟨635951, by rfl⟩ : syracuseStep 847935 = 1271903) B1271903
theorem B3436627 : Blo 846354 3436627 := bstep (se 1 (by rfl) ⟨2577470, by rfl⟩ : syracuseStep 3436627 = 5154941) B5154941
theorem B2715731 : Blo 846354 2715731 := bstep (se 1 (by rfl) ⟨2036798, by rfl⟩ : syracuseStep 2715731 = 4073597) B4073597
theorem B847975 : Blo 846354 847975 := bstep (se 1 (by rfl) ⟨635981, by rfl⟩ : syracuseStep 847975 = 1271963) B1271963
theorem B847999 : Blo 846354 847999 := bstep (se 1 (by rfl) ⟨635999, by rfl⟩ : syracuseStep 847999 = 1271999) B1271999
theorem B848027 : Blo 846354 848027 := bstep (se 1 (by rfl) ⟨636020, by rfl⟩ : syracuseStep 848027 = 1272041) B1272041
theorem B2420999 : Blo 846354 2420999 := bstep (se 1 (by rfl) ⟨1815749, by rfl⟩ : syracuseStep 2420999 = 3631499) B3631499
theorem B848231 : Blo 846354 848231 := bstep (se 1 (by rfl) ⟨636173, by rfl⟩ : syracuseStep 848231 = 1272347) B1272347
theorem B15692167 : Blo 846354 15692167 := bstep (se 1 (by rfl) ⟨11769125, by rfl⟩ : syracuseStep 15692167 = 23538251) B23538251
theorem B848283 : Blo 846354 848283 := bstep (se 1 (by rfl) ⟨636212, by rfl⟩ : syracuseStep 848283 = 1272425) B1272425
theorem B1274267 : Blo 846354 1274267 := bstep (se 1 (by rfl) ⟨955700, by rfl⟩ : syracuseStep 1274267 = 1911401) B1911401
theorem B848635 : Blo 846354 848635 := bstep (se 1 (by rfl) ⟨636476, by rfl⟩ : syracuseStep 848635 = 1272953) B1272953
theorem B848703 : Blo 846354 848703 := bstep (se 1 (by rfl) ⟨636527, by rfl⟩ : syracuseStep 848703 = 1273055) B1273055
theorem B1274687 : Blo 846354 1274687 := bstep (se 1 (by rfl) ⟨956015, by rfl⟩ : syracuseStep 1274687 = 1912031) B1912031
theorem B848731 : Blo 846354 848731 := bstep (se 1 (by rfl) ⟨636548, by rfl⟩ : syracuseStep 848731 = 1273097) B1273097
theorem B848799 : Blo 846354 848799 := bstep (se 1 (by rfl) ⟨636599, by rfl⟩ : syracuseStep 848799 = 1273199) B1273199
theorem B1274831 : Blo 846354 1274831 := bstep (se 1 (by rfl) ⟨956123, by rfl⟩ : syracuseStep 1274831 = 1912247) B1912247
theorem B848879 : Blo 846354 848879 := bstep (se 1 (by rfl) ⟨636659, by rfl⟩ : syracuseStep 848879 = 1273319) B1273319
theorem B1274873 : Blo 846354 1274873 := bstep (se 2 (by rfl) ⟨478077, by rfl⟩ : syracuseStep 1274873 = 956155) B956155
theorem B1274921 : Blo 846354 1274921 := bstep (se 2 (by rfl) ⟨478095, by rfl⟩ : syracuseStep 1274921 = 956191) B956191
theorem B848967 : Blo 846354 848967 := bstep (se 1 (by rfl) ⟨636725, by rfl⟩ : syracuseStep 848967 = 1273451) B1273451
theorem B1274951 : Blo 846354 1274951 := bstep (se 1 (by rfl) ⟨956213, by rfl⟩ : syracuseStep 1274951 = 1912427) B1912427
theorem B849051 : Blo 846354 849051 := bstep (se 1 (by rfl) ⟨636788, by rfl⟩ : syracuseStep 849051 = 1273577) B1273577
theorem B849147 : Blo 846354 849147 := bstep (se 1 (by rfl) ⟨636860, by rfl⟩ : syracuseStep 849147 = 1273721) B1273721
theorem B1275131 : Blo 846354 1275131 := bstep (se 1 (by rfl) ⟨956348, by rfl⟩ : syracuseStep 1275131 = 1912697) B1912697
theorem B3667207 : Blo 846354 3667207 := bstep (se 1 (by rfl) ⟨2750405, by rfl⟩ : syracuseStep 3667207 = 5500811) B5500811
theorem B849215 : Blo 846354 849215 := bstep (se 1 (by rfl) ⟨636911, by rfl⟩ : syracuseStep 849215 = 1273823) B1273823
theorem B849383 : Blo 846354 849383 := bstep (se 1 (by rfl) ⟨637037, by rfl⟩ : syracuseStep 849383 = 1274075) B1274075
theorem B849391 : Blo 846354 849391 := bstep (se 1 (by rfl) ⟨637043, by rfl⟩ : syracuseStep 849391 = 1274087) B1274087
theorem B32634413 : Blo 846354 32634413 := bstep (se 3 (by rfl) ⟨6118952, by rfl⟩ : syracuseStep 32634413 = 12237905) B12237905
theorem B15496775 : Blo 846354 15496775 := bstep (se 1 (by rfl) ⟨11622581, by rfl⟩ : syracuseStep 15496775 = 23245163) B23245163
theorem B5437019 : Blo 846354 5437019 := bstep (se 1 (by rfl) ⟨4077764, by rfl⟩ : syracuseStep 5437019 = 8155529) B8155529
theorem B849499 : Blo 846354 849499 := bstep (se 1 (by rfl) ⟨637124, by rfl⟩ : syracuseStep 849499 = 1274249) B1274249
theorem B849563 : Blo 846354 849563 := bstep (se 1 (by rfl) ⟨637172, by rfl⟩ : syracuseStep 849563 = 1274345) B1274345
theorem B849647 : Blo 846354 849647 := bstep (se 1 (by rfl) ⟨637235, by rfl⟩ : syracuseStep 849647 = 1274471) B1274471
theorem B11597579 : Blo 846354 11597579 := bstep (se 1 (by rfl) ⟨8698184, by rfl⟩ : syracuseStep 11597579 = 17396369) B17396369
theorem B849735 : Blo 846354 849735 := bstep (se 1 (by rfl) ⟨637301, by rfl⟩ : syracuseStep 849735 = 1274603) B1274603
theorem B849755 : Blo 846354 849755 := bstep (se 1 (by rfl) ⟨637316, by rfl⟩ : syracuseStep 849755 = 1274633) B1274633
theorem B849823 : Blo 846354 849823 := bstep (se 1 (by rfl) ⟨637367, by rfl⟩ : syracuseStep 849823 = 1274735) B1274735
theorem B849991 : Blo 846354 849991 := bstep (se 1 (by rfl) ⟨637493, by rfl⟩ : syracuseStep 849991 = 1274987) B1274987
theorem B850151 : Blo 846354 850151 := bstep (se 1 (by rfl) ⟨637613, by rfl⟩ : syracuseStep 850151 = 1275227) B1275227
theorem B10483991 : Blo 846354 10483991 := bstep (se 1 (by rfl) ⟨7862993, by rfl⟩ : syracuseStep 10483991 = 15725987) B15725987
theorem B850335 : Blo 846354 850335 := bstep (se 1 (by rfl) ⟨637751, by rfl⟩ : syracuseStep 850335 = 1275503) B1275503
theorem B6977987 : Blo 846354 6977987 := bstep (se 1 (by rfl) ⟨5233490, by rfl⟩ : syracuseStep 6977987 = 10466981) B10466981
theorem B9665081 : Blo 846354 9665081 := bstep (se 2 (by rfl) ⟨3624405, by rfl⟩ : syracuseStep 9665081 = 7248811) B7248811
theorem B7240337 : Blo 846354 7240337 := bstep (se 2 (by rfl) ⟨2715126, by rfl⟩ : syracuseStep 7240337 = 5430253) B5430253
theorem B4291217 : Blo 846354 4291217 := bstep (se 2 (by rfl) ⟨1609206, by rfl⟩ : syracuseStep 4291217 = 3218413) B3218413
theorem B3439741 : Blo 846354 3439741 := bstep (se 3 (by rfl) ⟨644951, by rfl⟩ : syracuseStep 3439741 = 1289903) B1289903
theorem B4587293 : Blo 846354 4587293 := bstep (se 3 (by rfl) ⟨860117, by rfl⟩ : syracuseStep 4587293 = 1720235) B1720235
theorem B3670427 : Blo 846354 3670427 := bstep (se 1 (by rfl) ⟨2752820, by rfl⟩ : syracuseStep 3670427 = 5505641) B5505641
theorem B10846973 : Blo 846354 10846973 := bstep (se 3 (by rfl) ⟨2033807, by rfl⟩ : syracuseStep 10846973 = 4067615) B4067615
theorem B9798425 : Blo 846354 9798425 := bstep (se 2 (by rfl) ⟨3674409, by rfl⟩ : syracuseStep 9798425 = 7348819) B7348819
theorem B14517305 : Blo 846354 14517305 := bstep (se 2 (by rfl) ⟨5443989, by rfl⟩ : syracuseStep 14517305 = 10887979) B10887979
theorem B2360495 : Blo 846354 2360495 := bstep (se 1 (by rfl) ⟨1770371, by rfl⟩ : syracuseStep 2360495 = 3540743) B3540743
theorem B5441377 : Blo 846354 5441377 := bstep (se 2 (by rfl) ⟨2040516, by rfl⟩ : syracuseStep 5441377 = 4081033) B4081033
theorem B9177047 : Blo 846354 9177047 := bstep (se 1 (by rfl) ⟨6882785, by rfl⟩ : syracuseStep 9177047 = 13765571) B13765571
theorem B12257405 : Blo 846354 12257405 := bstep (se 3 (by rfl) ⟨2298263, by rfl⟩ : syracuseStep 12257405 = 4596527) B4596527
theorem B10881215 : Blo 846354 10881215 := bstep (se 1 (by rfl) ⟨8160911, by rfl⟩ : syracuseStep 10881215 = 16321823) B16321823
theorem B7244711 : Blo 846354 7244711 := bstep (se 1 (by rfl) ⟨5433533, by rfl⟩ : syracuseStep 7244711 = 10867067) B10867067
theorem B4295753 : Blo 846354 4295753 := bstep (se 2 (by rfl) ⟨1610907, by rfl⟩ : syracuseStep 4295753 = 3221815) B3221815
theorem B8162603 : Blo 846354 8162603 := bstep (se 1 (by rfl) ⟨6121952, by rfl⟩ : syracuseStep 8162603 = 12243905) B12243905
theorem B1904633 : Blo 846354 1904633 := bstep (se 2 (by rfl) ⟨714237, by rfl⟩ : syracuseStep 1904633 = 1428475) B1428475
theorem B1904723 : Blo 846354 1904723 := bstep (se 1 (by rfl) ⟨1428542, by rfl⟩ : syracuseStep 1904723 = 2857085) B2857085
theorem B1904831 : Blo 846354 1904831 := bstep (se 1 (by rfl) ⟨1428623, by rfl⟩ : syracuseStep 1904831 = 2857247) B2857247
theorem B1904903 : Blo 846354 1904903 := bstep (se 1 (by rfl) ⟨1428677, by rfl⟩ : syracuseStep 1904903 = 2857355) B2857355
theorem B4297211 : Blo 846354 4297211 := bstep (se 1 (by rfl) ⟨3222908, by rfl⟩ : syracuseStep 4297211 = 6445817) B6445817
theorem B2036231 : Blo 846354 2036231 := bstep (se 1 (by rfl) ⟨1527173, by rfl⟩ : syracuseStep 2036231 = 3054347) B3054347
theorem B4297697 : Blo 846354 4297697 := bstep (se 2 (by rfl) ⟨1611636, by rfl⟩ : syracuseStep 4297697 = 3223273) B3223273
theorem B12227759 : Blo 846354 12227759 := bstep (se 1 (by rfl) ⟨9170819, by rfl⟩ : syracuseStep 12227759 = 18341639) B18341639
theorem B4822199 : Blo 846354 4822199 := bstep (se 1 (by rfl) ⟨3616649, by rfl⟩ : syracuseStep 4822199 = 7233299) B7233299
theorem B1905983 : Blo 846354 1905983 := bstep (se 1 (by rfl) ⟨1429487, by rfl⟩ : syracuseStep 1905983 = 2858975) B2858975
theorem B1840463 : Blo 846354 1840463 := bstep (se 1 (by rfl) ⟨1380347, by rfl⟩ : syracuseStep 1840463 = 2760695) B2760695
theorem B1906091 : Blo 846354 1906091 := bstep (se 1 (by rfl) ⟨1429568, by rfl⟩ : syracuseStep 1906091 = 2859137) B2859137
theorem B955903 : Blo 846354 955903 := bstep (se 1 (by rfl) ⟨716927, by rfl⟩ : syracuseStep 955903 = 1433855) B1433855
theorem B74225159 : Blo 846354 74225159 := bstep (se 1 (by rfl) ⟨55668869, by rfl⟩ : syracuseStep 74225159 = 111337739) B111337739
theorem B8689355 : Blo 846354 8689355 := bstep (se 1 (by rfl) ⟨6517016, by rfl⟩ : syracuseStep 8689355 = 13034033) B13034033
theorem B1906631 : Blo 846354 1906631 := bstep (se 1 (by rfl) ⟨1429973, by rfl⟩ : syracuseStep 1906631 = 2859947) B2859947
theorem B1906991 : Blo 846354 1906991 := bstep (se 1 (by rfl) ⟨1430243, by rfl⟩ : syracuseStep 1906991 = 2860487) B2860487
theorem B4823657 : Blo 846354 4823657 := bstep (se 2 (by rfl) ⟨1808871, by rfl⟩ : syracuseStep 4823657 = 3617743) B3617743
theorem B4889609 : Blo 846354 4889609 := bstep (se 2 (by rfl) ⟨1833603, by rfl⟩ : syracuseStep 4889609 = 3667207) B3667207
theorem B1547527 : Blo 846354 1547527 := bstep (se 1 (by rfl) ⟨1160645, by rfl⟩ : syracuseStep 1547527 = 2321291) B2321291
theorem B4070827 : Blo 846354 4070827 := bstep (se 1 (by rfl) ⟨3053120, by rfl⟩ : syracuseStep 4070827 = 6106241) B6106241
theorem B1908395 : Blo 846354 1908395 := bstep (se 1 (by rfl) ⟨1431296, by rfl⟩ : syracuseStep 1908395 = 2862593) B2862593
theorem B4300775 : Blo 846354 4300775 := bstep (se 1 (by rfl) ⟨3225581, by rfl⟩ : syracuseStep 4300775 = 6451163) B6451163
theorem B9281537 : Blo 846354 9281537 := bstep (se 2 (by rfl) ⟨3480576, by rfl⟩ : syracuseStep 9281537 = 6961153) B6961153
theorem B1810487 : Blo 846354 1810487 := bstep (se 1 (by rfl) ⟨1357865, by rfl⟩ : syracuseStep 1810487 = 2715731) B2715731
theorem B1613999 : Blo 846354 1613999 := bstep (se 1 (by rfl) ⟨1210499, by rfl⟩ : syracuseStep 1613999 = 2420999) B2420999
theorem B1908935 : Blo 846354 1908935 := bstep (se 1 (by rfl) ⟨1431701, by rfl⟩ : syracuseStep 1908935 = 2863403) B2863403
theorem B1909115 : Blo 846354 1909115 := bstep (se 1 (by rfl) ⟨1431836, by rfl⟩ : syracuseStep 1909115 = 2863673) B2863673
theorem B2040191 : Blo 846354 2040191 := bstep (se 1 (by rfl) ⟨1530143, by rfl⟩ : syracuseStep 2040191 = 3060287) B3060287
theorem B1909385 : Blo 846354 1909385 := bstep (se 2 (by rfl) ⟨716019, by rfl⟩ : syracuseStep 1909385 = 1432039) B1432039
theorem B3220175 : Blo 846354 3220175 := bstep (se 1 (by rfl) ⟨2415131, by rfl⟩ : syracuseStep 3220175 = 4830263) B4830263
theorem B2860001 : Blo 846354 2860001 := bstep (se 2 (by rfl) ⟨1072500, by rfl⟩ : syracuseStep 2860001 = 2145001) B2145001
theorem B10331183 : Blo 846354 10331183 := bstep (se 1 (by rfl) ⟨7748387, by rfl⟩ : syracuseStep 10331183 = 15496775) B15496775
theorem B1910267 : Blo 846354 1910267 := bstep (se 1 (by rfl) ⟨1432700, by rfl⟩ : syracuseStep 1910267 = 2865401) B2865401
theorem B6989327 : Blo 846354 6989327 := bstep (se 1 (by rfl) ⟨5241995, by rfl⟩ : syracuseStep 6989327 = 10483991) B10483991
theorem B1910447 : Blo 846354 1910447 := bstep (se 1 (by rfl) ⟨1432835, by rfl⟩ : syracuseStep 1910447 = 2865671) B2865671
theorem B1910537 : Blo 846354 1910537 := bstep (se 2 (by rfl) ⟨716451, by rfl⟩ : syracuseStep 1910537 = 1432903) B1432903
theorem B4826891 : Blo 846354 4826891 := bstep (se 1 (by rfl) ⟨3620168, by rfl⟩ : syracuseStep 4826891 = 7240337) B7240337
theorem B2860811 : Blo 846354 2860811 := bstep (se 1 (by rfl) ⟨2145608, by rfl⟩ : syracuseStep 2860811 = 4291217) B4291217
theorem B1910753 : Blo 846354 1910753 := bstep (se 2 (by rfl) ⟨716532, by rfl⟩ : syracuseStep 1910753 = 1433065) B1433065
theorem B12232781 : Blo 846354 12232781 := bstep (se 3 (by rfl) ⟨2293646, by rfl⟩ : syracuseStep 12232781 = 4587293) B4587293
theorem B1911167 : Blo 846354 1911167 := bstep (se 1 (by rfl) ⟨1433375, by rfl⟩ : syracuseStep 1911167 = 2866751) B2866751
theorem B1911635 : Blo 846354 1911635 := bstep (se 1 (by rfl) ⟨1433726, by rfl⟩ : syracuseStep 1911635 = 2867453) B2867453
theorem B17443907 : Blo 846354 17443907 := bstep (se 1 (by rfl) ⟨13082930, by rfl⟩ : syracuseStep 17443907 = 26165861) B26165861
theorem B10857635 : Blo 846354 10857635 := bstep (se 1 (by rfl) ⟨8143226, by rfl⟩ : syracuseStep 10857635 = 16286453) B16286453
theorem B2796713 : Blo 846354 2796713 := bstep (se 2 (by rfl) ⟨1048767, by rfl⟩ : syracuseStep 2796713 = 2097535) B2097535
theorem B1911995 : Blo 846354 1911995 := bstep (se 1 (by rfl) ⟨1433996, by rfl⟩ : syracuseStep 1911995 = 2867993) B2867993
theorem B8170753 : Blo 846354 8170753 := bstep (se 2 (by rfl) ⟨3064032, by rfl⟩ : syracuseStep 8170753 = 6128065) B6128065
theorem B1813843 : Blo 846354 1813843 := bstep (se 1 (by rfl) ⟨1360382, by rfl⟩ : syracuseStep 1813843 = 2720765) B2720765
theorem B2862431 : Blo 846354 2862431 := bstep (se 1 (by rfl) ⟨2146823, by rfl⟩ : syracuseStep 2862431 = 4293647) B4293647
theorem B1912175 : Blo 846354 1912175 := bstep (se 1 (by rfl) ⟨1434131, by rfl⟩ : syracuseStep 1912175 = 2868263) B2868263
theorem B7253459 : Blo 846354 7253459 := bstep (se 1 (by rfl) ⟨5440094, by rfl⟩ : syracuseStep 7253459 = 10880189) B10880189
theorem B2862971 : Blo 846354 2862971 := bstep (se 1 (by rfl) ⟨2147228, by rfl⟩ : syracuseStep 2862971 = 4294457) B4294457
theorem B9809977 : Blo 846354 9809977 := bstep (se 2 (by rfl) ⟨3678741, by rfl⟩ : syracuseStep 9809977 = 7357483) B7357483
theorem B1912895 : Blo 846354 1912895 := bstep (se 1 (by rfl) ⟨1434671, by rfl⟩ : syracuseStep 1912895 = 2869343) B2869343
theorem B2142521 : Blo 846354 2142521 := bstep (se 2 (by rfl) ⟨803445, by rfl⟩ : syracuseStep 2142521 = 1606891) B1606891
theorem B9154903 : Blo 846354 9154903 := bstep (se 1 (by rfl) ⟨6866177, by rfl⟩ : syracuseStep 9154903 = 13732355) B13732355
theorem B3224231 : Blo 846354 3224231 := bstep (se 1 (by rfl) ⟨2418173, by rfl⟩ : syracuseStep 3224231 = 4836347) B4836347
theorem B1816091 : Blo 846354 1816091 := bstep (se 1 (by rfl) ⟨1362068, by rfl⟩ : syracuseStep 1816091 = 2724137) B2724137
theorem B2864915 : Blo 846354 2864915 := bstep (se 1 (by rfl) ⟨2148686, by rfl⟩ : syracuseStep 2864915 = 4297373) B4297373
theorem B3258251 : Blo 846354 3258251 := bstep (se 1 (by rfl) ⟨2443688, by rfl⟩ : syracuseStep 3258251 = 4887377) B4887377
theorem B2144191 : Blo 846354 2144191 := bstep (se 1 (by rfl) ⟨1608143, by rfl⟩ : syracuseStep 2144191 = 3216287) B3216287
theorem B3225703 : Blo 846354 3225703 := bstep (se 1 (by rfl) ⟨2419277, by rfl⟩ : syracuseStep 3225703 = 4838555) B4838555
theorem B4831447 : Blo 846354 4831447 := bstep (se 1 (by rfl) ⟨3623585, by rfl⟩ : syracuseStep 4831447 = 7247171) B7247171
theorem B2865455 : Blo 846354 2865455 := bstep (se 1 (by rfl) ⟨2149091, by rfl⟩ : syracuseStep 2865455 = 4298183) B4298183
theorem B5159657 : Blo 846354 5159657 := bstep (se 2 (by rfl) ⟨1934871, by rfl⟩ : syracuseStep 5159657 = 3869743) B3869743
theorem B7355753 : Blo 846354 7355753 := bstep (se 2 (by rfl) ⟨2758407, by rfl⟩ : syracuseStep 7355753 = 5516815) B5516815
theorem B2146247 : Blo 846354 2146247 := bstep (se 1 (by rfl) ⟨1609685, by rfl⟩ : syracuseStep 2146247 = 3219371) B3219371
theorem B2146297 : Blo 846354 2146297 := bstep (se 2 (by rfl) ⟨804861, by rfl⟩ : syracuseStep 2146297 = 1609723) B1609723
theorem B565985303 : Blo 846354 565985303 := bstep (se 1 (by rfl) ⟨424488977, by rfl⟩ : syracuseStep 565985303 = 848977955) B848977955
theorem B4079803 : Blo 846354 4079803 := bstep (se 1 (by rfl) ⟨3059852, by rfl⟩ : syracuseStep 4079803 = 6119705) B6119705
theorem B20922889 : Blo 846354 20922889 := bstep (se 2 (by rfl) ⟨7846083, by rfl⟩ : syracuseStep 20922889 = 15692167) B15692167
theorem B5423897 : Blo 846354 5423897 := bstep (se 2 (by rfl) ⟨2033961, by rfl⟩ : syracuseStep 5423897 = 4067923) B4067923
theorem B2868911 : Blo 846354 2868911 := bstep (se 1 (by rfl) ⟨2151683, by rfl⟩ : syracuseStep 2868911 = 4303367) B4303367
theorem B19613495 : Blo 846354 19613495 := bstep (se 1 (by rfl) ⟨14710121, by rfl⟩ : syracuseStep 19613495 = 29420243) B29420243
theorem B8702579 : Blo 846354 8702579 := bstep (se 1 (by rfl) ⟨6526934, by rfl⟩ : syracuseStep 8702579 = 13053869) B13053869
theorem B14667161 : Blo 846354 14667161 := bstep (se 2 (by rfl) ⟨5500185, by rfl⟩ : syracuseStep 14667161 = 11000371) B11000371
theorem B1428907 : Blo 846354 1428907 := bstep (se 1 (by rfl) ⟨1071680, by rfl⟩ : syracuseStep 1428907 = 2143361) B2143361
theorem B3624679 : Blo 846354 3624679 := bstep (se 1 (by rfl) ⟨2718509, by rfl⟩ : syracuseStep 3624679 = 5437019) B5437019
theorem B2150135 : Blo 846354 2150135 := bstep (se 1 (by rfl) ⟨1612601, by rfl⟩ : syracuseStep 2150135 = 3225203) B3225203
theorem B1429447 : Blo 846354 1429447 := bstep (se 1 (by rfl) ⟨1072085, by rfl⟩ : syracuseStep 1429447 = 2144171) B2144171
theorem B6443387 : Blo 846354 6443387 := bstep (se 1 (by rfl) ⟨4832540, by rfl⟩ : syracuseStep 6443387 = 9665081) B9665081
theorem B16307365 : Blo 846354 16307365 := bstep (se 4 (by rfl) ⟨1528815, by rfl⟩ : syracuseStep 16307365 = 3057631) B3057631
theorem B1431209 : Blo 846354 1431209 := bstep (se 2 (by rfl) ⟨536703, by rfl⟩ : syracuseStep 1431209 = 1073407) B1073407
theorem B9164897 : Blo 846354 9164897 := bstep (se 2 (by rfl) ⟨3436836, by rfl⟩ : syracuseStep 9164897 = 6873673) B6873673
theorem B13064327 : Blo 846354 13064327 := bstep (se 1 (by rfl) ⟨9798245, by rfl⟩ : syracuseStep 13064327 = 19596491) B19596491
theorem B1432255 : Blo 846354 1432255 := bstep (se 1 (by rfl) ⟨1074191, by rfl⟩ : syracuseStep 1432255 = 2148383) B2148383
theorem B4578059 : Blo 846354 4578059 := bstep (se 1 (by rfl) ⟨3433544, by rfl⟩ : syracuseStep 4578059 = 6867089) B6867089
theorem B1432667 : Blo 846354 1432667 := bstep (se 1 (by rfl) ⟨1074500, by rfl⟩ : syracuseStep 1432667 = 2149001) B2149001
theorem B7232651 : Blo 846354 7232651 := bstep (se 1 (by rfl) ⟨5424488, by rfl⟩ : syracuseStep 7232651 = 10848977) B10848977
theorem B2415815 : Blo 846354 2415815 := bstep (se 1 (by rfl) ⟨1811861, by rfl⟩ : syracuseStep 2415815 = 3623723) B3623723
theorem B1072379 : Blo 846354 1072379 := bstep (se 1 (by rfl) ⟨804284, by rfl⟩ : syracuseStep 1072379 = 1608569) B1608569
theorem B2580025 : Blo 846354 2580025 := bstep (se 2 (by rfl) ⟨967509, by rfl⟩ : syracuseStep 2580025 = 1935019) B1935019
theorem B1629803 : Blo 846354 1629803 := bstep (se 1 (by rfl) ⟨1222352, by rfl⟩ : syracuseStep 1629803 = 2444705) B2444705
theorem B4579055 : Blo 846354 4579055 := bstep (se 1 (by rfl) ⟨3434291, by rfl⟩ : syracuseStep 4579055 = 6868583) B6868583
theorem B1269671 : Blo 846354 1269671 := bstep (se 1 (by rfl) ⟨952253, by rfl⟩ : syracuseStep 1269671 = 1904507) B1904507
theorem B1269743 : Blo 846354 1269743 := bstep (se 1 (by rfl) ⟨952307, by rfl⟩ : syracuseStep 1269743 = 1904615) B1904615
theorem B1269863 : Blo 846354 1269863 := bstep (se 1 (by rfl) ⟨952397, by rfl⟩ : syracuseStep 1269863 = 1904795) B1904795
theorem B1269995 : Blo 846354 1269995 := bstep (se 1 (by rfl) ⟨952496, by rfl⟩ : syracuseStep 1269995 = 1904993) B1904993
theorem B1270055 : Blo 846354 1270055 := bstep (se 1 (by rfl) ⟨952541, by rfl⟩ : syracuseStep 1270055 = 1905083) B1905083
theorem B4842179 : Blo 846354 4842179 := bstep (se 1 (by rfl) ⟨3631634, by rfl⟩ : syracuseStep 4842179 = 7263269) B7263269
theorem B1270505 : Blo 846354 1270505 := bstep (se 2 (by rfl) ⟨476439, by rfl⟩ : syracuseStep 1270505 = 952879) B952879
theorem B11035705 : Blo 846354 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B1270895 : Blo 846354 1270895 := bstep (se 1 (by rfl) ⟨953171, by rfl⟩ : syracuseStep 1270895 = 1906343) B1906343
theorem B4842611 : Blo 846354 4842611 := bstep (se 1 (by rfl) ⟨3631958, by rfl⟩ : syracuseStep 4842611 = 7263917) B7263917
theorem B1271015 : Blo 846354 1271015 := bstep (se 1 (by rfl) ⟨953261, by rfl⟩ : syracuseStep 1271015 = 1906523) B1906523
theorem B1271081 : Blo 846354 1271081 := bstep (se 2 (by rfl) ⟨476655, by rfl⟩ : syracuseStep 1271081 = 953311) B953311
theorem B1271351 : Blo 846354 1271351 := bstep (se 1 (by rfl) ⟨953513, by rfl⟩ : syracuseStep 1271351 = 1907027) B1907027
theorem B1271675 : Blo 846354 1271675 := bstep (se 1 (by rfl) ⟨953756, by rfl⟩ : syracuseStep 1271675 = 1907513) B1907513
theorem B5433227 : Blo 846354 5433227 := bstep (se 1 (by rfl) ⟨4074920, by rfl⟩ : syracuseStep 5433227 = 8149841) B8149841
theorem B1271711 : Blo 846354 1271711 := bstep (se 1 (by rfl) ⟨953783, by rfl⟩ : syracuseStep 1271711 = 1907567) B1907567
theorem B3434633 : Blo 846354 3434633 := bstep (se 2 (by rfl) ⟨1287987, by rfl⟩ : syracuseStep 3434633 = 2575975) B2575975
theorem B1271945 : Blo 846354 1271945 := bstep (se 2 (by rfl) ⟨476979, by rfl⟩ : syracuseStep 1271945 = 953959) B953959
theorem B5433587 : Blo 846354 5433587 := bstep (se 1 (by rfl) ⟨4075190, by rfl⟩ : syracuseStep 5433587 = 8150381) B8150381
theorem B1272095 : Blo 846354 1272095 := bstep (se 1 (by rfl) ⟨954071, by rfl⟩ : syracuseStep 1272095 = 1908143) B1908143
theorem B1272143 : Blo 846354 1272143 := bstep (se 1 (by rfl) ⟨954107, by rfl⟩ : syracuseStep 1272143 = 1908215) B1908215
theorem B4286843 : Blo 846354 4286843 := bstep (se 1 (by rfl) ⟨3215132, by rfl⟩ : syracuseStep 4286843 = 6430265) B6430265
theorem B1272233 : Blo 846354 1272233 := bstep (se 2 (by rfl) ⟨477087, by rfl⟩ : syracuseStep 1272233 = 954175) B954175
theorem B846491 : Blo 846354 846491 := bstep (se 1 (by rfl) ⟨634868, by rfl⟩ : syracuseStep 846491 = 1269737) B1269737
theorem B3631787 : Blo 846354 3631787 := bstep (se 1 (by rfl) ⟨2723840, by rfl⟩ : syracuseStep 3631787 = 5447681) B5447681
theorem B7563959 : Blo 846354 7563959 := bstep (se 1 (by rfl) ⟨5672969, by rfl⟩ : syracuseStep 7563959 = 11345939) B11345939
theorem B4582169 : Blo 846354 4582169 := bstep (se 2 (by rfl) ⟨1718313, by rfl⟩ : syracuseStep 4582169 = 3436627) B3436627
theorem B1272617 : Blo 846354 1272617 := bstep (se 2 (by rfl) ⟨477231, by rfl⟩ : syracuseStep 1272617 = 954463) B954463
theorem B1272827 : Blo 846354 1272827 := bstep (se 1 (by rfl) ⟨954620, by rfl⟩ : syracuseStep 1272827 = 1909241) B1909241
theorem B1272887 : Blo 846354 1272887 := bstep (se 1 (by rfl) ⟨954665, by rfl⟩ : syracuseStep 1272887 = 1909331) B1909331
theorem B846959 : Blo 846354 846959 := bstep (se 1 (by rfl) ⟨635219, by rfl⟩ : syracuseStep 846959 = 1270439) B1270439
theorem B1273007 : Blo 846354 1273007 := bstep (se 1 (by rfl) ⟨954755, by rfl⟩ : syracuseStep 1273007 = 1909511) B1909511
theorem B847039 : Blo 846354 847039 := bstep (se 1 (by rfl) ⟨635279, by rfl⟩ : syracuseStep 847039 = 1270559) B1270559
theorem B847055 : Blo 846354 847055 := bstep (se 1 (by rfl) ⟨635291, by rfl⟩ : syracuseStep 847055 = 1270583) B1270583
theorem B1273067 : Blo 846354 1273067 := bstep (se 1 (by rfl) ⟨954800, by rfl⟩ : syracuseStep 1273067 = 1909601) B1909601
theorem B847175 : Blo 846354 847175 := bstep (se 1 (by rfl) ⟨635381, by rfl⟩ : syracuseStep 847175 = 1270763) B1270763
theorem B18312571 : Blo 846354 18312571 := bstep (se 1 (by rfl) ⟨13734428, by rfl⟩ : syracuseStep 18312571 = 27468857) B27468857
theorem B26144279 : Blo 846354 26144279 := bstep (se 1 (by rfl) ⟨19608209, by rfl⟩ : syracuseStep 26144279 = 39216419) B39216419
theorem B2715383 : Blo 846354 2715383 := bstep (se 1 (by rfl) ⟨2036537, by rfl⟩ : syracuseStep 2715383 = 4073075) B4073075
theorem B1273727 : Blo 846354 1273727 := bstep (se 1 (by rfl) ⟨955295, by rfl⟩ : syracuseStep 1273727 = 1910591) B1910591
theorem B847903 : Blo 846354 847903 := bstep (se 1 (by rfl) ⟨635927, by rfl⟩ : syracuseStep 847903 = 1271855) B1271855
theorem B848079 : Blo 846354 848079 := bstep (se 1 (by rfl) ⟨636059, by rfl⟩ : syracuseStep 848079 = 1272119) B1272119
theorem B1274063 : Blo 846354 1274063 := bstep (se 1 (by rfl) ⟨955547, by rfl⟩ : syracuseStep 1274063 = 1911095) B1911095
theorem B4288787 : Blo 846354 4288787 := bstep (se 1 (by rfl) ⟨3216590, by rfl⟩ : syracuseStep 4288787 = 6433181) B6433181
theorem B848199 : Blo 846354 848199 := bstep (se 1 (by rfl) ⟨636149, by rfl⟩ : syracuseStep 848199 = 1272299) B1272299
theorem B1274183 : Blo 846354 1274183 := bstep (se 1 (by rfl) ⟨955637, by rfl⟩ : syracuseStep 1274183 = 1911275) B1911275
theorem B1209115 : Blo 846354 1209115 := bstep (se 1 (by rfl) ⟨906836, by rfl⟩ : syracuseStep 1209115 = 1813673) B1813673
theorem B848667 : Blo 846354 848667 := bstep (se 1 (by rfl) ⟨636500, by rfl⟩ : syracuseStep 848667 = 1273001) B1273001
theorem B1274651 : Blo 846354 1274651 := bstep (se 1 (by rfl) ⟨955988, by rfl⟩ : syracuseStep 1274651 = 1911977) B1911977
theorem B3863539 : Blo 846354 3863539 := bstep (se 1 (by rfl) ⟨2897654, by rfl⟩ : syracuseStep 3863539 = 5795309) B5795309
theorem B848943 : Blo 846354 848943 := bstep (se 1 (by rfl) ⟨636707, by rfl⟩ : syracuseStep 848943 = 1273415) B1273415
theorem B1274927 : Blo 846354 1274927 := bstep (se 1 (by rfl) ⟨956195, by rfl⟩ : syracuseStep 1274927 = 1912391) B1912391
theorem B1274975 : Blo 846354 1274975 := bstep (se 1 (by rfl) ⟨956231, by rfl⟩ : syracuseStep 1274975 = 1912463) B1912463
theorem B1275035 : Blo 846354 1275035 := bstep (se 1 (by rfl) ⟨956276, by rfl⟩ : syracuseStep 1275035 = 1912553) B1912553
theorem B849063 : Blo 846354 849063 := bstep (se 1 (by rfl) ⟨636797, by rfl⟩ : syracuseStep 849063 = 1273595) B1273595
theorem B1275047 : Blo 846354 1275047 := bstep (se 1 (by rfl) ⟨956285, by rfl⟩ : syracuseStep 1275047 = 1912571) B1912571
theorem B34796803 : Blo 846354 34796803 := bstep (se 1 (by rfl) ⟨26097602, by rfl⟩ : syracuseStep 34796803 = 52195205) B52195205
theorem B849511 : Blo 846354 849511 := bstep (se 1 (by rfl) ⟨637133, by rfl⟩ : syracuseStep 849511 = 1274267) B1274267
theorem B2291581 : Blo 846354 2291581 := bstep (se 3 (by rfl) ⟨429671, by rfl⟩ : syracuseStep 2291581 = 859343) B859343
theorem B849791 : Blo 846354 849791 := bstep (se 1 (by rfl) ⟨637343, by rfl⟩ : syracuseStep 849791 = 1274687) B1274687
theorem B849887 : Blo 846354 849887 := bstep (se 1 (by rfl) ⟨637415, by rfl⟩ : syracuseStep 849887 = 1274831) B1274831
theorem B849915 : Blo 846354 849915 := bstep (se 1 (by rfl) ⟨637436, by rfl⟩ : syracuseStep 849915 = 1274873) B1274873
theorem B849947 : Blo 846354 849947 := bstep (se 1 (by rfl) ⟨637460, by rfl⟩ : syracuseStep 849947 = 1274921) B1274921
theorem B849967 : Blo 846354 849967 := bstep (se 1 (by rfl) ⟨637475, by rfl⟩ : syracuseStep 849967 = 1274951) B1274951
theorem B850087 : Blo 846354 850087 := bstep (se 1 (by rfl) ⟨637565, by rfl⟩ : syracuseStep 850087 = 1275131) B1275131
theorem B18381005 : Blo 846354 18381005 := bstep (se 3 (by rfl) ⟨3446438, by rfl⟩ : syracuseStep 18381005 = 6892877) B6892877
theorem B21756275 : Blo 846354 21756275 := bstep (se 1 (by rfl) ⟨16317206, by rfl⟩ : syracuseStep 21756275 = 32634413) B32634413
theorem B7731719 : Blo 846354 7731719 := bstep (se 1 (by rfl) ⟨5798789, by rfl⟩ : syracuseStep 7731719 = 11597579) B11597579
theorem B12384913 : Blo 846354 12384913 := bstep (se 2 (by rfl) ⟨4644342, by rfl⟩ : syracuseStep 12384913 = 9288685) B9288685
theorem B4586321 : Blo 846354 4586321 := bstep (se 2 (by rfl) ⟨1719870, by rfl⟩ : syracuseStep 4586321 = 3439741) B3439741
theorem B4651991 : Blo 846354 4651991 := bstep (se 1 (by rfl) ⟨3488993, by rfl⟩ : syracuseStep 4651991 = 6977987) B6977987
theorem B10452239 : Blo 846354 10452239 := bstep (se 1 (by rfl) ⟨7839179, by rfl⟩ : syracuseStep 10452239 = 15678359) B15678359
theorem B47021633 : Blo 846354 47021633 := bstep (se 2 (by rfl) ⟨17633112, by rfl⟩ : syracuseStep 47021633 = 35266225) B35266225
theorem B377323535 : Blo 846354 377323535 := bstep (se 1 (by rfl) ⟨282992651, by rfl⟩ : syracuseStep 377323535 = 565985303) B565985303
theorem B5439737 : Blo 846354 5439737 := bstep (se 2 (by rfl) ⟨2039901, by rfl⟩ : syracuseStep 5439737 = 4079803) B4079803
theorem B1573663 : Blo 846354 1573663 := bstep (se 1 (by rfl) ⟨1180247, by rfl⟩ : syracuseStep 1573663 = 2360495) B2360495
theorem B13075663 : Blo 846354 13075663 := bstep (se 1 (by rfl) ⟨9806747, by rfl⟩ : syracuseStep 13075663 = 19613495) B19613495
theorem B14714273 : Blo 846354 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B5801719 : Blo 846354 5801719 := bstep (se 1 (by rfl) ⟨4351289, by rfl⟩ : syracuseStep 5801719 = 8702579) B8702579
theorem B5441735 : Blo 846354 5441735 := bstep (se 1 (by rfl) ⟨4081301, by rfl⟩ : syracuseStep 5441735 = 8162603) B8162603
theorem B4295591 : Blo 846354 4295591 := bstep (se 1 (by rfl) ⟨3221693, by rfl⟩ : syracuseStep 4295591 = 6443387) B6443387
theorem B3214799 : Blo 846354 3214799 := bstep (se 1 (by rfl) ⟨2411099, by rfl⟩ : syracuseStep 3214799 = 4822199) B4822199
theorem B19631605 : Blo 846354 19631605 := bstep (se 5 (by rfl) ⟨920231, by rfl⟩ : syracuseStep 19631605 = 1840463) B1840463
theorem B49483439 : Blo 846354 49483439 := bstep (se 1 (by rfl) ⟨37112579, by rfl⟩ : syracuseStep 49483439 = 74225159) B74225159
theorem B954139 : Blo 846354 954139 := bstep (se 1 (by rfl) ⟨715604, by rfl⟩ : syracuseStep 954139 = 1431209) B1431209
theorem B3215771 : Blo 846354 3215771 := bstep (se 1 (by rfl) ⟨2411828, by rfl⟩ : syracuseStep 3215771 = 4823657) B4823657
theorem B24416761 : Blo 846354 24416761 := bstep (se 2 (by rfl) ⟨9156285, by rfl⟩ : syracuseStep 24416761 = 18312571) B18312571
theorem B3052039 : Blo 846354 3052039 := bstep (se 1 (by rfl) ⟨2289029, by rfl⟩ : syracuseStep 3052039 = 4578059) B4578059
theorem B1905209 : Blo 846354 1905209 := bstep (se 2 (by rfl) ⟨714453, by rfl⟩ : syracuseStep 1905209 = 1428907) B1428907
theorem B955111 : Blo 846354 955111 := bstep (se 1 (by rfl) ⟨716333, by rfl⟩ : syracuseStep 955111 = 1432667) B1432667
theorem B4821767 : Blo 846354 4821767 := bstep (se 1 (by rfl) ⟨3616325, by rfl⟩ : syracuseStep 4821767 = 7232651) B7232651
theorem B1610543 : Blo 846354 1610543 := bstep (se 1 (by rfl) ⟨1207907, by rfl⟩ : syracuseStep 1610543 = 2415815) B2415815
theorem B1086535 : Blo 846354 1086535 := bstep (se 1 (by rfl) ⟨814901, by rfl⟩ : syracuseStep 1086535 = 1629803) B1629803
theorem B3052703 : Blo 846354 3052703 := bstep (se 1 (by rfl) ⟨2289527, by rfl⟩ : syracuseStep 3052703 = 4579055) B4579055
theorem B1905929 : Blo 846354 1905929 := bstep (se 2 (by rfl) ⟨714723, by rfl⟩ : syracuseStep 1905929 = 1429447) B1429447
theorem B13079969 : Blo 846354 13079969 := bstep (se 2 (by rfl) ⟨4904988, by rfl⟩ : syracuseStep 13079969 = 9809977) B9809977
theorem B1906667 : Blo 846354 1906667 := bstep (se 1 (by rfl) ⟨1430000, by rfl⟩ : syracuseStep 1906667 = 2860001) B2860001
theorem B4659551 : Blo 846354 4659551 := bstep (se 1 (by rfl) ⟨3494663, by rfl⟩ : syracuseStep 4659551 = 6989327) B6989327
theorem B1612153 : Blo 846354 1612153 := bstep (se 2 (by rfl) ⟨604557, by rfl⟩ : syracuseStep 1612153 = 1209115) B1209115
theorem B3217927 : Blo 846354 3217927 := bstep (se 1 (by rfl) ⟨2413445, by rfl⟩ : syracuseStep 3217927 = 4826891) B4826891
theorem B1907207 : Blo 846354 1907207 := bstep (se 1 (by rfl) ⟨1430405, by rfl⟩ : syracuseStep 1907207 = 2860811) B2860811
theorem B5151385 : Blo 846354 5151385 := bstep (se 2 (by rfl) ⟨1931769, by rfl⟩ : syracuseStep 5151385 = 3863539) B3863539
theorem B2857895 : Blo 846354 2857895 := bstep (se 1 (by rfl) ⟨2143421, by rfl⟩ : syracuseStep 2857895 = 4286843) B4286843
theorem B9673829 : Blo 846354 9673829 := bstep (se 4 (by rfl) ⟨906921, by rfl⟩ : syracuseStep 9673829 = 1813843) B1813843
theorem B3054779 : Blo 846354 3054779 := bstep (se 1 (by rfl) ⟨2291084, by rfl⟩ : syracuseStep 3054779 = 4582169) B4582169
theorem B1908287 : Blo 846354 1908287 := bstep (se 1 (by rfl) ⟨1431215, by rfl⟩ : syracuseStep 1908287 = 2862431) B2862431
theorem B3055441 : Blo 846354 3055441 := bstep (se 2 (by rfl) ⟨1145790, by rfl⟩ : syracuseStep 3055441 = 2291581) B2291581
theorem B1908647 : Blo 846354 1908647 := bstep (se 1 (by rfl) ⟨1431485, by rfl⟩ : syracuseStep 1908647 = 2862971) B2862971
theorem B2858921 : Blo 846354 2858921 := bstep (se 2 (by rfl) ⟨1072095, by rfl⟩ : syracuseStep 2858921 = 2144191) B2144191
theorem B4300937 : Blo 846354 4300937 := bstep (se 2 (by rfl) ⟨1612851, by rfl⟩ : syracuseStep 4300937 = 3225703) B3225703
theorem B2859191 : Blo 846354 2859191 := bstep (se 1 (by rfl) ⟨2144393, by rfl⟩ : syracuseStep 2859191 = 4288787) B4288787
theorem B2859677 : Blo 846354 2859677 := bstep (se 3 (by rfl) ⟨536189, by rfl⟩ : syracuseStep 2859677 = 1072379) B1072379
theorem B1909673 : Blo 846354 1909673 := bstep (se 2 (by rfl) ⟨716127, by rfl⟩ : syracuseStep 1909673 = 1432255) B1432255
theorem B1909943 : Blo 846354 1909943 := bstep (se 1 (by rfl) ⟨1432457, by rfl⟩ : syracuseStep 1909943 = 2864915) B2864915
theorem B2172167 : Blo 846354 2172167 := bstep (se 1 (by rfl) ⟨1629125, by rfl⟩ : syracuseStep 2172167 = 3258251) B3258251
theorem B1910303 : Blo 846354 1910303 := bstep (se 1 (by rfl) ⟨1432727, by rfl⟩ : syracuseStep 1910303 = 2865455) B2865455
theorem B5154479 : Blo 846354 5154479 := bstep (se 1 (by rfl) ⟨3865859, by rfl⟩ : syracuseStep 5154479 = 7731719) B7731719
theorem B3057547 : Blo 846354 3057547 := bstep (se 1 (by rfl) ⟨2293160, by rfl⟩ : syracuseStep 3057547 = 4586321) B4586321
theorem B2861729 : Blo 846354 2861729 := bstep (se 2 (by rfl) ⟨1073148, by rfl⟩ : syracuseStep 2861729 = 2146297) B2146297
theorem B3615931 : Blo 846354 3615931 := bstep (se 1 (by rfl) ⟨2711948, by rfl⟩ : syracuseStep 3615931 = 5423897) B5423897
theorem B6532283 : Blo 846354 6532283 := bstep (se 1 (by rfl) ⟨4899212, by rfl⟩ : syracuseStep 6532283 = 9798425) B9798425
theorem B27897185 : Blo 846354 27897185 := bstep (se 2 (by rfl) ⟨10461444, by rfl⟩ : syracuseStep 27897185 = 20922889) B20922889
theorem B9678203 : Blo 846354 9678203 := bstep (se 1 (by rfl) ⟨7258652, by rfl⟩ : syracuseStep 9678203 = 14517305) B14517305
theorem B1912607 : Blo 846354 1912607 := bstep (se 1 (by rfl) ⟨1434455, by rfl⟩ : syracuseStep 1912607 = 2868911) B2868911
theorem B8171603 : Blo 846354 8171603 := bstep (se 1 (by rfl) ⟨6128702, by rfl⟩ : syracuseStep 8171603 = 12257405) B12257405
theorem B7254143 : Blo 846354 7254143 := bstep (se 1 (by rfl) ⟨5440607, by rfl⟩ : syracuseStep 7254143 = 10881215) B10881215
theorem B4829807 : Blo 846354 4829807 := bstep (se 1 (by rfl) ⟨3622355, by rfl⟩ : syracuseStep 4829807 = 7244711) B7244711
theorem B2863835 : Blo 846354 2863835 := bstep (se 1 (by rfl) ⟨2147876, by rfl⟩ : syracuseStep 2863835 = 4295753) B4295753
theorem B7255169 : Blo 846354 7255169 := bstep (se 2 (by rfl) ⟨2720688, by rfl⟩ : syracuseStep 7255169 = 5441377) B5441377
theorem B2864807 : Blo 846354 2864807 := bstep (se 1 (by rfl) ⟨2148605, by rfl⟩ : syracuseStep 2864807 = 4297211) B4297211
theorem B1357487 : Blo 846354 1357487 := bstep (se 1 (by rfl) ⟨1018115, by rfl⟩ : syracuseStep 1357487 = 2036231) B2036231
theorem B2865131 : Blo 846354 2865131 := bstep (se 1 (by rfl) ⟨2148848, by rfl⟩ : syracuseStep 2865131 = 4297697) B4297697
theorem B6109931 : Blo 846354 6109931 := bstep (se 1 (by rfl) ⟨4582448, by rfl⟩ : syracuseStep 6109931 = 9164897) B9164897
theorem B10894337 : Blo 846354 10894337 := bstep (se 2 (by rfl) ⟨4085376, by rfl⟩ : syracuseStep 10894337 = 8170753) B8170753
theorem B3259739 : Blo 846354 3259739 := bstep (se 1 (by rfl) ⟨2444804, by rfl⟩ : syracuseStep 3259739 = 4889609) B4889609
theorem B4832905 : Blo 846354 4832905 := bstep (se 2 (by rfl) ⟨1812339, by rfl⟩ : syracuseStep 4832905 = 3624679) B3624679
theorem B2867183 : Blo 846354 2867183 := bstep (se 1 (by rfl) ⟨2150387, by rfl⟩ : syracuseStep 2867183 = 4300775) B4300775
theorem B1360127 : Blo 846354 1360127 := bstep (se 1 (by rfl) ⟨1020095, by rfl⟩ : syracuseStep 1360127 = 2040191) B2040191
theorem B12206537 : Blo 846354 12206537 := bstep (se 2 (by rfl) ⟨4577451, by rfl⟩ : syracuseStep 12206537 = 9154903) B9154903
theorem B3228119 : Blo 846354 3228119 := bstep (se 1 (by rfl) ⟨2421089, by rfl⟩ : syracuseStep 3228119 = 4842179) B4842179
theorem B2146783 : Blo 846354 2146783 := bstep (se 1 (by rfl) ⟨1610087, by rfl⟩ : syracuseStep 2146783 = 3220175) B3220175
theorem B3228407 : Blo 846354 3228407 := bstep (se 1 (by rfl) ⟨2421305, by rfl⟩ : syracuseStep 3228407 = 4842611) B4842611
theorem B3622151 : Blo 846354 3622151 := bstep (se 1 (by rfl) ⟨2716613, by rfl⟩ : syracuseStep 3622151 = 5433227) B5433227
theorem B3622391 : Blo 846354 3622391 := bstep (se 1 (by rfl) ⟨2716793, by rfl⟩ : syracuseStep 3622391 = 5433587) B5433587
theorem B21743153 : Blo 846354 21743153 := bstep (se 2 (by rfl) ⟨8153682, by rfl⟩ : syracuseStep 21743153 = 16307365) B16307365
theorem B4835639 : Blo 846354 4835639 := bstep (se 1 (by rfl) ⟨3626729, by rfl⟩ : syracuseStep 4835639 = 7253459) B7253459
theorem B1428347 : Blo 846354 1428347 := bstep (se 1 (by rfl) ⟨1071260, by rfl⟩ : syracuseStep 1428347 = 2142521) B2142521
theorem B6441929 : Blo 846354 6441929 := bstep (se 2 (by rfl) ⟨2415723, by rfl⟩ : syracuseStep 6441929 = 4831447) B4831447
theorem B2149487 : Blo 846354 2149487 := bstep (se 1 (by rfl) ⟨1612115, by rfl⟩ : syracuseStep 2149487 = 3224231) B3224231
theorem B39112429 : Blo 846354 39112429 := bstep (se 3 (by rfl) ⟨7333580, by rfl⟩ : syracuseStep 39112429 = 14667161) B14667161
theorem B14504183 : Blo 846354 14504183 := bstep (se 1 (by rfl) ⟨10878137, by rfl⟩ : syracuseStep 14504183 = 21756275) B21756275
theorem B5427769 : Blo 846354 5427769 := bstep (se 2 (by rfl) ⟨2035413, by rfl⟩ : syracuseStep 5427769 = 4070827) B4070827
theorem B3101327 : Blo 846354 3101327 := bstep (se 1 (by rfl) ⟨2325995, by rfl⟩ : syracuseStep 3101327 = 4651991) B4651991
theorem B6968159 : Blo 846354 6968159 := bstep (se 1 (by rfl) ⟨5226119, by rfl⟩ : syracuseStep 6968159 = 10452239) B10452239
theorem B4903835 : Blo 846354 4903835 := bstep (se 1 (by rfl) ⟨3677876, by rfl⟩ : syracuseStep 4903835 = 7355753) B7355753
theorem B31347755 : Blo 846354 31347755 := bstep (se 1 (by rfl) ⟨23510816, by rfl⟩ : syracuseStep 31347755 = 47021633) B47021633
theorem B1430831 : Blo 846354 1430831 := bstep (se 1 (by rfl) ⟨1073123, by rfl⟩ : syracuseStep 1430831 = 2146247) B2146247
theorem B7231315 : Blo 846354 7231315 := bstep (se 1 (by rfl) ⟨5423486, by rfl⟩ : syracuseStep 7231315 = 10846973) B10846973
theorem B9787805 : Blo 846354 9787805 := bstep (se 3 (by rfl) ⟨1835213, by rfl⟩ : syracuseStep 9787805 = 3670427) B3670427
theorem B6118031 : Blo 846354 6118031 := bstep (se 1 (by rfl) ⟨4588523, by rfl⟩ : syracuseStep 6118031 = 9177047) B9177047
theorem B1433423 : Blo 846354 1433423 := bstep (se 1 (by rfl) ⟨1075067, by rfl⟩ : syracuseStep 1433423 = 2150135) B2150135
theorem B1269755 : Blo 846354 1269755 := bstep (se 1 (by rfl) ⟨952316, by rfl⟩ : syracuseStep 1269755 = 1904633) B1904633
theorem B1269815 : Blo 846354 1269815 := bstep (se 1 (by rfl) ⟨952361, by rfl⟩ : syracuseStep 1269815 = 1904723) B1904723
theorem B27549821 : Blo 846354 27549821 := bstep (se 3 (by rfl) ⟨5165591, by rfl⟩ : syracuseStep 27549821 = 10331183) B10331183
theorem B1269887 : Blo 846354 1269887 := bstep (se 1 (by rfl) ⟨952415, by rfl⟩ : syracuseStep 1269887 = 1904831) B1904831
theorem B1269935 : Blo 846354 1269935 := bstep (se 1 (by rfl) ⟨952451, by rfl⟩ : syracuseStep 1269935 = 1904903) B1904903
theorem B8151839 : Blo 846354 8151839 := bstep (se 1 (by rfl) ⟨6113879, by rfl⟩ : syracuseStep 8151839 = 12227759) B12227759
theorem B1270655 : Blo 846354 1270655 := bstep (se 1 (by rfl) ⟨952991, by rfl⟩ : syracuseStep 1270655 = 1905983) B1905983
theorem B1270727 : Blo 846354 1270727 := bstep (se 1 (by rfl) ⟨953045, by rfl⟩ : syracuseStep 1270727 = 1906091) B1906091
theorem B5792903 : Blo 846354 5792903 := bstep (se 1 (by rfl) ⟨4344677, by rfl⟩ : syracuseStep 5792903 = 8689355) B8689355
theorem B1271087 : Blo 846354 1271087 := bstep (se 1 (by rfl) ⟨953315, by rfl⟩ : syracuseStep 1271087 = 1906631) B1906631
theorem B8709551 : Blo 846354 8709551 := bstep (se 1 (by rfl) ⟨6532163, by rfl⟩ : syracuseStep 8709551 = 13064327) B13064327
theorem B1271327 : Blo 846354 1271327 := bstep (se 1 (by rfl) ⟨953495, by rfl⟩ : syracuseStep 1271327 = 1906991) B1906991
theorem B1272263 : Blo 846354 1272263 := bstep (se 1 (by rfl) ⟨954197, by rfl⟩ : syracuseStep 1272263 = 1908395) B1908395
theorem B846447 : Blo 846354 846447 := bstep (se 1 (by rfl) ⟨634835, by rfl⟩ : syracuseStep 846447 = 1269671) B1269671
theorem B846495 : Blo 846354 846495 := bstep (se 1 (by rfl) ⟨634871, by rfl⟩ : syracuseStep 846495 = 1269743) B1269743
theorem B6187691 : Blo 846354 6187691 := bstep (se 1 (by rfl) ⟨4640768, by rfl⟩ : syracuseStep 6187691 = 9281537) B9281537
theorem B1206991 : Blo 846354 1206991 := bstep (se 1 (by rfl) ⟨905243, by rfl⟩ : syracuseStep 1206991 = 1810487) B1810487
theorem B846575 : Blo 846354 846575 := bstep (se 1 (by rfl) ⟨634931, by rfl⟩ : syracuseStep 846575 = 1269863) B1269863
theorem B1075999 : Blo 846354 1075999 := bstep (se 1 (by rfl) ⟨806999, by rfl⟩ : syracuseStep 1075999 = 1613999) B1613999
theorem B1272623 : Blo 846354 1272623 := bstep (se 1 (by rfl) ⟨954467, by rfl⟩ : syracuseStep 1272623 = 1908935) B1908935
theorem B846663 : Blo 846354 846663 := bstep (se 1 (by rfl) ⟨634997, by rfl⟩ : syracuseStep 846663 = 1269995) B1269995
theorem B846703 : Blo 846354 846703 := bstep (se 1 (by rfl) ⟨635027, by rfl⟩ : syracuseStep 846703 = 1270055) B1270055
theorem B1272743 : Blo 846354 1272743 := bstep (se 1 (by rfl) ⟨954557, by rfl⟩ : syracuseStep 1272743 = 1909115) B1909115
theorem B1272923 : Blo 846354 1272923 := bstep (se 1 (by rfl) ⟨954692, by rfl⟩ : syracuseStep 1272923 = 1909385) B1909385
theorem B847003 : Blo 846354 847003 := bstep (se 1 (by rfl) ⟨635252, by rfl⟩ : syracuseStep 847003 = 1270505) B1270505
theorem B847263 : Blo 846354 847263 := bstep (se 1 (by rfl) ⟨635447, by rfl⟩ : syracuseStep 847263 = 1270895) B1270895
theorem B847343 : Blo 846354 847343 := bstep (se 1 (by rfl) ⟨635507, by rfl⟩ : syracuseStep 847343 = 1271015) B1271015
theorem B847387 : Blo 846354 847387 := bstep (se 1 (by rfl) ⟨635540, by rfl⟩ : syracuseStep 847387 = 1271081) B1271081
theorem B1273511 : Blo 846354 1273511 := bstep (se 1 (by rfl) ⟨955133, by rfl⟩ : syracuseStep 1273511 = 1910267) B1910267
theorem B847567 : Blo 846354 847567 := bstep (se 1 (by rfl) ⟨635675, by rfl⟩ : syracuseStep 847567 = 1271351) B1271351
theorem B1273631 : Blo 846354 1273631 := bstep (se 1 (by rfl) ⟨955223, by rfl⟩ : syracuseStep 1273631 = 1910447) B1910447
theorem B1273691 : Blo 846354 1273691 := bstep (se 1 (by rfl) ⟨955268, by rfl⟩ : syracuseStep 1273691 = 1910537) B1910537
theorem B847783 : Blo 846354 847783 := bstep (se 1 (by rfl) ⟨635837, by rfl⟩ : syracuseStep 847783 = 1271675) B1271675
theorem B847807 : Blo 846354 847807 := bstep (se 1 (by rfl) ⟨635855, by rfl⟩ : syracuseStep 847807 = 1271711) B1271711
theorem B1273835 : Blo 846354 1273835 := bstep (se 1 (by rfl) ⟨955376, by rfl⟩ : syracuseStep 1273835 = 1910753) B1910753
theorem B8155187 : Blo 846354 8155187 := bstep (se 1 (by rfl) ⟨6116390, by rfl⟩ : syracuseStep 8155187 = 12232781) B12232781
theorem B2289755 : Blo 846354 2289755 := bstep (se 1 (by rfl) ⟨1717316, by rfl⟩ : syracuseStep 2289755 = 3434633) B3434633
theorem B847963 : Blo 846354 847963 := bstep (se 1 (by rfl) ⟨635972, by rfl⟩ : syracuseStep 847963 = 1271945) B1271945
theorem B848063 : Blo 846354 848063 := bstep (se 1 (by rfl) ⟨636047, by rfl⟩ : syracuseStep 848063 = 1272095) B1272095
theorem B848095 : Blo 846354 848095 := bstep (se 1 (by rfl) ⟨636071, by rfl⟩ : syracuseStep 848095 = 1272143) B1272143
theorem B1274111 : Blo 846354 1274111 := bstep (se 1 (by rfl) ⟨955583, by rfl⟩ : syracuseStep 1274111 = 1911167) B1911167
theorem B848155 : Blo 846354 848155 := bstep (se 1 (by rfl) ⟨636116, by rfl⟩ : syracuseStep 848155 = 1272233) B1272233
theorem B46395737 : Blo 846354 46395737 := bstep (se 2 (by rfl) ⟨17398401, by rfl⟩ : syracuseStep 46395737 = 34796803) B34796803
theorem B2421191 : Blo 846354 2421191 := bstep (se 1 (by rfl) ⟨1815893, by rfl⟩ : syracuseStep 2421191 = 3631787) B3631787
theorem B5042639 : Blo 846354 5042639 := bstep (se 1 (by rfl) ⟨3781979, by rfl⟩ : syracuseStep 5042639 = 7563959) B7563959
theorem B848411 : Blo 846354 848411 := bstep (se 1 (by rfl) ⟨636308, by rfl⟩ : syracuseStep 848411 = 1272617) B1272617
theorem B1274423 : Blo 846354 1274423 := bstep (se 1 (by rfl) ⟨955817, by rfl⟩ : syracuseStep 1274423 = 1911635) B1911635
theorem B13759085 : Blo 846354 13759085 := bstep (se 3 (by rfl) ⟨2579828, by rfl⟩ : syracuseStep 13759085 = 5159657) B5159657
theorem B848551 : Blo 846354 848551 := bstep (se 1 (by rfl) ⟨636413, by rfl⟩ : syracuseStep 848551 = 1272827) B1272827
theorem B1274537 : Blo 846354 1274537 := bstep (se 2 (by rfl) ⟨477951, by rfl⟩ : syracuseStep 1274537 = 955903) B955903
theorem B848591 : Blo 846354 848591 := bstep (se 1 (by rfl) ⟨636443, by rfl⟩ : syracuseStep 848591 = 1272887) B1272887
theorem B11629271 : Blo 846354 11629271 := bstep (se 1 (by rfl) ⟨8721953, by rfl⟩ : syracuseStep 11629271 = 17443907) B17443907
theorem B7238423 : Blo 846354 7238423 := bstep (se 1 (by rfl) ⟨5428817, by rfl⟩ : syracuseStep 7238423 = 10857635) B10857635
theorem B1864475 : Blo 846354 1864475 := bstep (se 1 (by rfl) ⟨1398356, by rfl⟩ : syracuseStep 1864475 = 2796713) B2796713
theorem B848671 : Blo 846354 848671 := bstep (se 1 (by rfl) ⟨636503, by rfl⟩ : syracuseStep 848671 = 1273007) B1273007
theorem B1274663 : Blo 846354 1274663 := bstep (se 1 (by rfl) ⟨955997, by rfl⟩ : syracuseStep 1274663 = 1911995) B1911995
theorem B848711 : Blo 846354 848711 := bstep (se 1 (by rfl) ⟨636533, by rfl⟩ : syracuseStep 848711 = 1273067) B1273067
theorem B1274783 : Blo 846354 1274783 := bstep (se 1 (by rfl) ⟨956087, by rfl⟩ : syracuseStep 1274783 = 1912175) B1912175
theorem B17429519 : Blo 846354 17429519 := bstep (se 1 (by rfl) ⟨13072139, by rfl⟩ : syracuseStep 17429519 = 26144279) B26144279
theorem B849151 : Blo 846354 849151 := bstep (se 1 (by rfl) ⟨636863, by rfl⟩ : syracuseStep 849151 = 1273727) B1273727
theorem B1275263 : Blo 846354 1275263 := bstep (se 1 (by rfl) ⟨956447, by rfl⟩ : syracuseStep 1275263 = 1912895) B1912895
theorem B849375 : Blo 846354 849375 := bstep (se 1 (by rfl) ⟨637031, by rfl⟩ : syracuseStep 849375 = 1274063) B1274063
theorem B849455 : Blo 846354 849455 := bstep (se 1 (by rfl) ⟨637091, by rfl⟩ : syracuseStep 849455 = 1274183) B1274183
theorem B849767 : Blo 846354 849767 := bstep (se 1 (by rfl) ⟨637325, by rfl⟩ : syracuseStep 849767 = 1274651) B1274651
theorem B849951 : Blo 846354 849951 := bstep (se 1 (by rfl) ⟨637463, by rfl⟩ : syracuseStep 849951 = 1274927) B1274927
theorem B849983 : Blo 846354 849983 := bstep (se 1 (by rfl) ⟨637487, by rfl⟩ : syracuseStep 849983 = 1274975) B1274975
theorem B850023 : Blo 846354 850023 := bstep (se 1 (by rfl) ⟨637517, by rfl⟩ : syracuseStep 850023 = 1275035) B1275035
theorem B850031 : Blo 846354 850031 := bstep (se 1 (by rfl) ⟨637523, by rfl⟩ : syracuseStep 850031 = 1275047) B1275047
theorem B16513217 : Blo 846354 16513217 := bstep (se 2 (by rfl) ⟨6192456, by rfl⟩ : syracuseStep 16513217 = 12384913) B12384913
theorem B1210727 : Blo 846354 1210727 := bstep (se 1 (by rfl) ⟨908045, by rfl⟩ : syracuseStep 1210727 = 1816091) B1816091
theorem B12254003 : Blo 846354 12254003 := bstep (se 1 (by rfl) ⟨9190502, by rfl⟩ : syracuseStep 12254003 = 18381005) B18381005
theorem B2063369 : Blo 846354 2063369 := bstep (se 2 (by rfl) ⟨773763, by rfl⟩ : syracuseStep 2063369 = 1547527) B1547527
theorem B7241021 : Blo 846354 7241021 := bstep (se 3 (by rfl) ⟨1357691, by rfl⟩ : syracuseStep 7241021 = 2715383) B2715383
theorem B3440033 : Blo 846354 3440033 := bstep (se 2 (by rfl) ⟨1290012, by rfl⟩ : syracuseStep 3440033 = 2580025) B2580025
theorem B2098217 : Blo 846354 2098217 := bstep (se 2 (by rfl) ⟨786831, by rfl⟩ : syracuseStep 2098217 = 1573663) B1573663
theorem B6456509 : Blo 846354 6456509 := bstep (se 3 (by rfl) ⟨1210595, by rfl⟩ : syracuseStep 6456509 = 2421191) B2421191
theorem B17434217 : Blo 846354 17434217 := bstep (se 2 (by rfl) ⟨6537831, by rfl⟩ : syracuseStep 17434217 = 13075663) B13075663
theorem B952231 : Blo 846354 952231 := bstep (se 1 (by rfl) ⟨714173, by rfl⟩ : syracuseStep 952231 = 1428347) B1428347
theorem B4294619 : Blo 846354 4294619 := bstep (se 1 (by rfl) ⟨3220964, by rfl⟩ : syracuseStep 4294619 = 6441929) B6441929
theorem B4294781 : Blo 846354 4294781 := bstep (se 3 (by rfl) ⟨805271, by rfl⟩ : syracuseStep 4294781 = 1610543) B1610543
theorem B7735625 : Blo 846354 7735625 := bstep (se 2 (by rfl) ⟨2900859, by rfl⟩ : syracuseStep 7735625 = 5801719) B5801719
theorem B13076893 : Blo 846354 13076893 := bstep (se 3 (by rfl) ⟨2451917, by rfl⟩ : syracuseStep 13076893 = 4903835) B4903835
theorem B9669455 : Blo 846354 9669455 := bstep (se 1 (by rfl) ⟨7252091, by rfl⟩ : syracuseStep 9669455 = 14504183) B14504183
theorem B2067551 : Blo 846354 2067551 := bstep (se 1 (by rfl) ⟨1550663, by rfl⟩ : syracuseStep 2067551 = 3101327) B3101327
theorem B3214511 : Blo 846354 3214511 := bstep (se 1 (by rfl) ⟨2410883, by rfl⟩ : syracuseStep 3214511 = 4821767) B4821767
theorem B2035135 : Blo 846354 2035135 := bstep (se 1 (by rfl) ⟨1526351, by rfl⟩ : syracuseStep 2035135 = 3052703) B3052703
theorem B953887 : Blo 846354 953887 := bstep (se 1 (by rfl) ⟨715415, by rfl⟩ : syracuseStep 953887 = 1430831) B1430831
theorem B1609321 : Blo 846354 1609321 := bstep (se 2 (by rfl) ⟨603495, by rfl⟩ : syracuseStep 1609321 = 1206991) B1206991
theorem B8719979 : Blo 846354 8719979 := bstep (se 1 (by rfl) ⟨6539984, by rfl⟩ : syracuseStep 8719979 = 13079969) B13079969
theorem B4821241 : Blo 846354 4821241 := bstep (se 2 (by rfl) ⟨1807965, by rfl⟩ : syracuseStep 4821241 = 3615931) B3615931
theorem B6525203 : Blo 846354 6525203 := bstep (se 1 (by rfl) ⟨4893902, by rfl⟩ : syracuseStep 6525203 = 9787805) B9787805
theorem B1905263 : Blo 846354 1905263 := bstep (se 1 (by rfl) ⟨1428947, by rfl⟩ : syracuseStep 1905263 = 2857895) B2857895
theorem B2036519 : Blo 846354 2036519 := bstep (se 1 (by rfl) ⟨1527389, by rfl⟩ : syracuseStep 2036519 = 3054779) B3054779
theorem B955615 : Blo 846354 955615 := bstep (se 1 (by rfl) ⟨716711, by rfl⟩ : syracuseStep 955615 = 1433423) B1433423
theorem B1905947 : Blo 846354 1905947 := bstep (se 1 (by rfl) ⟨1429460, by rfl⟩ : syracuseStep 1905947 = 2858921) B2858921
theorem B1906127 : Blo 846354 1906127 := bstep (se 1 (by rfl) ⟨1429595, by rfl⟩ : syracuseStep 1906127 = 2859191) B2859191
theorem B1906451 : Blo 846354 1906451 := bstep (se 1 (by rfl) ⟨1429838, by rfl⟩ : syracuseStep 1906451 = 2859677) B2859677
theorem B4069385 : Blo 846354 4069385 := bstep (se 2 (by rfl) ⟨1526019, by rfl⟩ : syracuseStep 4069385 = 3052039) B3052039
theorem B1448111 : Blo 846354 1448111 := bstep (se 1 (by rfl) ⟨1086083, by rfl⟩ : syracuseStep 1448111 = 2172167) B2172167
theorem B5806367 : Blo 846354 5806367 := bstep (se 1 (by rfl) ⟨4354775, by rfl⟩ : syracuseStep 5806367 = 8709551) B8709551
theorem B1448713 : Blo 846354 1448713 := bstep (se 2 (by rfl) ⟨543267, by rfl⟩ : syracuseStep 1448713 = 1086535) B1086535
theorem B1907819 : Blo 846354 1907819 := bstep (se 1 (by rfl) ⟨1430864, by rfl⟩ : syracuseStep 1907819 = 2861729) B2861729
theorem B16293149 : Blo 846354 16293149 := bstep (se 3 (by rfl) ⟨3054965, by rfl⟩ : syracuseStep 16293149 = 6109931) B6109931
theorem B9641753 : Blo 846354 9641753 := bstep (se 2 (by rfl) ⟨3615657, by rfl⟩ : syracuseStep 9641753 = 7231315) B7231315
theorem B5447735 : Blo 846354 5447735 := bstep (se 1 (by rfl) ⟨4085801, by rfl⟩ : syracuseStep 5447735 = 8171603) B8171603
theorem B3219871 : Blo 846354 3219871 := bstep (se 1 (by rfl) ⟨2414903, by rfl⟩ : syracuseStep 3219871 = 4829807) B4829807
theorem B1909223 : Blo 846354 1909223 := bstep (se 1 (by rfl) ⟨1431917, by rfl⟩ : syracuseStep 1909223 = 2863835) B2863835
theorem B4825615 : Blo 846354 4825615 := bstep (se 1 (by rfl) ⟨3619211, by rfl⟩ : syracuseStep 4825615 = 7238423) B7238423
theorem B1909871 : Blo 846354 1909871 := bstep (se 1 (by rfl) ⟨1432403, by rfl⟩ : syracuseStep 1909871 = 2864807) B2864807
theorem B1910087 : Blo 846354 1910087 := bstep (se 1 (by rfl) ⟨1432565, by rfl⟩ : syracuseStep 1910087 = 2865131) B2865131
theorem B8169335 : Blo 846354 8169335 := bstep (se 1 (by rfl) ⟨6127001, by rfl⟩ : syracuseStep 8169335 = 12254003) B12254003
theorem B4827347 : Blo 846354 4827347 := bstep (se 1 (by rfl) ⟨3620510, by rfl⟩ : syracuseStep 4827347 = 7241021) B7241021
theorem B2173159 : Blo 846354 2173159 := bstep (se 1 (by rfl) ⟨1629869, by rfl⟩ : syracuseStep 2173159 = 3259739) B3259739
theorem B4073921 : Blo 846354 4073921 := bstep (se 2 (by rfl) ⟨1527720, by rfl⟩ : syracuseStep 4073921 = 3055441) B3055441
theorem B1911455 : Blo 846354 1911455 := bstep (se 1 (by rfl) ⟨1433591, by rfl⟩ : syracuseStep 1911455 = 2867183) B2867183
theorem B6106013 : Blo 846354 6106013 := bstep (se 3 (by rfl) ⟨1144877, by rfl⟩ : syracuseStep 6106013 = 2289755) B2289755
theorem B8137691 : Blo 846354 8137691 := bstep (se 1 (by rfl) ⟨6103268, by rfl⟩ : syracuseStep 8137691 = 12206537) B12206537
theorem B2862377 : Blo 846354 2862377 := bstep (se 2 (by rfl) ⟨1073391, by rfl⟩ : syracuseStep 2862377 = 2146783) B2146783
theorem B9809515 : Blo 846354 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B14495435 : Blo 846354 14495435 := bstep (se 1 (by rfl) ⟨10871576, by rfl⟩ : syracuseStep 14495435 = 21743153) B21743153
theorem B13447037 : Blo 846354 13447037 := bstep (se 3 (by rfl) ⟨2521319, by rfl⟩ : syracuseStep 13447037 = 5042639) B5042639
theorem B3223759 : Blo 846354 3223759 := bstep (se 1 (by rfl) ⟨2417819, by rfl⟩ : syracuseStep 3223759 = 4835639) B4835639
theorem B2863727 : Blo 846354 2863727 := bstep (se 1 (by rfl) ⟨2147795, by rfl⟩ : syracuseStep 2863727 = 4295591) B4295591
theorem B2143199 : Blo 846354 2143199 := bstep (se 1 (by rfl) ⟨1607399, by rfl⟩ : syracuseStep 2143199 = 3214799) B3214799
theorem B4076729 : Blo 846354 4076729 := bstep (se 2 (by rfl) ⟨1528773, by rfl⟩ : syracuseStep 4076729 = 3057547) B3057547
theorem B46478717 : Blo 846354 46478717 := bstep (se 3 (by rfl) ⟨8714759, by rfl⟩ : syracuseStep 46478717 = 17429519) B17429519
theorem B2143847 : Blo 846354 2143847 := bstep (se 1 (by rfl) ⟨1607885, by rfl⟩ : syracuseStep 2143847 = 3215771) B3215771
theorem B4078687 : Blo 846354 4078687 := bstep (se 1 (by rfl) ⟨3059015, by rfl⟩ : syracuseStep 4078687 = 6118031) B6118031
theorem B52149905 : Blo 846354 52149905 := bstep (se 2 (by rfl) ⟨19556214, by rfl⟩ : syracuseStep 52149905 = 39112429) B39112429
theorem B18366547 : Blo 846354 18366547 := bstep (se 1 (by rfl) ⟨13774910, by rfl⟩ : syracuseStep 18366547 = 27549821) B27549821
theorem B2867291 : Blo 846354 2867291 := bstep (se 1 (by rfl) ⟨2150468, by rfl⟩ : syracuseStep 2867291 = 4300937) B4300937
theorem B32555681 : Blo 846354 32555681 := bstep (se 2 (by rfl) ⟨12208380, by rfl⟩ : syracuseStep 32555681 = 24416761) B24416761
theorem B3228605 : Blo 846354 3228605 := bstep (se 3 (by rfl) ⟨605363, by rfl⟩ : syracuseStep 3228605 = 1210727) B1210727
theorem B18598123 : Blo 846354 18598123 := bstep (se 1 (by rfl) ⟨13948592, by rfl⟩ : syracuseStep 18598123 = 27897185) B27897185
theorem B4836095 : Blo 846354 4836095 := bstep (se 1 (by rfl) ⟨3627071, by rfl⟩ : syracuseStep 4836095 = 7254143) B7254143
theorem B7752847 : Blo 846354 7752847 := bstep (se 1 (by rfl) ⟨5814635, by rfl⟩ : syracuseStep 7752847 = 11629271) B11629271
theorem B17419421 : Blo 846354 17419421 := bstep (se 3 (by rfl) ⟨3266141, by rfl⟩ : syracuseStep 17419421 = 6532283) B6532283
theorem B2149537 : Blo 846354 2149537 := bstep (se 2 (by rfl) ⟨806076, by rfl⟩ : syracuseStep 2149537 = 1612153) B1612153
theorem B4836779 : Blo 846354 4836779 := bstep (se 1 (by rfl) ⟨3627584, by rfl⟩ : syracuseStep 4836779 = 7255169) B7255169
theorem B6868513 : Blo 846354 6868513 := bstep (se 2 (by rfl) ⟨2575692, by rfl⟩ : syracuseStep 6868513 = 5151385) B5151385
theorem B904991 : Blo 846354 904991 := bstep (se 1 (by rfl) ⟨678743, by rfl⟩ : syracuseStep 904991 = 1357487) B1357487
theorem B7262891 : Blo 846354 7262891 := bstep (se 1 (by rfl) ⟨5447168, by rfl⟩ : syracuseStep 7262891 = 10894337) B10894337
theorem B6443873 : Blo 846354 6443873 := bstep (se 2 (by rfl) ⟨2416452, by rfl⟩ : syracuseStep 6443873 = 4832905) B4832905
theorem B251549023 : Blo 846354 251549023 := bstep (se 1 (by rfl) ⟨188661767, by rfl⟩ : syracuseStep 251549023 = 377323535) B377323535
theorem B3626491 : Blo 846354 3626491 := bstep (se 1 (by rfl) ⟨2719868, by rfl⟩ : syracuseStep 3626491 = 5439737) B5439737
theorem B906751 : Blo 846354 906751 := bstep (se 1 (by rfl) ⟨680063, by rfl⟩ : syracuseStep 906751 = 1360127) B1360127
theorem B2152079 : Blo 846354 2152079 := bstep (se 1 (by rfl) ⟨1614059, by rfl⟩ : syracuseStep 2152079 = 3228119) B3228119
theorem B2152271 : Blo 846354 2152271 := bstep (se 1 (by rfl) ⟨1614203, by rfl⟩ : syracuseStep 2152271 = 3228407) B3228407
theorem B2414767 : Blo 846354 2414767 := bstep (se 1 (by rfl) ⟨1811075, by rfl⟩ : syracuseStep 2414767 = 3622151) B3622151
theorem B2414927 : Blo 846354 2414927 := bstep (se 1 (by rfl) ⟨1811195, by rfl⟩ : syracuseStep 2414927 = 3622391) B3622391
theorem B3627823 : Blo 846354 3627823 := bstep (se 1 (by rfl) ⟨2720867, by rfl⟩ : syracuseStep 3627823 = 5441735) B5441735
theorem B1432991 : Blo 846354 1432991 := bstep (se 1 (by rfl) ⟨1074743, by rfl⟩ : syracuseStep 1432991 = 2149487) B2149487
theorem B32988959 : Blo 846354 32988959 := bstep (se 1 (by rfl) ⟨24741719, by rfl⟩ : syracuseStep 32988959 = 49483439) B49483439
theorem B1270139 : Blo 846354 1270139 := bstep (se 1 (by rfl) ⟨952604, by rfl⟩ : syracuseStep 1270139 = 1905209) B1905209
theorem B4645439 : Blo 846354 4645439 := bstep (se 1 (by rfl) ⟨3484079, by rfl⟩ : syracuseStep 4645439 = 6968159) B6968159
theorem B20898503 : Blo 846354 20898503 := bstep (se 1 (by rfl) ⟨15673877, by rfl⟩ : syracuseStep 20898503 = 31347755) B31347755
theorem B1270619 : Blo 846354 1270619 := bstep (se 1 (by rfl) ⟨952964, by rfl⟩ : syracuseStep 1270619 = 1905929) B1905929
theorem B1434665 : Blo 846354 1434665 := bstep (se 2 (by rfl) ⟨537999, by rfl⟩ : syracuseStep 1434665 = 1075999) B1075999
theorem B1271111 : Blo 846354 1271111 := bstep (se 1 (by rfl) ⟨953333, by rfl⟩ : syracuseStep 1271111 = 1906667) B1906667
theorem B3106367 : Blo 846354 3106367 := bstep (se 1 (by rfl) ⟨2329775, by rfl⟩ : syracuseStep 3106367 = 4659551) B4659551
theorem B1271471 : Blo 846354 1271471 := bstep (se 1 (by rfl) ⟨953603, by rfl⟩ : syracuseStep 1271471 = 1907207) B1907207
theorem B26175473 : Blo 846354 26175473 := bstep (se 2 (by rfl) ⟨9815802, by rfl⟩ : syracuseStep 26175473 = 19631605) B19631605
theorem B6449219 : Blo 846354 6449219 := bstep (se 1 (by rfl) ⟨4836914, by rfl⟩ : syracuseStep 6449219 = 9673829) B9673829
theorem B1272185 : Blo 846354 1272185 := bstep (se 2 (by rfl) ⟨477069, by rfl⟩ : syracuseStep 1272185 = 954139) B954139
theorem B1272191 : Blo 846354 1272191 := bstep (se 1 (by rfl) ⟨954143, by rfl⟩ : syracuseStep 1272191 = 1908287) B1908287
theorem B1272431 : Blo 846354 1272431 := bstep (se 1 (by rfl) ⟨954323, by rfl⟩ : syracuseStep 1272431 = 1908647) B1908647
theorem B846503 : Blo 846354 846503 := bstep (se 1 (by rfl) ⟨634877, by rfl⟩ : syracuseStep 846503 = 1269755) B1269755
theorem B846543 : Blo 846354 846543 := bstep (se 1 (by rfl) ⟨634907, by rfl⟩ : syracuseStep 846543 = 1269815) B1269815
theorem B846591 : Blo 846354 846591 := bstep (se 1 (by rfl) ⟨634943, by rfl⟩ : syracuseStep 846591 = 1269887) B1269887
theorem B846623 : Blo 846354 846623 := bstep (se 1 (by rfl) ⟨634967, by rfl⟩ : syracuseStep 846623 = 1269935) B1269935
theorem B5434559 : Blo 846354 5434559 := bstep (se 1 (by rfl) ⟨4075919, by rfl⟩ : syracuseStep 5434559 = 8151839) B8151839
theorem B847103 : Blo 846354 847103 := bstep (se 1 (by rfl) ⟨635327, by rfl⟩ : syracuseStep 847103 = 1270655) B1270655
theorem B1273115 : Blo 846354 1273115 := bstep (se 1 (by rfl) ⟨954836, by rfl⟩ : syracuseStep 1273115 = 1909673) B1909673
theorem B847151 : Blo 846354 847151 := bstep (se 1 (by rfl) ⟨635363, by rfl⟩ : syracuseStep 847151 = 1270727) B1270727
theorem B7237025 : Blo 846354 7237025 := bstep (se 2 (by rfl) ⟨2713884, by rfl⟩ : syracuseStep 7237025 = 5427769) B5427769
theorem B3861935 : Blo 846354 3861935 := bstep (se 1 (by rfl) ⟨2896451, by rfl⟩ : syracuseStep 3861935 = 5792903) B5792903
theorem B1273295 : Blo 846354 1273295 := bstep (se 1 (by rfl) ⟨954971, by rfl⟩ : syracuseStep 1273295 = 1909943) B1909943
theorem B847391 : Blo 846354 847391 := bstep (se 1 (by rfl) ⟨635543, by rfl⟩ : syracuseStep 847391 = 1271087) B1271087
theorem B1273481 : Blo 846354 1273481 := bstep (se 2 (by rfl) ⟨477555, by rfl⟩ : syracuseStep 1273481 = 955111) B955111
theorem B847551 : Blo 846354 847551 := bstep (se 1 (by rfl) ⟨635663, by rfl⟩ : syracuseStep 847551 = 1271327) B1271327
theorem B1273535 : Blo 846354 1273535 := bstep (se 1 (by rfl) ⟨955151, by rfl⟩ : syracuseStep 1273535 = 1910303) B1910303
theorem B3436319 : Blo 846354 3436319 := bstep (se 1 (by rfl) ⟨2577239, by rfl⟩ : syracuseStep 3436319 = 5154479) B5154479
theorem B848175 : Blo 846354 848175 := bstep (se 1 (by rfl) ⟨636131, by rfl⟩ : syracuseStep 848175 = 1272263) B1272263
theorem B4125127 : Blo 846354 4125127 := bstep (se 1 (by rfl) ⟨3093845, by rfl⟩ : syracuseStep 4125127 = 6187691) B6187691
theorem B848415 : Blo 846354 848415 := bstep (se 1 (by rfl) ⟨636311, by rfl⟩ : syracuseStep 848415 = 1272623) B1272623
theorem B848495 : Blo 846354 848495 := bstep (se 1 (by rfl) ⟨636371, by rfl⟩ : syracuseStep 848495 = 1272743) B1272743
theorem B848615 : Blo 846354 848615 := bstep (se 1 (by rfl) ⟨636461, by rfl⟩ : syracuseStep 848615 = 1272923) B1272923
theorem B6452135 : Blo 846354 6452135 := bstep (se 1 (by rfl) ⟨4839101, by rfl⟩ : syracuseStep 6452135 = 9678203) B9678203
theorem B849007 : Blo 846354 849007 := bstep (se 1 (by rfl) ⟨636755, by rfl⟩ : syracuseStep 849007 = 1273511) B1273511
theorem B849087 : Blo 846354 849087 := bstep (se 1 (by rfl) ⟨636815, by rfl⟩ : syracuseStep 849087 = 1273631) B1273631
theorem B1275071 : Blo 846354 1275071 := bstep (se 1 (by rfl) ⟨956303, by rfl⟩ : syracuseStep 1275071 = 1912607) B1912607
theorem B849127 : Blo 846354 849127 := bstep (se 1 (by rfl) ⟨636845, by rfl⟩ : syracuseStep 849127 = 1273691) B1273691
theorem B849223 : Blo 846354 849223 := bstep (se 1 (by rfl) ⟨636917, by rfl⟩ : syracuseStep 849223 = 1273835) B1273835
theorem B5436791 : Blo 846354 5436791 := bstep (se 1 (by rfl) ⟨4077593, by rfl⟩ : syracuseStep 5436791 = 8155187) B8155187
theorem B849407 : Blo 846354 849407 := bstep (se 1 (by rfl) ⟨637055, by rfl⟩ : syracuseStep 849407 = 1274111) B1274111
theorem B30930491 : Blo 846354 30930491 := bstep (se 1 (by rfl) ⟨23197868, by rfl⟩ : syracuseStep 30930491 = 46395737) B46395737
theorem B849615 : Blo 846354 849615 := bstep (se 1 (by rfl) ⟨637211, by rfl⟩ : syracuseStep 849615 = 1274423) B1274423
theorem B9172723 : Blo 846354 9172723 := bstep (se 1 (by rfl) ⟨6879542, by rfl⟩ : syracuseStep 9172723 = 13759085) B13759085
theorem B849691 : Blo 846354 849691 := bstep (se 1 (by rfl) ⟨637268, by rfl⟩ : syracuseStep 849691 = 1274537) B1274537
theorem B1242983 : Blo 846354 1242983 := bstep (se 1 (by rfl) ⟨932237, by rfl⟩ : syracuseStep 1242983 = 1864475) B1864475
theorem B849775 : Blo 846354 849775 := bstep (se 1 (by rfl) ⟨637331, by rfl⟩ : syracuseStep 849775 = 1274663) B1274663
theorem B849855 : Blo 846354 849855 := bstep (se 1 (by rfl) ⟨637391, by rfl⟩ : syracuseStep 849855 = 1274783) B1274783
theorem B4290569 : Blo 846354 4290569 := bstep (se 2 (by rfl) ⟨1608963, by rfl⟩ : syracuseStep 4290569 = 3217927) B3217927
theorem B850175 : Blo 846354 850175 := bstep (se 1 (by rfl) ⟨637631, by rfl⟩ : syracuseStep 850175 = 1275263) B1275263
theorem B11008811 : Blo 846354 11008811 := bstep (se 1 (by rfl) ⟨8256608, by rfl⟩ : syracuseStep 11008811 = 16513217) B16513217
theorem B1375579 : Blo 846354 1375579 := bstep (se 1 (by rfl) ⟨1031684, by rfl⟩ : syracuseStep 1375579 = 2063369) B2063369
theorem B2293355 : Blo 846354 2293355 := bstep (se 1 (by rfl) ⟨1720016, by rfl⟩ : syracuseStep 2293355 = 3440033) B3440033
theorem B4293161 : Blo 846354 4293161 := bstep (se 2 (by rfl) ⟨1609935, by rfl⟩ : syracuseStep 4293161 = 3219871) B3219871
theorem B1378367 : Blo 846354 1378367 := bstep (se 1 (by rfl) ⟨1033775, by rfl⟩ : syracuseStep 1378367 = 2067551) B2067551
theorem B69602165 : Blo 846354 69602165 := bstep (se 5 (by rfl) ⟨3262601, by rfl⟩ : syracuseStep 69602165 = 6525203) B6525203
theorem B17435857 : Blo 846354 17435857 := bstep (se 2 (by rfl) ⟨6538446, by rfl⟩ : syracuseStep 17435857 = 13076893) B13076893
theorem B4295915 : Blo 846354 4295915 := bstep (se 1 (by rfl) ⟨3221936, by rfl⟩ : syracuseStep 4295915 = 6443873) B6443873
theorem B3870911 : Blo 846354 3870911 := bstep (se 1 (by rfl) ⟨2903183, by rfl⟩ : syracuseStep 3870911 = 5806367) B5806367
theorem B1609951 : Blo 846354 1609951 := bstep (se 1 (by rfl) ⟨1207463, by rfl⟩ : syracuseStep 1609951 = 2414927) B2414927
theorem B3314621 : Blo 846354 3314621 := bstep (se 3 (by rfl) ⟨621491, by rfl⟩ : syracuseStep 3314621 = 1242983) B1242983
theorem B955327 : Blo 846354 955327 := bstep (se 1 (by rfl) ⟨716495, by rfl⟩ : syracuseStep 955327 = 1432991) B1432991
theorem B6427835 : Blo 846354 6427835 := bstep (se 1 (by rfl) ⟨4820876, by rfl⟩ : syracuseStep 6427835 = 9641753) B9641753
theorem B21992639 : Blo 846354 21992639 := bstep (se 1 (by rfl) ⟨16494479, by rfl⟩ : syracuseStep 21992639 = 32988959) B32988959
theorem B4298345 : Blo 846354 4298345 := bstep (se 2 (by rfl) ⟨1611879, by rfl⟩ : syracuseStep 4298345 = 3223759) B3223759
theorem B6428321 : Blo 846354 6428321 := bstep (se 2 (by rfl) ⟨2410620, by rfl⟩ : syracuseStep 6428321 = 4821241) B4821241
theorem B13932335 : Blo 846354 13932335 := bstep (se 1 (by rfl) ⟨10449251, by rfl⟩ : syracuseStep 13932335 = 20898503) B20898503
theorem B956443 : Blo 846354 956443 := bstep (se 1 (by rfl) ⟨717332, by rfl⟩ : syracuseStep 956443 = 1434665) B1434665
theorem B2070911 : Blo 846354 2070911 := bstep (se 1 (by rfl) ⟨1553183, by rfl⟩ : syracuseStep 2070911 = 3106367) B3106367
theorem B5446223 : Blo 846354 5446223 := bstep (se 1 (by rfl) ⟨4084667, by rfl⟩ : syracuseStep 5446223 = 8169335) B8169335
theorem B4299479 : Blo 846354 4299479 := bstep (se 1 (by rfl) ⟨3224609, by rfl⟩ : syracuseStep 4299479 = 6449219) B6449219
theorem B3218231 : Blo 846354 3218231 := bstep (se 1 (by rfl) ⟨2413673, by rfl⟩ : syracuseStep 3218231 = 4827347) B4827347
theorem B4070675 : Blo 846354 4070675 := bstep (se 1 (by rfl) ⟨3053006, by rfl⟩ : syracuseStep 4070675 = 6106013) B6106013
theorem B1908251 : Blo 846354 1908251 := bstep (se 1 (by rfl) ⟨1431188, by rfl⟩ : syracuseStep 1908251 = 2862377) B2862377
theorem B4824683 : Blo 846354 4824683 := bstep (se 1 (by rfl) ⟨3618512, by rfl⟩ : syracuseStep 4824683 = 7237025) B7237025
theorem B12230297 : Blo 846354 12230297 := bstep (se 2 (by rfl) ⟨4586361, by rfl⟩ : syracuseStep 12230297 = 9172723) B9172723
theorem B3219689 : Blo 846354 3219689 := bstep (se 2 (by rfl) ⟨1207383, by rfl⟩ : syracuseStep 3219689 = 2414767) B2414767
theorem B1909151 : Blo 846354 1909151 := bstep (se 1 (by rfl) ⟨1431863, by rfl⟩ : syracuseStep 1909151 = 2863727) B2863727
theorem B4301423 : Blo 846354 4301423 := bstep (se 1 (by rfl) ⟨3226067, by rfl⟩ : syracuseStep 4301423 = 6452135) B6452135
theorem B20620327 : Blo 846354 20620327 := bstep (se 1 (by rfl) ⟨15465245, by rfl⟩ : syracuseStep 20620327 = 30930491) B30930491
theorem B2860379 : Blo 846354 2860379 := bstep (se 1 (by rfl) ⟨2145284, by rfl⟩ : syracuseStep 2860379 = 4290569) B4290569
theorem B35858765 : Blo 846354 35858765 := bstep (se 3 (by rfl) ⟨6723518, by rfl⟩ : syracuseStep 35858765 = 13447037) B13447037
theorem B1911527 : Blo 846354 1911527 := bstep (se 1 (by rfl) ⟨1433645, by rfl⟩ : syracuseStep 1911527 = 2867291) B2867291
theorem B24488729 : Blo 846354 24488729 := bstep (se 2 (by rfl) ⟨9183273, by rfl⟩ : syracuseStep 24488729 = 18366547) B18366547
theorem B21703787 : Blo 846354 21703787 := bstep (se 1 (by rfl) ⟨16277840, by rfl⟩ : syracuseStep 21703787 = 32555681) B32555681
theorem B6434153 : Blo 846354 6434153 := bstep (se 2 (by rfl) ⟨2412807, by rfl⟩ : syracuseStep 6434153 = 4825615) B4825615
theorem B4304339 : Blo 846354 4304339 := bstep (se 1 (by rfl) ⟨3228254, by rfl⟩ : syracuseStep 4304339 = 6456509) B6456509
theorem B2863079 : Blo 846354 2863079 := bstep (se 1 (by rfl) ⟨2147309, by rfl⟩ : syracuseStep 2863079 = 4294619) B4294619
theorem B2863187 : Blo 846354 2863187 := bstep (se 1 (by rfl) ⟨2147390, by rfl⟩ : syracuseStep 2863187 = 4294781) B4294781
theorem B5157083 : Blo 846354 5157083 := bstep (se 1 (by rfl) ⟨3867812, by rfl⟩ : syracuseStep 5157083 = 7735625) B7735625
theorem B3224063 : Blo 846354 3224063 := bstep (se 1 (by rfl) ⟨2418047, by rfl⟩ : syracuseStep 3224063 = 4836095) B4836095
theorem B2143007 : Blo 846354 2143007 := bstep (se 1 (by rfl) ⟨1607255, by rfl⟩ : syracuseStep 2143007 = 3214511) B3214511
theorem B3224519 : Blo 846354 3224519 := bstep (se 1 (by rfl) ⟨2418389, by rfl⟩ : syracuseStep 3224519 = 4836779) B4836779
theorem B2897545 : Blo 846354 2897545 := bstep (se 2 (by rfl) ⟨1086579, by rfl⟩ : syracuseStep 2897545 = 2173159) B2173159
theorem B1357679 : Blo 846354 1357679 := bstep (se 1 (by rfl) ⟨1018259, by rfl⟩ : syracuseStep 1357679 = 2036519) B2036519
theorem B965407 : Blo 846354 965407 := bstep (se 1 (by rfl) ⟨724055, by rfl⟩ : syracuseStep 965407 = 1448111) B1448111
theorem B10337129 : Blo 846354 10337129 := bstep (se 2 (by rfl) ⟨3876423, by rfl⟩ : syracuseStep 10337129 = 7752847) B7752847
theorem B2866049 : Blo 846354 2866049 := bstep (se 2 (by rfl) ⟨1074768, by rfl⟩ : syracuseStep 2866049 = 2149537) B2149537
theorem B9158017 : Blo 846354 9158017 := bstep (se 2 (by rfl) ⟨3434256, by rfl⟩ : syracuseStep 9158017 = 6868513) B6868513
theorem B2145761 : Blo 846354 2145761 := bstep (se 2 (by rfl) ⟨804660, by rfl⟩ : syracuseStep 2145761 = 1609321) B1609321
theorem B10862099 : Blo 846354 10862099 := bstep (se 1 (by rfl) ⟨8146574, by rfl⟩ : syracuseStep 10862099 = 16293149) B16293149
theorem B3096959 : Blo 846354 3096959 := bstep (se 1 (by rfl) ⟨2322719, by rfl⟩ : syracuseStep 3096959 = 4645439) B4645439
theorem B17450315 : Blo 846354 17450315 := bstep (se 1 (by rfl) ⟨13087736, by rfl⟩ : syracuseStep 17450315 = 26175473) B26175473
theorem B335398697 : Blo 846354 335398697 := bstep (se 2 (by rfl) ⟨125774511, by rfl⟩ : syracuseStep 335398697 = 251549023) B251549023
theorem B5425127 : Blo 846354 5425127 := bstep (se 1 (by rfl) ⟨4068845, by rfl⟩ : syracuseStep 5425127 = 8137691) B8137691
theorem B4835321 : Blo 846354 4835321 := bstep (se 2 (by rfl) ⟨1813245, by rfl⟩ : syracuseStep 4835321 = 3626491) B3626491
theorem B3623039 : Blo 846354 3623039 := bstep (se 1 (by rfl) ⟨2717279, by rfl⟩ : syracuseStep 3623039 = 5434559) B5434559
theorem B2574623 : Blo 846354 2574623 := bstep (se 1 (by rfl) ⟨1930967, by rfl⟩ : syracuseStep 2574623 = 3861935) B3861935
theorem B46451789 : Blo 846354 46451789 := bstep (se 3 (by rfl) ⟨8709710, by rfl⟩ : syracuseStep 46451789 = 17419421) B17419421
theorem B52317413 : Blo 846354 52317413 := bstep (se 4 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 52317413 = 9809515) B9809515
theorem B1428799 : Blo 846354 1428799 := bstep (se 1 (by rfl) ⟨1071599, by rfl⟩ : syracuseStep 1428799 = 2143199) B2143199
theorem B3624527 : Blo 846354 3624527 := bstep (se 1 (by rfl) ⟨2718395, by rfl⟩ : syracuseStep 3624527 = 5436791) B5436791
theorem B30985811 : Blo 846354 30985811 := bstep (se 1 (by rfl) ⟨23239358, by rfl⟩ : syracuseStep 30985811 = 46478717) B46478717
theorem B4837097 : Blo 846354 4837097 := bstep (se 2 (by rfl) ⟨1813911, by rfl⟩ : syracuseStep 4837097 = 3627823) B3627823
theorem B1429231 : Blo 846354 1429231 := bstep (se 1 (by rfl) ⟨1071923, by rfl⟩ : syracuseStep 1429231 = 2143847) B2143847
theorem B23253277 : Blo 846354 23253277 := bstep (se 3 (by rfl) ⟨4359989, by rfl⟩ : syracuseStep 23253277 = 8719979) B8719979
theorem B2413309 : Blo 846354 2413309 := bstep (se 3 (by rfl) ⟨452495, by rfl⟩ : syracuseStep 2413309 = 904991) B904991
theorem B1528903 : Blo 846354 1528903 := bstep (se 1 (by rfl) ⟨1146677, by rfl⟩ : syracuseStep 1528903 = 2293355) B2293355
theorem B2152403 : Blo 846354 2152403 := bstep (se 1 (by rfl) ⟨1614302, by rfl⟩ : syracuseStep 2152403 = 3228605) B3228605
theorem B1398811 : Blo 846354 1398811 := bstep (se 1 (by rfl) ⟨1049108, by rfl⟩ : syracuseStep 1398811 = 2098217) B2098217
theorem B6446303 : Blo 846354 6446303 := bstep (se 1 (by rfl) ⟨4834727, by rfl⟩ : syracuseStep 6446303 = 9669455) B9669455
theorem B1269641 : Blo 846354 1269641 := bstep (se 2 (by rfl) ⟨476115, by rfl⟩ : syracuseStep 1269641 = 952231) B952231
theorem B24797497 : Blo 846354 24797497 := bstep (se 2 (by rfl) ⟨9299061, by rfl⟩ : syracuseStep 24797497 = 18598123) B18598123
theorem B1270175 : Blo 846354 1270175 := bstep (se 1 (by rfl) ⟨952631, by rfl⟩ : syracuseStep 1270175 = 1905263) B1905263
theorem B4841927 : Blo 846354 4841927 := bstep (se 1 (by rfl) ⟨3631445, by rfl⟩ : syracuseStep 4841927 = 7262891) B7262891
theorem B1270631 : Blo 846354 1270631 := bstep (se 1 (by rfl) ⟨952973, by rfl⟩ : syracuseStep 1270631 = 1905947) B1905947
theorem B1270751 : Blo 846354 1270751 := bstep (se 1 (by rfl) ⟨953063, by rfl⟩ : syracuseStep 1270751 = 1906127) B1906127
theorem B1434719 : Blo 846354 1434719 := bstep (se 1 (by rfl) ⟨1076039, by rfl⟩ : syracuseStep 1434719 = 2152079) B2152079
theorem B1270967 : Blo 846354 1270967 := bstep (se 1 (by rfl) ⟨953225, by rfl⟩ : syracuseStep 1270967 = 1906451) B1906451
theorem B1434847 : Blo 846354 1434847 := bstep (se 1 (by rfl) ⟨1076135, by rfl⟩ : syracuseStep 1434847 = 2152271) B2152271
theorem B2712923 : Blo 846354 2712923 := bstep (se 1 (by rfl) ⟨2034692, by rfl⟩ : syracuseStep 2712923 = 4069385) B4069385
theorem B46491245 : Blo 846354 46491245 := bstep (se 3 (by rfl) ⟨8717108, by rfl⟩ : syracuseStep 46491245 = 17434217) B17434217
theorem B2713513 : Blo 846354 2713513 := bstep (se 2 (by rfl) ⟨1017567, by rfl⟩ : syracuseStep 2713513 = 2035135) B2035135
theorem B1271849 : Blo 846354 1271849 := bstep (se 2 (by rfl) ⟨476943, by rfl⟩ : syracuseStep 1271849 = 953887) B953887
theorem B1271879 : Blo 846354 1271879 := bstep (se 1 (by rfl) ⟨953909, by rfl⟩ : syracuseStep 1271879 = 1907819) B1907819
theorem B3631823 : Blo 846354 3631823 := bstep (se 1 (by rfl) ⟨2723867, by rfl⟩ : syracuseStep 3631823 = 5447735) B5447735
theorem B846759 : Blo 846354 846759 := bstep (se 1 (by rfl) ⟨635069, by rfl⟩ : syracuseStep 846759 = 1270139) B1270139
theorem B1272815 : Blo 846354 1272815 := bstep (se 1 (by rfl) ⟨954611, by rfl⟩ : syracuseStep 1272815 = 1909223) B1909223
theorem B847079 : Blo 846354 847079 := bstep (se 1 (by rfl) ⟨635309, by rfl⟩ : syracuseStep 847079 = 1270619) B1270619
theorem B5500169 : Blo 846354 5500169 := bstep (se 2 (by rfl) ⟨2062563, by rfl⟩ : syracuseStep 5500169 = 4125127) B4125127
theorem B1273247 : Blo 846354 1273247 := bstep (se 1 (by rfl) ⟨954935, by rfl⟩ : syracuseStep 1273247 = 1909871) B1909871
theorem B847407 : Blo 846354 847407 := bstep (se 1 (by rfl) ⟨635555, by rfl⟩ : syracuseStep 847407 = 1271111) B1271111
theorem B1273391 : Blo 846354 1273391 := bstep (se 1 (by rfl) ⟨955043, by rfl⟩ : syracuseStep 1273391 = 1910087) B1910087
theorem B847647 : Blo 846354 847647 := bstep (se 1 (by rfl) ⟨635735, by rfl⟩ : syracuseStep 847647 = 1271471) B1271471
theorem B848123 : Blo 846354 848123 := bstep (se 1 (by rfl) ⟨636092, by rfl⟩ : syracuseStep 848123 = 1272185) B1272185
theorem B848127 : Blo 846354 848127 := bstep (se 1 (by rfl) ⟨636095, by rfl⟩ : syracuseStep 848127 = 1272191) B1272191
theorem B1274153 : Blo 846354 1274153 := bstep (se 2 (by rfl) ⟨477807, by rfl⟩ : syracuseStep 1274153 = 955615) B955615
theorem B2715947 : Blo 846354 2715947 := bstep (se 1 (by rfl) ⟨2036960, by rfl⟩ : syracuseStep 2715947 = 4073921) B4073921
theorem B848287 : Blo 846354 848287 := bstep (se 1 (by rfl) ⟨636215, by rfl⟩ : syracuseStep 848287 = 1272431) B1272431
theorem B1274303 : Blo 846354 1274303 := bstep (se 1 (by rfl) ⟨955727, by rfl⟩ : syracuseStep 1274303 = 1911455) B1911455
theorem B7336421 : Blo 846354 7336421 := bstep (se 4 (by rfl) ⟨687789, by rfl⟩ : syracuseStep 7336421 = 1375579) B1375579
theorem B1209001 : Blo 846354 1209001 := bstep (se 2 (by rfl) ⟨453375, by rfl⟩ : syracuseStep 1209001 = 906751) B906751
theorem B848743 : Blo 846354 848743 := bstep (se 1 (by rfl) ⟨636557, by rfl⟩ : syracuseStep 848743 = 1273115) B1273115
theorem B848863 : Blo 846354 848863 := bstep (se 1 (by rfl) ⟨636647, by rfl⟩ : syracuseStep 848863 = 1273295) B1273295
theorem B848987 : Blo 846354 848987 := bstep (se 1 (by rfl) ⟨636740, by rfl⟩ : syracuseStep 848987 = 1273481) B1273481
theorem B849023 : Blo 846354 849023 := bstep (se 1 (by rfl) ⟨636767, by rfl⟩ : syracuseStep 849023 = 1273535) B1273535
theorem B9663623 : Blo 846354 9663623 := bstep (se 1 (by rfl) ⟨7247717, by rfl⟩ : syracuseStep 9663623 = 14495435) B14495435
theorem B2290879 : Blo 846354 2290879 := bstep (se 1 (by rfl) ⟨1718159, by rfl⟩ : syracuseStep 2290879 = 3436319) B3436319
theorem B2717819 : Blo 846354 2717819 := bstep (se 1 (by rfl) ⟨2038364, by rfl⟩ : syracuseStep 2717819 = 4076729) B4076729
theorem B850047 : Blo 846354 850047 := bstep (se 1 (by rfl) ⟨637535, by rfl⟩ : syracuseStep 850047 = 1275071) B1275071
theorem B1931617 : Blo 846354 1931617 := bstep (se 2 (by rfl) ⟨724356, by rfl⟩ : syracuseStep 1931617 = 1448713) B1448713
theorem B5438249 : Blo 846354 5438249 := bstep (se 2 (by rfl) ⟨2039343, by rfl⟩ : syracuseStep 5438249 = 4078687) B4078687
theorem B7339207 : Blo 846354 7339207 := bstep (se 1 (by rfl) ⟨5504405, by rfl⟩ : syracuseStep 7339207 = 11008811) B11008811
theorem B34766603 : Blo 846354 34766603 := bstep (se 1 (by rfl) ⟨26074952, by rfl⟩ : syracuseStep 34766603 = 52149905) B52149905
theorem B33063329 : Blo 846354 33063329 := bstep (se 2 (by rfl) ⟨12398748, by rfl⟩ : syracuseStep 33063329 = 24797497) B24797497
theorem B11633543 : Blo 846354 11633543 := bstep (se 1 (by rfl) ⟨8725157, by rfl⟩ : syracuseStep 11633543 = 17450315) B17450315
theorem B8258557 : Blo 846354 8258557 := bstep (se 3 (by rfl) ⟨1548479, by rfl⟩ : syracuseStep 8258557 = 3096959) B3096959
theorem B918911 : Blo 846354 918911 := bstep (se 1 (by rfl) ⟨689183, by rfl⟩ : syracuseStep 918911 = 1378367) B1378367
theorem B27493769 : Blo 846354 27493769 := bstep (se 2 (by rfl) ⟨10310163, by rfl⟩ : syracuseStep 27493769 = 20620327) B20620327
theorem B46401443 : Blo 846354 46401443 := bstep (se 1 (by rfl) ⟨34801082, by rfl⟩ : syracuseStep 46401443 = 69602165) B69602165
theorem B30967859 : Blo 846354 30967859 := bstep (se 1 (by rfl) ⟨23225894, by rfl⟩ : syracuseStep 30967859 = 46451789) B46451789
theorem B1380607 : Blo 846354 1380607 := bstep (se 1 (by rfl) ⟨1035455, by rfl⟩ : syracuseStep 1380607 = 2070911) B2070911
theorem B1905065 : Blo 846354 1905065 := bstep (se 2 (by rfl) ⟨714399, by rfl⟩ : syracuseStep 1905065 = 1428799) B1428799
theorem B4297535 : Blo 846354 4297535 := bstep (se 1 (by rfl) ⟨3223151, by rfl⟩ : syracuseStep 4297535 = 6446303) B6446303
theorem B1905641 : Blo 846354 1905641 := bstep (se 2 (by rfl) ⟨714615, by rfl⟩ : syracuseStep 1905641 = 1429231) B1429231
theorem B3216455 : Blo 846354 3216455 := bstep (se 1 (by rfl) ⟨2412341, by rfl⟩ : syracuseStep 3216455 = 4824683) B4824683
theorem B31004369 : Blo 846354 31004369 := bstep (se 2 (by rfl) ⟨11626638, by rfl⟩ : syracuseStep 31004369 = 23253277) B23253277
theorem B956479 : Blo 846354 956479 := bstep (se 1 (by rfl) ⟨717359, by rfl⟩ : syracuseStep 956479 = 1434719) B1434719
theorem B1612001 : Blo 846354 1612001 := bstep (se 2 (by rfl) ⟨604500, by rfl⟩ : syracuseStep 1612001 = 1209001) B1209001
theorem B1808615 : Blo 846354 1808615 := bstep (se 1 (by rfl) ⟨1356461, by rfl⟩ : syracuseStep 1808615 = 2712923) B2712923
theorem B1906919 : Blo 846354 1906919 := bstep (se 1 (by rfl) ⟨1430189, by rfl⟩ : syracuseStep 1906919 = 2860379) B2860379
theorem B3217745 : Blo 846354 3217745 := bstep (se 2 (by rfl) ⟨1206654, by rfl⟩ : syracuseStep 3217745 = 2413309) B2413309
theorem B2038537 : Blo 846354 2038537 := bstep (se 2 (by rfl) ⟨764451, by rfl⟩ : syracuseStep 2038537 = 1528903) B1528903
theorem B3054505 : Blo 846354 3054505 := bstep (se 2 (by rfl) ⟨1145439, by rfl⟩ : syracuseStep 3054505 = 2290879) B2290879
theorem B16325819 : Blo 846354 16325819 := bstep (se 1 (by rfl) ⟨12244364, by rfl⟩ : syracuseStep 16325819 = 24488729) B24488729
theorem B1908719 : Blo 846354 1908719 := bstep (se 1 (by rfl) ⟨1431539, by rfl⟩ : syracuseStep 1908719 = 2863079) B2863079
theorem B1908791 : Blo 846354 1908791 := bstep (se 1 (by rfl) ⟨1431593, by rfl⟩ : syracuseStep 1908791 = 2863187) B2863187
theorem B1810631 : Blo 846354 1810631 := bstep (se 1 (by rfl) ⟨1357973, by rfl⟩ : syracuseStep 1810631 = 2715947) B2715947
theorem B4890947 : Blo 846354 4890947 := bstep (se 1 (by rfl) ⟨3668210, by rfl⟩ : syracuseStep 4890947 = 7336421) B7336421
theorem B1287209 : Blo 846354 1287209 := bstep (se 2 (by rfl) ⟨482703, by rfl⟩ : syracuseStep 1287209 = 965407) B965407
theorem B1811879 : Blo 846354 1811879 := bstep (se 1 (by rfl) ⟨1358909, by rfl⟩ : syracuseStep 1811879 = 2717819) B2717819
theorem B6891419 : Blo 846354 6891419 := bstep (se 1 (by rfl) ⟨5168564, by rfl⟩ : syracuseStep 6891419 = 10337129) B10337129
theorem B1910699 : Blo 846354 1910699 := bstep (se 1 (by rfl) ⟨1433024, by rfl⟩ : syracuseStep 1910699 = 2866049) B2866049
theorem B23177735 : Blo 846354 23177735 := bstep (se 1 (by rfl) ⟨17383301, by rfl⟩ : syracuseStep 23177735 = 34766603) B34766603
theorem B2862107 : Blo 846354 2862107 := bstep (se 1 (by rfl) ⟨2146580, by rfl⟩ : syracuseStep 2862107 = 4293161) B4293161
theorem B3616751 : Blo 846354 3616751 := bstep (se 1 (by rfl) ⟨2712563, by rfl⟩ : syracuseStep 3616751 = 5425127) B5425127
theorem B3223547 : Blo 846354 3223547 := bstep (se 1 (by rfl) ⟨2417660, by rfl⟩ : syracuseStep 3223547 = 4835321) B4835321
theorem B1913129 : Blo 846354 1913129 := bstep (se 2 (by rfl) ⟨717423, by rfl⟩ : syracuseStep 1913129 = 1434847) B1434847
theorem B34878275 : Blo 846354 34878275 := bstep (se 1 (by rfl) ⟨26158706, by rfl⟩ : syracuseStep 34878275 = 52317413) B52317413
theorem B2863943 : Blo 846354 2863943 := bstep (se 1 (by rfl) ⟨2147957, by rfl⟩ : syracuseStep 2863943 = 4295915) B4295915
theorem B20657207 : Blo 846354 20657207 := bstep (se 1 (by rfl) ⟨15492905, by rfl⟩ : syracuseStep 20657207 = 30985811) B30985811
theorem B3224731 : Blo 846354 3224731 := bstep (se 1 (by rfl) ⟨2418548, by rfl⟩ : syracuseStep 3224731 = 4837097) B4837097
theorem B3618017 : Blo 846354 3618017 := bstep (se 2 (by rfl) ⟨1356756, by rfl⟩ : syracuseStep 3618017 = 2713513) B2713513
theorem B2209747 : Blo 846354 2209747 := bstep (se 1 (by rfl) ⟨1657310, by rfl⟩ : syracuseStep 2209747 = 3314621) B3314621
theorem B2865563 : Blo 846354 2865563 := bstep (se 1 (by rfl) ⟨2149172, by rfl⟩ : syracuseStep 2865563 = 4298345) B4298345
theorem B23247809 : Blo 846354 23247809 := bstep (se 2 (by rfl) ⟨8717928, by rfl⟩ : syracuseStep 23247809 = 17435857) B17435857
theorem B2866319 : Blo 846354 2866319 := bstep (se 1 (by rfl) ⟨2149739, by rfl⟩ : syracuseStep 2866319 = 4299479) B4299479
theorem B2145487 : Blo 846354 2145487 := bstep (se 1 (by rfl) ⟨1609115, by rfl⟩ : syracuseStep 2145487 = 3218231) B3218231
theorem B3620477 : Blo 846354 3620477 := bstep (se 3 (by rfl) ⟨678839, by rfl⟩ : syracuseStep 3620477 = 1357679) B1357679
theorem B2146459 : Blo 846354 2146459 := bstep (se 1 (by rfl) ⟨1609844, by rfl⟩ : syracuseStep 2146459 = 3219689) B3219689
theorem B2146601 : Blo 846354 2146601 := bstep (se 2 (by rfl) ⟨804975, by rfl⟩ : syracuseStep 2146601 = 1609951) B1609951
theorem B3227951 : Blo 846354 3227951 := bstep (se 1 (by rfl) ⟨2420963, by rfl⟩ : syracuseStep 3227951 = 4841927) B4841927
theorem B2867615 : Blo 846354 2867615 := bstep (se 1 (by rfl) ⟨2150711, by rfl⟩ : syracuseStep 2867615 = 4301423) B4301423
theorem B6865661 : Blo 846354 6865661 := bstep (se 3 (by rfl) ⟨1287311, by rfl⟩ : syracuseStep 6865661 = 2574623) B2574623
theorem B23905843 : Blo 846354 23905843 := bstep (se 1 (by rfl) ⟨17929382, by rfl⟩ : syracuseStep 23905843 = 35858765) B35858765
theorem B14469191 : Blo 846354 14469191 := bstep (se 1 (by rfl) ⟨10851893, by rfl⟩ : syracuseStep 14469191 = 21703787) B21703787
theorem B2869559 : Blo 846354 2869559 := bstep (se 1 (by rfl) ⟨2152169, by rfl⟩ : syracuseStep 2869559 = 4304339) B4304339
theorem B2149375 : Blo 846354 2149375 := bstep (se 1 (by rfl) ⟨1612031, by rfl⟩ : syracuseStep 2149375 = 3224063) B3224063
theorem B2575489 : Blo 846354 2575489 := bstep (se 2 (by rfl) ⟨965808, by rfl⟩ : syracuseStep 2575489 = 1931617) B1931617
theorem B1428671 : Blo 846354 1428671 := bstep (se 1 (by rfl) ⟨1071503, by rfl⟩ : syracuseStep 1428671 = 2143007) B2143007
theorem B2149679 : Blo 846354 2149679 := bstep (se 1 (by rfl) ⟨1612259, by rfl⟩ : syracuseStep 2149679 = 3224519) B3224519
theorem B6442415 : Blo 846354 6442415 := bstep (se 1 (by rfl) ⟨4831811, by rfl⟩ : syracuseStep 6442415 = 9663623) B9663623
theorem B9785609 : Blo 846354 9785609 := bstep (se 2 (by rfl) ⟨3669603, by rfl⟩ : syracuseStep 9785609 = 7339207) B7339207
theorem B12210689 : Blo 846354 12210689 := bstep (se 2 (by rfl) ⟨4579008, by rfl⟩ : syracuseStep 12210689 = 9158017) B9158017
theorem B3625499 : Blo 846354 3625499 := bstep (se 1 (by rfl) ⟨2719124, by rfl⟩ : syracuseStep 3625499 = 5438249) B5438249
theorem B1430507 : Blo 846354 1430507 := bstep (se 1 (by rfl) ⟨1072880, by rfl⟩ : syracuseStep 1430507 = 2145761) B2145761
theorem B223599131 : Blo 846354 223599131 := bstep (se 1 (by rfl) ⟨167699348, by rfl⟩ : syracuseStep 223599131 = 335398697) B335398697
theorem B2415359 : Blo 846354 2415359 := bstep (se 1 (by rfl) ⟨1811519, by rfl⟩ : syracuseStep 2415359 = 3623039) B3623039
theorem B2416351 : Blo 846354 2416351 := bstep (se 1 (by rfl) ⟨1812263, by rfl⟩ : syracuseStep 2416351 = 3624527) B3624527
theorem B2580607 : Blo 846354 2580607 := bstep (se 1 (by rfl) ⟨1935455, by rfl⟩ : syracuseStep 2580607 = 3870911) B3870911
theorem B58647037 : Blo 846354 58647037 := bstep (se 3 (by rfl) ⟨10996319, by rfl⟩ : syracuseStep 58647037 = 21992639) B21992639
theorem B4285223 : Blo 846354 4285223 := bstep (se 1 (by rfl) ⟨3213917, by rfl⟩ : syracuseStep 4285223 = 6427835) B6427835
theorem B4285547 : Blo 846354 4285547 := bstep (se 1 (by rfl) ⟨3214160, by rfl⟩ : syracuseStep 4285547 = 6428321) B6428321
theorem B1434935 : Blo 846354 1434935 := bstep (se 1 (by rfl) ⟨1076201, by rfl⟩ : syracuseStep 1434935 = 2152403) B2152403
theorem B3630815 : Blo 846354 3630815 := bstep (se 1 (by rfl) ⟨2723111, by rfl⟩ : syracuseStep 3630815 = 5446223) B5446223
theorem B37152893 : Blo 846354 37152893 := bstep (se 3 (by rfl) ⟨6966167, by rfl⟩ : syracuseStep 37152893 = 13932335) B13932335
theorem B2713783 : Blo 846354 2713783 := bstep (se 1 (by rfl) ⟨2035337, by rfl⟩ : syracuseStep 2713783 = 4070675) B4070675
theorem B1272167 : Blo 846354 1272167 := bstep (se 1 (by rfl) ⟨954125, by rfl⟩ : syracuseStep 1272167 = 1908251) B1908251
theorem B8153531 : Blo 846354 8153531 := bstep (se 1 (by rfl) ⟨6115148, by rfl⟩ : syracuseStep 8153531 = 12230297) B12230297
theorem B846427 : Blo 846354 846427 := bstep (se 1 (by rfl) ⟨634820, by rfl⟩ : syracuseStep 846427 = 1269641) B1269641
theorem B846783 : Blo 846354 846783 := bstep (se 1 (by rfl) ⟨635087, by rfl⟩ : syracuseStep 846783 = 1270175) B1270175
theorem B1272767 : Blo 846354 1272767 := bstep (se 1 (by rfl) ⟨954575, by rfl⟩ : syracuseStep 1272767 = 1909151) B1909151
theorem B847087 : Blo 846354 847087 := bstep (se 1 (by rfl) ⟨635315, by rfl⟩ : syracuseStep 847087 = 1270631) B1270631
theorem B847167 : Blo 846354 847167 := bstep (se 1 (by rfl) ⟨635375, by rfl⟩ : syracuseStep 847167 = 1270751) B1270751
theorem B847311 : Blo 846354 847311 := bstep (se 1 (by rfl) ⟨635483, by rfl⟩ : syracuseStep 847311 = 1270967) B1270967
theorem B30994163 : Blo 846354 30994163 := bstep (se 1 (by rfl) ⟨23245622, by rfl⟩ : syracuseStep 30994163 = 46491245) B46491245
theorem B1273769 : Blo 846354 1273769 := bstep (se 2 (by rfl) ⟨477663, by rfl⟩ : syracuseStep 1273769 = 955327) B955327
theorem B847899 : Blo 846354 847899 := bstep (se 1 (by rfl) ⟨635924, by rfl⟩ : syracuseStep 847899 = 1271849) B1271849
theorem B847919 : Blo 846354 847919 := bstep (se 1 (by rfl) ⟨635939, by rfl⟩ : syracuseStep 847919 = 1271879) B1271879
theorem B2421215 : Blo 846354 2421215 := bstep (se 1 (by rfl) ⟨1815911, by rfl⟩ : syracuseStep 2421215 = 3631823) B3631823
theorem B1274351 : Blo 846354 1274351 := bstep (se 1 (by rfl) ⟨955763, by rfl⟩ : syracuseStep 1274351 = 1911527) B1911527
theorem B848543 : Blo 846354 848543 := bstep (se 1 (by rfl) ⟨636407, by rfl⟩ : syracuseStep 848543 = 1272815) B1272815
theorem B3666779 : Blo 846354 3666779 := bstep (se 1 (by rfl) ⟨2750084, by rfl⟩ : syracuseStep 3666779 = 5500169) B5500169
theorem B3863393 : Blo 846354 3863393 := bstep (se 2 (by rfl) ⟨1448772, by rfl⟩ : syracuseStep 3863393 = 2897545) B2897545
theorem B4289435 : Blo 846354 4289435 := bstep (se 1 (by rfl) ⟨3217076, by rfl⟩ : syracuseStep 4289435 = 6434153) B6434153
theorem B848831 : Blo 846354 848831 := bstep (se 1 (by rfl) ⟨636623, by rfl⟩ : syracuseStep 848831 = 1273247) B1273247
theorem B848927 : Blo 846354 848927 := bstep (se 1 (by rfl) ⟨636695, by rfl⟩ : syracuseStep 848927 = 1273391) B1273391
theorem B1865081 : Blo 846354 1865081 := bstep (se 2 (by rfl) ⟨699405, by rfl⟩ : syracuseStep 1865081 = 1398811) B1398811
theorem B1275257 : Blo 846354 1275257 := bstep (se 2 (by rfl) ⟨478221, by rfl⟩ : syracuseStep 1275257 = 956443) B956443
theorem B3438055 : Blo 846354 3438055 := bstep (se 1 (by rfl) ⟨2578541, by rfl⟩ : syracuseStep 3438055 = 5157083) B5157083
theorem B849435 : Blo 846354 849435 := bstep (se 1 (by rfl) ⟨637076, by rfl⟩ : syracuseStep 849435 = 1274153) B1274153
theorem B849535 : Blo 846354 849535 := bstep (se 1 (by rfl) ⟨637151, by rfl⟩ : syracuseStep 849535 = 1274303) B1274303
theorem B7241399 : Blo 846354 7241399 := bstep (se 1 (by rfl) ⟨5431049, by rfl⟩ : syracuseStep 7241399 = 10862099) B10862099
theorem B3440809 : Blo 846354 3440809 := bstep (se 2 (by rfl) ⟨1290303, by rfl⟩ : syracuseStep 3440809 = 2580607) B2580607
theorem B30934295 : Blo 846354 30934295 := bstep (se 1 (by rfl) ⟨23200721, by rfl⟩ : syracuseStep 30934295 = 46401443) B46401443
theorem B11011409 : Blo 846354 11011409 := bstep (se 2 (by rfl) ⟨4129278, by rfl⟩ : syracuseStep 11011409 = 8258557) B8258557
theorem B20645239 : Blo 846354 20645239 := bstep (se 1 (by rfl) ⟨15483929, by rfl⟩ : syracuseStep 20645239 = 30967859) B30967859
theorem B9667997 : Blo 846354 9667997 := bstep (se 3 (by rfl) ⟨1812749, by rfl⟩ : syracuseStep 9667997 = 3625499) B3625499
theorem B952447 : Blo 846354 952447 := bstep (se 1 (by rfl) ⟨714335, by rfl⟩ : syracuseStep 952447 = 1428671) B1428671
theorem B4294943 : Blo 846354 4294943 := bstep (se 1 (by rfl) ⟨3221207, by rfl⟩ : syracuseStep 4294943 = 6442415) B6442415
theorem B6523739 : Blo 846354 6523739 := bstep (se 1 (by rfl) ⟨4892804, by rfl⟩ : syracuseStep 6523739 = 9785609) B9785609
theorem B953671 : Blo 846354 953671 := bstep (se 1 (by rfl) ⟨715253, by rfl⟩ : syracuseStep 953671 = 1430507) B1430507
theorem B52170101 : Blo 846354 52170101 := bstep (se 5 (by rfl) ⟨2445473, by rfl⟩ : syracuseStep 52170101 = 4890947) B4890947
theorem B149066087 : Blo 846354 149066087 := bstep (se 1 (by rfl) ⟨111799565, by rfl⟩ : syracuseStep 149066087 = 223599131) B223599131
theorem B10883879 : Blo 846354 10883879 := bstep (se 1 (by rfl) ⟨8162909, by rfl⟩ : syracuseStep 10883879 = 16325819) B16325819
theorem B2856815 : Blo 846354 2856815 := bstep (se 1 (by rfl) ⟨2142611, by rfl⟩ : syracuseStep 2856815 = 4285223) B4285223
theorem B4298669 : Blo 846354 4298669 := bstep (se 3 (by rfl) ⟨806000, by rfl⟩ : syracuseStep 4298669 = 1612001) B1612001
theorem B4822973 : Blo 846354 4822973 := bstep (se 3 (by rfl) ⟨904307, by rfl⟩ : syracuseStep 4822973 = 1808615) B1808615
theorem B2857031 : Blo 846354 2857031 := bstep (se 1 (by rfl) ⟨2142773, by rfl⟩ : syracuseStep 2857031 = 4285547) B4285547
theorem B956623 : Blo 846354 956623 := bstep (se 1 (by rfl) ⟨717467, by rfl⟩ : syracuseStep 956623 = 1434935) B1434935
theorem B4594279 : Blo 846354 4594279 := bstep (se 1 (by rfl) ⟨3445709, by rfl⟩ : syracuseStep 4594279 = 6891419) B6891419
theorem B4299641 : Blo 846354 4299641 := bstep (se 2 (by rfl) ⟨1612365, by rfl⟩ : syracuseStep 4299641 = 3224731) B3224731
theorem B1908071 : Blo 846354 1908071 := bstep (se 1 (by rfl) ⟨1431053, by rfl⟩ : syracuseStep 1908071 = 2862107) B2862107
theorem B1614143 : Blo 846354 1614143 := bstep (se 1 (by rfl) ⟨1210607, by rfl⟩ : syracuseStep 1614143 = 2421215) B2421215
theorem B1909295 : Blo 846354 1909295 := bstep (se 1 (by rfl) ⟨1431971, by rfl⟩ : syracuseStep 1909295 = 2863943) B2863943
theorem B2859623 : Blo 846354 2859623 := bstep (se 1 (by rfl) ⟨2144717, by rfl⟩ : syracuseStep 2859623 = 4289435) B4289435
theorem B13771471 : Blo 846354 13771471 := bstep (se 1 (by rfl) ⟨10328603, by rfl⟩ : syracuseStep 13771471 = 20657207) B20657207
theorem B4072673 : Blo 846354 4072673 := bstep (se 2 (by rfl) ⟨1527252, by rfl⟩ : syracuseStep 4072673 = 3054505) B3054505
theorem B1910375 : Blo 846354 1910375 := bstep (se 1 (by rfl) ⟨1432781, by rfl⟩ : syracuseStep 1910375 = 2865563) B2865563
theorem B2860649 : Blo 846354 2860649 := bstep (se 2 (by rfl) ⟨1072743, by rfl⟩ : syracuseStep 2860649 = 2145487) B2145487
theorem B1910879 : Blo 846354 1910879 := bstep (se 1 (by rfl) ⟨1433159, by rfl⟩ : syracuseStep 1910879 = 2866319) B2866319
theorem B3221801 : Blo 846354 3221801 := bstep (se 2 (by rfl) ⟨1208175, by rfl⟩ : syracuseStep 3221801 = 2416351) B2416351
theorem B4827599 : Blo 846354 4827599 := bstep (se 1 (by rfl) ⟨3620699, by rfl⟩ : syracuseStep 4827599 = 7241399) B7241399
theorem B9644669 : Blo 846354 9644669 := bstep (se 3 (by rfl) ⟨1808375, by rfl⟩ : syracuseStep 9644669 = 3616751) B3616751
theorem B2861945 : Blo 846354 2861945 := bstep (se 2 (by rfl) ⟨1073229, by rfl⟩ : syracuseStep 2861945 = 2146459) B2146459
theorem B1911743 : Blo 846354 1911743 := bstep (se 1 (by rfl) ⟨1433807, by rfl⟩ : syracuseStep 1911743 = 2867615) B2867615
theorem B4828349 : Blo 846354 4828349 := bstep (se 3 (by rfl) ⟨905315, by rfl⟩ : syracuseStep 4828349 = 1810631) B1810631
theorem B78196049 : Blo 846354 78196049 := bstep (se 2 (by rfl) ⟨29323518, by rfl⟩ : syracuseStep 78196049 = 58647037) B58647037
theorem B18329179 : Blo 846354 18329179 := bstep (se 1 (by rfl) ⟨13746884, by rfl⟩ : syracuseStep 18329179 = 27493769) B27493769
theorem B9646127 : Blo 846354 9646127 := bstep (se 1 (by rfl) ⟨7234595, by rfl⟩ : syracuseStep 9646127 = 14469191) B14469191
theorem B1913039 : Blo 846354 1913039 := bstep (se 1 (by rfl) ⟨1434779, by rfl⟩ : syracuseStep 1913039 = 2869559) B2869559
theorem B3618377 : Blo 846354 3618377 := bstep (se 2 (by rfl) ⟨1356891, by rfl⟩ : syracuseStep 3618377 = 2713783) B2713783
theorem B8140459 : Blo 846354 8140459 := bstep (se 1 (by rfl) ⟨6105344, by rfl⟩ : syracuseStep 8140459 = 12210689) B12210689
theorem B2865023 : Blo 846354 2865023 := bstep (se 1 (by rfl) ⟨2148767, by rfl⟩ : syracuseStep 2865023 = 4297535) B4297535
theorem B2144303 : Blo 846354 2144303 := bstep (se 1 (by rfl) ⟨1608227, by rfl⟩ : syracuseStep 2144303 = 3216455) B3216455
theorem B2865833 : Blo 846354 2865833 := bstep (se 2 (by rfl) ⟨1074687, by rfl⟩ : syracuseStep 2865833 = 2149375) B2149375
theorem B2145163 : Blo 846354 2145163 := bstep (se 1 (by rfl) ⟨1608872, by rfl⟩ : syracuseStep 2145163 = 3217745) B3217745
theorem B188565077 : Blo 846354 188565077 := bstep (se 8 (by rfl) ⟨1104873, by rfl⟩ : syracuseStep 188565077 = 2209747) B2209747
theorem B15451823 : Blo 846354 15451823 := bstep (se 1 (by rfl) ⟨11588867, by rfl⟩ : syracuseStep 15451823 = 23177735) B23177735
theorem B6440957 : Blo 846354 6440957 := bstep (se 3 (by rfl) ⟨1207679, by rfl⟩ : syracuseStep 6440957 = 2415359) B2415359
theorem B20662775 : Blo 846354 20662775 := bstep (se 1 (by rfl) ⟨15497081, by rfl⟩ : syracuseStep 20662775 = 30994163) B30994163
theorem B2149031 : Blo 846354 2149031 := bstep (se 1 (by rfl) ⟨1611773, by rfl⟩ : syracuseStep 2149031 = 3223547) B3223547
theorem B23252183 : Blo 846354 23252183 := bstep (se 1 (by rfl) ⟨17439137, by rfl⟩ : syracuseStep 23252183 = 34878275) B34878275
theorem B2444519 : Blo 846354 2444519 := bstep (se 1 (by rfl) ⟨1833389, by rfl⟩ : syracuseStep 2444519 = 3666779) B3666779
theorem B2575595 : Blo 846354 2575595 := bstep (se 1 (by rfl) ⟨1931696, by rfl⟩ : syracuseStep 2575595 = 3863393) B3863393
theorem B2412011 : Blo 846354 2412011 := bstep (se 1 (by rfl) ⟨1809008, by rfl⟩ : syracuseStep 2412011 = 3618017) B3618017
theorem B2413651 : Blo 846354 2413651 := bstep (se 1 (by rfl) ⟨1810238, by rfl⟩ : syracuseStep 2413651 = 3620477) B3620477
theorem B1431067 : Blo 846354 1431067 := bstep (se 1 (by rfl) ⟨1073300, by rfl⟩ : syracuseStep 1431067 = 2146601) B2146601
theorem B2151967 : Blo 846354 2151967 := bstep (se 1 (by rfl) ⟨1613975, by rfl⟩ : syracuseStep 2151967 = 3227951) B3227951
theorem B22042219 : Blo 846354 22042219 := bstep (se 1 (by rfl) ⟨16531664, by rfl⟩ : syracuseStep 22042219 = 33063329) B33063329
theorem B4577107 : Blo 846354 4577107 := bstep (se 1 (by rfl) ⟨3432830, by rfl⟩ : syracuseStep 4577107 = 6865661) B6865661
theorem B7755695 : Blo 846354 7755695 := bstep (se 1 (by rfl) ⟨5816771, by rfl⟩ : syracuseStep 7755695 = 11633543) B11633543
theorem B7363237 : Blo 846354 7363237 := bstep (se 4 (by rfl) ⟨690303, by rfl⟩ : syracuseStep 7363237 = 1380607) B1380607
theorem B1433119 : Blo 846354 1433119 := bstep (se 1 (by rfl) ⟨1074839, by rfl⟩ : syracuseStep 1433119 = 2149679) B2149679
theorem B3432557 : Blo 846354 3432557 := bstep (se 3 (by rfl) ⟨643604, by rfl⟩ : syracuseStep 3432557 = 1287209) B1287209
theorem B1270043 : Blo 846354 1270043 := bstep (se 1 (by rfl) ⟨952532, by rfl⟩ : syracuseStep 1270043 = 1905065) B1905065
theorem B1270427 : Blo 846354 1270427 := bstep (se 1 (by rfl) ⟨952820, by rfl⟩ : syracuseStep 1270427 = 1905641) B1905641
theorem B2450429 : Blo 846354 2450429 := bstep (se 3 (by rfl) ⟨459455, by rfl⟩ : syracuseStep 2450429 = 918911) B918911
theorem B20669579 : Blo 846354 20669579 := bstep (se 1 (by rfl) ⟨15502184, by rfl⟩ : syracuseStep 20669579 = 31004369) B31004369
theorem B1271279 : Blo 846354 1271279 := bstep (se 1 (by rfl) ⟨953459, by rfl⟩ : syracuseStep 1271279 = 1906919) B1906919
theorem B3433985 : Blo 846354 3433985 := bstep (se 2 (by rfl) ⟨1287744, by rfl⟩ : syracuseStep 3433985 = 2575489) B2575489
theorem B1272479 : Blo 846354 1272479 := bstep (se 1 (by rfl) ⟨954359, by rfl⟩ : syracuseStep 1272479 = 1908719) B1908719
theorem B1272527 : Blo 846354 1272527 := bstep (se 1 (by rfl) ⟨954395, by rfl⟩ : syracuseStep 1272527 = 1908791) B1908791
theorem B1207919 : Blo 846354 1207919 := bstep (se 1 (by rfl) ⟨905939, by rfl⟩ : syracuseStep 1207919 = 1811879) B1811879
theorem B2420543 : Blo 846354 2420543 := bstep (se 1 (by rfl) ⟨1815407, by rfl⟩ : syracuseStep 2420543 = 3630815) B3630815
theorem B1273799 : Blo 846354 1273799 := bstep (se 1 (by rfl) ⟨955349, by rfl⟩ : syracuseStep 1273799 = 1910699) B1910699
theorem B24768595 : Blo 846354 24768595 := bstep (se 1 (by rfl) ⟨18576446, by rfl⟩ : syracuseStep 24768595 = 37152893) B37152893
theorem B848111 : Blo 846354 848111 := bstep (se 1 (by rfl) ⟨636083, by rfl⟩ : syracuseStep 848111 = 1272167) B1272167
theorem B5435687 : Blo 846354 5435687 := bstep (se 1 (by rfl) ⟨4076765, by rfl⟩ : syracuseStep 5435687 = 8153531) B8153531
theorem B848511 : Blo 846354 848511 := bstep (se 1 (by rfl) ⟨636383, by rfl⟩ : syracuseStep 848511 = 1272767) B1272767
theorem B4584073 : Blo 846354 4584073 := bstep (se 2 (by rfl) ⟨1719027, by rfl⟩ : syracuseStep 4584073 = 3438055) B3438055
theorem B849179 : Blo 846354 849179 := bstep (se 1 (by rfl) ⟨636884, by rfl⟩ : syracuseStep 849179 = 1273769) B1273769
theorem B1275305 : Blo 846354 1275305 := bstep (se 2 (by rfl) ⟨478239, by rfl⟩ : syracuseStep 1275305 = 956479) B956479
theorem B1275419 : Blo 846354 1275419 := bstep (se 1 (by rfl) ⟨956564, by rfl⟩ : syracuseStep 1275419 = 1913129) B1913129
theorem B127497829 : Blo 846354 127497829 := bstep (se 4 (by rfl) ⟨11952921, by rfl⟩ : syracuseStep 127497829 = 23905843) B23905843
theorem B849567 : Blo 846354 849567 := bstep (se 1 (by rfl) ⟨637175, by rfl⟩ : syracuseStep 849567 = 1274351) B1274351
theorem B1243387 : Blo 846354 1243387 := bstep (se 1 (by rfl) ⟨932540, by rfl⟩ : syracuseStep 1243387 = 1865081) B1865081
theorem B850171 : Blo 846354 850171 := bstep (se 1 (by rfl) ⟨637628, by rfl⟩ : syracuseStep 850171 = 1275257) B1275257
theorem B2718049 : Blo 846354 2718049 := bstep (se 2 (by rfl) ⟨1019268, by rfl⟩ : syracuseStep 2718049 = 2038537) B2038537
theorem B15498539 : Blo 846354 15498539 := bstep (se 1 (by rfl) ⟨11623904, by rfl⟩ : syracuseStep 15498539 = 23247809) B23247809
theorem B18350981 : Blo 846354 18350981 := bstep (se 4 (by rfl) ⟨1720404, by rfl⟩ : syracuseStep 18350981 = 3440809) B3440809
theorem B7340939 : Blo 846354 7340939 := bstep (se 1 (by rfl) ⟨5505704, by rfl⟩ : syracuseStep 7340939 = 11011409) B11011409
theorem B397509565 : Blo 846354 397509565 := bstep (se 3 (by rfl) ⟨74533043, by rfl⟩ : syracuseStep 397509565 = 149066087) B149066087
theorem B4293971 : Blo 846354 4293971 := bstep (se 1 (by rfl) ⟨3220478, by rfl⟩ : syracuseStep 4293971 = 6440957) B6440957
theorem B27526985 : Blo 846354 27526985 := bstep (se 2 (by rfl) ⟨10322619, by rfl⟩ : syracuseStep 27526985 = 20645239) B20645239
theorem B15501455 : Blo 846354 15501455 := bstep (se 1 (by rfl) ⟨11626091, by rfl⟩ : syracuseStep 15501455 = 23252183) B23252183
theorem B1608007 : Blo 846354 1608007 := bstep (se 1 (by rfl) ⟨1206005, by rfl⟩ : syracuseStep 1608007 = 2412011) B2412011
theorem B1904543 : Blo 846354 1904543 := bstep (se 1 (by rfl) ⟨1428407, by rfl⟩ : syracuseStep 1904543 = 2856815) B2856815
theorem B3215315 : Blo 846354 3215315 := bstep (se 1 (by rfl) ⟨2411486, by rfl⟩ : syracuseStep 3215315 = 4822973) B4822973
theorem B1904687 : Blo 846354 1904687 := bstep (se 1 (by rfl) ⟨1428515, by rfl⟩ : syracuseStep 1904687 = 2857031) B2857031
theorem B1906415 : Blo 846354 1906415 := bstep (se 1 (by rfl) ⟨1429811, by rfl⟩ : syracuseStep 1906415 = 2859623) B2859623
theorem B1907099 : Blo 846354 1907099 := bstep (se 1 (by rfl) ⟨1430324, by rfl⟩ : syracuseStep 1907099 = 2860649) B2860649
theorem B3218201 : Blo 846354 3218201 := bstep (se 2 (by rfl) ⟨1206825, by rfl⟩ : syracuseStep 3218201 = 2413651) B2413651
theorem B3218399 : Blo 846354 3218399 := bstep (se 1 (by rfl) ⟨2413799, by rfl⟩ : syracuseStep 3218399 = 4827599) B4827599
theorem B6429779 : Blo 846354 6429779 := bstep (se 1 (by rfl) ⟨4822334, by rfl⟩ : syracuseStep 6429779 = 9644669) B9644669
theorem B1907963 : Blo 846354 1907963 := bstep (se 1 (by rfl) ⟨1430972, by rfl⟩ : syracuseStep 1907963 = 2861945) B2861945
theorem B1908089 : Blo 846354 1908089 := bstep (se 2 (by rfl) ⟨715533, by rfl⟩ : syracuseStep 1908089 = 1431067) B1431067
theorem B3218899 : Blo 846354 3218899 := bstep (se 1 (by rfl) ⟨2414174, by rfl⟩ : syracuseStep 3218899 = 4828349) B4828349
theorem B10853945 : Blo 846354 10853945 := bstep (se 2 (by rfl) ⟨4070229, by rfl⟩ : syracuseStep 10853945 = 8140459) B8140459
theorem B6102809 : Blo 846354 6102809 := bstep (se 2 (by rfl) ⟨2288553, by rfl⟩ : syracuseStep 6102809 = 4577107) B4577107
theorem B1613695 : Blo 846354 1613695 := bstep (se 1 (by rfl) ⟨1210271, by rfl⟩ : syracuseStep 1613695 = 2420543) B2420543
theorem B6430751 : Blo 846354 6430751 := bstep (se 1 (by rfl) ⟨4823063, by rfl⟩ : syracuseStep 6430751 = 9646127) B9646127
theorem B2860217 : Blo 846354 2860217 := bstep (se 2 (by rfl) ⟨1072581, by rfl⟩ : syracuseStep 2860217 = 2145163) B2145163
theorem B1910015 : Blo 846354 1910015 := bstep (se 1 (by rfl) ⟨1432511, by rfl⟩ : syracuseStep 1910015 = 2865023) B2865023
theorem B3221117 : Blo 846354 3221117 := bstep (se 3 (by rfl) ⟨603959, by rfl⟩ : syracuseStep 3221117 = 1207919) B1207919
theorem B1910555 : Blo 846354 1910555 := bstep (se 1 (by rfl) ⟨1432916, by rfl⟩ : syracuseStep 1910555 = 2865833) B2865833
theorem B1910825 : Blo 846354 1910825 := bstep (se 2 (by rfl) ⟨716559, by rfl⟩ : syracuseStep 1910825 = 1433119) B1433119
theorem B10332359 : Blo 846354 10332359 := bstep (se 1 (by rfl) ⟨7749269, by rfl⟩ : syracuseStep 10332359 = 15498539) B15498539
theorem B9153485 : Blo 846354 9153485 := bstep (se 3 (by rfl) ⟨1716278, by rfl⟩ : syracuseStep 9153485 = 3432557) B3432557
theorem B132099173 : Blo 846354 132099173 := bstep (se 4 (by rfl) ⟨12384297, by rfl⟩ : syracuseStep 132099173 = 24768595) B24768595
theorem B20622863 : Blo 846354 20622863 := bstep (se 1 (by rfl) ⟨15467147, by rfl⟩ : syracuseStep 20622863 = 30934295) B30934295
theorem B18361961 : Blo 846354 18361961 := bstep (se 2 (by rfl) ⟨6885735, by rfl⟩ : syracuseStep 18361961 = 13771471) B13771471
theorem B125710051 : Blo 846354 125710051 := bstep (se 1 (by rfl) ⟨94282538, by rfl⟩ : syracuseStep 125710051 = 188565077) B188565077
theorem B10301215 : Blo 846354 10301215 := bstep (se 1 (by rfl) ⟨7725911, by rfl⟩ : syracuseStep 10301215 = 15451823) B15451823
theorem B2863295 : Blo 846354 2863295 := bstep (se 1 (by rfl) ⟨2147471, by rfl⟩ : syracuseStep 2863295 = 4294943) B4294943
theorem B13775183 : Blo 846354 13775183 := bstep (se 1 (by rfl) ⟨10331387, by rfl⟩ : syracuseStep 13775183 = 20662775) B20662775
theorem B34780067 : Blo 846354 34780067 := bstep (se 1 (by rfl) ⟨26085050, by rfl⟩ : syracuseStep 34780067 = 52170101) B52170101
theorem B7255919 : Blo 846354 7255919 := bstep (se 1 (by rfl) ⟨5441939, by rfl⟩ : syracuseStep 7255919 = 10883879) B10883879
theorem B2865779 : Blo 846354 2865779 := bstep (se 1 (by rfl) ⟨2149334, by rfl⟩ : syracuseStep 2865779 = 4298669) B4298669
theorem B2866427 : Blo 846354 2866427 := bstep (se 1 (by rfl) ⟨2149820, by rfl⟩ : syracuseStep 2866427 = 4299641) B4299641
theorem B13779719 : Blo 846354 13779719 := bstep (se 1 (by rfl) ⟨10334789, by rfl⟩ : syracuseStep 13779719 = 20669579) B20669579
theorem B6112097 : Blo 846354 6112097 := bstep (se 2 (by rfl) ⟨2292036, by rfl⟩ : syracuseStep 6112097 = 4584073) B4584073
theorem B2147867 : Blo 846354 2147867 := bstep (se 1 (by rfl) ⟨1610900, by rfl⟩ : syracuseStep 2147867 = 3221801) B3221801
theorem B2869289 : Blo 846354 2869289 := bstep (se 2 (by rfl) ⟨1075983, by rfl⟩ : syracuseStep 2869289 = 2151967) B2151967
theorem B3623791 : Blo 846354 3623791 := bstep (se 1 (by rfl) ⟨2717843, by rfl⟩ : syracuseStep 3623791 = 5435687) B5435687
theorem B1657849 : Blo 846354 1657849 := bstep (se 2 (by rfl) ⟨621693, by rfl⟩ : syracuseStep 1657849 = 1243387) B1243387
theorem B3624065 : Blo 846354 3624065 := bstep (se 2 (by rfl) ⟨1359024, by rfl⟩ : syracuseStep 3624065 = 2718049) B2718049
theorem B6868253 : Blo 846354 6868253 := bstep (se 3 (by rfl) ⟨1287797, by rfl⟩ : syracuseStep 6868253 = 2575595) B2575595
theorem B9817649 : Blo 846354 9817649 := bstep (se 2 (by rfl) ⟨3681618, by rfl⟩ : syracuseStep 9817649 = 7363237) B7363237
theorem B2412251 : Blo 846354 2412251 := bstep (se 1 (by rfl) ⟨1809188, by rfl⟩ : syracuseStep 2412251 = 3618377) B3618377
theorem B1429535 : Blo 846354 1429535 := bstep (se 1 (by rfl) ⟨1072151, by rfl⟩ : syracuseStep 1429535 = 2144303) B2144303
theorem B6445331 : Blo 846354 6445331 := bstep (se 1 (by rfl) ⟨4833998, by rfl⟩ : syracuseStep 6445331 = 9667997) B9667997
theorem B1432687 : Blo 846354 1432687 := bstep (se 1 (by rfl) ⟨1074515, by rfl⟩ : syracuseStep 1432687 = 2149031) B2149031
theorem B4349159 : Blo 846354 4349159 := bstep (se 1 (by rfl) ⟨3261869, by rfl⟩ : syracuseStep 4349159 = 6523739) B6523739
theorem B1269929 : Blo 846354 1269929 := bstep (se 2 (by rfl) ⟨476223, by rfl⟩ : syracuseStep 1269929 = 952447) B952447
theorem B5170463 : Blo 846354 5170463 := bstep (se 1 (by rfl) ⟨3877847, by rfl⟩ : syracuseStep 5170463 = 7755695) B7755695
theorem B1271561 : Blo 846354 1271561 := bstep (se 2 (by rfl) ⟨476835, by rfl⟩ : syracuseStep 1271561 = 953671) B953671
theorem B24438905 : Blo 846354 24438905 := bstep (se 2 (by rfl) ⟨9164589, by rfl⟩ : syracuseStep 24438905 = 18329179) B18329179
theorem B1272047 : Blo 846354 1272047 := bstep (se 1 (by rfl) ⟨954035, by rfl⟩ : syracuseStep 1272047 = 1908071) B1908071
theorem B846695 : Blo 846354 846695 := bstep (se 1 (by rfl) ⟨635021, by rfl⟩ : syracuseStep 846695 = 1270043) B1270043
theorem B1076095 : Blo 846354 1076095 := bstep (se 1 (by rfl) ⟨807071, by rfl⟩ : syracuseStep 1076095 = 1614143) B1614143
theorem B1272863 : Blo 846354 1272863 := bstep (se 1 (by rfl) ⟨954647, by rfl⟩ : syracuseStep 1272863 = 1909295) B1909295
theorem B846951 : Blo 846354 846951 := bstep (se 1 (by rfl) ⟨635213, by rfl⟩ : syracuseStep 846951 = 1270427) B1270427
theorem B1633619 : Blo 846354 1633619 := bstep (se 1 (by rfl) ⟨1225214, by rfl⟩ : syracuseStep 1633619 = 2450429) B2450429
theorem B2715115 : Blo 846354 2715115 := bstep (se 1 (by rfl) ⟨2036336, by rfl⟩ : syracuseStep 2715115 = 4072673) B4072673
theorem B847519 : Blo 846354 847519 := bstep (se 1 (by rfl) ⟨635639, by rfl⟩ : syracuseStep 847519 = 1271279) B1271279
theorem B2289323 : Blo 846354 2289323 := bstep (se 1 (by rfl) ⟨1716992, by rfl⟩ : syracuseStep 2289323 = 3433985) B3433985
theorem B1273583 : Blo 846354 1273583 := bstep (se 1 (by rfl) ⟨955187, by rfl⟩ : syracuseStep 1273583 = 1910375) B1910375
theorem B1273919 : Blo 846354 1273919 := bstep (se 1 (by rfl) ⟨955439, by rfl⟩ : syracuseStep 1273919 = 1910879) B1910879
theorem B848319 : Blo 846354 848319 := bstep (se 1 (by rfl) ⟨636239, by rfl⟩ : syracuseStep 848319 = 1272479) B1272479
theorem B848351 : Blo 846354 848351 := bstep (se 1 (by rfl) ⟨636263, by rfl⟩ : syracuseStep 848351 = 1272527) B1272527
theorem B1274495 : Blo 846354 1274495 := bstep (se 1 (by rfl) ⟨955871, by rfl⟩ : syracuseStep 1274495 = 1911743) B1911743
theorem B169997105 : Blo 846354 169997105 := bstep (se 2 (by rfl) ⟨63748914, by rfl⟩ : syracuseStep 169997105 = 127497829) B127497829
theorem B29389625 : Blo 846354 29389625 := bstep (se 2 (by rfl) ⟨11021109, by rfl⟩ : syracuseStep 29389625 = 22042219) B22042219
theorem B52130699 : Blo 846354 52130699 := bstep (se 1 (by rfl) ⟨39098024, by rfl⟩ : syracuseStep 52130699 = 78196049) B78196049
theorem B849199 : Blo 846354 849199 := bstep (se 1 (by rfl) ⟨636899, by rfl⟩ : syracuseStep 849199 = 1273799) B1273799
theorem B1275359 : Blo 846354 1275359 := bstep (se 1 (by rfl) ⟨956519, by rfl⟩ : syracuseStep 1275359 = 1913039) B1913039
theorem B1275497 : Blo 846354 1275497 := bstep (se 2 (by rfl) ⟨478311, by rfl⟩ : syracuseStep 1275497 = 956623) B956623
theorem B6518717 : Blo 846354 6518717 := bstep (se 3 (by rfl) ⟨1222259, by rfl⟩ : syracuseStep 6518717 = 2444519) B2444519
theorem B6125705 : Blo 846354 6125705 := bstep (se 2 (by rfl) ⟨2297139, by rfl⟩ : syracuseStep 6125705 = 4594279) B4594279
theorem B850203 : Blo 846354 850203 := bstep (se 1 (by rfl) ⟨637652, by rfl⟩ : syracuseStep 850203 = 1275305) B1275305
theorem B850279 : Blo 846354 850279 := bstep (se 1 (by rfl) ⟨637709, by rfl⟩ : syracuseStep 850279 = 1275419) B1275419
theorem B18351323 : Blo 846354 18351323 := bstep (se 1 (by rfl) ⟨13763492, by rfl⟩ : syracuseStep 18351323 = 27526985) B27526985
theorem B1608167 : Blo 846354 1608167 := bstep (se 1 (by rfl) ⟨1206125, by rfl⟩ : syracuseStep 1608167 = 2412251) B2412251
theorem B953023 : Blo 846354 953023 := bstep (se 1 (by rfl) ⟨714767, by rfl⟩ : syracuseStep 953023 = 1429535) B1429535
theorem B4296887 : Blo 846354 4296887 := bstep (se 1 (by rfl) ⟨3222665, by rfl⟩ : syracuseStep 4296887 = 6445331) B6445331
theorem B167613401 : Blo 846354 167613401 := bstep (se 2 (by rfl) ⟨62855025, by rfl⟩ : syracuseStep 167613401 = 125710051) B125710051
theorem B13734953 : Blo 846354 13734953 := bstep (se 2 (by rfl) ⟨5150607, by rfl⟩ : syracuseStep 13734953 = 10301215) B10301215
theorem B4068539 : Blo 846354 4068539 := bstep (se 1 (by rfl) ⟨3051404, by rfl⟩ : syracuseStep 4068539 = 6102809) B6102809
theorem B1906811 : Blo 846354 1906811 := bstep (se 1 (by rfl) ⟨1430108, by rfl⟩ : syracuseStep 1906811 = 2860217) B2860217
theorem B3446975 : Blo 846354 3446975 := bstep (se 1 (by rfl) ⟨2585231, by rfl⟩ : syracuseStep 3446975 = 5170463) B5170463
theorem B16292603 : Blo 846354 16292603 := bstep (se 1 (by rfl) ⟨12219452, by rfl⟩ : syracuseStep 16292603 = 24438905) B24438905
theorem B6888239 : Blo 846354 6888239 := bstep (se 1 (by rfl) ⟨5166179, by rfl⟩ : syracuseStep 6888239 = 10332359) B10332359
theorem B6102323 : Blo 846354 6102323 := bstep (se 1 (by rfl) ⟨4576742, by rfl⟩ : syracuseStep 6102323 = 9153485) B9153485
theorem B1908863 : Blo 846354 1908863 := bstep (se 1 (by rfl) ⟨1431647, by rfl⟩ : syracuseStep 1908863 = 2863295) B2863295
theorem B9183455 : Blo 846354 9183455 := bstep (se 1 (by rfl) ⟨6887591, by rfl⟩ : syracuseStep 9183455 = 13775183) B13775183
theorem B54994301 : Blo 846354 54994301 := bstep (se 3 (by rfl) ⟨10311431, by rfl⟩ : syracuseStep 54994301 = 20622863) B20622863
theorem B1910249 : Blo 846354 1910249 := bstep (se 2 (by rfl) ⟨716343, by rfl⟩ : syracuseStep 1910249 = 1432687) B1432687
theorem B1910519 : Blo 846354 1910519 := bstep (se 1 (by rfl) ⟨1432889, by rfl⟩ : syracuseStep 1910519 = 2865779) B2865779
theorem B1910951 : Blo 846354 1910951 := bstep (se 1 (by rfl) ⟨1433213, by rfl⟩ : syracuseStep 1910951 = 2866427) B2866427
theorem B9186479 : Blo 846354 9186479 := bstep (se 1 (by rfl) ⟨6889859, by rfl⟩ : syracuseStep 9186479 = 13779719) B13779719
theorem B4074731 : Blo 846354 4074731 := bstep (se 1 (by rfl) ⟨3056048, by rfl⟩ : syracuseStep 4074731 = 6112097) B6112097
theorem B12233987 : Blo 846354 12233987 := bstep (se 1 (by rfl) ⟨9175490, by rfl⟩ : syracuseStep 12233987 = 18350981) B18350981
theorem B4893959 : Blo 846354 4893959 := bstep (se 1 (by rfl) ⟨3670469, by rfl⟩ : syracuseStep 4893959 = 7340939) B7340939
theorem B2862647 : Blo 846354 2862647 := bstep (se 1 (by rfl) ⟨2146985, by rfl⟩ : syracuseStep 2862647 = 4293971) B4293971
theorem B1912859 : Blo 846354 1912859 := bstep (se 1 (by rfl) ⟨1434644, by rfl⟩ : syracuseStep 1912859 = 2869289) B2869289
theorem B10334303 : Blo 846354 10334303 := bstep (se 1 (by rfl) ⟨7750727, by rfl⟩ : syracuseStep 10334303 = 15501455) B15501455
theorem B2143543 : Blo 846354 2143543 := bstep (se 1 (by rfl) ⟨1607657, by rfl⟩ : syracuseStep 2143543 = 3215315) B3215315
theorem B2144009 : Blo 846354 2144009 := bstep (se 2 (by rfl) ⟨804003, by rfl⟩ : syracuseStep 2144009 = 1608007) B1608007
theorem B4831721 : Blo 846354 4831721 := bstep (se 2 (by rfl) ⟨1811895, by rfl⟩ : syracuseStep 4831721 = 3623791) B3623791
theorem B2210465 : Blo 846354 2210465 := bstep (se 2 (by rfl) ⟨828924, by rfl⟩ : syracuseStep 2210465 = 1657849) B1657849
theorem B2145467 : Blo 846354 2145467 := bstep (se 1 (by rfl) ⟨1609100, by rfl⟩ : syracuseStep 2145467 = 3218201) B3218201
theorem B3620153 : Blo 846354 3620153 := bstep (se 2 (by rfl) ⟨1357557, by rfl⟩ : syracuseStep 3620153 = 2715115) B2715115
theorem B2145599 : Blo 846354 2145599 := bstep (se 1 (by rfl) ⟨1609199, by rfl⟩ : syracuseStep 2145599 = 3218399) B3218399
theorem B2899439 : Blo 846354 2899439 := bstep (se 1 (by rfl) ⟨2174579, by rfl⟩ : syracuseStep 2899439 = 4349159) B4349159
theorem B2147411 : Blo 846354 2147411 := bstep (se 1 (by rfl) ⟨1610558, by rfl⟩ : syracuseStep 2147411 = 3221117) B3221117
theorem B88066115 : Blo 846354 88066115 := bstep (se 1 (by rfl) ⟨66049586, by rfl⟩ : syracuseStep 88066115 = 132099173) B132099173
theorem B12241307 : Blo 846354 12241307 := bstep (se 1 (by rfl) ⟨9180980, by rfl⟩ : syracuseStep 12241307 = 18361961) B18361961
theorem B1526215 : Blo 846354 1526215 := bstep (se 1 (by rfl) ⟨1144661, by rfl⟩ : syracuseStep 1526215 = 2289323) B2289323
theorem B113331403 : Blo 846354 113331403 := bstep (se 1 (by rfl) ⟨84998552, by rfl⟩ : syracuseStep 113331403 = 169997105) B169997105
theorem B34753799 : Blo 846354 34753799 := bstep (se 1 (by rfl) ⟨26065349, by rfl⟩ : syracuseStep 34753799 = 52130699) B52130699
theorem B23186711 : Blo 846354 23186711 := bstep (se 1 (by rfl) ⟨17390033, by rfl⟩ : syracuseStep 23186711 = 34780067) B34780067
theorem B4837279 : Blo 846354 4837279 := bstep (se 1 (by rfl) ⟨3627959, by rfl⟩ : syracuseStep 4837279 = 7255919) B7255919
theorem B4345811 : Blo 846354 4345811 := bstep (se 1 (by rfl) ⟨3259358, by rfl⟩ : syracuseStep 4345811 = 6518717) B6518717
theorem B4083803 : Blo 846354 4083803 := bstep (se 1 (by rfl) ⟨3062852, by rfl⟩ : syracuseStep 4083803 = 6125705) B6125705
theorem B2151593 : Blo 846354 2151593 := bstep (se 2 (by rfl) ⟨806847, by rfl⟩ : syracuseStep 2151593 = 1613695) B1613695
theorem B1431911 : Blo 846354 1431911 := bstep (se 1 (by rfl) ⟨1073933, by rfl⟩ : syracuseStep 1431911 = 2147867) B2147867
theorem B530012753 : Blo 846354 530012753 := bstep (se 2 (by rfl) ⟨198754782, by rfl⟩ : syracuseStep 530012753 = 397509565) B397509565
theorem B2416043 : Blo 846354 2416043 := bstep (se 1 (by rfl) ⟨1812032, by rfl⟩ : syracuseStep 2416043 = 3624065) B3624065
theorem B6545099 : Blo 846354 6545099 := bstep (se 1 (by rfl) ⟨4908824, by rfl⟩ : syracuseStep 6545099 = 9817649) B9817649
theorem B1269695 : Blo 846354 1269695 := bstep (se 1 (by rfl) ⟨952271, by rfl⟩ : syracuseStep 1269695 = 1904543) B1904543
theorem B1269791 : Blo 846354 1269791 := bstep (se 1 (by rfl) ⟨952343, by rfl⟩ : syracuseStep 1269791 = 1904687) B1904687
theorem B1270943 : Blo 846354 1270943 := bstep (se 1 (by rfl) ⟨953207, by rfl⟩ : syracuseStep 1270943 = 1906415) B1906415
theorem B1434793 : Blo 846354 1434793 := bstep (se 2 (by rfl) ⟨538047, by rfl⟩ : syracuseStep 1434793 = 1076095) B1076095
theorem B1271399 : Blo 846354 1271399 := bstep (se 1 (by rfl) ⟨953549, by rfl⟩ : syracuseStep 1271399 = 1907099) B1907099
theorem B4286519 : Blo 846354 4286519 := bstep (se 1 (by rfl) ⟨3214889, by rfl⟩ : syracuseStep 4286519 = 6429779) B6429779
theorem B1271975 : Blo 846354 1271975 := bstep (se 1 (by rfl) ⟨953981, by rfl⟩ : syracuseStep 1271975 = 1907963) B1907963
theorem B1272059 : Blo 846354 1272059 := bstep (se 1 (by rfl) ⟨954044, by rfl⟩ : syracuseStep 1272059 = 1908089) B1908089
theorem B7235963 : Blo 846354 7235963 := bstep (se 1 (by rfl) ⟨5426972, by rfl⟩ : syracuseStep 7235963 = 10853945) B10853945
theorem B4287167 : Blo 846354 4287167 := bstep (se 1 (by rfl) ⟨3215375, by rfl⟩ : syracuseStep 4287167 = 6430751) B6430751
theorem B846619 : Blo 846354 846619 := bstep (se 1 (by rfl) ⟨634964, by rfl⟩ : syracuseStep 846619 = 1269929) B1269929
theorem B1273343 : Blo 846354 1273343 := bstep (se 1 (by rfl) ⟨955007, by rfl⟩ : syracuseStep 1273343 = 1910015) B1910015
theorem B847707 : Blo 846354 847707 := bstep (se 1 (by rfl) ⟨635780, by rfl⟩ : syracuseStep 847707 = 1271561) B1271561
theorem B1273703 : Blo 846354 1273703 := bstep (se 1 (by rfl) ⟨955277, by rfl⟩ : syracuseStep 1273703 = 1910555) B1910555
theorem B1273883 : Blo 846354 1273883 := bstep (se 1 (by rfl) ⟨955412, by rfl⟩ : syracuseStep 1273883 = 1910825) B1910825
theorem B848031 : Blo 846354 848031 := bstep (se 1 (by rfl) ⟨636023, by rfl⟩ : syracuseStep 848031 = 1272047) B1272047
theorem B848575 : Blo 846354 848575 := bstep (se 1 (by rfl) ⟨636431, by rfl⟩ : syracuseStep 848575 = 1272863) B1272863
theorem B849055 : Blo 846354 849055 := bstep (se 1 (by rfl) ⟨636791, by rfl⟩ : syracuseStep 849055 = 1273583) B1273583
theorem B849279 : Blo 846354 849279 := bstep (se 1 (by rfl) ⟨636959, by rfl⟩ : syracuseStep 849279 = 1273919) B1273919
theorem B849663 : Blo 846354 849663 := bstep (se 1 (by rfl) ⟨637247, by rfl⟩ : syracuseStep 849663 = 1274495) B1274495
theorem B19593083 : Blo 846354 19593083 := bstep (se 1 (by rfl) ⟨14694812, by rfl⟩ : syracuseStep 19593083 = 29389625) B29389625
theorem B18315341 : Blo 846354 18315341 := bstep (se 3 (by rfl) ⟨3434126, by rfl⟩ : syracuseStep 18315341 = 6868253) B6868253
theorem B4356317 : Blo 846354 4356317 := bstep (se 3 (by rfl) ⟨816809, by rfl⟩ : syracuseStep 4356317 = 1633619) B1633619
theorem B850239 : Blo 846354 850239 := bstep (se 1 (by rfl) ⟨637679, by rfl⟩ : syracuseStep 850239 = 1275359) B1275359
theorem B850331 : Blo 846354 850331 := bstep (se 1 (by rfl) ⟨637748, by rfl⟩ : syracuseStep 850331 = 1275497) B1275497
theorem B4291865 : Blo 846354 4291865 := bstep (se 2 (by rfl) ⟨1609449, by rfl⟩ : syracuseStep 4291865 = 3218899) B3218899
theorem B8160871 : Blo 846354 8160871 := bstep (se 1 (by rfl) ⟨6120653, by rfl⟩ : syracuseStep 8160871 = 12241307) B12241307
theorem B23169199 : Blo 846354 23169199 := bstep (se 1 (by rfl) ⟨17376899, by rfl⟩ : syracuseStep 23169199 = 34753799) B34753799
theorem B2722535 : Blo 846354 2722535 := bstep (se 1 (by rfl) ⟨2041901, by rfl⟩ : syracuseStep 2722535 = 4083803) B4083803
theorem B2034953 : Blo 846354 2034953 := bstep (se 2 (by rfl) ⟨763107, by rfl⟩ : syracuseStep 2034953 = 1526215) B1526215
theorem B111742267 : Blo 846354 111742267 := bstep (se 1 (by rfl) ⟨83806700, by rfl⟩ : syracuseStep 111742267 = 167613401) B167613401
theorem B2297983 : Blo 846354 2297983 := bstep (se 1 (by rfl) ⟨1723487, by rfl⟩ : syracuseStep 2297983 = 3446975) B3446975
theorem B954607 : Blo 846354 954607 := bstep (se 1 (by rfl) ⟨715955, by rfl⟩ : syracuseStep 954607 = 1431911) B1431911
theorem B353341835 : Blo 846354 353341835 := bstep (se 1 (by rfl) ⟨265006376, by rfl⟩ : syracuseStep 353341835 = 530012753) B530012753
theorem B4592159 : Blo 846354 4592159 := bstep (se 1 (by rfl) ⟨3444119, by rfl⟩ : syracuseStep 4592159 = 6888239) B6888239
theorem B4068215 : Blo 846354 4068215 := bstep (se 1 (by rfl) ⟨3051161, by rfl⟩ : syracuseStep 4068215 = 6102323) B6102323
theorem B1610695 : Blo 846354 1610695 := bstep (se 1 (by rfl) ⟨1208021, by rfl⟩ : syracuseStep 1610695 = 2416043) B2416043
theorem B4363399 : Blo 846354 4363399 := bstep (se 1 (by rfl) ⟨3272549, by rfl⟩ : syracuseStep 4363399 = 6545099) B6545099
theorem B2857679 : Blo 846354 2857679 := bstep (se 1 (by rfl) ⟨2143259, by rfl⟩ : syracuseStep 2857679 = 4286519) B4286519
theorem B4823975 : Blo 846354 4823975 := bstep (se 1 (by rfl) ⟨3617981, by rfl⟩ : syracuseStep 4823975 = 7235963) B7235963
theorem B2858057 : Blo 846354 2858057 := bstep (se 2 (by rfl) ⟨1071771, by rfl⟩ : syracuseStep 2858057 = 2143543) B2143543
theorem B2858111 : Blo 846354 2858111 := bstep (se 1 (by rfl) ⟨2143583, by rfl⟩ : syracuseStep 2858111 = 4287167) B4287167
theorem B1908431 : Blo 846354 1908431 := bstep (se 1 (by rfl) ⟨1431323, by rfl⟩ : syracuseStep 1908431 = 2862647) B2862647
theorem B6889535 : Blo 846354 6889535 := bstep (se 1 (by rfl) ⟨5167151, by rfl⟩ : syracuseStep 6889535 = 10334303) B10334303
theorem B3221147 : Blo 846354 3221147 := bstep (se 1 (by rfl) ⟨2415860, by rfl⟩ : syracuseStep 3221147 = 4831721) B4831721
theorem B2861243 : Blo 846354 2861243 := bstep (se 1 (by rfl) ⟨2145932, by rfl⟩ : syracuseStep 2861243 = 4291865) B4291865
theorem B12234215 : Blo 846354 12234215 := bstep (se 1 (by rfl) ⟨9175661, by rfl⟩ : syracuseStep 12234215 = 18351323) B18351323
theorem B1913057 : Blo 846354 1913057 := bstep (se 2 (by rfl) ⟨717396, by rfl⟩ : syracuseStep 1913057 = 1434793) B1434793
theorem B2897207 : Blo 846354 2897207 := bstep (se 1 (by rfl) ⟨2172905, by rfl⟩ : syracuseStep 2897207 = 4345811) B4345811
theorem B2864591 : Blo 846354 2864591 := bstep (se 1 (by rfl) ⟨2148443, by rfl⟩ : syracuseStep 2864591 = 4296887) B4296887
theorem B9156635 : Blo 846354 9156635 := bstep (se 1 (by rfl) ⟨6867476, by rfl⟩ : syracuseStep 9156635 = 13734953) B13734953
theorem B151108537 : Blo 846354 151108537 := bstep (se 2 (by rfl) ⟨56665701, by rfl⟩ : syracuseStep 151108537 = 113331403) B113331403
theorem B10861735 : Blo 846354 10861735 := bstep (se 1 (by rfl) ⟨8146301, by rfl⟩ : syracuseStep 10861735 = 16292603) B16292603
theorem B3262639 : Blo 846354 3262639 := bstep (se 1 (by rfl) ⟨2446979, by rfl⟩ : syracuseStep 3262639 = 4893959) B4893959
theorem B1429339 : Blo 846354 1429339 := bstep (se 1 (by rfl) ⟨1072004, by rfl⟩ : syracuseStep 1429339 = 2144009) B2144009
theorem B13062055 : Blo 846354 13062055 := bstep (se 1 (by rfl) ⟨9796541, by rfl⟩ : syracuseStep 13062055 = 19593083) B19593083
theorem B12210227 : Blo 846354 12210227 := bstep (se 1 (by rfl) ⟨9157670, by rfl⟩ : syracuseStep 12210227 = 18315341) B18315341
theorem B2904211 : Blo 846354 2904211 := bstep (se 1 (by rfl) ⟨2178158, by rfl⟩ : syracuseStep 2904211 = 4356317) B4356317
theorem B1430311 : Blo 846354 1430311 := bstep (se 1 (by rfl) ⟨1072733, by rfl⟩ : syracuseStep 1430311 = 2145467) B2145467
theorem B2413435 : Blo 846354 2413435 := bstep (se 1 (by rfl) ⟨1810076, by rfl⟩ : syracuseStep 2413435 = 3620153) B3620153
theorem B1430399 : Blo 846354 1430399 := bstep (se 1 (by rfl) ⟨1072799, by rfl⟩ : syracuseStep 1430399 = 2145599) B2145599
theorem B1431607 : Blo 846354 1431607 := bstep (se 1 (by rfl) ⟨1073705, by rfl⟩ : syracuseStep 1431607 = 2147411) B2147411
theorem B58710743 : Blo 846354 58710743 := bstep (se 1 (by rfl) ⟨44033057, by rfl⟩ : syracuseStep 58710743 = 88066115) B88066115
theorem B1072111 : Blo 846354 1072111 := bstep (se 1 (by rfl) ⟨804083, by rfl⟩ : syracuseStep 1072111 = 1608167) B1608167
theorem B15457807 : Blo 846354 15457807 := bstep (se 1 (by rfl) ⟨11593355, by rfl⟩ : syracuseStep 15457807 = 23186711) B23186711
theorem B1434395 : Blo 846354 1434395 := bstep (se 1 (by rfl) ⟨1075796, by rfl⟩ : syracuseStep 1434395 = 2151593) B2151593
theorem B2712359 : Blo 846354 2712359 := bstep (se 1 (by rfl) ⟨2034269, by rfl⟩ : syracuseStep 2712359 = 4068539) B4068539
theorem B1270697 : Blo 846354 1270697 := bstep (se 2 (by rfl) ⟨476511, by rfl⟩ : syracuseStep 1270697 = 953023) B953023
theorem B1271207 : Blo 846354 1271207 := bstep (se 1 (by rfl) ⟨953405, by rfl⟩ : syracuseStep 1271207 = 1906811) B1906811
theorem B6449705 : Blo 846354 6449705 := bstep (se 2 (by rfl) ⟨2418639, by rfl⟩ : syracuseStep 6449705 = 4837279) B4837279
theorem B846463 : Blo 846354 846463 := bstep (se 1 (by rfl) ⟨634847, by rfl⟩ : syracuseStep 846463 = 1269695) B1269695
theorem B846527 : Blo 846354 846527 := bstep (se 1 (by rfl) ⟨634895, by rfl⟩ : syracuseStep 846527 = 1269791) B1269791
theorem B1272575 : Blo 846354 1272575 := bstep (se 1 (by rfl) ⟨954431, by rfl⟩ : syracuseStep 1272575 = 1908863) B1908863
theorem B6122303 : Blo 846354 6122303 := bstep (se 1 (by rfl) ⟨4591727, by rfl⟩ : syracuseStep 6122303 = 9183455) B9183455
theorem B847295 : Blo 846354 847295 := bstep (se 1 (by rfl) ⟨635471, by rfl⟩ : syracuseStep 847295 = 1270943) B1270943
theorem B36662867 : Blo 846354 36662867 := bstep (se 1 (by rfl) ⟨27497150, by rfl⟩ : syracuseStep 36662867 = 54994301) B54994301
theorem B1273499 : Blo 846354 1273499 := bstep (se 1 (by rfl) ⟨955124, by rfl⟩ : syracuseStep 1273499 = 1910249) B1910249
theorem B847599 : Blo 846354 847599 := bstep (se 1 (by rfl) ⟨635699, by rfl⟩ : syracuseStep 847599 = 1271399) B1271399
theorem B1273679 : Blo 846354 1273679 := bstep (se 1 (by rfl) ⟨955259, by rfl⟩ : syracuseStep 1273679 = 1910519) B1910519
theorem B847983 : Blo 846354 847983 := bstep (se 1 (by rfl) ⟨635987, by rfl⟩ : syracuseStep 847983 = 1271975) B1271975
theorem B1273967 : Blo 846354 1273967 := bstep (se 1 (by rfl) ⟨955475, by rfl⟩ : syracuseStep 1273967 = 1910951) B1910951
theorem B848039 : Blo 846354 848039 := bstep (se 1 (by rfl) ⟨636029, by rfl⟩ : syracuseStep 848039 = 1272059) B1272059
theorem B6124319 : Blo 846354 6124319 := bstep (se 1 (by rfl) ⟨4593239, by rfl⟩ : syracuseStep 6124319 = 9186479) B9186479
theorem B2716487 : Blo 846354 2716487 := bstep (se 1 (by rfl) ⟨2037365, by rfl⟩ : syracuseStep 2716487 = 4074731) B4074731
theorem B8155991 : Blo 846354 8155991 := bstep (se 1 (by rfl) ⟨6116993, by rfl⟩ : syracuseStep 8155991 = 12233987) B12233987
theorem B848895 : Blo 846354 848895 := bstep (se 1 (by rfl) ⟨636671, by rfl⟩ : syracuseStep 848895 = 1273343) B1273343
theorem B849135 : Blo 846354 849135 := bstep (se 1 (by rfl) ⟨636851, by rfl⟩ : syracuseStep 849135 = 1273703) B1273703
theorem B849255 : Blo 846354 849255 := bstep (se 1 (by rfl) ⟨636941, by rfl⟩ : syracuseStep 849255 = 1273883) B1273883
theorem B1275239 : Blo 846354 1275239 := bstep (se 1 (by rfl) ⟨956429, by rfl⟩ : syracuseStep 1275239 = 1912859) B1912859
theorem B1473643 : Blo 846354 1473643 := bstep (se 1 (by rfl) ⟨1105232, by rfl⟩ : syracuseStep 1473643 = 2210465) B2210465
theorem B1932959 : Blo 846354 1932959 := bstep (se 1 (by rfl) ⟨1449719, by rfl⟩ : syracuseStep 1932959 = 2899439) B2899439
theorem B10881161 : Blo 846354 10881161 := bstep (se 2 (by rfl) ⟨4080435, by rfl⟩ : syracuseStep 10881161 = 8160871) B8160871
theorem B953599 : Blo 846354 953599 := bstep (se 1 (by rfl) ⟨715199, by rfl⟩ : syracuseStep 953599 = 1430399) B1430399
theorem B1905119 : Blo 846354 1905119 := bstep (se 1 (by rfl) ⟨1428839, by rfl⟩ : syracuseStep 1905119 = 2857679) B2857679
theorem B3215983 : Blo 846354 3215983 := bstep (se 1 (by rfl) ⟨2411987, by rfl⟩ : syracuseStep 3215983 = 4823975) B4823975
theorem B1905371 : Blo 846354 1905371 := bstep (se 1 (by rfl) ⟨1429028, by rfl⟩ : syracuseStep 1905371 = 2858057) B2858057
theorem B1905407 : Blo 846354 1905407 := bstep (se 1 (by rfl) ⟨1429055, by rfl⟩ : syracuseStep 1905407 = 2858111) B2858111
theorem B1905785 : Blo 846354 1905785 := bstep (se 2 (by rfl) ⟨714669, by rfl⟩ : syracuseStep 1905785 = 1429339) B1429339
theorem B4593023 : Blo 846354 4593023 := bstep (se 1 (by rfl) ⟨3444767, by rfl⟩ : syracuseStep 4593023 = 6889535) B6889535
theorem B3872281 : Blo 846354 3872281 := bstep (se 2 (by rfl) ⟨1452105, by rfl⟩ : syracuseStep 3872281 = 2904211) B2904211
theorem B956263 : Blo 846354 956263 := bstep (se 1 (by rfl) ⟨717197, by rfl⟩ : syracuseStep 956263 = 1434395) B1434395
theorem B1808239 : Blo 846354 1808239 := bstep (se 1 (by rfl) ⟨1356179, by rfl⟩ : syracuseStep 1808239 = 2712359) B2712359
theorem B1907081 : Blo 846354 1907081 := bstep (se 2 (by rfl) ⟨715155, by rfl⟩ : syracuseStep 1907081 = 1430311) B1430311
theorem B3217913 : Blo 846354 3217913 := bstep (se 2 (by rfl) ⟨1206717, by rfl⟩ : syracuseStep 3217913 = 2413435) B2413435
theorem B1907495 : Blo 846354 1907495 := bstep (se 1 (by rfl) ⟨1430621, by rfl⟩ : syracuseStep 1907495 = 2861243) B2861243
theorem B4299803 : Blo 846354 4299803 := bstep (se 1 (by rfl) ⟨3224852, by rfl⟩ : syracuseStep 4299803 = 6449705) B6449705
theorem B1908809 : Blo 846354 1908809 := bstep (se 2 (by rfl) ⟨715803, by rfl⟩ : syracuseStep 1908809 = 1431607) B1431607
theorem B1810991 : Blo 846354 1810991 := bstep (se 1 (by rfl) ⟨1358243, by rfl⟩ : syracuseStep 1810991 = 2716487) B2716487
theorem B1909727 : Blo 846354 1909727 := bstep (se 1 (by rfl) ⟨1432295, by rfl⟩ : syracuseStep 1909727 = 2864591) B2864591
theorem B6104423 : Blo 846354 6104423 := bstep (se 1 (by rfl) ⟨4578317, by rfl⟩ : syracuseStep 6104423 = 9156635) B9156635
theorem B1288639 : Blo 846354 1288639 := bstep (se 1 (by rfl) ⟨966479, by rfl⟩ : syracuseStep 1288639 = 1932959) B1932959
theorem B1815023 : Blo 846354 1815023 := bstep (se 1 (by rfl) ⟨1361267, by rfl⟩ : syracuseStep 1815023 = 2722535) B2722535
theorem B1356635 : Blo 846354 1356635 := bstep (se 1 (by rfl) ⟨1017476, by rfl⟩ : syracuseStep 1356635 = 2034953) B2034953
theorem B8140151 : Blo 846354 8140151 := bstep (se 1 (by rfl) ⟨6105113, by rfl⟩ : syracuseStep 8140151 = 12210227) B12210227
theorem B3061439 : Blo 846354 3061439 := bstep (se 1 (by rfl) ⟨2296079, by rfl⟩ : syracuseStep 3061439 = 4592159) B4592159
theorem B39140495 : Blo 846354 39140495 := bstep (se 1 (by rfl) ⟨29355371, by rfl⟩ : syracuseStep 39140495 = 58710743) B58710743
theorem B17416073 : Blo 846354 17416073 := bstep (se 2 (by rfl) ⟨6531027, by rfl⟩ : syracuseStep 17416073 = 13062055) B13062055
theorem B3063977 : Blo 846354 3063977 := bstep (se 2 (by rfl) ⟨1148991, by rfl⟩ : syracuseStep 3063977 = 2297983) B2297983
theorem B2147431 : Blo 846354 2147431 := bstep (se 1 (by rfl) ⟨1610573, by rfl⟩ : syracuseStep 2147431 = 3221147) B3221147
theorem B2147593 : Blo 846354 2147593 := bstep (se 2 (by rfl) ⟨805347, by rfl⟩ : syracuseStep 2147593 = 1610695) B1610695
theorem B5817865 : Blo 846354 5817865 := bstep (se 2 (by rfl) ⟨2181699, by rfl⟩ : syracuseStep 5817865 = 4363399) B4363399
theorem B4081535 : Blo 846354 4081535 := bstep (se 1 (by rfl) ⟨3061151, by rfl⟩ : syracuseStep 4081535 = 6122303) B6122303
theorem B4082879 : Blo 846354 4082879 := bstep (se 1 (by rfl) ⟨3062159, by rfl⟩ : syracuseStep 4082879 = 6124319) B6124319
theorem B201478049 : Blo 846354 201478049 := bstep (se 2 (by rfl) ⟨75554268, by rfl⟩ : syracuseStep 201478049 = 151108537) B151108537
theorem B1429481 : Blo 846354 1429481 := bstep (se 2 (by rfl) ⟨536055, by rfl⟩ : syracuseStep 1429481 = 1072111) B1072111
theorem B30892265 : Blo 846354 30892265 := bstep (se 2 (by rfl) ⟨11584599, by rfl⟩ : syracuseStep 30892265 = 23169199) B23169199
theorem B4350185 : Blo 846354 4350185 := bstep (se 2 (by rfl) ⟨1631319, by rfl⟩ : syracuseStep 4350185 = 3262639) B3262639
theorem B235561223 : Blo 846354 235561223 := bstep (se 1 (by rfl) ⟨176670917, by rfl⟩ : syracuseStep 235561223 = 353341835) B353341835
theorem B2712143 : Blo 846354 2712143 := bstep (se 1 (by rfl) ⟨2034107, by rfl⟩ : syracuseStep 2712143 = 4068215) B4068215
theorem B148989689 : Blo 846354 148989689 := bstep (se 2 (by rfl) ⟨55871133, by rfl⟩ : syracuseStep 148989689 = 111742267) B111742267
theorem B1272287 : Blo 846354 1272287 := bstep (se 1 (by rfl) ⟨954215, by rfl⟩ : syracuseStep 1272287 = 1908431) B1908431
theorem B1272809 : Blo 846354 1272809 := bstep (se 2 (by rfl) ⟨477303, by rfl⟩ : syracuseStep 1272809 = 954607) B954607
theorem B7859429 : Blo 846354 7859429 := bstep (se 4 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 7859429 = 1473643) B1473643
theorem B847131 : Blo 846354 847131 := bstep (se 1 (by rfl) ⟨635348, by rfl⟩ : syracuseStep 847131 = 1270697) B1270697
theorem B847471 : Blo 846354 847471 := bstep (se 1 (by rfl) ⟨635603, by rfl⟩ : syracuseStep 847471 = 1271207) B1271207
theorem B848383 : Blo 846354 848383 := bstep (se 1 (by rfl) ⟨636287, by rfl⟩ : syracuseStep 848383 = 1272575) B1272575
theorem B8156143 : Blo 846354 8156143 := bstep (se 1 (by rfl) ⟨6117107, by rfl⟩ : syracuseStep 8156143 = 12234215) B12234215
theorem B24441911 : Blo 846354 24441911 := bstep (se 1 (by rfl) ⟨18331433, by rfl⟩ : syracuseStep 24441911 = 36662867) B36662867
theorem B848999 : Blo 846354 848999 := bstep (se 1 (by rfl) ⟨636749, by rfl⟩ : syracuseStep 848999 = 1273499) B1273499
theorem B849119 : Blo 846354 849119 := bstep (se 1 (by rfl) ⟨636839, by rfl⟩ : syracuseStep 849119 = 1273679) B1273679
theorem B849311 : Blo 846354 849311 := bstep (se 1 (by rfl) ⟨636983, by rfl⟩ : syracuseStep 849311 = 1273967) B1273967
theorem B1275371 : Blo 846354 1275371 := bstep (se 1 (by rfl) ⟨956528, by rfl⟩ : syracuseStep 1275371 = 1913057) B1913057
theorem B5437327 : Blo 846354 5437327 := bstep (se 1 (by rfl) ⟨4077995, by rfl⟩ : syracuseStep 5437327 = 8155991) B8155991
theorem B1931471 : Blo 846354 1931471 := bstep (se 1 (by rfl) ⟨1448603, by rfl⟩ : syracuseStep 1931471 = 2897207) B2897207
theorem B850159 : Blo 846354 850159 := bstep (se 1 (by rfl) ⟨637619, by rfl⟩ : syracuseStep 850159 = 1275239) B1275239
theorem B14482313 : Blo 846354 14482313 := bstep (se 2 (by rfl) ⟨5430867, by rfl⟩ : syracuseStep 14482313 = 10861735) B10861735
theorem B20610409 : Blo 846354 20610409 := bstep (se 2 (by rfl) ⟨7728903, by rfl⟩ : syracuseStep 20610409 = 15457807) B15457807
theorem B628163261 : Blo 846354 628163261 := bstep (se 3 (by rfl) ⟨117780611, by rfl⟩ : syracuseStep 628163261 = 235561223) B235561223
theorem B2721023 : Blo 846354 2721023 := bstep (se 1 (by rfl) ⟨2040767, by rfl⟩ : syracuseStep 2721023 = 4081535) B4081535
theorem B2721919 : Blo 846354 2721919 := bstep (se 1 (by rfl) ⟨2041439, by rfl⟩ : syracuseStep 2721919 = 4082879) B4082879
theorem B134318699 : Blo 846354 134318699 := bstep (se 1 (by rfl) ⟨100739024, by rfl⟩ : syracuseStep 134318699 = 201478049) B201478049
theorem B952987 : Blo 846354 952987 := bstep (se 1 (by rfl) ⟨714740, by rfl⟩ : syracuseStep 952987 = 1429481) B1429481
theorem B1808095 : Blo 846354 1808095 := bstep (se 1 (by rfl) ⟨1356071, by rfl⟩ : syracuseStep 1808095 = 2712143) B2712143
theorem B4069615 : Blo 846354 4069615 := bstep (se 1 (by rfl) ⟨3052211, by rfl⟩ : syracuseStep 4069615 = 6104423) B6104423
theorem B99326459 : Blo 846354 99326459 := bstep (se 1 (by rfl) ⟨74494844, by rfl⟩ : syracuseStep 99326459 = 148989689) B148989689
theorem B7249769 : Blo 846354 7249769 := bstep (se 2 (by rfl) ⟨2718663, by rfl⟩ : syracuseStep 7249769 = 5437327) B5437327
theorem B16294607 : Blo 846354 16294607 := bstep (se 1 (by rfl) ⟨12220955, by rfl⟩ : syracuseStep 16294607 = 24441911) B24441911
theorem B2040959 : Blo 846354 2040959 := bstep (se 1 (by rfl) ⟨1530719, by rfl⟩ : syracuseStep 2040959 = 3061439) B3061439
theorem B1287647 : Blo 846354 1287647 := bstep (se 1 (by rfl) ⟨965735, by rfl⟩ : syracuseStep 1287647 = 1931471) B1931471
theorem B26093663 : Blo 846354 26093663 := bstep (se 1 (by rfl) ⟨19570247, by rfl⟩ : syracuseStep 26093663 = 39140495) B39140495
theorem B11610715 : Blo 846354 11610715 := bstep (se 1 (by rfl) ⟨8708036, by rfl⟩ : syracuseStep 11610715 = 17416073) B17416073
theorem B2042651 : Blo 846354 2042651 := bstep (se 1 (by rfl) ⟨1531988, by rfl⟩ : syracuseStep 2042651 = 3063977) B3063977
theorem B7254107 : Blo 846354 7254107 := bstep (se 1 (by rfl) ⟨5440580, by rfl⟩ : syracuseStep 7254107 = 10881161) B10881161
theorem B2863241 : Blo 846354 2863241 := bstep (se 2 (by rfl) ⟨1073715, by rfl⟩ : syracuseStep 2863241 = 2147431) B2147431
theorem B2863457 : Blo 846354 2863457 := bstep (se 2 (by rfl) ⟨1073796, by rfl⟩ : syracuseStep 2863457 = 2147593) B2147593
theorem B3617693 : Blo 846354 3617693 := bstep (se 3 (by rfl) ⟨678317, by rfl⟩ : syracuseStep 3617693 = 1356635) B1356635
theorem B1718185 : Blo 846354 1718185 := bstep (se 2 (by rfl) ⟨644319, by rfl⟩ : syracuseStep 1718185 = 1288639) B1288639
theorem B3062015 : Blo 846354 3062015 := bstep (se 1 (by rfl) ⟨2296511, by rfl⟩ : syracuseStep 3062015 = 4593023) B4593023
theorem B2145275 : Blo 846354 2145275 := bstep (se 1 (by rfl) ⟨1608956, by rfl⟩ : syracuseStep 2145275 = 3217913) B3217913
theorem B2866535 : Blo 846354 2866535 := bstep (se 1 (by rfl) ⟨2149901, by rfl⟩ : syracuseStep 2866535 = 4299803) B4299803
theorem B20594843 : Blo 846354 20594843 := bstep (se 1 (by rfl) ⟨15446132, by rfl⟩ : syracuseStep 20594843 = 30892265) B30892265
theorem B2900123 : Blo 846354 2900123 := bstep (se 1 (by rfl) ⟨2175092, by rfl⟩ : syracuseStep 2900123 = 4350185) B4350185
theorem B5163041 : Blo 846354 5163041 := bstep (se 2 (by rfl) ⟨1936140, by rfl⟩ : syracuseStep 5163041 = 3872281) B3872281
theorem B2410985 : Blo 846354 2410985 := bstep (se 2 (by rfl) ⟨904119, by rfl⟩ : syracuseStep 2410985 = 1808239) B1808239
theorem B5426767 : Blo 846354 5426767 := bstep (se 1 (by rfl) ⟨4070075, by rfl⟩ : syracuseStep 5426767 = 8140151) B8140151
theorem B27480545 : Blo 846354 27480545 := bstep (se 2 (by rfl) ⟨10305204, by rfl⟩ : syracuseStep 27480545 = 20610409) B20610409
theorem B9654875 : Blo 846354 9654875 := bstep (se 1 (by rfl) ⟨7241156, by rfl⟩ : syracuseStep 9654875 = 14482313) B14482313
theorem B7757153 : Blo 846354 7757153 := bstep (se 2 (by rfl) ⟨2908932, by rfl⟩ : syracuseStep 7757153 = 5817865) B5817865
theorem B1270079 : Blo 846354 1270079 := bstep (se 1 (by rfl) ⟨952559, by rfl⟩ : syracuseStep 1270079 = 1905119) B1905119
theorem B1270247 : Blo 846354 1270247 := bstep (se 1 (by rfl) ⟨952685, by rfl⟩ : syracuseStep 1270247 = 1905371) B1905371
theorem B1270271 : Blo 846354 1270271 := bstep (se 1 (by rfl) ⟨952703, by rfl⟩ : syracuseStep 1270271 = 1905407) B1905407
theorem B1270523 : Blo 846354 1270523 := bstep (se 1 (by rfl) ⟨952892, by rfl⟩ : syracuseStep 1270523 = 1905785) B1905785
theorem B1271387 : Blo 846354 1271387 := bstep (se 1 (by rfl) ⟨953540, by rfl⟩ : syracuseStep 1271387 = 1907081) B1907081
theorem B1271465 : Blo 846354 1271465 := bstep (se 2 (by rfl) ⟨476799, by rfl⟩ : syracuseStep 1271465 = 953599) B953599
theorem B1271663 : Blo 846354 1271663 := bstep (se 1 (by rfl) ⟨953747, by rfl⟩ : syracuseStep 1271663 = 1907495) B1907495
theorem B1272539 : Blo 846354 1272539 := bstep (se 1 (by rfl) ⟨954404, by rfl⟩ : syracuseStep 1272539 = 1908809) B1908809
theorem B1207327 : Blo 846354 1207327 := bstep (se 1 (by rfl) ⟨905495, by rfl⟩ : syracuseStep 1207327 = 1810991) B1810991
theorem B1273151 : Blo 846354 1273151 := bstep (se 1 (by rfl) ⟨954863, by rfl⟩ : syracuseStep 1273151 = 1909727) B1909727
theorem B4287977 : Blo 846354 4287977 := bstep (se 2 (by rfl) ⟨1607991, by rfl⟩ : syracuseStep 4287977 = 3215983) B3215983
theorem B10874857 : Blo 846354 10874857 := bstep (se 2 (by rfl) ⟨4078071, by rfl⟩ : syracuseStep 10874857 = 8156143) B8156143
theorem B848191 : Blo 846354 848191 := bstep (se 1 (by rfl) ⟨636143, by rfl⟩ : syracuseStep 848191 = 1272287) B1272287
theorem B848539 : Blo 846354 848539 := bstep (se 1 (by rfl) ⟨636404, by rfl⟩ : syracuseStep 848539 = 1272809) B1272809
theorem B5239619 : Blo 846354 5239619 := bstep (se 1 (by rfl) ⟨3929714, by rfl⟩ : syracuseStep 5239619 = 7859429) B7859429
theorem B1275017 : Blo 846354 1275017 := bstep (se 2 (by rfl) ⟨478131, by rfl⟩ : syracuseStep 1275017 = 956263) B956263
theorem B1210015 : Blo 846354 1210015 := bstep (se 1 (by rfl) ⟨907511, by rfl⟩ : syracuseStep 1210015 = 1815023) B1815023
theorem B850247 : Blo 846354 850247 := bstep (se 1 (by rfl) ⟨637685, by rfl⟩ : syracuseStep 850247 = 1275371) B1275371
theorem B13729895 : Blo 846354 13729895 := bstep (se 1 (by rfl) ⟨10297421, by rfl⟩ : syracuseStep 13729895 = 20594843) B20594843
theorem B1933415 : Blo 846354 1933415 := bstep (se 1 (by rfl) ⟨1450061, by rfl⟩ : syracuseStep 1933415 = 2900123) B2900123
theorem B418775507 : Blo 846354 418775507 := bstep (se 1 (by rfl) ⟨314081630, by rfl⟩ : syracuseStep 418775507 = 628163261) B628163261
theorem B3442027 : Blo 846354 3442027 := bstep (se 1 (by rfl) ⟨2581520, by rfl⟩ : syracuseStep 3442027 = 5163041) B5163041
theorem B18320363 : Blo 846354 18320363 := bstep (se 1 (by rfl) ⟨13740272, by rfl⟩ : syracuseStep 18320363 = 27480545) B27480545
theorem B1609769 : Blo 846354 1609769 := bstep (se 2 (by rfl) ⟨603663, by rfl⟩ : syracuseStep 1609769 = 1207327) B1207327
theorem B858431 : Blo 846354 858431 := bstep (se 1 (by rfl) ⟨643823, by rfl⟩ : syracuseStep 858431 = 1287647) B1287647
theorem B6429293 : Blo 846354 6429293 := bstep (se 3 (by rfl) ⟨1205492, by rfl⟩ : syracuseStep 6429293 = 2410985) B2410985
theorem B264870557 : Blo 846354 264870557 := bstep (se 3 (by rfl) ⟨49663229, by rfl⟩ : syracuseStep 264870557 = 99326459) B99326459
theorem B1613353 : Blo 846354 1613353 := bstep (se 2 (by rfl) ⟨605007, by rfl⟩ : syracuseStep 1613353 = 1210015) B1210015
theorem B2858651 : Blo 846354 2858651 := bstep (se 1 (by rfl) ⟨2143988, by rfl⟩ : syracuseStep 2858651 = 4287977) B4287977
theorem B1908827 : Blo 846354 1908827 := bstep (se 1 (by rfl) ⟨1431620, by rfl⟩ : syracuseStep 1908827 = 2863241) B2863241
theorem B1908971 : Blo 846354 1908971 := bstep (se 1 (by rfl) ⟨1431728, by rfl⟩ : syracuseStep 1908971 = 2863457) B2863457
theorem B2041343 : Blo 846354 2041343 := bstep (se 1 (by rfl) ⟨1531007, by rfl⟩ : syracuseStep 2041343 = 3062015) B3062015
theorem B1911023 : Blo 846354 1911023 := bstep (se 1 (by rfl) ⟨1433267, by rfl⟩ : syracuseStep 1911023 = 2866535) B2866535
theorem B1814015 : Blo 846354 1814015 := bstep (se 1 (by rfl) ⟨1360511, by rfl⟩ : syracuseStep 1814015 = 2721023) B2721023
theorem B6436583 : Blo 846354 6436583 := bstep (se 1 (by rfl) ⟨4827437, by rfl⟩ : syracuseStep 6436583 = 9654875) B9654875
theorem B15480953 : Blo 846354 15480953 := bstep (se 2 (by rfl) ⟨5805357, by rfl⟩ : syracuseStep 15480953 = 11610715) B11610715
theorem B4833179 : Blo 846354 4833179 := bstep (se 1 (by rfl) ⟨3624884, by rfl⟩ : syracuseStep 4833179 = 7249769) B7249769
theorem B14499809 : Blo 846354 14499809 := bstep (se 2 (by rfl) ⟨5437428, by rfl⟩ : syracuseStep 14499809 = 10874857) B10874857
theorem B10863071 : Blo 846354 10863071 := bstep (se 1 (by rfl) ⟨8147303, by rfl⟩ : syracuseStep 10863071 = 16294607) B16294607
theorem B1360639 : Blo 846354 1360639 := bstep (se 1 (by rfl) ⟨1020479, by rfl⟩ : syracuseStep 1360639 = 2040959) B2040959
theorem B1361767 : Blo 846354 1361767 := bstep (se 1 (by rfl) ⟨1021325, by rfl⟩ : syracuseStep 1361767 = 2042651) B2042651
theorem B2410793 : Blo 846354 2410793 := bstep (se 2 (by rfl) ⟨904047, by rfl⟩ : syracuseStep 2410793 = 1808095) B1808095
theorem B4836071 : Blo 846354 4836071 := bstep (se 1 (by rfl) ⟨3627053, by rfl⟩ : syracuseStep 4836071 = 7254107) B7254107
theorem B5426153 : Blo 846354 5426153 := bstep (se 2 (by rfl) ⟨2034807, by rfl⟩ : syracuseStep 5426153 = 4069615) B4069615
theorem B3493079 : Blo 846354 3493079 := bstep (se 1 (by rfl) ⟨2619809, by rfl⟩ : syracuseStep 3493079 = 5239619) B5239619
theorem B2411795 : Blo 846354 2411795 := bstep (se 1 (by rfl) ⟨1808846, by rfl⟩ : syracuseStep 2411795 = 3617693) B3617693
theorem B1430183 : Blo 846354 1430183 := bstep (se 1 (by rfl) ⟨1072637, by rfl⟩ : syracuseStep 1430183 = 2145275) B2145275
theorem B89545799 : Blo 846354 89545799 := bstep (se 1 (by rfl) ⟨67159349, by rfl⟩ : syracuseStep 89545799 = 134318699) B134318699
theorem B3629225 : Blo 846354 3629225 := bstep (se 2 (by rfl) ⟨1360959, by rfl⟩ : syracuseStep 3629225 = 2721919) B2721919
theorem B1270649 : Blo 846354 1270649 := bstep (se 2 (by rfl) ⟨476493, by rfl⟩ : syracuseStep 1270649 = 952987) B952987
theorem B7235689 : Blo 846354 7235689 := bstep (se 2 (by rfl) ⟨2713383, by rfl⟩ : syracuseStep 7235689 = 5426767) B5426767
theorem B5171435 : Blo 846354 5171435 := bstep (se 1 (by rfl) ⟨3878576, by rfl⟩ : syracuseStep 5171435 = 7757153) B7757153
theorem B846719 : Blo 846354 846719 := bstep (se 1 (by rfl) ⟨635039, by rfl⟩ : syracuseStep 846719 = 1270079) B1270079
theorem B846831 : Blo 846354 846831 := bstep (se 1 (by rfl) ⟨635123, by rfl⟩ : syracuseStep 846831 = 1270247) B1270247
theorem B846847 : Blo 846354 846847 := bstep (se 1 (by rfl) ⟨635135, by rfl⟩ : syracuseStep 846847 = 1270271) B1270271
theorem B847015 : Blo 846354 847015 := bstep (se 1 (by rfl) ⟨635261, by rfl⟩ : syracuseStep 847015 = 1270523) B1270523
theorem B847591 : Blo 846354 847591 := bstep (se 1 (by rfl) ⟨635693, by rfl⟩ : syracuseStep 847591 = 1271387) B1271387
theorem B847643 : Blo 846354 847643 := bstep (se 1 (by rfl) ⟨635732, by rfl⟩ : syracuseStep 847643 = 1271465) B1271465
theorem B847775 : Blo 846354 847775 := bstep (se 1 (by rfl) ⟨635831, by rfl⟩ : syracuseStep 847775 = 1271663) B1271663
theorem B17395775 : Blo 846354 17395775 := bstep (se 1 (by rfl) ⟨13046831, by rfl⟩ : syracuseStep 17395775 = 26093663) B26093663
theorem B848359 : Blo 846354 848359 := bstep (se 1 (by rfl) ⟨636269, by rfl⟩ : syracuseStep 848359 = 1272539) B1272539
theorem B848767 : Blo 846354 848767 := bstep (se 1 (by rfl) ⟨636575, by rfl⟩ : syracuseStep 848767 = 1273151) B1273151
theorem B2290913 : Blo 846354 2290913 := bstep (se 2 (by rfl) ⟨859092, by rfl⟩ : syracuseStep 2290913 = 1718185) B1718185
theorem B850011 : Blo 846354 850011 := bstep (se 1 (by rfl) ⟨637508, by rfl⟩ : syracuseStep 850011 = 1275017) B1275017
theorem B279183671 : Blo 846354 279183671 := bstep (se 1 (by rfl) ⟨209387753, by rfl⟩ : syracuseStep 279183671 = 418775507) B418775507
theorem B7242047 : Blo 846354 7242047 := bstep (se 1 (by rfl) ⟨5431535, by rfl⟩ : syracuseStep 7242047 = 10863071) B10863071
theorem B1607195 : Blo 846354 1607195 := bstep (se 1 (by rfl) ⟨1205396, by rfl⟩ : syracuseStep 1607195 = 2410793) B2410793
theorem B4589369 : Blo 846354 4589369 := bstep (se 2 (by rfl) ⟨1721013, by rfl⟩ : syracuseStep 4589369 = 3442027) B3442027
theorem B1607863 : Blo 846354 1607863 := bstep (se 1 (by rfl) ⟨1205897, by rfl⟩ : syracuseStep 1607863 = 2411795) B2411795
theorem B37259509 : Blo 846354 37259509 := bstep (se 5 (by rfl) ⟨1746539, by rfl⟩ : syracuseStep 37259509 = 3493079) B3493079
theorem B953455 : Blo 846354 953455 := bstep (se 1 (by rfl) ⟨715091, by rfl⟩ : syracuseStep 953455 = 1430183) B1430183
theorem B1905767 : Blo 846354 1905767 := bstep (se 1 (by rfl) ⟨1429325, by rfl⟩ : syracuseStep 1905767 = 2858651) B2858651
theorem B3447623 : Blo 846354 3447623 := bstep (se 1 (by rfl) ⟨2585717, by rfl⟩ : syracuseStep 3447623 = 5171435) B5171435
theorem B3222119 : Blo 846354 3222119 := bstep (se 1 (by rfl) ⟨2416589, by rfl⟩ : syracuseStep 3222119 = 4833179) B4833179
theorem B9153263 : Blo 846354 9153263 := bstep (se 1 (by rfl) ⟨6864947, by rfl⟩ : syracuseStep 9153263 = 13729895) B13729895
theorem B1288943 : Blo 846354 1288943 := bstep (se 1 (by rfl) ⟨966707, by rfl⟩ : syracuseStep 1288943 = 1933415) B1933415
theorem B1814185 : Blo 846354 1814185 := bstep (se 2 (by rfl) ⟨680319, by rfl⟩ : syracuseStep 1814185 = 1360639) B1360639
theorem B3617435 : Blo 846354 3617435 := bstep (se 1 (by rfl) ⟨2713076, by rfl⟩ : syracuseStep 3617435 = 5426153) B5426153
theorem B1815689 : Blo 846354 1815689 := bstep (se 2 (by rfl) ⟨680883, by rfl⟩ : syracuseStep 1815689 = 1361767) B1361767
theorem B9647585 : Blo 846354 9647585 := bstep (se 2 (by rfl) ⟨3617844, by rfl⟩ : syracuseStep 9647585 = 7235689) B7235689
theorem B1360895 : Blo 846354 1360895 := bstep (se 1 (by rfl) ⟨1020671, by rfl⟩ : syracuseStep 1360895 = 2041343) B2041343
theorem B12896189 : Blo 846354 12896189 := bstep (se 3 (by rfl) ⟨2418035, by rfl⟩ : syracuseStep 12896189 = 4836071) B4836071
theorem B1527275 : Blo 846354 1527275 := bstep (se 1 (by rfl) ⟨1145456, by rfl⟩ : syracuseStep 1527275 = 2290913) B2290913
theorem B2151137 : Blo 846354 2151137 := bstep (se 2 (by rfl) ⟨806676, by rfl⟩ : syracuseStep 2151137 = 1613353) B1613353
theorem B12213575 : Blo 846354 12213575 := bstep (se 1 (by rfl) ⟨9160181, by rfl⟩ : syracuseStep 12213575 = 18320363) B18320363
theorem B1073179 : Blo 846354 1073179 := bstep (se 1 (by rfl) ⟨804884, by rfl⟩ : syracuseStep 1073179 = 1609769) B1609769
theorem B4286195 : Blo 846354 4286195 := bstep (se 1 (by rfl) ⟨3214646, by rfl⟩ : syracuseStep 4286195 = 6429293) B6429293
theorem B176580371 : Blo 846354 176580371 := bstep (se 1 (by rfl) ⟨132435278, by rfl⟩ : syracuseStep 176580371 = 264870557) B264870557
theorem B59697199 : Blo 846354 59697199 := bstep (se 1 (by rfl) ⟨44772899, by rfl⟩ : syracuseStep 59697199 = 89545799) B89545799
theorem B1272551 : Blo 846354 1272551 := bstep (se 1 (by rfl) ⟨954413, by rfl⟩ : syracuseStep 1272551 = 1908827) B1908827
theorem B2419483 : Blo 846354 2419483 := bstep (se 1 (by rfl) ⟨1814612, by rfl⟩ : syracuseStep 2419483 = 3629225) B3629225
theorem B1272647 : Blo 846354 1272647 := bstep (se 1 (by rfl) ⟨954485, by rfl⟩ : syracuseStep 1272647 = 1908971) B1908971
theorem B847099 : Blo 846354 847099 := bstep (se 1 (by rfl) ⟨635324, by rfl⟩ : syracuseStep 847099 = 1270649) B1270649
theorem B2289149 : Blo 846354 2289149 := bstep (se 3 (by rfl) ⟨429215, by rfl⟩ : syracuseStep 2289149 = 858431) B858431
theorem B1274015 : Blo 846354 1274015 := bstep (se 1 (by rfl) ⟨955511, by rfl⟩ : syracuseStep 1274015 = 1911023) B1911023
theorem B1209343 : Blo 846354 1209343 := bstep (se 1 (by rfl) ⟨907007, by rfl⟩ : syracuseStep 1209343 = 1814015) B1814015
theorem B11597183 : Blo 846354 11597183 := bstep (se 1 (by rfl) ⟨8697887, by rfl⟩ : syracuseStep 11597183 = 17395775) B17395775
theorem B4291055 : Blo 846354 4291055 := bstep (se 1 (by rfl) ⟨3218291, by rfl⟩ : syracuseStep 4291055 = 6436583) B6436583
theorem B10320635 : Blo 846354 10320635 := bstep (se 1 (by rfl) ⟨7740476, by rfl⟩ : syracuseStep 10320635 = 15480953) B15480953
theorem B9666539 : Blo 846354 9666539 := bstep (se 1 (by rfl) ⟨7249904, by rfl⟩ : syracuseStep 9666539 = 14499809) B14499809
theorem B186122447 : Blo 846354 186122447 := bstep (se 1 (by rfl) ⟨139591835, by rfl⟩ : syracuseStep 186122447 = 279183671) B279183671
theorem B1018183 : Blo 846354 1018183 := bstep (se 1 (by rfl) ⟨763637, by rfl⟩ : syracuseStep 1018183 = 1527275) B1527275
theorem B79596265 : Blo 846354 79596265 := bstep (se 2 (by rfl) ⟨29848599, by rfl⟩ : syracuseStep 79596265 = 59697199) B59697199
theorem B49679345 : Blo 846354 49679345 := bstep (se 2 (by rfl) ⟨18629754, by rfl⟩ : syracuseStep 49679345 = 37259509) B37259509
theorem B2298415 : Blo 846354 2298415 := bstep (se 1 (by rfl) ⟨1723811, by rfl⟩ : syracuseStep 2298415 = 3447623) B3447623
theorem B470880989 : Blo 846354 470880989 := bstep (se 3 (by rfl) ⟨88290185, by rfl⟩ : syracuseStep 470880989 = 176580371) B176580371
theorem B2857463 : Blo 846354 2857463 := bstep (se 1 (by rfl) ⟨2143097, by rfl⟩ : syracuseStep 2857463 = 4286195) B4286195
theorem B1612457 : Blo 846354 1612457 := bstep (se 2 (by rfl) ⟨604671, by rfl⟩ : syracuseStep 1612457 = 1209343) B1209343
theorem B6102175 : Blo 846354 6102175 := bstep (se 1 (by rfl) ⟨4576631, by rfl⟩ : syracuseStep 6102175 = 9153263) B9153263
theorem B859295 : Blo 846354 859295 := bstep (se 1 (by rfl) ⟨644471, by rfl⟩ : syracuseStep 859295 = 1288943) B1288943
theorem B6431723 : Blo 846354 6431723 := bstep (se 1 (by rfl) ⟨4823792, by rfl⟩ : syracuseStep 6431723 = 9647585) B9647585
theorem B2860703 : Blo 846354 2860703 := bstep (se 1 (by rfl) ⟨2145527, by rfl⟩ : syracuseStep 2860703 = 4291055) B4291055
theorem B4828031 : Blo 846354 4828031 := bstep (se 1 (by rfl) ⟨3621023, by rfl⟩ : syracuseStep 4828031 = 7242047) B7242047
theorem B3059579 : Blo 846354 3059579 := bstep (se 1 (by rfl) ⟨2294684, by rfl⟩ : syracuseStep 3059579 = 4589369) B4589369
theorem B8597459 : Blo 846354 8597459 := bstep (se 1 (by rfl) ⟨6448094, by rfl⟩ : syracuseStep 8597459 = 12896189) B12896189
theorem B2143817 : Blo 846354 2143817 := bstep (se 2 (by rfl) ⟨803931, by rfl⟩ : syracuseStep 2143817 = 1607863) B1607863
theorem B3225977 : Blo 846354 3225977 := bstep (se 2 (by rfl) ⟨1209741, by rfl⟩ : syracuseStep 3225977 = 2419483) B2419483
theorem B8142383 : Blo 846354 8142383 := bstep (se 1 (by rfl) ⟨6106787, by rfl⟩ : syracuseStep 8142383 = 12213575) B12213575
theorem B2148079 : Blo 846354 2148079 := bstep (se 1 (by rfl) ⟨1611059, by rfl⟩ : syracuseStep 2148079 = 3222119) B3222119
theorem B1526099 : Blo 846354 1526099 := bstep (se 1 (by rfl) ⟨1144574, by rfl⟩ : syracuseStep 1526099 = 2289149) B2289149
theorem B2411623 : Blo 846354 2411623 := bstep (se 1 (by rfl) ⟨1808717, by rfl⟩ : syracuseStep 2411623 = 3617435) B3617435
theorem B6444359 : Blo 846354 6444359 := bstep (se 1 (by rfl) ⟨4833269, by rfl⟩ : syracuseStep 6444359 = 9666539) B9666539
theorem B1430905 : Blo 846354 1430905 := bstep (se 2 (by rfl) ⟨536589, by rfl⟩ : syracuseStep 1430905 = 1073179) B1073179
theorem B1071463 : Blo 846354 1071463 := bstep (se 1 (by rfl) ⟨803597, by rfl⟩ : syracuseStep 1071463 = 1607195) B1607195
theorem B3629053 : Blo 846354 3629053 := bstep (se 3 (by rfl) ⟨680447, by rfl⟩ : syracuseStep 3629053 = 1360895) B1360895
theorem B1434091 : Blo 846354 1434091 := bstep (se 1 (by rfl) ⟨1075568, by rfl⟩ : syracuseStep 1434091 = 2151137) B2151137
theorem B1270511 : Blo 846354 1270511 := bstep (se 1 (by rfl) ⟨952883, by rfl⟩ : syracuseStep 1270511 = 1905767) B1905767
theorem B1271273 : Blo 846354 1271273 := bstep (se 2 (by rfl) ⟨476727, by rfl⟩ : syracuseStep 1271273 = 953455) B953455
theorem B2418913 : Blo 846354 2418913 := bstep (se 2 (by rfl) ⟨907092, by rfl⟩ : syracuseStep 2418913 = 1814185) B1814185
theorem B848367 : Blo 846354 848367 := bstep (se 1 (by rfl) ⟨636275, by rfl⟩ : syracuseStep 848367 = 1272551) B1272551
theorem B848431 : Blo 846354 848431 := bstep (se 1 (by rfl) ⟨636323, by rfl⟩ : syracuseStep 848431 = 1272647) B1272647
theorem B849343 : Blo 846354 849343 := bstep (se 1 (by rfl) ⟨637007, by rfl⟩ : syracuseStep 849343 = 1274015) B1274015
theorem B1210459 : Blo 846354 1210459 := bstep (se 1 (by rfl) ⟨907844, by rfl⟩ : syracuseStep 1210459 = 1815689) B1815689
theorem B7731455 : Blo 846354 7731455 := bstep (se 1 (by rfl) ⟨5798591, by rfl⟩ : syracuseStep 7731455 = 11597183) B11597183
theorem B6880423 : Blo 846354 6880423 := bstep (se 1 (by rfl) ⟨5160317, by rfl⟩ : syracuseStep 6880423 = 10320635) B10320635
theorem B313920659 : Blo 846354 313920659 := bstep (se 1 (by rfl) ⟨235440494, by rfl⟩ : syracuseStep 313920659 = 470880989) B470880989
theorem B4296239 : Blo 846354 4296239 := bstep (se 1 (by rfl) ⟨3222179, by rfl⟩ : syracuseStep 4296239 = 6444359) B6444359
theorem B3215497 : Blo 846354 3215497 := bstep (se 2 (by rfl) ⟨1205811, by rfl⟩ : syracuseStep 3215497 = 2411623) B2411623
theorem B1904975 : Blo 846354 1904975 := bstep (se 1 (by rfl) ⟨1428731, by rfl⟩ : syracuseStep 1904975 = 2857463) B2857463
theorem B4069597 : Blo 846354 4069597 := bstep (se 3 (by rfl) ⟨763049, by rfl⟩ : syracuseStep 4069597 = 1526099) B1526099
theorem B1907135 : Blo 846354 1907135 := bstep (se 1 (by rfl) ⟨1430351, by rfl⟩ : syracuseStep 1907135 = 2860703) B2860703
theorem B1907873 : Blo 846354 1907873 := bstep (se 2 (by rfl) ⟨715452, by rfl⟩ : syracuseStep 1907873 = 1430905) B1430905
theorem B3218687 : Blo 846354 3218687 := bstep (se 1 (by rfl) ⟨2414015, by rfl⟩ : syracuseStep 3218687 = 4828031) B4828031
theorem B1613945 : Blo 846354 1613945 := bstep (se 2 (by rfl) ⟨605229, by rfl⟩ : syracuseStep 1613945 = 1210459) B1210459
theorem B8136233 : Blo 846354 8136233 := bstep (se 2 (by rfl) ⟨3051087, by rfl⟩ : syracuseStep 8136233 = 6102175) B6102175
theorem B1912121 : Blo 846354 1912121 := bstep (se 2 (by rfl) ⟨717045, by rfl⟩ : syracuseStep 1912121 = 1434091) B1434091
theorem B2864105 : Blo 846354 2864105 := bstep (se 2 (by rfl) ⟨1074039, by rfl⟩ : syracuseStep 2864105 = 2148079) B2148079
theorem B3225217 : Blo 846354 3225217 := bstep (se 2 (by rfl) ⟨1209456, by rfl⟩ : syracuseStep 3225217 = 2418913) B2418913
theorem B1357577 : Blo 846354 1357577 := bstep (se 2 (by rfl) ⟨509091, by rfl⟩ : syracuseStep 1357577 = 1018183) B1018183
theorem B3064553 : Blo 846354 3064553 := bstep (se 2 (by rfl) ⟨1149207, by rfl⟩ : syracuseStep 3064553 = 2298415) B2298415
theorem B1428617 : Blo 846354 1428617 := bstep (se 2 (by rfl) ⟨535731, by rfl⟩ : syracuseStep 1428617 = 1071463) B1071463
theorem B1429211 : Blo 846354 1429211 := bstep (se 1 (by rfl) ⟨1071908, by rfl⟩ : syracuseStep 1429211 = 2143817) B2143817
theorem B2150651 : Blo 846354 2150651 := bstep (se 1 (by rfl) ⟨1612988, by rfl⟩ : syracuseStep 2150651 = 3225977) B3225977
theorem B5428255 : Blo 846354 5428255 := bstep (se 1 (by rfl) ⟨4071191, by rfl⟩ : syracuseStep 5428255 = 8142383) B8142383
theorem B22926557 : Blo 846354 22926557 := bstep (se 3 (by rfl) ⟨4298729, by rfl⟩ : syracuseStep 22926557 = 8597459) B8597459
theorem B4838737 : Blo 846354 4838737 := bstep (se 2 (by rfl) ⟨1814526, by rfl⟩ : syracuseStep 4838737 = 3629053) B3629053
theorem B124081631 : Blo 846354 124081631 := bstep (se 1 (by rfl) ⟨93061223, by rfl⟩ : syracuseStep 124081631 = 186122447) B186122447
theorem B33119563 : Blo 846354 33119563 := bstep (se 1 (by rfl) ⟨24839672, by rfl⟩ : syracuseStep 33119563 = 49679345) B49679345
theorem B82468853 : Blo 846354 82468853 := bstep (se 5 (by rfl) ⟨3865727, by rfl⟩ : syracuseStep 82468853 = 7731455) B7731455
theorem B106128353 : Blo 846354 106128353 := bstep (se 2 (by rfl) ⟨39798132, by rfl⟩ : syracuseStep 106128353 = 79596265) B79596265
theorem B1074971 : Blo 846354 1074971 := bstep (se 1 (by rfl) ⟨806228, by rfl⟩ : syracuseStep 1074971 = 1612457) B1612457
theorem B847007 : Blo 846354 847007 := bstep (se 1 (by rfl) ⟨635255, by rfl⟩ : syracuseStep 847007 = 1270511) B1270511
theorem B4287815 : Blo 846354 4287815 := bstep (se 1 (by rfl) ⟨3215861, by rfl⟩ : syracuseStep 4287815 = 6431723) B6431723
theorem B847515 : Blo 846354 847515 := bstep (se 1 (by rfl) ⟨635636, by rfl⟩ : syracuseStep 847515 = 1271273) B1271273
theorem B2291453 : Blo 846354 2291453 := bstep (se 3 (by rfl) ⟨429647, by rfl⟩ : syracuseStep 2291453 = 859295) B859295
theorem B9173897 : Blo 846354 9173897 := bstep (se 2 (by rfl) ⟨3440211, by rfl⟩ : syracuseStep 9173897 = 6880423) B6880423
theorem B8158877 : Blo 846354 8158877 := bstep (se 3 (by rfl) ⟨1529789, by rfl⟩ : syracuseStep 8158877 = 3059579) B3059579
theorem B952411 : Blo 846354 952411 := bstep (se 1 (by rfl) ⟨714308, by rfl⟩ : syracuseStep 952411 = 1428617) B1428617
theorem B952807 : Blo 846354 952807 := bstep (se 1 (by rfl) ⟨714605, by rfl⟩ : syracuseStep 952807 = 1429211) B1429211
theorem B4300289 : Blo 846354 4300289 := bstep (se 2 (by rfl) ⟨1612608, by rfl⟩ : syracuseStep 4300289 = 3225217) B3225217
theorem B2858543 : Blo 846354 2858543 := bstep (se 1 (by rfl) ⟨2143907, by rfl⟩ : syracuseStep 2858543 = 4287815) B4287815
theorem B1909403 : Blo 846354 1909403 := bstep (se 1 (by rfl) ⟨1432052, by rfl⟩ : syracuseStep 1909403 = 2864105) B2864105
theorem B4303853 : Blo 846354 4303853 := bstep (se 3 (by rfl) ⟨806972, by rfl⟩ : syracuseStep 4303853 = 1613945) B1613945
theorem B2043035 : Blo 846354 2043035 := bstep (se 1 (by rfl) ⟨1532276, by rfl⟩ : syracuseStep 2043035 = 3064553) B3064553
theorem B2864159 : Blo 846354 2864159 := bstep (se 1 (by rfl) ⟨2148119, by rfl⟩ : syracuseStep 2864159 = 4296239) B4296239
theorem B15284371 : Blo 846354 15284371 := bstep (se 1 (by rfl) ⟨11463278, by rfl⟩ : syracuseStep 15284371 = 22926557) B22926557
theorem B82721087 : Blo 846354 82721087 := bstep (se 1 (by rfl) ⟨62040815, by rfl⟩ : syracuseStep 82721087 = 124081631) B124081631
theorem B2866589 : Blo 846354 2866589 := bstep (se 3 (by rfl) ⟨537485, by rfl⟩ : syracuseStep 2866589 = 1074971) B1074971
theorem B2145791 : Blo 846354 2145791 := bstep (se 1 (by rfl) ⟨1609343, by rfl⟩ : syracuseStep 2145791 = 3218687) B3218687
theorem B5424155 : Blo 846354 5424155 := bstep (se 1 (by rfl) ⟨4068116, by rfl⟩ : syracuseStep 5424155 = 8136233) B8136233
theorem B5426129 : Blo 846354 5426129 := bstep (se 2 (by rfl) ⟨2034798, by rfl⟩ : syracuseStep 5426129 = 4069597) B4069597
theorem B1527635 : Blo 846354 1527635 := bstep (se 1 (by rfl) ⟨1145726, by rfl⟩ : syracuseStep 1527635 = 2291453) B2291453
theorem B905051 : Blo 846354 905051 := bstep (se 1 (by rfl) ⟨678788, by rfl⟩ : syracuseStep 905051 = 1357577) B1357577
theorem B44159417 : Blo 846354 44159417 := bstep (se 2 (by rfl) ⟨16559781, by rfl⟩ : syracuseStep 44159417 = 33119563) B33119563
theorem B6115931 : Blo 846354 6115931 := bstep (se 1 (by rfl) ⟨4586948, by rfl⟩ : syracuseStep 6115931 = 9173897) B9173897
theorem B209280439 : Blo 846354 209280439 := bstep (se 1 (by rfl) ⟨156960329, by rfl⟩ : syracuseStep 209280439 = 313920659) B313920659
theorem B283008941 : Blo 846354 283008941 := bstep (se 3 (by rfl) ⟨53064176, by rfl⟩ : syracuseStep 283008941 = 106128353) B106128353
theorem B1433767 : Blo 846354 1433767 := bstep (se 1 (by rfl) ⟨1075325, by rfl⟩ : syracuseStep 1433767 = 2150651) B2150651
theorem B1269983 : Blo 846354 1269983 := bstep (se 1 (by rfl) ⟨952487, by rfl⟩ : syracuseStep 1269983 = 1904975) B1904975
theorem B1271423 : Blo 846354 1271423 := bstep (se 1 (by rfl) ⟨953567, by rfl⟩ : syracuseStep 1271423 = 1907135) B1907135
theorem B1271915 : Blo 846354 1271915 := bstep (se 1 (by rfl) ⟨953936, by rfl⟩ : syracuseStep 1271915 = 1907873) B1907873
theorem B54979235 : Blo 846354 54979235 := bstep (se 1 (by rfl) ⟨41234426, by rfl⟩ : syracuseStep 54979235 = 82468853) B82468853
theorem B4287329 : Blo 846354 4287329 := bstep (se 2 (by rfl) ⟨1607748, by rfl⟩ : syracuseStep 4287329 = 3215497) B3215497
theorem B7237673 : Blo 846354 7237673 := bstep (se 2 (by rfl) ⟨2714127, by rfl⟩ : syracuseStep 7237673 = 5428255) B5428255
theorem B6451649 : Blo 846354 6451649 := bstep (se 2 (by rfl) ⟨2419368, by rfl⟩ : syracuseStep 6451649 = 4838737) B4838737
theorem B1274747 : Blo 846354 1274747 := bstep (se 1 (by rfl) ⟨956060, by rfl⟩ : syracuseStep 1274747 = 1912121) B1912121
theorem B5439251 : Blo 846354 5439251 := bstep (se 1 (by rfl) ⟨4079438, by rfl⟩ : syracuseStep 5439251 = 8158877) B8158877
theorem B1018423 : Blo 846354 1018423 := bstep (se 1 (by rfl) ⟨763817, by rfl⟩ : syracuseStep 1018423 = 1527635) B1527635
theorem B1905695 : Blo 846354 1905695 := bstep (se 1 (by rfl) ⟨1429271, by rfl⟩ : syracuseStep 1905695 = 2858543) B2858543
theorem B2858219 : Blo 846354 2858219 := bstep (se 1 (by rfl) ⟨2143664, by rfl⟩ : syracuseStep 2858219 = 4287329) B4287329
theorem B4825115 : Blo 846354 4825115 := bstep (se 1 (by rfl) ⟨3618836, by rfl⟩ : syracuseStep 4825115 = 7237673) B7237673
theorem B4301099 : Blo 846354 4301099 := bstep (se 1 (by rfl) ⟨3225824, by rfl⟩ : syracuseStep 4301099 = 6451649) B6451649
theorem B1909439 : Blo 846354 1909439 := bstep (se 1 (by rfl) ⟨1432079, by rfl⟩ : syracuseStep 1909439 = 2864159) B2864159
theorem B1911059 : Blo 846354 1911059 := bstep (se 1 (by rfl) ⟨1433294, by rfl⟩ : syracuseStep 1911059 = 2866589) B2866589
theorem B1911689 : Blo 846354 1911689 := bstep (se 2 (by rfl) ⟨716883, by rfl⟩ : syracuseStep 1911689 = 1433767) B1433767
theorem B3616103 : Blo 846354 3616103 := bstep (se 1 (by rfl) ⟨2712077, by rfl⟩ : syracuseStep 3616103 = 5424155) B5424155
theorem B3617419 : Blo 846354 3617419 := bstep (se 1 (by rfl) ⟨2713064, by rfl⟩ : syracuseStep 3617419 = 5426129) B5426129
theorem B29439611 : Blo 846354 29439611 := bstep (se 1 (by rfl) ⟨22079708, by rfl⟩ : syracuseStep 29439611 = 44159417) B44159417
theorem B4077287 : Blo 846354 4077287 := bstep (se 1 (by rfl) ⟨3057965, by rfl⟩ : syracuseStep 4077287 = 6115931) B6115931
theorem B2866859 : Blo 846354 2866859 := bstep (se 1 (by rfl) ⟨2150144, by rfl⟩ : syracuseStep 2866859 = 4300289) B4300289
theorem B36652823 : Blo 846354 36652823 := bstep (se 1 (by rfl) ⟨27489617, by rfl⟩ : syracuseStep 36652823 = 54979235) B54979235
theorem B2869235 : Blo 846354 2869235 := bstep (se 1 (by rfl) ⟨2151926, by rfl⟩ : syracuseStep 2869235 = 4303853) B4303853
theorem B1362023 : Blo 846354 1362023 := bstep (se 1 (by rfl) ⟨1021517, by rfl⟩ : syracuseStep 1362023 = 2043035) B2043035
theorem B279040585 : Blo 846354 279040585 := bstep (se 2 (by rfl) ⟨104640219, by rfl⟩ : syracuseStep 279040585 = 209280439) B209280439
theorem B2413469 : Blo 846354 2413469 := bstep (se 3 (by rfl) ⟨452525, by rfl⟩ : syracuseStep 2413469 = 905051) B905051
theorem B1430527 : Blo 846354 1430527 := bstep (se 1 (by rfl) ⟨1072895, by rfl⟩ : syracuseStep 1430527 = 2145791) B2145791
theorem B3626167 : Blo 846354 3626167 := bstep (se 1 (by rfl) ⟨2719625, by rfl⟩ : syracuseStep 3626167 = 5439251) B5439251
theorem B1269881 : Blo 846354 1269881 := bstep (se 2 (by rfl) ⟨476205, by rfl⟩ : syracuseStep 1269881 = 952411) B952411
theorem B1270409 : Blo 846354 1270409 := bstep (se 2 (by rfl) ⟨476403, by rfl⟩ : syracuseStep 1270409 = 952807) B952807
theorem B188672627 : Blo 846354 188672627 := bstep (se 1 (by rfl) ⟨141504470, by rfl⟩ : syracuseStep 188672627 = 283008941) B283008941
theorem B846655 : Blo 846354 846655 := bstep (se 1 (by rfl) ⟨634991, by rfl⟩ : syracuseStep 846655 = 1269983) B1269983
theorem B1272935 : Blo 846354 1272935 := bstep (se 1 (by rfl) ⟨954701, by rfl⟩ : syracuseStep 1272935 = 1909403) B1909403
theorem B847615 : Blo 846354 847615 := bstep (se 1 (by rfl) ⟨635711, by rfl⟩ : syracuseStep 847615 = 1271423) B1271423
theorem B847943 : Blo 846354 847943 := bstep (se 1 (by rfl) ⟨635957, by rfl⟩ : syracuseStep 847943 = 1271915) B1271915
theorem B20379161 : Blo 846354 20379161 := bstep (se 2 (by rfl) ⟨7642185, by rfl⟩ : syracuseStep 20379161 = 15284371) B15284371
theorem B849831 : Blo 846354 849831 := bstep (se 1 (by rfl) ⟨637373, by rfl⟩ : syracuseStep 849831 = 1274747) B1274747
theorem B55147391 : Blo 846354 55147391 := bstep (se 1 (by rfl) ⟨41360543, by rfl⟩ : syracuseStep 55147391 = 82721087) B82721087
theorem B1608979 : Blo 846354 1608979 := bstep (se 1 (by rfl) ⟨1206734, by rfl⟩ : syracuseStep 1608979 = 2413469) B2413469
theorem B1905479 : Blo 846354 1905479 := bstep (se 1 (by rfl) ⟨1429109, by rfl⟩ : syracuseStep 1905479 = 2858219) B2858219
theorem B3216743 : Blo 846354 3216743 := bstep (se 1 (by rfl) ⟨2412557, by rfl⟩ : syracuseStep 3216743 = 4825115) B4825115
theorem B372054113 : Blo 846354 372054113 := bstep (se 2 (by rfl) ⟨139520292, by rfl⟩ : syracuseStep 372054113 = 279040585) B279040585
theorem B4823225 : Blo 846354 4823225 := bstep (se 2 (by rfl) ⟨1808709, by rfl⟩ : syracuseStep 4823225 = 3617419) B3617419
theorem B1907369 : Blo 846354 1907369 := bstep (se 2 (by rfl) ⟨715263, by rfl⟩ : syracuseStep 1907369 = 1430527) B1430527
theorem B1911239 : Blo 846354 1911239 := bstep (se 1 (by rfl) ⟨1433429, by rfl⟩ : syracuseStep 1911239 = 2866859) B2866859
theorem B1912823 : Blo 846354 1912823 := bstep (se 1 (by rfl) ⟨1434617, by rfl⟩ : syracuseStep 1912823 = 2869235) B2869235
theorem B1357897 : Blo 846354 1357897 := bstep (se 2 (by rfl) ⟨509211, by rfl⟩ : syracuseStep 1357897 = 1018423) B1018423
theorem B54344429 : Blo 846354 54344429 := bstep (se 3 (by rfl) ⟨10189580, by rfl⟩ : syracuseStep 54344429 = 20379161) B20379161
theorem B2867399 : Blo 846354 2867399 := bstep (se 1 (by rfl) ⟨2150549, by rfl⟩ : syracuseStep 2867399 = 4301099) B4301099
theorem B4834889 : Blo 846354 4834889 := bstep (se 2 (by rfl) ⟨1813083, by rfl⟩ : syracuseStep 4834889 = 3626167) B3626167
theorem B125781751 : Blo 846354 125781751 := bstep (se 1 (by rfl) ⟨94336313, by rfl⟩ : syracuseStep 125781751 = 188672627) B188672627
theorem B2410735 : Blo 846354 2410735 := bstep (se 1 (by rfl) ⟨1808051, by rfl⟩ : syracuseStep 2410735 = 3616103) B3616103
theorem B24435215 : Blo 846354 24435215 := bstep (se 1 (by rfl) ⟨18326411, by rfl⟩ : syracuseStep 24435215 = 36652823) B36652823
theorem B908015 : Blo 846354 908015 := bstep (se 1 (by rfl) ⟨681011, by rfl⟩ : syracuseStep 908015 = 1362023) B1362023
theorem B1270463 : Blo 846354 1270463 := bstep (se 1 (by rfl) ⟨952847, by rfl⟩ : syracuseStep 1270463 = 1905695) B1905695
theorem B846587 : Blo 846354 846587 := bstep (se 1 (by rfl) ⟨634940, by rfl⟩ : syracuseStep 846587 = 1269881) B1269881
theorem B846939 : Blo 846354 846939 := bstep (se 1 (by rfl) ⟨635204, by rfl⟩ : syracuseStep 846939 = 1270409) B1270409
theorem B1272959 : Blo 846354 1272959 := bstep (se 1 (by rfl) ⟨954719, by rfl⟩ : syracuseStep 1272959 = 1909439) B1909439
theorem B1274039 : Blo 846354 1274039 := bstep (se 1 (by rfl) ⟨955529, by rfl⟩ : syracuseStep 1274039 = 1911059) B1911059
theorem B1274459 : Blo 846354 1274459 := bstep (se 1 (by rfl) ⟨955844, by rfl⟩ : syracuseStep 1274459 = 1911689) B1911689
theorem B848623 : Blo 846354 848623 := bstep (se 1 (by rfl) ⟨636467, by rfl⟩ : syracuseStep 848623 = 1272935) B1272935
theorem B19626407 : Blo 846354 19626407 := bstep (se 1 (by rfl) ⟨14719805, by rfl⟩ : syracuseStep 19626407 = 29439611) B29439611
theorem B2718191 : Blo 846354 2718191 := bstep (se 1 (by rfl) ⟨2038643, by rfl⟩ : syracuseStep 2718191 = 4077287) B4077287
theorem B36764927 : Blo 846354 36764927 := bstep (se 1 (by rfl) ⟨27573695, by rfl⟩ : syracuseStep 36764927 = 55147391) B55147391
theorem B167709001 : Blo 846354 167709001 := bstep (se 2 (by rfl) ⟨62890875, by rfl⟩ : syracuseStep 167709001 = 125781751) B125781751
theorem B3214313 : Blo 846354 3214313 := bstep (se 2 (by rfl) ⟨1205367, by rfl⟩ : syracuseStep 3214313 = 2410735) B2410735
theorem B3215483 : Blo 846354 3215483 := bstep (se 1 (by rfl) ⟨2411612, by rfl⟩ : syracuseStep 3215483 = 4823225) B4823225
theorem B16290143 : Blo 846354 16290143 := bstep (se 1 (by rfl) ⟨12217607, by rfl⟩ : syracuseStep 16290143 = 24435215) B24435215
theorem B1810529 : Blo 846354 1810529 := bstep (se 2 (by rfl) ⟨678948, by rfl⟩ : syracuseStep 1810529 = 1357897) B1357897
theorem B13084271 : Blo 846354 13084271 := bstep (se 1 (by rfl) ⟨9813203, by rfl⟩ : syracuseStep 13084271 = 19626407) B19626407
theorem B1812127 : Blo 846354 1812127 := bstep (se 1 (by rfl) ⟨1359095, by rfl⟩ : syracuseStep 1812127 = 2718191) B2718191
theorem B1911599 : Blo 846354 1911599 := bstep (se 1 (by rfl) ⟨1433699, by rfl⟩ : syracuseStep 1911599 = 2867399) B2867399
theorem B3223259 : Blo 846354 3223259 := bstep (se 1 (by rfl) ⟨2417444, by rfl⟩ : syracuseStep 3223259 = 4834889) B4834889
theorem B2144495 : Blo 846354 2144495 := bstep (se 1 (by rfl) ⟨1608371, by rfl⟩ : syracuseStep 2144495 = 3216743) B3216743
theorem B248036075 : Blo 846354 248036075 := bstep (se 1 (by rfl) ⟨186027056, by rfl⟩ : syracuseStep 248036075 = 372054113) B372054113
theorem B2145305 : Blo 846354 2145305 := bstep (se 2 (by rfl) ⟨804489, by rfl⟩ : syracuseStep 2145305 = 1608979) B1608979
theorem B9685493 : Blo 846354 9685493 := bstep (se 5 (by rfl) ⟨454007, by rfl⟩ : syracuseStep 9685493 = 908015) B908015
theorem B36229619 : Blo 846354 36229619 := bstep (se 1 (by rfl) ⟨27172214, by rfl⟩ : syracuseStep 36229619 = 54344429) B54344429
theorem B1270319 : Blo 846354 1270319 := bstep (se 1 (by rfl) ⟨952739, by rfl⟩ : syracuseStep 1270319 = 1905479) B1905479
theorem B1271579 : Blo 846354 1271579 := bstep (se 1 (by rfl) ⟨953684, by rfl⟩ : syracuseStep 1271579 = 1907369) B1907369
theorem B846975 : Blo 846354 846975 := bstep (se 1 (by rfl) ⟨635231, by rfl⟩ : syracuseStep 846975 = 1270463) B1270463
theorem B1274159 : Blo 846354 1274159 := bstep (se 1 (by rfl) ⟨955619, by rfl⟩ : syracuseStep 1274159 = 1911239) B1911239
theorem B848639 : Blo 846354 848639 := bstep (se 1 (by rfl) ⟨636479, by rfl⟩ : syracuseStep 848639 = 1272959) B1272959
theorem B1275215 : Blo 846354 1275215 := bstep (se 1 (by rfl) ⟨956411, by rfl⟩ : syracuseStep 1275215 = 1912823) B1912823
theorem B849359 : Blo 846354 849359 := bstep (se 1 (by rfl) ⟨637019, by rfl⟩ : syracuseStep 849359 = 1274039) B1274039
theorem B849639 : Blo 846354 849639 := bstep (se 1 (by rfl) ⟨637229, by rfl⟩ : syracuseStep 849639 = 1274459) B1274459
theorem B24509951 : Blo 846354 24509951 := bstep (se 1 (by rfl) ⟨18382463, by rfl⟩ : syracuseStep 24509951 = 36764927) B36764927
theorem B6456995 : Blo 846354 6456995 := bstep (se 1 (by rfl) ⟨4842746, by rfl⟩ : syracuseStep 6456995 = 9685493) B9685493
theorem B24153079 : Blo 846354 24153079 := bstep (se 1 (by rfl) ⟨18114809, by rfl⟩ : syracuseStep 24153079 = 36229619) B36229619
theorem B223612001 : Blo 846354 223612001 := bstep (se 2 (by rfl) ⟨83854500, by rfl⟩ : syracuseStep 223612001 = 167709001) B167709001
theorem B8722847 : Blo 846354 8722847 := bstep (se 1 (by rfl) ⟨6542135, by rfl⟩ : syracuseStep 8722847 = 13084271) B13084271
theorem B165357383 : Blo 846354 165357383 := bstep (se 1 (by rfl) ⟨124018037, by rfl⟩ : syracuseStep 165357383 = 248036075) B248036075
theorem B2142875 : Blo 846354 2142875 := bstep (se 1 (by rfl) ⟨1607156, by rfl⟩ : syracuseStep 2142875 = 3214313) B3214313
theorem B2143655 : Blo 846354 2143655 := bstep (se 1 (by rfl) ⟨1607741, by rfl⟩ : syracuseStep 2143655 = 3215483) B3215483
theorem B10860095 : Blo 846354 10860095 := bstep (se 1 (by rfl) ⟨8145071, by rfl⟩ : syracuseStep 10860095 = 16290143) B16290143
theorem B2148839 : Blo 846354 2148839 := bstep (se 1 (by rfl) ⟨1611629, by rfl⟩ : syracuseStep 2148839 = 3223259) B3223259
theorem B1429663 : Blo 846354 1429663 := bstep (se 1 (by rfl) ⟨1072247, by rfl⟩ : syracuseStep 1429663 = 2144495) B2144495
theorem B1430203 : Blo 846354 1430203 := bstep (se 1 (by rfl) ⟨1072652, by rfl⟩ : syracuseStep 1430203 = 2145305) B2145305
theorem B16339967 : Blo 846354 16339967 := bstep (se 1 (by rfl) ⟨12254975, by rfl⟩ : syracuseStep 16339967 = 24509951) B24509951
theorem B2416169 : Blo 846354 2416169 := bstep (se 2 (by rfl) ⟨906063, by rfl⟩ : syracuseStep 2416169 = 1812127) B1812127
theorem B1207019 : Blo 846354 1207019 := bstep (se 1 (by rfl) ⟨905264, by rfl⟩ : syracuseStep 1207019 = 1810529) B1810529
theorem B846879 : Blo 846354 846879 := bstep (se 1 (by rfl) ⟨635159, by rfl⟩ : syracuseStep 846879 = 1270319) B1270319
theorem B847719 : Blo 846354 847719 := bstep (se 1 (by rfl) ⟨635789, by rfl⟩ : syracuseStep 847719 = 1271579) B1271579
theorem B1274399 : Blo 846354 1274399 := bstep (se 1 (by rfl) ⟨955799, by rfl⟩ : syracuseStep 1274399 = 1911599) B1911599
theorem B849439 : Blo 846354 849439 := bstep (se 1 (by rfl) ⟨637079, by rfl⟩ : syracuseStep 849439 = 1274159) B1274159
theorem B850143 : Blo 846354 850143 := bstep (se 1 (by rfl) ⟨637607, by rfl⟩ : syracuseStep 850143 = 1275215) B1275215
theorem B1610779 : Blo 846354 1610779 := bstep (se 1 (by rfl) ⟨1208084, by rfl⟩ : syracuseStep 1610779 = 2416169) B2416169
theorem B1906217 : Blo 846354 1906217 := bstep (se 2 (by rfl) ⟨714831, by rfl⟩ : syracuseStep 1906217 = 1429663) B1429663
theorem B1906937 : Blo 846354 1906937 := bstep (se 2 (by rfl) ⟨715101, by rfl⟩ : syracuseStep 1906937 = 1430203) B1430203
theorem B3218717 : Blo 846354 3218717 := bstep (se 3 (by rfl) ⟨603509, by rfl⟩ : syracuseStep 3218717 = 1207019) B1207019
theorem B4304663 : Blo 846354 4304663 := bstep (se 1 (by rfl) ⟨3228497, by rfl⟩ : syracuseStep 4304663 = 6456995) B6456995
theorem B149074667 : Blo 846354 149074667 := bstep (se 1 (by rfl) ⟨111806000, by rfl⟩ : syracuseStep 149074667 = 223612001) B223612001
theorem B10893311 : Blo 846354 10893311 := bstep (se 1 (by rfl) ⟨8169983, by rfl⟩ : syracuseStep 10893311 = 16339967) B16339967
theorem B1428583 : Blo 846354 1428583 := bstep (se 1 (by rfl) ⟨1071437, by rfl⟩ : syracuseStep 1428583 = 2142875) B2142875
theorem B1429103 : Blo 846354 1429103 := bstep (se 1 (by rfl) ⟨1071827, by rfl⟩ : syracuseStep 1429103 = 2143655) B2143655
theorem B1432559 : Blo 846354 1432559 := bstep (se 1 (by rfl) ⟨1074419, by rfl⟩ : syracuseStep 1432559 = 2148839) B2148839
theorem B32204105 : Blo 846354 32204105 := bstep (se 2 (by rfl) ⟨12076539, by rfl⟩ : syracuseStep 32204105 = 24153079) B24153079
theorem B440953021 : Blo 846354 440953021 := bstep (se 3 (by rfl) ⟨82678691, by rfl⟩ : syracuseStep 440953021 = 165357383) B165357383
theorem B23260925 : Blo 846354 23260925 := bstep (se 3 (by rfl) ⟨4361423, by rfl⟩ : syracuseStep 23260925 = 8722847) B8722847
theorem B849599 : Blo 846354 849599 := bstep (se 1 (by rfl) ⟨637199, by rfl⟩ : syracuseStep 849599 = 1274399) B1274399
theorem B7240063 : Blo 846354 7240063 := bstep (se 1 (by rfl) ⟨5430047, by rfl⟩ : syracuseStep 7240063 = 10860095) B10860095
theorem B952735 : Blo 846354 952735 := bstep (se 1 (by rfl) ⟨714551, by rfl⟩ : syracuseStep 952735 = 1429103) B1429103
theorem B1904777 : Blo 846354 1904777 := bstep (se 2 (by rfl) ⟨714291, by rfl⟩ : syracuseStep 1904777 = 1428583) B1428583
theorem B955039 : Blo 846354 955039 := bstep (se 1 (by rfl) ⟨716279, by rfl⟩ : syracuseStep 955039 = 1432559) B1432559
theorem B21469403 : Blo 846354 21469403 := bstep (se 1 (by rfl) ⟨16102052, by rfl⟩ : syracuseStep 21469403 = 32204105) B32204105
theorem B15507283 : Blo 846354 15507283 := bstep (se 1 (by rfl) ⟨11630462, by rfl⟩ : syracuseStep 15507283 = 23260925) B23260925
theorem B587937361 : Blo 846354 587937361 := bstep (se 2 (by rfl) ⟨220476510, by rfl⟩ : syracuseStep 587937361 = 440953021) B440953021
theorem B2145811 : Blo 846354 2145811 := bstep (se 1 (by rfl) ⟨1609358, by rfl⟩ : syracuseStep 2145811 = 3218717) B3218717
theorem B2147705 : Blo 846354 2147705 := bstep (se 2 (by rfl) ⟨805389, by rfl⟩ : syracuseStep 2147705 = 1610779) B1610779
theorem B2869775 : Blo 846354 2869775 := bstep (se 1 (by rfl) ⟨2152331, by rfl⟩ : syracuseStep 2869775 = 4304663) B4304663
theorem B9653417 : Blo 846354 9653417 := bstep (se 2 (by rfl) ⟨3620031, by rfl⟩ : syracuseStep 9653417 = 7240063) B7240063
theorem B7262207 : Blo 846354 7262207 := bstep (se 1 (by rfl) ⟨5446655, by rfl⟩ : syracuseStep 7262207 = 10893311) B10893311
theorem B1270811 : Blo 846354 1270811 := bstep (se 1 (by rfl) ⟨953108, by rfl⟩ : syracuseStep 1270811 = 1906217) B1906217
theorem B1271291 : Blo 846354 1271291 := bstep (se 1 (by rfl) ⟨953468, by rfl⟩ : syracuseStep 1271291 = 1906937) B1906937
theorem B99383111 : Blo 846354 99383111 := bstep (se 1 (by rfl) ⟨74537333, by rfl⟩ : syracuseStep 99383111 = 149074667) B149074667
theorem B783916481 : Blo 846354 783916481 := bstep (se 2 (by rfl) ⟨293968680, by rfl⟩ : syracuseStep 783916481 = 587937361) B587937361
theorem B2861081 : Blo 846354 2861081 := bstep (se 2 (by rfl) ⟨1072905, by rfl⟩ : syracuseStep 2861081 = 2145811) B2145811
theorem B1913183 : Blo 846354 1913183 := bstep (se 1 (by rfl) ⟨1434887, by rfl⟩ : syracuseStep 1913183 = 2869775) B2869775
theorem B6435611 : Blo 846354 6435611 := bstep (se 1 (by rfl) ⟨4826708, by rfl⟩ : syracuseStep 6435611 = 9653417) B9653417
theorem B1431803 : Blo 846354 1431803 := bstep (se 1 (by rfl) ⟨1073852, by rfl⟩ : syracuseStep 1431803 = 2147705) B2147705
theorem B4841471 : Blo 846354 4841471 := bstep (se 1 (by rfl) ⟨3631103, by rfl⟩ : syracuseStep 4841471 = 7262207) B7262207
theorem B1269851 : Blo 846354 1269851 := bstep (se 1 (by rfl) ⟨952388, by rfl⟩ : syracuseStep 1269851 = 1904777) B1904777
theorem B1270313 : Blo 846354 1270313 := bstep (se 2 (by rfl) ⟨476367, by rfl⟩ : syracuseStep 1270313 = 952735) B952735
theorem B14312935 : Blo 846354 14312935 := bstep (se 1 (by rfl) ⟨10734701, by rfl⟩ : syracuseStep 14312935 = 21469403) B21469403
theorem B847207 : Blo 846354 847207 := bstep (se 1 (by rfl) ⟨635405, by rfl⟩ : syracuseStep 847207 = 1270811) B1270811
theorem B1273385 : Blo 846354 1273385 := bstep (se 2 (by rfl) ⟨477519, by rfl⟩ : syracuseStep 1273385 = 955039) B955039
theorem B847527 : Blo 846354 847527 := bstep (se 1 (by rfl) ⟨635645, by rfl⟩ : syracuseStep 847527 = 1271291) B1271291
theorem B66255407 : Blo 846354 66255407 := bstep (se 1 (by rfl) ⟨49691555, by rfl⟩ : syracuseStep 66255407 = 99383111) B99383111
theorem B20676377 : Blo 846354 20676377 := bstep (se 2 (by rfl) ⟨7753641, by rfl⟩ : syracuseStep 20676377 = 15507283) B15507283
theorem B954535 : Blo 846354 954535 := bstep (se 1 (by rfl) ⟨715901, by rfl⟩ : syracuseStep 954535 = 1431803) B1431803
theorem B1907387 : Blo 846354 1907387 := bstep (se 1 (by rfl) ⟨1430540, by rfl⟩ : syracuseStep 1907387 = 2861081) B2861081
theorem B3227647 : Blo 846354 3227647 := bstep (se 1 (by rfl) ⟨2420735, by rfl⟩ : syracuseStep 3227647 = 4841471) B4841471
theorem B76335653 : Blo 846354 76335653 := bstep (se 4 (by rfl) ⟨7156467, by rfl⟩ : syracuseStep 76335653 = 14312935) B14312935
theorem B13784251 : Blo 846354 13784251 := bstep (se 1 (by rfl) ⟨10338188, by rfl⟩ : syracuseStep 13784251 = 20676377) B20676377
theorem B522610987 : Blo 846354 522610987 := bstep (se 1 (by rfl) ⟨391958240, by rfl⟩ : syracuseStep 522610987 = 783916481) B783916481
theorem B846567 : Blo 846354 846567 := bstep (se 1 (by rfl) ⟨634925, by rfl⟩ : syracuseStep 846567 = 1269851) B1269851
theorem B846875 : Blo 846354 846875 := bstep (se 1 (by rfl) ⟨635156, by rfl⟩ : syracuseStep 846875 = 1270313) B1270313
theorem B848923 : Blo 846354 848923 := bstep (se 1 (by rfl) ⟨636692, by rfl⟩ : syracuseStep 848923 = 1273385) B1273385
theorem B1275455 : Blo 846354 1275455 := bstep (se 1 (by rfl) ⟨956591, by rfl⟩ : syracuseStep 1275455 = 1913183) B1913183
theorem B4290407 : Blo 846354 4290407 := bstep (se 1 (by rfl) ⟨3217805, by rfl⟩ : syracuseStep 4290407 = 6435611) B6435611
theorem B44170271 : Blo 846354 44170271 := bstep (se 1 (by rfl) ⟨33127703, by rfl⟩ : syracuseStep 44170271 = 66255407) B66255407
theorem B696814649 : Blo 846354 696814649 := bstep (se 2 (by rfl) ⟨261305493, by rfl⟩ : syracuseStep 696814649 = 522610987) B522610987
theorem B203561741 : Blo 846354 203561741 := bstep (se 3 (by rfl) ⟨38167826, by rfl⟩ : syracuseStep 203561741 = 76335653) B76335653
theorem B2860271 : Blo 846354 2860271 := bstep (se 1 (by rfl) ⟨2145203, by rfl⟩ : syracuseStep 2860271 = 4290407) B4290407
theorem B4303529 : Blo 846354 4303529 := bstep (se 2 (by rfl) ⟨1613823, by rfl⟩ : syracuseStep 4303529 = 3227647) B3227647
theorem B29446847 : Blo 846354 29446847 := bstep (se 1 (by rfl) ⟨22085135, by rfl⟩ : syracuseStep 29446847 = 44170271) B44170271
theorem B1271591 : Blo 846354 1271591 := bstep (se 1 (by rfl) ⟨953693, by rfl⟩ : syracuseStep 1271591 = 1907387) B1907387
theorem B1272713 : Blo 846354 1272713 := bstep (se 2 (by rfl) ⟨477267, by rfl⟩ : syracuseStep 1272713 = 954535) B954535
theorem B18379001 : Blo 846354 18379001 := bstep (se 2 (by rfl) ⟨6892125, by rfl⟩ : syracuseStep 18379001 = 13784251) B13784251
theorem B850303 : Blo 846354 850303 := bstep (se 1 (by rfl) ⟨637727, by rfl⟩ : syracuseStep 850303 = 1275455) B1275455
theorem B19631231 : Blo 846354 19631231 := bstep (se 1 (by rfl) ⟨14723423, by rfl⟩ : syracuseStep 19631231 = 29446847) B29446847
theorem B1906847 : Blo 846354 1906847 := bstep (se 1 (by rfl) ⟨1430135, by rfl⟩ : syracuseStep 1906847 = 2860271) B2860271
theorem B135707827 : Blo 846354 135707827 := bstep (se 1 (by rfl) ⟨101780870, by rfl⟩ : syracuseStep 135707827 = 203561741) B203561741
theorem B2869019 : Blo 846354 2869019 := bstep (se 1 (by rfl) ⟨2151764, by rfl⟩ : syracuseStep 2869019 = 4303529) B4303529
theorem B49010669 : Blo 846354 49010669 := bstep (se 3 (by rfl) ⟨9189500, by rfl⟩ : syracuseStep 49010669 = 18379001) B18379001
theorem B464543099 : Blo 846354 464543099 := bstep (se 1 (by rfl) ⟨348407324, by rfl⟩ : syracuseStep 464543099 = 696814649) B696814649
theorem B847727 : Blo 846354 847727 := bstep (se 1 (by rfl) ⟨635795, by rfl⟩ : syracuseStep 847727 = 1271591) B1271591
theorem B848475 : Blo 846354 848475 := bstep (se 1 (by rfl) ⟨636356, by rfl⟩ : syracuseStep 848475 = 1272713) B1272713
theorem B32673779 : Blo 846354 32673779 := bstep (se 1 (by rfl) ⟨24505334, by rfl⟩ : syracuseStep 32673779 = 49010669) B49010669
theorem B309695399 : Blo 846354 309695399 := bstep (se 1 (by rfl) ⟨232271549, by rfl⟩ : syracuseStep 309695399 = 464543099) B464543099
theorem B1912679 : Blo 846354 1912679 := bstep (se 1 (by rfl) ⟨1434509, by rfl⟩ : syracuseStep 1912679 = 2869019) B2869019
theorem B13087487 : Blo 846354 13087487 := bstep (se 1 (by rfl) ⟨9815615, by rfl⟩ : syracuseStep 13087487 = 19631231) B19631231
theorem B1271231 : Blo 846354 1271231 := bstep (se 1 (by rfl) ⟨953423, by rfl⟩ : syracuseStep 1271231 = 1906847) B1906847
theorem B180943769 : Blo 846354 180943769 := bstep (se 2 (by rfl) ⟨67853913, by rfl⟩ : syracuseStep 180943769 = 135707827) B135707827
theorem B8724991 : Blo 846354 8724991 := bstep (se 1 (by rfl) ⟨6543743, by rfl⟩ : syracuseStep 8724991 = 13087487) B13087487
theorem B120629179 : Blo 846354 120629179 := bstep (se 1 (by rfl) ⟨90471884, by rfl⟩ : syracuseStep 120629179 = 180943769) B180943769
theorem B21782519 : Blo 846354 21782519 := bstep (se 1 (by rfl) ⟨16336889, by rfl⟩ : syracuseStep 21782519 = 32673779) B32673779
theorem B206463599 : Blo 846354 206463599 := bstep (se 1 (by rfl) ⟨154847699, by rfl⟩ : syracuseStep 206463599 = 309695399) B309695399
theorem B847487 : Blo 846354 847487 := bstep (se 1 (by rfl) ⟨635615, by rfl⟩ : syracuseStep 847487 = 1271231) B1271231
theorem B1275119 : Blo 846354 1275119 := bstep (se 1 (by rfl) ⟨956339, by rfl⟩ : syracuseStep 1275119 = 1912679) B1912679
theorem B11633321 : Blo 846354 11633321 := bstep (se 2 (by rfl) ⟨4362495, by rfl⟩ : syracuseStep 11633321 = 8724991) B8724991
theorem B14521679 : Blo 846354 14521679 := bstep (se 1 (by rfl) ⟨10891259, by rfl⟩ : syracuseStep 14521679 = 21782519) B21782519
theorem B137642399 : Blo 846354 137642399 := bstep (se 1 (by rfl) ⟨103231799, by rfl⟩ : syracuseStep 137642399 = 206463599) B206463599
theorem B643355621 : Blo 846354 643355621 := bstep (se 4 (by rfl) ⟨60314589, by rfl⟩ : syracuseStep 643355621 = 120629179) B120629179
theorem B850079 : Blo 846354 850079 := bstep (se 1 (by rfl) ⟨637559, by rfl⟩ : syracuseStep 850079 = 1275119) B1275119
theorem B428903747 : Blo 846354 428903747 := bstep (se 1 (by rfl) ⟨321677810, by rfl⟩ : syracuseStep 428903747 = 643355621) B643355621
theorem B91761599 : Blo 846354 91761599 := bstep (se 1 (by rfl) ⟨68821199, by rfl⟩ : syracuseStep 91761599 = 137642399) B137642399
theorem B9681119 : Blo 846354 9681119 := bstep (se 1 (by rfl) ⟨7260839, by rfl⟩ : syracuseStep 9681119 = 14521679) B14521679
theorem B7755547 : Blo 846354 7755547 := bstep (se 1 (by rfl) ⟨5816660, by rfl⟩ : syracuseStep 7755547 = 11633321) B11633321
theorem B285935831 : Blo 846354 285935831 := bstep (se 1 (by rfl) ⟨214451873, by rfl⟩ : syracuseStep 285935831 = 428903747) B428903747
theorem B10340729 : Blo 846354 10340729 := bstep (se 2 (by rfl) ⟨3877773, by rfl⟩ : syracuseStep 10340729 = 7755547) B7755547
theorem B61174399 : Blo 846354 61174399 := bstep (se 1 (by rfl) ⟨45880799, by rfl⟩ : syracuseStep 61174399 = 91761599) B91761599
theorem B6454079 : Blo 846354 6454079 := bstep (se 1 (by rfl) ⟨4840559, by rfl⟩ : syracuseStep 6454079 = 9681119) B9681119
theorem B81565865 : Blo 846354 81565865 := bstep (se 2 (by rfl) ⟨30587199, by rfl⟩ : syracuseStep 81565865 = 61174399) B61174399
theorem B4302719 : Blo 846354 4302719 := bstep (se 1 (by rfl) ⟨3227039, by rfl⟩ : syracuseStep 4302719 = 6454079) B6454079
theorem B190623887 : Blo 846354 190623887 := bstep (se 1 (by rfl) ⟨142967915, by rfl⟩ : syracuseStep 190623887 = 285935831) B285935831
theorem B6893819 : Blo 846354 6893819 := bstep (se 1 (by rfl) ⟨5170364, by rfl⟩ : syracuseStep 6893819 = 10340729) B10340729
theorem B127082591 : Blo 846354 127082591 := bstep (se 1 (by rfl) ⟨95311943, by rfl⟩ : syracuseStep 127082591 = 190623887) B190623887
theorem B4595879 : Blo 846354 4595879 := bstep (se 1 (by rfl) ⟨3446909, by rfl⟩ : syracuseStep 4595879 = 6893819) B6893819
theorem B54377243 : Blo 846354 54377243 := bstep (se 1 (by rfl) ⟨40782932, by rfl⟩ : syracuseStep 54377243 = 81565865) B81565865
theorem B2868479 : Blo 846354 2868479 := bstep (se 1 (by rfl) ⟨2151359, by rfl⟩ : syracuseStep 2868479 = 4302719) B4302719
theorem B36251495 : Blo 846354 36251495 := bstep (se 1 (by rfl) ⟨27188621, by rfl⟩ : syracuseStep 36251495 = 54377243) B54377243
theorem B1912319 : Blo 846354 1912319 := bstep (se 1 (by rfl) ⟨1434239, by rfl⟩ : syracuseStep 1912319 = 2868479) B2868479
theorem B84721727 : Blo 846354 84721727 := bstep (se 1 (by rfl) ⟨63541295, by rfl⟩ : syracuseStep 84721727 = 127082591) B127082591
theorem B3063919 : Blo 846354 3063919 := bstep (se 1 (by rfl) ⟨2297939, by rfl⟩ : syracuseStep 3063919 = 4595879) B4595879
theorem B24167663 : Blo 846354 24167663 := bstep (se 1 (by rfl) ⟨18125747, by rfl⟩ : syracuseStep 24167663 = 36251495) B36251495
theorem B56481151 : Blo 846354 56481151 := bstep (se 1 (by rfl) ⟨42360863, by rfl⟩ : syracuseStep 56481151 = 84721727) B84721727
theorem B4085225 : Blo 846354 4085225 := bstep (se 2 (by rfl) ⟨1531959, by rfl⟩ : syracuseStep 4085225 = 3063919) B3063919
theorem B1274879 : Blo 846354 1274879 := bstep (se 1 (by rfl) ⟨956159, by rfl⟩ : syracuseStep 1274879 = 1912319) B1912319
theorem B2723483 : Blo 846354 2723483 := bstep (se 1 (by rfl) ⟨2042612, by rfl⟩ : syracuseStep 2723483 = 4085225) B4085225
theorem B75308201 : Blo 846354 75308201 := bstep (se 2 (by rfl) ⟨28240575, by rfl⟩ : syracuseStep 75308201 = 56481151) B56481151
theorem B16111775 : Blo 846354 16111775 := bstep (se 1 (by rfl) ⟨12083831, by rfl⟩ : syracuseStep 16111775 = 24167663) B24167663
theorem B849919 : Blo 846354 849919 := bstep (se 1 (by rfl) ⟨637439, by rfl⟩ : syracuseStep 849919 = 1274879) B1274879
theorem B50205467 : Blo 846354 50205467 := bstep (se 1 (by rfl) ⟨37654100, by rfl⟩ : syracuseStep 50205467 = 75308201) B75308201
theorem B1815655 : Blo 846354 1815655 := bstep (se 1 (by rfl) ⟨1361741, by rfl⟩ : syracuseStep 1815655 = 2723483) B2723483
theorem B10741183 : Blo 846354 10741183 := bstep (se 1 (by rfl) ⟨8055887, by rfl⟩ : syracuseStep 10741183 = 16111775) B16111775
theorem B57286309 : Blo 846354 57286309 := bstep (se 4 (by rfl) ⟨5370591, by rfl⟩ : syracuseStep 57286309 = 10741183) B10741183
theorem B133881245 : Blo 846354 133881245 := bstep (se 3 (by rfl) ⟨25102733, by rfl⟩ : syracuseStep 133881245 = 50205467) B50205467
theorem B2420873 : Blo 846354 2420873 := bstep (se 2 (by rfl) ⟨907827, by rfl⟩ : syracuseStep 2420873 = 1815655) B1815655
theorem B1613915 : Blo 846354 1613915 := bstep (se 1 (by rfl) ⟨1210436, by rfl⟩ : syracuseStep 1613915 = 2420873) B2420873
theorem B89254163 : Blo 846354 89254163 := bstep (se 1 (by rfl) ⟨66940622, by rfl⟩ : syracuseStep 89254163 = 133881245) B133881245
theorem B76381745 : Blo 846354 76381745 := bstep (se 2 (by rfl) ⟨28643154, by rfl⟩ : syracuseStep 76381745 = 57286309) B57286309
theorem B1075943 : Blo 846354 1075943 := bstep (se 1 (by rfl) ⟨806957, by rfl⟩ : syracuseStep 1075943 = 1613915) B1613915
theorem B59502775 : Blo 846354 59502775 := bstep (se 1 (by rfl) ⟨44627081, by rfl⟩ : syracuseStep 59502775 = 89254163) B89254163
theorem B203684653 : Blo 846354 203684653 := bstep (se 3 (by rfl) ⟨38190872, by rfl⟩ : syracuseStep 203684653 = 76381745) B76381745
theorem B79337033 : Blo 846354 79337033 := bstep (se 2 (by rfl) ⟨29751387, by rfl⟩ : syracuseStep 79337033 = 59502775) B59502775
theorem B2869181 : Blo 846354 2869181 := bstep (se 3 (by rfl) ⟨537971, by rfl⟩ : syracuseStep 2869181 = 1075943) B1075943
theorem B271579537 : Blo 846354 271579537 := bstep (se 2 (by rfl) ⟨101842326, by rfl⟩ : syracuseStep 271579537 = 203684653) B203684653
theorem B52891355 : Blo 846354 52891355 := bstep (se 1 (by rfl) ⟨39668516, by rfl⟩ : syracuseStep 52891355 = 79337033) B79337033
theorem B1912787 : Blo 846354 1912787 := bstep (se 1 (by rfl) ⟨1434590, by rfl⟩ : syracuseStep 1912787 = 2869181) B2869181
theorem B362106049 : Blo 846354 362106049 := bstep (se 2 (by rfl) ⟨135789768, by rfl⟩ : syracuseStep 362106049 = 271579537) B271579537
theorem B35260903 : Blo 846354 35260903 := bstep (se 1 (by rfl) ⟨26445677, by rfl⟩ : syracuseStep 35260903 = 52891355) B52891355
theorem B482808065 : Blo 846354 482808065 := bstep (se 2 (by rfl) ⟨181053024, by rfl⟩ : syracuseStep 482808065 = 362106049) B362106049
theorem B1275191 : Blo 846354 1275191 := bstep (se 1 (by rfl) ⟨956393, by rfl⟩ : syracuseStep 1275191 = 1912787) B1912787
theorem B188058149 : Blo 846354 188058149 := bstep (se 4 (by rfl) ⟨17630451, by rfl⟩ : syracuseStep 188058149 = 35260903) B35260903
theorem B5149952693 : Blo 846354 5149952693 := bstep (se 5 (by rfl) ⟨241404032, by rfl⟩ : syracuseStep 5149952693 = 482808065) B482808065
theorem B850127 : Blo 846354 850127 := bstep (se 1 (by rfl) ⟨637595, by rfl⟩ : syracuseStep 850127 = 1275191) B1275191
theorem B125372099 : Blo 846354 125372099 := bstep (se 1 (by rfl) ⟨94029074, by rfl⟩ : syracuseStep 125372099 = 188058149) B188058149
theorem B3433301795 : Blo 846354 3433301795 := bstep (se 1 (by rfl) ⟨2574976346, by rfl⟩ : syracuseStep 3433301795 = 5149952693) B5149952693
theorem B83581399 : Blo 846354 83581399 := bstep (se 1 (by rfl) ⟨62686049, by rfl⟩ : syracuseStep 83581399 = 125372099) B125372099
theorem B2288867863 : Blo 846354 2288867863 := bstep (se 1 (by rfl) ⟨1716650897, by rfl⟩ : syracuseStep 2288867863 = 3433301795) B3433301795
theorem B3051823817 : Blo 846354 3051823817 := bstep (se 2 (by rfl) ⟨1144433931, by rfl⟩ : syracuseStep 3051823817 = 2288867863) B2288867863
theorem B111441865 : Blo 846354 111441865 := bstep (se 2 (by rfl) ⟨41790699, by rfl⟩ : syracuseStep 111441865 = 83581399) B83581399
theorem B8138196845 : Blo 846354 8138196845 := bstep (se 3 (by rfl) ⟨1525911908, by rfl⟩ : syracuseStep 8138196845 = 3051823817) B3051823817
theorem B148589153 : Blo 846354 148589153 := bstep (se 2 (by rfl) ⟨55720932, by rfl⟩ : syracuseStep 148589153 = 111441865) B111441865
theorem B5425464563 : Blo 846354 5425464563 := bstep (se 1 (by rfl) ⟨4069098422, by rfl⟩ : syracuseStep 5425464563 = 8138196845) B8138196845
theorem B99059435 : Blo 846354 99059435 := bstep (se 1 (by rfl) ⟨74294576, by rfl⟩ : syracuseStep 99059435 = 148589153) B148589153
theorem B3616976375 : Blo 846354 3616976375 := bstep (se 1 (by rfl) ⟨2712732281, by rfl⟩ : syracuseStep 3616976375 = 5425464563) B5425464563
theorem B66039623 : Blo 846354 66039623 := bstep (se 1 (by rfl) ⟨49529717, by rfl⟩ : syracuseStep 66039623 = 99059435) B99059435
theorem B2411317583 : Blo 846354 2411317583 := bstep (se 1 (by rfl) ⟨1808488187, by rfl⟩ : syracuseStep 2411317583 = 3616976375) B3616976375
theorem B44026415 : Blo 846354 44026415 := bstep (se 1 (by rfl) ⟨33019811, by rfl⟩ : syracuseStep 44026415 = 66039623) B66039623
theorem B1607545055 : Blo 846354 1607545055 := bstep (se 1 (by rfl) ⟨1205658791, by rfl⟩ : syracuseStep 1607545055 = 2411317583) B2411317583
theorem B29350943 : Blo 846354 29350943 := bstep (se 1 (by rfl) ⟨22013207, by rfl⟩ : syracuseStep 29350943 = 44026415) B44026415
theorem B19567295 : Blo 846354 19567295 := bstep (se 1 (by rfl) ⟨14675471, by rfl⟩ : syracuseStep 19567295 = 29350943) B29350943
theorem B1071696703 : Blo 846354 1071696703 := bstep (se 1 (by rfl) ⟨803772527, by rfl⟩ : syracuseStep 1071696703 = 1607545055) B1607545055
theorem B13044863 : Blo 846354 13044863 := bstep (se 1 (by rfl) ⟨9783647, by rfl⟩ : syracuseStep 13044863 = 19567295) B19567295
theorem B1428928937 : Blo 846354 1428928937 := bstep (se 2 (by rfl) ⟨535848351, by rfl⟩ : syracuseStep 1428928937 = 1071696703) B1071696703
theorem B8696575 : Blo 846354 8696575 := bstep (se 1 (by rfl) ⟨6522431, by rfl⟩ : syracuseStep 8696575 = 13044863) B13044863
theorem B952619291 : Blo 846354 952619291 := bstep (se 1 (by rfl) ⟨714464468, by rfl⟩ : syracuseStep 952619291 = 1428928937) B1428928937
theorem B635079527 : Blo 846354 635079527 := bstep (se 1 (by rfl) ⟨476309645, by rfl⟩ : syracuseStep 635079527 = 952619291) B952619291
theorem B11595433 : Blo 846354 11595433 := bstep (se 2 (by rfl) ⟨4348287, by rfl⟩ : syracuseStep 11595433 = 8696575) B8696575
theorem B423386351 : Blo 846354 423386351 := bstep (se 1 (by rfl) ⟨317539763, by rfl⟩ : syracuseStep 423386351 = 635079527) B635079527
theorem B15460577 : Blo 846354 15460577 := bstep (se 2 (by rfl) ⟨5797716, by rfl⟩ : syracuseStep 15460577 = 11595433) B11595433
theorem B10307051 : Blo 846354 10307051 := bstep (se 1 (by rfl) ⟨7730288, by rfl⟩ : syracuseStep 10307051 = 15460577) B15460577
theorem B282257567 : Blo 846354 282257567 := bstep (se 1 (by rfl) ⟨211693175, by rfl⟩ : syracuseStep 282257567 = 423386351) B423386351
theorem B188171711 : Blo 846354 188171711 := bstep (se 1 (by rfl) ⟨141128783, by rfl⟩ : syracuseStep 188171711 = 282257567) B282257567
theorem B6871367 : Blo 846354 6871367 := bstep (se 1 (by rfl) ⟨5153525, by rfl⟩ : syracuseStep 6871367 = 10307051) B10307051
theorem B125447807 : Blo 846354 125447807 := bstep (se 1 (by rfl) ⟨94085855, by rfl⟩ : syracuseStep 125447807 = 188171711) B188171711
theorem B4580911 : Blo 846354 4580911 := bstep (se 1 (by rfl) ⟨3435683, by rfl⟩ : syracuseStep 4580911 = 6871367) B6871367
theorem B83631871 : Blo 846354 83631871 := bstep (se 1 (by rfl) ⟨62723903, by rfl⟩ : syracuseStep 83631871 = 125447807) B125447807
theorem B6107881 : Blo 846354 6107881 := bstep (se 2 (by rfl) ⟨2290455, by rfl⟩ : syracuseStep 6107881 = 4580911) B4580911
theorem B8143841 : Blo 846354 8143841 := bstep (se 2 (by rfl) ⟨3053940, by rfl⟩ : syracuseStep 8143841 = 6107881) B6107881
theorem B446036645 : Blo 846354 446036645 := bstep (se 4 (by rfl) ⟨41815935, by rfl⟩ : syracuseStep 446036645 = 83631871) B83631871
theorem B297357763 : Blo 846354 297357763 := bstep (se 1 (by rfl) ⟨223018322, by rfl⟩ : syracuseStep 297357763 = 446036645) B446036645
theorem B21716909 : Blo 846354 21716909 := bstep (se 3 (by rfl) ⟨4071920, by rfl⟩ : syracuseStep 21716909 = 8143841) B8143841
theorem B396477017 : Blo 846354 396477017 := bstep (se 2 (by rfl) ⟨148678881, by rfl⟩ : syracuseStep 396477017 = 297357763) B297357763
theorem B14477939 : Blo 846354 14477939 := bstep (se 1 (by rfl) ⟨10858454, by rfl⟩ : syracuseStep 14477939 = 21716909) B21716909
theorem B264318011 : Blo 846354 264318011 := bstep (se 1 (by rfl) ⟨198238508, by rfl⟩ : syracuseStep 264318011 = 396477017) B396477017
theorem B9651959 : Blo 846354 9651959 := bstep (se 1 (by rfl) ⟨7238969, by rfl⟩ : syracuseStep 9651959 = 14477939) B14477939
theorem B6434639 : Blo 846354 6434639 := bstep (se 1 (by rfl) ⟨4825979, by rfl⟩ : syracuseStep 6434639 = 9651959) B9651959
theorem B176212007 : Blo 846354 176212007 := bstep (se 1 (by rfl) ⟨132159005, by rfl⟩ : syracuseStep 176212007 = 264318011) B264318011
theorem B117474671 : Blo 846354 117474671 := bstep (se 1 (by rfl) ⟨88106003, by rfl⟩ : syracuseStep 117474671 = 176212007) B176212007
theorem B4289759 : Blo 846354 4289759 := bstep (se 1 (by rfl) ⟨3217319, by rfl⟩ : syracuseStep 4289759 = 6434639) B6434639
theorem B313265789 : Blo 846354 313265789 := bstep (se 3 (by rfl) ⟨58737335, by rfl⟩ : syracuseStep 313265789 = 117474671) B117474671
theorem B2859839 : Blo 846354 2859839 := bstep (se 1 (by rfl) ⟨2144879, by rfl⟩ : syracuseStep 2859839 = 4289759) B4289759
theorem B1906559 : Blo 846354 1906559 := bstep (se 1 (by rfl) ⟨1429919, by rfl⟩ : syracuseStep 1906559 = 2859839) B2859839
theorem B208843859 : Blo 846354 208843859 := bstep (se 1 (by rfl) ⟨156632894, by rfl⟩ : syracuseStep 208843859 = 313265789) B313265789
theorem B1271039 : Blo 846354 1271039 := bstep (se 1 (by rfl) ⟨953279, by rfl⟩ : syracuseStep 1271039 = 1906559) B1906559
theorem B139229239 : Blo 846354 139229239 := bstep (se 1 (by rfl) ⟨104421929, by rfl⟩ : syracuseStep 139229239 = 208843859) B208843859
theorem B185638985 : Blo 846354 185638985 := bstep (se 2 (by rfl) ⟨69614619, by rfl⟩ : syracuseStep 185638985 = 139229239) B139229239
theorem B847359 : Blo 846354 847359 := bstep (se 1 (by rfl) ⟨635519, by rfl⟩ : syracuseStep 847359 = 1271039) B1271039
theorem B123759323 : Blo 846354 123759323 := bstep (se 1 (by rfl) ⟨92819492, by rfl⟩ : syracuseStep 123759323 = 185638985) B185638985
theorem B82506215 : Blo 846354 82506215 := bstep (se 1 (by rfl) ⟨61879661, by rfl⟩ : syracuseStep 82506215 = 123759323) B123759323
theorem B55004143 : Blo 846354 55004143 := bstep (se 1 (by rfl) ⟨41253107, by rfl⟩ : syracuseStep 55004143 = 82506215) B82506215
theorem B73338857 : Blo 846354 73338857 := bstep (se 2 (by rfl) ⟨27502071, by rfl⟩ : syracuseStep 73338857 = 55004143) B55004143
theorem B48892571 : Blo 846354 48892571 := bstep (se 1 (by rfl) ⟨36669428, by rfl⟩ : syracuseStep 48892571 = 73338857) B73338857
theorem B32595047 : Blo 846354 32595047 := bstep (se 1 (by rfl) ⟨24446285, by rfl⟩ : syracuseStep 32595047 = 48892571) B48892571
theorem B21730031 : Blo 846354 21730031 := bstep (se 1 (by rfl) ⟨16297523, by rfl⟩ : syracuseStep 21730031 = 32595047) B32595047
theorem B14486687 : Blo 846354 14486687 := bstep (se 1 (by rfl) ⟨10865015, by rfl⟩ : syracuseStep 14486687 = 21730031) B21730031
theorem B9657791 : Blo 846354 9657791 := bstep (se 1 (by rfl) ⟨7243343, by rfl⟩ : syracuseStep 9657791 = 14486687) B14486687
theorem B6438527 : Blo 846354 6438527 := bstep (se 1 (by rfl) ⟨4828895, by rfl⟩ : syracuseStep 6438527 = 9657791) B9657791
theorem B4292351 : Blo 846354 4292351 := bstep (se 1 (by rfl) ⟨3219263, by rfl⟩ : syracuseStep 4292351 = 6438527) B6438527
theorem B2861567 : Blo 846354 2861567 := bstep (se 1 (by rfl) ⟨2146175, by rfl⟩ : syracuseStep 2861567 = 4292351) B4292351
theorem B1907711 : Blo 846354 1907711 := bstep (se 1 (by rfl) ⟨1430783, by rfl⟩ : syracuseStep 1907711 = 2861567) B2861567
theorem B1271807 : Blo 846354 1271807 := bstep (se 1 (by rfl) ⟨953855, by rfl⟩ : syracuseStep 1271807 = 1907711) B1907711
theorem B847871 : Blo 846354 847871 := bstep (se 1 (by rfl) ⟨635903, by rfl⟩ : syracuseStep 847871 = 1271807) B1271807

theorem C0 (j : ℕ) (h1 : 211588 ≤ j) (h2 : j ≤ 212287) : Blo 846354 (4 * j + 3) := by
  interval_cases j
  · exact B846355
  · exact B846359
  · exact B846363
  · exact B846367
  · exact B846371
  · exact B846375
  · exact B846379
  · exact B846383
  · exact B846387
  · exact B846391
  · exact B846395
  · exact B846399
  · exact B846403
  · exact B846407
  · exact B846411
  · exact B846415
  · exact B846419
  · exact B846423
  · exact B846427
  · exact B846431
  · exact B846435
  · exact B846439
  · exact B846443
  · exact B846447
  · exact B846451
  · exact B846455
  · exact B846459
  · exact B846463
  · exact B846467
  · exact B846471
  · exact B846475
  · exact B846479
  · exact B846483
  · exact B846487
  · exact B846491
  · exact B846495
  · exact B846499
  · exact B846503
  · exact B846507
  · exact B846511
  · exact B846515
  · exact B846519
  · exact B846523
  · exact B846527
  · exact B846531
  · exact B846535
  · exact B846539
  · exact B846543
  · exact B846547
  · exact B846551
  · exact B846555
  · exact B846559
  · exact B846563
  · exact B846567
  · exact B846571
  · exact B846575
  · exact B846579
  · exact B846583
  · exact B846587
  · exact B846591
  · exact B846595
  · exact B846599
  · exact B846603
  · exact B846607
  · exact B846611
  · exact B846615
  · exact B846619
  · exact B846623
  · exact B846627
  · exact B846631
  · exact B846635
  · exact B846639
  · exact B846643
  · exact B846647
  · exact B846651
  · exact B846655
  · exact B846659
  · exact B846663
  · exact B846667
  · exact B846671
  · exact B846675
  · exact B846679
  · exact B846683
  · exact B846687
  · exact B846691
  · exact B846695
  · exact B846699
  · exact B846703
  · exact B846707
  · exact B846711
  · exact B846715
  · exact B846719
  · exact B846723
  · exact B846727
  · exact B846731
  · exact B846735
  · exact B846739
  · exact B846743
  · exact B846747
  · exact B846751
  · exact B846755
  · exact B846759
  · exact B846763
  · exact B846767
  · exact B846771
  · exact B846775
  · exact B846779
  · exact B846783
  · exact B846787
  · exact B846791
  · exact B846795
  · exact B846799
  · exact B846803
  · exact B846807
  · exact B846811
  · exact B846815
  · exact B846819
  · exact B846823
  · exact B846827
  · exact B846831
  · exact B846835
  · exact B846839
  · exact B846843
  · exact B846847
  · exact B846851
  · exact B846855
  · exact B846859
  · exact B846863
  · exact B846867
  · exact B846871
  · exact B846875
  · exact B846879
  · exact B846883
  · exact B846887
  · exact B846891
  · exact B846895
  · exact B846899
  · exact B846903
  · exact B846907
  · exact B846911
  · exact B846915
  · exact B846919
  · exact B846923
  · exact B846927
  · exact B846931
  · exact B846935
  · exact B846939
  · exact B846943
  · exact B846947
  · exact B846951
  · exact B846955
  · exact B846959
  · exact B846963
  · exact B846967
  · exact B846971
  · exact B846975
  · exact B846979
  · exact B846983
  · exact B846987
  · exact B846991
  · exact B846995
  · exact B846999
  · exact B847003
  · exact B847007
  · exact B847011
  · exact B847015
  · exact B847019
  · exact B847023
  · exact B847027
  · exact B847031
  · exact B847035
  · exact B847039
  · exact B847043
  · exact B847047
  · exact B847051
  · exact B847055
  · exact B847059
  · exact B847063
  · exact B847067
  · exact B847071
  · exact B847075
  · exact B847079
  · exact B847083
  · exact B847087
  · exact B847091
  · exact B847095
  · exact B847099
  · exact B847103
  · exact B847107
  · exact B847111
  · exact B847115
  · exact B847119
  · exact B847123
  · exact B847127
  · exact B847131
  · exact B847135
  · exact B847139
  · exact B847143
  · exact B847147
  · exact B847151
  · exact B847155
  · exact B847159
  · exact B847163
  · exact B847167
  · exact B847171
  · exact B847175
  · exact B847179
  · exact B847183
  · exact B847187
  · exact B847191
  · exact B847195
  · exact B847199
  · exact B847203
  · exact B847207
  · exact B847211
  · exact B847215
  · exact B847219
  · exact B847223
  · exact B847227
  · exact B847231
  · exact B847235
  · exact B847239
  · exact B847243
  · exact B847247
  · exact B847251
  · exact B847255
  · exact B847259
  · exact B847263
  · exact B847267
  · exact B847271
  · exact B847275
  · exact B847279
  · exact B847283
  · exact B847287
  · exact B847291
  · exact B847295
  · exact B847299
  · exact B847303
  · exact B847307
  · exact B847311
  · exact B847315
  · exact B847319
  · exact B847323
  · exact B847327
  · exact B847331
  · exact B847335
  · exact B847339
  · exact B847343
  · exact B847347
  · exact B847351
  · exact B847355
  · exact B847359
  · exact B847363
  · exact B847367
  · exact B847371
  · exact B847375
  · exact B847379
  · exact B847383
  · exact B847387
  · exact B847391
  · exact B847395
  · exact B847399
  · exact B847403
  · exact B847407
  · exact B847411
  · exact B847415
  · exact B847419
  · exact B847423
  · exact B847427
  · exact B847431
  · exact B847435
  · exact B847439
  · exact B847443
  · exact B847447
  · exact B847451
  · exact B847455
  · exact B847459
  · exact B847463
  · exact B847467
  · exact B847471
  · exact B847475
  · exact B847479
  · exact B847483
  · exact B847487
  · exact B847491
  · exact B847495
  · exact B847499
  · exact B847503
  · exact B847507
  · exact B847511
  · exact B847515
  · exact B847519
  · exact B847523
  · exact B847527
  · exact B847531
  · exact B847535
  · exact B847539
  · exact B847543
  · exact B847547
  · exact B847551
  · exact B847555
  · exact B847559
  · exact B847563
  · exact B847567
  · exact B847571
  · exact B847575
  · exact B847579
  · exact B847583
  · exact B847587
  · exact B847591
  · exact B847595
  · exact B847599
  · exact B847603
  · exact B847607
  · exact B847611
  · exact B847615
  · exact B847619
  · exact B847623
  · exact B847627
  · exact B847631
  · exact B847635
  · exact B847639
  · exact B847643
  · exact B847647
  · exact B847651
  · exact B847655
  · exact B847659
  · exact B847663
  · exact B847667
  · exact B847671
  · exact B847675
  · exact B847679
  · exact B847683
  · exact B847687
  · exact B847691
  · exact B847695
  · exact B847699
  · exact B847703
  · exact B847707
  · exact B847711
  · exact B847715
  · exact B847719
  · exact B847723
  · exact B847727
  · exact B847731
  · exact B847735
  · exact B847739
  · exact B847743
  · exact B847747
  · exact B847751
  · exact B847755
  · exact B847759
  · exact B847763
  · exact B847767
  · exact B847771
  · exact B847775
  · exact B847779
  · exact B847783
  · exact B847787
  · exact B847791
  · exact B847795
  · exact B847799
  · exact B847803
  · exact B847807
  · exact B847811
  · exact B847815
  · exact B847819
  · exact B847823
  · exact B847827
  · exact B847831
  · exact B847835
  · exact B847839
  · exact B847843
  · exact B847847
  · exact B847851
  · exact B847855
  · exact B847859
  · exact B847863
  · exact B847867
  · exact B847871
  · exact B847875
  · exact B847879
  · exact B847883
  · exact B847887
  · exact B847891
  · exact B847895
  · exact B847899
  · exact B847903
  · exact B847907
  · exact B847911
  · exact B847915
  · exact B847919
  · exact B847923
  · exact B847927
  · exact B847931
  · exact B847935
  · exact B847939
  · exact B847943
  · exact B847947
  · exact B847951
  · exact B847955
  · exact B847959
  · exact B847963
  · exact B847967
  · exact B847971
  · exact B847975
  · exact B847979
  · exact B847983
  · exact B847987
  · exact B847991
  · exact B847995
  · exact B847999
  · exact B848003
  · exact B848007
  · exact B848011
  · exact B848015
  · exact B848019
  · exact B848023
  · exact B848027
  · exact B848031
  · exact B848035
  · exact B848039
  · exact B848043
  · exact B848047
  · exact B848051
  · exact B848055
  · exact B848059
  · exact B848063
  · exact B848067
  · exact B848071
  · exact B848075
  · exact B848079
  · exact B848083
  · exact B848087
  · exact B848091
  · exact B848095
  · exact B848099
  · exact B848103
  · exact B848107
  · exact B848111
  · exact B848115
  · exact B848119
  · exact B848123
  · exact B848127
  · exact B848131
  · exact B848135
  · exact B848139
  · exact B848143
  · exact B848147
  · exact B848151
  · exact B848155
  · exact B848159
  · exact B848163
  · exact B848167
  · exact B848171
  · exact B848175
  · exact B848179
  · exact B848183
  · exact B848187
  · exact B848191
  · exact B848195
  · exact B848199
  · exact B848203
  · exact B848207
  · exact B848211
  · exact B848215
  · exact B848219
  · exact B848223
  · exact B848227
  · exact B848231
  · exact B848235
  · exact B848239
  · exact B848243
  · exact B848247
  · exact B848251
  · exact B848255
  · exact B848259
  · exact B848263
  · exact B848267
  · exact B848271
  · exact B848275
  · exact B848279
  · exact B848283
  · exact B848287
  · exact B848291
  · exact B848295
  · exact B848299
  · exact B848303
  · exact B848307
  · exact B848311
  · exact B848315
  · exact B848319
  · exact B848323
  · exact B848327
  · exact B848331
  · exact B848335
  · exact B848339
  · exact B848343
  · exact B848347
  · exact B848351
  · exact B848355
  · exact B848359
  · exact B848363
  · exact B848367
  · exact B848371
  · exact B848375
  · exact B848379
  · exact B848383
  · exact B848387
  · exact B848391
  · exact B848395
  · exact B848399
  · exact B848403
  · exact B848407
  · exact B848411
  · exact B848415
  · exact B848419
  · exact B848423
  · exact B848427
  · exact B848431
  · exact B848435
  · exact B848439
  · exact B848443
  · exact B848447
  · exact B848451
  · exact B848455
  · exact B848459
  · exact B848463
  · exact B848467
  · exact B848471
  · exact B848475
  · exact B848479
  · exact B848483
  · exact B848487
  · exact B848491
  · exact B848495
  · exact B848499
  · exact B848503
  · exact B848507
  · exact B848511
  · exact B848515
  · exact B848519
  · exact B848523
  · exact B848527
  · exact B848531
  · exact B848535
  · exact B848539
  · exact B848543
  · exact B848547
  · exact B848551
  · exact B848555
  · exact B848559
  · exact B848563
  · exact B848567
  · exact B848571
  · exact B848575
  · exact B848579
  · exact B848583
  · exact B848587
  · exact B848591
  · exact B848595
  · exact B848599
  · exact B848603
  · exact B848607
  · exact B848611
  · exact B848615
  · exact B848619
  · exact B848623
  · exact B848627
  · exact B848631
  · exact B848635
  · exact B848639
  · exact B848643
  · exact B848647
  · exact B848651
  · exact B848655
  · exact B848659
  · exact B848663
  · exact B848667
  · exact B848671
  · exact B848675
  · exact B848679
  · exact B848683
  · exact B848687
  · exact B848691
  · exact B848695
  · exact B848699
  · exact B848703
  · exact B848707
  · exact B848711
  · exact B848715
  · exact B848719
  · exact B848723
  · exact B848727
  · exact B848731
  · exact B848735
  · exact B848739
  · exact B848743
  · exact B848747
  · exact B848751
  · exact B848755
  · exact B848759
  · exact B848763
  · exact B848767
  · exact B848771
  · exact B848775
  · exact B848779
  · exact B848783
  · exact B848787
  · exact B848791
  · exact B848795
  · exact B848799
  · exact B848803
  · exact B848807
  · exact B848811
  · exact B848815
  · exact B848819
  · exact B848823
  · exact B848827
  · exact B848831
  · exact B848835
  · exact B848839
  · exact B848843
  · exact B848847
  · exact B848851
  · exact B848855
  · exact B848859
  · exact B848863
  · exact B848867
  · exact B848871
  · exact B848875
  · exact B848879
  · exact B848883
  · exact B848887
  · exact B848891
  · exact B848895
  · exact B848899
  · exact B848903
  · exact B848907
  · exact B848911
  · exact B848915
  · exact B848919
  · exact B848923
  · exact B848927
  · exact B848931
  · exact B848935
  · exact B848939
  · exact B848943
  · exact B848947
  · exact B848951
  · exact B848955
  · exact B848959
  · exact B848963
  · exact B848967
  · exact B848971
  · exact B848975
  · exact B848979
  · exact B848983
  · exact B848987
  · exact B848991
  · exact B848995
  · exact B848999
  · exact B849003
  · exact B849007
  · exact B849011
  · exact B849015
  · exact B849019
  · exact B849023
  · exact B849027
  · exact B849031
  · exact B849035
  · exact B849039
  · exact B849043
  · exact B849047
  · exact B849051
  · exact B849055
  · exact B849059
  · exact B849063
  · exact B849067
  · exact B849071
  · exact B849075
  · exact B849079
  · exact B849083
  · exact B849087
  · exact B849091
  · exact B849095
  · exact B849099
  · exact B849103
  · exact B849107
  · exact B849111
  · exact B849115
  · exact B849119
  · exact B849123
  · exact B849127
  · exact B849131
  · exact B849135
  · exact B849139
  · exact B849143
  · exact B849147
  · exact B849151

theorem C1 (j : ℕ) (h1 : 212288 ≤ j) (h2 : j ≤ 212587) : Blo 846354 (4 * j + 3) := by
  interval_cases j
  · exact B849155
  · exact B849159
  · exact B849163
  · exact B849167
  · exact B849171
  · exact B849175
  · exact B849179
  · exact B849183
  · exact B849187
  · exact B849191
  · exact B849195
  · exact B849199
  · exact B849203
  · exact B849207
  · exact B849211
  · exact B849215
  · exact B849219
  · exact B849223
  · exact B849227
  · exact B849231
  · exact B849235
  · exact B849239
  · exact B849243
  · exact B849247
  · exact B849251
  · exact B849255
  · exact B849259
  · exact B849263
  · exact B849267
  · exact B849271
  · exact B849275
  · exact B849279
  · exact B849283
  · exact B849287
  · exact B849291
  · exact B849295
  · exact B849299
  · exact B849303
  · exact B849307
  · exact B849311
  · exact B849315
  · exact B849319
  · exact B849323
  · exact B849327
  · exact B849331
  · exact B849335
  · exact B849339
  · exact B849343
  · exact B849347
  · exact B849351
  · exact B849355
  · exact B849359
  · exact B849363
  · exact B849367
  · exact B849371
  · exact B849375
  · exact B849379
  · exact B849383
  · exact B849387
  · exact B849391
  · exact B849395
  · exact B849399
  · exact B849403
  · exact B849407
  · exact B849411
  · exact B849415
  · exact B849419
  · exact B849423
  · exact B849427
  · exact B849431
  · exact B849435
  · exact B849439
  · exact B849443
  · exact B849447
  · exact B849451
  · exact B849455
  · exact B849459
  · exact B849463
  · exact B849467
  · exact B849471
  · exact B849475
  · exact B849479
  · exact B849483
  · exact B849487
  · exact B849491
  · exact B849495
  · exact B849499
  · exact B849503
  · exact B849507
  · exact B849511
  · exact B849515
  · exact B849519
  · exact B849523
  · exact B849527
  · exact B849531
  · exact B849535
  · exact B849539
  · exact B849543
  · exact B849547
  · exact B849551
  · exact B849555
  · exact B849559
  · exact B849563
  · exact B849567
  · exact B849571
  · exact B849575
  · exact B849579
  · exact B849583
  · exact B849587
  · exact B849591
  · exact B849595
  · exact B849599
  · exact B849603
  · exact B849607
  · exact B849611
  · exact B849615
  · exact B849619
  · exact B849623
  · exact B849627
  · exact B849631
  · exact B849635
  · exact B849639
  · exact B849643
  · exact B849647
  · exact B849651
  · exact B849655
  · exact B849659
  · exact B849663
  · exact B849667
  · exact B849671
  · exact B849675
  · exact B849679
  · exact B849683
  · exact B849687
  · exact B849691
  · exact B849695
  · exact B849699
  · exact B849703
  · exact B849707
  · exact B849711
  · exact B849715
  · exact B849719
  · exact B849723
  · exact B849727
  · exact B849731
  · exact B849735
  · exact B849739
  · exact B849743
  · exact B849747
  · exact B849751
  · exact B849755
  · exact B849759
  · exact B849763
  · exact B849767
  · exact B849771
  · exact B849775
  · exact B849779
  · exact B849783
  · exact B849787
  · exact B849791
  · exact B849795
  · exact B849799
  · exact B849803
  · exact B849807
  · exact B849811
  · exact B849815
  · exact B849819
  · exact B849823
  · exact B849827
  · exact B849831
  · exact B849835
  · exact B849839
  · exact B849843
  · exact B849847
  · exact B849851
  · exact B849855
  · exact B849859
  · exact B849863
  · exact B849867
  · exact B849871
  · exact B849875
  · exact B849879
  · exact B849883
  · exact B849887
  · exact B849891
  · exact B849895
  · exact B849899
  · exact B849903
  · exact B849907
  · exact B849911
  · exact B849915
  · exact B849919
  · exact B849923
  · exact B849927
  · exact B849931
  · exact B849935
  · exact B849939
  · exact B849943
  · exact B849947
  · exact B849951
  · exact B849955
  · exact B849959
  · exact B849963
  · exact B849967
  · exact B849971
  · exact B849975
  · exact B849979
  · exact B849983
  · exact B849987
  · exact B849991
  · exact B849995
  · exact B849999
  · exact B850003
  · exact B850007
  · exact B850011
  · exact B850015
  · exact B850019
  · exact B850023
  · exact B850027
  · exact B850031
  · exact B850035
  · exact B850039
  · exact B850043
  · exact B850047
  · exact B850051
  · exact B850055
  · exact B850059
  · exact B850063
  · exact B850067
  · exact B850071
  · exact B850075
  · exact B850079
  · exact B850083
  · exact B850087
  · exact B850091
  · exact B850095
  · exact B850099
  · exact B850103
  · exact B850107
  · exact B850111
  · exact B850115
  · exact B850119
  · exact B850123
  · exact B850127
  · exact B850131
  · exact B850135
  · exact B850139
  · exact B850143
  · exact B850147
  · exact B850151
  · exact B850155
  · exact B850159
  · exact B850163
  · exact B850167
  · exact B850171
  · exact B850175
  · exact B850179
  · exact B850183
  · exact B850187
  · exact B850191
  · exact B850195
  · exact B850199
  · exact B850203
  · exact B850207
  · exact B850211
  · exact B850215
  · exact B850219
  · exact B850223
  · exact B850227
  · exact B850231
  · exact B850235
  · exact B850239
  · exact B850243
  · exact B850247
  · exact B850251
  · exact B850255
  · exact B850259
  · exact B850263
  · exact B850267
  · exact B850271
  · exact B850275
  · exact B850279
  · exact B850283
  · exact B850287
  · exact B850291
  · exact B850295
  · exact B850299
  · exact B850303
  · exact B850307
  · exact B850311
  · exact B850315
  · exact B850319
  · exact B850323
  · exact B850327
  · exact B850331
  · exact B850335
  · exact B850339
  · exact B850343
  · exact B850347
  · exact B850351

theorem solution (m : ℕ) (hlo : 846354 ≤ m) (hhi : m ≤ 850354) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 211588 ≤ j := by omega
    have hj2 : j ≤ 212587 := by omega
    have hb : Blo 846354 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 212288 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
